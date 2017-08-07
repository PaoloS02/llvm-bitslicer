#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/CodeExtractor.h"
#include "llvm/Analysis/LoopInfo.h"

#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/LegacyPassManager.h"


#define CPU_BYTES 1					//if you want N = 8, 16, 24, 32... blocks in parallel put this 
									//macro at 1, 2, 3, 4...

#define UNIFORM_ALLOCATION 8		//the scalar uint8_t variables are allocated with the same
									//size as the arrays for uniformity (it causes a segmentation
									//fault otherwise). You must set this macro to the dimension
									//of the array.

#define SENSIBLE_DATA_BYTES 1		//size in bits of the sensible data to be bitsliced in the program
#define BLOCK_LEN	8

using namespace llvm;

std::vector<Instruction *> eraseList;
std::vector<StringRef> AllocOldNames;
std::vector<AllocaInst *> AllocNewInstBuff;
std::vector<StringRef> BitSlicedAllocNames;
std::vector<AllocaInst *> BitSlicedAllocInstBuff;



bool BitSlice(CallInst *call, LLVMContext &Context){
	IRBuilder<> builder(call);
		
	Instruction *inputSize = cast<Instruction>(call->getArgOperand(0));
	for(; !isa<AllocaInst>(inputSize); inputSize = cast<Instruction>(inputSize->getOperand(0)));
	AllocaInst *blocksAlloca = cast<AllocaInst>(inputSize);
	if(!isa<ArrayType>(blocksAlloca->getAllocatedType())){
		errs() << "ERROR: argument 1 not a static array\n";
		return false;
	}
	uint64_t oldSize = cast<ArrayType>(blocksAlloca->getAllocatedType())->getNumElements();
		
	Instruction *outputSize = cast<Instruction>(call->getArgOperand(1));
	for(; !isa<AllocaInst>(outputSize); outputSize = cast<Instruction>(outputSize->getOperand(0)));
	AllocaInst *slicesAlloca = cast<AllocaInst>(outputSize);
	
	if(!isa<ArrayType>(slicesAlloca->getAllocatedType())){
		errs() << "ERROR: argument 1 not a static array\n";
		return false;
	}
	uint64_t newSize = dyn_cast<ArrayType>(slicesAlloca->getAllocatedType())->getNumElements();	
	
	if(newSize < (oldSize/32)*8){
		errs() << "ERROR: insufficient size of second operand.\nIt should be at least: ( " << oldSize << " / sizeof(int) ) * 8\n";
		return false;
	}

	
	//	MDNode *MData = MDNode::get(Context, 
	//							MDString::get(Context, "bitsliced"));
	Type *sliceTy = IntegerType::getInt32Ty(Context);						//FIXME: dependant on the target machine
	int i, j;
	
	std::vector<Value *> IdxList;
	Type *idxTy = IntegerType::getInt64Ty(Context);
	Value *idxZero = ConstantInt::get(idxTy, 0);
	IdxList.push_back(idxZero);
	IdxList.push_back(idxZero);
	Value *sliceAddr;
	Value *tmp;
	Value *bitVal;
	Value *Byte;
	int inputBits = newSize;
		
	for( i = 0; i < inputBits; i++ ){
		IdxList.at(1) = ConstantInt::get(idxTy, i);
		sliceAddr = builder.CreateGEP(slicesAlloca, ArrayRef <Value *>(IdxList), "sliceAddr");
		tmp = ConstantInt::get(sliceTy, 0);	
		for( j = 0; j < 32; j++){				//FIXME: dependant on the target machine
			IdxList.at(1) = ConstantInt::get(idxTy, j*inputBits/8+i/8);
			Byte = builder.CreateGEP(blocksAlloca, ArrayRef <Value *>(IdxList), "Block");
			Byte = builder.CreateLoad(Byte);

			bitVal = builder.CreateZExt(Byte, sliceTy);			
			bitVal = builder.CreateLShr(bitVal, ConstantInt::get(sliceTy, i%8));
			bitVal = builder.CreateAnd(bitVal, ConstantInt::get(sliceTy, 1));
			bitVal = builder.CreateShl(bitVal, ConstantInt::get(sliceTy, j));
			tmp = builder.CreateOr(tmp, bitVal);
		}
		builder.CreateStore(tmp, sliceAddr);
	}
	
	return true;
}


bool UnBitSlice(CallInst *call, LLVMContext &Context){
	IRBuilder<> builder(call);
	int i, j, k;
	
	Instruction *inputSize = cast<Instruction>(call->getArgOperand(0));
	for(; !isa<AllocaInst>(inputSize); inputSize = cast<Instruction>(inputSize->getOperand(0)));
	AllocaInst *slicesAlloca = cast<AllocaInst>(inputSize);
	
	if(!isa<ArrayType>(slicesAlloca->getAllocatedType())){
		errs() << "ERROR: argument 1 not a static array\n";
		return false;
	}
	uint64_t oldSize = cast<ArrayType>(slicesAlloca->getAllocatedType())->getNumElements();
	
	Instruction *outputSize = cast<Instruction>(call->getArgOperand(1));
	for(; !isa<AllocaInst>(outputSize); outputSize = cast<Instruction>(outputSize->getOperand(0)));
	AllocaInst *outputAlloca = cast<AllocaInst>(outputSize);
	
	if(!isa<ArrayType>(outputAlloca->getAllocatedType())){
		errs() << "ERROR: argument 1 not a static array\n";
		return false;
	}
	uint64_t newSize = cast<ArrayType>(outputAlloca->getAllocatedType())->getNumElements();
	
	if(newSize < (oldSize/32)*8){
		errs() << "ERROR: insufficient size of second operand.\nIt should be at least: (" 
			   << oldSize << " / sizeof(int)) * 8\n";
		return false;
	}
		
	Value *newByteAddr, *sliceAddr;
	Type *byteTy = IntegerType::getInt8Ty(Context);				//FIXME: dependant on the type used by the block cipher
	
	std::vector<Value *> IdxList;
	Type *idxTy = IntegerType::getInt64Ty(Context);
	Value *idxZero = ConstantInt::get(idxTy, 0);
	IdxList.push_back(idxZero);
	IdxList.push_back(idxZero);
	
	Value *bitVal, *tmp;
	Type *sliceTy = IntegerType::getInt32Ty(Context);			//FIXME: dependant on the target machine
	int outputLen = oldSize/8;
	
	for(i=0; i<32; i++){			//FIXME: dependant on the target machine
		for(j=0; j < outputLen; j++){
			IdxList.at(1) = ConstantInt::get(idxTy, i*outputLen + j);
			newByteAddr = builder.CreateGEP(outputAlloca, ArrayRef <Value *>(IdxList));
			tmp = ConstantInt::get(byteTy, 0);
			for(k=0;k<8;k++){
				IdxList.at(1) = ConstantInt::get(idxTy, j*8 + k);
				
				sliceAddr = builder.CreateGEP(slicesAlloca, ArrayRef <Value *>(IdxList));
				bitVal = builder.CreateLoad(sliceAddr);
				bitVal = builder.CreateLShr(bitVal, ConstantInt::get(sliceTy, i));
				bitVal = builder.CreateAnd(bitVal, ConstantInt::get(sliceTy, 1));
				bitVal = builder.CreateShl(bitVal, k);
				bitVal = builder.CreateTrunc(bitVal, byteTy);
				tmp = builder.CreateOr(tmp, bitVal);
			}

			builder.CreateStore(tmp, newByteAddr);
		}
	}
	
	return true;
}



void EndOrthogonalTransformation(CallInst *call, 
								 BasicBlock *startBlock, 
								 BasicBlock *endBlock,
								 Value *Description){
	BasicBlock *bb;
	std::vector<BasicBlock *> BlockList;
	for (bb = startBlock; bb != endBlock; bb = bb->getUniqueSuccessor()) {
		BlockList.push_back(bb);
	}
	auto CExtr = new CodeExtractor(ArrayRef <BasicBlock *>(BlockList));
	Function *NewFunc = CExtr->extractCodeRegion();
	
	//BasicBlock *entry = BasicBlock::Create(getGlobalContext(), "entry", NewFunc);
	//IRBuilder<> builder(entry);
	
	
	//for(; token = ParseDescription(Description);)
}



namespace{
	
	struct BitSlicer : public FunctionPass{
		static char ID;
		//static int TYPE_OK;
//		static int INSTR_TYPE;
//		static int LAST_INSTR_TYPE;
		static int done;
		BitSlicer() : FunctionPass(ID) {}
		
		BasicBlock *orthStartBlock = nullptr;
		Value *orthDescription;
/*		std::vector<LoadInst *> LoadInstBuff;
		std::vector<GetElementPtrInst *> GEPInstBuff;
		
		std::vector<StringRef> AllocNames;
		std::vector<StringRef> LoadNames;
		std::vector<StringRef> GEPNames;
*/		
		bool runOnFunction(Function &F){
		//	int i;
			for(BasicBlock& B : F){
				for(Instruction& I : B){
					IRBuilder<> builder(&I);
					if(auto *call = dyn_cast<CallInst>(&I)){
						Function *Fn = call->getCalledFunction();
						if(Fn && Fn->getIntrinsicID() == Intrinsic::bitslice_i32){
					//		errs() << "args: \n" << call->getNumArgOperands() << "\n";
							
							if(!BitSlice(call, I.getModule()->getContext())){
								errs() << "bitslicing failed\n";
								}
							eraseList.push_back(&I);
							done = 1;
							
						}else if(Fn && Fn->getIntrinsicID() == Intrinsic::unbitslice_i32){
					//		errs() << "args: \n" << call->getNumArgOperands() << "\n";
							
							if(!UnBitSlice(call, I.getModule()->getContext())){
								errs() << "unbitslicing failed\n";
								}
							eraseList.push_back(&I);
							done = 1;
							
						}else if(Fn && Fn->getIntrinsicID() == Intrinsic::start_bitslice){
							
							orthStartBlock = B.splitBasicBlock(&I, "START_ORTHO");
							orthDescription = call->getArgOperand(1);
						//	StartOrthogonalTransformation(call, orthStartBlock);
							
						}else if(Fn && Fn->getIntrinsicID() == Intrinsic::end_bitslice){
							
							EndOrthogonalTransformation(call, orthStartBlock, 
														B.splitBasicBlock(&I, "END_ORTHO"),
														orthDescription);
						}
					}
					
					if(I.getMetadata("bitsliced")){
						
						for(auto& U : I.uses()){
							User *user = U.getUser();
							//user->dump();
							auto *Inst = dyn_cast<Instruction>(user);
							MDNode *mdata = MDNode::get(I.getContext(), 
														MDString::get(I.getContext(), "bitsliced"));
							Inst->setMetadata("bitsliced", mdata);
						}
						
					//	errs() << "marked instruction: ";
					//	I.dump();
						
						if(auto *all = dyn_cast<AllocaInst>(&I)){
							AllocaInst *ret;
							MDNode *MData = MDNode::get(all->getContext(), 
														MDString::get(all->getContext(), "bitsliced"));
						//	Value *size = 0;
							/*
							if(auto *arrTy = dyn_cast<ArrayType>(all->getAllocatedType())){
								size = ConstantInt::get(IntegerType::getInt64Ty(I.getModule()->getContext()),
														arrTy->getArrayNumElements());
								}
								*/
							ArrayType *arrTy;
							//Type *sliceTy = IntegerType::getInt32Ty(I.getContext());
						
							if(isa<ArrayType>(all->getAllocatedType()))
								arrTy = ArrayType::get(all->getAllocatedType()->getArrayElementType(),
																  all->getAllocatedType()->getArrayNumElements()*8*CPU_BYTES);
							else
								arrTy = ArrayType::get(all->getAllocatedType(), 8*CPU_BYTES*SENSIBLE_DATA_BYTES);
							
							
							ret = builder.CreateAlloca(arrTy, 0, "bsliced");
							ret->setMetadata("bitsliced", MData);
							AllocaInst *fakeAlloc = new AllocaInst(all->getAllocatedType(), 0, all->getName());
							fakeAlloc->setMetadata("bitsliced", MData);
							all->replaceAllUsesWith(fakeAlloc);
							AllocOldNames.push_back(fakeAlloc->getName());
							AllocNewInstBuff.push_back(ret);
							eraseList.push_back(&I);
							done = 1;
						}	
						
						
						if(auto *st = dyn_cast<StoreInst>(&I)){
						//	bool IsBitSlicedVal = false;
							bool IsBitSlicedPtr = false;
							int i = 0;
							int j = 0;
							if(auto *stPtr = dyn_cast<Instruction>(st->getPointerOperand())){
								if(stPtr->getMetadata("bitsliced"))	
									IsBitSlicedPtr = true;			
							}					
						/*	if(auto *stVal = dyn_cast<Instruction>(st->getValueOperand())){
								if(stVal->getMetadata("bitsliced"))
									IsBitSlicedVal = true;
							}
						*/	
							if(IsBitSlicedPtr){
								Type *sliceTy = IntegerType::getInt8Ty(I.getModule()->getContext());	//FIXME:SENSIBLE DATA TYPE SELECTABLE?
								Type *idxTy = IntegerType::getInt64Ty(I.getModule()->getContext());
								Value *bitMaskInit = ConstantInt::get(sliceTy, 0x01);
							//	Value *bitIdxAddr = builder.CreateAlloca(sliceTy, 0, "bitIdx");
							//	builder.CreateStore(bitIdxVal, bitIdxAddr, "storeBitIdx");
								
								std::vector<Value *> IdxList;
								Value *init = ConstantInt::get(idxTy, 0);
								Value *bitAddr;
							//	Value *bitIdx;
								Value *bitMask;
								Value *bitAnd;
								Value *slice;
								Value *sliceSize;
								Value *bitBaseIdx;
								Value *bitOffset;
								Value *IDX;
								IdxList.push_back(init);
								IdxList.push_back(init);
								
								if(auto *ptrInst = dyn_cast<GetElementPtrInst>(st->getPointerOperand())){
									j=0;
									
									for(std::vector<StringRef>::iterator allName = AllocOldNames.begin();
																			allName != AllocOldNames.end();
																			allName++, j++){
										if(ptrInst->getPointerOperand()->getName().equals(*allName))
											break;
									}
									for(i=0;i<8*SENSIBLE_DATA_BYTES;i++){
										sliceSize = ConstantInt::get(idxTy, CPU_BYTES*SENSIBLE_DATA_BYTES*8);
										bitBaseIdx = builder.CreateMul(ptrInst->getOperand(2), sliceSize);
										bitOffset = ConstantInt::get(idxTy, CPU_BYTES * i);
										
										IDX = builder.CreateAdd(bitBaseIdx, bitOffset, "IDX");
										//errs() << "rowIdx: ";
										//rowIdx->dump();
										IdxList.at(1) = IDX;
										//errs() << "arraynumelem: " << cast<AllocaInst>(ptrInst->getPointerOperand())
										//									->getAllocatedType()
										//									->getArrayNumElements() << "\n";
										
								//		bitIdx = builder.CreateLoad(bitIdxAddr, "loadBitIdx");
										bitMask = builder.CreateShl(bitMaskInit, ConstantInt::get(sliceTy, i));
										bitAnd = builder.CreateAnd(st->getValueOperand(), bitMask, "applyMask");
								//		builder.CreateStore(bitIdx, bitIdxAddr, "storeBitIdx");
										slice = builder.CreateLShr(bitAnd, ConstantInt::get(sliceTy, i), "sliceReady");
										
										bitAddr = builder.CreateInBoundsGEP(AllocNewInstBuff.at(j), 
																	ArrayRef <Value *>(IdxList));
										builder.CreateStore(slice, bitAddr);
									}
									
								//	eraseList.push_back(ptrInst->getPointerOperand());
									eraseList.push_back(&I);
									eraseList.push_back(ptrInst);
									
								}
								
								if(auto *ptrInst = dyn_cast<AllocaInst>(st->getPointerOperand())){
									j=0;
									for(std::vector<StringRef>::iterator allName = AllocOldNames.begin();
																			allName != AllocOldNames.end();
																			allName++, j++){
										if(ptrInst->getName().equals(*allName))
											break;
									}
									
									for(i=0;i<8*SENSIBLE_DATA_BYTES;i++){
										IDX = ConstantInt::get(idxTy, CPU_BYTES * i);
										IdxList.at(1) = IDX;
										
								//		bitIdx = builder.CreateLoad(bitIdxAddr, "loadBitIdx");
										bitMask = builder.CreateShl(bitMaskInit, ConstantInt::get(sliceTy, i));
										bitAnd = builder.CreateAnd(st->getValueOperand(), bitMask, "applyMask");
								//		builder.CreateStore(bitIdx, bitIdxAddr, "storeBitIdx");
										slice = builder.CreateLShr(bitAnd, ConstantInt::get(sliceTy, i), "sliceReady");
										
										bitAddr = builder.CreateInBoundsGEP(AllocNewInstBuff.at(j), 
																	ArrayRef <Value *>(IdxList));
										builder.CreateStore(slice, bitAddr);
									}
									
									eraseList.push_back(&I);
								}
							}
						}
						
						if(auto *ld = dyn_cast<LoadInst>(&I)){
							int i = 0;
							int j = 0;
							
							if(auto *ptrInst = dyn_cast<GetElementPtrInst>(ld->getPointerOperand())){
							//	LoadInst *ret;
								Value *slice;
								Value *IDX;
								Value *bitBaseIdx;
								Value *bitOffset;
								Value *bitAddr;
								Value *bitShift;
								Type *sliceTy = IntegerType::getInt8Ty(I.getModule()->getContext());	//FIXME:SENSIBLE DATA TYPE SELECTABLE?
								Type *idxTy = IntegerType::getInt64Ty(I.getModule()->getContext());
								Value *sliceSize = ConstantInt::get(idxTy, 8*CPU_BYTES*SENSIBLE_DATA_BYTES);
								Value *init = ConstantInt::get(idxTy, 0);
								Value *byteAddr = builder.CreateAlloca(sliceTy, 0, "byte");
								Value *byte = ConstantInt::get(sliceTy, 0);
								builder.CreateStore(byte, byteAddr, "byteAddr");
								std::vector<Value *> IdxList;
								IdxList.push_back(init);
								IdxList.push_back(init);
								
								for(std::vector<StringRef>::iterator allName = AllocOldNames.begin();
																				allName != AllocOldNames.end();
																				allName++, j++){
									if(ptrInst->getPointerOperand()->getName().equals(*allName))
										break;
								}
								
								for(i=0;i<8*SENSIBLE_DATA_BYTES;i++){
									//sliceSize = ConstantInt::get(idxTy, CPU_BYTES*SENSIBLE_DATA_BYTES*8);
									byte = builder.CreateLoad(byteAddr, "loadByte");
									bitBaseIdx = builder.CreateMul(ptrInst->getOperand(2), sliceSize);
							//		errs() << "base idx: ";
							//		bitBaseIdx->dump();
							//		errs() << "allocated elements" << cast<AllocaInst>(AllocNewInstBuff.at(j))->getAllocatedType()->getArrayNumElements() << "\n";
									bitOffset = ConstantInt::get(idxTy, CPU_BYTES*SENSIBLE_DATA_BYTES*i);
									
									IDX = builder.CreateAdd(bitBaseIdx, bitOffset, "IDX");
									IdxList.at(1) = IDX;
						//			errs() << "IDX: ";
						//			IDX->dump();
									
									bitAddr = builder.CreateInBoundsGEP(AllocNewInstBuff.at(j), 
																	ArrayRef <Value *>(IdxList));
									slice = builder.CreateLoad(bitAddr, "slice");
									bitShift = ConstantInt::get(sliceTy, i);
									slice = builder.CreateShl(slice, bitShift);
							//		slice = builder.CreateZExt(slice, IntegerType::getInt32Ty(I.getModule()->getContext()), "sliceZExt");
							//		byte = builder.CreateZExt(byte, IntegerType::getInt32Ty(I.getModule()->getContext()), "byteZExt");
									byte = builder.CreateOr(byte, slice);
							//		byte = builder.CreateTrunc(byte, sliceTy, "byteTrunc");
							//		slice = builder.CreateTrunc(slice, sliceTy, "sliceTrunc");
									builder.CreateStore(byte, byteAddr, "storeByte");
								}
								
								//ret = builder.CreateLoad(byteAddr, "compactLoad");
							//	errs() << "byte users:\n";
							//	for(auto& U : I.uses()){
							//		User *user = U.getUser();
							//		user->dump();
							//	}
							//	errs() << "before replace\n";
								//ld->replaceAllUsesWith(ret);
								ld->setOperand(0, byteAddr);
							//	errs() << "after replace\n";
								//eraseList.push_back(&I);
								eraseList.push_back(ptrInst);
							}
						}
						
					done = 1;
					}
				}
			}
			for(auto &EI: eraseList){
				EI -> eraseFromParent();
			}
			
			if(done)
				return true;
			return false;
		}	//runOnFunction
	};	//class FunctionPass
} //namespace

char BitSlicer::ID = 0;
//int BitSlicer::TYPE_OK = 0;
//int BitSlicer::INSTR_TYPE = 0;
//int BitSlicer::LAST_INSTR_TYPE = 0;
int BitSlicer::done = 0;

static void registerBitSlicerPass(const PassManagerBuilder &,
                         legacy::PassManagerBase &PM) {
  PM.add(new BitSlicer());
}
static RegisterStandardPasses
  RegisterMyPass(PassManagerBuilder::EP_EarlyAsPossible,
registerBitSlicerPass);





