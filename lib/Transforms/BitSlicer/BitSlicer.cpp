#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Constant.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
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
std::vector<Instruction *> OrthEraseList;
std::vector<BasicBlock *> OrthBBEraseList;
std::vector<CallInst *> startSplitPoints;
std::vector<CallInst *> endSplitPoints;
std::vector<CallInst *> BitSliceAlloc;
std::vector<StringRef> Descriptions;
std::vector<StringRef> AllocOldNames;
std::vector<AllocaInst *> AllocNewInstBuff;
std::vector<StringRef> BitSlicedAllocNames;
std::vector<AllocaInst *> BitSlicedAllocInstBuff;



bool GetBitSlicedData(CallInst *call, LLVMContext &Context){
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


bool GetUnBitSlicedData(CallInst *call, LLVMContext &Context){
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


bool BitSlice(CallInst *call, LLVMContext &Context){
	IRBuilder<> builder(call);
/*	
	BasicBlock *Pred = call->getParent();
	BasicBlock *Succ = call->getParent()->splitBasicBlock(call, "for(alloca).end");
	BasicBlock *New = BasicBlock::Create(Context, "for(alloca).cond");
	New->insertInto(call->getFunction(), Succ);
	Pred->getTerminator()->setSuccessor(0, New);
*/		
	Instruction *inputSize = cast<Instruction>(call->getArgOperand(0));
	for(; !isa<AllocaInst>(inputSize); inputSize = cast<Instruction>(inputSize->getOperand(0)));
	AllocaInst *oldAlloca = cast<AllocaInst>(inputSize);
	AllocOldNames.push_back(oldAlloca->getName());
	
	if(!isa<ArrayType>(oldAlloca->getAllocatedType())){
		errs() << "ERROR: argument 1 not a static array\n";
		return false;
	}
	uint64_t oldSize = cast<ArrayType>(oldAlloca->getAllocatedType())->getNumElements();
	MDNode *MData = MDNode::get(Context, 
								MDString::get(Context, "bit-sliced"));
	oldAlloca->setMetadata("bit-sliced", MData);
	//oldAlloca->replaceAllUsesWith(oldAlloca);
	
	Type *sliceTy = IntegerType::getInt32Ty(Context);
	ArrayType *arrTy = ArrayType::get(sliceTy, (oldSize/32)*8);		//FIXME: need to make it type dependant.
	AllocaInst *all = builder.CreateAlloca(arrTy, 0, "SLICES");
	AllocNewInstBuff.push_back(all);
	
	int i, j;
	
	std::vector<Value *> IdxList;
	Type *idxTy = IntegerType::getInt64Ty(Context);
	Value *idxZero = ConstantInt::get(idxTy, 0);
	Value *tmp;
	Value *Byte;
	Value *bitVal;
	IdxList.push_back(idxZero);
	IdxList.push_back(idxZero);
	Value *sliceAddr;
	int BitSizeOfInput = (oldSize/32)*8;
	
	for( i = 0; i < BitSizeOfInput; i++ ){
		IdxList.at(1) = ConstantInt::get(idxTy, i);
		sliceAddr = builder.CreateGEP(all, ArrayRef <Value *>(IdxList), "sliceAddr");
		tmp = ConstantInt::get(sliceTy, 0);	
		for( j = 0; j < 32; j++){				//FIXME: dependant on the target machine
			IdxList.at(1) = ConstantInt::get(idxTy, j*BitSizeOfInput/8+i/8);
			Byte = builder.CreateGEP(oldAlloca, ArrayRef <Value *>(IdxList), "Block");
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



void OrthogonalTransformation(CallInst *call, StringRef Description){
	//StringRef Description = cast<ConstantDataSequential>(cast<User>(cast<User>(call->getArgOperand(1))
	//						->getOperand(0))->getOperand(0))->getAsCString();
	errs() << Description << "\n";
	//BasicBlock *OrthBlock = call->getParent();
	IRBuilder<> builder(call);
	
	Value *DOper, *LOper, *ROper;
	AllocaInst *allDOper, *allLOper, *allROper;
	std::vector<Value *> IdxList;
	Type *idxTy = IntegerType::getInt64Ty(call->getModule()->getContext());
	Value *idxZero = ConstantInt::get(idxTy, 0);
	IdxList.push_back(idxZero);
	IdxList.push_back(idxZero);
	uint64_t arraySize;
	
	StringRef op;
	std::vector<StringRef> tokens;
	std::vector<StringRef> destOperand;
	std::vector<StringRef> leftOperand;
	std::vector<StringRef> rightOperand;
	
	bool preOp, postOp, end, 
		 foundLeftOperand, foundRightOperand, foundDestOperand;
	
	preOp = postOp = end = 
	foundLeftOperand = foundRightOperand = foundDestOperand = false;
	
	size_t i, pos, count;
	for(i=0, pos=0; !end;){
		pos = Description.find(":", i);
		if(pos==0){
			errs() << "error: description can't begin with colon ':'\n";
			return;
		}
		if(pos==StringRef::npos){
	//	errs() << "end: i, pos: " << i << " " << pos << "\n";
			if(!i){	
				errs() << "error: expected colon ':' to separate the tokens of the description\n";
				return;
			}else{
				pos = Description.size();
				
			//	errs() << "end: i, pos: " << i << " " << pos << " " << Description.back() << "\n";
				tokens.push_back(Description.substr(i, pos-i));
				end = true;
				continue;
			}
		}
		if((pos-i) == 0){
				i++;
			//if(hasDestination && hasFirstOperand){
				if(!preOp){
					preOp = true;
			//	if(!postOp){
					pos = Description.find(":", i);
					op = Description.substr(i, pos-i);
					tokens.push_back("-");
					i = pos+1;
					pos = Description.find(":", i);
				}if((pos-i) == 0){
					i++;
					postOp = true;
				}else{
					//errs() << "i, pos: " << i << " " << pos << "\n";
					errs() << "error: found too many uses of '::' separator\n";
					return;
				}
			/*}else{
				errs() << "error: ";
				if(hasFirstOperand){
					errs() << "no destination\n";
					return;
				}
				
				if(hasDestination){
					errs() << "no left operand\n";
					return;
				}
				
				errs() << "no destination and no left operand\n";
				return;
			}*/
		}else{
			tokens.push_back(Description.substr(i, pos-i));
		//	errs() << Description.substr(i, pos-i) << " - " << i << "\n";
			i = pos+1;
		}
	}
	

	for(i=0; !tokens.at(i).equals("="); i++){
		if(i>3){
			errs() << "error: too many arguments for the left member of the assignement\n";
			return;
		}
		destOperand.push_back(tokens.at(i));
	}
	i++;
	count = i;

	if(count<3){
		errs() << "error: too few arguments for the left member of the assignement\n";
		return;
	}
		
	for(; !tokens.at(i).equals("-"); i++){
		if((i-count) > 3){
			errs() << "error: too many arguments for the left operand\n";
			return;
		}
		leftOperand.push_back(tokens.at(i));
	}

	if((i-count) < 2){
		errs() << "error: too few arguments for the left operand\n";
		return;
	}
	i++;
	count = i;
	for(; i<tokens.size(); i++){
		if((i-count) > 3){
			errs() << "error: too many arguments for the right operand\n";
			return;
		}
		rightOperand.push_back(tokens.at(i));
	}
	
	if((i-count) < 2){
		errs() << "error: too few arguments for the right operand\n";
		return;
	}	
	
	for(auto s : tokens){
		errs() << s << "\n";
	}
	
/*----------------------------------------XOR---------------------------------------*/	
	
	if(op.equals("^")){
		for(i=0; i<AllocOldNames.size(); i++){
			if(AllocOldNames.at(i).equals(leftOperand.at(0))){
				allLOper = cast<AllocaInst>(AllocNewInstBuff.at(i));
				allLOper->getType()->dump();
				foundLeftOperand = true;
			}
			if(AllocOldNames.at(i).equals(rightOperand.at(0))){
				allROper = cast<AllocaInst>(AllocNewInstBuff.at(i));
				allROper->getType()->dump();
				foundRightOperand = true;
			}
			if(AllocOldNames.at(i).equals(destOperand.at(0))){
				allDOper = cast<AllocaInst>(AllocNewInstBuff.at(i));
				allDOper->getType()->dump();
				foundDestOperand = true;
			}
			if(foundLeftOperand && foundRightOperand && foundDestOperand) break;
		}
	
		if(leftOperand.at(1).equals("all") && rightOperand.at(1).equals("all")){	//all ^ all
				arraySize = cast<ArrayType>(allLOper->getAllocatedType())->getNumElements();
				
				if(arraySize != cast<ArrayType>(allLOper->getAllocatedType())->getNumElements()){
					errs() << "error: operation addressing all of the bits of operands of different size\n";
					return;
				}
				if(arraySize > cast<ArrayType>(allDOper->getAllocatedType())->getNumElements()){
					errs() << "error: assignement to variable of insufficient size\n";
					return;
				}
				
				for(i=0; i<arraySize; i++){
					IdxList.at(0) = ConstantInt::get(idxTy, i);
					LOper = builder.CreateGEP(allLOper, ArrayRef <Value *>(IdxList), "LOper");
					LOper = builder.CreateLoad(LOper);
					ROper = builder.CreateGEP(allROper, ArrayRef <Value *>(IdxList), "ROper");
					ROper = builder.CreateLoad(ROper);
					DOper = builder.CreateGEP(allDOper, ArrayRef <Value *>(IdxList), "DOper");
					
					Value *res = builder.CreateXor(LOper, ROper, "Xor");
					
					builder.CreateStore(res, DOper, "storeXor");
				}
		}
	}
	
}

/*
void EndOrthogonalTransformation(BasicBlock *startBlock, 
								 BasicBlock *endBlock,
								 StringRef Description){
errs() << __LINE__ << "\n";
	
	bool stop = false;
	LoopInfoBase<BasicBlock, Loop> *CheckLoops = new LoopInfoBase<BasicBlock, Loop>();
errs() << __LINE__ << "\n";
	std::vector<BasicBlock *> BlockList;
	BlockList.push_back(startBlock);
	Function *Func = startBlock->getParent();
	for (Function::iterator b = Func->begin(); startBlock != &BB; b++) {
		BasicBlock &BB = *b;
	}
	
	for (; BB != *endBlock; b++){
		BB = *b;
		BB.dump();
		BlockList.push_back(&BB);
	}
*/	
/*
		if (CheckLoops->isLoopHeader(&BB))
				errs() << "Looooop\n";
errs() << __LINE__ << "\n";
		const TerminatorInst *TInst = BB.getTerminator();
		for (unsigned it = 0, NSucc = TInst->getNumSuccessors(); it < NSucc; ++it) {
			BasicBlock *Succ = TInst->getSuccessor(it);
			
			BB.dump();
			if (CheckLoops->isLoopHeader(Succ))
				errs() << "Looooop\n";
			if (Succ != endBlock)
				BlockList.push_back(Succ);
		}
		
		BB = *(TInst->getSuccessor(0));
	}
*/
/*
errs() << __LINE__ << "\n";	
	auto CExtr = new CodeExtractor(ArrayRef <BasicBlock *>(BlockList));
errs() << __LINE__ << "\n";	
	Function *NewFunc = CExtr->extractCodeRegion();
errs() << __LINE__ << "\n";	
	//NewFunc->deleteBody();
	
	//BasicBlock *entry = BasicBlock::Create(call->getModule()->getContext(), "entry", NewFunc);
	//IRBuilder<> builder(entry);
	
	
	//for(; token = ParseDescription(Description);)
}
*/


namespace{
	
	struct BitSlicer : public ModulePass{
		static char ID;
		//static int TYPE_OK;
//		static int INSTR_TYPE;
//		static int LAST_INSTR_TYPE;
		static int done;
		BitSlicer() : ModulePass(ID) {}
		
		BasicBlock *orthStartBlock = nullptr, *orthEndBlock = nullptr;
		Value *orthDescription;
		bool OrthErase = false;
		bool OrthBBErase = false;
		bool SameBlock = false;
/*		std::vector<LoadInst *> LoadInstBuff;
		std::vector<GetElementPtrInst *> GEPInstBuff;
		
		std::vector<StringRef> AllocNames;
		std::vector<StringRef> LoadNames;
		std::vector<StringRef> GEPNames;
*/
			
		bool runOnModule(Module &M) override {
		//	int i;
		
//		errs() << __LINE__ << "\n";
		for(Function& F : M){
			for(BasicBlock& B : F){
				
	//		B.dump();
				for(Instruction& I : B){
					if(OrthErase)
						OrthEraseList.push_back(&I);
					IRBuilder<> builder(&I);
					if(auto *call = dyn_cast<CallInst>(&I)){
						Function *Fn = call->getCalledFunction();
						if(Fn && Fn->getIntrinsicID() == Intrinsic::getbitsliced_i32){
							if(!GetBitSlicedData(call, I.getModule()->getContext())){
								errs() << "bit-slicing failed\n";
								}
							eraseList.push_back(&I);
							done = 1;
							
						}else if(Fn && Fn->getIntrinsicID() == Intrinsic::getunbitsliced_i32){
					//		errs() << "args: \n" << call->getNumArgOperands() << "\n";
							
							if(!GetUnBitSlicedData(call, I.getModule()->getContext())){
								errs() << "bit-slicing inversion failed\n";
								}
							eraseList.push_back(&I);
							done = 1;
						}else if(Fn && Fn->getIntrinsicID() == Intrinsic::bitslice_i32){
					//		errs() << "args: \n" << call->getNumArgOperands() << "\n";
							BitSliceAlloc.push_back(call);
							if(!BitSlice(call, I.getModule()->getContext())){
								errs() << "bit-slicing failed\n";
							}
							
							eraseList.push_back(&I);
							done = 1;	
						}else if(Fn && Fn->getIntrinsicID() == Intrinsic::start_bitslice){
							MDNode *MData = MDNode::get(I.getModule()->getContext(), 
								MDString::get(I.getModule()->getContext(), "start-orthogonalization"));
							call->setMetadata("start-orthogonalization", MData);
							startSplitPoints.push_back(call);
							Descriptions.push_back(cast<ConstantDataSequential>(cast<User>(cast<User>(call->getArgOperand(1))
													->getOperand(0))->getOperand(0))->getAsCString());
			//		errs() << __LINE__ << "\n";
						
						//	OrthogonalTransformation(call);
							OrthErase = true;
							eraseList.push_back(&I);				
						}else if(Fn && Fn->getIntrinsicID() == Intrinsic::end_bitslice){
							MDNode *MData = MDNode::get(I.getModule()->getContext(), 
								MDString::get(I.getModule()->getContext(), "stop-orthogonalization"));
							call->setMetadata("stop-orthogonalization", MData);
							endSplitPoints.push_back(call);
							OrthEraseList.pop_back();
//					errs() << __LINE__ << "\n";
							OrthErase = false;
							eraseList.push_back(&I);
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
				}//I : B
			}//B : F
			
			
			
			}//F : M
		/*	
			for(auto &SSP: startSplitPoints){
				StringRef StartName = cast<ConstantDataSequential>(cast<User>(cast<User>(SSP->getArgOperand(0))
															->getOperand(0))->getOperand(0))->getAsCString();
				orthStartBlock = SSP->getParent()->splitBasicBlock(SSP, Twine(StartName));
				
				for(auto &ESP: endSplitPoints){
					StringRef EndName = cast<ConstantDataSequential>(cast<User>(cast<User>(SSP->getArgOperand(0))
															->getOperand(0))->getOperand(0))->getAsCString();
					if(StartName.equals(EndName)){
						EndName = StringRef(EndName.str()+"_END");
						orthEndBlock = ESP->getParent()->splitBasicBlock(ESP, Twine(EndName));
						StringRef Descr = cast<ConstantDataSequential>(cast<User>(cast<User>(SSP->getArgOperand(1))
															->getOperand(0))->getOperand(0))->getAsCString();
						errs() << Descr << "\n";
						EndOrthogonalTransformation(orthStartBlock, orthEndBlock, Descr);
					}
				}
			}
		*/
			
			
			for(auto& ESP : endSplitPoints){
				for(auto& SSP : startSplitPoints){
					StringRef StartName = cast<ConstantDataSequential>(cast<User>(cast<User>(SSP->getArgOperand(0))
												->getOperand(0))->getOperand(0))->getAsCString();
						
					StringRef EndName = cast<ConstantDataSequential>(cast<User>(cast<User>(ESP->getArgOperand(0))
												->getOperand(0))->getOperand(0))->getAsCString();
		//		errs() << __LINE__ << "\n";		
					if(EndName.equals(StartName)){
					//SSP->getParent()->dump();
					//ESP->getParent()->dump();
		//		errs() << __LINE__ << "\n";	
						if(ESP->getParent() != SSP->getParent()){
							BasicBlock *Pred = SSP->getParent();
							orthStartBlock = SSP->getParent()->splitBasicBlock(SSP);
							orthEndBlock = ESP->getParent()->splitBasicBlock(ESP);
							Pred->getTerminator()->setSuccessor(0, orthEndBlock);
		//			errs() << __LINE__ << "\n";
						}
					
					}
					
				}
			}	
			
			
			
			for(auto &OEI: OrthEraseList){
				if(!OEI->use_empty())	
					OEI->replaceAllUsesWith(UndefValue::get(OEI->getType()));
				OEI -> eraseFromParent();
			}
		
			for(Function& F : M){
				for(BasicBlock& B : F){
					if(OrthBBErase)
							OrthBBEraseList.push_back(&B);
					for(Instruction& I : B){
						if(I.getMetadata("start-orthogonalization")){
						//	OrthBBEraseList.push_back(&B);
						//	OrthogonalTransformation(cast<CallInst>(&I));
							OrthBBErase = true;
						}
						if(I.getMetadata("stop-orthogonalization")){
							OrthBBEraseList.pop_back();
							OrthBBErase = false;
						}
					}
				}
			}
			
			for(auto &EB: OrthBBEraseList){
				EB -> eraseFromParent();
			}
			
			for(auto& ESP : endSplitPoints){
				StringRef EndName = cast<ConstantDataSequential>(cast<User>(cast<User>(ESP->getArgOperand(0))
																->getOperand(0))->getOperand(0))->getAsCString();
				for(auto& SSP : startSplitPoints){
					StringRef StartName = cast<ConstantDataSequential>(cast<User>(cast<User>(SSP->getArgOperand(0))
																	->getOperand(0))->getOperand(0))->getAsCString();
					
					if(EndName.equals(StartName)){
						StringRef Descr = cast<ConstantDataSequential>(cast<User>(cast<User>(SSP->getArgOperand(1))
																	->getOperand(0))->getOperand(0))->getAsCString();
						OrthogonalTransformation(ESP, Descr);
						SSP->getParent()->eraseFromParent();
		//				errs() << __LINE__ << "\n";	
					}
				}
			}
	
/*		
			for(Function& F : M){
				for(BasicBlock& B : F){
					B.dump();
				}
			}
*/	//errs() << __LINE__ << "\n";			
			for(auto &EI: eraseList){
				if(EI->getParent() != nullptr)
					EI -> eraseFromParent();
			}
	//errs() << __LINE__ << "\n";			
			if(done)
				return true;
			return false;
			
		}	//runOnModule
	};	//class ModulePass
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
  RegisterMyPass(PassManagerBuilder::EP_ModuleOptimizerEarly,
registerBitSlicerPass);

static RegisterStandardPasses
  RegisterMyPass0(PassManagerBuilder::EP_EnabledOnOptLevel0,
registerBitSlicerPass);



