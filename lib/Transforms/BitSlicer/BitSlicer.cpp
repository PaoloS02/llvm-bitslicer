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
std::vector<CallInst *> emitPoints;
std::vector<CallInst *> startSplitPoints;
std::vector<CallInst *> endSplitPoints;
std::vector<CallInst *> BitSliceAlloc;
std::vector<CallInst *> UnBitSliceCalls;
std::vector<StringRef> Descriptions;
std::vector<StringRef> AllocOldNames;
std::vector<AllocaInst *> AllocInstBuff;
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
	uint64_t blocks = cast<ConstantInt>(call->getArgOperand(1))->getZExtValue();
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
	
	MDNode *MData;
	if(blocks > 1){
		MData = MDNode::get(Context, 
							MDString::get(Context, "bit-sliced-multi"));
		oldAlloca->setMetadata("bit-sliced-m", MData);
	}else if(blocks == 1){
		MData = MDNode::get(Context, 
							MDString::get(Context, "bit-sliced"));
		oldAlloca->setMetadata("bit-sliced", MData);
	}
	
	//oldAlloca->replaceAllUsesWith(oldAlloca);
	
	Type *sliceTy = IntegerType::getInt32Ty(Context);
	ArrayType *arrTy;
	arrTy = ArrayType::get(sliceTy, (oldSize/blocks)*8);		//FIXME: need to make it type dependant.
	
	AllocaInst *all = builder.CreateAlloca(arrTy, 0, "SLICES");
	AllocNewInstBuff.push_back(all);
	
	//int i, j;
	
	std::vector<Value *> IdxList;
	Type *idxTy = IntegerType::getInt64Ty(Context);
	Value *idxZero = ConstantInt::get(idxTy, 0);
	IdxList.push_back(idxZero);
	IdxList.push_back(idxZero);
	Value *tmp;
	Value *Byte;
	Value *bitVal;
	Value *sliceAddr;
	int BitSizeOfInput = (oldSize/blocks)*8;

if(blocks > 1){			//FIXME: ADD THIS WARNING IN THE DOCUMENTATION: if a different size of the program dependent on the number of blocks processed in parallel is not an issue and you want more efficiency you'd better specify that you use just 1 block. If the different size of the program is an issue you should put always 32 as number of blocks (or the maximum value you use in your program). In that case, ALLOCATE FOR 32 BLOCKS AS WELL, AND FILL THE REMAINING SPACE WITH ZEROS!!

	AllocaInst *idxAlloca = builder.CreateAlloca(idxTy, 0, "idx_i");
	AllocaInst *idx2Alloca = builder.CreateAlloca(idxTy, 0, "idx_j");
	AllocaInst *tmpAlloca = builder.CreateAlloca(sliceTy, 0, "tmp");
	builder.CreateStore(idxZero, idxAlloca);
	builder.CreateStore(idxZero, idx2Alloca);
	BasicBlock *forEnd = call->getParent()->splitBasicBlock(call, "for.end");
	
	BasicBlock *forCond = BasicBlock::Create(Context, "for.cond", call->getFunction(), forEnd);
	idxAlloca->getParent()->getTerminator()->setSuccessor(0, forCond);

	IRBuilder<> forCondBuilder(forCond);
	Value *idx = forCondBuilder.CreateLoad(idxAlloca);
	Value *cmp = forCondBuilder.CreateICmpSLT(idx, ConstantInt::get(idxTy, BitSizeOfInput), "cmp");
	BasicBlock *forBody = BasicBlock::Create(Context, "for.body", call->getFunction(), forEnd);
	forCondBuilder.CreateCondBr(cmp, forBody, forEnd);
	
	IRBuilder<> forBodyBuilder(forBody);
	forBodyBuilder.CreateStore(ConstantInt::get(sliceTy, 0), tmpAlloca);
	forBodyBuilder.CreateStore(idxZero, idx2Alloca);
	idx = forBodyBuilder.CreateLoad(idxAlloca, "idxprom");
	IdxList.at(1) = idx;
	sliceAddr = forBodyBuilder.CreateGEP(all, ArrayRef <Value *>(IdxList), "sliceAddr");
	BasicBlock *forCond2 = BasicBlock::Create(Context, "for.cond", call->getFunction(), forEnd);
	forBodyBuilder.CreateBr(forCond2);
	
	IRBuilder<> forCond2Builder(forCond2);
	Value *idx2 = forCond2Builder.CreateLoad(idx2Alloca);
	Value *cmp2 = forCond2Builder.CreateICmpSLT(idx2, ConstantInt::get(idxTy, blocks), "cmp");
	BasicBlock *forBody2 = BasicBlock::Create(Context, "for.body", call->getFunction(), forEnd);
	BasicBlock *forEnd2 = BasicBlock::Create(Context, "for.end", call->getFunction(), forEnd);
	forCond2Builder.CreateCondBr(cmp2, forBody2, forEnd2);
//	
	IRBuilder<> forBody2Builder(forBody2);
	idx = forBody2Builder.CreateLoad(idxAlloca, "idxprom");
	Value *div = forBody2Builder.CreateSDiv(idx, ConstantInt::get(idxTy, 8), "div"); //coloumn i = 0, 1,... #input-elements
	idx2 = forBody2Builder.CreateLoad(idx2Alloca, "idxprom");
	//Value *div2 = forBody2Builder.CreateSDiv(idx2, ConstantInt::get(idxTy, 8), "div");
	Value *mul = forBody2Builder.CreateNSWMul(idx2, ConstantInt::get(idxTy, BitSizeOfInput/8), "mul"); //row j*sizeof(row)
	Value *add = forBody2Builder.CreateNSWAdd(div, mul, "add");
	IdxList.at(1) = add;
	Byte = forBody2Builder.CreateGEP(oldAlloca, ArrayRef <Value *>(IdxList));
	Byte = forBody2Builder.CreateLoad(Byte);
	tmp = forBody2Builder.CreateLoad(tmpAlloca);
	bitVal = forBody2Builder.CreateZExt(Byte, sliceTy);
	Value *bitShift = forBody2Builder.CreateSRem(idx, ConstantInt::get(idxTy, 8));
	bitShift = forBody2Builder.CreateTrunc(bitShift, sliceTy);
	bitVal = forBody2Builder.CreateLShr(bitVal, bitShift);
	bitVal = forBody2Builder.CreateAnd(bitVal, ConstantInt::get(sliceTy, 1));
	Value *blockShift = forBody2Builder.CreateTrunc(idx2, sliceTy);
	bitVal = forBody2Builder.CreateShl(bitVal, blockShift);
	tmp = forBody2Builder.CreateOr(tmp, bitVal);
	forBody2Builder.CreateStore(tmp, tmpAlloca);
	BasicBlock *forInc2 = BasicBlock::Create(Context, "for.inc", call->getFunction(), forEnd2);
	forBody2Builder.CreateBr(forInc2);
	
	IRBuilder<> forInc2Builder(forInc2);
	Value *inc2 = forInc2Builder.CreateLoad(idx2Alloca);
	inc2 = forInc2Builder.CreateNSWAdd(inc2, ConstantInt::get(idxTy, 1), "inc");
	forInc2Builder.CreateStore(inc2, idx2Alloca);
	forInc2Builder.CreateBr(forCond2);
	
	IRBuilder<> forEnd2Builder(forEnd2);
	Value *newSlice = forEnd2Builder.CreateLoad(tmpAlloca);
	forEnd2Builder.CreateStore(newSlice, sliceAddr);
	BasicBlock *forInc = BasicBlock::Create(Context, "for.inc", call->getFunction(), forEnd);
	forEnd2Builder.CreateBr(forInc);
	
	IRBuilder<> forIncBuilder(forInc);
	Value *inc = forIncBuilder.CreateLoad(idxAlloca);
	inc = forIncBuilder.CreateNSWAdd(inc, ConstantInt::get(idxTy, 1), "inc");
	forIncBuilder.CreateStore(inc, idxAlloca);
	forIncBuilder.CreateBr(forCond);

}else if(blocks == 1){
	
	AllocaInst *idxAlloca = builder.CreateAlloca(idxTy, 0, "idx_i");
	AllocaInst *idx2Alloca = builder.CreateAlloca(idxTy, 0, "idx_j");
	builder.CreateStore(idxZero, idxAlloca);
	builder.CreateStore(idxZero, idx2Alloca);
	BasicBlock *forEnd = call->getParent()->splitBasicBlock(call, "for.end");
	
	BasicBlock *forCond = BasicBlock::Create(Context, "for.cond", call->getFunction(), forEnd);
	idxAlloca->getParent()->getTerminator()->setSuccessor(0, forCond);

	IRBuilder<> forCondBuilder(forCond);
	Value *idx = forCondBuilder.CreateLoad(idxAlloca);
	Value *cmp = forCondBuilder.CreateICmpSLT(idx, ConstantInt::get(idxTy, BitSizeOfInput/8), "cmp");
	BasicBlock *forBody = BasicBlock::Create(Context, "for.body", call->getFunction(), forEnd);
	forCondBuilder.CreateCondBr(cmp, forBody, forEnd);
	
	IRBuilder<> forBodyBuilder(forBody);
	idx = forBodyBuilder.CreateLoad(idxAlloca, "idxprom");
	//Value *div = forBodyBuilder.CreateSDiv(idx, ConstantInt::get(idxTy, 8), "div"); //8, #bits per element
	IdxList.at(1) = idx;
	Byte = forBodyBuilder.CreateGEP(oldAlloca, ArrayRef <Value *>(IdxList));
	Byte = forBodyBuilder.CreateLoad(Byte);
	bitVal = forBodyBuilder.CreateZExt(Byte, sliceTy);
	forBodyBuilder.CreateStore(idxZero, idx2Alloca);
	BasicBlock *forCond2 = BasicBlock::Create(Context, "for.cond", call->getFunction(), forEnd);
	forBodyBuilder.CreateBr(forCond2);
	
	IRBuilder<> forCond2Builder(forCond2);
	Value *idx2 = forCond2Builder.CreateLoad(idx2Alloca);
	Value *cmp2 = forCond2Builder.CreateICmpSLT(idx2, ConstantInt::get(idxTy, 8), "cmp");	//8, #bits per element
	BasicBlock *forBody2 = BasicBlock::Create(Context, "for.body", call->getFunction(), forEnd);
	BasicBlock *forEnd2 = BasicBlock::Create(Context, "for.end", call->getFunction(), forEnd);
	forCond2Builder.CreateCondBr(cmp2, forBody2, forEnd2);
	
	IRBuilder<> forBody2Builder(forBody2);
	//Value *bitShift = forBody2Builder.CreateSRem(idx, ConstantInt::get(idxTy, 8));
	idx2 = forBody2Builder.CreateLoad(idx2Alloca);
	Value *bitShift = forBody2Builder.CreateTrunc(idx2, sliceTy);
	bitVal = forBody2Builder.CreateLShr(bitVal, bitShift);
	bitVal = forBody2Builder.CreateAnd(bitVal, ConstantInt::get(sliceTy, 1));
	IdxList.at(1) = idx2;
	sliceAddr = forBody2Builder.CreateGEP(all, ArrayRef <Value *>(IdxList), "sliceAddr");
	forBody2Builder.CreateStore(bitVal, sliceAddr);
	BasicBlock *forInc2 = BasicBlock::Create(Context, "for.inc", call->getFunction(), forEnd2);
	forBody2Builder.CreateBr(forInc2);
	
	IRBuilder<> forInc2Builder(forInc2);
	Value *inc2 = forInc2Builder.CreateLoad(idx2Alloca);
	inc2 = forInc2Builder.CreateNSWAdd(inc2, ConstantInt::get(idxTy, 1), "inc");
	forInc2Builder.CreateStore(inc2, idx2Alloca);
	forInc2Builder.CreateBr(forCond2);
	
	IRBuilder<> forEnd2Builder(forEnd2);
	//Value *newSlice = forEnd2Builder.CreateLoad(tmpAlloca);
	//forEnd2Builder.CreateStore(newSlice, sliceAddr);
	BasicBlock *forInc = BasicBlock::Create(Context, "for.inc", call->getFunction(), forEnd);
	forEnd2Builder.CreateBr(forInc);
	
	IRBuilder<> forIncBuilder(forInc);
	Value *inc = forIncBuilder.CreateLoad(idxAlloca);
	inc = forIncBuilder.CreateNSWAdd(inc, ConstantInt::get(idxTy, 1), "inc");
	forIncBuilder.CreateStore(inc, idxAlloca);
	forIncBuilder.CreateBr(forCond);
}

/*	
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
*/	

	return true;
}


bool UnBitSlice(CallInst *call, LLVMContext &Context){
	Instruction *input = cast<Instruction>(call->getArgOperand(0));
	for(; !isa<AllocaInst>(input); input = cast<Instruction>(input->getOperand(0)));
	AllocaInst *oldAlloca = cast<AllocaInst>(input);
	int i=0;
	for(auto name : AllocOldNames){
		if(oldAlloca->getName().equals(name)){
			break;
		}
		i++;
	}
	
	AllocaInst *slicesAlloca = AllocNewInstBuff.at(i);
	
	std::vector<Value *> IdxList;
	Type *idxTy = IntegerType::getInt64Ty(Context);
	Value *idxZero = ConstantInt::get(idxTy, 0);
	IdxList.push_back(idxZero);
	IdxList.push_back(idxZero);
	
	if(!isa<ArrayType>(oldAlloca->getAllocatedType())){
		errs() << "ERROR: argument 1 not a static array\n";
		return false;
	}
	uint64_t oldSize = cast<ArrayType>(oldAlloca->getAllocatedType())->getNumElements();
	int ByteSizeOfOutput = oldSize/32;
	Type *byteTy = IntegerType::getInt8Ty(Context);
	
	IRBuilder<> builder(call);
	AllocaInst *idxAlloca = builder.CreateAlloca(idxTy, 0, "idx_i");
	AllocaInst *idx2Alloca = builder.CreateAlloca(idxTy, 0, "idx_j");
	AllocaInst *tmpAlloca = builder.CreateAlloca(byteTy, 0, "tmp");
	builder.CreateStore(idxZero, idxAlloca);
	//builder.CreateStore(idxZero, idx2Alloca);
	BasicBlock *forEnd = call->getParent()->splitBasicBlock(call, "for.end");
	BasicBlock *forCond = BasicBlock::Create(Context, "for.cond", call->getFunction(), forEnd);
	idxAlloca->getParent()->getTerminator()->setSuccessor(0, forCond);

	IRBuilder<> forCondBuilder(forCond);
	Value *idx = forCondBuilder.CreateLoad(idxAlloca);
	Value *cmp = forCondBuilder.CreateICmpSLT(idx, ConstantInt::get(idxTy, ByteSizeOfOutput*32), "cmp");
	BasicBlock *forBody = BasicBlock::Create(Context, "for.body", call->getFunction(), forEnd);
	forCondBuilder.CreateCondBr(cmp, forBody, forEnd);
	
	IRBuilder<> forBodyBuilder(forBody);
	forBodyBuilder.CreateStore(idxZero, idx2Alloca);
	forBodyBuilder.CreateStore(ConstantInt::get(byteTy, 0), tmpAlloca);
	BasicBlock *forCond2 = BasicBlock::Create(Context, "for.cond", call->getFunction(), forEnd);
	forBodyBuilder.CreateBr(forCond2);
	
	IRBuilder<> forCond2Builder(forCond2);
	Value *idx2 = forCond2Builder.CreateLoad(idx2Alloca);
	Value *cmp2 = forCond2Builder.CreateICmpSLT(idx2, ConstantInt::get(idxTy, 8), "cmp");
	BasicBlock *forBody2 = BasicBlock::Create(Context, "for.body", call->getFunction(), forEnd);
	BasicBlock *forEnd2 = BasicBlock::Create(Context, "for.end", call->getFunction(), forEnd);
	forCond2Builder.CreateCondBr(cmp2, forBody2, forEnd2);
	
	IRBuilder<> forBody2Builder(forBody2);
	idx = forBody2Builder.CreateLoad(idxAlloca, "idxprom");
	Value *idxMod = forBody2Builder.CreateSRem(idx, ConstantInt::get(idxTy, ByteSizeOfOutput), "idx_mod");
	Value *idxMul = forBody2Builder.CreateNSWMul(idxMod, ConstantInt::get(idxTy, 8), "idx_mul");
	idx2 = forBody2Builder.CreateLoad(idx2Alloca);
	Value *idxAdd = forBody2Builder.CreateNSWAdd(idxMul, idx2);
	IdxList.at(1) = idxAdd;
	Value *sliceAddr = forBody2Builder.CreateGEP(slicesAlloca, ArrayRef <Value *>(IdxList));
	Value *slice = forBody2Builder.CreateLoad(sliceAddr);
	Value *sliceShift = forBody2Builder.CreateSDiv(idx, ConstantInt::get(idxTy, ByteSizeOfOutput));
	Value *byte = forBody2Builder.CreateZExt(slice, idxTy);
	byte = forBody2Builder.CreateLShr(byte, sliceShift);
	byte = forBody2Builder.CreateAnd(byte, ConstantInt::get(idxTy, 1));
	byte = forBody2Builder.CreateShl(byte, idx2);
	Value *tmp = forBody2Builder.CreateLoad(tmpAlloca);
	byte = forBody2Builder.CreateTrunc(byte, byteTy);
	tmp = forBody2Builder.CreateOr(tmp, byte);
	forBody2Builder.CreateStore(tmp, tmpAlloca);
	BasicBlock *forInc2 = BasicBlock::Create(Context, "for.inc", call->getFunction(), forEnd2);
	forBody2Builder.CreateBr(forInc2);
	
	IRBuilder<> forInc2Builder(forInc2);
	Value *inc2 = forInc2Builder.CreateLoad(idx2Alloca);
	inc2 = forInc2Builder.CreateNSWAdd(inc2, ConstantInt::get(idxTy, 1));
	forInc2Builder.CreateStore(inc2 ,idx2Alloca);
	forInc2Builder.CreateBr(forCond2);
	
	IRBuilder<> forEnd2Builder(forEnd2);
	Value *newByte = forEnd2Builder.CreateLoad(tmpAlloca);
	idx = forEnd2Builder.CreateLoad(idxAlloca, "idxprom");
	IdxList.at(1) = idx;
	Value *byteAddr = forEnd2Builder.CreateGEP(oldAlloca, ArrayRef <Value *>(IdxList), "sliceAddr");
	forEnd2Builder.CreateStore(newByte, byteAddr);
	BasicBlock *forInc = BasicBlock::Create(Context, "for.inc", call->getFunction(), forEnd);
	forEnd2Builder.CreateBr(forInc);
	
	IRBuilder<> forIncBuilder(forInc);
	Value *inc = forIncBuilder.CreateLoad(idxAlloca);
	inc = forIncBuilder.CreateNSWAdd(inc, ConstantInt::get(idxTy, 1));
	forIncBuilder.CreateStore(inc, idxAlloca);
	forIncBuilder.CreateBr(forCond);
	
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
	GlobalVariable *glOper;
	int constOper;
	std::vector<Value *> IdxList;
	LLVMContext &Context = call->getModule()->getContext();
	Type *sliceTy = IntegerType::getInt32Ty(Context);
	Type *idxTy = IntegerType::getInt64Ty(Context);
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
		 foundLeftOperand, foundRightOperand, foundDestOperand,
		 globalRightOperand, constantRightOperand,
		 notBitSlicedLeftOperand, notBitSlicedRightOperand,
		 rangedLeftOperand, rangedRightOperand, rangedDestOperand;
	
	preOp = postOp = end = 
	foundLeftOperand = foundRightOperand = foundDestOperand = 
	globalRightOperand = constantRightOperand = 
	notBitSlicedLeftOperand = notBitSlicedRightOperand = 
	rangedLeftOperand = rangedRightOperand = rangedDestOperand = false;
	
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
/*
	if((i-count) < 2){
		errs() << "error: too few arguments for the left operand\n";
		return;
	}
*/
	i++;
	count = i;
	for(; i<tokens.size(); i++){
		if((i-count) > 3){
			errs() << "error: too many arguments for the right operand\n";
			return;
		}
		rightOperand.push_back(tokens.at(i));
	}
/*	
	if((i-count) < 2){
		errs() << "error: too few arguments for the right operand\n";
		return;
	}	
*/	
	for(auto s : tokens){
		errs() << s << "\n";
	}
	
/*----------------------------------------XOR---------------------------------------*/	
	
	if(op.equals("^")){
		for(i=0; i<AllocOldNames.size(); i++){
			if(AllocOldNames.at(i).equals(leftOperand.at(0))){
				allLOper = cast<AllocaInst>(AllocNewInstBuff.at(i));
				foundLeftOperand = true;
			}
			if(AllocOldNames.at(i).equals(rightOperand.at(0))){
				allROper = cast<AllocaInst>(AllocNewInstBuff.at(i));
				foundRightOperand = true;
			}
			if(AllocOldNames.at(i).equals(destOperand.at(0))){
				allDOper = cast<AllocaInst>(AllocNewInstBuff.at(i));
				foundDestOperand = true;
			}
			if((foundLeftOperand || foundRightOperand) && foundDestOperand) break;
		}
		
		if(!(foundLeftOperand || foundRightOperand)){
			errs() << "warning: trying to transpose an operation with no bit-sliced operands\n";
		}
		
		if(!foundLeftOperand){
			for(i=0; i<AllocInstBuff.size(); i++){
				if(AllocInstBuff.at(i)->getName().equals(leftOperand.at(0))){
					allLOper = cast<AllocaInst>(AllocInstBuff.at(i));
					notBitSlicedLeftOperand = true;
				}
			}
		}
		
		if(!foundRightOperand){
			for(i=0; i<AllocInstBuff.size(); i++){
				if(AllocInstBuff.at(i)->getName().equals(rightOperand.at(0))){
					allROper = cast<AllocaInst>(AllocInstBuff.at(i));
					notBitSlicedRightOperand = true;
				}
			}
		}
		
		if(leftOperand.at(1).equals("all") && rightOperand.at(1).equals("all")){
			arraySize = cast<ArrayType>(allLOper->getAllocatedType())->getNumElements();
				
			if(arraySize != cast<ArrayType>(allROper->getAllocatedType())->getNumElements()){
				errs() << "error: operation addressing all of the bits of operands of different size\n";
				return;
			}
			if(arraySize > cast<ArrayType>(allDOper->getAllocatedType())->getNumElements()){
				errs() << "error: assignement to variable of insufficient size\n";
				return;
			}

			AllocaInst *idxAlloca = builder.CreateAlloca(idxTy, 0, "idx");
			builder.CreateStore(idxZero, idxAlloca);
			BasicBlock *forEnd = call->getParent()->splitBasicBlock(call, "for.end");
	/*		
			if(prevBB != nullptr){
				IRBuilder<> forHeadBuilder(prevBB->getTerminator());
				idxAlloca = forHeadBuilder.CreateAlloca(idxTy, 0, "idx");
				forHeadBuilder.CreateStore(idxZero, idxAlloca);
				forEnd = call->getParent();
				forEnd->setName("for.end");
			}else{
				idxAlloca = builder.CreateAlloca(idxTy, 0, "idx");
				builder.CreateStore(idxZero, idxAlloca);
				forEnd = call->getParent()->splitBasicBlock(call, "for.end");
			}
	*/		
			BasicBlock *forCond = BasicBlock::Create(Context, "for.cond", call->getFunction(), forEnd);
			idxAlloca->getParent()->getTerminator()->setSuccessor(0, forCond);
			
			IRBuilder<> forCondBuilder(forCond);
			Value *idx = forCondBuilder.CreateLoad(idxAlloca, "idx");
			Value *cmp = forCondBuilder.CreateICmpSLT(idx, ConstantInt::get(idxTy, arraySize), "cmp");
			
			BasicBlock *forBody = BasicBlock::Create(Context, "for.body", call->getFunction(), forEnd);
			forCondBuilder.CreateCondBr(cmp, forBody, forEnd);
			
			IRBuilder<> forBodyBuilder(forBody);
			idx = forBodyBuilder.CreateLoad(idxAlloca, "idxprom");
			IdxList.at(1) = idx;
			LOper = forBodyBuilder.CreateGEP(allLOper, ArrayRef <Value *>(IdxList), "LOper");
			LOper = forBodyBuilder.CreateLoad(LOper);
			ROper = forBodyBuilder.CreateGEP(allROper, ArrayRef <Value *>(IdxList), "ROper");
			ROper = forBodyBuilder.CreateLoad(ROper);
			Value *res = forBodyBuilder.CreateXor(LOper, ROper, "xor");
			DOper = forBodyBuilder.CreateGEP(allDOper, ArrayRef <Value *>(IdxList), "DOper");
			forBodyBuilder.CreateStore(res, DOper);
			
			BasicBlock *forInc = BasicBlock::Create(Context, "for.inc", call->getFunction(), forEnd);
			forBodyBuilder.CreateBr(forInc);
			
			IRBuilder<> forIncBuilder(forInc);
			Value *inc = forIncBuilder.CreateLoad(idxAlloca);
			inc = forIncBuilder.CreateNSWAdd(inc, ConstantInt::get(idxTy, 1), "inc");
			forIncBuilder.CreateStore(inc, idxAlloca);
			forIncBuilder.CreateBr(forCond);
		}

//bits are universal, while the element size may depend... why don't we make the user express the range
//in terms of bits?
		uint64_t rangeBeginLOp, rangeEndLOp, rangeBeginROp, rangeEndROp, rangeBeginDOp, rangeEndDOp, range = 0;
		if(leftOperand.at(1).equals("range") || rightOperand.at(1).equals("range")){
			pos = StringRef::npos;
			if(leftOperand.at(1).equals("range"))
				pos = leftOperand.at(2).find(",", 0);		
			if(pos != StringRef::npos){
				rangeBeginLOp = std::stoi(leftOperand.at(2).substr(0, pos).str());
				pos++;
				rangeEndLOp = std::stoi(leftOperand.at(2).substr(pos, leftOperand.at(2).size()-1).str());
				range = rangeEndLOp - rangeBeginLOp + 1;		//first and last bits included
				rangedLeftOperand = true;
			}
			pos = StringRef::npos;
			if(rightOperand.at(1).equals("range"))
				pos = rightOperand.at(2).find(",", 0);		
			if(pos != StringRef::npos){
				rangeBeginROp = std::stoi(rightOperand.at(2).substr(0, pos).str());
				pos++;
				rangeEndROp = std::stoi(rightOperand.at(2).substr(pos, rightOperand.at(2).size()-1).str());
				range = rangeEndROp - rangeBeginROp + 1;
				rangedRightOperand = true;
			}
			pos = StringRef::npos;
			if(destOperand.at(1).equals("range"))
				pos = destOperand.at(2).find(",", 0);		
			if(pos != StringRef::npos){
				rangeBeginDOp = std::stoi(destOperand.at(2).substr(0, pos).str());
				pos++;
				rangeEndDOp = std::stoi(destOperand.at(2).substr(pos, destOperand.at(2).size()-1).str());
				range = rangeEndDOp - rangeBeginDOp + 1;
				rangedDestOperand = true;
			}
			
			if(leftOperand.at(1).equals("range") && rightOperand.at(1).equals("range")){
				if((rangeEndLOp-rangeBeginLOp) != (rangeEndROp-rangeBeginROp)){
					errs() << "error: ranges of different size\n";
					return;
				}
			}
			
			AllocaInst *idxAlloca = builder.CreateAlloca(idxTy, 0, "idx");
			builder.CreateStore(idxZero, idxAlloca);
			BasicBlock *forEnd = call->getParent()->splitBasicBlock(call, "for.end");
	/*		
			if(prevBB != nullptr){
				IRBuilder<> forHeadBuilder(prevBB->getTerminator());
				idxAlloca = forHeadBuilder.CreateAlloca(idxTy, 0, "idx");
				forHeadBuilder.CreateStore(idxZero, idxAlloca);
				forEnd = call->getParent();
				forEnd->setName("for.end");
			}else{
				idxAlloca = builder.CreateAlloca(idxTy, 0, "idx");
				builder.CreateStore(idxZero, idxAlloca);
				forEnd = call->getParent()->splitBasicBlock(call, "for.end");
			}
	*/		
			BasicBlock *forCond = BasicBlock::Create(Context, "for.cond", call->getFunction(), forEnd);
			idxAlloca->getParent()->getTerminator()->setSuccessor(0, forCond);
			
			IRBuilder<> forCondBuilder(forCond);
			Value *idx = forCondBuilder.CreateLoad(idxAlloca, "idx");
			Value *cmp = forCondBuilder.CreateICmpSLT(idx, ConstantInt::get(idxTy, range), "cmp");
			
			BasicBlock *forBody = BasicBlock::Create(Context, "for.body", call->getFunction(), forEnd);
			forCondBuilder.CreateCondBr(cmp, forBody, forEnd);	
			IRBuilder<> forBodyBuilder(forBody);
			idx = forBodyBuilder.CreateLoad(idxAlloca, "idxprom");
			IdxList.at(1) = idx;
			if(rangedLeftOperand){
				Value *addOffset = forBodyBuilder.CreateAdd(idx, ConstantInt::get(idxTy, rangeBeginLOp), "offset");
				IdxList.at(1) = addOffset;
			}
			if(notBitSlicedLeftOperand){
				LOper = forBodyBuilder.CreateLoad(allLOper);
				if(rangedLeftOperand){
					Value *offset = forBodyBuilder.CreateNSWAdd(idx, ConstantInt::get(idxTy, rangeBeginLOp), "offset");
					LOper = forBodyBuilder.CreateSExt(LOper, idxTy);
					LOper = forBodyBuilder.CreateLShr(LOper, offset);
				}else{
					LOper = forBodyBuilder.CreateLShr(LOper, idx);
				}
				LOper = forBodyBuilder.CreateAnd(LOper, ConstantInt::get(idxTy, 1));
				LOper = forBodyBuilder.CreateSExt(LOper, sliceTy);
			}else{
				if(rangedLeftOperand){
					Value *addOffset = forBodyBuilder.CreateAdd(idx, ConstantInt::get(idxTy, rangeBeginLOp), "offset");
					IdxList.at(1) = addOffset;
				}
				LOper = forBodyBuilder.CreateGEP(allLOper, ArrayRef <Value *>(IdxList), "LOper");
				LOper = forBodyBuilder.CreateLoad(LOper);
			}
			IdxList.at(1) = idx;
			if(rangedRightOperand){
				Value *addOffset = forBodyBuilder.CreateAdd(idx, ConstantInt::get(idxTy, rangeBeginROp), "offset");
				IdxList.at(1) = addOffset;
			}
			if(notBitSlicedRightOperand){
				ROper = forBodyBuilder.CreateLoad(allROper);
				if(rangedLeftOperand){
					Value *offset = forBodyBuilder.CreateNSWAdd(idx, ConstantInt::get(idxTy, rangeBeginROp), "offset");
					ROper = forBodyBuilder.CreateSExt(ROper, idxTy);
					ROper = forBodyBuilder.CreateLShr(ROper, offset);
				}else{
					ROper = forBodyBuilder.CreateLShr(ROper, idx);
				}
				ROper = forBodyBuilder.CreateAnd(ROper, ConstantInt::get(idxTy, 1));
				ROper = forBodyBuilder.CreateTrunc(ROper, sliceTy);
			}else{
				if(rangedRightOperand){
					Value *addOffset = forBodyBuilder.CreateAdd(idx, ConstantInt::get(idxTy, rangeBeginROp), "offset");
					IdxList.at(1) = addOffset;
				}
				ROper = forBodyBuilder.CreateGEP(allROper, ArrayRef <Value *>(IdxList), "ROper");
				ROper = forBodyBuilder.CreateLoad(ROper);
			}
			Value *res = forBodyBuilder.CreateXor(LOper, ROper, "xor");
			IdxList.at(1) = idx;
			if(rangedDestOperand){
				Value *addOffset = forBodyBuilder.CreateAdd(idx, ConstantInt::get(idxTy, rangeBeginDOp), "offset");
				IdxList.at(1) = addOffset;
			}
			DOper = forBodyBuilder.CreateGEP(allDOper, ArrayRef <Value *>(IdxList), "DOper");
			forBodyBuilder.CreateStore(res, DOper);
			
			BasicBlock *forInc = BasicBlock::Create(Context, "for.inc", call->getFunction(), forEnd);
			forBodyBuilder.CreateBr(forInc);
			
			IRBuilder<> forIncBuilder(forInc);
			Value *inc = forIncBuilder.CreateLoad(idxAlloca);
			inc = forIncBuilder.CreateNSWAdd(inc, ConstantInt::get(idxTy, 1), "inc");
			forIncBuilder.CreateStore(inc, idxAlloca);
			forIncBuilder.CreateBr(forCond);
		}
	
	/*
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
		*/
	}
	
	
/*----------------------------------------MOVE--------------------------------------*/
	
	if(op.equals("move")){

		for(i=0; i<AllocOldNames.size(); i++){
			if(AllocOldNames.at(i).equals(leftOperand.at(0))){
				allLOper = cast<AllocaInst>(AllocNewInstBuff.at(i));
				foundLeftOperand = true;
			}
			if(AllocOldNames.at(i).equals(rightOperand.at(0))){
				allROper = cast<AllocaInst>(AllocNewInstBuff.at(i));
				foundRightOperand = true;
			}
			if(!foundRightOperand){
				glOper = call->getModule()->getGlobalVariable(rightOperand.at(0));
				if(!glOper){
					errs() << "error: undefined right operand\n";
					return;
				}
				globalRightOperand = true;
			}
			if(AllocOldNames.at(i).equals(destOperand.at(0))){
				allDOper = cast<AllocaInst>(AllocNewInstBuff.at(i));
				foundDestOperand = true;
			}
			if(foundLeftOperand && (foundRightOperand || globalRightOperand) && foundDestOperand) break;
		}
		
		if(leftOperand.at(1).equals("all") && rightOperand.at(1).equals("all")){
			arraySize = cast<ArrayType>(allLOper->getAllocatedType())->getNumElements();
			ArrayType *arrTy = ArrayType::get(sliceTy, arraySize);
			AllocaInst *tmpArray = builder.CreateAlloca(arrTy, 0, "tmpArray");
			AllocaInst *idxAlloca = builder.CreateAlloca(idxTy, 0, "idx");
			builder.CreateStore(idxZero, idxAlloca);
			BasicBlock *forEnd = call->getParent()->splitBasicBlock(call, "for.end");
	/*		
			if(prevBB != nullptr){
			errs() << __LINE__ << "\n";
				IRBuilder<> forHeadBuilder(prevBB->getTerminator());
				idxAlloca = forHeadBuilder.CreateAlloca(idxTy, 0, "idx");
				forHeadBuilder.CreateStore(idxZero, idxAlloca);
				forEnd = call->getParent();
				forEnd->setName("for.end");
			}else{
			errs() << __LINE__ << "\n";
				tmpArray = builder.CreateAlloca(arrTy, 0, "tmpArray");
				idxAlloca = builder.CreateAlloca(idxTy, 0, "idx");
				builder.CreateStore(idxZero, idxAlloca);
				forEnd = call->getParent()->splitBasicBlock(call, "for.end");
			}
			
	*/		
			BasicBlock *forCond = BasicBlock::Create(Context, "for.cond", call->getFunction(), forEnd);
			idxAlloca->getParent()->getTerminator()->setSuccessor(0, forCond);
			
			IRBuilder<> forCondBuilder(forCond);
			Value *idx = forCondBuilder.CreateLoad(idxAlloca, "idx");
			Value *cmp = forCondBuilder.CreateICmpSLT(idx, ConstantInt::get(idxTy, arraySize), "cmp");
			BasicBlock *forBody = BasicBlock::Create(Context, "for.body", call->getFunction(), forEnd);
			forCondBuilder.CreateCondBr(cmp, forBody, forEnd);
			
			IRBuilder<> forBodyBuilder(forBody);
			idx = forBodyBuilder.CreateLoad(idxAlloca, "idxprom");
			IdxList.at(1) = idx;
			LOper = forBodyBuilder.CreateGEP(allLOper, ArrayRef <Value *>(IdxList));
			LOper = forBodyBuilder.CreateLoad(LOper);
			Value *copy = forBodyBuilder.CreateGEP(tmpArray, ArrayRef <Value *>(IdxList));
			forBodyBuilder.CreateStore(LOper, copy);
			BasicBlock *forInc = BasicBlock::Create(Context, "for.inc", call->getFunction(), forEnd);
			forBodyBuilder.CreateBr(forInc);
			
			IRBuilder<> forIncBuilder(forInc);
			Value *inc = forIncBuilder.CreateLoad(idxAlloca);
			inc = forIncBuilder.CreateNSWAdd(inc, ConstantInt::get(idxTy, 1), "inc");
			forIncBuilder.CreateStore(inc, idxAlloca);
			forIncBuilder.CreateBr(forCond);
			
			BasicBlock *forEnd2 = call->getParent()->splitBasicBlock(call, "for.end");
			IRBuilder<> forEndBuilder(forEnd->getTerminator());
			forEndBuilder.CreateStore(idxZero, idxAlloca);
			BasicBlock *forCond2 = BasicBlock::Create(Context, "for.cond", call->getFunction(), forEnd2);
			forEnd->getTerminator()->setSuccessor(0, forCond2);
			
			IRBuilder<> forCond2Builder(forCond2);
			idx = forCond2Builder.CreateLoad(idxAlloca, "idx");
			cmp = forCond2Builder.CreateICmpSLT(idx, ConstantInt::get(idxTy, arraySize), "cmp");
			BasicBlock *forBody2 = BasicBlock::Create(Context, "for.body", call->getFunction(), forEnd2);
			forCond2Builder.CreateCondBr(cmp, forBody2, forEnd2);
			
			IRBuilder<> forBody2Builder(forBody2);
			idx = forBody2Builder.CreateLoad(idxAlloca, "idxprom");
			IdxList.at(1) = idx;
			LOper = forBody2Builder.CreateGEP(tmpArray, ArrayRef <Value *>(IdxList), "LOper");
			LOper = forBody2Builder.CreateLoad(LOper);
			Value *moveIdx;
			if(globalRightOperand)
				moveIdx = forBody2Builder.CreateGEP(glOper, ArrayRef <Value *>(IdxList));
			else
				moveIdx = forBody2Builder.CreateGEP(allROper, ArrayRef <Value *>(IdxList), "ROper");
			IdxList.at(1) = forBody2Builder.CreateLoad(moveIdx);
			DOper = forBody2Builder.CreateGEP(allDOper, ArrayRef <Value *>(IdxList));
			forBody2Builder.CreateStore(LOper, DOper);
			BasicBlock *forInc2 = BasicBlock::Create(Context, "for.inc", call->getFunction(), forEnd2);
			forBody2Builder.CreateBr(forInc2);
			
			IRBuilder<> forInc2Builder(forInc2);
			Value *inc2 = forInc2Builder.CreateLoad(idxAlloca);
			inc2 = forInc2Builder.CreateNSWAdd(inc2, ConstantInt::get(idxTy, 1), "inc");
			forInc2Builder.CreateStore(inc2, idxAlloca);
			forInc2Builder.CreateBr(forCond2);
		}
	}

	
/*--------------------------------------ROT------------------------------------*/

	if(op.equals("rotL") || op.equals("rotR")){
		for(i=0; i<AllocOldNames.size(); i++){
			if(AllocOldNames.at(i).equals(leftOperand.at(0))){
				allLOper = cast<AllocaInst>(AllocNewInstBuff.at(i));
				foundLeftOperand = true;
			}
			if(AllocOldNames.at(i).equals(rightOperand.at(0))){
				allROper = cast<AllocaInst>(AllocNewInstBuff.at(i));
				foundRightOperand = true;
			}
			if(!foundRightOperand){
				constOper = std::stoi(rightOperand.at(0).str());
				constantRightOperand = true;
			}
			if(AllocOldNames.at(i).equals(destOperand.at(0))){
				allDOper = cast<AllocaInst>(AllocNewInstBuff.at(i));
				foundDestOperand = true;
			}
			if(foundLeftOperand && (foundRightOperand || constantRightOperand) && foundDestOperand) break;
		}
		
		arraySize = cast<ArrayType>(allLOper->getAllocatedType())->getNumElements();
		ArrayType *arrTy = ArrayType::get(sliceTy, arraySize);
		AllocaInst *tmpArray = builder.CreateAlloca(arrTy, 0, "tmpArray");
		AllocaInst *idxAlloca = builder.CreateAlloca(idxTy, 0, "idx");
		builder.CreateStore(idxZero, idxAlloca);
		BasicBlock *forEnd = call->getParent()->splitBasicBlock(call, "for.end");
		BasicBlock *forCond = BasicBlock::Create(Context, "for.cond", call->getFunction(), forEnd);
		idxAlloca->getParent()->getTerminator()->setSuccessor(0, forCond);
			
		IRBuilder<> forCondBuilder(forCond);
		Value *idx = forCondBuilder.CreateLoad(idxAlloca, "idx");
		Value *cmp = forCondBuilder.CreateICmpSLT(idx, ConstantInt::get(idxTy, arraySize), "cmp");
		BasicBlock *forBody = BasicBlock::Create(Context, "for.body", call->getFunction(), forEnd);
		forCondBuilder.CreateCondBr(cmp, forBody, forEnd);
			
		IRBuilder<> forBodyBuilder(forBody);
		idx = forBodyBuilder.CreateLoad(idxAlloca, "idxprom");
		IdxList.at(1) = idx;
		LOper = forBodyBuilder.CreateGEP(allLOper, ArrayRef <Value *>(IdxList));
		LOper = forBodyBuilder.CreateLoad(LOper);
		Value *copy = forBodyBuilder.CreateGEP(tmpArray, ArrayRef <Value *>(IdxList));
		forBodyBuilder.CreateStore(LOper, copy);
		BasicBlock *forInc = BasicBlock::Create(Context, "for.inc", call->getFunction(), forEnd);
		forBodyBuilder.CreateBr(forInc);
	
		IRBuilder<> forIncBuilder(forInc);
		Value *inc = forIncBuilder.CreateLoad(idxAlloca);
		inc = forIncBuilder.CreateNSWAdd(inc, ConstantInt::get(idxTy, 1), "inc");
		forIncBuilder.CreateStore(inc, idxAlloca);
		forIncBuilder.CreateBr(forCond);



		BasicBlock *forEnd2 = call->getParent()->splitBasicBlock(call, "for.end");
		IRBuilder<> forEndBuilder(forEnd->getTerminator());
		forEndBuilder.CreateStore(idxZero, idxAlloca);
		BasicBlock *forCond2 = BasicBlock::Create(Context, "for.cond", call->getFunction(), forEnd2);
		forEnd->getTerminator()->setSuccessor(0, forCond2);
		
		IRBuilder<> forCond2Builder(forCond2);
		idx = forCond2Builder.CreateLoad(idxAlloca, "idx");
		cmp = forCond2Builder.CreateICmpSLT(idx, ConstantInt::get(idxTy, arraySize), "cmp");
		BasicBlock *forBody2 = BasicBlock::Create(Context, "for.body", call->getFunction(), forEnd2);
		forCond2Builder.CreateCondBr(cmp, forBody2, forEnd2);
			
		IRBuilder<> forBody2Builder(forBody2);
		idx = forBody2Builder.CreateLoad(idxAlloca, "idxprom");
		IdxList.at(1) = idx;
		Value *tmp = forBody2Builder.CreateGEP(tmpArray, ArrayRef <Value *>(IdxList));
		tmp = forBody2Builder.CreateLoad(tmp);
		Value *rotIdx;
		if(constantRightOperand){
			if(op.equals("rotL"))	
				rotIdx = forBody2Builder.CreateNSWAdd(idx, ConstantInt::get(idxTy, constOper));
			else if(op.equals("rotR"))
				rotIdx = forBody2Builder.CreateNSWAdd(idx, ConstantInt::get(idxTy, arraySize-constOper));
		}else{
			rotIdx = forBody2Builder.CreateLoad(allROper);
			if(op.equals("rotL"))
				rotIdx = forBody2Builder.CreateNSWAdd(idx, rotIdx);
			else if(op.equals("rotR")){
				Value *complement = forBody2Builder.CreateNSWSub(ConstantInt::get(idxTy, arraySize), rotIdx);
				rotIdx = forBody2Builder.CreateNSWAdd(rotIdx, complement);
			}	
		}
		rotIdx = forBody2Builder.CreateSRem(rotIdx, ConstantInt::get(idxTy, arraySize));
		IdxList.at(1) = rotIdx;
		DOper = forBody2Builder.CreateGEP(allLOper, ArrayRef <Value *>(IdxList), "LOper");
		forBody2Builder.CreateStore(tmp, DOper);
		BasicBlock *forInc2 = BasicBlock::Create(Context, "for.inc", call->getFunction(), forEnd2);
		forBody2Builder.CreateBr(forInc2);
		
		IRBuilder<> forInc2Builder(forInc2);
		Value *inc2 = forInc2Builder.CreateLoad(idxAlloca);
		inc2 = forInc2Builder.CreateNSWAdd(inc2, ConstantInt::get(idxTy, 1), "inc");
		forInc2Builder.CreateStore(inc2, idxAlloca);
		forInc2Builder.CreateBr(forCond2);
	}
}


/*
void printBitSliced(CallInst *call, LLVMContext &Context){
	Instruction *inputSize = cast<Instruction>(call->getArgOperand(0));
	for(; !isa<AllocaInst>(inputSize); inputSize = cast<Instruction>(inputSize->getOperand(0)));
	AllocaInst *all = cast<AllocaInst>(inputSize);
	ArrayType *arrTy = cast<ArrayType>(all->getAllocatedType());
	Type *elTy = arrTy->getElementType();
	uint64_t size = arrTy->getNumElements();
	uint64_t i;
	std::vector<Value *> IdxList;
	Type *idxTy = IntegerType::getInt64Ty(Context);
	Value *idxZero = ConstantInt::get(idxTy, 0);
	Value *idx;
	IdxList.push_back(idxZero);
	IdxList.push_back(idxZero);
	
	IRBuilder<> builder(call);
	AllocaInst *idxAlloca = builder.CreateAlloca();
	builder.CreateStore(idxZero, idxAlloca);
	BasicBlock *forEnd = call->getParent()->splitBasicBlock(call, "for.end");
	BasicBlock *forCond = BasicBlock::Create(Context, "for.cond", call->getFunction(), forEnd);
	idxAlloca->getParent()->getTerminator()->setSuccessor(0, forCond);
			
	IRBuilder<> forCondBuilder(forCond);
	Value *idx = forCondBuilder.CreateLoad(idxAlloca, "idx");
	Value *cmp = forCondBuilder.CreateICmpSLT(idx, ConstantInt::get(idxTy, size), "cmp");
	BasicBlock *forBody = BasicBlock::Create(Context, "for.body", call->getFunction(), forEnd);
	forCondBuilder.CreateCondBr(cmp, forBody, forEnd);		
	
	IRBuilder<> forBodyBuilder(forBody);
	idx = forBodyBuilder.CreateLoad(idxAlloca, "idxprom");
	IdxList.at(0) = idx;
	Value *element = forBodyBuilder.CreateGEP(all, ArrayRef <Value *>(IdxList));
	
}
*/

/*
void EndOrthogonalTransformation(BasicBlock *startBlock, 
								 BasicBlock *endBlock,
								 StringRef Description){

	
	bool stop = false;
	LoopInfoBase<BasicBlock, Loop> *CheckLoops = new LoopInfoBase<BasicBlock, Loop>();

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
	
	auto CExtr = new CodeExtractor(ArrayRef <BasicBlock *>(BlockList));
	
	Function *NewFunc = CExtr->extractCodeRegion();
	
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
		
		BasicBlock *orthStartBlock = nullptr, *orthEndBlock = nullptr, *prevBB = nullptr;
		Value *orthDescription;
	//	bool OrthErase = false;
	//	bool OrthBBErase = false;
		bool SameBlock = false;
/*		std::vector<LoadInst *> LoadInstBuff;
		std::vector<GetElementPtrInst *> GEPInstBuff;
		
		std::vector<StringRef> AllocNames;
		std::vector<StringRef> LoadNames;
		std::vector<StringRef> GEPNames;
*/
			
		bool runOnModule(Module &M) override {
		//	int i;
		
//		
		for(Function& F : M){
			for(BasicBlock& B : F){
				
	//		B.dump();
				for(Instruction& I : B){
					//if(OrthErase)
					//	OrthEraseList.push_back(&I);
					
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
			
							/*if(!BitSlice(call, I.getModule()->getContext())){
								errs() << "bit-slicing failed\n";
							}*/				
							eraseList.push_back(&I);
							done = 1;
						}else if(Fn && Fn->getIntrinsicID() == Intrinsic::unbitslice_i32){
					//		errs() << "args: \n" << call->getNumArgOperands() << "\n";
							UnBitSliceCalls.push_back(call);
			
							/*if(!BitSlice(call, I.getModule()->getContext())){
								errs() << "bit-slicing failed\n";
							}*/				
							eraseList.push_back(&I);
							done = 1;
						}else if(Fn && Fn->getIntrinsicID() == Intrinsic::start_bitslice){
							MDNode *MData = MDNode::get(I.getModule()->getContext(), 
								MDString::get(I.getModule()->getContext(), "start-orthogonalization"));
							call->setMetadata("start-orthogonalization", MData);
							emitPoints.push_back(call);
				
						//	Descriptions.push_back(cast<ConstantDataSequential>(cast<User>(cast<User>(call->getArgOperand(1))
						//							->getOperand(0))->getOperand(0))->getAsCString());
					
						
						//	OrthogonalTransformation(call);
						//	OrthErase = true;
							eraseList.push_back(&I);
									
						}else if(Fn && Fn->getIntrinsicID() == Intrinsic::end_bitslice){
					
							MDNode *MData = MDNode::get(I.getModule()->getContext(), 
								MDString::get(I.getModule()->getContext(), "stop-orthogonalization"));
							call->setMetadata("stop-orthogonalization", MData);
						//	endSplitPoints.push_back(call);
						//	OrthEraseList.pop_back();
//					
						//	OrthErase = false;
							eraseList.push_back(&I);
					
						}
					}
					
					if(auto *all = dyn_cast<AllocaInst>(&I))
						AllocInstBuff.push_back(all);
					
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
		
			for(CallInst *c : BitSliceAlloc){
				BitSlice(c, c->getModule()->getContext());
			}
			
			for(CallInst *c : UnBitSliceCalls){
				UnBitSlice(c, c->getModule()->getContext());
			}
		
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
		/*	
			for(auto& ESP : endSplitPoints){
				for(auto& SSP : startSplitPoints){
					StringRef StartName = cast<ConstantDataSequential>(cast<User>(cast<User>(SSP->getArgOperand(0))
												->getOperand(0))->getOperand(0))->getAsCString();
						
					StringRef EndName = cast<ConstantDataSequential>(cast<User>(cast<User>(ESP->getArgOperand(0))
												->getOperand(0))->getOperand(0))->getAsCString();
						
					if(EndName.equals(StartName)){
					//SSP->getParent()->dump();
					//ESP->getParent()->dump();
					
						if(ESP->getParent() != SSP->getParent()){
							prevBB = SSP->getParent();
							orthStartBlock = SSP->getParent()->splitBasicBlock(SSP);
							orthEndBlock = ESP->getParent()->splitBasicBlock(ESP);
							prevBB->getTerminator()->setSuccessor(0, orthEndBlock);
					
						}
					
					}
					
				}
			}	
			*/		
			/*
			for(auto &OEI: OrthEraseList){
				if(!OEI->use_empty())	
					OEI->replaceAllUsesWith(UndefValue::get(OEI->getType()));
				OEI -> eraseFromParent();
			}
			*/
			/*
			for(Function& F : M){
				for(BasicBlock& B : F){
					if(OrthBBErase){
							OrthBBEraseList.push_back(&B);
					}
					for(Instruction& I : B){
						if(I.getMetadata("start-orthogonalization")){
						//	OrthBBEraseList.push_back(&B);
						//	OrthogonalTransformation(cast<CallInst>(&I));
							OrthBBErase = true;
						}
						if(I.getMetadata("stop-orthogonalization")){
							if(!OrthBBEraseList.empty())	
								OrthBBEraseList.pop_back();
							OrthBBErase = false;
						}
					}
				}
			}
		
			if(!OrthBBEraseList.empty()){
				for(auto &EB: OrthBBEraseList){
					EB -> eraseFromParent();
				}
			}
		*/
		
			for(auto& EP : emitPoints){
				StringRef Descr = cast<ConstantDataSequential>(cast<User>(cast<User>(EP->getArgOperand(1))
																->getOperand(0))->getOperand(0))->getAsCString();
				OrthogonalTransformation(EP, Descr);
			}
		
		/*	
			for(auto& ESP : endSplitPoints){
				StringRef EndName = cast<ConstantDataSequential>(cast<User>(cast<User>(ESP->getArgOperand(0))
																->getOperand(0))->getOperand(0))->getAsCString();
				for(unsigned SSP = 0; SSP<startSplitPoints.size(); SSP++){
					
					StringRef StartName = cast<ConstantDataSequential>(
													cast<User>(cast<User>(startSplitPoints.at(SSP)->getArgOperand(0))
													->getOperand(0))->getOperand(0))
													->getAsCString();
					
				errs() << __LINE__ << StartName << EndName << "\n";	
					if(EndName.equals(StartName)){
						StringRef Descr = cast<ConstantDataSequential>(cast<User>(cast<User>(startSplitPoints.at(SSP)
													->getArgOperand(1))->getOperand(0))->getOperand(0))->getAsCString();
							
						OrthogonalTransformation(ESP, prevBB, Descr);
						
						if(prevBB != nullptr){
						
							startSplitPoints.at(SSP)->getParent()->eraseFromParent();
							startSplitPoints.erase(startSplitPoints.begin() + SSP);
							}
										
					}
				}
			}
			*/
	
		
			for(Function& F : M){
				for(BasicBlock& B : F){
					for(Instruction& I : B){
						if(I.getParent() != &B){
							errs() << "BOGUS PARENT!\n";
							I.dump();
							I.getParent()->dump();
							B.dump();
						}
					}
					//B.dump();
				}
			}
		
	//			
			for(auto &EI: eraseList){
				if(EI->getParent() != nullptr)
					EI -> eraseFromParent();
			}
	//
			
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



