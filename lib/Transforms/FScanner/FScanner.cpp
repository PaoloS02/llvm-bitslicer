/*
I.getType()->dump();

Type *Type::getSequentialElementType() const {
	return cast<SequentialType>(this)->getElementType();
	}

Type *getVectorElementType() const { return getSequentialElementType(); }
Type *getPointerElementType() const { return getSequentialElementType(); }

Type * 	getScalarType () const LLVM_READONLY
 	getScalarType - If this is a vector type, return the element type, otherwise return 'this'. 

unsigned Type::getIntegerBitWidth() const {
	return cast<IntegerType>(this)->getBitWidth();
	}
bool 	isIntegerTy (unsigned Bitwidth) const
 	isIntegerTy - Return true if this is an IntegerType of the given width. 
 	
the instruction may basically be a binaryoperator or a unaryinstruction (may be an allocation, a cast...)
*/

#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Analysis/LoopInfo.h"

#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/LegacyPassManager.h"

#define CPU_BYTES 1					//if you want N = 8, 16, 24, 32... blocks in parallel put this 
									//macro at 1, 2, 3, 4...

#define UNIFORM_ALLOCATION 8		//the scalar uint8_t variables are allocated with the same
									//size as the arrays for uniformity (it causes a segmentation
									//fault otherwise). You must set this macro to the dimension
									//of the array.

using namespace llvm;

namespace{
	
	struct FScanner : public FunctionPass{
		static char ID;
		static int done; 
		FScanner() : FunctionPass(ID) {}
		//Value *size;
		std::vector<Instruction *> eraseList;
		
		bool runOnFunction(Function &F){
			for(BasicBlock& B : F){
				errs() << "\nBLOCK:\n\n";
				B.dump();
				for(Instruction& I : B){
					
					
					if(auto *all = dyn_cast<AllocaInst>(&I)){
						IRBuilder<> alloca_builder(all);
						
						if(all->getAllocatedType()->isIntegerTy(8)){
							Type *sizety = IntegerType::getInt64Ty(I.getModule()->getContext());
							Value *size = ConstantInt::get(sizety, UNIFORM_ALLOCATION*8*CPU_BYTES);
							
							Value * all__ = alloca_builder.CreateAlloca(all->getAllocatedType(),size,"bitsliced"); //all->getName()
							all->replaceAllUsesWith(all__);
							
							eraseList.push_back(&I);
							all__->dump();
							done = 1;
						
						}else if(isa<ArrayType>(all->getAllocatedType())){
							Type *sizety = IntegerType::getInt64Ty(I.getModule()->getContext());
							Value *size = ConstantInt::get(sizety, 8*CPU_BYTES); //the 'size' parameter works! If I put 1
																					//I get a segmentation fault at runtime
																					//that means that by putting 8, even though
																					//the IR uses a bunch of temporary values
																					//as pointers to access the subsequent
																					//elements enough contiguous memory has
																					//been allocated for the bitsliced version.
																					
							Value *arr__ = alloca_builder.CreateAlloca(all->getAllocatedType(),size,"multibitsliced");
							
							all->replaceAllUsesWith(arr__);
							
							eraseList.push_back(&I);
							arr__->dump();
							
							done = 1;
							}
					}
					
					
					if(auto *st = dyn_cast<StoreInst>(&I)){
						IRBuilder<> store_builder(st);
						
						if(st->getValueOperand()->getType()->isIntegerTy(8)){
							unsigned align = st->getAlignment();
							int i;
							int pace = 8*CPU_BYTES;
							
							errs() << "store: ";
							I.dump();
							for(auto &us : st->uses()){
								User *Ust = us.getUser();
								errs() << "use value: ";
								Ust->dump();
							}
							
							Value *st_ptr = st->getPointerOperand();
							
							StoreInst *st__;
							
							//↓useful, because when we will have to implement the usage of blocks in parallel
							//↓we shouldn't rely on the type allocated in order to have enough multidimensionality
							//↓because we would have less freedom (int8, int16, int32, int64),
							//↓even though there may be enough types of integer in order to cover the main
							//↓processor types. But not enough store instruction types.
							Type *sliceTy = IntegerType::getInt8Ty(I.getModule()->getContext());
							
							
/*------------------>*/		if(!isa<Constant>(st->getValueOperand())){		//WARNING: POSSIBLE TIME DEPENDANCY ON INPUT		
								Value *st_val = st->getValueOperand();
								
								Value *bit_index_value = ConstantInt::get(sliceTy, 0);
								Value *bit_index_addr = store_builder.CreateAlloca(sliceTy, 0, "bit_index");
								Value *bit_inc = ConstantInt::get(sliceTy, 1);
								
								store_builder.CreateStore(bit_index_value, bit_index_addr);
							
								for(i=0;i<8;){
									Value *bit_index = store_builder.CreateLoad(bit_index_addr,"bit_index");
									Value *mask = ConstantInt::get(sliceTy, 0x01<<i);
									Value *bit_and = store_builder.CreateAnd(st_val, mask);
									Value *elem = store_builder.CreateLShr(bit_and,bit_index,"bit_shiftR");
									Value *bit_index_inc = store_builder.CreateAdd(bit_index, bit_inc);
									store_builder.CreateStore(bit_index_inc, bit_index_addr);
									
									i++;
									
									st__ = store_builder.CreateAlignedStore(elem, st_ptr, align);
									
									Value *index = ConstantInt::get(IntegerType::getInt64Ty(I.getModule()->getContext()), pace);
									st_ptr = store_builder.CreateGEP(st_ptr, index);
									
									st__->dump();
									st_ptr->dump();
								}
								
							}else{
								auto *st_val = dyn_cast<ConstantInt>(st->getValueOperand());
								uint64_t val = st_val->getZExtValue();
								uint8_t mask = 0x01;
								
								for(i=0;i<8;){
									Value *elem = ConstantInt::get(sliceTy, (val & (mask<<i)) >> i);
									i++;
									
									st__ = store_builder.CreateAlignedStore(elem, st_ptr, align);
									
									Value *index = ConstantInt::get(IntegerType::getInt64Ty(I.getModule()->getContext()), pace);
									st_ptr = store_builder.CreateGEP(st_ptr, index);
									
									st__->dump();
									st_ptr->dump();
								}
							}
							
							if(!st->isVolatile()){
								eraseList.push_back(&I);
							}
							
							done = 1;
						}
					}
					
					
					if(auto *ld = dyn_cast<LoadInst>(&I)){
						if(ld->getType()->isIntegerTy(8)){
							errs() << "load: ";
							I.dump();
							
							/*
							for(auto &UseLd : ld->uses()){
								for(ul = UseLd; ul;){
									User *userld = ul.getUser();
									errs() << "use value: ";
									userld->dump();
									Value *next = 
								}
							}
							*/
							
							for(auto &ul : ld->uses()){
								User *uld = ul.getUser();
								errs() << "user: ";
								uld -> dump();
								errs() << "operands:\n";
								
								for(auto &op : uld->operands()){
									op -> dump();
								}
							}
							/*
							Value *ld_ptr = ld->getPointerOperand();
							int pace = 8*CPU_BYTES;
							int i;
							
							for(i=0; i<8; i++){
								
							}
							*/
						}
					}
					
					
					
				}
					
			}
			for(auto &EI: eraseList){
						EI -> eraseFromParent();
						}
			
			
			if(done)
				return true;
			return false;
		}
		
		
			
	};

}

char FScanner::ID = 0;
int FScanner::done = 0;
static void registerFScannerPass(const PassManagerBuilder &,
                         legacy::PassManagerBase &PM) {
  PM.add(new FScanner());
}
static RegisterStandardPasses
  RegisterMyPass(PassManagerBuilder::EP_EarlyAsPossible,
registerFScannerPass);






/*
errs() << "changed uses of: ";
I.dump();
for(Instruction& J : B){
J.dump();
}
errs() << "------- end uses\n";
*/






