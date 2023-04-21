#include "llvm/Transforms/Obfuscation/BogusControlFlow.h"
#include "llvm-c/Core.h"
#include "llvm-c/Types.h"

// Stats
#define DEBUG_TYPE "BogusControlFlow"


IntegerType *i1Type, *i8Type, * i16Type, *i32Type, *i64Type;
ConstantInt *ci0_64, *ci1_64, *ci2_64, *ci3_64, *ci4_64, *ci5_64, *ci6_64, *ci7_64, *ci8_64, *ci9_64;
ConstantInt *ci0_32, *ci1_32, *ci2_32, *ci3_32, *ci4_32, *ci5_32, *ci6_32, *ci7_32, *ci8_32, *ci9_32;
vector<Value*> vec00_32,vec01_32;
vector<Value*> vec00_64,vec01_64;



int num1=0;
int num2=0;
int num3=0;
int num4=0;

//set the type of opaque predicate; for evaluation purpose
static cl::opt<int>
OpqType("OpqType", cl::desc("Choose the opaque predicate type"), cl::value_desc("opaque predicate type"), cl::init(0), cl::Optional);

static cl::opt<int>
OpqNum("OpqNum", cl::desc("Set the number of opaque predicates"), cl::value_desc("opaque predicate number"), cl::init(0), cl::Optional);


namespace {
  struct BogusControlFlow : public FunctionPass {
    static char ID; // Pass identification
    bool flag;
    BogusControlFlow() : FunctionPass(ID) {}
    BogusControlFlow(bool flag) : FunctionPass(ID) {this->flag = flag; BogusControlFlow();}

    /* runOnFunction
     *
     * Overwrite FunctionPass method to apply the transformation
     * to the function. See header for more details.
     */
    virtual bool runOnFunction(Function &F){
      // Check if the percentage is correct

      Module& M = *(F.getParent());
      LLVMContext& context = M.getContext();


      i1Type = IntegerType::get(context, 1);
      i8Type = IntegerType::getInt8Ty(context);
      i16Type = IntegerType::getInt16Ty(context);
      i32Type = IntegerType::getInt32Ty(context);
      i64Type = IntegerType::getInt64Ty(context);


      ci0_32 = (ConstantInt*) ConstantInt::getSigned(i32Type, 0);
      ci1_32 = (ConstantInt*) ConstantInt::getSigned(i32Type, 1);
      ci2_32 = (ConstantInt*) ConstantInt::getSigned(i32Type, 2);
      ci3_32 = (ConstantInt*) ConstantInt::getSigned(i32Type, 3);
      ci4_32 = (ConstantInt*) ConstantInt::getSigned(i32Type, 4);
      ci5_32 = (ConstantInt*) ConstantInt::getSigned(i32Type, 5);
      ci6_32 = (ConstantInt*) ConstantInt::getSigned(i32Type, 6);
      ci7_32 = (ConstantInt*) ConstantInt::getSigned(i32Type, 7);
      ci8_32 = (ConstantInt*) ConstantInt::getSigned(i32Type, 8);
      ci9_32 = (ConstantInt*) ConstantInt::getSigned(i32Type, 9);


      ci0_64 = (ConstantInt*) ConstantInt::getSigned(i64Type, 0);
      ci1_64 = (ConstantInt*) ConstantInt::getSigned(i64Type, 1);
      ci2_64 = (ConstantInt*) ConstantInt::getSigned(i64Type, 2);
      ci3_64 = (ConstantInt*) ConstantInt::getSigned(i64Type, 3);
      ci4_64 = (ConstantInt*) ConstantInt::getSigned(i64Type, 4);
      ci5_64 = (ConstantInt*) ConstantInt::getSigned(i64Type, 5);
      ci6_64 = (ConstantInt*) ConstantInt::getSigned(i64Type, 6);
      ci7_64 = (ConstantInt*) ConstantInt::getSigned(i64Type, 7);
      ci8_64 = (ConstantInt*) ConstantInt::getSigned(i64Type, 8);
      ci9_64 = (ConstantInt*) ConstantInt::getSigned(i64Type, 9);


      vec00_64.push_back(ci0_64);
      vec00_64.push_back(ci0_64);
      vec01_64.push_back(ci0_64);
      vec01_64.push_back(ci1_64);

      vec00_32.push_back(ci0_32);
      vec00_32.push_back(ci0_32);
      ArrayRef<Value*> ar00(vec00_32);
      vec01_32.push_back(ci0_32);
      vec01_32.push_back(ci1_32);
      ArrayRef<Value*> ar01(vec01_32);

       // If fla annotations
      if(toObfuscate(flag, &F, "bcf")) 
      {
         switch(OpqType){
           case 1:{
             addPF(F,1);
             break;
	   }
           case 2:{
              addJumpFlow(F,2);
              break;
	   }
           case 3:{
              addPF(F,3);
                //addExtrenFunc(F);
              break;
	   }
           case 4:{
              addJumpFlow(F,4);
              break;
	   }
           case 5:{
              addJumpFlow(F,2);
              addPF(F,1);
              break;
	   }
           case 6:{
              addJumpFlow(F,4);
              addPF(F,3);
              break;
	   }
         }
        return true;
      }
      return false;
    } // end of runOnFunction()



    void addPF(Function &F, int type){

       //errs()<< "addPF"<<"\n";
      Module* module = F.getParent();
      Module& M = *module;
      LLVMContext& context = M.getContext();
      //For creating symbolic opaque predicates
      Value *argValue;
      Type* argType;

      for (Function::arg_iterator argIt = F.arg_begin(); argIt != F.arg_end(); ++argIt){
           argValue = &*argIt;
           argType = argValue->getType();
             
      }


      std::vector<Instruction*> toEdit_1;      
      for(Module::iterator mi = M.begin(), me = M.end(); mi != me; ++mi){
        for(Function::iterator fi = mi->begin(), fe = mi->end(); fi != fe; ++fi){
          for (BasicBlock::iterator bi = fi->begin(), be = fi->end() ; bi != be; ++bi){
              Instruction* inst=dyn_cast<Instruction>(bi);
              if(inst->getOpcode()== Instruction::Load){
                 //errs() << "Load instruction is " << *inst <<"\n";
                 toEdit_1.push_back(inst);
                   break;
              }
           }
         }
       }
       Instruction* inst1;
       if(F.getName()=="main"){
        BasicBlock *bb=&F.getEntryBlock();        
        inst1=bb->getFirstNonPHI();
        //errs()<<"first instrucion is "<< *inst1 <<"\n";
      }

       if(type==1){ 
          while(num1<OpqNum){
                //errs()<<num1<<"\n";
              InsertArrayOpq(F,M,inst1,argValue);
              num1++;
           }

       }
        
       if(type==3){ 
          while(num3<OpqNum){
              //errs()<<num3<<"\n";
              InsertTentOpq(F,M,inst1,argValue);
              num3++;
           }

       }

    }

    //algorithm1--OP_I
    bool InsertArrayOpq(Function& F, Module &M, Instruction* inst, Value* arg){
      Type* argType = arg->getType();

      LLVMContext& context = M.getContext();

      const DataLayout &DL = M.getDataLayout(); // ?????
      AllocaInst* jAI = new AllocaInst(argType, DL.getAllocaAddrSpace(), "", inst);
      StoreInst* jSI = new StoreInst(arg, jAI, inst);
      LoadInst* jLI = new LoadInst(jAI, "", inst);

      BinaryOperator* remBO;
      BinaryOperator* remBO1;
      if(((IntegerType*) argType)->getBitWidth() != 64)
      {
        CastInst* j64CI = new SExtInst(jLI, i64Type, "idxprom", inst);
        remBO1 = BinaryOperator::Create(Instruction::SRem, j64CI, ci9_64, "rem", inst);      
      } 
      else 
      {
        remBO1 = BinaryOperator::Create(Instruction::SRem, jLI, ci9_64, "rem", inst);
      }

      remBO = BinaryOperator::Create(Instruction::Add, remBO1, ci1_64, "", inst);

      ArrayType* arAT = ArrayType::get(i64Type, 10);

      AllocaInst* array1AI = new AllocaInst(arAT, DL.getAllocaAddrSpace(), "", inst); // ?????

      std::vector<Value*> vec00;
      vec00.push_back(ci0_32);
      vec00.push_back(ci0_64);
      ArrayRef<Value*> ar00(vec00);
      std::vector<Value*> vec01;
      vec01.push_back(ci0_32);
      vec01.push_back(ci1_64);
      ArrayRef<Value*> ar01(vec01);
      std::vector<Value*> vec02;
      vec02.push_back(ci0_32);
      vec02.push_back(ci2_64);
      ArrayRef<Value*> ar02(vec02);
      std::vector<Value*> vec03;
      vec03.push_back(ci0_32);
      vec03.push_back(ci3_64);
      ArrayRef<Value*> ar03(vec03);
      std::vector<Value*> vec04;
      vec04.push_back(ci0_32);
      vec04.push_back(ci4_64);
      ArrayRef<Value*> ar04(vec04);
      std::vector<Value*> vec05;
      vec05.push_back(ci0_32);
      vec05.push_back(ci5_64);
      ArrayRef<Value*> ar05(vec05);
      std::vector<Value*> vec06;
      vec06.push_back(ci0_32);
      vec06.push_back(ci6_64);
      ArrayRef<Value*> ar06(vec06);
      std::vector<Value*> vec07;
      vec07.push_back(ci0_32);
      vec07.push_back(ci7_64);
      ArrayRef<Value*> ar07(vec07);
      std::vector<Value*> vec08;
      vec08.push_back(ci0_32);
      vec08.push_back(ci8_64);
      ArrayRef<Value*> ar08(vec08);
      std::vector<Value*> vec09;
      vec09.push_back(ci0_32);
      vec09.push_back(ci9_64);
      ArrayRef<Value*> ar09(vec09);

      Instruction* a10EPI = GetElementPtrInst::CreateInBounds((Value *) array1AI, ar00, "l1_arrayidx", inst);
      Instruction* a11EPI = GetElementPtrInst::CreateInBounds((Value *) array1AI, ar01, "l1_arrayidx", inst);
      Instruction* a12EPI = GetElementPtrInst::CreateInBounds((Value *) array1AI, ar02, "l1_arrayidx", inst);
      Instruction* a13EPI = GetElementPtrInst::CreateInBounds((Value *) array1AI, ar03, "l1_arrayidx", inst);
      Instruction* a14EPI = GetElementPtrInst::CreateInBounds((Value *) array1AI, ar04, "l1_arrayidx", inst);
      Instruction* a15EPI = GetElementPtrInst::CreateInBounds((Value *) array1AI, ar05, "l1_arrayidx", inst);
      Instruction* a16EPI = GetElementPtrInst::CreateInBounds((Value *) array1AI, ar06, "l1_arrayidx", inst);
      Instruction* a17EPI = GetElementPtrInst::CreateInBounds((Value *) array1AI, ar07, "l1_arrayidx", inst);
      Instruction* a18EPI = GetElementPtrInst::CreateInBounds((Value *) array1AI, ar08, "l1_arrayidx", inst);
      Instruction* a19EPI = GetElementPtrInst::CreateInBounds((Value *) array1AI, ar09, "l1_arrayidx", inst);

      StoreInst* a10SI = new StoreInst(ci0_64, a10EPI, inst);
      StoreInst* a11SI = new StoreInst(ci1_64, a11EPI, inst);
      StoreInst* a12SI = new StoreInst(ci2_64, a12EPI, inst);
      StoreInst* a13SI = new StoreInst(ci3_64, a13EPI, inst);
      StoreInst* a14SI = new StoreInst(ci4_64, a14EPI, inst);
      StoreInst* a15SI = new StoreInst(ci5_64, a15EPI, inst);
      StoreInst* a16SI = new StoreInst(ci6_64, a16EPI, inst);
      StoreInst* a17SI = new StoreInst(ci7_64, a17EPI, inst);
      StoreInst* a18SI = new StoreInst(ci8_64, a18EPI, inst);
      StoreInst* a19SI = new StoreInst(ci9_64, a19EPI, inst);

      std::vector<Value*> l1Vec;
      l1Vec.push_back(ci0_32);
      l1Vec.push_back(remBO);
      ArrayRef<Value*> l1AR(l1Vec);
      Instruction* l1EPI = GetElementPtrInst::CreateInBounds((Value *) array1AI, l1AR, "l1_arrayidx", inst);
      LoadInst* l1LI = new LoadInst(l1EPI, "", false, inst);

      std::vector<Value*> l2Vec;
      l2Vec.push_back(ci0_32);
      l2Vec.push_back(l1LI);
      ArrayRef<Value*> l2AR(l2Vec);
      Instruction* l2EPI = GetElementPtrInst::CreateInBounds((Value *) array1AI, l2AR, "l2_arrayidx", inst);
      LoadInst* l2LI = new LoadInst(l2EPI, "", false, inst);

      ICmpInst* arCI = new ICmpInst(inst, ICmpInst::ICMP_NE, l2LI, remBO, "cmp");
       //errs()<<"arCI "<< *arCI<<"\n";

       
     //获取指令inst所在基本块basicBlock      
      BasicBlock *basicBlock=inst->getParent();
      
      //从inst处分割基本块，inst前面的指令置于前基本块，后面的置于新基本块existBB中
      Twine *var;
      var = new Twine("existBB");
      BasicBlock *existBB = basicBlock->splitBasicBlock(inst, *var);
      //errs()<<"existBB"<<*existBB<<"\n";

/*
      //创建基本块BogusBB 
      BasicBlock *BogusBB = BasicBlock::Create (context, "bogus",&F,existBB ); 
      IRBuilder<> IRB(context);    
      IRB.SetInsertPoint(BogusBB);
      BinaryOperator* bogusIns=BinaryOperator::Create(Instruction::Add, jLI, ci1_64, "", BogusBB);
      IRB.CreateBr(existBB);*/
      //errs()<<"*BogusBB"<<*BogusBB<<"\n";


      BasicBlock *BogusBB = createAlteredBasicBlock(basicBlock, "", &F);
      IRBuilder<> IRB(context);
      IRB.SetInsertPoint(BogusBB);
      IRB.CreateBr(existBB);



      TerminatorInst * last= basicBlock->getTerminator();
      last->eraseFromParent();
      //errs()<<"last"<<last<<"\n";
      
      BranchInst::Create(BogusBB, existBB,(Value *) arCI, basicBlock);


      return true;
    }









    void addJumpFlow(Function &F,int type){
      Module* module = F.getParent();
      Module& M = *module;
      LLVMContext& context = M.getContext();
      //For creating symbolic opaque predicates
      Value *argValue;
      Type* argType;

      for (Function::arg_iterator argIt = F.arg_begin(); argIt != F.arg_end(); ++argIt){
        argValue = &*argIt;
        argType = argValue->getType();
        if(argType->isIntegerTy()){
          break;
        }
      }


      std::vector<Instruction*> toEdit_2;
      // Looking for the conditions and branches to transform
      for(Module::iterator mi = M.begin(), me = M.end(); mi != me; ++mi){
        for(Function::iterator fi = mi->begin(), fe = mi->end(); fi != fe; ++fi){
          //fi->setName("");
          TerminatorInst * tbb= fi->getTerminator();
          if(tbb->getOpcode() == Instruction::Br){
            BranchInst * br = (BranchInst *)(tbb);
            if(br->isConditional()){
              ICmpInst * cond = (ICmpInst *)br->getCondition();
              unsigned opcode = cond->getOpcode();
              if(opcode == Instruction::ICmp){
                  toEdit_2.push_back(tbb);    // The branch using the condition                
              }
             }
           }
         }
       }
            

 
      if(type==2){
         for(std::vector<Instruction*>::iterator it =toEdit_2.begin(); it!=toEdit_2.end(); ++it){ 
           while(num2<OpqNum){
             Instruction* inst=*it;
             EnhanceArrayOpq(M, inst, argValue,2);
             num2++;
           }

         }  
       } 
      if(type==4){
         for(std::vector<Instruction*>::iterator it =toEdit_2.begin(); it!=toEdit_2.end(); ++it){ 
           while(num4<OpqNum){
             Instruction* inst=*it;
             EnhanceArrayOpq(M, inst, argValue,4);
             num4++;
           }
         }  
       } 



    } // end of addJumpFlow


    //algorithm1--OP_II or algorithm2--OP_II
    bool EnhanceArrayOpq(Module &M, Instruction* inst, Value* arg,int type){
      Type* argType = arg->getType();


      LLVMContext& context = M.getContext();

      const DataLayout &DL = M.getDataLayout(); // ?????
      AllocaInst* jAI = new AllocaInst(argType, DL.getAllocaAddrSpace(), "", inst);
      StoreInst* jSI = new StoreInst(arg, jAI, inst);
      LoadInst* jLI = new LoadInst(jAI, "", inst);

      BinaryOperator* remBO;
      BinaryOperator* remBO1;
      if(((IntegerType*) argType)->getBitWidth() != 64)
      {
        CastInst* j64CI = new SExtInst(jLI, i64Type, "idxprom", inst);
        remBO1 = BinaryOperator::Create(Instruction::SRem, j64CI, ci9_64, "rem", inst);      
      } 
      else 
      {
        remBO1 = BinaryOperator::Create(Instruction::SRem, jLI, ci9_64, "rem", inst);
      }

      remBO = BinaryOperator::Create(Instruction::Add, remBO1, ci1_64, "", inst);

      ArrayType* arAT = ArrayType::get(i64Type, 10);

      AllocaInst* array1AI = new AllocaInst(arAT, DL.getAllocaAddrSpace(), "", inst); // ?????

      std::vector<Value*> vec00;
      vec00.push_back(ci0_32);
      vec00.push_back(ci0_64);
      ArrayRef<Value*> ar00(vec00);
      std::vector<Value*> vec01;
      vec01.push_back(ci0_32);
      vec01.push_back(ci1_64);
      ArrayRef<Value*> ar01(vec01);
      std::vector<Value*> vec02;
      vec02.push_back(ci0_32);
      vec02.push_back(ci2_64);
      ArrayRef<Value*> ar02(vec02);
      std::vector<Value*> vec03;
      vec03.push_back(ci0_32);
      vec03.push_back(ci3_64);
      ArrayRef<Value*> ar03(vec03);
      std::vector<Value*> vec04;
      vec04.push_back(ci0_32);
      vec04.push_back(ci4_64);
      ArrayRef<Value*> ar04(vec04);
      std::vector<Value*> vec05;
      vec05.push_back(ci0_32);
      vec05.push_back(ci5_64);
      ArrayRef<Value*> ar05(vec05);
      std::vector<Value*> vec06;
      vec06.push_back(ci0_32);
      vec06.push_back(ci6_64);
      ArrayRef<Value*> ar06(vec06);
      std::vector<Value*> vec07;
      vec07.push_back(ci0_32);
      vec07.push_back(ci7_64);
      ArrayRef<Value*> ar07(vec07);
      std::vector<Value*> vec08;
      vec08.push_back(ci0_32);
      vec08.push_back(ci8_64);
      ArrayRef<Value*> ar08(vec08);
      std::vector<Value*> vec09;
      vec09.push_back(ci0_32);
      vec09.push_back(ci9_64);
      ArrayRef<Value*> ar09(vec09);

      Instruction* a10EPI = GetElementPtrInst::CreateInBounds((Value *) array1AI, ar00, "l1_arrayidx", inst);
      Instruction* a11EPI = GetElementPtrInst::CreateInBounds((Value *) array1AI, ar01, "l1_arrayidx", inst);
      Instruction* a12EPI = GetElementPtrInst::CreateInBounds((Value *) array1AI, ar02, "l1_arrayidx", inst);
      Instruction* a13EPI = GetElementPtrInst::CreateInBounds((Value *) array1AI, ar03, "l1_arrayidx", inst);
      Instruction* a14EPI = GetElementPtrInst::CreateInBounds((Value *) array1AI, ar04, "l1_arrayidx", inst);
      Instruction* a15EPI = GetElementPtrInst::CreateInBounds((Value *) array1AI, ar05, "l1_arrayidx", inst);
      Instruction* a16EPI = GetElementPtrInst::CreateInBounds((Value *) array1AI, ar06, "l1_arrayidx", inst);
      Instruction* a17EPI = GetElementPtrInst::CreateInBounds((Value *) array1AI, ar07, "l1_arrayidx", inst);
      Instruction* a18EPI = GetElementPtrInst::CreateInBounds((Value *) array1AI, ar08, "l1_arrayidx", inst);
      Instruction* a19EPI = GetElementPtrInst::CreateInBounds((Value *) array1AI, ar09, "l1_arrayidx", inst);

      StoreInst* a10SI = new StoreInst(ci0_64, a10EPI, inst);
      StoreInst* a11SI = new StoreInst(ci1_64, a11EPI, inst);
      StoreInst* a12SI = new StoreInst(ci2_64, a12EPI, inst);
      StoreInst* a13SI = new StoreInst(ci3_64, a13EPI, inst);
      StoreInst* a14SI = new StoreInst(ci4_64, a14EPI, inst);
      StoreInst* a15SI = new StoreInst(ci5_64, a15EPI, inst);
      StoreInst* a16SI = new StoreInst(ci6_64, a16EPI, inst);
      StoreInst* a17SI = new StoreInst(ci7_64, a17EPI, inst);
      StoreInst* a18SI = new StoreInst(ci8_64, a18EPI, inst);
      StoreInst* a19SI = new StoreInst(ci9_64, a19EPI, inst);

      std::vector<Value*> l1Vec;
      l1Vec.push_back(ci0_32);
      l1Vec.push_back(remBO);
      ArrayRef<Value*> l1AR(l1Vec);
      Instruction* l1EPI = GetElementPtrInst::CreateInBounds((Value *) array1AI, l1AR, "l1_arrayidx", inst);
      LoadInst* l1LI = new LoadInst(l1EPI, "", false, inst);

      std::vector<Value*> l2Vec;
      l2Vec.push_back(ci0_32);
      l2Vec.push_back(l1LI);
      ArrayRef<Value*> l2AR(l2Vec);
      Instruction* l2EPI = GetElementPtrInst::CreateInBounds((Value *) array1AI, l2AR, "l2_arrayidx", inst);
      LoadInst* l2LI = new LoadInst(l2EPI, "", false, inst);


      ICmpInst* arCI;
      if(type==2){
        //here we get l2LI!=remBO,which is nest_var!=arg%9
        arCI = new ICmpInst(inst, ICmpInst::ICMP_NE, l2LI, remBO1, "cmp");
      }
      else if(type==4){
        //将l2LI转化为int类型
        //errs()<<"turn l2LI into type int \n";
        Value* val=l2LI->getPointerOperand();
        //errs()<<"val"<<val<< "\n";
        Value *r_nv=GetResult_value(M,inst,val);
        CastInst* r_nvCI = new SExtInst(r_nv, i64Type, "", inst);
        arCI = new ICmpInst(inst, ICmpInst::ICMP_NE, r_nvCI, remBO1, "cmp");
      }


       


     //获取指令inst所在基本块basicBlock      
      BasicBlock *basicBlock=inst->getParent();
      
      //从inst处分割基本块，inst前面的指令置于前基本块，后面的置于新基本块existBB中
      Twine *var;
      var = new Twine("existBB");
      BasicBlock *existBB = basicBlock->splitBasicBlock(inst, *var);

      //删除arCI 与existBB间的自动跳转指令
      TerminatorInst * last= basicBlock->getTerminator();
      //errs() << "br instruction need to delete is " << *last <<"\n";
      last->eraseFromParent();
      
      //创建跳转。当arCI为真时其跳转到基本块existBB,否则跳转到另一个基本块((BranchInst*) inst)->getSuccessor(1)
      BranchInst::Create(existBB, ((BranchInst*) inst)->getSuccessor(1),(Value *) arCI, ((BranchInst*) arCI)->getParent());
      

      //BranchInst::Create(((BranchInst*) inst)->getSuccessor(0), ((BranchInst*) inst)->getSuccessor(1),(Value *) arCI, ((BranchInst*) inst)->getParent());
      //inst->eraseFromParent(); // erase the branch
      return true;
    }



    //algorithm2--opI
    bool InsertTentOpq(Function& F, Module &M, Instruction* inst, Value* arg){
      Type* argType = arg->getType();


      LLVMContext& context = M.getContext();

      const DataLayout &DL = M.getDataLayout(); // ?????
      AllocaInst* jAI = new AllocaInst(argType, DL.getAllocaAddrSpace(), "", inst);
      StoreInst* jSI = new StoreInst(arg, jAI, inst);
      LoadInst* jLI = new LoadInst(jAI, "", inst);

      
      Value *r1=GetResult(M,inst,1);
      //This class represents a sign extension of integer types.
      CastInst* rCI1 = new SExtInst(r1, i64Type, "", inst);


      BinaryOperator *op,*op1 = NULL;
      if(((IntegerType*) argType)->getBitWidth() != 64)
      {
        CastInst* j64CI = new SExtInst(jLI, i64Type, "idxprom", inst);
        op= BinaryOperator::Create(Instruction::Add, j64CI, rCI1, "", inst);      
        op1 = BinaryOperator::Create(Instruction::Mul, j64CI, op, "", inst);
      } 
      else 
      {
        op= BinaryOperator::Create(Instruction::Add, jLI, rCI1, "", inst);
        op1 = BinaryOperator::Create(Instruction::Mul, jLI, op, "", inst);
      }
  
      Value *r2=GetResult(M,inst,2);
      CastInst* rCI2 = new SExtInst(r2, i64Type, "", inst);
      op = BinaryOperator::Create(Instruction::SRem, op1, rCI2, "", inst);



      Value *r0=GetResult(M,inst,0);
      CastInst* rCI0 = new SExtInst(r0, i64Type, "", inst);
      ICmpInst* arCI = new ICmpInst(inst, ICmpInst::ICMP_NE, op, rCI0, "cmp");



      //获取指令inst所在基本块basicBlock      
      BasicBlock *basicBlock=inst->getParent();
      
      //从inst处分割基本块，inst前面的指令置于前基本块，后面的置于新基本块existBB中
      Twine *var;
      var = new Twine("existBB");
      BasicBlock *existBB = basicBlock->splitBasicBlock(inst, *var);
      //errs()<<"existBB"<<*existBB<<"\n";

/*
      //创建基本块BogusBB 
      BasicBlock *BogusBB = BasicBlock::Create (context, "bogus",&F,existBB ); 
      IRBuilder<> IRB(context);    
      IRB.SetInsertPoint(BogusBB);
      BinaryOperator* bogusIns=BinaryOperator::Create(Instruction::Add, jLI, ci1_64, "", BogusBB);
      IRB.CreateBr(existBB);*/

      BasicBlock *BogusBB = createAlteredBasicBlock(basicBlock, "", &F);
      IRBuilder<> IRB(context);
      IRB.SetInsertPoint(BogusBB);
      IRB.CreateBr(existBB);



      TerminatorInst * last= basicBlock->getTerminator();
      last->eraseFromParent();
      //errs()<<"last"<<last<<"\n";
      
      BranchInst::Create(BogusBB, existBB,(Value *) arCI, basicBlock);      

      return true;
    }

    //only test
    void addExtrenFunc(Function& F){
      Module* module = F.getParent();
      Module& M = *module;
      //errs()<<"==== "<< F.getName()<< "\n";
      if(F.getName()=="main"){
        //errs()<<"main EntryBlock()  "<<F.getEntryBlock()<<"\n";
        BasicBlock *bb=&F.getEntryBlock();        
        Instruction* inst=bb->getFirstNonPHI();
        //errs()<<"first instrucion is "<< *inst <<"\n";
        Value *r=GetResult(M,inst,1);
        //errs()<<"fh:"<<*r<<"\n";
      }
    }

    Value *GetResult(Module &M, Instruction *inst,int value){
      //errs()<<"value="<<value<<"\n";
      LLVMContext& context = M.getContext();
      IRBuilder<> builder(context);

      std::vector<Type *> params(1,Type::getInt32Ty(context) ); 
      //FunctionType::get调用用于为给定的函数原型创建对应的FunctionType对象
      FunctionType *FuncTy = FunctionType::get(builder.getInt32Ty(), params, false);
    
      //Creates a new function and attaches it to a module.
      AttributeList func_printf_PAL;
      Function *func = cast<Function>(M.getOrInsertFunction("solve", FuncTy,func_printf_PAL));

      //The default llvm calling convention, compatible with C.
      func->setCallingConv(CallingConv::C); 
   
      builder.SetInsertPoint(inst);
      std::vector<Value *> call_params;
      //Value *print_str = builder.CreateGlobalStringPtr(value);
      Value* input = ConstantInt::get(Type::getInt32Ty(context), value);	
      call_params.push_back(input);

      Value *ret = builder.CreateCall(func, call_params);

      Type* ret_Type = ret->getType();
      const DataLayout &DL = M.getDataLayout();
      AllocaInst* ret_AI = new AllocaInst(ret_Type, DL.getAllocaAddrSpace(), "", inst);
      StoreInst* ret_SI = new StoreInst(ret, ret_AI, inst);
      LoadInst* ret_LI = new LoadInst(ret_AI, "", inst);

      return ret_LI;
    }



    Value *GetResult_value(Module &M, Instruction *inst,Value* value){
      LLVMContext& context = M.getContext();
      IRBuilder<> builder(context);

      std::vector<Type *> params(1,Type::getInt32Ty(context) ); 
      //FunctionType::get调用用于为给定的函数原型创建对应的FunctionType对象
      FunctionType *FuncTy = FunctionType::get(builder.getInt32Ty(), params, false);
    
      //Creates a new function and attaches it to a module.
      AttributeList func_printf_PAL;
      Function *func = cast<Function>(M.getOrInsertFunction("solve", FuncTy,func_printf_PAL));

      //The default llvm calling convention, compatible with C.
      func->setCallingConv(CallingConv::C); 
   
      builder.SetInsertPoint(inst);
      std::vector<Value *> call_params;	
      call_params.push_back(value);

      Value *ret = builder.CreateCall(func, call_params);

      Type* ret_Type = ret->getType();
      const DataLayout &DL = M.getDataLayout();
      AllocaInst* ret_AI = new AllocaInst(ret_Type, DL.getAllocaAddrSpace(), "", inst);
      StoreInst* ret_SI = new StoreInst(ret, ret_AI, inst);
      LoadInst* ret_LI = new LoadInst(ret_AI, "", inst);

      return ret_LI;
    }


    /* createAlteredBasicBlock
     *
     * This function return a basic block similar to a given one.
     * It's inserted just after the given basic block.
     * The instructions are similar but junk instructions are added between
     * the cloned one. The cloned instructions' phi nodes, metadatas, uses and
     * debug locations are adjusted to fit in the cloned basic block and
     * behave nicely.
     */
    virtual BasicBlock* createAlteredBasicBlock(BasicBlock * basicBlock,
        const Twine &  Name = "gen", Function * F = 0){
      // Useful to remap the informations concerning instructions.
      ValueToValueMapTy VMap;
      BasicBlock * alteredBB = llvm::CloneBasicBlock (basicBlock, VMap, Name, F);
      DEBUG_WITH_TYPE("gen", errs() << "bcf: Original basic block cloned\n");
      // Remap operands.
      BasicBlock::iterator ji = basicBlock->begin();
      for (BasicBlock::iterator i = alteredBB->begin(), e = alteredBB->end() ; i != e; ++i){
        // Loop over the operands of the instruction
        for(User::op_iterator opi = i->op_begin (), ope = i->op_end(); opi != ope; ++opi){
          // get the value for the operand
          Value *v = MapValue(*opi, VMap,  RF_None, 0);
          if (v != 0){
            *opi = v;
            DEBUG_WITH_TYPE("gen", errs() << "bcf: Value's operand has been setted\n");
          }
        }
        DEBUG_WITH_TYPE("gen", errs() << "bcf: Operands remapped\n");
        // Remap phi nodes' incoming blocks.
        if (PHINode *pn = dyn_cast<PHINode>(i)) {
          for (unsigned j = 0, e = pn->getNumIncomingValues(); j != e; ++j) {
            Value *v = MapValue(pn->getIncomingBlock(j), VMap, RF_None, 0);
            if (v != 0){
              pn->setIncomingBlock(j, cast<BasicBlock>(v));
            }
          }
        }
        DEBUG_WITH_TYPE("gen", errs() << "bcf: PHINodes remapped\n");
        // Remap attached metadata.
        SmallVector<std::pair<unsigned, MDNode *>, 4> MDs;
        i->getAllMetadata(MDs);
        DEBUG_WITH_TYPE("gen", errs() << "bcf: Metadatas remapped\n");
        // important for compiling with DWARF, using option -g.
        i->setDebugLoc(ji->getDebugLoc());
        ji++;
        DEBUG_WITH_TYPE("gen", errs() << "bcf: Debug information location setted\n");

      } // The instructions' informations are now all correct

      DEBUG_WITH_TYPE("gen", errs() << "bcf: The cloned basic block is now correct\n");
      DEBUG_WITH_TYPE("gen",
          errs() << "bcf: Starting to add junk code in the cloned bloc...\n");

      // add random instruction in the middle of the bloc. This part can be improve
      for (BasicBlock::iterator i = alteredBB->begin(), e = alteredBB->end() ; i != e; ++i){
        // in the case we find binary operator, we modify slightly this part by randomly
        // insert some instructions
        if(i->isBinaryOp()){ // binary instructions
          unsigned opcode = i->getOpcode();
          BinaryOperator *op, *op1 = NULL;
          Twine *var = new Twine("_");
          // treat differently float or int
          // Binary int
          if(opcode == Instruction::Add || opcode == Instruction::Sub ||
              opcode == Instruction::Mul || opcode == Instruction::UDiv ||
              opcode == Instruction::SDiv || opcode == Instruction::URem ||
              opcode == Instruction::SRem || opcode == Instruction::Shl ||
              opcode == Instruction::LShr || opcode == Instruction::AShr ||
              opcode == Instruction::And || opcode == Instruction::Or ||
              opcode == Instruction::Xor){
            for(int random = (int)llvm::cryptoutils->get_range(10); random < 10; ++random){
              switch(llvm::cryptoutils->get_range(4)){ // to improve
                case 0: //do nothing
                  break;
                case 1: op = BinaryOperator::CreateNeg(i->getOperand(0),*var,&*i);
                        op1 = BinaryOperator::Create(Instruction::Add,op,
                            i->getOperand(1),"gen",&*i);
                        break;
                case 2: op1 = BinaryOperator::Create(Instruction::Sub,
                            i->getOperand(0),
                            i->getOperand(1),*var,&*i);
                        op = BinaryOperator::Create(Instruction::Mul,op1,
                            i->getOperand(1),"gen",&*i);
                        break;
                case 3: op = BinaryOperator::Create(Instruction::Shl,
                            i->getOperand(0),
                            i->getOperand(1),*var,&*i);
                        break;
              }
            }
          }
          // Binary float
          if(opcode == Instruction::FAdd || opcode == Instruction::FSub ||
              opcode == Instruction::FMul || opcode == Instruction::FDiv ||
              opcode == Instruction::FRem){
            for(int random = (int)llvm::cryptoutils->get_range(10); random < 10; ++random){
              switch(llvm::cryptoutils->get_range(3)){ // can be improved
                case 0: //do nothing
                  break;
                case 1: op = BinaryOperator::CreateFNeg(i->getOperand(0),*var,&*i);
                        op1 = BinaryOperator::Create(Instruction::FAdd,op,
                            i->getOperand(1),"gen",&*i);
                        break;
                case 2: op = BinaryOperator::Create(Instruction::FSub,
                            i->getOperand(0),
                            i->getOperand(1),*var,&*i);
                        op1 = BinaryOperator::Create(Instruction::FMul,op,
                            i->getOperand(1),"gen",&*i);
                        break;
              }
            }
          }
          if(opcode == Instruction::ICmp){ // Condition (with int)
            ICmpInst *currentI = (ICmpInst*)(&i);
            switch(llvm::cryptoutils->get_range(3)){ // must be improved
              case 0: //do nothing
                break;
              case 1: currentI->swapOperands();
                      break;
              case 2: // randomly change the predicate
                      switch(llvm::cryptoutils->get_range(10)){
                        case 0: currentI->setPredicate(ICmpInst::ICMP_EQ);
                                break; // equal
                        case 1: currentI->setPredicate(ICmpInst::ICMP_NE);
                                break; // not equal
                        case 2: currentI->setPredicate(ICmpInst::ICMP_UGT);
                                break; // unsigned greater than
                        case 3: currentI->setPredicate(ICmpInst::ICMP_UGE);
                                break; // unsigned greater or equal
                        case 4: currentI->setPredicate(ICmpInst::ICMP_ULT);
                                break; // unsigned less than
                        case 5: currentI->setPredicate(ICmpInst::ICMP_ULE);
                                break; // unsigned less or equal
                        case 6: currentI->setPredicate(ICmpInst::ICMP_SGT);
                                break; // signed greater than
                        case 7: currentI->setPredicate(ICmpInst::ICMP_SGE);
                                break; // signed greater or equal
                        case 8: currentI->setPredicate(ICmpInst::ICMP_SLT);
                                break; // signed less than
                        case 9: currentI->setPredicate(ICmpInst::ICMP_SLE);
                                break; // signed less or equal
                      }
                      break;
            }

          }
          if(opcode == Instruction::FCmp){ // Conditions (with float)
            FCmpInst *currentI = (FCmpInst*)(&i);
            switch(llvm::cryptoutils->get_range(3)){ // must be improved
              case 0: //do nothing
                break;
              case 1: currentI->swapOperands();
                      break;
              case 2: // randomly change the predicate
                      switch(llvm::cryptoutils->get_range(10)){
                        case 0: currentI->setPredicate(FCmpInst::FCMP_OEQ);
                                break; // ordered and equal
                        case 1: currentI->setPredicate(FCmpInst::FCMP_ONE);
                                break; // ordered and operands are unequal
                        case 2: currentI->setPredicate(FCmpInst::FCMP_UGT);
                                break; // unordered or greater than
                        case 3: currentI->setPredicate(FCmpInst::FCMP_UGE);
                                break; // unordered, or greater than, or equal
                        case 4: currentI->setPredicate(FCmpInst::FCMP_ULT);
                                break; // unordered or less than
                        case 5: currentI->setPredicate(FCmpInst::FCMP_ULE);
                                break; // unordered, or less than, or equal
                        case 6: currentI->setPredicate(FCmpInst::FCMP_OGT);
                                break; // ordered and greater than
                        case 7: currentI->setPredicate(FCmpInst::FCMP_OGE);
                                break; // ordered and greater than or equal
                        case 8: currentI->setPredicate(FCmpInst::FCMP_OLT);
                                break; // ordered and less than
                        case 9: currentI->setPredicate(FCmpInst::FCMP_OLE);
                                break; // ordered or less than, or equal
                      }
                      break;
            }
          }
        }
      }
      return alteredBB;
    } // end of createAlteredBasicBlock()




  }; // end of struct BogusControlFlow : public FunctionPass
}

char BogusControlFlow::ID = 0;
static RegisterPass<BogusControlFlow> X("boguscf", "inserting bogus control flow");

Pass *llvm::createBogus() {
  return new BogusControlFlow();
}

Pass *llvm::createBogus(bool flag) {
  return new BogusControlFlow(flag);
}