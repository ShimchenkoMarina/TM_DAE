#include "TM_DAE_integrated.h"

void TM_DAE_INTGR_pass::markLoop(Loop * L)
{	
	//Don't mark it if it has been alredy marked
	bool isLoopMarked = (L->getHeader()->getName().str().find(KERNEL_MARKING) != string::npos);
	if (isLoopMarked)
		return;
	bool doExtract = true;
	BasicBlock *H = L->getHeader();
	//Don't want to mark loop for getting lock
	//It is unnesseccary troubles
	for (auto &I: *H)
	{
		if (isa<CallInst>(&I) && !dyn_cast<CallInst>(&I)->isInlineAsm())
		{
			CallInst * CI = dyn_cast<CallInst>(&I);
			//Don't want to target loops for getting locks									
			StringRef name = get_function_name(CI);
			if (name == "RTM_fallback_isLocked")
			{
				doExtract = false;
				break;
			}
			
		}
	}
	if (doExtract)
	{
		string funName = H->getParent()->getName().str();
		//celan function name, deleting redundant suffixes
		std::size_t found = funName.find(MAIN_FUNCTION_MARKING);
		while (found != std::string::npos)
		{
			funName.replace(found, MAIN_FUNCTION_MARKING_SIZE, "");
		 	found = funName.find(MAIN_FUNCTION_MARKING);
		}
	     	found = funName.find(TX_MARKING);
		while (found != std::string::npos)
		{
			funName.replace(found, TX_MARKING_SIZE, "");
		 	found = funName.find(TX_MARKING);
		}

		H->setName(Twine(KERNEL_MARKING + funName));
		//outs() << "MARKING loops #################################################################################### name =" << H->getParent()->getName() << " , " << H->getName()<<  "\n";
		std::vector<Loop *> subLoops = L->getSubLoops();
		for (auto &loop: subLoops)
		{
			markLoop(loop);
		}
	}
}

//#define AGGRESSION
bool TM_DAE_INTGR_pass::MarkEverything(Function &F, bool mark)
{
	bool once = false;
	for (Function::iterator it = F.begin();;)
	{
		if (it == F.end())
			break;
		BasicBlock * BB = &*it;
		if(isTargetBB(*BB, MODE::START))
		{
			//We want to mark it only once
			//Even if there are several TM inside
			if(!once && F.getName().str().find(MAIN_FUNCTION_MARKING) == string::npos && mark)
			{
				F.setName(Twine(MAIN_FUNCTION_MARKING + F.getName().str()));
				once = true;
			}
			parseCallGraph(*BB, false, mark);	
			//TXBBs.push_back(TXBB);
			FirstInnerBB = nullptr;
			stop = false;
			txDetected = false;
			//UsedBBs.clear();
			loop_depth = 0;
			if (do_it_again)
			{
				parseCallGraph(*BB, false, mark);
				do_it_again = false;
				FirstInnerBB = nullptr;
				stop = false;
				txDetected = false;
				//UsedBBs.clear();
				loop_depth = 0;
	
			}
			
		}
		++it;
	}
}

void TM_DAE_INTGR_pass::parseCallGraph(BasicBlock &BB, bool insideFun, bool mark)
{
	if (stop)
		return;
	//outs() << "Parse\n";
	//if BB was visited then don't do anything
	for (auto &bb: UsedBBs)
	{
		if (bb == &BB)
		{
			//outs() << "Used\n";
			return;
		}
				
	}
	//If BB wasn't visited then marked it as visited
	UsedBBs.push_back(&BB);	
	if (txInnerDetected && !insideFun)
	{
		TXBB.push_back(&BB);
	}
	
	//Mark Loop, only during a marking stage
	if (txDetected && mark && txInnerDetected)
	{
		for (auto *LI: LIBV)
		{
			Loop * L = LI->getLoopFor(&BB);
			int depth = (*LI).getLoopDepth(&BB);
			if ((L != NULL && !insideFun && depth > loop_depth) || (L != NULL && insideFun))
			{
				//outs() << "This BB is a loop########################################################### " << (*(&BB)->getTerminator())<< "\n";
				markLoop(L);
			}	
		}
	}
	//For each instruction check whether it is a function call 
	//If it's not a function call then do nothing with this instruction
	//If it's a function call, go inside this function after marking it
   	bool res = true;
	BasicBlock *BBC = &BB;
	BasicBlock::iterator it = BBC->begin();
	Instruction *I = &*it;
	while(res)
	{
		//outs() << "Instruction is proccessed: " << *I << "\n";
		//First check whether it is a call
		if (isa<CallInst>(I) && !dyn_cast<CallInst>(I)->isInlineAsm())
		{	
			#ifdef DEBUGE
			outs() << "Instruction is proccessed: " << *I << "\n";
			#endif
			//TODO: delete if it is redundant
			CallInst * CI = dyn_cast<CallInst>(I);
											
			StringRef name = get_function_name(CI);
			Function *fun = CI->getCalledFunction();
			if (fun == NULL)
			{
				if (Function * bitcastFunction = dyn_cast<Function>(CI->getCalledValue()->stripPointerCasts()))
				{
					if (bitcastFunction != NULL && !bitcastFunction->isIntrinsic())
					{
						//outs() << "Bitcast!\n";
						fun = bitcastFunction;
						name = fun->getName().str();
					}
				}
			}
			//outs() << "name =" << name << " txDetect = "<< txDetected<< "\n";
			if (txDetected && txInnerDetected){
				if (name.find("InnerPartEnd") != string::npos)
				{
					if (BBC == FirstInnerBB)
					{
						TXBBs.push_back(TXBB);
						TXBB.clear();
						txInnerDetected = false;
						txDetected = false;
						FirstInnerBB = nullptr;
						stop = true;
					}
					//outs() << "InnerPartEnd and flag = " << txInnerDetected << "\n";
					//txInnerDetected = false;
					BasicBlock * block = (I)->getParent()->splitBasicBlock(I, Twine((I)->getParent()->getName().str() + "splitedE"));					
					UsedBBs.push_back(block);	
					//BBC = block;
					//it = BBC->begin();
					return;
				}else /*if (name == "fakeCallEnd")
				{
					//outs() << "fakeCallEnd" << "\n";
					return;
				}
				else*/
				{	//another call
					//TODO:
					//Unfortunatelly asm insert is inderect call, but
					//currently I don't know how to check it.
					//Don't want to deal with loops inside RTM_fallback_lock function
					if (name != "inderect call" && name != "RTM_fallback_lock" && name!= "RTM_fallback_isLocked" && name != "RTM_fallback_unlock")
					{
						/*Function *fun = CI->getCalledFunction();
						if (auto* CstExpr = dyn_cast<ConstantExpr>(I->getOperand(0)))
						{
							if (CstExpr->isCast() && isa<Function>(CstExpr->getOperand(0)))
							{
								fun = dyn_cast<Function>(CstExpr->getOperand(0));
								//outs() << "Wierd thing: " << fun->getName() << "\n";
							}
						}*/

						//outs() << "FUNCTION CALL:" << name << "\n";
						if (!(fun->isDeclaration()))
						{
							if (mark && fun->getName().str().find(FUNCTION_MARKING) == string::npos)
							{
								fun->setName(Twine(FUNCTION_MARKING + fun->getName().str()));
							}
							#ifdef DEBUGE
							outs() << "FUNCTION CALL:" << fun->getName().str() << "\n";
							#endif
							//Update info for function
							llvm::DominatorTree DT = llvm::DominatorTree();
							DT.recalculate(*fun);

							LoopInfoBase<BasicBlock, Loop> * KLoop = new LoopInfoBase<BasicBlock, Loop>();
							KLoop->releaseMemory();
							KLoop->analyze(DT);
									
							LIBV.push_back(KLoop);
							//for (auto &BBfun: *fun)
							//{
							//BasicBlock *BBfun = fun->getEntryBlock();
							//outs()<< "Parse call graph:begin " << fun->getName().str() << "\n";
							parseCallGraph(fun->getEntryBlock(), true, mark);
							if (auto* CstExpr = dyn_cast<ConstantExpr>(I->getOperand(0)))
							{
								if (CstExpr->isCast() && isa<Function>(CstExpr->getOperand(0)))
								{
									fun = dyn_cast<Function>(CstExpr->getOperand(0));
									if (!(fun->isDeclaration()))
									{
										if (mark && fun->getName().str().find(FUNCTION_MARKING) == string::npos)
										{
											fun->setName(Twine(FUNCTION_MARKING + fun->getName().str()));
										}
										#ifdef DEBUGE
										outs() << "FUNCTION CALL:" << fun->getName().str() << "\n";
										#endif
										//Update info for function
										llvm::DominatorTree DT = llvm::DominatorTree();
										DT.recalculate(*fun);

										LoopInfoBase<BasicBlock, Loop> * KLoop = new LoopInfoBase<BasicBlock, Loop>();
										KLoop->releaseMemory();
										KLoop->analyze(DT);
									
										LIBV.push_back(KLoop);
										//for (auto &BBfun: *fun)
										//{
										//BasicBlock *BBfun = fun->getEntryBlock();
										//outs()<< "Parse call graph:begin " << fun->getName().str() << "\n";
										parseCallGraph(fun->getEntryBlock(), true, mark);
									}
								}
							}

							//outs()<< "Parse call graph:end " << fun->getName().str() << "\n";
							if (stop)
							{
								outs() << "RETURN\n";
								return;
							}
							//}
						}
					}else{
						//outs() << "Inderect call --> ";
						//outs() << I << "\n";
					}
				}
						
			}
			if (name == "beginTransaction")
			{
				//Check whether TX is inside loop
				//if it is a case then
				//Instruction is inside a loop only if this loop's depth is 2
				//outs() << "Function put name: " << BBC->getParent()->getName().str() << "Inner = " << txInnerDetected << " TX flag =" << txDetected<< "\n";
				FirstInstV.push_back(I);
				txDetected = true;
				isInstInsideLoop(I, true);
				const TerminatorInst *TInst = I->getParent()->getTerminator();
				unsigned numSuccs = TInst->getNumSuccessors();
				if (numSuccs > 1)
				{
					do_it_again = true;
					//outs() << "\n\nAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA\n\n";
				}
			}
			if (txDetected && (name.find("InnerPartBegin") != string::npos))
			{
				//outs() << "Ola\n";
				++it;
				if (it == BBC->end())
				{
					break;
				}else
				{
					I = &*it;
					//outs() << "Instruction: " << &I << "\n";
				}
				BasicBlock * block = (I)->getParent()->splitBasicBlock(I, Twine((I)->getParent()->getName().str() + "splitedB"));
				BBC = block;	
				FirstInnerBB = BBC;
				//FirstInnerBBs.push_back(BBC);
				it = BBC->begin();
				TXBB.push_back(BBC);
				UsedBBs.push_back(block);	
				txInnerDetected = true;
				//outs() << "InnerPartBegin and size = " << TXBB.size() <<" BB "<< BBC->getParent()->getName().str() <<"\n";
			}else
			{
				++it;
				if (it == BBC->end())
				{
					//outs() << "BB is ended "<< *(BBC->getTerminator())<< "\n";
					res = false;
				}else
				{
					I = &*it;
				}
			}
						
		}else
		{
			++it;
			if (it == BBC->end())
			{
				//outs() << "BB is ended "<< *(BBC->getTerminator())<< "\n";
				res = false;
			}else
			{
				I = &*it;
			}
		}
		
	}
	bool check;
	//If TxEnd wasn't found in current BB
	//TODO: appropriatly go throug complex CFGs
	//outs() << "BB's serach for succs "<< *(BBC->getTerminator())<< "\n";
	//if (!isTargetBB(*BBC, MODE::END))
	//{
		//if (BBC == FirstInnerBB)
			//outs() << "\n\nGot it\n\n";
		//RTM_fallbacl_unlock wasn't found in current function
		const TerminatorInst *TInst = BBC->getTerminator();
		for(unsigned I = 0, NSucc = TInst->getNumSuccessors(); I < NSucc; ++I)
		{
			check = false;
			BasicBlock *Succ = TInst->getSuccessor(I);
			
			for (auto &bb: UsedBBs)
			{
				//Already visited this BasicBlock
				//Skip it
				if (Succ == bb)
				{
					check = true;
					continue;
				}
			}
			//If BB wasn't used
			if (!check)
			{
				//outs() << "Successor " << *TInst << "\n";
				parseCallGraph(*Succ, insideFun? true: false, mark);
				if (stop)
					return;
			}
		}
		if (BBC == FirstInnerBB)
		{	
			//outs() << "OK\n\n";
			TXBBs.push_back(TXBB);
			TXBB.clear();
			txInnerDetected = false;
			FirstInnerBB = nullptr;
			stop = true;
			return;
		}

	//}else
	/*{
		parseCallGraph(*(getTargetBB(*BBC)), insideFun? true: false, mark);
	}*/
	return;
}

void TM_DAE_INTGR_pass::AnnotateBranchesLoop(Loop *loop)
{
	SmallVector<BasicBlock *, 8> ExitingBlocks; 
	//SmallVector<BasicBlock *, 8> LoopLatches; 
	loop->getExitingBlocks(ExitingBlocks);
	//loop->getLoopLatches(LoopLatches);
	for (auto BB: ExitingBlocks)
	{
		TerminatorInst * TI = (&*BB)->getTerminator();
		outs() << "LoopExitingBranchi111111§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§\n";
		AttachMetadata(TI, "LoopExitBranch", "1");
	}
	/*for (auto BB: LoopLatches)
	{
		TerminatorInst * TI = (&*BB)->getTerminator();
		outs() << "LoopExitingBranch22222222§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§\n";
		AttachMetadata(TI, "LoopExitBranch", "1");
	}*/
	
	std::vector<Loop *> subLoops = loop->getSubLoops();
	for (auto &subloop: subLoops)
	{
		AnnotateBranchesLoop(subloop);				
	}
}



void TM_DAE_INTGR_pass::ExtractSubLoops(Loop *loop, DominatorTree *DTI, LoopInfo *LI)
{	
	std::vector<Loop *> subLoops = loop->getSubLoops();
	for (auto &subloop: subLoops)
	{
		//when subloop is inside not extracted loop
		bool isSubLoopMarked = (subloop->getHeader()->getName().str().find(KERNEL_MARKING) != string::npos)&& (subloop->getHeader()->getParent()->getName().str().find(KERNEL_MARKING) == string::npos);
		//when subloop is inside extracted loop
		bool isSubLoopMarkedSecond = (subloop->getHeader()->getName().str().find(KERNEL_MARKING) != string::npos) && (subloop->getHeader()->getParent()->getName().str().find(KERNEL_MARKING) != string::npos) && (subloop->getHeader()->getParent()->getName().str().find(FUNCTION_MARKING) == string::npos);

		if (isSubLoopMarked || isSubLoopMarkedSecond)
		{
			ExtractLoop(subloop, DTI, LI);
			DTI->recalculate(*(subloop->getHeader()->getParent()));
		}
		ExtractSubLoops(subloop, DTI, LI);
		
	}
	return;
}
void DAE_interproc_loop_helper(Function * func, vector<Function *> vectorFunc, vector<set<Function *>> vectorcalledFunctions)
{
	int iter = 0;
	StringRef Kind = "DAE-interproc";
	StringRef Val = "loop-related";
	for (Function * fun: vectorFunc)
	{
		if (fun == func)
		{
			break;
		}
		iter++;
	}
	
	for (auto F: vectorcalledFunctions[iter])
	{
		if (!F->hasFnAttribute(Kind))
		{
			F->addFnAttr(Kind, Val);
			DAE_interproc_loop_helper(F, vectorFunc, vectorcalledFunctions);
		}	
	}

	
}
void DAE_interproc_looprelated(vector<Function* > vectorFunc, vector<set<Function*>> vectorcalledFunctions)
{
	int iter = 0;
	StringRef Kind = "DAE-interproc";
	StringRef Kind2 = "DAE-interproc-rec";
	StringRef Val = "loop-related";
	for (Function * fun: vectorFunc)
	{
		string funName = fun->getName().str();
		if (funName.find(LOOP_MARKING) != string::npos || fun->hasFnAttribute(Kind2))
		{
			if (!fun->hasFnAttribute(Kind))
			{
				fun->addFnAttr(Kind, Val);	
				for (auto F: vectorcalledFunctions[iter])
				{
					F->addFnAttr(Kind, Val);
					DAE_interproc_loop_helper(F, vectorFunc, vectorcalledFunctions);	
				}
			}
		}
		iter++;
				
	}
}
void DeleteFnAttr(Function *f)
{
	outs() << "Hello\n";
	StringRef Kind = "DAE-interproc";
	StringRef Kind1 = "DAE-interproc-calledfrom";
	bool again = false;
	if (f->hasFnAttribute(Kind))
	{
		/*Module * Mod = f->getParent();
		AttributeSet AS = f->getAttributes();
		//AttributeSet AS_remove;
		AttrBuilder B(AS);
		B.removeAttribute(Kind);
		//AS_remove.addAttribute(Mod->getContext(), 0, f->getFnAttribute(Kind).getKindAsString());
		AS.dump();
		//f->setAttributes(AS.removeAttributes(Mod->getContext(), AttributeSet::FunctionIndex, cast<Attribute::AttrKind>(Kind)));
		//f->setAttributes(get(Mod->getContext(), B));
		AS.dump();
		again = true;*/
	}
	if (f->hasFnAttribute(Kind1))
	{
		Module * Mod = f->getParent();
		AttributeSet AS = f->getAttributes();
		AttributeSet AS_remove;
		AS_remove.addAttribute(Mod->getContext(), 0, f->getFnAttribute(Kind1).getKindAsString());
		f->setAttributes(AS.removeAttributes(Mod->getContext(), AttributeSet::FunctionIndex, AS_remove));
		again = true;
	}
	if (again)
	{
		DeleteFnAttr(f);
	}
}
//Main function
bool TM_DAE_INTGR_pass::runOnModule(Module &M){
	GVV.clear();
	for (auto gv_iter = M.global_begin(); gv_iter != M.global_end(); gv_iter++)
	{
		GlobalVariable * gv = &*gv_iter;
		//outs() << "Global value: " << *gv << "\n";
		GVV.push_back(gv);
	}
	if (OracleCount)
	{
		outs() << "Oracele count\n";
		for (Module::iterator MI = M.begin();;++MI)
		{
			if(MI == M.end())
				break;
			if (MI->isDeclaration())
				continue;
			if ((*MI).isIntrinsic() && (*MI).empty())
				continue;
			string funName = (*MI).getName().str();
			if ((funName.find(TX_MARKING) != string::npos) && (funName.find(CLONE_SUFFIX) == string::npos))
			{	
					outs() << "AP: " << funName << "\n";
					int load_inst = 0;
					int store_inst = 0;
					int pref_inst = 0;
					vector<Function* > array_of_func;
					array_of_func.push_back(&*MI);
					count_LOADS_STORES_PREF(array_of_func, &*MI, &load_inst, &store_inst, &pref_inst, false);
					outs() << "LOAD: " << load_inst << " STORE: " << store_inst << " PREF: " << pref_inst << "\n";
            				(&*MI)->removeFnAttr(Attribute::NoInline);
        				(&*MI)->addFnAttr(Attribute::AlwaysInline);
		
			}
		}
		
	}else
	//1. Parse call graph and identify loops of interests
	//TODO: make it simplier,we don't need half of functionality here
	//What was a reason for us to extract loops? 
	//Can not we work with them as with linear code?
	//
	//For SVF design we still need to extract TX into APs
	//but we need to process it differently
	//We also need to prepare all clone functions for TM_FUNCTIONS(functions inside TXs)
	if (JUSTINLINE || SVFPREP)
	{
		//Extract TX
		for (Module::iterator MI = M.begin();;++MI)
		{
			//outs() << "THis is before isDEclaration " << (*MI).getName().str() << "\n";
			if(MI == M.end())
				break;
			if (MI->isDeclaration())
				continue;
			if ((*MI).isIntrinsic() && (*MI).empty())
				continue;
			llvm::DominatorTree DTI = llvm::DominatorTree();
			DTI.recalculate(*MI);
			MarkEverything(*MI, true);
			if (TXBBs.size() == FirstInstV.size())
			{
				for (size_t i =0; i < TXBBs.size(); ++i)
				{
					//outs() << "Extractor preparetion\n";
					CodeExtractor Extractor(TXBBs[i],&DTI);
					Function *nF = Extractor.extractCodeRegion();
					if (nF != 0)
					{
						nF->addFnAttr(Attribute::AlwaysInline);
						nF->setName(Twine(TX_MARKING + nF->getName().str()));
						TMtoInstMap.push_back(std::make_pair(nF, FirstInstV[i]));
						//outs() << "Extracted" << nF->getName().str()<<"\n";
					}
				}
			}
			FirstInstV.clear();
			TXBB.clear();
			TXBBs.clear();

		}

		for (Module::iterator MI = M.begin();;MI++)
		{
			//if (MI->isDeclaration())
			//	continue;
			if(MI == M.end())
				break;
			if ((*MI).isIntrinsic() && (*MI).empty())
				continue;
			//If function is marked then it is a part of TM
			bool isMarked = ((*MI).getName().str().find(FUNCTION_MARKING) != string::npos); 
			//isMarked = ((*MI).getName().str().find("rbtree_verify") != string::npos); 
			//if (isMarked && (*MI).getName().str().find("TMfixAfterInsertion") == string::npos)
			if (isMarked)
			//if (isMarked)
			{
				llvm::DominatorTree DTI = llvm::DominatorTree();
				DTI.recalculate(*MI);
				LoopInfo * LI = &getAnalysis<LoopInfoWrapperPass>(*MI).getLoopInfo();
				for (LoopInfo::iterator it = LI->begin();;)
				{
					if (it == LI->end())
						break;
					Loop* loop = *it;
					//First condition is nesseccary because it points out targeted loop
					//Second condition is to avoid infinity loops: means that if this loop has been extracted, it was out into new function
					//So if this function found, don't do anything with it, everything has been done
					//bool isLoopMarked = (loop->getHeader()->getName().str().find(KERNEL_MARKING) != string::npos)&& (loop->getHeader()->getParent()->getName().str().find(KERNEL_MARKING) == string::npos);
					bool isLoopMarked = ((loop->getHeader()->getParent()->getName().str().find(FUNCTION_MARKING) != string::npos) && (loop->getHeader()->getParent()->getName().str().find(MAIN_FUNCTION_MARKING) == string::npos));
					isLoopMarked = isLoopMarked || (loop->getHeader()->getParent()->getName().str().find(TX_MARKING) != string::npos);
					if (isLoopMarked)
					{
						ExtractLoop(loop, &DTI, LI);
						DTI.recalculate(*MI);
						//outs() << "Loop goes to extracting" << loop->getHeader()->getName()<<"\n";
					}
				
					ExtractSubLoops(loop, &DTI, LI);
					DTI.recalculate(*MI);
					++it;
				}
			}
		}

	
		//Create Access Phases
		for (Module::iterator MI = M.begin();;++MI)
		{
			if(MI == M.end())
				break;
			//if (MI->isDeclaration())
			//	continue;
			if ((*MI).isIntrinsic() && (*MI).empty())
				continue;
			
			string funName = (*MI).getName().str();
			//Run only for upper most functions 
			//Others are processed recursively
			//if ((funName.find(TX_MARKING) != string::npos) && (funName.find(LOOP_MARKING) == string::npos) && (funName.find(CLONE_SUFFIX) == string::npos))
			if (JUSTINLINE)
			{
				if ((funName.find(TX_MARKING) != string::npos) && (funName.find(CLONE_SUFFIX) == string::npos))
				{
					Function *access = &*MI;
					Instruction * Inst = getFirstTMInst(*MI);
			
					//outs() << "MAIN function name : " << funName << "\n";
			
					Function *execute = cloneFunction(access);

            				//execute->removeFnAttr(Attribute::NoInline);
        				//execute->addFnAttr(Attribute::AlwaysInline);
            				access->removeFnAttr(Attribute::AlwaysInline);
        				access->addFnAttr(Attribute::NoInline);
					insertAccessExecute(access, execute, Inst);
				}
		
				//If it is TMFUNC_, change attribute to AlwaysInline	
				//But not if it is TXFUNC, because we need this function not to be inlined for 
				//the next pass to be able to recognise it. _
				if (((funName.find(TX_MARKING) == string::npos) && (funName.find(LOOP_MARKING) == string::npos)) && (funName.find(FUNCTION_MARKING) != string::npos))
				{
					if (funName.find(CLONE_SUFFIX) == string::npos)
					{
						//(&*MI)->removeFnAttr(Attribute::NoInline);
        					//(&*MI)->addFnAttr(Attribute::AlwaysInline);
					}
				}
        			(&*MI)->removeFnAttr(Attribute::AlwaysInline);
				(&*MI)->addFnAttr(Attribute::NoInline);
			}else if (SVFPREP)
			{
				//outs() << "SVFPREP\n";
				if ((funName.find(TX_MARKING) != string::npos) && (funName.find(CLONE_SUFFIX) == string::npos))
				{
					Function *access = &*MI;
					Instruction * Inst = getFirstTMInst(*MI);
        				Function *execute = cloneFunction(access);
					insertAccessExecute(access, execute, Inst);
            				access->removeFnAttr(Attribute::AlwaysInline);
        				access->addFnAttr(Attribute::NoInline);
					if(!createDUPLAPs(access))
					{
						outs() << "ERROR!!!!!!!!!!!!!!!!!!!!!!!!!!";
						return false;	
					}
				}
			}
		}
		return false;
		
		
	}else if (JUSTINLINE_BEFORE || SVFDESIGN)
	{
		wpa = new WPAPass();
		wpa->runOnModule(M);
		
		vector<Function*> vectorFunc;
		vector<std::set<Instruction *> > vectortoKeepLoads;
		vector<std::set<Instruction *> > vectortoKeepStores;
		vector<std::set<Instruction *> > vectortoKeepFunc;
		vector<std::set<Instruction *> > vectortoKeepTerminators;
		vector<std::set<Instruction *> > vectortoKeepReturns;
		vector<std::set<Function * > > vectorcalledFunctions;
		vector<std::list<LoadInst *> > vectortoPref;
		if (!DUPL)
		{
			for (Module::iterator MI = M.begin();;++MI)
			{
				if(MI == M.end())
					break;
				//if (MI->isDeclaration())
				//	continue;
				if ((*MI).isIntrinsic() && (*MI).empty())
					continue;
			
				string funName = (*MI).getName().str();
			
				//outs() << "1: " << funName << "\n";

				if (((funName.find(TX_MARKING) != string::npos) || (funName.find(LOOP_MARKING) != string::npos) || ((funName.find(FUNCTION_MARKING) != string::npos) && (funName.find(MAIN_FUNCTION_MARKING) == string::npos))) && (funName.find(CLONE_SUFFIX) == string::npos))
				{	
					//outs() << "2: " << funName << "\n";
					vectorFunc.push_back(&*MI);
					vectortoKeepLoads.push_back(std::set<Instruction*>());
					vectortoKeepStores.push_back(std::set<Instruction*>());
					vectortoKeepFunc.push_back(std::set<Instruction*>());
					vectortoKeepTerminators.push_back(std::set<Instruction*>());
					vectortoKeepReturns.push_back(std::set<Instruction*>());
					vectorcalledFunctions.push_back(std::set<Function*>());
					vectortoPref.push_back(std::list<LoadInst*>());
				}
			}

			//outs() << "We just try to survive\n";
			//Maybe I can create a list of called functions in advance
			//It is usefull for interprocedural analyses
			int iter = 0;
			for (Function * fun: vectorFunc)
			{
				for (Value::user_iterator i = fun->user_begin(), e = fun->user_end(); i != e; i++)
  				{
    					if (CallInst *I = dyn_cast<CallInst>(*i)) 
					{
						Function * F = I->getParent()->getParent();
						string funName = F->getName().str();
						if (((funName.find(TX_MARKING) != string::npos) || (funName.find(LOOP_MARKING) != string::npos) || ((funName.find(FUNCTION_MARKING) != string::npos) && (funName.find(MAIN_FUNCTION_MARKING) == string::npos))) && (funName.find(CLONE_SUFFIX) == string::npos))
						{
							int iter2 = 0;
							for (auto F2: vectorFunc)
							{
								if (F2 == F)
								{
									break;
								}
								iter2++;
							}
							vectorcalledFunctions[iter2].insert(fun);
							if (vectorFunc[iter2] == fun)
							{
								//RECURSION_MARKING
								StringRef Kind = "DAE-interproc-rec";
								StringRef Val =  "recursion-related";
								fun->addFnAttr(Kind, Val);
							}
						}
      		
					}
				}
				iter++;
			}
			//Figure which functions are inside loops
			//Should we do 2 iterations to avoid recursions?
			DAE_interproc_looprelated(vectorFunc, vectorcalledFunctions); 
						//outs() << "We just try to survive\n";

		}
	
		for (Module::iterator MI = M.begin();;++MI)
		{
			if(MI == M.end())
				break;
			//if (MI->isDeclaration())
			//	continue;
			if ((*MI).isIntrinsic() && (*MI).empty())
				continue;
			
			string funName = (*MI).getName().str();
			//Run only for upper most functions 
			//Others are processed recursively
			if ((funName.find(TX_MARKING) != string::npos) && (funName.find(CLONE_SUFFIX) == string::npos))
			//if (funName.find("exit716splitedB") != string::npos)
			{
				Function *access = &*MI;				
				if (!DUPL)
				{
					LoopInfo *LI = &getAnalysis<LoopInfoWrapperPass>(*MI).getLoopInfo();
        				BasicAAResult BAR(createLegacyPMBasicAAResult(*this, *MI));
        				AAResults AAR(createLegacyPMAAResults(*this, *MI, BAR));
        				AA = &AAR;
					TransferPassResults(AA, LI, this, wpa, true);//true stands for wpa_flag
					std::map<Function *, std::set<Instruction *>> *mapOfInstructionsToKeep;
					//mapOfInstructionsToKeep->insert(std::pair<Function*, std::set<Instruction*>>(access, toKeep));
					//(*mapOfInstructionsToKeep)[access] = toKeep;
					TransferPassAttributes(AllocaNotAllowed, Oracle, MUSTMAYPART, TAP, INLINEINNER, DUPL, NOREMOVE, NODELETEUNUSED, SVFDESIGN, INTERPROC, vectorFunc, vectortoKeepLoads, vectortoKeepFunc, vectortoKeepTerminators, vectortoKeepReturns, vectortoKeepStores, vectortoPref, vectorcalledFunctions, FilterFP);
				
					list<LoadInst *> toPref;   // LoadInsts to prefetch
       					set<Instruction *> toKeep; // Instructions to keep
					int num = 0;
					for (auto inst = inst_begin(access); inst != inst_end(access); inst++)
					{	
						num++;
					}
					outs() << "##########################################################################\n";
					outs() << "BEFORE: Number of static instructions inside " << funName << " is " << num<< "\n";
					outs() << "##########################################################################\n";
					bool res = findAccessInsts(*access, toKeep, toPref, true, NULL);
					if (res) {
          					// insert prefetches
	  					outs() << "Helper Processed function1 " << access->getName().str() << "\n";
	  					if (!NOREMOVE && !INTERPROC)
						{
          						int prefs = insertPrefetches(toPref, toKeep, true);
							removeUnlisted(*access, toKeep);
						}
						num = 0;
						for (auto inst = inst_begin(access); inst != inst_end(access); inst++)
						{	
							num++;
						}
						outs() << "##########################################################################\n";
						outs() << "AFTER: Number of static instructions inside " << funName << " is " << num<< "\n";
						outs() << "##########################################################################\n";

            					// - No inlining of the A phase.
            					//access->removeFnAttr(Attribute::NoInline);
        					//access->addFnAttr(Attribute::AlwaysInline);
            					//access->removeFnAttr(Attribute::AlwaysInline);
            					//access->addFnAttr(Attribute::NoInline);
						access->setName(Twine(ACCESS_MARKING + access->getName().str()));
						//deleteEmptyAccessPhase(access);

					}else if (toKeep.size() == 0)
					{
						deleteAccessPhase(access);
	  					continue;
					}
				}else
				{
            				access->removeFnAttr(Attribute::NoInline);
        				access->addFnAttr(Attribute::AlwaysInline);
					access->setName(Twine(ACCESS_MARKING + access->getName().str()));
				}
				if (!INTERPROC || DUPL)
				{
					if (!TAP)
					{
						insertCompilerMarkers(access);
					}else
					{
						insertCompilerMarkers_TAP(access);
					}
					outs() << "DUPL AP: " << access->getName().str() << "\n";
					int load_inst = 0;
					int store_inst = 0;
					int pref_inst = 0;
					vector<Function* > array_of_func;
					array_of_func.push_back(access);
					count_LOADS_STORES_PREF(array_of_func, access, &load_inst, &store_inst, &pref_inst, true);
					/*for(inst_iterator inst = inst_begin(access); inst != inst_end(access); inst++)
					{
						if (isa<LoadInst>(&*inst))
						{
							load_inst++;	
						}
						if (isa<StoreInst>(&*inst))
						{
							store_inst++;	
						}
					}*/
					outs() << "LOAD: " << load_inst << " STORE: " << store_inst << "\n";
				}
				
				//This AP is ready to be cut off
				/*if (DUPL && HALFTM)
				{
					//The first step is to count instuctions
					//Loop functions are not inlined at this point
					//So we can safely cut an AP, loops in the remaining space will be preserved
					int inst_num = 0;
					int goal = 0;
					for(inst_iterator inst = inst_begin(access); inst != inst_end(access); inst++)
					{
						inst_num++;
					}
					if ((RTS != 0) && (inst_num > RTS))
					{
						outs() << "RTS is " << RTS << " and inst_num is " << inst_num << "\n";
					}
					if (TSP != 0)
					{
						outs() << "TSP is " << TSP << " and inst_num is " << inst_num << "\n";
						goal = inst_num * TSP; 	
					}
					if (goal != 0)
					{
						RipAP(access, inst_num, goal);
					}
					inst_num = 0;
					for(inst_iterator inst = inst_begin(access); inst != inst_end(access); inst++)
					{
						inst_num++;
					}
					outs() << "inst_num after ripping off is " << inst_num << "\n";
				}*/

			}
		}
		//outs() << "LAST PART START\n";
		// When we finished collecting all required instructions 
		// We can start deleting them now
		if (INTERPROC && !DUPL)
		{
			int iter = 0;
			//outs() << "IPINFO Sizes are : \n";
			vector<Function* > Seen;
			//checkIfFuncEmpty(vectorcalledFunctions, vectorFunc, vectortoKeepLoads, vectortoKeepStores, vectortoPref, Seen);
			/*Seen.clear();
			int num_return_func;
			int delta = 1;
			while(delta != 0)
			{
				num_return_func = 0;
				iter = 0;
				for (Function *f: vectorFunc)
				{
					if ((f->getName().str().find("_RETURN") != string::npos))
					{
						outs() << "RETURNPROBLEM: Function is " << f->getName().str() << "\n";
					if (std::find(Seen.begin(), Seen.end(), f) == Seen.end())
					{
						Seen.push_back(f);
						num_return_func++;
						getControlDepsPreliminary(*f, vectortoKeepReturns[iter]);
						set<Instruction *> toKeepReturns;
						set<Instruction *> DepsReturns;
						findReturns(*f, toKeepReturns);
						if (toKeepReturns.size() > 0)
						{
							int res = true;
							LoopInfo *LI = &getAnalysis<LoopInfoWrapperPass>(*f).getLoopInfo();
        						BasicAAResult BAR(createLegacyPMBasicAAResult(*this, *f));
        						AAResults AAR(createLegacyPMAAResults(*this, *f, BAR));
        						AA = &AAR;
							TransferPassResults(AA, LI, this, wpa, true);//true stands for wpa_flag
							res = followDeps(toKeepReturns, DepsReturns);
							if (!res)
							{
								outs() << "ERROR: no return instructions\n";
							}
						}else
						{
							outs() << "ERROR: no return instructions\n";
						}
						//vectortoKeepReturns[iter].insert(toKeepReturns.begin(), toKeepReturns.end());
						//vectortoKeepReturns[iter].insert(DepsReturns.begin(), DepsReturns.end());
					}
					}
					iter++;

				}
				delta = 0;
				for (Function *f: vectorFunc)
				{
					if ((f->getName().str().find("_RETURN") != string::npos))
					{
						delta++;
					}
			
				}
				delta = delta - num_return_func;
			}*/
			iter = 0;
			for (Function *f: vectorFunc)
			{
				string funName = f->getName().str();
				if (f->getReturnType()->isVoidTy())
				{
					//outs() << "SDDESIGN void: " << f->getName().str() << " toKeepLoads is " << vectortoKeepLoads[iter].size() << " toKeepFunc is " << vectortoKeepFunc[iter].size() << " toKeepTerminators is " << vectortoKeepTerminators[iter].size() << " toPref " << vectortoPref[iter].size() << " toKeepStores " << vectortoKeepStores[iter].size()<< " \n";
				}else
				{
					//outs() << "IPINFO: " << f->getName().str() << " toKeepLoads is " << vectortoKeepLoads[iter].size() << " toKeepFunc is " << vectortoKeepFunc[iter].size() << " toKeepTerminators is " << vectortoKeepTerminators[iter].size() << " toPref " << vectortoPref[iter].size() << " toKeepStores " << vectortoKeepStores[iter].size() << "\n";
					/*if ((funName.find("_RETURN") == string::npos) && (funName.find("LOOP_MARKING") == string::npos) && (funName.find(ACCESS_MARKING) != string::npos))
					{
						//check if parent returns
						vector<Function * > seen;
						if (!IfFuncReturns(f, vectorcalledFunctions, vectorFunc, seen))
						{
							getControlDepsPreliminary(*f, vectortoKeepFunc[iter]);
							outs() << "SDDESIGN: got control deps\n";	
							if (!deleteUnusedBranches(f, true))
							{
								outs() << "SDDESIGN: fail \n";	
							}else
							{
								vectortoKeepReturns[iter].clear();
								findReturns(*f, vectortoKeepReturns[iter]);
							}
						}
					}*/
				}
				#ifdef DEBUGE
				for (Instruction *I: vectortoKeepReturns[iter])
				{
					outs() << "IPINFO Instruction is " << *I << "\n";
				}
				#endif
				#ifdef DEBUGE
				for (Instruction *I: vectortoKeepStores[iter])
				{
					if (isa<StoreInst>(I))
					{
						outs() << "IPINFO Instruction is " << *I << "\n";
					}
				}
				#endif
				//outs() << "Loads\n";
				//refineUnique(vectortoKeepLoads[iter], vectortoPref[iter]);
				//outs() << "Stores\n";
				//refineUnique(vectortoKeepStores[iter], vectortoPref[iter]);
				//outs() << "Returns\n";
				//refineUnique(vectortoKeepReturns[iter], vectortoPref[iter]);
				//outs() << "Func\n";
				//refineUnique(vectortoKeepFunc[iter], vectortoPref[iter]);
				//outs() << "Terminators\n";
				//refineUnique(vectortoKeepTerminators[iter], vectortoPref[iter]);
				
				std::set<Instruction *> vectortoKeep;
				vectortoKeep.insert(vectortoKeepLoads[iter].begin(), vectortoKeepLoads[iter].end());
				vectortoKeep.insert(vectortoKeepStores[iter].begin(), vectortoKeepStores[iter].end());
				vectortoKeep.insert(vectortoKeepReturns[iter].begin(), vectortoKeepReturns[iter].end());
				vectortoKeep.insert(vectortoKeepFunc[iter].begin(), vectortoKeepFunc[iter].end());
				vectortoKeep.insert(vectortoKeepTerminators[iter].begin(), vectortoKeepTerminators[iter].end());
          			int prefs = insertPrefetches(vectortoPref[iter], vectortoKeep, true);
				//Because if there is no even single return
				//probably that function is not called inside TX
				//outs() << "BEFORE REMOVING UNLISTED\n";
				if (vectortoKeep.size() != 0 && funName.find(ACCESS_MARKING) != string::npos)
				{
					//if (funName.find("_LOOPFUNC_TMmesh_insert") == string::npos)
					//{
					//	if (funName.find("_LOOPFUNC_jsw_avlfind_") == string::npos)
					//	{
					//	if (funName.find("_LOOPFUNC_TMretriangulate_") == string::npos)
					//	{
						removeUnlisted(*f, vectortoKeep);
					//	}}
					//}
				}
				//outs() << "AFTER REMOVING UNLISTED\n";
				if ((funName.find(TX_MARKING) != string::npos) && (funName.find(CLONE_SUFFIX) == string::npos))
				{	
					if (!TAP)
					{
						insertCompilerMarkers(f);
					}else
					{
						//if (funName.find("exit107splitedB") == string::npos)
						//{
							insertCompilerMarkers_TAP(f);
						//}
					}
				}
				//outs() << "AFTER INSERTING MARKERS\n";
				iter++;
			}	
			for (Function *f: vectorFunc)
			{
				//DeleteFnAttr(f);
				//Let's delete all attributes that we added
				outs() << "Remove Redundant Pref: start\n";
				RRP = new RemoveRedundantPref();
				//assert(f->getEntryBlock().getTerminator()->getNumSuccessors() == 1 && "We assume that the loop header should be the only successor");
				//BasicBlock* LoopHeader = f->getEntryBlock().getTerminator()->getSuccessor(0);
				//SplitBlock(LoopHeader, LoopHeader->getFirstNonPHI());
				RRP->runOnFunction(*f);
				outs() << "Remove Redundant Pref: end\n";
				string funName = f->getName().str();
				if ((funName.find(TX_MARKING) != string::npos) && (funName.find(CLONE_SUFFIX) == string::npos))
				{	
					outs() << "AP: " << funName << "\n";
					int load_inst = 0;
					int store_inst = 0;
					int pref_inst = 0;
					vector<Function* > array_of_func;
					array_of_func.push_back(f);
					if (!Oracle)
					{
						count_LOADS_STORES_PREF(array_of_func, f, &load_inst, &store_inst, &pref_inst, false);
            					f->removeFnAttr(Attribute::NoInline);
        					f->addFnAttr(Attribute::AlwaysInline);
        					//f->removeFnAttr(Attribute::AlwaysInline);
            					//f->addFnAttr(Attribute::NoInline);
            					outs() << "Wow\n";
						TargetTransformInfo &TTI = getAnalysis<TargetTransformInfoWrapperPass>().getTTI(*f);
						outs() << "Cul\n";
						simplifyCFG(f, TTI);
						//outs() << "LOAD: " << load_inst << " STORE: " << store_inst << " PREF: " << pref_inst << "\n";
					}else
					{
            					f->removeFnAttr(Attribute::NoInline);
        					f->addFnAttr(Attribute::AlwaysInline);
        					//f->removeFnAttr(Attribute::AlwaysInline);
            					//f->addFnAttr(Attribute::NoInline);
            					outs() << "Wow\n";
						TargetTransformInfo &TTI = getAnalysis<TargetTransformInfoWrapperPass>().getTTI(*f);
						outs() << "Cul\n";
						simplifyCFG(f, TTI);
					}
				}else if (funName.find(CLONE_SUFFIX) == string::npos)
				{
					outs() << "AP: " << funName << "\n";
			
            				f->removeFnAttr(Attribute::NoInline);
        				f->addFnAttr(Attribute::AlwaysInline);
        				//f->removeFnAttr(Attribute::AlwaysInline);
            				//f->addFnAttr(Attribute::NoInline);
            				outs() << "Wow\n";
					TargetTransformInfo &TTI = getAnalysis<TargetTransformInfoWrapperPass>().getTTI(*f);
					outs() << "Cul\n";
					simplifyCFG(f, TTI);
				}

				
			}
		}
		//outs() << "LAST PART END!\n";
	}
	else
	{
	//This part is for original TM_DAE pass
	//Some functionality is the same as for other parts,
	//because i did not want to introduce more flags
	//if no flags are provided,
	//this part will be executed

	for (Module::iterator MI = M.begin();;++MI)
	{
		//if (MI->isDeclaration())
		//	continue;
		if(MI == M.end())
			break;
		if ((*MI).isIntrinsic() || (*MI).empty())
			continue;
		//Fill LoopInfo for identifying targeted loops
		llvm::DominatorTree DTI = llvm::DominatorTree();
		DTI.recalculate(*MI);
		LoopInfoBase<BasicBlock, Loop> * KLoop = new LoopInfoBase<BasicBlock, Loop>();
		KLoop->releaseMemory();
		KLoop->analyze(DTI);
		LIBV.clear();
		LIBV.push_back(KLoop);
		MarkEverything(*MI, true);
		if (TXBBs.size() == FirstInstV.size())
		{
			for (size_t i =0; i < TXBBs.size(); ++i)
			{
				//outs() << "Extractor preparetion\n";
				CodeExtractor Extractor(TXBBs[i],&DTI);
				Function *nF = Extractor.extractCodeRegion();
				if (nF != 0)
				{
					nF->addFnAttr(Attribute::AlwaysInline);
					nF->setName(Twine(TX_MARKING + nF->getName().str()));
					TMtoInstMap.push_back(std::make_pair(nF, FirstInstV[i]));
					//outs() << "Extracted" << nF->getName().str()<<"\n";
				}
			}
		}
		FirstInstV.clear();
		TXBB.clear();
		TXBBs.clear();
	}
	//2. Atempt to extract loops
	//right now loop(loop(loop())) --> fun(fun(fun()))
	//Only TMfixAfterInsertion function, I could not solve the problem that occurs within it
	/*for (Module::iterator MI = M.begin();;MI++)
	{
		if (MI->isDeclaration())
			continue;
		if(MI == M.end())
			break;
		if ((*MI).isIntrinsic() && (*MI).empty())
			continue;
		//If function is marked then it is a part of TM
		bool isMarked = ((*MI).getName().str().find(FUNCTION_MARKING) != string::npos); 
		//isMarked = ((*MI).getName().str().find("rbtree_verify") != string::npos); 
		//if (isMarked && (*MI).getName().str().find("TMfixAfterInsertion") == string::npos)
		if (isMarked)
		//if (isMarked)
		{
			llvm::DominatorTree DTI = llvm::DominatorTree();
			DTI.recalculate(*MI);
			LoopInfo * LI = &getAnalysis<LoopInfoWrapperPass>(*MI).getLoopInfo();
			for (LoopInfo::iterator it = LI->begin();;)
			{
				if (it == LI->end())
					break;
				Loop* loop = *it;
				//First condition is nesseccary because it points out targeted loop
				//Second condition is to avoid infinity loops: means that if this loop has been extracted, it was out into new function
				//So if this function found, don't do anything with it, everything has been done
				bool isLoopMarked = (loop->getHeader()->getName().str().find(KERNEL_MARKING) != string::npos)&& (loop->getHeader()->getParent()->getName().str().find(KERNEL_MARKING) == string::npos);
				if (isLoopMarked)
				{
					ExtractLoop(loop, &DTI, LI);
					DTI.recalculate(*MI);
					//outs() << "Loop goes to extracting" << loop->getHeader()->getName()<<"\n";
				}
				
				ExtractSubLoops(loop, &DTI, LI);
				DTI.recalculate(*MI);
				++it;

			}

			
		}
	}*/
	//4. Applying DAE
	//3.1 If function then DAE should be applied: create access phase and execute phase
	//if function contains function call inside, function call should be replaced with a call of an access phase
	//stores to global memory are not allowded as it was before
	//3.2 Parsing dependencies
	//
		
	if (!AccessNotAllowed)
	{
	//Annotate exit branches  in loops
	for (Module::iterator MI = M.begin();MI != M.end();++MI)
	{
		//if (MI->isDeclaration())
		//	continue;
		if ((*MI).isIntrinsic() || (*MI).empty())
			continue;
		string funName = (*MI).getName().str();
		if ((funName.find(TX_MARKING) != string::npos) || (funName.find(LOOP_MARKING) != string::npos))
		{
			LoopInfo * LI = &getAnalysis<LoopInfoWrapperPass>(*MI).getLoopInfo();
			for (LoopInfo::iterator it = LI->begin(); it !=LI->end(); ++it)
			{
				Loop* loop = *it;
				AnnotateBranchesLoop(loop);	
			}
		}
	}
	bool wpa_flag = false;
	/*if (SVFDESIGN)
	{
		wpa = new WPAPass();
		wpa->runOnModule(M);
		wpa_flag = true;

		for (Module::iterator MI = M.begin();MI != M.end();++MI)
		{
			//if (MI->isDeclaration())
			//	continue;
			if ((*MI).isIntrinsic() || (*MI).empty())
				continue;
			string funName = (*MI).getName().str();
			//Run only for upper most functions 
			//Others are processed recursively
			if ((funName.find(TX_MARKING) != string::npos) && (funName.find(LOOP_MARKING) == string::npos) && (funName.find(CLONE_SUFFIX) == string::npos))
			{
				Function *access = &*MI;
			
				LoopInfo *LI = &getAnalysis<LoopInfoWrapperPass>(*MI).getLoopInfo();
        			BasicAAResult BAR(createLegacyPMBasicAAResult(*this, *MI));
        			AAResults AAR(createLegacyPMAAResults(*this, *MI, BAR));
        			AA = &AAR;
				TransferPassResults(AA, LI, this, wpa, wpa_flag);
				outs() << "TAP is " << TAP;
				std::map<Function*, std::set<Instruction *>> *mapOfInstructionsToKeep;
				TransferPassAttributes(AllocaNotAllowed, Oracle, MUSTMAYPART, TAP, INLINEINNER, DUPL, NOREMOVE, NODELETEUNUSED, SVFDESIGN, INTERPROC,  mapOfInstructionsToKeep);

				if (!DUPL)
				{
					list<LoadInst *> toPref;   // LoadInsts to prefetch
       					set<Instruction *> toKeep; // Instructions to keep
					bool res = findAccessInsts(*access, toKeep, toPref, true);
					if (mapOfInstructionsToKeep->size() != 0)
					{
						outs() << "Success!\n";
					}
					if (res) {
          					// insert prefetches
	  					//outs() << "Helper Processed function1 " << access->getName().str() << "\n";
	  					if (!NOREMOVE)
						{
          						int prefs = insertPrefetches(toPref, toKeep, true);
							removeUnlisted(*access, toKeep);
						}

            					// - No inlining of the A phase.
            					access->removeFnAttr(Attribute::NoInline);
        					access->addFnAttr(Attribute::AlwaysInline);
            					//access->removeFnAttr(Attribute::AlwaysInline);
            					//access->addFnAttr(Attribute::NoInline);
						access->setName(Twine(ACCESS_MARKING + access->getName().str()));
						//deleteEmptyAccessPhase(access);

					}else if (toKeep.size() == 0)
					{
						deleteAccessPhase(access);
	  					continue;
					}
				}
				if (!TAP)
				{
					insertCompilerMarkers(access);
				}else
				{
					insertCompilerMarkers_TAP(access);
				}

			}
		}
		//Recursion left overs
		outs() << "RECURSION LEFT OVERS\n";
		//FIXME: was commented
		for (Module::iterator MI = M.begin();MI != M.end();++MI)
		{
			//if (MI->isDeclaration())
			//	continue;
			if ((*MI).isIntrinsic() || (*MI).empty())
				continue;
			string funName = (*MI).getName().str();
			//Run only for upper most functions 
			//Others are processed recursively
			if ((funName.find(TX_MARKING) == string::npos) && (funName.find(LOOP_MARKING) == string::npos) && (funName.find(CLONE_SUFFIX) == string::npos) && (funName.find(ACCESS_MARKING) == string::npos) && (funName.find(FUNCTION_MARKING) != string::npos) && (funName.find(RECURSION_MARKING) != string::npos))
			{
				Function *access = &*MI;
				LoopInfo *LI = &getAnalysis<LoopInfoWrapperPass>(*MI).getLoopInfo();
        			BasicAAResult BAR(createLegacyPMBasicAAResult(*this, *MI));
        			AAResults AAR(createLegacyPMAAResults(*this, *MI, BAR));
        			AA = &AAR;
				TransferPassResults(AA, LI, this, wpa, wpa_flag, &M, SVFDESIGN);
				TransferPassAttributes(AllocaNotAllowed, Oracle, MUSTMAYPART, TAP, INLINEINNER, DUPL, NOREMOVE, NODELETEUNUSED);

				if (!DUPL)
				{
					list<LoadInst *> toPref;   // LoadInsts to prefetch
       					set<Instruction *> toKeep; // Instructions to keep
					bool res = findAccessInsts(*access, toKeep, toPref, true);
					if (res) {
          					// insert prefetches
	  					//outs() << "Helper Processed function1 " << access->getName().str() << "\n";
	  					if (!NOREMOVE)
						{
          						int prefs = insertPrefetches(toPref, toKeep, true);
							removeUnlisted(*access, toKeep);
						}

            					// - No inlining of the A phase.
            					access->removeFnAttr(Attribute::NoInline);
        					access->addFnAttr(Attribute::AlwaysInline);
            					//access->removeFnAttr(Attribute::AlwaysInline);
            					//access->addFnAttr(Attribute::NoInline);
						access->setName(Twine(ACCESS_MARKING + access->getName().str()));
						//deleteEmptyAccessPhase(access);

					}else if (toKeep.size() == 0)
					{
						deleteAccessPhase(access);
	  					continue;
					}
				}
			}
		}
		//FIXME: till here
	}else */
	{
	
	for (Module::iterator MI = M.begin();MI != M.end();++MI)
	{
		//if (MI->isDeclaration())
		//	continue;
		if ((*MI).isIntrinsic() || (*MI).empty())
			continue;
		string funName = (*MI).getName().str();
		//Run only for upper most functions 
		//Others are processed recursively
		if ((funName.find(TX_MARKING) != string::npos) && (funName.find(LOOP_MARKING) == string::npos) && (funName.find(CLONE_SUFFIX) == string::npos))
		//if (((funName.find(FUNCTION_MARKING) != string::npos) || (funName.find(KERNEL_MARKING) != string::npos)) && (funName.find(CLONE_SUFFIX) == string::npos))
		{
			Function *access = &*MI;
			Instruction * Inst = getFirstTMInst(*MI);
			
			outs() << "MAIN function name : " << funName << "\n";
			
			LoopInfo *LI = &getAnalysis<LoopInfoWrapperPass>(*MI).getLoopInfo();
        		BasicAAResult BAR(createLegacyPMBasicAAResult(*this, *MI));
        		AAResults AAR(createLegacyPMAAResults(*this, *MI, BAR));
        		AA = &AAR;
			TransferPassResults(AA, LI, this, wpa, wpa_flag);
			outs() << "TAP is " << TAP;
			std::map<Function*, std::set<Instruction *>>* mapOfInstructionsToKeep;
			//TransferPassAttributes(AllocaNotAllowed, Oracle, MUSTMAYPART, TAP, INLINEINNER, DUPL, NOREMOVE, NODELETEUNUSED, SVFDESIGN, INTERPROC, mapOfInstructionsToKeep);
        		Function *execute = cloneFunction(access);

			//It is for merging branches from clayirvoynce 
			//
			//minimizeFunctionFromBranchPred(access);
            		execute->removeFnAttr(Attribute::NoInline);
        		execute->addFnAttr(Attribute::AlwaysInline);
			//it is important to insert it before findAccessInsts function
			//Inst = insertCheckDeps(access, Inst);
			insertAccessExecute(access, execute, Inst);
			
			if (!DUPL)
			{
				list<LoadInst *> toPref;   // LoadInsts to prefetch
       				set<Instruction *> toKeep; // Instructions to keep
				bool res = findAccessInsts(*access, toKeep, toPref, true, NULL);
				if (res) {
          				// insert prefetches
	  				//outs() << "Helper Processed function1 " << access->getName().str() << "\n";
	  				if (!NOREMOVE)
					{
          					int prefs = insertPrefetches(toPref, toKeep, true);
						removeUnlisted(*access, toKeep);
					}

            				// - No inlining of the A phase.
            				access->removeFnAttr(Attribute::NoInline);
        				access->addFnAttr(Attribute::AlwaysInline);
            				//access->removeFnAttr(Attribute::AlwaysInline);
            				//access->addFnAttr(Attribute::NoInline);
					access->setName(Twine(ACCESS_MARKING + access->getName().str()));
					//deleteEmptyAccessPhase(access);

				}else if (toKeep.size() == 0)
				{
					deleteAccessPhase(access);
	  				continue;
				}
			}
			//Adding fake call for simulator
			//In case it is not a transactional access phase
			//we just insert void DAE_beginAccessPhase
			//in the beginning of an access phase
			//to notify a simulator about a point to start count from
			else
			{
				// - No inlining of the A phase.
            			access->removeFnAttr(Attribute::NoInline);
        			access->addFnAttr(Attribute::AlwaysInline);
            			//access->removeFnAttr(Attribute::AlwaysInline);
            			//access->addFnAttr(Attribute::NoInline);
				access->setName(Twine(ACCESS_MARKING + access->getName().str()));
			}
			if (!TAP)
			{
				insertCompilerMarkers(access);
			}else
			{
				insertCompilerMarkers_TAP(access);
			}
				
        	}
	}
	}
	}
	}
	//4. Delete redundant memory bariers
	for (Module::iterator MI = M.begin();MI != M.end();++MI)
	{
		//if (MI->isDeclaration())
		//	continue;
		if ((*MI).isIntrinsic() && (*MI).empty())
			continue;
	
		string funName = (*MI).getName().str();
		//beginTransaction should not be deleted, right?
		if ((funName.find("InnerPartBegin") != string::npos) || (funName.find("InnerPartEnd") != string::npos) || (funName.find("fakeCallBegin") != string::npos) || (funName.find("fakeCallEnd") != string::npos))
		{
			//Basically called function deletes function
			//it was used for deleting access phases, that is why it has so wierd name.
			//TODO: rename?
			//We need to delete listed functions because they contain memory barriers
			outs() << "Function " << funName << " was deleted\n";
			//deleteAccessPhase(&*MI)
			//(*MI).removeFnAttr(Attribute::OptNone);
        		//(*MI).addFnAttr(Attribute::AlwaysInline);
;
			makeHelperFuncEmpty(&*MI);
		}
	}
		

	/*outs() << "Total number of loads                : " << TotalNUMLoads << "\n";
	outs() << "Total number of prefetched loads     : " << TotalNUMPrefetchedLoads << "\n";
	outs() << "Total number of prefetched loads TMARg     : " << TotalNUMPrefetchedLoadsTMDAE << "\n";
	outs() << "Total number of Loads inside loops   : " << TotalNUMLoadsInsideLoops << "\n";
	outs() << "Total number of Loads depend on loads: " << TotalNUMLoadsDependOnLoads << "\n";
	outs() << "Total number of TX inside Loops      : " << TotalNUMTXInsideLoops << "\n";
	outs() << "Total number of TX                   : " << TotalNUMTX << "\n";
	outs() << "Total number of function's calls     : " << TotalNUMFunctionCalls << "\n";*/
	return false;
}
void TM_DAE_INTGR_pass::count_LOADS_STORES_PREF(vector<Function* > &funcARR, Function * func, int *load_inst, int *store_inst, int *pref_inst, bool DUPL)
{
	outs() << "FUNC NAME in proc: " << func->getName().str() << "\n";
	for(inst_iterator inst = inst_begin(*func); inst != inst_end(*func); inst++)
	{
		if (isa<LoadInst>(&*inst))
		{
			outs() << "load: " << *inst << "\n";
			(*load_inst)++;	
		}
		if (isa<StoreInst>(&*inst))
		{
			(*store_inst)++;	
		}
		if (CallInst * CI = dyn_cast<CallInst>(&*inst))
		{
			if (CI->getCalledFunction() != NULL)
			{
			if (CI->getCalledFunction()->isIntrinsic())
			{
				//outs() << "I'm an intrinsic\n";
				Function *Ifunc = cast<CallInst>(&*inst)->getCalledFunction();
				if (getName(Ifunc->getIntrinsicID()).find("prefetch") != string::npos)
				{
					outs() << "prefetch: " << *inst << "\n";
					(*pref_inst)++;	
				}
			}else if ((DUPL && (CI->getCalledFunction()->getName().str().find(FUNCTION_MARKING) != string::npos)) || (CI->getCalledFunction()->getName().str().find(ACCESS_MARKING) != string::npos) || (CI->getCalledFunction()->getName().str().find(LOOP_MARKING) != string::npos))
			{
				//outs() << "Processed\n";
				Function *Cfunc = cast<CallInst>(&*inst)->getCalledFunction();
				bool skip = false;
				for (auto f: funcARR)
				{
					if (Cfunc == f)
					{
						//It means that we already went through this function
						skip = true;
						//outs() << "skip\n";
						break;
					}
				}
				if (!skip)
				{
					//outs() << " do not skip\n";
					(&funcARR)->push_back(Cfunc);
					count_LOADS_STORES_PREF(funcARR, CI->getCalledFunction(), load_inst, store_inst, pref_inst, DUPL);
				}
			}
			}
							
		}
	}
}

void TM_DAE_INTGR_pass::insertCompilerMarkers_TAP(Function * access)
{	
	Module *Mod = access->getParent();
					
	//Time to insert DAE_endAccessPhase
	//we do it before every return
	Instruction * inst;
	FunctionType *FTy = FunctionType::get(llvm::Type::getVoidTy(Mod->getContext()), 0);
	IRBuilder<> builder(&*(access->begin()));
	Function* marker_func;
	for (auto I = inst_begin(access); I != inst_end(access); ++I)
	{
		if (isa<ReturnInst>(&*I))
		{
			inst = &*I;
			builder.SetInsertPoint(inst);
			Constant *c = Mod->getOrInsertFunction("DAE_endAccessPhase", FTy);
			marker_func = cast<Function>(c);
			marker_func->setCallingConv(CallingConv::C);
			builder.CreateCall(marker_func);
		}
	}
	Function *function = Mod->getFunction("DAE_beginAccessPhase");
	if (!function)
	{
		outs() << "Error: can not find DAE_beginAccessPhase function\n";
	}	
	ConstantInt * Zero = builder.getInt64(0);
					/*FTy = FunctionType::get(llvm::Type::getInt32Ty(Mod->getContext()), 32);
					Constant *c = M.getOrInsertFunction("DAE_beginAccessPhase", FTy);
					marker_func = cast<Function>(c);*/
				
					// split the first block right away
					// to form an if statement	
	BasicBlock &curBB = *(access->begin());
	Instruction &Inst = *(curBB.begin());
	curBB.splitBasicBlock(&Inst);
						
	BasicBlock * ret = BasicBlock::Create(Mod->getContext(), "return", access);
	builder.SetInsertPoint(ret);
	if (access->getReturnType()->isVoidTy())
	{
		builder.CreateRetVoid();
	}else
	{
		Value *val = Constant::getNullValue(access->getReturnType());
		builder.CreateRet(val);
	}
	builder.SetInsertPoint(&*(access->begin())->getTerminator());
	Value * ret_value = builder.CreateCall(function, Zero);
	Value * One = ConstantInt::get(llvm::Type::getInt32Ty(Mod->getContext()), 1);
	Value * xEqualY = builder.CreateICmpEQ(ret_value, One, "tmp");
	builder.CreateCondBr(xEqualY, &*(++(access->begin())), ret);
	&*(access->begin())->getTerminator()->eraseFromParent();


}

void TM_DAE_INTGR_pass::insertCompilerMarkers(Function * access)
{
	Module *Mod = access->getParent();
	FunctionType *FTy = FunctionType::get(llvm::Type::getVoidTy(Mod->getContext()), 0);
	Constant *c = Mod->getOrInsertFunction("DAE_beginAccessPhase", FTy);
	Function *marker_func = cast<Function>(c);
	marker_func->setCallingConv(CallingConv::C);
	Instruction * inst;
	for (auto I = inst_begin(access); I != inst_end(access); ++I)
	{
		if (!isa<PHINode>(&*I))
		{
			inst = &*I;
			break;
		}
	}
	IRBuilder<> builder(inst);
	builder.CreateCall(marker_func);

}
void TM_DAE_INTGR_pass::deleteEmptyAccessPhase(Function * access)
{
	//Empty means that Access phase does not contain prefetches or calls of other Access phases.
	bool delete_access = true;
	for (auto I = inst_begin(access); I != inst_end(access); ++I)
	{
		if (!isa<TerminatorInst>(*I))
		{
			delete_access = false;
			break;
		}
	}
	if (delete_access)
	{
		deleteAccessPhase(access);
	}
	return;
}

//TODO: make this function general 
Instruction * TM_DAE_INTGR_pass::insertCheckDeps(Function *F, Instruction * Inst)
{
	//outs() << "Instruction "<< *(Inst->getParent()->getTerminator()) << "\n";
	std::vector<Instruction *> Inst_retV;
	llvm::DominatorTree DTT = llvm::DominatorTree();
	DTT.recalculate(*(Inst->getParent()->getParent()));

	for(Value::user_iterator I = F->user_begin(), E = F->user_end(); I != E; ++I)
	{
		//It should be the only user 
		if (CallInst *CI = dyn_cast<CallInst>(*I))
		{
			for (unsigned i = 0; i < CI->getNumOperands(); ++i)
			{
				Value *val = CI->getArgOperand(i);
				if (Instruction *inst = dyn_cast<Instruction>(val))
				{	if (!isa<PHINode>(inst))
					{
						if (Inst->getParent() == inst->getParent())
						{
							Inst_retV.push_back(Inst->getParent()->getTerminator());
						}else

						//Check that it does not belong to a TM region
						if (DTT.dominates(Inst, inst))
						{
							//outs() << "\n\n\nHERE\n\n\n\n\n";
							//TODO: to check lower instruction
							Inst_retV.push_back(inst);
						}else
						{
							//outs() << "\n\n\nB4\n\n\n\n\n" << *inst << "\n";

						}
					}else
					{
						//TODO; make it general
						BasicBlock * BB = inst->getParent();
						const TerminatorInst *TInst = BB->getTerminator();
						for(unsigned I = 0, NSucc = TInst->getNumSuccessors(); I < NSucc; ++I)
						{
							BasicBlock * Succ = TInst->getSuccessor(i);
							if (DTT.dominates(Inst, Succ))
							{
								Inst_retV.push_back(inst);
								break;
							}
							
						}
						
					}
				}
			}


		}
	}
	//TODO: to add a check that it is still before TM starts
	if (Inst_retV.size() == 0)
	{
		return Inst;
	}else if (Inst_retV.size() == 1)
	{
		return Inst_retV[0]->getParent()->getTerminator();
	}else
	{
		Instruction * temp = Inst_retV[0];
		for (unsigned i = 1; i < Inst_retV.size(); i++)
		{
			if (temp->getParent() == Inst_retV[i]->getParent())
			{
				temp = temp->getParent()->getTerminator();
			}else
			if (DTT.dominates(temp, Inst_retV[i]) )
			{
				temp = Inst_retV[i];
			}else if (!DTT.dominates(Inst_retV[i], temp))
			{
				//TODO: to find the a block that both instruction dominate
				//outs() << "\n\nIt is a case\n\n" << *temp <<"\n" << *(Inst_retV[i]) << "\n";
			}
		}
		return temp;
	}
}

/*Instruction * TM_DAE_INTGR_pass::followAccessDeps(Instruction *inst, Instruction *Inst)
{
	BasicBlock * BB = Inst->getParent();
	const TerminatorInst *TInst = BB->getTerminator();
	UsedBBs.clear();
	for(unsigned I = 0, NSucc = TInst->getNumSuccessors(); I < NSucc; ++I)
	{
		BasicBlock * Succ = &*I;
		if (printTxRegionInst(*Succ, inst)
		{
			return inst;
		}	
	}
	return nullptr;
}*/

Instruction * TM_DAE_INTGR_pass::getFirstTMInst(Function &F)
{
	for (auto &el: TMtoInstMap)
	{
		if ((&el)->first == &F)
		{
			//outs() << "Found: " << (&el)->second << "\n";
			return (&el)->second;
		}
	}
	//outs() << "Not found\n";
	return nullptr;
}

/*bool TM_DAE_INTGR_pass::runOnFunction(Function &F){
	for (auto &BB: F)
	{
		if (isTargetBB(BB, MODE::START))
		{
			//outs() << "TxBegin\n";
			
			txDetected = false;
			printTxRegionInst(BB, false);
			//TXBBs.push_back(TXBB);
			//prefetchGlobalLoads();
			//outs() << "TxEnd\n";
			txDetected = false;
			//need to clear UsedBBs
			UsedBBs.clear();
			//PrintTxStatistics();//TODO print into output file
			//List contains instruction for the current BB
			//Need to be cleared before starting next BB
			//InstList.clear();
			//PrefetchedAddresses.clear();
			//LoadNotPrefetch.clear();
			//FunctionArgs.clear();
			loop_depth = 0;
			//GlobalCount = 0;

			//TX_inst.clear();
		}
	}
	return false;
			
}*/		
		
void TM_DAE_INTGR_pass::PrintTxStatistics(){
	for (auto p:InstList)
		outs() << p.first << " : " << p.second << "\n";
}

StringRef TM_DAE_INTGR_pass::get_function_name(CallInst *ci)
{
	Function *fun = ci->getCalledFunction();
	if(Instruction *inst = dyn_cast<Instruction>(ci))
	{
		if (auto* CstExpr = dyn_cast<ConstantExpr>(inst->getOperand(0)))
		{
			if (CstExpr->isCast() && isa<Function>(CstExpr->getOperand(0)))
			{
				fun = dyn_cast<Function>(CstExpr->getOperand(0));
				//outs() << "Wierd thing: " << fun->getName() << "\n";
			}
		}
	}

	if (fun)
		return fun->getName();
	else return StringRef("inderect call");//Apparently nothing can be done with inderect calls
}

/*BasicBlock * TM_DAE_INTGR_pass::getTargetBB(BasicBlock &BB)
{
	for(auto it = succ_begin(&BB), et = succ_end(&BB); it != et; ++it)
	{
		BasicBlock* succ = *it;
		for (auto &I: *succ)
		{
			if(auto *CI = dyn_cast<CallInst>(&I))
			{
				StringRef name = get_function_name(CI);
				if (name == "InnerPartEnd")
				{
					return succ;
				}
			}
					
		}
	}
	return nullptr;

}*/
//This function goes through the BB and checks whether there is fakeCallBegin call there
bool TM_DAE_INTGR_pass::isTargetBB(BasicBlock &BB, MODE mode){
			switch (mode){
			//BB should contain fakeCallBegin
			case MODE::START:
				//Case when fakeCallBegin and fakeCallEnd are in the same region
				for (auto &I:BB)
				{
					if(auto *CI = dyn_cast<CallInst>(&I))
					{
						StringRef name = get_function_name(CI);
						if (name == "beginTransaction")
						{
							return true;
						}
					}
				}
				break;
			//Successor should contain fakeCallEnd
			case MODE::END:
				for(auto it = succ_begin(&BB), et = succ_end(&BB); it != et; ++it)
				{
					BasicBlock* succ = *it;
					for (auto &I: *succ)
					{
						if(auto *CI = dyn_cast<CallInst>(&I))
						{
							StringRef name = get_function_name(CI);
							if (name == "InnerPartEnd")
							{
								return true;
							}
						}
					
					}
				}
				break;
			default:
				break;
			}
				
			return false;
}

/*void TM_DAE_INTGR_pass::prefetchDL(Function *F, list<Instruction*> *DL, Instruction *FirstInst)
{
	for(auto &BB: F)
	{
		for (auto &I: &BB)
		{
			if (!isa<Terminator>(&I) && !isa<PHINode>(&I))
			{

			}
		}
	}
	for (Instruction *Inst : *DL)
	{
		outs() << "Dependent instruction" << *Inst << "\n";
		auto *new_inst = Inst->clone();
		new_inst->insertBefore(FirstInst);
		//new_inst->insertBefore(I);
		vmap[Inst] = new_inst;
		RemapInstruction(new_inst, vmap, RF_NoModuleLevelChanges | RF_IgnoreMissingEntries);
		if (isa<PHINode>(Inst))
		{
			BasicBlock * block = new_inst->getParent()->splitBasicBlock(new_inst, Twine(new_inst->getParent()->getName().str() + "splited"));
		}
	}	

}
bool TM_DAE_INTGR_pass::collectDL(list<Instruction *> *DL, Instruction* inst)
{
	bool res = true;
	for (unsigned int i = 0; i < inst->getNumOperands(); i++)
	{
		Value *V = inst->getOperand(i);

		if (Instruction *Inst = dyn_cast<Instruction>(V))
		{
			//outs() << "Cast to INstr\n";
		
			//Handle recursion
			//If this instruction was marked as dependent before
			//Don't need to mark it as dependent again
			if (!(std::find(DL->begin(), DL->end(), Inst) != DL->end()))
			{
				//outs() << "Was not before\n";
				//Handle TX boundaries
				if (std::find(TX_inst.begin(), TX_inst.end(), Inst) != TX_inst.end())
				{
					//outs() << "IN TM\n";
					//Global stores should not be placed outside TX
					if (StoreInst::classof(Inst)) {
        					res = isLocalPointer(((StoreInst *)Inst)->getPointerOperand());
        					if (!res) {
         		 				outs() << " <!TM_DAE_INTGR store " << *Inst << "!>\n";
							return false;
        					}
					}
					//For not strict version if a value was allocated inside TM
					// this dependence can not be solved
					if (OutsideTMMild && AllocaInst::classof(Inst))
					{
						return false;
					}

					DL->insert(DL->begin(), Inst);
					outs() << "DL instruction " << Inst << "\n"; 
					if (!collectDL(DL, Inst))
						return false;
				}
			}else return true;
		}	}
	return true;
}*/

/*bool TM_DAE_INTGR_pass::printTxRegionInst(BasicBlock &BB, Instruction *inst)
{
	//if BB was visited then don't do anything
	for (auto &bb: UsedBBs)
	{
		if (bb == &BB)
		{
			return;
		}
				
	}
	//If BB wasn't visited then marked it as visited
	UsedBBs.push_back(&BB);	
				
	//For each instruction check whether it is a function call 
	//If it's not a function call then just **print** this instruction
	//If it's a function call, go inside this function
	for(auto &I: BB)
	{
		//First check whether it is a call
		if (isa<CallInst>(&I) && !dyn_cast<CallInst>(&I)->isInlineAsm())
		{
			//TODO: delete if it is redundant
			CallInst * CI = dyn_cast<CallInst>(&I);
											
			StringRef name = get_function_name(CI);
			//outs() << "name =" << name << "\n";
			if (txDetected){
				if (name == "fakeCallEnd")
				{
					//outs() << "fakeCallEnd" << "\n";
					return false;
				}
			}							
							
					
						
			}
			if (name == "fakeCallBegin")
			{
				txDetected = true;
				continue;
			}

		}
		if (txDetected)
		{
			if (&I == inst)
			{
				return true;
			} 
		}

	}
	bool check;
	//If TxEnd wasn't found in current BB
	//TODO: appropriatly go throug complex CFGs
	if (!isTargetBB(BB, MODE::END))
	{
		//RTM_fallbacl_unlock wasn't found in current function
		const TerminatorInst *TInst = BB.getTerminator();
		for(unsigned I = 0, NSucc = TInst->getNumSuccessors(); I < NSucc; ++I)
		{
			check = false;
			//print all instructions inside
			BasicBlock *Succ = TInst->getSuccessor(I);
			for (auto &bb: UsedBBs)
			{
				//Already visited this BasicBlock
				//Skip it
				if (Succ == bb)
				{
					check = true;
					continue;
				}
			}
			//If BB wasn't used
			if (!check)
			{
				if(printTxRegionInst(*Succ, inst))
				{
					return true;
				}
			}
		}
	}
	return false;
}*/

void TM_DAE_INTGR_pass::LoadVisibleDependencies(Instruction * inst)
{
	
	for (unsigned int i = 0; i < inst->getNumOperands(); i++)
	{
		Value *V = inst->getOperand(i);
		//outs() << "Value: " << *V << "\n";
		if (Instruction *Inst = dyn_cast<Instruction>(V))
		{
			//Handle recursion
			//If this instruction was marked as dependent before
			//Don't need to mark it as dependent again
			if (!(std::find(inst_vect.begin(), inst_vect.end(), Inst) != inst_vect.end()))
			{
				//Handle TX boundaries
				if (std::find(TX_inst.begin(), TX_inst.end(), Inst) != TX_inst.end())
				{
					inst_vect.insert(inst_vect.begin(), Inst);
					LoadVisibleDependencies(Inst);
				}
			}else return;
		}
	}
}
//Check if load is inside loop
//forTX flaf is used to detect that this check is for the beginning of TX region
//If TX region is inside loop then increase loop_depth for other instruction 
bool TM_DAE_INTGR_pass::isInstInsideLoop(Instruction * li, bool forTX)
{
	BasicBlock *bb = li->getParent();
	//outs() << "BB:" << bb->getName() << "\n";
	for (auto *LI: LIBV)
	{ 
		int depth = (*LI).getLoopDepth(bb);
		if (forTX)
		{
			if (depth != 0)
			{
				loop_depth = depth;
				++TotalNUMTXInsideLoops;
				//outs() << "Loop: YES\n";
				return true;
			}
		}else
		if ((depth > loop_depth && (li->getParent()->getParent() == FirstInst->getParent()->getParent())) || (depth != 0 && li->getParent()->getParent() != FirstInst->getParent()->getParent()))
		{
			++TotalNUMLoadsInsideLoops;
			//outs() << "Loop: YES\n";
			return true;
		}	
	}
	//outs() << "Loop: NO\n";
	return false;
}

//Check two pointer points out to a global variable
AliasResult TM_DAE_INTGR_pass::pointerAlias(Value* P1, Value* P2, const DataLayout &DL)
{
	uint64_t P1Size = MemoryLocation::UnknownSize;
	Type *P1E1Ty = cast<PointerType>(P1->getType())->getElementType();
	if(P1E1Ty->isSized())
	{
		P1Size = DL.getTypeStoreSize(P1E1Ty);	
	}

	uint64_t P2Size = MemoryLocation::UnknownSize;
	Type *P2E1Ty = cast<PointerType>(P2->getType())->getElementType();
	if(P2E1Ty->isSized())
	{
		P2Size = DL.getTypeStoreSize(P2E1Ty);	
	}
	return AA->alias(P1, P1Size, P2, P2Size);	
}

std::pair<TM_DAE_INTGR_pass::GLOBALREASON, Instruction *>  TM_DAE_INTGR_pass::isLoadGlobal(Instruction * LMemI)
{
	for (User::op_iterator it = LMemI->op_begin(), et = LMemI->op_end(); it != et; ++it)
	{
		if (!isa<GlobalVariable>(&*it))
		{
			//Handling getelement inbounds 
			if(llvm::GetElementPtrConstantExpr::classof(*it))
			{
				if(GEPOperator * gepop = dyn_cast<GEPOperator>(*it))	
				{
					for(User::op_iterator inxs = gepop->idx_begin(); inxs != gepop->idx_end(); ++inxs)
					{
						Value *v = gepop->getPointerOperand();
						if(isa<GlobalVariable>(v))
						{ 
							return std::make_pair(GLOBALREASON::DIRECTGLOBAL, LMemI);
						}
					}
				}
			}
							//Case when load's operand is a pointer
			//it might be pointer to a global variable
			for (auto &gv: GVV)
			{
				for (auto user_of_gv: gv->users())
				{
					if (Instruction *instr_st_gv = dyn_cast<Instruction>(user_of_gv))
					{
						if (StoreInst *storeInst = dyn_cast<StoreInst>(instr_st_gv))
						{
				
							//outs() << "STORE INST  " << *instr_st_gv << "\n";
							Value * storePointer = storeInst->getPointerOperand();
							Value * loadPointer = (dyn_cast<LoadInst>(LMemI))->getPointerOperand();
							if (std::find(FunctionArgs.begin(), FunctionArgs.end(), loadPointer) == FunctionArgs.end())
							{
								AliasResult AAR = pointerAlias(storePointer, loadPointer, (dyn_cast<LoadInst>(LMemI))->getModule()->getDataLayout());
								if (AAR == AliasResult::MustAlias || AAR == AliasResult::MayAlias)
								{
									//outs() << "GLOBAL: MAY/MUST\n";
									//outs() << "Alias match " << *instr_st_gv << "\n";
									return std::make_pair(GLOBALREASON::ALIASGLOBAL, instr_st_gv);
								}	
							}else{
								//outs() << "GLOBAL: NO (function arg)\n";
								return std::make_pair(GLOBALREASON::NOTGLOBAL, LMemI);
							}
						}
					}
				}
			}	
		}else {
			//outs() << "GLOBAL: YES (direct)\n";
			return std::make_pair(GLOBALREASON::DIRECTGLOBAL, LMemI);
		}
	} 
	outs() << "GLOBAL: NO\n";
	return std::make_pair(GLOBALREASON::NOTGLOBAL, LMemI);
}
//1.Check if load depends on another load
//2. or PHINode(fix it later on)
//If agression flag is not set then don't touch a load in case it depends on another load
//With aggression flag set, prefetch this load as well
//3. Also It might be a case that instruction's a load depnds on, depend on function arguments
//TODO: add aggressive version of prefetching
//TODO: add check global stores
bool TM_DAE_INTGR_pass::isLoadDependLoad()
{
	bool flag = false;
	for (auto &inst: inst_vect)
	{
		if (isa<LoadInst>(inst))
		{
			#ifdef AGGRESSION
				LoadNotPrefetch.push_back(inst);
			#endif	
			flag = true;
			break;
		}
		if (isa<PHINode>(inst))
		{
			flag = true;
			break;
		}
		for (int i = 0; i < inst->getNumOperands(); ++i)
		{
			Value *v = inst->getOperand(i);
			if (std::find(FunctionArgs.begin(), FunctionArgs.end(), v) != FunctionArgs.end())
			{
				flag = true;
				break;
			}
		}
	}
	if(flag)
	{
		++TotalNUMLoadsDependOnLoads;
		//outs() << "Dependancy: YES\n";
	}else{
		//outs() << "Dependancy: NO\n";

	}
	return flag;
}

bool TM_DAE_INTGR_pass::isAddressPrefetched(Instruction * inst)
{
	Value * value;
	if (StoreInst *sti = dyn_cast<StoreInst>(inst))
		value = sti->getPointerOperand();
	else if (LoadInst *ldi = dyn_cast<LoadInst>(inst))
		value = ldi->getPointerOperand();
	if (std::find(PrefetchedAddresses.begin(), PrefetchedAddresses.end(), value) != PrefetchedAddresses.end())
	{
		//outs() << "Prefetched: Yes\n";
		return true;
	}
	else{
		//outs() << "Prefetched: NO\n";
		 return false;
	}
}

void TM_DAE_INTGR_pass::notAggressivePrefetching(Instruction * I, std::pair<TM_DAE_INTGR_pass::GLOBALREASON, Instruction *> *metadata)
{
	//outs() << "LOAD: " << *LMemI << "\n";
	//If there are instruction which current load depends on
	//First duplicate all these instruction before TX region
	for (Instruction *Inst : inst_vect)
	{
		//outs() << "Dependent instruction" << *Inst << "\n";
		auto *new_inst = Inst->clone();
		new_inst->insertBefore(FirstInst);
		//new_inst->insertBefore(I);
		vmap[Inst] = new_inst;
		RemapInstruction(new_inst, vmap, RF_NoModuleLevelChanges | RF_IgnoreMissingEntries);
	}	
	inst_vect.clear();
	//If load points to a global variable directly then
	//Get address for prefetching directly from this load
	unsigned PtrAs;
	Value *DataPtr;
	LoadInst *LMemI = dyn_cast<LoadInst>(I);
	if (metadata->first == GLOBALREASON::DIRECTGLOBAL || metadata->first == GLOBALREASON::ALIASGLOBAL)
	{
		//Clone load, because after renaming all instruction which current load depends on
		//Have different names of their arguments
		//To mach this differencies, need to rename
		auto *new_inst = LMemI->clone();
		new_inst->insertBefore(LMemI);
		vmap[LMemI] = new_inst;
		RemapInstruction(new_inst, vmap, RF_NoModuleLevelChanges | RF_IgnoreMissingEntries);
		//prefetch load before fakeCallBegin
		LoadInst * new_load_inst = dyn_cast<LoadInst>(new_inst);
		PtrAs = new_load_inst->getPointerAddressSpace();
		DataPtr = new_load_inst->getPointerOperand();
		//To mark that this address has already prefetched
		//Don't want to prefetch the same address twice
		PrefetchedAddresses.push_back(DataPtr);
		//This instruction is an actual load
		//don't need it as the address will be prefetched
		new_inst->eraseFromParent();
	}	
	//If load aliases with a global variable, then
	//take address for prefetching from appropriate store instruction
	/*else if (metadata->first == GLOBALREASON::ALIASGLOBAL)
	{
		StoreInst * storeInst = dyn_cast<StoreInst>(metadata->second);
		outs() << "ALIASGLOBAL " << *storeInst << "\n";
		PtrAs = storeInst->getPointerAddressSpace();
		DataPtr = storeInst->getPointerOperand();
		//To mark that this address has already prefetched
		//Don't want to prefetch the same address twice
		PrefetchedAddresses.push_back(DataPtr);
	}*/
	LLVMContext &Context = DataPtr->getContext();	
	Type *I8Ptr = Type::getInt8PtrTy(Context, PtrAs);
	CastInst *Cast = CastInst::CreatePointerCast(DataPtr, I8Ptr, "", FirstInst);
	IRBuilder<> Builder(FirstInst);
	Module *M = FirstInst->getParent()->getParent()->getParent();
	Type *I32 = Type::getInt32Ty(FirstInst->getContext());
	//CastInst *Cast = CastInst::CreatePointerCast(DataPtr, I8Ptr, "", I);
	//IRBuilder<> Builder(I);
	//Module *M = I->getParent()->getParent()->getParent();
	//Type *I32 = Type::getInt32Ty(I->getContext());
	Value *PrefetchFunc = Intrinsic::getDeclaration(M, Intrinsic::prefetch);
					
	//To remember: new_load_inst->mayReadFromMemory() ? 0 : 1	
	Builder.CreateCall(PrefetchFunc, 
		{Cast, 
		ConstantInt::get(I32, 0),
		ConstantInt::get(I32,3), ConstantInt::get(I32,1)});
	//outs() << "Prefetch is done\n";	
	++TotalNUMPrefetchedLoads;	
	return;
}

void TM_DAE_INTGR_pass::prefetchGlobalLoads(){
#ifdef AGGRESSION
	for (auto &I: TX_inst)
	{
		if (isa<LoadInst>(*&I))
		{
			//outs() << "LOAD is detected: " << *LMemI << "\n";
			//Check if load points out to global variable
			std::pair<GLOBALREASON, Instruction*> metadata = isLoadGlobal(*&I);
			//Prefetch only if load points to global variable and load is not inside loop
			//And its address wasn't prefetched before
			if( !(isInstInsideLoop(*&I, false)) &&  (metadata.first != GLOBALREASON::NOTGLOBAL) && !isAddressPrefetched(metadata.second))
			{
				//List of load's dependent instructions that should be prefetched
				inst_vect.clear();
				//Collect dependent inctructions
				LoadVisibleDependencies(*&I);
				//Remove all loads other loads depend on
				isLoadDependLoad();
			}else{
				inst_vect.clear();
				continue;
			}

		}
	}
#endif
	//chech whether an instruction is load or store
	for (auto &I: TX_inst)
	{
		if (LoadInst *LMemI = dyn_cast<LoadInst>(*&I))
		{
			outs() << "LOAD is detected: " << *LMemI << "\n";
			++TotalNUMLoads;
			//Check if load points out to global variable
			std::pair<GLOBALREASON, Instruction*> metadata = isLoadGlobal(*&I);
			bool insideloop = isInstInsideLoop(*&I, false);
			//Prefetch only if load points to global variable and load is not inside loop
			//And its address wasn't prefetched before
			if( (metadata.first != GLOBALREASON::NOTGLOBAL) && (insideloop == false) && !isAddressPrefetched(metadata.second) && (std::find(LoadNotPrefetch.begin(), LoadNotPrefetch.end(), *&I) == LoadNotPrefetch.end()))
			{
				//List of load's dependent instructions that should be prefetched
				inst_vect.clear();
				//Collect dependent inctructions
				LoadVisibleDependencies(*&I);
				//Now, don't touch a load if it depends on another load
				//TODO: add aggresive version
				if (!isLoadDependLoad())
				{
					notAggressivePrefetching(*&I, &metadata);
				}else{
					#ifdef AGGRESSION
						notAggressivePrefetching(*&I, &metadata);
					#endif
				}
			}else{
				inst_vect.clear();
				continue;
			}

		}
	}
}
