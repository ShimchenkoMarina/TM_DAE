//===--------------- Replace.cpp - Replaces conditional branch------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
/// \file Replace.cpp
///
/// \brief
///
/// \copyright Eta Scale AB. Licensed under the Eta Scale Open Source License. See
/// the LICENSE file for details.
//
//===----------------------------------------------------------------------===//
#include <map>
#include <vector>
#include <string>
#include <iostream>
#include <type_traits>
#include <fstream>

#include "llvm/Analysis/BranchProbabilityInfo.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Metadata.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/FileSystem.h"

#include "llvm/Transforms/Utils/Cloning.h"


#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "Util/Annotation/MetadataInfo.h"

//#define F_KERNEL_SUBSTR "__kernel__"
#define EXECUTE_SUFFIX "_execute"
#define CLONE_SUFFIX "_clone"
#define THRESHOLD (0.7)

std::pair<std::string, std::string> getBranchProb(BranchInst *BI, int number)
{
	std::ifstream file;
	int count = 0;
	std::string funName = dyn_cast<Instruction>(BI)->getParent()->getParent()->getName().str();
	std::string word;
	word.clear();

	file.open("branchProbabilities.txt");
	outs() << funName << "\n";
	while (file >> word)
	{
		if (word == funName)
		{
			if  (count == number)
			{
				file >> word;// ":"
				file >> word;// address of instruction
				std::string br0 = word;
				file >> word;// "funName"
				file >> word;// ":"
				file >> word;// address of instruction
				std::string br1 = word;
				return std::make_pair(br0, br1);
				
			}
			count++;
		}
	}	
	file.close();
	outs() << "Error: no such bb " << number <<"\n";
	return std::make_pair("0.0", "0.0");
}
// pair represents: <isReducable, whichBranch>
std::pair<bool, int> isReducableBranch(BranchInst *BI, int number) {
    std::pair<std::string, std::string> string_bp = getBranchProb(BI, number);
    //std::string string_bp1 = getBranchProb(BI, "BranchProb1");
    if (string_bp.first.length() > 0 && string_bp.second.length() > 0 ) {
        double bp0 = std::stod(string_bp.first);
        double bp1 = std::stod(string_bp.second);
        if (bp0 > THRESHOLD) {
            return std::make_pair(true, 0);
        } else if (bp1 > THRESHOLD) {
            return std::make_pair(true, 1);
        }
    }
    return std::make_pair(false, 0);
}
void replaceBranch(BasicBlock *block, int number) {
    TerminatorInst *TInst = block->getTerminator();
    IRBuilder<> Builder(TInst);
    BranchInst *uncondBI;
    BasicBlock *dst, *comp;
    if (BranchInst *BI = dyn_cast<BranchInst>(TInst)) {
        std::pair<bool, int> res = isReducableBranch(BI, number);
        if (res.first) {
            if (res.second == 0) {
                dst = BI->getSuccessor(0);
                comp = BI->getSuccessor(1);
                uncondBI = BranchInst::Create(dst);
                util::AttachMetadata(uncondBI, "BranchProb0", "1");
                util::AttachMetadata(uncondBI, "BranchProb1", "0");
                comp->removePredecessor(block);
                ReplaceInstWithInst(TInst, uncondBI);
            } else if (res.second == 1) {
                dst = BI->getSuccessor(1);
                comp = BI->getSuccessor(0);
                uncondBI = BranchInst::Create(dst);
                util::AttachMetadata(uncondBI, "BranchProb0", "0");
                util::AttachMetadata(uncondBI, "BranchProb1", "1");
                comp->removePredecessor(block);
                ReplaceInstWithInst(TInst, uncondBI);
            }
        }
    }
}

bool minimizeFunctionFromBranchPred(Function *cF) {
    errs() << "Optimizing function: " << cF->getName().str() << "\n";
    int number = 0;
    for (Function::iterator block = cF->begin(), blockEnd = cF->end(); block != blockEnd; ++block) {
	llvm::TerminatorInst *TInst = block->getTerminator();
        int numSuccessors = TInst->getNumSuccessors();
        if (numSuccessors == 2) {
		replaceBranch(&*block, number);
		number++;
		number++;
	}
    }
    return true;
}

