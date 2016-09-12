/*
 * All of the documentation and software included in the
 * Alchemy Software is copyrighted by Stanley Kok, Parag
 * Singla, Matthew Richardson, Pedro Domingos, Marc
 * Sumner, Hoifung Poon, Daniel Lowd, and Jue Wang.
 *
 * Copyright [2004-09] Stanley Kok, Parag Singla, Matthew
 * Richardson, Pedro Domingos, Marc Sumner, Hoifung
 * Poon, Daniel Lowd, and Jue Wang. All rights reserved.
 *
 * Contact: Pedro Domingos, University of Washington
 * (pedrod@cs.washington.edu).
 *
 * Redistribution and use in source and binary forms, with
 * or without modification, are permitted provided that
 * the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above
 * copyright notice, this list of conditions and the
 * following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the
 * above copyright notice, this list of conditions and the
 * following disclaimer in the documentation and/or other
 * materials provided with the distribution.
 *
 * 3. All advertising materials mentioning features or use
 * of this software must display the following
 * acknowledgment: "This product includes software
 * developed by Stanley Kok, Parag Singla, Matthew
 * Richardson, Pedro Domingos, Marc Sumner, Hoifung
 * Poon, Daniel Lowd, and Jue Wang in the Department of
 * Computer Science and Engineering at the University of
 * Washington".
 *
 * 4. Your publications acknowledge the use or
 * contribution made by the Software to your research
 * using the following citation(s):
 * Stanley Kok, Parag Singla, Matthew Richardson and
 * Pedro Domingos (2005). "The Alchemy System for
 * Statistical Relational AI", Technical Report,
 * Department of Computer Science and Engineering,
 * University of Washington, Seattle, WA.
 * http://alchemy.cs.washington.edu.
 *
 * 5. Neither the name of the University of Washington nor
 * the names of its contributors may be used to endorse or
 * promote products derived from this software without
 * specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE UNIVERSITY OF WASHINGTON
 * AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE UNIVERSITY
 * OF WASHINGTON OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT,
 * INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
 * ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN
 * IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 */
#ifndef GROUNDFORMULA_H_JUN_26_2005
#define GROUNDFORMULA_H_JUN_26_2005

#include <cfloat>
#include <ext/hash_set>
using namespace __gnu_cxx;
#include "hasharray.h"
#include "array.h"
#include "hash.h"
#include <map>
#include <cstring>

using namespace std;

// containers    /////////////////////////////////////////////
typedef map<int, pair<int,bool> > IntBoolPair;
typedef IntBoolPair::iterator IntBoolPairItr;
//////////////////////////////////////////////////////////////

// Constants
//const double HARD_GROUNDCLAUSE_WT = DBL_MAX;
const double HARD_GROUNDFORMULA_WT = 100;
const bool gfdebug = false;

// Forward declarations
class MLN;
class Domain;
class Clause;
class GroundPredicate;
class GroundClause;
class HashGroundPredicate;
class EqualGroundPredicate;

// Typedefs
typedef HashArray<GroundPredicate*, HashGroundPredicate, EqualGroundPredicate>
 GroundPredicateHashArray;

/**
 * Represents a grounded clause.
 */
class GroundFormula
{
 public:
  GroundFormula(const Array<GroundClause*>* const & gcs);

  ~GroundFormula()
  {
    if (gndClauses_) delete gndClauses_;
  }


  void addWt(const double& wt)
  { if (wt_ == HARD_GROUNDFORMULA_WT) return; wt_ += wt; }

  void setWt(const double& wt)
  { if (wt_ == HARD_GROUNDFORMULA_WT) return; wt_ = wt; }

  double getWt() const { return wt_; }

  void setWtToHardWt() { wt_ = HARD_GROUNDFORMULA_WT; }
  bool isHardFormula() const { return (wt_ == HARD_GROUNDFORMULA_WT); }

  int getNumGroundClauses() const { return gndClauses_->size(); }

  const GroundClause* getGroundClause(const int& i) const
  {
    return (*gndClauses_)[i];
  }


  size_t hashCode() { return hashCode_; }

  bool same(const GroundFormula* const & gf)
  {
    if (this == gf) return true;
    if (gndClauses_->size() != gf->getNumGroundClauses())
    {
      return false;
    }
    if(parentFormulaId_ != gf->parentFormulaId_){return false;} //added by Happy
    for(int c = 0 ; c < gndClauses_->size() ; c++)
    {
      if (!(*gndClauses_)[c]->same(gf->getGroundClause(c)))
        return false;
    }
    return true;
  }

  void printWithoutWt(ostream& out) const;
  void print(ostream& out) const;

  ostream& print(ostream& out, const Domain* const& domain,
                 const bool& withWt, const bool& asInt,
                 const bool& withStrVar,
                 const GroundPredicateHashArray* const & predHashArray) const;

  ostream& printWithoutWt(ostream& out, const Domain* const & domain,
                  const GroundPredicateHashArray* const & predHashArray) const;

  ostream&
  printWithoutWtWithStrVar(ostream& out, const Domain* const & domain,
                  const GroundPredicateHashArray* const & predHashArray) const;

  ostream& printWithWtAndStrVar(ostream& out, const Domain* const& domain,
                  const GroundPredicateHashArray* const & predHashArray) const;

  ostream& print(ostream& out, const Domain* const& domain,
                 const GroundPredicateHashArray* const & predHashArray) const;

  ostream& printWithoutWtWithStrVarAndPeriod(ostream& out,
                                             const Domain* const& domain,
                  const GroundPredicateHashArray* const & predHashArray) const;


 private:

  /**
   * Computes the hash code and stores it.
   */
  void rehash()
  {
    Array<unsigned int>* intArrRep = new Array<unsigned int>;

    // for each clause
    for(int c = 0 ; c < gndClauses_ ->size(); c++)
    {

      GroundClause* gc = (*gndClauses_)[c];

      // For each predicate
      for (int i = 0; i < gc->getGndPredIndexes()->size(); i++)
      {
          // For each pred 1 (if pos.) or 0 (if neg.) is appended to intArrRep
        if (gc->getGroundPredicateIndex(i) > 0)
          intArrRep->append(1);
        else
          intArrRep->append((unsigned int)0);
        intArrRep->append(abs(gc->getGroundPredicateIndex(i)));
      }
    }
    
    hashCode_ = Hash::hash(*intArrRep);
    delete intArrRep;
  }

 public://added by Happy
 int parentFormulaId_; //added by Happy
 private:
    // Hash code of this ground clause
  size_t hashCode_;
  Array<GroundClause*>* gndClauses_;

  //Array<int>* gndPredIndexes_; // 4 + 4*n bytes (n is no. of preds)

    // overloaded to indicate whether this is a hard clause
    // if this is a hard clause, wt_ is set to HARD_GROUNDCLAUSE_WT
  double wt_; // 8 bytes

    // Number of first-order clauses this clause corresponds to. Also stores
    // if the weight has been flipped from each parent clause
  IntBoolPair* foClauseFrequencies_;

};


////////////////////////////////// hash /////////////////////////////////


class HashGroundFormula
{
 public:
  size_t operator()(GroundFormula* const & gf) const  { return gf->hashCode(); }
};


class EqualGroundFormula
{
 public:
  bool operator()(GroundFormula* const & f1, GroundFormula* const & f2) const
    { return f1->same(f2); }
};


/////////////////////////////// containers  /////////////////////////////////


typedef HashArray<GroundFormula*, HashGroundFormula, EqualGroundFormula>
  GroundFormulaHashArray;

typedef hash_set<GroundFormula*, HashGroundFormula, EqualGroundFormula>
  GroundFormulaSet;


#endif
