/*
 * All of the documentation and software included in the
 * Alchemy Software is copyrighted by Stanley Kok, Parag
 * Singla, Matthew Richardson, Pedro Domingos, Marc
 * Sumner, Hoifung Poon, and Daniel Lowd.
 * 
 * Copyright [2004-07] Stanley Kok, Parag Singla, Matthew
 * Richardson, Pedro Domingos, Marc Sumner, Hoifung
 * Poon, and Daniel Lowd. All rights reserved.
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
 * Poon, and Daniel Lowd in the Department of Computer Science and
 * Engineering at the University of Washington".
 * 
 * 4. Your publications acknowledge the use or
 * contribution made by the Software to your research
 * using the following citation(s): 
 * Stanley Kok, Parag Singla, Matthew Richardson and
 * Pedro Domingos (2005). "The Alchemy System for
 * Statistical Relational AI", Technical Report,
 * Department of Computer Science and Engineering,
 * University of Washington, Seattle, WA.
 * http://www.cs.washington.edu/ai/alchemy.
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
#include "groundclause.h"
#include "groundformula.h"
#include "groundpredicate.h"
#include "clause.h"
#include "mln.h"

GroundFormula::GroundFormula(const Array<GroundClause*>* const & gcs) 
{
  wt_ = 0.0;
  for(int i = 0 ; i < gcs->size() ; i++)
  {
    wt_ += (*gcs)[i]->getWt();
  }
  gndClauses_ = gcs;
  Array<unsigned int>* intArrRep = new Array<unsigned int>;

    // for each clause
    for(int c = 0 ; c < gndClauses_ ->size(); c++)
    {

      GroundClause* gc = (*gndClauses_)[c];

      // For each predicate
      for (int i = 0; i < gc->getGroundPredIndexes()->size(); i++)
      {
          // For each pred 1 (if pos.) or 0 (if neg.) is appended to intArrRep
        if (gc->getGroundPredIndex(i) > 0)
          intArrRep->append(1);
        else
          intArrRep->append((unsigned int)0);
        intArrRep->append(abs(gc->getGroundPredIndex(i)));
      }
    }
  hashCode_ = Hash::hash(*intArrRep);
  delete intArrRep;
  gndPredIndexes_->compress();
}


void GroundFormula::printWithoutWt(ostream& out) const
{
  for(int c = 0 ; c < gndClauses_->size() ; c++)
  {
    (*gndClauses_)[c]->printWithoutWt(out);
    out<<endl;
  }
  
}

void GroundFormula::print(ostream& out) const
{ out << wt_ << " "; printWithoutWt(out); }

ostream&
GroundFormula::print(ostream& out, const Domain* const& domain, 
                    const bool& withWt, const bool& asInt, 
                    const bool& withStrVar,
                   const GroundPredicateHashArray* const & predHashArray) const
{
  
  for(int c = 0 ; c < gndClauses_->size() ; c++)
  {
    (*gndClauses_)[c]->print(out,domain,withWt,asInt,withStrVar,predHashArray);
    out<<endl;
  }
  return out;
}


ostream&
GroundFormula::printWithoutWt(ostream& out, const Domain* const & domain,
                   const GroundPredicateHashArray* const & predHashArray) const
{ return print(out, domain, false, false, false, predHashArray); }

ostream& 
GroundFormula::printWithoutWtWithStrVar(ostream& out,
                                       const Domain* const & domain,
                   const GroundPredicateHashArray* const & predHashArray) const
{ return print(out, domain, false, false, true, predHashArray); }

ostream&
GroundFormula::printWithWtAndStrVar(ostream& out, const Domain* const& domain,
                   const GroundPredicateHashArray* const & predHashArray) const
{ return print(out, domain, true, false, true, predHashArray); }

ostream&
GroundFormula::print(ostream& out, const Domain* const& domain,
                   const GroundPredicateHashArray* const & predHashArray) const
{ return print(out, domain, true, false, false, predHashArray); }
    
ostream&
GroundFormula::printWithoutWtWithStrVarAndPeriod(ostream& out, 
                                                const Domain* const& domain,
                   const GroundPredicateHashArray* const & predHashArray) const
{
  printWithoutWtWithStrVar(out, domain, predHashArray);
  if (isHardFormula()) out << ".";
  return out;
}

