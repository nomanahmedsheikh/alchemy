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
#ifndef MRF_H_SEP_23_2005
#define MRF_H_SEP_23_2005

#include <sys/times.h>
#include <sys/time.h>
#include <cstdlib>
#include <cfloat>
#include <fstream>
#include "timer.h"
#include "mln.h"
#include "groundpredicate.h"

const bool mrfdebug = true;

///////////////////////////////////////////////////////////////////////////

  // used as parameter of addGndClause()
struct AddGroundClauseStruct
{
  AddGroundClauseStruct(const GroundPredicateSet* const & sseenPreds,
                        GroundPredicateSet* const & uunseenPreds,
                        GroundPredicateHashArray* const & ggndPreds,
                        const Array<int>* const & aallPredGndingsAreQueries,
                        GroundClauseSet* const & ggndClausesSet,
                        Array<GroundClause*>* const & ggndClauses,
                        const bool& mmarkHardGndClauses,
                        const double* const & pparentWtPtr,
                        const int & cclauseId)
    : seenPreds(sseenPreds), unseenPreds(uunseenPreds), gndPreds(ggndPreds),
      allPredGndingsAreQueries(aallPredGndingsAreQueries),
      gndClausesSet(ggndClausesSet),
      gndClauses(ggndClauses), markHardGndClauses(mmarkHardGndClauses),
      parentWtPtr(pparentWtPtr), clauseId(cclauseId) {}
  
  ~AddGroundClauseStruct() {}
  
  const GroundPredicateSet* seenPreds;
  GroundPredicateSet* unseenPreds;
  GroundPredicateHashArray* gndPreds;
  const Array<int>* allPredGndingsAreQueries;
  GroundClauseSet* gndClausesSet;
  Array<GroundClause*>* gndClauses;
  const bool markHardGndClauses;
  const double* parentWtPtr;
  const int clauseId;
};

///////////////////////////////////////////////////////////////////////////


class MRF
{
 public:
    //allPredGndingsAreQueries[p] is 1 (true) if all groundings of predicate p 
    //are in queries, otherwise it is 0 (false). 
    //allPredGndingsAreQueries can be
    //NULL if none of the predicates have all their groundings as queries.
  MRF(const GroundPredicateHashArray* const& queries, 
      const Array<int>* const & allPredGndingsAreQueries,
      const Domain* const & domain,  const Database * const & db, 
      const MLN* const & mln, const bool& markHardGndClauses,
      const bool& trackParentClauseWts, const int& memLimit)
  {
    cout << "creating mrf..." << endl; 
    Timer timer;
    GroundPredicateSet unseenPreds, seenPreds;
    GroundPredicateToIntMap gndPredsMap;
    GroundClauseSet gndClausesSet;
    gndPreds_ = new GroundPredicateHashArray;
    gndClauses_ = new Array<GroundClause*>;
    realGndPreds_ = new GroundPredicateHashArray;
    realGndClauses_ = new Array<Array<Array<GroundClause*>*>*>();
    realGndClauses_->growToSize(mln->getNumClauses(), new Array<Array<GroundClause*>*>());
    if(mrfdebug)
      cout<<"realGndClauses size : "<<realGndClauses_->size()<<endl;    
    reverseMap = new Array<Array<Array<int>*>*>();
    long double memNeeded = 0;

    if(mrfdebug)
      cout<<"initialization done..."<<endl;
	
      //add GroundPredicates in queries to unseenPreds
    //cout<<"adding GroundPredicates in queries to unseenPreds"<<endl; //added by Happy
    //cout<<"Number of queries : "<<queries->size()<<endl; //added by Happy
    for (int i = 0; i < queries->size(); i++)
    {
      GroundPredicate* gp = (*queries)[i];
      unseenPreds.insert(gp);
      int gndPredIdx = gndPreds_->append(gp);
      assert(gndPredsMap.find(gp) == gndPredsMap.end());
      gndPredsMap[gp] = gndPredIdx;
    }
    //cout<<"added GroundPredicates in queries to unseenPreds"<<endl; //added by Happy
      // If too much memory to build MRF then destroy it
    if (memLimit > 0)
    {
      memNeeded = sizeKB();
      if (memNeeded > memLimit)
      {
        for (int i = 0; i < gndClauses_->size(); i++)
          delete (*gndClauses_)[i];
        delete gndClauses_;    

        for (int i = 0; i < gndPreds_->size(); i++)
          if ((*gndPreds_)[i]) delete (*gndPreds_)[i];
        delete gndPreds_;
                    
        throw 1;
      }
    }
	
      //while there are still unknown preds we have not looked at
    while (!unseenPreds.empty())   
    {
      GroundPredicateSet::iterator predIt = unseenPreds.begin();
      GroundPredicate* pred = *predIt;
      unsigned int predId = pred->getId();
      //cout << "\tlooking at pred: ";  pred->print(cout, domain); cout << " with predId : "<<predId<<endl; //added by Happy
//      cout << "(*allPredGndingsAreQueries)[predId] : "<<(*allPredGndingsAreQueries)[predId]<<endl; //added by Happy
      bool genClausesForAllPredGndings = false;
        // if all groundings of predicate with predId are queries
      if (allPredGndingsAreQueries && (*allPredGndingsAreQueries)[predId] >= 1)
      {
          // if we have not generated gnd clauses containing the queries before
        if ((*allPredGndingsAreQueries)[predId] == 1){
          genClausesForAllPredGndings = true;
          // cout<<"inside IF : Added By Noman"<<endl;
        } 
        else
        {   //we have dealt with predicate predId already          
          //cout << "\terasing at pred: ";  pred->print(cout, domain);  //added by Happy
          //cout<< endl; //added by Happy
          unseenPreds.erase(predIt);
          // cout<<"inside ELSE : Added By Noman"<<endl;
          seenPreds.insert(pred);
          continue;
        }
      }
        //get all clauses that contains pred with predId
        // We have recieved all the clauses that contains predicate "Smokes"  (Added By Noman)
      const Array<IndexClause*>* clauses
        = mln->getClausesContainingPred(predId);

        //for each clause, ground it and find those with unknown truth values,
        //dropping ground preds which do not matter to the clause's truth value
      //cout<<"\tclauses->size : "<<clauses->size()<<endl; //added by Happy
      for (int i = 0; clauses && i < clauses->size(); i++)
      {
        Clause* c = (*clauses)[i]->clause;
        //cout << "\tIn clause c: ";  c->printWithWtAndStrVar(cout, domain); cout << endl; //added by Happy
        //const int formulaId = c->parentFormulaId_;
//        cout<<"In formula : "<<((*(mln->getFormulaAndClausesArray()))[formulaId])->formula<<endl; //added by Happy
		    const int clauseId = mln->findClauseIdx(c);  
		    assert(clauseId >= 0);
		    //cout<<"\tclause id : " << clauseId <<endl; //added by Happy
		    //ignore clause with zero weight
        if (c->getWt() == 0) continue;

          //add gnd clauses with unknown truth values to gndClauses_
        const double* parentWtPtr =
          (trackParentClauseWts) ? c->getWtPtr() : NULL;
        AddGroundClauseStruct agc(&seenPreds, &unseenPreds, gndPreds_,
                                  allPredGndingsAreQueries,
                                  &gndClausesSet, gndClauses_,
                                  markHardGndClauses, parentWtPtr,
                                  clauseId);
        cout << "Happy number of grounded clauses = " << gndClauses_->size() << endl; //added by Happy
    	try
        {
          //pred = Smokes(A), c=!Smokes(a1)v Cancer(a1), genClausesForAllPredGndings=False      //added by Noman
          if(mrfdebug)
            cout<<"calling addUnknownGndClauses..."<<endl;
          addUnknownGndClauses(pred, c, domain, db, genClausesForAllPredGndings,
                               &agc);
          if(mrfdebug)
            cout<<"called addUnknownGndClauses..."<<endl;
        }
        catch (bad_alloc&)
        {
          cout << "Bad alloc when adding unknown ground clauses to MRF!\n";
          cerr << "Bad alloc when adding unknown ground clauses to MRF!\n";
          throw 1;
        }
        //cout<<"\tCalled addUnknownGndClauses..."<<endl; //added by Happy
        //cout << "number of grounded clauses = " << gndClauses_->size() << endl; //added by Happy
          // If too much memory to build MRF then destroy it
        if (memLimit > 0)
        {
          memNeeded = sizeKB();
            //cout << "preds " << gndPreds_->size() << endl;
            //cout << "clauses " << gndClauses_->size() << endl;
            //cout << "memory " << memNeeded << endl;
            //cout << "limit " << memLimit << endl;
          if (memNeeded > memLimit)
          {
            for (int i = 0; i < gndClauses_->size(); i++)
              delete (*gndClauses_)[i];
            delete gndClauses_;    

            for (int i = 0; i < gndPreds_->size(); i++)
              if ((*gndPreds_)[i]) delete (*gndPreds_)[i];
            delete gndPreds_;
    
            throw 1;
          }
        }
      } // clause loop ended
      //cout<<"all clauses done..."<<endl; //added by Happy
      //clauses with negative wts are handled by the inference algorithms

      //if all the gnd clauses that pred appears in have known truth value,
      //it is not added to gndPreds_ and excluded from the MCMC network

      //cout << "\terasing pred: ";  pred->print(cout, domain); cout << endl;//added by Happy
      unseenPreds.erase(predIt);
      seenPreds.insert(pred);
      if (genClausesForAllPredGndings)
      {
        assert(allPredGndingsAreQueries && 
               (*allPredGndingsAreQueries)[predId]==1);
          //indicate we have seen all groundings of pred predId
        (*allPredGndingsAreQueries)[predId]++;
      }
    }//while (!unseenPreds.empty())

    //replace gndClauses and gndPreds by realGndClauses and realGndPreds respectively.
    for(int i = 0 ; i < gndClauses_->size() ; i++)
    {
      delete (*gndClauses_)[i];
    }
    gndClauses_->clear();
    int I = realGndClauses_->size();
    for(int i = 0 ; i < I ; i++)
    {
      int J = (*realGndClauses_)[i]->size();
      reverseMap->append(new Array<Array<int>*>());
      for(int j = 0 ; j < J ; j++)
      {
        Array<GroundClause*> temp = *((*((*realGndClauses_)[i]))[j]);
        int K = temp.size();
        ((*reverseMap)[i])->append(new Array<int>());
        for(int k = 0 ; k < K ; k++)
        {
          (temp[k]->foAndGndId_).first = i;
          (temp[k]->foAndGndId_).second = j;
          ((*(*reverseMap)[i])[j])->append(gndClauses_->size());
          gndClauses_->append(temp[k]);
        } 
      }
    }

    for(int i = 0 ; i < gndPreds_->size() ; i++)
    {
      delete (*gndPreds_)[i];
    }
    gndPreds_ = realGndPreds_;
    //cout << "number of grounded predicates = " << gndPreds_->size() << endl; //added by Happy
    //cout << "number of grounded clauses = " << gndClauses_->size() << endl; //added by Happy
    if (gndClauses_->size() == 0)
      cout<< "Markov blankets of query ground predicates are empty" << endl;

    if (mrfdebug)
    {
      cout << "Clauses in MRF: " << endl;
      for (int i = 0; i < gndClauses_->size(); i++)
      {
        (*gndClauses_)[i]->print(cout, domain, gndPreds_);
        cout << endl;
      }
    }
      // Compress preds
    for (int i = 0; i < gndPreds_->size(); i++)
      (*gndPreds_)[i]->compress();

    gndPreds_->compress();
    gndClauses_->compress();

    cout <<"Time taken to construct MRF = ";
    Timer::printTime(cout,timer.time());
    cout << endl;
  }

  /**
   * Computes and returns size of the mrf in kilobytes
   */
  long double sizeKB()
  {
      // # of ground clauses times memory for a ground clause +
      // # of ground predicates times memory for a ground predicate
    long double size = 0;
    for (int i = 0; i < gndClauses_->size(); i++)
      size += (*gndClauses_)[i]->sizeKB();
    for (int i = 0; i < gndPreds_->size(); i++)
      size += (*gndPreds_)[i]->sizeKB();

    return size;    
  }

  static void addToRealGndClauses(const Clause* const & clause, const bool &isHardClause, const AddGroundClauseStruct* const & agcs)
  {
    if(mrfdebug)
      cout<<"In MRF::addToRealGndClauses"<<endl;
    int i = agcs->clauseId;
    int j = (*realGndClauses_)[i]->size();
    if(mrfdebug)
      cout<<"i : "<<i<<",j : "<<j<<endl;

    cout<<"realGroundPreds size : "<<realGndPreds_->size()<<endl;
    (*realGndClauses_)[i]->append(new Array<GroundClause*>());
    Array<int> subTypeIndices(1,-1);
    Array<int> normalIndices;
    const double* parentWtPtr = agcs->parentWtPtr;
    for(int n = 0 ; n < clause->getNumPredicates() ; n++)
    {
      Predicate* pred = clause->getPredicate(n);
      if(mrfdebug)
        cout<<"pred->getName() : "<<pred->getName()<<endl;
      if(strcmp(pred->getName(),"subtype") == 0)
      {
        subTypeIndices[0] = n;
        if(mrfdebug)cout<<"subtype size is : "<<subTypeIndices.size()<<endl;
        GroundClause *gc = new GroundClause(clause, realGndPreds_, subTypeIndices);
        if(mrfdebug)
          cout<<"piece gc is created..."<<endl;
        if (agcs->markHardGndClauses && isHardClause) gc->setWtToHardWt();
        gc->appendToGndPreds(realGndPreds_);
        if(mrfdebug)
          cout<<"appendtogndpreds done..."<<endl;
        bool invertWt = false;
        // We want to normalize soft unit clauses to all be positives
        if (!isHardClause && gc->getNumGroundPredicates() == 1 &&
            !gc->getGroundPredicateSense(0))
        {
          gc->setGroundPredicateSense(0, true);
          gc->setWt(-gc->getWt());
          invertWt = true;
        }
        if (parentWtPtr)
          gc->incrementClauseFrequency(agcs->clauseId, 1, invertWt);
        (*(*realGndClauses_)[i])[j]->append(gc);
      }
      else
      {
        normalIndices.append(n);
      }
    }
    GroundClause *gc = new GroundClause(clause, agcs->gndPreds, normalIndices);
    if (agcs->markHardGndClauses && isHardClause) gc->setWtToHardWt();
    gc->appendToGndPreds(realGndPreds_);
    bool invertWt = false;
    // We want to normalize soft unit clauses to all be positives
    if (!isHardClause && gc->getNumGroundPredicates() == 1 &&
        !gc->getGroundPredicateSense(0))
    {
      gc->setGroundPredicateSense(0, true);
      gc->setWt(-gc->getWt());
      invertWt = true;
    }
    
    if (parentWtPtr)
      gc->incrementClauseFrequency(agcs->clauseId, 1, invertWt);
    (*(*realGndClauses_)[i])[j]->append(gc);
    int numRealGndClauses = (*(*realGndClauses_)[i])[j]->size();
    for(int k = 0 ; k < numRealGndClauses ; k++)
    {
      double wt = (*(*(*realGndClauses_)[i])[j])[k]->getWt();
      (*(*(*realGndClauses_)[i])[j])[k]->setWt(wt/numRealGndClauses);
    }
  }

    // Do not delete the clause and truncClause argument.
    // This function is tightly bound to Clause::createAndAddUnknownClause().
  static void addUnknownGndClause(const AddGroundClauseStruct* const & agcs, 
                                  const Clause* const & clause,
                                  const Clause* const & truncClause,
                                  const bool& isHardClause, const Database *db)
  {
    const GroundPredicateSet* seenPreds     = agcs->seenPreds;
    GroundPredicateSet*       unseenPreds   = agcs->unseenPreds;
    GroundPredicateHashArray* gndPreds      = agcs->gndPreds;
    const Array<int>* allGndingsAreQueries  = agcs->allPredGndingsAreQueries;
    GroundClauseSet*          gndClausesSet = agcs->gndClausesSet;
    Array<GroundClause*>*     gndClauses    = agcs->gndClauses;
    const bool markHardGndClauses           = agcs->markHardGndClauses;
    const double* parentWtPtr               = agcs->parentWtPtr;
    const int clauseId                      = agcs->clauseId;

    // Check none of the grounded clause's predicates have been seen before.
    // If any of them have been seen before, this clause has been created 
    // before (for that seen predicate), and can be ignored

      // Check the untruncated ground clause whether any of its predicates
      // have been seen before
    bool seenBefore = false;
    //cout<<"seenPredsSize : "<<seenPreds->size()<<endl; //added by Happy
    for (int j = 0; j < clause->getNumPredicates(); j++)
    {
      Predicate* p = clause->getPredicate(j);
      GroundPredicate* gp = new GroundPredicate(p);
      if (seenPreds->find(gp) !=  seenPreds->end() ||
          (allGndingsAreQueries && (*allGndingsAreQueries)[gp->getId()] > 1) )
      { 
        seenBefore = true;
        delete gp;
        break;
      }
      delete gp;
    }
    //cout<<"seenBefore : "<<seenBefore<<endl; //added by Happy
    if (seenBefore) return;

    GroundClause* gndClause = new GroundClause(truncClause, gndPreds);
    if(mrfdebug)
    {
      cout<<"gndPreds size : "<<gndPreds->size()<<endl;
      cout<<"gndClause created..."<<endl;
    }
    // we don't want to add ground clause which only contains subtype predicates because that means rest of the formula was false.
    bool allPredsSubtype = true;
    for(int i = 0 ; i < gndClause->getNumGroundPredicates() ; i++)
    {
      const GroundPredicate* gp = gndClause->getGroundPredicate(i, gndPreds);
      if(gp->getPredName(db->getDomain()) != "subtype")
      {
        allPredsSubtype = false;
        break;
      }
    }
    if(allPredsSubtype)
      return;

    if(mrfdebug)
    {
      cout<<"checking for all subtype done..."<<endl;
    }
    if (markHardGndClauses && isHardClause) gndClause->setWtToHardWt();
    assert(gndClause->getWt() != 0);

    bool invertWt = false;
      // We want to normalize soft unit clauses to all be positives
    if (!isHardClause && gndClause->getNumGroundPredicates() == 1 &&
        !gndClause->getGroundPredicateSense(0))
    {
      gndClause->setGroundPredicateSense(0, true);
      gndClause->setWt(-gndClause->getWt());
      invertWt = true;
    }
    //gndClause->parentFormulaId_ = clause->parentFormulaId_; // added by Happy
    //cout<<"set parentFormulaId_ to : "<<gndClause->parentFormulaId_<<endl; // added by Happy
    GroundClauseSet::iterator iter = gndClausesSet->find(gndClause);
      // If the unknown clause is not in gndClauses
    if (iter == gndClausesSet->end())
    {
      cout<<"unknown clause is not in gndClauses..."<<endl; // added by Happy
      gndClausesSet->insert(gndClause);
      //gndClauses->append(gndClause);
      //gndClause->appendToGndPreds(gndPreds);
        // gndClause's wt is set when it was constructed
      if (parentWtPtr)
        gndClause->incrementClauseFrequency(clauseId, 1, invertWt);

        // Add the unknown predicates of the clause to unseenPreds if 
        // the predicates are already not in it
      for (int j = 0; j < gndClause->getNumGroundPredicates(); j++)
      {
        GroundPredicate* gp =
          (GroundPredicate*)gndClause->getGroundPredicate(j, gndPreds);
        assert(seenPreds->find(gp) == seenPreds->end());
          // if the ground predicate is not in unseenPreds
        GroundPredicateSet::iterator it = unseenPreds->find(gp);
        if (it == unseenPreds->end())
        {
          //cout << "\tinserting into unseen pred: ";  
          //pred->print(cout, domain); cout << endl;
          unseenPreds->insert(gp);
        }
      }
      addToRealGndClauses(clause, isHardClause, agcs);
      gndClause->jGivenI = ((*realGndClauses_)[agcs->clauseId])->size()-1;
    }
    else
    {  // gndClause has appeared before, so just accumulate its weight
      (*iter)->addWt(gndClause->getWt());
      int jGivenI = (*iter)->jGivenI;
      int i = agcs->clauseId;
      int n = (*(*realGndClauses_)[i])[jGivenI]->size();
      for(int k = 0 ; k < n ; k++)
      {
        double wt = gndClause->getWt();
        (*(*(*realGndClauses_)[i])[jGivenI])[k]->addWt(wt/n);
      }
      if (parentWtPtr)
        (*iter)->incrementClauseFrequency(clauseId, 1, invertWt);

      delete gndClause;

    }
  } //addUnknownGndClause()



  ~MRF()
  {
    for (int i = 0; i < gndClauses_->size(); i++)
      if ((*gndClauses_)[i]) delete (*gndClauses_)[i];
    delete gndClauses_;    

    for (int i = 0; i < gndPreds_->size(); i++)
      if ((*gndPreds_)[i]) delete (*gndPreds_)[i];
    delete gndPreds_;
  }

  void deleteGndPredsGndClauseSets()
  {
    for (int i = 0; i < gndPreds_->size(); i++)
      (*gndPreds_)[i]->deleteGndClauseSet();
  }  

  const GroundPredicateHashArray* getGndPreds() const { return gndPreds_; }

  const Array<GroundClause*>* getGndClauses() const { return gndClauses_; }

 private:

  void addUnknownGndClauses(const GroundPredicate* const& queryGndPred,
                            Clause* const & c, const Domain* const & domain, 
                            const Database* const & db, 
                            const bool& genClauseForAllPredGndings,
                            const AddGroundClauseStruct* const & agcs)
  {

    //cout<<"genClauseForAllPredGndings: "<<genClauseForAllPredGndings<<endl; //added by Happy
    
    if (genClauseForAllPredGndings)
      c->addUnknownClauses(domain, db, -1, NULL, agcs);
    else
    {
      for (int i = 0; i < c->getNumPredicates(); i++)
      {
        //pred is Smoke and All Terms are different Variables. hence this if conditon is satisfied //added by Noman
        if (c->getPredicate(i)->canBeGroundedAs(queryGndPred))
        {
          cout<<"c->getPredicate("<<i<<")"<<c->getPredicate(i)->getName()<<", calling addUnknownClauses..."<<endl; // added by Happy
          c->addUnknownClauses(domain, db, i, queryGndPred, agcs);
        }
      }
    }
  } 

 public:

  const int getNumGndPreds()
  {
    return gndPreds_->size();
  }

  const int getNumGndClauses()
  {
    return gndClauses_->size();
  }

 private:
  GroundPredicateHashArray* gndPreds_;
  static GroundPredicateHashArray* realGndPreds_;
  Array<GroundClause*>* gndClauses_;
  static Array<Array<Array<GroundClause*>*>*>* realGndClauses_; // If gndClause is subtype(0,A) ^ subtype(0,B) ^ (S(A)=>C(B)), which is stored as 
  // subtype(0,A) V subtype(0,B) V (S(A)=>C(B)), then this will contain all pieces of this gndClause i.e. 3 clauses : 
  // subtype(0,A), subtype(0,B), S(A)=>C(A)
  // realGndClauses[i][j][k] means kth piece of jth ground clause generated from ith first order clause.
  static Array<Array<Array<int>*>*>* reverseMap;
};


#endif
