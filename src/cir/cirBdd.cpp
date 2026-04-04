/****************************************************************************
  FileName     [ cirBdd.cpp ]
  PackageName  [ cir ]
  Synopsis     [ Define BDD manager functions ]
  Author       [ Design Verification Lab ]
  Copyright    [ Copyright(c) 2023-present DVLab, GIEE, NTU, Taiwan ]
****************************************************************************/

#include "bddMgrV.h"   // MODIFICATION FOR SoCV BDD
#include "bddNodeV.h"  // MODIFICATION FOR SoCV BDD
#include "cirGate.h"
#include "cirMgr.h"
#include "gvMsg.h"
#include "util.h"

#include <algorithm>
#include <unordered_map>
#include <unordered_set>

extern BddMgrV* bddMgrV;  // MODIFICATION FOR SoCV BDD

namespace gv {
namespace cir {

const bool CirMgr::setBddOrder(const BddOrderMode& mode) {
    unsigned supportSize = getNumPIs() + 2 * getNumLATCHs();
    if (supportSize >= bddMgrV->getNumSupports()) {
        gvMsg(GV_MSG_ERR) << "BDD Support Size is Smaller Than Current Design Required !!" << endl;
        return false;
    }

    const bool file = (mode == BDD_ORDER_FILE);
    vector<CirPiGate*> piOrder;
    vector<unsigned>   roLatchIdxOrder;

    if (mode == BDD_ORDER_FILE || mode == BDD_ORDER_RFILE) {
        for (unsigned i = 0, n = getNumPIs(); i < n; ++i)
            piOrder.push_back(file ? getPi(i) : getPi(n - i - 1));
        for (unsigned i = 0, n = getNumLATCHs(); i < n; ++i)
            roLatchIdxOrder.push_back(file ? i : (n - i - 1));
    } else {
        // Use _dfsList from CirMgr::genDfsList() (already called after read netlist).
        unordered_map<unsigned, unsigned> roGidToLatchIdx;
        for (unsigned i = 0, n = getNumLATCHs(); i < n; ++i)
            roGidToLatchIdx[getRo(i)->getGid()] = i;

        unordered_set<unsigned> seenPiGid;
        unordered_set<unsigned> seenRoGid;
        for (CirGate* g : _dfsList) {
            if (g->isPi()) {
                if (seenPiGid.insert(g->getGid()).second)
                    piOrder.push_back(static_cast<CirPiGate*>(g));
            } else if (g->getType() == RO_GATE) {
                unsigned gid = g->getGid();
                if (seenRoGid.insert(gid).second) {
                    auto it = roGidToLatchIdx.find(gid);
                    if (it != roGidToLatchIdx.end())
                        roLatchIdxOrder.push_back(it->second);
                }
            }
        }
        for (unsigned i = 0, n = getNumPIs(); i < n; ++i) {
            CirPiGate* p = getPi(i);
            if (!seenPiGid.count(p->getGid())) {
                seenPiGid.insert(p->getGid());
                piOrder.push_back(p);
            }
        }
        unordered_set<unsigned> seenLatchIdx(roLatchIdxOrder.begin(), roLatchIdxOrder.end());
        for (unsigned i = 0, n = getNumLATCHs(); i < n; ++i) {
            if (!seenLatchIdx.count(i)) {
                seenLatchIdx.insert(i);
                roLatchIdxOrder.push_back(i);
            }
        }
        if (mode == BDD_ORDER_RDFS) {
            reverse(piOrder.begin(), piOrder.end());
            reverse(roLatchIdxOrder.begin(), roLatchIdxOrder.end());
        }
    }

    unsigned supportId = 1;
    for (CirPiGate* gate : piOrder) {
        bddMgrV->addBddNodeV(gate->getGid(), bddMgrV->getSupport(supportId)());
        ++supportId;
    }
    for (unsigned li : roLatchIdxOrder) {
        bddMgrV->addBddNodeV(getRo(li)->getGid(), bddMgrV->getSupport(supportId)());
        ++supportId;
    }
    for (unsigned li : roLatchIdxOrder) {
        bddMgrV->addBddNodeV(getRi(li)->getName(), bddMgrV->getSupport(supportId)());
        ++supportId;
    }
    bddMgrV->addBddNodeV(_const0->getGid(), BddNodeV::_zero());
    ++supportId;

    return true;
}

void CirMgr::buildNtkBdd() {
    // TODO: build BDD for ntk here
    // Perform DFS traversal from DFF inputs, inout, and output gates.
    // Collect ordered nets to a GVNetVec
    // Construct BDDs in the DFS order

    // build PO
    for (unsigned i = 0; i < getNumPOs(); ++i) {
        buildBdd(getPo(i));
    }

    // build next state (RI)
    for (unsigned i = 0; i < getNumLATCHs(); ++i) {
        CirGate* left = getRi(i);  // get RI
        if (bddMgrV->getBddNodeV(left->getGid()) == (size_t)0) {
            buildBdd(left);
        }
    }
}

void CirMgr::buildBdd(CirGate* gate) {
    GateVec orderedGates;
    clearList(orderedGates);
    CirGate::setGlobalRef();
    gate->genDfsList(orderedGates);
    assert(orderedGates.size() <= getNumTots());

    // TODO: build BDD for the specified net here
    CirGateV left;
    CirGateV right;
    for (unsigned i = 0; i < orderedGates.size(); ++i) {
        if (orderedGates[i]->getType() == AIG_GATE) {
            // build fanin
            left             = orderedGates[i]->getIn0();
            right            = orderedGates[i]->getIn1();
            BddNodeV newNode = ((left.isInv()) ? ~bddMgrV->getBddNodeV(left.gateId())
                                               : bddMgrV->getBddNodeV(left.gateId())) &
                               ((right.isInv()) ? ~bddMgrV->getBddNodeV(right.gateId())
                                                : bddMgrV->getBddNodeV(right.gateId()));
            bddMgrV->addBddNodeV(orderedGates[i]->getGid(), newNode());
        }
        // PO, RI
        else if ((orderedGates[i]->getType() == RI_GATE) || (orderedGates[i]->getType() == PO_GATE)) {
            CirGateV in0     = orderedGates[i]->getIn0();
            BddNodeV newNode = (in0.isInv()) ? ~bddMgrV->getBddNodeV(in0.gateId()) : bddMgrV->getBddNodeV(in0.gateId());
            bddMgrV->addBddNodeV(orderedGates[i]->getGid(), newNode());
        }
    }
}

}  // namespace cir
}  // namespace gv
