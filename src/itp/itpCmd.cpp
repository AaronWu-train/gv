/****************************************************************************
  FileName     [ satCmd.cpp ]
  PackageName  [ sat ]
  Synopsis     [ Define basic sat prove package commands ]
  Author       [ ]
  Copyright    [ Copyright(c) 2023-present DVLab, GIEE, NTU, Taiwan ]
 ****************************************************************************/

#include "itpCmd.h"

#include <cstring>
#include <iomanip>

#include "cirGate.h"
#include "cirMgr.h"
#include "gvMsg.h"
#include "itpMgr.h"
#include "minisatMgr.h"
#include "util.h"
using namespace std;

using namespace gv::cir;

static gv::itp::ItpMgr* itpMgr = new gv::itp::ItpMgr();

bool initItpCmd() {
    return (gvCmdMgr->regCmd("SATVerify ITP", 4, 3, new SATVerifyItpCmd) &&
            gvCmdMgr->regCmd("SATVerify BMC", 4, 3, new SATVerifyBmcCmd));
}

//----------------------------------------------------------------------
//    SATVerify ITP < -GateId <gateId> | -Output <outputIndex> > >
//----------------------------------------------------------------------
GVCmdExecStatus
SATVerifyItpCmd::exec(const string& option) {
    vector<string> options;
    GVCmdExec::lexOptions(option, options);

    if (options.size() < 2) return GVCmdExec::errorOption(GV_CMD_OPT_MISSING, "");
    if (options.size() > 2) return GVCmdExec::errorOption(GV_CMD_OPT_EXTRA, options[2]);

    bool isNet = false;

    if (myStrNCmp("-GateId", options[0], 2) == 0)
        isNet = true;
    else if (myStrNCmp("-Output", options[0], 2) == 0)
        isNet = false;
    else
        return GVCmdExec::errorOption(GV_CMD_OPT_ILLEGAL, options[0]);

    int num = 0;
    CirGate* gate;
    string monitorName = "";
    if (!myStr2Int(options[1], num) || (num < 0)) return GVCmdExec::errorOption(GV_CMD_OPT_ILLEGAL, options[1]);
    if (isNet) {
        if ((unsigned)num >= cirMgr->getNumTots()) {
            gvMsg(GV_MSG_ERR) << "Net with Id " << num << " does NOT Exist in Current Ntk !!" << endl;
            return GVCmdExec::errorOption(GV_CMD_OPT_ILLEGAL, options[1]);
        }
        gate = cirMgr->getGate(num);
    } else {
        if ((unsigned)num >= cirMgr->getNumPOs()) {
            gvMsg(GV_MSG_ERR) << "Output with Index " << num << " does NOT Exist in Current Ntk !!" << endl;
            return GVCmdExec::errorOption(GV_CMD_OPT_ILLEGAL, options[1]);
        }
        gate        = cirMgr->getPo(num);
        monitorName = gate->getName();
    }
    // get PO's input, since the PO is actually a redundant node and should be removed
    CirGate* monitor = new CirAigGate(cirMgr->getNumTots(), 0);
    cirMgr->addTotGate(monitor);
    monitor->setIn0(gate->getIn0Gate(), gate->getIn0().isInv());
    monitor->setIn1(cirMgr->_const1, false);
    itpMgr->verifyPropertyItp(monitorName, monitor);

    return GV_CMD_EXEC_DONE;
}

void SATVerifyItpCmd::usage(const bool& verbose) const {
    cout << "Usage: SATVerify ITP < -GateId <gateId> | -Output <outputIndex> >" << endl;
}

void SATVerifyItpCmd::help() const {
    cout << setw(20) << left << "SATVerify ITP:"
         << "check the monitor by interpolation-based technique" << endl;
}

// //----------------------------------------------------------------------
// //    SATVerify BMC < -GateId <gateId> | -Output <outputIndex> > >
// //----------------------------------------------------------------------
GVCmdExecStatus
SATVerifyBmcCmd::exec(const string& option) {
    vector<string> options;
    GVCmdExec::lexOptions(option, options);

    if (options.size() < 2) return GVCmdExec::errorOption(GV_CMD_OPT_MISSING, "");

    bool isNet = false;

    if (myStrNCmp("-GateId", options[0], 2) == 0)
        isNet = true;
    else if (myStrNCmp("-Output", options[0], 2) == 0)
        isNet = false;
    else
        return GVCmdExec::errorOption(GV_CMD_OPT_ILLEGAL, options[0]);

    int num = 0;
    CirGate* gate;
    string monitorName = "";
    if (!myStr2Int(options[1], num) || (num < 0)) return GVCmdExec::errorOption(GV_CMD_OPT_ILLEGAL, options[1]);
    if (isNet) {
        if ((unsigned)num >= cirMgr->getNumTots()) {
            gvMsg(GV_MSG_ERR) << "Gate with Id " << num << " does NOT Exist in Current Cir !!" << endl;
            return GVCmdExec::errorOption(GV_CMD_OPT_ILLEGAL, options[1]);
        }
        gate = cirMgr->getGate(num);
    } else {
        if ((unsigned)num >= cirMgr->getNumPOs()) {
            gvMsg(GV_MSG_ERR) << "Output with Index " << num << " does NOT Exist in Current Cir !!" << endl;
            return GVCmdExec::errorOption(GV_CMD_OPT_ILLEGAL, options[1]);
        }
        gate        = cirMgr->getPo(num);
        monitorName = gate->getName();
    }

    vector<int> decOrder;
    int         satVerbosity = 0;
    for (size_t i = 2; i < options.size();) {
        if (myStrNCmp("-DecOrder", options[i], 4) == 0) {
            ++i;
            while (i < options.size() && options[i].size() && options[i][0] != '-') {
                int v = 0;
                if (!myStr2Int(options[i], v) || v < 0)
                    return GVCmdExec::errorOption(GV_CMD_OPT_ILLEGAL, options[i]);
                decOrder.push_back(v);
                ++i;
            }
        } else if (myStrNCmp("-SatVerbose", options[i], 4) == 0) {
            if (i + 1 >= options.size()) return GVCmdExec::errorOption(GV_CMD_OPT_MISSING, "");
            if (!myStr2Int(options[i + 1], satVerbosity) || satVerbosity < 0)
                return GVCmdExec::errorOption(GV_CMD_OPT_ILLEGAL, options[i + 1]);
            i += 2;
        } else
            return GVCmdExec::errorOption(GV_CMD_OPT_ILLEGAL, options[i]);
    }

    CirGate* monitor = gate;
    if (!isNet) {
        monitor = new CirAigGate(cirMgr->getNumTots(), 0);
        cirMgr->addTotGate(monitor);
        monitor->setIn0(gate->getIn0Gate(), gate->getIn0().isInv());
        monitor->setIn1(cirMgr->_const1, false);
    }

    itpMgr->verifyPropertyBmc(monitorName, monitor, decOrder, satVerbosity);

    return GV_CMD_EXEC_DONE;
}

void SATVerifyBmcCmd::usage(const bool& verbose) const {
    cout << "Usage: SATVerify BMC < -GateId <gateId> | -Output <outputIndex> > [-DecOrder <Var> ...] [-SatVerbose <0|1>]" << endl;
}

void SATVerifyBmcCmd::help() const {
    cout << setw(20) << left << "SATVerify BMC:"
         << "bounded model checking; optional MiniSAT branch order (-DecOrder uses internal Var ids)"
         << endl;
}
