
#include <limits.h>
#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <math.h>

#include "host.h"
#include "misc.h"
#include "machine.h"
#include "regs.h"
#include "memory.h"
#include "loader.h"
#include "syscall.h"
#include "dlite.h"
#include "options.h"
#include "stats.h"
#include "sim.h"
#include "decode.def"

#include "instr.h"

/* PARAMETERS OF THE TOMASULO'S ALGORITHM */

#define INSTR_QUEUE_SIZE         10

#define RESERV_INT_SIZE    4
#define RESERV_FP_SIZE     2
#define FU_INT_SIZE        2
#define FU_FP_SIZE         1

#define FU_INT_LATENCY     4
#define FU_FP_LATENCY      9

/* IDENTIFYING INSTRUCTIONS */

//unconditional branch, jump or call
#define IS_UNCOND_CTRL(op) (MD_OP_FLAGS(op) & F_CALL || \
                         MD_OP_FLAGS(op) & F_UNCOND)

//conditional branch instruction
#define IS_COND_CTRL(op) (MD_OP_FLAGS(op) & F_COND)

//floating-point computation
#define IS_FCOMP(op) (MD_OP_FLAGS(op) & F_FCOMP)

//integer computation
#define IS_ICOMP(op) (MD_OP_FLAGS(op) & F_ICOMP)

//load instruction
#define IS_LOAD(op)  (MD_OP_FLAGS(op) & F_LOAD)

//store instruction
#define IS_STORE(op) (MD_OP_FLAGS(op) & F_STORE)

//trap instruction
#define IS_TRAP(op) (MD_OP_FLAGS(op) & F_TRAP) 

#define USES_INT_FU(op) (IS_ICOMP(op) || IS_LOAD(op) || IS_STORE(op))
#define USES_FP_FU(op) (IS_FCOMP(op))

#define WRITES_CDB(op) (IS_ICOMP(op) || IS_LOAD(op) || IS_FCOMP(op))

/* FOR DEBUGGING */

//prints info about an instruction
#define PRINT_INST(out,instr,str,cycle)	\
  myfprintf(out, "%d: %s", cycle, str);		\
  md_print_insn(instr->inst, instr->pc, out); \
  myfprintf(stdout, "(%d)\n",instr->index);

#define PRINT_REG(out,reg,str,instr) \
  myfprintf(out, "reg#%d %s ", reg, str);	\
  md_print_insn(instr->inst, instr->pc, out); \
  myfprintf(stdout, "(%d)\n",instr->index);

/* VARIABLES */

//instruction queue for tomasulo
static instruction_t* instr_queue[INSTR_QUEUE_SIZE];
//number of instructions in the instruction queue
static int instr_queue_size = 0;

//reservation stations (each reservation station entry contains a pointer to an instruction)
static instruction_t* reservINT[RESERV_INT_SIZE];
static instruction_t* reservFP[RESERV_FP_SIZE];

//functional units
static instruction_t* fuINT[FU_INT_SIZE];
static instruction_t* fuFP[FU_FP_SIZE];

//common data bus
static instruction_t* commonDataBus = NULL;

//The map table keeps track of which instruction produces the value for each register
static instruction_t* map_table[MD_TOTAL_REGS];

//the index of the last instruction fetched
static int fetch_index = 0;

static int reservINTFill = 0;
static int reservFPFill = 0;

/* FUNCTIONAL UNITS */


/* RESERVATION STATIONS */


/* 
 * Description: 
 * 	Checks if simulation is done by finishing the very last instruction
 *      Remember that simulation is done only if the entire pipeline is empty
 * Inputs:
 * 	sim_insn: the total number of instructions simulated
 * Returns:
 * 	True: if simulation is finished
 */
static bool is_simulation_done(counter_t sim_insn) {

  /* ECE552: YOUR CODE GOES HERE */

  return true; //ECE552: you can change this as needed; we've added this so the code provided to you compiles
}

/* 
 * Description: 
 * 	Retires the instruction from writing to the Common Data Bus
 * Inputs:
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void CDB_To_retire(int current_cycle) {

    // Check the map table for an instruction that has written to the CDB and clear it
    
    for (int i = 0; i < MD_TOTAL_REGS; i++)
    {
        if (map_table[i]->tom_cdb_cycle < current_cycle)
        {
             map_table[i] = NULL;
        }
    }
}


/* 
 * Description: 
 * 	Moves an instruction from the execution stage to common data bus (if possible)
 * Inputs:
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void execute_To_CDB(int current_cycle) {

  /* ECE552: YOUR CODE GOES HERE */
    
    // stores, conditional/unconditional branches, jumps & calls do not write to CDB
    // no forwarding/bypassing support. values broadcasted by the CDB can be read in the next cycle
    // if 2+ instructions compete for a resource (FU, CDB), priority to older instruction (done in issue_To_execute)
    

    // Find the oldest instruction that has completed executing and write it to the CDB
    // Take the CDB data and write it back to the RS wherever it is needed

    int oldestInstrIndex = -1;
    instruction_t * oldestInstr;

    for (int i = 0; i < RESERV_INT_SIZE; i++)
    {
        if (reservINT[i]->tom_execute_cycle + FU_INT_LATENCY < current_cycle)
        {
            if (oldestInstrIndex == -1 || reservINT[i]->index < oldestInstrIndex)
            {
                oldestInstrIndex = reservINT[i]->index;
                oldestInstr = reservINT[i];
            }
        }
    }
    
    for (int i = 0; i < RESERV_FP_SIZE; i++)
    {
        if (reservFP[i]->tom_execute_cycle + FU_FP_LATENCY < current_cycle)
        {
            if (oldestInstrIndex == -1 || reservFP[i]->index < oldestInstrIndex)
            {
                oldestInstrIndex = reservFP[i]->index;
                oldestInstr = reservFP[i];
            }
        }
    }
    
    // Nothing has completed executing this cycle
    if (oldestInstrIndex == -1)
    {
        return;
    }
    
    oldestInstr->tom_cdb_cycle = current_cycle;
    commonDataBus = oldestInstr;
    
    // We should have the oldest completed instruction index in oldestInstrIndex
    // We need to clear the functional unit this came from
    
    for (int i = 0; i < RESERV_INT_SIZE; i++)
    {
        if (commonDataBus->index == reservINT[i]->index) reservINT[i] = NULL;
    }
    for (int i = 0; i < RESERV_FP_SIZE; i++)
    {
        if (commonDataBus->index == reservFP[i]->index) reservFP[i] = NULL;
    }
    for (int i = 0; i < FU_INT_SIZE; i++)
    {
        if (commonDataBus->index == fuINT[i]->index) fuINT[i] = NULL;
    }
    for (int i = 0; i < FU_FP_SIZE; i++)
    {
        if (commonDataBus->index == fuFP[i]->index) fuFP[i] = NULL;
    }
    
    // Now we broadcast to all other instructions waiting on us
    
    for (int i = 0; i < RESERV_INT_SIZE; i++)
    {
        for (int j = 0; j < 3; j++)
        {
            if (reservINT[i]->Q[j]->index == commonDataBus->index)
            {
                reservINT[i]->Q[j] = NULL;
            }
        }
    }
    
    for (int i = 0; i < RESERV_FP_SIZE; i++)
    {
        for (int j = 0; j < 3; j++)
        {
            if (reservFP[i]->Q[j]->index == commonDataBus->index)
            {
                reservFP[i]->Q[j] = NULL;
            }
        }
    }
}

/* 
 * Description: 
 * 	Moves instruction(s) from the issue to the execute stage (if possible). We prioritize old instructions
 *      (in program order) over new ones, if they both contend for the same functional unit.
 *      All RAW dependences need to have been resolved with stalls before an instruction enters execute.
 * Inputs:
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void issue_To_execute(int current_cycle) {

    /* ECE552 Assignment 3 - BEGIN CODE */
    
    int oldestInstructionValue = 9999;
    int oldestInstructionIndex = 0;
    
    // prioritize old instructions over new instructions from dispatch (if more than 1 ready to execute)
    // execute in the functional unit which matches its reservation station
    // ignore dependences over memory accesses (loads/stores do not have to wait for each other if they access the same address)
    // remain in reservation station until execute completed
    // multiple instructions can enter the execute stage in the same cycle
    
    // given an open FP/INT FU, go through the FP/INT reservation stations and look for any instructions that are ready to execute
    // to be ready to execute, it must
    // - have no RAW dependencies in input registers (check Q array in the instruction. if all NULL then no RAW dependencies)
    // functional units/execution is given priority to older instructions
    
    for (int i = 0; i < FU_FP_SIZE; i++)
    {
        // available FP FU
        if (fuFP[i] == NULL)
        {
            // iterate through FP reservation stations to look for an instruction ready to execute
            for (int j = 0; j < reservFPFill; j++)
            {
                // check for any RAW dependencies
                if (reservFP[j]->Q[0] == NULL && reservFP[j]->Q[1] == NULL && reservFP[j]->Q[2] == NULL)
                {
                    // check if it is the oldest current instruction. if so, update
                    if (reservFP[j]->index < oldestInstructionValue)
                    {
                        oldestInstructionValue = reservFP[j]->index;
                        oldestInstructionIndex = j;
                    }
                }
            }
            
            // once finished iterating through FP reservation stations, select the oldest instruction and place it into the FU for execution (if we found a ready instruction)
            if (oldestInstructionValue != 9999)
            {
                reservFP[oldestInstructionIndex]->tom_execute_cycle = current_cycle;
                fuFP[i] = reservFP[oldestInstructionIndex];      
                oldestInstructionValue = 9999;
                oldestInstructionIndex = 0;
            }
        }
    }
    
    oldestInstructionValue = 9999;
    oldestInstructionIndex = 0;
    
    for (int i = 0; i < FU_INT_SIZE; i++)
    {
        // available INT FU
        if (fuINT[i] == NULL)
        {
            // iterate through INT reservation stations to look for an instruction ready to execute
            for (int j = 0; j < reservINTFill; j++)
            {
                // check for any RAW dependencies
                if (reservINT[j]->Q[0] == NULL && reservINT[j]->Q[1] == NULL && reservINT[j]->Q[2] == NULL)
                {
                    // check if it is the oldest current instruction. if so, update
                    if (reservINT[j]->index < oldestInstructionValue)
                    {
                        oldestInstructionValue = reservINT[j]->index;
                        oldestInstructionIndex = j;
                    }
                }
            }
            
            // once finished iterating through INT reservation stations, select the oldest instruction and place it into the FU for execution (if we found a ready instruction)
            if (oldestInstructionValue != 9999)
            {
                reservFP[oldestInstructionIndex]->tom_execute_cycle = current_cycle;
                fuINT[i] = reservFP[oldestInstructionIndex];
                oldestInstructionValue = 9999;
                oldestInstructionIndex = 0;
            }
        }
    }
    
    return;
    
    /* ECE552 Assignment 3 - BEGIN CODE */
}

/* 
 * Description: 
 * 	Moves instruction(s) from the dispatch stage to the issue stage
 * Inputs:
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void dispatch_To_issue(int current_cycle) {

    /* ECE552 Assignment 3 - BEGIN CODE */
      
    // check if a reservation station is available
    // if not, stall
    
    // allocate a reservation station entry based on the instructions opcode
    // - do not issue a reservation station for an unconditional branch
    // - handle conditional branches the same way as unconditional branches
    // - load/stores use integer FU and their respective reservation stations
    // mark any RAW dependencies in the reservation entry
    
    // if there is RAW hazard, stall
    
    // we are only moving 1 instruction (oldest) to issue
    
    int input_reg = 3;
    int output_reg = 2;
    
    // instruction requires a floating reservation station
    if (IS_FCOMP(instr_queue[0]->op))
    {
        // check that a floating reservation station is available
        if (reservFPFill == 4)
            // no floating reservation station available. stall
            return;
        else
        {
            // reservation station available for our fp instruction
            // start adding the instruction and its information into the reservation station
            reservFP[reservFPFill] = instr_queue[0];
            reservFP[reservFPFill]->tom_issue_cycle = current_cycle;
            
            // check for RAW dependencies in the input registers
            for (int i = 0; i < input_reg; i++)
            {
                // if input register exists, check the map table to see if available
                // place the map table value into the Q array which contain the results of the input registers it needs to wait for
                if (reservFP[reservFPFill]->r_in[i] != DNA)
                    reservFP[reservFPFill]->Q[i] = map_table[reservFP[reservFPFill]->r_in[i]];
            }
            
            // add output registers to map table for other instructions
            for (int i = 0; i < output_reg; i++)
            {
                // if output register exists, set the map table value such that the result comes from that reservation station
                if (reservFP[reservFPFill]->r_out[i] != DNA)
                    map_table[reservFP[reservFPFill]->r_out[i]] = reservFP[reservFPFill];
            }
            
            // update instruction queue
            // remove first instruction from queue and move all other instructions in queue
            for (int i = 0; i < INSTR_QUEUE_SIZE - 1; i++)
            {
               instr_queue[i] = instr_queue[i+1];
            }
        
            // erase the last instruction in the queue since all instructions moved up one
            instr_queue[INSTR_QUEUE_SIZE - 1] = NULL;
            instr_queue_size--;
            
            // update free spots in FP reservation stations
            reservFPFill++;
            return;
        }
    }

    // instruction requires an integer reservation station (this includes loads and stores as well)
    if (IS_ICOMP(instr_queue[0]->op) || IS_LOAD(instr_queue[0]->op) || IS_STORE(instr_queue[0]->op))
    {
        // check that an integer reservation station is available
        if (reservINTFill == 4)
            // no integer reservation station available. stall
            return;
        else
        {
            // reservation station available for our int instruction
            // start adding the instruction and its information into the reservation station
            reservINT[reservINTFill] = instr_queue[0];
            reservINT[reservINTFill]->tom_issue_cycle = current_cycle;
            
            // check for RAW dependencies in the input registers
            for (int i = 0; i < input_reg; i++)
            {
                // if input register exists, check the map table to see if available
                // place the map table value into the Q array which contain the results of the input registers it needs to wait for
                if (reservINT[reservINTFill]->r_in[i] != DNA)
                    reservINT[reservINTFill]->Q[i] = map_table[reservINT[reservINTFill]->r_in[i]];
            }
            
            // add output registers to map table for other instructions
            for (int i = 0; i < output_reg; i++)
            {
                // if output register exists, set the map table value such that the result comes from that reservation station
                if (reservINT[reservINTFill]->r_out[i] != DNA)
                    map_table[reservINT[reservINTFill]->r_out[i]] = reservINT[reservINTFill];
            }
            
            // update instruction queue
            // remove first instruction from queue and move all other instructions in queue
            for (int i = 0; i < INSTR_QUEUE_SIZE - 1; i++)
            {
               instr_queue[i] = instr_queue[i+1];
            }
        
            // erase the last instruction in the queue since all instructions moved up one
            instr_queue[INSTR_QUEUE_SIZE - 1] = NULL;
            instr_queue_size--;
            
            // update free spots in integer reservation stations
            reservINTFill++;
            return;
        }
    }
    
    // instruction does not require a reservation station. send to issue immediately
    if (IS_UNCOND_CTRL(instr_queue[0]->op) || IS_COND_CTRL(instr_queue[0]->op))
    {    
        instr_queue[0]->tom_issue_cycle = current_cycle;
        
        // remove first instruction from queue and move all other instructions in queue
        for (int i = 0; i < INSTR_QUEUE_SIZE - 1; i++)
        {
            instr_queue[i] = instr_queue[i+1];
        }
        
        // erase the last instruction in the queue since all instructions moved up one
        instr_queue[INSTR_QUEUE_SIZE - 1] = NULL;
        instr_queue_size--;
        
        return;
    }  
    
    /* ECE552 Assignment 3 - END CODE */
}

/* 
 * Description: 
 * 	Grabs an instruction from the instruction trace (if possible)
 * Inputs:
 *      trace: instruction trace with all the instructions executed
 * Returns:
 * 	None
 */
void fetch(instruction_trace_t* trace) {

    /* ECE552 Assignment 3 - BEGIN CODE */
    
    // attempt to grab an instruction from the instruction trace
    // if the instruction is a trap instruction, skip (do not insert into IFQ)
    // otherwise, insert into IFQ in program-order (FIFO essentially)
    
    // first check that there's space in the IFQ
    if (instr_queue_size < INSTR_QUEUE_SIZE)
    {
        // trace starts at instruction 1, not instruction 0
        // therefore increment fetch_index before grabbing instruction
        fetch_index++;
        
        // grab the next instruction in the trace
        instruction_t *inst = get_instr(trace, fetch_index);
        
        // if the inst is empty, trace is complete
        if (inst == NULL)
            return;
        // if the inst is a trap inst, rerun fetch to grab the next inst
        else if (IS_TRAP(inst->op))
        {
            fetch(trace);
            return;
        }
        else
        {
            // initialize values in the instruction_t data structure
            inst->Q[0] = NULL;
            inst->Q[1] = NULL;
            inst->Q[2] = NULL;
            
            inst->tom_cdb_cycle = 0;
            inst->tom_dispatch_cycle = 0;
            inst->tom_execute_cycle = 0;
            inst->tom_issue_cycle = 0;
            
            // add instruction to IFQ
            // fetch completed at this point
            instr_queue[instr_queue_size] = inst;
            instr_queue_size++;
            return;
        }
    }
    
    //no space in the IFQ, stall
    return;
    
    /* ECE552 Assignment 3 - END CODE */
}

/* 
 * Description: 
 * 	Calls fetch and dispatches an instruction at the same cycle (if possible)
 * Inputs:
 *      trace: instruction trace with all the instructions executed
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void fetch_To_dispatch(instruction_trace_t* trace, int current_cycle) {

    fetch(trace);

    /* ECE552 Assignment 3 - BEGIN CODE */
  
    // check if there is an instruction in the IFQ
    if (instr_queue_size == 0)
        return;

    // send instructions to dispatch after being fetched
    for (int i = 0; i < instr_queue_size; i++)
    {
        if (instr_queue[i]->tom_dispatch_cycle == 0)
            instr_queue[i]->tom_dispatch_cycle = current_cycle;
    }
  
    return;
    
    /* ECE552 Assignment 3 - END CODE */
}

/* 
 * Description: 
 * 	Performs a cycle-by-cycle simulation of the 4-stage pipeline
 * Inputs:
 *      trace: instruction trace with all the instructions executed
 * Returns:
 * 	The total number of cycles it takes to execute the instructions.
 * Extra Notes:
 * 	sim_num_insn: the number of instructions in the trace
 */
counter_t runTomasulo(instruction_trace_t* trace)
{
  //initialize instruction queue
  int i;
  for (i = 0; i < INSTR_QUEUE_SIZE; i++) {
    instr_queue[i] = NULL;
  }

  //initialize reservation stations
  for (i = 0; i < RESERV_INT_SIZE; i++) {
      reservINT[i] = NULL;
  }

  for(i = 0; i < RESERV_FP_SIZE; i++) {
      reservFP[i] = NULL;
  }

  //initialize functional units
  for (i = 0; i < FU_INT_SIZE; i++) {
    fuINT[i] = NULL;
  }

  for (i = 0; i < FU_FP_SIZE; i++) {
    fuFP[i] = NULL;
  }

  //initialize map_table to no producers
  int reg;
  for (reg = 0; reg < MD_TOTAL_REGS; reg++) {
    map_table[reg] = NULL;
  }
  
  int cycle = 1;
  while (true) {

     /* ECE552: YOUR CODE GOES HERE */

     cycle++;

     if (is_simulation_done(sim_num_insn))
        break;
  }
  
  return cycle;
}
