
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

    /* ECE552 Assignment 3 - BEGIN CODE */
    
    // check if the fetch index is greater than or equal to the total number of instructions simulated
    // then confirm that all our structures are empty. if anything exists in a structure then we aren't done
    
    if (fetch_index >= sim_insn - 1)
    {
        // check the instruction queue
        if (instr_queue_size > 0)
        {
            printf("false 1\n");
            return false;
        }
        
        // check the reservation stations and the functional units
        for (int i = 0; i < RESERV_FP_SIZE; i++)
        {
            if (reservFP[i] != NULL)
            {
                printf("false 2\n");
                return false;
            }
        }
        
        for (int i = 0; i < RESERV_INT_SIZE; i++)
        {
            if (reservINT[i] != NULL)
            {
                printf("false 3\n");
                return false;
            }
        }
        
        for (int i = 0; i < FU_FP_SIZE; i++)
        {
            if (fuFP[i] != NULL)
            {
                printf("false 4\n");
                return false;
            }
        }
        
        for (int i = 0; i < FU_INT_SIZE; i++)
        {
            if (fuFP[i] != NULL)
            {
                printf("false 5\n");
                return false;
            }
        }
        
        // check that the CDB is clear
        if (commonDataBus != NULL)
        {
            printf("false 6\n");
            return false;
        }
        
        // at this point, everything is cleared and we are finished
        return true;
    }
    else
    {
        //printf("false 7\n");
        return false;
    }

  //return true; //ECE552: you can change this as needed; we've added this so the code provided to you compiles
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

    /* ECE552 Assignment 3 - BEGIN CODE */
    
    // Check the map table for an instruction that has written to the CDB and clear it
    
    for (int i = 0; i < MD_TOTAL_REGS; i++)
    {
        if (map_table[i] != NULL && map_table[i]->tom_cdb_cycle < current_cycle)
        {
             map_table[i] = NULL;
        }
    }
    
    // Now we broadcast to all other instructions waiting on us
    
    for (int i = 0; i < RESERV_INT_SIZE; i++)
    {
        if (reservINT[i] != NULL)
        {
            for (int j = 0; j < 3; j++)
            {
                if (reservINT[i]->Q[j] != NULL)
                {
                    if (reservINT[i]->Q[j]->index == commonDataBus->index)
                    {
                        reservINT[i]->Q[j] = NULL;
                    }
                }
            }
        }
    }
    
    for (int i = 0; i < RESERV_FP_SIZE; i++)
    {
        if (reservFP[i] != NULL)
        {
            for (int j = 0; j < 3; j++)
            {
                if (reservFP[i]->Q[j] != NULL)
                {
                    if (reservFP[i]->Q[j]->index == commonDataBus->index)
                    {
                        reservFP[i]->Q[j] = NULL;
                    }
                }
            }
        }
    }
    
    /* ECE552 Assignment 3 - END CODE */
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

    /* ECE552 Assignment 3 - BEGIN CODE */
    
    // stores, conditional/unconditional branches, jumps & calls do not write to CDB
    // no forwarding/bypassing support. values broadcasted by the CDB can be read in the next cycle
    // if 2+ instructions compete for a resource (FU, CDB), priority to older instruction (done in issue_To_execute)
    

    // Find the oldest instruction that has completed executing and write it to the CDB
    // Take the CDB data and write it back to the RS wherever it is needed

    int oldestInstrIndex = -1;
    instruction_t * oldestInstr;

    for (int i = 0; i < FU_INT_SIZE; i++)
    {
        if (fuINT[i] != NULL && fuINT[i]->tom_execute_cycle + FU_INT_LATENCY <= current_cycle && fuINT[i]->tom_execute_cycle != 0)
        {
            if (WRITES_CDB(fuINT[i]->op))
            {
                if (oldestInstrIndex == -1 || fuINT[i]->index < oldestInstrIndex)
                {
                    oldestInstrIndex = fuINT[i]->index;
                    oldestInstr = fuINT[i];
                }
            }
            else
            {
                // if instruction does not write to CDB, we still have to clear the reservation station and FU that the instruction occupied
                for (int j = 0; j < RESERV_INT_SIZE; j++)
                {
                    if (reservINT[j] != NULL && fuINT[i]->index == reservINT[j]->index)
                        reservINT[j] = NULL;
                }
                fuINT[i] = NULL;
            }
        }
    }
    
    for (int i = 0; i < FU_FP_SIZE; i++)
    {
        if (fuFP[i] != NULL && fuFP[i]->tom_execute_cycle + FU_FP_LATENCY <= current_cycle && fuFP[i]->tom_execute_cycle != 0)
        {
            if (WRITES_CDB(fuFP[i]->op))
            {
                if (oldestInstrIndex == -1 || fuFP[i]->index < oldestInstrIndex)
                {
                    oldestInstrIndex = fuFP[i]->index;
                    oldestInstr = fuFP[i];
                }
            }
            else
            {
                // if instruction does not write to CDB, we still have to clear the reservation station and FU that the instruction occupied
                for (int j = 0; j < RESERV_FP_SIZE; j++)
                {
                    if (reservFP[j] != NULL && fuFP[i]->index == reservFP[j]->index)
                        reservFP[j] = NULL;
                }
                fuFP[i] = NULL;
            }
        }
    }
    
    // Nothing that writes to the CDB has completed executing this cycle
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
        if (reservINT[i] != NULL && commonDataBus->index == reservINT[i]->index)
        {
            printf("Integer reservation station %d is availabe. Current cycle is %d.\n", i, current_cycle);
            reservINT[i] = NULL;
        }
    }
    for (int i = 0; i < RESERV_FP_SIZE; i++)
    {
        if (reservFP[i] != NULL && commonDataBus->index == reservFP[i]->index) reservFP[i] = NULL;
    }
    for (int i = 0; i < FU_INT_SIZE; i++)
    {
        if (fuINT[i] != NULL && commonDataBus->index == fuINT[i]->index)
        {
            printf("Integer FU %d is availabe. Current cycle is %d.\n", i, current_cycle);
            fuINT[i] = NULL;
        }
    }
    for (int i = 0; i < FU_FP_SIZE; i++)
    {
        if (fuFP[i] != NULL && commonDataBus->index == fuFP[i]->index) fuFP[i] = NULL;
    }
    
    /* ECE552 Assignment 3 - END CODE */
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
    instruction_t *oldestInstruction = NULL;
    
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
            for (int j = 0; j < RESERV_FP_SIZE; j++)
            {
                if (reservFP[j] != NULL)
                {
                    // check for any RAW dependencies
                    if (reservFP[j]->Q[0] == NULL && reservFP[j]->Q[1] == NULL && reservFP[j]->Q[2] == NULL && reservFP[j]->tom_execute_cycle == 0)
                    {
                        // check if it is the oldest current instruction. if so, update
                        if (reservFP[j]->index < oldestInstructionValue)
                        {
                            oldestInstruction = reservFP[j];
                            oldestInstructionValue = reservFP[j]->index;
                        }
                    }
                }
            }
            
            // once finished iterating through FP reservation stations, select the oldest instruction and place it into the FU for execution (if we found a ready instruction)
            if (oldestInstruction != NULL)
            {
                oldestInstruction->tom_execute_cycle = current_cycle;
                fuFP[i] = oldestInstruction;    
                printf("Instruction using fp FU %d.\n", i);
                oldestInstructionValue = 9999;
                oldestInstruction = NULL;
            }
        }
        else
            printf("All fp FU used. Current cycle is %d.\n", current_cycle);
    }
    
    for (int i = 0; i < FU_INT_SIZE; i++)
    {
        // available INT FU
        if (fuINT[i] == NULL)
        {
            // iterate through INT reservation stations to look for an instruction ready to execute
            for (int j = 0; j < RESERV_INT_SIZE; j++)
            {
                if (reservINT[j] != NULL)
                {
                    // check for any RAW dependencies
                    if (reservINT[j]->Q[0] == NULL && reservINT[j]->Q[1] == NULL && reservINT[j]->Q[2] == NULL && reservINT[j]->tom_execute_cycle == 0)
                    {
                        // check if it is the oldest current instruction. if so, update
                        if (reservINT[j]->index < oldestInstructionValue)
                        {
                            oldestInstruction = reservINT[j];
                            oldestInstructionValue = reservINT[j]->index;
                        }
                    }
                }
            }
            
            // once finished iterating through INT reservation stations, select the oldest instruction and place it into the FU for execution (if we found a ready instruction)
            if (oldestInstruction != NULL)
            {
                oldestInstruction->tom_execute_cycle = current_cycle;
                fuINT[i] = oldestInstruction;
                printf("Instruction using integer FU %d.\n", i);
                oldestInstructionValue = 9999;
                oldestInstruction = NULL;
            }
        }
        else
            printf("All integer FU used. Current cycle is %d.\n", current_cycle);
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
    
    // no instructions in IFQ, stall
    if (instr_queue_size == 0)
        return;
    
    // instruction requires a floating reservation station
    if (IS_FCOMP(instr_queue[0]->op))
    {
        for (int j = 0; j < RESERV_FP_SIZE; j++)
        {
            if (reservFP[j] == NULL)
            {
                // reservation station available for our fp instruction
                // start adding the instruction and its information into the reservation station
                reservFP[j] = instr_queue[0];
                printf("Instruction using fp reservation station %d.\n", j);
                reservFP[j]->tom_issue_cycle = current_cycle;

                // check for RAW dependencies in the input registers
                for (int i = 0; i < input_reg; i++)
                {
                    // if input register exists, check the map table to see if available
                    // place the map table value into the Q array which contain the results of the input registers it needs to wait for
                    if (reservFP[j]->r_in[i] != DNA)
                        reservFP[j]->Q[i] = map_table[reservFP[j]->r_in[i]];
                }

                // add output registers to map table for other instructions
                for (int i = 0; i < output_reg; i++)
                {
                    // if output register exists, set the map table value such that the result comes from that reservation station
                    if (reservFP[j]->r_out[i] != DNA)
                        map_table[reservFP[j]->r_out[i]] = reservFP[j];
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
                printf("decreasing instruction queue by 1. Instruction queue size: %d.\n", instr_queue_size);

                return;
            }
        }
    }

    // instruction requires an integer reservation station (this includes loads and stores as well)
    if (IS_ICOMP(instr_queue[0]->op) || IS_LOAD(instr_queue[0]->op) || IS_STORE(instr_queue[0]->op))
    {
        for (int j = 0; j < RESERV_INT_SIZE; j++)
        {
            if (reservINT[j] == NULL)
            {
                // reservation station available for our int instruction
                // start adding the instruction and its information into the reservation station
                reservINT[j] = instr_queue[0];
                printf("Instruction using integer reservation station %d.\n", j);
                reservINT[j]->tom_issue_cycle = current_cycle;

                // check for RAW dependencies in the input registers
                for (int i = 0; i < input_reg; i++)
                {
                    // if input register exists, check the map table to see if available
                    // place the map table value into the Q array which contain the results of the input registers it needs to wait for
                    if (reservINT[j]->r_in[i] != DNA)
                        reservINT[j]->Q[i] = map_table[reservINT[j]->r_in[i]];
                }

                // add output registers to map table for other instructions
                for (int i = 0; i < output_reg; i++)
                {
                    // if output register exists, set the map table value such that the result comes from that reservation station
                    if (reservINT[j]->r_out[i] != DNA)
                        map_table[reservINT[j]->r_out[i]] = reservINT[j];
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
                printf("decreasing instruction queue by 1. Instruction queue size: %d.\n", instr_queue_size);
                
                return;
            }
        }
    }
    
    // instruction does not require a reservation station. send to issue immediately
    if (IS_UNCOND_CTRL(instr_queue[0]->op) || IS_COND_CTRL(instr_queue[0]->op))
    {    
        // remove first instruction from queue and move all other instructions in queue
        for (int i = 0; i < INSTR_QUEUE_SIZE - 1; i++)
        {
            instr_queue[i] = instr_queue[i+1];
        }
        
        // erase the last instruction in the queue since all instructions moved up one
        instr_queue[INSTR_QUEUE_SIZE - 1] = NULL;
        instr_queue_size--;
        printf("decreasing instruction queue by 1. Instruction queue size: %d.\n", instr_queue_size);
        
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
            printf("Increasing instruction queue size by 1. Instruction queue size: %d. Fetch index is %d.\n", instr_queue_size, fetch_index);
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
  int loopCounter = 0;
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

     /* ECE552 Assignment 3 - BEGIN CODE */
     
     // run the created functions in reverse order, so retiring CDB comes first and fetching comes last
     CDB_To_retire(cycle);
     execute_To_CDB(cycle);
     issue_To_execute(cycle);
     dispatch_To_issue(cycle);
     fetch_To_dispatch(trace, cycle);
     loopCounter++;
     //printf("loop counter is %d\n", loopCounter); 
     //printf("fetch index is %d\n", fetch_index);
     /* ECE552 Assignment 3 - END CODE */ 
     
     cycle++;

     if (is_simulation_done(sim_num_insn))
     {
        //printf("done\n");
        break;
     }
  }
  
  return cycle;
}
