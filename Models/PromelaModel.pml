#define MAXSEQ  3
#define SBLNUM 3
#define FREE 0 
#define DEADLINE 3   

mtype:ball = {NONE, RED, WHITE, BLUE, CONSUMED};
mtype:network = {UNITIALIZED, ONTIME, LOSS, LATE};

mtype:network net_state = UNITIALIZED; 
bool track_sublink = false;
bool r_r, r_b;    
byte a_r, a_b;  
byte l_r, l_b;   

chan sublink[SBLNUM] = [MAXSEQ+1] of {mtype:ball, byte};
chan source = [0] of {mtype:ball};
byte timeBuffer[MAXSEQ+1];


inline increaseTime(){
    atomic{
        int time;
        if
        :: time = 0;
        :: time = 1;
        :: time = 2; 
        fi
        if
        :: time > 0 ->
            for (x : 0 .. MAXSEQ) {
                if
                :: timeBuffer[x] > 0 && timeBuffer[x] < DEADLINE  -> 
                    if
                    :: (timeBuffer[x] + time) > DEADLINE -> timeBuffer[x] = DEADLINE;
                    :: else -> timeBuffer[x] = timeBuffer[x] + time;
                    fi 
                :: else -> skip;
                fi 
            }       
        :: else -> skip;
        fi
    }
}

active proctype Source()
{
    do
        :: source!WHITE
        :: source!RED ->
                break
        od
        do
        :: source!WHITE
        :: source!BLUE ->
                break
        od
        do
        :: source!WHITE
        od
}

active proctype Sender()
{
    byte seqNum, x;
    mtype:ball data;
    do
    :: source?data ->  
        atomic{
        (timeBuffer[seqNum] == FREE) ->
        timeBuffer[seqNum] = 1; 
        sublink[0]!data,seqNum;
        sublink[1]!data,seqNum;
        sublink[2]!data,seqNum;
        increaseTime();
        }
        progress: seqNum = (seqNum + 1) % (MAXSEQ + 1);   

    od
}

inline cleanBuffers(){
    if
    :: controlBuffer[recvNum] == SBLNUM ->  
        controlBuffer[recvNum] = 0;
        if
        :: (lastNum + 1) % (MAXSEQ + 1) == recvNum -> lastNum = (lastNum + 1) % (MAXSEQ + 1);
            if
            :: rcpBuffer[lastNum] != NONE && rcpBuffer[lastNum] != CONSUMED -> //printf("* Packet Waiting \n Processed *\n"); 
                    if                             
                    :: rcpBuffer[lastNum] == RED ->
                        a_r++; r_r = true; 
                    :: rcpBuffer[lastNum] == BLUE ->
                        a_b++; r_b = true; 
                    :: else -> skip;
                    fi
                    rcpBuffer[lastNum] = NONE;
            :: else -> skip;
            fi
        :: else -> skip;
        fi
        rcpBuffer[recvNum] = NONE;
        timeBuffer[recvNum] = FREE;    
    :: else -> skip;
    fi
}

active proctype Receiver()
{
    byte recvNum, recvTime, lastNum = 3;
    mtype:ball recvData;
    byte rcpBuffer[MAXSEQ+1];
    byte controlBuffer[MAXSEQ+1];

    int i;
    d_step{
        for (i : 0 .. MAXSEQ) {
            rcpBuffer[i] = NONE;
        }
    } 

    do
    ::
        atomic{

            r_r = false;  
            r_b = false; 

            if
            :: sublink[0]?recvData,recvNum -> track_sublink = true;
            :: sublink[1]?recvData,recvNum;
            :: sublink[2]?recvData,recvNum;
            fi 

            controlBuffer[recvNum]++; 
        }
            if
            ::  /* packet loss */  /* printf("LOSS\n"); */
                if
                :: track_sublink ->  net_state = LOSS;
                :: else -> skip;
                fi
            ::  
                recvTime = timeBuffer[recvNum];
                if
                :: recvTime < DEADLINE ->  
                    if                     
                    :: recvData == RED ->
                        o_r: skip; 
                    :: recvData == BLUE ->
                        o_b: skip;
                    :: else -> skip;
                    fi
                    if
                    :: rcpBuffer[recvNum] != NONE ->  /* duplicated packet */ //printf("Discard [Duplicate]\n");
                       skip;  
                    :: else ->
                        rcpBuffer[recvNum] = recvData;
                        if
                        :: (lastNum + 1) % (MAXSEQ + 1) == recvNum ->  /*printf("Accept\n");*/
                            lastNum = recvNum; 
                            if                    
                            :: recvData == RED ->
                                a_r++; r_r = true; 
                            :: recvData == BLUE ->
                                a_b++; r_b = true;
                            :: else -> skip;
                            fi  
                            rcpBuffer[recvNum] = CONSUMED;
                        :: else -> skip; /* wait to consume*/  /*printf("Accept [Waiting]\n"); */
                        fi      
                    fi
                    if
                    :: track_sublink ->  net_state = ONTIME;
                    :: else -> skip;
                    fi
                :: else -> /* packet late */        /*printf("Discard [LATE]\n");*/
                    if
                    :: recvData == RED ->
                        l_r++;  
                    :: recvData == BLUE ->
                        l_b++; 
                    :: else -> skip;
                    fi 
                    if
                    :: track_sublink -> net_state = LATE;
                    :: else -> skip;
                    fi
                fi 
            fi

            cleanBuffers();
            track_sublink = false; 
       
    od

}

// /* Correctness properties */
// ltl p1_1{ [] (l_r == SBLNUM -> [](a_r == 0)) }
// ltl p1_2{ [] (l_b == SBLNUM -> [](a_b == 0)) }                                  
// ltl p2  { [] ((a_r <= 1) && (a_b <= 1)) }
// ltl p3  { [] (r_b -> []!r_r) }
// ltl p4  { [] (((Receiver@o_r && (a_r == 0)) -> <>r_r)  && ((Receiver@o_b && (a_b == 0))-> <>r_b)) }
 
// /* Network properties */                                  
// /* Type I */
// ltl sce_good{ !( <>(net_state == UNITIALIZED && (net_state == UNITIALIZED U [](net_state == ONTIME))))}
// ltl sce_late{ !( <>(net_state == UNITIALIZED && (net_state == UNITIALIZED U [](net_state == LATE))))}
// ltl sce_loss{ !( <>(net_state == UNITIALIZED && (net_state == UNITIALIZED U [](net_state == LOSS))))}

// /* Type II */
// ltl sce_good_then_late{ !(<> (net_state == UNITIALIZED && (net_state == UNITIALIZED U (net_state == ONTIME && (net_state == ONTIME U [](net_state == LATE))))))}
// ltl sce_good_then_loss{ !(<> (net_state == UNITIALIZED && (net_state == UNITIALIZED U (net_state == ONTIME && (net_state == ONTIME U [](net_state == LOSS))))))}
// ltl sce_loss_then_good{ !(<> (net_state == UNITIALIZED && (net_state == UNITIALIZED U (net_state == LOSS && (net_state == LOSS U [](net_state == ONTIME))))))}
// ltl sce_late_then_good{ !(<> (net_state == UNITIALIZED && (net_state == UNITIALIZED U (net_state == LATE && (net_state == LATE U [](net_state == ONTIME))))))}
 
// /* Type III */
// ltl sce_good_then_late_then_good{ !(<> (net_state == UNITIALIZED && (net_state == UNITIALIZED U (net_state == ONTIME && (net_state == ONTIME U (net_state == LATE && (net_state == LATE U [](net_state == ONTIME))))))))}
// ltl sce_good_then_loss_then_good{ !(<> (net_state == UNITIALIZED && (net_state == UNITIALIZED U (net_state == ONTIME && (net_state == ONTIME U (net_state == LOSS && (net_state == LOSS U [](net_state == ONTIME))))))))}
// ltl sce_late_then_good_then_late{ !(<> (net_state == UNITIALIZED && (net_state == UNITIALIZED U (net_state == LATE && (net_state == LATE U (net_state == ONTIME && (net_state == ONTIME U [](net_state == LATE))))))))}
// ltl sce_loss_then_good_then_loss{ !(<> (net_state == UNITIALIZED && (net_state == UNITIALIZED U (net_state == LOSS && (net_state == LOSS U (net_state == ONTIME && (net_state == ONTIME U [](net_state == LOSS))))))))}

// /* Type IV */
// ltl sce_variable{ !(<> (net_state == UNITIALIZED && (net_state == UNITIALIZED U (net_state == LOSS && (net_state == LOSS U (net_state == ONTIME && (net_state == ONTIME U [](net_state == LATE))))))))}
