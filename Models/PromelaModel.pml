#define MAXSEQ  3
#define SBLNUM 2 
#define FREE 0 
#define DEADLINE 3   

bool r_r, r_b;    
byte a_r, a_b;  
byte l_r, l_b;   

mtype = {NONE, RED, WHITE, BLUE, CONSUMED};
chan sublink[SBLNUM] = [MAXSEQ+1] of { mtype, byte };
chan source = [0] of { mtype };
byte timeBuffer[MAXSEQ+1];

inline increasetime(){
    atomic{
        int time;
        if
        :: time=0;
        :: time=1;
        :: time=2; 
        fi
        if
        :: time>0 ->
            for (x : 0 .. MAXSEQ) {
                if
                :: timeBuffer[x]>0 && timeBuffer[x]<DEADLINE  ->  
                    if
                    :: (timeBuffer[x]+time)>DEADLINE -> timeBuffer[x]=DEADLINE;
                    :: else -> timeBuffer[x]=timeBuffer[x]+time;
                    fi 
                :: else;
                fi 
            }       
        :: else;
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
    mtype data;
    do
    :: source?data ->  
        atomic{
        (timeBuffer[seqNum]==FREE) ->
        timeBuffer[seqNum]=1; 
        sublink[0]!data, seqNum;  
        sublink[1]!data, seqNum;  
        increasetime();
        }

        seqNum = (seqNum +1) % (MAXSEQ+1);   

    od
}

inline cleanBuffers(){
    if
    :: controlBuffer[recvNum]== 2 ->  
        controlBuffer[recvNum]= 0;
        if
        :: else; skip;
        :: (lastNum+1)%(MAXSEQ+1)==recvNum -> lastNum=(lastNum+1)%(MAXSEQ+1);
            if
            :: rcpBuffer[lastNum]!=NONE && rcpBuffer[lastNum]!=CONSUMED -> //printf("* Packet Waiting \n Processed *\n"); 
                    if                             
                    :: rcpBuffer[lastNum] == RED ->
                        a_r++; r_r=true; skip;
                    :: rcpBuffer[lastNum] == BLUE ->
                        a_b++; r_b=true; skip;
                    :: else -> skip;
                    fi
                    rcpBuffer[lastNum]=NONE;
            :: else -> skip;
            fi
        fi
        rcpBuffer[recvNum]=NONE;
        timeBuffer[recvNum]=FREE;    
    :: else;
    fi
}

active proctype Receiver()
{
    byte recvNum, recvTime, lastNum=3;
    mtype recvData;
    byte rcpBuffer[MAXSEQ+1];
    byte controlBuffer[MAXSEQ+1];

    int i;
    d_step{
    for (i : 0 .. MAXSEQ) {
            rcpBuffer[i]=NONE;
    }
    } 

    do
    ::
        atomic{

            r_r=false;  
            r_b=false; 

            if
            :: sublink[0]?recvData,recvNum
            :: sublink[1]?recvData,recvNum  
            fi 

            controlBuffer[recvNum]++; 
        }

            if
            :: //printf("[Loss]\n"); 
               skip; /* packet loss */
            ::  
                recvTime=timeBuffer[recvNum];  
     
                if
                :: recvTime<DEADLINE ->  

                    if                     
                    :: recvData == RED ->
                        o_r: skip; 
                    :: recvData == BLUE ->
                        o_b: skip;
                    :: else -> skip;
                    fi

                    if
                    :: rcpBuffer[recvNum] != NONE ->  //printf("Discard [Duplicate]\n");
                       skip; /* duplicated packet */
                    :: else ->
                        rcpBuffer[recvNum]=recvData;
                        if
                        :: (lastNum+1)%(MAXSEQ+1)==recvNum -> //printf("Accept\n");
                            lastNum=recvNum; 
                            if                    
                            :: recvData == RED ->
                                a_r++; r_r=true; skip;
                            :: recvData == BLUE ->
                                a_b++; r_b=true; skip;
                            :: else -> skip;
                            fi  
                            rcpBuffer[recvNum]=CONSUMED;
                        :: else -> //printf("Accept [Waiting]\n"); 
                            skip; /* wait to consume*/
                        fi      
                    fi
                :: else -> //printf("Discard [Late]\n");
                     if                       //COMMENT
                    :: recvData == RED ->
                        l_r++; skip; 
                    :: recvData == BLUE ->
                        l_b++; skip;
                    :: else -> skip;
                    fi 
                fi 
            fi

            cleanBuffers();
       
    od

}

                                  
//ltl p1{ [] ( (a_r<=1) && (a_b<=1) )}

//ltl p2{ [] ( (l_r==2 -> [](a_r==0)) && (l_b==2 -> [](a_b==0)) )}

//ltl p3{ [] ( r_b -> []!r_r )}

//ltl p4{ [] ( ((Receiver@o_r && a_r==0) -> <>r_r) && ((Receiver@o_b && a_r==0)-> <>r_b) )}


 
 