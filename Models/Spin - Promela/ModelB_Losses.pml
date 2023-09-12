#define MaxSeq  3
#define MaxSublinks 2 
#define FREE 0 
#define DEADLINE 3  
#define inc(x)  x = (x+1)%(MaxSeq+1)

//bool rr, rb   // FOR VERIFICATION
//byte nr, nb   // FOR VERIFICATION
//byte nlr,nlb  // FOR VERIFICATION

mtype = { none, red, white, blue, consumed}  
chan sublink[MaxSublinks] = [MaxSeq+1] of { mtype, byte }
chan source = [0] of { mtype }
byte timebuffer[MaxSeq+1];

inline increasetime(){
    atomic{
    int time;

    if
    :: time = 0;
    :: time = 1;
    :: time = 2; 
    fi

    if
    :: time>0 ->
        for (x : 0 .. MaxSeq) {
            if
            :: timebuffer[x]>0 && timebuffer[x]<DEADLINE  ->  
                if
                :: (timebuffer[x]+time)>DEADLINE -> timebuffer[x] = DEADLINE;
                :: else -> timebuffer[x] = timebuffer[x]+time;
                fi 
            :: else;
            fi
            assert(timebuffer[x] <= DEADLINE);
        }       
    :: else;
    fi
    }
}

active proctype Source()
{
    do
    :: source!white
    :: source!red -> break
    od
    do
    :: source!white
    :: source!blue -> break
    od
    do
    :: source!white
    od
}

active proctype Sender()
{
    byte SeqNum, x;
    mtype data;

    do
    :: source?data ->  
        
        atomic{
        (timebuffer[SeqNum] == FREE) ->
        timebuffer[SeqNum] = 1; 
        sublink[0]!data, SeqNum;  
        sublink[1]!data, SeqNum;  
        increasetime();
        }

        inc(SeqNum);

    od
}

active proctype Receiver()
{
    byte RecvNum, RecvTime, LastNum = 3;
    mtype RecvData ;
    byte rcpbuffer[MaxSeq+1];
    byte controlbuffer[MaxSeq+1];
    int i;

    d_step{
    for (i : 0 .. MaxSeq) {
            rcpbuffer[i] = none;
    }
    } 

    do
    ::
        atomic{
        //rr = false; // FOR VERIFICATION
        //rb = false; // FOR VERIFICATION

        if
        :: sublink[0]?RecvData,RecvNum
        :: sublink[1]?RecvData,RecvNum  
        fi 

        controlbuffer[RecvNum]++; 
        }

        if
        ::  skip;
        ::  RecvTime = timebuffer[RecvNum];  
    
            if
            :: RecvTime<DEADLINE ->  

                /*if    // FOR VERIFICATION
                :: RecvData == red ->
                    ontime_red: skip; 
                :: RecvData == blue ->
                    ontime_blue: skip;
                :: else -> skip;
                fi*/ 

                if
                :: rcpbuffer[RecvNum] != none ->  
                :: else ->
                    rcpbuffer[RecvNum] = RecvData;
                    if
                    :: (LastNum+1)%(MaxSeq+1) == RecvNum ->  
                        LastNum = RecvNum; 
                        /*if    // FOR VERIFICATION
                        :: RecvData == red ->
                            nr++; rr = true; skip;
                        :: RecvData == blue ->
                            nb++; rb = true; skip;
                        :: else -> skip;
                        fi*/
                        rcpbuffer[RecvNum]=consumed;
                    :: else -> skip;
                    fi      
                fi
            :: else -> 
                /* if   // FOR VERIFICATION
                :: RecvData == red ->
                    nlr++; skip; 
                :: RecvData == blue ->
                    nlb++; skip;
                :: else -> skip;
                fi*/
            fi 
        fi

        if
        :: controlbuffer[RecvNum] == 2 ->  
            controlbuffer[RecvNum] = 0;
            if
            :: else; skip;
            :: (LastNum+1)%(MaxSeq+1) == RecvNum -> LastNum = (LastNum+1)%(MaxSeq+1);
                if
                :: rcpbuffer[LastNum] != none && rcpbuffer[LastNum] != consumed -> 
                    /*if    // FOR VERIFICATION
                    :: rcpbuffer[LastNum] == red ->
                        nr++; rr = true; skip;
                    :: rcpbuffer[LastNum] == blue ->
                        nb++; rb = true; skip;
                    :: else -> skip;
                    fi*/
                    rcpbuffer[LastNum] = none;
                :: else -> skip;
                fi
            fi
            rcpbuffer[RecvNum] = none;
            timebuffer[RecvNum] = FREE;    
        :: else;
        fi
    od

}

/*  // FOR VERIFICATION
ltl p1{ [] ( (nr <= 1) && (nb <= 1) ) }
ltl p1_1{ [] ( (nr <= 1) ) }
ltl p1_2{ [] ( (nb <= 1) ) }

ltl p2{ [] ( (nlater == 2 -> [] nr=0) && (nlateb == 2 -> [] nb=0) )}
ltl p2_1{ [] (nlater == 2 -> [] nr=0)}
ltl p2_2{ [] (nlateb == 2 -> [] nb=0)}

ltl p3{ [] (rb -> []!rr) }

ltl p4{ [] (((Receiver@ontime_red && nr == 0) -> <>rr) && ((Receiver@ontime_blue && nb == 0)-> <>rb))}
ltl p4_1{ [] ((Receiver@ontime_red && nr == 0) -> <>rr)}
ltl p4_2{ [] ((Receiver@ontime_blue && nb == 0)-> <>rb)}
*/
 
