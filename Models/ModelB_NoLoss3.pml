#define MaxSeq  3
#define MaxSublinks 2 
#define FREE 0 
#define DEADLINE 3  
#define inc(x)  x = (x+1)%(MaxSeq+1)

//bool rr, rb   // FOR VERIFICATION
//byte nr, nb   // FOR VERIFICATION
//byte nlr, nlb // FOR VERIFICATION

mtype = { none, red, white, blue } 
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


active proctype sender()
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

active proctype receiver()
{
    byte RecvNum, RecvTime;
    mtype RecvData;
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
        
        RecvTime = timebuffer[RecvNum]; 
        controlbuffer[RecvNum]++; 
        }

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
                    rcpbuffer[RecvNum]=RecvData;
                /*if    // FOR VERIFICATION
                :: RecvData == red ->
                    nr++; rr = true; skip;
                :: RecvData == blue ->
                    nb++; rb = true; skip;
                :: else -> skip;
                fi*/
            fi

        :: else ->  
            /*if    // FOR VERIFICATION
            :: RecvData == red ->
                late_red: nlr++; skip;  
            :: RecvData == blue ->
                late_blue: nlb++; skip;
            :: else -> skip;
            fi*/
        fi

        atomic{
        if
        :: controlbuffer[RecvNum] == 2 ->  
            controlbuffer[RecvNum] = 0;
            rcpbuffer[RecvNum] = none;
            timebuffer[RecvNum] = FREE;
        :: else;
        fi
        }
    od

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
 
/*                                      // FOR VERIFICATION
ltl p1{ [] ( (nr <= 1) && (nb <= 1) ) }
ltl p1_1{ [] ( (nr <= 1) ) }
ltl p1_2{ [] ( (nb <= 1) ) }

ltl p2{ [] (receiver@late_red -> []!rr) && [] (receiver@late_blue -> []!rb) }
ltl p2_1{ [] ((receiver@late_red -> []!rr)}
ltl p2_2{ [] (receiver@late_blue -> []!rb)}

ltl p3{ [] (rb -> []!rr) }

ltl p4{ [] ((receiver@ontime_red && nr == 0) -> <>rr) && [] ((receiver@ontime_blue && nb == 0)-> <>rb)}
ltl p4_1{ [] ((receiver@ontime_red && nr == 0) -> <>rr)}
ltl p4_2{ [] ((receiver@ontime_blue && nb == 0)-> <>rb)}
*/
 
