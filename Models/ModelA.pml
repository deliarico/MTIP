#define MaxSeq  3
#define MaxSublinks 2 
#define ONTIME 0
#define LATE 1
#define inc(x)  x = (x+1)%(MaxSeq+1)

//bool rr, rb    //FOR VERIFICATION
//byte nr, nb    //FOR VERIFICATION
//byte nlr, nlb  //FOR VERIFICATION

mtype = { none, red, white, blue } 
chan sublink[MaxSublinks] = [MaxSeq+1] of { mtype, byte, byte }
chan source = [0] of { mtype }
byte ExpectedNum;

active proctype Sender()
{
    byte SeqNum;
    mtype data;
    atomic{
    do
    :: source?data -> 
        if
        :: 
            if
            :: sublink[0]!data, SeqNum, ONTIME; 
            :: sublink[0]!data, SeqNum, LATE; 
            fi 
        :: 
            if
            :: sublink[1]!data, SeqNum, ONTIME; 
            :: sublink[1]!data, SeqNum, LATE; 
            fi
        :: 
            if
            :: sublink[0]!data, SeqNum, ONTIME; 
            :: sublink[0]!data, SeqNum, LATE; 
            fi
            if
            :: sublink[1]!data, SeqNum, ONTIME; 
            :: sublink[1]!data, SeqNum, LATE; 
            fi 
        :: true -> skip;
        fi       
        inc(SeqNum);
        (ExpectedNum != SeqNum) ->  
    od
    } 
}

active proctype Receiver()
{
    byte RecvNum, RecvTime, LastNum, SublinkNum;
    mtype RecvData;
    byte rcpbuffer[MaxSeq+1];
    byte controlbuffer[MaxSeq+1];
    int i;
    d_step{
    for (i : 0 .. MaxSeq) {
            rcpbuffer[i] = none;
    }
    } 

    Receving: 
    do
    ::      
        atomic{
        //rr = false; //FOR VERIFICATION
        //rb = false; //FOR VERIFICATION           
        
        if
        :: ExpectedNum == 0 -> rcpbuffer[3] = none;
        :: else -> rcpbuffer[ExpectedNum-1] = none;
        fi        
        
        if
        :: ExpectedNum == 0 ->
            if
            :: sublink[0]?[_,0,ONTIME] -> SublinkNum = 0;
            :: sublink[1]?[_,0,ONTIME] -> SublinkNum = 1;
            :: timeout ->              
                if
                :: sublink[0]?[_,0,LATE] -> SublinkNum = 0;
                :: sublink[1]?[_,0,LATE] -> SublinkNum = 1;
                :: timeout -> ExpectedNum = (ExpectedNum+1)%(MaxSeq+1);   goto Receving;
                fi
            fi
        :: ExpectedNum == 1 ->
            if
            :: sublink[0]?[_,1,ONTIME] -> SublinkNum = 0;
            :: sublink[1]?[_,1,ONTIME] -> SublinkNum = 1;
            :: timeout ->              
                if
                :: sublink[0]?[_,1,LATE] -> SublinkNum = 0;
                :: sublink[1]?[_,1,LATE] -> SublinkNum = 1;
                :: timeout -> ExpectedNum = (ExpectedNum+1)%(MaxSeq+1);   goto Receving;
                fi
            fi
        :: ExpectedNum == 2 ->
            if
            :: sublink[0]?[_,2,ONTIME] -> SublinkNum = 0;
            :: sublink[1]?[_,2,ONTIME] -> SublinkNum = 1;
            :: timeout ->              
                if
                :: sublink[0]?[_,2,LATE] -> SublinkNum = 0;
                :: sublink[1]?[_,2,LATE] -> SublinkNum = 1;
                :: timeout -> ExpectedNum = (ExpectedNum+1)%(MaxSeq+1);   goto Receving;
                fi
            fi
        :: ExpectedNum == 3 ->
            if
            :: sublink[0]?[_,3,ONTIME] -> SublinkNum = 0;
            :: sublink[1]?[_,3,ONTIME] -> SublinkNum = 1;
            :: timeout ->              
                if
                :: sublink[0]?[_,3,LATE] -> SublinkNum = 0;
                :: sublink[1]?[_,3,LATE] -> SublinkNum = 1;
                :: timeout -> ExpectedNum = (ExpectedNum+1)%(MaxSeq+1);   goto Receving;
                fi
            fi
        fi
        
        sublink[SublinkNum]?RecvData,RecvNum,RecvTime   
        }

        if
        :: RecvTime == ONTIME ->          
            if
            :: rcpbuffer[RecvNum] != none ->  
                rcpbuffer[RecvNum] = none;
            :: else ->
                rcpbuffer[RecvNum] = RecvData;
                /*if    // FOR VERIFICATION
                :: RecvData == red ->
                    nr++;
                    rr=true; 
                    assert(!rb); assert(nlr == 0); assert(nr<=1); skip; 
                :: RecvData == blue ->
                    nb++;
                    rb=true; 
                    assert(nlb == 0); assert(nb<=1); skip; 
                :: else -> skip;
                fi*/
            fi
        :: else ->  
            /*if    // FOR VERIFICATION
            :: RecvData == red ->   nlr++; 
            :: RecvData == blue ->  nlb++;
            :: else -> skip;
            fi*/
        fi  
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
