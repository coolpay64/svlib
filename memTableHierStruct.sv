//==============================
// Copyright 2016 Wong Kin Hin , Hong Kong
// This work is licensed under a Creative Commons Attribution 4.0 International License.
// For further detail, please refer to 
// http://creativecommons.org/licenses/by/4.0/
//==============================
package armMemTablePkg;
  typedef bit  [47:0] MemAddrT;
  typedef class       memEntry;
  class memEntry;
    static memEntry tableRecord    [MemAddrT];
    static MemAddrT addrHierRecord [0:4][$];
    static MemAddrT addrRecord     [$];
    static int      totalRecords;

    int             level     ; 
    int             granule   ; // 4 / 64
    int             tableSize ; 
         MemAddrT   entryAddr ; 
    rand bit        endPoint  ; 
    memEntry        memTable[];
    rand int        addrTable[];
    rand MemAddrT   transAddr ; 

         bit  [3:0] memAttribute[string];

    constraint transAddr_cons{
      transAddr[47:40] inside {8'h00,8'hff}; 
      transAddr[12: 0] == 0; 
    };
    constraint endpoint_cons{
      level == 4 -> endPoint;
    }
    constraint contiguous_cons{
      //!endPoint -> memAttribute["con"]==0;
    };
    constraint addrTable_cons{
      !endPoint -> addrTable.size() == this.tableSize;
       endPoint -> addrTable.size() == 1;
      foreach(addrTable[i]){
        //addrTable[i] inside {[0: totalRecords-1]};
        addrTable[i] inside {[0:addrHierRecord[level+1].size()-1]};
      }
    }
    constraint dependancy_cons{
      //solve endPoint before memAttribute["con"];
      solve endPoint before addrTable;
    };
    
    function void post_randomize();
      if(tableSize)begin
        memTable = new[tableSize];
        foreach(addrTable[i])begin
          memTable[i] = tableRecord[addrRecord[addrTable[i]]];
        end
      end
      if(memAttribute["con"])begin
      end
    endfunction

    function new();
      //List out all field here
      memAttribute["ns" ]=0;
      memAttribute["ng" ]=0;
      memAttribute["nc" ]=0;
      memAttribute["ap" ]=0;
      memAttribute["xn" ]=0;
      memAttribute["uxn"]=0;
      memAttribute["pxn"]=0;
      memAttribute["con"]=0;
    endfunction
  endclass

  class memTable;
    int granule   ;
    int totalRecords  =1024*8;
    memEntry tableRoot;
    memEntry newEntry;
    rand MemAddrT   newAddr[];
    rand logic[2:0] newLevel[];
    
    function new();
    endfunction

    extern function void createTable(int granSize);
    extern function MemAddrT translate(MemAddrT va);


    function void clearWholeTable();
      memEntry::tableRecord.delete();
      memEntry::addrRecord .delete();
      tableRoot = null;
    endfunction
  endclass

    function void memTable::createTable(int granSize);
      MemAddrT   finalAddr;
      this.granule     = granSize;
      tableRoot = new;
      tableRoot.level = -1;
      tableRoot.entryAddr = 0;
      tableRoot.granule   = this.granule;
      if(tableRoot.granule == 4 ) begin // 4K
        tableRoot.tableSize = 512;
      end else if(tableRoot.granule == 64) begin // 64K
        tableRoot.tableSize = 64;
      end else begin // testing
        tableRoot.tableSize = 32;
      end

      this.randomize() with {
        newAddr .size() == this.totalRecords;
        newLevel.size() == this.totalRecords;
        foreach(newAddr[i]){
          newAddr[i][47:33] == 0; 
          newAddr[i][12: 0] == 0; 
        }
        foreach(newLevel[i]){
          newLevel[i] inside {[0:3]};
        }
      };

      foreach(newAddr[i])begin
        if(!memEntry::tableRecord.exists(newAddr[i]))begin
          memEntry::addrRecord.push_back(newAddr[i]);
          newEntry = new;
          newEntry.granule = this.granule;
          if(newLevel[i] == 0 )begin
            if(newEntry.granule == 4 ) begin // 4K
              newEntry.tableSize = 512;
            end else if(newEntry.granule == 64) begin // 64K
              newEntry.tableSize = 64 ;
            end else begin // testing
              newEntry.tableSize = 32 ;
            end
          end else begin
            if(newEntry.granule == 4 ) begin // 4K
              newEntry.tableSize = 512;
            end else if(newEntry.granule == 64) begin // 64K
              newEntry.tableSize = 8192;
            end else begin // testing
              newEntry.tableSize = 32;
            end
          end
          newEntry.entryAddr = newAddr[i];
          newEntry.level     = newLevel[i];
          memEntry::tableRecord[newAddr[i]] = newEntry;
          memEntry::addrHierRecord[newLevel[i]].push_back(newAddr[i]);
        end
      end
      
      finalAddr        = 0;
      finalAddr[12: 0] = 0;
      while(memEntry::tableRecord.exists(finalAddr))begin
        finalAddr[40:13]++;
      end
      newEntry       = new;
      newEntry.level = 4;
      newEntry.entryAddr = finalAddr;
      memEntry::tableRecord[finalAddr] = newEntry;
      memEntry::addrHierRecord[4].push_back(finalAddr);

      foreach(newAddr[i])begin
        memEntry::tableRecord[newAddr[i]].randomize with {
          i < tableRoot.tableSize -> endPoint == 0;
        };
      end
      tableRoot.randomize() with{
        endPoint == 0;
      };
    endfunction : createTable

    function MemAddrT memTable::translate(MemAddrT va);
      int indexMSB,indexLSB;
      int curLevel;
      int endPointReached;
      memEntry curRecord;
      MemAddrT result = 0;
      MemAddrT mask   = 0;

      curLevel = 0;
      endPointReached = 0;
      if(this.granule == 64)
        curLevel++;
      curRecord = tableRoot;

      indexMSB = 47;
      if(this.granule == 64) begin
        indexLSB = 42;
      end else begin
        indexLSB = 39;
      end
      while(!endPointReached)begin
        MemAddrT curIndex;
        curIndex = va;
        curIndex &= {indexMSB+1{1'b1}};
        curIndex = curIndex >> indexLSB;
        if(curLevel == 3 || curRecord.endPoint)begin
          endPointReached = 1;
          result = curRecord.transAddr;
          //$display("HERE %1d %1d",curLevel,curRecord.endPoint);
        end else begin
          curRecord = curRecord.memTable[curIndex % curRecord.tableSize];
        end
        
        indexMSB=indexLSB-1;
        if(!endPointReached)begin
          if(this.granule == 64) begin
            indexLSB = indexMSB-12;
          end else begin
            indexLSB = indexMSB-8;
          end
          curLevel++;
        end
      end
      foreach(mask[i])begin
        mask[i] = i > indexMSB ? 1 : 0;
      end
      result &= mask;
      $display("Cur LV: %1d VA: %12x PA: %12x", curLevel, va,result);
      return result;
    endfunction

endpackage

import armMemTablePkg::*;
module tb();
  initial begin
    MemAddrT inputVA;
    int seed; memEntry entry;
    memTable mem_table;
    $value$plusargs("seed=%d",seed);
    mem_table = new;
    if(seed)
      mem_table.srandom(seed);
    process::self().srandom(seed);
    mem_table.createTable(4);
    $display("Total Record: %d",memEntry::tableRecord.size());
    repeat(1000)begin
      inputVA= {$urandom,$urandom};
      mem_table.translate(inputVA);
    end

  end
endmodule
