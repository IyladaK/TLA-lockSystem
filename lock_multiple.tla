--------------------------- MODULE lock_multiple ---------------------------

EXTENDS lock_data


(* --algorithm lock_system

\*****************************
\* Define global variables
\*****************************
variables
  \* Variables for locks
  lockOrientations = [l \in Locks |-> IF l%2=0 THEN "west_low" ELSE "east_low"],
  doorsOpen = [l \in Locks |-> [ls \in LockSide |-> FALSE]],
  valvesOpen = [l \in Locks |-> [vs \in ValveSide |-> FALSE]],
  waterLevel = [l \in Locks |-> "low"],
  
  \* Variables for single ship
  shipLocations = [s \in Ships |-> IF s%2=0 THEN 0 ELSE EastEnd],
  shipStates = [s \in Ships |-> IF s%2=0 THEN "go_to_east" ELSE "go_to_west"],
  
  \* Command for lock
  \* for command "change_door" the side should be "west" or "east"
  \* for command "change_valve" the side should be "high" or "low"
  lockCommand = [l \in Locks |-> [command |-> "finished", open |-> FALSE, side |-> "west"]],
  \* Central requests of all ships
  requests = << >>,
  \* Permissions per ship
  permissions = [s \in Ships |-> << >>],
  moved = [s \in Ships |-> FALSE];


define

\*****************************
\* Helper functions
\*****************************
\* Check if given ship is within a lock
InLock(ship) == IsLock(shipLocations[ship])

\* given a lock, returns the location is the lock
lockLocation(lock) == lock + (lock - 1)

\* returns the set of ships at a given location
shipsAtLoc(loc) == {s \in Ships: shipLocations[s] = loc}

\* returns the number of ships at a given location
numShipsAtLoc(loc) == Cardinality(shipsAtLoc(loc))

\* returns TRUE if all ships at a given location want to head east
allHeadedEast(loc) == \A s \in shipsAtLoc(loc) : shipStates[s] = "go_to_east"

\* returns TRUE if all ships at a given location want to head west
allHeadedWest(loc) == \A s \in shipsAtLoc(loc) : shipStates[s] = "go_to_west"

\* returns TRUE if all doors in a given lock are closed
isDoorsClosed(lock) == doorsOpen[lock] = [ls \in LockSide |-> FALSE]



\*****************************
\* Type checks
\*****************************
\* Check that variables use the correct type
TypeOK == /\ \A l \in Locks: /\ lockOrientations[l] \in LockOrientation
                             /\ \A ls \in LockSide : doorsOpen[l][ls] \in BOOLEAN
                             /\ \A vs \in ValveSide : valvesOpen[l][vs] \in BOOLEAN
                             /\ waterLevel[l] \in WaterLevel
                             /\ lockCommand[l].command \in LockCommand
                             /\ lockCommand[l].open \in BOOLEAN
                             /\ lockCommand[l].side \in LockSide \union ValveSide
          /\ \A s \in Ships: /\ shipLocations[s] \in Locations
                             /\ shipStates[s] \in ShipStatus
                             /\ \A i \in 1..Len(permissions[s]):
                                  /\ permissions[s][i].lock \in Locks
                                  /\ permissions[s][i].granted \in BOOLEAN
                             /\ moved[s] \in BOOLEAN
          /\ \A i \in 1..Len(requests):
               /\ requests[i].ship \in Ships
               /\ requests[i].lock \in Locks
               /\ requests[i].side \in LockSide

\* Check that message queues are not overflowing
MessagesOK == /\ Len(requests) <= NumShips
              /\ \A s \in Ships: Len(permissions[s]) <= 1


\*****************************
\* Requirements on lock
\*****************************
\* The eastern pair of doors and the western pair of doors are never simultaneously open
DoorsMutex == [](\A l \in Locks : ~(doorsOpen[l]["west"] /\ doorsOpen[l]["east"]))
\* When the lower/higher pair of doors is open, the higher/lower valve is closed.
DoorsOpenValvesClosed == [](\A l \in Locks : (doorsOpen[l][LowSide(lockOrientations[l])] => ~valvesOpen[l]["high"]) /\
                                             (doorsOpen[l][HighSide(lockOrientations[l])] => ~valvesOpen[l]["low"]))
\* The lower/higher pair of doors is only open when the water level in the lock is low/high
DoorsOpenWaterlevelRight  == [](\A l \in Locks : (doorsOpen[l][LowSide(lockOrientations[l])] => (waterLevel[l] = "low")) /\
                                                 (doorsOpen[l][HighSide(lockOrientations[l])] => (waterLevel[l] = "high")))
\* Always if a ship requests to enter a lock, the ship will eventually be inside the lock. DONE???????
RequestLockFulfilled == [](\A s \in Ships: (\E r \in 1..Len(requests) : requests[r].ship = s => <>(shipLocations[s] = requests[r].lock)))
\* Water level is infinitely many times high/low DONE
WaterlevelChange == []<>(\A l \in Locks : (waterLevel[l] = "low" \/ waterLevel[l] = "high"))
\* Infinitely many times each ship does requests DONE?
RequestsShips == \A s \in Ships : []<>(\E r \in 1..Len(requests) : requests[r].ship = s)
\* Infinitely many times each ship reaches its end location DONE
ShipsReachGoals == \A s \in Ships: ([]<>(shipLocations[s] = EastEnd) /\ []<>(shipLocations[s] = WestEnd))
\* The maximal ship capacity per location is not exceeded
MaxShipsPerLocation == (\A loc \in Locations : IF IsLock(loc) THEN Cardinality({\A s \in Ships : shipLocations[s] = loc}) \leq MaxShipsLock
                                                 ELSE Cardinality({\A s \in Ships : shipLocations[s] = loc}) \leq MaxShipsLocation)
                           

end define;



\*****************************
\* Helper macros
\*****************************

\* Update the water level according to the state of doors and valves
macro updateWaterLevel(lock_orientation, doors, valves, waterlevel) begin
  if valves["low"] then
      \* Water can flow out through valve
      waterlevel := "low";
  elsif (lock_orientation = "west_low" /\ doors["west"])
         \/ (lock_orientation = "east_low" /\ doors["east"]) then
      \* Water can flow out through lower door
      waterlevel := "low";
  elsif valves["high"] then
      \* Water can flow in through valve
      waterlevel := "high";
  elsif (lock_orientation = "west_low" /\ doors["east"])
         \/ (lock_orientation = "east_low" /\ doors["west"]) then
      \* Water can flow in through higher door
      waterlevel := "high";
  \* In other case, the water level stays the same
  end if;
end macro

\* Read res from queue.
\* The macro awaits a non-empty queue.
macro read(queue, res) begin
  await queue /= <<>>;
  res := Head(queue);
  queue := Tail(queue);
end macro

\* Write msg to the queue.
macro write(queue, msg) begin
  queue := Append(queue, msg);
end macro

macro restoreShipState(ship) begin
    perm[ship].granted := FALSE;
    moved[ship] := FALSE;
end macro

\*****************************
\* Helper Procedures
\*****************************
procedure closeAllDoors(lock)
begin
  CloseEastDoor:
    lockCommand[lock] := [command |-> "change_door", open |-> FALSE, side |-> "east"];
  WaitEastDoorClosed:
    await lockCommand[lock].command = "finished";
  CloseWestDoor:
    lockCommand[lock] := [command |-> "change_door", open |-> FALSE, side |-> "west"];
  WaitWestDoorClosed:
    await lockCommand[lock].command = "finished";
  ReturnCloseAllDoors:
    return;
end procedure;

\* if a ship requests to enter from the west, the water level in the lock is adjusted to 
\* the water level on the west side. Vice versa for East
\* preconditions: both doors must be closed
procedure adjustWaterToRequestLevel(lock, reqSide)
begin
    \* check if requested side is the low side
  CheckWaterLevelSide:
    if reqSide = LowSide(lockOrientations[lock]) then
        \* adjust water level down
  OpenLowValve:
        lockCommand[lock] := [command |-> "change_valve", open |-> TRUE, side |-> "low"];
  WaitLowValveOpened:
        await lockCommand[lock].command = "finished";
  CloseLowValve:
        lockCommand[lock] := [command |-> "change_valve", open |-> FALSE, side |-> "low"];
  WaitLowValveClosed:
        await lockCommand[lock].command = "finished";
    \* requested side is the high side
    elsif reqSide = HighSide(lockOrientations[lock]) then
        \* adjust water level up
  OpenHighValve:
        lockCommand[lock] := [command |-> "change_valve", open |-> TRUE, side |-> "high"];
  WaitHighValveOpened:
        await lockCommand[lock].command = "finished";
  CloseHighValve:
        lockCommand[lock] := [command |-> "change_valve", open |-> FALSE, side |-> "high"];
  WaitHighValveClosed:
        await lockCommand[lock].command = "finished";
    end if;
  ReturnAdjustWaterToRequestLevel:
    return;
end procedure;

    

\*****************************
\* Process for a lock
\*****************************
fair process lockProcess \in Locks
begin
  LockWaitForCommand:
    while TRUE do
      await lockCommand[self].command /= "finished";
      if lockCommand[self].command = "change_door" then
        \* Change status of door
        doorsOpen[self][lockCommand[self].side] := lockCommand[self].open;
      elsif lockCommand[self].command = "change_valve" then
        \* Change status of valve
        valvesOpen[self][lockCommand[self].side] := lockCommand[self].open;
      else
        \* should not happen
        assert FALSE;
      end if;
  LockUpdateWaterLevel:
      updateWaterLevel(lockOrientations[self], doorsOpen[self], valvesOpen[self], waterLevel[self]);
  LockCommandFinished:
      lockCommand[self].command := "finished";    
    end while;
end process;


\*****************************
\* Process for a ship
\*****************************
fair process shipProcess \in Ships
variables
  perm = [lock |-> 1, granted |-> FALSE]
begin
  ShipNextIteration:
    while TRUE do
      if shipStates[self] = "go_to_east" then
        if shipLocations[self] = EastEnd then
  ShipGoalReachedEast:
          shipStates[self] := "goal_reached";
        else
          if ~InLock(self) then
  ShipRequestWest:
            \* Request west doors of next lock
            write(requests, [ship |-> self, lock |-> GetLock(shipLocations[self]+1), side |-> "west"]);
  ShipWaitForWest:
            \* Wait for permission
            read(permissions[self], perm);
            assert perm.lock = GetLock(shipLocations[self]+1);
          else
  ShipRequestEastInLock:
            \* Request east doors of current lock
            write(requests, [ship |-> self, lock |-> GetLock(shipLocations[self]), side |-> "east"]);
  ShipWaitForEastInLock:
            \* Wait for permission
            read(permissions[self], perm);
            assert perm.lock = GetLock(shipLocations[self]);
          end if;
  ShipMoveEast:
          if perm.granted then
            \* Move ship
            assert doorsOpen[perm.lock][IF InLock(self) THEN "east" ELSE "west"];
            shipLocations[self] := shipLocations[self] + 1;
            \* Signal finished movement
            moved[self] := TRUE;
          end if;
        end if;
      elsif shipStates[self] = "go_to_west" then
        if shipLocations[self] = WestEnd then
  ShipGoalReachedWest:
          shipStates[self] := "goal_reached";
        else
          if ~InLock(self) then
  ShipRequestEast:
            \* Request east doors of next lock
            write(requests, [ship |-> self, lock |-> GetLock(shipLocations[self]-1), side |-> "east"]);
  ShipWaitForEast:
            \* Wait for permission
            read(permissions[self], perm);
            assert perm.lock = GetLock(shipLocations[self]-1);
          else
  ShipRequestWestInLock:
            \* Request west doors of current lock
            write(requests, [ship |-> self, lock |-> GetLock(shipLocations[self]), side |-> "west"]);
  ShipWaitForWestInLock:
            \* Wait for permission
            read(permissions[self], perm);
            assert perm.lock = GetLock(shipLocations[self]);
          end if;
  ShipMoveWest:
          if perm.granted then
            \* Move ship
            assert doorsOpen[perm.lock][IF InLock(self) THEN "west" ELSE "east"];
            shipLocations[self] := shipLocations[self] - 1;
            \* Signal finished movement
            moved[self] := TRUE;
          end if;
        end if;
      else
        assert shipStates[self] = "goal_reached";
  ShipTurnAround:
        \* Turn around
        shipStates[self] := IF shipLocations[self] = WestEnd THEN "go_to_east" ELSE "go_to_west";
      end if;
    end while;
end process;



\*****************************
\* Process for the controller
\*****************************
fair process controlProcess = 0

variables
    req = [ship |-> 0, lock |-> 0, side |-> "east"],
    inUseLocks = [l \in Locks |-> FALSE]
begin
    MainLoop:
        while TRUE do
    ControlStart:
            await requests # <<>>;
            read(requests, req);
    EntryRequest:
            \*************************
            \* Terminating Conditions
            \*************************
            if ~IsLock(shipLocations[req.ship]) then
                \* assert req.lock = shipLocations[req.ship] + 1 \/ req.lock = shipLocations[req.ship] - 1;
                \* if the lock is currently occupied
                if inUseLocks[req.lock] = TRUE then
                    \* deny permission
                    write(permissions[req.ship], [lock |-> req.lock, granted |-> FALSE]);
                    goto ControlStart; \* break
                \* lock is not currenlty occupied
                else
                    \* check if there are (more than) two ships at the location in front of
                    \* the requested lock. If there are, the request is denied if those ships
                    \* are/will want to get into the requested lock
                    if numShipsAtLoc(lockLocation(req.lock + 1)) >= 2 then
                        \* current request going east, two or more ships headed west
                        if shipStates[req.ship] = "go_to_east" then
                            if allHeadedWest(lockLocation(req.lock + 1)) then
                                write(permissions[req.ship], [lock |-> req.lock, granted |-> FALSE]);
                                goto ControlStart; \* break
                            end if;
                        elsif shipStates[req.ship] = "go_to_west" then
                            if allHeadedEast(lockLocation(req.lock + 1)) then
                                write(permissions[req.ship], [lock |-> req.lock, granted |-> FALSE]);
                                goto ControlStart; \* break
                            end if;
                        end if;
                    end if;
                end if;               
                
            \**************
            \* Request OK
            \**************
    CloseBothDoorsBeforeEntry:
                call closeAllDoors(req.lock);
    AdjustWaterToEntraceLevel:
                call adjustWaterToRequestLevel(req.lock, req.side);
    OpenDoorForEntry:
                lockCommand[req.lock] := [command |-> "change_door", open |-> TRUE, side|-> req.side];
    DoorOpenForEntry:
                await lockCommand[req.lock].command = "finished";
    WriteEntryPermission:
                \* allow ship to enter
                write(permissions[req.ship], [lock |-> req.lock, granted |-> TRUE]);
    WaitForShipToEnter:
                await moved[req.ship] = TRUE;
    CloseDoorAfterEntry:
                \* open east door
                lockCommand[req.lock] := [command |-> "change_door", open |-> FALSE, side|-> req.side];
    DoorClosedAfterEntry:
                await lockCommand[req.lock].command = "finished";
                restoreShipState(req.ship);
                goto ControlStart; 
            end if;     
    ExitRequest:
            \*************************
            \* Terminating Conditions
            \*************************
            if IsLock(shipLocations[req.ship]) then
                assert lockLocation(req.lock) = shipLocations[req.ship];
                \* FILL OUT TERMINATING CONDITIONS
                
            \**************
            \* Request OK
            \**************
                \* adjust water to exit level
    \* All doors must already be closed at this point
    \* Adjust water level
    AdjustWaterToExitLevel:
                call adjustWaterToRequestLevel(req.lock, req.side);
    OpenDoorForExit:
                lockCommand[req.lock] := [command |-> "change_door", open |-> TRUE, side|-> req.side];
    DoorOpenForExit:
                await lockCommand[req.lock].command = "finished";
    WriteExitPermission:
                \* allow ship to enter
                write(permissions[req.ship], [lock |-> req.lock, granted |-> TRUE]);
    WaitForShipToExit:
                await moved[req.ship] = TRUE;
    CloseDoorAfterExit:
                \* open east door
                lockCommand[req.lock] := [command |-> "change_door", open |-> FALSE, side|-> req.side];
    DoorClosedAfterExit:
                await lockCommand[req.lock].command = "finished";
                restoreShipState(req.ship);
                goto ControlStart;         
            end if;
        end while;
end process;


end algorithm; *)


\* BEGIN TRANSLATION (chksum(pcal) = "ddfd159f" /\ chksum(tla) = "754dcd10")
\* Parameter lock of procedure closeAllDoors at line 161 col 25 changed to lock_
CONSTANT defaultInitValue
VARIABLES lockOrientations, doorsOpen, valvesOpen, waterLevel, shipLocations, 
          shipStates, lockCommand, requests, permissions, moved, pc, stack

(* define statement *)
InLock(ship) == IsLock(shipLocations[ship])


lockLocation(lock) == lock + (lock - 1)


shipsAtLoc(loc) == {s \in Ships: shipLocations[s] = loc}


numShipsAtLoc(loc) == Cardinality(shipsAtLoc(loc))


allHeadedEast(loc) == \A s \in shipsAtLoc(loc) : shipStates[s] = "go_to_east"


allHeadedWest(loc) == \A s \in shipsAtLoc(loc) : shipStates[s] = "go_to_west"


isDoorsClosed(lock) == doorsOpen[lock] = [ls \in LockSide |-> FALSE]







TypeOK == /\ \A l \in Locks: /\ lockOrientations[l] \in LockOrientation
                             /\ \A ls \in LockSide : doorsOpen[l][ls] \in BOOLEAN
                             /\ \A vs \in ValveSide : valvesOpen[l][vs] \in BOOLEAN
                             /\ waterLevel[l] \in WaterLevel
                             /\ lockCommand[l].command \in LockCommand
                             /\ lockCommand[l].open \in BOOLEAN
                             /\ lockCommand[l].side \in LockSide \union ValveSide
          /\ \A s \in Ships: /\ shipLocations[s] \in Locations
                             /\ shipStates[s] \in ShipStatus
                             /\ \A i \in 1..Len(permissions[s]):
                                  /\ permissions[s][i].lock \in Locks
                                  /\ permissions[s][i].granted \in BOOLEAN
                             /\ moved[s] \in BOOLEAN
          /\ \A i \in 1..Len(requests):
               /\ requests[i].ship \in Ships
               /\ requests[i].lock \in Locks
               /\ requests[i].side \in LockSide


MessagesOK == /\ Len(requests) <= NumShips
              /\ \A s \in Ships: Len(permissions[s]) <= 1






DoorsMutex == [](\A l \in Locks : ~(doorsOpen[l]["west"] /\ doorsOpen[l]["east"]))

DoorsOpenValvesClosed == [](\A l \in Locks : (doorsOpen[l][LowSide(lockOrientations[l])] => ~valvesOpen[l]["high"]) /\
                                             (doorsOpen[l][HighSide(lockOrientations[l])] => ~valvesOpen[l]["low"]))

DoorsOpenWaterlevelRight  == [](\A l \in Locks : (doorsOpen[l][LowSide(lockOrientations[l])] => (waterLevel[l] = "low")) /\
                                                 (doorsOpen[l][HighSide(lockOrientations[l])] => (waterLevel[l] = "high")))

RequestLockFulfilled == [](\A s \in Ships: (\E r \in 1..Len(requests) : requests[r].ship = s => <>(shipLocations[s] = requests[r].lock)))

WaterlevelChange == []<>(\A l \in Locks : (waterLevel[l] = "low" \/ waterLevel[l] = "high"))

RequestsShips == \A s \in Ships : []<>(\E r \in 1..Len(requests) : requests[r].ship = s)

ShipsReachGoals == \A s \in Ships: ([]<>(shipLocations[s] = EastEnd) /\ []<>(shipLocations[s] = WestEnd))

MaxShipsPerLocation == (\A loc \in Locations : IF IsLock(loc) THEN Cardinality({\A s \in Ships : shipLocations[s] = loc}) \leq MaxShipsLock
                                                 ELSE Cardinality({\A s \in Ships : shipLocations[s] = loc}) \leq MaxShipsLocation)

VARIABLES lock_, lock, reqSide, perm, req, inUseLocks

vars == << lockOrientations, doorsOpen, valvesOpen, waterLevel, shipLocations, 
           shipStates, lockCommand, requests, permissions, moved, pc, stack, 
           lock_, lock, reqSide, perm, req, inUseLocks >>

ProcSet == (Locks) \cup (Ships) \cup {0}

Init == (* Global variables *)
        /\ lockOrientations = [l \in Locks |-> IF l%2=0 THEN "west_low" ELSE "east_low"]
        /\ doorsOpen = [l \in Locks |-> [ls \in LockSide |-> FALSE]]
        /\ valvesOpen = [l \in Locks |-> [vs \in ValveSide |-> FALSE]]
        /\ waterLevel = [l \in Locks |-> "low"]
        /\ shipLocations = [s \in Ships |-> IF s%2=0 THEN 0 ELSE EastEnd]
        /\ shipStates = [s \in Ships |-> IF s%2=0 THEN "go_to_east" ELSE "go_to_west"]
        /\ lockCommand = [l \in Locks |-> [command |-> "finished", open |-> FALSE, side |-> "west"]]
        /\ requests = << >>
        /\ permissions = [s \in Ships |-> << >>]
        /\ moved = [s \in Ships |-> FALSE]
        (* Procedure closeAllDoors *)
        /\ lock_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure adjustWaterToRequestLevel *)
        /\ lock = [ self \in ProcSet |-> defaultInitValue]
        /\ reqSide = [ self \in ProcSet |-> defaultInitValue]
        (* Process shipProcess *)
        /\ perm = [self \in Ships |-> [lock |-> 1, granted |-> FALSE]]
        (* Process controlProcess *)
        /\ req = [ship |-> 0, lock |-> 0, side |-> "east"]
        /\ inUseLocks = [l \in Locks |-> FALSE]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Locks -> "LockWaitForCommand"
                                        [] self \in Ships -> "ShipNextIteration"
                                        [] self = 0 -> "MainLoop"]

CloseEastDoor(self) == /\ pc[self] = "CloseEastDoor"
                       /\ lockCommand' = [lockCommand EXCEPT ![lock_[self]] = [command |-> "change_door", open |-> FALSE, side |-> "east"]]
                       /\ pc' = [pc EXCEPT ![self] = "WaitEastDoorClosed"]
                       /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                                       waterLevel, shipLocations, shipStates, 
                                       requests, permissions, moved, stack, 
                                       lock_, lock, reqSide, perm, req, 
                                       inUseLocks >>

WaitEastDoorClosed(self) == /\ pc[self] = "WaitEastDoorClosed"
                            /\ lockCommand[lock_[self]].command = "finished"
                            /\ pc' = [pc EXCEPT ![self] = "CloseWestDoor"]
                            /\ UNCHANGED << lockOrientations, doorsOpen, 
                                            valvesOpen, waterLevel, 
                                            shipLocations, shipStates, 
                                            lockCommand, requests, permissions, 
                                            moved, stack, lock_, lock, reqSide, 
                                            perm, req, inUseLocks >>

CloseWestDoor(self) == /\ pc[self] = "CloseWestDoor"
                       /\ lockCommand' = [lockCommand EXCEPT ![lock_[self]] = [command |-> "change_door", open |-> FALSE, side |-> "west"]]
                       /\ pc' = [pc EXCEPT ![self] = "WaitWestDoorClosed"]
                       /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                                       waterLevel, shipLocations, shipStates, 
                                       requests, permissions, moved, stack, 
                                       lock_, lock, reqSide, perm, req, 
                                       inUseLocks >>

WaitWestDoorClosed(self) == /\ pc[self] = "WaitWestDoorClosed"
                            /\ lockCommand[lock_[self]].command = "finished"
                            /\ pc' = [pc EXCEPT ![self] = "ReturnCloseAllDoors"]
                            /\ UNCHANGED << lockOrientations, doorsOpen, 
                                            valvesOpen, waterLevel, 
                                            shipLocations, shipStates, 
                                            lockCommand, requests, permissions, 
                                            moved, stack, lock_, lock, reqSide, 
                                            perm, req, inUseLocks >>

ReturnCloseAllDoors(self) == /\ pc[self] = "ReturnCloseAllDoors"
                             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                             /\ lock_' = [lock_ EXCEPT ![self] = Head(stack[self]).lock_]
                             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                             /\ UNCHANGED << lockOrientations, doorsOpen, 
                                             valvesOpen, waterLevel, 
                                             shipLocations, shipStates, 
                                             lockCommand, requests, 
                                             permissions, moved, lock, reqSide, 
                                             perm, req, inUseLocks >>

closeAllDoors(self) == CloseEastDoor(self) \/ WaitEastDoorClosed(self)
                          \/ CloseWestDoor(self)
                          \/ WaitWestDoorClosed(self)
                          \/ ReturnCloseAllDoors(self)

CheckWaterLevelSide(self) == /\ pc[self] = "CheckWaterLevelSide"
                             /\ IF reqSide[self] = LowSide(lockOrientations[lock[self]])
                                   THEN /\ pc' = [pc EXCEPT ![self] = "OpenLowValve"]
                                   ELSE /\ IF reqSide[self] = HighSide(lockOrientations[lock[self]])
                                              THEN /\ pc' = [pc EXCEPT ![self] = "OpenHighValve"]
                                              ELSE /\ pc' = [pc EXCEPT ![self] = "ReturnAdjustWaterToRequestLevel"]
                             /\ UNCHANGED << lockOrientations, doorsOpen, 
                                             valvesOpen, waterLevel, 
                                             shipLocations, shipStates, 
                                             lockCommand, requests, 
                                             permissions, moved, stack, lock_, 
                                             lock, reqSide, perm, req, 
                                             inUseLocks >>

OpenLowValve(self) == /\ pc[self] = "OpenLowValve"
                      /\ lockCommand' = [lockCommand EXCEPT ![lock[self]] = [command |-> "change_valve", open |-> TRUE, side |-> "low"]]
                      /\ pc' = [pc EXCEPT ![self] = "WaitLowValveOpened"]
                      /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                                      waterLevel, shipLocations, shipStates, 
                                      requests, permissions, moved, stack, 
                                      lock_, lock, reqSide, perm, req, 
                                      inUseLocks >>

WaitLowValveOpened(self) == /\ pc[self] = "WaitLowValveOpened"
                            /\ lockCommand[lock[self]].command = "finished"
                            /\ pc' = [pc EXCEPT ![self] = "CloseLowValve"]
                            /\ UNCHANGED << lockOrientations, doorsOpen, 
                                            valvesOpen, waterLevel, 
                                            shipLocations, shipStates, 
                                            lockCommand, requests, permissions, 
                                            moved, stack, lock_, lock, reqSide, 
                                            perm, req, inUseLocks >>

CloseLowValve(self) == /\ pc[self] = "CloseLowValve"
                       /\ lockCommand' = [lockCommand EXCEPT ![lock[self]] = [command |-> "change_valve", open |-> FALSE, side |-> "low"]]
                       /\ pc' = [pc EXCEPT ![self] = "WaitLowValveClosed"]
                       /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                                       waterLevel, shipLocations, shipStates, 
                                       requests, permissions, moved, stack, 
                                       lock_, lock, reqSide, perm, req, 
                                       inUseLocks >>

WaitLowValveClosed(self) == /\ pc[self] = "WaitLowValveClosed"
                            /\ lockCommand[lock[self]].command = "finished"
                            /\ pc' = [pc EXCEPT ![self] = "ReturnAdjustWaterToRequestLevel"]
                            /\ UNCHANGED << lockOrientations, doorsOpen, 
                                            valvesOpen, waterLevel, 
                                            shipLocations, shipStates, 
                                            lockCommand, requests, permissions, 
                                            moved, stack, lock_, lock, reqSide, 
                                            perm, req, inUseLocks >>

OpenHighValve(self) == /\ pc[self] = "OpenHighValve"
                       /\ lockCommand' = [lockCommand EXCEPT ![lock[self]] = [command |-> "change_valve", open |-> TRUE, side |-> "high"]]
                       /\ pc' = [pc EXCEPT ![self] = "WaitHighValveOpened"]
                       /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                                       waterLevel, shipLocations, shipStates, 
                                       requests, permissions, moved, stack, 
                                       lock_, lock, reqSide, perm, req, 
                                       inUseLocks >>

WaitHighValveOpened(self) == /\ pc[self] = "WaitHighValveOpened"
                             /\ lockCommand[lock[self]].command = "finished"
                             /\ pc' = [pc EXCEPT ![self] = "CloseHighValve"]
                             /\ UNCHANGED << lockOrientations, doorsOpen, 
                                             valvesOpen, waterLevel, 
                                             shipLocations, shipStates, 
                                             lockCommand, requests, 
                                             permissions, moved, stack, lock_, 
                                             lock, reqSide, perm, req, 
                                             inUseLocks >>

CloseHighValve(self) == /\ pc[self] = "CloseHighValve"
                        /\ lockCommand' = [lockCommand EXCEPT ![lock[self]] = [command |-> "change_valve", open |-> FALSE, side |-> "high"]]
                        /\ pc' = [pc EXCEPT ![self] = "WaitHighValveClosed"]
                        /\ UNCHANGED << lockOrientations, doorsOpen, 
                                        valvesOpen, waterLevel, shipLocations, 
                                        shipStates, requests, permissions, 
                                        moved, stack, lock_, lock, reqSide, 
                                        perm, req, inUseLocks >>

WaitHighValveClosed(self) == /\ pc[self] = "WaitHighValveClosed"
                             /\ lockCommand[lock[self]].command = "finished"
                             /\ pc' = [pc EXCEPT ![self] = "ReturnAdjustWaterToRequestLevel"]
                             /\ UNCHANGED << lockOrientations, doorsOpen, 
                                             valvesOpen, waterLevel, 
                                             shipLocations, shipStates, 
                                             lockCommand, requests, 
                                             permissions, moved, stack, lock_, 
                                             lock, reqSide, perm, req, 
                                             inUseLocks >>

ReturnAdjustWaterToRequestLevel(self) == /\ pc[self] = "ReturnAdjustWaterToRequestLevel"
                                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                         /\ lock' = [lock EXCEPT ![self] = Head(stack[self]).lock]
                                         /\ reqSide' = [reqSide EXCEPT ![self] = Head(stack[self]).reqSide]
                                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                         /\ UNCHANGED << lockOrientations, 
                                                         doorsOpen, valvesOpen, 
                                                         waterLevel, 
                                                         shipLocations, 
                                                         shipStates, 
                                                         lockCommand, requests, 
                                                         permissions, moved, 
                                                         lock_, perm, req, 
                                                         inUseLocks >>

adjustWaterToRequestLevel(self) == CheckWaterLevelSide(self)
                                      \/ OpenLowValve(self)
                                      \/ WaitLowValveOpened(self)
                                      \/ CloseLowValve(self)
                                      \/ WaitLowValveClosed(self)
                                      \/ OpenHighValve(self)
                                      \/ WaitHighValveOpened(self)
                                      \/ CloseHighValve(self)
                                      \/ WaitHighValveClosed(self)
                                      \/ ReturnAdjustWaterToRequestLevel(self)

LockWaitForCommand(self) == /\ pc[self] = "LockWaitForCommand"
                            /\ lockCommand[self].command /= "finished"
                            /\ IF lockCommand[self].command = "change_door"
                                  THEN /\ doorsOpen' = [doorsOpen EXCEPT ![self][lockCommand[self].side] = lockCommand[self].open]
                                       /\ UNCHANGED valvesOpen
                                  ELSE /\ IF lockCommand[self].command = "change_valve"
                                             THEN /\ valvesOpen' = [valvesOpen EXCEPT ![self][lockCommand[self].side] = lockCommand[self].open]
                                             ELSE /\ Assert(FALSE, 
                                                            "Failure of assertion at line 226, column 9.")
                                                  /\ UNCHANGED valvesOpen
                                       /\ UNCHANGED doorsOpen
                            /\ pc' = [pc EXCEPT ![self] = "LockUpdateWaterLevel"]
                            /\ UNCHANGED << lockOrientations, waterLevel, 
                                            shipLocations, shipStates, 
                                            lockCommand, requests, permissions, 
                                            moved, stack, lock_, lock, reqSide, 
                                            perm, req, inUseLocks >>

LockUpdateWaterLevel(self) == /\ pc[self] = "LockUpdateWaterLevel"
                              /\ IF (valvesOpen[self])["low"]
                                    THEN /\ waterLevel' = [waterLevel EXCEPT ![self] = "low"]
                                    ELSE /\ IF ((lockOrientations[self]) = "west_low" /\ (doorsOpen[self])["west"])
                                                \/ ((lockOrientations[self]) = "east_low" /\ (doorsOpen[self])["east"])
                                               THEN /\ waterLevel' = [waterLevel EXCEPT ![self] = "low"]
                                               ELSE /\ IF (valvesOpen[self])["high"]
                                                          THEN /\ waterLevel' = [waterLevel EXCEPT ![self] = "high"]
                                                          ELSE /\ IF ((lockOrientations[self]) = "west_low" /\ (doorsOpen[self])["east"])
                                                                      \/ ((lockOrientations[self]) = "east_low" /\ (doorsOpen[self])["west"])
                                                                     THEN /\ waterLevel' = [waterLevel EXCEPT ![self] = "high"]
                                                                     ELSE /\ TRUE
                                                                          /\ UNCHANGED waterLevel
                              /\ pc' = [pc EXCEPT ![self] = "LockCommandFinished"]
                              /\ UNCHANGED << lockOrientations, doorsOpen, 
                                              valvesOpen, shipLocations, 
                                              shipStates, lockCommand, 
                                              requests, permissions, moved, 
                                              stack, lock_, lock, reqSide, 
                                              perm, req, inUseLocks >>

LockCommandFinished(self) == /\ pc[self] = "LockCommandFinished"
                             /\ lockCommand' = [lockCommand EXCEPT ![self].command = "finished"]
                             /\ pc' = [pc EXCEPT ![self] = "LockWaitForCommand"]
                             /\ UNCHANGED << lockOrientations, doorsOpen, 
                                             valvesOpen, waterLevel, 
                                             shipLocations, shipStates, 
                                             requests, permissions, moved, 
                                             stack, lock_, lock, reqSide, perm, 
                                             req, inUseLocks >>

lockProcess(self) == LockWaitForCommand(self) \/ LockUpdateWaterLevel(self)
                        \/ LockCommandFinished(self)

ShipNextIteration(self) == /\ pc[self] = "ShipNextIteration"
                           /\ IF shipStates[self] = "go_to_east"
                                 THEN /\ IF shipLocations[self] = EastEnd
                                            THEN /\ pc' = [pc EXCEPT ![self] = "ShipGoalReachedEast"]
                                            ELSE /\ IF ~InLock(self)
                                                       THEN /\ pc' = [pc EXCEPT ![self] = "ShipRequestWest"]
                                                       ELSE /\ pc' = [pc EXCEPT ![self] = "ShipRequestEastInLock"]
                                 ELSE /\ IF shipStates[self] = "go_to_west"
                                            THEN /\ IF shipLocations[self] = WestEnd
                                                       THEN /\ pc' = [pc EXCEPT ![self] = "ShipGoalReachedWest"]
                                                       ELSE /\ IF ~InLock(self)
                                                                  THEN /\ pc' = [pc EXCEPT ![self] = "ShipRequestEast"]
                                                                  ELSE /\ pc' = [pc EXCEPT ![self] = "ShipRequestWestInLock"]
                                            ELSE /\ Assert(shipStates[self] = "goal_reached", 
                                                           "Failure of assertion at line 308, column 9.")
                                                 /\ pc' = [pc EXCEPT ![self] = "ShipTurnAround"]
                           /\ UNCHANGED << lockOrientations, doorsOpen, 
                                           valvesOpen, waterLevel, 
                                           shipLocations, shipStates, 
                                           lockCommand, requests, permissions, 
                                           moved, stack, lock_, lock, reqSide, 
                                           perm, req, inUseLocks >>

ShipGoalReachedEast(self) == /\ pc[self] = "ShipGoalReachedEast"
                             /\ shipStates' = [shipStates EXCEPT ![self] = "goal_reached"]
                             /\ pc' = [pc EXCEPT ![self] = "ShipNextIteration"]
                             /\ UNCHANGED << lockOrientations, doorsOpen, 
                                             valvesOpen, waterLevel, 
                                             shipLocations, lockCommand, 
                                             requests, permissions, moved, 
                                             stack, lock_, lock, reqSide, perm, 
                                             req, inUseLocks >>

ShipMoveEast(self) == /\ pc[self] = "ShipMoveEast"
                      /\ IF perm[self].granted
                            THEN /\ Assert(doorsOpen[perm[self].lock][IF InLock(self) THEN "east" ELSE "west"], 
                                           "Failure of assertion at line 270, column 13.")
                                 /\ shipLocations' = [shipLocations EXCEPT ![self] = shipLocations[self] + 1]
                                 /\ moved' = [moved EXCEPT ![self] = TRUE]
                            ELSE /\ TRUE
                                 /\ UNCHANGED << shipLocations, moved >>
                      /\ pc' = [pc EXCEPT ![self] = "ShipNextIteration"]
                      /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                                      waterLevel, shipStates, lockCommand, 
                                      requests, permissions, stack, lock_, 
                                      lock, reqSide, perm, req, inUseLocks >>

ShipRequestWest(self) == /\ pc[self] = "ShipRequestWest"
                         /\ requests' = Append(requests, ([ship |-> self, lock |-> GetLock(shipLocations[self]+1), side |-> "west"]))
                         /\ pc' = [pc EXCEPT ![self] = "ShipWaitForWest"]
                         /\ UNCHANGED << lockOrientations, doorsOpen, 
                                         valvesOpen, waterLevel, shipLocations, 
                                         shipStates, lockCommand, permissions, 
                                         moved, stack, lock_, lock, reqSide, 
                                         perm, req, inUseLocks >>

ShipWaitForWest(self) == /\ pc[self] = "ShipWaitForWest"
                         /\ (permissions[self]) /= <<>>
                         /\ perm' = [perm EXCEPT ![self] = Head((permissions[self]))]
                         /\ permissions' = [permissions EXCEPT ![self] = Tail((permissions[self]))]
                         /\ Assert(perm'[self].lock = GetLock(shipLocations[self]+1), 
                                   "Failure of assertion at line 257, column 13.")
                         /\ pc' = [pc EXCEPT ![self] = "ShipMoveEast"]
                         /\ UNCHANGED << lockOrientations, doorsOpen, 
                                         valvesOpen, waterLevel, shipLocations, 
                                         shipStates, lockCommand, requests, 
                                         moved, stack, lock_, lock, reqSide, 
                                         req, inUseLocks >>

ShipRequestEastInLock(self) == /\ pc[self] = "ShipRequestEastInLock"
                               /\ requests' = Append(requests, ([ship |-> self, lock |-> GetLock(shipLocations[self]), side |-> "east"]))
                               /\ pc' = [pc EXCEPT ![self] = "ShipWaitForEastInLock"]
                               /\ UNCHANGED << lockOrientations, doorsOpen, 
                                               valvesOpen, waterLevel, 
                                               shipLocations, shipStates, 
                                               lockCommand, permissions, moved, 
                                               stack, lock_, lock, reqSide, 
                                               perm, req, inUseLocks >>

ShipWaitForEastInLock(self) == /\ pc[self] = "ShipWaitForEastInLock"
                               /\ (permissions[self]) /= <<>>
                               /\ perm' = [perm EXCEPT ![self] = Head((permissions[self]))]
                               /\ permissions' = [permissions EXCEPT ![self] = Tail((permissions[self]))]
                               /\ Assert(perm'[self].lock = GetLock(shipLocations[self]), 
                                         "Failure of assertion at line 265, column 13.")
                               /\ pc' = [pc EXCEPT ![self] = "ShipMoveEast"]
                               /\ UNCHANGED << lockOrientations, doorsOpen, 
                                               valvesOpen, waterLevel, 
                                               shipLocations, shipStates, 
                                               lockCommand, requests, moved, 
                                               stack, lock_, lock, reqSide, 
                                               req, inUseLocks >>

ShipTurnAround(self) == /\ pc[self] = "ShipTurnAround"
                        /\ shipStates' = [shipStates EXCEPT ![self] = IF shipLocations[self] = WestEnd THEN "go_to_east" ELSE "go_to_west"]
                        /\ pc' = [pc EXCEPT ![self] = "ShipNextIteration"]
                        /\ UNCHANGED << lockOrientations, doorsOpen, 
                                        valvesOpen, waterLevel, shipLocations, 
                                        lockCommand, requests, permissions, 
                                        moved, stack, lock_, lock, reqSide, 
                                        perm, req, inUseLocks >>

ShipGoalReachedWest(self) == /\ pc[self] = "ShipGoalReachedWest"
                             /\ shipStates' = [shipStates EXCEPT ![self] = "goal_reached"]
                             /\ pc' = [pc EXCEPT ![self] = "ShipNextIteration"]
                             /\ UNCHANGED << lockOrientations, doorsOpen, 
                                             valvesOpen, waterLevel, 
                                             shipLocations, lockCommand, 
                                             requests, permissions, moved, 
                                             stack, lock_, lock, reqSide, perm, 
                                             req, inUseLocks >>

ShipMoveWest(self) == /\ pc[self] = "ShipMoveWest"
                      /\ IF perm[self].granted
                            THEN /\ Assert(doorsOpen[perm[self].lock][IF InLock(self) THEN "west" ELSE "east"], 
                                           "Failure of assertion at line 301, column 13.")
                                 /\ shipLocations' = [shipLocations EXCEPT ![self] = shipLocations[self] - 1]
                                 /\ moved' = [moved EXCEPT ![self] = TRUE]
                            ELSE /\ TRUE
                                 /\ UNCHANGED << shipLocations, moved >>
                      /\ pc' = [pc EXCEPT ![self] = "ShipNextIteration"]
                      /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                                      waterLevel, shipStates, lockCommand, 
                                      requests, permissions, stack, lock_, 
                                      lock, reqSide, perm, req, inUseLocks >>

ShipRequestEast(self) == /\ pc[self] = "ShipRequestEast"
                         /\ requests' = Append(requests, ([ship |-> self, lock |-> GetLock(shipLocations[self]-1), side |-> "east"]))
                         /\ pc' = [pc EXCEPT ![self] = "ShipWaitForEast"]
                         /\ UNCHANGED << lockOrientations, doorsOpen, 
                                         valvesOpen, waterLevel, shipLocations, 
                                         shipStates, lockCommand, permissions, 
                                         moved, stack, lock_, lock, reqSide, 
                                         perm, req, inUseLocks >>

ShipWaitForEast(self) == /\ pc[self] = "ShipWaitForEast"
                         /\ (permissions[self]) /= <<>>
                         /\ perm' = [perm EXCEPT ![self] = Head((permissions[self]))]
                         /\ permissions' = [permissions EXCEPT ![self] = Tail((permissions[self]))]
                         /\ Assert(perm'[self].lock = GetLock(shipLocations[self]-1), 
                                   "Failure of assertion at line 288, column 13.")
                         /\ pc' = [pc EXCEPT ![self] = "ShipMoveWest"]
                         /\ UNCHANGED << lockOrientations, doorsOpen, 
                                         valvesOpen, waterLevel, shipLocations, 
                                         shipStates, lockCommand, requests, 
                                         moved, stack, lock_, lock, reqSide, 
                                         req, inUseLocks >>

ShipRequestWestInLock(self) == /\ pc[self] = "ShipRequestWestInLock"
                               /\ requests' = Append(requests, ([ship |-> self, lock |-> GetLock(shipLocations[self]), side |-> "west"]))
                               /\ pc' = [pc EXCEPT ![self] = "ShipWaitForWestInLock"]
                               /\ UNCHANGED << lockOrientations, doorsOpen, 
                                               valvesOpen, waterLevel, 
                                               shipLocations, shipStates, 
                                               lockCommand, permissions, moved, 
                                               stack, lock_, lock, reqSide, 
                                               perm, req, inUseLocks >>

ShipWaitForWestInLock(self) == /\ pc[self] = "ShipWaitForWestInLock"
                               /\ (permissions[self]) /= <<>>
                               /\ perm' = [perm EXCEPT ![self] = Head((permissions[self]))]
                               /\ permissions' = [permissions EXCEPT ![self] = Tail((permissions[self]))]
                               /\ Assert(perm'[self].lock = GetLock(shipLocations[self]), 
                                         "Failure of assertion at line 296, column 13.")
                               /\ pc' = [pc EXCEPT ![self] = "ShipMoveWest"]
                               /\ UNCHANGED << lockOrientations, doorsOpen, 
                                               valvesOpen, waterLevel, 
                                               shipLocations, shipStates, 
                                               lockCommand, requests, moved, 
                                               stack, lock_, lock, reqSide, 
                                               req, inUseLocks >>

shipProcess(self) == ShipNextIteration(self) \/ ShipGoalReachedEast(self)
                        \/ ShipMoveEast(self) \/ ShipRequestWest(self)
                        \/ ShipWaitForWest(self)
                        \/ ShipRequestEastInLock(self)
                        \/ ShipWaitForEastInLock(self)
                        \/ ShipTurnAround(self)
                        \/ ShipGoalReachedWest(self) \/ ShipMoveWest(self)
                        \/ ShipRequestEast(self) \/ ShipWaitForEast(self)
                        \/ ShipRequestWestInLock(self)
                        \/ ShipWaitForWestInLock(self)

MainLoop == /\ pc[0] = "MainLoop"
            /\ pc' = [pc EXCEPT ![0] = "ControlStart"]
            /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                            waterLevel, shipLocations, shipStates, lockCommand, 
                            requests, permissions, moved, stack, lock_, lock, 
                            reqSide, perm, req, inUseLocks >>

ControlStart == /\ pc[0] = "ControlStart"
                /\ requests # <<>>
                /\ requests /= <<>>
                /\ req' = Head(requests)
                /\ requests' = Tail(requests)
                /\ pc' = [pc EXCEPT ![0] = "EntryRequest"]
                /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                                waterLevel, shipLocations, shipStates, 
                                lockCommand, permissions, moved, stack, lock_, 
                                lock, reqSide, perm, inUseLocks >>

EntryRequest == /\ pc[0] = "EntryRequest"
                /\ IF ~IsLock(shipLocations[req.ship])
                      THEN /\ IF inUseLocks[req.lock] = TRUE
                                 THEN /\ permissions' = [permissions EXCEPT ![req.ship] = Append((permissions[req.ship]), ([lock |-> req.lock, granted |-> FALSE]))]
                                      /\ pc' = [pc EXCEPT ![0] = "ControlStart"]
                                 ELSE /\ IF numShipsAtLoc(lockLocation(req.lock + 1)) >= 2
                                            THEN /\ IF shipStates[req.ship] = "go_to_east"
                                                       THEN /\ IF allHeadedWest(lockLocation(req.lock + 1))
                                                                  THEN /\ permissions' = [permissions EXCEPT ![req.ship] = Append((permissions[req.ship]), ([lock |-> req.lock, granted |-> FALSE]))]
                                                                       /\ pc' = [pc EXCEPT ![0] = "ControlStart"]
                                                                  ELSE /\ pc' = [pc EXCEPT ![0] = "CloseBothDoorsBeforeEntry"]
                                                                       /\ UNCHANGED permissions
                                                       ELSE /\ IF shipStates[req.ship] = "go_to_west"
                                                                  THEN /\ IF allHeadedEast(lockLocation(req.lock + 1))
                                                                             THEN /\ permissions' = [permissions EXCEPT ![req.ship] = Append((permissions[req.ship]), ([lock |-> req.lock, granted |-> FALSE]))]
                                                                                  /\ pc' = [pc EXCEPT ![0] = "ControlStart"]
                                                                             ELSE /\ pc' = [pc EXCEPT ![0] = "CloseBothDoorsBeforeEntry"]
                                                                                  /\ UNCHANGED permissions
                                                                  ELSE /\ pc' = [pc EXCEPT ![0] = "CloseBothDoorsBeforeEntry"]
                                                                       /\ UNCHANGED permissions
                                            ELSE /\ pc' = [pc EXCEPT ![0] = "CloseBothDoorsBeforeEntry"]
                                                 /\ UNCHANGED permissions
                      ELSE /\ pc' = [pc EXCEPT ![0] = "ExitRequest"]
                           /\ UNCHANGED permissions
                /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                                waterLevel, shipLocations, shipStates, 
                                lockCommand, requests, moved, stack, lock_, 
                                lock, reqSide, perm, req, inUseLocks >>

CloseBothDoorsBeforeEntry == /\ pc[0] = "CloseBothDoorsBeforeEntry"
                             /\ /\ lock_' = [lock_ EXCEPT ![0] = req.lock]
                                /\ stack' = [stack EXCEPT ![0] = << [ procedure |->  "closeAllDoors",
                                                                      pc        |->  "AdjustWaterToEntraceLevel",
                                                                      lock_     |->  lock_[0] ] >>
                                                                  \o stack[0]]
                             /\ pc' = [pc EXCEPT ![0] = "CloseEastDoor"]
                             /\ UNCHANGED << lockOrientations, doorsOpen, 
                                             valvesOpen, waterLevel, 
                                             shipLocations, shipStates, 
                                             lockCommand, requests, 
                                             permissions, moved, lock, reqSide, 
                                             perm, req, inUseLocks >>

AdjustWaterToEntraceLevel == /\ pc[0] = "AdjustWaterToEntraceLevel"
                             /\ /\ lock' = [lock EXCEPT ![0] = req.lock]
                                /\ reqSide' = [reqSide EXCEPT ![0] = req.side]
                                /\ stack' = [stack EXCEPT ![0] = << [ procedure |->  "adjustWaterToRequestLevel",
                                                                      pc        |->  "OpenDoorForEntry",
                                                                      lock      |->  lock[0],
                                                                      reqSide   |->  reqSide[0] ] >>
                                                                  \o stack[0]]
                             /\ pc' = [pc EXCEPT ![0] = "CheckWaterLevelSide"]
                             /\ UNCHANGED << lockOrientations, doorsOpen, 
                                             valvesOpen, waterLevel, 
                                             shipLocations, shipStates, 
                                             lockCommand, requests, 
                                             permissions, moved, lock_, perm, 
                                             req, inUseLocks >>

OpenDoorForEntry == /\ pc[0] = "OpenDoorForEntry"
                    /\ lockCommand' = [lockCommand EXCEPT ![req.lock] = [command |-> "change_door", open |-> TRUE, side|-> req.side]]
                    /\ pc' = [pc EXCEPT ![0] = "DoorOpenForEntry"]
                    /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                                    waterLevel, shipLocations, shipStates, 
                                    requests, permissions, moved, stack, lock_, 
                                    lock, reqSide, perm, req, inUseLocks >>

DoorOpenForEntry == /\ pc[0] = "DoorOpenForEntry"
                    /\ lockCommand[req.lock].command = "finished"
                    /\ pc' = [pc EXCEPT ![0] = "WriteEntryPermission"]
                    /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                                    waterLevel, shipLocations, shipStates, 
                                    lockCommand, requests, permissions, moved, 
                                    stack, lock_, lock, reqSide, perm, req, 
                                    inUseLocks >>

WriteEntryPermission == /\ pc[0] = "WriteEntryPermission"
                        /\ permissions' = [permissions EXCEPT ![req.ship] = Append((permissions[req.ship]), ([lock |-> req.lock, granted |-> TRUE]))]
                        /\ pc' = [pc EXCEPT ![0] = "WaitForShipToEnter"]
                        /\ UNCHANGED << lockOrientations, doorsOpen, 
                                        valvesOpen, waterLevel, shipLocations, 
                                        shipStates, lockCommand, requests, 
                                        moved, stack, lock_, lock, reqSide, 
                                        perm, req, inUseLocks >>

WaitForShipToEnter == /\ pc[0] = "WaitForShipToEnter"
                      /\ moved[req.ship] = TRUE
                      /\ pc' = [pc EXCEPT ![0] = "CloseDoorAfterEntry"]
                      /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                                      waterLevel, shipLocations, shipStates, 
                                      lockCommand, requests, permissions, 
                                      moved, stack, lock_, lock, reqSide, perm, 
                                      req, inUseLocks >>

CloseDoorAfterEntry == /\ pc[0] = "CloseDoorAfterEntry"
                       /\ lockCommand' = [lockCommand EXCEPT ![req.lock] = [command |-> "change_door", open |-> FALSE, side|-> req.side]]
                       /\ pc' = [pc EXCEPT ![0] = "DoorClosedAfterEntry"]
                       /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                                       waterLevel, shipLocations, shipStates, 
                                       requests, permissions, moved, stack, 
                                       lock_, lock, reqSide, perm, req, 
                                       inUseLocks >>

DoorClosedAfterEntry == /\ pc[0] = "DoorClosedAfterEntry"
                        /\ lockCommand[req.lock].command = "finished"
                        /\ perm' = [perm EXCEPT ![0][(req.ship)].granted = FALSE]
                        /\ moved' = [moved EXCEPT ![(req.ship)] = FALSE]
                        /\ pc' = [pc EXCEPT ![0] = "ControlStart"]
                        /\ UNCHANGED << lockOrientations, doorsOpen, 
                                        valvesOpen, waterLevel, shipLocations, 
                                        shipStates, lockCommand, requests, 
                                        permissions, stack, lock_, lock, 
                                        reqSide, req, inUseLocks >>

ExitRequest == /\ pc[0] = "ExitRequest"
               /\ IF IsLock(shipLocations[req.ship])
                     THEN /\ Assert(lockLocation(req.lock) = shipLocations[req.ship], 
                                    "Failure of assertion at line 393, column 17.")
                          /\ pc' = [pc EXCEPT ![0] = "AdjustWaterToExitLevel"]
                     ELSE /\ pc' = [pc EXCEPT ![0] = "MainLoop"]
               /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                               waterLevel, shipLocations, shipStates, 
                               lockCommand, requests, permissions, moved, 
                               stack, lock_, lock, reqSide, perm, req, 
                               inUseLocks >>

AdjustWaterToExitLevel == /\ pc[0] = "AdjustWaterToExitLevel"
                          /\ /\ lock' = [lock EXCEPT ![0] = req.lock]
                             /\ reqSide' = [reqSide EXCEPT ![0] = req.side]
                             /\ stack' = [stack EXCEPT ![0] = << [ procedure |->  "adjustWaterToRequestLevel",
                                                                   pc        |->  "OpenDoorForExit",
                                                                   lock      |->  lock[0],
                                                                   reqSide   |->  reqSide[0] ] >>
                                                               \o stack[0]]
                          /\ pc' = [pc EXCEPT ![0] = "CheckWaterLevelSide"]
                          /\ UNCHANGED << lockOrientations, doorsOpen, 
                                          valvesOpen, waterLevel, 
                                          shipLocations, shipStates, 
                                          lockCommand, requests, permissions, 
                                          moved, lock_, perm, req, inUseLocks >>

OpenDoorForExit == /\ pc[0] = "OpenDoorForExit"
                   /\ lockCommand' = [lockCommand EXCEPT ![req.lock] = [command |-> "change_door", open |-> TRUE, side|-> req.side]]
                   /\ pc' = [pc EXCEPT ![0] = "DoorOpenForExit"]
                   /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                                   waterLevel, shipLocations, shipStates, 
                                   requests, permissions, moved, stack, lock_, 
                                   lock, reqSide, perm, req, inUseLocks >>

DoorOpenForExit == /\ pc[0] = "DoorOpenForExit"
                   /\ lockCommand[req.lock].command = "finished"
                   /\ pc' = [pc EXCEPT ![0] = "WriteExitPermission"]
                   /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                                   waterLevel, shipLocations, shipStates, 
                                   lockCommand, requests, permissions, moved, 
                                   stack, lock_, lock, reqSide, perm, req, 
                                   inUseLocks >>

WriteExitPermission == /\ pc[0] = "WriteExitPermission"
                       /\ permissions' = [permissions EXCEPT ![req.ship] = Append((permissions[req.ship]), ([lock |-> req.lock, granted |-> TRUE]))]
                       /\ pc' = [pc EXCEPT ![0] = "WaitForShipToExit"]
                       /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                                       waterLevel, shipLocations, shipStates, 
                                       lockCommand, requests, moved, stack, 
                                       lock_, lock, reqSide, perm, req, 
                                       inUseLocks >>

WaitForShipToExit == /\ pc[0] = "WaitForShipToExit"
                     /\ moved[req.ship] = TRUE
                     /\ pc' = [pc EXCEPT ![0] = "CloseDoorAfterExit"]
                     /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                                     waterLevel, shipLocations, shipStates, 
                                     lockCommand, requests, permissions, moved, 
                                     stack, lock_, lock, reqSide, perm, req, 
                                     inUseLocks >>

CloseDoorAfterExit == /\ pc[0] = "CloseDoorAfterExit"
                      /\ lockCommand' = [lockCommand EXCEPT ![req.lock] = [command |-> "change_door", open |-> FALSE, side|-> req.side]]
                      /\ pc' = [pc EXCEPT ![0] = "DoorClosedAfterExit"]
                      /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                                      waterLevel, shipLocations, shipStates, 
                                      requests, permissions, moved, stack, 
                                      lock_, lock, reqSide, perm, req, 
                                      inUseLocks >>

DoorClosedAfterExit == /\ pc[0] = "DoorClosedAfterExit"
                       /\ lockCommand[req.lock].command = "finished"
                       /\ perm' = [perm EXCEPT ![0][(req.ship)].granted = FALSE]
                       /\ moved' = [moved EXCEPT ![(req.ship)] = FALSE]
                       /\ pc' = [pc EXCEPT ![0] = "ControlStart"]
                       /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                                       waterLevel, shipLocations, shipStates, 
                                       lockCommand, requests, permissions, 
                                       stack, lock_, lock, reqSide, req, 
                                       inUseLocks >>

controlProcess == MainLoop \/ ControlStart \/ EntryRequest
                     \/ CloseBothDoorsBeforeEntry
                     \/ AdjustWaterToEntraceLevel \/ OpenDoorForEntry
                     \/ DoorOpenForEntry \/ WriteEntryPermission
                     \/ WaitForShipToEnter \/ CloseDoorAfterEntry
                     \/ DoorClosedAfterEntry \/ ExitRequest
                     \/ AdjustWaterToExitLevel \/ OpenDoorForExit
                     \/ DoorOpenForExit \/ WriteExitPermission
                     \/ WaitForShipToExit \/ CloseDoorAfterExit
                     \/ DoorClosedAfterExit

Next == controlProcess
           \/ (\E self \in ProcSet:  \/ closeAllDoors(self)
                                     \/ adjustWaterToRequestLevel(self))
           \/ (\E self \in Locks: lockProcess(self))
           \/ (\E self \in Ships: shipProcess(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Locks : WF_vars(lockProcess(self))
        /\ \A self \in Ships : WF_vars(shipProcess(self))
        /\ /\ WF_vars(controlProcess)
           /\ WF_vars(closeAllDoors(0))
           /\ WF_vars(adjustWaterToRequestLevel(0))

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Thu Oct 16 23:08:00 CEST 2025 by iyladakeekarjai
\* Last modified Wed Oct 15 23:54:03 CEST 2025 by 20241642
\* Last modified Wed Oct 15 10:06:38 CEST 2025 by 20241642
\* Last modified Wed Sep 24 12:00:55 CEST 2025 by mvolk
\* Created Thu Aug 28 11:30:07 CEST 2025 by mvolk
