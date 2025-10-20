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

\* check if a ship has requested entry for a given lock
shipRequestsEnterLock(shipR, lockR) == \E i \in 1..Len(requests) : (requests[i].ship = shipR) /\ (requests[i].lock = lockR)



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
DoorsMutex == (\A l \in Locks : ~(doorsOpen[l]["west"] /\ doorsOpen[l]["east"]))
\* When the lower/higher pair of doors is open, the higher/lower valve is closed.
DoorsOpenValvesClosed == (\A l \in Locks : (doorsOpen[l][LowSide(lockOrientations[l])] => ~valvesOpen[l]["high"]) /\
                                             (doorsOpen[l][HighSide(lockOrientations[l])] => ~valvesOpen[l]["low"]))

\* The lower/higher pair of doors is only open when the water level in the lock is low/high
DoorsOpenWaterlevelRight  == (\A l \in Locks : (doorsOpen[l][LowSide(lockOrientations[l])] => (waterLevel[l] = "low")) /\
                                                 (doorsOpen[l][HighSide(lockOrientations[l])] => (waterLevel[l] = "high")))

\* Always if a ship requests to enter a lock, the ship will eventually be inside the lock.

RequestLockFulfilled == [](\A s \in Ships: \A l \in Locks: (shipRequestsEnterLock(s, l) = TRUE) => <>(shipLocations[s] = lockLocation(l)))

\* RequestLockFulfilled == [](\A s \in Ships: \A \l in Locks: (requests /= << >> /\ (requests[Len(requests)].ship = s /\ requests[Len(requests)].lock = l) => <>(shipLocations[s] = lockLocation(l))))


\* WORKS RequestLockFulfilled == [](Len(requests) > 0 => (\A i \in 1..Len(requests) : (requests[i].side = "east" \/ requests[i].side = "west")))
\* DOESN'T WORK RequestLockFulfilled == [](Len(requests) > 0 => (\A i \in 1..Len(requests) : <>(requests[i].side = "east")))

\* Water level is infinitely many times high/low DONE
WaterlevelChange == \A l \in Locks : ([]<>(waterLevel[l] = "low") /\ []<>(waterLevel[l] = "high"))

\* Infinitely many times each ship does requests DONE?
RequestsShips == \A s \in Ships : []<>(\E r \in 1..Len(requests) : requests[r].ship = s)

\* Infinitely many times each ship reaches its end location DONE
\* ShipsReachGoals == \A s \in Ships: ([]<>(shipLocations[s] = EastEnd) /\ []<>(shipLocations[s] = WestEnd))
ShipsReachGoals == [](\A s \in Ships : <> (shipStates[s] = "goal_reached"))


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

\* Changes back the ship's moved to FALSE
macro restoreShipState(ship) begin
    moved[ship] := FALSE
end macro


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
    \* check that the request is for chamber entry
    if ~IsLock(shipLocations[req.ship]) then
        \*************************
        \* Terminating Conditions
        \************************* 
        \* deny permission if the lock is currently occupied
        if inUseLocks[req.lock] = TRUE then
            \* DON'T deny permission
            \* just add request back
            write(requests, req);
            goto ControlStart; \* break
                                
        end if;               
                
    \**************
    \* Request OK
    \**************
    \* close all doors (if they were not already closed)
    CloseEastDoorEntry:
                lockCommand[req.lock] := [command |-> "change_door", open |-> FALSE, side |-> "east"];
    WaitEastDoorClosedEntry:
                await lockCommand[req.lock].command = "finished";
    CloseWestDoorEntry:
                lockCommand[req.lock] := [command |-> "change_door", open |-> FALSE, side |-> "west"];
    WaitWestDoorClosedEntry:
                await lockCommand[req.lock].command = "finished";
    \* adjust water level according to requested side
    \* check if requested side is the low side
    CheckWaterLevelSideEntry:
                if req.side = LowSide(lockOrientations[req.lock]) then
                \* adjust water level down
    OpenLowValveEntry:
                    lockCommand[req.lock] := [command |-> "change_valve", open |-> TRUE, side |-> "low"];
    WaitLowValveOpenedEntry:
                    await lockCommand[req.lock].command = "finished";
    CloseLowValveEntry:
                    lockCommand[req.lock] := [command |-> "change_valve", open |-> FALSE, side |-> "low"];
    WaitLowValveClosedEntry:
                    await lockCommand[req.lock].command = "finished";
                \* requested side is the high side
                elsif req.side = HighSide(lockOrientations[req.lock]) then
    \* adjust water level up
    OpenHighValveEntry:
                    lockCommand[req.lock] := [command |-> "change_valve", open |-> TRUE, side |-> "high"];
    WaitHighValveOpenedEntry:
                    await lockCommand[req.lock].command = "finished";
    CloseHighValveEntry:
                    lockCommand[req.lock] := [command |-> "change_valve", open |-> FALSE, side |-> "high"];
    WaitHighValveClosedEntry:
                    await lockCommand[req.lock].command = "finished";
                end if;
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
                inUseLocks[req.lock] := TRUE;
                restoreShipState(req.ship);
                goto ControlStart; 
    end if;     
    ExitRequest:
    \*************************
    \* Terminating Conditions
    \*************************
    if IsLock(shipLocations[req.ship]) then
        assert lockLocation(req.lock) = shipLocations[req.ship];
                
        if shipStates[req.ship] = "go_to_east" then
        \* number of ships beyond the lock is greater than max
            if numShipsAtLoc(shipLocations[req.ship] + 1) >= 2 then
                write(permissions[req.ship], [lock |-> req.lock, granted |-> FALSE]);
                goto ControlStart;
            end if;
        elsif shipStates[req.ship] = "go_to_west" then       
            if numShipsAtLoc(shipLocations[req.ship] - 1) >= 2 then
                write(permissions[req.ship], [lock |-> req.lock, granted |-> FALSE]);
                goto ControlStart;
            end if;
        end if;
                
    \**************
    \* Request OK
    \**************
    \* adjust water to exit level
    \* All doors must already be closed at this point
    \* Adjust water level
    \* adjust water level according to requested side
    \* check if requested side is the low side
    CheckWaterLevelSideExit:
        if req.side = LowSide(lockOrientations[req.lock]) then
            \* adjust water level down
    OpenLowValveExit:
                    lockCommand[req.lock] := [command |-> "change_valve", open |-> TRUE, side |-> "low"];
    WaitLowValveOpenedExit:
                    await lockCommand[req.lock].command = "finished";
    CloseLowValveExit:
                    lockCommand[req.lock] := [command |-> "change_valve", open |-> FALSE, side |-> "low"];
    WaitLowValveClosedExit:
                    await lockCommand[req.lock].command = "finished";
        \* requested side is the high side
        elsif req.side = HighSide(lockOrientations[req.lock]) then
            \* adjust water level up
    OpenHighValveExit:
                    lockCommand[req.lock] := [command |-> "change_valve", open |-> TRUE, side |-> "high"];
    WaitHighValveOpenedExit:
                    await lockCommand[req.lock].command = "finished";
    CloseHighValveExit:
                    lockCommand[req.lock] := [command |-> "change_valve", open |-> FALSE, side |-> "high"];
    WaitHighValveClosedExit:
                    await lockCommand[req.lock].command = "finished";
        end if;
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
                inUseLocks[req.lock] := FALSE;
                restoreShipState(req.ship);
                goto ControlStart;         
        end if;
    end while;
end process;


end algorithm; *)


\* BEGIN TRANSLATION (chksum(pcal) = "f7ac2f39" /\ chksum(tla) = "a909a869")
VARIABLES lockOrientations, doorsOpen, valvesOpen, waterLevel, shipLocations, 
          shipStates, lockCommand, requests, permissions, moved, pc

(* define statement *)
InLock(ship) == IsLock(shipLocations[ship])


lockLocation(lock) == lock + (lock - 1)


shipsAtLoc(loc) == {s \in Ships: shipLocations[s] = loc}


numShipsAtLoc(loc) == Cardinality(shipsAtLoc(loc))


allHeadedEast(loc) == \A s \in shipsAtLoc(loc) : shipStates[s] = "go_to_east"


allHeadedWest(loc) == \A s \in shipsAtLoc(loc) : shipStates[s] = "go_to_west"


isDoorsClosed(lock) == doorsOpen[lock] = [ls \in LockSide |-> FALSE]


shipRequestsEnterLock(shipR, lockR) == \E i \in 1..Len(requests) : (requests[i].ship = shipR) /\ (requests[i].lock = lockR)







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






DoorsMutex == (\A l \in Locks : ~(doorsOpen[l]["west"] /\ doorsOpen[l]["east"]))

DoorsOpenValvesClosed == (\A l \in Locks : (doorsOpen[l][LowSide(lockOrientations[l])] => ~valvesOpen[l]["high"]) /\
                                             (doorsOpen[l][HighSide(lockOrientations[l])] => ~valvesOpen[l]["low"]))


DoorsOpenWaterlevelRight  == (\A l \in Locks : (doorsOpen[l][LowSide(lockOrientations[l])] => (waterLevel[l] = "low")) /\
                                                 (doorsOpen[l][HighSide(lockOrientations[l])] => (waterLevel[l] = "high")))



RequestLockFulfilled == [](\A s \in Ships: \A l \in Locks: (shipRequestsEnterLock(s, l) = TRUE) => <>(shipLocations[s] = lockLocation(l)))








WaterlevelChange == \A l \in Locks : ([]<>(waterLevel[l] = "low") /\ []<>(waterLevel[l] = "high"))


RequestsShips == \A s \in Ships : []<>(\E r \in 1..Len(requests) : requests[r].ship = s)



ShipsReachGoals == [](\A s \in Ships : <> (shipStates[s] = "goal_reached"))



MaxShipsPerLocation == (\A loc \in Locations : IF IsLock(loc) THEN Cardinality({\A s \in Ships : shipLocations[s] = loc}) \leq MaxShipsLock
                                                 ELSE Cardinality({\A s \in Ships : shipLocations[s] = loc}) \leq MaxShipsLocation)

VARIABLES perm, req, inUseLocks

vars == << lockOrientations, doorsOpen, valvesOpen, waterLevel, shipLocations, 
           shipStates, lockCommand, requests, permissions, moved, pc, perm, 
           req, inUseLocks >>

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
        (* Process shipProcess *)
        /\ perm = [self \in Ships |-> [lock |-> 1, granted |-> FALSE]]
        (* Process controlProcess *)
        /\ req = [ship |-> 0, lock |-> 0, side |-> "east"]
        /\ inUseLocks = [l \in Locks |-> FALSE]
        /\ pc = [self \in ProcSet |-> CASE self \in Locks -> "LockWaitForCommand"
                                        [] self \in Ships -> "ShipNextIteration"
                                        [] self = 0 -> "MainLoop"]

LockWaitForCommand(self) == /\ pc[self] = "LockWaitForCommand"
                            /\ lockCommand[self].command /= "finished"
                            /\ IF lockCommand[self].command = "change_door"
                                  THEN /\ doorsOpen' = [doorsOpen EXCEPT ![self][lockCommand[self].side] = lockCommand[self].open]
                                       /\ UNCHANGED valvesOpen
                                  ELSE /\ IF lockCommand[self].command = "change_valve"
                                             THEN /\ valvesOpen' = [valvesOpen EXCEPT ![self][lockCommand[self].side] = lockCommand[self].open]
                                             ELSE /\ Assert(FALSE, 
                                                            "Failure of assertion at line 193, column 9.")
                                                  /\ UNCHANGED valvesOpen
                                       /\ UNCHANGED doorsOpen
                            /\ pc' = [pc EXCEPT ![self] = "LockUpdateWaterLevel"]
                            /\ UNCHANGED << lockOrientations, waterLevel, 
                                            shipLocations, shipStates, 
                                            lockCommand, requests, permissions, 
                                            moved, perm, req, inUseLocks >>

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
                                              perm, req, inUseLocks >>

LockCommandFinished(self) == /\ pc[self] = "LockCommandFinished"
                             /\ lockCommand' = [lockCommand EXCEPT ![self].command = "finished"]
                             /\ pc' = [pc EXCEPT ![self] = "LockWaitForCommand"]
                             /\ UNCHANGED << lockOrientations, doorsOpen, 
                                             valvesOpen, waterLevel, 
                                             shipLocations, shipStates, 
                                             requests, permissions, moved, 
                                             perm, req, inUseLocks >>

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
                                                           "Failure of assertion at line 275, column 9.")
                                                 /\ pc' = [pc EXCEPT ![self] = "ShipTurnAround"]
                           /\ UNCHANGED << lockOrientations, doorsOpen, 
                                           valvesOpen, waterLevel, 
                                           shipLocations, shipStates, 
                                           lockCommand, requests, permissions, 
                                           moved, perm, req, inUseLocks >>

ShipGoalReachedEast(self) == /\ pc[self] = "ShipGoalReachedEast"
                             /\ shipStates' = [shipStates EXCEPT ![self] = "goal_reached"]
                             /\ pc' = [pc EXCEPT ![self] = "ShipNextIteration"]
                             /\ UNCHANGED << lockOrientations, doorsOpen, 
                                             valvesOpen, waterLevel, 
                                             shipLocations, lockCommand, 
                                             requests, permissions, moved, 
                                             perm, req, inUseLocks >>

ShipMoveEast(self) == /\ pc[self] = "ShipMoveEast"
                      /\ IF perm[self].granted
                            THEN /\ Assert(doorsOpen[perm[self].lock][IF InLock(self) THEN "east" ELSE "west"], 
                                           "Failure of assertion at line 237, column 13.")
                                 /\ shipLocations' = [shipLocations EXCEPT ![self] = shipLocations[self] + 1]
                                 /\ moved' = [moved EXCEPT ![self] = TRUE]
                            ELSE /\ TRUE
                                 /\ UNCHANGED << shipLocations, moved >>
                      /\ pc' = [pc EXCEPT ![self] = "ShipNextIteration"]
                      /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                                      waterLevel, shipStates, lockCommand, 
                                      requests, permissions, perm, req, 
                                      inUseLocks >>

ShipRequestWest(self) == /\ pc[self] = "ShipRequestWest"
                         /\ requests' = Append(requests, ([ship |-> self, lock |-> GetLock(shipLocations[self]+1), side |-> "west"]))
                         /\ pc' = [pc EXCEPT ![self] = "ShipWaitForWest"]
                         /\ UNCHANGED << lockOrientations, doorsOpen, 
                                         valvesOpen, waterLevel, shipLocations, 
                                         shipStates, lockCommand, permissions, 
                                         moved, perm, req, inUseLocks >>

ShipWaitForWest(self) == /\ pc[self] = "ShipWaitForWest"
                         /\ (permissions[self]) /= <<>>
                         /\ perm' = [perm EXCEPT ![self] = Head((permissions[self]))]
                         /\ permissions' = [permissions EXCEPT ![self] = Tail((permissions[self]))]
                         /\ Assert(perm'[self].lock = GetLock(shipLocations[self]+1), 
                                   "Failure of assertion at line 224, column 13.")
                         /\ pc' = [pc EXCEPT ![self] = "ShipMoveEast"]
                         /\ UNCHANGED << lockOrientations, doorsOpen, 
                                         valvesOpen, waterLevel, shipLocations, 
                                         shipStates, lockCommand, requests, 
                                         moved, req, inUseLocks >>

ShipRequestEastInLock(self) == /\ pc[self] = "ShipRequestEastInLock"
                               /\ requests' = Append(requests, ([ship |-> self, lock |-> GetLock(shipLocations[self]), side |-> "east"]))
                               /\ pc' = [pc EXCEPT ![self] = "ShipWaitForEastInLock"]
                               /\ UNCHANGED << lockOrientations, doorsOpen, 
                                               valvesOpen, waterLevel, 
                                               shipLocations, shipStates, 
                                               lockCommand, permissions, moved, 
                                               perm, req, inUseLocks >>

ShipWaitForEastInLock(self) == /\ pc[self] = "ShipWaitForEastInLock"
                               /\ (permissions[self]) /= <<>>
                               /\ perm' = [perm EXCEPT ![self] = Head((permissions[self]))]
                               /\ permissions' = [permissions EXCEPT ![self] = Tail((permissions[self]))]
                               /\ Assert(perm'[self].lock = GetLock(shipLocations[self]), 
                                         "Failure of assertion at line 232, column 13.")
                               /\ pc' = [pc EXCEPT ![self] = "ShipMoveEast"]
                               /\ UNCHANGED << lockOrientations, doorsOpen, 
                                               valvesOpen, waterLevel, 
                                               shipLocations, shipStates, 
                                               lockCommand, requests, moved, 
                                               req, inUseLocks >>

ShipTurnAround(self) == /\ pc[self] = "ShipTurnAround"
                        /\ shipStates' = [shipStates EXCEPT ![self] = IF shipLocations[self] = WestEnd THEN "go_to_east" ELSE "go_to_west"]
                        /\ pc' = [pc EXCEPT ![self] = "ShipNextIteration"]
                        /\ UNCHANGED << lockOrientations, doorsOpen, 
                                        valvesOpen, waterLevel, shipLocations, 
                                        lockCommand, requests, permissions, 
                                        moved, perm, req, inUseLocks >>

ShipGoalReachedWest(self) == /\ pc[self] = "ShipGoalReachedWest"
                             /\ shipStates' = [shipStates EXCEPT ![self] = "goal_reached"]
                             /\ pc' = [pc EXCEPT ![self] = "ShipNextIteration"]
                             /\ UNCHANGED << lockOrientations, doorsOpen, 
                                             valvesOpen, waterLevel, 
                                             shipLocations, lockCommand, 
                                             requests, permissions, moved, 
                                             perm, req, inUseLocks >>

ShipMoveWest(self) == /\ pc[self] = "ShipMoveWest"
                      /\ IF perm[self].granted
                            THEN /\ Assert(doorsOpen[perm[self].lock][IF InLock(self) THEN "west" ELSE "east"], 
                                           "Failure of assertion at line 268, column 13.")
                                 /\ shipLocations' = [shipLocations EXCEPT ![self] = shipLocations[self] - 1]
                                 /\ moved' = [moved EXCEPT ![self] = TRUE]
                            ELSE /\ TRUE
                                 /\ UNCHANGED << shipLocations, moved >>
                      /\ pc' = [pc EXCEPT ![self] = "ShipNextIteration"]
                      /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                                      waterLevel, shipStates, lockCommand, 
                                      requests, permissions, perm, req, 
                                      inUseLocks >>

ShipRequestEast(self) == /\ pc[self] = "ShipRequestEast"
                         /\ requests' = Append(requests, ([ship |-> self, lock |-> GetLock(shipLocations[self]-1), side |-> "east"]))
                         /\ pc' = [pc EXCEPT ![self] = "ShipWaitForEast"]
                         /\ UNCHANGED << lockOrientations, doorsOpen, 
                                         valvesOpen, waterLevel, shipLocations, 
                                         shipStates, lockCommand, permissions, 
                                         moved, perm, req, inUseLocks >>

ShipWaitForEast(self) == /\ pc[self] = "ShipWaitForEast"
                         /\ (permissions[self]) /= <<>>
                         /\ perm' = [perm EXCEPT ![self] = Head((permissions[self]))]
                         /\ permissions' = [permissions EXCEPT ![self] = Tail((permissions[self]))]
                         /\ Assert(perm'[self].lock = GetLock(shipLocations[self]-1), 
                                   "Failure of assertion at line 255, column 13.")
                         /\ pc' = [pc EXCEPT ![self] = "ShipMoveWest"]
                         /\ UNCHANGED << lockOrientations, doorsOpen, 
                                         valvesOpen, waterLevel, shipLocations, 
                                         shipStates, lockCommand, requests, 
                                         moved, req, inUseLocks >>

ShipRequestWestInLock(self) == /\ pc[self] = "ShipRequestWestInLock"
                               /\ requests' = Append(requests, ([ship |-> self, lock |-> GetLock(shipLocations[self]), side |-> "west"]))
                               /\ pc' = [pc EXCEPT ![self] = "ShipWaitForWestInLock"]
                               /\ UNCHANGED << lockOrientations, doorsOpen, 
                                               valvesOpen, waterLevel, 
                                               shipLocations, shipStates, 
                                               lockCommand, permissions, moved, 
                                               perm, req, inUseLocks >>

ShipWaitForWestInLock(self) == /\ pc[self] = "ShipWaitForWestInLock"
                               /\ (permissions[self]) /= <<>>
                               /\ perm' = [perm EXCEPT ![self] = Head((permissions[self]))]
                               /\ permissions' = [permissions EXCEPT ![self] = Tail((permissions[self]))]
                               /\ Assert(perm'[self].lock = GetLock(shipLocations[self]), 
                                         "Failure of assertion at line 263, column 13.")
                               /\ pc' = [pc EXCEPT ![self] = "ShipMoveWest"]
                               /\ UNCHANGED << lockOrientations, doorsOpen, 
                                               valvesOpen, waterLevel, 
                                               shipLocations, shipStates, 
                                               lockCommand, requests, moved, 
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
                            requests, permissions, moved, perm, req, 
                            inUseLocks >>

ControlStart == /\ pc[0] = "ControlStart"
                /\ requests # <<>>
                /\ requests /= <<>>
                /\ req' = Head(requests)
                /\ requests' = Tail(requests)
                /\ pc' = [pc EXCEPT ![0] = "EntryRequest"]
                /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                                waterLevel, shipLocations, shipStates, 
                                lockCommand, permissions, moved, perm, 
                                inUseLocks >>

EntryRequest == /\ pc[0] = "EntryRequest"
                /\ IF ~IsLock(shipLocations[req.ship])
                      THEN /\ IF inUseLocks[req.lock] = TRUE
                                 THEN /\ requests' = Append(requests, req)
                                      /\ pc' = [pc EXCEPT ![0] = "ControlStart"]
                                 ELSE /\ pc' = [pc EXCEPT ![0] = "CloseEastDoorEntry"]
                                      /\ UNCHANGED requests
                      ELSE /\ pc' = [pc EXCEPT ![0] = "ExitRequest"]
                           /\ UNCHANGED requests
                /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                                waterLevel, shipLocations, shipStates, 
                                lockCommand, permissions, moved, perm, req, 
                                inUseLocks >>

CloseEastDoorEntry == /\ pc[0] = "CloseEastDoorEntry"
                      /\ lockCommand' = [lockCommand EXCEPT ![req.lock] = [command |-> "change_door", open |-> FALSE, side |-> "east"]]
                      /\ pc' = [pc EXCEPT ![0] = "WaitEastDoorClosedEntry"]
                      /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                                      waterLevel, shipLocations, shipStates, 
                                      requests, permissions, moved, perm, req, 
                                      inUseLocks >>

WaitEastDoorClosedEntry == /\ pc[0] = "WaitEastDoorClosedEntry"
                           /\ lockCommand[req.lock].command = "finished"
                           /\ pc' = [pc EXCEPT ![0] = "CloseWestDoorEntry"]
                           /\ UNCHANGED << lockOrientations, doorsOpen, 
                                           valvesOpen, waterLevel, 
                                           shipLocations, shipStates, 
                                           lockCommand, requests, permissions, 
                                           moved, perm, req, inUseLocks >>

CloseWestDoorEntry == /\ pc[0] = "CloseWestDoorEntry"
                      /\ lockCommand' = [lockCommand EXCEPT ![req.lock] = [command |-> "change_door", open |-> FALSE, side |-> "west"]]
                      /\ pc' = [pc EXCEPT ![0] = "WaitWestDoorClosedEntry"]
                      /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                                      waterLevel, shipLocations, shipStates, 
                                      requests, permissions, moved, perm, req, 
                                      inUseLocks >>

WaitWestDoorClosedEntry == /\ pc[0] = "WaitWestDoorClosedEntry"
                           /\ lockCommand[req.lock].command = "finished"
                           /\ pc' = [pc EXCEPT ![0] = "CheckWaterLevelSideEntry"]
                           /\ UNCHANGED << lockOrientations, doorsOpen, 
                                           valvesOpen, waterLevel, 
                                           shipLocations, shipStates, 
                                           lockCommand, requests, permissions, 
                                           moved, perm, req, inUseLocks >>

CheckWaterLevelSideEntry == /\ pc[0] = "CheckWaterLevelSideEntry"
                            /\ IF req.side = LowSide(lockOrientations[req.lock])
                                  THEN /\ pc' = [pc EXCEPT ![0] = "OpenLowValveEntry"]
                                  ELSE /\ IF req.side = HighSide(lockOrientations[req.lock])
                                             THEN /\ pc' = [pc EXCEPT ![0] = "OpenHighValveEntry"]
                                             ELSE /\ pc' = [pc EXCEPT ![0] = "OpenDoorForEntry"]
                            /\ UNCHANGED << lockOrientations, doorsOpen, 
                                            valvesOpen, waterLevel, 
                                            shipLocations, shipStates, 
                                            lockCommand, requests, permissions, 
                                            moved, perm, req, inUseLocks >>

OpenLowValveEntry == /\ pc[0] = "OpenLowValveEntry"
                     /\ lockCommand' = [lockCommand EXCEPT ![req.lock] = [command |-> "change_valve", open |-> TRUE, side |-> "low"]]
                     /\ pc' = [pc EXCEPT ![0] = "WaitLowValveOpenedEntry"]
                     /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                                     waterLevel, shipLocations, shipStates, 
                                     requests, permissions, moved, perm, req, 
                                     inUseLocks >>

WaitLowValveOpenedEntry == /\ pc[0] = "WaitLowValveOpenedEntry"
                           /\ lockCommand[req.lock].command = "finished"
                           /\ pc' = [pc EXCEPT ![0] = "CloseLowValveEntry"]
                           /\ UNCHANGED << lockOrientations, doorsOpen, 
                                           valvesOpen, waterLevel, 
                                           shipLocations, shipStates, 
                                           lockCommand, requests, permissions, 
                                           moved, perm, req, inUseLocks >>

CloseLowValveEntry == /\ pc[0] = "CloseLowValveEntry"
                      /\ lockCommand' = [lockCommand EXCEPT ![req.lock] = [command |-> "change_valve", open |-> FALSE, side |-> "low"]]
                      /\ pc' = [pc EXCEPT ![0] = "WaitLowValveClosedEntry"]
                      /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                                      waterLevel, shipLocations, shipStates, 
                                      requests, permissions, moved, perm, req, 
                                      inUseLocks >>

WaitLowValveClosedEntry == /\ pc[0] = "WaitLowValveClosedEntry"
                           /\ lockCommand[req.lock].command = "finished"
                           /\ pc' = [pc EXCEPT ![0] = "OpenDoorForEntry"]
                           /\ UNCHANGED << lockOrientations, doorsOpen, 
                                           valvesOpen, waterLevel, 
                                           shipLocations, shipStates, 
                                           lockCommand, requests, permissions, 
                                           moved, perm, req, inUseLocks >>

OpenHighValveEntry == /\ pc[0] = "OpenHighValveEntry"
                      /\ lockCommand' = [lockCommand EXCEPT ![req.lock] = [command |-> "change_valve", open |-> TRUE, side |-> "high"]]
                      /\ pc' = [pc EXCEPT ![0] = "WaitHighValveOpenedEntry"]
                      /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                                      waterLevel, shipLocations, shipStates, 
                                      requests, permissions, moved, perm, req, 
                                      inUseLocks >>

WaitHighValveOpenedEntry == /\ pc[0] = "WaitHighValveOpenedEntry"
                            /\ lockCommand[req.lock].command = "finished"
                            /\ pc' = [pc EXCEPT ![0] = "CloseHighValveEntry"]
                            /\ UNCHANGED << lockOrientations, doorsOpen, 
                                            valvesOpen, waterLevel, 
                                            shipLocations, shipStates, 
                                            lockCommand, requests, permissions, 
                                            moved, perm, req, inUseLocks >>

CloseHighValveEntry == /\ pc[0] = "CloseHighValveEntry"
                       /\ lockCommand' = [lockCommand EXCEPT ![req.lock] = [command |-> "change_valve", open |-> FALSE, side |-> "high"]]
                       /\ pc' = [pc EXCEPT ![0] = "WaitHighValveClosedEntry"]
                       /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                                       waterLevel, shipLocations, shipStates, 
                                       requests, permissions, moved, perm, req, 
                                       inUseLocks >>

WaitHighValveClosedEntry == /\ pc[0] = "WaitHighValveClosedEntry"
                            /\ lockCommand[req.lock].command = "finished"
                            /\ pc' = [pc EXCEPT ![0] = "OpenDoorForEntry"]
                            /\ UNCHANGED << lockOrientations, doorsOpen, 
                                            valvesOpen, waterLevel, 
                                            shipLocations, shipStates, 
                                            lockCommand, requests, permissions, 
                                            moved, perm, req, inUseLocks >>

OpenDoorForEntry == /\ pc[0] = "OpenDoorForEntry"
                    /\ lockCommand' = [lockCommand EXCEPT ![req.lock] = [command |-> "change_door", open |-> TRUE, side|-> req.side]]
                    /\ pc' = [pc EXCEPT ![0] = "DoorOpenForEntry"]
                    /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                                    waterLevel, shipLocations, shipStates, 
                                    requests, permissions, moved, perm, req, 
                                    inUseLocks >>

DoorOpenForEntry == /\ pc[0] = "DoorOpenForEntry"
                    /\ lockCommand[req.lock].command = "finished"
                    /\ pc' = [pc EXCEPT ![0] = "WriteEntryPermission"]
                    /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                                    waterLevel, shipLocations, shipStates, 
                                    lockCommand, requests, permissions, moved, 
                                    perm, req, inUseLocks >>

WriteEntryPermission == /\ pc[0] = "WriteEntryPermission"
                        /\ permissions' = [permissions EXCEPT ![req.ship] = Append((permissions[req.ship]), ([lock |-> req.lock, granted |-> TRUE]))]
                        /\ pc' = [pc EXCEPT ![0] = "WaitForShipToEnter"]
                        /\ UNCHANGED << lockOrientations, doorsOpen, 
                                        valvesOpen, waterLevel, shipLocations, 
                                        shipStates, lockCommand, requests, 
                                        moved, perm, req, inUseLocks >>

WaitForShipToEnter == /\ pc[0] = "WaitForShipToEnter"
                      /\ moved[req.ship] = TRUE
                      /\ pc' = [pc EXCEPT ![0] = "CloseDoorAfterEntry"]
                      /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                                      waterLevel, shipLocations, shipStates, 
                                      lockCommand, requests, permissions, 
                                      moved, perm, req, inUseLocks >>

CloseDoorAfterEntry == /\ pc[0] = "CloseDoorAfterEntry"
                       /\ lockCommand' = [lockCommand EXCEPT ![req.lock] = [command |-> "change_door", open |-> FALSE, side|-> req.side]]
                       /\ pc' = [pc EXCEPT ![0] = "DoorClosedAfterEntry"]
                       /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                                       waterLevel, shipLocations, shipStates, 
                                       requests, permissions, moved, perm, req, 
                                       inUseLocks >>

DoorClosedAfterEntry == /\ pc[0] = "DoorClosedAfterEntry"
                        /\ lockCommand[req.lock].command = "finished"
                        /\ inUseLocks' = [inUseLocks EXCEPT ![req.lock] = TRUE]
                        /\ moved' = [moved EXCEPT ![(req.ship)] = FALSE]
                        /\ pc' = [pc EXCEPT ![0] = "ControlStart"]
                        /\ UNCHANGED << lockOrientations, doorsOpen, 
                                        valvesOpen, waterLevel, shipLocations, 
                                        shipStates, lockCommand, requests, 
                                        permissions, perm, req >>

ExitRequest == /\ pc[0] = "ExitRequest"
               /\ IF IsLock(shipLocations[req.ship])
                     THEN /\ Assert(lockLocation(req.lock) = shipLocations[req.ship], 
                                    "Failure of assertion at line 373, column 9.")
                          /\ IF shipStates[req.ship] = "go_to_east"
                                THEN /\ IF numShipsAtLoc(shipLocations[req.ship] + 1) >= 2
                                           THEN /\ permissions' = [permissions EXCEPT ![req.ship] = Append((permissions[req.ship]), ([lock |-> req.lock, granted |-> FALSE]))]
                                                /\ pc' = [pc EXCEPT ![0] = "ControlStart"]
                                           ELSE /\ pc' = [pc EXCEPT ![0] = "CheckWaterLevelSideExit"]
                                                /\ UNCHANGED permissions
                                ELSE /\ IF shipStates[req.ship] = "go_to_west"
                                           THEN /\ IF numShipsAtLoc(shipLocations[req.ship] - 1) >= 2
                                                      THEN /\ permissions' = [permissions EXCEPT ![req.ship] = Append((permissions[req.ship]), ([lock |-> req.lock, granted |-> FALSE]))]
                                                           /\ pc' = [pc EXCEPT ![0] = "ControlStart"]
                                                      ELSE /\ pc' = [pc EXCEPT ![0] = "CheckWaterLevelSideExit"]
                                                           /\ UNCHANGED permissions
                                           ELSE /\ pc' = [pc EXCEPT ![0] = "CheckWaterLevelSideExit"]
                                                /\ UNCHANGED permissions
                     ELSE /\ pc' = [pc EXCEPT ![0] = "MainLoop"]
                          /\ UNCHANGED permissions
               /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                               waterLevel, shipLocations, shipStates, 
                               lockCommand, requests, moved, perm, req, 
                               inUseLocks >>

CheckWaterLevelSideExit == /\ pc[0] = "CheckWaterLevelSideExit"
                           /\ IF req.side = LowSide(lockOrientations[req.lock])
                                 THEN /\ pc' = [pc EXCEPT ![0] = "OpenLowValveExit"]
                                 ELSE /\ IF req.side = HighSide(lockOrientations[req.lock])
                                            THEN /\ pc' = [pc EXCEPT ![0] = "OpenHighValveExit"]
                                            ELSE /\ pc' = [pc EXCEPT ![0] = "OpenDoorForExit"]
                           /\ UNCHANGED << lockOrientations, doorsOpen, 
                                           valvesOpen, waterLevel, 
                                           shipLocations, shipStates, 
                                           lockCommand, requests, permissions, 
                                           moved, perm, req, inUseLocks >>

OpenLowValveExit == /\ pc[0] = "OpenLowValveExit"
                    /\ lockCommand' = [lockCommand EXCEPT ![req.lock] = [command |-> "change_valve", open |-> TRUE, side |-> "low"]]
                    /\ pc' = [pc EXCEPT ![0] = "WaitLowValveOpenedExit"]
                    /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                                    waterLevel, shipLocations, shipStates, 
                                    requests, permissions, moved, perm, req, 
                                    inUseLocks >>

WaitLowValveOpenedExit == /\ pc[0] = "WaitLowValveOpenedExit"
                          /\ lockCommand[req.lock].command = "finished"
                          /\ pc' = [pc EXCEPT ![0] = "CloseLowValveExit"]
                          /\ UNCHANGED << lockOrientations, doorsOpen, 
                                          valvesOpen, waterLevel, 
                                          shipLocations, shipStates, 
                                          lockCommand, requests, permissions, 
                                          moved, perm, req, inUseLocks >>

CloseLowValveExit == /\ pc[0] = "CloseLowValveExit"
                     /\ lockCommand' = [lockCommand EXCEPT ![req.lock] = [command |-> "change_valve", open |-> FALSE, side |-> "low"]]
                     /\ pc' = [pc EXCEPT ![0] = "WaitLowValveClosedExit"]
                     /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                                     waterLevel, shipLocations, shipStates, 
                                     requests, permissions, moved, perm, req, 
                                     inUseLocks >>

WaitLowValveClosedExit == /\ pc[0] = "WaitLowValveClosedExit"
                          /\ lockCommand[req.lock].command = "finished"
                          /\ pc' = [pc EXCEPT ![0] = "OpenDoorForExit"]
                          /\ UNCHANGED << lockOrientations, doorsOpen, 
                                          valvesOpen, waterLevel, 
                                          shipLocations, shipStates, 
                                          lockCommand, requests, permissions, 
                                          moved, perm, req, inUseLocks >>

OpenHighValveExit == /\ pc[0] = "OpenHighValveExit"
                     /\ lockCommand' = [lockCommand EXCEPT ![req.lock] = [command |-> "change_valve", open |-> TRUE, side |-> "high"]]
                     /\ pc' = [pc EXCEPT ![0] = "WaitHighValveOpenedExit"]
                     /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                                     waterLevel, shipLocations, shipStates, 
                                     requests, permissions, moved, perm, req, 
                                     inUseLocks >>

WaitHighValveOpenedExit == /\ pc[0] = "WaitHighValveOpenedExit"
                           /\ lockCommand[req.lock].command = "finished"
                           /\ pc' = [pc EXCEPT ![0] = "CloseHighValveExit"]
                           /\ UNCHANGED << lockOrientations, doorsOpen, 
                                           valvesOpen, waterLevel, 
                                           shipLocations, shipStates, 
                                           lockCommand, requests, permissions, 
                                           moved, perm, req, inUseLocks >>

CloseHighValveExit == /\ pc[0] = "CloseHighValveExit"
                      /\ lockCommand' = [lockCommand EXCEPT ![req.lock] = [command |-> "change_valve", open |-> FALSE, side |-> "high"]]
                      /\ pc' = [pc EXCEPT ![0] = "WaitHighValveClosedExit"]
                      /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                                      waterLevel, shipLocations, shipStates, 
                                      requests, permissions, moved, perm, req, 
                                      inUseLocks >>

WaitHighValveClosedExit == /\ pc[0] = "WaitHighValveClosedExit"
                           /\ lockCommand[req.lock].command = "finished"
                           /\ pc' = [pc EXCEPT ![0] = "OpenDoorForExit"]
                           /\ UNCHANGED << lockOrientations, doorsOpen, 
                                           valvesOpen, waterLevel, 
                                           shipLocations, shipStates, 
                                           lockCommand, requests, permissions, 
                                           moved, perm, req, inUseLocks >>

OpenDoorForExit == /\ pc[0] = "OpenDoorForExit"
                   /\ lockCommand' = [lockCommand EXCEPT ![req.lock] = [command |-> "change_door", open |-> TRUE, side|-> req.side]]
                   /\ pc' = [pc EXCEPT ![0] = "DoorOpenForExit"]
                   /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                                   waterLevel, shipLocations, shipStates, 
                                   requests, permissions, moved, perm, req, 
                                   inUseLocks >>

DoorOpenForExit == /\ pc[0] = "DoorOpenForExit"
                   /\ lockCommand[req.lock].command = "finished"
                   /\ pc' = [pc EXCEPT ![0] = "WriteExitPermission"]
                   /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                                   waterLevel, shipLocations, shipStates, 
                                   lockCommand, requests, permissions, moved, 
                                   perm, req, inUseLocks >>

WriteExitPermission == /\ pc[0] = "WriteExitPermission"
                       /\ permissions' = [permissions EXCEPT ![req.ship] = Append((permissions[req.ship]), ([lock |-> req.lock, granted |-> TRUE]))]
                       /\ pc' = [pc EXCEPT ![0] = "WaitForShipToExit"]
                       /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                                       waterLevel, shipLocations, shipStates, 
                                       lockCommand, requests, moved, perm, req, 
                                       inUseLocks >>

WaitForShipToExit == /\ pc[0] = "WaitForShipToExit"
                     /\ moved[req.ship] = TRUE
                     /\ pc' = [pc EXCEPT ![0] = "CloseDoorAfterExit"]
                     /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                                     waterLevel, shipLocations, shipStates, 
                                     lockCommand, requests, permissions, moved, 
                                     perm, req, inUseLocks >>

CloseDoorAfterExit == /\ pc[0] = "CloseDoorAfterExit"
                      /\ lockCommand' = [lockCommand EXCEPT ![req.lock] = [command |-> "change_door", open |-> FALSE, side|-> req.side]]
                      /\ pc' = [pc EXCEPT ![0] = "DoorClosedAfterExit"]
                      /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                                      waterLevel, shipLocations, shipStates, 
                                      requests, permissions, moved, perm, req, 
                                      inUseLocks >>

DoorClosedAfterExit == /\ pc[0] = "DoorClosedAfterExit"
                       /\ lockCommand[req.lock].command = "finished"
                       /\ inUseLocks' = [inUseLocks EXCEPT ![req.lock] = FALSE]
                       /\ moved' = [moved EXCEPT ![(req.ship)] = FALSE]
                       /\ pc' = [pc EXCEPT ![0] = "ControlStart"]
                       /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                                       waterLevel, shipLocations, shipStates, 
                                       lockCommand, requests, permissions, 
                                       perm, req >>

controlProcess == MainLoop \/ ControlStart \/ EntryRequest
                     \/ CloseEastDoorEntry \/ WaitEastDoorClosedEntry
                     \/ CloseWestDoorEntry \/ WaitWestDoorClosedEntry
                     \/ CheckWaterLevelSideEntry \/ OpenLowValveEntry
                     \/ WaitLowValveOpenedEntry \/ CloseLowValveEntry
                     \/ WaitLowValveClosedEntry \/ OpenHighValveEntry
                     \/ WaitHighValveOpenedEntry \/ CloseHighValveEntry
                     \/ WaitHighValveClosedEntry \/ OpenDoorForEntry
                     \/ DoorOpenForEntry \/ WriteEntryPermission
                     \/ WaitForShipToEnter \/ CloseDoorAfterEntry
                     \/ DoorClosedAfterEntry \/ ExitRequest
                     \/ CheckWaterLevelSideExit \/ OpenLowValveExit
                     \/ WaitLowValveOpenedExit \/ CloseLowValveExit
                     \/ WaitLowValveClosedExit \/ OpenHighValveExit
                     \/ WaitHighValveOpenedExit \/ CloseHighValveExit
                     \/ WaitHighValveClosedExit \/ OpenDoorForExit
                     \/ DoorOpenForExit \/ WriteExitPermission
                     \/ WaitForShipToExit \/ CloseDoorAfterExit
                     \/ DoorClosedAfterExit

Next == controlProcess
           \/ (\E self \in Locks: lockProcess(self))
           \/ (\E self \in Ships: shipProcess(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Locks : WF_vars(lockProcess(self))
        /\ \A self \in Ships : WF_vars(shipProcess(self))
        /\ WF_vars(controlProcess)

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Mon Oct 20 20:58:30 CEST 2025 by 20241642
\* Last modified Fri Oct 17 19:21:31 CEST 2025 by iyladakeekarjai
\* Last modified Wed Oct 15 10:06:38 CEST 2025 by 20241642
\* Last modified Wed Sep 24 12:00:55 CEST 2025 by mvolk
\* Created Thu Aug 28 11:30:07 CEST 2025 by mvolk
