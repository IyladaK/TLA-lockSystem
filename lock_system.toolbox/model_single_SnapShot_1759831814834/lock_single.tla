---------------------------- MODULE lock_single ----------------------------

EXTENDS lock_data


(* --algorithm lock_system

\*****************************
\* Define global variables
\*****************************
variables
  \* Variables for locks
  lockOrientation = "west_low", 
  doorsOpen = [ls \in LockSide |-> FALSE], \* init all doors and valves are closed
  valvesOpen = [vs \in ValveSide |-> FALSE],
  waterLevel = "low", \* init water level in lock is low
  
  \* Variables for single ship
  shipLocation = 0,
  shipStatus = "go_to_east",
  
  \* Command for lock
  \* for command "change_door" the side should be "west" or "east"
  \* for command "change_valve" the side should be "high" or "low"
  lockCommand = [command |-> "finished", open |-> FALSE, side |-> "west"], \* stores current command
  \* Central requests of all ships
  requests = << >>,
  \* Permissions per ship
  permissions = << >>;

define

\*****************************
\* Helper functions
\*****************************
\* Check if ship is within the lock
InLock == IsLock(shipLocation)

\* Check if all doors are closed
BothDoorsClosed == \A ls \in LockSide : doorsOpen[ls] = FALSE
\* Return which door is open
OpenDoor == {ls \in LockSide : doorsOpen[ls] = TRUE}
\*****************************
\* Type checks
\*****************************
\* Check that variables use the correct type
TypeOK == /\ lockOrientation \in LockOrientation
          /\ \A ls \in LockSide : doorsOpen[ls] \in BOOLEAN
          /\ \A vs \in ValveSide : valvesOpen[vs] \in BOOLEAN
          /\ waterLevel \in WaterLevel
          /\ lockCommand.command \in LockCommand
          /\ lockCommand.open \in BOOLEAN
          /\ lockCommand.side \in LockSide \union ValveSide
          /\ shipLocation \in Locations
          /\ shipStatus \in ShipStatus
          /\ \A i \in 1..Len(permissions):
               /\ permissions[i].lock \in Locks
               /\ permissions[i].granted \in BOOLEAN
          /\ \A i \in 1..Len(requests):
               /\ requests[i].ship \in Ships
               /\ requests[i].lock \in Locks
               /\ requests[i].side \in LockSide

\* Check that message queues are not overflowing
MessagesOK == /\ Len(requests) <= 1
              /\ Len(permissions) <= 1


\*****************************
\* Requirements on lock
\*****************************
\* The eastern pair of doors and the western pair of doors are never simultaneously open
DoorsMutex == 
    ~(doorsOpen["west"] = TRUE /\ doorsOpen["east"] = TRUE)
\* When the lower/higher pair of doors is open, the higher/lower valve is closed.
DoorsOpenValvesClosed == 
    \A v \in ValveSide:
        valvesOpen[v] = TRUE => (\A d \in LockSide : doorsOpen[d] = FALSE)
\* The lower/higher pair of doors is only open when the water level in the lock is low/high
DoorsOpenWaterlevelRight  == 
    /\ (doorsOpen["west"] = TRUE => waterLevel = "low")
    /\ (doorsOpen["east"] = TRUE => waterLevel = "high")
\* Always if the ship requests to enter the lock, the ship will eventually be inside the lock.
RequestLockFulfilled == FALSE
\* Water level is infinitely many times high/low
WaterlevelChange == 
    /\ ([](<> (waterLevel = "low")))
    /\ ([](<> (waterLevel = "high")))
\* Infinitely many times the ship does requests
RequestsShips == FALSE
\* Infinitely many times the ship reaches its end location
ShipsReachGoals == 
    /\ []((shipStatus = "go_to_east") ~> (shipStatus = "goal_reached"))
    /\ []((shipStatus = "go_to_west") ~> (shipStatus = "goal_reached"))

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


\*****************************
\* Process for a lock
\*****************************
process lockProcess \in Locks
begin
  LockWaitForCommand:
    while TRUE do
      await lockCommand.command /= "finished";
      if lockCommand.command = "change_door" then
        \* Change status of door
        doorsOpen[lockCommand.side] := lockCommand.open;
      elsif lockCommand.command = "change_valve" then
        \* Change status of valve
        valvesOpen[lockCommand.side] := lockCommand.open;
      else
        \* should not happen
        assert FALSE;
      end if;
  LockUpdateWaterLevel:
      updateWaterLevel(lockOrientation, doorsOpen, valvesOpen, waterLevel);
  LockCommandFinished:
      lockCommand.command := "finished";    
    end while;
end process;


\*****************************
\* Process for a ship
\*****************************
process shipProcess \in Ships
variables
  perm = [lock |-> 1, granted |-> FALSE] \* current permission to enter the lock
begin
  ShipNextIteration:
    while TRUE do
      if shipStatus = "go_to_east" then
        if shipLocation = EastEnd then
  ShipGoalReachedEast:
          shipStatus := "goal_reached";
        else
          if ~InLock then
  ShipRequestWest:
            \* Request west doors of lock
            write(requests, [ship |-> self, lock |-> 1, side |-> "west"]); \* if the ship is not in a lock, 
            \* it writes a request for west
  ShipWaitForWest:
            \* Wait for permission
            read(permissions, perm);
            assert perm.lock = GetLock(shipLocation+1); \* makes sure that permission is for right lock
          else
          \* waits until perm["lock] = next location 
  ShipRequestEastInLock: \* it's INSIDE the lock
            \* Request east doors of lock
            write(requests, [ship |-> self, lock |-> 1, side |-> "east"]);
  ShipWaitForEastInLock:
            \* Wait for permission
            read(permissions, perm);
            assert perm.lock = GetLock(shipLocation); \* makes sure that permission is for current lock
          end if;
  ShipMoveEast:
          if perm.granted then
            \* Move ship
            assert doorsOpen[IF InLock THEN "east" ELSE "west"];
            shipLocation := shipLocation + 1;
          end if;
        end if;
      elsif shipStatus = "go_to_west" then
        if shipLocation = WestEnd then
  ShipGoalReachedWest:
          shipStatus := "goal_reached";
        else
          if ~InLock then
  ShipRequestEast:
            \* Request east doors of lock
            write(requests, [ship |-> self, lock |-> 1, side |-> "east"]);
  ShipWaitForEast:
            \* Wait for permission
            read(permissions, perm);
            assert perm.lock = GetLock(shipLocation-1);
          else
  ShipRequestWestInLock:
            \* Request west doors of lock
            write(requests, [ship |-> self, lock |-> 1, side |-> "west"]);
  ShipWaitForWestInLock:
            \* Wait for permission
            read(permissions, perm);
            assert perm.lock = GetLock(shipLocation);
          end if;
  ShipMoveWest:
          if perm.granted then
            \* Move ship
            assert doorsOpen[IF InLock THEN "west" ELSE "east"];
            shipLocation := shipLocation - 1;
          end if;
        end if;
      else
        assert shipStatus = "goal_reached";
  ShipTurnAround:
        \* Turn around
        shipStatus := IF shipLocation = WestEnd THEN "go_to_east" ELSE "go_to_west";
      end if;
    end while;
end process;


\*****************************
\* Process for the controller
\*****************************
process controlProcess = 0

variables
  req = [ship |-> 0, lock |-> 0, side |-> ""]
begin
  ControlStart:
    \* wait for request to come through
    read(requests, req);
    assert req.lock = 1 /\ req.side \in LockSide;
  HandleWestRequest:
    if ~InLock /\ req.side = "west" then
        WaitForReady:
            await lockCommand.command = "finished";
       
       OpenWestDoor:
            lockCommand := [command |-> "change_door", open |-> TRUE, side |-> "west"];
       
       WestDoorOpened:
            await lockCommand.command = "finished";
    
    write(permissions, [lock |-> req.lock, granted |-> TRUE]);
    end if;
            
    
end process;


end algorithm; *)


\* BEGIN TRANSLATION (chksum(pcal) = "eeddda9f" /\ chksum(tla) = "8a67773a")
VARIABLES lockOrientation, doorsOpen, valvesOpen, waterLevel, shipLocation, 
          shipStatus, lockCommand, requests, permissions, pc

(* define statement *)
InLock == IsLock(shipLocation)


BothDoorsClosed == \A ls \in LockSide : doorsOpen[ls] = FALSE

OpenDoor == {ls \in LockSide : doorsOpen[ls] = TRUE}




TypeOK == /\ lockOrientation \in LockOrientation
          /\ \A ls \in LockSide : doorsOpen[ls] \in BOOLEAN
          /\ \A vs \in ValveSide : valvesOpen[vs] \in BOOLEAN
          /\ waterLevel \in WaterLevel
          /\ lockCommand.command \in LockCommand
          /\ lockCommand.open \in BOOLEAN
          /\ lockCommand.side \in LockSide \union ValveSide
          /\ shipLocation \in Locations
          /\ shipStatus \in ShipStatus
          /\ \A i \in 1..Len(permissions):
               /\ permissions[i].lock \in Locks
               /\ permissions[i].granted \in BOOLEAN
          /\ \A i \in 1..Len(requests):
               /\ requests[i].ship \in Ships
               /\ requests[i].lock \in Locks
               /\ requests[i].side \in LockSide


MessagesOK == /\ Len(requests) <= 1
              /\ Len(permissions) <= 1






DoorsMutex ==
    ~(doorsOpen["west"] = TRUE /\ doorsOpen["east"] = TRUE)

DoorsOpenValvesClosed ==
    \A v \in ValveSide:
        valvesOpen[v] = TRUE => (\A d \in LockSide : doorsOpen[d] = FALSE)

DoorsOpenWaterlevelRight  ==
    /\ (doorsOpen["west"] = TRUE => waterLevel = "low")
    /\ (doorsOpen["east"] = TRUE => waterLevel = "high")

RequestLockFulfilled == FALSE

WaterlevelChange ==
    /\ ([](<> (waterLevel = "low")))
    /\ ([](<> (waterLevel = "high")))

RequestsShips == FALSE

ShipsReachGoals ==
    /\ []((shipStatus = "go_to_east") ~> (shipStatus = "goal_reached"))
    /\ []((shipStatus = "go_to_west") ~> (shipStatus = "goal_reached"))

VARIABLES perm, req

vars == << lockOrientation, doorsOpen, valvesOpen, waterLevel, shipLocation, 
           shipStatus, lockCommand, requests, permissions, pc, perm, req >>

ProcSet == (Locks) \cup (Ships) \cup {0}

Init == (* Global variables *)
        /\ lockOrientation = "west_low"
        /\ doorsOpen = [ls \in LockSide |-> FALSE]
        /\ valvesOpen = [vs \in ValveSide |-> FALSE]
        /\ waterLevel = "low"
        /\ shipLocation = 0
        /\ shipStatus = "go_to_east"
        /\ lockCommand = [command |-> "finished", open |-> FALSE, side |-> "west"]
        /\ requests = << >>
        /\ permissions = << >>
        (* Process shipProcess *)
        /\ perm = [self \in Ships |-> [lock |-> 1, granted |-> FALSE]]
        (* Process controlProcess *)
        /\ req = [ship |-> 0, lock |-> 0, side |-> ""]
        /\ pc = [self \in ProcSet |-> CASE self \in Locks -> "LockWaitForCommand"
                                        [] self \in Ships -> "ShipNextIteration"
                                        [] self = 0 -> "ControlStart"]

LockWaitForCommand(self) == /\ pc[self] = "LockWaitForCommand"
                            /\ lockCommand.command /= "finished"
                            /\ IF lockCommand.command = "change_door"
                                  THEN /\ doorsOpen' = [doorsOpen EXCEPT ![lockCommand.side] = lockCommand.open]
                                       /\ UNCHANGED valvesOpen
                                  ELSE /\ IF lockCommand.command = "change_valve"
                                             THEN /\ valvesOpen' = [valvesOpen EXCEPT ![lockCommand.side] = lockCommand.open]
                                             ELSE /\ Assert(FALSE, 
                                                            "Failure of assertion at line 153, column 9.")
                                                  /\ UNCHANGED valvesOpen
                                       /\ UNCHANGED doorsOpen
                            /\ pc' = [pc EXCEPT ![self] = "LockUpdateWaterLevel"]
                            /\ UNCHANGED << lockOrientation, waterLevel, 
                                            shipLocation, shipStatus, 
                                            lockCommand, requests, permissions, 
                                            perm, req >>

LockUpdateWaterLevel(self) == /\ pc[self] = "LockUpdateWaterLevel"
                              /\ IF valvesOpen["low"]
                                    THEN /\ waterLevel' = "low"
                                    ELSE /\ IF (lockOrientation = "west_low" /\ doorsOpen["west"])
                                                \/ (lockOrientation = "east_low" /\ doorsOpen["east"])
                                               THEN /\ waterLevel' = "low"
                                               ELSE /\ IF valvesOpen["high"]
                                                          THEN /\ waterLevel' = "high"
                                                          ELSE /\ IF (lockOrientation = "west_low" /\ doorsOpen["east"])
                                                                      \/ (lockOrientation = "east_low" /\ doorsOpen["west"])
                                                                     THEN /\ waterLevel' = "high"
                                                                     ELSE /\ TRUE
                                                                          /\ UNCHANGED waterLevel
                              /\ pc' = [pc EXCEPT ![self] = "LockCommandFinished"]
                              /\ UNCHANGED << lockOrientation, doorsOpen, 
                                              valvesOpen, shipLocation, 
                                              shipStatus, lockCommand, 
                                              requests, permissions, perm, req >>

LockCommandFinished(self) == /\ pc[self] = "LockCommandFinished"
                             /\ lockCommand' = [lockCommand EXCEPT !.command = "finished"]
                             /\ pc' = [pc EXCEPT ![self] = "LockWaitForCommand"]
                             /\ UNCHANGED << lockOrientation, doorsOpen, 
                                             valvesOpen, waterLevel, 
                                             shipLocation, shipStatus, 
                                             requests, permissions, perm, req >>

lockProcess(self) == LockWaitForCommand(self) \/ LockUpdateWaterLevel(self)
                        \/ LockCommandFinished(self)

ShipNextIteration(self) == /\ pc[self] = "ShipNextIteration"
                           /\ IF shipStatus = "go_to_east"
                                 THEN /\ IF shipLocation = EastEnd
                                            THEN /\ pc' = [pc EXCEPT ![self] = "ShipGoalReachedEast"]
                                            ELSE /\ IF ~InLock
                                                       THEN /\ pc' = [pc EXCEPT ![self] = "ShipRequestWest"]
                                                       ELSE /\ pc' = [pc EXCEPT ![self] = "ShipRequestEastInLock"]
                                 ELSE /\ IF shipStatus = "go_to_west"
                                            THEN /\ IF shipLocation = WestEnd
                                                       THEN /\ pc' = [pc EXCEPT ![self] = "ShipGoalReachedWest"]
                                                       ELSE /\ IF ~InLock
                                                                  THEN /\ pc' = [pc EXCEPT ![self] = "ShipRequestEast"]
                                                                  ELSE /\ pc' = [pc EXCEPT ![self] = "ShipRequestWestInLock"]
                                            ELSE /\ Assert(shipStatus = "goal_reached", 
                                                           "Failure of assertion at line 233, column 9.")
                                                 /\ pc' = [pc EXCEPT ![self] = "ShipTurnAround"]
                           /\ UNCHANGED << lockOrientation, doorsOpen, 
                                           valvesOpen, waterLevel, 
                                           shipLocation, shipStatus, 
                                           lockCommand, requests, permissions, 
                                           perm, req >>

ShipGoalReachedEast(self) == /\ pc[self] = "ShipGoalReachedEast"
                             /\ shipStatus' = "goal_reached"
                             /\ pc' = [pc EXCEPT ![self] = "ShipNextIteration"]
                             /\ UNCHANGED << lockOrientation, doorsOpen, 
                                             valvesOpen, waterLevel, 
                                             shipLocation, lockCommand, 
                                             requests, permissions, perm, req >>

ShipMoveEast(self) == /\ pc[self] = "ShipMoveEast"
                      /\ IF perm[self].granted
                            THEN /\ Assert(doorsOpen[IF InLock THEN "east" ELSE "west"], 
                                           "Failure of assertion at line 199, column 13.")
                                 /\ shipLocation' = shipLocation + 1
                            ELSE /\ TRUE
                                 /\ UNCHANGED shipLocation
                      /\ pc' = [pc EXCEPT ![self] = "ShipNextIteration"]
                      /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                      waterLevel, shipStatus, lockCommand, 
                                      requests, permissions, perm, req >>

ShipRequestWest(self) == /\ pc[self] = "ShipRequestWest"
                         /\ requests' = Append(requests, ([ship |-> self, lock |-> 1, side |-> "west"]))
                         /\ pc' = [pc EXCEPT ![self] = "ShipWaitForWest"]
                         /\ UNCHANGED << lockOrientation, doorsOpen, 
                                         valvesOpen, waterLevel, shipLocation, 
                                         shipStatus, lockCommand, permissions, 
                                         perm, req >>

ShipWaitForWest(self) == /\ pc[self] = "ShipWaitForWest"
                         /\ permissions /= <<>>
                         /\ perm' = [perm EXCEPT ![self] = Head(permissions)]
                         /\ permissions' = Tail(permissions)
                         /\ Assert(perm'[self].lock = GetLock(shipLocation+1), 
                                   "Failure of assertion at line 185, column 13.")
                         /\ pc' = [pc EXCEPT ![self] = "ShipMoveEast"]
                         /\ UNCHANGED << lockOrientation, doorsOpen, 
                                         valvesOpen, waterLevel, shipLocation, 
                                         shipStatus, lockCommand, requests, 
                                         req >>

ShipRequestEastInLock(self) == /\ pc[self] = "ShipRequestEastInLock"
                               /\ requests' = Append(requests, ([ship |-> self, lock |-> 1, side |-> "east"]))
                               /\ pc' = [pc EXCEPT ![self] = "ShipWaitForEastInLock"]
                               /\ UNCHANGED << lockOrientation, doorsOpen, 
                                               valvesOpen, waterLevel, 
                                               shipLocation, shipStatus, 
                                               lockCommand, permissions, perm, 
                                               req >>

ShipWaitForEastInLock(self) == /\ pc[self] = "ShipWaitForEastInLock"
                               /\ permissions /= <<>>
                               /\ perm' = [perm EXCEPT ![self] = Head(permissions)]
                               /\ permissions' = Tail(permissions)
                               /\ Assert(perm'[self].lock = GetLock(shipLocation), 
                                         "Failure of assertion at line 194, column 13.")
                               /\ pc' = [pc EXCEPT ![self] = "ShipMoveEast"]
                               /\ UNCHANGED << lockOrientation, doorsOpen, 
                                               valvesOpen, waterLevel, 
                                               shipLocation, shipStatus, 
                                               lockCommand, requests, req >>

ShipTurnAround(self) == /\ pc[self] = "ShipTurnAround"
                        /\ shipStatus' = (IF shipLocation = WestEnd THEN "go_to_east" ELSE "go_to_west")
                        /\ pc' = [pc EXCEPT ![self] = "ShipNextIteration"]
                        /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                        waterLevel, shipLocation, lockCommand, 
                                        requests, permissions, perm, req >>

ShipGoalReachedWest(self) == /\ pc[self] = "ShipGoalReachedWest"
                             /\ shipStatus' = "goal_reached"
                             /\ pc' = [pc EXCEPT ![self] = "ShipNextIteration"]
                             /\ UNCHANGED << lockOrientation, doorsOpen, 
                                             valvesOpen, waterLevel, 
                                             shipLocation, lockCommand, 
                                             requests, permissions, perm, req >>

ShipMoveWest(self) == /\ pc[self] = "ShipMoveWest"
                      /\ IF perm[self].granted
                            THEN /\ Assert(doorsOpen[IF InLock THEN "west" ELSE "east"], 
                                           "Failure of assertion at line 228, column 13.")
                                 /\ shipLocation' = shipLocation - 1
                            ELSE /\ TRUE
                                 /\ UNCHANGED shipLocation
                      /\ pc' = [pc EXCEPT ![self] = "ShipNextIteration"]
                      /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                      waterLevel, shipStatus, lockCommand, 
                                      requests, permissions, perm, req >>

ShipRequestEast(self) == /\ pc[self] = "ShipRequestEast"
                         /\ requests' = Append(requests, ([ship |-> self, lock |-> 1, side |-> "east"]))
                         /\ pc' = [pc EXCEPT ![self] = "ShipWaitForEast"]
                         /\ UNCHANGED << lockOrientation, doorsOpen, 
                                         valvesOpen, waterLevel, shipLocation, 
                                         shipStatus, lockCommand, permissions, 
                                         perm, req >>

ShipWaitForEast(self) == /\ pc[self] = "ShipWaitForEast"
                         /\ permissions /= <<>>
                         /\ perm' = [perm EXCEPT ![self] = Head(permissions)]
                         /\ permissions' = Tail(permissions)
                         /\ Assert(perm'[self].lock = GetLock(shipLocation-1), 
                                   "Failure of assertion at line 215, column 13.")
                         /\ pc' = [pc EXCEPT ![self] = "ShipMoveWest"]
                         /\ UNCHANGED << lockOrientation, doorsOpen, 
                                         valvesOpen, waterLevel, shipLocation, 
                                         shipStatus, lockCommand, requests, 
                                         req >>

ShipRequestWestInLock(self) == /\ pc[self] = "ShipRequestWestInLock"
                               /\ requests' = Append(requests, ([ship |-> self, lock |-> 1, side |-> "west"]))
                               /\ pc' = [pc EXCEPT ![self] = "ShipWaitForWestInLock"]
                               /\ UNCHANGED << lockOrientation, doorsOpen, 
                                               valvesOpen, waterLevel, 
                                               shipLocation, shipStatus, 
                                               lockCommand, permissions, perm, 
                                               req >>

ShipWaitForWestInLock(self) == /\ pc[self] = "ShipWaitForWestInLock"
                               /\ permissions /= <<>>
                               /\ perm' = [perm EXCEPT ![self] = Head(permissions)]
                               /\ permissions' = Tail(permissions)
                               /\ Assert(perm'[self].lock = GetLock(shipLocation), 
                                         "Failure of assertion at line 223, column 13.")
                               /\ pc' = [pc EXCEPT ![self] = "ShipMoveWest"]
                               /\ UNCHANGED << lockOrientation, doorsOpen, 
                                               valvesOpen, waterLevel, 
                                               shipLocation, shipStatus, 
                                               lockCommand, requests, req >>

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

ControlStart == /\ pc[0] = "ControlStart"
                /\ requests /= <<>>
                /\ req' = Head(requests)
                /\ requests' = Tail(requests)
                /\ Assert(req'.lock = 1 /\ req'.side \in LockSide, 
                          "Failure of assertion at line 253, column 5.")
                /\ pc' = [pc EXCEPT ![0] = "HandleWestRequest"]
                /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                waterLevel, shipLocation, shipStatus, 
                                lockCommand, permissions, perm >>

HandleWestRequest == /\ pc[0] = "HandleWestRequest"
                     /\ IF ~InLock /\ req.side = "west"
                           THEN /\ pc' = [pc EXCEPT ![0] = "WaitForReady"]
                           ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
                     /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                     waterLevel, shipLocation, shipStatus, 
                                     lockCommand, requests, permissions, perm, 
                                     req >>

WaitForReady == /\ pc[0] = "WaitForReady"
                /\ lockCommand.command = "finished"
                /\ pc' = [pc EXCEPT ![0] = "OpenWestDoor"]
                /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                waterLevel, shipLocation, shipStatus, 
                                lockCommand, requests, permissions, perm, req >>

OpenWestDoor == /\ pc[0] = "OpenWestDoor"
                /\ lockCommand' = [command |-> "change_door", open |-> TRUE, side |-> "west"]
                /\ pc' = [pc EXCEPT ![0] = "WestDoorOpened"]
                /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                waterLevel, shipLocation, shipStatus, requests, 
                                permissions, perm, req >>

WestDoorOpened == /\ pc[0] = "WestDoorOpened"
                  /\ lockCommand.command = "finished"
                  /\ permissions' = Append(permissions, ([lock |-> req.lock, granted |-> TRUE]))
                  /\ pc' = [pc EXCEPT ![0] = "Done"]
                  /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                  waterLevel, shipLocation, shipStatus, 
                                  lockCommand, requests, perm, req >>

controlProcess == ControlStart \/ HandleWestRequest \/ WaitForReady
                     \/ OpenWestDoor \/ WestDoorOpened

Next == controlProcess
           \/ (\E self \in Locks: lockProcess(self))
           \/ (\E self \in Ships: shipProcess(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Tue Oct 07 12:10:08 CEST 2025 by iyladakeekarjai
\* Last modified Wed Sep 24 11:08:53 CEST 2025 by mvolk
\* Created Thu Aug 28 11:30:23 CEST 2025 by mvolk
