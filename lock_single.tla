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

\* given a lock, returns the location is the lock
lockLocation(lock) == lock + (lock - 1)


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
DoorsOpenValvesClosed == /\ (doorsOpen[LowSide(lockOrientation)] => ~ valvesOpen["high"]) 
                         /\ (doorsOpen[HighSide(lockOerientation)] => ~valvesOpen["low"])
\* The lower/higher pair of doors is only open when the water level in the lock is low/high
DoorsOpenWaterlevelRight  == /\ (doorsOpen[LowSide(lockOrientation)] = TRUE => waterLevel = "low")
                             /\ (doorsOpen[HighSide(lockOrientation)] = TRUE => waterLevel = "high")
\* Always if the ship requests to enter the lock, the ship will eventually be inside the lock.
RequestLockFulfilled == [](requests/=<<>> => <> InLock)
\* Water level is infinitely many times high/low
WaterlevelChange == []<>(waterLevel = "high") /\ []<>(waterLevel = "low")
\* Infinitely many times the ship does requests
RequestsShips == []<> (requests /= <<>>)
\* Infinitely many times the ship reaches its end location
ShipsReachGoals == []<> (shipStatus = "goal_reached")

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

\* wait until previous process completes
macro WaitForReady() begin
    await lockCommand.command = "finished";
end macro;


\*****************************
\* Process for a lock
\*****************************
fair process lockProcess \in Locks
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
fair process shipProcess \in Ships
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
fair process controlProcess = 0

variables
  req = [ship |-> 0, lock |-> 0, side |-> ""]
begin
    MainLoop:
        while TRUE do
    ControlStart:
            \* wait for request to come through
            read(requests, req);
            assert req.lock = 1 /\ req.side \in LockSide;


            if ~InLock /\ req.side = "west" then
    WaitForReadyW:
                await lockCommand.command = "finished";
    OpenWestDoorW:
                lockCommand := [command |-> "change_door", open |-> TRUE, side |-> "west"];
    WestDoorOpened:
                await lockCommand.command = "finished";
    GrantPermissionW:
                write(permissions, [lock |-> req.lock, granted |-> TRUE]);
    WaitForEnterW:
                await InLock;
    CloseWestDoor:
                lockCommand := [command |-> "change_door", open |-> FALSE, side |-> "west"];
    WestDoorClosedIn:
                await lockCommand.command = "finished";
    RequestToOutW:
                read(requests, req);
    IncreaseWaterLevel:
                lockCommand := [command |-> "change_valve", open |-> TRUE, side |-> "high"];
    WaterLevelIncreased:
                await lockCommand.command = "finished";
    CloseHighValve:
                lockCommand := [command |-> "change_valve", open |-> FALSE, side |-> "high"];
    HighValveCLosed:
                await lockCommand.command = "finished";
    OpenEastDoorW:
                lockCommand := [command |-> "change_door", open |-> TRUE, side|-> "east"];
    EastDoorOpenedInW:  
                await lockCommand.command = "finished";
    GrantPermissionOutW:
                write(permissions, [lock |-> req.lock, granted |-> TRUE]);
    WaitExitW:
                await ~InLock;     
            
        
            elsif ~InLock /\ req.side = "east" then
    WaitForReadyE:
                await lockCommand.command = "finished";
    OpenEastDoorE:
                lockCommand := [command |-> "change_door", open |-> TRUE, side |-> "east"];
    EastDoorOpened:
                await lockCommand.command = "finished";
    GrantPermissionE:
                write(permissions, [lock |-> req.lock, granted |-> TRUE]);
    WaitForEnterE:
                await InLock;
    CloseEastDoor:
                lockCommand := [command |-> "change_door", open |-> FALSE, side |-> "east"];
    EastDoorClosedIn:
                await lockCommand.command = "finished";
    RequestToOutE:
                read(requests, req);
    DecreaseWaterLevel:
                lockCommand := [command |-> "change_valve", open |-> TRUE, side |-> "low"];
    WaterLevelDecreased:
                await lockCommand.command = "finished";
    CloseLowValve:
                lockCommand := [command |-> "change_valve", open |-> FALSE, side |-> "low"];
    LowValveCLosed:
                await lockCommand.command = "finished";
    WaitForWaterLow:
                await waterLevel = "low";
    OpenWestDoorE:
                lockCommand := [command |-> "change_door", open |-> TRUE, side |-> "west"];
    WestDoorOpenedInE:  
                await lockCommand.command = "finished";
    GrantPermissionOutE:
                write(permissions, [lock |-> req.lock, granted |-> TRUE]);
    WaitExitE:
                await ~InLock; 
            
            end if;
            
    end while;       
end process;


end algorithm; *)


\* BEGIN TRANSLATION (chksum(pcal) = "4df13781" /\ chksum(tla) = "13c7a8e3")
VARIABLES lockOrientation, doorsOpen, valvesOpen, waterLevel, shipLocation, 
          shipStatus, lockCommand, requests, permissions, pc

(* define statement *)
InLock == IsLock(shipLocation)


BothDoorsClosed == \A ls \in LockSide : doorsOpen[ls] = FALSE


lockLocation(lock) == lock + (lock - 1)






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


RequestLockFulfilled == [](requests/=<<>> => <> InLock)

WaterlevelChange == []<>(waterLevel = "high" \/ waterLevel = "low")

RequestsShips == []<> (requests /= <<>>)

ShipsReachGoals == []<> (shipStatus = "goal_reached")

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
                                        [] self = 0 -> "MainLoop"]

LockWaitForCommand(self) == /\ pc[self] = "LockWaitForCommand"
                            /\ lockCommand.command /= "finished"
                            /\ IF lockCommand.command = "change_door"
                                  THEN /\ doorsOpen' = [doorsOpen EXCEPT ![lockCommand.side] = lockCommand.open]
                                       /\ UNCHANGED valvesOpen
                                  ELSE /\ IF lockCommand.command = "change_valve"
                                             THEN /\ valvesOpen' = [valvesOpen EXCEPT ![lockCommand.side] = lockCommand.open]
                                             ELSE /\ Assert(FALSE, 
                                                            "Failure of assertion at line 158, column 9.")
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
                                                           "Failure of assertion at line 238, column 9.")
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
                                           "Failure of assertion at line 204, column 13.")
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
                                   "Failure of assertion at line 190, column 13.")
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
                                         "Failure of assertion at line 199, column 13.")
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
                                           "Failure of assertion at line 233, column 13.")
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
                                   "Failure of assertion at line 220, column 13.")
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
                                         "Failure of assertion at line 228, column 13.")
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

MainLoop == /\ pc[0] = "MainLoop"
            /\ pc' = [pc EXCEPT ![0] = "ControlStart"]
            /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, waterLevel, 
                            shipLocation, shipStatus, lockCommand, requests, 
                            permissions, perm, req >>

ControlStart == /\ pc[0] = "ControlStart"
                /\ requests /= <<>>
                /\ req' = Head(requests)
                /\ requests' = Tail(requests)
                /\ Assert(req'.lock = 1 /\ req'.side \in LockSide, 
                          "Failure of assertion at line 260, column 13.")
                /\ IF ~InLock /\ req'.side = "west"
                      THEN /\ pc' = [pc EXCEPT ![0] = "WaitForReadyW"]
                      ELSE /\ IF ~InLock /\ req'.side = "east"
                                 THEN /\ pc' = [pc EXCEPT ![0] = "WaitForReadyE"]
                                 ELSE /\ pc' = [pc EXCEPT ![0] = "MainLoop"]
                /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                waterLevel, shipLocation, shipStatus, 
                                lockCommand, permissions, perm >>

WaitForReadyW == /\ pc[0] = "WaitForReadyW"
                 /\ lockCommand.command = "finished"
                 /\ pc' = [pc EXCEPT ![0] = "OpenWestDoorW"]
                 /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                 waterLevel, shipLocation, shipStatus, 
                                 lockCommand, requests, permissions, perm, req >>

OpenWestDoorW == /\ pc[0] = "OpenWestDoorW"
                 /\ lockCommand' = [command |-> "change_door", open |-> TRUE, side |-> "west"]
                 /\ pc' = [pc EXCEPT ![0] = "WestDoorOpened"]
                 /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                 waterLevel, shipLocation, shipStatus, 
                                 requests, permissions, perm, req >>

WestDoorOpened == /\ pc[0] = "WestDoorOpened"
                  /\ lockCommand.command = "finished"
                  /\ pc' = [pc EXCEPT ![0] = "GrantPermissionW"]
                  /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                  waterLevel, shipLocation, shipStatus, 
                                  lockCommand, requests, permissions, perm, 
                                  req >>

GrantPermissionW == /\ pc[0] = "GrantPermissionW"
                    /\ permissions' = Append(permissions, ([lock |-> req.lock, granted |-> TRUE]))
                    /\ pc' = [pc EXCEPT ![0] = "WaitForEnterW"]
                    /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                    waterLevel, shipLocation, shipStatus, 
                                    lockCommand, requests, perm, req >>

WaitForEnterW == /\ pc[0] = "WaitForEnterW"
                 /\ InLock
                 /\ pc' = [pc EXCEPT ![0] = "CloseWestDoor"]
                 /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                 waterLevel, shipLocation, shipStatus, 
                                 lockCommand, requests, permissions, perm, req >>

CloseWestDoor == /\ pc[0] = "CloseWestDoor"
                 /\ lockCommand' = [command |-> "change_door", open |-> FALSE, side |-> "west"]
                 /\ pc' = [pc EXCEPT ![0] = "WestDoorClosedIn"]
                 /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                 waterLevel, shipLocation, shipStatus, 
                                 requests, permissions, perm, req >>

WestDoorClosedIn == /\ pc[0] = "WestDoorClosedIn"
                    /\ lockCommand.command = "finished"
                    /\ pc' = [pc EXCEPT ![0] = "RequestToOutW"]
                    /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                    waterLevel, shipLocation, shipStatus, 
                                    lockCommand, requests, permissions, perm, 
                                    req >>

RequestToOutW == /\ pc[0] = "RequestToOutW"
                 /\ requests /= <<>>
                 /\ req' = Head(requests)
                 /\ requests' = Tail(requests)
                 /\ pc' = [pc EXCEPT ![0] = "IncreaseWaterLevel"]
                 /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                 waterLevel, shipLocation, shipStatus, 
                                 lockCommand, permissions, perm >>

IncreaseWaterLevel == /\ pc[0] = "IncreaseWaterLevel"
                      /\ lockCommand' = [command |-> "change_valve", open |-> TRUE, side |-> "high"]
                      /\ pc' = [pc EXCEPT ![0] = "WaterLevelIncreased"]
                      /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                      waterLevel, shipLocation, shipStatus, 
                                      requests, permissions, perm, req >>

WaterLevelIncreased == /\ pc[0] = "WaterLevelIncreased"
                       /\ lockCommand.command = "finished"
                       /\ pc' = [pc EXCEPT ![0] = "CloseHighValve"]
                       /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                       waterLevel, shipLocation, shipStatus, 
                                       lockCommand, requests, permissions, 
                                       perm, req >>

CloseHighValve == /\ pc[0] = "CloseHighValve"
                  /\ lockCommand' = [command |-> "change_valve", open |-> FALSE, side |-> "high"]
                  /\ pc' = [pc EXCEPT ![0] = "HighValveCLosed"]
                  /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                  waterLevel, shipLocation, shipStatus, 
                                  requests, permissions, perm, req >>

HighValveCLosed == /\ pc[0] = "HighValveCLosed"
                   /\ lockCommand.command = "finished"
                   /\ pc' = [pc EXCEPT ![0] = "OpenEastDoorW"]
                   /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                   waterLevel, shipLocation, shipStatus, 
                                   lockCommand, requests, permissions, perm, 
                                   req >>

OpenEastDoorW == /\ pc[0] = "OpenEastDoorW"
                 /\ lockCommand' = [command |-> "change_door", open |-> TRUE, side|-> "east"]
                 /\ pc' = [pc EXCEPT ![0] = "EastDoorOpenedInW"]
                 /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                 waterLevel, shipLocation, shipStatus, 
                                 requests, permissions, perm, req >>

EastDoorOpenedInW == /\ pc[0] = "EastDoorOpenedInW"
                     /\ lockCommand.command = "finished"
                     /\ pc' = [pc EXCEPT ![0] = "GrantPermissionOutW"]
                     /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                     waterLevel, shipLocation, shipStatus, 
                                     lockCommand, requests, permissions, perm, 
                                     req >>

GrantPermissionOutW == /\ pc[0] = "GrantPermissionOutW"
                       /\ permissions' = Append(permissions, ([lock |-> req.lock, granted |-> TRUE]))
                       /\ pc' = [pc EXCEPT ![0] = "WaitExitW"]
                       /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                       waterLevel, shipLocation, shipStatus, 
                                       lockCommand, requests, perm, req >>

WaitExitW == /\ pc[0] = "WaitExitW"
             /\ ~InLock
             /\ pc' = [pc EXCEPT ![0] = "MainLoop"]
             /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                             waterLevel, shipLocation, shipStatus, lockCommand, 
                             requests, permissions, perm, req >>

WaitForReadyE == /\ pc[0] = "WaitForReadyE"
                 /\ lockCommand.command = "finished"
                 /\ pc' = [pc EXCEPT ![0] = "OpenEastDoorE"]
                 /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                 waterLevel, shipLocation, shipStatus, 
                                 lockCommand, requests, permissions, perm, req >>

OpenEastDoorE == /\ pc[0] = "OpenEastDoorE"
                 /\ lockCommand' = [command |-> "change_door", open |-> TRUE, side |-> "east"]
                 /\ pc' = [pc EXCEPT ![0] = "EastDoorOpened"]
                 /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                 waterLevel, shipLocation, shipStatus, 
                                 requests, permissions, perm, req >>

EastDoorOpened == /\ pc[0] = "EastDoorOpened"
                  /\ lockCommand.command = "finished"
                  /\ pc' = [pc EXCEPT ![0] = "GrantPermissionE"]
                  /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                  waterLevel, shipLocation, shipStatus, 
                                  lockCommand, requests, permissions, perm, 
                                  req >>

GrantPermissionE == /\ pc[0] = "GrantPermissionE"
                    /\ permissions' = Append(permissions, ([lock |-> req.lock, granted |-> TRUE]))
                    /\ pc' = [pc EXCEPT ![0] = "WaitForEnterE"]
                    /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                    waterLevel, shipLocation, shipStatus, 
                                    lockCommand, requests, perm, req >>

WaitForEnterE == /\ pc[0] = "WaitForEnterE"
                 /\ InLock
                 /\ pc' = [pc EXCEPT ![0] = "CloseEastDoor"]
                 /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                 waterLevel, shipLocation, shipStatus, 
                                 lockCommand, requests, permissions, perm, req >>

CloseEastDoor == /\ pc[0] = "CloseEastDoor"
                 /\ lockCommand' = [command |-> "change_door", open |-> FALSE, side |-> "east"]
                 /\ pc' = [pc EXCEPT ![0] = "EastDoorClosedIn"]
                 /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                 waterLevel, shipLocation, shipStatus, 
                                 requests, permissions, perm, req >>

EastDoorClosedIn == /\ pc[0] = "EastDoorClosedIn"
                    /\ lockCommand.command = "finished"
                    /\ pc' = [pc EXCEPT ![0] = "RequestToOutE"]
                    /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                    waterLevel, shipLocation, shipStatus, 
                                    lockCommand, requests, permissions, perm, 
                                    req >>

RequestToOutE == /\ pc[0] = "RequestToOutE"
                 /\ requests /= <<>>
                 /\ req' = Head(requests)
                 /\ requests' = Tail(requests)
                 /\ pc' = [pc EXCEPT ![0] = "DecreaseWaterLevel"]
                 /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                 waterLevel, shipLocation, shipStatus, 
                                 lockCommand, permissions, perm >>

DecreaseWaterLevel == /\ pc[0] = "DecreaseWaterLevel"
                      /\ lockCommand' = [command |-> "change_valve", open |-> TRUE, side |-> "low"]
                      /\ pc' = [pc EXCEPT ![0] = "WaterLevelDecreased"]
                      /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                      waterLevel, shipLocation, shipStatus, 
                                      requests, permissions, perm, req >>

WaterLevelDecreased == /\ pc[0] = "WaterLevelDecreased"
                       /\ lockCommand.command = "finished"
                       /\ pc' = [pc EXCEPT ![0] = "CloseLowValve"]
                       /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                       waterLevel, shipLocation, shipStatus, 
                                       lockCommand, requests, permissions, 
                                       perm, req >>

CloseLowValve == /\ pc[0] = "CloseLowValve"
                 /\ lockCommand' = [command |-> "change_valve", open |-> FALSE, side |-> "low"]
                 /\ pc' = [pc EXCEPT ![0] = "LowValveCLosed"]
                 /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                 waterLevel, shipLocation, shipStatus, 
                                 requests, permissions, perm, req >>

LowValveCLosed == /\ pc[0] = "LowValveCLosed"
                  /\ lockCommand.command = "finished"
                  /\ pc' = [pc EXCEPT ![0] = "WaitForWaterLow"]
                  /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                  waterLevel, shipLocation, shipStatus, 
                                  lockCommand, requests, permissions, perm, 
                                  req >>

WaitForWaterLow == /\ pc[0] = "WaitForWaterLow"
                   /\ waterLevel = "low"
                   /\ pc' = [pc EXCEPT ![0] = "OpenWestDoorE"]
                   /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                   waterLevel, shipLocation, shipStatus, 
                                   lockCommand, requests, permissions, perm, 
                                   req >>

OpenWestDoorE == /\ pc[0] = "OpenWestDoorE"
                 /\ lockCommand' = [command |-> "change_door", open |-> TRUE, side |-> "west"]
                 /\ pc' = [pc EXCEPT ![0] = "WestDoorOpenedInE"]
                 /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                 waterLevel, shipLocation, shipStatus, 
                                 requests, permissions, perm, req >>

WestDoorOpenedInE == /\ pc[0] = "WestDoorOpenedInE"
                     /\ lockCommand.command = "finished"
                     /\ pc' = [pc EXCEPT ![0] = "GrantPermissionOutE"]
                     /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                     waterLevel, shipLocation, shipStatus, 
                                     lockCommand, requests, permissions, perm, 
                                     req >>

GrantPermissionOutE == /\ pc[0] = "GrantPermissionOutE"
                       /\ permissions' = Append(permissions, ([lock |-> req.lock, granted |-> TRUE]))
                       /\ pc' = [pc EXCEPT ![0] = "WaitExitE"]
                       /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                       waterLevel, shipLocation, shipStatus, 
                                       lockCommand, requests, perm, req >>

WaitExitE == /\ pc[0] = "WaitExitE"
             /\ ~InLock
             /\ pc' = [pc EXCEPT ![0] = "MainLoop"]
             /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                             waterLevel, shipLocation, shipStatus, lockCommand, 
                             requests, permissions, perm, req >>

controlProcess == MainLoop \/ ControlStart \/ WaitForReadyW
                     \/ OpenWestDoorW \/ WestDoorOpened \/ GrantPermissionW
                     \/ WaitForEnterW \/ CloseWestDoor \/ WestDoorClosedIn
                     \/ RequestToOutW \/ IncreaseWaterLevel
                     \/ WaterLevelIncreased \/ CloseHighValve
                     \/ HighValveCLosed \/ OpenEastDoorW
                     \/ EastDoorOpenedInW \/ GrantPermissionOutW
                     \/ WaitExitW \/ WaitForReadyE \/ OpenEastDoorE
                     \/ EastDoorOpened \/ GrantPermissionE \/ WaitForEnterE
                     \/ CloseEastDoor \/ EastDoorClosedIn \/ RequestToOutE
                     \/ DecreaseWaterLevel \/ WaterLevelDecreased
                     \/ CloseLowValve \/ LowValveCLosed \/ WaitForWaterLow
                     \/ OpenWestDoorE \/ WestDoorOpenedInE
                     \/ GrantPermissionOutE \/ WaitExitE

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
\* Last modified Fri Oct 17 09:42:03 CEST 2025 by iyladakeekarjai
\* Last modified Wed Oct 08 16:56:23 CEST 2025 by 20241642
\* Last modified Wed Sep 24 11:08:53 CEST 2025 by mvolk
\* Created Thu Aug 28 11:30:23 CEST 2025 by mvolk
