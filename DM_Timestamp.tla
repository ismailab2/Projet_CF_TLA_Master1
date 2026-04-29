---------------------------- MODULE DM_Timestamp ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANT N
ProcSet1 == 1..N

ASSUME N >= 2

(*--algorithm DM_Timestamp

variables
  Messages = <<>>;
  clocks   = [i \in ProcSet1 |-> 0];
  sent     = [i \in ProcSet1 |-> FALSE];

define
  LeftNeighbour(i)  == ((i - 2) % N) + 1
  RightNeighbour(i) == (i % N) + 1
  Voisins(i)        == {LeftNeighbour(i), RightNeighbour(i)}

  MessagesFor(i, t) ==
    {k \in DOMAIN Messages :
       Messages[k].to = i /\ Messages[k].type = t}
end define;

macro IncClock(i) begin
  clocks[i] := clocks[i] + 1;
end macro;

macro SyncClock(i, ts) begin
  clocks[i] := (IF clocks[i] > ts THEN clocks[i] ELSE ts) + 1;
end macro;

macro Send(t, sender, receiver, ts) begin
  Messages := Append(Messages,
    [type |-> t,
     ts   |-> ts,
     from |-> sender,
     to   |-> receiver]);
end macro;

process proc \in ProcSet1
begin

  SendEnvoi:
    if ~sent[self] then
      IncClock(self);
      S1:
        Send("ENVOI", self, LeftNeighbour(self), clocks[self]);
      S2:
        Send("ENVOI", self, RightNeighbour(self), clocks[self]);
      sent[self] := TRUE;
    end if;

  HandleEnvoi:
    with k \in MessagesFor(self, "ENVOI") do
      SyncClock(self, Messages[k].ts);
      Send("CONFIRMATION", self, Messages[k].from, clocks[self]);
    end with;

  HandleConfirmation:
    with k \in MessagesFor(self, "CONFIRMATION") do
      SyncClock(self, Messages[k].ts);
    end with;

end process;
end algorithm;*)

\* BEGIN TRANSLATION (chksum(pcal) = "a0740dca" /\ chksum(tla) = "ddb5bb5d")
VARIABLES Messages, clocks, sent, pc

(* define statement *)
LeftNeighbour(i)  == ((i - 2) % N) + 1
RightNeighbour(i) == (i % N) + 1
Voisins(i)        == {LeftNeighbour(i), RightNeighbour(i)}

MessagesFor(i, t) ==
  {k \in DOMAIN Messages :
     Messages[k].to = i /\ Messages[k].type = t}


vars == << Messages, clocks, sent, pc >>

ProcSet == (ProcSet1)

Init == (* Global variables *)
        /\ Messages = <<>>
        /\ clocks = [i \in ProcSet1 |-> 0]
        /\ sent = [i \in ProcSet1 |-> FALSE]
        /\ pc = [self \in ProcSet |-> "SendEnvoi"]

SendEnvoi(self) == /\ pc[self] = "SendEnvoi"
                   /\ IF ~sent[self]
                         THEN /\ clocks' = [clocks EXCEPT ![self] = clocks[self] + 1]
                              /\ pc' = [pc EXCEPT ![self] = "S1"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "HandleEnvoi"]
                              /\ UNCHANGED clocks
                   /\ UNCHANGED << Messages, sent >>

S1(self) == /\ pc[self] = "S1"
            /\ Messages' =           Append(Messages,
                           [type |-> "ENVOI",
                            ts   |-> (clocks[self]),
                            from |-> self,
                            to   |-> (LeftNeighbour(self))])
            /\ pc' = [pc EXCEPT ![self] = "S2"]
            /\ UNCHANGED << clocks, sent >>

S2(self) == /\ pc[self] = "S2"
            /\ Messages' =           Append(Messages,
                           [type |-> "ENVOI",
                            ts   |-> (clocks[self]),
                            from |-> self,
                            to   |-> (RightNeighbour(self))])
            /\ sent' = [sent EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "HandleEnvoi"]
            /\ UNCHANGED clocks

HandleEnvoi(self) == /\ pc[self] = "HandleEnvoi"
                     /\ \E k \in MessagesFor(self, "ENVOI"):
                          /\ clocks' = [clocks EXCEPT ![self] = (IF clocks[self] > (Messages[k].ts) THEN clocks[self] ELSE (Messages[k].ts)) + 1]
                          /\ Messages' =           Append(Messages,
                                         [type |-> "CONFIRMATION",
                                          ts   |-> (clocks'[self]),
                                          from |-> self,
                                          to   |-> (Messages[k].from)])
                     /\ pc' = [pc EXCEPT ![self] = "HandleConfirmation"]
                     /\ sent' = sent

HandleConfirmation(self) == /\ pc[self] = "HandleConfirmation"
                            /\ \E k \in MessagesFor(self, "CONFIRMATION"):
                                 clocks' = [clocks EXCEPT ![self] = (IF clocks[self] > (Messages[k].ts) THEN clocks[self] ELSE (Messages[k].ts)) + 1]
                            /\ pc' = [pc EXCEPT ![self] = "Done"]
                            /\ UNCHANGED << Messages, sent >>

proc(self) == SendEnvoi(self) \/ S1(self) \/ S2(self) \/ HandleEnvoi(self)
                 \/ HandleConfirmation(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet1: proc(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

\* Invariants et propriétés

TypeOk ==
  /\ clocks   \in [ProcSet -> Nat]
  /\ sent     \in [ProcSet -> BOOLEAN]
  /\ Messages \in Seq([type : {"ENVOI", "CONFIRMATION"},
                        ts   : Nat,
                        from : ProcSet,
                        to   : ProcSet])


=============================================================================
