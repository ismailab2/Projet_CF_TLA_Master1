---------------- MODULE DM_Mutex ----------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets

CONSTANT N
ProcSet1 == 1..N

ASSUME N >= 2

(*--fair algorithm DM_Mutex

variables
  Messages     = <<>>;
  clocks       = [i \in 1..N |-> 0];
  accordEnvoye = [i \in 1..N |-> 0];
  accordTS     = [i \in 1..N |-> -1];
  waitQueue    = [i \in 1..N |-> <<>>];
  nbAccords    = [i \in 1..N |-> 0];
  wantsCS      = [i \in 1..N |-> FALSE];
  gotEchec     = [i \in 1..N |-> FALSE];

define

  Left(i)    == ((i - 2) % N) + 1
  Right(i)   == (i % N) + 1
  Voisins(i) == {Left(i), Right(i)}
  NbVoisins  == 2

  RemoveAt(seq, k) ==
    SubSeq(seq, 1, k-1) \o SubSeq(seq, k+1, Len(seq))

  QHead(q) == q[1]
  QTail(q) == SubSeq(q, 2, Len(q))

end define;

macro IncClock(i) begin
  clocks[i] := clocks[i] + 1;
end macro;

\* Horloge de Lamport : max(local, recu) + 1
macro SyncClock(i, ts) begin
  clocks[i] := (IF clocks[i] > ts THEN clocks[i] ELSE ts) + 1;
end macro;

macro Send(t, from, to, ts) begin
  Messages := Append(Messages,
    [type |-> t, ts |-> ts, from |-> from, to |-> to]);
end macro;


fair process p \in ProcSet1
variables
  k     = 0;
  found = FALSE;
  msg   = [type |-> "", ts |-> 0, from |-> 0, to |-> 0];
begin


\* DEMANDE
Request:
  wantsCS[self]   := TRUE;
  gotEchec[self]  := FALSE;
  nbAccords[self] := 0;
  IncClock(self);
S1:
  Send("DEMANDE", self, Left(self),  clocks[self]);
S2:
  Send("DEMANDE", self, Right(self), clocks[self]);

\* ATTENTE
\* Boucle : on traite un message a la fois jusqu'a avoir 2 ACCORD.
\* on traite TOUS les types de messages (pas seulement ACCORD)
\* pour eviter les interblocages.
Wait:
  if nbAccords[self] = NbVoisins then goto CS end if;

I:
  found := FALSE;
  k     := 1;

Scan:
  while k <= Len(Messages) /\ ~found do
    if Messages[k].to = self then
      msg      := Messages[k];
      Messages := RemoveAt(Messages, k);
      found    := TRUE;
    else
      k := k + 1;
    end if;
  end while;

  if ~found then goto Wait end if;

  \* ACCORD recu
 II: if msg.type = "ACCORD" then
    SyncClock(self, msg.ts);
    nbAccords[self] := nbAccords[self] + 1;

  \* ECHEC recu : on enregistre l'echec, on met la demande en file.
  \* (L'emetteur nous mettra en file et nous enverra un ACCORD plus tard.)
  elsif msg.type = "ECHEC" then
    SyncClock(self, msg.ts);
    gotEchec[self] := TRUE;

  \* DEMANDE recue pendant qu'on attend soi-meme
  \* Trois cas selon la priorite relative.
  elsif msg.type = "DEMANDE" then
    SyncClock(self, msg.ts);

    \* CAS 1 — Aucun accord en cours : on accorde directement.
    if accordEnvoye[self] = 0 then
      S5:
        IncClock(self);
        Send("ACCORD", self, msg.from, clocks[self]);
        accordEnvoye[self] := msg.from;
        accordTS[self]     := msg.ts;

    \* CAS 2 — Accord en cours mais la nouvelle demande est plus prioritaire
    \*          (timestamp plus petit, ou egal avec id plus petit) . On sonde le detenteur actuel.
    elsif (accordTS[self] > msg.ts)
       \/ (accordTS[self] = msg.ts /\ accordEnvoye[self] > msg.from)
    then
      S4:
        IncClock(self);
        Send("SONDAGE", self, accordEnvoye[self], clocks[self]);
        waitQueue[self] :=
          Append(waitQueue[self], [from |-> msg.from, ts |-> msg.ts]);

    \* CAS 3 — Accord en cours avec priorite plus haute que la demande. On refuse (ECHEC) et on met en file.
    else
      S3:
        IncClock(self);
        Send("ECHEC", self, msg.from, clocks[self]);
        waitQueue[self] :=
          Append(waitQueue[self], [from |-> msg.from, ts |-> msg.ts]);
    end if;

  \* SONDAGE recu pendant qu'on attend
  \* on restitue si on a recu un ECHEC OU si on n'a pas encore . recu de nouvel ACCORD (nbAccords < NbVoisins).
  elsif msg.type = "SONDAGE" then
    SyncClock(self, msg.ts);

    if gotEchec[self] \/ nbAccords[self] < NbVoisins then
      S6:
        IncClock(self);
        Send("RESTITUTION", self, msg.from, clocks[self]);
    end if;

  \* RESTITUTION recue
  \* Spec : accorde a la 1ere demande de la file, puis place l'emetteur de la RESTITUTION dans la file.
  elsif msg.type = "RESTITUTION" then
    SyncClock(self, msg.ts);

    if Len(waitQueue[self]) > 0 then
      I1:
        IncClock(self);
        Send("ACCORD", self,
             QHead(waitQueue[self]).from,
             clocks[self]);
        accordEnvoye[self] := QHead(waitQueue[self]).from;
        accordTS[self]     := QHead(waitQueue[self]).ts;
        waitQueue[self]    := QTail(waitQueue[self]);
    else
      \* File vide : on remet a zero, l'emetteur va rejoindre la file
      accordEnvoye[self] := 0;
      accordTS[self]     := -1;
    end if;

    \* L'emetteur de RESTITUTION rejoint la file d'attente.
    W:
      waitQueue[self] :=
        Append(waitQueue[self],
               [from |-> msg.from, ts |-> msg.ts]);

  \* LIBERATION recue pendant qu'on attend, d'un autre processus)
  \* on supprime l'emetteur de la file, puis accorde a la 1ere demande.
  elsif msg.type = "LIBERATION" then
    SyncClock(self, msg.ts);

    waitQueue[self] :=
      SelectSeq(waitQueue[self], LAMBDA e : e.from # msg.from);

    if Len(waitQueue[self]) > 0 then
      I2:
        IncClock(self);
        Send("ACCORD", self,
             QHead(waitQueue[self]).from,
             clocks[self]);
        accordEnvoye[self] := QHead(waitQueue[self]).from;
        accordTS[self]     := QHead(waitQueue[self]).ts;
        waitQueue[self]    := QTail(waitQueue[self]);
    else
      accordEnvoye[self] := 0;
      accordTS[self]     := -1;
    end if;

  end if;

W1:
  goto Wait;

\* SECTION CRITIQUE
CS:
  IncClock(self);

\* LIBERATION
\* on Reinitialise l'etat local, previent les deux voisins.
Release:
  wantsCS[self]      := FALSE;
  nbAccords[self]    := 0;
  accordEnvoye[self] := 0;
  accordTS[self]     := -1;
  waitQueue[self]    := <<>>;
  gotEchec[self]     := FALSE;
  IncClock(self);
S7:
  Send("LIBERATION", self, Left(self),  clocks[self]);
S8:
  Send("LIBERATION", self, Right(self), clocks[self]);

  goto Request;

end process;
end algorithm;*)

\* BEGIN TRANSLATION (chksum(pcal) = "3ec615d6" /\ chksum(tla) = "33b860be") (chksum(pcal) = "3ec615d6" /\ chksum(tla) = "33b860be") (chksum(pcal) = "3ec615d6" /\ chksum(tla) = "33b860be") (chksum(pcal) = "18c28796" /\ chksum(tla) = "600187") (chksum(pcal) = "18c28796" /\ chksum(tla) = "600187") (chksum(pcal) = "18c28796" /\ chksum(tla) = "600187") (chksum(pcal) = "af2b480c" /\ chksum(tla) = "a9601f75") (chksum(pcal) = "af2b480c" /\ chksum(tla) = "a9601f75") (chksum(pcal) = "af2b480c" /\ chksum(tla) = "a9601f75")
VARIABLES Messages, clocks, accordEnvoye, accordTS, waitQueue, nbAccords, 
          wantsCS, gotEchec, pc

(* define statement *)
Left(i)    == ((i - 2) % N) + 1
Right(i)   == (i % N) + 1
Voisins(i) == {Left(i), Right(i)}
NbVoisins  == 2

RemoveAt(seq, k) ==
  SubSeq(seq, 1, k-1) \o SubSeq(seq, k+1, Len(seq))

QHead(q) == q[1]
QTail(q) == SubSeq(q, 2, Len(q))

VARIABLES k, found, msg

vars == << Messages, clocks, accordEnvoye, accordTS, waitQueue, nbAccords, 
           wantsCS, gotEchec, pc, k, found, msg >>

ProcSet == (ProcSet1)

Init == (* Global variables *)
        /\ Messages = <<>>
        /\ clocks = [i \in 1..N |-> 0]
        /\ accordEnvoye = [i \in 1..N |-> 0]
        /\ accordTS = [i \in 1..N |-> -1]
        /\ waitQueue = [i \in 1..N |-> <<>>]
        /\ nbAccords = [i \in 1..N |-> 0]
        /\ wantsCS = [i \in 1..N |-> FALSE]
        /\ gotEchec = [i \in 1..N |-> FALSE]
        (* Process p *)
        /\ k = [self \in ProcSet1 |-> 0]
        /\ found = [self \in ProcSet1 |-> FALSE]
        /\ msg = [self \in ProcSet1 |-> [type |-> "", ts |-> 0, from |-> 0, to |-> 0]]
        /\ pc = [self \in ProcSet |-> "Request"]

Request(self) == /\ pc[self] = "Request"
                 /\ wantsCS' = [wantsCS EXCEPT ![self] = TRUE]
                 /\ gotEchec' = [gotEchec EXCEPT ![self] = FALSE]
                 /\ nbAccords' = [nbAccords EXCEPT ![self] = 0]
                 /\ clocks' = [clocks EXCEPT ![self] = clocks[self] + 1]
                 /\ pc' = [pc EXCEPT ![self] = "S1"]
                 /\ UNCHANGED << Messages, accordEnvoye, accordTS, waitQueue, 
                                 k, found, msg >>

S1(self) == /\ pc[self] = "S1"
            /\ Messages' =           Append(Messages,
                           [type |-> "DEMANDE", ts |-> (clocks[self]), from |-> self, to |-> (Left(self))])
            /\ pc' = [pc EXCEPT ![self] = "S2"]
            /\ UNCHANGED << clocks, accordEnvoye, accordTS, waitQueue, 
                            nbAccords, wantsCS, gotEchec, k, found, msg >>

S2(self) == /\ pc[self] = "S2"
            /\ Messages' =           Append(Messages,
                           [type |-> "DEMANDE", ts |-> (clocks[self]), from |-> self, to |-> (Right(self))])
            /\ pc' = [pc EXCEPT ![self] = "Wait"]
            /\ UNCHANGED << clocks, accordEnvoye, accordTS, waitQueue, 
                            nbAccords, wantsCS, gotEchec, k, found, msg >>

Wait(self) == /\ pc[self] = "Wait"
              /\ IF nbAccords[self] = NbVoisins
                    THEN /\ pc' = [pc EXCEPT ![self] = "CS"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "I"]
              /\ UNCHANGED << Messages, clocks, accordEnvoye, accordTS, 
                              waitQueue, nbAccords, wantsCS, gotEchec, k, 
                              found, msg >>

I(self) == /\ pc[self] = "I"
           /\ found' = [found EXCEPT ![self] = FALSE]
           /\ k' = [k EXCEPT ![self] = 1]
           /\ pc' = [pc EXCEPT ![self] = "Scan"]
           /\ UNCHANGED << Messages, clocks, accordEnvoye, accordTS, waitQueue, 
                           nbAccords, wantsCS, gotEchec, msg >>

Scan(self) == /\ pc[self] = "Scan"
              /\ IF k[self] <= Len(Messages) /\ ~found[self]
                    THEN /\ IF Messages[k[self]].to = self
                               THEN /\ msg' = [msg EXCEPT ![self] = Messages[k[self]]]
                                    /\ Messages' = RemoveAt(Messages, k[self])
                                    /\ found' = [found EXCEPT ![self] = TRUE]
                                    /\ k' = k
                               ELSE /\ k' = [k EXCEPT ![self] = k[self] + 1]
                                    /\ UNCHANGED << Messages, found, msg >>
                         /\ pc' = [pc EXCEPT ![self] = "Scan"]
                    ELSE /\ IF ~found[self]
                               THEN /\ pc' = [pc EXCEPT ![self] = "Wait"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "II"]
                         /\ UNCHANGED << Messages, k, found, msg >>
              /\ UNCHANGED << clocks, accordEnvoye, accordTS, waitQueue, 
                              nbAccords, wantsCS, gotEchec >>

II(self) == /\ pc[self] = "II"
            /\ IF msg[self].type = "ACCORD"
                  THEN /\ clocks' = [clocks EXCEPT ![self] = (IF clocks[self] > (msg[self].ts) THEN clocks[self] ELSE (msg[self].ts)) + 1]
                       /\ nbAccords' = [nbAccords EXCEPT ![self] = nbAccords[self] + 1]
                       /\ pc' = [pc EXCEPT ![self] = "W1"]
                       /\ UNCHANGED << accordEnvoye, accordTS, waitQueue, 
                                       gotEchec >>
                  ELSE /\ IF msg[self].type = "ECHEC"
                             THEN /\ clocks' = [clocks EXCEPT ![self] = (IF clocks[self] > (msg[self].ts) THEN clocks[self] ELSE (msg[self].ts)) + 1]
                                  /\ gotEchec' = [gotEchec EXCEPT ![self] = TRUE]
                                  /\ pc' = [pc EXCEPT ![self] = "W1"]
                                  /\ UNCHANGED << accordEnvoye, accordTS, 
                                                  waitQueue >>
                             ELSE /\ IF msg[self].type = "DEMANDE"
                                        THEN /\ clocks' = [clocks EXCEPT ![self] = (IF clocks[self] > (msg[self].ts) THEN clocks[self] ELSE (msg[self].ts)) + 1]
                                             /\ IF accordEnvoye[self] = 0
                                                   THEN /\ pc' = [pc EXCEPT ![self] = "S5"]
                                                   ELSE /\ IF    (accordTS[self] > msg[self].ts)
                                                              \/ (accordTS[self] = msg[self].ts /\ accordEnvoye[self] > msg[self].from)
                                                              THEN /\ pc' = [pc EXCEPT ![self] = "S4"]
                                                              ELSE /\ pc' = [pc EXCEPT ![self] = "S3"]
                                             /\ UNCHANGED << accordEnvoye, 
                                                             accordTS, 
                                                             waitQueue >>
                                        ELSE /\ IF msg[self].type = "SONDAGE"
                                                   THEN /\ clocks' = [clocks EXCEPT ![self] = (IF clocks[self] > (msg[self].ts) THEN clocks[self] ELSE (msg[self].ts)) + 1]
                                                        /\ IF gotEchec[self] \/ nbAccords[self] < NbVoisins
                                                              THEN /\ pc' = [pc EXCEPT ![self] = "S6"]
                                                              ELSE /\ pc' = [pc EXCEPT ![self] = "W1"]
                                                        /\ UNCHANGED << accordEnvoye, 
                                                                        accordTS, 
                                                                        waitQueue >>
                                                   ELSE /\ IF msg[self].type = "RESTITUTION"
                                                              THEN /\ clocks' = [clocks EXCEPT ![self] = (IF clocks[self] > (msg[self].ts) THEN clocks[self] ELSE (msg[self].ts)) + 1]
                                                                   /\ IF Len(waitQueue[self]) > 0
                                                                         THEN /\ pc' = [pc EXCEPT ![self] = "I1"]
                                                                              /\ UNCHANGED << accordEnvoye, 
                                                                                              accordTS >>
                                                                         ELSE /\ accordEnvoye' = [accordEnvoye EXCEPT ![self] = 0]
                                                                              /\ accordTS' = [accordTS EXCEPT ![self] = -1]
                                                                              /\ pc' = [pc EXCEPT ![self] = "W"]
                                                                   /\ UNCHANGED waitQueue
                                                              ELSE /\ IF msg[self].type = "LIBERATION"
                                                                         THEN /\ clocks' = [clocks EXCEPT ![self] = (IF clocks[self] > (msg[self].ts) THEN clocks[self] ELSE (msg[self].ts)) + 1]
                                                                              /\ waitQueue' = [waitQueue EXCEPT ![self] = SelectSeq(waitQueue[self], LAMBDA e : e.from # msg[self].from)]
                                                                              /\ IF Len(waitQueue'[self]) > 0
                                                                                    THEN /\ pc' = [pc EXCEPT ![self] = "I2"]
                                                                                         /\ UNCHANGED << accordEnvoye, 
                                                                                                         accordTS >>
                                                                                    ELSE /\ accordEnvoye' = [accordEnvoye EXCEPT ![self] = 0]
                                                                                         /\ accordTS' = [accordTS EXCEPT ![self] = -1]
                                                                                         /\ pc' = [pc EXCEPT ![self] = "W1"]
                                                                         ELSE /\ pc' = [pc EXCEPT ![self] = "W1"]
                                                                              /\ UNCHANGED << clocks, 
                                                                                              accordEnvoye, 
                                                                                              accordTS, 
                                                                                              waitQueue >>
                                  /\ UNCHANGED gotEchec
                       /\ UNCHANGED nbAccords
            /\ UNCHANGED << Messages, wantsCS, k, found, msg >>

S5(self) == /\ pc[self] = "S5"
            /\ clocks' = [clocks EXCEPT ![self] = clocks[self] + 1]
            /\ Messages' =           Append(Messages,
                           [type |-> "ACCORD", ts |-> (clocks'[self]), from |-> self, to |-> (msg[self].from)])
            /\ accordEnvoye' = [accordEnvoye EXCEPT ![self] = msg[self].from]
            /\ accordTS' = [accordTS EXCEPT ![self] = msg[self].ts]
            /\ pc' = [pc EXCEPT ![self] = "W1"]
            /\ UNCHANGED << waitQueue, nbAccords, wantsCS, gotEchec, k, found, 
                            msg >>

S4(self) == /\ pc[self] = "S4"
            /\ clocks' = [clocks EXCEPT ![self] = clocks[self] + 1]
            /\ Messages' =           Append(Messages,
                           [type |-> "SONDAGE", ts |-> (clocks'[self]), from |-> self, to |-> (accordEnvoye[self])])
            /\ waitQueue' = [waitQueue EXCEPT ![self] = Append(waitQueue[self], [from |-> msg[self].from, ts |-> msg[self].ts])]
            /\ pc' = [pc EXCEPT ![self] = "W1"]
            /\ UNCHANGED << accordEnvoye, accordTS, nbAccords, wantsCS, 
                            gotEchec, k, found, msg >>

S3(self) == /\ pc[self] = "S3"
            /\ clocks' = [clocks EXCEPT ![self] = clocks[self] + 1]
            /\ Messages' =           Append(Messages,
                           [type |-> "ECHEC", ts |-> (clocks'[self]), from |-> self, to |-> (msg[self].from)])
            /\ waitQueue' = [waitQueue EXCEPT ![self] = Append(waitQueue[self], [from |-> msg[self].from, ts |-> msg[self].ts])]
            /\ pc' = [pc EXCEPT ![self] = "W1"]
            /\ UNCHANGED << accordEnvoye, accordTS, nbAccords, wantsCS, 
                            gotEchec, k, found, msg >>

S6(self) == /\ pc[self] = "S6"
            /\ clocks' = [clocks EXCEPT ![self] = clocks[self] + 1]
            /\ Messages' =           Append(Messages,
                           [type |-> "RESTITUTION", ts |-> (clocks'[self]), from |-> self, to |-> (msg[self].from)])
            /\ pc' = [pc EXCEPT ![self] = "W1"]
            /\ UNCHANGED << accordEnvoye, accordTS, waitQueue, nbAccords, 
                            wantsCS, gotEchec, k, found, msg >>

W(self) == /\ pc[self] = "W"
           /\ waitQueue' = [waitQueue EXCEPT ![self] = Append(waitQueue[self],
                                                              [from |-> msg[self].from, ts |-> msg[self].ts])]
           /\ pc' = [pc EXCEPT ![self] = "W1"]
           /\ UNCHANGED << Messages, clocks, accordEnvoye, accordTS, nbAccords, 
                           wantsCS, gotEchec, k, found, msg >>

I1(self) == /\ pc[self] = "I1"
            /\ clocks' = [clocks EXCEPT ![self] = clocks[self] + 1]
            /\ Messages' =           Append(Messages,
                           [type |-> "ACCORD", ts |-> (clocks'[self]), from |-> self, to |-> (QHead(waitQueue[self]).from)])
            /\ accordEnvoye' = [accordEnvoye EXCEPT ![self] = QHead(waitQueue[self]).from]
            /\ accordTS' = [accordTS EXCEPT ![self] = QHead(waitQueue[self]).ts]
            /\ waitQueue' = [waitQueue EXCEPT ![self] = QTail(waitQueue[self])]
            /\ pc' = [pc EXCEPT ![self] = "W"]
            /\ UNCHANGED << nbAccords, wantsCS, gotEchec, k, found, msg >>

I2(self) == /\ pc[self] = "I2"
            /\ clocks' = [clocks EXCEPT ![self] = clocks[self] + 1]
            /\ Messages' =           Append(Messages,
                           [type |-> "ACCORD", ts |-> (clocks'[self]), from |-> self, to |-> (QHead(waitQueue[self]).from)])
            /\ accordEnvoye' = [accordEnvoye EXCEPT ![self] = QHead(waitQueue[self]).from]
            /\ accordTS' = [accordTS EXCEPT ![self] = QHead(waitQueue[self]).ts]
            /\ waitQueue' = [waitQueue EXCEPT ![self] = QTail(waitQueue[self])]
            /\ pc' = [pc EXCEPT ![self] = "W1"]
            /\ UNCHANGED << nbAccords, wantsCS, gotEchec, k, found, msg >>

W1(self) == /\ pc[self] = "W1"
            /\ pc' = [pc EXCEPT ![self] = "Wait"]
            /\ UNCHANGED << Messages, clocks, accordEnvoye, accordTS, 
                            waitQueue, nbAccords, wantsCS, gotEchec, k, found, 
                            msg >>

CS(self) == /\ pc[self] = "CS"
            /\ clocks' = [clocks EXCEPT ![self] = clocks[self] + 1]
            /\ pc' = [pc EXCEPT ![self] = "Release"]
            /\ UNCHANGED << Messages, accordEnvoye, accordTS, waitQueue, 
                            nbAccords, wantsCS, gotEchec, k, found, msg >>

Release(self) == /\ pc[self] = "Release"
                 /\ wantsCS' = [wantsCS EXCEPT ![self] = FALSE]
                 /\ nbAccords' = [nbAccords EXCEPT ![self] = 0]
                 /\ accordEnvoye' = [accordEnvoye EXCEPT ![self] = 0]
                 /\ accordTS' = [accordTS EXCEPT ![self] = -1]
                 /\ waitQueue' = [waitQueue EXCEPT ![self] = <<>>]
                 /\ gotEchec' = [gotEchec EXCEPT ![self] = FALSE]
                 /\ clocks' = [clocks EXCEPT ![self] = clocks[self] + 1]
                 /\ pc' = [pc EXCEPT ![self] = "S7"]
                 /\ UNCHANGED << Messages, k, found, msg >>

S7(self) == /\ pc[self] = "S7"
            /\ Messages' =           Append(Messages,
                           [type |-> "LIBERATION", ts |-> (clocks[self]), from |-> self, to |-> (Left(self))])
            /\ pc' = [pc EXCEPT ![self] = "S8"]
            /\ UNCHANGED << clocks, accordEnvoye, accordTS, waitQueue, 
                            nbAccords, wantsCS, gotEchec, k, found, msg >>

S8(self) == /\ pc[self] = "S8"
            /\ Messages' =           Append(Messages,
                           [type |-> "LIBERATION", ts |-> (clocks[self]), from |-> self, to |-> (Right(self))])
            /\ pc' = [pc EXCEPT ![self] = "Request"]
            /\ UNCHANGED << clocks, accordEnvoye, accordTS, waitQueue, 
                            nbAccords, wantsCS, gotEchec, k, found, msg >>

p(self) == Request(self) \/ S1(self) \/ S2(self) \/ Wait(self) \/ I(self)
              \/ Scan(self) \/ II(self) \/ S5(self) \/ S4(self) \/ S3(self)
              \/ S6(self) \/ W(self) \/ I1(self) \/ I2(self) \/ W1(self)
              \/ CS(self) \/ Release(self) \/ S7(self) \/ S8(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet1: p(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in ProcSet1 : WF_vars(p(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

  \* TypeOk : invariant de typage
  TypeOk ==
    /\ Messages \in Seq([type  : {"DEMANDE","ACCORD","ECHEC",
                                   "SONDAGE","RESTITUTION","LIBERATION"},
                          ts   : Nat,
                          from : ProcSet1,
                          to   : ProcSet1])
    /\ clocks        \in [ProcSet1 -> Nat]
    /\ accordEnvoye  \in [ProcSet1 -> 0..N]
    /\ accordTS      \in [ProcSet1 -> {-1} \union Nat]
    /\ waitQueue     \in [ProcSet1 -> Seq([from : ProcSet1, ts : Nat])]
    /\ nbAccords     \in [ProcSet1 -> 0..NbVoisins]
    /\ wantsCS       \in [ProcSet1 -> BOOLEAN]
    /\ gotEchec      \in [ProcSet1 -> BOOLEAN]

  \* Invariant : chaque message est envoye a un voisin de son emetteur
  VoisinsOk ==
    \A idx \in 1..Len(Messages) :
      Messages[idx].to \in Voisins(Messages[idx].from)

  \* Invariant : deux messages du meme emetteur vers le meme destinataire ont des timestamps distincts.
  TimestampDistinct ==
    \A i, j \in 1..Len(Messages) :
      (i # j
       /\ Messages[i].from = Messages[j].from
       /\ Messages[i].to   = Messages[j].to)
      => Messages[i].ts # Messages[j].ts
   
   \* processus i est en section critique
  CS1(i) == pc[i] = "CS"

  \* Exclusion mutuelle : deux processus distincts ne peuvent pas etre simultanement en SC.
  Mutex == \A i, j \in ProcSet1 : (i # j) => ~(CS1(i) /\ CS1(j))

  
  \* Vivacite : tout processus qui demande la SC finit par y entrer.
  LivenessCS ==
    \A i \in ProcSet1 : wantsCS[i] ~> CS1(i)

=============================================================================
