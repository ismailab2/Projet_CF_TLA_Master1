---------------- MODULE DM_Mutex ----------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets

CONSTANT N
ProcSet1 == 1..N

ASSUME N >= 2

(*--fair algorithm DM_Mutex

variables
  Messages     = [i \in 1..N |-> <<>>];
  clocks       = [i \in 1..N |-> 0];
  accordEnvoye = [i \in 1..N |-> 0];
  accordTS     = [i \in 1..N |-> -1];
  waitQueue    = [i \in 1..N |-> <<>>];
  nbAccords    = [i \in 1..N |-> 0];
  accordRecus  = [i \in 1..N |-> {}];
  accordRestitues = [i \in 1..N |-> {}];
  wantsCS      = [i \in 1..N |-> FALSE];
  gotEchec     = [i \in 1..N |-> FALSE];

define

  Left(i)    == ((i - 2) % N) + 1
  Right(i)   == (i % N) + 1
  Voisins(i) == {Left(i), Right(i)}
  NbVoisins  == 2

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
  Messages[to] := Append(Messages[to],
    [type |-> t, ts |-> ts, from |-> from, to |-> to]);
end macro;


fair process p \in ProcSet1
variables
  msg   = [type |-> "", ts |-> 0, from |-> 0, to |-> 0];
begin


\* DEMANDE
Request:
  wantsCS[self]   := TRUE;
  gotEchec[self]  := FALSE;
  nbAccords[self] := 0;
  accordRecus[self] := {};
  accordRestitues[self] := {};
  IncClock(self);
  Messages := [Messages EXCEPT
    ![Left(self)]  = Append(@, [type |-> "DEMANDE", ts |-> clocks[self], from |-> self, to |-> Left(self)]),
    ![Right(self)] = Append(@, [type |-> "DEMANDE", ts |-> clocks[self], from |-> self, to |-> Right(self)])];

\* ATTENTE
\* Boucle : on traite un message a la fois jusqu'a avoir 2 ACCORD.
\* on traite TOUS les types de messages (pas seulement ACCORD)
\* pour eviter les interblocages.
Wait:
  if nbAccords[self] = NbVoisins then 
    goto CS;
  elsif Len(Messages[self]) = 0 then
    goto Wait;
  else
    msg            := QHead(Messages[self]);
    Messages[self] := QTail(Messages[self]);
  end if;

  \* ACCORD recu
 II: if msg.type = "ACCORD" then
    SyncClock(self, msg.ts);
    if msg.from \notin accordRecus[self] 
      /\ msg.from \notin accordRestitues[self] then
      accordRecus[self] := accordRecus[self] \union {msg.from};
      nbAccords[self] := nbAccords[self] + 1;
    end if;

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
        accordRestitues[self] := accordRestitues[self] \union {msg.from};
        if msg.from \in accordRecus[self] then
          accordRecus[self] := accordRecus[self] \ {msg.from};
          nbAccords[self] := nbAccords[self] - 1;
        end if;
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
  accordRecus[self]  := {};
  accordRestitues[self] := {};
  accordTS[self]     := -1;
  waitQueue[self]    := <<>>;
  gotEchec[self]     := FALSE;
  IncClock(self);
  Messages := [Messages EXCEPT
    ![Left(self)]  = Append(@, [type |-> "LIBERATION", ts |-> clocks[self], from |-> self, to |-> Left(self)]),
    ![Right(self)] = Append(@, [type |-> "LIBERATION", ts |-> clocks[self], from |-> self, to |-> Right(self)])];

  goto Done;

end process;
end algorithm;*)
 
\* BEGIN TRANSLATION (chksum(pcal) = "db90c263" /\ chksum(tla) = "71b511df") (chksum(pcal) = "3ec615d6" /\ chksum(tla) = "33b860be") (chksum(pcal) = "3ec615d6" /\ chksum(tla) = "33b860be") (chksum(pcal) = "18c28796" /\ chksum(tla) = "600187") (chksum(pcal) = "18c28796" /\ chksum(tla) = "600187") (chksum(pcal) = "18c28796" /\ chksum(tla) = "600187") (chksum(pcal) = "af2b480c" /\ chksum(tla) = "a9601f75") (chksum(pcal) = "af2b480c" /\ chksum(tla) = "a9601f75") (chksum(pcal) = "af2b480c" /\ chksum(tla) = "a9601f75")
VARIABLES Messages, clocks, accordEnvoye, accordTS, waitQueue, nbAccords, 
          accordRecus, accordRestitues, wantsCS, gotEchec, pc

(* define statement *)
Left(i)    == ((i - 2) % N) + 1
Right(i)   == (i % N) + 1
Voisins(i) == {Left(i), Right(i)}
NbVoisins  == 2

QHead(q) == q[1]
QTail(q) == SubSeq(q, 2, Len(q))

VARIABLE msg

vars == << Messages, clocks, accordEnvoye, accordTS, waitQueue, nbAccords, 
           accordRecus, accordRestitues, wantsCS, gotEchec, pc, msg >>

ProcSet == (ProcSet1)

Init == (* Global variables *)
        /\ Messages = [i \in 1..N |-> <<>>]
        /\ clocks = [i \in 1..N |-> 0]
        /\ accordEnvoye = [i \in 1..N |-> 0]
        /\ accordTS = [i \in 1..N |-> -1]
        /\ waitQueue = [i \in 1..N |-> <<>>]
        /\ nbAccords = [i \in 1..N |-> 0]
        /\ accordRecus = [i \in 1..N |-> {}]
        /\ accordRestitues = [i \in 1..N |-> {}]
        /\ wantsCS = [i \in 1..N |-> FALSE]
        /\ gotEchec = [i \in 1..N |-> FALSE]
        (* Process p *)
        /\ msg = [self \in ProcSet1 |-> [type |-> "", ts |-> 0, from |-> 0, to |-> 0]]
        /\ pc = [self \in ProcSet |-> "Request"]

Request(self) == /\ pc[self] = "Request"
                 /\ wantsCS' = [wantsCS EXCEPT ![self] = TRUE]
                 /\ gotEchec' = [gotEchec EXCEPT ![self] = FALSE]
                 /\ nbAccords' = [nbAccords EXCEPT ![self] = 0]
                 /\ accordRecus' = [accordRecus EXCEPT ![self] = {}]
                 /\ accordRestitues' = [accordRestitues EXCEPT ![self] = {}]
                 /\ clocks' = [clocks EXCEPT ![self] = clocks[self] + 1]
                 /\ Messages' =           [Messages EXCEPT
                                ![Left(self)]  = Append(@, [type |-> "DEMANDE", ts |-> clocks'[self], from |-> self, to |-> Left(self)]),
                                ![Right(self)] = Append(@, [type |-> "DEMANDE", ts |-> clocks'[self], from |-> self, to |-> Right(self)])]
                 /\ pc' = [pc EXCEPT ![self] = "Wait"]
                 /\ UNCHANGED << accordEnvoye, accordTS, waitQueue, msg >>

Wait(self) == /\ pc[self] = "Wait"
              /\ IF nbAccords[self] = NbVoisins
                    THEN /\ pc' = [pc EXCEPT ![self] = "CS"]
                         /\ UNCHANGED << Messages, msg >>
                    ELSE /\ IF Len(Messages[self]) = 0
                               THEN /\ pc' = [pc EXCEPT ![self] = "Wait"]
                                    /\ UNCHANGED << Messages, msg >>
                               ELSE /\ msg' = [msg EXCEPT ![self] = QHead(Messages[self])]
                                    /\ Messages' = [Messages EXCEPT ![self] = QTail(Messages[self])]
                                    /\ pc' = [pc EXCEPT ![self] = "II"]
              /\ UNCHANGED << clocks, accordEnvoye, accordTS, waitQueue, 
                              nbAccords, accordRecus, accordRestitues, wantsCS, 
                              gotEchec >>

II(self) == /\ pc[self] = "II"
            /\ IF msg[self].type = "ACCORD"
                  THEN /\ clocks' = [clocks EXCEPT ![self] = (IF clocks[self] > (msg[self].ts) THEN clocks[self] ELSE (msg[self].ts)) + 1]
                       /\ IF  msg[self].from \notin accordRecus[self]
                             /\ msg[self].from \notin accordRestitues[self]
                             THEN /\ accordRecus' = [accordRecus EXCEPT ![self] = accordRecus[self] \union {msg[self].from}]
                                  /\ nbAccords' = [nbAccords EXCEPT ![self] = nbAccords[self] + 1]
                             ELSE /\ TRUE
                                  /\ UNCHANGED << nbAccords, accordRecus >>
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
                       /\ UNCHANGED << nbAccords, accordRecus >>
            /\ UNCHANGED << Messages, accordRestitues, wantsCS, msg >>

S5(self) == /\ pc[self] = "S5"
            /\ clocks' = [clocks EXCEPT ![self] = clocks[self] + 1]
            /\ Messages' = [Messages EXCEPT ![(msg[self].from)] =               Append(Messages[(msg[self].from)],
                                                                  [type |-> "ACCORD", ts |-> (clocks'[self]), from |-> self, to |-> (msg[self].from)])]
            /\ accordEnvoye' = [accordEnvoye EXCEPT ![self] = msg[self].from]
            /\ accordTS' = [accordTS EXCEPT ![self] = msg[self].ts]
            /\ pc' = [pc EXCEPT ![self] = "W1"]
            /\ UNCHANGED << waitQueue, nbAccords, accordRecus, accordRestitues, 
                            wantsCS, gotEchec, msg >>

S4(self) == /\ pc[self] = "S4"
            /\ clocks' = [clocks EXCEPT ![self] = clocks[self] + 1]
            /\ Messages' = [Messages EXCEPT ![(accordEnvoye[self])] =               Append(Messages[(accordEnvoye[self])],
                                                                      [type |-> "SONDAGE", ts |-> (clocks'[self]), from |-> self, to |-> (accordEnvoye[self])])]
            /\ waitQueue' = [waitQueue EXCEPT ![self] = Append(waitQueue[self], [from |-> msg[self].from, ts |-> msg[self].ts])]
            /\ pc' = [pc EXCEPT ![self] = "W1"]
            /\ UNCHANGED << accordEnvoye, accordTS, nbAccords, accordRecus, 
                            accordRestitues, wantsCS, gotEchec, msg >>

S3(self) == /\ pc[self] = "S3"
            /\ clocks' = [clocks EXCEPT ![self] = clocks[self] + 1]
            /\ Messages' = [Messages EXCEPT ![(msg[self].from)] =               Append(Messages[(msg[self].from)],
                                                                  [type |-> "ECHEC", ts |-> (clocks'[self]), from |-> self, to |-> (msg[self].from)])]
            /\ waitQueue' = [waitQueue EXCEPT ![self] = Append(waitQueue[self], [from |-> msg[self].from, ts |-> msg[self].ts])]
            /\ pc' = [pc EXCEPT ![self] = "W1"]
            /\ UNCHANGED << accordEnvoye, accordTS, nbAccords, accordRecus, 
                            accordRestitues, wantsCS, gotEchec, msg >>

S6(self) == /\ pc[self] = "S6"
            /\ clocks' = [clocks EXCEPT ![self] = clocks[self] + 1]
            /\ Messages' = [Messages EXCEPT ![(msg[self].from)] =               Append(Messages[(msg[self].from)],
                                                                  [type |-> "RESTITUTION", ts |-> (clocks'[self]), from |-> self, to |-> (msg[self].from)])]
            /\ accordRestitues' = [accordRestitues EXCEPT ![self] = accordRestitues[self] \union {msg[self].from}]
            /\ IF msg[self].from \in accordRecus[self]
                  THEN /\ accordRecus' = [accordRecus EXCEPT ![self] = accordRecus[self] \ {msg[self].from}]
                       /\ nbAccords' = [nbAccords EXCEPT ![self] = nbAccords[self] - 1]
                  ELSE /\ TRUE
                       /\ UNCHANGED << nbAccords, accordRecus >>
            /\ pc' = [pc EXCEPT ![self] = "W1"]
            /\ UNCHANGED << accordEnvoye, accordTS, waitQueue, wantsCS, 
                            gotEchec, msg >>

W(self) == /\ pc[self] = "W"
           /\ waitQueue' = [waitQueue EXCEPT ![self] = Append(waitQueue[self],
                                                              [from |-> msg[self].from, ts |-> msg[self].ts])]
           /\ pc' = [pc EXCEPT ![self] = "W1"]
           /\ UNCHANGED << Messages, clocks, accordEnvoye, accordTS, nbAccords, 
                           accordRecus, accordRestitues, wantsCS, gotEchec, 
                           msg >>

I1(self) == /\ pc[self] = "I1"
            /\ clocks' = [clocks EXCEPT ![self] = clocks[self] + 1]
            /\ Messages' = [Messages EXCEPT ![(QHead(waitQueue[self]).from)] =               Append(Messages[(QHead(waitQueue[self]).from)],
                                                                               [type |-> "ACCORD", ts |-> (clocks'[self]), from |-> self, to |-> (QHead(waitQueue[self]).from)])]
            /\ accordEnvoye' = [accordEnvoye EXCEPT ![self] = QHead(waitQueue[self]).from]
            /\ accordTS' = [accordTS EXCEPT ![self] = QHead(waitQueue[self]).ts]
            /\ waitQueue' = [waitQueue EXCEPT ![self] = QTail(waitQueue[self])]
            /\ pc' = [pc EXCEPT ![self] = "W"]
            /\ UNCHANGED << nbAccords, accordRecus, accordRestitues, wantsCS, 
                            gotEchec, msg >>

I2(self) == /\ pc[self] = "I2"
            /\ clocks' = [clocks EXCEPT ![self] = clocks[self] + 1]
            /\ Messages' = [Messages EXCEPT ![(QHead(waitQueue[self]).from)] =               Append(Messages[(QHead(waitQueue[self]).from)],
                                                                               [type |-> "ACCORD", ts |-> (clocks'[self]), from |-> self, to |-> (QHead(waitQueue[self]).from)])]
            /\ accordEnvoye' = [accordEnvoye EXCEPT ![self] = QHead(waitQueue[self]).from]
            /\ accordTS' = [accordTS EXCEPT ![self] = QHead(waitQueue[self]).ts]
            /\ waitQueue' = [waitQueue EXCEPT ![self] = QTail(waitQueue[self])]
            /\ pc' = [pc EXCEPT ![self] = "W1"]
            /\ UNCHANGED << nbAccords, accordRecus, accordRestitues, wantsCS, 
                            gotEchec, msg >>

W1(self) == /\ pc[self] = "W1"
            /\ pc' = [pc EXCEPT ![self] = "Wait"]
            /\ UNCHANGED << Messages, clocks, accordEnvoye, accordTS, 
                            waitQueue, nbAccords, accordRecus, accordRestitues, 
                            wantsCS, gotEchec, msg >>

CS(self) == /\ pc[self] = "CS"
            /\ clocks' = [clocks EXCEPT ![self] = clocks[self] + 1]
            /\ pc' = [pc EXCEPT ![self] = "Release"]
            /\ UNCHANGED << Messages, accordEnvoye, accordTS, waitQueue, 
                            nbAccords, accordRecus, accordRestitues, wantsCS, 
                            gotEchec, msg >>

Release(self) == /\ pc[self] = "Release"
                 /\ wantsCS' = [wantsCS EXCEPT ![self] = FALSE]
                 /\ nbAccords' = [nbAccords EXCEPT ![self] = 0]
                 /\ accordEnvoye' = [accordEnvoye EXCEPT ![self] = 0]
                 /\ accordRecus' = [accordRecus EXCEPT ![self] = {}]
                 /\ accordRestitues' = [accordRestitues EXCEPT ![self] = {}]
                 /\ accordTS' = [accordTS EXCEPT ![self] = -1]
                 /\ waitQueue' = [waitQueue EXCEPT ![self] = <<>>]
                 /\ gotEchec' = [gotEchec EXCEPT ![self] = FALSE]
                 /\ clocks' = [clocks EXCEPT ![self] = clocks[self] + 1]
                 /\ Messages' =           [Messages EXCEPT
                                ![Left(self)]  = Append(@, [type |-> "LIBERATION", ts |-> clocks'[self], from |-> self, to |-> Left(self)]),
                                ![Right(self)] = Append(@, [type |-> "LIBERATION", ts |-> clocks'[self], from |-> self, to |-> Right(self)])]
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ msg' = msg

p(self) == Request(self) \/ Wait(self) \/ II(self) \/ S5(self) \/ S4(self)
              \/ S3(self) \/ S6(self) \/ W(self) \/ I1(self) \/ I2(self)
              \/ W1(self) \/ CS(self) \/ Release(self)

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
    /\ Messages \in [ProcSet1 -> Seq([type  : {"DEMANDE","ACCORD","ECHEC",
                                                "SONDAGE","RESTITUTION","LIBERATION"},
                                       ts   : Nat,
                                       from : ProcSet1,
                                       to   : ProcSet1])]
    /\ clocks        \in [ProcSet1 -> Nat]
    /\ accordEnvoye  \in [ProcSet1 -> 0..N]
    /\ accordTS      \in [ProcSet1 -> {-1} \union Nat]
    /\ waitQueue     \in [ProcSet1 -> Seq([from : ProcSet1, ts : Nat])]
    /\ nbAccords     \in [ProcSet1 -> 0..NbVoisins]
    /\ accordRecus   \in [ProcSet1 -> SUBSET ProcSet1]
    /\ accordRestitues \in [ProcSet1 -> SUBSET ProcSet1]
    /\ wantsCS       \in [ProcSet1 -> BOOLEAN]
    /\ gotEchec      \in [ProcSet1 -> BOOLEAN]

  \* Invariant : chaque message est envoye a un voisin de son emetteur
  VoisinsOk ==
    \A dest \in ProcSet1 :
      \A idx \in 1..Len(Messages[dest]) :
        Messages[dest][idx].to \in Voisins(Messages[dest][idx].from)

  \* Invariant : deux messages du meme emetteur vers le meme destinataire ont des timestamps distincts.
  TimestampDistinct ==
    \A dest \in ProcSet1 :
      \A i, j \in 1..Len(Messages[dest]) :
        (i # j
         /\ Messages[dest][i].from = Messages[dest][j].from
         /\ Messages[dest][i].to   = Messages[dest][j].to)
        => Messages[dest][i].ts # Messages[dest][j].ts
   
   \* processus i est en section critique
  CS1(i) == pc[i] = "CS"

  \* Exclusion mutuelle : deux processus distincts ne peuvent pas etre simultanement en SC.
  Mutex == \A i, j \in ProcSet1 : (i # j) => ~(CS1(i) /\ CS1(j))

  
  \* Vivacite : tout processus qui demande la SC finit par y entrer.
  LivenessCS ==
    \A i \in ProcSet1 : wantsCS[i] ~> CS1(i)

=============================================================================
