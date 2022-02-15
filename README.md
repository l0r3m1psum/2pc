The modelled protocol is the two phase commit protocol described in
```
@book {
    ccontrol,
    title     = "Concurrency Control and Recovery in Database Systems",
    author    = "Philip A. Berstein, Vassos Hadzilacos, Nathan Goodman",
    publisher = "Addison-Wesley",
    editor    = "Michael A. Harrison",
    year      = "1987",
    month     = "January",
    chapter   = "7",
    pages     = "232",
    url       = "https://www.microsoft.com/en-us/research/people/philbe/book/",
}
```

Description of the protocol in pseudo-code
```
2 Phase Commit Protocol
 Coordinator's algorithm
  send VOTE-REQ to all participants;
  write start-2PC record in DT log;
  wait for vote messages(YES or NO) from all participants
      on timeout begin
          let Py be the processes from which YES was received;
          write abort record in DT log;
          send ABORT to all processes in Py;
          return
      end;
  if all votes were YES and coordinator votes Yes then begin
      write commit record in DT log;
      send COMMIT to all participants
  end
  else begin
      let Py be the processes from which YES was received;
      write abort record in DT Iog;
      send ABORT to all processes in Py
  end;
  return

 Participant's algorithm
  wait for VOTE-REQ from coordinator
      on timeout begin
          write abort record in DT log;
          return
      end;
  if participant votes Yes then begin
      write a yes record in DT log;
      send YES to coordinator;
      wait for decision message(COMMIT or ABORT) from coordinator
          on timeout initiate termination protocol
      if decision messageis COMMIT then write commit record in DT log
      else write abort record in DT log
  end
  else (* participant's vote is No *) begin
      write abort record in DT log;
      send NO to coordinator
  end;
  return

Cooperative Termination Protocol
 Initiator's algorithm
  start: send DECISION-REQ to all processes;
  wait for decision messagefrom any process
      on timeout goto start; (* blocked! *)
  if decision messageis COMMMIT then
      write commit record in DT log
  else (* decision messageis ABORT *)
      write abort record in DT log;
  return

 Responder's algorithm
  wait for DECISION-REQ from any process p;
  if responder has not voted Yes or has decided to Abort (i.e., has an
      abort record in DT log) then send ABORT to p
  else if responder has decided to Commit (i.e., has a commit
      record in DT log) then send COMMIT to p
  else (* responder is in its uncertainty period *) skip;
  return
```

Conditions for beeing an Atomic Commit protocol
  * AC1: All processes that reach a decision reach the same one.
  * AC2: A process cannot reverse its decision after it has reached one.
  * AC3: The Commit decision can only be reached if all processes voted Yes.
  * AC4: If there are no failures and all processes voted Yes, then the decision
    will be to Commit.
  * AC5: Consider any execution containing only failures that the algorithm is
    designed to tolerate. At any point in this execution, if all existing
    failures are repaired and no new failures occur for sufficiently long, then
    all processes will eventually reach a decision.

# Experience report
In Promela you have to program much more to expose the properties that you want
to verify because the specification language is less powerfull (i.e. only LTL
possibly without the next operator). Instead in NuSMV the opposite is true, the
input language is very weak but it has a great capacity in expressing
specifications.

Often you discover bugs either in the model or in the specifics (if they are too
tight).

A faulty channel could have been implemented by a module or a process which
randomly <q>drops</q> some packets. So that the sender needs only to send the
messages and not simulate the *not* sending of the message. Also a special
message such as `lost` can be delivered.

`assert` statement in Promela where really usefull to put sanity check in the
code. Also `printf` fas really insightfull, NuSMV on the other hand has the
possibility to run interactie simulations which allows you to guide the
simulation exactly as you want/need.

## What could have been done better
After reading <q>Principles of Model Checking</q>, by Christel Baier and
Joost-Pieter Katoen, I understood many more things, in particular I could have
ruled out bad executions of the termination protocol via fairness constrains.
