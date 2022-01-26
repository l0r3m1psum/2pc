/* This is a model of the two phase commit protocol described in
 * @book {
 *     ccontrol,
 *     title = "Concurrency Control and Recovery in Database Systems",
 *     author = "Philip A. Berstein, Vassos Hadzilacos, Nathan Goodman",
 *     publisher = "Addison-Wesley",
 *     editor = "Michael A. Harrison",
 *     year = "1987",
 *     month = "January",
 *     pages = "232",
 *     url = "https://www.microsoft.com/en-us/research/people/philbe/book/",
 * }
 *
 * 2 Phase Commit Protocol
 *  Coordinator's algorithm
 *   send VOTE-REQ to all participants;
 *   write start-2PC record in DT log;
 *   wait for vote messages(YES or NO) from all participants
 *       on timeout begin
 *           let Py be the processes from which YES was received;
 *           write abort record in DT log;
 *           send ABORT to all processes in Py;
 *           return
 *       end;
 *   if all votes were YES and coordinator votes Yes then begin
 *       write commit record in DT log;
 *       send COMMIT to all participants
 *   end
 *   else begin
 *       let Py be the processes from which YES was received;
 *       write abort record in DT Iog;
 *       send ABORT to all processes in Py
 *   end;
 *   return
 *
 *  Participant's algorithm
 *   wait for VOTE-REQ from coordinator
 *       on timeout begin
 *           write abort record in DT log;
 *           return
 *       end;
 *   if participant votes Yes then begin
 *       write a yes record in DT log;
 *       send YES to coordinator;
 *       wait for decision message(COMMIT or ABORT) from coordinator
 *           on timeout initiate termination protocol
 *       if decision messageis COMMIT then write commit record in DT log
 *       else write abort record in DT log
 *   end
 *   else (* participant's vote is No *) begin
 *       write abort record in DT log;
 *       send NO to coordinator
 *   end;
 *   return
 *
 * Cooperative Termination Protocol
 *  Initiator's algorithm
 *   start: send DECISION-REQ to all processes;
 *   wait for decision messagefrom any process
 *       on timeout goto start; (* blocked! *)
 *   if decision messageis COMMMIT then
 *       write commit record in DT log
 *   else (* decision messageis ABORT *)
 *       write abort record in DT log;
 *   return
 *
 *  Responder's algorithm
 *   wait for DECISION-REQ from any process p;
 *   if responder has not voted Yes or has decided to Abort (i.e., has an
 *       abort record in DT log) then send ABORT to p
 *   else if responder has decided to Commit (i.e., has a commit
 *       record in DT log) then send COMMIT to p
 *   else (* responder is in its uncertainty period *) skip;
 *   return
 *
 * Conditions for beeing an Atomic Commit protocol
 * AC1: All processes that reach a decision reach the same one.
 * AC2: A process cannot reverse its decision after it has reached one.
 * AC3: The Commit decision can only be reached if all processes voted Yes.
 * AC4: If there are no failures and all processes voted Yes, then the decision
 * will be to Commit.
 * AC5: Consider any execution containing only failures that the algorithm is
 * designed to tolerate. At any point in this execution, if all existing
 * failures are repaired and no new failures occur for sufficiently long, then
 * all processes will eventually reach a decision.
 */

/* NOTE: The cooperative termination is implementent in a simplified way because
 * the actual implementation is too complex and doesn't guarantee termination.
 * In this case only the coodinator is the only process to which help is asked.
 */

/* compile and run: spin -a 2pc.pml && cc -O2 -DNXT -o pan pan.c && pan -a -N AC1
 * debug: pan -r 2pc.pml.trail
 * clean: rm _spin_nvr.tmp pan*
 * documentation: https://spinroot.com/spin/Man/
 */

/******************************************************************************/

/* Number of partecipant in the algorithm */
#ifndef N
	#define N 1
#endif

/* Content of the messages */
#define YES 1
#define NO 0
#define COMMIT 1
#define ABORT 0
#define DONT_CARE 0

/* Utilities to keep track of values over time used for AC2 */
#define REMEMBER(X) byte old_ ## X = 0; byte X = 0;
#define INC(X) d_step {old_ ## X = X; X++}
#define IS_INC(X) (old_ ## X <= X)

mtype = {VOTE_REQ, VOTE, DECISION_REQ, DECISION};
chan channel[N] = [1] of {mtype, bit};
chan help = [0] of {mtype, bit};

/* This counters are used to keep track of what the partecipants do, not the
 * coordinator.
 */
REMEMBER(decidedToAbort)
REMEMBER(decidedToCommit)
byte votedYes = 0;
byte votedNo = 0;

active [N] proctype partecipant() {
	if
	:: channel[_pid]?VOTE_REQ(_)
	:: timeout ->
		INC(decidedToAbort);
		printf("partecipant %d aborted prematurely\n", _pid);
		goto end
	fi;
	if
	:: atomic {channel[_pid]!VOTE(YES); votedYes++} ->
		printf("partecipant %d voted YES\n", _pid)
	:: atomic {channel[_pid]!VOTE(NO); votedNo++} ->
		printf("partecipant %d voted NO\n", _pid)
	:: skip ->
		/*probabilmente qua comunque devono votare*/
		printf("partecipant %d timed out\n", _pid)
	fi;
	if
	:: channel[_pid]?DECISION(COMMIT) ->
		assert(votedYes == N);
		INC(decidedToCommit);
		printf("partecipant %d committed\n", _pid)
	:: channel[_pid]?DECISION(ABORT) ->
		INC(decidedToAbort);
		printf("partecipant %d aborted\n", _pid)
	:: timeout -> /* cooperative termination */
/* askAgain: */
		printf("partecipant %d is asking for help\n", _pid);
		help!DECISION_REQ(DONT_CARE);
		if
		:: help?DECISION(COMMIT) -> INC(decidedToCommit);
		:: help?DECISION(ABORT) -> INC(decidedToAbort)
		/*:: timeout -> printf("partecipant %d is asking again\n", _pid); goto askAgain
		removed because could cause an infinite loop */
		fi
	fi
end:
}

active proctype coordinator() {
	int i;
	bit decision;
	for (i : 0 .. N-1) {
		if
		:: channel[i]!VOTE_REQ(DONT_CARE)
		:: skip;
		fi
	};
	for (i : 0 .. N-1) {
		if
		:: channel[i]?VOTE(YES) -> skip
		:: channel[i]?VOTE(NO) -> goto abort
		:: timeout -> goto abort
		fi
	};
	assert(votedYes == N);
	for (i : 0 .. N-1) {
		if
		:: channel[i]!DECISION(COMMIT)
		:: skip /* will triggers cooperative termination */
		fi
	};
	decision = COMMIT;
	printf("coordinator committed\n");
	if
	:: 0 ->
abort:
		for (i : 0 .. N-1) {
			if
			:: channel[i]!DECISION(ABORT)
			:: skip /* will triggers cooperative termination */
			fi
		};
		decision = ABORT;
		printf("coordinator aborted\n")
	fi;
end:
	do
	:: nempty(help) ->
		help?DECISION_REQ(DONT_CARE);
		help!DECISION(decision)
	od;
}

/* Which properties are for safety and which ones are for liveness? */

ltl AC1 {
	[]((decidedToCommit > 0 -> decidedToAbort == 0)
		|| (decidedToAbort > 0 -> decidedToCommit == 0))
}

/* NOTE: X requires -DNXT
 * https://www.buzzphp.com/posts/referencing-previous-state-in-promela-ltl-statement
 */
ltl AC2 {
	[]((IS_INC(decidedToCommit) -> (X IS_INC(decidedToCommit)))
		&& (IS_INC(decidedToAbort) -> (X IS_INC(decidedToAbort))))
}

ltl AC3 {
	/* (`>' is used because it says that a decision _can_ be reached) */
	[](decidedToCommit > 0 -> votedYes == N)
}

ltl AC4 {
	/* (`<>' is used because it says that the decision _will_ be to Commit) */
	[](votedYes == N -> <>(decidedToCommit == N))
}

ltl AC5 {
	<>[](decidedToCommit == N || decidedToAbort == N)
}

ltl sanity_check {
	[](decidedToCommit <= N && decidedToAbort <= N
		&& votedYes <= N && votedNo <= N)
}
