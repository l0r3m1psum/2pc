/* NOTE: The cooperative termination was not implementd because I'm not able to.
 */

/* compile and run: spin -a 2pc.pml && cc -O2 -DNXT -o pan pan.c && pan -a -N AC1
 * debug: pan -r 2pc.pml.trail
 * clean: rm _spin_nvr.tmp pan* *.trail
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

mtype = {VOTE_REQ, VOTE, DECISION};
chan channel[N] = [1] of {mtype, bit};

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
	fi;
	if
	:: channel[_pid]?DECISION(COMMIT) ->
		assert(votedYes == N);
		INC(decidedToCommit);
		printf("partecipant %d committed\n", _pid)
	:: channel[_pid]?DECISION(ABORT) ->
		assert(votedYes < N);
		INC(decidedToAbort);
		printf("partecipant %d aborted\n", _pid)
	fi
end:
}

active proctype coordinator() {
	int i;
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
		fi
	};
	assert(votedYes == N);
	for (i : 0 .. N-1) {
		channel[i]!DECISION(COMMIT)
	};
	printf("coordinator committed\n");
	if
	:: 0 ->
abort:
		assert(votedYes < N);
		for (i : 0 .. N-1) {
			channel[i]!DECISION(ABORT)
		};
		printf("coordinator aborted\n")
	fi;
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
