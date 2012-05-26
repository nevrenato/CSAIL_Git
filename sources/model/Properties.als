open operations

assert commitMentalSanity{
	all s,s':State{
		commit[s,s'] => all o:(head.s').(marks.s').points.*(contents.Name) | o in Path.((head.s').(marks.s').abs) &&  (head.s').(marks.s').abs.o in (index.s).path.*pathparent
	}
}

assert addCommitRmCommit{
	all s0,s1,s2,s3,s4:State, f:File | some head.s0 and 
												add[s0,s1,f] and
												commit[s1,s2] and
												rm[s2,s3,f] and
												commit[s3,s4]
												implies (head.s0).(marks.s0).points = (head.s4).(marks.s4).points
}
/*
	it fails with 6
	when we make add[s0,s1,f], f can exist in initial commit
*/

assert commitAddCommitRmCommit{
	all s0,s1,s2,s3,s4,s5:State, f:File |
					(commit[s0,s1] and
					add[s1,s2,f] and
					commit[s2,s3] and
					rm[s3,s4,f] and
					commit[s4,s5])
					implies (head.s1).(marks.s1).points = (head.s5).(marks.s5).points
}

check commitAddCommitRmCommit for 6
