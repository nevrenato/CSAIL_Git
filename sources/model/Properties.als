open operations

--Commit, idempotent
assert commitIdempotence {
	all s0,s1,s2 : State | (commit[s0,s1] and commit[s1,s2]) implies (head.s1).(marks.s1).points = (head.s2).(marks.s2).points
}
/*
	for 6, Valid
*/

--Commit, no trees without sons
assert noEmptyTrees {
	all s0,s1 : State | commit[s0,s1] implies all t : Tree & Path.((head.s1).(marks.s1).abs) | some t.contains
} 
/*
	for 6, Valid
*/

-- Commit, all blobs must have a parent
assert blobHasParent {
	all s0,s1 : State | commit[s0,s1] => all b : Blob & Path.((head.s1).(marks.s1).abs) | some (contents.Name).b
} 
/*
	for 6, Valid
*/

-- Commit, with different content can never be the same
assert differentContentDifferentCommit{
	all s0,s1,s2,s3 : State, f :File |
	 commit[s0,s1] and add[s1,s2,f] and commit[s2,s3] and f not in index.s1 
		implies (head.s1).(marks.s1).points != (head.s3).(marks.s3).points
} 
/*
	for 6, not Valid
	if f.path is included in commit[s0,s1]
*/

-- Add, idempotent
assert addIdempotence{
	all s0,s1,s2 : State, f : File | add[s0,s1,f] and add[s1,s2,f] implies index.s1 = index.s2
} 
/*
	for 6, Valid
*/

assert addCommitRmCommit{
	all s0,s1,s2,s3,s4:State, f:File | some head.s0 and 
												add[s0,s1,f] and
												commit[s1,s2] and
												rm[s2,s3,f] and
												commit[s3,s4] and
												f not in index.s0
												implies (head.s0).(marks.s0).points = (head.s4).(marks.s4).points
}
/*
	for 6, not Valid
	when we make add[s0,s1,f], f can already exist on the initial commit
*/

assert commitAddCommitRmCommit{
	all s0,s1,s2,s3,s4,s5:State, f:File |
					(commit[s0,s1] and
					add[s1,s2,f] and
					commit[s2,s3] and
					rm[s3,s4,f] and
					commit[s4,s5])
					implies ((head.s1).(marks.s1).points = (head.s5).(marks.s5).points or 
								 (head.s1).(marks.s1).points = (head.s4).(marks.s4).points)
}
/*
	for 6, Valid
	s1 can be the same as s2, so - we need to compara s1 with s5 for the case s1!=s2
											   - we need to compare s1 with s4 for the case s1=s2
*/

assert addRm{
	all s0,s1,s2:State, f:File | add[s0,s1,f] and rm[s1,s2,f] and f not in  index.s0
			implies index.s0 = index.s2
}
/*
	for 6, not Valid
	f can be on index.s0
*/

assert rmAdd{
	all s0,s1,s2:State, f:File | rm[s0,s1,f] and add[s1,s2,f]
			implies index.s0 = index.s2
}
/*
	for 8, Valid
*/

assert branchBranchDel{
	all s0,s1,s2:State, b:Branch | branch[s0,s1,b] and branchDel[s1,s2,b]
			implies branches.s0 = branches.s2 and marks.s0 = marks.s2
}
/*
	for 8, Valid
*/

assert commitInvariantPreservation{
	all s,s':State | invariant[s] and commit[s,s'] => invariant[s']
}
/* 
	for 8, Valid
*/

assert checkoutInvariantPreservation{
	all s,s':State, b:Branch | invariant[s] and checkout[s,s',b] => invariant[s']
}
/*
	for 8, Valid
*/

assert RevertCheckout {
	all s,s',s'' : State , b : Branch | (checkout[s,s',b] and checkout[s',s'',head.s]) => 
			(head.s).(marks.s) = (head.s'').(marks.s'')
}
/*
	for 8, Valid
*/
assert commitForthAndBack {
        all s0,s1,s2,s3: State, b : Branch | commit[s0,s1] 
													and checkout[s1,s2,b] 
													and checkout[s2,s3,head.s1] 
													implies s1.pathcontents = s3.pathcontents and head.s1 = head.s3
}

check branchBranchDel for 8
