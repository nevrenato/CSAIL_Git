open operations

-- Commit, idempotence.
-- Doing a commit after another should add no modifications 
assert commitIdempotence {
	all s0,s1,s2 : State | (commit[s0,s1] and commit[s1,s2]) implies (head.s1).(marks.s1).points = (head.s2).(marks.s2).points
}
--	for 6, Valid


-- Commit, no tree without sons.
-- All trees in one commit must have at least one son
assert noEmptyTrees {
	all s0,s1 : State | commit[s0,s1] implies all t : Tree & Path.((head.s1).(marks.s1).abs) | some t.contains
} 
--	for 6, Valid


-- Commit, no orphan blobs
-- All blobs on a commit must have at least one parent
assert blobHasParent {
	all s0,s1 : State | commit[s0,s1] => all b : Blob & Path.((head.s1).(marks.s1).abs) | some (contents.Name).b
} 
--	for 6, Valid

-- Commit, different contents
-- If two commits have the same content they cannot
-- point to the same root tree
assert differentContentDifferentCommit{
	all s0,s1,s2,s3 : State, f :File |
	 commit[s0,s1] and add[s1,s2,f] and f.path not in (head.s1).(marks.s1).abs.univ and commit[s2,s3] 
		implies (head.s1).(marks.s1).points != (head.s3).(marks.s3).points
} 
--	for 6, Valid


-- Add, idempotence
-- Add a file, after adding the same, brings no new modification
assert addIdempotence{
	all s0,s1,s2 : State, f : File | add[s0,s1,f] and add[s1,s2,f] implies index.s1 = index.s2
} 
--	for 7, Valid

-- This maybe should be removed, because a similar assertion is below
assert addCommitRmCommit{
	all s0,s1,s2,s3,s4:State, f:File | some head.s0 and f.path not in (head.s0).(marks.s0).abs.univ and
							add[s0,s1,f] and
							commit[s1,s2] and
							rm[s2,s3,f] and
							commit[s3,s4] and
							f not in index.s0
						        implies (head.s0).(marks.s0).points = (head.s4).(marks.s4).points
}
--	for 6, Valid



-- Commit, inverse operation
-- Removing a file and commiting is the inverse of adding the same file
-- and commiting
assert commitAddCommitRmCommit{
	all s0,s1,s2,s3,s4,s5:State, f:File |
					(commit[s0,s1] and
					add[s1,s2,f] and f.path not in (index.s1).path and
					commit[s2,s3] and
					rm[s3,s4,f] and
					commit[s4,s5])
					implies ((head.s1).(marks.s1).points = (head.s5).(marks.s5).points)
}
--	for 6, Valid


-- Add and Remove, inverse operation
-- Adding a file and then removing it, brings to a state that is equal 
-- to the state right before the addition
assert addRm{
	all s0,s1,s2:State, f:File | add[s0,s1,f] and f.path not in (index.s0).path and rm[s1,s2,f] and f not in  index.s0
			implies index.s0 = index.s2
}
--	for 8, Valid


-- Remove and Add, inverse operation
-- Removing a file and then adding it, brings to a state that is equal 
-- to the state right before the addition
assert rmAdd{
	all s0,s1,s2:State, f:File | rm[s0,s1,f] and add[s1,s2,f]
			implies index.s0 = index.s2
}
--	for 8, Valid


-- Creating and Removing a branch, inverse operation
-- Creating a branch and then removing it, brings to a state that is equal
-- to the state right before the addition
assert branchBranchDel{
	all s0,s1,s2:State, b:Branch | branch[s0,s1,b] and branchDel[s1,s2,b]
			implies branches.s0 = branches.s2 and marks.s0 = marks.s2
}
--	for 8, Valid


-- Invariant preservation. If before a commit the invariant holds
-- then after the commmit the invariant must continue to hold
assert commitInvariantPreservation{
	all s,s':State | invariant[s] and commit[s,s'] => invariant[s']
} 
--	for 8, Valid


-- Invariant preservation. If before a checkout the invariant holds
-- then after the checkout the invariant must continue to hold
assert checkoutInvariantPreservation{
	all s,s':State, b:Branch | invariant[s] and checkout[s,s',b] => invariant[s']
}
--	for 8, Valid


-- The inverse operation of a checkout, is just doing checkout to the branch where
-- we were before doing the first checkout. The current commit before of the first
-- checkout should be equal to the commit after doings the first and second checkouts
assert RevertCheckout {
	all s,s',s'' : State , b : Branch | (checkout[s,s',b] and checkout[s',s'',head.s]) => 
			(head.s).(marks.s) = (head.s'').(marks.s'')
}
--	for 8, Valid


-- The inverse operation of a checkout, is just doing checkout to the branch where
-- we were before doing the first checkout. The current index before the first
-- checkout should be equal to the index after doing the first and second checkouts
assert checkoutForthAndBack {
        all s0,s1,s2,s3: State, b : Branch | commit[s0,s1] and checkout[s1,s2,b] and checkout[s2,s3,head.s1] 
								implies s1.pathcontents = s3.pathcontents and head.s1 = head.s3
}
--	for 7, Valid


-- Invariant preservation. If before a merge the invariant holds
-- then after the merge the invariant must continue to hold
assert mergeInvariantPreservation {
	all s,s' : State, b : Branch | invariant[s] and merge[s,s',b] => invariant[s']
} 


check mergeInvariantPreservation for 10 but 2 State
