open operations

--------------------------------------INVARIANT PRESERVATION----------------------------------
-- Invariant preservation. If before a commit the invariant holds
-- then after the commmit the invariant must continue to hold
assert commitInvariantPreservation{
	all s,s':State | invariant[s] and commit[s,s'] => invariant[s']
} 
--	for 8, Valid

assert branchInvariantPreservation{
	all s,s':State, b:Branch | invariant[s] and branch[s,s',b] => invariant[s']
}

assert branchDelInvariantPreservation{
	all s,s':State, b:Branch | invariant[s] and branchRm[s,s',b] => invariant[s']
}

-- Invariant preservation. If before a checkout the invariant holds
-- then after the checkout the invariant must continue to hold
assert checkoutInvariantPreservation{
	all s,s':State, b:Branch | invariant[s] and checkout[s,s',b] => invariant[s']
}
--	for 8, Valid

assert addInvariantPreservation{
	all s,s':State, f:File | invariant[s] and add[s,s',f] => invariant[s']
}

assert rmInvariantPreservation{
	all s,s':State, f:File | invariant[s] and rm[s,s',f] => invariant[s']
}

-- Invariant preservation. If before a merge the invariant holds
-- then after the merge the invariant must continue to hold
assert mergeInvariantPreservation {
	all s,s' : State, b : Branch | invariant[s] and merge[s,s',b] => invariant[s']
} 
-----------------------------------------------------------------------------------------------
-------------------------------------Idempotence-----------------------------------------------
-- Commit, idempotence.
-- Doing a commit after another should add no modifications 
assert commitIdempotence {
	all s0,s1,s2 : State | (commit[s0,s1] and commit[s1,s2]) implies (head.s1).(marks.s1).points = (head.s2).(marks.s2).points
}
--	for 6, Valid

-- Add, idempotence
-- Add a file, after adding the same, brings no new modification
assert addIdempotence{
	all s0,s1,s2 : State, f : File | add[s0,s1,f] and add[s1,s2,f] implies index.s1 = index.s2
} 
--	for 7, Valid

--Checkout, idempotence
--Checking out twice is the same as checking out once
assert checkoutIdempotence{
	all s0,s1,s2:State, b:Branch | checkout[s0,s1,b] and checkout[s1,s2,b] => index.s1 = index.s2 
																										and marks.s1 = marks.s2 
																										and branches.s1 = branches.s2
																										and objects.s1 = objects.s2
}

-----------------------------------------------------------------------------------------------
-------------------------------commit operation-------------------------------------------------
--Commit, no tree without sons
--All trees in one commit must have at least one son
assert noEmptyTrees {
	all s0,s1 : State | commit[s0,s1] 
			implies all t : Tree & Path.((head.s1).(marks.s1).abs) | some t.contains
}
--	for 6, Valid

-- Commit, no orphan blobs
-- All blobs on a commit must have at least one parent
assert blobHasParent {
	all s0,s1 : State | commit[s0,s1] implies all b : Blob & Path.((head.s1).(marks.s1).abs)| some (contents.Name).b
} 
--	for 6, Valid

-- Commit, different contents
-- If two commits have the same content they cannot
-- point to the same root tree
assert differentContentDifferentCommit{
	all s0,s1,s2,s3 : State, f :File | commit[s0,s1] 
												and add[s1,s2,f] 
												and f.path not in (head.s1).(marks.s1).abs.univ 
												and commit[s2,s3] 
		implies (head.s1).(marks.s1).points != (head.s3).(marks.s3).points
} 
--	for 6, Valid


-- Commit, inverse operation
-- Removing a file and commiting is the inverse of adding the same file
-- and commiting
assert commitAddCommitRmCommit{
	all s0,s1,s2,s3,s4,s5:State, f:File | invariant[s0] 
											and commit[s0,s1] 
											and add[s1,s2,f] and f.path not in (index.s1).path 
											and commit[s2,s3] 
											and rm[s3,s4,f] 
											and commit[s4,s5]
					implies ((head.s1).(marks.s1).points = (head.s5).(marks.s5).points)
}
--	for 6, Valid
-----------------------------------------------------------------------------------------------
-------------------------------------add and rm operations---------------------------------------
-- Add and Remove, inverse operation
-- Adding a file and then removing it, brings to a state that is equal 
-- to the state right before the addition
assert addRm{
	all s0,s1,s2:State, f:File | add[s0,s1,f] 
									and f.path not in (index.s0).path 
									and rm[s1,s2,f] 
									and f not in  index.s0
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

--Making a commit after adding a file from index
--implies that the file is on the next commit
assert addCommit{
	all s0,s1,s2:State, f:File | add[s0,s1,f] 
									and commit[s1,s2] 
			=> f.path -> f.blob in (head.s2).(marks.s2).abs
}

--Making a commit after removing a file from index
--implies that the file is not on the next commit
assert rmCommit{
	all s0,s1,s2:State, f:File | rm[s0,s1,f] 
										and commit[s1,s2] 
			=> f.path -> f.blob not in (head.s2).(marks.s2).abs
}
-----------------------------------------------------------------------------------------------
------------------------------------branch and branchRm operation--------------------------------
-- Creating and Removing a branch, inverse operation
-- Creating a branch and then removing it, brings to a state that is equal
-- to the state right before the addition
assert branchBranchDel{
	all s0,s1,s2:State, b:Branch | branch[s0,s1,b] and branchRm[s1,s2,b]
			implies branches.s0 = branches.s2 and marks.s0 = marks.s2
}
--	for 8, Valid

--A newly created branch always points to head
assert newBranchPointsToHead{
	all s0,s1:State, b:Branch | branch[s0,s1,b] => b.marks.s1 = (head.s1).(marks.s1)
}
-----------------------------------------------------------------------------------------------
--------------------------------------checkout operation-----------------------------------------
-- The inverse operation of a checkout, is just doing checkout to the branch where
-- we were before doing the first checkout. The current commit before of the first
-- checkout should be equal to the commit after doings the first and second checkouts
assert RevertCheckout {
	all s,s',s'' : State , b : Branch |	   invariant[s] 
												and (checkout[s,s',b] 
												and checkout[s',s'',head.s]) 
		=> (head.s).(marks.s) = (head.s'').(marks.s'')
}
--	for 8, Valid

-- The inverse operation of a checkout, is just doing checkout to the branch where
-- we were before doing the first checkout. The current index before the first
-- checkout should be equal to the index after doing the first and second checkouts
assert checkoutForthAndBack {
        all s0,s1,s2,s3: State, b : Branch | commit[s0,s1] 
														and checkout[s1,s2,b] 
														and checkout[s2,s3,head.s1] 
								implies s1.pathcontents = s3.pathcontents and head.s1 = head.s3
}
--	for 7, Valid

assert checkoutNoLostFiles{
	all s0,s1:State, b:Branch | checkout[s0,s1,b] => 
										all f:index.s0 | (f.path -> f.blob in (head.s0).(marks.s0).abs
															or some f':index.s1 | f.blob = f'.blob and f.path = f'.path)
}

assert checkoutNoLostFiles'{
	all s0,s1:State, b:Branch | checkout[s0,s1,b] => 
										no f:index.s0 | f.path -> f.blob not in s1.pathcontents + (head.s0).(marks.s0).abs
}

assert CBInIndex{
	all s,s':State, b:branches.s |
		invariant[s] and checkout[s,s',b] => (b.marks.s).abs in s'.pathcontents
}

check CBInIndex for 5
-----------------------------------------------------------------------------------------------

