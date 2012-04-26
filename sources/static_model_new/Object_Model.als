open Objects

sig RootCommit extends Commit {}


sig Commit extends Object {
	points : Tree,
	parent : set Commit,
}

sig Branch{
	marks: Commit
}

sig Head{
	on: Branch
}

fact {
	// A commit cannot be an ancestor of itself
	no ^parent & iden

	// RootCommits don't have a parent
	no RootCommit.parent

	// All commits (except RootCommit) need to have at least one parent
	all c : Commit - RootCommit | some c.parent

	//if there is at least one commit then there is a Head
	some Head or no Commit
	//at most one head
	lone Head
}

run{
	some Head
	no Commit
} for 3
