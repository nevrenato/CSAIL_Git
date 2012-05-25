open Objects

sig RootCommit extends Commit {}


sig Commit extends Object {
	points : Tree,
	parent : set Commit,
}

sig Branch{
	marks: Commit,
	head: Branch
}

fact {
	// A commit cannot be an ancestor of itself
	no ^parent & iden

	// RootCommits don't have a parent
	no RootCommit.parent

	// All commits (except RootCommit) need to have at least one parent
	all c : Commit - RootCommit | some c.parent

	//if there is one commit, there is at least one branch and an head
	some Commit <=> one head
}

run{
	some Commit
} for 3
