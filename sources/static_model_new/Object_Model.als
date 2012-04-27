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

	//if there is at least one commit, there is one head
	no Commit or one head
}

run{
//	one head
//	no Commit
} for 3
