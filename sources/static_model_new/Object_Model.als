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

	//if there is one commit, there is at least one branch
	some Commit <=> some Branch
	//if there is at least one Branch, there is one head
	no Branch or one head
}

run{
} for 3
