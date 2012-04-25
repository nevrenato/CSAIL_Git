open Objects

some sig RootCommit extends Commit {}


sig Commit extends Object {
	points : Tree,
	parent : set Commit
}

one sig Head extends Object {
	pointsToLast : Commit

}


fact {
	// A commit cannot be an ancestor of itself
	no ^parent & iden

	// RootCommits don't have a parent
	no RootCommit.parent

	// All commits (except RootCommit) need to have at least one parent
	all c : Commit - RootCommit | some c.parent
}

run {
	# Commit > 0

} for 5
