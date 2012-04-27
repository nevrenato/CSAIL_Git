open Objects

sig RootCommit extends Commit {}


sig Commit extends Object {
	points : one Tree,
	parent : Commit set -> State
}

sig Branch{
	marks: Commit one -> State,
	branches: set State,
	head: set State
}

fact {
	all s:State{
		// A commit cannot be an ancestor of itself
		no ^(parent.s) & iden

		// RootCommits doesn't have a parent
		no RootCommit.parent.s

		// All commits (except RootCommit) need to have at least one parent
		all c : ((Commit - RootCommit) & objects.s) | some c.parent.s

		//if there is at least one commit, there is one head
		no (Commit & objects.s) or one head.s

		//referential integrity
		parent.s in objects.s -> objects.s
		marks.s in branches.s -> objects.s
		
	}
}
run{
} for 4 but exactly 1 State
