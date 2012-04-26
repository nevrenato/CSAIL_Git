open Objects

sig RootCommit extends Commit {}


sig Commit extends Object {
	points : Tree one -> State,
	parent : Commit set -> State
}

sig Branch{
	marks: Commit one -> State,
	branches: set State
}

sig Head{
	on: Branch one -> State
}

fact {
	all s:State{
		// A commit cannot be an ancestor of itself
		no ^(parent.s) & iden

		// RootCommits don't have a parent
		no RootCommit.parent.s

		// All commits (except RootCommit) need to have at least one parent
		all c : Commit - RootCommit | some c.parent.s



//??????????????????
		//if there is at least one commit then there is a Head
		some on.s or no (Commit & objects.s)
		//at most one head
		lone on.s
//????????????????
		//referential integrity
		parent.s in objects.s -> objects.s
		marks.s in branches.s -> objects.s
		
	}
}
run{} for 3 but exactly 1 State
