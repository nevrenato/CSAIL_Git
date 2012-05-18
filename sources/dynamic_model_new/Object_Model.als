open Objects

sig Commit extends Object {
	points : one Tree,
	parent : set Commit
}

sig RootCommit extends Commit {}

sig Branch{
	marks: Commit -> State,
	branches: set State,
	head: set State
}

lone sig master extends Branch{}

fact {
	//no cycles
	no ^parent & iden //check3

	all s:State{
		all c:objects.s & Commit{
			c.points in objects.s//check4
			c.parent in objects.s//check5
			c not in RootCommit => some c.parent
			//facts about the abs goes here
		}
		// RootCommits doesn't have a parent
		no RootCommit.parent

		//there is one commit iff there is at least one branch and an head
		some Commit & objects.s <=> some marks.s && one head.s
		head.s in branches.s

		marks.s in branches.s -> one objects.s
	}
}
run{
#Commit = 1
} for 3 but exactly 1 State
