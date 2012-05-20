
open Objects
open Path

sig Commit extends Object {
	points : one Tree,
	parent : set Commit,
	abs: Path -> Object
}

sig RootCommit extends Commit {}

sig Branch{
	marks: Commit -> State,
	branches: set State,
	head: set State
}

lone sig Master extends Branch{}

fact {
	//no cycles
	no ^parent & iden //check3

	all s:State{

		all c:objects.s & Commit{

			c.points in objects.s//check4
			c.parent in objects.s//check5

			c not in RootCommit => some c.parent

			let objs = c.points.*(contents.Name){

				c.abs in Path some -> lone objs
				(c.abs).(c.points) in Root
				all p,q: (c.abs).univ | p -> q in pathparent implies q.(c.abs) -> p.name -> p.(c.abs) in contains
				all t,o: objs, n:Name | t -> n -> o  in contains implies some x: c.abs.o, y: c.abs.t | x -> y in pathparent and x.name = n

			}
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

} for 6 but exactly 1 State
