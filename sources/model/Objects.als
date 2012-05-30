open Name
open util/ordering[State]
sig State {}


abstract sig Object {
	objects: set State
}

sig Blob extends Object {}

sig Tree extends Object {
		contains : Name  -> lone (Tree+Blob)
}

fun contents: Tree -> Object -> Name{
	{t:Tree, o:Object, n:Name | t -> n-> o in contains}
}

fact {
		//trees with the same content shall be the same
		all t,t' : Tree | t.contains = t'.contains implies t=t'
		// there shall be no cycles
		no ^(contents.Name) & iden 
		// all trees must have at least one son (git restriction)
		all s:State, t : objects.s & Tree | some t.contains
}

run {
	some contains
} for 3 but exactly 1 State
