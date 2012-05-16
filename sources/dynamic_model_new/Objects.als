open Name
open State 

abstract sig Object {
	objects: set State
}

sig Blob extends Object {}

sig Tree extends Object {
		contains : Name  -> one (Tree+Blob)
}

fun contents: Tree -> Object -> Name{
	{t:Tree, o:Object, n:Name | t -> n-> o in contains}
}

fact {

		//trees with the same content shall be the same
		no disj t,t':Tree | t.contains = t'.contains //check1

		// there shall be no cycles
		no ^(contents.Name) & iden //check2

		// all trees must have at least one son (git restriction)
		all t : Tree | some t.(contents.Name)

		// at most one parent
		all t : Tree | lone contains.t

		//NEW FACT
		//if a tree is on a certain state the all the descendants are on that state
		all s:State, t:objects.s & Tree | t.contents.Name in objects.s //check6
}

run {
	some t:Tree | #t.*(contents.Name) > 2 && some t.(contents.Name) & Tree
} for 3 but exactly 1 State
