open Path
open Object_Model


pred commit[s,s':State]{

	some index.s
	index.s' = index.s
	
	no head.s =>{

		head.s' = Master
		branches.s' = Master
		(head.s').(marks.s') in RootCommit

	}else{
	
		head.s' = head.s
		branches.s' = branches.s
		marks.s' - (head.s -> Commit) = marks.s - (head.s -> Commit) //think better about this
		(head.s').(marks.s') != (head.s).(marks.s)
	
	}

	(index.s).path.*pathparent = (head.s').(marks.s').(abs.univ)
	all f:index.s | f.path -> f.blob in (head.s').(marks.s').abs
	objects.s' = objects.s + (head.s').(marks.s') + univ.((head.s').(marks.s').abs) 
}



pred add[s,s':State, f:File]{
	head.s' = head.s
	branches.s' = branches.s
	marks.s' = marks.s
	objects.s' = objects.s
	index.s' = index.s + f - ((f.path).~path -f)
}



pred rm[s,s':State,f:File]{
	//pre conditions
		//file on index
		f in index.s
		//the content of the file is the same as in the last commit
		f.path -> f.blob in (head.s).(marks.s).abs


	head.s' = head.s
	branches.s' = branches.s
	marks.s' = marks.s
	objects.s' = objects.s
	index.s' = index.s - f
}



pred branch[s,s':State,b:Branch]{
	//pre condition
		b not in branches.s

	head.s' = head.s
	branches.s' = branches.s + b
	marks.s' = marks.s + b -> (head.s).(marks.s)
	objects.s' = objects.s
	index.s' = index.s
}



pred branchDel[s,s':State, b:Branch]{
	
	//pre condition
		//the branch exists
		b in branches.s
		//the branch is not pointed by Head
		b not in (head.s)
		//the branch is already merged with the head
		b.marks.s in (head.s).(marks.s).^parent
	
	head.s' = head.s
	branches.s' = branches.s - b
	marks.s' = marks.s - b -> Commit
	objects.s' = objects.s
	index.s' = index.s 
}

fun comFls[b : Branch, s : State ] : set File {

	path.(b.(marks.s).(abs.univ))

}


pred checkout[s,s':State,b:Branch]{

	// usefull instances
	(head.s) != b

	//pre condition
		//the branch is on s

	b in branches.s

	b.(marks.s) != (head.s).(marks.s) => 
	no (index.s - comFls[(head.s),s]).path & comFls[b,s].path

	// pos condition 
	index.s' = index.s - comFls[(head.s),s] + comFls[b,s]

	head.s' = b
	branches.s' = branches.s
	marks.s' = marks.s
	objects.s' = objects.s

}

pred merge[s,s' : State, b,b' : Branch] {
	
	// first common ancestor encountered for what ?



	// choose one of the files conflicting 
}
/*
run{
//	some s,s':State | s!=s' && commit[s,s'] && some index.s
	//some pathparent.pathparent 
	//some s,s':State, f:File | s!=s' && rm[s,s',f]
/*	some disj s1,s2,s3,s4,s5,s6,s7:State, disj b1:Branch, disj f1,f2:File {
		add[s1,s2,f1]
		commit[s2,s3]
		branch[s3,s4,b1] && b1 != Master
		checkout[s4,s5,b1]
		add[s5,s6,f2]
		commit[s6,s7]
	}
*/
//	some s,s':State, b:Branch | branchDel[s,s',b]
//	some c:Commit | #parent.c > 1
//	some s:State, disj b1,b2:branches.s | no b1.marks & b2.marks
//	some parent

	some s,s':State, b:Branch | checkout[s,s',b]
} for 3 but 2 State
*/
run {
/*	some disj s,s',s'',s''' : State, b : Branch, f : File | 
		commit[s,s'] and  add[s',s'',f] and f not in comFls[head.s',s'] and checkout[s'',s''',b]
*/
	some disj s,s': State, f : File | commit[s,s'] and f.path not in (index.(s'+s)).path

} for 6 but 2 State


