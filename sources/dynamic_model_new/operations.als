	open Path
open Object_Model

pred add[s,s' : State,  p: Path ] {
		s != s'
	//pre-condition
		//path has to be a leaf
		no pathparent.p
	
	//post-condition
		//a path is added to the set of objects
		objects.s' = objects.s + p.blob
		//a path is added to index
		index.s' = index.s + p

		//all others relations are kept

		parent.s' = parent.s
		marks.s' = marks.s
		branches.s' = branches.s
		head.s' = head.s
}

pred rm[s,s' : State, p:Path] {
	
	s != s'
	//pre-condition
	p in index.s

	let r = { t : Tree, o : (Tree+Blob) | some n : Name | t->n->o in contains},
			root = (((head.s).marks).s).points,
			pathdown = root.*r {

				some t : pathdown {
					
						// there is one tree in the commit that has the relation name->blob
						p.name -> p.blob in t.contains 

						let pathup = t.^(~r) |
					
								// the depth of the path tree must be equal to the path leading to the
								// tree t
								#p.^pathparent = #(pathup & pathdown) and

								//for all parent trees there must be some correspondance to a parent
								// path
								all t' : (pathup & pathdown) |
								
									// t'' is son of t' ; p' is some parent in the path
									some t'' : (t.*(~r) & pathdown), p' : p.^pathparent |
											p'.name -> t'' in t'.contains and
											#(t.*(~r) & t'.*r) = #p'.*(~pathparent)
				 }
		 }


	//post-condition
	// the path is removed from the index
	index.s' = index.s - p

	//all others relations are kept
	parent.s' = parent.s
	marks.s' = marks.s
	branches.s' = branches.s
	head.s' = head.s
	objects.s' = objects.s
}

/*
run { 
	some s,s':State | commit[s,s'] && no head.s &&  some (index.s).pathparent
	
} for 5 but exactly 2 State

pred commit[s,s' : State] {
			s != s'

//			index.s' = index.s
	some c:Commit{
		c not in objects.s
		index.s' = index.s
		no head.s =>  {		head.s' = master
									branches.s' = master
									marks.s' = master -> c
									no parent.s'
							  }
					   else{		head.s' = head.s
									branches.s' = branches.s + master
									marks.s' = marks.s ++ head.s' -> c
									parent.s' = parent.s + c -> head.s.(marks.s)
							 }
		let r = {t:Tree, o:(Tree+Blob) | some n:Name | t -> n -> o in contains}{
			objects.s' = objects.s  + c + c.points.*r
	
			all p:index.s | no p.pathparent => p.name -> p.blob in c.points.contains
			all o: c.points.contains
*/
		/*	all disj p,p': index.s | (p.pathparent = p'.pathparent <=> 
				(some t: c.points.*r | p.name -> p.blob + p.name -> p'.blob in t.contains))
			
			all t:c.points.*r, n: t.contains, sons:n.(t.contains) | some p:(index.s).*parent, p':p.parent 
			
			all p:index.s.*pathparent | 
				some p.pathparent => 
					(some disj t,t':c.points.*r | p.name in t.contains.(Tree + p.blob) &&  t in (p.pathparent.name).(t'.contains))
				else p.name in (c.points).contains.(p.blob + Tree)
*/
/*					all p:index.s | some t: c.points.*r | p.name -> p.blob in t .contains && 
						all p': p.^pathparent | some t',t'':c.points.*r | t + t' in ^r.t && p'.name -> t' in t''.contains
*/

/*					all t:c.points.*r | some p:index.s | t.contains in p.name -> p.blob &&
						all t',t'':c.points.*r | some p':p.^pathparent | t''.contains in p'.name -> t'
	*/				
/*					all p:index.s, p':p.^pathparent |  some t: c.points.*r | p.name -> p.blob in t .contains &&
							p'.name -> Tree
					all o:(c.points).^r | o.
*/

/*					all p: (index.s) | some t: (contains.(p.blob)).(p.name) | t in c.points.^r &&
						all p':(index.s).^pathparent | p'.name in Tree.(contains.t)
	*/		//		all o: c.points.*r | (o.contains)
//				}	
		//all p:index.s | some o:c.points.^r | o = p.blob && all p':p.*pathparent | some o':r.o.r | o'=p'.blob
				

pred commit[s,s' : State] {

	s != s' 

	some new : Commit & objects.s' {
	  
		let lastC = (((head.s).marks).s),
				r = { t : Tree, o : (Tree+Blob) | some n : Name | t->n->o in contains},
				root = new.points,
				pathdown = root.*r {
	
				//new commit cannot have same tree relative to last commit
				new.points != lastC.points
			
		// the number of relations to the model that new points must be equal to the index
				#(contains & pathdown->Name->(Tree+Blob)) = #(index.s').*pathparent

				//the new commit must  be son of the previous head commit, or none if none existed before
				lastC = (new.parent).s'

				//the branch points to the new commit and head must point to the same branch
				new = ((head.s').marks).s' and  head.s' = head.s			

					// all objects that  belong to the previous state must belong to new state plus the
				// new ones
				let newObjs = (new.points).*r | objects.s' = objects.s + newObjs 

				// all files and just the files in the index must be present in the new commit
				// (Hard)
				all p : index.s |
		
						some t : pathdown |
					
								p.name -> p.blob in t.contains and

								let pathup = t.^(~r) |
					
										#p.^pathparent = #(pathup & pathdown) and 									

										all t' : (pathup & pathdown) |
								
											some t'' : ((pathup+t) & pathdown), p' : p.^pathparent |
													
													(p'.name -> t'' in t'.contains)  and
													#((pathup+t) & t'.*r) = #p'.*(~pathparent)
			}
		}

	index.s' = index.s
}

run { 
	
	some s,s':State | commit[s,s'] and #(index.s) = 2 and some (index.s).pathparent

} for 10 but exactly 2 State, 6 Int
