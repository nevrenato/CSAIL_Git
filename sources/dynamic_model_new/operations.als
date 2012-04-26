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
		on.s' = on.s
}

pred rm[s,s' : State, p:Path] {
		s != s'

	//pre-condition
		//path is on index
		p in index.s
		//the blob
		let r = {t:Tree, o:(Tree+Blob) | some n:Name | t -> n -> o in contains},
			 root = (Head.(on.s)).(marks.s).points
		{
			p.blob in root.^r
		}
	
	//post-condition
		//a path is added to the set of objects
		objects.s' = objects.s + p.blob 
		//a path is added to index
		index.s' = index.s + p

		//all others relations are kept
		parent.s' = parent.s
		marks.s' = marks.s
		branches.s' = branches.s
		on.s' = on.s
}

run { 
//	some s,s':State, p:Path | add[s,s',p] 
	one Head
	some parent
	one Branch
	#Commit.points > 1
	#Commit > 1
	one Path
	one index
} for 5 but exactly 1 State

pred commit[s,s' : State] {
			s != s'
/*
			some c : Commit  {
					
					// the parent of the new commit is the last commit
					s'.(c.parent) = s.(Head.pointsToLast)
					// the new commit cannot be in the last state
					no s.(c.parent) 
				 	// Head points to the new commit
					s'.(Head.pointsToLast) = c
			
					
					// The Hard part
					all f : s.(Index.staged) {

						let root = c.points, 
								fname = (s.(f.pathname)).name,
								fparents = (s.(f.pathname)).^parent,
								sons = 
								{t : Tree, t' : (Tree+Blob) | some n : Name | t->s'->n->t' in contains}  {
				
								
							// The object model of the new commit (s') can only have the blobs
							// that are staged in s
							(root.^sons) & Blob in s.((s.(Index.staged)).blob)
				
								one t : root.*sons {
														
											// relation name->blob in some tree									
											fname->s.(f.blob) in s'.(t.contains)
														
											// and for all parents of that file there must be a correspondent
											// tree										
											all fp : fparents |
												one t',t'' : root.*sons |
														some fp.parent implies s'->(fp.name->t'') in t'.contains   		
							  }
					   }
					}
			}
*/
}

