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
		//path is on index
		p in index.s
		//the blob
		let r = {t:Tree, o:(Tree+Blob) | some n:Name | t -> n -> o in contains},
			 root = (head.s).(marks.s).points
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
		head.s' = head.s
}

run { 
	some s,s':State | commit[s,s'] && no head.s && some index.s
} for 3 but exactly 2 State

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
					all p:index.s, p':p.^pathparent | some t: (contains.(p.blob)).(p.name) | t in c.points.^r &&
							p'.name = Tree.contains.t


/*					all p: (index.s) | some t: (contains.(p.blob)).(p.name) | t in c.points.^r &&
						all p':(index.s).^pathparent | p'.name in Tree.(contains.t)
	*/		//		all o: c.points.*r | (o.contains)
				}	
		//all p:index.s | some o:c.points.^r | o = p.blob && all p':p.*pathparent | some o':r.o.r | o'=p'.blob
				
			}


}
