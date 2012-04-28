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
				}	
		//all p:index.s | some o:c.points.^r | o = p.blob && all p':p.*pathparent | some o':r.o.r | o'=p'.blob
				
			}


}
