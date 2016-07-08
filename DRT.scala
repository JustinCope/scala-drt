sealed class DR (val id: String)

class Individual (id: String) extends DR(id)

class Eventuality (id: String) extends DR(id)

class Event (id: String) extends Eventuality(id)

class State (id: String) extends Eventuality(id)

class Process (id: String) extends Eventuality(id)

// class Condition (val id: String)
	
class Condition (val name: String, val ref: DR, val non_ref: List[DR]){
	def id: String = {
	if (non_ref.length == 0){
		return name + "(" + ref.id + ")"
	} else {
		val nonRefArgs: String = "," + non_ref.map(x=>x.id).mkString(",");
		return name + "(" + ref.id + nonRefArgs + ")"
	}
	}
}

class Condition1 (val name: String,val ref: DR,val arg1: DR){
	def toCondition: Condition = new Condition(name,ref,List(arg1))
}

class Condition2 (val name: String,val ref: DR,val arg1: DR,val arg2: DR){
	def toCondition: Condition = new Condition(name,ref,List(arg2,arg1))
}

class Condition3 (val name: String, val arg1: DR, val arg2: DR){
	def toCondition: Condition = new Condition(name,arg2,List(arg1))
}

class CondScheme1 (val name: String, val ref: DR){
	def apply(dr: DR): Condition1 = new Condition1(name, ref, dr)
}

class CondScheme2b (val name: String,val ref: DR,val arg1: DR){
	def apply(dr: DR): Condition2 = new Condition2(name, ref, arg1, dr)
}

class CondScheme2a (val name: String, val ref: DR) {
	def apply(dr: DR): CondScheme2b = new CondScheme2b(name, ref, dr)
}

class CondScheme3b (val name: String, val arg1: DR){
	def apply(dr: DR): Condition3 = new Condition3(name, arg1, dr)
}

class CondScheme3a (val name: String) {
	def apply(dr: DR): CondScheme3b = new CondScheme3b(name, dr)
}
	
class DRS (val u: Set[DR], val con: Set[Condition]){
	def merge (drs: DRS): DRS = {
		val u1 = u.union(drs.u)
		val con1 = con.union(drs.con)
		new DRS(u1, con1)
	}
	def merge1 (drs: DRSS1): DRSS1 = {
		val u1 = u.union(drs.u)
		val con1 = con.union(drs.con)
		val conscheme1 = drs.y
		new DRSS1(u1,con1,conscheme1)
	}
	def merge2 (drs: DRSS2A): DRSS2A = {
		val u1 = u.union(drs.u)
		val con1 = con.union(drs.con)
		val conscheme2 = drs.y
		new DRSS2A(u1,con1,conscheme2)
	}
}
	
class DRSS1 (u: Set[DR], con: Set[Condition], val y: CondScheme1) extends DRS(u,con){
	def lambda (x: DR): DRS = new DRS(u,Set(y(x).toCondition).union(con))
}

class DRSS2B (u: Set[DR], con: Set[Condition], val y: CondScheme2b) extends DRS(u, con){
	def lambda (x: DR):DRS = new DRS(u,Set(y(x).toCondition).union(con))
	override def merge (drs: DRS): DRSS2B = {
		val u1 = u.union(drs.u)
		val con1 = con.union(drs.con)
		new DRSS2B(u1, con1, y)
	}
}

class DRSS2A (u: Set[DR],con: Set[Condition], val y: CondScheme2a) extends DRS(u,con){
	def lambda (x: DR): DRSS2B = new DRSS2B(u,con,y(x))
}

class DRSS3B (u: Set[DR], con: Set[Condition], val y: CondScheme3b) extends DRS(u,con){
	def lambda (x: DR): DRS = new DRS(u,Set(y(x).toCondition).union(con))
	override def merge (drs: DRS): DRSS3B = {
		val u1 = u.union(drs.u)
		val con1 = con.union(drs.con)
		new DRSS3B(u1, con1, y)
	}
}

class DRSS3A (u: Set[DR], con: Set[Condition], val y: CondScheme3a) extends DRS(u,con){
	def lambda (x: DR): DRSS3B = new DRSS3B(u,con,y(x))
}

class SemRep (val ref: DR,val drs: DRS) {
	override def toString = {
		val universe = drs.u.map(x=>x.id).mkString(", ")
		val conditions = drs.con.map(x=>x.id).mkString(", ")
		"<" + ref.id + ", <" + universe + " | " + conditions + "> >"
	}
}

class SemRep1 (val ref: DR, val drs: DRSS1) {
	def functApp (sr: SemRep): SemRep = {
		val drs1 = drs.lambda(sr.ref).merge(sr.drs)
		new SemRep(ref,drs1)
	}
	def functApp1 (sr: SemRep1): SemRep1 = {
		val drs1 = drs.lambda(sr.ref)
		val drss1 = sr.drs
		val drss2 = drs1.merge1(drss1)
		new SemRep1(ref,drss2)
	}
	def functApp2 (sr: SemRep2A): SemRep2A = {
		val drs1 = drs.lambda(sr.ref)
		val drss1 = sr.drs
		val drss2 = drs1.merge2(drss1)
		new SemRep2A(ref,drss2)
	}
	override def toString = {
		val universe = drs.u.map(x=>x.id).mkString(", ");
		val conditions = if (drs.con.nonEmpty){
			", " + drs.con.map(x=>x.id).mkString(", ")
		} else {
			""
		}
		"<" + ref.id + ", <" + universe + " | " + drs.y.name + "(" + drs.y.ref.id + ",x)" + conditions + "> >"
	}
	}

class SemRep2B (val ref: DR, val drs: DRSS2B){
	def functApp (sr: SemRep): SemRep = {
		val drs1 = drs.lambda(sr.ref).merge(sr.drs)
		new SemRep(ref,drs1)
	}
	override def toString = {
		val universe = drs.u.map(x=>x.id).mkString(", ");
		val conditions = if (drs.con.nonEmpty){
			", " + drs.con.map(x=>x.id).mkString(", ")
		} else {
			""
		}
		"<" + ref.id + ", <" + universe + " | " + drs.y.name + "(" + drs.y.ref.id + ",x" + "," + drs.y.arg1.id + ")" + conditions + "> >"
	}
	}
	
class SemRep2A (val ref: DR, val drs: DRSS2A){
	def functApp (sr: SemRep): SemRep2B = {
		val drs1 = drs.lambda(sr.ref).merge(sr.drs)
		new SemRep2B(ref,drs1)
	}
	override def toString = {
		val universe = drs.u.map(x=>x.id).mkString(" ");
		val conditions = if (drs.con.nonEmpty){
			", " + drs.con.map(x=>x.id).mkString(", ")
		} else {
			""
		}		
		"<" + ref.id + ", <" + universe + " | " + drs.y.name + "(" + drs.y.ref.id + ",x,y)" + conditions + "> >"
	}
	}

class SemRep3B (val drs: DRSS3B){
	def functApp (sr: SemRep): SemRep = {
		val drs1 = drs.lambda(sr.ref).merge(sr.drs)
		new SemRep(sr.ref,drs1)
	}
	override def toString = {
		val universe = drs.u.map(x=>x.id).mkString(", ");
		val conditions = if (drs.con.nonEmpty){
			", " + drs.con.map(x=>x.id).mkString(", ")
		} else {
			""
		}
		"< <" + universe + " | " + drs.y.name + "(x," + drs.y.arg1.id + ")" + conditions + "> >"
	}
}
	
class SemRep3A (val drs: DRSS3A){
	def functApp (sr: SemRep): SemRep3B = {
		val drs1 = drs.lambda(sr.ref).merge(sr.drs)
		new SemRep3B(drs1)
	}
	override def toString = {
		val universe = drs.u.map(x=>x.id).mkString(" ");
		val conditions = if (drs.con.nonEmpty){
		} else {
		}
		"< <" + universe + " | " + drs.y.name + "(x,y)" + conditions + "> >"
	}
	}
		
def lex0 (word: String, n: Int): SemRep = {
	val id: String = typeMap(word) + n.toString;
	val dr: DR = new Individual(id);
	val c: Condition = new Condition(word,dr,List());
	val drs: DRS = new DRS(Set(dr),Set(c));
	new SemRep(dr, drs)
}

def lex1 (word: String, n: Int): SemRep1 = {
	val id: String = typeMap(word) + n.toString;
	val dr: DR = new Event(id);
	val c: CondScheme1 = new CondScheme1(word,dr);
	val drss1: DRSS1 = new DRSS1(Set(dr),Set(),c);
	new SemRep1(dr, drss1)
}

def lex2 (word: String, n: Int): SemRep2A = {
	val id: String = typeMap(word) + n.toString;
	val dr: DR = new State(id);
	val c: CondScheme2a = new CondScheme2a(word,dr);
	val drss2a: DRSS2A = new DRSS2A(Set(dr),Set(),c);
	new SemRep2A(dr,drss2a)
	}
	
def lex3 (word: String): SemRep3A = {
	val c: CondScheme3a = new CondScheme3a(word)
	val drss3a: DRSS3A = new DRSS3A(Set(),Set(),c)
	new SemRep3A(drss3a)
}

///////////////////////////////


val typeMap = Map("john" -> "a", "mary" -> "a", "arrive" -> "e", "leave" -> "e", "love" -> "s", "past" -> "t", "before" -> "t")
//val arityMap = Map("john" -> 1, "arrive" -> 2)

val sr1 = lex0("john", 1)
val sr2 = lex0("mary", 2)
val sr3 = lex1("arrive", 3)
val sr4 = lex1("leave", 7)
val sr5 = lex2("love",4)
val sr6 = lex1("past", 5)
val sr7 = lex3("before")

val sr8 = sr6.functApp1(sr3)
val sr9 = sr8.functApp(sr1)
val sr10 = sr4.functApp(sr2)
val sr11 = sr7.functApp(sr10)
val sr12 = sr11.functApp(sr9)

val sr13 = sr6.functApp2(sr5)
val sr14 = sr13.functApp(sr2).functApp(sr1)
val sr15 = sr5.functApp(sr1).functApp(sr2)
val sr16 = sr7.functApp(sr15)
val sr17 = sr16.functApp(sr14)

println()
println(sr8)
println()
println(sr9)
println()
println(sr10)
println()
println(sr11)
println()
println(sr12)
println()
println(sr13)
println()
println(sr14)
println()
println(sr15)
println()
println(sr16)
println()
println(sr17)
println()






