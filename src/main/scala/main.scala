import javax.swing.SpringLayout.Constraints
abstract class Rational {
    def less(r: Rational): Boolean = {
        (this, r) match {
            case (RationalFiniteInf(a, b, c), RationalFiniteInf(x, y, z)) => {
              if (a * y == x * b) {
                (c < z)
              } else {
                (a * y < x * b)
              }
            }
            case (RationalFiniteInf(a, b, c), RationalFinite(x, y)) => {
              if (a * y == x * b) {
                (c < RationalFinite(0, 1))
              } else {
                (a * y < x * b)
              }
            }
            case (RationalFinite(a, b), RationalFiniteInf(x, y, z)) => {
              if (a * y == x * b) {
                (RationalFinite(0, 1) < z)
              } else {
                (a * y < x * b)
              }
            }
            case (RationalFinite(a, b), RationalFinite(x, y)) => (a * y < x * b)
            case (RationalInfinite(1), _) => false
            case (_, RationalInfinite(-1)) => false
            case _ => true
        }
    }

    def <(r: Rational): Boolean = less(r)

    def more(r: Rational): Boolean = {
        (this, r) match {
            case (RationalFiniteInf(a, b, c), RationalFiniteInf(x, y, z)) => {
              if (a * y == x * b) {
                (c > z)
              } else {
                (a * y > x * b)
              }
            }
            case (RationalFiniteInf(a, b, c), RationalFinite(x, y)) => {
              if (a * y == x * b) {
                (c > RationalFinite(0, 1))
              } else {
                (a * y > x * b)
              }
            }
            case (RationalFinite(a, b), RationalFiniteInf(x, y, z)) => {
              if (a * y == x * b) {
                (RationalFinite(0, 1) > z)
              } else {
                (a * y > x * b)
              }
            }
            case (RationalFinite(a, b), RationalFinite(x, y)) => (a * y > x * b)
            case (_, RationalInfinite(1)) => false
            case (RationalInfinite(-1), _) => false
            case _ => true
        }
    }

    def >(r: Rational): Boolean = more(r)
  
    def eval(r: RationalFinite): Rational = this
  
    def toStringInf: String = toString
}
case class RationalFinite(x: Int, y: Int) extends Rational {

    // require is used to enforce a precondition on the caller
    require(y != 0, "denominator must be non-zero")

    // define a greatest common divisor method we can use to simplify rationals
    private def gcd(a: Int, b: Int): Int = Math.abs(if (b == 0) a else gcd(b, a % b))

    val g = gcd(x, y)

    val numer = x / g
    val denom = y / g

    // define methods on this class
    def add(r: RationalFinite): RationalFinite =
        new RationalFinite(numer * r.denom + r.numer * denom, denom * r.denom)

    def +(r: RationalFinite): RationalFinite = add(r)

    // negation
    def neg = new RationalFinite(-numer, denom)
    def unary_- : RationalFinite = neg

    def sub(r: RationalFinite): RationalFinite = add(r.neg)

    def -(r: RationalFinite): RationalFinite = sub(r)

    def mult(r: RationalFinite) =
        new RationalFinite(numer * r.numer, denom * r.denom)

    def *(r: RationalFinite): RationalFinite = mult(r)
  
    def multInf(r: RationalFiniteInf) =
        new RationalFiniteInf(numer * r.numer, denom * r.denom, this * r.infinitesimal)
  
    def *(r: RationalFiniteInf): RationalFiniteInf = multInf(r)

    def div(r: RationalFinite) =
        new RationalFinite(numer * r.denom, denom * r.numer)

    def /(r: RationalFinite): RationalFinite = div(r)

    def max(r: RationalFinite): RationalFinite = if (less(r)) r else this

    def min(r: RationalFinite): RationalFinite = if (more(r)) r else this

    def inv: RationalFinite = new RationalFinite(denom, numer)
    def unary_/ : RationalFinite = inv
  
    def absoluteValue(): RationalFinite = new RationalFinite(numer.abs, denom.abs)

    override
    def toString: String = numer.toString + "/" + denom.toString
}
case class RationalFiniteInf(x: Int, y: Int, inf: RationalFinite) extends Rational {

    // require is used to enforce a precondition on the caller
    require(y != 0, "denominator must be non-zero")

    // define a greatest common divisor method we can use to simplify rationals
    private def gcd(a: Int, b: Int): Int = Math.abs(if (b == 0) a else gcd(b, a % b))

    val g = gcd(x, y)

    val numer = x / g
    val denom = y / g
    val infinitesimal = inf

    // define methods on this class
    def add(r: RationalFiniteInf): RationalFiniteInf =
        new RationalFiniteInf(numer * r.denom + r.numer * denom, denom * r.denom, infinitesimal + r.infinitesimal)

    def +(r: RationalFiniteInf): RationalFiniteInf = add(r)

    // negation
    def neg = new RationalFiniteInf(-numer, denom, -infinitesimal)
    def unary_- : RationalFiniteInf = neg

    def sub(r: RationalFiniteInf): RationalFiniteInf = add(r.neg)

    def -(r: RationalFiniteInf): RationalFiniteInf = sub(r)
  
    def mult(r: RationalFinite): RationalFiniteInf =
        new RationalFiniteInf(numer * r.numer, denom * r.denom, r * infinitesimal)

    def *(r: RationalFinite): RationalFiniteInf = mult(r)

    def div(r: RationalFinite): RationalFiniteInf =
        new RationalFiniteInf(numer * r.denom, denom * r.numer, r.inv * infinitesimal)

    def /(r: RationalFinite): RationalFiniteInf = div(r)

    def max(r: RationalFiniteInf): RationalFiniteInf = if (less(r)) r else this

    def min(r: RationalFiniteInf): RationalFiniteInf = if (more(r)) r else this
  
    override
    def eval(r: RationalFinite): RationalFinite = new RationalFinite(numer, denom) + r * infinitesimal

    override
    def toStringInf: String = numer.toString + "/" + denom.toString + " + " + infinitesimal.toString + "δ"
  
    override
    def toString: String = numer.toString + "/" + denom.toString
}
case class RationalInfinite(x: Int) extends Rational {
    require(x == 1 || x == -1)
    
    override
    def toString: String = {
        if (x == 1) {"∞"} else {"-∞"}
    }
}

class Var(val name: String) {
    override
    def toString: String = name
}

class ConstraintLin(val expr: Map[Var, RationalFinite], val lowerBound: Rational, val upperBound: Rational, val lowStrict: Boolean, val upStrict: Boolean) {
    require(verif)
  
    def getVar(): Set[Var] = {
        expr.keySet
    }
  
    def verif: Boolean = {
        if (lowStrict || upStrict) {
            (lowerBound < upperBound)
        } else {
            !(lowerBound > upperBound)
        }
    }
    def auxToString(expr: Map[Var, RationalFinite]): String = {
        def aux(l: List[(Var, RationalFinite)]): String = {
            l match {
                case head :: tl if tl.isEmpty => head._2.toString + "*" + head._1.toString + aux(tl)
                case head :: tl => head._2.toString + "*" + head._1.toString + " + " + aux(tl)
                case Nil => ""
            }
        }
        aux(expr.toList)
    }

    override
    def toString: String = {
        if (upStrict) {
            if (lowStrict) {
                lowerBound.toString + " < " + auxToString(expr) + " < " + upperBound.toString
            } else {
                lowerBound.toString + " <= " + auxToString(expr) + " < " + upperBound.toString
            }
        } else {
            if (lowStrict) {
                lowerBound.toString + " < " + auxToString(expr) + " <= " + upperBound.toString
            } else {
               lowerBound.toString + " <= " + auxToString(expr) + " <= " + upperBound.toString
            }
        }
    }
}

class ConstraintNorm(val variable: Var, val lowerBound: Rational, val upperBound: Rational) {
    require(!(lowerBound > upperBound))
    //require(isInf)
  
    def isInf: Boolean = {
        lowerBound match {
            case RationalFiniteInf(_, _, _) => true
            case _ => false
        }
    }
  
    def toStringClean: String = {
        lowerBound match {
            case RationalFiniteInf(a, b, c) if (c > RationalFinite(0, 1)) => {
                upperBound match {
                    case RationalFiniteInf(d, e, f) if (f < RationalFinite(0, 1)) => lowerBound.toString + " < " + variable.toString + " < " + upperBound.toString
                    case _ => lowerBound.toString + " < " + variable.toString + " <= " + upperBound.toString
                }
            }
            case _ => {
                upperBound match {
                    case RationalFiniteInf(d, e, f) if (f < RationalFinite(0, 1)) => lowerBound.toString + " <= " + variable.toString + " < " + upperBound.toString
                    case _ => lowerBound.toString + " <= " + variable.toString + " <= " + upperBound.toString
                }
            }
        }
    }
    
    override
    def toString: String = {
        lowerBound.toStringInf + " <= " + variable.toString + " <= " + upperBound.toStringInf
    }
}

class Formula(form: List[List[ConstraintLin]]) {
    def toNorm(): NormFormula = {
        def auxNbVar(formula: List[ConstraintLin]): Set[Var] = {
            formula match {
                case head :: tl => head.getVar() ++ auxNbVar(tl)
                case Nil => Set()
            }
        }

        def nbVar(formula: List[List[ConstraintLin]]): Set[Var] = {
            formula match {
                case head :: tl => auxNbVar(head) ++ nbVar(tl)
                case Nil => Set()
            }
        }

        def mapnip(varMap: List[Var], expr: Map[Var, RationalFinite]): Map[Var, RationalFinite] = {
            varMap match {
                case head :: tl if expr.contains(head) => Map(head -> expr(head)) ++ mapnip(tl, expr)
                case head :: tl => Map(head -> new RationalFinite(0, 1)) ++ mapnip(tl, expr)
                case Nil => Map()
            }
        }

        def auxGetMat(formula: List[ConstraintLin], varMap: List[Var], i: Int): (Map[Var, Map[Var, RationalFinite]], Int) = {
            formula match {
                case head :: tl if head.expr.size > 1 => (Map((new Var("s" + i.toString())) -> mapnip(varMap, head.expr)) ++ auxGetMat(tl, varMap, i + 1)._1, auxGetMat(tl, varMap, i + 1)._2)
                case head :: tl => auxGetMat(tl, varMap, i)
                case Nil => (Map(), i)
            }
        }

        def getMat(formula: List[List[ConstraintLin]], varMap: List[Var], i: Int): Map[Var, Map[Var, RationalFinite]] = {
            formula match {
                case head :: tl => auxGetMat(head, varMap, i)._1 ++ getMat(tl, varMap, auxGetMat(head, varMap, i)._2)
                case Nil => Map()
            }
        }
      
        def iziLintoNorm(exp: ConstraintLin): ConstraintNorm = {
            val (key, value) = exp.expr.head
            
            if (exp.lowStrict) {
                if (exp.upStrict) {
                    (exp.lowerBound, exp.upperBound) match {
                        case (RationalFinite(x, y), RationalFinite(w, z)) => new ConstraintNorm(key, RationalFiniteInf(x, y, RationalFinite(1, 1)) / value, RationalFiniteInf(w, z, RationalFinite(-1, 1)) / value)
                        case (RationalFinite(x, y), _) => new ConstraintNorm(key, RationalFiniteInf(x, y, RationalFinite(1, 1)) / value, exp.upperBound)
                        case (_, RationalFinite(x, y)) => new ConstraintNorm(key, exp.lowerBound, RationalFiniteInf(x, y, RationalFinite(-1, 1)) / value)
                        case _ => new ConstraintNorm(key, exp.lowerBound, exp.upperBound)
                    }
                } else {
                    (exp.lowerBound, exp.upperBound) match {
                        case (RationalFinite(x, y), RationalFinite(w, z)) => new ConstraintNorm(key, RationalFiniteInf(x, y, RationalFinite(1, 1)) / value, RationalFiniteInf(w, z, RationalFinite(0, 1)) / value)
                        case (RationalFinite(x, y), _) => new ConstraintNorm(key, RationalFiniteInf(x, y, RationalFinite(1, 1)) / value, exp.upperBound)
                        case (_, RationalFinite(x, y)) => new ConstraintNorm(key, exp.lowerBound, RationalFiniteInf(x, y, RationalFinite(0, 1)) / value)
                        case _ => new ConstraintNorm(key, exp.lowerBound, exp.upperBound)
                    }
                }
            } else {
                if (exp.upStrict) {
                    (exp.lowerBound, exp.upperBound) match {
                        case (RationalFinite(x, y), RationalFinite(w, z)) => new ConstraintNorm(key, RationalFiniteInf(x, y, RationalFinite(0, 1)) / value, RationalFiniteInf(w, z, RationalFinite(-1, 1)) / value)
                        case (RationalFinite(x, y), _) => new ConstraintNorm(key, RationalFiniteInf(x, y, RationalFinite(0, 1)) / value, exp.upperBound)
                        case (_, RationalFinite(x, y)) => new ConstraintNorm(key, exp.lowerBound, RationalFiniteInf(x, y, RationalFinite(-1, 1)) / value)
                        case _ => new ConstraintNorm(key, exp.lowerBound, exp.upperBound)
                    }
                } else {
                    (exp.lowerBound, exp.upperBound) match {
                        case (RationalFinite(x, y), RationalFinite(w, z)) => new ConstraintNorm(key, RationalFiniteInf(x, y, RationalFinite(0, 1)) / value, RationalFiniteInf(w, z, RationalFinite(0, 1)) / value)
                        case (RationalFinite(x, y), _) => new ConstraintNorm(key, RationalFiniteInf(x, y, RationalFinite(0, 1)) / value, exp.upperBound)
                        case (_, RationalFinite(x, y)) => new ConstraintNorm(key, exp.lowerBound, RationalFiniteInf(x, y, RationalFinite(0, 1)) / value)
                        case _ => new ConstraintNorm(key, exp.lowerBound, exp.upperBound)
                    }
                }
            }
        }
      
        def iziTooLinToNorm(exp: ConstraintLin, v: Var): ConstraintNorm = {          
            if (exp.lowStrict) {
                if (exp.upStrict) {
                    (exp.lowerBound, exp.upperBound) match {
                        case (RationalFinite(x, y), RationalFinite(w, z)) => new ConstraintNorm(v, RationalFiniteInf(x, y, RationalFinite(1, 1)), RationalFiniteInf(w, z, RationalFinite(-1, 1)))
                        case (RationalFinite(x, y), _) => new ConstraintNorm(v, RationalFiniteInf(x, y, RationalFinite(1, 1)), exp.upperBound)
                        case (_, RationalFinite(x, y)) => new ConstraintNorm(v, exp.lowerBound, RationalFiniteInf(x, y, RationalFinite(-1, 1)))
                        case _ => new ConstraintNorm(v, exp.lowerBound, exp.upperBound)
                    }
                } else {
                    (exp.lowerBound, exp.upperBound) match {
                        case (RationalFinite(x, y), RationalFinite(w, z)) => new ConstraintNorm(v, RationalFiniteInf(x, y, RationalFinite(1, 1)), RationalFiniteInf(w, z, RationalFinite(0, 1)))
                        case (RationalFinite(x, y), _) => new ConstraintNorm(v, RationalFiniteInf(x, y, RationalFinite(1, 1)), exp.upperBound)
                        case (_, RationalFinite(x, y)) => new ConstraintNorm(v, exp.lowerBound, RationalFiniteInf(x, y, RationalFinite(0, 1)))
                        case _ => new ConstraintNorm(v, exp.lowerBound, exp.upperBound)
                    }
                }
            } else {
                if (exp.upStrict) {
                    (exp.lowerBound, exp.upperBound) match {
                        case (RationalFinite(x, y), RationalFinite(w, z)) => new ConstraintNorm(v, RationalFiniteInf(x, y, RationalFinite(0, 1)), RationalFiniteInf(w, z, RationalFinite(-1, 1)))
                        case (RationalFinite(x, y), _) => new ConstraintNorm(v, RationalFiniteInf(x, y, RationalFinite(0, 1)), exp.upperBound)
                        case (_, RationalFinite(x, y)) => new ConstraintNorm(v, exp.lowerBound, RationalFiniteInf(x, y, RationalFinite(-1, 1)))
                        case _ => new ConstraintNorm(v, exp.lowerBound, exp.upperBound)
                    }
                } else {
                    (exp.lowerBound, exp.upperBound) match {
                        case (RationalFinite(x, y), RationalFinite(w, z)) => new ConstraintNorm(v, RationalFiniteInf(x, y, RationalFinite(0, 1)), RationalFiniteInf(w, z, RationalFinite(0, 1)))
                        case (RationalFinite(x, y), _) => new ConstraintNorm(v, RationalFiniteInf(x, y, RationalFinite(0, 1)), exp.upperBound)
                        case (_, RationalFinite(x, y)) => new ConstraintNorm(v, exp.lowerBound, RationalFiniteInf(x, y, RationalFinite(0, 1)))
                        case _ => new ConstraintNorm(v, exp.lowerBound, exp.upperBound)
                    }
                }
            }
        }

        def auxGetNorm(formula: List[ConstraintLin], newVarMap: List[Var]): (List[ConstraintNorm], List[Var]) = {
            formula match {
                case head :: tl if head.expr.size > 1 => (iziTooLinToNorm(head, newVarMap.head) :: auxGetNorm(tl, newVarMap.tail)._1, auxGetNorm(tl, newVarMap.tail)._2)
                case head :: tl => (iziLintoNorm(head) :: auxGetNorm(tl, newVarMap)._1, auxGetNorm(tl, newVarMap)._2)
                case Nil => (List(), newVarMap)
            }
        }

        def getNorm(formula: List[List[ConstraintLin]], newVarMap: List[Var]): List[List[ConstraintNorm]] = {
            formula match {
                case head :: tl => auxGetNorm(head, newVarMap)._1 :: getNorm(tl, auxGetNorm(head, newVarMap)._2)
                case Nil => List()
            }
        }
      
        var newMat: Map[Var, Map[Var, RationalFinite]] = getMat(form, nbVar(form).toList, 0)
        
        new NormFormula(newMat, getNorm(form, newMat.keySet.toList))
    }
  
    def auxToString(form: List[List[ConstraintLin]]): String = {
        def aux1(form: List[List[ConstraintLin]]): String = {
            form match {
                case head :: tl if tl.isEmpty => "( " + aux2(head) + " )" + aux1(tl)
                case head :: tl => "( " + aux2(head) + " )" + " ∧ " + aux1(tl)
                case Nil => ""
            }
        }
      
        def aux2(form: List[ConstraintLin]): String = {
            form match {
                case head :: tl if tl.isEmpty => head.toString + aux2(tl)
                case head :: tl => head.toString + " ∨ " + aux2(tl)
                case Nil => ""
            }
        }
      
        aux1(form)
    }
  
    override
    def toString: String = {
        auxToString(form)
    }
}

class NormFormula(var matrix: Map[Var, Map[Var, RationalFinite]], val form: List[List[ConstraintNorm]]) {
    def pivot(x: Var, y: Var): Unit = {
        def auxneg(row: Map[Var, RationalFinite], denomy: RationalFinite): Map[Var, RationalFinite] = {
            var res: Map[Var, RationalFinite] = Map()
            for ((k, v) <- row) {res = res + (k -> v * denomy)}
            res
        }
        def aux1(row: Map[Var, RationalFinite], y: Var): Map[Var, Map[Var, RationalFinite]] = {
            var res: Map[Var, Map[Var, RationalFinite]] = Map()
            for ((k, v) <- matrix) {res = res + (k -> aux2(v, row, v(y)))}
            res
        }
        def aux2(crow: Map[Var, RationalFinite], row: Map[Var, RationalFinite], facty: RationalFinite): Map[Var, RationalFinite] = {
            var res: Map[Var, RationalFinite] = Map()
            for ((k, v) <- row) {if (crow.contains(k)) {res = res + (k -> (crow(k) + v * facty))} else {res = res + (k -> (v * facty))}}
            res
        }
        
        var rowx: Map[Var, RationalFinite] = matrix(x)
        rowx = rowx + (x -> new RationalFinite(-1, 1))
        rowx = rowx + (y -> -rowx(y))
        rowx = rowx ++ auxneg(rowx, (new RationalFinite(1, 1)) / rowx(y))
        rowx = rowx - y
        matrix = matrix - x
        matrix = aux1(rowx, y)
        matrix = matrix + (y -> rowx)
    }

    def auxToStringForm(form: List[List[ConstraintNorm]]): String = {
        def aux1(form: List[List[ConstraintNorm]]): String = {
            form match {
                case head :: tl if tl.isEmpty => "( " + aux2(head) + " )" + aux1(tl)
                case head :: tl => "( " + aux2(head) + " )" + " ∧ " + aux1(tl)
                case Nil => ""
            }
        }
      
        def aux2(form: List[ConstraintNorm]): String = {
            form match {
                case head :: tl if tl.isEmpty => head.toString + aux2(tl)
                case head :: tl => head.toString + " ∨ " + aux2(tl)
                case Nil => ""
            }
        }
      
        aux1(form)
    }
  
    def auxToStringMat(matrix: Map[Var, Map[Var, RationalFinite]]): String = {
        def aux1(matrix: List[(Var, Map[Var, RationalFinite])]): String = {
            matrix match {
                case head :: tl if tl.isEmpty => head._1.toString + " = " + aux2(head._2.toList) + aux1(tl)
                case head :: tl => head._1.toString + " = " + aux2(head._2.toList) + " ∧ " + aux1(tl)
                case Nil => ""
            }
        }
      
        def aux2(matrix: List[(Var, RationalFinite)]): String = {
            matrix match {
                case head :: tl if tl.isEmpty => head._2.toString + "*" + head._1.toString + aux2(tl)
                case head :: tl => head._2.toString + "*" + head._1.toString + " + " + aux2(tl)
                case Nil => ""
            }
        }
        
        aux1(matrix.toList)
    }
  
    override
    def toString: String = {
        "( " + auxToStringMat(matrix) + " )" + " ∧ " + "( " + auxToStringForm(form) + " )"
    }
}

class Simplex(var formS: NormFormula) {
    def betaInit(): Map[Var, RationalFiniteInf] = {
        def auxNbVar(formula: List[(Var, RationalFinite)]): Set[Var] = {
            formula match {
                case head :: tl => Set(head._1) ++ auxNbVar(tl)
                case Nil => Set()
            }
        }

        def nbVar(formula: List[(Var, Map[Var, RationalFinite])]): Set[Var] = {
            formula match {
                case head :: tl => Set(head._1) ++ nbVar(tl)
                case Nil => Set()
            }
        }
      
        def aux1(formula: List[ConstraintNorm]): Set[Var] = {
            formula match {
                case head :: tl => Set(head.variable) ++ aux1(tl)
                case Nil => Set()
            }
        }

        def aux2(formula: List[List[ConstraintNorm]]): Set[Var] = {
            formula match {
                case head :: tl => aux1(head) ++ aux2(tl)
                case Nil => Set()
            }
        }
      
        def aux(l: Set[Var]): Map[Var, RationalFiniteInf] = {
            var res: Map[Var, RationalFiniteInf] = Map()
            for (e <- l) {res = res + (e -> new RationalFiniteInf(0, 1, RationalFinite(0, 1)))}
            res
        }
        
        if (formS.matrix.isEmpty) {
            if (formS.form.isEmpty) {
                Map()
            } else {
                aux(aux2(formS.form))
            }
        } else {
            if (formS.form.isEmpty) {
                aux(nbVar(formS.matrix.toList) ++ auxNbVar(formS.matrix.toList.head._2.toList))
            } else {
                aux(nbVar(formS.matrix.toList) ++ auxNbVar(formS.matrix.toList.head._2.toList) ++ aux2(formS.form))
            }
        }
    }
  
    def formulaInit(): Map[Var, (Rational, Rational)] = {
        def auxNbVar(formula: List[(Var, RationalFinite)]): Set[Var] = {
            formula match {
                case head :: tl => Set(head._1) ++ auxNbVar(tl)
                case Nil => Set()
            }
        }

        def nbVar(formula: List[(Var, Map[Var, RationalFinite])]): Set[Var] = {
            formula match {
                case head :: tl => Set(head._1) ++ nbVar(tl)
                case Nil => Set()
            }
        }
      
        def aux1(formula: List[ConstraintNorm]): Set[Var] = {
            formula match {
                case head :: tl => Set(head.variable) ++ aux1(tl)
                case Nil => Set()
            }
        }

        def aux2(formula: List[List[ConstraintNorm]]): Set[Var] = {
            formula match {
                case head :: tl => aux1(head) ++ aux2(tl)
                case Nil => Set()
            }
        }
      
        def aux(l: Set[Var]): Map[Var, (Rational, Rational)] = {
            var res: Map[Var, (Rational, Rational)] = Map()
            for (e <- l) {res = res + (e -> (new RationalInfinite(-1), new RationalInfinite(1)))}
            res
        }
      
        if (formS.matrix.isEmpty) {
            if (formS.form.isEmpty) {
                Map()
            } else {
                aux(aux2(formS.form))
            }
        } else {
            if (formS.form.isEmpty) {
                aux(nbVar(formS.matrix.toList) ++ auxNbVar(formS.matrix.toList.head._2.toList))
            } else {
                aux(nbVar(formS.matrix.toList) ++ auxNbVar(formS.matrix.toList.head._2.toList) ++ aux2(formS.form))
            }
        }
    }
  
    def recomputeBeta(): Unit = {
        def aux1(l1: List[Var]): Unit = {
            l1 match {
                case head :: tl => {
                    beta = beta + (l1.head -> aux2(formS.matrix(head).toList))
                    aux1(tl)
                }
                case _ => ()
            }
        }
      
        def aux2(l2: List[(Var, RationalFinite)]): RationalFiniteInf = {
            l2 match {
                case head :: tl => beta(head._1) * head._2 + aux2(tl)
                case _ => new RationalFiniteInf(0, 1, RationalFinite(0, 1))
            }
        }
        
        aux1(formS.matrix.keySet.toList)
    }
  
    def assertAtom(constraintNorm: ConstraintNorm): Boolean = {
        constraintNorm.lowerBound match {
            case RationalFiniteInf(w, x, _) if (constraintNorm.lowerBound > formulaSoFar(constraintNorm.variable)._2) => false
            case RationalFiniteInf(w, x, _) if (constraintNorm.lowerBound < formulaSoFar(constraintNorm.variable)._1) => {
                constraintNorm.upperBound match {
                    case RationalFiniteInf(y, z, _) if (constraintNorm.upperBound < formulaSoFar(constraintNorm.variable)._1) => false
                    case RationalFiniteInf(y, z, _) if (constraintNorm.upperBound > formulaSoFar(constraintNorm.variable)._2) => true
                    case RationalFiniteInf(y, z, _) if !(beta(constraintNorm.variable) > constraintNorm.upperBound) => {
                        formulaSoFar = formulaSoFar + (constraintNorm.variable -> (formulaSoFar(constraintNorm.variable)._1, constraintNorm.upperBound))
                        true
                    }
                    case RationalFiniteInf(y, z, _) if (formS.matrix.contains(constraintNorm.variable)) => {
                        formulaSoFar = formulaSoFar + (constraintNorm.variable -> (formulaSoFar(constraintNorm.variable)._1, constraintNorm.upperBound))
                        check()
                    }
                    case RationalFiniteInf(y, z, inf) => {
                        beta = beta + (constraintNorm.variable -> new RationalFiniteInf(y, z, inf))
                        recomputeBeta()
                        formulaSoFar = formulaSoFar + (constraintNorm.variable -> (formulaSoFar(constraintNorm.variable)._1, constraintNorm.upperBound))
                        true
                    }
                }
            }
            case RationalFiniteInf(w, x, _) if !(beta(constraintNorm.variable) < constraintNorm.lowerBound) => {
                constraintNorm.upperBound match {
                    case RationalFiniteInf(y, z, _) if (constraintNorm.upperBound < formulaSoFar(constraintNorm.variable)._1) => false
                    case RationalFiniteInf(y, z, _) if (constraintNorm.upperBound > formulaSoFar(constraintNorm.variable)._2) => {
                        formulaSoFar = formulaSoFar + (constraintNorm.variable -> (constraintNorm.lowerBound, formulaSoFar(constraintNorm.variable)._2))
                        true
                    }
                    case RationalFiniteInf(y, z, _) if !(beta(constraintNorm.variable) > constraintNorm.upperBound) => {
                        formulaSoFar = formulaSoFar + (constraintNorm.variable -> (constraintNorm.lowerBound, constraintNorm.upperBound))
                        true
                    }
                    case RationalFiniteInf(y, z, _) if (formS.matrix.contains(constraintNorm.variable)) => {
                        formulaSoFar = formulaSoFar + (constraintNorm.variable -> (constraintNorm.lowerBound, constraintNorm.upperBound))
                        check()
                    }
                    case RationalFiniteInf(y, z, inf) => {
                        beta = beta + (constraintNorm.variable -> new RationalFiniteInf(y, z, inf))
                        recomputeBeta()
                        formulaSoFar = formulaSoFar + (constraintNorm.variable -> (constraintNorm.lowerBound, constraintNorm.upperBound))
                        true
                    }
                }
            }
            case RationalFiniteInf(w, x, _) if (formS.matrix.contains(constraintNorm.variable)) => {
                constraintNorm.upperBound match {
                    case RationalFiniteInf(y, z, _) if (constraintNorm.upperBound > formulaSoFar(constraintNorm.variable)._2) => {
                        formulaSoFar = formulaSoFar + (constraintNorm.variable -> (constraintNorm.lowerBound, formulaSoFar(constraintNorm.variable)._2))
                        check()
                    }
                    case _ => {
                        formulaSoFar = formulaSoFar + (constraintNorm.variable -> (constraintNorm.lowerBound, constraintNorm.upperBound))
                        check()
                    }
                }
            }
            case RationalFiniteInf(w, x, inf) => {
                constraintNorm.upperBound match {
                    case RationalFiniteInf(y, z, _) if (constraintNorm.upperBound > formulaSoFar(constraintNorm.variable)._2) => {
                        beta = beta + (constraintNorm.variable -> new RationalFiniteInf(w, x, inf))
                        recomputeBeta()
                        formulaSoFar = formulaSoFar + (constraintNorm.variable -> (constraintNorm.lowerBound, formulaSoFar(constraintNorm.variable)._2))
                        true
                    }
                    case _ => {
                        beta = beta + (constraintNorm.variable -> new RationalFiniteInf(w, x, inf))
                        recomputeBeta()
                        formulaSoFar = formulaSoFar + (constraintNorm.variable -> (constraintNorm.lowerBound, constraintNorm.upperBound))
                        true
                    }
                }
            }
            case _ => {
                constraintNorm.upperBound match {
                    case RationalFiniteInf(y, z, _) if (constraintNorm.upperBound < formulaSoFar(constraintNorm.variable)._1) => false
                    case RationalFiniteInf(y, z, _) if (constraintNorm.upperBound > formulaSoFar(constraintNorm.variable)._2) => true
                    case RationalFiniteInf(y, z, _) if !(beta(constraintNorm.variable) > constraintNorm.upperBound) => {
                        formulaSoFar = formulaSoFar + (constraintNorm.variable -> (formulaSoFar(constraintNorm.variable)._1, constraintNorm.upperBound))
                        true
                    }
                    case RationalFiniteInf(y, z, _) if (formS.matrix.contains(constraintNorm.variable)) => {
                        formulaSoFar = formulaSoFar + (constraintNorm.variable -> (formulaSoFar(constraintNorm.variable)._1, constraintNorm.upperBound))
                        check()
                    }
                    case RationalFiniteInf(y, z, inf) => {
                        beta = beta + (constraintNorm.variable -> new RationalFiniteInf(y, z, inf))
                        recomputeBeta()
                        formulaSoFar = formulaSoFar + (constraintNorm.variable -> (formulaSoFar(constraintNorm.variable)._1, constraintNorm.upperBound))
                        true
                    }
                }
            }
        }
    }
  
    def check(): Boolean = {
        def findFirstOutbound(l: List[Var]): Option[(Var, RationalFiniteInf, Boolean)] = {
            l match {
                case head :: tl if (beta(head) < formulaSoFar(head)._1) => {
                    formulaSoFar(head)._1 match {
                        case RationalFiniteInf(x, y, z) => Some((head, new RationalFiniteInf(x, y, z), false))
                        case _ => None
                    }
                }
                case head :: tl if (beta(head) > formulaSoFar(head)._2) => {
                    formulaSoFar(head)._2 match {
                        case RationalFiniteInf(x, y, z) => Some((head, new RationalFiniteInf(x, y, z), true))
                        case _ => None
                    }
                }
                case head :: tl => findFirstOutbound(tl)
                case _ => None
            }
        }
      
        def findPivotVarAndPivot(v: Var, r: RationalFiniteInf, b: Boolean): Boolean = {
            def aux(l: List[(Var, RationalFinite)], r: RationalFiniteInf, b: Boolean): Boolean = {
                l match {
                    case head :: tl if (head._2 < new RationalFinite(0, 1) && b && beta(head._1) < formulaSoFar(head._1)._2) => {
                        formS.pivot(v, head._1)
                        beta = beta + (v -> r)
                        recomputeBeta()
                        true
                    }
                    case head :: tl if (head._2 < new RationalFinite(0, 1) && beta(head._1) > formulaSoFar(head._1)._1) => {
                        formS.pivot(v, head._1)
                        beta = beta + (v -> r)
                        recomputeBeta()
                        true
                    }
                    case head :: tl if (head._2 > new RationalFinite(0, 1) && b && beta(head._1) > formulaSoFar(head._1)._1) => {
                        formS.pivot(v, head._1)
                        beta = beta + (v -> r)
                        recomputeBeta()
                        true
                    }
                    case head :: tl if (head._2 > new RationalFinite(0, 1) && beta(head._1) < formulaSoFar(head._1)._2) => {
                        formS.pivot(v, head._1)
                        beta = beta + (v -> r)
                        recomputeBeta()
                        true
                    }
                    case head :: tl => aux(tl, r, b)
                    case _ => false
                }
            }
            
            var varMap: List[(Var, RationalFinite)] = formS.matrix(v).toList
            varMap.sortWith(_._2.absoluteValue() < _._2.absoluteValue())
            aux(varMap, r, b)
        }
        
        var fOOB: Option[(Var, RationalFiniteInf, Boolean)] = findFirstOutbound(formS.matrix.keySet.toList)
        fOOB match {
            case Some((x, y, z)) => {
                if (findPivotVarAndPivot(x, y, z)) {
                    check()
                } else {
                    false
                }
            }
            case _ => {
                checkpoints = (formulaSoFar, beta, leftToBeAsserted) :: checkpoints
                true
            }
        }
    }
    
    def backtrack(): Boolean = {
        if (checkpoints.isEmpty) {
            false
        } else {
            formulaSoFar = checkpoints.head._1
            beta = checkpoints.head._2
            if (checkpoints.head._3.head.tail.isEmpty) {
                checkpoints = checkpoints.tail
                backtrack()
            } else {
                leftToBeAsserted = checkpoints.head._3.head.tail :: checkpoints.head._3.tail
                checkpoints = (checkpoints.head._1, checkpoints.head._2, checkpoints.head._3.head.tail :: checkpoints.head._3.tail) :: checkpoints.tail
                true
            }
        }
    }
  
    def getInf(delta: RationalFinite): RationalFinite = {
        def aux(l: List[Var]): Boolean = {
            l match {
                case hd :: tl => (!(formulaSoFar(hd)._1.eval(delta) > beta(hd).eval(delta)) && !(beta(hd).eval(delta) > formulaSoFar(hd)._2.eval(delta))) && aux(tl)
                case _ => true
            }
        }
      
        if (aux(beta.keySet.toList)) {delta} else {getInf(delta * new RationalFinite(1, 2))}
    }
  
    def evalBeta(delta: RationalFinite): Map[Var, RationalFinite] = {
        def aux(be: List[(Var, RationalFiniteInf)]): Map[Var, RationalFinite] = {
            be match {
                case hd :: tl => Map(hd._1 -> beta(hd._1).eval(delta)) ++ aux(tl)
                case _ => Map()
            }
        }
      
        aux(beta.toList)
    }
  
    def protocol(): Unit = {
        leftToBeAsserted match {
            case hd :: tl if (hd.tail.isEmpty) => {
                formulaForFailure = Set(hd) ++ formulaForFailure
                if (assertAtom(hd.head)) {
                    leftToBeAsserted = leftToBeAsserted.tail
                    protocol()
                } else {
                    if (backtrack()) {
                        protocol()
                    } else {
                        println("Failure : " + auxToStringFailure(formulaForFailure.toList))
                    }
                }
            }
            case hd :: tl => {
                formulaForFailure = Set(hd) ++ formulaForFailure
                if (assertAtom(hd.head)) {
                    if (check()) {
                        leftToBeAsserted = leftToBeAsserted.tail
                    } else {
                        leftToBeAsserted = leftToBeAsserted.head.tail :: leftToBeAsserted.tail
                    }
                } else {
                    leftToBeAsserted = leftToBeAsserted.head.tail :: leftToBeAsserted.tail
                }
                protocol()
            }
            case _ => {
                print("Success : ")
                print(auxToStringBeta() + " | ")
                println(auxToStringBetaEval(evalBeta(getInf(new RationalFinite(1, 1)))))
            }
        }
    }
  
    var beta: Map[Var, RationalFiniteInf] = betaInit()
    var formulaSoFar: Map[Var, (Rational, Rational)] = formulaInit()
    var leftToBeAsserted: List[List[ConstraintNorm]] = formS.form
    var checkpoints: List[(Map[Var, (Rational, Rational)], Map[Var, RationalFiniteInf], List[List[ConstraintNorm]])] = List((formulaSoFar, beta, leftToBeAsserted))
    var formulaForFailure: Set[List[ConstraintNorm]] = Set()
  
    def auxToStringBeta(): String = {
        def aux(l: List[(Var, RationalFiniteInf)]): String = {
            l match {
                case head :: tl if tl.isEmpty => head._1.toString + " = " + head._2.toStringInf + aux(tl)
                case head :: tl => head._1.toString + " = " + head._2.toStringInf + ", " + aux(tl)
                case Nil => " )"
            }
        }
        "( " + aux(beta.toList)
    }
  
    def auxToStringBetaEval(be: Map[Var, RationalFinite]): String = {
        def aux(l: List[(Var, RationalFinite)]): String = {
            l match {
                case head :: tl if tl.isEmpty => head._1.toString + " = " + head._2.toString + aux(tl)
                case head :: tl => head._1.toString + " = " + head._2.toString + ", " + aux(tl)
                case Nil => " )"
            }
        }
        "( " + aux(be.toList)
    }
  
    def auxToStringFormula(): String = {
        def aux(l: List[(Var, (Rational, Rational))]): String = {
            l match {
                case head :: tl if tl.isEmpty => head._2._1.toStringInf + " <= " + head._1.toString + " <= " + head._2._2.toStringInf + aux(tl)
                case head :: tl => head._2._1.toStringInf + " <= " + head._1.toString + " <= " + head._2._2.toStringInf + ", " + aux(tl)
                case Nil => " )"
            }
        }
        "( " + aux(formulaSoFar.toList)
    }
  
    def auxToStringFailure(form: List[List[ConstraintNorm]]): String = {
        def aux1(form: List[List[ConstraintNorm]]): String = {
            form match {
                case head :: tl if tl.isEmpty => "( " + aux2(head) + " )" + aux1(tl)
                case head :: tl => "( " + aux2(head) + " )" + " ∧ " + aux1(tl)
                case Nil => ""
            }
        }
      
        def aux2(form: List[ConstraintNorm]): String = {
            form match {
                case head :: tl if tl.isEmpty => head.toStringClean + aux2(tl)
                case head :: tl => head.toStringClean + " ∨ " + aux2(tl)
                case Nil => ""
            }
        }
      
        def aux3(cn: ConstraintNorm): String = {
            cn.lowerBound.toString + " <= " + cn.variable.toString + " <= " + cn.upperBound.toString
        }
      
        aux1(form)
    }
  
    override
    def toString: String = {
        auxToStringBeta() + auxToStringFormula()
    }
}



val rational: RationalFinite = new RationalFinite(2, 3)
val infinity: RationalInfinite = new RationalInfinite(1)

rational
infinity

val x: Var = new Var("x")
val y: Var = new Var("y")

x
y

val constraintLin1: ConstraintLin = new ConstraintLin(Map((x -> new RationalFinite(1, 1))),
                                                      new RationalInfinite(-1), 
                                                      new RationalFinite(1, 1),
                                                      false, false)

val constraintLin2: ConstraintLin = new ConstraintLin(Map((x -> new RationalFinite(2, 1)), 
                                                          y -> new RationalFinite(2, 1)), 
                                                      new RationalFinite(-2, 1), 
                                                      new RationalFinite(-1, 1),
                                                      false, true)

val constraintLin3: ConstraintLin = new ConstraintLin(Map(x -> new RationalFinite(1, 1)), 
                                                      new RationalFinite(3, 1), 
                                                      new RationalFinite(4, 1),
                                                      true, false)

val constraintLin4: ConstraintLin = new ConstraintLin(Map((x -> new RationalFinite(4, 1)), 
                                                          y -> new RationalFinite(4, 1)), 
                                                      new RationalFinite(-4, 1), 
                                                      new RationalFinite(-1, 1),
                                                      true, true)

constraintLin1
constraintLin2
constraintLin3
constraintLin4

val f: Formula = new Formula(List(List(constraintLin1, constraintLin2), List(constraintLin3, constraintLin4)))

f

val nf: NormFormula = f.toNorm()

nf

var simpl: Simplex = new Simplex(nf)

simpl

simpl.protocol()

simpl

val f1: NormFormula = new Formula(List(List(new ConstraintLin(Map((x -> new RationalFinite(1, 1))), new RationalInfinite(-1), new RationalFinite(1, 1), true, false)), List(new ConstraintLin(Map((x -> new RationalFinite(1, 1))), new RationalFinite(1, 1), new RationalInfinite(1), true, true)), List(new ConstraintLin(Map((x -> new RationalFinite(1, 1))), new RationalInfinite(-1), new RationalFinite(1, 1), true, false)))).toNorm()

f1

var simpl1: Simplex = new Simplex(f1)

simpl1.protocol()

simpl1












