# Formal-verification-project

This project is really not user friendly, I personaly built it in Scastie and used the scalac tools to output the results.

To test the algorithm, you have to first create some variables with the class Var (which is basically a string) and then the atoms. All atoms are linear constraints and they are built with the class ConstraintLin which take a Map from variables to a RationalFinite. Here is an example :

2x+3y = Map((Var("x")->RationalFinite(2,1)), (Var("y")->RationalFinite(3,1)))

Then you want to build the constraints, so you give a lower and an upper bound on this expression which are RationalFinite or RationalInfinite, indicate if these bounds are strict or not :

-∞ < 2x+3y <= 5 = ConstriantLin(2x+3y, new RationalInfinite(-1), new RationalFinite(5, 1), true, false)

And now you can make some list of list of them to have a clausal from and make a Formula :

F = new Formula([[-∞ < 2x+3y <= 5]])

Then you have to normalize it, give it to the Simplex class and compute the result :

Simplex(F.toNorm()).protocol()

The result will be prompted in the console.
