import Semileanear2024.testproject.letsgo

/-!
# SemiLƎⱯNear 2024

This is the master file where all the finished and unfinished projects may be showcased.

Please create a subfolder for your project, just like "testproject" which is already there.

In order to have a better structure, you may use imports.

Have fun!
-/

--this theorem from Semileanear2024/testproject/letsgo.lean is now available:
#check fundamental_theorem_of_algebra

variable (P Q : Prop) (α : Type)
#check P → Q -- Luckily, arrow types between propositions are themselves propositions
#check ¬P -- in particular the negation, which is defined as ¬P := P → False
#check List α -- List is a dependent type
#check Type → Type -- here we go into a higher universe
