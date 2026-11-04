module

public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import StacksCore.Tactic.EgaSgaAttribute

/-! # Separatedness and the plus construction

Let `(C, J)` be a site and `F` a presheaf of sets on `C`.  Stacks 00WB collects the four basic
properties of the plus construction `F ↦ F⁺` relating it to separatedness and to the sheaf
condition.  Following the source, "separated" means that two sections over `X` which agree
after restriction along every arrow of some covering sieve of `X` are equal.

## Main results

* `StacksSheafification.IsSeparated`: a presheaf is *separated* when sections are determined
  locally (Stacks 00WA, the hypothesis of Stacks 00WB(2)).
* `StacksSheafification.isSeparated_plusObj`: `F⁺` is separated (Stacks 00WB(1)).
* `StacksSheafification.isSheaf_plusObj`: if `F` is separated then `F⁺` is a sheaf
  (Stacks 00WB(2), first half).
* `StacksSheafification.injective_toPlus_app`: if `F` is separated then `F → F⁺` is injective
  (Stacks 00WB(2), second half).
* `StacksSheafification.isIso_toPlus`: if `F` is a sheaf then `F → F⁺` is an isomorphism
  (Stacks 00WB(3)).
* `StacksSheafification.isSheaf_plusObj_plusObj`: `F⁺⁺` is always a sheaf
  (Stacks 00WB(4)).

## References

* [Stacks Project, Tag 00WB](https://stacks.math.columbia.edu/tag/00WB)
-/

@[expose] public section

namespace StacksSheafification

open CategoryTheory CategoryTheory.Limits Opposite

universe u

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-- **Stacks 00WA.** A presheaf of sets `P` on a site `(C, J)` is *separated* if for every
covering sieve `S` of an object `X` two sections `x y : P(X)` whose restrictions along all the
arrows of `S` agree are already equal. -/
def IsSeparated (P : Cᵒᵖ ⥤ Type u) : Prop :=
  ∀ (X : C) (S : J.Cover X) (x y : P.obj (op X)),
    (∀ I : S.Arrow, P.map I.f.op x = P.map I.f.op y) → x = y

variable (P : Cᵒᵖ ⥤ Type u)

/-- **Stacks 00WB(1).** The presheaf `P⁺` is separated. -/
@[stacks 00WB, sga "3 IV 4.3.11" "(i), LP separated", sga "4 II 3.2" "2)"]
theorem isSeparated_plusObj : IsSeparated J (J.plusObj P) :=
  fun _ S _ _ h => GrothendieckTopology.Plus.sep P S _ _ h

/-- **Stacks 00WB(2), first half.** If `P` is separated then `P⁺` is a sheaf. -/
@[stacks 00WB]
theorem isSheaf_plusObj (hP : IsSeparated J P) : Presheaf.IsSheaf J (J.plusObj P) :=
  GrothendieckTopology.Plus.isSheaf_of_sep P hP

/-- **Stacks 00WB(2), second half.** If `P` is separated then the canonical map
`P → P⁺` is injective on sections over every object. -/
@[stacks 00WB, sga "3 IV 4.3.11" "(iv), mono part", sga "4 II 3.2" "3) separated ⇒ mono"]
theorem injective_toPlus_app (hP : IsSeparated J P) (X : C) :
    Function.Injective ((J.toPlus P).app (op X)) :=
  GrothendieckTopology.Plus.inj_of_sep (J := J) P (fun Y S x y h => hP Y S x y h) X

/-- **Stacks 00WB(3).** If `P` is a sheaf then the canonical map `P → P⁺` is an
isomorphism. -/
@[stacks 00WB, sga "3 IV 4.3.11" "(ii)", sga "4 II 3.2" "4) (ii) ⇒ (i)"]
theorem isIso_toPlus (hP : Presheaf.IsSheaf J P) : IsIso (J.toPlus P) :=
  J.isIso_toPlus_of_isSheaf P hP

/-- **Stacks 00WB(4).** The presheaf `P⁺⁺` is always a sheaf. -/
@[stacks 00WB, sga "4 II 3.2" "clause 3, special case"]
theorem isSheaf_plusObj_plusObj : Presheaf.IsSheaf J (J.plusObj (J.plusObj P)) :=
  GrothendieckTopology.Plus.isSheaf_plus_plus J P

end StacksSheafification
