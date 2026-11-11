module

public import StacksFrontier.AlgebraicGeometry.Stacks.ClassifyingStackFirstCohomology
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.Torsion
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.SmoothPerfectField
public import StacksFrontier.Examples.Stacks.NonAlgebraicHomStack.FormalObjects
public import StacksFrontier.Examples.Stacks.NonAlgebraicHomStack.Situation

/-!
# The classifying stack `[S/A]` of the example of a non-algebraic Hom-stack

For the standing data of Section 0AF8 (`Stacks.Examples.NonAlgebraicHomStack.Situation`), the
constant abelian scheme `A = A₀ ×_k S` over `S = Spec k⟦t⟧` is commutative and smooth over `S`, so
its classifying stack `[S/A]` is an algebraic stack (Stacks 04TK) and has a small model `𝒵` with
the universes of the 2-category of algebraic stacks, equivalent to `[S/A]` over the site. The
class in `H¹(U, A)` of the torsor attached to an object over `U` is a classifying invariant of `𝒵`
with values in `U ↦ H¹(U, A)` (`Stacks.Examples.NonAlgebraicHomStack.h1Presheaf`), which is the
input of `Stacks.Examples.NonAlgebraicHomStack.exists_not_isEffective_homStack` and
`Stacks.Examples.NonAlgebraicHomStack.not_isAlgebraicStack_homStack`.

## Main definitions

* `Stacks.Examples.NonAlgebraicHomStack.Situation.classifyingStackModel`: the small model `𝒵` of
  `[S/A]`.
* `Stacks.Examples.NonAlgebraicHomStack.Situation.classifyingStackModelEquivalenceOver`: its
  equivalence over the site with `[S/A]`.
* `Stacks.Examples.NonAlgebraicHomStack.Situation.classifyingStackModelClass`: the class in `H¹`.

## Main results

* `Stacks.Examples.NonAlgebraicHomStack.Situation.smooth_abelianScheme`: `A ⟶ S` is smooth.
* `Stacks.Examples.NonAlgebraicHomStack.Situation.isClassifyingInvariant_classifyingStackModelClass`
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Examples.NonAlgebraicHomStack.Situation

variable {k : Type u} [Field k] (sit : Situation k)

/-- The constant abelian scheme is commutative: so is the abelian variety `A₀` (Tag 03RP), and
base change preserves commutative group objects. -/
instance isCommMonObj_abelianScheme : IsCommMonObj sit.abelianScheme :=
  haveI := sit.isAbelianVariety
  ((Over.pullback (baseToField (k := k))).mapCommGrp.obj
    (CommGrp.mk sit.A₀)).comm

/-- **The constant abelian scheme is smooth over `S`**: the abelian variety `A₀` is a reduced
group scheme locally of finite type over the perfect field `k` (Stacks 047P), and smoothness is
stable under base change. -/
theorem smooth_abelianScheme : Smooth sit.abelianScheme.hom := by
  have := sit.isAlgClosed
  have := sit.isAbelianVariety
  have : GrpObj (Over.mk sit.A₀.hom) := inferInstanceAs (GrpObj sit.A₀)
  have h0 : Smooth sit.A₀.hom :=
    smooth_of_isReduced_groupScheme_of_perfectField k sit.A₀.left sit.A₀.hom
  exact AlgebraicGeometry.smooth_isStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback sit.A₀.hom (baseToField (k := k))) h0

variable (B : BigFppfSite.{u}) (hS : B.Contains (base k)) (hA : B.Contains sit.abelianScheme.left)

/-- The abelian sheaf of points of the constant abelian scheme on the big fppf site of `S`. -/
abbrev pointsSheafA : Sheaf (BigFppfOver.topology B (base k) hS) AddCommGrpCat.{u} :=
  pointsSheaf B (base k) hS sit.abelianScheme hA

/-- **The small model of the classifying stack `[S/A]`**, with the universes of the
2-category of algebraic stacks. -/
abbrev classifyingStackModel : BasedCategory.{u, u + 1} (BigFppfOver B (base k) hS) :=
  Stack.classifyingStackModel B (base k) hS sit.abelianScheme hA sit.smooth_abelianScheme

/-- The small model is equivalent to `[S/A]` over the site. -/
def classifyingStackModelEquivalenceOver :
    StacksRepresentableCFG.EquivalenceOver (sit.classifyingStackModel B hS hA).p
      (Stack.classifyingStackOfGroupScheme B (base k) hS sit.abelianScheme hA).p :=
  Stack.classifyingStackModelEquivalenceOver B (base k) hS sit.abelianScheme hA
    sit.smooth_abelianScheme

/-- The small model of `[S/A]` is fibred in groupoids. -/
theorem isFiberedInGroupoids_classifyingStackModel :
    (sit.classifyingStackModel B hS hA).p.IsFiberedInGroupoids :=
  (Stack.AlgebraicStacks.smallModel B (base k) hS _
    (Stack.isAlgebraicStack_classifyingStackOfGroupScheme B (base k) hS sit.abelianScheme hA
      sit.smooth_abelianScheme)).val.property

variable [HasSheafify (BigFppfOver.topology B (base k) hS) AddCommGrpCat.{u}]
  [HasExt.{u} (Sheaf (BigFppfOver.topology B (base k) hS) AddCommGrpCat.{u})]

/-- **The class in `H¹(U, A)` of an object of the small model of `[S/A]` over `U`.** -/
def classifyingStackModelClass (z : (sit.classifyingStackModel B hS hA).obj) :
    (h1Presheaf B hS (sit.pointsSheafA B hS hA)).obj
      (op ((sit.classifyingStackModel B hS hA).p.obj z)) :=
  Stack.classifyingStackClass B (base k) hS sit.abelianScheme hA sit.smooth_abelianScheme z

/-- **The class in `H¹(-, A)` is a classifying invariant of the small model of `[S/A]`**: it is
natural, every class over `U` is the class of an object over `U`, and objects whose classes agree
along an isomorphism of their bases are related by a morphism over that isomorphism. -/
theorem isClassifyingInvariant_classifyingStackModelClass :
    Deformation.Artin.IsClassifyingInvariant (h1Presheaf B hS (sit.pointsSheafA B hS hA))
      (sit.classifyingStackModelClass B hS hA) :=
  Stack.isClassifyingInvariant_classifyingStackClass B (base k) hS sit.abelianScheme hA
    sit.smooth_abelianScheme

end Stacks.Examples.NonAlgebraicHomStack.Situation

end
