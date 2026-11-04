module

public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionBaseRestriction
public import StacksFrontier.Deformation.RingedSpaceThickening.SolutionHomAlgebraExtension
public import StacksFrontier.Deformation.RingedSpaceThickening.SolutionPushoutExtensions
public import StacksFrontier.Deformation.RingedSpaceThickening.SolutionTorsor
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentDerivedExt
public import StacksFrontier.Deformation.ToposThickening.FlatLiftTorsors

/-!
# The isomorphism classes of solutions are a torsor (Stacks 08UC)

Fix a first order thickening `t : (S, 𝒪_S) ⟶ (S', 𝒪_{S'})`, a morphism `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)`,
an `𝒪_X`-module `𝒢` and a map `c : f^*t^*𝒥 ⟶ 𝒢`. **Stacks 08UC** says that if the deformation
problem (91.7.0.1) of **Stacks 08U7** has a solution, then the set of isomorphism classes of
solutions is principal homogeneous under `Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)`.

## The argument

A solution `X'` is a square-zero extension `𝒪_{X'}` of `(f ≫ t)⁻¹𝒪_{S'}`-algebras
(`DeformationSolution.toAlgebraExtension`), so it has a class
`κ(X') ∈ Ext¹_{𝒪_X}(𝖭𝖫_{X/S'}, 𝒢)` (`DeformationSolution.extClass`). Two solutions are isomorphic
exactly when their classes agree (`DeformationSolution.extClass_eq_extClass_iff_isomorphic`): by
the converse of **Stacks 0GPZ**'s separation
(`AlgebraSquareZeroExtension.exists_hom_of_extClass_eq`) and the translation between morphisms of
solutions and morphisms of their extensions.

The two solutions `X'₁`, `X'₂` also have a difference: the square-zero pushout of the difference
homomorphism over `𝒪_{X'₁} ×_{𝒪_X} 𝒪_{X'₂}`, which is an extension of `f⁻¹𝒪_S`-algebras because
both solutions induce the same map `c` on the ideal of the base
(`DeformationSolution.differenceExtension`). Its class
`o(X'₁, X'₂) ∈ Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)` is the difference class (`differenceClass`), and the
injective homomorphism `ρ : Ext¹(𝖭𝖫_{X/S}, 𝒢) ⟶ Ext¹(𝖭𝖫_{X/S'}, 𝒢)` of `restrictBaseExtClassHom`
carries it to `κ(X'₁) - κ(X'₂)`. Conversely every `κ(X') + ρ(ξ)` is the class of a solution
(`DeformationSolution.exists_extClass_eq_add`: the source's pushout along `ψ`). Injectivity of
`ρ` turns these two facts into the cocycle identity and the realization of every class, which is
the obstruction data `SolutionObstruction` of `SolutionTorsor.lean`.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.isomorphicSetoid`: isomorphism of solutions,
  `AlgebraicGeometry.RingedSpaceThickening.Isomorphic`, as an equivalence relation; and
  `SolutionClasses`, the set of isomorphism classes, as its `Quotient`.
* `AlgebraicGeometry.RingedSpaceThickening.differenceClass`: the class `o(X'₁, X'₂)`.
* `AlgebraicGeometry.RingedSpaceThickening.solutionTwist`: the solution `X'_ξ`.
* `AlgebraicGeometry.RingedSpaceThickening.solutionClassesAddTorsor`: **Stacks 08UC**, the
  principal homogeneous structure, as Mathlib's `AddTorsor`.

## References

* [Stacks Project, Tag 08UC](https://stacks.math.columbia.edu/tag/08UC)
* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8)
* [Stacks Project, Tag 0GPZ](https://stacks.math.columbia.edu/tag/0GPZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

attribute [local instance] HasDerivedCategory.standard

variable {X S S' : RingedSpace.{u, u}} {t : S ⟶ S'} {ht : IsFirstOrderThickening t} {f : X ⟶ S}
  {G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf)}
  {c : (modulePullback f).obj
    ((modulePullback t).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶ G}

/-! ### The class of a solution over `S'` -/

namespace DeformationSolution

/-- The class `κ(X') ∈ Ext¹_{𝒪_X}(𝖭𝖫_{X/S'}, 𝒢)` of a solution: the class of its structure sheaf
as a square-zero extension of `(f ≫ t)⁻¹𝒪_{S'}`-algebras. -/
abbrev extClass (Q : DeformationSolution t ht f G c) :
    (PresentedSquareZeroExtension.relativeObj (f ≫ t) ⟶
      PresentedSquareZeroExtension.shiftedSingleObj G) :=
  Q.toAlgebraExtension.toPresented.extClass

/-- **Two solutions are isomorphic exactly when their classes over `S'` agree.** -/
theorem extClass_eq_extClass_iff_isomorphic (Q₁ Q₂ : DeformationSolution t ht f G c) :
    Q₁.extClass = Q₂.extClass ↔ Isomorphic Q₁ Q₂ := by
  refine Iff.trans ?_ (isomorphic_iff_nonempty_solutionHom Q₁ Q₂).symm
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨θ, hbase, hred, hideal⟩ := AlgebraSquareZeroExtension.exists_hom_of_extClass_eq
      Q₂.toAlgebraExtension Q₁.toAlgebraExtension Q₁.toAlgebraExtension_idealBijective h.symm
    exact ⟨solutionHomOfExtensionHom θ hred hideal hbase⟩
  · obtain ⟨θ, hbase, hred, hideal⟩ := (nonempty_solutionHom_iff Q₂ Q₁).1 h
    exact (AlgebraSquareZeroExtension.extClass_eq_extClass_of_hom _ _ θ hbase hred hideal).symm

end DeformationSolution

/-! ### Isomorphism classes -/

/-- **Isomorphism of solutions of Stacks 08U7 is an equivalence relation.** The relation is the
library's geometric one, `Isomorphic`, by definition. -/
def isomorphicSetoid : Setoid (DeformationSolution t ht f G c) where
  r := Isomorphic
  iseqv :=
    { refl := isomorphic_refl
      symm := fun {Q₁ Q₂} h => (DeformationSolution.extClass_eq_extClass_iff_isomorphic Q₂ Q₁).1
        ((DeformationSolution.extClass_eq_extClass_iff_isomorphic Q₁ Q₂).2 h).symm
      trans := fun {Q₁ Q₂ Q₃} h₁ h₂ =>
        (DeformationSolution.extClass_eq_extClass_iff_isomorphic Q₁ Q₃).1
          (((DeformationSolution.extClass_eq_extClass_iff_isomorphic Q₁ Q₂).2 h₁).trans
            ((DeformationSolution.extClass_eq_extClass_iff_isomorphic Q₂ Q₃).2 h₂)) }

/-- Two solutions are related by `isomorphicSetoid` exactly when they are isomorphic. -/
theorem isomorphicSetoid_r (Q₁ Q₂ : DeformationSolution t ht f G c) :
    (isomorphicSetoid : Setoid (DeformationSolution t ht f G c)) Q₁ Q₂ ↔ Isomorphic Q₁ Q₂ :=
  Iff.rfl

variable (t ht f G c) in
/-- **The set of isomorphism classes of solutions** of the deformation problem of
**Stacks 08U7**. -/
abbrev SolutionClasses : Type _ :=
  Quotient (isomorphicSetoid (t := t) (ht := ht) (f := f) (G := G) (c := c))

/-! ### The difference class and the action -/

/-- **The difference class `o(X'₁, X'₂) ∈ Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)` of two solutions**: the class
of their difference, a square-zero extension of `f⁻¹𝒪_S`-algebras. -/
def differenceClass (Q₁ Q₂ : DeformationSolution t ht f G c) :
    (PresentedSquareZeroExtension.relativeObj f ⟶
      PresentedSquareZeroExtension.shiftedSingleObj G) :=
  (Q₁.differenceExtension Q₂).toPresented.extClass

/-- **The difference class, read over `S'`, is the difference of the two classes.** -/
theorem restrictBaseExtClass_differenceClass (Q₁ Q₂ : DeformationSolution t ht f G c) :
    restrictBaseExtClassHom t (differenceClass Q₁ Q₂) = Q₁.extClass - Q₂.extClass :=
  (restrictBaseExtClass_extClass t _).trans (Q₁.restrictBase_differenceExtension_extClass Q₂)

/-- Two difference classes agree once their images over `S'` agree. -/
private theorem differenceClass_eq_iff_restrictBase (ht : IsFirstOrderThickening t)
    (Q₁ Q₂ : DeformationSolution t ht f G c)
    (ξ : (PresentedSquareZeroExtension.relativeObj f ⟶
      PresentedSquareZeroExtension.shiftedSingleObj G)) :
    differenceClass Q₁ Q₂ = ξ ↔ Q₁.extClass - Q₂.extClass = restrictBaseExtClassHom t ξ := by
  rw [← (restrictBaseExtClass_injective t ht.1).eq_iff, ← restrictBaseExtClassHom_apply,
    ← restrictBaseExtClassHom_apply, restrictBaseExtClass_differenceClass]

/-- **The cocycle identity** `o(X'₁, X'₂) + o(X'₂, X'₃) = o(X'₁, X'₃)`. -/
theorem differenceClass_add (Q₁ Q₂ Q₃ : DeformationSolution t ht f G c) :
    differenceClass Q₁ Q₂ + differenceClass Q₂ Q₃ = differenceClass Q₁ Q₃ := by
  refine ((differenceClass_eq_iff_restrictBase ht _ _ _).2 ?_).symm
  rw [map_add, restrictBaseExtClass_differenceClass, restrictBaseExtClass_differenceClass,
    sub_add_sub_cancel]

/-- **Two solutions are isomorphic exactly when their difference class vanishes.** This is the
source's "this element is the obstruction to the existence of an isomorphism". -/
theorem differenceClass_eq_zero_iff (Q₁ Q₂ : DeformationSolution t ht f G c) :
    differenceClass Q₁ Q₂ = 0 ↔ Isomorphic Q₁ Q₂ := by
  rw [differenceClass_eq_iff_restrictBase ht, map_zero, sub_eq_zero,
    DeformationSolution.extClass_eq_extClass_iff_isomorphic]

/-- **The solution `X'_ξ` of the source's proof**: a solution whose class over `S'` is
`κ(X') + ρ(ξ)`, which exists by the pushout construction along `ψ`. -/
def solutionTwist (Q : DeformationSolution t ht f G c)
    (ξ : (PresentedSquareZeroExtension.relativeObj f ⟶
      PresentedSquareZeroExtension.shiftedSingleObj G)) :
    DeformationSolution t ht f G c :=
  (Q.exists_extClass_eq_add (exists_extension_extClass_eq (f := f) (G := G) ξ).choose).choose

/-- The class of `X'_ξ` over `S'` is `κ(X') + ρ(ξ)`. -/
theorem extClass_solutionTwist (Q : DeformationSolution t ht f G c)
    (ξ : (PresentedSquareZeroExtension.relativeObj f ⟶
      PresentedSquareZeroExtension.shiftedSingleObj G)) :
    (solutionTwist Q ξ).extClass = Q.extClass + restrictBaseExtClassHom t ξ :=
  (Q.exists_extClass_eq_add
      (exists_extension_extClass_eq (f := f) (G := G) ξ).choose).choose_spec.trans
    (congrArg (Q.extClass + ·) ((restrictBaseExtClass_extClass t _).symm.trans
      (congrArg (restrictBaseExtClass t)
        (exists_extension_extClass_eq (f := f) (G := G) ξ).choose_spec)))

/-- **The difference class of `X'_ξ` and `X'` is `ξ`**: the source's "a calculation shows that
`o(X', X'_ξ) = ξ`", with the difference written in the order of the torsor's subtraction. -/
theorem differenceClass_solutionTwist (Q : DeformationSolution t ht f G c)
    (ξ : (PresentedSquareZeroExtension.relativeObj f ⟶
      PresentedSquareZeroExtension.shiftedSingleObj G)) :
    differenceClass (solutionTwist Q ξ) Q = ξ := by
  rw [differenceClass_eq_iff_restrictBase ht, extClass_solutionTwist, add_sub_cancel_left]

/-! ### The torsor -/

/-- **The obstruction data of Stacks 08UC**, built: the cocycle is the difference class (in the
order `o(X'₁, X'₂) = [X'₂] - [X'₁]` of `SolutionObstruction`), and the construction `X' ↦ X'_ξ`
is `solutionTwist`. -/
def solutionObstruction :
    SolutionObstruction (DeformationSolution t ht f G c)
      ((PresentedSquareZeroExtension.relativeObj f ⟶
        PresentedSquareZeroExtension.shiftedSingleObj G)) where
  o Q₁ Q₂ := differenceClass Q₂ Q₁
  o_add Q₁ Q₂ Q₃ := (add_comm _ _).trans (differenceClass_add Q₃ Q₂ Q₁)
  twist := solutionTwist
  o_twist := differenceClass_solutionTwist

/-- The equivalence relation of the obstruction data is isomorphism of solutions. -/
theorem solutionObstruction_setoid_iff (Q₁ Q₂ : DeformationSolution t ht f G c) :
    (solutionObstruction (t := t) (ht := ht) (f := f) (G := G) (c := c)).setoid.r Q₁ Q₂ ↔
      Isomorphic Q₁ Q₂ :=
  (differenceClass_eq_zero_iff Q₂ Q₁).trans
    ⟨fun h => isomorphicSetoid.symm h, fun h => isomorphicSetoid.symm h⟩

/-- **Stacks Project, Tag 08UC.** If there exists a solution of the deformation problem
(91.7.0.1) of **Stacks 08U7**, the set of isomorphism classes of solutions is principal
homogeneous under `Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)`, as Mathlib's `AddTorsor`.

The isomorphism classes are the `Quotient` of the solutions by `Isomorphic`; the class
separating two of them is their difference class (`vsub_mk_mk`), and the action of `ξ` on the
class of `X'` is the class of `X'_ξ` (`vadd_mk`). -/
@[instance_reducible]
noncomputable def solutionClassesAddTorsor [Nonempty (DeformationSolution t ht f G c)] :
    AddTorsor ((PresentedSquareZeroExtension.relativeObj f ⟶
      PresentedSquareZeroExtension.shiftedSingleObj G)) (SolutionClasses t ht f G c) :=
  letI := (solutionObstruction (t := t) (ht := ht) (f := f) (G := G) (c := c)).addTorsor
  Deformation.ToposThickening.addTorsorCongr (AddEquiv.refl _)
    (Quotient.congrRight fun Q₁ Q₂ => (solutionObstruction_setoid_iff Q₁ Q₂).symm)

/-- The class separating the classes of two solutions is their difference class. -/
theorem vsub_mk_mk [Nonempty (DeformationSolution t ht f G c)]
    (Q₁ Q₂ : DeformationSolution t ht f G c) :
    letI := solutionClassesAddTorsor (t := t) (ht := ht) (f := f) (G := G) (c := c)
    ((⟦Q₁⟧ : SolutionClasses t ht f G c) -ᵥ ⟦Q₂⟧) = differenceClass Q₁ Q₂ :=
  rfl

/-- The action of `ξ` on the class of `X'` is the class of `X'_ξ`. -/
theorem vadd_mk [Nonempty (DeformationSolution t ht f G c)]
    (ξ : (PresentedSquareZeroExtension.relativeObj f ⟶
      PresentedSquareZeroExtension.shiftedSingleObj G)) (Q : DeformationSolution t ht f G c) :
    letI := solutionClassesAddTorsor (t := t) (ht := ht) (f := f) (G := G) (c := c)
    (ξ +ᵥ (⟦Q⟧ : SolutionClasses t ht f G c)) = ⟦solutionTwist Q ξ⟧ :=
  rfl

end AlgebraicGeometry.RingedSpaceThickening

end
