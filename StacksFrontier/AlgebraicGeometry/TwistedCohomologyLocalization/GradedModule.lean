module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TwistActionMorphism
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedFunctorAdditive
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.NonvanishingSections
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The graded cohomology module of the twists of a module by an invertible module

Let `X` be a scheme, `ℒ` an invertible `𝒪_X`-module and `ℱ` an `𝒪_X`-module. For an open
`U ⊆ X` and a cohomological degree `p` the graded group

`H^p_*(U, ℒ, ℱ) = ⨁_{j ∈ ℤ} H^p(U, ℱ ⊗ ℒ^{⊗ j})`

is a graded module over the graded section ring `Γ_*(X, ℒ) = ⨁_{n ≥ 0} Γ(X, ℒ^{⊗ n})` of
[Stacks, Tag 01CV]: a global section `s` of `ℒ^{⊗ n}` multiplies the twist `ℱ ⊗ ℒ^{⊗ j}` into
`ℱ ⊗ ℒ^{⊗ (n + j)}`, and the induced map on cohomology is the action. This file builds that
module structure, for **every** `p` and every `U`.

## Why this is needed

The degree-`0` case is the graded section module of [Stacks, Tag 01CV], built in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TwistSectionRing.lean`. The source of
[Stacks, Tag 09MR] takes the degree-zero localization of `H^p_*(X, ℒ, ℱ)` at `s`, and
`GradedModuleDegreeZeroLocalization` takes the graded module as an *instance* argument, so
without the module structure below the **type** of the source of the comparison map of
[Stacks, Tag 09MR] cannot be formed in a positive degree.

The whole construction is the image under the cohomology functor of the morphism-level
coherence of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TwistActionMorphism.lean`: the unit and
associativity laws there are equations between morphisms of sheaves, and an additive functor
carries them along. Nothing about cohomology is used beyond functoriality and additivity.

## Main definitions

* `Stacks.Cohomology.TwistedGradedModule.twist`: the twist `ℱ ⊗ ℒ^{⊗ j}`.
* `Stacks.Cohomology.TwistedGradedModule.twistedCohomologyModule`:
  `H^p_*(U, ℒ, ℱ) = ⨁_{j} H^p(U, ℱ ⊗ ℒ^{⊗ j})`.
* `Stacks.Cohomology.TwistedGradedModule.act`: the action of a global section of `ℒ^{⊗ n}` on
  `H^p(U, ℱ ⊗ ℒ^{⊗ j})`, landing in `H^p(U, ℱ ⊗ ℒ^{⊗ (n + j)})`.
* `Stacks.Cohomology.TwistedGradedModule.gmodule` and
  `Stacks.Cohomology.TwistedGradedModule.instModule`: the graded module structure and the
  resulting module structure over `Γ_*(X, ℒ)`.
* `Stacks.Cohomology.TwistedGradedModule.grading`: the homogeneous components as additive
  subgroups, with `Stacks.Cohomology.TwistedGradedModule.instDecomposition` and
  `Stacks.Cohomology.TwistedGradedModule.instGradedSMul` the internal-grading data that
  `GradedModuleDegreeZeroLocalization` requires.

## Main results

* `Stacks.Cohomology.TwistedGradedModule.of_smul_of`: **the action on homogeneous elements is
  the map induced on cohomology by multiplication by the section.** This is what pins the module
  structure down; without it the structure would say nothing.
* `Stacks.Cohomology.TwistedGradedModule.degreeZeroLocalization`: the degree-zero localization
  of `H^p_*(U, ℒ, ℱ)` at a global section of `ℒ`, which is the source of the comparison map of
  [Stacks, Tag 09MR].

## Implementation notes

The module structure is **constructed**, not chosen from an existence statement: `gmodule` has a
real body, so `of_smul_of` is a theorem about the structure actually in use rather than about
some structure whose existence is asserted.

The graded ring is graded by `ℕ` and the module by `ℤ`, with the degree map the `VAdd ℕ ℤ` of
`Stacks.SheafOfModules.sectionDegreeVAdd` sending `n +ᵥ j` to `(n : ℤ) + j`. The two spellings
`((n + m : ℕ) : ℤ)` and `(n : ℤ) + (m : ℤ)` of the total degree of a product are crossed exactly
once, in the associativity field, through
`Stacks.SheafOfModules.TwistAction.actionOf_sectionRingMul`, which carries the reindexing
comparison between them; the cohomology classes themselves are then compared by
`Stacks.Cohomology.TwistedGradedModule.map_reindexTwist_heq`, the statement that transport along
an equality of twist degrees is heterogeneously the identity.

The cohomology functor `Stacks.Cohomology.Hfunctor` is the right derived functor of sections of
[Stacks, Tag 01E3]. Additivity of the action in the multiplying section is exactly what the
`add_smul` and `zero_smul` fields need, and
`CategoryTheory.Functor.additive_rightDerived` of
`StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/DerivedFunctorAdditive.lean` supplies it. That
instance is applied as an explicit term rather than left to instance search: at the spelling of
the structure sheaf of a scheme the universe variables of the target category are not determined
by the functor, so a search for it does not fire.

## References

* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 09MR](https://stacks.math.columbia.edu/tag/09MR)
* [Stacks Project, Tag 01E3](https://stacks.math.columbia.edu/tag/01E3)
* [Stacks Project, Tag 01M4](https://stacks.math.columbia.edu/tag/01M4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Cohomology Stacks.SheafOfModules
open Stacks.SheafOfModules.TwistAction
open scoped DirectSum

universe u

namespace Stacks.Cohomology.TwistedGradedModule

attribute [local instance] Stacks.SheafOfModules.sectionDegreeVAdd

attribute [local implicit_reducible] _root_.SheafOfModules.forget
  PresheafOfModules.restrictScalars TensorSheafification.structureSheaf

/-! ### Functoriality of cohomology, read on classes

The cohomology functor is read at a spelling of the structure sheaf of a scheme which does not
iota-reduce, so a rewrite by `CategoryTheory.Functor.map_comp` inside a goal mentioning a twist
has an ill-typed motive. These two lemmas state functoriality for abstract modules, where the
motive is clean, and are then applied as equations. -/

section Functoriality

variable {Y : Type u} [TopologicalSpace Y]
  (R : Sheaf (Opens.grothendieckTopology Y) RingCat.{u})
  [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} R)]

/-- Functoriality of cohomology on a composite, read on a class. -/
theorem map_comp_apply (p : ℕ) (U : Opens Y) {A B D : SheafOfModules.{u} R}
    (f : A ⟶ B) (g : B ⟶ D) (z : (Hgroup R U p A : Type u)) :
    (Hfunctor R U p).map (f ≫ g) z =
      (Hfunctor R U p).map g ((Hfunctor R U p).map f z) := by
  rw [CategoryTheory.Functor.map_comp]
  rfl

/-- The identity morphism induces the identity on cohomology classes. -/
theorem map_id_apply (p : ℕ) (U : Opens Y) (A : SheafOfModules.{u} R)
    (z : (Hgroup R U p A : Type u)) :
    (Hfunctor R U p).map (𝟙 A) z = z := by
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- Equal morphisms induce equal maps on cohomology classes. -/
private theorem map_congr_apply (p : ℕ) (U : Opens Y) {A B : SheafOfModules.{u} R}
    {f g : A ⟶ B} (h : f = g) (z : (Hgroup R U p A : Type u)) :
    (Hfunctor R U p).map f z = (Hfunctor R U p).map g z := by
  subst h
  rfl

/-- Additivity of cohomology in the morphism, read on a class. The additivity of the cohomology
functor is an explicit hypothesis rather than something searched for: the instance exists, as
`CategoryTheory.Functor.additive_rightDerived`, but at the spelling of the structure sheaf of a
scheme instance search for it does not terminate within the default budget. -/
theorem map_add_apply (p : ℕ) (U : Opens Y) (hadd : (Hfunctor R U p).Additive)
    {A B : SheafOfModules.{u} R} (f g : A ⟶ B) (z : (Hgroup R U p A : Type u)) :
    (Hfunctor R U p).map (f + g) z =
      (Hfunctor R U p).map f z + (Hfunctor R U p).map g z := by
  let _ := hadd
  rw [CategoryTheory.Functor.map_add]
  rfl

/-- The zero morphism induces zero on cohomology classes. -/
theorem map_zero_apply (p : ℕ) (U : Opens Y) (hadd : (Hfunctor R U p).Additive)
    {A B : SheafOfModules.{u} R} (z : (Hgroup R U p A : Type u)) :
    (Hfunctor R U p).map (0 : A ⟶ B) z = 0 := by
  let _ := hadd
  rw [CategoryTheory.Functor.map_zero]
  rfl

end Functoriality

variable (X : Scheme.{u})
  (L : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  [IsInvertible (sectionSiteRing X) (sectionSiteSheaf X) L]

attribute [local instance] Stacks.SheafOfModules.tensorRightEquiv

/-- The cohomology functors are additive, being right derived functors of the additive
global-sections functor. This reuses `CategoryTheory.Functor.additive_rightDerived`, applying it
as an explicit term so that no search for it is launched at the scheme spelling. -/
theorem additive_Hfunctor (U : X.Opens) (p : ℕ) :
    (Hfunctor X.ringCatSheaf U p).Additive :=
  Functor.additive_rightDerived (secF X.ringCatSheaf U) p

/-- The twist `ℱ ⊗ ℒ^{⊗ j}`, the coefficients of the degree-`j` homogeneous component of
`H^p_*(U, ℒ, ℱ)`. -/
abbrev twist (F : X.Modules) (j : ℤ) : X.Modules :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X))
        (forget₂ CommRingCat RingCat) ((sectionSiteSheaf X))⟩).obj (F)).obj
    ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L j)))

/-- The degree-`n` homogeneous component `Γ(X, ℒ^{⊗ n})` of the graded section ring
`Γ_*(X, ℒ)`, as a type. -/
abbrev sectionPiece (n : ℕ) : Type u :=
  (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)).val.obj
    (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))

/-- The degree-`j` homogeneous component `H^p(U, ℱ ⊗ ℒ^{⊗ j})` of `H^p_*(U, ℒ, ℱ)`. -/
@[sga "2 XII 1.3" "partial"]
abbrev gradedPiece (F : X.Modules) (p : ℕ) (U : X.Opens) (j : ℤ) : Type u :=
  (Hgroup X.ringCatSheaf U p (twist X L F j) : Type u)

/-- **The graded cohomology module `H^p_*(U, ℒ, ℱ) = ⨁_{j ∈ ℤ} H^p(U, ℱ ⊗ ℒ^{⊗ j})`.** -/
@[sga "2 XII 1.3" "partial"]
abbrev twistedCohomologyModule (F : X.Modules) (p : ℕ) (U : X.Opens) : Type u :=
  ⨁ j : ℤ, gradedPiece X L F p U j

/-- The reindexing comparison of twists along an equality of degrees. -/
abbrev reindexTwist (F : X.Modules) {i i' : ℤ} (h : i = i') :
    twist X L F i ⟶ twist X L F i' :=
  (Invertible.tensorProductIso (sectionSiteRing X) (sectionSiteSheaf X) (Iso.refl F)
    (TensorPower.tensorPowerReindex (sectionSiteRing X) (sectionSiteSheaf X) L h)).hom

/-- **Transport of a cohomology class along an equality of twist degrees is heterogeneously the
identity.** This is what lets the two spellings of the total degree of a product of homogeneous
sections be compared. -/
theorem map_reindexTwist_heq (F : X.Modules) (p : ℕ) (U : X.Opens) {i i' : ℤ} (h : i = i')
    (ξ : gradedPiece X L F p U i) :
    HEq ((Hfunctor X.ringCatSheaf U p).map (reindexTwist X L F h) ξ) ξ := by
  subst h
  refine heq_of_eq ((map_congr_apply X.ringCatSheaf p U
    (tensorProductIso_reindex_hom_of_eq (sectionSiteRing X) (sectionSiteSheaf X) F L
      (rfl : i = i)) ξ).trans ?_)
  exact map_id_apply X.ringCatSheaf p U (twist X L F i) ξ

/-- **The action of a global section of `ℒ^{⊗ n}` on a cohomology class of the twist
`ℱ ⊗ ℒ^{⊗ j}`**: the map induced on cohomology by multiplication by that section. -/
def act (F : X.Modules) (p : ℕ) (U : X.Opens) (n j : ℤ)
    (s : (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L n).val.obj
      (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))))
    (ξ : gradedPiece X L F p U j) : gradedPiece X L F p U (n + j) :=
  (Hfunctor X.ringCatSheaf U p).map
    (actionOf (sectionSiteRing X) (sectionSiteSheaf X) L F n j s) ξ

/-- **The action is additive in the multiplying section.** -/
theorem act_add (F : X.Modules) (p : ℕ) (U : X.Opens) (n j : ℤ)
    (s s' : (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L n).val.obj
      (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))))
    (ξ : gradedPiece X L F p U j) :
    act X L F p U n j (s + s') ξ = act X L F p U n j s ξ + act X L F p U n j s' ξ := by
  refine (map_congr_apply X.ringCatSheaf p U
    (actionOf_add (sectionSiteRing X) (sectionSiteSheaf X) L F n j s s') ξ).trans ?_
  exact map_add_apply X.ringCatSheaf p U (additive_Hfunctor X U p) _ _ ξ

/-- **The zero section acts as zero.** -/
theorem act_zero (F : X.Modules) (p : ℕ) (U : X.Opens) (n j : ℤ)
    (ξ : gradedPiece X L F p U j) :
    act X L F p U n j
      (0 : (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L n).val.obj
        (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))) ξ = 0 := by
  refine (map_congr_apply X.ringCatSheaf p U
    (actionOf_zero (sectionSiteRing X) (sectionSiteSheaf X) L F n j) ξ).trans ?_
  exact map_zero_apply X.ringCatSheaf p U (additive_Hfunctor X U p) ξ

/-- **The graded module structure on the twisted cohomology over the graded section ring.** The
two laws are the images under the cohomology functor of the unit and associativity laws of
multiplication by a global section, and the additivity of the action in the section is the
additivity of that multiplication together with the additivity of the cohomology functor. -/
@[instance_reducible, ega "II 2.6.1" "(F)", ega "III 2.1.1" "partial"]
def gmodule (F : X.Modules) (p : ℕ) (U : X.Opens) :
    DirectSum.Gmodule (fun n : ℕ => sectionPiece X L n) (fun j : ℤ => gradedPiece X L F p U j)
      where
  smul {n j} s ξ := act X L F p U (n : ℤ) j s ξ
  one_smul := by
    intro ⟨j, ξ⟩
    apply Sigma.ext (Int.zero_add j)
    refine HEq.trans (heq_of_eq (congrArg (fun z => act X L F p U 0 j z ξ)
      (sectionRingGradedOne_eq (sectionSiteRing X) (sectionSiteSheaf X) L))) ?_
    refine HEq.trans (heq_of_eq (congrArg (fun φ => (Hfunctor X.ringCatSheaf U p).map φ ξ)
      (actionOf_one (sectionSiteRing X) (sectionSiteSheaf X) L F j))) ?_
    exact map_reindexTwist_heq X L F p U (Int.zero_add j).symm ξ
  mul_smul := by
    intro ⟨n, s⟩ ⟨m, t⟩ ⟨j, ξ⟩
    apply Sigma.ext (show ((n + m : ℕ) : ℤ) + j = (n : ℤ) + ((m : ℤ) + j) by push_cast; ring)
    have hdeg : (n : ℤ) + ((m : ℤ) + j) = ((n + m : ℕ) : ℤ) + j := by push_cast; ring
    refine HEq.trans (heq_of_eq (congrArg (fun z => act X L F p U ((n + m : ℕ) : ℤ) j z ξ)
      ((chosenRingStructure (sectionSiteRing X) (sectionSiteSheaf X) L).mul_eq n m s t))) ?_
    refine HEq.trans (heq_of_eq (congrArg (fun φ => (Hfunctor X.ringCatSheaf U p).map φ ξ)
      (actionOf_sectionRingMul (sectionSiteRing X) (sectionSiteSheaf X) L F n m j s t hdeg))) ?_
    refine HEq.trans (heq_of_eq ?_) (map_reindexTwist_heq X L F p U hdeg
      (act X L F p U (n : ℤ) ((m : ℤ) + j) s (act X L F p U (m : ℤ) j t ξ)))
    exact (map_comp_apply X.ringCatSheaf p U _ _ ξ).trans
      (map_comp_apply X.ringCatSheaf p U _ _
        ((Hfunctor X.ringCatSheaf U p).map
          (actionOf (sectionSiteRing X) (sectionSiteSheaf X) L F (m : ℤ) j t) ξ))
  smul_add := by
    intro n j s ξ η
    exact map_add _ _ _
  smul_zero := by
    intro n j s
    exact map_zero _
  add_smul := by
    intro n j s s' ξ
    exact act_add X L F p U (n : ℤ) j s s' ξ
  zero_smul := by
    intro n j ξ
    exact act_zero X L F p U (n : ℤ) j ξ

attribute [local instance] gmodule

/-- **The twisted cohomology is a module over the graded section ring `Γ_*(X, ℒ)`.** -/
instance instModule (F : X.Modules) (p : ℕ) (U : X.Opens) :
    Module (sectionRing (sectionSiteRing X) (sectionSiteSheaf X) L)
      (twistedCohomologyModule X L F p U) :=
  DirectSum.Gmodule.module _ _

/-- **The action on homogeneous elements is the map induced on cohomology by multiplication by
the section.** -/
theorem of_smul_of (F : X.Modules) (p : ℕ) (U : X.Opens) (n : ℕ) (j : ℤ)
    (s : sectionPiece X L n) (ξ : gradedPiece X L F p U j) :
    (DirectSum.of _ n s : sectionRing (sectionSiteRing X) (sectionSiteSheaf X) L) •
        (DirectSum.of _ j ξ : twistedCohomologyModule X L F p U) =
      DirectSum.of _ ((n : ℤ) + j) (act X L F p U (n : ℤ) j s ξ) :=
  DirectSum.Gmodule.of_smul_of _ _ s ξ

/-- The degree-`j` homogeneous component of `H^p_*(U, ℒ, ℱ)`, as an additive subgroup of the
direct sum. -/
@[ega "III 2.1.1" "Bidegree (m", sga "2 XII 1.3" "partial"]
def grading (F : X.Modules) (p : ℕ) (U : X.Opens) (j : ℤ) :
    AddSubgroup (twistedCohomologyModule X L F p U) :=
  (DirectSum.of _ j).range

/-- The twisted cohomology module is internally graded by its homogeneous summands. -/
instance instDecomposition (F : X.Modules) (p : ℕ) (U : X.Opens) :
    DirectSum.Decomposition (grading X L F p U) :=
  directSumComponentDecomposition _

/-- **The action adds the degrees**, which is the compatibility of the two internal gradings
that `GradedModuleDegreeZeroLocalization` requires. -/
instance instGradedSMul (F : X.Modules) (p : ℕ) (U : X.Opens) :
    SetLike.GradedSMul (sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L)
      (grading X L F p U) where
  smul_mem := by
    intro n j s ξ hs hξ
    obtain ⟨s, rfl⟩ := hs
    obtain ⟨ξ, rfl⟩ := hξ
    exact ⟨act X L F p U (n : ℤ) j s ξ, (of_smul_of X L F p U n j s ξ).symm⟩

/-- **The degree-zero localization `H^p_*(U, ℒ, ℱ)₍s₎` of the twisted cohomology at a global
section `s` of `ℒ`**, the submodule of the localization away from `s` spanned by the fractions
whose numerator and denominator have equal degree. This is the source of the comparison map of
[Stacks, Tag 09MR]; it is this type that could not be formed before the module structure
above. -/
abbrev degreeZeroLocalization (F : X.Modules) (p : ℕ) (U : X.Opens)
    (s : sectionRing (sectionSiteRing X) (sectionSiteSheaf X) L) :=
  GradedModuleDegreeZeroLocalization
    (sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L) (grading X L F p U) s

end Stacks.Cohomology.TwistedGradedModule

end
