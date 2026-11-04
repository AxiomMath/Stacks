module

public import StacksFrontier.RingTheory.NaiveCotangent.FormallySmoothExtensionQuasiIso
public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentPresentationQuasiIso
public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentTrivialPresentation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The naive cotangent complex of a formally smooth presentation

Let `R ⟶ A ⟶ B` be morphisms of sheaves of commutative rings on a topological space with
`A ⟶ B` locally surjective, so that `A` *presents* `B` over `R`, and write `I` for the kernel of
`A ⟶ B`.  This file compares `NL_{B/R}` with the two-term complex

`(I/I² ⟶ B ⊗_A Ω[A/R])`

— the conormal sequence of [Stacks Project, Tag 08TS] placed in degrees `-1` and `0` — and proves
that the canonical comparison is a quasi-isomorphism as soon as `A` is **formally smooth over
`R` at every stalk**.

This is the sheaf-theoretic core of [Stacks Project, Tag 0FV4], whose geometric instance takes
`R ⟶ A ⟶ B` to be `f^{-1}𝒪_Y ⟶ i^{-1}𝒪_P ⟶ 𝒪_X` for a morphism `f : X ⟶ Y` factored as
`f = g ∘ i` with `i` an immersion and `g` formally smooth.  The tag itself is **not** proved here.

## Main definitions

* `Stacks.SheafOfModules.towerNaiveCotangentComplex`: the two-term complex
  `(I/I² ⟶ B ⊗_A Ω[A/R])`.
* `Stacks.SheafOfModules.towerFacComparison`: the chain map of two-term complexes induced by a
  factorisation `ψ ≫ φ₂ = φ₁` of one presentation of `B` over `R` through another.
* `Stacks.SheafOfModules.towerGenerators` and `Stacks.SheafOfModules.towerPresentationMap`: the
  family of generators of `B` over `R` given by the sections of `A`, and the resulting polynomial
  presentation `R[A] ⟶ B`.
* `Stacks.SheafOfModules.towerPresentationComparison`: `towerFacComparison` at the factorisation
  of `R[A] ⟶ B` through `A`, a chain map `NL(R[A] ⟶ B) ⟶ (I/I² ⟶ B ⊗_A Ω[A/R])`.

## Main results

* `Stacks.SheafOfModules.quasiIso_towerFacComparison`: the comparison attached to a factorisation
  is a quasi-isomorphism as soon as both presenting rings are formally smooth over `R` at every
  stalk.
* `Stacks.SheafOfModules.formallySmooth_stalk_freeAlgebraSheaf`: the stalk of a free algebra sheaf
  is formally smooth over the stalk of its coefficients, which discharges that hypothesis for the
  polynomial presentation.
* `Stacks.SheafOfModules.quasiIso_towerPresentationComparison`: consequently, for `A` formally
  smooth over `R` at every stalk, `NL(R[A] ⟶ B) ⟶ (I/I² ⟶ B ⊗_A Ω[A/R])` is a
  quasi-isomorphism.  Together with [Stacks Project, Tag 08TL]
  (`Stacks.SheafOfModules.quasiIso_naiveCotangentComplexComparison`), which identifies
  `NL(R[A] ⟶ B)` with `NL_{B/R}` unconditionally, this identifies `NL_{B/R}` with
  `(I/I² ⟶ B ⊗_A Ω[A/R])` in the derived category of sheaves of `B`-modules.

## Route

The two presentations of `B` over `R` in play are `A ⟶ B` itself and the *polynomial* one
`R[A] ⟶ B` on the presheaf of sets underlying `A`.  The point of taking the sections of `A` as
the generating family is that the evaluation `R[A] ⟶ A` — the canonical presentation of `A` over
`R` — is then available with no choices, so the factorisation needed to compare the two
conormal sequences exists globally.  A set-theoretic section of `A ⟶ B` would not.

`Stacks.Sites.Conormal.conormalSheafMapOfFac` and `...tensorSheafMapOfFac` are the two maps that
a factorisation induces on the terms of the conormal sequence, and
`Stacks.Sites.Conormal.conormalSequence_f_naturality` is the square they fit in; together they
give the chain map.  Quasi-isomorphy is stalkwise ([Stacks Project, Tag 01AG]), and at a point
`x` both stalk complexes are naive cotangent complexes of extensions of `Bₓ` over `Rₓ`, the
chain map between them being the one induced by the morphism of extensions
`Stacks.Sites.Conormal.stalkExtensionHom`: that is
`Stacks.SheafOfModules.conormalSheafMapOfFacStalk_eq_cotangentMap` and
`...tensorSheafMapOfFacStalk_eq_cotangentSpaceMap`, with
`...conormalSequenceStalkMapF_eq_cotangentComplex'` for the differentials.  The presenting ring
of the first extension is `Rₓ[Aₓ]`, a polynomial algebra, hence formally smooth; that of the
second is `Aₓ`, formally smooth by hypothesis.  So
`NaiveCotangent.nlExtensionMap_isQuasiIso_of_formallySmooth` applies.

Unlike [Stacks Project, Tag 08TL], which compares two *polynomial* presentations and has a
morphism of extensions in both directions at each stalk, here only one direction exists: a
morphism `Aₓ ⟶ Rₓ[Aₓ]` of extensions of `Bₓ` would lift `Aₓ ⟶ Bₓ` along `Rₓ[Aₓ] ⟶ Bₓ`, whose
kernel is not nilpotent.  Formal smoothness replaces it.

## References

* [Stacks Project, Tag 08TS](https://stacks.math.columbia.edu/tag/08TS), the conormal sequence.
* [Stacks Project, Tag 08TL](https://stacks.math.columbia.edu/tag/08TL), the comparison of a
  presentation with the canonical one.
* [Stacks Project, Tag 0FV4](https://stacks.math.columbia.edu/tag/0FV4), the geometric statement
  this is the sheaf-theoretic core of.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal
open AlgebraicGeometry.SheafOfModules (stalkFunctor)
open Stacks.RelativeDifferentialStalk (algebraStalk)

universe u

noncomputable section

namespace Stacks.SheafOfModules

variable {T : TopCat.{u}} (R A B : CategoryTheory.Sheaf (Opens.grothendieckTopology T)
    CommRingCat.{u}) (a : R ⟶ A) (φ : A ⟶ B)
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology T) φ.hom]

/-! ### The two-term complex of the conormal sequence of a presentation -/

/-- **The two-term complex of a presentation.**  For a tower `R ⟶ A ⟶ B` of sheaves of
commutative rings with `A ⟶ B` locally surjective and kernel `I`, this is the complex
`(I/I² ⟶ B ⊗_A Ω[A/R])` with the conormal sheaf in degree `-1`: the first arrow of the conormal
sequence of [Stacks Project, Tag 08TS], doubled.

For `A = R[E]` a free algebra this is `Stacks.SheafOfModules.presentationNaiveCotangentComplex`,
and for `A = R` it is `Stacks.SheafOfModules.trivialNaiveCotangentComplex`; neither covers the
case the geometric application needs, where `A` is formally smooth over `R` but neither free nor
equal to `R`. -/
@[sga "6 0 4.4" "more general"]
def towerNaiveCotangentComplex :
    CochainComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := Opens.grothendieckTopology T) B)) ℤ := by
  have : HasZeroObject (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := Opens.grothendieckTopology T) B)) :=
    hasZeroObject_of_hasTerminal_object
  exact HomologicalComplex.double
    (Stacks.Sites.Conormal.conormalSequence.{u, u, u, u}
      (Opens.grothendieckTopology T) R A B a φ).f
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide)

/-- The conormal sheaf `I/I²` is the degree `-1` term. -/
theorem towerNaiveCotangentComplex_X_negOne :
    (towerNaiveCotangentComplex R A B a φ).X (-1) =
      (Stacks.Sites.Conormal.conormalSequence.{u, u, u, u}
        (Opens.grothendieckTopology T) R A B a φ).X₁ := by
  simp [towerNaiveCotangentComplex, HomologicalComplex.double]

/-- The sheaf `B ⊗_A Ω[A/R]` is the degree `0` term. -/
theorem towerNaiveCotangentComplex_X_zero :
    (towerNaiveCotangentComplex R A B a φ).X 0 =
      (Stacks.Sites.Conormal.conormalSequence.{u, u, u, u}
        (Opens.grothendieckTopology T) R A B a φ).X₂ := by
  simp [towerNaiveCotangentComplex, HomologicalComplex.double]

/-- The complex has no terms outside degrees `-1` and `0`. -/
theorem towerNaiveCotangentComplex_isZero_X (i : ℤ) (hneg : i ≠ -1) (hzero : i ≠ 0) :
    IsZero ((towerNaiveCotangentComplex R A B a φ).X i) := by
  have : HasZeroObject (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := Opens.grothendieckTopology T) B)) :=
    hasZeroObject_of_hasTerminal_object
  show IsZero ((HomologicalComplex.double
    (Stacks.Sites.Conormal.conormalSequence.{u, u, u, u}
      (Opens.grothendieckTopology T) R A B a φ).f
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide)).X i)
  exact HomologicalComplex.isZero_double_X _ _ i hneg hzero

/-- The complex has no differential out of degree `0`. -/
theorem towerNaiveCotangentComplex_d_zero (k : ℤ) :
    (towerNaiveCotangentComplex R A B a φ).d 0 k = 0 := by
  have : HasZeroObject (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := Opens.grothendieckTopology T) B)) :=
    hasZeroObject_of_hasTerminal_object
  show (HomologicalComplex.double
    (Stacks.Sites.Conormal.conormalSequence.{u, u, u, u}
      (Opens.grothendieckTopology T) R A B a φ).f
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide)).d 0 k = 0
  exact HomologicalComplex.double_d_eq_zero₀ _ _ 0 k (by decide)

/-- The only nonzero differential is the first arrow of the conormal sequence. -/
theorem towerNaiveCotangentComplex_d_negOne_zero :
    (towerNaiveCotangentComplex R A B a φ).d (-1) 0 =
      eqToHom (towerNaiveCotangentComplex_X_negOne R A B a φ) ≫
        (Stacks.Sites.Conormal.conormalSequence.{u, u, u, u}
          (Opens.grothendieckTopology T) R A B a φ).f ≫
        eqToHom (towerNaiveCotangentComplex_X_zero R A B a φ).symm := by
  have : HasZeroObject (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := Opens.grothendieckTopology T) B)) :=
    hasZeroObject_of_hasTerminal_object
  show (HomologicalComplex.double
    (Stacks.Sites.Conormal.conormalSequence.{u, u, u, u}
      (Opens.grothendieckTopology T) R A B a φ).f
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide)).d (-1) 0 = _
  rw [HomologicalComplex.double_d _ _ (by decide)]
  rfl

/-! ### The comparison attached to a factorisation of one presentation through another -/

section Fac

variable (A₁ A₂ : CategoryTheory.Sheaf (Opens.grothendieckTopology T) CommRingCat.{u})
  (a₁ : R ⟶ A₁) (a₂ : R ⟶ A₂) (φ₁ : A₁ ⟶ B) (φ₂ : A₂ ⟶ B) (ψ : A₁ ⟶ A₂)
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology T) φ₁.hom]
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology T) φ₂.hom]
  (hψ : ψ ≫ φ₂ = φ₁) (ha : a₁ ≫ ψ = a₂)

/-- The degree `-1` component of the comparison: the map of conormal sheaves induced by a
factorisation `ψ ≫ φ₂ = φ₁` of one presentation of `B` through another. -/
def towerFacConormalMap :=
  Stacks.Sites.Conormal.conormalSheafMapOfFac.{u, u, u, u} (Opens.grothendieckTopology T) B
    A₁ A₂ φ₁ φ₂ ψ hψ

/-- The degree `0` component of the comparison. -/
def towerFacTensorMap :=
  Stacks.Sites.Conormal.tensorSheafMapOfFac.{u, u, u, u} (Opens.grothendieckTopology T) R B
    A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha

/-- The square expressing that the two induced maps commute with the two differentials. -/
theorem towerFacConormalMap_comm :
    (towerFacConormalMap B A₁ A₂ φ₁ φ₂ ψ hψ ≫
          eqToHom (towerNaiveCotangentComplex_X_negOne R A₂ B a₂ φ₂).symm) ≫
        (towerNaiveCotangentComplex R A₂ B a₂ φ₂).d (-1) 0 =
      (Stacks.Sites.Conormal.conormalSequence.{u, u, u, u}
          (Opens.grothendieckTopology T) R A₁ B a₁ φ₁).f ≫
        (towerFacTensorMap R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha ≫
          eqToHom (towerNaiveCotangentComplex_X_zero R A₂ B a₂ φ₂).symm) := by
  rw [towerNaiveCotangentComplex_d_negOne_zero]
  exact CategoryTheory.eqToHom_comm_of_naturality
    (towerNaiveCotangentComplex_X_negOne R A₂ B a₂ φ₂)
    (towerNaiveCotangentComplex_X_zero R A₂ B a₂ φ₂) _ _ _ _
    (Stacks.Sites.Conormal.conormalSequence_f_naturality.{u, u, u, u}
      (Opens.grothendieckTopology T) R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha)

/-- The degree `0` component is killed by every differential out of degree `0`, the target
complex having none. -/
theorem towerFacTensorMap_comp_d (k : ℤ) :
    (towerFacTensorMap R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha ≫
          eqToHom (towerNaiveCotangentComplex_X_zero R A₂ B a₂ φ₂).symm) ≫
        (towerNaiveCotangentComplex R A₂ B a₂ φ₂).d 0 k = 0 := by
  rw [towerNaiveCotangentComplex_d_zero, Limits.comp_zero]

/-- **The chain map of two-term complexes induced by a factorisation of one presentation of `B`
over `R` through another.** -/
def towerFacComparison :
    towerNaiveCotangentComplex R A₁ B a₁ φ₁ ⟶ towerNaiveCotangentComplex R A₂ B a₂ φ₂ := by
  have : HasZeroObject (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := Opens.grothendieckTopology T) B)) :=
    hasZeroObject_of_hasTerminal_object
  exact HomologicalComplex.mkHomFromDouble
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide)
    (towerFacConormalMap B A₁ A₂ φ₁ φ₂ ψ hψ ≫
      eqToHom (towerNaiveCotangentComplex_X_negOne R A₂ B a₂ φ₂).symm)
    (towerFacTensorMap R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha ≫
      eqToHom (towerNaiveCotangentComplex_X_zero R A₂ B a₂ φ₂).symm)
    (towerFacConormalMap_comm R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha)
    (fun k _ ↦ towerFacTensorMap_comp_d R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha k)

/-- In degree `-1` the comparison is the map of conormal sheaves. -/
theorem towerFacComparison_f_negOne :
    (towerFacComparison R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha).f (-1) =
      eqToHom (towerNaiveCotangentComplex_X_negOne R A₁ B a₁ φ₁) ≫
        towerFacConormalMap B A₁ A₂ φ₁ φ₂ ψ hψ ≫
        eqToHom (towerNaiveCotangentComplex_X_negOne R A₂ B a₂ φ₂).symm := by
  have : HasZeroObject (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := Opens.grothendieckTopology T) B)) :=
    hasZeroObject_of_hasTerminal_object
  exact HomologicalComplex.mkHomFromDouble_f₀
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide) _ _
    (towerFacConormalMap_comm R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha)
    (fun k _ ↦ towerFacTensorMap_comp_d R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha k)

/-- In degree `0` the comparison is the map of the tensor terms. -/
theorem towerFacComparison_f_zero :
    (towerFacComparison R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha).f 0 =
      eqToHom (towerNaiveCotangentComplex_X_zero R A₁ B a₁ φ₁) ≫
        towerFacTensorMap R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha ≫
        eqToHom (towerNaiveCotangentComplex_X_zero R A₂ B a₂ φ₂).symm := by
  have : HasZeroObject (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := Opens.grothendieckTopology T) B)) :=
    hasZeroObject_of_hasTerminal_object
  exact HomologicalComplex.mkHomFromDouble_f₁
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide) _ _
    (towerFacConormalMap_comm R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha)
    (fun k _ ↦ towerFacTensorMap_comp_d R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha k)

/-! #### The two components, unfolded -/

/-- The degree `-1` component is the map of conormal sheaves of the factorisation. -/
theorem towerFacConormalMap_eq :
    towerFacConormalMap B A₁ A₂ φ₁ φ₂ ψ hψ =
      Stacks.Sites.Conormal.conormalSheafMapOfFac.{u, u, u, u} (Opens.grothendieckTopology T) B
        A₁ A₂ φ₁ φ₂ ψ hψ :=
  rfl

/-- The degree `0` component is the map of the tensor terms of the factorisation. -/
theorem towerFacTensorMap_eq :
    towerFacTensorMap R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha =
      Stacks.Sites.Conormal.tensorSheafMapOfFac.{u, u, u, u} (Opens.grothendieckTopology T) R B
        A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha :=
  rfl

/-! #### Quasi-isomorphy from formal smoothness of the two presenting rings -/

/-- **The comparison of two presentations is a quasi-isomorphism when both presenting rings are
formally smooth at every stalk.**  For a tower `R ⟶ A₁ ⟶ B` and `R ⟶ A₂ ⟶ B` of sheaves of
commutative rings with both maps onto `B` locally surjective, and a factorisation
`ψ ≫ φ₂ = φ₁` over `R`, the induced chain map

`(I₁/I₁² ⟶ B ⊗_{A₁} Ω[A₁/R]) ⟶ (I₂/I₂² ⟶ B ⊗_{A₂} Ω[A₂/R])`

is a quasi-isomorphism as soon as `A₁` and `A₂` are formally smooth over `R` at every stalk.

Quasi-isomorphy is stalkwise; at a point the two complexes are the naive cotangent complexes of
`Stacks.Sites.Conormal.stalkExtension` and the chain map between them is the one induced by
`Stacks.Sites.Conormal.stalkExtensionHom`, so
`NaiveCotangent.nlExtensionMap_isQuasiIso_of_formallySmooth` applies. -/
theorem quasiIso_towerFacComparison
    (hfs₁ : ∀ x : T, letI := algebraStalk a₁.hom x
      Algebra.FormallySmooth (ToType (TopCat.Presheaf.stalk R.obj x))
        (ToType (TopCat.Presheaf.stalk A₁.obj x)))
    (hfs₂ : ∀ x : T, letI := algebraStalk a₂.hom x
      Algebra.FormallySmooth (ToType (TopCat.Presheaf.stalk R.obj x))
        (ToType (TopCat.Presheaf.stalk A₂.obj x))) :
    QuasiIso (towerFacComparison R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha) := by
  refine (AlgebraicGeometry.SheafOfModules.quasiIso_iff_forall_stalk_quasiIso _ _).mpr fun x ↦ ?_
  let _ : DecidableEq (OrderDual (TopologicalSpace.OpenNhds x)) := Classical.decEq _
  have hc₁ : a₁ ≫ φ₁ = a₁ ≫ φ₁ := rfl
  have hc₂ : a₂ ≫ φ₂ = a₁ ≫ φ₁ := by rw [← ha, Category.assoc, hψ]
  let := Stacks.Sites.Conormal.stalkAlgebraBase R B (a₁ ≫ φ₁) x
  let u₁ := (Stacks.Sites.Conormal.conormalSheafStalkLinearEquiv A₁ B φ₁ x).toAddEquiv
  let u₀ := (Stacks.Sites.Conormal.cotangentSpaceStalkLinearEquiv R A₁ B a₁ φ₁ x).toAddEquiv
  let v₁ := (Stacks.Sites.Conormal.conormalSheafStalkLinearEquiv A₂ B φ₂ x).toAddEquiv
  let v₀ := (Stacks.Sites.Conormal.cotangentSpaceStalkLinearEquiv R A₂ B a₂ φ₂ x).toAddEquiv
  have : Algebra.FormallySmooth (ToType (TopCat.Presheaf.stalk R.obj x))
      (Stacks.Sites.Conormal.stalkExtension R A₁ B a₁ φ₁ (a₁ ≫ φ₁) x hc₁).Ring := hfs₁ x
  have : Algebra.FormallySmooth (ToType (TopCat.Presheaf.stalk R.obj x))
      (Stacks.Sites.Conormal.stalkExtension R A₂ B a₂ φ₂ (a₁ ≫ φ₁) x hc₂).Ring := hfs₂ x
  have hqi := NaiveCotangent.nlExtensionMap_isQuasiIso_of_formallySmooth
    (Stacks.Sites.Conormal.stalkExtensionHom R A₁ A₂ B a₁ a₂ φ₁ φ₂ (a₁ ≫ φ₁) ψ x hc₁ hc₂ ha hψ)
  have hdK := conormalSequenceStalkMapF_eq_cotangentComplex' R A₁ B a₁ φ₁ x (a₁ ≫ φ₁) hc₁
  have hdL := conormalSequenceStalkMapF_eq_cotangentComplex' R A₂ B a₂ φ₂ x (a₁ ≫ φ₁) hc₂
  have hpc := conormalSheafMapOfFacStalk_eq_cotangentMap R A₁ A₂ B a₁ a₂ φ₁ φ₂ ψ x hψ ha
    (a₁ ≫ φ₁) hc₁ hc₂
  have hpt := tensorSheafMapOfFacStalk_eq_cotangentSpaceMap R A₁ A₂ B a₁ a₂ φ₁ φ₂ ψ x hψ ha
    (a₁ ≫ φ₁) hc₁ hc₂
  refine CochainComplex.quasiIso_of_isZero_X_of_eqToHom _ ?_ ?_
    ((AlgebraicGeometry.SheafOfModules.stalkFunctor _ x).map
      (Stacks.Sites.Conormal.conormalSequence.{u, u, u, u}
        (Opens.grothendieckTopology T) R A₁ B a₁ φ₁).f)
    ((AlgebraicGeometry.SheafOfModules.stalkFunctor _ x).map
      (Stacks.Sites.Conormal.conormalSequence.{u, u, u, u}
        (Opens.grothendieckTopology T) R A₂ B a₂ φ₂).f)
    ((AlgebraicGeometry.SheafOfModules.stalkFunctor _ x).map
      (Stacks.Sites.Conormal.conormalSheafMapOfFac.{u, u, u, u}
        (Opens.grothendieckTopology T) B A₁ A₂ φ₁ φ₂ ψ hψ))
    ((AlgebraicGeometry.SheafOfModules.stalkFunctor _ x).map
      (Stacks.Sites.Conormal.tensorSheafMapOfFac.{u, u, u, u}
        (Opens.grothendieckTopology T) R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i h1 h2
    rw [Functor.mapHomologicalComplex_obj_X]
    exact AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj _ x _
      (towerNaiveCotangentComplex_isZero_X R A₁ B a₁ φ₁ i h1 h2)
  · intro i h1 h2
    rw [Functor.mapHomologicalComplex_obj_X]
    exact AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj _ x _
      (towerNaiveCotangentComplex_isZero_X R A₂ B a₂ φ₂ i h1 h2)
  · exact congrArg (AlgebraicGeometry.SheafOfModules.stalkFunctor _ x).obj
      (towerNaiveCotangentComplex_X_negOne R A₁ B a₁ φ₁)
  · exact congrArg (AlgebraicGeometry.SheafOfModules.stalkFunctor _ x).obj
      (towerNaiveCotangentComplex_X_zero R A₁ B a₁ φ₁)
  · exact congrArg (AlgebraicGeometry.SheafOfModules.stalkFunctor _ x).obj
      (towerNaiveCotangentComplex_X_negOne R A₂ B a₂ φ₂)
  · exact congrArg (AlgebraicGeometry.SheafOfModules.stalkFunctor _ x).obj
      (towerNaiveCotangentComplex_X_zero R A₂ B a₂ φ₂)
  · refine (Functor.mapHomologicalComplex_obj_d _ _ _ _ _).trans
      ((congrArg (AlgebraicGeometry.SheafOfModules.stalkFunctor _ x).map
        (towerNaiveCotangentComplex_d_negOne_zero R A₁ B a₁ φ₁)).trans
        (Functor.map_eqToHom_comp_comp_eqToHom _
          (towerNaiveCotangentComplex_X_negOne R A₁ B a₁ φ₁) _
          (towerNaiveCotangentComplex_X_zero R A₁ B a₁ φ₁)))
  · refine (Functor.mapHomologicalComplex_obj_d _ _ _ _ _).trans
      ((congrArg (AlgebraicGeometry.SheafOfModules.stalkFunctor _ x).map
        (towerNaiveCotangentComplex_d_negOne_zero R A₂ B a₂ φ₂)).trans
        (Functor.map_eqToHom_comp_comp_eqToHom _
          (towerNaiveCotangentComplex_X_negOne R A₂ B a₂ φ₂) _
          (towerNaiveCotangentComplex_X_zero R A₂ B a₂ φ₂)))
  · refine (Functor.mapHomologicalComplex_map_f _ _ _ _).trans
      ((congrArg (AlgebraicGeometry.SheafOfModules.stalkFunctor _ x).map
        ((towerFacComparison_f_negOne R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha).trans
          (congrArg (fun t ↦ eqToHom (towerNaiveCotangentComplex_X_negOne R A₁ B a₁ φ₁) ≫
            t ≫ eqToHom (towerNaiveCotangentComplex_X_negOne R A₂ B a₂ φ₂).symm)
            (towerFacConormalMap_eq B A₁ A₂ φ₁ φ₂ ψ hψ)))).trans
        (Functor.map_eqToHom_comp_comp_eqToHom _
          (towerNaiveCotangentComplex_X_negOne R A₁ B a₁ φ₁) _
          (towerNaiveCotangentComplex_X_negOne R A₂ B a₂ φ₂)))
  · refine (Functor.mapHomologicalComplex_map_f _ _ _ _).trans
      ((congrArg (AlgebraicGeometry.SheafOfModules.stalkFunctor _ x).map
        ((towerFacComparison_f_zero R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha).trans
          (congrArg (fun t ↦ eqToHom (towerNaiveCotangentComplex_X_zero R A₁ B a₁ φ₁) ≫
            t ≫ eqToHom (towerNaiveCotangentComplex_X_zero R A₂ B a₂ φ₂).symm)
            (towerFacTensorMap_eq R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha)))).trans
        (Functor.map_eqToHom_comp_comp_eqToHom _
          (towerNaiveCotangentComplex_X_zero R A₁ B a₁ φ₁) _
          (towerNaiveCotangentComplex_X_zero R A₂ B a₂ φ₂)))
  · exact CochainComplex.eq_zero_of_d_eq_zero_of_addEquiv (u₁ := u₁) (u₀ := u₀) (v₁ := v₁)
      hdK hpc hqi.eq_zero_of_d_eq_zero
  · exact CochainComplex.exists_of_d_eq_zero_of_addEquiv (u₁ := u₁) (u₀ := u₀) (v₁ := v₁)
      (v₀ := v₀) hdK hdL hpc hqi.exists_of_d_eq_zero
  · exact CochainComplex.exists_d_eq_of_addEquiv (u₁ := u₁) (u₀ := u₀) (v₁ := v₁) (v₀ := v₀)
      hdK hdL hpt hqi.exists_d_eq
  · exact CochainComplex.exists_add_d_eq_of_addEquiv (u₀ := u₀) (v₁ := v₁) (v₀ := v₀)
      hdL hpt hqi.exists_add_d_eq

end Fac

/-! ### The polynomial presentation on the sections of `A` -/

/-- **The stalk of a free algebra sheaf is formally smooth over the stalk of the coefficients.**
It is a polynomial algebra, `Stacks.Sites.FreeAlgebra.freeAlgebraSheafStalkRingEquiv` carrying it
to `Rₓ[Eₓ]` compatibly with the coefficient inclusion. -/
theorem formallySmooth_stalk_freeAlgebraSheaf (E : Functor (Opens T)ᵒᵖ (Type u)) (x : T) :
    letI := algebraStalk (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology T) R E).hom x
    Algebra.FormallySmooth (ToType (TopCat.Presheaf.stalk R.obj x))
      (ToType (TopCat.Presheaf.stalk
        (freeAlgebraSheaf (Opens.grothendieckTopology T) R E).obj x)) := by
  let := algebraStalk (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology T) R E).hom x
  refine Algebra.FormallySmooth.of_equiv
    (A := MvPolynomial _ (ToType (TopCat.Presheaf.stalk R.obj x))) (AlgEquiv.ofRingEquiv
      (f := (Stacks.Sites.FreeAlgebra.freeAlgebraSheafStalkRingEquiv R E x).symm) fun r ↦ ?_)
  refine (Stacks.Sites.FreeAlgebra.freeAlgebraSheafStalkRingEquiv R E x).injective ?_
  rw [RingEquiv.apply_symm_apply]
  exact (Stacks.Sites.FreeAlgebra.freeAlgebraSheafStalkRingEquiv_coefficientMap R E x r).symm

/-- The family of generators of `B` over `R` given by the sections of `A`: the morphism of
presheaves of sets underlying `φ`. -/
abbrev towerGenerators : underlyingPresheaf (Opens.grothendieckTopology T) A ⟶
    underlyingPresheaf (Opens.grothendieckTopology T) B :=
  Functor.whiskerRight φ.hom (forget CommRingCat.{u})

/-- **The polynomial presentation of `B` on the sections of `A` factors through `A`.**
Evaluating a polynomial with coefficients in `R` at sections of `A` and then applying `φ` is the
same as evaluating it at the images of those sections: both morphisms out of the free algebra
agree on coefficients and on variables. -/
theorem canonicalPresentation_comp_eq_presentation :
    canonicalPresentation (Opens.grothendieckTopology T) R A a ≫ φ =
      presentation (Opens.grothendieckTopology T) R B (a ≫ φ)
        (underlyingPresheaf (Opens.grothendieckTopology T) A) (towerGenerators A B φ) := by
  refine freeAlgebraSheaf_hom_ext (Opens.grothendieckTopology T) R B
    (underlyingPresheaf (Opens.grothendieckTopology T) A) ?_ ?_
  · rw [← Category.assoc, canonicalPresentation_comp_coefficientMap, presentation,
      freeAlgebraSheafCoefficientMap_comp_desc]
  · rw [presentation, freeAlgebraSheafVariable_comp_desc (Opens.grothendieckTopology T) R B
        (underlyingPresheaf (Opens.grothendieckTopology T) A) (a ≫ φ) (towerGenerators A B φ),
      Functor.map_comp, Functor.whiskerRight_comp, ← Category.assoc,
      canonicalPresentation_eq_desc, freeAlgebraSheafVariable_comp_desc
        (Opens.grothendieckTopology T) R A
        (underlyingPresheaf (Opens.grothendieckTopology T) A) a (𝟙 _), Category.id_comp]
    rfl

/-- The polynomial presentation of `B` over `R` on the sections of `A` is locally surjective. -/
instance isLocallySurjective_presentation_towerGenerators :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology T)
      (presentation (Opens.grothendieckTopology T) R B (a ≫ φ)
        (underlyingPresheaf (Opens.grothendieckTopology T) A) (towerGenerators A B φ)).hom := by
  have hcan : Presheaf.IsLocallySurjective (Opens.grothendieckTopology T)
      (canonicalPresentation (Opens.grothendieckTopology T) R A a).hom :=
    canonicalPresentation_isLocallySurjective (Opens.grothendieckTopology T) R A a
  rw [← canonicalPresentation_comp_eq_presentation R A B a φ]
  exact inferInstanceAs (Presheaf.IsLocallySurjective (Opens.grothendieckTopology T)
    ((canonicalPresentation (Opens.grothendieckTopology T) R A a).hom ≫ φ.hom))

/-- **`NL(R[A] ⟶ B)` is the two-term complex of the presentation `R[A] ⟶ B`.**  Both are the
conormal sequence of that presentation, doubled. -/
theorem presentationNaiveCotangentComplex_eq_tower :
    presentationNaiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) R B (a ≫ φ)
        (underlyingPresheaf (Opens.grothendieckTopology T) A) (towerGenerators A B φ) =
      towerNaiveCotangentComplex R
        (freeAlgebraSheaf (Opens.grothendieckTopology T) R
          (underlyingPresheaf (Opens.grothendieckTopology T) A)) B
        (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology T) R
          (underlyingPresheaf (Opens.grothendieckTopology T) A))
        (presentation (Opens.grothendieckTopology T) R B (a ≫ φ)
          (underlyingPresheaf (Opens.grothendieckTopology T) A) (towerGenerators A B φ)) :=
  rfl

/-- **The comparison `NL(R[A] ⟶ B) ⟶ (I/I² ⟶ B ⊗_A Ω[A/R])`.**  It is the chain map of the
factorisation of the polynomial presentation on the sections of `A` through `A` itself. -/
def towerPresentationComparison :
    towerNaiveCotangentComplex R
        (freeAlgebraSheaf (Opens.grothendieckTopology T) R
          (underlyingPresheaf (Opens.grothendieckTopology T) A)) B
        (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology T) R
          (underlyingPresheaf (Opens.grothendieckTopology T) A))
        (presentation (Opens.grothendieckTopology T) R B (a ≫ φ)
          (underlyingPresheaf (Opens.grothendieckTopology T) A) (towerGenerators A B φ)) ⟶
      towerNaiveCotangentComplex R A B a φ :=
  towerFacComparison R B
    (freeAlgebraSheaf (Opens.grothendieckTopology T) R
      (underlyingPresheaf (Opens.grothendieckTopology T) A)) A
    (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology T) R
      (underlyingPresheaf (Opens.grothendieckTopology T) A)) a
    (presentation (Opens.grothendieckTopology T) R B (a ≫ φ)
      (underlyingPresheaf (Opens.grothendieckTopology T) A) (towerGenerators A B φ)) φ
    (canonicalPresentation (Opens.grothendieckTopology T) R A a)
    (canonicalPresentation_comp_eq_presentation R A B a φ)
    (canonicalPresentation_comp_coefficientMap (Opens.grothendieckTopology T) R A a)

/-- **The comparison `NL(R[A] ⟶ B) ⟶ (I/I² ⟶ B ⊗_A Ω[A/R])` is a quasi-isomorphism when `A` is
formally smooth over `R` at every stalk.**

Together with [Stacks Project, Tag 08TL]
(`Stacks.SheafOfModules.quasiIso_naiveCotangentComplexComparison`), which identifies
`NL(R[A] ⟶ B)` with `NL_{B/R}`, this identifies `NL_{B/R}` with the two-term complex
`(I/I² ⟶ B ⊗_A Ω[A/R])` in the derived category of sheaves of `B`-modules. -/
theorem quasiIso_towerPresentationComparison
    (hfs : ∀ x : T, letI := algebraStalk a.hom x
      Algebra.FormallySmooth (ToType (TopCat.Presheaf.stalk R.obj x))
        (ToType (TopCat.Presheaf.stalk A.obj x))) :
    QuasiIso (towerPresentationComparison R A B a φ) :=
  quasiIso_towerFacComparison R B
    (freeAlgebraSheaf (Opens.grothendieckTopology T) R
      (underlyingPresheaf (Opens.grothendieckTopology T) A)) A
    (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology T) R
      (underlyingPresheaf (Opens.grothendieckTopology T) A)) a
    (presentation (Opens.grothendieckTopology T) R B (a ≫ φ)
      (underlyingPresheaf (Opens.grothendieckTopology T) A) (towerGenerators A B φ)) φ
    (canonicalPresentation (Opens.grothendieckTopology T) R A a)
    (canonicalPresentation_comp_eq_presentation R A B a φ)
    (canonicalPresentation_comp_coefficientMap (Opens.grothendieckTopology T) R A a)
    (fun x ↦ formallySmooth_stalk_freeAlgebraSheaf R
      (underlyingPresheaf (Opens.grothendieckTopology T) A) x) hfs

end Stacks.SheafOfModules

end

end
