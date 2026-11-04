module

public import StacksFrontier.AlgebraicGeometry.AmplePullback.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleProjectiveImmersion.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCharts
public import StacksFrontier.AlgebraicGeometry.HProjective.AffineBase
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Dimension.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.AmpleProjOpenImmersion
public import StacksFrontier.AlgebraicGeometry.SegreChartProduct.TargetCover
public import StacksFrontier.AlgebraicGeometry.TwistMapsInvertible.Absolute
public import StacksFrontier.AlgebraicGeometry.TwistFlatness.Polynomial
public import StacksFrontier.AlgebraicGeometry.AmpleAffineBaseTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistMono.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeAmpleImplications.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The hyperplane sheaf is ample on projective space

On `Proj S` for a graded ring `S` whose homogeneous elements of one positive degree `d` define
standard opens covering the whole space, the twist `𝒪(d)` is ample. For a polynomial ring the
variables are such a family in degree `d = 1`, so `𝒪(1)` is ample on `Proj R[T₀, …, Tₙ]`; and
since `ℙⁿ_S` is the base change of `ℙⁿ_ℤ` along the affine morphism `S ⟶ Spec ℤ` when `S` is
affine, `𝒪(1)` is ample on `ℙⁿ_S`.

The last statement is the opening step of the proof of [Stacks, Tag 01YS], and it proves the
hypothesis `Stacks.Tag01VT.TwistAmpleOverAffine`. That hypothesis carries no label of its own in
the source, so no `@[stacks]` attribute is attached below.

## Main results

* `Stacks.ProjectiveSpace.isAmple_twistingSheaf_of_commonDegreeCover`: **`𝒪(d)` is ample on
  `Proj S`** when `Proj S` is quasi-compact, `𝒪(d)` is invertible, and `Proj S` is covered by
  finitely many standard opens of one common degree `d`.
* `Stacks.ProjectiveSpace.commonDegreeCoverTop`: the variables of a polynomial ring in finitely
  many indeterminates are such a family, in degree one.
* `Stacks.ProjectiveSpace.compactSpace_proj_homogeneousSubmodule`: `Proj R[T₀, …, Tₙ]` is
  quasi-compact.
* `Stacks.ProjectiveSpace.isInvertibleModule_twistingSheaf_homogeneousSubmodule`: every twist of
  the structure sheaf of `Proj R[T₀, …, Tₙ]` is invertible.
* `Stacks.ProjectiveSpace.isAmple_twistingSheaf_one`: **`𝒪(1)` is ample on `Proj R[T₀, …, Tₙ]`.**
* `Stacks.ProjectiveSpace.isInvertibleModule_projectiveSpaceTwistingSheaf`: `𝒪(1)` is invertible
  on `ℙⁿ_S`.
* `Stacks.ProjectiveSpace.isAmple_projectiveSpaceTwistingSheaf`: **`𝒪(1)` is ample on `ℙⁿ_S`**
  for `S` affine.
* `Stacks.ProjectiveSpace.twistAmpleOverAffine`: the named hypothesis
  `Stacks.Tag01VT.TwistAmpleOverAffine` is a theorem.
* `Stacks.ProjectiveSpace.isRelativelyAmple_of_exists_hasImmersionTwistOver` and
  `Stacks.ProjectiveSpace.tfae_of_immersionTwistGapUniform`: the implication (5) ⟹ (2) of
  [Stacks, Tag 01VT] over an affine base with no named input, and the equivalence of conditions
  (1), (2), (5) and (6) on the single input
  `Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform`.

## References

* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
* [Stacks Project, Tag 01Q2](https://stacks.math.columbia.edu/tag/01Q2)
* [Stacks Project, Tag 01MW](https://stacks.math.columbia.edu/tag/01MW)
* [Stacks Project, Tag 0B3E](https://stacks.math.columbia.edu/tag/0B3E)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.Ample Stacks.AlgebraicGeometry.CommonDegreeTwist

universe u v

namespace Stacks.ProjectiveSpace

/-! ### Ampleness of a twist on `Proj` -/

section Proj

variable {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- **A twist of the structure sheaf of `Proj S` in a degree whose standard opens cover is
ample.** -/
theorem isAmple_twistingSheaf_of_commonDegreeCover
    (C : AlgebraicGeometry.Proj.CommonDegreeCover 𝒜 ⊤) {c : ℤ} (hc : c = (C.degree : ℤ))
    [CompactSpace (AlgebraicGeometry.Proj 𝒜)]
    [IsInvertibleModule (AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 c)] :
    IsAmple (AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 c) := by
  subst hc
  have : IsInvertibleModule ((⊤ : (AlgebraicGeometry.Proj 𝒜).Opens) : Scheme.{u})
      (restrictedTwist 𝒜 ⊤ (C.degree : ℤ)) :=
    Stacks.AlgebraicGeometry.ProjAmpleTwist.isInvertibleModule_restrictedTwist 𝒜 ⊤ C 1 (by ring)
  exact Stacks.HProjective.isAmple_of_isAmple_restrictTop _
    (Stacks.AlgebraicGeometry.ProjAmpleTwist.isAmple_restrictedTwist 𝒜 ⊤ C
      (isCompact_iff_compactSpace.mp isCompact_univ))

end Proj

/-! ### The degree-one cover of `Proj` of a polynomial ring -/

section Polynomial

variable (R : Type u) [CommRing R] (n : ℕ)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **The variables cover `Proj R[T₀, …, Tₙ]` in degree one**: the cover of `Proj R[T₀, …, Tₙ]`
by the standard opens `D₊(Tᵢ)`, as a common-degree cover of degree one. -/
def commonDegreeCoverTop :
    AlgebraicGeometry.Proj.CommonDegreeCover
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) ⊤ :=
  letI : DecidableEq (MvPolynomial (Fin (n + 1)) R) := Classical.decEq _
  { degree := 1
    degree_pos := Nat.one_pos
    sections := Finset.univ.image (MvPolynomial.X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R)
    sections_mem := fun f hf => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hf
      exact Stacks.SymmetricAway.X_mem_homogeneousSubmodule_one i
    iSup_basicOpen_inf_eq :=
      le_antisymm le_top
        ((Stacks.ProjectiveSpace.iSup_basicOpen_X_eq_top R (Fin (n + 1))).ge.trans
          (iSup_le fun i => le_iSup_of_le (MvPolynomial.X i)
            (le_iSup_of_le (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
              (le_inf le_rfl le_top)))) }

/-- **`Proj R[T₀, …, Tₙ]` is quasi-compact.** -/
instance compactSpace_proj_homogeneousSubmodule :
    CompactSpace (AlgebraicGeometry.Proj
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) := by
  classical
  refine (AlgebraicGeometry.Proj.compactSpace_iff _).mpr
    ⟨Finset.univ.image (MvPolynomial.X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R),
      fun f hf => ?_, ?_⟩
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hf
    exact ⟨1, Nat.one_pos, Stacks.SymmetricAway.X_mem_homogeneousSubmodule_one i⟩
  · refine le_trans (Stacks.AlgebraicGeometry.SegreChartProduct.irrelevant_le_span_X R
      (Fin (n + 1))) (le_trans (Ideal.span_mono ?_) Ideal.le_radical)
    rintro - ⟨i, rfl⟩
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

/-- The common degree of the cover of `Proj R[T₀, …, Tₙ]` by the standard opens of the variables
is one. -/
@[simp]
theorem commonDegreeCoverTop_degree : (commonDegreeCoverTop R n).degree = 1 := rfl

/-- **Every twist of the structure sheaf of `Proj R[T₀, …, Tₙ]` is invertible.** -/
@[ega "II 3.2.5" "special case"]
instance isInvertibleModule_twistingSheaf_homogeneousSubmodule (d : ℤ) :
    IsInvertibleModule (AlgebraicGeometry.Proj
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
      (twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) d) :=
  Stacks.AlgebraicGeometry.TwistMapsInvertible.isInvertibleModule_twistingSheaf_of_adjoin _
    (by
      rw [← Stacks.AlgebraicGeometry.ProjTwistMono.range_coe_degree_one
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)]
      exact Stacks.AlgebraicGeometry.TwistFlatness.adjoin_degree_one_homogeneousSubmodule
        (Fin (n + 1)) R) d

/-- **`𝒪(1)` is ample on `Proj R[T₀, …, Tₙ]`.** -/
theorem isAmple_twistingSheaf_one :
    IsAmple (AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
      (twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) 1) :=
  isAmple_twistingSheaf_of_commonDegreeCover _ (commonDegreeCoverTop R n) (by norm_num)

end Polynomial

/-! ### The hyperplane sheaf on projective space over an affine base -/

section AffineBase

open Stacks.AmpleProjectiveImmersion

variable (n : ℕ) (S : Scheme.{u})

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **The projection `ℙⁿ_S ⟶ ℙⁿ_ℤ` is an affine morphism when `S` is affine.** -/
instance isAffineHom_toIntegralAtUniverse [IsAffine S] :
    IsAffineHom (projectiveSpaceOver.toIntegralAtUniverse n S) :=
  AlgebraicGeometry.ProjectiveSpace.isAffineHom_toIntegralAtUniverse n S

/-- **`𝒪(1)` on the integral model `ℙⁿ_ℤ` is invertible.** -/
instance isInvertibleModule_twistingSheafAtUniverse :
    IsInvertibleModule (projectiveSpaceAtUniverse.{u} n) (twistingSheafAtUniverse.{u} n) :=
  isInvertibleModule_twistingSheaf_homogeneousSubmodule (ULift.{u} ℤ) n 1

/-- **`𝒪(1)` on `ℙⁿ_S` is invertible**, with no hypothesis on `S`. -/
instance isInvertibleModule_projectiveSpaceTwistingSheaf :
    IsInvertibleModule (projectiveSpaceOver n S) (projectiveSpaceTwistingSheaf n S) :=
  Stacks.InvertiblePullback.isInvertibleModule_pullback
    (projectiveSpaceOver.toIntegralAtUniverse n S) (twistingSheafAtUniverse.{u} n)

/-- **`𝒪(1)` is ample on `ℙⁿ_S` for an affine base `S`.** -/
theorem isAmple_projectiveSpaceTwistingSheaf [IsAffine S] :
    IsAmple (projectiveSpaceOver n S) (projectiveSpaceTwistingSheaf n S) :=
  Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom
    (projectiveSpaceOver.toIntegralAtUniverse n S) (twistingSheafAtUniverse.{u} n)
    (isAmple_twistingSheaf_one (ULift.{u} ℤ) n)

/-- **The named hypothesis `Stacks.Tag01VT.TwistAmpleOverAffine` is a theorem**: over an affine
base the hyperplane sheaf on projective space is an invertible ample module. -/
theorem twistAmpleOverAffine : Stacks.Tag01VT.TwistAmpleOverAffine.{u} :=
  fun n S _ => ⟨isInvertibleModule_projectiveSpaceTwistingSheaf n S,
    isAmple_projectiveSpaceTwistingSheaf n S⟩

end AffineBase

/-! ### Consequences for Stacks Tag 01VT -/

section Dividend

open Stacks.AmpleProjectiveImmersion

variable {X S : Scheme.{u}}

/-- **The implication (5) ⟹ (2) of [Stacks, Tag 01VT] with no named input**, over an affine
base. -/
theorem isRelativelyAmple_of_exists_hasImmersionTwistOver [IsAffine S] (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L] (hf : QuasiCompact f)
    (h : ∃ d : ℕ, 1 ≤ d ∧ HasImmersionTwistOver f (tensorPowModule X L (d : ℤ))) :
    Stacks.RelativeAmple.IsRelativelyAmple f L :=
  Stacks.RelativeAmpleImplications.isRelativelyAmple_of_exists_hasImmersionTwistOver
    twistAmpleOverAffine f L hf h

/-- **[Stacks, Tag 01VT], conditions (1), (2), (5) and (6)**, over an affine base, on the input
[Stacks, Tag 01VS] in the form `Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform`. -/
theorem tfae_of_immersionTwistGapUniform
    (hgap01VS : Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform.{u})
    [IsAffine S] (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L] [LocallyOfFiniteType f] (hqc : QuasiCompact f) :
    List.TFAE [
      IsAmple X L,
      Stacks.RelativeAmple.IsRelativelyAmple f L,
      ∃ d : ℕ, 1 ≤ d ∧ HasImmersionTwistOver f (tensorPowModule X L (d : ℤ)),
      ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
        HasImmersionTwistOver f (tensorPowModule X L (d : ℤ))] :=
  Stacks.RelativeAmpleImplications.tfae hgap01VS twistAmpleOverAffine f L hqc

end Dividend

end Stacks.ProjectiveSpace

end
