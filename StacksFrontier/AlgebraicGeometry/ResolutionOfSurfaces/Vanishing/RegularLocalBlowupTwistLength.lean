module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.FieldExtension
public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalTwistSequence
public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalTwistComparison
public import StacksFrontier.AlgebraicGeometry.Blowup.ProjectivePushforwardTruncation
public import StacksFrontier.AlgebraicGeometry.Blowup.TwistedPullbackTerms
public import StacksFrontier.AlgebraicGeometry.UniformTwistBound.Basic
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyComparison.Basic
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.IdealPowerCohomologySequence
public import StacksFrontier.AlgebraicGeometry.ProjModelStructureMap.BaseChange
public import StacksFrontier.AlgebraicGeometry.ProjModelStructureMap.ComparisonNatural
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.ProjectiveLineTopDimension
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.ProjectiveLineVanishing
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.GrauertRiemenschneider
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.RegularLocalBlowupTwists
public import StacksFrontier.RingTheory.Length.IndexAdditivity
public import StacksFrontier.Algebra.Category.ModuleCat.FiniteLength
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.StalkLength

/-!
# The length of the first cohomology of the negative twists on the blowup of a regular local
surface

Let `(A, 𝔪, κ)` be a regular local ring of dimension two and let `f : X ⟶ S = Spec A` be the
blowing up of `A` in `𝔪`. This file proves part (5) of [Stacks, Tag 0AGS],
$$ \text{length}_A H^1(X, \mathcal{O}_X(n)) = \frac{(-n)(-n-1)}{2} \qquad (n < 0), $$
by the source's descending induction.

## Main results

The elided prefix is `Stacks.Blowup`.

* `length_firstCohomologySheafAsBaseModule_blowUpTwist_maximalIdeal`: **part (5) of
  [Stacks, Tag 0AGS]**.
* `exceptionalTwistCohomologyIsoLine`: `H^q(X, i_* i^* 𝒪_X(n))`, read as an `A`-module through
  `f`, is `H^q(𝐏¹_κ, 𝒪(n))` read as an `A`-module through `A ↠ κ`.
* `appTop_comp_structure_eq_quotient_coeffScalar`: the exceptional divisor lies over the closed
  point, on global sections — the composite `A ⟶ Γ(X, 𝒪_X) ⟶ Γ(E, 𝒪_E)` is `A ↠ κ` followed by
  the coefficient scalars of `𝐏¹_κ` through `ρ`.
* `length_rightDerived_one_blowUpTwist_pred`: the induction step, the length additivity along the
  twist sequence.
* `length_rightDerived_one_blowUpTwist_neg`: the formula in the form `𝓁 H¹(X, 𝒪_X(-d)) = C(d, 2)`.

## The route

The source's: descending induction on `n`, anchored at `n = -1` by part (2) of the tag
(`Stacks.Blowup.isZero_hgroup_one_twistingSheaf_maximalIdeal`), along the short exact sequences
`0 → 𝒪_X(n) → 𝒪_X(n-1) → i_*𝒪_E(n-1) → 0`
(`Stacks.Blowup.shortExact_twist_exceptional`, read at `(n, n-1)`).

In degree one the long exact cohomology sequence of that sequence collapses to a short exact
sequence. The connecting map `H⁰(X, i_*𝒪_E(n-1)) ⟶ H¹(X, 𝒪_X(n))` is zero because its source is:
`i_*𝒪_E(n-1)` restricts to a negative twist on `𝐏¹_κ`, whose global sections vanish
([Stacks, Tag 01XT]). The connecting map `H¹(X, i_*𝒪_E(n-1)) ⟶ H²(X, 𝒪_X(n))` is zero because its
target is, by part (1) of the tag. So the lengths add, and the new term is
`𝓁_A H¹(𝐏¹_κ, 𝒪(n-1)) = -n` by [Stacks, Tag 01XT]
(`Stacks.ProjectiveSpace.Cohomology.length_twistCohomology_line_top`). The recursion
`𝓁(n-1) = 𝓁(n) + (-n)` with `𝓁(-1) = 0` is the recursion for the binomial coefficient
`C(-n, 2) = (-n)(-n-1)/2`.

The long exact sequence is the cohomological δ-functor
`Stacks.Cohomology.FormalFunctions.cohomologyDeltaFunctor`, which is valued in
`Γ(X, 𝒪_X)`-modules; restriction of scalars along `A ⟶ Γ(X, 𝒪_X)` changes neither the carriers
nor the maps, so it carries the short exact sequence to a short exact sequence of `A`-modules
and the lengths are read there.

## Finite length

Nothing is assumed about finiteness of `H¹(X, 𝒪_X(n))` over `A`, and nothing needs to be: the
induction produces the value of `Module.length` outright at every stage, starting from the zero
module at `n = -1` and adding a finite length at each step, so finiteness is a consequence of the
formula rather than an input to it. This is why the argument runs through
`Module.length_eq_add_of_exact`, which is an identity in `ℕ∞` with no finiteness hypothesis,
rather than through the `ℕ`-valued bookkeeping of
`Module.length_alternating_exact_six`.

## The two `A`-module structures

`H¹(X, i_*𝒪_E(n-1))` arrives as an `A`-module through `X ⟶ Spec A`, while its computation as
`H¹(𝐏¹_κ, 𝒪(n-1))` produces a `κ`-module. The comparison of lengths therefore needs the
identification of the two scalar actions, which is
`Stacks.Blowup.appTop_comp_structure_eq_quotient_coeffScalar`: the structure morphism of `E` over
`Spec A` factors through `Spec κ` compatibly with `ρ`. It is assembled from the factorization
clause of part (1) of [Stacks, Tag 0AGQ], the immersion of the blowup into `𝐏¹_{Spec A}` being a
morphism over the base, and the base-change compatibility
`Stacks.ProjectiveCohomology.projModelMap_comp_projModelToSpec` of the structure morphisms of
projective space. With the two actions identified, the length over `A` is the length over `κ`
because `A ↠ κ` is surjective (`Module.length_eq_of_surjective`).

## References

* [Stacks Project, Tag 0AGS](https://stacks.math.columbia.edu/tag/0AGS)
* [Stacks Project, Tag 0AGQ](https://stacks.math.columbia.edu/tag/0AGQ)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 0898](https://stacks.math.columbia.edu/tag/0898)
* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf)

universe u
namespace Stacks.Blowup
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] modulesMonoidal modulesMonoidal'
attribute [local instance] Stacks.AlgebraicGeometry.ProjTwistUnitorSections.projGradedMonoidal

variable {R : Type u} [CommRing R] (I : Ideal R)

section Assembly

/-- The scalars of the exceptional divisor over the base factor through the residue ring: the
composite `R ⟶ Γ(X, 𝒪_X) ⟶ Γ(E, 𝒪_E)` is `R ↠ R/I` followed by the coefficient scalars of
`𝐏¹_{R/I}` read through `ρ`. -/
theorem appTop_comp_structure_eq_quotient_coeffScalar
    (x : Fin 2 → R) (hx : ∀ i, x i ∈ I) (hspan : I = Ideal.span (Set.range x))
    (ρ : (exceptionalIdealData I).subscheme ≅
      AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin 2) (R ⧸ I)))
    (hcomp : (exceptionalIdealData I).subschemeι ≫ blowUpSpecToProjSpace I x hx hspan =
      ρ.hom ≫ AlgebraicGeometry.Proj.map
        (Stacks.ProjectiveCohomology.polyGradedMap (Fin 2) (Ideal.Quotient.mk I))
        (Stacks.ProjectiveCohomology.irrelevant_le_map_polyGradedMap (Fin 2)
          (Ideal.Quotient.mk I))) :
    (exceptionalIdealData I).subschemeι.appTop.hom.comp
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (toSpec I).appTop).hom =
      ρ.hom.appTop.hom.comp
        ((Stacks.ProjectiveSpace.Cohomology.coeffScalar (R ⧸ I) 1).comp
          (Ideal.Quotient.mk I)) := by
  have hs : (exceptionalIdealData I).subschemeι ≫ toSpec I =
      ρ.hom ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff (R ⧸ I) 1 ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
    have h1 : projSpaceToSpec R 2 =
        Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff R 1 :=
      projSpaceToSpec_eq_projToSpecCoeff R 1
    have h2 : AlgebraicGeometry.Proj.map
          (Stacks.ProjectiveCohomology.polyGradedMap (Fin 2) (Ideal.Quotient.mk I))
          (Stacks.ProjectiveCohomology.irrelevant_le_map_polyGradedMap (Fin 2)
            (Ideal.Quotient.mk I)) ≫
          Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff R 1 =
        Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff (R ⧸ I) 1 ≫
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
      rw [Stacks.ProjectiveCohomology.projToSpecCoeff_eq_projModelToSpec,
        Stacks.ProjectiveCohomology.projToSpecCoeff_eq_projModelToSpec]
      exact Stacks.ProjectiveCohomology.projModelMap_comp_projModelToSpec 1 (Ideal.Quotient.mk I)
    rw [← blowUpSpecToProjSpace_comp_projSpaceToSpec I x hx hspan, ← Category.assoc, hcomp,
      Category.assoc, h1, h2]
  have key : ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (toSpec I).appTop) ≫
        (exceptionalIdealData I).subschemeι.appTop =
      CommRingCat.ofHom (Ideal.Quotient.mk I) ≫
        ((Scheme.ΓSpecIso (CommRingCat.of (R ⧸ I))).inv ≫
          (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff (R ⧸ I) 1).appTop) ≫
            ρ.hom.appTop := by
    rw [Category.assoc, ← Scheme.Hom.comp_appTop, hs]
    simp only [Scheme.Hom.comp_appTop, Category.assoc]
    rw [← Scheme.ΓSpecIso_inv_naturality_assoc]
  exact congrArg CommRingCat.Hom.hom key

/-- **The cohomology of the exceptional term is the cohomology of a twist on `𝐏¹_{R/I}`.**
`H^q(X, i_* i^* 𝒪_X(n))`, read as an `R`-module through `X ⟶ Spec R`, is `H^q(𝐏¹_{R/I}, 𝒪(n))`
read as an `R`-module through `R ↠ R/I`.

Two instances of [Stacks, Tag 0898] (`Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward`
for an affine morphism), the comparison of twists on the exceptional divisor
`Stacks.Blowup.pullbackExceptionalTwistIso`, and the invertibility of the unit of
`ρ^* ⊣ ρ_*` for the isomorphism `ρ`. The two `R`-module structures agree by
`Stacks.Blowup.appTop_comp_structure_eq_quotient_coeffScalar`. -/
def exceptionalTwistCohomologyIsoLine
    (x : Fin 2 → R) (hx : ∀ i, x i ∈ I) (hspan : I = Ideal.span (Set.range x))
    (ρ : (exceptionalIdealData I).subscheme ≅
      AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin 2) (R ⧸ I)))
    (hcomp : (exceptionalIdealData I).subschemeι ≫ blowUpSpecToProjSpace I x hx hspan =
      ρ.hom ≫ AlgebraicGeometry.Proj.map
        (Stacks.ProjectiveCohomology.polyGradedMap (Fin 2) (Ideal.Quotient.mk I))
        (Stacks.ProjectiveCohomology.irrelevant_le_map_polyGradedMap (Fin 2)
          (Ideal.Quotient.mk I)))
    (n : ℤ) (q : ℕ) :
    (ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (toSpec I).appTop).hom).obj
        (((Stacks.Cohomology.AffineBase.moduleGlobalSections (blowUpSpec I)).rightDerived q).obj
          ((Scheme.Modules.pushforward (exceptionalIdealData I).subschemeι).obj
            ((Scheme.Modules.pullback (exceptionalIdealData I).subschemeι).obj
              (blowUpTwist I n)))) ≅
      (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj
        (Stacks.ProjectiveSpace.Cohomology.twistCohomology (R ⧸ I) 1 n q) := by
  haveI : ((Scheme.Modules.pullback (exceptionalIdealData I).subschemeι).obj
      (blowUpTwist I n)).IsQuasicoherent :=
    AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback _ _
  haveI : _root_.SheafOfModules.IsQuasicoherent
      (R := (AlgebraicGeometry.Proj
        (MvPolynomial.homogeneousSubmodule (Fin 2) (R ⧸ I))).ringCatSheaf)
      (twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin 2) (R ⧸ I)) n) :=
    Stacks.AlgebraicGeometry.Tag0B5QUniformTwistBound.isQuasicoherent_twistingSheaf _ n
  haveI : ((Scheme.Modules.pullback ρ.hom).obj
      (twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin 2) (R ⧸ I)) n)).IsQuasicoherent :=
    AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback _ _
  haveI : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction ρ.hom).unit.app
      (twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin 2) (R ⧸ I)) n)) :=
    NatIso.isIso_app_of_isIso
      (α := (Scheme.Modules.pullbackPushforwardAdjunction ρ.hom).unit) _
  -- the three geometric comparisons
  have e1 := Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward
    (exceptionalIdealData I).subschemeι
    ((Scheme.Modules.pullback (exceptionalIdealData I).subschemeι).obj (blowUpTwist I n)) q
  have e2 := ((Stacks.Cohomology.AffineBase.moduleGlobalSections
    (exceptionalIdealData I).subscheme).rightDerived q).mapIso
      (pullbackExceptionalTwistIso I x hx hspan ρ hcomp n)
  have e3 := Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward ρ.hom
      ((Scheme.Modules.pullback ρ.hom).obj
        (twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin 2) (R ⧸ I)) n)) q ≪≫
    ((Stacks.Cohomology.AffineBase.moduleGlobalSections
      (AlgebraicGeometry.Proj
        (MvPolynomial.homogeneousSubmodule (Fin 2) (R ⧸ I)))).rightDerived q).mapIso
        (asIso ((Scheme.Modules.pullbackPushforwardAdjunction ρ.hom).unit.app _)).symm
  have hH := appTop_comp_structure_eq_quotient_coeffScalar I x hx hspan ρ hcomp
  refine (ModuleCat.restrictScalars
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (toSpec I).appTop).hom).mapIso e1.symm ≪≫ ?_
  refine (ModuleCat.restrictScalars
    ((exceptionalIdealData I).subschemeι.appTop.hom.comp
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (toSpec I).appTop).hom)).mapIso e2 ≪≫ ?_
  exact eqToIso (congrArg (fun ψ => (ModuleCat.restrictScalars ψ).obj _) hH) ≪≫
    (ModuleCat.restrictScalars
      ((Stacks.ProjectiveSpace.Cohomology.coeffScalar (R ⧸ I) 1).comp
        (Ideal.Quotient.mk I))).mapIso e3

/-- **`H⁰(X, i_* i^* 𝒪_X(n)) = 0` for `n < 0`.** The exceptional term is a twist on `𝐏¹_{R/I}`,
and the global sections of a negative twist on the projective line vanish. -/
theorem isZero_rightDerived_zero_pushforward_pullback_blowUpTwist
    (x : Fin 2 → R) (hx : ∀ i, x i ∈ I) (hspan : I = Ideal.span (Set.range x))
    (ρ : (exceptionalIdealData I).subscheme ≅
      AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin 2) (R ⧸ I)))
    (hcomp : (exceptionalIdealData I).subschemeι ≫ blowUpSpecToProjSpace I x hx hspan =
      ρ.hom ≫ AlgebraicGeometry.Proj.map
        (Stacks.ProjectiveCohomology.polyGradedMap (Fin 2) (Ideal.Quotient.mk I))
        (Stacks.ProjectiveCohomology.irrelevant_le_map_polyGradedMap (Fin 2)
          (Ideal.Quotient.mk I)))
    {n : ℤ} (hn : n < 0) :
    IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections (blowUpSpec I)).rightDerived 0).obj
      ((Scheme.Modules.pushforward (exceptionalIdealData I).subschemeι).obj
        ((Scheme.Modules.pullback (exceptionalIdealData I).subschemeι).obj
          (blowUpTwist I n)))) := by
  refine (Stacks.ProjectiveCohomology.isZero_restrictScalars_iff
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (toSpec I).appTop).hom _).1 ?_
  refine IsZero.of_iso ?_ (exceptionalTwistCohomologyIsoLine I x hx hspan ρ hcomp n 0)
  exact (Stacks.ProjectiveCohomology.isZero_restrictScalars_iff (Ideal.Quotient.mk I) _).2
    (Stacks.ProjectiveSpace.Cohomology.isZero_twistCohomology_zero_of_neg (R ⧸ I) hn)

/-- **The length of the cohomology of the exceptional term.** `H^q(X, i_* i^* 𝒪_X(n))` has the
same length over `R` as `H^q(𝐏¹_{R/I}, 𝒪(n))` has over `R/I`. -/
theorem length_rightDerived_pushforward_pullback_blowUpTwist
    (x : Fin 2 → R) (hx : ∀ i, x i ∈ I) (hspan : I = Ideal.span (Set.range x))
    (ρ : (exceptionalIdealData I).subscheme ≅
      AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin 2) (R ⧸ I)))
    (hcomp : (exceptionalIdealData I).subschemeι ≫ blowUpSpecToProjSpace I x hx hspan =
      ρ.hom ≫ AlgebraicGeometry.Proj.map
        (Stacks.ProjectiveCohomology.polyGradedMap (Fin 2) (Ideal.Quotient.mk I))
        (Stacks.ProjectiveCohomology.irrelevant_le_map_polyGradedMap (Fin 2)
          (Ideal.Quotient.mk I)))
    (n : ℤ) (q : ℕ) :
    Module.length R ((ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (toSpec I).appTop).hom).obj
        (((Stacks.Cohomology.AffineBase.moduleGlobalSections (blowUpSpec I)).rightDerived q).obj
          ((Scheme.Modules.pushforward (exceptionalIdealData I).subschemeι).obj
            ((Scheme.Modules.pullback (exceptionalIdealData I).subschemeι).obj
              (blowUpTwist I n))))) =
      Module.length (R ⧸ I)
        (Stacks.ProjectiveSpace.Cohomology.twistCohomology (R ⧸ I) 1 n q) := by
  rw [ModuleCat.length_eq_of_iso (exceptionalTwistCohomologyIsoLine I x hx hspan ρ hcomp n q),
    Stacks.ClosedImmersion.length_restrictScalars_obj_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective]

/-- **`H²(X, 𝒪_X(n)) = 0`**, in the module-valued spelling: part (1) of [Stacks, Tag 0AGS] for
the blowup in a two-generated ideal, transported from the `Hgroup` spelling. -/
theorem isZero_rightDerived_two_blowUpTwist [IsNoetherianRing R]
    (x : Fin 2 → R) (hx : ∀ j, x j ∈ I) (hspan : I = Ideal.span (Set.range x)) (n : ℤ) :
    IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections (blowUpSpec I)).rightDerived 2).obj
      (blowUpTwist I n)) :=
  (Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup
      (blowUpSpec I).ringCatSheaf ⊤ 2 (blowUpTwist I n)).2
    (isZero_hgroup_of_two_le_of_two_generators x hx hspan (blowUpTwist I n) 2 le_rfl)

/-- **The induction step of part (5) of [Stacks, Tag 0AGS].** For `n ≤ 0` the long exact
cohomology sequence of `0 → 𝒪_X(n) → 𝒪_X(n-1) → i_*𝒪_E(n-1) → 0` collapses to a short exact
sequence in degree one — `H⁰(X, i_*𝒪_E(n-1)) = 0` kills the connecting map on the left and
`H²(X, 𝒪_X(n)) = 0` kills it on the right — so the lengths add. -/
theorem length_rightDerived_one_blowUpTwist_pred [IsNoetherianRing R]
    (x : Fin 2 → R) (hx : ∀ i, x i ∈ I) (hspan : I = Ideal.span (Set.range x))
    (ρ : (exceptionalIdealData I).subscheme ≅
      AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin 2) (R ⧸ I)))
    (hcomp : (exceptionalIdealData I).subschemeι ≫ blowUpSpecToProjSpace I x hx hspan =
      ρ.hom ≫ AlgebraicGeometry.Proj.map
        (Stacks.ProjectiveCohomology.polyGradedMap (Fin 2) (Ideal.Quotient.mk I))
        (Stacks.ProjectiveCohomology.irrelevant_le_map_polyGradedMap (Fin 2)
          (Ideal.Quotient.mk I)))
    {n : ℤ} (hn : n ≤ 0) :
    Module.length R ((ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (toSpec I).appTop).hom).obj
        (((Stacks.Cohomology.AffineBase.moduleGlobalSections (blowUpSpec I)).rightDerived 1).obj
          (blowUpTwist I (n - 1)))) =
      Module.length R ((ModuleCat.restrictScalars
            ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (toSpec I).appTop).hom).obj
          (((Stacks.Cohomology.AffineBase.moduleGlobalSections (blowUpSpec I)).rightDerived 1).obj
            (blowUpTwist I n))) +
        Module.length (R ⧸ I)
          (Stacks.ProjectiveSpace.Cohomology.twistCohomology (R ⧸ I) 1 (n - 1) 1) := by
  obtain ⟨hz, hSE⟩ := shortExact_twist_exceptional I (m := n) (n := n - 1) (by ring)
  set S := ShortComplex.mk _ _ hz with hS
  set φ := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (toSpec I).appTop).hom with hφ
  have h0 := isZero_rightDerived_zero_pushforward_pullback_blowUpTwist I x hx hspan ρ hcomp
    (n := n - 1) (by omega)
  have h2 := isZero_rightDerived_two_blowUpTwist I x hx hspan n
  have hmono : Mono (((Stacks.Cohomology.AffineBase.moduleGlobalSections
      (blowUpSpec I)).rightDerived 1).map S.f) :=
    ((Stacks.Cohomology.FormalFunctions.cohomologyDeltaFunctor
      (blowUpSpec I)).exact_δ₂ hSE 0).mono_g (h0.eq_zero_of_src _)
  have hepi : Epi (((Stacks.Cohomology.AffineBase.moduleGlobalSections
      (blowUpSpec I)).rightDerived 1).map S.g) :=
    ((Stacks.Cohomology.FormalFunctions.cohomologyDeltaFunctor
      (blowUpSpec I)).exact_δ₁ hSE 1).epi_f (h2.eq_zero_of_tgt _)
  have hT : (S.map ((Stacks.Cohomology.AffineBase.moduleGlobalSections
      (blowUpSpec I)).rightDerived 1)).ShortExact :=
    { exact := (Stacks.Cohomology.FormalFunctions.cohomologyDeltaFunctor
        (blowUpSpec I)).exact_map hSE 1
      mono_f := hmono
      epi_g := hepi }
  have hT' := hT.map_of_exact (ModuleCat.restrictScalars φ)
  refine (Module.length_eq_add_of_exact (R := R) _ _
    ((ModuleCat.mono_iff_injective _).1 hT'.mono_f)
    ((ModuleCat.epi_iff_surjective _).1 hT'.epi_g)
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hT'.exact)).trans ?_
  congr 1
  exact length_rightDerived_pushforward_pullback_blowUpTwist I x hx hspan ρ hcomp (n - 1) 1

/-- **The base of the induction.** `H¹(X, 𝒪_X(n))` vanishes for `n ≥ -1`, hence has length zero;
this is part (2) of [Stacks, Tag 0AGS]. -/
theorem length_rightDerived_one_blowUpTwist_eq_zero [IsNoetherianRing R]
    (x : Fin 2 → R) (hx : ∀ j, x j ∈ I) (hspan : I = Ideal.span (Set.range x))
    {n : ℤ} (hn : -1 ≤ n) :
    Module.length R ((ModuleCat.restrictScalars
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (toSpec I).appTop).hom).obj
      (((Stacks.Cohomology.AffineBase.moduleGlobalSections (blowUpSpec I)).rightDerived 1).obj
        (blowUpTwist I n))) = 0 := by
  have h := (Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup
    (blowUpSpec I).ringCatSheaf ⊤ 1 (blowUpTwist I n)).2
      (isZero_hgroup_one_twistingSheaf_of_two_generators x hx hspan hn)
  exact Module.length_eq_zero_iff.2 (ModuleCat.subsingleton_of_isZero
    ((Stacks.ProjectiveCohomology.isZero_restrictScalars_iff
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (toSpec I).appTop).hom _).2 h))

/-- **The length formula, by descending induction.** For `d : ℕ`,
`𝓁_R H¹(X, 𝒪_X(-d)) = d(d-1)/2 = C(d, 2)`. -/
theorem length_rightDerived_one_blowUpTwist_neg [IsNoetherianRing R] [I.IsMaximal]
    (x : Fin 2 → R) (hx : ∀ i, x i ∈ I) (hspan : I = Ideal.span (Set.range x))
    (ρ : (exceptionalIdealData I).subscheme ≅
      AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin 2) (R ⧸ I)))
    (hcomp : (exceptionalIdealData I).subschemeι ≫ blowUpSpecToProjSpace I x hx hspan =
      ρ.hom ≫ AlgebraicGeometry.Proj.map
        (Stacks.ProjectiveCohomology.polyGradedMap (Fin 2) (Ideal.Quotient.mk I))
        (Stacks.ProjectiveCohomology.irrelevant_le_map_polyGradedMap (Fin 2)
          (Ideal.Quotient.mk I)))
    (d : ℕ) :
    Module.length R ((ModuleCat.restrictScalars
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (toSpec I).appTop).hom).obj
      (((Stacks.Cohomology.AffineBase.moduleGlobalSections (blowUpSpec I)).rightDerived 1).obj
        (blowUpTwist I (-(d : ℤ))))) = (d.choose 2 : ℕ) := by
  induction d with
  | zero =>
    rw [show (-((0 : ℕ) : ℤ)) = 0 by norm_num]
    simpa using length_rightDerived_one_blowUpTwist_eq_zero I x hx hspan (n := 0) (by norm_num)
  | succ e ih =>
    have harg : (-((e + 1 : ℕ) : ℤ)) = -(e : ℤ) - 1 := by push_cast; ring
    have hline : Module.length (R ⧸ I)
        (Stacks.ProjectiveSpace.Cohomology.twistCohomology (R ⧸ I) 1 (-(e : ℤ) - 1) 1)
          = ((e : ℕ) : ℕ∞) := by
      let : Field (R ⧸ I) := Ideal.Quotient.field I
      have h := Stacks.ProjectiveSpace.Cohomology.length_twistCohomology_line_top (R ⧸ I) (e + 1)
      rw [harg] at h
      simpa using h
    rw [harg, length_rightDerived_one_blowUpTwist_pred I x hx hspan ρ hcomp
      (n := -(e : ℤ)) (by omega), ih, hline, Nat.choose_succ_succ e 1, Nat.choose_one_right]
    push_cast
    ring

/-- `d(d-1)/2 = C(d, 2)`, read in `ℤ` and brought back to `ℕ`. -/
private theorem toNat_mul_pred_div_two (d : ℕ) :
    ((d : ℤ) * ((d : ℤ) - 1) / 2).toNat = d.choose 2 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · have h1 : ((d : ℤ) - 1) = ((d - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_sub hd, Nat.cast_one]
    rw [h1, ← Nat.cast_mul, show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, ← Int.natCast_div,
      Int.toNat_natCast, Nat.choose_two_right]

end Assembly

section MaximalIdeal

open IsLocalRing

/-- **Stacks Project, Tag 0AGS part (5).** Let `(A, 𝔪, κ)` be a regular local ring of dimension
two and let `f : X ⟶ S = Spec A` be the blowing up of `A` in `𝔪`. Then for every `n < 0`
$$ \text{length}_A H^1(X, \mathcal{O}_X(n)) = \frac{(-n)(-n-1)}{2}. $$
The cohomology is read as an `A`-module through `f`, which is
`AlgebraicGeometry.firstCohomologySheafAsBaseModule`.

The proof is the source's descending induction. Part (2) of the tag
(`Stacks.Blowup.isZero_hgroup_one_twistingSheaf_maximalIdeal`) anchors it at `n = -1`, where the
length is zero. The step is the long exact cohomology sequence of
`0 → 𝒪_X(n) → 𝒪_X(n-1) → i_*𝒪_E(n-1) → 0`
(`Stacks.Blowup.shortExact_twist_exceptional`), which in degree one collapses to a short exact
sequence: the connecting map out of `H⁰(X, i_*𝒪_E(n-1))` vanishes because that module is zero,
and the one into `H²(X, 𝒪_X(n))` vanishes by part (1) of the tag. The middle term is
`H¹(𝐏¹_κ, 𝒪(n-1))`, of length `-n` by [Stacks, Tag 01XT]
(`Stacks.ProjectiveSpace.Cohomology.length_twistCohomology_line_top`) through the identification
`E ≅ 𝐏¹_κ` of part (1) of [Stacks, Tag 0AGQ]; the lengths therefore satisfy
`𝓁 H¹(𝒪_X(n-1)) = 𝓁 H¹(𝒪_X(n)) + (-n)`, which is the recursion for `C(-n, 2)`.

Finite length is not assumed: it is a by-product of the induction, since the formula gives a
natural number at every stage. -/
@[stacks 0AGS "part (5): length_A H^1(X, O_X(n)) = (-n)(-n-1)/2 for n < 0"]
theorem length_firstCohomologySheafAsBaseModule_blowUpTwist_maximalIdeal (A : Type u)
    [CommRing A] [IsRegularLocalRing A] (hdim : ringKrullDim A = 2) {n : ℤ} (hn : n < 0) :
    Module.length A (AlgebraicGeometry.firstCohomologySheafAsBaseModule
        (blowUpSpec (maximalIdeal A)) (toSpec (maximalIdeal A))
        (blowUpTwist (maximalIdeal A) n))
      = ((((-n) * (-n - 1) / 2).toNat : ℕ) : ℕ∞) := by
  obtain ⟨x, hspan⟩ := exists_range_eq_maximalIdeal A hdim
  have hx : ∀ i, x i ∈ maximalIdeal A := fun i ↦ by
    rw [hspan]; exact Ideal.subset_span ⟨i, rfl⟩
  obtain ⟨ρ, hcomp⟩ := exists_iso_exceptional_projectiveLine A hdim x hx hspan
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, n = -(d : ℤ) := ⟨(-n).toNat, by omega⟩
  rw [show (-(-(d : ℤ))) = (d : ℤ) by ring]
  rw [show AlgebraicGeometry.firstCohomologySheafAsBaseModule
      (blowUpSpec (maximalIdeal A)) (toSpec (maximalIdeal A))
        (blowUpTwist (maximalIdeal A) (-(d : ℤ))) =
      (ModuleCat.restrictScalars
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (toSpec (maximalIdeal A)).appTop).hom).obj
        (((Stacks.Cohomology.AffineBase.moduleGlobalSections
          (blowUpSpec (maximalIdeal A))).rightDerived 1).obj
            (blowUpTwist (maximalIdeal A) (-(d : ℤ)))) from rfl]
  rw [length_rightDerived_one_blowUpTwist_neg (maximalIdeal A) x hx hspan ρ hcomp d,
    toNat_mul_pred_div_two]

end MaximalIdeal

end Stacks.Blowup
end
