module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedRealizationFunctorial
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistAlgebraSheaf
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistPuncturedAlgebraSheaf
public import StacksFrontier.AlgebraicGeometry.ProjGradedModuleQcoh.StructureRestriction

/-!
# The inclusion of the two twist algebras is restriction from the cone to the punctured cone

Let `A` be a nonnegatively graded ring, `P = Proj A`, and let `π : L ⟶ P` be the cone of the
truncation algebra with `U ⊆ L` the punctured cone. The two direct images are the two twist
algebras of [Stacks, Tag 01CF],

  `π_* 𝒪_L = ⨁_{m ≥ 0} 𝒪_P(m)` and `(π|_U)_* 𝒪_U = ⨁_{m ∈ ℤ} 𝒪_P(m)`,

and the inclusion `⨁_{m ≥ 0} 𝒪_P(m) ↪ ⨁_{m ∈ ℤ} 𝒪_P(m)` of graded algebras is
`Stacks.AlgebraicGeometry.ProjConeTwist.nonnegToIntegerTwistAlgebra`. This file identifies the
algebra morphism that inclusion induces on the ungraded realizations with the restriction map
`π_* 𝒪_L ⟶ (π|_U)_* 𝒪_U` of the two direct images, under the two identifications. That square is
what makes the morphism of relative spectra induced by the inclusion the open immersion
`U ⟶ L`, and so what makes the left square of the diagram of [Stacks, Tag 0EKG] commute.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjConeTwist.nonnegToIntegerTwistUnitalHom`: the inclusion of the
  two twist algebras, as a **unital** homomorphism of sheaves of graded algebras.
* `Stacks.AlgebraicGeometry.ProjConeTwist.nonnegToIntegerTwistAlgebraSheafHom`: **the inclusion
  `⨁_{m ≥ 0} 𝒪_P(m) ⟶ ⨁_{m ∈ ℤ} 𝒪_P(m)` as a morphism of sheaves of commutative
  `𝒪_P`-algebras**, which is the shape the relative spectrum consumes.

## Main results

* `Stacks.AlgebraicGeometry.ProjConeTwist.degreeZeroRingMap_coneTwistAwayHom`: on the sections
  over a standard open `D₊(f)`, the degreewise inclusion into `(B[1/ψ f])₀` followed by
  restriction to `D₊(σ f · ψ f)` is the degreewise inclusion into `(B[1/σ f · ψ f])₀`.
* `Stacks.AlgebraicGeometry.ProjConeTwist.coneTwistApp_comp_restrict`: the same statement for
  the local degreewise inclusions into the two direct images.
* `Stacks.AlgebraicGeometry.ProjConeTwist.coneTwistHom_comp_restrict`: **the degreewise
  inclusion `𝒪_P(m) ⟶ π_* 𝒪_L` followed by restriction to the punctured cone is the degreewise
  inclusion `𝒪_P(m) ⟶ (π|_U)_* 𝒪_U`**, for `m ≥ 0`.
* `Stacks.AlgebraicGeometry.ProjConeTwist.nonnegToIntegerTwistAlgebraSheafHom_comp_iso`:
  **the inclusion of the two twist algebras is restriction from the cone to the punctured
  cone**, as morphisms of `𝒪_P`-algebras.

## Implementation notes

The degreewise statement is proved on the basis of positive-degree standard opens through the
uniqueness clause `Stacks.AlgebraicGeometry.ProjTwistComparison.eq_homOfStandardOpenHomData` of
the gluing principle the punctured inclusion is built by, so no second gluing argument is
needed. Over one standard open the comparison reduces to an identity between the two degreewise
inclusions into the degree-zero localizations of the truncation algebra, and that identity is
proved by injectivity of the comparison map `(B[1/σ f · ψ f])₀ → A[1/f]` of
`Stacks.Truncation.puncturedToLocalization_injective`: both sides have the same image there,
namely the standard-open description of the section one starts from.

The algebra-level square is reduced to the degreewise one by the universal property of
sheafification: `Stacks.GradedAlgebra.totalSheaf_hom_ext` brings both sides back to the presheaf
of direct sums, where `Stacks.GradedAlgebra.incl_induction` reduces to a homogeneous section.

## References

* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj CategoryTheory Opposite
open TopologicalSpace
open Stacks.AffineAlgebraEquivalence
open Stacks.AlgebraicGeometry.ProjAndSpecTruncation Stacks.Truncation
open Stacks.AlgebraicGeometry.ProjTwistComparison

namespace Stacks.AlgebraicGeometry.ProjConeTwist

universe u

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  PresheafOfModules.presheaf SheafOfModules.toSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {f : A}

/-! ### The two degreewise inclusions over one standard open -/

/-- **The degreewise inclusion of `Γ(D₊(f), 𝒪_P(m))` into the functions on the cone chart,
followed by restriction to the chart of the punctured cone, is the degreewise inclusion into the
functions on that chart**, for `m ≥ 0`. Both sides are elements of `(B[1/σ f · ψ f])₀`, and the
comparison map to `A[1/f]` is injective and sends both to the standard-open description of the
section one starts from. -/
@[stacks 0EKG "the degreewise inclusion of the sections of O_P(m) into the degree-zero \
localization of the truncation algebra at psi f, followed by restriction to the chart of the \
punctured cone, is the punctured degreewise inclusion, for a nonnegative degree m"]
theorem degreeZeroRingMap_coneTwistAwayHom (m : ℕ) {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (s : (twistingSheaf 𝒜 (m : ℤ)).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    ProjectiveSpectrum.degreeZeroRingMap (grading 𝒜) (psi 𝒜 f) (sigmaMulPsi 𝒜 f)
        ⟨d, hd, GradedRingHom.map_mem (psi 𝒜) hf⟩ ⟨d, hd, sigmaMulPsi_mem_grading 𝒜 d hf⟩
        (basicOpen_sigmaMulPsi_le_psi 𝒜) (coneTwistAwayHom 𝒜 m d hf hd s) =
      puncturedConeTwistAwayHom 𝒜 (m : ℤ) d hf hd s := by
  refine puncturedToLocalization_injective 𝒜 d hf ?_
  refine Eq.trans (puncturedToLocalization_degreeZeroRingMap 𝒜 _ _
    (basicOpen_sigmaMulPsi_le_psi 𝒜) _) ?_
  refine Eq.trans (awayToLocalization_awayGradingEquivSectionsTwist_symm 𝒜 d hf hd m s) ?_
  exact (puncturedToLocalization_puncturedGradingEquivSectionsTwist_symm 𝒜 d hf hd (m : ℤ) s).symm

/-- **The local degreewise inclusion into `π_* 𝒪_L` over a standard open, followed by restriction
along the open immersion of the punctured cone, is the punctured local degreewise inclusion**, for
`m ≥ 0`. Both are read on the chart `D₊(σ f · ψ f)` of the punctured cone inside the chart
`D₊(ψ f)` of the cone, where restriction of functions is the degree-zero restriction map of `B`
and `Stacks.AlgebraicGeometry.ProjConeTwist.degreeZeroRingMap_coneTwistAwayHom` applies. -/
@[stacks 0EKG "the local degreewise inclusion O_P(m) to pi_* O_L over a standard open, followed \
by restriction to the punctured cone, is the punctured local degreewise inclusion, for a \
nonnegative degree m"]
theorem appLE_coneTwistApp (m : ℕ) {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (hle : ((openUInL 𝒜).ι ≫ pi 𝒜) ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f ≤
      (openUInL 𝒜).ι ⁻¹ᵁ (pi 𝒜 ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f))
    (s : (twistingSheaf 𝒜 (m : ℤ)).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    ((openUInL 𝒜).ι.appLE (pi 𝒜 ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f)
          (((openUInL 𝒜).ι ≫ pi 𝒜) ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f) hle).hom
        ((coneTwistApp 𝒜 m d hf hd).hom s) =
      (puncturedConeTwistApp 𝒜 (m : ℤ) d hf hd).hom s := by
  have h1 := ConcreteCategory.congr_hom
    (Scheme.Hom.map_appLE (openUInL 𝒜).ι hle
      (eqToHom (pi_preimage_basicOpen 𝒜 f d hf hd)).op)
    ((AlgebraicGeometry.Proj.awayToSection (grading 𝒜) (psi 𝒜 f)).hom
      (coneTwistAwayHom 𝒜 m d hf hd s))
  have h2 := ConcreteCategory.congr_hom
    (Scheme.Hom.map_appLE (openUInL 𝒜).ι (puncturedPi_preimage_basicOpen 𝒜 d hf hd).le
      (homOfLE (basicOpen_sigmaMulPsi_le_psi 𝒜)).op)
    ((AlgebraicGeometry.Proj.awayToSection (grading 𝒜) (psi 𝒜 f)).hom
      (coneTwistAwayHom 𝒜 m d hf hd s))
  have h3 := ConcreteCategory.congr_hom
    (ProjectiveSpectrum.awayToSection_degreeZeroRingMap (grading 𝒜) (psi 𝒜 f) (sigmaMulPsi 𝒜 f)
      ⟨d, hd, GradedRingHom.map_mem (psi 𝒜) hf⟩ ⟨d, hd, sigmaMulPsi_mem_grading 𝒜 d hf⟩
      (basicOpen_sigmaMulPsi_le_psi 𝒜))
    (coneTwistAwayHom 𝒜 m d hf hd s)
  simp only [CommRingCat.comp_apply] at h1 h2 h3
  refine Eq.trans h1 ?_
  refine Eq.trans h2.symm ?_
  refine Eq.trans (congrArg
    (((openUInL 𝒜).ι.appLE (AlgebraicGeometry.Proj.basicOpen (grading 𝒜) (sigmaMulPsi 𝒜 f))
      (((openUInL 𝒜).ι ≫ pi 𝒜) ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f)
      (puncturedPi_preimage_basicOpen 𝒜 d hf hd).le).hom) h3.symm) ?_
  exact congrArg (fun z => (puncturedChartRestrict 𝒜 d hf hd).hom
      ((AlgebraicGeometry.Proj.awayToSection (grading 𝒜) (sigmaMulPsi 𝒜 f)).hom z))
    (degreeZeroRingMap_coneTwistAwayHom 𝒜 m hf hd s)

/-! ### The two degreewise inclusions over an arbitrary open -/

/-- **The degreewise inclusion `𝒪_P(m) ⟶ π_* 𝒪_L` followed by restriction of functions from the
cone to the punctured cone is the degreewise inclusion `𝒪_P(m) ⟶ (π|_U)_* 𝒪_U`**, for `m ≥ 0`,
read on the sections over an arbitrary open of `P`. Both sides are morphisms out of the sheaf
the punctured inclusion is glued from, so it is enough to compare them over the positive-degree
standard opens, where the comparison is
`Stacks.AlgebraicGeometry.ProjConeTwist.appLE_coneTwistApp`. -/
@[stacks 0EKG "the degreewise inclusion O_P(m) to pi_* O_L followed by restriction to the \
punctured cone is the degreewise inclusion O_P(m) to (pi|_U)_* O_U, for a nonnegative degree m"]
theorem appLE_coneTwistHom_app (m : ℕ) (V : Opens (ProjectiveSpectrum.top 𝒜))
    (hleV : ((openUInL 𝒜).ι ≫ pi 𝒜) ⁻¹ᵁ V ≤ (openUInL 𝒜).ι ⁻¹ᵁ (pi 𝒜 ⁻¹ᵁ V))
    (x : (twistingSheaf 𝒜 (m : ℤ)).val.obj (op V)) :
    ((openUInL 𝒜).ι.appLE (pi 𝒜 ⁻¹ᵁ V) (((openUInL 𝒜).ι ≫ pi 𝒜) ⁻¹ᵁ V) hleV).hom
        ((coneTwistHom 𝒜 m).val.app (op V) x) =
      (puncturedTwistHom 𝒜 (m : ℤ)).val.app (op V) x := by
  refine (homOfStandardOpenHomData_app_eq_of_restrict 𝒜
    (ProjectiveSpectrum.Proj.twistGrading (S := A) 𝒜 (m : ℤ))
    (Stacks.Morphisms.pushforwardStructureSheaf ((openUInL 𝒜).ι ≫ pi 𝒜))
    (puncturedConeTwistStandardOpenHomData 𝒜 (m : ℤ)) x _ ?_).symm
  intro p hp
  have hdp : 0 < Classical.choose p.2 := (Classical.choose_spec p.2).1
  have hfp : p.1 ∈ 𝒜 (Classical.choose p.2) := (Classical.choose_spec p.2).2
  have hlep : ((openUInL 𝒜).ι ≫ pi 𝒜) ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 p.1 ≤
      (openUInL 𝒜).ι ⁻¹ᵁ (pi 𝒜 ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 p.1) :=
    (Scheme.Hom.comp_preimage _ _ _).le
  have hnat := PresheafOfModules.naturality_apply (coneTwistHom 𝒜 m).val (homOfLE hp).op x
  have hmap := ConcreteCategory.congr_hom
    (Scheme.Hom.map_appLE (openUInL 𝒜).ι hlep
      ((Opens.map (pi 𝒜).base).map (homOfLE hp)).op)
    ((coneTwistHom 𝒜 m).val.app (op V) x)
  have hmap2 := ConcreteCategory.congr_hom
    (Scheme.Hom.appLE_map (openUInL 𝒜).ι hleV
      ((Opens.map ((openUInL 𝒜).ι ≫ pi 𝒜).base).map (homOfLE hp)).op)
    ((coneTwistHom 𝒜 m).val.app (op V) x)
  simp only at hmap hmap2
  refine Eq.trans (appLE_coneTwistApp 𝒜 m hfp hdp hlep
    ((ConcreteCategory.hom ((ProjectiveSpectrum.Proj.twistingSheaf 𝒜 (m : ℤ)).val.map
      (homOfLE hp).op)) x)).symm ?_
  refine Eq.trans (congrArg
    ((openUInL 𝒜).ι.appLE (pi 𝒜 ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 p.1)
      (((openUInL 𝒜).ι ≫ pi 𝒜) ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 p.1) hlep).hom
    (Eq.trans (congrArg (fun φ => (ConcreteCategory.hom φ)
        ((ConcreteCategory.hom ((ProjectiveSpectrum.Proj.twistingSheaf 𝒜 (m : ℤ)).val.map
          (homOfLE hp).op)) x)) (coneTwistHom_app 𝒜 m hfp hdp).symm) hnat)) ?_
  exact hmap.trans hmap2.symm

/-! ### The inclusion as a unital homomorphism of graded algebras -/

/-- **The inclusion `⨁_{m ≥ 0} 𝒪_P(m) ⟶ ⨁_{m ∈ ℤ} 𝒪_P(m)` as a unital homomorphism of sheaves
of graded algebras.** It is `Stacks.AlgebraicGeometry.ProjConeTwist.nonnegToIntegerTwistAlgebra`
with the preservation of the degree-zero unit recorded: both unit sections are the unit section
`Stacks.AlgebraicGeometry.ProjConeTwist.twistOne` of the untwisted sheaf, and in degree zero the
inclusion is the identity. -/
@[stacks 0EKG "the inclusion of the nonnegative twist algebra in the integral one, as a unital \
homomorphism of sheaves of graded algebras"]
def nonnegToIntegerTwistUnitalHom :
    SheafOfModules.GradedAlgebra.UnitalHom (nonnegTwistAlgebra 𝒜) (integerTwistAlgebra 𝒜) where
  app := nonnegToIntegerApp 𝒜
  map_mul i j U x y := nonnegToIntegerApp_map_mul 𝒜 i j U x y
  map_one _ := rfl

/-- **The inclusion of the two twist algebras as a morphism of sheaves of commutative
`𝒪_P`-algebras**, which is the shape the relative spectrum of [Stacks, Tag 01LM] consumes. Its
underlying morphism of sheaves of rings is the one the degreewise inclusions induce on the
ungraded realizations. -/
@[stacks 0EKG "the inclusion of the nonnegative twist algebra in the integral one, as a \
morphism of sheaves of commutative algebras over the structure sheaf of P"]
def nonnegToIntegerTwistAlgebraSheafHom :
    nonnegTwistAlgebraSheaf 𝒜 ⟶ integerTwistAlgebraSheaf 𝒜 :=
  Stacks.RelativeSpec.gradedAlgebraSheafMap (AlgebraicGeometry.Proj 𝒜)
    (nonnegToIntegerTwistUnitalHom 𝒜) (heq_nonnegTwistMul_comm 𝒜) (heq_twistMul_comm 𝒜)

/-! ### The inclusion is restriction from the cone to the punctured cone -/

/-- **The degreewise inclusion of each homogeneous piece of `⨁_{m ≥ 0} 𝒪_P(m)` into `π_* 𝒪_L`,
followed by restriction to the punctured cone, is the degreewise inclusion into
`(π|_U)_* 𝒪_U` composed with the degreewise inclusion of the two twist algebras**: the
nonnegative-degree case is
`Stacks.AlgebraicGeometry.ProjConeTwist.appLE_coneTwistHom_app`, and in a negative degree the
source sheaf is zero, so both sides vanish. -/
@[stacks 0EKG "the inclusion of each homogeneous piece of the nonnegative twist algebra in \
pi_* O_L, followed by restriction to the punctured cone, is the degreewise inclusion in \
(pi|_U)_* O_U after the inclusion of the two twist algebras"]
theorem appLE_coneIota_app (i : ℤ) (W : Opens (ProjectiveSpectrum.top 𝒜))
    (hleW : ((openUInL 𝒜).ι ≫ pi 𝒜) ⁻¹ᵁ W ≤ (openUInL 𝒜).ι ⁻¹ᵁ (pi 𝒜 ⁻¹ᵁ W))
    (y : (nonnegTwistingSheaf 𝒜 i).val.obj (op W)) :
    ((openUInL 𝒜).ι.appLE (pi 𝒜 ⁻¹ᵁ W) (((openUInL 𝒜).ι ≫ pi 𝒜) ⁻¹ᵁ W) hleW).hom
        ((coneIota 𝒜 i).val.app (op W) y) =
      (puncturedTwistHom 𝒜 i).val.app (op W) ((nonnegToIntegerApp 𝒜 i).val.app (op W) y) := by
  cases i with
  | ofNat k => exact appLE_coneTwistHom_app 𝒜 k W hleW y
  | negSucc k =>
    have hy : y = 0 :=
      eq_zero_of_isZero (isZero_nonnegTwistingSheaf 𝒜 (Int.negSucc_lt_zero k)) y
    subst hy
    simp only [map_zero]
    exact (RingHom.map_zero _).trans (map_zero (ConcreteCategory.hom
      ((puncturedTwistHom 𝒜 (Int.negSucc k)).val.app (op W)))).symm

/-- Two morphisms of sheaves of rings out of the ungraded realization of `⨁_{m ≥ 0} 𝒪_P(m)`
agree as soon as they agree on the homogeneous local sections. This is
`Stacks.GradedAlgebra.totalSheaf_hom_ext` with the universal property of sheafification already
used: a section of the presheaf of direct sums is a finite sum of homogeneous ones, and
`Stacks.GradedAlgebra.incl_induction` reduces to those. -/
private theorem ungradedSheaf_hom_ext
    {S : Sheaf (Opens.grothendieckTopology ↥(AlgebraicGeometry.Proj 𝒜)) RingCat.{u}}
    {g h : (nonnegTwistAlgebra 𝒜).ungradedSheaf ⟶ S}
    (hgh : ∀ (W : (Opens ↥(AlgebraicGeometry.Proj 𝒜))ᵒᵖ) (i : ℤ)
      (y : ((nonnegTwistAlgebra 𝒜).piece i).val.obj W),
      (ConcreteCategory.hom (g.hom.app W)) ((nonnegTwistAlgebra 𝒜).ungradedIncl i y) =
        (ConcreteCategory.hom (h.hom.app W)) ((nonnegTwistAlgebra 𝒜).ungradedIncl i y)) :
    g = h := by
  refine Stacks.GradedAlgebra.totalSheaf_hom_ext
    (nonnegTwistAlgebra 𝒜).toPresheafGradedAlgebra _ ?_
  refine NatTrans.ext (funext fun W => RingCat.hom_ext (RingHom.ext fun z => ?_))
  show (ConcreteCategory.hom (g.hom.app W))
      ((nonnegTwistAlgebra 𝒜).toPresheafGradedAlgebra.totalUnit
        (Opens.grothendieckTopology ↥(AlgebraicGeometry.Proj 𝒜)) W z) =
    (ConcreteCategory.hom (h.hom.app W))
      ((nonnegTwistAlgebra 𝒜).toPresheafGradedAlgebra.totalUnit
        (Opens.grothendieckTopology ↥(AlgebraicGeometry.Proj 𝒜)) W z)
  induction z using Stacks.GradedAlgebra.incl_induction
    (A := (nonnegTwistAlgebra 𝒜).toPresheafGradedAlgebra) with
  | zero =>
      rw [map_zero]
      exact (map_zero (ConcreteCategory.hom (g.hom.app W))).trans
        (map_zero (ConcreteCategory.hom (h.hom.app W))).symm
  | incl i y => exact hgh W i y
  | add a b ha hb =>
      rw [map_add]
      exact (map_add (ConcreteCategory.hom (g.hom.app W)) _ _).trans
        ((congrArg₂ (· + ·) ha hb).trans (map_add (ConcreteCategory.hom (h.hom.app W)) _ _).symm)

/-- **The inclusion of the two twist algebras is restriction of functions from the cone to the
punctured cone**, as morphisms of sheaves of rings: the morphism the degreewise inclusions induce
on the ungraded realizations, followed by the identification of `⨁_{m ∈ ℤ} 𝒪_P(m)` with
`(π|_U)_* 𝒪_U`, is the identification of `⨁_{m ≥ 0} 𝒪_P(m)` with `π_* 𝒪_L` followed by the
restriction map of the two direct images. -/
@[stacks 0EKG "the inclusion of the two twist algebras is restriction of functions from the cone \
to the punctured cone, as morphisms of sheaves of rings"]
theorem ungradedSheafMap_comp_puncturedConeUngradedSheafIso :
    SheafOfModules.GradedAlgebra.ungradedSheafMap (nonnegToIntegerTwistUnitalHom 𝒜) ≫
        (puncturedConeUngradedSheafIso 𝒜).hom =
      (coneUngradedSheafIso 𝒜).hom ≫
        Stacks.RelativeSpec.AlgebraSheaf.ringSheafMap
          (coneToPuncturedConeAlgebra (truncationConeData 𝒜)) := by
  refine ungradedSheaf_hom_ext 𝒜 fun W i y => ?_
  have hle : ((openUInL 𝒜).ι ≫ pi 𝒜) ⁻¹ᵁ W.unop ≤
      (openUInL 𝒜).ι ⁻¹ᵁ (pi 𝒜 ⁻¹ᵁ W.unop) := (Scheme.Hom.comp_preimage _ _ _).le
  have hL : (ConcreteCategory.hom
        ((SheafOfModules.GradedAlgebra.ungradedSheafMap (nonnegToIntegerTwistUnitalHom 𝒜) ≫
          (puncturedConeUngradedSheafIso 𝒜).hom).hom.app W))
        ((nonnegTwistAlgebra 𝒜).ungradedIncl i y) =
      (puncturedTwistHom 𝒜 i).val.app W ((nonnegToIntegerApp 𝒜 i).val.app W y) := by
    refine Eq.trans (RingCat.comp_apply
      ((SheafOfModules.GradedAlgebra.ungradedSheafMap
        (nonnegToIntegerTwistUnitalHom 𝒜)).hom.app W)
      ((puncturedConeUngradedSheafIso 𝒜).hom.hom.app W) _) ?_
    refine Eq.trans (congrArg (ConcreteCategory.hom
        ((puncturedConeUngradedSheafIso 𝒜).hom.hom.app W))
      (SheafOfModules.GradedAlgebra.ungradedIncl_ungradedSheafMap
        (nonnegToIntegerTwistUnitalHom 𝒜) i y)) ?_
    refine Eq.trans (puncturedConeUngradedSheafIso_totalUnit 𝒜 W
      ((integerTwistPresheafAlgebra 𝒜).incl i
        ((nonnegToIntegerApp 𝒜 i).val.app W y))) ?_
    exact puncturedTotalMap_incl 𝒜 W.unop i _
  have hR : (ConcreteCategory.hom
        (((coneUngradedSheafIso 𝒜).hom ≫ Stacks.RelativeSpec.AlgebraSheaf.ringSheafMap
          (coneToPuncturedConeAlgebra (truncationConeData 𝒜))).hom.app W))
        ((nonnegTwistAlgebra 𝒜).ungradedIncl i y) =
      ((openUInL 𝒜).ι.appLE (pi 𝒜 ⁻¹ᵁ W.unop)
          (((openUInL 𝒜).ι ≫ pi 𝒜) ⁻¹ᵁ W.unop) hle).hom
        ((coneIota 𝒜 i).val.app W y) := by
    refine Eq.trans (RingCat.comp_apply ((coneUngradedSheafIso 𝒜).hom.hom.app W)
      ((Stacks.RelativeSpec.AlgebraSheaf.ringSheafMap
        (coneToPuncturedConeAlgebra (truncationConeData 𝒜))).hom.app W) _) ?_
    refine Eq.trans (congrArg (ConcreteCategory.hom
        ((Stacks.RelativeSpec.AlgebraSheaf.ringSheafMap
          (coneToPuncturedConeAlgebra (truncationConeData 𝒜))).hom.app W))
      (Eq.trans (coneUngradedSheafIso_totalUnit 𝒜 W ((nonnegTwistPresheafAlgebra 𝒜).incl i y))
        (coneTotalMap_incl 𝒜 W.unop i y))) ?_
    exact ConcreteCategory.congr_hom
      (coneToPuncturedConeAlgebra_app (truncationConeData 𝒜) W.unop hle)
      ((coneIota 𝒜 i).val.app W y)
  exact hL.trans ((appLE_coneIota_app 𝒜 i W.unop hle y).symm.trans hR.symm)

/-- **The inclusion of the two twist algebras is restriction of functions from the cone to the
punctured cone**, as morphisms of sheaves of commutative `𝒪_P`-algebras. This is the square
that makes the morphism of relative spectra induced by the inclusion the open immersion of the
punctured cone, and hence the left square of the diagram of [Stacks, Tag 0EKG] commute. -/
@[stacks 0EKG "the inclusion of the two twist algebras is restriction of functions from the cone \
to the punctured cone, as morphisms of sheaves of commutative algebras over the structure sheaf \
of P"]
theorem nonnegToIntegerTwistAlgebraSheafHom_comp_puncturedConeAlgebraSheafIso :
    nonnegToIntegerTwistAlgebraSheafHom 𝒜 ≫ (puncturedConeAlgebraSheafIso 𝒜).hom =
      (coneAlgebraSheafIso 𝒜).hom ≫ coneToPuncturedConeAlgebra (truncationConeData 𝒜) := by
  refine Under.UnderMorphism.ext (Sheaf.hom_ext (NatTrans.ext (funext fun W =>
    CommRingCat.hom_ext (RingHom.ext fun z => ?_))))
  exact congrArg (fun φ : (nonnegTwistAlgebra 𝒜).ungradedSheaf ⟶
      puncturedConePushforwardRingSheaf 𝒜 => (ConcreteCategory.hom (φ.hom.app W)) z)
    (ungradedSheafMap_comp_puncturedConeUngradedSheafIso 𝒜)

end Stacks.AlgebraicGeometry.ProjConeTwist

end
