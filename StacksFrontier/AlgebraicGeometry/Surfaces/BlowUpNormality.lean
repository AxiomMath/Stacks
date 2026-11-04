module

public import StacksFrontier.AlgebraicGeometry.Blowup.NormalizedBlowUp
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.AffineCharts
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Proper
public import StacksFrontier.AlgebraicGeometry.Blowup.RegularSurfaceBlowup
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Birational
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.StandardChart
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Stability
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Scheme
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.Basic
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.IntegralClosureBaseChange
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.NormalizationBirational.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.Basic
import all StacksFrontier.AlgebraicGeometry.Properties.Normal

/-!
# Normality of a blowup is a property of its affine blowup algebras

The blowup of a scheme `X` in a quasi-coherent ideal `I` is covered by the spectra of the affine
blowup algebras `Γ(X, U)[I/a]`, one for each affine open `U` of `X` and each section `a` of `I`
over `U`. Normality of a scheme is a condition on its local rings, and the local rings of the
blowup are therefore localizations of those algebras. This file turns that observation into a
criterion: the blowup is normal as soon as every affine blowup algebra over the members of one
affine open covering of the base is a normal ring.

The criterion is specialized to the blowup of the spectrum of a local ring in its maximal ideal,
which is the geometric situation of the resolution of surface singularities. For a
two-dimensional local Noetherian domain `A` that blowup is an integral scheme and a modification
of `Spec(A)`; when `A` is moreover Nagata the normalization of the blowup is a finite morphism,
and normality of the blowup is exactly the assertion that this normalization morphism is an
isomorphism. For `A` regular the blowup is a regular, hence normal, scheme.

The chart itself is `AlgebraicGeometry.blowUpAffineChart`: the spectrum of the affine blowup
algebra attached to an affine open `U` of the base and a section `a` of the ideal over `U`, as an
open subscheme of the blowup.

## Main results

* `affineBlowup_top`: the affine blowup algebra of the unit ideal at `a` is the whole
  localization away from `a`.
* `isNormalRing_of_subsingleton`: a ring with at most one element is a normal ring.
* `AlgebraicGeometry.exists_blowUpAffineChart_eq`: the charts over the members of an affine open
  covering of the base jointly cover the blowup.
* `AlgebraicGeometry.isNormal_blowUp_of_isNormalRing_affineBlowupAlgebra`: the blowup is normal
  if the affine blowup algebras over one affine open covering of the base are normal rings.
* `AlgebraicGeometry.isNormalRing_affineBlowupAlgebra_of_isNormal_blowUp`: conversely, every
  affine blowup algebra of a normal blowup is a normal ring, so the criterion is an equivalence
  (`AlgebraicGeometry.isNormal_blowUp_iff_forall_isNormalRing_affineBlowupAlgebra`).
* `AlgebraicGeometry.isNormal_blowUp_ofIdealTop_iff`: over an affine base the single covering
  member `⊤` suffices, so normality of the blowup in an ideal of the global sections is exactly
  normality of the affine blowup algebras of that ideal.
* `AlgebraicGeometry.isNormal_blowUp_maximalIdeal_iff` and
  `AlgebraicGeometry.isNormal_blowUp_maximalIdeal_rationalSingularitySituation_iff`: the same
  statement for the blowup of `Spec(A)` in the maximal ideal of a local ring `A`, which is the
  shape in which normality of the blowup of a rational surface singularity is asked for.
* `AlgebraicGeometry.isNormal_blowUp_ofIdealTop_iff_isIntegrallyClosed`,
  `AlgebraicGeometry.isNormal_blowUp_maximalIdeal_iff_isIntegrallyClosed` and the corresponding
  statement for the rational singularity situation: over a domain the condition sharpens to
  integral closedness of each affine blowup algebra, since those algebras are automatically
  domains.
* `AlgebraicGeometry.isNormal_blowUp_ofIdealTop_top` and
  `AlgebraicGeometry.isNormal_blowUp_ofIdealTop_top_int`: the condition holds, non-degenerately,
  for the blowup of the spectrum of a normal ring in the unit ideal — in particular for `Spec ℤ`.
* `AlgebraicGeometry.isNormal_blowUp_maximalIdeal_field`: it holds degenerately for the maximal
  ideal of a field, where the blowup is empty.
* `AlgebraicGeometry.maximalIdealSheaf_ne_bot`,
  `AlgebraicGeometry.isIntegral_blowUp_maximalIdeal` and
  `AlgebraicGeometry.isModification_blowUpToBase_maximalIdeal`: for a two-dimensional local
  Noetherian domain the centre is a nonzero ideal, so the blowup is an integral scheme and the
  blowup morphism is a modification of `Spec(A)`.
* `AlgebraicGeometry.finite_irreducibleComponents_blowUp_spec` and
  `AlgebraicGeometry.isFinite_normalization_blowUp_maximalIdeal`: the blowup of the spectrum of a
  Noetherian ring has a normalization, and that normalization is a finite morphism when the ring
  is Nagata, the blowup then being a Nagata scheme.
* `AlgebraicGeometry.isNormal_normalizationScheme_blowUp_maximalIdeal` and
  `AlgebraicGeometry.isModification_normalization_comp_blowUpToBase_maximalIdeal`: over a
  two-dimensional local Nagata domain the normalization of that blowup is a normal modification
  of `Spec(A)`.
* `AlgebraicGeometry.isNormal_blowUp_maximalIdeal_iff_isIso_normalization`: normality of the
  blowup is exactly the assertion that its normalization morphism is an isomorphism.
* `AlgebraicGeometry.finite_irreducibleComponents_fiber_closedPoint`: the special fibre of a
  proper morphism to the spectrum of a Noetherian local ring has finitely many irreducible
  components, so the enumeration asked for by Situation 0B4W always exists.
* `AlgebraicGeometry.rationalSingularitySituationOfModification` and
  `AlgebraicGeometry.rationalSingularitySituationNormalizedBlowUp`: Situation 0B4W at an
  arbitrary normal modification, and at the normalization of the blowup in the maximal ideal.
* `AlgebraicGeometry.isNormal_blowUp_maximalIdeal_of_isRegularLocalRing`: for a two-dimensional
  regular local ring the blowup in the maximal ideal is normal, the blowup being regular.

## Implementation notes

`AlgebraicGeometry.blowUpAffineChart` is the composition of three morphisms already in the
library: the identification
`AlgebraicGeometry.affineBlowupStandardOpenIso` of the spectrum of the affine blowup algebra
with a standard open of the projective spectrum of the local Rees algebra, the inclusion of that
standard open, and the chart `Stacks.RelativeProj.Situation.relativeProjChart` of the relative
projective spectrum over the affine open. It is therefore an open immersion, and the local rings
of the blowup along it are the local rings of the affine blowup algebra; the covering statement
is `AlgebraicGeometry.blownUpAffine_chart_cover` together with the fact that the affine opens of
the base cover it.

The criterion is phrased with `IsNormalRing`, not with `IsIntegrallyClosed`, because the affine
blowup algebra of an ideal of a ring that is not a domain need not be a domain, and normality of
a scheme is the condition that the local rings are normal domains rather than a condition on the
global sections of a chart. Phrased that way it is an equivalence rather than a sufficient
condition: the spectrum of each affine blowup algebra is an open subscheme of the blowup, so the
condition is also necessary.

In the statement for a local ring the ideal sheaf is the one generated over the whole space by
the image of the maximal ideal under `AlgebraicGeometry.Scheme.ΓSpecIso`, so the affine blowup
algebras appearing there are those of that image: the canonical isomorphism `Γ(Spec A, ⊤) ≅ A`
carries it to the maximal ideal of `A`, and the condition says that each `A[𝔪/a]` is a normal
ring.

## References

* [Stacks Project, Tag 052Q](https://stacks.math.columbia.edu/tag/052Q)
* [Stacks Project, Tag 0804](https://stacks.math.columbia.edu/tag/0804)
* [Stacks Project, Tag 033I](https://stacks.math.columbia.edu/tag/033I)
* [Stacks Project, Tag 02ND](https://stacks.math.columbia.edu/tag/02ND)
* [Stacks Project, Tag 035S](https://stacks.math.columbia.edu/tag/035S)
* [Stacks Project, Tag 0AGR](https://stacks.math.columbia.edu/tag/0AGR)
* [Stacks Project, Tag 0B4Z](https://stacks.math.columbia.edu/tag/0B4Z)
* [Stacks Project, Tag 0H7D](https://stacks.math.columbia.edu/tag/0H7D)
-/

@[expose] public noncomputable section

universe v u

/-- The affine blowup algebra of the **unit** ideal at `a` is the whole localization away from
`a`: the fraction `1 / a` is one of its generators, so it contains every `x / aⁿ`. -/
public theorem affineBlowup_top {R : Type u} [CommRing R] (a : R) :
    affineBlowup (⊤ : Ideal R) a = ⊤ := by
  refine Algebra.eq_top_iff.2 fun z => ?_
  rw [affineBlowup_mem_iff _ _ Submodule.mem_top]
  induction z using Localization.induction_on with
  | H x =>
    obtain ⟨n, hn⟩ := x.2.2
    exact ⟨n, x.1, by rw [Ideal.top_pow]; exact Submodule.mem_top,
      by congr 1; exact Subtype.ext hn.symm⟩

/-- A ring with at most one element is a normal ring: it has no prime ideals. -/
public theorem isNormalRing_of_subsingleton (R : Type u) [CommRing R] [Subsingleton R] :
    IsNormalRing R := by
  intro p hp
  exact absurd (Ideal.eq_top_iff_one p |>.2
    (by rw [Subsingleton.elim (1 : R) 0]; exact p.zero_mem)) hp.ne_top

namespace AlgebraicGeometry

open CategoryTheory TopologicalSpace

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- Every point of the blowup lies on an affine chart attached to a member of a given affine open
covering of the base. -/
public theorem exists_blowUpAffineChart_eq {ι : Type v} (U : ι → X.affineOpens)
    (hU : ⨆ i, (U i : X.Opens) = ⊤) (x : blowUp I) :
    ∃ (i : ι) (a : I.ideal (U i))
      (w : Spec (.of (affineBlowupAlgebra (I.ideal (U i))
        (a : X.presheaf.obj (.op (U i).1))
        (Localization.Away (a : X.presheaf.obj (.op (U i).1)))))),
      (blowUpAffineChart I (U i) a).base w = x := by
  obtain ⟨i, hi⟩ : ∃ i, blowUpToBase I x ∈ (U i).1 := by
    have hmem : blowUpToBase I x ∈ (⊤ : X.Opens) := trivial
    rw [← hU] at hmem
    exact Opens.mem_iSup.mp hmem
  have hx : x ∈ (blowUpToBase I ⁻¹ᵁ (U i).1).1 := hi
  rw [← blownUpAffine_chart_cover I (U i)] at hx
  obtain ⟨a, z, hz⟩ := Set.mem_iUnion.mp hx
  refine ⟨i, a, (affineBlowupStandardOpenIso I (U i) a).inv.base z, ?_⟩
  show ((affineBlowupStandardOpenIso I (U i) a).hom ≫
    (Proj.basicOpen ((reesSituation I).sectionRingGrading (U i).1)
      (reesDegreeOne I (U i) a).1).ι ≫
    Stacks.RelativeProj.Situation.relativeProjChart (reesSituation I) (U i)).base _ = x
  rw [Scheme.Hom.comp_apply]
  have hid : (affineBlowupStandardOpenIso I (U i) a).hom.base
      ((affineBlowupStandardOpenIso I (U i) a).inv.base z) = z := by
    rw [← Scheme.Hom.comp_apply, (affineBlowupStandardOpenIso I (U i) a).inv_hom_id]
    rfl
  rwa [hid]

/-- **The blowup of `X` in `I` is normal as soon as the affine blowup algebras over one affine
open covering of `X` are normal rings.** -/
public theorem isNormal_blowUp_of_isNormalRing_affineBlowupAlgebra {ι : Type v}
    (U : ι → X.affineOpens) (hU : ⨆ i, (U i : X.Opens) = ⊤)
    (h : ∀ (i : ι) (a : X.presheaf.obj (.op (U i).1)), a ∈ I.ideal (U i) →
      IsNormalRing (affineBlowupAlgebra (I.ideal (U i)) a (Localization.Away a))) :
    IsNormal (blowUp I) := by
  refine (isNormal_iff_stalk_normal (blowUp I)).2 fun x => ?_
  obtain ⟨i, a, w, hw⟩ := exists_blowUpAffineChart_eq I U hU x
  have hchart : IsNormal (Spec (.of (affineBlowupAlgebra (I.ideal (U i))
      (a : X.presheaf.obj (.op (U i).1))
      (Localization.Away (a : X.presheaf.obj (.op (U i).1)))))) :=
    isNormal_spec_of_isNormalRing (h i a a.2)
  have hres := normal_of_equiv
    (asIso ((blowUpAffineChart I (U i) a).stalkMap w)).commRingCatIsoToRingEquiv.symm
    ((isNormal_iff_stalk_normal _).mp hchart w)
  rwa [hw] at hres

/-- A ring whose spectrum is a normal scheme is a normal ring. -/
public theorem isNormalRing_of_isNormal_spec {R : Type u} [CommRing R]
    (h : IsNormal (Spec (.of R))) : IsNormalRing R := by
  have hiff : IsNormal (Spec (CommRingCat.of R)) ↔
      ∀ U : (Spec (CommRingCat.of R)).affineOpens,
        IsNormalRing Γ(Spec (CommRingCat.of R), U) :=
    (isNormal_tfae (Spec (CommRingCat.of R))).out 1 2
  exact IsNormalRing.congr (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
    (hiff.mp h ⟨⊤, isAffineOpen_top _⟩)

/-- **Conversely, every affine blowup algebra of a normal blowup is a normal ring:** its spectrum
is an open subscheme of the blowup, so its local rings are local rings of the blowup. -/
public theorem isNormalRing_affineBlowupAlgebra_of_isNormal_blowUp (hI : IsNormal (blowUp I))
    (U : X.affineOpens) (a : X.presheaf.obj (.op U.1)) (ha : a ∈ I.ideal U) :
    IsNormalRing (affineBlowupAlgebra (I.ideal U) a (Localization.Away a)) := by
  refine isNormalRing_of_isNormal_spec ((isNormal_iff_stalk_normal _).2 fun w => ?_)
  exact normal_of_equiv
    (asIso ((blowUpAffineChart I U ⟨a, ha⟩).stalkMap w)).commRingCatIsoToRingEquiv
    ((isNormal_iff_stalk_normal _).mp hI _)

/-- **Normality of a blowup is exactly normality of all of its affine blowup algebras.** -/
public theorem isNormal_blowUp_iff_forall_isNormalRing_affineBlowupAlgebra :
    IsNormal (blowUp I) ↔ ∀ (U : X.affineOpens) (a : X.presheaf.obj (.op U.1)),
      a ∈ I.ideal U →
        IsNormalRing (affineBlowupAlgebra (I.ideal U) a (Localization.Away a)) :=
  ⟨fun h => isNormalRing_affineBlowupAlgebra_of_isNormal_blowUp I h,
    fun h => isNormal_blowUp_of_isNormalRing_affineBlowupAlgebra I id
      (iSup_affineOpens_eq_top X) h⟩

/-- **Over an affine base a single chart family suffices:** the blowup of an affine scheme in the
ideal sheaf generated by an ideal `J` of its global sections is normal exactly when every affine
blowup algebra of `J` is a normal ring. -/
public theorem isNormal_blowUp_ofIdealTop_iff {X : Scheme.{u}} [IsAffine X]
    (J : Ideal Γ(X, ⊤)) :
    IsNormal (blowUp (Scheme.IdealSheafData.ofIdealTop J)) ↔
      ∀ a ∈ J, IsNormalRing (affineBlowupAlgebra J a (Localization.Away a)) := by
  have hJ : (Scheme.IdealSheafData.ofIdealTop J).ideal ⟨⊤, isAffineOpen_top X⟩ = J := by simp
  constructor
  · intro hb a ha
    have hb' := isNormalRing_affineBlowupAlgebra_of_isNormal_blowUp _ hb
      ⟨⊤, isAffineOpen_top X⟩ a (by rwa [hJ])
    rwa [hJ] at hb'
  · refine fun h => isNormal_blowUp_of_isNormalRing_affineBlowupAlgebra _
      (fun _ : PUnit.{u + 1} => (⟨⊤, isAffineOpen_top X⟩ : X.affineOpens)) (by simp) ?_
    intro _ a ha
    rw [hJ] at ha ⊢
    exact h a ha

/-- **Normality of the blowup of the spectrum of a local ring in its maximal ideal is exactly
normality of its affine blowup algebras.** This is the shape in which normality of the blowup of
a rational surface singularity is asked for; the canonical isomorphism `Γ(Spec A, ⊤) ≅ A` carries
the ideal appearing here to the maximal ideal of `A`, so the right-hand side says that every
`A[𝔪/a]` is a normal ring. -/
public theorem isNormal_blowUp_maximalIdeal_iff (A : Type u) [CommRing A] [IsLocalRing A] :
    IsNormal (blowUp (Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (IsLocalRing.maximalIdeal A)))) ↔
      ∀ a ∈ Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (IsLocalRing.maximalIdeal A),
        IsNormalRing (affineBlowupAlgebra
          (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (IsLocalRing.maximalIdeal A))
          a (Localization.Away a)) :=
  isNormal_blowUp_ofIdealTop_iff _

/-- **In the rational singularity situation, the blowup of `Spec(A)` in the maximal ideal is
normal exactly when its affine blowup algebras are normal rings.** The left-hand side is
normality of the blowup of the spectrum of the two-dimensional local normal Nagata domain of the
situation in its maximal ideal; the right-hand side is the remaining content, namely that each
affine blowup algebra of that maximal ideal is a normal ring. -/
public theorem isNormal_blowUp_maximalIdeal_rationalSingularitySituation_iff
    (S : RationalSingularitySituation.{u}) :
    IsNormal (blowUp (Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (.of S.A)).inv.hom S.maximalIdeal))) ↔
      ∀ a ∈ Ideal.map (Scheme.ΓSpecIso (.of S.A)).inv.hom S.maximalIdeal,
        IsNormalRing (affineBlowupAlgebra
          (Ideal.map (Scheme.ΓSpecIso (.of S.A)).inv.hom S.maximalIdeal)
          a (Localization.Away a)) :=
  isNormal_blowUp_maximalIdeal_iff S.A

/-- **The criterion is satisfiable at a concrete object, and not only degenerately:** for a
normal ring `R` the blowup of `Spec R` in the unit ideal has normal affine blowup algebras, so it
is normal. Every chart is the whole localization away from its parameter, hence a localization of
`R`, hence a normal ring; the blowup itself is `Spec R` again, since the support of the unit ideal
is empty. -/
public theorem isNormal_blowUp_ofIdealTop_top (R : Type u) [CommRing R] (hR : IsNormalRing R) :
    IsNormal (blowUp (Scheme.IdealSheafData.ofIdealTop
      (⊤ : Ideal Γ(Spec (.of R), ⊤)))) := by
  have hΓ : IsNormalRing Γ(Spec (CommRingCat.of R), ⊤) :=
    IsNormalRing.congr (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv hR
  refine (isNormal_blowUp_ofIdealTop_iff _).2 fun a _ => ?_
  rw [affineBlowupAlgebra_eq_basicBlowup, affineBlowup_top]
  exact IsNormalRing.congr Subalgebra.topEquiv.toRingEquiv.symm
    (hΓ.isLocalization (Submonoid.powers a) (Localization.Away a))

/-- The affine blowup algebra at `0` is a normal ring: it is the zero ring. -/
private theorem isNormalRing_affineBlowupAlgebra_zero {R : Type u} [CommRing R] (J : Ideal R) :
    IsNormalRing (affineBlowupAlgebra J 0 (Localization.Away (0 : R))) := by
  have : Subsingleton (Localization.Away (0 : R)) :=
    IsLocalization.subsingleton (M := Submonoid.powers (0 : R)) ⟨1, pow_one 0⟩
  exact isNormalRing_of_subsingleton _

/-- **Over a domain the criterion sharpens to integral closedness.** The affine blowup algebra
of an ideal of a domain at a nonzero element is a domain (Tag 052R), and at `0` it has one
element, so the only remaining condition on each chart is that it is integrally closed. -/
public theorem isNormal_blowUp_ofIdealTop_iff_isIntegrallyClosed {X : Scheme.{u}} [IsAffine X]
    [IsDomain Γ(X, ⊤)] (J : Ideal Γ(X, ⊤)) :
    IsNormal (blowUp (Scheme.IdealSheafData.ofIdealTop J)) ↔
      ∀ a ∈ J, IsIntegrallyClosed (affineBlowupAlgebra J a (Localization.Away a)) := by
  rw [isNormal_blowUp_ofIdealTop_iff]
  refine ⟨fun h a ha => (h a ha).isIntegrallyClosed, fun h a ha => ?_⟩
  by_cases h0 : a = 0
  · subst h0
    exact isNormalRing_affineBlowupAlgebra_zero J
  · have hic := h a ha
    rw [affineBlowupAlgebra_eq_basicBlowup] at hic ⊢
    let : IsDomain (affineBlowup J a) := affineBlowup_isDomain J a h0
    let : IsIntegrallyClosed (affineBlowup J a) := hic
    exact IsNormalRing.of_isIntegrallyClosed _

/-- **The blowup of the spectrum of a local domain in its maximal ideal is normal exactly when
each of its affine blowup algebras is integrally closed.** -/
public theorem isNormal_blowUp_maximalIdeal_iff_isIntegrallyClosed (A : Type u) [CommRing A]
    [IsLocalRing A] [IsDomain A] :
    IsNormal (blowUp (Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (IsLocalRing.maximalIdeal A)))) ↔
      ∀ a ∈ Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (IsLocalRing.maximalIdeal A),
        IsIntegrallyClosed (affineBlowupAlgebra
          (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (IsLocalRing.maximalIdeal A))
          a (Localization.Away a)) := by
  let : IsDomain Γ(Spec (CommRingCat.of A), ⊤) :=
    Function.Injective.isDomain
      ((Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv : _ →+* A)
      (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.injective
  exact isNormal_blowUp_ofIdealTop_iff_isIntegrallyClosed _

/-- **In the rational singularity situation, normality of the blowup of `Spec(A)` in the maximal
ideal is exactly integral closedness of each affine blowup algebra `A[𝔪/a]`.** This is the
sharpest form of the reduction: the left-hand side is the conclusion of Stacks Tag 0B4Z and the
right-hand side is all that remains to be proved, which in the source is obtained from the
identification `H⁰(X', (ℐ')ⁿ) = 𝔪ⁿ` of Tag 0B4Y. -/
public theorem isNormal_blowUp_maximalIdeal_rationalSingularitySituation_iff_isIntegrallyClosed
    (S : RationalSingularitySituation.{u}) :
    IsNormal (blowUp (Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (.of S.A)).inv.hom S.maximalIdeal))) ↔
      ∀ a ∈ Ideal.map (Scheme.ΓSpecIso (.of S.A)).inv.hom S.maximalIdeal,
        IsIntegrallyClosed (affineBlowupAlgebra
          (Ideal.map (Scheme.ΓSpecIso (.of S.A)).inv.hom S.maximalIdeal)
          a (Localization.Away a)) :=
  isNormal_blowUp_maximalIdeal_iff_isIntegrallyClosed S.A

/-- A concrete non-degenerate witness for `isNormal_blowUp_ofIdealTop_top`: the blowup of
`Spec ℤ` in the unit ideal is normal. -/
public theorem isNormal_blowUp_ofIdealTop_top_int :
    IsNormal (blowUp (Scheme.IdealSheafData.ofIdealTop
      (⊤ : Ideal Γ(Spec (.of ℤ), ⊤)))) :=
  isNormal_blowUp_ofIdealTop_top ℤ (IsNormalRing.of_isIntegrallyClosed ℤ)

/-- The maximal-ideal form holds for a field, degenerately: the maximal ideal is zero, so the
only affine blowup algebra is the localization away from `0`, which has one element. The blowup
is empty, so this witness says nothing about the non-degenerate case. -/
public theorem isNormal_blowUp_maximalIdeal_field (k : Type u) [Field k] :
    IsNormal (blowUp (Scheme.IdealSheafData.ofIdealTop
      (Ideal.map (Scheme.ΓSpecIso (.of k)).inv.hom (IsLocalRing.maximalIdeal k)))) := by
  refine (isNormal_blowUp_maximalIdeal_iff k).2 fun a ha => ?_
  rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.map_bot] at ha ⊢
  obtain rfl := Ideal.mem_bot.mp ha
  exact isNormalRing_affineBlowupAlgebra_zero _

/-! ### Instantiating Situation 0B4W at a normal modification

The irreducible components of the special fibre can always be enumerated: the fibre is a closed
subspace of the source, which is Noetherian because the morphism is proper over the spectrum of
a Noetherian ring. -/

/-- The special fibre of a proper morphism to the spectrum of a Noetherian local ring has
finitely many irreducible components: it is a closed subspace of a Noetherian scheme. -/
public theorem finite_irreducibleComponents_fiber_closedPoint (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f] :
    Finite {Z : Set (f.fiber (IsLocalRing.closedPoint A)) //
      Z ∈ irreducibleComponents (f.fiber (IsLocalRing.closedPoint A))} := by
  have : IsNoetherianRing (CommRingCat.of A) := ‹IsNoetherianRing A›
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X := {}
  have : IsClosedImmersion ((Spec (CommRingCat.of A)).fromSpecResidueField
      (IsLocalRing.closedPoint A)) :=
    isClosed_singleton_iff_isClosedImmersion.mp
      (IsLocalRing.isClosed_singleton_closedPoint A)
  have hci : IsClosedImmersion (f.fiberι (IsLocalRing.closedPoint A)) :=
    inferInstanceAs (IsClosedImmersion (Limits.pullback.fst f _))
  have : NoetherianSpace (f.fiber (IsLocalRing.closedPoint A)) :=
    (f.fiberι (IsLocalRing.closedPoint A)).isClosedEmbedding.isInducing.noetherianSpace
  exact NoetherianSpace.finite_irreducibleComponents.to_subtype

/-- **Situation 0B4W at a given normal modification.** A two-dimensional local normal Nagata
domain defining a rational singularity together with a normal modification of its spectrum is
all the data Situation 0B4W needs: the enumeration of the components of the special fibre is
supplied by their finiteness. -/
public def rationalSingularitySituationOfModification (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNormalDomain A] (hnag : IsNagataRing A) (hdim : ringKrullDim A = 2)
    (hrat : DefinesRationalSingularity A) {X : Scheme.{u}} [IsNormal X]
    (f : X ⟶ Spec (.of A)) (hf : IsModification f) : RationalSingularitySituation.{u} :=
  have : IsNoetherianRing A := hnag.1
  have : IsProper f := hf.isProper
  have := finite_irreducibleComponents_fiber_closedPoint A f
  { A := A
    nagata := hnag
    dimension_two := hdim
    definesRationalSingularity := hrat
    X := X
    f := f
    modification := hf
    numberOfComponents := Nat.card {Z : Set (f.fiber (IsLocalRing.closedPoint A)) //
      Z ∈ irreducibleComponents (f.fiber (IsLocalRing.closedPoint A))}
    components := (Finite.equivFin _).symm }

/-! ### The blowup of a two-dimensional local ring in its maximal ideal -/

/-- The ideal sheaf generated by the maximal ideal of a local ring of Krull dimension two is
nonzero: the ring is not a field, and `Γ(Spec A, ⊤) ≅ A` is injective on ideals. -/
public theorem maximalIdealSheaf_ne_bot (A : Type u) [CommRing A] [IsLocalRing A]
    (hdim : ringKrullDim A = 2) :
    Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (IsLocalRing.maximalIdeal A)) ≠ ⊥ := by
  have hmax : IsLocalRing.maximalIdeal A ≠ ⊥ := by
    intro hm
    have hfield : IsField A := IsLocalRing.isField_iff_maximalIdeal_eq.mpr hm
    have hbad : (2 : WithBot ℕ∞) = 0 :=
      hdim.symm.trans (ringKrullDim_eq_zero_of_isField hfield)
    exact (by norm_num : (2 : WithBot ℕ∞) ≠ 0) hbad
  have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom := by
    intro r r' h
    have h' := congrArg (fun w => (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom w) h
    simpa using h'
  intro h
  have htop := congrArg
    (fun J : (Spec (CommRingCat.of A)).IdealSheafData =>
      J.ideal ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of A))⟩) h
  have hbot : Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
      (IsLocalRing.maximalIdeal A) = ⊥ := by
    simpa [Scheme.IdealSheafData.ofIdealTop_ideal] using htop
  exact hmax ((Ideal.map_eq_bot_iff_of_injective hinj).mp hbot)

/-- **The blowup of the spectrum of a two-dimensional local domain in its maximal ideal is an
integral scheme**, being the blowup of an integral scheme in a nonzero ideal. -/
public theorem isIntegral_blowUp_maximalIdeal (A : Type u) [CommRing A] [IsLocalRing A]
    [IsDomain A] (hdim : ringKrullDim A = 2) :
    IsIntegral (blowUp (Scheme.IdealSheafData.ofIdealTop
      (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (IsLocalRing.maximalIdeal A)))) :=
  isIntegral_blowUp _ (maximalIdealSheaf_ne_bot A hdim)

/-- **The blowup of the spectrum of a two-dimensional local Noetherian domain in its maximal
ideal is a modification of that spectrum:** it is birational, proper, and integral. -/
public theorem isModification_blowUpToBase_maximalIdeal (A : Type u) [CommRing A] [IsLocalRing A]
    [IsDomain A] [IsNoetherianRing A] (hdim : ringKrullDim A = 2) :
    IsModification (blowUpToBase (Scheme.IdealSheafData.ofIdealTop
      (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (IsLocalRing.maximalIdeal A)))) := by
  have : IsNoetherianRing (CommRingCat.of A) := ‹IsNoetherianRing A›
  exact ⟨isBirational_blowUpToBase _ (maximalIdealSheaf_ne_bot A hdim), inferInstance,
    isIntegral_blowUp_maximalIdeal A hdim⟩

/-- Quasi-compact opens of a blowup of the spectrum of a Noetherian ring have finitely many
irreducible components, which is the hypothesis under which the blowup has a normalization. -/
public theorem finite_irreducibleComponents_blowUp_spec (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : (Spec (CommRingCat.of A)).IdealSheafData) :
    ∀ U : (blowUp I).Opens, IsCompact (U : Set (blowUp I)) →
      (irreducibleComponents U).Finite :=
  Stacks.Blowup.finite_irreducibleComponents_blowUp I fun U _ =>
    @NoetherianSpace.finite_irreducibleComponents (U : Set (Spec (CommRingCat.of A))) _
      inferInstance

/-- **The normalization of the blowup of the spectrum of a local Nagata ring in its maximal ideal
is finite:** the blowup is locally of finite type over a Nagata scheme, hence Nagata, and the
normalization of a Nagata scheme is finite. -/
public theorem isFinite_normalization_blowUp_maximalIdeal (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNagataRing A] :
    IsFinite (Scheme.normalization (blowUp (Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (IsLocalRing.maximalIdeal A))))
      (finite_irreducibleComponents_blowUp_spec A _)) := by
  have : IsNoetherianRing (CommRingCat.of A) := inferInstance
  exact Scheme.isFinite_normalization
    (isNagataScheme_of_locallyOfFiniteType
      (blowUpToBase (Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (IsLocalRing.maximalIdeal A))))
      (isNagataScheme_spec_of_isNagataRing A ‹IsNagataRing A›))
    (finite_irreducibleComponents_blowUp_spec A _)

/-- **The normalization of the blowup of the spectrum of a Noetherian local ring in its maximal
ideal is a normal scheme**, every normalization being normal. -/
public theorem isNormal_normalizationScheme_blowUp_maximalIdeal (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] :
    IsNormal (Scheme.normalizationScheme (blowUp (Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (IsLocalRing.maximalIdeal A))))
      (finite_irreducibleComponents_blowUp_spec A _)) :=
  Scheme.isNormal_normalizationScheme _ _

/-- **The normalization of the blowup of the spectrum of a two-dimensional local Nagata domain in
its maximal ideal is a modification of that spectrum:** the blowup morphism is birational and
proper, and the normalization morphism is birational and finite. -/
public theorem isModification_normalization_comp_blowUpToBase_maximalIdeal (A : Type u)
    [CommRing A] [IsLocalRing A] [IsDomain A] [IsNagataRing A] (hdim : ringKrullDim A = 2) :
    IsModification (Scheme.normalization (blowUp (Scheme.IdealSheafData.ofIdealTop
          (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (IsLocalRing.maximalIdeal A))))
        (finite_irreducibleComponents_blowUp_spec A _) ≫
      blowUpToBase (Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (IsLocalRing.maximalIdeal A)))) := by
  have : IsNoetherianRing (CommRingCat.of A) := inferInstance
  have : IsIntegral (blowUp (Scheme.IdealSheafData.ofIdealTop
      (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (IsLocalRing.maximalIdeal A)))) :=
    isIntegral_blowUp_maximalIdeal A hdim
  have := isFinite_normalization_blowUp_maximalIdeal A
  exact ⟨(Scheme.isBirational_normalization _ _).comp
      (isBirational_blowUpToBase _ (maximalIdealSheaf_ne_bot A hdim)),
    inferInstance, inferInstance⟩

/-- **Situation 0B4W at the normalization of the blowup in the maximal ideal.** For a
two-dimensional local normal Nagata domain defining a rational singularity, the normalization of
the blowup of its spectrum in the maximal ideal is a normal modification of that spectrum, so it
is a legitimate choice of `X` in Situation 0B4W. -/
public def rationalSingularitySituationNormalizedBlowUp (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNormalDomain A] (hnag : IsNagataRing A) (hdim : ringKrullDim A = 2)
    (hrat : DefinesRationalSingularity A) : RationalSingularitySituation.{u} :=
  have : IsNoetherianRing A := hnag.1
  have : IsNagataRing A := hnag
  have : IsNormal (Scheme.normalizationScheme (blowUp (Scheme.IdealSheafData.ofIdealTop
      (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (IsLocalRing.maximalIdeal A))))
    (finite_irreducibleComponents_blowUp_spec A _)) :=
    isNormal_normalizationScheme_blowUp_maximalIdeal A
  rationalSingularitySituationOfModification A hnag hdim hrat _
    (isModification_normalization_comp_blowUpToBase_maximalIdeal A hdim)

/-- The source of Situation 0B4W at the normalized blowup is the normalization of the blowup. -/
@[simp]
public theorem rationalSingularitySituationNormalizedBlowUp_X (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNormalDomain A] (hnag : IsNagataRing A) (hdim : ringKrullDim A = 2)
    (hrat : DefinesRationalSingularity A) :
    (rationalSingularitySituationNormalizedBlowUp A hnag hdim hrat).X =
      Scheme.normalizationScheme (blowUp (Scheme.IdealSheafData.ofIdealTop
          (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (IsLocalRing.maximalIdeal A))))
        (finite_irreducibleComponents_blowUp_spec A _) := rfl

/-- The morphism of Situation 0B4W at the normalized blowup is the normalization followed by the
blowup morphism. -/
@[simp]
public theorem rationalSingularitySituationNormalizedBlowUp_f (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNormalDomain A] (hnag : IsNagataRing A) (hdim : ringKrullDim A = 2)
    (hrat : DefinesRationalSingularity A) :
    (rationalSingularitySituationNormalizedBlowUp A hnag hdim hrat).f =
      Scheme.normalization (blowUp (Scheme.IdealSheafData.ofIdealTop
            (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (IsLocalRing.maximalIdeal A))))
          (finite_irreducibleComponents_blowUp_spec A _) ≫
        blowUpToBase (Scheme.IdealSheafData.ofIdealTop
          (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (IsLocalRing.maximalIdeal A))) := rfl

/-- **Normality of the blowup of the spectrum of a Noetherian local ring in its maximal ideal is
exactly the assertion that the normalization morphism of the blowup is an isomorphism.** -/
public theorem isNormal_blowUp_maximalIdeal_iff_isIso_normalization (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] :
    IsNormal (blowUp (Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (IsLocalRing.maximalIdeal A)))) ↔
      IsIso (Scheme.normalization (blowUp (Scheme.IdealSheafData.ofIdealTop
          (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (IsLocalRing.maximalIdeal A))))
        (finite_irreducibleComponents_blowUp_spec A _)) :=
  (Scheme.isIso_normalization_iff_isNormal _ _).symm

/-- **The blowup of the spectrum of a two-dimensional regular local ring in its maximal ideal is
a normal scheme:** that blowup is a regular scheme, and every regular scheme is normal. -/
public theorem isNormal_blowUp_maximalIdeal_of_isRegularLocalRing (A : Type u) [CommRing A]
    [IsRegularLocalRing A] (hdim : ringKrullDim A = 2) :
    IsNormal (blowUp (Scheme.IdealSheafData.ofIdealTop
      (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (IsLocalRing.maximalIdeal A)))) :=
  isNormal_of_isRegular _ (isRegular_blowUp_maximalIdeal A hdim)

end AlgebraicGeometry

end
