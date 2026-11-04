module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityPowerSeriesFullyFaithful
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.RestrictionSectionwiseCriteria
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.Chain
import all StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityPowerSeriesFullyFaithful
public import StacksCore.Tactic.StacksAttribute

/-!
# Purity over a power series ring: full faithfulness of restriction

Let `(A, 𝔪)` be a Noetherian local ring of depth at least two, let `B = A[[x_1, …, x_d]]` with
`d ≥ 1`, set `Y = Spec B` and let `Y_0 = V(x_1, …, x_d) ≅ Spec A` be the closed fibre. For an
open `V ⊆ Y` whose intersection with `Y_0` is the punctured spectrum of `A`, the restriction
functor `FÉt_V ⟶ FÉt_{V ∩ Y_0}` is fully faithful [Stacks, Tag 0EY9].

## Main results

* `Stacks.FundamentalGroup.isInfinitesimalSectionsComplete_unit_mvPowerSeries`: the structure
  sheaf of `V` is infinitesimal section complete along `V ∩ Y_0`.
* `Stacks.FundamentalGroup.fullyFaithful_finiteEtaleBaseChange_restrict_mvPowerSeries`: the
  restriction functor `FÉt_V ⟶ FÉt_{V ∩ Y_0}` is fully faithful.

## References

* [Stacks Project, Tag 0EKP](https://stacks.math.columbia.edu/tag/0EKP)
* [Stacks Project, Tag 0EL8](https://stacks.math.columbia.edu/tag/0EL8)
* [Stacks Project, Tag 0EY9](https://stacks.math.columbia.edu/tag/0EY9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.RelativeSpec
open Stacks.Algebraization (IsInfinitesimalSectionsComplete nthInfinitesimalNeighbourhood)

universe u

namespace Stacks.FundamentalGroup

/-- The restriction to an open `V` of `Spec` of the constant coefficient map is a closed
immersion. -/
private theorem isClosedImmersion_restrict_spec_constantCoeff (A : Type u) [CommRing A] (d : ℕ)
    (V : (Spec (.of (MvPowerSeries (Fin d) A))).Opens) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (MvPowerSeries.constantCoeff : MvPowerSeries (Fin d) A →+* A)) ∣_ V) :=
  IsZariskiLocalAtTarget.restrict
    (IsClosedImmersion.spec_of_surjective _ fun a =>
      ⟨MvPowerSeries.C a, MvPowerSeries.constantCoeff_C a⟩) V

/-- **Functions on `V` are the completion along the punctured closed fibre.** Let `(A, 𝔪)` be a
Noetherian local ring of depth at least two, `B = A[[x_1, …, x_d]]`, and `V ⊆ Spec B` an open
meeting the closed fibre `Spec A ⟶ Spec B` exactly in the punctured spectrum of `A`. Then the
structure sheaf of `V` is infinitesimal section complete along `V ∩ Spec A`: `Γ(V, 𝒪_V)` is the
inverse limit of the functions on the infinitesimal neighbourhoods. -/
public theorem isInfinitesimalSectionsComplete_unit_mvPowerSeries (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (d : ℕ)
    (hdepth : (2 : ℕ∞) ≤ Module.depth A (IsLocalRing.maximalIdeal A) A)
    (V : (Spec (.of (MvPowerSeries (Fin d) A))).Opens)
    (hV : (Spec.map (CommRingCat.ofHom
        (MvPowerSeries.constantCoeff : MvPowerSeries (Fin d) A →+* A)) ⁻¹ᵁ V :
      Set (Spec (.of A))) = {IsLocalRing.closedPoint A}ᶜ) :
    haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom
        (MvPowerSeries.constantCoeff : MvPowerSeries (Fin d) A →+* A)) ∣_ V) :=
      IsZariskiLocalAtTarget.restrict
        (IsClosedImmersion.spec_of_surjective _ fun a =>
          ⟨MvPowerSeries.C a, MvPowerSeries.constantCoeff_C a⟩) V
    IsInfinitesimalSectionsComplete (Spec.map (CommRingCat.ofHom
        (MvPowerSeries.constantCoeff : MvPowerSeries (Fin d) A →+* A)) ∣_ V)
      (SheafOfModules.unit V.toScheme.ringCatSheaf) := by
  classical
  let B := MvPowerSeries (Fin d) A
  let Y : Scheme.{u} := Spec (.of B)
  let s : Spec (.of A) ⟶ Y :=
    Spec.map (CommRingCat.ofHom (MvPowerSeries.constantCoeff : B →+* A))
  let i := s ∣_ V
  have : IsClosedImmersion s := IsClosedImmersion.spec_of_surjective _ fun a =>
    ⟨MvPowerSeries.C a, MvPowerSeries.constantCoeff_C a⟩
  have : IsClosedImmersion i := isClosedImmersion_restrict_spec_constantCoeff A d V
  let J : Ideal B := RingHom.ker (MvPowerSeries.constantCoeff : B →+* A)
  have : IsAdicComplete J B := Stacks.MvPowerSeries.isAdicComplete_ker_constantCoeff A d
  let Q (n : ℕ) := B ⧸ J ^ (n + 1)
  let qq (n : ℕ) : Spec (.of (Q n)) ⟶ Y :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J ^ (n + 1))))
  have hqc (n : ℕ) : IsClosedImmersion (qq n) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hqk (n : ℕ) : (qq n).ker = s.ker ^ (n + 1) :=
    ker_specMap_pow _ _ _ Ideal.mk_ker
  have hQnoeth (n : ℕ) : IsNoetherianRing (Q n) := inferInstance
  have hQnt (n : ℕ) : Nontrivial (Q n) :=
    Stacks.MvPowerSeries.nontrivial_quotient_pow_ker_constantCoeff A d n
  have hQlocal (n : ℕ) : IsLocalRing (Q n) :=
    Stacks.MvPowerSeries.isLocalRing_quotient_pow_ker_constantCoeff A d n
  have hpunctured (n : ℕ) : (qq n ⁻¹ᵁ V : Set (Spec (.of (Q n)))) =
      {IsLocalRing.closedPoint (Q n)}ᶜ := by
    have := Stacks.MvPowerSeries.isLocalHom_constantCoeffQuotient A d n
    refine preimage_eq_punctured_of_ker_pow (Q n) A s (qq n)
      (Stacks.MvPowerSeries.constantCoeffQuotient A d n)
      (Stacks.MvPowerSeries.surjective_constantCoeffQuotient A d n) ?_ (n + 1) (by omega)
      (hqk n) V hV
    rw [← Spec.map_comp]
    congr 1
  have hdepthQ (n : ℕ) :
      (2 : ℕ∞) ≤ Module.depth (Q n) (IsLocalRing.maximalIdeal (Q n)) (Q n) :=
    hdepth.trans (Stacks.MvPowerSeries.le_depth_quotient_pow_ker_constantCoeff A d n)
  obtain ⟨e, he⟩ := Classical.axiomOfChoice (fun n : ℕ =>
    exists_ringEquiv_nthInfinitesimalNeighbourhood s V (Q n) (qq n) n (hqk n)
      (hpunctured n) (hdepthQ n))
  have hinv (a : B) : (Scheme.ΓSpecIso (.of B)).hom
      ((Scheme.ΓSpecIso (.of B)).inv a) = a :=
    (ConcreteCategory.comp_apply (Scheme.ΓSpecIso (.of B)).inv
        (Scheme.ΓSpecIso (.of B)).hom a).symm.trans
      (congrArg (fun φ : (CommRingCat.of B) ⟶ (CommRingCat.of B) => φ a)
        (Scheme.ΓSpecIso (.of B)).inv_hom_id)
  have hmk (n : ℕ) (a : B) :
      (Scheme.ΓSpecIso (.of (Q n))).hom
          ((qq n).appTop ((Scheme.ΓSpecIso (.of B)).inv a)) =
        Ideal.Quotient.mk (J ^ (n + 1)) a := by
    have hnat := Scheme.ΓSpecIso_naturality
      (CommRingCat.ofHom (Ideal.Quotient.mk (J ^ (n + 1))))
    have h2 := congrArg (fun φ : Γ(Spec (.of B), ⊤) ⟶ (CommRingCat.of (Q n)) =>
      φ ((Scheme.ΓSpecIso (.of B)).inv a)) hnat
    simp only [ConcreteCategory.comp_apply] at h2
    exact h2.trans (congrArg (fun z : B => Ideal.Quotient.mk (J ^ (n + 1)) z) (hinv a))
  refine isInfinitesimalSectionsComplete_of_quotientEquivs B J V
    (TopologicalSpace.NoetherianSpace.isCompact _) i e ?_
  intro n a
  exact (congrArg (e n) (hmk n a).symm).trans (he n ((Scheme.ΓSpecIso (.of B)).inv a))

/-- Let `(A, 𝔪)` be a Noetherian local ring of depth at least two, let `B = A[[x_1, …, x_d]]`
with `d ≥ 1`, set `Y = Spec B` and let `Y_0 = V(x_1, …, x_d)` be the closed fibre, the image of the
closed immersion `Spec A ⟶ Y` induced by the constant coefficient. For any open `V ⊆ Y` with
`V ∩ Y_0` the punctured spectrum of `A`, the restriction functor `FÉt_V ⟶ FÉt_{V ∩ Y_0}` is fully
faithful.

The condition on `V` is the hypothesis `hV`: the inverse image of `V` under the closed immersion
`Spec A ⟶ Y` is the complement of the closed point of `Spec A`. -/
@[stacks 0EY9 "the full statement under the source's hypotheses; nothing is assumed"]
public theorem fullyFaithful_finiteEtaleBaseChange_restrict_mvPowerSeries (A : Type u)
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (d : ℕ) (hd : 0 < d)
    (hdepth : (2 : ℕ∞) ≤ Module.depth A (IsLocalRing.maximalIdeal A) A)
    (V : (Spec (.of (MvPowerSeries (Fin d) A))).Opens)
    (hV : (Spec.map (CommRingCat.ofHom
        (MvPowerSeries.constantCoeff : MvPowerSeries (Fin d) A →+* A)) ⁻¹ᵁ V :
      Set (Spec (.of A))) = {IsLocalRing.closedPoint A}ᶜ) :
    Nonempty (finiteEtaleBaseChange (Spec.map (CommRingCat.ofHom
      (MvPowerSeries.constantCoeff : MvPowerSeries (Fin d) A →+* A)) ∣_ V)).FullyFaithful := by
  have : 0 < d := hd
  let s : Spec (.of A) ⟶ Spec (.of (MvPowerSeries (Fin d) A)) :=
    Spec.map (CommRingCat.ofHom
      (MvPowerSeries.constantCoeff : MvPowerSeries (Fin d) A →+* A))
  have : IsClosedImmersion (s ∣_ V) := isClosedImmersion_restrict_spec_constantCoeff A d V
  have : TopologicalSpace.NoetherianSpace V.toScheme :=
    V.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : IsNoetherian V.toScheme := AlgebraicGeometry.IsNoetherian.mk
  exact fullyFaithful_finiteEtaleBaseChange_of_completionEquivalence (s ∣_ V)
    (Stacks.Algebraization.completionFullyFaithful_of_sectionsCompleteQuasiAffine (s ∣_ V)
      ⟨Scheme.IsQuasiAffine.of_isImmersion (f := V.ι),
        isInfinitesimalSectionsComplete_unit_mvPowerSeries A d hdepth V hV⟩)

end Stacks.FundamentalGroup

end
