module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.RingTheory.Valuation.ValuationRing
public import StacksCore.Tactic.StacksAttribute

/-!
# Reaching points of a scheme-theoretic image by valuation rings

Let `f : X ⟶ Y` be a quasi-compact morphism of schemes. Every point `z` of the scheme-theoretic
image `f.image` is the image of the closed point of a valuation ring `A` under a morphism
`h : Spec A ⟶ f.image` which fits into a commutative square with a morphism
`g : Spec K ⟶ X` out of the fraction field of `A`. Consequently every point of the
scheme-theoretic image is a specialization of a point in the set-theoretic image of `f`.

## Main results

* `AlgebraicGeometry.exists_valuationRing_of_image_point`: the valuative diagram over a point of
  the scheme-theoretic image.
* `AlgebraicGeometry.exists_specializes_of_image_point`: the specialization that diagram yields.

## Implementation notes

The diagram is stated inside the scheme-theoretic image rather than in `Y`: the generic map
`g` followed by the canonical factorization `f.toImage` equals the composite through `Spec A`,
and the closed point of `A` maps to the prescribed point. Composing with `f.imageι` recovers
the displayed diagram over `Y`.

The proof reduces to the affine case by two `wlog` steps. For the target one passes to a member
of `Y.affineCover` and uses that the ideal sheaf `Hom.ker` of the base change along an open
immersion is the comap of `Hom.ker`; for the source one uses that `X` is quasi-compact over an
affine target, so that finitely many members of `X.affineCover` suffice and the supports of the
kernels of the restricted morphisms cover the support of `f.ker`. In the affine case the
valuation ring is produced by `IsLocalRing.exists_factor_valuationRing` applied to the map from
`R_p` to the residue field of a prime of `S` lying under `p`.

## References

* [Stacks Project, Tag 02JQ](https://stacks.math.columbia.edu/tag/02JQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits IsLocalRing TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The affine case of the valuative diagram: given a ring map `φ : R →+* S` and primes `p` of
`R` and `q` of `S` with `φ⁻¹ q ≤ p`, there is a valuation ring `A` with fraction field `K`
making the square over `Spec φ` commute and sending the closed point of `A` to `p`. -/
private theorem exists_valuationRing_diagram_of_comap_le
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hpq : q.asIdeal.comap φ ≤ p.asIdeal) :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : ValuationRing A)
      (K : Type u) (_ : Field K) (_ : Algebra A K) (_ : IsFractionRing A K)
      (g : Spec (.of K) ⟶ Spec (.of S)) (h : Spec (.of A) ⟶ Spec (.of R)),
      g ≫ Spec.map (CommRingCat.ofHom φ) =
        Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ h ∧
      h (closedPoint A) = p := by
  let K := q.asIdeal.ResidueField
  let _ : Field K := inferInstance
  let _ : IsLocalRing (Localization.AtPrime p.asIdeal) :=
    IsLocalization.AtPrime.isLocalRing (Localization.AtPrime p.asIdeal) p.asIdeal
  have hden : p.asIdeal.primeCompl ≤ Submonoid.comap φ q.asIdeal.primeCompl :=
    fun _ hs hq ↦ hs (hpq hq)
  let θ : Localization.AtPrime p.asIdeal →+* Localization.AtPrime q.asIdeal :=
    IsLocalization.map (Localization.AtPrime q.asIdeal) φ hden
  let ψ : Localization.AtPrime p.asIdeal →+* K :=
    (IsLocalRing.residue (Localization.AtPrime q.asIdeal)).comp θ
  let _ : Nontrivial K := inferInstance
  obtain ⟨V, hV, hVlocal⟩ := IsLocalRing.exists_factor_valuationRing ψ
  let A := V
  let _ : IsLocalRing A := V.isLocalRing
  let _ : Algebra A K := inferInstance
  let _ : IsFractionRing A K := inferInstance
  let ρ : Localization.AtPrime p.asIdeal →+* A := ψ.codRestrict V.toSubring hV
  let _ : IsLocalHom ρ := hVlocal
  let r : R →+* A := ρ.comp (algebraMap R (Localization.AtPrime p.asIdeal))
  let g : Spec (.of K) ⟶ Spec (.of S) :=
    Spec.map (CommRingCat.ofHom (algebraMap S K))
  let h : Spec (.of A) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom r)
  have hcomm : (algebraMap A K).comp r = (algebraMap S K).comp φ := by
    ext x
    show (IsLocalRing.residue (Localization.AtPrime q.asIdeal))
        (θ (algebraMap R (Localization.AtPrime p.asIdeal) x)) = algebraMap S K (φ x)
    have hθ : θ.comp (algebraMap R (Localization.AtPrime p.asIdeal)) =
        (algebraMap S (Localization.AtPrime q.asIdeal)).comp φ :=
      IsLocalization.map_comp hden
    calc
      _ = (IsLocalRing.residue (Localization.AtPrime q.asIdeal))
          ((algebraMap S (Localization.AtPrime q.asIdeal)) (φ x)) :=
            congrArg (IsLocalRing.residue (Localization.AtPrime q.asIdeal))
              (DFunLike.congr_fun hθ x)
      _ = algebraMap S K (φ x) :=
        IsScalarTower.algebraMap_apply S (Localization.AtPrime q.asIdeal) K (φ x)
  have hclosed : h (closedPoint A) = p := by
    show PrimeSpectrum.comap r (IsLocalRing.closedPoint A) = p
    rw [PrimeSpectrum.comap_comp]
    show PrimeSpectrum.comap (algebraMap R (Localization.AtPrime p.asIdeal))
      (PrimeSpectrum.comap ρ (IsLocalRing.closedPoint A)) = p
    rw [IsLocalRing.comap_closedPoint ρ]
    exact PrimeSpectrum.ext
      (IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime p.asIdeal) p.asIdeal)
  refine ⟨A, inferInstance, inferInstance, inferInstance,
    K, inferInstance, inferInstance, inferInstance, g, h, ?_, hclosed⟩
  show Spec.map (CommRingCat.ofHom (algebraMap S K)) ≫
      Spec.map (CommRingCat.ofHom φ) =
    Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ Spec.map (CommRingCat.ofHom r)
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext hcomm.symm)

/-- Every point of the support of the ideal sheaf `f.ker` of a quasi-compact morphism `f` is
reached by a valuation ring, in the sense that it is the image of the closed point of a morphism
`Spec A ⟶ Y` which, over the fraction field of `A`, factors through `X`. -/
public theorem exists_valuationRing_diagram_of_mem_support_ker
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] (y : Y)
    (hy : y ∈ f.ker.support) :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : ValuationRing A)
      (K : Type u) (_ : Field K) (_ : Algebra A K) (_ : IsFractionRing A K)
      (g : Spec (.of K) ⟶ X) (h : Spec (.of A) ⟶ Y),
      g ≫ f =
        Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ h ∧
      h (closedPoint A) = y := by
  wlog hY : ∃ R, Y = Spec R generalizing X Y
  · let 𝒰 := Y.affineCover
    obtain ⟨i, x, rfl⟩ := 𝒰.exists_eq y
    let hstable : MorphismProperty.IsStableUnderBaseChangeAlong
        (@QuasiCompact) (𝒰.f i) :=
      ⟨fun pb hqc ↦ quasiCompact_isStableUnderBaseChange.of_isPullback pb hqc⟩
    let hqc : QuasiCompact (pullback.snd f (𝒰.f i)) :=
      MorphismProperty.pullback_snd f (𝒰.f i) inferInstance
    have hx : x ∈ (pullback.snd f (𝒰.f i)).ker.support := by
      apply (𝒰.f i).isOpenEmbedding.injective.mem_set_image.mp
      have hs : ((pullback.snd f (𝒰.f i)).ker.support : Set (𝒰.X i)) =
          (𝒰.X i).zeroLocus
            (↑((pullback.snd f (𝒰.f i)).ker.ideal ⟨⊤, isAffineOpen_top _⟩) :
              Set Γ(𝒰.X i, ⊤)) := by
        ext t
        exact Scheme.IdealSheafData.mem_support_iff_of_mem (by simp)
      rw [hs, Scheme.image_zeroLocus,
        Scheme.ker_ideal_of_isPullback_of_isOpenImmersion f (pullback.snd f (𝒰.f i))
          (pullback.fst f (𝒰.f i)) (𝒰.f i) (IsPullback.of_hasPullback f (𝒰.f i)).flip,
        Ideal.coe_comap,
        Set.image_preimage_eq _ (ConcreteCategory.bijective_of_isIso ((𝒰.f i).appIso ⊤).inv).2]
      exact ⟨((Scheme.IdealSheafData.coe_support_inter _ _).le ⟨hy, by simp⟩).1, ⟨_, rfl⟩⟩
    obtain ⟨A, hA, hAd, hAv, K, hK, hAK, hAF, g', h', hcomm, hclosed⟩ :=
      this (pullback.snd f (𝒰.f i)) x hx ⟨_, rfl⟩
    let g := g' ≫ pullback.fst f (𝒰.f i)
    let h := h' ≫ 𝒰.f i
    refine ⟨A, hA, hAd, hAv, K, hK, hAK, hAF, g, h, ?_, ?_⟩
    · show g' ≫ pullback.fst f (𝒰.f i) ≫ f =
        Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ h' ≫ 𝒰.f i
      rw [pullback.condition, reassoc_of% hcomm]
    · exact congrArg (𝒰.f i) hclosed
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S generalizing X R
  · let compactX : CompactSpace X :=
      (quasiCompact_iff_compactSpace (f := f)).mp ‹QuasiCompact f›
    let 𝒱 := X.affineCover.finiteSubcover
    obtain ⟨_, ⟨i, rfl⟩, hy'⟩ := (f.iUnion_support_ker_openCover_map_comp 𝒱).ge hy
    let hqc : QuasiCompact (𝒱.f i ≫ f) :=
      (quasiCompact_iff_compactSpace (f := 𝒱.f i ≫ f)).mpr inferInstance
    obtain ⟨A, hA, hAd, hAv, K, hK, hAK, hAF, g', h', hcomm, hclosed⟩ :=
      this R (𝒱.f i ≫ f) y hy' ⟨_, rfl⟩
    let g := g' ≫ 𝒱.f i
    refine ⟨A, hA, hAd, hAv, K, hK, hAK, hAF, g, h', ?_, hclosed⟩
    simpa [g, Category.assoc] using hcomm
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  let p : PrimeSpectrum R := y
  have hclosure : y ∈ closure (Set.range (Spec.map φ)) :=
    (Scheme.Hom.support_ker (Spec.map φ)).symm ▸ hy
  have hclosure' : p ∈ closure (Set.range (PrimeSpectrum.comap φ.hom)) := hclosure
  rw [PrimeSpectrum.closure_range_comap] at hclosure'
  have hker : RingHom.ker φ.hom ≤ p.asIdeal := by
    change p ∈ PrimeSpectrum.zeroLocus (RingHom.ker φ.hom) at hclosure'
    simpa using hclosure'
  obtain ⟨Q, _, hQ, hQle⟩ :=
    p.asIdeal.exists_ideal_comap_le_prime (⊥ : Ideal S) (by simpa [RingHom.ker] using hker)
  let q : PrimeSpectrum S := ⟨Q, hQ⟩
  exact exists_valuationRing_diagram_of_comap_le φ.hom p q hQle

/-- Every point of the scheme-theoretic image of a quasi-compact morphism is reached
by a map from a valuation ring whose generic point factors through the source. -/
@[stacks 02JQ "valuative diagram"]
public theorem exists_valuationRing_of_image_point
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] (z : f.image) :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : ValuationRing A)
      (K : Type u) (_ : Field K) (_ : Algebra A K) (_ : IsFractionRing A K)
      (g : Spec (.of K) ⟶ X) (h : Spec (.of A) ⟶ f.image),
      g ≫ f.toImage =
        Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ h ∧
      h (closedPoint A) = z := by
  have hz : z ∈ f.toImage.ker.support := by
    have hs : (f.toImage.ker.support : Set f.image) = Set.univ := by
      rw [Scheme.Hom.support_ker]
      exact f.toImage.denseRange.closure_range
    show (z : f.image) ∈ (f.toImage.ker.support : Set f.image)
    rw [hs]
    exact Set.mem_univ z
  exact exists_valuationRing_diagram_of_mem_support_ker f.toImage z hz

/-- A point of the scheme-theoretic image is a specialization of a point coming
from the source. -/
@[stacks 02JQ "specialization consequence"]
public theorem exists_specializes_of_image_point
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] (z : f.image) :
    ∃ x : X, f x ⤳ f.imageι z := by
  obtain ⟨A, hA, hAd, hAv, K, hK, hAK, hAF, g, h, hcomm, hclosed⟩ :=
    exists_valuationRing_of_image_point f z
  refine ⟨g (genericPoint (Spec (.of K))), ?_⟩
  have hgen :
      Spec.map (CommRingCat.ofHom (algebraMap A K)) (genericPoint (Spec (.of K))) =
        genericPoint (Spec (.of A)) := by
    rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
    exact PrimeSpectrum.ext
      ((RingHom.injective_iff_ker_eq_bot (algebraMap A K)).mp (IsFractionRing.injective A K))
  have heq : f (g (genericPoint (Spec (.of K)))) =
      f.imageι (h (genericPoint (Spec (.of A)))) := by
    have hf := congrArg (fun k : X ⟶ Y => k (g (genericPoint (Spec (.of K)))))
      (Scheme.Hom.toImage_imageι (f := f))
    simp only [Scheme.Hom.comp_apply] at hf
    rw [← hf]
    have hc := congrArg (fun k : Spec (.of K) ⟶ f.image =>
      k (genericPoint (Spec (.of K)))) hcomm
    simpa only [Scheme.Hom.comp_apply, hgen] using congrArg f.imageι hc
  rw [heq, ← hclosed]
  exact ((genericPoint_specializes (closedPoint A)).map h.base.hom.continuous).map
    f.imageι.base.hom.continuous

end AlgebraicGeometry

end
