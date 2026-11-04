module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.AffineScheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Examples.PolynomialRetractPoints

/-!
# The polynomial retract is nowhere an isomorphism

For the square-zero extension of `k[x]` over an infinite field `k`, neither the projection nor
the section is an isomorphism over any nonempty open of its target, even though both are
birational.

The obstruction is a square-zero element that survives localization. Every nonempty open of
either spectrum contains a rational point `x = α` at which the variable `y_α` is still nonzero
after localizing, so the map of local rings there cannot be injective — while an isomorphism
over an open would force it to be.

## Main results

* `AlgebraicGeometry.PolynomialRetract.not_isIso_restrict_specMap_inclusionMap`: no restriction
  of the projection to a nonempty open of the base is an isomorphism.
* `AlgebraicGeometry.PolynomialRetract.not_isIso_restrict_specMap_retractionMap`: the same for
  the section over any nonempty open of its target.

## Implementation notes

The map over an open is the canonical restriction of a morphism of schemes, and its stalk maps
are compared with those of the unrestricted morphism through `morphismRestrictStalkMap`. The
field is infinite so that a nonempty open contains a rational point at which a square-zero
variable survives.

## References

* [Stacks Project, Tag 01RQ](https://stacks.math.columbia.edu/tag/01RQ), Example 29.50.4
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.PolynomialRetract

/-- If a spectrum map induces an isomorphism on the local ring at a point, then the
corresponding localization homomorphism is bijective. -/
private lemma stalkLocalizationMap_bijective
    {R S : CommRingCat.{u}} (φ : R ⟶ S) (p : PrimeSpectrum S)
    (h : IsIso ((Spec.map φ).stalkMap p)) :
    Function.Bijective (Localization.localRingHom (p.comap φ.hom).asIdeal p.asIdeal
      φ.hom rfl) :=
  (ConcreteCategory.isIso_iff_bijective _).mp <|
    (Arrow.isIso_iff_isIso_of_isIso (Scheme.arrowStalkMapSpecIso φ p).hom).mp h

/-- The spectrum of the polynomial retract is not isomorphic to the base over
any nonempty open. -/
@[stacks 01RQ "projection_not_iso"]
theorem not_isIso_restrict_specMap_inclusionMap
    (k : Type u) [Field k] [Infinite k]
    (U : (Spec (.of (baseRing k))).Opens) (hU : (U : Set (Spec (.of (baseRing k)))).Nonempty) :
    ¬ IsIso ((Spec.map (CommRingCat.ofHom (inclusionMap k))) ∣_ U) := by
  intro hIso
  let f := Spec.map (CommRingCat.ofHom (inclusionMap k))
  let V : TopologicalSpace.Opens (PrimeSpectrum (extensionRing k)) :=
    (TopologicalSpace.Opens.map f.base).obj U
  have hV : (V : Set (PrimeSpectrum (extensionRing k))).Nonempty := by
    obtain ⟨x, hx⟩ := hU
    obtain ⟨p, rfl⟩ := (isHomeomorph_comap_inclusionMap k).homeomorph.surjective x
    exact ⟨p, hx⟩
  obtain ⟨α, hαV, hJ⟩ :=
    exists_evaluationPrime_mem_and_projectionKernel_localization_ne_bot
      k V hV
  let p := evaluationPrime k α
  let x : f ⁻¹ᵁ U := ⟨p, hαV⟩
  have hstalk : IsIso (f.stalkMap p) := by
    rw [← Arrow.isIso_iff_isIso_of_isIso (morphismRestrictStalkMap f U x).hom]
    exact (AlgebraicGeometry.isIso_iff_isIso_stalkMap (f ∣_ U)).mp hIso |>.2 x
  let φ := CommRingCat.ofHom (inclusionMap k)
  let q := (p.comap (inclusionMap k)).asIdeal
  let J : Ideal (extensionRing k) := projectionKernel k
  have hIncl : q = p.asIdeal.comap (inclusionMap k) :=
    PrimeSpectrum.comap_asIdeal (inclusionMap k) p
  let ℓ : Localization.AtPrime q →+* Localization.AtPrime p.asIdeal :=
    Localization.localRingHom q p.asIdeal (inclusionMap k) hIncl
  have hRetr : p.asIdeal = q.comap (retractionMap k) := by
    ext b
    show (MvPolynomial.eval (fun _ : Unit => α) (retractionMap k b) = 0) ↔
      MvPolynomial.eval (fun _ : Unit => α)
        (retractionMap k (inclusionMap k (retractionMap k b))) = 0
    rw [← RingHom.comp_apply (retractionMap k), retractionMap_comp_inclusionMap,
      RingHom.id_apply]
  let r : Localization.AtPrime p.asIdeal →+* Localization.AtPrime q :=
    Localization.localRingHom p.asIdeal q (retractionMap k) hRetr
  have hℓsurj : Function.Surjective ℓ := (stalkLocalizationMap_bijective φ p hstalk).2
  have hcomp : r.comp ℓ = RingHom.id _ := by
    refine IsLocalization.ringHom_ext q.primeCompl (RingHom.ext fun a ↦ ?_)
    show r (ℓ (algebraMap (baseRing k) (Localization.AtPrime q) a)) =
      algebraMap (baseRing k) (Localization.AtPrime q) a
    simp only [ℓ, r, Localization.localRingHom_to_map]
    rw [← RingHom.comp_apply (retractionMap k), retractionMap_comp_inclusionMap,
      RingHom.id_apply]
  have hrinj : Function.Injective r := Function.LeftInverse.injective fun b ↦ by
    obtain ⟨a, rfl⟩ := hℓsurj b
    exact congrArg ℓ (RingHom.congr_fun hcomp a)
  have hJle : Ideal.map (algebraMap (extensionRing k)
      (Localization.AtPrime p.asIdeal)) J ≤ RingHom.ker r := by
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    show r (algebraMap (extensionRing k) (Localization.AtPrime p.asIdeal) b) = 0
    have hb0 : retractionMap k b = 0 := by
      simpa [J, projectionKernel, RingHom.mem_ker] using hb
    simp [r, Localization.localRingHom_to_map, hb0]
  exact hJ (by simpa [p, J, (RingHom.injective_iff_ker_eq_bot r).1 hrinj] using hJle)

/-- The section induced by the polynomial-ring retraction is not an isomorphism
over any nonempty open of the target. -/
@[stacks 01RQ "section_not_iso"]
theorem not_isIso_restrict_specMap_retractionMap
    (k : Type u) [Field k] [Infinite k]
    (U : (Spec (.of (extensionRing k))).Opens)
    (hU : (U : Set (Spec (.of (extensionRing k)))).Nonempty) :
    ¬ IsIso ((Spec.map (CommRingCat.ofHom (retractionMap k))) ∣_ U) := by
  intro hIso
  let f := Spec.map (CommRingCat.ofHom (retractionMap k))
  obtain ⟨α, hpU, hJ⟩ :=
    exists_evaluationPrime_mem_and_projectionKernel_localization_ne_bot k U hU
  let p := evaluationPrime k α
  let q : PrimeSpectrum (baseRing k) :=
    ⟨RingHom.ker (MvPolynomial.eval (fun _ : Unit => α)), RingHom.ker_isPrime _⟩
  let x : f ⁻¹ᵁ U := ⟨q, hpU⟩
  let p_isPrime : p.asIdeal.IsPrime := p.2
  let q_isPrime : q.asIdeal.IsPrime := q.2
  have hIsoStalk : IsIso (f.stalkMap x.1) :=
    (CategoryTheory.Arrow.isIso_iff_isIso_of_isIso
      (AlgebraicGeometry.morphismRestrictStalkMap f U x).hom).mp
        (((AlgebraicGeometry.isIso_iff_isIso_stalkMap (f ∣_ U)).mp hIso).2 x)
  have hIJ : p.asIdeal = Ideal.comap (retractionMap k) q.asIdeal := rfl
  let φ : CommRingCat.of (Localization.AtPrime p.asIdeal) ⟶
      CommRingCat.of (Localization.AtPrime q.asIdeal) :=
    CommRingCat.ofHom
      (Localization.localRingHom p.asIdeal q.asIdeal (retractionMap k) hIJ)
  have hIsoLocal : IsIso φ :=
    (CategoryTheory.Arrow.isIso_iff_isIso_of_isIso
      (AlgebraicGeometry.Scheme.arrowStalkMapSpecIso
        (CommRingCat.ofHom (retractionMap k)) q).hom).mp hIsoStalk
  have hφ_inj : Function.Injective φ :=
    (CategoryTheory.ConcreteCategory.bijective_of_isIso φ).1
  have hmap_le_ker : projectionKernel k ≤ RingHom.ker
      (algebraMap (extensionRing k) (Localization.AtPrime p.asIdeal)) := by
    refine fun b hb ↦ RingHom.mem_ker.mpr (hφ_inj ?_)
    show (Localization.localRingHom p.asIdeal q.asIdeal (retractionMap k) hIJ)
        (algebraMap (extensionRing k) (Localization.AtPrime p.asIdeal) b) = _
    simp only [Localization.localRingHom_to_map, RingHom.mem_ker.mp hb, map_zero]
  exact hJ <| (Ideal.map_eq_bot_iff_le_ker
    (algebraMap (extensionRing k) (Localization.AtPrime p.asIdeal))).2 hmap_le_ker

end AlgebraicGeometry.PolynomialRetract
