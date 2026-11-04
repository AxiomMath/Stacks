module

public import StacksFrontier.AlgebraicGeometry.ProjTwistMono.Basic

/-!
# Tag 01N1's third assertion: the comparison map is an isomorphism on every twist

Let `ψ : 𝒜 →+*ᵍ ℬ` be a homomorphism of nonnegatively graded rings, surjective on homogeneous
components of all sufficiently large degree, and let `𝒜` be generated in degree one over `𝒜 0`.
This file proves Tag 01N1's third assertion: Tag 01MY's comparison map `θ n` is an isomorphism
for every `n : ℤ`.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistMono.isIso_projMapData_twistMap`: **the assertion**, under
  the hypotheses `hψ` and `hgen`, for every `n : ℤ`.
* `Stacks.AlgebraicGeometry.ProjTwistMono.pullbackTwistIsoUnit`: the `n`-th twist pulls back to
  the unit on a standard open `D₊(pq)` with `deg p = deg q + 1`.

## Implementation notes

`θ n` is an epimorphism by Tag 01N0, and being an isomorphism is local on the base. Around each
point of the domain of definition `U(ψ)` both sides of `θ n` become the unit: generation in degree
one puts the images of the point in standard opens `D₊(pq)` with `deg p = deg q + 1`, on which the
twists pull back to the unit by `pullbackTwistIsoUnit`.

The twists of `𝒜` and of `ℬ` are handled by one lemma, `pullbackTwistIsoUnit`, stated for a
single graded ring; the two sides of `θ n` differ only in which ring and which morphism are fed
to `restrictPullbackIsoUnit`.

`pullbackTwistIsoUnit` goes through `Scheme.Modules.restrictFunctor`, not directly through
`Scheme.Modules.pullback`: the trivialization transport
`Stacks.AlgebraicGeometry.GoodOpenClose.trivRestrict` produces sectionwise data for the
restriction functor, whose sections over an open of the subscheme are the sections over its
image, and `Scheme.Modules.restrictFunctorIsoPullback` carries the result across.

## What is not done

Invertibility of the source of `θ n` is not proved here, so the hypothesis `hsrc` of
`isIso_projMapData_twistMap_of_isInvertible_source` is not discharged: this file produces an
isomorphism with the unit after restriction to each member of a cover, not
`SheafOfModules.IsInvertible` of the source on all of `U(ψ)`.

Tag 01N1's first two assertions are not here; they are
`Stacks.AlgebraicGeometry.RelativeProjChain.mapDomain_eq_top_of_eventually_surjective` and
`.isClosedImmersion_projMapData_hom_of_eventually_surjective`.

## References

* [Stacks Project, Tag 01N1](https://stacks.math.columbia.edu/tag/01N1)
* [Stacks Project, Tag 01N0](https://stacks.math.columbia.edu/tag/01N0)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite
open Filter
open AlgebraicGeometry.ProjectiveSpectrum.Proj

namespace Stacks.AlgebraicGeometry.ProjTwistMono

universe u w w'

/-! ### The twist is the unit on a standard open of the degree-one ratio locus -/

section OneRing

variable {C : Type u} {ρ : Type w} [CommRing C] [SetLike ρ C] [AddSubgroupClass ρ C]
  (𝒞 : ℕ → ρ) [GradedRing 𝒞]

/-- **The `n`-th twist pulls back to the unit on a standard open of the degree-one ratio
locus.** On `D₊(pq)` with `deg p = deg q + 1` this is the isomorphism given by the sectionwise
trivialization `(p/q)^n` of `𝒪(n)` (`GoodOpenClose.ratioTriv`). -/
noncomputable def pullbackTwistIsoUnit {p q : C} {e : ℕ} (hp : p ∈ 𝒞 (e + 1)) (hq : q ∈ 𝒞 e)
    (n : ℤ) :
    (Scheme.Modules.pullback (AlgebraicGeometry.Proj.basicOpen 𝒞 (p * q)).ι).obj
        (twistingSheaf 𝒞 n) ≅
      SheafOfModules.unit
        (AlgebraicGeometry.Proj.basicOpen 𝒞 (p * q)).toScheme.ringCatSheaf :=
  ((Scheme.Modules.restrictFunctorIsoPullback
      (AlgebraicGeometry.Proj.basicOpen 𝒞 (p * q)).ι).app (twistingSheaf 𝒞 n)).symm ≪≫
    isoUnitOfTriv ((GoodOpenClose.trivRestrict (AlgebraicGeometry.Proj.basicOpen 𝒞 (p * q))
      (twistingSheaf 𝒞 n)
      (GoodOpenClose.ratioTriv 𝒞 hp hq (n := n) (c := n)
        (by rw [Nat.cast_one, mul_one]))).comp
        (homOfLE (preimage_self_eq_top
          (AlgebraicGeometry.Proj.basicOpen 𝒞 (p * q))).ge))

/-- A pair of homogeneous elements with `deg p = deg q + 1` that a point omits puts the point in
their standard open. -/
theorem mem_basicOpen_of_notMem {p q : C} (x : AlgebraicGeometry.Proj 𝒞)
    (hpx : p ∉ x.asHomogeneousIdeal) (hqx : q ∉ x.asHomogeneousIdeal) :
    x ∈ AlgebraicGeometry.Proj.basicOpen 𝒞 (p * q) := by
  rw [AlgebraicGeometry.Proj.mem_basicOpen]
  exact fun hmul => (x.isPrime.mem_or_mem hmul).elim hpx hqx

end OneRing

/-! ### The assertion -/

/-- The restriction to `W` of the pullback of the `n`-th twist along `f` is the unit, when `f`
carries `W` into the standard open `D₊(pq)` with `deg p = deg q + 1`. -/
private noncomputable def restrictPullbackTwistIsoUnit {C : Type u} {ρ : Type w} [CommRing C]
    [SetLike ρ C] [AddSubgroupClass ρ C] (𝒞 : ℕ → ρ) [GradedRing 𝒞] {X : Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Proj 𝒞) {p q : C} {e : ℕ} (hp : p ∈ 𝒞 (e + 1)) (hq : q ∈ 𝒞 e)
    (n : ℤ) {W : X.Opens} (hW : W ≤ f ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒞 (p * q)) :
    (Scheme.Modules.restrictFunctor W.ι).obj ((Scheme.Modules.pullback f).obj (twistingSheaf 𝒞 n))
      ≅ SheafOfModules.unit W.toScheme.ringCatSheaf :=
  restrictPullbackIsoUnit f W (twistingSheaf 𝒞 n) (AlgebraicGeometry.Proj.basicOpen 𝒞 (p * q))
    (X.homOfLE hW ≫ (f ∣_ AlgebraicGeometry.Proj.basicOpen 𝒞 (p * q)))
    (by rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι])
    (pullbackTwistIsoUnit 𝒞 hp hq n)

variable {A B : Type u} {σ : Type w} {τ : Type w'}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-- **Tag 01N1's third assertion.** For a homomorphism of graded rings surjective on homogeneous
components of all large degree, with the source generated in degree one over its degree-zero
part, Tag 01MY's comparison map on the `n`-th twist is an isomorphism for every `n`. -/
@[stacks 01N1 "part (3): isomorphisms on all twists"]
theorem isIso_projMapData_twistMap (ψ : 𝒜 →+*ᵍ ℬ)
    (hψ : ∀ᶠ d : ℕ in atTop, Function.Surjective (GradedRingHom.gradedAddHom ψ d))
    (hgen : Algebra.adjoin (𝒜 0) (𝒜 1 : Set A) = ⊤) (n : ℤ) :
    IsIso ((ProjTwistCompare.projMapData 𝒜 ℬ ψ).twistMap n) := by
  have hepi := ProjTwistEpi.epi_projMapData_twistMap_of_eventually_surjective 𝒜 ℬ ψ hψ n
  refine isIso_of_isIso_restrict_locally _ fun x => ?_
  obtain ⟨e₁, p₁, q₁, hp₁, hq₁, hp₁x, hq₁x⟩ :=
    (ProjShared.mem_ratioLocus_iff 𝒜 1
      ((ProjTwistCompare.projMapData 𝒜 ℬ ψ).hom.base x)).mp (by
        rw [ratioLocus_eq_top_of_adjoin_coe_degree_one 𝒜 hgen 1]
        exact Opens.mem_top _)
  have hxU : (ProjShared.mapDomain 𝒜 ℬ ψ).ι.base x ∈ ProjShared.mapDomain 𝒜 ℬ ψ := x.2
  obtain ⟨e₂, p₂, q₂, hp₂, hq₂, hp₂x, hq₂x⟩ :=
    (ProjShared.mem_ratioLocus_iff ℬ 1 ((ProjShared.mapDomain 𝒜 ℬ ψ).ι.base x)).mp
      (mapDomain_le_ratioLocus_one 𝒜 ℬ ψ hgen hxU)
  refine ⟨(ProjTwistCompare.projMapData 𝒜 ℬ ψ).hom ⁻¹ᵁ
      AlgebraicGeometry.Proj.basicOpen 𝒜 (p₁ * q₁) ⊓
    (ProjShared.mapDomain 𝒜 ℬ ψ).ι ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen ℬ (p₂ * q₂),
    ⟨mem_basicOpen_of_notMem 𝒜 _ hp₁x hq₁x, mem_basicOpen_of_notMem ℬ _ hp₂x hq₂x⟩,
    isIso_of_epi_of_trivializations _ (epi_restrictFunctor_map _ _ hepi) fun _ =>
      ⟨⊤, Opens.mem_top _, ⟨trivOfIsoUnit ?_⟩, ⟨trivOfIsoUnit ?_⟩⟩⟩
  · exact restrictPullbackTwistIsoUnit 𝒜 _ hp₁ hq₁ n inf_le_left
  · exact restrictPullbackTwistIsoUnit ℬ _ hp₂ hq₂ n inf_le_right

end Stacks.AlgebraicGeometry.ProjTwistMono

end
