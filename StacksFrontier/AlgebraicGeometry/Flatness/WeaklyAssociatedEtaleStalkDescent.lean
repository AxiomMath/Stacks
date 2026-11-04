module

public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleLocalization.EtalePullback
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociatedTensorPullback
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.FiberMaximalIdeal

/-!
# Descending weak association from the local ring of an étale neighbourhood

Let `e : U ⟶ S` be an étale neighbourhood of a scheme `S` and `R' = 𝒪_{U, u}` the local ring at
its distinguished point, an algebra over `R = 𝒪_{S, e u}` through the stalk map. This file
proves, for a quasi-coherent `𝒪_S`-module `G`: if some nonzero element of `R' ⊗_R G_{e u}` is
killed by a power of every element of the maximal ideal of `R`, then `e u` is weakly associated
to `G`.

This is the last step of the base clause of [Stacks, Tag 05IH] in the proof of
[Stacks, Tag 05IG]: "then `𝔭' ∈ WeakAss_{R'}(M')`, which in turn gives `𝔭 ∈ WeakAss_R(M)`". The
first half is that the maximal ideal of `R` generates that of `R'` (the stalk map of an étale
morphism is unramified); the second half is the étale invariance of weakly associated points,
[Stacks, Tag 05FP], with the stalk of the pullback of `G` identified with `R' ⊗_R G_{e u}`.

## Main results

* `AlgebraicGeometry.isWeaklyAssociatedPoint_of_ne_zero_of_etaleNeighborhood_stalk`

## References

* [Stacks Project, Tag 05FP](https://stacks.math.columbia.edu/tag/05FP)
* [Stacks Project, Tag 05IG](https://stacks.math.columbia.edu/tag/05IG)
-/

@[expose] public section

open CategoryTheory TensorProduct IsLocalRing

universe u

namespace AlgebraicGeometry

/-- **Weak association descends from the local ring of an étale neighbourhood.** Let `U` be an
étale neighbourhood of a scheme `S`, let `R' = 𝒪_{U, u}` be the local ring at its distinguished
point, an `𝒪_{S, e u}`-algebra through the stalk map of `e : U ⟶ S`, and let `G` be a
quasi-coherent `𝒪_S`-module. If a nonzero `y ∈ R' ⊗ G_{e u}` is killed by a power of every
element of the maximal ideal of `𝒪_{S, e u}`, then `e u` is weakly associated to `G`. -/
theorem isWeaklyAssociatedPoint_of_ne_zero_of_etaleNeighborhood_stalk
    {S : Scheme.{u}} {c : S} (U : EtaleNeighborhood S c) (G : S.Modules) [G.IsQuasicoherent] :
    letI : Algebra (S.presheaf.stalk (U.toBase U.point)) (U.scheme.presheaf.stalk U.point) :=
      (U.toBase.stalkMap U.point).hom.toAlgebra
    ∀ y : U.scheme.presheaf.stalk U.point ⊗[S.presheaf.stalk (U.toBase U.point)]
        (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf (U.toBase U.point)),
      y ≠ 0 → (∀ f ∈ maximalIdeal (S.presheaf.stalk (U.toBase U.point)), ∃ k : ℕ, f ^ k • y = 0) →
      Stacks.Divisors.IsWeaklyAssociatedPoint G (U.toBase U.point) := by
  let : Algebra (S.presheaf.stalk (U.toBase U.point)) (U.scheme.presheaf.stalk U.point) :=
    (U.toBase.stalkMap U.point).hom.toAlgebra
  intro y hy hyf
  -- the maximal ideal of `𝒪_{S, e u}` generates that of `R'`
  have hmax : (maximalIdeal (S.presheaf.stalk (U.toBase U.point))).map
      (algebraMap (S.presheaf.stalk (U.toBase U.point)) (U.scheme.presheaf.stalk U.point)) =
        maximalIdeal (U.scheme.presheaf.stalk U.point) := by
    refine map_maximalIdeal_eq_of_etale_fibers U.toBase (fun s => ?_) U.point
    change Etale (Limits.pullback.snd U.toBase (S.fromSpecResidueField s))
    infer_instance
  -- `𝔪_{R'}` is weakly associated to `R' ⊗ G_{e u}`
  have h1 : IsWeaklyAssociatedPrime (U.scheme.presheaf.stalk U.point)
      (U.scheme.presheaf.stalk U.point ⊗[S.presheaf.stalk (U.toBase U.point)]
        (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf (U.toBase U.point)))
      (maximalIdeal (U.scheme.presheaf.stalk U.point)) := by
    change WeaklyAssociated (maximalIdeal (U.scheme.presheaf.stalk U.point)) _
    refine weaklyAssociated_maximalIdeal_iff_exists_radical_eq.mpr ⟨y, le_antisymm ?_ ?_⟩
    · have hne : annihilatorOfElem_semiring (R := U.scheme.presheaf.stalk U.point) y ≠ ⊤ := by
        intro h
        apply hy
        have h0 := (mem_annihilatorOfElem_semiring_iff y 1).mp (h ▸ Submodule.mem_top)
        rwa [one_smul] at h0
      exact (Ideal.radical_mono (le_maximalIdeal hne)).trans_eq
        (maximalIdeal.isMaximal _).isPrime.radical
    · rw [← hmax, Ideal.map_le_iff_le_comap]
      intro f hf
      obtain ⟨k, hk⟩ := hyf f hf
      exact ⟨k, (mem_annihilatorOfElem_semiring_iff y _).mpr (by rw [← map_pow, algebraMap_smul,
        hk])⟩
  -- the stalk of the pullback at `u` is `R' ⊗ G_{e u}`
  let H := (Scheme.Modules.pullback U.toBase).obj G
  let : Module (U.scheme.presheaf.stalk U.point)
      (TopCat.Presheaf.stalk (C := Ab.{u}) H.val.presheaf U.point) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := U.scheme.presheaf) H.val U.point
  let e₀ : TopCat.Presheaf.stalk (C := Ab.{u}) H.val.presheaf U.point
      ≃ₗ[U.scheme.presheaf.stalk U.point]
        U.scheme.presheaf.stalk U.point ⊗[S.presheaf.stalk (U.toBase U.point)]
          (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf (U.toBase U.point)) :=
    Classical.choose
    (RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv
      U.toBase.toLRSHom.toShHom G U.point)
  have h2 : Stacks.Divisors.IsWeaklyAssociatedPoint H U.point :=
    (LinearEquiv.isWeaklyAssociatedPrime_iff e₀.symm _).mp h1
  -- étale descent, Stacks 05FP
  exact (isWeaklyAssociatedPoint_pullback_iff_of_etale U.toBase G U.point).mp h2

/-- **Weak association descends from the local ring of an étale neighbourhood, over an affine
open.** The same statement as
`AlgebraicGeometry.isWeaklyAssociatedPoint_of_ne_zero_of_etaleNeighborhood_stalk`, with the
tensor product taken over the ring of sections `Γ(S, V)` of an affine open `V ∋ s` rather than
over the local ring at `s`, the point `s` only propositionally equal to the image of the
distinguished point, and the torsion condition imposed on the prime of `Γ(S, V)` at `s`. -/
theorem isWeaklyAssociatedPoint_of_ne_zero_of_etaleNeighborhood_affineOpen
    {S : Scheme.{u}} {c : S} (U : EtaleNeighborhood S c) (G : S.Modules) [G.IsQuasicoherent]
    {s : S} (hs : U.toBase U.point = s) {V : S.Opens} (hV : IsAffineOpen V) (hsV : s ∈ V)
    [Algebra Γ(S, V) (U.scheme.presheaf.stalk U.point)]
    (halg : ∀ r : Γ(S, V), algebraMap Γ(S, V) (U.scheme.presheaf.stalk U.point) r =
      U.toBase.stalkMap U.point (S.presheaf.germ V (U.toBase U.point) (hs ▸ hsV) r))
    [Module Γ(S, V) (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf s)]
    (hmod : ∀ (r : Γ(S, V)) (m : TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf s),
      letI : Module (S.presheaf.stalk s) (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf s) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := S.presheaf) G.val s
      r • m = (S.presheaf.germ V s hsV r) • m)
    (y : U.scheme.presheaf.stalk U.point ⊗[Γ(S, V)]
      TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf s) (hy : y ≠ 0)
    (hyf : ∀ f ∈ (hV.primeIdealOf ⟨s, hsV⟩).asIdeal, ∃ k : ℕ, f ^ k • y = 0) :
    Stacks.Divisors.IsWeaklyAssociatedPoint G s := by
  subst hs
  set p := (hV.primeIdealOf ⟨U.toBase U.point, hsV⟩).asIdeal
  let : Algebra Γ(S, V) (S.presheaf.stalk (U.toBase U.point)) :=
    (S.presheaf.germ V (U.toBase U.point) hsV).hom.toAlgebra
  have hloc : IsLocalization.AtPrime (S.presheaf.stalk (U.toBase U.point)) p :=
    hV.isLocalization_stalk ⟨U.toBase U.point, hsV⟩
  let : Algebra (S.presheaf.stalk (U.toBase U.point)) (U.scheme.presheaf.stalk U.point) :=
    (U.toBase.stalkMap U.point).hom.toAlgebra
  have : IsScalarTower Γ(S, V) (S.presheaf.stalk (U.toBase U.point))
      (U.scheme.presheaf.stalk U.point) := IsScalarTower.of_algebraMap_eq fun r => halg r
  let : Module (S.presheaf.stalk (U.toBase U.point))
      (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf (U.toBase U.point)) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := S.presheaf) G.val (U.toBase U.point)
  have : IsScalarTower Γ(S, V) (S.presheaf.stalk (U.toBase U.point))
      (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf (U.toBase U.point)) :=
    IsScalarTower.of_algebraMap_smul fun r m => (hmod r m).symm
  let e : (U.scheme.presheaf.stalk U.point) ⊗[S.presheaf.stalk (U.toBase U.point)]
        TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf (U.toBase U.point)
      ≃ₗ[S.presheaf.stalk (U.toBase U.point)] (U.scheme.presheaf.stalk U.point) ⊗[Γ(S, V)]
        TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf (U.toBase U.point) :=
    IsLocalization.moduleTensorEquiv p.primeCompl (S.presheaf.stalk (U.toBase U.point)) _ _
  refine isWeaklyAssociatedPoint_of_ne_zero_of_etaleNeighborhood_stalk U G (e.symm y)
    (fun h => hy (by simpa using congrArg e h)) fun f hf => ?_
  obtain ⟨⟨f₀, σ⟩, hfσ⟩ := IsLocalization.mk'_surjective p.primeCompl f
  simp only at hfσ
  subst hfσ
  have hf₀ : f₀ ∈ p := by
    rwa [IsLocalization.AtPrime.mk'_mem_maximal_iff (S.presheaf.stalk (U.toBase U.point)) p]
      at hf
  obtain ⟨k, hk⟩ := hyf f₀ hf₀
  refine ⟨k, ?_⟩
  have h1 : f₀ ^ k • e.symm y = e.symm (f₀ ^ k • y) :=
    ((e.symm.restrictScalars Γ(S, V)).map_smul _ _).symm
  rw [IsLocalization.mk'_eq_mul_mk'_one, mul_pow, mul_comm, mul_smul, ← map_pow, algebraMap_smul,
    h1, hk, map_zero, smul_zero]

end AlgebraicGeometry

end
