module

public import StacksFrontier.AlgebraicGeometry.Perfect.TorIndependence
public import StacksFrontier.Homology.Tor.IndependenceTransitivity

/-!
# Tor independence along a composition of schemes

Let `U ⟶ V ⟶ W` and `W' ⟶ W` be morphisms of schemes and let `V'` be the fibre product
`V ×_W W'`. If `V` and `W'` are Tor independent over `W`, and `U` and `V'` are Tor independent
over `V`, then `U` and `W'` are Tor independent over `W`.

## Main results

* `AlgebraicGeometry.TorIndependent.comp_of_isPullback`: Tor independence of `U ⟶ V` and
  `V ×_W W' ⟶ V`, together with Tor independence of `V ⟶ W` and `W' ⟶ W`, gives Tor
  independence of `U ⟶ W` and `W' ⟶ W`.

## Implementation notes

Tor independence is checked on rings of sections over affine opens (Stacks 0FXV). Over affine
opens `W₀ ⊆ W`, `V₀ ⊆ V`, `W₀' ⊆ W'` the open `V₀ ×_{W₀} W₀'` of `V'` is affine with ring of
sections `Γ(V₀) ⊗_{Γ(W₀)} Γ(W₀')`, so the statement becomes the ring-theoretic one,
`RingTheory.TorIndependence.torIndependent_of_torIndependent_tensorProduct`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- The affine-local form of `AlgebraicGeometry.TorIndependent.comp_of_isPullback`: over affine
opens `W₀ ⊆ W`, `V₀ ⊆ V`, `U₀ ⊆ U` and `W₀' ⊆ W'` compatible with the morphisms, the rings of
sections of `U₀` and `W₀'` are Tor independent over that of `W₀`. -/
theorem torIndependent_appLE_comp_of_isPullback {U V W W' V' : Scheme.{u}} {p : U ⟶ V}
    {q : V ⟶ W} {s : W' ⟶ W} {π₁ : V' ⟶ V} {π₂ : V' ⟶ W'} (sq : IsPullback π₁ π₂ q s)
    (hqs : TorIndependent q s) (hp : TorIndependent p π₁) {W₀ : W.Opens} {V₀ : V.Opens}
    {U₀ : U.Opens} {W₀' : W'.Opens} (hW₀ : IsAffineOpen W₀) (hV₀ : IsAffineOpen V₀)
    (hU₀ : IsAffineOpen U₀) (hW₀' : IsAffineOpen W₀') (hV : V₀ ≤ q ⁻¹ᵁ W₀)
    (hU : U₀ ≤ p ⁻¹ᵁ V₀) (hW' : W₀' ≤ s ⁻¹ᵁ W₀) (hUW : U₀ ≤ (p ≫ q) ⁻¹ᵁ W₀) :
    letI : Algebra Γ(W, W₀) Γ(U, U₀) := ((p ≫ q).appLE W₀ U₀ hUW).hom.toAlgebra
    letI : Algebra Γ(W, W₀) Γ(W', W₀') := (s.appLE W₀ W₀' hW').hom.toAlgebra
    Algebra.TorIndependent Γ(W, W₀) Γ(U, U₀) Γ(W', W₀') := by
  letI : Algebra Γ(W, W₀) Γ(V, V₀) := (q.appLE W₀ V₀ hV).hom.toAlgebra
  letI : Algebra Γ(V, V₀) Γ(U, U₀) := (p.appLE V₀ U₀ hU).hom.toAlgebra
  letI : Algebra Γ(W, W₀) Γ(U, U₀) := ((p ≫ q).appLE W₀ U₀ hUW).hom.toAlgebra
  letI : Algebra Γ(W, W₀) Γ(W', W₀') := (s.appLE W₀ W₀' hW').hom.toAlgebra
  haveI : IsScalarTower Γ(W, W₀) Γ(V, V₀) Γ(U, U₀) := IsScalarTower.of_algebraMap_eq' <|
    (congrArg CommRingCat.Hom.hom (Scheme.Hom.appLE_comp_appLE p q W₀ V₀ U₀ hV hU)).symm
  -- the open `V₀ ×_{W₀} W₀'` of the fibre product
  let Y₀ : V'.Opens := π₁ ⁻¹ᵁ V₀ ⊓ π₂ ⁻¹ᵁ W₀'
  have hY₀ : IsAffineOpen Y₀ := by
    have : IsAffine W₀ := hW₀
    have : IsAffine W₀' := hW₀'
    have : IsAffine V₀ := hV₀
    exact .of_isIso (Scheme.Hom.isPullback_resLE sq hW' hV rfl).isoPullback.hom
  have hpush := (isIso_pushoutSection_iff sq hW' hV (rfl : Y₀ = _)).mp
    (isIso_pushoutSection_of_isAffineOpen sq hW' hV rfl hW₀ hW₀' hV₀)
  have ht := CommRingCat.isPushout_tensorProduct Γ(W, W₀) Γ(V, V₀) Γ(W', W₀')
  let e := ht.isoIsPushout _ _ hpush
  let eB : Γ(V', Y₀) ≃+* Γ(V, V₀) ⊗[Γ(W, W₀)] Γ(W', W₀') := e.symm.commRingCatIsoToRingEquiv
  have tq := (torIndependent_tfae q s).out 1 2
  have tp := (torIndependent_tfae p π₁).out 1 2
  have h₁ : RingTheory.TorIndependence.TorIndependent Γ(W, W₀) Γ(V, V₀) Γ(W', W₀') :=
    (RingTheory.TorIndependence.torIndependent_iff_isZero_tor _ _ _).mpr
      (tq.mp hqs V₀ hV₀ W₀' hW₀' W₀ hW₀ hV hW')
  letI : Algebra Γ(V, V₀) Γ(V', Y₀) := (π₁.appLE V₀ Y₀ inf_le_left).hom.toAlgebra
  have h₂' : RingTheory.TorIndependence.TorIndependent Γ(V, V₀) Γ(U, U₀) Γ(V', Y₀) :=
    (RingTheory.TorIndependence.torIndependent_iff_isZero_tor _ _ _).mpr
      (tp.mp hp U₀ hU₀ Y₀ hY₀ V₀ hV₀ hU inf_le_left)
  have h₂ : RingTheory.TorIndependence.TorIndependent Γ(V, V₀) Γ(U, U₀)
      (Γ(V, V₀) ⊗[Γ(W, W₀)] Γ(W', W₀')) :=
    (torIndependent_congr Γ(V, V₀) Γ(U, U₀) Γ(V', Y₀) Γ(V, V₀) Γ(U, U₀)
      (Γ(V, V₀) ⊗[Γ(W, W₀)] Γ(W', W₀')) (RingEquiv.refl _) (RingEquiv.refl _) eB
      (fun _ => rfl)
      (fun r => congrArg (fun φ => CommRingCat.Hom.hom φ r)
        (IsPushout.inl_isoIsPushout_inv _ _ ht hpush))).mp h₂'
  exact (RingTheory.TorIndependence.torIndependent_iff_isZero_tor _ _ _).mp
    (RingTheory.TorIndependence.torIndependent_of_torIndependent_tensorProduct h₁ h₂)

/-- Tor independence along a composition: if `V ⟶ W` and `W' ⟶ W` are Tor independent, and
`U ⟶ V` is Tor independent of the base change `V ×_W W' ⟶ V`, then `U ⟶ W` and `W' ⟶ W` are
Tor independent. -/
theorem TorIndependent.comp_of_isPullback {U V W W' V' : Scheme.{u}} {p : U ⟶ V} {q : V ⟶ W}
    {s : W' ⟶ W} {π₁ : V' ⟶ V} {π₂ : V' ⟶ W'} (sq : IsPullback π₁ π₂ q s)
    (hqs : TorIndependent q s) (hp : TorIndependent p π₁) : TorIndependent (p ≫ q) s := by
  refine ((torIndependent_tfae (p ≫ q) s).out 1 3).mpr ?_
  refine ⟨W.affineOpens, fun i => i.1, iSup_affineOpens_eq_top W, fun i => i.2, fun i => ?_⟩
  let J := {x : U.affineOpens × V.affineOpens //
    (x.2 : V.Opens) ≤ q ⁻¹ᵁ i.1 ∧ (x.1 : U.Opens) ≤ p ⁻¹ᵁ (x.2 : V.Opens)}
  let K := {k : W'.affineOpens // (k : W'.Opens) ≤ s ⁻¹ᵁ i.1}
  refine ⟨J, fun j => j.1.1.1, ?_, fun j => j.1.1.2, K, fun k => k.1.1, ?_, fun k => k.1.2,
    fun j k => ?_⟩
  · apply le_antisymm
    · refine iSup_le fun j => j.2.2.trans ?_
      rw [Scheme.Hom.comp_preimage]
      exact Scheme.Hom.preimage_mono p j.2.1
    · intro x hx
      rw [Scheme.Hom.comp_preimage] at hx
      obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hxV₀, hV₀le⟩ :=
        V.isBasis_affineOpens.exists_subset_of_mem_open hx (q ⁻¹ᵁ i.1).2
      obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hxU₀, hU₀le⟩ :=
        U.isBasis_affineOpens.exists_subset_of_mem_open (show p.base x ∈ V₀ from hxV₀)
          (p ⁻¹ᵁ V₀).2
      exact Opens.mem_iSup.mpr ⟨⟨(⟨U₀, hU₀⟩, ⟨V₀, hV₀⟩), hV₀le, hU₀le⟩, hxU₀⟩
  · apply le_antisymm
    · exact iSup_le fun k => k.2
    · intro x hx
      obtain ⟨_, ⟨W₀, hW₀, rfl⟩, hxW₀, hW₀le⟩ :=
        W'.isBasis_affineOpens.exists_subset_of_mem_open hx (s ⁻¹ᵁ i.1).2
      exact Opens.mem_iSup.mpr ⟨⟨⟨W₀, hW₀⟩, hW₀le⟩, hxW₀⟩
  · exact torIndependent_appLE_comp_of_isPullback sq hqs hp i.2 j.1.2.2 j.1.1.2 k.1.2
      j.2.1 j.2.2 k.2 _

end AlgebraicGeometry
