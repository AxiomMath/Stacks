module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.Devissage

/-!
# From the trivial bundle to an arbitrary affine-space bundle

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project. The devissage of
`StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.Devissage` reduces Stacks 02TT for affine-space
bundles of rank `r` to the generic decomposition over integral bases
(`Stacks.Chow.GenericDecompositionHolds`). This file supplies that decomposition from the
surjectivity of flat pullback along the trivial bundle `𝔸^r_B ⟶ B` for every base `B`: a bundle
is trivial over an open neighbourhood `U` of the image of the point, the trivial bundle over `U`
has the decomposition with no error term, and the decomposition descends from the open piece by
`Stacks.Chow.hasGenericDecomposition_of_isOpenImmersion_square`.

This is the second paragraph of the proof of Stacks 02TT: the reduction from a locally trivial
bundle to a trivial one.

## Main results

* `Stacks.Chow.hasGenericDecomposition_of_trivialization` — the generic decomposition descends
  from a trivializing open subscheme of the base.
* `Stacks.Chow.genericDecompositionHolds_of_surjective_affineSpaceOver` — the generic
  decomposition from surjectivity of flat pullback along trivial bundles.
* `Stacks.Chow.flatPullbackChow_surjective_of_surjective_affineSpaceOver` — **Stacks 02TT** for
  an affine-space bundle, from surjectivity of flat pullback along trivial bundles.

## References

* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

attribute [local instance] flat_affineSpaceOver

/-- Transporting a trivialization back along `e.inv` commutes with the structure maps. -/
private theorem inv_comp_comp_eq {A B S T P V : Scheme.{u}} (sA : A ⟶ S) (sB : B ⟶ S) (q : A ⟶ B)
    (hq : q ≫ sB = sA) (e : T ≅ P) (ι : T ⟶ A) (j : V ⟶ B) (p : P ⟶ V) (g : T ⟶ V)
    (he : e.hom ≫ p = g) (hg : g ≫ j = ι ≫ q) :
    (e.inv ≫ ι) ≫ q = p ≫ j ∧ (e.inv ≫ ι) ≫ sA = p ≫ j ≫ sB := by
  have h : (e.inv ≫ ι) ≫ q = p ≫ j := by
    rw [Category.assoc, ← hg, ← he, Category.assoc, Iso.inv_hom_id_assoc]
  exact ⟨h, by rw [← hq, ← Category.assoc, h, Category.assoc]⟩

/-- **The generic decomposition descends from a trivializing open.** Let `q : A ⟶ B` be flat of
relative dimension `r` over the base, let `U ⊆ B` be open and let `e : q⁻¹(U) ≅ 𝔸^r_U` identify
`q` over `U` with the projection. A generic decomposition for the projection `𝔸^r_U ⟶ U` at
`e(w)` gives one for `q` at `w`, for every point `w` of `q⁻¹(U)`. -/
theorem hasGenericDecomposition_of_trivialization (C : ChowSituation.{u}) {A B : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB]
    (q : A ⟶ B) [LocallyOfFiniteType q] [Flat q] (hq : q ≫ sB = sA) (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension q r) (U : B.Opens)
    (e : (q ⁻¹ᵁ U).toScheme ≅ 𝔸(ULift.{u} (Fin r); U.toScheme))
    (he : e.hom ≫ (𝔸(ULift.{u} (Fin r); U.toScheme) ↘ U.toScheme) = q ∣_ U) (k : ℤ)
    (w : (q ⁻¹ᵁ U).toScheme)
    (h : HasGenericDecomposition C
      ((𝔸(ULift.{u} (Fin r); U.toScheme) ↘ U.toScheme) ≫ U.ι ≫ sB) (U.ι ≫ sB)
      (𝔸(ULift.{u} (Fin r); U.toScheme) ↘ U.toScheme) rfl r
      (relativeDimension_affineSpaceOver U.toScheme r) k (e.hom.base w)) :
    HasGenericDecomposition C sA sB q hq r hr k ((q ⁻¹ᵁ U).ι.base w) := by
  set p := 𝔸(ULift.{u} (Fin r); U.toScheme) ↘ U.toScheme with hp
  set mA := e.inv ≫ (q ⁻¹ᵁ U).ι with hmA
  obtain ⟨hmAq, hmAs⟩ := inv_comp_comp_eq sA sB q hq e _ _ _ _ he (morphismRestrict_ι q U)
  have hw1 : mA.base (e.hom.base w) = (q ⁻¹ᵁ U).ι.base w := by
    rw [hmA, Scheme.Hom.comp_apply, Scheme.hom_inv_apply]
  have hrange : Set.range mA.base = q.base ⁻¹' (U : Set B) := by
    have hsurj : Function.Surjective e.inv.base := fun z ↦
      ⟨e.hom.base z, by rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]; rfl⟩
    rw [hmA, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hsurj.range_eq,
      Set.image_univ, Scheme.Opens.range_ι]
    rfl
  rw [← hw1]
  refine hasGenericDecomposition_of_isOpenImmersion_square C sA sB (p ≫ U.ι ≫ sB) (U.ι ≫ sB)
    q hq r hr mA hmAs U.ι rfl p rfl hmAq (relativeDimension_affineSpaceOver U.toScheme r) k
    (e.hom.base w) (fun t ht heq ↦ ht ?_) h
  rw [hrange, Set.mem_preimage, heq, hw1]
  exact w.2

/-- **The generic decomposition from the trivial bundle.** If flat pullback along the projection
`𝔸^r_B ⟶ B` is surjective on Chow groups in degree `k` for every base `B`, then every
affine-space bundle of rank `r` has a generic decomposition in degree `k` at every point; in
particular `Stacks.Chow.GenericDecompositionHolds` holds.

The bundle is trivial over an open neighbourhood `U` of the image of the point. Over `U` the
class of the prime cycle is a flat pullback, which is a generic decomposition with no error
term, and it descends by `Stacks.Chow.hasGenericDecomposition_of_trivialization`. -/
theorem genericDecompositionHolds_of_surjective_affineSpaceOver (C : ChowSituation.{u}) (r : ℕ)
    (k : ℤ)
    (hTBS : ∀ (B : Scheme.{u}) (sB : B ⟶ C.S) [LocallyOfFiniteType sB],
      Function.Surjective (flatPullbackChow C ((𝔸(ULift.{u} (Fin r); B) ↘ B) ≫ sB) sB
        (𝔸(ULift.{u} (Fin r); B) ↘ B) rfl r (relativeDimension_affineSpaceOver B r) k
        (flatPullbackFactorsThroughRationalEquivalence_general C _ sB _ rfl r
          (relativeDimension_affineSpaceOver B r) k))) :
    GenericDecompositionHolds C r k := by
  intro A B sA _ sB _ q _ _ hq hr hbundle _ w hw _
  obtain ⟨U, hwU, e, he⟩ := hbundle (q.base w)
  set w0 : (q ⁻¹ᵁ U).toScheme := ⟨w, hwU⟩ with hw0def
  have hw0 : (q ⁻¹ᵁ U).ι.base w0 = w := rfl
  rw [← hw0]
  refine hasGenericDecomposition_of_trivialization C sA sB q hq r hr U e he k w0 ?_
  set p := 𝔸(ULift.{u} (Fin r); U.toScheme) ↘ U.toScheme with hp
  have hmAs := (inv_comp_comp_eq sA sB q hq e _ _ _ _ he (morphismRestrict_ι q U)).2
  have hdim : relativeDimension C.dimensionFunction (p ≫ U.ι ≫ sB) (e.hom.base w0) =
      k + (r : ℤ) := by
    rw [← hmAs, relativeDimension_comp_isOpenImmersion, Scheme.Hom.comp_apply]
    show relativeDimension C.dimensionFunction sA
      ((q ⁻¹ᵁ U).ι.base (e.inv.base (e.hom.base w0))) = _
    rw [Scheme.hom_inv_apply]
    exact hw
  obtain ⟨b, hb⟩ := hTBS U.toScheme (U.ι ≫ sB)
    (QuotientAddGroup.mk' _ (pointCycle C _ _ _ hdim))
  obtain ⟨β, rfl⟩ := QuotientAddGroup.mk'_surjective _ b
  rw [flatPullbackChow_mk] at hb
  refine ⟨hdim, β, 0, fun t ht ↦ absurd rfl ht, ?_⟩
  rw [sub_zero, ← neg_sub]
  exact neg_mem ((QuotientAddGroup.eq_iff_sub_mem).mp hb)

/-- **Stacks 02TT from the trivial bundle.** If flat pullback along the projection `𝔸^r_B ⟶ B`
is surjective on Chow groups in degree `k` for every base `B`, then so is flat pullback along
every affine-space bundle of rank `r`. -/
theorem flatPullbackChow_surjective_of_surjective_affineSpaceOver (C : ChowSituation.{u})
    (r : ℕ) (k : ℤ)
    (hTBS : ∀ (B : Scheme.{u}) (sB : B ⟶ C.S) [LocallyOfFiniteType sB],
      Function.Surjective (flatPullbackChow C ((𝔸(ULift.{u} (Fin r); B) ↘ B) ≫ sB) sB
        (𝔸(ULift.{u} (Fin r); B) ↘ B) rfl r (relativeDimension_affineSpaceOver B r) k
        (flatPullbackFactorsThroughRationalEquivalence_general C _ sB _ rfl r
          (relativeDimension_affineSpaceOver B r) k)))
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f] [Flat f]
    (hbase : f ≫ sY = sX) (hf : AlgebraicGeometry.RelativeDimension f r)
    (hbundle : IsAffineSpaceBundle f r)
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C sX sY f hbase r hf k) :
    Function.Surjective (flatPullbackChow C sX sY f hbase r hf k hfac) :=
  flatPullbackChow_surjective_of_genericDecompositionHolds C r k
    (genericDecompositionHolds_of_surjective_affineSpaceOver C r k hTBS) sX sY f hbase hf
    hbundle hfac

end Stacks.Chow

end
