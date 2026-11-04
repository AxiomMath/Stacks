module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.IrreducibleComponentsBaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.IrreducibleGaloisAction
public import StacksFrontier.RingTheory.GeometricallyIrreducible.GaloisAction

/-!
# Galois orbits of geometric irreducible components

Let `K/k` be a normal extension of fields, for instance a separable closure of `k`. For a
scheme over `k`, the fibres of the canonical map from the irreducible components after base
change to the irreducible components of the original scheme are precisely the orbits of the
group `K ≃ₐ[k] K` of `k`-automorphisms of `K`.

## Main definitions

* `AlgebraicGeometry.irreducibleComponentsBaseChangeMap` is the canonical map on irreducible
  components induced by projection from a base change.

## Main results

* `AlgebraicGeometry.fiber_irreducibleComponentsBaseChangeMap_eq_orbit` identifies every fibre
  of this map with a Galois orbit.

## Implementation notes

The map is the restriction to irreducible components of the direct-image operation of
`AlgebraicGeometry.mapsTo_irreducibleComponents_baseChange`. The action is the canonical action
on geometric irreducible components. A fibre over the image of a component is written as the
inverse image of its singleton; every nonempty fibre has this form.

The transitivity input is purely affine: two points of the base change over one point `η` of the
scheme are two primes of `κ(η) ⊗[k] K`, and the Galois group acts transitively on those.

Normality of `K/k` is what that affine input needs, and it cannot be dropped: over the
non-normal extension `ℚ(2 ^ (1 / 3))/ℚ` the group `K ≃ₐ[k] K` is trivial while
`Spec (K ⊗[k] K)` has two points. It is also all that is needed — separability is not: a
purely inseparable extension contributes no splitting of components at all.

## References

* [Stacks Project, Tag 04KY](https://stacks.math.columbia.edu/tag/04KY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

universe u

/-- The map induced on pullbacks is compatible with the first projections. -/
private theorem pullback_map_comp_fst {X Y S X' Y' S' : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    {f' : X' ⟶ S'} {g' : Y' ⟶ S'} {i₁ : X ⟶ X'} {i₂ : Y ⟶ Y'} {i₃ : S ⟶ S'}
    {e₁ : f ≫ i₃ = i₁ ≫ f'} {e₂ : g ≫ i₃ = i₂ ≫ g'} :
    pullback.map f g f' g' i₁ i₂ i₃ e₁ e₂ ≫ pullback.fst f' g' = pullback.fst f g ≫ i₁ :=
  pullback.lift_fst _ _ _

/-- The map induced on pullbacks is compatible with the second projections. -/
private theorem pullback_map_comp_snd {X Y S X' Y' S' : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    {f' : X' ⟶ S'} {g' : Y' ⟶ S'} {i₁ : X ⟶ X'} {i₂ : Y ⟶ Y'} {i₃ : S ⟶ S'}
    {e₁ : f ≫ i₃ = i₁ ≫ f'} {e₂ : g ≫ i₃ = i₂ ≫ g'} :
    pullback.map f g f' g' i₁ i₂ i₃ e₁ e₂ ≫ pullback.snd f' g' = pullback.snd f g ≫ i₂ :=
  pullback.lift_snd _ _ _

/-- The Galois action on a base change commutes with the projection to the original scheme. -/
private theorem galoisActionOnBaseChange_ρ_comp_fst (k K : Type u) [Field k] [Field K]
    [Algebra k K] (X : Over (Spec (.of k))) (σ : MulOpposite (K ≃ₐ[k] K)) :
    (galoisActionOnBaseChange k K X).ρ σ ≫
        pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
      pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
  dsimp [galoisActionOnBaseChange, SchemeOver.baseChange]
  simp [pullback.map, pullback.lift_fst]

/-- The Galois action on a base change acts on the `Spec K` coordinate by `Spec σ`. -/
private theorem galoisActionOnBaseChange_ρ_comp_snd (k K : Type u) [Field k] [Field K]
    [Algebra k K] (X : Over (Spec (.of k))) (σ : MulOpposite (K ≃ₐ[k] K)) :
    (galoisActionOnBaseChange k K X).ρ σ ≫
        pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
      pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≫
        specMapAlgAut k K σ.unop := by
  dsimp [galoisActionOnBaseChange, SchemeOver.baseChange]
  simp only [pullback.map, Category.comp_id]
  rw [pullback.lift_snd]

private theorem pullbackSpecIso_comm_inv_fst (k K L : Type u) [Field k] [Field K] [Algebra k K]
    [CommRing L] [Algebra k L] :
    (pullbackSpecIso k L K ≪≫ (Scheme.Spec.mapIso
        ((Algebra.TensorProduct.comm k L K).toRingEquiv.toCommRingCatIso.op)).symm).inv ≫
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k L)))
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) := by
  dsimp
  rw [Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  ext a
  show Algebra.TensorProduct.comm k L K (a ⊗ₜ[k] (1 : K)) = (1 : K) ⊗ₜ[k] a
  exact Algebra.TensorProduct.comm_tmul k a (1 : K)

private theorem pullbackSpecIso_comm_inv_snd (k K L : Type u) [Field k] [Field K] [Algebra k K]
    [CommRing L] [Algebra k L] :
    (pullbackSpecIso k L K ≪≫ (Scheme.Spec.mapIso
        ((Algebra.TensorProduct.comm k L K).toRingEquiv.toCommRingCatIso.op)).symm).inv ≫
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k L)))
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) := by
  dsimp
  rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  ext a
  show Algebra.TensorProduct.comm k L K ((1 : L) ⊗ₜ[k] a) = a ⊗ₜ[k] (1 : L)
  exact Algebra.TensorProduct.comm_tmul k (1 : L) a

/-- Under `Spec L ×_{Spec k} Spec K ≅ Spec (K ⊗[k] L)`, the twist `id × Spec σ` becomes
`Spec (σ ⊗ id)`. -/
private theorem pullbackSpecIso_comm_hom_galoisTwist (k K L : Type u) [Field k] [Field K]
    [Algebra k K] [CommRing L] [Algebra k L] (σ : K ≃ₐ[k] K) :
    pullback.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))
        (Spec.map (CommRingCat.ofHom (algebraMap k L)))
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) (𝟙 _) (specMapAlgAut k K σ)
        (𝟙 (Spec (.of k))) rfl (by simp) ≫
      (pullbackSpecIso k L K ≪≫ (Scheme.Spec.mapIso
        ((Algebra.TensorProduct.comm k L K).toRingEquiv.toCommRingCatIso.op)).symm).hom =
    (pullbackSpecIso k L K ≪≫ (Scheme.Spec.mapIso
        ((Algebra.TensorProduct.comm k L K).toRingEquiv.toCommRingCatIso.op)).symm).hom ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.congr σ
        (AlgEquiv.refl (R := k) (A₁ := L))).toRingEquiv.toRingHom) := by
  let fL := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let gK := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let affineIso := pullbackSpecIso k L K ≪≫ (Scheme.Spec.mapIso
    ((Algebra.TensorProduct.comm k L K).toRingEquiv.toCommRingCatIso.op)).symm
  let actionOnAffine := pullback.map fL gK fL gK (𝟙 _) (specMapAlgAut k K σ)
    (𝟙 (Spec (.of k))) rfl (by simp [gK])
  let tensorAut := Algebra.TensorProduct.congr σ (AlgEquiv.refl (R := k) (A₁ := L))
  let tensorAutMap := Spec.map (CommRingCat.ofHom tensorAut.toRingEquiv.toRingHom)
  have hInvFst : affineIso.inv ≫ pullback.fst fL gK =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) :=
    pullbackSpecIso_comm_inv_fst k K L
  have hInvSnd : affineIso.inv ≫ pullback.snd fL gK =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) :=
    pullbackSpecIso_comm_inv_snd k K L
  have hAffineFst : actionOnAffine ≫ pullback.fst fL gK = pullback.fst fL gK :=
    pullback_map_comp_fst.trans (Category.comp_id _)
  have hAffineSnd :
      actionOnAffine ≫ pullback.snd fL gK = pullback.snd fL gK ≫ specMapAlgAut k K σ :=
    pullback_map_comp_snd
  have hTensorFst : tensorAutMap ≫
        Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) := by
    dsimp [tensorAutMap]
    rw [← Spec.map_comp, Spec.map_inj]
    apply CommRingCat.hom_ext
    ext a
    simp [tensorAut]
  have hTensorSnd : tensorAutMap ≫
        Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫
        specMapAlgAut k K σ := by
    dsimp [tensorAutMap, specMapAlgAut]
    rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj]
    apply CommRingCat.hom_ext
    ext a
    simp [tensorAut]
  have hmap : tensorAutMap ≫ affineIso.inv = affineIso.inv ≫ actionOnAffine := by
    apply pullback.hom_ext
    · rw [Category.assoc, hInvFst, hTensorFst, Category.assoc, hAffineFst, hInvFst]
    · rw [Category.assoc, hInvSnd, hTensorSnd, Category.assoc, hAffineSnd,
        ← Category.assoc, hInvSnd]
  show actionOnAffine ≫ affineIso.hom = affineIso.hom ≫ tensorAutMap
  rw [← Iso.inv_comp_eq, ← Category.assoc, ← hmap]
  simp

private theorem pullback_galoisAction_comp_hom (k K L : Type u) [Field k] [Field K]
    [Algebra k K] [CommRing L] [Algebra k L] (X : Over (Spec (.of k)))
    (q : Spec (.of L) ⟶ X.left)
    (hq : q ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k L))) (σ : K ≃ₐ[k] K) :
    pullback.map (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))) q
        (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))) q
        ((galoisActionOnBaseChange k K X).ρ (MulOpposite.op σ)) (𝟙 _) (𝟙 X.left)
        (by simpa using (galoisActionOnBaseChange_ρ_comp_fst k K X (.op σ)).symm) (by simp) ≫
      (pullbackSymmetry (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))) q ≪≫
        pullbackRightPullbackFstIso X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) q ≪≫
        pullback.congrHom hq rfl).hom =
    (pullbackSymmetry (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))) q ≪≫
        pullbackRightPullbackFstIso X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) q ≪≫
        pullback.congrHom hq rfl).hom ≫
      pullback.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))
        (Spec.map (CommRingCat.ofHom (algebraMap k L)))
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) (𝟙 _) (specMapAlgAut k K σ)
        (𝟙 (Spec (.of k))) rfl (by simp) := by
  let gK := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let p := pullback.fst X.hom gK
  let fL := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let a := (galoisActionOnBaseChange k K X).ρ (MulOpposite.op σ)
  let fiberIso : pullback p q ≅ pullback fL gK :=
    pullbackSymmetry p q ≪≫ pullbackRightPullbackFstIso X.hom gK q ≪≫ pullback.congrHom hq rfl
  let actionOnFiber : pullback p q ⟶ pullback p q := pullback.map p q p q a (𝟙 _) (𝟙 X.left)
    (by simpa using (galoisActionOnBaseChange_ρ_comp_fst k K X (.op σ)).symm) (by simp)
  let actionOnAffine := pullback.map fL gK fL gK (𝟙 _) (specMapAlgAut k K σ)
    (𝟙 (Spec (.of k))) rfl (by simp [gK])
  show actionOnFiber ≫ fiberIso.hom = fiberIso.hom ≫ actionOnAffine
  have hFst : fiberIso.hom ≫ pullback.fst fL gK = pullback.snd p q := by
    show ((pullbackSymmetry p q).hom ≫ (pullbackRightPullbackFstIso X.hom gK q).hom ≫
      (pullback.congrHom hq rfl).hom) ≫ pullback.fst fL gK = _
    simp only [fL, Category.assoc, pullback.congrHom_hom, pullback.map, pullback.lift_fst,
      Category.comp_id, pullbackRightPullbackFstIso_hom_fst]
    exact pullbackSymmetry_hom_comp_fst p q
  have hSnd : fiberIso.hom ≫ pullback.snd fL gK = pullback.fst p q ≫ pullback.snd X.hom gK := by
    show ((pullbackSymmetry p q).hom ≫ (pullbackRightPullbackFstIso X.hom gK q).hom ≫
      (pullback.congrHom hq rfl).hom) ≫ pullback.snd fL gK = _
    simp only [fL, Category.assoc, pullback.congrHom_hom, pullback.map, pullback.lift_snd,
      Category.comp_id, pullbackRightPullbackFstIso_hom_snd]
    exact pullbackSymmetry_hom_comp_snd_assoc p q (pullback.snd X.hom gK)
  have hFiberFst : actionOnFiber ≫ pullback.fst p q = pullback.fst p q ≫ a :=
    pullback_map_comp_fst
  have hFiberSnd : actionOnFiber ≫ pullback.snd p q = pullback.snd p q :=
    pullback_map_comp_snd.trans (Category.comp_id _)
  have hBaseSnd : a ≫ pullback.snd X.hom gK = pullback.snd X.hom gK ≫ specMapAlgAut k K σ :=
    galoisActionOnBaseChange_ρ_comp_snd k K X (.op σ)
  have hAffineFst : actionOnAffine ≫ pullback.fst fL gK = pullback.fst fL gK :=
    pullback_map_comp_fst.trans (Category.comp_id _)
  have hAffineSnd :
      actionOnAffine ≫ pullback.snd fL gK = pullback.snd fL gK ≫ specMapAlgAut k K σ :=
    pullback_map_comp_snd
  apply pullback.hom_ext
  · simp only [Category.assoc, hFst, hFiberSnd, hAffineFst]
  · rw [Category.assoc, hSnd, ← Category.assoc, hFiberFst, Category.assoc, hBaseSnd,
      ← Category.assoc, ← hSnd, Category.assoc, ← hAffineSnd, ← Category.assoc]

/-- For a `k`-algebra `L` and an `L`-point `q` of `X`, the pullback of `X_K ⟶ X` along `q` is
`Spec (K ⊗[k] L)`, compatibly with the Galois twist `id × Spec σ` and `σ ⊗ id`. -/
private theorem exists_pullbackIso_galoisAction_comp (k K L : Type u) [Field k] [Field K]
    [Algebra k K] [CommRing L] [Algebra k L] (X : Over (Spec (.of k)))
    (q : Spec (.of L) ⟶ X.left)
    (hq : q ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k L))) :
    ∃ e : pullback (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))) q ≅
        Spec (.of (K ⊗[k] L)), ∀ σ : K ≃ₐ[k] K,
      pullback.map (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))) q
          (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))) q
          ((galoisActionOnBaseChange k K X).ρ (MulOpposite.op σ)) (𝟙 _) (𝟙 X.left)
          (by simpa using (galoisActionOnBaseChange_ρ_comp_fst k K X (.op σ)).symm)
          (by simp) ≫ e.hom =
        e.hom ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.congr σ
          (AlgEquiv.refl (R := k) (A₁ := L))).toRingEquiv.toRingHom) := by
  let gK := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let p := pullback.fst X.hom gK
  let fL := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let fiberIso : pullback p q ≅ pullback fL gK :=
    pullbackSymmetry p q ≪≫ pullbackRightPullbackFstIso X.hom gK q ≪≫ pullback.congrHom hq rfl
  let affineIso : pullback fL gK ≅ Spec (.of (K ⊗[k] L)) :=
    pullbackSpecIso k L K ≪≫ (Scheme.Spec.mapIso
      ((Algebra.TensorProduct.comm k L K).toRingEquiv.toCommRingCatIso.op)).symm
  refine ⟨fiberIso ≪≫ affineIso, fun σ => ?_⟩
  let actionOnFiber : pullback p q ⟶ pullback p q :=
    pullback.map p q p q ((galoisActionOnBaseChange k K X).ρ (MulOpposite.op σ)) (𝟙 _)
      (𝟙 X.left) (by simpa using (galoisActionOnBaseChange_ρ_comp_fst k K X (.op σ)).symm)
      (by simp)
  let actionOnAffine := pullback.map fL gK fL gK (𝟙 _) (specMapAlgAut k K σ)
    (𝟙 (Spec (.of k))) rfl (by simp [gK])
  let tensorAutMap := Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.congr σ
    (AlgEquiv.refl (R := k) (A₁ := L))).toRingEquiv.toRingHom)
  have hFiber : actionOnFiber ≫ fiberIso.hom = fiberIso.hom ≫ actionOnAffine :=
    pullback_galoisAction_comp_hom k K L X q hq σ
  have hAffine : actionOnAffine ≫ affineIso.hom = affineIso.hom ≫ tensorAutMap :=
    pullbackSpecIso_comm_hom_galoisTwist k K L σ
  show actionOnFiber ≫ (fiberIso ≪≫ affineIso).hom =
    (fiberIso ≪≫ affineIso).hom ≫ tensorAutMap
  rw [Iso.trans_hom, ← Category.assoc, hFiber, Category.assoc, hAffine, ← Category.assoc]

/-- Over a normal extension `K/k`, the group `K ≃ₐ[k] K` acts transitively on the points of
`X_K` lying over a fixed `L`-point of `X`, for a field extension `L/k`. -/
private theorem exists_galoisAction_pullback_fst_eq (k K L : Type u) [Field k] [Field K]
    [Algebra k K] [Normal k K] [Field L] [Algebra k L] (X : Over (Spec (.of k)))
    (q : Spec (.of L) ⟶ X.left)
    (hq : q ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k L)))
    (x y : pullback (C := Scheme)
      (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))) q) :
    ∃ σ : K ≃ₐ[k] K, ((galoisActionOnBaseChange k K X).ρ (MulOpposite.op σ)).base
        (pullback.fst (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))) q x) =
      pullback.fst (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))) q y := by
  let p := pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  obtain ⟨e, he⟩ := exists_pullbackIso_galoisAction_comp k K L X q hq
  let P : PrimeSpectrum (K ⊗[k] L) := e.hom.base y
  let Q : PrimeSpectrum (K ⊗[k] L) := e.hom.base x
  obtain ⟨σ, hσ⟩ := gal_acts_transitively_on_primes_of_normal (k := k) (K := L) (kbar := K) P Q
  refine ⟨σ, ?_⟩
  let a := (galoisActionOnBaseChange k K X).ρ (MulOpposite.op σ)
  let actionOnFiber : pullback p q ⟶ pullback p q := pullback.map p q p q a (𝟙 _) (𝟙 X.left)
    (by simpa using (galoisActionOnBaseChange_ρ_comp_fst k K X (.op σ)).symm) (by simp)
  have hpoints : e.hom.base (actionOnFiber x) = e.hom.base y := by
    have heq := congrArg (fun f : pullback p q ⟶ Spec (.of (K ⊗[k] L)) => f.base.hom x) (he σ)
    simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.coe_comp,
      Function.comp_apply] at heq
    have hprime : (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.congr σ
        (AlgEquiv.refl (R := k) (A₁ := L))).toRingEquiv.toRingHom)).base Q = P := by
      show PrimeSpectrum.comap (Algebra.TensorProduct.congr σ
        (AlgEquiv.refl (R := k) (A₁ := L))).toAlgHom.toRingHom Q = P
      exact hσ
    exact heq.trans hprime
  have hfiber : actionOnFiber x = y := by
    simpa using congrArg (fun z : PrimeSpectrum (K ⊗[k] L) => e.inv.base z) hpoints
  have hfst : actionOnFiber ≫ pullback.fst p q = pullback.fst p q ≫ a :=
    pullback_map_comp_fst
  have h := congrArg (fun f : pullback p q ⟶ pullback X.hom
    (Spec.map (CommRingCat.ofHom (algebraMap k K))) => f.base.hom x) hfst
  simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.coe_comp,
    Function.comp_apply] at h
  rw [← hfiber]
  exact h.symm

/-- Over a normal extension, the group of `k`-automorphisms of `K` acts transitively on the
points of a base change lying over a fixed point of the original scheme. -/
private theorem galoisAction_transitive_on_points_over
    (k K : Type u) [Field k] [Field K] [Algebra k K] [Normal k K]
    (X : Over (Spec (.of k))) (η : X.left)
    (x y : pullback (C := Scheme) X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (hx : (pullback.fst X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base x = η)
    (hy : (pullback.fst X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y = η) :
    ∃ σ : K ≃ₐ[k] K,
      ((galoisActionOnBaseChange k K X).ρ (MulOpposite.op σ)).base x = y := by
  classical
  let gK := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let p := pullback.fst X.hom gK
  let q := X.left.fromSpecResidueField η
  let s := X.hom η
  let : s.asIdeal.IsPrime := s.2
  let : Algebra k (X.left.residueField η) :=
    ((CommRingCat.ofHom (algebraMap k s.asIdeal.ResidueField) ≫
      (Scheme.Spec.residueFieldIso (.of k) s).inv ≫ X.hom.residueFieldMap η).hom).toAlgebra
  have hbase :
      q ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k (X.left.residueField η))) := by
    show X.left.fromSpecResidueField η ≫ X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap k s.asIdeal.ResidueField) ≫
        (Scheme.Spec.residueFieldIso (.of k) s).inv ≫ X.hom.residueFieldMap η)
    rw [Spec.map_comp, Spec.map_comp, Category.assoc,
      Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
    exact (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField X.hom η).symm
  obtain ⟨σ, hσ⟩ := exists_galoisAction_pullback_fst_eq k K (X.left.residueField η) X q hbase
    ((p.fiberHomeo η).symm ⟨x, hx⟩) ((p.fiberHomeo η).symm ⟨y, hy⟩)
  exact ⟨σ, by
    convert hσ using 2 <;> exact (p.fiberι_fiberHomeo_symm η ⟨_, ‹_›⟩).symm⟩

/-- The canonical map from the irreducible components of a field-extension base change to the
irreducible components of the original scheme. -/
public def irreducibleComponentsBaseChangeMap
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Over (Spec (.of k))) :
    (galoisActionOnGeometricIrreducibleComponents k K X).V →
      irreducibleComponents X.left :=
  Set.MapsTo.restrict
    (fun Z ↦
      (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base '' Z)
    (irreducibleComponents
      (pullback (C := Scheme) X.hom
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
    (irreducibleComponents X.left)
    (mapsTo_irreducibleComponents_baseChange k K X.left X.hom)

/-- If a morphism carries one irreducible component onto another, it carries the generic point
of the first to the generic point of the second. -/
private theorem genericPoint_map_eq_of_image_component
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (A : irreducibleComponents Y) (B : irreducibleComponents X)
    (hAB : f.base '' (A : Set Y) = (B : Set X)) :
    f.base (genericPoints.ofComponent A).1 = (genericPoints.ofComponent B).1 := by
  apply IsGenericPoint.eq _ (genericPoints.isGenericPoint_ofComponent B)
  have hclosed : IsClosed (f.base '' (A : Set Y)) := by
    rw [hAB]
    exact isClosed_of_mem_irreducibleComponents B.1 B.2
  have h := (genericPoints.isGenericPoint_ofComponent A).image f.continuous
  rwa [hclosed.closure_eq, hAB] at h

/-- The canonical map on irreducible components is invariant under the Galois action. -/
private theorem irreducibleComponentsBaseChangeMap_galoisAction
    (k K : Type u) [Field k] [Field K] [Algebra k K] (X : Over (Spec (.of k)))
    (σ : MulOpposite (K ≃ₐ[k] K)) (Z : (galoisActionOnGeometricIrreducibleComponents k K X).V) :
    irreducibleComponentsBaseChangeMap k K X
        (ConcreteCategory.hom ((galoisActionOnGeometricIrreducibleComponents k K X).ρ σ) Z) =
      irreducibleComponentsBaseChangeMap k K X Z := by
  let gK := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let Y := pullback (C := Scheme) X.hom gK
  let p := pullback.fst X.hom gK
  let a := (galoisActionOnBaseChange k K X).ρ σ
  have hprojPoint (x : Y) : p.base (a.base x) = p.base x := by
    have hh := congrArg (fun f : Y ⟶ X.left => f.base x)
      (galoisActionOnBaseChange_ρ_comp_fst k K X σ)
    simpa [Scheme.Hom.comp_base, TopCat.hom_comp] using hh
  apply Subtype.ext
  show p.base '' (ConcreteCategory.hom
    ((galoisActionOnGeometricIrreducibleComponents k K X).ρ σ) Z).1 = p.base '' Z.1
  rw [galoisActionOnGeometricIrreducibleComponents_ρ_apply_coe]
  show p.base '' ((fun x : Y => a.base x) '' Z.1) = p.base '' Z.1
  ext y
  simp only [Set.mem_image]
  constructor
  · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, (hprojPoint z).symm⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨a.base z, ⟨z, hz, rfl⟩, hprojPoint z⟩

/-- Over a normal extension `K/k`, two geometric irreducible components with the same image
downstairs are conjugate under `K ≃ₐ[k] K`. -/
private theorem exists_galoisAction_eq_of_irreducibleComponentsBaseChangeMap_eq
    (k K : Type u) [Field k] [Field K] [Algebra k K] [Normal k K] (X : Over (Spec (.of k)))
    (Z W : (galoisActionOnGeometricIrreducibleComponents k K X).V)
    (hWZ : irreducibleComponentsBaseChangeMap k K X W =
      irreducibleComponentsBaseChangeMap k K X Z) :
    ∃ σ : MulOpposite (K ≃ₐ[k] K),
      ConcreteCategory.hom ((galoisActionOnGeometricIrreducibleComponents k K X).ρ σ) Z = W := by
  let gK := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let Y := pullback (C := Scheme) X.hom gK
  let p := pullback.fst X.hom gK
  let F := irreducibleComponentsBaseChangeMap k K X
  let Zc : irreducibleComponents Y := Z
  let Wc : irreducibleComponents Y := W
  let ξZ : genericPoints Y := genericPoints.ofComponent Zc
  let ξW : genericPoints Y := genericPoints.ofComponent Wc
  let T : irreducibleComponents X.left := F Z
  let ξT : genericPoints X.left := genericPoints.ofComponent T
  have hξZ : IsGenericPoint ξZ.1 Zc := genericPoints.isGenericPoint_ofComponent Zc
  have hξW : IsGenericPoint ξW.1 Wc := genericPoints.isGenericPoint_ofComponent Wc
  have hηZ := genericPoint_map_eq_of_image_component p Zc T rfl
  have hηW := genericPoint_map_eq_of_image_component p Wc T
    (by change p.base '' (Wc : Set Y) = ((F Z : irreducibleComponents X.left) : Set X.left)
        exact congrArg Subtype.val hWZ)
  obtain ⟨σ, hσ⟩ := galoisAction_transitive_on_points_over k K X ξT.1 ξZ.1 ξW.1 hηZ hηW
  refine ⟨MulOpposite.op σ, ?_⟩
  let C : irreducibleComponents Y := ConcreteCategory.hom
    ((galoisActionOnGeometricIrreducibleComponents k K X).ρ (MulOpposite.op σ)) Z
  let a := (galoisActionOnBaseChange k K X).ρ (MulOpposite.op σ)
  have hCset : (C : Set Y) = a.base '' (Zc : Set Y) := by
    show (ConcreteCategory.hom
      ((galoisActionOnGeometricIrreducibleComponents k K X).ρ (MulOpposite.op σ)) Z).1 =
        a.base '' (Zc : Set Y)
    rw [galoisActionOnGeometricIrreducibleComponents_ρ_apply_coe]
    rfl
  have hclosed : IsClosed (a.base '' (Zc : Set Y)) := by
    rw [← hCset]
    exact isClosed_of_mem_irreducibleComponents C.1 C.2
  have hCgen := hξZ.image a.continuous
  rw [hclosed.closure_eq] at hCgen
  exact Subtype.ext <| calc
    (C : Set Y) = closure {a.base ξZ.1} := hCgen.def.symm
    _ = closure {ξW.1} := by rw [hσ]
    _ = (Wc : Set Y) := hξW.def

/-- **Stacks Project, Tag 04KY.** For a scheme over a field `k` and a normal extension `K/k`,
for instance a separable closure of `k`, the fibre through each geometric irreducible component
of the canonical map to the irreducible components downstairs is its orbit under the group
`K ≃ₐ[k] K`. -/
@[stacks 04KY]
public theorem fiber_irreducibleComponentsBaseChangeMap_eq_orbit
    (k K : Type u) [Field k] [Field K] [Algebra k K] [Normal k K]
    (X : Over (Spec (.of k)))
    (Z : (galoisActionOnGeometricIrreducibleComponents k K X).V) :
    (irreducibleComponentsBaseChangeMap k K X) ⁻¹'
        {irreducibleComponentsBaseChangeMap k K X Z} =
      Set.range (fun σ : MulOpposite (K ≃ₐ[k] K) ↦
        ConcreteCategory.hom
          ((galoisActionOnGeometricIrreducibleComponents k K X).ρ σ) Z) := by
  ext W
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_range]
  refine ⟨exists_galoisAction_eq_of_irreducibleComponentsBaseChangeMap_eq k K X Z W, ?_⟩
  rintro ⟨σ, rfl⟩
  exact irreducibleComponentsBaseChangeMap_galoisAction k K X σ Z

end AlgebraicGeometry
