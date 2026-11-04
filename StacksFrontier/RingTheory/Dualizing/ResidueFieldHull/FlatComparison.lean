module

public import StacksFrontier.RingTheory.Dualizing.ResidueFieldHull.PowerTorsionFiltration

/-!
# Injective hulls of residue fields along a flat local homomorphism

Let `R → S` be a flat local homomorphism of Noetherian local rings whose closed fibre is trivial,
i.e. `R / 𝔪_R → S / 𝔪_R S` is bijective.  This file shows that an injective hull of the residue
field of `S`, viewed as an `R`-module, is an injective hull of the residue field of `R`, compatibly
with the induced identification of residue fields.

It was split from `StacksFrontier.RingTheory.Dualizing.ResidueFieldHull`, which re-exports it.

## Main definitions

* `Dualizing.closedFiberMap` and `Dualizing.residueFieldMap` — the comparison maps attached to a
  local homomorphism `R → S`.

## Main results

* `Dualizing.exists_iso_injectiveHull_residueField` — comparison of injective hulls along a flat
  local homomorphism with trivial closed fibre.

## References

* [Stacks Project, Tag 08Z5](https://stacks.math.columbia.edu/tag/08Z5)
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace Dualizing

section FlatComparison

open IsLocalRing

/-- The canonical map from the residue field of `R` to the closed fibre of an
`R`-algebra `S`. -/
public def closedFiberMap
    (R S : Type u) [CommRing R] [CommRing S] [IsLocalRing R]
    [Algebra R S] :
    R ⧸ maximalIdeal R →+* S ⧸ (maximalIdeal R).map (algebraMap R S) :=
  Ideal.quotientMap ((maximalIdeal R).map (algebraMap R S))
    (algebraMap R S) Ideal.le_comap_map

/-- The map on residue fields induced by a local homomorphism, viewed after
restriction of scalars as a morphism of modules over the source ring. -/
public noncomputable def residueFieldMap
    (R S : Type u) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)] :
    ModuleCat.of R (ResidueField R) ⟶
      (ModuleCat.restrictScalars (algebraMap R S)).obj
        (ModuleCat.of S (ResidueField S)) :=
  ModuleCat.ofHom
    (X := ModuleCat.of R (ResidueField R))
    (Y := (ModuleCat.restrictScalars (algebraMap R S)).obj
      (ModuleCat.of S (ResidueField S)))
    ({
      toFun := ResidueField.map (algebraMap R S)
      map_add' := map_add _
      map_smul' := fun r x ↦ by
        change ResidueField.map (algebraMap R S) (residue R r * x) =
          residue S (algebraMap R S r) *
            ResidueField.map (algebraMap R S) x
        rw [map_mul, ResidueField.map_residue]
    } : ResidueField R →ₗ[R]
      (ModuleCat.restrictScalars (algebraMap R S)).obj
        (ModuleCat.of S (ResidueField S)))

private theorem quotientMap_maximalIdealPow_bijective
    (R S : Type u) [CommRing R] [CommRing S] [IsLocalRing R]
    [Algebra R S] (hflat : RingHom.Flat (algebraMap R S))
    (hclosed : Function.Bijective (closedFiberMap R S)) (n : ℕ) :
    Function.Bijective
      (Ideal.quotientMap
        (((maximalIdeal R) ^ (n + 1)).map (algebraMap R S))
        (algebraMap R S) Ideal.le_comap_map) := by
  let I := maximalIdeal R
  let M := R ⧸ I ^ (n + 1)
  have hT : IsIPowerTorsion R M I := by
    intro x
    refine ⟨n + 1, Nat.succ_pos n, ?_⟩
    intro a ha
    induction x using Quotient.inductionOn' with
    | _ x =>
      change Ideal.Quotient.mk (I ^ (n + 1)) (a * x) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mul_mem_right _ _ ha)
  have hflat' : Module.Flat R S := (RingHom.flat_algebraMap_iff).mp hflat
  have hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S)
        Ideal.le_comap_map) := by
    simpa [I, closedFiberMap] using hclosed
  have hunit :=
    (IPowerTorsion.baseChange_bijective_iff_quotientMap_bijective
      R S I hflat').2 hquot
  have hunitM := hunit M hT
  let e : TensorProduct R M S ≃ₗ[R] S ⧸ (I ^ (n + 1)).map (algebraMap R S) :=
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor
      S (I ^ (n + 1))).symm.toLinearEquiv.restrictScalars R
  let q : R ⧸ I ^ (n + 1) →+* S ⧸ (I ^ (n + 1)).map (algebraMap R S) :=
    Ideal.quotientMap ((I ^ (n + 1)).map (algebraMap R S))
      (algebraMap R S) Ideal.le_comap_map
  have he (x : M) : e ((TensorProduct.mk R M S).flip 1 x) = q x := by
    induction x using Quotient.inductionOn' with
    | _ x =>
      dsimp [e]
      change (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S
        (I ^ (n + 1))).symm (Ideal.Quotient.mk (I ^ (n + 1)) x ⊗ₜ[R] (1 : S)) =
          q (Ideal.Quotient.mk (I ^ (n + 1)) x)
      rw [AlgEquiv.symm_apply_eq]
      simpa [q] using
        ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor S
          (I ^ (n + 1))).commutes (Ideal.Quotient.mk (I ^ (n + 1)) x)).symm
  have hcomp : Function.Bijective (fun x : M ↦ e ((TensorProduct.mk R M S).flip 1 x)) :=
    e.bijective.comp hunitM
  rw [show (fun x : M ↦ e ((TensorProduct.mk R M S).flip 1 x)) = q from funext he] at hcomp
  simpa [q, I] using hcomp

private theorem residueFieldMap_bijective
    (R S : Type u) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    (hclosed : Function.Bijective (closedFiberMap R S)) :
    Function.Bijective (ResidueField.map (algebraMap R S)) := by
  let J := (maximalIdeal R).map (algebraMap R S)
  refine ⟨RingHom.injective _, fun y => ?_⟩
  obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨x, hx⟩ := hclosed.2 (Ideal.Quotient.mk J s)
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨residue R r, ?_⟩
  rw [ResidueField.map_residue]
  have hq : Ideal.Quotient.mk J (algebraMap R S r) = Ideal.Quotient.mk J s := by
    simpa [closedFiberMap] using hx
  have hdiff : algebraMap R S r - s ∈ maximalIdeal S :=
    IsLocalRing.map_maximalIdeal_le (algebraMap R S) (Ideal.Quotient.eq.mp hq)
  rw [← sub_eq_zero, ← map_sub]
  exact (IsLocalRing.residue_eq_zero_iff _).mpr hdiff

-- Match the accepted statement's synthesized ModuleCat limits instance.
attribute [-instance] ModuleCat.abelian

/-- **Stacks Project, Tag 08Z5.** Injective hulls of the residue fields of a
flat local homomorphism with trivial closed fibre agree after restriction of
scalars.  The comparison isomorphism extends the induced identification of
residue fields. -/
@[stacks 08Z5]
public theorem exists_iso_injectiveHull_residueField
    (R S : Type u) [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing R]
    [IsNoetherianRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)]
    (hflat : RingHom.Flat (algebraMap R S))
    (hclosed : Function.Bijective (closedFiberMap R S))
    {E_R : ModuleCat.{u} R} {E_S : ModuleCat.{u} S}
    (i_R : ModuleCat.of R (ResidueField R) ⟶ E_R)
    (i_S : ModuleCat.of S (ResidueField S) ⟶ E_S)
    [Mono i_R] [Mono i_S]
    (hR : Module.IsInjectiveHull i_R)
    (hS : Module.IsInjectiveHull i_S) :
    ∃ e : E_R ≅ (ModuleCat.restrictScalars (algebraMap R S)).obj E_S,
      i_R ≫ e.hom = residueFieldMap R S ≫
        (ModuleCat.restrictScalars (algebraMap R S)).map i_S := by
  classical
  let : Abelian (ModuleCat R) := ModuleCat.abelian
  let f := algebraMap R S
  have hresHom : Function.Bijective (residueFieldMap R S).hom :=
    residueFieldMap_bijective R S hclosed
  let ke : ResidueField R ≃ₗ[R]
      (ModuleCat.restrictScalars f).obj (ModuleCat.of S (ResidueField S)) :=
    LinearEquiv.ofBijective (residueFieldMap R S).hom hresHom
  let jS := (ModuleCat.restrictScalars f).map i_S
  let j : ModuleCat.of R (ResidueField R) ⟶ (ModuleCat.restrictScalars f).obj E_S :=
    residueFieldMap R S ≫ jS
  have : Mono (residueFieldMap R S) :=
    (ModuleCat.mono_iff_injective _).2 hresHom.1
  have : Mono j := by dsimp [j]; infer_instance
  let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat
  have hI : Injective ((ModuleCat.restrictScalars f).obj E_S) :=
    (ModuleCat.extendRestrictScalarsAdj f).map_injective _ hS.1
  have hEss : Module.IsEssentialMono j := by
    intro Q hQ
    let ordR := ModuleCat.subobjectModule ((ModuleCat.restrictScalars f).obj E_S)
    let N := ordR Q
    have hN : N ≠ ⊥ := fun h => hQ (ordR.injective (by simpa [N] using h))
    obtain ⟨x, hxN, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN
    let : Module R E_S := Module.compHom E_S f
    change E_S at x
    let ordS := ModuleCat.subobjectModule (ModuleCat.of S E_S)
    let Qs := ordS.symm (Submodule.span S ({x} : Set E_S))
    have hspan : Submodule.span S ({x} : Set E_S) ≠ ⊥ := by
      intro h
      apply hx0
      have hxspan : x ∈ Submodule.span S ({x} : Set E_S) :=
        Submodule.subset_span (by simp)
      have hxS0 : x = 0 := by simpa [h] using hxspan
      exact hxS0
    have hQs : Qs ≠ ⊥ := by
      intro h
      apply hspan
      simpa [Qs] using congrArg ordS h
    have hmeetS : Qs ⊓ Subobject.mk i_S ≠ ⊥ := hS.2 Qs hQs
    have hL : ordS (Qs ⊓ Subobject.mk i_S) ≠ ⊥ := by
      intro h
      exact hmeetS (ordS.injective (by simpa using h))
    obtain ⟨y, hyL, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hL
    have hyParts : y ∈ ordS Qs ⊓ ordS (Subobject.mk i_S) := by
      simpa only [OrderIso.map_inf] using hyL
    have hySpan : y ∈ Submodule.span S ({x} : Set E_S) := by
      simpa [Qs] using hyParts.1
    have hyRange : y ∈ LinearMap.range i_S.hom := by
      rw [← subobjectModule_mk_eq_range i_S]
      exact hyParts.2
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hySpan
    let T : ℕ →o Submodule S E_S :=
      ⟨fun n ↦ maximalIdealPowTorsion S E_S n,
        fun m n hmn ↦ Submodule.torsionBySet_le_torsionBySet_pow
          (m + 1) (n + 1) (Nat.add_le_add_right hmn 1) _⟩
    have htop : (⨆ n : ℕ, T n) = ⊤ := by
      change (⨆ n : ℕ, maximalIdealPowTorsion S E_S n) = ⊤
      exact iSup_maximalIdealPowTorsion_eq_top S
        (ModuleCat.of S (ResidueField S)) E_S (LinearEquiv.refl S _) i_S hS
    have hxTop : x ∈ ⨆ n : ℕ, T n := by rw [htop]; exact Submodule.mem_top
    obtain ⟨n, hn⟩ :=
      (Submodule.mem_iSup_of_directed T T.monotone.directed_le).mp hxTop
    change x ∈ Submodule.torsionBySet S E_S
      ((maximalIdeal S) ^ (n + 1) : Ideal S) at hn
    rw [Submodule.mem_torsionBySet_iff] at hn
    have hquot := quotientMap_maximalIdealPow_bijective R S hflat hclosed n
    let Ipow := (maximalIdeal R) ^ (n + 1)
    obtain ⟨rbar, hrbar⟩ := hquot.2 (Ideal.Quotient.mk (Ipow.map f) s)
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective rbar
    have hquotEq : Ideal.Quotient.mk (Ipow.map f) (f r) =
        Ideal.Quotient.mk (Ipow.map f) s := by
      change Ideal.quotientMap (Ipow.map f) f Ideal.le_comap_map
          (Ideal.Quotient.mk Ipow r) = _ at hrbar
      simpa [Ideal.quotientMap_mk] using hrbar
    have hJle : (maximalIdeal R).map f ≤ maximalIdeal S :=
      IsLocalRing.map_maximalIdeal_le f
    have hdiffS : s - f r ∈ (maximalIdeal S) ^ (n + 1) := by
      have hpow : Ipow.map f ≤ (maximalIdeal S) ^ (n + 1) := by
        change ((maximalIdeal R) ^ (n + 1)).map f ≤ (maximalIdeal S) ^ (n + 1)
        rw [Ideal.map_pow]
        exact pow_le_pow_left' hJle (n + 1)
      apply hpow
      simpa only [neg_sub] using
        (Ipow.map f).neg_mem (Ideal.Quotient.eq.mp hquotEq)
    have hsx : s • x = f r • x := by
      rw [← sub_add_cancel s (f r), add_smul, hn ⟨s - f r, hdiffS⟩, zero_add]
    have hyR : y = r • x := hs.symm.trans hsx
    have hyN : y ∈ N := hyR ▸ N.smul_mem r hxN
    obtain ⟨zS, hzS⟩ := hyRange
    let zS' : ↑((ModuleCat.restrictScalars f).obj
        (ModuleCat.of S (ResidueField S))) := zS
    have hjy : j.hom (ke.symm zS') = y := by
      change i_S.hom (ke (ke.symm zS')) = y
      rw [ke.apply_symm_apply]
      simpa [zS'] using hzS
    have hInf : N ⊓ LinearMap.range j.hom ≠ ⊥ :=
      (Submodule.ne_bot_iff _).2 ⟨y, ⟨hyN, ⟨_, hjy⟩⟩, hy0⟩
    have hmap : ordR (Q ⊓ Subobject.mk j) = N ⊓ LinearMap.range j.hom := by
      rw [OrderIso.map_inf]
      change ordR Q ⊓ ordR (Subobject.mk j) = N ⊓ LinearMap.range j.hom
      rw [subobjectModule_mk_eq_range]
    intro hzero
    exact (hInf (by rw [← hmap]; simpa using congrArg ordR hzero)).elim
  have hHull : Module.IsInjectiveHull j := ⟨hI, hEss⟩
  obtain ⟨fext, hfext⟩ := hI.factors j i_R
  have hcomm : i_R ≫ fext = (Iso.refl _).hom ≫ j := by simpa using hfext
  have hIso := Module.isIso_of_isInjectiveHull_of_extends_iso
    i_R j hR hHull (Iso.refl _) fext hcomm
  let e : E_R ≅ (ModuleCat.restrictScalars f).obj E_S := asIso fext
  exact ⟨e, by simpa [e, j, jS] using hcomm⟩

attribute [instance] ModuleCat.abelian

end FlatComparison

end Dualizing
