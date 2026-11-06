module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Algebra.DirectLimit.Descent
public import StacksFrontier.RingTheory.Flat.OpenFlatLocus
public import StacksFrontier.RingTheory.Flat.OpenFlatLocusNoetherian
public import StacksFrontier.RingTheory.Flat.SyzygyFreeLocus
public import StacksFrontier.RingTheory.SpreadingOut.FlatModel
public import StacksFrontier.RingTheory.Flat.TowerLTensor
public import StacksFrontier.RingTheory.Flat.ClosedSubset.FlatAlongZeroLocus
public import StacksFrontier.RingTheory.Flat.ClosedSubset.DirectedColimit

/-!
# Descent of flatness along a closed subset from a directed colimit

Let `R → S` be a finitely presented map of commutative rings, `M` a finitely presented
`S`-module and `A` a directed system of `R`-algebras with a compatible family of ideals `I i`.
If, after base change to the colimit of `A`, the module is flat along the inverse image of the
zero locus of the colimit ideal, then the same holds at some stage `A i`. We first show that
relative flatness after extension of scalars holds at all sufficiently large stages, then pass
to finite principal-open covers of the closed subset.

## Main results

* `Module.Flat.eventually_flat_tensorProduct_of_isDirectedColimit`: eventual flatness in a
  directed system of finitely presented algebras.
* `Module.Flat.exists_ge_flat_localizationAway_tensorProduct`: the same after localizing at an
  element.
* `Module.exists_flatAlongZeroLocus_baseChange_of_colimit`: descent from a directed colimit.

## References

* [The Stacks Project, Tag 05LM](https://stacks.math.columbia.edu/tag/05LM)
-/

@[expose] public section

open scoped TensorProduct

universe u v w x uS uM uL uT uA uB uLam

/-! ### Eventual flatness in a directed system of finitely presented algebras -/

/-- Restricting scalars along `algebraMap` of a scalar tower recovers the given module structure. -/
private theorem compHom_algebraMap_eq
    {A B N : Type*} [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup N] [Module A N]
    [Module B N] [IsScalarTower A B N] :
    Module.compHom N (algebraMap A B) = (inferInstance : Module A N) :=
  Module.ext' _ _ fun c x => IsScalarTower.algebraMap_smul B c x

/-- Flatness of `B' ⊗[S] M` over `A` transfers along an algebra isomorphism `B ≃ B'` that is both
`S`-linear and `A`-linear. -/
private theorem flat_tensorProduct_of_algEquiv
    {A S B B' M : Type*} [CommRing A] [CommRing S] [CommRing B] [CommRing B'] [Algebra S B]
    [Algebra S B'] [Algebra A B] [Algebra A B'] [AddCommGroup M] [Module S M]
    [SMulCommClass S A B] [SMulCommClass S A B'] (e : B ≃ₐ[S] B') (e' : B ≃ₐ[A] B')
    (he : ∀ x, e' x = e x) [Module.Flat A (B' ⊗[S] M)] : Module.Flat A (B ⊗[S] M) := by
  let e0 : B ⊗[S] M ≃ₗ[S] B' ⊗[S] M := TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl S M)
  refine Module.Flat.of_linearEquiv (e0.toAddEquiv.toLinearEquiv (fun c x => ?_) :
    B ⊗[S] M ≃ₗ[A] B' ⊗[S] M)
  induction x with
  | tmul t m =>
    rw [TensorProduct.smul_tmul' c t m]
    change e0 ((c • t) ⊗ₜ[S] m) = c • e0 (t ⊗ₜ[S] m)
    simp only [e0, TensorProduct.congr_tmul, LinearEquiv.refl_apply, AlgEquiv.toLinearEquiv_apply]
    rw [TensorProduct.smul_tmul' c (e t) m]
    refine congrArg (fun t : B' => t ⊗ₜ[S] m) ?_
    rw [← he, ← he]
    exact e'.toLinearEquiv.map_smul c t
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

set_option backward.isDefEq.respectTransparency false in
/-- In a compatible system of finitely presented algebras, relative flatness of a fixed module
after extension of scalars holds at every sufficiently large stage. -/
theorem Module.Flat.eventually_flat_tensorProduct_of_isDirectedColimit
    {S : Type uS} [CommRing S] (M : Type uM) [AddCommGroup M] [Module S M]
    [Module.FinitePresentation S M]
    {Λ : Type uLam} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    (A : Λ → Type uA) [∀ i, CommRing (A i)]
    (a : ∀ i j, i ≤ j → A i →+* A j) [DirectedSystem A (fun i j h => a i j h)]
    {B : Λ → Type uB} [∀ i, CommRing (B i)] [∀ i, Algebra S (B i)]
    {b : ∀ ⦃i j⦄, i ≤ j → B i →ₐ[S] B j}
    {L : Type uL} [CommRing L] {T : Type uT} [CommRing T] [Algebra S T]
    [Algebra L T] [Algebra.FinitePresentation L T]
    (ρ : ∀ i, A i →+* L) {σ : ∀ i, B i →ₐ[S] T}
    (hcB : IsDirectedColimit B b T σ)
    (g : ∀ i, A i →+* B i)
    (hg : ∀ i j (h : i ≤ j), (g j).comp (a i j h) = (b h).toRingHom.comp (g i))
    (hρ : ∀ i j (h : i ≤ j), ρ j ∘ a i j h = ρ i)
    (hρsurj : ∀ z : L, ∃ i y, ρ i y = z)
    (hρzero : ∀ i y, ρ i y = 0 → ∃ j, ∃ h : i ≤ j, a i j h y = 0)
    (hσg : ∀ i, (algebraMap L T).comp (ρ i) = (σ i).toRingHom.comp (g i))
    (hfp : ∀ i, letI : Algebra (A i) (B i) := (g i).toAlgebra
      Algebra.FinitePresentation (A i) (B i))
    (hpush : ∀ i j (h : i ≤ j),
      letI : Algebra (A i) (B i) := (g i).toAlgebra
      letI : Algebra (A i) (A j) := (a i j h).toAlgebra
      letI : Algebra (B i) (B j) := (b h).toRingHom.toAlgebra
      letI : Algebra (A j) (B j) := (g j).toAlgebra
      letI : Algebra (A i) (B j) := ((g j).comp (a i j h)).toAlgebra
      letI : IsScalarTower (A i) (A j) (B j) :=
        IsScalarTower.of_algebraMap_smul fun _ _ => rfl
      letI : IsScalarTower (A i) (B i) (B j) :=
        IsScalarTower.of_algebraMap_smul fun z y => by
          change b h (g i z) * y = g j (a i j h z) * y
          exact congrArg (fun t : B j => t * y)
            (by simpa using (RingHom.congr_fun (hg i j h) z).symm)
      Algebra.IsPushout (A i) (A j) (B i) (B j))
    [Module.Flat L (T ⊗[S] M)] :
    ∃ i, ∀ j, i ≤ j →
      letI : Module (A j) (B j ⊗[S] M) := Module.compHom (B j ⊗[S] M) (g j)
      Module.Flat (A j) (B j ⊗[S] M) := by
  let algAB : ∀ i, Algebra (A i) (B i) := fun i => (g i).toAlgebra
  have hfp' : ∀ i, Algebra.FinitePresentation (A i) (B i) := hfp
  have hsmallB : ∀ i, Small.{uA} (B i) := fun i => by
    have := hfp' i
    have : Algebra.FiniteType (A i) (B i) := inferInstance
    exact Algebra.FiniteType.small (R := A i)
  have hsmallT : Small.{uL} T := by
    have : Algebra.FiniteType L T := inferInstance
    exact Algebra.FiniteType.small (R := L)
  let B' : Λ → Type uA := fun i => Shrink.{uA} (B i)
  let T' : Type uL := Shrink.{uL} T
  let eB : ∀ i, B' i ≃ₐ[S] B i := fun i => Shrink.algEquiv S (B i)
  let eBA : ∀ i, B' i ≃ₐ[A i] B i := fun i => Shrink.algEquiv (A i) (B i)
  let eT : T' ≃ₐ[S] T := Shrink.algEquiv S T
  let eTL : T' ≃ₐ[L] T := Shrink.algEquiv L T
  have heBA : ∀ i (z : B' i), eBA i z = eB i z := fun _ _ => rfl
  have heTL : ∀ z : T', eTL z = eT z := fun _ => rfl
  let b' : ∀ ⦃i j⦄, i ≤ j → B' i →ₐ[S] B' j :=
    fun {i j} h => (eB j).symm.toAlgHom.comp ((b h).comp (eB i).toAlgHom)
  let σ' : ∀ i, B' i →ₐ[S] T' := fun i => eT.symm.toAlgHom.comp ((σ i).comp (eB i).toAlgHom)
  have hgB' : ∀ i (z : A i), algebraMap (A i) (B' i) z = (eBA i).symm (g i z) := fun _ _ => rfl
  have hb' : ∀ ⦃i j : Λ⦄ (h : i ≤ j) (z : B' i), eB j (b' h z) = b h (eB i z) := by
    intro i j h z
    exact AlgEquiv.apply_symm_apply _ _
  have hs' : ∀ (i : Λ) (z : B' i), eT (σ' i z) = σ i (eB i z) := by
    intro i z
    exact AlgEquiv.apply_symm_apply _ _
  have hcB' : IsDirectedColimit B' b' T' σ' := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i j k hij hjk z
      exact (eB k).injective (by rw [hb', hb', hb', hcB.map_comp])
    · intro i z
      exact (eB i).injective (by rw [hb', hcB.map_id])
    · intro i j hij z
      exact eT.injective (by rw [hs', hs', hb', hcB.comp])
    · intro z
      obtain ⟨i, y, hy⟩ := hcB.jointly_surjective (eT z)
      refine ⟨i, (eB i).symm y, eT.injective ?_⟩
      rw [hs', AlgEquiv.apply_symm_apply, hy]
    · intro i z hz
      obtain ⟨j, hij, hj⟩ := hcB.exists_eq_zero (eB i z) (by
        rw [← hs', hz, map_zero])
      exact ⟨j, hij, (eB j).injective (by rw [hb', hj, map_zero])⟩
  let : Algebra.FinitePresentation L T' :=
    Algebra.FinitePresentation.equiv eTL.symm
  let modT' : Module T' (T ⊗[S] M) := Module.compHom (T ⊗[S] M) eT.toRingHom
  have hflatT' : Module.Flat L (T' ⊗[S] M) := by
    exact flat_tensorProduct_of_algEquiv eT eTL heTL
  let : DirectedSystem B' (fun i j h => ((b' h).toRingHom : B' i →+* B' j)) :=
    ⟨hcB'.map_id, fun i j k hij hjk z => hcB'.map_comp hij hjk z⟩
  let : DirectedSystem B' (fun i j h => ((b' h).toLinearMap : B' i →ₗ[S] B' j)) :=
    ⟨hcB'.map_id, fun i j k hij hjk z => hcB'.map_comp hij hjk z⟩
  have hN := TensorProduct.exists_rep_and_eventually_zero_of_directedColimit
    (A := fun i => B' i) (fun i j h => (b' h).toLinearMap)
    (fun i => (σ' i).toLinearMap) (fun i j h z => hcB'.comp h z)
    hcB'.jointly_surjective (fun i z hz => hcB'.exists_eq_zero z hz) M
  have hgBe : ∀ i (z : A i), eB i (algebraMap (A i) (B' i) z) = g i z := by
    intro i z
    rw [hgB', ← heBA]
    exact AlgEquiv.apply_symm_apply _ _
  have hab' : ∀ i j (h : i ≤ j),
      ((b' h).toRingHom).comp (algebraMap (A i) (B' i)) =
        (algebraMap (A j) (B' j)).comp (a i j h) := by
    intro i j h
    refine RingHom.ext fun z => (eB j).injective ?_
    show eB j (b' h (algebraMap (A i) (B' i) z)) =
      eB j (algebraMap (A j) (B' j) (a i j h z))
    rw [hb', hgBe, hgBe]
    exact (RingHom.congr_fun (hg i j h) z).symm
  have hνcomp : ∀ i j (h : i ≤ j) (x : B' i ⊗[S] M),
      (σ' j).rTensorSemilinear M ((b' h).rTensorSemilinear M x) =
        (σ' i).rTensorSemilinear M x := by
    intro i j h x
    induction x with
    | tmul t m =>
      simp only [AlgHom.rTensorSemilinear_tmul]
      rw [hcB'.comp]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hρσ' : ∀ i, ((σ' i).toRingHom).comp (algebraMap (A i) (B' i)) =
      (algebraMap L T').comp (ρ i) := by
    intro i
    refine RingHom.ext fun z => eT.injective ?_
    show eT (σ' i (algebraMap (A i) (B' i) z)) = eT (algebraMap L T' (ρ i z))
    rw [hs', hgBe, ← heTL, eTL.commutes]
    exact (RingHom.congr_fun (hσg i) z).symm
  have hfpB' : ∀ i, Algebra.FinitePresentation (A i) (B' i) := by
    intro i
    have := hfp' i
    exact Algebra.FinitePresentation.equiv (eBA i).symm
  have hpush' : ∀ i j (h : i ≤ j),
      CategoryTheory.IsPushout (CommRingCat.ofHom (a i j h))
        (CommRingCat.ofHom (algebraMap (A i) (B' i)))
        (CommRingCat.ofHom (algebraMap (A j) (B' j)))
        (CommRingCat.ofHom (b' h).toRingHom) := by
    intro i j h
    let : Algebra (A i) (A j) := (a i j h).toAlgebra
    let : Algebra (B i) (B j) := (b h).toRingHom.toAlgebra
    let : Algebra (A i) (B j) := ((g j).comp (a i j h)).toAlgebra
    have hstA : IsScalarTower (A i) (A j) (B j) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    have hstB : IsScalarTower (A i) (B i) (B j) :=
      IsScalarTower.of_algebraMap_smul fun z y => by
        show b h (g i z) * y = g j (a i j h z) * y
        exact congrArg (fun t : B j => t * y)
          (by simpa using (RingHom.congr_fun (hg i j h) z).symm)
    have hP : Algebra.IsPushout (A i) (A j) (B i) (B j) := hpush i j h
    have hPs : Algebra.IsPushout (A i) (B i) (A j) (B j) := hP.symm
    let : Algebra (B' i) (B' j) := (b' h).toRingHom.toAlgebra
    let : Algebra (A i) (B' j) := ((b' h).toRingHom.comp (algebraMap (A i) (B' i))).toAlgebra
    have hstA' := IsScalarTower.of_algebraMap_eq' (hab' i j h)
    have hstB' := IsScalarTower.of_algebraMap_eq'
      (R := A i) (S := B' i) (A := B' j) rfl
    let : Algebra (A j) (B' i ⊗[A i] A j) := Algebra.TensorProduct.rightAlgebra
    let etens : (B' i ⊗[A i] A j) ≃+* B' j :=
      (Algebra.TensorProduct.congr (eBA i) AlgEquiv.refl).toRingEquiv.trans
        ((Algebra.IsPushout.equiv (A i) (B i) (A j) (B j)).toRingEquiv.trans
          (eBA j).symm.toRingEquiv)
    have hetens : ∀ (s : B' i) (x : A j),
        etens (s ⊗ₜ[A i] x) =
          (eBA j).symm (algebraMap (B i) (B j) (eBA i s) * algebraMap (A j) (B j) x) := by
      intro s x
      show (eBA j).symm ((Algebra.IsPushout.equiv (A i) (B i) (A j) (B j))
        ((Algebra.TensorProduct.congr (eBA i) AlgEquiv.refl) (s ⊗ₜ[A i] x))) = _
      rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
        Algebra.IsPushout.equiv_tmul]
      rfl
    let e : (B' i ⊗[A i] A j) ≃ₐ[A j] B' j :=
      AlgEquiv.ofRingEquiv (f := etens) (by
        intro x
        show etens ((1 : B' i) ⊗ₜ[A i] x) = algebraMap (A j) (B' j) x
        rw [hetens]
        simp only [map_one, one_mul]
        exact (eBA j).symm.commutes x)
    have hPB' : Algebra.IsPushout (A i) (A j) (B' i) (B' j) := by
      refine Algebra.IsPushout.of_equiv (R := A i) (R' := A j) (S := B' i)
        (S' := B' i ⊗[A i] A j) e ?_
      refine RingHom.ext fun s => ?_
      show etens (s ⊗ₜ[A i] (1 : A j)) = b' h s
      rw [hetens]
      simp only [map_one, mul_one]
      rfl
    exact CommRingCat.isPushout_iff_isPushout.mpr hPB'
  have hbc' : ∀ i j (h : i ≤ j),
      let : Algebra (B' i) (B' j) := (b' h).toRingHom.toAlgebra
      let : Module (B' i) (B' j ⊗[S] M) := Module.compHom (B' j ⊗[S] M) (b' h).toRingHom
      have : IsScalarTower (B' i) (B' j) (B' j ⊗[S] M) :=
        IsScalarTower.of_algebraMap_smul fun _ _ => rfl
      IsBaseChange (B' j)
        (⟨((b' h).rTensorSemilinear M).toAddHom,
          fun z y => ((b' h).rTensorSemilinear M).map_smul' z y⟩ :
            B' i ⊗[S] M →ₗ[B' i] B' j ⊗[S] M) :=
    fun i j h => AlgHom.isBaseChange_rTensorSemilinear (b' h) M
  let : DirectedSystem (fun i => B' i ⊗[S] M)
      (fun i j h => ((b' h).rTensorSemilinear M : B' i ⊗[S] M → B' j ⊗[S] M)) := by
    refine ⟨?_, ?_⟩
    · intro i x
      induction x with
      | tmul t m =>
        simp only [AlgHom.rTensorSemilinear_tmul]
        rw [hcB'.map_id]
      | add x y hx hy => simp only [map_add, hx, hy]
    · intro i j k hij hjk x
      induction x with
      | tmul t m =>
        simp only [AlgHom.rTensorSemilinear_tmul]
        rw [hcB'.map_comp]
      | add x y hx hy => simp only [map_add, hx, hy]
  obtain ⟨i₀, hi₀⟩ := Module.Flat.eventually_flat_of_directed
    (R := L) (S := T') (M := T' ⊗[S] M) (A := A) (B := B')
    (N := fun i => B' i ⊗[S] M)
    (fun i j h => a i j h) (fun i j h => (b' h).toRingHom)
    (fun i j h => (b' h).rTensorSemilinear M)
    hab' (fun i => ρ i) (fun i => (σ' i).toRingHom)
    (fun i => (σ' i).rTensorSemilinear M)
    (fun i j h x => congrFun (hρ i j h) x)
    (fun i j h x => hcB'.comp h x) hνcomp hρσ' hρsurj hρzero
    hcB'.jointly_surjective (fun i x hx => hcB'.exists_eq_zero x hx)
    hN.1 hN.2 hpush' hbc' hfpB' (fun i => inferInstance)
  refine ⟨i₀, fun j hj => ?_⟩
  have hflatj : Module.Flat (A j) (B' j ⊗[S] M) := by
    convert! hi₀ j hj using 1
    exact compHom_algebraMap_eq.symm
  have hres : Module.Flat (A j) (B j ⊗[S] M) :=
    flat_tensorProduct_of_algEquiv (eB j).symm (eBA j).symm fun _ => rfl
  rw [show Module.compHom (B j ⊗[S] M) (g j) = _ from compHom_algebraMap_eq]
  exact hres

set_option backward.isDefEq.respectTransparency false in
/-- Flatness of a compatible principal localization of a finitely presented base-change module
holds at every sufficiently large stage. -/
theorem Module.Flat.eventually_flat_localizationAway_tensorProduct
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S]
    (M : Type*) [AddCommGroup M] [Module S M] [Module.FinitePresentation S M]
    {Λ : Type*} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    {A : Λ → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    {f : ∀ ⦃i j⦄, i ≤ j → A i →ₐ[R] A j}
    {L : Type*} [CommRing L] [Algebra R L] {ρ : ∀ i, A i →ₐ[R] L}
    (hc : IsDirectedColimit A f L ρ)
    (z : ∀ i, S ⊗[R] A i) (y : S ⊗[R] L)
    (hz : ∀ ⦃i j⦄ (h : i ≤ j),
      Algebra.TensorProduct.map (AlgHom.id S S) (f h) (z i) = z j)
    (hy : ∀ i, Algebra.TensorProduct.map (AlgHom.id S S) (ρ i) (z i) = y)
    (hflat : letI : Algebra L (S ⊗[R] L) := Algebra.TensorProduct.rightAlgebra
      Module.Flat L (LocalizedModule.Away y ((S ⊗[R] L) ⊗[S] M))) :
    ∃ i, ∀ j, i ≤ j →
      letI : Algebra (A j) (S ⊗[R] A j) := Algebra.TensorProduct.rightAlgebra
      Module.Flat (A j) (LocalizedModule.Away (z j) ((S ⊗[R] A j) ⊗[S] M)) := by
  let : ∀ i, Algebra (A i) (S ⊗[R] A i) := fun _ => Algebra.TensorProduct.rightAlgebra
  let : Algebra L (S ⊗[R] L) := Algebra.TensorProduct.rightAlgebra
  let b : ∀ ⦃i j⦄, i ≤ j → (S ⊗[R] A i) →ₐ[S] (S ⊗[R] A j) :=
    fun {_ _} h => Algebra.TensorProduct.map (AlgHom.id S S) (f h)
  let σ : ∀ i, (S ⊗[R] A i) →ₐ[S] (S ⊗[R] L) :=
    fun i => Algebra.TensorProduct.map (AlgHom.id S S) (ρ i)
  have ht := IsDirectedColimit.tensorLeft hc S
  have hcS : IsDirectedColimit (fun i => S ⊗[R] A i) b (S ⊗[R] L) σ :=
    ⟨ht.map_comp, ht.map_id, ht.comp, ht.jointly_surjective, ht.exists_eq_zero⟩
  have hcLoc := IsDirectedColimit.localizationAway hcS z y hz hy
  let g : ∀ i, A i →+* Localization.Away (z i) :=
    fun i => (algebraMap (S ⊗[R] A i) (Localization.Away (z i))).comp
      (Algebra.TensorProduct.includeRight : A i →ₐ[R] S ⊗[R] A i).toRingHom
  have hg : ∀ i j (h : i ≤ j), (g j).comp (f h).toRingHom =
      ((b h).localizationAwayMap _ _ (hz h)).toRingHom.comp (g i) := by
    intro i j h
    ext a
    simp only [g, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.localizationAwayMap_algebraMap]
    rfl
  let : DirectedSystem A (fun i j h => (f h).toRingHom) :=
    ⟨hc.map_id, fun i j k hij hjk a => hc.map_comp hij hjk a⟩
  have : Algebra.FinitePresentation L (S ⊗[R] L) :=
    Algebra.FinitePresentation.tensorProduct_right
  have : Algebra.FinitePresentation L (Localization.Away y) :=
    Algebra.FinitePresentation.trans L (S ⊗[R] L) _
  have : Module.Flat L (Localization.Away y ⊗[S] M) :=
    (Module.flat_localizedModule_away_tensor_iff M y).mp hflat
  have hfp : ∀ i, let : Algebra (A i) (Localization.Away (z i)) := (g i).toAlgebra
      Algebra.FinitePresentation (A i) (Localization.Away (z i)) := by
    intro i
    have : Algebra.FinitePresentation (A i) (S ⊗[R] A i) :=
      Algebra.FinitePresentation.tensorProduct_right
    have ha : (g i).toAlgebra = (inferInstance : Algebra (A i) (Localization.Away (z i))) :=
      Algebra.algebra_ext _ _ fun _ => rfl
    show @Algebra.FinitePresentation (A i) (Localization.Away (z i)) _ _ (g i).toAlgebra
    rw [ha]
    exact Algebra.FinitePresentation.trans (A i) (S ⊗[R] A i) _
  have hσg : ∀ i, (algebraMap L (Localization.Away y)).comp (ρ i).toRingHom =
      ((σ i).localizationAwayMap _ _ (hy i)).toRingHom.comp (g i) := by
    intro i
    ext a
    simp only [g, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.localizationAwayMap_algebraMap]
    rfl
  obtain ⟨i, hi⟩ := Module.Flat.eventually_flat_tensorProduct_of_isDirectedColimit M A
    (fun i j h => (f h).toRingHom) (fun i => (ρ i).toRingHom) hcLoc g hg
    (fun i j h => funext (hc.comp h)) hc.jointly_surjective
    (fun i a ha => hc.exists_eq_zero a ha) hσg hfp (by
    intro i j h
    let : Algebra (A i) (A j) := (f h).toRingHom.toAlgebra
    let : Algebra (A i) (S ⊗[R] A j) :=
      (Algebra.TensorProduct.includeRight.comp (f h)).toRingHom.toAlgebra
    let : Algebra (S ⊗[R] A i) (S ⊗[R] A j) := (b h).toRingHom.toAlgebra
    have : IsScalarTower (A i) (A j) (S ⊗[R] A j) :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    have : IsScalarTower (A i) (S ⊗[R] A i) (S ⊗[R] A j) :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    have : Algebra.IsPushout (A i) (A j) (S ⊗[R] A i) (S ⊗[R] A j) :=
      Algebra.IsPushout.tensorProduct_map (f h)
    convert! Algebra.IsPushout.localizationAway_of_algebraMap_eq
      (R := A i) (S := A j) (z i) (z j) (hz h) using 1 <;>
      apply Algebra.algebra_ext <;> intro a <;> rfl)
  refine ⟨i, fun j hj => (Module.flat_localizedModule_away_tensor_iff M (z j)).mpr ?_⟩
  convert! hi j hj using 1
  exact compHom_algebraMap_eq.symm

set_option backward.isDefEq.respectTransparency false in
/-- A principal localization defined at one stage which is flat at the colimit is flat at every
sufficiently large stage. -/
theorem Module.Flat.exists_ge_flat_localizationAway_tensorProduct
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S]
    (M : Type*) [AddCommGroup M] [Module S M] [Module.FinitePresentation S M]
    {Λ : Type*} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    {A : Λ → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    {f : ∀ ⦃i j⦄, i ≤ j → A i →ₐ[R] A j}
    {L : Type*} [CommRing L] [Algebra R L] {ρ : ∀ i, A i →ₐ[R] L}
    (hc : IsDirectedColimit A f L ρ) (i : Λ) (g : S ⊗[R] A i)
    (hflat : letI : Algebra L (S ⊗[R] L) := Algebra.TensorProduct.rightAlgebra
      Module.Flat L (LocalizedModule.Away
        (Algebra.TensorProduct.map (AlgHom.id S S) (ρ i) g) ((S ⊗[R] L) ⊗[S] M))) :
    ∃ j, ∃ hij : i ≤ j, ∀ k (hjk : j ≤ k),
      letI : Algebra (A k) (S ⊗[R] A k) := Algebra.TensorProduct.rightAlgebra
      Module.Flat (A k) (LocalizedModule.Away
        (Algebra.TensorProduct.map (AlgHom.id S S) (f (hij.trans hjk)) g)
        ((S ⊗[R] A k) ⊗[S] M)) := by
  let : Nonempty (Set.Ici i) := ⟨⟨i, le_rfl⟩⟩
  let : IsDirected (Set.Ici i) (· ≤ ·) := ⟨fun j k => by
    obtain ⟨l, hjl, hkl⟩ := directed_of (· ≤ ·) j.1 k.1
    exact ⟨⟨l, j.2.trans hjl⟩, hjl, hkl⟩⟩
  have ht := IsDirectedColimit.tensorLeft hc S
  obtain ⟨j, hj⟩ := Module.Flat.eventually_flat_localizationAway_tensorProduct M
    (hc.restrict_Ici i)
    (fun j => Algebra.TensorProduct.map (AlgHom.id S S) (f j.2) g)
    (Algebra.TensorProduct.map (AlgHom.id S S) (ρ i) g)
    (fun j k h => ht.map_comp j.2 h g) (fun j => ht.comp j.2 g) hflat
  exact ⟨j.1, j.2, fun k hk => hj ⟨k, j.2.trans hk⟩ hk⟩

/-! ### Descent of flatness along a closed subset to a stage of a directed colimit -/

/-- A finite principal-open cover converts away-flatness into flatness along the closed
subset. -/
private theorem flatAlongZeroLocus_of_away_cover
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (M : Type w) [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] (I : Ideal R) (G : Finset S)
    (hcover : I.map (algebraMap R S) + Ideal.span (G : Set S) = ⊤)
    (hflat : ∀ g ∈ G, Module.Flat R (LocalizedModule.Away g M)) :
    Module.FlatAlongZeroLocus R S I M := by
  classical
  intro q hq hIq
  have hGq : ∃ g ∈ G, g ∉ q := by
    by_contra h
    push Not at h
    have hspan : Ideal.span (G : Set S) ≤ q := Ideal.span_le.mpr fun g hg => h g hg
    have htop : (⊤ : Ideal S) ≤ q := by
      rw [← hcover]
      exact add_le hIq hspan
    exact Ideal.IsPrime.ne_top hq (top_le_iff.mp htop)
  obtain ⟨g, hgG, hgq⟩ := hGq
  have := hflat g hgG
  exact Module.Flat.localizedModule_atPrime_of_away q g hgq

/-- An open relative flat locus containing a closed subset admits a finite away-flat cover. -/
private theorem exists_away_cover_of_isOpen
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (M : Type w) [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] (J : Ideal S)
    (hopen : IsOpen {q : PrimeSpectrum S |
      Module.Flat R (LocalizedModule.AtPrime q.asIdeal M)})
    (hflat : ∀ q : PrimeSpectrum S, J ≤ q.asIdeal →
      Module.Flat R (LocalizedModule.AtPrime q.asIdeal M)) :
    ∃ G : Finset S, J + Ideal.span (G : Set S) = ⊤ ∧
      ∀ g ∈ G, Module.Flat R (LocalizedModule.Away g M) := by
  classical
  let V : Set (PrimeSpectrum S) := PrimeSpectrum.zeroLocus J
  have hVcompact : IsCompact V :=
    (PrimeSpectrum.isClosed_zeroLocus (J : Set S)).isCompact
  have hVsub : V ⊆ {q : PrimeSpectrum S |
      Module.Flat R (LocalizedModule.AtPrime q.asIdeal M)} :=
    fun q hq => hflat q ((PrimeSpectrum.mem_zeroLocus q J).mp hq)
  have hlocal : ∀ q : V, ∃ g : S,
      q.1 ∈ PrimeSpectrum.basicOpen g ∧
      (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) ⊆
        {p : PrimeSpectrum S | Module.Flat R (LocalizedModule.AtPrime p.asIdeal M)} := by
    intro q
    obtain ⟨_, ⟨g, rfl⟩, hqg, hgsub⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp hopen q.1 (hVsub q.2)
    exact ⟨g, hqg, hgsub⟩
  choose g hgmem hgsub using hlocal
  obtain ⟨T, hT⟩ := hVcompact.elim_finite_subcover
    (fun q : V => (PrimeSpectrum.basicOpen (g q) : Set (PrimeSpectrum S)))
    (fun q => PrimeSpectrum.isOpen_basicOpen)
    (fun q hq => Set.mem_iUnion.mpr ⟨⟨q, hq⟩, hgmem ⟨q, hq⟩⟩)
  let G : Finset S := T.image g
  refine ⟨G, ?_, ?_⟩
  · apply (PrimeSpectrum.zeroLocus_empty_iff_eq_top).mp
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro q hq
    have hqsum : J + Ideal.span (G : Set S) ≤ q.asIdeal :=
      (PrimeSpectrum.mem_zeroLocus q (J + Ideal.span (G : Set S))).mp hq
    rw [Ideal.add_eq_sup] at hqsum
    obtain ⟨i, hiT, hqi⟩ := Set.mem_iUnion₂.mp (hT ((PrimeSpectrum.mem_zeroLocus q J).mpr
      (show J ≤ q.asIdeal from le_sup_left.trans hqsum)))
    exact hqi (le_sup_right.trans hqsum (Ideal.subset_span (Finset.mem_image.mpr ⟨i, hiT, rfl⟩)))
  · intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact Stacks.Flatness.OpenFlatLocus.flat_localizedModule_away_of_forall_flat_atPrime (g i)
      (fun p hp => hgsub i hp)

/-- A finitely presented module over a finitely presented algebra admits a finite flat
principal-open cover of every closed subset along which it is flat. -/
private theorem exists_away_cover_of_finitePresentation
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S]
    (M : Type w) [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] [Module.FinitePresentation S M]
    (I : Ideal R) (hflat : Module.FlatAlongZeroLocus R S I M) :
    ∃ G : Finset S,
      I.map (algebraMap R S) + Ideal.span (G : Set S) = ⊤ ∧
      ∀ g ∈ G, Module.Flat R (LocalizedModule.Away g M) :=
  exists_away_cover_of_isOpen R S M (I.map (algebraMap R S))
    Module.isOpen_setOf_flat_localizedModule_atPrime fun q hq => hflat q.asIdeal hq

open CategoryTheory Limits

/-- The underlying type of the colimit of commutative algebras is the colimit of the underlying
types. -/
private theorem commAlgCat_colimit_nonempty_isColimit
    (R : Type u) [CommRing R] (Λ : Type u) [Preorder Λ] [Nonempty Λ]
    [IsDirected Λ (· ≤ ·)] (A : Λ ⥤ CommAlgCat.{u} R) :
    Nonempty (IsColimit ((forget CommRingCat).mapCocone ((Under.forget (CommRingCat.of R)).mapCocone
      ((commAlgCatEquivUnder (CommRingCat.of R)).functor.mapCocone (colimit.cocone A))))) :=
  ⟨isColimitOfPreserves (forget CommRingCat) <| isColimitOfPreserves (Under.forget _) <|
    isColimitOfPreserves _ (colimit.isColimit A)⟩

/-- Every element of a filtered colimit of commutative algebras comes from a stage. -/
private theorem commAlgCat_colimit_exists_rep
    (R : Type u) [CommRing R] (Λ : Type u) [Preorder Λ] [Nonempty Λ]
    [IsDirected Λ (· ≤ ·)] (A : Λ ⥤ CommAlgCat.{u} R)
    (z : (colimit A : CommAlgCat.{u} R)) :
    ∃ i : Λ, ∃ y : A.obj i, (colimit.ι A i) y = z := by
  obtain ⟨h⟩ := commAlgCat_colimit_nonempty_isColimit R Λ A
  exact Types.jointly_surjective_of_isColimit h z

/-- Equality of two stage representatives holds at a common later stage. -/
private theorem commAlgCat_colimit_eq_iff_later
    (R : Type u) [CommRing R] (Λ : Type u) [Preorder Λ] [Nonempty Λ]
    [IsDirected Λ (· ≤ ·)] (A : Λ ⥤ CommAlgCat.{u} R)
    {i j : Λ} (z : A.obj i) (y : A.obj j)
    (h : (colimit.ι A i) z = (colimit.ι A j) y) :
    ∃ k : Λ, ∃ (hik : i ≤ k) (hjk : j ≤ k),
      A.map (homOfLE hik) z = A.map (homOfLE hjk) y := by
  obtain ⟨h₃⟩ := commAlgCat_colimit_nonempty_isColimit R Λ A
  obtain ⟨k, f, g, heq⟩ := (Types.FilteredColimit.isColimit_eq_iff _ h₃).mp h
  exact ⟨k, leOfHom f, leOfHom g, heq⟩

/-- The categorical colimit carries the elementwise universal property of a directed colimit. -/
private theorem isDirectedColimit_commAlgCat_colimit
    (R : Type u) [CommRing R] (Λ : Type u) [Preorder Λ] [Nonempty Λ]
    [IsDirected Λ (· ≤ ·)] (A : Λ ⥤ CommAlgCat.{u} R) :
    IsDirectedColimit (fun i => A.obj i)
      (fun {_ _} h => (A.map (homOfLE h)).hom)
      (colimit A : CommAlgCat.{u} R) (fun i => (colimit.ι A i).hom) := by
  refine ⟨?_, ?_, ?_, commAlgCat_colimit_exists_rep R Λ A, ?_⟩
  · intro i j k hij hjk z
    exact (ConcreteCategory.congr_hom (A.map_comp (homOfLE hij) (homOfLE hjk)) z).symm
  · intro i z
    exact ConcreteCategory.congr_hom (A.map_id i) z
  · intro i j hij z
    exact ConcreteCategory.congr_hom (colimit.w A (homOfLE hij)) z
  · intro i z hz
    obtain ⟨j, hij, _, hj⟩ := commAlgCat_colimit_eq_iff_later R Λ A z (0 : A.obj i)
      (by simpa using hz)
    exact ⟨j, hij, by simpa using hj⟩

/-- Mapping to a later stage and then into the colimit is mapping into the colimit. -/
private theorem map_colimit_ι_map
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (Λ : Type u) [Preorder Λ] (A : Λ ⥤ CommAlgCat.{u} R) {i k : Λ} (h : i ≤ k)
    (w : S ⊗[R] A.obj i) :
    Algebra.TensorProduct.map (AlgHom.id R S) (colimit.ι A k).hom
      (Algebra.TensorProduct.map (AlgHom.id R S) (A.map (homOfLE h)).hom w) =
      Algebra.TensorProduct.map (AlgHom.id R S) (colimit.ι A i).hom w := by
  rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_id_comp]
  congr 2
  exact AlgHom.ext fun w => ConcreteCategory.congr_hom (colimit.w A (homOfLE h)) w

/-- An element of a tensor product with the colimit comes from one tensor product with a
stage. -/
private theorem tensorProduct_commAlgCat_colimit_exists_rep
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (Λ : Type u) [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    (A : Λ ⥤ CommAlgCat.{u} R) (z : S ⊗[R] (colimit A : CommAlgCat.{u} R)) :
    ∃ i : Λ, ∃ y : S ⊗[R] A.obj i,
      (Algebra.TensorProduct.map (AlgHom.id R S) (colimit.ι A i).hom) y = z := by
  induction z using TensorProduct.inductionOn with
  | tmul s c =>
    obtain ⟨i, t, ht⟩ := commAlgCat_colimit_exists_rep R Λ A c
    exact ⟨i, s ⊗ₜ[R] t, by simp [ht]⟩
  | add z y hz hy =>
    obtain ⟨i, c, hc⟩ := hz
    obtain ⟨j, t, ht⟩ := hy
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
    refine ⟨k, Algebra.TensorProduct.map (AlgHom.id R S) (A.map (homOfLE hik)).hom c +
      Algebra.TensorProduct.map (AlgHom.id R S) (A.map (homOfLE hjk)).hom t, ?_⟩
    rw [map_add, map_colimit_ι_map R S Λ A hik, map_colimit_ι_map R S Λ A hjk, hc, ht]

/-- A finite family of elements of the colimit tensor product lifts to one stage. -/
private theorem tensorProduct_commAlgCat_colimit_finset_exists_rep
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (Λ : Type u) [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    (A : Λ ⥤ CommAlgCat.{u} R)
    (F : Finset (S ⊗[R] (colimit A : CommAlgCat.{u} R))) :
    ∃ k : Λ, ∃ y : F → S ⊗[R] A.obj k,
      ∀ z : F,
        (Algebra.TensorProduct.map (AlgHom.id R S) (colimit.ι A k).hom) (y z) = z.1 := by
  classical
  have hrep : ∀ z : F, ∃ i : Λ, ∃ y : S ⊗[R] A.obj i,
      (Algebra.TensorProduct.map (AlgHom.id R S) (colimit.ι A i).hom) y = z.1 :=
    fun z => tensorProduct_commAlgCat_colimit_exists_rep R S Λ A z.1
  choose i y hy using hrep
  obtain ⟨k, hk⟩ := (Finset.univ.image i).exists_le
  have hk' : ∀ z, i z ≤ k := fun z => hk _ (Finset.mem_image_of_mem i (Finset.mem_univ z))
  refine ⟨k, fun z => Algebra.TensorProduct.map (AlgHom.id R S)
    (A.map (homOfLE (hk' z))).hom (y z), fun z => ?_⟩
  rw [map_colimit_ι_map R S Λ A (hk' z), hy z]

set_option backward.isDefEq.respectTransparency false in
/-- Flatness of a finitely presented module along the closed subset defined
by a compatible family of ideals in a directed system descends from the colimit to one stage. -/
@[stacks 05LM]
theorem Module.exists_flatAlongZeroLocus_baseChange_of_colimit
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S]
    (M : Type w) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.FinitePresentation S M]
    (Λ : Type u) [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    (A : Λ ⥤ CommAlgCat.{u} R) (I : ∀ i, Ideal (A.obj i))
    (hI : ∀ {i j : Λ} (hij : i ≤ j),
      Ideal.map (A.map (homOfLE hij)).hom.toRingHom (I i) ≤ I j)
    (hflat :
      let R' := (colimit A : CommAlgCat.{u} R)
      let S' := S ⊗[R] R'
      letI : Algebra R' S' := Algebra.TensorProduct.rightAlgebra
      Module.FlatAlongZeroLocus
        R' S'
        (⨆ i, Ideal.map (colimit.ι A i).hom.toRingHom (I i))
        (S' ⊗[S] M)) :
    ∃ i : Λ,
      let Sᵢ := S ⊗[R] (A.obj i)
      letI : Algebra (A.obj i) Sᵢ := Algebra.TensorProduct.rightAlgebra
      Module.FlatAlongZeroLocus
        (A.obj i) Sᵢ (I i) (Sᵢ ⊗[S] M) := by
  classical
  let L := (colimit A : CommAlgCat.{u} R)
  let : Algebra L (S ⊗[R] L) := Algebra.TensorProduct.rightAlgebra
  let : ∀ i, Algebra (A.obj i) (S ⊗[R] A.obj i) :=
    fun _ => Algebra.TensorProduct.rightAlgebra
  have : Algebra.FinitePresentation L (S ⊗[R] L) :=
    Algebra.FinitePresentation.tensorProduct_right
  obtain ⟨G, hcover, hGflat⟩ := exists_away_cover_of_finitePresentation
    L (S ⊗[R] L) ((S ⊗[R] L) ⊗[S] M)
    (⨆ i, Ideal.map (colimit.ι A i).hom.toRingHom (I i)) hflat
  obtain ⟨i₀, y, hy⟩ := tensorProduct_commAlgCat_colimit_finset_exists_rep R S Λ A G
  have hc := isDirectedColimit_commAlgCat_colimit R Λ A
  have ht := IsDirectedColimit.tensorLeft hc S
  let b : ∀ ⦃i j : Λ⦄, i ≤ j → (S ⊗[R] A.obj i) →ₐ[R] (S ⊗[R] A.obj j) :=
    fun {_ _} h => Algebra.TensorProduct.map (AlgHom.id R S) (A.map (homOfLE h)).hom
  let σ : ∀ i, (S ⊗[R] A.obj i) →ₐ[R] (S ⊗[R] L) :=
    fun i => Algebra.TensorProduct.map (AlgHom.id R S) (colimit.ι A i).hom
  let J : ∀ i, Ideal (S ⊗[R] A.obj i) :=
    fun i => Ideal.map
      (Algebra.TensorProduct.includeRight : A.obj i →ₐ[R] S ⊗[R] A.obj i).toRingHom (I i)
  have hJ : ∀ ⦃i j⦄ (h : i ≤ j), Ideal.map (b h).toRingHom (J i) ≤ J j :=
    fun _ _ h => Ideal.map_includeRight_le_of_map_le (A.map (homOfLE h)).hom (I _) (I _) (hI h)
  let K : Ideal (S ⊗[R] A.obj i₀) := Ideal.span (Set.range y)
  have hspan : Ideal.map (σ i₀).toRingHom K = Ideal.span (G : Set (S ⊗[R] L)) := by
    show Ideal.map (σ i₀).toRingHom (Ideal.span (Set.range y)) = _
    rw [Ideal.map_span]
    congr 1
    ext t
    constructor
    · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
      show σ i₀ (y c) ∈ (G : Set (S ⊗[R] L))
      rw [show σ i₀ (y c) = c.1 from hy c]
      exact c.2
    · intro ht
      exact ⟨y ⟨t, ht⟩, ⟨⟨t, ht⟩, rfl⟩, hy ⟨t, ht⟩⟩
  have hcover' : (⨆ i, Ideal.map (σ i).toRingHom (J i)) ⊔
      Ideal.map (σ i₀).toRingHom K = ⊤ := by
    rw [hspan, ← Ideal.map_includeRight_iSup_map (fun i => (colimit.ι A i).hom) I]
    exact hcover
  obtain ⟨j, hij, hjcover⟩ := Ideal.exists_ge_sup_map_eq_top ht J hJ i₀ K hcover'
  have hdesc : ∀ c : G, ∃ k, ∃ hik : i₀ ≤ k, ∀ l (hkl : k ≤ l),
      Module.Flat (A.obj l) (LocalizedModule.Away (b (hik.trans hkl) (y c))
        ((S ⊗[R] A.obj l) ⊗[S] M)) := by
    intro c
    apply Module.Flat.exists_ge_flat_localizationAway_tensorProduct M hc i₀ (y c)
    show Module.Flat L (LocalizedModule.Away (σ i₀ (y c)) ((S ⊗[R] L) ⊗[S] M))
    rw [show σ i₀ (y c) = c.1 from hy c]
    exact hGflat c.1 c.2
  choose k hik hk using hdesc
  obtain ⟨l, hl⟩ := (insert j (Finset.univ.image k)).exists_le
  have hjl : j ≤ l := hl j (Finset.mem_insert_self _ _)
  have hi₀l : i₀ ≤ l := hij.trans hjl
  let F : Finset (S ⊗[R] A.obj l) := Finset.univ.image (fun c : G => b hi₀l (y c))
  refine ⟨l, flatAlongZeroLocus_of_away_cover (A.obj l) (S ⊗[R] A.obj l)
    ((S ⊗[R] A.obj l) ⊗[S] M) (I l) F ?_ ?_⟩
  · have hm := congrArg (Ideal.map (b hjl).toRingHom) hjcover
    rw [Ideal.map_sup, Ideal.map_top] at hm
    have hb : (b hjl).toRingHom.comp (b hij).toRingHom = (b hi₀l).toRingHom :=
      RingHom.ext (ht.map_comp hij hjl)
    have hmapK : Ideal.map (b hjl).toRingHom (Ideal.map (b hij).toRingHom K) =
        Ideal.map (b hi₀l).toRingHom K := by rw [Ideal.map_map, hb]
    rw [hmapK] at hm
    change Ideal.map (b hjl).toRingHom (J j) ⊔
      Ideal.map (b hi₀l).toRingHom (Ideal.span (Set.range y)) = ⊤ at hm
    rw [Ideal.map_span, ← Set.range_comp'] at hm
    have hle : Ideal.map (b hjl).toRingHom (J j) ⊔
        Ideal.span (Set.range (fun c : G => b hi₀l (y c))) ≤
        J l ⊔ Ideal.span (Set.range (fun c : G => b hi₀l (y c))) :=
      sup_le_sup (hJ hjl) le_rfl
    have htop : J l ⊔ Ideal.span (Set.range (fun c : G => b hi₀l (y c))) = ⊤ :=
      top_unique (hm ▸ hle)
    have hright : algebraMap (A.obj l) (S ⊗[R] A.obj l) =
        (Algebra.TensorProduct.includeRight :
          A.obj l →ₐ[R] S ⊗[R] A.obj l).toRingHom := rfl
    simpa only [F, J, hright, Ideal.add_eq_sup, Finset.coe_image, Finset.coe_univ,
      Set.image_univ] using htop
  · intro g hg
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hg
    exact hk c l (hl (k c)
      (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨c, Finset.mem_univ c, rfl⟩)))
