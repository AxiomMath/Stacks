module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Support.KoszulDeformation
public import StacksFrontier.Homology.Perfect.Basic
public import StacksFrontier.Homology.Perfect.Lifting
public import StacksFrontier.RingTheory.Koszul.Relations

/-!
# A finite free lift of a fibrewise Koszul complex

A perfect complex over a flat local deformation situation whose closed fibre is the Koszul
complex of a regular sequence has a finite free representative with the same term ranks, and the
first differential of that representative exhibits a lift of the regular sequence.

## Main results

* `AlgebraicGeometry.exists_finiteFree_lift_of_fibrewise_koszul` supplies the finite free
  complex, its identification in the derived category, the isomorphism with the Koszul complex
  after reduction, and the lifted sequence.

## Implementation notes

The degree `-n` term has rank `r.choose n` and the positive degrees vanish, matching the ranks
of the Koszul complex on `r` elements. The lifted elements are read off as the components of the
differential from degree `-1` to degree `0` in chosen free bases, which is why free bases rather
than abstract projective modules are produced.

The reduction is an isomorphism of complexes, not merely a derived isomorphism: that is what
lets the lifted sequence be recognised componentwise.

## References

* [Stacks Project, Tag 0G0N](https://stacks.math.columbia.edu/tag/0G0N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

private theorem exteriorPower_finiteFree {R : Type u} [CommRing R] (r n : ℕ) :
    Module.Finite R (⋀[R]^n (Fin r → R)) ∧ Module.Free R (⋀[R]^n (Fin r → R)) :=
  ⟨inferInstance, Module.Free.of_basis ((Pi.basisFun R (Fin r)).exteriorPower n)⟩

private noncomputable def scalar_finOneEquiv {R : Type u} [CommRing R] :
    R ≃ₗ[R] (Fin 1 → R) where
  toFun x := fun _ => x
  invFun f := f 0
  left_inv _ := rfl
  right_inv := by intro f; funext i; fin_cases i; rfl
  map_add' := by intros; ext i; simp
  map_smul' := by intros; ext i; simp

private noncomputable def exteriorPower_finIso {R : Type u} [CommRing R] (r n : ℕ) :
    ModuleCat.of R (⋀[R]^n (Fin r → R)) ≅
      ModuleCat.of R (Fin (r.choose n) → R) := by
  classical
  by_cases hn0 : n = 0
  · subst n
    let eFin : Fin (r.choose 0) ≃ Fin 1 := Equiv.cast (congrArg Fin (Nat.choose_zero_right r))
    exact ((exteriorPower.zeroEquiv R (Fin r → R)).trans
      (scalar_finOneEquiv (R := R))).trans
        (LinearEquiv.piCongrLeft' R (fun _ : Fin 1 => R) eFin.symm) |>.toModuleIso
  · by_cases hn1 : n = 1
    · subst n
      let eFin : Fin r ≃ Fin (r.choose 1) := Equiv.cast (congrArg Fin (Nat.choose_one_right r).symm)
      exact ((exteriorPower.oneEquiv R (Fin r → R)).trans
        (Pi.basisFun R (Fin r)).equivFun).trans
          (LinearEquiv.piCongrLeft' R (fun _ : Fin r => R) eFin) |>.toModuleIso
    · let b := (Pi.basisFun R (Fin r)).exteriorPower n
      have hc : Fintype.card (Set.powersetCard (Fin r) n) = r.choose n := by
        rw [← Nat.card_eq_fintype_card, Set.powersetCard.card, Nat.card_fin]
      exact (b.reindex (Fintype.equivFinOfCardEq hc)).equivFun.toModuleIso

private theorem exists_lift_linearEquiv_quotient
    {A : Type u} [CommRing A] (I : Ideal A)
    (hI : ∀ x ∈ I, IsUnit (1 + x))
    {P F : Type u} [AddCommGroup P] [Module A P] [Module.Finite A P]
      [Module.Projective A P]
      [AddCommGroup F] [Module A F] [Module.Finite A F] [Module.Projective A F]
    (e : (P ⧸ (I • (⊤ : Submodule A P))) ≃ₗ[A]
      (F ⧸ (I • (⊤ : Submodule A F)))) :
    ∃ eLift : P ≃ₗ[A] F, inducedQuot I eLift.toLinearMap = e := by
  obtain ⟨φ, hφ⟩ := Module.projective_lifting_property
    (Submodule.mkQ (I • (⊤ : Submodule A F)))
    (e.toLinearMap.comp (Submodule.mkQ (I • (⊤ : Submodule A P))))
    (Submodule.mkQ_surjective _)
  have hquot : inducedQuot I φ = e := by
    refine LinearMap.ext fun (x : P ⧸ (I • (⊤ : Submodule A P))) => ?_
    obtain ⟨p, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule A P)) x
    show Submodule.mkQ (I • (⊤ : Submodule A F)) (φ p) =
      e (Submodule.mkQ (I • (⊤ : Submodule A P)) p)
    simpa using LinearMap.congr_fun hφ p
  have hbij : Function.Bijective (inducedQuot I φ) := hquot ▸ e.bijective
  exact ⟨LinearEquiv.ofBijective φ (lift_iso_of_quot_iso I hI φ hbij), hquot⟩

/-- A perfect deformation of a fibrewise Koszul complex has a finite free complex
representative of the Koszul ranks. Its first differential, written in free bases,
gives a sequence lifting the original one. -/
public theorem exists_finiteFree_lift_of_fibrewise_koszul
    (S : FlatLocalKoszulDeformationSituation.{u}) :
    letI : CommRing S.A := S.commRingA
    let I := Ideal.map (algebraMap S.R S.A) (IsLocalRing.maximalIdeal S.R)
    ∃ (P : CochainComplex (ModuleCat.{u} S.A) ℤ)
      (f : Fin S.r → S.A),
      Nonempty (DerivedCategory.Q.obj P ≅ S.K) ∧
      Nonempty
        (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P ≅
          (Koszul.seqComplex S.residueSequence).extend ComplexShape.embeddingDownNat) ∧
      (∀ n : ℕ,
        Nonempty (P.X (-(n : ℤ)) ≅
          ModuleCat.of S.A (Fin (S.r.choose n) → S.A))) ∧
      (∀ i : ℤ, 0 < i → IsZero (P.X i)) ∧
      ∃ (e₀ : P.X 0 ≅ ModuleCat.of S.A S.A)
        (e₁ : P.X (-1) ≅ ModuleCat.of S.A (Fin S.r → S.A)),
        (∀ i, f i = e₀.hom.hom ((P.d (-1) 0).hom
          (e₁.inv.hom (Pi.single i 1)))) ∧
        (∀ i, Ideal.Quotient.mk I (f i) = S.residueSequence i) := by
  classical
  let I := Ideal.map (algebraMap S.R S.A) (IsLocalRing.maximalIdeal S.R)
  let E := (Koszul.seqComplex S.residueSequence).extend ComplexShape.embeddingDownNat
  let D := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral
    (Ideal.Quotient.mk I)
  have hEzero (i : ℤ) (hi : 0 < i) : IsZero (E.X i) := by
    apply HomologicalComplex.isZero_extend_X
    intro n
    simp only [ComplexShape.embeddingDownNat_f]
    omega
  have hEbd : ∃ b, CochainComplex.IsStrictlyLE E b :=
    ⟨0, (CochainComplex.isStrictlyLE_iff E 0).2 hEzero⟩
  have hEterm (n : ℕ) : Module.Finite (S.A ⧸ I) (E.X (-(n : ℤ))) ∧
      Module.Free (S.A ⧸ I) (E.X (-(n : ℤ))) := by
    let e := HomologicalComplex.extendXIso (Koszul.seqComplex S.residueSequence)
      ComplexShape.embeddingDownNat (show ComplexShape.embeddingDownNat.f n = -(n : ℤ) by rfl)
    have hex := exteriorPower_finiteFree (R := S.A ⧸ I) S.r n
    let : Module.Finite (S.A ⧸ I) ((Koszul.seqComplex S.residueSequence).X n) := hex.1
    let : Module.Free (S.A ⧸ I) ((Koszul.seqComplex S.residueSequence).X n) := hex.2
    exact ⟨Module.Finite.equiv e.symm.toLinearEquiv, Module.Free.of_equiv e.symm.toLinearEquiv⟩
  have hEterms (i : ℤ) : Module.Finite (S.A ⧸ I) (E.X i) ∧
      Module.IsStablyFree (S.A ⧸ I) (E.X i) := by
    by_cases hi : i ≤ 0
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = -(n : ℤ) := ⟨(-i).toNat, by omega⟩
      have := (hEterm n).2
      exact ⟨(hEterm n).1, inferInstance⟩
    · have : Subsingleton (E.X i) := ModuleCat.subsingleton_of_isZero (hEzero i (not_le.1 hi))
      constructor <;> infer_instance
  have hK : StacksDraft.PseudoCoherence.IsPseudoCoherent S.K :=
    (((StacksDraft.Perfect.isPerfect_iff_pseudoCoherent_and_finiteTorDimension S.K).1.mp
      S.K_perfect).1)
  have hI : ∀ x ∈ I, IsUnit (1 + x) := by
    intro x hx
    have hmap : I ≤ IsLocalRing.maximalIdeal S.A := by
      apply Ideal.map_le_iff_le_comap.mpr
      rw [IsLocalRing.maximalIdeal_comap]
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hx'
    have h1 : (1 : S.A) ∈ IsLocalRing.maximalIdeal S.A := by
      simpa using (IsLocalRing.maximalIdeal S.A).sub_mem hx' (hmap hx)
    exact (IsLocalRing.maximalIdeal.isMaximal S.A).ne_top
      ((Ideal.eq_top_iff_one (IsLocalRing.maximalIdeal S.A)).mpr h1)
  have hErep : Nonempty ((DerivedCategory.Q.obj E) ≅ D.functor.obj S.K) :=
    ⟨S.closedFiber_isKoszul.some.symm⟩
  obtain ⟨P, hP, hPbdd, hRed, hPK, hfree⟩ :=
    StacksDraft.Perfect.exists_boundedAbove_isStablyFree_lift_representing_of_datum
      I D S.K E hEbd hEterms hErep hK hI
  let restrict := ModuleCat.restrictScalars (Ideal.Quotient.mk I)
  let qP (n : ℕ) := TensorProduct.quotTensorEquivQuotSMul (P.X (-(n : ℤ)) : Type u) I
  let qF (n : ℕ) := TensorProduct.quotTensorEquivQuotSMul (Fin (S.r.choose n) → S.A) I
  let red (n : ℕ) := (restrict.mapIso ((HomologicalComplex.eval (ModuleCat.{u} (S.A ⧸ I))
    (ComplexShape.up ℤ) (-(n : ℤ))).mapIso hRed.some)).toLinearEquiv
  let term (n : ℕ) := (restrict.mapIso
    (HomologicalComplex.extendXIso (Koszul.seqComplex S.residueSequence)
      ComplexShape.embeddingDownNat
      (show ComplexShape.embeddingDownNat.f n = -(n : ℤ) by rfl) ≪≫
      exteriorPower_finIso (R := S.A ⧸ I) S.r n)).toLinearEquiv
  let basis (n : ℕ) := (restrict.mapIso ((Pi.basisFun S.A (Fin (S.r.choose n))).baseChange
    (S.A ⧸ I)).equivFun.toModuleIso.symm).toLinearEquiv
  have hTerm (n : ℕ) : ∃ e : P.X (-(n : ℤ)) ≅ ModuleCat.of S.A (Fin (S.r.choose n) → S.A),
      ∀ y : P.X (-(n : ℤ)), (1 : S.A ⧸ I) ⊗ₜ[S.A] e.hom.hom y =
        basis n (term n (red n ((qP n).symm (Submodule.mkQ (I • ⊤) y)))) := by
    let : Module.Finite S.A (P.X (-(n : ℤ))) := (hP (-(n : ℤ))).1
    let : Module.Free S.A (P.X (-(n : ℤ))) := hfree (-(n : ℤ)) (hEterm n).2
    obtain ⟨eLift, heLift⟩ := exists_lift_linearEquiv_quotient I hI
      ((qP n).symm.trans ((red n).trans ((term n).trans ((basis n).trans (qF n)))))
    refine ⟨eLift.toModuleIso, fun y => (qF n).injective ?_⟩
    rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul]
    exact congrArg (fun g => g (Submodule.mkQ (I • ⊤) y)) heLift
  have hTerms : ∀ n : ℕ,
      Nonempty (P.X (-(n : ℤ)) ≅
        ModuleCat.of S.A (Fin (S.r.choose n) → S.A)) :=
    fun n => ⟨(hTerm n).choose⟩
  have hPositive (i : ℤ) (hi : 0 < i) : IsZero (P.X i) := by
    let eRedI := (HomologicalComplex.eval (ModuleCat.{u} (S.A ⧸ I))
      (ComplexShape.up ℤ) i).mapIso hRed.some
    have hzExt : IsZero (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj
        (P.X i))) := CategoryTheory.Limits.IsZero.of_iso (hEzero i hi) eRedI
    have : Subsingleton (TensorProduct S.A (S.A ⧸ I) (P.X i)) := by
      show Subsingleton ↑(((ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj
        (P.X i)))
      exact ModuleCat.subsingleton_of_isZero hzExt
    let qeq := TensorProduct.quotTensorEquivQuotSMul (P.X i : Type u) I
    let : Subsingleton (P.X i ⧸ I • (⊤ : Submodule S.A (P.X i))) :=
      qeq.symm.injective.subsingleton
    have hle : (⊤ : Submodule S.A (P.X i)) ≤ I • ⊤ := fun _ _ =>
      (Submodule.Quotient.mk_eq_zero (I • (⊤ : Submodule S.A (P.X i)))).mp (Subsingleton.elim _ _)
    let : Module.Finite S.A (P.X i) := (hP i).1
    have htop : (⊤ : Submodule S.A (P.X i)) = ⊥ :=
      Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I ⊤ Module.Finite.fg_top hle
        (jacobson_aux I hI)
    have : Subsingleton (P.X i) :=
      (Submodule.subsingleton_iff S.A).mp (subsingleton_of_bot_eq_top htop.symm)
    exact ModuleCat.isZero_of_subsingleton (P.X i)
  obtain ⟨e₀base, he₀⟩ := hTerm 0
  obtain ⟨e₁base, he₁⟩ := hTerm 1
  let e₀ := e₀base ≪≫
    (LinearEquiv.piCongrLeft' S.A (fun _ : Fin (S.r.choose 0) => S.A)
      (Equiv.cast (congrArg Fin (Nat.choose_zero_right S.r)))).toModuleIso ≪≫
        (scalar_finOneEquiv (R := S.A)).symm.toModuleIso
  let e₁ := e₁base ≪≫
    (LinearEquiv.piCongrLeft' S.A (fun _ : Fin (S.r.choose 1) => S.A)
      (Equiv.cast (congrArg Fin (Nat.choose_one_right S.r)))).toModuleIso
  let f : Fin S.r → S.A := fun i =>
    e₀.hom.hom ((P.d (-1) 0).hom (e₁.inv.hom (Pi.single i 1)))
  refine ⟨P, f, hPK, hRed, hTerms, hPositive, e₀, e₁, fun _ => rfl, fun i => ?_⟩
  have hcomm := hRed.some.hom.comm (-1) 0
  rw [CategoryTheory.Functor.mapHomologicalComplex_obj_d] at hcomm
  let y := e₁.inv.hom (Pi.single i 1)
  let x : ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj (P.X (-1))) :=
    (1 : S.A ⧸ I) ⊗ₜ[S.A] y
  have hlin := congrArg ModuleCat.Hom.hom hcomm
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at hlin
  have hEval := congrArg (fun g => g x) hlin
  have hybase : e₁base.hom.hom y =
      (LinearEquiv.piCongrLeft' S.A (fun _ : Fin (S.r.choose 1) => S.A)
        (Equiv.cast (congrArg Fin (Nat.choose_one_right S.r)))).symm (Pi.single i 1) := by
    simp [y, e₁]
  let z := (P.d (-1) 0).hom y
  change (ModuleCat.Hom.hom (E.d (-1) 0))
      ((ModuleCat.Hom.hom (hRed.some.hom.f (-1))) x) =
    (ModuleCat.Hom.hom (hRed.some.hom.f 0))
      ((ModuleCat.Hom.hom ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map
        (P.d (-1) 0))) x) at hEval
  have hmap : (ModuleCat.Hom.hom ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map
      (P.d (-1) 0))) ((1 : S.A ⧸ I) ⊗ₜ[S.A] y) =
      (1 : S.A ⧸ I) ⊗ₜ[S.A] z :=
    rfl
  rw [hmap] at hEval
  have hcoordLeft : (basis 1).symm
      ((1 : S.A ⧸ I) ⊗ₜ[S.A]
        (LinearEquiv.piCongrLeft' S.A (fun _ : Fin (S.r.choose 1) => S.A)
          (Equiv.cast (congrArg Fin (Nat.choose_one_right S.r)))).symm (Pi.single i 1)) =
      Pi.single ((Equiv.cast (congrArg Fin (Nat.choose_one_right S.r))).symm i) 1 := by
    let v : ↑((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj
        (ModuleCat.of (S.A ⧸ I) (TensorProduct S.A (S.A ⧸ I) (Fin (S.r.choose 1) → S.A)))) :=
      (1 : S.A ⧸ I) ⊗ₜ[S.A]
        (LinearEquiv.piCongrLeft' S.A (fun _ : Fin (S.r.choose 1) => S.A)
          (Equiv.cast (congrArg Fin (Nat.choose_one_right S.r)))).symm (Pi.single i 1)
    show (ConcreteCategory.hom ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).map
      (ModuleCat.ofHom ((Pi.basisFun S.A (Fin (S.r.choose 1))).baseChange
        (S.A ⧸ I)).equivFun.toLinearMap))) v = _
    rw [ModuleCat.restrictScalars.map_apply]
    dsimp [v, ModuleCat.restrictScalars, ModuleCat.RestrictScalars.obj']
    ext j
    simp [Module.Basis.baseChange_repr_tmul, Pi.basisFun_repr,
      LinearEquiv.piCongrLeft'_symm_apply,
      Equiv.eq_symm_apply, Pi.single_apply]
  have hterm1 : term 1 (red 1 ((qP 1).symm (Submodule.mkQ (I • ⊤) y))) =
      Pi.single ((Equiv.cast (congrArg Fin (Nat.choose_one_right S.r))).symm i) 1 := by
    have hc := ((basis 1).symm_apply_eq).2 (he₁ y)
    rw [hybase, hcoordLeft] at hc
    exact hc.symm
  let hred1 := (ModuleCat.Hom.hom (hRed.some.hom.f (-1))) x
  let w1 :=
    (HomologicalComplex.extendXIso (Koszul.seqComplex S.residueSequence)
      ComplexShape.embeddingDownNat
      (show ComplexShape.embeddingDownNat.f 1 = -1 by rfl)).hom.hom hred1
  let eFin1 : Fin S.r ≃ Fin (S.r.choose 1) :=
    Equiv.cast (congrArg Fin (Nat.choose_one_right S.r).symm)
  have hcomp1 : (LinearEquiv.piCongrLeft' (S.A ⧸ I)
      (fun _ : Fin S.r => S.A ⧸ I) eFin1)
      (exteriorPower.oneEquiv (S.A ⧸ I) (Fin S.r → S.A ⧸ I) w1) =
      Pi.single ((Equiv.cast (congrArg Fin (Nat.choose_one_right S.r))).symm i) 1 :=
    hterm1
  let L := LinearEquiv.piCongrLeft' (S.A ⧸ I)
    (fun _ : Fin S.r => S.A ⧸ I) eFin1
  have hL : L.symm (Pi.single ((Equiv.cast
      (congrArg Fin (Nat.choose_one_right S.r))).symm i) 1) = Pi.single i 1 := by
    have hidx : (Equiv.cast (congrArg Fin (Nat.choose_one_right S.r))).symm i = eFin1 i := rfl
    ext j
    simp only [L, LinearEquiv.piCongrLeft'_symm_apply,
      Equiv.piCongrLeft'_symm_apply, Pi.single_apply]
    rw [hidx]
    simp [eFin1.apply_eq_iff_eq]
  have hOne : exteriorPower.oneEquiv (S.A ⧸ I) (Fin S.r → S.A ⧸ I) w1 =
      Pi.single i 1 := by
    calc
      _ = L.symm (L ((exteriorPower.oneEquiv (S.A ⧸ I)
          (Fin S.r → S.A ⧸ I) w1))) := (LinearEquiv.symm_apply_apply L _).symm
      _ = L.symm (Pi.single ((Equiv.cast
          (congrArg Fin (Nat.choose_one_right S.r))).symm i) 1) := congrArg L.symm hcomp1
      _ = Pi.single i 1 := hL
  let x0 : ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj (P.X 0)) :=
    (1 : S.A ⧸ I) ⊗ₜ[S.A] z
  have hcoord0' : (basis 0).symm ((1 : S.A ⧸ I) ⊗ₜ[S.A] e₀base.hom.hom z) =
      term 0 (red 0 ((qP 0).symm (Submodule.mkQ (I • ⊤) z))) :=
    ((basis 0).symm_apply_eq).2 (he₀ z)
  let eFin0 : Fin (S.r.choose 0) ≃ Fin 1 :=
    Equiv.cast (congrArg Fin (Nat.choose_zero_right S.r))
  let p0 : (Fin (S.r.choose 0) → S.A) ≃ₗ[S.A] S.A :=
    (LinearEquiv.piCongrLeft' S.A (fun _ : Fin (S.r.choose 0) => S.A) eFin0).trans
      (scalar_finOneEquiv (R := S.A)).symm
  let p0bar : (Fin (S.r.choose 0) → S.A ⧸ I) ≃ₗ[S.A ⧸ I] (S.A ⧸ I) :=
    (LinearEquiv.piCongrLeft' (S.A ⧸ I)
      (fun _ : Fin (S.r.choose 0) => S.A ⧸ I) eFin0).trans
      (scalar_finOneEquiv (R := S.A ⧸ I)).symm
  let bFRed0 := Module.Basis.baseChange (S.A ⧸ I) (Pi.basisFun S.A (Fin (S.r.choose 0)))
  have hscalar0 := congrArg p0bar hcoord0'
  have hleft0 : p0bar ((basis 0).symm ((1 : S.A ⧸ I) ⊗ₜ[S.A] e₀base.hom.hom z)) =
      Ideal.Quotient.mk I (p0 (e₀base.hom.hom z)) := by
    show p0bar (bFRed0.equivFun ((1 : S.A ⧸ I) ⊗ₜ[S.A]
      e₀base.hom.hom z)) = _
    simp [p0bar, p0, eFin0, scalar_finOneEquiv, bFRed0,
      Module.Basis.equivFun_apply, Module.Basis.baseChange_repr_tmul,
      Pi.basisFun_repr, LinearEquiv.piCongrLeft'_apply,
      ← Algebra.algebraMap_eq_smul_one, Ideal.Quotient.algebraMap_eq]
  have hcoeff : Ideal.Quotient.mk I (f i) =
      p0bar (term 0 (red 0 ((qP 0).symm (Submodule.mkQ
        (I • ⊤) z)))) := by
    calc
      _ = p0bar ((basis 0).symm ((1 : S.A ⧸ I) ⊗ₜ[S.A] e₀base.hom.hom z)) := by
        rw [hleft0]
        show Ideal.Quotient.mk I (e₀.hom.hom z) =
          Ideal.Quotient.mk I (p0 (e₀base.hom.hom z))
        rfl
      _ = _ := hscalar0
  let eX0 := (Koszul.seqComplex S.residueSequence).extendXIso
    ComplexShape.embeddingDownNat
    (show ComplexShape.embeddingDownNat.f 0 = 0 by rfl)
  let hred0 := (ModuleCat.Hom.hom (hRed.some.hom.f 0)) x0
  let w0 := (ModuleCat.Hom.hom eX0.hom) hred0
  have hKoszulD : (ModuleCat.Hom.hom ((Koszul.seqComplex S.residueSequence).d 1 0))
      w1 = w0 := by
    have h' := congrArg (ModuleCat.Hom.hom eX0.hom) hEval
    have hEtoK : (ModuleCat.Hom.hom eX0.hom)
        ((ModuleCat.Hom.hom (E.d (-1) 0)) hred1) =
        (ModuleCat.Hom.hom ((Koszul.seqComplex S.residueSequence).d 1 0)) w1 := by
      have hd := HomologicalComplex.extend_d_eq (Koszul.seqComplex S.residueSequence)
        ComplexShape.embeddingDownNat
        (show ComplexShape.embeddingDownNat.f 1 = -1 by rfl)
        (show ComplexShape.embeddingDownNat.f 0 = 0 by rfl)
      show (ModuleCat.Hom.hom eX0.hom)
          ((ModuleCat.Hom.hom
            (((Koszul.seqComplex S.residueSequence).extend
              ComplexShape.embeddingDownNat).d (-1) 0)) hred1) = _
      rw [hd]
      simp [ModuleCat.hom_comp, LinearMap.comp_apply, w1, eX0]
    exact hEtoK.symm.trans h'
  have hscalarSeq : exteriorPower.zeroEquiv (S.A ⧸ I) (Fin S.r → S.A ⧸ I) w0 =
      S.residueSequence i := by
    have hKoszulD' : Koszul.d (Koszul.seqDual S.residueSequence) 0 w1 = w0 := hKoszulD
    have hd := congrArg
      (exteriorPower.zeroEquiv (S.A ⧸ I) (Fin S.r → S.A ⧸ I)) hKoszulD'
    have hzero := Koszul.zeroEquiv_d_zero S.residueSequence w1
    calc
      exteriorPower.zeroEquiv (S.A ⧸ I) (Fin S.r → S.A ⧸ I) w0 =
          Koszul.seqDual S.residueSequence
            (exteriorPower.oneEquiv (S.A ⧸ I) (Fin S.r → S.A ⧸ I) w1) :=
        (hzero.symm.trans hd).symm
      _ = S.residueSequence i := by rw [hOne, Koszul.seqDual_single]
  have hcoordSeq : p0bar (term 0 (red 0 ((qP 0).symm (Submodule.mkQ
      (I • ⊤) z)))) =
      exteriorPower.zeroEquiv (S.A ⧸ I) (Fin S.r → S.A ⧸ I) w0 := by
    show p0bar ((exteriorPower_finIso (R := S.A ⧸ I) S.r 0).hom.hom w0) =
      exteriorPower.zeroEquiv (S.A ⧸ I) (Fin S.r → S.A ⧸ I) w0
    show scalar_finOneEquiv (R := S.A ⧸ I)
        (exteriorPower.zeroEquiv (S.A ⧸ I) (Fin S.r → S.A ⧸ I) w0)
        (eFin0 (eFin0.symm 0)) = _
    simp [scalar_finOneEquiv]
  rw [hcoeff, hcoordSeq]
  exact hscalarSeq

end AlgebraicGeometry
