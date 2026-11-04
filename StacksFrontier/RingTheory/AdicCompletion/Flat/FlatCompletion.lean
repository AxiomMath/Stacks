module

public import StacksFrontier.RingTheory.AdicCompletion.Flat.TensorLimit

/-!
# Flatness of the adic completion of a module

This file proves that the `I`-adic completion of a flat module over a Noetherian ring is flat, that
the completion `(⊕_{α ∈ A} R)^∧` is flat, and that `R^∧` is Noetherian and `M^∧` is flat over
`R^∧` when `I` is finitely generated, `R/I` is Noetherian, `M/IM` is flat over `R/I` and
`Tor₁ᴿ(M, R/I) = 0`.

## Main definitions

* `quotientTower`, `adicCompletionCone`, `adicCompletionIsLimit`

## Main results

* `adicCompletion_flat_of_flat`
* `AdicCompletion.flat_directSum`
* `AdicCompletion.isNoetherianRing_and_flat_of_flat_quotient`
-/

@[expose] public section

universe u v

/-- The transition maps `M ⧸ Iⁿ • ⊤ → M ⧸ Iᵐ • ⊤` of the `I`-adic filtration of a module are
surjective. -/
private theorem transitionMap_surjective {R : Type*} [CommRing R] (I : Ideal R)
    (M : Type*) [AddCommGroup M] [Module R M] {m n : ℕ} (h : m ≤ n) :
    Function.Surjective (AdicCompletion.transitionMap I M h) :=
  Submodule.factor_surjective (Submodule.pow_smul_top_le I M h)

section FlatDirectSum

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

/-- The tower of quotients `M ⧸ Iⁿ • ⊤` of a module `M`, with the canonical projections as
transition maps. -/
noncomputable def quotientTower {R : Type u} [CommRing R] (I : Ideal R)
    (M : Type u) [AddCommGroup M] [Module R M] : ℕᵒᵖ ⥤ ModuleCat.{u} R where
  obj n := ModuleCat.of R (M ⧸ (I ^ n.unop • (⊤ : Submodule R M)))
  map {n m} f := ModuleCat.ofHom (AdicCompletion.transitionMap I M (leOfHom f.unop))
  map_id := by
    intro n
    ext x
    rfl
  map_comp := by
    intro n m k f g
    ext x
    rfl

/-- The cone over `quotientTower I M` with vertex the `I`-adic completion of `M` and the
evaluation maps as projections. -/
noncomputable def adicCompletionCone {R : Type u} [CommRing R] (I : Ideal R)
    (M : Type u) [AddCommGroup M] [Module R M] : Cone (quotientTower I M) where
  pt := ModuleCat.of R (AdicCompletion I M)
  π := {
    app n := ModuleCat.ofHom (AdicCompletion.eval I M n.unop)
    naturality := by
      intro n m f
      ext x
      exact (x.property (leOfHom f.unop)).symm }

/-- The `I`-adic completion of `M` is the limit of the tower `quotientTower I M`. -/
noncomputable def adicCompletionIsLimit {R : Type u} [CommRing R] (I : Ideal R)
    (M : Type u) [AddCommGroup M] [Module R M] : IsLimit (adicCompletionCone I M) :=
  IsLimit.mk
    (fun s => ModuleCat.ofHom {
      toFun := fun x => ⟨fun n => (s.π.app (.op n)) x, by
        intro m n h
        have hw := s.w (homOfLE h).op
        have := congrArg (fun f : s.pt ⟶ (quotientTower I M).obj (.op m) => f x) hw
        change (AdicCompletion.transitionMap I M h) ((s.π.app (.op n)) x) =
          (s.π.app (.op m)) x at this
        exact this⟩
      map_add' x y := AdicCompletion.ext fun n => (s.π.app (.op n)).hom.map_add x y
      map_smul' r x := AdicCompletion.ext fun n => (s.π.app (.op n)).hom.map_smul r x })
    (by
      intro s n
      ext x
      rfl)
    (by
      intro s f hf
      ext x
      refine AdicCompletion.ext fun n => ?_
      have h := congrArg (fun g : s.pt ⟶ (quotientTower I M).obj (.op n) => g x) (hf (.op n))
      exact h)

/-- The `I`-adic completion of a flat module over a Noetherian ring is flat. -/
theorem adicCompletion_flat_of_flat {R : Type u} [CommRing R]
    [IsNoetherianRing R] (I : Ideal R)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Flat R M] :
    Module.Flat R (AdicCompletion I M) := by
  let F := quotientTower I M
  let qmod : ∀ n : ℕ, Module (R ⧸ I ^ n) (F.obj (.op n)) :=
    fun n => Module.instQuotientIdealSubmoduleHSMulTop M (I ^ n)
  have hscalar : ∀ n : ℕ, let := qmod n
      IsScalarTower R (R ⧸ I ^ n) (F.obj (.op n)) := by
    intro n
    show IsScalarTower R (R ⧸ I ^ n) (M ⧸ (I ^ n • (⊤ : Submodule R M)))
    infer_instance
  have hflat : ∀ n : ℕ, let := qmod n
      Module.Flat (R ⧸ I ^ n) (F.obj (.op n)) :=
    fun n => Module.Flat.quotient_smul_top (I ^ n)
  have hsurj : ∀ n : ℕ, Function.Surjective
      (F.map (homOfLE (Nat.le_succ n)).op) :=
    fun n => transitionMap_surjective I M (Nat.le_succ n)
  have : Module.Flat R (limit.cone F).pt :=
    (flat_limit_and_tensor_limit_of_flat_quotients I F qmod hscalar hflat hsurj).1
  let e := ((limit.isLimit F).conePointUniqueUpToIso (adicCompletionIsLimit I M)).toLinearEquiv
  exact Module.Flat.of_linearEquiv e.symm

private theorem ulift_pow_smul_top {R : Type u} [CommRing R]
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) :
    ((I.map (algebraMap R (ULift.{v} R))) ^ n •
      (⊤ : Submodule (ULift.{v} R) M)).restrictScalars R =
    I ^ n • (⊤ : Submodule R M) := by
  rw [← Ideal.map_pow]
  simpa using Submodule.restrictScalars_map_smul_eq (I ^ n)
    (⊤ : Submodule (ULift.{v} R) M)

private noncomputable def uliftQuotientEquiv {R : Type u} [CommRing R]
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) :
    (M ⧸ ((I.map (algebraMap R (ULift.{v} R))) ^ n •
      (⊤ : Submodule (ULift.{v} R) M))) ≃ₗ[R]
      (M ⧸ I ^ n • (⊤ : Submodule R M)) := by
  let P : Submodule (ULift.{v} R) M :=
    (I.map (algebraMap R (ULift.{v} R))) ^ n • ⊤
  exact (Submodule.Quotient.restrictScalarsEquiv R P).symm.trans
    ((P.restrictScalars R).quotEquivOfEq
      (I ^ n • (⊤ : Submodule R M)) (ulift_pow_smul_top I M n))

private theorem uliftQuotientEquiv_mk {R : Type u} [CommRing R]
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) (x : M) :
    uliftQuotientEquiv I M n (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := by
  simp [uliftQuotientEquiv, Submodule.Quotient.restrictScalarsEquiv_symm_mk,
    Submodule.quotEquivOfEq_mk]

private theorem uliftQuotientEquiv_transition {R : Type u} [CommRing R]
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    {m n : ℕ} (h : m ≤ n)
    (x : M ⧸ (I.map (algebraMap R (ULift.{v} R))) ^ n •
      (⊤ : Submodule (ULift.{v} R) M)) :
    uliftQuotientEquiv I M m
      (AdicCompletion.transitionMap (I.map (algebraMap R (ULift.{v} R))) M h x) =
    AdicCompletion.transitionMap I M h (uliftQuotientEquiv I M n x) := by
  induction x using Quotient.inductionOn' with
  | _ x =>
    show uliftQuotientEquiv I M m
        (AdicCompletion.transitionMap (I.map (algebraMap R (ULift.{v} R))) M h
          (Submodule.Quotient.mk x)) =
      AdicCompletion.transitionMap I M h
        (uliftQuotientEquiv I M n (Submodule.Quotient.mk x))
    dsimp only [AdicCompletion.transitionMap, Submodule.factorPow]
    rw [← Submodule.mkQ_apply, Submodule.factor_mk]
    simp only [Submodule.mkQ_apply, uliftQuotientEquiv_mk]
    exact (Submodule.factor_mk (Submodule.pow_smul_top_le I M h) x).symm

private noncomputable def uliftAdicCompletionEquiv {R : Type u} [CommRing R]
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] :
    AdicCompletion (I.map (algebraMap R (ULift.{v} R))) M ≃ₗ[R]
      AdicCompletion I M where
  toFun x := ⟨fun n => uliftQuotientEquiv I M n (x.val n), by
    intro m n h
    rw [← uliftQuotientEquiv_transition I M h, x.property h]⟩
  invFun x := ⟨fun n => (uliftQuotientEquiv I M n).symm (x.val n), by
    intro m n h
    apply (uliftQuotientEquiv I M m).injective
    rw [uliftQuotientEquiv_transition I M h]
    simp [x.property h]⟩
  left_inv x := AdicCompletion.ext fun n => (uliftQuotientEquiv I M n).symm_apply_apply (x.val n)
  right_inv x := AdicCompletion.ext fun n => (uliftQuotientEquiv I M n).apply_symm_apply (x.val n)
  map_add' x y := AdicCompletion.ext fun n => (uliftQuotientEquiv I M n).map_add (x.val n) (y.val n)
  map_smul' r x := AdicCompletion.ext fun n => (uliftQuotientEquiv I M n).map_smul r (x.val n)

private theorem adicCompletion_flat_of_flat_general {R : Type u} [CommRing R]
    [IsNoetherianRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Flat R M] :
    Module.Flat R (AdicCompletion I M) := by
  let S := ULift.{v} R
  let J : Ideal S := I.map (algebraMap R S)
  have : IsNoetherianRing S :=
    isNoetherianRing_of_ringEquiv R (ULift.ringEquiv.symm : R ≃+* S)
  have hM : Module.Flat S M := Module.Flat.ulift_left_iff.mpr inferInstance
  let N := ULift.{u} M
  have hN : Module.Flat S N := Module.Flat.ulift_right_iff.mpr hM
  have hS : Module.Flat S (AdicCompletion J N) :=
    adicCompletion_flat_of_flat J N
  have hSM : Module.Flat S (AdicCompletion J M) := by
    let e := (AdicCompletion.congr J (ULift.moduleEquiv : N ≃ₗ[S] M)).restrictScalars S
    exact Module.Flat.of_linearEquiv e.symm
  have hR : Module.Flat R (AdicCompletion J M) :=
    Module.Flat.ulift_left_iff.mp hSM
  exact Module.Flat.of_linearEquiv (uliftAdicCompletionEquiv I M).symm

/-- For a Noetherian ring `R` and an ideal `I`, the `I`-adic completion `(⊕_{α ∈ A} R)^∧` of an
arbitrary direct sum of copies of `R` is a flat `R`-module. -/
@[stacks 06LE, ega "0 7.3.3" "more general", sga "1 IV 3.1" "more general"]
theorem AdicCompletion.flat_directSum
    (R : Type u) [CommRing R] (I : Ideal R) (A : Type v) [IsNoetherianRing R] :
    Module.Flat R (AdicCompletion I (DirectSum A (fun _ : A => R))) := by
  have : Module.Flat R (DirectSum A (fun _ : A => R)) := inferInstance
  exact adicCompletion_flat_of_flat_general I _

end FlatDirectSum

section CompletionFlat

set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

noncomputable section

private theorem flat_of_equiv {R S M N : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]
    (e : R ≃+* S) (f : M ≃+ N) (hf : ∀ r x, f (r • x) = e r • f x)
    [Module.Flat S N] : Module.Flat R M := by
  apply Module.Flat.of_forall_isTrivialRelation
  intro l a x hx
  have hx' : ∑ i, e (a i) • f (x i) = 0 := by
    simpa only [map_sum, hf, map_zero] using congrArg f hx
  obtain ⟨k, b, y, hxy, hab⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hx'
  refine ⟨k, fun i j => e.symm (b i j), fun j => f.symm (y j), ?_, ?_⟩
  · intro i
    apply f.injective
    simpa only [map_sum, hf, e.apply_symm_apply, f.apply_symm_apply] using hxy i
  · intro j
    apply e.injective
    simpa only [map_sum, map_mul, e.apply_symm_apply, map_zero] using hab j

private theorem flat_quotient_iff_of_equiv {R S M N : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]
    (e : R ≃+* S) (f : M ≃+ N) (hf : ∀ r x, f (r • x) = e r • f x)
    (I : Ideal R) (J : Ideal S) (hIJ : J = I.map e) :
    Module.Flat (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M)) ↔
      Module.Flat (S ⧸ J) (N ⧸ J • (⊤ : Submodule S N)) := by
  have := RingHomInvPair.of_ringEquiv e
  have := RingHomInvPair.of_ringEquiv_symm e
  have : RingHomSurjective (e : R →+* S) := ⟨e.surjective⟩
  let g : M ≃ₛₗ[(e : R →+* S)] N := { f with map_smul' := hf }
  have hsub : (I • (⊤ : Submodule R M)).map g.toLinearMap =
      J • (⊤ : Submodule S N) := by
    subst J
    apply le_antisymm
    · rw [Submodule.map_le_iff_le_comap]
      refine Submodule.smul_le.2 fun r hr x _ => ?_
      show f (r • x) ∈ I.map e • (⊤ : Submodule S N)
      rw [hf]
      exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem e hr) Submodule.mem_top
    · refine Submodule.smul_le.2 fun s hs y _ => ?_
      obtain ⟨r, hr, rfl⟩ := (Ideal.mem_map_iff_of_surjective e e.surjective).mp hs
      refine Submodule.mem_map.2 ⟨r • f.symm y,
        Submodule.smul_mem_smul hr Submodule.mem_top, ?_⟩
      exact (hf _ _).trans (by rw [f.apply_symm_apply])
  let q := Submodule.Quotient.equiv _ _ g hsub
  let er := Ideal.quotientEquiv I J e hIJ
  have hq : ∀ r x, q (r • x) = er r • q x := by
    intro r x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    show Submodule.Quotient.mk (f (r • x)) =
      (Submodule.Quotient.mk (e r • f x) : N ⧸ J • (⊤ : Submodule S N))
    rw [hf]
  constructor
  · intro h
    let := h
    apply flat_of_equiv er.symm q.toAddEquiv.symm
    intro r x
    apply q.injective
    show q (q.symm (r • x)) = q (er.symm r • q.symm x)
    rw [hq, q.apply_symm_apply, er.apply_symm_apply, q.apply_symm_apply]
  · intro h
    let := h
    exact flat_of_equiv er q.toAddEquiv hq

private theorem flat_quotient_pow_of_isZero_tor
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R)
    (hflat : Module.Flat (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M)))
    (htor : IsZero
      (((Tor (ModuleCat.{max u v} (ULift.{v} R)) 1).obj
        (ModuleCat.of (ULift.{v} R) (ULift.{u} M))).obj
        (ModuleCat.of (ULift.{v} R) (ULift.{v} (R ⧸ I))))) (n : ℕ) :
    Module.Flat (R ⧸ I ^ n) (M ⧸ I ^ n • (⊤ : Submodule R M)) := by
  let S := ULift.{v} R
  let N := ULift.{u} M
  let e : R ≃+* S := ULift.ringEquiv.symm
  let f : M ≃+ N := (ULift.moduleEquiv : N ≃ₗ[R] M).symm.toAddEquiv
  let J : Ideal S := I.map e
  have hf : ∀ r x, f (r • x) = e r • f x := fun _ _ => rfl
  have hflat' := (flat_quotient_iff_of_equiv e f hf I J rfl).mp hflat
  let er := Ideal.quotientEquiv I J e rfl
  let g : (S ⧸ J) ≃ₗ[S] ULift.{v} (R ⧸ I) :=
    { er.symm.toAddEquiv.trans
        (ULift.moduleEquiv : ULift.{v} (R ⧸ I) ≃ₗ[R] (R ⧸ I)).symm.toAddEquiv with
      map_smul' := by
        intro s x
        obtain ⟨r, rfl⟩ := e.surjective s
        obtain ⟨x, rfl⟩ := er.surjective x
        apply ULift.down_injective
        show er.symm (e r • er x) = r • er.symm (er x)
        rw [er.symm_apply_apply]
        apply er.injective
        simp only [er.apply_symm_apply]
        show Ideal.Quotient.mk J (e r) * er x = er (Ideal.Quotient.mk I r * x)
        rw [map_mul]
        rfl }
  have ht : Tor1Vanishes S N (S ⧸ J) :=
    htor.of_iso (((Tor (ModuleCat.{max u v} S) 1).obj (ModuleCat.of S N)).mapIso
      g.toModuleIso)
  obtain ⟨et⟩ := tor_symm_canonically_iso S 1
  have ht' : Tor1Vanishes S (S ⧸ J) N :=
    ht.of_iso ((et.app (ModuleCat.of S (S ⧸ J))).app (ModuleCat.of S N))
  have hpow : Module.Flat (S ⧸ J ^ n) (N ⧸ J ^ n • (⊤ : Submodule S N)) := by
    cases n with
    | zero =>
      have : Subsingleton (N ⧸ J ^ 0 • (⊤ : Submodule S N)) := by
        rw [pow_zero, one_smul]
        infer_instance
      infer_instance
    | succ n => exact flat_quotient_pow J hflat' ht' (n + 1) (Nat.succ_pos n)
  exact (flat_quotient_iff_of_equiv e f hf (I ^ n) (J ^ n)
    (Ideal.map_pow e I n).symm).mpr hpow

private abbrev liftedEval {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ) :
    ULift.{v} (AdicCompletion I R) →+* R ⧸ I ^ n :=
  (AdicCompletion.evalₐ I n).toRingHom.comp ULift.ringEquiv.toRingHom

private theorem ker_liftedEval {R : Type u} [CommRing R] (I : Ideal R)
    (hI : I.FG) (n : ℕ) :
    RingHom.ker (liftedEval.{u, v} I n) =
      (I.map (algebraMap R (ULift.{v} (AdicCompletion I R)))) ^ n := by
  show (RingHom.ker (AdicCompletion.evalₐ I n).toRingHom).comap
    ULift.ringEquiv.toRingHom = _
  rw [AdicCompletion.ker_evalₐ I hI n]
  calc
    _ = ((I.map (algebraMap R (AdicCompletion I R))) ^ n).map
        (ULift.ringEquiv.symm : AdicCompletion I R ≃+* ULift.{v} (AdicCompletion I R)) :=
      (Ideal.map_symm _).symm
    _ = _ := by
      have hc : (ULift.ringEquiv :
          ULift.{v} (AdicCompletion I R) ≃+* AdicCompletion I R).symm.toRingHom.comp
          (algebraMap R (AdicCompletion I R)) =
          algebraMap R (ULift.{v} (AdicCompletion I R)) := by
        ext r
        rfl
      rw [Ideal.map_pow]
      show ((I.map (algebraMap R (AdicCompletion I R))).map
        (ULift.ringEquiv : ULift.{v} (AdicCompletion I R) ≃+*
          AdicCompletion I R).symm.toRingHom) ^ n = _
      rw [Ideal.map_map, hc]

private abbrev quotientModule {R : Type u} [CommRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) :
    Module (ULift.{v} (AdicCompletion I R))
      (ULift.{u} (M ⧸ I ^ n • (⊤ : Submodule R M))) :=
  Module.compHom _ (liftedEval I n)

attribute [local instance] quotientModule

private noncomputable def completionTower {R : Type u} [CommRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] :
    ℕᵒᵖ ⥤ ModuleCat.{max u v} (ULift.{v} (AdicCompletion I R)) where
  obj n := ModuleCat.of _ (ULift.{u} (M ⧸ I ^ n.unop • (⊤ : Submodule R M)))
  map {n m} f := ModuleCat.ofHom {
    toFun x := ⟨AdicCompletion.transitionMap I M (leOfHom f.unop) x.down⟩
    map_add' x y := congrArg ULift.up (map_add _ _ _)
    map_smul' r x := by
      apply ULift.down_injective
      change AdicCompletion.transitionMap I M (leOfHom f.unop)
        (AdicCompletion.evalₐ I n.unop r.down • x.down) =
          AdicCompletion.evalₐ I m.unop r.down •
            AdicCompletion.transitionMap I M (leOfHom f.unop) x.down
      obtain ⟨y, hy⟩ := AdicCompletion.eval_surjective I M n.unop x.down
      rw [← hy, ← AdicCompletion.val_smul_eq_evalₐ_smul]
      change AdicCompletion.transitionMap I M (leOfHom f.unop) ((r.down • y).val n.unop) =
        AdicCompletion.evalₐ I m.unop r.down •
          AdicCompletion.transitionMap I M (leOfHom f.unop) (y.val n.unop)
      rw [(r.down • y).property (leOfHom f.unop), y.property (leOfHom f.unop)]
      exact AdicCompletion.val_smul_eq_evalₐ_smul _ _ _ _ }
  map_id n := by
    ext ⟨x⟩
    induction x using Submodule.Quotient.induction_on
    rfl
  map_comp f g := by
    ext ⟨x⟩
    induction x using Submodule.Quotient.induction_on
    rfl

private noncomputable def completionCone {R : Type u} [CommRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] : Cone (completionTower I M) where
  pt := ModuleCat.of _ (ULift.{u} (AdicCompletion I M))
  π := {
    app n := ModuleCat.ofHom {
      toFun x := ⟨x.down.val n.unop⟩
      map_add' _ _ := rfl
      map_smul' r x :=
        ULift.down_injective (AdicCompletion.val_smul_eq_evalₐ_smul I n.unop r.down _) }
    naturality := by
      intro n m f
      ext x
      exact congrArg ULift.up (x.down.property (leOfHom f.unop)).symm }

private noncomputable def completionConeIsLimit {R : Type u} [CommRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] : IsLimit (completionCone I M) :=
  IsLimit.mk
    (fun s => ModuleCat.ofHom {
      toFun x := ⟨⟨fun n => ((s.π.app (.op n)) x).down, by
        intro m n h
        exact congrArg (fun f : s.pt ⟶ (completionTower I M).obj (.op m) => (f x).down)
          (s.w (homOfLE h).op)⟩⟩
      map_add' x y := ULift.down_injective <| AdicCompletion.ext fun n =>
        congrArg ULift.down ((s.π.app (.op n)).hom.map_add x y)
      map_smul' r x := by
        refine ULift.down_injective (AdicCompletion.ext fun n => ?_)
        change ((s.π.app (.op n)) (r • x)).down =
          r.down.val n • ((s.π.app (.op n)) x).down
        rw [AdicCompletion.val_smul_eq_evalₐ_smul]
        exact congrArg ULift.down ((s.π.app (.op n)).hom.map_smul r x) })
    (by intro s n; ext x; rfl)
    (by
      intro s f hf
      ext x
      exact ULift.down_injective <| AdicCompletion.ext fun n =>
        congrArg (fun g : s.pt ⟶ (completionTower I M).obj (.op n) => (g x).down) (hf (.op n)))

private theorem adicCompletion_flat_of_flat_quotients
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (hI : I.FG) [IsNoetherianRing (AdicCompletion I R)]
    (hflat : ∀ n : ℕ, Module.Flat (R ⧸ I ^ n) (M ⧸ I ^ n • (⊤ : Submodule R M))) :
    Module.Flat (AdicCompletion I R) (AdicCompletion I M) := by
  let A := ULift.{v} (AdicCompletion I R)
  let J : Ideal A := I.map (algebraMap R A)
  let F := completionTower I M
  have hsur : ∀ n, Function.Surjective (liftedEval.{u, v} I n) := fun n =>
    (AdicCompletion.surjective_evalₐ I n).comp ULift.down_surjective
  let e (n : ℕ) : (A ⧸ J ^ n) ≃+* (R ⧸ I ^ n) :=
    (Ideal.quotEquivOfEq (ker_liftedEval I hI n).symm).trans
      (RingHom.quotientKerEquivOfSurjective (hsur n))
  have he (n : ℕ) (a : A) : e n (Ideal.Quotient.mk (J ^ n) a) = liftedEval I n a := by
    show (RingHom.quotientKerEquivOfSurjective (hsur n))
      ((Ideal.quotEquivOfEq (ker_liftedEval I hI n).symm) (Ideal.Quotient.mk (J ^ n) a)) = _
    rw [Ideal.quotEquivOfEq_mk]
    exact RingHom.quotientKerEquivOfSurjective_apply_mk (hsur n) a
  let qmod (n : ℕ) : Module (A ⧸ J ^ n) (F.obj (.op n)) :=
    Module.compHom (ULift.{u} (M ⧸ I ^ n • (⊤ : Submodule R M))) (e n).toRingHom
  have hscalar : ∀ n, let := qmod n
      IsScalarTower A (A ⧸ J ^ n) (F.obj (.op n)) := by
    intro n
    let : Module (A ⧸ J ^ n) (ULift.{u} (M ⧸ I ^ n • (⊤ : Submodule R M))) := qmod n
    show IsScalarTower A (A ⧸ J ^ n) (ULift.{u} (M ⧸ I ^ n • (⊤ : Submodule R M)))
    constructor
    intro a b x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    show e n (Ideal.Quotient.mk (J ^ n) (a * b)) • x =
      liftedEval I n a • (e n (Ideal.Quotient.mk (J ^ n) b) • x)
    rw [he, he, map_mul, mul_smul]
  have hflat' : ∀ n, let := qmod n
      Module.Flat (A ⧸ J ^ n) (F.obj (.op n)) := by
    intro n
    let : Module (A ⧸ J ^ n) (ULift.{u} (M ⧸ I ^ n • (⊤ : Submodule R M))) := qmod n
    have := hflat n
    have : Module.Flat (R ⧸ I ^ n) (ULift.{u} (M ⧸ I ^ n • (⊤ : Submodule R M))) :=
      Module.Flat.ulift_right_iff.mpr ‹_›
    show Module.Flat (A ⧸ J ^ n) (ULift.{u} (M ⧸ I ^ n • (⊤ : Submodule R M)))
    exact flat_of_equiv (e n) (AddEquiv.refl _) (fun _ _ => rfl)
  have htrans : ∀ n, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op) := by
    intro n x
    obtain ⟨y, hy⟩ := transitionMap_surjective I M (Nat.le_succ n) x.down
    exact ⟨ULift.up y, congrArg ULift.up hy⟩
  have : IsNoetherianRing A :=
    isNoetherianRing_of_ringEquiv (AdicCompletion I R) ULift.ringEquiv.symm
  let : Module.Flat A (limit.cone F).pt :=
    (flat_limit_and_tensor_limit_of_flat_quotients J F qmod hscalar hflat' htrans).1
  have : Module.Flat A (ULift.{u} (AdicCompletion I M)) :=
    Module.Flat.of_linearEquiv
      ((completionConeIsLimit I M).conePointUniqueUpToIso (limit.isLimit F)).toLinearEquiv
  exact Module.Flat.ulift_left_iff.mp (Module.Flat.ulift_right_iff.mp this)

/-- Let `R` be a commutative ring, `I ⊆ R` a finitely generated ideal and `M` an `R`-module. If
`R/I` is Noetherian, `M/IM` is flat over `R/I` and `Tor₁ᴿ(M, R/I) = 0`, then the `I`-adic
completion `R^∧` is a Noetherian ring and the `I`-adic completion `M^∧` is flat over `R^∧`. -/
@[stacks 0AGW, ega "0 10.2.3" "forward implication"]
theorem AdicCompletion.isNoetherianRing_and_flat_of_flat_quotient
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (hI : I.FG) (hRI : IsNoetherianRing (R ⧸ I))
    (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))))
    (htor : IsZero
      (((Tor (ModuleCat.{max u v} (ULift.{v} R)) 1).obj
        (ModuleCat.of (ULift.{v} R) (ULift.{u} M))).obj
        (ModuleCat.of (ULift.{v} R) (ULift.{v} (R ⧸ I))))) :
    IsNoetherianRing (AdicCompletion I R) ∧
      Module.Flat (AdicCompletion I R) (AdicCompletion I M) := by
  have := (completion_noetherian R I hRI hI).1
  exact ⟨this, adicCompletion_flat_of_flat_quotients I hI
    (flat_quotient_pow_of_isZero_tor I hflat htor)⟩

end

end CompletionFlat

end
