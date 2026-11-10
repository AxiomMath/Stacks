module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Nakayama
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.Projective.OfQuotient
public import StacksFrontier.RingTheory.Etale.LiftIdempotentsAndModules
public import StacksFrontier.RingTheory.Henselian.Pair.Criteria

@[expose] public section

/-!
# Finite projective modules over a henselian pair

For a henselian pair `(A, I)`, reduction modulo `I` is a bijection on isomorphism classes of
finite projective modules: every finite projective `A ⧸ I`-module lifts, and two finite
projective `A`-modules are isomorphic exactly when their reductions are. Existence of the lift
comes from lifting a finite projective module along an étale base change and descending the
resulting étale algebra with the henselian lifting criterion; uniqueness is Nakayama together
with Orzech's property.

The same circle of ideas gives the limit statement: a compatible inverse system of finite flat
modules over a surjective inverse system of rings with locally nilpotent transition kernels has
finite projective limit, provided its first term is finite projective.

## Main results

* `henselianPair_finiteProjective_quotient_bijective`: reduction modulo the ideal of a henselian
  pair is a bijection on isomorphism classes of finite projective modules.
* `finiteProjective_limit_of_finiteFlat_of_isBaseChange`: the inverse limit of such a system of
  finite flat modules is finite projective and commutes with base change.

## References

* [Stacks: Tag 0D4A](https://stacks.math.columbia.edu/tag/0D4A)
* [Stacks: Tag 0D4B](https://stacks.math.columbia.edu/tag/0D4B)
-/

universe u v w

section FiniteProjectiveLift

open scoped TensorProduct

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- Reduction of a linear map modulo `I`, as a map of the `I`-reductions of source and target. -/
private noncomputable def inducedQuotientMap {R : Type*} [CommRing R] (I : Ideal R)
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    (M ⧸ I • (⊤ : Submodule R M)) →ₗ[R] (N ⧸ I • (⊤ : Submodule R N)) :=
  Submodule.mapQ _ _ f (by
    rw [Submodule.map_le_iff_le_comap.symm, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top)

private theorem surjective_of_surjective_comp_of_ker_le_smul
    {R P X Y : Type*} [CommRing R] [AddCommGroup P] [Module R P]
    [AddCommGroup X] [Module R X] [Module.Finite R X]
    [AddCommGroup Y] [Module R Y]
    (I : Ideal R) (hI : I ≤ Ideal.jacobson (⊥ : Ideal R))
    (p : P →ₗ[R] X) (d : X →ₗ[R] Y)
    (hk : LinearMap.ker d ≤ I • (⊤ : Submodule R X))
    (hp : Function.Surjective (d.comp p)) : Function.Surjective p := by
  rw [← LinearMap.range_eq_top]
  apply top_le_iff.mp
  apply Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hI
  intro x _
  obtain ⟨y, hy⟩ := hp (d x)
  have hxy : x - p y ∈ I • (⊤ : Submodule R X) := by
    apply hk
    change d (x - p y) = 0
    rw [map_sub, ← hy, LinearMap.comp_apply, sub_self]
  rw [show x = p y + (x - p y) by abel]
  exact Submodule.add_mem _ (Submodule.mem_sup_left ⟨y, rfl⟩)
    (Submodule.mem_sup_right hxy)

/-- A map from a projective module that is surjective modulo `I` and hits a finite module
surjectively modulo `I` exists, assuming `I` lies in the Jacobson radical. -/
private theorem exists_surjective_lift_of_surjective_quotient {R : Type*} [CommRing R]
    (I : Ideal R) (hI : I ≤ (⊥ : Ideal R).jacobson)
    {M N : Type*} [AddCommGroup M] [Module R M] [Module.Projective R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N]
    (e : (M ⧸ I • (⊤ : Submodule R M)) →ₗ[R] (N ⧸ I • (⊤ : Submodule R N)))
    (he : Function.Surjective e) :
    ∃ f : M →ₗ[R] N, Function.Surjective f := by
  obtain ⟨f, hf⟩ := Module.projective_lifting_property
    (Submodule.mkQ (I • (⊤ : Submodule R N))) (e ∘ₗ Submodule.mkQ (I • (⊤ : Submodule R M)))
    (Submodule.mkQ_surjective _)
  refine ⟨f, surjective_of_surjective_comp_of_ker_le_smul I hI f _
    (by rw [Submodule.ker_mkQ]) ?_⟩
  rw [hf]
  exact he.comp (Submodule.mkQ_surjective _)

private theorem quotient_linearEquiv_of_linearEquiv {R : Type*} [CommRing R] (I : Ideal R)
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) :
    Nonempty ((M ⧸ I • (⊤ : Submodule R M)) ≃ₗ[R ⧸ I]
      (N ⧸ I • (⊤ : Submodule R N))) := by
  let f := inducedQuotientMap I e.toLinearMap
  let g := inducedQuotientMap I e.symm.toLinearMap
  have hfg : f ∘ₗ g = LinearMap.id := by
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp [f, g, inducedQuotientMap]
  have hgf : g ∘ₗ f = LinearMap.id := by
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp [f, g, inducedQuotientMap]
  have hf : Function.Bijective f := by
    refine ⟨fun x y hxy => ?_, fun y => ⟨g y, ?_⟩⟩
    · simpa [← LinearMap.comp_apply, hgf] using congrArg g hxy
    · simp [← LinearMap.comp_apply, hfg]
  exact ⟨LinearEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
    (LinearEquiv.ofBijective f hf)⟩

private theorem linearEquiv_of_quotient_linearEquiv {R : Type*} [CommRing R] (I : Ideal R)
    (hI : I ≤ (⊥ : Ideal R).jacobson)
    {M N : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]
    (h : Nonempty ((M ⧸ I • (⊤ : Submodule R M)) ≃ₗ[R ⧸ I]
      (N ⧸ I • (⊤ : Submodule R N)))) : Nonempty (M ≃ₗ[R] N) := by
  obtain ⟨e⟩ := h
  obtain ⟨f, hfsurj⟩ := exists_surjective_lift_of_surjective_quotient I hI
    (e.restrictScalars R).toLinearMap (e.restrictScalars R).surjective
  obtain ⟨g, hgsurj⟩ := exists_surjective_lift_of_surjective_quotient I hI
    (e.symm.restrictScalars R).toLinearMap (e.symm.restrictScalars R).surjective
  have hcomp : Function.Bijective (g ∘ₗ f) :=
    OrzechProperty.bijective_of_surjective_endomorphism (g ∘ₗ f) (hgsurj.comp hfsurj)
  exact ⟨LinearEquiv.ofBijective f ⟨Function.Injective.of_comp hcomp.injective, hfsurj⟩⟩

private theorem exists_finiteProjective_lift {R : Type u} [CommRing R] (I : Ideal R)
    (hI : HenselianPair R I)
    (Pbar : Type v) [AddCommGroup Pbar] [Module (R ⧸ I) Pbar]
    [Module.Finite (R ⧸ I) Pbar] [Module.Projective (R ⧸ I) Pbar] :
    ∃ (P : Type (max u v)) (_ : AddCommGroup P) (_ : Module R P),
      Module.Finite R P ∧ Module.Projective R P ∧
        Nonempty ((P ⧸ I • (⊤ : Submodule R P)) ≃ₗ[R ⧸ I] Pbar) := by
  obtain ⟨A', _, _, _, hq, P', _, _, _, _, ⟨e⟩⟩ :=
    exists_etale_baseChange_finite_projective_lift I Pbar
  let J := I.map (algebraMap R A')
  let q : (R ⧸ I) →+* (A' ⧸ J) :=
    Ideal.quotientMap J (algebraMap R A') Ideal.le_comap_map
  let qe : (R ⧸ I) ≃+* (A' ⧸ J) := RingEquiv.ofBijective q hq
  let σ : A' →ₐ[R] R ⧸ I :=
    { toRingHom := qe.symm.toRingHom.comp (Ideal.Quotient.mk J)
      commutes' := fun r => by
        apply qe.injective
        simp [qe, q, J] }
  have hlift := (henselianPair_tfae R I).out 1 2 |>.mp hI
  obtain ⟨τ, hτ⟩ := hlift A' σ
  let : Algebra A' R := τ.toRingHom.toAlgebra
  let : IsScalarTower A' R (R ⧸ I) := ⟨fun a r x => by
    induction x using Submodule.Quotient.induction_on
    change Ideal.Quotient.mk I ((τ a * r) * _) = Ideal.Quotient.mk I (τ a * (r * _))
    rw [mul_assoc]⟩
  let : Algebra (R ⧸ I) (A' ⧸ J) := qe.toRingHom.toAlgebra
  let qlin : (R ⧸ I) ≃ₗ[A'] (A' ⧸ J) :=
    { qe with
      map_smul' := fun a x => by
        induction x using Submodule.Quotient.induction_on
        change qe (Ideal.Quotient.mk I (τ a * _)) = Ideal.Quotient.mk J (a * _)
        simp only [map_mul]
        rw [show Ideal.Quotient.mk I (τ a) = σ a from DFunLike.congr_fun hτ a,
          show qe (σ a) = Ideal.Quotient.mk J a from qe.apply_symm_apply _]
        rfl }
  let P := TensorProduct A' R P'
  refine ⟨P, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  let red : (P ⧸ I • (⊤ : Submodule R P)) ≃ₗ[R ⧸ I] (R ⧸ I) ⊗[R] P :=
    (LinearEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
      (TensorProduct.quotTensorEquivQuotSMul P I)).symm
  let cancel : (R ⧸ I) ⊗[R] P ≃ₗ[R ⧸ I] (R ⧸ I) ⊗[A'] P' :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange A' R (R ⧸ I) (R ⧸ I) P'
  let changeRing : (R ⧸ I) ⊗[A'] P' ≃ₛₗ[(qe : (R ⧸ I) →+* (A' ⧸ J))]
      (A' ⧸ J) ⊗[A'] P' :=
    { TensorProduct.congr qlin (LinearEquiv.refl A' P') with
      map_smul' := fun c x => by
        change (TensorProduct.congr qlin (LinearEquiv.refl A' P')) (c • x) =
          qe c • (TensorProduct.congr qlin (LinearEquiv.refl A' P')) x
        induction x with
        | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]
        | tmul x y =>
            rw [TensorProduct.smul_tmul', TensorProduct.congr_tmul,
              TensorProduct.congr_tmul, TensorProduct.smul_tmul']
            change qe (c * x) ⊗ₜ[A'] y = (qe c * qe x) ⊗ₜ[A'] y
            rw [map_mul] }
  exact ⟨red.trans (cancel.trans (changeRing.trans e.symm))⟩

/-- **Stacks 0D4A.** Reduction modulo the ideal of a henselian pair induces a bijection on
isomorphism classes of finite projective modules. Concretely, every finite projective module
over the quotient lifts, and two finite projective modules lift the same isomorphism class
exactly when they were already isomorphic. -/
@[stacks 0D4A]
theorem henselianPair_finiteProjective_quotient_bijective
    {R : Type u} [CommRing R] (I : Ideal R) (hI : HenselianPair R I) :
    (∀ (Pbar : Type v) [AddCommGroup Pbar] [Module (R ⧸ I) Pbar]
        [Module.Finite (R ⧸ I) Pbar] [Module.Projective (R ⧸ I) Pbar],
      ∃ (P : Type (max u v)) (_ : AddCommGroup P) (_ : Module R P),
        Module.Finite R P ∧ Module.Projective R P ∧
          Nonempty ((P ⧸ (I • (⊤ : Submodule R P))) ≃ₗ[R ⧸ I] Pbar)) ∧
    (∀ (P₁ : Type v) [AddCommGroup P₁] [Module R P₁]
        [Module.Finite R P₁] [Module.Projective R P₁]
        (P₂ : Type w) [AddCommGroup P₂] [Module R P₂]
        [Module.Finite R P₂] [Module.Projective R P₂],
      Nonempty
          ((P₁ ⧸ (I • (⊤ : Submodule R P₁))) ≃ₗ[R ⧸ I]
            (P₂ ⧸ (I • (⊤ : Submodule R P₂)))) ↔
        Nonempty (P₁ ≃ₗ[R] P₂)) :=
  ⟨fun Pbar => exists_finiteProjective_lift I hI Pbar, fun _ _ _ _ _ _ _ _ _ _ =>
    ⟨linearEquiv_of_quotient_linearEquiv I hI.1,
      fun ⟨e⟩ => quotient_linearEquiv_of_linearEquiv I e⟩⟩

end FiniteProjectiveLift

section InverseLimit

open CategoryTheory CategoryTheory.Limits TensorProduct

private theorem surjective_of_isBaseChange
    {R S X Y : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    [AddCommMonoid X] [Module R X] [AddCommMonoid Y] [Module R Y] [Module S Y]
    [IsScalarTower R S Y] (d : X →ₗ[R] Y) (h : IsBaseChange S d)
    (hs : Function.Surjective (algebraMap R S)) : Function.Surjective d := by
  have he : Function.Surjective (fun x : X => h.equiv (1 ⊗ₜ[R] x)) :=
    h.equiv.surjective.comp (TensorProduct.mk_surjective R X S hs)
  simpa only [IsBaseChange.equiv_tmul, one_smul] using he

private theorem isBaseChange_of_retract
    {R S X Y P Q : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    [AddCommMonoid X] [Module R X] [AddCommMonoid Y] [Module R Y] [Module S Y]
    [IsScalarTower R S Y] [AddCommMonoid P] [Module R P]
    [AddCommMonoid Q] [Module R Q] [Module S Q] [IsScalarTower R S Q]
    (f : X →ₗ[R] Y) (g : P →ₗ[R] Q) (hg : IsBaseChange S g)
    (p : P →ₗ[R] X) (i : X →ₗ[R] P) (p' : Q →ₗ[S] Y) (i' : Y →ₗ[S] Q)
    (hp : p.comp i = LinearMap.id) (hp' : p'.comp i' = LinearMap.id)
    (hf : f.comp p = (p'.restrictScalars R).comp g)
    (hi : (i'.restrictScalars R).comp f = g.comp i) : IsBaseChange S f := by
  apply IsBaseChange.of_lift_unique
  intro T _ _ _ _ a
  refine ⟨(hg.lift (a.comp p)).comp i', ?_, ?_⟩
  · ext x
    change hg.lift (a.comp p) (i' (f x)) = a x
    rw [show i' (f x) = g (i x) from LinearMap.congr_fun hi x,
      IsBaseChange.lift_eq]
    change a (p (i x)) = a x
    rw [show p (i x) = x from LinearMap.congr_fun hp x]
  · intro b hb
    have hb' : b.comp p' = hg.lift (a.comp p) := by
      apply hg.algHom_ext
      intro x
      change b (p' (g x)) = hg.lift (a.comp p) (g x)
      rw [← show f (p x) = p' (g x) from LinearMap.congr_fun hf x,
        IsBaseChange.lift_eq]
      exact LinearMap.congr_fun hb (p x)
    ext x
    change b x = hg.lift (a.comp p) (i' x)
    rw [← hb']
    change b x = b (p' (i' x))
    rw [show p' (i' x) = x from LinearMap.congr_fun hp' x]

private theorem quotient_equiv_of_isBaseChange
    {R S X Y : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] [Module S Y]
    [IsScalarTower R S Y] (d : X →ₗ[R] Y) (h : IsBaseChange S d)
    (hs : Function.Surjective (algebraMap R S)) :
    ∃ e : (X ⧸ (RingHom.ker (algebraMap R S) • (⊤ : Submodule R X))) ≃ₗ[R] Y,
      ∀ x, e (Submodule.Quotient.mk x) = d x := by
  let eR : (R ⧸ RingHom.ker (algebraMap R S)) ≃ₐ[R] S :=
    AlgEquiv.ofRingEquiv (RingHom.quotientKerEquivOfSurjective_apply_mk hs)
  refine ⟨(quotTensorEquivQuotSMul X _).symm ≪≫ₗ
    TensorProduct.congr eR.toLinearEquiv (LinearEquiv.refl R X) ≪≫ₗ
      h.equiv.restrictScalars R, ?_⟩
  intro x
  simp [IsBaseChange.equiv_tmul]

private theorem ker_eq_smul_of_isBaseChange
    {R S X Y : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] [Module S Y]
    [IsScalarTower R S Y] (d : X →ₗ[R] Y) (h : IsBaseChange S d)
    (hs : Function.Surjective (algebraMap R S)) :
    LinearMap.ker d = RingHom.ker (algebraMap R S) • (⊤ : Submodule R X) := by
  obtain ⟨e, he⟩ := quotient_equiv_of_isBaseChange d h hs
  ext x
  rw [LinearMap.mem_ker, ← he, ← e.map_zero, e.injective.eq_iff,
    Submodule.Quotient.mk_eq_zero]

private theorem projective_quotient_of_isBaseChange
    {R S X Y : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] [Module S Y]
    [IsScalarTower R S Y] [Module.Projective S Y]
    (d : X →ₗ[R] Y) (h : IsBaseChange S d)
    (hs : Function.Surjective (algebraMap R S)) :
    Module.Projective (R ⧸ RingHom.ker (algebraMap R S))
      (X ⧸ (RingHom.ker (algebraMap R S) • (⊤ : Submodule R X))) := by
  obtain ⟨e, he⟩ := quotient_equiv_of_isBaseChange d h hs
  let er := RingHom.quotientKerEquivOfSurjective hs
  have := RingHomInvPair.of_ringEquiv er
  have := RingHomInvPair.symm (er : (R ⧸ RingHom.ker (algebraMap R S)) →+* S)
    (er.symm : S →+* (R ⧸ RingHom.ker (algebraMap R S)))
  let e' : (X ⧸ (RingHom.ker (algebraMap R S) • (⊤ : Submodule R X)))
      ≃ₛₗ[(er : (R ⧸ RingHom.ker (algebraMap R S)) →+* S)] Y :=
    { e.toAddEquiv with
      map_smul' := by
        intro r x
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := RingHom.ker (algebraMap R S)) r
        change e ((Ideal.Quotient.mk (RingHom.ker (algebraMap R S))) a • x) =
          er ((Ideal.Quotient.mk (RingHom.ker (algebraMap R S))) a) • e x
        rw [RingHom.quotientKerEquivOfSurjective_apply_mk]
        change e ((algebraMap R (R ⧸ RingHom.ker (algebraMap R S))) a • x) = _
        rw [IsScalarTower.algebraMap_smul, e.map_smul, IsScalarTower.algebraMap_smul] }
  exact Module.Projective.of_equiv e'.symm

private theorem exists_compatible_splitting
    {R X Y P Q : Type*} [CommRing R]
    [AddCommGroup X] [Module R X] [Module.Finite R X] [Module.Projective R X]
    [AddCommGroup Y] [Module R Y] [AddCommGroup P] [Module R P]
    [Module.Projective R P] [AddCommGroup Q] [Module R Q]
    (I : Ideal R) (hI : I ≤ Ideal.jacobson (⊥ : Ideal R))
    (d : X →ₗ[R] Y) (hd : Function.Surjective d)
    (hk : LinearMap.ker d ≤ I • (⊤ : Submodule R X))
    (g : P →ₗ[R] Q) (hg : Function.Surjective g)
    (p₀ : Q →ₗ[R] Y) (i₀ : Y →ₗ[R] Q) (h₀ : p₀.comp i₀ = LinearMap.id) :
    ∃ (p : P →ₗ[R] X) (i : X →ₗ[R] P), p.comp i = LinearMap.id ∧
      d.comp p = p₀.comp g ∧ g.comp i = i₀.comp d := by
  obtain ⟨p, hp⟩ := Module.projective_lifting_property d (p₀.comp g) hd
  obtain ⟨j, hj⟩ := Module.projective_lifting_property g (i₀.comp d) hg
  have hdpj : d.comp (p.comp j) = d := by
    rw [← LinearMap.comp_assoc, hp, LinearMap.comp_assoc, hj,
      ← LinearMap.comp_assoc, h₀, LinearMap.id_comp]
  have hsurj : Function.Surjective (p.comp j) :=
    surjective_of_surjective_comp_of_ker_le_smul I hI (p.comp j) d hk
      (by rwa [hdpj])
  let e := LinearEquiv.ofBijective (p.comp j)
    (OrzechProperty.bijective_of_surjective_endomorphism _ hsurj)
  refine ⟨p, j.comp e.symm.toLinearMap, ?_, hp, ?_⟩
  · ext x
    exact e.apply_symm_apply x
  · ext x
    change g (j (e.symm x)) = i₀ (d x)
    rw [show g (j (e.symm x)) = i₀ (d (e.symm x)) from
      LinearMap.congr_fun hj (e.symm x)]
    congr 1
    have hd' := LinearMap.congr_fun hdpj (e.symm x)
    change d (e (e.symm x)) = d (e.symm x) at hd'
    simpa only [e.apply_symm_apply] using hd'.symm

private theorem exists_tower_splitting
    (R : ℕ → Type u) [∀ n, CommRing (R n)]
    (X : ℕ → Type v) [∀ n, AddCommGroup (X n)] [∀ n, Module (R n) (X n)]
    (φ : ∀ n, R (n + 1) →+* R n)
    (d : ∀ n, let := Module.compHom (X n) (φ n); X (n + 1) →ₗ[R (n + 1)] X n)
    (hφ : ∀ n, Function.Surjective (φ n) ∧ RingHom.ker (φ n) ≤ nilradical (R (n + 1)))
    (hX : ∀ n, Module.Finite (R n) (X n) ∧ Module.Flat (R n) (X n))
    (h₀ : Module.Projective (R 0) (X 0))
    (hb : ∀ n,
      let := (φ n).toAlgebra
      ∃ e : R n ⊗[R (n + 1)] X (n + 1) ≃ₗ[R n] X n,
        ∀ a x, e (a ⊗ₜ[R (n + 1)] x) = a • d n x) :
    ∃ (r : ℕ) (p : ∀ n, (Fin r → R n) →ₗ[R n] X n)
      (i : ∀ n, X n →ₗ[R n] (Fin r → R n)),
      (∀ n, (p n).comp (i n) = LinearMap.id) ∧
      (∀ n x, d n (p (n + 1) x) = p n (fun j => φ n (x j))) ∧
      (∀ n x j, φ n (i (n + 1) x j) = i n (d n x) j) := by
  classical
  have hproj : ∀ n, Module.Projective (R n) (X n) := by
    intro n
    induction n with
    | zero => exact h₀
    | succ n hn =>
      let := (φ n).toAlgebra
      let := Module.compHom (X n) (φ n)
      let : IsScalarTower (R (n + 1)) (R n) (X n) :=
        IsScalarTower.of_algebraMap_smul fun _ _ => rfl
      have := hn
      have := (hX (n + 1)).1
      have := (hX (n + 1)).2
      obtain ⟨e, he⟩ := hb n
      have hd : IsBaseChange (R n) (d n) :=
        IsBaseChange.of_equiv e (fun x => by simpa using he 1 x)
      apply Module.projective_of_projective_quotient_of_le_jacobson
        (RingHom.ker (φ n)) ((hφ n).2.trans Ideal.radical_le_jacobson)
      exact projective_quotient_of_isBaseChange (d n) hd (hφ n).1
  have := (hX 0).1
  have := hproj 0
  obtain ⟨r, p₀, i₀, _, _, hp₀⟩ := Module.Finite.exists_comp_eq_id_of_projective (R 0) (X 0)
  let T := fun n => {s : ((Fin r → R n) →ₗ[R n] X n) ×
      (X n →ₗ[R n] (Fin r → R n)) // s.1.comp s.2 = LinearMap.id}
  have hstep : ∀ n (s : T n), ∃ t : T (n + 1),
      (∀ x, d n (t.val.1 x) = s.val.1 (fun j => φ n (x j))) ∧
      (∀ x j, φ n (t.val.2 x j) = s.val.2 (d n x) j) := by
    intro n s
    let := (φ n).toAlgebra
    let := Module.compHom (X n) (φ n)
    let : IsScalarTower (R (n + 1)) (R n) (X n) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    have := (hX (n + 1)).1
    have := hproj (n + 1)
    let g : (Fin r → R (n + 1)) →ₗ[R (n + 1)] (Fin r → R n) :=
      LinearMap.pi (fun j => (Algebra.linearMap (R (n + 1)) (R n)).comp (LinearMap.proj j))
    have hg : Function.Surjective g := by
      intro y
      choose z hz using fun j => (hφ n).1 (y j)
      exact ⟨z, funext hz⟩
    obtain ⟨e, he⟩ := hb n
    have hbc : IsBaseChange (R n) (d n) :=
      IsBaseChange.of_equiv e (fun x => by simpa using he 1 x)
    obtain ⟨p, i, hpi, hp, hi⟩ := exists_compatible_splitting
      (RingHom.ker (φ n)) ((hφ n).2.trans Ideal.radical_le_jacobson)
      (d n) (surjective_of_isBaseChange (d n) hbc (hφ n).1)
      (ker_eq_smul_of_isBaseChange (d n) hbc (hφ n).1).le g hg
      (s.val.1.restrictScalars (R (n + 1))) (s.val.2.restrictScalars (R (n + 1)))
      (LinearMap.ext fun x => LinearMap.congr_fun s.property x)
    exact ⟨⟨(p, i), hpi⟩, fun x => LinearMap.congr_fun hp x,
      fun x j => congrFun (LinearMap.congr_fun hi x) j⟩
  let step : ∀ n, T n → T (n + 1) := fun n s => (hstep n s).choose
  let s : ∀ n, T n := Nat.rec ⟨(p₀, i₀), hp₀⟩ step
  exact ⟨r, fun n => (s n).val.1, fun n => (s n).val.2, fun n => (s n).property,
    fun n => (hstep n (s n)).choose_spec.1, fun n => (hstep n (s n)).choose_spec.2⟩

private theorem sections_of_succ {F : ℕᵒᵖ ⥤ Type u}
    (x : ∀ n : ℕ, F.obj (.op n))
    (hx : ∀ n, F.map (homOfLE (Nat.le_succ n)).op (x (n + 1)) = x n) :
    (fun j : ℕᵒᵖ => x j.unop) ∈ F.sections := by
  have hle : ∀ n m (h : n ≤ m), F.map (homOfLE h).op (x m) = x n := by
    intro n m h
    induction h with
    | refl => simp
    | @step m h ih =>
      have hh : (homOfLE (Nat.le.step h)).op =
          (homOfLE (Nat.le_succ m)).op ≫ (homOfLE h).op := Subsingleton.elim _ _
      rw [hh, F.map_comp]
      change F.map (homOfLE h).op (F.map (homOfLE (Nat.le_succ m)).op (x (m + 1))) = x n
      rw [hx, ih]
  exact fun j k f => hle k.unop j.unop (leOfHom f.unop)

private theorem exists_limit_splitting
    (A : ℕᵒᵖ ⥤ CommRingCat.{u}) (c : Cone A) (hc : IsLimit c)
    (M : ℕᵒᵖ ⥤ ModuleCat.{v} c.pt)
    (moduleStructure : ∀ n : ℕ, Module (A.obj (.op n)) (M.obj (.op n)))
    (hscalar : ∀ n : ℕ,
      let := moduleStructure n
      let : Algebra c.pt (A.obj (.op n)) := (c.π.app (.op n)).hom.toAlgebra
      IsScalarTower c.pt (A.obj (.op n)) (M.obj (.op n)))
    (r : ℕ)
    (pₙ : ∀ n, let := moduleStructure n;
      (Fin r → A.obj (.op n)) →ₗ[A.obj (.op n)] M.obj (.op n))
    (iₙ : ∀ n, let := moduleStructure n;
      M.obj (.op n) →ₗ[A.obj (.op n)] (Fin r → A.obj (.op n)))
    (hsplit : ∀ n, let := moduleStructure n; (pₙ n).comp (iₙ n) = LinearMap.id)
    (hp : ∀ n x, M.map (homOfLE (Nat.le_succ n)).op (pₙ (n + 1) x) =
      pₙ n (fun j => A.map (homOfLE (Nat.le_succ n)).op (x j)))
    (hi : ∀ n x j, A.map (homOfLE (Nat.le_succ n)).op (iₙ (n + 1) x j) =
      iₙ n (M.map (homOfLE (Nat.le_succ n)).op x) j) :
    ∃ (p : (Fin r → c.pt) →ₗ[c.pt] (limit M : ModuleCat.{v} c.pt))
      (i : (limit M : ModuleCat.{v} c.pt) →ₗ[c.pt] (Fin r → c.pt)),
      p.comp i = LinearMap.id ∧
      (∀ n x, limit.π M (.op n) (p x) = pₙ n (fun j => c.π.app (.op n) (x j))) ∧
      (∀ n x j, c.π.app (.op n) (i x j) = iₙ n (limit.π M (.op n) x) j) := by
  classical
  let eA := Types.isLimitEquivSections (isLimitOfPreserves (forget CommRingCat) hc)
  let eM := Types.isLimitEquivSections
    (isLimitOfPreserves (forget (ModuleCat c.pt)) (limit.isLimit M))
  have extA : ∀ x y : c.pt, (∀ n : ℕ, c.π.app (.op n) x = c.π.app (.op n) y) → x = y :=
    fun x y h => eA.injective (Subtype.ext (funext fun n => h n.unop))
  have extM : ∀ x y : (limit M : ModuleCat.{v} c.pt),
      (∀ n : ℕ, limit.π M (.op n) x = limit.π M (.op n) y) → x = y :=
    fun x y h => eM.injective (Subtype.ext (funext fun n => h n.unop))
  let pf : (Fin r → c.pt) → (limit M : ModuleCat.{v} c.pt) := fun x =>
    eM.symm ⟨fun n => pₙ n.unop (fun j => c.π.app n (x j)), by
      apply sections_of_succ (F := M ⋙ forget (ModuleCat c.pt))
        (fun n => pₙ n (fun j => c.π.app (.op n) (x j)))
      intro n
      change M.map (homOfLE (Nat.le_succ n)).op
        (pₙ (n + 1) (fun j => c.π.app (.op (n + 1)) (x j))) = _
      rw [hp]
      congr 1
      funext j
      exact c.w_apply (homOfLE (Nat.le_succ n)).op (x j)⟩
  have hpf : ∀ n x, limit.π M (.op n) (pf x) =
      pₙ n (fun j => c.π.app (.op n) (x j)) :=
    fun n x => congrArg (fun s : (M ⋙ forget (ModuleCat c.pt)).sections => s.val (.op n))
      (eM.apply_symm_apply _)
  let ifn : (↑(limit M) : Type v) → (Fin r → c.pt) := fun x j =>
    eA.symm ⟨fun n => iₙ n.unop (limit.π M n x) j, by
      apply sections_of_succ (F := A ⋙ forget CommRingCat)
        (fun n => iₙ n (limit.π M (.op n) x) j)
      intro n
      change A.map (homOfLE (Nat.le_succ n)).op
        (iₙ (n + 1) (limit.π M (.op (n + 1)) x) j) = _
      rw [hi, limit.w_apply]⟩
  have hinf : ∀ n x j, c.π.app (.op n) (ifn x j) =
      iₙ n (limit.π M (.op n) x) j :=
    fun n x j => congrArg (fun s : (A ⋙ forget CommRingCat).sections => s.val (.op n))
      (eA.apply_symm_apply _)
  let p : (Fin r → c.pt) →ₗ[c.pt] (limit M : ModuleCat.{v} c.pt) :=
    { toFun := pf
      map_add' := by
        intro x y
        apply extM
        intro n
        let := moduleStructure n
        simp only [map_add, hpf, Pi.add_apply]
        exact (pₙ n).map_add _ _
      map_smul' := by
        intro a x
        apply extM
        intro n
        let := moduleStructure n
        let : Algebra c.pt (A.obj (.op n)) := (c.π.app (.op n)).hom.toAlgebra
        have := hscalar n
        simp only [map_smul, hpf, Pi.smul_apply]
        change pₙ n (fun j => (c.π.app (.op n)).hom (a * x j)) =
          a • pₙ n (fun j => c.π.app (.op n) (x j))
        simp only [map_mul]
        rw [← IsScalarTower.algebraMap_smul (A.obj (.op n)) a]
        exact (pₙ n).map_smul _ _ }
  let i : (limit M : ModuleCat.{v} c.pt) →ₗ[c.pt] (Fin r → c.pt) :=
    { toFun := ifn
      map_add' := by
        intro x y
        funext j
        apply extA
        intro n
        let := moduleStructure n
        simp only [Pi.add_apply, map_add, hinf]
      map_smul' := by
        intro a x
        funext j
        apply extA
        intro n
        let := moduleStructure n
        let : Algebra c.pt (A.obj (.op n)) := (c.π.app (.op n)).hom.toAlgebra
        have := hscalar n
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, hinf, map_smul]
        rw [← IsScalarTower.algebraMap_smul (A.obj (.op n)) a]
        exact congrFun ((iₙ n).map_smul ((c.π.app (.op n)).hom a) _) j }
  refine ⟨p, i, ?_, hpf, hinf⟩
  ext x
  apply extM
  intro n
  change limit.π M (.op n) (pf (ifn x)) = limit.π M (.op n) x
  simp only [hpf, hinf]
  exact LinearMap.congr_fun (hsplit n) _

/-- **Stacks 0D4B.** A compatible inverse system of finite flat modules over a surjective
inverse system of rings with locally nilpotent transition kernels has finite projective inverse
limit, provided its first term is finite projective. The limit commutes with base change to every
ring in the system. -/
@[stacks 0D4B, ega "IV 18.3.2.1" "(ii)"]
theorem finiteProjective_limit_of_finiteFlat_of_isBaseChange
    (A : ℕᵒᵖ ⥤ CommRingCat.{u}) (c : Cone A) (hc : IsLimit c)
    (M : ℕᵒᵖ ⥤ ModuleCat.{v} c.pt)
    (moduleStructure : ∀ n : ℕ, Module (A.obj (.op n)) (M.obj (.op n)))
    (hscalar : ∀ n : ℕ,
      letI := moduleStructure n
      letI : Algebra c.pt (A.obj (.op n)) := (c.π.app (.op n)).hom.toAlgebra
      IsScalarTower c.pt (A.obj (.op n)) (M.obj (.op n)))
    (d : ∀ n : ℕ,
      letI := moduleStructure (n + 1)
      letI := moduleStructure n
      ModuleCat.of (A.obj (.op (n + 1))) (M.obj (.op (n + 1))) ⟶
        (ModuleCat.restrictScalars (A.map (homOfLE (Nat.le_succ n)).op).hom).obj
          (ModuleCat.of (A.obj (.op n)) (M.obj (.op n))))
    (hd : ∀ (n : ℕ) (x : M.obj (.op (n + 1))),
      letI := moduleStructure (n + 1)
      letI := moduleStructure n
      d n x = M.map (homOfLE (Nat.le_succ n)).op x)
    (hA : ∀ n : ℕ,
      Function.Surjective (A.map (homOfLE (Nat.le_succ n)).op).hom ∧
        RingHom.ker (A.map (homOfLE (Nat.le_succ n)).op).hom ≤
          nilradical (A.obj (.op (n + 1))))
    (hfirst :
      letI := moduleStructure 0
      Module.Finite (A.obj (.op 0)) (M.obj (.op 0)) ∧
        Module.Projective (A.obj (.op 0)) (M.obj (.op 0)))
    (hflat : ∀ n : ℕ,
      letI := moduleStructure n
      Module.Finite (A.obj (.op n)) (M.obj (.op n)) ∧
        Module.Flat (A.obj (.op n)) (M.obj (.op n)))
    (hbaseChange : ∀ n : ℕ,
      letI := moduleStructure (n + 1)
      letI := moduleStructure n
      letI : Algebra (A.obj (.op (n + 1))) (A.obj (.op n)) :=
        (A.map (homOfLE (Nat.le_succ n)).op).hom.toAlgebra
      ∃ e : TensorProduct (A.obj (.op (n + 1))) (A.obj (.op n)) (M.obj (.op (n + 1)))
          ≃ₗ[A.obj (.op n)] M.obj (.op n),
        ∀ (a : A.obj (.op n)) (x : M.obj (.op (n + 1))),
          e (TensorProduct.tmul (A.obj (.op (n + 1))) a x) = a • d n x) :
    Module.Finite c.pt (limit M : ModuleCat.{v} c.pt) ∧
      Module.Projective c.pt (limit M : ModuleCat.{v} c.pt) ∧
      ∀ n : ℕ,
        letI := moduleStructure n
        letI : Algebra c.pt (A.obj (.op n)) := (c.π.app (.op n)).hom.toAlgebra
        ∃ e : TensorProduct c.pt (A.obj (.op n)) (limit M : ModuleCat.{v} c.pt)
            ≃ₗ[A.obj (.op n)] M.obj (.op n),
          ∀ (a : A.obj (.op n)) (x : (limit M : ModuleCat.{v} c.pt)),
            e (TensorProduct.tmul c.pt a x) = a • (limit.π M (.op n) x) := by
  classical
  let (n : ℕ) : Module (A.obj (.op n)) (M.obj (.op n)) := moduleStructure n
  obtain ⟨r, pₙ, iₙ, hsplit, hp, hi⟩ := exists_tower_splitting
    (fun n => A.obj (.op n)) (fun n => M.obj (.op n))
    (fun n => (A.map (homOfLE (Nat.le_succ n)).op).hom)
    (fun n => (d n).hom) hA hflat hfirst.2 hbaseChange
  obtain ⟨p, i, hpi, hpp, hii⟩ := exists_limit_splitting A c hc M moduleStructure
    hscalar r pₙ iₙ hsplit
    (fun n x => (hd n (pₙ (n + 1) x)).symm.trans (hp n x))
    (fun n x j => (hi n x j).trans (congrArg (fun y => iₙ n y j) (hd n x)))
  refine ⟨Module.Finite.of_surjective p (fun x => ⟨i x, LinearMap.congr_fun hpi x⟩),
    Module.Projective.of_split i p hpi, ?_⟩
  intro n
  let : Algebra c.pt (A.obj (.op n)) := (c.π.app (.op n)).hom.toAlgebra
  have := hscalar n
  let g : (Fin r → c.pt) →ₗ[c.pt] (Fin r → A.obj (.op n)) :=
    LinearMap.pi (fun j => (Algebra.linearMap c.pt (A.obj (.op n))).comp (LinearMap.proj j))
  have hg : IsBaseChange (A.obj (.op n)) g :=
    IsBaseChange.pi (fun _ : Fin r => Algebra.linearMap c.pt (A.obj (.op n)))
      (fun _ => IsBaseChange.linearMap _ _)
  have hf : IsBaseChange (A.obj (.op n)) (limit.π M (.op n)).hom :=
    isBaseChange_of_retract (limit.π M (.op n)).hom g hg p i (pₙ n) (iₙ n) hpi
      (hsplit n) (LinearMap.ext (hpp n))
      (LinearMap.ext fun x => funext fun j => (hii n x j).symm)
  exact ⟨hf.equiv, hf.equiv_tmul⟩

end InverseLimit

end
