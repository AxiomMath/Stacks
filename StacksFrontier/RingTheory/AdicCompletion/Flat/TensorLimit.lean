module

public import StacksFrontier.RingTheory.AdicCompletion.Flat.LimitExactness
import all StacksFrontier.RingTheory.AdicCompletion.Flat.LimitExactness

/-!
# Flatness of limits of towers flat over `R ⧸ Iⁿ`

For `R` Noetherian and a tower `(M_n)` of `R`-modules with surjective transition maps and `M_n`
flat over `R/Iⁿ`, this file proves that `lim M_n` is flat over `R` and that
`Q ⊗_R lim M_n → lim (Q ⊗_R M_n)` is an isomorphism for every finite `R`-module `Q`.

## Main results

* `flat_limit_and_tensor_limit_of_flat_quotients`
-/

@[expose] public section

universe u v

section FlatLimit

open CategoryTheory CategoryTheory.Limits

open TensorProduct

private theorem flat_kernel_lift {S U X Y : Type*} [CommRing S]
    [AddCommGroup U] [Module S U] [Module.Flat S U]
    [AddCommGroup X] [Module S X] [AddCommGroup Y] [Module S Y]
    (f : X →ₗ[S] Y) (w : U ⊗[S] X) (hw : f.lTensor U w = 0) :
    ∃ t : U ⊗[S] f.ker, f.ker.subtype.lTensor U t = w :=
  (Module.Flat.lTensor_exact U (LinearMap.exact_subtype_ker_map f) w).mp hw

/-- Let `U` be flat over `A ⧸ J`, let `K ⊆ P` satisfy `K ⊓ J • ⊤ ≤ L • K`, and let `L`
annihilate `V`. Then every element of `K ⊗ U` in the kernel of `K ⊗ U → P ⊗ U` maps to zero under
`K ⊗ g : K ⊗ U → K ⊗ V`. -/
private theorem tensor_subtype_kernel_transition_eq_zero
    {A P U V : Type*} [CommRing A]
    [AddCommGroup P] [Module A P] [AddCommGroup U] [Module A U]
    [AddCommGroup V] [Module A V]
    (J L : Ideal A) (K : Submodule A P)
    [Module (A ⧸ J) U] [IsScalarTower A (A ⧸ J) U] [Module.Flat (A ⧸ J) U]
    (hAR : K ⊓ J • ⊤ ≤ L • K)
    (hV : ∀ a ∈ L, ∀ v : V, a • v = 0) (g : U →ₗ[A] V)
    (z : K ⊗[A] U) (hz : K.subtype.rTensor U z = 0) :
    g.lTensor K z = 0 := by
  let S := A ⧸ J
  let f := K.subtype.baseChange S
  let eK := AlgebraTensorModule.cancelBaseChange A S S U K
  let eP := AlgebraTensorModule.cancelBaseChange A S S U P
  let w := eK.symm (TensorProduct.comm A K U z)
  have hnat : K.subtype.lTensor U ∘ₗ eK.toLinearMap.restrictScalars A =
      eP.toLinearMap.restrictScalars A ∘ₗ (f.lTensor U).restrictScalars A := by
    refine LinearMap.ext fun t => ?_
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    | tmul a b =>
      induction b using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simpa only [tmul_add, map_add] using congrArg₂ (· + ·) hx hy
      | tmul b c => simp [eK, eP, f]
  have hw : f.lTensor U w = 0 := by
    apply eP.injective
    rw [map_zero]
    show eP (f.lTensor U w) = 0
    have hn := congrArg (fun t => t w) hnat
    change K.subtype.lTensor U (eK w) = eP (f.lTensor U w) at hn
    rw [← hn]
    simp only [w, LinearEquiv.apply_symm_apply]
    have hn : K.subtype.lTensor U ∘ₗ (TensorProduct.comm A K U).toLinearMap =
        (TensorProduct.comm A P U).toLinearMap ∘ₗ K.subtype.rTensor U := by
      ext a b
      rfl
    simpa [hz] using congrArg (fun t => t z) hn
  obtain ⟨t, ht⟩ := flat_kernel_lift f w hw
  have hzero : ∀ t : U ⊗[S] LinearMap.ker f,
      g.rTensor K (eK ((LinearMap.ker f).subtype.lTensor U t)) = 0 := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [map_add, hx, hy]
    | tmul a b =>
      obtain ⟨q, hq⟩ := (TensorProduct.quotTensorEquivQuotSMul K J).symm.surjective b.val
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      have hb : b.val = (1 : S) ⊗ₜ[A] x := by
        simpa using hq.symm
      have hxp : (x : P) ∈ J • (⊤ : Submodule A P) := by
        have hh := b.property
        change f b.val = 0 at hh
        rw [hb] at hh
        have hh' := congrArg (TensorProduct.quotTensorEquivQuotSMul P J) hh
        change (TensorProduct.quotTensorEquivQuotSMul P J)
          ((1 : A ⧸ J) ⊗ₜ[A] (x : P)) = _ at hh'
        rwa [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, map_zero,
          Submodule.Quotient.mk_eq_zero] at hh'
      have hxK : x ∈ L • (⊤ : Submodule A K) := by
        have hm : (L • (⊤ : Submodule A K)).map K.subtype = L • K := by
          rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]
        have hx := hAR ⟨x.property, hxp⟩
        rw [← hm] at hx
        obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp hx
        exact K.injective_subtype hyx ▸ hy
      dsimp only [eK]
      simp only [LinearMap.lTensor_tmul, Submodule.subtype_apply, hb,
        AlgebraTensorModule.cancelBaseChange_tmul, one_smul, LinearMap.rTensor_tmul]
      show g a ⊗ₜ[A] x = 0
      refine Submodule.smul_induction_on hxK ?_ ?_
      · intro r hr x _
        rw [← TensorProduct.smul_tmul, hV r hr, zero_tmul]
      · intro x y hx hy
        rw [tmul_add, hx, hy, add_zero]
  have hzw : g.rTensor K (TensorProduct.comm A K U z) = 0 := by
    simpa only [ht, w, LinearEquiv.apply_symm_apply] using hzero t
  apply (TensorProduct.comm A K V).injective
  rw [map_zero]
  have hn : (TensorProduct.comm A K V).toLinearMap ∘ₗ g.lTensor K =
      g.rTensor K ∘ₗ (TensorProduct.comm A K U).toLinearMap := by
    ext a b
    rfl
  exact (congrArg (fun t => t z) hn).trans hzw

/-- The map of tensor towers induced by a map of the fixed factors. -/
private abbrev tensorTowerMap {A : Type u} [CommRing A]
    (M : ℕᵒᵖ ⥤ ModuleCat.{u} A) {P Q : ModuleCat.{u} A} (f : P ⟶ Q) :
    tensorTower P M ⟶ tensorTower Q M :=
  Functor.whiskerLeft M ((MonoidalCategory.tensoringLeft (ModuleCat.{u} A)).map f)

/-- The canonical comparison map `Q ⊗ lim M → lim (Q ⊗ M)`. -/
private noncomputable abbrev tensorComparison {A : Type u} [CommRing A]
    (M : ℕᵒᵖ ⥤ ModuleCat.{u} A) (Q : ModuleCat.{u} A) :=
  limit.post M ((MonoidalCategory.tensoringLeft (ModuleCat.{u} A)).obj Q)

private theorem tensorComparison_π {A : Type u} [CommRing A]
    (M : ℕᵒᵖ ⥤ ModuleCat.{u} A) (Q : ModuleCat.{u} A) (i : ℕᵒᵖ)
    (x : Q ⊗[A] (limit M : ModuleCat.{u} A)) :
    (limit.π (tensorTower Q M) i) (tensorComparison M Q x) =
      (limit.π M i).hom.lTensor Q x :=
  congrArg (fun f => f x)
    (limit.post_π M ((MonoidalCategory.tensoringLeft (ModuleCat.{u} A)).obj Q) i)

private theorem tensorComparison_natural {A : Type u} [CommRing A]
    (M : ℕᵒᵖ ⥤ ModuleCat.{u} A) {P Q : ModuleCat.{u} A} (f : P ⟶ Q) :
    ModuleCat.ofHom (f.hom.rTensor (limit M : ModuleCat.{u} A)) ≫
        tensorComparison M Q =
      tensorComparison M P ≫ limMap (tensorTowerMap M f) := by
  apply limit.hom_ext
  intro i
  dsimp only [tensorComparison]
  rw [Category.assoc, Category.assoc, limit.post_π, limMap_π, ← Category.assoc,
    limit.post_π]
  exact (((MonoidalCategory.tensoringLeft (ModuleCat.{u} A)).map f).naturality
    (limit.π M i)).symm

private theorem tensorComparison_natural_apply {A : Type u} [CommRing A]
    (M : ℕᵒᵖ ⥤ ModuleCat.{u} A) {P Q : ModuleCat.{u} A} (f : P ⟶ Q)
    (x : P ⊗[A] (limit M : ModuleCat.{u} A)) :
    tensorComparison M Q (f.hom.rTensor (limit M : ModuleCat.{u} A) x) =
      limMap (tensorTowerMap M f) (tensorComparison M P x) :=
  congrArg (fun g => g x) (tensorComparison_natural M f)

/-- Tensoring a surjection with `M_i` is exact together with its kernel inclusion. -/
private theorem tensorTowerMap_ker_exact {A : Type u} [CommRing A]
    (M : ℕᵒᵖ ⥤ ModuleCat.{u} A) {P Q : ModuleCat.{u} A} (q : P ⟶ Q)
    (hq : Function.Surjective q) (i : ℕᵒᵖ) :
    Function.Exact ((tensorTowerMap M (ModuleCat.ofHom q.hom.ker.subtype)).app i)
      ((tensorTowerMap M q).app i) :=
  _root_.rTensor_exact (M.obj i) (LinearMap.exact_subtype_ker_map q.hom) hq

/-- The kernel of a tensor inclusion is a pro-zero tower. -/
private theorem tensorTower_subtype_prozero_kernel
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (M : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (quotientModule : ∀ n : ℕ, Module (A ⧸ I ^ n) (M.obj (.op n)))
    (hscalar : ∀ n : ℕ, letI := quotientModule n
      IsScalarTower A (A ⧸ I ^ n) (M.obj (.op n)))
    (hflat : ∀ n : ℕ, letI := quotientModule n
      Module.Flat (A ⧸ I ^ n) (M.obj (.op n)))
    (P : ModuleCat.{u} A) [Module.Finite A P] (K : Submodule A P) :
    ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m),
      ∀ x : (tensorTower (ModuleCat.of A K) M).obj (.op m),
        (tensorTowerMap M (ModuleCat.ofHom K.subtype)).app (.op m) x = 0 →
        (tensorTower (ModuleCat.of A K) M).map (homOfLE h).op x = 0 := by
  obtain ⟨c, hc⟩ := I.exists_pow_inf_eq_pow_smul K
  intro n
  refine ⟨n + c, Nat.le_add_right _ _, fun x hx => ?_⟩
  let := quotientModule (n + c)
  let := hscalar (n + c)
  let := hflat (n + c)
  apply tensor_subtype_kernel_transition_eq_zero (I ^ (n + c)) (I ^ n) K
    (g := (M.map (homOfLE (Nat.le_add_right n c)).op).hom) (z := x) (hz := hx)
  · rw [inf_comm, hc (n + c) (by omega), Nat.add_sub_cancel]
    exact Submodule.smul_mono le_rfl inf_le_right
  · intro a ha v
    let := quotientModule n
    let := hscalar n
    have hz : algebraMap A (A ⧸ I ^ n) a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ha
    rw [← IsScalarTower.algebraMap_smul (A ⧸ I ^ n) a v, hz, zero_smul]

/-- Tensor inclusions induce injections on limits. -/
private theorem limMap_tensor_subtype_injective
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (M : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (quotientModule : ∀ n : ℕ, Module (A ⧸ I ^ n) (M.obj (.op n)))
    (hscalar : ∀ n : ℕ, letI := quotientModule n
      IsScalarTower A (A ⧸ I ^ n) (M.obj (.op n)))
    (hflat : ∀ n : ℕ, letI := quotientModule n
      Module.Flat (A ⧸ I ^ n) (M.obj (.op n)))
    (P : ModuleCat.{u} A) [Module.Finite A P] (K : Submodule A P) :
    Function.Injective (limMap (tensorTowerMap M (ModuleCat.ofHom K.subtype))) :=
  limMap_injective_of_prozero_kernel _
    (tensorTower_subtype_prozero_kernel I M quotientModule hscalar hflat P K)

/-- Finite free tensor products commute with inverse limits, with the canonical map. -/
private theorem finiteFree_tensorComparison_bijective
    {A : Type u} [CommRing A] (M : ℕᵒᵖ ⥤ ModuleCat.{u} A) (r : ℕ) :
    Function.Bijective (tensorComparison M (ModuleCat.of A (Fin r → A))) := by
  let F := ModuleCat.of A (Fin r → A)
  let T := tensorTower F M
  have hcoord (i : ℕᵒᵖ) (z : F ⊗[A] (limit M : ModuleCat.{u} A)) (j : Fin r) :
      finiteFreeTensorEquiv r (M.obj i) ((limit.π T i) (tensorComparison M F z)) j =
        (limit.π M i) (finiteFreeTensorEquiv r (limit M) z j) := by
    rw [tensorComparison_π, finiteFreeTensorEquiv_natural]
  constructor
  · intro x y hxy
    apply (finiteFreeTensorEquiv r (limit M)).injective
    funext j
    apply Concrete.limit_ext M
    intro i
    rw [← hcoord, ← hcoord, hxy]
  · intro y
    let τ (j : Fin r) : (M ⋙ forget (ModuleCat.{u} A)).sections :=
      ⟨fun i => finiteFreeTensorEquiv r (M.obj i) ((limit.π T i) y) j, by
        intro i k f
        have hn := finiteFreeTensorEquiv_natural r (M.obj i) (M.obj k) (M.map f)
          ((limit.π T i) y)
        have hw := congrArg (fun t : (limit T : ModuleCat.{u} A) ⟶ T.obj k => t y)
          (limit.w T f)
        show (M.map f) (finiteFreeTensorEquiv r (M.obj i) ((limit.π T i) y) j) = _
        rw [← congrFun hn j]
        show finiteFreeTensorEquiv r (M.obj k) ((T.map f) ((limit.π T i) y)) j = _
        change (T.map f) ((limit.π T i) y) = (limit.π T k) y at hw
        rw [hw]⟩
    let e := Types.isLimitEquivSections
      (isLimitOfPreserves (forget (ModuleCat.{u} A)) (limit.isLimit M))
    let x : Fin r → (limit M : ModuleCat.{u} A) := fun j => e.symm (τ j)
    refine ⟨(finiteFreeTensorEquiv r (limit M)).symm x, ?_⟩
    apply Concrete.limit_ext T
    intro i
    apply (finiteFreeTensorEquiv r (M.obj i)).injective
    funext j
    rw [hcoord, LinearEquiv.apply_symm_apply]
    have h := Types.isLimitEquivSections_symm_apply
      (isLimitOfPreserves (forget (ModuleCat.{u} A)) (limit.isLimit M)) (τ j) i
    exact h

/-- For a surjection `q : P → Q`, the induced map `lim (P ⊗ M) → lim (Q ⊗ M)` is surjective. -/
private theorem limMap_tensor_surjective
    {A : Type u} [CommRing A] (M : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hsurj : ∀ n : ℕ, Function.Surjective (M.map (homOfLE (Nat.le_succ n)).op))
    {P Q : ModuleCat.{u} A} (q : P ⟶ Q) (hq : Function.Surjective q) :
    Function.Surjective (limMap (tensorTowerMap M q)) := by
  let K := ModuleCat.of A (LinearMap.ker q.hom)
  let k : K ⟶ P := ModuleCat.ofHom q.hom.ker.subtype
  have hex := tensorTowerMap_ker_exact M q hq
  apply limMap_surjective_of_prozero_homology (tensorTowerMap M k)
    (tensorTowerMap M q)
  · intro i
    ext x
    exact (hex i).apply_apply_eq_zero x
  · exact tensorTower_successor_surjective K M hsurj
  · exact fun n => LinearMap.rTensor_surjective (M.obj (.op n)) hq
  · refine fun n => ⟨n, le_rfl, fun x hx => ?_⟩
    obtain ⟨y, hy⟩ := (hex (.op n) x).mp hx
    refine ⟨y, ?_⟩
    simpa only [show (homOfLE (le_refl n)).op = 𝟙 (Opposite.op n) from
      Subsingleton.elim _ _, (tensorTower P M).map_id, id_apply] using hy

/-- For a finite module, the canonical tensor comparison is surjective. -/
private theorem tensorComparison_surjective
    {A : Type u} [CommRing A] (M : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hsurj : ∀ n : ℕ, Function.Surjective (M.map (homOfLE (Nat.le_succ n)).op))
    (Q : ModuleCat.{u} A) [Module.Finite A Q] :
    Function.Surjective (tensorComparison M Q) := by
  obtain ⟨r, q, hq⟩ := Module.Finite.exists_fin' A Q
  let q' : ModuleCat.of A (Fin r → A) ⟶ Q := ModuleCat.ofHom q
  intro y
  obtain ⟨z, rfl⟩ := limMap_tensor_surjective M hsurj q' hq y
  obtain ⟨w, rfl⟩ := (finiteFree_tensorComparison_bijective M r).surjective z
  refine ⟨q.rTensor (limit M : ModuleCat.{u} A) w, ?_⟩
  exact tensorComparison_natural_apply M q' w

/-- Tensor presentations remain exact at the middle term after taking limits. -/
private theorem limMap_tensor_lift
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (M : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (quotientModule : ∀ n : ℕ, Module (A ⧸ I ^ n) (M.obj (.op n)))
    (hscalar : ∀ n : ℕ, letI := quotientModule n
      IsScalarTower A (A ⧸ I ^ n) (M.obj (.op n)))
    (hflat : ∀ n : ℕ, letI := quotientModule n
      Module.Flat (A ⧸ I ^ n) (M.obj (.op n)))
    (hsurj : ∀ n : ℕ, Function.Surjective (M.map (homOfLE (Nat.le_succ n)).op))
    {P Q : ModuleCat.{u} A} [Module.Finite A P]
    (q : P ⟶ Q) (hq : Function.Surjective q)
    (x : (limit (tensorTower P M) : ModuleCat.{u} A))
    (hx : limMap (tensorTowerMap M q) x = 0) :
    ∃ y : (limit (tensorTower (ModuleCat.of A q.hom.ker) M) : ModuleCat.{u} A),
      limMap (tensorTowerMap M (ModuleCat.ofHom q.hom.ker.subtype)) y = x := by
  let K := ModuleCat.of A q.hom.ker
  let k : K ⟶ P := ModuleCat.ofHom q.hom.ker.subtype
  have hex := tensorTowerMap_ker_exact M q hq
  apply limMap_lift_of_prozero_homology
    (0 : tensorTower K M ⟶ tensorTower K M) (tensorTowerMap M k) x
  · simp
  · exact tensorTower_successor_surjective K M hsurj
  · intro i
    apply (hex i _).mp
    have hh := congrArg (fun t => (limit.π (tensorTower Q M) i) t) hx
    have hn := congrArg (fun f => f x) (limMap_π (tensorTowerMap M q) i)
    exact hn.symm.trans (by simpa using hh)
  · intro n
    obtain ⟨m, h, hz⟩ :=
      tensorTower_subtype_prozero_kernel I M quotientModule hscalar hflat P q.hom.ker n
    exact ⟨m, h, fun t ht => ⟨0, by simpa using (hz t ht).symm⟩⟩

/-- Finite tensor products commute with the inverse limit of a surjective
system of modules flat over successive ideal-power quotients. -/
private theorem tensorComparison_bijective
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (M : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (quotientModule : ∀ n : ℕ, Module (A ⧸ I ^ n) (M.obj (.op n)))
    (hscalar : ∀ n : ℕ, letI := quotientModule n
      IsScalarTower A (A ⧸ I ^ n) (M.obj (.op n)))
    (hflat : ∀ n : ℕ, letI := quotientModule n
      Module.Flat (A ⧸ I ^ n) (M.obj (.op n)))
    (hsurj : ∀ n : ℕ, Function.Surjective (M.map (homOfLE (Nat.le_succ n)).op))
    (Q : ModuleCat.{u} A) [Module.Finite A Q] :
    Function.Bijective (tensorComparison M Q) := by
  refine ⟨?_, tensorComparison_surjective M hsurj Q⟩
  apply (tensorComparison M Q).hom.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨r, q, hq⟩ := Module.Finite.exists_fin' A Q
  let F := ModuleCat.of A (Fin r → A)
  let q' : F ⟶ Q := ModuleCat.ofHom q
  let K := ModuleCat.of A q.ker
  let k : K ⟶ F := ModuleCat.ofHom q.ker.subtype
  obtain ⟨z, rfl⟩ := LinearMap.rTensor_surjective (limit M : ModuleCat.{u} A) hq x
  have hqz : limMap (tensorTowerMap M q') (tensorComparison M F z) = 0 :=
    (tensorComparison_natural_apply M q' z).symm.trans hx
  obtain ⟨y, hy⟩ := limMap_tensor_lift I M quotientModule hscalar hflat hsurj q' hq _ hqz
  obtain ⟨w, rfl⟩ := tensorComparison_surjective M hsurj K y
  have hkw : k.hom.rTensor (limit M : ModuleCat.{u} A) w = z :=
    (finiteFree_tensorComparison_bijective M r).injective
      ((tensorComparison_natural_apply M k w).trans hy)
  rw [← hkw]
  exact (_root_.rTensor_exact (limit M : ModuleCat.{u} A)
    (LinearMap.exact_subtype_ker_map q) hq).apply_apply_eq_zero w

/-- Let `A` be a Noetherian ring and `I ⊆ A` an ideal. Let `(M_n)` be an inverse system of
`A`-modules such that each `M_n` is flat over `A ⧸ Iⁿ` (compatibly with its `A`-module structure)
and each transition map `M_{n+1} → M_n` is surjective. Then `M = lim M_n` is flat over `A`, and
for every finite `A`-module `Q` the canonical comparison map `Q ⊗_A lim M_n → lim (Q ⊗_A M_n)` is
an isomorphism. -/
@[stacks 0912]
theorem flat_limit_and_tensor_limit_of_flat_quotients
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (M : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (quotientModule : ∀ n : ℕ, Module (A ⧸ I ^ n) (M.obj (.op n)))
    (hscalar : ∀ n : ℕ, letI := quotientModule n
      IsScalarTower A (A ⧸ I ^ n) (M.obj (.op n)))
    (hflat : ∀ n : ℕ, letI := quotientModule n
      Module.Flat (A ⧸ I ^ n) (M.obj (.op n)))
    (hsurjective : ∀ n : ℕ, Function.Surjective
      (M.map (homOfLE (Nat.le_succ n)).op)) :
    Module.Flat A (limit M : ModuleCat.{u} A) ∧
      ∀ (Q : ModuleCat.{u} A), Module.Finite A Q →
        IsIso (limit.post M
          ((MonoidalCategory.tensoringLeft (ModuleCat.{u} A)).obj Q)) := by
  have hbij := tensorComparison_bijective I M quotientModule hscalar hflat hsurjective
  constructor
  · apply Module.Flat.iff_rTensor_injective.mpr
    intro K hK
    let P := ModuleCat.of A A
    let Q := ModuleCat.of A K
    let k : Q ⟶ P := ModuleCat.ofHom K.subtype
    have hlim := limMap_tensor_subtype_injective I M quotientModule hscalar hflat P K
    intro x y hxy
    apply (hbij Q).injective
    apply hlim
    exact (tensorComparison_natural_apply M k x).symm.trans
      ((congrArg (tensorComparison M P) hxy).trans (tensorComparison_natural_apply M k y))
  · intro Q hQ
    let := hQ
    exact (ConcreteCategory.isIso_iff_bijective _).mpr (hbij Q)

end FlatLimit

end
