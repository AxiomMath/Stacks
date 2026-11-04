module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.KTheory.Grothendieck.Defs
public import StacksFrontier.KTheory.Grothendieck.Product.BaseChange
public import StacksFrontier.KTheory.Grothendieck.Product.Factors

/-!
# The Grothendieck group `K'_0` of a product of two Noetherian rings

Stacks Project lemma `lemma-K0-product`:
Let `R = R_1 \times R_2` be a product of two commutative rings. Then
`K_0(R) = K_0(R_1) \times K_0(R_2)` and, when `R` is Noetherian,
`K'_0(R) = K'_0(R_1) \times K'_0(R_2)`.

This file proves the second half: `K'_0(R_1 \times R_2) = K'_0(R_1) \times K'_0(R_2)`
for Noetherian `R_1`, `R_2`, where `K'_0` is the Grothendieck group of *all*
finite modules. The three-step pattern (forward map by base change along the two
projections, backward map by restriction of scalars, both composites the
identity) is the one described in
`StacksFrontier.KTheory.Grothendieck.Product.K0`; the extra input here is that each
factor `R_i` is a flat `R`-algebra, so base change along `p_i` is exact and
therefore sends short exact sequences of finite modules to short exact
sequences.
-/

@[expose] public section

universe u

/-- **(A') Forward map, K'₀** (Noetherian case).  Base change along the two
projections gives a homomorphism `K'₀(R₁×R₂) → K'₀(R₁) × K'₀(R₂)` sending each
generator `[M]` to `([M⊗R₁],[M⊗R₂])`.

PROOF SKETCH: as for `K0_product_forward`, lift `M ↦ (baseChangeMk fst M.module,
baseChangeMk snd M.module)` through `FreeAbelianGroup.lift` then
`QuotientAddGroup.lift`, descending past `K0Sub R`.
Well-definedness now needs that base change `_ ⊗_R Rᵢ` sends the `K0Rel`
relations to relations: it preserves isomorphisms (`K0Rel.iso`) and, crucially,
sends a short exact sequence `0→M'→M→M''→0` to a short exact sequence
`0→M'⊗Rᵢ→M⊗Rᵢ→M''⊗Rᵢ→0` because `Rᵢ` is a FLAT `R`-algebra (it is a direct
factor of `R = R₁×R₂`, hence projective hence flat), so `_ ⊗_R Rᵢ` is exact
(`Module.Flat`, `TensorProduct` right-exactness + injectivity-preservation under
flatness).  Hence the images satisfy `K0Rel.ses` and the map descends. -/
theorem K0prime_product_forward (R1 R2 : Type u) [CommRing R1] [CommRing R2]
    [IsNoetherianRing R1] [IsNoetherianRing R2] :
    ∃ φ : K0prime (R1 × R2) →+ (K0prime R1 × K0prime R2),
      ∀ M : FGPres (R1 × R2),
        φ (K0prime.mk M) =
          ( K0prime.baseChangeMk (RingHom.fst R1 R2) M.module,
            K0prime.baseChangeMk (RingHom.snd R1 R2) M.module ) := by
  classical
  -- base-change of the relations is again a relation, in each component.
  -- We prove a single helper covering both projections `f : (R1×R2) →+* S`
  -- with `S` a flat finite `(R1×R2)`-algebra (a direct factor).
  have hbc : ∀ {S : Type u} [CommRing S] (f : (R1 × R2) →+* S)
      (_ : let : Algebra (R1 × R2) S := f.toAlgebra; Module.Finite (R1 × R2) S)
      (_ : let : Algebra (R1 × R2) S := f.toAlgebra; Module.Flat (R1 × R2) S),
      ∀ x : FreeAbelianGroup (FGPres (R1 × R2)),
        K0Rel (R1 × R2) x →
        (FreeAbelianGroup.lift (fun M : FGPres (R1 × R2) =>
            K0prime.baseChangeMk f M.module)) x = 0 := by
    intro S _ f hSfin hSflat x hx
    let : Algebra (R1 × R2) S := f.toAlgebra
    have : Module.Finite (R1 × R2) S := hSfin
    have : Module.Flat (R1 × R2) S := hSflat
    cases hx with
    | iso P Q e =>
      rw [map_sub]
      simp only [FreeAbelianGroup.lift_apply_of]
      rw [sub_eq_zero]
      -- baseChangeMk f P.module = baseChangeMk f Q.module
      show K0prime.mkModule S (TensorProduct (R1 × R2) S P.module)
        = K0prime.mkModule S (TensorProduct (R1 × R2) S Q.module)
      exact K0prime.mkModule_eq_of_iso _ _ (LinearEquiv.baseChange (R1 × R2) S P.module Q.module e)
    | ses P P' P'' f0 g0 hf0 hg0 he0 =>
      rw [map_sub, map_sub]
      simp only [FreeAbelianGroup.lift_apply_of]
      rw [sub_sub, sub_eq_zero]
      -- baseChangeMk f P.module = baseChangeMk f P'.module + baseChangeMk f P''.module
      show K0prime.mkModule S (TensorProduct (R1 × R2) S P.module)
        = K0prime.mkModule S (TensorProduct (R1 × R2) S P'.module)
          + K0prime.mkModule S (TensorProduct (R1 × R2) S P''.module)
      exact K0prime.mkModule_add_of_ses _ _ _
        (LinearMap.baseChange S f0) (LinearMap.baseChange S g0)
        (Module.Flat.lTensor_preserves_injective_linearMap (M := S) f0 hf0)
        (LinearMap.lTensor_surjective S hg0) (Module.Flat.lTensor_exact S he0)
  -- assemble the lifted map on the free abelian group
  let g : FreeAbelianGroup (FGPres (R1 × R2)) →+ (K0prime R1 × K0prime R2) :=
    (FreeAbelianGroup.lift fun M : FGPres (R1 × R2) =>
      K0prime.baseChangeMk (RingHom.fst R1 R2) M.module).prod
    (FreeAbelianGroup.lift fun M : FGPres (R1 × R2) =>
      K0prime.baseChangeMk (RingHom.snd R1 R2) M.module)
  -- the lifted map kills the relation generators
  have hker : AddSubgroup.closure {x | K0Rel (R1 × R2) x} ≤ g.ker := by
    rw [AddSubgroup.closure_le]
    rintro x hx
    -- prove componentwise
    exact Prod.ext
      (hbc (RingHom.fst R1 R2) (Prod.fst_finite R1 R2)
        (by let : Algebra (R1 × R2) R1 := (RingHom.fst R1 R2).toAlgebra
            have : Module.Projective (R1 × R2) R1 := Prod.fst_projective R1 R2
            exact Module.Flat.of_projective) x hx)
      (hbc (RingHom.snd R1 R2) (Prod.snd_finite R1 R2)
        (by let : Algebra (R1 × R2) R2 := (RingHom.snd R1 R2).toAlgebra
            have : Module.Projective (R1 × R2) R2 := Prod.snd_projective R1 R2
            exact Module.Flat.of_projective) x hx)
  exact ⟨QuotientAddGroup.lift _ g hker, fun _ => rfl⟩

/-- Restriction of scalars along `f` sends isomorphic finite `S`-modules to the same class. -/
private theorem restrictMk_eq_of_linearEquiv {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hfin : letI : Module R S := (f.toAlgebra).toModule; Module.Finite R S)
    {A B : Type u} [AddCommGroup A] [Module S A] [Module.Finite S A]
    [AddCommGroup B] [Module S B] [Module.Finite S B] (e : A ≃ₗ[S] B) :
    K0prime.restrictMk f hfin A = K0prime.restrictMk f hfin B := by
  let : Algebra R S := f.toAlgebra
  let : Module R A := Module.compHom A f
  let : Module R B := Module.compHom B f
  have : Module.Finite R S := hfin
  have : IsScalarTower R S A := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower R S B := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Finite R A := Module.Finite.trans S A
  have : Module.Finite R B := Module.Finite.trans S B
  exact K0prime.mkModule_eq_of_iso _ _ (e.restrictScalars R)

/-- Restriction of scalars along `f` descends to a homomorphism `K'₀(S) → K'₀(R)`. -/
private theorem exists_restrictMk_hom {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hfin : letI : Module R S := (f.toAlgebra).toModule; Module.Finite R S) :
    ∃ ψ : K0prime S →+ K0prime R,
      ∀ N : FGPres S, ψ (K0prime.mk N) = K0prime.restrictMk f hfin N.module := by
  classical
  let : Algebra R S := f.toAlgebra
  have : Module.Finite R S := hfin
  let g : FreeAbelianGroup (FGPres S) →+ K0prime R :=
    FreeAbelianGroup.lift fun N : FGPres S => K0prime.restrictMk f hfin N.module
  refine ⟨QuotientAddGroup.lift _ g ?_, fun _ => rfl⟩
  rw [K0Sub, AddSubgroup.closure_le]
  rintro x hx
  show g x = 0
  cases hx with
  | iso P Q e =>
    rw [map_sub, sub_eq_zero]
    exact restrictMk_eq_of_linearEquiv f hfin e
  | ses P P' P'' f0 g0 hf0 hg0 he0 =>
    rw [map_sub, map_sub, sub_sub, sub_eq_zero]
    let : Module R P.module := Module.compHom P.module f
    let : Module R P'.module := Module.compHom P'.module f
    let : Module R P''.module := Module.compHom P''.module f
    have : IsScalarTower R S P.module := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    have : IsScalarTower R S P'.module := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    have : IsScalarTower R S P''.module := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    have : Module.Finite R P.module := Module.Finite.trans S P.module
    have : Module.Finite R P'.module := Module.Finite.trans S P'.module
    have : Module.Finite R P''.module := Module.Finite.trans S P''.module
    exact K0prime.mkModule_add_of_ses _ _ _ (f0.restrictScalars R) (g0.restrictScalars R)
      hf0 hg0 he0

/-- **(B') Backward map, K'₀.**  Restriction of scalars along the projections
gives `K'₀(R₁) × K'₀(R₂) → K'₀(R₁×R₂)` sending `([N₁],0) ↦ [N₁|_R]` and
`(0,[N₂]) ↦ [N₂|_R]`.

PROOF SKETCH: define `ψᵢ` on `FGPres Rᵢ` by `P ↦ K0prime.restrictMk pᵢ P.module`,
lift through `FreeAbelianGroup.lift` and descend past the `K0Rel`-closure: a SES
of `Rᵢ`-modules is also a SES of `R`-modules under restriction of scalars (the
underlying abelian-group sequence is unchanged), so `K0Rel.ses`/`K0Rel.iso` are
respected.  Set `ψ := ψ₁ ∘ fst + ψ₂ ∘ snd`; evaluate on generators with
`map_zero`.  (Note `restrictMk pᵢ P.module` is the class of the same finite
module regarded over `R`.) -/
theorem K0prime_product_backward (R1 R2 : Type u) [CommRing R1] [CommRing R2]
    [IsNoetherianRing R1] [IsNoetherianRing R2] :
    ∃ ψ : (K0prime R1 × K0prime R2) →+ K0prime (R1 × R2),
      (∀ N1 : FGPres R1,
          ψ (K0prime.mk N1, 0) =
          K0prime.restrictMk (RingHom.fst R1 R2) (Prod.fst_finite R1 R2) N1.module) ∧
      (∀ N2 : FGPres R2,
          ψ (0, K0prime.mk N2) = K0prime.restrictMk (RingHom.snd R1 R2) (Prod.snd_finite R1
              R2) N2.module) := by
  classical
  obtain ⟨ψ1, hψ1⟩ := exists_restrictMk_hom (RingHom.fst R1 R2) (Prod.fst_finite R1 R2)
  obtain ⟨ψ2, hψ2⟩ := exists_restrictMk_hom (RingHom.snd R1 R2) (Prod.snd_finite R1 R2)
  refine ⟨ψ1.comp (AddMonoidHom.fst (K0prime R1) (K0prime R2))
        + ψ2.comp (AddMonoidHom.snd (K0prime R1) (K0prime R2)), fun N1 => ?_, fun N2 => ?_⟩
  · show ψ1 (K0prime.mk N1) + ψ2 0 = _
    rw [map_zero, add_zero, hψ1]
  · show ψ1 0 + ψ2 (K0prime.mk N2) = _
    rw [map_zero, zero_add, hψ2]

/-- The class of `M.module` as a module agrees with the class of the presentation `M`. -/
private theorem mkModule_module_eq_mk {R : Type u} [CommRing R] (M : FGPres R) :
    K0prime.mkModule R M.module = K0prime.mk M := by
  obtain ⟨e⟩ := (FGPres.skeleton_surjective (R := R) M.module).choose_spec
  set P := (FGPres.skeleton_surjective (R := R) M.module).choose with hP
  have hmem : FreeAbelianGroup.of M - FreeAbelianGroup.of P ∈ K0Sub R :=
    AddSubgroup.subset_closure (K0Rel.iso M P e.symm)
  show (QuotientAddGroup.mk (FreeAbelianGroup.of P) : K0prime R) = QuotientAddGroup.mk _
  rw [QuotientAddGroup.eq]
  simpa [sub_eq_neg_add] using hmem

/-- The class of a product of finite modules is the sum of the classes. -/
private theorem mkModule_prod (R : Type u) [CommRing R] (A B : Type u) [AddCommGroup A]
    [Module R A] [Module.Finite R A] [AddCommGroup B] [Module R B] [Module.Finite R B] :
    K0prime.mkModule R (A × B) = K0prime.mkModule R A + K0prime.mkModule R B :=
  K0prime.mkModule_add_of_ses (A × B) A B (LinearMap.inl R A B) (LinearMap.snd R A B)
    (fun a b h => congrArg Prod.fst h) (fun b => ⟨(0, b), rfl⟩)
    (fun x => ⟨fun hx => ⟨x.fst, Prod.ext rfl hx.symm⟩, by rintro ⟨a, rfl⟩; rfl⟩)

/-- Two additive maps out of `K'₀(S)` agreeing on the classes of presentations are equal. -/
private theorem K0prime_hom_ext {S : Type u} [CommRing S] {T : Type*} [AddCommGroup T]
    {F G : K0prime S →+ T} (h : ∀ N : FGPres S, F (K0prime.mk N) = G (K0prime.mk N)) : F = G :=
  QuotientAddGroup.addMonoidHom_ext _ (FreeAbelianGroup.lift_ext _ _ h)

-- needed: `K0prime_product_left_inv`'s `FreeAbelianGroup` induction leaves the `H.zero` goal
-- unless the quotient's `HAdd` instance is defeq to the target's at `default` transparency
set_option backward.isDefEq.respectTransparency false in
/-- **(C'-left) `ψ ∘ φ = id` on K'₀.**

PROOF SKETCH: `K0prime (R1×R2)` is generated by the `K0prime.mk M`
(`QuotientAddGroup.induction_on` + `FreeAbelianGroup.induction_on`), and `φ`,
`ψ` are additive, so check on a generator `K0prime.mk M` with underlying finite
`R`-module `M.module`.  Then `ψ(φ(mk M)) = ψ(baseChangeMk fst M.module,
baseChangeMk snd M.module) = restrictMk fst (M.module ⊗ R₁) + restrictMk snd
(M.module ⊗ R₂)`, and the IDEMPOTENT DECOMPOSITION `M.module ≅ (M.module⊗R₁)|_R ⊕
(M.module⊗R₂)|_R` as `R`-modules together with the additivity of `K0prime` on direct
sums (a split SES is a SES: `K0Rel.ses`) gives `= mk M`.  The class identities
use that `K0prime.mkModule`/`K0prime.restrictMk`/`K0prime.baseChangeMk` are well defined on
isomorphism classes of finite modules (via `K0Rel.iso` / `FGPres.skeleton_surjective`). -/
theorem K0prime_product_left_inv (R1 R2 : Type u) [CommRing R1] [CommRing R2]
    [IsNoetherianRing R1] [IsNoetherianRing R2]
    (φ : K0prime (R1 × R2) →+ (K0prime R1 × K0prime R2))
    (ψ : (K0prime R1 × K0prime R2) →+ K0prime (R1 × R2))
    (hφ : ∀ M : FGPres (R1 × R2),
        φ (K0prime.mk M) =
          ( K0prime.baseChangeMk (RingHom.fst R1 R2) M.module,
            K0prime.baseChangeMk (RingHom.snd R1 R2) M.module ))
    (hψ1 : ∀ N1 : FGPres R1,
        ψ (K0prime.mk N1, 0) =
          K0prime.restrictMk (RingHom.fst R1 R2) (Prod.fst_finite R1 R2) N1.module)
    (hψ2 : ∀ N2 : FGPres R2,
        ψ (0, K0prime.mk N2) =
          K0prime.restrictMk (RingHom.snd R1 R2) (Prod.snd_finite R1 R2) N2.module) :
    ∀ x : K0prime (R1 × R2), ψ (φ x) = x := by
  classical
  let : Algebra (R1 × R2) R1 := (RingHom.fst R1 R2).toAlgebra
  let : Algebra (R1 × R2) R2 := (RingHom.snd R1 R2).toAlgebra
  -- helper: the idempotent decomposition `(N⊗R1) ⊕ (N⊗R2) ≅ N` for any finite
  -- `(R1×R2)`-module `N`, as `(R1×R2)`-linear equiv.
  have hidem : ∀ (N : Type u) [AddCommGroup N] [Module (R1 × R2) N],
      (TensorProduct (R1 × R2) R1 N × TensorProduct (R1 × R2) R2 N) ≃ₗ[R1 × R2] N := by
    intro N _ _
    let b1 : R1 →ₗ[R1 × R2] N →ₗ[R1 × R2] N :=
      { toFun := fun r1 =>
          { toFun := fun m => ((r1, 0) : R1 × R2) • m
            map_add' := fun x y => by simp
            map_smul' := fun c x => by
              simp only [RingHom.id_apply, smul_smul]
              congr 1
              ext <;> simp [mul_comm] }
        map_add' := fun x y => by
          ext m
          simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
          rw [show ((x + y, 0) : R1 × R2) = (x, 0) + (y, 0) by ext <;> simp, add_smul]
        map_smul' := fun c x => by
          ext m
          simp only [LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply,
            smul_smul]
          congr 1
          show (c.fst * x, 0) = c * (x, 0)
          ext <;> simp }
    let g1 : TensorProduct (R1 × R2) R1 N →ₗ[R1 × R2] N := TensorProduct.lift b1
    let b2 : R2 →ₗ[R1 × R2] N →ₗ[R1 × R2] N :=
      { toFun := fun r2 =>
          { toFun := fun m => ((0, r2) : R1 × R2) • m
            map_add' := fun x y => by simp
            map_smul' := fun c x => by
              simp only [RingHom.id_apply, smul_smul]
              congr 1
              ext <;> simp [mul_comm] }
        map_add' := fun x y => by
          ext m
          simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
          rw [show ((0, x + y) : R1 × R2) = (0, x) + (0, y) by ext <;> simp, add_smul]
        map_smul' := fun c x => by
          ext m
          simp only [LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply,
            smul_smul]
          congr 1
          show (0, c.snd * x) = c * (0, x)
          ext <;> simp }
    let g2 : TensorProduct (R1 × R2) R2 N →ₗ[R1 × R2] N := TensorProduct.lift b2
    let F : (TensorProduct (R1 × R2) R1 N × TensorProduct (R1 × R2) R2 N) →ₗ[R1 × R2] N :=
      (g1.comp (LinearMap.fst (R1 × R2) _ _)) + (g2.comp (LinearMap.snd (R1 × R2) _ _))
    let G : N →ₗ[R1 × R2]
        (TensorProduct (R1 × R2) R1 N × TensorProduct (R1 × R2) R2 N) :=
      { toFun := fun m => ((1 : R1) ⊗ₜ[R1 × R2] m, (1 : R2) ⊗ₜ[R1 × R2] m)
        map_add' := fun x y => by simp [TensorProduct.tmul_add]
        map_smul' := fun c x => by
          simp only [RingHom.id_apply, Prod.smul_mk]
          rw [TensorProduct.tmul_smul, TensorProduct.tmul_smul] }
    refine LinearEquiv.ofLinearMap F G ?_ ?_
    · ext m
      show g1 ((1 : R1) ⊗ₜ[R1 × R2] m) + g2 ((1 : R2) ⊗ₜ[R1 × R2] m) = m
      show ((1, 0) : R1 × R2) • m + ((0, 1) : R1 × R2) • m = m
      rw [← add_smul, show ((1, 0) : R1 × R2) + (0, 1) = 1 by ext <;> simp, one_smul]
    · refine LinearMap.ext (fun x => ?_)
      refine Prod.ext ?_ ?_
      · show (1 : R1) ⊗ₜ[R1 × R2] (g1 x.fst + g2 x.snd) = x.fst
        rw [TensorProduct.tmul_add]
        have hcross : (1 : R1) ⊗ₜ[R1 × R2] (g2 x.snd) = 0 := by
          induction x.snd using TensorProduct.induction_on with
          | zero => simp
          | tmul r2 m =>
            show (1 : R1) ⊗ₜ[R1 × R2] (((0, r2) : R1 × R2) • m) = 0
            rw [TensorProduct.tmul_smul]
            show (((0, r2) : R1 × R2) • (1 : R1)) ⊗ₜ[R1 × R2] m = 0
            rw [show ((0, r2) : R1 × R2) • (1 : R1) = (0 : R1) by
              show (RingHom.fst R1 R2) (0, r2) * 1 = 0; simp]
            rw [TensorProduct.zero_tmul]
          | add a b ha hb => rw [map_add, TensorProduct.tmul_add, ha, hb, add_zero]
        have hself : (1 : R1) ⊗ₜ[R1 × R2] (g1 x.fst) = x.fst := by
          induction x.fst using TensorProduct.induction_on with
          | zero => simp
          | tmul r1 m =>
            show (1 : R1) ⊗ₜ[R1 × R2] (((r1, 0) : R1 × R2) • m) = r1 ⊗ₜ[R1 × R2] m
            rw [TensorProduct.tmul_smul]
            show (((r1, 0) : R1 × R2) • (1 : R1)) ⊗ₜ[R1 × R2] m = r1 ⊗ₜ[R1 × R2] m
            rw [show ((r1, 0) : R1 × R2) • (1 : R1) = r1 by
              show (RingHom.fst R1 R2) (r1, 0) * 1 = r1; simp]
          | add a b ha hb => rw [map_add, TensorProduct.tmul_add, ha, hb]
        rw [hself, hcross, add_zero]
      · show (1 : R2) ⊗ₜ[R1 × R2] (g1 x.fst + g2 x.snd) = x.snd
        rw [TensorProduct.tmul_add]
        have hcross : (1 : R2) ⊗ₜ[R1 × R2] (g1 x.fst) = 0 := by
          induction x.fst using TensorProduct.induction_on with
          | zero => simp
          | tmul r1 m =>
            show (1 : R2) ⊗ₜ[R1 × R2] (((r1, 0) : R1 × R2) • m) = 0
            rw [TensorProduct.tmul_smul]
            show (((r1, 0) : R1 × R2) • (1 : R2)) ⊗ₜ[R1 × R2] m = 0
            rw [show ((r1, 0) : R1 × R2) • (1 : R2) = (0 : R2) by
              show (RingHom.snd R1 R2) (r1, 0) * 1 = 0; simp]
            rw [TensorProduct.zero_tmul]
          | add a b ha hb => rw [map_add, TensorProduct.tmul_add, ha, hb, add_zero]
        have hself : (1 : R2) ⊗ₜ[R1 × R2] (g2 x.snd) = x.snd := by
          induction x.snd using TensorProduct.induction_on with
          | zero => simp
          | tmul r2 m =>
            show (1 : R2) ⊗ₜ[R1 × R2] (((0, r2) : R1 × R2) • m) = r2 ⊗ₜ[R1 × R2] m
            rw [TensorProduct.tmul_smul]
            show (((0, r2) : R1 × R2) • (1 : R2)) ⊗ₜ[R1 × R2] m = r2 ⊗ₜ[R1 × R2] m
            rw [show ((0, r2) : R1 × R2) • (1 : R2) = r2 by
              show (RingHom.snd R1 R2) (0, r2) * 1 = r2; simp]
          | add a b ha hb => rw [map_add, TensorProduct.tmul_add, ha, hb]
        rw [hcross, hself, zero_add]
  intro x
  refine DFunLike.congr_fun (K0prime_hom_ext (F := ψ.comp φ) (G := AddMonoidHom.id _)
    fun M => ?_) x
  show ψ (φ (K0prime.mk M)) = K0prime.mk M
  rw [hφ M]
  -- the two base-change carriers
  set A1 := TensorProduct (R1 × R2) R1 M.module with hA1
  set A2 := TensorProduct (R1 × R2) R2 M.module with hA2
  -- presentations chosen by `mkModule`
  have hbc1 : K0prime.baseChangeMk (RingHom.fst R1 R2) M.module = K0prime.mkModule R1 A1 := rfl
  have hbc2 : K0prime.baseChangeMk (RingHom.snd R1 R2) M.module = K0prime.mkModule R2 A2 := rfl
  set P1 := (FGPres.skeleton_surjective (R := R1) A1).choose with hP1
  set P2 := (FGPres.skeleton_surjective (R := R2) A2).choose with hP2
  obtain ⟨e1⟩ := (FGPres.skeleton_surjective (R := R1) A1).choose_spec
  obtain ⟨e2⟩ := (FGPres.skeleton_surjective (R := R2) A2).choose_spec
  -- `baseChangeMk fst M.module = K0prime.mk P1`
  have hmk1 : K0prime.baseChangeMk (RingHom.fst R1 R2) M.module = K0prime.mk P1 := rfl
  have hmk2 : K0prime.baseChangeMk (RingHom.snd R1 R2) M.module = K0prime.mk P2 := rfl
  -- split the pair
  have hsplit : ((K0prime.baseChangeMk (RingHom.fst R1 R2) M.module,
        K0prime.baseChangeMk (RingHom.snd R1 R2) M.module) : K0prime R1 × K0prime R2)
      = (K0prime.mk P1, 0) + (0, K0prime.mk P2) := by
    rw [hmk1, hmk2]; ext <;> simp
  rw [hsplit, map_add, hψ1 P1, hψ2 P2]
  -- now: restrictMk fst _ P1.module + restrictMk snd _ P2.module = mk M
  rw [restrictMk_eq_of_linearEquiv _ _ e1, restrictMk_eq_of_linearEquiv _ _ e2]
  -- set up the `(R1×R2)`-module structures by restriction along the projections
  let : Module (R1 × R2) A1 := Module.compHom A1 (RingHom.fst R1 R2)
  let : Module (R1 × R2) A2 := Module.compHom A2 (RingHom.snd R1 R2)
  have : IsScalarTower (R1 × R2) R1 A1 := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower (R1 × R2) R2 A2 := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Finite (R1 × R2) R1 := Prod.fst_finite R1 R2
  have : Module.Finite (R1 × R2) R2 := Prod.snd_finite R1 R2
  have : Module.Finite (R1 × R2) A1 := Module.Finite.trans R1 A1
  have : Module.Finite (R1 × R2) A2 := Module.Finite.trans R2 A2
  show K0prime.mkModule (R1 × R2) A1 + K0prime.mkModule (R1 × R2) A2 = K0prime.mk M
  -- the idempotent decomposition iso `A1 ⊕ A2 ≅ M.module` as `(R1×R2)`-modules
  have eM : (A1 × A2) ≃ₗ[R1 × R2] M.module := hidem M.module
  -- `mkModule A1 + mkModule A2 = mkModule (A1 × A2) = mkModule M.module = mk M`
  rw [← mkModule_prod, K0prime.mkModule_eq_of_iso _ _ eM, mkModule_module_eq_mk]

-- needed: `K0prime_product_right_inv`'s product-component goals need the `K0prime` quotient
-- instances unfolded at `default` transparency
set_option backward.isDefEq.respectTransparency false in
/-- **(C'-right) `φ ∘ ψ = id` on K'₀.**

PROOF SKETCH: `K0prime R1 × K0prime R2` is generated by `(mk N1, 0)` and `(0, mk N2)`;
both maps additive, so check on these.  For `(mk N1,0)`: `φ(ψ(mk N1,0)) =
φ(restrictMk fst N1.module)`; choosing a presentation of the `R`-module
`N1.module|_R` and applying `hφ` gives `(baseChangeMk fst (N1.module|_R),
baseChangeMk snd (N1.module|_R))`.  The BASE-CHANGE/RESTRICTION CANCELLATIONS
`(N1.module|_R) ⊗_R R₁ ≅ N1.module` (idempotent `e₁` acts as identity after
restricting then extending along the same surjection `fst`) and
`(N1.module|_R) ⊗_R R₂ ≅ 0` (idempotent `e₂` kills it), together with
`K0prime.mkModule`/`baseChangeMk` respecting isomorphisms and `mkModule R 0 = 0`,
give `(mk N1, 0)`.  Symmetric for `(0, mk N2)`. -/
theorem K0prime_product_right_inv (R1 R2 : Type u) [CommRing R1] [CommRing R2]
    [IsNoetherianRing R1] [IsNoetherianRing R2]
    (φ : K0prime (R1 × R2) →+ (K0prime R1 × K0prime R2))
    (ψ : (K0prime R1 × K0prime R2) →+ K0prime (R1 × R2))
    (hφ : ∀ M : FGPres (R1 × R2),
        φ (K0prime.mk M) =
          ( K0prime.baseChangeMk (RingHom.fst R1 R2) M.module,
            K0prime.baseChangeMk (RingHom.snd R1 R2) M.module ))
    (hψ1 : ∀ N1 : FGPres R1,
        ψ (K0prime.mk N1, 0) =
          K0prime.restrictMk (RingHom.fst R1 R2) (Prod.fst_finite R1 R2) N1.module)
    (hψ2 : ∀ N2 : FGPres R2,
        ψ (0, K0prime.mk N2) =
          K0prime.restrictMk (RingHom.snd R1 R2) (Prod.snd_finite R1 R2) N2.module) :
    ∀ y : K0prime R1 × K0prime R2, φ (ψ y) = y := by
  classical
  let : Algebra (R1 × R2) R1 := (RingHom.fst R1 R2).toAlgebra
  let : Algebra (R1 × R2) R2 := (RingHom.snd R1 R2).toAlgebra
  have : Module.Finite (R1 × R2) R1 := Prod.fst_finite R1 R2
  have : Module.Finite (R1 × R2) R2 := Prod.snd_finite R1 R2
  -- subsingleton modules have zero class
  have hzero : ∀ {R : Type u} [CommRing R] (A : Type u) [AddCommGroup A] [Module R A]
      [Module.Finite R A] [Subsingleton A], K0prime.mkModule R A = 0 := by
    intro R _ A _ _ _ _
    have hadd := mkModule_prod R A A
    rw [K0prime.mkModule_eq_of_iso _ _ (LinearEquiv.ofSubsingleton (A × A) A)] at hadd
    exact left_eq_add.mp hadd
  -- generators
  have hgen1 : ∀ N1 : FGPres R1, φ (ψ (K0prime.mk N1, 0)) = (K0prime.mk N1, 0) := by
    intro N1
    rw [hψ1 N1]
    -- set up the `(R1×R2)`-module structure on `N1.module` and present it
    let : Module (R1 × R2) N1.module := Module.compHom N1.module (RingHom.fst R1 R2)
    have : IsScalarTower (R1 × R2) R1 N1.module := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    have : Module.Finite (R1 × R2) N1.module := Module.Finite.trans R1 N1.module
    obtain ⟨e⟩ := (FGPres.skeleton_surjective (R := R1 × R2) N1.module).choose_spec
    set P := (FGPres.skeleton_surjective (R := R1 × R2) N1.module).choose with hP
    have hres : K0prime.restrictMk (RingHom.fst R1 R2) (Prod.fst_finite R1 R2) N1.module
        = K0prime.mk P := rfl
    rw [hres, hφ P]
    refine Prod.ext ?_ ?_
    · -- fst component: baseChangeMk fst P.module = K0prime.mk N1
      show K0prime.mkModule R1 (TensorProduct (R1 × R2) R1 P.module) = K0prime.mk N1
      -- iso: T R1 P.module ≅ T R1 N1.module ≅ N1.module
      have eT : TensorProduct (R1 × R2) R1 P.module ≃ₗ[R1] TensorProduct (R1 × R2) R1 N1.module :=
        LinearEquiv.baseChange (R1 × R2) R1 P.module N1.module e
      rw [K0prime.mkModule_eq_of_iso _ _ eT,
        K0prime.mkModule_eq_of_iso _ _ (Prod.tensorFstEquiv R1 R2 N1.module)]
      exact mkModule_module_eq_mk N1
    · -- snd component: baseChangeMk snd P.module = 0
      show K0prime.mkModule R2 (TensorProduct (R1 × R2) R2 P.module) = 0
      have eT : TensorProduct (R1 × R2) R2 P.module ≃ₗ[R2] TensorProduct (R1 × R2) R2 N1.module :=
        LinearEquiv.baseChange (R1 × R2) R2 P.module N1.module e
      rw [K0prime.mkModule_eq_of_iso _ _ eT]
      have : Subsingleton (TensorProduct (R1 × R2) R2 N1.module) :=
        Prod.subsingleton_tensor_snd_of_fst R1 R2 N1.module
      exact hzero _
  have hgen2 : ∀ N2 : FGPres R2, φ (ψ (0, K0prime.mk N2)) = (0, K0prime.mk N2) := by
    intro N2
    rw [hψ2 N2]
    let : Module (R1 × R2) N2.module := Module.compHom N2.module (RingHom.snd R1 R2)
    have : IsScalarTower (R1 × R2) R2 N2.module := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    have : Module.Finite (R1 × R2) N2.module := Module.Finite.trans R2 N2.module
    obtain ⟨e⟩ := (FGPres.skeleton_surjective (R := R1 × R2) N2.module).choose_spec
    set P := (FGPres.skeleton_surjective (R := R1 × R2) N2.module).choose with hP
    have hres : K0prime.restrictMk (RingHom.snd R1 R2) (Prod.snd_finite R1 R2) N2.module
        = K0prime.mk P := rfl
    rw [hres, hφ P]
    refine Prod.ext ?_ ?_
    · -- fst component: baseChangeMk fst P.module = 0
      show K0prime.mkModule R1 (TensorProduct (R1 × R2) R1 P.module) = 0
      have eT : TensorProduct (R1 × R2) R1 P.module ≃ₗ[R1] TensorProduct (R1 × R2) R1 N2.module :=
        LinearEquiv.baseChange (R1 × R2) R1 P.module N2.module e
      rw [K0prime.mkModule_eq_of_iso _ _ eT]
      have : Subsingleton (TensorProduct (R1 × R2) R1 N2.module) :=
        Prod.subsingleton_tensor_fst_of_snd R1 R2 N2.module
      exact hzero _
    · -- snd component: baseChangeMk snd P.module = K0prime.mk N2
      show K0prime.mkModule R2 (TensorProduct (R1 × R2) R2 P.module) = K0prime.mk N2
      have eT : TensorProduct (R1 × R2) R2 P.module ≃ₗ[R2] TensorProduct (R1 × R2) R2 N2.module :=
        LinearEquiv.baseChange (R1 × R2) R2 P.module N2.module e
      rw [K0prime.mkModule_eq_of_iso _ _ eT,
        K0prime.mkModule_eq_of_iso _ _ (Prod.tensorSndEquiv R1 R2 N2.module)]
      exact mkModule_module_eq_mk N2
  -- reduce to generators
  have hleft : ∀ a : K0prime R1, φ (ψ (a, 0)) = (a, 0) := fun a =>
    DFunLike.congr_fun (K0prime_hom_ext (F := (φ.comp ψ).comp (AddMonoidHom.inl _ _))
      (G := AddMonoidHom.inl _ _) hgen1) a
  have hright : ∀ c : K0prime R2, φ (ψ (0, c)) = (0, c) := fun c =>
    DFunLike.congr_fun (K0prime_hom_ext (F := (φ.comp ψ).comp (AddMonoidHom.inr _ _))
      (G := AddMonoidHom.inr _ _) hgen2) c
  intro y
  have hy : y = (y.fst, 0) + (0, y.snd) := by ext <;> simp
  rw [hy, map_add, map_add, hleft y.fst, hright y.snd]

/-- Assume in addition that `R₁` and `R₂` are Noetherian
(equivalently that `R = R₁ × R₂` is Noetherian).  Then the natural
homomorphism `K'₀(R) → K'₀(R₁) × K'₀(R₂)`, given on generators by
`[M] ↦ ([M ⊗_R R₁], [M ⊗_R R₂])`, is an isomorphism of abelian groups.

As for Statement 1, the classes `K0prime.mk M` generate `K0prime (R₁ × R₂)`, so the
additive isomorphism `e` is uniquely determined by the stated property. -/
@[stacks 00JH "K'_0"]
theorem K0prime_product (R1 R2 : Type u) [CommRing R1] [CommRing R2]
    [IsNoetherianRing R1] [IsNoetherianRing R2] :
    ∃ e : K0prime (R1 × R2) ≃+ (K0prime R1 × K0prime R2),
      ∀ M : FGPres (R1 × R2),
        e (K0prime.mk M) =
          ( K0prime.baseChangeMk (RingHom.fst R1 R2) M.module,
            K0prime.baseChangeMk (RingHom.snd R1 R2) M.module ) := by
  -- Same assembly as Statement 1: combine forward/backward maps with the two
  -- round-trip identities (the math is in the four `K0prime_product_*` sub-lemmas).
  obtain ⟨φ, hφ⟩ := K0prime_product_forward R1 R2
  obtain ⟨ψ, hψ1, hψ2⟩ := K0prime_product_backward R1 R2
  exact ⟨{ toFun := φ, invFun := ψ, map_add' := φ.map_add,
           left_inv := K0prime_product_left_inv R1 R2 φ ψ hφ hψ1 hψ2,
            right_inv := K0prime_product_right_inv R1 R2 φ ψ hφ hψ1 hψ2 }, hφ⟩
