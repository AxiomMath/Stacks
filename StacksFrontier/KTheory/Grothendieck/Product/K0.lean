module

public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.KTheory.Grothendieck.Defs
public import StacksFrontier.KTheory.Grothendieck.Product.BaseChange
public import StacksFrontier.KTheory.Grothendieck.Product.Factors

/-!
# The Grothendieck group `K_0` of a product of two rings

Stacks Project lemma `lemma-K0-product`:
Let `R = R_1 \times R_2` be a product of two commutative rings. Then
`K_0(R) = K_0(R_1) \times K_0(R_2)` and, when `R` is Noetherian,
`K'_0(R) = K'_0(R_1) \times K'_0(R_2)`.

This file proves the first half: `K_0(R_1 \times R_2) = K_0(R_1) \times K_0(R_2)`,
for the Grothendieck group of finite projective modules. The forward map is base
change along the two projections, the backward map is restriction of scalars
along them, and the two composites are the identity. The overall strategy,
which the `K'_0` half follows verbatim, is spelled out in the comment below.
-/

@[expose] public section

universe u

-- Auxiliary constructions and sub-lemmas for the proof
--
-- OVERALL STRATEGY (Stacks `lemma-K0-product`, idempotent decomposition).
-- Write `R = R₁ × R₂` with complementary central idempotents `e₁ = (1,0)`,
-- `e₂ = (0,1)`.  The two ring projections `p₁ = fst`, `p₂ = snd : R →+* Rᵢ` are
-- surjective and each `Rᵢ` is a direct factor of `R` (hence a finite projective
-- `R`-algebra).  The proof of both statements is the same three-step pattern:
--
--   (A) FORWARD map `φ : K?(R) →+ K?(R₁) × K?(R₂)`, `[M] ↦ ([M⊗_R R₁],[M⊗_R R₂])`
--       (base change along the two projections).  Well defined because base
--       change is additive on the free group, sends direct sums to direct sums
--       and isomorphisms to isomorphisms (and for K₀' it is exact on the SES
--       relations because `Rᵢ` is `R`-flat: it is a direct factor).
--   (B) BACKWARD map `ψ : K?(R₁) × K?(R₂) →+ K?(R)`,
--       `([N₁],[N₂]) ↦ [N₁] + [N₂]` where `Nᵢ` is regarded as an `R`-module by
--       restriction of scalars along `pᵢ` (equivalently, extension by zero of
--       the other idempotent).  Restriction along `pᵢ` preserves "finite",
--       "projective" (resp. is exact), so `ψ` is a well-defined homomorphism.
--   (C) The two composites are the identity, checked on the generating classes:
--         * `ψ ∘ φ = id`:  for an `R`-module `M`,
--               `M ≅ (M⊗_R R₁)|_R ⊕ (M⊗_R R₂)|_R`           (idempotent split)
--           as `R`-modules, so `ψ(φ[M]) = [(M⊗R₁)|_R] + [(M⊗R₂)|_R] = [M]`.
--         * `φ ∘ ψ = id`:  `(N₁|_R) ⊗_R R₁ ≅ N₁` and `(N₁|_R) ⊗_R R₂ ≅ 0`
--           (and symmetrically for `N₂`), so `φ(ψ([N₁],[N₂])) = ([N₁],[N₂])`.
--       Reduction to generators uses additivity of `φ`, `ψ` together with the
--       fact that the classes `mk M` generate the source groups.

/-- A function on `FGProj R` that is additive on direct sums and invariant under isomorphism
descends to an additive homomorphism on `K0 R`. -/
private theorem K0_exists_lift {R : Type u} [CommRing R] {A : Type*} [AddCommGroup A]
    (F : FGProj R → A) (hsum : ∀ M N : FGProj R, F (M.directSum N) = F M + F N)
    (hiso : ∀ M N : FGProj R, (M.carrier ≃ₗ[R] N.carrier) → F M = F N) :
    ∃ f : K0 R →+ A, ∀ M : FGProj R, f (K0.mk M) = F M := by
  have hker : K0.rels R ≤ (FreeAbelianGroup.lift F).ker := by
    rw [K0.rels, AddSubgroup.closure_le]
    rintro x (⟨M, N, rfl⟩ | ⟨M, N, ⟨e⟩, rfl⟩)
    · simp [hsum]
    · simp [hiso M N e]
  exact ⟨QuotientAddGroup.lift _ _ hker, fun M => FreeAbelianGroup.lift_apply_of _ _⟩

/-- Two additive homomorphisms out of `K0 R` agreeing on all classes `K0.mk M` are equal. -/
private theorem K0_hom_ext {R : Type u} [CommRing R] {A : Type*} [AddCommGroup A]
    {f g : K0 R →+ A} (h : ∀ M : FGProj R, f (K0.mk M) = g (K0.mk M)) : f = g :=
  QuotientAddGroup.addMonoidHom_ext _ (FreeAbelianGroup.lift_ext _ _ h)

/-- **(A) Forward map, K₀.**  Base change along the two projections assembles
into a well-defined additive homomorphism `K₀(R₁×R₂) → K₀(R₁) × K₀(R₂)` sending
each generator `[M]` to `([M⊗R₁],[M⊗R₂])`.

PROOF SKETCH: lift the function `M ↦ (mk (M.baseChangeHom fst), mk (M.baseChangeHom snd))`
through `FreeAbelianGroup.lift`, then descend through the quotient by `K0.rels`
via `QuotientAddGroup.lift`/`K0.rels`-respecting.  The two relation families are
respected because `baseChangeHom f` sends `M.directSum N` to a module isomorphic
to `(M.baseChangeHom f).directSum (N.baseChangeHom f)` (`S ⊗ (M⊕N) ≅ S⊗M ⊕ S⊗N`,
`TensorProduct.prodRight`/`TensorProduct.lift`), and sends isomorphic modules to
isomorphic modules (`LinearEquiv` base-change `TensorProduct.congr`/
`LinearEquiv.lTensor`).  Use `K0.mk_directSum_eq` and `K0.mk_eq_of_iso` to see
the images satisfy the defining relations. -/
theorem K0_product_forward (R1 R2 : Type u) [CommRing R1] [CommRing R2] :
    ∃ φ : K0 (R1 × R2) →+ (K0 R1 × K0 R2),
      ∀ M : FGProj (R1 × R2),
        φ (K0.mk M) =
          ( K0.mk (M.baseChangeHom (RingHom.fst R1 R2)),
            K0.mk (M.baseChangeHom (RingHom.snd R1 R2)) ) := by
  -- helper: base change respects direct sums in K0
  have hsum : ∀ {S : Type u} [CommRing S] (f : (R1 × R2) →+* S) (M N : FGProj (R1 × R2)),
      K0.mk ((M.directSum N).baseChangeHom f)
        = K0.mk (M.baseChangeHom f) + K0.mk (N.baseChangeHom f) := by
    intro S _ f M N
    let : Algebra (R1 × R2) S := f.toAlgebra
    rw [← K0.mk_directSum_eq (M.baseChangeHom f) (N.baseChangeHom f)]
    exact K0.mk_eq_of_iso _ _ (TensorProduct.prodRight (R1 × R2) S S M.carrier N.carrier)
  -- helper: base change respects isos in K0
  have hiso : ∀ {S : Type u} [CommRing S] (f : (R1 × R2) →+* S) (M N : FGProj (R1 × R2)),
      (M.carrier ≃ₗ[R1 × R2] N.carrier) →
      K0.mk (M.baseChangeHom f) = K0.mk (N.baseChangeHom f) := by
    intro S _ f M N e
    let : Algebra (R1 × R2) S := f.toAlgebra
    exact K0.mk_eq_of_iso _ _ (LinearEquiv.baseChange (R1 × R2) S M.carrier N.carrier e)
  obtain ⟨φ, hφ⟩ := K0_exists_lift (R := R1 × R2)
    (fun M => (K0.mk (M.baseChangeHom (RingHom.fst R1 R2)),
      K0.mk (M.baseChangeHom (RingHom.snd R1 R2))))
    (fun M N => Prod.ext (hsum _ M N) (hsum _ M N))
    (fun M N e => Prod.ext (hiso _ M N e) (hiso _ M N e))
  exact ⟨φ, hφ⟩

/-- **(B) Backward map, K₀.**  Restriction of scalars along the projections
assembles into a homomorphism `K₀(R₁) × K₀(R₂) → K₀(R₁×R₂)` sending the two
families of generators `([N₁],0)` and `(0,[N₂])` to `[N₁|_R]` and `[N₂|_R]`.

PROOF SKETCH: define `ψ₁ : K0 R1 →+ K0 (R1×R2)` and `ψ₂ : K0 R2 →+ K0 (R1×R2)`
each by `FreeAbelianGroup.lift` + `QuotientAddGroup.lift` of `N ↦ mk (N.restrict pᵢ)`;
these respect `K0.rels` because restriction of scalars preserves direct sums
(`(N⊕N')|_R = N|_R ⊕ N'|_R` definitionally on carriers, so `FGProj.restrict`
commutes with `directSum` up to iso) and isomorphisms (an `Rᵢ`-linear equiv is in
particular `R`-linear via `f`).  Then `ψ := ψ₁ ∘ fst + ψ₂ ∘ snd` (i.e.
`(ψ₁.comp (AddMonoidHom.fst _ _)) + (ψ₂.comp (AddMonoidHom.snd _ _))`); evaluate
on the generators using `map_zero` to get the stated values. -/
theorem K0_product_backward (R1 R2 : Type u) [CommRing R1] [CommRing R2] :
    ∃ ψ : (K0 R1 × K0 R2) →+ K0 (R1 × R2),
      (∀ N1 : FGProj R1, ψ (K0.mk N1, 0) =
          K0.mk (N1.restrict (RingHom.fst R1 R2) (Prod.fst_finite R1 R2) (Prod.fst_projective R1
              R2))) ∧
      (∀ N2 : FGProj R2, ψ (0, K0.mk N2) =
          K0.mk (N2.restrict (RingHom.snd R1 R2) (Prod.snd_finite R1 R2) (Prod.snd_projective R1
              R2))) := by
  -- helper: restriction respects direct sums in K0
  have hsum : ∀ {S : Type u} [CommRing S] (f : (R1 × R2) →+* S)
      (hfin : let : Module (R1 × R2) S := (f.toAlgebra).toModule; Module.Finite (R1 × R2) S)
      (hproj : let : Module (R1 × R2) S := (f.toAlgebra).toModule; Module.Projective (R1 × R2) S)
      (M N : FGProj S),
      K0.mk ((M.directSum N).restrict f hfin hproj)
        = K0.mk (M.restrict f hfin hproj) + K0.mk (N.restrict f hfin hproj) := by
    intro S _ f hfin hproj M N
    rw [← K0.mk_directSum_eq (M.restrict f hfin hproj) (N.restrict f hfin hproj)]
    exact K0.mk_eq_of_iso _ _ (LinearEquiv.refl _ _)
  -- helper: restriction respects isos in K0
  have hiso : ∀ {S : Type u} [CommRing S] (f : (R1 × R2) →+* S)
      (hfin : let : Module (R1 × R2) S := (f.toAlgebra).toModule; Module.Finite (R1 × R2) S)
      (hproj : let : Module (R1 × R2) S := (f.toAlgebra).toModule; Module.Projective (R1 × R2) S)
      (M N : FGProj S),
      (M.carrier ≃ₗ[S] N.carrier) →
      K0.mk (M.restrict f hfin hproj) = K0.mk (N.restrict f hfin hproj) := by
    intro S _ f hfin hproj M N e
    let : Algebra (R1 × R2) S := f.toAlgebra
    let : Module (R1 × R2) M.carrier := Module.compHom M.carrier f
    let : Module (R1 × R2) N.carrier := Module.compHom N.carrier f
    refine K0.mk_eq_of_iso _ _ ?_
    exact
      { toFun := e.toFun
        map_add' := e.map_add'
        map_smul' := fun (c : R1 × R2) x => e.map_smul' (f c) x
        invFun := e.invFun
        left_inv := e.left_inv
        right_inv := e.right_inv }
  obtain ⟨ψ1, hψ1⟩ := K0_exists_lift (R := R1)
    (fun N => K0.mk (N.restrict (RingHom.fst R1 R2) (Prod.fst_finite R1 R2)
      (Prod.fst_projective R1 R2)))
    (fun M N => hsum _ _ _ M N) (fun M N e => hiso _ _ _ M N e)
  obtain ⟨ψ2, hψ2⟩ := K0_exists_lift (R := R2)
    (fun N => K0.mk (N.restrict (RingHom.snd R1 R2) (Prod.snd_finite R1 R2)
      (Prod.snd_projective R1 R2)))
    (fun M N => hsum _ _ _ M N) (fun M N e => hiso _ _ _ M N e)
  exact ⟨ψ1.comp (AddMonoidHom.fst (K0 R1) (K0 R2)) + ψ2.comp (AddMonoidHom.snd (K0 R1) (K0 R2)),
    fun N1 => by simp [hψ1], fun N2 => by simp [hψ2]⟩

-- needed: `K0_product_idem_iso`'s `rw [add_zero]` on `K0prime R1 × K0prime R2` needs the product's
-- `AddZeroClass` instance unfolded at `default` transparency
set_option backward.isDefEq.respectTransparency false in
/-- **Idempotent decomposition isomorphism.**  For `R = R₁ × R₂` and a finite
projective `R`-module `M`, restricting the two base changes `M ⊗_R R₁` and
`M ⊗_R R₂` back to `R`-modules and taking their direct sum recovers `M`. -/
noncomputable def K0_product_idem_iso (R1 R2 : Type u) [CommRing R1] [CommRing R2]
    (M : FGProj (R1 × R2)) :
    (((M.baseChangeHom (RingHom.fst R1 R2)).restrict (RingHom.fst R1 R2)
        (Prod.fst_finite R1 R2) (Prod.fst_projective R1 R2)).directSum
      ((M.baseChangeHom (RingHom.snd R1 R2)).restrict (RingHom.snd R1 R2)
        (Prod.snd_finite R1 R2) (Prod.snd_projective R1 R2))).carrier ≃ₗ[R1 × R2]
      M.carrier := by
  classical
  letI : Algebra (R1 × R2) R1 := (RingHom.fst R1 R2).toAlgebra
  letI : Algebra (R1 × R2) R2 := (RingHom.snd R1 R2).toAlgebra
  -- abbreviations for the two tensor carriers
  -- `g1 : R1 ⊗ M → M`, `r1 ⊗ m ↦ (r1,0) • m`.
  let b1 : R1 →ₗ[R1 × R2] M.carrier →ₗ[R1 × R2] M.carrier :=
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
        change (c.fst * x, 0) = c * (x, 0)
        ext <;> simp }
  let g1 : TensorProduct (R1 × R2) R1 M.carrier →ₗ[R1 × R2] M.carrier :=
    TensorProduct.lift b1
  let b2 : R2 →ₗ[R1 × R2] M.carrier →ₗ[R1 × R2] M.carrier :=
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
        change (0, c.snd * x) = c * (0, x)
        ext <;> simp }
  let g2 : TensorProduct (R1 × R2) R2 M.carrier →ₗ[R1 × R2] M.carrier :=
    TensorProduct.lift b2
  -- forward map F : (R1⊗M) × (R2⊗M) → M
  let F : (TensorProduct (R1 × R2) R1 M.carrier × TensorProduct (R1 × R2) R2 M.carrier)
        →ₗ[R1 × R2] M.carrier :=
    (g1.comp (LinearMap.fst (R1 × R2) _ _)) + (g2.comp (LinearMap.snd (R1 × R2) _ _))
  -- backward map G : M → (R1⊗M) × (R2⊗M), m ↦ (1⊗m, 1⊗m)
  let G : M.carrier →ₗ[R1 × R2]
      (TensorProduct (R1 × R2) R1 M.carrier × TensorProduct (R1 × R2) R2 M.carrier) :=
    { toFun := fun m =>
        ((1 : R1) ⊗ₜ[R1 × R2] m, (1 : R2) ⊗ₜ[R1 × R2] m)
      map_add' := fun x y => by simp [TensorProduct.tmul_add]
      map_smul' := fun c x => by
        simp only [RingHom.id_apply, Prod.smul_mk]
        rw [TensorProduct.tmul_smul, TensorProduct.tmul_smul] }
  refine LinearEquiv.ofLinearMap F G ?_ ?_
  · -- F ∘ G = id
    ext m
    change g1 ((1 : R1) ⊗ₜ[R1 × R2] m) + g2 ((1 : R2) ⊗ₜ[R1 × R2] m) = m
    change ((1, 0) : R1 × R2) • m + ((0, 1) : R1 × R2) • m = m
    rw [← add_smul, show ((1, 0) : R1 × R2) + (0, 1) = 1 by ext <;> simp, one_smul]
  · -- G ∘ F = id
    ext x
    refine Prod.ext ?_ ?_
    · -- first component:  1 ⊗ (g1 x.1 + g2 x.2) = x.1
      change (1 : R1) ⊗ₜ[R1 × R2] (g1 x.fst + g2 x.snd) = x.fst
      rw [TensorProduct.tmul_add]
      have hcross : (1 : R1) ⊗ₜ[R1 × R2] (g2 x.snd) = 0 := by
        induction x.snd using TensorProduct.induction_on with
        | zero => simp
        | tmul r2 m =>
          change (1 : R1) ⊗ₜ[R1 × R2] (((0, r2) : R1 × R2) • m) = 0
          rw [TensorProduct.tmul_smul]
          change (((0, r2) : R1 × R2) • (1 : R1)) ⊗ₜ[R1 × R2] m = 0
          rw [show ((0, r2) : R1 × R2) • (1 : R1) = (0 : R1) by
            change (RingHom.fst R1 R2) (0, r2) * 1 = 0; simp]
          rw [TensorProduct.zero_tmul]
        | add a b ha hb => rw [map_add, TensorProduct.tmul_add, ha, hb, add_zero]
      have hself : (1 : R1) ⊗ₜ[R1 × R2] (g1 x.fst) = x.fst := by
        induction x.fst using TensorProduct.induction_on with
        | zero => simp
        | tmul r1 m =>
          change (1 : R1) ⊗ₜ[R1 × R2] (((r1, 0) : R1 × R2) • m) = r1 ⊗ₜ[R1 × R2] m
          rw [TensorProduct.tmul_smul]
          change (((r1, 0) : R1 × R2) • (1 : R1)) ⊗ₜ[R1 × R2] m = r1 ⊗ₜ[R1 × R2] m
          rw [show ((r1, 0) : R1 × R2) • (1 : R1) = r1 by
            change (RingHom.fst R1 R2) (r1, 0) * 1 = r1; simp]
        | add a b ha hb => rw [map_add, TensorProduct.tmul_add, ha, hb]
      rw [hself, hcross, add_zero]
    · -- second component:  1 ⊗ (g1 x.1 + g2 x.2) = x.2
      change (1 : R2) ⊗ₜ[R1 × R2] (g1 x.fst + g2 x.snd) = x.snd
      rw [TensorProduct.tmul_add]
      have hcross : (1 : R2) ⊗ₜ[R1 × R2] (g1 x.fst) = 0 := by
        induction x.fst using TensorProduct.induction_on with
        | zero => simp
        | tmul r1 m =>
          change (1 : R2) ⊗ₜ[R1 × R2] (((r1, 0) : R1 × R2) • m) = 0
          rw [TensorProduct.tmul_smul]
          change (((r1, 0) : R1 × R2) • (1 : R2)) ⊗ₜ[R1 × R2] m = 0
          rw [show ((r1, 0) : R1 × R2) • (1 : R2) = (0 : R2) by
            change (RingHom.snd R1 R2) (r1, 0) * 1 = 0; simp]
          rw [TensorProduct.zero_tmul]
        | add a b ha hb => rw [map_add, TensorProduct.tmul_add, ha, hb, add_zero]
      have hself : (1 : R2) ⊗ₜ[R1 × R2] (g2 x.snd) = x.snd := by
        induction x.snd using TensorProduct.induction_on with
        | zero => simp
        | tmul r2 m =>
          change (1 : R2) ⊗ₜ[R1 × R2] (((0, r2) : R1 × R2) • m) = r2 ⊗ₜ[R1 × R2] m
          rw [TensorProduct.tmul_smul]
          change (((0, r2) : R1 × R2) • (1 : R2)) ⊗ₜ[R1 × R2] m = r2 ⊗ₜ[R1 × R2] m
          rw [show ((0, r2) : R1 × R2) • (1 : R2) = r2 by
            change (RingHom.snd R1 R2) (0, r2) * 1 = r2; simp]
        | add a b ha hb => rw [map_add, TensorProduct.tmul_add, ha, hb]
      rw [hcross, hself, zero_add]

-- needed: `K0_product_left_inv`'s `FreeAbelianGroup` induction leaves the `H.zero` goal unless
-- the quotient's `HAdd` instance is defeq to the target's at `default` transparency
set_option backward.isDefEq.respectTransparency false in
/-- **(C-left) `ψ ∘ φ = id` on K₀.**  Given any forward `φ` and backward `ψ`
with their characterizing values on generators, their composite (in this order)
is the identity of `K₀(R₁×R₂)`.

PROOF SKETCH: both `ψ ∘ φ` and `id` are additive, and `K0 (R1×R2)` is generated
by the classes `K0.mk M` (`K0` is a quotient of `FreeAbelianGroup (FGProj _)`;
use the induction principle for the free abelian group + quotient surjectivity,
e.g. `QuotientAddGroup.induction_on` then `FreeAbelianGroup.induction_on`).  On a
generator: `ψ (φ (mk M)) = ψ (mk (M⊗R₁), mk (M⊗R₂))`
`= ψ (mk (M⊗R₁),0) + ψ (0, mk (M⊗R₂))` (additivity, splitting the pair)
`= mk ((M⊗R₁).restrict fst) + mk ((M⊗R₂).restrict snd)`  (by `hψ`)
`= mk (((M⊗R₁).restrict fst).directSum ((M⊗R₂).restrict snd))` (`K0.mk_directSum_eq`)
`= mk M`  (`K0.mk_eq_of_iso`, via the IDEMPOTENT DECOMPOSITION isomorphism
`M ≅ (M⊗_R R₁)|_R ⊕ (M⊗_R R₂)|_R` of `R`-modules: `M ≅ e₁M ⊕ e₂M` with
`eᵢM ≅ M ⊗_R Rᵢ`; Mathlib: the `R = R₁×R₂`-module decomposition via the
idempotents, `LinearEquiv.prodₓ`, `TensorProduct` cancellation). -/
theorem K0_product_left_inv (R1 R2 : Type u) [CommRing R1] [CommRing R2]
    (φ : K0 (R1 × R2) →+ (K0 R1 × K0 R2)) (ψ : (K0 R1 × K0 R2) →+ K0 (R1 × R2))
    (hφ : ∀ M : FGProj (R1 × R2),
        φ (K0.mk M) =
          ( K0.mk (M.baseChangeHom (RingHom.fst R1 R2)),
            K0.mk (M.baseChangeHom (RingHom.snd R1 R2)) ))
    (hψ1 : ∀ N1 : FGProj R1, ψ (K0.mk N1, 0) =
        K0.mk (N1.restrict (RingHom.fst R1 R2) (Prod.fst_finite R1 R2) (Prod.fst_projective R1 R2)))
    (hψ2 : ∀ N2 : FGProj R2, ψ (0, K0.mk N2) =
        K0.mk (N2.restrict (RingHom.snd R1 R2) (Prod.snd_finite R1 R2) (Prod.snd_projective R1
            R2))) :
    ∀ x : K0 (R1 × R2), ψ (φ x) = x := by
  suffices h : ψ.comp φ = AddMonoidHom.id _ from fun x => DFunLike.congr_fun h x
  refine K0_hom_ext fun M => ?_
  change ψ (φ (K0.mk M)) = K0.mk M
  rw [hφ M]
  set M1 := M.baseChangeHom (RingHom.fst R1 R2) with hM1
  set M2 := M.baseChangeHom (RingHom.snd R1 R2) with hM2
  have hsplit : ((K0.mk M1, K0.mk M2) : K0 R1 × K0 R2) = (K0.mk M1, 0) + (0, K0.mk M2) := by
    ext <;> simp
  rw [hsplit, map_add, hψ1 M1, hψ2 M2,
    ← K0.mk_directSum_eq
      (M1.restrict (RingHom.fst R1 R2) (Prod.fst_finite R1 R2) (Prod.fst_projective R1 R2))
      (M2.restrict (RingHom.snd R1 R2) (Prod.snd_finite R1 R2) (Prod.snd_projective R1 R2))]
  exact K0.mk_eq_of_iso _ M (K0_product_idem_iso R1 R2 M)

set_option backward.isDefEq.respectTransparency false in
/-- If `φ : K₀(R₁ × R₂) → K₀(R₁) × K₀(R₂)` and `ψ` in the other direction act on classes
by base change and by restriction of scalars, then `φ ∘ ψ` is the identity. -/
theorem K0_product_right_inv (R1 R2 : Type u) [CommRing R1] [CommRing R2]
    (φ : K0 (R1 × R2) →+ (K0 R1 × K0 R2)) (ψ : (K0 R1 × K0 R2) →+ K0 (R1 × R2))
    (hφ : ∀ M : FGProj (R1 × R2),
        φ (K0.mk M) =
          ( K0.mk (M.baseChangeHom (RingHom.fst R1 R2)),
            K0.mk (M.baseChangeHom (RingHom.snd R1 R2)) ))
    (hψ1 : ∀ N1 : FGProj R1, ψ (K0.mk N1, 0) =
        K0.mk (N1.restrict (RingHom.fst R1 R2) (Prod.fst_finite R1 R2) (Prod.fst_projective R1 R2)))
    (hψ2 : ∀ N2 : FGProj R2, ψ (0, K0.mk N2) =
        K0.mk (N2.restrict (RingHom.snd R1 R2) (Prod.snd_finite R1 R2) (Prod.snd_projective R1
            R2))) :
    ∀ y : K0 R1 × K0 R2, φ (ψ y) = y := by
  -- It suffices to check on generators (mk N1, 0) and (0, mk N2).
  have hgen1 : ∀ N1 : FGProj R1, φ (ψ (K0.mk N1, 0)) = (K0.mk N1, 0) := by
    intro N1
    rw [hψ1 N1, hφ]
    refine Prod.ext ?_ ?_
    · exact K0.mk_eq_of_iso _ N1 (Prod.tensorFstEquiv R1 R2 N1.carrier)
    · have : Subsingleton ((N1.restrict (RingHom.fst R1 R2) (Prod.fst_finite R1 R2)
        (Prod.fst_projective R1 R2)).baseChangeHom (RingHom.snd R1 R2)).carrier :=
        Prod.subsingleton_tensor_snd_of_fst R1 R2 N1.carrier
      exact K0.mk_eq_zero_of_subsingleton _
  have hgen2 : ∀ N2 : FGProj R2, φ (ψ (0, K0.mk N2)) = (0, K0.mk N2) := by
    intro N2
    rw [hψ2 N2, hφ]
    refine Prod.ext ?_ ?_
    · have : Subsingleton ((N2.restrict (RingHom.snd R1 R2) (Prod.snd_finite R1 R2)
        (Prod.snd_projective R1 R2)).baseChangeHom (RingHom.fst R1 R2)).carrier :=
        Prod.subsingleton_tensor_fst_of_snd R1 R2 N2.carrier
      exact K0.mk_eq_zero_of_subsingleton _
    · exact K0.mk_eq_of_iso _ N2 (Prod.tensorSndEquiv R1 R2 N2.carrier)
  intro y
  have hl := DFunLike.congr_fun (K0_hom_ext (f := (φ.comp ψ).comp (AddMonoidHom.inl _ _))
    (g := AddMonoidHom.inl _ _) hgen1) y.1
  have hr := DFunLike.congr_fun (K0_hom_ext (f := (φ.comp ψ).comp (AddMonoidHom.inr _ _))
    (g := AddMonoidHom.inr _ _) hgen2) y.2
  have hy : y = (y.1, 0) + (0, y.2) := by ext <;> simp
  rw [hy, map_add, map_add]
  exact congr_arg₂ (· + ·) hl hr

/-- For a product ring `R = R₁ × R₂`, the natural
homomorphism `K₀(R) → K₀(R₁) × K₀(R₂)`, given on generators by
`[M] ↦ ([M ⊗_R R₁], [M ⊗_R R₂])` (base change along the two projections), is an
isomorphism of abelian groups.

The product map is characterized by its values on the generating classes
`K0.mk M`; since these generate `K0 (R₁ × R₂)`, the additive isomorphism `e`
below is unique with the stated property, so this faithfully expresses that the
product map is an isomorphism. -/
@[stacks 00JH "K_0"]
theorem K0_product (R1 R2 : Type u) [CommRing R1] [CommRing R2] :
    ∃ e : K0 (R1 × R2) ≃+ (K0 R1 × K0 R2),
      ∀ M : FGProj (R1 × R2),
        e (K0.mk M) =
          ( K0.mk (M.baseChangeHom (RingHom.fst R1 R2)),
            K0.mk (M.baseChangeHom (RingHom.snd R1 R2)) ) := by
  -- Assemble the isomorphism from the forward map, backward map, and the two
  -- round-trip identities (the genuine mathematical content lives in those
  -- four sub-lemmas; this is pure glue).
  obtain ⟨φ, hφ⟩ := K0_product_forward R1 R2
  obtain ⟨ψ, hψ1, hψ2⟩ := K0_product_backward R1 R2
  exact ⟨{ toFun := φ, invFun := ψ, map_add' := φ.map_add,
           left_inv := K0_product_left_inv R1 R2 φ ψ hφ hψ1 hψ2,
           right_inv := K0_product_right_inv R1 R2 φ ψ hφ hψ1 hψ2 }, hφ⟩
