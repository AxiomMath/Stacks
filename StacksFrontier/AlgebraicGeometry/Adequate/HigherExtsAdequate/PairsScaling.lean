module

public import StacksFrontier.AlgebraicGeometry.Adequate.HigherExtsAdequate.DualScalingPair
public import StacksFrontier.AlgebraicGeometry.Adequate.HigherExtsAdequate.PairsWeightOne
public import StacksFrontier.CategoryTheory.Abelian.ExtMapFunctorial

/-!
# The dual-number scaling on module-valued functors on pairs

Restriction along the dual-number pair functor `T : (C, V) ↦ (C[ε], V ⊕ εV)` is an exact
endofunctor `T^*` of module-valued functors on pairs. The natural maps of pairs
`(C, V) → (C[ε], V ⊕ εV)`, `v ↦ (v, 0)` and `v ↦ (0, v)`, give natural transformations
`p, a : 𝟭 ⟶ T^*`, and multiplication by `ε` gives `τ : T^* ⟶ T^*`. On the tautological functor
`V`, `a = p ≫ τ`, since `(0, v) = ε (v, 0)`.

For `ψ_N^* M̲ : (C, V) ↦ Sym_C(V ⊗_A N) ⊗_A M`, the `ε`-coefficient gives a retraction
`π : T^* ψ_N^* M̲ ⟶ ψ_N^* M̲` of `p ≫ τ` with `a ≫ π` the weight-one projection
(`AdequateFunctor.pairsWeightOneProjection`). By
`Stacks.ExtFunctorial.comp_mk₀_eq_self_of_app_eq_comp` every class in `Ext^n(V, ψ_N^* M̲)` is
therefore unchanged by the weight-one projection.

## Main definitions

* `AdequateFunctor.dualScaling`: the exact endofunctor `T^*`.
* `AdequateFunctor.dualScalingInl`, `AdequateFunctor.dualScalingInr`: `p` and `a`.
* `AdequateFunctor.dualScalingEps`: `τ`.
* `AdequateFunctor.dualRetraction`: `π`.

## Main results

* `AdequateFunctor.dualScalingInr_app_tautological`: `a = p ≫ τ` on `V`.
* `AdequateFunctor.dualScalingInl_comp_eps_comp_retraction`: `p ≫ τ ≫ π = 𝟙`.
* `AdequateFunctor.dualScalingInr_comp_retraction`: `a ≫ π = Π`.
* `AdequateFunctor.ext_comp_pairsWeightOneProjection`: `ξ ∘ Π = ξ` for `ξ ∈ Ext^n(V, ψ_N^* M̲)`.
-/

@[expose] public section

universe t w' w v u

open CategoryTheory Opposite TrivSqZeroExt
open scoped TensorProduct

namespace AdequateFunctor

section Endofunctor

variable (A : Type u) [CommRing A]

/-- The inclusions `C → C[ε]`, comparing the ring diagram of pairs with itself along the
dual-number pair functor. -/
noncomputable def dualNumberRingHom :
    pairRingDiagram.{v} A ⟶ (dualNumberPairFunctor.{u, max u v} (A := A)).op.op ⋙
      pairRingDiagram.{v} A where
  app X := RingCat.ofHom (inlAlgHom A X.unop.unop.algebra X.unop.unop.algebra).toRingHom
  naturality {X Y} g := by
    refine RingCat.hom_ext (RingHom.ext fun c => ?_)
    exact TrivSqZeroExt.ext rfl (map_zero g.unop.unop.base).symm

/-- **The dual-number scaling** `T^*`: restriction along `(C, V) ↦ (C[ε], V ⊕ εV)`. -/
noncomputable abbrev dualScaling :
    PairModuleValuedFunctor.{w, v} A ⥤ PairModuleValuedFunctor.{w, v} A :=
  PresheafOfModules.pushforward.{w} (dualNumberRingHom.{v} A)

open Stacks.AlgebraicGeometry.RestrictionExact CategoryTheory.Limits in
/-- `T^*` is additive. -/
instance dualScaling_additive : (dualScaling.{w, v} A).Additive :=
  additive_presheafPushforward _

open Stacks.AlgebraicGeometry.RestrictionExact CategoryTheory.Limits in
/-- `T^*` preserves finite limits. -/
instance dualScaling_preservesFiniteLimits : PreservesFiniteLimits (dualScaling.{w, v} A) :=
  preservesFiniteLimits_presheafPushforward _

open CategoryTheory.Limits in
/-- `T^*` preserves finite colimits. -/
instance dualScaling_preservesFiniteColimits : PreservesFiniteColimits (dualScaling.{w, v} A) :=
  preservesFiniteColimits_presheafPushforward _

variable {A}

/-- A natural transformation `𝟭 ⟶ T^*` from natural maps of pairs `X → (C[ε], V ⊕ εV)` lying
over `C → C[ε]`. -/
noncomputable def dualScalingNatTrans
    (κ : ∀ X : AlgebraModulePair.{max u v} A, X ⟶ dualNumberPair X)
    (hbase : ∀ X, (κ X).base = inlAlgHom A X.algebra X.algebra)
    (hnat : ∀ {X Y : AlgebraModulePair.{max u v} A} (g : X ⟶ Y),
      g ≫ κ Y = κ X ≫ dualNumberPairMap g) :
    𝟭 (PairModuleValuedFunctor.{w, v} A) ⟶ dualScaling.{w, v} A where
  app Z :=
    { app X := ModuleCat.ofHom (X := Z.obj X) (Y := ((dualScaling.{w, v} A).obj Z).obj X)
        { toFun := fun z => Z.map (κ X.unop.unop).op.op z
          map_add' := fun z z' => map_add (Z.map (κ X.unop.unop).op.op).hom z z'
          map_smul' := fun c z => by
            refine (PresheafOfModules.map_smul Z (κ X.unop.unop).op.op c z).trans ?_
            change (κ X.unop.unop).base c • _ = _
            rw [hbase]
            rfl }
      naturality {X Y} g := by
        ext z
        change Z.map (κ Y.unop.unop).op.op (Z.map g z) =
          Z.map (dualNumberPairMap g.unop.unop).op.op (Z.map (κ X.unop.unop).op.op z)
        rw [← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply]
        refine Z.congr_map_apply ?_ z
        exact congrArg (fun f => f.op.op) (hnat g.unop.unop) }
  naturality Z Z' α := by
    refine PresheafOfModules.hom_ext fun X => ?_
    ext z
    exact (PresheafOfModules.naturality_apply α (κ X.unop.unop).op.op z).symm

/-- `p : 𝟭 ⟶ T^*`, from `v ↦ (v, 0)`. -/
noncomputable abbrev dualScalingInl : 𝟭 (PairModuleValuedFunctor.{w, v} A) ⟶ dualScaling.{w, v} A :=
  dualScalingNatTrans dualNumberPairInl (fun _ => rfl) dualNumberPairInl_naturality

/-- `a : 𝟭 ⟶ T^*`, from `v ↦ (0, v) = ε v`. -/
noncomputable abbrev dualScalingInr : 𝟭 (PairModuleValuedFunctor.{w, v} A) ⟶ dualScaling.{w, v} A :=
  dualScalingNatTrans dualNumberPairInr (fun _ => rfl) dualNumberPairInr_naturality

/-- Multiplication by `ε` on the value of a module-valued functor on pairs at a dual-number
pair. -/
noncomputable def dualEpsSmul (Z : PairModuleValuedFunctor.{w, v} A)
    (X : AlgebraModulePair.{max u v} A) :
    Z.obj (op (op (dualNumberPair X))) →ₗ[(dualNumberPair X).algebra]
      Z.obj (op (op (dualNumberPair X))) :=
  { toFun := fun z => dualEps X • z
    map_add' := fun z z' => smul_add _ z z'
    map_smul' := fun c z => smul_comm _ c z }

/-- `dualEpsSmul Z X` is multiplication by `ε`. -/
lemma dualEpsSmul_apply (Z : PairModuleValuedFunctor.{w, v} A) (X : AlgebraModulePair.{max u v} A)
    (z : Z.obj (op (op (dualNumberPair X)))) :
    dualEpsSmul Z X z = dualEps X • z := rfl

/-- Multiplication by `ε` commutes with the map `Z(T g)` induced by a map of pairs `g`. -/
lemma dualEpsSmul_map (Z : PairModuleValuedFunctor.{w, v} A) {X Y : AlgebraModulePair.{max u v} A}
    (g : X ⟶ Y) (z : Z.obj (op (op (dualNumberPair X)))) :
    (Z.map (dualNumberPairMap g).op.op (dualEpsSmul Z X z) : Z.obj (op (op (dualNumberPair Y)))) =
      dualEpsSmul Z Y (Z.map (dualNumberPairMap g).op.op z) := by
  have h : (pairRingDiagram.{v} A).map (dualNumberPairMap g).op.op
      (dualEps X) = dualEps Y :=
    TrivSqZeroExt.ext (map_zero g.base) (map_one g.base)
  exact (PresheafOfModules.map_smul Z (dualNumberPairMap g).op.op
    (dualEps X) z).trans
      (congrArg (fun r => r • Z.map (dualNumberPairMap g).op.op z) h)

/-- `τ : T^* ⟶ T^*`, multiplication by `ε`. -/
noncomputable def dualScalingEps : dualScaling.{w, v} A ⟶ dualScaling.{w, v} A where
  app Z :=
    { app X := ModuleCat.ofHom (X := ((dualScaling.{w, v} A).obj Z).obj X)
        (Y := ((dualScaling.{w, v} A).obj Z).obj X)
        { toFun := fun z => dualEpsSmul Z X.unop.unop z
          map_add' := fun z z' => map_add (dualEpsSmul Z X.unop.unop) z z'
          map_smul' := fun c z => (dualEpsSmul Z X.unop.unop).map_smul (inl c) z }
      naturality {X Y} g := by
        ext z
        exact (dualEpsSmul_map Z g.unop.unop z).symm }
  naturality {Z Z'} α := by
    refine PresheafOfModules.hom_ext fun X => ?_
    ext z
    exact ((α.app (op (op (dualNumberPair X.unop.unop)))).hom.map_smul
      (dualEps X.unop.unop) z).symm

/-- **On the tautological functor, `a = p ≫ τ`**: `(0, v) = ε (v, 0)`. -/
lemma dualScalingInr_app_tautological :
    (dualScalingInr.{max (u + 1) (v + 1) w, v} (A := A)).app (tautologicalPairModule.{w, v} A) =
      (dualScalingInl.{max (u + 1) (v + 1) w, v} (A := A)).app (tautologicalPairModule.{w, v} A) ≫
        (dualScalingEps.{max (u + 1) (v + 1) w, v} (A := A)).app
          (tautologicalPairModule.{w, v} A) := by
  refine PresheafOfModules.hom_ext fun X => ?_
  ext z
  exact ULift.ext (dualNumberPairInr_eq_eps_smul X.unop.unop z.down)

end Endofunctor

section Retraction

variable {A : Type u} [CommRing A] (N : Type (max u v)) [AddCommGroup N] [Module A N]

attribute [local instance] symPairAlgebra

/-- The symmetric algebra `Sym_C(V ⊗_A N)` of a pair. -/
abbrev pairSym (X : AlgebraModulePair.{max u v} A) : Type (max u v) :=
  SymmetricAlgebra X.algebra (X.module ⊗[A] N)

/-- The `A`-algebra structure of the dual numbers `Sym_C(V ⊗_A N)[ε]`. -/
@[instance_reducible]
noncomputable def pairSymDualAlgebra (X : AlgebraModulePair.{max u v} A) :
    Algebra A (TrivSqZeroExt (pairSym N X) (pairSym N X)) :=
  TrivSqZeroExt.algebra' A (pairSym N X) (pairSym N X)

attribute [local instance] pairSymDualAlgebra

/-- The `ε`-expansion `(x₀, x₁) ⊗ n ↦ ι(x₀ ⊗ n) + ε ι(x₁ ⊗ n)` on pure tensors. -/
noncomputable def dualExpandBil (X : AlgebraModulePair.{max u v} A) :
    (dualNumberPair X).module →ₗ[A] N →ₗ[A] TrivSqZeroExt (pairSym N X) (pairSym N X) :=
  LinearMap.mk₂ A
    (fun x n => inl (SymmetricAlgebra.ι X.algebra (X.module ⊗[A] N) (dualCoordFst X x ⊗ₜ n)) +
      inr (SymmetricAlgebra.ι X.algebra (X.module ⊗[A] N) (dualCoordSnd X x ⊗ₜ n)))
    (fun x y n => by
      simp only [map_add, TensorProduct.add_tmul, inl_add, inr_add]
      abel)
    (fun a x n => by
      apply TrivSqZeroExt.ext
      · simp only [fst_add, fst_inl, fst_inr, add_zero, dualCoordFst_smul_base, fst_smul]
        rw [← TensorProduct.smul_tmul', LinearMap.map_smul_of_tower]
        rfl
      · simp only [snd_add, snd_inl, snd_inr, zero_add, dualCoordSnd_smul_base, snd_smul]
        rw [← TensorProduct.smul_tmul', LinearMap.map_smul_of_tower]
        rfl)
    (fun x n n' => by
      simp only [TensorProduct.tmul_add, map_add, inl_add, inr_add]
      abel)
    (fun a x n => by
      apply TrivSqZeroExt.ext
      · simp only [fst_add, fst_inl, fst_inr, add_zero, fst_smul]
        rw [TensorProduct.tmul_smul, LinearMap.map_smul_of_tower]
        rfl
      · simp only [snd_add, snd_inl, snd_inr, zero_add, snd_smul]
        rw [TensorProduct.tmul_smul, LinearMap.map_smul_of_tower]
        rfl)

/-- The `ε`-expansion `(V ⊕ εV) ⊗_A N → Sym_C(V ⊗_A N)[ε]`, as an `A`-linear map. -/
noncomputable def dualExpandA (X : AlgebraModulePair.{max u v} A) :
    (dualNumberPair X).module ⊗[A] N →ₗ[A] TrivSqZeroExt (pairSym N X) (pairSym N X) :=
  TensorProduct.lift (dualExpandBil N X)

/-- The `ε`-expansion of a pure tensor `x ⊗ n` is `ι(x₀ ⊗ n) + ε ι(x₁ ⊗ n)`, where
`x₀ = dualCoordFst X x` and `x₁ = dualCoordSnd X x`. -/
lemma dualExpandA_tmul (X : AlgebraModulePair.{max u v} A) (x : (dualNumberPair X).module)
    (n : N) :
    dualExpandA N X (x ⊗ₜ n) =
      inl (SymmetricAlgebra.ι _ _ (dualCoordFst X x ⊗ₜ n)) +
        inr (SymmetricAlgebra.ι _ _ (dualCoordSnd X x ⊗ₜ n)) := rfl

/-- The dual numbers of the structure map `C → Sym_C(V ⊗_A N)`. -/
noncomputable abbrev dualSymBase (X : AlgebraModulePair.{max u v} A) :
    (dualNumberPair X).algebra →ₐ[A] TrivSqZeroExt (pairSym N X) (pairSym N X) :=
  dualNumberAlgHom (symAlgebraMap X.algebra (X.module ⊗[A] N))

/-- The scalar component of `dualSymBase N X q` is the image of the scalar component of
`q`. -/
lemma dualSymBase_fst (X : AlgebraModulePair.{max u v} A) (q : (dualNumberPair X).algebra) :
    (dualSymBase N X q).fst = algebraMap X.algebra (pairSym N X) (dualAlgFst X q) := rfl

/-- The `ε`-component of `dualSymBase N X q` is the image of the `ε`-component of `q`. -/
lemma dualSymBase_snd (X : AlgebraModulePair.{max u v} A) (q : (dualNumberPair X).algebra) :
    (dualSymBase N X q).snd = algebraMap X.algebra (pairSym N X) (dualAlgSnd X q) := rfl

/-- The `ε`-expansion as a semilinear map over the dual numbers. -/
noncomputable def dualExpand (X : AlgebraModulePair.{max u v} A) :
    (dualNumberPair X).module ⊗[A] N →ₛₗ[(dualSymBase N X).toRingHom]
      TrivSqZeroExt (pairSym N X) (pairSym N X) where
  toFun := dualExpandA N X
  map_add' := map_add _
  map_smul' q t := by
    induction t using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | tmul x n =>
      rw [TensorProduct.smul_tmul', dualExpandA_tmul, dualExpandA_tmul, smul_eq_mul]
      apply TrivSqZeroExt.ext
      · rw [fst_mul, fst_add, fst_add, fst_inl, fst_inl, fst_inr, fst_inr, add_zero, add_zero,
          dualCoordFst_smul, ← TensorProduct.smul_tmul', LinearMap.map_smul]
        exact Algebra.smul_def _ _
      · rw [snd_mul, snd_add, snd_add, snd_inl, snd_inl, snd_inr, snd_inr, zero_add, zero_add,
          fst_add, fst_inl, fst_inr, add_zero, dualCoordSnd_smul, TensorProduct.add_tmul,
          map_add, ← TensorProduct.smul_tmul', ← TensorProduct.smul_tmul', LinearMap.map_smul,
          LinearMap.map_smul, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
        exact congrArg₂ (· + ·) (Algebra.smul_def _ _)
          (Algebra.smul_def _ _)
    | add t t' ht ht' => rw [smul_add, map_add, map_add, ht, ht', smul_add]

/-- **The `ε`-expansion of the symmetric algebra of a dual-number pair**,
`Sym_{C[ε]}((V ⊕ εV) ⊗_A N) → Sym_C(V ⊗_A N)[ε]`. -/
noncomputable def dualExpandSym (X : AlgebraModulePair.{max u v} A) :
    SymmetricAlgebra (dualNumberPair X).algebra ((dualNumberPair X).module ⊗[A] N) →ₐ[A]
      TrivSqZeroExt (pairSym N X) (pairSym N X) :=
  symLift (dualSymBase N X) (dualExpand N X)

/-- On scalars, `dualExpandSym N X` is `dualSymBase N X`. -/
lemma dualExpandSym_algebraMap (X : AlgebraModulePair.{max u v} A)
    (q : (dualNumberPair X).algebra) :
    dualExpandSym N X (algebraMap _
        (SymmetricAlgebra (dualNumberPair X).algebra ((dualNumberPair X).module ⊗[A] N)) q) =
      dualSymBase N X q :=
  symLift_algebraMap _ _ q

/-- On generators, `dualExpandSym N X` is `dualExpandA N X`. -/
lemma dualExpandSym_ι (X : AlgebraModulePair.{max u v} A) (t : (dualNumberPair X).module ⊗[A] N) :
    dualExpandSym N X (SymmetricAlgebra.ι _ _ t) = dualExpandA N X t :=
  symLift_ι _ _ t

/-- On the image of `v ↦ (v, 0)`, the `ε`-expansion is the inclusion `s ↦ s`. -/
lemma dualExpandSym_symPairMap_inl (X : AlgebraModulePair.{max u v} A) (s : pairSym N X) :
    dualExpandSym N X (symPairMap N (dualNumberPairInl X) s) = inl s := by
  induction s using SymmetricAlgebra.induction with
  | algebraMap c =>
    refine (congrArg (dualExpandSym N X)
      (symPairMap_algebraMap N (dualNumberPairInl X) c)).trans ?_
    rw [dualExpandSym_algebraMap]
    exact TrivSqZeroExt.ext rfl (map_zero _)
  | ι t =>
    rw [symPairMap_ι, dualExpandSym_ι]
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero, inl_zero]
    | tmul x n =>
      rw [pairTensorMap_tmul, dualExpandA_tmul, dualCoordFst_inl, dualCoordSnd_inl,
        TensorProduct.zero_tmul, map_zero, inr_zero, add_zero]
    | add t t' ht ht' => rw [map_add, map_add, ht, ht', map_add, inl_add]
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb, inl_mul]
  | add a b ha hb => rw [map_add, map_add, ha, hb, inl_add]

/-- On the image of `v ↦ (0, v)`, the `ε`-expansion is the weight coaction `w ↦ ε w`. -/
lemma dualExpandSym_symPairMap_inr (X : AlgebraModulePair.{max u v} A) (s : pairSym N X) :
    dualExpandSym N X (symPairMap N (dualNumberPairInr X) s) =
      symmetricWeightCoaction X.algebra (X.module ⊗[A] N) s := by
  induction s using SymmetricAlgebra.induction with
  | algebraMap c =>
    refine (congrArg (dualExpandSym N X)
      (symPairMap_algebraMap N (dualNumberPairInr X) c)).trans ?_
    rw [dualExpandSym_algebraMap, AlgHom.commutes]
    exact TrivSqZeroExt.ext rfl (map_zero _)
  | ι t =>
    rw [symPairMap_ι, dualExpandSym_ι]
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x n =>
      rw [pairTensorMap_tmul, dualExpandA_tmul, dualCoordFst_inr, dualCoordSnd_inr,
        TensorProduct.zero_tmul, map_zero, inl_zero, zero_add, symmetricWeightCoaction,
        SymmetricAlgebra.lift_ι_apply]
      rfl
    | add t t' ht ht' =>
      rw [map_add, map_add, ht, ht', map_add (SymmetricAlgebra.ι X.algebra (X.module ⊗[A] N)),
        map_add (symmetricWeightCoaction X.algebra (X.module ⊗[A] N))]
  | mul a b ha hb =>
    rw [map_mul, map_mul, ha, hb]
    exact (map_mul (symmetricWeightCoaction X.algebra (X.module ⊗[A] N)) _ _).symm
  | add a b ha hb =>
    rw [map_add, map_add, ha, hb]
    exact (map_add (symmetricWeightCoaction X.algebra (X.module ⊗[A] N)) _ _).symm

/-- The scalar component of `Sym_C(V ⊗_A N)[ε]`, as an `A`-linear map. -/
def dualSymFst (X : AlgebraModulePair.{max u v} A) :
    TrivSqZeroExt (pairSym N X) (pairSym N X) →ₗ[A] pairSym N X where
  toFun := TrivSqZeroExt.fst
  map_add' := TrivSqZeroExt.fst_add
  map_smul' _ _ := rfl

/-- The `ε`-component of `Sym_C(V ⊗_A N)[ε]`, as an `A`-linear map. -/
def dualSymSnd (X : AlgebraModulePair.{max u v} A) :
    TrivSqZeroExt (pairSym N X) (pairSym N X) →ₗ[A] pairSym N X where
  toFun := TrivSqZeroExt.snd
  map_add' := TrivSqZeroExt.snd_add
  map_smul' _ _ := rfl

/-- `dualSymSnd N X` is the `ε`-component `x ↦ x.snd`. -/
@[simp] lemma dualSymSnd_apply (X : AlgebraModulePair.{max u v} A)
    (x : TrivSqZeroExt (pairSym N X) (pairSym N X)) : dualSymSnd N X x = x.snd := rfl

/-- On generators, the `ε`-expansion is natural in the pair. -/
lemma dualExpandA_naturality {X Y : AlgebraModulePair.{max u v} A} (g : X ⟶ Y)
    (t : (dualNumberPair X).module ⊗[A] N) :
    (dualExpandA N Y (pairTensorMap N (dualNumberPairMap g) t)).fst =
        symPairMap N g (dualExpandA N X t).fst ∧
      (dualExpandA N Y (pairTensorMap N (dualNumberPairMap g) t)).snd =
        symPairMap N g (dualExpandA N X t).snd := by
  have hT : ∀ t, pairTensorMap N (dualNumberPairMap g) t =
      TensorProduct.map (pairLinearA (dualNumberPairMap g)) LinearMap.id t := fun _ => rfl
  simp only [hT]
  refine ⟨congrArg (fun F => F t) (TensorProduct.ext' (g := dualSymFst N Y ∘ₗ dualExpandA N Y ∘ₗ
      TensorProduct.map (pairLinearA (dualNumberPairMap g)) LinearMap.id)
    (h := (symPairMap N g).toLinearMap ∘ₗ dualSymFst N X ∘ₗ dualExpandA N X) fun x n => ?_),
    congrArg (fun F => F t) (TensorProduct.ext' (g := dualSymSnd N Y ∘ₗ dualExpandA N Y ∘ₗ
      TensorProduct.map (pairLinearA (dualNumberPairMap g)) LinearMap.id)
    (h := (symPairMap N g).toLinearMap ∘ₗ dualSymSnd N X ∘ₗ dualExpandA N X) fun x n => ?_)⟩
  · show (dualExpandA N Y ((dualNumberPairMap g).linear x ⊗ₜ n)).fst =
      symPairMap N g (dualExpandA N X (x ⊗ₜ n)).fst
    rw [dualExpandA_tmul, dualExpandA_tmul, fst_add, fst_add, fst_inl, fst_inl, fst_inr, fst_inr,
      add_zero, add_zero, dualCoordFst_map, symPairMap_ι, pairTensorMap_tmul]
  · show (dualExpandA N Y ((dualNumberPairMap g).linear x ⊗ₜ n)).snd =
      symPairMap N g (dualExpandA N X (x ⊗ₜ n)).snd
    rw [dualExpandA_tmul, dualExpandA_tmul, snd_add, snd_add, snd_inl, snd_inl, snd_inr, snd_inr,
      zero_add, zero_add, dualCoordSnd_map, symPairMap_ι, pairTensorMap_tmul]

/-- On scalars, the scalar component of the `ε`-expansion is natural in the pair. -/
lemma dualExpandSym_algebraMap_fst_naturality {X Y : AlgebraModulePair.{max u v} A} (g : X ⟶ Y)
    (q : (dualNumberPair X).algebra) :
    (dualExpandSym N Y (symPairMap N (dualNumberPairMap g)
        (algebraMap (dualNumberPair X).algebra
          (SymmetricAlgebra (dualNumberPair X).algebra
            ((dualNumberPair X).module ⊗[A] N)) q))).fst =
      symPairMap N g (dualExpandSym N X
        (algebraMap (dualNumberPair X).algebra
          (SymmetricAlgebra (dualNumberPair X).algebra
            ((dualNumberPair X).module ⊗[A] N)) q)).fst := by
  rw [symPairMap_algebraMap, dualExpandSym_algebraMap, dualExpandSym_algebraMap, dualSymBase_fst,
    dualSymBase_fst, dualAlgFst_map]
  exact (symPairMap_algebraMap N g _).symm

/-- On scalars, the `ε`-component of the `ε`-expansion is natural in the pair. -/
lemma dualExpandSym_algebraMap_snd_naturality {X Y : AlgebraModulePair.{max u v} A} (g : X ⟶ Y)
    (q : (dualNumberPair X).algebra) :
    (dualExpandSym N Y (symPairMap N (dualNumberPairMap g)
        (algebraMap (dualNumberPair X).algebra
          (SymmetricAlgebra (dualNumberPair X).algebra
            ((dualNumberPair X).module ⊗[A] N)) q))).snd =
      symPairMap N g (dualExpandSym N X
        (algebraMap (dualNumberPair X).algebra
          (SymmetricAlgebra (dualNumberPair X).algebra
            ((dualNumberPair X).module ⊗[A] N)) q)).snd := by
  rw [symPairMap_algebraMap, dualExpandSym_algebraMap, dualExpandSym_algebraMap, dualSymBase_snd,
    dualSymBase_snd, dualAlgSnd_map]
  exact (symPairMap_algebraMap N g _).symm

/-- On generators, the scalar component of the `ε`-expansion is natural in the pair. -/
lemma dualExpandSym_ι_fst_naturality {X Y : AlgebraModulePair.{max u v} A} (g : X ⟶ Y)
    (t : (dualNumberPair X).module ⊗[A] N) :
    (dualExpandSym N Y (symPairMap N (dualNumberPairMap g)
        (SymmetricAlgebra.ι (dualNumberPair X).algebra ((dualNumberPair X).module ⊗[A] N) t))).fst =
      symPairMap N g (dualExpandSym N X
        (SymmetricAlgebra.ι (dualNumberPair X).algebra
          ((dualNumberPair X).module ⊗[A] N) t)).fst := by
  rw [symPairMap_ι, dualExpandSym_ι, dualExpandSym_ι]
  exact (dualExpandA_naturality N g t).1

/-- On generators, the `ε`-component of the `ε`-expansion is natural in the pair. -/
lemma dualExpandSym_ι_snd_naturality {X Y : AlgebraModulePair.{max u v} A} (g : X ⟶ Y)
    (t : (dualNumberPair X).module ⊗[A] N) :
    (dualExpandSym N Y (symPairMap N (dualNumberPairMap g)
        (SymmetricAlgebra.ι (dualNumberPair X).algebra ((dualNumberPair X).module ⊗[A] N) t))).snd =
      symPairMap N g (dualExpandSym N X
        (SymmetricAlgebra.ι (dualNumberPair X).algebra
          ((dualNumberPair X).module ⊗[A] N) t)).snd := by
  rw [symPairMap_ι, dualExpandSym_ι, dualExpandSym_ι]
  exact (dualExpandA_naturality N g t).2

/-- The scalar component of the `ε`-expansion is natural in the pair. -/
lemma dualExpandSym_fst_naturality {X Y : AlgebraModulePair.{max u v} A} (g : X ⟶ Y)
    (s : SymmetricAlgebra (dualNumberPair X).algebra ((dualNumberPair X).module ⊗[A] N)) :
    (dualExpandSym N Y (symPairMap N (dualNumberPairMap g) s)).fst =
      symPairMap N g (dualExpandSym N X s).fst := by
  induction s using SymmetricAlgebra.induction with
  | algebraMap q => exact dualExpandSym_algebraMap_fst_naturality N g q
  | ι t =>
    rw [symPairMap_ι, dualExpandSym_ι, dualExpandSym_ι]
    exact (dualExpandA_naturality N g t).1
  | mul a b ha hb =>
    rw [map_mul, map_mul, map_mul, TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_mul, ha, hb, map_mul]
  | add a b ha hb =>
    rw [map_add, map_add, map_add, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_add, ha, hb, map_add]

/-- The `ε`-component of the `ε`-expansion is natural in the pair. -/
lemma dualExpandSym_snd_naturality {X Y : AlgebraModulePair.{max u v} A} (g : X ⟶ Y)
    (s : SymmetricAlgebra (dualNumberPair X).algebra ((dualNumberPair X).module ⊗[A] N)) :
    (dualExpandSym N Y (symPairMap N (dualNumberPairMap g) s)).snd =
      symPairMap N g (dualExpandSym N X s).snd := by
  induction s using SymmetricAlgebra.induction with
  | algebraMap q => exact dualExpandSym_algebraMap_snd_naturality N g q
  | ι t =>
    rw [symPairMap_ι, dualExpandSym_ι, dualExpandSym_ι]
    exact (dualExpandA_naturality N g t).2
  | mul a b ha hb =>
    rw [map_mul, map_mul, map_mul, TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_mul, ha, hb,
      dualExpandSym_fst_naturality, dualExpandSym_fst_naturality]
    simp only [smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, map_add, map_mul]
  | add a b ha hb =>
    rw [map_add, map_add, map_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_add, ha, hb, map_add]

/-- The `ε`-coefficient of the `ε`-expansion, `Sym_{C[ε]}((V ⊕ εV) ⊗_A N) → Sym_C(V ⊗_A N)`, as an
`A`-linear map. -/
noncomputable def dualExpandSnd (X : AlgebraModulePair.{max u v} A) :
    SymmetricAlgebra (dualNumberPair X).algebra ((dualNumberPair X).module ⊗[A] N) →ₗ[A]
      pairSym N X :=
  dualSymSnd N X ∘ₗ (dualExpandSym N X).toLinearMap

/-- `dualExpandSnd N X s` is the `ε`-component of `dualExpandSym N X s`. -/
lemma dualExpandSnd_apply (X : AlgebraModulePair.{max u v} A)
    (s : SymmetricAlgebra (dualNumberPair X).algebra ((dualNumberPair X).module ⊗[A] N)) :
    dualExpandSnd N X s = (dualExpandSym N X s).snd := rfl

/-- The `ε`-coefficient is natural in the pair. -/
lemma dualExpandSnd_naturality {X Y : AlgebraModulePair.{max u v} A} (g : X ⟶ Y)
    (s : SymmetricAlgebra (dualNumberPair X).algebra ((dualNumberPair X).module ⊗[A] N)) :
    dualExpandSnd N Y (symPairMap N (dualNumberPairMap g) s) =
      symPairMap N g (dualExpandSnd N X s) := by
  rw [dualExpandSnd_apply, dualExpandSnd_apply]
  exact dualExpandSym_snd_naturality N g s

/-- The `ε`-coefficient is linear over `C ⊂ C[ε]`. -/
lemma dualExpandSnd_algebraMap_mul (X : AlgebraModulePair.{max u v} A) (c : X.algebra)
    (s : SymmetricAlgebra (dualNumberPair X).algebra ((dualNumberPair X).module ⊗[A] N)) :
    dualExpandSnd N X (algebraMap (dualNumberPair X).algebra
        (SymmetricAlgebra (dualNumberPair X).algebra ((dualNumberPair X).module ⊗[A] N))
        ((dualNumberPairInl X).base c) * s) =
      algebraMap X.algebra (pairSym N X) c * dualExpandSnd N X s := by
  rw [dualExpandSnd_apply, dualExpandSnd_apply, map_mul, dualExpandSym_algebraMap,
    TrivSqZeroExt.snd_mul, dualSymBase_fst, dualSymBase_snd, dualAlgFst_inl, dualAlgSnd_inl,
    map_zero, MulOpposite.smul_eq_mul_unop, zero_mul, add_zero, smul_eq_mul]

/-- The `ε`-coefficient of `ε · (s, 0)` is `s`. -/
lemma dualExpandSnd_eps_mul_inl (X : AlgebraModulePair.{max u v} A) (s : pairSym N X) :
    dualExpandSnd N X (algebraMap (dualNumberPair X).algebra
        (SymmetricAlgebra (dualNumberPair X).algebra ((dualNumberPair X).module ⊗[A] N))
        (dualEps X) * symPairMap N (dualNumberPairInl X) s) = s := by
  rw [dualExpandSnd_apply, map_mul, dualExpandSym_algebraMap, dualExpandSym_symPairMap_inl,
    TrivSqZeroExt.snd_mul, dualSymBase_fst, dualSymBase_snd, dualAlgFst_eps, dualAlgSnd_eps,
    map_zero, map_one, TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inl, smul_zero, zero_add,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, one_mul]

/-- The `ε`-coefficient of the image of `v ↦ (0, v)` is the weight-one projection. -/
lemma dualExpandSnd_inr (X : AlgebraModulePair.{max u v} A) (s : pairSym N X) :
    dualExpandSnd N X (symPairMap N (dualNumberPairInr X) s) = symPairWeightOne N X s := by
  rw [dualExpandSnd_apply, dualExpandSym_symPairMap_inr, snd_symmetricWeightCoaction]
  rfl

/-- The `ε`-coefficient on values, `Sym_{C[ε]}((V ⊕ εV) ⊗_A N) ⊗_A M → Sym_C(V ⊗_A N) ⊗_A M`. -/
noncomputable def dualCoefficientMap (M : ModuleCat.{w'} A)
    (X : AlgebraModulePair.{max u v} A) :
    (SymmetricAlgebra (dualNumberPair X).algebra ((dualNumberPair X).module ⊗[A] N)) ⊗[A] M →ₗ[A]
      (SymmetricAlgebra X.algebra (X.module ⊗[A] N)) ⊗[A] M :=
  (dualExpandSnd N X).rTensor M

/-- `dualCoefficientMap N M X` applies `dualExpandSnd N X` to the first factor of a pure tensor. -/
lemma dualCoefficientMap_tmul (M : ModuleCat.{w'} A)
    (X : AlgebraModulePair.{max u v} A)
    (s : SymmetricAlgebra (dualNumberPair X).algebra ((dualNumberPair X).module ⊗[A] N)) (m : M) :
    dualCoefficientMap N M X (s ⊗ₜ m) = dualExpandSnd N X s ⊗ₜ m := rfl

/-- On values, `p ≫ τ ≫ π` is the identity (explicit form). -/
lemma dualCoefficientMap_eps_inl (M : ModuleCat.{w'} A)
    (X : AlgebraModulePair.{max u v} A)
    (t : (SymmetricAlgebra X.algebra (X.module ⊗[A] N)) ⊗[A] M) :
    dualCoefficientMap N M X (algebraMap (dualNumberPair X).algebra
        (SymmetricAlgebra (dualNumberPair X).algebra ((dualNumberPair X).module ⊗[A] N))
        (dualEps X) • TensorProduct.map (symPairMap N (dualNumberPairInl X)).toLinearMap
          LinearMap.id t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, smul_zero, map_zero]
  | tmul s m =>
    rw [TensorProduct.map_tmul, TensorProduct.smul_tmul', smul_eq_mul, dualCoefficientMap_tmul,
      AlgHom.toLinearMap_apply, LinearMap.id_apply, dualExpandSnd_eps_mul_inl]
  | add t t' ht ht' => rw [map_add, smul_add, map_add, ht, ht']

/-- On values, `a ≫ π` is the weight-one projection (explicit form). -/
lemma dualCoefficientMap_inr (M : ModuleCat.{w'} A)
    (X : AlgebraModulePair.{max u v} A)
    (t : (SymmetricAlgebra X.algebra (X.module ⊗[A] N)) ⊗[A] M) :
    dualCoefficientMap N M X (TensorProduct.map (symPairMap N (dualNumberPairInr X)).toLinearMap
        LinearMap.id t) = (symPairWeightOne N X).rTensor M t := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul s m =>
    rw [TensorProduct.map_tmul, dualCoefficientMap_tmul, AlgHom.toLinearMap_apply,
      LinearMap.id_apply, dualExpandSnd_inr, LinearMap.rTensor_tmul]
  | add t t' ht ht' => rw [map_add, map_add, ht, ht', map_add]

/-- The map of `ψ_N^* M̲` along a map of pairs `g` is `symPairMap N g ⊗ id_M`. -/
lemma symPairExtension_map_apply (M : ModuleCat.{max (u + 1) (v + 1) w} A)
    {X Y : AlgebraModulePair.{max u v} A} (g : X ⟶ Y)
    (t : (symPairExtension.{w, v} N M).obj (op (op X))) :
    (symPairExtension.{w, v} N M).map g.op.op t =
      (TensorProduct.map (symPairMap N g).toLinearMap LinearMap.id
        (t : (SymmetricAlgebra X.algebra (X.module ⊗[A] N)) ⊗[A] M) :
          (symPairExtension.{w, v} N M).obj (op (op Y))) := rfl

/-- On `ψ_N^* M̲`, multiplication by `ε` is scalar multiplication by the image of `ε` in
`Sym_{C[ε]}((V ⊕ εV) ⊗_A N)`. -/
lemma dualEpsSmul_symPairExtension (M : ModuleCat.{max (u + 1) (v + 1) w} A)
    (X : AlgebraModulePair.{max u v} A)
    (z : (SymmetricAlgebra (dualNumberPair X).algebra ((dualNumberPair X).module ⊗[A] N)) ⊗[A] M) :
    dualEpsSmul (symPairExtension.{w, v} N M) X z =
      (algebraMap (dualNumberPair X).algebra
        (SymmetricAlgebra (dualNumberPair X).algebra ((dualNumberPair X).module ⊗[A] N))
        (dualEps X) • z : (SymmetricAlgebra (dualNumberPair X).algebra
          ((dualNumberPair X).module ⊗[A] N)) ⊗[A] M) := rfl

end Retraction

section RetractionMorphism

variable {A : Type u} [CommRing A] (N : Type (max u v)) [AddCommGroup N] [Module A N]
  (M : ModuleCat.{max (u + 1) (v + 1) w} A)

attribute [local instance] symPairAlgebra pairSymDualAlgebra

attribute [local irreducible] dualNumberPair


/-- On values, the `ε`-coefficient `Sym_{C[ε]}((V ⊕ εV) ⊗_A N) ⊗_A M → Sym_C(V ⊗_A N) ⊗_A M`, typed
with the symmetric algebra of `T(C, V)` spelled through the functor `T`. -/
noncomputable def dualRetractionMap (X : AlgebraModulePair.{max u v} A) :
    (SymmetricAlgebra (dualNumberPairFunctor.obj X).algebra
        ((dualNumberPairFunctor.obj X).module ⊗[A] N)) ⊗[A] M →ₗ[A]
      (SymmetricAlgebra X.algebra (X.module ⊗[A] N)) ⊗[A] M :=
  dualCoefficientMap N M X

/-- `dualRetractionMap N M X` applies `dualExpandSnd N X` to the first factor of a pure tensor. -/
lemma dualRetractionMap_tmul (X : AlgebraModulePair.{max u v} A)
    (s : SymmetricAlgebra (dualNumberPairFunctor.obj X).algebra
        ((dualNumberPairFunctor.obj X).module ⊗[A] N)) (m : M) :
    dualRetractionMap N M X (s ⊗ₜ m) = dualExpandSnd N X s ⊗ₜ m := rfl

/-- The `ε`-coefficient is linear over `C ⊂ C[ε]`, with `C[ε]` spelled through the functor `T`. -/
lemma dualExpandSnd_algebraMap_mul' (X : AlgebraModulePair.{max u v} A) (c : X.algebra)
    (s : SymmetricAlgebra (dualNumberPairFunctor.obj X).algebra
        ((dualNumberPairFunctor.obj X).module ⊗[A] N)) :
    dualExpandSnd N X (algebraMap (dualNumberPairFunctor.obj X).algebra
        (SymmetricAlgebra (dualNumberPairFunctor.obj X).algebra
          ((dualNumberPairFunctor.obj X).module ⊗[A] N))
        (((dualNumberRingHom.{v} A).app (op (op X))).hom c) * s) =
      algebraMap X.algebra (pairSym N X) c * dualExpandSnd N X s :=
  dualExpandSnd_algebraMap_mul N X c s

/-- The `ε`-coefficient is natural in the pair, with `T` spelled as `dualNumberPairFunctor`. -/
lemma dualExpandSnd_naturality' {X Y : AlgebraModulePair.{max u v} A} (g : X ⟶ Y)
    (s : SymmetricAlgebra (dualNumberPairFunctor.obj X).algebra
        ((dualNumberPairFunctor.obj X).module ⊗[A] N)) :
    dualExpandSnd N Y (symPairMap N (dualNumberPairFunctor.map g) s) =
      symPairMap N g (dualExpandSnd N X s) :=
  dualExpandSnd_naturality N g s

/-- **The `ε`-coefficient retraction** `π : T^* ψ_N^* M̲ ⟶ ψ_N^* M̲`. -/
noncomputable def dualRetraction :
    (dualScaling.{max (u + 1) (v + 1) w, v} A).obj (symPairExtension.{w, v} N M) ⟶
      symPairExtension.{w, v} N M :=
  pushforwardSymPairExtensionHom.{w, v} dualNumberPairFunctor (dualNumberRingHom.{v} A)
    (dualRetractionMap N M)
    (fun X c t => by
      induction t using TensorProduct.induction_on with
      | zero => rw [smul_zero, map_zero, smul_zero]
      | tmul s m =>
        rw [TensorProduct.smul_tmul', smul_eq_mul, dualRetractionMap_tmul, dualRetractionMap_tmul,
          dualExpandSnd_algebraMap_mul', TensorProduct.smul_tmul', smul_eq_mul]
      | add t t' ht ht' => rw [smul_add, map_add, map_add, ht, ht', smul_add])
    (fun g t => by
      induction t using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul s m =>
        simp only [TensorProduct.map_tmul, dualRetractionMap_tmul, AlgHom.toLinearMap_apply,
          LinearMap.id_apply, dualExpandSnd_naturality']
      | add t t' ht ht' => rw [map_add, map_add, ht, ht', map_add, map_add])


end RetractionMorphism

section RetractionIdentities

variable {A : Type u} [CommRing A] (N : Type (max u v)) [AddCommGroup N] [Module A N]
  (M : ModuleCat.{max (u + 1) (v + 1) w} A)

attribute [local instance] symPairAlgebra

attribute [local irreducible] dualNumberPair

/-- On values, `p ≫ τ ≫ π` is the identity. -/
lemma dualRetractionMap_eps_inl (X : AlgebraModulePair.{max u v} A)
    (t : (symPairExtension.{w, v} N M).obj (op (op X))) :
    dualRetractionMap N M X (dualEpsSmul (symPairExtension.{w, v} N M) X
      ((symPairExtension.{w, v} N M).map (dualNumberPairInl X).op.op t)) = t := by
  rw [symPairExtension_map_apply, dualEpsSmul_symPairExtension]
  exact dualCoefficientMap_eps_inl N M X t

/-- On values, `a ≫ π` is the weight-one projection. -/
lemma dualRetractionMap_inr (X : AlgebraModulePair.{max u v} A)
    (t : (symPairExtension.{w, v} N M).obj (op (op X))) :
    dualRetractionMap N M X ((symPairExtension.{w, v} N M).map (dualNumberPairInr X).op.op t) =
      (symPairWeightOne N X).rTensor M t := by
  rw [symPairExtension_map_apply]
  exact dualCoefficientMap_inr N M X t

/-- **`π` is a retraction of `p ≫ τ`** on `ψ_N^* M̲`. -/
theorem dualScalingInl_comp_eps_comp_retraction :
    (dualScalingInl.{max (u + 1) (v + 1) w, v} (A := A)).app (symPairExtension.{w, v} N M) ≫
        (dualScalingEps.{max (u + 1) (v + 1) w, v} (A := A)).app (symPairExtension.{w, v} N M) ≫
          dualRetraction N M =
      𝟙 (symPairExtension.{w, v} N M) := by
  refine PresheafOfModules.hom_ext fun X => ?_
  ext t
  show dualRetractionMap N M X.unop.unop (dualEpsSmul (symPairExtension.{w, v} N M) X.unop.unop
    ((symPairExtension.{w, v} N M).map (dualNumberPairInl X.unop.unop).op.op t)) = t
  exact dualRetractionMap_eps_inl N M X.unop.unop t

/-- **`a ≫ π` is the weight-one projection** `Π` of `ψ_N^* M̲`. -/
theorem dualScalingInr_comp_retraction :
    (dualScalingInr.{max (u + 1) (v + 1) w, v} (A := A)).app (symPairExtension.{w, v} N M) ≫
        dualRetraction N M =
      pairsWeightOneProjection.{w, v} N M := by
  refine PresheafOfModules.hom_ext fun X => ?_
  ext t
  show dualRetractionMap N M X.unop.unop ((symPairExtension.{w, v} N M).map
    (dualNumberPairInr X.unop.unop).op.op t) = (symPairWeightOne N X.unop.unop).rTensor M t
  exact dualRetractionMap_inr N M X.unop.unop t
end RetractionIdentities

section WeightOneExt

variable {A : Type u} [CommRing A] (N : Type (max u v)) [AddCommGroup N] [Module A N]
  (M : ModuleCat.{max (u + 1) (v + 1) w} A)

open CategoryTheory.Abelian

attribute [local instance] moduleValuedFunctor_enoughInjectives in
/-- **Classes out of `V` see only the weight-one part of `ψ_N^* M̲`.** For every
`ξ ∈ Ext^n(V, ψ_N^* M̲)`, `ξ ∘ Π = ξ`, where `Π` is the weight-one projection. -/
theorem ext_comp_pairsWeightOneProjection
    [HasExt.{t} (PairModuleValuedFunctor.{max (u + 1) (v + 1) w, v} A)] (n : ℕ)
    (ξ : Ext.{t} (tautologicalPairModule.{w, v} A) (symPairExtension.{w, v} N M) n) :
    ξ.comp (Ext.mk₀ (pairsWeightOneProjection.{w, v} N M)) (add_zero n) = ξ := by
  have h := Stacks.ExtFunctorial.comp_mk₀_eq_self_of_app_eq_comp
    (dualScaling.{max (u + 1) (v + 1) w, v} A) dualScalingInl dualScalingInr dualScalingEps
    dualScalingInr_app_tautological (dualRetraction N M) ?_ n ξ
  · rwa [dualScalingInr_comp_retraction] at h
  · exact dualScalingInl_comp_eps_comp_retraction.{w, v, u} N M

end WeightOneExt

end AdequateFunctor

end
