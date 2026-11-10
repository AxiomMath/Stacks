module

public import StacksFrontier.AlgebraicGeometry.Adequate.HigherExtsAdequate.PairsExt
public import StacksFrontier.AlgebraicGeometry.Adequate.HigherExtsAdequate.SymmetricWeightOne

/-!
# The weight-one part of `ψ_N^* M̲` on pairs

For an `A`-module `N` and an `A`-module `M`, the module-valued functor on pairs
`ψ_N^* M̲ : (C, V) ↦ Sym_C(V ⊗_A N) ⊗_A M` carries the weight-one projection
`Π = (ι ∘ λ) ⊗ M`, where `λ` is the linear part of the symmetric algebra
(`AdequateFunctor.symmetricLinearPart`). This file proves that `Π` factors through
`ψ_{A}^* (N ⊗ M)̲`, the same construction for the module `A` (carried as `ULift A`) and the
coefficient module `N ⊗_A M`.

## Main definitions

* `AdequateFunctor.pairsWeightOneProjection`: the projection `Π` as an endomorphism of
  `ψ_N^* M̲`.
* `AdequateFunctor.pairsWeightOneOut`, `AdequateFunctor.pairsWeightOneIn`: the two morphisms
  `ψ_N^* M̲ ⟶ ψ_A^* (N ⊗ M)̲ ⟶ ψ_N^* M̲`.

## Main results

* `AdequateFunctor.pairsWeightOneOut_comp_in`: their composite is `Π`.
-/

@[expose] public section

universe w' w v u

open CategoryTheory Opposite
open scoped TensorProduct

namespace AdequateFunctor

attribute [local instance] symPairAlgebra

section SymFunctoriality

variable {A : Type u} [CommRing A] (N : Type (max u v)) [AddCommGroup N] [Module A N]

/-- The `A`-linear map underlying the semilinear map of a morphism of pairs. -/
def pairLinearA {X Y : AlgebraModulePair.{max u v} A} (g : X ⟶ Y) : X.module →ₗ[A] Y.module where
  toFun := g.linear
  map_add' := g.linear.map_add
  map_smul' a x := by
    rw [← algebraMap_smul X.algebra a x, g.linear.map_smulₛₗ]
    change g.base (algebraMap A X.algebra a) • _ = _
    rw [AlgHom.commutes]
    exact algebraMap_smul Y.algebra a (g.linear x)

/-- The semilinear map `V ⊗_A N → V' ⊗_A N` induced by a morphism of pairs. -/
noncomputable def pairTensorMap {X Y : AlgebraModulePair.{max u v} A} (g : X ⟶ Y) :
    X.module ⊗[A] N →ₛₗ[g.base.toRingHom] Y.module ⊗[A] N where
  toFun := TensorProduct.map (pairLinearA g) LinearMap.id
  map_add' := map_add _
  map_smul' c t := by
    induction t using TensorProduct.inductionOn with
    | tmul x n =>
      rw [TensorProduct.smul_tmul', TensorProduct.map_tmul, TensorProduct.map_tmul,
        TensorProduct.smul_tmul']
      change g.linear (c • x) ⊗ₜ[A] n = _
      rw [g.linear.map_smulₛₗ]
      rfl
    | add s t hs ht => rw [smul_add, map_add, map_add, hs, ht, smul_add]

/-- `pairTensorMap N g` sends `x ⊗ n` to `g x ⊗ n`. -/
@[simp] lemma pairTensorMap_tmul {X Y : AlgebraModulePair.{max u v} A} (g : X ⟶ Y)
    (x : X.module) (n : N) : pairTensorMap N g (x ⊗ₜ n) = g.linear x ⊗ₜ n := rfl

/-- `ψ_N` on a morphism of pairs, as a map of `A`-algebras between symmetric algebras. -/
noncomputable def symPairMap {X Y : AlgebraModulePair.{max u v} A} (g : X ⟶ Y) :
    SymmetricAlgebra X.algebra (X.module ⊗[A] N) →ₐ[A]
      SymmetricAlgebra Y.algebra (Y.module ⊗[A] N) :=
  ((symPairFunctor.{v, u} (A := A) N).map g).hom

/-- `ψ_N` on a morphism of pairs is its algebra map on scalars. -/
lemma symPairMap_algebraMap {X Y : AlgebraModulePair.{max u v} A} (g : X ⟶ Y) (c : X.algebra) :
    symPairMap N g (algebraMap _ _ c) = algebraMap _ _ (g.base c) :=
  symPairHomEquiv_symm_algebraMap N X _ _ c

/-- `ψ_N` on a morphism of pairs sends the generator `ι t` to `ι (g ⊗ N) t`. -/
lemma symPairMap_ι {X Y : AlgebraModulePair.{max u v} A} (g : X ⟶ Y) (t : X.module ⊗[A] N) :
    symPairMap N g (SymmetricAlgebra.ι _ _ t) = SymmetricAlgebra.ι _ _ (pairTensorMap N g t) := by
  induction t using TensorProduct.inductionOn with
  | tmul x n => exact symLift_ι (D := symPairObj N Y) _ _ _
  | add s t hs ht => rw [map_add, map_add, hs, ht, map_add, map_add]

/-- The linear part commutes with `ψ_N` on morphisms of pairs. -/
lemma symmetricLinearPart_symPairMap {X Y : AlgebraModulePair.{max u v} A} (g : X ⟶ Y)
    (s : SymmetricAlgebra X.algebra (X.module ⊗[A] N)) :
    symmetricLinearPart Y.algebra (Y.module ⊗[A] N) (symPairMap N g s) =
      pairTensorMap N g (symmetricLinearPart X.algebra (X.module ⊗[A] N) s) :=
  symmetricLinearPart_naturality g.base.toRingHom (pairTensorMap N g)
    (symPairMap N g).toRingHom (symPairMap_algebraMap N g) (symPairMap_ι N g) s

end SymFunctoriality

section ExtensionHom

variable {A : Type u} [CommRing A]

/-- The module-valued functor `(C, V) ↦ Sym_C(V ⊗_A N) ⊗_A M` on pairs, i.e. `ψ_N^* M̲`. -/
noncomputable abbrev symPairExtension (N : Type (max u v)) [AddCommGroup N] [Module A N]
    (M : ModuleCat.{max (u + 1) (v + 1) w} A) :
    PairModuleValuedFunctor.{max (u + 1) (v + 1) w, v} A :=
  (PresheafOfModules.pushforward.{max (u + 1) (v + 1) w} (symPairRingHom.{v, u} (A := A) N)).obj
    (moduleExtension.{max (u + 1) (v + 1) w, v} A M)

variable {N N' : Type (max u v)} [AddCommGroup N] [Module A N] [AddCommGroup N'] [Module A N']
  {M M' : ModuleCat.{max (u + 1) (v + 1) w} A}

/-- A morphism `ψ_N^* M̲ ⟶ ψ_{N'}^* M'̲` from a family of `A`-linear maps on the values which is
linear over the algebra of each pair and natural in the pair. -/
noncomputable def symPairExtensionHom
    (L : ∀ X : AlgebraModulePair.{max u v} A,
      (SymmetricAlgebra X.algebra (X.module ⊗[A] N)) ⊗[A] M →ₗ[A]
        (SymmetricAlgebra X.algebra (X.module ⊗[A] N')) ⊗[A] M')
    (hL : ∀ (X : AlgebraModulePair.{max u v} A) (c : X.algebra) t,
      L X (algebraMap X.algebra (SymmetricAlgebra X.algebra (X.module ⊗[A] N)) c • t) =
        algebraMap X.algebra (SymmetricAlgebra X.algebra (X.module ⊗[A] N')) c • L X t)
    (hnat : ∀ {X Y : AlgebraModulePair.{max u v} A} (g : X ⟶ Y) t,
      L Y (TensorProduct.map (symPairMap N g).toLinearMap LinearMap.id t) =
        TensorProduct.map (symPairMap N' g).toLinearMap LinearMap.id (L X t)) :
    symPairExtension.{w, v} N M ⟶ symPairExtension.{w, v} N' M' where
  app X := ModuleCat.ofHom (X := (symPairExtension.{w, v} N M).obj X)
    (Y := (symPairExtension.{w, v} N' M').obj X)
    { toFun := L X.unop.unop
      map_add' := map_add _
      map_smul' := fun c t => hL X.unop.unop c t }
  naturality {X Y} g := by
    ext t
    exact hnat g.unop.unop t

/-- The component of `symPairExtensionHom L hL hnat` at a pair `X` is `L X`. -/
@[simp] lemma symPairExtensionHom_app_apply
    (L : ∀ X : AlgebraModulePair.{max u v} A,
      (SymmetricAlgebra X.algebra (X.module ⊗[A] N)) ⊗[A] M →ₗ[A]
        (SymmetricAlgebra X.algebra (X.module ⊗[A] N')) ⊗[A] M') (hL) (hnat)
    (X : (AlgebraModulePair.{max u v} A)ᵒᵖᵒᵖ) t :
    (symPairExtensionHom.{w, v} L hL hnat).app X t = L X.unop.unop t := rfl

/-- The composite of two morphisms `symPairExtensionHom` is `symPairExtensionHom` of the
composite families of linear maps. -/
lemma symPairExtensionHom_comp
    {N'' : Type (max u v)} [AddCommGroup N''] [Module A N'']
    {M'' : ModuleCat.{max (u + 1) (v + 1) w} A}
    (L L') (hL hnat hL' hnat') :
    symPairExtensionHom.{w, v} (N := N) (N' := N') (M := M) (M' := M') L hL hnat ≫
        symPairExtensionHom.{w, v} (N := N') (N' := N'') (M := M') (M' := M'') L' hL' hnat' =
      symPairExtensionHom.{w, v} (fun X => L' X ∘ₗ L X)
        (fun X c t => by simp only [LinearMap.comp_apply, hL, hL'])
        (fun g t => by simp only [LinearMap.comp_apply, hnat, hnat']) := rfl

/-- A morphism `T^* ψ_N^* M̲ ⟶ ψ_{N'}^* M'̲`, for an endofunctor `T` of pairs with ring maps
`ρ : C → T(C, V)`, from a family of `A`-linear maps on the values which is linear over the algebra
of each pair and natural in the pair. -/
noncomputable def pushforwardSymPairExtensionHom
    (T : AlgebraModulePair.{max u v} A ⥤ AlgebraModulePair.{max u v} A)
    (ρ : pairRingDiagram.{v} A ⟶ T.op.op ⋙ pairRingDiagram.{v} A)
    (L : ∀ X : AlgebraModulePair.{max u v} A,
      (SymmetricAlgebra (T.obj X).algebra ((T.obj X).module ⊗[A] N)) ⊗[A] M →ₗ[A]
        (SymmetricAlgebra X.algebra (X.module ⊗[A] N')) ⊗[A] M')
    (hL : ∀ (X : AlgebraModulePair.{max u v} A) (c : X.algebra) t,
      L X (algebraMap (T.obj X).algebra
          (SymmetricAlgebra (T.obj X).algebra ((T.obj X).module ⊗[A] N))
          ((ρ.app (op (op X))).hom c) • t) =
        algebraMap X.algebra (SymmetricAlgebra X.algebra (X.module ⊗[A] N')) c • L X t)
    (hnat : ∀ {X Y : AlgebraModulePair.{max u v} A} (g : X ⟶ Y) t,
      L Y (TensorProduct.map (symPairMap N (T.map g)).toLinearMap LinearMap.id t) =
        TensorProduct.map (symPairMap N' g).toLinearMap LinearMap.id (L X t)) :
    (PresheafOfModules.pushforward.{max (u + 1) (v + 1) w} ρ).obj (symPairExtension.{w, v} N M) ⟶
      symPairExtension.{w, v} N' M' where
  app X := ModuleCat.ofHom
    (X := ((PresheafOfModules.pushforward.{max (u + 1) (v + 1) w} ρ).obj
      (symPairExtension.{w, v} N M)).obj X)
    (Y := (symPairExtension.{w, v} N' M').obj X)
    { toFun := L X.unop.unop
      map_add' := map_add _
      map_smul' := fun c t => hL X.unop.unop c t }
  naturality {X Y} g := by
    ext t
    exact hnat g.unop.unop t

/-- The component of `pushforwardSymPairExtensionHom T ρ L hL hnat` at a pair `X` is `L X`. -/
@[simp] lemma pushforwardSymPairExtensionHom_app_apply
    (T : AlgebraModulePair.{max u v} A ⥤ AlgebraModulePair.{max u v} A)
    (ρ : pairRingDiagram.{v} A ⟶ T.op.op ⋙ pairRingDiagram.{v} A) (L) (hL) (hnat)
    (X : (AlgebraModulePair.{max u v} A)ᵒᵖᵒᵖ) t :
    (pushforwardSymPairExtensionHom.{w, v} (N := N) (N' := N') (M := M) (M' := M') T ρ L hL
      hnat).app X t = L X.unop.unop t := rfl

end ExtensionHom

section WeightOne

variable {A : Type u} [CommRing A] (N : Type (max u v)) [AddCommGroup N] [Module A N]
  (M : ModuleCat.{max (u + 1) (v + 1) w} A)

/-- The weight-one projection `ι ∘ λ` of `Sym_C(V ⊗_A N)`, as an `A`-linear map. -/
noncomputable def symPairWeightOne (X : AlgebraModulePair.{max u v} A) :
    SymmetricAlgebra X.algebra (X.module ⊗[A] N) →ₗ[A]
      SymmetricAlgebra X.algebra (X.module ⊗[A] N) :=
  (SymmetricAlgebra.ι X.algebra (X.module ⊗[A] N)).restrictScalars A ∘ₗ
    (symmetricLinearPart X.algebra (X.module ⊗[A] N)).restrictScalars A

/-- The weight-one projection `ι ∘ λ` is linear over the algebra `C` of the pair. -/
lemma symPairWeightOne_algebraMap_mul (X : AlgebraModulePair.{max u v} A) (c : X.algebra)
    (s : SymmetricAlgebra X.algebra (X.module ⊗[A] N)) :
    symPairWeightOne N X (algebraMap _ _ c * s) = algebraMap _ _ c * symPairWeightOne N X s := by
  simp only [symPairWeightOne, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
    Function.comp_apply]
  have h := symmetricLinearPart_algebraMap_mul (R := X.algebra) (W := X.module ⊗[A] N) c s
  refine (congrArg (SymmetricAlgebra.ι X.algebra (X.module ⊗[A] N)) h).trans ?_
  rw [LinearMap.map_smul]
  exact Algebra.smul_def _ _

/-- The weight-one projection `ι ∘ λ` commutes with `ψ_N` on morphisms of pairs. -/
lemma symPairWeightOne_naturality {X Y : AlgebraModulePair.{max u v} A} (g : X ⟶ Y)
    (s : SymmetricAlgebra X.algebra (X.module ⊗[A] N)) :
    symPairWeightOne N Y (symPairMap N g s) = symPairMap N g (symPairWeightOne N X s) := by
  simp only [symPairWeightOne, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
    Function.comp_apply, symmetricLinearPart_symPairMap, symPairMap_ι]

/-- A linear map out of `P ⊗ M` is equivariant for scalars acting on the left factor as soon as it
is so on pure tensors. -/
private theorem tensor_smul_left_induction {A S S' P M Q : Type*} [CommSemiring A] [Monoid S]
    [AddCommMonoid P] [Module A P] [DistribMulAction S P] [SMulCommClass A S P] [AddCommMonoid M]
    [Module A M] [AddCommMonoid Q] [Module A Q] [DistribSMul S' Q] (F : P ⊗[A] M →ₗ[A] Q) (a : S)
    (a' : S') (h : ∀ (p : P) (m : M), F ((a • p) ⊗ₜ[A] m) = a' • F (p ⊗ₜ[A] m))
    (t : P ⊗[A] M) : F (a • t) = a' • F t := by
  induction t using TensorProduct.inductionOn with
  | tmul p m => rw [TensorProduct.smul_tmul']; exact h p m
  | add t t' ht ht' => rw [smul_add, map_add, map_add, ht, ht', smul_add]

/-- The weight-one projection `(ι ∘ λ) ⊗ M` is linear over the algebra of the pair. -/
lemma symPairWeightOne_rTensor_algebraMap_smul {M' : Type*} [AddCommGroup M'] [Module A M']
    (X : AlgebraModulePair.{max u v} A) (c : X.algebra)
    (t : (SymmetricAlgebra X.algebra (X.module ⊗[A] N)) ⊗[A] M') :
    (symPairWeightOne N X).rTensor M'
        (algebraMap X.algebra (SymmetricAlgebra X.algebra (X.module ⊗[A] N)) c • t) =
      algebraMap X.algebra (SymmetricAlgebra X.algebra (X.module ⊗[A] N)) c •
        (symPairWeightOne N X).rTensor M' t := by
  refine tensor_smul_left_induction ((symPairWeightOne N X).rTensor M') _ _ (fun s m => ?_) t
  simp only [LinearMap.rTensor_tmul, smul_eq_mul, symPairWeightOne_algebraMap_mul,
    TensorProduct.smul_tmul']

/-- The weight-one projection `(ι ∘ λ) ⊗ M` is natural in the pair. -/
lemma symPairWeightOne_rTensor_naturality {M' : Type*} [AddCommGroup M'] [Module A M']
    {X Y : AlgebraModulePair.{max u v} A} (g : X ⟶ Y) (t : _) :
    (symPairWeightOne N Y).rTensor M'
        (TensorProduct.map (symPairMap N g).toLinearMap (LinearMap.id (M := M')) t) =
      TensorProduct.map (symPairMap N g).toLinearMap LinearMap.id
        ((symPairWeightOne N X).rTensor M' t) := by
  induction t using TensorProduct.inductionOn with
  | tmul s m =>
    simp only [TensorProduct.map_tmul, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply,
      LinearMap.id_apply, symPairWeightOne_naturality]
  | add t t' ht ht' => rw [map_add, map_add, ht, ht', map_add, map_add]

/-- **The weight-one projection of `ψ_N^* M̲`**, `(ι ∘ λ) ⊗ M`. -/
noncomputable def pairsWeightOneProjection :
    symPairExtension.{w, v} N M ⟶ symPairExtension.{w, v} N M :=
  symPairExtensionHom.{w, v} (fun X => (symPairWeightOne N X).rTensor M)
    (fun X c t => symPairWeightOne_rTensor_algebraMap_smul N X c t)
    (fun g t => (symPairWeightOne_rTensor_naturality N (M' := M) g t :))

end WeightOne

section Comparison

/-! The maps on values below are stated for a coefficient module `M` in any universe, so that
they serve module-valued functors on pairs in every value universe; the morphisms of
module-valued functors on all pairs take `M` in the value universe of those functors. -/

variable {A : Type u} [CommRing A] (N : Type (max u v)) [AddCommGroup N] [Module A N]
  (M : ModuleCat.{w'} A)

/-- The rank-one free `A`-module, carried in the universe of pairs. -/
abbrev unitPairModule (A : Type u) [CommRing A] : Type (max u v) := ULift.{max u v} A

/-- The coefficient module `N ⊗_A M`. -/
noncomputable abbrev pairCoefficient (M : ModuleCat.{max (u + 1) (v + 1) w} A) :
    ModuleCat.{max (u + 1) (v + 1) w} A :=
  ModuleCat.of A (N ⊗[A] M)

/-- The reassociation `(V ⊗ N) ⊗ M ≃ (V ⊗ A) ⊗ (N ⊗ M)`. -/
noncomputable def pairReassoc (V : Type (max u v)) [AddCommGroup V] [Module A V] :
    (V ⊗[A] N) ⊗[A] M ≃ₗ[A] (V ⊗[A] unitPairModule.{v} A) ⊗[A] (N ⊗[A] M) :=
  TensorProduct.assoc A V N M ≪≫ₗ
    TensorProduct.congr ((TensorProduct.rid A V).symm ≪≫ₗ
      TensorProduct.congr (LinearEquiv.refl A V) ULift.moduleEquiv.symm) (LinearEquiv.refl A _)

/-- The reassociation sends `(x ⊗ n) ⊗ m` to `(x ⊗ 1) ⊗ (n ⊗ m)`. -/
@[simp] lemma pairReassoc_tmul (V : Type (max u v)) [AddCommGroup V] [Module A V] (x : V) (n : N)
    (m : M) : pairReassoc N M V ((x ⊗ₜ n) ⊗ₜ m) = (x ⊗ₜ ULift.up 1) ⊗ₜ (n ⊗ₜ m) := rfl

/-- The inverse reassociation sends `(x ⊗ a) ⊗ (n ⊗ m)` to `(a • x ⊗ n) ⊗ m`. -/
@[simp] lemma pairReassoc_symm_tmul (V : Type (max u v)) [AddCommGroup V] [Module A V] (x : V)
    (a : unitPairModule.{v} A) (n : N) (m : M) :
    (pairReassoc N M V).symm ((x ⊗ₜ a) ⊗ₜ (n ⊗ₜ m)) = ((a.down • x) ⊗ₜ n) ⊗ₜ m := by
  apply (pairReassoc N M V).injective
  rw [LinearEquiv.apply_symm_apply, pairReassoc_tmul, TensorProduct.smul_tmul]
  congr 2
  ext
  simp

/-- On values, `ψ_N^* M̲ ⟶ ψ_A^* (N ⊗ M)̲`: take the linear part, reassociate, include. -/
noncomputable def pairsWeightOneOutMap (X : AlgebraModulePair.{max u v} A) :
    (SymmetricAlgebra X.algebra (X.module ⊗[A] N)) ⊗[A] M →ₗ[A]
      (SymmetricAlgebra X.algebra (X.module ⊗[A] unitPairModule.{v} A)) ⊗[A] (N ⊗[A] M) :=
  ((SymmetricAlgebra.ι X.algebra (X.module ⊗[A] unitPairModule.{v} A)).restrictScalars A).rTensor
      (N ⊗[A] M) ∘ₗ
    (pairReassoc N M X.module).toLinearMap ∘ₗ
      ((symmetricLinearPart X.algebra (X.module ⊗[A] N)).restrictScalars A).rTensor M

/-- On values, `ψ_A^* (N ⊗ M)̲ ⟶ ψ_N^* M̲`: take the linear part, reassociate back, include. -/
noncomputable def pairsWeightOneInMap (X : AlgebraModulePair.{max u v} A) :
    (SymmetricAlgebra X.algebra (X.module ⊗[A] unitPairModule.{v} A)) ⊗[A] (N ⊗[A] M) →ₗ[A]
      (SymmetricAlgebra X.algebra (X.module ⊗[A] N)) ⊗[A] M :=
  ((SymmetricAlgebra.ι X.algebra (X.module ⊗[A] N)).restrictScalars A).rTensor M ∘ₗ
    (pairReassoc N M X.module).symm.toLinearMap ∘ₗ
      ((symmetricLinearPart X.algebra (X.module ⊗[A] unitPairModule.{v} A)).restrictScalars
        A).rTensor (N ⊗[A] M)

/-- `pairsWeightOneOutMap` on a pure tensor `s ⊗ m`: the generator of the reassociation of
`λ s ⊗ m`. -/
lemma pairsWeightOneOutMap_tmul (X : AlgebraModulePair.{max u v} A)
    (s : SymmetricAlgebra X.algebra (X.module ⊗[A] N)) (m : M) :
    pairsWeightOneOutMap N M X (s ⊗ₜ m) =
      ((SymmetricAlgebra.ι X.algebra (X.module ⊗[A] unitPairModule.{v} A)).restrictScalars
        A).rTensor (N ⊗[A] M)
        (pairReassoc N M X.module (symmetricLinearPart X.algebra (X.module ⊗[A] N) s ⊗ₜ m)) :=
  rfl

/-- `pairsWeightOneInMap` on a pure tensor `s ⊗ y`: the generator of the inverse reassociation
of `λ s ⊗ y`. -/
lemma pairsWeightOneInMap_tmul (X : AlgebraModulePair.{max u v} A)
    (s : SymmetricAlgebra X.algebra (X.module ⊗[A] unitPairModule.{v} A)) (y : N ⊗[A] M) :
    pairsWeightOneInMap N M X (s ⊗ₜ y) =
      ((SymmetricAlgebra.ι X.algebra (X.module ⊗[A] N)).restrictScalars A).rTensor M
        ((pairReassoc N M X.module).symm
          (symmetricLinearPart X.algebra (X.module ⊗[A] unitPairModule.{v} A) s ⊗ₜ y)) :=
  rfl

/-- The composite of the two comparison maps is the weight-one projection. -/
lemma pairsWeightOneInMap_outMap (X : AlgebraModulePair.{max u v} A)
    (t : (SymmetricAlgebra X.algebra (X.module ⊗[A] N)) ⊗[A] M) :
    pairsWeightOneInMap N M X (pairsWeightOneOutMap N M X t) =
      (symPairWeightOne N X).rTensor M t := by
  have key : ∀ (y : X.module ⊗[A] N) (m : M),
      pairsWeightOneInMap N M X
        (((SymmetricAlgebra.ι X.algebra (X.module ⊗[A] unitPairModule.{v} A)).restrictScalars
          A).rTensor (N ⊗[A] M) (pairReassoc N M X.module (y ⊗ₜ m))) =
        SymmetricAlgebra.ι X.algebra (X.module ⊗[A] N) y ⊗ₜ m := by
    intro y m
    induction y using TensorProduct.inductionOn with
    | tmul x n =>
      rw [pairReassoc_tmul, LinearMap.rTensor_tmul, pairsWeightOneInMap_tmul,
        LinearMap.restrictScalars_apply, symmetricLinearPart_ι, pairReassoc_symm_tmul,
        LinearMap.rTensor_tmul]
      simp
    | add y y' hy hy' => rw [TensorProduct.add_tmul, map_add, map_add, map_add, hy, hy',
        map_add, TensorProduct.add_tmul]
  induction t using TensorProduct.inductionOn with
  | tmul s m =>
    rw [pairsWeightOneOutMap_tmul, key, LinearMap.rTensor_tmul]
    rfl
  | add t t' ht ht' => rw [map_add, map_add, ht, ht', map_add]

/-- The middle part of `pairsWeightOneOutMap`, on a tensor `y ⊗ m` with `y ∈ V ⊗ N`. -/
noncomputable def pairsOutAux (X : AlgebraModulePair.{max u v} A) (y : X.module ⊗[A] N) (m : M) :
    (SymmetricAlgebra X.algebra (X.module ⊗[A] unitPairModule.{v} A)) ⊗[A] (N ⊗[A] M) :=
  ((SymmetricAlgebra.ι X.algebra (X.module ⊗[A] unitPairModule.{v} A)).restrictScalars
    A).rTensor (N ⊗[A] M) (pairReassoc N M X.module (y ⊗ₜ m))

/-- `pairsOutAux` is linear over the algebra `C` of the pair in its first argument. -/
lemma pairsOutAux_smul (X : AlgebraModulePair.{max u v} A) (c : X.algebra) (y : X.module ⊗[A] N)
    (m : M) :
    pairsOutAux N M X (c • y) m =
      algebraMap X.algebra (SymmetricAlgebra X.algebra (X.module ⊗[A] unitPairModule.{v} A)) c •
        pairsOutAux N M X y m := by
  induction y using TensorProduct.inductionOn with
  | tmul x n =>
    simp only [pairsOutAux, TensorProduct.smul_tmul', pairReassoc_tmul, LinearMap.rTensor_tmul,
      LinearMap.restrictScalars_apply, smul_eq_mul]
    rw [← TensorProduct.smul_tmul', LinearMap.map_smul]
    exact congrArg (· ⊗ₜ[A] (n ⊗ₜ[A] m)) (Algebra.smul_def _ _)
  | add y y' hy hy' =>
    simp only [pairsOutAux] at hy hy' ⊢
    rw [smul_add, TensorProduct.add_tmul, map_add, map_add, hy, hy', TensorProduct.add_tmul,
      map_add, map_add, smul_add]

/-- `pairsOutAux` commutes with the maps induced by a morphism of pairs. -/
lemma pairsOutAux_naturality {X Y : AlgebraModulePair.{max u v} A} (g : X ⟶ Y)
    (y : X.module ⊗[A] N) (m : M) :
    pairsOutAux N M Y (pairTensorMap N g y) m =
      TensorProduct.map (symPairMap (unitPairModule.{v} A) g).toLinearMap LinearMap.id
        (pairsOutAux N M X y m) := by
  induction y using TensorProduct.inductionOn with
  | tmul x n =>
    simp only [pairsOutAux, pairTensorMap_tmul, pairReassoc_tmul, LinearMap.rTensor_tmul,
      LinearMap.restrictScalars_apply, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
      LinearMap.id_apply, symPairMap_ι]
  | add y y' hy hy' =>
    simp only [pairsOutAux] at hy hy' ⊢
    rw [map_add, TensorProduct.add_tmul, map_add, map_add, hy, hy', TensorProduct.add_tmul,
      map_add, map_add, map_add]

/-- `pairsWeightOneOutMap` is linear over the algebra of the pair. -/
lemma pairsWeightOneOutMap_algebraMap_smul (X : AlgebraModulePair.{max u v} A) (c : X.algebra)
    (t : (SymmetricAlgebra X.algebra (X.module ⊗[A] N)) ⊗[A] M) :
    pairsWeightOneOutMap N M X
        (algebraMap X.algebra (SymmetricAlgebra X.algebra (X.module ⊗[A] N)) c • t) =
      algebraMap X.algebra (SymmetricAlgebra X.algebra (X.module ⊗[A] unitPairModule.{v} A)) c •
        pairsWeightOneOutMap N M X t := by
  refine tensor_smul_left_induction (pairsWeightOneOutMap N M X) _ _ (fun s m => ?_) t
  rw [smul_eq_mul, pairsWeightOneOutMap_tmul, pairsWeightOneOutMap_tmul]
  have h := symmetricLinearPart_algebraMap_mul (R := X.algebra) (W := X.module ⊗[A] N) c s
  exact (congrArg (fun y => pairsOutAux N M X y m) h).trans (pairsOutAux_smul N M X c _ m)

/-- `pairsWeightOneOutMap` is natural in the pair. -/
lemma pairsWeightOneOutMap_naturality {X Y : AlgebraModulePair.{max u v} A} (g : X ⟶ Y) (t : _) :
    pairsWeightOneOutMap N M Y (TensorProduct.map (symPairMap N g).toLinearMap LinearMap.id t) =
      TensorProduct.map (symPairMap (unitPairModule.{v} A) g).toLinearMap LinearMap.id
        (pairsWeightOneOutMap N M X t) := by
  induction t using TensorProduct.inductionOn with
  | tmul s m =>
    rw [TensorProduct.map_tmul, pairsWeightOneOutMap_tmul, pairsWeightOneOutMap_tmul]
    simp only [AlgHom.toLinearMap_apply, LinearMap.id_apply, symmetricLinearPart_symPairMap]
    exact pairsOutAux_naturality N M g _ m
  | add t t' ht ht' => rw [map_add, map_add, ht, ht', map_add, map_add]

/-- **The comparison `ψ_N^* M̲ ⟶ ψ_A^* (N ⊗ M)̲`.** -/
noncomputable def pairsWeightOneOut (M : ModuleCat.{max (u + 1) (v + 1) w} A) :
    symPairExtension.{w, v} N M ⟶
      symPairExtension.{w, v} (unitPairModule.{v} A) (pairCoefficient.{w, v} N M) :=
  symPairExtensionHom.{w, v} (pairsWeightOneOutMap N M)
    (pairsWeightOneOutMap_algebraMap_smul N M)
    (fun g t => (pairsWeightOneOutMap_naturality N M g t :))

/-- The middle part of `pairsWeightOneInMap`, on a tensor `z ⊗ y` with `z ∈ V ⊗ A`. -/
noncomputable def pairsInAux (X : AlgebraModulePair.{max u v} A)
    (z : X.module ⊗[A] unitPairModule.{v} A) (y : N ⊗[A] M) :
    (SymmetricAlgebra X.algebra (X.module ⊗[A] N)) ⊗[A] M :=
  ((SymmetricAlgebra.ι X.algebra (X.module ⊗[A] N)).restrictScalars A).rTensor M
    ((pairReassoc N M X.module).symm (z ⊗ₜ y))

/-- `pairsInAux` sends `(x ⊗ a, n ⊗ m)` to `ι (a • x ⊗ n) ⊗ m`. -/
lemma pairsInAux_tmul_tmul (X : AlgebraModulePair.{max u v} A) (x : X.module)
    (a : unitPairModule.{v} A) (n : N) (m : M) :
    pairsInAux N M X (x ⊗ₜ a) (n ⊗ₜ m) =
      SymmetricAlgebra.ι X.algebra (X.module ⊗[A] N) ((a.down • x) ⊗ₜ n) ⊗ₜ m := by
  simp only [pairsInAux, pairReassoc_symm_tmul, LinearMap.rTensor_tmul,
    LinearMap.restrictScalars_apply]

/-- `pairsInAux` is additive in its first argument. -/
lemma pairsInAux_add_left (X : AlgebraModulePair.{max u v} A) (z z') (y : N ⊗[A] M) :
    pairsInAux N M X (z + z') y = pairsInAux N M X z y + pairsInAux N M X z' y := by
  simp only [pairsInAux, TensorProduct.add_tmul, map_add]

/-- `pairsInAux` is additive in its second argument. -/
lemma pairsInAux_add_right (X : AlgebraModulePair.{max u v} A) (z) (y y' : N ⊗[A] M) :
    pairsInAux N M X z (y + y') = pairsInAux N M X z y + pairsInAux N M X z y' := by
  simp only [pairsInAux, TensorProduct.tmul_add, map_add]

/-- `pairsInAux` vanishes when its first argument is zero. -/
lemma pairsInAux_zero_left (X : AlgebraModulePair.{max u v} A) (y : N ⊗[A] M) :
    pairsInAux N M X 0 y = 0 := by
  simp only [pairsInAux, TensorProduct.zero_tmul, map_zero]

/-- `pairsInAux` vanishes when its second argument is zero. -/
lemma pairsInAux_zero_right (X : AlgebraModulePair.{max u v} A) (z) :
    pairsInAux N M X z 0 = 0 := by
  simp only [pairsInAux, TensorProduct.tmul_zero, map_zero]

/-- `pairsInAux` is linear over the algebra `C` of the pair in its first argument. -/
lemma pairsInAux_smul (X : AlgebraModulePair.{max u v} A) (c : X.algebra) (z) (y : N ⊗[A] M) :
    pairsInAux N M X (c • z) y =
      algebraMap X.algebra (SymmetricAlgebra X.algebra (X.module ⊗[A] N)) c •
        pairsInAux N M X z y := by
  induction z using TensorProduct.inductionOn with
  | tmul x a =>
    induction y using TensorProduct.inductionOn with
    | tmul n m =>
      rw [TensorProduct.smul_tmul', pairsInAux_tmul_tmul, pairsInAux_tmul_tmul,
        TensorProduct.smul_tmul', smul_comm, ← TensorProduct.smul_tmul', LinearMap.map_smul]
      exact congrArg (· ⊗ₜ[A] m) (Algebra.smul_def _ _)
    | add y y' hy hy' => rw [pairsInAux_add_right, pairsInAux_add_right, hy, hy', smul_add]
  | add z z' hz hz' => rw [smul_add, pairsInAux_add_left, pairsInAux_add_left, hz, hz', smul_add]

/-- `pairsInAux` commutes with the maps induced by a morphism of pairs. -/
lemma pairsInAux_naturality {X Y : AlgebraModulePair.{max u v} A} (g : X ⟶ Y)
    (z : X.module ⊗[A] unitPairModule.{v} A) (y : N ⊗[A] M) :
    pairsInAux N M Y (pairTensorMap (unitPairModule.{v} A) g z) y =
      TensorProduct.map (symPairMap N g).toLinearMap LinearMap.id (pairsInAux N M X z y) := by
  induction z using TensorProduct.inductionOn with
  | tmul x a =>
    induction y using TensorProduct.inductionOn with
    | tmul n m =>
      rw [pairTensorMap_tmul, pairsInAux_tmul_tmul, pairsInAux_tmul_tmul, TensorProduct.map_tmul,
        AlgHom.toLinearMap_apply, symPairMap_ι, pairTensorMap_tmul, LinearMap.id_apply]
      congr 3
      exact ((pairLinearA g).map_smul a.down x).symm
    | add y y' hy hy' => rw [pairsInAux_add_right, pairsInAux_add_right, hy, hy', map_add]
  | add z z' hz hz' =>
    rw [map_add, pairsInAux_add_left, pairsInAux_add_left, hz, hz', map_add]

/-- `pairsWeightOneInMap` is linear over the algebra of the pair. -/
lemma pairsWeightOneInMap_algebraMap_smul (X : AlgebraModulePair.{max u v} A) (c : X.algebra)
    (t : (SymmetricAlgebra X.algebra (X.module ⊗[A] unitPairModule.{v} A)) ⊗[A] (N ⊗[A] M)) :
    pairsWeightOneInMap N M X
        (algebraMap X.algebra (SymmetricAlgebra X.algebra (X.module ⊗[A] unitPairModule.{v} A))
          c • t) =
      algebraMap X.algebra (SymmetricAlgebra X.algebra (X.module ⊗[A] N)) c •
        pairsWeightOneInMap N M X t := by
  refine tensor_smul_left_induction (pairsWeightOneInMap N M X) _ _ (fun s y => ?_) t
  rw [smul_eq_mul, pairsWeightOneInMap_tmul, pairsWeightOneInMap_tmul]
  have h := symmetricLinearPart_algebraMap_mul (R := X.algebra)
    (W := X.module ⊗[A] unitPairModule.{v} A) c s
  exact (congrArg (fun z => pairsInAux N M X z y) h).trans (pairsInAux_smul N M X c _ y)

/-- `pairsWeightOneInMap` is natural in the pair. -/
lemma pairsWeightOneInMap_naturality {X Y : AlgebraModulePair.{max u v} A} (g : X ⟶ Y) (t : _) :
    pairsWeightOneInMap N M Y
        (TensorProduct.map (symPairMap (unitPairModule.{v} A) g).toLinearMap LinearMap.id t) =
      TensorProduct.map (symPairMap N g).toLinearMap LinearMap.id
        (pairsWeightOneInMap N M X t) := by
  induction t using TensorProduct.inductionOn with
  | tmul s y =>
    rw [TensorProduct.map_tmul, pairsWeightOneInMap_tmul, pairsWeightOneInMap_tmul]
    simp only [AlgHom.toLinearMap_apply, LinearMap.id_apply, symmetricLinearPart_symPairMap]
    exact pairsInAux_naturality N M g _ y
  | add t t' ht ht' => rw [map_add, map_add, ht, ht', map_add, map_add]

/-- **The comparison `ψ_A^* (N ⊗ M)̲ ⟶ ψ_N^* M̲`.** -/
noncomputable def pairsWeightOneIn (M : ModuleCat.{max (u + 1) (v + 1) w} A) :
    symPairExtension.{w, v} (unitPairModule.{v} A) (pairCoefficient.{w, v} N M) ⟶
      symPairExtension.{w, v} N M :=
  symPairExtensionHom.{w, v} (pairsWeightOneInMap N M)
    (pairsWeightOneInMap_algebraMap_smul N M)
    (fun g t => (pairsWeightOneInMap_naturality N M g t :))

/-- **The weight-one projection factors through `ψ_A^* (N ⊗ M)̲`.** -/
theorem pairsWeightOneOut_comp_in (M : ModuleCat.{max (u + 1) (v + 1) w} A) :
    pairsWeightOneOut.{w, v} N M ≫ pairsWeightOneIn.{w, v} N M =
      pairsWeightOneProjection.{w, v} N M := by
  refine PresheafOfModules.hom_ext fun X => ?_
  ext t
  exact pairsWeightOneInMap_outMap N M X.unop.unop t

end Comparison

end AdequateFunctor

end
