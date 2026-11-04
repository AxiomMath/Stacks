module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineDirectImageAction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackMonoidal

/-!
# The tensor structures of the affine direct image and inverse image

Let `g : 𝒰 ⟶ 𝒳` be an affine 1-morphism of algebraic stacks, with direct image
`g_* = AlgebraicGeometry.Stack.affinePushforward g` (`(g_*N)(x) = N(r x)` for the right adjoint
`r` of `g`) and inverse image `g^* = AlgebraicGeometry.Stack.stackModulePullback g`
(`(g^*M)(u) = M(g u)`), both on sheaves of modules with the tensor product sheaf of Tag 01CA.
Both are restrictions of presheaves, so both carry a tensor comparison: the sheafification of
the objectwise tensorator of restriction of scalars. This file constructs them and proves the
compatibilities used to show that the comparison of Stacks 0GRQ is an isomorphism of tensor
functors:

* `λ_{N,𝒪} ≫ g_*(ρ_N)` is the action of `g_*𝒪_𝒰` on `g_*N`;
* `λ` is natural in the right factor;
* the unit `η` of `g^* ⊣ g_*` is compatible with the tensor products:
  `η_{M ⊗ N} = (η_M ⊗ η_N) ≫ λ ≫ g_*(μ^{g^*})`.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.directImageTensor`: `g_*N ⊗ g_*N' ⟶ g_*(N ⊗ N')`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.pullbackTensor`: `g^*M ⊗ g^*N ⟶ g^*(M ⊗ N)`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.directImageTensor_comp_rightUnitor`
* `AlgebraicGeometry.Stack.AlgebraicStacks.directImageTensor_naturality_right`
* `AlgebraicGeometry.Stack.AlgebraicStacks.unit_app_tensor`

## References

* [Stacks Project, Tag 0GRQ](https://stacks.math.columbia.edu/tag/0GRQ)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u w v₁ u₁ w₁

namespace Stacks.SheafOfModules

attribute [local implicit_reducible]
  TensorSheafification.structureSheaf TensorSheafification.sheafify Tensor.ringSheaf

attribute [local instance] monoidalCategoryPresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w₁})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w₁}]
  [HasWeakSheafify J AddCommGrpCat.{w₁}]

/-- A map out of a sheafification, followed by a morphism of sheaves, is the map induced by the
composite of presheaves. -/
theorem sheafify_map_comp_sheafifyValIso_hom_comp
    {P : PresheafOfModules.{w₁} (TensorSheafification.structureRingPresheaf O)}
    {T T' : _root_.SheafOfModules.{w₁} (TensorSheafification.structureSheaf O hO)}
    (α : P ⟶ T.val) (t : T ⟶ T') (α' : P ⟶ T'.val) (h : α ≫ t.val = α') :
    ((sheafifyFunctor O hO).map α ≫ (sheafifyValIso O hO T).hom) ≫ t =
      (sheafifyFunctor O hO).map α' ≫ (sheafifyValIso O hO T').hom := by
  rw [Category.assoc, sheafifyValIso_hom_naturality, ← Category.assoc, ← Functor.map_comp, h]

attribute [local instance] Strict.monoidalCategory in
/-- **Naturality of a map out of a tensor product sheaf in the right factor, from naturality of
its objectwise version.** -/
theorem tensorHom_comp_sheafify_map_comp
    {G M M' T T' : _root_.SheafOfModules.{w₁} (TensorSheafification.structureSheaf O hO)}
    (f : M ⟶ M') (t : T ⟶ T')
    (α : PresheafOfModules.Monoidal.tensorObj (R := O) G.val M.val ⟶ T.val)
    (α' : PresheafOfModules.Monoidal.tensorObj (R := O) G.val M'.val ⟶ T'.val)
    (h : PresheafOfModules.Monoidal.tensorHom (R := O) (𝟙 G.val) f.val ≫ α' = α ≫ t.val) :
    (𝟙 G ⊗ₘ f) ≫ (sheafifyFunctor O hO).map α' ≫ (sheafifyValIso O hO T').hom =
      ((sheafifyFunctor O hO).map α ≫ (sheafifyValIso O hO T).hom) ≫ t := by
  refine (congrArg (· ≫ (sheafifyFunctor O hO).map α' ≫ (sheafifyValIso O hO T').hom)
    (tensorHom_eq_sheafify_map O hO (𝟙 G) f)).trans ?_
  refine (Functor.map_comp_assoc _ _ _ _).symm.trans ?_
  refine Eq.trans ?_ (sheafify_map_comp_sheafifyValIso_hom_comp O hO α t _ rfl).symm
  exact congrArg (fun k => (sheafifyFunctor O hO).map k ≫ (sheafifyValIso O hO T').hom) h

attribute [local instance] Strict.monoidalCategory in
/-- The tensor product of two morphisms on the sheafification unit of a local pure tensor. -/
theorem tensorHom_val_app_toSheafify_tmul
    {A A' D D' : _root_.SheafOfModules.{w₁} (TensorSheafification.structureSheaf O hO)}
    (a : A ⟶ A') (b : D ⟶ D') (V : Cᵒᵖ) (x : A.val.obj V) (y : D.val.obj V) :
    (a ⊗ₘ b).val.app V ((TensorSheafification.toSheafify O hO
        (PresheafOfModules.Monoidal.tensorObj (R := O) A.val D.val)).app V (x ⊗ₜ y)) =
      (TensorSheafification.toSheafify O hO
        (PresheafOfModules.Monoidal.tensorObj (R := O) A'.val D'.val)).app V
          (a.val.app V x ⊗ₜ b.val.app V y) :=
  (congrArg (fun h => h.val.app V ((TensorSheafification.toSheafify O hO
      (PresheafOfModules.Monoidal.tensorObj (R := O) A.val D.val)).app V (x ⊗ₜ y)))
    (tensorHom_eq_sheafify_map O hO a b)).trans
    (sheafify_map_toSheafify_app O hO (a.val ⊗ₘ b.val) V (x ⊗ₜ y))

/-- The map out of a sheafification induced by `α`, on the image of a section under the
sheafification unit, is `α` of that section. -/
theorem sheafify_map_comp_sheafifyValIso_hom_val_app_toSheafify
    {P : PresheafOfModules.{w₁} (TensorSheafification.structureRingPresheaf O)}
    {T : _root_.SheafOfModules.{w₁} (TensorSheafification.structureSheaf O hO)}
    (α : P ⟶ T.val) (V : Cᵒᵖ) (x : P.obj V) :
    ((sheafifyFunctor O hO).map α ≫ (sheafifyValIso O hO T).hom).val.app V
        ((TensorSheafification.toSheafify O hO P).app V x) = α.app V x :=
  (congrArg (((sheafifyValIso O hO T).hom).val.app V)
    (sheafify_map_toSheafify_app O hO α V x)).trans (counit_toSheafify_app O hO T V (α.app V x))

attribute [local instance] Strict.monoidalCategory in
/-- **Two maps out of a tensor product sheaf agree once they agree on the images of local pure
tensors.** -/
theorem sheafify_tensor_hom_ext
    {A D T : _root_.SheafOfModules.{w₁} (TensorSheafification.structureSheaf O hO)}
    {f₁ f₂ : A ⊗ D ⟶ T}
    (h : ∀ (V : Cᵒᵖ) (a : A.val.obj V) (d : D.val.obj V),
      f₁.val.app V ((TensorSheafification.toSheafify O hO
          (PresheafOfModules.Monoidal.tensorObj (R := O) A.val D.val)).app V (a ⊗ₜ d)) =
        f₂.val.app V ((TensorSheafification.toSheafify O hO
          (PresheafOfModules.Monoidal.tensorObj (R := O) A.val D.val)).app V (a ⊗ₜ d))) :
    f₁ = f₂ := by
  refine ((TensorSheafification.sheafifyAdjunction O hO).homEquiv _ _).injective ?_
  refine PresheafOfModules.hom_ext fun V => ModuleCat.MonoidalCategory.tensor_ext fun a d => ?_
  exact h V a d

attribute [local instance] Strict.monoidalCategory in
/-- Left whiskering on the sheafification unit of a local pure tensor. -/
theorem whiskerLeft_val_app_toSheafify_tmul
    {A D D' : _root_.SheafOfModules.{w₁} (TensorSheafification.structureSheaf O hO)}
    (b : D ⟶ D') (V : Cᵒᵖ) (x : A.val.obj V) (y : D.val.obj V) :
    (A ◁ b).val.app V ((TensorSheafification.toSheafify O hO
        (PresheafOfModules.Monoidal.tensorObj (R := O) A.val D.val)).app V (x ⊗ₜ y)) =
      (TensorSheafification.toSheafify O hO
        (PresheafOfModules.Monoidal.tensorObj (R := O) A.val D'.val)).app V
          (x ⊗ₜ b.val.app V y) := by
  rw [← MonoidalCategory.id_tensorHom]
  exact tensorHom_val_app_toSheafify_tmul O hO (𝟙 A) b V x y

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Stack.AlgebraicStacks

attribute [local instance] hasSheafCompose_forget_ringCat
  hasSheafCompose_forget_commRingCat Stacks.hasSheafCompose_forget₂_commRingCat
  FlatFppf.hasSheafify_addCommGrpCat FlatFppf.wEqualsLocallyBijective_addCommGrpCat
  FlatFppf.hasSheafify_fppf_addCommGrpCat FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat
  FlatFppf.hasSheafify_associatedTopology_ab
  FlatFppf.wEqualsLocallyBijective_fppfTopology_addCommGrpCat
attribute [local instance] fppfModulesMonoidal fppfModulesBraided fppfModulesSymmetric
attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS} (g : 𝒰 ⟶ 𝒳) (hg : IsAffineHom B S hS g)

/-- The objectwise tensorator of `g_*`, followed by `g_*` of the sheafification unit. -/
def directImageTensorPresheaf (N N' : Stack.fppfModules B S hS 𝒰) :
    PresheafOfModules.Monoidal.tensorObj (R := fppfStructurePresheaf B S hS 𝒳)
        ((affinePushforward.{u, w, u} g hg).obj N).val
        ((affinePushforward.{u, w, u} g hg).obj N').val ⟶
      ((affinePushforward.{u, w, u} g hg).obj (N ⊗ N')).val :=
  PresheafOfModules.pushforwardMu (F := affineRightAdjoint g hg)
      (S := fppfStructurePresheaf B S hS 𝒳) (R := fppfStructurePresheaf B S hS 𝒰)
      (Functor.whiskerRight (pushforwardCommRingHom g hg) (forget₂ _ _)) N.val N'.val ≫
    (PresheafOfModules.pushforwardComm (pushforwardCommRingHom g hg)).map
      (Stacks.SheafOfModules.TensorSheafification.toSheafify (fppfStructurePresheaf B S hS 𝒰)
        (fppfStructurePresheaf_isSheaf B S hS 𝒰)
        (PresheafOfModules.Monoidal.tensorObj N.val N'.val))

/-- On a pure tensor `n ⊗ₜ n'` at `X`, the tensorator of `g_*` is the sheafification unit of
`N ⊗ N'` at `r X`. -/
theorem directImageTensorPresheaf_app_tmul (N N' : Stack.fppfModules B S hS 𝒰)
    (X : 𝒳.val.val.objᵒᵖ) (n : N.val.obj (op ((affineRightAdjoint g hg).obj X.unop)))
    (n' : N'.val.obj (op ((affineRightAdjoint g hg).obj X.unop))) :
    ((directImageTensorPresheaf g hg N N').app X).hom (n ⊗ₜ n') =
      (Stacks.SheafOfModules.TensorSheafification.toSheafify (fppfStructurePresheaf B S hS 𝒰)
        (fppfStructurePresheaf_isSheaf B S hS 𝒰)
        (PresheafOfModules.Monoidal.tensorObj N.val N'.val)).app
          (op ((affineRightAdjoint g hg).obj X.unop)) (n ⊗ₜ n') :=
  congrArg (((PresheafOfModules.pushforwardComm (pushforwardCommRingHom g hg)).map
      (Stacks.SheafOfModules.TensorSheafification.toSheafify (fppfStructurePresheaf B S hS 𝒰)
        (fppfStructurePresheaf_isSheaf B S hS 𝒰)
        (PresheafOfModules.Monoidal.tensorObj N.val N'.val))).app X).hom
    (PresheafOfModules.pushforwardMu_app_tmul (F := affineRightAdjoint g hg)
      (S := fppfStructurePresheaf B S hS 𝒳) (R := fppfStructurePresheaf B S hS 𝒰)
      (Functor.whiskerRight (pushforwardCommRingHom g hg) (forget₂ _ _)) N.val N'.val X n n')

/-- **The lax structure `g_*N ⊗ g_*N' ⟶ g_*(N ⊗ N')` of the affine direct image** (strict
structure): the sheafification of the objectwise tensorator, followed by the counit. -/
def directImageTensor (N N' : Stack.fppfModules B S hS 𝒰) :
    (affinePushforward.{u, w, u} g hg).obj N ⊗ (affinePushforward.{u, w, u} g hg).obj N' ⟶
      (affinePushforward.{u, w, u} g hg).obj (N ⊗ N') :=
  (Stacks.SheafOfModules.sheafifyFunctor (fppfStructurePresheaf B S hS 𝒳)
      (fppfStructurePresheaf_isSheaf B S hS 𝒳)).map (directImageTensorPresheaf g hg N N') ≫
    (Stacks.SheafOfModules.sheafifyValIso (fppfStructurePresheaf B S hS 𝒳)
      (fppfStructurePresheaf_isSheaf B S hS 𝒳)
      ((affinePushforward.{u, w, u} g hg).obj (N ⊗ N'))).hom

/-- The objectwise form of the right unitor relation. -/
theorem directImageTensorPresheaf_comp_rightUnitor (N : Stack.fppfModules B S hS 𝒰) :
    directImageTensorPresheaf g hg N (SheafOfModules.unit _) ≫
        ((affinePushforward.{u, w, u} g hg).map (ρ_ N).hom).val =
      PresheafOfModules.pushforwardAct (pushforwardCommRingHom g hg) N.val := by
  refine PresheafOfModules.hom_ext fun X => ModuleCat.MonoidalCategory.tensor_ext fun n s => ?_
  have h1 := directImageTensorPresheaf_app_tmul g hg N (SheafOfModules.unit _) X n s
  have h2 := Stacks.SheafOfModules.rightUnitor_hom_val_app_tmul (fppfStructurePresheaf B S hS 𝒰)
    (fppfStructurePresheaf_isSheaf B S hS 𝒰) N (op ((affineRightAdjoint g hg).obj X.unop)) n s
  have h3 := PresheafOfModules.pushforwardAct_app_tmul (pushforwardCommRingHom g hg) N.val X n s
  exact (congrArg (fun z => (((affinePushforward.{u, w, u} g hg).map (ρ_ N).hom).val.app X).hom z)
    h1).trans (h2.trans h3.symm)

/-- **`λ_{N,𝒪} ≫ g_*(ρ_N)` is the action of `g_*𝒪` on `g_*N`.** -/
theorem directImageTensor_comp_rightUnitor (N : Stack.fppfModules B S hS 𝒰) :
    directImageTensor g hg N (SheafOfModules.unit _) ≫
        (affinePushforward.{u, w, u} g hg).map (ρ_ N).hom =
      directImageAct g hg N :=
  Stacks.SheafOfModules.sheafify_map_comp_sheafifyValIso_hom_comp _ _ _ _ _
    (directImageTensorPresheaf_comp_rightUnitor g hg N)

/-- The objectwise form of the naturality of the lax structure in the right factor. -/
theorem directImageTensorPresheaf_naturality_right (N : Stack.fppfModules B S hS 𝒰)
    {N' N'' : Stack.fppfModules B S hS 𝒰} (ψ : N' ⟶ N'') :
    PresheafOfModules.Monoidal.tensorHom (R := fppfStructurePresheaf B S hS 𝒳)
        (𝟙 ((affinePushforward.{u, w, u} g hg).obj N).val)
        ((affinePushforward.{u, w, u} g hg).map ψ).val ≫ directImageTensorPresheaf g hg N N'' =
      directImageTensorPresheaf g hg N N' ≫
        ((affinePushforward.{u, w, u} g hg).map (𝟙 N ⊗ₘ ψ)).val := by
  refine PresheafOfModules.hom_ext fun X => ModuleCat.MonoidalCategory.tensor_ext fun n n' => ?_
  have h1 := directImageTensorPresheaf_app_tmul g hg N N'' X n
    (ψ.val.app (op ((affineRightAdjoint g hg).obj X.unop)) n')
  have h2 := directImageTensorPresheaf_app_tmul g hg N N' X n n'
  have h3 := Stacks.SheafOfModules.tensorHom_val_app_toSheafify_tmul
    (fppfStructurePresheaf B S hS 𝒰) (fppfStructurePresheaf_isSheaf B S hS 𝒰) (𝟙 N) ψ
    (op ((affineRightAdjoint g hg).obj X.unop)) n n'
  exact h1.trans (h3.symm.trans (congrArg (fun z => (((affinePushforward.{u, w, u} g hg).map
    (𝟙 N ⊗ₘ ψ)).val.app X).hom z) h2.symm))

/-- **The lax structure of the affine direct image is natural in the right factor.** -/
theorem directImageTensor_naturality_right (N : Stack.fppfModules B S hS 𝒰)
    {N' N'' : Stack.fppfModules B S hS 𝒰} (ψ : N' ⟶ N'') :
    (𝟙 ((affinePushforward.{u, w, u} g hg).obj N) ⊗ₘ (affinePushforward.{u, w, u} g hg).map ψ) ≫
        directImageTensor g hg N N'' =
      directImageTensor g hg N N' ≫ (affinePushforward.{u, w, u} g hg).map (𝟙 N ⊗ₘ ψ) :=
  Stacks.SheafOfModules.tensorHom_comp_sheafify_map_comp (fppfStructurePresheaf B S hS 𝒳)
    (fppfStructurePresheaf_isSheaf B S hS 𝒳) ((affinePushforward.{u, w, u} g hg).map ψ)
    ((affinePushforward.{u, w, u} g hg).map (𝟙 N ⊗ₘ ψ)) _ _
    (directImageTensorPresheaf_naturality_right g hg N ψ)

/-- The objectwise tensorator of `g^*` followed by `g^*` of the sheafification unit. -/
def pullbackTensorPresheaf (M N : Stack.fppfModules B S hS 𝒳) :
    PresheafOfModules.Monoidal.tensorObj (R := fppfStructurePresheaf B S hS 𝒰)
        ((stackModulePullback.{u, w, u} g).obj M).val
        ((stackModulePullback.{u, w, u} g).obj N).val ⟶
      ((stackModulePullback.{u, w, u} g).obj (M ⊗ N)).val :=
  PresheafOfModules.pushforwardMu (F := g.hom.hom.toFunctor)
      (S := fppfStructurePresheaf B S hS 𝒰) (R := fppfStructurePresheaf B S hS 𝒳)
      (pullbackRingHom g).hom M.val N.val ≫
    (PresheafOfModules.pushforward (pullbackRingHom g).hom).map
      (Stacks.SheafOfModules.TensorSheafification.toSheafify (fppfStructurePresheaf B S hS 𝒳)
        (fppfStructurePresheaf_isSheaf B S hS 𝒳)
        (PresheafOfModules.Monoidal.tensorObj M.val N.val))

/-- On a pure tensor `m ⊗ₜ n` at `X`, the tensorator of `g^*` is the sheafification unit of
`M ⊗ N` at `g X`. -/
theorem pullbackTensorPresheaf_app_tmul (M N : Stack.fppfModules B S hS 𝒳)
    (X : 𝒰.val.val.objᵒᵖ) (m : M.val.obj (op (g.hom.hom.toFunctor.obj X.unop)))
    (n : N.val.obj (op (g.hom.hom.toFunctor.obj X.unop))) :
    ((pullbackTensorPresheaf g M N).app X).hom (m ⊗ₜ n) =
      (Stacks.SheafOfModules.TensorSheafification.toSheafify (fppfStructurePresheaf B S hS 𝒳)
        (fppfStructurePresheaf_isSheaf B S hS 𝒳)
        (PresheafOfModules.Monoidal.tensorObj M.val N.val)).app
          (op (g.hom.hom.toFunctor.obj X.unop)) (m ⊗ₜ n) :=
  congrArg (((PresheafOfModules.pushforward (pullbackRingHom g).hom).map
      (Stacks.SheafOfModules.TensorSheafification.toSheafify (fppfStructurePresheaf B S hS 𝒳)
        (fppfStructurePresheaf_isSheaf B S hS 𝒳)
        (PresheafOfModules.Monoidal.tensorObj M.val N.val))).app X).hom
    (PresheafOfModules.pushforwardMu_app_tmul (F := g.hom.hom.toFunctor)
      (S := fppfStructurePresheaf B S hS 𝒰) (R := fppfStructurePresheaf B S hS 𝒳)
      (pullbackRingHom g).hom M.val N.val X m n)

/-- **The tensor comparison `g^*M ⊗ g^*N ⟶ g^*(M ⊗ N)` of the inverse image** (strict
structure): the sheafification of the objectwise tensorator, followed by the counit. -/
def pullbackTensor (M N : Stack.fppfModules B S hS 𝒳) :
    (stackModulePullback.{u, w, u} g).obj M ⊗ (stackModulePullback.{u, w, u} g).obj N ⟶
      (stackModulePullback.{u, w, u} g).obj (M ⊗ N) :=
  (Stacks.SheafOfModules.sheafifyFunctor (fppfStructurePresheaf B S hS 𝒰)
      (fppfStructurePresheaf_isSheaf B S hS 𝒰)).map (pullbackTensorPresheaf g M N) ≫
    (Stacks.SheafOfModules.sheafifyValIso (fppfStructurePresheaf B S hS 𝒰)
      (fppfStructurePresheaf_isSheaf B S hS 𝒰) ((stackModulePullback.{u, w, u} g).obj (M ⊗ N))).hom

/-- `g^*` of the tensor comparison on the image of a local pure tensor. -/
theorem pullbackTensor_val_app_toSheafify (M N : Stack.fppfModules B S hS 𝒳)
    (X : 𝒰.val.val.objᵒᵖ) (m : M.val.obj (op (g.hom.hom.toFunctor.obj X.unop)))
    (n : N.val.obj (op (g.hom.hom.toFunctor.obj X.unop))) :
    (pullbackTensor g M N).val.app X ((Stacks.SheafOfModules.TensorSheafification.toSheafify
        (fppfStructurePresheaf B S hS 𝒰) (fppfStructurePresheaf_isSheaf B S hS 𝒰)
        (PresheafOfModules.Monoidal.tensorObj ((stackModulePullback.{u, w, u} g).obj M).val
          ((stackModulePullback.{u, w, u} g).obj N).val)).app X (m ⊗ₜ n)) =
      (Stacks.SheafOfModules.TensorSheafification.toSheafify (fppfStructurePresheaf B S hS 𝒳)
        (fppfStructurePresheaf_isSheaf B S hS 𝒳)
        (PresheafOfModules.Monoidal.tensorObj M.val N.val)).app
          (op (g.hom.hom.toFunctor.obj X.unop)) (m ⊗ₜ n) :=
  (Stacks.SheafOfModules.sheafify_map_comp_sheafifyValIso_hom_val_app_toSheafify
    (fppfStructurePresheaf B S hS 𝒰) (fppfStructurePresheaf_isSheaf B S hS 𝒰)
    (pullbackTensorPresheaf g M N) X (m ⊗ₜ n)).trans (pullbackTensorPresheaf_app_tmul g M N X m n)

/-- The lax structure of `g_*` on the image of a local pure tensor. -/
theorem directImageTensor_val_app_toSheafify (N N' : Stack.fppfModules B S hS 𝒰)
    (X : 𝒳.val.val.objᵒᵖ) (n : N.val.obj (op ((affineRightAdjoint g hg).obj X.unop)))
    (n' : N'.val.obj (op ((affineRightAdjoint g hg).obj X.unop))) :
    (directImageTensor g hg N N').val.app X ((Stacks.SheafOfModules.TensorSheafification.toSheafify
        (fppfStructurePresheaf B S hS 𝒳) (fppfStructurePresheaf_isSheaf B S hS 𝒳)
        (PresheafOfModules.Monoidal.tensorObj ((affinePushforward.{u, w, u} g hg).obj N).val
          ((affinePushforward.{u, w, u} g hg).obj N').val)).app X (n ⊗ₜ n')) =
      (Stacks.SheafOfModules.TensorSheafification.toSheafify (fppfStructurePresheaf B S hS 𝒰)
        (fppfStructurePresheaf_isSheaf B S hS 𝒰)
        (PresheafOfModules.Monoidal.tensorObj N.val N'.val)).app
          (op ((affineRightAdjoint g hg).obj X.unop)) (n ⊗ₜ n') :=
  (Stacks.SheafOfModules.sheafify_map_comp_sheafifyValIso_hom_val_app_toSheafify
    (fppfStructurePresheaf B S hS 𝒳) (fppfStructurePresheaf_isSheaf B S hS 𝒳)
    (directImageTensorPresheaf g hg N N') X (n ⊗ₜ n')).trans
    (directImageTensorPresheaf_app_tmul g hg N N' X n n')

/-- **The unit of `g^* ⊣ g_*` is compatible with the tensor products**: `η_{M ⊗ N}` is
`η_M ⊗ η_N` followed by the lax structure of `g_*` and `g_*` of the tensor comparison of `g^*`.
On a local pure tensor `m ⊗ n` over `x` both sides are `m|_{g(r x)} ⊗ n|_{g(r x)}`. -/
theorem unit_app_tensor (M N : Stack.fppfModules B S hS 𝒳) :
    (affinePullbackPushforwardAdjunction.{u, w, u} g hg).unit.app (M ⊗ N) =
      ((affinePullbackPushforwardAdjunction.{u, w, u} g hg).unit.app M ⊗ₘ
          (affinePullbackPushforwardAdjunction.{u, w, u} g hg).unit.app N) ≫
        directImageTensor g hg ((stackModulePullback.{u, w, u} g).obj M)
          ((stackModulePullback.{u, w, u} g).obj N) ≫
          (affinePushforward.{u, w, u} g hg).map (pullbackTensor g M N) := by
  refine Stacks.SheafOfModules.sheafify_tensor_hom_ext (fppfStructurePresheaf B S hS 𝒳)
    (fppfStructurePresheaf_isSheaf B S hS 𝒳) fun V m n => ?_
  have e1 := PresheafOfModules.naturality_apply
    (Stacks.SheafOfModules.TensorSheafification.toSheafify (fppfStructurePresheaf B S hS 𝒳)
      (fppfStructurePresheaf_isSheaf B S hS 𝒳) (PresheafOfModules.Monoidal.tensorObj M.val N.val))
    ((affineAdjunction g hg).counit.app V.unop).op (m ⊗ₜ n)
  have e2 := Stacks.SheafOfModules.tensorHom_val_app_toSheafify_tmul
    (fppfStructurePresheaf B S hS 𝒳) (fppfStructurePresheaf_isSheaf B S hS 𝒳)
    ((affinePullbackPushforwardAdjunction.{u, w, u} g hg).unit.app M)
    ((affinePullbackPushforwardAdjunction.{u, w, u} g hg).unit.app N) V m n
  have e3 := directImageTensor_val_app_toSheafify g hg ((stackModulePullback.{u, w, u} g).obj M)
    ((stackModulePullback.{u, w, u} g).obj N) V
    (M.val.map ((affineAdjunction g hg).counit.app V.unop).op m)
    (N.val.map ((affineAdjunction g hg).counit.app V.unop).op n)
  have e4 := pullbackTensor_val_app_toSheafify g M N (op ((affineRightAdjoint g hg).obj V.unop))
    (M.val.map ((affineAdjunction g hg).counit.app V.unop).op m)
    (N.val.map ((affineAdjunction g hg).counit.app V.unop).op n)
  refine e1.symm.trans (Eq.trans ?_ (congrArg (fun z => (pullbackTensor g M N).val.app _
    ((directImageTensor g hg _ _).val.app V z)) e2).symm)
  exact (e4.symm.trans (congrArg ((pullbackTensor g M N).val.app _) e3.symm))

end AlgebraicGeometry.Stack.AlgebraicStacks
