module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAlgebraPullbackIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerWedgeQuotient
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.ExteriorAlgebraComparison
public import StacksFrontier.AlgebraicGeometry.PullbackTensorIso.Invertible
public import StacksFrontier.AlgebraicGeometry.PullbackTensor.UniversalGradedAlgebra
public import StacksFrontier.AlgebraicGeometry.ProjectionFormulaMap.Basic

/-!
# Pullback of exterior powers and of the wedge maps

Let `f : X ⟶ Y` be a morphism of ringed spaces, `K ⟶ F` a morphism of sheaves of `𝒪_Y`-modules
and `K' ⟶ F'` one of `𝒪_X`-modules, identified with the pullback of the first by isomorphisms
`f^* K ≅ K'` and `f^* F ≅ F'`. The pullbacks of the exterior powers of `K` and `F` are the
exterior powers of `K'` and `F'`, compatibly with the induced maps on exterior powers, with the
products, and with the wedge maps `⋀ʳ K ⊗ F ⟶ ⋀ʳ⁺¹ F / ⋀ʳ⁺¹ K` of
`Stacks.SheafOfModules.WedgeQuotient`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.extPullbackIso`:
  `f^*(⋀ⁿ K) ≅ ⋀ⁿ K'`.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.extPullbackIso_extPowMap`: compatibility
  with the maps induced on exterior powers.
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.pullback_tensorSheaf_hom_ext`: morphisms
  out of the pullback of a tensor product are determined on pulled-back pure tensors.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.RingedSpace PresheafOfModules RingedSpaceModuleAdjunction
open SheafOfModules.GradedAlgebra
open scoped TensorProduct

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **Two morphisms out of the pullback of a tensor product that agree on the pullback-unit images
of the local pure tensors are equal.** -/
public theorem pullback_tensorSheaf_hom_ext
    {A B : _root_.SheafOfModules.{u} (structureRingSheaf Y)}
    {N : _root_.SheafOfModules.{u} (structureRingSheaf X)}
    {θ₁ θ₂ : (pullbackFunctor f).obj ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩)).obj
          (A, B)) ⟶ N}
    (h : ∀ (U : (Opens Y.carrier)ᵒᵖ) (a : A.val.obj U) (b : B.val.obj U),
      θ₁.val.app ((opensMap f).op.obj U)
          (pullbackUnit f ((Functor.uncurry.obj
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                  ⟨Y.presheaf, Y.IsSheaf⟩)).obj (A, B)) U
            ((tensorSheafUnit (Osharp := Y.sheaf) A B).app U (a ⊗ₜ b))) =
        θ₂.val.app ((opensMap f).op.obj U)
          (pullbackUnit f ((Functor.uncurry.obj
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                  ⟨Y.presheaf, Y.IsSheaf⟩)).obj (A, B)) U
            ((tensorSheafUnit (Osharp := Y.sheaf) A B).app U (a ⊗ₜ b)))) :
    θ₁ = θ₂ := by
  refine ((pullbackAdjunction f).homEquiv _ N).injective ?_
  refine PresheafOfModules.tensorSheaf_hom_ext (Osharp := Y.sheaf) (F := A) (G := B)
    (Q := (pushforwardFunctor f).obj N) fun U a b ↦ ?_
  exact (SheafOfModules.GradedAlgebra.homEquiv_val_app f θ₁ U _).trans
    ((h U a b).trans (SheafOfModules.GradedAlgebra.homEquiv_val_app f θ₂ U _).symm)


/-- The tensor product of two morphisms of sheaves of modules on a ringed space. -/
public abbrev tensorMap {Z : RingedSpace.{u, u}}
    {A A' B B' : _root_.SheafOfModules.{u} (structureRingSheaf Z)} (a : A ⟶ A') (b : B ⟶ B') :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨Z.presheaf, Z.IsSheaf⟩)).obj
        (A, B) ⟶
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨Z.presheaf, Z.IsSheaf⟩)).obj
        (A', B') :=
  (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Z.presheaf, Z.IsSheaf⟩)).map
    (X := (A, B)) (Y := (A', B')) (a, b)

/-- `tensorMap` is compatible with composition in both variables. -/
@[reassoc]
public theorem tensorMap_comp {Z : RingedSpace.{u, u}}
    {A A' A'' B B' B'' : _root_.SheafOfModules.{u} (structureRingSheaf Z)} (a : A ⟶ A')
    (a' : A' ⟶ A'') (b : B ⟶ B') (b' : B' ⟶ B'') :
    tensorMap a b ≫ tensorMap a' b' = tensorMap (a ≫ a') (b ≫ b') :=
  ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Z.presheaf, Z.IsSheaf⟩)).map_comp
    (X := (A, B)) (Y := (A', B')) (Z := (A'', B'')) (a, b) (a', b')).symm

/-- `tensorMap` of the identities is the identity. -/
public theorem tensorMap_id {Z : RingedSpace.{u, u}}
    (A B : _root_.SheafOfModules.{u} (structureRingSheaf Z)) :
    tensorMap (𝟙 A) (𝟙 B) = 𝟙 _ :=
  (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Z.presheaf, Z.IsSheaf⟩)).map_id
    (A, B)

/-- **Naturality of the comparison of Tag 01CD** in both variables. -/
@[reassoc]
public theorem comparison_naturality {A A' B B' : _root_.SheafOfModules.{u} (structureRingSheaf Y)}
    (a : A ⟶ A') (b : B ⟶ B') :
    (pullbackFunctor f).map (tensorMap a b) ≫ Stacks.RingedSpace.comparison f A' B' =
      Stacks.RingedSpace.comparison f A B ≫
        tensorMap ((pullbackFunctor f).map a) ((pullbackFunctor f).map b) :=
  (Stacks.RingedSpace.comparisonNatTrans f).naturality (X := (A, B)) (Y := (A', B')) (a, b)


section TensorPullback

variable {M M' : _root_.SheafOfModules.{u} (structureRingSheaf Y)}
  {N N' : _root_.SheafOfModules.{u} (structureRingSheaf X)}
  {L : _root_.SheafOfModules.{u} (structureRingSheaf Y)}
  {L' : _root_.SheafOfModules.{u} (structureRingSheaf X)}

/-- `f^*(M ⊗ L) ≅ N ⊗ L'` from `f^* M ≅ N` and `f^* L ≅ L'`, through the comparison of
Tag 01CD. -/
public def tensorPullbackIso (a : (pullbackFunctor f).obj M ≅ N)
    (l : (pullbackFunctor f).obj L ≅ L') :
    (pullbackFunctor f).obj ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩)).obj
            (M, L)) ≅
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨X.presheaf, X.IsSheaf⟩)).obj
        (N, L') :=
  asIso (Stacks.RingedSpace.comparison f M L) ≪≫
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.presheaf, X.IsSheaf⟩)).mapIso
      (X := ((pullbackFunctor f).obj M, (pullbackFunctor f).obj L))
      (Y := (N, L')) (Iso.prod a l)

/-- `tensorPullbackIso` is natural in the first factor. -/
@[reassoc]
public theorem tensorPullbackIso_naturality (a : (pullbackFunctor f).obj M ≅ N)
    (a' : (pullbackFunctor f).obj M' ≅ N') (l : (pullbackFunctor f).obj L ≅ L') (g : M ⟶ M')
    (g' : N ⟶ N') (hg : (pullbackFunctor f).map g ≫ a'.hom = a.hom ≫ g') :
    (pullbackFunctor f).map (tensorMap g (𝟙 L)) ≫ (tensorPullbackIso f a' l).hom =
      (tensorPullbackIso f a l).hom ≫ tensorMap g' (𝟙 L') := by
  change (pullbackFunctor f).map (tensorMap g (𝟙 L)) ≫
      Stacks.RingedSpace.comparison f M' L ≫ tensorMap a'.hom l.hom =
    (Stacks.RingedSpace.comparison f M L ≫ tensorMap a.hom l.hom) ≫ tensorMap g' (𝟙 L')
  have hl : (pullbackFunctor f).map (𝟙 L) ≫ l.hom = l.hom ≫ 𝟙 L' := by
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  refine (comparison_naturality_assoc f g (𝟙 L) (tensorMap a'.hom l.hom)).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  exact congrArg (Stacks.RingedSpace.comparison f M L ≫ ·)
    ((tensorMap_comp _ _ _ _).trans
      ((congrArg₂ tensorMap hg hl).trans (tensorMap_comp _ _ _ _).symm))

/-- `tensorPullbackIso` is natural in both factors. -/
@[reassoc]
public theorem tensorPullbackIso_naturality₂
    {M M' L₁ L₂ : _root_.SheafOfModules.{u} (structureRingSheaf Y)}
    {N N' L₁' L₂' : _root_.SheafOfModules.{u} (structureRingSheaf X)}
    (a : (pullbackFunctor f).obj M ≅ N) (a' : (pullbackFunctor f).obj M' ≅ N')
    (l : (pullbackFunctor f).obj L₁ ≅ L₁') (l' : (pullbackFunctor f).obj L₂ ≅ L₂')
    (g : M ⟶ M') (g' : N ⟶ N') (k : L₁ ⟶ L₂) (k' : L₁' ⟶ L₂')
    (hg : (pullbackFunctor f).map g ≫ a'.hom = a.hom ≫ g')
    (hk : (pullbackFunctor f).map k ≫ l'.hom = l.hom ≫ k') :
    (pullbackFunctor f).map (tensorMap g k) ≫ (tensorPullbackIso f a' l').hom =
      (tensorPullbackIso f a l).hom ≫ tensorMap g' k' := by
  change (pullbackFunctor f).map (tensorMap g k) ≫
      Stacks.RingedSpace.comparison f M' L₂ ≫ tensorMap a'.hom l'.hom =
    (Stacks.RingedSpace.comparison f M L₁ ≫ tensorMap a.hom l.hom) ≫ tensorMap g' k'
  refine (comparison_naturality_assoc f g k (tensorMap a'.hom l'.hom)).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  exact congrArg (Stacks.RingedSpace.comparison f M L₁ ≫ ·)
    ((tensorMap_comp _ _ _ _).trans
      ((congrArg₂ tensorMap hg hk).trans (tensorMap_comp _ _ _ _).symm))

/-- `tensorPullbackIso` on the pullback of a pure tensor. -/
public theorem tensorPullbackIso_unit {M L : _root_.SheafOfModules.{u} (structureRingSheaf Y)}
    {N L' : _root_.SheafOfModules.{u} (structureRingSheaf X)}
    (a : (pullbackFunctor f).obj M ≅ N) (l : (pullbackFunctor f).obj L ≅ L')
    (U : (Opens Y.carrier)ᵒᵖ) (x : M.val.obj U) (y : L.val.obj U) :
    (tensorPullbackIso f a l).hom.val.app ((opensMap f).op.obj U)
        (pullbackUnit f _ U ((tensorSheafUnit (Osharp := Y.sheaf) M L).app U (x ⊗ₜ y))) =
      (tensorSheafUnit (Osharp := X.sheaf) N L').app ((opensMap f).op.obj U)
        (a.hom.val.app _ (pullbackUnit f M U x) ⊗ₜ l.hom.val.app _ (pullbackUnit f L U y)) := by
  refine Eq.trans (_root_.SheafOfModules.comp_val_app_apply _ _ _ _) ?_
  refine Eq.trans (congrArg _ (Stacks.RingedSpace.comparison_pullbackUnit_tmul f M L U x y)) ?_
  exact Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit
    (J := Opens.grothendieckTopology X.carrier) (Osharp := X.sheaf)
    (f := a.hom) (g := l.hom) (V := (opensMap f).op.obj U) _ _ _ _

/-- **Two morphisms out of the pullback of an iterated tensor product that agree on the
pulled-back triple pure tensors are equal.** -/
public theorem pullback_tensorSheaf_hom_ext₂
    {A B C : _root_.SheafOfModules.{u} (structureRingSheaf Y)}
    {N : _root_.SheafOfModules.{u} (structureRingSheaf X)}
    {θ₁ θ₂ : (pullbackFunctor f).obj ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨Y.presheaf, Y.IsSheaf⟩)).obj ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩)).obj
            (A, B), C)) ⟶ N}
    (h : ∀ (U : (Opens Y.carrier)ᵒᵖ) (a : A.val.obj U) (b : B.val.obj U) (c : C.val.obj U),
      θ₁.val.app ((opensMap f).op.obj U)
          (pullbackUnit f _ U ((tensorSheafUnit (Osharp := Y.sheaf) _ C).app U
            ((tensorSheafUnit (Osharp := Y.sheaf) A B).app U (a ⊗ₜ b) ⊗ₜ c))) =
        θ₂.val.app ((opensMap f).op.obj U)
          (pullbackUnit f _ U ((tensorSheafUnit (Osharp := Y.sheaf) _ C).app U
            ((tensorSheafUnit (Osharp := Y.sheaf) A B).app U (a ⊗ₜ b) ⊗ₜ c)))) :
    θ₁ = θ₂ := by
  refine ((pullbackAdjunction f).homEquiv _ N).injective ?_
  refine PresheafOfModules.tensorSheaf_hom_ext₂ (Osharp := Y.sheaf) (F := A) (G := B) (H := C)
    (Q := (pushforwardFunctor f).obj N) fun U a b c ↦ ?_
  exact (SheafOfModules.GradedAlgebra.homEquiv_val_app f θ₁ U _).trans
    ((h U a b c).trans (SheafOfModules.GradedAlgebra.homEquiv_val_app f θ₂ U _).symm)

/-- The associator of the tensor product on a ringed space. -/
public abbrev tensorAssoc (Z : RingedSpace.{u, u})
    (A B C : _root_.SheafOfModules.{u} (structureRingSheaf Z)) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨Z.presheaf, Z.IsSheaf⟩)).obj
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨Z.presheaf, Z.IsSheaf⟩)).obj
          (A, B), C) ≅
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨Z.presheaf, Z.IsSheaf⟩)).obj
        (A, (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨Z.presheaf, Z.IsSheaf⟩)).obj
          (B, C)) :=
  Stacks.SheafOfModules.tensorSheafAssociator Z.sheaf.obj
    (CategoryTheory.Sheaf.toRingCat (Opens.grothendieckTopology Z.carrier) Z.sheaf).property A B C

/-- The associator on a triple pure tensor. -/
public theorem tensorAssoc_unit (Z : RingedSpace.{u, u})
    (A B C : _root_.SheafOfModules.{u} (structureRingSheaf Z)) (U : (Opens Z.carrier)ᵒᵖ)
    (a : A.val.obj U) (b : B.val.obj U) (c : C.val.obj U) :
    (tensorAssoc Z A B C).hom.val.app U ((tensorSheafUnit (Osharp := Z.sheaf) _ C).app U
        ((tensorSheafUnit (Osharp := Z.sheaf) A B).app U (a ⊗ₜ b) ⊗ₜ c)) =
      (tensorSheafUnit (Osharp := Z.sheaf) A _).app U
        (a ⊗ₜ (tensorSheafUnit (Osharp := Z.sheaf) B C).app U (b ⊗ₜ c)) :=
  Stacks.SheafOfModules.tensorSheafAssociator_hom_val_app_tmul _ _ A B C U a b c

/-- **`tensorPullbackIso` is compatible with the associators.** -/
public theorem tensorPullbackIso_assoc {A B C : _root_.SheafOfModules.{u} (structureRingSheaf Y)}
    {A' B' C' : _root_.SheafOfModules.{u} (structureRingSheaf X)}
    (a : (pullbackFunctor f).obj A ≅ A') (b : (pullbackFunctor f).obj B ≅ B')
    (c : (pullbackFunctor f).obj C ≅ C') :
    (pullbackFunctor f).map (tensorAssoc Y A B C).hom ≫
        (tensorPullbackIso f a (tensorPullbackIso f b c)).hom =
      (tensorPullbackIso f (tensorPullbackIso f a b) c).hom ≫ (tensorAssoc X A' B' C').hom := by
  refine pullback_tensorSheaf_hom_ext₂ f fun U x y z => ?_
  refine Eq.trans (congrArg ((tensorPullbackIso f a (tensorPullbackIso f b c)).hom.val.app _)
    ((pullbackUnit_naturality f _ U _).trans (congrArg (pullbackUnit f _ U)
      (tensorAssoc_unit Y A B C U x y z)))) ?_
  refine Eq.trans (tensorPullbackIso_unit f a (tensorPullbackIso f b c) U x _) ?_
  refine Eq.trans (congrArg (fun w => (tensorSheafUnit (Osharp := X.sheaf) A' _).app _
    (a.hom.val.app _ (pullbackUnit f A U x) ⊗ₜ w)) (tensorPullbackIso_unit f b c U y z)) ?_
  refine Eq.trans (tensorAssoc_unit X A' B' C' _ _ _ _).symm ?_
  refine congrArg ((tensorAssoc X A' B' C').hom.val.app _) ?_
  refine Eq.trans ?_ (tensorPullbackIso_unit f (tensorPullbackIso f a b) c U _ z).symm
  exact congrArg (fun w => (tensorSheafUnit (Osharp := X.sheaf) _ C').app _ (w ⊗ₜ c.hom.val.app _
    (pullbackUnit f C U z))) (tensorPullbackIso_unit f a b U x y).symm

/-- **The projection formula morphism on a pure tensor**: `s ⊗ t ↦ s ⊗ f^* t`. -/
public theorem projectionFormulaMap'_unit_tmul
    (G : _root_.SheafOfModules.{u} (structureRingSheaf X))
    (H : _root_.SheafOfModules.{u} (structureRingSheaf Y)) (U : (Opens Y.carrier)ᵒᵖ)
    (s : ((pushforwardFunctor f).obj G).val.obj U) (t : H.val.obj U) :
    (Stacks.ProjectionFormula.projectionFormulaMap' f G H).val.app U
        ((tensorSheafUnit (Osharp := Y.sheaf) _ H).app U (s ⊗ₜ t)) =
      (tensorSheafUnit (Osharp := X.sheaf) G ((pullbackFunctor f).obj H)).app
        ((opensMap f).op.obj U) (s ⊗ₜ pullbackUnit f H U t) := by
  refine Eq.trans (SheafOfModules.GradedAlgebra.homEquiv_val_app f _ U _) ?_
  refine Eq.trans (_root_.SheafOfModules.comp_val_app_apply _ _ _ _) ?_
  refine Eq.trans (congrArg _ (Stacks.RingedSpace.comparison_pullbackUnit_tmul f _ H U s t)) ?_
  refine Eq.trans (Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit
    (J := Opens.grothendieckTopology X.carrier) (Osharp := X.sheaf)
    (f := (pullbackAdjunction f).counit.app G) (g := 𝟙 _) (V := (opensMap f).op.obj U) _ _ _ _) ?_
  have htri := congrArg (fun φ => φ.val.app U s)
    ((pullbackAdjunction f).right_triangle_components G)
  exact congrArg (fun z => (tensorSheafUnit (Osharp := X.sheaf) G ((pullbackFunctor f).obj H)).app _
    (z ⊗ₜ pullbackUnit f H U t)) htri

end TensorPullback

section Mul

variable {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Y)}
  {B : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf X)}
  (θ : ∀ d : ℤ, (pullbackFunctor f).obj (A.piece d) ⟶ B.piece d)

/-- **A family `f^* A_d ⟶ B_d` multiplicative on pulled-back sections intertwines the
multiplication maps** `A_i ⊗ A_j ⟶ A_{i+j}` and `B_i ⊗ B_j ⟶ B_{i+j}`, through the comparison of
Tag 01CD. -/
public theorem pullback_mulSheaf (i j : ℤ)
    (hθ : ∀ (U : (Opens Y.carrier)ᵒᵖ) (x : (A.piece i).val.obj U) (y : (A.piece j).val.obj U),
      (θ (i + j)).val.app ((opensMap f).op.obj U)
          (pullbackUnit f (A.piece (i + j)) U ((A.mul i j).app U x y)) =
        (B.mul i j).app ((opensMap f).op.obj U)
          ((θ i).val.app ((opensMap f).op.obj U) (pullbackUnit f (A.piece i) U x))
          ((θ j).val.app ((opensMap f).op.obj U) (pullbackUnit f (A.piece j) U y))) :
    (pullbackFunctor f).map (SheafOfModules.GradedAlgebra.mulSheaf
        (J := Opens.grothendieckTopology Y.carrier) (Osharp := Y.sheaf) A i j) ≫ θ (i + j) =
      Stacks.RingedSpace.comparison f (A.piece i) (A.piece j) ≫ tensorMap (θ i) (θ j) ≫
        SheafOfModules.GradedAlgebra.mulSheaf
          (J := Opens.grothendieckTopology X.carrier) (Osharp := X.sheaf) B i j := by
  refine pullback_tensorSheaf_hom_ext f fun U x y => ?_
  have hR := Stacks.RingedSpace.comparison_pullbackUnit_tmul f (A.piece i) (A.piece j) U x y
  have hM : (tensorMap (θ i) (θ j)).val.app ((opensMap f).op.obj U)
        ((tensorSheafUnit (Osharp := X.sheaf) _ _).app ((opensMap f).op.obj U)
          (pullbackUnit f _ U x ⊗ₜ pullbackUnit f _ U y)) =
      (tensorSheafUnit (Osharp := X.sheaf) (B.piece i) (B.piece j)).app ((opensMap f).op.obj U)
        ((θ i).val.app _ (pullbackUnit f _ U x) ⊗ₜ (θ j).val.app _ (pullbackUnit f _ U y)) :=
    Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit
      (J := Opens.grothendieckTopology X.carrier) (Osharp := X.sheaf)
      (f := θ i) (g := θ j) (V := (opensMap f).op.obj U) _ _ _ _
  refine Eq.trans (congrArg ((θ (i + j)).val.app _)
    ((pullbackUnit_naturality f _ U _).trans (congrArg (pullbackUnit f _ U)
      (SheafOfModules.GradedAlgebra.mulSheaf_unit (J := Opens.grothendieckTopology Y.carrier)
        (Osharp := Y.sheaf) A i j U x y)))) ?_
  refine Eq.trans (hθ U x y) ?_
  refine Eq.trans ?_ (congrArg ((SheafOfModules.GradedAlgebra.mulSheaf
    (J := Opens.grothendieckTopology X.carrier) (Osharp := X.sheaf) B i j).val.app _)
    (hM.symm.trans (congrArg ((tensorMap (θ i) (θ j)).val.app _) hR.symm)))
  exact (SheafOfModules.GradedAlgebra.mulSheaf_unit (J := Opens.grothendieckTopology X.carrier)
    (Osharp := X.sheaf) B i j _ _ _).symm

end Mul

section Exterior

variable {K : _root_.SheafOfModules.{u} (structureRingSheaf Y)}
  {K' : _root_.SheafOfModules.{u} (structureRingSheaf X)}
  (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology Y.carrier)
    (Osharp := Y.sheaf) K)
  (A' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (Osharp := X.sheaf) K')
  (l : (pullbackFunctor f).obj K ≅ K')

/-- The pulled-back generator `f^* K ≅ K' ⟶ ⋀¹ K'` is square-zero. -/
public theorem squareZero_extPullbackGenerator : SquareZero (l.hom ≫ A'.exteriorGenerator) :=
  SquareZero.comp A'.exterior_isExteriorAlgebra.1 l.hom

include l

/-- **`f^*(⋀ⁿ K) ≅ ⋀ⁿ K'`**: the comparison of Tag 01CI, followed by the identification
`f^* K ≅ K'`. -/
public def extPullbackIso (n : ℤ) :
    (pullbackFunctor f).obj (A.exterior.piece n) ≅ A'.exterior.piece n :=
  Stacks.PullbackExteriorAlgebra.pieceIso f A.exterior A.exterior_isExteriorAlgebra
    (squareZero_extPullbackGenerator f A' l)
    (A'.exterior_isExteriorAlgebra.comp_iso l.hom inferInstance) n

/-- `extPullbackIso` on the pullback of a product. -/
public theorem extPullbackIso_mul (i j : ℤ) (U : (Opens Y.carrier)ᵒᵖ)
    (x : (A.exterior.piece i).val.obj U) (y : (A.exterior.piece j).val.obj U) :
    (extPullbackIso f A A' l (i + j)).hom.val.app ((opensMap f).op.obj U)
        (pullbackUnit f (A.exterior.piece (i + j)) U ((A.exterior.mul i j).app U x y)) =
      (A'.exterior.mul i j).app ((opensMap f).op.obj U)
        ((extPullbackIso f A A' l i).hom.val.app ((opensMap f).op.obj U)
          (pullbackUnit f (A.exterior.piece i) U x))
        ((extPullbackIso f A A' l j).hom.val.app ((opensMap f).op.obj U)
          (pullbackUnit f (A.exterior.piece j) U y)) :=
  Stacks.PullbackExteriorAlgebra.comparisonHom_mul f A.exterior _ _ i j U x y

/-- `extPullbackIso` on the pullback of the unit. -/
public theorem extPullbackIso_one (U : (Opens Y.carrier)ᵒᵖ) :
    (extPullbackIso f A A' l 0).hom.val.app ((opensMap f).op.obj U)
        (pullbackUnit f (A.exterior.piece 0) U (A.exterior.one.eval U)) =
      A'.exterior.one.eval ((opensMap f).op.obj U) :=
  Stacks.PullbackExteriorAlgebra.comparisonHom_one f A.exterior _ _ U

/-- `extPullbackIso` on the pullback of a generator. -/
public theorem extPullbackIso_generator (U : (Opens Y.carrier)ᵒᵖ) (s : K.val.obj U) :
    (extPullbackIso f A A' l 1).hom.val.app ((opensMap f).op.obj U)
        (pullbackUnit f (A.exterior.piece 1) U (A.exteriorGenerator.val.app U s)) =
      A'.exteriorGenerator.val.app ((opensMap f).op.obj U)
        (l.hom.val.app ((opensMap f).op.obj U) (pullbackUnit f K U s)) :=
  Stacks.PullbackExteriorAlgebra.comparisonHom_generator f A.exterior _ _ U s

/-- `extPullbackIso` in degree one, on the generator, as an identity of morphisms. -/
public theorem extPullbackIso_generator_hom :
    (pullbackFunctor f).map A.exteriorGenerator ≫ (extPullbackIso f A A' l 1).hom =
      l.hom ≫ A'.exteriorGenerator :=
  Stacks.PullbackTensorCoherence.pullback_hom_ext f fun U s =>
    (congrArg ((extPullbackIso f A A' l 1).hom.val.app _)
      (pullbackUnit_naturality f A.exteriorGenerator U s)).trans
      (extPullbackIso_generator f A A' l U s)

end Exterior


section ExtHom

open Stacks.SheafOfModules.TopWedge

variable {K F : _root_.SheafOfModules.{u} (structureRingSheaf Y)}
  {K' F' : _root_.SheafOfModules.{u} (structureRingSheaf X)}
  (AK : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology Y.carrier)
    (Osharp := Y.sheaf) K)
  (AF : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology Y.carrier)
    (Osharp := Y.sheaf) F)
  (AK' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (Osharp := X.sheaf) K')
  (AF' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (Osharp := X.sheaf) F')
  (ι : K ⟶ F) (ι' : K' ⟶ F') (l : (pullbackFunctor f).obj K ≅ K')
  (k : (pullbackFunctor f).obj F ≅ F')
  (hlk : (pullbackFunctor f).map ι ≫ k.hom = l.hom ≫ ι')

include hlk in
/-- **The pullback of the map induced on exterior powers is the map induced on exterior
powers**, under the comparisons `f^*(⋀ⁿ K) ≅ ⋀ⁿ K'` and `f^*(⋀ⁿ F) ≅ ⋀ⁿ F'`. -/
public theorem extPullbackIso_extHom (n : ℤ) :
    (pullbackFunctor f).map ((extHom AK AF ι).app n) ≫ (extPullbackIso f AF AF' k n).hom =
      (extPullbackIso f AK AK' l n).hom ≫ (extHom AK' AF' ι').app n := by
  have hκ : SquareZero (l.hom ≫ ι' ≫ AF'.exteriorGenerator) :=
    SquareZero.comp (SquareZero.comp AF'.exterior_isExteriorAlgebra.1 ι') l.hom
  have hgen : ∀ (U : (Opens Y.carrier)ᵒᵖ) (s : K.val.obj U),
      AF'.exteriorGenerator.val.app ((opensMap f).op.obj U)
          (k.hom.val.app ((opensMap f).op.obj U) (pullbackUnit f F U (ι.val.app U s))) =
        (l.hom ≫ ι' ≫ AF'.exteriorGenerator).val.app ((opensMap f).op.obj U)
          (pullbackUnit f K U s) := by
    intro U s
    have h1 := congrArg (fun φ => φ.val.app ((opensMap f).op.obj U) (pullbackUnit f K U s)) hlk
    exact congrArg (AF'.exteriorGenerator.val.app ((opensMap f).op.obj U))
      ((congrArg (k.hom.val.app ((opensMap f).op.obj U))
        (pullbackUnit_naturality f ι U s)).symm.trans h1)
  refine (pullbackComparison_unique f AK.exterior_isExteriorAlgebra hκ
    (fun n => (pullbackFunctor f).map ((extHom AK AF ι).app n) ≫ (extPullbackIso f AF AF' k n).hom)
    (fun i j U a b => ?_) (fun U => ?_) (fun U s => ?_) n).trans
    (pullbackComparison_unique f AK.exterior_isExteriorAlgebra hκ
    (fun n => (extPullbackIso f AK AK' l n).hom ≫ (extHom AK' AF' ι').app n)
    (fun i j U a b => ?_) (fun U => ?_) (fun U s => ?_) n).symm
  · refine Eq.trans (congrArg ((extPullbackIso f AF AF' k (i + j)).hom.val.app _)
      ((pullbackUnit_naturality f ((extHom AK AF ι).app (i + j)) U _).trans
        (congrArg (pullbackUnit f _ U) ((extHom AK AF ι).map_mul i j U a b)))) ?_
    refine Eq.trans (extPullbackIso_mul f AF AF' k i j U _ _) ?_
    exact congrArg₂ (fun x y => (AF'.exterior.mul i j).app ((opensMap f).op.obj U) x y)
      (congrArg ((extPullbackIso f AF AF' k i).hom.val.app _)
        (pullbackUnit_naturality f ((extHom AK AF ι).app i) U a).symm)
      (congrArg ((extPullbackIso f AF AF' k j).hom.val.app _)
        (pullbackUnit_naturality f ((extHom AK AF ι).app j) U b).symm)
  · refine Eq.trans (congrArg ((extPullbackIso f AF AF' k 0).hom.val.app _)
      ((pullbackUnit_naturality f ((extHom AK AF ι).app 0) U _).trans
        (congrArg (pullbackUnit f _ U) ((extHom AK AF ι).map_one U)))) ?_
    exact extPullbackIso_one f AF AF' k U
  · refine Eq.trans (congrArg ((extPullbackIso f AF AF' k 1).hom.val.app _)
      ((pullbackUnit_naturality f ((extHom AK AF ι).app 1) U _).trans
        (congrArg (pullbackUnit f _ U) (extHom_app_one AK AF ι U s)))) ?_
    exact (extPullbackIso_generator f AF AF' k U (ι.val.app U s)).trans (hgen U s)
  · refine Eq.trans (congrArg (((extHom AK' AF' ι').app (i + j)).val.app _)
      (extPullbackIso_mul f AK AK' l i j U a b)) ?_
    exact (extHom AK' AF' ι').map_mul i j _ _ _
  · refine Eq.trans (congrArg (((extHom AK' AF' ι').app 0).val.app _)
      (extPullbackIso_one f AK AK' l U)) ?_
    exact (extHom AK' AF' ι').map_one _
  · refine Eq.trans (congrArg (((extHom AK' AF' ι').app 1).val.app _)
      (extPullbackIso_generator f AK AK' l U s)) ?_
    exact extHom_app_one AK' AF' ι' _ _

include hlk in
/-- **The pullback of the wedge map is the wedge map**, under the comparisons of exterior powers
and the comparison of Tag 01CD. -/
public theorem extPullbackIso_wedgeHom (r s : ℕ) :
    (pullbackFunctor f).map (wedgeHom AK AF ι r s) ≫ (extPullbackIso f AF AF' k (r + s : ℕ)).hom =
      Stacks.RingedSpace.comparison f (AK.exteriorPower r) (AF.exteriorPower s) ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨X.presheaf, X.IsSheaf⟩)).map (X := ((pullbackFunctor f).obj (AK.exteriorPower r),
            (pullbackFunctor f).obj (AF.exteriorPower s)))
          (Y := (AK'.exteriorPower r, AF'.exteriorPower s))
          ((extPullbackIso f AK AK' l r).hom, (extPullbackIso f AF AF' k s).hom) ≫
        wedgeHom AK' AF' ι' r s := by
  refine pullback_tensorSheaf_hom_ext f fun U x y => ?_
  have hext := congrArg (fun φ => φ.val.app ((opensMap f).op.obj U)
    (pullbackUnit f (AK.exteriorPower r) U x))
      (extPullbackIso_extHom f AK AF AK' AF' ι ι' l k hlk r)
  have hL : ((pullbackFunctor f).map (wedgeHom AK AF ι r s)).val.app ((opensMap f).op.obj U)
      (pullbackUnit f _ U ((tensorSheafUnit (Osharp := Y.sheaf) _ _).app U (x ⊗ₜ y))) =
      pullbackUnit f (AF.exterior.piece ((r : ℤ) + (s : ℤ))) U
        ((AF.exterior.mul (r : ℤ) (s : ℤ)).app U (((extHom AK AF ι).app r).val.app U x) y) :=
    (pullbackUnit_naturality f (wedgeHom AK AF ι r s) U _).trans
      (congrArg (pullbackUnit f _ U) (wedgeHom_unit AK AF ι r s U x y))
  have hR : (Stacks.RingedSpace.comparison f (AK.exteriorPower r) (AF.exteriorPower s)).val.app
      ((opensMap f).op.obj U)
      (pullbackUnit f _ U ((tensorSheafUnit (Osharp := Y.sheaf) _ _).app U (x ⊗ₜ y))) =
      (tensorSheafUnit (Osharp := X.sheaf) _ _).app ((opensMap f).op.obj U)
        (pullbackUnit f _ U x ⊗ₜ pullbackUnit f _ U y) :=
    Stacks.RingedSpace.comparison_pullbackUnit_tmul f _ _ U x y
  have hM : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.presheaf, X.IsSheaf⟩)).map (X := ((pullbackFunctor f).obj (AK.exteriorPower r),
            (pullbackFunctor f).obj (AF.exteriorPower s)))
          (Y := (AK'.exteriorPower r, AF'.exteriorPower s))
          ((extPullbackIso f AK AK' l r).hom, (extPullbackIso f AF AF' k s).hom)).val.app
        ((opensMap f).op.obj U) ((tensorSheafUnit (Osharp := X.sheaf) _ _).app
            ((opensMap f).op.obj U)
          (pullbackUnit f _ U x ⊗ₜ pullbackUnit f _ U y)) =
      (tensorSheafUnit (Osharp := X.sheaf) (AK'.exteriorPower r)
          (AF'.exteriorPower s)).app ((opensMap f).op.obj U)
        ((extPullbackIso f AK AK' l r).hom.val.app _ (pullbackUnit f _ U x) ⊗ₜ
          (extPullbackIso f AF AF' k s).hom.val.app _ (pullbackUnit f _ U y)) :=
    Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit
      (J := Opens.grothendieckTopology X.carrier) (Osharp := X.sheaf)
      (f := (extPullbackIso f AK AK' l r).hom) (g := (extPullbackIso f AF AF' k s).hom)
      (V := (opensMap f).op.obj U) _ _ _ _
  have hx : (extPullbackIso f AF AF' k r).hom.val.app ((opensMap f).op.obj U)
      (pullbackUnit f _ U (((extHom AK AF ι).app r).val.app U x)) =
      ((extHom AK' AF' ι').app r).val.app _
        ((extPullbackIso f AK AK' l r).hom.val.app _ (pullbackUnit f _ U x)) :=
    (congrArg ((extPullbackIso f AF AF' k r).hom.val.app _)
      (pullbackUnit_naturality f ((extHom AK AF ι).app r) U x)).symm.trans hext
  refine Eq.trans (congrArg ((extPullbackIso f AF AF' k (r + s : ℕ)).hom.val.app _) hL) ?_
  refine Eq.trans (extPullbackIso_mul f AF AF' k r s U _ _) ?_
  refine Eq.trans (congrArg (fun z => (AF'.exterior.mul (r : ℤ) (s : ℤ)).app ((opensMap f).op.obj U)
    z ((extPullbackIso f AF AF' k s).hom.val.app _ (pullbackUnit f _ U y))) hx) ?_
  refine Eq.trans (wedgeHom_unit AK' AF' ι' r s _ _ _).symm ?_
  refine Eq.trans (congrArg ((wedgeHom AK' AF' ι' r s).val.app _) hM.symm) ?_
  exact congrArg (fun z => (wedgeHom AK' AF' ι' r s).val.app _
    (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.presheaf, X.IsSheaf⟩)).map (X := ((pullbackFunctor f).obj (AK.exteriorPower r),
            (pullbackFunctor f).obj (AF.exteriorPower s)))
          (Y := (AK'.exteriorPower r, AF'.exteriorPower s))
          ((extPullbackIso f AK AK' l r).hom, (extPullbackIso f AF AF' k s).hom)).val.app _ z))
    hR.symm

end ExtHom

section Quotient

open Stacks.SheafOfModules.TopWedge Stacks.SheafOfModules.WedgeQuotient

variable {K F L : _root_.SheafOfModules.{u} (structureRingSheaf Y)}
  {K' F' L' : _root_.SheafOfModules.{u} (structureRingSheaf X)}
  (AK : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology Y.carrier)
    (Osharp := Y.sheaf) K)
  (AF : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology Y.carrier)
    (Osharp := Y.sheaf) F)
  (AK' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (Osharp := X.sheaf) K')
  (AF' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (Osharp := X.sheaf) F')
  (ι : K ⟶ F) (ι' : K' ⟶ F') (l : (pullbackFunctor f).obj K ≅ K')
  (k : (pullbackFunctor f).obj F ≅ F')
  (hlk : (pullbackFunctor f).map ι ≫ k.hom = l.hom ≫ ι')

/-- The pullback of the cokernel of `⋀ʳ K ⟶ ⋀ʳ F` is the cokernel of `⋀ʳ K' ⟶ ⋀ʳ F'`. -/
public def cokernelPullbackIso (r : ℕ) :
    (pullbackFunctor f).obj (cokernel (extPowMap AK AF ι r)) ≅ cokernel (extPowMap AK' AF' ι' r) :=
  PreservesCokernel.iso (pullbackFunctor f) _ ≪≫
    cokernel.mapIso _ _ (extPullbackIso f AK AK' l r) (extPullbackIso f AF AF' k r)
      (extPullbackIso_extHom f AK AF AK' AF' ι ι' l k hlk r)

/-- `cokernelPullbackIso` commutes with the projections onto the cokernels. -/
@[reassoc]
public theorem cokernelPullbackIso_π (r : ℕ) :
    (pullbackFunctor f).map (cokernel.π (extPowMap AK AF ι r)) ≫
        (cokernelPullbackIso f AK AF AK' AF' ι ι' l k hlk r).hom =
      (extPullbackIso f AF AF' k r).hom ≫ cokernel.π (extPowMap AK' AF' ι' r) := by
  simp [cokernelPullbackIso]

include hlk in
/-- **The pullback of the wedge-and-project map is the wedge-and-project map.** -/
public theorem cokernelPullbackIso_wedgeQuotientMap (r : ℕ) :
    (pullbackFunctor f).map (wedgeQuotientMap AK AF ι r) ≫
        (cokernelPullbackIso f AK AF AK' AF' ι ι' l k hlk (r + 1)).hom =
      Stacks.RingedSpace.comparison f (AK.exteriorPower r) F ≫
        tensorMap (extPullbackIso f AK AK' l r).hom k.hom ≫ wedgeQuotientMap AK' AF' ι' r := by
  refine pullback_tensorSheaf_hom_ext f fun U x v => ?_
  have hext := congrArg (fun φ => φ.val.app ((opensMap f).op.obj U)
    (pullbackUnit f (AK.exteriorPower r) U x))
      (extPullbackIso_extHom f AK AF AK' AF' ι ι' l k hlk r)
  have hx : (extPullbackIso f AF AF' k r).hom.val.app ((opensMap f).op.obj U)
      (pullbackUnit f _ U (((extHom AK AF ι).app r).val.app U x)) =
      ((extHom AK' AF' ι').app r).val.app _
        ((extPullbackIso f AK AK' l r).hom.val.app _ (pullbackUnit f _ U x)) :=
    (congrArg ((extPullbackIso f AF AF' k r).hom.val.app _)
      (pullbackUnit_naturality f ((extHom AK AF ι).app r) U x)).symm.trans hext
  have hπ := congrArg (fun φ => φ.val.app ((opensMap f).op.obj U)
    (pullbackUnit f _ U ((AF.exterior.mul (r : ℤ) 1).app U (((extHom AK AF ι).app r).val.app U x)
      (AF.exteriorGenerator.val.app U v))))
    (cokernelPullbackIso_π f AK AF AK' AF' ι ι' l k hlk (r + 1))
  have hR : (Stacks.RingedSpace.comparison f (AK.exteriorPower r) F).val.app ((opensMap f).op.obj U)
      (pullbackUnit f _ U ((tensorSheafUnit (Osharp := Y.sheaf) _ _).app U (x ⊗ₜ v))) =
      (tensorSheafUnit (Osharp := X.sheaf) _ _).app ((opensMap f).op.obj U)
        (pullbackUnit f _ U x ⊗ₜ pullbackUnit f _ U v) :=
    Stacks.RingedSpace.comparison_pullbackUnit_tmul f _ _ U x v
  have hM : (tensorMap (extPullbackIso f AK AK' l r).hom k.hom).val.app
        ((opensMap f).op.obj U) ((tensorSheafUnit (Osharp := X.sheaf) _ _).app
            ((opensMap f).op.obj U)
          (pullbackUnit f _ U x ⊗ₜ pullbackUnit f _ U v)) =
      (tensorSheafUnit (Osharp := X.sheaf) (AK'.exteriorPower r) F').app ((opensMap f).op.obj U)
        ((extPullbackIso f AK AK' l r).hom.val.app _ (pullbackUnit f _ U x) ⊗ₜ
          k.hom.val.app _ (pullbackUnit f _ U v)) :=
    Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit
      (J := Opens.grothendieckTopology X.carrier) (Osharp := X.sheaf)
      (f := (extPullbackIso f AK AK' l r).hom) (g := k.hom)
      (V := (opensMap f).op.obj U) _ _ _ _
  refine Eq.trans (congrArg ((cokernelPullbackIso f AK AF AK' AF' ι ι' l k hlk
      (r + 1)).hom.val.app _)
    ((pullbackUnit_naturality f (wedgeQuotientMap AK AF ι r) U _).trans
      (congrArg (pullbackUnit f _ U) (wedgeQuotientMap_unit AK AF ι r U x v)))) ?_
  refine Eq.trans (congrArg ((cokernelPullbackIso f AK AF AK' AF' ι ι' l k hlk
      (r + 1)).hom.val.app _)
    (pullbackUnit_naturality f (cokernel.π (extPowMap AK AF ι (r + 1))) U _).symm) ?_
  refine Eq.trans hπ ?_
  refine Eq.trans (congrArg ((cokernel.π (extPowMap AK' AF' ι' (r + 1))).val.app _)
    (extPullbackIso_mul f AF AF' k r 1 U _ _)) ?_
  refine Eq.trans ?_ (congrArg ((wedgeQuotientMap AK' AF' ι' r).val.app _)
    (hM.symm.trans (congrArg ((tensorMap (extPullbackIso f AK AK' l r).hom k.hom).val.app _)
      hR.symm)))
  refine Eq.trans ?_ (wedgeQuotientMap_unit AK' AF' ι' r _ _ _).symm
  exact congrArg ((cokernel.π (extPowMap AK' AF' ι' (r + 1))).val.app _)
    (congrArg₂ (fun z w => (AF'.exterior.mul (r : ℤ) 1).app ((opensMap f).op.obj U) z w) hx
      (extPullbackIso_generator f AF AF' k U v))

variable (t : F ⟶ L) (t' : F' ⟶ L') (hfg : ι ≫ t = 0) (hfg' : ι' ≫ t' = 0)
  (hS : (ShortComplex.mk ι t hfg).Exact) (hS' : (ShortComplex.mk ι' t' hfg').Exact) [ht : Epi t]
  [ht' : Epi t'] (m : (pullbackFunctor f).obj L ≅ L')
  (hkm : (pullbackFunctor f).map t ≫ m.hom = k.hom ≫ t')

include hkm in
/-- **The pullback of the comparison `⋀ʳ K ⊗ L ⟶ ⋀ʳ⁺¹ F / ⋀ʳ⁺¹ K` is the comparison**, for
compatible short exact sequences `K ⟶ F ⟶ L` and `K' ⟶ F' ⟶ L'`. -/
public theorem cokernelPullbackIso_wedgeQuotient (r : ℕ) :
    (pullbackFunctor f).map (wedgeQuotient AK AF ι t hfg hS r) ≫
        (cokernelPullbackIso f AK AF AK' AF' ι ι' l k hlk (r + 1)).hom =
      Stacks.RingedSpace.comparison f (AK.exteriorPower r) L ≫
        tensorMap (extPullbackIso f AK AK' l r).hom m.hom ≫
        wedgeQuotient AK' AF' ι' t' hfg' hS' r := by
  have hepi : Epi (C := _root_.SheafOfModules.{u} (structureRingSheaf Y))
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj
          (AK.exteriorPower r)).map t) :=
    Limits.epi_of_isColimit_cofork (tensorCokernelIsColimit AK ι t hfg hS r)
  have : Epi ((pullbackFunctor f).map
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj
          (AK.exteriorPower r)).map t)) :=
    Functor.map_epi _ _
  refine (cancel_epi ((pullbackFunctor f).map
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj
        (AK.exteriorPower r)).map t))).1 ?_
  have hP : (pullbackFunctor f).map
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj
          (AK.exteriorPower r)).map t) ≫
      (pullbackFunctor f).map (wedgeQuotient AK AF ι t hfg hS r) =
      (pullbackFunctor f).map (wedgeQuotientMap AK AF ι r) :=
    ((pullbackFunctor f).map_comp _ _).symm.trans
      (congrArg (pullbackFunctor f).map (tensorLeftMap_comp_wedgeQuotient AK AF ι t hfg hS r))
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ (cokernelPullbackIso f AK AF AK' AF' ι ι' l k hlk (r + 1)).hom) hP).trans ?_
  refine (cokernelPullbackIso_wedgeQuotientMap f AK AF AK' AF' ι ι' l k hlk r).trans ?_
  refine pullback_tensorSheaf_hom_ext f fun U x v => ?_
  have hR := Stacks.RingedSpace.comparison_pullbackUnit_tmul f (AK.exteriorPower r) F U x v
  have hR' := Stacks.RingedSpace.comparison_pullbackUnit_tmul f (AK.exteriorPower r) L U x
    (t.val.app U v)
  have hM : (tensorMap (extPullbackIso f AK AK' l r).hom k.hom).val.app
        ((opensMap f).op.obj U) ((tensorSheafUnit (Osharp := X.sheaf) _ _).app
            ((opensMap f).op.obj U)
          (pullbackUnit f _ U x ⊗ₜ pullbackUnit f _ U v)) =
      (tensorSheafUnit (Osharp := X.sheaf) (AK'.exteriorPower r) F').app ((opensMap f).op.obj U)
        ((extPullbackIso f AK AK' l r).hom.val.app _ (pullbackUnit f _ U x) ⊗ₜ
          k.hom.val.app _ (pullbackUnit f _ U v)) :=
    Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit
      (J := Opens.grothendieckTopology X.carrier) (Osharp := X.sheaf)
      (f := (extPullbackIso f AK AK' l r).hom) (g := k.hom)
      (V := (opensMap f).op.obj U) _ _ _ _
  have hM' : (tensorMap (extPullbackIso f AK AK' l r).hom m.hom).val.app
        ((opensMap f).op.obj U) ((tensorSheafUnit (Osharp := X.sheaf) _ _).app
            ((opensMap f).op.obj U)
          (pullbackUnit f _ U x ⊗ₜ pullbackUnit f _ U (t.val.app U v))) =
      (tensorSheafUnit (Osharp := X.sheaf) (AK'.exteriorPower r) L').app ((opensMap f).op.obj U)
        ((extPullbackIso f AK AK' l r).hom.val.app _ (pullbackUnit f _ U x) ⊗ₜ
          m.hom.val.app _ (pullbackUnit f _ U (t.val.app U v))) :=
    Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit
      (J := Opens.grothendieckTopology X.carrier) (Osharp := X.sheaf)
      (f := (extPullbackIso f AK AK' l r).hom) (g := m.hom)
      (V := (opensMap f).op.obj U) _ _ _ _
  have hT : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj
      (AK.exteriorPower r)).map t).val.app U ((tensorSheafUnit (Osharp := Y.sheaf) _ _).app U
      (x ⊗ₜ v)) =
      (tensorSheafUnit (Osharp := Y.sheaf) (AK.exteriorPower r) L).app U (x ⊗ₜ t.val.app U v) := by
    have mapUnit := Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit
      (J := Opens.grothendieckTopology Y.carrier) (Osharp := Y.sheaf)
      (f := 𝟙 (AK.exteriorPower r)) (g := t) (V := U) _ _ x v
    have hid : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).map
        (𝟙 (AK.exteriorPower r))).app F = 𝟙 _ :=
      NatTrans.congr_app
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).map_id _) _
    rw [hid, Category.id_comp] at mapUnit
    exact mapUnit
  have hT' : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj
      (AK'.exteriorPower r)).map t').val.app ((opensMap f).op.obj U)
      ((tensorSheafUnit (Osharp := X.sheaf) _ _).app ((opensMap f).op.obj U)
        ((extPullbackIso f AK AK' l r).hom.val.app _ (pullbackUnit f _ U x) ⊗ₜ
          k.hom.val.app _ (pullbackUnit f _ U v))) =
      (tensorSheafUnit (Osharp := X.sheaf) (AK'.exteriorPower r) L').app ((opensMap f).op.obj U)
        ((extPullbackIso f AK AK' l r).hom.val.app _ (pullbackUnit f _ U x) ⊗ₜ
          t'.val.app _ (k.hom.val.app _ (pullbackUnit f _ U v))) := by
    have mapUnit := Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit
      (J := Opens.grothendieckTopology X.carrier) (Osharp := X.sheaf)
      (f := 𝟙 (AK'.exteriorPower r)) (g := t') (V := (opensMap f).op.obj U) _ _
      ((extPullbackIso f AK AK' l r).hom.val.app _ (pullbackUnit f _ U x))
      (k.hom.val.app _ (pullbackUnit f _ U v))
    have hid : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).map
        (𝟙 (AK'.exteriorPower r))).app F' = 𝟙 _ :=
      NatTrans.congr_app
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).map_id _) _
    rw [hid, Category.id_comp] at mapUnit
    exact mapUnit
  have h2 : m.hom.val.app ((opensMap f).op.obj U) (pullbackUnit f L U (t.val.app U v)) =
      t'.val.app _ (k.hom.val.app _ (pullbackUnit f F U v)) :=
    (congrArg (m.hom.val.app _) (pullbackUnit_naturality f t U v)).symm.trans
      (congrArg (fun φ => φ.val.app ((opensMap f).op.obj U) (pullbackUnit f F U v)) hkm)
  have hW := congrArg (fun φ => φ.val.app ((opensMap f).op.obj U)
      ((tensorSheafUnit (Osharp := X.sheaf) _ _).app ((opensMap f).op.obj U)
      ((extPullbackIso f AK AK' l r).hom.val.app _ (pullbackUnit f _ U x) ⊗ₜ
        k.hom.val.app _ (pullbackUnit f _ U v))))
    (tensorLeftMap_comp_wedgeQuotient AK' AF' ι' t' hfg' hS' r)
  refine Eq.trans (congrArg (fun z => (wedgeQuotientMap AK' AF' ι' r).val.app _
    ((tensorMap (extPullbackIso f AK AK' l r).hom k.hom).val.app _ z)) hR) ?_
  refine Eq.trans (congrArg ((wedgeQuotientMap AK' AF' ι' r).val.app _) hM) ?_
  refine Eq.trans hW.symm ?_
  refine Eq.trans (congrArg ((wedgeQuotient AK' AF' ι' t' hfg' hS' r).val.app _) hT') ?_
  refine Eq.trans ?_ (congrArg (fun z => (wedgeQuotient AK' AF' ι' t' hfg' hS' r).val.app _
    ((tensorMap (extPullbackIso f AK AK' l r).hom m.hom).val.app _
      ((Stacks.RingedSpace.comparison f (AK.exteriorPower r) L).val.app _ z)))
    ((pullbackUnit_naturality f (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        Y.sheaf).obj (AK.exteriorPower r)).map t) U _).trans
      (congrArg (pullbackUnit f _ U) hT)).symm)
  refine Eq.trans ?_ (congrArg (fun z => (wedgeQuotient AK' AF' ι' t' hfg' hS' r).val.app _
    ((tensorMap (extPullbackIso f AK AK' l r).hom m.hom).val.app _ z)) hR'.symm)
  refine Eq.trans ?_ (congrArg ((wedgeQuotient AK' AF' ι' t' hfg' hS' r).val.app _) hM'.symm)
  exact congrArg (fun z => (wedgeQuotient AK' AF' ι' t' hfg' hS' r).val.app _
    ((tensorSheafUnit (Osharp := X.sheaf) (AK'.exteriorPower r) L').app ((opensMap f).op.obj U)
      ((extPullbackIso f AK AK' l r).hom.val.app _ (pullbackUnit f _ U x) ⊗ₜ z))) h2.symm

end Quotient

end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

end
