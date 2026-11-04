module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import StacksFrontier.Deformation.ToposThickening.CoefficientSquareZeroReduction
public import StacksFrontier.Deformation.ToposThickening.DerivedTensorUnit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorRightScalar
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionLinear

/-!
# The obstruction groups at `V = k` are the Ext groups, `k`-linearly

Let `O₀` be a sheaf of commutative `k`-algebras on a site, through `θ : k ⟶ O₀`. The obstruction
groups of the proof of Stacks 0DLL are the `k`-linear functors
`V ↦ Hom(K₀, (K₀ ⊗^L (O₀ ⊗_k V))⟦1⟧)` (`Deformation.ComplexLift.coefficientExtLinearFunctor`) and
`V ↦ Hom(K₀, K₀ ⊗^L (O₀ ⊗_k V))` (`Deformation.ComplexLift.coefficientHomLinearFunctor`), on which
`c ∈ k` acts through `O₀ ⊗_k (c · 𝟙_V)`.

At `V = k` the derived tensor product with `O₀ ⊗_k k ≅ O₀` is the identity, so these are
`Ext¹(K₀, K₀)` and `Ext⁰(K₀, K₀)`. This file proves that the identification is `k`-linear for
any `k`-linear structure on `O₀`-modules in which `c` acts on `M ⊗_{O₀} (O₀ ⊗_k k)` as
`M ⊗ (O₀ ⊗_k c)` (`Deformation.ComplexLift.IsCoefficientScalar`), with the induced `k`-linear
structure on the derived category. That is the structure of Stacks 0D0T (multiplication by the
global function `θ(c)`), so finiteness of the Ext groups from Stacks 0D0T gives the finiteness of
the obstruction groups at `V = k` that the fibre computation of Stacks 0DLL uses.

Nothing here is registered.

## Main results

* `Deformation.ComplexLift.derivedTensorRightMap_eq_smul`: a map of sheaves of modules acting as
  a scalar after every degreewise tensor product derives to that scalar.
* `Deformation.ComplexLift.coefficientExtUnitLinearEquiv` and
  `Deformation.ComplexLift.coefficientHomUnitLinearEquiv`: `Hom(K₀, K₀⟦1⟧)` and `Hom(K₀, K₀)` are
  `k`-linearly the obstruction groups at `V = k`.
* `Deformation.ComplexLift.finiteDimensional_coefficientExt_unit` and
  `Deformation.ComplexLift.finiteDimensional_coefficientHom_unit`: the resulting finiteness.
* `Stacks.sheafTensorLeft_map_globalSmul`: tensoring on the left commutes with multiplication by
  a section, the mirror image of `Stacks.sheafTensorRight_map_globalSmul`.
* `Deformation.ComplexLift.isCoefficientScalar_linearOfHom`: the `k`-linear structure of
  multiplication by the global functions `θ(c)` (`Stacks.TensorByBaseModule.linearOfHom`)
  satisfies the scalar condition.

## References

* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
* [Stacks Project, Tag 0D0T](https://stacks.math.columbia.edu/tag/0D0T)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
-/

/- See `StacksFrontier/Deformation/ToposThickening/CoefficientSquareZeroReduction.lean`: this
instance makes the universe unifier get stuck on sheaves of modules over a site in
`Type (u + 1)`. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

@[expose] public noncomputable section

open CategoryTheory

universe d₀ u

namespace Stacks

section Sheaf

variable {C : Type*} [Category* C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] {O : Sheaf J CommRingCat.{u}}
  [∀ U, IsMulCommutative ((commRingSheafToRingSheaf O).obj.obj U)]

/-- **Tensoring on the left commutes with multiplication by a section**: the endofunctor
`F ↦ G ⊗_O F` carries multiplication by a compatible family `f` of local sections of `O` on `F`
to multiplication by `f` on `G ⊗_O F`. This is the mirror image of
`Stacks.sheafTensorRight_map_globalSmul`; on a pure tensor both sides are `x ⊗ (a · y)`. -/
theorem sheafTensorLeft_map_globalSmul
    (f : ((commRingSheafToRingSheaf O).obj ⋙ forget RingCat).sections)
    (G F : _root_.SheafOfModules.{u} (commRingSheafToRingSheaf O)) :
    ((SheafOfModules.Tensor.sheafTensor O).obj G).map
        ((SheafOfModules.globalSectionToEnd (commRingSheafToRingSheaf O) f).app F) =
      (SheafOfModules.globalSectionToEnd (commRingSheafToRingSheaf O) f).app
        (((SheafOfModules.Tensor.sheafTensor O).obj G).obj F) := by
  have h1 : PresheafOfModules.tensorHom (O := O.obj) (𝟙 G.val)
        ((SheafOfModules.globalSectionToEnd (commRingSheafToRingSheaf O) f).app F).val =
      (presheafSectionToEnd (commRingSheafToRingSheaf O).obj f).app
        (PresheafOfModules.tensorObj (O := O.obj) G.val F.val) := by
    refine PresheafOfModules.tensorObj_hom_ext fun U x y ↦ ?_
    let r : ((ringPresheaf O.obj).obj U) := f.val U
    show x ⊗ₜ[(ringPresheaf O.obj).obj U] (r • y) = r • (x ⊗ₜ[(ringPresheaf O.obj).obj U] y)
    rw [TensorProduct.tmul_smul]
  exact (congrArg (fun ψ => (PresheafOfModules.sheafification
    (𝟙 (commRingSheafToRingSheaf O).obj)).map ψ) h1).trans
      (sheafification_map_presheafSmul (commRingSheafToRingSheaf O) f _)

end Sheaf

end Stacks

namespace Deformation.ComplexLift

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {k : Type u} [Field k] {O₀ : Sheaf J CommRingCat.{u}}
  [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]

/-- The derived tensor product with an isomorphism of sheaves of modules. -/
def derivedTensorRightMapIso
    {I₀ I₀' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)} (e : I₀ ≅ I₀') :
    derivedTensorRight.{d₀} I₀ ≅ derivedTensorRight.{d₀} I₀' where
  hom := derivedTensorRightMap.{d₀} e.hom
  inv := derivedTensorRightMap.{d₀} e.inv
  hom_inv_id := by rw [← derivedTensorRightMap_comp, e.hom_inv_id, derivedTensorRightMap_id]
  inv_hom_id := by rw [← derivedTensorRightMap_comp, e.inv_hom_id, derivedTensorRightMap_id]

section Scalar

variable [Linear k (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]

/-- **A degreewise scalar derives to the scalar.** If a map `a : I₀ ⟶ I₀` of sheaves of modules
acts on every tensor product `M ⊗_{O₀} I₀` as the scalar `c`, then the induced endomorphism of
`- ⊗^L I₀` is `c` at every object, for the `k`-linear structure of the derived category induced
by that of the modules. -/
theorem derivedTensorRightMap_eq_smul (c : k)
    {I₀ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)} (a : I₀ ⟶ I₀)
    (ha : ∀ M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀),
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} O₀).flip.map a).app M =
        c • 𝟙 _)
    (X : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))) :
    (derivedTensorRightMap.{d₀} a).app X = c • 𝟙 _ := by
  have key : derivedTensorRightMap.{d₀} a = c • 𝟙 (derivedTensorRight.{d₀} I₀) := by
    refine derivedTensorRightMap_ext _ _ fun Y => ?_
    rw [derivedTensorRightMap_app_Q, NatTrans.app_smul, NatTrans.id_app, Linear.smul_comp,
      Category.id_comp]
    have hY : (NatTrans.mapHomologicalComplex
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} O₀).flip.map a)
          (ComplexShape.up ℤ)).app Y = c • 𝟙 _ := by
      ext n : 1
      rw [NatTrans.mapHomologicalComplex_app_f, ha, HomologicalComplex.smul_f_apply,
        HomologicalComplex.id_f]
      rfl
    rw [hY, Functor.map_smul, CategoryTheory.Functor.map_id, Linear.comp_smul]
    exact congrArg (c • ·) (Category.comp_id _)
  rw [key, NatTrans.app_smul, NatTrans.id_app]

variable (θ : Stacks.TensorByBaseModule.constantRingPresheaf (C := C) k ⟶ O₀.obj)

/-- **The scalar condition on a `k`-linear structure of `O₀`-modules**: `c ∈ k` acts on every
`M ⊗_{O₀} (O₀ ⊗_k k)` as `M ⊗ (O₀ ⊗_k c)`. For the structure of Stacks 0D0T (multiplication by
the global function `θ(c)`) this is the `O₀`-bilinearity of the tensor product. -/
def IsCoefficientScalar : Prop :=
  ∀ (c : k) (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)),
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} O₀).flip.map
      ((coefficientModule θ).map (c • 𝟙 (FGModuleCat.of k k)))).app M = c • 𝟙 _

variable {θ}
variable (K₀ : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)))

/-- The identification `K₀ ⊗^L (O₀ ⊗_k k) ≅ K₀`: the derived tensor product with
`O₀ ⊗_k k ≅ O₀`, followed by `- ⊗^L O₀ ≅ 𝟭`. -/
def coefficientUnitIso :
    (derivedTensorRight.{d₀} ((coefficientModule θ).obj (FGModuleCat.of k k))).obj K₀ ≅ K₀ :=
  ((derivedTensorRightMapIso.{d₀} (coefficientModuleUnitIso θ)) ≪≫
    derivedTensorRightUnitIso.{d₀} O₀).app K₀

/-- **`Ext¹(K₀, K₀)` is `k`-linearly the obstruction group at `V = k`**, for a `k`-linear
structure on `O₀`-modules satisfying the scalar condition. -/
def coefficientExtUnitLinearEquiv (hθ : IsCoefficientScalar θ) :
    (K₀ ⟶ K₀⟦(1 : ℤ)⟧) ≃ₗ[k] (coefficientExtLinearFunctor.{d₀} θ K₀).obj (FGModuleCat.of k k) where
  toFun h := h ≫ (coefficientUnitIso K₀).inv⟦(1 : ℤ)⟧'
  invFun h := (show K₀ ⟶ ((derivedTensorRight.{d₀}
      ((coefficientModule θ).obj (FGModuleCat.of k k))).obj K₀)⟦(1 : ℤ)⟧ from h) ≫
    (coefficientUnitIso K₀).hom⟦(1 : ℤ)⟧'
  left_inv h := by
    change (h ≫ (coefficientUnitIso K₀).inv⟦(1 : ℤ)⟧') ≫ (coefficientUnitIso K₀).hom⟦(1 : ℤ)⟧' = h
    rw [Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
  right_inv h := by
    change ((show K₀ ⟶ ((derivedTensorRight.{d₀}
      ((coefficientModule θ).obj (FGModuleCat.of k k))).obj K₀)⟦(1 : ℤ)⟧ from h) ≫
        (coefficientUnitIso K₀).hom⟦(1 : ℤ)⟧') ≫ (coefficientUnitIso K₀).inv⟦(1 : ℤ)⟧' = h
    rw [Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
  map_add' h h' := Preadditive.add_comp _ _ _ h h' _
  map_smul' c h := by
    change (c • h) ≫ (coefficientUnitIso K₀).inv⟦(1 : ℤ)⟧' =
      (h ≫ (coefficientUnitIso K₀).inv⟦(1 : ℤ)⟧') ≫
        ((derivedTensorRightMap.{d₀} ((coefficientModule θ).map (c • 𝟙 _))).app K₀)⟦(1 : ℤ)⟧'
    rw [derivedTensorRightMap_eq_smul c _ (hθ c) K₀, Functor.map_smul,
      CategoryTheory.Functor.map_id, Linear.comp_smul, Category.comp_id, Linear.smul_comp]

/-- **`Ext⁰(K₀, K₀)` is `k`-linearly the group `Hom(K₀, K₀ ⊗^L (O₀ ⊗_k k))`**, for a `k`-linear
structure on `O₀`-modules satisfying the scalar condition. -/
def coefficientHomUnitLinearEquiv (hθ : IsCoefficientScalar θ) :
    (K₀ ⟶ K₀) ≃ₗ[k] (coefficientHomLinearFunctor.{d₀} θ K₀).obj (FGModuleCat.of k k) where
  toFun h := h ≫ (coefficientUnitIso K₀).inv
  invFun h := (show K₀ ⟶ (derivedTensorRight.{d₀}
      ((coefficientModule θ).obj (FGModuleCat.of k k))).obj K₀ from h) ≫
    (coefficientUnitIso K₀).hom
  left_inv h := by
    change (h ≫ (coefficientUnitIso K₀).inv) ≫ (coefficientUnitIso K₀).hom = h
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  right_inv h := by
    change ((show K₀ ⟶ (derivedTensorRight.{d₀}
      ((coefficientModule θ).obj (FGModuleCat.of k k))).obj K₀ from h) ≫
        (coefficientUnitIso K₀).hom) ≫ (coefficientUnitIso K₀).inv = h
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  map_add' h h' := Preadditive.add_comp _ _ _ h h' _
  map_smul' c h := by
    change (c • h) ≫ (coefficientUnitIso K₀).inv =
      (h ≫ (coefficientUnitIso K₀).inv) ≫
        (derivedTensorRightMap.{d₀} ((coefficientModule θ).map (c • 𝟙 _))).app K₀
    rw [derivedTensorRightMap_eq_smul c _ (hθ c) K₀, Linear.comp_smul, Category.comp_id,
      Linear.smul_comp]

/-- **The obstruction group at `V = k` is finite dimensional when `Ext¹(K₀, K₀)` is**, for a
`k`-linear structure on `O₀`-modules satisfying the scalar condition. -/
theorem finiteDimensional_coefficientExt_unit (hθ : IsCoefficientScalar θ)
    [FiniteDimensional k (K₀ ⟶ K₀⟦(1 : ℤ)⟧)] :
    FiniteDimensional k ((coefficientExtLinearFunctor.{d₀} θ K₀).obj (FGModuleCat.of k k)) :=
  (coefficientExtUnitLinearEquiv K₀ hθ).finiteDimensional

/-- **The group `Hom(K₀, K₀ ⊗^L (O₀ ⊗_k k))` is finite dimensional when `Ext⁰(K₀, K₀)` is**, for
a `k`-linear structure on `O₀`-modules satisfying the scalar condition. -/
theorem finiteDimensional_coefficientHom_unit (hθ : IsCoefficientScalar θ)
    [FiniteDimensional k (K₀ ⟶ K₀)] :
    FiniteDimensional k ((coefficientHomLinearFunctor.{d₀} θ K₀).obj (FGModuleCat.of k k)) :=
  (coefficientHomUnitLinearEquiv K₀ hθ).finiteDimensional

end Scalar

omit [HasDerivedCategory (SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf O₀))] in
/-- **The structure of multiplication by `θ(c)` satisfies the scalar condition.** For the
`k`-linear structure `Stacks.TensorByBaseModule.linearOfHom` on `O₀`-modules, in which `c` acts as
multiplication by the global function `θ(c)` (the structure of Stacks 0D0T when `θ` is the
structure map), `O₀ ⊗_k (c · 𝟙_k)` acts on every `M ⊗_{O₀} (O₀ ⊗_k k)` as `c`: the functor
`O₀ ⊗_k -` is `k`-linear, and the tensor product is `O₀`-linear in its second factor. -/
theorem isCoefficientScalar_linearOfHom
    (θ : Stacks.TensorByBaseModule.constantRingPresheaf (C := C) k ⟶ O₀.obj) :
    letI : Linear k (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) :=
      Stacks.TensorByBaseModule.linearOfHom k J O₀ θ
    IsCoefficientScalar θ := by
  let : Linear k (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) :=
    Stacks.TensorByBaseModule.linearOfHom k J O₀ θ
  intro c M
  have h1 : (coefficientModule θ).map (c • 𝟙 (FGModuleCat.of k k)) =
      Stacks.Cohomology.SiteModules.globalSmul _
        (Stacks.TensorByBaseModule.globalSectionRingHomOfHom k J O₀ θ c)
        ((coefficientModule θ).obj (FGModuleCat.of k k)) := by
    let := Stacks.TensorByBaseModule.linearOfHom k J O₀ θ
    let := Stacks.TensorByBaseModule.tensorByBaseModuleOfHom_linear k J O₀
      (SheafOfModules.unit _) θ
    show (Stacks.TensorByBaseModule.tensorByBaseModuleOfHom k J O₀ (SheafOfModules.unit _)
      θ).map (c • 𝟙 (ModuleCat.of k k)) = _
    rw [Functor.map_smul, CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  show ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} O₀).obj M).map
    ((coefficientModule θ).map (c • 𝟙 (FGModuleCat.of k k))) = _
  rw [h1]
  have : ∀ U, IsMulCommutative ((Stacks.commRingSheafToRingSheaf O₀).obj.obj U) :=
    fun U => Stacks.ringPresheaf_isMulCommutative O₀.obj U
  exact (Stacks.sheafTensorLeft_map_globalSmul _ M _).trans (Category.comp_id _).symm

end Deformation.ComplexLift

end
