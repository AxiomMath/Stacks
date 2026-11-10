module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorByBaseModuleOfHomLinearIso
public import StacksFrontier.Deformation.Artin.FiniteDimensional.ScalarLinearFunctor
public import StacksFrontier.Deformation.ToposThickening.TrivialSquareZeroReductionBaseChange

/-!
# The square-zero extensions `O₀[O₀ ⊗_k V]` as a functor of the vector space `V`

Let `O₀` be a sheaf of commutative rings on a site whose sections are `k`-algebras, through a
morphism `θ : k ⟶ O₀` from the constant presheaf of rings. For a finite-dimensional
`k`-vector space `V` the sheaf of `O₀`-modules `O₀ ⊗_k V` is
`Stacks.TensorByBaseModule.tensorByBaseModuleOfHom` at the unit; it is additive and `k`-linear
in `V`, and it is `O₀` itself at `V = k`. A linear map `f : V ⟶ W` induces a map
`O₀[V] ⟶ O₀[W]` over `O₀` of the trivial square-zero extensions `O₀[V] := O₀ ⊕ (O₀ ⊗_k V)`,
and the reduction triangles of the two extensions are related by derived base change along it.
The obstruction groups `Hom(K₀, (K₀ ⊗^L (O₀ ⊗_k V))⟦1⟧)` of Stacks 0DIY form an additive, hence
`k`-linear, functor of `V`.

## Main definitions

* `Deformation.ComplexLift.coefficientModule`: the sheaf of `O₀`-modules `O₀ ⊗_k V`, as a
  functor of `V`.
* `Deformation.ComplexLift.coefficientRing`: the trivial square-zero extension `O₀[V]`.
* `Deformation.ComplexLift.coefficientReductionBaseChange`: the base change between the reduction
  triangles of `O₀[V]` and `O₀[W]` along a linear map `V ⟶ W`.
* `Deformation.ComplexLift.coefficientExtFunctor`,
  `Deformation.ComplexLift.coefficientExtLinearFunctor`: the groups
  `Hom(K₀, (K₀ ⊗^L (O₀ ⊗_k V))⟦1⟧)` as an additive and as a `k`-linear functor of `V`.
* `Deformation.ComplexLift.coefficientHomFunctor`,
  `Deformation.ComplexLift.coefficientHomLinearFunctor`: the groups `Hom(K₀, K₀ ⊗^L (O₀ ⊗_k V))`
  as an additive and as a `k`-linear functor of `V`.

## References

* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
* [Stacks Project, Tag 0DIY](https://stacks.math.columbia.edu/tag/0DIY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

/- `Stacks.Cohomology.SiteModules.moduleSheavesAbelian` (imported through
`Stacks.TensorByBaseModule.linearOfHom`) is stated for sheaves of modules in a `max` universe and
makes the universe unifier get stuck on `SheafOfModules.{u}` over a site in `Type (u + 1)`;
Mathlib's instance is the one the derived categories here are taken for. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe d d₀ u

namespace Deformation.ComplexLift

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {k : Type u} [Field k] {O₀ : Sheaf J CommRingCat.{u}}
  (θ : Stacks.TensorByBaseModule.constantRingPresheaf (C := C) k ⟶ O₀.obj)

/-! ### The coefficient module `O₀ ⊗_k V` -/

/-- **The sheaf of `O₀`-modules `O₀ ⊗_k V`, as a functor of the finite-dimensional vector space
`V`**: `Stacks.TensorByBaseModule.tensorByBaseModuleOfHom` at the unit, along the `k`-algebra
structure `θ` of `O₀`. -/
def coefficientModule :
    FGModuleCat.{u} k ⥤ SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀) :=
  forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k) ⋙
    Stacks.TensorByBaseModule.tensorByBaseModuleOfHom k J O₀ (SheafOfModules.unit _) θ

/-- The functor `V ↦ O₀ ⊗_k V` is additive. -/
instance coefficientModule_additive : (coefficientModule θ).Additive where
  map_add {_ _ f g} :=
    (Stacks.TensorByBaseModule.tensorByBaseModuleOfHom k J O₀ (SheafOfModules.unit _) θ).map_add
      (f := (forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).map f)
      (g := (forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).map g)

/-- **`O₀ ⊗_k k ≅ O₀`.** -/
def coefficientModuleUnitIso :
    (coefficientModule θ).obj (FGModuleCat.of k k) ≅ SheafOfModules.unit _ :=
  Stacks.TensorByBaseModule.tensorByBaseModuleOfHomUnitIso k J O₀ (SheafOfModules.unit _) θ

/-! ### The square-zero extensions `O₀[V]` -/

/-- **The trivial square-zero extension `O₀[V] = O₀ ⊕ (O₀ ⊗_k V)`.** -/
abbrev coefficientRing (V : FGModuleCat.{u} k) : Sheaf J CommRingCat.{u} :=
  sqZeroExtSheafAnySite O₀ ((coefficientModule θ).obj V)

/-- The map `O₀[V] ⟶ O₀[W]` over `O₀` induced by a linear map `f : V ⟶ W`. -/
abbrev coefficientRingMap {V W : FGModuleCat.{u} k} (f : V ⟶ W) :
    coefficientRing θ V ⟶ coefficientRing θ W :=
  sqZeroExtSheafAnySiteMap ((coefficientModule θ).map f)

/-- The map `O₀[V] ⟶ O₀[W]` induced by a linear map is a map over `O₀`. -/
theorem coefficientRingMap_comp_proj {V W : FGModuleCat.{u} k} (f : V ⟶ W) :
    coefficientRingMap θ f ≫ sqZeroExtSheafAnySiteProj ((coefficientModule θ).obj W) =
      sqZeroExtSheafAnySiteProj ((coefficientModule θ).obj V) :=
  rfl

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- `O₀[-]` carries identities to identities. -/
theorem sqZeroExtSheafAnySiteMap_id
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) :
    sqZeroExtSheafAnySiteMap (𝟙 M) = 𝟙 (sqZeroExtSheafAnySite O₀ M) := by
  ext U x
  exact PresheafOfModules.sqZeroExt_ext_anySite rfl rfl

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- `O₀[-]` carries composites to composites. -/
theorem sqZeroExtSheafAnySiteMap_comp
    {M N P : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)}
    (φ : M ⟶ N) (ψ : N ⟶ P) :
    sqZeroExtSheafAnySiteMap (φ ≫ ψ) = sqZeroExtSheafAnySiteMap φ ≫ sqZeroExtSheafAnySiteMap ψ := by
  ext U x
  exact PresheafOfModules.sqZeroExt_ext_anySite rfl rfl

/-- The identity of `V` induces the identity of `O₀[V]`. -/
theorem coefficientRingMap_id (V : FGModuleCat.{u} k) :
    coefficientRingMap θ (𝟙 V) = 𝟙 (coefficientRing θ V) := by
  rw [coefficientRingMap, CategoryTheory.Functor.map_id, sqZeroExtSheafAnySiteMap_id]

/-- The map induced by a composite of linear maps is the composite of the induced maps. -/
theorem coefficientRingMap_comp {V W X : FGModuleCat.{u} k} (f : V ⟶ W) (g : W ⟶ X) :
    coefficientRingMap θ (f ≫ g) = coefficientRingMap θ f ≫ coefficientRingMap θ g := by
  rw [coefficientRingMap, CategoryTheory.Functor.map_comp, sqZeroExtSheafAnySiteMap_comp]

/-! ### The reduction triangles and their base change -/

section Reduction

variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [∀ V : FGModuleCat.{u} k, HasDerivedCategory.{d} (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (coefficientRing θ V)))]
  [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]

/-- **The reduction triangle of `O₀[V] ⟶ O₀`**, with ideal part `- ⊗^L (O₀ ⊗_k V)`. -/
abbrev coefficientReduction (V : FGModuleCat.{u} k) :
    DerivedReduction (derivedExtensionOfScalarsData.{d, d₀}
        (sqZeroExtSheafAnySiteProj ((coefficientModule θ).obj V)))
      (derivedTensorRight.{d₀} ((coefficientModule θ).obj V)) :=
  sqZeroExtReduction.{d, d₀} ((coefficientModule θ).obj V)

/-- **The base change between the reduction triangles of `O₀[V]` and `O₀[W]`** along the map
induced by a linear map `f : V ⟶ W`: derived extension of scalars along `O₀[V] ⟶ O₀[W]`, with the
map of ideal parts `- ⊗^L (O₀ ⊗_k V) ⟶ - ⊗^L (O₀ ⊗_k W)` induced by `O₀ ⊗_k f`. -/
def coefficientReductionBaseChange {V W : FGModuleCat.{u} k} (f : V ⟶ W) :
    DerivedReductionBaseChange (coefficientReduction.{d, d₀} θ V)
      (coefficientReduction.{d, d₀} θ W) :=
  sqZeroExtReductionBaseChange.{d, d, d₀} ((coefficientModule θ).map f)

/-- The functor of `coefficientReductionBaseChange` is derived extension of scalars along
`O₀[V] ⟶ O₀[W]`. -/
theorem coefficientReductionBaseChange_functor {V W : FGModuleCat.{u} k} (f : V ⟶ W) :
    (coefficientReductionBaseChange.{d, d₀} θ f).functor =
      derivedExtensionOfScalars.{d, d} (coefficientRingMap θ f) := rfl

/-- The map of ideal parts of `coefficientReductionBaseChange` is the derived map of
`O₀ ⊗_k f`. -/
theorem coefficientReductionBaseChange_idealMap {V W : FGModuleCat.{u} k} (f : V ⟶ W) :
    (coefficientReductionBaseChange.{d, d₀} θ f).idealMap =
      derivedTensorRightMap.{d₀} ((coefficientModule θ).map f) := rfl

end Reduction

/-! ### Functoriality of the derived ideal part -/

section IdealMap

variable [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]

/-- Two transformations between the derived functors `- ⊗^L I₀ ⟶ - ⊗^L I₀'` agree if they agree
after composition with the counit of `- ⊗^L I₀'` on every cochain complex. -/
theorem derivedTensorRightMap_ext {I₀ I₀' : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf O₀)}
    (γ₁ γ₂ : derivedTensorRight.{d₀} I₀ ⟶ derivedTensorRight.{d₀} I₀')
    (h : ∀ Y : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) ℤ,
      γ₁.app (DerivedCategory.Q.obj Y) ≫ (derivedTensorRightCounit.{d₀} I₀').app Y =
        γ₂.app (DerivedCategory.Q.obj Y) ≫ (derivedTensorRightCounit.{d₀} I₀').app Y) :
    γ₁ = γ₂ :=
  Functor.leftDerived_ext (derivedTensorRight.{d₀} I₀') (derivedTensorRightCounit.{d₀} I₀')
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) _ γ₁ γ₂ (NatTrans.ext (funext h))

/-- The derived map of the identity is the identity. -/
theorem derivedTensorRightMap_id
    (I₀ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) :
    derivedTensorRightMap.{d₀} (𝟙 I₀) = 𝟙 _ := by
  refine derivedTensorRightMap_ext _ _ fun Y => ?_
  rw [derivedTensorRightMap_app_Q, NatTrans.id_app, Category.id_comp,
    CategoryTheory.Functor.map_id, NatTrans.mapHomologicalComplex_id, NatTrans.id_app,
    CategoryTheory.Functor.map_id]
  exact Category.comp_id _

/-- The derived map of a composite is the composite of the derived maps. -/
theorem derivedTensorRightMap_comp
    {I₀ I₀' I₀'' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)}
    (u₀ : I₀ ⟶ I₀') (u₀' : I₀' ⟶ I₀'') :
    derivedTensorRightMap.{d₀} (u₀ ≫ u₀') =
      derivedTensorRightMap.{d₀} u₀ ≫ derivedTensorRightMap.{d₀} u₀' := by
  refine derivedTensorRightMap_ext _ _ fun Y => ?_
  rw [derivedTensorRightMap_app_Q, NatTrans.comp_app, Category.assoc, derivedTensorRightMap_app_Q,
    derivedTensorRightMap_app_Q_assoc, ← DerivedCategory.Q.map_comp,
    CategoryTheory.Functor.map_comp, NatTrans.mapHomologicalComplex_comp, NatTrans.comp_app]

/-- The derived map of a sum is the sum of the derived maps. -/
theorem derivedTensorRightMap_add
    {I₀ I₀' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)}
    (u₀ u₀' : I₀ ⟶ I₀') :
    derivedTensorRightMap.{d₀} (u₀ + u₀') =
      derivedTensorRightMap.{d₀} u₀ + derivedTensorRightMap.{d₀} u₀' := by
  refine derivedTensorRightMap_ext _ _ fun Y => ?_
  rw [derivedTensorRightMap_app_Q, NatTrans.app_add, Preadditive.add_comp,
    derivedTensorRightMap_app_Q, derivedTensorRightMap_app_Q, ← Preadditive.comp_add,
    ← Functor.map_add]
  congr 2
  ext n : 1
  simp only [NatTrans.mapHomologicalComplex_app_f, HomologicalComplex.add_f_apply,
    Functor.map_add, NatTrans.app_add]

end IdealMap

/-! ### The obstruction groups as a functor of `V` -/

section ExtFunctor

variable [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]
  (K₀ : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)))

/-- **The obstruction groups `Hom(K₀, (K₀ ⊗^L (O₀ ⊗_k V))⟦1⟧)` as an additive functor of `V`**,
acting by postcomposition with the derived map of `O₀ ⊗_k f`. -/
def coefficientExtFunctor : FGModuleCat.{u} k ⥤ AddCommGrpCat.{d₀} where
  obj V := AddCommGrpCat.of
    (K₀ ⟶ ((derivedTensorRight.{d₀} ((coefficientModule θ).obj V)).obj K₀)⟦(1 : ℤ)⟧)
  map f := AddCommGrpCat.ofHom
    { toFun := fun x => x ≫
        ((derivedTensorRightMap.{d₀} ((coefficientModule θ).map f)).app K₀)⟦(1 : ℤ)⟧'
      map_zero' := Limits.zero_comp
      map_add' := fun x y => Preadditive.add_comp _ _ _ x y _ }
  map_id V := by
    ext x
    change x ≫ ((derivedTensorRightMap.{d₀} ((coefficientModule θ).map (𝟙 V))).app K₀)⟦(1 : ℤ)⟧' =
      x
    rw [CategoryTheory.Functor.map_id, derivedTensorRightMap_id, NatTrans.id_app,
      CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  map_comp f g := by
    ext x
    change x ≫ ((derivedTensorRightMap.{d₀} ((coefficientModule θ).map (f ≫ g))).app K₀)⟦(1 : ℤ)⟧' =
      (x ≫ ((derivedTensorRightMap.{d₀} ((coefficientModule θ).map f)).app K₀)⟦(1 : ℤ)⟧') ≫
        ((derivedTensorRightMap.{d₀} ((coefficientModule θ).map g)).app K₀)⟦(1 : ℤ)⟧'
    rw [CategoryTheory.Functor.map_comp, derivedTensorRightMap_comp, NatTrans.comp_app,
      CategoryTheory.Functor.map_comp, Category.assoc]

/-- `coefficientExtFunctor` acts on a morphism by postcomposition with the shifted derived map
of `O₀ ⊗_k f`. -/
theorem coefficientExtFunctor_map_apply {V W : FGModuleCat.{u} k} (f : V ⟶ W)
    (x : (coefficientExtFunctor.{d₀} θ K₀).obj V) :
    (coefficientExtFunctor.{d₀} θ K₀).map f x =
      (show K₀ ⟶ ((derivedTensorRight.{d₀} ((coefficientModule θ).obj V)).obj K₀)⟦(1 : ℤ)⟧ from
        x) ≫ ((derivedTensorRightMap.{d₀} ((coefficientModule θ).map f)).app K₀)⟦(1 : ℤ)⟧' :=
  rfl

/-- The functor `coefficientExtFunctor` is additive. -/
instance coefficientExtFunctor_additive : (coefficientExtFunctor.{d₀} θ K₀).Additive where
  map_add {V W f g} := by
    ext x
    have key : ((derivedTensorRightMap.{d₀} ((coefficientModule θ).map (f + g))).app K₀)⟦(1 : ℤ)⟧' =
        ((derivedTensorRightMap.{d₀} ((coefficientModule θ).map f)).app K₀)⟦(1 : ℤ)⟧' +
          ((derivedTensorRightMap.{d₀} ((coefficientModule θ).map g)).app K₀)⟦(1 : ℤ)⟧' := by
      rw [CategoryTheory.Functor.map_add, derivedTensorRightMap_add, NatTrans.app_add,
        CategoryTheory.Functor.map_add]
    exact (congrArg (fun t => (show K₀ ⟶ ((derivedTensorRight.{d₀}
      ((coefficientModule θ).obj V)).obj K₀)⟦(1 : ℤ)⟧ from x) ≫ t) key).trans
        (Preadditive.comp_add _ _ _ _ _ _)

/-- **The obstruction groups as a `k`-linear functor of `V`**: `c` acts on
`Hom(K₀, (K₀ ⊗^L (O₀ ⊗_k V))⟦1⟧)` through `O₀ ⊗_k (c · 𝟙_V)`. -/
abbrev coefficientExtLinearFunctor : FGModuleCat.{u} k ⥤ ModuleCat.{d₀} k :=
  Deformation.Artin.scalarLinearFunctor (coefficientExtFunctor.{d₀} θ K₀)

/-- **The groups `Hom(K₀, K₀ ⊗^L (O₀ ⊗_k V))` as an additive functor of `V`**, acting by
postcomposition with the derived map of `O₀ ⊗_k f`: the infinitesimal automorphisms of a lift of
`K₀` to `O₀[V]` (Stacks 0DIZ (1)). -/
def coefficientHomFunctor : FGModuleCat.{u} k ⥤ AddCommGrpCat.{d₀} where
  obj V := AddCommGrpCat.of
    (K₀ ⟶ (derivedTensorRight.{d₀} ((coefficientModule θ).obj V)).obj K₀)
  map f := AddCommGrpCat.ofHom
    { toFun := fun x => x ≫ (derivedTensorRightMap.{d₀} ((coefficientModule θ).map f)).app K₀
      map_zero' := Limits.zero_comp
      map_add' := fun x y => Preadditive.add_comp _ _ _ x y _ }
  map_id V := by
    ext x
    change x ≫ (derivedTensorRightMap.{d₀} ((coefficientModule θ).map (𝟙 V))).app K₀ = x
    rw [CategoryTheory.Functor.map_id, derivedTensorRightMap_id, NatTrans.id_app]
    exact Category.comp_id _
  map_comp f g := by
    ext x
    change x ≫ (derivedTensorRightMap.{d₀} ((coefficientModule θ).map (f ≫ g))).app K₀ =
      (x ≫ (derivedTensorRightMap.{d₀} ((coefficientModule θ).map f)).app K₀) ≫
        (derivedTensorRightMap.{d₀} ((coefficientModule θ).map g)).app K₀
    rw [CategoryTheory.Functor.map_comp, derivedTensorRightMap_comp, NatTrans.comp_app,
      Category.assoc]

/-- `coefficientHomFunctor` acts on a morphism by postcomposition with the derived map of
`O₀ ⊗_k f`. -/
theorem coefficientHomFunctor_map_apply {V W : FGModuleCat.{u} k} (f : V ⟶ W)
    (x : (coefficientHomFunctor.{d₀} θ K₀).obj V) :
    (coefficientHomFunctor.{d₀} θ K₀).map f x =
      (show K₀ ⟶ (derivedTensorRight.{d₀} ((coefficientModule θ).obj V)).obj K₀ from x) ≫
        (derivedTensorRightMap.{d₀} ((coefficientModule θ).map f)).app K₀ :=
  rfl

/-- The functor `coefficientHomFunctor` is additive. -/
instance coefficientHomFunctor_additive : (coefficientHomFunctor.{d₀} θ K₀).Additive where
  map_add {V W f g} := by
    ext x
    have key : (derivedTensorRightMap.{d₀} ((coefficientModule θ).map (f + g))).app K₀ =
        (derivedTensorRightMap.{d₀} ((coefficientModule θ).map f)).app K₀ +
          (derivedTensorRightMap.{d₀} ((coefficientModule θ).map g)).app K₀ := by
      rw [CategoryTheory.Functor.map_add, derivedTensorRightMap_add, NatTrans.app_add]
    exact (congrArg (fun t => (show K₀ ⟶ (derivedTensorRight.{d₀}
      ((coefficientModule θ).obj V)).obj K₀ from x) ≫ t) key).trans
        (Preadditive.comp_add _ _ _ _ _ _)

/-- **The groups `Hom(K₀, K₀ ⊗^L (O₀ ⊗_k V))` as a `k`-linear functor of `V`**: `c` acts through
`O₀ ⊗_k (c · 𝟙_V)`. -/
abbrev coefficientHomLinearFunctor : FGModuleCat.{u} k ⥤ ModuleCat.{d₀} k :=
  Deformation.Artin.scalarLinearFunctor (coefficientHomFunctor.{d₀} θ K₀)

end ExtFunctor

end Deformation.ComplexLift

end
