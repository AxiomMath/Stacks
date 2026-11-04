module

public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionGlobalPullbackValue

/-!
# The sheaf of meromorphic sections is functorial in the module

Let `F` be an algebraic space over a scheme `S`. The sheaf `𝒦_F(M)` of meromorphic sections of
a sheaf of `𝒪_F`-modules `M` is the extension of scalars of `M` along `𝒪_F ⟶ 𝒦_F` followed by
sheafification, and both of those operations are functorial in `M`. This file defines the
resulting action on morphisms,

`(M ⟶ N) → (𝒦_F(M) ⟶ 𝒦_F(N))`,

and computes its value on a meromorphic section over an étale chart that is an element of
`M ⊗_{𝒪_F} 𝒦_F`.

## Main definitions

* `AlgebraicGeometry.Space.meromorphicSectionModuleMap` is extension of scalars along
  `𝒪_F ⟶ 𝒦_F` on a morphism of modules, that is `a ⊗ m ↦ a ⊗ φ(m)`.
* `AlgebraicGeometry.Space.meromorphicSectionPresheafMap` is that morphism carried to the
  universe in which the small étale site admits sheafification of presheaves of modules.
* `AlgebraicGeometry.Space.meromorphicSectionPresheafFunctor` and
  `AlgebraicGeometry.Space.meromorphicSectionSheafFunctor` are the two constructions read as
  functors of the module.
* `AlgebraicGeometry.Space.meromorphicSectionSheafMap` is the morphism `𝒦_F(M) ⟶ 𝒦_F(N)` and
  `AlgebraicGeometry.Space.meromorphicSectionSheafMapIso` the isomorphism `𝒦_F(M) ≅ 𝒦_F(N)`
  attached to an isomorphism `M ≅ N`.

## Main results

* `AlgebraicGeometry.Space.meromorphicSectionSheafMap_toMeromorphicSectionSheaf`: the value of
  `𝒦_F(φ)` on the section of `𝒦_F(M)` over a chart that an element `t` of
  `M(V) ⊗_{𝒪_F(V)} 𝒦_F(V)` becomes is the section that `(1 ⊗ φ)(t)` becomes.
* `AlgebraicGeometry.Space.isRegularMeromorphicSection_sectionsMap_of_iso`: regularity of a
  meromorphic section is carried along the isomorphism attached to an isomorphism of modules.

## References

* [Stacks Project, Tag 0EN5](https://stacks.math.columbia.edu/tag/0EN5)
* [Stacks Project, Tag 0ENB](https://stacks.math.columbia.edu/tag/0ENB)
* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.PresheafOfModules.ChangeOfRings

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] chartMeromorphicAlgebra

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    {M N : Modules.{u, u} B S hS F hF}

/-- Extension of scalars along `𝒪_F ⟶ 𝒦_F` on a morphism of modules: the morphism
`M ⊗_{𝒪_F} 𝒦_F ⟶ N ⊗_{𝒪_F} 𝒦_F` of presheaves of `𝒦_F`-modules that `φ : M ⟶ N` induces,
namely `a ⊗ m ↦ a ⊗ φ(m)`. -/
def meromorphicSectionModuleMap (φ : M ⟶ N) :
    meromorphicSectionModule B S hS F hF M ⟶ meromorphicSectionModule B S hS F hF N :=
  (changeOfRings (toMeromorphicFunctionSheaf B S hS F hF).hom).map φ.val

/-- Extension of scalars carries `a ⊗ m` to `a ⊗ φ(m)`. -/
theorem meromorphicSectionModuleMap_tmul (φ : M ⟶ N) (V : SmallEtale B S hS F)
    (a : (meromorphicChartSheaf B S hS F hF).obj.obj (op V)) (m : M.val.obj (op V)) :
    ((meromorphicSectionModuleMap B S hS F hF φ).app (op V)).hom
        (a ⊗ₜ[chartRing B S hS F hF V] m) =
      a ⊗ₜ[chartRing B S hS F hF V] ((φ.val.app (op V)).hom m) :=
  cofHom_app_tmul (toMeromorphicFunctionSheaf B S hS F hF).hom φ.val (op V) a m

/-- Extension of scalars along `𝒪_F ⟶ 𝒦_F` on a morphism of modules, lifted to the universe in
which the small étale site admits sheafification of presheaves of modules. -/
def meromorphicSectionPresheafMap (φ : M ⟶ N) :
    meromorphicSectionPresheaf.{u, u} B S hS F hF M ⟶
      meromorphicSectionPresheaf.{u, u} B S hS F hF N :=
  PresheafOfModules.homMk
    (Functor.whiskerRight
      ((PresheafOfModules.toPresheaf _).map (meromorphicSectionModuleMap B S hS F hF φ))
      AddCommGrpCat.uliftFunctor.{u + 1})
    fun X r m => ULift.ext _ _ <|
      ((meromorphicSectionModuleMap B S hS F hF φ).app X).hom.map_smul r m.down

/-- Extension of scalars along `𝒪_F ⟶ 𝒦_F` is compatible with composition. -/
theorem meromorphicSectionModuleMap_comp {P : Modules.{u, u} B S hS F hF}
    (φ : M ⟶ N) (ψ : N ⟶ P) :
    meromorphicSectionModuleMap B S hS F hF (φ ≫ ψ) =
      meromorphicSectionModuleMap B S hS F hF φ ≫ meromorphicSectionModuleMap B S hS F hF ψ :=
  (changeOfRings (toMeromorphicFunctionSheaf B S hS F hF).hom).map_comp φ.val ψ.val

/-- Extension of scalars along `𝒪_F ⟶ 𝒦_F` carries the identity to the identity. -/
theorem meromorphicSectionModuleMap_id :
    meromorphicSectionModuleMap B S hS F hF (𝟙 M) = 𝟙 _ :=
  (changeOfRings (toMeromorphicFunctionSheaf B S hS F hF).hom).map_id M.val

/-- The presheaf of meromorphic sections as a functor of the module. -/
def meromorphicSectionPresheafFunctor :
    Modules.{u, u} B S hS F hF ⥤
      PresheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS F hF).O).obj where
  obj M := meromorphicSectionPresheaf.{u, u} B S hS F hF M
  map φ := meromorphicSectionPresheafMap B S hS F hF φ
  map_id M := by
    refine PresheafOfModules.hom_ext fun X => ?_
    refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
    apply ULift.ext
    change ((meromorphicSectionModuleMap B S hS F hF (𝟙 M)).app X).hom m.down = m.down
    rw [meromorphicSectionModuleMap_id]
    rfl
  map_comp φ ψ := by
    refine PresheafOfModules.hom_ext fun X => ?_
    refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
    apply ULift.ext
    change ((meromorphicSectionModuleMap B S hS F hF (_ ≫ _)).app X).hom m.down = _
    rw [meromorphicSectionModuleMap_comp]
    rfl

/-- The sheaf `𝒦_F(M)` of meromorphic sections as a functor of the module: extension of scalars
along `𝒪_F ⟶ 𝒦_F` followed by sheafification. -/
def meromorphicSectionSheafFunctor :
    Modules.{u, u} B S hS F hF ⥤
      SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS F hF).O) :=
  letI := moduleHasWeakSheafify.{u, u} B S hS F
  letI := moduleWEqualsLocallyBijective.{u, u} B S hS F
  meromorphicSectionPresheafFunctor B S hS F hF ⋙
    PresheafOfModules.sheafification
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS F hF).O).obj)

/-- On objects, `meromorphicSectionSheafFunctor` is the sheaf of meromorphic sections. -/
theorem meromorphicSectionSheafFunctor_obj :
    (meromorphicSectionSheafFunctor B S hS F hF).obj M =
      meromorphicSectionSheaf.{u, u} B S hS F hF M :=
  rfl

/-- The morphism `𝒦_F(M) ⟶ 𝒦_F(N)` of sheaves of `𝒦_F`-modules induced by `φ : M ⟶ N`. -/
def meromorphicSectionSheafMap (φ : M ⟶ N) :
    meromorphicSectionSheaf.{u, u} B S hS F hF M ⟶
      meromorphicSectionSheaf.{u, u} B S hS F hF N :=
  (meromorphicSectionSheafFunctor B S hS F hF).map φ

/-- The isomorphism `𝒦_F(M) ≅ 𝒦_F(N)` induced by an isomorphism `M ≅ N`. -/
def meromorphicSectionSheafMapIso (e : M ≅ N) :
    meromorphicSectionSheaf.{u, u} B S hS F hF M ≅
      meromorphicSectionSheaf.{u, u} B S hS F hF N :=
  (meromorphicSectionSheafFunctor B S hS F hF).mapIso e

/-- If a section of `𝒦_F(M)` over an étale chart `V` is the image of an element `t` of
`M(V) ⊗_{𝒪_F(V)} 𝒦_F(V)`, then its image under `𝒦_F(φ)` is the image of `(1 ⊗ φ)(t)`. -/
theorem meromorphicSectionSheafMap_toMeromorphicSectionSheaf (φ : M ⟶ N)
    (V : SmallEtale B S hS F) (t : (meromorphicSectionModule B S hS F hF M).obj (op V)) :
    ((meromorphicSectionSheafMap B S hS F hF φ).val.app (op V)).hom
        (toMeromorphicSectionSheaf B S hS F hF M V t) =
      toMeromorphicSectionSheaf B S hS F hF N V
        (((meromorphicSectionModuleMap B S hS F hF φ).app (op V)).hom t) := by
  have h := toSheafify_naturality (SmallEtale.topology B S hS F)
    (Functor.whiskerRight
      ((PresheafOfModules.toPresheaf _).map (meromorphicSectionModuleMap B S hS F hF φ))
      AddCommGrpCat.uliftFunctor.{u + 1})
  exact (ConcreteCategory.congr_hom (NatTrans.congr_app h (op V)) (ULift.up t)).symm

/-- The isomorphism of sheaves of meromorphic sections attached to an isomorphism of modules is
the morphism attached to its forward direction. -/
theorem meromorphicSectionSheafMapIso_hom (e : M ≅ N) :
    (meromorphicSectionSheafMapIso B S hS F hF e).hom =
      meromorphicSectionSheafMap B S hS F hF e.hom :=
  rfl

/-- The value over an étale chart of a meromorphic section transported along a morphism of
modules. -/
theorem eval_sectionsMap_meromorphicSectionSheafMap (φ : M ⟶ N)
    (s : MeromorphicSection.{u, u} B S hS F hF M) (V : (SmallEtale B S hS F)ᵒᵖ) :
    (SheafOfModules.sectionsMap (meromorphicSectionSheafMap B S hS F hF φ) s).eval V =
      ((meromorphicSectionSheafMap B S hS F hF φ).val.app V).hom (s.eval V) :=
  rfl

/-- The isomorphism `𝒦_F(M) ≅ 𝒦_F(N)` of an isomorphism of modules is injective over every
chart. -/
theorem injective_meromorphicSectionSheafMapIso_hom_app (e : M ≅ N)
    (V : (SmallEtale B S hS F)ᵒᵖ) :
    Function.Injective
      ((meromorphicSectionSheafMapIso B S hS F hF e).hom.val.app V).hom := by
  have hround : ∀ x : (meromorphicSectionSheaf.{u, u} B S hS F hF M).val.obj V,
      (((meromorphicSectionSheafMapIso B S hS F hF e).inv.val.app V)).hom
          ((((meromorphicSectionSheafMapIso B S hS F hF e).hom.val.app V)).hom x) = x :=
    fun x => congrArg (fun φ : meromorphicSectionSheaf.{u, u} B S hS F hF M ⟶
        meromorphicSectionSheaf.{u, u} B S hS F hF M =>
      (PresheafOfModules.Hom.app φ.val V).hom x)
      (meromorphicSectionSheafMapIso B S hS F hF e).hom_inv_id
  exact Function.LeftInverse.injective hround

/-- If `s` is a regular meromorphic section of `M` and `e : M ≅ N`, then the image of `s` under
the isomorphism `𝒦_F(M) ≅ 𝒦_F(N)` is a regular meromorphic section of `N`. -/
theorem isRegularMeromorphicSection_sectionsMap_of_iso (e : M ≅ N)
    (s : MeromorphicSection.{u, u} B S hS F hF M)
    (hs : IsRegularMeromorphicSection.{u, u} B S hS F hF M s) :
    IsRegularMeromorphicSection.{u, u} B S hS F hF N
      (SheafOfModules.sectionsMap (meromorphicSectionSheafMapIso B S hS F hF e).hom s) := by
  intro V r r' h
  refine hs V (injective_meromorphicSectionSheafMapIso_hom_app B S hS F hF e (op V) ?_)
  rwa [((meromorphicSectionSheafMapIso B S hS F hF e).hom.val.app (op V)).hom.map_smul,
    ((meromorphicSectionSheafMapIso B S hS F hF e).hom.val.app (op V)).hom.map_smul]

end AlgebraicGeometry.Space

end
