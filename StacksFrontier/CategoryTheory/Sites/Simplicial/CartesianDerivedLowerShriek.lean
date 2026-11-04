module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedModuleSystemOfObject
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleSumFormulaSituation
public import StacksFrontier.CategoryTheory.Functor.IsIsoMapOfHypothesis
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationResolutionTerms
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianAbSheafLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianDerivedPostnikov
public import StacksFrontier.CategoryTheory.Sites.Simplicial.IntegerResolutionDerivedTensor
public import StacksFrontier.CategoryTheory.Sites.Simplicial.IntegerTensorBarTerm

/-!
# Cartesian objects of the derived category and lower shriek

In the simplicial-site situation of Stacks 09WE, write `g_n : 𝒞_n ⟶ 𝒞_total` for the inclusion
of the degree-`n` component, `g_{n!}` for extension by lower shriek and `K_n = g_n^{-1}K` for
restriction. Stacks 0D9E says that an object `K` of `D(𝒞_total)` is cartesian exactly when the
canonical map `g_{n!}K_n ⟶ g_{n!}ℤ ⊗^L_ℤ K` is an isomorphism for all `n`, and that for a sheaf
of rings `O` on `𝒞_total` all of whose transitions `f_φ^{-1}O_n ⟶ O_m` are flat, an object `K`
of `D(O)` is cartesian exactly when `g_{n!}K_n ⟶ g_{n!}O_n ⊗^L_O K` is an isomorphism for all
`n`.

Restricted to degree `m`, the map becomes, by the direct-sum formula of Stacks 09WG (resp.
Stacks 0D72), the direct sum `⨁_φ f_φ^{-1}K_n ⟶ ⨁_φ K_m` of the transitions over the simplex
maps `φ : [n] ⟶ [m]`.

## Main definitions

All names are in the namespace `CategoryTheory.SimplicialSiteSituation`.

* `componentLowerShriekDerivedBiproductIso`: the direct-sum formula of Stacks 09WG on unbounded
  derived categories of abelian sheaves, with `componentLowerShriekDerivedBiproductIso_ι`
  identifying its summand inclusions.
* `componentModuleLowerShriekDerived`: lower shriek of sheaves of modules on unbounded derived
  categories, when the transitions are flat.
* `integerProjectionSheaf`: the canonical comparison `g_{n!}(F_n) ⟶ g_{n!}ℤ ⊗_ℤ F` of abelian
  sheaves.
* `integerProjection`: the canonical projection map `g_{n!}K_n ⟶ g_{n!}ℤ ⊗^L_ℤ K` of
  Stacks 0D9E (1), the derived functor of `integerProjectionSheaf`.

## Main results

* `isCartesianDerived_iff_isIso_integerProjection`: Stacks 0D9E (1).
* `isCartesianDerivedModule_iff_isIso_moduleProjection_of_sourceIso`: Stacks 0D9E (2) for a
  map `proj` whose restriction to every degree is, under given direct-sum identifications of its
  source and target, the direct sum of the derived transitions.
* `isIso_of_forall_isIso_derivedComponent_map` and
  `isIso_of_forall_isIso_derivedComponentModuleRestriction_map`: the restrictions to the
  simplicial degrees are jointly conservative on `D(𝒞_total)` and on `D(O)`.
* `isIso_iff_forall_isIso_componentModuleRestriction`: the restrictions of sheaves of modules to
  the simplicial degrees are jointly conservative.
* `isIso_integerProjection_iff`: the projection map is invertible exactly when the sheaf-level
  comparison is invertible at every cohomology sheaf.
* `CategoryTheory.Limits.isIso_biproduct_map_iff`: a map of finite direct sums with diagonal
  components is invertible exactly when all of its components are.

## Implementation notes

The projection maps are built on sheaves. The comparison `integerProjectionSheaf` is a natural
transformation of exact functors of abelian sheaves (the target is exact because `g_{n!}ℤ` is
flat), and `integerTensorAbDerivedIso` identifies the derived functor of its target with the
derived tensor product by `g_{n!}ℤ` in degree zero. Likewise `g_{n!}O_n` is flat, so
`g_{n!}O_n ⊗^L_O -` is the derived functor of the exact functor `g_{n!}O_n ⊗_O -`. No comparison
of derived pullback with the derived tensor product (Stacks 07A4) is used.

## References

* [Stacks Project, Tag 0D9E](https://stacks.math.columbia.edu/tag/0D9E)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 0D74](https://stacks.math.columbia.edu/tag/0D74)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe v u

namespace CategoryTheory.Limits

variable {ι : Type*} {C : Type*} [Category C] [Preadditive C]

/-- A map of finite direct sums with diagonal components is invertible exactly when all of its
components are. -/
theorem isIso_biproduct_map_iff {X Y : ι → C} [HasBiproduct X] [HasBiproduct Y]
    (f : ∀ i, X i ⟶ Y i) : IsIso (biproduct.map f) ↔ ∀ i, IsIso (f i) := by
  constructor
  · intro h i
    have h1 : f i ≫ biproduct.ι Y i = biproduct.ι X i ≫ biproduct.map f := by simp
    have h2 : biproduct.π X i ≫ f i = biproduct.map f ≫ biproduct.π Y i := by simp
    refine ⟨biproduct.ι Y i ≫ inv (biproduct.map f) ≫ biproduct.π X i, ?_, ?_⟩
    · rw [← Category.assoc, h1, Category.assoc, IsIso.hom_inv_id_assoc, biproduct.ι_π_self]
    · rw [Category.assoc, Category.assoc, h2, IsIso.inv_hom_id_assoc, biproduct.ι_π_self]
  · intro h
    exact inferInstanceAs (IsIso (biproduct.mapIso fun i => asIso (f i)).hom)

end CategoryTheory.Limits

namespace CategoryTheory

/-- Two morphisms that a commutative square of isomorphisms identifies are invertible
together. -/
theorem isIso_iff_of_isoSquare {C : Type*} [Category C] {X Y Z W : C} {f : X ⟶ Y} (e₁ : X ≅ Z)
    (e₂ : Y ≅ W) {g : Z ⟶ W} (h : f ≫ e₂.hom = e₁.hom ≫ g) : IsIso f ↔ IsIso g := by
  rw [← isIso_comp_right_iff f e₂.hom, h, isIso_comp_left_iff]

end CategoryTheory

namespace CategoryTheory.SimplicialSiteSituation

attribute [local implicit_reducible] CategoryTheory.derivedInverseImage
  CategoryTheory.SimplicialSiteSituation.abelianComponent
  CategoryTheory.SimplicialSiteSituation.componentLowerShriekDerived

attribute [local instance]
  CategoryTheory.SimplicialSiteSituation.componentFunctorHasCoproductsOfShape
  CategoryTheory.SimplicialSiteSituation.abelianTransitionHasBiproduct

attribute [local instance]
  CategoryTheory.SimplicialSiteSituation.componentLowerShriekDerived_additive
  CategoryTheory.SimplicialSiteSituation.derivedComponent_additive

section SumFormula

variable (S : SimplicialSiteSituation.{u})
  [HasDerivedCategory.{v} (Sheaf S.totalTopology Ab.{u})]
  [∀ n, HasDerivedCategory.{v} (Sheaf (S.componentTopology n) Ab.{u})]

/-- **Stacks 09WG on derived categories.** The restriction to simplicial degree `m` of the
derived lower shriek from degree `n` is the direct sum, over the simplex maps `φ : [n] ⟶ [m]`,
of the derived inverse images along the transitions. -/
noncomputable def componentLowerShriekDerivedBiproductIso (n m : SimplexCategory)
    (X : DerivedCategory (Sheaf (S.componentTopology n) Ab.{u})) :
    (derivedComponent S m).obj ((S.componentLowerShriekDerived n).obj X) ≅
      ⨁ fun φ : n ⟶ m => (derivedInverseImage S φ).obj X := by
  letI : Fintype (n ⟶ m) := Fintype.ofFinite (n ⟶ m)
  exact ((derivedCompIso
      (Functor.sheafPullbackConstruction.sheafPullback (S.componentFunctor n) Ab.{u}
        (S.componentTopology n) S.totalTopology) (S.abelianComponent m) _
      (Iso.refl _)).app X).symm ≪≫
    derivedBiproductIso
      (Functor.sheafPullbackConstruction.sheafPullback (S.componentFunctor n) Ab.{u}
        (S.componentTopology n) S.totalTopology ⋙ S.abelianComponent m)
      (fun φ : n ⟶ m => abelianTransition S φ) (S.componentLowerShriekBiproductIso m n) X

/-- The `φ`-th summand inclusion of the derived sum formula is the unit of
`Lg_{n!} ⊣ g_n^{-1}` transported along the transition, followed by the derived transition. -/
theorem componentLowerShriekDerivedBiproductIso_ι {n m : SimplexCategory}
    (X : DerivedCategory (Sheaf (S.componentTopology n) Ab.{u})) (φ : n ⟶ m) :
    Limits.biproduct.ι (fun ψ : n ⟶ m => (derivedInverseImage S ψ).obj X) φ ≫
        (componentLowerShriekDerivedBiproductIso S n m X).inv =
      (derivedInverseImage S φ).map
          ((S.componentLowerShriekDerivedAdjunction n).unit.app X) ≫
        (derivedTransition S φ).app ((S.componentLowerShriekDerived n).obj X) := by
  let _ : Fintype (n ⟶ m) := Fintype.ofFinite (n ⟶ m)
  simpa only [componentLowerShriekDerivedBiproductIso, derivedBiproductIso, Iso.trans_inv,
    Iso.symm_inv, Iso.app_hom, Category.assoc, Limits.biproduct.ι_desc_assoc,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] using
    congr_app (derived_component_summand S φ) X

/-- **The restrictions to the simplicial degrees are jointly conservative on `D(𝒞_total)`.** A
morphism of `D(𝒞_total)` whose restriction to every simplicial degree is invertible is
invertible. -/
theorem isIso_of_forall_isIso_derivedComponent_map
    {K L : DerivedCategory (Sheaf S.totalTopology Ab.{u})} (f : K ⟶ L)
    (h : ∀ m : SimplexCategory, IsIso ((derivedComponent S m).map f)) : IsIso f := by
  rw [DerivedCategory.isIso_iff]
  intro i
  refine isIso_of_forall_isIso_restrictAb_map S _ fun m => ?_
  exact ((S.restrictAb m).isIso_mapDerivedCategory_map_iff f).1 (h m) i

end SumFormula

section IntegerProjection

attribute [local instance] HasDerivedCategory.standard

variable (S : SimplicialSiteSituation.{u})

/-- The object `g_{n!}ℤ ⊗^L_ℤ K` of `D(𝒞_total)`: the derived tensor product of `K` with the
lower shriek image of the constant integer sheaf of the degree-`n` component, placed in degree
zero. This is the target of the projection map of Stacks 0D9E (1). -/
noncomputable abbrev integerLowerShriekDerivedTensor (n : SimplexCategory)
    (K : DerivedCategory (Sheaf S.totalTopology Ab.{u})) :
    DerivedCategory (Sheaf S.totalTopology Ab.{u}) :=
  ((Stacks.DerivedTensor.AbelianSheaves.derivedTensor S.totalTopology).obj
    ((DerivedCategory.singleFunctor (Sheaf S.totalTopology Ab.{u}) 0).obj
      (componentIntegerSheaf S n))).obj K

/-- The canonical map `g_{n!}(F_n) ⟶ g_{n!}ℤ ⊗_ℤ F` of abelian sheaves on the total site: the
comparison of the lower shriek image of the degree-`n` restriction of `F` with the degree-`n`
term of the simplex-coefficient resolution, read through the projection formula
`barTermIsoIntegerTensor`.

It is the adjoint of `F_n ⟶ (g_n^{-1}g_{n!}ℤ) ⊗_ℤ F_n`, the map induced by the unit
`ℤ ⟶ g_n^{-1}g_{n!}ℤ`; under the projection formula this is the adjoint
`componentLowerShriekMap'` of the inclusion of `F_n` as the summand of `bar_n(F)|_n` labelled by
the identity simplex map. -/
noncomputable def integerProjectionSheaf (n : SimplexCategory) :
    S.restrictAb n ⋙ componentLowerShriekAb S n ⟶ integerTensorAb S n :=
  componentLowerShriekMap' S n ≫ (barTermIsoIntegerTensor S n).hom

/-- The comparison map is invertible at an abelian sheaf exactly when the comparison with the
simplex-coefficient resolution is. -/
theorem isIso_integerProjectionSheaf_app_iff (n : SimplexCategory)
    (F : Sheaf S.totalTopology Ab.{u}) :
    IsIso ((integerProjectionSheaf S n).app F) ↔
      IsIso ((componentLowerShriekMap' S n).app F) := by
  rw [integerProjectionSheaf, NatTrans.comp_app, isIso_comp_right_iff]

/-- **The canonical projection map of Stacks 0D9E (1)**, `g_{n!}K_n ⟶ g_{n!}ℤ ⊗^L_ℤ K`: the
derived functor of the sheaf-level comparison `integerProjectionSheaf`, read through the
identification of the derived functor of a composite of exact functors with the composite of
their derived functors, and through `integerTensorAbDerivedIso`, which identifies the derived
functor of `g_{n!}ℤ ⊗_ℤ -` with the derived tensor product by `g_{n!}ℤ` in degree zero. -/
noncomputable def integerProjection (K : DerivedCategory (Sheaf S.totalTopology Ab.{u}))
    (n : SimplexCategory) :
    (S.componentLowerShriekDerived n).obj ((derivedComponent S n).obj K) ⟶
      S.integerLowerShriekDerivedTensor n K :=
  (derivedCompIso (S.restrictAb n) (componentLowerShriekAb S n) _ (Iso.refl _)).inv.app K ≫
    (derivedNatTrans _ _ (integerProjectionSheaf S n)).app K ≫
      (S.integerTensorAbDerivedIso n).hom.app K

/-- **The projection map is invertible exactly when the sheaf-level comparison is invertible at
every cohomology sheaf.** -/
theorem isIso_integerProjection_iff (K : DerivedCategory (Sheaf S.totalTopology Ab.{u}))
    (n : SimplexCategory) :
    IsIso (S.integerProjection K n) ↔
      ∀ q : ℤ, IsIso ((componentLowerShriekMap' S n).app
        ((DerivedCategory.homologyFunctor (Sheaf S.totalTopology Ab.{u}) q).obj K)) := by
  rw [integerProjection, isIso_comp_left_iff, isIso_comp_right_iff,
    Functor.isIso_app_iff_forall_isIso_app_homology (integerProjectionSheaf S n) _
      (derivedNatTrans_app_Q _ _ (integerProjectionSheaf S n)) K]
  exact forall_congr' fun q => isIso_integerProjectionSheaf_app_iff S n _

/-- **Stacks 0D9E (1).** An object `K` of `D(𝒞_total)` is cartesian if and only if the canonical
map `g_{n!}K_n ⟶ g_{n!}ℤ ⊗^L_ℤ K` is an isomorphism for every simplicial degree `n`.

Since `K` is cartesian exactly when all of its cohomology sheaves are (Stacks 0D7L), this is the
sheaf-level statement `isCartesianAbSheaf_iff_isIso_componentLowerShriekMap` read through
`isIso_integerProjection_iff`. -/
@[stacks 0D9E "part (1)"]
theorem isCartesianDerived_iff_isIso_integerProjection
    (K : DerivedCategory (Sheaf S.totalTopology Ab.{u})) :
    S.IsCartesianDerived K ↔ ∀ n : SimplexCategory, IsIso (S.integerProjection K n) := by
  simp_rw [isCartesianDerived_iff_forall_isCartesianAbSheaf_homology',
    isCartesianAbSheaf_iff_isIso_componentLowerShriekMap, isIso_integerProjection_iff]
  exact forall_comm

end IntegerProjection

section Modules

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology RingCat.{u})

/-- **The restrictions of sheaves of modules to the simplicial components are jointly
conservative.** A morphism of sheaves of modules on the total site is invertible if and only if
its restriction to every simplicial degree is. -/
theorem isIso_iff_forall_isIso_componentModuleRestriction {M N : SheafOfModules.{u} O}
    (α : M ⟶ N) :
    IsIso α ↔ ∀ n : SimplexCategory, IsIso ((componentModuleRestriction S O n).map α) := by
  refine ⟨fun _ n => inferInstance, fun h => ?_⟩
  have hval : IsIso ((SheafOfModules.forget.{u} O ⋙
      PresheafOfModules.toPresheaf O.obj).map α) := by
    refine (NatTrans.isIso_iff_isIso_app _).2 fun U => ?_
    obtain ⟨W⟩ := U
    obtain ⟨m, V, rfl⟩ := exists_componentFunctor_obj S W
    have := h m
    exact inferInstanceAs (IsIso (((SheafOfModules.forget.{u} (componentRingSheaf S O m) ⋙
      PresheafOfModules.toPresheaf _).map ((componentModuleRestriction S O m).map α)).app
        (Opposite.op V)))
  exact isIso_of_reflects_iso α
    (SheafOfModules.forget.{u} O ⋙ PresheafOfModules.toPresheaf O.obj)

end Modules

section ModuleProjection

open AlgebraicGeometry Stacks.Cohomology.DerivedPushforward Stacks.Sheaves.RingedToposModules

attribute [local instance] HasDerivedCategory.standard
  CategoryTheory.SimplicialSiteSituation.hasWeakSheafifyComponent
  CategoryTheory.SimplicialSiteSituation.hasSheafifyTotal
  CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-- **Derived lower shriek on sheaves of modules.** When the transitions out of degree `n` are
flat, lower shriek from the degree-`n` component is exact by Stacks 0D74; this is the functor it
induces on unbounded derived categories. -/
noncomputable def componentModuleLowerShriekDerived (n : SimplexCategory)
    (hflat : ∀ (m : SimplexCategory) (φ : n ⟶ m), (S.transitionRingedToposHom O φ).IsFlat) :
    DerivedCategory (S.componentRingedTopos O n).Modules ⥤
      DerivedCategory (S.totalRingedTopos O).Modules := by
  have h := S.exactFunctor_componentModuleLowerShriek' O n hflat
  letI : PreservesFiniteLimits (S.componentModuleLowerShriek
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O) n) := h.1
  letI : PreservesFiniteColimits (S.componentModuleLowerShriek
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O) n) := h.2
  letI : (S.componentModuleLowerShriek
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O) n).Additive :=
    Functor.additive_of_preserves_binary_products _
  exact (S.componentModuleLowerShriek
    (Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O) n).mapDerivedCategory

/-- **The derived adjunction `Lg_{n!} ⊣ Lg_n^*` on sheaves of modules.** Under the hypotheses
that make `CategoryTheory.SimplicialSiteSituation.componentModuleLowerShriekDerived` exist, both
`g_{n!}` and `g_n^*` are exact, so the adjunction `g_{n!} ⊣ g_n^*` of Stacks 0D72 descends to the
unbounded derived categories, as in the degree-zero step of Stacks 0D9S. -/
noncomputable def componentModuleLowerShriekDerivedAdjunction (n : SimplexCategory)
    (hflat : ∀ (m : SimplexCategory) (φ : n ⟶ m), (S.transitionRingedToposHom O φ).IsFlat) :
    S.componentModuleLowerShriekDerived O n hflat ⊣
      S.derivedComponentModuleRestriction O n := by
  have h := S.exactFunctor_componentModuleLowerShriek' O n hflat
  letI : PreservesFiniteLimits (S.componentModuleLowerShriek
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O) n) := h.1
  letI : PreservesFiniteColimits (S.componentModuleLowerShriek
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O) n) := h.2
  letI : (S.componentModuleLowerShriek
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O) n).Additive :=
    Functor.additive_of_preserves_binary_products _
  letI : PreservesFiniteLimits (S.componentModuleRestriction
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O) n) :=
    S.componentModulesRestriction_preservesFiniteLimits O n
  letI : PreservesFiniteColimits (S.componentModuleRestriction
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O) n) :=
    S.componentModulesRestriction_preservesFiniteColimits O n
  letI : (S.componentModuleRestriction
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O) n).Additive :=
    ⟨rfl⟩
  exact Adjunction.mapDerivedCategory
    (F := S.componentModuleLowerShriek
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O) n)
    (G := S.componentModuleRestriction
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O) n)
    (S.componentModuleLowerShriekAdjunction
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O) n)

/-- **The derived restrictions to the simplicial degrees are jointly conservative on `D(O)`.** A
morphism of `D(O)` whose restriction to every simplicial degree is invertible is invertible. -/
theorem isIso_of_forall_isIso_derivedComponentModuleRestriction_map
    {K L : DerivedCategory (S.totalRingedTopos O).Modules} (f : K ⟶ L)
    (h : ∀ m : SimplexCategory, IsIso ((S.derivedComponentModuleRestriction O m).map f)) :
    IsIso f := by
  rw [DerivedCategory.isIso_iff]
  intro i
  refine (isIso_iff_forall_isIso_componentModuleRestriction S
    ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) _).2 fun m => ?_
  exact ((S.componentModulesRestriction O m).isIso_mapDerivedCategory_map_iff f).1 (h m) i

variable [∀ (m n : SimplexCategory) (φ : m ⟶ n),
  (pullbackOnHomotopy (S.transitionRingedToposHom O φ)).HasLeftDerivedFunctor
    (targetQuasiIso (S.componentRingedTopos O m))]

/-- **The general form of Stacks 0D9E (2), with the componentwise direct-sum formula taken as a
hypothesis.** Let `O` be a sheaf of rings on `𝒞_total` whose transition morphisms
`f_φ^{-1}O_n ⟶ O_m` are all flat. Then an object `K` of `D(O)` is cartesian if and only if the
canonical map `g_{n!}K_n ⟶ g_{n!}O_n ⊗^L_O K` is an isomorphism for every simplicial degree `n`.

Here the canonical map is a family `proj`, and `sourceIso`, `targetIso` identify the
restrictions to degree `m` of its source and target with `⨁_φ Lf_φ^*K_n` and `⨁_φ K_m`, as in
the componentwise direct-sum formula of Stacks 0D72 (6); `proj_restrict` says that under these
identifications the restriction of `proj n` is the direct sum of the derived transitions
`K(φ) : Lf_φ^*K_n ⟶ K_m` of Stacks 07TF (4). -/
theorem isCartesianDerivedModule_iff_isIso_moduleProjection_of_sourceIso
    (hflat : ∀ (n m : SimplexCategory) (φ : n ⟶ m), (S.transitionRingedToposHom O φ).IsFlat)
    (K : DerivedCategory (S.totalRingedTopos O).Modules)
    (proj : ∀ n : SimplexCategory,
      (S.componentModuleLowerShriekDerived O n (hflat n)).obj
          ((S.derivedComponentModuleRestriction O n).obj K) ⟶
        (((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O).tensor.obj
            ((DerivedCategory.singleFunctor
                (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O)) 0).obj
              ((S.componentModuleLowerShriek
                  (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O) n).obj
                (SheafOfModules.unit (S.componentRingSheaf
                  (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O) n))))).obj K))
    (sourceIso : ∀ n m : SimplexCategory,
      (S.derivedComponentModuleRestriction O m).obj
          ((S.componentModuleLowerShriekDerived O n (hflat n)).obj
            ((S.derivedComponentModuleRestriction O n).obj K)) ≅
        ⨁ fun φ : n ⟶ m => (S.derivedTransitionPullback O φ).obj
          ((S.derivedComponentModuleRestriction O n).obj K))
    (targetIso : ∀ n m : SimplexCategory,
      (S.derivedComponentModuleRestriction O m).obj
          ((((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O).tensor.obj
              ((DerivedCategory.singleFunctor
                  (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O)) 0).obj
                ((S.componentModuleLowerShriek
                    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O) n).obj
                  (SheafOfModules.unit (S.componentRingSheaf
                    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O) n))))).obj K)) ≅
        ⨁ fun _ : n ⟶ m => (S.derivedComponentModuleRestriction O m).obj K)
    (proj_restrict : ∀ n m : SimplexCategory,
      (S.derivedComponentModuleRestriction O m).map (proj n) ≫ (targetIso n m).hom =
        (sourceIso n m).hom ≫
          Limits.biproduct.map fun φ : n ⟶ m =>
            (S.derivedComponentModuleTransition O φ).app K) :
    S.IsCartesianDerivedModule O K ↔ ∀ n : SimplexCategory, IsIso (proj n) := by
  constructor
  · intro hK n
    refine isIso_of_forall_isIso_derivedComponentModuleRestriction_map S O _ fun m => ?_
    exact (isIso_iff_of_isoSquare _ _ (proj_restrict n m)).2
      ((Limits.isIso_biproduct_map_iff _).2 fun φ => hK φ)
  · intro h m n φ
    have hf : IsIso ((S.derivedComponentModuleRestriction O n).map (proj m)) :=
      Functor.isIso_map_of_isIso _ (proj m) (h m)
    exact (Limits.isIso_biproduct_map_iff _).1
      ((isIso_iff_of_isoSquare _ _ (proj_restrict m n)).1 hf) φ

end ModuleProjection

end CategoryTheory.SimplicialSiteSituation

end
