module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorCoproductRight
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorsTriangle
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleLowerShriekUnitFlat
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianDerivedLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Simplicial.DerivedSystem

/-!
# The canonical projection map `g_{n!}K_n ⟶ g_{n!}O_n ⊗^L_O K` of Stacks 0D9E (2)

Let `S` be a simplicial-site situation (Stacks 09WE), `O` a sheaf of commutative rings on its
total site and `g_n` the inclusion of the degree-`n` simplicial component. Stacks 0D9E (2)
compares an object `K` of `D(O)` with its degree-`n` restriction through the map

`g_{n!}K_n ⟶ g_{n!}O_n ⊗^L_O K`

and says that `K` is cartesian exactly when that map is invertible in every degree. This file
**constructs the map**. Until now it was carried as a hypothesis, `proj`, by
`CategoryTheory.SimplicialSiteSituation.isCartesianDerivedModule_iff_isIso_moduleProjection`.

The construction is the source's, and it runs at the level of *sheaves* of modules, which is what
makes it available: the derived tensor product by `g_{n!}O_n` placed in degree zero is the derived
functor of the exact endofunctor `g_{n!}O_n ⊗_O -` of `Mod(O)`, because `g_{n!}O_n` is a flat
sheaf of modules (`…isFlat_componentModuleLowerShriek_unit`, with no flatness hypothesis on the
structure-sheaf transitions). So the derived map is the derived functor of a map of sheaves, and
that map of sheaves is the transpose along `g_{n!} ⊣ g_n^*` of

`M_n ≅ O_n ⊗_{O_n} M_n ⟶ (g_n^*g_{n!}O_n) ⊗_{O_n} M_n ≅ g_n^*(g_{n!}O_n ⊗_O M)`,

the map induced by the unit `O_n ⟶ g_n^*g_{n!}O_n`, read through Stacks 03EL at the component
inclusion. Both ingredients are theorems of this library: the comparison is
`CategoryTheory.SimplicialSiteSituation.componentRestrictionTensorIso` and the unitor is
`Stacks.SheafOfModules.Strict.unitTensorIso`.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.componentModuleLowerShriekUnitTensor`: the endofunctor
  `g_{n!}O_n ⊗_O -` of sheaves of `O`-modules on the total site.
* `CategoryTheory.SimplicialSiteSituation.componentModuleLowerShriekUnitTensorDerivedIso`:
  **`g_{n!}O_n ⊗^L_O -` is the derived functor of `g_{n!}O_n ⊗_O -`.**
* `CategoryTheory.SimplicialSiteSituation.componentModuleProjectionSheaf`: the canonical map
  `g_{n!}(M_n) ⟶ g_{n!}O_n ⊗_O M` of sheaves of modules.
* `CategoryTheory.SimplicialSiteSituation.moduleProjection`: **the canonical projection map
  `g_{n!}K_n ⟶ g_{n!}O_n ⊗^L_O K` of Stacks 0D9E (2)**, on unbounded derived categories.

## Main results

* `CategoryTheory.SimplicialSiteSituation.exactFunctor_componentModuleLowerShriekUnitTensor`:
  tensoring with `g_{n!}O_n` is exact.

## Implementation notes

*Why the derived map is assembled through the adjunction rather than from the sheaf-level map
directly.* The abelian analogue
`CategoryTheory.SimplicialSiteSituation.integerProjection` is the derived functor of its
sheaf-level comparison, read through `CategoryTheory.derivedCompIso` for the composite
`g_n^{-1} ⋙ g_{n!}`. That route is unavailable here: `g_{n!}` on modules is exact only under the
flatness hypothesis, so its `Additive`, `PreservesFiniteLimits` and `PreservesFiniteColimits`
witnesses are local `letI`s, and instance search then fails to find them because the two spellings
of the category of modules on a component — `(S.componentRingedTopos O n).Modules` and
`SheafOfModules (S.componentRingSheaf (S.totalRingSheaf O) n)` — carry two different
`Preadditive` instances which are definitionally but not syntactically equal. The composite
`g_n^* ⋙ (g_{n!}O_n ⊗_O -)` of *this* file's route needs no such witness: restriction and
tensoring with a flat module are exact unconditionally. So the derived adjunct datum
`…componentModuleProjectionAdjunctDerived` is built first, over functors whose exactness is
instance-level, and the map itself is its transpose along the derived adjunction
`…componentModuleLowerShriekDerivedAdjunction`, which is where the flatness hypothesis enters.

*The naturality squares are assembled by hand.* The comparison of Stacks 03EL is stated between
uncurried bifunctors on `Mod(O) × Mod(O)`, so its naturality in the second variable alone has to
be extracted from its naturality at `(𝟙, f)`; that is
`…componentRestrictionTensorIso_inv_naturality_right`, where the two values of the uncurried
bifunctor on `(𝟙, f)` are reduced by `show` to their defining composites before the identity is
cancelled. The naturality of the adjunct datum is then an explicit `Eq.trans` chain rather than a
rewrite, because the goal mentions the composite `(g_{n!}O_n ⊗_O -) ⋙ g_n^*` whose middle object
is written in the other of the two spellings above and a rewrite motive is checked at `implicit`
transparency.

## References

* [Stacks Project, Tag 0D9E](https://stacks.math.columbia.edu/tag/0D9E)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 0D74](https://stacks.math.columbia.edu/tag/0D74)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.SheafOfModules.Tensor

universe u

namespace CategoryTheory.SimplicialSiteSituation

attribute [local instance] hasSheafifyTotal
  CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat hasWeakSheafifyComponent
  wEqualsLocallyBijectiveComponent HasDerivedCategory.standard

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})
  (n : SimplexCategory)

/-- The sheaf of `O`-modules `g_{n!}O_n`: the lower shriek image of the structure sheaf of the
degree-`n` simplicial component. It is the sheaf by which Stacks 0D9E (2) tensors. -/
abbrev componentModuleLowerShriekUnit : (S.totalRingedTopos O).Modules :=
  (S.componentModuleLowerShriek (S.totalRingSheaf O) n).obj
    (SheafOfModules.unit (S.componentRingSheaf (S.totalRingSheaf O) n))

/-- **The endofunctor `g_{n!}O_n ⊗_O -` of sheaves of `O`-modules on the total site.** -/
abbrev componentModuleLowerShriekUnitTensor :
    (S.totalRingedTopos O).Modules ⥤ (S.totalRingedTopos O).Modules :=
  (sheafTensor (S.totalRingedTopos O).O).obj (S.componentModuleLowerShriekUnit O n)

/-- **Tensoring with `g_{n!}O_n` is an exact endofunctor of `Mod(O)`**: the sheaf `g_{n!}O_n` is
flat by `CategoryTheory.SimplicialSiteSituation.isFlat_componentModuleLowerShriek_unit`, with no
flatness hypothesis on the structure-sheaf transitions. -/
theorem exactFunctor_componentModuleLowerShriekUnitTensor :
    exactFunctor _ _ (S.componentModuleLowerShriekUnitTensor O n) :=
  Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.exactFunctor_sheafTensorObj
    (S.totalRingedTopos O).O _ (S.isFlat_componentModuleLowerShriek_unit O n)

/-- The functor `g_{n!}O_n ⊗_O -` preserves finite limits. -/
instance preservesFiniteLimits_componentModuleLowerShriekUnitTensor :
    PreservesFiniteLimits (S.componentModuleLowerShriekUnitTensor O n) :=
  ((exactFunctor_iff _).1 (S.exactFunctor_componentModuleLowerShriekUnitTensor O n)).1

/-- The functor `g_{n!}O_n ⊗_O -` preserves finite colimits. -/
instance preservesFiniteColimits_componentModuleLowerShriekUnitTensor :
    PreservesFiniteColimits (S.componentModuleLowerShriekUnitTensor O n) :=
  ((exactFunctor_iff _).1 (S.exactFunctor_componentModuleLowerShriekUnitTensor O n)).2

/-- The functor `g_{n!}O_n ⊗_O -` is additive. -/
instance additive_componentModuleLowerShriekUnitTensor :
    (S.componentModuleLowerShriekUnitTensor O n).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- **`g_{n!}O_n ⊗^L_O -` is the derived functor of `g_{n!}O_n ⊗_O -`.** The sheaf `g_{n!}O_n` is
flat, so its degree-zero complex is K-flat and the derived tensor product with it is computed by
the ordinary tensor product applied degreewise; that is
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.flatSingleTensorIso`.

This is the module analogue of `CategoryTheory.SimplicialSiteSituation.integerTensorAbDerivedIso`.
-/
def componentModuleLowerShriekUnitTensorDerivedIso :
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O).tensor.obj
        ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O)) 0).obj
          (S.componentModuleLowerShriekUnit O n)) ≅
      (S.componentModuleLowerShriekUnitTensor O n).mapDerivedCategory :=
  Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.flatSingleTensorIso
    (S.totalRingedTopos O).O (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O) _
    (S.isFlat_componentModuleLowerShriek_unit O n)

/-- **The left unitor `O_n ⊗_{O_n} - ≅ -` of the component, as an isomorphism of functors.** The
tensor product sheaf is the tensor product of a monoidal structure on `Mod(O_n)`
(`Stacks.SheafOfModules.Strict.monoidalCategory`), so its components are the left unitor
of that structure and its naturality is the naturality of that unitor. -/
def componentModuleUnitTensorLeftUnitor :
    (sheafTensor (S.componentRingedTopos O n).O).obj
        (SheafOfModules.unit (S.componentRingSheaf (S.totalRingSheaf O) n)) ≅
      𝟭 ((S.componentRingedTopos O n).Modules) :=
  NatIso.ofComponents
    (fun L => Stacks.SheafOfModules.Strict.unitTensorIso (S.componentRingedTopos O n).O L)
    (fun {_L L'} g =>
      (congrArg (fun k => k ≫ (Stacks.SheafOfModules.Strict.unitTensorIso
            (S.componentRingedTopos O n).O L').hom)
          (Stacks.SheafOfModules.Strict.whiskerLeft_eq_sheafTensor
            (S.componentRingedTopos O n).O
            (SheafOfModules.unit (S.componentRingSheaf (S.totalRingSheaf O) n)) g).symm).trans
        (@MonoidalCategory.leftUnitor_naturality _ _
          (Stacks.SheafOfModules.Strict.monoidalCategory (S.componentRingedTopos O n).O.obj
            (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf (S.componentRingedTopos O n).O))
          _ _ g))

/-- **The map `- ⟶ (g_n^*g_{n!}O_n) ⊗_{O_n} -` of endofunctors of `Mod(O_n)`** induced by the unit
`O_n ⟶ g_n^*g_{n!}O_n` of `g_{n!} ⊣ g_n^*`, read through the left unitor. This is the map the
source transposes to obtain the projection map of Stacks 0D9E (2). -/
def componentModuleUnitTensorUnit :
    𝟭 ((S.componentRingedTopos O n).Modules) ⟶
      (sheafTensor (S.componentRingedTopos O n).O).obj
        ((S.componentModulesRestriction O n).obj (S.componentModuleLowerShriekUnit O n)) :=
  (S.componentModuleUnitTensorLeftUnitor O n).inv ≫
    (sheafTensor (S.componentRingedTopos O n).O).map
      ((S.componentModuleLowerShriekAdjunction (S.totalRingSheaf O) n).unit.app
        (SheafOfModules.unit (S.componentRingSheaf (S.totalRingSheaf O) n)))

/-- **Naturality of Stacks 03EL at the component inclusion in its second variable alone.** The
comparison `g_n^*(A ⊗_O B) ≅ g_n^*A ⊗_{O_n} g_n^*B` is stated between uncurried bifunctors, so
naturality in `B` is its naturality at the pair `(𝟙 A, f)`; the two values of the uncurried
bifunctors on that pair are their defining composites, in which the first factor is an identity.
-/
theorem componentRestrictionTensorIso_inv_naturality_right (A : (S.totalRingedTopos O).Modules)
    {M N : (S.totalRingedTopos O).Modules} (f : M ⟶ N) :
    ((sheafTensor (S.componentRingedTopos O n).O).obj
          ((S.componentModulesRestriction O n).obj A)).map
        ((S.componentModulesRestriction O n).map f) ≫
      (S.componentRestrictionTensorIso O n).inv.app (A, N) =
    (S.componentRestrictionTensorIso O n).inv.app (A, M) ≫
      (S.componentModulesRestriction O n).map
        (((sheafTensor (S.totalRingedTopos O).O).obj A).map f) := by
  have e₁ : (Functor.uncurry.obj (sheafTensor (S.componentRingedTopos O n).O)).map
        (((S.componentModulesRestriction O n).prod
          (S.componentModulesRestriction O n)).map ((𝟙 A, f) : (A, M) ⟶ (A, N))) =
      ((sheafTensor (S.componentRingedTopos O n).O).obj
        ((S.componentModulesRestriction O n).obj A)).map
          ((S.componentModulesRestriction O n).map f) := by
    change ((sheafTensor (S.componentRingedTopos O n).O).map
        ((S.componentModulesRestriction O n).map (𝟙 A))).app _ ≫ _ = _
    simp only [Functor.prod_obj, Functor.prod_map, Functor.map_id, NatTrans.id_app,
      Category.id_comp]
  have e₂ : (Functor.uncurry.obj (sheafTensor (S.totalRingedTopos O).O)).map
        ((𝟙 A, f) : (A, M) ⟶ (A, N)) =
      ((sheafTensor (S.totalRingedTopos O).O).obj A).map f := by
    change ((sheafTensor (S.totalRingedTopos O).O).map (𝟙 A)).app _ ≫ _ = _
    simp only [Functor.map_id, NatTrans.id_app, Category.id_comp]
  have h := (S.componentRestrictionTensorIso O n).inv.naturality
    (X := (A, M)) (Y := (A, N)) (𝟙 A, f)
  simp only [Functor.comp_map, e₁, e₂] at h
  exact h

/-- **The adjunct of the projection map of Stacks 0D9E (2), on sheaves of modules**: the natural
map `M_n ⟶ g_n^*(g_{n!}O_n ⊗_O M)` obtained from the unit of `g_{n!} ⊣ g_n^*` at the structure
sheaf of the component and the comparison of Stacks 03EL. -/
def componentModuleProjectionAdjunct :
    S.componentModulesRestriction O n ⟶
      S.componentModuleLowerShriekUnitTensor O n ⋙ S.componentModulesRestriction O n where
  app M := (S.componentModuleUnitTensorUnit O n).app
      ((S.componentModulesRestriction O n).obj M) ≫
    (S.componentRestrictionTensorIso O n).inv.app (S.componentModuleLowerShriekUnit O n, M)
  naturality M N f :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ (S.componentRestrictionTensorIso O n).inv.app
            (S.componentModuleLowerShriekUnit O n, N))
          ((S.componentModuleUnitTensorUnit O n).naturality
            ((S.componentModulesRestriction O n).map f))).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun k => (S.componentModuleUnitTensorUnit O n).app
                ((S.componentModulesRestriction O n).obj M) ≫ k)
              (S.componentRestrictionTensorIso_inv_naturality_right O n
                (S.componentModuleLowerShriekUnit O n) f)).trans
            (Category.assoc _ _ _).symm)))

/-- **The canonical map `g_{n!}(M_n) ⟶ g_{n!}O_n ⊗_O M` of sheaves of modules on the total
site**: the transpose along `g_{n!} ⊣ g_n^*` of
`CategoryTheory.SimplicialSiteSituation.componentModuleProjectionAdjunct`.

This is the module analogue of
`CategoryTheory.SimplicialSiteSituation.integerProjectionSheaf`, the layer the development did
not have for sheaves of modules. -/
def componentModuleProjectionSheaf :
    S.componentModulesRestriction O n ⋙ S.componentModuleLowerShriek (S.totalRingSheaf O) n ⟶
      S.componentModuleLowerShriekUnitTensor O n :=
  Functor.whiskerRight (S.componentModuleProjectionAdjunct O n)
      (S.componentModuleLowerShriek (S.totalRingSheaf O) n) ≫
    Functor.whiskerLeft (S.componentModuleLowerShriekUnitTensor O n)
      (S.componentModuleLowerShriekAdjunction (S.totalRingSheaf O) n).counit

/-- **The adjunct of the projection map of Stacks 0D9E (2), on unbounded derived categories**: the
map `K_n ⟶ (g_{n!}O_n ⊗^L_O K)_n`. It is the derived functor of
`CategoryTheory.SimplicialSiteSituation.componentModuleProjectionAdjunct`, read through the
comparison of the derived functor of a composite of exact functors with the composite of their
derived functors and through
`CategoryTheory.SimplicialSiteSituation.componentModuleLowerShriekUnitTensorDerivedIso`.

No flatness hypothesis is needed: restriction to a component is exact, and tensoring with
`g_{n!}O_n` is exact because that sheaf is flat. -/
def componentModuleProjectionAdjunctDerived
    (K : DerivedCategory ((S.totalRingedTopos O).Modules)) :
    (S.derivedComponentModuleRestriction O n).obj K ⟶
      (S.derivedComponentModuleRestriction O n).obj
        (((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O).tensor.obj
          ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O)) 0).obj
            (S.componentModuleLowerShriekUnit O n))).obj K) :=
  (derivedNatTrans (S.componentModulesRestriction O n)
      (S.componentModuleLowerShriekUnitTensor O n ⋙ S.componentModulesRestriction O n)
      (S.componentModuleProjectionAdjunct O n)).app K ≫
    (derivedCompIso (S.componentModuleLowerShriekUnitTensor O n)
      (S.componentModulesRestriction O n) _ (Iso.refl _)).hom.app K ≫
    (S.derivedComponentModuleRestriction O n).map
      ((S.componentModuleLowerShriekUnitTensorDerivedIso O n).inv.app K)

/-- **The canonical projection map of Stacks 0D9E (2)**,
`g_{n!}K_n ⟶ g_{n!}O_n ⊗^L_O K`: the transpose along the derived adjunction
`Lg_{n!} ⊣ Lg_n^*` of
`CategoryTheory.SimplicialSiteSituation.componentModuleProjectionAdjunctDerived`.

This is the map whose invertibility
`CategoryTheory.SimplicialSiteSituation.isCartesianDerivedModule_iff_isIso_moduleProjection`
is about; it is the module analogue of
`CategoryTheory.SimplicialSiteSituation.integerProjection`. The flatness of the structure-sheaf
transitions out of degree `n` enters only through the derived adjunction, which is where the
source spends it too. -/
def moduleProjection
    (hflat : ∀ (m : SimplexCategory) (φ : n ⟶ m), (S.transitionRingedToposHom O φ).IsFlat)
    (K : DerivedCategory ((S.totalRingedTopos O).Modules)) :
    (S.componentModuleLowerShriekDerived O n hflat).obj
        ((S.derivedComponentModuleRestriction O n).obj K) ⟶
      ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O).tensor.obj
        ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O)) 0).obj
          (S.componentModuleLowerShriekUnit O n))).obj K :=
  ((S.componentModuleLowerShriekDerivedAdjunction O n hflat).homEquiv _ _).symm
    (S.componentModuleProjectionAdjunctDerived O n K)

end CategoryTheory.SimplicialSiteSituation

end
