module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OverMapPentagon
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionOfModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.RestrictionOfComplexes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.RestrictionOfDerivedHoms
import StacksCore.Tactic.StacksAttribute

/-!
# Restricting a derived-category morphism along an arrow of a ringed site

Let `(C, O)` be a ringed site and `g : W ⟶ V` an arrow of `C`. Restriction of sheaves of
`O`-modules to a slice of the site is transitive on the nose: restricting to the slice over `V`
and then along `g` **is** restricting to the slice over `W`, as functors, including the
additivity and exactness instances that `CategoryTheory.Functor.mapDerivedCategory` consumes. So
the same holds for the functors induced on unbounded derived categories, up to the canonical
comparison of the derived action of a composite with the composite of the derived actions, and a
morphism `K|_V ⟶ L|_V` of `D(O|_V)` can be restricted to a morphism `K|_W ⟶ L|_W` of `D(O|_W)`.

This file records that restriction map on Hom groups, together with the comparison isomorphism
of restriction along an identity arrow which a proof of the unit presheaf law for it consumes,
and the restriction map on the sections of a complex of `O`-modules which is the source side of
the naturality in the object of the site of [Stacks, Tag 0A94].

## Main definitions

* `Stacks.SheafOfModules.overMapIdIso`: restriction of sheaves of modules along the identity
  arrow of an object of the site is the identity functor.
* `AlgebraicGeometry.RingedSite.overMapIdDerivedIso`: the same on unbounded derived categories.
* `AlgebraicGeometry.RingedSite.overMapDerivedRestrictIso`: restriction to the slice over `V`
  followed by restriction along `g`, compared with restriction to the slice over `W`, on
  unbounded derived categories.
* `AlgebraicGeometry.RingedSite.restrictHom`: the restriction map
  `(K|_V ⟶ L|_V) →+ (K|_W ⟶ L|_W)` of the rule `V ↦ Hom_{D(O|_V)}(K|_V, L|_V)`.
* `AlgebraicGeometry.RingedSite.sectionComplexRestrict`: the map of section complexes over an
  arrow of the site, formed degreewise by the restriction maps of the underlying presheaves.

## Main results

* `Stacks.SheafOfModules.overMapIdIso_hom_app_overFunctor_obj`: on a module restricted from the
  site, the comparison isomorphism of restriction along an identity arrow is the identity. This
  is the sheaf-level content of the unit presheaf law for
  `AlgebraicGeometry.RingedSite.restrictHom`.
* `AlgebraicGeometry.RingedSite.restrictHom_mapDerivedCategory_map`: the restriction of the
  restriction of a morphism of `D(O)` is its restriction.
* `AlgebraicGeometry.RingedSite.sectionComplexRestrict_f`: the degreewise description of the
  restriction map of section complexes.
* `Stacks.Homology.mapDerivedCategoryIdIso_hom_app_Q`: the value at the image of a cochain
  complex of the identification of the derived action of the identity functor with the identity
  functor. Together with
  `Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso_hom_app_Q`, which is hosted
  in `StacksFrontier/Algebra/Homology/DerivedCategory/MapDerivedCategoryComparisons.lean`, these are
  the two computations a proof of the unit presheaf law consumes.

## Implementation notes

The composite `overFunctor V ⋙ overMap g` is definitionally `overFunctor W`, which is what lets
`AlgebraicGeometry.RingedSite.overMapDerivedCategoryRestrictIso` be *stated* between the two
spellings at all. It is not what that comparison is built on: the transport along
`SheafOfModules.overFunctorMap` is inserted there on purpose, because the definitional equality,
while cheap at the level of functors, is unaffordable at the level of derived-category objects
and so a definition leaving it implicit cannot be computed with; see the implementation notes of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Slice/RestrictionOfDerivedHoms.lean`. The
definitional equality is cheap to verify at the level of functors for
*one* `overMap`, and **not** cheap for two: `overFunctor U ⋙ overMap f ⋙ overMap g` and
`overFunctor W` are definitionally equal and the check exhausts the heartbeat budget, because
identifying the ring of sections of a twice-restricted sheaf of rings with the ring of sections
of the original is expensive — the same phenomenon that
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/OverMapPentagon.lean` analyses in its
implementation notes. That is why **neither presheaf law for
`AlgebraicGeometry.RingedSite.restrictHom` is proved here**, and the obstruction is of exactly
that shape in both cases.

For the composition law `restrictHom (g ≫ f) = restrictHom g ∘ restrictHom f` the statement
itself elaborates cheaply, since it mentions only `overFunctor U`, `overFunctor V` and
`overFunctor W`; but it reduces, through the comparison
`Stacks.SheafOfModules.overMapCompIso` of restriction in one and in two steps, to the assertion
that that comparison is the identity on a module restricted from the site, and that assertion
cannot be *stated* as an equality of morphisms of sheaves of modules inside the heartbeat
budget. What can be stated, and is `rfl`, is its image under the faithful forgetful functor to
presheaves of abelian groups — `Stacks.SheafOfModules.forget₂_map_overMapCompIso_hom_app_val_app`
composed with `Stacks.SheafOfModules.overFunctor_obj_val_presheaf_map` — so the missing step is
the passage back across that faithful functor.

The unit law `restrictHom (𝟙 V) = id` needs the sheaf-level comparison only at one `overMap`,
and that one *is* available here as
`Stacks.SheafOfModules.overMapIdIso_hom_app_overFunctor_obj`; the derived-category
reduction of the law to it is also available, as
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso_hom_app_Q` and
`Stacks.Homology.mapDerivedCategoryIdIso_hom_app_Q`. What is missing is the degreewise step
between them: the assertion that `overMapIdIso` induces the identity on the *complex*
`restrictComplex X P V` cannot be stated either, because identifying
`((overMap (𝟙 V)).mapHomologicalComplex _).obj (restrictComplex X P V)` with
`restrictComplex X P V` forces the object-level check under the binder of the degree, degree by
degree, instead of the one functor-level check that `overMapDerivedRestrictIso` gets away with.

## References

* [Stacks Project, Tag 0A94](https://stacks.math.columbia.edu/tag/0A94)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w₁ w₂ v₁ v₂ u₁ u₂ w v u

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})

/-- The action of the underlying presheaf of the restriction of a sheaf of modules to a slice of
the site is the action of the underlying presheaf of the module on the source of the arrow. -/
theorem overFunctor_obj_val_presheaf_map (U : C) (M : SheafOfModules.{w} R)
    {A A' : (Over U)ᵒᵖ} (m : A ⟶ A') :
    ((SheafOfModules.overFunctor.{w} R U).obj M).val.presheaf.map m =
      M.val.presheaf.map ((Over.forget U).map m.unop).op :=
  rfl

/-- Restriction of sheaves of modules along the identity arrow of an object of the site is the
identity functor: it is the pushforward along `CategoryTheory.Over.map (𝟙 V)`, which
`CategoryTheory.Over.mapId` identifies with the identity functor of the slice category, and the
comparison of the structure maps of the sheaves of rings that the identification induces is the
identity on sections. -/
def overMapIdIso (V : C) : SheafOfModules.overMap.{w} R (𝟙 V) ≅ 𝟭 _ := by
  refine SheafOfModules.pushforwardCongr₂ _ (Over.mapId V).symm ?_ ≪≫
    SheafOfModules.pushforwardId _
  ext A : 3
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  have h : ((Functor.sheafPushforwardContinuousNatTrans (Over.mapId V).symm.hom RingCat.{w}
      (J.over V) (J.over V)).app (R.over V)).hom.app A = 𝟙 _ := by
    simp; rfl
  rw [h]
  rfl

/-- **The identity comparison of restriction, on underlying presheaves of abelian groups**: the
module's action on the arrow `CategoryTheory.Over.mapId` of the slice category, whose underlying
map is the identity. -/
theorem forget₂_map_overMapIdIso_hom_app_val_app (V : C)
    (M : SheafOfModules.{w} (R.over V)) (A : (Over V)ᵒᵖ) :
    (forget₂ (ModuleCat.{w} _) Ab).map (((overMapIdIso R V).hom.app M).val.app A) =
      M.val.presheaf.map ((Over.mapId V).inv.app A.unop).op :=
  rfl

/-- **On a module restricted from the site, the identity comparison of restriction is the
identity.** The restriction of a module to a slice has, over an arrow of that slice, the sections
of the module over the source of the arrow, and `CategoryTheory.Over.mapId` is the identity on
sources. -/
theorem overMapIdIso_hom_app_overFunctor_obj (V : C) (M : SheafOfModules.{w} R) :
    (overMapIdIso R V).hom.app ((SheafOfModules.overFunctor.{w} R V).obj M) =
      𝟙 ((SheafOfModules.overFunctor.{w} R V).obj M) := by
  ext A : 2
  refine (forget₂ (ModuleCat.{w} _) Ab).map_injective ?_
  have h : (Over.forget V).map ((Over.mapId V).inv.app A.unop) = 𝟙 A.unop.left := by simp
  have key : ((SheafOfModules.overFunctor.{w} R V).obj M).val.presheaf.map
      ((Over.mapId V).inv.app A.unop).op = 𝟙 _ := by
    rw [overFunctor_obj_val_presheaf_map, Quiver.Hom.unop_op, h]
    exact M.val.presheaf.map_id _
  rw [forget₂_map_overMapIdIso_hom_app_val_app, key]
  exact ((forget₂ (ModuleCat.{w} _) Ab).map_id _).symm

end Stacks.SheafOfModules

namespace Stacks.Homology

/-- **At the image of a cochain complex, the identification of the derived action of the identity
functor with the identity functor** is the degreewise identification on cochain complexes, read
through the comparison of that derived action with the localization. -/
theorem mapDerivedCategoryIdIso_hom_app_Q {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁]
    [HasDerivedCategory.{w₁} C₁] (P : CochainComplex C₁ ℤ) :
    mapDerivedCategoryIdIso.hom.app (DerivedCategory.Q.obj P) =
      (𝟭 C₁).mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexIdIso C₁ (ComplexShape.up ℤ)).hom.app P) := by
  simp [mapDerivedCategoryIdIso, Localization.Lifting.iso]

end Stacks.Homology

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard
  CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

variable (X : RingedSite.{u, u, u})

/-! The five instances making the derived category of modules on a slice of the site available
— a sheafification for abelian sheaves there, the identification of its weak equivalences with
the locally bijective maps, and the additivity and two-sided exactness of restriction along an
arrow — are hosted once, in
`StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.RestrictionOfDerivedHoms`, together with the
slice-restriction comparison `AlgebraicGeometry.RingedSite.overMapDerivedCategoryRestrictIso`
and the Hom-restriction map `AlgebraicGeometry.RingedSite.restrictDerivedHom`.  They used to be
declared a second time here, under the same five fully-qualified names, which is why this file
did not import the host.  Keeping both copies is not merely redundant: the type
`DerivedCategory (SheafOfModules (X.ringSheaf.over V))` is parameterized by the
`HasSheafify` instance, so a file that saw both copies would elaborate that type at whichever
one name resolution happened to pick, and a statement proved against one copy would not compose
with a statement proved against the other. -/

attribute [local instance] hasSheafifyOver wEqualsLocallyBijectiveOver additiveOverMap
  preservesFiniteLimitsOverMap preservesFiniteColimitsOverMap

/-! ### The unit presheaf law -/

/-- **The derived action of restriction along an identity arrow of the site is the identity
functor.** It is `Stacks.SheafOfModules.overMapIdIso` transported to unbounded derived
categories, followed by the identification of the derived action of the identity functor with
the identity functor. -/
def overMapIdDerivedIso (V : X.C) :
    (SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (𝟙 V)).mapDerivedCategory ≅
      𝟭 (DerivedCategory
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V))) :=
  Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
      (Stacks.SheafOfModules.overMapIdIso (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V) ≪≫
    Stacks.Homology.mapDerivedCategoryIdIso

/-- **The restriction map of the section complexes of a complex of `O`-modules along an arrow of
the site.** Over an arrow `g : W ⟶ V` it is, in each degree, the restriction map of the
underlying presheaf of abelian groups of that degree of the complex. -/
abbrev sectionComplexRestrict
    (A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {V W : X.C} (g : W ⟶ V) :
    sectionComplex X A V ⟶ sectionComplex X A W :=
  (NatTrans.mapHomologicalComplex
    (Functor.whiskerLeft (sheafToPresheaf X.J AddCommGrpCat.{u})
      ((evaluation X.Cᵒᵖ AddCommGrpCat.{u}).map g.op)) (ComplexShape.up ℤ)).app
    (underlyingComplex X A)

/-- **The degreewise description of the restriction map of section complexes**: in degree `n` it
is the restriction map of the underlying presheaf of the degree-`n` term. -/
theorem sectionComplexRestrict_f
    (A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {V W : X.C} (g : W ⟶ V) (n : ℤ) :
    (sectionComplexRestrict X A g).f n =
      ((sheafToPresheaf X.J AddCommGrpCat.{u}).obj
        ((underlyingComplex X A).X n)).map g.op :=
  rfl

end AlgebraicGeometry.RingedSite

end
