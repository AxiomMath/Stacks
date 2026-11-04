module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.SectionsRestriction

/-! # Restriction of derived sections along an isomorphism of the site

`Stacks.Cohomology.HypercohomologyEdge.derivedSectionsRestrict` compares derived sections over
two objects of a ringed site along a morphism `g : U' ⟶ U`, as
`RΓ(U, -) ⟶ RΓ(U', -) ⋙ R Res_ρ` with `ρ : O(U) ⟶ O(U')` the restriction map of the structure
ring.  When `g` is an isomorphism that comparison is invertible, and that is what this file
adds.

Two isomorphic objects of the site have isomorphic, not equal, rings of sections, so the
restriction of scalars does not disappear: the conclusion is an isomorphism of functors
`RΓ(U, -) ≅ RΓ(U', -) ⋙ R Res_ρ`, and not an equality of functors into one category.  Both
sides have `RΓ` as their head, which is what makes the comparison usable inside a longer chain
of identifications of derived sections.

## Main results

* `Stacks.Cohomology.HypercohomologyEdge.isIso_presheafOfModules_map`: the restriction map of a
  presheaf of modules along an isomorphism of the site is an isomorphism.
* `Stacks.Cohomology.HypercohomologyEdge.isIso_sectionsRestrict`: the underived restriction of
  sections along an isomorphism of the site is an isomorphism of functors.
* `Stacks.Cohomology.HypercohomologyEdge.isIso_derivedSectionsRestrict`: so is the derived
  restriction.
* `Stacks.Cohomology.HypercohomologyEdge.derivedSectionsRestrictIso`: the resulting isomorphism
  of functors, whose underlying morphism is `derivedSectionsRestrict` itself.

## Implementation notes

The invertibility is not proved by exhibiting an inverse transformation, and not by comparing
two right derived functors of isomorphic functors either: the transformation
`Stacks.Cohomology.HypercohomologyEdge.sectionsRestrictUnit` through which
`derivedSectionsRestrict` is prescribed is a composite of four factors whose intermediate
functors are spelled with `CategoryTheory.Functor.comp` bracketed two ways, so rebracketing it
as "an isomorphism followed by the unit of the second derived functor" is not available to
`CategoryTheory.Category.assoc`, which cannot match the middle object at the two spellings.

What is available is the pointwise criterion
`Stacks.Cohomology.Localization.rightDerived_of_kInjectives`: a comparison invertible at every
K-injective complex exhibits its target as a right derived functor.  Read at a K-injective
complex the four factors are *composed*, not rebracketed, and each is separately invertible —
three of them because they are coherence isomorphisms or the degreewise restriction of sections,
the fourth because the unit of a right derived functor is invertible on a K-injective complex
(`Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective`).  So
`RΓ(U', -) ⋙ R Res_ρ` is a right derived functor of sections over `U` with comparison
`sectionsRestrictUnit`, and
`CategoryTheory.Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc` turns that into the
invertibility of `derivedSectionsRestrict`.

The underived input is invertible for an elementary reason: restriction of scalars does not
change the underlying abelian group, so the component of `sectionsRestrict` at a sheaf of
modules is the restriction map of the underlying presheaf of modules, and the restriction maps of
a presheaf along `g` and along its inverse are mutually inverse functions.

## References

* [Stacks Project, Tag 0BKV](https://stacks.math.columbia.edu/tag/0BKV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.HypercohomologyEdge

universe u v wRing wModule g

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] restrictScalars_preservesFiniteLimits
  restrictScalars_preservesFiniteColimits evaluation_additive

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-! ### The underived restriction along an isomorphism -/

/-- **The restriction map of a presheaf of modules along an isomorphism of the site is an
isomorphism.**  Restriction of scalars leaves the underlying abelian group alone, so the
restriction maps along `f` and along its inverse are mutually inverse functions. -/
theorem isIso_presheafOfModules_map {R : Cᵒᵖ ⥤ RingCat.{wRing}}
    (M : PresheafOfModules.{wModule} R) {X Y : Cᵒᵖ} (f : X ⟶ Y) [IsIso f] :
    IsIso (M.map f) := by
  have key : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ X), f ≫ g = 𝟙 X → ∀ m : M.obj X,
      M.map g (M.map f m) = m := by
    intro X Y f g h m
    rw [← M.map_comp_apply, h, M.map_id]
    rfl
  rw [ConcreteCategory.isIso_iff_bijective]
  exact Function.bijective_iff_has_inverse.2
    ⟨fun m => M.map (inv f) m, key f _ (IsIso.hom_inv_id f), key _ f (IsIso.inv_hom_id f)⟩

variable (O : Sheaf J RingCat.{wRing})

/-- **Restriction of sections along an isomorphism of the site is an isomorphism of functors.**
Its component at a sheaf of modules is the restriction map of the underlying presheaf of
modules, which `isIso_presheafOfModules_map` inverts. -/
instance isIso_sectionsRestrict {U U' : C} (g : U' ⟶ U) [IsIso g] :
    IsIso (C := SheafOfModules.{wModule} O ⥤ ModuleCat.{wModule} (O.obj.obj (.op U)))
      (sectionsRestrict O g) :=
  haveI : ∀ M : SheafOfModules.{wModule} O, IsIso ((sectionsRestrict O g).app M) := fun M =>
    isIso_presheafOfModules_map ((SheafOfModules.forget O).obj M) g.op
  NatIso.isIso_of_isIso_app _

/-! ### The derived restriction along an isomorphism -/

variable [HasSheafify J AddCommGrpCat.{wModule}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}]
  [IsGrothendieckAbelian.{g} (SheafOfModules.{wModule} O)]

/-- **`RΓ(U', -) ⋙ R Res_ρ` is a right derived functor of sections over `U`**, with comparison
`sectionsRestrictUnit`, when `g : U' ⟶ U` is an isomorphism.

The criterion is pointwise on K-injective complexes, where the four factors of
`sectionsRestrictUnit` are each invertible: the degreewise restriction of sections by
`isIso_sectionsRestrict`, two coherence isomorphisms, and the unit of `RΓ(U', -)` by
`Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective`. -/
theorem isRightDerivedFunctor_sectionsRestrictUnit {U U' : C} (g : U' ⟶ U) [IsIso g] :
    (derivedSections O U' ⋙ restrictScalarsDerived O g).IsRightDerivedFunctor
      (sectionsRestrictUnit O g)
      (HomotopyCategory.quasiIso (SheafOfModules.{wModule} O) (ComplexShape.up ℤ)) := by
  have : IsIso (NatTrans.mapHomotopyCategory (sectionsRestrict O g) (ComplexShape.up ℤ)) :=
    (Stacks.Homology.mapHomotopyCategoryIso (asIso (sectionsRestrict O g))
      (ComplexShape.up ℤ)).isIso_hom
  have hcomp : ∀ {F₁ F₂ F₃ : HomotopyCategory (SheafOfModules.{wModule} O) (ComplexShape.up ℤ) ⥤
        DerivedCategory (ModuleCat.{wModule} (O.obj.obj (.op U)))}
      (α : F₁ ⟶ F₂) (β : F₂ ⟶ F₃)
      (K : HomotopyCategory (SheafOfModules.{wModule} O) (ComplexShape.up ℤ)),
      IsIso (α.app K) → IsIso (β.app K) → IsIso ((α ≫ β).app K) := by
    intro F₁ F₂ F₃ α β K h₁ h₂
    rw [NatTrans.comp_app]
    infer_instance
  refine Stacks.Cohomology.Localization.rightDerived_of_kInjectives _ _ _ (fun I hI => ?_)
  have hunit : IsIso (((homotopySections O U').totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (SheafOfModules.{wModule} O) (ComplexShape.up ℤ))).app
        ((HomotopyCategory.quotient (SheafOfModules.{wModule} O) (ComplexShape.up ℤ)).obj I)) :=
    Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective (homotopySections O U')
      (derivedSections O U') ((homotopySections O U').totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso (SheafOfModules.{wModule} O) (ComplexShape.up ℤ))) I
  rw [sectionsRestrictUnit]
  refine hcomp _ _ _ inferInstance (hcomp _ _ _ inferInstance (hcomp _ _ _ inferInstance ?_))
  rw [Functor.whiskerRight_app]
  exact Functor.map_isIso (restrictScalarsDerived O g) _

/-- **Restriction of derived sections along an isomorphism of the site is an isomorphism.**
Both `RΓ(U, -)` and `RΓ(U', -) ⋙ R Res_ρ` are right derived functors of sections over `U`, by
`isRightDerivedFunctor_sectionsRestrictUnit`, and `derivedSectionsRestrict` is the comparison
that uniqueness of right derived functors produces. -/
instance isIso_derivedSectionsRestrict {U U' : C} (g : U' ⟶ U) [IsIso g] :
    IsIso (derivedSectionsRestrict O g) :=
  (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc (derivedSections O U)
      ((homotopySections O U).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso (SheafOfModules.{wModule} O) (ComplexShape.up ℤ)))
      (HomotopyCategory.quasiIso (SheafOfModules.{wModule} O) (ComplexShape.up ℤ)) _
      (sectionsRestrictUnit O g)).mp
    (isRightDerivedFunctor_sectionsRestrictUnit O g)

/-- **Derived sections over two isomorphic objects of a ringed site agree**, after the
restriction of scalars along the induced isomorphism of the rings of sections:
`RΓ(U, -) ≅ RΓ(U', -) ⋙ R Res_ρ` for `g : U' ⟶ U` an isomorphism.

Its underlying morphism is `derivedSectionsRestrict O g`, so everything known about that
transformation — in particular `derivedSectionsRestrict_fac` and
`derivedSectionsRestrictHomology` — applies to this isomorphism unchanged. -/
def derivedSectionsRestrictIso {U U' : C} (g : U' ⟶ U) [IsIso g] :
    derivedSections O U ≅ derivedSections O U' ⋙ restrictScalarsDerived O g :=
  asIso (derivedSectionsRestrict O g)

end Stacks.Cohomology.HypercohomologyEdge

end
