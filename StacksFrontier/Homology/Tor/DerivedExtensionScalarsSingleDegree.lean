module

public import StacksFrontier.Homology.Tor.DerivedChangeOfRingsAdjunctionUnit
public import StacksFrontier.Homology.HomComplex.RHom.SingleBaseChangeUnit

/-!
# Derived extension of scalars at a module in one degree

Let `g : A → A₂` be a homomorphism of commutative rings and let `M` be an `A`-module placed in
degree `d`. Where the comparison of a total left derived model of extension of scalars with the
termwise extension is invertible at that complex — at a module with a projective resolution of
length zero, for instance, so in particular at the regular module — derived extension of scalars
carries `M[d]` to `(A₂ ⊗_A M)[d]`, and the unit of the derived change-of-rings adjunction of
[stacks 0GMT] is then the single complex on the unit `M ⟶ (A₂ ⊗_A M)|_A` of the adjunction on
modules.

That last statement is what a dévissage along the compact generator of `D(A)` needs and what the
derived adjunction does not say by itself: the unit of a derived adjunction is characterized only
on the image of the localization functor and only after composition with the comparison, so the
identification at a single complex is an argument rather than a definition.

## Main definitions

* `CochainComplex.DerivedExtensionScalars.singleRestrictDerivedIso`: restriction of scalars
  commutes with placing a module in degree `d`, read on derived categories.
* `CochainComplex.DerivedExtensionScalars.singleExtendIso`: derived extension of scalars carries
  `M[d]` to `(A₂ ⊗_A M)[d]`.

## Main results

* `CochainComplex.DerivedExtensionScalars.unit_app_single_eq`: the unit of the derived
  change-of-rings adjunction at `M[d]`, read through the two isomorphisms above, is `M[d] ⟶
  ((A₂ ⊗_A M)|_A)[d]`, the single complex on the unit of the adjunction on modules.

## Implementation notes

The proof composes three facts. The unit of the derived adjunction followed by the comparison is
the termwise unit —
`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_unit_app`, the
model-free form of the factorization of `CategoryTheory.Adjunction.derivedη`. The termwise
unit at a complex concentrated in one degree is the single complex on the unit of the adjunction
on modules — `CategoryTheory.Adjunction.mapHomologicalComplex_unit_app_single`. And the
comparison of derived restriction of scalars with termwise restriction,
`CategoryTheory.Functor.mapDerivedCategoryFactors`, cancels against its own inverse, which is
where the two single-complex comparisons `HomologicalComplex.singleMapHomologicalComplex` enter.

The statement is first proved with the module in degree `d` written as
`DerivedCategory.Q.obj ((HomologicalComplex.single _ _ d).obj M)` and then restated with
`DerivedCategory.singleFunctor`: the two are definitionally equal — `DerivedCategory.singleFunctor`
is `HomologicalComplex.single` followed by `DerivedCategory.Q` on the nose — but not syntactically
so, and `rw` needs the first spelling while a consumer wants the second.

The model of the derived category is a binder `[HasDerivedCategory.{w} (ModuleCat.{u} ·)]` for
each of the two rings, not `HasDerivedCategory.standard`.

## References

* [The Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u w

namespace CochainComplex.DerivedExtensionScalars

variable {A A₂ : Type u} [CommRing A] [CommRing A₂] (g : A →+* A₂)
  [HasDerivedCategory.{w} (ModuleCat.{u} A)] [HasDerivedCategory.{w} (ModuleCat.{u} A₂)]

/-- **Restriction of scalars commutes with placing a module in degree `d`.** Read on derived
categories: the `A₂`-module `N` in degree `d`, restricted to `A`, is `N|_A` in degree `d`. -/
def singleRestrictDerivedIso (d : ℤ) :
    ModuleCat.restrictScalars.{u} g ⋙ DerivedCategory.singleFunctor (ModuleCat.{u} A) d ≅
      DerivedCategory.singleFunctor (ModuleCat.{u} A₂) d ⋙
        (ModuleCat.restrictScalars.{u} g).mapDerivedCategory :=
  Functor.isoWhiskerRight
      (HomologicalComplex.singleMapHomologicalComplex (ModuleCat.restrictScalars.{u} g)
        (ComplexShape.up ℤ) d).symm DerivedCategory.Q ≪≫
    Functor.isoWhiskerLeft
      (HomologicalComplex.single (ModuleCat.{u} A₂) (ComplexShape.up ℤ) d)
      (ModuleCat.restrictScalars.{u} g).mapDerivedCategoryFactors.symm

/-- The two factors of `singleRestrictDerivedIso`, read at an object. -/
theorem singleRestrictDerivedIso_inv_app (d : ℤ) (N : ModuleCat.{u} A₂) :
    (singleRestrictDerivedIso g d).inv.app N =
      (ModuleCat.restrictScalars.{u} g).mapDerivedCategoryFactors.hom.app
          ((HomologicalComplex.single (ModuleCat.{u} A₂) (ComplexShape.up ℤ) d).obj N) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex (ModuleCat.restrictScalars.{u} g)
            (ComplexShape.up ℤ) d).hom.app N) :=
  rfl

variable (F : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A₂))
  (cmp : DerivedCategory.Q ⋙ F ⟶
    (ModuleCat.extendScalars.{u, u, u} g).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q)
  (d : ℤ) (M : ModuleCat.{u} A)

/-- **Derived extension of scalars of a module in one degree.** Where the comparison with the
termwise extension is invertible at `M[d]`, derived extension of scalars carries `M[d]` to
`(A₂ ⊗_A M)[d]`. -/
def singleExtendIso
    (hiso : IsIso
      (cmp.app ((HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) d).obj M))) :
    F.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} A) d).obj M) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A₂) d).obj
        ((ModuleCat.extendScalars.{u, u, u} g).obj M) :=
  letI := hiso
  asIso (cmp.app ((HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) d).obj M)) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (ModuleCat.extendScalars.{u, u, u} g) (ComplexShape.up ℤ) d).app M)

/-- The two factors of `singleExtendIso`. -/
theorem singleExtendIso_hom
    (hiso : IsIso
      (cmp.app ((HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) d).obj M))) :
    (singleExtendIso g F cmp d M hiso).hom =
      cmp.app ((HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) d).obj M) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex
            (ModuleCat.extendScalars.{u, u, u} g) (ComplexShape.up ℤ) d).hom.app M) :=
  rfl

/-- **The unit of the derived change-of-rings adjunction at a module in one degree.** Read
through `singleExtendIso` and `singleRestrictDerivedIso`, it is the single complex in degree `d`
on the unit `M ⟶ (A₂ ⊗_A M)|_A` of the adjunction on modules.

The adjunction and the factorization of its unit through the comparison are taken as arguments:
a consumer has them from `derivedExtensionScalarsAdjunction` and
`derivedExtensionScalarsAdjunction_unit_app`, and passing them avoids re-synthesizing the
left-derived-functor instance of the chosen model. -/
theorem unit_app_Q_single_eq
    (adj : F ⊣ (ModuleCat.restrictScalars.{u} g).mapDerivedCategory)
    (hB : ∀ X : CochainComplex (ModuleCat.{u} A) ℤ,
      adj.unit.app (DerivedCategory.Q.obj X) ≫
          (ModuleCat.restrictScalars.{u} g).mapDerivedCategory.map (cmp.app X) =
        DerivedCategory.Q.map
            (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} g).mapHomologicalComplex
              (ComplexShape.up ℤ)).unit.app X) ≫
          (ModuleCat.restrictScalars.{u} g).mapDerivedCategoryFactors.inv.app
            (((ModuleCat.extendScalars.{u, u, u} g).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj X)) :
    adj.unit.app (DerivedCategory.Q.obj
          ((HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) d).obj M)) ≫
        (ModuleCat.restrictScalars.{u} g).mapDerivedCategory.map
            (cmp.app ((HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) d).obj M) ≫
              DerivedCategory.Q.map
                ((HomologicalComplex.singleMapHomologicalComplex
                  (ModuleCat.extendScalars.{u, u, u} g) (ComplexShape.up ℤ) d).hom.app M)) ≫
          (singleRestrictDerivedIso g d).inv.app
            ((ModuleCat.extendScalars.{u, u, u} g).obj M) =
      DerivedCategory.Q.map
        ((HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) d).map
          ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} g).unit.app M)) := by
  have hnat := (ModuleCat.restrictScalars.{u} g).mapDerivedCategoryFactors.inv.naturality
    ((HomologicalComplex.singleMapHomologicalComplex (ModuleCat.extendScalars.{u, u, u} g)
      (ComplexShape.up ℤ) d).hom.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hnat
  rw [singleRestrictDerivedIso_inv_app, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hB, ← reassoc_of% hnat, Iso.inv_hom_id_app_assoc,
    ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  congr 1
  exact Adjunction.mapHomologicalComplex_unit_app_single
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} g) (ComplexShape.up ℤ) d M

/-- The same identification, with the module in degree `d` written through
`DerivedCategory.singleFunctor` and the comparison packaged as `singleExtendIso`. -/
theorem unit_app_single_eq
    (adj : F ⊣ (ModuleCat.restrictScalars.{u} g).mapDerivedCategory)
    (hB : ∀ X : CochainComplex (ModuleCat.{u} A) ℤ,
      adj.unit.app (DerivedCategory.Q.obj X) ≫
          (ModuleCat.restrictScalars.{u} g).mapDerivedCategory.map (cmp.app X) =
        DerivedCategory.Q.map
            (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} g).mapHomologicalComplex
              (ComplexShape.up ℤ)).unit.app X) ≫
          (ModuleCat.restrictScalars.{u} g).mapDerivedCategoryFactors.inv.app
            (((ModuleCat.extendScalars.{u, u, u} g).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj X))
    (hiso : IsIso
      (cmp.app ((HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) d).obj M))) :
    adj.unit.app ((DerivedCategory.singleFunctor (ModuleCat.{u} A) d).obj M) ≫
        (ModuleCat.restrictScalars.{u} g).mapDerivedCategory.map
            (singleExtendIso g F cmp d M hiso).hom ≫
          (singleRestrictDerivedIso g d).inv.app
            ((ModuleCat.extendScalars.{u, u, u} g).obj M) =
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) d).map
        ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} g).unit.app M) := by
  rw [singleExtendIso_hom]
  exact unit_app_Q_single_eq g F cmp d M adj hB

end CochainComplex.DerivedExtensionScalars

end
