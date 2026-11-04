module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.ExtensionOfScalars
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Adjunction.Whiskering

/-!
# Extension of scalars of sheaves of modules is left adjoint to restriction of scalars

For a ring homomorphism `f : R →+* S` and a site `J` on which sheaves of `S`-modules can be
sheafified, extension of scalars of sheaves of modules
`CategoryTheory.extendScalarsSheaf J R S f` (the sheafification of the sectionwise extension of
scalars, the functor of Tag 0GKB) is left adjoint to sectionwise restriction of scalars.

## Main definitions

* `CategoryTheory.extendScalarsSheafAdj`: the adjunction.

## Main results

* `CategoryTheory.extendScalarsSheafAdj_unit_app_val`: its unit, on sections, is the sectionwise
  unit followed by the sheafification map.
-/

@[expose] public noncomputable section

open CategoryTheory

universe w r s v c

namespace CategoryTheory

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C) (R : Type r) (S : Type s)
  [CommRing R] [CommRing S] [HasWeakSheafify J (ModuleCat.{max r s w} S)] (f : R →+* S)
  [J.HasSheafCompose (ModuleCat.restrictScalars.{max r s w} f)]

/-- The adjunction `extendScalars ⊣ restrictScalars` on presheaves of modules, followed by
sheafification. -/
abbrev extendScalarsPresheafSheafAdj :
    ((Functor.whiskeringRight Cᵒᵖ (ModuleCat.{max r s w} R) (ModuleCat.{max r s w} S)).obj
        (ModuleCat.extendScalars f) ⋙ presheafToSheaf J (ModuleCat.{max r s w} S)) ⊣
      (sheafToPresheaf J (ModuleCat.{max r s w} S) ⋙
        (Functor.whiskeringRight Cᵒᵖ (ModuleCat.{max r s w} S) (ModuleCat.{max r s w} R)).obj
          (ModuleCat.restrictScalars f)) :=
  (Adjunction.whiskerRight Cᵒᵖ (ModuleCat.extendRestrictScalarsAdj.{max r w} f)).comp
    (sheafificationAdjunction J (ModuleCat.{max r s w} S))

/-- **Extension of scalars of sheaves of modules is left adjoint to restriction of scalars.** -/
def extendScalarsSheafAdj :
    extendScalarsSheaf.{w} J R S f ⊣ sheafCompose J (ModuleCat.restrictScalars.{max r s w} f) :=
  (extendScalarsPresheafSheafAdj.{w} J R S f).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf J (ModuleCat.{max r s w} R)) (Functor.FullyFaithful.id _)
    (Iso.refl _) (Iso.refl _)

/-- The unit of `extendScalarsSheafAdj`, on sections: the sectionwise unit of
`extendScalars ⊣ restrictScalars`, followed by restriction of scalars of the sheafification
map. -/
theorem extendScalarsSheafAdj_unit_app_val (F : Sheaf J (ModuleCat.{max r s w} R)) :
    ((extendScalarsSheafAdj.{w} J R S f).unit.app F).hom =
      (Adjunction.whiskerRight Cᵒᵖ
          (ModuleCat.extendRestrictScalarsAdj.{max r w} f)).unit.app F.obj ≫
        Functor.whiskerRight (toSheafify J (F.obj ⋙ ModuleCat.extendScalars f))
          (ModuleCat.restrictScalars f) := by
  have := Adjunction.map_restrictFullyFaithful_unit_app
    (extendScalarsPresheafSheafAdj.{w} J R S f)
    (fullyFaithfulSheafToPresheaf J (ModuleCat.{max r s w} R)) (Functor.FullyFaithful.id _)
    (L := extendScalarsSheaf.{w} J R S f) (R := sheafCompose J (ModuleCat.restrictScalars f))
    (Iso.refl _) (Iso.refl _) F
  simp only [Functor.comp_obj, Functor.id_obj, Iso.refl_hom, NatTrans.id_app] at this
  exact this

end CategoryTheory

end
