module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Localization
public import Mathlib.AlgebraicTopology.ModelCategory.LeftHomotopy
public import Mathlib.CategoryTheory.Localization.Composition
public import Mathlib.CategoryTheory.Localization.OfQuotient
import StacksCore.Tactic.StacksAttribute

/-!
# A subcategory of complexes localizing onto the derived category

Let `C` be an abelian category and `P` a property of objects of the homotopy category
`K(C)`, closed under isomorphisms. Write `Pc` for the corresponding property of cochain
complexes, that is `Pc K ↔ P (quotient K)`. Suppose that `P` localizes onto the derived
category, in the sense that `P.ι ⋙ DerivedCategory.Qh` is a localization functor for the
quasi-isomorphisms between objects of `P`. Then so does the subcategory of complexes:
`Pc.ι ⋙ DerivedCategory.Q` is a localization functor for the quasi-isomorphisms between
complexes satisfying `Pc`.

This is the two-step factorisation `Pc.ι ⋙ Q = (Pc → P) ⋙ (P.ι ⋙ Qh)`. The second step is
the hypothesis; the first step — passing from complexes satisfying `Pc` to objects of `K(C)`
satisfying `P` — is a localization at the homotopy equivalences between them, which is the
general criterion `Functor.isLocalization_of_essSurj_of_full_of_exists_cylinders` applied to
the cylinder of a complex. The two are then composed with
`CategoryTheory.Functor.IsLocalization.comp`.

## Main results

* `CategoryTheory.ObjectProperty.complexSubcategoryQuotient_isLocalization`: the first step.
* `CategoryTheory.ObjectProperty.ι_comp_Q_isLocalization`: the conclusion.

## Main definitions

* `CategoryTheory.ObjectProperty.complexSubcategory`: the property `Pc` of complexes.
* `CategoryTheory.ObjectProperty.complexSubcategoryQuotient`: the functor from complexes
  satisfying `Pc` to objects of `K(C)` satisfying `P`.

## Implementation notes

Only closure of `P` under isomorphisms is used; `P` need not be pre-triangulated. Stability
of `Pc` under passing to the cylinder of a complex, which the cylinder criterion needs, is
automatic: the cylinder of `K` is homotopy equivalent to `K`, so the two have isomorphic
images in `K(C)`.

This is the pattern Mathlib uses for the bounded below derived category, in
`Mathlib.Algebra.Homology.HomotopyCategory.Plus` and
`Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`, generalised from
the boundedness property to an arbitrary isomorphism-closed one.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex HomotopicalAlgebra

universe w v u

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] [Abelian C]
  (P : ObjectProperty (HomotopyCategory C (ComplexShape.up ℤ)))
  [P.IsClosedUnderIsomorphisms]

/-- The property of cochain complexes corresponding to a property `P` of objects of the
homotopy category: the class of the complex satisfies `P`. -/
abbrev complexSubcategory : ObjectProperty (CochainComplex C ℤ) :=
  P.inverseImage (HomotopyCategory.quotient C (ComplexShape.up ℤ))

/-- The functor from complexes satisfying `complexSubcategory P` to objects of the homotopy
category satisfying `P`. -/
abbrev complexSubcategoryQuotient :
    (complexSubcategory P).FullSubcategory ⥤ P.FullSubcategory :=
  P.lift ((complexSubcategory P).ι ⋙ HomotopyCategory.quotient C (ComplexShape.up ℤ))
    (fun X ↦ X.2)

/-- `complexSubcategoryQuotient` is full, the homotopy quotient being full. -/
instance : (complexSubcategoryQuotient P).Full :=
  Functor.Full.of_comp_faithful_iso (P.liftCompιIso
    ((complexSubcategory P).ι ⋙ HomotopyCategory.quotient C (ComplexShape.up ℤ))
    (fun X ↦ X.2))

omit [P.IsClosedUnderIsomorphisms] in
/-- Every object of `P.FullSubcategory` is the image of a complex. -/
theorem complexSubcategoryQuotient_obj_surjective :
    Function.Surjective (complexSubcategoryQuotient P).obj := fun X ↦ by
  obtain ⟨L, hL⟩ := HomotopyCategory.quotient_obj_surjective X.obj
  refine ⟨⟨L, ?_⟩, by ext; exact hL⟩
  show P ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj L)
  rw [hL]
  exact X.property

/-- `complexSubcategoryQuotient` is essentially surjective, every object of the homotopy
category being the class of a complex. -/
instance : (complexSubcategoryQuotient P).EssSurj where
  mem_essImage X := by
    obtain ⟨L, rfl⟩ := complexSubcategoryQuotient_obj_surjective P X
    exact ⟨L, ⟨Iso.refl _⟩⟩

/-- The cylinder of a complex satisfying `complexSubcategory P` again satisfies it, since it
is homotopy equivalent to the complex. -/
theorem complexSubcategory_cylinder (K : CochainComplex C ℤ)
    (hK : complexSubcategory P K) : complexSubcategory P K.cylinder :=
  P.prop_of_iso (HomotopyCategory.isoOfHomotopyEquiv
    (cylinder.homotopyEquiv K (fun n ↦ ⟨n - 1, by simp⟩))).symm hK

/-- Complexes satisfying `complexSubcategory P` localize at their homotopy equivalences onto
the objects of `K(C)` satisfying `P`. -/
instance complexSubcategoryQuotient_isLocalization :
    (complexSubcategoryQuotient P).IsLocalization
      ((HomologicalComplex.homotopyEquivalences C (ComplexShape.up ℤ)).inverseImage
        (complexSubcategory P).ι) :=
  Functor.isLocalization_of_essSurj_of_full_of_exists_cylinders _ _
    (fun _ _ f hf ↦ by
      simpa [← isIso_iff_of_reflects_iso _ P.ι,
        ← HomotopyCategory.inverseImage_quotient_isomorphisms] using! hf)
    (by
      rintro K L f₀ f₁ hf
      obtain ⟨f₀, rfl⟩ := ObjectProperty.homMk_surjective f₀
      obtain ⟨f₁, rfl⟩ := ObjectProperty.homMk_surjective f₁
      replace hf := HomotopyCategory.homotopyOfEq f₀ f₁ (P.ι.congr_map hf)
      refine ⟨⟨⟨K.obj.cylinder, complexSubcategory_cylinder P K.obj K.property⟩,
        ObjectProperty.homMk (cylinder.ι₀ _), ObjectProperty.homMk (cylinder.ι₁ _),
        ObjectProperty.homMk (cylinder.π _), by ext; simp, by ext; simp⟩,
        Precylinder.LeftHomotopy.fullSubcategoryEquiv.symm
          { h := cylinder.desc _ _ hf
            h₀ := cylinder.ι₀_desc _ _ _
            h₁ := cylinder.ι₁_desc _ _ _ }, ?_⟩
      exact ⟨cylinder.homotopyEquiv _ (fun n ↦ ⟨n - 1, by simp⟩), rfl⟩)

variable [HasDerivedCategory.{w} C]

/-- The comparison of the two factorisations of `Pc.ι ⋙ Q`. -/
def complexSubcategoryQuotientCompIso :
    complexSubcategoryQuotient P ⋙ (P.ι ⋙ DerivedCategory.Qh) ≅
      (complexSubcategory P).ι ⋙ DerivedCategory.Q :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (ObjectProperty.liftCompιIso ..) DerivedCategory.Qh ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso C)

/-- If the objects of `K(C)` satisfying `P` localize onto the derived category, then so do
the complexes satisfying `complexSubcategory P`. -/
theorem ι_comp_Q_isLocalization
    [(P.ι ⋙ DerivedCategory.Qh).IsLocalization
      ((HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).inverseImage P.ι)] :
    (((complexSubcategory P).ι ⋙ DerivedCategory.Q)).IsLocalization
      ((HomologicalComplex.quasiIso C (ComplexShape.up ℤ)).inverseImage
        (complexSubcategory P).ι) := by
  have : (complexSubcategoryQuotient P ⋙ (P.ι ⋙ DerivedCategory.Qh)).IsLocalization
      ((HomologicalComplex.quasiIso C (ComplexShape.up ℤ)).inverseImage
        (complexSubcategory P).ι) := by
    refine Functor.IsLocalization.comp _ _
      ((HomologicalComplex.homotopyEquivalences C (ComplexShape.up ℤ)).inverseImage
        (complexSubcategory P).ι)
      ((HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).inverseImage P.ι) _ ?_ ?_ ?_
    · intro Y Z f hf
      refine ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
        (Arrow.isoOfNatIso (complexSubcategoryQuotientCompIso P) (Arrow.mk f))).2 ?_
      exact Localization.inverts DerivedCategory.Q
        (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) _ hf
    · intro Y Z f hf
      exact homotopyEquivalences_le_quasiIso _ _ _ hf
    · rintro Y Z f hf
      obtain ⟨Y, rfl⟩ := complexSubcategoryQuotient_obj_surjective P Y
      obtain ⟨Z, rfl⟩ := complexSubcategoryQuotient_obj_surjective P Z
      obtain ⟨f, rfl⟩ := (complexSubcategoryQuotient P).map_surjective f
      exact MorphismProperty.map_mem_map _ _ _
        ((HomotopyCategory.quotient_map_mem_quasiIso_iff f.hom).1 hf)
  exact Functor.IsLocalization.of_iso _ (complexSubcategoryQuotientCompIso P)

end CategoryTheory.ObjectProperty

end
