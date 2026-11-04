module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Valuative.Criterion
public import StacksFrontier.CategoryTheory.FiberedCategory.DiscreteTwoFibreProduct

/-!
# Sections of a presheaf over the spectrum of a valuation ring are determined generically

Let `B` be a big fppf site containing a scheme `S`, let `F` be a presheaf on the big fppf site of
`S` and let `p : F ⟶ 1` be its structure morphism to the final presheaf, that is to the presheaf
represented by the base. Suppose `p` satisfies the uniqueness part of the valuative criterion
(Stacks 03IX).

Two consequences are recorded here, both ingredients of the valuative criterion for a morphism of
algebraic stacks. The first is the criterion restated as an injectivity: restricting a section of
`F` over the spectrum of a valuation ring to the spectrum of its fraction field is injective. The
second applies that when `S` *is* the spectrum of a valuation ring: two 1-morphisms from the site
of `S` into the category of elements of `F` over the site which name the same element over the
generic point name the same element everywhere, since every object of the site maps to the whole
spectrum.

## Main results

* `AlgebraicGeometry.Space.valuativeGenericRestriction_injective`: restriction to the generic
  point is injective on sections over the spectrum of a valuation ring.
* `AlgebraicGeometry.Space.sectionOfBasedFunctor_eq_of_uniqueness`: two sections of the category
  of elements of `F` agreeing over the generic point agree everywhere.

## Implementation notes

The injectivity is the uniqueness criterion read backwards: a pair of sections over the spectrum
of the valuation ring with the same restriction to the generic point *is* a pair of dotted arrows
for one valuative square, so they agree. The square's lower edge is forced: the target of `p` is
a final object of the category of presheaves
(`AlgebraicGeometry.Space.isTerminal_yoneda_obj_base`), so the compatibility of the second lift
with it is automatic rather than something to check.

The second result reduces to the first through
`CategoryTheory.PresheafOfCategories.sectionHom`, which packages a compatible family of elements
of `F` as a morphism from a representable presheaf; the two morphisms it produces are the two
sections over the spectrum of the valuation ring, and the family is recovered from a morphism by
evaluating at the identity.

## References

* [Stacks Project, Tag 03IX](https://stacks.math.columbia.edu/tag/03IX)
* [Stacks Project, Tag 02XV](https://stacks.math.columbia.edu/tag/02XV)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.PresheafOfCategories Opposite

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Restriction to the generic point is injective on sections over the spectrum of a valuation
ring**, for a presheaf whose structure morphism satisfies the uniqueness part of the valuative
criterion. Two sections with the same restriction form a valuative square with two lifts, and the
criterion identifies them; the compatibility of the second lift with the lower edge of that
square is automatic because the target of the structure morphism is a final presheaf. -/
theorem valuativeGenericRestriction_injective
    (p : F ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS))))
    (hu : ValuativeCriterion.Uniqueness p)
    (R K : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (hR : B.Contains (Spec (.of R))) (hK : B.Contains (Spec (.of K)))
    (base : Spec (.of R) ⟶ S) :
    Function.Injective (fun a : yoneda.obj (siteObject B S hS hR base) ⟶ F =>
      yoneda.map (Over.homMk
        (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R K))) :
          B.obj hK ⟶ B.obj hR) :
        siteObject B S hS hK
          (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ base) ⟶
        siteObject B S hS hR base) ≫ a) := by
  intro a b hab
  let q : ValuativeSquare p :=
    { R := R
      K := K
      ring_mem := hR
      field_mem := hK
      base := base
      generic := yoneda.map (Over.homMk
        (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R K))) :
          B.obj hK ⟶ B.obj hR) :
        siteObject B S hS hK
          (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ base) ⟶
        siteObject B S hS hR base) ≫ a
      special := a ≫ p
      comm := Category.assoc _ _ _ }
  exact congrArg ValuativeSquare.Lift.map ((hu q).elim ⟨a, rfl, rfl⟩
    ⟨b, hab.symm, (isTerminal_yoneda_obj_base B S hS).hom_ext _ _⟩)

/-- Two sections of the category of elements of `F` over the site of `S` which agree on an object
agree on every object mapping to it. -/
theorem sectionOfBasedFunctor_eq_of_hom
    (H K : BigFppfOver B S hS ⥤ (presheafOfCategories (F ⋙ typeToCat)).obj)
    (hH : H ⋙ discreteProjection F = 𝟭 _) (hK : K ⋙ discreteProjection F = 𝟭 _)
    {V W : BigFppfOver B S hS} (i : V ⟶ W)
    (h : sectionOfBasedFunctor H hH W = sectionOfBasedFunctor K hK W) :
    sectionOfBasedFunctor H hH V = sectionOfBasedFunctor K hK V :=
  ((sectionOfBasedFunctor_map H hH i).symm.trans (congrArg (F.map i.op) h)).trans
    (sectionOfBasedFunctor_map K hK i)

/-- **Two sections of the category of elements of `F` over the site of `S` which name the same
element over the generic point name the same element everywhere**, when `S` is the spectrum of a
valuation ring and the structure morphism of `F` satisfies the uniqueness part of the valuative
criterion.

Both sections are read as morphisms from the presheaf represented by the whole spectrum; they
agree there by `AlgebraicGeometry.Space.valuativeGenericRestriction_injective`, and every object
of the site has a morphism to the whole spectrum, along which the agreement restricts. -/
theorem sectionOfBasedFunctor_eq_of_uniqueness
    (p : F ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS))))
    (hu : ValuativeCriterion.Uniqueness p)
    (H K : BigFppfOver B S hS ⥤ (presheafOfCategories (F ⋙ typeToCat)).obj)
    (hH : H ⋙ discreteProjection F = 𝟭 _) (hK : K ⋙ discreteProjection F = 𝟭 _)
    (R L : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    [Field L] [Algebra R L] [IsFractionRing R L]
    (hR : B.Contains (Spec (.of R))) (hL : B.Contains (Spec (.of L)))
    (eR : Spec (.of R) ≅ S)
    (hg : sectionOfBasedFunctor H hH (siteObject B S hS hL
        (Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ eR.hom)) =
      sectionOfBasedFunctor K hK (siteObject B S hS hL
        (Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ eR.hom))) :
    ∀ V, sectionOfBasedFunctor H hH V = sectionOfBasedFunctor K hK V := by
  let A := siteObject B S hS hR eR.hom
  have hmap : sectionHom _ (sectionOfBasedFunctor_map H hH) A =
      sectionHom _ (sectionOfBasedFunctor_map K hK) A := by
    refine valuativeGenericRestriction_injective B S hS p hu R L hR hL eR.hom ?_
    ext V i
    change sectionOfBasedFunctor H hH V.unop = sectionOfBasedFunctor K hK V.unop
    exact sectionOfBasedFunctor_eq_of_hom B S hS H K hH hK i hg
  have hA : sectionOfBasedFunctor H hH A = sectionOfBasedFunctor K hK A :=
    congrArg (fun t : yoneda.obj A ⟶ F => t.app (op A) (𝟙 A)) hmap
  intro V
  refine sectionOfBasedFunctor_eq_of_hom B S hS H K hH hK
    (Over.homMk (ObjectProperty.homMk (V.hom.hom ≫ eR.inv)) ?_ : V ⟶ A) hA
  apply ObjectProperty.hom_ext
  simp [A]

end AlgebraicGeometry.Space

end
