module

public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentials
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHomInverseImage

/-!
# The structure map of a composite, in inverse-image form, on a section

For morphisms `p : U ⟶ X` and `f : X ⟶ Y` of algebraic spaces over a scheme `S`, the
inverse-image form `(p ≫ f)^♯ : (p ≫ f)^{-1}𝒪_Y ⟶ 𝒪_U` of the structure map of
[Stacks Project, Tag 03G8] **factors** through the structure map of the first factor: a section
of `(p ≫ f)^{-1}𝒪_Y` is carried by `(p ≫ f)^♯` to the same value as the one its transport along
the iterated-inverse-image comparison is carried to by `p^{-1}(f^♯)` followed by `p^♯`.

That is the whole content of this file, and it carries no hypothesis on `p` or `f`.

## Implementation notes

The underlying statement between the morphisms is
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_compInverseImageRingIso_fSharpInverseImage`;
all that is done here is to evaluate it at a section and to transport the section along the
comparison, which is an isomorphism.

`AlgebraicGeometry.Space.inverseImageStructureSharp_square` is the same equation between the
morphisms, carrying the hypothesis that `p` is étale — which it needs only because it states the
left-hand side through the clause `p^{-1}𝒪_X = 𝒪_U` of [Stacks Project, Tag 03LV].  For the
factorization itself no such hypothesis is used.

This used to live in
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/LiftDifferenceBaseVanishingPair.lean`, where it
was introduced.  It is an identity about the structure map of a composite and nothing else, and
that module's own closure is large — it brings in the universe-polymorphic `Abelian`
instance of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Modules/CohomologyOfModules.lean`, which makes
instance search for an `Epi` of a composite of morphisms of sheaves of modules produce stuck
universe constraints in any module that did not already have it.  So the statement lives here,
where its only import is the comparison it is read off, and both consumers import this.

## Main results

* `AlgebraicGeometry.Space.app_structureSharpInverseImage_comp`: **[Stacks Project, Tag 03G8],
  the composition law in inverse-image form, read on a section.**

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the structure map.
* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV), whose clause the étale
  form of the same equation is stated through.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U X Y : AlgebraicSpaces B S hS}

/-- **[Stacks Project, Tag 03G8], the composition law in inverse-image form, read on a
section.**  A section of `(p ≫ f)^{-1}𝒪_Y` is carried by `(p ≫ f)^♯` to the same value as the
one its transport along the iterated-inverse-image comparison is carried to by `p^{-1}(f^♯)`
followed by `p^♯`.

So the structure map of a composite **factors** through the structure map of its first factor,
as an equation and with no hypothesis on `p` or `f`.  The underlying statement is
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_compInverseImageRingIso_fSharpInverseImage`;
all that is done here is to evaluate it at a section and to transport the section along the
comparison, which is an isomorphism.

`AlgebraicGeometry.Space.inverseImageStructureSharp_square` is the same equation between the
morphisms, carrying the hypothesis that `p` is étale — which it needs only because it states the
left hand side through the clause `p^{-1}𝒪_X = 𝒪_U` of [Stacks Project, Tag 03LV]. For the
factorization itself no such hypothesis is used. -/
theorem app_structureSharpInverseImage_comp (p : U ⟶ X) (f : X ⟶ Y)
    (A : (SmallEtale B S hS U.1)ᵒᵖ)
    (s : ToType ((inverseImageStructureSheaf B S hS (p ≫ f)).obj.obj A)) :
    (structureSharpInverseImage B S hS (p ≫ f)).hom.app A s =
      (structureSharpInverseImage B S hS p).hom.app A
        (((smallEtaleInverseImageRing B S hS p).map
            (structureSharpInverseImage B S hS f)).hom.app A
          (((smallEtaleRingedToposHom_compInverseImageRingIso B S hS p f).inv.app
            (smallEtaleRingedTopos B S hS Y).O).hom.app A s)) := by
  have hiso : ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS p f).hom.app
          (smallEtaleRingedTopos B S hS Y).O).hom.app A
        (((smallEtaleRingedToposHom_compInverseImageRingIso B S hS p f).inv.app
          (smallEtaleRingedTopos B S hS Y).O).hom.app A s) = s :=
    ConcreteCategory.congr_hom
      (congrArg (fun m : inverseImageStructureSheaf B S hS (p ≫ f) ⟶
            inverseImageStructureSheaf B S hS (p ≫ f) ↦ m.hom.app A)
        ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS p f).inv_hom_id_app
          (smallEtaleRingedTopos B S hS Y).O))
      s
  refine Eq.trans (congrArg
    (fun z : ToType ((inverseImageStructureSheaf B S hS (p ≫ f)).obj.obj A) ↦
      (structureSharpInverseImage B S hS (p ≫ f)).hom.app A z) hiso.symm) ?_
  exact ConcreteCategory.congr_hom
    (congrArg (fun m : (smallEtaleInverseImageRing B S hS f ⋙
            smallEtaleInverseImageRing B S hS p).obj (smallEtaleRingedTopos B S hS Y).O ⟶
          (smallEtaleRingedTopos B S hS U).O ↦ m.hom.app A)
      (smallEtaleRingedToposHom_compInverseImageRingIso_fSharpInverseImage B S hS p f))
    (((smallEtaleRingedToposHom_compInverseImageRingIso B S hS p f).inv.app
      (smallEtaleRingedTopos B S hS Y).O).hom.app A s)

end AlgebraicGeometry.Space

end
