module

public import StacksFrontier.CategoryTheory.Sites.Point.OfToposPoint

/-!
# The identification of Stacks 00YA (2) on germs

Let `p` be a point of the topos `Sh(C, J)`. Stacks 00YA (2) reconstructs a point
`CategoryTheory.PointOfTopos.sitePointOfEssentiallySmall` of the site `(C, J)` whose stalk
functor on sheaves of sets is identified with `p⁻¹` by
`CategoryTheory.PointOfTopos.sheafFiberIsoInverseImageOfEssentiallySmall`. That identification
is built as a comparison of functors and is consumed as such, which is enough to transport a
stalk but not to compute with one: every element of a stalk at a point of a site is a germ of a
section over a chart, and nothing said what the comparison does to such a germ.

This file says it. A section `z` of a sheaf `F` over a chart `X` is named by a morphism of
sheaves `h_X^# ⟶ F` out of the sheafification of the presheaf represented by `X`, through
sheafification and the counit; the comparison sends the germ of `z` at a point of the site lying
over `X` to the image of that point under `p⁻¹` applied to the naming morphism. Both halves of
the statement are forced: the fibre functor of the reconstructed point is `X ↦ p⁻¹(h_X^#)` by
construction, so a point of the site lying over `X` *is* an element of `p⁻¹(h_X^#)`, and the
comparison on presheaves is Yoneda's lemma
(`CategoryTheory.PointOfTopos.presheafStalkSection`).

## Main results

* `CategoryTheory.PointOfTopos.sheafFiberIsoInverseImage_hom_app_toPresheafFiber` — the
  comparison carries the germ of `z` at `(X, x)` to `p⁻¹` of the naming morphism, applied
  to `x`.
* `CategoryTheory.PointOfTopos.sheafFiberIsoInverseImage_hom_app_toPresheafFiber_sheafHom` —
  the same with the naming morphism written as a single morphism of sheaves, in the form a
  computation downstream uses.

## References

* [Stacks Project, Tag 00YA](https://stacks.math.columbia.edu/tag/00YA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace CategoryTheory.PointOfTopos

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [LocallySmall.{w} C]
  [HasSheafify J (Type w)] (p : PointOfTopos.{w, v, u} J) [EssentiallySmall.{w} C]

/-- **The identification of Stacks 00YA (2), on a germ.**  A section `z` of a sheaf `F` over a
chart `X` is named by the morphism of presheaves `h_X ⟶ F` that Yoneda's lemma attaches to it;
sheafifying and composing with the counit turns that into a morphism of sheaves
`h_X^# ⟶ F`.  The comparison `p⁻¹ ≅ (sitePoint)_*` carries the germ of `z` at a point `x` of
the site lying over `X` — that is, an element of `p⁻¹(h_X^#)` — to the image of `x` under `p⁻¹`
of the naming morphism. -/
theorem sheafFiberIsoInverseImage_hom_app_toPresheafFiber (F : Sheaf J (Type w)) (X : C)
    (x : p.sitePointOfEssentiallySmall.fiber.obj X) (z : F.obj.obj (op X)) :
    p.sheafFiberIsoInverseImageOfEssentiallySmall.hom.app F
        (p.sitePointOfEssentiallySmall.toPresheafFiber X x F.obj z) =
      p.inverseImage.map ((sheafificationAdjunction J (Type w)).counit.app F)
        (p.presheafStalkFunctor.map (shrinkYonedaEquiv.symm z) x) := by
  change p.inverseImage.map ((sheafificationAdjunction J (Type w)).counit.app F)
      (p.presheafFiberComparisonAppOfEssentiallySmall F.obj
        (p.sitePointOfEssentiallySmall.toPresheafFiber X x F.obj z)) = _
  rw [p.presheafFiberComparisonAppOfEssentiallySmall_toPresheafFiber F.obj x z]

/-- **The identification of Stacks 00YA (2), on a germ, with the naming morphism assembled.**
The same statement as
`CategoryTheory.PointOfTopos.sheafFiberIsoInverseImage_hom_app_toPresheafFiber`, with the
sheafification of the Yoneda morphism and the counit composed into the single morphism of
sheaves `h_X^# ⟶ F` which names the section. -/
theorem sheafFiberIsoInverseImage_hom_app_toPresheafFiber_sheafHom (F : Sheaf J (Type w)) (X : C)
    (x : p.sitePointOfEssentiallySmall.fiber.obj X) (z : F.obj.obj (op X)) :
    p.sheafFiberIsoInverseImageOfEssentiallySmall.hom.app F
        (p.sitePointOfEssentiallySmall.toPresheafFiber X x F.obj z) =
      p.inverseImage.map
        ((presheafToSheaf J (Type w)).map (shrinkYonedaEquiv.symm z) ≫
          (sheafificationAdjunction J (Type w)).counit.app F) x := by
  rw [p.sheafFiberIsoInverseImage_hom_app_toPresheafFiber F X x z, p.inverseImage.map_comp]
  rfl

end CategoryTheory.PointOfTopos

end
