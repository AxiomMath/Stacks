module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringSieveSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheaf

/-!
# The quotient map onto the quotient sheaf of a pre-relation is locally surjective

Let `j` be a pre-relation on an object `U` of a site of `S`-schemes presented by a functor
`F`. The canonical map from the functor of points of `F.obj U` onto the quotient sheaf of `j`
is locally surjective, and so is the morphism `yoneda.obj U ⟶ (quotientSheaf J F j).obj`
which the atlas clause of `AlgebraicGeometry.IsAlgebraicSpace` is asked about — the one
determined by the image of the identity of `F.obj U` under the canonical projection.

For the big fppf site over `S` this yields the surjectivity half of the atlas clause for the
quotient sheaf, conditionally on relative representability of that morphism.

## Main definitions

No new definitions are introduced.

## Main results

* `CategoryTheory.Presheaf.isLocallySurjective_yonedaMap`: the comparison morphism of
  representable presheaves attached to a full functor is locally surjective.
* `Stacks.Groupoids.isLocallySurjective_toQuotientPresheaf`: the canonical projection onto the
  quotient presheaf is locally surjective, for every topology and with the objects of the site
  in a universe unrelated to that of the schemes.
* `Stacks.Groupoids.yonedaEquiv_symm_toQuotientSheaf_app_id` identifies the morphism out of
  `yoneda.obj U` determined by the class of the identity with the composite of the Yoneda
  comparison morphism and the projection, and
  `Stacks.Groupoids.isLocallySurjective_yonedaEquiv_symm_toQuotientSheaf` is its local
  surjectivity.
* `AlgebraicGeometry.Space.presheaf_surjective_toQuotientSheaf`: a relatively representable
  quotient map onto the quotient sheaf satisfies the presheaf relativization of
  `AlgebraicGeometry.Surjective`.

## Implementation notes

The big fppf site over `S` has objects in `Type (u + 1)` and morphisms in `Type u`, while the
presheaves of interest are valued in `Type u`, so Mathlib's instance deriving local
surjectivity of the sheafification unit never fires here. Local surjectivity of the
projection onto the quotient sheaf is nevertheless available at these universes from
`Stacks.Groupoids.isLocallySurjective_toQuotientSheaf`, which assumes no relation between
the universes of the site and the values of the presheaves.

Local surjectivity of the projection onto the quotient *presheaf* needs no topology at all: a
coequalizer projection is an epimorphism, epimorphisms of presheaves of types are pointwise
surjective, and a pointwise surjective morphism is locally surjective for every topology. The
pointwise description of the coequalizer is never used.

The morphism the atlas clause asks about is not the projection itself, whose source is the
restricted functor of points `Stacks.Groupoids.points F (F.obj U)` rather than
`yoneda.obj U`. The two are compared by `CategoryTheory.yonedaMap`, which is pointwise
surjective as soon as `F` is full — fullness, not full faithfulness, is what local
surjectivity needs, so no inverse of the comparison is ever constructed.

## References

* [Stacks Project, Tag 0265](https://stacks.math.columbia.edu/tag/0265)
* [Stacks Project, Tag 02VG](https://stacks.math.columbia.edu/tag/02VG)
* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory.Presheaf

/-- **The Yoneda comparison morphism of a full functor is locally surjective.** For `F` full
the map `(V ⟶ X) → (F.obj V ⟶ F.obj X)` is surjective for every `V`, so
`CategoryTheory.yonedaMap F X` is already pointwise surjective. -/
theorem isLocallySurjective_yonedaMap {C : Type u} [Category.{v} C] {D : Type*} [Category.{v} D]
    (J : GrothendieckTopology C) (F : C ⥤ D) [F.Full] (X : C) :
    IsLocallySurjective J (yonedaMap F X) :=
  isLocallySurjective_of_surjective J _ fun _ g => F.map_surjective g

end CategoryTheory.Presheaf

namespace Stacks.Groupoids

variable {S : Scheme.{u}} {C : Type v} [Category.{u} C]

/-- The projection onto the quotient presheaf of a pre-relation is pointwise surjective: it is
a coequalizer projection, hence an epimorphism of presheaves of types.

File-local, because the same statement is available publicly from
`StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafInjective` with the morphisms of the site
left in a free universe; only the specialization used below is needed here. -/
private theorem surjective_toQuotientPresheaf_app (F : C ⥤ Over S) {R U : Over S}
    (j : PreRelation R U) (X : Cᵒᵖ) :
    Function.Surjective ((toQuotientPresheaf F j).app X) := by
  have hepi : Epi (toQuotientPresheaf F j) := coequalizer.π_epi
  rw [NatTrans.epi_iff_epi_app] at hepi
  exact (epi_iff_surjective _).1 (hepi X)

/-- The projection onto the quotient presheaf of a pre-relation is locally surjective for
every topology on the site. -/
theorem isLocallySurjective_toQuotientPresheaf (J : GrothendieckTopology C) (F : C ⥤ Over S)
    {R U : Over S} (j : PreRelation R U) :
    Presheaf.IsLocallySurjective J (toQuotientPresheaf F j) :=
  Presheaf.isLocallySurjective_of_surjective J _ (surjective_toQuotientPresheaf_app F j)

/-- The morphism `yoneda.obj U ⟶ (quotientSheaf J F j).obj` determined by the class of the
identity of `F.obj U` is the Yoneda comparison morphism followed by the canonical projection
onto the quotient sheaf. -/
theorem yonedaEquiv_symm_toQuotientSheaf_app_id (J : GrothendieckTopology C)
    [HasSheafify J (Type u)] (F : C ⥤ Over S) {R : Over S} {U : C}
    (j : PreRelation R (F.obj U)) :
    yonedaEquiv.symm ((toQuotientSheaf J F j).app (op U) (𝟙 (F.obj U))) =
      yonedaMap F U ≫ toQuotientSheaf J F j := by
  apply yonedaEquiv.injective
  rw [Equiv.apply_symm_apply, yonedaEquiv_comp]
  congr 1
  exact (F.map_id U).symm

/-- **The quotient map onto the quotient sheaf of a pre-relation is locally surjective.** This
is the morphism out of `yoneda.obj U` which the atlas clause of
`AlgebraicGeometry.IsAlgebraicSpace` is asked about. -/
theorem isLocallySurjective_yonedaEquiv_symm_toQuotientSheaf (J : GrothendieckTopology C)
    [HasSheafify J (Type u)] (F : C ⥤ Over S) [F.Full] {R : Over S} {U : C}
    (j : PreRelation R (F.obj U)) :
    Presheaf.IsLocallySurjective J
      (yonedaEquiv.symm ((toQuotientSheaf J F j).app (op U) (𝟙 (F.obj U)))) := by
  rw [yonedaEquiv_symm_toQuotientSheaf_app_id]
  have := Presheaf.isLocallySurjective_yonedaMap J F U
  have := isLocallySurjective_toQuotientSheaf J F j
  infer_instance

end Stacks.Groupoids

namespace AlgebraicGeometry.Space

/-- **The quotient map onto the quotient sheaf of a pre-relation is surjective after every
representable base change, provided it is relatively representable.** This is the surjectivity
clause of Stacks 0265 for the big fppf site over `S`, with relative representability of the
quotient map as a hypothesis.

The hypothesis is not weaker than the conclusion: `CategoryTheory.MorphismProperty.presheaf`
is `CategoryTheory.MorphismProperty.relative` for `CategoryTheory.yoneda`, whose first
conjunct is exactly relative representability, so the two are equivalent. What the statement
says is that the surjectivity half carries no further content once the quotient map is known
to be representable; neither the affineness of `U` nor the étale equivalence-relation
condition on `j` is used.

The sheafification hypothesis is not a restriction: the big fppf site over `S` is essentially
small, so `AlgebraicGeometry.BigFppfOver.hasSheafify` discharges it unconditionally. -/
theorem presheaf_surjective_toQuotientSheaf (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (U : BigFppfOver B S hS)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {R : Over S} (j : Stacks.Groupoids.PreRelation R ((Over.post B.inclusion).obj U))
    (hrep : yoneda.relativelyRepresentable
      (yonedaEquiv.symm ((Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS)
        (Over.post B.inclusion) j).app (op U) (𝟙 ((Over.post B.inclusion).obj U))))) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))
      (yonedaEquiv.symm ((Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS)
        (Over.post B.inclusion) j).app (op U) (𝟙 ((Over.post B.inclusion).obj U)))) :=
  presheaf_surjective_of_isLocallySurjective B S hS hrep
    (Stacks.Groupoids.isLocallySurjective_yonedaEquiv_symm_toQuotientSheaf
      (BigFppfOver.topology B S hS) (Over.post B.inclusion (X := B.obj hS)) j)

end AlgebraicGeometry.Space

end
