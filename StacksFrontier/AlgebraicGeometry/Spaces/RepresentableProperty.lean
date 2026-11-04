module

public import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
public import StacksCore.CategoryTheory.Pullback
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.RepresentableByAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# Properties of maps of presheaves representable by algebraic spaces (Stacks 03XZ)

Let `a : F ⟶ G` be a map of presheaves on the big fppf site of `S` which is representable by
algebraic spaces, and let `P` be a property of morphisms of algebraic spaces over `S`. Then
`a` *has property `P`* when for every object `U` of the site and every scheme-valued point
`ξ : h_U ⟶ G` the resulting morphism of algebraic spaces `U ×_G F ⟶ U` has `P`.

This is the definition that makes properties of non-representable maps of presheaves work: the
source and target of `a` need not be algebraic spaces, while every base change of `a` to a
scheme of the site is a morphism of algebraic spaces by representability, so `P` can be tested
there.

The source applies the definition only to properties which are stable under base change and
fppf local on the base; as the source itself remarks, the definition makes sense for any
property, and those two conditions are what make it behave well. They are therefore not
imposed here, and a consumer that needs them carries them explicitly.

## Main definitions

* `AlgebraicGeometry.Space.HasProperty`: **Stacks 03XZ**.

## Main results

* `AlgebraicGeometry.yoneda_relativelyRepresentable_diag_tfae_bigFppfOver`: **Stacks 025W**,
  the three equivalent forms of representability of the diagonal of a presheaf.

## Implementation notes

The fibre product is the pullback of presheaves, carrying the algebraic-space structure that
representability supplies; its first projection is read as a morphism in the full subcategory
`AlgebraicGeometry.AlgebraicSpaces` of **Stacks 02X2**, whose target is the representable
algebraic space of `U` from **Stacks 025Z**. Since `AlgebraicGeometry.IsAlgebraicSpace` is a
`Prop`, the algebraic-space structure attached to the fibre product is proof-irrelevant, so the
predicate does not depend on which proof of representability is supplied and no transport
lemma is owed.

The predicate is an `abbrev`, so its universal quantifier is directly available to clients
rather than hidden behind an unfolding lemma.

The same section of the source defines what it means for a representable map of presheaves to
have a property of morphisms of schemes (**Stacks 025V**) — that is Mathlib's
`CategoryTheory.MorphismProperty.presheaf`, the relative property along the Yoneda embedding —
and records the three equivalent forms of representability of the diagonal of a presheaf
(**Stacks 025W**), which is proved for the Yoneda embedding of an arbitrary category with
binary products and fibre products as
`CategoryTheory.yoneda_relativelyRepresentable_diag_tfae`; the instance of that equivalence
for the big fppf site of `S` is stated here, since the site has both kinds of limit.

## References

* [Stacks Project, Tag 025V](https://stacks.math.columbia.edu/tag/025V)
* [Stacks Project, Tag 025W](https://stacks.math.columbia.edu/tag/025W)
* [Stacks Project, Tag 03XZ](https://stacks.math.columbia.edu/tag/03XZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

/-- **Stacks 03XZ.** A map of presheaves `a : F ⟶ G` on the big fppf site of `S` which is
representable by algebraic spaces *has property `P`* when, for every object `U` of the site
and every `ξ : h_U ⟶ G`, the morphism of algebraic spaces `U ×_G F ⟶ U` has `P`. -/
@[stacks 03XZ]
abbrev HasProperty (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G)
    (ha : IsRepresentableByAlgebraicSpaces B S hS a) : Prop :=
  ∀ (U : BigFppfOver B S hS) (ξ : yoneda.obj U ⟶ G),
    P (ObjectProperty.homMk (pullback.fst ξ a) :
      (⟨pullback ξ a, ha U ξ⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS))

end AlgebraicGeometry.Space

namespace AlgebraicGeometry

universe u

add_to_stacks 025V
  "a representable map of presheaves has a property of morphisms of schemes when every
  represented base change of it has that property"
  CategoryTheory.MorphismProperty.presheaf

add_to_stacks 025W
  "stated for the Yoneda embedding of an arbitrary category with binary products and fibre
  products"
  CategoryTheory.yoneda_relativelyRepresentable_diag_tfae

/-- **Stacks 025V.** A representable map of presheaves `a : F ⟶ G` on the big fppf site of `S`
*has property `P`*, for `P` a property of morphisms of schemes, when for every object `U` of
the site and every `ξ : h_U ⟶ G` the resulting morphism of schemes `V_ξ ⟶ U` has `P`. -/
@[stacks 025V]
abbrev Space.HasSchemeProperty (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty Scheme.{u}) {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G) :
    Prop :=
  (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf a

/-- **Stacks 025W.** For a presheaf `F` on the big fppf site of `S`, representability of the
diagonal of `F`, representability of every scheme-valued point of `F`, and representability of
the fibre product of every pair of scheme-valued points of `F` are equivalent. -/
@[stacks 025W]
theorem yoneda_relativelyRepresentable_diag_tfae_bigFppfOver
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    List.TFAE
      [yoneda.relativelyRepresentable (Limits.diag F),
        ∀ (U : BigFppfOver B S hS) (ξ : F.obj (Opposite.op U)),
          yoneda.relativelyRepresentable (yonedaEquiv.symm ξ),
        ∀ (U V : BigFppfOver B S hS) (ξ : F.obj (Opposite.op U))
          (ξ' : F.obj (Opposite.op V)),
          (Limits.pullback (yonedaEquiv.symm ξ) (yonedaEquiv.symm ξ')).IsRepresentable] := by
  let _ : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  exact CategoryTheory.yoneda_relativelyRepresentable_diag_tfae F

end AlgebraicGeometry

end
