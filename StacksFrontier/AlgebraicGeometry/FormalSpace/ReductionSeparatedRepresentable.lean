module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionSeparatedConverse
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 0AJ6 with clause (2) asserting representability

Let `S` be a scheme contained in a big fppf site `B` and let `X` be a formal algebraic space
over `S`. Clause (2) of **Stacks 0AJ6** reads, in the source, that for every pair of morphisms
`U ⟶ X`, `V ⟶ X` with `U`, `V` affine the fibre product `U ×_X V` *is affine* and
`𝒪(U) ⊗_ℤ 𝒪(V) ⟶ 𝒪(U ×_X V)` is surjective. Calling `U ×_X V` affine presupposes that it is a
scheme, which for a formal algebraic space is the representability assertion of **Stacks
0AIP**; the source invokes 0AIP for exactly that.

`AlgebraicGeometry.FormalSpace.HasAffineIntersectionsULift`, the form of clause (2) that
`StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionSeparated` and
`StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionSeparatedConverse` carry, instead
quantifies over the objects of the site that represent the fibre product and says nothing when
there are none — the reading the carrier of Stacks 0AHS uses for the identical clause. This
file supplies the stronger form, `…HasRepresentableAffineIntersectionsULift`, which asserts
that a representing object exists, and proves the two equivalent for a formal algebraic space:
the representing object comes from Stacks 0AIP for an *arbitrary* formal algebraic space,
`AlgebraicGeometry.FormalSpace.exists_isPullback_locallyOfFiniteType_of_isFormalAlgebraicSpace`,
and conversely any two objects representing one fibre product are isomorphic over the two test
objects, the universe-lifted Yoneda embedding being fully faithful, so affineness and the
surjectivity do not depend on which is taken.

Stacks 0AJ6 then holds with clause (2) in the source's own form.

## Main definitions

* `AlgebraicGeometry.FormalSpace.HasRepresentableAffineIntersectionsULift`: clause (2) of
  Stacks 0AJ6 asserting representability — for every pair of affine test objects over `X` there
  *exists* an object of the site representing the fibre product, its underlying scheme is affine
  and the map on global sections is surjective.

## Main results

* `hasAffineIntersectionsULift_of_hasRepresentableAffineIntersectionsULift`: the stronger clause
  (2) implies the weaker one, for an arbitrary presheaf.
* `AlgebraicGeometry.FormalSpace.hasRepresentableAffineIntersectionsULift_iff`: the two forms of
  clause (2) agree on a formal algebraic space.
* `isAbsolutelySeparated_reduction_iff_hasRepresentableAffineIntersectionsULift`: **Stacks 0AJ6**
  with clause (2) in the source's form, read against a reduction of `X` and a presentation of it
  by a presheaf of `Type u`.
* `…exists_isReduction_and_isAbsolutelySeparated_iff_hasRepresentableAffineIntersectionsULift`:
  **Stacks 0AJ6** with clause (2) in the source's form, the reduction produced from Stacks 0AIN.

## References

* [Stacks Project, Tag 0AHS](https://stacks.math.columbia.edu/tag/0AHS)
* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
* [Stacks Project, Tag 0AIP](https://stacks.math.columbia.edu/tag/0AIP)
* [Stacks Project, Tag 0AJ6](https://stacks.math.columbia.edu/tag/0AJ6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Clause (2) asserting representability -/

/-- **Clause (2) of Stacks 0AJ6, asserting representability.** For every pair of objects `U`,
`V` of the big fppf site of `S` with affine underlying scheme and every pair of morphisms
`h_U ⟶ X`, `h_V ⟶ X` out of their universe-lifted Yoneda presheaves there is an object of the
site representing the fibre product `U ×_X V`, its underlying scheme is affine, and the
canonical map `Γ(U, ⊤) ⊗_ℤ Γ(V, ⊤) ⟶ Γ(U ×_X V, ⊤)` of
`AlgebraicGeometry.globalSectionsTensorLift` is surjective.

This is the source's own reading of clause (2), in which calling `U ×_X V` affine presupposes
that it is a scheme. `AlgebraicGeometry.FormalSpace.HasAffineIntersectionsULift` is the weaker
form which quantifies over the representing objects instead; the two agree on a formal
algebraic space, by `…hasRepresentableAffineIntersectionsULift_iff`. -/
abbrev HasRepresentableAffineIntersectionsULift
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)) : Prop :=
  ∀ (U V : BigFppfOver B S hS)
    (a : (uliftYoneda.{u + 1}).obj U ⟶ X) (b : (uliftYoneda.{u + 1}).obj V ⟶ X),
    IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
    IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
    ∃ (Q : BigFppfOver B S hS) (p : Q ⟶ U) (q : Q ⟶ V),
      IsPullback ((uliftYoneda.{u + 1}).map p) ((uliftYoneda.{u + 1}).map q) a b ∧
        IsAffine ((BigFppfOver.toScheme B S hS).obj Q) ∧
          Function.Surjective (globalSectionsTensorLift
            ((BigFppfOver.toScheme B S hS).map p) ((BigFppfOver.toScheme B S hS).map q))

/-- **Two objects of the site representing one fibre product of universe-lifted Yoneda
presheaves are isomorphic over the two test objects.** The two cartesian squares give an
isomorphism of the two representing presheaves commuting with the projections, and the
universe-lifted Yoneda embedding is fully faithful, so that isomorphism comes from one in the
site. -/
private theorem exists_isIso_comp_eq_of_isPullback
    {U V Q Q' : BigFppfOver B S hS} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    {a : (uliftYoneda.{u + 1}).obj U ⟶ X} {b : (uliftYoneda.{u + 1}).obj V ⟶ X}
    {p : Q ⟶ U} {q : Q ⟶ V} {p' : Q' ⟶ U} {q' : Q' ⟶ V}
    (sq : IsPullback ((uliftYoneda.{u + 1}).map p) ((uliftYoneda.{u + 1}).map q) a b)
    (sq' : IsPullback ((uliftYoneda.{u + 1}).map p') ((uliftYoneda.{u + 1}).map q') a b) :
    ∃ φ : Q ⟶ Q', IsIso φ ∧ φ ≫ p' = p ∧ φ ≫ q' = q := by
  let ff : (uliftYoneda.{u + 1} (C := BigFppfOver B S hS)).FullyFaithful :=
    ULiftYoneda.fullyFaithful _
  let e := sq.isoIsPullback _ _ sq'
  refine ⟨ff.preimage e.hom, (ff.preimageIso e).isIso_hom, ff.map_injective ?_,
    ff.map_injective ?_⟩ <;> rw [Functor.map_comp, ff.map_preimage]
  · exact sq.isoIsPullback_hom_fst _ _ sq'
  · exact sq.isoIsPullback_hom_snd _ _ sq'

/-- **The stronger clause (2) implies the weaker one.** If some object of the site represents
the fibre product with affine underlying scheme and surjective map on global sections then every
object representing it does: the two are isomorphic over the two test objects, the comparison is
an isomorphism of affine schemes hence a closed immersion onto an affine scheme, so the source
is affine and the comparison is surjective on global sections, and precomposing both
projections with it precomposes the map on global sections with that surjection. -/
theorem hasAffineIntersectionsULift_of_hasRepresentableAffineIntersectionsULift
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (h : HasRepresentableAffineIntersectionsULift B S hS X) :
    HasAffineIntersectionsULift B S hS X := by
  intro U V Q a b p q hU hV sq
  obtain ⟨Q', p', q', sq', hQ'aff, hQ'surj⟩ := h U V a b hU hV
  obtain ⟨φ, hφiso, hφp, hφq⟩ := exists_isIso_comp_eq_of_isPullback B S hS sq sq'
  obtain ⟨hQaff, hφsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine
    ((BigFppfOver.toScheme B S hS).map φ)
  refine ⟨hQaff, ?_⟩
  rw [← hφp, ← hφq, Functor.map_comp, Functor.map_comp, globalSectionsTensorLift_comp]
  exact hφsurj.comp hQ'surj

/-- **The two forms of clause (2) of Stacks 0AJ6 agree on a formal algebraic space.** The
stronger form implies the weaker one always; the converse needs a representing object for the
fibre product of two scheme-valued points, which is the representability assertion of Stacks
0AIP for an arbitrary formal algebraic space. -/
theorem hasRepresentableAffineIntersectionsULift_iff
    {X : FppfSheaf B S hS} (hX : IsFormalAlgebraicSpace B S hS X) :
    HasRepresentableAffineIntersectionsULift B S hS X.obj ↔
      HasAffineIntersectionsULift B S hS X.obj := by
  let : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  refine ⟨hasAffineIntersectionsULift_of_hasRepresentableAffineIntersectionsULift B S hS,
    fun h U V a b hU hV ↦ ?_⟩
  obtain ⟨Q, p, q, sq, -⟩ :=
    exists_isPullback_locallyOfFiniteType_of_isFormalAlgebraicSpace B S hS hX U V a b
  exact ⟨Q, p, q, sq, h U V Q a b p q hU hV sq⟩

/-! ### Stacks 0AJ6 with clause (2) in the source's form -/

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **Stacks 0AJ6, with clause (2) asserting representability.** Let `X` be a formal algebraic
space over `S` and let `i : X_red ⟶ X` be a reduction of `X`, presented by a presheaf `Xred` of
`Type u` together with an isomorphism from its universe lift. Then `Xred` is a separated
algebraic space if and only if for every pair of objects of the big fppf site of `S` with affine
underlying scheme and every pair of morphisms from their universe-lifted Yoneda presheaves into
`X` the fibre product is represented by an object of the site with affine underlying scheme and
the canonical map from the tensor product over `ℤ` of the two rings of global sections to its
ring of global sections is surjective.

This is `…isAbsolutelySeparated_reduction_iff_hasAffineIntersectionsULift` composed with
`…hasRepresentableAffineIntersectionsULift_iff`, which identifies clause (2) in the source's
form with the form that quantifies over the representing objects. -/
@[stacks 0AJ6 "both implications, with clause (2) in the source's own form, which asserts that \
the fibre product U ×_X V is representable by an object of the site and that its underlying \
scheme is affine, rather than quantifying over the objects of the site representing it. The \
two readings agree on a formal algebraic space, by AlgebraicGeometry.FormalSpace.\
hasRepresentableAffineIntersectionsULift_iff, whose nontrivial direction is the \
representability assertion of Stacks 0AIP for an arbitrary formal algebraic space. Read \
against a reduction of X, in the sense of AlgebraicGeometry.FormalSpace.IsReduction, and a \
presentation of it by a presheaf of Type u together with an isomorphism from its universe \
lift -- an algebraic space over S being a presheaf of Type u while a formal algebraic space \
is a sheaf of Type (u + 1). The tag with the reduction and its presentation produced is \
AlgebraicGeometry.FormalSpace.\
exists_isReduction_and_isAbsolutelySeparated_iff_hasRepresentableAffineIntersectionsULift",
  ega "I 10.15.7" "more general"]
theorem isAbsolutelySeparated_reduction_iff_hasRepresentableAffineIntersectionsULift
    {X Xr : FppfSheaf B S hS} (hX : IsFormalAlgebraicSpace B S hS X)
    {i : Xr ⟶ X} (hi : IsReduction B S hS X Xr i)
    {Xred : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : Xred ⋙ uliftFunctor.{u + 1} ≅ Xr.obj) :
    Space.IsAbsolutelySeparated B S hS hZ Xred ↔
      HasRepresentableAffineIntersectionsULift B S hS X.obj :=
  (isAbsolutelySeparated_reduction_iff_hasAffineIntersectionsULift B S hS hZ hX hi e).trans
    (hasRepresentableAffineIntersectionsULift_iff B S hS hX).symm

/-- **Stacks 0AJ6, with clause (2) asserting representability.** Let `S` be a scheme contained
in a big fppf site `B` and let `X` be a formal algebraic space over `S`. The reduction of `X`
exists — a reduced algebraic space `X_red` and a representable thickening `i : X_red ⟶ X`
through which every morphism to `X` from a reduced algebraic space factors uniquely — it is
presented by a presheaf `Xred` of `Type u` together with an isomorphism from its universe lift,
and the following are equivalent:

1. `Xred` is a separated algebraic space;
2. for every pair of objects of the big fppf site of `S` with affine underlying scheme and
   every pair of morphisms from their universe-lifted Yoneda presheaves into `X`, the fibre
   product is represented by an object of the site with affine underlying scheme and the
   canonical map from the tensor product over `ℤ` of the two rings of global sections to its
   ring of global sections is surjective.

Clause (2) is here the source's own, asserting that `U ×_X V` is a scheme. The reduction comes
from Stacks 0AIN for an arbitrary formal algebraic space,
`AlgebraicGeometry.FormalSpace.exists_isReduction_of_isFormalAlgebraicSpace`. -/
@[stacks 0AJ6 "the reduction and its presentation by a presheaf of Type u produced, from \
Stacks 0AIN for an arbitrary formal algebraic space and from the pointwise u-smallness of an \
algebraic space, with clause (2) in the source's own form, which asserts that the fibre \
product U ×_X V is representable by an object of the site and that its underlying scheme is \
affine. The variant whose clause (2) quantifies over the objects of the site representing the \
fibre product instead is AlgebraicGeometry.FormalSpace.\
exists_isReduction_and_isAbsolutelySeparated_iff_hasAffineIntersectionsULift in \
StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionSeparatedConverse",
  ega "I 10.15.7" "more general"]
theorem exists_isReduction_and_isAbsolutelySeparated_iff_hasRepresentableAffineIntersectionsULift
    (X : FppfSheaf B S hS) (hX : IsFormalAlgebraicSpace B S hS X) :
    ∃ (Xr : FppfSheaf B S hS) (i : Xr ⟶ X) (Xred : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (_ : Xred ⋙ uliftFunctor.{u + 1} ≅ Xr.obj),
      IsReduction B S hS X Xr i ∧
        (Space.IsAbsolutelySeparated B S hS hZ Xred ↔
          HasRepresentableAffineIntersectionsULift B S hS X.obj) := by
  obtain ⟨Xr, i, Xred, e, hi, hiff⟩ :=
    exists_isReduction_and_isAbsolutelySeparated_iff_hasAffineIntersectionsULift
      B S hS hZ X hX
  exact ⟨Xr, i, Xred, e, hi,
    hiff.trans (hasRepresentableAffineIntersectionsULift_iff B S hS hX).symm⟩

end AlgebraicGeometry.FormalSpace

end
