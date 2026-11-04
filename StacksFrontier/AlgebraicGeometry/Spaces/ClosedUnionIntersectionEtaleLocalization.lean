module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealLattice
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleIdealSheafRestriction

/-!
# Scheme-theoretic union and intersection commute with étale localization

Let `φ : U ⟶ X` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf site
`B` and let `Y, Z ⊆ X` be closed subspaces, with inverse images `φ⁻¹Y, φ⁻¹Z ⊆ U`, the closed
subspaces of Stacks 083Q.  Right after Definition 0CYZ the Stacks project records, without
proof, that the formation of the scheme-theoretic intersection commutes with étale localization
and that the same is true for the scheme-theoretic union.  This file proves both:

`φ⁻¹(Y ∩ Z) = φ⁻¹Y ∩ φ⁻¹Z` and, for `φ` étale, `φ⁻¹(Y ∪ Z) = φ⁻¹Y ∪ φ⁻¹Z`.

## Main results

* `AlgebraicGeometry.Space.preimage_schemeTheoreticIntersection`: the inverse image of the
  scheme-theoretic intersection is the scheme-theoretic intersection of the inverse images, for
  an arbitrary morphism of algebraic spaces.
* `AlgebraicGeometry.Space.definingIdealSheaf_preimage_inf_eq`: for `φ` étale, the defining ideal
  sheaf of the inverse image of the scheme-theoretic union is the meet of the defining ideal
  sheaves of the inverse images.
* `AlgebraicGeometry.Space.preimage_schemeTheoreticUnion`: **the inverse image of the
  scheme-theoretic union is the scheme-theoretic union of the inverse images**, for `φ` étale.

## Implementation notes

The intersection is the meet of the two subfunctors, and both the meet and the inverse image of
subfunctors are formed objectwise, so the first statement holds for every morphism and is
`rfl`: membership in the inverse image of the meet and in the meet of the inverse images unfold
to the same conjunction, `Set.preimage_inter` being itself `rfl`.

The union is not formed objectwise — it is the smallest closed subspace containing both — so the
second statement is proved through defining ideal sheaves, where it becomes the meet again.
Three inputs from the library are combined, at every étale chart `V` of `U`:

* `AlgebraicGeometry.Space.definingIdealAt_preimage_eq_definingIdealAt_postcomp`, the clause of
  Stacks 04CO saying that the defining ideal of `φ⁻¹W` at `V` is the defining ideal of `W` at the
  postcomposed chart `V ⟶ U ⟶ X`;
* `AlgebraicGeometry.Space.definingIdealSheaf_schemeTheoreticUnion`, the union half of
  Stacks 0CYZ, used on `X` for `Y ∪ Z` and on `U` for `φ⁻¹Y ∪ φ⁻¹Z`;
* `AlgebraicGeometry.Space.definingIdealSheaf_injective`, the injectivity clause of Stacks 03MB,
  which turns the resulting equality of ideal sheaves back into an equality of closed subspaces.

Étaleness is used only to have the postcomposed chart at all, that is, to know that composing an
étale chart of `U` with `φ` is an étale chart of `X`; the ideal computation itself needs no
hypothesis on `φ`.

## References

* [Stacks Project, Tag 0CYZ](https://stacks.math.columbia.edu/tag/0CYZ)
* [Stacks Project, Tag 04CO](https://stacks.math.columbia.edu/tag/04CO)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U X : AlgebraicSpaces B S hS}

/-- **The inverse image of the scheme-theoretic intersection of two closed subspaces is the
scheme-theoretic intersection of their inverse images.**  No hypothesis on the morphism is
needed: the scheme-theoretic intersection is the meet of the two subfunctors, and both the meet
and the inverse image of subfunctors are formed objectwise. -/
theorem preimage_schemeTheoreticIntersection (φ : U ⟶ X) (Y Z : ClosedSubspaces B S hS X.1) :
    (schemeTheoreticIntersection B S hS X.1 X.2 Y Z).1.preimage φ.hom =
      (schemeTheoreticIntersection B S hS U.1 U.2
          ⟨Y.1.preimage φ.hom, isClosedSubspace_preimage B S hS φ.hom Y.1 X.2 U.2 Y.2⟩
          ⟨Z.1.preimage φ.hom,
            isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2⟩).1 := by
  show (Y.1 ⊓ Z.1).preimage φ.hom = Y.1.preimage φ.hom ⊓ Z.1.preimage φ.hom
  rfl

/-- **The defining ideal of the inverse image of a closed subspace at an étale chart is the
defining ideal of the subspace at the postcomposed chart.**  This is
`AlgebraicGeometry.Space.definingIdealAt_preimage_eq_definingIdealAt_postcomp`, the clause of
Stacks 04CO, read through `AlgebraicGeometry.Space.definingIdealSheaf_obj`. -/
theorem definingIdealSheaf_preimage_obj (φ : U ⟶ X) (hφ : IsEtale B S hS φ.hom)
    (W : ClosedSubspaces B S hS X.1) (V : SmallEtale B S hS U.1) :
    (definingIdealSheaf B S hS U
        ⟨W.1.preimage φ.hom,
          isClosedSubspace_preimage B S hS φ.hom W.1 X.2 U.2 W.2⟩).obj (op V) =
      (definingIdealSheaf B S hS X W).obj (op ((smallEtalePostcomp B S hS φ hφ).obj V)) :=
  definingIdealAt_preimage_eq_definingIdealAt_postcomp B S hS φ hφ W V

/-- **The defining ideal sheaf of the inverse image of the scheme-theoretic union is the meet of
the defining ideal sheaves of the inverse images.**

At an étale chart `V` of `U` both sides are the meet of the defining ideals of `Y` and of `Z` at
the postcomposed chart `V ⟶ U ⟶ X`: on the left by
`AlgebraicGeometry.Space.definingIdealAt_preimage_eq_definingIdealAt_postcomp` followed by the
union half of Stacks 0CYZ on `X`, on the right by that same chartwise equality applied to `Y` and
to `Z` separately. -/
theorem definingIdealSheaf_preimage_inf_eq (φ : U ⟶ X) (hφ : IsEtale B S hS φ.hom)
    (Y Z : ClosedSubspaces B S hS X.1) :
    definingIdealSheaf B S hS U
        ⟨(schemeTheoreticUnion B S hS X.1 X.2 Y Z).1.preimage φ.hom,
          isClosedSubspace_preimage B S hS φ.hom
            (schemeTheoreticUnion B S hS X.1 X.2 Y Z).1 X.2 U.2
            (schemeTheoreticUnion B S hS X.1 X.2 Y Z).2⟩ =
      definingIdealSheaf B S hS U
          ⟨Y.1.preimage φ.hom, isClosedSubspace_preimage B S hS φ.hom Y.1 X.2 U.2 Y.2⟩ ⊓
        definingIdealSheaf B S hS U
          ⟨Z.1.preimage φ.hom, isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2⟩ := by
  refine SheafOfModules.Submodule.ext (PresheafOfModules.Submodule.ext fun W => ?_)
  obtain ⟨V⟩ := W
  change _ = _ ⊓ _
  rw [definingIdealSheaf_preimage_obj B S hS φ hφ _ V,
    definingIdealSheaf_preimage_obj B S hS φ hφ Y V,
    definingIdealSheaf_preimage_obj B S hS φ hφ Z V,
    definingIdealSheaf_schemeTheoreticUnion B S hS X Y Z]
  rfl

/-- **The inverse image of the scheme-theoretic union of two closed subspaces along an étale
morphism is the scheme-theoretic union of their inverse images.**  This is the second half of the
remark the Stacks project makes after Definition 0CYZ.

By `AlgebraicGeometry.Space.definingIdealSheaf_preimage_inf_eq` the two closed subspaces have the
same defining ideal sheaf — on the right by the union half of Stacks 0CYZ on `U` — and a closed
subspace is determined by its defining ideal sheaf, which is the injectivity clause of
Stacks 03MB. -/
theorem preimage_schemeTheoreticUnion (φ : U ⟶ X) (hφ : IsEtale B S hS φ.hom)
    (Y Z : ClosedSubspaces B S hS X.1) :
    (schemeTheoreticUnion B S hS X.1 X.2 Y Z).1.preimage φ.hom =
      (schemeTheoreticUnion B S hS U.1 U.2
          ⟨Y.1.preimage φ.hom, isClosedSubspace_preimage B S hS φ.hom Y.1 X.2 U.2 Y.2⟩
          ⟨Z.1.preimage φ.hom,
            isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2⟩).1 :=
  congrArg Subtype.val (definingIdealSheaf_injective B S hS U
    ((definingIdealSheaf_preimage_inf_eq B S hS φ hφ Y Z).trans
      (definingIdealSheaf_schemeTheoreticUnion B S hS U _ _).symm))

end AlgebraicGeometry.Space

end
