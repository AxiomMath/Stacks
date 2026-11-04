module

public import StacksFrontier.AlgebraicGeometry.QuasiCompactColimit.AffineCover

/-!
# Recognising a filtered colimit of algebra sheaves that is not a union of subalgebras

`Stacks.QuasiCompactColimit.nonempty_isColimit_of_sections` recognises a filtered colimit of
algebra sheaves from two conditions on the sections over each affine open: the components of the
cocone are *injective*, and they are jointly surjective.  The injectivity hypothesis restricts
that criterion to diagrams of subalgebras of the vertex, which is the situation of Stacks Tag
05JT.

The diagram of Stacks Tag 05JS is not of that kind.  There the approximating algebras are
`Sym(F_i)/I_{i,j}` for `I_{i,j}` a finitely generated subideal of the kernel of
`Sym(F_i) → A`, so the map to `A` has kernel `I_i/I_{i,j}` and is injective only in the limit.
What holds instead is that two sections with the same image agree after passing to a later index,
which is the general elementwise description of a filtered colimit and is exactly the hypothesis
of `Stacks.QuasiCompactColimit.isColimitOfJointlySurjective`.  This file records that
combination at the level of algebra sheaves, which is the shape Tag 05JS needs and which is not
obtainable from the injective criterion.

## Main results

* `Stacks.QcohAlgebraFPColimit.nonempty_isColimit_of_affineSections`: **a cocone of algebra
  sheaves over a filtered diagram is colimiting as soon as, over every affine open, its
  components are jointly surjective on sections and two sections with the same image already
  agree at a later index.**

## Implementation notes

No quasi-compactness or quasi-separatedness hypothesis appears, for the reason recorded in
`Stacks.QuasiCompactColimit.nonempty_isColimit_of_affineOpens`: the reduction to affine opens
needs only that they form a basis, which holds on any scheme.  Those hypotheses of Tag 05JS are
consumed in *verifying* the two sectionwise conditions, not in the reduction to them.

The eventual-injectivity hypothesis is stated for the composite diagram
`F ⋙ Stacks.QuasiCompactColimit.algebraSectionsFunctor U` rather than for `F` followed by taking
sections, so that it is the hypothesis of
`Stacks.QuasiCompactColimit.isColimitOfJointlySurjective` verbatim after the diagram of the
mapped cocone is unfolded; the two are definitionally equal, the diagram of
`CategoryTheory.Functor.mapCocone` being that composite by definition.

## References

* [The Stacks Project, Tag 05JS](https://stacks.math.columbia.edu/tag/05JS)
* [The Stacks Project, Tag 05JT](https://stacks.math.columbia.edu/tag/05JT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.RelativeSpec Stacks.QuasiCompactColimit

universe v' u' u

namespace Stacks.QcohAlgebraFPColimit

variable {X : Scheme.{u}} {K : Type u'} [Category.{v'} K] {F : K ⥤ AlgebraSheaf X}

/-- **A cocone of algebra sheaves over a filtered diagram is colimiting as soon as, over every
affine open, its components are jointly surjective on sections and two sections with the same
image agree at a later index.**

This is the criterion Stacks Tag 05JS needs.  Its diagram of finitely presented approximations
does not consist of subalgebras of the vertex, so
`Stacks.QuasiCompactColimit.nonempty_isColimit_of_sections`, whose injectivity hypothesis forces
that, does not apply. -/
theorem nonempty_isColimit_of_affineSections [IsFiltered K] (c : Cocone F)
    (hsurj : ∀ U : X.Opens, IsAffineOpen U → ∀ x : (algebraSectionsFunctor U).obj c.pt,
      ∃ (k : K) (y : (algebraSectionsFunctor U).obj (F.obj k)),
        (algebraSectionsFunctor U).map (c.ι.app k) y = x)
    (hinj : ∀ U : X.Opens, IsAffineOpen U → ∀ (k : K)
        (x y : (algebraSectionsFunctor U).obj (F.obj k)),
        (algebraSectionsFunctor U).map (c.ι.app k) x =
            (algebraSectionsFunctor U).map (c.ι.app k) y →
          ∃ (l : K) (f : k ⟶ l),
            (F ⋙ algebraSectionsFunctor U).map f x = (F ⋙ algebraSectionsFunctor U).map f y) :
    Nonempty (IsColimit c) :=
  let := IsFiltered.isConnected (C := K)
  nonempty_isColimit_of_affineOpens c fun U hU =>
    ⟨isColimitOfJointlySurjective _ (hsurj U hU) (hinj U hU)⟩

end Stacks.QcohAlgebraFPColimit
