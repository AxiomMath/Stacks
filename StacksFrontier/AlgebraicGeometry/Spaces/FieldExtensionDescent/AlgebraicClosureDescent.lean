module

public import StacksFrontier.AlgebraicGeometry.Spaces.FieldExtensionDescent.AlgebraicClosureSite
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldExtensionDescent.FactorizationDescent

/-!
# Descending from the algebraic closure of the ground field

The reduction to an algebraically closed field in the proof of [Stacks, Tag 0AEM] is carried out
over the algebraic closure `k̄` of the given field `k`, and the source says "details omitted" for
the passage back. This file assembles the pieces for that passage: the spectrum of `k̄` lies in
the big fppf site, so base change to `k̄` is defined; and a morphism constructed over `k̄` which
is pinned down by an equation — a factorization through a morphism with a section — comes from a
morphism over `k`.

## Main results

* `AlgebraicGeometry.Space.eq_of_relocalizeRestrict_algebraicClosure_eq`: two morphisms of
  algebraic spaces over `k` out of a reduced space into one separated over the base which agree
  after base change to `k̄` are equal.
* `AlgebraicGeometry.Space.exists_factorization_of_relocalizeRestrict_algebraicClosure`:
  **a factorization through a morphism with a section constructed over `k̄` descends to `k`**,
  by a unique morphism, which base changes to the given one.

## Implementation notes

Nothing here is special to the algebraic closure: the two statements are the general ones of
`StacksFrontier/AlgebraicGeometry/Spaces/FieldExtensionDescent/MorphismDescent.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/FieldExtensionDescent/FactorizationDescent.lean`,
specialized to `AlgebraicGeometry.Space.algebraicClosureMap`. The one thing that has to be
checked before the specialization can be stated is the containment of `Spec k̄` in the site,
`AlgebraicGeometry.BigFppfSite.contains_spec_algebraicClosure`.

In particular neither statement asks the extension to be finite, flat in any site-theoretic
sense, or a covering: `Spec k̄ ⟶ Spec k` is not a covering of the big fppf site unless `k̄/k` is
finite, and the descent here does not go through a sheaf condition. See the implementation notes
of `StacksFrontier/AlgebraicGeometry/Spaces/FieldExtensionDescent/MorphismDescent.lean`.

## References

* [Stacks Project, Tag 0AEM](https://stacks.math.columbia.edu/tag/0AEM)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))

/-- **Two morphisms agreeing after base change to the algebraic closure are equal.** Let
`a, b : X ⟶ Y` be morphisms of algebraic spaces over a field `k` with `X` reduced and `Y`
separated over `T` along `q`. If the base changes of `a` and `b` to the algebraic closure of `k`
agree, then `a = b`. -/
theorem eq_of_relocalizeRestrict_algebraicClosure_eq
    {T X Y : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u}
    (hT : IsAlgebraicSpace B (Spec (.of k)) hk T)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (hY : IsAlgebraicSpace B (Spec (.of k)) hk Y)
    (hXred : HasEtaleLocalProperty B (Spec (.of k)) hk X
      (fun W : Scheme.{u} => IsReduced W))
    (q : Y ⟶ T) (hq : IsSeparated B (Spec (.of k)) hk q)
    (a b : X ⟶ Y) (hab : a ≫ q = b ≫ q)
    (h : (OverShriek.relocalizeRestrict (algebraicClosureMap B k hk)).map a =
      (OverShriek.relocalizeRestrict (algebraicClosureMap B k hk)).map b) :
    a = b :=
  eq_of_relocalizeRestrict_map_eq B k (AlgebraicClosure k) hk
    (B.contains_spec_algebraicClosure k hk) (algebraicClosureMap B k hk)
    hT hX hY hXred q hq a b hab h

/-- **A factorization constructed over the algebraic closure descends.** Let `p : X ⟶ Y` be a
morphism of algebraic spaces over a field `k` with a section `s`, let `X` be reduced, and let
`f : X ⟶ Z` be a morphism to an algebraic space separated over a terminal presheaf. If the base
change of `f` to the algebraic closure of `k` factors through the base change of `p`, then `f`
factors through `p` over `k`, by a unique morphism, and that morphism base changes to the given
second factor.

This is the step the proof of [Stacks, Tag 0AEM] leaves as "details omitted": the contraction
process is run over an algebraically closed field, where rational points are available, and the
factorization it produces through a coordinate projection is then descended. A coordinate
projection of a finite power has a section as soon as the factor has a rational point, which the
projective line does. -/
theorem exists_factorization_of_relocalizeRestrict_algebraicClosure
    {T X Y Z : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u}
    (hTterm : IsTerminal T)
    (hT : IsAlgebraicSpace B (Spec (.of k)) hk T)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (hZ : IsAlgebraicSpace B (Spec (.of k)) hk Z)
    (hXred : HasEtaleLocalProperty B (Spec (.of k)) hk X
      (fun W : Scheme.{u} => IsReduced W))
    (qZ : Z ⟶ T) (hqZ : IsSeparated B (Spec (.of k)) hk qZ)
    (p : X ⟶ Y) (s : Y ⟶ X) (hsp : s ≫ p = 𝟙 Y) (f : X ⟶ Z)
    (u : (OverShriek.relocalizeRestrict (algebraicClosureMap B k hk)).obj Y ⟶
      (OverShriek.relocalizeRestrict (algebraicClosureMap B k hk)).obj Z)
    (hfac : (OverShriek.relocalizeRestrict (algebraicClosureMap B k hk)).map f =
      (OverShriek.relocalizeRestrict (algebraicClosureMap B k hk)).map p ≫ u) :
    ∃ v : Y ⟶ Z, f = p ≫ v ∧
      (OverShriek.relocalizeRestrict (algebraicClosureMap B k hk)).map v = u ∧
      ∀ w : Y ⟶ Z, f = p ≫ w → w = v :=
  exists_factorization_of_relocalizeRestrict_factorization B k (AlgebraicClosure k) hk
    (B.contains_spec_algebraicClosure k hk) (algebraicClosureMap B k hk)
    hTterm hT hX hZ hXred qZ hqZ p s hsp f u hfac

end AlgebraicGeometry.Space

end
