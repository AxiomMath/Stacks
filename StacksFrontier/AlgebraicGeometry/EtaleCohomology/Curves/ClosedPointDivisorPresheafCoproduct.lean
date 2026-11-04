module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointDivisorSheaf
public import StacksFrontier.CategoryTheory.Sites.SigmaPresheafComparison

/-!
# Mapping into the sheaf `⨁_x i_{x,*} ℤ`

The third term of the divisor sequence of Stacks 03RM on a curve `X`,
`0 → 𝐆_{m,X} → j_* 𝐆_{m,K} → ⨁_x i_{x,*} ℤ → 0`,
is the coproduct `Stacks.EtaleCohomology.closedPointDivisorSheaf` of the skyscraper sheaves over
the closed points. The sequence's second map goes *into* that coproduct, and a coproduct of
sheaves has a universal property only for morphisms *out* of it: it is the sheafification of the
coproduct of the underlying presheaves, so a section of it over an étale `X`-scheme is only
locally a finite sum of sections of the summands, and a morphism into it is not assembled from a
family of morphisms into the summands.

What does assemble it is the coproduct of the underlying *presheaves*, which does have a
universal property for morphisms out of it. This file forms that presheaf coproduct over the
closed points — a question of reachability, exactly as for the sheaf coproduct, since the index
type is a `Type u` while the coefficient universe is `max (u + 1) v` — and specialises
`CategoryTheory.Sheaf.sigmaHomOfPresheafHom` to it: a morphism of presheaves into the presheaf
coproduct is a morphism of sheaves into `⨁_x i_{x,*} ℤ`.

The datum this asks of the second map of the divisor sequence is therefore a section of the
presheaf coproduct over each étale `X`-scheme — a family of orders of vanishing with finite
support — natural in the scheme, and nothing about sheafification.

## Main definitions

* `Stacks.EtaleCohomology.closedPointDivisorSheaf.fromPresheafCoproduct`: the comparison morphism
  from the coproduct of the underlying presheaves of the skyscrapers to the underlying presheaf
  of `⨁_x i_{x,*} ℤ`.
* `Stacks.EtaleCohomology.closedPointDivisorSheaf.homOfPresheafHom`: **the morphism into
  `⨁_x i_{x,*} ℤ` determined by a morphism of presheaves into the coproduct of the underlying
  presheaves of the skyscrapers.**

## Main results

* `Stacks.EtaleCohomology.hasCoproduct_closedPointSkyscraper_obj`: the presheaf coproduct exists.
* `Stacks.EtaleCohomology.closedPointDivisorSheaf.ι_fromPresheafCoproduct` and
  `Stacks.EtaleCohomology.closedPointDivisorSheaf.homOfPresheafHom_ι`: the comparison morphism
  and the construction are compatible with the summand inclusions.

## Implementation notes

Both coproducts are supplied as local instances at a high priority, as in
`Stacks.EtaleCohomology.closedPointDivisorSheaf`: the coefficient universe `max (u + 1) v` is not
determined by the arguments of either, so global instances would make the unifier stick. The
presheaf one is obtained from `CategoryTheory.Limits.functorCategoryHasColimitsOfShape` with
colimits in the coefficient category discharged by hand, for the same reason the sheaf one is
written down in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sheafification.SmallEtaleColimits`: instance
search does not reach the conclusion.

## References

* [Stacks Project, Tag 03RM](https://stacks.math.columbia.edu/tag/03RM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

variable (X : Scheme.{u})

/-- **The coproduct over the closed points of `X` of the underlying presheaves of the skyscraper
sheaves `i_{x,*} ℤ` exists.**

Colimits in a category of presheaves are computed in the coefficient category, where the shape —
the closed points of `X`, a `Type u` — is small in the coefficient universe `max (u + 1) v`. As
with the coproduct of the sheaves themselves, instance search does not reach this conclusion, so
it is written down. -/
theorem hasCoproduct_closedPointSkyscraper_obj :
    HasCoproduct (fun x : closedPoints X ↦ (closedPointSkyscraper.{u, v} X x).obj) :=
  let : HasColimitsOfShape (Discrete ↥(closedPoints X)) AddCommGrpCat.{max (u + 1) v} :=
    AddCommGrpCat.hasColimitsOfShape
  (functorCategoryHasColimitsOfShape (J := Discrete ↥(closedPoints X))
    (K := X.Etaleᵒᵖ) (C := AddCommGrpCat.{max (u + 1) v})).has_colimit _

attribute [local instance 10000] hasCoproduct_closedPointSkyscraper
  hasCoproduct_closedPointSkyscraper_obj

namespace closedPointDivisorSheaf

/-- **The comparison morphism from the coproduct of the underlying presheaves of the skyscrapers
to the underlying presheaf of `⨁_x i_{x,*} ℤ`.** -/
def fromPresheafCoproduct :
    (∐ fun x : closedPoints X ↦ (closedPointSkyscraper.{u, v} X x).obj) ⟶
      (closedPointDivisorSheaf.{u, v} X).obj :=
  Sheaf.sigmaPresheafComparison (closedPointSkyscraper.{u, v} X)

/-- The comparison morphism restricts on the summand at a closed point to the underlying presheaf
morphism of the inclusion of that summand. -/
@[simp]
theorem ι_fromPresheafCoproduct (x : closedPoints X) :
    Sigma.ι (fun x : closedPoints X ↦ (closedPointSkyscraper.{u, v} X x).obj) x ≫
        fromPresheafCoproduct.{u, v} X =
      (ι.{u, v} X x).hom :=
  Sheaf.ι_sigmaPresheafComparison (closedPointSkyscraper.{u, v} X) x

variable {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}

/-- **The morphism into `⨁_x i_{x,*} ℤ` determined by a morphism of presheaves into the coproduct
of the underlying presheaves of the skyscrapers.** -/
def homOfPresheafHom
    (φ : F.obj ⟶ ∐ fun x : closedPoints X ↦ (closedPointSkyscraper.{u, v} X x).obj) :
    F ⟶ closedPointDivisorSheaf.{u, v} X :=
  Sheaf.sigmaHomOfPresheafHom (closedPointSkyscraper.{u, v} X) φ

/-- The underlying presheaf morphism of `homOfPresheafHom X φ` is `φ` followed by the comparison
morphism `fromPresheafCoproduct X`. -/
@[simp]
theorem homOfPresheafHom_hom
    (φ : F.obj ⟶ ∐ fun x : closedPoints X ↦ (closedPointSkyscraper.{u, v} X x).obj) :
    (homOfPresheafHom.{u, v} X φ).hom = φ ≫ fromPresheafCoproduct.{u, v} X :=
  rfl

/-- **The construction extends the summand inclusions**: a presheaf morphism factoring through the
summand at a closed point, by the underlying presheaf morphism of a morphism of sheaves,
determines that morphism followed by the inclusion of that summand. -/
theorem homOfPresheafHom_ι (x : closedPoints X) (ψ : F ⟶ closedPointSkyscraper.{u, v} X x) :
    homOfPresheafHom.{u, v} X (ψ.hom ≫
        Sigma.ι (fun x : closedPoints X ↦ (closedPointSkyscraper.{u, v} X x).obj) x) =
      ψ ≫ ι.{u, v} X x :=
  Sheaf.sigmaHomOfPresheafHom_ι (closedPointSkyscraper.{u, v} X) x ψ

end closedPointDivisorSheaf

end Stacks.EtaleCohomology

end
