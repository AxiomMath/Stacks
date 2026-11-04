module
public import Mathlib.CategoryTheory.Sites.Point.Conservative
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

/-!
# Finite limits of sheaves are detected on the stalks

Let `(C, J)` be a site and let `{p_i}` be a *conservative* family of points, that is, a family of
points of the site whose fibre functors on sheaves of sets jointly reflect isomorphisms
(Stacks 00YK; `CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints`). Then "exactness" of
sheaves may be checked stalkwise: for a finite diagram `G : K ⥤ Sh(C)` of sheaves, a cone
`(F, q_j)` over `G` is a limit if and only if the cone of stalks `(F_{p_i}, (q_j)_{p_i})` is a
limit for every `i`.

Both directions come from the left exactness of a stalk functor `F ↦ F_{p_i}`: it is a filtered
colimit of evaluations, hence commutes with finite limits. Given preservation, a family of functors
which jointly reflects isomorphisms also reflects those limits that exist, by comparison with the
actual limit (`CategoryTheory.JointlyReflectIsomorphisms.jointlyReflectsLimit`). Applied to kernels
this is half of the statement that a sequence of abelian sheaves is exact if and only if it is
exact on all stalks (Stacks 05V3).

The companion statement for colimits holds for an *arbitrary* shape, a stalk functor being a left
adjoint, and so has different hypotheses; it is stated separately.

## Main results

* `CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.nonempty_isLimit_iff`:
  Stacks 00YL (4) — a conservative family of points reflects, and preserves, the limit of a finite
  diagram of sheaves.

## Implementation notes

* Parts (1), (2) and (3) of the source's lemma — injectivity, surjectivity and equality of maps of
  sheaves are detected on the stalks — are already available, as Mathlib's
  `CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.jointlyReflectMonomorphisms`,
  `…jointlyReflectEpimorphisms` and `…jointlyFaithful`, each carrying the corresponding part of
  this tag: an injection of sheaves is a monomorphism and a surjection is an epimorphism
  (Stacks 00WN), and (3) is joint faithfulness of the fibre functors. A tag may be realized by
  several declarations, and this file adds part (4).
* Parts (4) and (5) are not one conjunction, because they do not hold under the same hypotheses and
  a conjunction would force each half to carry the other's. A stalk functor is only *left* exact,
  so (4) needs the shape `K` to be finite and needs `Limits.HasFiniteLimits A` and
  `AB5OfSize.{w, w} A` — exactly the hypotheses of part (1). It is a *left adjoint*, so (5) holds
  for an arbitrary shape and needs instead `Limits.HasProducts.{w} A`, for the skyscraper sheaf
  functor it is adjoint to.
* No hypothesis on the shape beyond finiteness is needed: `Limits.HasFiniteLimits A` already gives
  `Limits.HasFiniteLimits (Sheaf J A)`, so the limit the two sides are compared with exists.
* "Is a limit" is spelled `Nonempty (Limits.IsLimit c)` rather than `Limits.IsLimit c`, because
  `IsLimit` is data and the source's assertion is an equivalence of propositions. Nothing is lost:
  `IsLimit c` is a subsingleton, and `Nonempty (IsLimit c)` is the form Mathlib itself uses for the
  proposition "this cone is a limit", both in a hypothesis (`Limits.ReflectsLimit.reflects`) and in
  a characterization (`CategoryTheory.Limits.Types.isLimit_iff`, whose name this one mutates).
* The cone is a parameter, so that the statement is the equivalence asserted of the one cone the
  source names, and the maps the source writes as `(q_j)_{p_i}` are thereby pinned: they are the
  image of `c` under the stalk functor, `(Φ.obj.sheafFiber).mapCone c`.
* The coefficients are a general category `A` rather than only `Type w` (the source's `Sh(C)` is
  sheaves of sets), matching parts (1)–(3), which Mathlib states for `A`; hence the
  concrete-category assumptions on `A` under which conservativity at `Type w` transfers to
  `A`-valued sheaves (`…IsConservativeFamilyOfPoints.jointlyReflectIsomorphisms`). Taking
  `A := Type w` recovers the source's statement for sheaves of sets, where only
  `LocallySmall.{w} C` remains.
* The category `A` is implicit, being determined by the diagram, whereas in parts (1)–(3) it is
  explicit for want of anything to determine it. The shape `K` is allowed to live in any universe,
  which is free: both `Limits.hasLimitsOfShape_of_hasFiniteLimits` and
  `Limits.preservesLimitsOfShapeOfPreservesFiniteLimits` are stated for a finite category in an
  arbitrary universe.

## References

* [Stacks 00YL](https://stacks.math.columbia.edu/tag/00YL)
  (`sites-lemma-check-exactness-stalks`), in the section "Sites with enough points" (Stacks 00YJ);
  the definition of a conservative family is Stacks 00YK, injections and surjections of sheaves are
  Stacks 00WN, and the application to abelian sheaves is Stacks 05V3.
* [SGA4], Exposé IV, 6.
-/

namespace CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints

section

universe w v' v u'' u' u
open CategoryTheory Limits

namespace Stacks.SitePoints.StalkwiseLimits

private theorem nonempty_isLimit_iff_proof {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {P : ObjectProperty (GrothendieckTopology.Point.{w} J)}
    (hP : P.IsConservativeFamilyOfPoints) {A : Type u'} [Category.{v'} A] [LocallySmall.{w} C]
    [HasColimitsOfSize.{w, w} A] [HasFiniteLimits A] [AB5OfSize.{w, w} A]
    {FC : A → A → Type*} {CC : A → Type w}
    [∀ X Y : A, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{w} A FC]
    [(forget A).ReflectsIsomorphisms] [PreservesFilteredColimitsOfSize.{w, w} (forget A)]
    [J.HasSheafCompose (forget A)]
    {K : Type u''} [SmallCategory K] [FinCategory K] {G : K ⥤ Sheaf J A} (c : Cone G) :
    Nonempty (IsLimit c) ↔
      ∀ Φ : P.FullSubcategory, Nonempty (IsLimit ((Φ.obj.sheafFiber (A := A)).mapCone c)) :=
  ⟨fun ⟨hc⟩ _Φ ↦ ⟨isLimitOfPreserves _ hc⟩,
    fun h ↦ ⟨(hP.jointlyReflectIsomorphisms A).jointlyReflectsLimit fun Φ ↦ (h Φ).some⟩⟩

end Stacks.SitePoints.StalkwiseLimits

@[expose] public section

open Stacks.SitePoints.StalkwiseLimits in
/-- **Stacks 00YL (4).** Let `(C, J)` be a site and let `P` be a conservative family of points of
it. Let `G : K ⥤ Sh(C)` be a finite diagram of sheaves with values in `A`. Then a cone over `G` is
a limit if and only if its image under every stalk functor `F ↦ F_{p_i}`, `p_i ∈ P`, is a limit. -/
@[stacks 00YL "(4): a cone over a finite diagram of sheaves is a limit if and only if it is one in
  every stalk at a conservative family of points."]
public theorem nonempty_isLimit_iff {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {P : ObjectProperty (GrothendieckTopology.Point.{w} J)}
    (hP : P.IsConservativeFamilyOfPoints) {A : Type u'} [Category.{v'} A] [LocallySmall.{w} C]
    [HasColimitsOfSize.{w, w} A] [HasFiniteLimits A] [AB5OfSize.{w, w} A]
    {FC : A → A → Type*} {CC : A → Type w}
    [∀ X Y : A, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{w} A FC]
    [(forget A).ReflectsIsomorphisms] [PreservesFilteredColimitsOfSize.{w, w} (forget A)]
    [J.HasSheafCompose (forget A)]
    {K : Type u''} [SmallCategory K] [FinCategory K] {G : K ⥤ Sheaf J A} (c : Cone G) :
    Nonempty (IsLimit c) ↔
      ∀ Φ : P.FullSubcategory, Nonempty (IsLimit ((Φ.obj.sheafFiber (A := A)).mapCone c)) := by
  apply Stacks.SitePoints.StalkwiseLimits.nonempty_isLimit_iff_proof ; assumption
end

end

end CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints
