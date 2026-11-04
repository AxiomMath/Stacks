module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.OverField.Representable
public import StacksFrontier.AlgebraicGeometry.Stacks.AutomorphismGroupGroundFieldExtension
public import StacksFrontier.AlgebraicGeometry.Stacks.IntegralAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.InertiaProjectionFiniteType
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAbsoluteDMEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalSeparatednessRelativeInertia
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.AutomorphismGroupFibre
public import StacksFrontier.AlgebraicGeometry.Stacks.IsomPresheafFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparatedSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.LocallySeparated

/-!
# The automorphism group algebraic space of a point is often a scheme (Stacks 0DTS)

Let `𝒳` be an algebraic stack over `S` and let `x : Spec k ⟶ 𝒳` be a field-valued point, with
automorphism group algebraic space `G_x = Isom_𝒳(x, x)` over `Spec k`
(`AlgebraicGeometry.Stack.pointAutomorphismSpace`, the setting of Stacks 0DTR). **Stacks 0DTS**
says that `G_x` is a scheme as soon as one of the following holds:

1. `Δ : 𝒳 ⟶ 𝒳 × 𝒳` is quasi-separated,
2. `Δ : 𝒳 ⟶ 𝒳 × 𝒳` is locally separated,
3. `𝒳` is quasi-DM,
4. `I_𝒳 ⟶ 𝒳` is quasi-separated,
5. `I_𝒳 ⟶ 𝒳` is locally separated, or
6. `I_𝒳 ⟶ 𝒳` is locally quasi-finite.

## Main results

* `AlgebraicGeometry.Stack.isRepresentable_pointAutomorphismSpace`: **Stacks 0DTS**.

## Implementation notes

`G_x` is the base change of `Δ` along `(x, x)` and of `I_𝒳 ⟶ 𝒳` along `x`, so each of the six
conditions makes `G_x` quasi-separated, locally separated or locally quasi-finite over `k`
(`StacksFrontier.AlgebraicGeometry.Stacks.AutomorphismGroupFibre`). A quasi-separated or locally
separated algebraic space is decent (Stacks 03I7, Stacks 088J), and so is an algebraic space
locally quasi-finite over a field
(`AlgebraicGeometry.Space.isDecentSpace_of_isLocallyQuasiFinite`). Since `G_x` is locally of
finite type over `k` (Stacks 04XR) and is a group algebraic space over `k` (Stacks 04YP), it is a
scheme by
`AlgebraicGeometry.Space.GroupOverField.isRepresentable_of_isDecentSpace_of_isLocallyOfFiniteType`.
The source instead proves cases (4) and (5) through Stacks 08BH and Stacks 0B8G, and case (6)
through Stacks 06S0; the result used here covers all six at once, the decent case of Stacks
0B8G being only needed for group algebraic spaces locally of finite type, which `G_x` is.

## References

* [Stacks Project, Tag 0DTR](https://stacks.math.columbia.edu/tag/0DTR)
* [Stacks Project, Tag 0DTS](https://stacks.math.columbia.edu/tag/0DTS)
* [Stacks Project, Tag 0B8G](https://stacks.math.columbia.edu/tag/0B8G)
* [Stacks Project, Tag 04XR](https://stacks.math.columbia.edu/tag/04XR)
* [Stacks Project, Tag 04YP](https://stacks.math.columbia.edu/tag/04YP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0DTS.** Let `𝒳` be an algebraic stack over `S` and let `x : Spec k ⟶ 𝒳` be a
field-valued point with automorphism group algebraic space `G_x = Isom_𝒳(x, x)` over `Spec k`.
Then `G_x` is a scheme if one of the following holds: the diagonal `Δ : 𝒳 ⟶ 𝒳 × 𝒳` is
quasi-separated, `Δ` is locally separated, `𝒳` is quasi-DM, the inertia projection
`I_𝒳 ⟶ 𝒳` is quasi-separated, `I_𝒳 ⟶ 𝒳` is locally separated, or `I_𝒳 ⟶ 𝒳` is locally
quasi-finite.

Products are over `S` (Properties of Stacks, Section 04XA), the properties of `Δ` and of
`I_𝒳 ⟶ 𝒳` are taken in the sense of Properties of Stacks, Section 04XB, quasi-DM is the absolute
notion of Stacks 050D (over `Spec ℤ`), and "is a scheme" is representability of the presheaf
`G_x` on the big fppf site of `Spec k`. -/
@[stacks 0DTS "the automorphism group algebraic space of a field-valued point is a scheme under \
any of the six conditions"]
theorem isRepresentable_pointAutomorphismSpace (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (x : FieldValuedPoint B S hS 𝒳.val.val)
    (h : IsQuasiSeparated B S hS (diagonal.{u, u, u + 1} B S hS 𝒳.val) ∨
      IsLocallySeparated B S hS (diagonal.{u, u, u + 1} B S hS 𝒳.val) ∨
      AlgebraicStacks.IsAbsolutelyQuasiDM B S hS B.contains_terminal 𝒳 ∨
      IsQuasiSeparated B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳).hom ∨
      IsLocallySeparated B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳).hom ∨
      IsLocallyQuasiFinite B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳).hom) :
    (pointAutomorphismSpace B S hS 𝒳.val x).IsRepresentable := by
  let U := x.base
  let y : 𝒳.val.val.p.Fiber U := Functor.Fiber.mk x.over
  let F := isomSpace B S hS 𝒳.val U y y
  have hF : IsAlgebraicSpace B U.left.1 U.left.2 F :=
    isAlgebraicSpace_isomSpace B S hS 𝒳.val 𝒳.property U y y
  have hlft : Space.IsLocallyOfFiniteType B U.left.1 U.left.2
      ((Space.isTerminal_yoneda_obj_base B U.left.1 U.left.2).from F) :=
    Space.holdsOnEveryEtaleChart_of_isTerminal B U.left.1 U.left.2 terminalIsTerminal
      (Space.isTerminal_yoneda_obj_base B U.left.1 U.left.2) _ _
      (isLocallyOfFiniteType_isomPresheaf B S hS 𝒳.val 𝒳.property U y y)
  have hqs (h : Space.IsQuasiSeparatedOver B U.left.1 U.left.2 F) :
      Space.IsDecentSpace B U.left.1 U.left.2 F :=
    Space.isDecentSpace_of_isZariskiLocallyQuasiSeparatedOver B _ _ B.contains_terminal F hF
      (Space.isZariskiLocallyQuasiSeparatedOver_of_isQuasiSeparatedOver B _ _ hF h)
  have hdec : Space.IsDecentSpace B U.left.1 U.left.2 F := by
    rcases h with h | h | h | h | h | h
    · exact hqs (isQuasiSeparatedOver_isomSpace_of_diagonal B S hS 𝒳 U y h)
    · exact Space.isDecentSpace_of_isLocallySeparatedOver B _ _ hF
        (isLocallySeparatedOver_isomSpace_of_diagonal B S hS 𝒳 U y h)
    · exact Space.isDecentSpace_of_isLocallyQuasiFinite B _ _ x.isSpec hF
        (isLocallyQuasiFinite_isomSpace_of_isAbsolutelyQuasiDM B S hS 𝒳 U y h)
    · exact hqs (isQuasiSeparatedOver_isomSpace_of_inertiaProjection B S hS 𝒳 U y h)
    · exact Space.isDecentSpace_of_isLocallySeparatedOver B _ _ hF
        (isLocallySeparatedOver_isomSpace_of_inertiaProjection B S hS 𝒳 U y h)
    · exact Space.isDecentSpace_of_isLocallyQuasiFinite B _ _ x.isSpec hF
        (isLocallyQuasiFinite_isomSpace_of_inertiaProjection B S hS 𝒳 U y h)
  exact Space.GroupOverField.isRepresentable_of_isDecentSpace_of_isLocallyOfFiniteType
    (automorphismGroupSpace B S hS 𝒳.val 𝒳.property U y) x.isSpec hdec hlft

end AlgebraicGeometry.Stack
