module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactFieldValuedPoint

/-!
# Finite type points of an algebraic stack (Stacks 06FY)

A point of an algebraic stack `𝒳` over `S` is a *finite type point* when it is represented by a
field-valued point whose 1-morphism `Spec k → 𝒳` is locally of finite type, and
`AlgebraicGeometry.Stack.finiteTypePoints` is the set `𝒳_{ft-pts}` of such points.

This is the first of the two equivalent conditions of Stacks 06FX, which is what the source's
definition refers to. The second condition — a closed point of a scheme carrying a smooth
1-morphism to `𝒳`, which the point is the image of — mentions the point topology of Stacks 04XL
and the identification of the points of a represented algebraic stack with the points of its
scheme, where the first condition mentions only the points of Stacks 04XG and the 1-morphism of
Stacks 050T that a field-valued point determines. The equivalence of the two is Stacks 06FX and
is not available here.

## Main definitions

* `AlgebraicGeometry.Stack.IsFiniteTypePoint`: a point of an algebraic stack is of finite type.
* `AlgebraicGeometry.Stack.finiteTypePoints`: the set of finite type points.

## Main results

There are no results beyond the definitions.

## Implementation notes

A point of `𝒳` is an equivalence class of field-valued points (Stacks 04XG), and the condition is
stated existentially over the representatives of the class. So it is a condition on the class by
construction, and the independence of the chosen representative — which for a condition imposed
on *one* representative would be a theorem about the stack — is not needed and is not stated. The
shape is the one `AlgebraicGeometry.Stack.IsQuasiCompactFieldValuedPoint` of Stacks 0GW1 takes for
quasi-compactness, read through `AlgebraicGeometry.Stack.fieldValuedPointStackMorphism`, which
places that 1-morphism in the 2-category of algebraic stacks over `S` and so makes
`AlgebraicGeometry.Stack.AlgebraicStacks.IsLocallyOfFiniteType` of Stacks 06FS applicable to it.

The two declarations carry the two keys of Stacks 06FY's two assertions — the predicate and the
set it cuts out — which is how the same definition one level down is registered: Stacks 02J1 sits
on `AlgebraicGeometry.IsFiniteTypePoint` under the key `finite_type_point` and on
`AlgebraicGeometry.Scheme.finiteTypePoints` under `finite_type_points_set`, and both are `abbrev`
there too, so membership of the set and the construction of the predicate need no lemma.

The leaf names repeat those scheme-level ones. A leaf-name search will therefore return two
constants for each, as it does for `AlgebraicGeometry.Space.IsQuasiCompact` against
`AlgebraicGeometry.Stack.IsQuasiCompact`; the namespace is what separates them, and the two
predicates are type-incomparable, the scheme-level one taking a point of a scheme at one universe
and these a point of an algebraic stack at two.

## References

* [Stacks Project, Tag 02J1](https://stacks.math.columbia.edu/tag/02J1)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 06FS](https://stacks.math.columbia.edu/tag/06FS)
* [Stacks Project, Tag 06FX](https://stacks.math.columbia.edu/tag/06FX)
* [Stacks Project, Tag 06FY](https://stacks.math.columbia.edu/tag/06FY)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 06FY.** A point of an algebraic stack `𝒳` over `S` is a *finite type point* when
some field-valued point representing it has a locally-of-finite-type 1-morphism `Spec k → 𝒳`.

This is condition (1) of Stacks 06FX. -/
@[stacks 06FY "finite_type_point"]
abbrev IsFiniteTypePoint (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (x : points B S hS 𝒳.val.val 𝒳.val.property) : Prop :=
  ∃ p : FieldValuedPoint B S hS 𝒳.val.val,
    pointClass B S hS 𝒳.val.val 𝒳.val.property p = x ∧
      AlgebraicStacks.IsLocallyOfFiniteType B S hS
        (fieldValuedPointStackMorphism.{u, w} B S hS 𝒳 p)

/-- **Stacks 06FY.** The set `𝒳_{ft-pts}` of finite type points of an algebraic stack `𝒳`
over `S`. -/
@[stacks 06FY "finite_type_points_set"]
abbrev finiteTypePoints (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    Set (points B S hS 𝒳.val.val 𝒳.val.property) :=
  {x | IsFiniteTypePoint.{u, w} B S hS 𝒳 x}

end AlgebraicGeometry.Stack

end
