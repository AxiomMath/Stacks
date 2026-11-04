module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesDeligneMumford

/-!
# The Deligne–Mumford open substack of the stack of curves

Stacks 0DSW asserts the existence of one open substack `Curves^DM ⊂ Curves` with three
properties: (1) it is the largest open substack which is Deligne–Mumford; (2) a family of curves
`X → S` is classified by a morphism `S → Curves` factoring through it exactly when the group
algebraic space `Aut_S(X)` is unramified over `S`; (3) for `X` proper of dimension `≤ 1` over a
field `k`, the point `Spec k → Curves` classifying `X` factors through it iff `Aut(X)` is
geometrically reduced over `k` of dimension `0`, iff `Aut(X) → Spec k` is unramified.

The whole lemma is stated as one existential,
`AlgebraicGeometry.curvesSmall.exists_deligneMumfordLocus`, at
`AlgebraicGeometry.curvesAlgebraicStack B hZ h`. It takes one hypothesis, `h`: the algebraicity
of the stack of curves (Stacks 0D5A).

For a field-valued point `x` of `Curves`, `Aut(X)` is the automorphism group algebraic space
`G_x = Isom(x, x)` of Stacks 04YP, viewed over the spectrum of the field of `x`. It is identified
with the automorphism functor of the family classified by `x` in
`AlgebraicGeometry.curvesSmall.nonempty_arrowIso_autFunctorProjection`. The objects of `Curves`
over `Spec k` are the proper algebraic spaces of dimension `≤ 1` over `k` (flat and of finite
presentation being automatic over a field). These are schemes by Stacks 0ADD, so (3) is stated for
every field-valued point.

## Main results

* `AlgebraicGeometry.Stack.isLocallyOfFiniteType_automorphismGroupSpace`: `G_y` is locally of
  finite type over the base, for any algebraic stack.
* `AlgebraicGeometry.curvesSmall.tfae_dmLocus_fieldValuedPoint_of_isAlgebraicStack`: Stacks 0DSW
  (3), given `h`.
* `AlgebraicGeometry.curvesSmall.exists_deligneMumfordLocus`: Stacks 0DSW, the whole statement,
  given `h` (Stacks 0D5A).

## References

* [Stacks Project, Tag 0DSW](https://stacks.math.columbia.edu/tag/0DSW)
* [Stacks Project, Tag 0D5A](https://stacks.math.columbia.edu/tag/0D5A)
* [Stacks Project, Tag 04XR](https://stacks.math.columbia.edu/tag/04XR)
* [Stacks Project, Tag 0DSM](https://stacks.math.columbia.edu/tag/0DSM)
* [Stacks Project, Tag 0DSN](https://stacks.math.columbia.edu/tag/0DSN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry

namespace Stack

/-- **The automorphism group algebraic space of an object of an algebraic stack is locally of
finite type over its base.** For an object `y` of an algebraic stack `𝒳` over a scheme `U` of the
site, `G_y = Isom_𝒳(y, y) ⟶ U` is locally of finite type. -/
theorem isLocallyOfFiniteType_automorphismGroupSpace (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (𝒳 : AlgebraicStacks.{u, w} B S hS) (U : BigFppfOver B S hS)
    (y : 𝒳.val.val.p.Fiber U) :
    Space.IsLocallyOfFiniteType B U.left.1 U.left.2
      (automorphismGroupSpace B S hS 𝒳.val 𝒳.property U y).obj.X.hom :=
  (holdsOnEveryEtaleChart_isomSpaceOver_hom_iff B S hS 𝒳 _ U y y).mpr
    (isLocallyOfFiniteType_isomPresheaf B S hS 𝒳.val 𝒳.property U y y)

end Stack

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

namespace curvesSmall

variable (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)

/-- **Stacks 0DSW (3), at the stack of curves, given only its algebraicity.** Let
`x : Spec k → Curves` be a field-valued point, classifying a proper curve `X` over `k`. The
following are equivalent: `x` factors through `Curves^DM`; `Aut(X)` is geometrically reduced over
`k` and has dimension `0`; `Aut(X) → Spec k` is unramified. The only hypothesis is `h`, the
algebraicity of the stack of curves (Stacks 0D5A). -/
theorem tfae_dmLocus_fieldValuedPoint_of_isAlgebraicStack
    (x : Stack.FieldValuedPoint B integerBase hZ (curvesAlgebraicStack B hZ h).val.val) :
    List.TFAE
      [Stack.dmLocus B integerBase hZ B.contains_terminal (curvesAlgebraicStack B hZ h) x.obj,
        Space.IsGeometricallyReduced x.carrier B
            (Stack.contains_spectrum_fieldValuedPoint B integerBase hZ x)
            (Stack.automorphismGroupSpaceOverField B integerBase hZ _ x)
            (Stack.isAlgebraicSpace_automorphismGroupSpaceOverField B integerBase hZ _ x) ∧
          Space.dimension B (Spec (.of x.carrier))
            (Stack.contains_spectrum_fieldValuedPoint B integerBase hZ x)
            (Stack.automorphismGroupSpaceOverField B integerBase hZ _ x)
            (Stack.isAlgebraicSpace_automorphismGroupSpaceOverField B integerBase hZ _ x) = 0,
        Stack.IsUnramifiedAutomorphismGroupSpace B integerBase hZ
          (curvesAlgebraicStack B hZ h) x] :=
  tfae_dmLocus_fieldValuedPoint h x
    (Stack.isLocallyOfFiniteType_automorphismGroupSpace B integerBase hZ _ x.base
      ⟨x.obj, x.over⟩)

/-- **Stacks 0DSW, the whole statement, given the algebraicity of the stack of curves.** There
exists an open substack `Curves^DM ⊂ Curves` such that

1. `Curves^DM` is the maximal open substack of `Curves` which is DM: it is Deligne–Mumford, and
   every Deligne–Mumford open substack of `Curves` is contained in it;
2. for a family of curves `X → S`, the classifying morphism `S → Curves` factors through
   `Curves^DM` if and only if the group algebraic space `Aut_S(X)` is unramified over `S`;
3. for a field-valued point `x : Spec k → Curves`, classifying a proper `X` of dimension `≤ 1`
   over `k`, the following are equivalent: `x` factors through `Curves^DM`; `Aut(X)` is
   geometrically reduced over `k` of dimension `0`; `Aut(X) → Spec k` is unramified.

The only hypothesis is `h`, Stacks 0D5A. -/
theorem exists_deligneMumfordLocus :
    ∃ W : Stack.OpenSubstack (curvesAlgebraicStack B hZ h),
      (Stack.AlgebraicStacks.IsAbsolutelyDM B integerBase hZ B.contains_terminal
          W.toAlgebraicStack ∧
        ∀ V : Stack.OpenSubstack (curvesAlgebraicStack B hZ h),
          Stack.AlgebraicStacks.IsAbsolutelyDM B integerBase hZ B.contains_terminal
              V.toAlgebraicStack →
            V.property ≤ W.property) ∧
      (∀ F : CurveFamily B hZ,
        W.property (ShrinkHoms.toShrinkHoms F) ↔
          Space.IsUnramified B integerBase hZ (CurveFamily.autFunctorProjection F)) ∧
      ∀ x : Stack.FieldValuedPoint B integerBase hZ (curvesAlgebraicStack B hZ h).val.val,
        List.TFAE
          [W.property x.obj,
            Space.IsGeometricallyReduced x.carrier B
                (Stack.contains_spectrum_fieldValuedPoint B integerBase hZ x)
                (Stack.automorphismGroupSpaceOverField B integerBase hZ _ x)
                (Stack.isAlgebraicSpace_automorphismGroupSpaceOverField B integerBase hZ _ x) ∧
              Space.dimension B (Spec (.of x.carrier))
                (Stack.contains_spectrum_fieldValuedPoint B integerBase hZ x)
                (Stack.automorphismGroupSpaceOverField B integerBase hZ _ x)
                (Stack.isAlgebraicSpace_automorphismGroupSpaceOverField B integerBase hZ _ x) = 0,
            Stack.IsUnramifiedAutomorphismGroupSpace B integerBase hZ
              (curvesAlgebraicStack B hZ h) x] := by
  obtain ⟨W, hW, hDM, hmax⟩ := exists_largest_isAbsolutelyDM_openSubstack h
  refine ⟨W, ⟨hDM, hmax⟩, fun F => ?_, fun x => ?_⟩
  · rw [hW]
    exact dmLocus_toShrinkHoms_iff h F
  · rw [hW]
    exact tfae_dmLocus_fieldValuedPoint_of_isAlgebraicStack h x

end curvesSmall

end AlgebraicGeometry

end
