module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveAutomorphismDerivationsAlgebraic
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesIsAlgebraic

/-!
# Stacks 0E6G: the DM locus of `Curves` at a field point and the derivations of `𝒪_X`

Let `X` be a proper scheme of dimension at most one over a field `k`, and `x : Spec k → Curves`
the point of the algebraic stack of curves classifying it. Stacks 0DSW, part (3), lists three
conditions on `X`:
* (a) `x` factors through `Curves^DM`, the maximal open substack of `Curves` which is DM
  (Stacks 0DSW, part (1); in Lean `Stack.dmLocus`, the supremum of the DM open substacks, which
  is the largest one by Stacks 0DSM);
* (b) `Aut(X)` is geometrically reduced over `k` and has dimension `0`;
* (c) `Aut(X) → Spec k` is unramified.
Stacks 0E6G says that these are equivalent to `Der_k(𝒪_X, 𝒪_X) = 0`.

Here `Aut(X)` is the automorphism group algebraic space of the point `x`
(`Stack.automorphismGroupSpaceOverField`), the fibre of the inertia of `Curves` over `x`; it is
an algebraic space because the diagonal of an algebraic stack is representable by algebraic
spaces. The algebraicity of `Curves` is Stacks 0D5A,
`AlgebraicGeometry.curvesFiberedCategory_isAlgebraicStack`.

## Main results

* `AlgebraicGeometry.curvesSmall.tfae_curvesDMLocus_unramified_derivations`: Stacks 0E6G.

## References

* [Stacks Project, Tag 0E6G](https://stacks.math.columbia.edu/tag/0E6G)
* [Stacks Project, Tag 0DSW](https://stacks.math.columbia.edu/tag/0DSW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.curvesSmall

open Deformation Deformation.Examples

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}
variable {k : Type u} [Field k] (X : Over (Spec (.of k))) [IsProper X.hom]
  (hk : B.Contains (Spec (.of k))) (hdim : topologicalKrullDim X.left ≤ 1)

/-- Let `X` be a proper scheme of dimension at most one over a field `k`, and `x : Spec k → Curves`
the point of the algebraic stack of curves classifying it. The following are equivalent:
1. (Stacks 0DSW (3)(a)) `x` factors through `Curves^DM`, the maximal DM open substack;
2. (Stacks 0DSW (3)(b)) `Aut(X)` is geometrically reduced over `k` and has dimension `0`;
3. (Stacks 0DSW (3)(c)) `Aut(X) → Spec k` is unramified;
4. `Der_k(𝒪_X, 𝒪_X) = 0`, i.e. the type of `k`-derivations of `𝒪_X` into `𝒪_X` is a
   subsingleton (it has the zero derivation). -/
@[stacks 0E6G]
theorem tfae_curvesDMLocus_unramified_derivations :
    List.TFAE
      [Stack.dmLocus B integerBase hZ B.contains_terminal
          (curvesAlgebraicStack B hZ (curvesFiberedCategory_isAlgebraicStack.{u, w} B hZ))
          (curveFieldPoint X hk hdim (curvesFiberedCategory_isAlgebraicStack B hZ)).obj,
        Space.IsGeometricallyReduced k B hk
            (Stack.automorphismGroupSpaceOverField B integerBase hZ _
              (curveFieldPoint X hk hdim (curvesFiberedCategory_isAlgebraicStack.{u, w} B hZ)))
            (Stack.isAlgebraicSpace_automorphismGroupSpaceOverField B integerBase hZ _
              (curveFieldPoint X hk hdim (curvesFiberedCategory_isAlgebraicStack B hZ))) ∧
          Space.dimension B (Spec (.of k)) hk
            (Stack.automorphismGroupSpaceOverField B integerBase hZ _
              (curveFieldPoint X hk hdim (curvesFiberedCategory_isAlgebraicStack.{u, w} B hZ)))
            (Stack.isAlgebraicSpace_automorphismGroupSpaceOverField B integerBase hZ _
              (curveFieldPoint X hk hdim (curvesFiberedCategory_isAlgebraicStack B hZ))) = 0,
        Stack.IsUnramifiedAutomorphismGroupSpace B integerBase hZ
          (curvesAlgebraicStack B hZ (curvesFiberedCategory_isAlgebraicStack.{u, w} B hZ))
          (curveFieldPoint X hk hdim (curvesFiberedCategory_isAlgebraicStack B hZ)),
        Subsingleton (schemeMorphismDerivations (Λ := k) (k := k) (𝟙 X.left) X.hom)] :=
  tfae_dmLocus_curveFieldPoint_subsingleton_derivations_of_curvesAlgebraic X hk hdim
    (curvesFiberedCategory_isAlgebraicStack B hZ)

end AlgebraicGeometry.curvesSmall

end
