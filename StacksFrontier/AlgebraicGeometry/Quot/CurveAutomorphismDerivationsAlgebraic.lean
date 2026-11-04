module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveAutomorphismDerivations
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmallIsom

/-!
# Stacks 0E6G at the algebraic stack of curves, from its algebraicity alone

`curvesSmall.tfae_dmLocus_curveFieldPoint_subsingleton_derivations_of_isAlgebraicStack` takes
`hIsomSep`, the separatedness of the isomorphism spaces of the small model of the stack of curves
(the separation step of Stacks 0DSQ). That is
`curvesSmall.isSeparated_relocalizeToYoneda_isomSpace`; this file applies it.

## Main results

* `curvesSmall.isSeparatedOver_autIsomSpace`: `Aut(X)` is separated over `k`.
* `curvesSmall.tfae_dmLocus_curveFieldPoint_subsingleton_derivations_of_curvesAlgebraic`: the
  equivalences of Stacks 0E6G, given only that `Curves` is algebraic (`h`).

## Implementation notes

Unregistered: the hypothesis `h` is Stacks 0D5A, which is not proved here.

## References

* [Stacks Project, Tag 0E6G](https://stacks.math.columbia.edu/tag/0E6G)
* [Stacks Project, Tag 0DSQ](https://stacks.math.columbia.edu/tag/0DSQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.curvesSmall

open Deformation Deformation.Examples

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}
variable {k : Type u} [Field k] (X : Over (Spec (.of k))) [IsProper X.hom]
  (hk : B.Contains (Spec (.of k))) (hdim : topologicalKrullDim X.left ≤ 1)

/-- **`Aut(X)` is separated over `k`.** For a proper scheme `X` of dimension at most one over a
field `k`, the automorphism functor `Isom(X, X)` of the point of `Curves` classifying `X` is
separated over `Spec k`: the isomorphism spaces of the small model of `Curves` are separated
(`AlgebraicGeometry.curvesSmall.isSeparated_relocalizeToYoneda_isomSpace`, Stacks 0DPN and
0DPP). -/
theorem isSeparatedOver_autIsomSpace :
    Space.IsSeparatedOver B (Spec (.of k)) hk (autIsomSpace (hZ := hZ) X hk hdim) :=
  isSeparatedOver_autIsomSpace_of X hk hdim
    (fun y₁ y₂ => isSeparated_relocalizeToYoneda_isomSpace y₁ y₂)

/-- **Stacks 0E6G, at the algebraic stack of curves, from its algebraicity.** Let `X` be a proper
scheme of dimension at most one over a field `k`, and `x : Spec k → Curves` the point classifying
it, `Curves` being algebraic (`h`, Stacks 0D5A). The following are equivalent:
1. `x` factors through the Deligne–Mumford locus `Curves^DM`;
2. `Aut(X)` is geometrically reduced over `k` and has dimension `0`;
3. `Aut(X) → Spec k` is unramified;
4. `Der_k(𝒪_X, 𝒪_X) = 0`. -/
theorem tfae_dmLocus_curveFieldPoint_subsingleton_derivations_of_curvesAlgebraic
    (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val) :
    List.TFAE
      [Stack.dmLocus B integerBase hZ B.contains_terminal (curvesAlgebraicStack B hZ h)
          (curveFieldPoint X hk hdim h).obj,
        Space.IsGeometricallyReduced k B hk
            (Stack.automorphismGroupSpaceOverField B integerBase hZ _ (curveFieldPoint X hk hdim h))
            (Stack.isAlgebraicSpace_automorphismGroupSpaceOverField B integerBase hZ _
              (curveFieldPoint X hk hdim h)) ∧
          Space.dimension B (Spec (.of k)) hk
            (Stack.automorphismGroupSpaceOverField B integerBase hZ _ (curveFieldPoint X hk hdim h))
            (Stack.isAlgebraicSpace_automorphismGroupSpaceOverField B integerBase hZ _
              (curveFieldPoint X hk hdim h)) = 0,
        Stack.IsUnramifiedAutomorphismGroupSpace B integerBase hZ (curvesAlgebraicStack B hZ h)
          (curveFieldPoint X hk hdim h),
        Subsingleton (schemeMorphismDerivations (Λ := k) (k := k) (𝟙 X.left) X.hom)] :=
  tfae_dmLocus_curveFieldPoint_subsingleton_derivations_of_isAlgebraicStack X hk hdim h
    (fun y₁ y₂ => isSeparated_relocalizeToYoneda_isomSpace y₁ y₂)

end AlgebraicGeometry.curvesSmall

end
