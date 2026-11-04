module

public import StacksFrontier.AlgebraicGeometry.Curves.VectorFieldsGenus
public import StacksFrontier.AlgebraicGeometry.Quot.CurveAutomorphismDerivationsAlgebraic
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliStableCurvesDeligneMumford

/-!
# Stacks 0E7A from the algebraicity of `Curves` and part (2) of Stacks 0E76

Assume the stack of curves `Curves` is algebraic (Stacks 0D5A). At a stable curve `X` over an
algebraically closed field the automorphism group algebraic space is unramified, since the
isomorphism spaces of `Curves` are separated (Stacks 0DSQ) and `X` has no nonzero vector fields
(Stacks 0E69). Consequently the open substacks `𝓜̄_g ⊆ 𝓜̄` of `Curves` are Deligne–Mumford
(Stacks 0E7A), given the implication (a) ⇒ (b) of part (2) of Stacks 0E76 at `𝓜̄`.

## Main results

In the namespace `AlgebraicGeometry.curvesSmall`:

* `isUnramifiedAutomorphismGroupSpace_curveFieldPoint_of_hasGenusTwoNoRationalTailNoRationalBridge`
  asserts that at a stable curve over an algebraically closed field, `Aut(X)` is unramified.
* `le_and_isAbsolutelyDM_and_isDeligneMumfordStack_of_stableFieldPoints` and
  `exists_curvesDM_and_le_and_isDeligneMumfordStack_of_stableFieldPoints`: open substacks
  `𝒱 ⊆ 𝒰` of `Curves` satisfying `hU` are Deligne–Mumford and contained in `Curves^{DM}`
  (Stacks 0E7A).

## Implementation notes

The hypothesis `h` is the algebraicity of `Curves` (Stacks 0D5A), and `hU` is the implication
(a) ⇒ (b) of part (2) of Stacks 0E76, at the open substack `𝒰 = 𝓜̄` of Stacks 0E76.

## References

* [Stacks Project, Tag 0E7A](https://stacks.math.columbia.edu/tag/0E7A)
* [Stacks Project, Tag 0E69](https://stacks.math.columbia.edu/tag/0E69)
* [Stacks Project, Tag 0E6G](https://stacks.math.columbia.edu/tag/0E6G)
* [Stacks Project, Tag 0E76](https://stacks.math.columbia.edu/tag/0E76)
-/

@[expose] public noncomputable section

open CategoryTheory Deformation.Examples

universe w u

namespace Stacks.Curves

/-- **Stacks 0E69, read as the vanishing of the space of vector fields.** For an at-worst-nodal,
proper, connected, one-dimensional scheme `X` over an algebraically closed field `k`, of genus at
least two, with no rational tails and no rational bridges, `Der_k(𝒪_X, 𝒪_X)` is a subsingleton
(`Stacks.Curves.SheafDerivation.eq_zero_of_hasAtWorstNodalSingularities`). -/
theorem subsingleton_sheafDerivation_of_hasAtWorstNodalSingularities (k : Type u) [Field k]
    [IsAlgClosed k] (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (.of k))]
    [AlgebraicGeometry.IsProper (X ↘ AlgebraicGeometry.Spec (.of k))]
    [ConnectedSpace X] (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    (hg : 2 ≤ AlgebraicGeometry.genus (X ↘ AlgebraicGeometry.Spec (.of k)))
    (htail : ∀ C : X.IdealSheafData, ¬ AlgebraicGeometry.IsRationalTail k X C)
    (hbridge : ∀ C : X.IdealSheafData, ¬ AlgebraicGeometry.IsRationalBridge k X C) :
    Subsingleton (SheafDerivation k X) :=
  subsingleton_of_forall_eq 0
    (SheafDerivation.eq_zero_of_hasAtWorstNodalSingularities k X hdim hnodal hg htail hbridge)

end Stacks.Curves

namespace AlgebraicGeometry.curvesSmall

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}
  (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)

/-- **At a stable curve over an algebraically closed field, `Aut(X)` is unramified.** Let
`Curves` be algebraic (`h`, Stacks 0D5A), `k` algebraically closed and `X` proper over `k` of
dimension at most one, at-worst-nodal of dimension one, with `k = H⁰(X, 𝒪_X)`, of genus at least
two and without rational tails or bridges. Then the automorphism group algebraic space of the
point `Spec k → Curves` classifying `X` is unramified (Stacks 0BY5, 0E69, 0E6G). -/
theorem
    isUnramifiedAutomorphismGroupSpace_curveFieldPoint_of_hasGenusTwoNoRationalTailNoRationalBridge
    {k : Type u} [Field k] [IsAlgClosed k] (X : Over (Spec (.of k))) [IsProper X.hom]
    (hk : B.Contains (Spec (.of k))) (hdim : topologicalKrullDim X.left ≤ 1)
    (hnodal : letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
      Stacks.Curves.HasAtWorstNodalSingularities k X.left)
    (hdim1 : topologicalKrullDim X.left = 1)
    (hH0 : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop))
    (hstab : HasGenusTwoNoRationalTailNoRationalBridge k X.hom) :
    Stack.IsUnramifiedAutomorphismGroupSpace B integerBase hZ (curvesAlgebraicStack B hZ h)
      (curveFieldPoint X hk hdim h) :=
  isUnramifiedAutomorphismGroupSpace_curveFieldPoint_of_stable h
    isSeparated_relocalizeToYoneda_isomSpace
    Stacks.Curves.subsingleton_sheafDerivation_of_hasAtWorstNodalSingularities X hk hdim hnodal
    hdim1 hH0 hstab

/-- **Stacks 0E7A, from the algebraicity of `Curves` and part (2) of Stacks 0E76.** Let `Curves`
be algebraic (`h`, Stacks 0D5A), let `𝒲 = Curves^{DM}` be a largest DM open substack
(Stacks 0DSW (1)), and let `𝒱 ⊆ 𝒰` be open substacks (`𝓜̄_g ⊆ 𝓜̄`, Stacks 0E78) such that the
point `Spec k → Curves` of a proper scheme `X` over an algebraically closed field `k` lies in `𝒰`
only if `X` satisfies condition (b) of Stacks 0E76 (2) (`hU`). Then `𝓜̄` and `𝓜̄_g` are open
substacks of `Curves^{DM}`, are DM (Stacks 050D) and are Deligne–Mumford stacks (Stacks 03YO). -/
theorem le_and_isAbsolutelyDM_and_isDeligneMumfordStack_of_stableFieldPoints
    (W : Stack.OpenSubstack (curvesAlgebraicStack B hZ h))
    (hW : ∀ V : Stack.OpenSubstack (curvesAlgebraicStack B hZ h),
      Stack.AlgebraicStacks.IsAbsolutelyDM B integerBase hZ B.contains_terminal
          V.toAlgebraicStack →
        V.property ≤ W.property)
    (U V : Stack.OpenSubstack (curvesAlgebraicStack B hZ h)) (hVU : V.property ≤ U.property)
    (hU : ∀ (k : Type u) [Field k] [IsAlgClosed k] (X : Over (Spec (.of k))) [IsProper X.hom]
      (hk : B.Contains (Spec (.of k))) (hdim : topologicalKrullDim X.left ≤ 1),
      U.property (curveFieldPoint X hk hdim h).obj →
        (letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩;
          Stacks.Curves.HasAtWorstNodalSingularities k X.left) ∧
        topologicalKrullDim X.left = 1 ∧
        IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop) ∧
        HasGenusTwoNoRationalTailNoRationalBridge k X.hom) :
    (U.property ≤ W.property ∧
      Stack.AlgebraicStacks.IsAbsolutelyDM B integerBase hZ B.contains_terminal
        U.toAlgebraicStack ∧
      Stack.IsDeligneMumfordStack.{u, w} B integerBase hZ U.toAlgebraicStack.val.val) ∧
    (V.property ≤ W.property ∧
      Stack.AlgebraicStacks.IsAbsolutelyDM B integerBase hZ B.contains_terminal
        V.toAlgebraicStack ∧
      Stack.IsDeligneMumfordStack.{u, w} B integerBase hZ V.toAlgebraicStack.val.val) :=
  le_and_isAbsolutelyDM_and_isDeligneMumfordStack_of_stable h
    isSeparated_relocalizeToYoneda_isomSpace
    Stacks.Curves.subsingleton_sheafDerivation_of_hasAtWorstNodalSingularities W hW U V hVU hU

/-- **Stacks 0E7A from the algebraicity of `Curves` and part (2) of Stacks 0E76, with
`Curves^{DM}` produced.** Under the inputs of
`le_and_isAbsolutelyDM_and_isDeligneMumfordStack_of_stableFieldPoints` other than `𝒲`: there is
an open substack `Curves^{DM}` of `Curves`, cutting out the Deligne–Mumford locus and DM
(Stacks 0DSW (1)), such that `𝓜̄` and `𝓜̄_g` are open substacks of it, DM (Stacks 050D) and
Deligne–Mumford stacks (Stacks 03YO). -/
theorem exists_curvesDM_and_le_and_isDeligneMumfordStack_of_stableFieldPoints
    (U V : Stack.OpenSubstack (curvesAlgebraicStack B hZ h)) (hVU : V.property ≤ U.property)
    (hU : ∀ (k : Type u) [Field k] [IsAlgClosed k] (X : Over (Spec (.of k))) [IsProper X.hom]
      (hk : B.Contains (Spec (.of k))) (hdim : topologicalKrullDim X.left ≤ 1),
      U.property (curveFieldPoint X hk hdim h).obj →
        (letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩;
          Stacks.Curves.HasAtWorstNodalSingularities k X.left) ∧
        topologicalKrullDim X.left = 1 ∧
        IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop) ∧
        HasGenusTwoNoRationalTailNoRationalBridge k X.hom) :
    ∃ W : Stack.OpenSubstack (curvesAlgebraicStack B hZ h),
      W.property =
        Stack.dmLocus B integerBase hZ B.contains_terminal (curvesAlgebraicStack B hZ h) ∧
      Stack.AlgebraicStacks.IsAbsolutelyDM B integerBase hZ B.contains_terminal
        W.toAlgebraicStack ∧
      (U.property ≤ W.property ∧
        Stack.AlgebraicStacks.IsAbsolutelyDM B integerBase hZ B.contains_terminal
          U.toAlgebraicStack ∧
        Stack.IsDeligneMumfordStack.{u, w} B integerBase hZ U.toAlgebraicStack.val.val) ∧
      (V.property ≤ W.property ∧
        Stack.AlgebraicStacks.IsAbsolutelyDM B integerBase hZ B.contains_terminal
          V.toAlgebraicStack ∧
        Stack.IsDeligneMumfordStack.{u, w} B integerBase hZ V.toAlgebraicStack.val.val) :=
  exists_curvesDM_and_le_and_isDeligneMumfordStack_of_stable h
    isSeparated_relocalizeToYoneda_isomSpace
    Stacks.Curves.subsingleton_sheafDerivation_of_hasAtWorstNodalSingularities U V hVU hU

end AlgebraicGeometry.curvesSmall

end
