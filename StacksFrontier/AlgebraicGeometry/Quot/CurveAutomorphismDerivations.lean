module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyAutomorphismGroupScheme
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordIsomCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# Infinitesimal automorphisms and the Deligne–Mumford locus of `Curves` (Stacks 0E6G)

Let `X` be a proper scheme of dimension at most one over a field `k`. Stacks 0E6G says that the
conditions of Stacks 0DSW (3) on `X` — the point `Spec k → Curves` classifying `X` factors through
`Curves^DM`; `Aut(X)` is geometrically reduced over `k` of dimension `0`; `Aut(X) → Spec k` is
unramified — are equivalent to `Der_k(𝒪_X, 𝒪_X) = 0`.

`AlgebraicGeometry.curvesSmall.tfae_dmLocus_curveFieldPoint_subsingleton_derivations` proves this
from the algebraicity of `Curves` (Stacks 0D5A) and two further inputs: that `Aut(X)` is separated
over `k`, and that it is locally of finite type over `k`, both of which the proof of Stacks 0E6G
reads off Stacks 0DSQ. This file derives both inputs:

* `Aut(X)` is locally of finite type over `k` because the isomorphism sheaves of any algebraic
  stack are (Stacks 04XR, `AlgebraicGeometry.Stack.isLocallyOfFiniteType_isomPresheaf`);
* `Aut(X) = Isom_k(X, X)` is separated over `k` once the isomorphism spaces `Isom_U(Y, X)` of
  the small model of `Curves` are separated over their bases, read over `Spec(ℤ)` (`hIsomSep`).
  That is the separation step of the proof of Stacks 0DSQ, from Moduli Stacks, Lemmas 0DPN and
  0DPP; its proof is `AlgebraicGeometry.curvesSmall.isSeparated_relocalizeToYoneda_isomSpace`,
  which is not yet in this library.

## Main results

* `AlgebraicGeometry.Space.isSeparated_toYonedaId_of_isSeparated_relocalizeToYoneda`: separatedness
  of an algebraic space over `W` from that of its structure morphism read over a larger base.
* `AlgebraicGeometry.curvesSmall.isSeparatedOver_autIsomSpace_of`: `Aut(X)` is separated over `k`.
* `AlgebraicGeometry.curvesSmall.isLocallyOfFiniteType_automorphismGroupSpace_curveFieldPoint`:
  `Aut(X)` is locally of finite type over `k`.
* `curvesSmall.tfae_dmLocus_curveFieldPoint_subsingleton_derivations_of_isAlgebraicStack`:
  the statement of Stacks 0E6G at the algebraic stack of curves.

The last statement is not registered: it takes `h`, the algebraicity of `Curves` (Stacks 0D5A),
and `hIsomSep`, the separation step of Stacks 0DSQ (Stacks 0DPN, 0DPP).

## References

* [Stacks Project, Tag 0E6G](https://stacks.math.columbia.edu/tag/0E6G)
* [Stacks Project, Tag 0DSW](https://stacks.math.columbia.edu/tag/0DSW)
* [Stacks Project, Tag 0DSQ](https://stacks.math.columbia.edu/tag/0DSQ)
* [Stacks Project, Tag 04XR](https://stacks.math.columbia.edu/tag/04XR)
* [Stacks Project, Tag 0DPP](https://stacks.math.columbia.edu/tag/0DPP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (W S : Scheme.{u}) (hW : B.Contains W) (hS : B.Contains S)
  (h : B.obj hW ⟶ B.obj hS)

/-- **Separatedness of an algebraic space is read off its structure morphism over a larger
base.** If the structural morphism of the lower-shriek extension of a presheaf `F` on the big fppf
site of `W` along `h : W ⟶ S` (Stacks 04SG) is separated, then so is the morphism from `F` to the
terminal presheaf over `W`: that structural morphism is the extension of `F ⟶ W` followed by an
isomorphism, and separatedness of an extended morphism descends (Stacks 03HL). -/
theorem isSeparated_toYonedaId_of_isSeparated_relocalizeToYoneda
    (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u)
    (hF : IsSeparated B S hS (OverShriek.relocalizeToYoneda h F)) :
    IsSeparated B W hW (toYonedaId B W hW F) := by
  have _ := isIso_relocalizeToYoneda_yonedaId B W S hW hS h
  have := isSeparated_respectsIso B S hS
  rw [← relocalizeToYoneda_eq_map_toYonedaId B W S hW hS h F] at hF
  exact isSeparated_of_relocalizeMap B W S hW hS h _
    ((MorphismProperty.cancel_right_of_respectsIso (@IsSeparated B S hS) _ _).1 hF)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.curvesSmall

open Deformation Deformation.Examples

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}
variable {k : Type u} [Field k] (X : Over (Spec (.of k))) [IsProper X.hom]
  (hk : B.Contains (Spec (.of k))) (hdim : topologicalKrullDim X.left ≤ 1)

/-- **`Aut(X)` is separated over `k`.** For a proper scheme `X` of dimension at most one over a
field `k`, the automorphism functor `Isom(X, X)` of the point of `Curves` classifying `X` is
separated over `Spec k`, given `hIsomSep`: the structure morphism of every isomorphism space of the
small model of `Curves`, read over `Spec(ℤ)` (Stacks 04SG), is separated. Separatedness of the
structure morphism does not depend on the base it is read over. The input `hIsomSep` is the
statement of `AlgebraicGeometry.curvesSmall.isSeparated_relocalizeToYoneda_isomSpace`, the
separation step of the proof of Stacks 0DSQ, from Moduli Stacks, Lemmas 0DPN and
0DPP. -/
theorem isSeparatedOver_autIsomSpace_of
    (hIsomSep : ∀ {U : BigFppfOver B integerBase hZ} (y₁ y₂ : (curvesSmall B hZ).val.p.Fiber U),
      Space.IsSeparated B integerBase hZ (OverShriek.relocalizeToYoneda U.hom
        (Stack.isomSpace B integerBase hZ (curvesSmall B hZ) U y₁ y₂))) :
    Space.IsSeparatedOver B (Spec (.of k)) hk (autIsomSpace (hZ := hZ) X hk hdim) :=
  (Space.isSeparatedOver_iff_isSeparated_of_isTerminal B (Spec (.of k)) hk
    (Space.isTerminal_yoneda_obj_base B (Spec (.of k)) hk) _).2
    (Space.isSeparated_toYonedaId_of_isSeparated_relocalizeToYoneda B (Spec (.of k)) integerBase hk
      hZ (integerSiteObject B hZ hk).hom (autIsomSpace (hZ := hZ) X hk hdim)
      (hIsomSep (curveFiber (hZ := hZ) X hk hdim) (curveFiber (hZ := hZ) X hk hdim)))

section Stack

variable (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)

/-- **`Aut(X)` is locally of finite type over `k`.** For a proper scheme `X` of dimension at most
one over a field `k` and the algebraic stack of curves, the automorphism group algebraic space of
the point `Spec k → Curves` classifying `X` is locally of finite type over `k`: the isomorphism
sheaves of an algebraic stack are locally of finite type (Stacks 04XR). -/
theorem isLocallyOfFiniteType_automorphismGroupSpace_curveFieldPoint :
    Space.IsLocallyOfFiniteType B (Spec (.of k)) hk
      (Stack.automorphismGroupSpace B integerBase hZ (curvesAlgebraicStack B hZ h).val
        (curvesAlgebraicStack B hZ h).property (curveFieldPoint X hk hdim h).base
        ⟨(curveFieldPoint X hk hdim h).obj, (curveFieldPoint X hk hdim h).over⟩).obj.X.hom :=
  (Stack.holdsOnEveryEtaleChart_isomSpaceOver_hom_iff B integerBase hZ
    (curvesAlgebraicStack B hZ h) _ (curveFieldPoint X hk hdim h).base
    ⟨(curveFieldPoint X hk hdim h).obj, (curveFieldPoint X hk hdim h).over⟩
    ⟨(curveFieldPoint X hk hdim h).obj, (curveFieldPoint X hk hdim h).over⟩).mpr
    (Stack.isLocallyOfFiniteType_isomPresheaf B integerBase hZ (curvesAlgebraicStack B hZ h).val
      (curvesAlgebraicStack B hZ h).property _ _ _)

/-- **Stacks 0E6G, at the algebraic stack of curves.** Let `X` be a proper scheme of dimension at
most one over a field `k`, and `x : Spec k → Curves` the point classifying it, `Curves` being
algebraic (`h`, Stacks 0D5A), and let the isomorphism spaces of `Curves` be separated
(`hIsomSep`, the separation step of Stacks 0DSQ). The following are equivalent:
1. `x` factors through the Deligne–Mumford locus `Curves^DM`;
2. `Aut(X)` is geometrically reduced over `k` and has dimension `0`;
3. `Aut(X) → Spec k` is unramified;
4. `Der_k(𝒪_X, 𝒪_X) = 0`.

This is `AlgebraicGeometry.curvesSmall.tfae_dmLocus_curveFieldPoint_subsingleton_derivations`,
with separatedness of `Aut(X)` over `k` from
`AlgebraicGeometry.curvesSmall.isSeparatedOver_autIsomSpace_of` and its local finite type over `k`
from `AlgebraicGeometry.curvesSmall.isLocallyOfFiniteType_automorphismGroupSpace_curveFieldPoint`.

Not registered: `h` is Stacks 0D5A, and `hIsomSep` is
`AlgebraicGeometry.curvesSmall.isSeparated_relocalizeToYoneda_isomSpace`. -/
theorem tfae_dmLocus_curveFieldPoint_subsingleton_derivations_of_isAlgebraicStack
    (hIsomSep : ∀ {U : BigFppfOver B integerBase hZ} (y₁ y₂ : (curvesSmall B hZ).val.p.Fiber U),
      Space.IsSeparated B integerBase hZ (OverShriek.relocalizeToYoneda U.hom
        (Stack.isomSpace B integerBase hZ (curvesSmall B hZ) U y₁ y₂))) :
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
  tfae_dmLocus_curveFieldPoint_subsingleton_derivations X hk hdim h
    (isSeparatedOver_autIsomSpace_of X hk hdim hIsomSep)
    (isLocallyOfFiniteType_automorphismGroupSpace_curveFieldPoint X hk hdim h)

end Stack

end AlgebraicGeometry.curvesSmall
