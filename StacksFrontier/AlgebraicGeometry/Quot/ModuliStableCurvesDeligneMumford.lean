module

public import StacksFrontier.AlgebraicGeometry.Curves.SheafDerivationSchemeMorphismDerivations
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.AutomaticProperties
public import StacksFrontier.AlgebraicGeometry.Quot.CurveAutomorphismDerivations
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOverFieldScheme
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesDeligneMumford
public import StacksFrontier.AlgebraicGeometry.Quot.StableCurveFamilies
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordOpenSubstackOfPoints

/-!
# `𝓜̄` and `𝓜̄_g` are open substacks of `Curves^{DM}` (towards Stacks 0E7A)

Stacks 0E7A: the moduli stacks `𝓜̄` of stable curves and `𝓜̄_g` of stable curves of genus `g` are
open substacks of `Curves^{DM}`; in particular they are DM (Stacks 050D) and Deligne–Mumford
stacks (Stacks 03YO). The source's proof: a point of `𝓜̄` is a proper curve `X` over a field `k`
satisfying condition (b) of Stacks 0E76 (2); replace `k` by its algebraic closure; by Stacks 0DSW
and 0E6G it suffices that `Der_k(𝒪_X, 𝒪_X) = 0`, which is Stacks 0E69; then `𝓜̄ ⊆ Curves^{DM}`
by maximality, and a DM algebraic stack is Deligne–Mumford by Stacks 06N3.

This file runs that argument in the small model `AlgebraicGeometry.curvesAlgebraicStack B hZ h`
of the stack of curves:

* every field-valued point of `Curves` is refined by the point `Spec k → Curves` classifying a
  proper scheme over the same field (`AlgebraicGeometry.curvesSmall.exists_curveFieldPoint_hom`,
  from Stacks 0ADD through
  `AlgebraicGeometry.CurveFamily.exists_iso_curveFamilyOfScheme_of_base_eq`);
* at such a point over an algebraically closed field with condition (b) of 0E76 (2), `Aut(X)` is
  unramified, by 0E6G (`tfae_dmLocus_curveFieldPoint_subsingleton_derivations_of_isAlgebraicStack`)
  and 0E69 through `Stacks.Curves.subsingleton_schemeMorphismDerivations_of_isStableOverAlgClosed`;
  connectedness of `X` is Stacks 0BY5 (`k = H⁰(X, 𝒪_X)`);
* the reduction to algebraically closed fields is
  `AlgebraicGeometry.Stack.FieldValuedPoint.exists_isAlgClosed_hom`, and the containment in
  `Curves^{DM}` and the Deligne–Mumford property are, in the namespace
  `AlgebraicGeometry.Stack`,
  `OpenSubstack.le_and_isAbsolutelyDM_and_isDeligneMumfordStack_of_fieldValuedPoint`.

## Main results

* `AlgebraicGeometry.curvesSmall.exists_curveFieldPoint_hom`.
* `AlgebraicGeometry.curvesSmall.isUnramifiedAutomorphismGroupSpace_curveFieldPoint_of_stable`.
* `AlgebraicGeometry.curvesSmall.le_and_isAbsolutelyDM_and_isDeligneMumfordStack_of_stable`:
  Stacks 0E7A from its inputs, relative to a given `Curves^{DM}` (unregistered).
* `AlgebraicGeometry.curvesSmall.exists_curvesDM_and_le_and_isDeligneMumfordStack_of_stable`:
  the same with `Curves^{DM}` produced by Stacks 0DSW (1) (unregistered).

## Implementation notes

Unregistered. The inputs, each explicit: `h`, the algebraicity of `Curves` (Stacks 0D5A);
`hIsomSep`, the separation step of Stacks 0DSQ, in the shape of
`AlgebraicGeometry.curvesSmall.isSeparated_relocalizeToYoneda_isomSpace`; `hvan`, Stacks 0E69 in
the shape of `Stacks.Curves.SheafDerivation.eq_zero_of_hasAtWorstNodalSingularities` (conclusion
read as `Subsingleton`); the open substacks `𝒲 = Curves^{DM}` (with the maximality of
Stacks 0DSW (1)), `𝒰 = 𝓜̄` and `𝒱 = 𝓜̄_g ⊆ 𝓜̄` (Stacks 0E76, 0E78); and `hU`, the implication
(a) ⇒ (b) of Stacks 0E76 (2) at the points classifying proper schemes over algebraically closed
fields.

The open substacks `𝒰 ⊇ 𝒱` are taken as inputs, and no second `𝓜̄` or `𝓜̄_g` is defined here.
They are `AlgebraicGeometry.curvesSmallOpenSubstack B hZ h hP`, with `hP` the openness
(`AlgebraicGeometry.IsOpenCurvesLocus`) of `AlgebraicGeometry.IsStableCurveFamily B hZ` for
`𝒰 = 𝓜̄` and of `AlgebraicGeometry.IsStableGenusCurveFamily B hZ g` (stable with `R¹f_*𝒪_X`
finite locally free of rank `g`) for `𝒱 = 𝓜̄_g`; then `𝒱 ⊆ 𝒰` is the first conjunct of
`IsStableGenusCurveFamily`, read through `AlgebraicGeometry.curvesSmallOpenSubstack_property_iff`.

## References

* [Stacks Project, Tag 0E7A](https://stacks.math.columbia.edu/tag/0E7A)
* [Stacks Project, Tag 0E76](https://stacks.math.columbia.edu/tag/0E76)
* [Stacks Project, Tag 0DSW](https://stacks.math.columbia.edu/tag/0DSW)
* [Stacks Project, Tag 0E6G](https://stacks.math.columbia.edu/tag/0E6G)
* [Stacks Project, Tag 0E69](https://stacks.math.columbia.edu/tag/0E69)
* [Stacks Project, Tag 0BY5](https://stacks.math.columbia.edu/tag/0BY5)
* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
-/

@[expose] public noncomputable section

open CategoryTheory Deformation.Examples

universe w u

namespace AlgebraicGeometry.curvesSmall

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}
  (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)

/-- **Every field-valued point of `Curves` is refined by the point of a proper curve over the same
field.** For a field-valued point `y` of the small model of the stack of curves, with field `K`,
there is a proper scheme `X` of dimension at most one over `K` and an arrow from the object of the
point `Spec K → Curves` classifying `X` to the object of `y`: pull `y` back to the spectrum of `K`
as an object of the site, where its family is the family of a proper scheme (Stacks 0ADD). -/
theorem exists_curveFieldPoint_hom
    (y : Stack.FieldValuedPoint B integerBase hZ (curvesAlgebraicStack B hZ h).val.val) :
    ∃ (hK : B.Contains (Spec (.of y.carrier))) (X : Over (Spec (.of y.carrier)))
      (_ : IsProper X.hom) (hdim : topologicalKrullDim X.left ≤ 1),
      Nonempty ((curveFieldPoint X hK hdim h).obj ⟶ y.obj) := by
  have hK := Stack.contains_spectrum_fieldValuedPoint B integerBase hZ y
  have hspec : Stack.spectrumSiteObject B integerBase hZ y = integerSiteObject B hZ hK :=
    congrArg Over.mk (ObjectProperty.hom_ext _ (specULiftZIsTerminal.hom_ext _ _))
  let β : integerSiteObject B hZ hK ⟶ y.base :=
    eqToHom hspec.symm ≫ (Stack.spectrumSiteObjectIso B integerBase hZ y).hom
  obtain ⟨z, φ, hφ⟩ := (curvesAlgebraicStack B hZ h).val.property.exists_lift β y.obj y.over
  have hz : (curvesAlgebraicStack B hZ h).val.val.p.obj z = integerSiteObject B hZ hK :=
    IsHomLift.domain_eq _ β φ
  obtain ⟨X, hX, hdim, ⟨e⟩⟩ :=
    CurveFamily.exists_iso_curveFamilyOfScheme_of_base_eq hK (ShrinkHoms.fromShrinkHoms z) hz
  let := locallySmall_curveFamily B hZ
  exact ⟨hK, X, hX, hdim, ⟨(ShrinkHoms.functor (CurveFamily B hZ)).map e.inv ≫ φ⟩⟩

/-- **At a stable curve over an algebraically closed field, `Aut(X)` is unramified.** Let `k` be
algebraically closed and `X` proper over `k` of dimension at most one, at-worst-nodal of dimension
one, with `k = H⁰(X, 𝒪_X)`, of genus at least two and without rational tails or bridges. Then the
automorphism group algebraic space of the point `Spec k → Curves` classifying `X` is unramified:
`X` is connected (Stacks 0BY5), so `Der_k(𝒪_X, 𝒪_X) = 0` (Stacks 0E69, `hvan`), which is
unramifiedness by Stacks 0E6G. Unregistered. -/
theorem isUnramifiedAutomorphismGroupSpace_curveFieldPoint_of_stable
    (hIsomSep : ∀ {U : BigFppfOver B integerBase hZ} (y₁ y₂ : (curvesSmall B hZ).val.p.Fiber U),
      Space.IsSeparated B integerBase hZ (OverShriek.relocalizeToYoneda U.hom
        (Stack.isomSpace B integerBase hZ (curvesSmall B hZ) U y₁ y₂)))
    (hvan : ∀ (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [IsProper (X ↘ Spec (.of k))] [ConnectedSpace X] (_ : topologicalKrullDim X = 1)
      (_ : Stacks.Curves.HasAtWorstNodalSingularities k X) (_ : 2 ≤ genus (X ↘ Spec (.of k)))
      (_ : ∀ C : X.IdealSheafData, ¬ IsRationalTail k X C)
      (_ : ∀ C : X.IdealSheafData, ¬ IsRationalBridge k X C),
      Subsingleton (Stacks.Curves.SheafDerivation k X))
    {k : Type u} [Field k] [IsAlgClosed k] (X : Over (Spec (.of k))) [IsProper X.hom]
    (hk : B.Contains (Spec (.of k))) (hdim : topologicalKrullDim X.left ≤ 1)
    (hnodal : letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
      Stacks.Curves.HasAtWorstNodalSingularities k X.left)
    (hdim1 : topologicalKrullDim X.left = 1)
    (hH0 : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop))
    (hstab : HasGenusTwoNoRationalTailNoRationalBridge k X.hom) :
    Stack.IsUnramifiedAutomorphismGroupSpace B integerBase hZ (curvesAlgebraicStack B hZ h)
      (curveFieldPoint X hk hdim h) := by
  let : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
  have : IsProper (X.left ↘ Spec (.of k)) := ‹IsProper X.hom›
  have : ConnectedSpace X.left := connectedSpace_of_isIso_globalSections k X.hom
  obtain ⟨hg, htail, hbridge⟩ := hstab
  have hD : Subsingleton (schemeMorphismDerivations (Λ := k) (k := k) (𝟙 X.left) X.hom) :=
    Stacks.Curves.subsingleton_schemeMorphismDerivations_of_isStableOverAlgClosed hvan X.left
      hdim1 hnodal hg htail hbridge.snd
  have T := tfae_dmLocus_curveFieldPoint_subsingleton_derivations_of_isAlgebraicStack X hk hdim h
    hIsomSep
  exact (T.out 3 4).2 hD

/-- **Stacks 0E7A from its inputs.** Let `Curves` be algebraic (`h`, Stacks 0D5A), with separated
isomorphism spaces (`hIsomSep`, the separation step of Stacks 0DSQ), and let Stacks 0E69 hold
(`hvan`). Let `𝒲 = Curves^{DM}` be a largest DM open substack (Stacks 0DSW (1)), and let
`𝒱 ⊆ 𝒰` be open substacks (`𝓜̄_g ⊆ 𝓜̄`, Stacks 0E78) such that the point `Spec k → Curves` of a
proper scheme `X` over an algebraically closed field `k` lies in `𝒰` only if `X` satisfies
condition (b) of Stacks 0E76 (2) (`hU`): at-worst-nodal, `dim X = 1`, `k = H⁰(X, 𝒪_X)`, genus at
least two, no rational tails or bridges. Then `𝓜̄` and `𝓜̄_g` are open substacks of `Curves^{DM}`,
are DM (Stacks 050D) and are Deligne–Mumford stacks (Stacks 03YO). Unregistered. -/
theorem le_and_isAbsolutelyDM_and_isDeligneMumfordStack_of_stable
    (hIsomSep : ∀ {U : BigFppfOver B integerBase hZ} (y₁ y₂ : (curvesSmall B hZ).val.p.Fiber U),
      Space.IsSeparated B integerBase hZ (OverShriek.relocalizeToYoneda U.hom
        (Stack.isomSpace B integerBase hZ (curvesSmall B hZ) U y₁ y₂)))
    (hvan : ∀ (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [IsProper (X ↘ Spec (.of k))] [ConnectedSpace X] (_ : topologicalKrullDim X = 1)
      (_ : Stacks.Curves.HasAtWorstNodalSingularities k X) (_ : 2 ≤ genus (X ↘ Spec (.of k)))
      (_ : ∀ C : X.IdealSheafData, ¬ IsRationalTail k X C)
      (_ : ∀ C : X.IdealSheafData, ¬ IsRationalBridge k X C),
      Subsingleton (Stacks.Curves.SheafDerivation k X))
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
      Stack.IsDeligneMumfordStack.{u, w} B integerBase hZ V.toAlgebraicStack.val.val) := by
  have hR : U.HasUnramifiedRefinements B integerBase hZ := fun x hx => by
    obtain ⟨y, hy, ⟨a⟩⟩ := Stack.FieldValuedPoint.exists_isAlgClosed_hom B integerBase hZ x
    obtain ⟨hK, X, hX, hdim, ⟨b⟩⟩ := exists_curveFieldPoint_hom h y
    obtain ⟨hnodal, hdim1, hH0, hstab⟩ :=
      hU y.carrier X hK hdim (Stack.OpenSubstack.prop_of_hom B integerBase hZ U (b ≫ a) hx)
    exact ⟨curveFieldPoint X hK hdim h, ⟨b ≫ a⟩,
      isUnramifiedAutomorphismGroupSpace_curveFieldPoint_of_stable h hIsomSep hvan X hK hdim
        hnodal hdim1 hH0 hstab⟩
  exact ⟨Stack.OpenSubstack.le_and_isAbsolutelyDM_and_isDeligneMumfordStack_of_fieldValuedPoint
      B integerBase hZ B.contains_terminal W hW U hR,
    Stack.OpenSubstack.le_and_isAbsolutelyDM_and_isDeligneMumfordStack_of_fieldValuedPoint
      B integerBase hZ B.contains_terminal W hW V (hR.of_le B integerBase hZ hVU)⟩

/-- **Stacks 0E7A from its inputs, with `Curves^{DM}` produced.** Under the inputs of
`AlgebraicGeometry.curvesSmall.le_and_isAbsolutelyDM_and_isDeligneMumfordStack_of_stable` other
than `𝒲`: there is an open substack `Curves^{DM}` of `Curves`, cutting out the Deligne–Mumford
locus and DM (Stacks 0DSW (1),
`AlgebraicGeometry.curvesSmall.exists_largest_isAbsolutelyDM_openSubstack`),
such that `𝓜̄` and `𝓜̄_g` are open substacks of it, DM (Stacks 050D) and Deligne–Mumford stacks
(Stacks 03YO). Unregistered: `h` is Stacks 0D5A, `hIsomSep` the separation step of Stacks 0DSQ,
`hvan` Stacks 0E69 and `hU` part (2) of Stacks 0E76. -/
theorem exists_curvesDM_and_le_and_isDeligneMumfordStack_of_stable
    (hIsomSep : ∀ {U : BigFppfOver B integerBase hZ} (y₁ y₂ : (curvesSmall B hZ).val.p.Fiber U),
      Space.IsSeparated B integerBase hZ (OverShriek.relocalizeToYoneda U.hom
        (Stack.isomSpace B integerBase hZ (curvesSmall B hZ) U y₁ y₂)))
    (hvan : ∀ (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [IsProper (X ↘ Spec (.of k))] [ConnectedSpace X] (_ : topologicalKrullDim X = 1)
      (_ : Stacks.Curves.HasAtWorstNodalSingularities k X) (_ : 2 ≤ genus (X ↘ Spec (.of k)))
      (_ : ∀ C : X.IdealSheafData, ¬ IsRationalTail k X C)
      (_ : ∀ C : X.IdealSheafData, ¬ IsRationalBridge k X C),
      Subsingleton (Stacks.Curves.SheafDerivation k X))
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
        Stack.IsDeligneMumfordStack.{u, w} B integerBase hZ V.toAlgebraicStack.val.val) := by
  obtain ⟨W, hW, hDM, hmax⟩ := exists_largest_isAbsolutelyDM_openSubstack h
  exact ⟨W, hW, hDM,
    le_and_isAbsolutelyDM_and_isDeligneMumfordStack_of_stable h hIsomSep hvan W hmax U V hVU hU⟩

end AlgebraicGeometry.curvesSmall

end
