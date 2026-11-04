module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.ComponentCriterion
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecialFibreDimension
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.BaseChangeUnion
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.DualizingAmple
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.DualizingSheafDegree
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafDuality
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingComplexBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesPrestableOpen
public import StacksFrontier.AlgebraicGeometry.Quot.StableCurveFamilies
public import StacksFrontier.AlgebraicGeometry.Quot.StableLocusOpenFibreAmple
public import StacksFrontier.AlgebraicGeometry.Curves.CanonicalContraction.NodalAwayFromAttaching
public import StacksFrontier.AlgebraicGeometry.Curves.NodalGorensteinReduced
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
public import StacksFrontier.AlgebraicGeometry.AmplePullback.Affine
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.UFDExtensionInvertibleGlobal
public import StacksFrontier.AlgebraicGeometry.ComponentDegreeDevissage.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.ComponentPositivity
public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.BaseFieldInvariance

/-!
# The open substack of stable curves (towards Stacks 0E76)

Stacks 0E76 produces the open substack `Curves^{stable} ⊂ Curves` of stable families of curves
(Stacks 0E75): prestable families whose fibres have genus at least two and neither a rational
tail nor a rational bridge. Its proof runs the method of Section 0E0E: by Stacks 0E6U it suffices
to cut out an open of the base of a *prestable* family, which Stacks 0E74 does (the fibre has no
rational tail or bridge exactly when `ω_{X/S}` is ample near the point, an open condition by
Stacks 0D3D), and the formation of that open commutes with base change.

This file proves the formal part of that argument and assembles the whole statement from its
inputs.

## Main definitions

* `AlgebraicGeometry.CurveFamily.HasStableFibres`: the fibrewise half of Stacks 0E75 — every
  fibre over a field-valued point of the base has genus at least two and neither a rational tail
  nor a rational bridge — so that `IsStableCurveFamily = IsPrestableCurveFamily ∧ HasStableFibres`.
* `AlgebraicGeometry.IsOpenCurvesLocusWithin`: condition (o) of Section 0E0E *relative to* a
  property `P`, tested only on families having `P`. This is the shape of the reduction "it suffices
  to look at families of prestable curves" of the source.

## Main results

* `AlgebraicGeometry.IsOpenCurvesLocus.and_of_within`: if `P` satisfies condition (o) and `Q`
  satisfies it relative to `P`, then `P ∧ Q` satisfies condition (o).
* `AlgebraicGeometry.isOpenCurvesLocus_isStableCurveFamily_of_prestable`: condition (o) for
  `Curves^{stable}`, from condition (o) for `Curves^{prestable}` (Stacks 0E6U) and the relative
  openness of `HasStableFibres` on prestable families (Stacks 0E74 with Stacks 0D3D).
* `AlgebraicGeometry.curvesStable_isOpenSubstack_and_factors_iff_of_prestable`: the open
  substack and part (1) of Stacks 0E76 from those two inputs.
* `hasGenusTwoNoRationalTailNoRationalBridge_iff_isAmple_dualizingSheafOverField_of`:
  for a proper nodal curve over a field with `H⁰ = k`, conditions (b) and (c) of part (2) of
  Stacks 0E76 agree, from Stacks 0E3P and its converse.
* `AlgebraicGeometry.two_le_genus_of_isAmple_dualizingSheafOverField_of`: an ample `ω_X` forces
  genus at least two, from Stacks 0AYW, 0B5Y, 0E37 and 0C19.
* `AlgebraicGeometry.hasGenusTwoNoRationalTailNoRationalBridge_of_isPullback_of`: a stable curve
  stays stable under extension of the ground field, for every presentation of `X ×_k K`.
* `AlgebraicGeometry.hasStableFibres_curveFamilyOverFieldOfProper_iff_of`: the fibres of the
  family of a nodal proper curve `X` over `k` with `H⁰ = k` are stable exactly when `X` is.
* `AlgebraicGeometry.curvesStable_isOpenSubstack_and_factors_iff_of_inputs`: the whole of
  Stacks 0E76, parts (1) and (2), from the inputs of Stacks 0E6U and `hrel` below.

## Implementation notes

All results with inputs are unregistered: Stacks 0E76 is registered once the inputs are proved
outright. The inputs of the assembled statement, each an explicit hypothesis:

* `hopen`, `hpush`, `hsch`: the three inputs of Stacks 0E6U, in the exact shape of
  `AlgebraicGeometry.curvesPrestable_isOpenSubstack_and_factors_iff_of_h01Inputs`.
* `hrel`: `HasStableFibres` satisfies condition (o) relative to `IsPrestableCurveFamily`. This is
  what Stacks 0E74 with Stacks 0D3D (openness of the relatively ample locus) and the base-change
  invariance of the source's proof (Stacks 0E3L, 0E3Q, 0D2P) provide.

The intermediate results below carry five further results of other chapters as explicit
hypotheses. All five are available in the tree, so the assembled statement discharges them:

* `hbc`: part (2) of Stacks 0E32 at the dualizing sheaf — for any presentation `X'` of the base
  change of a proper `X` over `k` along a field extension `K/k`, the pullback of `ω_X` is
  `ω_{X'}` — discharged by `Stacks.Duality.dualizingSheafOverFieldBaseChangeIso`. With it the
  fibre conditions of the family of a proper curve over a field are proved
  (`AlgebraicGeometry.hasStableFibres_curveFamilyOverFieldOfProper_iff_of`): the source's
  "ampleness is insensitive to base field extensions".
* `h0E3P`: Stacks 0E3P, discharged by
  `AlgebraicGeometry.isAmple_dualizingSheafOverField_of_hasAtWorstNodalSingularities`.
* `h0E63`, `h0E64`: Stacks 0E63 and 0E64 (degree of `ω_X` on a rational tail is negative, on a
  rational bridge zero), discharged by
  `AlgebraicGeometry.invertibleCurveDegree_pullback_dualizingSheafOverField_neg_of_isRationalTail`
  and
  `invertibleCurveDegree_pullback_dualizingSheafOverField_eq_zero_of_isRationalBridge`;
  the dimension of `C` and the invertibility of `ω_X|_C`, which those two statements supply
  themselves, are quantified over in the hypotheses, and both are propositions, so the statements
  specialize to the hypotheses exactly. With the base's Stacks 0B5Y they exclude rational tails
  and bridges when `ω_X` is ample.
* `h0C19`: Stacks 0C19 (`deg ω_X = 2g - 2` on a Gorenstein curve), discharged by
  `AlgebraicGeometry.invertibleCurveDegree_dualizingSheafOverField`, with the connectedness of
  `X` and the invertibility of `ω_X` that it supplies itself quantified over; with Stacks 0AYW
  and 0B5Y it gives the genus bound for an ample `ω_X`
  (`AlgebraicGeometry.two_le_genus_of_isAmple_dualizingSheafOverField_of`).

## References

* [Stacks Project, Tag 0E76](https://stacks.math.columbia.edu/tag/0E76)
* [Stacks Project, Tag 0E75](https://stacks.math.columbia.edu/tag/0E75)
* [Stacks Project, Tag 0E74](https://stacks.math.columbia.edu/tag/0E74)
* [Stacks Project, Tag 0E6U](https://stacks.math.columbia.edu/tag/0E6U)
* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
* [Stacks Project, Tag 0E3P](https://stacks.math.columbia.edu/tag/0E3P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

attribute [local instance] Space.pointTopology

open Stacks.AlgebraicGeometry.ComponentDegrees

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

variable (B hZ) in
/-- **The fibrewise half of Stacks 0E75.** For every field-valued point `Spec K → S` of the base,
the fibre of the family there — presented by a scheme `V` of the site over `Spec K` exhibiting it
as the fibre product — has genus at least two and neither a rational tail nor a rational bridge.
A family of curves is stable exactly when it is prestable and has stable fibres,
`AlgebraicGeometry.CurveFamily.isStableCurveFamily_iff`. -/
abbrev CurveFamily.HasStableFibres (X : CurveFamily B hZ) : Prop :=
  ∀ p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj,
    ∃ (V : BigFppfOver B integerBase hZ) (v : V ⟶ p.siteObject)
      (q : yoneda.obj V ⟶ X.total.obj),
      IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm p.value) ∧
        HasGenusTwoNoRationalTailNoRationalBridge p.carrier
          ((BigFppfOver.toScheme B integerBase hZ).map v)

/-- A family of curves is stable (Stacks 0E75) exactly when it is prestable and has stable
fibres. -/
theorem CurveFamily.isStableCurveFamily_iff (X : CurveFamily B hZ) :
    IsStableCurveFamily B hZ X ↔
      IsPrestableCurveFamily B hZ X ∧ CurveFamily.HasStableFibres B hZ X :=
  Iff.rfl

variable (B hZ) in
/-- **Condition (o) of Stacks 0E0E relative to a property `P`.** Every family of curves `G` has
an open subspace `W` of its base such that a family of curves `F` mapping to `G` *and having `P`*
has `Q` exactly when its morphism of base schemes factors through `W`. -/
def IsOpenCurvesLocusWithin (P Q : ObjectProperty (CurveFamily B hZ)) : Prop :=
  ∀ G : CurveFamily B hZ, ∃ W : Subfunctor (schemeSpace G.base).obj,
    Space.IsOpenSubspace B integerBase hZ W ∧
      ∀ (F : CurveFamily B hZ) (a : F ⟶ G), P F →
        (Q F ↔ ∃ t : (schemeSpace F.base).obj ⟶ W.toFunctor,
          t ≫ W.ι = (schemeSpaceMap a.baseMap).hom)

/-- **Condition (o) for `P ∧ Q` from condition (o) for `P` and for `Q` relative to `P`.** The open
of the base for `P ∧ Q` is the intersection of the open for `P` with the open for `Q`: over the
first, a family has `P`, and then it has `Q` exactly over the second. This is the reduction "it
suffices to look at families having `P`" of Section 0E0E. -/
theorem IsOpenCurvesLocus.and_of_within {P Q : ObjectProperty (CurveFamily B hZ)}
    (hP : IsOpenCurvesLocus B hZ P) (hQ : IsOpenCurvesLocusWithin B hZ P Q) :
    IsOpenCurvesLocus B hZ (fun F => P F ∧ Q F) := by
  refine IsOpenCurvesLocus.of_points fun G => ?_
  obtain ⟨W₁, hW₁, h₁⟩ := hP G
  obtain ⟨W₂, hW₂, h₂⟩ := hQ G
  have hO := fun W hW => Space.isOpen_range_pointsMap_ι_of_isOpenSubspace B integerBase hZ
    (schemeSpace G.base).property W hW
  refine ⟨Set.range (Space.pointsMap B integerBase hZ W₁.toFunctor W₁.ι) ∩
      Set.range (Space.pointsMap B integerBase hZ W₂.toFunctor W₂.ι),
    (hO _ hW₁).inter (hO _ hW₂), fun F a => ?_⟩
  have e := fun W hW => Space.factorsThrough_openSubspace_iff_points B integerBase hZ
    (schemeSpace G.base).property (schemeSpace F.base).property W hW
    (schemeSpaceMap a.baseMap).hom
  rw [Set.subset_inter_iff, ← e _ hW₁, ← e _ hW₂, ← h₁ F a]
  exact and_congr_right (h₂ F a)

/-- **Condition (o) of Section 0E0E for `Curves^{stable}`**, from condition (o) for
`Curves^{prestable}` (`hPre`, Stacks 0E6U) and condition (o) for `HasStableFibres` relative to
prestable families (`hrel`, Stacks 0E74 with Stacks 0D3D): `Curves^{stable}` is the locus of
`Curves^{prestable}` over which the fibres are stable. -/
theorem isOpenCurvesLocus_isStableCurveFamily_of_prestable
    (hPre : IsOpenCurvesLocus B hZ (IsPrestableCurveFamily B hZ))
    (hrel : IsOpenCurvesLocusWithin B hZ (IsPrestableCurveFamily B hZ)
      (CurveFamily.HasStableFibres B hZ)) :
    IsOpenCurvesLocus B hZ (IsStableCurveFamily B hZ) :=
  hPre.and_of_within hrel

/-- **Stacks 0E76, the open substack and part (1), from its two inputs.** The strictly full
subcategory `Curves^{stable}` of stable families of curves (Stacks 0E75) is an open substack of
`Curves` — its inclusion is representable by algebraic spaces and an open immersion — and the
classifying morphism of a family of curves factors through it exactly when the family is stable.
The inputs are condition (o) for `Curves^{prestable}` (`hPre`, Stacks 0E6U) and the relative
openness of stable fibres on prestable families (`hrel`, Stacks 0E74 with Stacks 0D3D). -/
theorem curvesStable_isOpenSubstack_and_factors_iff_of_prestable
    (hPre : IsOpenCurvesLocus B hZ (IsPrestableCurveFamily B hZ))
    (hrel : IsOpenCurvesLocusWithin B hZ (IsPrestableCurveFamily B hZ)
      (CurveFamily.HasStableFibres B hZ)) :
    (ObjectProperty.IsClosedUnderIsomorphisms (IsStableCurveFamily B hZ) ∧
      Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (curvesSubstackInclusion B hZ (IsStableCurveFamily B hZ)
          (isOpenCurvesLocus_isStableCurveFamily_of_prestable hPre hrel).prop_of_hom).hom ∧
      Stack.IsOpenImmersion B integerBase hZ
        (curvesSubstackInclusion B hZ (IsStableCurveFamily B hZ)
          (isOpenCurvesLocus_isStableCurveFamily_of_prestable hPre hrel).prop_of_hom)) ∧
    ∀ (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
          ObjectProperty.FullSubcategory (IsStableCurveFamily B hZ),
          z ⋙ ObjectProperty.ι (IsStableCurveFamily B hZ) = y) ↔
        IsStableCurveFamily B hZ (y.obj (Over.mk (𝟙 U.left)))) :=
  isOpenImmersion_curvesSubstackInclusion_and_factors_iff
    (isOpenCurvesLocus_isStableCurveFamily_of_prestable hPre hrel)

/-! ### Part (2): a proper scheme of dimension at most one over a field -/

/-- **A curve with ample dualizing sheaf has neither a rational tail nor a rational bridge, from
Stacks 0E63, Stacks 0E64 and Stacks 0B5Y.** Let `X` be proper of dimension one over a field `k`
with `H⁰(X, 𝒪_X) = k` and at-worst-nodal singularities, and suppose `ω_X` is invertible and
ample. Every irreducible component of dimension one then has `deg(ω_X|_C) > 0` (Stacks 0B5Y,
the base's `AlgebraicGeometry.isAmple_iff_forall_invertibleCurveDegree_reducedComponent_pos`),
while a rational tail has `deg(ω_X|_C) < 0` (`h0E63`) and a rational bridge has
`deg(ω_X|_C) = 0` (`h0E64`).

`h0E63` and `h0E64` are Stacks 0E63 and Stacks 0E64
(`invertibleCurveDegree_pullback_dualizingSheafOverField_neg_of_isRationalTail` and
`invertibleCurveDegree_pullback_dualizingSheafOverField_eq_zero_of_isRationalBridge`), with the
two auxiliary terms their statements name and this tree does not yet have — the invertibility of
`ω_X` and of its restriction, and the dimension of `C` — quantified over instead. Both are
propositions, so the statements of those tags specialize to these exactly. -/
theorem forall_not_isRationalTail_and_not_isRationalBridge_of_isAmple_of
    (h0E63 : ∀ (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [IsProper (X ↘ Spec (.of k))] (hdim : topologicalKrullDim X = 1)
      [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
      (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
      (C : X.IdealSheafData) (hC : IsRationalTail k X C)
      (hCdim : topologicalKrullDim C.subscheme ≤ 1)
      [SheafOfModules.IsInvertible C.subscheme.presheaf C.subscheme.ringCatSheaf.2
        ((Scheme.Modules.pullback C.subschemeι).obj
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))))],
      invertibleCurveDegree k (C.subschemeι ≫ (X ↘ Spec (.of k))) hCdim
        ((Scheme.Modules.pullback C.subschemeι).obj
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))) < 0)
    (h0E64 : ∀ (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [IsProper (X ↘ Spec (.of k))] (hdim : topologicalKrullDim X = 1)
      [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
      (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
      (C : X.IdealSheafData) (hC : IsRationalBridge k X C)
      (hCdim : topologicalKrullDim C.subscheme ≤ 1)
      [SheafOfModules.IsInvertible C.subscheme.presheaf C.subscheme.ringCatSheaf.2
        ((Scheme.Modules.pullback C.subschemeι).obj
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))))],
      invertibleCurveDegree k (C.subschemeι ≫ (X ↘ Spec (.of k))) hCdim
        ((Scheme.Modules.pullback C.subschemeι).obj
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))) = 0)
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
    (hω : ∃ _ : SheafOfModules.IsInvertible X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))),
        Scheme.Modules.IsAmple X (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))) :
    (∀ C : X.IdealSheafData, ¬ IsRationalTail k X C) ∧
      ∀ C : X.IdealSheafData, ¬ IsRationalBridge k X C := by
  obtain ⟨hinv, hL⟩ := hω
  have hpos := (isAmple_iff_forall_invertibleCurveDegree_reducedComponent_pos k
    (X ↘ Spec (.of k)) hdim.le (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))).1 hL
  have : ConnectedSpace X :=
    connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := {}
  -- an integral component of dimension one has positive degree
  have key : ∀ C : X.IdealSheafData, IsIntegral C.subscheme →
      (C.support : Set X) ∈ irreducibleComponents X →
      ∀ hCdim : topologicalKrullDim C.subscheme = 1,
      ∀ _ : SheafOfModules.IsInvertible C.subscheme.presheaf C.subscheme.ringCatSheaf.2
        ((Scheme.Modules.pullback C.subschemeι).obj
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))),
      0 < invertibleCurveDegree k (C.subschemeι ≫ (X ↘ Spec (.of k))) hCdim.le
        ((Scheme.Modules.pullback C.subschemeι).obj
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))) := by
    intro C hint hirr hCdim _
    obtain ⟨ζ, rfl⟩ := exists_genericPointsOne_eq_vanishingIdeal_of_isIntegral C hirr hCdim
    exact hpos ζ
  have hdimC : ∀ C : X.IdealSheafData, (C.support : Set X) ∈ irreducibleComponents X →
      topologicalKrullDim C.subscheme = 1 := fun C hirr => by
    rw [Stacks.Chow.topologicalKrullDim_subscheme]
    exact topologicalKrullDim_eq_one_of_mem_irreducibleComponents hdim hirr
  have hinvC : ∀ C : X.IdealSheafData,
      SheafOfModules.IsInvertible C.subscheme.presheaf C.subscheme.ringCatSheaf.2
        ((Scheme.Modules.pullback C.subschemeι).obj
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))) := fun C =>
    SheafOfModules.isInvertible_pullback C.subschemeι _
  refine ⟨fun C hC => ?_, fun C hC => ?_⟩
  · have : IsIntegral C.subscheme := hC.1
    have := hinvC C
    have hd := hdimC C hC.2.1
    exact lt_asymm (h0E63 k X hdim hnodal C hC hd.le) (key C hC.1 hC.2.1 hd _)
  · rcases id hC with ⟨hint, hirr, -⟩
    have := hint
    have := hinvC C
    have hd := hdimC C hirr
    exact (key C hint hirr hd _).ne' (h0E64 k X hdim hnodal C hC hd.le)


/-- **An ample dualizing sheaf forces genus at least two.** Let `X` be proper over `k` of
dimension one with `H⁰(X, 𝒪_X) = k` and at-worst-nodal singularities, and suppose `ω_X` is
invertible and ample. Then `X` is Gorenstein (Stacks 0E37), so `deg ω_X = 2g - 2` (Stacks 0C19,
`h0C19`), and `deg ω_X > 0` because `ω_X` is ample
(`AlgebraicGeometry.invertibleCurveDegree_pos_of_isAmple_of_isConnected`); hence `g ≥ 2`.

`h0C19` is Stacks 0C19 (`AlgebraicGeometry.invertibleCurveDegree_dualizingSheafOverField`)
with the two instances its statement names and this tree does not yet have — connectedness and
invertibility of `ω_X` — quantified over; both are propositions, so the statement of 0C19
specializes to this one exactly. -/
theorem two_le_genus_of_isAmple_dualizingSheafOverField_of
    (h0C19 : ∀ (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
      [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] [IsGorenstein X]
      (hdim : topologicalKrullDim X = 1) [ConnectedSpace X]
      [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
        (Stacks.Duality.dualizingSheafOverField f)],
      invertibleCurveDegree k f hdim.le (Stacks.Duality.dualizingSheafOverField f) =
        2 * (genus f : ℤ) - 2)
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
    (hω : ∃ _ : SheafOfModules.IsInvertible X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))),
        Scheme.Modules.IsAmple X (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))) :
    2 ≤ genus (X ↘ Spec (.of k)) := by
  obtain ⟨hinv, hL⟩ := hω
  have : ConnectedSpace X := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
  have : IsGorenstein X := Stacks.Curves.isGorenstein_of_hasAtWorstNodalSingularities k X
    (equidimensional_of_isIso_globalSections_of_dimension_one k (X ↘ Spec (.of k)) hdim) hdim
    hnodal
  have hpos := invertibleCurveDegree_pos_of_isAmple_of_isConnected k (X ↘ Spec (.of k)) hdim
    _ hL
  rw [h0C19 k (X ↘ Spec (.of k)) hdim] at hpos
  omega

/-- **Conditions (b) and (c) of part (2) of Stacks 0E76 agree, from Stacks 0E3P and its
converse.** Let `X` be proper over a field `k` of dimension one with `H⁰(X, 𝒪_X) = k` and
at-worst-nodal singularities. Then `X` has genus at least two and neither a rational tail nor a
rational bridge exactly when `ω_X` is invertible and ample. The forward direction is
Stacks 0E3P (`h0E3P`). For the converse, rational tails and bridges are excluded by
`AlgebraicGeometry.forall_not_isRationalTail_and_not_isRationalBridge_of_isAmple_of` from
Stacks 0E63 and 0E64 (`h0E63`, `h0E64`) and Stacks 0B5Y, and the genus bound is
`AlgebraicGeometry.two_le_genus_of_isAmple_dualizingSheafOverField_of` from Stacks 0C19
(`h0C19`). -/
theorem hasGenusTwoNoRationalTailNoRationalBridge_iff_isAmple_dualizingSheafOverField_of
    (h0E3P : ∀ (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [IsProper (X ↘ Spec (.of k))] (hdim : topologicalKrullDim X = 1)
      [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
      (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
      (htail : ∀ C : X.IdealSheafData, ¬ IsRationalTail k X C)
      (hbridge : ∀ C : X.IdealSheafData, ¬ IsRationalBridge k X C)
      (hg : 2 ≤ genus (X ↘ Spec (.of k))),
      ∃ _ : SheafOfModules.IsInvertible X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))),
        Scheme.Modules.IsAmple X (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))))
    (h0E63 : ∀ (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [IsProper (X ↘ Spec (.of k))] (hdim : topologicalKrullDim X = 1)
      [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
      (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
      (C : X.IdealSheafData) (hC : IsRationalTail k X C)
      (hCdim : topologicalKrullDim C.subscheme ≤ 1)
      [SheafOfModules.IsInvertible C.subscheme.presheaf C.subscheme.ringCatSheaf.2
        ((Scheme.Modules.pullback C.subschemeι).obj
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))))],
      invertibleCurveDegree k (C.subschemeι ≫ (X ↘ Spec (.of k))) hCdim
        ((Scheme.Modules.pullback C.subschemeι).obj
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))) < 0)
    (h0E64 : ∀ (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [IsProper (X ↘ Spec (.of k))] (hdim : topologicalKrullDim X = 1)
      [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
      (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
      (C : X.IdealSheafData) (hC : IsRationalBridge k X C)
      (hCdim : topologicalKrullDim C.subscheme ≤ 1)
      [SheafOfModules.IsInvertible C.subscheme.presheaf C.subscheme.ringCatSheaf.2
        ((Scheme.Modules.pullback C.subschemeι).obj
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))))],
      invertibleCurveDegree k (C.subschemeι ≫ (X ↘ Spec (.of k))) hCdim
        ((Scheme.Modules.pullback C.subschemeι).obj
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))) = 0)
    (h0C19 : ∀ (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
      [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] [IsGorenstein X]
      (hdim : topologicalKrullDim X = 1) [ConnectedSpace X]
      [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
        (Stacks.Duality.dualizingSheafOverField f)],
      invertibleCurveDegree k f hdim.le (Stacks.Duality.dualizingSheafOverField f) =
        2 * (genus f : ℤ) - 2)
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim X = 1)
    (hglob : Function.Bijective f.appTop)
    (hnodal : letI : X.Over (Spec (.of k)) := ⟨f⟩
      Stacks.Curves.HasAtWorstNodalSingularities k X) :
    HasGenusTwoNoRationalTailNoRationalBridge k f ↔
      ∃ _ : SheafOfModules.IsInvertible X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property
          (Stacks.Duality.dualizingSheafOverField f),
        Scheme.Modules.IsAmple X (Stacks.Duality.dualizingSheafOverField f) := by
  let : X.Over (Spec (.of k)) := ⟨f⟩
  have : IsProper (X ↘ Spec (.of k)) := inferInstanceAs (IsProper f)
  have : IsIso f.appTop := (ConcreteCategory.isIso_iff_bijective f.appTop).2 hglob
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop) :=
    inferInstanceAs (IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop))
  refine ⟨fun ⟨hg, htail, hbridge⟩ => h0E3P k X hdim hnodal htail hbridge.snd hg, fun hω => ?_⟩
  obtain ⟨htail, hbridge⟩ :=
    forall_not_isRationalTail_and_not_isRationalBridge_of_isAmple_of h0E63 h0E64 k X hdim hnodal hω
  exact ⟨two_le_genus_of_isAmple_dualizingSheafOverField_of h0C19 k X hdim hnodal hω, htail,
    inferInstance, hbridge⟩

/-! ### The fibre conditions under extension of the ground field -/

/-- **At-worst-nodal singularities pass to every base change along a field extension.** For a
proper scheme `X` of dimension one over `k` with `H⁰(X, 𝒪_X) = k` and at-worst-nodal
singularities, and any presentation `X'` of the base change `X ×_k K` along a field extension
`K/k`, the singularities of `X'` over `K` are at-worst-nodal. The chosen fibre product is nodal by
`Stacks.Curves.hasAtWorstNodalSingularities_baseChange`, and the dichotomy "smooth or a node" is
carried across the isomorphism with `X'` by `Stacks.Curves.smoothAt_or_isNode_of_etale_of_comm`. -/
theorem hasAtWorstNodalSingularities_of_isPullback_of_isProper (k K : Type u) [Field k] [Field K]
    [Algebra k K] {X X' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Spec (.of K))
    (f : X ⟶ Spec (.of k)) (h : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    [IsProper f] [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    (hdim : topologicalKrullDim X = 1)
    (hnodal : letI : X.Over (Spec (.of k)) := ⟨f⟩
      Stacks.Curves.HasAtWorstNodalSingularities k X) :
    letI : X'.Over (Spec (.of K)) := ⟨f'⟩
    Stacks.Curves.HasAtWorstNodalSingularities K X' := by
  let : X.Over (Spec (.of k)) := ⟨f⟩
  let : X'.Over (Spec (.of K)) := ⟨f'⟩
  let γ : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have : LocallyOfFiniteType (X ↘ Spec (.of k)) := inferInstanceAs (LocallyOfFiniteType f)
  have hP := Stacks.Curves.hasAtWorstNodalSingularities_baseChange k K X
    (equidimensional_of_isIso_globalSections_of_dimension_one k f hdim) hdim hnodal
  have : LocallyOfFiniteType f' := MorphismProperty.of_isPullback h inferInstance
  have hdimP : topologicalKrullDim (pullback f γ : Scheme.{u}) = 1 :=
    (topologicalKrullDim_baseChange k K _ _ f (IsPullback.of_hasPullback f γ)).trans hdim
  have hdimX' : topologicalKrullDim X' = 1 :=
    (topologicalKrullDim_baseChange k K g' f' f h).trans hdim
  intro x hx
  have hcomm : 𝟙 X' ≫ f' = h.isoPullback.hom ≫ pullback.snd f γ := by
    rw [Category.id_comp, IsPullback.isoPullback_hom_snd]
  have hxc : IsClosed ({h.isoPullback.hom.base x} : Set (pullback f γ : Scheme.{u})) := by
    rw [← Set.image_singleton]
    exact h.isoPullback.hom.isClosedEmbedding.isClosedMap _ hx
  exact Stacks.Curves.smoothAt_or_isNode_of_etale_of_comm K (pullback.snd f γ) f' hdimP hdimX'
    h.isoPullback.hom (𝟙 X') hcomm x (hP _ hxc)

/-- **Conditions (b) of part (2) of Stacks 0E76, other than the genus and the absence of tails
and bridges, pass to every base change along a field extension**: properness, `dim = 1`,
`H⁰ = K` (Stacks 0BY9) and at-worst-nodal singularities
(`AlgebraicGeometry.hasAtWorstNodalSingularities_of_isPullback_of_isProper`). -/
theorem isProper_and_isIso_globalSections_and_dim_and_nodal_of_isPullback (k K : Type u)
    [Field k] [Field K] [Algebra k K] {X X' : Scheme.{u}} (g' : X' ⟶ X)
    (f' : X' ⟶ Spec (.of K)) (f : X ⟶ Spec (.of k))
    (h : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    [IsProper f] [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    (hdim : topologicalKrullDim X = 1)
    (hnodal : letI : X.Over (Spec (.of k)) := ⟨f⟩
      Stacks.Curves.HasAtWorstNodalSingularities k X) :
    IsProper f' ∧ IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ f'.appTop) ∧
      topologicalKrullDim X' = 1 ∧
      @Stacks.Curves.HasAtWorstNodalSingularities K _ X' ⟨f'⟩ :=
  ⟨isProper_of_isPullback_specMapAlgebraMap k K g' f' f h,
    isIso_globalSections_baseChange k K g' f' f h,
    (topologicalKrullDim_baseChange k K g' f' f h).trans hdim,
    hasAtWorstNodalSingularities_of_isPullback_of_isProper k K g' f' f h hdim hnodal⟩

/-- **A stable curve stays stable under extension of the ground field.** Let `X` be proper over
`k` of dimension one with `H⁰(X, 𝒪_X) = k` and at-worst-nodal singularities, of genus at least two
and with neither a rational tail nor a rational bridge, and let `X'` present the base change
`X ×_k K` along a field extension `K/k`. Then `X'` over `K` has genus at least two and neither a
rational tail nor a rational bridge.

The genus is unchanged (Stacks 0BY9). By Stacks 0E3P (`h0E3P`) `ω_X` is invertible and ample; its
pullback to `X'` is ample, the projection `X' ⟶ X` being affine, and is `ω_{X'}` (Stacks 0E32,
`hbc`, in the shape of `Stacks.Duality.dualizingSheafOverFieldBaseChangeIso`). So `ω_{X'}`
is invertible and ample, and `X'` — again nodal, of dimension one with `H⁰ = K` — has neither a
rational tail nor a rational bridge by
`AlgebraicGeometry.forall_not_isRationalTail_and_not_isRationalBridge_of_isAmple_of`. This is the
source's "ampleness is insensitive to base field extensions". -/
theorem hasGenusTwoNoRationalTailNoRationalBridge_of_isPullback_of
    (h0E3P : ∀ (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [IsProper (X ↘ Spec (.of k))] (hdim : topologicalKrullDim X = 1)
      [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
      (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
      (htail : ∀ C : X.IdealSheafData, ¬ IsRationalTail k X C)
      (hbridge : ∀ C : X.IdealSheafData, ¬ IsRationalBridge k X C)
      (hg : 2 ≤ genus (X ↘ Spec (.of k))),
      ∃ _ : SheafOfModules.IsInvertible X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))),
        Scheme.Modules.IsAmple X (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))))
    (h0E63 : ∀ (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [IsProper (X ↘ Spec (.of k))] (hdim : topologicalKrullDim X = 1)
      [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
      (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
      (C : X.IdealSheafData) (hC : IsRationalTail k X C)
      (hCdim : topologicalKrullDim C.subscheme ≤ 1)
      [SheafOfModules.IsInvertible C.subscheme.presheaf C.subscheme.ringCatSheaf.2
        ((Scheme.Modules.pullback C.subschemeι).obj
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))))],
      invertibleCurveDegree k (C.subschemeι ≫ (X ↘ Spec (.of k))) hCdim
        ((Scheme.Modules.pullback C.subschemeι).obj
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))) < 0)
    (h0E64 : ∀ (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [IsProper (X ↘ Spec (.of k))] (hdim : topologicalKrullDim X = 1)
      [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
      (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
      (C : X.IdealSheafData) (hC : IsRationalBridge k X C)
      (hCdim : topologicalKrullDim C.subscheme ≤ 1)
      [SheafOfModules.IsInvertible C.subscheme.presheaf C.subscheme.ringCatSheaf.2
        ((Scheme.Modules.pullback C.subschemeι).obj
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))))],
      invertibleCurveDegree k (C.subschemeι ≫ (X ↘ Spec (.of k))) hCdim
        ((Scheme.Modules.pullback C.subschemeι).obj
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))) = 0)
    (hbc : ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] {X X' : Scheme.{u}}
      (f : X ⟶ Spec (.of k)) [IsProper f] (g' : X' ⟶ X) (f' : X' ⟶ Spec (.of K))
      (h : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (algebraMap k K)))),
      haveI := isProper_of_isPullback_specMapAlgebraMap k K g' f' f h
      Nonempty ((Scheme.Modules.pullback g').obj (Stacks.Duality.dualizingSheafOverField f) ≅
        Stacks.Duality.dualizingSheafOverField f'))
    (k K : Type u) [Field k] [Field K] [Algebra k K] {X X' : Scheme.{u}} (g' : X' ⟶ X)
    (f' : X' ⟶ Spec (.of K)) (f : X ⟶ Spec (.of k))
    (h : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    [IsProper f] [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    (hdim : topologicalKrullDim X = 1)
    (hnodal : letI : X.Over (Spec (.of k)) := ⟨f⟩
      Stacks.Curves.HasAtWorstNodalSingularities k X)
    (hst : HasGenusTwoNoRationalTailNoRationalBridge k f) :
    HasGenusTwoNoRationalTailNoRationalBridge K f' := by
  obtain ⟨hp', hgl', hdim', hnodal'⟩ :=
    isProper_and_isIso_globalSections_and_dim_and_nodal_of_isPullback k K g' f' f h hdim hnodal
  let : X.Over (Spec (.of k)) := ⟨f⟩
  let : X'.Over (Spec (.of K)) := ⟨f'⟩
  have : IsProper (X ↘ Spec (.of k)) := inferInstanceAs (IsProper f)
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop) :=
    inferInstanceAs (IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop))
  have := hp'
  have : IsProper (X' ↘ Spec (.of K)) := inferInstanceAs (IsProper f')
  have : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ (X' ↘ Spec (.of K)).appTop) := hgl'
  obtain ⟨hg, htail, hbridge⟩ := hst
  obtain ⟨hinv, hamp⟩ := h0E3P k X hdim hnodal htail hbridge.snd hg
  have : SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property (Stacks.Duality.dualizingSheafOverField f) :=
    hinv
  have hamp₀ : Scheme.Modules.IsAmple X (Stacks.Duality.dualizingSheafOverField f) := hamp
  obtain ⟨φ⟩ := hbc f g' f' h
  have : IsAffineHom g' := MorphismProperty.of_isPullback h.flip inferInstance
  have : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace f'
  have hinvP : SheafOfModules.IsInvertible X'.toRingedSpace.presheaf
      (structureSheafRing X'.toRingedSpace).property
      ((Scheme.Modules.pullback g').obj (Stacks.Duality.dualizingSheafOverField f)) :=
    SheafOfModules.isInvertible_pullback g' _
  have hinv' : SheafOfModules.IsInvertible X'.toRingedSpace.presheaf
      (structureSheafRing X'.toRingedSpace).property (Stacks.Duality.dualizingSheafOverField f') :=
    Stacks.UFDExtensionGlobal.isInvertible_of_iso φ hinvP
  have hamp' : Scheme.Modules.IsAmple X' (Stacks.Duality.dualizingSheafOverField f') :=
    Scheme.Modules.isAmple_of_iso φ (Scheme.Modules.isAmple_pullback_of_isAffineHom g' _ hamp₀)
  obtain ⟨htail', hbridge'⟩ := forall_not_isRationalTail_and_not_isRationalBridge_of_isAmple_of
    h0E63 h0E64 K X' hdim' hnodal' ⟨hinv', hamp'⟩
  exact ⟨(genus_baseChange k K g' f' f h).symm ▸ hg, htail', inferInstance, hbridge'⟩

/-- **The fibre conditions descend along an isomorphism over the field.** Let `T` be proper over
`k` of dimension one with `H⁰(T, 𝒪_T) = k` and at-worst-nodal singularities, and let `e : V ≅ T`
be an isomorphism over `k`. If `V` has genus at least two and neither a rational tail nor a
rational bridge, so has `T`: `V` is the base change of `T` along the identity of `k`, hence again
nodal of dimension one with `H⁰ = k`, and `T` is in turn the base change of `V`, so
`AlgebraicGeometry.hasGenusTwoNoRationalTailNoRationalBridge_of_isPullback_of` applies. -/
theorem hasGenusTwoNoRationalTailNoRationalBridge_of_iso_of
    (h0E3P : ∀ (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [IsProper (X ↘ Spec (.of k))] (hdim : topologicalKrullDim X = 1)
      [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
      (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
      (htail : ∀ C : X.IdealSheafData, ¬ IsRationalTail k X C)
      (hbridge : ∀ C : X.IdealSheafData, ¬ IsRationalBridge k X C)
      (hg : 2 ≤ genus (X ↘ Spec (.of k))),
      ∃ _ : SheafOfModules.IsInvertible X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))),
        Scheme.Modules.IsAmple X (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))))
    (h0E63 : ∀ (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [IsProper (X ↘ Spec (.of k))] (hdim : topologicalKrullDim X = 1)
      [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
      (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
      (C : X.IdealSheafData) (hC : IsRationalTail k X C)
      (hCdim : topologicalKrullDim C.subscheme ≤ 1)
      [SheafOfModules.IsInvertible C.subscheme.presheaf C.subscheme.ringCatSheaf.2
        ((Scheme.Modules.pullback C.subschemeι).obj
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))))],
      invertibleCurveDegree k (C.subschemeι ≫ (X ↘ Spec (.of k))) hCdim
        ((Scheme.Modules.pullback C.subschemeι).obj
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))) < 0)
    (h0E64 : ∀ (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [IsProper (X ↘ Spec (.of k))] (hdim : topologicalKrullDim X = 1)
      [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
      (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
      (C : X.IdealSheafData) (hC : IsRationalBridge k X C)
      (hCdim : topologicalKrullDim C.subscheme ≤ 1)
      [SheafOfModules.IsInvertible C.subscheme.presheaf C.subscheme.ringCatSheaf.2
        ((Scheme.Modules.pullback C.subschemeι).obj
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))))],
      invertibleCurveDegree k (C.subschemeι ≫ (X ↘ Spec (.of k))) hCdim
        ((Scheme.Modules.pullback C.subschemeι).obj
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))) = 0)
    (hbc : ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] {X X' : Scheme.{u}}
      (f : X ⟶ Spec (.of k)) [IsProper f] (g' : X' ⟶ X) (f' : X' ⟶ Spec (.of K))
      (h : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (algebraMap k K)))),
      haveI := isProper_of_isPullback_specMapAlgebraMap k K g' f' f h
      Nonempty ((Scheme.Modules.pullback g').obj (Stacks.Duality.dualizingSheafOverField f) ≅
        Stacks.Duality.dualizingSheafOverField f'))
    (k : Type u) [Field k] {V T : Scheme.{u}} (fV : V ⟶ Spec (.of k)) (fT : T ⟶ Spec (.of k))
    (e : V ≅ T) (he : e.hom ≫ fT = fV)
    [IsProper fT] [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ fT.appTop)]
    (hdim : topologicalKrullDim T = 1)
    (hnodal : letI : T.Over (Spec (.of k)) := ⟨fT⟩
      Stacks.Curves.HasAtWorstNodalSingularities k T)
    (hst : HasGenusTwoNoRationalTailNoRationalBridge k fV) :
    HasGenusTwoNoRationalTailNoRationalBridge k fT := by
  have : IsIso (Spec.map (CommRingCat.ofHom (algebraMap k k))) :=
    inferInstanceAs (IsIso (Spec.map (𝟙 (CommRingCat.of k))))
  have hγ : Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 (Spec (.of k)) :=
    Spec.map_id _
  have hV : IsPullback e.hom fV fT (Spec.map (CommRingCat.ofHom (algebraMap k k))) :=
    IsPullback.of_horiz_isIso ⟨by rw [he, hγ, Category.comp_id]⟩
  have hT : IsPullback e.inv fT fV (Spec.map (CommRingCat.ofHom (algebraMap k k))) :=
    IsPullback.of_horiz_isIso ⟨by rw [← he, Iso.inv_hom_id_assoc, hγ, Category.comp_id]⟩
  obtain ⟨hpV, hglV, hdimV, hnodalV⟩ :=
    isProper_and_isIso_globalSections_and_dim_and_nodal_of_isPullback k k e.hom fV fT hV hdim
      hnodal
  have := hpV
  have := hglV
  exact hasGenusTwoNoRationalTailNoRationalBridge_of_isPullback_of h0E3P h0E63 h0E64 hbc k k
    e.inv fT fV hT hdimV hnodalV hst
variable (B hZ) in
/-- **The fibre conditions on the family of a proper curve over a field.** Let `g : T ⟶ W` be a
proper morphism of the site with `W = Spec k`, and suppose `X = T` is nodal of dimension one with
`H⁰(X, 𝒪_X) = k`. Then every fibre of the family of curves of `X` over a field-valued point has
genus at least two and neither a rational tail nor a rational bridge exactly when `X` does.

The fibre over `Spec K → Spec k` is presented by the fibre product `T ×_W Spec K` of the site,
which Yoneda preserves and whose underlying scheme is a base change `X ×_k K`; stability passes
to it by `AlgebraicGeometry.hasGenusTwoNoRationalTailNoRationalBridge_of_isPullback_of`.
Conversely, a presentation of the fibre over the tautological point `Spec k = W` is isomorphic to
`X` over `k`, and stability descends along that isomorphism
(`AlgebraicGeometry.hasGenusTwoNoRationalTailNoRationalBridge_of_iso_of`). The inputs are
Stacks 0E3P (`h0E3P`), Stacks 0E63 and 0E64 (`h0E63`, `h0E64`) and part (2) of Stacks 0E32 for the
dualizing sheaf (`hbc`), each in the shape of its statement. -/
theorem hasStableFibres_curveFamilyOverFieldOfProper_iff_of
    (h0E3P : ∀ (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [IsProper (X ↘ Spec (.of k))] (hdim : topologicalKrullDim X = 1)
      [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
      (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
      (htail : ∀ C : X.IdealSheafData, ¬ IsRationalTail k X C)
      (hbridge : ∀ C : X.IdealSheafData, ¬ IsRationalBridge k X C)
      (hg : 2 ≤ genus (X ↘ Spec (.of k))),
      ∃ _ : SheafOfModules.IsInvertible X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))),
        Scheme.Modules.IsAmple X (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))))
    (h0E63 : ∀ (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [IsProper (X ↘ Spec (.of k))] (hdim : topologicalKrullDim X = 1)
      [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
      (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
      (C : X.IdealSheafData) (hC : IsRationalTail k X C)
      (hCdim : topologicalKrullDim C.subscheme ≤ 1)
      [SheafOfModules.IsInvertible C.subscheme.presheaf C.subscheme.ringCatSheaf.2
        ((Scheme.Modules.pullback C.subschemeι).obj
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))))],
      invertibleCurveDegree k (C.subschemeι ≫ (X ↘ Spec (.of k))) hCdim
        ((Scheme.Modules.pullback C.subschemeι).obj
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))) < 0)
    (h0E64 : ∀ (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [IsProper (X ↘ Spec (.of k))] (hdim : topologicalKrullDim X = 1)
      [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
      (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
      (C : X.IdealSheafData) (hC : IsRationalBridge k X C)
      (hCdim : topologicalKrullDim C.subscheme ≤ 1)
      [SheafOfModules.IsInvertible C.subscheme.presheaf C.subscheme.ringCatSheaf.2
        ((Scheme.Modules.pullback C.subschemeι).obj
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))))],
      invertibleCurveDegree k (C.subschemeι ≫ (X ↘ Spec (.of k))) hCdim
        ((Scheme.Modules.pullback C.subschemeι).obj
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))) = 0)
    (hbc : ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] {X X' : Scheme.{u}}
      (f : X ⟶ Spec (.of k)) [IsProper f] (g' : X' ⟶ X) (f' : X' ⟶ Spec (.of K))
      (h : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (algebraMap k K)))),
      haveI := isProper_of_isPullback_specMapAlgebraMap k K g' f' f h
      Nonempty ((Scheme.Modules.pullback g').obj (Stacks.Duality.dualizingSheafOverField f) ≅
        Stacks.Duality.dualizingSheafOverField f'))
    (k : Type u) [Field k] {T W : BigFppfOver B integerBase hZ} (g : T ⟶ W)
    (hW : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k))
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1) :
    letI : ((BigFppfOver.toScheme B integerBase hZ).obj T).Over (Spec (.of k)) :=
      ⟨(BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW⟩
    (Stacks.Curves.HasAtWorstNodalSingularities k
        ((BigFppfOver.toScheme B integerBase hZ).obj T) ∧
      topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) = 1 ∧
      Function.Bijective
        ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW).appTop) →
    (CurveFamily.HasStableFibres B hZ (curveFamilyOverFieldOfProper B hZ g k hW hproper hdim) ↔
      HasGenusTwoNoRationalTailNoRationalBridge k
        ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW)) := by
  rintro ⟨hnodal, hdim1, hglob⟩
  rcases W with ⟨⟨W0, hW0⟩, ⟨⟨⟩⟩, Wh⟩
  change W0 = Spec (.of k) at hW
  subst hW
  simp only [eqToHom_refl, Category.comp_id] at hnodal hglob ⊢
  have := hproper
  have : IsIso ((BigFppfOver.toScheme B integerBase hZ).map g).appTop :=
    (ConcreteCategory.isIso_iff_bijective _).2 hglob
  have hσ : ∀ {U V : BigFppfOver B integerBase hZ} (v : (yoneda.obj V).obj (Opposite.op U)),
      yonedaEquiv.symm v = yoneda.map v := fun v =>
    yonedaEquiv.symm_apply_eq.mpr (yonedaEquiv_yoneda_map _).symm
  constructor
  · intro hS
    let p₀ : Space.FieldValuedPoint B integerBase hZ
        (schemeSpace (Over.mk Wh : BigFppfOver B integerBase hZ)).obj :=
      { carrier := k
        contained := hW0
        toBase := Wh.hom
        value := 𝟙 (Over.mk Wh : BigFppfOver B integerBase hZ) }
    obtain ⟨V, v₁, q₁, hpb, hV⟩ := hS p₀
    let q : yoneda.obj V ⟶ yoneda.obj T := q₁
    let v : V ⟶ (Over.mk Wh : BigFppfOver B integerBase hZ) := v₁
    have hpb' : IsPullback q (yoneda.map v) (yoneda.map g)
        (𝟙 (yoneda.obj (Over.mk Wh : BigFppfOver B integerBase hZ))) := by
      have h1 : yonedaEquiv.symm p₀.value =
          𝟙 (yoneda.obj (Over.mk Wh : BigFppfOver B integerBase hZ)) :=
        (hσ (U := (Over.mk Wh : BigFppfOver B integerBase hZ))
          (V := (Over.mk Wh : BigFppfOver B integerBase hZ)) (𝟙 _)).trans (yoneda.map_id _)
      rwa [← h1]
    have : IsIso q := hpb'.isIso_fst_of_isIso (IsIso.id _)
    let q' : V ⟶ T := Yoneda.fullyFaithful.preimage q
    have hq : yoneda.map q' = q := Yoneda.fullyFaithful.map_preimage q
    have : IsIso (yoneda.map q') := hq ▸ inferInstance
    have : IsIso q' := isIso_of_fully_faithful yoneda q'
    have hq'g : q' ≫ g = v := yoneda.map_injective (by
      rw [Functor.map_comp, hq]
      simpa using hpb'.w)
    let e := (BigFppfOver.toScheme B integerBase hZ).mapIso (asIso q')
    have he : e.hom ≫ (BigFppfOver.toScheme B integerBase hZ).map g =
        (BigFppfOver.toScheme B integerBase hZ).map v := by
      show (BigFppfOver.toScheme B integerBase hZ).map q' ≫ _ = _
      rw [← Functor.map_comp, hq'g]
    exact hasGenusTwoNoRationalTailNoRationalBridge_of_iso_of h0E3P h0E63 h0E64 hbc k
      ((BigFppfOver.toScheme B integerBase hZ).map v) _ e he hdim1 hnodal hV
  · intro hT p
    let v : p.siteObject ⟶ (Over.mk Wh : BigFppfOver B integerBase hZ) := p.value
    refine ⟨pullback g v, pullback.snd g v, yoneda.map (pullback.fst g v), ?_, ?_⟩
    · show IsPullback (yoneda.map (pullback.fst g v)) (yoneda.map (pullback.snd g v))
        (yoneda.map g) (yonedaEquiv.symm v)
      rw [hσ]
      exact (IsPullback.of_hasPullback g v).map yoneda
    · let γ : Spec (.of p.carrier) ⟶ Spec (.of k) := (BigFppfOver.toScheme B integerBase hZ).map v
      let : Algebra k p.carrier := (Spec.preimage γ).hom.toAlgebra
      have hγ : Spec.map (CommRingCat.ofHom (algebraMap k p.carrier)) = γ := by
        show Spec.map (CommRingCat.ofHom (Spec.preimage γ).hom) = γ
        rw [CommRingCat.ofHom_hom, Spec.map_preimage]
      have h' : IsPullback ((BigFppfOver.toScheme B integerBase hZ).map (pullback.fst g v))
          ((BigFppfOver.toScheme B integerBase hZ).map (pullback.snd g v))
          ((BigFppfOver.toScheme B integerBase hZ).map g)
          (Spec.map (CommRingCat.ofHom (algebraMap k p.carrier))) := by
        rw [hγ]
        exact (IsPullback.of_hasPullback g v).map (BigFppfOver.toScheme B integerBase hZ)
      exact hasGenusTwoNoRationalTailNoRationalBridge_of_isPullback_of h0E3P h0E63 h0E64 hbc k
        p.carrier _ _ _ h' hdim1 hnodal hT

variable (B hZ) in
/-- **Part (2) of Stacks 0E76 read on the family of a proper scheme over a field.** Let
`g : T ⟶ W` be a proper morphism of the site with `W = Spec k`, `X = T` of dimension at most one.
Its family of curves is stable exactly when the singularities of `X` are at-worst-nodal,
`dim(X) = 1`, `k = H⁰(X, 𝒪_X)`, and `X` has genus at least two and neither a rational tail nor a
rational bridge.

The inputs are those of part (2) of Stacks 0E6U (`hpush`, `hsch`) and those of
`AlgebraicGeometry.hasStableFibres_curveFamilyOverFieldOfProper_iff_of` (`h0E3P`, `h0E63`,
`h0E64`, `hbc`), which proves the fibre conditions: the fibre of the family over a field-valued
point `Spec K → Spec k` is `X_K`. -/
theorem isStableCurveFamily_curveFamilyOverFieldOfProper_iff_of
    (hpush : ∀ X : CurveFamily B hZ, CurveFamily.HasBijectiveGlobalFunctionsOnFieldFibres B hZ X →
      HasUniversallyBijectiveGlobalFunctions B hZ X)
    (hsch : ∀ (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [LocallyOfFiniteType (X ↘ Spec (.of k))],
      IsAtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of k)) ↔
        (Stacks.Curves.HasAtWorstNodalSingularities k X ∧ TopologicalSpace.Equidimensional X ∧
          ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = (1 : WithBot ℕ∞)))
    (h0E3P : ∀ (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [IsProper (X ↘ Spec (.of k))] (hdim : topologicalKrullDim X = 1)
      [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
      (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
      (htail : ∀ C : X.IdealSheafData, ¬ IsRationalTail k X C)
      (hbridge : ∀ C : X.IdealSheafData, ¬ IsRationalBridge k X C)
      (hg : 2 ≤ genus (X ↘ Spec (.of k))),
      ∃ _ : SheafOfModules.IsInvertible X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))),
        Scheme.Modules.IsAmple X (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))))
    (h0E63 : ∀ (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [IsProper (X ↘ Spec (.of k))] (hdim : topologicalKrullDim X = 1)
      [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
      (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
      (C : X.IdealSheafData) (hC : IsRationalTail k X C)
      (hCdim : topologicalKrullDim C.subscheme ≤ 1)
      [SheafOfModules.IsInvertible C.subscheme.presheaf C.subscheme.ringCatSheaf.2
        ((Scheme.Modules.pullback C.subschemeι).obj
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))))],
      invertibleCurveDegree k (C.subschemeι ≫ (X ↘ Spec (.of k))) hCdim
        ((Scheme.Modules.pullback C.subschemeι).obj
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))) < 0)
    (h0E64 : ∀ (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [IsProper (X ↘ Spec (.of k))] (hdim : topologicalKrullDim X = 1)
      [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
      (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
      (C : X.IdealSheafData) (hC : IsRationalBridge k X C)
      (hCdim : topologicalKrullDim C.subscheme ≤ 1)
      [SheafOfModules.IsInvertible C.subscheme.presheaf C.subscheme.ringCatSheaf.2
        ((Scheme.Modules.pullback C.subschemeι).obj
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))))],
      invertibleCurveDegree k (C.subschemeι ≫ (X ↘ Spec (.of k))) hCdim
        ((Scheme.Modules.pullback C.subschemeι).obj
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))) = 0)
    (hbc : ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] {X X' : Scheme.{u}}
      (f : X ⟶ Spec (.of k)) [IsProper f] (g' : X' ⟶ X) (f' : X' ⟶ Spec (.of K))
      (h : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (algebraMap k K)))),
      haveI := isProper_of_isPullback_specMapAlgebraMap k K g' f' f h
      Nonempty ((Scheme.Modules.pullback g').obj (Stacks.Duality.dualizingSheafOverField f) ≅
        Stacks.Duality.dualizingSheafOverField f'))
    (k : Type u) [Field k] {T W : BigFppfOver B integerBase hZ} (g : T ⟶ W)
    (hW : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k))
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1) :
    letI : ((BigFppfOver.toScheme B integerBase hZ).obj T).Over (Spec (.of k)) :=
      ⟨(BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW⟩
    IsStableCurveFamily B hZ (curveFamilyOverFieldOfProper B hZ g k hW hproper hdim) ↔
      ((Stacks.Curves.HasAtWorstNodalSingularities k
          ((BigFppfOver.toScheme B integerBase hZ).obj T) ∧
        topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) = 1 ∧
        Function.Bijective
          ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW).appTop) ∧
        HasGenusTwoNoRationalTailNoRationalBridge k
          ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW)) := by
  have := hproper
  have hfl := flat_and_locallyOfFinitePresentation_of_obj_eq_specField g k hW hproper
  have hqc := Space.isQuasiCompact_yoneda_map B integerBase hZ g inferInstance
  have hsep := (Space.isSeparated_yoneda_map_iff B integerBase hZ g).mpr inferInstance
  have hqsep := (Space.isQuasiSeparated_yoneda_map_iff B integerBase hZ g).mpr inferInstance
  have hpre := isPrestableCurveFamily_curveFamilyOfSchemeMorphism_iff_of B hZ g k hW hfl.1
    hproper hfl.2 hqc hsep hqsep hdim hsch
    (CurveFamily.isH01CurveFamily_curveFamilyOfSchemeMorphism_iff_of hpush g k hW hfl.1 hproper
      hfl.2 hqc hsep hqsep hdim)
  have hfib := hasStableFibres_curveFamilyOverFieldOfProper_iff_of B hZ h0E3P h0E63 h0E64 hbc k g
    hW hproper hdim
  rw [CurveFamily.isStableCurveFamily_iff]
  exact (and_congr_left' hpre).trans (and_congr_right hfib)

/-- **Stacks 0E76, from its inputs.** There is an open substack `Curves^{stable} ⊂ Curves` — the
strictly full subcategory of stable families of curves (Stacks 0E75), whose inclusion is
representable by algebraic spaces and an open immersion — such that

1. the classifying morphism of a family of curves factors through it exactly when the family is
   stable, and
2. for a scheme `X` proper over a field `k` with `dim(X) ≤ 1` (a proper morphism `g : T ⟶ W` of
   the site with `W = Spec k`), the following are equivalent:
   (a) the classifying morphism `Spec k → Curves` of `X` factors through it,
   (b) the singularities of `X` are at-worst-nodal, `dim(X) = 1`, `k = H⁰(X, 𝒪_X)`, the genus of
   `X` is at least two, and `X` has no rational tails or bridges,
   (c) the singularities of `X` are at-worst-nodal, `dim(X) = 1`, `k = H⁰(X, 𝒪_X)`, and `ω_X` is
   (invertible and) ample;
   stated as `(a) ↔ (b)` and `(a) ↔ (c)`.

The inputs are those of Stacks 0E6U (`hopen`, `hpush`, `hsch`) and the relative openness of
stable fibres on prestable families (`hrel`, Stacks 0E74 with Stacks 0D3D). The remaining results
of other chapters that the proof uses — Stacks 0E3P, Stacks 0E63 and 0E64 (with the base's
Stacks 0B5Y), Stacks 0C19 and part (2) of Stacks 0E32 for the dualizing sheaf — are available in
the tree and are taken from there. -/
theorem curvesStable_isOpenSubstack_and_factors_iff_of_inputs
    (hopen : IsOpenCurvesLocus B hZ (CurveFamily.HasBijectiveGlobalFunctionsOnFieldFibres B hZ))
    (hpush : ∀ X : CurveFamily B hZ, CurveFamily.HasBijectiveGlobalFunctionsOnFieldFibres B hZ X →
      HasUniversallyBijectiveGlobalFunctions B hZ X)
    (hsch : ∀ (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [LocallyOfFiniteType (X ↘ Spec (.of k))],
      IsAtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of k)) ↔
        (Stacks.Curves.HasAtWorstNodalSingularities k X ∧ TopologicalSpace.Equidimensional X ∧
          ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = (1 : WithBot ℕ∞)))
    (hrel : IsOpenCurvesLocusWithin B hZ (IsPrestableCurveFamily B hZ)
      (CurveFamily.HasStableFibres B hZ)) :
    (ObjectProperty.IsClosedUnderIsomorphisms (IsStableCurveFamily B hZ) ∧
      Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (curvesSubstackInclusion B hZ (IsStableCurveFamily B hZ)
          (isOpenCurvesLocus_isStableCurveFamily_of_prestable
            (isOpenCurvesLocus_isPrestableCurveFamily_of
              (isOpenCurvesLocus_isH01CurveFamily_of hopen hpush)) hrel).prop_of_hom).hom ∧
      Stack.IsOpenImmersion B integerBase hZ
        (curvesSubstackInclusion B hZ (IsStableCurveFamily B hZ)
          (isOpenCurvesLocus_isStableCurveFamily_of_prestable
            (isOpenCurvesLocus_isPrestableCurveFamily_of
              (isOpenCurvesLocus_isH01CurveFamily_of hopen hpush)) hrel).prop_of_hom)) ∧
    (∀ (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
          ObjectProperty.FullSubcategory (IsStableCurveFamily B hZ),
          z ⋙ ObjectProperty.ι (IsStableCurveFamily B hZ) = y) ↔
        IsStableCurveFamily B hZ (y.obj (Over.mk (𝟙 U.left))))) ∧
    (∀ (k : Type u) [Field k] {T W : BigFppfOver B integerBase hZ} (g : T ⟶ W)
      (hW : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k))
      (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
      (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1)
      (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      (y.obj (Over.mk (𝟙 U.left)) ≅ curveFamilyOverFieldOfProper B hZ g k hW hproper hdim) →
      letI : ((BigFppfOver.toScheme B integerBase hZ).obj T).Over (Spec (.of k)) :=
        ⟨(BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW⟩
      (((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
          ObjectProperty.FullSubcategory (IsStableCurveFamily B hZ),
          z ⋙ ObjectProperty.ι (IsStableCurveFamily B hZ) = y) ↔
        (Stacks.Curves.HasAtWorstNodalSingularities k
            ((BigFppfOver.toScheme B integerBase hZ).obj T) ∧
          topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) = 1 ∧
          Function.Bijective
            ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW).appTop ∧
          HasGenusTwoNoRationalTailNoRationalBridge k
            ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW))) ∧
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
          ObjectProperty.FullSubcategory (IsStableCurveFamily B hZ),
          z ⋙ ObjectProperty.ι (IsStableCurveFamily B hZ) = y) ↔
        (Stacks.Curves.HasAtWorstNodalSingularities k
            ((BigFppfOver.toScheme B integerBase hZ).obj T) ∧
          topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) = 1 ∧
          Function.Bijective
            ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW).appTop ∧
          ∃ _ : SheafOfModules.IsInvertible
              ((BigFppfOver.toScheme B integerBase hZ).obj T).toRingedSpace.presheaf
              (structureSheafRing
                ((BigFppfOver.toScheme B integerBase hZ).obj T).toRingedSpace).property
              (Stacks.Duality.dualizingSheafOverField
                ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW)),
            Scheme.Modules.IsAmple ((BigFppfOver.toScheme B integerBase hZ).obj T)
              (Stacks.Duality.dualizingSheafOverField
                ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW)))))) := by
  have hPre := isOpenCurvesLocus_isPrestableCurveFamily_of
    (isOpenCurvesLocus_isH01CurveFamily_of hopen hpush)
  refine ⟨(curvesStable_isOpenSubstack_and_factors_iff_of_prestable hPre hrel).1,
    (curvesStable_isOpenSubstack_and_factors_iff_of_prestable hPre hrel).2, ?_⟩
  intro k _ T W g hW hproper hdim U y hy e
  have hstable := isStableCurveFamily_curveFamilyOverFieldOfProper_iff_of B hZ hpush hsch
    isAmple_dualizingSheafOverField_of_hasAtWorstNodalSingularities
    (fun _ _ _ _ _ hd _ hn C hC _ _ =>
      invertibleCurveDegree_pullback_dualizingSheafOverField_neg_of_isRationalTail hd hn C hC)
    (fun _ _ _ _ _ hd _ hn C hC _ _ =>
      invertibleCurveDegree_pullback_dualizingSheafOverField_eq_zero_of_isRationalBridge hd hn C hC)
    (fun f _ g' f' h => ⟨Stacks.Duality.dualizingSheafOverFieldBaseChangeIso f g' f' h⟩)
  have hample := hasGenusTwoNoRationalTailNoRationalBridge_iff_isAmple_dualizingSheafOverField_of
    isAmple_dualizingSheafOverField_of_hasAtWorstNodalSingularities
    (fun _ _ _ _ _ hd _ hn C hC _ _ =>
      invertibleCurveDegree_pullback_dualizingSheafOverField_neg_of_isRationalTail hd hn C hC)
    (fun _ _ _ _ _ hd _ hn C hC _ _ =>
      invertibleCurveDegree_pullback_dualizingSheafOverField_eq_zero_of_isRationalBridge hd hn C hC)
    (fun κ _ _ f _ _ _ hd _ _ => invertibleCurveDegree_dualizingSheafOverField κ f hd)
  rw [factors_curvesSubstack_iff_of_iso
    (isOpenCurvesLocus_isStableCurveFamily_of_prestable hPre hrel) U y hy _ e,
    hstable k g hW hproper hdim]
  exact ⟨⟨fun ⟨⟨h1, h2, h3⟩, h4⟩ => ⟨h1, h2, h3, h4⟩, fun ⟨h1, h2, h3, h4⟩ => ⟨⟨h1, h2, h3⟩, h4⟩⟩,
    fun ⟨⟨h1, h2, h3⟩, h4⟩ => ⟨h1, h2, h3, (hample k _ h2 h3 h1).1 h4⟩,
    fun ⟨h1, h2, h3, h4⟩ => ⟨⟨h1, h2, h3⟩, (hample k _ h2 h3 h1).2 h4⟩⟩

end AlgebraicGeometry

end
