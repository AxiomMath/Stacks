module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyEtaleSchemeCharts
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesOpenLocusRelative
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesPrestableGenus
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableFibreLocusScheme
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableFibreTransport
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableModelNearFibre
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilySchemeChart

/-!
# The open substack `Curves^{stable}` of stable curves (Stacks 0E76)

This file proves that the stable families of curves (Stacks 0E75) satisfy condition (o) of
Stacks 0E0E, which is the openness assertion of Stacks 0E76, following the source proof. By the
discussion of Section 0E0E it suffices to look at prestable families, prestability satisfying
condition (o). Over a prestable family `G` with base `S`, the points `s` whose fibre is a stable
curve form an open subset `Ω` of `S`:

* étale locally on `S` the total space of `G` is a scheme (Stacks 0E6F, the input `h0E6F`), so
  over an étale `U → S` whose image contains `s` the family is a proper flat morphism of schemes
  `Z → U` with nodal fibres, which over an affine open of `U` carries a relative dualizing sheaf
  `ω_{Z/U}` restricting on every fibre to its dualizing sheaf (Stacks 0E6R, the input `hω`);
* a fibre is stable exactly when `ω` is ample on it (Stacks 0E74, 0E3P), and ampleness on one
  fibre of a proper morphism spreads to a neighbourhood (Stacks 0D2S, which replaces the source's
  Stacks 0D3D for algebraic spaces on the chart), so the stable locus of `Z → U` is open
  (`AlgebraicGeometry.C1590Private.exists_isOpen_isStableCurveOver_fiber`), and its image in `S`
  is open, étale morphisms being open.

Formation of `Ω` commutes with base change because stability of a fibre is insensitive to
extensions of the ground field (Stacks 0D2P, through the ampleness of `ω`;
`AlgebraicGeometry.C1590Private.hasStableFibresAt_of_isStableCurveOver`).

## Main definitions

* `AlgebraicGeometry.C1590Private.HasNodalRelativeDualizingSheaf`: the input `hω`.

## Main results

* `AlgebraicGeometry.C1590Private.exists_isOpen_hasStableFibresAt`: over a prestable family, the
  points with stable fibres form a neighbourhood of each of them.
* `AlgebraicGeometry.C1590Private.isOpenCurvesLocus_isStableCurveFamily_of`: condition (o) for
  stable families, from condition (o) for prestable families, `h0E6F` and `hω`.

## Implementation notes

Unregistered helpers towards Stacks 0E76, which is not registered here. The inputs `h0E6F` and
`hω` are the étale local representability of families of curves (Stacks 0E6F) and the relative
dualizing sheaf of a nodal family of schemes over an affine base (Stacks 0E6P, 0E6Q, 0E6R).

## References

* [Stacks Project, Tag 0E76](https://stacks.math.columbia.edu/tag/0E76)
* [Stacks Project, Tag 0E74](https://stacks.math.columbia.edu/tag/0E74)
* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
* [Stacks Project, Tag 0E6R](https://stacks.math.columbia.edu/tag/0E6R)
* [Stacks Project, Tag 0D2S](https://stacks.math.columbia.edu/tag/0D2S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.C1590Private

universe u

attribute [local instance] Space.pointTopology

/-- **Input: the relative dualizing sheaf of a nodal family of schemes over an affine base.**
Every proper, flat, finitely presented morphism of schemes `q : Z ⟶ U` to an affine scheme which
is at-worst-nodal of relative dimension one carries an invertible module `ω` whose restriction to
every fibre `Z_u` is the dualizing sheaf of `Z_u` over `κ(u)` (Stacks 0E6P, 0E6Q, 0E6R). -/
def HasNodalRelativeDualizingSheaf : Prop :=
  ∀ ⦃Z U : Scheme.{u}⦄ (q : Z ⟶ U) [IsAffine U] [IsProper q] [Flat q]
    [LocallyOfFinitePresentation q], IsAtWorstNodalOfRelativeDimensionOne q →
    ∃ (ω : Z.Modules) (_ : SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 ω),
      ∀ u : U, Nonempty ((Scheme.Modules.pullback (q.fiberι u)).obj ω ≅
        Stacks.Duality.dualizingSheafOverField (k := U.residueField u)
          (q.fiberToSpecResidueField u))

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **The stable locus on an affine scheme chart.** Let `G` be prestable and `Z ⟶ U` a scheme
chart of `G` over a morphism `φ : U ⟶ S` from an affine scheme (a cartesian square). If the
fibres over `φ(u)` are stable, so are the fibres over `φ(u')` for every `u'` in an open
neighbourhood of `u`. -/
theorem exists_isOpen_hasStableFibresAt_of_isAffine (hω : HasNodalRelativeDualizingSheaf.{u})
    {G : CurveFamily B hZ} (hG : IsPrestableCurveFamily B hZ G) {U Z : BigFppfOver B integerBase hZ}
    {φ : U ⟶ G.base} {q : Z ⟶ U} {p : schemeSpace Z ⟶ G.total}
    (hsq : IsPullback p (schemeSpaceMap q) G.toBase (schemeSpaceMap φ))
    [IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj U)]
    (u : (BigFppfOver.toScheme B integerBase hZ).obj U)
    (hu : HasStableFibresAt G ((BigFppfOver.toScheme B integerBase hZ).map φ u)) :
    ∃ N : ((BigFppfOver.toScheme B integerBase hZ).obj U).Opens, u ∈ N ∧
      ∀ u' ∈ N, HasStableFibresAt G ((BigFppfOver.toScheme B integerBase hZ).map φ u') := by
  let T := BigFppfOver.toScheme B integerBase hZ
  have : PreservesLimitsOfShape WalkingCospan T :=
    Space.preservesLimitsOfShape_walkingCospan_toScheme B integerBase hZ
  have : Flat (T.map q) := G.flat_toScheme_map_of_isPullback hsq
  have : LocallyOfFinitePresentation (T.map q) :=
    G.locallyOfFinitePresentation_toScheme_map_of_isPullback hsq
  have : IsProper (T.map q) := G.isProper_toScheme_map_of_isPullback_schemeSpaceMap hsq
  have hnod : IsAtWorstNodalOfRelativeDimensionOne (T.map q) :=
    (Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ
      isAtWorstNodalOfRelativeDimensionOne_isEtaleLocalOnSourceAndTarget q).1
      ((Space.isAtWorstNodalOfRelativeDimensionOne_isStableUnderBaseChange B integerBase
        hZ).of_isPullback hsq hG.1)
  obtain ⟨ω, hinv, hωfib⟩ := hω (T.map q) hnod
  -- the field-valued point of `S` at the residue field of a point of the chart
  let Q : T.obj U → Space.FieldValuedPoint B integerBase hZ (schemeSpace G.base).obj := fun u' =>
    Space.FieldValuedPoint.map B integerBase hZ _ (schemeSpaceMap φ).hom
      (residueFieldValuedPoint U u')
  let ρ : ∀ u' : T.obj U, (residueFieldValuedPoint U u').siteObject ⟶ U := fun u' =>
    (residueFieldValuedPoint U u').value
  have hQ : ∀ u' x, T.map (Q u').value x = T.map φ u' := fun u' x => by
    show T.map φ ((T.obj U).fromSpecResidueField u' x) = _
    exact congrArg _ ((T.obj U).fromSpecResidueField_apply u' x)
  have hval : ∀ u', yonedaEquiv.symm (Q u').value = yoneda.map (ρ u' ≫ φ) := fun u' => by
    ext W f
    rfl
  -- the presentation of the fibre over it by the fibre of the chart
  have hpres : ∀ u', IsPullback ((schemeSpaceMap (pullback.fst q (ρ u')) ≫ p).hom)
      (yoneda.map (pullback.snd q (ρ u'))) G.toBase.hom (yonedaEquiv.symm (Q u').value) := by
    intro u'
    exact AlgebraicSpaces.isPullback_hom B integerBase hZ
      (isPullback_schemeSpaceMap_pullback_fst_comp hsq (ρ u'))
  -- it is isomorphic to the scheme-theoretic fibre of `Z ⟶ U`
  have hfibT : ∀ u', IsPullback (T.map (pullback.fst q (ρ u'))) (T.map (pullback.snd q (ρ u')))
      (T.map q) ((T.obj U).fromSpecResidueField u') := fun u' =>
    (IsPullback.of_hasPullback q (ρ u')).map T
  let e : ∀ u', T.obj (pullback q (ρ u')) ≅ (T.map q).fiber u' := fun u' => (hfibT u').isoPullback
  have he : ∀ u', (e u').hom ≫ (T.map q).fiberToSpecResidueField u' =
      T.map (pullback.snd q (ρ u')) := fun u' => (hfibT u').isoPullback_hom_snd
  have hst : ∀ u', HasStableFibresAt G (T.map φ u') ↔
      IsStableCurveOver ((T.obj U).residueField u') ((T.map q).fiberToSpecResidueField u') := by
    intro u'
    exact ⟨fun h => isStableCurveOver_of_iso (e u').symm ((Iso.inv_comp_eq _).2 (he u').symm)
        (h (Q u') (hQ u') (pullback.snd q (ρ u')) _ (hpres u')),
      fun h => hasStableFibresAt_of_isStableCurveOver hG _ (Q u') (hQ u') _ _ (hpres u')
        (isStableCurveOver_of_iso (e u') (he u') h)⟩
  -- the fibres of the chart are proper nodal curves with `H⁰ = κ(u)`
  have hfib : ∀ u' : T.obj U, topologicalKrullDim ((T.map q).fiber u') = 1 ∧
      IsIso ((Scheme.ΓSpecIso ((T.obj U).residueField u')).inv ≫
        ((T.map q).fiberToSpecResidueField u').appTop) ∧
      (let : ((T.map q).fiber u').Over (Spec ((T.obj U).residueField u')) :=
          ⟨(T.map q).fiberToSpecResidueField u'⟩;
        Stacks.Curves.HasAtWorstNodalSingularities ((T.obj U).residueField u')
          ((T.map q).fiber u')) := by
    intro u'
    obtain ⟨hp, hdim, hH0, hnodal⟩ :=
      fibre_properties_of_isPrestableCurveFamily hG (Q u') _ _ (hpres u')
    obtain ⟨-, h₁, h₂, h₃⟩ := prestable_properties_of_iso (e u').symm
      ((Iso.inv_comp_eq _).2 (he u').symm) ⟨hp, hdim, hH0, hnodal⟩
    exact ⟨h₁, h₂, h₃⟩
  obtain ⟨N, huN, hN⟩ := exists_isOpen_isStableCurveOver_fiber (T.map q) ω hωfib hfib u
    ((hst u).1 hu)
  exact ⟨N, huN, fun u' hu' => (hst u').2 (hN u' hu')⟩

/-- **The stable locus on a scheme chart.** As
`AlgebraicGeometry.C1590Private.exists_isOpen_hasStableFibresAt_of_isAffine`, for a chart over an
arbitrary scheme `U`: the chart is restricted to an affine open neighbourhood of `u`. -/
theorem exists_isOpen_hasStableFibresAt_of_chart (hω : HasNodalRelativeDualizingSheaf.{u})
    {G : CurveFamily B hZ} (hG : IsPrestableCurveFamily B hZ G) {U Z : BigFppfOver B integerBase hZ}
    {φ : U ⟶ G.base} {q : Z ⟶ U} {p : schemeSpace Z ⟶ G.total}
    (hsq : IsPullback p (schemeSpaceMap q) G.toBase (schemeSpaceMap φ))
    (u : (BigFppfOver.toScheme B integerBase hZ).obj U)
    (hu : HasStableFibresAt G ((BigFppfOver.toScheme B integerBase hZ).map φ u)) :
    ∃ N : ((BigFppfOver.toScheme B integerBase hZ).obj U).Opens, u ∈ N ∧
      ∀ u' ∈ N, HasStableFibresAt G ((BigFppfOver.toScheme B integerBase hZ).map φ u') := by
  let T := BigFppfOver.toScheme B integerBase hZ
  obtain ⟨A, hA, huA, -⟩ := exists_isAffineOpen_mem_and_subset (X := T.obj U) (x := u) (U := ⊤)
    trivial
  have : IsAffine A.toScheme := hA
  have hAc : B.Contains A.toScheme := B.contains_of_mono A.ι U.left.2
  -- the chart restricted to `A`
  let ι : BigFppfOver.siteObjectOver B integerBase hZ U hAc A.ι ⟶ U :=
    BigFppfOver.siteMapOver B integerBase hZ U hAc A.ι
  have : IsAffine (T.obj (BigFppfOver.siteObjectOver B integerBase hZ U hAc A.ι)) :=
    inferInstanceAs (IsAffine A.toScheme)
  obtain ⟨N, huN, hN⟩ := exists_isOpen_hasStableFibresAt_of_isAffine hω hG
    (isPullback_schemeSpaceMap_pullback_fst_comp hsq ι)
    (⟨u, huA⟩ : A.toScheme) hu
  refine ⟨A.ι ''ᵁ N, ⟨_, huN, rfl⟩, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  exact hN a ha

/-- **Over a prestable family the points with stable fibres form an open set.** If the fibres
of a prestable family `G` over a point `s` of its base are stable, so are the fibres over every
point of an open neighbourhood of `s`: on an étale scheme chart (Stacks 0E6F, `h0E6F`) this is
`AlgebraicGeometry.C1590Private.exists_isOpen_hasStableFibresAt_of_chart`, and étale morphisms
are open. -/
theorem exists_isOpen_hasStableFibresAt (h0E6F : HasEtaleLocalSchemeCharts B hZ)
    (hω : HasNodalRelativeDualizingSheaf.{u}) {G : CurveFamily B hZ}
    (hG : IsPrestableCurveFamily B hZ G) (s : (BigFppfOver.toScheme B integerBase hZ).obj G.base)
    (hs : HasStableFibresAt G s) :
    ∃ N : ((BigFppfOver.toScheme B integerBase hZ).obj G.base).Opens, s ∈ N ∧
      ∀ s' ∈ N, HasStableFibresAt G s' := by
  let T := BigFppfOver.toScheme B integerBase hZ
  obtain ⟨U, Z, φ, q, p, hφ, ⟨u, hu⟩, hsq⟩ := h0E6F G s
  have : Etale (T.map φ) := hφ
  obtain ⟨N, huN, hN⟩ := exists_isOpen_hasStableFibresAt_of_chart hω hG hsq u (hu ▸ hs)
  refine ⟨⟨T.map φ '' N, (T.map φ).isOpenMap _ N.2⟩, ⟨u, huN, hu⟩, ?_⟩
  rintro _ ⟨u', hu', rfl⟩
  exact hN u' hu'

/-- The fibre of a family of curves `F` mapping to `G` over a field-valued point `t` of its base
is, by any of its presentations, the fibre of `G` over the image of `t`. -/
theorem isPullback_map_fieldValuedPoint {F G : CurveFamily B hZ} (a : F ⟶ G)
    (t : Space.FieldValuedPoint B integerBase hZ (schemeSpace F.base).obj)
    {V : BigFppfOver B integerBase hZ} (v : V ⟶ t.siteObject) (r : yoneda.obj V ⟶ F.total.obj)
    (hr : IsPullback r (yoneda.map v) F.toBase.hom (yonedaEquiv.symm t.value)) :
    IsPullback (r ≫ a.totalMap.hom) (yoneda.map v) G.toBase.hom
      (yonedaEquiv.symm (Space.FieldValuedPoint.map B integerBase hZ _
        (schemeSpaceMap a.baseMap).hom t).value) := by
  have hval : yonedaEquiv.symm (Space.FieldValuedPoint.map B integerBase hZ _
      (schemeSpaceMap a.baseMap).hom t).value =
        yonedaEquiv.symm t.value ≫ (schemeSpaceMap a.baseMap).hom :=
    (yonedaEquiv_symm_naturality_right _ _ _).symm
  exact (congrArg (fun k => IsPullback (r ≫ a.totalMap.hom) (yoneda.map v) G.toBase.hom k)
    hval).mpr (hr.paste_horiz (AlgebraicSpaces.isPullback_hom B integerBase hZ a.cartesian))

/-- The image of a field-valued point under a morphism of families of curves is the image of the
closed point of its field spectrum. -/
theorem toScheme_map_value_map_fieldValuedPoint {F G : CurveFamily B hZ} (a : F ⟶ G)
    (t : Space.FieldValuedPoint B integerBase hZ (schemeSpace F.base).obj)
    (x : (BigFppfOver.toScheme B integerBase hZ).obj t.siteObject) :
    (BigFppfOver.toScheme B integerBase hZ).map
        (Space.FieldValuedPoint.map B integerBase hZ _ (schemeSpaceMap a.baseMap).hom t).value x =
      (BigFppfOver.toScheme B integerBase hZ).map a.baseMap
        ((BigFppfOver.toScheme B integerBase hZ).map t.value
          (IsLocalRing.closedPoint t.carrier)) := by
  have hx : x = IsLocalRing.closedPoint t.carrier :=
    Subsingleton.elim (α := Spec (CommRingCat.of t.carrier)) _ _
  subst hx
  rfl

/-- **The stable fibre locus of a prestable family is open.** -/
theorem isOpen_setOf_hasStableFibresAt (h0E6F : HasEtaleLocalSchemeCharts B hZ)
    (hω : HasNodalRelativeDualizingSheaf.{u}) {G : CurveFamily B hZ}
    (hG : IsPrestableCurveFamily B hZ G) :
    IsOpen {s : (BigFppfOver.toScheme B integerBase hZ).obj G.base | HasStableFibresAt G s} := by
  refine isOpen_iff_forall_mem_open.2 fun s hs => ?_
  obtain ⟨N, hsN, hN⟩ := exists_isOpen_hasStableFibresAt h0E6F hω hG s hs
  exact ⟨N, fun s' hs' => hN s' hs', N.2, hsN⟩

/-- **Stable fibres are read on the stable fibre locus.** A family of curves `F` mapping to a
prestable family `G` has stable fibres (condition (2) of Stacks 0E75) exactly when its morphism
of bases lands in the locus of points of the base of `G` with stable fibres. -/
theorem stableFibres_iff_range_subset {F G : CurveFamily B hZ}
    (hG : IsPrestableCurveFamily B hZ G) (a : F ⟶ G) :
    (∀ t : Space.FieldValuedPoint B integerBase hZ (schemeSpace F.base).obj,
      ∃ (V : BigFppfOver B integerBase hZ) (v : V ⟶ t.siteObject)
        (r : yoneda.obj V ⟶ F.total.obj),
        IsPullback r (yoneda.map v) F.toBase.hom (yonedaEquiv.symm t.value) ∧
          HasGenusTwoNoRationalTailNoRationalBridge t.carrier
            ((BigFppfOver.toScheme B integerBase hZ).map v)) ↔
      Set.range ((BigFppfOver.toScheme B integerBase hZ).map a.baseMap) ⊆
        {s | HasStableFibresAt G s} := by
  have hFp : IsPrestableCurveFamily B hZ F := CurveFamily.isPrestableCurveFamily_of_hom a hG
  constructor
  · rintro hF _ ⟨x, rfl⟩
    -- the fibre of `F` at the residue field of `x` is stable
    obtain ⟨V, v, r, hr, hst⟩ := hF (residueFieldValuedPoint F.base x)
    obtain ⟨hp, hdim, hH0, hnodal⟩ :=
      fibre_properties_of_isPrestableCurveFamily hFp (residueFieldValuedPoint F.base x) v r hr
    have htx : (BigFppfOver.toScheme B integerBase hZ).map
        (residueFieldValuedPoint F.base x).value
        (IsLocalRing.closedPoint (residueFieldValuedPoint F.base x).carrier) = x :=
      ((BigFppfOver.toScheme B integerBase hZ).obj F.base).fromSpecResidueField_apply x _
    show HasStableFibresAt G ((BigFppfOver.toScheme B integerBase hZ).map a.baseMap x)
    exact hasStableFibresAt_of_isStableCurveOver hG
      ((BigFppfOver.toScheme B integerBase hZ).map a.baseMap x)
      (Space.FieldValuedPoint.map B integerBase hZ _ (schemeSpaceMap a.baseMap).hom
        (residueFieldValuedPoint F.base x))
      (fun y => (toScheme_map_value_map_fieldValuedPoint a _ y).trans (congrArg _ htx)) v _
      (isPullback_map_fieldValuedPoint a _ v r hr) ⟨hp, hdim, hH0, hnodal, hst⟩
  · intro hrange t
    obtain ⟨V, v, r, hr⟩ := exists_presentation_of_fieldValuedPoint F t
    have hmem : HasStableFibresAt G ((BigFppfOver.toScheme B integerBase hZ).map a.baseMap
        ((BigFppfOver.toScheme B integerBase hZ).map t.value
          (IsLocalRing.closedPoint t.carrier))) := hrange ⟨_, rfl⟩
    exact ⟨V, v, r, hr, (hmem (Space.FieldValuedPoint.map B integerBase hZ _
      (schemeSpaceMap a.baseMap).hom t) (toScheme_map_value_map_fieldValuedPoint a t) v _
      (isPullback_map_fieldValuedPoint a t v r hr)).2.2.2.2⟩

/-- **Condition (o) of Stacks 0E0E for `Curves^{stable}`: the openness of Stacks 0E76.** From
condition (o) for prestable families (Stacks 0E6U, `hpre`), the étale local representability of
families of curves (Stacks 0E6F, `h0E6F`) and the relative dualizing sheaf of a nodal family of
schemes over an affine base (Stacks 0E6R, `hω`). As in the source proof it suffices to look at
prestable families, over which the stable locus is the open of
`AlgebraicGeometry.C1590Private.exists_isOpen_stableFibres_iff`. -/
theorem isOpenCurvesLocus_isStableCurveFamily_of
    (hpre : IsOpenCurvesLocus B hZ (IsPrestableCurveFamily B hZ))
    (h0E6F : HasEtaleLocalSchemeCharts B hZ) (hω : HasNodalRelativeDualizingSheaf.{u}) :
    IsOpenCurvesLocus B hZ (IsStableCurveFamily B hZ) := by
  refine IsOpenCurvesLocus.of_le hpre (fun _ h => h.1) fun G hG => ?_
  refine ⟨Space.schemePointsHomeomorph B integerBase hZ G.base ⁻¹' {s | HasStableFibresAt G s},
    (isOpen_setOf_hasStableFibresAt h0E6F hω hG).preimage
      (Space.schemePointsHomeomorph B integerBase hZ G.base).continuous, fun F a => ?_⟩
  refine Iff.trans ?_ (range_pointsMap_subset_preimage_iff a.baseMap _).symm
  exact ⟨fun h => (stableFibres_iff_range_subset hG a).1 h.2,
    fun h => ⟨CurveFamily.isPrestableCurveFamily_of_hom a hG,
      (stableFibres_iff_range_subset hG a).2 h⟩⟩

end AlgebraicGeometry.C1590Private

end
