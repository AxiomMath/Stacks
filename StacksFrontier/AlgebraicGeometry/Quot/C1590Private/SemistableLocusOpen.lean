module

public import StacksFrontier.AlgebraicGeometry.Duality.C1590Private.RelativeDualizingSheafNodal
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyEtaleSchemeChartsProof
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.NoRationalTailOpenScheme
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.PrestableGenusLociOpen
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.SemistableFibreLocus
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableLocusOpen

/-!
# The semistable fibre locus of a prestable family of curves is open

Let `G` be a prestable family of curves over `S`. The points of `S` whose fibre has genus at least
one and no rational tail form an open subset of `S`
(`AlgebraicGeometry.C1590Private.isOpen_semistableFibreLocus`). This is the openness in the proof
of Stacks 0E70: "By Lemma 0E6Y we obtain the desired openness of the locus in question", the
genus being locally constant on a prestable family (Stacks 0E6V).

Étale locally on `S` the family is a morphism of schemes `q : Z ⟶ U` (Stacks 0E6F, the input
`h0E6F`); restricted to an affine open of `U` on which the genus of the fibres is constant (the
genus loci are open, Stacks 0E6V, `AlgebraicGeometry.C1590Private.prestableGenusLociOpen_of`),
the locus of fibres without rational tail is open by
`AlgebraicGeometry.C1590Private.exists_isOpen_noRationalTail_of_isAffine` (Stacks 0E6Y, with the
relative dualizing sheaf of the input `hω`), and its image in `S` is open, étale
morphisms being open.

Consequently the input `AlgebraicGeometry.C1590Private.PrestableSemistableFibresOpen` of
`StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesSemistableOpen` holds, given the charts
of Stacks 0E6F (`AlgebraicGeometry.C1590Private.prestableSemistableFibresOpen_of`).

## Main results

* `AlgebraicGeometry.C1590Private.hasSemistableFibreAt_iff_of_isPullback`: the semistable fibre
  condition of a prestable family is read on any presentation of the fibre.
* `AlgebraicGeometry.C1590Private.exists_isOpen_semistableFibreLocus_of_chart`: on a scheme
  chart.
* `AlgebraicGeometry.C1590Private.isOpen_semistableFibreLocus`: the semistable fibre locus of a
  prestable family is open.
* `AlgebraicGeometry.C1590Private.prestableSemistableFibresOpen_of`: the input
  `PrestableSemistableFibresOpen`, from `h0E6F`.
* `AlgebraicGeometry.C1590Private.prestableSemistableFibresOpen`: the input, unconditionally.

## Implementation notes

Unregistered helpers. The remaining input is the étale local scheme charts of Stacks
0E6F (`AlgebraicGeometry.C1590Private.HasEtaleLocalSchemeCharts`). The relative dualizing sheaf of
a nodal family over an affine base
(`AlgebraicGeometry.C1590Private.HasNodalRelativeDualizingSheaf`, Stacks 0E6P, 0E6Q, 0E6R) is
`AlgebraicGeometry.C1590Private.hasNodalRelativeDualizingSheaf`, and the openness of the genus loci
(`AlgebraicGeometry.C1590Private.PrestableGenusLociOpen`, Stacks 0E6V) is derived from the charts.

## References

* [Stacks Project, Tag 0E70](https://stacks.math.columbia.edu/tag/0E70)
* [Stacks Project, Tag 0E6Y](https://stacks.math.columbia.edu/tag/0E6Y)
* [Stacks Project, Tag 0E6V](https://stacks.math.columbia.edu/tag/0E6V)
* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.C1590Private

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **The semistable fibre condition is read on any presentation of the fibre.** For a prestable
family, the fibre at a field-valued point has genus at least one and no rational tail exactly
when a given scheme presenting it does. -/
theorem hasSemistableFibreAt_iff_of_isPullback {G : CurveFamily B hZ}
    (hG : IsPrestableCurveFamily B hZ G)
    {P : Space.FieldValuedPoint B integerBase hZ (schemeSpace G.base).obj}
    {V : BigFppfOver B integerBase hZ} (v : V ⟶ P.siteObject) (r : yoneda.obj V ⟶ G.total.obj)
    (hV : IsPullback r (yoneda.map v) G.toBase.hom (yonedaEquiv.symm P.value)) :
    HasSemistableFibreAt G P ↔
      HasPositiveGenusNoRationalTail P.carrier ((BigFppfOver.toScheme B integerBase hZ).map v) := by
  refine ⟨fun ⟨W, w, r', hW, hP⟩ => ?_, fun h => ⟨V, v, r, hV, h⟩⟩
  exact (hasPositiveGenusNoRationalTail_iff_of_dominates hG (𝟙 _) (by simp) w r' hW v r hV).2 hP

/-- Having genus at least one and no rational tail is invariant under isomorphism over the
field. -/
theorem hasPositiveGenusNoRationalTail_iff_of_iso {k : Type u} [Field k] {W W₀ : Scheme.{u}}
    {g : W ⟶ Spec (.of k)} {g₀ : W₀ ⟶ Spec (.of k)} [IsProper g₀] (e : W ≅ W₀)
    (he : e.hom ≫ g₀ = g) :
    HasPositiveGenusNoRationalTail k g ↔ HasPositiveGenusNoRationalTail k g₀ := by
  subst he
  let : W₀.Over (Spec (.of k)) := ⟨g₀⟩
  let : W.Over (Spec (.of k)) := ⟨e.hom ≫ g₀⟩
  have : IsProper (W₀ ↘ Spec (.of k)) := ‹IsProper g₀›
  refine and_congr (by rw [genus_comp_iso_eq k g₀ e]) ?_
  exact (forall_not_isRationalTail_iff_of_isIso (k := k) (Y := W) e.hom rfl).symm

/-- **The semistable fibre locus on an affine scheme chart of constant genus.** Let `G` be
prestable and `Z ⟶ U` a scheme chart of `G` over a morphism `φ : U ⟶ S` from an affine scheme
(a cartesian square), such that the fibres of `G` over the image of `φ` all have genus `g`. If
the fibre over `φ(u)` has genus at least one and no rational tail, so has the fibre over `φ(u')`
for every `u'` in an open neighbourhood of `u`. -/
theorem exists_isOpen_semistableFibreLocus_of_isAffine (hω : HasNodalRelativeDualizingSheaf.{u})
    {G : CurveFamily B hZ} (hG : IsPrestableCurveFamily B hZ G) {U Z : BigFppfOver B integerBase hZ}
    {φ : U ⟶ G.base} {q : Z ⟶ U} {p : schemeSpace Z ⟶ G.total}
    (hsq : IsPullback p (schemeSpaceMap q) G.toBase (schemeSpaceMap φ))
    [IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj U)] {g : ℕ}
    (hgU : ∀ u', (BigFppfOver.toScheme B integerBase hZ).map φ u' ∈ G.genusLocus g)
    (u : (BigFppfOver.toScheme B integerBase hZ).obj U)
    (hu : (BigFppfOver.toScheme B integerBase hZ).map φ u ∈ semistableFibreLocus G) :
    ∃ N : ((BigFppfOver.toScheme B integerBase hZ).obj U).Opens, u ∈ N ∧
      ∀ u' ∈ N, (BigFppfOver.toScheme B integerBase hZ).map φ u' ∈ semistableFibreLocus G := by
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
  -- the field-valued point of `S` at the residue field of a point of the chart
  let Q : T.obj U → Space.FieldValuedPoint B integerBase hZ (schemeSpace G.base).obj := fun u' =>
    Space.FieldValuedPoint.map B integerBase hZ _ (schemeSpaceMap φ).hom
      (residueFieldValuedPoint U u')
  let ρ : ∀ u' : T.obj U, (residueFieldValuedPoint U u').siteObject ⟶ U := fun u' =>
    (residueFieldValuedPoint U u').value
  have hQ : ∀ u' x, T.map (Q u').value x = T.map φ u' := fun u' x => by
    show T.map φ ((T.obj U).fromSpecResidueField u' x) = _
    exact congrArg _ ((T.obj U).fromSpecResidueField_apply u' x)
  have hpt : ∀ u', Space.schemePoint B integerBase hZ G.base (Q u') = T.map φ u' := fun u' =>
    hQ u' _
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
  have hpr : ∀ u', IsProper (Y := Spec (.of ((T.obj U).residueField u')))
      ((T.map q).fiberToSpecResidueField u') := fun u' =>
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback (T.map q) _) inferInstance
  -- the semistable fibre locus and the genus loci, read on the scheme-theoretic fibres
  have hss : ∀ u', T.map φ u' ∈ semistableFibreLocus G ↔
      HasPositiveGenusNoRationalTail ((T.obj U).residueField u')
        ((T.map q).fiberToSpecResidueField u') := by
    intro u'
    obtain ⟨hdim, hH0, hnodal⟩ := hfib u'
    have h1 : HasSemistableFibreAt G (Q u') ↔
        HasPositiveGenusNoRationalTail ((T.obj U).residueField u')
          (T.map (pullback.snd q (ρ u'))) :=
      hasSemistableFibreAt_iff_of_isPullback hG _ _ (hpres u')
    have := hpr u'
    have h2 := hasPositiveGenusNoRationalTail_iff_of_iso (k := (T.obj U).residueField u')
      (e u') (he u')
    rw [← hpt u', schemePoint_mem_semistableFibreLocus_iff hG]
    exact h1.trans h2
  have hgen : ∀ u', genus ((T.map q).fiberToSpecResidueField u') = g := by
    intro u'
    have h := (CurveFamily.schemePoint_mem_genusLocus_iff
      (exists_isPullback_yoneda_fieldValuedPoint B hZ G) (Q u') g).1 (hpt u' ▸ hgU u')
    have := hpr u'
    have h2 := genus_comp_iso_eq ((T.obj U).residueField u')
      ((T.map q).fiberToSpecResidueField u') (e u')
    rw [he u'] at h2
    exact h2.symm.trans (h.genus_eq _ _ (hpres u'))
  have hg1 : 1 ≤ g := hgen u ▸ ((hss u).1 hu).1
  obtain ⟨N, huN, hN⟩ := exists_isOpen_noRationalTail_of_isAffine hω (T.map q) hnod hfib hg1
    hgen u ((hss u).1 hu)
  exact ⟨N, huN, fun u' hu' => (hss u').2 (hN u' hu')⟩

/-- **The semistable fibre locus on a scheme chart.** As
`AlgebraicGeometry.C1590Private.exists_isOpen_semistableFibreLocus_of_isAffine`, for a chart over
an arbitrary scheme `U`: the chart is restricted to an affine open neighbourhood of `u` on which
the genus of the fibres is constant, the genus loci being open (the input `hgo`). -/
theorem exists_isOpen_semistableFibreLocus_of_chart (hω : HasNodalRelativeDualizingSheaf.{u})
    (hgo : PrestableGenusLociOpen B hZ) {G : CurveFamily B hZ}
    (hG : IsPrestableCurveFamily B hZ G) {U Z : BigFppfOver B integerBase hZ}
    {φ : U ⟶ G.base} {q : Z ⟶ U} {p : schemeSpace Z ⟶ G.total}
    (hsq : IsPullback p (schemeSpaceMap q) G.toBase (schemeSpaceMap φ))
    (u : (BigFppfOver.toScheme B integerBase hZ).obj U)
    (hu : (BigFppfOver.toScheme B integerBase hZ).map φ u ∈ semistableFibreLocus G) :
    ∃ N : ((BigFppfOver.toScheme B integerBase hZ).obj U).Opens, u ∈ N ∧
      ∀ u' ∈ N, (BigFppfOver.toScheme B integerBase hZ).map φ u' ∈ semistableFibreLocus G := by
  let T := BigFppfOver.toScheme B integerBase hZ
  -- the genus locus through `u`
  obtain ⟨g, hg⟩ := exists_mem_genusLocus G (T.map φ u)
  let Vg : (T.obj U).Opens := ⟨T.map φ ⁻¹' G.genusLocus g,
    (hgo G hG g).preimage (T.map φ).continuous⟩
  obtain ⟨A, hA, huA, hAV⟩ := exists_isAffineOpen_mem_and_subset (X := T.obj U) (x := u) (U := Vg)
    hg
  have : IsAffine A.toScheme := hA
  have hAc : B.Contains A.toScheme := B.contains_of_mono A.ι U.left.2
  -- the chart restricted to `A`
  let ι : BigFppfOver.siteObjectOver B integerBase hZ U hAc A.ι ⟶ U :=
    BigFppfOver.siteMapOver B integerBase hZ U hAc A.ι
  have : IsAffine (T.obj (BigFppfOver.siteObjectOver B integerBase hZ U hAc A.ι)) :=
    inferInstanceAs (IsAffine A.toScheme)
  obtain ⟨N, huN, hN⟩ := exists_isOpen_semistableFibreLocus_of_isAffine hω hG
    (isPullback_schemeSpaceMap_pullback_fst_comp hsq ι)
    (g := g) (fun a => hAV a.2) (⟨u, huA⟩ : A.toScheme) hu
  refine ⟨A.ι ''ᵁ N, ⟨_, huN, rfl⟩, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  exact hN a ha

/-- **Over a prestable family the semistable fibre locus is a neighbourhood of each of its
points**: on an étale scheme chart (Stacks 0E6F, `h0E6F`) this is
`AlgebraicGeometry.C1590Private.exists_isOpen_semistableFibreLocus_of_chart`, and étale morphisms
are open. -/
theorem isOpen_semistableFibreLocus (h0E6F : HasEtaleLocalSchemeCharts B hZ)
    (hω : HasNodalRelativeDualizingSheaf.{u}) (hgo : PrestableGenusLociOpen B hZ)
    {G : CurveFamily B hZ} (hG : IsPrestableCurveFamily B hZ G) :
    IsOpen (semistableFibreLocus G) := by
  let T := BigFppfOver.toScheme B integerBase hZ
  refine isOpen_iff_forall_mem_open.2 fun s hs => ?_
  obtain ⟨U, Z, φ, q, p, hφ, ⟨u, hu⟩, hsq⟩ := h0E6F G s
  have : Etale (T.map φ) := hφ
  obtain ⟨N, huN, hN⟩ := exists_isOpen_semistableFibreLocus_of_chart hω hgo hG hsq u
    (hu ▸ hs)
  refine ⟨T.map φ '' N, ?_, (T.map φ).isOpenMap _ N.2, ⟨u, huN, hu⟩⟩
  rintro _ ⟨u', hu', rfl⟩
  exact hN u' hu'

variable (B hZ) in
/-- **The input `PrestableSemistableFibresOpen`**, from the étale local scheme charts of Stacks
0E6F (`h0E6F`). The relative dualizing sheaf of a nodal family over an affine base is
`AlgebraicGeometry.C1590Private.hasNodalRelativeDualizingSheaf` (Stacks 0E6R), and the genus loci
of a prestable family are open by `AlgebraicGeometry.C1590Private.prestableGenusLociOpen_of`
(Stacks 0E6V), from `h0E6F`. -/
theorem prestableSemistableFibresOpen_of (h0E6F : HasEtaleLocalSchemeCharts B hZ) :
    PrestableSemistableFibresOpen B hZ :=
  prestableSemistableFibresOpen_of_isOpen B hZ fun _ hG =>
    isOpen_semistableFibreLocus h0E6F hasNodalRelativeDualizingSheaf
      (prestableGenusLociOpen_of h0E6F) hG

variable (B hZ) in
/-- **The input `PrestableSemistableFibresOpen`, unconditionally.** Over a prestable family of
curves the points whose fibre has genus at least one and no rational tail form an open set, and a
family mapping to it has such fibres exactly when its morphism of bases lands in that set (Stacks
0E6V, 0E6Y and the base field compatibility of Stacks 0E3L, as used in the proof of Stacks 0E70).
The étale local scheme charts are `AlgebraicGeometry.C1590Private.hasEtaleLocalSchemeCharts`
(Stacks 0E6F). -/
theorem prestableSemistableFibresOpen : PrestableSemistableFibresOpen B hZ :=
  prestableSemistableFibresOpen_of B hZ (hasEtaleLocalSchemeCharts B hZ)

end AlgebraicGeometry.C1590Private

end
