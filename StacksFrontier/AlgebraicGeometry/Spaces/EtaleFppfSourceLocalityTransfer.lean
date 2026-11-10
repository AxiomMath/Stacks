module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FromLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcSourceLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas

/-!
# Source locality for the étale and fppf topologies transferred from schemes to spaces

Let `S` be a scheme contained in a big fppf site `B`, and let `P` be a property of morphisms of
schemes which is étale local on the source and target (**Stacks 04QZ**). **Stacks 06ER** says
that if `P` is local on the source for one of the five topologies of **Stacks 03YH** then so is
the chart property `AlgebraicGeometry.Space.HoldsOnEveryEtaleChart B S hS P` of
**Stacks 03MJ**. This module proves the **étale** and **fppf** cases.

The argument of Stacks 06ER is topology-free except at three steps, and this module isolates
them: `AlgebraicGeometry.Space.isLocalAtSource_of_schemes_of_coveringTransfer` takes a topology
`τ`, a precoverage `K` on schemes, and the three statements that relate `τ`-coverings of
algebraic spaces to `K`-coverings of schemes, and runs the argument once. The étale and fppf
cases are then the two instantiations, each supplying its own three:

* a `τ`-covering of algebraic spaces whose members and target are all representable is a
  `K`-covering of the representing schemes;
* a `τ`-covering base-changed along a scheme chart of its target is a `τ`-covering of that
  chart, each member sitting in a cartesian square;
* a `τ`-covering composed with a surjective étale scheme atlas of each of its members is a
  `τ`-covering.

For the étale topology the three are cheap because an étale covering (**Stacks 041E**) is a
jointly surjective family of étale morphisms: joint surjectivity on scheme points comes from
joint surjectivity on presheaf points, base change of an étale morphism is étale
(**Stacks 03FU**) with joint surjectivity from **Stacks 03H4**, and an étale morphism composed
with an étale chart is étale (**Stacks 03FT**). For the fppf topology (**Stacks 03Y8**) the
same three run over the two conditions *flat* and *locally of finite presentation*, by
**Stacks 03XR** and **Stacks 03XQ** and by **Stacks 0467** and **Stacks 0468**.

## Main results

* `AlgebraicGeometry.Space.isLocalAtSource_of_schemes_of_coveringTransfer`: the topology-free
  core of Stacks 06ER.
* `AlgebraicGeometry.Space.isEtaleCovering_yoneda_of_isCovering`,
  `AlgebraicGeometry.Space.isEtaleCovering_baseChange_of_chart`,
  `AlgebraicGeometry.Space.etale_atlases_comp_isEtaleCovering`: the three étale-topology
  inputs.
* `AlgebraicGeometry.Space.isLocalAtSource_etale_of_schemes'`: **Stacks 06ER**, the étale case,
  needing no source-locality hypothesis; the prime marks that weaker hypothesis against
  `AlgebraicGeometry.Space.isLocalAtSource_etale_of_schemes`, which takes source locality for
  `AlgebraicGeometry.Scheme.etalePrecoverage` as an instance argument.
* `AlgebraicGeometry.Space.isFppfCovering_yoneda_of_isCovering`,
  `AlgebraicGeometry.Space.isFppfCovering_baseChange_of_chart`,
  `AlgebraicGeometry.Space.etale_atlases_comp_isFppfCovering`: the three fppf-topology inputs.
* `AlgebraicGeometry.Space.isLocalAtSource_fppf_of_schemes`: **Stacks 06ER**, the fppf case.

## Implementation notes

`isLocalAtSource_etale_of_schemes'` and `isLocalAtSource_fppf_of_schemes` are **deliberately not
tagged** `@[stacks 06ER]`, for the same reason as their fpqc and smooth siblings in
`StacksFrontier.AlgebraicGeometry.Spaces.FpqcSourceLocalityTransfer` and
`StacksFrontier.AlgebraicGeometry.Spaces.SmoothSourceLocalityTransfer`: Stacks 06ER asserts the
transfer for all five topologies of Stacks 03YH at once, and four of five is still a strictly
weaker statement. The one missing case is the syntomic one, whose base-change input needs
`AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget @AlgebraicGeometry.Syntomic` (**Stacks 04R3**,
syntomic case), itself waiting on the syntomic case of **Stacks 02KM**.

The étale case needs no source-locality hypothesis beyond `hP`: a property étale local on the
source and target is local on the source for `AlgebraicGeometry.Scheme.etalePrecoverage`. The
fppf case takes source locality for `AlgebraicGeometry.Scheme.fppfPrecoverage` as an instance
argument, exactly as the smooth case takes it for the smooth precoverage. Coarsening cannot
replace either: a property local on the source for a precoverage is preserved by precomposition
with every member of one of its coverings, and `AlgebraicGeometry.Scheme.fppfPrecoverage` is
already too coarse for smoothness — the relative Frobenius of the affine line over a field of
characteristic `p` is faithfully flat and of finite presentation, so a one-member fppf covering,
and is not smooth.

The fpqc and smooth cases predate this module and prove the same core argument inline; they
are instances of `isLocalAtSource_of_schemes_of_coveringTransfer` and should be re-derived from
it when those files are next touched.

These are **Chapter 74 results** (Descent on Spaces).

## References

* [Stacks Project, Tag 06ER](https://stacks.math.columbia.edu/tag/06ER)
* [Stacks Project, Tag 041E](https://stacks.math.columbia.edu/tag/041E)
* [Stacks Project, Tag 03Y8](https://stacks.math.columbia.edu/tag/03Y8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/- Lean v4.35.0: instance search for these limits on presheaves of the big fppf site times out;
supply them directly. -/
local instance : HasLimitsOfSize.{u, u} ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance
local instance : HasLimitsOfSize.{0, 0} ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance
local instance (J : Type) : HasLimitsOfShape (Discrete J) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  HasLimitsOfSize.has_limits_of_shape _
local instance : HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-! ### The topology-free core of Stacks 06ER -/

section CoveringTransfer

variable (τ : Topology) (K : Precoverage Scheme.{u})
  (hyoneda : ∀ {J : Type v} (U : J → BigFppfOver B S hS) (V : BigFppfOver B S hS)
    (f : ∀ j, U j ⟶ V),
    Topology.IsCovering τ B S hS (fun j => yoneda.obj (U j)) (fun j => yoneda.map (f j)) →
    Presieve.ofArrows (fun j => (BigFppfOver.toScheme B S hS).obj (U j))
      (fun j => (BigFppfOver.toScheme B S hS).map (f j)) ∈
      K ((BigFppfOver.toScheme B S hS).obj V))
  (hbaseChange : ∀ {J : Type v} {X : AlgebraicSpaces B S hS}
    (Zi : J → AlgebraicSpaces B S hS) (gi : ∀ j, Zi j ⟶ X),
    Topology.IsCovering τ B S hS (fun j => (Zi j).1) (fun j => (gi j).hom) →
    ∀ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X.1),
      ∃ (Ai : J → AlgebraicSpaces B S hS)
        (qi : ∀ j, Ai j ⟶ representedAlgebraicSpace B S hS U)
        (projZ : ∀ j, Ai j ⟶ Zi j),
          Topology.IsCovering τ B S hS (fun j => (Ai j).1) (fun j => (qi j).hom) ∧
          (∀ j, IsPullback (qi j) (projZ j)
            (ObjectProperty.homMk a : representedAlgebraicSpace B S hS U ⟶ X) (gi j)))
  (hatlasComp : ∀ {J : Type v} (Z : J → AlgebraicSpaces B S hS)
    (V : AlgebraicSpaces B S hS) (g : ∀ j, Z j ⟶ V),
    Topology.IsCovering τ B S hS (fun j => (Z j).1) (fun j => (g j).hom) →
    ∀ (U : J → BigFppfOver B S hS) (a : ∀ j, yoneda.obj (U j) ⟶ (Z j).1),
      (∀ j, (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (a j)) →
      (∀ j, (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (a j)) →
      Topology.IsCovering τ B S hS
        (fun p : Σ _ : J, PUnit.{v + 1} => yoneda.obj (U p.1))
        (fun p => a p.1 ≫ (g p.1).hom))

include hyoneda hbaseChange hatlasComp

/-- Under the three covering-transfer inputs, a `τ`-covering of `X` base-changed along a scheme
chart `U ⟶ X` and refined by surjective étale scheme atlases of its members gives a `K`-covering
of the scheme `U`. -/
theorem exists_atlas_cover_of_coveringTransfer {I : Type v} {X : AlgebraicSpaces B S hS}
    (Zi : I → AlgebraicSpaces B S hS) (gi : ∀ i, Zi i ⟶ X)
    (hcover : Topology.IsCovering τ B S hS (fun i => (Zi i).1) (fun i => (gi i).hom))
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X.1) :
    ∃ (Ai : I → AlgebraicSpaces B S hS) (qi : ∀ i, Ai i ⟶ representedAlgebraicSpace B S hS U)
      (projZ : ∀ i, Ai i ⟶ Zi i) (Wi : I → BigFppfOver B S hS)
      (wi : ∀ i, yoneda.obj (Wi i) ⟶ (Ai i).1),
      (∀ i, IsPullback (qi i) (projZ i)
        (ObjectProperty.homMk a : representedAlgebraicSpace B S hS U ⟶ X) (gi i)) ∧
      (∀ i, (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (wi i)) ∧
      (∀ i, (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (wi i)) ∧
      Presieve.ofArrows
        (fun p : Σ _ : I, PUnit.{v + 1} => (BigFppfOver.toScheme B S hS).obj (Wi p.1))
        (fun p => (BigFppfOver.toScheme B S hS).map (yoneda.preimage (wi p.1 ≫ (qi p.1).hom))) ∈
        K ((BigFppfOver.toScheme B S hS).obj U) := by
  obtain ⟨Ai, qi, projZ, hAi, hpb⟩ := hbaseChange Zi gi hcover U a
  choose Wi wi hsurjWi hetaleWi using fun i => (Ai i).property.exists_atlas
  let d : ∀ p : Σ _ : I, PUnit.{v + 1}, Wi p.1 ⟶ U :=
    fun p => yoneda.preimage (wi p.1 ≫ (qi p.1).hom)
  have hd (p : Σ _ : I, PUnit.{v + 1}) : yoneda.map (d p) = wi p.1 ≫ (qi p.1).hom := by
    simp [d]
  refine ⟨Ai, qi, projZ, Wi, wi, hpb, hsurjWi, hetaleWi,
    hyoneda (fun p : Σ _ : I, PUnit.{v + 1} => Wi p.1) U d ?_⟩
  simpa only [hd] using hatlasComp Ai _ qi hAi Wi wi hsurjWi hetaleWi

/-- Under the three covering-transfer inputs, if `P` is étale local on the source and target and
local on the source for `K`, the chart property attached to `P` passes from `f` to its
precomposition with each member of a `τ`-covering of its source. -/
theorem holdsOnEveryEtaleChart_comp_of_coveringTransfer (P : MorphismProperty Scheme.{u})
    (hP : IsEtaleLocalOnSourceAndTarget P) (hlocal : P.IsLocalAtSource K) {I : Type v}
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : HoldsOnEveryEtaleChart B S hS P f.hom)
    (Zi : I → AlgebraicSpaces B S hS) (gi : ∀ i, Zi i ⟶ X)
    (hcover : Topology.IsCovering τ B S hS (fun i => (Zi i).1) (fun i => (gi i).hom)) (j : I) :
    HoldsOnEveryEtaleChart B S hS P (gi j ≫ f).hom := by
  let T := BigFppfOver.toScheme B S hS
  obtain ⟨V, b, hbSurj, hbEtale⟩ := Y.property.exists_atlas
  obtain ⟨T0, t, alpha, hα, htSurj, htEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS
      X.property Y.property f.hom V b hbSurj hbEtale
  have hPalpha : P (T.map alpha) := hf T0 V t b alpha htEtale hbEtale hα.symm
  let Tobj : AlgebraicSpaces B S hS := ⟨yoneda.obj T0, isAlgebraicSpace_yoneda B S hS T0⟩
  let tX : Tobj ⟶ X := ObjectProperty.homMk t
  obtain ⟨Ai, qi, projZ, Wi, wi, hpb, hsurjWi, hetaleWi, hK⟩ :=
    exists_atlas_cover_of_coveringTransfer B S hS τ K hyoneda hbaseChange hatlasComp
      Zi gi hcover T0 t
  let d : ∀ p : Σ _ : I, PUnit.{v + 1}, Wi p.1 ⟶ T0 :=
    fun p => yoneda.preimage (wi p.1 ≫ (qi p.1).hom)
  have hd (p : Σ _ : I, PUnit.{v + 1}) : yoneda.map (d p) = wi p.1 ≫ (qi p.1).hom := by
    simp [d]
  let c : yoneda.obj (Wi j) ⟶ (Zi j).1 := wi j ≫ (projZ j).hom
  have hcEtale := (isEtale_iff_presheaf_of_yoneda B S hS c).1 <| isEtale_comp B S hS
    (chart_map_isEtale B S hS (Wi j) (wi j) (hetaleWi j))
    (isEtale_of_isPullback B S hS (qi j) (projZ j) tX (gi j) (hpb j)
      (chart_map_isEtale B S hS T0 t htEtale))
  have hcSurj := (surjective_iff_surjective_pointsMap B S hS
    (Zi j).1 (Zi j).property (Wi j) c).mpr <| isSurjective_comp B S hS
      ((surjective_iff_surjective_pointsMap B S hS (Ai j).1 (Ai j).property
        (Wi j) (wi j)).mp (hsurjWi j))
      (isSurjective_of_isPullback B S hS (hpb j)
        ((surjective_iff_surjective_pointsMap B S hS X.1 X.property T0 t).mp htSurj))
  let p : Σ _ : I, PUnit.{v + 1} := ⟨j, PUnit.unit⟩
  let h : Wi j ⟶ V := yoneda.preimage (wi j ≫ (qi j).hom ≫ yoneda.map alpha)
  have hh : yoneda.map h = wi j ≫ (qi j).hom ≫ yoneda.map alpha := by simp [h]
  have heq : h = d p ≫ alpha := yoneda.map_injective (by simp [p, hd, hh])
  have hPh : P (T.map h) := by
    rw [heq, Functor.map_comp]
    exact hlocal.comp hK (T.map (d p)) ⟨p⟩ hPalpha
  have hpbw : (qi j).hom ≫ tX.hom = (projZ j).hom ≫ (gi j).hom :=
    congrArg (fun k => k.hom) (hpb j).w
  have hα' : tX.hom ≫ f.hom = yoneda.map alpha ≫ b := by simpa [tX] using hα
  have hcomm : yoneda.map h ≫ b = c ≫ (gi j).hom ≫ f.hom := by
    rw [hh]
    simp only [c, Category.assoc, ← hα', reassoc_of% hpbw]
  exact (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS P hP (Zi j).property
    Y.property ((gi j ≫ f).hom)).2 ⟨Wi j, V, c, b, h, hcEtale, hbEtale, hcSurj, hcomm, hPh⟩

/-- Under the three covering-transfer inputs, if `P` is local on the source for `K`, the chart
property attached to `P` holds for `f` once it holds for its precomposition with every member of
a `τ`-covering of its source. -/
theorem holdsOnEveryEtaleChart_of_comp_of_coveringTransfer (P : MorphismProperty Scheme.{u})
    (hlocal : P.IsLocalAtSource K) {I : Type v} {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (Zi : I → AlgebraicSpaces B S hS) (gi : ∀ i, Zi i ⟶ X)
    (hcover : Topology.IsCovering τ B S hS (fun i => (Zi i).1) (fun i => (gi i).hom))
    (hall : ∀ i, HoldsOnEveryEtaleChart B S hS P (gi i ≫ f).hom) :
    HoldsOnEveryEtaleChart B S hS P f.hom := by
  intro U V a b h ha hb hcomm
  let Uobj : AlgebraicSpaces B S hS := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
  let au : Uobj ⟶ X := ObjectProperty.homMk a
  obtain ⟨Ai, qi, projZ, Wi, wi, hpb, -, hetaleWi, hK⟩ :=
    exists_atlas_cover_of_coveringTransfer B S hS τ K hyoneda hbaseChange hatlasComp
      Zi gi hcover U a
  let d : ∀ p : Σ _ : I, PUnit.{v + 1}, Wi p.1 ⟶ U :=
    fun p => yoneda.preimage (wi p.1 ≫ (qi p.1).hom)
  have hd (p : Σ _ : I, PUnit.{v + 1}) : yoneda.map (d p) = wi p.1 ≫ (qi p.1).hom := by
    simp [d]
  have hK' : Presieve.ofArrows
      (fun p : Σ _ : I, PUnit.{v + 1} => (BigFppfOver.toScheme B S hS).obj (Wi p.1))
      (fun p => (BigFppfOver.toScheme B S hS).map (d p)) ∈
      K ((BigFppfOver.toScheme B S hS).obj U) := hK
  apply hlocal.of_forall_comp hK'
  rintro W' k ⟨⟨i, ji⟩⟩
  let wz : yoneda.obj (Wi i) ⟶ (Zi i).1 := wi i ≫ (projZ i).hom
  have hwzEtale := (isEtale_iff_presheaf_of_yoneda B S hS wz).1 <| isEtale_comp B S hS
    (chart_map_isEtale B S hS (Wi i) (wi i) (hetaleWi i))
    (isEtale_of_isPullback B S hS (qi i) (projZ i) au (gi i) (hpb i)
      (chart_map_isEtale B S hS U a ha))
  let hV : Wi i ⟶ V := yoneda.preimage (wi i ≫ (qi i).hom ≫ yoneda.map h)
  have hhV : yoneda.map hV = wi i ≫ (qi i).hom ≫ yoneda.map h := by simp [hV]
  have hbaseEq : (qi i).hom ≫ a = (projZ i).hom ≫ (gi i).hom :=
    congrArg (fun k => k.hom) (hpb i).w
  have hchartComm : yoneda.map hV ≫ b = wz ≫ (gi i).hom ≫ f.hom := by
    rw [hhV]
    simp only [wz, Category.assoc, hcomm, reassoc_of% hbaseEq]
  have hdcomp : d ⟨i, ji⟩ ≫ h = hV := yoneda.map_injective (by simp [hd, hhV])
  rw [← Functor.map_comp, hdcomp]
  exact hall i (Wi i) V wz b hV hwzEtale hb hchartComm

end CoveringTransfer

/-- The argument of **Stacks 06ER**, with its three topology-dependent inputs abstracted.

Let `P` be a property of morphisms of schemes which is étale local on the source and target and
local on the source for a precoverage `K` of schemes, and let `τ` be one of the five topologies
of Stacks 03YH. If `τ`-coverings of algebraic spaces transfer to `K`-coverings of schemes on
representables, are stable under base change along a chart, and absorb surjective étale scheme
atlases of their members, then the chart property of Stacks 03MJ attached to `P` is local on
the source for `τ`.

Given `f : X ⟶ Y` and a `τ`-covering `{Zᵢ ⟶ X}`, choose a surjective étale scheme atlas
`V ⟶ Y`, lift it to a surjective étale chart `T₀ ⟶ X` over a morphism `α : T₀ ⟶ V` of the site
(**Stacks 02X1**), base-change the covering along `T₀ ⟶ X`, choose a surjective étale scheme
atlas `Wᵢ ⟶ Zᵢ ×_X T₀` of each member, and compose: the resulting family `{Wᵢ ⟶ T₀}` is a
family of morphisms of the *site*, so the first input turns it into a `K`-covering of schemes.
With both sides of the equivalence expressed on schemes, source locality of `P` for `K` gives
the two implications, and Stacks 03MJ carries them back. -/
theorem isLocalAtSource_of_schemes_of_coveringTransfer
    (τ : Topology) (K : Precoverage Scheme.{u}) (P : MorphismProperty Scheme.{u})
    (hP : IsEtaleLocalOnSourceAndTarget P) (hlocal : P.IsLocalAtSource K)
    (hyoneda : ∀ {J : Type v} (U : J → BigFppfOver B S hS) (V : BigFppfOver B S hS)
      (f : ∀ j, U j ⟶ V),
      Topology.IsCovering τ B S hS (fun j => yoneda.obj (U j)) (fun j => yoneda.map (f j)) →
      Presieve.ofArrows (fun j => (BigFppfOver.toScheme B S hS).obj (U j))
        (fun j => (BigFppfOver.toScheme B S hS).map (f j)) ∈
        K ((BigFppfOver.toScheme B S hS).obj V))
    (hbaseChange : ∀ {J : Type v} {X : AlgebraicSpaces B S hS}
      (Zi : J → AlgebraicSpaces B S hS) (gi : ∀ j, Zi j ⟶ X),
      Topology.IsCovering τ B S hS (fun j => (Zi j).1) (fun j => (gi j).hom) →
      ∀ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X.1),
        ∃ (Ai : J → AlgebraicSpaces B S hS)
          (qi : ∀ j, Ai j ⟶ representedAlgebraicSpace B S hS U)
          (projZ : ∀ j, Ai j ⟶ Zi j),
            Topology.IsCovering τ B S hS (fun j => (Ai j).1) (fun j => (qi j).hom) ∧
            (∀ j, IsPullback (qi j) (projZ j)
              (ObjectProperty.homMk a : representedAlgebraicSpace B S hS U ⟶ X) (gi j)))
    (hatlasComp : ∀ {J : Type v} (Z : J → AlgebraicSpaces B S hS)
      (V : AlgebraicSpaces B S hS) (g : ∀ j, Z j ⟶ V),
      Topology.IsCovering τ B S hS (fun j => (Z j).1) (fun j => (g j).hom) →
      ∀ (U : J → BigFppfOver B S hS) (a : ∀ j, yoneda.obj (U j) ⟶ (Z j).1),
        (∀ j, (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf (a j)) →
        (∀ j, (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf (a j)) →
        Topology.IsCovering τ B S hS
          (fun p : Σ _ : J, PUnit.{v + 1} => yoneda.obj (U p.1))
          (fun p => a p.1 ≫ (g p.1).hom)) :
    MorphismProperty.IsLocalAtSource
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) =>
        HoldsOnEveryEtaleChart B S hS P f.hom)
      (Topology.precoverage.{u, v} τ B S hS) := by
  let Q : MorphismProperty (AlgebraicSpaces B S hS) :=
    fun {F G} f => HoldsOnEveryEtaleChart B S hS P f.hom
  have : Q.RespectsIso := holdsOnEveryEtaleChart_respectsIso B S hS P
  refine MorphismProperty.IsLocalAtSource.mk_of_iff_of_zeroHypercover fun f E => ?_
  rcases E.mem₀ with ⟨I, Zi, gi, hpres, hcover⟩
  refine ⟨fun hf i => ?_, fun hall => ?_⟩
  · have hmem : E.presieve₀ (E.f i) := ⟨i⟩
    obtain ⟨j, hobj, hindex⟩ := Presieve.ofArrows_surj gi (E.f i) (by
      simpa only [hpres] using hmem)
    change Q (E.f i ≫ f)
    rw [hindex]
    exact MorphismProperty.RespectsIso.precomp Q (eqToHom hobj.symm) (gi j ≫ f)
      (holdsOnEveryEtaleChart_comp_of_coveringTransfer B S hS τ K hyoneda hbaseChange
        hatlasComp P hP hlocal f hf Zi gi hcover j)
  · refine holdsOnEveryEtaleChart_of_comp_of_coveringTransfer B S hS τ K hyoneda hbaseChange
      hatlasComp P hlocal f Zi gi hcover fun i => ?_
    have hmem : E.presieve₀ (gi i) := by
      rw [hpres]
      exact ⟨i⟩
    obtain ⟨j, hobj, hgi⟩ := Presieve.ofArrows_surj E.f (gi i) (by
      simpa only [hpres] using hmem)
    change Q (gi i ≫ f)
    rw [hgi]
    exact MorphismProperty.RespectsIso.precomp Q (eqToHom hobj.symm) (E.f j ≫ f) (hall j)

/-! ### The three étale-topology inputs of Stacks 06ER -/

/-- The fibre products of the members of a jointly surjective family with a scheme chart `a` of the
target form a jointly surjective family over the chart, each member sitting in a cartesian
square. -/
private theorem exists_fiberProduct_jointly_surjective
    {I : Type v} {X : AlgebraicSpaces B S hS}
    (Zi : I → AlgebraicSpaces B S hS) (gi : ∀ i, Zi i ⟶ X)
    (hsurj : (⋃ i, Set.range (pointsMap B S hS (Zi i).1 (gi i).hom)) = Set.univ)
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X.1) :
    ∃ (Ai : I → AlgebraicSpaces B S hS)
      (qi : ∀ i, Ai i ⟶ representedAlgebraicSpace B S hS U)
      (projZ : ∀ i, Ai i ⟶ Zi i),
        (∀ i, IsPullback (qi i) (projZ i)
          (ObjectProperty.homMk a : representedAlgebraicSpace B S hS U ⟶ X) (gi i)) ∧
        (⋃ i, Set.range (pointsMap B S hS (Ai i).1 (qi i).hom)) = Set.univ := by
  let Uobj := representedAlgebraicSpace B S hS U
  let au : Uobj ⟶ X := ObjectProperty.homMk a
  have hpb : ∀ i, IsPullback (ObjectProperty.homMk (pullback.snd (gi i).hom au.hom) : _ ⟶ Uobj)
      (ObjectProperty.homMk (pullback.fst (gi i).hom au.hom) :
        AlgebraicSpaces.fiberProduct B S hS (gi i) au ⟶ Zi i) au (gi i) :=
    fun i => (AlgebraicSpaces.isPullback_fiberProduct B S hS (gi i) au).flip
  refine ⟨_, _, _, hpb, Set.eq_univ_of_forall fun u => ?_⟩
  obtain ⟨i, z, hz⟩ := Set.mem_iUnion.mp <|
    Set.eq_univ_iff_forall.mp hsurj (pointsMap B S hS Uobj.1 au.hom u)
  obtain ⟨w, hw, -⟩ := exists_point_of_isPullback B S hS (hpb i) u z hz.symm
  exact Set.mem_iUnion.mpr ⟨i, w, hw⟩

/-- Composing a jointly surjective family with surjective charts of its members gives a jointly
surjective family, indexed by the members paired with a one-element type. -/
private theorem jointly_surjective_atlases_comp
    {I : Type v} (Z : I → AlgebraicSpaces B S hS) (V : AlgebraicSpaces B S hS)
    (g : ∀ i, Z i ⟶ V)
    (hbase : (⋃ i, Set.range (pointsMap B S hS (Z i).1 (g i).hom)) = Set.univ)
    (hspace : ∀ i, IsAlgebraicSpace B S hS (Z i).1)
    (U : I → BigFppfOver B S hS) (a : ∀ i, yoneda.obj (U i) ⟶ (Z i).1)
    (hsurj : ∀ i, (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (a i)) :
    (⋃ p : Σ _ : I, PUnit.{v + 1},
      Set.range (pointsMap B S hS (yoneda.obj (U p.1)) (a p.1 ≫ (g p.1).hom))) = Set.univ := by
  refine Set.eq_univ_of_forall fun v => ?_
  obtain ⟨i, z, hz⟩ := Set.mem_iUnion.mp <| Set.eq_univ_iff_forall.mp hbase v
  obtain ⟨w, hw⟩ := (surjective_iff_surjective_pointsMap B S hS (Z i).1 (hspace i)
    (U i) (a i)).mp (hsurj i) z
  refine Set.mem_iUnion.mpr ⟨⟨i, PUnit.unit⟩, w, ?_⟩
  rw [pointsMap_comp]
  change pointsMap B S hS (Z i).1 (g i).hom (pointsMap B S hS _ (a i) w) = v
  rw [hw, hz]

/-- An étale covering family of algebraic spaces over `S` all of whose members and whose target
are representable is an étale covering family of the representing schemes, that is, lies in
`AlgebraicGeometry.Scheme.etalePrecoverage`.

Joint surjectivity on the schemes' points follows from joint surjectivity on the presheaves'
points, and étaleness of each member of the family, read at the identity chart, is étaleness of
the corresponding morphism of the site. -/
theorem isEtaleCovering_yoneda_of_isCovering
    {I : Type v} (U : I → BigFppfOver B S hS) (V : BigFppfOver B S hS) (f : ∀ i, U i ⟶ V)
    (hcover : Topology.IsCovering .etale B S hS
      (fun i => yoneda.obj (U i)) (fun i => yoneda.map (f i))) :
    Presieve.ofArrows
      (fun i => (BigFppfOver.toScheme B S hS).obj (U i))
      (fun i => (BigFppfOver.toScheme B S hS).map (f i)) ∈
      Scheme.etalePrecoverage ((BigFppfOver.toScheme B S hS).obj V) :=
  ofArrows_mem_etalePrecoverage_iff.mpr
    ⟨scheme_family_jointly_surjective_of_points B S hS U V f hcover.2.2.jointly_surjective,
      fun i => (presheaf_yoneda_map_etale_iff B S hS (f i)).1
        ((isEtale_iff_presheaf_of_yoneda B S hS (yoneda.map (f i))).1 (hcover.2.2.etale i))⟩

/-- An étale covering family of an algebraic space over `S`, base-changed along a scheme chart
of its target, is an étale covering family of that chart, and each member sits in a cartesian
square over the chart and the corresponding member of the original family.

Étaleness of the projections is base-change stability of étaleness (Stacks 03FU); joint
surjectivity is Stacks 03H4, which produces a point of a cartesian square from a compatible
pair of points. -/
theorem isEtaleCovering_baseChange_of_chart
    {I : Type v} {X : AlgebraicSpaces B S hS}
    (Zi : I → AlgebraicSpaces B S hS) (gi : ∀ i, Zi i ⟶ X)
    (hcover : Topology.IsCovering .etale B S hS (fun i => (Zi i).1) (fun i => (gi i).hom))
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X.1) :
    ∃ (Ai : I → AlgebraicSpaces B S hS)
      (qi : ∀ i, Ai i ⟶ representedAlgebraicSpace B S hS U)
      (projZ : ∀ i, Ai i ⟶ Zi i),
        Topology.IsCovering .etale B S hS (fun i => (Ai i).1) (fun i => (qi i).hom) ∧
        (∀ i, IsPullback (qi i) (projZ i)
          (ObjectProperty.homMk a : representedAlgebraicSpace B S hS U ⟶ X) (gi i)) := by
  obtain ⟨Ai, qi, projZ, hpb, hsurj⟩ := exists_fiberProduct_jointly_surjective B S hS Zi gi
    hcover.2.2.jointly_surjective U a
  exact ⟨Ai, qi, projZ, ⟨(representedAlgebraicSpace B S hS U).property, fun i => (Ai i).property,
    (representedAlgebraicSpace B S hS U).property, fun i => (Ai i).property,
    fun i => isEtale_of_isPullback B S hS (projZ i) (qi i) (gi i) _ (hpb i).flip
      (hcover.2.2.etale i), hsurj⟩, hpb⟩

/-- Composing an étale covering of an algebraic space over `S` with a surjective étale scheme
atlas of each of its members gives an étale covering, indexed by the members paired with a
one-element type.

An étale chart is an étale morphism of algebraic spaces and étale morphisms compose
(**Stacks 03FT**), and joint surjectivity is transitive. -/
theorem etale_atlases_comp_isEtaleCovering
    {I : Type v} (Z : I → AlgebraicSpaces B S hS) (V : AlgebraicSpaces B S hS)
    (g : ∀ i, Z i ⟶ V)
    (hbase : Topology.IsCovering .etale B S hS (fun i => (Z i).1) (fun i => (g i).hom))
    (U : I → BigFppfOver B S hS) (a : ∀ i, yoneda.obj (U i) ⟶ (Z i).1)
    (hsurj : ∀ i, (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (a i))
    (hetale : ∀ i, (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (a i)) :
    Topology.IsCovering .etale B S hS
      (fun p : Σ _ : I, PUnit.{v + 1} => yoneda.obj (U p.1))
      (fun p => a p.1 ≫ (g p.1).hom) := by
  have hUspace : ∀ i, IsAlgebraicSpace B S hS (yoneda.obj (U i)) := fun i =>
    isAlgebraicSpace_yoneda B S hS (U i)
  refine ⟨hbase.1, fun p => hUspace p.1, hbase.1, fun p => hUspace p.1,
    fun p => isEtale_comp B S hS (chart_map_isEtale B S hS (U p.1) (a p.1) (hetale p.1))
      (hbase.2.2.etale p.1),
    jointly_surjective_atlases_comp B S hS Z V g hbase.2.2.jointly_surjective hbase.2.1 U a hsurj⟩

/-! ### Stacks 06ER, the étale case -/

/-- **Stacks 06ER**, the étale case. If a property `P` of morphisms of schemes is étale local on
the source and target, then the associated property of morphisms of algebraic spaces over `S`
of Stacks 03MJ is local on the source for the étale topology of algebraic spaces.

No source-locality hypothesis is needed: a property étale local on the source and target is
local on the source for `AlgebraicGeometry.Scheme.etalePrecoverage` (**Stacks 04R0**).

Deliberately untagged: Stacks 06ER asserts this for all five topologies of Stacks 03YH at once,
and the syntomic case is still missing. -/
theorem isLocalAtSource_etale_of_schemes'
    (P : MorphismProperty Scheme.{u}) (hP : IsEtaleLocalOnSourceAndTarget P) :
    MorphismProperty.IsLocalAtSource
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) =>
        HoldsOnEveryEtaleChart B S hS P f.hom)
      (Topology.precoverage.{u, v} .etale B S hS) :=
  isLocalAtSource_of_schemes_of_coveringTransfer B S hS .etale Scheme.etalePrecoverage P hP
    (IsEtaleLocalOnSourceAndTarget.isLocalAtSource_etalePrecoverage P hP)
    (isEtaleCovering_yoneda_of_isCovering B S hS) (isEtaleCovering_baseChange_of_chart B S hS)
    (etale_atlases_comp_isEtaleCovering B S hS)

/-! ### The three fppf-topology inputs of Stacks 06ER -/

/-- An fppf covering family of algebraic spaces over `S` all of whose members and whose target
are representable is an fppf covering family of the representing schemes, that is, lies in
`AlgebraicGeometry.Scheme.fppfPrecoverage`.

Joint surjectivity on the schemes' points follows from joint surjectivity on the presheaves'
points, and flatness and finite presentation of each member are the chart conditions of
Stacks 03MJ read at the two identity charts. -/
theorem isFppfCovering_yoneda_of_isCovering
    {I : Type v} (U : I → BigFppfOver B S hS) (V : BigFppfOver B S hS) (f : ∀ i, U i ⟶ V)
    (hcover : Topology.IsCovering .fppf B S hS
      (fun i => yoneda.obj (U i)) (fun i => yoneda.map (f i))) :
    Presieve.ofArrows
      (fun i => (BigFppfOver.toScheme B S hS).obj (U i))
      (fun i => (BigFppfOver.toScheme B S hS).map (f i)) ∈
      Scheme.fppfPrecoverage ((BigFppfOver.toScheme B S hS).obj V) := by
  rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
  exact ⟨scheme_family_jointly_surjective_of_points B S hS U V f hcover.2.2.jointly_surjective,
    fun i => ⟨(hcover.2.2.flat i) (U i) V (𝟙 (yoneda.obj (U i))) (𝟙 (yoneda.obj V)) (f i)
      (presheaf_etale_id B S hS (U i)) (presheaf_etale_id B S hS V) (by simp),
    (hcover.2.2.locallyOfFinitePresentation i) (U i) V (𝟙 (yoneda.obj (U i)))
      (𝟙 (yoneda.obj V)) (f i)
      (presheaf_etale_id B S hS (U i)) (presheaf_etale_id B S hS V) (by simp)⟩⟩

/-- An fppf covering family of an algebraic space over `S`, base-changed along a scheme chart of
its target, is an fppf covering family of that chart, and each member sits in a cartesian square
over the chart and the corresponding member of the original family.

Flatness and finite presentation of the projections are base-change stability of those two
properties (**Stacks 03XR**); joint surjectivity is Stacks 03H4, which produces a point of a
cartesian square from a compatible pair of points. -/
theorem isFppfCovering_baseChange_of_chart
    {I : Type v} {X : AlgebraicSpaces B S hS}
    (Zi : I → AlgebraicSpaces B S hS) (gi : ∀ i, Zi i ⟶ X)
    (hcover : Topology.IsCovering .fppf B S hS (fun i => (Zi i).1) (fun i => (gi i).hom))
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X.1) :
    ∃ (Ai : I → AlgebraicSpaces B S hS)
      (qi : ∀ i, Ai i ⟶ representedAlgebraicSpace B S hS U)
      (projZ : ∀ i, Ai i ⟶ Zi i),
        Topology.IsCovering .fppf B S hS (fun i => (Ai i).1) (fun i => (qi i).hom) ∧
        (∀ i, IsPullback (qi i) (projZ i)
          (ObjectProperty.homMk a : representedAlgebraicSpace B S hS U ⟶ X) (gi i)) := by
  obtain ⟨Ai, qi, projZ, hpb, hsurj⟩ := exists_fiberProduct_jointly_surjective B S hS Zi gi
    hcover.2.2.jointly_surjective U a
  exact ⟨Ai, qi, projZ, ⟨(representedAlgebraicSpace B S hS U).property, fun i => (Ai i).property,
    (representedAlgebraicSpace B S hS U).property, fun i => (Ai i).property,
    fun i => (isFlat_isStableUnderBaseChange B S hS).of_isPullback (hpb i).flip
      (hcover.2.2.flat i),
    fun i => (isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback
      (hpb i).flip (hcover.2.2.locallyOfFinitePresentation i), hsurj⟩, hpb⟩

/-- Composing an fppf covering of an algebraic space over `S` with a surjective étale scheme
atlas of each of its members gives an fppf covering, indexed by the members paired with a
one-element type.

An étale morphism of algebraic spaces is flat (**Stacks 0467**) and locally of finite
presentation (**Stacks 0468**), both properties compose (**Stacks 03MN** and **Stacks 03XQ**),
and joint surjectivity is transitive. -/
theorem etale_atlases_comp_isFppfCovering
    {I : Type v} (Z : I → AlgebraicSpaces B S hS) (V : AlgebraicSpaces B S hS)
    (g : ∀ i, Z i ⟶ V)
    (hbase : Topology.IsCovering .fppf B S hS (fun i => (Z i).1) (fun i => (g i).hom))
    (U : I → BigFppfOver B S hS) (a : ∀ i, yoneda.obj (U i) ⟶ (Z i).1)
    (hsurj : ∀ i, (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (a i))
    (hetale : ∀ i, (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (a i)) :
    Topology.IsCovering .fppf B S hS
      (fun p : Σ _ : I, PUnit.{v + 1} => yoneda.obj (U p.1))
      (fun p => a p.1 ≫ (g p.1).hom) := by
  have hUspace : ∀ i, IsAlgebraicSpace B S hS (yoneda.obj (U i)) := fun i =>
    isAlgebraicSpace_yoneda B S hS (U i)
  have haEtale : ∀ i, IsEtale B S hS (a i) := fun i =>
    chart_map_isEtale B S hS (U i) (a i) (hetale i)
  refine ⟨hbase.1, fun p => hUspace p.1, hbase.1, fun p => hUspace p.1,
    fun p => isFlat_comp B S hS (hUspace p.1) (hbase.2.1 p.1) hbase.1
      (a p.1) (g p.1).hom (isFlat_of_isEtale B S hS (haEtale p.1)) (hbase.2.2.flat p.1),
    fun p => isLocallyOfFinitePresentation_comp B S hS (hUspace p.1) (hbase.2.1 p.1) hbase.1
      (a p.1) (g p.1).hom (isLocallyOfFinitePresentation_of_isEtale B S hS (haEtale p.1))
      (hbase.2.2.locallyOfFinitePresentation p.1),
    jointly_surjective_atlases_comp B S hS Z V g hbase.2.2.jointly_surjective hbase.2.1 U a hsurj⟩

/-! ### Stacks 06ER, the fppf case -/

/-- **Stacks 06ER**, the fppf case. If a property `P` of morphisms of schemes is étale local on
the source and target and local on the source for the fppf topology of schemes, then the
associated property of morphisms of algebraic spaces over `S` of Stacks 03MJ is local on the
source for the fppf topology of algebraic spaces.

Deliberately untagged: Stacks 06ER asserts this for all five topologies of Stacks 03YH at once,
and the syntomic case is still missing. -/
theorem isLocalAtSource_fppf_of_schemes
    (P : MorphismProperty Scheme.{u}) (hP : IsEtaleLocalOnSourceAndTarget P)
    [P.IsLocalAtSource Scheme.fppfPrecoverage] :
    MorphismProperty.IsLocalAtSource
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) =>
        HoldsOnEveryEtaleChart B S hS P f.hom)
      (Topology.precoverage.{u, v} .fppf B S hS) :=
  isLocalAtSource_of_schemes_of_coveringTransfer B S hS .fppf Scheme.fppfPrecoverage P hP ‹_›
    (isFppfCovering_yoneda_of_isCovering B S hS) (isFppfCovering_baseChange_of_chart B S hS)
    (etale_atlases_comp_isFppfCovering B S hS)

end AlgebraicGeometry.Space

end
