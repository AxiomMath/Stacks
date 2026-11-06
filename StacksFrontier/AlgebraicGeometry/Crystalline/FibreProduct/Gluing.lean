module

public import StacksFrontier.AlgebraicGeometry.Crystalline.FibreProduct.AffineChart

/-!
# Fibre products of divided power schemes: gluing and the universal property

This file holds the universal property of the divided power fibre product over a chart, the
functoriality of the charts under inclusion, the gluing of the chart-wise fibre products into
a divided power scheme, and the universal property of the glued scheme against an arbitrary cone.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction Opposite
open scoped AlgebraicGeometry

universe u v w

namespace Crystalline.DividedPowerScheme

attribute [local implicit_reducible] specDividedPowerScheme toSpecDividedPowerScheme
  specDividedPowerSchemeUnit specDividedPowerHomEquiv

attribute [local implicit_reducible] affineDividedPowerPushoutComparison

attribute [local implicit_reducible] dividedPowersOfSeparatingFamily

attribute [local implicit_reducible] idealTypeSheaf

attribute [local implicit_reducible] kernelSubmodule

attribute [local implicit_reducible] kernelSubmoduleIsLimit

attribute [local implicit_reducible] kernelSubmoduleIso

attribute [local implicit_reducible] dividedPowerIdealData

attribute [local implicit_reducible] openDividedPowerScheme

attribute [local implicit_reducible] openDividedPowerInclusion

attribute [local implicit_reducible] inducedOpenLift

attribute [local implicit_reducible] globalSectionsDPMorphism

attribute [local implicit_reducible] dividedPowerSchemeForget

attribute [local implicit_reducible] coneSchemeComparison

attribute [local implicit_reducible] zeroDividedPowerScheme

attribute [local implicit_reducible] zeroDividedPowerScheme_map

attribute [local implicit_reducible] zeroClosedFiberPresentation

attribute [local implicit_reducible] zeroDividedPowerScheme_map_factorSpec

attribute [local implicit_reducible] zeroDividedPowerScheme_map_factor

attribute [local implicit_reducible] closedFiberFunctor

attribute [local implicit_reducible] DividedPowerOpenPresentation.closedFiberGluing

attribute [local implicit_reducible] DividedPowerOpenPresentation.ideal

attribute [local implicit_reducible] DividedPowerOpenPresentation.basisDividedPowers

attribute [local implicit_reducible] DividedPowerOpenPresentation.gluedMap

attribute [local implicit_reducible] DividedPowerOpenPresentation.cocone

attribute [local implicit_reducible] DividedPowerOpenPresentation.isColimit

attribute [local implicit_reducible] restrictDividedPowerHom

attribute [local implicit_reducible] DividedPowerPullbackChart.data

attribute [local implicit_reducible] DividedPowerPullbackChart.fst

attribute [local implicit_reducible] DividedPowerPullbackChart.snd

/-- A divided-power cone landing in the two chart opens factors uniquely through the local
pullback. -/
private noncomputable def DividedPowerPullbackChart.lift
    {T T' S : DividedPowerScheme.{u}} {f : T ⟶ S} {g : T' ⟶ S}
    (a : DividedPowerPullbackChart f g) (c : PullbackCone f g)
    (h₁ : Set.range c.fst.hom ⊆ a.left.1) (h₂ : Set.range c.snd.hom ⊆ a.right.1) :
    c.pt ⟶ a.obj := by
  let p : c.pt.scheme ⟶ a.left.1 :=
    IsOpenImmersion.lift a.left.1.ι c.fst.hom (by simpa using h₁)
  let q : c.pt.scheme ⟶ a.right.1 :=
    IsOpenImmersion.lift a.right.1.ι c.snd.hom (by simpa using h₂)
  let p' := inducedOpenLift (openDividedPowerInclusion T a.left.1.ι)
    (openDividedPowerInclusion_isInducedOpen T _) c.fst p (IsOpenImmersion.lift_fac ..)
  let q' := inducedOpenLift (openDividedPowerInclusion T' a.right.1.ι)
    (openDividedPowerInclusion_isInducedOpen T' _) c.snd q (IsOpenImmersion.lift_fac ..)
  have hw : p' ≫ restrictDividedPowerHom f a.base.1 a.left.1 a.left_le =
      q' ≫ restrictDividedPowerHom g a.base.1 a.right.1 a.right_le := by
    have : Mono (openDividedPowerInclusion S a.base.1.ι) := by
      have hi : Mono (openDividedPowerInclusion S a.base.1.ι).hom :=
        inferInstanceAs (Mono a.base.1.ι)
      exact dividedPower_mono_of_hom _
    apply (cancel_mono (openDividedPowerInclusion S a.base.1.ι)).mp
    rw [Category.assoc, Category.assoc, restrictDividedPowerHom_comp,
      restrictDividedPowerHom_comp, ← Category.assoc, ← Category.assoc,
      inducedOpenLift_comp, inducedOpenLift_comp]
    exact c.condition
  exact a.isPullbackDP.lift p' q' hw

attribute [local implicit_reducible] DividedPowerPullbackChart.lift

private theorem DividedPowerPullbackChart.lift_fst
    {T T' S : DividedPowerScheme.{u}} {f : T ⟶ S} {g : T' ⟶ S}
    (a : DividedPowerPullbackChart f g) (c : PullbackCone f g)
    (h₁ : Set.range c.fst.hom ⊆ a.left.1) (h₂ : Set.range c.snd.hom ⊆ a.right.1) :
    a.lift c h₁ h₂ ≫ a.fst = c.fst := by
  dsimp only [DividedPowerPullbackChart.lift, DividedPowerPullbackChart.fst]
  rw [← Category.assoc, IsPullback.lift_fst, inducedOpenLift_comp]

private theorem DividedPowerPullbackChart.lift_snd
    {T T' S : DividedPowerScheme.{u}} {f : T ⟶ S} {g : T' ⟶ S}
    (a : DividedPowerPullbackChart f g) (c : PullbackCone f g)
    (h₁ : Set.range c.fst.hom ⊆ a.left.1) (h₂ : Set.range c.snd.hom ⊆ a.right.1) :
    a.lift c h₁ h₂ ≫ a.snd = c.snd := by
  dsimp only [DividedPowerPullbackChart.lift, DividedPowerPullbackChart.snd]
  rw [← Category.assoc, IsPullback.lift_snd, inducedOpenLift_comp]

private theorem DividedPowerPullbackChart.range_fst
    {T T' S : DividedPowerScheme.{u}} {f : T ⟶ S} {g : T' ⟶ S}
    (a : DividedPowerPullbackChart f g) : Set.range a.fst.hom ⊆ a.left.1 := by
  rintro _ ⟨x, rfl⟩
  exact (a.data.cone.fst.hom x).property

private theorem DividedPowerPullbackChart.range_snd
    {T T' S : DividedPowerScheme.{u}} {f : T ⟶ S} {g : T' ⟶ S}
    (a : DividedPowerPullbackChart f g) : Set.range a.snd.hom ⊆ a.right.1 := by
  rintro _ ⟨x, rfl⟩
  exact (a.data.cone.snd.hom x).property

private noncomputable def DividedPowerPullbackChart.map
    {T T' S : DividedPowerScheme.{u}} {f : T ⟶ S} {g : T' ⟶ S}
    {a b : DividedPowerPullbackChart f g} (h : a ⟶ b) : a.obj ⟶ b.obj :=
  b.lift (PullbackCone.mk a.fst a.snd a.condition)
    (a.range_fst.trans (leOfHom h).2.1) (a.range_snd.trans (leOfHom h).2.2)

attribute [local implicit_reducible] DividedPowerPullbackChart.map

private theorem DividedPowerPullbackChart.map_fst
    {T T' S : DividedPowerScheme.{u}} {f : T ⟶ S} {g : T' ⟶ S}
    {a b : DividedPowerPullbackChart f g} (h : a ⟶ b) :
    DividedPowerPullbackChart.map h ≫ b.fst = a.fst := b.lift_fst _ _ _

private theorem DividedPowerPullbackChart.map_snd
    {T T' S : DividedPowerScheme.{u}} {f : T ⟶ S} {g : T' ⟶ S}
    {a b : DividedPowerPullbackChart f g} (h : a ⟶ b) :
    DividedPowerPullbackChart.map h ≫ b.snd = a.snd := b.lift_snd _ _ _

private noncomputable def dividedPowerPullbackChartFunctor
    {T T' S : DividedPowerScheme.{u}} (f : T ⟶ S) (g : T' ⟶ S) :
    DividedPowerPullbackChart f g ⥤ DividedPowerScheme.{u} where
  obj a := a.obj
  map := DividedPowerPullbackChart.map
  map_id a := a.hom_ext _ _ (by rw [DividedPowerPullbackChart.map_fst, Category.id_comp])
    (by rw [DividedPowerPullbackChart.map_snd, Category.id_comp])
  map_comp h k := by
    apply DividedPowerPullbackChart.hom_ext
    · rw [DividedPowerPullbackChart.map_fst, Category.assoc,
        DividedPowerPullbackChart.map_fst, DividedPowerPullbackChart.map_fst]
    · rw [DividedPowerPullbackChart.map_snd, Category.assoc,
        DividedPowerPullbackChart.map_snd, DividedPowerPullbackChart.map_snd]

attribute [local implicit_reducible] dividedPowerPullbackChartFunctor

/-- The local divided-power pullback embeds into its open chart in the ordinary pullback. -/
private noncomputable def DividedPowerPullbackChart.toOpen
    {T T' S : DividedPowerScheme.{u}} {f : T ⟶ S} {g : T' ⟶ S}
    (a : DividedPowerPullbackChart f g) : a.obj.scheme ⟶ a.open :=
  coneSchemeComparison a.data.cone ≫ a.isPullback.isoPullback.inv

attribute [local implicit_reducible] DividedPowerPullbackChart.toOpen

private theorem DividedPowerPullbackChart.toOpen_isClosedImmersion
    {T T' S : DividedPowerScheme.{u}} {f : T ⟶ S} {g : T' ⟶ S}
    (a : DividedPowerPullbackChart f g) : IsClosedImmersion a.toOpen := by
  have hi := a.data.isClosedImmersion
  exact IsClosedImmersion.comp (coneSchemeComparison a.data.cone) a.isPullback.isoPullback.inv

private noncomputable abbrev DividedPowerPullbackChart.toBase
    {T T' S : DividedPowerScheme.{u}} {f : T ⟶ S} {g : T' ⟶ S}
    (a : DividedPowerPullbackChart f g) : a.obj.scheme ⟶ pullback f.hom g.hom :=
  a.toOpen ≫ a.open.ι

private theorem DividedPowerPullbackChart.toBase_fst
    {T T' S : DividedPowerScheme.{u}} {f : T ⟶ S} {g : T' ⟶ S}
    (a : DividedPowerPullbackChart f g) :
    a.toBase ≫ pullback.fst f.hom g.hom = a.fst.hom := by
  show (coneSchemeComparison a.data.cone ≫ a.isPullback.isoPullback.inv ≫ a.open.ι) ≫ _ = _
  rw [Category.assoc, Category.assoc,
    ← Scheme.Hom.resLE_comp_ι _ (inf_le_left : a.open ≤ _),
    IsPullback.isoPullback_inv_fst_assoc]
  show coneSchemeComparison a.data.cone ≫ pullback.fst _ _ ≫ a.left.1.ι = _
  simp only [← Category.assoc, coneSchemeComparison, pullback.lift_fst]
  rfl

private theorem DividedPowerPullbackChart.toBase_snd
    {T T' S : DividedPowerScheme.{u}} {f : T ⟶ S} {g : T' ⟶ S}
    (a : DividedPowerPullbackChart f g) :
    a.toBase ≫ pullback.snd f.hom g.hom = a.snd.hom := by
  show (coneSchemeComparison a.data.cone ≫ a.isPullback.isoPullback.inv ≫ a.open.ι) ≫ _ = _
  rw [Category.assoc, Category.assoc,
    ← Scheme.Hom.resLE_comp_ι _ (inf_le_right : a.open ≤ _),
    IsPullback.isoPullback_inv_snd_assoc]
  show coneSchemeComparison a.data.cone ≫ pullback.snd _ _ ≫ a.right.1.ι = _
  simp only [← Category.assoc, coneSchemeComparison, pullback.lift_snd]
  rfl

private theorem DividedPowerPullbackChart.map_toBase
    {T T' S : DividedPowerScheme.{u}} {f : T ⟶ S} {g : T' ⟶ S}
    {a b : DividedPowerPullbackChart f g} (h : a ⟶ b) :
    (DividedPowerPullbackChart.map h).hom ≫ b.toBase = a.toBase := by
  apply pullback.hom_ext
  · rw [Category.assoc, b.toBase_fst, a.toBase_fst]
    exact congrArg DividedPowerScheme.Hom.hom (DividedPowerPullbackChart.map_fst h)
  · rw [Category.assoc, b.toBase_snd, a.toBase_snd]
    exact congrArg DividedPowerScheme.Hom.hom (DividedPowerPullbackChart.map_snd h)

private theorem exists_dividedPowerPullbackChart_refinement
    {T T' S : DividedPowerScheme.{u}} (f : T ⟶ S) (g : T' ⟶ S)
    (U : S.scheme.Opens) (V : T.scheme.Opens) (W : T'.scheme.Opens)
    (x : ↥(pullback f.hom g.hom)) (hU : f.hom (pullback.fst f.hom g.hom x) ∈ U)
    (hV : pullback.fst f.hom g.hom x ∈ V) (hW : pullback.snd f.hom g.hom x ∈ W) :
    ∃ a : DividedPowerPullbackChart f g,
      a.base.1 ≤ U ∧ a.left.1 ≤ V ∧ a.right.1 ≤ W ∧ x ∈ a.open := by
  obtain ⟨A, hA, hxA, hAU⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.scheme.isBasis_affineOpens hU
  obtain ⟨B, hB, hxB, hBV⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    T.scheme.isBasis_affineOpens (U := V ⊓ f.hom ⁻¹ᵁ A) ⟨hV, hxA⟩
  have he : f.hom (pullback.fst f.hom g.hom x) = g.hom (pullback.snd f.hom g.hom x) :=
    congrArg (fun k : pullback f.hom g.hom ⟶ S.scheme => k x) pullback.condition
  obtain ⟨C, hC, hxC, hCW⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    T'.scheme.isBasis_affineOpens (U := W ⊓ g.hom ⁻¹ᵁ A)
      ⟨hW, by
        show g.hom (pullback.snd f.hom g.hom x) ∈ A
        rw [← he]
        exact hxA⟩
  exact ⟨⟨⟨A, hA⟩, ⟨B, hB⟩, ⟨C, hC⟩, hBV.trans inf_le_right, hCW.trans inf_le_right⟩,
    hAU, hBV.trans inf_le_left, hCW.trans inf_le_left, hxB, hxC⟩

private abbrev dividedPowerPullbackBaseCover
    {T T' S : DividedPowerScheme.{u}} (f : T ⟶ S) (g : T' ⟶ S) :
    (pullback f.hom g.hom).OpenCover where
  I₀ := DividedPowerPullbackChart f g
  X a := a.open
  f a := a.open.ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, fun _ => inferInstance⟩
    intro x
    obtain ⟨a, _, _, _, hx⟩ := exists_dividedPowerPullbackChart_refinement f g ⊤ ⊤ ⊤ x
      trivial trivial trivial
    exact ⟨a, ⟨x, hx⟩, rfl⟩

private instance dividedPowerPullbackBaseCover_locallyDirected
    {T T' S : DividedPowerScheme.{u}} (f : T ⟶ S) (g : T' ⟶ S) :
    (dividedPowerPullbackBaseCover f g).LocallyDirected where
  trans h := (pullback f.hom g.hom).homOfLE (DividedPowerPullbackChart.open_le_open (leOfHom h))
  trans_id _ := by simp
  trans_comp _ _ := by simp
  w _ := by simp
  directed {a b} z := by
    let x := (pullback.fst a.open.ι b.open.ι z).val
    have ha : x ∈ a.open := (pullback.fst a.open.ι b.open.ι z).property
    have he : x = (pullback.snd a.open.ι b.open.ι z).val :=
      congrArg (fun k : pullback a.open.ι b.open.ι ⟶ pullback f.hom g.hom => k z)
        pullback.condition
    have hb : x ∈ b.open := he ▸ (pullback.snd a.open.ι b.open.ι z).property
    obtain ⟨c, hU, hV, hW, hc⟩ := exists_dividedPowerPullbackChart_refinement f g
      (a.base.1 ⊓ b.base.1) (a.left.1 ⊓ b.left.1) (a.right.1 ⊓ b.right.1) x
      ⟨a.left_le ha.1, b.left_le hb.1⟩ ⟨ha.1, hb.1⟩ ⟨ha.2, hb.2⟩
    let hca : c ≤ a := ⟨hU.trans inf_le_left, hV.trans inf_le_left, hW.trans inf_le_left⟩
    let hcb : c ≤ b := ⟨hU.trans inf_le_right, hV.trans inf_le_right, hW.trans inf_le_right⟩
    let y : ↑((dividedPowerPullbackBaseCover f g).X c) := ⟨x, hc⟩
    refine ⟨c, homOfLE hca, homOfLE hcb, y, ?_⟩
    apply (pullback.fst a.open.ι b.open.ι).injective
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
    exact Subtype.ext (Scheme.homOfLE_apply _ y)

private theorem DividedPowerPullbackChart.map_isInducedOpen_and_range
    {T T' S : DividedPowerScheme.{u}} {f : T ⟶ S} {g : T' ⟶ S}
    {a b : DividedPowerPullbackChart f g} (h : a ⟶ b) :
    IsInducedOpen (DividedPowerPullbackChart.map h) ∧
      Set.range (DividedPowerPullbackChart.map h).hom = b.toBase ⁻¹' (a.open : Set _) := by
  let W : b.obj.scheme.Opens := b.toBase ⁻¹ᵁ a.open
  let Q := openDividedPowerScheme b.obj W.ι
  let q : Q ⟶ b.obj := openDividedPowerInclusion b.obj W.ι
  have hq := openDividedPowerInclusion_isInducedOpen b.obj W.ι
  let c : PullbackCone f g := PullbackCone.mk (q ≫ b.fst) (q ≫ b.snd)
    (by rw [Category.assoc, Category.assoc, b.condition])
  have h₁ : Set.range c.fst.hom ⊆ a.left.1 := by
    rintro _ ⟨x, rfl⟩
    have hx := x.property.1
    change pullback.fst f.hom g.hom (b.toBase (W.ι x)) ∈ a.left.1 at hx
    rwa [← Scheme.Hom.comp_apply, b.toBase_fst] at hx
  have h₂ : Set.range c.snd.hom ⊆ a.right.1 := by
    rintro _ ⟨x, rfl⟩
    have hx := x.property.2
    change pullback.snd f.hom g.hom (b.toBase (W.ι x)) ∈ a.right.1 at hx
    rwa [← Scheme.Hom.comp_apply, b.toBase_snd] at hx
  let l : Q ⟶ a.obj := a.lift c h₁ h₂
  have hl₁ : l ≫ a.fst = q ≫ b.fst := a.lift_fst c h₁ h₂
  have hl₂ : l ≫ a.snd = q ≫ b.snd := a.lift_snd c h₁ h₂
  have hl : l ≫ DividedPowerPullbackChart.map h = q :=
    b.hom_ext _ _ (by rw [Category.assoc, DividedPowerPullbackChart.map_fst, hl₁])
      (by rw [Category.assoc, DividedPowerPullbackChart.map_snd, hl₂])
  have hrange : Set.range (DividedPowerPullbackChart.map h).hom ⊆ Set.range W.ι := by
    rintro _ ⟨x, rfl⟩
    have hx : b.toBase ((DividedPowerPullbackChart.map h).hom x) ∈ a.open := by
      rw [← Scheme.Hom.comp_apply, DividedPowerPullbackChart.map_toBase]
      exact (a.toOpen x).property
    exact ⟨⟨_, hx⟩, rfl⟩
  let r : a.obj ⟶ Q := inducedOpenLift q hq (DividedPowerPullbackChart.map h)
    (IsOpenImmersion.lift W.ι (DividedPowerPullbackChart.map h).hom hrange)
    (IsOpenImmersion.lift_fac ..)
  have hr : r ≫ q = DividedPowerPullbackChart.map h := inducedOpenLift_comp ..
  have hrl : r ≫ l = 𝟙 a.obj := by
    apply a.hom_ext
    · rw [Category.assoc, hl₁, ← Category.assoc, hr,
        DividedPowerPullbackChart.map_fst, Category.id_comp]
    · rw [Category.assoc, hl₂, ← Category.assoc, hr,
        DividedPowerPullbackChart.map_snd, Category.id_comp]
  have hlr : l ≫ r = 𝟙 Q := by
    apply DividedPowerScheme.Hom.ext
    apply (cancel_mono W.ι).mp
    show ((l ≫ r) ≫ q).hom = ((𝟙 Q) ≫ q).hom
    rw [Category.assoc, hr, hl, Category.id_comp]
  have : IsIso r := ⟨l, hrl, hlr⟩
  refine ⟨hr ▸ (isInducedOpen_of_isIso r).comp hq, ?_⟩
  ext y
  exact ⟨fun hy => (hrange hy).elim fun z hz => hz ▸ z.property,
    fun hy => ⟨l.hom ⟨y, hy⟩, congrArg (fun t : Q ⟶ b.obj => t.hom ⟨y, hy⟩) hl⟩⟩

private theorem DividedPowerPullbackChart.map_isInducedOpen
    {T T' S : DividedPowerScheme.{u}} {f : T ⟶ S} {g : T' ⟶ S}
    {a b : DividedPowerPullbackChart f g} (h : a ⟶ b) :
    IsInducedOpen (DividedPowerPullbackChart.map h) :=
  (DividedPowerPullbackChart.map_isInducedOpen_and_range h).1

private theorem DividedPowerPullbackChart.isPullback_toOpen
    {T T' S : DividedPowerScheme.{u}} {f : T ⟶ S} {g : T' ⟶ S}
    {a b : DividedPowerPullbackChart f g} (h : a ⟶ b) :
    IsPullback (DividedPowerPullbackChart.map h).hom a.toOpen b.toOpen
      ((pullback f.hom g.hom).homOfLE (DividedPowerPullbackChart.open_le_open (leOfHom h))) := by
  have hi := (DividedPowerPullbackChart.map_isInducedOpen h).isOpenImmersion
  apply IsPullback.flip
  apply IsOpenImmersion.isPullback
  · apply (cancel_mono b.open.ι).mp
    simpa only [Category.assoc, Scheme.homOfLE_ι] using
      DividedPowerPullbackChart.map_toBase h
  · apply TopologicalSpace.Opens.coe_inj.mp
    show b.toOpen ⁻¹' Set.range ((pullback f.hom g.hom).homOfLE
      (DividedPowerPullbackChart.open_le_open (leOfHom h))) =
      Set.range (DividedPowerPullbackChart.map h).hom
    rw [(DividedPowerPullbackChart.map_isInducedOpen_and_range h).2]
    ext y
    constructor
    · rintro ⟨z, hz⟩
      have hz' := congrArg Subtype.val hz
      show b.toBase y ∈ a.open
      have hv : z.val = b.toBase y :=
        (Scheme.homOfLE_apply _ z).symm.trans hz'
      exact hv ▸ z.property
    · intro hy
      refine ⟨⟨b.toBase y, hy⟩, ?_⟩
      apply Subtype.ext
      simp only [Scheme.homOfLE_apply]
      rfl

private noncomputable def dividedPowerPullbackGluing
    {T T' S : DividedPowerScheme.{u}} (f : T ⟶ S) (g : T' ⟶ S) :
    (dividedPowerPullbackBaseCover f g).RelativeGluingData where
  functor := dividedPowerPullbackChartFunctor f g ⋙ dividedPowerSchemeForget
  natTrans :=
    { app a := a.toOpen
      naturality a b h := by
        change (DividedPowerPullbackChart.map h).hom ≫ b.toOpen =
          a.toOpen ≫ (pullback f.hom g.hom).homOfLE
            (DividedPowerPullbackChart.open_le_open (leOfHom h))
        apply (cancel_mono b.open.ι).mp
        simpa only [Category.assoc, Scheme.homOfLE_ι] using
          DividedPowerPullbackChart.map_toBase h }
  equifibered _ _ h := DividedPowerPullbackChart.isPullback_toOpen h

attribute [local implicit_reducible] dividedPowerPullbackGluing

private theorem isDPMorphism_of_postcomp
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    {I : Ideal A} {J : Ideal B} {K : Ideal C}
    (α : DividedPowers I) (β : DividedPowers J) (γ : DividedPowers K)
    (f : A →+* B) (g : B →+* C) (hg : Function.Injective g)
    (hJ : J = K.comap g) (hβ : DividedPowers.IsDPMorphism β γ g)
    (hα : DividedPowers.IsDPMorphism α γ (g.comp f)) :
    DividedPowers.IsDPMorphism α β f := by
  have hmem (x : A) (hx : x ∈ I) : f x ∈ J := by
    rw [hJ]
    exact hα.ideal_comp (Ideal.mem_map_of_mem _ hx)
  exact ⟨Ideal.map_le_iff_le_comap.mpr hmem, fun {_ x} hx =>
    hg ((hβ.map_dpow (hmem x hx)).trans (hα.map_dpow hx).symm)⟩

private theorem isDPMorphism_app_of_local
    (X Y : DividedPowerScheme.{u}) (f : X.scheme ⟶ Y.scheme)
    (U : Y.scheme.Opens)
    (hlocal : ∀ (x : X.scheme), x ∈ f ⁻¹ᵁ U →
      ∃ (V : X.scheme.Opens) (hV : V ≤ f ⁻¹ᵁ U), x ∈ V ∧
        DividedPowers.IsDPMorphism (Y.dividedPowers.dividedPowers (op U))
          (X.dividedPowers.dividedPowers (op V)) (f.appLE U V hV).hom) :
    DividedPowers.IsDPMorphism (Y.dividedPowers.dividedPowers (op U))
      (X.dividedPowers.dividedPowers (op (f ⁻¹ᵁ U))) (f.app U).hom := by
  have hmem (a : Γ(Y.scheme, U)) (ha : a ∈ Y.ideal.obj (op U)) :
      f.app U a ∈ X.ideal.obj (op (f ⁻¹ᵁ U)) := by
    apply X.ideal.isSheaf
    intro x hx
    obtain ⟨V, hV, hxV, hdp⟩ := hlocal x hx
    exact ⟨V, homOfLE hV, hdp.ideal_comp (Ideal.mem_map_of_mem _ ha), hxV⟩
  refine ⟨Ideal.map_le_iff_le_comap.mpr hmem, ?_⟩
  intro n a ha
  apply TopCat.Presheaf.IsSheaf.section_ext X.scheme.sheaf.property
  intro x hx
  obtain ⟨V, hV, hxV, hdp⟩ := hlocal x hx
  exact ⟨V, hV, hxV,
    ((X.dividedPowers.naturality (homOfLE hV).op).map_dpow (hmem a ha)).trans
      (hdp.map_dpow ha).symm⟩

/-- Divided-power compatibility descends along an open cover with induced structures. -/
private noncomputable def dividedPowerHomOfOpenCover
    {J : Type u} {X Y : DividedPowerScheme.{u}} (F : J → DividedPowerScheme.{u})
    (i : ∀ j, F j ⟶ X) (hi : ∀ j, IsInducedOpen (i j))
    (hsurj : ∀ x : X.scheme, ∃ j y, (i j).hom y = x)
    (f : X.scheme ⟶ Y.scheme) (m : ∀ j, F j ⟶ Y)
    (hm : ∀ j, (i j).hom ≫ f = (m j).hom) : X ⟶ Y where
  hom := f
  compatible U := by
    apply isDPMorphism_app_of_local X Y f U
    intro x hx
    obtain ⟨j, y, rfl⟩ := hsurj x
    have hi' := (hi j).isOpenImmersion
    have hy : y ∈ (i j).hom ⁻¹ᵁ (f ⁻¹ᵁ U) := hx
    obtain ⟨W, hW, hyW, hWU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      (F j).scheme.isBasis_affineOpens hy
    let V : X.scheme.affineOpens :=
      ⟨(i j).hom ''ᵁ W, hW.image_of_isOpenImmersion (i j).hom⟩
    have hV : V.1 ≤ f ⁻¹ᵁ U := by
      rintro _ ⟨z, hz, rfl⟩
      exact hWU hz
    have hW' : W ≤ (i j).hom ⁻¹ᵁ V.1 := fun z hz => ⟨z, hz, rfl⟩
    have hmap := (hi j).ideal_map V ⟨W, hW⟩ hW'
    have he : (i j).hom.appLE V.1 W hW' = ((i j).hom.appIso W).hom :=
      (Scheme.Hom.appIso_hom' _ _).symm
    have hcomap : Crystalline.sectionIdeal X.scheme.sheaf X.ideal (op V.1) =
        (Crystalline.sectionIdeal (F j).scheme.sheaf (F j).ideal (op W)).comap
          ((i j).hom.appLE V.1 W hW').hom := by
      rw [← hmap, he]
      exact (Ideal.comap_map_of_bijective _
        ((i j).hom.appIso W).commRingCatIsoToRingEquiv.bijective).symm
    refine ⟨V.1, hV, ⟨y, hyW, rfl⟩, ?_⟩
    apply isDPMorphism_of_postcomp _ _ _ (f.appLE U V.1 hV).hom
      ((i j).hom.appLE V.1 W hW').hom
      (by rw [he]; exact ((i j).hom.appIso W).commRingCatIsoToRingEquiv.injective)
      hcomap (dividedPowerHom_appLE (i j) V.1 W hW')
    have hWm : W ≤ (m j).hom ⁻¹ᵁ U := by rw [← hm j]; exact hWU
    have hcomp : ((i j).hom.appLE V.1 W hW').hom.comp (f.appLE U V.1 hV).hom =
        ((m j).hom.appLE U W hWm).hom := by
      rw [← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]
      simp only [hm j]
    exact hcomp ▸ dividedPowerHom_appLE (m j) U W hWm

attribute [local implicit_reducible] dividedPowerHomOfOpenCover

private theorem coneSchemeComparison_fst {X Y S : DividedPowerScheme.{u}}
    {f : X ⟶ S} {g : Y ⟶ S} (c : PullbackCone f g) :
    coneSchemeComparison c ≫ pullback.fst f.hom g.hom = c.fst.hom :=
  pullback.lift_fst ..

private theorem coneSchemeComparison_snd {X Y S : DividedPowerScheme.{u}}
    {f : X ⟶ S} {g : Y ⟶ S} (c : PullbackCone f g) :
    coneSchemeComparison c ≫ pullback.snd f.hom g.hom = c.snd.hom :=
  pullback.lift_snd ..

private noncomputable def dividedPowerPullbackPresentation
    {T T' S : DividedPowerScheme.{u}} (f : T ⟶ S) (g : T' ⟶ S) :
    DividedPowerOpenPresentation (DividedPowerPullbackChart f g)
      (dividedPowerPullbackGluing f g).glued where
  functor := dividedPowerPullbackChartFunctor f g
  ι :=
    { app a := (dividedPowerPullbackGluing f g).cover.f a
      naturality a b h := by
        change (dividedPowerPullbackGluing f g).cover.trans h ≫
          (dividedPowerPullbackGluing f g).cover.f b =
          (dividedPowerPullbackGluing f g).cover.f a ≫ 𝟙 _
        rw [Category.comp_id]
        exact (dividedPowerPullbackGluing f g).cover.trans_map h }
  isOpen a := (dividedPowerPullbackGluing f g).cover.map_prop a
  surjective x := (dividedPowerPullbackGluing f g).cover.exists_eq x
  induced h := DividedPowerPullbackChart.map_isInducedOpen h
  directed xi xj h := (dividedPowerPullbackGluing f g).cover.exists_of_f_eq_f xi xj h

attribute [local implicit_reducible] dividedPowerPullbackPresentation

private theorem dividedPowerPullbackGluing_isClosedImmersion
    {T T' S : DividedPowerScheme.{u}} (f : T ⟶ S) (g : T' ⟶ S) :
    IsClosedImmersion (dividedPowerPullbackGluing f g).toBase := by
  apply IsZariskiLocalAtTarget.of_openCover (dividedPowerPullbackBaseCover f g)
  intro a
  let e := ((dividedPowerPullbackGluing f g).isPullback_natTrans_ι_toBase a).flip.isoPullback
  have he : (dividedPowerPullbackBaseCover f g).pullbackHom
      (dividedPowerPullbackGluing f g).toBase a = e.inv ≫ a.toOpen := by
    apply (cancel_epi e.hom).mp
    rw [e.hom_inv_id_assoc]
    exact ((dividedPowerPullbackGluing f g).isPullback_natTrans_ι_toBase a).flip.isoPullback_hom_snd
  rw [he]
  exact @IsClosedImmersion.comp _ _ _ e.inv a.toOpen inferInstance
    a.toOpen_isClosedImmersion

/-- Maps out of the glued divided-power pullback, defined chart by chart. -/
private noncomputable def dividedPowerPullbackDesc
    {T T' S X : DividedPowerScheme.{u}} (f : T ⟶ S) (g : T' ⟶ S)
    (p : ∀ a : DividedPowerPullbackChart f g, a.obj ⟶ X)
    (hp : ∀ {a b : DividedPowerPullbackChart f g} (h : a ⟶ b),
      DividedPowerPullbackChart.map h ≫ p b = p a) :
    (dividedPowerPullbackPresentation f g).glued ⟶ X :=
  (dividedPowerPullbackPresentation f g).isColimit.desc
    { pt := X
      ι := { app := p
             naturality a b h := by
               change DividedPowerPullbackChart.map h ≫ p b = p a ≫ 𝟙 X
               rw [Category.comp_id]
               exact hp h } }

private noncomputable def dividedPowerPullbackFst
    {T T' S : DividedPowerScheme.{u}} (f : T ⟶ S) (g : T' ⟶ S) :
    (dividedPowerPullbackPresentation f g).glued ⟶ T :=
  dividedPowerPullbackDesc f g (·.fst) DividedPowerPullbackChart.map_fst

attribute [local implicit_reducible] dividedPowerPullbackFst

private noncomputable def dividedPowerPullbackSnd
    {T T' S : DividedPowerScheme.{u}} (f : T ⟶ S) (g : T' ⟶ S) :
    (dividedPowerPullbackPresentation f g).glued ⟶ T' :=
  dividedPowerPullbackDesc f g (·.snd) DividedPowerPullbackChart.map_snd

attribute [local implicit_reducible] dividedPowerPullbackSnd

private theorem dividedPowerPullback_ι_fst
    {T T' S : DividedPowerScheme.{u}} (f : T ⟶ S) (g : T' ⟶ S)
    (a : DividedPowerPullbackChart f g) :
    (dividedPowerPullbackPresentation f g).gluedι a ≫ dividedPowerPullbackFst f g = a.fst :=
  (dividedPowerPullbackPresentation f g).isColimit.fac _ a

private theorem dividedPowerPullback_ι_snd
    {T T' S : DividedPowerScheme.{u}} (f : T ⟶ S) (g : T' ⟶ S)
    (a : DividedPowerPullbackChart f g) :
    (dividedPowerPullbackPresentation f g).gluedι a ≫ dividedPowerPullbackSnd f g = a.snd :=
  (dividedPowerPullbackPresentation f g).isColimit.fac _ a

private theorem dividedPowerPullback_condition
    {T T' S : DividedPowerScheme.{u}} (f : T ⟶ S) (g : T' ⟶ S) :
    dividedPowerPullbackFst f g ≫ f = dividedPowerPullbackSnd f g ≫ g := by
  apply (dividedPowerPullbackPresentation f g).isColimit.hom_ext
  intro a
  show (dividedPowerPullbackPresentation f g).gluedι a ≫ _ =
    (dividedPowerPullbackPresentation f g).gluedι a ≫ _
  rw [← Category.assoc, ← Category.assoc,
    dividedPowerPullback_ι_fst, dividedPowerPullback_ι_snd]
  exact a.condition

private noncomputable def dividedPowerPullbackCone
    {T T' S : DividedPowerScheme.{u}} (f : T ⟶ S) (g : T' ⟶ S) : PullbackCone f g :=
  PullbackCone.mk (dividedPowerPullbackFst f g) (dividedPowerPullbackSnd f g)
    (dividedPowerPullback_condition f g)

/-- The inclusion of a chart into the divided-power pullback cone. -/
private noncomputable def dividedPowerPullbackChartι
    {T T' S : DividedPowerScheme.{u}} {f : T ⟶ S} {g : T' ⟶ S}
    (a : DividedPowerPullbackChart f g) :
    a.obj ⟶ (dividedPowerPullbackCone f g).pt :=
  (dividedPowerPullbackPresentation f g).gluedι a

private theorem dividedPowerPullbackChartι_fst
    {T T' S : DividedPowerScheme.{u}} (f : T ⟶ S) (g : T' ⟶ S)
    (a : DividedPowerPullbackChart f g) :
    dividedPowerPullbackChartι a ≫ dividedPowerPullbackFst f g = a.fst :=
  dividedPowerPullback_ι_fst f g a

private theorem dividedPowerPullbackChartι_snd
    {T T' S : DividedPowerScheme.{u}} (f : T ⟶ S) (g : T' ⟶ S)
    (a : DividedPowerPullbackChart f g) :
    dividedPowerPullbackChartι a ≫ dividedPowerPullbackSnd f g = a.snd :=
  dividedPowerPullback_ι_snd f g a

attribute [local implicit_reducible] dividedPowerPullbackCone

/-- A chart of a relative gluing datum, followed by the structure map, is the chart's
own map to the base. -/
private theorem relativeGluing_cover_f_toBase {S : Scheme.{u}} {𝒰 : S.OpenCover}
    [Category.{u} 𝒰.I₀] [Scheme.Cover.LocallyDirected 𝒰] [Small.{u} 𝒰.I₀]
    [Quiver.IsThin 𝒰.I₀] (d : Scheme.Cover.RelativeGluingData 𝒰) (i : 𝒰.I₀) :
    d.cover.f i ≫ d.toBase = d.natTrans.app i ≫ 𝒰.f i :=
  Scheme.Cover.RelativeGluingData.ι_toBase d i

/-- The comparison from the glued divided-power pullback to the ordinary fibre product,
at the type of the glued scheme. -/
private noncomputable def dividedPowerPullbackComparison
    {T T' S : DividedPowerScheme.{u}} (f : T ⟶ S) (g : T' ⟶ S) :
    (dividedPowerPullbackGluing f g).glued ⟶ pullback f.hom g.hom :=
  coneSchemeComparison (dividedPowerPullbackCone f g)

private theorem dividedPowerPullbackComparison_fst
    {T T' S : DividedPowerScheme.{u}} (f : T ⟶ S) (g : T' ⟶ S) :
    dividedPowerPullbackComparison f g ≫ pullback.fst f.hom g.hom =
      (dividedPowerPullbackFst f g).hom :=
  coneSchemeComparison_fst (dividedPowerPullbackCone f g)

private theorem dividedPowerPullbackComparison_snd
    {T T' S : DividedPowerScheme.{u}} (f : T ⟶ S) (g : T' ⟶ S) :
    dividedPowerPullbackComparison f g ≫ pullback.snd f.hom g.hom =
      (dividedPowerPullbackSnd f g).hom :=
  coneSchemeComparison_snd (dividedPowerPullbackCone f g)

private theorem dividedPowerPullbackCone_comparison
    {T T' S : DividedPowerScheme.{u}} (f : T ⟶ S) (g : T' ⟶ S) :
    coneSchemeComparison (dividedPowerPullbackCone f g) =
      (dividedPowerPullbackGluing f g).toBase := by
  show dividedPowerPullbackComparison f g = _
  apply (dividedPowerPullbackGluing f g).cover.hom_ext
  intro a
  rw [relativeGluing_cover_f_toBase (dividedPowerPullbackGluing f g) a]
  apply pullback.hom_ext
  · rw [Category.assoc, dividedPowerPullbackComparison_fst]
    exact (congrArg DividedPowerScheme.Hom.hom (dividedPowerPullback_ι_fst f g a)).trans
      a.toBase_fst.symm
  · rw [Category.assoc, dividedPowerPullbackComparison_snd]
    exact (congrArg DividedPowerScheme.Hom.hom (dividedPowerPullback_ι_snd f g a)).trans
      a.toBase_snd.symm

attribute [local implicit_reducible] CategoryTheory.PreZeroHypercover.pullback₁
  CategoryTheory.Precoverage.ZeroHypercover.pullback₁

private noncomputable abbrev dividedPowerConeCover
    {T T' S : DividedPowerScheme.{u}} {f : T ⟶ S} {g : T' ⟶ S}
    (c : PullbackCone f g) : c.pt.scheme.OpenCover :=
  (dividedPowerPullbackBaseCover f g).pullback₁ (coneSchemeComparison c)

private noncomputable abbrev dividedPowerConeChart
    {T T' S : DividedPowerScheme.{u}} {f : T ⟶ S} {g : T' ⟶ S}
    (c : PullbackCone f g) (a : DividedPowerPullbackChart f g) : DividedPowerScheme.{u} := by
  have := (dividedPowerConeCover c).map_prop a
  exact openDividedPowerScheme c.pt ((dividedPowerConeCover c).f a)

private noncomputable abbrev dividedPowerConeChartInclusion
    {T T' S : DividedPowerScheme.{u}} {f : T ⟶ S} {g : T' ⟶ S}
    (c : PullbackCone f g) (a : DividedPowerPullbackChart f g) :
    dividedPowerConeChart c a ⟶ c.pt :=
  @openDividedPowerInclusion c.pt _ ((dividedPowerConeCover c).f a)
    ((dividedPowerConeCover c).map_prop a)

private theorem dividedPowerConeChartInclusion_range_fst
    {T T' S : DividedPowerScheme.{u}} {f : T ⟶ S} {g : T' ⟶ S}
    (c : PullbackCone f g) (a : DividedPowerPullbackChart f g) :
    Set.range (dividedPowerConeChartInclusion c a ≫ c.fst).hom ⊆ a.left.1 := by
  have he : (dividedPowerConeCover c).f a ≫ coneSchemeComparison c =
      pullback.snd (coneSchemeComparison c) a.open.ι ≫ a.open.ι := pullback.condition
  rintro _ ⟨x, rfl⟩
  have hx := (pullback.snd (coneSchemeComparison c) a.open.ι x).property.1
  change pullback.fst f.hom g.hom
    ((pullback.snd (coneSchemeComparison c) a.open.ι ≫ a.open.ι) x) ∈ a.left.1 at hx
  rw [← he, ← Scheme.Hom.comp_apply, Category.assoc, coneSchemeComparison_fst] at hx
  exact hx

private theorem dividedPowerConeChartInclusion_range_snd
    {T T' S : DividedPowerScheme.{u}} {f : T ⟶ S} {g : T' ⟶ S}
    (c : PullbackCone f g) (a : DividedPowerPullbackChart f g) :
    Set.range (dividedPowerConeChartInclusion c a ≫ c.snd).hom ⊆ a.right.1 := by
  have he : (dividedPowerConeCover c).f a ≫ coneSchemeComparison c =
      pullback.snd (coneSchemeComparison c) a.open.ι ≫ a.open.ι := pullback.condition
  rintro _ ⟨x, rfl⟩
  have hx := (pullback.snd (coneSchemeComparison c) a.open.ι x).property.2
  change pullback.snd f.hom g.hom
    ((pullback.snd (coneSchemeComparison c) a.open.ι ≫ a.open.ι) x) ∈ a.right.1 at hx
  rw [← he, ← Scheme.Hom.comp_apply, Category.assoc, coneSchemeComparison_snd] at hx
  exact hx

/-- The pullback cone on `f` and `g` cut out by one chart of the cone cover. -/
private noncomputable abbrev dividedPowerConeChartCone
    {T T' S : DividedPowerScheme.{u}} {f : T ⟶ S} {g : T' ⟶ S}
    (c : PullbackCone f g) (a : DividedPowerPullbackChart f g) : PullbackCone f g :=
  PullbackCone.mk (dividedPowerConeChartInclusion c a ≫ c.fst)
    (dividedPowerConeChartInclusion c a ≫ c.snd)
    (by rw [Category.assoc, Category.assoc, c.condition])

private noncomputable def dividedPowerConeChartLift
    {T T' S : DividedPowerScheme.{u}} {f : T ⟶ S} {g : T' ⟶ S}
    (c : PullbackCone f g) (a : DividedPowerPullbackChart f g) :
    dividedPowerConeChart c a ⟶ a.obj :=
  a.lift (dividedPowerConeChartCone c a) (dividedPowerConeChartInclusion_range_fst c a)
    (dividedPowerConeChartInclusion_range_snd c a)

attribute [local implicit_reducible] dividedPowerConeChartLift

private theorem dividedPowerConeChartLift_fst
    {T T' S : DividedPowerScheme.{u}} {f : T ⟶ S} {g : T' ⟶ S}
    (c : PullbackCone f g) (a : DividedPowerPullbackChart f g) :
    dividedPowerConeChartLift c a ≫ a.fst = dividedPowerConeChartInclusion c a ≫ c.fst :=
  a.lift_fst (dividedPowerConeChartCone c a) (dividedPowerConeChartInclusion_range_fst c a)
    (dividedPowerConeChartInclusion_range_snd c a)

private theorem dividedPowerConeChartLift_snd
    {T T' S : DividedPowerScheme.{u}} {f : T ⟶ S} {g : T' ⟶ S}
    (c : PullbackCone f g) (a : DividedPowerPullbackChart f g) :
    dividedPowerConeChartLift c a ≫ a.snd = dividedPowerConeChartInclusion c a ≫ c.snd :=
  a.lift_snd (dividedPowerConeChartCone c a) (dividedPowerConeChartInclusion_range_fst c a)
    (dividedPowerConeChartInclusion_range_snd c a)

private noncomputable def dividedPowerConeLocalLift
    {T T' S : DividedPowerScheme.{u}} {f : T ⟶ S} {g : T' ⟶ S}
    (c : PullbackCone f g) (a : DividedPowerPullbackChart f g) :
    dividedPowerConeChart c a ⟶ (dividedPowerPullbackCone f g).pt :=
  dividedPowerConeChartLift c a ≫ dividedPowerPullbackChartι a

attribute [local implicit_reducible] dividedPowerConeLocalLift

private theorem dividedPowerConeLocalLift_comparison
    {T T' S : DividedPowerScheme.{u}} {f : T ⟶ S} {g : T' ⟶ S}
    (c : PullbackCone f g) (a : DividedPowerPullbackChart f g) :
    (dividedPowerConeLocalLift c a).hom ≫ (dividedPowerPullbackGluing f g).toBase =
      (dividedPowerConeCover c).f a ≫ coneSchemeComparison c := by
  rw [← dividedPowerPullbackCone_comparison]
  apply pullback.hom_ext
  · have hmid : dividedPowerConeLocalLift c a ≫ dividedPowerPullbackFst f g =
        dividedPowerConeChartInclusion c a ≫ c.fst := by
      rw [dividedPowerConeLocalLift, Category.assoc, dividedPowerPullbackChartι_fst,
        dividedPowerConeChartLift_fst]
    rw [Category.assoc, Category.assoc, coneSchemeComparison_fst, coneSchemeComparison_fst]
    exact congrArg DividedPowerScheme.Hom.hom hmid
  · have hmid : dividedPowerConeLocalLift c a ≫ dividedPowerPullbackSnd f g =
        dividedPowerConeChartInclusion c a ≫ c.snd := by
      rw [dividedPowerConeLocalLift, Category.assoc, dividedPowerPullbackChartι_snd,
        dividedPowerConeChartLift_snd]
    rw [Category.assoc, Category.assoc, coneSchemeComparison_snd, coneSchemeComparison_snd]
    exact congrArg DividedPowerScheme.Hom.hom hmid

private noncomputable def dividedPowerConeLiftCocone
    {T T' S : DividedPowerScheme.{u}} {f : T ⟶ S} {g : T' ⟶ S}
    (c : PullbackCone f g) : Cocone (dividedPowerConeCover c).functorOfLocallyDirected where
  pt := (dividedPowerPullbackCone f g).pt.scheme
  ι :=
    { app a := (dividedPowerConeLocalLift c a).hom
      naturality a b h := by
        change (dividedPowerConeCover c).trans h ≫ (dividedPowerConeLocalLift c b).hom =
          (dividedPowerConeLocalLift c a).hom ≫ 𝟙 _
        rw [Category.comp_id]
        have := dividedPowerPullbackGluing_isClosedImmersion f g
        apply (cancel_mono (dividedPowerPullbackGluing f g).toBase).mp
        refine (Category.assoc _ _ _).trans ?_
        refine (congrArg ((dividedPowerConeCover c).trans h ≫ ·)
          (dividedPowerConeLocalLift_comparison c b)).trans ?_
        refine (Category.assoc _ _ _).symm.trans ?_
        refine (congrArg (· ≫ coneSchemeComparison c)
          ((dividedPowerConeCover c).trans_map h)).trans ?_
        exact (dividedPowerConeLocalLift_comparison c a).symm }

attribute [local implicit_reducible] dividedPowerConeLiftCocone

private noncomputable def dividedPowerConeLift
    {T T' S : DividedPowerScheme.{u}} {f : T ⟶ S} {g : T' ⟶ S}
    (c : PullbackCone f g) : c.pt ⟶ (dividedPowerPullbackCone f g).pt :=
  dividedPowerHomOfOpenCover (dividedPowerConeChart c) (dividedPowerConeChartInclusion c)
    (fun a => @openDividedPowerInclusion_isInducedOpen c.pt _
      ((dividedPowerConeCover c).f a) ((dividedPowerConeCover c).map_prop a))
    (dividedPowerConeCover c).exists_eq
    ((dividedPowerConeCover c).isColimitCoconeOfLocallyDirected.desc
      (dividedPowerConeLiftCocone c)) (dividedPowerConeLocalLift c)
    ((dividedPowerConeCover c).isColimitCoconeOfLocallyDirected.fac
      (dividedPowerConeLiftCocone c))

attribute [local implicit_reducible] dividedPowerConeLift

private theorem dividedPowerConeLift_comparison
    {T T' S : DividedPowerScheme.{u}} {f : T ⟶ S} {g : T' ⟶ S}
    (c : PullbackCone f g) :
    (dividedPowerConeLift c).hom ≫ (dividedPowerPullbackGluing f g).toBase =
      coneSchemeComparison c := by
  refine (dividedPowerConeCover c).hom_ext _ _ (fun a => ?_)
  have he : (dividedPowerConeCover c).f a ≫ (dividedPowerConeLift c).hom =
      (dividedPowerConeLocalLift c a).hom :=
    (dividedPowerConeCover c).isColimitCoconeOfLocallyDirected.fac
      (dividedPowerConeLiftCocone c) a
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ (dividedPowerPullbackGluing f g).toBase) he).trans
      (dividedPowerConeLocalLift_comparison c a))

theorem nonempty_dividedPowerPullbackData
    {T T' S : DividedPowerScheme.{u}} (f : T ⟶ S) (g : T' ⟶ S) :
    Nonempty (DividedPowerPullbackData f g) := by
  have hi : IsClosedImmersion (coneSchemeComparison (dividedPowerPullbackCone f g)) := by
    rw [dividedPowerPullbackCone_comparison]
    exact dividedPowerPullbackGluing_isClosedImmersion f g
  refine ⟨⟨dividedPowerPullbackCone f g, ?_, hi⟩⟩
  refine PullbackCone.IsLimit.mk (dividedPowerPullback_condition f g) dividedPowerConeLift ?_ ?_ ?_
  · intro c
    apply DividedPowerScheme.Hom.ext
    show (dividedPowerConeLift c).hom ≫ (dividedPowerPullbackFst f g).hom = c.fst.hom
    have he := congrArg (fun k => k ≫ pullback.fst f.hom g.hom)
      (dividedPowerConeLift_comparison c)
    simp only [← dividedPowerPullbackCone_comparison, Category.assoc,
      coneSchemeComparison_fst, dividedPowerPullbackCone, PullbackCone.mk_fst] at he
    exact he
  · intro c
    apply DividedPowerScheme.Hom.ext
    show (dividedPowerConeLift c).hom ≫ (dividedPowerPullbackSnd f g).hom = c.snd.hom
    have he := congrArg (fun k => k ≫ pullback.snd f.hom g.hom)
      (dividedPowerConeLift_comparison c)
    simp only [← dividedPowerPullbackCone_comparison, Category.assoc,
      coneSchemeComparison_snd, dividedPowerPullbackCone, PullbackCone.mk_snd] at he
    exact he
  · intro c m h₁ h₂
    apply DividedPowerScheme.Hom.ext
    apply (cancel_mono (coneSchemeComparison (dividedPowerPullbackCone f g))).mp
    rw [dividedPowerPullbackCone_comparison, dividedPowerConeLift_comparison,
      ← dividedPowerPullbackCone_comparison]
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, coneSchemeComparison_fst, coneSchemeComparison_fst]
      exact congrArg DividedPowerScheme.Hom.hom h₁
    · rw [Category.assoc, coneSchemeComparison_snd, coneSchemeComparison_snd]
      exact congrArg DividedPowerScheme.Hom.hom h₂

end Crystalline.DividedPowerScheme

end
