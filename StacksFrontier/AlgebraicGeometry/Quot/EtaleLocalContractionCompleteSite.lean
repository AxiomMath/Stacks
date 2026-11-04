module

public import StacksFrontier.AlgebraicGeometry.Quot.EtaleLocalContractionComplete
public import StacksFrontier.AlgebraicGeometry.Quot.ContractionUniquenessCompleteSite
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.QuasiAffineClosedInFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.StructureSheafIsoNearSpecialFibreTransport
public import StacksFrontier.AlgebraicGeometry.NodalContraction.CentreFibre

/-!
# Extending a contraction of the closed fibre over a complete local object of the site

Let `W` be an object of the big fppf site of a scheme `S` whose underlying scheme is, through `ε`,
the spectrum of a complete Noetherian local ring `Λ`, with closed point `k : K ⟶ W`. Let
`p : P ⟶ W` be a proper flat morphism of algebraic spaces whose closed fibre is presented by an
object `F` of the site of dimension at most one, and let `h₀ : F ⟶ Y₀` be a morphism over `K` to a
proper scheme of dimension at most one with `𝒪_{Y₀} ≅ h₀,*𝒪_F` and `R¹h₀,*𝒪_F = 0`. Then there
are an object `Q` of the site with a proper, flat, finitely presented morphism `q : Q ⟶ W` of
relative dimension at most one, and a morphism `c : P ⟶ Q` over `W`, whose closed fibre is `h₀`:
the closed fibre of `Q` is presented by an object `G` whose scheme is `Y₀`, and `c` restricts to
`h₀` on the presentations.

This is the case of a complete Noetherian local base in the proof of [Stacks, Tag 0E7C], for
algebraic spaces over a big fppf site: `P` is a scheme ([Stacks, Tag 0AE7],
`AlgebraicGeometry.Space.exists_iso_yoneda_of_isProper_of_closedFibre`), and the statement is the
scheme case `AlgebraicGeometry.EtaleLocalContraction.exists_contraction_of_isAdicComplete`.

## Main results

* `AlgebraicGeometry.Space.relativeDimensionLE_yoneda_of_fiberDimension_le`: a morphism of the
  site whose scheme fibres have dimension at most `d` has relative dimension at most `d`.
* `AlgebraicGeometry.EtaleLocalContraction.exists_contraction_of_isAdicComplete_of_siteObject`:
  the statement above.

## References

* [Stacks Project, Tag 0E7C](https://stacks.math.columbia.edu/tag/0E7C)
* [Stacks Project, Tag 0AE7](https://stacks.math.columbia.edu/tag/0AE7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

/-! ### Relative dimension of a morphism of the site from its fibres -/

namespace Space

private theorem exists_nat_localDimension_of_le {T : Type*} [TopologicalSpace T]
    (x : T) (d : ℕ) (hd : topologicalKrullDimAt T x ≤ (d : WithBot ℕ∞)) :
    ∃ e : ℕ, e ≤ d ∧ topologicalKrullDimAt T x = (e : WithBot ℕ∞) := by
  have hne : topologicalKrullDimAt T x ≠ ⊥ := by
    obtain ⟨⟨U, hxU, _, hdim⟩, _⟩ := topologicalKrullDimAt_isLeast T x
    intro hbot
    have hU : topologicalKrullDim U = ⊥ := hdim.symm.trans hbot
    exact ((topologicalKrullDim_eq_bot_iff_isEmpty U).mp hU).false ⟨x, hxU⟩
  obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.mp hne
  have he' : e ≤ (d : ℕ∞) := WithBot.coe_le_coe.mp (he ▸ hd)
  have hn : e ≠ ⊤ := ne_top_of_le_ne_top (by simp) he'
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp hn
  exact ⟨n, ENat.natCast_le_natCast.mp he', he.symm⟩

/-- A morphism of schemes locally of finite type all of whose fibres have dimension at most `d`
has, at any point, germ fibre dimension some natural number at most `d`. -/
theorem exists_hasFiberDimensionAt_of_fiberDimension_le {X Y : Scheme.{u}} (g : X ⟶ Y)
    [LocallyOfFiniteType g] (x : X) (d : ℕ)
    (hd : ∀ y, g.fiberDimension y ≤ (d : WithBot ℕ∞)) :
    ∃ e : ℕ, e ≤ d ∧ HasFiberDimensionAt (e : ℕ∞) (MorphismOfGerms.ofSchemeHom g x) := by
  set h : ((⊤ : X.Opens) : Scheme.{u}) ⟶ Y := X.topIso.hom ≫ g with hh
  set z : ((⊤ : X.Opens) : Scheme.{u}) := ⟨x, by simp⟩ with hz
  have hpb : IsPullback X.topIso.hom h g (𝟙 Y) := IsPullback.of_horiz_isIso ⟨by simp [hh]⟩
  have hpt : X.topIso.hom z = x := by simp [hz]
  have heq : topologicalKrullDimAt (h.fiber (h z)) (h.asFiber z) =
      topologicalKrullDimAt (g.fiber (g x)) (g.asFiber x) := by
    rw [← hpt]
    exact topologicalKrullDimAt_fiber_eq_of_isPullback hpb z
  have hle : topologicalKrullDimAt (h.fiber (h z)) (h.asFiber z) ≤ (d : WithBot ℕ∞) :=
    heq ▸ ((AlgebraicGeometry.topologicalKrullDimAt_le_topologicalKrullDim _).trans (hd (g x)))
  obtain ⟨e, hen, hee⟩ := exists_nat_localDimension_of_le (h.asFiber z) d hle
  exact ⟨e, hen, { source := ⊤
                   mem_source := by simp
                   hom := h
                   map_point := rfl }, rfl, hee⟩

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Relative dimension of a morphism of the site from its fibres.** A morphism of the big fppf
site whose underlying morphism of schemes is locally of finite type with all fibres of dimension
at most `d` has relative dimension at most `d` (Stacks 06LR) as a morphism of algebraic
spaces. -/
theorem relativeDimensionLE_yoneda_of_fiberDimension_le {U V : BigFppfOver B S hS} (f : U ⟶ V)
    [LocallyOfFiniteType f.left.hom] (d : ℕ)
    (hd : ∀ y, f.left.hom.fiberDimension y ≤ (d : WithBot ℕ∞)) :
    HasRelativeDimensionLE d B S hS (yoneda.map f) := by
  intro x
  obtain ⟨e, hen, hee⟩ := exists_hasFiberDimensionAt_of_fiberDimension_le f.left.hom
    (pointsToScheme B S hS U x) d hd
  exact ⟨e, hen, (holdsOnEveryEtaleChartAtPoint_yoneda_map_iff B S hS
    (@HasFiberDimensionAt.{u} (e : ℕ∞))
    (fiberDimensionAt_isEtaleLocalOnSourceAndTarget (e : ℕ∞)) f x).2 hee⟩

end Space

/-! ### The complete case over an object of the site -/

namespace EtaleLocalContraction

open ContractionUniquenessComplete Stacks.AlgebraicGeometry.TopDegreeBaseChange

/-- The fibres of a morphism of schemes have dimension at most that of the source. -/
theorem topologicalKrullDim_fiber_le {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) :
    topologicalKrullDim (f.fiber y) ≤ topologicalKrullDim X := by
  rw [(f.fiberHomeo y).isHomeomorph.topologicalKrullDim_eq]
  exact Topology.IsInducing.topologicalKrullDim_le (Topology.IsEmbedding.subtypeVal.isInducing)

/-- **`𝒪 ≅ h_*𝒪` and `R¹h_*𝒪 = 0` are invariant under precomposition with an isomorphism**, for a
proper morphism with fibres of dimension at most one. -/
theorem isIso_and_isZero_of_iso_comp {X X' Y : Scheme.{u}} (e : X' ⟶ X) [IsIso e] (h : X ⟶ Y)
    [IsProper h] (hdim : topologicalKrullDim X ≤ 1)
    (h0 : IsIso (Scheme.Modules.unitToPushforwardUnit h))
    (hR : IsZero (((Scheme.Modules.pushforward h).rightDerived 1).obj
      (SheafOfModules.unit X.ringCatSheaf))) :
    IsIso (Scheme.Modules.unitToPushforwardUnit (e ≫ h)) ∧
      IsZero (((Scheme.Modules.pushforward (e ≫ h)).rightDerived 1).obj
        (SheafOfModules.unit X'.ringCatSheaf)) := by
  let := HasDerivedCategory.standard X.Modules
  let := HasDerivedCategory.standard X'.Modules
  let := HasDerivedCategory.standard Y.Modules
  have H : IsPullback e (e ≫ h) h (𝟙 Y) := IsPullback.of_horiz_isIso ⟨by simp⟩
  have hdimF : ∀ y : Y, topologicalKrullDim (h.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞) :=
    fun y => (topologicalKrullDim_fiber_le h y).trans (by exact_mod_cast hdim)
  have hR' : IsZero (firstDirectImageStructureSheaf h) :=
    (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff (Scheme.Modules.pushforward h)
      (m := (1 : ℤ)) (n := 1) rfl _).2 hR
  obtain ⟨hR'', h0''⟩ := isZero_and_isIso_of_isPullback H hdimF hR' h0
  exact ⟨h0'', (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff
    (Scheme.Modules.pushforward (e ≫ h)) (m := (1 : ℤ)) (n := 1) rfl _).1 hR''⟩

attribute [local instance] Space.preservesLimitsOfShape_walkingCospan_toScheme

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

local notation "𝒯S" => BigFppfOver.toScheme B S hS

/-- **Extending a contraction of the closed fibre over a complete local object of the site.**
Let `W` be an object of the big fppf site whose underlying scheme is, through `ε`, the spectrum of
a complete Noetherian local ring `Λ`, and `k : K ⟶ W` its closed point (through `ι`). Let
`p : P ⟶ W` be a proper flat morphism of algebraic spaces whose fibre over `k` is presented by
`t : F ⟶ K` with `dim F ≤ 1`, and let `h₀ : F ⟶ Y₀` be a morphism over `K` to a proper scheme of
dimension at most one with `𝒪_{Y₀} ≅ h₀,*𝒪_F` and `R¹h₀,*𝒪_F = 0`. Then there are a morphism
`q : Q ⟶ W` of the site which is proper, flat, of finite presentation and of relative dimension at
most one, and a morphism `c : P ⟶ Q` over `W` whose fibre over `k` is `h₀`: the fibre of `Q` over
`k` is presented by `tG : G ⟶ K` with `G ≅ Y₀` over `K`, and `c` restricts to `h₀` on the
presentations (`a ≫ tG = t`). -/
theorem exists_contraction_of_isAdicComplete_of_siteObject (Λ : Type u) [CommRing Λ]
    [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ]
    (W : BigFppfOver B S hS) (ε : (𝒯S).obj W ≅ Spec (.of Λ))
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP : IsAlgebraicSpace B S hS P)
    (p : P ⟶ yoneda.obj W) (hpr : Space.IsProper B S hS p) (hfl : Space.IsFlat B S hS p)
    {K F : BigFppfOver B S hS} (k : K ⟶ W) (ι : Spec (.of (ResidueField Λ)) ≅ (𝒯S).obj K)
    (hι : ι.hom ≫ (𝒯S).map k ≫ ε.hom = ContractionUniquenessComplete.closedPoint Λ)
    (t : F ⟶ K) (i : yoneda.obj F ⟶ P) (hi : IsPullback i (yoneda.map t) p (yoneda.map k))
    (hdimF : topologicalKrullDim ((𝒯S).obj F) ≤ 1)
    {Y₀ : Scheme.{u}} (pY₀ : Y₀ ⟶ (𝒯S).obj K) [IsProper pY₀]
    (hdimY : topologicalKrullDim Y₀ ≤ 1) (h₀ : (𝒯S).obj F ⟶ Y₀) (hh₀ : h₀ ≫ pY₀ = (𝒯S).map t)
    (h0 : IsIso (Scheme.Modules.unitToPushforwardUnit h₀))
    (hR : IsZero (((Scheme.Modules.pushforward h₀).rightDerived 1).obj
      (SheafOfModules.unit ((𝒯S).obj F).ringCatSheaf))) :
    ∃ (Q : BigFppfOver B S hS) (q : Q ⟶ W) (c : P ⟶ yoneda.obj Q),
      Space.IsProper B S hS (yoneda.map q) ∧ Space.IsFlat B S hS (yoneda.map q) ∧
      Space.IsFinitePresentation B S hS (yoneda.map q) ∧
      Space.HasRelativeDimensionLE 1 B S hS (yoneda.map q) ∧ c ≫ yoneda.map q = p ∧
      ∃ (G : BigFppfOver B S hS) (tG : G ⟶ K) (iG : G ⟶ Q) (φ : (𝒯S).obj G ≅ Y₀) (a : F ⟶ G),
        IsPullback (yoneda.map iG) (yoneda.map tG) (yoneda.map q) (yoneda.map k) ∧
        φ.hom ≫ pY₀ = (𝒯S).map tG ∧ a ≫ tG = t ∧ i ≫ c = yoneda.map a ≫ yoneda.map iG ∧
        (𝒯S).map a ≫ φ.hom = h₀ := by
  -- `P` is a scheme (Stacks 0AE7)
  obtain ⟨QX, qX, eX, heX⟩ :=
    Space.exists_iso_yoneda_of_isProper_of_closedFibre B S hS Λ W ε hP p hpr k ι hι t i hi hdimF
  set fX' := (𝒯S).map qX ≫ ε.hom with hfX'
  have : IsProper fX' := (Space.isProper_and_flat_of_iso_yoneda B S hS ε eX heX).1 hpr
  have : Flat fX' := (Space.isProper_and_flat_of_iso_yoneda B S hS ε eX heX).2 hfl
  obtain ⟨jX, hjX, sqX⟩ :=
    Space.exists_isPullback_closedPoint_of_isPullback_of_iso B S hS Λ ε eX heX k ι hι t i hi
  have : IsProper ((𝒯S).map t ≫ ι.inv) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsProper) sqX
      inferInstance
  have : IsProper ((𝒯S).map t) := by
    have e : (𝒯S).map t = ((𝒯S).map t ≫ ι.inv) ≫ ι.hom := by simp
    rw [e]
    infer_instance
  have : IsProper h₀ := by
    have : IsProper (h₀ ≫ pY₀) := by rw [hh₀]; infer_instance
    exact IsProper.of_comp h₀ pY₀
  set h₀' := sqX.isoPullback.inv ≫ h₀ with hh₀'def
  have hh₀' :
      h₀' ≫ (pY₀ ≫ ι.inv) = pullback.snd fX' (ContractionUniquenessComplete.closedPoint Λ) := by
    rw [hh₀'def, Category.assoc, reassoc_of% hh₀]
    exact sqX.isoPullback_inv_snd
  obtain ⟨h0', hR'⟩ := isIso_and_isZero_of_iso_comp sqX.isoPullback.inv h₀ hdimF h0 hR
  obtain ⟨Y, fY, h, j, -, hprY, hflY, hfpY, hdimY', hh, hjpb, hjh⟩ :=
    exists_contraction_of_isAdicComplete (Λ := Λ) inferInstance fX' h₀' (pY₀ ≫ ι.inv) hh₀' h0' hR'
      inferInstance hdimY
  have hYc : B.Contains Y :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (fY ≫ ε.inv) W.left.property
  let qY : B.obj hYc ⟶ W.left := ObjectProperty.homMk (fY ≫ ε.inv)
  let Q : BigFppfOver B S hS := Over.mk (qY ≫ W.hom)
  let q : Q ⟶ W := Over.homMk qY rfl
  have hq : (𝒯S).map q = fY ≫ ε.inv := rfl
  have hqY : IsProper ((𝒯S).map q) := by rw [hq]; infer_instance
  have hfY : Flat ((𝒯S).map q) := by rw [hq]; infer_instance
  have hfpq : FinitePresentation ((𝒯S).map q) := by
    obtain ⟨h1, h2, h3⟩ := hfpY
    rw [hq]
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  have hdimq : ∀ y, ((𝒯S).map q).fiberDimension y ≤ ((1 : ℕ) : WithBot ℕ∞) := by
    intro y
    have H : IsPullback (𝟙 Y) (fY ≫ ε.inv) fY ε.hom := IsPullback.of_horiz_isIso ⟨by simp⟩
    rw [hq, Scheme.Hom.fiberDimension_eq_of_isPullback H]
    exact hdimY' _
  have : LocallyOfFiniteType q.left.hom := inferInstanceAs (LocallyOfFiniteType ((𝒯S).map q))
  have hγ : h ≫ fY ≫ ε.inv = (𝒯S).map qX := by
    rw [reassoc_of% hh, hfX', Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let γ : QX ⟶ Q := Over.homMk (ObjectProperty.homMk h) (by
    apply ObjectProperty.hom_ext
    show (h ≫ fY) ≫ ε.inv ≫ W.hom.hom = QX.hom.hom
    rw [Category.assoc, ← Category.assoc fY, ← Category.assoc h, hγ]
    exact congrArg (fun m => m.hom) (Over.w qX))
  have hγq : γ ≫ q = qX := Over.OverMorphism.ext (ObjectProperty.hom_ext _ hγ)
  have hγT : (𝒯S).map γ = h := rfl
  let c : P ⟶ yoneda.obj Q := eX.inv ≫ yoneda.map γ
  have hc : c ≫ yoneda.map q = p := by
    simp only [c, Category.assoc, ← Functor.map_comp, hγq, ← heX, Iso.inv_hom_id_assoc]
  have hk : (𝒯S).map k = ι.inv ≫ ContractionUniquenessComplete.closedPoint Λ ≫ ε.inv := by
    rw [← hι]
    simp
  have hYpb : IsPullback j pY₀ ((𝒯S).map q) ((𝒯S).map k) := by
    refine IsPullback.of_iso hjpb (Iso.refl _) (Iso.refl _) ι ε.symm (by simp)
      (by simp) ?_ ?_
    · rw [Iso.refl_hom, Category.id_comp]
      exact hq.symm
    · rw [hk]
      simp
  have hGpb : IsPullback ((𝒯S).map (pullback.fst q k)) ((𝒯S).map (pullback.snd q k))
      ((𝒯S).map q) ((𝒯S).map k) := (IsPullback.of_hasPullback q k).map (𝒯S)
  obtain ⟨φ, hφ1, hφ2⟩ : ∃ φ : (𝒯S).obj (pullback q k) ≅ Y₀,
      φ.hom ≫ j = (𝒯S).map (pullback.fst q k) ∧ φ.hom ≫ pY₀ = (𝒯S).map (pullback.snd q k) :=
    ⟨hGpb.isoIsPullback _ _ hYpb, IsPullback.isoIsPullback_hom_fst _ _ _ _,
      IsPullback.isoIsPullback_hom_snd _ _ _ _⟩
  have hjXk : jX ≫ qX = t ≫ k := by
    apply yoneda.map_injective
    rw [Functor.map_comp, Functor.map_comp, hjX, Category.assoc, ← heX, Iso.inv_hom_id_assoc,
      hi.w]
  let a : F ⟶ pullback q k := pullback.lift (jX ≫ γ) t (by rw [Category.assoc, hγq, hjXk])
  refine ⟨Q, q, c, Space.isProper_yoneda_map B S hS q hqY,
    Space.isFlat_yoneda_map B S hS q hfY, Space.isFinitePresentation_yoneda_map B S hS q hfpq,
    Space.relativeDimensionLE_yoneda_of_fiberDimension_le B S hS q 1 hdimq, hc,
    pullback q k, pullback.snd q k, pullback.fst q k, φ, a,
    (IsPullback.of_hasPullback q k).map yoneda, hφ2, pullback.lift_snd _ _ _, ?_, ?_⟩
  · rw [← Functor.map_comp, pullback.lift_fst, Functor.map_comp, hjX, Category.assoc]
  · apply hYpb.hom_ext
    · rw [Category.assoc, hφ1, ← Functor.map_comp, pullback.lift_fst,
        Functor.map_comp, hγT, ← IsPullback.isoPullback_hom_fst sqX, Category.assoc, hjh,
        hh₀'def, Category.assoc, Iso.hom_inv_id_assoc]
    · rw [Category.assoc, hφ2, ← Functor.map_comp,
        pullback.lift_snd, hh₀]

end EtaleLocalContraction

end AlgebraicGeometry

end
