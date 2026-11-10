module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceRange
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartNoetherianSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactImageEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties

/-!
# Stacks 0CP9: the limit of the system of scheme-theoretic images

Let `B = lim_i B_i` be the limit of a directed inverse system of Noetherian algebraic spaces
over a scheme `S` with affine transition morphisms — an
`AlgebraicGeometry.Space.NoetherianLimitSystem`, Stacks 0CP6 — and let `G` be a diagram

```
X ⟶ W
↓    ↓
B ⟶ B_i
```

as in Stacks 0CP8, that is, an `AlgebraicGeometry.Space.GoodDiagram`. For a stage `i' ≥ i` let
`X_{i'}` be the scheme-theoretic image of `X ⟶ B_{i'} ×_{B_i} W`. Stacks 0CP9 asserts that the
canonical cone from `X` to the inverse system of the `X_{i'}` is a limit cone.

By `AlgebraicGeometry.Space.GoodDiagram.nonempty_isLimit_imageCone_iff` that assertion is
equivalent to the single inclusion of subfunctors of `B ×_{B_i} W`

`imageInter G ≤ Subfunctor.range G.induced`,

where `AlgebraicGeometry.Space.GoodDiagram.imageInter` is the intersection, over the stages
above `i`, of the inverse images of the `X_{i'}`. This file proves that inclusion, hence
Stacks 0CP9.

The argument is the one of the Stacks project, and of its scheme analogue Stacks 0CNQ. Since
the model `W ⟶ B_i` is of finite type and `B_i` is Noetherian, `W` is quasi-compact, so it has
a single affine étale surjective chart `U₀ ⟶ W`. Base changing it gives an affine étale
surjective chart `B ×_{B_i} U₀ ⟶ B ×_{B_i} W` of the base-changed model, and affine étale
charts `B_{i'} ×_{B_i} U₀ ⟶ B_{i'} ×_{B_i} W` of its base changes to the later stages; the
first is the limit of the others, which is
`AlgebraicGeometry.Space.AffineChartSystem.LimitBridge`, Stacks 07SF. Membership in the closed
subspace `X ⊆ B ×_{B_i} W` is local on `B ×_{B_i} W` by
`AlgebraicGeometry.Space.mem_obj_of_surjective_etale`, so it may be tested on that chart, where
it is the inclusion of the ideal sheaf of `X ×_{B ×_{B_i} W} (B ×_{B_i} U₀)` into the kernel of
the point, by `AlgebraicGeometry.Space.mem_obj_iff_exists_comp` and
`AlgebraicGeometry.Space.exists_comp_eq_of_ker_le`. The chart is affine and is a cofiltered
limit of the affine charts of the stages, so every regular function on it is pulled back from
one of those; and on the chart of a stage the ideal of `X_{i'}` is, by Stacks 082Z, the ideal of
functions vanishing on the chart of `X`, which the point kills precisely because it lies in
`X_{i'}`.

## Main definitions

* `AlgebraicGeometry.Space.GoodDiagram.modelChartSystem`: the system of affine charts
  `B_{i'} ×_{B_i} U₀` of the stages cut out by an affine scheme-valued point `U₀ ⟶ W` of the
  model.
* `AlgebraicGeometry.Space.GoodDiagram.stageChart` and
  `AlgebraicGeometry.Space.GoodDiagram.limitChart`: the induced charts
  `B_{i'} ×_{B_i} U₀ ⟶ B_{i'} ×_{B_i} W` and `B ×_{B_i} U₀ ⟶ B ×_{B_i} W` of the base-changed
  models.

## Main results

* `AlgebraicGeometry.exists_eq_ι_app_of_isColimit'`: every element of a filtered colimit of
  commutative rings comes from one of the stages.
* `AlgebraicGeometry.Space.ker_le_of_mem_schemeTheoreticImageSubfunctor`: a regular function
  killed by a morphism of the site is killed by every point of its scheme-theoretic image.
* `AlgebraicGeometry.ker_le_of_stagewise_ker_le'`: over an affine base, an inclusion of kernel
  ideal sheaves may be checked after composing with a family of morphisms to affine schemes
  whose regular functions generate.
* `AlgebraicGeometry.Space.isQuasiCompact_of_isAffineHom'`: an affine morphism of algebraic
  spaces over `S` is quasi-compact.
* `AlgebraicGeometry.Space.GoodDiagram.exists_appTop_eq_of_limitChart`: every regular function
  on the affine chart `B ×_{B_i} U₀` of the limit space is pulled back from the chart of some
  later stage.
* `AlgebraicGeometry.Space.GoodDiagram.schemeTheoreticImage_chart_eq_preimage_stageImage` is
  **Stacks 082Z, part (3)** read on these charts: on `B_{i'} ×_{B_i} U₀` the space `X_{i'}` cuts
  out the scheme-theoretic image of the chart of `X`.
* `AlgebraicGeometry.Space.GoodDiagram.imageInter_le_range_induced` is the inclusion
  `imageInter G ≤ Subfunctor.range G.induced`, and
  `AlgebraicGeometry.Space.GoodDiagram.isLimit_imageCone` is **Stacks 0CP9** itself.

## Implementation notes

Two hypotheses appear that `AlgebraicGeometry.Space.GoodDiagram` does not record. The first is
that `X` is an algebraic space over `S`, which is part of Situation 0CP6 and is needed for the
range of `X ⟶ B ×_{B_i} W` to be a closed *subspace*; the structure only asks that the morphism
be a closed immersion, which does not by itself make `X` a sheaf. The second is that the index
type is small for the site, `#I < B.cutoff.ord.cof`; it is a hypothesis of
`AlgebraicGeometry.Space.NoetherianLimitSystem.chartLimitBridge`, which constructs the limit of
the system of affine charts inside the site, and it is the only hypothesis of the statement
proved here that is not present in the source. It is therefore recorded in the clause string of
the `@[stacks 0CP9]` attribute.

The charts of the base-changed models are `CategoryTheory.Limits.pullback.lift` of the two
projections of a chart of the chart system, so that they are morphisms into the *chosen* fibre
products `B_{i'} ×_{B_i} W` that the image system is built from; `IsPullback.of_right` and
`IsPullback.of_bot` then identify them as the base changes of the chosen chart of the model and
as a cofiltered limit.

## References

* [Stacks Project, Tag 0CP6](https://stacks.math.columbia.edu/tag/0CP6)
* [Stacks Project, Tag 0CP8](https://stacks.math.columbia.edu/tag/0CP8)
* [Stacks Project, Tag 0CP9](https://stacks.math.columbia.edu/tag/0CP9)
* [Stacks Project, Tag 0CNQ](https://stacks.math.columbia.edu/tag/0CNQ)
* [Stacks Project, Tag 082X](https://stacks.math.columbia.edu/tag/082X)
* [Stacks Project, Tag 082Z](https://stacks.math.columbia.edu/tag/082Z)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry

/-! ### Filtered colimits of commutative rings -/

/-- Every element of a filtered colimit of commutative rings is the image of an element of one
of the stages. -/
lemma exists_eq_ι_app_of_isColimit' {J : Type v} [Category.{u} J] [IsFiltered J]
    {F : J ⥤ CommRingCat.{u}} {c : Cocone F} (hc : IsColimit c) (x : c.pt) :
    ∃ (j : J) (a : F.obj j), (c.ι.app j : F.obj j ⟶ c.pt).hom a = x := by
  let T (j : J) : Subring c.pt := (c.ι.app j : F.obj j ⟶ c.pt).hom.range
  let R : Subring c.pt := ⨆ j, T j
  have hR (j : J) : (c.ι.app j).hom.range ≤ R := le_iSup T j
  let d : Cocone F :=
    { pt := CommRingCat.of R
      ι :=
      { app j := CommRingCat.ofHom
          ((Subring.inclusion (S := (c.ι.app j).hom.range) (T := R) (hR j)).comp
            (c.ι.app j).hom.rangeRestrict)
        naturality := by
          intro i j g
          ext a
          exact Subtype.ext (congrArg (fun k : F.obj i ⟶ c.pt => k.hom a) (c.w g)) } }
  have h : hc.desc d ≫ CommRingCat.ofHom R.subtype = 𝟙 c.pt := by
    refine hc.hom_ext fun j => ?_
    rw [← Category.assoc, hc.fac]
    rfl
  have hx : x ∈ R := by
    have hval := congrArg (fun k : c.pt ⟶ c.pt => k.hom x) h
    change ((hc.desc d).hom x : c.pt) = x at hval
    rw [← hval]
    exact ((hc.desc d).hom x).property
  have hd : Directed (· ≤ ·) T := by
    intro i j
    obtain ⟨k, gi, gj, -⟩ := IsFilteredOrEmpty.cocone_objs i j
    refine ⟨k, ?_, ?_⟩
    · rintro _ ⟨a, rfl⟩
      exact ⟨(F.map gi).hom a, congrArg (fun k : F.obj i ⟶ c.pt => k.hom a) (c.w gi)⟩
    · rintro _ ⟨a, rfl⟩
      exact ⟨(F.map gj).hom a, congrArg (fun k : F.obj j ⟶ c.pt => k.hom a) (c.w gj)⟩
  have : Nonempty J := IsFiltered.nonempty
  exact (Subring.mem_iSup_of_directed hd).mp hx

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Scheme-theoretic images of morphisms of the site -/

/-- A morphism of the site whose underlying morphism of schemes has a base-change stable
property has that property relatively, as a morphism of representable presheaves. -/
theorem presheaf_yoneda_map_of_property' (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] {R V : BigFppfOver B S hS} (j : R ⟶ V)
    (hj : P ((BigFppfOver.toScheme B S hS).map j)) :
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf
      (yoneda.map j) := by
  classical
  have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).RespectsIso :=
    inferInstance
  refine MorphismProperty.relative.of_exists (F := yoneda)
    (P := MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)) ?_
  intro A g
  obtain ⟨g₀, rfl⟩ := yoneda.map_surjective g
  have hbase : P ((BigFppfOver.toScheme B S hS).map (pullback.snd j g₀)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      ((BigFppfOver.toScheme B S hS).map_isPullback (IsPullback.of_hasPullback j g₀)) hj
  exact ⟨pullback j g₀, yoneda.map (pullback.fst j g₀), pullback.snd j g₀,
    yoneda.map_isPullback (IsPullback.of_hasPullback j g₀), hbase⟩

/-- The scheme-theoretic image of a morphism of schemes underlying a morphism of the site is
again an object of the site: it is a closed subscheme of the target, hence no larger. -/
theorem exists_schemeImage_site' {A V : BigFppfOver B S hS} (f : A ⟶ V) :
    ∃ (R : BigFppfOver B S hS) (q : R ⟶ V) (l : A ⟶ R),
      ∃ e : (BigFppfOver.toScheme B S hS).obj R ≅
          ((BigFppfOver.toScheme B S hS).map f).image,
        (BigFppfOver.toScheme B S hS).map q =
            e.hom ≫ ((BigFppfOver.toScheme B S hS).map f).imageι ∧
          l ≫ q = f := by
  classical
  have hI : B.Contains ((BigFppfOver.toScheme B S hS).map f).image :=
    lt_of_le_of_lt (Scheme.size_le_of_mono_quasiCompact
      ((BigFppfOver.toScheme B S hS).map f).imageι) V.left.property
  let qI : B.obj hI ⟶ V.left := B.inclusion.preimage (X := B.obj hI) (Y := V.left)
    ((BigFppfOver.toScheme B S hS).map f).imageι
  let lI : A.left ⟶ B.obj hI := B.inclusion.preimage (X := A.left) (Y := B.obj hI)
    ((BigFppfOver.toScheme B S hS).map f).toImage
  have hlI : lI ≫ qI = f.left := by
    refine B.inclusion.map_injective ?_
    rw [B.inclusion.map_comp, B.inclusion.map_preimage (X := A.left) (Y := B.obj hI)
      ((BigFppfOver.toScheme B S hS).map f).toImage,
      B.inclusion.map_preimage (X := B.obj hI) (Y := V.left)
        ((BigFppfOver.toScheme B S hS).map f).imageι]
    change ((BigFppfOver.toScheme B S hS).map f).toImage ≫
      ((BigFppfOver.toScheme B S hS).map f).imageι = (BigFppfOver.toScheme B S hS).map f
    rw [Scheme.Hom.toImage_imageι]
  refine ⟨Over.mk (qI ≫ V.hom), Over.homMk qI, Over.homMk lI (by
    change lI ≫ (qI ≫ V.hom) = A.hom
    rw [← Category.assoc, hlI, f.w]), eqToIso (by rfl), ?_, ?_⟩
  · change B.inclusion.map qI = _
    rw [B.inclusion.map_preimage (X := B.obj hI) (Y := V.left)
      ((BigFppfOver.toScheme B S hS).map f).imageι]
    simp
  · ext
    exact congrArg (fun k => k.hom) hlI

/-! ### Scheme-theoretic images and kernels -/

/-- Two morphisms with the same range have the same scheme-theoretic image. -/
theorem schemeTheoreticImageSubfunctor_congr_range'
    {Y₁ Y₂ Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f₁ : Y₁ ⟶ Z) (f₂ : Y₂ ⟶ Z)
    (hZ : IsAlgebraicSpace B S hS Z)
    (h : Subfunctor.range f₁ = Subfunctor.range f₂) :
    schemeTheoreticImageSubfunctor B S hS f₁ = schemeTheoreticImageSubfunctor B S hS f₂ :=
  le_antisymm
    (schemeTheoreticImageSubfunctor_le B S hS f₁
      (isClosedSubspace_schemeTheoreticImageSubfunctor B S hS f₂ hZ)
      (le_of_eq h |>.trans (range_le_schemeTheoreticImageSubfunctor B S hS f₂)))
    (schemeTheoreticImageSubfunctor_le B S hS f₂
      (isClosedSubspace_schemeTheoreticImageSubfunctor B S hS f₁ hZ)
      (le_of_eq h.symm |>.trans (range_le_schemeTheoreticImageSubfunctor B S hS f₁)))

/-- **A regular function killed by a morphism of the site is killed by every point of its
scheme-theoretic image.** The scheme-theoretic image of `yoneda.map g` is contained in the
closed subspace cut out by the scheme-theoretic image of the underlying morphism of schemes,
so a point of it factors through that closed subscheme, whose ideal sheaf is the kernel of
`g`. -/
theorem ker_le_of_mem_schemeTheoreticImageSubfunctor {A V T : BigFppfOver B S hS}
    (g : A ⟶ V) (t : T ⟶ V)
    (ht : t ∈ (schemeTheoreticImageSubfunctor B S hS (yoneda.map g)).obj (op T)) :
    ((BigFppfOver.toScheme B S hS).map g).ker ≤
      ((BigFppfOver.toScheme B S hS).map t).ker := by
  obtain ⟨R, q, l, e, hq, hlq⟩ := exists_schemeImage_site' B S hS g
  have hqc : AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map q) := by
    rw [hq]; infer_instance
  have hZ : IsClosedSubspace B S hS (Subfunctor.range (yoneda.map q)) :=
    AlgebraicGeometry.Space.isClosedSubspace_range_yoneda_map B S hS q hqc
  have hle : schemeTheoreticImageSubfunctor B S hS (yoneda.map g) ≤
      Subfunctor.range (yoneda.map q) := by
    refine schemeTheoreticImageSubfunctor_le B S hS (yoneda.map g) hZ ?_
    rw [← hlq, yoneda.map_comp]
    exact Subfunctor.range_comp_le _ _
  obtain ⟨r, hr⟩ := hle (op T) ht
  change r ≫ q = t at hr
  have hfac : ((BigFppfOver.toScheme B S hS).map r ≫ e.hom) ≫
      ((BigFppfOver.toScheme B S hS).map g).imageι =
      (BigFppfOver.toScheme B S hS).map t := by
    rw [Category.assoc, ← hq, ← Functor.map_comp, hr]
  calc ((BigFppfOver.toScheme B S hS).map g).ker
      = ((BigFppfOver.toScheme B S hS).map g).imageι.ker :=
        (Scheme.IdealSheafData.ker_subschemeι _).symm
    _ ≤ (((BigFppfOver.toScheme B S hS).map r ≫ e.hom) ≫
          ((BigFppfOver.toScheme B S hS).map g).imageι).ker :=
        Scheme.Hom.le_ker_comp _ _
    _ = ((BigFppfOver.toScheme B S hS).map t).ker := congrArg Scheme.Hom.ker hfac

/-! ### Closed subspaces from closed immersions -/

/-- The range of a closed immersion of presheaves on the big fppf category over `S` whose
source is an algebraic space is a closed subspace of the target. -/
theorem isClosedSubspace_range_of_isClosedImmersion
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : F ⟶ G)
    (hF : IsAlgebraicSpace B S hS F) (hp : IsClosedImmersion B S hS p) :
    IsClosedSubspace B S hS (Subfunctor.range p) := by
  have hmono : Mono p := mono_of_isClosedImmersion B S hS p hp
  refine ⟨isAlgebraicSpace_of_iso B S hS (asIso (Subfunctor.toRange p)) hF, ?_⟩
  have heq : (asIso (Subfunctor.toRange p)).inv ≫ p = (Subfunctor.range p).ι := by
    calc (asIso (Subfunctor.toRange p)).inv ≫ p
        = (asIso (Subfunctor.toRange p)).inv ≫
            (Subfunctor.toRange p ≫ (Subfunctor.range p).ι) := by rw [Subfunctor.toRange_ι]
      _ = (Subfunctor.range p).ι := by simp
  exact heq ▸ MorphismProperty.RespectsIso.precomp
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))
    (asIso (Subfunctor.toRange p)).inv p hp

/-! ### Affine morphisms are quasi-compact -/

/-- **An affine morphism of algebraic spaces over `S` is quasi-compact.** By the affine
criterion it is enough that every base change along an affine scheme-valued point of the
target has quasi-compact source, and affineness says that base change is represented by an
affine object of the site. -/
theorem isQuasiCompact_of_isAffineHom' {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hf : IsAffineHom B S hS f) : IsQuasiCompact B S hS f := by
  refine isQuasiCompact_of_isQuasiCompactSpace_pullback_affine B S hS hF hG f ?_
  intro T hTaff h
  obtain ⟨W, p, q, hpb⟩ := hf ⟨T, hTaff⟩ h
  exact isQuasiCompactSpace_of_iso B S hS
    (hpb.flip.isoIsPullback _ _ (IsPullback.of_hasPullback h f))
    (isQuasiCompactSpace_yoneda_of_isAffine B S hS _ W.property)

/-- A base change of an affine morphism of algebraic spaces over `S` is affine. -/
theorem isAffineHom_of_isPullback' {F F' G G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p : F' ⟶ F} {q : F' ⟶ G'} {f : F ⟶ G} {g : G' ⟶ G}
    (h : IsPullback p q f g) (hf : IsAffineHom B S hS f) : IsAffineHom B S hS q := by
  intro Z z
  obtain ⟨W, b, c, hb⟩ := hf Z (z ≫ g)
  refine ⟨W, h.lift b (yoneda.map c ≫ z) (by simpa only [Category.assoc] using hb.w), c, ?_⟩
  exact IsPullback.of_right (by simpa only [IsPullback.lift_fst] using hb)
    (by simp only [IsPullback.lift_snd]) h

/-! ### Étaleness of a morphism from a representable presheaf -/

/-- A morphism from a representable presheaf which is relatively étale is étale as a morphism
of algebraic spaces in the sense of Stacks 03FR. -/
theorem isEtale_of_presheaf_etale' {V : BigFppfOver B S hS}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : yoneda.obj V ⟶ F)
    (hp : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p) :
    IsEtale B S hS p := by
  have := etale_isStableUnderComposition.{u}
  have : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage (BigFppfOver.toScheme B S hS)
  have : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition _
  intro T ψ hψ
  exact MorphismProperty.comp_mem _ ψ p hψ hp

end Space

/-! ### Kernels on an affine target, stage by stage -/

/-- **A kernel inclusion over an affine base may be checked after composing with a family of
morphisms to affine schemes whose functions generate.** If every regular function on `Y` is
pulled back from one of the `Z i`, and the kernel of `a` dies on `t` after composing with
each `p i`, then the kernel of `a` dies on `t`. -/
theorem ker_le_of_stagewise_ker_le' {J : Type v} {Y A T : Scheme.{u}} [IsAffine Y]
    (Z : J → Scheme.{u}) (hZ : ∀ i, IsAffine (Z i)) (p : ∀ i, Y ⟶ Z i) (a : A ⟶ Y) (t : T ⟶ Y)
    (hgen : ∀ x : Γ(Y, ⊤), ∃ i y, (p i).appTop y = x)
    (hker : ∀ i, (a ≫ p i).ker ≤ (t ≫ p i).ker) : a.ker ≤ t.ker := by
  refine Scheme.IdealSheafData.le_of_isAffine ?_
  simp only [Scheme.ker_of_isAffine, Scheme.IdealSheafData.ofIdealTop_ideal, homOfLE_refl, op_id]
  rw [Y.presheaf.map_id]
  simp only [CommRingCat.hom_id, Ideal.map_id]
  intro x hx
  obtain ⟨i, y, rfl⟩ := hgen x
  have hYi : IsAffine (Z i) := hZ i
  have hi := hker i ⟨⊤, isAffineOpen_top (Z i)⟩
  simp only [Scheme.ker_of_isAffine, Scheme.IdealSheafData.ofIdealTop_ideal,
    homOfLE_refl, op_id] at hi
  rw [(Z i).presheaf.map_id] at hi
  simp only [CommRingCat.hom_id, Ideal.map_id] at hi
  simpa only [RingHom.mem_ker, Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using
    hi (by simpa only [RingHom.mem_ker, Scheme.Hom.comp_appTop,
      CommRingCat.comp_apply] using hx)

namespace Space

section Helpers

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism from a representable presheaf which is étale in the sense of Stacks 03FR is
relatively étale: test the definition against the identity of the source. -/
theorem etale_presheaf_of_isEtale' {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ F) (hp : IsEtale B S hS p) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) p := by
  simpa using hp U (𝟙 (yoneda.obj U)) (presheaf_etale_id B S hS U)

/-- The projections of the chosen limiting cone of a Noetherian limit system are affine
morphisms: they are, up to the comparison isomorphism with the chosen limit of the diagram,
the projections of that limit, and those are affine by Stacks 07SF, part (1). -/
lemma isAffineHom_limitCone_π {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I]
    [Nonempty I] [IsDirectedOrder I] (D : NoetherianLimitSystem B S hS hZ I)
    (hSize : Cardinal.mk I < B.cutoff.ord.cof) (k : Iᵒᵖ) :
    IsAffineHom B S hS (D.limitCone.π.app k) := by
  have hhom : ∀ p q : Iᵒᵖ, Cardinal.mk (p ⟶ q) < B.cutoff.ord.cof := fun _ _ =>
    (Cardinal.le_one_iff_subsingleton.2 inferInstance).trans_lt
      (Cardinal.one_lt_aleph0.trans B.aleph0_lt_cutoff_cof)
  have hSize' : Cardinal.mk (Iᵒᵖ) < B.cutoff.ord.cof := by
    rwa [Cardinal.mk_congr (show Iᵒᵖ ≃ I from ⟨unop, op, fun _ => rfl, fun _ => rfl⟩)]
  have heq : D.limitCone.π.app k = D.limitIso.inv ≫ limit.π D.system k := by
    rw [← D.limitIso_hom_comp_π, Iso.inv_hom_id_assoc]
  rw [heq]
  exact isAffineHom_comp B S hS _ _ (isAffineHom_of_isIso _)
    (isAffineHom_limitπ B S hS D.system hSize' hhom D.transition_affine k)

end Helpers

namespace GoodDiagram

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [Nonempty I]
    [IsDirectedOrder I] {D : NoetherianLimitSystem B S hS hZ I}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ D.limitCone.pt}
    (G : GoodDiagram B S hS hZ D f) {U₀ : BigAffineFppf B S hS}
    (a : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ G.model)

/-! ### The charts of the base-changed models cut out by a chart of the model -/

/-- The system of affine charts of the stages above the index of a good diagram cut out by an
affine scheme-valued point `a` of its model: the stage `i'` is sent to an affine object of the
site representing `B_{i'} ×_{B_i} U₀`. -/
noncomputable abbrev modelChartSystem :
    AffineChartSystem B S hS (op G.index) D.system U₀ (a ≫ G.modelMap) :=
  D.chartSystem G.index (a ≫ G.modelMap)

/-- The chart `B_{i'} ×_{B_i} U₀ ⟶ B_{i'} ×_{B_i} W` of the base change of the model to a
later stage. -/
noncomputable def stageChart (j : Over (op G.index)) :
    ((modelChartSystem G a).siteDiagram ⋙ yoneda).obj j ⟶
      pullback (D.system.map j.hom) G.modelMap :=
  pullback.lift ((modelChartSystem G a).stageMap j)
    ((modelChartSystem G a).baseMap j ≫ a)
    (((modelChartSystem G a).isPullback j).w.trans (Category.assoc _ _ _).symm)

/-- The chart of a stage, followed by the projection to that stage. -/
lemma stageChart_fst (j : Over (op G.index)) :
    stageChart G a j ≫ pullback.fst (D.system.map j.hom) G.modelMap =
      (modelChartSystem G a).stageMap j :=
  pullback.lift_fst _ _ _

/-- The chart of a stage, followed by the projection to the model. -/
lemma stageChart_snd (j : Over (op G.index)) :
    stageChart G a j ≫ pullback.snd (D.system.map j.hom) G.modelMap =
      (modelChartSystem G a).baseMap j ≫ a :=
  pullback.lift_snd _ _ _

/-- The chart of the base change of the model to a later stage is the base change of the
chosen chart of the model. -/
lemma isPullback_stageChart (j : Over (op G.index)) :
    IsPullback (stageChart G a j) ((modelChartSystem G a).baseMap j)
      (pullback.snd (D.system.map j.hom) G.modelMap) a := by
  refine IsPullback.of_right ?_ (stageChart_snd G a j)
    (IsPullback.of_hasPullback (D.system.map j.hom) G.modelMap)
  rw [stageChart_fst]
  exact (modelChartSystem G a).isPullback j

/-- The chart `B ×_{B_i} U₀ ⟶ B ×_{B_i} W` of the base change of the model to the limit
space. -/
noncomputable def limitChart (L : AffineChartSystem.LimitBridge (modelChartSystem G a)) :
    yoneda.obj L.cone.pt ⟶ pullback (D.limitCone.π.app (op G.index)) G.modelMap :=
  pullback.lift (D.chartToLimit G.index (a ≫ G.modelMap) L) (L.toBase ≫ a)
    ((D.isPullback_chartToLimit G.index (a ≫ G.modelMap) L).w.trans
      (Category.assoc _ _ _).symm)

/-- The chart of the limit space, followed by the projection to the limit space. -/
lemma limitChart_fst (L : AffineChartSystem.LimitBridge (modelChartSystem G a)) :
    limitChart G a L ≫ pullback.fst (D.limitCone.π.app (op G.index)) G.modelMap =
      D.chartToLimit G.index (a ≫ G.modelMap) L :=
  pullback.lift_fst _ _ _

/-- The chart of the limit space, followed by the projection to the model. -/
lemma limitChart_snd (L : AffineChartSystem.LimitBridge (modelChartSystem G a)) :
    limitChart G a L ≫ pullback.snd (D.limitCone.π.app (op G.index)) G.modelMap =
      L.toBase ≫ a :=
  pullback.lift_snd _ _ _

/-- The chart of the base change of the model to the limit space is the base change of the
chosen chart of the model. -/
lemma isPullback_limitChart (L : AffineChartSystem.LimitBridge (modelChartSystem G a)) :
    IsPullback (limitChart G a L) L.toBase
      (pullback.snd (D.limitCone.π.app (op G.index)) G.modelMap) a := by
  refine IsPullback.of_right ?_ (limitChart_snd G a L)
    (IsPullback.of_hasPullback (D.limitCone.π.app (op G.index)) G.modelMap)
  rw [limitChart_fst]
  exact D.isPullback_chartToLimit G.index (a ≫ G.modelMap) L

/-- The chart of the limit space projects to the chart of each later stage. -/
lemma limitChart_comp_modelπ (L : AffineChartSystem.LimitBridge (modelChartSystem G a))
    (j : Over (op G.index)) :
    limitChart G a L ≫ modelπ G j =
      yoneda.map (L.cone.π.app j) ≫ stageChart G a j := by
  have hct : D.chartToLimit G.index (a ≫ G.modelMap) L = L.toLimit ≫ D.limitIso.hom := rfl
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, modelπ_fst, ← Category.assoc, limitChart_fst, Category.assoc,
      stageChart_fst, hct, Category.assoc, D.limitIso_hom_comp_π, L.toLimit_comp_limitπ j]
  · rw [Category.assoc, modelπ_snd, limitChart_snd, Category.assoc, stageChart_snd,
      ← Category.assoc, L.baseMap_comp j]

/-- The chart of the limit space is the limit of the charts of the stages: it is the base
change of the chart of any one stage along the projection of the base-changed models. -/
lemma isPullback_limitChart_stage
    (L : AffineChartSystem.LimitBridge (modelChartSystem G a)) (j : Over (op G.index)) :
    IsPullback (limitChart G a L) (yoneda.map (L.cone.π.app j)) (modelπ G j)
      (stageChart G a j) := by
  refine IsPullback.of_bot ?_ (limitChart_comp_modelπ G a L j) (isPullback_stageChart G a j)
  rw [L.baseMap_comp j, modelπ_snd]
  exact isPullback_limitChart G a L

/-- A property of presheaf morphisms induced by a property of schemes passes to the base change
of a morphism having it. -/
private lemma presheaf_of_isPullback {P : MorphismProperty Scheme.{u}}
    {F F' G G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p : F' ⟶ F} {q : F' ⟶ G'} {f : F ⟶ G}
    {g : G' ⟶ G} (h : IsPullback p q f g)
    (hq : (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf f) :
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf q := by
  have : (MorphismProperty.inverseImage P
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  exact MorphismProperty.of_isPullback h hq

/-- A base-change stable property of the chosen chart of the model passes to the chart of the
base change of the model to the limit space. -/
lemma presheaf_limitChart {P : MorphismProperty Scheme.{u}}
    (L : AffineChartSystem.LimitBridge (modelChartSystem G a))
    (ha : (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf a) :
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf
      (limitChart G a L) :=
  presheaf_of_isPullback (isPullback_limitChart G a L).flip ha

/-- A base-change stable property of the chosen chart of the model passes to the chart of the
base change of the model to a later stage. -/
lemma presheaf_stageChart {P : MorphismProperty Scheme.{u}} (j : Over (op G.index))
    (ha : (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf a) :
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf
      (stageChart G a j) :=
  presheaf_of_isPullback (isPullback_stageChart G a j).flip ha

/-- The base change `B ×_{B_i} W` of the model to the limit space is an algebraic space. -/
private lemma isAlgebraicSpace_pullback_limit :
    IsAlgebraicSpace B S hS (pullback (D.limitCone.π.app (op G.index)) G.modelMap) :=
  isAlgebraicSpace_pullback B S hS _ _ D.limit_isAlgebraicSpace G.model_isAlgebraicSpace
    (D.system_isAlgebraicSpace G.index)

/-! ### Regular functions on the affine chart of the limit space -/

/-- **Every regular function on the affine chart `B ×_{B_i} U₀` of the limit space is pulled
back from the chart `B_{i'} ×_{B_i} U₀` of some later stage.** The charts of the stages are
affine and their limit is the chart of the limit space, so taking global sections turns that
limit into a filtered colimit of rings. -/
theorem exists_appTop_eq_of_limitChart
    (L : AffineChartSystem.LimitBridge (modelChartSystem G a))
    (s : Γ((BigFppfOver.toScheme B S hS).obj L.cone.pt, ⊤)) :
    ∃ (j : Over (op G.index)) (y : Γ((modelChartSystem G a).schemeDiagram.obj j, ⊤)),
      ((BigFppfOver.toScheme B S hS).map (L.cone.π.app j)).appTop y = s := by
  have haff : ∀ b : (Over (op G.index))ᵒᵖ,
      IsAffine ((((modelChartSystem G a).siteDiagram ⋙
        BigFppfOver.toScheme B S hS).op.obj b).unop) :=
    fun b => (modelChartSystem G a).isAffine_obj b.unop
  have hcolim := isColimitOfPreserves Scheme.Γ L.schemeIsLimit.op
  obtain ⟨j, y, hy⟩ := exists_eq_ι_app_of_isColimit' hcolim s
  exact ⟨j.unop, y, hy⟩

/-! ### The chart-local identification of the scheme-theoretic images -/

/-- **The chart-local form of Stacks 082Z, part (3), for a good diagram.** On the chart
`B_{i'} ×_{B_i} U₀` of a later stage, the scheme-theoretic image `X_{i'}` cuts out exactly the
scheme-theoretic image of the chart `X ×_{B ×_{B_i} W} (B ×_{B_i} U₀)` of `X`, which is an
object of the site because `X ⟶ B ×_{B_i} W` is a closed immersion. -/
lemma schemeTheoreticImage_chart_eq_preimage_stageImage
    (hX : IsAlgebraicSpace B S hS X)
    (hetale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hqc : ∀ j : Over (op G.index), IsQuasiCompact B S hS (stageMap G j))
    (L : AffineChartSystem.LimitBridge (modelChartSystem G a)) (j : Over (op G.index)) :
    schemeTheoreticImageSubfunctor B S hS
        (yoneda.map (G.isClosedImmersion.rep.snd (limitChart G a L) ≫
          L.cone.π.app j)) =
      (stageImage G j).preimage (stageChart G a j) := by
  have hpb : IsPullback (G.isClosedImmersion.rep.fst (limitChart G a L))
      (yoneda.map (G.isClosedImmersion.rep.snd (limitChart G a L) ≫ L.cone.π.app j))
      (stageMap G j) (stageChart G a j) := by
    have h := (G.isClosedImmersion.rep.isPullback (limitChart G a L)).paste_vert
      (isPullback_limitChart_stage G a L j)
    rw [← Functor.map_comp, induced_comp_modelπ] at h
    exact h
  have hrange : Subfunctor.range
      (yoneda.map (G.isClosedImmersion.rep.snd (limitChart G a L) ≫ L.cone.π.app j)) =
      Subfunctor.range (pullback.snd (stageMap G j) (stageChart G a j)) := by
    rw [← hpb.isoPullback_hom_snd, Subfunctor.range_comp, Subfunctor.range_eq_top,
      Subfunctor.image_top]
  rw [schemeTheoreticImageSubfunctor_congr_range' B S hS _ _
      (isAlgebraicSpace_yoneda B S hS _) hrange,
    schemeTheoreticImageSubfunctor_pullback_snd_of_isEtale_of_isQuasiCompact' B S hS
      (stageMap G j) (stageChart G a j) hX (isAlgebraicSpace_stageTarget G j)
      (isAlgebraicSpace_yoneda B S hS _) (hqc j)
      (isEtale_of_presheaf_etale' B S hS _ (presheaf_stageChart G a j hetale))]

/-! ### The remaining inclusion of Stacks 0CP9, on one chart -/

/-- **The inclusion `imageInter G ≤ Subfunctor.range G.induced` of Stacks 0CP9, proved from a
single affine étale surjective chart of the model.**

A point of `B ×_{B_i} W` lying in every `X_{i'}` is tested after the surjective étale base
change by the chart `B ×_{B_i} U₀`, where membership in the closed subspace `X` is the
inclusion of the ideal sheaf of `X ×_{B ×_{B_i} W} (B ×_{B_i} U₀)` into the kernel of the
point. The chart is affine and is the limit of the affine charts `B_{i'} ×_{B_i} U₀`, so every
regular function on it is pulled back from one of those; there the ideal of `X` is, by Stacks
082Z, the ideal of functions vanishing on the chart of `X`, which the point kills because it
lies in `X_{i'}`. -/
theorem imageInter_le_range_induced_of_chart
    (hX : IsAlgebraicSpace B S hS X)
    (hsurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hetale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hqc : ∀ j : Over (op G.index), IsQuasiCompact B S hS (stageMap G j))
    (L : AffineChartSystem.LimitBridge (modelChartSystem G a)) :
    imageInter G ≤ Subfunctor.range G.induced := by
  classical
  have hMalg := isAlgebraicSpace_pullback_limit G
  have hmono : Mono G.induced := mono_of_isClosedImmersion B S hS _ G.isClosedImmersion
  have hRalg : IsAlgebraicSpace B S hS (Subfunctor.range G.induced).toFunctor :=
    isAlgebraicSpace_of_iso B S hS (asIso (Subfunctor.toRange G.induced)) hX
  have hclE : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (limitChart G a L) :=
    presheaf_limitChart G a L hetale
  have hclS : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (limitChart G a L) :=
    presheaf_limitChart G a L hsurj
  have hCLaff : IsAffine ((BigFppfOver.toScheme B S hS).obj L.cone.pt) := L.isAffine_pt
  have hciA : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map
      (G.isClosedImmersion.rep.snd (limitChart G a L))) :=
    G.isClosedImmersion.property (limitChart G a L) _ _
      (G.isClosedImmersion.rep.isPullback (limitChart G a L))
  intro T x hx
  have hxj : ∀ j : Over (op G.index),
      (modelπ G j).app T x ∈ (stageImage G j).obj T := fun j => imageInter_le G j T hx
  set t : yoneda.obj T.unop ⟶ pullback (D.limitCone.π.app (op G.index)) G.modelMap :=
    yonedaEquiv.symm x with ht
  have hw : yoneda.map (hclE.rep.fst' t) ≫ limitChart G a L =
      yoneda.map (hclE.rep.snd t) ≫ t := by
    rw [hclE.rep.map_fst' t]
    exact (hclE.rep.isPullback t).w
  have hval : (pullback (D.limitCone.π.app (op G.index)) G.modelMap).map
      (hclE.rep.snd t).op x =
      (limitChart G a L).app (op (hclE.rep.pullback t)) (hclE.rep.fst' t) := by
    rw [← yonedaEquiv_yoneda_map_comp B S hS (limitChart G a L) (hclE.rep.fst' t), hw,
      ← yonedaEquiv_naturality, ht, Equiv.apply_symm_apply]
  refine mem_obj_of_surjective_etale B S hS hMalg.isSheaf (Subfunctor.range G.induced)
    hRalg.isSheaf (hclE.rep.snd t) (hclS.property_snd t) (hclE.property_snd t) x ?_
  rw [hval]
  have hker : ((BigFppfOver.toScheme B S hS).map
      (G.isClosedImmersion.rep.snd (limitChart G a L))).ker ≤
      ((BigFppfOver.toScheme B S hS).map (hclE.rep.fst' t)).ker := by
    refine ker_le_of_stagewise_ker_le'
      (fun j => (modelChartSystem G a).schemeDiagram.obj j)
      (fun j => (modelChartSystem G a).isAffine_obj j)
      (fun j => (BigFppfOver.toScheme B S hS).map (L.cone.π.app j)) _ _
      (fun s => exists_appTop_eq_of_limitChart G a L s) ?_
    intro j
    rw [← Functor.map_comp, ← Functor.map_comp]
    refine ker_le_of_mem_schemeTheoreticImageSubfunctor B S hS _ _ ?_
    rw [schemeTheoreticImage_chart_eq_preimage_stageImage G a hX hetale hqc L j]
    have h1 : (pullback (D.system.map j.hom) G.modelMap).map (hclE.rep.snd t).op
        ((modelπ G j).app T x) ∈ (stageImage G j).obj (op (hclE.rep.pullback t)) :=
      (stageImage G j).map (hclE.rep.snd t).op (hxj j)
    rw [← (modelπ G j).naturality_apply, hval] at h1
    have h2 : (stageChart G a j).app (op (hclE.rep.pullback t))
        (hclE.rep.fst' t ≫ L.cone.π.app j) =
        (modelπ G j).app (op (hclE.rep.pullback t))
          ((limitChart G a L).app (op (hclE.rep.pullback t)) (hclE.rep.fst' t)) :=
      (congrArg
        (fun k : yoneda.obj L.cone.pt ⟶ pullback (D.system.map j.hom) G.modelMap =>
          k.app (op (hclE.rep.pullback t)) (hclE.rep.fst' t))
        (limitChart_comp_modelπ G a L j)).symm
    have hgoal : (stageChart G a j).app (op (hclE.rep.pullback t))
        (hclE.rep.fst' t ≫ L.cone.π.app j) ∈
        (stageImage G j).obj (op (hclE.rep.pullback t)) := by
      rw [h2]; exact h1
    exact hgoal
  obtain ⟨ψ, hψ⟩ := exists_comp_eq_of_ker_le B S hS
    (G.isClosedImmersion.rep.snd (limitChart G a L)) (hclE.rep.fst' t) hciA hker
  refine ⟨yonedaEquiv (yoneda.map ψ ≫
    G.isClosedImmersion.rep.fst (limitChart G a L)), ?_⟩
  have hfac : (yoneda.map ψ ≫ G.isClosedImmersion.rep.fst (limitChart G a L)) ≫
      G.induced = yoneda.map (hclE.rep.fst' t) ≫ limitChart G a L := by
    rw [Category.assoc, (G.isClosedImmersion.rep.isPullback (limitChart G a L)).w,
      ← Category.assoc, ← Functor.map_comp, hψ]
  calc G.induced.app (op (hclE.rep.pullback t))
        (yonedaEquiv (yoneda.map ψ ≫ G.isClosedImmersion.rep.fst (limitChart G a L)))
      = yonedaEquiv ((yoneda.map ψ ≫ G.isClosedImmersion.rep.fst (limitChart G a L)) ≫
          G.induced) := (yonedaEquiv_comp _ _).symm
    _ = yonedaEquiv (yoneda.map (hclE.rep.fst' t) ≫ limitChart G a L) := congrArg _ hfac
    _ = (limitChart G a L).app (op (hclE.rep.pullback t)) (hclE.rep.fst' t) :=
        yonedaEquiv_yoneda_map_comp B S hS _ _

/-! ### Quasi-compactness of the stage maps -/

/-- The projection `B ×_{B_i} W ⟶ B_{i'} ×_{B_i} W` is the base change of the projection
`B ⟶ B_{i'}` along the projection of the base-changed model to its stage. -/
lemma isPullback_modelπ (j : Over (op G.index)) :
    IsPullback (pullback.fst (D.limitCone.π.app (op G.index)) G.modelMap) (modelπ G j)
      (D.limitCone.π.app j.left) (pullback.fst (D.system.map j.hom) G.modelMap) := by
  refine IsPullback.of_bot ?_ (modelπ_fst G j).symm
    (IsPullback.of_hasPullback (D.system.map j.hom) G.modelMap)
  rw [modelπ_snd, D.limitCone.w j.hom]
  exact IsPullback.of_hasPullback _ _

/-- **The stage maps of a good diagram are quasi-compact.** The morphism `X ⟶ B ×_{B_i} W` is
a closed immersion, and `B ×_{B_i} W ⟶ B_{i'} ×_{B_i} W` is a base change of the affine
projection `B ⟶ B_{i'}`. -/
lemma isQuasiCompact_stageMap (hSize : Cardinal.mk I < B.cutoff.ord.cof)
    (j : Over (op G.index)) : IsQuasiCompact B S hS (stageMap G j) := by
  have hMalg := isAlgebraicSpace_pullback_limit G
  have hmaff : IsAffineHom B S hS (modelπ G j) :=
    isAffineHom_of_isPullback' B S hS (isPullback_modelπ G j)
      (isAffineHom_limitCone_π B S hS D hSize j.left)
  have hmqc : IsQuasiCompact B S hS (modelπ G j) :=
    isQuasiCompact_of_isAffineHom' B S hS _ hMalg (isAlgebraicSpace_stageTarget G j) hmaff
  rw [← induced_comp_modelπ G j]
  exact isQuasiCompact_comp B S hS hMalg (isAlgebraicSpace_stageTarget G j) _ _
    (isQuasiCompact_of_isClosedImmersion' B S hS G.isClosedImmersion) hmqc

/-! ### Stacks 0CP9 -/

/-- **The inclusion that remained of Stacks 0CP9.** Every point of `B ×_{B_i} W` which lies in
the scheme-theoretic image `X_{i'}` at every stage `i' ≥ i` already lies in `X`.

The model `W` is quasi-compact over the Noetherian stage `B_i`, hence quasi-compact, so it has
a single affine étale surjective chart `U₀ ⟶ W`; the statement is then
`AlgebraicGeometry.Space.GoodDiagram.imageInter_le_range_induced_of_chart` for that chart,
whose system of charts of the stages has a limit because the index type is small for the
site. -/
theorem imageInter_le_range_induced (hX : IsAlgebraicSpace B S hS X)
    (hSize : Cardinal.mk I < B.cutoff.ord.cof) :
    imageInter G ≤ Subfunctor.range G.induced := by
  obtain ⟨A, a, hAaff, hasurj, haetale⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS G.model
      G.model_isAlgebraicSpace).mp
      (isQuasiCompactSpace_source_of_isQuasiCompact B S hS
        (D.system_isAlgebraicSpace G.index) (D.noetherian G.index).1 G.isFiniteType.2)
  have hbridge := D.chartLimitBridge (U₀ := ⟨A, hAaff⟩) G.index (a ≫ G.modelMap) hSize
  have hae := etale_presheaf_of_isEtale' B S hS A a haetale
  have hqc : ∀ j : Over (op G.index), IsQuasiCompact B S hS (stageMap G j) := fun j =>
    isQuasiCompact_stageMap G hSize j
  exact imageInter_le_range_induced_of_chart G (U₀ := ⟨A, hAaff⟩) a hX hasurj hae hqc
    hbridge

/-- **Stacks 0CP9.** In Situation 0CP6, for a diagram as in Stacks 0CP8, the canonical cone
from `X` to the inverse system of the scheme-theoretic images `X_{i'}` of
`X ⟶ B_{i'} ×_{B_i} W` is a limit cone: `X = lim_{i' ≥ i} X_{i'}`.

By `AlgebraicGeometry.Space.GoodDiagram.nonempty_isLimit_imageCone_iff` this is the single
inclusion `AlgebraicGeometry.Space.GoodDiagram.imageInter_le_range_induced` of subfunctors of
`B ×_{B_i} W`. The hypothesis that the index type of the system be small for the site is what
produces the limit of the system of affine charts used there; it is not a hypothesis of the
source. -/
@[stacks 0CP9 "X = lim X_{i'}, for an index type small for the site"]
noncomputable def isLimit_imageCone (hX : IsAlgebraicSpace B S hS X)
    (hSize : Cardinal.mk I < B.cutoff.ord.cof) : IsLimit (imageCone G) :=
  isLimit_imageCone_of_imageInter_le G (imageInter_le_range_induced G hX hSize)

end GoodDiagram

end Space

end AlgebraicGeometry

end
