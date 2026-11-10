module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.GenericFibreFreeBlowup0811
public import StacksFrontier.AlgebraicGeometry.LimitFPObjectDescent.Approximation
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.FiniteLocallyFreeRank
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Limits.NoetherianApproximation.Absolute
public import StacksFrontier.AlgebraicGeometry.ObjectDescent.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.BaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.Flattening

/-!
# Flattening a morphism by a pair of almost blowup squares over a general base

Let `f : X ⟶ Y` be a morphism of finite presentation to a quasi-compact and quasi-separated
scheme and let `V ⊆ Y` be a quasi-compact open over which `f` is flat. Then the diagram of two
almost blowup squares of [Stacks, Tag 0EVC] exists, with the centre on `Y` disjoint from `V` and
the relative morphism flat and of finite presentation. This is the tag in its own generality; the
locally Noetherian case is `AlgebraicGeometry.hasFlatAlmostBlowUpSquarePair` and the content of
this file is the reduction of the general case to it by absolute Noetherian approximation.

The reduction is the one the source prescribes. Write `Y` as the limit of a directed inverse
system of schemes of finite type over `ℤ` with affine transition morphisms, so that each stage is
Noetherian. The morphism `f` is the base change of a morphism of finite presentation over some
stage, and `V` is the inverse image of a quasi-compact open of some stage; passing to a stage
below both puts the two over one stage. Flatness over the open is a condition on the base change
of a morphism over that stage, so it already holds over a further stage. The Noetherian case
applied there produces the diagram, and the whole diagram base changes back to `Y`: the
conclusion is stable under base change, which is the last sentence of the source's proof.

## Main results

* `AlgebraicGeometry.HasFlatAlmostBlowUpSquarePair.of_isPullback`: the conclusion of
  [Stacks, Tag 0EVC] is stable under base change, the new centre being the inverse image of the
  old one and the new open the inverse image of the old one.
* `AlgebraicGeometry.hasFlatAlmostBlowUpSquarePair_of_flat`: **[Stacks, Tag 0EVC]**.

## Implementation notes

Flatness over an open `U` of the target appears in three guises here: as flatness of
`pullback.snd p U.ι`, which is how the hypothesis of the tag is stated; as flatness of the
restriction `p ∣_ U`, which is what the flattening centre of [Stacks, Tag 0815] is fed; and as
flatness of the base change of a morphism of schemes over a stage, which is the shape
[Stacks, Tag 04AI] descends. The private lemma
`AlgebraicGeometry.flat_overPullback_map_restrictOver_iff` identifies the third with a base
change of `p` along the inclusion of the inverse image of `U`, and is used both to feed
[Stacks, Tag 04AI] at the limit and to read its conclusion at the stage it produces.

The hypothesis `AlgebraicGeometry.AffineChartFlatteningCentre` carried by the library's Noetherian
case is discharged at each stage by
`AlgebraicGeometry.finitePresentationHasAffineChartFlatteningCentre`, so the statement proved
here assumes nothing beyond the hypotheses of the tag.

## References

* [Stacks Project, Tag 0EVC](https://stacks.math.columbia.edu/tag/0EVC)
* [Stacks Project, Tag 0EV7](https://stacks.math.columbia.edu/tag/0EV7)
* [Stacks Project, Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 01Z4](https://stacks.math.columbia.edu/tag/01Z4)
* [Stacks Project, Tag 04AI](https://stacks.math.columbia.edu/tag/04AI)
* [Stacks Project, Tag 0815](https://stacks.math.columbia.edu/tag/0815)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Base change of the conclusion -/

/-- **Base change of the diagram of [Stacks, Tag 0EVC].** If `f' : X' ⟶ Y'` is a base change of
`f : X ⟶ Y` along `q : Y' ⟶ Y` and `f` admits the diagram of the tag relative to an open
`V ⊆ Y`, then `f'` admits it relative to `q ⁻¹ᵁ V`.

Every piece base changes: the new centre is `Z·𝒪_{Y'}`, whose support is the inverse image of the
support of `Z` and hence misses `q ⁻¹ᵁ V`; the two modifications base change to modifications of
almost blowup squares by [Stacks, Tag 0EV7], the right-hand one because `(Z·𝒪_{Y'})·𝒪_{X'}` and
`(Z·𝒪_X)·𝒪_{X'}` are both the inverse image of `Z` along the common composite `X' ⟶ Y`; and the
relative morphism base changes to the relative morphism of the new diagram, so it stays flat and
of finite presentation. This is the last sentence of the proof of the tag. -/
public theorem HasFlatAlmostBlowUpSquarePair.of_isPullback {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {q : Y' ⟶ Y} {f' : X' ⟶ Y'} {p : X' ⟶ X} (hcart : IsPullback p f' f q)
    (V : Y.Opens) (h : HasFlatAlmostBlowUpSquarePair f V) :
    HasFlatAlmostBlowUpSquarePair f' (q ⁻¹ᵁ V) := by
  obtain ⟨Z, Y₁, b, X₁, k, g, hleft, hright, hdisj, hcomm, hflat, hfp⟩ := h
  have hcentre : (Z.comap q).comap f' = (Z.comap f).comap p := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hcart.w]
  have hlift : (pullback.fst p k ≫ f') ≫ q = (pullback.snd p k ≫ g) ≫ b := by
    calc (pullback.fst p k ≫ f') ≫ q = (pullback.fst p k ≫ p) ≫ f := by
          rw [Category.assoc, ← hcart.w, Category.assoc]
      _ = (pullback.snd p k ≫ k) ≫ f := by rw [pullback.condition]
      _ = (pullback.snd p k ≫ g) ≫ b := by rw [Category.assoc, ← hcomm, Category.assoc]
  have hsq : IsPullback (pullback.snd p k) (pullback.lift _ _ hlift) g (pullback.snd q b) := by
    refine IsPullback.of_bot ?_ (pullback.lift_snd _ _ _).symm
      (IsPullback.of_hasPullback q b).flip
    rw [show pullback.lift _ _ hlift ≫ pullback.fst q b = pullback.fst p k ≫ f' from
      pullback.lift_fst _ _ _, hcomm]
    exact (IsPullback.of_hasPullback p k).flip.paste_vert hcart
  refine ⟨Z.comap q, pullback q b, pullback.fst q b, pullback p k, pullback.fst p k,
    pullback.lift _ _ hlift, isAlmostBlowUpSquare_baseChange Z b q hleft, ?_, ?_,
    pullback.lift_fst _ _ _, MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq hflat,
    FinitePresentation.of_isPullback hsq hfp⟩
  · rw [hcentre]
    exact isAlmostBlowUpSquare_baseChange (Z.comap f) k p hright
  · have hsupp : ((Z.comap q).support : Set Y') = q.base ⁻¹' (Z.support : Set Y) := by
      rw [Scheme.IdealSheafData.support_comap]
      rfl
    rw [hsupp, show ((q ⁻¹ᵁ V : Y'.Opens) : Set Y') = q.base ⁻¹' (V : Set Y) from rfl]
    exact hdisj.preimage q.base

/-! ### Flatness over an open -/

/-- The restriction of `p : Z ⟶ S` over an open `U` of `S`, read as a morphism of schemes over
`S` from the open subscheme `p ⁻¹ᵁ U` to the open subscheme `U`. This is the shape in which
[Stacks, Tag 04AI] descends flatness of `p` over `U`. -/
private def restrictOver {Z S : Scheme.{u}} (p : Z ⟶ S) (U : S.Opens) :
    (Over.mk (p ∣_ U ≫ U.ι) : Over S) ⟶ Over.mk U.ι :=
  Over.homMk (p ∣_ U) rfl

/-- Flatness of a morphism does not depend on the choice of pullback square it sits in. -/
private lemma flat_iff_of_isPullback {Z S T A B : Scheme.{u}} {p : Z ⟶ S} {b : T ⟶ S}
    {a₁ : A ⟶ Z} {f₁ : A ⟶ T} {a₂ : B ⟶ Z} {f₂ : B ⟶ T}
    (sq₁ : IsPullback a₁ f₁ p b) (sq₂ : IsPullback a₂ f₂ p b) : Flat f₁ ↔ Flat f₂ :=
  have : MorphismProperty.RespectsIso (@Flat : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  prop_iff_of_isPullback (@Flat) sq₁ sq₂

/-- Base changing along `k ≫ b` is flat exactly when base changing the base change along `b`
by `k` is. -/
private lemma flat_pullback_snd_comp_iff {Z S T T' : Scheme.{u}} (p : Z ⟶ S) (b : T ⟶ S)
    (k : T' ⟶ T) : Flat (pullback.snd p (k ≫ b)) ↔ Flat (pullback.snd (pullback.snd p b) k) :=
  flat_iff_of_isPullback (IsPullback.of_hasPullback p (k ≫ b)) (isPullback_pullback_snd_comp p b k)

/-- Base changing the target of a base change: if `Z ×_S T ⟶ T` is flat, so is `Z ×_S T' ⟶ T'`
for any `T' ⟶ T` over `S`. -/
private lemma flat_pullback_snd_comp {Z S T T' : Scheme.{u}} (p : Z ⟶ S) (b : T ⟶ S)
    (k : T' ⟶ T) (h : Flat (pullback.snd p b)) : Flat (pullback.snd p (k ≫ b)) :=
  (flat_pullback_snd_comp_iff p b k).mpr <| MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback (pullback.snd p b) k) h

/-- **Flatness over an open, in the shape [Stacks, Tag 04AI] descends.** For `p : Z ⟶ S`, an open
`U ⊆ S` and a morphism `b : T ⟶ S`, the base change along `b` of the restriction of `p` over `U`
is flat exactly when the base change of `p` along the inclusion of `b ⁻¹ᵁ U` into `S` is flat.

The comparison is in two steps: the base change of `p ∣_ U` along `b` is a base change of `p`
itself, along the composite `Z ×_S U ⟶ U ⟶ S`; and that composite is the inclusion of
`b ⁻¹ᵁ U` precomposed with the comparison isomorphism `T ×_S U ≅ b ⁻¹ᵁ U`. -/
private lemma flat_overPullback_map_restrictOver_iff {Z S T : Scheme.{u}} (p : Z ⟶ S)
    (U : S.Opens) (b : T ⟶ S) :
    Flat ((Over.pullback b).map (restrictOver p U)).left ↔
      Flat (pullback.snd p ((b ⁻¹ᵁ U).ι ≫ b)) := by
  have hstep : Flat ((Over.pullback b).map (restrictOver p U)).left ↔
      Flat (pullback.snd p (pullback.snd U.ι b ≫ b)) := by
    refine (flat_iff_of_isPullback
      (overPullback_isPullback b _ _ (restrictOver p U))
      (IsPullback.of_hasPullback (p ∣_ U) (pullback.fst U.ι b))).trans ?_
    exact flat_iff_of_isPullback
      (isPullback_pullback_snd_morphismRestrict p U (pullback.fst U.ι b)
        (pullback.snd U.ι b ≫ b) pullback.condition)
      (IsPullback.of_hasPullback p (pullback.snd U.ι b ≫ b))
  have hι : (pullbackSymmetry U.ι b ≪≫ pullbackRestrictIsoRestrict b U).hom ≫ (b ⁻¹ᵁ U).ι =
      pullback.snd U.ι b := by
    simp
  rw [hstep]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [show (b ⁻¹ᵁ U).ι ≫ b = (pullbackSymmetry U.ι b ≪≫ pullbackRestrictIsoRestrict b U).inv ≫
        (pullback.snd U.ι b ≫ b) by rw [← hι, Category.assoc, Iso.inv_hom_id_assoc]]
    exact flat_pullback_snd_comp p _ _ h
  · rw [← hι, Category.assoc]
    exact flat_pullback_snd_comp p _ _ h

/-! ### The Noetherian case with the carried hypothesis discharged -/

/-- **[Stacks, Tag 0EVC] over a locally Noetherian base, with nothing carried.** The
Noetherian case `AlgebraicGeometry.hasFlatAlmostBlowUpSquarePair` asks for the affine case of the
flatness half of [Stacks, Tag 0815] as the hypothesis
`AlgebraicGeometry.AffineChartFlatteningCentre`;
`AlgebraicGeometry.finitePresentationHasAffineChartFlatteningCentre` supplies it from flatness of
the restriction of `p` over `U`. -/
private lemma hasFlatAlmostBlowUpSquarePair_of_flat_morphismRestrict {Z S : Scheme.{u}}
    [IsLocallyNoetherian S] [CompactSpace S] [QuasiSeparatedSpace S] (p : Z ⟶ S)
    (hp : FinitePresentation p) (U : S.Opens) (hU : IsCompact (U : Set S))
    (hflat : Flat (p ∣_ U)) : HasFlatAlmostBlowUpSquarePair p U := by
  have : LocallyOfFinitePresentation p := hp.locallyOfFinitePresentation
  have : QuasiCompact p := hp.quasiCompact
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace p
  refine hasFlatAlmostBlowUpSquarePair p hp U hU
    (finitePresentationHasAffineChartFlatteningCentre p U hU ?_)
  rwa [Scheme.Hom.resLE_eq_morphismRestrict]

/-- If `f` is a base change of `p` along `q` and `q` factors as `r ≫ m`, then `f` is a base change
of `pullback.snd p m` along `r`. -/
private theorem isPullback_pullbackLift_of_fac {C : Type*} [Category C]
    {A B P Q R : C} {a : A ⟶ P} {f : A ⟶ B} {p : P ⟶ Q} {q : B ⟶ Q} {r : B ⟶ R} {m : R ⟶ Q}
    [HasPullback p m] (h : IsPullback a f p q) (hw : r ≫ m = q) :
    IsPullback (pullback.lift a (f ≫ r) (by rw [h.w, ← hw, Category.assoc])) f
      (pullback.snd p m) r := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback p m)
  rw [pullback.lift_fst, hw]
  exact h

/-- **[Stacks, Tag 0EVC] from flatness at a Noetherian stage.** Let `f : X ⟶ Y` be the base change
of a morphism `p : P ⟶ S` of finite presentation along `q : Y ⟶ S`, and let `W ⊆ S` be a
quasi-compact open. If `q` factors through a quasi-compact `g : T ⟶ S` with `T` quasi-compact,
quasi-separated and locally Noetherian, and the base change of `p` along the composite of the
inclusion of `g ⁻¹ᵁ W` with `g` is flat, then `f` admits the diagram of the tag relative to
`q ⁻¹ᵁ W`. -/
private theorem hasFlatAlmostBlowUpSquarePair_of_isPullback_of_flat_stage
    {X Y P S T : Scheme.{u}} [IsLocallyNoetherian T] [CompactSpace T] [QuasiSeparatedSpace T]
    {f : X ⟶ Y} {a : X ⟶ P} {p : P ⟶ S} {q : Y ⟶ S} (hA : IsPullback a f p q)
    (hp : FinitePresentation p) (W : S.Opens) (hW : IsCompact (W : Set S)) (g : T ⟶ S)
    [QuasiCompact g] (r : Y ⟶ T) (hr : r ≫ g = q)
    (hflat : Flat (pullback.snd p ((g ⁻¹ᵁ W).ι ≫ g))) :
    HasFlatAlmostBlowUpSquarePair f (q ⁻¹ᵁ W) := by
  have hflatStage : Flat (pullback.snd p g ∣_ (g ⁻¹ᵁ W)) := by
    refine (flat_iff_of_isPullback
      (isPullback_morphismRestrict (pullback.snd p g) (g ⁻¹ᵁ W)).flip
      (IsPullback.of_hasPullback (pullback.snd p g) (g ⁻¹ᵁ W).ι)).mpr ?_
    exact (flat_pullback_snd_comp_iff p g _).mp hflat
  rw [← hr, Scheme.Hom.comp_preimage]
  exact HasFlatAlmostBlowUpSquarePair.of_isPullback (isPullback_pullbackLift_of_fac hA hr) _
    (hasFlatAlmostBlowUpSquarePair_of_flat_morphismRestrict _
      (FinitePresentation.of_isPullback (IsPullback.of_hasPullback p g) hp) _
      (g.isCompact_preimage hW) hflatStage)

/-! ### The limit argument -/

/-- **[Stacks, Tag 0EVC] for a base change from a stage of a Noetherian limit.** Let `Y` be the
limit of a cofiltered system of Noetherian schemes with affine transition morphisms, let `f` be the
base change of a morphism `p` of finite presentation over a stage, and let `W` be a quasi-compact
open of that stage over whose inverse image `f` is flat. Then `f` admits the diagram of the tag
relative to the inverse image of `W`. -/
private theorem hasFlatAlmostBlowUpSquarePair_of_isLimit_of_isPullback
    {I : Type*} [Category* I] [EssentiallySmall.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] [∀ i, IsLocallyNoetherian (D.obj i)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    {X P : Scheme.{u}} {j : I} {f : X ⟶ c.pt} {a : X ⟶ P} {p : P ⟶ D.obj j}
    (hA : IsPullback a f p (c.π.app j)) (hp : FinitePresentation p) (W : (D.obj j).Opens)
    (hW : IsCompact (W : Set (D.obj j))) (hflat : Flat (pullback.snd f (c.π.app j ⁻¹ᵁ W).ι)) :
    HasFlatAlmostBlowUpSquarePair f (c.π.app j ⁻¹ᵁ W) := by
  have : LocallyOfFinitePresentation p := hp.1
  have : QuasiCompact p := hp.2.1
  have : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace p
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace (Over.mk W.ι : Over (D.obj j)).left :=
    (isCompact_iff_compactSpace.mp hW : CompactSpace W.toScheme)
  have : QuasiSeparatedSpace (Over.mk W.ι : Over (D.obj j)).left :=
    inferInstanceAs (QuasiSeparatedSpace W.toScheme)
  have : CompactSpace (Over.mk (p ∣_ W ≫ W.ι) : Over (D.obj j)).left :=
    (isCompact_iff_compactSpace.mp (Scheme.Hom.isCompact_preimage p hW) :
      CompactSpace (p ⁻¹ᵁ W).toScheme)
  have : QuasiSeparatedSpace (Over.mk (p ∣_ W ≫ W.ι) : Over (D.obj j)).left :=
    inferInstanceAs (QuasiSeparatedSpace (p ⁻¹ᵁ W).toScheme)
  have : LocallyOfFinitePresentation (restrictOver p W).left :=
    inferInstanceAs (LocallyOfFinitePresentation (p ∣_ W))
  -- Flatness over the open at the limit, in the shape tag 04AI descends.
  have : Flat ((Over.pullback (c.π.app j)).map (restrictOver p W)).left := by
    rw [flat_overPullback_map_restrictOver_iff]
    exact (flat_iff_of_isPullback
      ((IsPullback.of_hasPullback f (c.π.app j ⁻¹ᵁ W).ι).paste_horiz hA)
      (IsPullback.of_hasPullback p ((c.π.app j ⁻¹ᵁ W).ι ≫ c.π.app j))).mp hflat
  -- Tag 04AI: flatness already holds over some further stage.
  obtain ⟨i, g, hg⟩ := exists_flat_baseChange_of_limitBaseChange D c j
    (Over.mk (p ∣_ W ≫ W.ι)) (Over.mk W.ι) (restrictOver p W) hc
  -- The Noetherian case over that stage, base changed back to `Y`.
  exact hasFlatAlmostBlowUpSquarePair_of_isPullback_of_flat_stage hA hp W hW (D.map g)
    (c.π.app i) (c.w g) ((flat_overPullback_map_restrictOver_iff p W (D.map g)).mp hg)

/-- **[Stacks, Tag 0EVC].** Let `Y` be a quasi-compact and quasi-separated scheme, let `X` be a
scheme of finite presentation over `Y`, and let `V ⊆ Y` be a quasi-compact open such that
`X_V ⟶ V` is flat. Then there is a diagram as in the tag: two almost blowup squares, over `Y`
with a centre disjoint from `V` and over `X` with the inverse-image centre, whose lower and top
squares are cartesian (`AlgebraicGeometry.lowerSquareIso`,
`AlgebraicGeometry.topSquareIso`) and whose relative morphism `X' ⟶ Y'` is flat and of finite
presentation.

The general case is reduced to the locally Noetherian case
`AlgebraicGeometry.hasFlatAlmostBlowUpSquarePair` by absolute Noetherian approximation; see the
module docstring. -/
@[stacks 0EVC]
public theorem hasFlatAlmostBlowUpSquarePair_of_flat {X Y : Scheme.{u}}
    [CompactSpace Y] [QuasiSeparatedSpace Y] (f : X ⟶ Y) (hf : FinitePresentation f)
    (V : Y.Opens) (hV : IsCompact (V : Set Y)) (hflat : Flat (pullback.snd f V.ι)) :
    HasFlatAlmostBlowUpSquarePair f V := by
  -- Write `Y` as the limit of a directed system of schemes of finite type over `ℤ`.
  let Q := LimitFPObjectDescent.finiteTypeSchemeApproximation Y
  let : Preorder Q.indexType := Q.indexPreorder
  let : Nonempty Q.indexType := Q.indexNonempty
  let : IsDirected Q.indexType (· ≤ ·) := Q.indexDirected
  let D := Q.stages
  let c : Cone D := Cone.mk Y Q.projection
  have hc : IsLimit c := Q.limit
  let : ∀ {i j : Q.indexTypeᵒᵖ} (e : i ⟶ j), IsAffineHom (D.map e) := Q.transition_affine
  let : ∀ i : Q.indexTypeᵒᵖ, LocallyOfFiniteType (terminal.from (D.obj i)) :=
    Q.stage_locallyOfFiniteType
  let : ∀ i : Q.indexTypeᵒᵖ, QuasiCompact (terminal.from (D.obj i)) := Q.stage_quasiCompact
  have hnoeth : ∀ i : Q.indexTypeᵒᵖ, IsNoetherian (D.obj i) := fun i ↦
    isNoetherian_of_locallyOfFiniteType_terminal_from (D.obj i)
  let : ∀ i : Q.indexTypeᵒᵖ, CompactSpace (D.obj i) := fun i ↦ (hnoeth i).toCompactSpace
  let : ∀ i : Q.indexTypeᵒᵖ, IsLocallyNoetherian (D.obj i) := fun i ↦
    (hnoeth i).toIsLocallyNoetherian
  let : ∀ i : Q.indexTypeᵒᵖ, QuasiSeparatedSpace (D.obj i) := fun i ↦ inferInstance
  -- Descend `f` and `V` to stages, then pass to a stage below both.
  obtain ⟨i₀, X₀, hfp₀, ⟨e₀⟩⟩ :=
    LimitFPObjectDescent.exists_model_of_finitePresentation D c hc (Over.mk f) hf
  obtain ⟨i₁, W₁, hW₁, hW₁V⟩ := exists_preimage_eq D c hc V hV
  obtain ⟨j, u, ⟨v⟩⟩ : ∃ (j : Q.indexTypeᵒᵖ) (_ : j ⟶ i₀), Nonempty (j ⟶ i₁) :=
    ⟨IsCofiltered.min i₀ i₁, IsCofiltered.minToLeft i₀ i₁, ⟨IsCofiltered.minToRight i₀ i₁⟩⟩
  -- The quasi-compact open at that stage.
  let W : (D.obj j).Opens := D.map v ⁻¹ᵁ W₁
  have hWcpt : IsCompact (W : Set (D.obj j)) := Scheme.Hom.isCompact_preimage (D.map v) hW₁
  have hWV : c.π.app j ⁻¹ᵁ W = V := by
    change c.π.app j ⁻¹ᵁ (D.map v ⁻¹ᵁ W₁) = V
    rw [← Scheme.Hom.comp_preimage, c.w v, hW₁V]
  -- `f` is the base change of the model of `f`, hence of its base change to that stage.
  let eL₀ : X ≅ pullback X₀.hom (c.π.app i₀) := (Over.forget Y).mapIso e₀
  have hew₀ : eL₀.hom ≫ pullback.snd X₀.hom (c.π.app i₀) = f := Over.w e₀.hom
  have hA₀ : IsPullback (eL₀.hom ≫ pullback.fst X₀.hom (c.π.app i₀)) f X₀.hom (c.π.app i₀) :=
    IsPullback.of_iso_pullback
      ⟨by rw [Category.assoc, pullback.condition, ← Category.assoc, hew₀]⟩ eL₀ rfl hew₀
  let pj : pullback X₀.hom (D.map u) ⟶ D.obj j := pullback.snd X₀.hom (D.map u)
  have hA : IsPullback _ f pj (c.π.app j) := isPullback_pullbackLift_of_fac hA₀ (c.w u)
  have hfpj : FinitePresentation pj :=
    FinitePresentation.of_isPullback (IsPullback.of_hasPullback X₀.hom (D.map u)) hfp₀
  subst hWV
  exact hasFlatAlmostBlowUpSquarePair_of_isLimit_of_isPullback D c hc hA hfpj W hWcpt hflat

end AlgebraicGeometry

end
