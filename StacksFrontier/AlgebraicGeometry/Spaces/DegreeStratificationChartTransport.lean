module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartFibrePropertyDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.DegreeInductionSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.RepresentableByAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# Transporting the degree stratification of Stacks 07RY along an étale chart

Stacks 07S8, Lemma 68.8.1, says that a morphism `W ⟶ X` from a scheme to an algebraic space
which is flat, locally of finite presentation, separated and locally quasi-finite with
universally bounded fibres admits a finite filtration of `|X|` by reduced closed subspaces whose
strata universally characterize the base changes that are finite locally free of each degree.
Its proof is exactly one step: apply Stacks 07RY — the same statement for a morphism of
*schemes* — to the base change of `W ⟶ X` along a surjective étale scheme chart of `X`, and
descend the resulting filtration of the chart to `|X|`.

This file performs that transport. Everything here carries the hypothesis `h07RY`, which is
Stacks 07RY stated for morphisms of schemes in the repository's own vocabulary, with the bound
given in advance and the chain indexed by `ℕ`. Stacks 07RY itself is
`AlgebraicGeometry.exists_closed_filtration_characterizing_finiteLocallyFree_rank`, which
produces its own bound and indexes its chain by `Fin (n + 2)`; the module
`StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeClosedStratification` discharges `h07RY`
directly. Nothing below carries a Stacks attribute.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.exists_closedChain_isFiniteLocallyFreeOfRank_of_h07RY`: **Stacks 07S8
  modulo Stacks 07RY alone**, in the exact shape in which
  `StacksFrontier.AlgebraicGeometry.Spaces.DegreeInductionSchematicLocus` carries it as the
  hypothesis `h07S8`.
* `AlgebraicGeometry.Space.exists_isRepresentable_isOpenSubspace_of_h07RY`: the hypothesis
  `hchart` of Stacks 03JI, modulo Stacks 07RY alone.
* `AlgebraicGeometry.Space.exists_denseRange_isRepresentable_isOpenSubspace_of_h07RY`:
  **Stacks 03JI modulo Stacks 07RY alone** — a reasonable algebraic space over `S` has a
  representable open subspace with dense point set.

## Implementation notes

**The one hypothesis carried.** `h07RY` asks, for a morphism of schemes `f : X' ⟶ S'` which is
`AlgebraicGeometry.Flat`, `AlgebraicGeometry.LocallyOfFinitePresentation`,
`AlgebraicGeometry.IsSeparated` and `AlgebraicGeometry.LocallyQuasiFinite`, and for a natural
number `n` with `AlgebraicGeometry.BoundsFiberDegrees f n`, a chain `Y` of closed subsets of
`S'` with `Y 0 = ∅`, `Monotone Y` and `Y (n + 1) = Set.univ`, such that for `r ≤ n` a base
change `pullback.snd f t` is finite locally free of rank `r` exactly when the set-theoretic
image of `t` lies in the stratum `Y (r + 1) ∖ Y r`.

The three presentational choices — closed **subsets** rather than reduced closed subschemes, a
`Monotone` chain indexed by `ℕ` rather than a strictly increasing chain indexed by
`Fin (n + 2)`, and the universal property asked only for `r ≤ n` — are the same three the
hypothesis `h07S8` of
`StacksFrontier.AlgebraicGeometry.Spaces.DegreeInductionSchematicLocus` already makes, with the
same index shift: `Y r` is the source's `Z_{r-1}`, so `Y 0 = ∅` is the source's `Z_{-1}` and the
source's stratum `S_r` is `Y (r + 1) ∖ Y r`. A chain indexed by `Fin (n + 2)` yields one indexed
by `ℕ` by `fun m ↦ Z (min m (n + 1))`, and `Monotone` on `ℕ` is the conjunction of the
consecutive inclusions, so neither of those two choices asks for more than the source gives.

**The bound is given rather than produced.** `h07RY` takes `n` as an argument and asks for a
chain adapted to it, where Stacks 07RY states the bound existentially. This is the one respect in
which `h07RY` is stronger than the existential packaging: it is what the source's own proof
establishes, which opens "Let `n` be an integer bounding the degree of the fibres" and inducts on
that `n`, producing a chain indexed up to it. The hypothesis is phrased with the repository's
`AlgebraicGeometry.BoundsFiberDegrees`, which is part (1) of Stacks 03J4, rather than with
`AlgebraicGeometry.HasUniversallyBoundedFibers`, which is part (2) and quantifies `n` away.

**Why the bound transports.** The fibre bound available at the level of algebraic spaces,
`AlgebraicGeometry.Space.HasUniversallyBoundedFibers`, quantifies over field-valued points whose
spectra lie in the chosen site, while `AlgebraicGeometry.BoundsFiberDegrees` asks for the fibre
over the residue field at every point of the chart. The two are matched in
`boundsFiberDegrees_map_snd` through `property_fiberToSpecResidueField_iff`: a field-valued point
of the chart factors through the residue field at its underlying scheme point
(`AlgebraicGeometry.exists_residueFieldHom_comp_fromSpecResidueField`), a morphism of spectra of
fields is by itself an fpqc covering
(`AlgebraicGeometry.Space.fpqc_singleton_of_fieldSpecHom`), and being finite locally free of a
fixed rank is fpqc local at the target by the second assertion of Stacks 02VO,
`Stacks.Morphisms.isFiniteLocallyFreeOfRank_isLocalAtTarget_fpqc`. No field outside the site is
ever needed, and no new bound notion is introduced.

**Why the descent works.** The chain on the chart is pulled back to the point set of the chart
along the comparison bijection of clause (1) of Stacks 03BX,
`AlgebraicGeometry.Space.pointsToScheme`, and pushed forward to `|X|`. Both steps are legitimate
because membership of a point of the chart in `Y m` is, by the universal property of `h07RY`
applied to the residue field at that point, equivalent to the fibre over it being finite locally
free of some rank `s < m` — and that condition depends only on the class of the field-valued
point in the sense of Stacks 03BU, by
`AlgebraicGeometry.Space.property_representedFibre_iff_of_class_eq`. So each `Y m` pulls back to
a saturated set for the chart, whose image is closed because a surjective étale chart is a
quotient map on points (clauses (2) and (3) of Stacks 03BX).

**Why no 02VO descent step appears in the universal property.** The source proves the universal
property for `g : T ⟶ X` by choosing a chart `V ⟶ T`, passing to `U ×_X V` and descending along
`U ×_X V ⟶ V` by Stacks 02VO. That step is avoided here by choosing the chart of `T` to *be*
`A ×_X C ⟶ C ⟶ T` for an arbitrary chart `C ⟶ T` of `T`: it is again étale and surjective on
points, and its composite with `T ⟶ X` factors through the chart `A` of `X` by construction. The
fibre of the base change over that chart is then the fibre of the original morphism over a
morphism into `A`, by
`AlgebraicGeometry.Space.property_representedPullback_assoc`, and `h07RY` applies to it
directly. Condition (1) of Stacks 03ZW is read off the chart by
`AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_presheaf_iff_of_etaleChart_surjectiveOnPoints`.

**Nothing here carries a Stacks attribute.** Every statement below carries `h07RY`, so neither
Stacks 07S8 nor Stacks 03JI is proved in this file. Stacks 07S8 is
`AlgebraicGeometry.Space.exists_closedChain_isFiniteLocallyFreeOfRank` and Stacks 03JI is
`AlgebraicGeometry.Space.exists_denseRange_isRepresentable_isOpenSubspace_of_isReasonableSpace`.

## References

* [Stacks Project, Tag 07S8](https://stacks.math.columbia.edu/tag/07S8)
* [Stacks Project, Tag 07RY](https://stacks.math.columbia.edu/tag/07RY)
* [Stacks Project, Tag 03JI](https://stacks.math.columbia.edu/tag/03JI)
* [Stacks Project, Tag 03J4](https://stacks.math.columbia.edu/tag/03J4)
* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
* [Stacks Project, Tag 02VO](https://stacks.math.columbia.edu/tag/02VO)
* [Stacks Project, Tag 03ZW](https://stacks.math.columbia.edu/tag/03ZW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Morphisms

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
-- the `inferInstance` search for limits of presheaves on `BigFppfOver B S hS` is deep
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
private instance hasPullbacks_presheaf_DegreeStratificationChartTransport :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

private instance (priority := high) hasPullback_presheaf_DegreeStratificationChartTransport
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### Set-theoretic preliminaries -/

/-- A monotone chain of sets starting at the empty set is the union of its strata below the
index: a point lies in `Y r` exactly when it lies in one stratum `Y (s + 1) ∖ Y s` with
`s < r`. -/
private theorem mem_iff_exists_lt_mem_sdiff {α : Type*} (Y : ℕ → Set α) (hY0 : Y 0 = ∅)
    (hYm : Monotone Y) (x : α) (r : ℕ) : x ∈ Y r ↔ ∃ s, s < r ∧ x ∈ Y (s + 1) \ Y s := by
  induction r with
  | zero => simp [hY0]
  | succ r ih =>
    constructor
    · intro hx
      by_cases hr : x ∈ Y r
      · obtain ⟨s, hs, hmem⟩ := ih.mp hr
        exact ⟨s, hs.trans (Nat.lt_succ_self r), hmem⟩
      · exact ⟨r, Nat.lt_succ_self r, hx, hr⟩
    · rintro ⟨s, hs, hmem⟩
      exact hYm (Nat.succ_le_of_lt hs) hmem.1

/-- A set invariant under the fibres of a map is the preimage of its own image. -/
private theorem preimage_image_eq_of_invariant {α β : Type*} (f : α → β) (A : Set α)
    (h : ∀ x y, f x = f y → (x ∈ A ↔ y ∈ A)) : f ⁻¹' (f '' A) = A := by
  refine Set.Subset.antisymm ?_ (Set.subset_preimage_image _ _)
  rintro x ⟨y, hy, hxy⟩
  exact (h y x hxy).mp hy

/-- Taking the image along a map commutes with removing a set invariant under its fibres. -/
private theorem image_sdiff_of_invariant {α β : Type*} (f : α → β) (A C : Set α)
    (h : ∀ x y, f x = f y → (x ∈ C ↔ y ∈ C)) : f '' (A \ C) = f '' A \ f '' C := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro z ⟨x, ⟨hxA, hxC⟩, rfl⟩
    refine ⟨⟨x, hxA, rfl⟩, ?_⟩
    rintro ⟨y, hyC, hyx⟩
    exact hxC ((h y x hyx).mp hyC)
  · rintro z ⟨⟨x, hxA, rfl⟩, hz⟩
    exact ⟨x, ⟨hxA, fun hxC => hz ⟨x, hxC, rfl⟩⟩, rfl⟩

/-! ### Transport of a morphism property across represented base changes -/

/-- A morphism property respecting isomorphisms cannot distinguish the two projections to the
same object of two pullbacks of one cospan of schemes. -/
private theorem property_iff_of_isPullback_isPullback (P : MorphismProperty Scheme.{u})
    [P.RespectsIso] {Z Y T Q Q' : Scheme.{u}} {g : Z ⟶ Y} {c : T ⟶ Y}
    {fst : Q ⟶ Z} {snd : Q ⟶ T} {fst' : Q' ⟶ Z} {snd' : Q' ⟶ T}
    (h : IsPullback fst snd g c) (h' : IsPullback fst' snd' g c) : P snd ↔ P snd' := by
  have he : (h.isoIsPullback _ _ h').hom ≫ snd' = snd := h.isoIsPullback_hom_snd _ _ h'
  rw [← he]
  exact MorphismProperty.cancel_left_of_respectsIso P _ snd'

/-- A morphism property local at the target for the fpqc precoverage may be tested on an
arbitrary base change along a single morphism which is by itself an fpqc covering. This is
`AlgebraicGeometry.Space.property_iff_fpqc_singleton_pullback` for a pullback square that need
not be the chosen one. -/
private theorem property_iff_snd_of_isPullback_fpqc (P : MorphismProperty Scheme.{u})
    [P.IsLocalAtTarget Scheme.fpqcPrecoverage]
    {Z Y T Q : Scheme.{u}} {g : Z ⟶ Y} {c : T ⟶ Y} {fst : Q ⟶ Z} {snd : Q ⟶ T}
    (h : IsPullback fst snd g c)
    (hcov : Presieve.singleton c ∈ Scheme.fpqcPrecoverage.coverings Y) : P g ↔ P snd :=
  (property_iff_fpqc_singleton_pullback P g c hcov).trans
    (property_iff_of_isPullback_isPullback P (IsPullback.of_hasPullback g c) h)

/-- A morphism property respecting isomorphisms holds of the underlying morphism of schemes of
one represented base change of a relatively representable morphism exactly when it holds of the
base change provided by the representability witness. -/
private theorem property_map_iff_snd_of_isPullback (P : MorphismProperty Scheme.{u})
    [P.RespectsIso] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {W : BigFppfOver B S hS}
    {g : yoneda.obj W ⟶ X} (hg : yoneda.relativelyRepresentable g)
    {T Q : BigFppfOver B S hS} (ξ : yoneda.obj T ⟶ X)
    (i : yoneda.obj Q ⟶ yoneda.obj W) (q : Q ⟶ T)
    (hsq : IsPullback i (yoneda.map q) g ξ) :
    P ((BigFppfOver.toScheme B S hS).map q) ↔
      P ((BigFppfOver.toScheme B S hS).map (hg.snd ξ)) := by
  let e := yoneda.preimageIso (hsq.isoIsPullback _ _ (hg.isPullback ξ))
  have he : e.hom ≫ hg.snd ξ = q := by
    apply yoneda.map_injective
    simp [e]
  rw [← he, Functor.map_comp]
  exact MorphismProperty.cancel_left_of_respectsIso P _ _

/-- The morphism of presheaves attached to the image of a field-valued point of a represented
presheaf under a chart is the chart precomposed with the point. -/
private theorem yonedaEquiv_symm_map_value {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {A : BigFppfOver B S hS} (a : yoneda.obj A ⟶ X)
    (p : FieldValuedPoint B S hS (yoneda.obj A)) :
    yonedaEquiv.symm ((FieldValuedPoint.map B S hS (yoneda.obj A) a p).value) =
      yoneda.map p.value ≫ a := by
  apply yonedaEquiv.injective
  simp only [Equiv.apply_symm_apply]
  exact Eq.trans
    (by simp [FieldValuedPoint.map, FieldValuedPoint.siteObject, yonedaEquiv_apply,
      ← NatTrans.naturality_apply]
        rfl)
    (yonedaEquiv_naturality a p.value)

/-- **The fibre over a point of the chart is the fibre over any field-valued point above it.**
For a morphism property local at the target for the fpqc precoverage, the property of the
scheme-theoretic fibre of the represented chart base change over a point `x` of the chart agrees
with the property of the represented fibre of the original morphism over any field-valued point
of the chart with underlying scheme point `x`.

The field-valued point factors through the residue field at `x`, so the two fibres differ by a
base change along a morphism of spectra of fields, which is by itself an fpqc covering. -/
private theorem property_fiberToSpecResidueField_iff (P : MorphismProperty Scheme.{u})
    [P.IsLocalAtTarget Scheme.fpqcPrecoverage]
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {W : BigFppfOver B S hS}
    {g : yoneda.obj W ⟶ X} (hg : yoneda.relativelyRepresentable g)
    {A : BigFppfOver B S hS} (a : yoneda.obj A ⟶ X)
    (p : FieldValuedPoint B S hS (yoneda.obj A))
    (x : (BigFppfOver.toScheme B S hS).obj A) (hp : schemePoint B S hS A p = x) :
    P (((BigFppfOver.toScheme B S hS).map (hg.snd a)).fiberToSpecResidueField x) ↔
      P ((BigFppfOver.toScheme B S hS).map (hg.snd (yoneda.map p.value ≫ a))) := by
  have hsub : Subsingleton ((BigFppfOver.toScheme B S hS).obj p.siteObject) :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of p.carrier)))
  obtain ⟨ψ, hψ⟩ := exists_residueFieldHom_comp_fromSpecResidueField
    ((BigFppfOver.toScheme B S hS).map p.value) x
    (fun y => by
      rw [← hp]
      exact congrArg (fun z => (BigFppfOver.toScheme B S hS).map p.value z)
        (@Subsingleton.elim _ hsub y (IsLocalRing.closedPoint p.carrier)))
  have hout : IsPullback
      (pullback.snd ((BigFppfOver.toScheme B S hS).map p.value)
        ((BigFppfOver.toScheme B S hS).map (hg.snd a)))
      (pullback.fst ((BigFppfOver.toScheme B S hS).map p.value)
        ((BigFppfOver.toScheme B S hS).map (hg.snd a)))
      ((BigFppfOver.toScheme B S hS).map (hg.snd a))
      (Spec.map ψ ≫ ((BigFppfOver.toScheme B S hS).obj A).fromSpecResidueField x) := by
    rw [hψ]
    exact (IsPullback.of_hasPullback ((BigFppfOver.toScheme B S hS).map p.value)
      ((BigFppfOver.toScheme B S hS).map (hg.snd a))).flip
  have hfib : IsPullback
      (((BigFppfOver.toScheme B S hS).map (hg.snd a)).fiberι x)
      (((BigFppfOver.toScheme B S hS).map (hg.snd a)).fiberToSpecResidueField x)
      ((BigFppfOver.toScheme B S hS).map (hg.snd a))
      (((BigFppfOver.toScheme B S hS).obj A).fromSpecResidueField x) :=
    IsPullback.of_hasPullback ((BigFppfOver.toScheme B S hS).map (hg.snd a))
      (((BigFppfOver.toScheme B S hS).obj A).fromSpecResidueField x)
  refine (property_iff_snd_of_isPullback_fpqc P (IsPullback.of_right' hout hfib)
    (fpqc_singleton_of_fieldSpecHom (Spec.map ψ))).trans ?_
  refine Iff.trans ?_ (property_representedPullback_assoc B S hS P g hg a p.value).symm
  exact (property_map_pullback_snd_iff_pullback_fst B S hS P (hg.snd a) p.value).symm

/-! ### The chart base change of the morphism -/

/-- The base change of an étale chart along any morphism of presheaves is again an étale chart. -/
private theorem presheafEtale_of_isPullback {T₁ T₂ T₃ T₄ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {fst : T₁ ⟶ T₂} {snd : T₁ ⟶ T₃} {f : T₂ ⟶ T₄} {g : T₃ ⟶ T₄}
    (h : IsPullback fst snd f g)
    (hf : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf snd := by
  have := MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) (F := yoneda)
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback h hf

/-- A property holding on every étale chart of a morphism to an algebraic space holds of the
underlying morphism of schemes of its represented base change along an étale chart. -/
private theorem property_map_snd_of_holdsOnEveryEtaleChart (P : MorphismProperty Scheme.{u})
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {W : BigFppfOver B S hS}
    {g : yoneda.obj W ⟶ X} (hg : yoneda.relativelyRepresentable g)
    {A : BigFppfOver B S hS} {a : yoneda.obj A ⟶ X}
    (hae : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hP : HoldsOnEveryEtaleChart B S hS P g) :
    P ((BigFppfOver.toScheme B S hS).map (hg.snd a)) :=
  hP _ _ (hg.fst a) a (hg.snd a) (presheafEtale_of_isPullback B S hS (hg.isPullback a).flip hae) hae
    (hg.isPullback a).w.symm

/-- The represented base change of a separated morphism to an algebraic space along a chart is
a separated morphism of schemes. Separatedness is stable under base change, and separatedness of
a represented morphism is separatedness of the underlying morphism of schemes by Stacks 03KY. -/
private theorem isSeparated_map_snd {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {W : BigFppfOver B S hS} {g : yoneda.obj W ⟶ X} (hg : yoneda.relativelyRepresentable g)
    {A : BigFppfOver B S hS} (a : yoneda.obj A ⟶ X) (hsep : IsSeparated B S hS g) :
    _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map (hg.snd a)) := by
  refine (isSeparated_yoneda_map_iff B S hS (hg.snd a)).1 ?_
  have hstable : ((MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).diagonal) (hg.isPullback a) hsep

/-- **The fibre bound transports to the chart.** If every field-valued fibre of a morphism from
an object of the site to an algebraic space is finite locally free of rank at most `n`, then `n`
bounds the degrees of the fibres of the underlying morphism of schemes of its represented base
change along a chart. -/
private theorem boundsFiberDegrees_map_snd
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {W : BigFppfOver B S hS}
    {g : yoneda.obj W ⟶ X} (hg : yoneda.relativelyRepresentable g)
    {A : BigFppfOver B S hS} (a : yoneda.obj A ⟶ X) (n : ℕ)
    (hbound : ∀ (k : Type u) [Field k] (T : BigFppfOver B S hS),
      ((BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of k)) →
      ∀ ξ : yoneda.obj T ⟶ X,
        ∃ (Q : BigFppfOver B S hS) (q : Q ⟶ T) (i : yoneda.obj Q ⟶ yoneda.obj W) (r : ℕ),
          r ≤ n ∧ IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map q) r ∧
          IsPullback i (yoneda.map q) g ξ) :
    BoundsFiberDegrees ((BigFppfOver.toScheme B S hS).map (hg.snd a)) (n : ℤ) := by
  intro x
  obtain ⟨p, hp⟩ := exists_fieldValuedPoint_schemePoint_eq B S hS A x
  obtain ⟨Q, q, i, r, hrn, hr, hsq⟩ := hbound p.carrier p.siteObject (Iso.refl _)
    (yoneda.map p.value ≫ a)
  have _ := isFiniteLocallyFreeOfRank_isLocalAtTarget_fpqc.{u} r
  refine ⟨r, by exact_mod_cast hrn, ?_⟩
  refine (property_fiberToSpecResidueField_iff B S hS
    (IsFiniteLocallyFreeOfRank.property.{u} r) hg a p x hp).mpr ?_
  exact (property_map_iff_snd_of_isPullback B S hS
    (IsFiniteLocallyFreeOfRank.property.{u} r) hg (yoneda.map p.value ≫ a) i q hsq).mp hr

/-- For sets invariant under the fibres of a map, containment in a difference may be tested
after taking images. -/
private theorem subset_image_iff_of_invariant {α β : Type*} (f : α → β) (R A C : Set α)
    (hA : ∀ x y, f x = f y → (x ∈ A ↔ y ∈ A))
    (hC : ∀ x y, f x = f y → (x ∈ C ↔ y ∈ C)) :
    R ⊆ A \ C ↔ f '' R ⊆ f '' A \ f '' C := by
  rw [← image_sdiff_of_invariant f A C hC]
  refine ⟨fun h => Set.image_mono h, fun h => ?_⟩
  refine (Set.subset_preimage_image f R).trans ?_
  rw [← preimage_image_eq_of_invariant f (A \ C) (fun x y hxy => by
    simp only [Set.mem_sdiff]
    exact and_congr (hA x y hxy) (not_congr (hC x y hxy)))]
  exact Set.preimage_mono h

/-- **Stacks 07S8 modulo Stacks 07RY.** Let `h07RY` be Stacks 07RY for morphisms of schemes:
given a flat, locally finitely presented, separated and locally quasi-finite morphism of schemes
and a natural number `n` bounding the degrees of its fibres, a `Monotone` chain of closed
subsets of the target with `Y 0 = ∅` and `Y (n + 1) = Set.univ` whose strata `Y (r + 1) ∖ Y r`,
for `r ≤ n`, characterize the base changes which are finite locally free of degree `r`.

Then the same holds for a morphism from an object of the big fppf site of `S` to an algebraic
space over `S`, with the strata taken as closed subsets of its point set in the sense of
Stacks 03BU, and with "the fibre product is finite locally free of degree `r`" read as the
relative property `CategoryTheory.MorphismProperty.presheaf` of
`Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property r` on an arbitrary cartesian square
realizing the fibre product.

This is the hypothesis `h07S8` of
`StacksFrontier.AlgebraicGeometry.Spaces.DegreeInductionSchematicLocus`, stated there verbatim; it
is discharged here from `h07RY` alone. -/
theorem exists_closedChain_isFiniteLocallyFreeOfRank_of_h07RY
    (h07RY : ∀ {X' S' : Scheme.{u}} (f : X' ⟶ S'), Flat f → LocallyOfFinitePresentation f →
      _root_.AlgebraicGeometry.IsSeparated f → LocallyQuasiFinite f →
      ∀ n : ℕ, BoundsFiberDegrees f (n : ℤ) →
        ∃ Y : ℕ → Set S', Y 0 = ∅ ∧ (∀ r, IsClosed (Y r)) ∧ Monotone Y ∧
          Y (n + 1) = Set.univ ∧
          ∀ r : ℕ, r ≤ n → ∀ (T : Scheme.{u}) (t : T ⟶ S'),
            IsFiniteLocallyFreeOfRank (pullback.snd f t) r ↔
              Set.range t.base ⊆ Y (r + 1) \ Y r)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (W : BigFppfOver B S hS)
    (g : yoneda.obj W ⟶ X) (hX : IsAlgebraicSpace B S hS X)
    (hflat : IsFlat B S hS g) (hlfp : IsLocallyOfFinitePresentation B S hS g)
    (hsep : IsSeparated B S hS g) (hlqf : IsLocallyQuasiFinite B S hS g)
    (n : ℕ)
    (hbound : ∀ (k : Type u) [Field k] (T : BigFppfOver B S hS),
      ((BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of k)) →
      ∀ ξ : yoneda.obj T ⟶ X,
        ∃ (Q : BigFppfOver B S hS) (q : Q ⟶ T) (i : yoneda.obj Q ⟶ yoneda.obj W) (r : ℕ),
          r ≤ n ∧ IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map q) r ∧
          IsPullback i (yoneda.map q) g ξ) :
    ∃ Z : ℕ → Set (points B S hS X), Z 0 = ∅ ∧ (∀ r, IsClosed (Z r)) ∧ Monotone Z ∧
      Z (n + 1) = Set.univ ∧
      ∀ r : ℕ, r ≤ n → ∀ (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hm : T ⟶ X),
        IsAlgebraicSpace B S hS T →
        ∀ (Pp : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (pr₁ : Pp ⟶ yoneda.obj W) (pr₂ : Pp ⟶ T),
          IsPullback pr₁ pr₂ g hm →
          ((MorphismProperty.inverseImage (IsFiniteLocallyFreeOfRank.property.{u} r)
              (BigFppfOver.toScheme B S hS)).presheaf pr₂ ↔
            Set.range (pointsMap B S hS T hm) ⊆ Z (r + 1) \ Z r) := by
  obtain ⟨A, a, hasurjrep, haetale⟩ := hX.exists_atlas
  have hg : yoneda.relativelyRepresentable g :=
    relativelyRepresentable_of_isAlgebraicSpace B S hS hX g
  have ha : yoneda.relativelyRepresentable a := haetale.rep
  have hasurj : Function.Surjective (pointsMap B S hS (yoneda.obj A) a) :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS X hX A a).mp hasurjrep
  have hflat' : Flat ((BigFppfOver.toScheme B S hS).map (hg.snd a)) :=
    property_map_snd_of_holdsOnEveryEtaleChart B S hS _ hg haetale hflat
  have hlfp' : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map (hg.snd a)) :=
    property_map_snd_of_holdsOnEveryEtaleChart B S hS _ hg haetale hlfp
  have hlqf' : LocallyQuasiFinite ((BigFppfOver.toScheme B S hS).map (hg.snd a)) :=
    (property_map_snd_of_holdsOnEveryEtaleChart B S hS _ hg haetale hlqf).2
  have hsep' := isSeparated_map_snd B S hS hg a hsep
  obtain ⟨Y, hY0, hYc, hYm, hYtop, hYuniv⟩ := h07RY _ hflat' hlfp' hsep' hlqf' n
    (boundsFiberDegrees_map_snd B S hS hg a n hbound)
  -- the chain is the degree filtration of the fibres of the chart base change
  have hmemY : ∀ (x : (BigFppfOver.toScheme B S hS).obj A) (m : ℕ),
      x ∈ Y m ↔ ∃ s, s < m ∧ s ≤ n ∧ IsFiniteLocallyFreeOfRank
        (((BigFppfOver.toScheme B S hS).map (hg.snd a)).fiberToSpecResidueField x) s := by
    intro x m
    have hstratum : ∀ s : ℕ, s ≤ n → (x ∈ Y (s + 1) \ Y s ↔
        IsFiniteLocallyFreeOfRank
          (((BigFppfOver.toScheme B S hS).map (hg.snd a)).fiberToSpecResidueField x) s) := by
      intro s hs
      have h1 := hYuniv s hs (Spec (((BigFppfOver.toScheme B S hS).obj A).residueField x))
        (((BigFppfOver.toScheme B S hS).obj A).fromSpecResidueField x)
      have hrange : Set.range
          (((BigFppfOver.toScheme B S hS).obj A).fromSpecResidueField x).base = {x} := by
        simp
      rw [hrange, Set.singleton_subset_iff] at h1
      exact h1.symm
    rw [mem_iff_exists_lt_mem_sdiff Y hY0 hYm x m]
    constructor
    · rintro ⟨s, hs, hmem⟩
      have hsn : s ≤ n := by
        by_contra hc
        exact hmem.2 (hYm (by omega : n + 1 ≤ s) (by simp [hYtop]))
      exact ⟨s, hs, hsn, (hstratum s hsn).mp hmem⟩
    · rintro ⟨s, hs, hsn, hflf⟩
      exact ⟨s, hs, (hstratum s hsn).mpr hflf⟩
  have hinv : ∀ (m : ℕ) (w₁ w₂ : points B S hS (yoneda.obj A)),
      pointsMap B S hS (yoneda.obj A) a w₁ = pointsMap B S hS (yoneda.obj A) a w₂ →
      (w₁ ∈ pointsToScheme B S hS A ⁻¹' Y m ↔ w₂ ∈ pointsToScheme B S hS A ⁻¹' Y m) := by
    intro m w₁ w₂ hw
    obtain ⟨p, rfl⟩ := Quot.exists_rep w₁
    obtain ⟨q, rfl⟩ := Quot.exists_rep w₂
    simp only [Set.mem_preimage, pointsToScheme_class]
    rw [hmemY _ m, hmemY _ m]
    refine exists_congr fun s => and_congr_right fun _ => and_congr_right fun _ => ?_
    have hcl : (FieldValuedPoint.map B S hS (yoneda.obj A) a p).class B S hS X =
        (FieldValuedPoint.map B S hS (yoneda.obj A) a q).class B S hS X := hw
    have _ := isFiniteLocallyFreeOfRank_isLocalAtTarget_fpqc.{u} s
    refine Iff.trans (property_fiberToSpecResidueField_iff B S hS
      (IsFiniteLocallyFreeOfRank.property.{u} s) hg a p _ rfl) ?_
    refine Iff.trans ?_ (property_fiberToSpecResidueField_iff B S hS
      (IsFiniteLocallyFreeOfRank.property.{u} s) hg a q _ rfl).symm
    rw [← yonedaEquiv_symm_map_value B S hS a p, ← yonedaEquiv_symm_map_value B S hS a q]
    exact property_representedFibre_iff_of_class_eq B S hS
      (IsFiniteLocallyFreeOfRank.property.{u} s)
      (isFiniteLocallyFreeOfRank_isLocalAtTarget_fpqc.{u} s) g hg _ _ hcl
  refine ⟨fun m => pointsMap B S hS (yoneda.obj A) a '' (pointsToScheme B S hS A ⁻¹' Y m),
    ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only
    rw [hY0]
    simp
  · intro m
    dsimp only
    have hq := isQuotientMap_pointsMap_of_presheafEtale B S hS a haetale hasurj
    rw [← hq.isCoinducing.isClosed_preimage,
      preimage_image_eq_of_invariant _ _ (hinv m),
      isClosed_pointTopology_yoneda_iff_isClosed_image,
      Set.image_preimage_eq _ (surjective_pointsToScheme B S hS A)]
    exact hYc m
  · exact fun m₁ m₂ hm => Set.image_mono (Set.preimage_mono (hYm hm))
  · dsimp only
    rw [hYtop, Set.preimage_univ, Set.image_univ, hasurj.range_eq]
  · intro r hrn Tf hm hT Pp pr₁ pr₂ hsq
    dsimp only
    obtain ⟨C, c, hcsurjrep, hcetale⟩ := hT.exists_atlas
    have hcsurj : Function.Surjective (pointsMap B S hS (yoneda.obj C) c) :=
      (presheafSurjective_iff_isSurjective_yoneda B S hS Tf hT C c).mp hcsurjrep
    obtain ⟨d, hdmap⟩ : ∃ d : ha.pullback (c ≫ hm) ⟶ A,
        yoneda.map d = ha.fst (c ≫ hm) :=
      ⟨yoneda.preimage (ha.fst (c ≫ hm)), by simp⟩
    have hsqa : IsPullback (ha.fst (c ≫ hm)) (yoneda.map (ha.snd (c ≫ hm))) a (c ≫ hm) :=
      ha.isPullback (c ≫ hm)
    have hsndEtale := presheafEtale_of_isPullback B S hS hsqa haetale
    have hsndSurj : Function.Surjective
        (pointsMap B S hS (yoneda.obj (ha.pullback (c ≫ hm)))
          (yoneda.map (ha.snd (c ≫ hm)))) :=
      surjective_pointsMap_of_isPullback B S hS hsqa hasurj
    have hc'etale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf
        (yoneda.map (ha.snd (c ≫ hm)) ≫ c) :=
      isEtale_of_presheaf_etale B S hS hcetale _ (yoneda.map (ha.snd (c ≫ hm))) hsndEtale
    have hc'surj : Function.Surjective (pointsMap B S hS
        (yoneda.obj (ha.pullback (c ≫ hm))) (yoneda.map (ha.snd (c ≫ hm)) ≫ c)) := by
      rw [pointsMap_comp]
      exact hcsurj.comp hsndSurj
    have hpr₂ : yoneda.relativelyRepresentable pr₂ :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq hg
    have hPp : IsAlgebraicSpace B S hS Pp :=
      isAlgebraicSpace_of_iso B S hS hsq.isoPullback.symm
        (isAlgebraicSpace_pullback B S hS g hm (isAlgebraicSpace_yoneda B S hS W) hT hX)
    have hcomp : (yoneda.map (ha.snd (c ≫ hm)) ≫ c) ≫ hm = yoneda.map d ≫ a := by
      rw [Category.assoc, ← hsqa.w, hdmap]
    have hpaste : IsPullback (hpr₂.fst (yoneda.map (ha.snd (c ≫ hm)) ≫ c) ≫ pr₁)
        (yoneda.map (hpr₂.snd (yoneda.map (ha.snd (c ≫ hm)) ≫ c))) g (yoneda.map d ≫ a) := by
      rw [← hcomp]
      exact (hpr₂.isPullback _).paste_horiz hsq
    have hstep5 : IsFiniteLocallyFreeOfRank
        (pullback.fst ((BigFppfOver.toScheme B S hS).map d)
          ((BigFppfOver.toScheme B S hS).map (hg.snd a))) r ↔
        IsFiniteLocallyFreeOfRank (pullback.snd
          ((BigFppfOver.toScheme B S hS).map (hg.snd a))
          ((BigFppfOver.toScheme B S hS).map d)) r :=
      property_iff_of_isPullback_isPullback (IsFiniteLocallyFreeOfRank.property.{u} r)
        (IsPullback.of_hasPullback ((BigFppfOver.toScheme B S hS).map d)
          ((BigFppfOver.toScheme B S hS).map (hg.snd a))).flip
        (IsPullback.of_hasPullback ((BigFppfOver.toScheme B S hS).map (hg.snd a))
          ((BigFppfOver.toScheme B S hS).map d))
    have hrangeA : Set.range ((BigFppfOver.toScheme B S hS).map d).base =
        pointsToScheme B S hS A ''
          Set.range (pointsMap B S hS (yoneda.obj (ha.pullback (c ≫ hm)))
            (yoneda.map d)) := by
      rw [← Set.range_comp]
      refine Set.ext fun z => ?_
      constructor
      · rintro ⟨y, rfl⟩
        obtain ⟨w, hw⟩ := surjective_pointsToScheme B S hS (ha.pullback (c ≫ hm)) y
        exact ⟨w, by rw [Function.comp_apply, pointsToScheme_pointsMap_yoneda, hw]⟩
      · rintro ⟨w, rfl⟩
        exact ⟨pointsToScheme B S hS (ha.pullback (c ≫ hm)) w, by
          rw [Function.comp_apply, pointsToScheme_pointsMap_yoneda]⟩
    have hrangeT : Set.range (pointsMap B S hS Tf hm) =
        pointsMap B S hS (yoneda.obj A) a ''
          Set.range (pointsMap B S hS (yoneda.obj (ha.pullback (c ≫ hm)))
            (yoneda.map d)) := by
      have e1 : Set.range (pointsMap B S hS (yoneda.obj (ha.pullback (c ≫ hm)))
          ((yoneda.map (ha.snd (c ≫ hm)) ≫ c) ≫ hm)) =
          Set.range (pointsMap B S hS Tf hm) := by
        rw [pointsMap_comp, Set.range_comp, hc'surj.range_eq, Set.image_univ]
      rw [← e1, hcomp, pointsMap_comp, Set.range_comp]
    refine (isFiniteLocallyFreeOfRank_presheaf_iff_of_etaleChart_surjectiveOnPoints
      B S hS r hPp hT hpr₂ hc'etale hc'surj).trans ?_
    refine (property_map_iff_snd_of_isPullback B S hS
      (IsFiniteLocallyFreeOfRank.property.{u} r) hg (yoneda.map d ≫ a) _ _ hpaste).trans ?_
    refine (property_representedPullback_assoc B S hS
      (IsFiniteLocallyFreeOfRank.property.{u} r) g hg a d).trans ?_
    refine (property_map_pullback_snd_iff_pullback_fst B S hS
      (IsFiniteLocallyFreeOfRank.property.{u} r) (hg.snd a) d).trans ?_
    refine hstep5.trans ?_
    refine (hYuniv r hrn _ ((BigFppfOver.toScheme B S hS).map d)).trans ?_
    rw [hrangeA, hrangeT]
    refine Iff.trans Set.image_subset_iff ?_
    rw [Set.preimage_sdiff]
    exact subset_image_iff_of_invariant _ _ _ _ (hinv (r + 1)) (hinv r)

/-! ### Tag 03JI modulo Tag 07RY -/

/-- **The hypothesis `hchart` of Stacks 03JI, modulo Stacks 07RY alone.** A nonempty algebraic
space over `S` carrying an affine étale chart which is surjective on points and has universally
bounded fibres has a nonempty representable open subspace.

This is
`AlgebraicGeometry.Space.exists_isRepresentable_isOpenSubspace_of_h07S8` with its hypothesis
`h07S8` discharged by
`AlgebraicGeometry.Space.exists_closedChain_isFiniteLocallyFreeOfRank_of_h07RY`. -/
theorem exists_isRepresentable_isOpenSubspace_of_h07RY
    (h07RY : ∀ {X' S' : Scheme.{u}} (f : X' ⟶ S'), Flat f → LocallyOfFinitePresentation f →
      _root_.AlgebraicGeometry.IsSeparated f → LocallyQuasiFinite f →
      ∀ n : ℕ, BoundsFiberDegrees f (n : ℤ) →
        ∃ Y : ℕ → Set S', Y 0 = ∅ ∧ (∀ r, IsClosed (Y r)) ∧ Monotone Y ∧
          Y (n + 1) = Set.univ ∧
          ∀ r : ℕ, r ≤ n → ∀ (T : Scheme.{u}) (t : T ⟶ S'),
            IsFiniteLocallyFreeOfRank (pullback.snd f t) r ↔
              Set.range t.base ⊆ Y (r + 1) \ Y r)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (V : BigFppfOver B S hS)
    (b : yoneda.obj V ⟶ X) (hX : IsAlgebraicSpace B S hS X)
    (hVaff : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (hbetale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (hbsurj : Function.Surjective (pointsMap B S hS (yoneda.obj V) b))
    (hbfib : HasUniversallyBoundedFibers B S hS V b)
    (hne : Nonempty (points B S hS X)) :
    ∃ H : Subfunctor X, IsOpenSubspace B S hS H ∧ H.toFunctor.IsRepresentable ∧
      (Set.range (pointsMap B S hS H.toFunctor H.ι)).Nonempty :=
  exists_isRepresentable_isOpenSubspace_of_h07S8 B S hS
    (fun X' W' g' hX' hflat' hlfp' hsep' hlqf' n' hbound' =>
      exists_closedChain_isFiniteLocallyFreeOfRank_of_h07RY B S hS h07RY X' W' g' hX' hflat'
        hlfp' hsep' hlqf' n' hbound')
    X V b hX hVaff hbetale hbsurj hbfib hne

/-- **Stacks 03JI modulo Stacks 07RY alone.** A reasonable algebraic space over `S` has a
representable open subspace whose point set is dense, as soon as Stacks 07RY is available.

This is
`AlgebraicGeometry.Space.exists_denseRange_isRepresentable_isOpenSubspace_of_h07S8` with its
hypothesis `h07S8` discharged by
`AlgebraicGeometry.Space.exists_closedChain_isFiniteLocallyFreeOfRank_of_h07RY`. Everything else
in the proof of Stacks 03JI is proved in
`StacksFrontier.AlgebraicGeometry.Spaces.DegreeInductionSchematicLocus` and in
`StacksFrontier.AlgebraicGeometry.Spaces.ReasonableDenseSchematicLocus`. -/
theorem exists_denseRange_isRepresentable_isOpenSubspace_of_h07RY
    (h07RY : ∀ {X' S' : Scheme.{u}} (f : X' ⟶ S'), Flat f → LocallyOfFinitePresentation f →
      _root_.AlgebraicGeometry.IsSeparated f → LocallyQuasiFinite f →
      ∀ n : ℕ, BoundsFiberDegrees f (n : ℤ) →
        ∃ Y : ℕ → Set S', Y 0 = ∅ ∧ (∀ r, IsClosed (Y r)) ∧ Monotone Y ∧
          Y (n + 1) = Set.univ ∧
          ∀ r : ℕ, r ≤ n → ∀ (T : Scheme.{u}) (t : T ⟶ S'),
            IsFiniteLocallyFreeOfRank (pullback.snd f t) r ↔
              Set.range t.base ⊆ Y (r + 1) \ Y r)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hr : IsReasonableSpace B S hS X) :
    ∃ G : Subfunctor X, IsOpenSubspace B S hS G ∧ G.toFunctor.IsRepresentable ∧
      DenseRange (pointsMap B S hS G.toFunctor G.ι) :=
  exists_denseRange_isRepresentable_isOpenSubspace_of_h07S8 B S hS
    (fun X' W' g' hX' hflat' hlfp' hsep' hlqf' n' hbound' =>
      exists_closedChain_isFiniteLocallyFreeOfRank_of_h07RY B S hS h07RY X' W' g' hX' hflat'
        hlfp' hsep' hlqf' n' hbound')
    hX hr

end AlgebraicGeometry.Space

end
