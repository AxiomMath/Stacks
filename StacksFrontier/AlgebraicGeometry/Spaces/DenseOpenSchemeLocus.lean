module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.QuasiFiniteUniversallyBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fold5.Monomorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.ReasonableDenseSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# Rydh's theorem: a decent algebraic space has a dense schematic open subspace

Tag 086U, due to David Rydh, says that a *decent* algebraic space over a scheme `S` contains a
dense open subspace which is a scheme. This file proves statements about a single scheme and
permanence statements for decency used in its proof, and deduces the conclusion of Tag 086U
from its geometric core, that a nonempty decent algebraic space has a nonempty representable
open subspace, taken as a hypothesis: either for every nonempty decent algebraic space
(`hcore`), or only for those carrying an affine étale chart surjective on points (`hchart`).

## Main results

* `AlgebraicGeometry.Scheme.exists_antitone_affineOpens_le`: from a family `W : ℕ → Y.Opens` of
  opens of a scheme, one nonempty affine open inside `W 0`, and the hypothesis that a nonempty
  affine open inside `W n` always meets `W (n + 1)`, there is an antitone family of nonempty
  affine opens with `V n ≤ W n`.
* `AlgebraicGeometry.Scheme.nonempty_iInter_of_forall_inter_nonempty`: under the same
  hypotheses, and assuming that a descending chain of nonempty affine opens of a scheme has
  nonempty intersection, the intersection of all the `W n` is nonempty.
* `AlgebraicGeometry.Space.isQuasiCompact_of_comp_mono`: quasi-compactness of a morphism of
  algebraic spaces over `S` in the sense of Tag 03HE may be cancelled against a monomorphism on
  the target side.
* `AlgebraicGeometry.Space.eq_openSubspaceOfPoints_range_pointsMap_ι`: an open subspace is the
  subspace cut out by its own set of points.
* `AlgebraicGeometry.Space.exists_comp_ι_eq_fieldMorphism`: a field-valued point whose class
  lies in the point set of an open subspace factors through that open subspace.
* `AlgebraicGeometry.Space.isDecentSpace_of_isOpenSubspace`: an open subspace of a decent
  algebraic space over `S` is decent.
* `AlgebraicGeometry.Space.isSchemeOpen_preimage_range_pointsMap_ι` and
  `AlgebraicGeometry.Space.exists_opens_mem_iff_mem_range_pointsMap_ι`: the preimage of an
  open subspace in an étale chart is cut out by an open of the chart's scheme.
* `AlgebraicGeometry.Space.exists_isRepresentable_isOpenSubspace_of_decentChartCore`: the
  absolute core from the affine-chart core.
* `AlgebraicGeometry.Space.exists_isRepresentable_isOpenSubspace_le_of_decentCore`: from the
  absolute core, every nonempty open subspace of a decent algebraic space contains a nonempty
  representable open subspace.
* `AlgebraicGeometry.Space.exists_denseRange_isRepresentable_isOpenSubspace_of_decentCore` and
  `AlgebraicGeometry.Space.exists_denseRange_isRepresentable_isOpenSubspace_of_decentChartCore`:
  the conclusion of Tag 086U for a decent algebraic space over `S`, from the absolute core and
  from the affine-chart core respectively.

## References

* [Stacks Project, Tag 086U](https://stacks.math.columbia.edu/tag/086U)
* [Stacks Project, Tag 086T](https://stacks.math.columbia.edu/tag/086T)
* [Stacks Project, Tag 03JI](https://stacks.math.columbia.edu/tag/03JI)
* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
* [Stacks Project, Tag 03JV](https://stacks.math.columbia.edu/tag/03JV)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03I8](https://stacks.math.columbia.edu/tag/03I8)
* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
* [Stacks Project, Tag 03FX](https://stacks.math.columbia.edu/tag/03FX)
* [Stacks Project, Tag 01Z2](https://stacks.math.columbia.edu/tag/01Z2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### The chain of affine opens of Rydh's argument -/

/-- Let `W : ℕ → Y.Opens` be any family of opens of a scheme `Y`, let `W 0` contain a nonempty
affine open, and assume that every nonempty affine open contained in `W n` meets `W (n + 1)`.
Then there is an antitone family of nonempty affine opens `V n ≤ W n`. -/
theorem Scheme.exists_antitone_affineOpens_le {Y : Scheme.{u}} (W : ℕ → Y.Opens)
    (hbase : ∃ V : Y.Opens, IsAffineOpen V ∧ (V : Set Y).Nonempty ∧ V ≤ W 0)
    (hstep : ∀ (n : ℕ) (V : Y.Opens), IsAffineOpen V → (V : Set Y).Nonempty → V ≤ W n →
      ((V : Set Y) ∩ (W (n + 1) : Set Y)).Nonempty) :
    ∃ V : ℕ → Y.Opens, Antitone V ∧
      ∀ n, IsAffineOpen (V n) ∧ (V n : Set Y).Nonempty ∧ V n ≤ W n := by
  set Q : ℕ → Y.Opens → Prop :=
    fun n V => IsAffineOpen V ∧ (V : Set Y).Nonempty ∧ V ≤ W n
  have key : ∀ (n : ℕ) (v : {V : Y.Opens // Q n V}),
      ∃ v' : {V : Y.Opens // Q (n + 1) V}, v'.1 ≤ v.1 := by
    intro n v
    obtain ⟨hVaff, hVne, hVle⟩ := v.2
    obtain ⟨y, hyV, hyW⟩ := hstep n v.1 hVaff hVne hVle
    obtain ⟨T, hTaff, hyT, hTle⟩ :=
      exists_isAffineOpen_mem_and_subset (U := v.1 ⊓ W (n + 1)) (x := y) ⟨hyV, hyW⟩
    exact ⟨⟨T, hTaff, ⟨y, hyT⟩, le_trans hTle inf_le_right⟩, le_trans hTle inf_le_left⟩
  obtain ⟨V0, hV0⟩ := hbase
  let g : (n : ℕ) → {V : Y.Opens // Q n V} := fun n =>
    Nat.rec (motive := fun n => {V : Y.Opens // Q n V}) ⟨V0, hV0⟩
      (fun n v => (key n v).choose) n
  have hgstep : ∀ n, (g (n + 1)).1 ≤ (g n).1 := fun n => (key n (g n)).choose_spec
  exact ⟨fun n => (g n).1, antitone_nat_of_succ_le hgstep, fun n => (g n).2⟩

/-- Under the hypotheses of `AlgebraicGeometry.Scheme.exists_antitone_affineOpens_le`, and
assuming `h01Z2`, that a descending chain of nonempty affine opens of a scheme has nonempty
intersection, the intersection of all the `W n` is nonempty. -/
theorem Scheme.nonempty_iInter_of_forall_inter_nonempty
    (h01Z2 : ∀ (Z : Scheme.{u}) (V : ℕ → Z.Opens), (∀ n, IsAffineOpen (V n)) →
      (∀ n, (V n : Set Z).Nonempty) → Antitone V → (⋂ n, (V n : Set Z)).Nonempty)
    {Y : Scheme.{u}} (W : ℕ → Y.Opens)
    (hbase : ∃ V : Y.Opens, IsAffineOpen V ∧ (V : Set Y).Nonempty ∧ V ≤ W 0)
    (hstep : ∀ (n : ℕ) (V : Y.Opens), IsAffineOpen V → (V : Set Y).Nonempty → V ≤ W n →
      ((V : Set Y) ∩ (W (n + 1) : Set Y)).Nonempty) :
    (⋂ n, (W n : Set Y)).Nonempty := by
  obtain ⟨V, hVanti, hV⟩ := Scheme.exists_antitone_affineOpens_le W hbase hstep
  obtain ⟨y, hy⟩ := h01Z2 Y V (fun n => (hV n).1) (fun n => (hV n).2.1) hVanti
  exact ⟨y, Set.mem_iInter.2 fun n => (hV n).2.2 (Set.mem_iInter.1 hy n)⟩

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/-! ### Cancelling a monomorphism out of quasi-compactness -/

set_option synthInstance.maxHeartbeats 200000 in
-- instance search for the pullbacks (`IsPullback.of_hasPullback`) of functors on the fppf site
/-- If `f ≫ m` is a quasi-compact morphism of algebraic spaces over `S` in the sense of
Tag 03HE and `m` is a monomorphism, then `f` is quasi-compact. -/
theorem isQuasiCompact_of_comp_mono {F Y X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ Y) (m : Y ⟶ X) [Mono m] (hf : IsQuasiCompact B S hS (f ≫ m)) :
    IsQuasiCompact B S hS f := by
  intro Z hZ hZqc g
  exact (hf Z hZ hZqc (g ≫ m)).of_iso B S hS
    (isPullback_comp_mono (IsPullback.of_hasPullback g f) m).isoPullback.symm

/-! ### An open subspace is cut out by its own point set -/

/-- An open subspace of an algebraic space over `S` is the subspace cut out by its own set of
points. -/
theorem eq_openSubspaceOfPoints_range_pointsMap_ι
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {G : Subfunctor X} (hG : IsOpenSubspace B S hS G) :
    G = openSubspaceOfPoints B S hS X
      (Set.range (pointsMap B S hS G.toFunctor G.ι)) := by
  have hopen : IsOpen (Set.range (pointsMap B S hS G.toFunctor G.ι)) :=
    isOpen_range_pointsMap_of_isOpenImmersion B S hS G.ι hG.2
  have hrange := range_pointsMap_ι_openSubspaceOfPoints B S hS
    (F := X) (Set.range (pointsMap B S hS G.toFunctor G.ι))
  refine le_antisymm (le_of_range_pointsMap_ι_subset B S hS
      (isOpenSubspace_openSubspaceOfPoints B S hS hX _ hopen) ?_)
    (le_of_range_pointsMap_ι_subset B S hS hG ?_) <;> rw [hrange]

/-- A field-valued point whose class lies in the point set of an open subspace factors through
that open subspace. -/
theorem exists_comp_ι_eq_fieldMorphism
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {G : Subfunctor X} (hG : IsOpenSubspace B S hS G)
    (p : FieldValuedPoint B S hS X)
    (hp : p.class B S hS X ∈ Set.range (pointsMap B S hS G.toFunctor G.ι)) :
    ∃ g : yoneda.obj (FieldValuedPoint.siteObject B S hS X p) ⟶ G.toFunctor,
      g ≫ G.ι = fieldMorphism B S hS X p := by
  set W := Set.range (pointsMap B S hS G.toFunctor G.ι) with hW
  have hGeq := eq_openSubspaceOfPoints_range_pointsMap_ι B S hS hX hG
  rw [hGeq]
  have hmem : p.value ∈ (openSubspaceOfPoints B S hS X W).obj
      (Opposite.op (FieldValuedPoint.siteObject B S hS X p)) := by
    rintro y ⟨w, rfl⟩
    obtain ⟨q, rfl⟩ := Quot.exists_rep w
    rw [FieldValuedPoint.pointsMap_class_eq_class]
    exact hp
  exact ⟨yonedaEquiv.symm ⟨p.value, hmem⟩,
    yonedaEquiv_symm_naturality_right _ (openSubspaceOfPoints B S hS X W).ι _⟩

/-! ### Decency passes to open subspaces -/

/-- An open subspace of a decent algebraic space over `S` is decent. -/
theorem isDecentSpace_of_isOpenSubspace
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X)
    {G : Subfunctor X} (hG : IsOpenSubspace B S hS G) :
    IsDecentSpace B S hS G.toFunctor := by
  intro y
  obtain ⟨p, hpx, hmono, hqc⟩ := hdec (pointsMap B S hS G.toFunctor G.ι y)
  obtain ⟨g, hg⟩ := exists_comp_ι_eq_fieldMorphism B S hS hX hG p (hpx ▸ ⟨y, rfl⟩)
  have hfield : fieldMorphism B S hS G.toFunctor
      (FieldValuedPoint.map B S hS (yoneda.obj (FieldValuedPoint.siteObject B S hS X p)) g
        (FieldValuedPoint.tautological B S hS p)) = g := by
    change yonedaEquiv.symm (yonedaEquiv g) = g
    exact yonedaEquiv.symm_apply_apply g
  refine ⟨FieldValuedPoint.map B S hS (yoneda.obj (FieldValuedPoint.siteObject B S hS X p)) g
    (FieldValuedPoint.tautological B S hS p), ?_, ?_, ?_⟩
  · refine pointsMap_injective_of_mono B S hS G.ι ?_
    rw [← pointsMap_class, ← pointsMap_comp_apply, hg, ← hpx]
    exact FieldValuedPoint.pointsMap_class_eq_class B S hS p
      (FieldValuedPoint.tautological B S hS p)
  · have hgm : Mono (g ≫ G.ι) := by rw [hg]; exact hmono
    rw [hfield]
    exact CategoryTheory.mono_of_mono g G.ι
  · rw [hfield]
    exact isQuasiCompact_of_comp_mono B S hS g G.ι (by rw [hg]; exact hqc)

/-! ### The preimage of an open subspace in a chart -/

/-- The preimage of the point set of an open subspace under a scheme-valued point `a` is cut
out by an open of the scheme. -/
theorem isSchemeOpen_preimage_range_pointsMap_ι
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {G : Subfunctor X}
    (hG : IsOpenSubspace B S hS G) (A : BigFppfOver B S hS) (a : yoneda.obj A ⟶ X) :
    IsSchemeOpen B S hS A (pointsMap B S hS (yoneda.obj A) a ⁻¹'
      Set.range (pointsMap B S hS G.toFunctor G.ι)) :=
  (isOpen_pointTopology_iff B S hS _).1
    (isOpen_range_pointsMap_of_isOpenImmersion B S hS G.ι hG.2) A a

/-- The preimage of the point set of an open subspace under a scheme-valued point `a` is cut
out by an element `Vs` of the opens of the scheme. -/
theorem exists_opens_mem_iff_mem_range_pointsMap_ι
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {G : Subfunctor X}
    (hG : IsOpenSubspace B S hS G) (A : BigFppfOver B S hS) (a : yoneda.obj A ⟶ X) :
    ∃ Vs : ((BigFppfOver.toScheme B S hS).obj A).Opens,
      ∀ q : FieldValuedPoint B S hS (yoneda.obj A),
        pointsMap B S hS (yoneda.obj A) a (q.class B S hS (yoneda.obj A)) ∈
            Set.range (pointsMap B S hS G.toFunctor G.ι) ↔
          schemePoint B S hS A q ∈ Vs := by
  obtain ⟨Vs, hVsopen, hVsmem⟩ := isSchemeOpen_preimage_range_pointsMap_ι B S hS hG A a
  exact ⟨⟨Vs, hVsopen⟩, hVsmem⟩

/-! ### From the affine-chart core to Tag 086U -/

/-- Assume `hchart`: a nonempty decent algebraic space over `S` carrying an affine étale chart
which is surjective on points has a nonempty representable open subspace. Then every nonempty
decent algebraic space over `S` has a nonempty representable open subspace. -/
theorem exists_isRepresentable_isOpenSubspace_of_decentChartCore
    (hchart : ∀ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (V : BigFppfOver B S hS)
      (b : yoneda.obj V ⟶ Y), IsAlgebraicSpace B S hS Y → IsDecentSpace B S hS Y →
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf b →
      Function.Surjective (pointsMap B S hS (yoneda.obj V) b) →
      Nonempty (points B S hS Y) →
      ∃ H : Subfunctor Y, IsOpenSubspace B S hS H ∧ H.toFunctor.IsRepresentable ∧
        (Set.range (pointsMap B S hS H.toFunctor H.ι)).Nonempty)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (hne : Nonempty (points B S hS X)) :
    ∃ H : Subfunctor X, IsOpenSubspace B S hS H ∧ H.toFunctor.IsRepresentable ∧
      (Set.range (pointsMap B S hS H.toFunctor H.ι)).Nonempty := by
  obtain ⟨x⟩ := hne
  obtain ⟨V, b, hVaffine, hbetale, v, hv⟩ :=
    exists_affine_etale_chart_at_point B S hS X hX x
  have _hE : MorphismProperty.RespectsIso (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
      (P := (@Etale.{u} : MorphismProperty Scheme.{u}))
  have _hQ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have hbEtale : IsEtale B S hS b := isEtale_of_presheaf_etale B S hS hbetale
  have hWopen : IsOpen (Set.range (pointsMap B S hS (yoneda.obj V) b)) :=
    isOpen_range_pointsMap_of_isEtale B S hS b (isAlgebraicSpace_yoneda B S hS V) hX hbEtale
  set G := openSubspaceOfPoints B S hS X (Set.range (pointsMap B S hS (yoneda.obj V) b))
    with hGdef
  have hG : IsOpenSubspace B S hS G :=
    isOpenSubspace_openSubspaceOfPoints B S hS hX _ hWopen
  have hGrange : Set.range (pointsMap B S hS G.toFunctor G.ι) =
      Set.range (pointsMap B S hS (yoneda.obj V) b) :=
    range_pointsMap_ι_openSubspaceOfPoints B S hS _
  set b' := Subfunctor.lift b (range_le_openSubspaceOfPoints_range_pointsMap b) with hb'def
  have hb'ι : b' ≫ G.ι = b := Subfunctor.lift_ι _ _
  have hb'etale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b' :=
    MorphismProperty.presheaf_of_comp_mono _ (m := G.ι) (by rw [hb'ι]; exact hbetale)
  have hιinj : Function.Injective (pointsMap B S hS G.toFunctor G.ι) :=
    pointsMap_injective_of_mono B S hS G.ι
  have hb'surj : Function.Surjective (pointsMap B S hS (yoneda.obj V) b') := by
    intro z
    have hmem : pointsMap B S hS G.toFunctor G.ι z ∈
        Set.range (pointsMap B S hS (yoneda.obj V) b) := by
      rw [← hGrange]; exact ⟨z, rfl⟩
    obtain ⟨w, hw⟩ := hmem
    refine ⟨w, hιinj ?_⟩
    rw [← pointsMap_comp_apply, hb'ι]
    exact hw
  obtain ⟨H', hH'open, hH'rep, hH'ne⟩ := hchart G.toFunctor V b' hG.1
    (isDecentSpace_of_isOpenSubspace B S hS hX hdec hG) hVaffine hb'etale hb'surj
    ⟨pointsMap B S hS (yoneda.obj V) b' v⟩
  obtain ⟨H, -, hHopen, hHrep, hHne⟩ :=
    exists_isRepresentable_isOpenSubspace_le_of_isOpenSubspace B S hS hX hG hH'open hH'rep
      hH'ne
  exact ⟨H, hHopen, hHrep, hHne⟩

/-- Assume `hcore`: every nonempty decent algebraic space over `S` has a nonempty
representable open subspace. Then every nonempty open subspace of a decent algebraic space over
`S` contains a nonempty representable open subspace. -/
theorem exists_isRepresentable_isOpenSubspace_le_of_decentCore
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X)
    (hcore : ∀ Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u, IsAlgebraicSpace B S hS Y →
      IsDecentSpace B S hS Y → Nonempty (points B S hS Y) →
      ∃ H : Subfunctor Y, IsOpenSubspace B S hS H ∧ H.toFunctor.IsRepresentable ∧
        (Set.range (pointsMap B S hS H.toFunctor H.ι)).Nonempty)
    (G : Subfunctor X) (hG : IsOpenSubspace B S hS G)
    (hGne : (Set.range (pointsMap B S hS G.toFunctor G.ι)).Nonempty) :
    ∃ H : Subfunctor X, H ≤ G ∧ IsOpenSubspace B S hS H ∧ H.toFunctor.IsRepresentable ∧
      (Set.range (pointsMap B S hS H.toFunctor H.ι)).Nonempty := by
  obtain ⟨H', hH'open, hH'rep, hH'ne⟩ := hcore G.toFunctor hG.1
    (isDecentSpace_of_isOpenSubspace B S hS hX hdec hG)
    (Set.range_nonempty_iff_nonempty.mp hGne)
  exact exists_isRepresentable_isOpenSubspace_le_of_isOpenSubspace B S hS hX hG hH'open
    hH'rep hH'ne

/-- A decent algebraic space over `S` has a representable open subspace whose point set is
dense, as soon as every nonempty decent algebraic space over `S` has a nonempty representable
open subspace. -/
theorem exists_denseRange_isRepresentable_isOpenSubspace_of_decentCore
    (hcore : ∀ Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u, IsAlgebraicSpace B S hS Y →
      IsDecentSpace B S hS Y → Nonempty (points B S hS Y) →
      ∃ H : Subfunctor Y, IsOpenSubspace B S hS H ∧ H.toFunctor.IsRepresentable ∧
        (Set.range (pointsMap B S hS H.toFunctor H.ι)).Nonempty)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) :
    ∃ G : Subfunctor X, IsOpenSubspace B S hS G ∧ G.toFunctor.IsRepresentable ∧
      DenseRange (pointsMap B S hS G.toFunctor G.ι) :=
  exists_denseRange_isRepresentable_isOpenSubspace_of_isAlgebraicSpace B S hS hX
    (exists_isRepresentable_isOpenSubspace_le_of_decentCore B S hS hX hdec hcore)

/-- A decent algebraic space over `S` has a representable open subspace whose point set is
dense, as soon as every nonempty decent algebraic space over `S` carrying an affine étale chart
surjective on points has a nonempty representable open subspace. -/
theorem exists_denseRange_isRepresentable_isOpenSubspace_of_decentChartCore
    (hchart : ∀ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (V : BigFppfOver B S hS)
      (b : yoneda.obj V ⟶ Y), IsAlgebraicSpace B S hS Y → IsDecentSpace B S hS Y →
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf b →
      Function.Surjective (pointsMap B S hS (yoneda.obj V) b) →
      Nonempty (points B S hS Y) →
      ∃ H : Subfunctor Y, IsOpenSubspace B S hS H ∧ H.toFunctor.IsRepresentable ∧
        (Set.range (pointsMap B S hS H.toFunctor H.ι)).Nonempty)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) :
    ∃ G : Subfunctor X, IsOpenSubspace B S hS G ∧ G.toFunctor.IsRepresentable ∧
      DenseRange (pointsMap B S hS G.toFunctor G.ι) :=
  exists_denseRange_isRepresentable_isOpenSubspace_of_decentCore B S hS
    (fun _Y hY hYdec hYne =>
      exists_isRepresentable_isOpenSubspace_of_decentChartCore B S hS hchart hY hYdec hYne)
    hX hdec

end AlgebraicGeometry.Space

end
