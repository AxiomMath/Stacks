module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GroupoidOfEquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.Groupoids.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.EtaleUnramified
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffineQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.EtaleUniversallyBounded
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank
public import StacksFrontier.AlgebraicGeometry.Morphisms.Misc.FiniteCoproduct
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Diagonal
public import StacksFrontier.AlgebraicGeometry.SigmaPoints
public import StacksFrontier.AlgebraicGeometry.Size.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.SchemeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.UniversallyBoundedFibres
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.VeryReasonableImpliesReasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ZariskiLocallyQuasiSeparatedVeryReasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.EquivalenceRelations
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPointOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFinitePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleImageSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteFlatQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteFlatQuotientCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteFlatQuotientSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupActionRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Unramified
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionSurjectiveOnPointsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopologyUnique
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Reasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.ResidueDegreeBound

/-!
# Fibre powers of an étale chart of an algebraic space

Compactness and atlas facts for quasi-compact algebraic spaces and for quotients by finite
locally free equivalence relations, and the `(n + 1)`-fold fibre power of a represented map
over an algebraic space: its projections, the permutation action of the symmetric group on
the coordinates, the coordinate diagonals and the open locus of pairwise distinct coordinates.

This is the first part of
`StacksFrontier.AlgebraicGeometry.Spaces.Decent.FiniteSchemeFiltration`.

## Main results

* `AlgebraicGeometry.Space.compact_of_isQuasiCompact_yoneda`: an object of the
  site representing a quasi-compact algebraic space has compact underlying scheme.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v u₁ v₁

namespace AlgebraicGeometry.Space

theorem size_le_of_surjective_flat_locallyOfFinitePresentation
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : Flat f) (hfp : LocallyOfFinitePresentation f) (hs : Surjective f) :
    Y.size ≤ X.size := by
  let E : FppfCovering.{0} Y :=
    ⟨PUnit, fun _ ↦ X, fun _ ↦ f, fun _ ↦ hf, fun _ ↦ hfp,
      fun y ↦ by obtain ⟨x, hx⟩ := hs.surj y; exact ⟨PUnit.unit, x, hx⟩⟩
  have hE : _root_.AlgebraicGeometry.IsFpqcCovering E.X E.f := by
    refine ⟨E.flat, ?_⟩
    intro U hU
    obtain ⟨n, a, A, hA, hc⟩ := E.exists_finite_affineOpens_cover ⟨U, hU⟩
    refine ⟨n, a, A, hA, ?_, hc.symm⟩
    intro i
    rw [← hc]
    exact fun x hx ↦ Set.mem_iUnion.mpr ⟨i, hx⟩
  exact Scheme.size_le_of_fpqc_factorsThrough f E.X E.f hE
    (fun _ ↦ ⟨𝟙 X, Category.id_comp f⟩)

theorem reasonable_of_quasiSeparated
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (hqs : AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS hZ X) :
    AlgebraicGeometry.Space.IsReasonableSpace B S hS X := by
  have hzlqs :=
    AlgebraicGeometry.Space.isAbsolutelyZariskiLocallyQuasiSeparated_of_isAbsolutelyQuasiSeparated
      B S hS X hZ hX hqs
  have hvr :=
    AlgebraicGeometry.Space.isVeryReasonableSpace_of_isAbsolutelyZariskiLocallyQuasiSeparated
      B S hS hZ X hX hzlqs
  exact AlgebraicGeometry.Space.isReasonableSpace_of_isVeryReasonableSpace
    B S hS X hX hvr

theorem exists_affine_etale_atlas_of_quasiCompact
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (hqc : AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS X) :
    ∃ (U : AlgebraicGeometry.BigFppfOver B S hS) (f : yoneda.obj U ⟶ X),
      IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U) ∧
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf f ∧
      AlgebraicGeometry.Space.IsEtale B S hS f :=
  (AlgebraicGeometry.Space.isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover
    B S hS X hX).mp hqc

private theorem compactSpace_of_surjective_continuous
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [CompactSpace α] (f : α → β) (hf : Function.Surjective f)
    (hcont : Continuous f) : CompactSpace β := by
  have himage : IsCompact (Set.range f) := isCompact_range hcont
  have hrange : Set.range f = Set.univ := Set.range_eq_univ.mpr hf
  exact ⟨by rw [← hrange]; exact himage⟩

theorem compactSpace_of_finiteFlatQuotient
    {S : Scheme.{u}} {G : Stacks.Groupoids.GroupoidScheme S}
    (Q : Stacks.Groupoids.FiniteFlatQuotient G)
    (hG : CompactSpace G.objects.left) : CompactSpace Q.space.left := by
  let : CompactSpace G.objects.left := hG
  exact compactSpace_of_surjective_continuous Q.quotientMap.left.base
    Q.surjective.surj (by fun_prop)

/-- The quotient of a finite locally free equivalence relation each of whose nonempty closed
subsets contains a point with affine-contained orbit, chosen from Stacks 07S6. -/
noncomputable def finiteFlatQuotientOfAffineOrbits
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    [Stacks.Morphisms.IsFiniteLocallyFree G.source.left]
    [Stacks.Morphisms.IsFiniteLocallyFree G.target.left]
    (hrel : IsEquivalenceRelation G.target G.source)
    (horbit : ∀ Z : Set G.objects.left, IsClosed Z → Z.Nonempty →
      ∃ x ∈ Z, ∃ W : G.objects.left.Opens,
        IsAffineOpen W ∧ ∀ r : G.arrows.left,
          G.source.left.base r = x → G.target.left.base r ∈ W) :
    Stacks.Groupoids.FiniteFlatQuotient G := by
  letI := hrel
  refine (AlgebraicGeometry.Space.nonempty_finiteFlatQuotient_of_affineOrbits G ?_).some
  intro Z hZclosed hZnonempty
  obtain ⟨x, hxZ, W, hWaff, hWorbit⟩ := horbit Z hZclosed hZnonempty
  refine ⟨x, hxZ, W, hWaff, ?_⟩
  rintro _ ⟨r, hr, rfl⟩
  exact hWorbit r hr

private theorem compactAndSeparated_finiteFlatQuotient
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    [Stacks.Morphisms.IsFiniteLocallyFree G.source.left]
    [Stacks.Morphisms.IsFiniteLocallyFree G.target.left]
    (hrel : IsEquivalenceRelation G.target G.source)
    (horbit : ∀ Z : Set G.objects.left, IsClosed Z → Z.Nonempty →
      ∃ x ∈ Z, ∃ W : G.objects.left.Opens,
        IsAffineOpen W ∧ ∀ r : G.arrows.left,
          G.source.left.base r = x → G.target.left.base r ∈ W)
    (hcompact : CompactSpace G.objects.left)
    [G.objects.left.IsSeparated] :
    CompactSpace (finiteFlatQuotientOfAffineOrbits G hrel horbit).space.left ∧
      (finiteFlatQuotientOfAffineOrbits G hrel horbit).space.left.IsSeparated :=
  ⟨compactSpace_of_finiteFlatQuotient
    (finiteFlatQuotientOfAffineOrbits G hrel horbit) hcompact,
    Stacks.Groupoids.FiniteFlatQuotient.isSeparated_space
      (finiteFlatQuotientOfAffineOrbits G hrel horbit) inferInstance⟩

theorem exists_affineOpen_containing_finiteOrbit
    {U Y : Scheme.{u}}
    {G : Type*} [Group G] [Finite G] (a : G →* Aut U)
    (f : U ⟶ Y) [_root_.AlgebraicGeometry.IsSeparated f] [LocallyOfFiniteType f]
    [LocallyQuasiFinite f] [IsAffine Y]
    (Z : Set U) (hnonempty : Z.Nonempty) :
    ∃ x ∈ Z, ∃ W : U.Opens, IsAffineOpen W ∧
      ∀ g : G, ((a g).hom.base x) ∈ W := by
  obtain ⟨x, hx⟩ := hnonempty
  let orbit : Set U := Set.range (fun g : G ↦ (a g).hom.base x)
  have horbit : orbit.Finite := Set.finite_range _
  obtain ⟨W, hW, hcontains⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_containing_finite_of_locallyQuasiFinite f horbit
  refine ⟨x, hx, W, hW, ?_⟩
  intro g
  exact hcontains ⟨g, rfl⟩

private theorem exists_affineOpen_containing_groupoidOrbit
    {S Y : Scheme.{u}} (R : Stacks.Groupoids.GroupoidScheme S)
    {G : Type*} [Group G] [Finite G]
    (a : G →* Aut R.objects.left)
    (f : R.objects.left ⟶ Y) [_root_.AlgebraicGeometry.IsSeparated f] [LocallyOfFiniteType f]
    [LocallyQuasiFinite f] [IsAffine Y]
    (htarget : ∀ r : R.arrows.left, ∃ g : G,
      R.target.left.base r = (a g).hom.base (R.source.left.base r))
    (Z : Set R.objects.left) (hZ : Z.Nonempty) :
    ∃ x ∈ Z, ∃ W : R.objects.left.Opens,
      IsAffineOpen W ∧ ∀ r : R.arrows.left,
        R.source.left.base r = x → R.target.left.base r ∈ W := by
  obtain ⟨x, hx, W, hW, hcontains⟩ :=
    exists_affineOpen_containing_finiteOrbit a f Z hZ
  refine ⟨x, hx, W, hW, ?_⟩
  intro r hr
  obtain ⟨g, hg⟩ := htarget r
  rw [hg, hr]
  exact hcontains g

/-- An object of the big fppf site over `S` whose represented presheaf is a quasi-compact
algebraic space has compact underlying scheme. -/
theorem compact_of_isQuasiCompact_yoneda
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : AlgebraicGeometry.BigFppfOver B S hS)
    (hT : AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS (yoneda.obj T)) :
    CompactSpace ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T) := by
  rcases hT with ⟨U, p, hcompact, hsurj, hetale⟩
  let q := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let m : U ⟶ T := yoneda.preimage p
  have hpm : yoneda.map m = p := yoneda.map_preimage p
  have hm : Surjective (q.map m) :=
    hsurj.property (𝟙 (yoneda.obj T)) (𝟙 (yoneda.obj U)) m (by
      simpa [hpm] using (IsPullback.of_id_fst : IsPullback (𝟙 (yoneda.obj U))
        (yoneda.map m) (yoneda.map m) (𝟙 (yoneda.obj T))))
  let : CompactSpace (q.obj U) := hcompact
  let : CompactSpace (q.obj T) :=
    compactSpace_of_surjective_continuous (q.map m).base hm.surj (by fun_prop)
  infer_instance

private theorem compact_represented_pullback
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U V : AlgebraicGeometry.BigFppfOver B S hS}
    (f : yoneda.obj U ⟶ X) (g : yoneda.obj V ⟶ X)
    (hf : yoneda.relativelyRepresentable f)
    (hqc : AlgebraicGeometry.Space.IsQuasiCompact B S hS f)
    (hV : CompactSpace ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj V)) :
    CompactSpace ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (hf.pullback g)) := by
  have hp := hqc (yoneda.obj V) (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V)
    (isQuasiCompact_yoneda_of_compact B S hS V hV) g
  exact compact_of_isQuasiCompact_yoneda B S hS _
    (isQuasiCompactSpace_of_iso B S hS (hf.isPullback g).flip.isoPullback.symm hp)

/-- The `(n + 1)`-fold fibre power of a represented map, with its map to the base. -/
noncomputable def fiberPower
    {C : Type*} [Category.{u} C] {X : Cᵒᵖ ⥤ Type u} {U : C}
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f) :
    ℕ → Σ V : C, yoneda.obj V ⟶ X
  | 0 => ⟨U, f⟩
  | n + 1 =>
      let P := fiberPower f hf n
      ⟨hf.pullback P.2, hf.fst P.2 ≫ f⟩

/-- Projection from a fibre power to its oldest factor. -/
noncomputable def fiberPowerBaseProjection
    {C : Type*} [Category.{u} C] {X : Cᵒᵖ ⥤ Type u} {U : C}
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f) :
    (n : ℕ) → (fiberPower f hf n).1 ⟶ U
  | 0 => 𝟙 U
  | n + 1 => hf.snd (fiberPower f hf n).2 ≫ fiberPowerBaseProjection f hf n

theorem etale_separated_fiberPowerBaseProjection
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : AlgebraicGeometry.BigFppfOver B S hS}
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (he : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf f)
    (hs : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsSeparated.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf f)
    (n : ℕ) :
    Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
      (fiberPowerBaseProjection f hf n)) ∧
    _root_.AlgebraicGeometry.IsSeparated ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
      (fiberPowerBaseProjection f hf n)) := by
  let q := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  induction n with
  | zero =>
      change Etale (q.map (𝟙 U)) ∧ _root_.AlgebraicGeometry.IsSeparated (q.map (𝟙 U))
      rw [q.map_id]
      exact ⟨inferInstance, inferInstance⟩
  | succ n ih =>
      have : Etale (q.map (hf.snd (fiberPower f hf n).2)) :=
        he.property _ _ _ (hf.isPullback _)
      have : _root_.AlgebraicGeometry.IsSeparated (q.map (hf.snd (fiberPower f hf n).2)) :=
        hs.property _ _ _ (hf.isPullback _)
      have := ih.1
      have := ih.2
      show Etale (q.map (hf.snd (fiberPower f hf n).2 ≫ fiberPowerBaseProjection f hf n)) ∧
        _root_.AlgebraicGeometry.IsSeparated
          (q.map (hf.snd (fiberPower f hf n).2 ≫ fiberPowerBaseProjection f hf n))
      rw [q.map_comp]
      exact ⟨inferInstance, inferInstance⟩

noncomputable def fiberPowerProjection
    {C : Type*} [Category.{u} C] {X : Cᵒᵖ ⥤ Type u} {U : C}
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f) :
    (n : ℕ) → Fin (n + 1) → ((fiberPower f hf n).1 ⟶ U)
  | 0, _ => 𝟙 U
  | n + 1, i => Fin.cases (hf.fst' (fiberPower f hf n).2)
      (fun j => hf.snd (fiberPower f hf n).2 ≫ fiberPowerProjection f hf n j) i

theorem fiberPowerProjection_comp
    {C : Type*} [Category.{u} C] {X : Cᵒᵖ ⥤ Type u} {U : C}
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (n : ℕ) (i : Fin (n + 1)) :
    yoneda.map (fiberPowerProjection f hf n i) ≫ f = (fiberPower f hf n).2 := by
  induction n with
  | zero => simp [fiberPowerProjection, fiberPower]
  | succ n ih =>
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · show yoneda.map (hf.fst' (fiberPower f hf n).2) ≫ f = _
        rw [hf.map_fst']
        rfl
      · show yoneda.map (hf.snd (fiberPower f hf n).2 ≫
          fiberPowerProjection f hf n j) ≫ f = hf.fst (fiberPower f hf n).2 ≫ f
        rw [Functor.map_comp, Category.assoc, ih]
        exact (hf.w _).symm

theorem fiberPower_hom_ext
    {C : Type*} [Category.{u} C] {X : Cᵒᵖ ⥤ Type u} {U : C}
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (n : ℕ) {V : C} {a b : V ⟶ (fiberPower f hf n).1}
    (h : ∀ i, a ≫ fiberPowerProjection f hf n i =
      b ≫ fiberPowerProjection f hf n i) : a = b := by
  induction n with
  | zero =>
      have h0 := h 0
      change a ≫ 𝟙 U = b ≫ 𝟙 U at h0
      exact (Category.comp_id a).symm.trans (h0.trans (Category.comp_id b))
  | succ n ih =>
      apply hf.hom_ext'
      · exact h 0
      · apply ih
        intro i
        have hi := h i.succ
        change a ≫ (hf.snd (fiberPower f hf n).2 ≫ fiberPowerProjection f hf n i) =
          b ≫ (hf.snd (fiberPower f hf n).2 ≫ fiberPowerProjection f hf n i) at hi
        exact (Category.assoc _ _ _).trans (hi.trans (Category.assoc _ _ _).symm)

noncomputable def fiberPowerLift
    {C : Type*} [Category.{u} C] {X : Cᵒᵖ ⥤ Type u} {U V : C}
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (n : ℕ) (g : yoneda.obj V ⟶ X) (a : Fin (n + 1) → (V ⟶ U))
    (ha : ∀ i, yoneda.map (a i) ≫ f = g) :
    {l : V ⟶ (fiberPower f hf n).1 //
      yoneda.map l ≫ (fiberPower f hf n).2 = g ∧
      ∀ i, l ≫ fiberPowerProjection f hf n i = a i} := by
  induction n with
  | zero =>
      refine ⟨a 0, ha 0, ?_⟩
      intro i
      have : i = 0 := Fin.eq_zero i
      subst i
      exact Category.comp_id _
  | succ n ih =>
      let l := ih (fun i ↦ a i.succ) (fun i ↦ ha i.succ)
      let m := hf.lift' (a 0) l.1 ((ha 0).trans l.2.1.symm)
      refine ⟨m, ?_, ?_⟩
      · change yoneda.map m ≫ hf.fst (fiberPower f hf n).2 ≫ f = g
        simpa [m, Functor.relativelyRepresentable.lift', ← Category.assoc] using ha 0
      · intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · change m ≫ hf.fst' (fiberPower f hf n).2 = _
          exact hf.lift'_fst _ _ _
        · change m ≫ (hf.snd (fiberPower f hf n).2 ≫
            fiberPowerProjection f hf n j) = _
          rw [← Category.assoc, Functor.relativelyRepresentable.lift'_snd]
          exact l.2.2 j

noncomputable def fiberPowerPermute
    {C : Type*} [Category.{u} C] {X : Cᵒᵖ ⥤ Type u} {U : C}
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (n : ℕ) (σ : Equiv.Perm (Fin (n + 1))) :
    (fiberPower f hf n).1 ⟶ (fiberPower f hf n).1 :=
  (fiberPowerLift f hf n (fiberPower f hf n).2
    (fun i ↦ fiberPowerProjection f hf n (σ i))
    (fun i ↦ fiberPowerProjection_comp f hf n (σ i))).1

theorem fiberPowerPermute_projection
    {C : Type*} [Category.{u} C] {X : Cᵒᵖ ⥤ Type u} {U : C}
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (n : ℕ) (σ : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 1)) :
    fiberPowerPermute f hf n σ ≫ fiberPowerProjection f hf n i =
      fiberPowerProjection f hf n (σ i) :=
  (fiberPowerLift f hf n (fiberPower f hf n).2 _ _).2.2 i

theorem fiberPowerPermute_comp_base
    {C : Type*} [Category.{u} C] {X : Cᵒᵖ ⥤ Type u} {U : C}
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (n : ℕ) (σ : Equiv.Perm (Fin (n + 1))) :
    yoneda.map (fiberPowerPermute f hf n σ) ≫ (fiberPower f hf n).2 =
      (fiberPower f hf n).2 :=
  (fiberPowerLift f hf n (fiberPower f hf n).2 _ _).2.1

theorem fiberPowerPermute_injective
    {C : Type*} [Category.{u} C] {X : Cᵒᵖ ⥤ Type u} {U V : C}
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (n : ℕ) (a : V ⟶ (fiberPower f hf n).1)
    (ha : Function.Injective (fun i => a ≫ fiberPowerProjection f hf n i)) :
    Function.Injective (fun σ => a ≫ fiberPowerPermute f hf n σ) := by
  intro σ τ h
  apply Equiv.ext
  intro i
  apply ha
  have hi := congrArg (fun k ↦ k ≫ fiberPowerProjection f hf n i) h
  simpa only [Category.assoc, fiberPowerPermute_projection] using hi

theorem fiberPowerPermute_comp
    {C : Type*} [Category.{u} C] {X : Cᵒᵖ ⥤ Type u} {U : C}
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (n : ℕ) (σ τ : Equiv.Perm (Fin (n + 1))) :
    fiberPowerPermute f hf n σ ≫ fiberPowerPermute f hf n τ =
      fiberPowerPermute f hf n (τ.trans σ) := by
  apply fiberPower_hom_ext f hf n
  intro i
  simp [Category.assoc, fiberPowerPermute_projection]

private noncomputable def fiberPowerPermutationIso
    {C : Type*} [Category.{u} C] {X : Cᵒᵖ ⥤ Type u} {U : C}
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (n : ℕ) (σ : Equiv.Perm (Fin (n + 1))) :
    (fiberPower f hf n).1 ≅ (fiberPower f hf n).1 where
  hom := fiberPowerPermute f hf n σ
  inv := fiberPowerPermute f hf n σ.symm
  hom_inv_id := by
    apply fiberPower_hom_ext f hf n
    intro i
    simp [Category.assoc, fiberPowerPermute_projection]
  inv_hom_id := by
    apply fiberPower_hom_ext f hf n
    intro i
    simp [Category.assoc, fiberPowerPermute_projection]

private theorem isPullback_diagonal_of_isLimit_fork
    {C : Type*} [Category* C] {E A U X : C}
    (p q : A ⟶ U) (f : U ⟶ X) [HasPullback f f]
    (hpq : p ≫ f = q ≫ f) (e : E ⟶ A) (he : e ≫ p = e ≫ q)
    (hE : IsLimit (Fork.ofι e he)) :
    IsPullback (e ≫ p) e (pullback.diagonal f) (pullback.lift p q hpq) := by
  have hw : (e ≫ p) ≫ pullback.diagonal f = e ≫ pullback.lift p q hpq := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id, pullback.lift_fst]
    · simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id, pullback.lift_snd]
      exact he
  have hfirst (s : PullbackCone (pullback.diagonal f) (pullback.lift p q hpq)) :
      s.snd ≫ p = s.fst := by
    simpa only [Category.assoc, pullback.diagonal_fst, Category.comp_id,
      pullback.lift_fst] using (congrArg (fun k ↦ k ≫ pullback.fst f f) s.condition).symm
  have hsecond (s : PullbackCone (pullback.diagonal f) (pullback.lift p q hpq)) :
      s.snd ≫ q = s.fst := by
    simpa only [Category.assoc, pullback.diagonal_snd, Category.comp_id,
      pullback.lift_snd] using (congrArg (fun k ↦ k ≫ pullback.snd f f) s.condition).symm
  have hs (s : PullbackCone (pullback.diagonal f) (pullback.lift p q hpq)) :
      s.snd ≫ p = s.snd ≫ q := (hfirst s).trans (hsecond s).symm
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw
    (fun s ↦ Fork.IsLimit.lift hE s.snd (hs s)) ?_ ?_ ?_)
  · intro s
    rw [← Category.assoc]
    show (Fork.IsLimit.lift hE s.snd (hs s) ≫ (Fork.ofι e he).ι) ≫ p = s.fst
    rw [Fork.IsLimit.lift_ι']
    exact hfirst s
  · intro s
    exact Fork.IsLimit.lift_ι' hE _ _
  · intro s m _ hm
    exact Fork.IsLimit.hom_ext hE (hm.trans (Fork.IsLimit.lift_ι' hE _ _).symm)

private theorem property_equalizer_of_diagonal
    {C : Type*} [Category.{u} C] (P : MorphismProperty C)
    {X : Cᵒᵖ ⥤ Type u} {U A : C} (f : yoneda.obj U ⟶ X)
    (p q : A ⟶ U) [HasEqualizer p q]
    (hpq : yoneda.map p ≫ f = yoneda.map q ≫ f)
    (hdiag : P.presheaf (pullback.diagonal f)) : P (equalizer.ι p q) := by
  let e := equalizer.ι p q
  have he : yoneda.map e ≫ yoneda.map p = yoneda.map e ≫ yoneda.map q :=
    (yoneda.map_comp e p).symm.trans
      ((congrArg yoneda.map (equalizer.condition p q)).trans
        (yoneda.map_comp e q))
  have hE : IsLimit (Fork.ofι (yoneda.map e) he) :=
    isLimitOfHasEqualizerOfPreservesLimit yoneda p q
  exact hdiag.property (pullback.lift (yoneda.map p) (yoneda.map q) hpq)
    (yoneda.map e ≫ yoneda.map p) e
    (isPullback_diagonal_of_isLimit_fork (yoneda.map p) (yoneda.map q) f hpq
      (yoneda.map e) he hE)

private theorem compact_fiberPower
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : AlgebraicGeometry.BigFppfOver B S hS}
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (hqc : AlgebraicGeometry.Space.IsQuasiCompact B S hS f)
    (hU : CompactSpace ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U)) (n : ℕ) :
    CompactSpace ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
      (fiberPower f hf n).1) := by
  induction n with
  | zero => exact hU
  | succ n ih =>
      exact compact_represented_pullback B S hS f (fiberPower f hf n).2 hf hqc ih

noncomputable def fiberPowerPair
    {C : Type*} [Category.{u} C] {X : Cᵒᵖ ⥤ Type u} {U : C}
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (n : ℕ) (i j : Fin (n + 1)) : yoneda.obj (fiberPower f hf n).1 ⟶ pullback f f :=
  pullback.lift (yoneda.map (fiberPowerProjection f hf n i))
    (yoneda.map (fiberPowerProjection f hf n j))
    ((fiberPowerProjection_comp f hf n i).trans (fiberPowerProjection_comp f hf n j).symm)

/-- The first coordinate of the pair map of a fibre power is the first of the two
projections. -/
theorem fiberPowerPair_fst
    {C : Type*} [Category.{u} C] {X : Cᵒᵖ ⥤ Type u} {U : C}
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (n : ℕ) (i j : Fin (n + 1)) :
    fiberPowerPair f hf n i j ≫ pullback.fst f f =
      yoneda.map (fiberPowerProjection f hf n i) :=
  pullback.lift_fst _ _ _

/-- The second coordinate of the pair map of a fibre power is the second of the two
projections. -/
theorem fiberPowerPair_snd
    {C : Type*} [Category.{u} C] {X : Cᵒᵖ ⥤ Type u} {U : C}
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (n : ℕ) (i j : Fin (n + 1)) :
    fiberPowerPair f hf n i j ≫ pullback.snd f f =
      yoneda.map (fiberPowerProjection f hf n j) :=
  pullback.lift_snd _ _ _

private theorem fiberPowerPermute_pair
    {C : Type*} [Category.{u} C] {X : Cᵒᵖ ⥤ Type u} {U : C}
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (n : ℕ) (σ : Equiv.Perm (Fin (n + 1))) (i j : Fin (n + 1)) :
    yoneda.map (fiberPowerPermute f hf n σ) ≫ fiberPowerPair f hf n i j =
      fiberPowerPair f hf n (σ i) (σ j) := by
  apply pullback.hom_ext <;>
    simp only [fiberPowerPair, Category.assoc, pullback.lift_fst, pullback.lift_snd,
      ← Functor.map_comp, fiberPowerPermute_projection]

private noncomputable def coordinateDiagonalPermute
    {C : Type*} [Category.{u} C] {X : Cᵒᵖ ⥤ Type u} {U : C}
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (hd : yoneda.relativelyRepresentable (pullback.diagonal f))
    (n : ℕ) (σ : Equiv.Perm (Fin (n + 1))) (i j : Fin (n + 1)) :
    hd.pullback (fiberPowerPair f hf n (σ i) (σ j)) ⟶
      hd.pullback (fiberPowerPair f hf n i j) :=
  hd.lift (hd.fst (fiberPowerPair f hf n (σ i) (σ j)))
    (hd.snd (fiberPowerPair f hf n (σ i) (σ j)) ≫ fiberPowerPermute f hf n σ)
    (by rw [Functor.map_comp, Category.assoc, fiberPowerPermute_pair]; exact hd.w _)

private theorem coordinateDiagonalPermute_snd
    {C : Type*} [Category.{u} C] {X : Cᵒᵖ ⥤ Type u} {U : C}
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (hd : yoneda.relativelyRepresentable (pullback.diagonal f))
    (n : ℕ) (σ : Equiv.Perm (Fin (n + 1))) (i j : Fin (n + 1)) :
    coordinateDiagonalPermute f hf hd n σ i j ≫ hd.snd (fiberPowerPair f hf n i j) =
      hd.snd (fiberPowerPair f hf n (σ i) (σ j)) ≫ fiberPowerPermute f hf n σ :=
  hd.lift_snd _ _ _

theorem isClopen_coordinateDiagonal
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : AlgebraicGeometry.BigFppfOver B S hS}
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (ho : AlgebraicGeometry.Space.IsOpenImmersion B S hS (pullback.diagonal f))
    (hc : AlgebraicGeometry.Space.IsClosedImmersion B S hS (pullback.diagonal f))
    (n : ℕ) (i j : Fin (n + 1)) :
    IsClopen (Set.range ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
      (ho.rep.snd (fiberPowerPair f hf n i j))).base) := by
  let k := fiberPowerPair f hf n i j
  let d := (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (ho.rep.snd k)
  have : AlgebraicGeometry.IsOpenImmersion d := ho.property_snd k
  have : AlgebraicGeometry.IsClosedImmersion d :=
    hc.property k (ho.rep.fst k) (ho.rep.snd k) (ho.rep.isPullback k)
  exact ⟨d.isClosedEmbedding.isClosed_range, d.isOpenEmbedding.isOpen_range⟩

private theorem preimage_range_represented_pullback
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : X ⟶ Y} (hf : yoneda.relativelyRepresentable f)
    {U V : AlgebraicGeometry.BigFppfOver B S hS}
    (g : yoneda.obj U ⟶ Y) (g' : yoneda.obj V ⟶ Y)
    (k : V ⟶ U) (hk : yoneda.map k ≫ g = g') :
    ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map k) ⁻¹'
      Set.range ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (hf.snd g)) =
        Set.range ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (hf.snd g')) := by
  let m := hf.lift (hf.fst g') (hf.snd g' ≫ k) (by
    rw [CategoryTheory.Functor.map_comp, Category.assoc, hk]
    exact hf.w g')
  have hm₁ : yoneda.map m ≫ hf.fst g = hf.fst g' := hf.lift_fst _ _ _
  have hm₂ : m ≫ hf.snd g = hf.snd g' ≫ k := hf.lift_snd _ _ _
  have hp : IsPullback (yoneda.map m) (yoneda.map (hf.snd g'))
      (yoneda.map (hf.snd g)) (yoneda.map k) := by
    apply IsPullback.of_right (t := hf.isPullback g)
    · rw [hm₁, hk]
      exact hf.isPullback g'
    · simpa only [← CategoryTheory.Functor.map_comp] using congrArg yoneda.map hm₂
  have hp' : IsPullback m (hf.snd g') (hf.snd g) k :=
    hp.of_map yoneda hm₂
  exact (AlgebraicGeometry.range_snd_of_isPullback
    (hp'.map (AlgebraicGeometry.BigFppfOver.toScheme B S hS))).symm

private theorem fiberPower_snd_pair
    {C : Type*} [Category.{u} C] {X : Cᵒᵖ ⥤ Type u} {U : C}
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (n : ℕ) (i j : Fin (n + 1)) :
    yoneda.map (hf.snd (fiberPower f hf n).2) ≫ fiberPowerPair f hf n i j =
      fiberPowerPair f hf (n + 1) i.succ j.succ := by
  apply pullback.hom_ext
  · rw [Category.assoc, fiberPowerPair_fst]
    exact (yoneda.map_comp _ _).symm.trans
      (fiberPowerPair_fst f hf (n + 1) i.succ j.succ).symm
  · rw [Category.assoc, fiberPowerPair_snd]
    exact (yoneda.map_comp _ _).symm.trans
      (fiberPowerPair_snd f hf (n + 1) i.succ j.succ).symm

/-- The complement of the coordinate diagonals in a fibre power. -/
noncomputable def distinctFiberPowerLocus
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : AlgebraicGeometry.BigFppfOver B S hS}
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (ho : AlgebraicGeometry.Space.IsOpenImmersion B S hS (pullback.diagonal f))
    (hc : AlgebraicGeometry.Space.IsClosedImmersion B S hS (pullback.diagonal f)) (n : ℕ) :
    ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (fiberPower f hf n).1).Opens :=
  ⟨(⋃ ij : {ij : Fin (n + 1) × Fin (n + 1) // ij.1 ≠ ij.2},
      Set.range ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
        (ho.rep.snd (fiberPowerPair f hf n ij.1.1 ij.1.2))).base)ᶜ,
    (isClopen_iUnion_of_finite
      (fun ij : {ij : Fin (n + 1) × Fin (n + 1) // ij.1 ≠ ij.2} ↦
      isClopen_coordinateDiagonal B S hS f hf ho hc n ij.1.1 ij.1.2)).compl.isOpen⟩

theorem mapsTo_distinctFiberPowerLocus_snd
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : AlgebraicGeometry.BigFppfOver B S hS}
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (ho : AlgebraicGeometry.Space.IsOpenImmersion B S hS (pullback.diagonal f))
    (hc : AlgebraicGeometry.Space.IsClosedImmersion B S hS (pullback.diagonal f)) (n : ℕ) :
    Set.MapsTo ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
      (hf.snd (fiberPower f hf n).2))
      (distinctFiberPowerLocus B S hS f hf ho hc (n + 1)).1
      (distinctFiberPowerLocus B S hS f hf ho hc n).1 := by
  intro x hx hbad
  obtain ⟨⟨⟨i, j⟩, hij⟩, hbad⟩ := Set.mem_iUnion.mp hbad
  apply hx
  refine Set.mem_iUnion.mpr ⟨⟨(i.succ, j.succ), fun h ↦ hij (Fin.succ_injective _ h)⟩, ?_⟩
  have heq := preimage_range_represented_pullback B S hS ho.rep
    (fiberPowerPair f hf n i j) (fiberPowerPair f hf (n + 1) i.succ j.succ)
    (hf.snd (fiberPower f hf n).2) (fiberPower_snd_pair f hf n i j)
  exact heq ▸ hbad

theorem compact_distinctFiberPowerLocus
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : AlgebraicGeometry.BigFppfOver B S hS}
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (hqc : AlgebraicGeometry.Space.IsQuasiCompact B S hS f)
    (hU : CompactSpace ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U))
    (ho : AlgebraicGeometry.Space.IsOpenImmersion B S hS (pullback.diagonal f))
    (hc : AlgebraicGeometry.Space.IsClosedImmersion B S hS (pullback.diagonal f)) (n : ℕ) :
    CompactSpace (distinctFiberPowerLocus B S hS f hf ho hc n).toScheme := by
  have := compact_fiberPower B S hS f hf hqc hU n
  apply isCompact_iff_compactSpace.mp
  exact (isClopen_iUnion_of_finite
    (fun ij : {ij : Fin (n + 1) × Fin (n + 1) // ij.1 ≠ ij.2} ↦
      isClopen_coordinateDiagonal B S hS f hf ho hc n ij.1.1 ij.1.2)).compl.isClosed.isCompact

private theorem mapsTo_coordinateDiagonal
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : AlgebraicGeometry.BigFppfOver B S hS}
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (hd : yoneda.relativelyRepresentable (pullback.diagonal f))
    (n : ℕ) (σ : Equiv.Perm (Fin (n + 1))) (i j : Fin (n + 1)) :
    Set.MapsTo
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (fiberPowerPermute f hf n σ))
      (Set.range ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
        (hd.snd (fiberPowerPair f hf n (σ i) (σ j)))))
      (Set.range ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
        (hd.snd (fiberPowerPair f hf n i j)))) := by
  rintro _ ⟨y, rfl⟩
  refine ⟨((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
    (coordinateDiagonalPermute f hf hd n σ i j)) y, ?_⟩
  have h := congrArg ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map)
    (coordinateDiagonalPermute_snd f hf hd n σ i j)
  simpa only [Functor.map_comp, Scheme.Hom.comp_apply] using
    congrArg (fun k ↦ k y) h

private theorem mapsTo_coordinateDiagonals
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : AlgebraicGeometry.BigFppfOver B S hS}
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (hd : yoneda.relativelyRepresentable (pullback.diagonal f))
    (n : ℕ) (σ : Equiv.Perm (Fin (n + 1))) :
    Set.MapsTo
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (fiberPowerPermute f hf n σ))
      (⋃ ij : {ij : Fin (n + 1) × Fin (n + 1) // ij.1 ≠ ij.2},
        Set.range ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
          (hd.snd (fiberPowerPair f hf n ij.1.1 ij.1.2))))
      (⋃ ij : {ij : Fin (n + 1) × Fin (n + 1) // ij.1 ≠ ij.2},
        Set.range ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
          (hd.snd (fiberPowerPair f hf n ij.1.1 ij.1.2)))) := by
  intro x hx
  obtain ⟨⟨⟨i, j⟩, hij⟩, hx⟩ := Set.mem_iUnion.mp hx
  refine Set.mem_iUnion.mpr ⟨⟨(σ.symm i, σ.symm j),
    fun h ↦ hij (σ.symm.injective h)⟩, ?_⟩
  apply mapsTo_coordinateDiagonal B S hS f hf hd n σ (σ.symm i) (σ.symm j)
  exact (congrArg₂ (fun a b ↦ x ∈ Set.range
    ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
      (hd.snd (fiberPowerPair f hf n a b))))
    (σ.apply_symm_apply i) (σ.apply_symm_apply j)).mpr hx

theorem mapsTo_distinctFiberPowerLocus
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : AlgebraicGeometry.BigFppfOver B S hS}
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (ho : AlgebraicGeometry.Space.IsOpenImmersion B S hS (pullback.diagonal f))
    (hc : AlgebraicGeometry.Space.IsClosedImmersion B S hS (pullback.diagonal f))
    (n : ℕ) (σ : Equiv.Perm (Fin (n + 1))) :
    Set.MapsTo
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (fiberPowerPermute f hf n σ))
      (distinctFiberPowerLocus B S hS f hf ho hc n)
      (distinctFiberPowerLocus B S hS f hf ho hc n) := by
  intro x hx hσx
  have h := mapsTo_coordinateDiagonals B S hS f hf ho.rep n σ.symm hσx
  have he := congrArg ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map)
    (fiberPowerPermutationIso f hf n σ).hom_inv_id
  have hx' : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
      (fiberPowerPermute f hf n σ.symm))
      (((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (fiberPowerPermute f hf n σ)) x) =
      x := by
    dsimp only [fiberPowerPermutationIso] at he
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at he
    exact congrArg (fun k ↦ k.base x) he
  exact hx (hx' ▸ h)

end AlgebraicGeometry.Space

end
