module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.FibreOverFieldPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PropertyGammaPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.QuasiSeparatedVeryReasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Sober
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.VeryReasonableImpliesReasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralAlteration
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace

/-!
# An alteration inside a proper surjection onto an integral algebraic space

A proper surjective morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` whose target
is integral restricts to an alteration on an integral closed subspace of its source.

## Main results

* `AlgebraicGeometry.Space.exists_isClosedSubspace_isAlteration` is **Stacks 0DMN**: a proper
  surjective morphism onto an integral algebraic space contains an alteration, carried by an
  integral closed subspace of the source.

## Implementation notes

The closed subspace is the reduced closed subspace of Stacks 03IQ supported on the closure of
a closed point of the fibre of `f` over the generic point `η` of `|Y|`; it is produced as data
by `AlgebraicGeometry.Space.reducedClosedSubspace`, so no witness is chosen out of an
existence statement. The generic point exists because `|Y|` is irreducible and, `Y` being
decent, quasi-sober by Stacks 03K6.

The closed point is found in the set-theoretic fibre `|f|^{-1}({η})` viewed as a subspace of
`|X|`, rather than on the fibre product: by Stacks 0AC8 the two are homeomorphic, and the
subspace form is where the closed point is used, namely to identify the fibre of the restricted
morphism over `η`. That fibre is quasi-compact because `f` is, and Kolmogorov because `|X|` is:
the source of a proper, hence separated, morphism with decent target is decent by Stacks 0ABY,
so Stacks 03K6 applies to `|X|` as well.

Properness of the restriction is Stacks 04XZ and Stacks 04XY, and dominance holds because `η`
is in its image. That the restriction is an alteration is then Stacks 0ADB, whose hypothesis is
quasi-finiteness at the generic point of the source; that in turn is condition (5) of
Stacks 0AD5, the fibre over `η` consisting of that generic point alone.

## References

* [Stacks Project, Tag 0DMN](https://stacks.math.columbia.edu/tag/0DMN)
* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
* [Stacks Project, Tag 03K6](https://stacks.math.columbia.edu/tag/03K6)
* [Stacks Project, Tag 0AC8](https://stacks.math.columbia.edu/tag/0AC8)
* [Stacks Project, Tag 0ABY](https://stacks.math.columbia.edu/tag/0ABY)
* [Stacks Project, Tag 0AD5](https://stacks.math.columbia.edu/tag/0AD5)
* [Stacks Project, Tag 0ADB](https://stacks.math.columbia.edu/tag/0ADB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/-- A point of a topological space is a generic point of the whole space as soon as some
embedding of that space carries it to a point whose closure is the entire range. -/
private theorem isGenericPoint_univ_of_isEmbedding {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {g : α → β} (hg : Topology.IsEmbedding g) {a : α}
    (h : Set.range g = closure ({g a} : Set β)) :
    IsGenericPoint a (Set.univ : Set α) := by
  rw [isGenericPoint_def, hg.closure_eq_preimage_closure_image, Set.image_singleton, ← h]
  exact Set.eq_univ_of_forall fun z ↦ Set.mem_range_self z

/-- If the singleton of a point `w` of a subspace `A` is closed in `A`, then `w` is the only
point of `A` lying in the closure of `{w}` in the ambient space. -/
private theorem eq_of_mem_closure_of_isClosed_singleton {α : Type*} [TopologicalSpace α]
    {A : Set α} {w : A} (hw : IsClosed ({w} : Set A)) {a : α} (haA : a ∈ A)
    (ha : a ∈ closure ({(w : α)} : Set α)) : a = (w : α) := by
  have h : (⟨a, haA⟩ : A) ∈ ({w} : Set A) := by
    rw [← hw.closure_eq, Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,
      Set.image_singleton]
    exact ha
  exact congrArg Subtype.val (Set.mem_singleton_iff.mp h)

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The reduced closed subspace supported on the closure of a point `w` of the set-theoretic
fibre of `f` over a generic point `η` of `|Y|` which is closed in that fibre is integral, and
`f` restricts to an alteration on it. -/
private theorem isIntegralSpace_and_isAlteration_of_isClosed_singleton_fibre
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hXdec : IsDecentSpace B S hS X) (hYint : IsIntegralSpace B S hS Y) (f : X ⟶ Y)
    (hp : IsProper B S hS f) {η : points B S hS Y}
    (hηgen : IsGenericPoint η (Set.univ : Set (points B S hS Y)))
    {w : ↥(pointsMap B S hS X f ⁻¹' {η})}
    (hw : IsClosed ({w} : Set ↥(pointsMap B S hS X f ⁻¹' {η})))
    (Z : Subfunctor X) (hZalg : IsAlgebraicSpace B S hS Z.toFunctor)
    (hZci : IsClosedImmersion B S hS Z.ι)
    (hZrange : Set.range (pointsMap B S hS Z.toFunctor Z.ι) =
      closure ({(w : points B S hS X)} : Set (points B S hS X)))
    (hZred : HasEtaleLocalProperty B S hS Z.toFunctor (fun W : Scheme.{u} => IsReduced W)) :
    IsIntegralSpace B S hS Z.toFunctor ∧ IsAlteration B S hS (Z.ι ≫ f) := by
  have hZemb : Topology.IsEmbedding (pointsMap B S hS Z.toFunctor Z.ι) :=
    isEmbedding_pointsMap_of_isImmersion B S hS hX Z.ι
      (isImmersion_of_isClosedImmersion B S hS hZci)
  have hwrange : (w : points B S hS X) ∈ Set.range (pointsMap B S hS Z.toFunctor Z.ι) := by
    rw [hZrange]
    exact subset_closure rfl
  obtain ⟨z, hz⟩ := hwrange
  have hzgen : IsGenericPoint z (Set.univ : Set (points B S hS Z.toFunctor)) :=
    isGenericPoint_univ_of_isEmbedding hZemb (by rw [hZrange, hz])
  have hZint : IsIntegralSpace B S hS Z.toFunctor :=
    ⟨hZred, isDecentSpace_of_isClosedSubspace B S hS hXdec ⟨hZalg, hZci⟩,
      (irreducibleSpace_def _).2 hzgen.isIrreducible⟩
  have hφproper : IsProper B S hS (Z.ι ≫ f) :=
    isProper_comp B S hS hZalg hX hY Z.ι f
      (isProper_of_isClosedImmersion B S hS hZalg hX Z.ι hZci) hp
  have hwfib : pointsMap B S hS X f (w : points B S hS X) = η :=
    Set.mem_singleton_iff.mp (Set.mem_preimage.mp w.2)
  have hφz : pointsMap B S hS Z.toFunctor (Z.ι ≫ f) z = η := by
    rw [pointsMap_comp_apply, hz, hwfib]
  have hφdom : IsDominant B S hS (Z.ι ≫ f) := by
    have hmem : η ∈ Set.range (pointsMap B S hS Z.toFunctor (Z.ι ≫ f)) := ⟨z, hφz⟩
    have h : closure ({η} : Set (points B S hS Y)) ⊆
        closure (Set.range (pointsMap B S hS Z.toFunctor (Z.ι ≫ f))) :=
      closure_mono (Set.singleton_subset_iff.2 hmem)
    rw [isGenericPoint_def.mp hηgen] at h
    exact fun y ↦ h (Set.mem_univ y)
  have hfibre : ∀ z' : points B S hS Z.toFunctor,
      pointsMap B S hS Z.toFunctor (Z.ι ≫ f) z' = η → z' = z := by
    intro z' hz'
    rw [pointsMap_comp_apply] at hz'
    have hclo : pointsMap B S hS Z.toFunctor Z.ι z' ∈
        closure ({(w : points B S hS X)} : Set (points B S hS X)) := by
      rw [← hZrange]
      exact Set.mem_range_self z'
    exact hZemb.injective ((eq_of_mem_closure_of_isClosed_singleton hw
      (Set.mem_preimage.mpr (Set.mem_singleton_iff.mpr hz')) hclo).trans hz.symm)
  refine ⟨hZint, (isAlteration_iff_isQuasiFiniteAt B S hS hZalg hY hZint hYint (Z.ι ≫ f)
    hφproper hφdom hzgen hηgen).2 ?_⟩
  exact (isQuasiFiniteAt_iff_forall_eq_of_pointsMap_eq B S hS hZalg hY hYint (Z.ι ≫ f)
    hφproper.2.1.1 hφdom hzgen hηgen).2 hfibre

/-- Let `f : X ⟶ Y` be a proper surjective morphism of algebraic spaces over a scheme `S` with
`Y` integral. Then `f` restricts to an alteration on some integral closed subspace of `X`. -/
@[stacks 0DMN]
theorem exists_isClosedSubspace_isAlteration (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hYint : IsIntegralSpace B S hS Y) (f : X ⟶ Y)
    (hp : IsProper B S hS f) (hsurj : IsSurjective B S hS f) :
    ∃ Z : Subfunctor X, IsClosedSubspace B S hS Z ∧
      IsIntegralSpace B S hS Z.toFunctor ∧ IsAlteration B S hS (Z.ι ≫ f) := by
  have hYdec : IsDecentSpace B S hS Y := hYint.isDecentSpace
  have hXdec : IsDecentSpace B S hS X :=
    isDecentSpace_of_isDecent B S hS hX hY f hYdec
      (isDecent_of_isReasonable B S hS hX hY f
        (isReasonable_of_isVeryReasonable B S hS hX hY
          (isVeryReasonable_of_isQuasiSeparated B S hS hX hY
            (isQuasiSeparated_of_isSeparated B S hS hp.1))))
  have hXt0 : T0Space (points B S hS X) := t0Space_points_of_isDecentSpace B S hS hX hXdec
  have hYqs : QuasiSober (points B S hS Y) :=
    quasiSober_points_of_isDecentSpace B S hS hY hYdec
  have hYirr : IrreducibleSpace (points B S hS Y) := hYint.irreducibleSpace
  obtain ⟨η, hηgen⟩ :=
    hYqs.sober (IrreducibleSpace.isIrreducible_univ (points B S hS Y)) isClosed_univ
  obtain ⟨p, hpη, hpmono, hpqc⟩ := hYdec η
  subst hpη
  have hKalg : IsAlgebraicSpace B S hS (yoneda.obj p.siteObject) :=
    isAlgebraicSpace_yoneda B S hS _
  have hKsub : Subsingleton (points B S hS (yoneda.obj p.siteObject)) :=
    subsingleton_points_yoneda_siteObject B S hS p
  have hFalg : IsAlgebraicSpace B S hS (pullback f (fieldMorphism B S hS Y p)) :=
    isAlgebraicSpace_pullback B S hS f (fieldMorphism B S hS Y p) hX hKalg hY
  have hFcompact : CompactSpace (points B S hS (pullback f (fieldMorphism B S hS Y p))) := by
    refine ⟨?_⟩
    have h := isQuasiCompactMap_pointsMap B S hS hFalg hKalg
      (pullback.snd f (fieldMorphism B S hS Y p))
      (isQuasiCompact_of_isPullback B S hS (IsPullback.of_hasPullback _ _) hp.2.1.2)
      isOpen_univ Set.subsingleton_univ.isCompact
    rwa [Set.preimage_univ] at h
  have hfibCompact : CompactSpace ↥(pointsMap B S hS X f ⁻¹' {p.class B S hS Y}) :=
    (fibreHomeomorph B S hS hX hY f p hpmono hpqc).compactSpace
  obtain ⟨x, hx⟩ := hsurj (p.class B S hS Y)
  have hfibne : Nonempty ↥(pointsMap B S hS X f ⁻¹' {p.class B S hS Y}) := ⟨⟨x, hx⟩⟩
  obtain ⟨w, -, hwclosed⟩ := isClosed_univ.exists_closed_singleton
    (Set.univ_nonempty (α := ↥(pointsMap B S hS X f ⁻¹' {p.class B S hS Y})))
  have hTclosed : IsClosed (closure ({(w : points B S hS X)} : Set (points B S hS X))) :=
    isClosed_closure
  obtain ⟨hZalg, hZci⟩ :
      IsClosedSubspace B S hS (reducedClosedSubspace B S hS X hX _ hTclosed) :=
    isClosedSubspace_reducedClosedSubspace B S hS X hX _ hTclosed
  exact ⟨reducedClosedSubspace B S hS X hX _ hTclosed, ⟨hZalg, hZci⟩,
    isIntegralSpace_and_isAlteration_of_isClosed_singleton_fibre B S hS hX hY hXdec hYint f hp
      hηgen hwclosed _ hZalg hZci
      (range_pointsMap_ι_reducedClosedSubspace B S hS X hX _ hTclosed)
      (hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS X hX _ hTclosed)⟩

end AlgebraicGeometry.Space

end
