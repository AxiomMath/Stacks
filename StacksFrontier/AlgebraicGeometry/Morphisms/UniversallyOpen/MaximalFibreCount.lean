module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcAffine
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.ConnectedComponents
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversallyOpen.FibreCountLowerBound
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.GeometricFibreCount
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Coverings

/-!
# The locus where the number of geometric components of the fibres is maximal

For a separated, locally quasi-finite and universally open morphism whose geometric fibre count
attains a finite maximum `d`, the locus where the count equals `d` is open and the morphism is
finite over it.

## Main results

* `AlgebraicGeometry.isOpen_geometricIrreducibleComponentCount_maxLocus` is openness of the
  maximal locus.
* `AlgebraicGeometry.isFinite_restrict_geometricIrreducibleComponentCount_maxLocus` is finiteness
  of the morphism over that locus.

## Implementation notes

Openness is immediate from lower semicontinuity of the count. For finiteness, restrict to the
maximal locus, where the count is constant equal to `d`. Over an étale neighbourhood of a point
the fibre splits into finite open-and-closed pieces together with a residual piece; the union `V`
of the finite pieces is finite over the neighbourhood and contains the whole distinguished fibre,
so the count of the composite `V ⟶ U` already equals `d` there. The locus where that happens is
open by lower semicontinuity again, and over it the base change of the morphism is finite because
the source of the base change is covered by `V`. These étale morphisms form an étale covering of
the maximal locus, and finiteness is local at the target for the fpqc topology.

The geometric fibre count is compared with the geometric connected-component count, which is the
function known to be compatible with arbitrary base change; the two agree for locally
quasi-finite morphisms.

## References

* [Stacks Project, Tag 0F37](https://stacks.math.columbia.edu/tag/0F37)
-/

public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

universe u

/-- The geometric fibre counts of `f` and `i ≫ f` at `y` are the cardinalities of the pullbacks of
`f` and of `i` along the geometric point of `y`. -/
private theorem geometricIrreducibleComponentCount_eq_card_pullback
    {V X Y : Scheme.{u}} (i : V ⟶ X) (f : X ⟶ Y) [IsOpenImmersion i] [LocallyQuasiFinite f]
    (y : Y) :
    let k := Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y)
      (SeparableClosure (Y.residueField y)))) ≫ Y.fromSpecResidueField y
    let p := pullback.fst f k
    geometricIrreducibleComponentCount f y = ENat.card (pullback f k : Scheme) ∧
      geometricIrreducibleComponentCount (i ≫ f) y = ENat.card (pullback i p : Scheme) := by
  intro k p
  exact ⟨geometricIrreducibleComponentCount_eq_card_of_isPullback f y _ (pullback.snd f k)
      (IsPullback.of_hasPullback f k),
    geometricIrreducibleComponentCount_eq_card_of_isPullback (i ≫ f) y (pullback.fst i _)
      (pullback.snd i _ ≫ pullback.snd f k)
      ((IsPullback.of_hasPullback i _).paste_vert (IsPullback.of_hasPullback f k))⟩

/-- Restricting to an open subscheme leaves the geometric fibre count at a point unchanged
exactly when the open contains the whole fibre. -/
private theorem geometricIrreducibleComponentCount_comp_eq_iff
    {V X Y : Scheme.{u}} (i : V ⟶ X) (f : X ⟶ Y) [IsOpenImmersion i] [LocallyQuasiFinite f]
    (y : Y) (hfinite : geometricIrreducibleComponentCount f y ≠ ⊤) :
    geometricIrreducibleComponentCount (i ≫ f) y = geometricIrreducibleComponentCount f y ↔
      f ⁻¹' {y} ⊆ Set.range i := by
  classical
  obtain ⟨hc, hd⟩ := geometricIrreducibleComponentCount_eq_card_pullback i f y
  let k := Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y)
    (SeparableClosure (Y.residueField y)))) ≫ Y.fromSpecResidueField y
  let Z := pullback f k
  let p : Z ⟶ X := pullback.fst f k
  let W := pullback i p
  let j : W ⟶ Z := pullback.snd i p
  have : Finite Z := ENat.card_lt_top.mp (lt_top_iff_ne_top.mpr (hc ▸ hfinite))
  have : IsOpenImmersion j := inferInstanceAs (IsOpenImmersion (pullback.snd i p))
  have hj : Function.Injective j := j.isOpenEmbedding.injective
  have : Finite W := Finite.of_injective j hj
  have hk : Set.range k = {y} := by
    simp only [k, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    rw [Set.range_eq_univ.mpr (Scheme.Hom.surjective _), Set.image_univ,
      Scheme.range_fromSpecResidueField]
  have hp : Set.range p = f ⁻¹' {y} := by
    show Set.range (pullback.fst f k) = _
    rw [Scheme.Pullback.range_fst, hk]
  have hr : Set.range j = p ⁻¹' Set.range i := Scheme.Pullback.range_snd i p
  rw [hc, hd]
  constructor
  · intro heq
    have hjS : Function.Surjective j := by
      let : Fintype Z := Fintype.ofFinite _
      let : Fintype W := Fintype.ofFinite _
      have heq' : Fintype.card W = Fintype.card Z := by
        simpa only [ENat.card_eq_coe_fintype_card, Nat.cast_inj] using heq
      exact ((Fintype.bijective_iff_injective_and_card j).mpr ⟨hj, heq'⟩).2
    rw [← hp]
    rintro x ⟨z, rfl⟩
    have hz : z ∈ Set.range j := hjS z
    rwa [hr] at hz
  · intro h
    have hjS : Function.Surjective j := by
      intro z
      have hz : z ∈ p ⁻¹' Set.range i := h (hp ▸ Set.mem_range_self z)
      rwa [← hr] at hz
    exact ENat.card_congr (Equiv.ofBijective j ⟨hj, hjS⟩)

/-- Restricting to an open subscheme can only decrease the geometric fibre count. -/
private theorem geometricIrreducibleComponentCount_comp_le
    {V X Y : Scheme.{u}} (i : V ⟶ X) (f : X ⟶ Y) [IsOpenImmersion i] [LocallyQuasiFinite f]
    (y : Y) :
    geometricIrreducibleComponentCount (i ≫ f) y ≤ geometricIrreducibleComponentCount f y := by
  obtain ⟨hc, hd⟩ := geometricIrreducibleComponentCount_eq_card_pullback i f y
  rw [hc, hd]
  exact ENat.card_le_card_of_injective (pullback.snd i _).isOpenEmbedding.injective

/-- A morphism covered by finitely many universally closed pieces is universally closed. -/
private theorem universallyClosed_of_finite_cover
    {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type*} [Finite ι]
    (Z : ι → Scheme.{u}) (i : ∀ a, Z a ⟶ X) (hcover : ∀ x : X, ∃ a z, i a z = x)
    (hfinite : ∀ a, UniversallyClosed (i a ≫ f)) : UniversallyClosed f := by
  constructor
  intro X' Y' p q f' h C hC
  let j (a : ι) := pullback.snd (i a) p
  have hj (a : ι) : IsClosedMap (j a ≫ f') :=
    (hfinite a).universally_isClosedMap _ _ _
      ((IsPullback.of_hasPullback (i a) p).paste_vert h.flip).flip
  have heq : f' '' C = ⋃ a, (j a ≫ f') '' ((j a) ⁻¹' C) := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨a, z, hz⟩ := hcover (p x)
      obtain ⟨w, -, hw⟩ := Scheme.Pullback.exists_preimage_pullback z x hz
      exact Set.mem_iUnion.mpr ⟨a, w, by simpa [j, hw] using hx, by simp [j, hw]⟩
    · intro y hy
      obtain ⟨a, z, hz, rfl⟩ := Set.mem_iUnion.mp hy
      exact ⟨j a z, hz, rfl⟩
  rw [heq]
  exact isClosed_iUnion_of_finite fun a => hj a _ (hC.preimage (j a).continuous)

/-- A separated, locally quasi-finite morphism covered by finitely many finite pieces is
finite. -/
private theorem isFinite_of_finite_cover
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
    [LocallyQuasiFinite f] {ι : Type*} [Finite ι]
    (Z : ι → Scheme.{u}) (i : ∀ a, Z a ⟶ X) (hcover : ∀ x : X, ∃ a z, i a z = x)
    (hfinite : ∀ a, IsFinite (i a ≫ f)) : IsFinite f := by
  have : UniversallyClosed f := universallyClosed_of_finite_cover f Z i hcover
    fun a => by have := hfinite a; infer_instance
  have : IsProper f := ⟨⟩
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

/-- If an open subscheme is finite over the target and contains every fibre over the range of a
morphism `t`, the base change along `t` is finite. -/
private theorem isFinite_pullback_snd_of_range_subset
    {V X Y T : Scheme.{u}} (i : V ⟶ X) (f : X ⟶ Y) (t : T ⟶ Y)
    [IsOpenImmersion i] [IsFinite (i ≫ f)] (h : f ⁻¹' Set.range t ⊆ Set.range i) :
    IsFinite (pullback.snd f t) := by
  let p := pullback.fst f t
  let j := pullback.snd i p
  have : Surjective j := by
    refine ⟨fun z => ?_⟩
    rw [← Set.mem_range, Scheme.Pullback.range_snd]
    exact h ((Scheme.Pullback.range_fst f t).subset (Set.mem_range_self z))
  have : IsIso j := (isIso_iff_isOpenImmersion_and_surjective j).mpr ⟨inferInstance, inferInstance⟩
  have : IsFinite (j ≫ pullback.snd f t) :=
    MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback i p).paste_vert (IsPullback.of_hasPullback f t)) inferInstance
  have hfin : IsFinite (inv j ≫ (j ≫ pullback.snd f t)) := inferInstance
  simpa only [IsIso.inv_hom_id_assoc] using hfin

/-- Given an open subscheme finite over the target which contains the whole fibre over a point of
maximal count, the morphism is finite over an open neighbourhood of that point. -/
private theorem exists_isOpen_isFinite_pullback_snd
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
    [LocallyQuasiFinite f] [UniversallyOpen f] (d : ℕ)
    (hbound : ∀ y, geometricIrreducibleComponentCount f y ≤ d)
    (y : Y) (hy : geometricIrreducibleComponentCount f y = d)
    (V : X.Opens) [IsFinite (V.ι ≫ f)] (hV : f ⁻¹' {y} ⊆ V) :
    ∃ U : Y.Opens, y ∈ U ∧ IsFinite (pullback.snd f U.ι) := by
  let U : Y.Opens :=
    ⟨{z | (d : ℕ∞) ≤ geometricIrreducibleComponentCount (V.ι ≫ f) z},
      isOpen_geometricIrreducibleComponentCount_ge (V.ι ≫ f) d⟩
  refine ⟨U, ?_, ?_⟩
  · have heq := (geometricIrreducibleComponentCount_comp_eq_iff V.ι f y
      (hy ▸ ENat.natCast_ne_top d)).mpr (by simpa only [Scheme.Opens.range_ι] using hV)
    show (d : ℕ∞) ≤ geometricIrreducibleComponentCount (V.ι ≫ f) y
    rw [heq, hy]
  · refine isFinite_pullback_snd_of_range_subset V.ι f U.ι fun x hx => ?_
    rw [Scheme.Opens.range_ι] at hx ⊢
    have heq : geometricIrreducibleComponentCount (V.ι ≫ f) (f x) =
        geometricIrreducibleComponentCount f (f x) :=
      le_antisymm (geometricIrreducibleComponentCount_comp_le V.ι f (f x)) ((hbound _).trans hx)
    have hi : x ∈ Set.range V.ι := (geometricIrreducibleComponentCount_comp_eq_iff V.ι f (f x)
      (ne_top_of_le_ne_top (ENat.natCast_ne_top d) (hbound _))).mp heq rfl
    simpa only [Scheme.Opens.range_ι] using hi

/-- A finite geometric fibre count makes the fibre finite. -/
private theorem finite_fiber_of_geometricIrreducibleComponentCount_ne_top
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] (y : Y)
    (hcount : geometricIrreducibleComponentCount f y ≠ ⊤) : (f ⁻¹' {y}).Finite := by
  let K := SeparableClosure (Y.residueField y)
  rw [geometricIrreducibleComponentCount_eq_card] at hcount
  have : Finite (geometricFiber f y K) := ENat.card_lt_top.mp (lt_top_iff_ne_top.mpr hcount)
  let p : geometricFiber f y K ⟶ f.fiber y := pullback.fst (f.fiberToSpecResidueField y)
    (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) K)))
  have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) K))) :=
    inferInstance
  have : Surjective p := by
    show Surjective (pullback.fst (f.fiberToSpecResidueField y)
      (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) K))))
    infer_instance
  have : Finite (f.fiber y) := Finite.of_surjective p p.surjective
  have : Finite (f ⁻¹' {y}) := Finite.of_equiv (f.fiber y) (f.fiberHomeo y)
  exact Set.toFinite _

/-- Split the whole of a finite fibre off over an étale neighbourhood. -/
private theorem exists_etaleNeighborhood_decomposition_of_count_ne_top
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
    [LocallyQuasiFinite f] (y : Y) (hcount : geometricIrreducibleComponentCount f y ≠ ⊤) :
    ∃ (n : ℕ) (x : Fin n → f.fiber y) (U : EtaleNeighborhood Y y) (m : Fin n → ℕ)
      (D : Option (Σ i, Fin (m i)) → (pullback f U.toBase).Opens)
      (v : ∀ i j, D (some ⟨i, j⟩)),
      Function.Surjective x ∧
      Set.PairwiseDisjoint Set.univ (fun k => (D k).1) ∧
      (⋃ k, (D k).1) = Set.univ ∧
      (∀ k, IsClopen (D k).1) ∧
      (∀ i j,
        let V := D (some ⟨i, j⟩)
        let g := V.ι ≫ pullback.snd f U.toBase
        IsFinite g ∧
          g ⁻¹' {U.point} = {v i j} ∧
          (V.ι ≫ pullback.fst f U.toBase) (v i j) = f.fiberι y (x i) ∧
          ∃ hvu : g (v i j) = U.point,
            ((U.scheme.residueFieldCongr hvu).inv ≫
              g.residueFieldMap (v i j)).hom.IsPurelyInseparable) ∧
      (∀ w : D none,
        ((D none).ι ≫ pullback.snd f U.toBase) w = U.point →
          ∀ i, ((D none).ι ≫ pullback.fst f U.toBase) w ≠ f.fiberι y (x i)) := by
  classical
  have : Finite (f ⁻¹' {y}) :=
    (finite_fiber_of_geometricIrreducibleComponentCount_ne_top f y hcount).to_subtype
  have : Finite (f.fiber y) := Finite.of_equiv (f ⁻¹' {y}) (f.fiberHomeo y).symm.toEquiv
  let : Fintype (f.fiber y) := Fintype.ofFinite _
  have : DiscreteTopology (f ⁻¹' {y}) :=
    isDiscrete_iff_discreteTopology.mp (f.isDiscrete_preimage_singleton y)
  have : DiscreteTopology (f.fiber y) :=
    (f.fiberHomeo y).discreteTopology_iff.mpr inferInstance
  obtain ⟨U, m, D, v, hD⟩ :=
    exists_etaleNeighborhood_purelyInseparable_decomposition f (Fintype.card (f.fiber y)) y
      (Fintype.equivFin (f.fiber y)).symm (Fintype.equivFin (f.fiber y)).symm.injective
      fun i => isOpen_discrete _
  exact ⟨Fintype.card (f.fiber y), (Fintype.equivFin (f.fiber y)).symm, U, m, D, v,
    (Fintype.equivFin (f.fiber y)).symm.surjective, hD⟩

/-- The geometric fibre count is compatible with arbitrary base change. -/
private theorem geometricIrreducibleComponentCount_eq_of_isPullback
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {p : X' ⟶ X} {q : X' ⟶ Y'}
    [LocallyQuasiFinite f] [LocallyQuasiFinite q] (h : IsPullback p q f g) :
    geometricIrreducibleComponentCount q = geometricIrreducibleComponentCount f ∘ g := by
  simp only [geometricIrreducibleComponentCount_eq_numGeometricConnectedComponents]
  exact numGeometricConnectedComponents_eq_of_isPullback f q p g h

/-- With the count constant, every point of the target has an étale neighbourhood over which the
base change of the morphism is finite. -/
private theorem exists_etale_isFinite_pullback_snd
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
    [LocallyQuasiFinite f] [UniversallyOpen f] (d : ℕ)
    (hcount : ∀ y, geometricIrreducibleComponentCount f y = d) (y : Y) :
    ∃ (T : Scheme.{u}) (t : T ⟶ Y), Etale t ∧ y ∈ Set.range t ∧ IsFinite (pullback.snd f t) := by
  classical
  obtain ⟨n, x, U, m, D, v, hx, hdisj, hcover, hclopen, hparts, haway⟩ :=
    exists_etaleNeighborhood_decomposition_of_count_ne_top f y
      ((hcount y) ▸ ENat.natCast_ne_top d)
  let Z := pullback f U.toBase
  let g : Z ⟶ U.scheme := pullback.snd f U.toBase
  let V : Z.Opens := ⨆ a : Σ i, Fin (m i), D (some a)
  have hle (a : Σ i, Fin (m i)) : D (some a) ≤ V :=
    le_iSup (fun a : Σ i, Fin (m i) => D (some a)) a
  have : IsFinite (V.ι ≫ g) := by
    refine isFinite_of_finite_cover (V.ι ≫ g) (fun a : Σ i, Fin (m i) => (D (some a)).toScheme)
      (fun a => Z.homOfLE (hle a)) (fun z => ?_) fun a => ?_
    · have hz : z.1 ∈ (V : Set Z) := z.2
      simp only [V, TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion] at hz
      obtain ⟨a, ha⟩ := hz
      exact ⟨a, ⟨z.1, ha⟩, Subtype.ext (by simp [Scheme.homOfLE_apply])⟩
    · have hi : Z.homOfLE (hle a) ≫ (V.ι ≫ g) = (D (some a)).ι ≫ g := by
        rw [← Category.assoc, Scheme.homOfLE_ι]
      rw [hi]
      exact (hparts a.1 a.2).1
  have hV : g ⁻¹' {U.point} ⊆ V := by
    intro z hz
    change g z = U.point at hz
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hcover ▸ Set.mem_univ z)
    cases k with
    | some a => exact hle a hk
    | none =>
      exfalso
      have hzy : f (pullback.fst f U.toBase z) = y := by
        simpa [Scheme.Hom.comp_apply, ← U.map_point, ← hz, g] using
          congr($(pullback.condition (f := f) (g := U.toBase)) z)
      obtain ⟨w, hw⟩ := (f.range_fiberι y).symm ▸
        (show pullback.fst f U.toBase z ∈ f ⁻¹' {y} from hzy)
      obtain ⟨a, rfl⟩ := hx w
      exact haway ⟨z, hk⟩ hz a hw.symm
  have hg (z : U.scheme) : geometricIrreducibleComponentCount g z = d := by
    rw [geometricIrreducibleComponentCount_eq_of_isPullback
      (IsPullback.of_hasPullback f U.toBase)]
    exact hcount _
  obtain ⟨O, hO, hfin⟩ := exists_isOpen_isFinite_pullback_snd g d (fun z => (hg z).le) U.point
    (hg _) V hV
  refine ⟨O.toScheme, O.ι ≫ U.toBase, inferInstance, ⟨⟨U.point, hO⟩, U.map_point⟩, ?_⟩
  have hi : IsFinite (((IsPullback.of_hasPullback g O.ι).paste_horiz
    (IsPullback.of_hasPullback f U.toBase)).isoPullback.inv ≫ pullback.snd g O.ι) :=
    inferInstance
  simpa only [IsPullback.isoPullback_inv_snd] using hi

/-- A separated, locally quasi-finite and universally open morphism with constant geometric fibre
count is finite. -/
@[ega "IV 15.5.9" "more general"]
private theorem isFinite_of_constant_geometricIrreducibleComponentCount
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
    [LocallyQuasiFinite f] [UniversallyOpen f] (d : ℕ)
    (hcount : ∀ y, geometricIrreducibleComponentCount f y = d) : IsFinite f := by
  classical
  choose T t ht hy hfin using exists_etale_isFinite_pullback_snd f d hcount
  let C : Y.Cover Scheme.etalePrecoverage :=
    Scheme.Cover.mkOfCovers (P := @Etale) Y T t (fun y => ⟨y, hy y⟩) ht
  have : MorphismProperty.IsLocalAtTarget (@IsFinite : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage :=
    Stacks.Morphisms.isFinite_isLocalAtTarget_fpqc_of_isAffineHom inferInstance
  exact MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
    (P := @IsFinite) (K := Scheme.fpqcPrecoverage)
    (Scheme.etalePrecoverage_le_fpqcPrecoverage _ C.mem₀)
    (by rintro _ _ _ ⟨y⟩; exact hfin y)

/-- **Stacks Project, Tag 0F37.** For a separated, locally quasi-finite and universally open
morphism whose geometric fibre count attains the finite maximum `d`, the locus where the count
equals `d` is open. -/
@[stacks 0F37 "openness"]
theorem isOpen_geometricIrreducibleComponentCount_maxLocus
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
    [LocallyQuasiFinite f] [UniversallyOpen f] (d : ℕ)
    (hmax : IsGreatest (Set.range (geometricIrreducibleComponentCount f)) (d : ℕ∞)) :
    IsOpen {y : Y | geometricIrreducibleComponentCount f y = (d : ℕ∞)} := by
  convert isOpen_geometricIrreducibleComponentCount_ge f d using 1
  ext y
  exact ⟨fun h => le_of_eq h.symm, le_antisymm (hmax.2 ⟨y, rfl⟩)⟩

/-- **Stacks Project, Tag 0F37.** The morphism is finite over the open locus where its geometric
fibre count attains the finite maximum. -/
@[stacks 0F37 "finiteness"]
theorem isFinite_restrict_geometricIrreducibleComponentCount_maxLocus
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
    [LocallyQuasiFinite f] [UniversallyOpen f] (d : ℕ)
    (hmax : IsGreatest (Set.range (geometricIrreducibleComponentCount f)) (d : ℕ∞)) :
    IsFinite (f ∣_ ⟨{y : Y | geometricIrreducibleComponentCount f y = (d : ℕ∞)},
      isOpen_geometricIrreducibleComponentCount_maxLocus f d hmax⟩) := by
  let U : Y.Opens := ⟨{y | geometricIrreducibleComponentCount f y = (d : ℕ∞)},
    isOpen_geometricIrreducibleComponentCount_maxLocus f d hmax⟩
  have : UniversallyOpen (f ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f U).flip inferInstance
  refine isFinite_of_constant_geometricIrreducibleComponentCount (f ∣_ U) d fun y => ?_
  rw [geometricIrreducibleComponentCount_eq_of_isPullback (isPullback_morphismRestrict f U).flip]
  exact y.2

end AlgebraicGeometry

end
