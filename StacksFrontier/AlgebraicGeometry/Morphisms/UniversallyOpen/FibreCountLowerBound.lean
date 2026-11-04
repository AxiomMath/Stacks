module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.EtaleLocalizationQuasiFinite.PurelyInseparableDecomposition
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NowhereDenseFibres.FibrePoints
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.PurelyInseparablePoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.IrreducibleComponents
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Defs

/-!
# Lower semicontinuity of the number of geometric components of the fibres

For a separated, locally quasi-finite and universally open morphism of schemes, the locus of
points of the target whose geometric fibre has at least a fixed number of irreducible components
is open.

## Main results

* `AlgebraicGeometry.isOpen_geometricIrreducibleComponentCount_ge` is that openness.

## Implementation notes

The count is the extended-natural-valued number of geometrically irreducible components of the
fibre. Around a point `y` where the count is at least `d`, pick `d` distinct points of the
geometric fibre, let `x₁, …, xₙ` be the finitely many points of the fibre they lie over, and
split them off over an étale neighbourhood `(U, u)` of `y`: each piece `V` of the resulting
decomposition is finite over `U`, meets the distinguished fibre in one point, and its geometric
fibre over `u` is a single point because the residue field extension there is purely inseparable.
Distinct chosen points therefore live in distinct pieces. Since each piece is open over `U`, the
locus of points of `U` met by all `d` pieces is an open neighbourhood of `u`; over it the count
is at least `d`, and the count is insensitive to the étale base change, so the image of that
neighbourhood is the required open set.

## References

* [Stacks Project, Tag 0F36](https://stacks.math.columbia.edu/tag/0F36)
-/

public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry

universe u

/-- In a Hausdorff space the irreducible components are the singletons. -/
private lemma encard_irreducibleComponents_of_t2Space (α : Type*) [TopologicalSpace α]
    [T2Space α] : (irreducibleComponents α).encard = (Set.univ : Set α).encard := by
  have hcomponents : irreducibleComponents α = Set.range (fun x : α => ({x} : Set α)) := by
    ext s
    constructor
    · intro hs
      obtain ⟨x, hx⟩ := isIrreducible_iff_singleton.mp hs.1
      exact ⟨x, hx.symm⟩
    · rintro ⟨x, rfl⟩
      refine ⟨isIrreducible_singleton, fun t ht hxt => ?_⟩
      obtain ⟨y, rfl⟩ := isIrreducible_iff_singleton.mp ht
      cases Set.singleton_subset_singleton.mp hxt
      rfl
  rw [hcomponents, ← Set.image_univ]
  exact Set.singleton_injective.encard_image _

/-- The map from a fibre to the spectrum of the residue field is locally quasi-finite. -/
private lemma locallyQuasiFinite_fiberToSpecResidueField
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] (y : Y) :
    LocallyQuasiFinite (f.fiberToSpecResidueField y) := by
  change LocallyQuasiFinite (pullback.snd f (Y.fromSpecResidueField y))
  infer_instance

/-- A locally quasi-finite morphism to a one-point scheme has discrete source. -/
private lemma isDiscrete_univ_of_locallyQuasiFinite {A B : Scheme.{u}} (q : A ⟶ B)
    [LocallyQuasiFinite q] [Nonempty B] [Subsingleton B] :
    _root_.IsDiscrete (Set.univ : Set A) := by
  have h := q.isDiscrete_preimage_singleton (Classical.arbitrary B)
  have heq : q ⁻¹' {Classical.arbitrary B} = Set.univ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  rwa [heq] at h

/-- The geometric fibre of a locally quasi-finite morphism is discrete, so its cardinality is
the geometric component count. -/
private lemma encard_geometricFiber {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] (y : Y)
    (K : Type u) [Field K] [Algebra (Y.residueField y) K] [IsSepClosed K] :
    (Set.univ : Set (geometricFiber f y K)).encard = geometricIrreducibleComponentCount f y := by
  have := locallyQuasiFinite_fiberToSpecResidueField f y
  let q : geometricFiber f y K ⟶ Spec (CommRingCat.of K) :=
    pullback.snd (f.fiberToSpecResidueField y)
      (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) K)))
  have : LocallyQuasiFinite q := inferInstanceAs (LocallyQuasiFinite (pullback.snd _ _))
  have : DiscreteTopology (geometricFiber f y K) :=
    isDiscrete_univ_iff.mp (isDiscrete_univ_of_locallyQuasiFinite q)
  exact (encard_irreducibleComponents_of_t2Space (geometricFiber f y K)).symm.trans
    (encard_irreducibleComponents_geometricFiber f y K)

/-- A geometric fibre count of at least `d` produces `d` distinct points of the geometric
fibre. -/
private theorem exists_injective_geometricFiber_points
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] (y : Y)
    (K : Type u) [Field K] [Algebra (Y.residueField y) K] [IsSepClosed K] (d : ℕ)
    (hd : (d : ℕ∞) ≤ geometricIrreducibleComponentCount f y) :
    ∃ z : Fin d → geometricFiber f y K, Function.Injective z := by
  classical
  obtain ⟨s, -, hs⟩ := Set.exists_subset_encard_eq
    (s := (Set.univ : Set (geometricFiber f y K))) (k := (d : ℕ∞))
    (by rwa [encard_geometricFiber f y K])
  have hsfin : s.Finite := Set.finite_of_encard_eq_coe hs
  let : Fintype s := hsfin.fintype
  have hcard : Fintype.card s = d := by
    have hcard' : (Fintype.card s : ℕ∞) = (d : ℕ∞) := by rw [Set.coe_fintypeCard, hs]
    exact_mod_cast hcard'
  let e : Fin d ≃ s := (finCongr hcard.symm).trans (Fintype.equivFin s).symm
  exact ⟨fun i => (e i).1, fun i j hij => e.injective (Subtype.ext hij)⟩

/-- Conversely, `d` distinct points of a geometric fibre bound the count from below. -/
private lemma le_geometricIrreducibleComponentCount_of_injective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] (y : Y)
    (K : Type u) [Field K] [Algebra (Y.residueField y) K] [IsSepClosed K]
    (d : ℕ) (z : Fin d → geometricFiber f y K) (hz : Function.Injective z) :
    (d : ℕ∞) ≤ geometricIrreducibleComponentCount f y := by
  rw [← encard_geometricFiber f y K, Set.encard_univ]
  simpa using ENat.card_le_card_of_injective hz

/-- Replace a finite family of points by an injective family with the same image. -/
private lemma exists_injective_range_eq {α : Type*} {d : ℕ} (x₀ : Fin d → α) :
    ∃ (n : ℕ) (x : Fin n → α), Function.Injective x ∧ ∀ i, ∃ j, x j = x₀ i := by
  classical
  let : Fintype (Set.range x₀) := (Set.finite_range x₀).fintype
  let e : Fin (Fintype.card (Set.range x₀)) ≃ Set.range x₀ :=
    (Fintype.equivFin (Set.range x₀)).symm
  refine ⟨Fintype.card (Set.range x₀), fun i => (e i).1,
    fun i j hij => e.injective (Subtype.ext hij), fun i => ?_⟩
  obtain ⟨j, hj⟩ := e.surjective ⟨x₀ i, ⟨i, rfl⟩⟩
  exact ⟨j, congrArg Subtype.val hj⟩

/-- The fibres of a locally quasi-finite morphism are discrete. -/
private lemma isDiscrete_fiber_of_locallyQuasiFinite
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] (y : Y) :
    _root_.IsDiscrete (Set.univ : Set (f.fiber y)) := by
  have := locallyQuasiFinite_fiberToSpecResidueField f y
  exact isDiscrete_univ_of_locallyQuasiFinite (f.fiberToSpecResidueField y)

/-- Every point of a fibre of a locally quasi-finite morphism is isolated in that fibre. -/
private lemma isIsolatedPoint_of_locallyQuasiFinite
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] (y : Y) (x : f.fiber y) :
    IsIsolatedPoint x := by
  have : DiscreteTopology (f.fiber y) :=
    isDiscrete_univ_iff.mp (isDiscrete_fiber_of_locallyQuasiFinite f y)
  simp [IsIsolatedPoint]

/-- Pairwise disjoint opens of the source, each meeting the fibre over a point, give that many
distinct points of a geometric fibre. -/
private lemma exists_injective_geometricFiber_points_of_disjoint_opens
    {P U : Scheme.{u}} (p : P ⟶ U) (u : U) (K : Type u) [Field K] [Algebra (U.residueField u) K]
    {I : Type*} (A : I → P.Opens)
    (hdisj : Set.PairwiseDisjoint Set.univ fun i => (A i : Set P))
    (hmeet : ∀ i, u ∈ Set.range ((A i).ι ≫ p)) :
    ∃ z : I → geometricFiber p u K, Function.Injective z := by
  classical
  let q := p.fiberToSpecResidueField u
  let r := Spec.map (CommRingCat.ofHom (algebraMap (U.residueField u) K))
  let w : ∀ i, (A i : Scheme) := fun i => Classical.choose (Set.mem_range.mp (hmeet i))
  have hw (i : I) : ((A i).ι ≫ p) (w i) = u :=
    Classical.choose_spec (Set.mem_range.mp (hmeet i))
  let a : I → p.fiber u := fun i => (p.fiberHomeo u).symm ⟨(A i).ι (w i), hw i⟩
  have ha (i : I) : q (a i) = r (Classical.arbitrary (Spec (CommRingCat.of K))) :=
    Subsingleton.elim _ _
  let z : I → geometricFiber p u K := fun i => Classical.choose <|
    Scheme.Pullback.exists_preimage_pullback (f := q) (g := r) (a i)
      (Classical.arbitrary (Spec (CommRingCat.of K))) (ha i)
  have hz (i : I) : pullback.fst q r (z i) = a i :=
    (Classical.choose_spec (Scheme.Pullback.exists_preimage_pullback (f := q) (g := r) (a i)
      (Classical.arbitrary (Spec (CommRingCat.of K))) (ha i))).1
  refine ⟨z, fun i j hij => ?_⟩
  have hfst := congrArg (pullback.fst q r) hij
  rw [hz i, hz j] at hfst
  have hpoint : (A i).ι (w i) = (A j).ι (w j) := by
    simpa [a] using congrArg Subtype.val (congrArg (p.fiberHomeo u) hfst)
  by_contra hne
  have hmem (k : I) : (A k).ι (w k) ∈ (A k : Set P) :=
    (congrArg (fun V : P.Opens => (A k).ι (w k) ∈ (V : Set P))
      (Scheme.Opens.opensRange_ι (A k))).mp (Scheme.Hom.mem_opensRange.mpr ⟨w k, rfl⟩)
  exact Set.disjoint_left.mp (hdisj (Set.mem_univ i) (Set.mem_univ j) hne) (hmem i)
    (hpoint ▸ hmem j)

/-- The geometric fibre of a base change along one and the same field extension, together with
its compatibility with the two projections to the common source. -/
private noncomputable def geometricFiberPullbackIsoData
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (y : Y')
    (K : Type u) [Field K] [Algebra (Y'.residueField y) K] [Algebra (Y.residueField (g y)) K]
    (compat : (algebraMap (Y'.residueField y) K).comp (g.residueFieldMap y).hom =
      algebraMap (Y.residueField (g y)) K) :
    {e : geometricFiber (pullback.snd f g) y K ≅ geometricFiber f (g y) K //
      e.hom ≫ pullback.fst (f.fiberToSpecResidueField (g y))
            (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField (g y)) K))) ≫
          f.fiberι (g y) =
        pullback.fst ((pullback.snd f g).fiberToSpecResidueField y)
            (Spec.map (CommRingCat.ofHom (algebraMap (Y'.residueField y) K))) ≫
          (pullback.snd f g).fiberι y ≫ pullback.fst f g} := by
  have hspec : (Spec.map (CommRingCat.ofHom (algebraMap (Y'.residueField y) K))) ≫
      Spec.map (g.residueFieldMap y) =
      Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField (g y)) K)) := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact DFunLike.congr_fun compat x
  have h2 : IsPullback
      (pullback.fst (f.fiberToSpecResidueField (g y))
        (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField (g y)) K))))
      (pullback.snd (f.fiberToSpecResidueField (g y))
        (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField (g y)) K))))
      (f.fiberToSpecResidueField (g y))
      (Spec.map (CommRingCat.ofHom (algebraMap (Y'.residueField y) K)) ≫
        Spec.map (g.residueFieldMap y)) := by
    rw [hspec]
    exact IsPullback.of_hasPullback _ _
  have paste := (IsPullback.of_hasPullback ((pullback.snd f g).fiberToSpecResidueField y)
    (Spec.map (CommRingCat.ofHom (algebraMap (Y'.residueField y) K)))).paste_horiz
      (isPullback_fiberToSpecResidueField_of_isPullback (IsPullback.of_hasPullback f g) y)
  refine ⟨paste.isoIsPullback _ _ h2,
    (IsPullback.isoIsPullback_hom_fst_assoc _ _ paste h2 (f.fiberι (g y))).trans ?_⟩
  exact (Category.assoc _ _ _).trans (congrArg _ (pullback.lift_fst _ _ _))

/-- Over an étale neighbourhood, the geometric fibre of the base change at the distinguished
point is identified with the geometric fibre at the base point. -/
private lemma exists_geometricFiber_etale_iso
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) [Etale g] (y : Y) (t : Y') (ht : g t = y)
    (K : Type u) [Field K] [Algebra (Y.residueField y) K] [IsSepClosed K] :
    ∃ (a : Algebra (Y'.residueField t) K),
      ∃ e : @geometricFiber _ _ (pullback.snd f g) t K _ a ≅ geometricFiber f y K,
        e.hom ≫ pullback.fst (f.fiberToSpecResidueField y)
            (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) K))) ≫ f.fiberι y =
          pullback.fst ((pullback.snd f g).fiberToSpecResidueField t)
              (Spec.map (CommRingCat.ofHom (@algebraMap (Y'.residueField t) K _ _ a))) ≫
            (pullback.snd f g).fiberι t ≫ pullback.fst f g := by
  subst ht
  algebraize [(g.residueFieldMap t).hom]
  let b : Y'.residueField t →ₐ[Y.residueField (g t)] K := IsSepClosed.lift
  let a : Algebra (Y'.residueField t) K := b.toRingHom.toAlgebra
  let := a
  have hb : (algebraMap (Y'.residueField t) K).comp (g.residueFieldMap t).hom =
      algebraMap (Y.residueField (g t)) K := b.comp_algebraMap
  exact ⟨a, (geometricFiberPullbackIsoData f g t K hb).1,
    (geometricFiberPullbackIsoData f g t K hb).2⟩

/-- The induced map of geometric fibres along a composite with an open immersion. -/
private noncomputable def geometricFiberMapOfComp
    {T X Y : Scheme.{u}} (i : T ⟶ X) (f : X ⟶ Y) (y : Y)
    (K : Type u) [Field K] [Algebra (Y.residueField y) K] :
    geometricFiber (i ≫ f) y K ⟶ geometricFiber f y K :=
  pullback.map ((i ≫ f).fiberToSpecResidueField y)
    (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) K)))
    (f.fiberToSpecResidueField y)
    (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) K)))
    (Scheme.Hom.fiberMapComp i f y) (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id]; exact (Scheme.Hom.fiberMapComp_fiberToSpecResidueField i f y).symm)
    (by simp)

private lemma range_geometricFiberMapOfComp
    {T X Y : Scheme.{u}} (i : T ⟶ X) (f : X ⟶ Y) (y : Y)
    (K : Type u) [Field K] [Algebra (Y.residueField y) K] :
    Set.range (geometricFiberMapOfComp i f y K).base =
      (pullback.fst (f.fiberToSpecResidueField y)
        (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) K)))).base ⁻¹'
        Set.range (Scheme.Hom.fiberMapComp i f y).base := by
  let r := Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) K))
  have e₁ : (i ≫ f).fiberToSpecResidueField y ≫ (𝟙 _) =
      Scheme.Hom.fiberMapComp i f y ≫ f.fiberToSpecResidueField y := by
    rw [Category.comp_id]
    exact (Scheme.Hom.fiberMapComp_fiberToSpecResidueField i f y).symm
  have e₂ : r ≫ (𝟙 _) = (𝟙 _) ≫ r := by simp
  let m := pullback.map ((i ≫ f).fiberToSpecResidueField y) r (f.fiberToSpecResidueField y) r
    (Scheme.Hom.fiberMapComp i f y) (𝟙 _) (𝟙 _) e₁ e₂
  have h := Scheme.Pullback.range_map ((i ≫ f).fiberToSpecResidueField y) r
    (f.fiberToSpecResidueField y) r (Scheme.Hom.fiberMapComp i f y) (𝟙 _) (𝟙 _) e₁ e₂
  show Set.range m.base =
    (pullback.fst (f.fiberToSpecResidueField y) r).base ⁻¹'
      Set.range (Scheme.Hom.fiberMapComp i f y).base
  simpa only [Scheme.Hom.id_base, TopCat.hom_id, ContinuousMap.coe_id, Set.range_id,
    Set.preimage_univ, Set.inter_univ] using h

/-- Two points of a fibre product with the same images agree when one residue extension is
purely inseparable. -/
private theorem eq_of_pullback_images_eq_of_isPurelyInseparable
    {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} (T : Scheme.Pullback.Triplet f g)
    (hpi : (((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x).hom).IsPurelyInseparable)
    {z z' : ↑(pullback f g)}
    (hzx : pullback.fst f g z = T.x) (hzy : pullback.snd f g z = T.y)
    (hz'x : pullback.fst f g z' = T.x) (hz'y : pullback.snd f g z' = T.y) : z = z' := by
  let e := Scheme.Pullback.carrierEquiv (f := f) (g := g)
  have htriplet (w : ↑(pullback f g)) (hwx : pullback.fst f g w = T.x)
      (hwy : pullback.snd f g w = T.y) : (e w).1 = T := by
    refine Scheme.Pullback.Triplet.ext ?_ ?_
    · have hh := Scheme.Pullback.carrierEquiv_symm_fst (e w).1 (e w).2
      change pullback.fst f g (e.symm (e w)) = (e w).1.x at hh
      rw [e.symm_apply_apply] at hh
      exact hh.symm.trans hwx
    · have hh := Scheme.Pullback.carrierEquiv_symm_snd (e w).1 (e w).2
      change pullback.snd f g (e.symm (e w)) = (e w).1.y at hh
      rw [e.symm_apply_apply] at hh
      exact hh.symm.trans hwy
  have hTz := htriplet z hzx hzy
  have hTz' := htriplet z' hz'x hz'y
  refine e.injective (Scheme.Pullback.carrierEquiv_eq_iff.mpr ⟨hTz.trans hTz'.symm, ?_⟩)
  have : Subsingleton (Spec (e z').1.tensor) := by
    rw [hTz']
    exact Scheme.Pullback.tensor_subsingleton_of_isPurelyInseparable T hpi
  exact Subsingleton.elim _ _

/-- A piece of the decomposition with singleton fibre and purely inseparable residue extension
has a one-point geometric fibre. -/
private lemma subsingleton_geometricFiber_of_singleton_fiber
    {P U : Scheme.{u}} (g : P ⟶ U) (u : U) (v : P) (hfiber : g ⁻¹' {u} = {v})
    (hres : ∃ h : g v = u,
      ((U.residueFieldCongr h).inv ≫ g.residueFieldMap v).hom.IsPurelyInseparable)
    (K : Type u) [Field K] [Algebra (U.residueField u) K] :
    Subsingleton (geometricFiber g u K) := by
  obtain ⟨hvu, hpure⟩ := hres
  let r := Spec.map (CommRingCat.ofHom (algebraMap (U.residueField u) K)) ≫
    U.fromSpecResidueField u
  let e := pullbackLeftPullbackSndIso g (U.fromSpecResidueField u)
    (Spec.map (CommRingCat.ofHom (algebraMap (U.residueField u) K)))
  have hfst (z : ↑(pullback (C := Scheme) g r)) : pullback.fst g r z = v := by
    have hbase : g (pullback.fst g r z) = r (pullback.snd g r z) := by
      simpa only [Scheme.Hom.comp_apply] using
        congrArg (fun q : pullback (C := Scheme) g r ⟶ U => q z)
          (pullback.condition (f := g) (g := r))
    have hz : g (pullback.fst g r z) = u := hbase.trans (U.fromSpecResidueField_apply u _)
    have hm : pullback.fst g r z ∈ g ⁻¹' {u} := by simpa using hz
    rw [hfiber] at hm
    exact Set.mem_singleton_iff.mp hm
  have hQ : Subsingleton (pullback (C := Scheme) g r) := by
    refine ⟨fun z z' => ?_⟩
    let T : Scheme.Pullback.Triplet g r :=
      ⟨v, Classical.arbitrary (Spec (CommRingCat.of K)), u, hvu,
        U.fromSpecResidueField_apply u _⟩
    exact eq_of_pullback_images_eq_of_isPurelyInseparable T hpure (hfst z)
      (Subsingleton.elim _ _) (hfst z') (Subsingleton.elim _ _)
  exact ⟨fun x z => e.hom.homeomorph.injective (hQ.elim _ _)⟩

/-- An étale neighbourhood over which the count is bounded below produces an open neighbourhood
of the base point over which it is bounded below. -/
private lemma exists_isOpen_le_geometricIrreducibleComponentCount
    {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) (U : EtaleNeighborhood Y y) (V : U.scheme.Opens)
    (d : ℕ) (hu : U.point ∈ (V : Set U.scheme))
    (hlocal : ∀ u' ∈ (V : Set U.scheme),
      (d : ℕ∞) ≤ geometricIrreducibleComponentCount (pullback.snd f U.toBase) u') :
    ∃ O : Y.Opens, y ∈ (O : Set Y) ∧
      (O : Set Y) ⊆ {z : Y | (d : ℕ∞) ≤ geometricIrreducibleComponentCount f z} := by
  refine ⟨⟨U.toBase '' (V : Set U.scheme), U.toBase.isOpenMap _ V.2⟩, ?_, ?_⟩
  · simpa [U.map_point] using Set.mem_image_of_mem U.toBase hu
  · rintro z ⟨u', huV, rfl⟩
    have heq := congrFun (geometricIrreducibleComponentCount_pullback f U.toBase) u'
    show (d : ℕ∞) ≤ geometricIrreducibleComponentCount f (U.toBase u')
    exact (hlocal u' huV).trans_eq (by simpa [Function.comp_apply] using heq)

/-- Pairwise disjoint opens of an étale base change, each meeting the fibre over the
distinguished point, give an open neighbourhood of the base point over which the count is at
least their number. -/
private lemma exists_isOpen_le_count_of_disjoint_opens {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyQuasiFinite f] [UniversallyOpen f] (y : Y) (U : EtaleNeighborhood Y y) (d : ℕ)
    (A : Fin d → (pullback f U.toBase).Opens)
    (hA : Set.PairwiseDisjoint Set.univ fun i => (A i : Set (pullback (C := Scheme) f U.toBase)))
    (hU : ∀ i, U.point ∈ Set.range ((A i).ι ≫ pullback.snd f U.toBase)) :
    ∃ O : Y.Opens, y ∈ (O : Set Y) ∧
      (O : Set Y) ⊆ {z : Y | (d : ℕ∞) ≤ geometricIrreducibleComponentCount f z} := by
  let p := pullback.snd f U.toBase
  let V : U.scheme.Opens :=
    ⟨{t | ∀ i, t ∈ Set.range ((A i).ι ≫ p)}, by
      have hopen (i : Fin d) : IsOpen (Set.range ((A i).ι ≫ p)) :=
        ((A i).ι ≫ p).isOpenMap.isOpen_range
      convert isOpen_iInter_of_finite hopen using 1
      ext t
      simp⟩
  refine exists_isOpen_le_geometricIrreducibleComponentCount f y U V d hU fun t ht => ?_
  obtain ⟨w, hw⟩ := exists_injective_geometricFiber_points_of_disjoint_opens p t
    (SeparableClosure (U.scheme.residueField t)) A hA ht
  exact le_geometricIrreducibleComponentCount_of_injective p t
    (SeparableClosure (U.scheme.residueField t)) d w hw

/-- Points of a geometric fibre lying in pieces with one-point geometric fibres lie in pairwise
distinct pieces when they are distinct. -/
private lemma injective_of_mem_opens_of_subsingleton {P U : Scheme.{u}} (p : P ⟶ U) (u : U)
    (K : Type u) [Field K] [Algebra (U.residueField u) K] {d : ℕ}
    (z : Fin d → geometricFiber p u K) (hz : Function.Injective z) {ι : Type*}
    (D : ι → P.Opens) (b : Fin d → ι)
    (hb : ∀ k, (pullback.fst (p.fiberToSpecResidueField u)
      (Spec.map (CommRingCat.ofHom (algebraMap (U.residueField u) K))) ≫ p.fiberι u) (z k) ∈
        (D (b k) : Set P))
    (hsub : ∀ k, Subsingleton (geometricFiber ((D (b k)).ι ≫ p) u K)) :
    Function.Injective b := by
  intro i j hij
  let q := pullback.fst (p.fiberToSpecResidueField u)
    (Spec.map (CommRingCat.ofHom (algebraMap (U.residueField u) K))) ≫ p.fiberι u
  have hmem (k : Fin d) :
      z k ∈ Set.range (geometricFiberMapOfComp (D (b k)).ι p u K).base := by
    rw [range_geometricFiberMapOfComp, Scheme.Hom.range_fiberMapComp]
    show q (z k) ∈ Set.range (D (b k)).ι.base
    exact ⟨⟨q (z k), hb k⟩, rfl⟩
  obtain ⟨w, hw⟩ := hmem i
  have hjmem := hmem j
  rw [← hij] at hjmem
  obtain ⟨w', hw'⟩ := hjmem
  exact hz (hw.symm.trans ((congrArg _ ((hsub i).elim w w')).trans hw'))

/-- **Stacks Project, Tag 0F36.** For a separated, locally quasi-finite and universally open
morphism of schemes, the locus where the number of geometric components of the fibre is at least
a fixed natural number is open. -/
@[stacks 0F36, ega "IV 18.10.17.1" "globally univ. open", sga "1 I 10.7" "more general"]
theorem isOpen_geometricIrreducibleComponentCount_ge {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [LocallyQuasiFinite f] [UniversallyOpen f] (d : ℕ) :
    IsOpen {y : Y | (d : ℕ∞) ≤ geometricIrreducibleComponentCount f y} := by
  classical
  refine isOpen_iff_forall_mem_open.mpr fun y hy => ?_
  let K := SeparableClosure (Y.residueField y)
  obtain ⟨z₀, hz₀⟩ := exists_injective_geometricFiber_points f y K d hy
  let r₀ := Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) K))
  let x₀ : Fin d → f.fiber y := fun i => pullback.fst (f.fiberToSpecResidueField y) r₀ (z₀ i)
  obtain ⟨n, x, hx, hxx⟩ := exists_injective_range_eq x₀
  obtain ⟨U, m, D, v, hdisj, hcover, hclopen, hpieces, hnone⟩ :=
    exists_etaleNeighborhood_purelyInseparable_decomposition f n y x hx
      (fun i => isIsolatedPoint_of_locallyQuasiFinite f y (x i))
  obtain ⟨a, e, he⟩ := exists_geometricFiber_etale_iso f U.toBase y U.point U.map_point K
  let := a
  let p := pullback.snd f U.toBase
  let r := Spec.map (CommRingCat.ofHom (algebraMap (U.scheme.residueField U.point) K))
  let q : geometricFiber p U.point K ⟶ pullback f U.toBase :=
    pullback.fst (p.fiberToSpecResidueField U.point) r ≫ p.fiberι U.point
  let z : Fin d → geometricFiber p U.point K := fun i => e.inv (z₀ i)
  have hz : Function.Injective z := e.inv.homeomorph.injective.comp hz₀
  have hzbase (i : Fin d) : p (q (z i)) = U.point :=
    (p.fiberHomeo U.point (pullback.fst (p.fiberToSpecResidueField U.point) r (z i))).2
  have hehom (i : Fin d) : e.hom (z i) = z₀ i := by
    show e.hom (e.inv (z₀ i)) = z₀ i
    simp
  have hzfst (i : Fin d) : pullback.fst f U.toBase (q (z i)) = f.fiberι y (x₀ i) := by
    have h := congrArg (fun k : geometricFiber p U.point K ⟶ X => k (z i)) he
    simp only [Scheme.Hom.comp_apply, hehom] at h
    exact h.symm
  have hex (i : Fin d) : ∃ b : Σ j, Fin (m j),
      q (z i) ∈ (D (some b) : Set (pullback (C := Scheme) f U.toBase)) := by
    obtain ⟨j, hj⟩ := hxx i
    have hmem : q (z i) ∈ ⋃ k, (D k).1 := by rw [hcover]; trivial
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hmem
    cases k with
    | none =>
      exact False.elim (hnone ⟨q (z i), hk⟩ (hzbase i) j
        ((hzfst i).trans (congrArg _ hj.symm)))
    | some b => exact ⟨b, hk⟩
  choose b hb using hex
  have hbinj : Function.Injective b :=
    injective_of_mem_opens_of_subsingleton p U.point K z hz (fun c => D (some c)) b hb fun k =>
      subsingleton_geometricFiber_of_singleton_fiber ((D (some (b k))).ι ≫ p) U.point
        (v (b k).1 (b k).2) (hpieces (b k).1 (b k).2).2.1 (hpieces (b k).1 (b k).2).2.2.2 K
  let A : Fin d → (pullback f U.toBase).Opens := fun i => D (some (b i))
  have hA : Set.PairwiseDisjoint Set.univ
      fun i => (A i : Set (pullback (C := Scheme) f U.toBase)) := fun i _ j _ hij =>
    hdisj (Set.mem_univ _) (Set.mem_univ _) fun h => hij (hbinj (Option.some.inj h))
  have hU (i : Fin d) : U.point ∈ Set.range ((A i).ι ≫ p) :=
    ⟨v (b i).1 (b i).2, (hpieces (b i).1 (b i).2).2.2.2.choose⟩
  obtain ⟨O, hyO, hO⟩ := exists_isOpen_le_count_of_disjoint_opens f y U d A hA hU
  exact ⟨O, hO, O.isOpen, hyO⟩

end AlgebraicGeometry

end
