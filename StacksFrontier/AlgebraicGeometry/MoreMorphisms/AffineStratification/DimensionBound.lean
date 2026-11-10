module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AffineStratification.Union
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.AlgebraicGeometry.Properties.GenericPoints

/-!
# The affine stratification number of a finite-dimensional Noetherian scheme

A Noetherian scheme of finite dimension `d` has affine stratification number at most `d`.

## Main results

* `AlgebraicGeometry.exists_affineOpen_isAffineHom_mem_genericPoints`: a Noetherian scheme has
  an affine open containing the generic points of all its irreducible components whose
  inclusion is an affine morphism.
* `AlgebraicGeometry.affineStratificationNumber_le_of_topologicalKrullDim`: the bound.

## Implementation notes

The induction is on the dimension. In dimension zero a Noetherian scheme is a finite discrete
scheme, hence affine, and one stratum suffices. In positive dimension one chooses an affine
open `U` containing the generic points of every irreducible component and with affine
inclusion, obtained by intersecting a finite affine covering adapted to those generic points;
its closed complement then has strictly smaller dimension, because a chain of irreducible
closed subsets of the complement extends by the irreducible component containing the image of
its top member, whose generic point is missing from the complement. Adjoining `U` as the top
stratum to an affine stratification of the complement gives the result.

Finite dimension is expressed as an inequality `topologicalKrullDim X ≤ d` with `d` a natural
number, which excludes infinite dimension; the empty scheme is allowed.

## References

* [Stacks Project, Tag 0F2X](https://stacks.math.columbia.edu/tag/0F2X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed

universe u v

namespace AlgebraicGeometry

/-- If a closed subspace of a sober space of dimension at most `d + 1` misses the generic point
of every irreducible component, then it has dimension at most `d`: a chain of irreducible
closed subsets of the subspace extends by an irreducible component containing the image of its
top member, which is strictly larger because its generic point is not in the image. -/
private lemma topologicalKrullDim_le_of_isClosedEmbedding_of_genericPoint_notMem
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] [QuasiSober B]
    {f : A → B} (hf : Topology.IsClosedEmbedding f) (d : ℕ)
    (hdim : topologicalKrullDim B ≤ ((d + 1 : ℕ) : WithBot ℕ∞))
    (hAvoid : ∀ C : irreducibleComponents B, C.2.1.genericPoint ∉ Set.range f) :
    topologicalKrullDim A ≤ (d : WithBot ℕ∞) := by
  classical
  unfold topologicalKrullDim Order.krullDim
  refine iSup_le fun p => ?_
  let map := IrreducibleCloseds.map f hf.continuous
  let q := p.map map (IrreducibleCloseds.map_strictMono_of_isInducing hf.isInducing)
  have hLast : (q.last : Set B) = f '' (p.last : Set A) := by
    change (map p.last : Set B) = f '' (p.last : Set A)
    rw [IrreducibleCloseds.coe_map, (hf.isClosedMap _ p.last.isClosed).closure_eq]
  obtain ⟨C, hC, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (q.last : Set B) q.last.isIrreducible
  let component : IrreducibleCloseds B :=
    ⟨C, hC.1, isClosed_of_mem_irreducibleComponents _ hC⟩
  have hlt : q.last < component := by
    refine lt_of_le_of_ne hsub fun heq => ?_
    have hηLast : hC.1.genericPoint ∈ (q.last : Set B) := by
      rw [heq]
      exact (hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hC)).mem
    rw [hLast] at hηLast
    exact hAvoid ⟨C, hC⟩ (Set.image_subset_range _ _ hηLast)
  have hlen := (Order.LTSeries.length_le_krullDim (q.snoc component hlt)).trans hdim
  have hnat : p.length + 1 ≤ d + 1 := by
    apply (Nat.cast_le (α := WithBot ℕ∞)).mp
    simpa [q] using hlen
  exact Nat.cast_le.mpr (by omega)

/-- Inside any open set containing the generic points of finitely many distinct irreducible
components of a quasi-separated scheme there is an affine open containing them. -/
private lemma exists_affineOpen_le_mem_genericPoints {X : Scheme.{u}} [QuasiSeparatedSpace X]
    {n : ℕ} (Z : Fin n → Set X) (hZ : ∀ i, Z i ∈ irreducibleComponents X)
    (hZinj : Function.Injective Z) (η : Fin n → X) (hη : ∀ i, IsGenericPoint (η i) (Z i))
    (O : X.Opens) (hηO : ∀ i, η i ∈ O) :
    ∃ U : X.Opens, IsAffineOpen U ∧ U ≤ O ∧ ∀ i, η i ∈ U := by
  classical
  obtain ⟨A, hAaff, hηA, hAdisj, -⟩ :=
    exists_pairwise_disjoint_affine_opens_of_generic_points Z hZ hZinj η hη
  have hbasis : ∀ i, ∃ V : X.Opens, IsAffineOpen V ∧ η i ∈ V ∧ V ≤ A i ⊓ O := by
    intro i
    obtain ⟨-, ⟨V, hV, rfl⟩, hηV, hVle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (show η i ∈ (A i ⊓ O : X.Opens) from ⟨hηA i, hηO i⟩) (A i ⊓ O).isOpen
    exact ⟨V, hV, hηV, hVle⟩
  choose V hVaff hηV hVle using hbasis
  have hVdisj : Pairwise fun i j : Fin n => Disjoint (V i) (V j) := fun i j hij =>
    Disjoint.mono ((hVle i).trans inf_le_left) ((hVle j).trans inf_le_left) (hAdisj hij)
  exact ⟨⨆ i, V i, IsAffineOpen.iSup_of_disjoint hVaff hVdisj,
    iSup_le fun i => (hVle i).trans inf_le_right, fun i => le_iSup V i (hηV i)⟩

/-- **A Noetherian scheme has an affine open with affine inclusion containing the generic
points of all its irreducible components.** The covering of the source constructed in
[Stacks, Tag 0F2X]. -/
theorem exists_affineOpen_isAffineHom_mem_genericPoints (X : Scheme.{u}) [IsNoetherian X] :
    ∃ U : X.Opens, IsAffineOpen U ∧ IsAffineHom U.ι ∧
      ∀ C : irreducibleComponents X, C.2.1.genericPoint ∈ U := by
  classical
  have : Finite (irreducibleComponents X) := finite_irreducibleComponents_of_isNoetherian
  have : Fintype (irreducibleComponents X) := Fintype.ofFinite _
  let e : Fin (Fintype.card (irreducibleComponents X)) ≃ irreducibleComponents X :=
    (Fintype.equivFin _).symm
  let Z : Fin (Fintype.card (irreducibleComponents X)) → Set X := fun i => (e i : Set X)
  let η : Fin (Fintype.card (irreducibleComponents X)) → X := fun i => (e i).2.1.genericPoint
  have hZ : ∀ i, Z i ∈ irreducibleComponents X := fun i => (e i).2
  have hZinj : Function.Injective Z := fun i j hij => e.injective (Subtype.ext hij)
  have hη : ∀ i, IsGenericPoint (η i) (Z i) := fun i =>
    (e i).2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ (e i).2)
  choose V hVaff hxV hVη using
    exists_affineOpen_mem_of_genericPoints_irreducibleComponents X Z hZ hZinj η hη
  obtain ⟨s, hs⟩ := (isCompact_univ : IsCompact (Set.univ : Set X)).elim_finite_subcover
    (fun x : X => (V x : Set X)) (fun x => (V x).2)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hxV x⟩)
  let eS : Fin s.card ≃ s := s.equivFin.symm
  let W : Fin s.card → X.Opens := fun i => V (eS i).1
  let O : X.Opens := Finset.univ.inf W
  have hOη (i : Fin (Fintype.card (irreducibleComponents X))) : η i ∈ O := by
    change η i ∈ ((Finset.univ.inf W : X.Opens) : Set X)
    simp only [Opens.coe_finset_inf, Finset.inf_set_eq_iInter, Set.mem_iInter]
    exact fun j _ => hVη (eS j).1 i
  obtain ⟨U, hUaff, hUO, hUη⟩ := exists_affineOpen_le_mem_genericPoints Z hZ hZinj η hη O hOη
  have hUaffHom : IsAffineHom U.ι := by
    apply isAffineHom_of_forall_exists_isAffineOpen
    intro x
    obtain ⟨i, his, hx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    let j := eS.symm ⟨i, his⟩
    have hle : U ≤ W j := hUO.trans (Finset.inf_le (Finset.mem_univ j))
    refine ⟨W j, by simpa [W, j] using hx, hVaff (eS j).1, ?_⟩
    have hpre : U.ι ⁻¹ᵁ W j = ⊤ := by
      ext y
      exact ⟨fun _ => Set.mem_univ y, fun _ => hle y.property⟩
    rw [hpre]
    have : IsAffine U.toScheme := hUaff
    exact isAffineOpen_top U.toScheme
  exact ⟨U, hUaff, hUaffHom, fun C => by simpa [η] using hUη (e.symm C)⟩

/-- Affineness of the reduced induced scheme on a locally closed subset, and of its inclusion,
depends only on the subset. -/
private lemma isAffine_reducedInduced_congr {X : Scheme.{u}} {T S : Set X}
    (hT : IsLocallyClosed T) (hS : IsLocallyClosed S) (h : T = S) :
    (IsAffine (reducedInducedScheme T hT) ∧ IsAffineHom (reducedInducedInclusion T hT)) ↔
      (IsAffine (reducedInducedScheme S hS) ∧ IsAffineHom (reducedInducedInclusion S hS)) := by
  subst h
  rfl

/-- Adjoining an open as the top stratum to the image of a stratification of its closed
complement covers the scheme. -/
private lemma iUnion_lastCases_image_eq_univ
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsClosedImmersion f] (U : X.Opens)
    (hRange : Set.range f = (U : Set X)ᶜ) {n : ℕ} (s : AffineStratification Y (Fin (n + 1))) :
    ⋃ i, (Fin.lastCases (U : Set X) fun i => f '' s.strata i : Fin (n + 2) → Set X) i =
      Set.univ := by
  let strata : Fin (n + 2) → Set X := Fin.lastCases (U : Set X) fun i => f '' s.strata i
  change ⋃ i, strata i = Set.univ
  refine Set.eq_univ_of_forall fun x => ?_
  by_cases hx : x ∈ U
  · exact Set.mem_iUnion.mpr ⟨Fin.last (n + 1), by simpa [strata] using hx⟩
  · obtain ⟨y, rfl⟩ := hRange.ge (Set.mem_compl hx)
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
      (s.isLocallyFiniteStratification.isStratification.isPartition.cover ▸ Set.mem_univ y)
    exact Set.mem_iUnion.mpr ⟨i.castSucc, by
      simpa [strata] using (show f y ∈ f '' s.strata i from ⟨y, hi, rfl⟩)⟩

/-- Adjoining an open as the top stratum to the image of a stratification of its closed
complement gives a locally finite stratification. -/
private lemma isLocallyFiniteStratification_lastCases_image
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsClosedImmersion f] (U : X.Opens)
    (hRange : Set.range f = (U : Set X)ᶜ) {n : ℕ} (s : AffineStratification Y (Fin (n + 1))) :
    IsLocallyFiniteStratification
      (Fin.lastCases (U : Set X) fun i => f '' s.strata i : Fin (n + 2) → Set X) := by
  let strata : Fin (n + 2) → Set X := Fin.lastCases (U : Set X) fun i => f '' s.strata i
  have hCover : ⋃ i, strata i = Set.univ := iUnion_lastCases_image_eq_univ f U hRange s
  change IsLocallyFiniteStratification strata
  refine ⟨⟨⟨?_, ?_, hCover⟩, ?_⟩, locallyFinite_of_finite _⟩
  · intro i
    induction i using Fin.lastCases with
    | last => simpa [strata] using U.isOpen.isLocallyClosed
    | cast i =>
      simpa [strata] using
        (s.isLocallyFiniteStratification.isStratification.isPartition.locallyClosed i).image
          f.isClosedEmbedding.isInducing f.isClosedEmbedding.isClosed_range.isLocallyClosed
  · have hdisj (j : Fin (n + 1)) : Disjoint (strata (Fin.last (n + 1))) (strata j.castSucc) := by
      simp only [strata, Fin.lastCases_last, Fin.lastCases_castSucc]
      exact disjoint_compl_right.mono_right (hRange ▸ Set.image_subset_range _ _)
    intro i j hij
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact (hij rfl).elim
      | cast j => exact hdisj j
    | cast i =>
      induction j using Fin.lastCases with
      | last => exact (hdisj i).symm
      | cast j =>
        refine Set.disjoint_left.mpr fun x hxi hxj => ?_
        obtain ⟨y, hy, rfl⟩ := (show x ∈ f '' s.strata i by simpa [strata] using hxi)
        obtain ⟨z, hz, heq⟩ := (show f y ∈ f '' s.strata j by simpa [strata] using hxj)
        obtain rfl : z = y := f.isClosedEmbedding.injective heq
        exact (s.isLocallyFiniteStratification.isStratification.isPartition.disjoint
          i j fun heq => hij (congrArg Fin.castSucc heq)).le_bot ⟨hy, hz⟩
  · intro i x hx
    induction i using Fin.lastCases with
    | last =>
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hCover ▸ Set.mem_univ x)
      exact Set.mem_iUnion₂.mpr ⟨j, Set.mem_ofPred_eq.mpr (Fin.le_last _), hj⟩
    | cast i =>
      have hxImage : x ∈ f '' closure (s.strata i) := by
        rw [← f.isClosedEmbedding.closure_image_eq]
        simpa [strata] using hx
      obtain ⟨y, hy, rfl⟩ := hxImage
      have hyLower := s.isLocallyFiniteStratification.isStratification.closure_subset i hy
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hyLower
      obtain ⟨j, hji, hyj⟩ := hyLower
      exact Set.mem_iUnion₂.mpr ⟨j.castSucc, Set.mem_ofPred_eq.mpr (by simpa using hji),
        by simpa [strata] using (show f y ∈ f '' s.strata j from ⟨y, hyj, rfl⟩)⟩

/-- Adjoining an affine open with affine inclusion as the top stratum to an affine
stratification of its closed complement. -/
private noncomputable def affineStratificationOfClosedComplement
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsClosedImmersion f]
    (U : X.Opens) (hU : IsAffineOpen U) [IsAffineHom U.ι]
    (hRange : Set.range f = (U : Set X)ᶜ) {n : ℕ}
    (s : AffineStratification Y (Fin (n + 1))) : AffineStratification X (Fin (n + 2)) := by
  classical
  let strata : Fin (n + 2) → Set X := Fin.lastCases (U : Set X) fun i => f '' s.strata i
  have hlf : IsLocallyFiniteStratification strata :=
    isLocallyFiniteStratification_lastCases_image f U hRange s
  have hAff (i : Fin (n + 2)) : IsAffine (reducedInducedScheme (strata i)
      (hlf.isStratification.isPartition.locallyClosed i)) ∧
      IsAffineHom (reducedInducedInclusion (strata i)
        (hlf.isStratification.isPartition.locallyClosed i)) := by
    induction i using Fin.lastCases with
    | last =>
      exact (isAffine_reducedInduced_congr
        (hlf.isStratification.isPartition.locallyClosed (Fin.last (n + 1)))
        U.isOpen.isLocallyClosed (by simp [strata])).mpr
        (isAffine_reducedInduced_of_isAffineOpen U hU)
    | cast i =>
      let hT := s.isLocallyFiniteStratification.isStratification.isPartition.locallyClosed i
      let g := reducedInducedInclusion (s.strata i) hT
      have : IsAffine (reducedInducedScheme (s.strata i) hT) := s.isAffine i
      have : IsAffineHom g := s.isAffineHom i
      have : IsImmersion (g ≫ f) := inferInstance
      have : IsAffineHom (g ≫ f) := inferInstance
      have hRangeComp : Set.range (g ≫ f) = strata i.castSucc := by
        change Set.range (f.base ∘ g.base) = _
        rw [Set.range_comp, range_reducedInducedInclusion]
        simp [strata]
      exact isAffine_reducedInduced_of_range_eq (strata i.castSucc) _ (g ≫ f) hRangeComp
  exact { strata := strata
          isLocallyFiniteStratification := hlf
          isAffine := fun i => (hAff i).1
          isAffineHom := fun i => (hAff i).2 }

/-- A Noetherian scheme of dimension at most `d` has an affine stratification indexed by
`Fin (d + 1)`. -/
private lemma exists_affineStratification_of_topologicalKrullDim_le (d : ℕ) (X : Scheme.{u})
    [IsNoetherian X] (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) :
    Nonempty (AffineStratification X (Fin (d + 1))) := by
  classical
  induction d generalizing X with
  | zero =>
    have : IsLocallyArtinian X :=
      IsLocallyArtinian.of_topologicalKrullDim_le_zero (by simpa using hdim)
    have : Finite X := finite_of_compact_of_discrete
    have : Subsingleton (Fin (0 + 1)) := inferInstanceAs (Subsingleton (Fin 1))
    exact ⟨AffineStratification.ofIsAffine X⟩
  | succ d ih =>
    obtain ⟨U, hU, _, hGeneric⟩ := exists_affineOpen_isAffineHom_mem_genericPoints X
    let C : Closeds X := ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩
    let K := Scheme.IdealSheafData.vanishingIdeal C
    let f : K.subscheme ⟶ X := K.subschemeι
    have hRange : Set.range f = (U : Set X)ᶜ :=
      Scheme.IdealSheafData.range_subschemeι_vanishingIdeal C
    have : IsLocallyNoetherian K.subscheme := LocallyOfFiniteType.isLocallyNoetherian f
    have : NoetherianSpace K.subscheme := f.isClosedEmbedding.isInducing.noetherianSpace
    have : IsNoetherian K.subscheme := ⟨⟩
    have hYdim : topologicalKrullDim K.subscheme ≤ (d : WithBot ℕ∞) :=
      topologicalKrullDim_le_of_isClosedEmbedding_of_genericPoint_notMem
        f.isClosedEmbedding d hdim fun c hmem => hRange.le hmem (hGeneric c)
    obtain ⟨s⟩ := ih K.subscheme hYdim
    exact ⟨affineStratificationOfClosedComplement f U hU hRange s⟩

/-- **[Stacks, Tag 0F2X].** A Noetherian scheme of finite dimension `d` has affine
stratification number at most `d`. -/
@[stacks 0F2X]
theorem affineStratificationNumber_le_of_topologicalKrullDim (X : Scheme.{u}) [IsNoetherian X]
    (d : ℕ) (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) :
    affineStratificationNumber X ≤ d :=
  Nat.sInf_le (exists_affineStratification_of_topologicalKrullDim_le d X hdim)

end AlgebraicGeometry

end
