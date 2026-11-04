module

public import Mathlib.Order.Cover
public import Mathlib.Order.RelSeries
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.Topology.Sets.Closeds
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen
public import StacksFrontier.RingTheory.KrullDimension.FiniteTypeNeTop
public import StacksFrontier.RingTheory.KrullDimension.FiniteTypeOverField
public import StacksFrontier.Topology.Noetherian.CatenaryOpenCovering

/-!
# Maximal chains in an irreducible scheme over a field

Let `X` be an irreducible scheme locally of finite type over a field. Every finite strict chain
of irreducible closed subsets of `X` extends to a maximal chain, and every maximal chain has
length equal to the dimension of `X`.

## Main results

* `AlgebraicGeometry.exists_maximalChain_extending`: extension of a chain of irreducible closed
  subsets to a maximal chain.
* `AlgebraicGeometry.maximalChain_length_eq_topologicalKrullDim` identifies the length of every
  maximal chain of irreducible closed subsets with the topological Krull dimension.

## Implementation notes

A finite strict chain is represented by an `LTSeries` in `TopologicalSpace.IrreducibleCloseds X`,
and a maximal chain by a `RelSeries` for the covering relation: its consecutive terms cannot be
refined, while `IsMin` and `IsMax` say that it cannot be extended at either end. Containment of
the original chain is expressed as containment of the ranges of the two series, and the length of
a chain counts strict inclusions, as does `topologicalKrullDim`.

Both statements are reduced to an affine chart, where the order of irreducible closed subsets is
dual to the prime spectrum of a finitely generated algebra over the field; the restriction of a
maximal chain to an open subset meeting its head stays maximal.

## References

* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The Krull dimension of a finitely generated algebra over a field is finite. -/
private alias ringKrullDim_ne_top_of_finiteType_aux := _root_.ringKrullDim_ne_top_of_finiteType

/-- Inserting a term into a strict chain does not lose any of its terms. -/
private lemma range_subset_insertNth_ltSeries {α : Type*} [Preorder α]
    (p : LTSeries α) (i : Fin p.length) (a : α)
    (h₁ : p i.castSucc < a) (h₂ : a < p i.succ) :
    Set.range p ⊆ Set.range (p.insertNth i a h₁ h₂) := by
  rintro x ⟨j, rfl⟩
  refine ⟨i.castSucc.succ.succAbove j, ?_⟩
  simp [RelSeries.insertNth]

/-- In a finite-dimensional order, every strict chain extends to a chain for the covering
relation which cannot be extended at either end. -/
private lemma exists_maximalRelSeries_extending {α : Type*} [PartialOrder α]
    [FiniteDimensionalOrder α] (p : LTSeries α) :
    ∃ q : RelSeries {(a, b) : α × α | a ⋖ b},
      IsMin q.head ∧ IsMax q.last ∧ Set.range p ⊆ Set.range q := by
  let L : Set ℕ := {n | ∃ q : LTSeries α, Set.range p ⊆ Set.range q ∧ q.length = n}
  have hLnonempty : L.Nonempty := ⟨p.length, p, subset_rfl, rfl⟩
  have hLfinite : L.Finite :=
    (Set.finite_le_nat (LTSeries.longestOf α).length).subset fun n hn => by
    obtain ⟨q, -, rfl⟩ := hn
    exact LTSeries.longestOf_is_longest q
  obtain ⟨n, ⟨q, hpq, rfl⟩, hnmax⟩ := L.exists_max_image id hLfinite hLnonempty
  have hlong (r : LTSeries α) (hqr : Set.range q ⊆ Set.range r) : r.length ≤ q.length :=
    hnmax r.length ⟨r, hpq.trans hqr, rfl⟩
  have hcov : ∀ i : Fin q.length, q i.castSucc ⋖ q i.succ := by
    intro i
    refine ⟨q.step i, ?_⟩
    intro z hqz hzi
    have h1 : q i.castSucc < z := hqz
    have h2 : z < q i.succ := hzi
    let r := q.insertNth i z h1 h2
    have hr := hlong r (range_subset_insertNth_ltSeries q i z h1 h2)
    rw [show r.length = q.length + 1 by simp [r]] at hr
    omega
  have hmin : IsMin q.head := by
    rw [isMin_iff_forall_not_lt]
    intro a haq
    let r := q.cons a haq
    have hrlen : r.length = q.length + 1 := by
      simp [r, RelSeries.cons, RelSeries.append, RelSeries.singleton]
    have hqr : Set.range q ⊆ Set.range r := by
      rintro x ⟨i, rfl⟩
      refine ⟨Fin.cast (congrArg Nat.succ hrlen.symm) i.succ, ?_⟩
      show (q.cons a haq) (Fin.cast (congrArg Nat.succ hrlen.symm) i.succ) = q i
      simpa using RelSeries.cons_cast_succ q a haq i
    have hr := hlong r hqr
    omega
  have hmax : IsMax q.last := by
    rw [isMax_iff_forall_not_lt]
    intro a hqa
    let r := q.snoc a hqa
    have hrlen : r.length = q.length + 1 := by
      simp [r, RelSeries.snoc, RelSeries.append, RelSeries.singleton]
    have hqr : Set.range q ⊆ Set.range r := by
      rintro x ⟨i, rfl⟩
      refine ⟨Fin.castSucc i, ?_⟩
      show (q.snoc a hqa) (Fin.castSucc i) = q i
      exact RelSeries.snoc_castSucc q a hqa i
    have hr := hlong r hqr
    omega
  exact ⟨⟨q.length, q, hcov⟩, hmin, hmax, hpq⟩

/-- Any finite chain of irreducible closed subsets of an irreducible locally algebraic scheme
over a field extends to a maximal chain. -/
@[stacks 0A21 "extend_irreducible_chain"]
lemma exists_maximalChain_extending
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [IrreducibleSpace X]
    (p : LTSeries (IrreducibleCloseds X)) :
    ∃ q : RelSeries {(Y, Z) : IrreducibleCloseds X × IrreducibleCloseds X | Y ⋖ Z},
      IsMin q.head ∧ IsMax q.last ∧ Set.range p ⊆ Set.range q := by
  let α := IrreducibleCloseds X
  have hαnonempty : Nonempty α :=
    ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩⟩
  obtain ⟨x⟩ := (IrreducibleSpace.toNonempty (X := X))
  obtain ⟨_, ⟨V : X.Opens, hV, rfl⟩, hxV, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let U' : X.affineOpens := ⟨V, hV⟩
  have hU'nonempty : (U' : Set X).Nonempty := ⟨x, hxV⟩
  let : Field Γ(Spec (.of k), ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField k)).toField
  let : Algebra (Γ(Spec (.of k), ⊤)) (Γ(X, U')) := (f.appLE ⊤ U' (by simp)).hom.toAlgebra
  have : Algebra.FiniteType (Γ(Spec (.of k), ⊤)) (Γ(X, U')) :=
    RingHom.finiteType_algebraMap.mp (f.finiteType_appLE (isAffineOpen_top _) U'.2 (by simp))
  have hdimU : topologicalKrullDim (U' : Set X) = ringKrullDim Γ(X, U') := by
    calc
      topologicalKrullDim (U' : Set X) = topologicalKrullDim (Spec Γ(X, U')) :=
        IsHomeomorph.topologicalKrullDim_eq _ U'.2.isoSpec.hom.homeomorph.isHomeomorph
      _ = ringKrullDim Γ(X, U') := by
        show topologicalKrullDim (PrimeSpectrum Γ(X, U')) = ringKrullDim Γ(X, U')
        exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(X, U')
  have hdimXne : topologicalKrullDim X ≠ ⊤ := by
    rw [topologicalKrullDim_eq_of_isOpen k X f (U' : Set X) U'.1.2 hU'nonempty, hdimU]
    exact ringKrullDim_ne_top_of_finiteType_aux
      (κ := Γ(Spec (.of k), ⊤)) (A := Γ(X, U'))
  have : FiniteDimensionalOrder α := by
    rw [Order.finiteDimensionalOrder_iff_krullDim_ne_bot_and_top]
    refine ⟨Order.krullDim_ne_bot_iff.mpr hαnonempty, ?_⟩
    show topologicalKrullDim X ≠ ⊤
    exact hdimXne
  exact exists_maximalRelSeries_extending p

/-- Mapping an irreducible closed subset along a homeomorphism and back is the identity. -/
private lemma map_symm_map_eq {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) (Z : IrreducibleCloseds A) :
    IrreducibleCloseds.map e.symm e.symm.continuous
      (IrreducibleCloseds.map e e.continuous Z) = Z := by
  apply SetLike.coe_injective
  simp only [IrreducibleCloseds.coe_map]
  rw [closure_eq_iff_isClosed.mpr (e.isClosedMap Z Z.isClosed'),
    closure_eq_iff_isClosed.mpr (e.symm.isClosedMap _ (e.isClosedMap Z Z.isClosed'))]
  ext x
  simp

/-- A homeomorphism induces an order isomorphism of irreducible closed subsets. -/
private noncomputable def irreducibleClosedsOrderIsoOfHomeomorph
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] (e : A ≃ₜ B) :
    IrreducibleCloseds A ≃o IrreducibleCloseds B where
  toFun := IrreducibleCloseds.map e e.continuous
  invFun := IrreducibleCloseds.map e.symm e.symm.continuous
  left_inv := map_symm_map_eq e
  right_inv := map_symm_map_eq e.symm
  map_rel_iff' := by
    intro Z W
    change closure (e '' (Z : Set A)) ⊆ closure (e '' (W : Set A)) ↔ (Z : Set A) ⊆ W
    rw [closure_eq_iff_isClosed.mpr (e.isClosedMap Z Z.isClosed'),
      closure_eq_iff_isClosed.mpr (e.isClosedMap W W.isClosed')]
    exact Set.image_subset_image_iff e.injective

/-- For `U` open, `closureInAmbient U` is an order embedding. -/
private lemma closureInAmbient_le_iff {A : Type*} [TopologicalSpace A]
    (U : Set A) (hU : IsOpen U) (Z W : IrreducibleCloseds U) :
    CatenaryTopologicalSpace.closureInAmbient U Z ≤
      CatenaryTopologicalSpace.closureInAmbient U W ↔ Z ≤ W := by
  refine ⟨fun h ↦ ?_, fun h ↦
    (CatenaryTopologicalSpace.closureInAmbient_strictMono U hU).monotone h⟩
  rw [← CatenaryTopologicalSpace.restrictToOpen_closureInAmbient U hU Z,
    ← CatenaryTopologicalSpace.restrictToOpen_closureInAmbient U hU W, ← SetLike.coe_subset_coe,
    CatenaryTopologicalSpace.coe_restrictToOpen, CatenaryTopologicalSpace.coe_restrictToOpen]
  exact Set.preimage_mono h

/-- Restriction to an open subset preserves minimality of an irreducible closed subset. -/
private lemma isMin_restrictToOpen {A : Type*} [TopologicalSpace A]
    (U : Set A) (hU : IsOpen U) (T : IrreducibleCloseds A)
    (hT : (T.carrier ∩ U).Nonempty) (hmin : IsMin T) :
    IsMin (CatenaryTopologicalSpace.restrictToOpen U hU T hT) := by
  intro Z hZ
  rw [← closureInAmbient_le_iff U hU] at hZ ⊢
  rw [CatenaryTopologicalSpace.closureInAmbient_restrictToOpen U hU T hT] at hZ ⊢
  exact hmin hZ

/-- Restriction to an open subset preserves maximality of an irreducible closed subset. -/
private lemma isMax_restrictToOpen {A : Type*} [TopologicalSpace A]
    (U : Set A) (hU : IsOpen U) (T : IrreducibleCloseds A)
    (hT : (T.carrier ∩ U).Nonempty) (hmax : IsMax T) :
    IsMax (CatenaryTopologicalSpace.restrictToOpen U hU T hT) := by
  intro Z hZ
  rw [← closureInAmbient_le_iff U hU] at hZ ⊢
  rw [CatenaryTopologicalSpace.closureInAmbient_restrictToOpen U hU T hT] at hZ ⊢
  exact hmax hZ

/-- On the spectrum of a finitely generated algebra over a field whose spectrum is irreducible,
every maximal chain of primes has length the Krull dimension of the ring. -/
private lemma maximalChain_length_eq_ringKrullDim_of_irreducible
    (k : Type*) [Field k] (R : Type*) [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] [IrreducibleSpace (PrimeSpectrum R)]
    (s : RelSeries {p : PrimeSpectrum R × PrimeSpectrum R | p.1 ⋖ p.2})
    (hmin : IsMin s.head) (hmax : IsMax s.last) :
    (s.length : WithBot ℕ∞) = ringKrullDim R := by
  let I : Ideal R := nilradical R
  have : I.IsPrime := PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp inferInstance
  have : IsDomain (R ⧸ I) := Ideal.Quotient.isDomain I
  have : Algebra.FiniteType k (R ⧸ I) := Algebra.FiniteType.quotient k I
  let φ : R →+* R ⧸ I := Ideal.Quotient.mk I
  let emb : PrimeSpectrum (R ⧸ I) ↪o PrimeSpectrum R :=
    { toFun := PrimeSpectrum.comap φ
      inj' := PrimeSpectrum.comap_injective_of_surjective φ Ideal.Quotient.mk_surjective
      map_rel_iff' := by
        intro a b
        exact Ideal.comap_le_comap_iff_of_surjective φ
          Ideal.Quotient.mk_surjective a.asIdeal b.asIdeal }
  let e : PrimeSpectrum (R ⧸ I) ≃o PrimeSpectrum R :=
    OrderIso.ofSurjective emb
      (PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical (I := I) le_rfl).2
  let t : RelSeries {p : PrimeSpectrum (R ⧸ I) × PrimeSpectrum (R ⧸ I) | p.1 ⋖ p.2} :=
    s.map ⟨e.symm, fun h ↦ (apply_covBy_apply_iff e.symm).mpr h⟩
  have htmin : IsMin t.head := by
    show IsMin (e.symm s.head)
    exact e.symm.isMin_apply.mpr hmin
  have htmax : IsMax t.last := by
    show IsMax (e.symm s.last)
    exact e.symm.isMax_apply.mpr hmax
  exact ((Algebra.FiniteType.ringKrullDim_eq_height_of_isMaximal_and_length_eq_ringKrullDim
    k (R ⧸ I)).2 t htmin htmax).trans (Order.krullDim_eq_of_orderIso e)

/-- Every maximal chain of irreducible closed subsets of an irreducible locally algebraic
scheme over a field has length equal to the dimension of the scheme. -/
@[stacks 0A21 "maximal_chain_length"]
theorem maximalChain_length_eq_topologicalKrullDim
    (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [IrreducibleSpace X]
    (s : RelSeries {p : IrreducibleCloseds X × IrreducibleCloseds X | p.1 ⋖ p.2})
    (hmin : IsMin s.head) (hmax : IsMax s.last) :
    (s.length : WithBot ℕ∞) = topologicalKrullDim X := by
  let p : LTSeries (IrreducibleCloseds X) := s.ofLE fun _ h ↦ h.lt
  obtain ⟨x, hx⟩ := s.head.isIrreducible'.nonempty
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hmeet : (s.head.carrier ∩ U).Nonempty := ⟨x, hx, hxU⟩
  have hle : s.head ≤ s.last := p.monotone (Fin.zero_le _)
  obtain ⟨q, hq, hq_len⟩ := CatenaryTopologicalSpace.map_restrictToOpen_maximal
    U U.2 s.head s.last hle hmeet p ⟨rfl, rfl, fun i ↦ s.step i⟩
  let e : IrreducibleCloseds U ≃o (PrimeSpectrum Γ(X, U))ᵒᵈ :=
    (irreducibleClosedsOrderIsoOfHomeomorph hU.isoSpec.hom.homeomorph).trans
      (PrimeSpectrum.pointsEquivIrreducibleCloseds Γ(X, U)).symm.dual
  let r : RelSeries {p : IrreducibleCloseds U × IrreducibleCloseds U | p.1 ⋖ p.2} :=
    ⟨q.length, q.toFun, hq.2.2⟩
  let td : RelSeries {p : (PrimeSpectrum Γ(X, U))ᵒᵈ × (PrimeSpectrum Γ(X, U))ᵒᵈ | p.1 ⋖ p.2} :=
    r.map ⟨e, fun h ↦ (apply_covBy_apply_iff e).mpr h⟩
  let t : RelSeries {p : PrimeSpectrum Γ(X, U) × PrimeSpectrum Γ(X, U) | p.1 ⋖ p.2} :=
    td.reverse.ofLE (by
      intro a h
      change a.2 ⋖ a.1 at h
      exact ⟨h.lt, fun c hac hcb ↦ h.2 hcb hac⟩)
  have : Nonempty (U : Set X) := ⟨⟨x, hxU⟩⟩
  have : IrreducibleSpace (U : Set X) := U.isOpen.isOpenEmbedding_subtypeVal.irreducibleSpace
  have hUirr : IrreducibleSpace U := by
    show IrreducibleSpace (U : Set X)
    exact inferInstance
  have : IrreducibleSpace (PrimeSpectrum Γ(X, U)) :=
    hU.isoSpec.hom.homeomorph.irreducibleSpace_iff.mp hUirr
  let : Algebra k Γ(X, U) :=
    ((f.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
  have : Algebra.FiniteType k Γ(X, U) := by
    apply RingHom.FiniteType.comp
      (f.finiteType_appLE (isAffineOpen_top (Spec (.of k))) hU (by simp))
    exact RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.surjective
  have hqmin : IsMin q.head := by
    rw [hq.1]
    exact isMin_restrictToOpen U U.isOpen s.head hmeet hmin
  have hqmax : IsMax q.last := by
    rw [hq.2.1]
    exact isMax_restrictToOpen U U.isOpen s.last
      (CatenaryTopologicalSpace.meets_open_of_ge U s.head hmeet s.last hle) hmax
  have htmin : IsMin t.head := by
    show IsMin (OrderDual.ofDual (e q.last))
    exact e.isMax_apply.mpr hqmax
  have htmax : IsMax t.last := by
    show IsMax (OrderDual.ofDual td.reverse.last)
    rw [RelSeries.last_reverse, RelSeries.head_map]
    exact e.isMin_apply.mpr hqmin
  calc
    (s.length : WithBot ℕ∞) = (t.length : WithBot ℕ∞) := by
      show (s.length : WithBot ℕ∞) = (q.length : WithBot ℕ∞)
      rw [hq_len]
      rfl
    _ = ringKrullDim Γ(X, U) :=
      maximalChain_length_eq_ringKrullDim_of_irreducible k Γ(X, U) t htmin htmax
    _ = topologicalKrullDim U := by
      rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
      exact (IsHomeomorph.topologicalKrullDim_eq _ hU.isoSpec.hom.homeomorph.isHomeomorph).symm
    _ = topologicalKrullDim X :=
      (topologicalKrullDim_eq_of_isOpen k X f U U.isOpen ⟨x, hxU⟩).symm

end AlgebraicGeometry

end
