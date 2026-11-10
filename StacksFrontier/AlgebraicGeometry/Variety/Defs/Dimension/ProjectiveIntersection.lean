module

public import Mathlib.RingTheory.GradedAlgebra.Radical
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NowhereDenseFibres.Topology
public import StacksFrontier.AlgebraicGeometry.ProjBaseChange.IsIso
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Dimension.AffineCone
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpectrum.Topology
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.AffineIntersection
public import StacksFrontier.RingTheory.Equidimensional.FlatLocal
public import StacksFrontier.RingTheory.MvPolynomial.HypersurfaceDimension

/-!
# Intersections of closed subsets of projective space

Let `k` be a field and let `X` and `Y` be nonempty closed subsets of `ℙⁿ_k` of dimensions `r`
and `s`. If `n ≤ r + s` then `X ∩ Y` is nonempty and has dimension at least `r + s - n`
([Stacks, Tag 0B2R]). This is the projective counterpart of [Stacks, Tag 0B2Q],
`AlgebraicGeometry.add_le_add_topologicalKrullDim_irreducibleComponent_inter`.

## Main results

* `AlgebraicGeometry.inter_nonempty_projectiveSpaceOverRing`: the intersection is nonempty.
* `AlgebraicGeometry.le_topologicalKrullDim_inter_projectiveSpaceOverRing`: the intersection has
  dimension at least `r + s - n`.

## Implementation notes

The statements are about `AlgebraicGeometry.projectiveSpaceOverRing n (CommRingCat.of k)`, which
`Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison` identifies homeomorphically with
`Proj` of the total-degree grading of `k[T₀, …, Tₙ]`, where homogeneous ideals are available.
Dimensions are `topologicalKrullDim` of the subspaces, with values in `WithBot ℕ∞`.

The proof passes to the affine cones in `Spec k[T₀, …, Tₙ]`, which both contain the origin, the
irrelevant ideal, and applies [Stacks, Tag 0B2Q] to the irreducible component of their
intersection through the origin. The homogeneous core ([Stacks, Tag 00JT]) of the generic prime of
that component defines a nonempty projective zero locus contained in `X ∩ Y`.

## References

* [Stacks Project, Tag 0B2R](https://stacks.math.columbia.edu/tag/0B2R)
* [Stacks Project, Tag 0B2Q](https://stacks.math.columbia.edu/tag/0B2Q)
* [Stacks Project, Tag 00JT](https://stacks.math.columbia.edu/tag/00JT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry TopologicalSpace

universe u v

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.ProjectiveIntersection

/-- The grading of `k[T₀, …, T_{N-1}]` by total degree. -/
abbrev 𝒜 (N : ℕ) (k : Type u) [Field k] : ℕ → Submodule k (MvPolynomial (Fin N) k) :=
  MvPolynomial.homogeneousSubmodule (Fin N) k

/-! ### Dimensions of subspaces -/

section Topology

variable {T : Type v} [TopologicalSpace T]

/-- An irreducible closed subset of a closed subspace, pushed forward to the ambient space. -/
private def pushCl {s : Set T} (hs : IsClosed s) (W : IrreducibleCloseds s) :
    IrreducibleCloseds T where
  carrier := Subtype.val '' (W : Set s)
  isIrreducible' := W.isIrreducible'.image _ continuous_subtype_val.continuousOn
  isClosed' := hs.isClosedEmbedding_subtypeVal.isClosedMap _ W.isClosed'

/-- Pushing forward irreducible closed subsets of a closed subspace to the ambient space is
strictly monotone. -/
private lemma pushCl_strictMono {s : Set T} (hs : IsClosed s) : StrictMono (pushCl hs) := by
  refine strictMono_of_le_iff_le fun W W' => ?_
  change (W : Set s) ⊆ W' ↔ Subtype.val '' (W : Set s) ⊆ Subtype.val '' (W' : Set s)
  exact (Set.image_subset_image_iff Subtype.val_injective).symm

/-- The height of an irreducible closed subset of a closed subspace bounds the dimension of its
image in the ambient space. -/
private lemma height_le_topologicalKrullDim_pushCl {s : Set T} (hs : IsClosed s)
    (W : IrreducibleCloseds s) :
    (Order.height W : WithBot ℕ∞) ≤ topologicalKrullDim (pushCl hs W : Set T) := by
  rw [topologicalKrullDim_coe_eq_height]
  exact WithBot.coe_le_coe.mpr
    (Order.height_le_height_apply_of_strictMono _ (pushCl_strictMono hs) W)

/-- An irreducible closed subset of a closed subspace has dimension at most that of its image in
the ambient space. -/
private lemma topologicalKrullDim_le_image_val {s : Set T} (hs : IsClosed s) {Z : Set s}
    (hZi : IsIrreducible Z) (hZc : IsClosed Z) :
    topologicalKrullDim Z ≤ topologicalKrullDim (Subtype.val '' Z) := by
  have h := height_le_topologicalKrullDim_pushCl hs ⟨Z, hZi, hZc⟩
  rwa [← topologicalKrullDim_coe_eq_height (⟨Z, hZi, hZc⟩ : IrreducibleCloseds s)] at h

/-- A closed subspace of dimension at least `r` contains an irreducible closed subset of the
ambient space of dimension at least `r`. -/
private lemma exists_isIrreducible_isClosed_of_le_topologicalKrullDim {s : Set T}
    (hs : IsClosed s) {r : ℕ} (hd : (r : WithBot ℕ∞) ≤ topologicalKrullDim s) :
    ∃ W : Set T, IsIrreducible W ∧ IsClosed W ∧ W ⊆ s ∧
      (r : WithBot ℕ∞) ≤ topologicalKrullDim W := by
  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.mp hd
  refine ⟨pushCl hs l.last, (pushCl hs l.last).isIrreducible',
    (pushCl hs l.last).isClosed', ?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · refine le_trans ?_ (height_le_topologicalKrullDim_pushCl hs l.last)
    have hr : (r : ℕ∞) ≤ Order.height l.last := hl ▸ Order.length_le_height_last
    exact_mod_cast hr

end Topology

/-! ### Arithmetic in `WithBot ℕ∞` -/

section Arith

/-- Cancellation of a natural summand in `WithBot ℕ∞`: if `a ≤ b + x` and `b + c ≤ a` for natural
numbers `a`, `b`, `c`, then `c ≤ x`. -/
private lemma natCast_le_of_add_le {a b c : ℕ} {x : WithBot ℕ∞}
    (h : ((a : ℕ) : WithBot ℕ∞) ≤ ((b : ℕ) : WithBot ℕ∞) + x) (hab : b + c ≤ a) :
    ((c : ℕ) : WithBot ℕ∞) ≤ x := by
  induction x using WithBot.recBotCoe with
  | bot => simp at h
  | coe y =>
    induction y using ENat.recTopCoe with
    | top => simp
    | coe d =>
      have hd : a ≤ b + d := by exact_mod_cast h
      exact_mod_cast Nat.le_of_add_le_add_left (le_trans hab hd)

/-- An element of `WithBot ℕ∞` squeezed between two natural numbers is a natural number. -/
private lemma exists_eq_natCast {x : WithBot ℕ∞} {a b : ℕ}
    (h1 : ((a : ℕ) : WithBot ℕ∞) ≤ x) (h2 : x ≤ ((b : ℕ) : WithBot ℕ∞)) :
    ∃ d : ℕ, x = ((d : ℕ) : WithBot ℕ∞) ∧ a ≤ d ∧ d ≤ b := by
  induction x using WithBot.recBotCoe with
  | bot => simp at h1
  | coe y =>
    induction y using ENat.recTopCoe with
    | top =>
      refine absurd h2 (not_le.mpr ?_)
      exact_mod_cast ENat.natCast_lt_top b
    | coe d => exact ⟨d, rfl, by exact_mod_cast h1, by exact_mod_cast h2⟩

end Arith

/-! ### The irrelevant ideal of a polynomial algebra -/

section Irrelevant

variable (k : Type u) [Field k] (N : ℕ)

/-- The degree-zero projection of the total-degree grading of a polynomial algebra is the
degree-zero homogeneous component. -/
private lemma proj_zero_eq (a : MvPolynomial (Fin N) k) :
    GradedRing.proj (𝒜 N k) 0 a = MvPolynomial.homogeneousComponent 0 a := by
  rw [GradedRing.proj_apply]
  exact MvPolynomial.decomposition.decompose'_apply a 0

/-- The irrelevant ideal `(T₀, …, T_{N-1})` is the kernel of evaluation at the origin. -/
private lemma irrelevant_eq_ker : (HomogeneousIdeal.irrelevant (𝒜 N k)).toIdeal =
    RingHom.ker (MvPolynomial.eval (0 : Fin N → k)) := by
  ext a
  rw [RingHom.mem_ker, HomogeneousIdeal.mem_iff, HomogeneousIdeal.mem_irrelevant_iff,
    proj_zero_eq, MvPolynomial.homogeneousComponent_zero, MvPolynomial.eval_zero]
  simp [MvPolynomial.constantCoeff_eq]

/-- The irrelevant ideal of a polynomial algebra over a field is maximal. -/
private lemma isMaximal_irrelevant : (HomogeneousIdeal.irrelevant (𝒜 N k)).toIdeal.IsMaximal := by
  rw [irrelevant_eq_ker]
  exact RingHom.ker_isMaximal_of_surjective _ fun c => ⟨MvPolynomial.C c, by simp⟩

/-- The quotient of a polynomial algebra over a field by its irrelevant ideal has Krull dimension
zero. -/
private lemma ringKrullDim_quotient_irrelevant :
    ringKrullDim (MvPolynomial (Fin N) k ⧸ (HomogeneousIdeal.irrelevant (𝒜 N k)).toIdeal) = 0 :=
  ringKrullDim_eq_zero_of_isField
    ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp (isMaximal_irrelevant k N))

end Irrelevant

/-! ### Homogeneous primes from irreducible closed subsets -/

section HomogeneousPrimes

variable (k : Type u) [Field k] (N : ℕ)

/-- The homogeneous prime spectrum of a polynomial algebra over a field is a sober space. -/
private lemma quasiSober_projectiveSpectrum : QuasiSober (ProjectiveSpectrum (𝒜 N k)) :=
  inferInstanceAs (QuasiSober (AlgebraicGeometry.Proj (𝒜 N k)))

/-- A closed subset `X` of `Proj k[T₀, …, T_{N-1}]` of dimension at least `r` contains the
projective zero locus of a homogeneous prime `q`, nonempty and of dimension at least `r`. -/
private lemma exists_homogeneous_prime {r : ℕ} (X : Set (ProjectiveSpectrum (𝒜 N k)))
    (hXc : IsClosed X) (hXd : (r : WithBot ℕ∞) ≤ topologicalKrullDim X) :
    ∃ q : HomogeneousIdeal (𝒜 N k), q.toIdeal.IsPrime ∧
      ProjectiveSpectrum.zeroLocus (𝒜 N k) (q.toIdeal : Set (MvPolynomial (Fin N) k)) ⊆ X ∧
      (ProjectiveSpectrum.zeroLocus (𝒜 N k)
        (q.toIdeal : Set (MvPolynomial (Fin N) k))).Nonempty ∧
      (r : WithBot ℕ∞) ≤ topologicalKrullDim ↥(ProjectiveSpectrum.zeroLocus (𝒜 N k)
        (q.toIdeal : Set (MvPolynomial (Fin N) k))) := by
  have := quasiSober_projectiveSpectrum k N
  obtain ⟨W, hWi, hWc, hWX, hWd⟩ :=
    exists_isIrreducible_isClosed_of_le_topologicalKrullDim hXc hXd
  obtain ⟨w, hw⟩ := QuasiSober.sober hWi hWc
  have hzl : ProjectiveSpectrum.zeroLocus (𝒜 N k)
      ((w.asHomogeneousIdeal.toIdeal : Ideal (MvPolynomial (Fin N) k)) :
        Set (MvPolynomial (Fin N) k)) = W := by
    rw [coe_toIdeal, ← ProjectiveSpectrum.vanishingIdeal_singleton w,
      ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    exact hw
  exact ⟨w.asHomogeneousIdeal, w.isPrime, hzl ▸ hWX, hzl ▸ hWi.nonempty, hzl ▸ hWd⟩

/-- If `Z` is an irreducible closed subset of dimension at least `c` of the affine cone `V(I)` over
a homogeneous ideal `I`, then there is a homogeneous prime containing `I` whose quotient has
dimension at least `c`. -/
private lemma exists_homogeneous_prime_of_isIrreducible {c : ℕ}
    (I : Ideal (MvPolynomial (Fin N) k)) (hI : I.IsHomogeneous (𝒜 N k))
    (Z : Set (PrimeSpectrum (MvPolynomial (Fin N) k))) (hZi : IsIrreducible Z)
    (hZc : IsClosed Z)
    (hZI : Z ⊆ PrimeSpectrum.zeroLocus (I : Set (MvPolynomial (Fin N) k)))
    (hZd : (c : WithBot ℕ∞) ≤ topologicalKrullDim Z) :
    ∃ Q : HomogeneousIdeal (𝒜 N k), Q.toIdeal.IsPrime ∧ I ≤ Q.toIdeal ∧
      ((c : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin N) k ⧸ Q.toIdeal) := by
  have hPp : (PrimeSpectrum.vanishingIdeal Z).IsPrime :=
    PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.mp hZi
  have hZeq : PrimeSpectrum.zeroLocus
      ((PrimeSpectrum.vanishingIdeal Z : Ideal (MvPolynomial (Fin N) k)) :
        Set (MvPolynomial (Fin N) k)) = Z := by
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hZc.closure_eq]
  have hIP : I ≤ PrimeSpectrum.vanishingIdeal Z :=
    (PrimeSpectrum.subset_zeroLocus_iff_le_vanishingIdeal Z I).mp hZI
  refine ⟨(PrimeSpectrum.vanishingIdeal Z).homogeneousCore (𝒜 N k),
    hPp.homogeneousCore (𝒜 := 𝒜 N k), ?_, ?_⟩
  · calc I = (I.homogeneousCore (𝒜 N k)).toIdeal :=
          hI.toIdeal_homogeneousCore_eq_self.symm
      _ ≤ _ := Ideal.homogeneousCore_mono (𝒜 N k) hIP
  · calc ((c : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim ↥Z := hZd
      _ = topologicalKrullDim ↥(PrimeSpectrum.zeroLocus
            ((PrimeSpectrum.vanishingIdeal Z : Ideal (MvPolynomial (Fin N) k)) :
              Set (MvPolynomial (Fin N) k))) := by rw [hZeq]
      _ ≤ topologicalKrullDim ↥(PrimeSpectrum.zeroLocus
            ((((PrimeSpectrum.vanishingIdeal Z).homogeneousCore (𝒜 N k)).toIdeal :
              Ideal (MvPolynomial (Fin N) k)) : Set (MvPolynomial (Fin N) k))) :=
          topologicalKrullDim_le_of_subset (PrimeSpectrum.zeroLocus_anti_mono_ideal
            (Ideal.toIdeal_homogeneousCore_le (𝒜 N k) (PrimeSpectrum.vanishingIdeal Z)))
      _ = _ := topologicalKrullDim_zeroLocus _

/-- For a homogeneous prime `q` with a projective zero locus of dimension at least `r`, the affine
zero locus of `q` is closed and irreducible, `q` lies in the irrelevant ideal, and the dimension of
the affine zero locus is a natural number at least `r + 1`. -/
private lemma cone_data_of_zeroLocus {r : ℕ} (q : HomogeneousIdeal (𝒜 N k))
    (hqp : q.toIdeal.IsPrime)
    (hqne : (ProjectiveSpectrum.zeroLocus (𝒜 N k)
      (q.toIdeal : Set (MvPolynomial (Fin N) k))).Nonempty)
    (hqd : (r : WithBot ℕ∞) ≤ topologicalKrullDim ↥(ProjectiveSpectrum.zeroLocus (𝒜 N k)
      (q.toIdeal : Set (MvPolynomial (Fin N) k)))) :
    q.toIdeal ≤ (HomogeneousIdeal.irrelevant (𝒜 N k)).toIdeal ∧
      IsClosed (PrimeSpectrum.zeroLocus (q.toIdeal : Set (MvPolynomial (Fin N) k))) ∧
      IsIrreducible (PrimeSpectrum.zeroLocus (q.toIdeal : Set (MvPolynomial (Fin N) k))) ∧
      ∃ d : ℕ, r + 1 ≤ d ∧ topologicalKrullDim ↥(PrimeSpectrum.zeroLocus
        (q.toIdeal : Set (MvPolynomial (Fin N) k))) = (d : WithBot ℕ∞) := by
  have hup : topologicalKrullDim ↥(PrimeSpectrum.zeroLocus
      (q.toIdeal : Set (MvPolynomial (Fin N) k))) ≤ (N : WithBot ℕ∞) := by
    refine le_trans (topologicalKrullDim_subspace_le _ _) ?_
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
      Stacks.MvPolynomial.ringKrullDim_mvPolynomial]
    simp
  have hlow : ((r + 1 : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim ↥(PrimeSpectrum.zeroLocus
      (q.toIdeal : Set (MvPolynomial (Fin N) k))) := by
    rw [topologicalKrullDim_zeroLocus,
      ← Stacks.ProjectiveSpace.topologicalKrullDim_projectiveSpectrum_zeroLocus_add_one
        q.toIdeal q.isHomogeneous hqne, Nat.cast_add, Nat.cast_one]
    exact add_le_add hqd le_rfl
  obtain ⟨d, hd, hdr, -⟩ := exists_eq_natCast hlow hup
  exact ⟨Stacks.ProjectiveSpace.le_irrelevant_of_isHomogeneous_of_ne_top q.isHomogeneous
    hqp.ne_top, PrimeSpectrum.isClosed_zeroLocus _,
    (PrimeSpectrum.isIrreducible_zeroLocus_iff_of_radical _ hqp.isRadical).mpr hqp, d, hdr, hd⟩

end HomogeneousPrimes

/-! ### Tag 0B2R -/

section Main

variable (k : Type u) [Field k] (n r s : ℕ)

/-- Let `X` and `Y` be closed subsets of `Proj k[T₀, …, Tₙ]` of dimensions `r` and `s`, with
`n ≤ r + s`. Then there is an ideal `Q` whose projective zero locus is a nonempty subset of
`X ∩ Y` of dimension at least `r + s - n`. -/
private lemma exists_homogeneous_prime_inter
    (X Y : Set (ProjectiveSpectrum (𝒜 (n + 1) k))) (hXc : IsClosed X) (hYc : IsClosed Y)
    (hXd : topologicalKrullDim ↥X = (r : WithBot ℕ∞))
    (hYd : topologicalKrullDim ↥Y = (s : WithBot ℕ∞)) (hrs : n ≤ r + s) :
    ∃ Q : Ideal (MvPolynomial (Fin (n + 1)) k),
      ProjectiveSpectrum.zeroLocus (𝒜 (n + 1) k)
          (Q : Set (MvPolynomial (Fin (n + 1)) k)) ⊆ X ∩ Y ∧
      (ProjectiveSpectrum.zeroLocus (𝒜 (n + 1) k)
          (Q : Set (MvPolynomial (Fin (n + 1)) k))).Nonempty ∧
      ((r + s - n : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim
        ↥(ProjectiveSpectrum.zeroLocus (𝒜 (n + 1) k)
          (Q : Set (MvPolynomial (Fin (n + 1)) k))) := by
  obtain ⟨q, hqp, hqX, hqne, hqd⟩ := exists_homogeneous_prime k (n + 1) X hXc hXd.ge
  obtain ⟨q', hq'p, hq'Y, hq'ne, hq'd⟩ := exists_homogeneous_prime k (n + 1) Y hYc hYd.ge
  have hmprime := (isMaximal_irrelevant k (n + 1)).isPrime
  obtain ⟨hqm, hVc, hVi, d, hdr, hd⟩ := cone_data_of_zeroLocus k (n + 1) q hqp hqne hqd
  obtain ⟨hq'm, hV'c, hV'i, d', hd's, hd'⟩ := cone_data_of_zeroLocus k (n + 1) q' hq'p hq'ne hq'd
  have hmV : (⟨(HomogeneousIdeal.irrelevant (𝒜 (n + 1) k)).toIdeal, hmprime⟩ :
      PrimeSpectrum (MvPolynomial (Fin (n + 1)) k)) ∈
      PrimeSpectrum.zeroLocus (q.toIdeal : Set (MvPolynomial (Fin (n + 1)) k)) ∩
        PrimeSpectrum.zeroLocus (q'.toIdeal : Set (MvPolynomial (Fin (n + 1)) k)) :=
    ⟨hqm, hq'm⟩
  set x₀ : ↥(PrimeSpectrum.zeroLocus (q.toIdeal : Set (MvPolynomial (Fin (n + 1)) k)) ∩
    PrimeSpectrum.zeroLocus (q'.toIdeal : Set (MvPolynomial (Fin (n + 1)) k))) :=
    ⟨⟨(HomogeneousIdeal.irrelevant (𝒜 (n + 1) k)).toIdeal, hmprime⟩, hmV⟩
  have h2q := AlgebraicGeometry.add_le_add_topologicalKrullDim_irreducibleComponent_inter
    k (n + 1) d d' _ _ hVc hV'c hVi.2.equidimensional hV'i.2.equidimensional hd hd'
    (irreducibleComponent x₀) (irreducibleComponent_mem_irreducibleComponents x₀)
  have h2 : ((d + d' : ℕ) : WithBot ℕ∞) ≤ ((n + 1 : ℕ) : WithBot ℕ∞) +
      topologicalKrullDim ↥(irreducibleComponent x₀) := by
    rwa [Nat.cast_add]
  have hZlow : (((r + s - n) + 1 : ℕ) : WithBot ℕ∞) ≤
      topologicalKrullDim ↥(irreducibleComponent x₀) := natCast_le_of_add_le h2 (by omega)
  have hZZ' : topologicalKrullDim ↥(irreducibleComponent x₀) ≤
      topologicalKrullDim ↥(Subtype.val '' irreducibleComponent x₀) :=
    topologicalKrullDim_le_image_val (hVc.inter hV'c) isIrreducible_irreducibleComponent
      isClosed_irreducibleComponent
  obtain ⟨Q, hQp, hsupQ, hQdim⟩ := exists_homogeneous_prime_of_isIrreducible k (n + 1)
    (c := (r + s - n) + 1) _ ((q ⊔ q').isHomogeneous)
    (Subtype.val '' irreducibleComponent x₀)
    (isIrreducible_irreducibleComponent.image _ continuous_subtype_val.continuousOn)
    ((hVc.inter hV'c).isClosedEmbedding_subtypeVal.isClosedMap _ isClosed_irreducibleComponent)
    (by
      rw [HomogeneousIdeal.toIdeal_sup, PrimeSpectrum.zeroLocus_sup]
      rintro _ ⟨y, -, rfl⟩
      exact y.2)
    (le_trans hZlow hZZ')
  have : Q.toIdeal.IsPrime := hQp
  have hQm : Q.toIdeal ≤ (HomogeneousIdeal.irrelevant (𝒜 (n + 1) k)).toIdeal :=
    Stacks.ProjectiveSpace.le_irrelevant_of_isHomogeneous_of_ne_top Q.isHomogeneous hQp.ne_top
  have hQne : (ProjectiveSpectrum.zeroLocus (𝒜 (n + 1) k)
      ((Q.toIdeal : Ideal (MvPolynomial (Fin (n + 1)) k)) :
        Set (MvPolynomial (Fin (n + 1)) k))).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hempty
    have h1 : HomogeneousIdeal.irrelevant (𝒜 (n + 1) k) ≤ Q.radical :=
      (ProjectiveSpectrum.zeroLocus_empty_iff_irrelevant_le_radical (𝒜 (n + 1) k) Q).mp hempty
    have h2' : (HomogeneousIdeal.irrelevant (𝒜 (n + 1) k)).toIdeal ≤ Q.toIdeal := by
      have h3 : (HomogeneousIdeal.irrelevant (𝒜 (n + 1) k)).toIdeal ≤ Q.radical.toIdeal := h1
      rwa [HomogeneousIdeal.coe_radical, hQp.radical] at h3
    rw [le_antisymm hQm h2', ringKrullDim_quotient_irrelevant] at hQdim
    simp at hQdim
  refine ⟨Q.toIdeal, ?_, hQne, ?_⟩
  · refine le_trans (ProjectiveSpectrum.zeroLocus_anti_mono_ideal (𝒜 (n + 1) k) hsupQ) ?_
    rw [HomogeneousIdeal.toIdeal_sup, ProjectiveSpectrum.zeroLocus_sup_ideal]
    exact Set.inter_subset_inter hqX hq'Y
  · refine natCast_le_of_add_le (a := (r + s - n) + 1) (b := 1) ?_ (by omega)
    rw [Nat.cast_one, add_comm (1 : WithBot ℕ∞),
      Stacks.ProjectiveSpace.topologicalKrullDim_projectiveSpectrum_zeroLocus_add_one
        Q.toIdeal Q.isHomogeneous hQne]
    exact hQdim

/-- Closed subsets `X` and `Y` of `ℙⁿ_k` of dimensions `r` and `s`, with `n ≤ r + s`, have a
nonempty common subset of dimension at least `r + s - n`. -/
private lemma exists_subset_inter_projectiveSpaceOverRing
    (X Y : Set (AlgebraicGeometry.projectiveSpaceOverRing n (CommRingCat.of k)))
    (hXc : IsClosed X) (hYc : IsClosed Y)
    (hXd : topologicalKrullDim ↥X = (r : WithBot ℕ∞))
    (hYd : topologicalKrullDim ↥Y = (s : WithBot ℕ∞)) (hrs : n ≤ r + s) :
    ∃ V : Set (AlgebraicGeometry.projectiveSpaceOverRing n (CommRingCat.of k)),
      V ⊆ X ∩ Y ∧ V.Nonempty ∧ ((r + s - n : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim ↥V := by
  set e := (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison k n).iso.hom.homeomorph
  obtain ⟨Q, hQsub, ⟨z, hz⟩, hQd⟩ := exists_homogeneous_prime_inter
    k n r s (e.symm ⁻¹' X) (e.symm ⁻¹' Y) (hXc.preimage e.symm.continuous)
    (hYc.preimage e.symm.continuous)
    ((topologicalKrullDim_preimage_of_homeomorph e.symm X).trans hXd)
    ((topologicalKrullDim_preimage_of_homeomorph e.symm Y).trans hYd) hrs
  exact ⟨e.symm '' _, fun _ ⟨_, hy, h⟩ => h ▸ hQsub hy, ⟨e.symm z, z, hz, rfl⟩,
    hQd.trans (by
      rw [e.image_symm]
      exact (topologicalKrullDim_preimage_of_homeomorph e _).ge)⟩

end Main

end Stacks.ProjectiveIntersection

namespace AlgebraicGeometry

variable (k : Type u) [Field k] (n r s : ℕ)

/-- Let `k` be a field and let `X` and `Y` be nonempty closed subsets of `ℙⁿ_k` of dimensions `r`
and `s`. If `n ≤ r + s` then `X` and `Y` meet. -/
@[stacks 0B2R "nonemptiness"]
theorem inter_nonempty_projectiveSpaceOverRing
    (X Y : Set (AlgebraicGeometry.projectiveSpaceOverRing n (CommRingCat.of k)))
    (hXc : IsClosed X) (hYc : IsClosed Y) (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hXd : topologicalKrullDim ↥X = (r : WithBot ℕ∞))
    (hYd : topologicalKrullDim ↥Y = (s : WithBot ℕ∞))
    (hrs : n ≤ r + s) : (X ∩ Y).Nonempty := by
  have _hX : X.Nonempty := hXne
  have _hY : Y.Nonempty := hYne
  obtain ⟨V, hV, ⟨z, hz⟩, -⟩ :=
    Stacks.ProjectiveIntersection.exists_subset_inter_projectiveSpaceOverRing
      k n r s X Y hXc hYc hXd hYd hrs
  exact ⟨z, hV hz⟩

/-- Let `k` be a field and let `X` and `Y` be nonempty closed subsets of `ℙⁿ_k` of dimensions `r`
and `s`. If `n ≤ r + s` then `X ∩ Y` has dimension at least `r + s - n`. -/
@[stacks 0B2R "dimension bound"]
theorem le_topologicalKrullDim_inter_projectiveSpaceOverRing
    (X Y : Set (AlgebraicGeometry.projectiveSpaceOverRing n (CommRingCat.of k)))
    (hXc : IsClosed X) (hYc : IsClosed Y) (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hXd : topologicalKrullDim ↥X = (r : WithBot ℕ∞))
    (hYd : topologicalKrullDim ↥Y = (s : WithBot ℕ∞))
    (hrs : n ≤ r + s) : ((r + s - n : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim ↥(X ∩ Y) := by
  have _hX : X.Nonempty := hXne
  have _hY : Y.Nonempty := hYne
  obtain ⟨V, hV, -, hVd⟩ :=
    Stacks.ProjectiveIntersection.exists_subset_inter_projectiveSpaceOverRing
      k n r s X Y hXc hYc hXd hYd hrs
  exact hVd.trans (topologicalKrullDim_le_of_subset hV)

end AlgebraicGeometry

end
