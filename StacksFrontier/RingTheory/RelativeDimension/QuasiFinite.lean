module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.QuasiFinite
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.RingTheory.ZariskisMainTheorem
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import StacksFrontier.Topology.Dimension.Krull
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Relative dimension `n` gives a quasi-finite map to a polynomial ring in `n` variables
-/

/-!
# Relative dimension `n` implies quasi-finiteness over a polynomial ring in `n` variables

Stacks tag 00QE (Lemma 10.125.2).

Let `R → S` be a finite type ring map and let `q ⊂ S` be a prime ideal lying over the
prime `p = q ∩ R` of `R`. Suppose the relative dimension of `S/R` at `q` equals `n` for
some natural number `n`. Then there exist `g ∈ S` with `g ∉ q` and a ring map of
`R`-algebras `φ : R[t_1, …, t_n] → S_g` such that the localization `S_g = S[1/g]` is
quasi-finite over `R[t_1, …, t_n]` via `φ`; that is, `R[t_1, …, t_n] → S_g` is a finite
type, quasi-finite ring map.

## Conventions

For a ring map `R → S` and a prime `p ⊂ R`, the *residue field* of `R` at `p` is
`κ(p) = Frac(R/p)` and the *fibre* of `S` over `p` is the `κ(p)`-algebra `S ⊗_R κ(p)`;
these are `Ideal.ResidueField` and `Ideal.Fiber S = TensorProduct R p.ResidueField S`.

For a topological space `X` and a point `x ∈ X`, the Krull dimension of `X` at `x` is
`dim_x(X) = min { dim(U) : x ∈ U ⊆ X open }` (Stacks tag 0055), where `dim` is
`topologicalKrullDim`, valued in `WithBot ℕ∞` so that `dim(∅) = ⊥ = -∞`. The minimum
over open neighbourhoods is formalized as an infimum over the type of open
neighbourhoods of `x`.

For `R → S` of finite type and a prime `q ⊂ S` over `p ⊂ R`, the relative dimension of
`S/R` at `q` is `dim_q(S/R) = dim_{q̄}(Spec(S ⊗_R κ(p)))` (Stacks tag 00QD), the Krull
dimension of the spectrum of the fibre at the point `q̄` corresponding to `q`. That point
`q̄ ∈ Spec(S ⊗_R κ(p))` is characterized by its image under pullback of primes along the
natural map `S → S ⊗_R κ(p)` being `q`.

A finite type ring map `R → S` is *quasi-finite* exactly when for every prime `p ⊂ R`
the fibre `S ⊗_R κ(p)` is a finite `κ(p)`-vector space (Stacks tag 00PM,
`forall_quasiFiniteAt_iff_forall_finite_fiber`); this is
`Algebra.QuasiFinite` / `RingHom.QuasiFinite`, whose defining field is
`∀ (P : Ideal R) [P.IsPrime], Module.Finite P.ResidueField (P.Fiber S)`.

Finally `R[t_1, …, t_n]` is `MvPolynomial (Fin n) R` and `S_g = S[1/g]` is
`Localization.Away g`, and "`S_g` is quasi-finite over `R[t_1, …, t_n]`" means there is
an `R`-algebra map `φ : R[t_1, …, t_n] → S_g` making `S_g` a finite type
`R[t_1, …, t_n]`-algebra which is quasi-finite.

The hypothesis `dim_q(S/R) = n` with `n : ℕ` ensures the dimension is finite, in
particular neither `⊥` nor `⊤`. The `R`-algebra-map condition on `φ` is expressed as the
commutativity `φ ∘ (R → R[t_1,…,t_n]) = (R → S_g)`, the right-hand structure map being
the composite `R → S → S_g`.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Algebra

/-- The Krull dimension of a topological space `X` at a point `x` (Stacks tag 0055): the
infimum, i.e. minimum, of the Krull dimensions `topologicalKrullDim` of the open
neighbourhoods of `x`, valued in `WithBot ℕ∞`. -/
@[ega "0 14.1.2", sga "1 II 5.9", sga "3 VIB 1.5", sga "7 XV 1.2"]
def krullDimAt {X : Type*} [TopologicalSpace X] (x : X) : WithBot ℕ∞ :=
  ⨅ U : {U : Set X // IsOpen U ∧ x ∈ U}, topologicalKrullDim U.val

/-- `krullDimAt` is `topologicalKrullDimAt`: the same infimum over the open neighbourhoods of
`x`, indexed here by the subtype recording openness before membership and there by the subtype
recording them in the other order. Each index of one infimum is an index of the other, so each
is below the other. -/
theorem krullDimAt_eq_topologicalKrullDimAt {X : Type*} [TopologicalSpace X] (x : X) :
    krullDimAt x = topologicalKrullDimAt X x :=
  le_antisymm
    (le_iInf fun U => iInf_le_of_le ⟨U.1, U.2.2, U.2.1⟩ le_rfl)
    (le_iInf fun U => iInf_le_of_le ⟨U.1, U.2.2, U.2.1⟩ le_rfl)

/-- The natural ring map `S → S ⊗_R κ(p)` of `S` into the fibre `p.Fiber S` over the prime
`p`, given by `s ↦ 1 ⊗ s`. Pulling back primes along this map realizes the canonical
homeomorphism of `Spec(S ⊗_R κ(p))` onto the fibre over `p`. -/
@[ega "IV 9.4.1" "special case"]
def fiberMap (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] : S →+* p.Fiber S :=
  (Algebra.TensorProduct.includeRight : S →ₐ[R] p.Fiber S).toRingHom

/-- The relative dimension of `S/R` at a point `qbar` of the fibre spectrum
`Spec(S ⊗_R κ(p))` (Stacks tag 00QD), namely the Krull dimension of `Spec(S ⊗_R κ(p))` at
`qbar`. The point `qbar` corresponding to a prime `q ⊂ S` lying over `p` is the one with
`PrimeSpectrum.comap (fiberMap R S p) qbar = q`. -/
@[ega "IV 17.10.1" "affine case", sga "3 XI 1.9" "special case"]
def relativeDimensionAt (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] (qbar : PrimeSpectrum (p.Fiber S)) : WithBot ℕ∞ :=
  krullDimAt qbar

/-- An infimum over a nonempty family valued in `WithBot ℕ∞` is attained, because
`WithBot ℕ∞` is well-founded for `<`. -/
private theorem exists_iInf_eq_of_nonempty {ι : Type*} [Nonempty ι] (f : ι → WithBot ℕ∞) :
    ∃ i, (⨅ j, f j) = f i := by
  obtain ⟨_, ⟨i, rfl⟩, hi⟩ :=
    WellFounded.has_min wellFounded_lt (Set.range f) (Set.range_nonempty f)
  exact ⟨i, le_antisymm (iInf_le _ _) (le_iInf (fun j => by
    by_contra h; exact hi (f j) ⟨j, rfl⟩ (lt_of_not_ge h)))⟩

/-- (Stacks 00OK / Tag 00OK, "dimension is invariant under integral extensions") The Krull
dimension of a ring is preserved by a module-finite injective ring map. Concretely, if
`f : A →+* B` is module-finite (`f.Finite`, so `B` is a finite `A`-module) and injective
(so `A ↪ B` and `B` is integral over `A`), then `ringKrullDim B = ringKrullDim A`.

This is the going-up / lying-over theorem for integral extensions (Stacks 00OK, the key
ingredient of Noether normalization's dimension statement 00OW). Mathlib in this environment
provides the easy inequality `ringKrullDim A ≤ ringKrullDim B` (prime chains pull back along
the surjective `Spec B → Spec A`, `comap` strictly monotone), but NOT the reverse going-up
inequality `ringKrullDim B ≤ ringKrullDim A`. The reverse direction needs lying-over plus a
single-step going-up induction lifting a maximal `LTSeries` of primes of `A` to `B`
(`Algebra.IsIntegral.comap_surjective` on the quotients `A/𝔭 ↪ B/𝔓`). Left as a cited
dependency to be discharged as its own subgoal. -/
@[ega "0 16.1.5" "special case", ega "IV 5.4.3" "more general"]
private theorem ringKrullDim_eq_of_finite_injective
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : f.Finite) (hinj : Function.Injective f) :
    ringKrullDim B = ringKrullDim A := by
  let := f.toAlgebra
  have : Module.Finite A B := hf
  have : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hinj
  apply le_antisymm
  · -- ringKrullDim B ≤ ringKrullDim A: comap is strictly monotone
    refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap A B)) ?_
    intro x y hxy
    exact Ideal.IsIntegral.under_lt_under (R := A) (A := B) hxy
  · -- ringKrullDim A ≤ ringKrullDim B: going-up chain lift
    have lift : ∀ (l : LTSeries (PrimeSpectrum A)) (P₀ : PrimeSpectrum B),
        PrimeSpectrum.comap (algebraMap A B) P₀ = l.head →
        ∃ l' : LTSeries (PrimeSpectrum B), l'.length = l.length ∧
          PrimeSpectrum.comap (algebraMap A B) l'.last = l.last := by
      intro l
      induction hn : l.length using Nat.strong_induction_on generalizing l with
      | _ n IH =>
        intro P₀ hP₀
        match n, hn with
        | 0, hn =>
          refine ⟨RelSeries.singleton _ P₀, by simp, ?_⟩
          rw [RelSeries.last_singleton, hP₀]
          have : l.head = l.last := by
            rw [RelSeries.head, RelSeries.last]; congr 1
            apply Fin.ext; simp [Fin.last, hn]
          rw [this]
        | (k+1), hn =>
          set m := l.eraseLast with hm
          have hmlen : m.length = k := by rw [hm, RelSeries.eraseLast_length, hn]; omega
          have hmhead : m.head = l.head := by rw [hm, RelSeries.head_eraseLast]
          obtain ⟨m', hm'len, hm'last⟩ := IH k (by omega) m hmlen P₀ (by rw [hmhead]; exact hP₀)
          have hrel : m.last < l.last := by
            have := RelSeries.eraseLast_last_rel_last l (by rw [hn]; omega)
            rw [hm]; exact this
          have hle : (m'.last.asIdeal).comap (algebraMap A B) ≤ l.last.asIdeal := by
            rw [show (m'.last.asIdeal).comap (algebraMap A B)
              = (PrimeSpectrum.comap (algebraMap A B) m'.last).asIdeal from rfl, hm'last]
            exact le_of_lt hrel
          obtain ⟨Q, hQge, hQprime, hQcomap⟩ :=
            Ideal.exists_ideal_over_prime_of_isIntegral (R := A) (S := B)
              l.last.asIdeal m'.last.asIdeal hle
          let P' : PrimeSpectrum B := ⟨Q, hQprime⟩
          have hPcomap : PrimeSpectrum.comap (algebraMap A B) P' = l.last := by
            apply PrimeSpectrum.ext; exact hQcomap
          have hlt : m'.last < P' := by
            rw [lt_iff_le_and_ne]
            refine ⟨hQge, ?_⟩
            intro heq
            rw [heq, hPcomap] at hm'last
            exact absurd hm'last (ne_of_lt hrel).symm
          refine ⟨m'.snoc P' hlt, ?_, ?_⟩
          · rw [RelSeries.snoc_length, hm'len]
          · rw [RelSeries.last_snoc]; exact hPcomap
    have hsurj := Algebra.IsIntegral.comap_surjective A B
    change Order.krullDim (PrimeSpectrum A) ≤ Order.krullDim (PrimeSpectrum B)
    apply iSup_le
    intro l
    obtain ⟨P₀, hP₀⟩ := hsurj l.head
    obtain ⟨l', hl'len, _⟩ := lift l P₀ hP₀
    calc (l.length : WithBot ℕ∞) = (l'.length : WithBot ℕ∞) := by rw [hl'len]
      _ ≤ Order.krullDim (PrimeSpectrum B) := Order.LTSeries.length_le_krullDim l'

-- The topological and base-change content of Stacks 00E6.

/-- `topologicalKrullDim` is invariant under homeomorphism: the Krull dimension of a
topological space depends only on its lattice of irreducible closed sets, equivalently on
its specialization order, and a homeomorphism preserves that lattice. -/
private theorem topologicalKrullDim_eq_of_homeo {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (h : X ≃ₜ Y) :
    topologicalKrullDim X = topologicalKrullDim Y := by
  have linv : Function.LeftInverse (IrreducibleCloseds.map h.symm h.symm.continuous)
      (IrreducibleCloseds.map h h.continuous) := by
    intro c
    apply IrreducibleCloseds.ext
    change closure (h.symm '' closure (h '' (c : Set X))) = (c : Set X)
    rw [(h.isClosedMap _ c.isClosed).closure_eq, ← Set.image_comp]
    simp [c.isClosed.closure_eq]
  have rinv : Function.RightInverse (IrreducibleCloseds.map h.symm h.symm.continuous)
      (IrreducibleCloseds.map h h.continuous) := by
    intro c
    apply IrreducibleCloseds.ext
    change closure (h '' closure (h.symm '' (c : Set Y))) = (c : Set Y)
    rw [(h.symm.isClosedMap _ c.isClosed).closure_eq, ← Set.image_comp]
    simp [c.isClosed.closure_eq]
  have hrel : ∀ a b : IrreducibleCloseds X,
      IrreducibleCloseds.map h h.continuous a ≤ IrreducibleCloseds.map h h.continuous b
        ↔ a ≤ b := by
    intro a b
    refine ⟨fun hab => ?_, fun hab => IrreducibleCloseds.map_mono h.continuous hab⟩
    have hm := IrreducibleCloseds.map_mono h.symm.continuous hab
    rwa [linv a, linv b] at hm
  let oiso : IrreducibleCloseds X ≃o IrreducibleCloseds Y :=
    { toFun := IrreducibleCloseds.map h h.continuous
      invFun := IrreducibleCloseds.map h.symm h.symm.continuous
      left_inv := linv
      right_inv := rinv
      map_rel_iff' := fun {a b} => hrel a b }
  rw [topologicalKrullDim, topologicalKrullDim, Order.krullDim_eq_of_orderIso oiso]

/-- (Obligation B, Stacks 00E6) Base change of localization: the spectrum of the fibre of
the localization `S_g = Localization.Away g` over `p` is homeomorphic to the basic open
`D(fiberMap g) ⊆ Spec(p.Fiber S)`. The algebraic content is that `p.Fiber (S_g) =
S_g ⊗_R κ(p)` is the localization `(p.Fiber S)[1/(fiberMap g)] = Localization.Away
(fiberMap R S p g)` (tensor commutes with localization); then `Spec` of a localization-away
is the open immersion onto the basic open via `PrimeSpectrum.localization_away_comap_range`.
To prove: build `IsLocalization.Away (fiberMap R S p g) (p.Fiber (Localization.Away g))`
(register `Algebra (p.Fiber S) (p.Fiber (Localization.Away g))` via the tensor-product
functor map; use `isLocalizedModule_iff_isLocalization` + base-change-preserves-localized-
module), then `PrimeSpectrum.localization_away_comap_range` gives the range = `D(φ g)`, and
`PrimeSpectrum.localization_away_isOpenEmbedding`/`.comap` packages the homeomorphism onto
the subspace. -/
private theorem fiberLocAway_spec_homeo_basicOpen
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] (g : S) :
    Nonempty (PrimeSpectrum (p.Fiber (Localization.Away g)) ≃ₜ
      (PrimeSpectrum.basicOpen (fiberMap R S p g) : Set (PrimeSpectrum (p.Fiber S)))) := by
  -- Algebraic content: with `T := (p.Fiber S) ⊗_S (S[1/g])`, base change of localization
  -- (`IsLocalization.Away.tensor`) gives `IsLocalization.Away (fiberMap g) T`. Topologically
  -- `comap (algebraMap (p.Fiber S) T)` is then an open embedding with range `D(fiberMap g)`
  -- (`localization_away_isOpenEmbedding` / `localization_away_comap_range`). Finally a ring
  -- isomorphism `T ≃+* p.Fiber (S[1/g])` (associativity/cancellation of base change) transports
  -- the spectrum, yielding the desired homeomorphism onto the basic open.
  let : Algebra S (TensorProduct R p.ResidueField S) := Algebra.TensorProduct.rightAlgebra
  set T := TensorProduct S (TensorProduct R p.ResidueField S) (Localization.Away g) with hT
  have hloc : IsLocalization.Away (fiberMap R S p g) T :=
    IsLocalization.Away.tensor g (Localization.Away g)
  have hoe := PrimeSpectrum.localization_away_isOpenEmbedding T (fiberMap R S p g)
  have hrange := PrimeSpectrum.localization_away_comap_range T (fiberMap R S p g)
  -- forward ring equiv: T ≃+* p.Fiber (Loc g)
  have efwd : T ≃+* (TensorProduct R p.ResidueField (Localization.Away g)) := by
    refine (Algebra.TensorProduct.comm S (TensorProduct R p.ResidueField S)
      (Localization.Away g)).toRingEquiv.trans ?_
    refine (Algebra.TensorProduct.congr (AlgEquiv.refl (R := S) (A₁ := Localization.Away g))
      ((TensorProduct.commRight R S p.ResidueField).symm)).toRingEquiv.trans ?_
    refine (Algebra.TensorProduct.cancelBaseChange R S S (Localization.Away g)
      p.ResidueField).toRingEquiv.trans ?_
    exact (Algebra.TensorProduct.comm R (Localization.Away g) p.ResidueField).toRingEquiv
  have h0 : PrimeSpectrum (p.Fiber (Localization.Away g)) ≃ₜ PrimeSpectrum T :=
    PrimeSpectrum.homeomorphOfRingEquiv efwd.symm
  have h1 := hoe.isEmbedding.toHomeomorph
  have h2 := Homeomorph.setCongr hrange
  exact ⟨h0.trans (h1.trans h2)⟩

/-- Every element of the fibre `p.Fiber S` becomes the image of an element of `S` after scaling by
a unit of `κ(p)` (clearing denominators). -/
private theorem exists_fiberMap_eq_unit_smul
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] (a : p.Fiber S) :
    ∃ (g : S) (c : p.ResidueField), IsUnit c ∧ fiberMap R S p g = c • a := by
  classical
  -- key identity: (algebraMap R κ(p) ρ) • fiberMap t = fiberMap (ρ • t)
  have key_id : ∀ (ρ : R) (t : S),
      (algebraMap R p.ResidueField ρ) • (fiberMap R S p t) = fiberMap R S p (ρ • t) := by
    intro ρ t
    change (algebraMap R p.ResidueField ρ) • (1 ⊗ₜ[R] t : TensorProduct R p.ResidueField S)
        = (1 ⊗ₜ[R] (ρ • t) : TensorProduct R p.ResidueField S)
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, TensorProduct.tmul_smul]
  -- span: every a is a κ(p)-combination of fiberMap images
  have span_top : ∀ a : p.Fiber S,
      a ∈ Submodule.span p.ResidueField (Set.range (fiberMap R S p)) := by
    intro a
    induction a using TensorProduct.inductionOn with
    | tmul c s =>
      have : (c ⊗ₜ[R] s : TensorProduct R p.ResidueField S) = c • (fiberMap R S p s) := by
        simp [fiberMap, Algebra.TensorProduct.includeRight_apply, TensorProduct.smul_tmul']
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)
    | add x y hx hy => exact Submodule.add_mem _ hx hy
  have ha := span_top a
  rw [Submodule.mem_span_set'] at ha
  obtain ⟨n, f, gg, hsum⟩ := ha
  choose t ht using fun i => (gg i).property
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (R ⧸ p))
    (Finset.univ : Finset (Fin n)) f
  set c : p.ResidueField := algebraMap (R ⧸ p) p.ResidueField b with hc
  have hcunit : IsUnit c := IsLocalization.map_units p.ResidueField b
  choose rbar hrbar using fun i => hb i (Finset.mem_univ i)
  choose ρ hρ using fun i => Ideal.Quotient.mk_surjective (rbar i)
  have hkey : ∀ i, algebraMap R p.ResidueField (ρ i) = c • f i := by
    intro i
    rw [IsScalarTower.algebraMap_apply R (R ⧸ p) p.ResidueField]
    rw [show algebraMap R (R ⧸ p) (ρ i) = rbar i from hρ i]
    rw [hrbar i, hc, algebra_compatible_smul p.ResidueField (b : R ⧸ p) (f i)]
  refine ⟨∑ i, (ρ i) • t i, c, hcunit, ?_⟩
  rw [← hsum, map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← key_id (ρ i) (t i), hkey i, ht i, smul_assoc]

/-- (Lemma A, denominator clearing) Any open neighborhood `U` of `qbar` in `Spec(p.Fiber S)`
contains a basic open `D(fiberMap g₁)` of an *image element* `fiberMap g₁` (`g₁ ∈ S`) that
still contains `qbar`. Proof: `U = V(I)ᶜ`; pick `a ∈ I \ qbar` so `D(a) ⊆ U` and
`qbar ∈ D(a)`; write `a = Σ cᵢ · fiberMap tᵢ` (`cᵢ ∈ κ(p)`, `tᵢ ∈ S`; images of `S` span
the fibre as a `κ(p)`-module); clear denominators by a field unit `c = Π (denominators) ∈
κ(p)ˣ` so that each `c·cᵢ` is the image of some `ρᵢ ∈ R`, whence `c·a = fiberMap (Σ ρᵢ tᵢ)`
using `r • (1 ⊗ t) = 1 ⊗ (r • t)`. Set `g₁ := Σ ρᵢ tᵢ`. Then `fiberMap g₁ = c·a ∈ I` (so
`D(fiberMap g₁) ⊆ V(I)ᶜ = U`) and `fiberMap g₁ ∉ qbar` (as `c` is a unit, `a ∉ qbar`). -/
private theorem exists_image_basicOpen_subset
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime]
    (qbar : PrimeSpectrum (p.Fiber S))
    (U : Set (PrimeSpectrum (p.Fiber S))) (hU : IsOpen U) (hq : qbar ∈ U) :
    ∃ g₁ : S, qbar ∈ (PrimeSpectrum.basicOpen (fiberMap R S p g₁) : Set _) ∧
      (PrimeSpectrum.basicOpen (fiberMap R S p g₁) : Set _) ⊆ U := by
  classical
  -- Now the main argument
  set I := PrimeSpectrum.vanishingIdeal Uᶜ with hI
  have hZ : Uᶜ = PrimeSpectrum.zeroLocus (I : Set (p.Fiber S)) := by
    rw [hI, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, (hU.isClosed_compl).closure_eq]
  have hInotle : ¬ (I ≤ qbar.asIdeal) := by
    intro hle
    have hmem : qbar ∈ Uᶜ := by
      rw [hZ]; exact fun x hx => hle hx
    exact hmem hq
  obtain ⟨a, haI, haq⟩ := Set.not_subset.mp hInotle
  obtain ⟨g₁, c, hcunit, hg1eq⟩ := exists_fiberMap_eq_unit_smul R S p a
  refine ⟨g₁, ?_, ?_⟩
  · -- qbar ∈ basicOpen (fiberMap g₁): fiberMap g₁ ∉ qbar.asIdeal
    change fiberMap R S p g₁ ∉ qbar.asIdeal
    rw [hg1eq, Algebra.smul_def]
    intro h
    rcases qbar.isPrime.mem_or_mem h with h1 | h2
    · exact qbar.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 (hcunit.map _))
    · exact haq h2
  · -- basicOpen (fiberMap g₁) ⊆ U: fiberMap g₁ ∈ I
    have hg1I : fiberMap R S p g₁ ∈ I := by
      rw [hg1eq, Algebra.smul_def]
      exact I.mul_mem_left _ haI
    rw [PrimeSpectrum.basicOpen_eq_zeroLocus_compl]
    rw [Set.compl_subset_comm, hZ]
    apply PrimeSpectrum.zeroLocus_anti_mono
    simpa using hg1I

-- Ingredients for the final assembly (Steps C, D and E) of Stacks 00QE.

/-- (Step D/E core, Stacks 00QA/00Q9, Zariski's main property) If `R → S₁` is a finite type
ring map that is *weakly quasi-finite at* the prime `q₁` (an isolated/quasi-finite-type point
of the fibre), then there is `r ∉ q₁` such that the localization `(S₁)_r` is quasi-finite over
`R` at *every* prime (i.e. `Algebra.QuasiFinite R (Localization.Away r)`). This is the
openness of the quasi-finite locus: the quasi-finite-at-`q₁` point has a basic open
neighborhood `D(r)` on which quasi-finiteness holds everywhere. PROVED via
`Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective` (which extracts a
finite subalgebra `S'` and `r` with `(S')_r ≅ (S₁)_r`), then `Module.Finite ⇒ QuasiFinite`
(`Algebra.QuasiFinite.instLocalization`) transported across the algebra isomorphism
(`Algebra.QuasiFinite.iff_of_algEquiv`). -/
@[ega "II 6.2.1" "(b) ⇒ (a), affine case", ega "IV 13.1.4" "special case"]
private theorem exists_quasiFinite_localization_of_wqf
    (B S₁ : Type*) [CommRing B] [CommRing S₁] [Algebra B S₁] [Algebra.FiniteType B S₁]
    (q₁ : Ideal S₁) [q₁.IsPrime] [Algebra.WeaklyQuasiFiniteAt B q₁] :
    ∃ r : S₁, r ∉ q₁ ∧ Algebra.QuasiFinite B (Localization.Away r) := by
  obtain ⟨S', hfg, r, hr, hbij⟩ :=
    Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective (R := B) q₁
  refine ⟨(r : S₁), hr, ?_⟩
  have : Module.Finite B S' := Module.Finite.iff_fg.mpr hfg
  have : Algebra.QuasiFinite B S' := inferInstance
  have : Algebra.QuasiFinite B (Localization.Away r) := Algebra.QuasiFinite.instLocalization _
  let φ := Localization.awayMapₐ S'.val r
  let e := AlgEquiv.ofBijective φ hbij
  exact (Algebra.QuasiFinite.iff_of_algEquiv e).mp ‹_›

-- needed: a `rw` in `weaklyQuasiFiniteAt_of_finite_fiber` matches only when defeq unfolds
-- the residue-field fibre `κ(p₁).Fiber` past the default transparency
set_option backward.isDefEq.respectTransparency false in
/-- (Step D descent, Stacks 00PM/00PN) Quasi-finiteness from the residue-field fibre. If the
finite-type `B`-algebra `S₁` has the property that the fibre `κ(p₁).Fiber S₁` over the prime
`p₁ = q₁ ∩ B` is a finite `κ(p₁)`-vector space, then `B → S₁` is weakly quasi-finite at `q₁`
(`Algebra.WeaklyQuasiFiniteAt B q₁`). This is exactly `Algebra.quasiFinite_iff`'s
characterization at a single prime, packaged via
`Algebra.WeaklyQuasiFiniteAt.of_quasiFiniteAt_residueField`: one produces the fibre prime
`Q ⊆ κ(p₁).Fiber S₁` lying over `q₁` (`Ideal.comap TensorProduct.includeRight Q = q₁`) and
notes `QuasiFiniteAt κ(p₁) Q` holds because `Module.Finite κ(p₁) (κ(p₁).Fiber S₁) ⇒
WeaklyQuasiFiniteAt κ(p₁) Q ⇒ QuasiFiniteAt κ(p₁) Q` (`QuasiFiniteAt.of_weaklyQuasiFiniteAt`).
TO PROVE: construct the fibre prime `Q` over `q₁` (use the surjection / lying-over for the
fibre `S₁ → κ(p₁).Fiber S₁`, `Algebra.TensorProduct.includeRight`), discharge the `LiesOver`
and `comap` side conditions, and apply the cited lemmas. -/
private theorem weaklyQuasiFiniteAt_of_finite_fiber
    (B S₁ : Type*) [CommRing B] [CommRing S₁] [Algebra B S₁] [Algebra.FiniteType B S₁]
    (q₁ : Ideal S₁) [q₁.IsPrime]
    (hfin : Module.Finite (q₁.under B).ResidueField ((q₁.under B).Fiber S₁)) :
    Algebra.WeaklyQuasiFiniteAt B q₁ := by
  -- p₁ := q₁.under B is prime and q₁ lies over it.
  -- Build Q : Ideal ((q₁.under B).Fiber S₁) with comap includeRight Q = q₁; then
  -- `Module.Finite κ(p₁) (fibre) ⇒ QuasiFiniteAt κ(p₁) Q` (via WeaklyQuasiFiniteAt), and
  -- `WeaklyQuasiFiniteAt.of_quasiFiniteAt_residueField` closes the goal. (Stacks 00PM/00PN.)
  set p₁ := q₁.under B with hp₁
  have : p₁.IsPrime := Ideal.IsPrime.under B q₁
  have : q₁.LiesOver p₁ := ⟨rfl⟩
  have : IsScalarTower B S₁ q₁.ResidueField := inferInstance
  -- The residue-field map `κ(p₁) → κ(q₁)`, built via `Ideal.ResidueField.lift` of
  -- `algebraMap B κ(q₁)` (which kills `p₁ = q₁ ∩ B` and inverts `p₁`'s complement).
  have hker : RingHom.ker (algebraMap B q₁.ResidueField) = p₁ := by
    ext y
    rw [RingHom.mem_ker, IsScalarTower.algebraMap_apply B S₁ q₁.ResidueField,
      Ideal.algebraMap_residueField_eq_zero]
    rfl
  have hle : p₁ ≤ RingHom.ker (algebraMap B q₁.ResidueField) := hker.ge
  have hunit : p₁.primeCompl ≤
      Submonoid.comap (algebraMap B q₁.ResidueField) (IsUnit.submonoid q₁.ResidueField) := by
    intro x hx
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
    rw [isUnit_iff_ne_zero, ne_eq, ← RingHom.mem_ker, hker]
    exact hx
  let fκ : p₁.ResidueField →+* q₁.ResidueField :=
    Ideal.ResidueField.lift p₁ (algebraMap B q₁.ResidueField) hle hunit
  have hfκ_alg : ∀ x : B, fκ (algebraMap B p₁.ResidueField x) = algebraMap B q₁.ResidueField x :=
    fun x => Ideal.ResidueField.lift_algebraMap p₁ (algebraMap B q₁.ResidueField) hle hunit x
  let fAlg : p₁.ResidueField →ₐ[B] q₁.ResidueField := AlgHom.mk' fκ (by
    intro c x
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, hfκ_alg c])
  let gAlg : S₁ →ₐ[B] q₁.ResidueField := IsScalarTower.toAlgHom B S₁ q₁.ResidueField
  -- The induced `B`-algebra map `h : κ(p₁) ⊗_B S₁ = p₁.Fiber S₁ → κ(q₁)`.
  let h : (p₁.Fiber S₁) →ₐ[B] q₁.ResidueField :=
    Algebra.TensorProduct.lift fAlg gAlg (fun x y => mul_comm _ _)
  -- `Q := ker h` is a prime of the fibre, and it lies over `q₁`.
  set Q : Ideal (p₁.Fiber S₁) := RingHom.ker h.toRingHom with hQ
  have : Q.IsPrime := by
    rw [hQ]; exact RingHom.ker_isPrime h.toRingHom
  have hcomp : h.toRingHom.comp (fiberMap B S₁ p₁) = algebraMap S₁ q₁.ResidueField := by
    ext s
    simp only [RingHom.comp_apply, fiberMap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.includeRight_apply]
    change h (1 ⊗ₜ[B] s) = algebraMap S₁ q₁.ResidueField s
    rw [Algebra.TensorProduct.lift_tmul]
    simp [fAlg, gAlg, IsScalarTower.coe_toAlgHom']
  have hcomapQ : Ideal.comap (fiberMap B S₁ p₁) Q = q₁ := by
    rw [hQ, RingHom.comap_ker, hcomp]
    exact Ideal.ker_algebraMap_residueField q₁
  -- `Module.Finite κ(p₁) (p₁.Fiber S₁) ⇒ WeaklyQuasiFiniteAt κ(p₁) Q ⇒ QuasiFiniteAt κ(p₁) Q`.
  have : Algebra.WeaklyQuasiFiniteAt p₁.ResidueField Q := inferInstance
  have : Algebra.QuasiFiniteAt p₁.ResidueField Q :=
    Algebra.QuasiFiniteAt.of_weaklyQuasiFiniteAt Q
  have hcomapQ' : Ideal.comap Algebra.TensorProduct.includeRight.toRingHom Q = q₁ := hcomapQ
  exact Algebra.WeaklyQuasiFiniteAt.of_quasiFiniteAt_residueField p₁ q₁ Q hcomapQ'

/-- Rescaling each generator by a unit of the base field does not change module-finiteness of
the `MvPolynomial` evaluation map: if `(aeval z)` is module-finite then so is
`(aeval (fun i => c i • z i))` whenever each `c i` is a unit. The rescaling map
`X i ↦ C (c i) * X i` is an algebra automorphism (its inverse rescales by `c i⁻¹`), hence
surjective, and `aeval (c • z) = (aeval z).comp (rescale)`. -/
private theorem aeval_finite_of_unit_smul {κ A : Type*} [Field κ] [CommRing A] [Algebra κ A]
    {n : ℕ} (z : Fin n → A) (c : Fin n → κ) (hc : ∀ i, IsUnit (c i))
    (hz : (MvPolynomial.aeval z : MvPolynomial (Fin n) κ →ₐ[κ] A).toRingHom.Finite) :
    (MvPolynomial.aeval (fun i => c i • z i) : MvPolynomial (Fin n) κ →ₐ[κ] A).toRingHom.Finite
      := by
  classical
  let f : MvPolynomial (Fin n) κ →ₐ[κ] MvPolynomial (Fin n) κ :=
    MvPolynomial.aeval (fun i => MvPolynomial.C (c i) * MvPolynomial.X i)
  let g : MvPolynomial (Fin n) κ →ₐ[κ] MvPolynomial (Fin n) κ :=
    MvPolynomial.aeval (fun i => MvPolynomial.C (c i)⁻¹ * MvPolynomial.X i)
  have hne : ∀ i, c i ≠ 0 := fun i => (hc i).ne_zero
  have hfg : f.comp g = AlgHom.id κ _ := by
    apply MvPolynomial.algHom_ext
    intro i
    change (MvPolynomial.aeval fun i => MvPolynomial.C (c i) * MvPolynomial.X i)
        ((MvPolynomial.aeval fun i => MvPolynomial.C (c i)⁻¹ * MvPolynomial.X i)
          (MvPolynomial.X i)) = MvPolynomial.X i
    rw [MvPolynomial.aeval_X, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      MvPolynomial.algebraMap_eq, ← mul_assoc, ← MvPolynomial.C_mul,
      inv_mul_cancel₀ (hne i), MvPolynomial.C_1, one_mul]
  have hfsurj : Function.Surjective f := fun x =>
    ⟨g x, by rw [← AlgHom.comp_apply, hfg, AlgHom.id_apply]⟩
  have hcomp : (MvPolynomial.aeval (fun i => c i • z i) :
      MvPolynomial (Fin n) κ →ₐ[κ] A) = (MvPolynomial.aeval z).comp f := by
    rw [MvPolynomial.comp_aeval]
    congr 1
    funext i
    change c i • z i = (MvPolynomial.aeval z) (MvPolynomial.C (c i) * MvPolynomial.X i)
    rw [map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, Algebra.smul_def]
  rw [show ((MvPolynomial.aeval (fun i => c i • z i) :
      MvPolynomial (Fin n) κ →ₐ[κ] A).toRingHom) = ((MvPolynomial.aeval z).comp f).toRingHom from
        by rw [hcomp]]
  exact RingHom.Finite.comp hz (RingHom.Finite.of_surjective f.toRingHom hfsurj)

/-- Noether normalization of the fibre together with a denominator-clearing lift
(Stacks tag 00OW). Given the basic localization `S₁ = S_{g₁}` whose fibre spectrum has
topological Krull dimension `n`, there exist `n` elements `y : Fin n → S₁` such that the
`κ(p)`-algebra map `κ(p)[t₁,…,tₙ] → p.Fiber S₁` with `tᵢ ↦ (1 ⊗ yᵢ) = fiberMap yᵢ` is
module-finite.

Noether normalization of the finitely generated `κ(p)`-algebra `p.Fiber S₁` gives some `s`
and a module-finite injective `κ(p)[t_s] → p.Fiber S₁`; comparing Krull dimensions pins
`s = n`, since a finite injective map preserves `ringKrullDim`, the dimension of
`κ(p)[t_s]` is `s` because `κ(p)` is a field, and the topological Krull dimension of the
fibre spectrum is its ring-theoretic one. This yields `z : Fin n → p.Fiber S₁` with
`(aeval z).Finite`. Each `zᵢ` then lifts to `yᵢ ∈ S₁` by clearing denominators, giving
`fiberMap yᵢ = cᵢ • zᵢ` for a `κ(p)`-unit `cᵢ`; since the `cᵢ` are units,
`κ(p)[fiberMap y] = κ(p)[z]`, so `aeval (fiberMap ∘ y)` is still module-finite. -/
private theorem normLift_aeval_finite
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (p : Ideal R) [hp : p.IsPrime] (n : ℕ) (g₁ : S)
    (hg1dim : topologicalKrullDim (PrimeSpectrum (p.Fiber (Localization.Away g₁))) = (n : ℕ∞)) :
    ∃ y : Fin n → Localization.Away g₁,
      ((MvPolynomial.aeval (fun i => fiberMap R (Localization.Away g₁) p (y i)) :
        MvPolynomial (Fin n) p.ResidueField →ₐ[p.ResidueField]
          p.Fiber (Localization.Away g₁)).toRingHom).Finite := by
  classical
  set S₁ := Localization.Away g₁ with hS₁
  set F := p.Fiber S₁ with hF
  set κ := p.ResidueField with hκ
  -- ════════════════════════════════════════════════════════════════════════════════
  -- Part A: Noether-normalize the fibre to get z : Fin n → F with (aeval z).Finite.
  -- ════════════════════════════════════════════════════════════════════════════════
  -- F is nontrivial because its spectrum is nonempty (dimension is a finite n ≠ ⊥).
  have hntF : Nontrivial F := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have : Subsingleton F := h
    have : IsEmpty (PrimeSpectrum F) := PrimeSpectrum.isEmpty_iff_subsingleton.mpr ‹_›
    have hbot : topologicalKrullDim (PrimeSpectrum F) = ⊥ :=
      (topologicalKrullDim_eq_bot_iff_isEmpty (PrimeSpectrum F)).mpr ‹_›
    rw [show topologicalKrullDim (PrimeSpectrum F) = topologicalKrullDim
        (PrimeSpectrum (p.Fiber (Localization.Away g₁))) from rfl, hg1dim] at hbot
    exact (WithBot.natCast_ne_bot n) hbot
  have hdimS : ringKrullDim F = (n : ℕ∞) := by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]; exact hg1dim
  obtain ⟨s, gg, hginj, hgfin⟩ := exists_finite_inj_algHom_of_fg κ F
  have hks : ringKrullDim (MvPolynomial (Fin s) κ) = (s : ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing]
    simp [ringKrullDim_eq_zero_of_field]
  have hsn : s = n := by
    have := ringKrullDim_eq_of_finite_injective gg.toRingHom hgfin hginj
    rw [hdimS, hks] at this
    exact_mod_cast this.symm
  subst hsn
  -- z i := gg (X i); then aeval z = gg is module-finite.
  set z : Fin s → F := fun i => gg (MvPolynomial.X i) with hz
  have hzfin : ((MvPolynomial.aeval z : MvPolynomial (Fin s) κ →ₐ[κ] F).toRingHom).Finite := by
    have hgeq : (MvPolynomial.aeval z : MvPolynomial (Fin s) κ →ₐ[κ] F) = gg :=
      (MvPolynomial.aeval_unique gg).symm
    rw [hgeq]; exact hgfin
  -- ════════════════════════════════════════════════════════════════════════════════
  -- Part B: lift z to y : Fin s → S₁ with fiberMap (y i) = c i • z i (c i a unit).
  -- ════════════════════════════════════════════════════════════════════════════════
  choose y c hcunit hyeq using exists_fiberMap_eq_unit_smul R S₁ p
  -- Build the final witness: y ∘ z gives the lift.
  refine ⟨fun i => y (z i), ?_⟩
  -- fiberMap (y (z i)) = c (z i) • z i, with c (z i) a unit.
  have hpt : (fun i => fiberMap R S₁ p (y (z i))) = (fun i => c (z i) • z i) := by
    funext i; exact hyeq (z i)
  rw [show (fun i => fiberMap R S₁ p (y (z i))) = (fun i => c (z i) • z i) from hpt]
  exact aeval_finite_of_unit_smul z (fun i => c (z i)) (fun i => hcunit (z i)) hzfin

/-- The image of a prime `q` under the localization-away map
`S → S_{g₁} = Localization.Away g₁` is prime, provided `g₁ ∉ q`. This is the standard
correspondence: primes of `S_{g₁}` are the primes of `S` disjoint from the submonoid
`{g₁ⁿ}`, and `g₁ ∉ q` means `q` is disjoint from that monoid, so its extension
`q.map (algebraMap S S_{g₁})` is prime. -/
private theorem map_away_isPrime_of_notMem
    (S : Type*) [CommRing S] (g₁ : S) (q : PrimeSpectrum S) (hg1q : g₁ ∉ q.asIdeal) :
    (q.asIdeal.map (algebraMap S (Localization.Away g₁))).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g₁) (Localization.Away g₁)
    q.asIdeal q.isPrime ((Ideal.disjoint_powers_iff_notMem g₁ q.isPrime.isRadical).2 hg1q)

-- The prime `q ⊂ S` corresponding to a point `qbar` of the fibre over `p`
-- contracts to `p` in `R`.
private theorem fiber_qR_eq_p (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) (p : Ideal R) [hp : p.IsPrime]
    (qbar : PrimeSpectrum (p.Fiber S))
    (hqbar : PrimeSpectrum.comap (fiberMap R S p) qbar = q) :
    q.asIdeal.comap (algebraMap R S) = p := by
  have hcomp : (fiberMap R S p).comp (algebraMap R S) = algebraMap R (p.Fiber S) := by
    ext r
    simp only [RingHom.comp_apply, fiberMap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [← Algebra.TensorProduct.includeRight.commutes r]
  have hq : q.asIdeal = Ideal.comap (fiberMap R S p) qbar.asIdeal := by rw [← hqbar]; rfl
  rw [hq, Ideal.comap_comap, hcomp]
  have htower : algebraMap R (p.Fiber S) =
      (algebraMap p.ResidueField (p.Fiber S)).comp (algebraMap R p.ResidueField) := by
    rw [← IsScalarTower.algebraMap_eq]
  rw [htower, ← Ideal.comap_comap]
  set J := Ideal.comap (algebraMap p.ResidueField (p.Fiber S)) qbar.asIdeal with hJ
  have : J.IsPrime := Ideal.IsPrime.comap _
  have hJbot : J = ⊥ := (Ideal.eq_bot_or_top J).resolve_right this.ne_top
  rw [hJbot, ← RingHom.ker_eq_comap_bot]
  exact Ideal.ker_algebraMap_residueField p

-- Action of `MvPolynomial.scalarRTensorAlgEquiv` on `monomial`-tensors, needed to
-- show it is a `B = MvPolynomial _ R`-algebra map onto `MvPolynomial _ κ`.
-- After the Mathlib bump `scalarRTensorAlgEquiv : N ⊗[R] MvPolynomial σ R ≃ₐ[N] MvPolynomial σ N`
-- takes the scalar factor `N` on the *left*, so the tensor is `a ⊗ₜ monomial d r`.
private theorem scalarRTensorAlgEquiv_monomial_tmul
    (R κ : Type*) (n : ℕ) [CommRing R] [CommRing κ] [Algebra R κ]
    (d : Fin n →₀ ℕ) (r : R) (a : κ) :
    (MvPolynomial.scalarRTensorAlgEquiv (R := R) (σ := Fin n) (N := κ))
      (a ⊗ₜ[R] (MvPolynomial.monomial d r))
      = MvPolynomial.monomial d ((Algebra.TensorProduct.lid R κ) (r ⊗ₜ[R] a)) := by
  rw [show (MvPolynomial.scalarRTensorAlgEquiv (R := R) (σ := Fin n) (N := κ))
        = MvPolynomial.algebraTensorAlgEquiv R κ from rfl,
    MvPolynomial.algebraTensorAlgEquiv_tmul, MvPolynomial.map_monomial,
    MvPolynomial.smul_monomial, Algebra.TensorProduct.lid_tmul]
  congr 1
  rw [smul_eq_mul, Algebra.smul_def, mul_comm]

set_option maxHeartbeats 400000 in
-- needed: `module_finite_residueField_fiber_descent` exhausts the default budget in `whnf`
/-- Base change of the normalization through residue fields (Stacks tag 00PM). Given the
`B = R[t₁,…,tₙ]`-algebra structure `instB` on `S₁ = S_{g₁}` defined by `tᵢ ↦ yᵢ`, i.e.
`algebraMap B S₁ = (aeval y).toRingHom`, together with the `κ(p)`-fibre normalization
saying that `aeval (fiberMap ∘ y)` is module-finite, the residue-field fibre
`κ(p₁).Fiber S₁` over `B`, with `p₁ = q₁.under B`, is module-finite over `κ(p₁)`.

Since `qbar` is a fibre point, `q ∩ R = p`, hence `p₁ ∩ R = q₁ ∩ R = q ∩ R = p` by the
scalar tower `R → B → S₁`, which gives a `κ(p)`-algebra map
`φ : κ(p)[t] = B ⊗_R κ(p) → κ(p₁)` through `B/p₁ ↪ κ(p₁)`. Tensor cancellation identifies
`κ(p₁).Fiber S₁ = S₁ ⊗_B κ(p₁) ≅ (S₁ ⊗_R κ(p)) ⊗_{κ(p)[t]} κ(p₁) = (p.Fiber S₁) ⊗_{κ(p)[t]} κ(p₁)`.
As `p.Fiber S₁` is module-finite over `κ(p)[t]` via `aeval (fiberMap ∘ y)`, base change
along `φ` makes it module-finite over `κ(p₁)`; the `aeval (fiberMap ∘ y)` structure agrees
with the `instB`-induced `κ(p)[t]`-structure on `p.Fiber S₁`. -/
private theorem module_finite_residueField_fiber_descent
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (q : PrimeSpectrum S) (p : Ideal R) [hp : p.IsPrime]
    (qbar : PrimeSpectrum (p.Fiber S))
    (hqbar : PrimeSpectrum.comap (fiberMap R S p) qbar = q)
    (n : ℕ) (g₁ : S) (hg1q : g₁ ∉ q.asIdeal)
    (y : Fin n → Localization.Away g₁)
    (hyfin : ((MvPolynomial.aeval (fun i => fiberMap R (Localization.Away g₁) p (y i)) :
        MvPolynomial (Fin n) p.ResidueField →ₐ[p.ResidueField]
          p.Fiber (Localization.Away g₁)).toRingHom).Finite)
    (instB : Algebra (MvPolynomial (Fin n) R) (Localization.Away g₁))
    (hinstB : (algebraMap (MvPolynomial (Fin n) R) (Localization.Away g₁))
      = (MvPolynomial.aeval y).toRingHom)
    (q₁ : Ideal (Localization.Away g₁)) [q₁.IsPrime]
    (hq₁eq : q₁ = q.asIdeal.map (algebraMap S (Localization.Away g₁))) :
    Module.Finite (q₁.under (MvPolynomial (Fin n) R)).ResidueField
      ((q₁.under (MvPolynomial (Fin n) R)).Fiber (Localization.Away g₁)) := by
  classical
  -- scalar tower R → B → S₁
  have towerRBS : IsScalarTower R (MvPolynomial (Fin n) R) (Localization.Away g₁) := by
    refine IsScalarTower.of_algebraMap_eq (fun r => ?_)
    rw [hinstB]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.algebraMap_eq,
      MvPolynomial.aeval_C]
  -- scalar tower R → S → S₁
  have towerRSS : IsScalarTower R S (Localization.Away g₁) :=
    IsScalarTower.of_algebraMap_eq (fun r => by
      rw [IsScalarTower.algebraMap_apply R S (Localization.Away g₁)])
  -- (1) lying over: p₁ ∩ R = p
  have hdisj : Disjoint (↑(Submonoid.powers g₁) : Set S) (↑q.asIdeal : Set S) := by
    rw [Set.disjoint_left]
    rintro x ⟨k, rfl⟩ hxq
    exact hg1q (q.isPrime.mem_of_pow_mem k hxq)
  have hq1S : Ideal.comap (algebraMap S (Localization.Away g₁)) q₁ = q.asIdeal := by
    rw [hq₁eq, ← Ideal.under_def]
    exact IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers g₁)
      (Localization.Away g₁) q.isPrime hdisj
  have hp1R : Ideal.comap (algebraMap R (MvPolynomial (Fin n) R))
      (q₁.under (MvPolynomial (Fin n) R)) = p := by
    rw [Ideal.under_def, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq,
      IsScalarTower.algebraMap_eq R S (Localization.Away g₁), ← Ideal.comap_comap, hq1S]
    exact fiber_qR_eq_p R S q p qbar hqbar
  set B := MvPolynomial (Fin n) R with hB
  set κ := p.ResidueField with hκ
  set p₁ := q₁.under B with hp₁
  set κ₁ := p₁.ResidueField with hκ₁
  set F := p.Fiber (Localization.Away g₁) with hF
  -- (2) κ = p.ResidueField → κ₁ algebra structure (from lying over)
  let algκκ₁ : Algebra κ κ₁ :=
    (Ideal.ResidueField.map p p₁ (algebraMap R B) hp1R.symm).toAlgebra
  -- scalar tower R → κ → κ₁
  have towerRκκ₁ : IsScalarTower R κ κ₁ := by
    refine IsScalarTower.of_algebraMap_eq (fun r => ?_)
    change algebraMap R κ₁ r = (Ideal.ResidueField.map p p₁ (algebraMap R B) hp1R.symm)
      (algebraMap R κ r)
    rw [Ideal.ResidueField.map_algebraMap p p₁ (algebraMap R B) hp1R.symm r,
      ← IsScalarTower.algebraMap_apply R B κ₁]
  -- The polynomial ring over κ.
  set κt := MvPolynomial (Fin n) κ with hκt
  -- (3) algebra structures for the base-change chain.
  let instBκt : Algebra B κt := MvPolynomial.algebraMvPolynomial
  have hBκt : (algebraMap B κt) = MvPolynomial.map (algebraMap R κ) := rfl
  have towerRBκt : IsScalarTower R B κt := by
    refine IsScalarTower.of_algebraMap_eq (fun r => ?_)
    rw [hBκt]
    change MvPolynomial.C (algebraMap R κ r) = MvPolynomial.map (algebraMap R κ) (algebraMap R B r)
    rw [MvPolynomial.algebraMap_eq, MvPolynomial.map_C]
  -- φ : κt → κ₁ as a κ-algebra map sending tᵢ ↦ (image of tᵢ in κ₁).
  let instκtκ₁ : Algebra κt κ₁ :=
    (MvPolynomial.aeval (R := κ) (fun i => algebraMap B κ₁ (MvPolynomial.X i))).toRingHom.toAlgebra
  have hκtκ₁map : (algebraMap κt κ₁)
      = (MvPolynomial.aeval (R := κ) (fun i => algebraMap B κ₁ (MvPolynomial.X i))).toRingHom := rfl
  -- scalar tower B → κt → κ₁
  have towerBκtκ₁ : IsScalarTower B κt κ₁ := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    rw [hκtκ₁map, hBκt]
    apply MvPolynomial.ringHom_ext
    · intro r
      change (algebraMap B κ₁) (MvPolynomial.C r)
        = (MvPolynomial.aeval fun i => (algebraMap B κ₁) (MvPolynomial.X i))
          ((MvPolynomial.map (algebraMap R κ)) (MvPolynomial.C r))
      rw [MvPolynomial.map_C, MvPolynomial.aeval_C,
        show (MvPolynomial.C r : B) = algebraMap R B r from rfl,
        ← IsScalarTower.algebraMap_apply R B κ₁ r, IsScalarTower.algebraMap_apply R κ κ₁ r]
    · intro i
      change (algebraMap B κ₁) (MvPolynomial.X i)
        = (MvPolynomial.aeval fun i => (algebraMap B κ₁) (MvPolynomial.X i))
          ((MvPolynomial.map (algebraMap R κ)) (MvPolynomial.X i))
      rw [MvPolynomial.map_X, MvPolynomial.aeval_X]
  -- (4) κt acts on F = p.Fiber (Localization.Away g₁) via the normalization aeval; hyfin is
  -- finiteness over κt.
  let instκtF : Algebra κt F :=
    (MvPolynomial.aeval (fun i => fiberMap R (Localization.Away g₁) p (y i)) :
      κt →ₐ[κ] F).toRingHom.toAlgebra
  have hκtFmap : (algebraMap κt F)
      = (MvPolynomial.aeval (fun i => fiberMap R (Localization.Away g₁) p (y i)) :
        κt →ₐ[κ] F).toRingHom := rfl
  have hFin_κt : Module.Finite κt F := hyfin
  -- B-algebra equiv κt ≃ₐ[B] (κ ⊗_R B): upgrade scalarRTensorAlgEquiv to B-linearity.
  let e0B : TensorProduct R B κ ≃ₐ[B] κt :=
    { ((Algebra.TensorProduct.comm R B κ).toRingEquiv.trans
        (MvPolynomial.scalarRTensorAlgEquiv (R := R) (σ := Fin n) (N := κ)).toRingEquiv) with
      commutes' := fun b => by
        change (((Algebra.TensorProduct.comm R B κ).toRingEquiv.trans
            (MvPolynomial.scalarRTensorAlgEquiv (R := R) (σ := Fin n)
              (N := κ)).toRingEquiv)).toRingHom.comp
            (algebraMap B (TensorProduct R B κ)) b = algebraMap B κt b
        revert b
        rw [← RingHom.ext_iff]
        apply MvPolynomial.ringHom_ext
        · intro r
          change (MvPolynomial.scalarRTensorAlgEquiv (R := R) (σ := Fin n) (N := κ))
              ((Algebra.TensorProduct.comm R B κ)
                (algebraMap B (TensorProduct R B κ) (MvPolynomial.C r)))
            = algebraMap B κt (MvPolynomial.C r)
          rw [show algebraMap B (TensorProduct R B κ) (MvPolynomial.C r)
              = (MvPolynomial.C r) ⊗ₜ[R] (1:κ) from rfl,
            Algebra.TensorProduct.comm_tmul,
            show (MvPolynomial.C r : B) = MvPolynomial.monomial 0 r from rfl,
            scalarRTensorAlgEquiv_monomial_tmul R κ n 0 r 1,
            hBκt, MvPolynomial.map_monomial]
          simp [Algebra.TensorProduct.lid_tmul, Algebra.algebraMap_eq_smul_one]
        · intro i
          change (MvPolynomial.scalarRTensorAlgEquiv (R := R) (σ := Fin n) (N := κ))
              ((Algebra.TensorProduct.comm R B κ)
                (algebraMap B (TensorProduct R B κ) (MvPolynomial.X i)))
            = algebraMap B κt (MvPolynomial.X i)
          rw [show algebraMap B (TensorProduct R B κ) (MvPolynomial.X i)
              = (MvPolynomial.X i) ⊗ₜ[R] (1:κ) from rfl,
            Algebra.TensorProduct.comm_tmul,
            show (MvPolynomial.X i : B) = MvPolynomial.monomial (Finsupp.single i 1) 1 from rfl,
            scalarRTensorAlgEquiv_monomial_tmul R κ n (Finsupp.single i 1) 1 1,
            hBκt, MvPolynomial.map_monomial, map_one,
            show MvPolynomial.monomial (Finsupp.single i 1) (1:κ) = MvPolynomial.X i from rfl]
          rw [Algebra.TensorProduct.lid_tmul, one_smul]
          rfl }
  -- the inner ring equiv TensorProduct B κt (Localization.Away g₁) ≃+* F.
  let e_inner : TensorProduct B κt (Localization.Away g₁) ≃+* F :=
    ((Algebra.TensorProduct.comm B κt (Localization.Away g₁)).toRingEquiv.trans
      ((Algebra.TensorProduct.congr
            (AlgEquiv.refl (R := B) (A₁ := (Localization.Away g₁))) e0B.symm).toRingEquiv.trans
        ((Algebra.TensorProduct.cancelBaseChange R B B (Localization.Away g₁) κ).toRingEquiv.trans
          (Algebra.TensorProduct.comm R (Localization.Away g₁) κ).toRingEquiv)))
  -- inner coherence: e_inner intertwines the κt-algebra structure maps.
  have he0Bsymm_X : ∀ i : Fin n, e0B.symm (MvPolynomial.X i)
      = (MvPolynomial.X i : B) ⊗ₜ[R] (1:κ) := by
    intro i
    rw [AlgEquiv.symm_apply_eq]
    change MvPolynomial.X i
      = (MvPolynomial.scalarRTensorAlgEquiv (R := R) (σ := Fin n) (N := κ))
          ((Algebra.TensorProduct.comm R B κ) ((MvPolynomial.X i : B) ⊗ₜ[R] (1:κ)))
    rw [Algebra.TensorProduct.comm_tmul,
      show ((MvPolynomial.X i : B)) = MvPolynomial.monomial (Finsupp.single i 1) 1 from rfl,
      scalarRTensorAlgEquiv_monomial_tmul R κ n (Finsupp.single i 1) 1 1]
    rw [Algebra.TensorProduct.lid_tmul, one_smul]
    rfl
  have he0Bsymm_C : ∀ a : κ, e0B.symm (MvPolynomial.C a)
      = (1 : B) ⊗ₜ[R] a := by
    intro a
    rw [AlgEquiv.symm_apply_eq]
    change MvPolynomial.C a
      = (MvPolynomial.scalarRTensorAlgEquiv (R := R) (σ := Fin n) (N := κ))
          ((Algebra.TensorProduct.comm R B κ) ((1 : B) ⊗ₜ[R] a))
    rw [Algebra.TensorProduct.comm_tmul,
      show ((1 : B)) = MvPolynomial.monomial (0 : Fin n →₀ ℕ) 1 from rfl,
      scalarRTensorAlgEquiv_monomial_tmul R κ n (0 : Fin n →₀ ℕ) 1 a]
    rw [MvPolynomial.monomial_zero']
    congr 1
    rw [Algebra.TensorProduct.lid_tmul, one_smul]
  have key : ∀ c : κt, e_inner (algebraMap κt (TensorProduct B κt (Localization.Away g₁)) c)
      = algebraMap κt F c := by
    have hringhom : (e_inner.toRingHom.comp
        (algebraMap κt (TensorProduct B κt (Localization.Away g₁)))) = algebraMap κt F := by
      apply MvPolynomial.ringHom_ext
      · intro a
        change e_inner
            (algebraMap κt (TensorProduct B κt (Localization.Away g₁)) (MvPolynomial.C a))
          = algebraMap κt F (MvPolynomial.C a)
        rw [show algebraMap κt (TensorProduct B κt (Localization.Away g₁)) (MvPolynomial.C a)
            = (MvPolynomial.C a) ⊗ₜ[B] (1 : (Localization.Away g₁)) from rfl]
        change (Algebra.TensorProduct.comm R (Localization.Away g₁) κ)
            ((Algebra.TensorProduct.cancelBaseChange R B B (Localization.Away g₁) κ)
              ((Algebra.TensorProduct.congr
                  (AlgEquiv.refl (R := B) (A₁ := (Localization.Away g₁))) e0B.symm)
                ((Algebra.TensorProduct.comm B κt (Localization.Away g₁))
                  ((MvPolynomial.C a) ⊗ₜ[B] (1 : (Localization.Away g₁))))))
          = algebraMap κt F (MvPolynomial.C a)
        rw [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.congr_apply,
          Algebra.TensorProduct.map_tmul]
        erw [he0Bsymm_C,
          Algebra.TensorProduct.cancelBaseChange_tmul, Algebra.TensorProduct.comm_tmul]
        rw [hκtFmap]
        change a ⊗ₜ[R] ((1:B) • (1:(Localization.Away g₁)))
          = (MvPolynomial.aeval fun i => fiberMap R (Localization.Away g₁) p (y i))
              (MvPolynomial.C a)
        rw [one_smul, MvPolynomial.aeval_C]
        change a ⊗ₜ[R] (1:(Localization.Away g₁)) = algebraMap κ F a
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      · intro i
        change e_inner
            (algebraMap κt (TensorProduct B κt (Localization.Away g₁)) (MvPolynomial.X i))
          = algebraMap κt F (MvPolynomial.X i)
        rw [show algebraMap κt (TensorProduct B κt (Localization.Away g₁)) (MvPolynomial.X i)
            = (MvPolynomial.X i) ⊗ₜ[B] (1 : (Localization.Away g₁)) from rfl]
        change (Algebra.TensorProduct.comm R (Localization.Away g₁) κ)
            ((Algebra.TensorProduct.cancelBaseChange R B B (Localization.Away g₁) κ)
              ((Algebra.TensorProduct.congr
                  (AlgEquiv.refl (R := B) (A₁ := (Localization.Away g₁))) e0B.symm)
                ((Algebra.TensorProduct.comm B κt (Localization.Away g₁))
                  ((MvPolynomial.X i) ⊗ₜ[B] (1 : (Localization.Away g₁))))))
          = algebraMap κt F (MvPolynomial.X i)
        rw [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.congr_apply,
          Algebra.TensorProduct.map_tmul]
        erw [he0Bsymm_X,
          Algebra.TensorProduct.cancelBaseChange_tmul, Algebra.TensorProduct.comm_tmul]
        rw [hκtFmap]
        change (1:κ) ⊗ₜ[R] ((MvPolynomial.X i : B) • (1:(Localization.Away g₁)))
          = (MvPolynomial.aeval fun i => fiberMap R (Localization.Away g₁) p (y i))
              (MvPolynomial.X i)
        rw [MvPolynomial.aeval_X]
        have hsmul : (MvPolynomial.X i : B) • (1:(Localization.Away g₁)) = y i := by
          rw [Algebra.smul_def, mul_one, hinstB]
          change (MvPolynomial.aeval y).toRingHom (MvPolynomial.X i) = y i
          rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X]
        rw [hsmul]
        change (1:κ) ⊗ₜ[R] (y i) = fiberMap R (Localization.Away g₁) p (y i)
        rfl
    intro c
    exact congrFun (congrArg (fun f : κt →+* F => (f : κt → F)) hringhom) c
  have hcompat :
      (algebraMap κt (TensorProduct B κt (Localization.Away g₁))).comp
        (RingEquiv.refl κt).toRingHom
      = e_inner.symm.toRingHom.comp (algebraMap κt F) := by
    apply RingHom.ext
    intro c
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.toRingHom_refl,
      RingHom.id_apply]
    rw [← key c]
    exact (RingEquiv.symm_apply_apply e_inner _).symm
  -- assemble.
  have hfin1 : Module.Finite κt (TensorProduct B κt (Localization.Away g₁)) :=
    Module.Finite.of_equiv_equiv (RingEquiv.refl κt) e_inner.symm hcompat
  have := Module.Finite.base_change κt κ₁ (TensorProduct B κt (Localization.Away g₁))
  refine Module.Finite.of_equiv_equiv (RingEquiv.refl κ₁)
    (Algebra.TensorProduct.cancelBaseChange B κt κ₁ κ₁ (Localization.Away g₁)).toRingEquiv ?_
  apply RingHom.ext
  intro x
  change (algebraMap κ₁ (TensorProduct B κ₁ (Localization.Away g₁))) x
    = (Algebra.TensorProduct.cancelBaseChange B κt κ₁ κ₁ (Localization.Away g₁))
      ((algebraMap κ₁ (TensorProduct κt κ₁ (TensorProduct B κt (Localization.Away g₁)))) x)
  change x ⊗ₜ[B] (1:(Localization.Away g₁))
    = (Algebra.TensorProduct.cancelBaseChange B κt κ₁ κ₁ (Localization.Away g₁))
      (x ⊗ₜ[κt] ((1:κt) ⊗ₜ[B] (1:(Localization.Away g₁))))
  rw [Algebra.TensorProduct.cancelBaseChange_tmul]
  simp

/-- (Steps B+D normalization/descent bridge, Stacks 00OW + 00PM) From a basic-localization
`S₁ = S_{g₁}` whose fibre spectrum has topological Krull dimension `n`, Noether-normalize the
fibre `κ(p).Fiber S₁` over the field `κ(p)` by `n` elements, *lift* them (denominator-clearing,
as in `exists_image_basicOpen_subset`) to `y : Fin n → S₁`, and equip `S₁` with the
`R[t₁,…,tₙ]`-algebra structure `instB` sending `tᵢ ↦ yᵢ` (`MvPolynomial.aeval y`). Output: that
algebra structure is an `R`-scalar-tower of finite type, the prime `q₁` of `S₁` corresponding
to `q` (the image ideal `q.asIdeal.map (algebraMap S S₁)`, prime since `g₁ ∉ q`) has its
residue-field fibre over `B = R[t]` module-finite — the hypothesis feeding the descent lemma
`weaklyQuasiFiniteAt_of_finite_fiber`. This is the geometric heart: the module-finiteness of
`κ(p).Fiber S₁` over `κ(p)[t]` (Noether normalization) descends, by base change through the
residue fields `κ(p)[t] → κ(p₁)` (`p₁ = q₁ ∩ B`), to module-finiteness of `κ(p₁).Fiber S₁`
over `κ(p₁)`. TO PROVE: (i) apply `exists_finite_inj_algHom_of_fg`/dimension-count (as in
`normLift_aeval_finite`) to `κ(p).Fiber S₁`, getting `z` with `(aeval z).Finite` and exactly `n`
variables (via `ringKrullDim_eq_of_finite_injective` + `hg1dim`); (ii) lift `z` to `y ⊆ S₁`;
(iii) build `instB`, `IsScalarTower`, `FiniteType`; (iv) the residue-field-fibre finiteness via
base change of the κ(p)-finiteness (`Algebra.QuasiFiniteAt.baseChange` / fibre-module-finite
characterization). -/
private theorem exists_normalization_lift
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (q : PrimeSpectrum S) (p : Ideal R) [hp : p.IsPrime]
    (qbar : PrimeSpectrum (p.Fiber S))
    (hqbar : PrimeSpectrum.comap (fiberMap R S p) qbar = q)
    (n : ℕ) (g₁ : S) (hg1q : g₁ ∉ q.asIdeal)
    (hg1dim : topologicalKrullDim (PrimeSpectrum (p.Fiber (Localization.Away g₁))) = (n : ℕ∞)) :
    ∃ (instB : Algebra (MvPolynomial (Fin n) R) (Localization.Away g₁)),
      letI := instB
      IsScalarTower R (MvPolynomial (Fin n) R) (Localization.Away g₁) ∧
      Algebra.FiniteType (MvPolynomial (Fin n) R) (Localization.Away g₁) ∧
      ∃ (q₁ : Ideal (Localization.Away g₁)) (_ : q₁.IsPrime),
        q₁ = q.asIdeal.map (algebraMap S (Localization.Away g₁)) ∧
        Module.Finite (q₁.under (MvPolynomial (Fin n) R)).ResidueField
          ((q₁.under (MvPolynomial (Fin n) R)).Fiber (Localization.Away g₁)) := by
  -- IsLocalization.isPrime_of_isPrime_disjoint; module-finiteness descends through the κ(p)-fibre)
  -- ════════════════════════════════════════════════════════════════════════════════
  -- The argument runs in four steps, each supplied by a lemma above: (a) Noether-normalize
  -- the fibre and lift to S₁; (b) build the B = R[t]-algebra structure, the scalar tower
  -- and finite type; (c) check that q₁ = q.map is prime; (d) descend module-finiteness
  -- through the residue fields. The two substantial steps are `normLift_aeval_finite`,
  -- for (a) and the lift in (b), and `module_finite_residueField_fiber_descent` for (d).
  classical
  set S₁ := Localization.Away g₁ with hS₁
  set B := MvPolynomial (Fin n) R with hB
  -- (a)+(b lift): obtain y : Fin n → S₁ such that the κ(p)-algebra map κ(p)[t] → p.Fiber S₁
  --   sending tᵢ ↦ (1 ⊗ yᵢ) is module-finite (Noether normalization of the fibre over κ(p),
  --   then denominator-clearing lift à la exists_image_basicOpen_subset).
  obtain ⟨y, hyfin⟩ := normLift_aeval_finite R S p n g₁ hg1dim
  -- (b): the B-algebra structure on S₁ sending tᵢ ↦ yᵢ, the R-scalar-tower, and finite type.
  let instB : Algebra B S₁ := (MvPolynomial.aeval y).toRingHom.toAlgebra
  -- IsScalarTower R B S₁ : algebraMap R S₁ = (algebraMap B S₁) ∘ (algebraMap R B)
  have htower : IsScalarTower R B S₁ := IsScalarTower.of_algebraMap_eq (fun r => by
    change algebraMap R S₁ r = (MvPolynomial.aeval y) (algebraMap R B r)
    rw [MvPolynomial.algebraMap_eq, MvPolynomial.aeval_C])
  refine ⟨instB, htower, ?_, ?_⟩
  · -- FiniteType B S₁ : S₁ is R-finite type, so B-finite type (R → B → S₁ scalar tower).
    exact Algebra.FiniteType.of_restrictScalars_finiteType R B S₁
  · -- (c) + (d): produce q₁ = q.map (prime), then descend module-finiteness.
    -- q₁ = q.map (algebraMap S S₁) is prime because g₁ ∉ q (localization away of a prime
    -- disjoint from {g₁ⁿ}). Isolated as `map_away_isPrime_of_notMem`.
    have hq₁prime : (q.asIdeal.map (algebraMap S S₁)).IsPrime :=
      map_away_isPrime_of_notMem S g₁ q hg1q
    refine ⟨q.asIdeal.map (algebraMap S S₁), hq₁prime, rfl, ?_⟩
    -- (d) THE DESCENT (Stacks 00PM base-change through residue fields):
    -- module-finiteness of p.Fiber S₁ over κ(p)[t] (= hyfin) descends to module-finiteness
    -- of κ(p₁).Fiber S₁ over κ(p₁), where p₁ = q₁.under B. Isolated as
    -- `module_finite_residueField_fiber_descent`.
    have hinstB : (algebraMap B S₁) = (MvPolynomial.aeval y).toRingHom := rfl
    exact module_finite_residueField_fiber_descent R S q p qbar hqbar n g₁ hg1q y hyfin
      instB hinstB (q.asIdeal.map (algebraMap S S₁)) rfl

/-- (Step E assembly, Stacks 02C6 + 00F4) Combine the two localizations and produce the final
witness. Given the `B = R[t₁,…,tₙ]`-algebra structure `instB` on `S₁ = S_{g₁}` (an `R`-scalar
tower) and an element `r ∉ q.asIdeal.map (algebraMap S S₁)` with `Algebra.QuasiFinite B
(Localization.Away r)`, write `r` as a unit multiple of the image of some `s ∈ S` (denominators
in `S₁` are powers of `g₁`, units) so that `Localization.Away r` is, as a `B`-algebra, a
localization of `S` away from a single `g := g₁ * s ∈ S` (`IsLocalization.Away.mul` /
`IsLocalization.localization_localization_isLocalization`, 02C6). Then `g ∉ q` (both `g₁ ∉ q`
and `s ∉ q`, the latter since `r ∉ q.map`), and define `φ : B →+* Localization.Away g` as the
B-algebra structure map; the commutation conjunct is `aeval`/scalar-tower naturality
(`IsScalarTower.algebraMap_apply`), `φ.FiniteType` is `Algebra.FiniteType B (Localization.Away
g)` (00F4, finite type of the localization composite), and `φ.QuasiFinite` is transported from
`hqf` across the `B`-algebra isomorphism `Localization.Away r ≅ Localization.Away g`
(`Algebra.QuasiFinite.iff_of_algEquiv` / `Algebra.QuasiFinite.of_isLocalization`). -/
private theorem exists_g_phi
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (q : PrimeSpectrum S) (n : ℕ) (g₁ : S) (hg1q : g₁ ∉ q.asIdeal)
    (instB : Algebra (MvPolynomial (Fin n) R) (Localization.Away g₁))
    (htower : IsScalarTower R (MvPolynomial (Fin n) R) (Localization.Away g₁))
    (r : Localization.Away g₁)
    (hr : r ∉ q.asIdeal.map (algebraMap S (Localization.Away g₁)))
    (hqf : Algebra.QuasiFinite (MvPolynomial (Fin n) R) (Localization.Away r)) :
    ∃ (g : S), g ∉ q.asIdeal ∧
      ∃ (φ : MvPolynomial (Fin n) R →+* Localization.Away g),
        φ.comp (algebraMap R (MvPolynomial (Fin n) R)) = algebraMap R (Localization.Away g) ∧
        φ.FiniteType ∧ φ.QuasiFinite := by
  -- so g = g₁*s ∉ q; Away r ≅ Away g over B via 02C6; transport FiniteType/QuasiFinite)
  classical
  let := instB
  have := htower
  -- Step 1: write `r = (image s) * unit`, with `s : S`.
  obtain ⟨⟨s, m⟩, hmk⟩ := IsLocalization.mk'_surjective (Submonoid.powers g₁) r
  obtain ⟨k, hk⟩ := m.property
  simp only at hmk hk
  have hunit : IsUnit (IsLocalization.mk' (Localization.Away g₁) (1 : S) m) := by
    apply IsUnit.of_mul_eq_one (b := algebraMap S (Localization.Away g₁) (m : S))
    rw [IsLocalization.mk'_spec]; simp
  have hru : r = algebraMap S (Localization.Away g₁) s
      * IsLocalization.mk' (Localization.Away g₁) 1 m := by
    rw [← hmk, IsLocalization.mk'_eq_mul_mk'_one]
  have hassoc : Associated r (algebraMap S (Localization.Away g₁) s) := by
    rw [hru]; exact associated_mul_unit_left _ _ hunit
  -- Step 2: `s ∉ q` (else `r ∈ q.map`, contradicting `hr`).
  have hsq : s ∉ q.asIdeal := by
    intro hs
    apply hr
    rw [hru]
    have hmem : algebraMap S (Localization.Away g₁) s
        ∈ q.asIdeal.map (algebraMap S (Localization.Away g₁)) := Ideal.mem_map_of_mem _ hs
    exact (q.asIdeal.map (algebraMap S (Localization.Away g₁))).mul_mem_right _ hmem
  -- The witness `g := g₁ * s`.
  refine ⟨g₁ * s, ?_, ?_⟩
  · -- `g₁ * s ∉ q` since `q` is prime and neither factor is in `q`.
    intro hmem
    rcases (q.isPrime.mem_or_mem hmem) with h | h
    · exact hg1q h
    · exact hsq h
  -- Step 3: set up `T := Localization.Away (g₁ * s)` as a `Localization.Away g₁`-algebra.
  have hg₁unitT : IsUnit (algebraMap S (Localization.Away (g₁ * s)) g₁) := by
    have h1 : IsUnit (algebraMap S (Localization.Away (g₁ * s)) (g₁ * s)) :=
      IsLocalization.Away.algebraMap_isUnit (g₁ * s)
    rw [map_mul] at h1; exact isUnit_of_mul_isUnit_left h1
  let algST : Algebra (Localization.Away g₁) (Localization.Away (g₁ * s)) :=
    (IsLocalization.Away.lift (S := Localization.Away g₁) g₁ hg₁unitT).toAlgebra
  have towerSST : IsScalarTower S (Localization.Away g₁) (Localization.Away (g₁ * s)) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      change algebraMap S (Localization.Away (g₁ * s)) x
          = (IsLocalization.Away.lift (S := Localization.Away g₁) g₁ hg₁unitT)
            (algebraMap S (Localization.Away g₁) x)
      rw [IsLocalization.Away.lift_eq]
  have hatower : ∀ x : S, algebraMap (Localization.Away g₁) (Localization.Away (g₁ * s))
      (algebraMap S (Localization.Away g₁) x) = algebraMap S (Localization.Away (g₁ * s)) x :=
    fun x => by rw [← IsScalarTower.algebraMap_apply]
  have hg₁unitS₁ : IsUnit (algebraMap S (Localization.Away g₁) g₁) :=
    IsLocalization.Away.algebraMap_isUnit g₁
  -- Step 4: the key localization instance `IsLocalization.Away (image s) T` over `Away g₁`.
  have keyLoc : IsLocalization (Submonoid.powers (algebraMap S (Localization.Away g₁) s))
      (Localization.Away (g₁ * s)) := by
    have hsT : IsUnit (algebraMap (Localization.Away g₁) (Localization.Away (g₁ * s))
        (algebraMap S (Localization.Away g₁) s)) := by
      rw [hatower s]
      have h1 : IsUnit (algebraMap S (Localization.Away (g₁ * s)) (g₁ * s)) :=
        IsLocalization.Away.algebraMap_isUnit (g₁ * s)
      rw [map_mul] at h1; exact isUnit_of_mul_isUnit_right h1
    refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
    · rintro ⟨y, j, rfl⟩
      rw [map_pow]; exact hsT.pow j
    · intro z
      obtain ⟨⟨a, mm⟩, hm⟩ := IsLocalization.surj (Submonoid.powers (g₁ * s)) z
      obtain ⟨l, hl⟩ := mm.property
      simp only at hm
      rw [← hl] at hm
      have hwk : IsUnit (algebraMap S (Localization.Away g₁) g₁ ^ l) := hg₁unitS₁.pow l
      refine ⟨⟨(hwk.unit⁻¹ : (Localization.Away g₁)ˣ) * algebraMap S (Localization.Away g₁) a,
        ⟨algebraMap S (Localization.Away g₁) s ^ l, l, rfl⟩⟩, ?_⟩
      simp only
      rw [map_mul, map_pow]
      rw [← hatower, ← hatower, map_pow, map_mul, mul_pow, map_mul, map_pow, map_pow] at hm
      have hUeq : (algebraMap (Localization.Away g₁) (Localization.Away (g₁ * s))
          (algebraMap S (Localization.Away g₁) g₁)) ^ l
          = algebraMap (Localization.Away g₁) (Localization.Away (g₁ * s))
              (hwk.unit : Localization.Away g₁) := by
        rw [hwk.unit_spec, map_pow]
      have hinv : (algebraMap (Localization.Away g₁) (Localization.Away (g₁ * s))
          (algebraMap S (Localization.Away g₁) g₁)) ^ l
          * algebraMap (Localization.Away g₁) (Localization.Away (g₁ * s))
              (hwk.unit⁻¹ : (Localization.Away g₁)ˣ) = 1 := by
        rw [hUeq, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
      set U := (algebraMap (Localization.Away g₁) (Localization.Away (g₁ * s))
        (algebraMap S (Localization.Away g₁) g₁)) ^ l with hU
      set V := (algebraMap (Localization.Away g₁) (Localization.Away (g₁ * s))
        (algebraMap S (Localization.Away g₁) s)) ^ l with hV
      set W := algebraMap (Localization.Away g₁) (Localization.Away (g₁ * s))
        (hwk.unit⁻¹ : (Localization.Away g₁)ˣ) with hW
      calc z * V = (W * U) * (z * V) := by rw [mul_comm W U, hinv, one_mul]
        _ = W * (z * (U * V)) := by ring
        _ = W * algebraMap (Localization.Away g₁) (Localization.Away (g₁ * s))
              (algebraMap S (Localization.Away g₁) a) := by rw [hm]
    · intro x y hxy
      obtain ⟨⟨ax, ⟨dx, ix, hix⟩⟩, hxe⟩ := IsLocalization.surj (Submonoid.powers g₁) x
      obtain ⟨⟨ay, ⟨dy, iy, hiy⟩⟩, hye⟩ := IsLocalization.surj (Submonoid.powers g₁) y
      simp only at hxe hye hix hiy
      subst hix hiy
      have hTx : algebraMap (Localization.Away g₁) (Localization.Away (g₁ * s)) x
          * algebraMap S (Localization.Away (g₁ * s)) (g₁ ^ ix)
          = algebraMap S (Localization.Away (g₁ * s)) ax := by
        have := congrArg (algebraMap (Localization.Away g₁) (Localization.Away (g₁ * s))) hxe
        rwa [map_mul, hatower, hatower] at this
      have hTy : algebraMap (Localization.Away g₁) (Localization.Away (g₁ * s)) y
          * algebraMap S (Localization.Away (g₁ * s)) (g₁ ^ iy)
          = algebraMap S (Localization.Away (g₁ * s)) ay := by
        have := congrArg (algebraMap (Localization.Away g₁) (Localization.Away (g₁ * s))) hye
        rwa [map_mul, hatower, hatower] at this
      have hTeq : algebraMap S (Localization.Away (g₁ * s)) (ax * g₁ ^ iy)
          = algebraMap S (Localization.Away (g₁ * s)) (ay * g₁ ^ ix) := by
        rw [map_mul, map_mul]
        calc algebraMap S (Localization.Away (g₁ * s)) ax
              * algebraMap S (Localization.Away (g₁ * s)) (g₁ ^ iy)
            = (algebraMap (Localization.Away g₁) (Localization.Away (g₁ * s)) x
                * algebraMap S (Localization.Away (g₁ * s)) (g₁ ^ ix))
                * algebraMap S (Localization.Away (g₁ * s)) (g₁ ^ iy) := by rw [hTx]
          _ = (algebraMap (Localization.Away g₁) (Localization.Away (g₁ * s)) y
                * algebraMap S (Localization.Away (g₁ * s)) (g₁ ^ iy))
                * algebraMap S (Localization.Away (g₁ * s)) (g₁ ^ ix) := by rw [hxy]; ring
          _ = algebraMap S (Localization.Away (g₁ * s)) ay
                * algebraMap S (Localization.Away (g₁ * s)) (g₁ ^ ix) := by rw [hTy]
      rw [IsLocalization.eq_iff_exists (Submonoid.powers (g₁ * s))
        (Localization.Away (g₁ * s))] at hTeq
      obtain ⟨⟨c, l, hcl⟩, hc⟩ := hTeq
      simp only at hcl hc
      subst hcl
      have hcS₁ := congrArg (algebraMap S (Localization.Away g₁)) hc
      rw [map_mul, map_mul, map_mul, map_mul] at hcS₁
      rw [← hxe, ← hye] at hcS₁
      refine ⟨⟨algebraMap S (Localization.Away g₁) s ^ l, l, rfl⟩, ?_⟩
      simp only
      have hUunit : IsUnit (algebraMap S (Localization.Away g₁) (g₁ ^ l)
          * algebraMap S (Localization.Away g₁) (g₁ ^ ix)
          * algebraMap S (Localization.Away g₁) (g₁ ^ iy)) := by
        simp only [map_pow]
        exact ((hg₁unitS₁.pow l).mul (hg₁unitS₁.pow ix)).mul (hg₁unitS₁.pow iy)
      apply hUunit.mul_left_cancel
      simp only [map_pow, map_mul, mul_pow] at hcS₁ ⊢
      linear_combination hcS₁
  -- Step 5: assemble the `B`-algebra structure on `T` and the three conjuncts.
  let algBT : Algebra (MvPolynomial (Fin n) R) (Localization.Away (g₁ * s)) :=
    ((algebraMap (Localization.Away g₁) (Localization.Away (g₁ * s))).comp
      (algebraMap (MvPolynomial (Fin n) R) (Localization.Away g₁))).toAlgebra
  have towerBST : IsScalarTower (MvPolynomial (Fin n) R) (Localization.Away g₁)
      (Localization.Away (g₁ * s)) := IsScalarTower.of_algebraMap_eq fun x => rfl
  have towerRBT : IsScalarTower R (MvPolynomial (Fin n) R) (Localization.Away (g₁ * s)) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      change algebraMap R (Localization.Away (g₁ * s)) x
          = algebraMap (Localization.Away g₁) (Localization.Away (g₁ * s))
            (algebraMap (MvPolynomial (Fin n) R) (Localization.Away g₁)
              (algebraMap R (MvPolynomial (Fin n) R) x))
      rw [← IsScalarTower.algebraMap_apply R (MvPolynomial (Fin n) R) (Localization.Away g₁) x]
      rw [IsScalarTower.algebraMap_apply R S (Localization.Away g₁) x, hatower]
      rw [← IsScalarTower.algebraMap_apply R S (Localization.Away (g₁ * s)) x]
  -- `Algebra.FiniteType R T`
  have hftST : Algebra.FiniteType S (Localization.Away (g₁ * s)) := instFiniteTypeAway (g₁ * s)
  have hftRT : Algebra.FiniteType R (Localization.Away (g₁ * s)) :=
    Algebra.FiniteType.trans inferInstance hftST
  -- The `B`-algebra equiv `Away r ≃ₐ[B] T` for the QuasiFinite transport.
  have hAwayR :
      IsLocalization.Away (algebraMap S (Localization.Away g₁) s) (Localization.Away r) :=
    IsLocalization.Away.of_associated hassoc
  let e0 : Localization.Away r ≃ₐ[Localization.Away g₁] Localization.Away (g₁ * s) :=
    IsLocalization.algEquiv (Submonoid.powers (algebraMap S (Localization.Away g₁) s))
      (Localization.Away r) (Localization.Away (g₁ * s))
  let e : Localization.Away r ≃ₐ[MvPolynomial (Fin n) R] Localization.Away (g₁ * s) :=
    e0.restrictScalars (MvPolynomial (Fin n) R)
  -- Provide `φ` and prove the three conjuncts.
  refine ⟨algebraMap (MvPolynomial (Fin n) R) (Localization.Away (g₁ * s)), ?_, ?_, ?_⟩
  · -- commutation
    rw [← IsScalarTower.algebraMap_eq R (MvPolynomial (Fin n) R) (Localization.Away (g₁ * s))]
  · -- FiniteType
    change Algebra.FiniteType (MvPolynomial (Fin n) R) (Localization.Away (g₁ * s))
    exact Algebra.FiniteType.of_restrictScalars_finiteType R (MvPolynomial (Fin n) R)
      (Localization.Away (g₁ * s))
  · -- QuasiFinite
    change Algebra.QuasiFinite (MvPolynomial (Fin n) R) (Localization.Away (g₁ * s))
    exact (Algebra.QuasiFinite.iff_of_algEquiv e).mp hqf

-- needed: the `change`/`simp` steps of `quasiFinite_over_polynomial_of_relativeDimension`
-- are type-correct only with `Localization.Away`/`MvPolynomial` unfolded past the default
-- transparency
set_option backward.isDefEq.respectTransparency false in
/-- Stacks tag 00QE (Lemma 10.125.2). Let `R → S` be a finite type ring map, `q ⊂ S` a prime
lying over `p = q ∩ R`, with corresponding point `qbar` of the fibre spectrum
`Spec(S ⊗_R κ(p))`. If the relative dimension `dim_q(S/R)` equals `n : ℕ`, then there is
`g ∈ S`, `g ∉ q`, and an `R`-algebra ring map `φ : R[t_1, …, t_n] → S_g` such that
`S_g = S[1/g]` is finite type and quasi-finite over `R[t_1, …, t_n]` via `φ`. -/
@[stacks 00QE]
theorem quasiFinite_over_polynomial_of_relativeDimension
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (q : PrimeSpectrum S)
    (p : Ideal R) [hp : p.IsPrime]
    (qbar : PrimeSpectrum (p.Fiber S))
    (hqbar : PrimeSpectrum.comap (fiberMap R S p) qbar = q)
    (n : ℕ)
    (hdim : relativeDimensionAt R S p qbar = (n : ℕ∞)) :
    ∃ (g : S), g ∉ q.asIdeal ∧
      ∃ (φ : MvPolynomial (Fin n) R →+* Localization.Away g),
        φ.comp (algebraMap R (MvPolynomial (Fin n) R)) = algebraMap R (Localization.Away g) ∧
        φ.FiniteType ∧ φ.QuasiFinite := by
  -- Write `S̄ = p.Fiber S = S ⊗_R κ(p)` and let `q̄ = qbar` be the point of `Spec S̄`
  -- corresponding to `q`. The argument is: (A) localize on `S` so that the *whole* fibre
  -- spectrum has Krull
  -- dimension `n`; (B) Noether-normalize the fibre over `κ(p)` to get `n` elements of `S`
  -- giving a finite map `κ(p)[t₁,…,tₙ] → S̄`; (C) build `φ` and check it is finite type;
  -- (D) deduce quasi-finiteness at `q`, then shrink (further localize) so that
  -- quasi-finiteness holds at *every* prime. The two localizations are combined into a
  -- single `g`. Each step is isolated as a `have` below.
  --
  -- ════════════════════════════════════════════════════════════════════════════════
  -- Step A — Extract an open neighborhood of `q̄` of dimension `n`, then a basic open.
  -- ════════════════════════════════════════════════════════════════════════════════
  -- `relativeDimensionAt = krullDimAt qbar = ⨅ U∋q̄ topologicalKrullDim U = n`. The infimum
  -- over open neighborhoods is *attained* — and this needs NO spectral/Noetherian input,
  -- it is purely order-theoretic: `WithBot ℕ∞` is well-founded for `<`
  -- (`WellFoundedLT (WithBot ℕ∞)` by `inferInstance`), and an infimum over a NONEMPTY family
  -- in a conditionally-complete well-founded order equals one of the family's values (the
  -- `<`-minimal element of the range, via `WellFounded.has_min`). The neighborhood index
  -- type `{U // IsOpen U ∧ qbar ∈ U}` is nonempty (`U = Set.univ`). Concretely,
  --   `lemma (ι) [Nonempty ι] (f : ι → WithBot ℕ∞) : ∃ i, (⨅ j, f j) = f i`
  -- (proved by `WellFounded.has_min (wellFounded_lt) (Set.range f) (Set.range_nonempty f)`
  -- then `le_antisymm (iInf_le ..) (le_iInf ..)`) applied to
  -- `f := fun U => topologicalKrullDim U.1` gives `U₀` with `topologicalKrullDim U₀ = n`
  -- (rewriting via `hdim`/`relativeDimensionAt`/`krullDimAt`).
  have hU : ∃ U : Set (PrimeSpectrum (p.Fiber S)), IsOpen U ∧ qbar ∈ U ∧
      topologicalKrullDim U = (n : ℕ∞) := by
    have : Nonempty {U : Set (PrimeSpectrum (p.Fiber S)) // IsOpen U ∧ qbar ∈ U} :=
      ⟨⟨Set.univ, isOpen_univ, Set.mem_univ _⟩⟩
    obtain ⟨U₀, hU₀⟩ := exists_iInf_eq_of_nonempty
      (ι := {U : Set (PrimeSpectrum (p.Fiber S)) // IsOpen U ∧ qbar ∈ U})
      (fun U => topologicalKrullDim U.val)
    refine ⟨U₀.val, U₀.property.left, U₀.property.right, ?_⟩
    have hk : krullDimAt qbar = topologicalKrullDim U₀.val := hU₀
    have := hdim
    rw [relativeDimensionAt, hk] at this
    exact this
  -- Refine `U` to a *basic* open `D(s)` of `Spec S̄` containing `q̄` with `D(s) ⊆ U`
  -- (basic opens form a basis of the Zariski topology), and then lift `s ∈ S̄` to an
  -- element `g₁ ∈ S` with `g₁ ∉ q` whose image is (a unit multiple of) `s`, using that
  -- `fiberMap R S p : S → S̄` and `D(s)` pulls back to a neighborhood; `g₁ ∉ q` because
  -- `q̄ ∈ D(s)` and `PrimeSpectrum.comap (fiberMap R S p) qbar = q` (`hqbar`). Stacks 00E6
  -- (topology of the fibre induced from `Spec S`) is the conceptual input; concretely use
  -- `PrimeSpectrum.basicOpen` and `PrimeSpectrum.comap`.
  -- Then on `S_{g₁}` the fibre `(S_{g₁}) ⊗_R κ(p)` is `S̄_{ḡ₁}`, whose spectrum is `D(ḡ₁)`,
  -- of dimension `n`. We package "the fibre of `S_{g₁}` has dimension `n` everywhere" as:
  have hg1 : ∃ (g₁ : S), g₁ ∉ q.asIdeal ∧
      topologicalKrullDim (PrimeSpectrum (p.Fiber (Localization.Away g₁))) = (n : ℕ∞) := by
    obtain ⟨U, hUopen, hqU, hUdim⟩ := hU
    -- Lemma A: refine `U` to a basic open `D(φ g₁)` of an image element, still ⊆ U, ∋ qbar.
    obtain ⟨g₁, hqD, hDU⟩ := exists_image_basicOpen_subset R S p qbar U hUopen hqU
    refine ⟨g₁, ?_, ?_⟩
    · -- `g₁ ∉ q`: `qbar ∈ D(φ g₁)` ⟹ `φ g₁ ∉ qbar`; and `g₁ ∈ q ↔ φ g₁ ∈ qbar` via `hqbar`.
      have hφ : fiberMap R S p g₁ ∉ qbar.asIdeal := by
        simpa [PrimeSpectrum.basicOpen, PrimeSpectrum.mem_basicOpen] using hqD
      -- `q = comap (fiberMap R S p) qbar`, so `g₁ ∈ q ↔ fiberMap g₁ ∈ qbar`.
      intro hg1q
      rw [← hqbar] at hg1q
      exact hφ hg1q
    · -- Dimension squeeze.
      -- The spectrum of the fibre of `S_{g₁}` is homeomorphic to `D(φ g₁)`, so their
      -- topologicalKrullDims agree (Obligation C via fiberLocAway_spec_homeo_basicOpen).
      obtain ⟨homeo⟩ := fiberLocAway_spec_homeo_basicOpen R S p g₁
      have hdimEq : topologicalKrullDim (PrimeSpectrum (p.Fiber (Localization.Away g₁)))
          = topologicalKrullDim
            (PrimeSpectrum.basicOpen (fiberMap R S p g₁) : Set (PrimeSpectrum (p.Fiber S))) :=
        topologicalKrullDim_eq_of_homeo homeo
      rw [hdimEq]
      -- Upper bound: `D(φ g₁) ⊆ U`, `dim U = n` ⟹ `dim D(φ g₁) ≤ n`.
      have hle : topologicalKrullDim
          (PrimeSpectrum.basicOpen (fiberMap R S p g₁) : Set (PrimeSpectrum (p.Fiber S)))
          ≤ (n : ℕ∞) := by
        have := topologicalKrullDim_le_of_subset hDU
        rwa [hUdim] at this
      -- Lower bound: `D(φ g₁)` is an open neighborhood of `qbar`, so
      -- `krullDimAt qbar ≤ dim D(φ g₁)`; and `krullDimAt qbar = n` (from `hdim`).
      have hkd : krullDimAt qbar = (n : ℕ∞) := by
        have := hdim; rwa [relativeDimensionAt] at this
      have hge : (n : ℕ∞) ≤ topologicalKrullDim
          (PrimeSpectrum.basicOpen (fiberMap R S p g₁) : Set (PrimeSpectrum (p.Fiber S))) := by
        rw [← hkd, krullDimAt]
        exact iInf_le (fun U : {U : Set (PrimeSpectrum (p.Fiber S)) // IsOpen U ∧ qbar ∈ U} =>
            topologicalKrullDim U.val)
          ⟨(PrimeSpectrum.basicOpen (fiberMap R S p g₁) : Set (PrimeSpectrum (p.Fiber S))),
            (PrimeSpectrum.basicOpen (fiberMap R S p g₁)).isOpen, hqD⟩
      exact le_antisymm hle hge
  -- ════════════════════════════════════════════════════════════════════════════════
  -- Step B — Noether normalization of the fibre over the residue field κ(p).
  -- ════════════════════════════════════════════════════════════════════════════════
  -- Done in `normLift_aeval_finite`, applied to `S_{g₁}` from Step A (via
  -- `exists_normalization_lift`).
  -- ════════════════════════════════════════════════════════════════════════════════
  -- Step C/D/E — assemble `φ`, finite type, quasi-finite, and combine localizations.
  -- ════════════════════════════════════════════════════════════════════════════════
  -- We now produce the witness `g`, the map `φ`, and the three conjuncts. The element `y`
  -- of Step B gives `φ = MvPolynomial.aeval` of `t_i ↦ (image of y_i in S_g)`. The
  -- commutation conjunct is `MvPolynomial.aeval`-naturality (`aeval_C`/`comp_algebraMap`).
  -- `φ.FiniteType`: `S` (hence every localization `S_g`) is finite type over `R`, and the
  -- composite `R → R[t] → S_g` is finite type, so by base/cancellation
  -- (`RingHom.FiniteType.comp`, 00F4, plus finite-type of `R[t]`-algebra structure) `φ` is
  -- finite type. `φ.QuasiFinite`: from Step B the fibre over `q` is module-finite, giving
  -- `QuasiFiniteAt … q` (`forall_quasiFiniteAt_iff_forall_finite_fiber` 00PM / 00PN); the
  -- quasi-finite locus is open (Stacks 00QA / Zariski's main property 00Q9
  -- `Algebra.zariskisMainProperty_iff_exists_saturation_eq_top`), so a further localization
  -- by some `g₂ ∉ q` makes it quasi-finite at *every* prime. Combine `g₁, g₂` into one `g`
  -- via `IsLocalization.localization_localization_isLocalization` (02C6). This whole
  -- assembly is decomposed into the four lemmas above:
  -- `exists_normalization_lift` (Steps B+D bridge), `weaklyQuasiFiniteAt_of_finite_fiber`
  -- (Step D descent), `exists_quasiFinite_localization_of_wqf` (Step D/E openness, PROVED),
  -- and `exists_g_phi` (Step E localization combine + φ). The gluing:
  obtain ⟨g₁, hg1q, hg1dim⟩ := hg1
  obtain ⟨instB, htower, hft, q₁, hq₁prime, hq₁eq, hfin⟩ :=
    exists_normalization_lift R S q p qbar hqbar n g₁ hg1q hg1dim
  let := instB
  have := htower
  have := hft
  have := hq₁prime
  have : Algebra.WeaklyQuasiFiniteAt (MvPolynomial (Fin n) R) q₁ :=
    weaklyQuasiFiniteAt_of_finite_fiber (MvPolynomial (Fin n) R) (Localization.Away g₁) q₁ hfin
  obtain ⟨r, hr, hqf⟩ :=
    exists_quasiFinite_localization_of_wqf (MvPolynomial (Fin n) R) (Localization.Away g₁) q₁
  rw [hq₁eq] at hr
  exact exists_g_phi R S q n g₁ hg1q instB htower r hr hqf

end

end
