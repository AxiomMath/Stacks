module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.ZeroDivisorsNilpotent
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.SchemeTheoreticallyDense
public import StacksFrontier.RingTheory.TensorProduct.ZeroDimLocalZeroDivisors

/-!
# Zero divisors of the local rings of a group scheme, and schematic density

Let `k` be a field of characteristic zero and `G` a group scheme over `k`.  Every zero divisor
of every local ring `𝒪_{G,x}` is nilpotent (Perrin, thèse, II 1.2), and consequently an open
subscheme of `G` containing every maximal point of `G` is scheme-theoretically dense (Perrin,
I 1.9–1.10).

## Main results

* `AlgebraicGeometry.zeroDivisorsNilpotent_stalk_of_charZero`: the local statement for group
  schemes, unconditionally in characteristic zero.
* `ZeroDivisorsNilpotent.eq_zero_of_forall_minimalPrimes`: in a ring whose
  local rings have nilpotent zero divisors, an element killed by a power of some element outside
  every minimal prime vanishes.
* `AlgebraicGeometry.isSchemeTheoreticallyDominant_ι_of_zeroDivisorsNilpotent`,
  `AlgebraicGeometry.Scheme.Opens.isSchemeTheoreticallyDense_of_zeroDivisorsNilpotent`: on a
  scheme whose local rings have nilpotent zero divisors, an open containing every maximal point
  is scheme-theoretically dense; and
  `AlgebraicGeometry.Scheme.Opens.isSchemeTheoreticallyDense_of_charZero` for group schemes in
  characteristic zero.
* `AlgebraicGeometry.Scheme.Opens.isSchemeTheoreticallyDense_of_irreducibleSpace`: on such an
  irreducible scheme, every nonempty open is scheme-theoretically dense.

## Implementation notes

Perrin's I 1.9 says that a topologically dense open of a scheme `X` satisfying `P(X)` is
schematically dense, where `P(X)` asks every ring of an affine open to have nilpotent zero
divisors; such a ring is irreducible (Perrin I 1.4), so `P(X)` forces `X` to be locally
irreducible on every affine open, and in particular a dense open contains the generic point of
every affine open.  The condition on the local rings alone, which is what holds for every group
scheme (`AlgebraicGeometry.zeroDivisorsNilpotent_stalk_of_charZero`; a group scheme need not be
irreducible), does not make a merely dense open contain every maximal point when the irreducible
components do not form a locally finite family.  The density statement is therefore stated with
the hypothesis that the open contains every maximal point, i.e. every point without proper
generization; on an irreducible scheme this is nonemptiness.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Zero divisors in the local rings of a group scheme over a field of characteristic zero are
nilpotent** (Perrin, II 1.2).  This is `AlgebraicGeometry.zeroDivisorsNilpotent_stalk` with its
input supplied by `TensorProduct.isNilpotent_of_not_mem_nonZeroDivisors_localization`. -/
theorem zeroDivisorsNilpotent_stalk_of_charZero (k : Type u) [Field k] [CharZero k]
    (G : Grp (Over (Spec (CommRingCat.of k)))) (x : G.X.left) :
    ZeroDivisorsNilpotent (G.X.left.presheaf.stalk x) :=
  zeroDivisorsNilpotent_stalk k (fun K L _ _ _ _ _ _ _ _ P _ r hr =>
    TensorProduct.isNilpotent_of_not_mem_nonZeroDivisors_localization k K L P r hr) G x

/-! ### The ring-theoretic statement -/

/-- **An element killed by powers of elements avoiding every minimal prime vanishes**, in a ring
all of whose local rings have nilpotent zero divisors.  If `a ≠ 0`, it survives in some local
ring `A_𝔭`; below `𝔭` lies a minimal prime `𝔮`, and an element `g ∉ 𝔮` with `g ^ n a = 0` is a
zero divisor of `A_𝔭`, hence nilpotent there, hence in `𝔮`. -/
theorem _root_.ZeroDivisorsNilpotent.eq_zero_of_forall_minimalPrimes {A : Type*} [CommRing A]
    (hA : ∀ (p : Ideal A) [p.IsPrime], ZeroDivisorsNilpotent (Localization.AtPrime p)) (a : A)
    (h : ∀ q ∈ minimalPrimes A, ∃ g ∉ q, ∃ n : ℕ, g ^ n * a = 0) : a = 0 := by
  by_contra ha
  obtain ⟨p, hp, hpa⟩ : ∃ (p : Ideal A) (_ : p.IsMaximal),
      algebraMap A (Localization.AtPrime p) a ≠ 0 := by
    by_contra hne
    push Not at hne
    exact ha (eq_zero_of_localization a fun p hp => hne p hp)
  obtain ⟨q, hqp, hq⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ p)
  have hqmin : q ∈ minimalPrimes A := by
    rw [minimalPrimes, Ideal.minimalPrimes] at *
    assumption
  obtain ⟨g, hg, n, hgn⟩ := h q hqmin
  have hqprime : q.IsPrime := hqmin.1.1
  have hzd : algebraMap A (Localization.AtPrime p) (g ^ n) ∉
      nonZeroDivisors (Localization.AtPrime p) := by
    rw [mem_nonZeroDivisors_iff_right]
    push Not
    exact ⟨algebraMap A _ a, by rw [mul_comm, ← map_mul, hgn, map_zero], hpa⟩
  obtain ⟨m, hm⟩ := hA p _ hzd
  rw [← map_pow] at hm
  obtain ⟨⟨t, ht⟩, htg⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl _ _).1 hm
  have hmem : t * (g ^ n) ^ m ∈ q := by rw [htg]; exact q.zero_mem
  rcases hqprime.mem_or_mem hmem with h1 | h1
  · exact ht (hq h1)
  · exact hg (hqprime.mem_of_pow_mem _ (by rw [← pow_mul] at h1; exact h1))

/-- `ZeroDivisorsNilpotent` transports along a ring isomorphism. -/
theorem _root_.ZeroDivisorsNilpotent.of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S)
    (hS : ZeroDivisorsNilpotent S) : ZeroDivisorsNilpotent R :=
  ZeroDivisorsNilpotent.of_injective e.toRingHom e.injective hS

/-! ### Schematic density -/

/-- **On a scheme whose local rings have nilpotent zero divisors, an open containing every
maximal point is scheme-theoretically dominant**: restriction of sections to it is injective on
every affine open. -/
theorem isSchemeTheoreticallyDominant_ι_of_zeroDivisorsNilpotent {Y : Scheme.{u}}
    (hY : ∀ y : Y, ZeroDivisorsNilpotent (Y.presheaf.stalk y)) (U : Y.Opens)
    (hU : ∀ η : Y, (∀ y : Y, y ⤳ η → y = η) → η ∈ U) :
    IsSchemeTheoreticallyDominant U.ι := by
  refine ⟨le_bot_iff.1 fun W => ?_⟩
  refine (U.ι.ideal_ker_le W).trans ?_
  rw [Scheme.IdealSheafData.ideal_bot, Pi.bot_apply, le_bot_iff, ← RingHom.injective_iff_ker_eq_bot,
    injective_iff_map_eq_zero]
  intro s hs
  have hW : IsAffineOpen (W : Y.Opens) := W.2
  refine ZeroDivisorsNilpotent.eq_zero_of_forall_minimalPrimes (A := Γ(Y, (W : Y.Opens)))
    (fun p _ => ?_) s ?_
  · let y := hW.fromSpec ⟨p, inferInstance⟩
    have hy : y ∈ (W : Y.Opens) := hW.range_fromSpec.subset ⟨_, rfl⟩
    let := TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨y, hy⟩
    have : IsLocalization.AtPrime (Y.presheaf.stalk y) p :=
      hW.isLocalization_stalk' ⟨p, inferInstance⟩ hy
    exact ZeroDivisorsNilpotent.of_ringEquiv
      (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p)
        (Y.presheaf.stalk y)).toRingEquiv (hY y)
  · intro q hq
    have hqp : q.IsPrime := hq.1.1
    let η := hW.fromSpec ⟨q, hqp⟩
    have hηW : η ∈ (W : Y.Opens) := hW.range_fromSpec.subset ⟨_, rfl⟩
    have hηmax : ∀ y : Y, y ⤳ η → y = η := by
      intro y hyη
      have hyW : y ∈ (W : Y.Opens) := hyη.mem_open W.1.isOpen hηW
      set y' := hW.primeIdealOf ⟨y, hyW⟩
      have hy' : hW.fromSpec y' = y := hW.fromSpec_primeIdealOf ⟨y, hyW⟩
      rw [← hy'] at hyη ⊢
      have hsp : y' ⤳ ⟨q, hqp⟩ :=
        (hW.fromSpec.isOpenEmbedding.toIsInducing.specializes_iff).1 hyη
      have hle : y'.asIdeal ≤ q := (PrimeSpectrum.le_iff_specializes _ _).2 hsp
      have hge : q ≤ y'.asIdeal := hq.2 ⟨y'.isPrime, bot_le⟩ hle
      have : y' = ⟨q, hqp⟩ := PrimeSpectrum.ext (le_antisymm hle hge)
      rw [this]
    have hηU : η ∈ U := hU η hηmax
    obtain ⟨g, hgle, hgη⟩ := hW.exists_basicOpen_le (V := U ⊓ (W : Y.Opens))
      ⟨η, ⟨hηU, hηW⟩⟩ hηW
    have hgq : g ∉ q := by
      have h : (⟨q, hqp⟩ : PrimeSpectrum _) ∈ hW.fromSpec ⁻¹ᵁ Y.basicOpen g := hgη
      rw [hW.fromSpec_preimage_basicOpen] at h
      exact h
    refine ⟨g, hgq, ?_⟩
    have hsub : Y.basicOpen g ≤ U.ι ''ᵁ U.ι ⁻¹ᵁ (W : Y.Opens) := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact hgle
    have hres : Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op s = 0 := by
      have h2 : Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op =
          Y.presheaf.map (homOfLE (x := U.ι ''ᵁ U.ι ⁻¹ᵁ (W : Y.Opens))
            (Set.image_preimage_subset _ _)).op ≫ Y.presheaf.map (homOfLE hsub).op := by
        rw [← Functor.map_comp]; rfl
      rw [h2, CommRingCat.comp_apply]
      rw [Scheme.Opens.ι_app] at hs
      exact (congrArg (Y.presheaf.map (homOfLE hsub).op) hs).trans (map_zero _)
    have := hW.isLocalization_basicOpen g
    have h0 : algebraMap Γ(Y, (W : Y.Opens)) Γ(Y, Y.basicOpen g) s = 0 := hres
    obtain ⟨⟨m, ⟨n, rfl⟩⟩, hm⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers g) Γ(Y, Y.basicOpen g) s).1 h0
    exact ⟨n, hm⟩

/-- **On a scheme whose local rings have nilpotent zero divisors, an open containing every
maximal point is scheme-theoretically dense** (Perrin, I 1.9, in the form valid without
irreducibility): for every open `V`, the trace of `U` on `V` contains every maximal point of `V`,
and the local rings of `V` are those of `X`. -/
theorem Scheme.Opens.isSchemeTheoreticallyDense_of_zeroDivisorsNilpotent {X : Scheme.{u}}
    (hX : ∀ x : X, ZeroDivisorsNilpotent (X.presheaf.stalk x)) (U : X.Opens)
    (hU : ∀ η : X, (∀ y : X, y ⤳ η → y = η) → η ∈ U) :
    U.IsSchemeTheoreticallyDense := by
  intro V
  refine isSchemeTheoreticallyDominant_ι_of_zeroDivisorsNilpotent (fun y => ?_) _ (fun η hη => ?_)
  · exact ZeroDivisorsNilpotent.of_ringEquiv
      (asIso (V.ι.stalkMap y)).symm.commRingCatIsoToRingEquiv (hX (V.ι y))
  · refine hU (V.ι η) fun y hy => ?_
    have hyV : y ∈ V := hy.mem_open V.isOpen η.2
    have hy' : (⟨y, hyV⟩ : V.toScheme) ⤳ η :=
      (V.ι.isOpenEmbedding.toIsInducing.specializes_iff).1 hy
    have := hη _ hy'
    exact congrArg Subtype.val this

/-- **On an irreducible scheme whose local rings have nilpotent zero divisors, every nonempty
open is scheme-theoretically dense** (Perrin, I 1.9): the only maximal point is the generic
point, which lies in every nonempty open. -/
theorem Scheme.Opens.isSchemeTheoreticallyDense_of_irreducibleSpace {X : Scheme.{u}}
    [IrreducibleSpace X] (hX : ∀ x : X, ZeroDivisorsNilpotent (X.presheaf.stalk x))
    (U : X.Opens) (hU : (U : Set X).Nonempty) : U.IsSchemeTheoreticallyDense := by
  refine isSchemeTheoreticallyDense_of_zeroDivisorsNilpotent hX U fun η hη => ?_
  have hgen : genericPoint X = η := hη _ ((genericPoint_spec X).specializes (Set.mem_univ η))
  rw [← hgen]
  exact (genericPoint_spec X).mem_open_set_iff U.isOpen |>.2 (by simpa using hU)

/-- **On a group scheme over a field of characteristic zero, an open containing every maximal
point is scheme-theoretically dense** (Perrin, II 2.9 in characteristic zero). -/
theorem Scheme.Opens.isSchemeTheoreticallyDense_of_charZero (k : Type u) [Field k] [CharZero k]
    (G : Grp (Over (Spec (CommRingCat.of k)))) (U : G.X.left.Opens)
    (hU : ∀ η : G.X.left, (∀ y : G.X.left, y ⤳ η → y = η) → η ∈ U) :
    U.IsSchemeTheoreticallyDense :=
  isSchemeTheoreticallyDense_of_zeroDivisorsNilpotent
    (zeroDivisorsNilpotent_stalk_of_charZero k G) U hU

end AlgebraicGeometry

end
