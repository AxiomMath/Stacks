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
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Nilpotent.Ideal

/-!
# Lifting along locally nilpotent ideals

A smooth ring map `R → S` lifts along a *locally* nilpotent ideal, not merely a nilpotent one.

Formal smoothness is Mathlib's `Algebra.FormallySmooth`; its square-zero lifting property is
`Algebra.FormallySmooth.iff_comp_surjective` and `Algebra.FormallySmooth.comp_surjective`.

## Main results

* `isNilpotent_of_fg`: a finitely generated ideal contained in a locally nilpotent ideal is
  nilpotent.
* `exists_lift_through_fg_subideal`: an `R`-algebra map from a finitely presented `R`-algebra to
  `A ⧸ I` factors through `A ⧸ J` for a finitely generated ideal `J ≤ I`.
* `main_theorem07K4`: a smooth `R`-algebra has the lifting property with respect to locally
  nilpotent ideals.
-/

@[expose] public section
set_option linter.unusedVariables false


/-- A finitely generated ideal `J` contained in a locally nilpotent ideal `I`
is itself nilpotent. -/
lemma isNilpotent_of_fg
    {A : Type*} [CommRing A] {I J : Ideal A}
    (hI : Ideal.IsLocallyNilpotent I) (hJI : J ≤ I) (hJ : J.FG) :
    IsNilpotent J := by
  have hJrad : J ≤ (⊥ : Ideal A).radical := fun x hx =>
    (hI x (hJI hx)).imp fun n hn => by simpa using hn
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hJrad hJ
  exact ⟨n, le_bot_iff.mp hn⟩

/-- **Lifting through an fg sub-ideal.** Given a finitely presented `R`-algebra `S`,
a commutative `R`-algebra `A`, an ideal `I` of `A`, and an `R`-algebra map
`g : S →ₐ[R] A ⧸ I`, there exist a finitely generated ideal `J ⊆ I` of `A` and
an `R`-algebra map `g' : S →ₐ[R] A ⧸ J` whose composition with the natural map
`A ⧸ J →ₐ[R] A ⧸ I` is `g`. -/
lemma exists_lift_through_fg_subideal
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S]
    {A : Type*} [CommRing A] [Algebra R A] (I : Ideal A)
    (g : S →ₐ[R] A ⧸ I) :
    ∃ (J : Ideal A) (hJI : J ≤ I) (g' : S →ₐ[R] A ⧸ J),
      J.FG ∧
        (Ideal.quotientMapₐ I (AlgHom.id R A) hJI).comp g' = g := by
  obtain ⟨n, π, hπ_surj, hπ_ker_fg⟩ :=
    Algebra.FinitePresentation.out (R := R) (A := S)
  set q : A →ₐ[R] A ⧸ I := Ideal.Quotient.mkₐ R I
  have hq_surj : Function.Surjective q := Ideal.Quotient.mkₐ_surjective R I
  let a : Fin n → A := fun i => (hq_surj (g (π (MvPolynomial.X i)))).choose
  have ha : ∀ i, q (a i) = g (π (MvPolynomial.X i)) := fun i =>
    (hq_surj (g (π (MvPolynomial.X i)))).choose_spec
  let ψ : MvPolynomial (Fin n) R →ₐ[R] A := MvPolynomial.aeval a
  have hqψ : q.comp ψ = g.comp π := by
    ext i
    simp [ψ, ha i]
  refine ⟨Ideal.map ψ.toRingHom (RingHom.ker π.toRingHom), ?_, ?_⟩
  · rw [Ideal.map_le_iff_le_comap]
    intro p hp
    have hqψp : q (ψ p) = g (π p) := DFunLike.congr_fun hqψ p
    exact (Ideal.Quotient.eq_zero_iff_mem (I := I)).mp
      (show q (ψ p) = 0 by rw [hqψp, show π p = 0 from hp, map_zero])
  set J : Ideal A := Ideal.map ψ.toRingHom (RingHom.ker π.toRingHom)
  set qJ : A →ₐ[R] A ⧸ J := Ideal.Quotient.mkₐ R J
  have h_killker : RingHom.ker π.toRingHom ≤ RingHom.ker (qJ.comp ψ).toRingHom :=
    fun p hp => Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem ψ.toRingHom hp)
  let φ : (MvPolynomial (Fin n) R) ⧸ RingHom.ker π.toRingHom →ₐ[R] A ⧸ J :=
    Ideal.Quotient.liftₐ (RingHom.ker π.toRingHom) (qJ.comp ψ) h_killker
  let e : S ≃ₐ[R] (MvPolynomial (Fin n) R) ⧸ RingHom.ker π.toRingHom :=
    (Ideal.quotientKerAlgEquivOfSurjective hπ_surj).symm
  refine ⟨φ.comp e.toAlgHom, hπ_ker_fg.map ψ.toRingHom, ?_⟩
  refine (AlgHom.cancel_right hπ_surj).mp (AlgHom.ext fun p => ?_)
  have h1 : e (π p) = Ideal.Quotient.mkₐ R (RingHom.ker π.toRingHom) p :=
    Ideal.quotientKerAlgEquivOfSurjective_symm_apply hπ_surj p
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, h1]
  exact DFunLike.congr_fun hqψ p

/-- **Smooth strong lifting**: a smooth ring map `R → S` has the lifting
property with respect to locally nilpotent ideals. For any commutative
`R`-algebra `A` with a locally nilpotent ideal `I`, every `R`-algebra map
`S → A ⧸ I` lifts to an `R`-algebra map `S → A`. -/
@[stacks 07K4,
  ega "0 19.0.1" "special case",
  ega "0 19.3.10.1" "special case",
  ega "0 19.5.6.4" "special case",
  ega "IV 17.14.2" "partial",
  sga "1 III 5.2" "special case",
  sga "3 III 0.17" "special case",
  sga "3 III 2.3" "(a), special case",
  sga "3 III 2.5" "(a), special case",
  sga "3 IX 3.3" "special case",
  sga "3 XI 1.5" "partial"]
theorem main_theorem07K4
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] [Algebra.Smooth R S]
    (A : Type*) [CommRing A] [Algebra R A] (I : Ideal A)
    (hI : Ideal.IsLocallyNilpotent I)
    (g : S →ₐ[R] A ⧸ I) :
    ∃ f : S →ₐ[R] A, (Ideal.Quotient.mkₐ R I).comp f = g := by
  obtain ⟨J, hJI, g', hJfg, hcomm⟩ := exists_lift_through_fg_subideal I g
  obtain ⟨f, hf⟩ := Algebra.FormallySmooth.exists_lift J (isNilpotent_of_fg hI hJI hJfg) g'
  exact ⟨f, by rw [← hcomm, ← hf]; rfl⟩

end

add_to_sga "3 XI 1.6" "affine case, smooth" Algebra.FormallySmooth
