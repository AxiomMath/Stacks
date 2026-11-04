module

public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.RingTheory.Unramified.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Henselian.Pair
public import StacksFrontier.RingTheory.Henselian.Pair.Criteria
public import StacksFrontier.RingTheory.Henselian.Pair.Nilpotent
public import StacksFrontier.RingTheory.Smooth.Lifting

@[expose] public section

/-!
# The henselian-pair form of the nilpotent case

For a locally nilpotent ideal `I ⊆ A`, every coprime monic factorization modulo `I` of a monic
polynomial over `A` lifts to `A`, so `(A, I)` is a henselian pair in the sense of Stacks 09XE,
and reduction modulo `I` is fully faithful on étale algebras in the form that lifts and compares
`A`-algebra maps.

## Main results

* `henselianPair_of_le_nilradical`: `(A, I)` is a `HenselianPair` whenever `I ≤ nilradical A`.
* `bijective_mkₐ_comp_of_etale_of_le_nilradical`: for an étale `A`-algebra `B` and any
  `A`-algebra `C`, composing with `C → C ⧸ IC` is a bijection on `A`-algebra maps out of `B`.
* `etaleBaseChange_isEquivalence_and_henselianPair_of_le_nilradical`: the conclusion of Stacks
  0ALI with henselianness read as the monic-factorization condition of Stacks 09XE.

## Implementation notes

`I ≤ nilradical A` is Stacks' "`I` is locally nilpotent" (Stacks 00IL): every element of `I` is
nilpotent. The factorization condition is obtained from the characterization of henselian pairs
by lifting of `A`-algebra maps out of étale algebras (Stacks 09XI) together with smooth lifting
along a locally nilpotent ideal (Stacks 07K4).

## References

* [Stacks: Tag 0ALI](https://stacks.math.columbia.edu/tag/0ALI)
* [Stacks: Tag 09XE](https://stacks.math.columbia.edu/tag/09XE)
* [Stacks: Tag 09XI](https://stacks.math.columbia.edu/tag/09XI)
-/

universe u

section

/-- Two `A`-algebra maps out of a finitely presented formally unramified algebra agreeing
modulo a locally nilpotent ideal are equal. -/
private lemma algHom_ext_of_le_nilradical
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra.FinitePresentation R S]
    [Algebra.FormallyUnramified R S]
    (J : Ideal T) (hJ : J ≤ nilradical T) (f g : S →ₐ[R] T)
    (h : (Ideal.Quotient.mkₐ R J).comp f = (Ideal.Quotient.mkₐ R J).comp g) : f = g := by
  obtain ⟨n, π, hπ, -⟩ := Algebra.FinitePresentation.out (R := R) (A := S)
  let d : Fin n → T := fun i => f (π (MvPolynomial.X i)) - g (π (MvPolynomial.X i))
  let K : Ideal T := Ideal.span (Set.range d)
  have hKJ : K ≤ J := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact Ideal.Quotient.eq.mp (DFunLike.congr_fun h (π (MvPolynomial.X i)))
  have hKnil : IsNilpotent K := isNilpotent_of_fg
    (fun x hx => mem_nilradical.mp (hJ hx)) hKJ
    (Submodule.fg_span (Set.finite_range d))
  refine Algebra.FormallyUnramified.lift_unique K hKnil f g
    ((AlgHom.cancel_right hπ).mp (MvPolynomial.algHom_ext fun i => ?_))
  exact Ideal.Quotient.eq.mpr (Ideal.subset_span ⟨i, rfl⟩)

/-- **Stacks 0ALI**, the monic-factorization half. If every element of `I` is nilpotent then
`(A, I)` is a henselian pair: `I` lies in the Jacobson radical of `A` and every factorization
modulo `I` of a monic polynomial into coprime monic factors lifts to `A`. -/
theorem henselianPair_of_le_nilradical {A : Type u} [CommRing A] (I : Ideal A)
    (hI : I ≤ nilradical A) : HenselianPair A I := by
  refine ((henselianPair_tfae.{u, u} A I).out 2 1).mp ?_
  intro A' _ _ _ σ
  exact main_theorem07K4 A A' A I (fun x hx => mem_nilradical.mp (hI hx)) σ

/-- **Stacks 0ALI**, the fully faithful half in ring-theoretic form. For an étale `A`-algebra `B`
and a locally nilpotent ideal `I ⊆ A`, reduction modulo `IC` is a bijection from `A`-algebra maps
`B → C` to `A`-algebra maps `B → C ⧸ IC`, for every `A`-algebra `C`. -/
theorem bijective_mkₐ_comp_of_etale_of_le_nilradical
    {A : Type u} [CommRing A] (I : Ideal A) (hI : I ≤ nilradical A)
    (B : Type*) (C : Type*) [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    [Algebra.Etale A B] :
    Function.Bijective fun f : B →ₐ[A] C =>
      (Ideal.Quotient.mkₐ A (I.map (algebraMap A C))).comp f := by
  have hJ : Ideal.IsLocallyNilpotent (I.map (algebraMap A C)) :=
    Ideal.IsLocallyNilpotent0544.map (algebraMap A C) I fun x hx => mem_nilradical.mp (hI hx)
  exact ⟨fun f g h => algHom_ext_of_le_nilradical _ (fun x hx => mem_nilradical.mpr (hJ x hx))
    f g h, fun g => main_theorem07K4 A B C _ hJ g⟩

/-- **Stacks 0ALI.** If every element of `I` is nilpotent, reduction modulo `I` induces an
equivalence from étale `A`-algebras to étale `(A ⧸ I)`-algebras, and `(A, I)` is a henselian pair
in the sense that coprime monic factorizations modulo `I` lift to `A`. -/
@[stacks 0ALI "henselianness in the monic-factorization sense of Definition 09XE"]
theorem etaleBaseChange_isEquivalence_and_henselianPair_of_le_nilradical
    {A : Type u} [CommRing A] (I : Ideal A) (hI : I ≤ nilradical A) :
    (etaleBaseChange I).IsEquivalence ∧ HenselianPair A I :=
  ⟨(etaleBaseChange_isEquivalence_and_henselianRing_of_le_nilradical I hI).1,
    henselianPair_of_le_nilradical I hI⟩

end

end
