module

public import StacksFrontier.RingTheory.Rig.Algebraization.RigSmoothAlgebraizationCases
public import StacksFrontier.RingTheory.Rig.Algebraization.RigSmoothAlgebraizationPrincipal
public import StacksFrontier.RingTheory.Rig.Algebraization.RigSmoothAlgebraizationTower
public import StacksFrontier.RingTheory.Rig.Algebraization.RigSmoothQuotientsLimit
public import StacksFrontier.RingTheory.Rig.Algebraization.SquareZeroLiftSmooth

/-!
# Gabber–Zavyalov: algebraization of rig-smooth algebras (Stacks 0GAX)

Let `I` be an ideal of a Noetherian ring `A` and let `B` be an object of the category of Stacks
0AL4 which is rig-smooth over `(A, I)`. Remark 0GAX of the Stacks Project records that `B` is
isomorphic to the `I`-adic completion of a finite type `A`-algebra, by Gabber–Zavyalov
[Theorem 1.2], and that this supersedes three partial results: the case of a G-ring `A`
(Proposition 0GAT), the case of a rig-étale `B` (Lemma 0AKA) and the case of a principal ideal
`I` (Elkik [III, Theorem 7]).

## The proof of the main claim

By induction on the number of generators of `I = (s ∪ {a})`, following Gabber–Zavyalov, in the
form in which the library proves Lemma 0AKA (`RigSmoothAlgebraizationTower.lean`): the quotients
`B ⧸ aᵐ B` are algebraized over `A ⧸ (aᵐ)` by the induction hypothesis, with algebraizations
smooth away from `V(I)` (Stacks 0GAK (2)); the levels are made compatible one at a time by the
smooth square-zero lifting lemma `Rig.exists_squareZeroLift_of_smoothAwayFrom` (Gabber–Zavyalov's
deformation lemma, proved through the exactness of the formal glueing complex at its fourth
term); the limit `B'` of the system is rig-smooth over `(A, (a))`
(`Rig.isRigSmooth_of_isBijectiveMod_of_smoothAwayFrom_quotients`, Gabber–Zavyalov's
"smoothify"), so the principal case algebraizes it, and the `I`-adic completion of that
algebraization is `B`.

## Main results

* `Rig.exists_finiteType_algEquiv_adicCompletion_of_isRigSmooth`: Gabber–Zavyalov [Theorem 1.2].
* `Rig.isRigSmooth_algebraization`: **Stacks 0GAX**, the theorem together with the three partial
  results the remark lists.

## References

* [Stacks Project, Tag 0GAX](https://stacks.math.columbia.edu/tag/0GAX)
* O. Gabber, B. Zavyalov, *Algebraization techniques and rigid-analytic Artin–Grothendieck
  vanishing*, arXiv:2402.08741, Theorem 1.2 (= Theorem "Noetherian rig-smooth algebraization").
* R. Elkik, *Solutions d'équations à coefficients dans un anneau hensélien*, Ann. Sci. ENS 1973,
  III Théorème 7.
-/

@[expose] public section

namespace Rig

universe u v

/-- The principal case in the form used by the induction: an ideal which is principal and an
object whose carrier lies in the universe of `A`. -/
theorem exists_finiteType_algEquiv_of_isRigSmooth_of_isPrincipal
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A} (hI : I.IsPrincipal)
    (B : AdicFiniteTypeAlgebra.{u, u} A I) (hB : IsRigSmooth B) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C), Algebra.FiniteType A C ∧
      Nonempty (B.carrier ≃ₐ[A] AdicCompletion (I.map (algebraMap A C)) C) := by
  obtain ⟨a, rfl⟩ := hI.principal
  exact exists_finiteType_adicCompletion_algEquiv_of_isRigSmooth_principal B hB

/-- **Gabber–Zavyalov [Theorem 1.2].** Let `I` be an ideal of a Noetherian ring `A` and let `B`
be an object of the category of Stacks 0AL4 which is rig-smooth over `(A, I)`. Then there is a
finite type `A`-algebra `C` and an isomorphism `B ≅ C^∧` of `A`-algebras with the `I`-adic
completion of `C`.

The carrier of `B` is replaced by the quotient `A⟨x₁, …, x_r⟩/J` of a presentation of `B`, which
lies in the universe of `A` (`Rig.isRigSmooth_of_algEquiv` transports rig-smoothness), and `I` is
written as the span of a finite set; the induction
`Rig.exists_finiteType_algEquiv_of_isRigSmooth_span` then applies, with its three inputs
discharged by `Rig.exists_squareZeroLift_of_smoothAwayFrom`,
`Rig.isRigSmooth_of_isBijectiveMod_of_smoothAwayFrom_quotients` and the principal case. -/
public theorem exists_finiteType_algEquiv_adicCompletion_of_isRigSmooth
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    (B : AdicFiniteTypeAlgebra.{u, v} A I) (hB : IsRigSmooth B) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C),
      Algebra.FiniteType A C ∧
        Nonempty (B.carrier ≃ₐ[A] AdicCompletion (I.map (algebraMap A C)) C) := by
  obtain ⟨P⟩ := nonempty_completedPolynomialPresentation (Ideal.fg_of_isNoetherianRing I) B
  have he : (PerturbedPresentation.quotientObj A I P.variableCount P.ideal).carrier ≃ₐ[A]
      B.carrier := P.quotientEquiv
  obtain ⟨s, rfl⟩ := Ideal.fg_of_isNoetherianRing I
  obtain ⟨C, _, _, hCft, ⟨E⟩⟩ := exists_finiteType_algEquiv_of_isRigSmooth_span
    @exists_squareZeroLift_of_smoothAwayFrom
    @isRigSmooth_of_isBijectiveMod_of_smoothAwayFrom_quotients
    @exists_finiteType_algEquiv_of_isRigSmooth_of_isPrincipal
    s.card s le_rfl (PerturbedPresentation.quotientObj A _ P.variableCount P.ideal)
    (isRigSmooth_of_algEquiv he hB)
  exact ⟨C, inferInstance, inferInstance, hCft, ⟨he.symm.trans E⟩⟩

/-- **Stacks 0GAX.** Let `I` be an ideal of a Noetherian ring `A` and let `B` be an object of the
category of Stacks 0AL4 which is rig-smooth over `(A, I)`. Then `B` is isomorphic to the `I`-adic
completion of a finite type `A`-algebra (Gabber–Zavyalov [Theorem 1.2]). This supersedes the
partial results:

1. if `A` is a G-ring, the result follows from Proposition 0GAT;
2. if `B` is rig-étale over `(A, I)`, the result follows from Lemma 0AKA;
3. if `I` is principal, the result follows from Elkik [III, Theorem 7].

The four conjuncts are, in order, the theorem
(`Rig.exists_finiteType_algEquiv_adicCompletion_of_isRigSmooth`) and the three partial results,
each proved by the route the remark names: Proposition 0GAT and Lemma 0AKA through
`Rig.exists_finiteType_adicCompletion_algEquiv_of_isRigSmooth_of_isGRing_or_isRigEtale`, and
Elkik's theorem through `Rig.exists_finiteType_adicCompletion_algEquiv_of_isRigSmooth_principal`.
In the theorem the finite type algebra lies in the universe of `A`; the partial results produce it
in the universe `max u v`, as the lemmas they follow from do. -/
@[stacks 0GAX]
public theorem isRigSmooth_algebraization :
    (∀ {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
        (B : AdicFiniteTypeAlgebra.{u, v} A I), IsRigSmooth B →
        ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C), Algebra.FiniteType A C ∧
          Nonempty (B.carrier ≃ₐ[A] AdicCompletion (I.map (algebraMap A C)) C)) ∧
    (∀ {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
        (B : AdicFiniteTypeAlgebra.{u, v} A I), IsRigSmooth B → IsGRing A →
        ∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra A C), Algebra.FiniteType A C ∧
          Nonempty (B.carrier ≃ₐ[A] AdicCompletion (I.map (algebraMap A C)) C)) ∧
    (∀ {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
        (B : AdicFiniteTypeAlgebra.{u, v} A I), IsRigSmooth B → IsRigEtale B →
        ∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra A C), Algebra.FiniteType A C ∧
          Nonempty (B.carrier ≃ₐ[A] AdicCompletion (I.map (algebraMap A C)) C)) ∧
    (∀ {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
        (B : AdicFiniteTypeAlgebra.{u, v} A I), IsRigSmooth B → I.IsPrincipal →
        ∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra A C), Algebra.FiniteType A C ∧
          Nonempty (B.carrier ≃ₐ[A] AdicCompletion (I.map (algebraMap A C)) C)) := by
  refine ⟨fun B hB ↦ exists_finiteType_algEquiv_adicCompletion_of_isRigSmooth B hB,
    fun B hB hA ↦ ?_, fun B hB hEt ↦ ?_, fun {A} _ _ {I} B hB hI ↦ ?_⟩
  · exact exists_finiteType_adicCompletion_algEquiv_of_isRigSmooth_of_isGRing_or_isRigEtale B hB
      (Or.inl hA)
  · exact exists_finiteType_adicCompletion_algEquiv_of_isRigSmooth_of_isGRing_or_isRigEtale B hB
      (Or.inr hEt)
  · obtain ⟨a, rfl⟩ := hI.principal
    exact exists_finiteType_adicCompletion_algEquiv_of_isRigSmooth_principal B hB

end Rig

end
