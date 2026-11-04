module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorRegularRight
public import StacksFrontier.Algebra.DifferentialGraded.Module.CohomologyActionTensor
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedEquivalenceRegularImage
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorBaseChangeSecondVariable
public import StacksFrontier.Algebra.DifferentialGraded.Module.EndomorphismDGAToAlgebra

/-! # A derived equivalence of differential graded algebras comes from a bimodule

Let `R` be a ring, let `(A, d)` and `(B, d)` be differential graded `R`-algebras and let
`F : D(A, d) → D(B, d)` be an `R`-linear equivalence of triangulated categories. Assume

1. `A = H^0(A)`, and
2. `B` is K-flat as a complex of `R`-modules.

[Stacks, Tag 09SA] says that there is then a differential graded `(A, B)`-bimodule `N` as in
[Stacks, Tag 09S7] — that is, satisfying that lemma's three hypotheses, so that
`- ⊗_A^𝐋 N : D(A, d) ⥤ D(B, d)` is an equivalence.

The construction is the source's. Replace `F(A)` by a differential graded module `Q` with
property (P) and set `E = End(Q)`, its endomorphism differential graded algebra (Tag 09LE). Then
`Q` is a differential graded `(E, B)`-bimodule, tautologically
(`DifferentialGraded.Bimodule.endomorphism`), and Tag 09S7 applies to it: its class in `D(B, d)`
is compact and weakly generating because `F(A)` is, and the endomorphism comparison is bijective
by `DifferentialGraded.Bimodule.bijective_cohomologyEndomorphismComparison_endomorphism`. Let `E'`
be the degree-`≤ 0` truncation of `E`. There are quasi-isomorphisms
`(A, d) ← (E', d) → (E, d)`, so by Tag 09S6 three of the four functors in
$$D(A, \text{d}) \longleftarrow D(E', \text{d}) \longrightarrow D(E, \text{d})
\longrightarrow D(B, \text{d})$$
are equivalences and the fourth, the quasi-inverse of the first, is derived restriction of
scalars along `E' → A`, which is the derived tensor product with the regular bimodule
(Tag 0BYX). The composite of the three derived tensor products is therefore the derived tensor
product with a single `(A, B)`-bimodule, by Tag 09S4 — and that is where K-flatness of `B` is
spent, and the only place.

## Main results

* `DifferentialGraded.Bimodule.exists_bimodule_of_quasiIso_pair`: the construction, with the two
  quasi-isomorphisms out of `E'` and the `(E, B)`-bimodule as hypotheses.
* `DifferentialGraded.Bimodule.exists_bimodule_of_derivedEquivalence`: **Stacks 09SA.**

## Implementation notes

*How the three hypotheses of Tag 09S7 are verified for the composite bimodule `N`.* Not one of
them is checked by hand on `N`, whose underlying module is a relative tensor product of
property-(P) replacements and is not a computable object. Instead the isomorphism of functors
`- ⊗_A^𝐋 N ≅ (- ⊗_A^𝐋 A_{E'}) ⋙ (- ⊗_{E'}^𝐋 E) ⋙ (- ⊗_E^𝐋 Q)` supplied by Tag 09S4 exhibits
`- ⊗_A^𝐋 N` as an equivalence, and each hypothesis is read off that:

* the class of `N` is `(- ⊗_A^𝐋 N)(A)` up to the unit isomorphism
  (`DifferentialGraded.Bimodule.derivedTensorIsoOfLeftOrthogonal` at the regular module), and an
  additive equivalence carries the compact object `A` to a compact object;
* the same isomorphism and
  `CategoryTheory.Pretriangulated.isWeakTriangulatedGenerator_obj_of_equivalence` carry the weak
  generation of `D(A, d)` by `A` to weak generation of `D(B, d)` by the class of `N`;
* hypothesis (3) *is* the bijectivity of `- ⊗_A^𝐋 N` on `Hom_{D(A,d)}(A, A[k])`, by
  `DifferentialGraded.Bimodule.bijective_cohomologyEndomorphismComparison_iff_shift`, so it
  follows from full faithfulness.

*What the conclusion records beyond the source.* Besides the three hypotheses of Tag 09S7 the
conclusion also states that `- ⊗_A^𝐋 N` is an equivalence — free, since that is how the
hypotheses were obtained — and that the class of `N` in `D(B, d)` is isomorphic to `F(A)`, which
is the input the remark [Stacks, Tag 09SB] takes.

*Where the two hypotheses of the source are used.* Hypothesis (1), `A = H^0(A)`, is used twice:
it makes `Hom_{D(B,d)}(Q, Q[k])` vanish for `k ≠ 0`
(`DifferentialGradedModule.eq_zero_of_hom_obj_q_regularModule_shift`), and it identifies `A` with
the endomorphism algebra of the regular module in `D(A, d)`
(`DifferentialGradedModule.regularEndAlgEquiv`); both feed
`DifferentialGradedModule.exists_hom_nonpositiveEndomorphismDGA_to_concentrated`. Hypothesis (2),
K-flatness of `B`, is used only in the two applications of
`DifferentialGraded.Bimodule.derivedTensorFunctorCompIsoOfKFlatAlgebra` (Tag 09S4) that compose
the three derived tensor functors into one.

*Universes.* As throughout this chapter, the base ring, the algebras and the modules live in a
single universe `u`, following Tag 09JJ; compactness is taken with respect to coproducts indexed
by `Type u`, matching Tags 09R9 and 09S7.

*What is not asserted about `F`.* The source's hypothesis is an `R`-linear equivalence of
triangulated categories. What is assumed below is additivity, `R`-linearity and commutation with
the translation; `Functor.IsTriangulated` is not used. Nothing is asserted about the relation
between `F` and `- ⊗_A^𝐋 N` beyond the isomorphism `N ≅ F(A)`; that they are isomorphic as
functors is not known, as [Stacks, Tag 09SB] itself observes.

## References

* [Stacks Project, Tag 09SA](https://stacks.math.columbia.edu/tag/09SA), the result proved here.
* [Stacks Project, Tag 09S7](https://stacks.math.columbia.edu/tag/09S7) for the criterion the
  bimodule satisfies, [Tag 09S6](https://stacks.math.columbia.edu/tag/09S6) for the equivalence
  attached to a quasi-isomorphism, [Tag 09S4](https://stacks.math.columbia.edu/tag/09S4) and
  [Tag 0BZ5](https://stacks.math.columbia.edu/tag/0BZ5) for the composition of derived tensor
  functors, [Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX) for restriction of scalars as a
  derived tensor product, [Tag 09S9](https://stacks.math.columbia.edu/tag/09S9) for the
  discussion the proof follows, and [Tag 09KP](https://stacks.math.columbia.edu/tag/09KP) for
  property-(P) resolutions.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

namespace DifferentialGraded.Bimodule

open DifferentialGradedAlgebra DifferentialGradedModule CategoryTheory.ObjectProperty

variable {R : Type u} [CommRing R]

/-- The derived tensor product with `N` sends the class of the regular module to the class of
`N`. -/
private def derivedTensorObjRegularIso {A B : DifferentialGradedAlgebra.{u, u} R}
    (N : Bimodule A B) :
    (derivedTensorFunctor N).obj
      ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)) ≅
      (toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj N.rightModule :=
  derivedTensorIsoOfLeftOrthogonal N (regularModule A)
    (leftOrthogonal_acyclic_toHomotopyCategory_regularModule A) (tensorRegularIso N).1

/-- **Stacks 09SA, with the two quasi-isomorphisms and the `(E, B)`-bimodule as hypotheses.** Let
`(A, d)`, `(B, d)`, `(E', d)` and `(E, d)` be differential graded `R`-algebras with `B` K-flat as
a complex of `R`-modules, let `θ : E' → A` and `ψ : E' → E` be homomorphisms of differential
graded algebras inducing isomorphisms on cohomology, and let `NE` be a differential graded
`(E, B)`-bimodule satisfying the three hypotheses of [Stacks, Tag 09S7]. Then there is a
differential graded `(A, B)`-bimodule `N` satisfying those three hypotheses, with
`- ⊗_A^𝐋 N : D(A, d) ⥤ D(B, d)` an equivalence and with the class of `N` in `D(B, d)` isomorphic
to that of `NE`.

The bimodule is the twofold composite `N = A_{E'} ⊗_{E'} E ⊗_E NE` of
`DifferentialGraded.Bimodule.compTensorResolution`, whose derived tensor functor is the composite
of the three by Tag 09S4; the first factor is the regular `(A, E')`-bimodule of `θ`, whose derived
tensor functor is derived restriction of scalars along `θ` (Tag 0BYX) and so the quasi-inverse of
the equivalence of Tag 09S6. The three hypotheses for `N` are read off the resulting equivalence
as described in the implementation notes of this file. -/
theorem exists_bimodule_of_quasiIso_pair (A B E' E : DifferentialGradedAlgebra.{u, u} R)
    (hB : CochainComplex.KFlat.{u, u} (regularModule B).toCochainComplex)
    (θ : E'.Hom A) (hθ : ∀ k : ℤ, Function.Bijective (θ.cohomologyMap k))
    (ψ : E'.Hom E) (hψ : ∀ k : ℤ, Function.Bijective (ψ.cohomologyMap k))
    (NE : Bimodule E B)
    [IsCompactObject.{u} ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj NE.rightModule)]
    (h2 : ∀ X : derivedCategory' B,
      (∀ (n : ℤ) (f : (toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj NE.rightModule ⟶
        X⟦n⟧), f = 0) → IsZero X)
    (h3 : ∀ k : ℤ, Function.Bijective (NE.cohomologyEndomorphismComparison k)) :
    ∃ N : Bimodule A B,
      IsCompactObject.{u}
          ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj N.rightModule) ∧
        (∀ X : derivedCategory' B,
            (∀ (n : ℤ) (f : (toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj N.rightModule ⟶
              X⟦n⟧), f = 0) → IsZero X) ∧
          (∀ k : ℤ, Function.Bijective (N.cohomologyEndomorphismComparison k)) ∧
            (derivedTensorFunctor N).IsEquivalence ∧
              Nonempty ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj N.rightModule ≅
                (toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj NE.rightModule) := by
  let EQ := derivedTensorEquivalence NE h2 h3
  let Eps := derivedExtensionEquivalence ψ hψ
  let Eth := derivedExtensionEquivalence θ hθ
  let M := compTensorResolution (Bimodule.regular ψ) NE
  let N := compTensorResolution (regularRight θ) M
  let iso1 := derivedTensorFunctorCompIsoOfKFlatAlgebra E' E B hB (Bimodule.regular ψ) NE
  let iso2 := derivedTensorFunctorCompIsoOfKFlatAlgebra A E' B hB (regularRight θ) M
  have ciso : derivedTensorFunctor N ≅ (Eth.symm.trans (Eps.trans EQ)).functor :=
    iso2.symm ≪≫ (Functor.isoWhiskerLeft (derivedTensorFunctor (regularRight θ)) iso1).symm ≪≫
      Functor.isoWhiskerRight (derivedTensorRegularRightIso θ) (Eps.functor ⋙ EQ.functor)
  have : (derivedTensorFunctor N).IsEquivalence := Functor.isEquivalence_of_iso ciso.symm
  let uN := derivedTensorObjRegularIso N
  refine ⟨N, ?_, ?_, ?_, inferInstance, ?_⟩
  · exact isCompactObject_of_iso uN.symm ((isCompactObject_iff_isCompactObject_obj
      (derivedTensorFunctor N) _).1 (isCompactObject_q_regularModule A))
  · have hcs : (derivedTensorFunctor N).asEquivalence.functor.CommShift ℤ :=
      inferInstanceAs ((derivedTensorFunctor N).CommShift ℤ)
    have hpz : (derivedTensorFunctor N).asEquivalence.functor.PreservesZeroMorphisms :=
      inferInstanceAs ((derivedTensorFunctor N).PreservesZeroMorphisms)
    exact (isWeakTriangulatedGenerator_singleton_iff_forall_hom_eq_zero _).1
      (isWeakTriangulatedGenerator_singleton_of_iso uN
        (isWeakTriangulatedGenerator_obj_of_equivalence
          (derivedTensorFunctor N).asEquivalence _
          (isWeakTriangulatedGenerator_q_regularModule A)))
  · exact fun k => (bijective_cohomologyEndomorphismComparison_iff_shift N k).2
      ⟨(derivedTensorFunctor N).map_injective, (derivedTensorFunctor N).map_surjective⟩
  · let rth : Eth.functor.obj ((toHomotopyCategory E' ⋙ (quasiIsomorphisms' E').Q).obj
        (regularModule E')) ≅
        (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A) :=
      derivedTensorObjRegularIso (Bimodule.regular θ)
    let rps : Eps.functor.obj ((toHomotopyCategory E' ⋙ (quasiIsomorphisms' E').Q).obj
        (regularModule E')) ≅
        (toHomotopyCategory E ⋙ (quasiIsomorphisms' E).Q).obj (regularModule E) :=
      derivedTensorObjRegularIso (Bimodule.regular ψ)
    let rQ : EQ.functor.obj ((toHomotopyCategory E ⋙ (quasiIsomorphisms' E).Q).obj
        (regularModule E)) ≅
        (toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj NE.rightModule :=
      derivedTensorObjRegularIso NE
    let rthinv : Eth.inverse.obj
        ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)) ≅
        (toHomotopyCategory E' ⋙ (quasiIsomorphisms' E').Q).obj (regularModule E') :=
      Eth.inverse.mapIso rth.symm ≪≫ (Eth.unitIso.app _).symm
    exact ⟨uN.symm ≪≫ ciso.app _ ≪≫
      (Eps.functor ⋙ EQ.functor).mapIso rthinv ≪≫ EQ.functor.mapIso rps ≪≫ rQ⟩

/-- **Stacks 09SA.** Let `R` be a commutative ring, let `(A, d)` and `(B, d)` be differential
graded `R`-algebras and let `F : D(A, d) ≌ D(B, d)` be an additive, `R`-linear,
shift-commuting equivalence. Assume

1. `A = H^0(A)`, i.e. every homogeneous component of `A` outside degree zero vanishes, and
2. `B` is K-flat as a complex of `R`-modules.

Then there is a differential graded `(A, B)`-bimodule `N` as in [Stacks, Tag 09S7]: the class of
`N` in `D(B, d)` is a compact object, it weakly generates `D(B, d)`, and the canonical map
`H^k(A) → Hom_{D(B,d)}(N, N[k])` of
`DifferentialGraded.Bimodule.cohomologyEndomorphismComparison` is bijective for every `k`.
Consequently `- ⊗_A^𝐋 N : D(A, d) ⥤ D(B, d)` is an equivalence, and the class of `N` is `F(A)`.

Hypothesis (1) enters through
`DifferentialGradedModule.exists_hom_nonpositiveEndomorphismDGA_to_concentrated`, which needs the
vanishing of `Hom_{D(B,d)}(Q, Q[k])` for `k ≠ 0` and the identification of `A` with the
endomorphism algebra of the class of `Q`; hypothesis (2) enters only through Tag 09S4
(`DifferentialGraded.Bimodule.derivedTensorFunctorCompIsoOfKFlatAlgebra`), which composes the
three derived tensor functors of the proof into one. -/
@[stacks 09SA "the (A, B)-bimodule N as in Lemma 09S7, together with the equivalence it defines \
and the identification of its class in D(B, d) with F(A); the equivalence F is taken to be \
additive, R-linear and shift-commuting, Functor.IsTriangulated not being used"]
theorem exists_bimodule_of_derivedEquivalence (A B : DifferentialGradedAlgebra.{u, u} R)
    (hA : ∀ i : ℤ, i ≠ 0 → A.grading i = ⊥)
    (hB : CochainComplex.KFlat.{u, u} (regularModule B).toCochainComplex)
    (F : derivedCategory' A ≌ derivedCategory' B) [F.functor.Additive]
    [F.functor.Linear R] [F.functor.CommShift ℤ] :
    ∃ N : Bimodule A B,
      IsCompactObject.{u}
          ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj N.rightModule) ∧
        (∀ X : derivedCategory' B,
            (∀ (n : ℤ) (f : (toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj N.rightModule ⟶
              X⟦n⟧), f = 0) → IsZero X) ∧
          (∀ k : ℤ, Function.Bijective (N.cohomologyEndomorphismComparison k)) ∧
            (derivedTensorFunctor N).IsEquivalence ∧
              Nonempty ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj N.rightModule ≅
                F.functor.obj ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj
                  (regularModule A))) := by
  obtain ⟨Q, hQ, ⟨eQ⟩⟩ := exists_propertyPFiltration_model B
    (F.functor.obj ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)))
  have hcQ : IsCompactObject.{u} ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj Q) :=
    isCompactObject_of_iso eQ ((isCompactObject_iff_isCompactObject_obj F.functor _).1
      (isCompactObject_q_regularModule A))
  have hwQ := isWeakTriangulatedGenerator_singleton_of_iso eQ.symm
    (isWeakTriangulatedGenerator_obj_of_equivalence F _
      (isWeakTriangulatedGenerator_q_regularModule A))
  have hvanish : ∀ k : ℤ, k ≠ 0 →
      ∀ f : (toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj Q ⟶
        (toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj (Q.shift k), f = 0 :=
    fun k hk f => (Iso.homCongr eQ (shiftCompare Q k ≪≫
        (shiftFunctor (derivedCategory' B) k).mapIso eQ)).injective
      ((eq_zero_of_hom_obj_q_regularModule_shift A B F.functor hA hk _).trans
        (eq_zero_of_hom_obj_q_regularModule_shift A B F.functor hA hk _).symm)
  have ealg : A.A ≃ₐ[R] End ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj Q) :=
    ((regularEndAlgEquiv A hA).trans
      (F.fullyFaithfulFunctor.algEquivEndOfFullyFaithful (R := R) _)).trans
        (Iso.endAlgEquiv (R := R) eQ.symm)
  obtain ⟨θ, hθ⟩ := exists_hom_nonpositiveEndomorphismDGA_to_concentrated A B hA Q hQ hvanish ealg
  obtain ⟨ψ, hψ⟩ := exists_hom_nonpositiveEndomorphismDGA_bijective_cohomologyMap B Q hQ
    (fun k hk => hvanish k (ne_of_gt hk))
  have : IsCompactObject.{u} ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj
      (endomorphism B Q).rightModule) := hcQ
  obtain ⟨N, h1, h2, h3, h4, ⟨eN⟩⟩ := exists_bimodule_of_quasiIso_pair A B _ _ hB θ hθ ψ hψ
    (endomorphism B Q)
    ((isWeakTriangulatedGenerator_singleton_iff_forall_hom_eq_zero _).1 hwQ)
    (bijective_cohomologyEndomorphismComparison_endomorphism B Q hQ)
  exact ⟨N, h1, h2, h3, h4, ⟨eN.trans eQ⟩⟩

end DifferentialGraded.Bimodule

end
