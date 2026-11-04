module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.DegreeZeroRickard
public import StacksFrontier.Algebra.DifferentialGraded.Module.DegreeZeroRickardBimodule
public import StacksFrontier.Algebra.DifferentialGraded.Module.DegreeZeroTriangulated
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedEquivalenceCompactGeneratorConverse

/-! # Rickard's criterion for ordinary algebras: the converse implications

Let `R` be a commutative ring and let `A` and `B` be `R`-algebras, not assumed commutative.
[Stacks, Tag 09SC] asserts the equivalence of

1. the existence of an `R`-linear triangulated equivalence `D(A) → D(B)`;
2. the existence of an object `P` of `D(B)` which is perfect, which detects vanishing, and whose
   graded endomorphism algebra is `A` in degree zero and vanishes elsewhere;

together with a third condition, equivalent to these when `B` is flat over `R`:

3. the existence of an `(A, B)`-bimodule `N` for which `- ⊗_A^𝐋 N : D(A) → D(B)` is an
   equivalence.

The implications `(1) ⇒ (2)` and `(1) ⇒ (3)` are
`DifferentialGradedModule.exists_isPerfect_and_detectsZero_of_derivedEquivalence` and
`DifferentialGradedModule.exists_bimodule_derivedTensorEquivalence_of_derivedEquivalence`. This
file proves the two converses, `(2) ⇒ (1)` and `(3) ⇒ (1)`, and packages the resulting
equivalences `(1) ↔ (2)` and `(1) ↔ (3)`.

## Main results

* `DifferentialGradedModule.exists_derivedEquivalence_of_isPerfect_and_detectsZero`:
  **Stacks 09SC, the implication (2) ⇒ (1).**
* `DifferentialGradedModule.derivedEquivalence_iff_exists_isPerfect_and_detectsZero`:
  **Stacks 09SC, the equivalence (1) ↔ (2).**
* `DifferentialGradedModule.exists_derivedEquivalence_of_bimodule`:
  **Stacks 09SC, the implication (3) ⇒ (1).**
* `DifferentialGradedModule.derivedEquivalence_iff_exists_bimodule`:
  **Stacks 09SC, the equivalence (1) ↔ (3)**, for `B` flat over `R`.

## Implementation notes

*What unblocked the converses.* Both converses need the degree-zero comparison
`DifferentialGradedModule.degreeZeroDerivedEquivalence` to be *exact*, not merely
shift-commuting: the equivalence that [Stacks, Tag 09S8] produces lives between the differential
graded derived categories and has to be conjugated into the ordinary ones, and clause (1) asks
for a triangulated equivalence. That exactness is
`DifferentialGradedModule.degreeZeroDerivedEquivalence_functor_exact`. The implementation notes
of `StacksFrontier/Algebra/DifferentialGraded/Module/DegreeZeroRickard.lean` and
`StacksFrontier/Algebra/DifferentialGraded/Module/DegreeZeroRickardBimodule.lean`, which record it as the one thing missing, predate it.

*Why the commutation with the shift is existentially bound.* The exactness of the degree-zero
comparison holds for the commutation with the shift that the localization of the homotopy category
induces on it, which is not known to be the global instance
`DifferentialGradedModule.degreeZeroDerivedEquivalence_functor_commShift` built from the
differential graded localization. Clause (1) is therefore spelled, here as in
`DifferentialGraded.Bimodule.derivedEquivalence_iff_exists_isCompactObject_and_isWeakGenerator`
(Tag 09S8), as an equivalence that is additive, `R`-linear and, *for some* commutation with the
shift, triangulated. An existential clause (1) composes with Tag 09S8's existential clause (1),
which is what the proofs below do.

*Which derived category `D(A)` is, and universes.* Exactly as in
`StacksFrontier/Algebra/DifferentialGraded/Module/DegreeZeroRickard.lean`: a differential graded
module is a *right* module throughout Chapter 22, so `D(A)` is `DerivedCategory (ModuleCat Aᵐᵒᵖ)`,
reached through the genuine instance `DifferentialGradedAlgebra.instIsOppositeAlgebraOp`, which
identifies `A` with the opposite of `Aᵐᵒᵖ` and therefore uses `A` itself as the degree-zero
differential graded algebra; the base ring, the algebras and the modules live in a single universe
`u`, and the ordinary derived categories are the standard models,
`HasDerivedCategory.standard`. Clause (2)(a) is `StacksDraft.Perfect.IsPerfect`, vanishing of an
`Ext` group is `Subsingleton` of the corresponding shifted `Hom` group, and the degree-zero clause
of (2)(c) is an isomorphism of `R`-algebras `A ≃ₐ[R] End P` — the same spellings as the forward
direction, so that the two compose into the stated equivalences.

*Clause (3).* The hypothesis of `(3) ⇒ (1)` is that the differential graded derived tensor
functor of `N` is an equivalence, which is the first of the two conclusions of `(1) ⇒ (3)` and the
conclusion of [Stacks, Tag 09SA]; the conjugate functor `D(Mod-A) ⥤ D(Mod-B)` that the source's
`- ⊗_A^𝐋 N` names is then an equivalence automatically, the two comparisons being equivalences.
`(3) ⇒ (1)` needs no flatness hypothesis; the equivalence `(1) ↔ (3)` does, because `(1) ⇒ (3)`
does. The reading of "`(A, B)`-bimodule" is the differential graded one, for the reasons set out
in `StacksFrontier/Algebra/DifferentialGraded/Module/DegreeZeroRickardBimodule.lean`.

## References

* [Stacks Project, Tag 09SC](https://stacks.math.columbia.edu/tag/09SC), the lemma whose
  converses are proved here.
* [Stacks Project, Tag 09S8](https://stacks.math.columbia.edu/tag/09S8), Rickard's criterion for
  differential graded algebras, whose converse is conjugated here, and
  [Tag 07LT](https://stacks.math.columbia.edu/tag/07LT), the identification of perfect with
  compact objects.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ModuleCat.Algebra

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

namespace DifferentialGradedModule

open DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] {A : Type u} [Ring A] [Algebra R A]
  {B : Type u} [Ring B] [Algebra R B]

/-- An additive, `R`-linear, triangulated equivalence of the degree-zero differential graded
derived categories, conjugated by the degree-zero comparisons, gives clause (1) of Tag 09SC. -/
private theorem exists_derivedEquivalence_of_degreeZero
    (F : derivedCategory' (degreeZero R A) ⥤ derivedCategory' (degreeZero R B))
    [F.IsEquivalence] [F.Additive] [F.Linear R] [F.CommShift ℤ] [F.IsTriangulated] :
    ∃ E : DerivedCategory (ModuleCat.{u} Aᵐᵒᵖ) ≌ DerivedCategory (ModuleCat.{u} Bᵐᵒᵖ),
      E.functor.Additive ∧ E.functor.Linear R ∧
        ∃ hs : E.functor.CommShift ℤ, letI := hs; E.functor.IsTriangulated := by
  obtain ⟨hsA, htriA⟩ :=
    degreeZeroDerivedEquivalence_functor_exact (R := R) (S := A) (A := Aᵐᵒᵖ)
  obtain ⟨hsB, htriB⟩ :=
    degreeZeroDerivedEquivalence_functor_exact (R := R) (S := B) (A := Bᵐᵒᵖ)
  let EA := degreeZeroDerivedEquivalence (R := R) (S := A) (A := Aᵐᵒᵖ)
  let EB := degreeZeroDerivedEquivalence (R := R) (S := B) (A := Bᵐᵒᵖ)
  let : EA.functor.CommShift ℤ := hsA
  let : EB.functor.CommShift ℤ := hsB
  have htriA' : EA.functor.IsTriangulated := htriA
  have htriB' : EB.functor.IsTriangulated := htriB
  let : EA.inverse.CommShift ℤ := EA.commShiftInverse ℤ
  let : EB.inverse.CommShift ℤ := EB.commShiftInverse ℤ
  have := EA.commShift_of_functor ℤ
  have : EA.IsTriangulated := Equivalence.IsTriangulated.mk' EA htriA'
  let hcomp : (EA.symm.trans (F.asEquivalence.trans EB)).functor.CommShift ℤ :=
    inferInstanceAs ((EA.inverse ⋙ F ⋙ EB.functor).CommShift ℤ)
  refine ⟨EA.symm.trans (F.asEquivalence.trans EB), ?_, ?_, hcomp, ?_⟩
  · show (EA.inverse ⋙ F ⋙ EB.functor).Additive
    infer_instance
  · show (EA.inverse ⋙ F ⋙ EB.functor).Linear R
    infer_instance
  · show (EA.inverse ⋙ F ⋙ EB.functor).IsTriangulated
    infer_instance

/-- **Stacks 09SC, the implication (2) ⇒ (1).** Let `R` be a commutative ring and let `A` and `B`
be `R`-algebras, not assumed commutative. Let `P` be an object of `D(Mod-B)` such that

* `P` can be represented by a finite complex of finite projective right `B`-modules, that is, `P`
  is perfect;
* an object `K` of `D(Mod-B)` with `Ext^i_B(P, K) = 0` for every `i : ℤ` is zero;
* `Ext^i_B(P, P) = 0` for `i ≠ 0`, and the endomorphism `R`-algebra of `P` is `A`.

Then `D(Mod-A)` and `D(Mod-B)` are equivalent by an additive, `R`-linear equivalence which, for
some commutation with the translation, is triangulated.

The object `P` is carried back along the degree-zero comparison
`DifferentialGradedModule.degreeZeroDerivedEquivalence` into `D(degreeZero R B, d)`, where
[Stacks, Tag 09S8] produces an equivalence with `D(degreeZero R A, d)`; conjugating that
equivalence by the two comparisons gives the conclusion, the comparisons being exact by
`DifferentialGradedModule.degreeZeroDerivedEquivalence_functor_exact`. Compactness of `P` is its
perfectness, by Tag 07LT. -/
@[stacks 09SC "(2) ⇒ (1), the converse of DegreeZeroRickard's (1) ⇒ (2), with the same \
spellings: clause (2)(a) as StacksDraft.Perfect.IsPerfect, Ext vanishing as Subsingleton of the \
shifted Hom group, the degree-zero clause of (2)(c) as A ≃ₐ[R] End P, and clause (1) delivered \
as an additive R-linear equivalence triangulated for SOME commutation with the translation, as \
in 09S8's own clause (1). D(A) is the derived category of right A-modules"]
theorem exists_derivedEquivalence_of_isPerfect_and_detectsZero
    (P : DerivedCategory (ModuleCat.{u} Bᵐᵒᵖ))
    (hperf : StacksDraft.Perfect.IsPerfect P)
    (hgen : ∀ K : DerivedCategory (ModuleCat.{u} Bᵐᵒᵖ),
      (∀ i : ℤ, Subsingleton (P ⟶ K⟦i⟧)) → IsZero K)
    (hvan : ∀ i : ℤ, i ≠ 0 → Subsingleton (P ⟶ P⟦i⟧))
    (hend : Nonempty (A ≃ₐ[R] End P)) :
    ∃ E : DerivedCategory (ModuleCat.{u} Aᵐᵒᵖ) ≌ DerivedCategory (ModuleCat.{u} Bᵐᵒᵖ),
      E.functor.Additive ∧ E.functor.Linear R ∧
        ∃ hs : E.functor.CommShift ℤ, letI := hs; E.functor.IsTriangulated := by
  obtain ⟨hsB, -⟩ :=
    degreeZeroDerivedEquivalence_functor_exact (R := R) (S := B) (A := Bᵐᵒᵖ)
  let EB := degreeZeroDerivedEquivalence (R := R) (S := B) (A := Bᵐᵒᵖ)
  let : EB.functor.CommShift ℤ := hsB
  let : EB.symm.functor.CommShift ℤ := EB.commShiftInverse ℤ
  have hcompact : IsCompactObject.{u} (EB.inverse.obj P) :=
    (isCompactObject_iff_isCompactObject_obj EB.inverse P).1
      ((StacksDraft.Perfect.isPerfect_iff_isCompactObject P).1 hperf)
  have hgen₀ : ∀ N : derivedCategory' (degreeZero R B),
      (∀ (i : ℤ) (f : EB.inverse.obj P ⟶ N⟦i⟧), f = 0) → IsZero N := fun N hN =>
    (detectsZero_iff_obj EB.symm P).1 hgen N fun i =>
      (subsingleton_hom_iff_forall_eq_zero _ _).2 (hN i)
  have hvan₀ : ∀ i : ℤ, i ≠ 0 →
      ∀ f : EB.inverse.obj P ⟶ (EB.inverse.obj P)⟦i⟧, f = 0 := fun i hi =>
    (subsingleton_hom_iff_forall_eq_zero _ _).1
      ((subsingleton_shiftHom_iff_obj EB.symm P P i).1 (hvan i hi))
  have hend₀ : Nonempty ((degreeZero R A).A ≃ₐ[R] End (EB.inverse.obj P)) := by
    obtain ⟨ea⟩ := hend
    exact ⟨ea.trans ((Iso.endAlgEquiv (R := R) (EB.counitIso.app P)).symm.trans
      (EB.fullyFaithfulFunctor.algEquivEndOfFullyFaithful (R := R) (EB.inverse.obj P)).symm)⟩
  obtain ⟨G, hadd, hlin, ⟨hsG, htriG⟩, -⟩ :=
    DifferentialGraded.Bimodule.exists_derivedEquivalence_of_isCompactObject_and_isWeakGenerator
      (degreeZero R A) (degreeZero R B) degreeZero_grading_eq_bot (EB.inverse.obj P)
      hcompact hgen₀ hvan₀ hend₀
  let : G.functor.CommShift ℤ := hsG
  have := hadd
  have := hlin
  have : G.functor.IsTriangulated := htriG
  exact exists_derivedEquivalence_of_degreeZero G.functor

/-- **Stacks 09SC, the equivalence of (1) and (2).** Let `R` be a commutative ring and let `A`
and `B` be `R`-algebras, not assumed commutative. The following are equivalent.

1. `D(Mod-A)` and `D(Mod-B)` are equivalent by an additive, `R`-linear equivalence which, for some
   commutation with the translation, is triangulated.
2. There is an object `P` of `D(Mod-B)` which is perfect, for which an object `K` with
   `Ext^i_B(P, K) = 0` for all `i : ℤ` is zero, with `Ext^i_B(P, P) = 0` for `i ≠ 0` and with
   endomorphism `R`-algebra `A`.

The implication `(1) ⇒ (2)` is
`DifferentialGradedModule.exists_isPerfect_and_detectsZero_of_derivedEquivalence`, which needs
only additivity, `R`-linearity and commutation with the translation; the converse is
`DifferentialGradedModule.exists_derivedEquivalence_of_isPerfect_and_detectsZero`. -/
@[stacks 09SC "the equivalence of (1) and (2), with clause (1) as an additive R-linear \
equivalence of the derived categories of right modules which is triangulated for SOME \
commutation with the translation, clause (2)(a) as StacksDraft.Perfect.IsPerfect, Ext vanishing \
as Subsingleton of the shifted Hom group and the degree-zero clause of (2)(c) as an isomorphism \
of R-algebras A ≃ₐ[R] End P"]
theorem derivedEquivalence_iff_exists_isPerfect_and_detectsZero :
    (∃ E : DerivedCategory (ModuleCat.{u} Aᵐᵒᵖ) ≌ DerivedCategory (ModuleCat.{u} Bᵐᵒᵖ),
        E.functor.Additive ∧ E.functor.Linear R ∧
          ∃ hs : E.functor.CommShift ℤ, letI := hs; E.functor.IsTriangulated) ↔
      ∃ P : DerivedCategory (ModuleCat.{u} Bᵐᵒᵖ),
        StacksDraft.Perfect.IsPerfect P ∧
        (∀ K : DerivedCategory (ModuleCat.{u} Bᵐᵒᵖ),
          (∀ i : ℤ, Subsingleton (P ⟶ K⟦i⟧)) → IsZero K) ∧
        (∀ i : ℤ, i ≠ 0 → Subsingleton (P ⟶ P⟦i⟧)) ∧
        Nonempty (A ≃ₐ[R] End P) := by
  constructor
  · rintro ⟨E, hadd, hlin, hs, -⟩
    have := hadd
    have := hlin
    let := hs
    exact exists_isPerfect_and_detectsZero_of_derivedEquivalence E
  · exact fun ⟨P, hperf, hgen, hvan, hend⟩ =>
      exists_derivedEquivalence_of_isPerfect_and_detectsZero P hperf hgen hvan hend

/-- **Stacks 09SC, the implication (3) ⇒ (1).** Let `R` be a commutative ring, let `A` and `B` be
`R`-algebras, not assumed commutative, and let `N` be a differential graded `(A, B)`-bimodule over
the degree-zero algebras for which the derived tensor functor

`- ⊗_A^𝐋 N : D(degreeZero R A, d) ⥤ D(degreeZero R B, d)`

is an equivalence. Then `D(Mod-A)` and `D(Mod-B)` are equivalent by an additive, `R`-linear
equivalence which, for some commutation with the translation, is triangulated.

The derived tensor functor is additive, `R`-linear (Tag 09S7) and exact (Tags 09LR and 09LS), so
conjugating it by the two degree-zero comparisons — exact by
`DifferentialGradedModule.degreeZeroDerivedEquivalence_functor_exact` — gives the conclusion. No
flatness hypothesis is needed for this direction. -/
@[stacks 09SC "(3) ⇒ (1), the converse of DegreeZeroRickardBimodule's (1) ⇒ (3), with N a \
differential graded (A,B)-bimodule over the degree-zero algebras and the hypothesis that its \
differential graded derived tensor functor is an equivalence; no flatness of B over R is needed \
for this direction. Clause (1) is delivered as an additive R-linear equivalence of the derived \
categories of right modules which is triangulated for SOME commutation with the translation"]
theorem exists_derivedEquivalence_of_bimodule
    (N : DifferentialGraded.Bimodule (degreeZero R A) (degreeZero R B))
    (hN : (DifferentialGraded.Bimodule.derivedTensorFunctor N).IsEquivalence) :
    ∃ E : DerivedCategory (ModuleCat.{u} Aᵐᵒᵖ) ≌ DerivedCategory (ModuleCat.{u} Bᵐᵒᵖ),
      E.functor.Additive ∧ E.functor.Linear R ∧
        ∃ hs : E.functor.CommShift ℤ, letI := hs; E.functor.IsTriangulated := by
  have := hN
  exact exists_derivedEquivalence_of_degreeZero (DifferentialGraded.Bimodule.derivedTensorFunctor N)

/-- **Stacks 09SC, the equivalence of (1) and (3).** Let `R` be a commutative ring, let `A` and
`B` be `R`-algebras, not assumed commutative, and assume `B` is flat as an `R`-module. The
following are equivalent.

1. `D(Mod-A)` and `D(Mod-B)` are equivalent by an additive, `R`-linear equivalence which, for some
   commutation with the translation, is triangulated.
3. There is a differential graded `(A, B)`-bimodule `N` over the degree-zero algebras for which
   `- ⊗_A^𝐋 N : D(degreeZero R A, d) ⥤ D(degreeZero R B, d)` is an equivalence.

The implication `(1) ⇒ (3)` is
`DifferentialGradedModule.exists_bimodule_derivedTensorEquivalence_of_derivedEquivalence`, which
is where flatness is used; the converse is
`DifferentialGradedModule.exists_derivedEquivalence_of_bimodule`, which needs no flatness. The
reading of "`(A, B)`-bimodule" is the differential graded one of
`StacksFrontier/Algebra/DifferentialGraded/Module/DegreeZeroRickardBimodule.lean`. -/
@[stacks 09SC "the equivalence of (1) and (3) for B flat over R, with clause (1) as an additive \
R-linear equivalence of the derived categories of right modules which is triangulated for SOME \
commutation with the translation, and N a differential graded (A,B)-bimodule over the \
degree-zero algebras per 09SA/09S7 rather than an ordinary bimodule"]
theorem derivedEquivalence_iff_exists_bimodule [Module.Flat R B] :
    (∃ E : DerivedCategory (ModuleCat.{u} Aᵐᵒᵖ) ≌ DerivedCategory (ModuleCat.{u} Bᵐᵒᵖ),
        E.functor.Additive ∧ E.functor.Linear R ∧
          ∃ hs : E.functor.CommShift ℤ, letI := hs; E.functor.IsTriangulated) ↔
      ∃ N : DifferentialGraded.Bimodule (degreeZero R A) (degreeZero R B),
        (DifferentialGraded.Bimodule.derivedTensorFunctor N).IsEquivalence := by
  constructor
  · rintro ⟨E, hadd, hlin, hs, -⟩
    have := hadd
    have := hlin
    let := hs
    obtain ⟨N, hN, -⟩ :=
      exists_bimodule_derivedTensorEquivalence_of_derivedEquivalence (R := R) (A := A) (B := B) E
    exact ⟨N, hN⟩
  · exact fun ⟨N, hN⟩ => exists_derivedEquivalence_of_bimodule N hN

end DifferentialGradedModule

end
