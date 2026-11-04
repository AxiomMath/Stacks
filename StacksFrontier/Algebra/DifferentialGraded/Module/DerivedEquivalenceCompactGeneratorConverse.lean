module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedEquivalenceBimoduleExistence

/-! # A compact generator with the expected endomorphisms produces a derived equivalence

Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative ring `R` and assume
`A = H^0(A)`. [Stacks, Tag 09S8] says that `D(A, d)` and `D(B, d)` are equivalent as `R`-linear
triangulated categories if and only if `D(B, d)` contains an object `P` which is compact, which
weakly generates, and whose graded endomorphism ring is `A` in degree `0` and vanishes in every
other degree; and that the equivalence constructed from such a `P` carries `A` to `P`.

The direction `(1) ⇒ (2)` is
`DifferentialGradedModule.exists_isCompactObject_and_isWeakGenerator_of_derivedEquivalence`. This
file proves the converse `(2) ⇒ (1)`, assembles the two into the source's `↔`, and proves the
source's final clause for the equivalence the converse constructs.

Given `P` as in (2), replace it by a differential graded module `Q` with property (P)
(`DifferentialGradedModule.exists_propertyPFiltration_model`) and set `E = End(Q)`. Then `Q` is a
differential graded `(E, B)`-bimodule, tautologically, and satisfies the three hypotheses of
[Stacks, Tag 09S7], so `- ⊗_E^𝐋 Q : D(E, d) ⥤ D(B, d)` is an equivalence carrying `E` to `Q`. Let
`E'` be the degree-`≤ 0` truncation of `E`; the two quasi-isomorphisms
`(A, d) ← (E', d) → (E, d)` turn into two further equivalences by [Stacks, Tag 09S6], and the
composite
$$D(A, \text{d}) \longleftarrow D(E', \text{d}) \longrightarrow D(E, \text{d})
\longrightarrow D(B, \text{d})$$
is the equivalence of (1). Each of the three steps carries the regular module to the regular
module — the two extensions of scalars by the unit isomorphism of the relative tensor product, the
last one to `Q` — so the composite carries `A` to `P`.

## Main results

* `DifferentialGraded.Bimodule.exists_derivedEquivalence_of_quasiIso_pair`: the composite
  equivalence, with the two quasi-isomorphisms out of `E'` and the `(E, B)`-bimodule as
  hypotheses.
* `DifferentialGraded.Bimodule.exists_derivedEquivalence_of_isCompactObject_and_isWeakGenerator`:
  **Stacks 09S8, the implication (2) ⇒ (1) together with the source's final clause** that the
  equivalence it constructs sends `A` to `P`.
* `DifferentialGraded.Bimodule.derivedEquivalence_iff_exists_isCompactObject_and_isWeakGenerator`:
  **Stacks 09S8**, the `↔`.

## Implementation notes

*What "equivalent as `R`-linear triangulated categories" is taken to mean.* Condition (1) below
is the existence of an equivalence `D(A, d) ≌ D(B, d)` whose functor is additive, `R`-linear,
commutes with the translation and is triangulated. The converse produces all four; the forward
direction, which is
`DifferentialGradedModule.exists_isCompactObject_and_isWeakGenerator_of_derivedEquivalence`, uses
only the first three. The `Functor.CommShift ℤ` datum is existentially quantified inside (1)
because it is data rather than a proposition, and `Functor.IsTriangulated` is stated relative to
it.

*How the three equivalences acquire their structure.* The two extensions of scalars are derived
tensor products with the regular bimodule, so they are additive, `R`-linear, shift-commuting and
triangulated by Tags 09LR, 09LS and 09S7, all of which are instances; the instances are recorded
for the bundled equivalences of Tags 09S6 and 09S7 in the section
`EquivalenceInstances` below, since instance search does not unfold the bundling. The
quasi-inverse of the first then inherits all four:
`CategoryTheory.Equivalence.inverse_additive`, `.inverseLinear`, `.commShiftInverse` and — as the
right adjoint of a triangulated functor, Tag 0A8D — `CategoryTheory.Adjunction`
`.isTriangulated_rightAdjoint` through `CategoryTheory.Equivalence.IsTriangulated.mk'`.

*K-flatness is not needed.* Unlike [Stacks, Tag 09SA], the converse direction of Tag 09S8 does not
produce an `(A, B)`-bimodule, only an equivalence, so the composition of derived tensor functors
of Tag 09S4 — the one step that needs `B` to be K-flat over `R` — never appears. The source
likewise assumes nothing of the kind here.

*The final clause, and what it is not.* The source's last sentence is about the equivalence
constructed in (2); it is proved here, as the last clause of
`DifferentialGraded.Bimodule.exists_derivedEquivalence_of_isCompactObject_and_isWeakGenerator`,
and it has content: the composite of three functors is tracked across all three. The
corresponding clause of the `(1) ⇒ (2)` statement is a different, trivial assertion — that
the witness `P` may be taken to be `E(A)` — whose proof is `Iso.refl`.

*Universes.* The algebras live in a single universe `u` together with the base ring, and
compactness is taken with respect to coproducts indexed by `Type u`; this is the convention of
Tag 09JJ followed throughout the chapter, and it is more restrictive than the `(1) ⇒ (2)` statement,
which leaves the algebra universes free.

## References

* [Stacks Project, Tag 09S8](https://stacks.math.columbia.edu/tag/09S8), the lemma proved here.
* [Stacks Project, Tag 09S6](https://stacks.math.columbia.edu/tag/09S6) and
  [Tag 09S7](https://stacks.math.columbia.edu/tag/09S7) for the three equivalences the proof
  composes, [Tag 09LE](https://stacks.math.columbia.edu/tag/09LE) for the endomorphism algebra,
  [Tag 09KP](https://stacks.math.columbia.edu/tag/09KP) for property-(P) resolutions and
  [Tag 0A8D](https://stacks.math.columbia.edu/tag/0A8D) for the exactness of a right adjoint.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

namespace DifferentialGraded.Bimodule

open DifferentialGradedAlgebra DifferentialGradedModule CategoryTheory.ObjectProperty

variable {R : Type u} [CommRing R]

/-! ### The structure carried by the bundled equivalences of Tags 09S6 and 09S7 -/

section EquivalenceInstances

variable {A B : DifferentialGradedAlgebra.{u, u} R}

/-- The functor `- ⊗_A^𝐋 B : D(A, d) ⥤ D(B, d)` of
`derivedExtensionEquivalence φ hφ` is additive. -/
instance derivedExtensionEquivalence_functor_additive (φ : A.Hom B)
    (hφ : ∀ k : ℤ, Function.Bijective (φ.cohomologyMap k)) :
    (derivedExtensionEquivalence φ hφ).functor.Additive :=
  inferInstanceAs (derivedTensorFunctor (Bimodule.regular φ)).Additive

/-- The functor `- ⊗_A^𝐋 B : D(A, d) ⥤ D(B, d)` of
`derivedExtensionEquivalence φ hφ` commutes with shifts. -/
instance derivedExtensionEquivalence_functor_commShift (φ : A.Hom B)
    (hφ : ∀ k : ℤ, Function.Bijective (φ.cohomologyMap k)) :
    (derivedExtensionEquivalence φ hφ).functor.CommShift ℤ :=
  inferInstanceAs ((derivedTensorFunctor (Bimodule.regular φ)).CommShift ℤ)

/-- The functor `- ⊗_A^𝐋 B : D(A, d) ⥤ D(B, d)` of
`derivedExtensionEquivalence φ hφ` is `R`-linear. -/
instance derivedExtensionEquivalence_functor_linear (φ : A.Hom B)
    (hφ : ∀ k : ℤ, Function.Bijective (φ.cohomologyMap k)) :
    (derivedExtensionEquivalence φ hφ).functor.Linear R :=
  derivedTensorFunctor_linear (Bimodule.regular φ)

/-- For a homomorphism `φ : A ⟶ B` of differential graded `R`-algebras inducing an isomorphism
on cohomology, the functor `- ⊗_A^𝐋 B : D(A, d) ⥤ D(B, d)` of `derivedExtensionEquivalence φ hφ`
is a triangulated functor. -/
@[stacks 09S6 "the equivalence is one of TRIANGULATED categories: exactness of the functor \
- ⊗_A^𝐋 B : D(A, d) ⥤ D(B, d), under the source's hypothesis that φ is an isomorphism on \
cohomology and no other"]
instance derivedExtensionEquivalence_functor_isTriangulated (φ : A.Hom B)
    (hφ : ∀ k : ℤ, Function.Bijective (φ.cohomologyMap k)) :
    (derivedExtensionEquivalence φ hφ).functor.IsTriangulated :=
  inferInstanceAs (derivedTensorFunctor (Bimodule.regular φ)).IsTriangulated

/-- The quasi-inverse of `derivedExtensionEquivalence φ hφ` commutes with shifts. -/
instance derivedExtensionEquivalence_inverse_commShift (φ : A.Hom B)
    (hφ : ∀ k : ℤ, Function.Bijective (φ.cohomologyMap k)) :
    (derivedExtensionEquivalence φ hφ).inverse.CommShift ℤ :=
  (derivedExtensionEquivalence φ hφ).commShiftInverse ℤ

/-- The equivalence `derivedExtensionEquivalence φ hφ` commutes with shifts. -/
instance derivedExtensionEquivalence_commShift (φ : A.Hom B)
    (hφ : ∀ k : ℤ, Function.Bijective (φ.cohomologyMap k)) :
    (derivedExtensionEquivalence φ hφ).CommShift ℤ :=
  (derivedExtensionEquivalence φ hφ).commShift_of_functor ℤ

/-- For a homomorphism `φ : A ⟶ B` of differential graded `R`-algebras inducing an isomorphism
on cohomology, the quasi-inverse `N ↦ N_A` of `derivedExtensionEquivalence φ hφ` is a triangulated
functor. -/
@[stacks 09S6 "the equivalence is one of TRIANGULATED categories: exactness of the quasi-inverse, \
the restriction functor N ↦ N_A, under the source's hypothesis that φ is an isomorphism on \
cohomology and no other"]
instance derivedExtensionEquivalence_inverse_isTriangulated (φ : A.Hom B)
    (hφ : ∀ k : ℤ, Function.Bijective (φ.cohomologyMap k)) :
    (derivedExtensionEquivalence φ hφ).inverse.IsTriangulated :=
  have h : (derivedExtensionEquivalence φ hφ).IsTriangulated :=
    Equivalence.IsTriangulated.mk' (derivedExtensionEquivalence φ hφ) inferInstance
  h.rightAdjoint_isTriangulated

/-- The functor `- ⊗_A^𝐋 N : D(A, d) ⥤ D(B, d)` of
`derivedTensorEquivalence N h2 h3` is additive. -/
instance derivedTensorEquivalence_functor_additive (N : Bimodule A B)
    [IsCompactObject.{u} ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj N.rightModule)]
    (h2 : ∀ X : derivedCategory' B,
      (∀ (n : ℤ) (f : (toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj N.rightModule ⟶
        X⟦n⟧), f = 0) → IsZero X)
    (h3 : ∀ k : ℤ, Function.Bijective (N.cohomologyEndomorphismComparison k)) :
    (derivedTensorEquivalence N h2 h3).functor.Additive :=
  inferInstanceAs (derivedTensorFunctor N).Additive

/-- The functor `- ⊗_A^𝐋 N : D(A, d) ⥤ D(B, d)` of
`derivedTensorEquivalence N h2 h3` commutes with shifts. -/
instance derivedTensorEquivalence_functor_commShift (N : Bimodule A B)
    [IsCompactObject.{u} ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj N.rightModule)]
    (h2 : ∀ X : derivedCategory' B,
      (∀ (n : ℤ) (f : (toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj N.rightModule ⟶
        X⟦n⟧), f = 0) → IsZero X)
    (h3 : ∀ k : ℤ, Function.Bijective (N.cohomologyEndomorphismComparison k)) :
    (derivedTensorEquivalence N h2 h3).functor.CommShift ℤ :=
  inferInstanceAs ((derivedTensorFunctor N).CommShift ℤ)

/-- The functor `- ⊗_A^𝐋 N : D(A, d) ⥤ D(B, d)` of
`derivedTensorEquivalence N h2 h3` is `R`-linear. -/
instance derivedTensorEquivalence_functor_linear (N : Bimodule A B)
    [IsCompactObject.{u} ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj N.rightModule)]
    (h2 : ∀ X : derivedCategory' B,
      (∀ (n : ℤ) (f : (toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj N.rightModule ⟶
        X⟦n⟧), f = 0) → IsZero X)
    (h3 : ∀ k : ℤ, Function.Bijective (N.cohomologyEndomorphismComparison k)) :
    (derivedTensorEquivalence N h2 h3).functor.Linear R :=
  derivedTensorFunctor_linear N

/-- The functor `- ⊗_A^𝐋 N : D(A, d) ⥤ D(B, d)` of
`derivedTensorEquivalence N h2 h3` is a triangulated functor. -/
instance derivedTensorEquivalence_functor_isTriangulated (N : Bimodule A B)
    [IsCompactObject.{u} ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj N.rightModule)]
    (h2 : ∀ X : derivedCategory' B,
      (∀ (n : ℤ) (f : (toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj N.rightModule ⟶
        X⟦n⟧), f = 0) → IsZero X)
    (h3 : ∀ k : ℤ, Function.Bijective (N.cohomologyEndomorphismComparison k)) :
    (derivedTensorEquivalence N h2 h3).functor.IsTriangulated :=
  inferInstanceAs (derivedTensorFunctor N).IsTriangulated

end EquivalenceInstances

/-! ### The composite equivalence -/

/-- **The composite equivalence of the proof of [Stacks, Tag 09S8], with the two
quasi-isomorphisms and the `(E, B)`-bimodule as hypotheses.** Let `(A, d)`, `(B, d)`, `(E', d)`
and `(E, d)` be differential graded `R`-algebras, let `θ : E' → A` and `ψ : E' → E` be
homomorphisms of differential graded algebras inducing isomorphisms on cohomology, and let `NE` be
a differential graded `(E, B)`-bimodule satisfying the three hypotheses of [Stacks, Tag 09S7].
Then `D(A, d)` and `D(B, d)` are equivalent, by an equivalence which is additive, `R`-linear,
shift-commuting and triangulated and which carries the regular module `A` to the class of `NE`.

The equivalence is `(- ⊗_{E'}^𝐋 A)⁻¹` followed by `- ⊗_{E'}^𝐋 E` and `- ⊗_E^𝐋 NE`, the first two
being Tag 09S6 for `θ` and `ψ` and the third Tag 09S7 for `NE`. Its value on the regular module is
computed one step at a time: the quasi-inverse of extension of scalars along `θ` carries `A` back
to `E'`, because extension of scalars carries `E'` to `A` by the unit isomorphism of the relative
tensor product; extension along `ψ` carries `E'` to `E` for the same reason; and `- ⊗_E^𝐋 NE`
carries `E` to `NE`. -/
theorem exists_derivedEquivalence_of_quasiIso_pair (A B E' E : DifferentialGradedAlgebra.{u, u} R)
    (θ : E'.Hom A) (hθ : ∀ k : ℤ, Function.Bijective (θ.cohomologyMap k))
    (ψ : E'.Hom E) (hψ : ∀ k : ℤ, Function.Bijective (ψ.cohomologyMap k))
    (NE : Bimodule E B)
    [IsCompactObject.{u} ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj NE.rightModule)]
    (h2 : ∀ X : derivedCategory' B,
      (∀ (n : ℤ) (f : (toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj NE.rightModule ⟶
        X⟦n⟧), f = 0) → IsZero X)
    (h3 : ∀ k : ℤ, Function.Bijective (NE.cohomologyEndomorphismComparison k)) :
    ∃ G : derivedCategory' A ≌ derivedCategory' B,
      G.functor.Additive ∧ G.functor.Linear R ∧
        (∃ hs : G.functor.CommShift ℤ, letI := hs; G.functor.IsTriangulated) ∧
          Nonempty (G.functor.obj ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj
            (regularModule A)) ≅
              (toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj NE.rightModule) := by
  refine ⟨(derivedExtensionEquivalence θ hθ).symm.trans
    ((derivedExtensionEquivalence ψ hψ).trans (derivedTensorEquivalence NE h2 h3)), ?_, ?_, ?_, ?_⟩
  · simp only [Equivalence.trans_functor, Equivalence.symm_functor]
    infer_instance
  · simp only [Equivalence.trans_functor, Equivalence.symm_functor]
    infer_instance
  · refine ⟨inferInstance, ?_⟩
    change ((derivedExtensionEquivalence θ hθ).inverse ⋙
      (derivedExtensionEquivalence ψ hψ).functor ⋙
        (derivedTensorEquivalence NE h2 h3).functor).IsTriangulated
    infer_instance
  · have key : ∀ {X Y : DifferentialGradedAlgebra.{u, u} R} (N : Bimodule X Y),
        (derivedTensorFunctor N).obj ((toHomotopyCategory X ⋙ (quasiIsomorphisms' X).Q).obj
          (regularModule X)) ≅
        (toHomotopyCategory Y ⋙ (quasiIsomorphisms' Y).Q).obj N.rightModule :=
      fun N => derivedTensorIsoOfLeftOrthogonal N (regularModule _)
        (leftOrthogonal_acyclic_toHomotopyCategory_regularModule _) (tensorRegularIso N).1
    let rth := key (Bimodule.regular θ)
    let rps := key (Bimodule.regular ψ)
    let rQ := key NE
    let rthinv : (derivedExtensionEquivalence θ hθ).inverse.obj
        ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)) ≅
        (toHomotopyCategory E' ⋙ (quasiIsomorphisms' E').Q).obj (regularModule E') :=
      (derivedExtensionEquivalence θ hθ).inverse.mapIso rth.symm ≪≫
        ((derivedExtensionEquivalence θ hθ).unitIso.app _).symm
    exact ⟨((derivedExtensionEquivalence ψ hψ).functor ⋙
        (derivedTensorEquivalence NE h2 h3).functor).mapIso rthinv ≪≫
      (derivedTensorEquivalence NE h2 h3).functor.mapIso rps ≪≫ rQ⟩

/-! ### Stacks 09S8 -/

/-- **Stacks 09S8, the implication (2) ⇒ (1), with the source's final clause.** Let `(A, d)` and
`(B, d)` be differential graded `R`-algebras with `A = H^0(A)`, i.e. with every homogeneous
component of `A` outside degree zero vanishing. Let `P` be an object of `D(B, d)` such that

* `P` is a compact object of `D(B, d)`,
* an object `N` of `D(B, d)` with `Hom_{D(B,d)}(P, N[i]) = 0` for every `i : ℤ` is zero,
* `Hom_{D(B,d)}(P, P[i]) = 0` for `i ≠ 0`, and
* the endomorphism `R`-algebra of `P` is `A`.

Then `D(A, d)` and `D(B, d)` are equivalent by an additive, `R`-linear, shift-commuting and
triangulated equivalence, **and that equivalence sends the regular module `A` to `P`** — the
source's final clause.

The proof replaces `P` by a property-(P) model `Q`, whose endomorphism differential graded algebra
`E = End(Q)` makes `Q` an `(E, B)`-bimodule satisfying the hypotheses of [Stacks, Tag 09S7], and
composes the equivalence that bimodule defines with the two equivalences of [Stacks, Tag 09S6]
attached to the quasi-isomorphisms `(A, d) ← (E', d) → (E, d)` out of the degree-`≤ 0` truncation
`E'` of `E`; see
`DifferentialGradedModule.exists_hom_nonpositiveEndomorphismDGA_to_concentrated` and
`DifferentialGraded.Bimodule.exists_derivedEquivalence_of_quasiIso_pair`. -/
@[stacks 09S8 "(2) ⇒ (1), by an additive R-linear shift-commuting triangulated equivalence, \
together with the source's final clause that the equivalence constructed in (2) sends A to P"]
theorem exists_derivedEquivalence_of_isCompactObject_and_isWeakGenerator
    (A B : DifferentialGradedAlgebra.{u, u} R)
    (hA : ∀ i : ℤ, i ≠ 0 → A.grading i = ⊥)
    (P : derivedCategory' B) (hcompact : IsCompactObject.{u} P)
    (hgen : ∀ N : derivedCategory' B, (∀ (i : ℤ) (f : P ⟶ N⟦i⟧), f = 0) → IsZero N)
    (hvan : ∀ i : ℤ, i ≠ 0 → ∀ f : P ⟶ P⟦i⟧, f = 0)
    (hend : Nonempty (A.A ≃ₐ[R] End P)) :
    ∃ G : derivedCategory' A ≌ derivedCategory' B,
      G.functor.Additive ∧ G.functor.Linear R ∧
        (∃ hs : G.functor.CommShift ℤ, letI := hs; G.functor.IsTriangulated) ∧
          Nonempty (G.functor.obj ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj
            (regularModule A)) ≅ P) := by
  obtain ⟨Q, hQ, ⟨eQ⟩⟩ := exists_propertyPFiltration_model B P
  have hwQ := isWeakTriangulatedGenerator_singleton_of_iso eQ.symm
    ((isWeakTriangulatedGenerator_singleton_iff_forall_hom_eq_zero P).2 hgen)
  have hvanish : ∀ k : ℤ, k ≠ 0 →
      ∀ f : (toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj Q ⟶
        (toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj (Q.shift k), f = 0 := fun k hk f =>
    (Iso.homCongr eQ (shiftCompare Q k ≪≫
      (shiftFunctor (derivedCategory' B) k).mapIso eQ)).injective
      ((hvan k hk _).trans (hvan k hk _).symm)
  obtain ⟨ea⟩ := hend
  obtain ⟨θ, hθ⟩ := exists_hom_nonpositiveEndomorphismDGA_to_concentrated A B hA Q hQ hvanish
    (ea.trans (Iso.endAlgEquiv (R := R) eQ.symm))
  obtain ⟨ψ, hψ⟩ := exists_hom_nonpositiveEndomorphismDGA_bijective_cohomologyMap B Q hQ
    (fun k hk => hvanish k hk.ne')
  have : IsCompactObject.{u} ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj
      (endomorphism B Q).rightModule) := isCompactObject_of_iso eQ hcompact
  obtain ⟨G, hadd, hlin, hsh, ⟨eG⟩⟩ := exists_derivedEquivalence_of_quasiIso_pair A B _ _ θ hθ ψ hψ
    (endomorphism B Q)
    ((isWeakTriangulatedGenerator_singleton_iff_forall_hom_eq_zero _).1 hwQ)
    (bijective_cohomologyEndomorphismComparison_endomorphism B Q hQ)
  exact ⟨G, hadd, hlin, hsh, ⟨eG.trans eQ⟩⟩

/-- **Stacks 09S8.** Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative
ring `R` and assume `A = H^0(A)`. The following are equivalent.

1. `D(A, d)` and `D(B, d)` are equivalent as `R`-linear triangulated categories.
2. There is an object `P` of `D(B, d)` such that `P` is compact, an object `N` with
   `Hom_{D(B,d)}(P, N[i]) = 0` for all `i : ℤ` is zero, `Hom_{D(B,d)}(P, P[i]) = 0` for `i ≠ 0`,
   and the endomorphism `R`-algebra of `P` is `A`.

Condition (1) is spelled as the existence of an equivalence of categories whose functor is
additive, `R`-linear, commutes with the translation and is triangulated; the degree-zero clause of
(2) is an isomorphism of `R`-algebras `A ≃ₐ[R] End P`, which is what the source's "equal to `A`"
says, the ring structure on the right-hand side being composition.

The implication (1) ⇒ (2) is
`DifferentialGradedModule.exists_isCompactObject_and_isWeakGenerator_of_derivedEquivalence`, which
needs only additivity, `R`-linearity and commutation with the translation; the converse is
`DifferentialGraded.Bimodule`
`.exists_derivedEquivalence_of_isCompactObject_and_isWeakGenerator`, which also proves the
source's final clause that the equivalence it constructs sends `A` to `P`. -/
@[stacks 09S8 "the equivalence of (1) and (2), with (1) as an additive R-linear shift-commuting \
triangulated equivalence and the degree-zero clause of (2) as an isomorphism of R-algebras \
A ≃ₐ[R] End P"]
theorem derivedEquivalence_iff_exists_isCompactObject_and_isWeakGenerator
    (A B : DifferentialGradedAlgebra.{u, u} R)
    (hA : ∀ i : ℤ, i ≠ 0 → A.grading i = ⊥) :
    (∃ G : derivedCategory' A ≌ derivedCategory' B,
        G.functor.Additive ∧ G.functor.Linear R ∧
          ∃ hs : G.functor.CommShift ℤ, letI := hs; G.functor.IsTriangulated) ↔
      ∃ P : derivedCategory' B,
        IsCompactObject.{u} P ∧
          (∀ N : derivedCategory' B, (∀ (i : ℤ) (f : P ⟶ N⟦i⟧), f = 0) → IsZero N) ∧
            (∀ i : ℤ, i ≠ 0 → ∀ f : P ⟶ P⟦i⟧, f = 0) ∧ Nonempty (A.A ≃ₐ[R] End P) := by
  constructor
  · rintro ⟨G, hadd, hlin, hs, _⟩
    obtain ⟨P, h1, h2, h3, h4, _⟩ :=
      exists_isCompactObject_and_isWeakGenerator_of_derivedEquivalence A B hA G
    exact ⟨P, h1, h2, h3, h4⟩
  · rintro ⟨P, h1, h2, h3, h4⟩
    obtain ⟨G, hadd, hlin, hs, _⟩ :=
      exists_derivedEquivalence_of_isCompactObject_and_isWeakGenerator A B hA P h1 h2 h3 h4
    exact ⟨G, hadd, hlin, hs⟩

end DifferentialGraded.Bimodule

end
