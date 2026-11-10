module

public import StacksFrontier.Algebra.DifferentialGraded.Module.CohomologyAlgebra
public import StacksFrontier.Algebra.DifferentialGraded.Module.EndomorphismDGAQuasiIso
public import StacksFrontier.Algebra.DifferentialGraded.Module.PropertyP

/-! # The quasi-isomorphism from the degree-`≤ 0` truncation of an endomorphism algebra onto an
algebra concentrated in degree zero

Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative ring `R`, assume
`A = H^0(A)`, and let `Q` be a right differential graded `B`-module with property (P) such that

* `Hom_{D(B, d)}(Q, Q[k]) = 0` for every `k ≠ 0`, and
* `A` is the endomorphism `R`-algebra of the class of `Q` in `D(B, d)`.

Let `E = End(Q)` be the endomorphism differential graded algebra of `Q` (Tag 09LE) and let `E'` be
its degree-`≤ 0` truncation, that is the endomorphism algebra of `Q` in the degree-`≤ 0` truncation
of the differential graded category of right differential graded `B`-modules. This file produces
the second of the two quasi-isomorphisms
$$(A, \text{d}) \longleftarrow (E', \text{d}) \longrightarrow (E, \text{d})$$
of the proofs of [Stacks, Tag 09S8] and [Stacks, Tag 09SA]. The first one is
`DifferentialGradedModule.exists_hom_nonpositiveEndomorphismDGA_bijective_cohomologyMap`.

## Main definitions

* `DifferentialGradedModule.shiftCompare`: the comparison in `D(B, d)` between the image of the
  `k`-th shift of a module and the `k`-th shift of its image.

## Main results

* `DifferentialGradedModule.exists_propertyPFiltration_model`: every object of `D(B, d)` is
  isomorphic to the image of a differential graded module carrying a property-(P) filtration.
* `DifferentialGradedAlgebra.exists_hom_of_cohomologyZeroAlgEquiv`: **a differential graded
  algebra `E` with nothing in positive degrees, whose cohomology is concentrated in degree zero
  and whose degree-zero cohomology is identified with an algebra `A` concentrated in degree zero,
  admits a quasi-isomorphism `E → A`.**
* `DifferentialGradedModule.exists_hom_nonpositiveEndomorphismDGA_to_concentrated`: the
  specialisation to `E = E'`, the degree-`≤ 0` truncation of `End(Q)`.

## References

* [Stacks Project, Tag 09SA](https://stacks.math.columbia.edu/tag/09SA) and
  [Tag 09S8](https://stacks.math.columbia.edu/tag/09S8), in whose proofs this quasi-isomorphism
  appears.
* [Stacks Project, Tag 09LE](https://stacks.math.columbia.edu/tag/09LE) for the endomorphism
  algebra, [Tag 09KP](https://stacks.math.columbia.edu/tag/09KP) for property-(P) resolutions and
  [Tag 09KY](https://stacks.math.columbia.edu/tag/09KY) for the identification of `H^k(End(Q))`
  with `Hom_{D(B,d)}(Q, Q[k])`.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]

/-! ### Comparing the two shifts, and property-(P) models -/

/-- **The image in `D(B, d)` of the `k`-th shift of a module, identified with the `k`-th shift of
its image**: the comparison isomorphism of the quotient functor onto the homotopy category,
followed by that of the localization functor. -/
def shiftCompare {B : DifferentialGradedAlgebra R} (M : DifferentialGradedModule B) (k : ℤ) :
    (toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj (M.shift k) ≅
      ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj M)⟦k⟧ :=
  (quasiIsomorphisms' B).Q.mapIso (quotientShiftIso M k) ≪≫
    ((quasiIsomorphisms' B).Q.commShiftIso k).app ((toHomotopyCategory B).obj M)

/-- `regularShiftCompare` is `shiftCompare` at the regular module. -/
theorem regularShiftCompare_eq (A : DifferentialGradedAlgebra R) (k : ℤ) :
    regularShiftCompare A k = shiftCompare (regularModule A) k :=
  rfl

/-- **Every object of `D(B, d)` is isomorphic to the image of a differential graded module
carrying a property-(P) filtration.** -/
theorem exists_propertyPFiltration_model (B : DifferentialGradedAlgebra.{u, u} R)
    (X : derivedCategory' B) :
    ∃ Q : DifferentialGradedModule.{u, u, u} B, Nonempty (PropertyPFiltration Q) ∧
      Nonempty ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj Q ≅ X) := by
  obtain ⟨Q, g, hg, hQ⟩ := exists_propertyP_resolution B
    (((quasiIsomorphisms' B).Q.objPreimage X).as)
  have : IsIso ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).map g) :=
    Localization.inverts (quasiIsomorphisms' B).Q (quasiIsomorphisms' B) _
      ((quasiIsomorphisms_map_iff' B g).2 hg)
  exact ⟨Q, hQ, ⟨(asIso ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).map g)).trans
    (show (toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj
        (((quasiIsomorphisms' B).Q.objPreimage X).as) ≅ X
      from (quasiIsomorphisms' B).Q.objObjPreimageIso X)⟩⟩

end DifferentialGradedModule

namespace DifferentialGradedAlgebra

variable {R : Type u} [CommRing R]

/-- **A degree-`≤ 0` differential graded algebra whose cohomology is concentrated in degree zero
maps quasi-isomorphically onto that cohomology.** Let `A` be a differential graded `R`-algebra
concentrated in degree zero and let `E` be one with nothing in positive degrees, with
`H^k(E)` a singleton for `k ≠ 0` and with an isomorphism of `R`-algebras `H^0(E) ≃ₐ[R] A`. Then
there is a homomorphism of differential graded algebras `E → A` which is bijective on cohomology
in every degree. -/
theorem exists_hom_of_cohomologyZeroAlgEquiv (A E : DifferentialGradedAlgebra R)
    (hA : ∀ i : ℤ, i ≠ 0 → A.grading i = ⊥)
    (hE : ∀ n : ℤ, 0 < n → E.grading n = ⊥)
    (Φ : E.Cohomology 0 ≃ₐ[R] A.A)
    (hsub : ∀ k : ℤ, k ≠ 0 → Subsingleton (E.Cohomology k)) :
    ∃ θ : E.Hom A, ∀ k : ℤ, Function.Bijective (θ.cohomologyMap k) := by
  let Λ : ↥(E.grading 0) →ₐ[R] A.A :=
    Φ.toAlgHom.comp ((cohomologyZeroMk E).comp (E.gradingZeroAlgEquivCocycleZero hE).toAlgHom)
  have hΛ1 : Λ.toLinearMap ⟨1, SetLike.one_mem_graded E.grading⟩ = 1 := map_one Λ
  have hΛmul : ∀ a b : ↥(E.grading 0),
      Λ.toLinearMap ⟨(a : E.A) * b, SetLike.mul_mem_graded a.property b.property⟩ =
        Λ.toLinearMap a * Λ.toLinearMap b := by
    intro a b
    rw [show (⟨(a : E.A) * b, SetLike.mul_mem_graded a.property b.property⟩ : ↥(E.grading 0))
        = a * b from Subtype.ext (SetLike.GradeZero.coe_mul a b).symm]
    exact map_mul Λ a b
  have hΛd : ∀ a : E.grading (-1),
      Λ.toLinearMap ⟨E.d a, by simpa using E.d_mem (-1) (a : E.A) a.property⟩ = 0 := by
    intro a
    change Φ (cohomologyZeroMk E _) = 0
    refine (congrArg Φ ?_).trans (map_zero Φ)
    rw [cohomologyZeroMk_apply]
    exact (Cohomology.mk_eq_zero_iff _).2 ⟨a, rfl⟩
  obtain ⟨θ, hθ0, hθne⟩ := E.exists_hom_of_degreeZero A hE hA Λ.toLinearMap hΛ1 hΛmul hΛd
  refine ⟨θ, fun k ↦ ?_⟩
  by_cases hk : k = 0
  · subst hk
    have hfun : (A.cohomologyZeroEquiv hA) ∘ (θ.cohomologyMap 0) = Φ := by
      funext x
      induction x using Quotient.ind with | _ a => ?_
      change θ.toAlgebraHom (a.1 : E.A) = Φ (Quotient.mk _ a)
      rw [hθ0 a.1]
      change Φ (cohomologyZeroMk E (E.gradingZeroAlgEquivCocycleZero hE a.1)) = _
      rw [cohomologyZeroMk_apply,
        show E.gradingZeroAlgEquivCocycleZero hE a.1 = a from Subtype.ext rfl]
    rw [← Equiv.comp_bijective _ (A.cohomologyZeroEquiv hA), hfun]
    exact Φ.bijective
  · have := hsub k hk
    have := A.subsingleton_cohomology hA hk
    exact ⟨fun x y _ ↦ Subsingleton.elim x y,
      fun y ↦ ⟨Quotient.mk _ ⟨0, by simp⟩, Subsingleton.elim _ _⟩⟩

end DifferentialGradedAlgebra

namespace DifferentialGradedModule

open DifferentialGraded.Bimodule DifferentialGradedAlgebra

variable {R : Type u} [CommRing R]

/-- **The quasi-isomorphism `E' → A` of the proofs of [Stacks, Tag 09S8] and
[Stacks, Tag 09SA].** Let `A` be a differential graded `R`-algebra concentrated in degree zero,
let `Q` be a right differential graded `B`-module with property (P) such that
`Hom_{D(B, d)}(Q, Q[k]) = 0` for every `k ≠ 0`, and let `A` be the endomorphism `R`-algebra of
the class of `Q` in `D(B, d)`. Then the endomorphism algebra of `Q` in the degree-`≤ 0` truncation
of the differential graded category of right differential graded `B`-modules admits a
homomorphism onto `A` which is bijective on cohomology in every degree. -/
theorem exists_hom_nonpositiveEndomorphismDGA_to_concentrated
    (A B : DifferentialGradedAlgebra.{u, u} R)
    (hA : ∀ i : ℤ, i ≠ 0 → A.grading i = ⊥)
    (Q : DifferentialGradedModule.{u, u, u} B)
    (hQ : Nonempty (PropertyPFiltration Q))
    (hvanish : ∀ k : ℤ, k ≠ 0 →
      ∀ f : (toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj Q ⟶
        (toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj (Q.shift k), f = 0)
    (e : A.A ≃ₐ[R] End ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj Q)) :
    ∃ θ : (DGCategory.homRepresentation
        (DGCategory.nonpositive (dgCategory.{u, u, u} B)) Q).algebra.Hom A,
      ∀ k : ℤ, Function.Bijective (θ.cohomologyMap k) := by
  obtain ⟨ψ, hψ⟩ := exists_hom_nonpositiveEndomorphismDGA_bijective_cohomologyMap B Q hQ
    (fun k hk ↦ hvanish k (ne_of_gt hk))
  have hcomp := bijective_cohomologyEndomorphismComparison_endomorphism B Q hQ
  have hsubE : ∀ k : ℤ, k ≠ 0 → Subsingleton ((endomorphismDGA B Q).Cohomology k) :=
    fun k hk ↦ ⟨fun x y ↦ (hcomp k).injective
      ((hvanish k hk _).trans (hvanish k hk _).symm)⟩
  exact DifferentialGradedAlgebra.exists_hom_of_cohomologyZeroAlgEquiv A _ hA
    (fun n hn ↦ DGCategory.nonpositive_grading_eq_bot (dgCategory.{u, u, u} B) Q n hn)
    ((AlgEquiv.ofBijective ψ.cohomologyZeroAlgHom (hψ 0)).trans
      ((AlgEquiv.ofBijective (cohomologyZeroBimoduleEndAlgHom (endomorphism B Q))
        ((bijective_cohomologyZeroBimoduleEnd_iff _).2 (hcomp 0))).trans e.symm))
    (fun k hk ↦ ⟨fun x y ↦ (hψ k).injective (@Subsingleton.elim _ (hsubE k hk) _ _)⟩)

end DifferentialGradedModule

end
