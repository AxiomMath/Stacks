module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportRepresentationHomologyUniversal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricRepresentationCohomologyNotProjectiveLine

/-!
# The homological half of Tag 03VM for `X_k̄ ≇ ℙ¹_k̄`

Let `k` be a field, `X` a geometrically connected smooth curve over `k` with `X_k̄ ≇ ℙ¹_k̄`, `Λ` a
finite ring with `#Λ ∈ k^*` and `X ⟶ X̄` a compactification. The ring need not be commutative, and
its modules are left modules. Then the functors `(M, ρ) ↦ H_c^{2-i}(X_k̄, ℱ_ρ)` on finite
`Λ`-modules with continuous action of `π₁(X, η̄)` form a universal homological δ-functor, i.e. they
are the left derived functors of `(M, ρ) ↦ H_c^2(X_k̄, ℱ_ρ)`, and they are isomorphic, as
δ-functors, to the homology `H_i(π₁(X_k̄, η̄), M)` (`AlgebraicGeometry.geometricGroupHomology`).

## Main results

* `AlgebraicGeometry.isUniversal_compactSupportRepresentationHomology_of_not_iso_projectiveLine`.
* `AlgebraicGeometry.compactSupportGroupHomologyIsoOfNotIsoProjectiveLine`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupCohomology Stacks.EtaleCohomology
  Stacks.Frobenius

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (K : Type u) [Field K] [Algebra k K]
  [IsAlgClosure k K] (Λ : Type) [Ring Λ] [Finite Λ]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) K)) (j : CompactificationOf (Over.mk f))
  (hΛ : IsUnit ((Nat.card Λ : ℕ) : k))
  (hP : ¬ ∃ e : fieldBaseChange (Over.mk f) K ≅ projectiveSpaceOver 1 (Spec (.of K)),
    e.hom ≫ (projectiveSpaceOver 1 (Spec (.of K)) ↘ Spec (.of K)) =
      pullback.snd (Over.mk f).hom (specAlgebraMap k K))

omit [IsAlgClosure k K] [Ring Λ] [Finite Λ] in
include hΛ in
/-- `#Λ` is invertible in `K` when it is in `k`. -/
lemma isUnit_card_fieldBaseChange [Fintype Λ] : IsUnit ((Fintype.card Λ : ℕ) : K) := by
  rw [← Nat.card_eq_fintype_card, ← map_natCast (algebraMap k K)]
  exact hΛ.map _

omit [Ring Λ] [Finite Λ] in
include hΛ in
/-- `#Λᵐᵒᵖ = #Λ` is invertible in `k`. -/
lemma isUnit_natCard_mulOpposite : IsUnit ((Nat.card Λᵐᵒᵖ : ℕ) : k) := by
  rwa [Nat.card_congr MulOpposite.opEquiv.symm]

include hΛ hP in
/-- **`(M, ρ) ↦ H_c^{2-i}(X_k̄, ℱ_ρ)` are the left derived functors of
`(M, ρ) ↦ H_c^2(X_k̄, ℱ_ρ)`**: they form a universal homological δ-functor, for `X_k̄ ≇ ℙ¹_k̄` and
`#Λ` invertible in `k`. -/
@[stacks 03VM "first assertion: `(M, ρ) ↦ H_c^{2-i}(X_k̄, ℱ_ρ)` is a universal homological \
δ-functor, i.e. the left derived functors of `(M, ρ) ↦ H_c^2(X_k̄, ℱ_ρ)`"]
theorem isUniversal_compactSupportRepresentationHomology_of_not_iso_projectiveLine :
    letI := connectedSpace_of_isCurve B X f
    haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
    (compactSupportRepresentationHomology B X
      (y.map (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom)
      Λ f j K).IsUniversal := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f K
  let := QuasiCompact.compactSpace_of_compactSpace f
  let := quasiSeparatedSpace_of_quasiSeparated f
  have : IsAlgClosed K := IsAlgClosure.isAlgClosed k
  have : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
  let : Fintype Λ := Fintype.ofFinite Λ
  have hn := isUnit_card_fieldBaseChange K Λ hΛ
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_isUnit hn
  exact isUniversal_compactSupportRepresentationHomology B X f K Λ y j hn hζ
    (isIso_geometricComparison_of_not_iso_projectiveLine B X f K Λ y hΛ hP)
    (isIso_geometricComparison_of_not_iso_projectiveLine B X f K Λᵐᵒᵖ y
      (isUnit_natCard_mulOpposite Λ hΛ) hP)

include hΛ hP in
/-- **Tag 03VM, homological half: `H_c^{2-i}(X_k̄, ℱ_ρ) ≅ H_i(π₁(X_k̄, η̄), M)`** as homological
δ-functors, extending the identification `H²_c(X_k̄, ℱ_ρ) = M_{π₁(X_k̄, η̄)}` of Tag 03VK (for a
primitive `#Λ`-th root of unity of `k̄`), for `X_k̄ ≇ ℙ¹_k̄` and `#Λ` invertible in `k`. -/
def compactSupportGroupHomologyIsoOfNotIsoProjectiveLine :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f K
    haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
    letI : Fintype Λ := Fintype.ofFinite Λ
    compactSupportRepresentationHomology B X
        (y.map (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom)
        Λ f j K ≅
      geometricGroupHomology B X f K Λ y :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f K
  letI := QuasiCompact.compactSpace_of_compactSpace f
  letI := quasiSeparatedSpace_of_quasiSeparated f
  haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
  haveI : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
  letI : Fintype Λ := Fintype.ofFinite Λ
  have hn := isUnit_card_fieldBaseChange K Λ hΛ
  compactSupportGroupHomologyIso B X f K Λ y j hn
    (exists_isPrimitiveRoot_of_isUnit hn).choose_spec
    (isIso_geometricComparison_of_not_iso_projectiveLine B X f K Λ y hΛ hP)
    (isIso_geometricComparison_of_not_iso_projectiveLine B X f K Λᵐᵒᵖ y
      (isUnit_natCard_mulOpposite Λ hΛ) hP)

end AlgebraicGeometry

end
