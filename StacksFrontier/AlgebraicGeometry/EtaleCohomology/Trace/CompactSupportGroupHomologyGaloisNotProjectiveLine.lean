module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportGroupHomologyGalois
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportGroupHomologyNotProjectiveLine

/-!
# The Galois-equivariant `H_c^{2-i}(X_k̄, ℱ_ρ) = H_i(π₁(X_k̄, η̄), M)(-1)` for `X_k̄ ≇ ℙ¹_k̄`

Let `k` be a field, `X` a geometrically connected smooth curve over `k` with `X_k̄ ≇ ℙ¹_k̄`, `Λ` a
finite ring with `#Λ ∈ k^*` and `X ⟶ X̄` a compactification. Then
`H_c^{2-i}(X_k̄, ℱ_ρ) ≅ H_i(π₁(X_k̄, η̄), M)(-1)` as homological δ-functors in `(M, ρ)`, the twist
`(-1)` being `Hom(μ_n(k̄), -)` for `n = #Λ`, with degree zero the choice-free identification of
Tag 03VK, and this isomorphism commutes in every degree with the action of every
`σ ∈ Aut_k(k̄) = Gal(k^{sep}/k)`.

## Main results

* `AlgebraicGeometry.compactSupportGroupHomologyTwistIsoOfNotIsoProjectiveLine`.
* `AlgebraicGeometry.compactSupportGroupHomologyTwistIsoOfNotIsoProjectiveLine_galois`.
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

include hΛ hP in
/-- When `X_k̄ ≇ ℙ¹_k̄`, the isomorphism `H_c^{2-i}(X_k̄, ℱ_ρ) ≅ H_i(π₁(X_k̄, η̄), M)(-1)` of
homological δ-functors, extending the choice-free identification
`H²_c(X_k̄, ℱ_ρ) = Hom(μ_n(k̄), M_{π₁(X_k̄, η̄)})` of Tag 03VK. -/
@[stacks 03VM "second assertion: `H_c^{2-i}(X_k̄, ℱ_ρ) ≅ H_i(π₁(X_k̄, η̄), M)(-1)` as \
homological δ-functors in `(M, ρ)`"]
def compactSupportGroupHomologyTwistIsoOfNotIsoProjectiveLine :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f K
    haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
    letI : Fintype Λ := Fintype.ofFinite Λ
    compactSupportRepresentationHomology B X
        (y.map (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom)
        Λ f j K ≅
      geometricGroupHomologyTwist B X f K Λ y (isUnit_card_fieldBaseChange K Λ hΛ) :=
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f K
  let := QuasiCompact.compactSpace_of_compactSpace f
  let := quasiSeparatedSpace_of_quasiSeparated f
  have : IsAlgClosed K := IsAlgClosure.isAlgClosed k
  have : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
  let : Fintype Λ := Fintype.ofFinite Λ
  compactSupportGroupHomologyTwistIso B X f K Λ y j (isUnit_card_fieldBaseChange K Λ hΛ)
    (isIso_geometricComparison_of_not_iso_projectiveLine B X f K Λᵐᵒᵖ y
      (isUnit_natCard_mulOpposite Λ hΛ) hP)
    (isIso_geometricComparison_of_not_iso_projectiveLine B X f K Λ y hΛ hP)

include hΛ hP in
/-- The isomorphism `H_c^{2-i}(X_k̄, ℱ_ρ) ≅ H_i(π₁(X_k̄, η̄), M)(-1)` is
`Gal(k^{sep}/k)`-equivariant: for every `σ ∈ Aut_k(k̄)` the action of `σ` on `H_c^{2-i}(X_k̄, ℱ_ρ)`
(`AlgebraicGeometry.compactSupportRepresentationHomologyGalois`) corresponds, in every degree, to
the action of `σ` on `H_i(π₁(X_k̄, η̄), M)(-1)`
(`AlgebraicGeometry.geometricGroupHomologyTwistGalois`), which in degree zero is
`f ↦ σ ∘ f ∘ σ⁻¹` on `Hom(μ_n(k̄), M_{π₁(X_k̄, η̄)})`. -/
@[stacks 03VM "second assertion, Galois action: the isomorphism `H_c^{2-i}(X_k̄, ℱ_ρ) ≅ \
H_i(π₁(X_k̄, η̄), M)(-1)` commutes with every `σ ∈ Aut_k(k̄)`"]
theorem compactSupportGroupHomologyTwistIsoOfNotIsoProjectiveLine_galois (σ : K ≃ₐ[k] K) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f K
    letI := QuasiCompact.compactSpace_of_compactSpace f
    letI := quasiSeparatedSpace_of_quasiSeparated f
    haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
    haveI : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
    letI : Fintype Λ := Fintype.ofFinite Λ
    compactSupportRepresentationHomologyGalois B X
        (y.map (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom)
        Λ f j K σ ≫
        (compactSupportGroupHomologyTwistIsoOfNotIsoProjectiveLine B X f K Λ y j hΛ hP).hom =
      (compactSupportGroupHomologyTwistIsoOfNotIsoProjectiveLine B X f K Λ y j hΛ hP).hom ≫
        geometricGroupHomologyTwistGalois B X f K Λ y σ j (isUnit_card_fieldBaseChange K Λ hΛ)
          (isIso_geometricComparison_of_not_iso_projectiveLine B X f K Λᵐᵒᵖ y
            (isUnit_natCard_mulOpposite Λ hΛ) hP) := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f K
  let := QuasiCompact.compactSpace_of_compactSpace f
  let := quasiSeparatedSpace_of_quasiSeparated f
  have : IsAlgClosed K := IsAlgClosure.isAlgClosed k
  have : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
  let : Fintype Λ := Fintype.ofFinite Λ
  exact compactSupportGroupHomologyTwistIso_galois B X f K Λ y σ j
    (isUnit_card_fieldBaseChange K Λ hΛ)
    (isIso_geometricComparison_of_not_iso_projectiveLine B X f K Λᵐᵒᵖ y
      (isUnit_natCard_mulOpposite Λ hΛ) hP)
    (isIso_geometricComparison_of_not_iso_projectiveLine B X f K Λ y hΛ hP)

end AlgebraicGeometry

end
