module

public import StacksFrontier.Algebra.Homology.MapTotalComplex
public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso

/-!
# Total complexes with finitely many nonzero summands

The degree-`n` term of the total complex of a bicomplex `K` is the coproduct of the terms
`(K.X i₁).X i₂` of total degree `n`. This module records what follows when, in each total degree,
only finitely many of those terms are nonzero: such a coproduct is a finite biproduct, so it
vanishes when all its summands do, and **every** additive functor preserves it — no preservation
of coproducts need be assumed.

The second point upgrades the comparison morphism `Tot(G(K)) ⟶ G(Tot(K))` of
`StacksFrontier.Algebra.Homology.MapTotalComplex` to an isomorphism. It is the second of the two
sufficient conditions announced there, the first being preservation of the relevant coproducts,
which needs no finiteness; the two are proved from the same criterion
`HomologicalComplex₂.TotalMap.isIso_totalMapf_of_isColimit`.

## Main results

* `HomologicalComplex₂.isZero_total_X_of_isZero`: a term of the total complex all of whose
  summands vanish is zero.
* `HomologicalComplex₂.TotalMap.isIso_totalMapf_of_finite`: the comparison
  `Tot(G(K))^n ⟶ G(Tot(K)^n)` is invertible when only finitely many terms of `K` are nonzero in
  total degree `n`.
* `HomologicalComplex₂.TotalMap.totalIsoOfFinite`: **an additive functor commutes with the total
  complex of a bicomplex with finite support in each total degree**, `Tot(G(K)) ≅ G(Tot(K))`.

## Implementation notes

The finiteness hypothesis is taken in the form used by `HomologicalComplex₂.hasTotal_of_finite`,
namely finiteness of the set of pairs of total degree `n` whose term is not a zero object, so
that one and the same hypothesis gives the existence of the total complex and the invertibility
of the comparison. `isIso_totalMapf_of_finite` asks it for a single total degree, which is all
its conclusion concerns.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace HomologicalComplex₂

variable {C : Type*} [Category* C] [Preadditive C]
  {I₁ I₂ I₁₂ : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  (K : HomologicalComplex₂ C c₁ c₂) (c₁₂ : ComplexShape I₁₂)
  [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂] [K.HasTotal c₁₂]

/-- **A term of the total complex all of whose summands vanish is zero**: it is a coproduct of
zero objects. -/
lemma isZero_total_X_of_isZero (n : I₁₂)
    (h : ∀ i₁ i₂, ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = n → IsZero ((K.X i₁).X i₂)) :
    IsZero ((K.total c₁₂).X n) :=
  StacksDraft.TotalComplexQuasiIso.isZero_cofan_pt _
    (K.toGradedObject.isColimitCofanMapObj (ComplexShape.π c₁ c₂ c₁₂) n)
    (fun i => h i.1.1 i.1.2 i.2)

end HomologicalComplex₂

namespace HomologicalComplex₂.TotalMap

variable {C : Type*} {D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  {I₁ I₂ I₁₂ : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} {c₁₂ : ComplexShape I₁₂}
  [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂]
  (G : C ⥤ D) [G.Additive] (K : HomologicalComplex₂ C c₁ c₂)
  [K.HasTotal c₁₂] [(mapBicomplex G K).HasTotal c₁₂]

/-- **`Tot(G(K))^n ⟶ G(Tot(K)^n)` is an isomorphism** when only finitely many terms of `K` are
nonzero in total degree `n`: both sides are then colimits of the same finite family, because an
additive functor preserves a coproduct with finitely many nonzero terms
(`StacksDraft.TotalComplexQuasiIso.isColimitMapCofan`). This is the finite-support sufficient
condition for the general criterion `isIso_totalMapf_of_isColimit`; the other one, which needs no
finiteness but preservation of the coproduct, is `isIso_totalMapf`. -/
lemma isIso_totalMapf_of_finite (n : I₁₂)
    (hfin : {pq : I₁ × I₂ | ComplexShape.π c₁ c₂ c₁₂ pq = n ∧
      ¬ IsZero ((K.X pq.1).X pq.2)}.Finite) :
    IsIso (totalMapf (c₁₂ := c₁₂) G K n) := by
  let S : Set ↥(ComplexShape.π c₁ c₂ c₁₂ ⁻¹' {n}) := {i | ¬ IsZero (K.toGradedObject i.1)}
  have hS : S.Finite :=
    (hfin.preimage Subtype.val_injective.injOn).subset (fun i hi => ⟨i.2, hi⟩)
  have : Finite ↥S := hS.to_subtype
  exact isIso_totalMapf_of_isColimit G K n
    (StacksDraft.TotalComplexQuasiIso.isColimitMapCofan _
      (K.toGradedObject.isColimitCofanMapObj (ComplexShape.π c₁ c₂ c₁₂) n) S
      (fun _ hi => not_not.1 hi) G)

/-- **An additive functor commutes with the total complex** of a bicomplex having, in each total
degree, only finitely many nonzero terms: `Tot(G(K)) ≅ G(Tot(K))`. Unlike `totalIso`, this
assumes no preservation of coproducts. -/
def totalIsoOfFinite
    (hfin : ∀ n, {pq : I₁ × I₂ | ComplexShape.π c₁ c₂ c₁₂ pq = n ∧
      ¬ IsZero ((K.X pq.1).X pq.2)}.Finite) :
    (mapBicomplex G K).total c₁₂ ≅ (G.mapHomologicalComplex c₁₂).obj (K.total c₁₂) :=
  totalIsoOfIsIso G K (fun n => isIso_totalMapf_of_finite G K n (hfin n))

/-- The forward direction of `totalIsoOfFinite` is `totalMap`. -/
theorem totalIsoOfFinite_hom_eq_totalMap
    (hfin : ∀ n, {pq : I₁ × I₂ | ComplexShape.π c₁ c₂ c₁₂ pq = n ∧
      ¬ IsZero ((K.X pq.1).X pq.2)}.Finite) :
    (totalIsoOfFinite (c₁₂ := c₁₂) G K hfin).hom = totalMap G K := rfl

end HomologicalComplex₂.TotalMap

end
