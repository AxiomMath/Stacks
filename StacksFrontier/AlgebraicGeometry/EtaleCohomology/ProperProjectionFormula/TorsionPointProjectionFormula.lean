module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperProjectionFormula.TorsionPointEquivalence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProjectionFormulaConstant.Devissage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedTensorHom.DerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedTensorHom.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperDirectImageDirectSums
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormulaOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Coproducts

/-!
# The projection formula for a proper scheme over a separably closed field, torsion coefficients

Let `k` be a separably closed field, `π : X ⟶ Spec k` a proper morphism and `Λ` a torsion ring.
For `E ∈ D(X_étale, Λ̲)` and `K ∈ D(Spec(k)_étale, Λ̲)`, unbounded, the canonical map of
Cohomology on Sites, Section 21.50 ([Stacks, Tag 0B56]),

`Rπ_*E ⊗^L_Λ K ⟶ Rπ_*(E ⊗^L_Λ π^{-1}K)`,

is an isomorphism. This is the fibre case of the proof of [Stacks, Tag 0F0G]; through
`D(Spec(k)_étale, Λ̲) = D(Λ)` it is the computation of Lemma 63.95.6 for the proper `k`-scheme
`X`, whose cohomological dimension is finite by [Stacks, Tag 095U].

The proof is the source's dévissage (More on Algebra, Remark 15.60.11, [Stacks, Tag 09PB]),
`Stacks.EtaleCohomology.ProjectionFormulaConstant.isIso_app_of_coproducts_of_unitShifts`, run on
`D(Spec(k)_étale, Λ̲)` through the equivalence
`Stacks.EtaleCohomology.etalePointDerivedEquivalence` with `D(Λ)`:

1. both sides commute with direct sums: the derived tensor products in the second variable,
   `π^{-1}` as a left adjoint, and `Rπ_*` by [Stacks, Tag 0F11] (1), whose inputs are the
   vanishing of `R^qπ_*` above twice the fibre dimension for torsion sheaves ([Stacks, Tag 095U]
   with [Stacks, Tag 0A3V]) and the commuting of each `R^qπ_*` with direct sums;
2. both sides are exact functors of `K`;
3. the map is invertible at every shift of `Λ̲[0]`, which is the image of `Λ[0]`
   (`Stacks.EtaleCohomology.etalePointDerivedUnitIso`), by
   `Stacks.Cohomology.ProjectionFormulaOfToposHom.isIso_projectionFormulaMap_unitShift`.

## Main results

* `Stacks.EtaleCohomology.preservesColimitsOfShape_etaleRingedDerivedPushforward_of_isProper`: for
  `f` proper and `Λ` torsion, the unbounded `Rf_*` of the constant ringed topoi commutes with
  direct sums ([Stacks, Tag 0F0D] for a torsion ring, read through
  `Stacks.EtaleCohomology.etaleDerivedEquivalence`).
* `Stacks.EtaleCohomology.isIso_projectionFormulaMap_of_preservesCoproducts_of_isSepClosed`: the
  projection formula map along a morphism to the spectrum of a separably closed field is
  invertible as soon as the derived direct image commutes with direct sums.
* `Stacks.EtaleCohomology.isIso_projectionFormulaMap_of_isProper_of_isSepClosed`: the projection
  formula map along a proper morphism to the spectrum of a separably closed field is invertible,
  for a torsion ring of coefficients.

## References

* [Stacks Project, Tag 0F0G](https://stacks.math.columbia.edu/tag/0F0G)
* [Stacks Project, Tag 09PB](https://stacks.math.columbia.edu/tag/09PB)
* [Stacks Project, Tag 0F11](https://stacks.math.columbia.edu/tag/0F11)
* [Stacks Project, Tag 095U](https://stacks.math.columbia.edu/tag/095U)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPushforward
open Stacks.Cohomology.ProjectionFormulaOfToposHom
open Stacks.DerivedTensor.RingedSite

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [CommRing Λ]

/-- A torsion ring is killed by a positive integer: the additive order of `1`. -/
theorem exists_natCast_eq_zero_of_isTorsion (hΛ : IsAddTorsion Λ) :
    ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0 :=
  ⟨addOrderOf (1 : Λ), (hΛ 1).addOrderOf_pos, by
    rw [← nsmul_one]; exact addOrderOf_nsmul_eq_zero 1⟩

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The unbounded derived direct image along the morphism of constant ringed topoi
`(X_étale, Λ̲) ⟶ (Y_étale, Λ̲)` commutes with the direct sums with which the étale one commutes**:
it is the étale one read through `Stacks.EtaleCohomology.etaleDerivedEquivalence`. -/
theorem preservesColimitsOfShape_etaleRingedDerivedPushforward_of_etaleModule (J : Type*)
    [Category* J]
    [PreservesColimitsOfShape J (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f)] :
    PreservesColimitsOfShape J (etaleRingedDerivedPushforward.{u, r} Λ f) := by
  let e : (etaleDerivedEquivalence.{u, r} Λ X).inverse ⋙
      etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f ⋙
        (etaleDerivedEquivalence.{u, r} Λ Y).functor ≅
      etaleRingedDerivedPushforward.{u, r} Λ f :=
    Functor.isoWhiskerLeft _ (etaleDerivedPushforwardIso.{u, r} Λ f) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (etaleDerivedEquivalence.{u, r} Λ X).counitIso _ ≪≫
      Functor.leftUnitor _
  exact preservesColimitsOfShape_of_natIso e

/-- **For `f` proper and `Λ` torsion, the unbounded derived direct
image along the morphism of constant ringed topoi `(X_étale, Λ̲) ⟶ (Y_étale, Λ̲)` commutes with
direct sums**: it is the étale one read through `Stacks.EtaleCohomology.etaleDerivedEquivalence`.
-/
theorem preservesColimitsOfShape_etaleRingedDerivedPushforward_of_isProper
    [IsProper f] (hΛ : IsAddTorsion Λ) (I : Type (max (u + 1) r)) :
    PreservesColimitsOfShape (Discrete I) (etaleRingedDerivedPushforward.{u, r} Λ f) := by
  have := preservesColimitsOfShape_etaleModuleDerivedDirectImageUnbounded_of_isProper Λ f
    (exists_natCast_eq_zero_of_isTorsion Λ hΛ) I
  exact preservesColimitsOfShape_etaleRingedDerivedPushforward_of_etaleModule Λ f _

/-- **The projection formula along a morphism to the spectrum of a separably closed field whose
derived direct image commutes with direct sums.** Let `k` be a separably closed field and
`π : X ⟶ Spec k` a morphism such that the unbounded `Rπ_*` along the morphism of constant ringed
topoi of `π` commutes with direct sums. For every `E ∈ D(X_étale, Λ̲)` and every
`K ∈ D(Spec(k)_étale, Λ̲)`, unbounded, the map of [Stacks, Tag 0B56]
`Rπ_*E ⊗^L_Λ K ⟶ Rπ_*(E ⊗^L_Λ π^{-1}K)` is an isomorphism. This is the dévissage of the proof of
[Stacks, Tag 0F12] (More on Algebra, Remark 15.60.11, [Stacks, Tag 09PB]); the commuting of `Rπ_*`
with direct sums is where finiteness of the cohomological dimension enters. -/
theorem isIso_projectionFormulaMap_of_preservesCoproducts_of_isSepClosed
    (k : Type u) [Field k] [IsSepClosed k] (π : X ⟶ Spec (.of k))
    (hπ : ∀ I : Type (max (u + 1) r),
      PreservesColimitsOfShape (Discrete I) (etaleRingedDerivedPushforward.{u, r} Λ π))
    (E : DerivedCategory (EtaleRingedModules.{u, r} Λ X))
    (K : DerivedCategory (EtaleRingedModules.{u, r} Λ (Spec (.of k)))) :
    IsIso (projectionFormulaMap (etaleRingedToposHom.{u, r} Λ π) E K) := by
  let f := etaleRingedToposHom.{u, r} Λ π
  let := HasDerivedCategory.standard (EtaleRingedModules.{u, r} Λ X)
  let := HasDerivedCategory.standard (EtaleRingedModules.{u, r} Λ (Spec (.of k)))
  let := HasDerivedCategory.standard (ModuleCat.{max (u + 1) r} Λ)
  let A := RingedSite.ringedTopos.{max (u + 1) r, max (u + 1) r, max (u + 1) r}
    (etaleRingedSite.{u, r} Λ X)
  let B := RingedSite.ringedTopos.{max (u + 1) r, max (u + 1) r, max (u + 1) r}
    (etaleRingedSite.{u, r} Λ (Spec (.of k)))
  let adj := derivedAdjunction (X := A) (Y := B) f
  let P := derivedPushforward (X := A) (Y := B) f
  have := hasLeftDerivedFunctor_pullbackOnHomotopy.{max (u + 1) r, max (u + 1) r, max (u + 1) r,
    max (u + 1) r, max (u + 1) r, max (u + 1) r} f
  let Q := derivedPullback (X := A) (Y := B) f
  let _ : Q.CommShift ℤ := derivedPullback_commShift f
  let _ : Q.IsTriangulated := derivedPullback_isTriangulated f
  let _ : P.CommShift ℤ := adj.rightAdjointCommShift ℤ
  let _ : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  let _ : P.IsTriangulated := adj.isTriangulated_rightAdjoint
  let _ : ((derivedTensorProductFunctor (etaleRingedSite.{u, r} Λ X).O).obj E).CommShift ℤ :=
    (canonicalDerivedTensorProduct (etaleRingedSite.{u, r} Λ X).O).commShift_right _
  let _ : ((derivedTensorProductFunctor (etaleRingedSite.{u, r} Λ X).O).obj E).IsTriangulated :=
    (canonicalDerivedTensorProduct (etaleRingedSite.{u, r} Λ X).O).exact_right _
  let _ : ((derivedTensorProductFunctor (etaleRingedSite.{u, r} Λ X).O).obj E ⋙
      P).CommShift ℤ := Functor.CommShift.comp _ _
  let _ : ((derivedTensorProductFunctor (etaleRingedSite.{u, r} Λ (Spec (.of k))).O).obj
      ((P).obj E)).CommShift ℤ :=
    (canonicalDerivedTensorProduct (etaleRingedSite.{u, r} Λ (Spec (.of k))).O).commShift_right _
  let _ : ((derivedTensorProductFunctor (etaleRingedSite.{u, r} Λ (Spec (.of k))).O).obj
      ((P).obj E)).IsTriangulated :=
    (canonicalDerivedTensorProduct (etaleRingedSite.{u, r} Λ (Spec (.of k))).O).exact_right _
  have hG : ∀ I : Type (max (u + 1) r), PreservesColimitsOfShape (Discrete I)
      (Q ⋙ (derivedTensorProductFunctor (etaleRingedSite.{u, r} Λ X).O).obj E ⋙
        P) := fun I => by
    have : PreservesColimitsOfShape (Discrete I) (Q) := by
      have := adj.leftAdjoint_preservesColimits
      infer_instance
    have : PreservesColimitsOfShape (Discrete I)
        ((derivedTensorProductFunctor (etaleRingedSite.{u, r} Λ X).O).obj E) :=
      -- `E` read in the model of the local instance above, the one this proof works in.
      preservesColimitsOfShape_discrete_derivedTensorProductFunctor _ I
        (show DerivedCategory (EtaleRingedModules.{u, r} Λ X) from E)
    have : PreservesColimitsOfShape (Discrete I) (P) := hπ I
    infer_instance
  have hF : ∀ I : Type (max (u + 1) r), PreservesColimitsOfShape (Discrete I)
      ((derivedTensorProductFunctor (etaleRingedSite.{u, r} Λ (Spec (.of k))).O).obj
        ((P).obj E)) :=
    fun I => preservesColimitsOfShape_discrete_derivedTensorProductFunctor _ I _
  have hΨ : ∀ I : Type (max (u + 1) r), PreservesColimitsOfShape (Discrete I)
      (etalePointDerived.{u, r} Λ k) := fun I => inferInstance
  exact ProjectionFormulaConstant.isIso_app_of_coproducts_of_unitShifts (R := Λ) _ _
    (projectionFormulaNatTrans f E) (etalePointDerived.{u, r} Λ k)
    (fun n => ((projectionFormulaNatTrans f E).isIso_app_iff_of_iso
      ((shiftFunctor _ n).mapIso (etalePointDerivedUnitIso.{u, r} Λ k))).2
        (isIso_projectionFormulaMap_unitShift f E n)) K

/-- **The projection formula along a proper morphism to the spectrum of a separably closed
field, for a torsion ring of coefficients.** Let `k` be a separably closed field,
`π : X ⟶ Spec k` a proper morphism and `Λ` a torsion ring. For every `E ∈ D(X_étale, Λ̲)` and
every `K ∈ D(Spec(k)_étale, Λ̲)`, unbounded, the map of [Stacks, Tag 0B56]
`Rπ_*E ⊗^L_Λ K ⟶ Rπ_*(E ⊗^L_Λ π^{-1}K)` along the morphism of constant ringed topoi of `π` is an
isomorphism. -/
theorem isIso_projectionFormulaMap_of_isProper_of_isSepClosed (hΛ : IsAddTorsion Λ)
    (k : Type u) [Field k] [IsSepClosed k] (π : X ⟶ Spec (.of k)) [IsProper π]
    (E : DerivedCategory (EtaleRingedModules.{u, r} Λ X))
    (K : DerivedCategory (EtaleRingedModules.{u, r} Λ (Spec (.of k)))) :
    IsIso (projectionFormulaMap (etaleRingedToposHom.{u, r} Λ π) E K) :=
  isIso_projectionFormulaMap_of_preservesCoproducts_of_isSepClosed Λ k π
    (preservesColimitsOfShape_etaleRingedDerivedPushforward_of_isProper Λ π hΛ) E K

end Stacks.EtaleCohomology

end
