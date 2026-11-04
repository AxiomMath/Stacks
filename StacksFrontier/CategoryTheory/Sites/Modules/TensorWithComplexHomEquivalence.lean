module

public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedEquivalenceQuasicoherent
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexHomComparison
public import StacksFrontier.CategoryTheory.Triangulated.WeakGeneratorNatTransIso

/-!
# Two endomorphism algebras of generators, and the bimodule `Hom(L, K)` between them

Let `(C, O)` be a ringed site over a base ring `R` and let `𝒬` be a strictly full triangulated
subcategory of `D(O)` closed under direct sums. Let `K` and `L` be K-injective complexes of
`O`-modules lying in `𝒬`, compact relative to `𝒬` and generating `𝒬`, and let `A = Hom^•(K, K)`
and `B = Hom^•(L, L)` be their endomorphism differential graded `R`-algebras. By
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedEquivalenceOver` both
`- ⊗_A^𝐋 K : D(A, d) ⥤ 𝒬` and `- ⊗_B^𝐋 L : D(B, d) ⥤ 𝒬` are equivalences, so there is an
equivalence `D(A, d) ⥤ 𝒬 ⥤ D(B, d)`. This file proves that this equivalence is the derived tensor
product with the differential graded `(A, B)`-bimodule `Hom^•(L, K)` of
`AlgebraicGeometry.RingedSite.complexHomBimodule`.

## Main definitions

* `AlgebraicGeometry.RingedSite.IsRelativelyCompactGenerator`: a complex lying in `𝒬`, whose
  shifts are compact relative to `𝒬`, and which generates `𝒬`.
* `AlgebraicGeometry.RingedSite.IsRelativelyCompactGenerator.equivalence`: the equivalence
  `- ⊗_A^𝐋 K : D(A, d) ≌ 𝒬`.

## Main results

* `AlgebraicGeometry.RingedSite.derivedHomWithComplexOverRestrictIso`: on `𝒬`, `RHom(L, -)` is
  the quasi-inverse of `- ⊗_B^𝐋 L`.
* `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedCompDerivedHomIso`:
  `RHom(L, - ⊗_A^𝐋 K)` is the functor of the equivalence `D(A, d) ⥤ 𝒬 ⥤ D(B, d)`.
* `AlgebraicGeometry.RingedSite.isIso_tensorHomDGComparisonDerived`: the comparison
  `M ⊗_A^𝐋 Φ(A) ⟶ RHom(L, M ⊗_A^𝐋 K)` is invertible.
* `AlgebraicGeometry.RingedSite.derivedTensorComplexHomBimoduleIso`:
  `- ⊗_A^𝐋 Hom^•(L, K) ≅ RHom(L, - ⊗_A^𝐋 K)`.
* `AlgebraicGeometry.RingedSite.derivedTensorComplexHomBimoduleIsoEquivalence`: the functor of
  the equivalence `D(A, d) ⥤ 𝒬 ⥤ D(B, d)` is `- ⊗_A^𝐋 Hom^•(L, K)`.

## References

* [Stacks Project, Tag 0DK9](https://stacks.math.columbia.edu/tag/0DK9)
* [Stacks Project, Tag 09MC](https://stacks.math.columbia.edu/tag/09MC)
* [Stacks Project, Tag 09ST](https://stacks.math.columbia.edu/tag/09ST)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open DifferentialGradedModule

universe u v w t s

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory

variable (X : AlgebraicGeometry.RingedSite.{u, v, w})
  (R : Type (max u v w t s)) [CommRing R] [Linear R (TensorModO.{u, v, w, t, s} X)]
  [ScalarSections.{u, v, w, t, s, max u v w t s} X R]
  (𝒬 : ObjectProperty (DerivedCategory (TensorModO.{u, v, w, t, s} X)))

/-- A complex `K` of `O`-modules is a relatively compact generator of a subcategory `𝒬` of
`D(O)` closed under direct sums if it lies in `𝒬`, its shifts are compact relative to `𝒬`, and it
generates `𝒬`. -/
structure IsRelativelyCompactGenerator (K : CochainComplex (ModO.{u, v, w, t} X) ℤ) : Prop where
  /-- `𝒬` is closed under direct sums taken in `D(O)`. -/
  coprod : ∀ {ι : Type (max u v w t s)} (Z : ι → DerivedCategory (TensorModO.{u, v, w, t, s} X))
    (c : Cofan Z), IsColimit c → (∀ i, 𝒬 (Z i)) → 𝒬 c.pt
  /-- `K` lies in `𝒬`. -/
  mem : 𝒬 (DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K))
  /-- The shifts of `K` are compact relative to `𝒬`. -/
  compact : IsRelativelyCompactShifts.{u, v, w, t, s} X K 𝒬
  /-- `K` generates `𝒬`. -/
  generates : ∀ L : DerivedCategory (TensorModO.{u, v, w, t, s} X), 𝒬 L →
    (∀ (n : ℤ) (f : (DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K))⟦n⟧ ⟶ L), f = 0) →
      IsZero L

variable {X 𝒬} [𝒬.IsClosedUnderIsomorphisms] [𝒬.IsTriangulated]

/-- The equivalence `- ⊗_E^𝐋 K : D(E, d) ≌ 𝒬` for a K-injective relatively compact generator `K`
of `𝒬`, `E = Hom^•(K, K)` over `R`. -/
abbrev IsRelativelyCompactGenerator.equivalence {K : CochainComplex (ModO.{u, v, w, t} X) ℤ}
    [(liftComplex.{u, v, w, t, s} X K).IsKInjective]
    (hK : IsRelativelyCompactGenerator.{u, v, w, t, s} X 𝒬 K)
    (R : Type (max u v w t s)) [CommRing R] [Linear R (TensorModO.{u, v, w, t, s} X)]
    [ScalarSections.{u, v, w, t, s, max u v w t s} X R] :
    DifferentialGradedModule.derivedCategory.{max u v w t s, max u v w t s, max u v w t s}
      (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra ≌ 𝒬.FullSubcategory :=
  tensorWithComplexDerivedEquivalenceOver.{u, v, w, t, s} X R K 𝒬 hK.coprod hK.mem hK.compact
    hK.generates

variable {L : CochainComplex (ModO.{u, v, w, t} X) ℤ}
  [(liftComplex.{u, v, w, t, s} X L).IsKInjective]
  (hL : IsRelativelyCompactGenerator.{u, v, w, t, s} X 𝒬 L)

/-- On `𝒬`, `RHom(L, -)` is the quasi-inverse of `- ⊗_B^𝐋 L : D(B, d) ≌ 𝒬`. -/
def derivedHomWithComplexOverRestrictIso :
    𝒬.ι ⋙ derivedHomWithComplexOver.{u, v, w, t, s, max u v w t s} X R L ≅
      (hL.equivalence R).inverse :=
  Adjunction.rightAdjointUniq
    ((tensorWithComplexDerived_adj_derivedHomWithComplexOver.{u, v, w, t, s, max u v w t s}
      X R L).restrictFullyFaithful (Functor.FullyFaithful.id _) 𝒬.fullyFaithfulι
      (Functor.leftUnitor _) (Functor.rightUnitor _).symm)
    (hL.equivalence R).toAdjunction

variable {K : CochainComplex (ModO.{u, v, w, t} X) ℤ}
  [(liftComplex.{u, v, w, t, s} X K).IsKInjective]
  (hK : IsRelativelyCompactGenerator.{u, v, w, t, s} X 𝒬 K)

/-- `RHom(L, - ⊗_A^𝐋 K)` is the functor of the equivalence `D(A, d) ⥤ 𝒬 ⥤ D(B, d)`. -/
def tensorWithComplexDerivedCompDerivedHomIso :
    tensorWithComplexDerived.{u, v, w, t, s, max u v w t s} X R K ⋙
        derivedHomWithComplexOver.{u, v, w, t, s, max u v w t s} X R L ≅
      ((hK.equivalence R).trans (hL.equivalence R).symm).functor :=
  Functor.associator (hK.equivalence R).functor 𝒬.ι
      (derivedHomWithComplexOver.{u, v, w, t, s, max u v w t s} X R L) ≪≫
    Functor.isoWhiskerLeft (hK.equivalence R).functor (derivedHomWithComplexOverRestrictIso R hL)

include hL hK in
/-- For K-injective relatively compact generators `K` and `L` of `𝒬`, the comparison
`M ⊗_A^𝐋 Φ(A) ⟶ RHom(L, M ⊗_A^𝐋 K)`, with `Φ(A) = Hom(L, A ⊗_A K)`, is invertible. -/
theorem isIso_tensorHomDGComparisonDerived :
    IsIso (tensorHomDGComparisonDerived.{u, v, w, t, s} X R K L) := by
  refine (Stacks.AlgebraicGeometry.ProjectiveGenerator.isWeakTriangulatedGenerator_q_regularModule.{
      max u v w t s, max u v w t s} (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra
    ).isIso_of_isIso_app_of_adjunction
    (DifferentialGraded.Bimodule.derivedTensorFunctor_adj_derivedHomFunctor _)
    (((hK.equivalence R).trans (hL.equivalence R).symm).toAdjunction.ofNatIsoLeft
      (tensorWithComplexDerivedCompDerivedHomIso R hL hK).symm) _ ?_
  rintro M ⟨M₀, n, e, hM₀⟩
  rw [ObjectProperty.singleton_iff] at hM₀
  subst hM₀
  exact (NatTrans.isIso_app_iff_of_iso _
    (e ≪≫ repRegularDerivedOverShiftIso.{u, v, w, t, s} X R K n)).2
    (isIso_tensorHomComparisonDerived_app_shift.{u, v, w, t, s} X R K L n)

/-- `- ⊗_A^𝐋 Hom^•(L, K) ≅ RHom(L, - ⊗_A^𝐋 K)`, for `K` and `L` K-injective relatively compact
generators of `𝒬`. -/
def derivedTensorComplexHomBimoduleIso :
    DifferentialGraded.Bimodule.derivedTensorFunctor
        (complexHomBimodule.{u, v, w, t, s} X R K L) ≅
      tensorWithComplexDerived.{u, v, w, t, s, max u v w t s} X R K ⋙
        derivedHomWithComplexOver.{u, v, w, t, s, max u v w t s} X R L :=
  have := isIso_tensorHomDGComparisonDerived R hL hK
  { hom := DifferentialGraded.Bimodule.derivedTensorNatTrans
        (complexHomBimoduleIsoRegular.{u, v, w, t, s} X R K L).hom ≫
      tensorHomDGComparisonDerived.{u, v, w, t, s} X R K L
    inv := inv (tensorHomDGComparisonDerived.{u, v, w, t, s} X R K L) ≫
      DifferentialGraded.Bimodule.derivedTensorNatTrans
        (complexHomBimoduleIsoRegular.{u, v, w, t, s} X R K L).inv
    hom_inv_id := by
      rw [Category.assoc, IsIso.hom_inv_id_assoc,
        ← DifferentialGraded.Bimodule.derivedTensorNatTrans_comp, Iso.hom_inv_id,
        DifferentialGraded.Bimodule.derivedTensorNatTrans_id]
    inv_hom_id := by
      rw [Category.assoc, ← Category.assoc (DifferentialGraded.Bimodule.derivedTensorNatTrans _),
        ← DifferentialGraded.Bimodule.derivedTensorNatTrans_comp, Iso.inv_hom_id,
        DifferentialGraded.Bimodule.derivedTensorNatTrans_id, Category.id_comp,
        IsIso.inv_hom_id] }

/-- The equivalence `D(A, d) ⥤ 𝒬 ⥤ D(B, d)` is `- ⊗_A^𝐋 Hom^•(L, K)`. -/
def derivedTensorComplexHomBimoduleIsoEquivalence :
    DifferentialGraded.Bimodule.derivedTensorFunctor
        (complexHomBimodule.{u, v, w, t, s} X R K L) ≅
      ((hK.equivalence R).trans (hL.equivalence R).symm).functor :=
  derivedTensorComplexHomBimoduleIso R hL hK ≪≫ tensorWithComplexDerivedCompDerivedHomIso R hL hK

end AlgebraicGeometry.RingedSite
