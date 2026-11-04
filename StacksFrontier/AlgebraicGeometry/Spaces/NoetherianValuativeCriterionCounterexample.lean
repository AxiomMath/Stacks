module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianValuativeCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactAffineMorphism
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet

/-!
# The residue-field clause of Stacks 0CMC fails when the field-valued point lies over `y`

Stacks 0CMC asserts that, for a morphism `f : X ⟶ Y` of finite type of algebraic spaces with
`Y` locally Noetherian and a point `y` in the closure of the image of `|f|`, the diagram
`Spec K ⟶ X`, `Spec A ⟶ Y` with `A` a discrete valuation ring reaching `y` can be chosen with
`K` the residue field of a point of a scheme étale over `X`. This fails for the identity of
`Spec k` with `k` algebraically closed: every residue field of a scheme étale over `Spec k` is
algebraically closed, while the fraction field of a discrete valuation ring never is, since a
uniformizer has no square root in it.

## Main results

* `AlgebraicGeometry.isAlgClosed_residueField_of_etale`: the residue fields of a scheme étale
  over an algebraically closed field are algebraically closed.
* `IsDiscreteValuationRing.not_isAlgClosed_of_isFractionRing`: the fraction field of a discrete
  valuation ring is not algebraically closed.
* `AlgebraicGeometry.Space.not_forall_exists_etale_residueFieldEquiv`: in the situation of
  Stacks 0CMC, the fraction field of a discrete valuation ring with a field-valued point of `X`
  need not be isomorphic to any residue field of a scheme étale over `X`.
* `AlgebraicGeometry.Space.not_forall_exists_discreteValuationSpecialization_residueField`:
  the statement of Stacks 0CMC with the residue-field clause required unconditionally is false.

## References

* [Stacks Project, Tag 0CMC](https://stacks.math.columbia.edu/tag/0CMC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/-- **The fraction field of a discrete valuation ring is not algebraically closed.** A square
root of a uniformizer would be integral over the valuation ring, hence in it, and a uniformizer
is not a square of an element of the ring. -/
theorem IsDiscreteValuationRing.not_isAlgClosed_of_isFractionRing (A K : Type*) [CommRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [Field K] [Algebra A K] [IsFractionRing A K] :
    ¬ IsAlgClosed K := by
  intro hK
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap A K ϖ) two_pos
  obtain ⟨a, rfl⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (R := A)
    two_pos (hz ▸ isIntegral_algebraMap)
  rw [← map_pow, (IsFractionRing.injective A K).eq_iff] at hz
  rcases hϖ.isUnit_or_isUnit (by rw [← hz, sq]) with h | h <;>
    exact hϖ.not_isUnit (hz ▸ h.pow 2)

namespace AlgebraicGeometry

/-- **The residue fields of a scheme étale over an algebraically closed field are algebraically
closed.** The residue field extension at a point of an étale scheme over a field is separable,
hence algebraic, and an algebraically closed field has no proper algebraic extension. -/
theorem isAlgClosed_residueField_of_etale {k : Type u} [Field k] [IsAlgClosed k]
    {V : Scheme.{u}} (π : V ⟶ Spec (.of k)) [Etale π] (v : V) :
    IsAlgClosed (V.residueField v) := by
  have : (π.base v).asIdeal.IsPrime := (π.base v).isPrime
  have : IsAlgClosed ((Spec (.of k)).residueField (π.base v)) :=
    IsAlgClosed.of_ringEquiv k _
      ((Ideal.algEquivResidueFieldOfField (π.base v).asIdeal).toRingEquiv.trans
        (Scheme.Spec.residueFieldIso (.of k) (π.base v)).commRingCatIsoToRingEquiv.symm)
  let : Algebra ((Spec (.of k)).residueField (π.base v)) (V.residueField v) :=
    (π.residueFieldMap v).hom.toAlgebra
  exact IsAlgClosed.of_ringEquiv _ _
    (RingEquiv.ofBijective _ (IsAlgClosed.algebraMap_bijective_of_isIntegral
      (k := (Spec (.of k)).residueField (π.base v)) (K := V.residueField v)))

namespace Space

attribute [local instance] pointTopology

/-- **The residue-field clause of Stacks 0CMC fails, even read up to abstract isomorphism.**
It is not true that for every morphism `f : X ⟶ Y` of finite type of algebraic spaces over a
scheme `S`, with `Y` locally Noetherian, and every point `y` in the closure of the image of
`|f|`, there are a discrete valuation ring `A` and a field-valued point of `X` over its fraction
field `K` such that `K` is isomorphic to the residue field of a point of a scheme étale over `X`.

The counterexample is the identity of `X = Y = S = Spec k` for an algebraically closed field `k`:
a scheme étale over `Spec k` has algebraically closed residue fields
(`AlgebraicGeometry.isAlgClosed_residueField_of_etale`), while the fraction field of a discrete
valuation ring is never algebraically closed
(`IsDiscreteValuationRing.not_isAlgClosed_of_isFractionRing`). -/
theorem not_forall_exists_etale_residueFieldEquiv :
    ¬ ∀ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
        (X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f : X ⟶ Y), IsAlgebraicSpace B S hS X →
        IsAlgebraicSpace B S hS Y → IsFiniteType B S hS f →
        HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) →
        ∀ y : points B S hS Y, y ∈ closure (Set.range (pointsMap B S hS X f)) →
          ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : IsDiscreteValuationRing A)
            (K : FieldValuedPoint B S hS X) (_ : Algebra A K.carrier)
            (_ : IsFractionRing A K.carrier) (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X)
            (u : (BigFppfOver.toScheme B S hS).obj U),
            IsEtale B S hS a ∧
              Nonempty (K.carrier ≃+* ((BigFppfOver.toScheme B S hS).obj U).residueField u) := by
  intro h
  let k : Type u := AlgebraicClosure (ULift.{u} ℚ)
  obtain ⟨B, hS⟩ := BigFppfSite.exists_contains (Spec (.of k))
  let T : BigFppfOver B (Spec (.of k)) hS :=
    Over.mk (⟨𝟙 (Spec (.of k))⟩ : B.obj hS ⟶ B.obj hS)
  let X := yoneda.obj T
  have hft : IsFiniteType B (Spec (.of k)) hS (𝟙 X) := by
    have hlft := (isLocallyOfFiniteType_yoneda_map_iff B (Spec (.of k)) hS (𝟙 T)).2
      (by rw [CategoryTheory.Functor.map_id]; infer_instance)
    have hqc := isQuasiCompact_yoneda_map_of_isAffineHom B (Spec (.of k)) hS (𝟙 T)
      (by rw [CategoryTheory.Functor.map_id]; infer_instance)
    rw [yoneda.map_id] at hlft hqc
    exact ⟨hlft, hqc⟩
  have hnoeth : HasEtaleLocalProperty B (Spec (.of k)) hS X
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) :=
    hasEtaleLocalProperty_of_representable B (Spec (.of k)) hS _ _ T (Iso.refl _)
      (inferInstanceAs (IsLocallyNoetherian (Spec (.of k))))
  let y : FieldValuedPoint B (Spec (.of k)) hS X :=
    { carrier := k
      contained := hS
      toBase := 𝟙 _
      value := 𝟙 T }
  have hy : y.class B (Spec (.of k)) hS X ∈
      closure (Set.range (pointsMap B (Spec (.of k)) hS X (𝟙 X))) := by
    rw [pointsMap_id, Set.range_id]
    exact subset_closure (Set.mem_univ _)
  obtain ⟨A, _, _, _, K, _, _, U, a, u, ha, ⟨e⟩⟩ :=
    h B (Spec (.of k)) hS X X (𝟙 X) (isAlgebraicSpace_yoneda B _ hS T)
      (isAlgebraicSpace_yoneda B _ hS T) hft hnoeth _ hy
  obtain ⟨φ, rfl⟩ : ∃ φ : U ⟶ T, yoneda.map φ = a :=
    ⟨Yoneda.fullyFaithful.preimage a, Yoneda.fullyFaithful.map_preimage _⟩
  have hφ : Etale ((BigFppfOver.toScheme B (Spec (.of k)) hS).map φ) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B (Spec (.of k)) hS
      (@AlgebraicGeometry.Etale.{u}) φ).1 (presheaf_etale_of_isEtale B (Spec (.of k)) hS ha)
  have := isAlgClosed_residueField_of_etale (k := k)
    ((BigFppfOver.toScheme B (Spec (.of k)) hS).map φ) u
  exact IsDiscreteValuationRing.not_isAlgClosed_of_isFractionRing A K.carrier
    (IsAlgClosed.of_ringEquiv _ _ e.symm)

/-- **Stacks 0CMC with the residue-field clause required unconditionally is false.** It is not
true that for every morphism `f : X ⟶ Y` of finite type of algebraic spaces over a scheme `S`,
with `Y` locally Noetherian, and every point `y` in the closure of the image of `|f|`, there are
a discrete valuation ring `A` with fraction field `K`, a `K`-valued point of `X` and an
`A`-valued point of `Y` forming a commutative square with `f`, the closed point of `Spec A`
mapping to `y`, the point `x` of `X` given by `Spec K ⟶ X` of codimension zero, and the morphism
`Spec K ⟶ X` factoring as `Spec K ≅ Spec κ(u) ⟶ U ⟶ X` for a point `u` of a scheme `U` étale
over `X`. This is the conclusion of
`AlgebraicGeometry.Space.exists_discreteValuationSpecialization` with the residue-field clause
freed of its hypothesis `f x ≠ y`.

It already fails for the identity of `Spec k` with `k` algebraically closed, by
`AlgebraicGeometry.Space.not_forall_exists_etale_residueFieldEquiv`: the fraction field of a
discrete valuation ring is not algebraically closed, while every residue field of a scheme étale
over `Spec k` is. -/
theorem not_forall_exists_discreteValuationSpecialization_residueField :
    ¬ ∀ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
        (X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f : X ⟶ Y), IsAlgebraicSpace B S hS X →
        IsAlgebraicSpace B S hS Y → IsFiniteType B S hS f →
        HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) →
        ∀ y : points B S hS Y, y ∈ closure (Set.range (pointsMap B S hS X f)) →
          ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : IsDiscreteValuationRing A)
            (K : FieldValuedPoint B S hS X) (_ : Algebra A K.carrier)
            (_ : IsFractionRing A K.carrier) (A_contained : B.Contains (Spec (.of A)))
            (s : Spec (.of A) ⟶ S) (j : K.siteObject ⟶ valuationObject B S hS A A_contained s)
            (g : yoneda.obj (valuationObject B S hS A A_contained s) ⟶ Y),
            j.left.1 = Scheme.Spec.map (CommRingCat.ofHom (algebraMap A K.carrier)).op ∧
            yoneda.map j ≫ g = yonedaEquiv.symm K.value ≫ f ∧
            pointsMap B S hS (yoneda.obj (valuationObject B S hS A A_contained s)) g
                ((schemePointRepresentative B S hS (valuationObject B S hS A A_contained s)
                    (⟨IsLocalRing.maximalIdeal A, inferInstance⟩ : PrimeSpectrum A)).class B S hS
                  (yoneda.obj (valuationObject B S hS A A_contained s))) = y ∧
            localRingDimension B S hS (K.class B S hS X) = 0 ∧
            ∃ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X)
              (u : (BigFppfOver.toScheme B S hS).obj U)
              (e : K.carrier ≃+* ((BigFppfOver.toScheme B S hS).obj U).residueField u)
              (t : K.siteObject ⟶ U),
              IsEtale B S hS a ∧
                t.left.1 = Scheme.Spec.map (CommRingCat.ofHom e.symm.toRingHom).op ≫
                    ((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField u ∧
                  a.app (Opposite.op K.siteObject) t = K.value := by
  intro h
  refine not_forall_exists_etale_residueFieldEquiv fun B S hS X Y f hX hY hf hN y hy ↦ ?_
  obtain ⟨A, _, _, _, K, _, _, -, -, -, -, -, -, -, -, U, a, u, e, -, ha, -⟩ :=
    h B S hS X Y f hX hY hf hN y hy
  exact ⟨A, inferInstance, inferInstance, inferInstance, K, inferInstance, inferInstance, U, a, u,
    ha, ⟨e⟩⟩

end Space

end AlgebraicGeometry

end
