module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.IntegralMorphism
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkEquivalence.FieldFiber
public import StacksFrontier.AlgebraicGeometry.Variety.GeometricFieldChange.NoetherNormalization

/-!
# Reduction of cohomological dimension bounds to affine spaces

Let `K` be a field and `Y` an affine scheme of finite type over `K` of dimension `d`. By Noether
normalization (Stacks 0CBI) there is a finite morphism `Y ⟶ 𝔸^d_K`, and cohomological dimension
does not increase along an integral morphism, so `cd(Y) ≤ cd(𝔸^d_K)`. This is the step of the
proof of Stacks 0F0V that reduces the proposition to the affine spaces over `K`.

## Main results

* `AlgebraicGeometry.Scheme.etaleCohomologicalDimension_le_affineSpace`: `cd(Y) ≤ cd(𝔸^d_K)` for
  `Y` affine of finite type and of dimension `d` over `K`.
* `AlgebraicGeometry.Scheme.etaleCohomologicalDimension_le_of_isEmpty`: the empty scheme has
  cohomological dimension at most that of any field it lies over.

## References

* [Stacks Project, Tag 0F0V](https://stacks.math.columbia.edu/tag/0F0V)
* [Stacks Project, Tag 0CBI](https://stacks.math.columbia.edu/tag/0CBI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- Over a field, the fiber inclusion of any morphism at any point is an isomorphism. -/
private theorem isIso_fiberι_of_field {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (s : Spec (.of K)) : IsIso (f.fiberι s) :=
  have := isIso_fromSpecResidueField_of_field K s
  inferInstanceAs (IsIso (pullback.fst f ((Spec (.of K)).fromSpecResidueField s)))

/-- **Noether normalization bounds cohomological dimension by that of an affine space.** For an
affine scheme `Y` of finite type over a field `K` with `dim Y = d`, there is a finite morphism
`Y ⟶ 𝔸^d_K` (Stacks 0CBI), hence `cd(Y) ≤ cd(𝔸^d_K)`. -/
public theorem etaleCohomologicalDimension_le_affineSpace {K : Type u} [Field K] {Y : Scheme.{u}}
    [IsAffine Y] (g : Y ⟶ Spec (.of K)) [LocallyOfFiniteType g] (d : ℕ)
    (hd : topologicalKrullDim Y = d) :
    etaleCohomologicalDimension Y ≤ etaleCohomologicalDimension 𝔸(ULift (Fin d); Spec (.of K)) := by
  let s : Spec (.of K) := IsLocalRing.closedPoint K
  have := isIso_fiberι_of_field g s
  have := isIso_fiberι_of_field (𝔸(ULift (Fin d); Spec (.of K)) ↘ Spec (.of K)) s
  have hfib : topologicalKrullDim (g.fiber s) = d := by
    rw [← hd]
    exact IsHomeomorph.topologicalKrullDim_eq _
      (Scheme.homeoOfIso (asIso (g.fiberι s))).isHomeomorph
  obtain ⟨π, -, πs, hπs, -, hfin⟩ := exists_factorization_finite_fiber g s d hfib
  have hπ : π =
      inv (g.fiberι s) ≫ πs ≫ (𝔸(ULift (Fin d); Spec (.of K)) ↘ Spec (.of K)).fiberι s := by
    rw [hπs, IsIso.inv_hom_id_assoc]
  have : IsFinite π := hπ ▸ inferInstance
  exact etaleCohomologicalDimension_le_of_isIntegralHom π

/-- **The empty scheme.** An empty scheme over a field `K` has cohomological dimension at most
`cd(K)`: the structure morphism is a closed immersion, hence integral. -/
public theorem etaleCohomologicalDimension_le_of_isEmpty {K : Type u} [Field K] {Y : Scheme.{u}}
    [IsEmpty Y] (g : Y ⟶ Spec (.of K)) [CompactSpace Y] [QuasiSeparatedSpace Y] :
    etaleCohomologicalDimension Y ≤ etaleCohomologicalDimension (Spec (.of K)) :=
  etaleCohomologicalDimension_le_of_isIntegralHom g

end AlgebraicGeometry.Scheme

end
