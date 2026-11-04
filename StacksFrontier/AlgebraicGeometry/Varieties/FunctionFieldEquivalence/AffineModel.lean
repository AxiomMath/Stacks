module

public import StacksFrontier.AlgebraicGeometry.Varieties.FunctionFieldEquivalence.FunctionField
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Affine models of finitely generated field extensions

A finitely generated field extension `K/k` contains a finite type `k`-subalgebra `A` with `K`
the fraction field of `A`. The spectrum of `A` is then a variety over `k` whose function field is
`K`; this realizes every finitely generated field extension of `k` as the function field of a
variety.

## Main definitions

* `AlgebraicGeometry.affineModelOfFieldExtension` — the variety `Spec A` attached to `K/k`.
* `AlgebraicGeometry.affineModelFunctionFieldAlgEquivOver` — its function field is `K`.
* `AlgebraicGeometry.affineModelFunctionFieldObjectIso` — the same statement in the category of
  finitely generated field extensions of `k`.

## References

* [Stacks Project, Tag 0BXN](https://stacks.math.columbia.edu/tag/0BXN)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- An affine model of a finitely generated field extension `K/k`: the spectrum of a finite type
`k`-subalgebra `A ⊆ K` with `K` the fraction field of `A`, which is a variety over `k`. -/
noncomputable def affineModelOfFieldExtension {k : Type u} [Field k]
    (K : FinitelyGeneratedFieldExtension k) : Variety k := by
  let L : Type u := K.1
  letI : Field L := K.2.1.toField
  letI : Algebra.EssFiniteType k L := K.2.2
  let A : Subalgebra k L := Algebra.EssFiniteType.subalgebra k L
  letI : Algebra.FiniteType k A := inferInstance
  letI : IsDomain A := inferInstance
  let f : Spec (.of A) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k A))
  have hLocallyOfFiniteType : LocallyOfFiniteType f := by
    let : Algebra (.of k : CommRingCat) (.of A : CommRingCat) := inferInstance
    let : Algebra.FiniteType (↑(.of k : CommRingCat)) (↑(.of A : CommRingCat)) :=
      inferInstance
    have h : LocallyOfFiniteType ((Spec (.of A)) ↘ (Spec (.of k))) := inferInstance
    rwa [specOverSpec_over] at h
  letI : IsVariety k f :=
    { toIsIntegral := inferInstance
      toIsSeparated := inferInstance
      toLocallyOfFiniteType := hLocallyOfFiniteType
      toQuasiCompact := inferInstance }
  exact ⟨Spec (.of A), f⟩

/-- The function field of the affine model `Spec A` of `K/k` is `K`, as an `A`-algebra: both are
localizations of the domain `A` at its nonzero divisors. -/
noncomputable def affineModelFunctionFieldAlgEquiv {k : Type u} [Field k]
    (K : FinitelyGeneratedFieldExtension k) :
    let L : Type u := K.1
    letI : Field L := K.2.1.toField
    letI : Algebra.EssFiniteType k L := K.2.2
    let A : Subalgebra k L := Algebra.EssFiniteType.subalgebra k L
    letI : IsDomain A := inferInstance
    let R : CommRingCat := .of A
    letI : IsDomain R := inferInstance
    letI : Algebra R L := (algebraMap A L).toAlgebra
    letI : Algebra R (Spec R).functionField :=
      RingHom.toAlgebra ((StructureSheaf.toStalk R (genericPoint (Spec R))).hom)
    (Spec R).functionField ≃ₐ[R] L := by
  let L : Type u := K.1
  letI : Algebra.EssFiniteType k L := K.2.2
  letI : Field L := K.2.1.toField
  let A : Subalgebra k L := Algebra.EssFiniteType.subalgebra k L
  letI : IsDomain A := inferInstance
  let R : CommRingCat := .of A
  letI : Algebra R L := (algebraMap A L).toAlgebra
  let M : Submonoid R := Algebra.EssFiniteType.submonoid k L
  have hM : M = nonZeroDivisors A := by
    ext x
    dsimp [M, Algebra.EssFiniteType.submonoid]
    change IsUnit (algebraMap A L x) ↔ x ∈ nonZeroDivisors A
    rw [isUnit_iff_ne_zero, mem_nonZeroDivisors_iff_ne_zero]
    exact map_ne_zero_iff (algebraMap A L) (fun x y h ↦ Subtype.ext h) (x := x)
  letI : IsLocalization M L := Algebra.EssFiniteType.isLocalization k L
  letI : IsDomain R := inferInstance
  have hMR : M = nonZeroDivisors R := hM
  letI : Algebra R (Spec R).functionField :=
    RingHom.toAlgebra ((StructureSheaf.toStalk R (genericPoint (Spec R))).hom)
  letI : IsFractionRing R (Spec R).functionField := functionField_isFractionRing_of_affine R
  letI : IsLocalization M (Spec R).functionField := by
    rw [hMR]
    exact functionField_isFractionRing_of_affine R
  exact IsLocalization.algEquiv M (Spec R).functionField L

/-- The `k`-algebra structure map of the function field of an affine model is the composition of
the inclusion `k → A` with the canonical map from `A` to the generic stalk of `Spec A`.

Unfolding the generic-point stalk maps for the affine model is more expensive than the default,
which is why this identification is isolated in its own lemma. -/
lemma affineModel_functionFieldAlgebraMap {k : Type u} [Field k]
    (K : FinitelyGeneratedFieldExtension k) :
    let L : Type u := K.1
    letI : Field L := K.2.1.toField
    letI : Algebra.EssFiniteType k L := K.2.2
    let A : Subalgebra k L := Algebra.EssFiniteType.subalgebra k L
    let X : Variety k := affineModelOfFieldExtension K
    functionFieldAlgebraMap X =
      (StructureSheaf.toStalk A (genericPoint (Spec (.of A)))).hom.comp
        (algebraMap k A) := by
  let L : Type u := K.1
  let : Field L := K.2.1.toField
  let : Algebra.EssFiniteType k L := K.2.2
  let A : Subalgebra k L := Algebra.EssFiniteType.subalgebra k L
  let X : Variety k := affineModelOfFieldExtension K
  let η := genericPoint X.toScheme
  let g : CommRingCat.of k ⟶ CommRingCat.of A := CommRingCat.ofHom (algebraMap k A)
  have hp : X.structureMap η = PrimeSpectrum.comap g.hom (genericPoint (Spec (.of A))) := rfl
  cases hp
  exact congrArg CommRingCat.Hom.hom (stalkMap_toStalk g (genericPoint (Spec (.of A))))

/-- The function field of the affine model of a finitely generated field extension `K/k` is `K`,
as a `k`-algebra.

The algebra equivalence unfolds the same function-field localization and its base algebra map
as `AlgebraicGeometry.affineModelFunctionFieldAlgEquiv`. -/
noncomputable def affineModelFunctionFieldAlgEquivOver {k : Type u} [Field k]
    (K : FinitelyGeneratedFieldExtension k) :
    let L : Type u := K.1
    letI : Field L := K.2.1.toField
    letI : Algebra.EssFiniteType k L := K.2.2
    (affineModelOfFieldExtension K).toScheme.functionField ≃ₐ[k] L := by
  let L : Type u := K.1
  letI : Field L := K.2.1.toField
  letI : Algebra.EssFiniteType k L := K.2.2
  let A : Subalgebra k L := Algebra.EssFiniteType.subalgebra k L
  let R : CommRingCat := .of A
  let X : Variety k := affineModelOfFieldExtension K
  letI : IsDomain A := inferInstance
  letI : IsDomain R := inferInstance
  letI : Algebra k R := RingHom.toAlgebra (algebraMap k A)
  letI : Algebra R L := (algebraMap A L).toAlgebra
  letI : Algebra R (Spec R).functionField :=
    RingHom.toAlgebra ((StructureSheaf.toStalk R (genericPoint (Spec R))).hom)
  letI : Algebra k (Spec R).functionField := varietyFunctionFieldAlgebra X
  let e : (Spec R).functionField ≃ₐ[R] L := affineModelFunctionFieldAlgEquiv K
  change (Spec R).functionField ≃ₐ[k] L
  have hsource : algebraMap k (Spec R).functionField =
      (StructureSheaf.toStalk A (genericPoint (Spec R))).hom.comp (algebraMap k A) := by
    change functionFieldAlgebraMap X = _
    exact affineModel_functionFieldAlgebraMap K
  have htarget : algebraMap k L = (algebraMap A L).comp (algebraMap k A) := rfl
  refine AlgEquiv.ofRingEquiv (R := k) (f := e.toRingEquiv) fun a ↦ ?_
  rw [hsource, htarget]
  simp only [RingHom.comp_apply]
  exact e.commutes (algebraMap k A a)

/-- A finitely generated field extension of `k` is the function field of its affine model, as an
object of the category of finitely generated field extensions. -/
@[sga "7 I 6.3"]
noncomputable def affineModelFunctionFieldObjectIso {k : Type u} [Field k]
    (K : FinitelyGeneratedFieldExtension k) :
    functionFieldObject (affineModelOfFieldExtension K) ≅ K :=
  ObjectProperty.isoMk
    (fun A : CommAlgCat k ↦ IsField A ∧ Algebra.EssFiniteType k A)
    (CommAlgCat.isoMk (affineModelFunctionFieldAlgEquivOver K))

end AlgebraicGeometry

end
