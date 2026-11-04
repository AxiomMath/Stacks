module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.JacobsonPoints.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.ResidueField

/-!
# Jacobson schemes and finite type points

For a scheme `S`, being Jacobson is equivalent to its finite type points being exactly its
closed points. It is also equivalent to closed points of every scheme locally of finite type
over `S` mapping to closed points of `S`, either with or without explicitly recording that the
induced residue field extension is finite.

## Main results

* `AlgebraicGeometry.jacobsonSpace_finiteTypePoints_tfae` gives the four equivalent
  characterizations.

## Implementation notes

The finiteness of the residue field extension uses the algebra structure induced by the
canonical residue field map. Closed points are expressed by closed singleton subsets.

## References

* [Stacks Project, Tag 01TB](https://stacks.math.columbia.edu/tag/01TB)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- A scheme is Jacobson exactly when its finite type points are its closed points; equivalently,
closed points under every locally finite type morphism to it have closed image, and the induced
residue field extensions are finite. -/
@[stacks 01TB, ega "IV 10.4.7" "(1) => (3)", ega "IV 10.9.2" "more general"]
public theorem jacobsonSpace_finiteTypePoints_tfae (S : Scheme.{u}) :
    List.TFAE [
      JacobsonSpace S,
      S.finiteTypePoints = {s | IsClosed ({s} : Set S)},
      ∀ (T : Scheme.{u}) (f : T ⟶ S) [LocallyOfFiniteType f] (t : T),
        IsClosed ({t} : Set T) → IsClosed ({f t} : Set S),
      ∀ (T : Scheme.{u}) (f : T ⟶ S) [LocallyOfFiniteType f] (t : T),
        IsClosed ({t} : Set T) → (
          IsClosed ({f t} : Set S) ∧
            letI := (f.residueFieldMap t).hom.toAlgebra
            Module.Finite (S.residueField (f t)) (T.residueField t))] := by
  tfae_have 1 → 4 := by
    intro _ T f _ t ht
    have hclosedFiber : IsClosed ({f.asFiber t} : Set (f.fiber (f t))) := by
      have hpre : (f.fiberι (f t)) ⁻¹' ({t} : Set T) = {f.asFiber t} := by
        ext z
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        exact (f.fiberι (f t)).isEmbedding.injective.eq_iff' (f.fiberι_asFiber t)
      rw [← hpre]
      exact ht.preimage (f.fiberι _).continuous
    exact ⟨mem_closedPoints_iff.mp (f.closePoints_subset_preimage_closedPoints
      (mem_closedPoints_iff.mpr ht)),
      (isClosed_asFiber_iff_finite_residueField f t).mp hclosedFiber⟩
  tfae_have 4 → 3 := by
    intro h T f _ t ht
    exact (h T f t ht).1
  tfae_have 3 → 2 := by
    refine fun h ↦ Set.ext fun x ↦ ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
    · change AlgebraicGeometry.IsFiniteTypePoint x at hx
      have : LocallyOfFiniteType (S.fromSpecResidueField x) := hx.1
      show IsClosed ({x} : Set S)
      simpa only [Scheme.fromSpecResidueField_apply x (IsLocalRing.closedPoint _)] using
        h (Spec (.of (S.residueField x))) (S.fromSpecResidueField x)
          (IsLocalRing.closedPoint (S.residueField x))
          (IsLocalRing.isClosed_singleton_closedPoint _)
    · obtain ⟨y, hy, hfin⟩ := inter_finiteTypePoints_nonempty hx.isLocallyClosed ⟨x, rfl⟩
      simpa only [Set.mem_singleton_iff.mp hy] using hfin
  tfae_have 2 → 1 := fun h ↦ ⟨by
    intro Z hZ
    show closure (Z ∩ {s | IsClosed ({s} : Set S)}) = Z
    rw [← h]
    exact closure_inter_finiteTypePoints (S := S) (T := Z) hZ⟩
  tfae_finish

end AlgebraicGeometry

end
