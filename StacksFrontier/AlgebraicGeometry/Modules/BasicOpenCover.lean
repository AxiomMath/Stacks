module

public import Mathlib.AlgebraicGeometry.StructureSheaf
public import StacksCore.RingTheory.Spectrum.Prime.Topology

/-!
# Module sections over a cover by standard opens

For a family of elements of a commutative ring, the complement of their common zero locus is
covered by the associated standard opens. The sheaf condition for the structure sheaf of a
module describes the sections on this open as the compatible families of sections on the
standard opens: restriction to the cover is injective, and a family of sections agreeing on
every pairwise intersection glues.

## Main definitions

* `AlgebraicGeometry.StructureSheaf.basicOpenCoverRestriction`: restriction of a section to
  every member of a cover by standard opens.
* `AlgebraicGeometry.StructureSheaf.basicOpenCoverDifference`: the difference of the two
  restriction maps to the pairwise intersections.

## Main results

* `AlgebraicGeometry.StructureSheaf.basicOpenCoverRestriction_injective`: restriction to the
  cover is injective.
* `AlgebraicGeometry.StructureSheaf.exact_basicOpenCoverRestriction_basicOpenCoverDifference`:
  the sections on the union are exactly the compatible families.

## Implementation notes

The union of the standard opens is the complement of the common zero locus by
`PrimeSpectrum.iUnion_basicOpen_eq_compl_zeroLocus`; the statements below are phrased for the
union itself, so that equality is not needed. Sections on `D(f)` serve as the abstract
localization of the module at `f`.

The pairwise intersection `D(f i) ⊓ D(f j)` is spelled `D(f i * f j)`, which is the form in
which the two restrictions arise; the identification is `PrimeSpectrum.basicOpen_mul`. For a
finite index type the products below are the finite direct sums displayed in the source.

## References

* [Stacks Project, Tag 01PM](https://stacks.math.columbia.edu/tag/01PM)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open PrimeSpectrum

universe u

namespace AlgebraicGeometry.StructureSheaf

variable {R : Type u} [CommRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]
variable {ι : Type u}

/-- Restrict a section on the union of a family of standard opens to every member of the
family. -/
public noncomputable def basicOpenCoverRestriction (f : ι → R) :
    ((structurePresheafInModuleCat R M).obj (op (⨆ i, basicOpen (f i)))) →ₗ[R]
      ((i : ι) → (structurePresheafInModuleCat R M).obj (op (basicOpen (f i)))) :=
  LinearMap.pi fun i ↦
    ((structurePresheafInModuleCat R M).map
      (homOfLE (le_iSup (fun i ↦ basicOpen (f i)) i)).op).hom

/-- The difference of the two restrictions of a family of sections on standard opens to each
pairwise intersection, written as `D(f i * f j)`. -/
public noncomputable def basicOpenCoverDifference (f : ι → R) :
    ((i : ι) → (structurePresheafInModuleCat R M).obj (op (basicOpen (f i)))) →ₗ[R]
      ((i : ι) → (j : ι) →
        (structurePresheafInModuleCat R M).obj (op (basicOpen (f i * f j)))) where
  toFun s i j :=
    (structurePresheafInModuleCat R M).map
        (homOfLE ((basicOpen_mul (f i) (f j)).le.trans inf_le_left)).op (s i) -
      (structurePresheafInModuleCat R M).map
        (homOfLE ((basicOpen_mul (f i) (f j)).le.trans inf_le_right)).op (s j)
  map_add' _ _ := by
    ext i j
    simp
    abel
  map_smul' _ _ := by
    ext i j
    simp only [homOfLE_leOfHom, Pi.smul_apply, map_smul, RingHom.id_apply]
    rw [smul_sub]

/-- A family of sections on standard opens killed by `basicOpenCoverDifference` is a compatible
family for the structure sheaf. -/
private lemma isCompatible_of_basicOpenCoverDifference_eq_zero (f : ι → R)
    (s : (i : ι) → (structurePresheafInModuleCat R M).obj (op (basicOpen (f i))))
    (hs : basicOpenCoverDifference (M := M) f s = 0) :
    TopCat.Presheaf.IsCompatible (structureSheafInType R M).1 (fun i ↦ basicOpen (f i)) s := by
  intro i j
  have hij := congrFun (congrFun hs i) j
  simp only [basicOpenCoverDifference, LinearMap.coe_mk, AddHom.coe_mk,
    Pi.zero_apply, sub_eq_zero] at hij
  change
    (structurePresheafInModuleCat R M).map
        (homOfLE (inf_le_left : basicOpen (f i) ⊓ basicOpen (f j) ≤ basicOpen (f i))).op
          (s i) =
      (structurePresheafInModuleCat R M).map
        (homOfLE (inf_le_right : basicOpen (f i) ⊓ basicOpen (f j) ≤ basicOpen (f j))).op
          (s j)
  have hij' := congrArg (fun x ↦
    (structurePresheafInModuleCat R M).map
      (eqToHom (basicOpen_mul (f i) (f j)).symm).op x) hij
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← ConcreteCategory.comp_apply, ← Functor.map_comp] at hij'
  convert hij' using 1

private lemma basicOpenCover_exact_and_injective (f : ι → R) :
    Function.Exact (basicOpenCoverRestriction (M := M) f)
        (basicOpenCoverDifference (M := M) f) ∧
      Function.Injective (basicOpenCoverRestriction (M := M) f) := by
  constructor
  · intro s
    constructor
    · intro hs
      obtain ⟨t, ht, -⟩ := (structureSheafInType R M).existsUnique_gluing
        (fun i ↦ basicOpen (f i)) s (isCompatible_of_basicOpenCoverDifference_eq_zero f s hs)
      exact ⟨t, funext ht⟩
    · rintro ⟨t, rfl⟩
      ext i j
      simp only [basicOpenCoverRestriction, basicOpenCoverDifference, LinearMap.coe_mk,
        AddHom.coe_mk, Pi.zero_apply]
      change
        (structurePresheafInModuleCat R M).map
            (homOfLE ((basicOpen_mul (f i) (f j)).le.trans inf_le_left)).op
            ((structurePresheafInModuleCat R M).map
              (homOfLE (le_iSup (fun i ↦ basicOpen (f i)) i)).op t) -
          (structurePresheafInModuleCat R M).map
            (homOfLE ((basicOpen_mul (f i) (f j)).le.trans inf_le_right)).op
            ((structurePresheafInModuleCat R M).map
              (homOfLE (le_iSup (fun i ↦ basicOpen (f i)) j)).op t) = 0
      rw [sub_eq_zero, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
        ← ConcreteCategory.comp_apply, ← Functor.map_comp]
      congr 1
  · intro s t h
    exact (structureSheafInType R M).eq_of_locally_eq _ _ _ fun i ↦ congrFun h i

/-- A section on a union of standard opens is determined by all of its restrictions. -/
public lemma basicOpenCoverRestriction_injective (f : ι → R) :
    Function.Injective (basicOpenCoverRestriction (M := M) f) :=
  (basicOpenCover_exact_and_injective (M := M) f).2

/-- The sections on a union of standard opens are exactly the families of sections on its
members whose two restrictions to every pairwise intersection agree. -/
public lemma exact_basicOpenCoverRestriction_basicOpenCoverDifference (f : ι → R) :
    Function.Exact (basicOpenCoverRestriction (M := M) f)
      (basicOpenCoverDifference (M := M) f) :=
  (basicOpenCover_exact_and_injective (M := M) f).1

end AlgebraicGeometry.StructureSheaf
