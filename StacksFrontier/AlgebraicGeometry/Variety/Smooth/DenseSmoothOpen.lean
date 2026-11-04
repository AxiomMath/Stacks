module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.NoetherianSpace
public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreDimensionSpecialization
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Reduced
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ReducedGenericPoints
public import StacksFrontier.FieldTheory.Separable.TFAE
public import StacksFrontier.RingTheory.FormallySmooth.Field

/-!
# Geometrically reduced schemes and dense smooth opens

A reduced scheme locally of finite type over a field is geometrically reduced precisely when it
contains a dense open subscheme which is smooth over the field.

## Main results

* `AlgebraicGeometry.geometricallyReduced_iff_exists_dense_open_smooth`: geometric reducedness is
  characterized by the existence of a dense smooth open subscheme.

## Implementation notes

The structure morphism of the open subscheme associated to `U : X.Opens` is written as the
composite `U.ι ≫ f`, so the existential records the dense open subscheme itself rather than
merely its underlying set. The smooth open witnessing the forward direction is the smooth locus
of the structure morphism; the two directions meet at the generic points of the irreducible
components, where smoothness and geometric reducedness agree because the local ring there is a
field, and where a dense open of a locally Noetherian space is forced to contain every generic
point.

## References

* [Stacks Project, Tag 056V](https://stacks.math.columbia.edu/tag/056V)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- At a generic point of an irreducible component of a reduced scheme locally of finite type
over a field, membership of the smooth locus is equivalent to geometric reducedness. -/
@[sga "3 VIB 7.8" "partial"]
public lemma smoothLocus_iff_isGeometricallyReducedAt_genericPoint
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsReduced X] [LocallyOfFiniteType f] (x : X) (hx : x ∈ genericPoints X) :
    x ∈ f.smoothLocus ↔ IsGeometricallyReducedAt f x := by
  let A := X.presheaf.stalk x
  let : Field A :=
    (isField_stalk_of_closure_mem_irreducibleComponents X x hx).toField
  let R := (Spec.structureSheaf k).presheaf.stalk (f.base x)
  let : Algebra k R := StructureSheaf.stalkAlgebra k (f.base x)
  have : (f.base x).asIdeal.IsPrime := (f.base x).isPrime
  have : IsLocalization.AtPrime R (f.base x).asIdeal :=
    StructureSheaf.IsLocalization.to_stalk k (f.base x)
  let : Algebra k A := ((f.stalkMap x).hom.comp (algebraMap k R)).toAlgebra
  let e : k ≃ₐ[k] R := IsLocalization.atUnits k (f.base x).asIdeal.primeCompl
    (fun a ha ↦ by aesop (add simp IsUnit.mem_submonoid_iff))
  have : IsIso (CommRingCat.ofHom (algebraMap k R)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (by
      convert e.toRingEquiv.bijective using 1
      funext a
      exact (e.commutes a).symm)
  have hsm : (algebraMap k A).FormallySmooth ↔ Algebra.IsGeometricallyReduced k A := by
    rw [RingHom.formallySmooth_algebraMap,
      Algebra.FormallySmooth.iff_isSeparableExtension]
    exact (Algebra.isSeparableExtension_tfae k A (ringExpChar k)).out 1 4
  calc
    x ∈ f.smoothLocus ↔ (f.stalkMap x).hom.FormallySmooth :=
      Scheme.Hom.mem_smoothLocus
    _ ↔ ((f.stalkMap x).hom.comp (algebraMap k R)).FormallySmooth :=
      (RingHom.FormallySmooth.respectsIso.cancel_left_isIso
        (CommRingCat.ofHom (algebraMap k R)) (f.stalkMap x)).symm
    _ ↔ Algebra.IsGeometricallyReduced k A := hsm
    _ ↔ IsGeometricallyReducedAt f x :=
      (isGeometricallyReducedAt_iff_isGeometricallyReduced_stalk f x).symm

/-- A reduced scheme locally of finite type over a field is geometrically reduced if and only if
it contains a dense open subscheme smooth over that field. -/
@[stacks 056V, ega "IV 17.15.12" "X reduced, 1st equiv"]
public theorem geometricallyReduced_iff_exists_dense_open_smooth
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsReduced X] [LocallyOfFiniteType f] :
    GeometricallyReduced f ↔
      ∃ U : X.Opens, Dense (U : Set X) ∧ Smooth (U.ι ≫ f) := by
  constructor
  · intro hgeom
    refine ⟨f.smoothLocus, ?_, ?_⟩
    · exact (dense_iff_closure_eq.mpr genericPoints.closure).mono fun x hx ↦
        (smoothLocus_iff_isGeometricallyReducedAt_genericPoint f x hx).2
          ((geometricallyReduced_iff_forall_isGeometricallyReducedAt f).mp hgeom x)
    · apply Scheme.Hom.smoothLocus_eq_top_iff.mp
      rw [← Scheme.Hom.preimage_smoothLocus_eq f.smoothLocus.ι f]
      simp
  · rintro ⟨U, hUdense, hUsmooth⟩
    have hUsub : (U : Set X) ⊆ f.smoothLocus := by
      intro x hx
      have hx' : (⟨x, hx⟩ : U) ∈ (U.ι ≫ f).smoothLocus := by
        rw [(Scheme.Hom.smoothLocus_eq_top_iff).2 hUsmooth]
        trivial
      rwa [← Scheme.Hom.preimage_smoothLocus_eq] at hx'
    have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    exact geometricallyReduced_of_isGeometricallyReducedAt_genericPoints f fun x hx ↦
      (smoothLocus_iff_isGeometricallyReducedAt_genericPoint f x hx).1
        (scheme_genericPoints_mem_dense_open X f.smoothLocus.2 (hUdense.mono hUsub) hx)

end AlgebraicGeometry

end
