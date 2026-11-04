module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.FieldTheory.IsSepClosed
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.GeometricallyIrreducible.Criteria

/-!
# Irreducibility over a separably closed field

An irreducible scheme over a separably closed field remains irreducible after every field
extension of the base, and the base-change projection is a bijection on irreducible components.

## Main results

* `AlgebraicGeometry.geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed` says that an
  irreducible scheme over a separably closed field is geometrically irreducible.
* `AlgebraicGeometry.bijOn_irreducibleComponents_baseChange_of_isSepClosed` says that taking
  images along the base-change projection is a bijection on irreducible components.

## Implementation notes

The structure morphism is retained explicitly. Geometric irreducibility is expressed by
`AlgebraicGeometry.GeometricallyIrreducible`; by definition, this asserts irreducibility after
base change by every spectrum of a field over the base. The base change `X_{k'}` is represented
by the categorical pullback of the structure morphism `X ⟶ Spec k` along `Spec k' ⟶ Spec k`, and
the induced map on components is made explicit as taking direct images along the underlying
continuous map of the first pullback projection.

## References

* [Stacks Project, Tag 020J](https://stacks.math.columbia.edu/tag/020J)
* [Stacks Project, Tag 038H](https://stacks.math.columbia.edu/tag/038H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CommRingCat

namespace AlgebraicGeometry

universe u

/-- A field extension of a separably closed field is geometrically irreducible. -/
private theorem isGeometricallyIrreducible_of_isSepClosed
    (k K : Type u) [Field k] [IsSepClosed k] [Field K] [Algebra k K] :
    Algebra.IsGeometricallyIrreducible k K :=
  (Algebra.isGeometricallyIrreducible_iff_irreducibleSpace_primeSpectrum k K).mpr inferInstance

/-- **Stacks Project, Tag 020J.** An irreducible scheme over a separably closed field is
geometrically irreducible. -/
@[stacks 020J, ega "IV 4.4.4" "more general", ega "IV 4.5.9" "(b) ⇒ (a), special case"]
public theorem geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed
    (k : Type u) [Field k] [IsSepClosed k] (X : Scheme.{u})
    (f : X ⟶ Spec (.of k)) [IrreducibleSpace X] : GeometricallyIrreducible f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ g ↦ ?_⟩
  let : Algebra k K := (Spec.fullyFaithful.preimage g).unop.hom.toAlgebra
  have := isGeometricallyIrreducible_of_isSepClosed k K
  rw [← show Spec.map (CommRingCat.ofHom (algebraMap k K)) = g from by
    simp [RingHom.algebraMap_toAlgebra]]
  infer_instance

/-- **Stacks Project, Tag 038H.** If `k` is separably algebraically closed, `k' / k` is a field
extension, and `X` is a scheme over `k`, then the projection `X_{k'} ⟶ X` induces a bijection
on irreducible components. -/
@[stacks 038H,
  sga "3 VIA 2.6.0" "k sep. alg. closed",
  ega "IV 4.5.19" "partial, special case",
  ega "IV 4.5.21" "more general",
  ega "IV 4.5.6" "(i), special case"]
public theorem bijOn_irreducibleComponents_baseChange_of_isSepClosed
    (k k' : Type u) [Field k] [IsSepClosed k] [Field k'] [Algebra k k']
    (X : Scheme.{u}) (f : X ⟶ Spec (of k)) :
    Set.BijOn
      (fun Z ↦
        (pullback.fst (C := Scheme.{u}) f (Spec.map (ofHom (algebraMap k k')))).base '' Z)
      (irreducibleComponents
        (pullback (C := Scheme.{u}) f (Spec.map (ofHom (algebraMap k k')))))
      (irreducibleComponents X) := by
  have := isGeometricallyIrreducible_of_isSepClosed k k'
  let p := pullback.fst (C := Scheme.{u}) f (Spec.map (ofHom (algebraMap k k')))
  let e := Scheme.Hom.irreducibleComponentsEquiv p p.isOpenMap
  exact Set.InvOn.bijOn (f' := (p.base ⁻¹' ·))
    ⟨fun _ hZ => congrArg Subtype.val (e.symm_apply_apply ⟨_, hZ⟩),
      fun _ _ => Set.image_preimage_eq _ p.surjective⟩
    (fun _ hZ => (e ⟨_, hZ⟩).2) fun _ hT => (e.symm ⟨_, hT⟩).2

end AlgebraicGeometry
