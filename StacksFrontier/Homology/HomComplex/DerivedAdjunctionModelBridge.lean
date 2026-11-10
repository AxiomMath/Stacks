module

public import StacksFrontier.Homology.HomComplex.DerivedAdjunctionTransport

/-!
# The bundle bridge: model transposes read in the [stacks 0A63] bundle over the ring

Two tensor--Hom bundles of [stacks 0A63] are in play whenever a statement about `D(R)` at a
module universe independent of the ring's is compared with a chain-level computation.

* `StacksDraft.DerivedHom.derivedHomAdjunctionOverRing R` is the bundle on `D(R)` itself.
* `StacksDraft.DerivedHom.derivedHomAdjunctionULift (R := R)`, which is a bare `abbrev` for
  `StacksDraft.DerivedHom.derivedHomAdjunction` at the lifted ring and hence the very same term
  as `StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction (ULift.{v} R)`, is the bundle
  on `D(ULift.{v} R)`, where the ring and its modules share a universe and the K-flat and
  K-injective comparisons `DerivedHomData.tensorIso` and `DerivedHomData.homIso` are available.

They are not two bundles: the first is *defined* as the transport of the second along
`StacksDraft.DerivedHom.derivedScalarEquivalence`, the derived restriction-of-scalars
equivalence for `ULift.ringEquiv`.  So anything proved in the model bundle can be read in the
bundle over the ring, and this file carries the transposes across.

`StacksDraft.DerivedHom.derivedHomAdjunctionOverRing_homEquiv_symm_apply` already does this for
the transpose of a chain map, but only after that transpose has been replaced by its chain-level
value, the map `Φ` of [stacks 0A62] followed by postcomposition.  The statements below keep the
model transpose itself, which is the shape in which it occurs when it has to be *inverted*: the
inverse of a transpose is not the transpose of anything, so the chain-level reading is unusable
there.

## Main results

* `StacksDraft.DerivedHom.homEquiv_symm_derivedTensorModelIso` — **the bridge**: the transpose
  taken in the bundle over the ring, at the K-flat tensor model
  `StacksDraft.DerivedHom.derivedTensorModelIso`, is the image of the model transpose at
  `DerivedHomData.tensorIso`, read through
  `StacksDraft.DerivedHom.derivedHomULiftIso`.
* `StacksDraft.DerivedHom.isIso_homEquiv_symm_derivedTensorModelIso` — so one is invertible as
  soon as the other is.
* `StacksDraft.DerivedHom.inv_homEquiv_symm_derivedTensorModelIso` — the inverses correspond.
* `StacksDraft.DerivedHom.derivedHomModelIso_inv_comp_inv_homEquiv_symm` — **the inverted
  bridge**, in the shape a consumer meets it: the K-injective representation of derived internal
  Hom followed by the inverted model transpose is, after transport, the inverse of
  `StacksDraft.DerivedHom.derivedHomModelIso` followed by the inverted transpose of the bundle
  over the ring.

## Implementation notes

The invertibility hypothesis is an instance argument on the *model* transpose, which is the side
a chain-level criterion is available on; the transported one is then produced by
`StacksDraft.DerivedHom.isIso_homEquiv_symm_derivedTensorModelIso` and appears in the statements
as a `letI`.

`rw` cannot move the bridge underneath `CategoryTheory.inv`, the invertibility instance being
a dependent occurrence of the very morphism rewritten; `CategoryTheory.IsIso.inv_eq_of_hom_inv_id`
is used instead, which asks only for a positive occurrence.

No `@[stacks]` attribute is placed here: this file identifies two readings of one construction,
and covers no tag.

## References

* [Stacks Project, Tag 0A62](https://stacks.math.columbia.edu/tag/0A62)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace StacksDraft.DerivedHom

variable {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]

/-- **The bundle bridge for the transpose.**  The [stacks 0A63] transpose of
`StacksDraft.DerivedHom.derivedHomAdjunctionOverRing R`, evaluated at the K-flat tensor model
`StacksDraft.DerivedHom.derivedTensorModelIso` of a chain map `h`, is the image under the scalar
equivalence of the transpose taken in the model bundle
`StacksDraft.DerivedHom.derivedHomAdjunctionULift` at `DerivedHomData.tensorIso`, read through
the bifunctor comparison `StacksDraft.DerivedHom.derivedHomULiftIso`.

This is `DerivedHomAdjunction.transportHomEquiv_symm_apply_functor_obj` with the model tensor
comparison absorbed into `StacksDraft.DerivedHom.derivedTensorModelIso`; unlike
`StacksDraft.DerivedHom.derivedHomAdjunctionOverRing_homEquiv_symm_apply` it leaves the model
transpose standing, so it can be used where that transpose is inverted. -/
theorem homEquiv_symm_derivedTensorModelIso
    (K L I : CochainComplex (ModuleCat.{max u v} (ULift.{v} R)) ℤ)
    (hL : L.KFlat) [I.IsKInjective] (h : K ⊗ L ⟶ I) :
    ((derivedHomAdjunctionOverRing.{u, v, w} R).homEquiv
        ((derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj K))
        ((derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj L))
        ((derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj I))).symm
        ((derivedTensorModelIso.{u, v, w} R K L hL).hom ≫
          (derivedScalarEquivalence.{u, v, w} R).functor.map (DerivedCategory.Q.map h)) =
      (derivedScalarEquivalence.{u, v, w} R).functor.map
          (((derivedHomAdjunctionULift.{u, v, max u v + 1} (R := R)).homEquiv
              (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
              (DerivedCategory.Q.obj I)).symm
            (((derivedHomAdjunctionULift.{u, v, max u v + 1} (R := R)).tensorIso K L hL).hom ≫
              DerivedCategory.Q.map h)) ≫
        ((derivedHomULiftIso.{u, v, w} R).app
          (Opposite.op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj I)).inv := by
  have harg : (derivedTensorModelIso.{u, v, w} R K L hL).hom ≫
        (derivedScalarEquivalence.{u, v, w} R).functor.map (DerivedCategory.Q.map h) =
      ((derivedTensorULiftIso.{u, v, w} R).app
          (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L)).hom ≫
        (derivedScalarEquivalence.{u, v, w} R).functor.map
          (((derivedHomAdjunctionULift.{u, v, max u v + 1} (R := R)).tensorIso K L hL).hom ≫
            DerivedCategory.Q.map h) := by
    refine (Category.assoc _ _ _).trans ?_
    rw [Functor.mapIso_hom, ← (derivedScalarEquivalence.{u, v, w} R).functor.map_comp]
  rw [harg]
  exact (derivedHomAdjunctionULift.{u, v, max u v + 1}
      (R := R)).toDerivedHomAdjunction.transportHomEquiv_symm_apply_functor_obj
      (derivedScalarEquivalence.{u, v, w} R) (DerivedCategory.Q.obj K)
      (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj I) _

/-- The transported transpose is invertible as soon as the model one is: by
`StacksDraft.DerivedHom.homEquiv_symm_derivedTensorModelIso` it is the image of the model
transpose composed with an isomorphism of bifunctors. -/
instance isIso_homEquiv_symm_derivedTensorModelIso
    (K L I : CochainComplex (ModuleCat.{max u v} (ULift.{v} R)) ℤ)
    (hL : L.KFlat) [I.IsKInjective] (h : K ⊗ L ⟶ I)
    [IsIso (((derivedHomAdjunctionULift.{u, v, max u v + 1} (R := R)).homEquiv
        (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj I)).symm
      (((derivedHomAdjunctionULift.{u, v, max u v + 1} (R := R)).tensorIso K L hL).hom ≫
        DerivedCategory.Q.map h))] :
    IsIso (((derivedHomAdjunctionOverRing.{u, v, w} R).homEquiv
        ((derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj K))
        ((derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj L))
        ((derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj I))).symm
      ((derivedTensorModelIso.{u, v, w} R K L hL).hom ≫
        (derivedScalarEquivalence.{u, v, w} R).functor.map (DerivedCategory.Q.map h))) := by
  rw [homEquiv_symm_derivedTensorModelIso.{u, v, w} K L I hL h]
  infer_instance

/-- The inverses correspond: the inverse of the transported transpose is the image of the
inverse of the model transpose, read through
`StacksDraft.DerivedHom.derivedHomULiftIso`. -/
theorem inv_homEquiv_symm_derivedTensorModelIso
    (K L I : CochainComplex (ModuleCat.{max u v} (ULift.{v} R)) ℤ)
    (hL : L.KFlat) [I.IsKInjective] (h : K ⊗ L ⟶ I)
    [IsIso (((derivedHomAdjunctionULift.{u, v, max u v + 1} (R := R)).homEquiv
        (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj I)).symm
      (((derivedHomAdjunctionULift.{u, v, max u v + 1} (R := R)).tensorIso K L hL).hom ≫
        DerivedCategory.Q.map h))] :
    inv (((derivedHomAdjunctionOverRing.{u, v, w} R).homEquiv
        ((derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj K))
        ((derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj L))
        ((derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj I))).symm
      ((derivedTensorModelIso.{u, v, w} R K L hL).hom ≫
        (derivedScalarEquivalence.{u, v, w} R).functor.map (DerivedCategory.Q.map h))) =
      ((derivedHomULiftIso.{u, v, w} R).app
          (Opposite.op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj I)).hom ≫
        (derivedScalarEquivalence.{u, v, w} R).functor.map
          (inv (((derivedHomAdjunctionULift.{u, v, max u v + 1} (R := R)).homEquiv
              (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
              (DerivedCategory.Q.obj I)).symm
            (((derivedHomAdjunctionULift.{u, v, max u v + 1} (R := R)).tensorIso K L hL).hom ≫
              DerivedCategory.Q.map h))) := by
  refine IsIso.inv_eq_of_hom_inv_id ?_
  rw [homEquiv_symm_derivedTensorModelIso.{u, v, w} K L I hL h, Category.assoc,
    Iso.inv_hom_id_assoc, ← (derivedScalarEquivalence.{u, v, w} R).functor.map_comp,
    IsIso.hom_inv_id, (derivedScalarEquivalence.{u, v, w} R).functor.map_id]

/-- **The inverted bridge.**  The K-injective representation `DerivedHomData.homIso` of derived
internal Hom followed by the inverted model transpose, transported along the scalar equivalence,
is the inverse of `StacksDraft.DerivedHom.derivedHomModelIso` followed by the inverted transpose
of the bundle over the ring.

Both representation isomorphisms are absorbed, so no bifunctor comparison survives on either
side: this is the form in which a chain-level computation carried out in the model bundle is
read in the [stacks 0A63] bundle on `D(R)`. -/
theorem derivedHomModelIso_inv_comp_inv_homEquiv_symm
    (K L I : CochainComplex (ModuleCat.{max u v} (ULift.{v} R)) ℤ)
    (hL : L.KFlat) [I.IsKInjective] (h : K ⊗ L ⟶ I)
    [IsIso (((derivedHomAdjunctionULift.{u, v, max u v + 1} (R := R)).homEquiv
        (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj I)).symm
      (((derivedHomAdjunctionULift.{u, v, max u v + 1} (R := R)).tensorIso K L hL).hom ≫
        DerivedCategory.Q.map h))] :
    (derivedScalarEquivalence.{u, v, w} R).functor.map
        (((derivedHomAdjunctionULift.{u, v, max u v + 1} (R := R)).homIso L I).inv ≫
          inv (((derivedHomAdjunctionULift.{u, v, max u v + 1} (R := R)).homEquiv
              (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
              (DerivedCategory.Q.obj I)).symm
            (((derivedHomAdjunctionULift.{u, v, max u v + 1} (R := R)).tensorIso K L hL).hom ≫
              DerivedCategory.Q.map h))) =
      (derivedHomModelIso.{u, v, w} R L I).inv ≫
        inv (((derivedHomAdjunctionOverRing.{u, v, w} R).homEquiv
            ((derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj K))
            ((derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj L))
            ((derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj I))).symm
          ((derivedTensorModelIso.{u, v, w} R K L hL).hom ≫
            (derivedScalarEquivalence.{u, v, w} R).functor.map (DerivedCategory.Q.map h))) := by
  rw [inv_homEquiv_symm_derivedTensorModelIso.{u, v, w} K L I hL h,
    (derivedScalarEquivalence.{u, v, w} R).functor.map_comp]
  change _ = ((derivedHomULiftIso.{u, v, w} R).app
        (Opposite.op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj I) ≪≫
      (derivedScalarEquivalence.{u, v, w} R).functor.mapIso
        ((derivedHomAdjunctionULift.{u, v, max u v + 1} (R := R)).homIso L I)).inv ≫ _
  simp only [Iso.trans_inv, Functor.mapIso_inv, Category.assoc, Iso.inv_hom_id_assoc]

end StacksDraft.DerivedHom

end
