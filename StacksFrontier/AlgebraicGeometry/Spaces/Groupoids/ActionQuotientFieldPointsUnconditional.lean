module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineFlatChartDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.ActionQuotientFieldPoints

/-!
# Stacks 02Z5, the lifting direction, unconditionally

`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.ActionQuotientFieldPoints` proves the lifting
direction of Stacks 02Z5 — every field-valued point of the quotient of an object of the big
fppf site of `S` by a group action satisfying condition `(*)` of Stacks 02Z2 is the image of a
group-equivariant point over a finite Galois extension of the field — conditional on

```
IsEffectiveDescentAlongCoveringSieve B S hS
  (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType)
```

and on nothing else; that hypothesis is where the quotient's being an algebraic space, which
Stacks 02Z2 supplies in the source, enters. The proposition is a theorem:
`AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft`. This file
substitutes it, which discharges the tag.

## Main results

* `AlgebraicGeometry.Space.exists_galois_equivariant_lift_and_existsUnique_quotientPoint`:
  **Stacks 02Z5** entire, both directions together.
* `AlgebraicGeometry.Space.exists_galois_equivariant_lift`: a `K`-valued point of the quotient
  of `V` by `G` comes from a finite Galois extension `L/K`, a finite subgroup `H` of `G`, an
  isomorphism `H ≃* Gal(L/K)` and an `H`-equivariant `L`-valued point of `V` whose image in
  the quotient is the pullback of the given point.

## Implementation notes

This is `AlgebraicGeometry.Space.exists_galois_equivariant_lift_of_descent` with its last
explicit argument discharged, in exactly the way
`AlgebraicGeometry.Space.isSeparatedOver_actionQuotient_unconditional` discharges the same
hypothesis for Stacks 02Z4 and
`AlgebraicGeometry.Space.isAlgebraicSpace_quotient_unconditional` for Stacks 02WW. Nothing
else changes: the hypothesis `ha` is condition `(*)` of Stacks 02Z2, which the source assumes
too, and `HasSheafify (BigFppfOver.topology B S hS) (Type u)` is the choice of universe in
which the quotient presheaf is sheafified rather than an open mathematical assumption.

The converse direction, `AlgebraicGeometry.Space.quotientPoint_of_galois_equivariant`, never
had a descent hypothesis and is tagged where it is stated.

## References

* [Stacks Project, Tag 02Z5](https://stacks.math.columbia.edu/tag/02Z5)
* [Stacks Project, Tag 02Z2](https://stacks.math.columbia.edu/tag/02Z2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Groupoids

universe u v

namespace AlgebraicGeometry.Space

variable {S : Scheme.{u}} (B : BigFppfSite.{u}) (hS : B.Contains S)
  (V : BigFppfOver B S hS) (G : Type v) [Group G] [Small.{u} G]
  (a : G →* Aut (underlyingOver B hS V))
  [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
  (K : Type u) [Field K] (hK : B.Contains (Spec (.of K))) (b : Spec (.of K) ⟶ S)

/-- **Stacks 02Z5, the Galois-equivariant lift.** Let a group `G` act on an object `V` of the
big fppf site over `S` so that no nonidentity element fixes a point of `V` together with its
residue field. Then every `K`-valued point `ξ` of the quotient `V/G` is the image of an
equivariant point over a finite Galois extension of `K`: there are a finite Galois extension
`L/K`, a finite subgroup `H` of `G`, an isomorphism `H ≃* Gal(L/K)` and a morphism
`Spec L ⟶ V` over the given point of the base which is equivariant for that isomorphism and
whose image in the quotient is the pullback of `ξ`.

This is `AlgebraicGeometry.Space.exists_galois_equivariant_lift_of_descent` with its descent
hypothesis discharged by
`AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft`. -/
@[stacks 02Z5 "the Galois-equivariant lift of a field-valued point of the quotient"]
theorem exists_galois_equivariant_lift
    (ha : ActsNontriviallyOnFixedResidueFields (underlyingOver B hS V) G a)
    (ξ : (actionQuotient G B hS V a).obj (op (fieldObject (hS := hS) K hK b))) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : IsGalois K L) (H : Subgroup G) (_ : Finite H) (e : H ≃* (L ≃ₐ[K] L))
      (f : Spec (.of L) ⟶ (underlyingOver B hS V).left)
      (hf : f ≫ (underlyingOver B hS V).hom =
        Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ b),
      (∀ h : H,
        Spec.map (CommRingCat.ofHom (e h⁻¹).toRingHom) ≫ f = f ≫ (a h.1).hom.left) ∧
      IsQuotientLift B hS V G a K hK b ξ L f hf :=
  exists_galois_equivariant_lift_of_descent B hS V G a K hK b ha ξ
    (isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft B S hS)

/-- **Stacks 02Z5.** Let a group `G` act on an object `V` of the big fppf site over `S` so
that condition `(*)` of Stacks 02Z2 holds: no nonidentity element fixes a point of `V`
together with its residue field. Then for a field `K` with a point `Spec K ⟶ S` of the base:

* every `K`-valued point `ξ` of the quotient `V/G` comes from a finite Galois extension `L/K`,
  a finite subgroup `H ⊆ G`, an isomorphism `H ≃* Gal(L/K)` and an `H`-equivariant morphism
  `Spec L ⟶ V` over the base whose image in the quotient is the pullback of `ξ`;
* conversely, such data determine a `K`-valued point of `V/G`: there is exactly one whose
  pullback to `Spec L` is the image of the given morphism `Spec L ⟶ V`.

The two halves are `AlgebraicGeometry.Space.exists_galois_equivariant_lift` and
`AlgebraicGeometry.Space.existsUnique_quotientPoint_of_galois_equivariant`. -/
@[stacks 02Z5]
theorem exists_galois_equivariant_lift_and_existsUnique_quotientPoint
    (ha : ActsNontriviallyOnFixedResidueFields (underlyingOver B hS V) G a) :
    (∀ ξ : (actionQuotient G B hS V a).obj (op (fieldObject (hS := hS) K hK b)),
      ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
        (_ : IsGalois K L) (H : Subgroup G) (_ : Finite H) (e : H ≃* (L ≃ₐ[K] L))
        (f : Spec (.of L) ⟶ (underlyingOver B hS V).left)
        (hf : f ≫ (underlyingOver B hS V).hom =
          Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ b),
        (∀ h : H,
          Spec.map (CommRingCat.ofHom (e h⁻¹).toRingHom) ≫ f = f ≫ (a h.1).hom.left) ∧
        IsQuotientLift B hS V G a K hK b ξ L f hf) ∧
    (∀ (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
      (H : Subgroup G) [Finite H] (e : H ≃* (L ≃ₐ[K] L))
      (f : Spec (.of L) ⟶ (underlyingOver B hS V).left)
      (hf : f ≫ (underlyingOver B hS V).hom =
        Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ b),
      (∀ h : H,
        Spec.map (CommRingCat.ofHom (e h⁻¹).toRingHom) ≫ f = f ≫ (a h.1).hom.left) →
      ∃! ξ : (actionQuotient G B hS V a).obj (op (fieldObject (hS := hS) K hK b)),
        IsQuotientLift B hS V G a K hK b ξ L f hf) :=
  ⟨exists_galois_equivariant_lift B hS V G a K hK b ha,
    fun L _ _ _ _ H _ e f hf he =>
      existsUnique_quotientPoint_of_galois_equivariant B hS V G a K hK b L H e f hf he⟩

end AlgebraicGeometry.Space

end
