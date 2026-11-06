module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineFlatChartDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafAlgebraicGlueing

/-!
# Quotients of schemes by free actions of abstract groups

Let `S` be a scheme and let an abstract group `G` act by automorphisms over `S` on an object
`V` of a big fppf site over `S`. The Stacks Project calls the action *free* when it is free on
the `T`-valued points of `V` for every scheme `T` over `S`. For a scheme that condition is the
same as condition (*) of Tag 02Z2 — a nonidentity element fixing a point acts nontrivially on
the residue field there — so the quotient `V/G` is an algebraic space over `S`.

## Main definitions

* `AlgebraicGeometry.Space.ActsFreelyOnNonemptyPoints` is freeness of the action on the points
  of `V` over the schemes over `S` with nonempty underlying space.

## Main results

* `AlgebraicGeometry.Space.actsFreelyOnNonemptyPoints_iff`: freeness on points is exactly
  condition (*) of Tag 02Z2.
* `AlgebraicGeometry.Space.isAlgebraicSpace_actionQuotient_of_actsFreelyOnNonemptyPoints`:
  **Stacks 071S** for an action on an object of the site: the quotient of `V` by a free action
  of an abstract group is an algebraic space over `S`.

## Implementation notes

Freeness is read on the points over the schemes over `S` whose underlying space is nonempty.
The source asks for freeness on `X(T)` for *every* scheme `T` over `S`, and over the empty
scheme a sheaf of sets is terminal, so a free action there forces `G` to be trivial; this is
`AlgebraicGeometry.Space.forall_isCancelSMul_iff_subsingleton`. The restriction is also exactly
what the geometry uses, since the translating element is only ever read at a point of a scheme.

The two directions of `AlgebraicGeometry.Space.actsFreelyOnNonemptyPoints_iff` both pass
through the canonical point `Spec κ(x) ⟶ V` at a point `x`: a nonidentity element fixing that
point gives a fixed point of the scheme together with a trivial action on its residue field,
and conversely a fixed `T`-valued point gives a fixed point of `V` whose residue field map
can be cancelled off, residue field maps of a morphism of schemes being injective. This is why
the criterion of Tag 02Z2 is available here although Tag 071S cannot use it in general: the
points of an algebraic space have no residue fields, but the points of a scheme do.

The descent input of Tag 0265 which the quotient consumes is discharged, by
`AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft`, so the
statement below has no hypothesis beyond the source's.

## References

* [Stacks Project, Tag 071S](https://stacks.math.columbia.edu/tag/071S)
* [Stacks Project, Tag 02Z2](https://stacks.math.columbia.edu/tag/02Z2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable {S : Scheme.{u}} (U : Over S) (G : Type v) [Group G]

/-- An action of an abstract group on a scheme over `S` *acts freely on nonempty points* when
it is free on the `T`-valued points of the scheme for every scheme `T` over `S` with nonempty
underlying space: two group elements carrying a point to the same point are equal.

This is the freeness condition of Tag 071S, restricted to the test schemes with nonempty
underlying space; over the empty scheme there is exactly one point and freeness there would
force the group to be trivial. -/
def ActsFreelyOnNonemptyPoints (a : G →* Aut U) : Prop :=
  ∀ T : Over S, Nonempty T.left → ∀ (x : T ⟶ U) (g g' : G),
    x ≫ (a g).asIso.hom = x ≫ (a g').asIso.hom → g = g'

/-- A free action of an abstract group on a scheme over `S` has residue-field-faithful
stabilizers: the canonical point `Spec κ(x) ⟶ U` at a fixed point `x` of a group element
acting trivially on `κ(x)` is fixed by that element, hence the element is the identity. -/
theorem actsNontriviallyOnFixedResidueFields_of_actsFreelyOnNonemptyPoints
    (a : G →* Aut U) (ha : ActsFreelyOnNonemptyPoints U G a) :
    ActsNontriviallyOnFixedResidueFields U G a := by
  intro g x hx hg hres
  refine hg (ha (Over.mk (U.left.fromSpecResidueField x ≫ U.hom)) ?_
    (Over.homMk (U.left.fromSpecResidueField x)) g 1 ?_)
  · exact ⟨(IsLocalRing.closedPoint (U.left.residueField x) : PrimeSpectrum _)⟩
  have h1 : (a (1 : G)).asIso.hom = 𝟙 U := by rw [map_one]; rfl
  rw [h1, Category.comp_id]
  apply Over.OverMorphism.ext
  change U.left.fromSpecResidueField x ≫ (a g).asIso.hom.left = U.left.fromSpecResidueField x
  have h := ((a g).asIso.hom.left).SpecMap_residueFieldMap_fromSpecResidueField x
  rw [hres, Scheme.residueFieldCongr_fromSpecResidueField hx] at h
  exact h.symm

/-- An action of an abstract group on a scheme over `S` with residue-field-faithful stabilizers
is free on the points over every scheme over `S` with nonempty underlying space: a point of `U`
fixed by a group element has a fixed image point, and the residue field map of the fixed point
is injective, so the group element acts trivially on the residue field there. -/
theorem actsFreelyOnNonemptyPoints_of_actsNontriviallyOnFixedResidueFields
    (a : G →* Aut U) (ha : ActsNontriviallyOnFixedResidueFields U G a) :
    ActsFreelyOnNonemptyPoints U G a := by
  intro T hT x g g' hgg'
  obtain ⟨t⟩ := hT
  set d : G := g'⁻¹ * g with hd
  have hcancel : (a g').asIso.hom ≫ (a g'⁻¹).asIso.hom = 𝟙 U := by
    rw [a.map_inv g', Aut.inv_asIso]
    exact Iso.hom_inv_id _
  have hmul : (a d).asIso.hom = (a g).asIso.hom ≫ (a g'⁻¹).asIso.hom := by
    rw [hd, a.map_mul, Aut.mul_asIso]
    rfl
  have hfix : x ≫ (a d).asIso.hom = x := by
    rw [hmul, ← Category.assoc, hgg', Category.assoc, hcancel, Category.comp_id]
  have hfixl : x.left ≫ (a d).asIso.hom.left = x.left := congrArg Over.Hom.left hfix
  have hbase : (a d).asIso.hom.left (x.left t) = x.left t := by
    simpa using congrArg (fun f : T.left ⟶ U.left ↦ f.base t) hfixl
  have hmono : Mono (x.left.residueFieldMap t) :=
    ConcreteCategory.mono_of_injective _
      (RingHom.injective (x.left.residueFieldMap t).hom)
  have hres : (a d).asIso.hom.left.residueFieldMap (x.left t) ≫ x.left.residueFieldMap t =
      (U.left.residueFieldCongr hbase).hom ≫ x.left.residueFieldMap t := by
    rw [← Scheme.residueFieldMap_comp, Scheme.Hom.residueFieldMap_congr hfixl t]
    rfl
  have hd1 : d = 1 := by
    by_contra hne
    exact ha d (x.left t) hbase hne ((cancel_mono _).mp hres)
  rw [hd] at hd1
  exact (inv_mul_eq_one.mp hd1).symm

/-- Freeness of an action of an abstract group on a scheme over `S`, read on the points over
the schemes over `S` with nonempty underlying space, is condition (*) of Tag 02Z2. -/
theorem actsFreelyOnNonemptyPoints_iff (a : G →* Aut U) :
    ActsFreelyOnNonemptyPoints U G a ↔ ActsNontriviallyOnFixedResidueFields U G a :=
  ⟨actsNontriviallyOnFixedResidueFields_of_actsFreelyOnNonemptyPoints U G a,
    actsFreelyOnNonemptyPoints_of_actsNontriviallyOnFixedResidueFields U G a⟩

variable [Small.{u} G] (B : BigFppfSite.{u}) (hS : B.Contains S) (V : BigFppfOver B S hS)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

/-- **Stacks 071S** for an action on an object of a big fppf site over `S`: the quotient of `V`
by a free action of an abstract group `G` is an algebraic space over `S`.

The graph relation of a free action is an étale equivalence relation, by
`AlgebraicGeometry.Space.actsFreelyOnNonemptyPoints_iff` and Tag 02Z2, so this is
`AlgebraicGeometry.Space.isAlgebraicSpace_actionQuotient` with its descent hypothesis
discharged. -/
@[stacks 071S "for an action of the abstract group on an object of the big fppf site in place \
of an arbitrary algebraic space, the quotient being the sheaf quotient of the graph relation \
of the action, and freeness being read on the points over the test schemes with nonempty \
underlying space"]
theorem isAlgebraicSpace_actionQuotient_of_actsFreelyOnNonemptyPoints
    (a : G →* Aut (underlyingOver B hS V))
    (ha : ActsFreelyOnNonemptyPoints (underlyingOver B hS V) G a) :
    IsAlgebraicSpace B S hS (actionQuotient G B hS V a) :=
  isAlgebraicSpace_actionQuotient G B hS V a
    (actsNontriviallyOnFixedResidueFields_of_actsFreelyOnNonemptyPoints _ G a ha)
    (isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft B S hS)

end AlgebraicGeometry.Space

end
