module

public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.AbelianSheaves
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ChangeOfBigSites

/-!
# Sheafification and affineness on a localized big site, uniformly in the topology

The five big sites of schemes are five different structures, and
`AlgebraicGeometry.overTopology` dispatches on `AlgebraicGeometry.CoveringTopology` to select
the topology of the localization of one of them at a scheme `S`.  The instances that the five
localized sites carry — sheafification of abelian presheaves, and the identification of the
weak equivalences with the locally bijective morphisms — are registered one topology at a time
in `StacksFrontier/AlgebraicGeometry/Topologies/BigSites/AbelianSheaves.lean`, against
`AlgebraicGeometry.BigZariskiOver.topology` and its four siblings.  Instance search cannot see
through the dispatch, so none of them applies to `overTopology τ B S hS`.  This file supplies
them there, by a five-case match.

Likewise the predicate "this object of the localized big site has affine total space" exists
five times over, once per topology and with the same body each time; this file gives it once,
dispatched on `τ`.

## Main definitions

* `AlgebraicGeometry.overScheme`: the scheme underlying an object of a localized big site.
* `AlgebraicGeometry.overIsAffine`: the objects of a localized big site whose underlying
  scheme is affine, uniformly in `τ`.

## Main results

* `AlgebraicGeometry.hasSheafify_overTopology_addCommGrp` and
  `AlgebraicGeometry.wEqualsLocallyBijective_overTopology`: the two sheaf-theoretic instances
  for `overTopology τ B S hS`.
* `AlgebraicGeometry.overIsAffine_iff`: membership in `overIsAffine` is affineness of the
  underlying scheme, in every one of the five topologies.

## Implementation notes

The sheafification instance carries `_addCommGrp` in its name because
`AlgebraicGeometry.hasSheafify_overTopology` is already taken, by the statement that
*set*-valued presheaves on the localized big *fppf* site can be sheafified.  The two are
different results — a different coefficient category and one topology rather than five — so the
name has to distinguish them rather than be shared.

The dispatch has to be discharged by giving the five terms explicitly.  Neither
`cases τ <;> infer_instance` nor `cases τ <;> dsimp only [overTopology] <;> infer_instance`
suffices: the second does reduce the dispatch, but instance search then still fails for the
fppf, syntomic and smooth cases while succeeding for the Zariski and étale ones.  The obstruction
is the order in which unification meets the `Contains` hypothesis, not a missing instance, so the
fix is to name the instance in each branch.

The five per-topology affineness predicates are `ObjectProperty` on the five localized
categories, which are all reducibly `CategoryTheory.Over (AlgebraicGeometry.base B S hS)`; the
fppf one is declared at the `AlgebraicGeometry` root rather than inside a `BigFppfOver`
namespace, unlike the other four.  None of them is to be confused with the notion of an object
*affine over* `S`, which is a condition on the structure morphism rather than on the total
space.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (τ : CoveringTopology) (B : BigSite.{u} τ) (S : Scheme.{u})
  (hS : S.size < cutoff τ B)

/-! ### Sheafification on a localized big site -/

/-- Abelian presheaves on the localization at `S` of any of the five big sites can be
sheafified.  This is the per-topology instance of
`StacksFrontier/AlgebraicGeometry/Topologies/BigSites/AbelianSheaves.lean`, made available at the
topology selected by `AlgebraicGeometry.overTopology`. -/
public instance hasSheafify_overTopology_addCommGrp :
    HasSheafify (overTopology τ B S hS) AddCommGrpCat.{u} := by
  cases τ with
  | zariski => exact BigZariskiOver.hasSheafify' B S hS
  | etale => exact BigEtaleOver.hasSheafify' B S hS
  | smooth => exact BigSmoothOver.hasSheafify' B S hS
  | syntomic => exact BigSyntomicOver.hasSheafify' B S hS
  | fppf => exact BigFppfOver.hasSheafify' B S hS

/-- The weak equivalences of abelian presheaves on the localization at `S` of any of the five
big sites are the locally bijective morphisms. -/
public instance wEqualsLocallyBijective_overTopology :
    (overTopology τ B S hS).WEqualsLocallyBijective AddCommGrpCat.{u} := by
  cases τ with
  | zariski => exact BigZariskiOver.wEqualsLocallyBijective' B S hS
  | etale => exact BigEtaleOver.wEqualsLocallyBijective' B S hS
  | smooth => exact BigSmoothOver.wEqualsLocallyBijective' B S hS
  | syntomic => exact BigSyntomicOver.wEqualsLocallyBijective' B S hS
  | fppf => exact BigFppfOver.wEqualsLocallyBijective' B S hS

/-! ### Affine objects of a localized big site -/

/-- The scheme underlying an object of the localization at `S` of a big site: the total space
of the structure morphism, with its size bound forgotten. -/
public abbrev overScheme (X : Over (base B S hS)) : Scheme.{u} := X.left.obj

/-- The objects of the localization at `S` of a big site whose underlying scheme is affine,
uniformly in the topology.  Each of the five big sites carries this predicate already; this is
the one dispatched on `τ`. -/
public def overIsAffine : (τ : CoveringTopology) → (B : BigSite.{u} τ) → (S : Scheme.{u}) →
    (hS : S.size < cutoff τ B) → ObjectProperty (Over (base B S hS))
  | .zariski, B, S, hS => BigZariskiOver.IsAffineOver B S hS
  | .etale, B, S, hS => BigEtaleOver.IsAffineOver B S hS
  | .smooth, B, S, hS => BigSmoothOver.IsAffineOver B S hS
  | .syntomic, B, S, hS => BigSyntomicOver.IsAffineOver B S hS
  | .fppf, B, S, hS => IsAffineOver B S hS

/-- Membership in `AlgebraicGeometry.overIsAffine` is affineness of the underlying scheme. -/
public theorem overIsAffine_iff (X : Over (base B S hS)) :
    overIsAffine τ B S hS X ↔ IsAffine (overScheme τ B S hS X) := by
  cases τ <;> exact Iff.rfl

end AlgebraicGeometry

end
