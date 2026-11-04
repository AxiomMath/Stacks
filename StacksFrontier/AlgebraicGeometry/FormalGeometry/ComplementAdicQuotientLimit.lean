module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationLocalCohomologyLimit
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.ComplementCohomologyDeltaNatural

/-!
# The cohomology of `M̃` on a complement is the limit of that of the adic quotients

Let `A` be a commutative ring, let `I` and `J` be ideals, let `M` be an `A`-module and let
`V = Spec A ∖ V(J)`. The canonical map

`H^p(V, M̃) ⟶ lim_n H^p(V, (M/IⁿM)~)`

is the limit comparison of the cone obtained by applying the functor `N ↦ H^p(V, Ñ)` to the cone
of quotient maps `M ⟶ M/IⁿM`. This file builds that map and reduces its invertibility to the
invertibility of the corresponding map for local cohomology,

`H^{p+1}_J(M) ⟶ lim_n H^{p+1}_J(M/IⁿM)`,

which is `Stacks.Algebraization.isIso_localCohomologyAdicQuotientToLimit`, by transport along a
natural isomorphism of the two functors of the module.

## The reason a natural isomorphism is needed

Both sides of the comparison are inverse limits over the tower `n ↦ M/IⁿM`, so an isomorphism
`H^p(V, Ñ) ≅ H^{p+1}_J(N)` for each individual `N` does not suffice: it must be compatible with
the transition maps of the tower. That is exactly what naturality in `N` provides, and it is why
`Stacks.LocalCohomologySequence.nonempty_complementCohomologyBase_iso_localCohomology`, which
asserts only that the two modules are isomorphic, cannot be used here. The natural comparison is
`Stacks.LocalCohomologySequence.complementDeltaBaseNatIso` followed by the degreewise comparison
of Stacks 0A6T.

## Main definitions

* `Stacks.Algebraization.localCohomologyDegreeFunctor` — `N ↦ H^q_J(N)` as a functor on
  `A`-modules; its value is `Stacks.LocalCohomology.localCohomologyModule`.
* `Stacks.Algebraization.complementAdicQuotientToLimit` — the canonical map
  `H^p(V, M̃) ⟶ lim_n H^p(V, (M/IⁿM)~)`.

## Main results

* `CategoryTheory.Limits.isIso_limit_lift_mapCone_iff` — a natural isomorphism of functors
  identifies the limit comparisons of the images of one cone under the two functors, so one is
  invertible exactly when the other is.
* `Stacks.Algebraization.localCohomologyAdicQuotientToLimit_eq_lift_mapCone` — the canonical map
  of Tag 0DXJ is the limit comparison of the image of the cone of quotient maps under
  `N ↦ H^q_J(N)`.
* `Stacks.Algebraization.isIso_complementAdicQuotientToLimit_of_natIso` — the canonical map on
  the complement is invertible as soon as the one for local cohomology one degree up is, and the
  two functors of the module are naturally isomorphic.

## Implementation notes

The cone of quotient maps is built with `Stacks.Algebraization.natCone`, so its legs are the
maps `Stacks.Algebraization.adicQuotientProjection` and nothing is chosen. The identification of
`Stacks.Algebraization.localCohomologyAdicQuotientToLimit` with a limit comparison of a
`Functor.mapCone` is proved by `CategoryTheory.Limits.limit.hom_ext`, from the two `π`-equations
that pin both maps down.

Two spellings of the ring occur: the complement cohomology `complementCohomologyBaseFunctor` is
indexed by a `CommRingCat`, while local cohomology and the adic quotient tower are indexed by a
type with a `CommRing` instance. The statements below are at the latter and insert
`CommRingCat.of` where the former is needed.

## References

* [Stacks Project, Tag 0DXQ](https://stacks.math.columbia.edu/tag/0DXQ)
* [Stacks Project, Tag 0DXJ](https://stacks.math.columbia.edu/tag/0DXJ)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
* [Stacks Project, Tag 0A6T](https://stacks.math.columbia.edu/tag/0A6T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard

universe v₁ u₁ v₂ u₂ v₃ u₃ u

namespace CategoryTheory.Limits

/-- **A natural isomorphism identifies the limit comparisons of the images of a cone.** For
functors `F ≅ G` and a cone `c` on a diagram `Dg`, the limit comparison of `F.mapCone c` and the
limit comparison of `G.mapCone c` differ by the component of the isomorphism at the vertex and
the isomorphism of the two limits; so one is invertible exactly when the other is. -/
public theorem limit_lift_mapCone_comp_isoOfNatIso {J : Type v₁} [Category.{u₁} J]
    {C : Type v₂} [Category.{u₂} C] {D : Type v₃} [Category.{u₃} D]
    {Dg : J ⥤ C} (F G : C ⥤ D) (e : F ≅ G) (c : Cone Dg)
    [HasLimit (Dg ⋙ F)] [HasLimit (Dg ⋙ G)] :
    limit.lift (Dg ⋙ F) (F.mapCone c) ≫
        (HasLimit.isoOfNatIso (Functor.isoWhiskerLeft Dg e)).hom =
      e.hom.app c.pt ≫ limit.lift (Dg ⋙ G) (G.mapCone c) := by
  refine limit.hom_ext fun j => ?_
  rw [Category.assoc, HasLimit.isoOfNatIso_hom_π, limit.lift_π_assoc, Category.assoc,
    limit.lift_π]
  exact e.hom.naturality (c.π.app j)

/-- **The two limit comparisons are invertible together.** -/
public theorem isIso_limit_lift_mapCone_iff {J : Type v₁} [Category.{u₁} J]
    {C : Type v₂} [Category.{u₂} C] {D : Type v₃} [Category.{u₃} D]
    {Dg : J ⥤ C} (F G : C ⥤ D) (e : F ≅ G) (c : Cone Dg)
    [HasLimit (Dg ⋙ F)] [HasLimit (Dg ⋙ G)] :
    IsIso (limit.lift (Dg ⋙ F) (F.mapCone c)) ↔
      IsIso (limit.lift (Dg ⋙ G) (G.mapCone c)) := by
  rw [← isIso_comp_right_iff _ (HasLimit.isoOfNatIso (Functor.isoWhiskerLeft Dg e)).hom,
    limit_lift_mapCone_comp_isoOfNatIso, isIso_comp_left_iff]

end CategoryTheory.Limits

namespace Stacks.Algebraization

open Stacks.LocalCohomology Stacks.LocalCohomologySequence

variable (A : Type u) [CommRing A]

/-! ### The two functors of the module -/

/-- `N ↦ H^q_J(N)`, the degree-`q` local cohomology with support in `V(J)`, as a functor on
`A`-modules. Its value at `N` is `Stacks.LocalCohomology.localCohomologyModule A J hJ N q`. -/
def localCohomologyDegreeFunctor (J : Ideal A) (hJ : J.FG) (q : ℤ) :
    ModuleCat.{u} A ⥤ ModuleCat.{u} A :=
  DerivedCategory.singleFunctor (ModuleCat.{u} A) 0 ⋙ localCohomologyDerived A J hJ ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{u} A) q

/-- The value of `localCohomologyDegreeFunctor A J hJ q` at `N` is
`Stacks.LocalCohomology.localCohomologyModule A J hJ N q`. -/
theorem localCohomologyDegreeFunctor_obj (J : Ideal A) (hJ : J.FG) (q : ℤ)
    (N : ModuleCat.{u} A) :
    (localCohomologyDegreeFunctor A J hJ q).obj N = localCohomologyModule A J hJ N q :=
  rfl

/-! ### The canonical map of Tag 0DXJ as a limit comparison of an image cone -/

/-- **The canonical map `H^q_J(M) ⟶ lim_n H^q_J(M/IⁿM)` is the limit comparison of the image of
the cone of quotient maps under `N ↦ H^q_J(N)`.** Both maps are determined by their composites
with the projections of the limit, and those composites agree because the `n`-th leg of either
cone is local cohomology applied to the `n`-th quotient map. -/
theorem localCohomologyAdicQuotientToLimit_eq_lift_mapCone (I J : Ideal A) (hJ : J.FG)
    (M : ModuleCat.{u} A) (q : ℤ) :
    localCohomologyAdicQuotientToLimit A I J hJ M q =
      limit.lift (adicQuotientModuleSystem A I M ⋙ localCohomologyDegreeFunctor A J hJ q)
        ((localCohomologyDegreeFunctor A J hJ q).mapCone
          (Dualizing.adicQuotientModuleCone A I M)) := by
  refine limit.hom_ext fun j => ?_
  obtain ⟨n⟩ := j
  rw [localCohomologyAdicQuotientToLimit_π]
  exact (limit.lift_π ((localCohomologyDegreeFunctor A J hJ q).mapCone
    (Dualizing.adicQuotientModuleCone A I M)) (op n)).symm

/-! ### The canonical map on the complement -/

/-- **The canonical map `H^p(V, M̃) ⟶ lim_n H^p(V, (M/IⁿM)~)`** for `V = Spec A ∖ V(J)`: the
limit comparison of the image of the cone of quotient maps `M ⟶ M/IⁿM` under the functor
`N ↦ H^p(V, Ñ)`. -/
def complementAdicQuotientToLimit (I J : Ideal A) (M : ModuleCat.{u} A) (p : ℕ) :
    (complementCohomologyBaseFunctor (A := CommRingCat.of A) J p).obj M ⟶
      limit (adicQuotientModuleSystem A I M ⋙
        complementCohomologyBaseFunctor (A := CommRingCat.of A) J p) :=
  limit.lift _ ((complementCohomologyBaseFunctor (A := CommRingCat.of A) J p).mapCone
    (Dualizing.adicQuotientModuleCone A I M))

/-- The composite of `complementAdicQuotientToLimit` with the `n`-th projection of the limit is
the map `H^p(V, M̃) ⟶ H^p(V, (M/IⁿM)~)` induced by the quotient map `M ⟶ M/IⁿM`. -/
theorem complementAdicQuotientToLimit_π (I J : Ideal A) (M : ModuleCat.{u} A) (p : ℕ) (n : ℕ) :
    complementAdicQuotientToLimit A I J M p ≫
        limit.π (adicQuotientModuleSystem A I M ⋙
          complementCohomologyBaseFunctor (A := CommRingCat.of A) J p) (op n) =
      (complementCohomologyBaseFunctor (A := CommRingCat.of A) J p).map
        (Dualizing.adicQuotientProjection A I M n) :=
  limit.lift_π _ _

/-! ### The transport -/

/-- **The canonical map on the complement is invertible once the one for local cohomology a
degree up is.** The hypothesis `e` is the comparison of Stacks 0DWR above degree zero read as a
natural isomorphism of functors of the module, which is what makes the two inverse limits over
the tower `n ↦ M/IⁿM` correspond. -/
theorem isIso_complementAdicQuotientToLimit_of_natIso (I J : Ideal A) (hJ : J.FG)
    (M : ModuleCat.{u} A) (p : ℕ)
    (e : complementCohomologyBaseFunctor (A := CommRingCat.of A) J p ≅
      localCohomologyDegreeFunctor A J hJ ((p : ℤ) + 1))
    (h : IsIso (localCohomologyAdicQuotientToLimit A I J hJ M ((p : ℤ) + 1))) :
    IsIso (complementAdicQuotientToLimit A I J M p) := by
  rw [localCohomologyAdicQuotientToLimit_eq_lift_mapCone] at h
  exact (isIso_limit_lift_mapCone_iff
    (complementCohomologyBaseFunctor (A := CommRingCat.of A) J p)
    (localCohomologyDegreeFunctor A J hJ ((p : ℤ) + 1)) e
    (Dualizing.adicQuotientModuleCone A I M)).2 h

end Stacks.Algebraization

end
