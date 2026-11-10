module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraDescentSitePushforward
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraOpenSubspace

/-!
# Descent of a sheaf of graded algebras, read on an open subspace

Let `X` be a ringed space, `U` an open of it, and `α : O_X|_U ⟶ R'` a locally surjective
morphism of sheaves of rings on the **slice site** `(Opens X).over U` — a quotient of the slice
structure sheaf. `SheafOfModules.GradedAlgebra.descendSitePushforwardHom` interchanges descent
along such a quotient with pushforward along a continuous functor of sites, but it consumes a
commuting square of two structure maps and two quotients. This file supplies that square for the
passage from the slice site to the **open subspace** `X|_U`, whose site is `Opens ↥U`, and reads
off the resulting transport.

The square is the degenerate one: the structure map of the open subspace is the identity
(`Stacks.SheafOfModules.openSubspaceStructureMap`), the quotient downstairs is the pushforward
of the quotient upstairs, and the second structure map is the identity again, so the square
commutes by `Category.id_comp` against `Category.comp_id` and nothing has to be checked on
sections. What is not degenerate is that the pushed-forward quotient map is still *locally
surjective* on `Opens ↥U`; that is the cocontinuity of
`Stacks.SheafOfModules.openSubspaceSiteFunctor`.

## Main definitions

* `Stacks.SheafOfModules.openSubspaceRingSheaf` and `openSubspaceRingHom`: a quotient of the
  slice structure sheaf and its quotient map, read on the open subspace.
* `Stacks.SheafOfModules.descendOpenSubspaceHom` and `descendOpenSubspaceIso`: **the
  transport** — the open-subspace reading of an algebra descended on the slice site is the
  descent, along the open-subspace reading of the quotient map, of the open-subspace reading of
  the algebra.

## Main results

* `Stacks.SheafOfModules.isLocallySurjective_openSubspaceRingHom`: the quotient map stays
  locally surjective on the open subspace.
* `Stacks.SheafOfModules.openSubspace_descent_square`: **the commuting square**, in the shape
  `SheafOfModules.GradedAlgebra.descendSitePushforwardHom` consumes.
* `Stacks.SheafOfModules.smul_openSubspaceGradedAlgebra_eq_zero`: the open-subspace reading of
  an annihilated algebra is annihilated, so the descent downstairs needs no extra hypothesis.
* `Stacks.SheafOfModules.isIso_descendOpenSubspaceHom_app`: the transport is an isomorphism in
  every degree.
* `Stacks.SheafOfModules.isExteriorAlgebra_descendOpenSubspace` and
  `isExteriorAlgebra_of_descendOpenSubspace`: **the universal property of an exterior algebra
  crosses the transport**, in either direction.

## What this is for

The local-to-global step of [Stacks, Tag 0BQY] runs over the slice sites at the members of a
cover, while the local statements it glues are proved on restricted ringed *spaces*. The algebra
being compared there is a *descended* one — the composition-product algebra of an internal Hom
complex, descended along `O_X ↠ O_X/I` — so moving a statement between the two presentations has
to carry the descent, and `SheafOfModules.GradedAlgebra.descendSitePushforwardHom` is the only
thing that does. Its commuting square at the open-subspace spelling is what this file is,
alongside `Stacks.SheafOfModules.openSubspaceHomologyGradedAlgebraOfSpaceHom`, which identifies
*which* algebra is being transported.

What this file removes is the need for a commuting *square*: with the quotient downstairs taken
to be the pushforward of the quotient upstairs, there is no square left to prove. Nothing here
identifies `openSubspaceRingSheaf` with a quotient of the structure sheaf formed independently on
`X.restrict U` — it is the pushforward of the slice quotient, by definition — but that
identification is no longer owed: it is
`Stacks.SheafOfModules.openSubspaceRingQuotientIso` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuotientRingSheafOpenSubspace`, which identifies
the quotient of the structure sheaf of `X.restrict U` by a sheaf of ideals with the pushforward
of the slice quotient by the sheaf of ideals having the same sections, compatibly with the two
quotient maps. Its engine is `Stacks.Sites.quotientRingSheafIso`, the recognition of a locally
surjective quotient of a sheaf of rings as the quotient by its kernel.

## References

* [Stacks Project, Tag 08M3](https://stacks.math.columbia.edu/tag/08M3)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 0FR9](https://stacks.math.columbia.edu/tag/0FR9)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry RingedSpaceModuleAdjunction
open SheafOfModules.GradedAlgebra

universe u

namespace Stacks.SheafOfModules

variable {X : RingedSpace.{u, u}} (U : Opens X.carrier)
  {R' : Sheaf ((Opens.grothendieckTopology X.carrier).over U) RingCat.{u}}
  (α : (structureSheafRing X).over U ⟶ R')

/-- Pushforward from the slice site at `U` to the open subspace `U`, on sheaves of rings. This
is the functor of which `Stacks.SheafOfModules.openSubspaceEquiv` is the module-level
counterpart. -/
abbrev openSubspaceRingPushforward :
    Sheaf ((Opens.grothendieckTopology X.carrier).over U) RingCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology ↥U) RingCat.{u} :=
  (openSubspaceSiteFunctor U).sheafPushforwardContinuous RingCat.{u}
    (Opens.grothendieckTopology ↥U) ((Opens.grothendieckTopology X.carrier).over U)

/-- **A quotient of the slice structure sheaf, read on the open subspace.** Its sections over an
open `W` of `U` are the sections of `R'` over the corresponding object of `Opens X / U`. -/
abbrev openSubspaceRingSheaf : Sheaf (Opens.grothendieckTopology ↥U) RingCat.{u} :=
  (openSubspaceRingPushforward U).obj R'

/-- **A quotient map of the slice structure sheaf, read on the open subspace.** Its source is the
structure sheaf of `X.restrict U`, the pushforward of the slice structure sheaf being that sheaf
by definition. -/
abbrev openSubspaceRingHom :
    structureSheafRing (openSubspace U) ⟶ openSubspaceRingSheaf U (R' := R') :=
  (openSubspaceRingPushforward U).map α

/-- **The quotient map stays locally surjective on the open subspace**, the site functor
`Stacks.SheafOfModules.openSubspaceSiteFunctor` being cocontinuous. -/
instance isLocallySurjective_openSubspaceRingHom
    [Presheaf.IsLocallySurjective ((Opens.grothendieckTopology X.carrier).over U) α.hom] :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology ↥U)
      (openSubspaceRingHom U α).hom :=
  Presheaf.isLocallySurjective_whisker (Opens.grothendieckTopology ↥U)
    ((Opens.grothendieckTopology X.carrier).over U) (openSubspaceSiteFunctor U) α.hom

/-- **Pushforward along the site functor of the open subspace is full**, for an arbitrary sheaf
of rings on the slice site: it is the forward functor of
`Stacks.Sites.pushforwardModuleEquivOfSiteEquiv` at the equivalence of sites
`TopologicalSpace.Opens.overEquivalence`, which is continuous in both directions. The
equivalence `Stacks.SheafOfModules.openSubspaceEquiv` supplies this only at the *structure*
sheaf; what the descent presentation of [Stacks, Tag 0BQY] crosses the site with is a quotient
of it. -/
instance full_pushforward_openSubspaceRingSheaf :
    (_root_.SheafOfModules.pushforward.{u} (𝟙 (openSubspaceRingSheaf U (R' := R')))).Full :=
  Stacks.Sites.full_pushforward_of_siteEquiv (Opens.grothendieckTopology ↥U)
    U.overEquivalence.symm R'

/-- **Pushforward along the site functor of the open subspace is faithful**, for an arbitrary
sheaf of rings on the slice site. -/
instance faithful_pushforward_openSubspaceRingSheaf :
    (_root_.SheafOfModules.pushforward.{u} (𝟙 (openSubspaceRingSheaf U (R' := R')))).Faithful :=
  Stacks.Sites.faithful_pushforward_of_siteEquiv (Opens.grothendieckTopology ↥U)
    U.overEquivalence.symm R'

/-- **The commuting square of structure maps and quotients, at the open-subspace spelling.** The
hypothesis `SheafOfModules.GradedAlgebra.descendSitePushforwardHom` consumes, for the site
functor `Stacks.SheafOfModules.openSubspaceSiteFunctor`: both structure maps are identities and
the quotient downstairs is the pushforward of the quotient upstairs. -/
theorem openSubspace_descent_square :
    openSubspaceStructureMap U ≫ (openSubspaceRingPushforward U).map α =
      openSubspaceRingHom U α ≫ 𝟙 (openSubspaceRingSheaf U (R' := R')) :=
  (Category.id_comp _).trans (Category.comp_id _).symm

variable [Presheaf.IsLocallySurjective ((Opens.grothendieckTopology X.carrier).over U) α.hom]
  (A : _root_.SheafOfModules.GradedAlgebra.{u, u} ((structureSheafRing X).over U))
  (hA : ∀ (n : ℤ) (V : (Over U)ᵒᵖ) (b : ((structureSheafRing X).over U).obj.obj V),
    b ∈ RingHom.ker (α.hom.app V).hom → ∀ m : (A.piece n).val.obj V, b • m = 0)

omit [Presheaf.IsLocallySurjective ((Opens.grothendieckTopology X.carrier).over U) α.hom] in
include hA in
/-- **The open-subspace reading of an annihilated sheaf of graded algebras is annihilated.** A
section of the structure sheaf of `X.restrict U` killing the quotient acts on a section of the
transported algebra as it does upstairs, so the descent downstairs is available with no further
hypothesis. -/
theorem smul_openSubspaceGradedAlgebra_eq_zero (n : ℤ) (V : (Opens ↥U)ᵒᵖ)
    (b : (structureSheafRing (openSubspace U)).obj.obj V)
    (hb : b ∈ RingHom.ker ((openSubspaceRingHom U α).hom.app V).hom)
    (m : ((openSubspaceGradedAlgebra U A).piece n).val.obj V) : b • m = 0 :=
  ChangeOfRings.smul_pushforward_eq_zero (F := openSubspaceSiteFunctor U) α
    (openSubspaceRingHom U α) (openSubspaceStructureMap U) (𝟙 _)
    (openSubspace_descent_square U α) (A.piece n) (hA n) V b hb m

/-- **The transport**: the open-subspace reading of an algebra descended along a quotient of the
slice structure sheaf is the descent, along the open-subspace reading of that quotient, of the
open-subspace reading of the algebra. Degreewise the identity on local sections; this is
`SheafOfModules.GradedAlgebra.descendSitePushforwardHom` at the site functor of the open
subspace, with the commuting square `openSubspace_descent_square`. -/
def descendOpenSubspaceHom :
    _root_.SheafOfModules.GradedAlgebra.UnitalHom
      (_root_.SheafOfModules.GradedAlgebra.pushforward
        (𝟙 (openSubspaceRingSheaf U (R' := R')))
        (_root_.SheafOfModules.GradedAlgebra.descend α A hA))
      (_root_.SheafOfModules.GradedAlgebra.descend (openSubspaceRingHom U α)
        (openSubspaceGradedAlgebra U A) (smul_openSubspaceGradedAlgebra_eq_zero U α A hA)) :=
  descendSitePushforwardHom (F := openSubspaceSiteFunctor U) α (openSubspaceRingHom U α)
    (openSubspaceStructureMap U) (𝟙 _) (openSubspace_descent_square U α) A hA
    (smul_openSubspaceGradedAlgebra_eq_zero U α A hA)

/-- The transport is the identity on local sections. -/
theorem descendOpenSubspaceHom_app_val_app (n : ℤ) (V : (Opens ↥U)ᵒᵖ)
    (x : ((_root_.SheafOfModules.GradedAlgebra.pushforward
      (𝟙 (openSubspaceRingSheaf U (R' := R')))
        (_root_.SheafOfModules.GradedAlgebra.descend α A hA)).piece n).val.obj V) :
    ((descendOpenSubspaceHom U α A hA).app n).val.app V x = x :=
  rfl

/-- **Every degree of the transport is an isomorphism.** -/
instance isIso_descendOpenSubspaceHom_app (n : ℤ) :
    IsIso ((descendOpenSubspaceHom U α A hA).app n) :=
  isIso_descendSitePushforwardHom_app (F := openSubspaceSiteFunctor U) α
    (openSubspaceRingHom U α) (openSubspaceStructureMap U) (𝟙 _)
    (openSubspace_descent_square U α) A hA
    (smul_openSubspaceGradedAlgebra_eq_zero U α A hA) n

/-- **The transport, as an isomorphism of sheaves of graded algebras on the open subspace.** -/
def descendOpenSubspaceIso :
    _root_.SheafOfModules.GradedAlgebra.pushforward
        (𝟙 (openSubspaceRingSheaf U (R' := R')))
        (_root_.SheafOfModules.GradedAlgebra.descend α A hA) ≅
      _root_.SheafOfModules.GradedAlgebra.descend (openSubspaceRingHom U α)
        (openSubspaceGradedAlgebra U A) (smul_openSubspaceGradedAlgebra_eq_zero U α A hA) :=
  descendSitePushforwardIso (F := openSubspaceSiteFunctor U) α (openSubspaceRingHom U α)
    (openSubspaceStructureMap U) (𝟙 _) (openSubspace_descent_square U α) A hA
    (smul_openSubspaceGradedAlgebra_eq_zero U α A hA)

/-- **The universal property of an exterior algebra crosses the transport.** If the
open-subspace reading of the descended algebra is an exterior algebra on a degree-one generator,
then so is the descent of the open-subspace reading, on the image of that generator. -/
theorem isExteriorAlgebra_descendOpenSubspace
    {M : _root_.SheafOfModules.{u} (openSubspaceRingSheaf U (R' := R'))}
    {ι : M ⟶ (_root_.SheafOfModules.GradedAlgebra.pushforward
      (𝟙 (openSubspaceRingSheaf U (R' := R')))
        (_root_.SheafOfModules.GradedAlgebra.descend α A hA)).piece 1}
    (h : IsExteriorAlgebra (_root_.SheafOfModules.GradedAlgebra.pushforward
      (𝟙 (openSubspaceRingSheaf U (R' := R')))
        (_root_.SheafOfModules.GradedAlgebra.descend α A hA)) ι) :
    IsExteriorAlgebra (_root_.SheafOfModules.GradedAlgebra.descend (openSubspaceRingHom U α)
        (openSubspaceGradedAlgebra U A) (smul_openSubspaceGradedAlgebra_eq_zero U α A hA))
      (ι ≫ (descendOpenSubspaceHom U α A hA).app 1) :=
  isExteriorAlgebra_descendSitePushforward (F := openSubspaceSiteFunctor U) α
    (openSubspaceRingHom U α) (openSubspaceStructureMap U) (𝟙 _)
    (openSubspace_descent_square U α) A hA
    (smul_openSubspaceGradedAlgebra_eq_zero U α A hA) h

/-- **The universal property of an exterior algebra crosses the transport backwards.** The
direction a local-to-global argument uses: the universal property is established on the open
subspace, where the local computation lives, for the descent of the transported algebra, and is
needed for the transport of the descended algebra, which is the presentation the comparison map
is built in. -/
theorem isExteriorAlgebra_of_descendOpenSubspace
    {M : _root_.SheafOfModules.{u} (openSubspaceRingSheaf U (R' := R'))}
    {ι : M ⟶ (_root_.SheafOfModules.GradedAlgebra.descend (openSubspaceRingHom U α)
      (openSubspaceGradedAlgebra U A)
      (smul_openSubspaceGradedAlgebra_eq_zero U α A hA)).piece 1}
    (h : IsExteriorAlgebra (_root_.SheafOfModules.GradedAlgebra.descend (openSubspaceRingHom U α)
      (openSubspaceGradedAlgebra U A)
      (smul_openSubspaceGradedAlgebra_eq_zero U α A hA)) ι) :
    IsExteriorAlgebra (_root_.SheafOfModules.GradedAlgebra.pushforward
        (𝟙 (openSubspaceRingSheaf U (R' := R')))
        (_root_.SheafOfModules.GradedAlgebra.descend α A hA))
      (ι ≫ (descendOpenSubspaceHom U α A hA).inverse.app 1) :=
  isExteriorAlgebra_of_descendSitePushforward (F := openSubspaceSiteFunctor U) α
    (openSubspaceRingHom U α) (openSubspaceStructureMap U) (𝟙 _)
    (openSubspace_descent_square U α) A hA
    (smul_openSubspaceGradedAlgebra_eq_zero U α A hA) h

end Stacks.SheafOfModules

end
