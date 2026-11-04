module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedSitePushforwardEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasicoherentAlgebras

/-!
# The graded algebra of a slice site, read on the open subspace

Let `X` be a ringed space and `U` an open of it. A sheaf of graded algebras on the **slice
site** `(Opens X).over U` and one on the **open subspace** `X|_U`, whose site is `Opens ↥U`,
live on two different presentations of the same ringed topos. This file identifies them, by
`Stacks.SheafOfModules.openSubspaceEquiv` — Mathlib's
`TopologicalSpace.Opens.sheafOfModulesEquivOver`, read through
`Stacks.SheafOfModules.openSubspace_eq_restrict`, so that the target really is Mathlib's
`X.restrict U.isOpenEmbedding` and not a second notion of open subspace.

The identification is the degreewise one and nothing more: the forward functor of
`openSubspaceEquiv` is the pushforward along the site functor
`Stacks.SheafOfModules.openSubspaceSiteFunctor` with the identity structure map
(`Stacks.SheafOfModules.openSubspaceEquiv_functor`), so
`SheafOfModules.GradedAlgebra.pushforward` at that structure map *is* the transport, with
every comparison below `rfl`.

## Main definitions

* `Stacks.SheafOfModules.openSubspaceGradedAlgebra`: **a sheaf of graded algebras on the slice
  site over `U`, read as one on the open subspace `U`.**
* `Stacks.SheafOfModules.openSubspaceUnitalHom`: the same for a homomorphism.

## Main results

* `Stacks.SheafOfModules.openSubspaceGradedAlgebra_piece`: its degree-`n` piece is the image of
  the degree-`n` piece under `Stacks.SheafOfModules.openSubspaceEquiv`.
* `Stacks.SheafOfModules.isIso_openSubspaceUnitalHom_app_iff`: **a homomorphism of sheaves of
  graded algebras on the slice site is an isomorphism in degree `n` if and only if it is one on
  the open subspace.** This is the form in which a statement proved on `X|_U` is fed to the
  gluing primitive `SheafOfModules.GradedAlgebra.UnitalHom.isIso_app_of_coversTop`, which runs
  over slice sites.
* `Stacks.SheafOfModules.isExteriorAlgebra_of_openSubspaceGradedAlgebra` and
  `Stacks.SheafOfModules.isExteriorAlgebra_id_of_openSubspaceGradedAlgebra`: **the
  exterior-algebra universal property crosses the identification too**, in the direction a
  local-to-global argument uses — from the open subspace, where the local statements are
  proved, to the slice site, over which the gluing runs — at an arbitrary degree-one generator
  and at the identity generator respectively.

## Implementation notes

**The lift of `TopologicalSpace.Opens.overEquivalence` to sheaves of modules is available.** It is
`TopologicalSpace.Opens.sheafOfModulesEquivOver`, in Mathlib, recorded here as
`Stacks.SheafOfModules.openSubspaceEquiv` and used by the main tree in `ExteriorPowerFiniteType`,
`ExteriorPowerShortExact` and `QuasicoherentAlgebras` itself.

**What the identification carries, and what it took.** Invertibility of a morphism present on
both sides transports in both directions with nothing but the pushforward being an equivalence,
hence reflecting isomorphisms: that is `isIso_openSubspaceUnitalHom_app_iff`, and invertibility
is what the gluing primitive
`SheafOfModules.GradedAlgebra.UnitalHom.isIso_app_of_coversTop` consumes.

`SheafOfModules.GradedAlgebra.IsExteriorAlgebra` is a universal property, quantifying over all
sheaves of graded algebras on its site, so it does *not* transport on the strength of the
pushforward being a functor — the implementation notes of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedSitePushforward.lean` say so, and a note
here previously left it at that. It does nonetheless cross this identification, in the direction
a local-to-global argument uses, and what that took is
`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.of_sitePushforward` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedSitePushforwardEquivalence.lean`: the test
algebra of the property being proved travels *forwards* along the pushforward, so only fullness
and faithfulness of `SheafOfModules.GradedAlgebra.UnitalHom.sitePushforward` are needed, and
not — as one might expect, and as the earlier note suggested — essential surjectivity on graded
algebras. All three hypotheses are discharged here by the equivalence:
`full_pushforward_openSubspaceStructureMap`,
`faithful_pushforward_openSubspaceStructureMap`, and essential surjectivity of
`Stacks.SheafOfModules.openSubspaceSiteFunctor`, which is the inverse of an equivalence of
categories.

The direction *into* the open subspace is a different statement and is not proved here: it
would need a sheaf of graded algebras on the slice site to be produced from one on the open
subspace, which is essential surjectivity on graded algebras. The gluing does not use it.

**Which graded algebra is transported** is a separate question from the transport, and is
settled in
`StacksFrontier/Topology/Sheaves/Cohomology/InternalHom/HomComplexAlgebraOpenSubspace.lean`: for
the graded algebra of the cohomology sheaves of an internal Hom complex, the transport off the
slice site is the same algebra formed on `X.restrict V`, by
`Stacks.SheafOfModules.openSubspaceHomologyGradedAlgebraOfSpaceHom`. That needs the nested
slice equivalence applied to internal Homs and is not an instance of anything here.

**Universes.** Everything is the single universe `u` that `RingedSpace.{u, u}` and the slice
site force, as in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/QuasicoherentAlgebras.lean`.

## References

* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 0FR9](https://stacks.math.columbia.edu/tag/0FR9)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry RingedSpaceModuleAdjunction

universe u

namespace Stacks.SheafOfModules

variable {X : RingedSpace.{u, u}} (U : Opens X.carrier)

/-- The structure map of `Stacks.SheafOfModules.openSubspaceEquiv`: the identity, the
pushforward of the slice structure sheaf along the site functor being the structure sheaf of the
open subspace by definition. -/
abbrev openSubspaceStructureMap :
    structureSheafRing (openSubspace U) ⟶
      ((openSubspaceSiteFunctor U).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology ↥U)
        ((Opens.grothendieckTopology X.carrier).over U)).obj ((structureSheafRing X).over U) :=
  𝟙 _

/-- The pushforward along the structure map is the forward functor of
`Stacks.SheafOfModules.openSubspaceEquiv`. -/
theorem pushforward_openSubspaceStructureMap :
    _root_.SheafOfModules.pushforward.{u} (openSubspaceStructureMap U) =
      (openSubspaceEquiv U).functor := rfl

/-- **A sheaf of graded algebras on the slice site over `U`, read on the open subspace `U`.**
Its pieces are the images of the pieces under `Stacks.SheafOfModules.openSubspaceEquiv`, and its
multiplication and unit are those of `A` read at the opens of `X` contained in `U`. -/
def openSubspaceGradedAlgebra
    (A : _root_.SheafOfModules.GradedAlgebra.{u, u} ((structureSheafRing X).over U)) :
    _root_.SheafOfModules.GradedAlgebra.{u, u} (structureSheafRing (openSubspace U)) :=
  _root_.SheafOfModules.GradedAlgebra.pushforward (openSubspaceStructureMap U) A

/-- **The degree-`n` piece of the transported algebra is the transport of the degree-`n`
piece**, along `Stacks.SheafOfModules.openSubspaceEquiv`. -/
@[simp]
theorem openSubspaceGradedAlgebra_piece
    (A : _root_.SheafOfModules.GradedAlgebra.{u, u} ((structureSheafRing X).over U)) (n : ℤ) :
    (openSubspaceGradedAlgebra U A).piece n = (openSubspaceEquiv U).functor.obj (A.piece n) :=
  rfl

/-- The multiplication of the transported algebra is the multiplication of `A` read at the
corresponding object of the slice site. -/
theorem openSubspaceGradedAlgebra_mul_app
    (A : _root_.SheafOfModules.GradedAlgebra.{u, u} ((structureSheafRing X).over U)) (i j : ℤ)
    (V : (Opens ↥U)ᵒᵖ) :
    ((openSubspaceGradedAlgebra U A).mul i j).app V =
      (A.mul i j).app (op ((openSubspaceSiteFunctor U).obj V.unop)) := rfl

/-- **A homomorphism of sheaves of graded algebras on the slice site, read on the open
subspace.** -/
def openSubspaceUnitalHom
    {A B : _root_.SheafOfModules.GradedAlgebra.{u, u} ((structureSheafRing X).over U)}
    (g : _root_.SheafOfModules.GradedAlgebra.UnitalHom A B) :
    _root_.SheafOfModules.GradedAlgebra.UnitalHom
      (openSubspaceGradedAlgebra U A) (openSubspaceGradedAlgebra U B) :=
  g.sitePushforward (openSubspaceStructureMap U)

/-- The degree-`n` component of the transported homomorphism is the transport of the degree-`n`
component. -/
@[simp]
theorem openSubspaceUnitalHom_app
    {A B : _root_.SheafOfModules.GradedAlgebra.{u, u} ((structureSheafRing X).over U)}
    (g : _root_.SheafOfModules.GradedAlgebra.UnitalHom A B) (n : ℤ) :
    (openSubspaceUnitalHom U g).app n = (openSubspaceEquiv U).functor.map (g.app n) := rfl

/-- The transport reflects isomorphisms, being the forward functor of an equivalence. -/
instance reflectsIsomorphisms_pushforward_openSubspaceStructureMap :
    (_root_.SheafOfModules.pushforward.{u} (openSubspaceStructureMap U)).ReflectsIsomorphisms :=
  inferInstanceAs ((openSubspaceEquiv U).functor).ReflectsIsomorphisms

/-- **A homomorphism of sheaves of graded algebras on the slice site over `U` is an isomorphism
in degree `n` exactly when it is one on the open subspace.**

This is the bridge the local-to-global step of [Stacks, Tag 0BQY] needs on the invertibility
side: `SheafOfModules.GradedAlgebra.UnitalHom.isIso_app_of_coversTop` asks for invertibility
after restriction to the **slice site** at each member of a cover, while a statement proved by
restricting a ringed space to an open is a statement on the **open subspace**. The two are the
same assertion, because the pushforward along
`Stacks.SheafOfModules.openSubspaceSiteFunctor` is an equivalence. -/
theorem isIso_openSubspaceUnitalHom_app_iff
    {A B : _root_.SheafOfModules.GradedAlgebra.{u, u} ((structureSheafRing X).over U)}
    (g : _root_.SheafOfModules.GradedAlgebra.UnitalHom A B) (n : ℤ) :
    IsIso ((openSubspaceUnitalHom U g).app n) ↔ IsIso (g.app n) :=
  g.isIso_sitePushforward_app_iff (openSubspaceStructureMap U) n

/-- The transport is full, being the forward functor of an equivalence. -/
instance full_pushforward_openSubspaceStructureMap :
    (_root_.SheafOfModules.pushforward.{u} (openSubspaceStructureMap U)).Full :=
  inferInstanceAs ((openSubspaceEquiv U).functor).Full

/-- The transport is faithful, being the forward functor of an equivalence. -/
instance faithful_pushforward_openSubspaceStructureMap :
    (_root_.SheafOfModules.pushforward.{u} (openSubspaceStructureMap U)).Faithful :=
  inferInstanceAs ((openSubspaceEquiv U).functor).Faithful

/-- **The exterior-algebra universal property crosses the identification of the slice site with
the open subspace**, in the direction a local-to-global argument uses: a sheaf of graded
algebras on the slice site over `U` is the exterior algebra of a sheaf of modules there as soon
as its reading on the open subspace is the exterior algebra of the reading of that sheaf of
modules.

This is the one link of the chain of presentations that the local-to-global step of
[Stacks, Tag 0BQY] runs through which changes the site, and the only one at which a universal
property is not carried by degreewise invertibility alone. It is
`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.of_sitePushforward` at
`Stacks.SheafOfModules.openSubspaceStructureMap`, whose three hypotheses are supplied by the
equivalence `Stacks.SheafOfModules.openSubspaceEquiv` and by essential surjectivity of the
functor of sites. -/
theorem isExteriorAlgebra_of_openSubspaceGradedAlgebra
    {A : _root_.SheafOfModules.GradedAlgebra.{u, u} ((structureSheafRing X).over U)}
    {M : _root_.SheafOfModules.{u} ((structureSheafRing X).over U)} {ι : M ⟶ A.piece 1}
    (h : _root_.SheafOfModules.GradedAlgebra.IsExteriorAlgebra (openSubspaceGradedAlgebra U A)
      (_root_.SheafOfModules.GradedAlgebra.genSitePushforward (openSubspaceStructureMap U) ι)) :
    _root_.SheafOfModules.GradedAlgebra.IsExteriorAlgebra A ι :=
  _root_.SheafOfModules.GradedAlgebra.IsExteriorAlgebra.of_sitePushforward
    (openSubspaceStructureMap U) h

/-- **The exterior-algebra universal property at the identity generator crosses the
identification of the slice site with the open subspace.** The form in which the chain of
presentations of [Stacks, Tag 0BQY] uses it: neither the source nor the target sheaf of modules
appears, so this composes with
`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.id_ofDegreewiseIso` at the links that stay on
one site, with no bookkeeping about generators. -/
theorem isExteriorAlgebra_id_of_openSubspaceGradedAlgebra
    (A : _root_.SheafOfModules.GradedAlgebra.{u, u} ((structureSheafRing X).over U))
    (h : _root_.SheafOfModules.GradedAlgebra.IsExteriorAlgebra (openSubspaceGradedAlgebra U A)
      (𝟙 ((openSubspaceGradedAlgebra U A).piece 1))) :
    _root_.SheafOfModules.GradedAlgebra.IsExteriorAlgebra A (𝟙 (A.piece 1)) :=
  _root_.SheafOfModules.GradedAlgebra.IsExteriorAlgebra.id_of_sitePushforward
    (openSubspaceStructureMap U) h

end Stacks.SheafOfModules

end
