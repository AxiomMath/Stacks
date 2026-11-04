module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModuleUnitCompAbsorption

/-!
# The comparison of the units of étale restriction along a composite

Let `h : D ⟶ A` and `g : A ⟶ C` be étale morphisms of algebraic spaces over a scheme `S` of a big
fppf site `B`.  `AlgebraicGeometry.Space.etaleModulePullbackCompAdjunction` is the adjunction
between étale restriction along `h ≫ g` and the direct image along `h ≫ g` assembled from the two
factors, and `AlgebraicGeometry.Space.etaleModulePullbackAdjunction` of `h ≫ g` is the one taken
along the composite directly.  **The two have the same unit**, which is what this file proves, and
consequently
`AlgebraicGeometry.Space.QuasiCoherentDescent.ModulePullbackCompIsoEtaleRestriction` holds — the
coherence that the descent of quasi-coherent modules along a Zariski covering, Stacks 04W6, is
conditional on.

`StacksFrontier/AlgebraicGeometry/Spaces/EtaleModuleUnitCompLaw.lean`,
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleModulePullbackCompUnit.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleModuleUnitCompAbsorption.lean` supply everything the
comparison rests on: the composite unit at a module is the inner unit there
(`AlgebraicGeometry.Space.etaleModulePullbackCompAdjunction_unit_app_eq_inner`), and the inner
unit on a local section is the unit of étale restriction along `h ≫ g` on that section
(`AlgebraicGeometry.Space.innerUnitVal`).  What is added here is the lift of the second from
sections to the component, and the two retypings that let it be composed with the first.

## Main results

* `AlgebraicGeometry.Space.innerUnit_app_eq_unit_app`: **the inner unit at a module is the unit of
  étale restriction along `h ≫ g` at that module**, the lift of
  `AlgebraicGeometry.Space.innerUnitVal` from sections to the component.
* `AlgebraicGeometry.Space.etaleModulePullbackCompAdjunction_unit_app_eq`: the unit of the
  composite adjunction at a module is the unit of étale restriction along `h ≫ g` there.
* `AlgebraicGeometry.Space.etaleModulePullbackCompAdjunction_unit`: **the two adjunctions of étale
  restriction along a composite have the same unit.**
* `AlgebraicGeometry.Space.modulePullbackCompIsoEtaleRestriction`: consequently the comparison of
  Stacks 03LU is compatible with iterated étale restriction.

## Implementation notes

The spelling discipline is the one the three predecessor files record, with one further observation,
which is what closes the step they leave open.  The target of the inner unit is spelled
`(etaleModulePullback g ⋙ etaleModulePullback h) ⋙ modulePushforward (h ≫ g)` applied to the
module, and the target of the unit along the composite is spelled
`etaleModulePullback (h ≫ g) ⋙ modulePushforward (h ≫ g)` applied to it; the two agree as objects
by `AlgebraicGeometry.Space.innerUnit_target_eq_unit_target`, but a unification that reaches them
through `CategoryTheory.Functor.obj` congruence compares the two *functors* and exhausts the
heartbeat budget.

**Which crossings are affordable.**  A crossing whose two sides are
`(F ⋙ G).obj X` and `G.obj (F'.obj X)` — one side a composite, the other written out — reduces the
`CategoryTheory.Functor.comp` projection first and costs nothing, because the comparison it is
left with is between two applications of the *same* functor constant, which fails by first-order
matching and is then settled by unfolding.  A crossing between two composites
`(F ⋙ G).obj X` and `(F' ⋙ G).obj X` is the fatal one: first-order matching succeeds down to
`F =?= F'`, which is the functor comparison.  So **every intermediate object is written out, never
as a composite**, and the join is carried out at the spelling
`(modulePushforward (h ≫ g)).obj ((etaleModulePullback h).obj ((etaleModulePullback g).obj M))`.

**Each retyping is its own declaration.**  `AlgebraicGeometry.Space.innerUnit_app_eq_unit_app`
composed with a retyping written inline in the same term exhausts the budget, while the same two
steps as two declarations do not: a named constant's type is already instantiated when the next
step reads it, whereas inline the elaborator has both crossings open at once and answers the
second by unfolding.  Hence the chain of four one-step declarations below.

**Why the lift of `innerUnitVal` needs no target at all.**  The predecessor file records that
feeding `AlgebraicGeometry.Space.innerUnitVal` to
`AlgebraicGeometry.Space.modulesHom_ext` with the target module pinned at either spelling of the
unit's target exhausts the budget.  It is not pinned here: the hypothesis is supplied first and
determines both morphisms and the target, and the target it determines is the written-out one.
The same declaration with the target pinned at
`(modulePushforward (h ≫ g)).obj ((etaleModulePullback (h ≫ g)).obj M)` does
not elaborate.

## References

* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 04W6](https://stacks.math.columbia.edu/tag/04W6)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {A C D : AlgebraicSpaces B S hS}
variable (h : D ⟶ A) (g : A ⟶ C) (hh : IsEtale B S hS h.hom) (hg : IsEtale B S hS g.hom)
    (hhg : IsEtale B S hS (h ≫ g).hom)
variable (M : Modules.{u, u} B S hS C.1 C.2)

/-- **The inner unit at a module is the unit of étale restriction along the composite at that
module.**  The lift of `AlgebraicGeometry.Space.innerUnitVal` from local sections to the
component, through `AlgebraicGeometry.Space.modulesHom_ext`.

The target of the two morphisms is the written-out one,
`(modulePushforward (h ≫ g)).obj ((etaleModulePullback h).obj ((etaleModulePullback g).obj M))`:
it is read off the hypothesis rather than pinned, which is what the implementation notes of this
file record. -/
def innerUnit_app_eq_unit_app :=
  modulesHom_ext (N := (modulePushforward B S hS (h ≫ g)).obj
      ((etaleModulePullback.{u, u} B S hS h hh).obj
        ((etaleModulePullback.{u, u} B S hS g hg).obj M)))
    (fun W s => innerUnitVal B S hS h g hh hg hhg M W s)

/-- The unit of the composite adjunction at a module, identified with the inner unit, read at the
written-out spelling of the target. -/
def etaleModulePullbackCompAdjunction_unit_app_eq_inner_nested :=
  Stacks.eq_atType (α := (M ⟶ (modulePushforward B S hS (h ≫ g)).obj
      ((etaleModulePullback.{u, u} B S hS h hh).obj
        ((etaleModulePullback.{u, u} B S hS g hg).obj M))))
    (etaleModulePullbackCompAdjunction_unit_app_eq_inner B S hS h g hh hg hhg M)

/-- The unit of the composite adjunction at a module **is** the unit of étale restriction along
the composite at that module, read at the written-out spelling of the target. -/
def etaleModulePullbackCompAdjunction_unit_app_eq_nested :=
  (etaleModulePullbackCompAdjunction_unit_app_eq_inner_nested B S hS h g hh hg hhg M).trans
    (innerUnit_app_eq_unit_app B S hS h g hh hg hhg M)

/-- The same, read at the spelling the components of the two units carry. -/
def etaleModulePullbackCompAdjunction_unit_app_eq :=
  Stacks.eq_atType (α := (M ⟶ (etaleModulePullback.{u, u} B S hS (h ≫ g) hhg ⋙
      modulePushforward B S hS (h ≫ g)).obj M))
    (etaleModulePullbackCompAdjunction_unit_app_eq_nested B S hS h g hh hg hhg M)

section Unit

/-- **The two adjunctions of étale restriction along a composite have the same unit.**  The
adjunction assembled from the two factors and the comparison of the two direct images, and the
adjunction of étale restriction along the composite, have the same unit. -/
theorem etaleModulePullbackCompAdjunction_unit :
    (etaleModulePullbackCompAdjunction B S hS h g hh hg hhg).unit =
      (etaleModulePullbackAdjunction B S hS (h ≫ g) hhg).unit :=
  NatTrans.ext
    (funext fun N => etaleModulePullbackCompAdjunction_unit_app_eq B S hS h g hh hg hhg N)

end Unit

/-- **The comparison of inverse images along a composite is compatible with étale restriction.**
Reading a section of an iterated inverse image through the comparison of Stacks 03LU is reading it
over the two charts in turn.  This is
`AlgebraicGeometry.Space.modulePullbackCompIsoEtaleRestriction_of_unit` discharged by
`AlgebraicGeometry.Space.etaleModulePullbackCompAdjunction_unit`. -/
theorem modulePullbackCompIsoEtaleRestriction :
    QuasiCoherentDescent.ModulePullbackCompIsoEtaleRestriction B S hS :=
  modulePullbackCompIsoEtaleRestriction_of_unit B S hS
    fun h' g' hh' hg' hhg' => etaleModulePullbackCompAdjunction_unit B S hS h' g' hh' hg' hhg'

end AlgebraicGeometry.Space

end
