module

public import StacksFrontier.AlgebraicGeometry.Modules.TensorOpenSubspaceMulCrossing
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExteriorAlgebra

/-!
# The multiplication of a restricted sheaf of graded algebras, on a local section

`SheafOfModules.openSubspaceAlg A U` is the restriction of a sheaf of graded algebras `A` on a
ringed space `X` to an open subspace `U`, and
`StacksFrontier.AlgebraicGeometry.Modules.TensorOpenSubspaceMulCrossing` identifies its
multiplication with a `PresheafOfModules.tensorSheafDesc` at the restricted pieces, *as an
equation between morphisms*. What a consumer then needs is the same identification **on a local
section**: that the bilinear multiplication of the restricted algebra over `V ⊆ U` is the
bilinear multiplication of `A` over the image of `V` in `X`. The notes of that file record this
step as `rfl` at 664,347 heartbeats, more than three times the budget, and identify it as the
obstruction to the multiplication square.

This file supplies it for **181,218** heartbeats. Nothing clever happens on the ringed space: the
step is factored through the two pushforwards `SheafOfModules.openSubspaceAlg` is built along,
and the content of each is a single `rfl` proved once at a **variable site**, where it costs
13,980.

## Main results

* `SheafOfModules.GradedAlgebra.mulPresheaf_pushforwardAlg_app`: **the bilinear multiplication of
  a pushed-forward sheaf of graded algebras, on a local section over `V`, is the bilinear
  multiplication of the original over `G V`.** At a variable site, where it is `rfl` for 13,980
  heartbeats.
* `SheafOfModules.GradedAlgebra.mulPresheaf_openSubspacePushforward_app_image`: **the
  multiplication of the restriction of `A` to the open subspace `U`, on a local section over
  `V`, is the multiplication of `A` over the image of `V` in `X`** — the step above, at the
  ringed space.
* `SheafOfModules.mulSheaf_openSubspaceAlg_eq_tensorSheafDesc_pushforward`: the multiplication of
  the restricted algebra as a descent, with the bilinear map written at the pushforward spelling
  the result above is stated at. This is
  `SheafOfModules.mulSheaf_openSubspaceAlg_eq_tensorSheafDesc` with the one pin changed, and it
  is what lets a consumer use the two together.
* `SheafOfModules.openSubspaceTensorBifunctorIso_inv_comp_map_mulSheaf`: **the multiplication
  square** — restricting a sheaf of graded algebras to an open subspace commutes with its
  multiplication.
* `PresheafOfModules.hom_app_congr_fun`: equal morphisms of presheaves of modules agree on every
  local section, at a variable site.

## Implementation notes

Every figure is a measurement against the default budget of 200,000 heartbeats, taken on this
branch. No compiler option is set and no heartbeat limit is raised.

| declaration | heartbeats |
| --- | --- |
| `PresheafOfModules.hom_app_congr_fun` | 717 |
| `GradedAlgebra.mulPresheaf_pushforwardAlg_app` | 13,980 |
| `GradedAlgebra.mulPresheaf_over_app` | 9,342 |
| `GradedAlgebra.mulPresheaf_openSubspacePushforward_app` | 9,693 |
| `GradedAlgebra.mulPresheaf_openSubspacePushforward_app_siteFunctor` | 160,649 |
| `GradedAlgebra.mulPresheaf_openSubspacePushforward_app_image` | 181,218 |
| `mulSheaf_openSubspaceAlg_eq_tensorSheafDesc_pushforward` | 10,141 |
| `openSubspaceTensorBifunctorIso_inv_comp_map_mulSheaf` | 151,225 |

**The pushed algebra has to be named at the `toRingCat` spelling of its sheaf of rings.**
`SheafOfModules.GradedAlgebra.pushforwardAlg` produces a graded algebra over
`Stacks.SheafOfModules.PushforwardSheafification.pushforwardRingSheaf`, while
`SheafOfModules.GradedAlgebra.mulPresheaf` — which needs the objectwise tensor product, hence a
sheaf of *commutative* rings — is stated over `toRingCat J O♯`.
`SheafOfModules.GradedAlgebra.pushforwardCommAlg` below is the one ascription that reconciles
them, and it is cheap because it is made once, abstractly. Making it at each use instead leaves
the elaborator the higher-order problem `toRingCat J ?O♯ =?= pushforwardRingSheaf J G R`, which
is where the routes in the table below that fail, fail.

**Pass `O♯` explicitly at every application.** With it left implicit the same higher-order
problem reappears and `isDefEq` runs out of heartbeats: with `O♯` implicit,
`mulPresheaf_openSubspacePushforward_app` exceeds the budget for exactly this reason, and it is
affordable with `(Osharp := X.sheaf.over U)` supplied.

**The two pushforwards must be taken one at a time, and the intermediate algebra must be spelled
`SheafOfModules.GradedAlgebra.over`.** `SheafOfModules.openSubspaceAlg A U` is
`pushforwardAlg` along `Stacks.SheafOfModules.openSubspaceSiteFunctor` of `A.over U`, and
`A.over U` is in turn definitionally a `pushforwardAlg` along `CategoryTheory.Over.forget`
(`rfl`, cheap: the two graded algebras are equal at the doubly-pushed ring spelling). So a
single generic lemma for a *nested* pushforward is available in principle, and it is the route
that does not work:

| route | heartbeats |
| --- | --- |
| nested generic lemma, `rfl` | over budget at `whnf` |
| nested generic lemma, by two applications of the one-step lemma | 160,736 |
| its ringed-space instance, section at the nested spelling | over budget at `whnf` |
| its ringed-space instance, section at the `PresheafOfModules.tensorObj` spelling | over budget |

The reason is the **ring**, not the algebra. Nesting the generic lemma forces the restricted
structure sheaf to be spelled `pushforwardCommRingSheaf _ _ (pushforwardCommRingSheaf _ _ X♯)`,
and retyping a local section of the objectwise tensor product from
`PresheafOfModules.tensorObj (O := (restrictToOpen X U).presheaf) …`
across *that* is over budget — where retyping it across the **single** pushforward of
`X.sheaf.over U` is 6,415. Taking the stages one at a time keeps the inner ring at the
`Sheaf.over` spelling, and every retyping stays cheap.

**The multiplication square, and the one pin it needs.**
`SheafOfModules.openSubspaceTensorBifunctorIso_inv_comp_map_mulSheaf` is the three legs above
composed inside `SheafOfModules.eq_tensorSheafDesc_of_unit_eq`, with
`mulSheaf_openSubspaceAlg_eq_tensorSheafDesc_pushforward` closing the morphism level, for
151,225 heartbeats. The composition is within budget; what it needs is the sheaf of commutative rings of the extensionality supplied as
`(Osharp := (restrictToOpen X U).sheaf)`. Left to be inferred, the application does not reach
the budget at all — instance synthesis fails outright for
`(Opens.grothendieckTopology ↥(restrictToOpen X U).carrier).WEqualsLocallyBijective
AddCommGrpCat` and for the corresponding `CategoryTheory.HasWeakSheafify`, neither of which is a
missing instance: `inferInstance` supplies both on their own at that site, so the failure is one
of elaboration order and the pin fixes it. This is the same discipline recorded above for
`SheafOfModules.GradedAlgebra.mulPresheaf_openSubspacePushforward_app`.

The routes ruled out while the composition was thought to be the obstruction are recorded in the
implementation notes of
`StacksFrontier.AlgebraicGeometry.Modules.TensorOpenSubspaceMulCrossing`; they remain ruled out.
Two of them are worth keeping in view, because they are what makes the shape above the only one
that works: the crossing-and-descent step cannot be split off as its own declaration — putting
`SheafOfModules.GradedAlgebra.mulSheaf`, which is a `PresheafOfModules.tensorSheafDesc` by
definition, inside the composite of a *new* statement is over budget on its own — and the three
legs have to be chained against the square's own goal rather than against an intermediate
right-hand side.

## References

* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Section 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf AlgebraicGeometry Opposite PresheafOfModules
  TopologicalSpace Stacks.SheafOfModules.PushforwardSheafification
open Stacks.Cohomology.HigherDirectImage (restrictToOpen)

universe w v u v' u'

/-! ### Congruence in the morphism, at a variable site -/

namespace PresheafOfModules

/-- Two equal morphisms of presheaves of modules agree on every local section.

Stated at a variable site so that the motive is elaborated there. The sheaf-level analogue is
`SheafOfModules.val_app_congr_fun`; as there, the `_fun` records that this is congruence in the
*morphism* and not in the section. -/
theorem hom_app_congr_fun {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{w}}
    {P Q : PresheafOfModules.{w} R} {f g : P ⟶ Q} (h : f = g) (V : Cᵒᵖ) (x : P.obj V) :
    PresheafOfModules.Hom.app f V x = PresheafOfModules.Hom.app g V x :=
  congrArg (fun φ : P ⟶ Q => PresheafOfModules.Hom.app φ V x) h

end PresheafOfModules

namespace SheafOfModules

/-! ### The multiplication of a pushed-forward sheaf of graded algebras, at a variable site -/

namespace GradedAlgebra

section Generic

variable {Cs : Type u} [Category.{v} Cs] {Ct : Type u'} [Category.{v'} Ct]
  (Js : GrothendieckTopology Cs) {Jt : GrothendieckTopology Ct} (G : Cs ⥤ Ct)
  [G.IsContinuous Js Jt]
  {Osharp : Sheaf Jt CommRingCat.{w}}
  [Jt.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Js.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- **The pushforward of a sheaf of graded algebras along a continuous functor of sites, named at
the `toRingCat` spelling of its sheaf of rings.** `SheafOfModules.GradedAlgebra.pushforwardAlg`
produces a graded algebra over
`Stacks.SheafOfModules.PushforwardSheafification.pushforwardRingSheaf`, and the objectwise tensor
product — hence `SheafOfModules.GradedAlgebra.mulPresheaf` — needs a sheaf of commutative rings;
this is the ascription that reconciles the two, made once and abstractly. See the implementation
notes for what happens when it is made at each use instead. -/
abbrev pushforwardCommAlg (A : GradedAlgebra.{w, w} (toRingCat Jt Osharp)) :
    GradedAlgebra.{w, w}
      (toRingCat Js (Stacks.SheafOfModules.pushforwardCommRingSheaf Js G (Osharp := Osharp))) :=
  GradedAlgebra.pushforwardAlg.{w, w} Js G A

/-- **The bilinear multiplication of a pushed-forward sheaf of graded algebras, on an arbitrary
local section of the objectwise tensor product over `V`, is the bilinear multiplication of the
original over `G V`.** The pushforward leaves the underlying presheaves untouched and the change
of scalars is the identity, so this is `rfl`.

It is stated at a **variable site**, and that is the whole point: 13,980 heartbeats here against
the 664,347 the implementation notes of
`StacksFrontier.AlgebraicGeometry.Modules.TensorOpenSubspaceMulCrossing` record for the same
identification written out at an open subspace. Everything else in this file is two applications
of this one lemma. -/
theorem mulPresheaf_pushforwardAlg_app (A : GradedAlgebra.{w, w} (toRingCat Jt Osharp))
    (i j : ℤ) (V : Csᵒᵖ)
    (z : (tensorObj ((pushforwardCommAlg Js G A).piece i).val
      ((pushforwardCommAlg Js G A).piece j).val).obj V) :
    PresheafOfModules.Hom.app (mulPresheaf (pushforwardCommAlg Js G A) i j) V z =
      PresheafOfModules.Hom.app (mulPresheaf A i j) (G.op.obj V) z :=
  rfl

end Generic

/-! ### The multiplication of a restricted sheaf of graded algebras on a ringed space -/

section RingedSpace

open Stacks.SheafOfModules (openSubspaceSiteFunctor)

variable {X : RingedSpace.{u, u}} (U : Opens X.carrier)
  (A : GradedAlgebra.{u, u} (structureSheafRing X)) (i j : ℤ)

/-- **The multiplication of the slice restriction `A_U` of `A`, on a local section over an object
`W` of the slice site, is the multiplication of `A` over the underlying open.** This is
`SheafOfModules.GradedAlgebra.mulPresheaf_pushforwardAlg_app` along
`CategoryTheory.Over.forget`, which is the functor of sites
`SheafOfModules.GradedAlgebra.over` is the pushforward along. -/
theorem mulPresheaf_over_app (W : (Over U)ᵒᵖ)
    (y : (tensorObj (O := (X.sheaf.over U).obj)
      ((A.over U).piece i).val ((A.over U).piece j).val).obj W) :
    PresheafOfModules.Hom.app (mulPresheaf (Osharp := X.sheaf.over U) (A.over U) i j) W y =
      PresheafOfModules.Hom.app (mulPresheaf A i j) (op W.unop.left) y :=
  mulPresheaf_pushforwardAlg_app _ (Over.forget U) (Osharp := X.sheaf) A i j W y

/-- **The multiplication of the restriction of `A` to the open subspace `U`, on a local section
over `V ⊆ U`, is the multiplication of the slice restriction `A_U` over the image of `V` in the
slice site.** This is `SheafOfModules.GradedAlgebra.mulPresheaf_pushforwardAlg_app` along
`Stacks.SheafOfModules.openSubspaceSiteFunctor`, the outer of the two pushforwards
`SheafOfModules.openSubspaceAlg` is built along. -/
theorem mulPresheaf_openSubspacePushforward_app (V : (Opens ↥U)ᵒᵖ)
    (z : (tensorObj
      ((pushforwardCommAlg (Opens.grothendieckTopology ↥U) (openSubspaceSiteFunctor U)
        (Osharp := X.sheaf.over U) (A.over U)).piece i).val
      ((pushforwardCommAlg (Opens.grothendieckTopology ↥U) (openSubspaceSiteFunctor U)
        (Osharp := X.sheaf.over U) (A.over U)).piece j).val).obj V) :
    PresheafOfModules.Hom.app (mulPresheaf
        (pushforwardCommAlg (Opens.grothendieckTopology ↥U) (openSubspaceSiteFunctor U)
          (Osharp := X.sheaf.over U) (A.over U)) i j) V z =
      PresheafOfModules.Hom.app (mulPresheaf (Osharp := X.sheaf.over U) (A.over U) i j)
        ((openSubspaceSiteFunctor U).op.obj V) z :=
  mulPresheaf_pushforwardAlg_app (Opens.grothendieckTopology ↥U) (openSubspaceSiteFunctor U)
    (Osharp := X.sheaf.over U) (A.over U) i j V z

/-- The two pushforwards composed, with the ambient open spelled through
`Stacks.SheafOfModules.openSubspaceSiteFunctor`. The spelling matters to the bill: naming the
same open as the image of `V` under `U.isOpenEmbedding.functor` costs 20,569 heartbeats more,
and that is `SheafOfModules.GradedAlgebra.mulPresheaf_openSubspacePushforward_app_image`
below. -/
theorem mulPresheaf_openSubspacePushforward_app_siteFunctor (V : (Opens ↥U)ᵒᵖ)
    (z : (tensorObj
      ((pushforwardCommAlg (Opens.grothendieckTopology ↥U) (openSubspaceSiteFunctor U)
        (Osharp := X.sheaf.over U) (A.over U)).piece i).val
      ((pushforwardCommAlg (Opens.grothendieckTopology ↥U) (openSubspaceSiteFunctor U)
        (Osharp := X.sheaf.over U) (A.over U)).piece j).val).obj V) :
    PresheafOfModules.Hom.app (mulPresheaf
        (pushforwardCommAlg (Opens.grothendieckTopology ↥U) (openSubspaceSiteFunctor U)
          (Osharp := X.sheaf.over U) (A.over U)) i j) V z =
      PresheafOfModules.Hom.app (mulPresheaf A i j)
        (op ((openSubspaceSiteFunctor U).obj V.unop).left) z :=
  (mulPresheaf_openSubspacePushforward_app U A i j V z).trans
    (mulPresheaf_over_app U A i j _ z)

/-- **The multiplication of the restriction of `A` to the open subspace `U`, on a local section
over `V ⊆ U`, is the multiplication of `A` over the image of `V` in `X`.**

This is the step the implementation notes of
`StacksFrontier.AlgebraicGeometry.Modules.TensorOpenSubspaceMulCrossing` record as `rfl` at 664,347
heartbeats and call the obstruction to the multiplication square: identifying the small and the
large spelling of one tensor product on a *section*, where the corresponding identification of
*morphisms* is cheap. It is affordable here because nothing is identified at the ringed space at
all: the two pushforwards `SheafOfModules.openSubspaceAlg` is built along are taken one at a
time, and the content of each is
`SheafOfModules.GradedAlgebra.mulPresheaf_pushforwardAlg_app`, a `rfl` proved once at a variable
site. -/
theorem mulPresheaf_openSubspacePushforward_app_image (V : (Opens ↥U)ᵒᵖ)
    (z : (tensorObj
      ((pushforwardCommAlg (Opens.grothendieckTopology ↥U) (openSubspaceSiteFunctor U)
        (Osharp := X.sheaf.over U) (A.over U)).piece i).val
      ((pushforwardCommAlg (Opens.grothendieckTopology ↥U) (openSubspaceSiteFunctor U)
        (Osharp := X.sheaf.over U) (A.over U)).piece j).val).obj V) :
    PresheafOfModules.Hom.app (mulPresheaf
        (pushforwardCommAlg (Opens.grothendieckTopology ↥U) (openSubspaceSiteFunctor U)
          (Osharp := X.sheaf.over U) (A.over U)) i j) V z =
      PresheafOfModules.Hom.app (mulPresheaf A i j)
        (op (U.isOpenEmbedding.functor.obj V.unop)) z :=
  mulPresheaf_openSubspacePushforward_app_siteFunctor U A i j V z

end RingedSpace

end GradedAlgebra

section RingedSpace

open Stacks.SheafOfModules (openSubspaceSiteFunctor)

variable {X : RingedSpace.{u, u}} (U : Opens X.carrier)
  (A : GradedAlgebra.{u, u} (structureSheafRing X)) (i j : ℤ)

/-- **The multiplication of the restricted graded algebra as a descent, with the bilinear map
written at the pushforward spelling.** This is
`SheafOfModules.mulSheaf_openSubspaceAlg_eq_tensorSheafDesc` with the sheaf of commutative rings
of the bilinear map pinned to the pushforward of the slice structure sheaf rather than to the
structure sheaf of the open subspace, which is the spelling
`SheafOfModules.GradedAlgebra.mulPresheaf_openSubspacePushforward_app_image` is stated at. The
two pins are crossed here, at the level of *morphisms*, where this crossing is cheap; crossing
them on a section is what the implementation notes of
`StacksFrontier.AlgebraicGeometry.Modules.TensorOpenSubspaceMulCrossing` measure over budget. -/
theorem mulSheaf_openSubspaceAlg_eq_tensorSheafDesc_pushforward :
    GradedAlgebra.mulSheaf (Osharp := (restrictToOpen X U).sheaf) (openSubspaceAlg A U) i j =
      PresheafOfModules.tensorSheafDesc (Osharp := (restrictToOpen X U).sheaf)
        (F := (openSubspaceRestriction U).obj (A.piece i))
        (G := (openSubspaceRestriction U).obj (A.piece j))
        (Q := (openSubspaceRestriction U).obj (A.piece (i + j)))
        (GradedAlgebra.mulPresheaf
          (GradedAlgebra.pushforwardCommAlg (Opens.grothendieckTopology ↥U)
            (openSubspaceSiteFunctor U) (Osharp := X.sheaf.over U) (A.over U)) i j) :=
  rfl

/-- **The multiplication square: restricting a sheaf of graded algebras to an open subspace
commutes with its multiplication.** Reading the multiplication of `A` on the open subspace `U`
through the identification `(M ⊗ L)|_U ≅ M|_U ⊗ L|_U` gives the multiplication of the restricted
algebra `SheafOfModules.openSubspaceAlg A U`.

Both sides are morphisms out of a tensor product *sheaf*, so they are equal as soon as they agree
on the sheafification unit of a pure tensor
(`SheafOfModules.eq_tensorSheafDesc_of_unit_eq`), and there the three legs are: the crossing of
the identification with the restricted morphism
(`SheafOfModules.openSubspaceTensorBifunctorIso_inv_comp_map_val_app_sheafificationHomEquiv`),
which leaves a morphism out of the *objectwise* tensor product and so never forms a pure tensor
again at the larger site; the identification of that morphism with the bilinear multiplication
(`SheafOfModules.GradedAlgebra.sheafificationHomEquiv_mulSheaf`); and the bilinear
multiplication of the restricted algebra read at the image open
(`SheafOfModules.GradedAlgebra.mulPresheaf_openSubspacePushforward_app_image`).
`SheafOfModules.mulSheaf_openSubspaceAlg_eq_tensorSheafDesc_pushforward` closes the morphism
level.

**The sheaf of commutative rings of the extensionality has to be pinned.** With `O♯` left to be
inferred, the application of `SheafOfModules.eq_tensorSheafDesc_of_unit_eq` does not reach the
budget at all: instance synthesis fails for
`(Opens.grothendieckTopology ↥(restrictToOpen X U).carrier).WEqualsLocallyBijective
AddCommGrpCat` and for the corresponding `CategoryTheory.HasWeakSheafify`, both of which
`inferInstance` supplies on their own. With `(Osharp := (restrictToOpen X U).sheaf)` supplied the
whole composition is 151,225 heartbeats. This is the same discipline the implementation notes
record for `SheafOfModules.GradedAlgebra.mulPresheaf_openSubspacePushforward_app`. -/
theorem openSubspaceTensorBifunctorIso_inv_comp_map_mulSheaf :
    (openSubspaceTensorBifunctorIso U (A.piece i) (A.piece j)).inv ≫
        (openSubspaceRestriction U).map (GradedAlgebra.mulSheaf A i j) =
      GradedAlgebra.mulSheaf (Osharp := (restrictToOpen X U).sheaf) (openSubspaceAlg A U) i j :=
  (eq_tensorSheafDesc_of_unit_eq (Osharp := (restrictToOpen X U).sheaf) _ (fun V _ _ =>
      ((openSubspaceTensorBifunctorIso_inv_comp_map_val_app_sheafificationHomEquiv
            U (A.piece i) (A.piece j) _ (GradedAlgebra.mulSheaf A i j) V _).trans
          (PresheafOfModules.hom_app_congr_fun
            (GradedAlgebra.sheafificationHomEquiv_mulSheaf A i j) _ _)).trans
        (GradedAlgebra.mulPresheaf_openSubspacePushforward_app_image U A i j V _).symm)).trans
    (mulSheaf_openSubspaceAlg_eq_tensorSheafDesc_pushforward U A i j).symm

end RingedSpace

end SheafOfModules

end
