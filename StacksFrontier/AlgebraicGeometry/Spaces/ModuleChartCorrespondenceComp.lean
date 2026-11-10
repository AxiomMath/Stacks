module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleChartCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback

/-!
# Composition of linear maps of sections along a morphism of algebraic spaces

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of algebraic spaces over a scheme `S` contained in
a big fppf site `B`.  `AlgebraicGeometry.Space.ModuleFMap`
(`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModuleImageData.lean`) is a linear map of
sections along a morphism, and `AlgebraicGeometry.Space.modulePushforwardHomEquiv`
(`StacksFrontier/AlgebraicGeometry/Spaces/ModuleChartCorrespondence.lean`) is the module-level
chart correspondence of Stacks 03G4 identifying them with morphisms of modules into the direct
image.  This file composes them, and reduces the two composition fields of
`AlgebraicGeometry.Space.ModuleImageData` to a single owed declaration; see the implementation
notes for exactly what is still owed and why.

**Why the set-level composition does not suffice.**
`AlgebraicGeometry.Space.FMap.comp`
(`StacksFrontier/AlgebraicGeometry/Spaces/ChartCorrespondenceComp.lean`) composes `f`-maps of
sheaves of *sets*, and its chart formula `AlgebraicGeometry.Space.FMap.comp_app` holds only on
the chart diagrams over `f ≫ g` that factor through an étale scheme chart of `Y`.  A
`AlgebraicGeometry.Space.ModuleFMap` demands additivity and semilinearity at *every* chart
diagram, so a composite of linear maps of sections cannot be assembled from the set-level
composite together with the chart formula.  The composite is built instead by *module-level
transport*: carry both linear maps across the module chart correspondence, compose the two
morphisms of modules, transport the result along the composition comparison
`AlgebraicGeometry.Space.modulePushforwardCompIso'` of the direct images, and carry it back.
Every field of the resulting `AlgebraicGeometry.Space.ModuleFMap` is then supplied by the chart
correspondence, at every chart diagram, with no factorization hypothesis anywhere.

## Main definitions

* `AlgebraicGeometry.Space.modulePushforwardComp` is the composition comparison
  `AlgebraicGeometry.Space.modulePushforwardCompIso'` of Stacks 03LU, restated for
  `AlgebraicGeometry.Space.modulePushforward` — the functor that carries the Stacks 03LU
  direct-image tag — rather than for the direct image of modules of the morphism of ringed
  topoi.  The two functors are equal by
  `AlgebraicGeometry.Space.pushforwardModules_eq_modulePushforward`, so this is a
  transport along that equality and not a second comparison.
* `AlgebraicGeometry.Space.moduleFMapHomComp` is the morphism of modules into the direct image
  along `f ≫ g` attached to a linear map of sections along `g` and one along `f`: the two
  morphisms of modules the chart correspondence attaches to them, composed, followed by the
  composition comparison.
* `AlgebraicGeometry.Space.ModuleFMap.comp` is **the composite of two linear maps of sections**:
  the linear map of sections along `f ≫ g` which the module chart correspondence attaches to
  `AlgebraicGeometry.Space.moduleFMapHomComp`.
* `AlgebraicGeometry.Space.counitCompIso` is the isomorphism of the direct image along `g` of a
  functor satisfying the chartwise universal property of the direct image along `f` with the
  direct image along `f ≫ g`, and
  `AlgebraicGeometry.Space.modulePushforwardCounitCompEquiv` the bijection of linear maps of
  sections it induces, which by
  `AlgebraicGeometry.Space.modulePushforwardCounitCompEquiv_apply` is composition with the
  counit.
* `AlgebraicGeometry.Space.compCounit` and `AlgebraicGeometry.Space.compHomEquiv` are the counit
  and the universal correspondence of a composite of two functors satisfying the chartwise
  universal property: the data half of the `compositionPresentation` field of
  `AlgebraicGeometry.Space.ModuleImageData`.
* `AlgebraicGeometry.Space.presentationOfEquiv` builds a
  `AlgebraicGeometry.Space.ModulePushforwardPresentation` out of the universal correspondence
  alone, taking the counit to be its value at the identity.  It exists because assembling the
  composite presentation from the counit directly does not pass the kernel; see the
  implementation notes.
* `AlgebraicGeometry.Space.ModulePushforwardPresentation.natIso` upgrades
  `AlgebraicGeometry.Space.ModulePushforwardPresentation.objIso` to an isomorphism of functors.

## Main results

* `AlgebraicGeometry.Space.ModuleFMap.comp_app_precomp`,
  `AlgebraicGeometry.Space.ModuleFMap.comp_middle` and
  `AlgebraicGeometry.Space.ModuleFMap.comp_app_postcomp`: **the composite is functorial in each
  of its three modules.**  These three are the whole content of the composition fields, and they
  replace a chart formula: the counits are compared by moving a morphism of modules from one
  slot of the composite to the next, never by evaluating the composite on a chart diagram.
* `AlgebraicGeometry.Space.ModuleFMap.comp_unique`: **the composite is the only linear map of
  sections whose morphism of modules is the composite of the two morphisms of modules.**  This,
  and not a chart formula, is what pins the composite down; it is the module-level counterpart of
  `AlgebraicGeometry.Space.FMap.comp_unique`.
* `AlgebraicGeometry.Space.compHomEquiv_app`: the composite universal correspondence is
  composition with the composite counit.  This is the `homEquiv_apply` component of the
  composite universal property.
* `AlgebraicGeometry.Space.ModuleFMap.comp_counit_naturality` and
  `AlgebraicGeometry.Space.compCounit_naturality`: **the composite of two counits is natural in
  the module.**  This is the `naturality` component of the composite universal property.
* `AlgebraicGeometry.Space.compHomEquiv_comp` and `AlgebraicGeometry.Space.compHomEquiv_map`:
  those two components in exactly the form `AlgebraicGeometry.Space.presentationOfEquiv`
  consumes.  With these, the `compositionPresentation` field of
  `AlgebraicGeometry.Space.ModuleImageData` is one application of
  `AlgebraicGeometry.Space.presentationOfEquiv` away; see the implementation notes for why that
  application is not made here.
* `AlgebraicGeometry.Space.ModulePushforwardPresentation.objIso_naturality`: the canonical
  isomorphism between two functors satisfying the universal property is natural in the module.
  This is what the `composition` field needs beyond
  `AlgebraicGeometry.Space.ModulePushforwardPresentation.objIso`, which is objectwise.
* `AlgebraicGeometry.Space.ModulePushforwardPresentation.compositionComparison`: **Stacks 03LU,
  the composition comparison normalized by the chartwise universal property.**  A composite of
  direct images is isomorphic, as a functor, to any direct image along the composite, by the
  isomorphism carrying the one counit to the other.  This is the `composition` field of
  `AlgebraicGeometry.Space.ModuleImageData`, with that field's own `compositionPresentation`
  taken as a hypothesis.

## Implementation notes

The whole file rests on two naturality properties of the module chart correspondence, both
immediate from its description: `AlgebraicGeometry.Space.modulePushforwardHomFMap_precomp`
says that precomposing a morphism of modules into the direct image precomposes the linear map of
sections, which is definitional, and
`AlgebraicGeometry.Space.modulePushforwardHomFMap_comp_map` says that postcomposing with the
direct image of a morphism of modules postcomposes it, which is
`AlgebraicGeometry.Space.modulePushforwardCounitApp_map`, naturality of the counit.  Everything
else is those two transported across the bijection and the composition comparison.

The three functoriality lemmas for `AlgebraicGeometry.Space.ModuleFMap.comp` carry their
hypothesis as an equation on components rather than taking a `precomp`/`postcomp` operation on
`AlgebraicGeometry.Space.ModuleFMap` as input.  That is deliberate: the fields of
`AlgebraicGeometry.Space.ModulePushforwardPresentation` are stated on components, so the
component form is what the consumers have in hand, and no further operation on linear maps of
sections has to be defined.

`AlgebraicGeometry.Space.modulePushforwardCounitCompEquiv` is stated for an arbitrary functor
`P` satisfying the universal property of the direct image along `f`, not only for
`AlgebraicGeometry.Space.modulePushforward` itself; that generality is what lets the composite
presentation apply to a value of `AlgebraicGeometry.Space.ModuleImageData` whose `pushforward`
field is some other model of the direct image.  The passage from `P` to
`AlgebraicGeometry.Space.modulePushforward` is
`AlgebraicGeometry.Space.ModulePushforwardPresentation.objIso` against
`AlgebraicGeometry.Space.modulePushforwardPresentation`, so no choice is made.

**What is still owed, and why.**  One declaration, whose statement and whose four inputs are all
here:

```
noncomputable def ModulePushforwardPresentation.comp {f : X ⟶ Y} {g : Y ⟶ Z}
    {P : Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS Y.1 Y.2}
    {Pg : Modules.{u, u} B S hS Y.1 Y.2 ⥤ Modules.{u, u} B S hS Z.1 Z.2}
    (hP : ModulePushforwardPresentation B S hS f P)
    (hPg : ModulePushforwardPresentation B S hS g Pg) :
    ModulePushforwardPresentation B S hS (f ≫ g) (P ⋙ Pg) :=
  presentationOfEquiv B S hS (compHomEquiv B S hS f g hP hPg)
    (compHomEquiv_comp B S hS f g hP hPg)
    (fun a d s ↦ compHomEquiv_map B S hS f g hP hPg a d s)
```

This *elaborates* in 2.4 s — but the **kernel** then rejects it with
`(kernel) deterministic timeout` after about 45 s, against a 2.3 s positive control.  Assembling
the presentation field by field from the four components above fails the same way, at 45 s.
Seven further formulations — wrapping the counit in a structure literal, naming
every component, giving the composite functor and morphism explicitly — each leave it
unchanged.

**The obstruction is structural and not a budget; a raise does not remove it.**  At ten
times the default budget the kernel still reports `(kernel) deterministic timeout`, after 473 s,
and with the budget unbounded there is no verdict after 1000 s.  Raising the budget converts a
timeout into non-termination, so nothing is bought by raising it.

**What the kernel is doing.**  The claim that every argument has as its type exactly
the parameter type *syntactically* is false, and that is the whole story.  The first structural
difference between an argument's inferred type and the parameter type it is checked against is a
**proof term**: the algebraic-space witness `X.2`, spelt
`CategoryTheory.ObjectProperty.FullSubcategory.property` in the argument's type and as a lifted
auxiliary theorem `<the declaration>._proof_1` in the parameter type.  Lean lifts proofs nested
in the *value* of a `def` into auxiliary theorems (`Lean.Meta.abstractNestedProofs`), and
`AlgebraicGeometry.Space.Modules` takes that witness as an argument, so the implicit functor
argument `P ⋙ Pg` of the application carries the lifted copy while each argument's own type
carries `X.2`.  The two are equal but not syntactically equal, so the kernel's structural
shortcut fails and the comparison becomes a full `isDefEq`, which reaches
`AlgebraicGeometry.Space.modulePushforwardCompIso'` and the comparison equivalence of Stacks 03G1,
whose inverse is `CategoryTheory.Functor.objPreimage`, a `Classical.choose`, and diverges there.
That divergence is the one the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModuleCompIso.lean` record from the other side:
it is the symptom, and the lifted proof is the cause.

The bisection that localizes it, each figure against the same 2.3 s control: all three
arguments free, 2.4 s; the morphism and the functor instantiated to `f ≫ g` and `P ⋙ Pg` with the
correspondence still a free variable, 2.4 s; the correspondence alone instantiated to
`AlgebraicGeometry.Space.compHomEquiv`, with *both* proof arguments free, timeout at 47 s; the
same with that correspondence eta-expanded, timeout at 45 s; the eta-reduced partial application
on its own, with no `AlgebraicGeometry.Space.presentationOfEquiv`, 2.3 s.  Consistently with the
diagnosis, `AlgebraicGeometry.Space.presentationOfEquiv` applied to
`AlgebraicGeometry.Space.modulePushforwardHomEquiv` — where the functor argument is a constant
applied to variables, so no proof is lifted — reproduces
`AlgebraicGeometry.Space.modulePushforwardPresentation` in 2.5 s.

**The route that follows, with no `set_option` and no change upstream.**  The proof lift
runs on definitions and not on theorems, so stating the existence first costs nothing:

```
theorem exists_comp (hP : ModulePushforwardPresentation B S hS f P)
    (hPg : ModulePushforwardPresentation B S hS g Pg) :
    ∃ hc : ModulePushforwardPresentation B S hS (f ≫ g) (P ⋙ Pg),
      hc.homEquiv = compHomEquiv B S hS f g hP hPg :=
  ⟨presentationOfEquiv B S hS (compHomEquiv B S hS f g hP hPg)
    (compHomEquiv_comp B S hS f g hP hPg)
    (fun a d s ↦ compHomEquiv_map B S hS f g hP hPg a d s), rfl⟩
```

That, together with `(exists_comp …).choose` as the presentation and `(exists_comp …).choose_spec`
pinning its universal correspondence to `AlgebraicGeometry.Space.compHomEquiv` on the nose,
elaborates and passes the kernel in 2.4 s.  With it, `compositionPresentation` is the `.choose`
and `composition` is
`AlgebraicGeometry.Space.ModulePushforwardPresentation.compositionComparison` applied to it.
Not proved, only inferred: the `counit` field is
determined by `homEquiv` through `homEquiv_apply` at the identity, so the `.choose` is a choice
from a singleton.

**It is not formalized here, and the tag does not ask for it.**  Stacks 03LU is an `equation` in the
source — the display of the two functors `f^*` and `f_*`, whose covering set is
`AlgebraicGeometry.Space.modulePullback` and `AlgebraicGeometry.Space.modulePushforward`, both
tagged — so neither composition field of `AlgebraicGeometry.Space.ModuleImageData` is required by
it.  The route above would add three declarations, one of them a definition.

**Why there is no chart formula here, and where there is one.**  The chart formula for the
composite comes from identifying the underlying `AlgebraicGeometry.Space.FMap` of the composite
with `AlgebraicGeometry.Space.FMap.comp`, after which
`AlgebraicGeometry.Space.FMap.comp_app` applies verbatim.  By
`AlgebraicGeometry.Space.FMap.comp_unique` that identification is one equation of homomorphisms
of sheaves of sets, and by
`AlgebraicGeometry.Space.moduleFMapSetHom_modulePushforwardHomFMap` its left side is the
underlying map of `AlgebraicGeometry.Space.moduleFMapHomComp`.

**That programme has been carried out, in another file and for a composite whose comparison of
direct images is a parameter.**
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleFMapCompChartFormula.lean` defines
`AlgebraicGeometry.Space.ModuleFMap.compOfIso` — the same composite with the comparison `ι`
given as an argument rather than fixed — and proves `AlgebraicGeometry.Space.toFMap_compOfIso`,
the identification with
`AlgebraicGeometry.Space.FMap.comp`, and `AlgebraicGeometry.Space.ModuleFMap.compOfIso_app`, the
chart formula, from one hypothesis on `ι`: that `ι` is the geometric comparison of Stacks 03G2,
part (3), on underlying sheaves of sets.  For the comparison of Stacks 03LU in the form
`AlgebraicGeometry.Space.modulePushforwardCompIso` that hypothesis is
`AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforwardCompIso_hom_app`
(`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardCompIsoSheafTransfer.lean`), and from the
two of them `AlgebraicGeometry.Space.modulePullbackCompIso_hom_val_app_modulePullbackUnitSection`
(`StacksFrontier/AlgebraicGeometry/Spaces/ModulePullbackCompIsoChartSection.lean`) and
`AlgebraicGeometry.Space.moduleFMapEtaleSourceCompCorrespondence`
(`StacksFrontier/AlgebraicGeometry/Spaces/EtaleSourceModuleFMapCompDischarge.lean`) follow.  The
reason the comparison is a parameter there and not a fixed construction is the proof-lifting
obstruction recorded above for the composite presentation.

Of the two lemmas the coherence needs, the second — the substantive half — is stated and proved, for
`modulePushforwardCompIso`; what is still owed *here* is only that this file's own comparison
`AlgebraicGeometry.Space.modulePushforwardComp` has that same property, or equivalently that it
agrees with `modulePushforwardCompIso`.  The two lemmas are:

* **Open.**  The sheaf of sets underlying the direct image of a *morphism* of modules is the
  direct image of the underlying map.
  `AlgebraicGeometry.Space.moduleSheaf_moduleDirectImage`
  (`StacksFrontier/AlgebraicGeometry/Spaces/ModuleDirectImage.lean`) is the statement on objects and
  is `rfl`; the statement on morphisms is its companion, and no file states it.
* **Proved.**  The sheaf of sets underlying `AlgebraicGeometry.Space.modulePushforwardComp` is
  `AlgebraicGeometry.Space.smallToposMorphismTypeU_comp`, the cartesian comparison of
  Stacks 03G2, part (3).  This is the substantive half, and it is
  `AlgebraicGeometry.Space.moduleSheafFunctor_map_compIsoCongr_hom_app`
  (`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsComp.lean`), at a general module and
  carrying the Stacks 03LU clause "the composition comparison for direct images is the geometric
  comparison".  `AlgebraicGeometry.Space.modulePushforwardCompIso_hom_app_val_app`
  (`StacksFrontier/AlgebraicGeometry/Spaces/ModulePullbackChartSectionCoherence.lean`) is the same
  clause read on a section, and
  `AlgebraicGeometry.Space.modulePushforwardCounitApp_smallToposMorphismTypeU_comp` there is the
  chart formula it gives for the chart components of the direct image.

A second, purely bookkeeping obstacle to stating that coherence *here*:
`StacksFrontier.AlgebraicGeometry.Spaces.ChartCorrespondenceComp` is **not** in this file's import
closure, so `AlgebraicGeometry.Space.FMap.comp` does not resolve in this file at all — a bare
`FMap.comp` silently resolves to `Function.comp` instead.  Every reference to it above is prose.
Whoever adds the coherence must add that import.

Until those exist, `AlgebraicGeometry.Space.ModuleFMap.comp` is characterized by
`AlgebraicGeometry.Space.ModuleFMap.comp_unique` and by its three functoriality lemmas, and that
is all it is characterized by.  The composition fields of Stacks 03LU need no more than that.

Three further elaboration constraints, none needing a raised budget.  First,
`AlgebraicGeometry.Space.modulePushforwardCounitCompEquiv` is given as an explicit pair of
functions rather than as a composite of the module chart correspondence at `g`,
`CategoryTheory.Iso.homCongr` and the module chart correspondence at `f ≫ g`: in the composite
form, identifying its forward direction with `AlgebraicGeometry.Space.ModuleFMap.comp` needs
`CategoryTheory.Category.id_comp` and then a `rfl`, and the kernel exceeds its budget on the
resulting term.  Second, even in the explicit form that identification is not reachable by
`rfl`, although it holds by beta reduction alone: `rfl` diverges in `isDefEq` at five times the
default budget, for the same reason as above.  What works, and instantly, is `unfold` followed by
`rw [Equiv.coe_fn_mk]`: the projection is discharged by Mathlib's own lemma, stated at free
variables, so nothing is unfolded.  Third, and generally: **two occurrences of
`AlgebraicGeometry.Space.ModuleFMap.comp` must never be handed to the unifier unless they are
syntactically equal.**  Where a proof needs to change the argument of `(compCounit …).app d`, the
step must be `congrArg ((compCounit …).app d) (rfl : _ = _)` with the function *eta-reduced* —
`Eq.trans` of two `AlgebraicGeometry.Space.compHomEquiv_app`s, and `congrArg` with a lambda
instead of the eta-reduced projection, both diverge where this is instant.

The module universe is the universe `u` of the structure rings, not a free one, for the reason
recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModuleImageData.lean`:
`AlgebraicGeometry.Space.modulePushforward` is declared only as a functor
`Modules.{u, u} ⥤ Modules.{u, u}`, because the direct image of modules applies the direct image
of sheaves of *sets*, which on these sites exists only at `Type u`.

No declaration here carries a `@[stacks]` attribute, and none is owed one.  Stacks 03LU is a
displayed *equation* introducing the two functors `f^*` and `f_*`; its covering set is
`AlgebraicGeometry.Space.modulePullback`
(`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullback.lean`) and
`AlgebraicGeometry.Space.modulePushforward`
(`StacksFrontier/AlgebraicGeometry/Spaces/StructureMapSharp.lean`), both of which carry the tag with
a part-string.  The adjointness and the two composition identities of the same paragraph of the
source are carried by `AlgebraicGeometry.Space.modulePullbackAdjPushforward`
(`StacksFrontier/AlgebraicGeometry/Spaces/PushforwardPresentationExact.lean`) and by
`AlgebraicGeometry.Space.modulePushforwardCompIso'` and
`AlgebraicGeometry.Space.modulePullbackCompIso`
(`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModuleCompIso.lean`).  Nothing in this file is
part of that covering set: the two `AlgebraicGeometry.Space.ModuleImageData` composition fields
are a bundle of this development's own, beyond what the equation asserts, so a tag here would
overclaim.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G4](https://stacks.math.columbia.edu/tag/03G4)
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : AlgebraicSpaces B S hS}

/-! ### Naturality of the module chart correspondence -/

/-- Precomposing a morphism of modules into the direct image precomposes the linear map of
sections it corresponds to.  This is definitional: the correspondence is composition with the
counit. -/
theorem modulePushforwardHomFMap_precomp (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    (G G' : Modules.{u, u} B S hS Y.1 Y.2) (a : G' ⟶ G)
    (c : G ⟶ (modulePushforward B S hS f).obj F)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) (s : G'.val.obj (op d.V)) :
    (modulePushforwardHomFMap B S hS f F G' (a ≫ c)).app d s =
      (modulePushforwardHomFMap B S hS f F G c).app d (a.val.app (op d.V) s) := rfl

/-- Postcomposing a morphism of modules into the direct image with the direct image of a morphism
of modules postcomposes the linear map of sections it corresponds to.  This is naturality of the
counit, `AlgebraicGeometry.Space.modulePushforwardCounitApp_map`. -/
theorem modulePushforwardHomFMap_comp_map (f : X ⟶ Y)
    {F F' : Modules.{u, u} B S hS X.1 X.2} (a : F ⟶ F')
    (G : Modules.{u, u} B S hS Y.1 Y.2)
    (c : G ⟶ (modulePushforward B S hS f).obj F)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) (s : G.val.obj (op d.V)) :
    (modulePushforwardHomFMap B S hS f F' G
          (c ≫ (modulePushforward B S hS f).map a)).app d s =
      a.val.app (op d.U) ((modulePushforwardHomFMap B S hS f F G c).app d s) :=
  modulePushforwardCounitApp_map B S hS f a d (c.val.app (op d.V) s)

/-- The two directions of the module chart correspondence are mutually inverse, in the direction
that recovers a linear map of sections from its morphism of modules. -/
theorem modulePushforwardHomFMap_moduleFMapHom (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (G : Modules.{u, u} B S hS Y.1 Y.2)
    (ξ : ModuleFMap B S hS f F G) :
    modulePushforwardHomFMap B S hS f F G (moduleFMapHom B S hS f F G ξ) = ξ :=
  (modulePushforwardHomEquiv B S hS f F G).apply_symm_apply ξ

/-- A linear map of sections is attached to a morphism of modules as soon as the morphism of
modules gives rise to it componentwise. -/
private theorem moduleFMapHom_eq_of_app_eq (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    (G : Modules.{u, u} B S hS Y.1 Y.2) (ξ : ModuleFMap B S hS f F G)
    (c : G ⟶ (modulePushforward B S hS f).obj F)
    (h : ∀ (d : ChartDiagram B S hS X.1 Y.1 f.hom) (s : G.val.obj (op d.V)),
      (modulePushforwardHomFMap B S hS f F G c).app d s = ξ.app d s) :
    moduleFMapHom B S hS f F G ξ = c :=
  (modulePushforwardHomEquiv B S hS f F G).symm_apply_eq.mpr
    (ModuleFMap.ext B S hS (funext fun d ↦ funext (h d))).symm

/-- The morphism of modules attached to a linear map of sections precomposed with a morphism of
modules on the target is that morphism followed by the morphism of modules attached to the
original. -/
theorem moduleFMapHom_precomp (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    {G G' : Modules.{u, u} B S hS Y.1 Y.2} (a : G' ⟶ G)
    (ξ : ModuleFMap B S hS f F G) (ξ' : ModuleFMap B S hS f F G')
    (h : ∀ (d : ChartDiagram B S hS X.1 Y.1 f.hom) (s : G'.val.obj (op d.V)),
      ξ'.app d s = ξ.app d (a.val.app (op d.V) s)) :
    moduleFMapHom B S hS f F G' ξ' = a ≫ moduleFMapHom B S hS f F G ξ :=
  moduleFMapHom_eq_of_app_eq B S hS f F G' ξ' _ fun d s ↦
    (modulePushforwardHomFMap_precomp B S hS f F G G' a _ d s).trans
      ((congrArg (fun ζ : ModuleFMap B S hS f F G ↦ ζ.app d (a.val.app (op d.V) s))
        (modulePushforwardHomFMap_moduleFMapHom B S hS f F G ξ)).trans (h d s).symm)

/-- The morphism of modules attached to a linear map of sections postcomposed with a morphism of
modules on the source is the morphism of modules attached to the original, followed by its direct
image. -/
theorem moduleFMapHom_postcomp (f : X ⟶ Y)
    {F F' : Modules.{u, u} B S hS X.1 X.2} (a : F ⟶ F')
    (G : Modules.{u, u} B S hS Y.1 Y.2)
    (η : ModuleFMap B S hS f F G) (η' : ModuleFMap B S hS f F' G)
    (h : ∀ (d : ChartDiagram B S hS X.1 Y.1 f.hom) (s : G.val.obj (op d.V)),
      η'.app d s = a.val.app (op d.U) (η.app d s)) :
    moduleFMapHom B S hS f F' G η' =
      moduleFMapHom B S hS f F G η ≫ (modulePushforward B S hS f).map a :=
  moduleFMapHom_eq_of_app_eq B S hS f F' G η' _ fun d s ↦
    (modulePushforwardHomFMap_comp_map B S hS f a G _ d s).trans
      ((congrArg (fun ζ : ModuleFMap B S hS f F G ↦ a.val.app (op d.U) (ζ.app d s))
        (modulePushforwardHomFMap_moduleFMapHom B S hS f F G η)).trans (h d s).symm)

/-! ### The composite of two linear maps of sections -/

/-- The morphism of modules from `H` into the direct image of `F` along `f ≫ g` attached to a
linear map of sections along `g` from `G` to `H` and one along `f` from `F` to `G`: the morphism
of modules of the first, followed by the direct image along `g` of the morphism of modules of the
second, followed by the composition comparison of the direct images. -/
noncomputable def moduleFMapHomComp (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) (G : Modules.{u, u} B S hS Y.1 Y.2)
    (H : Modules.{u, u} B S hS Z.1 Z.2)
    (ξ : ModuleFMap B S hS g G H) (η : ModuleFMap B S hS f F G) :
    H ⟶ (modulePushforward B S hS (f ≫ g)).obj F :=
  moduleFMapHom B S hS g G H ξ ≫
    (modulePushforward B S hS g).map (moduleFMapHom B S hS f F G η) ≫
    (modulePushforwardCompIso B S hS f g).hom.app F

/-- **The composite of two linear maps of sections.**  Given a linear map of sections along
`g : Y ⟶ Z` from `G` to `H` and one along `f : X ⟶ Y` from `F` to `G`, the linear map of sections
along `f ≫ g` from `F` to `H` which the module chart correspondence of Stacks 03G4 attaches to
`AlgebraicGeometry.Space.moduleFMapHomComp`.

It is not given chart diagram by chart diagram, and cannot be: the vertical scheme morphism of a
chart diagram over `f ≫ g` need not factor through an étale scheme chart of `Y`, while
additivity and semilinearity are demanded at every chart diagram.  Transporting the composite of
the two morphisms of modules supplies all four fields at once.

What pins it down is `AlgebraicGeometry.Space.ModuleFMap.comp_unique`: it is the unique linear
map of sections whose morphism of modules is the composite.  Its functoriality in each of the
three modules — `AlgebraicGeometry.Space.ModuleFMap.comp_app_precomp`,
`AlgebraicGeometry.Space.ModuleFMap.comp_middle`,
`AlgebraicGeometry.Space.ModuleFMap.comp_app_postcomp` — is what the composition fields of
Stacks 03LU consume.  **Two things are deliberately not proved here**, and the name should be
read against them: there is no chart formula, i.e. no statement that on a chart diagram over
`f ≫ g` which does factor through a chart of `Y` the components compose, and no identification
of the underlying `AlgebraicGeometry.Space.FMap` with
`AlgebraicGeometry.Space.FMap.comp`.  Either would follow from the other, since
`AlgebraicGeometry.Space.FMap.comp_app` is the chart formula at the level of sheaves of sets;
what blocks both is recorded in the implementation notes of this file.

The argument order is outer-first, matching `AlgebraicGeometry.Space.FMap.comp`. -/
noncomputable def ModuleFMap.comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) (G : Modules.{u, u} B S hS Y.1 Y.2)
    (H : Modules.{u, u} B S hS Z.1 Z.2)
    (ξ : ModuleFMap B S hS g G H) (η : ModuleFMap B S hS f F G) :
    ModuleFMap B S hS (f ≫ g) F H :=
  modulePushforwardHomFMap B S hS (f ≫ g) F H
    (moduleFMapHomComp B S hS f g F G H ξ η)

/-- `AlgebraicGeometry.Space.ModuleFMap.comp` is the *only* linear map of sections along `f ≫ g`
whose morphism of modules into the direct image is the composite of the two morphisms of modules:
the module chart correspondence is a bijection, so the composite is a characterization and not a
choice.  This is the module-level counterpart of
`AlgebraicGeometry.Space.FMap.comp_unique`. -/
theorem ModuleFMap.comp_unique (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) (G : Modules.{u, u} B S hS Y.1 Y.2)
    (H : Modules.{u, u} B S hS Z.1 Z.2)
    (ξ : ModuleFMap B S hS g G H) (η : ModuleFMap B S hS f F G)
    (θ : ModuleFMap B S hS (f ≫ g) F H)
    (h : moduleFMapHom B S hS (f ≫ g) F H θ =
      moduleFMapHomComp B S hS f g F G H ξ η) :
    θ = ModuleFMap.comp B S hS f g F G H ξ η :=
  (modulePushforwardHomFMap_moduleFMapHom B S hS (f ≫ g) F H θ).symm.trans
    (congrArg (modulePushforwardHomFMap B S hS (f ≫ g) F H) h)

/-! ### Functoriality of the composite -/

/-- Precomposing the outer linear map of sections with a morphism of modules on `Z` precomposes
the morphism of modules of the composite. -/
theorem moduleFMapHomComp_precomp (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) (G : Modules.{u, u} B S hS Y.1 Y.2)
    {H H' : Modules.{u, u} B S hS Z.1 Z.2} (b : H' ⟶ H)
    (ξ : ModuleFMap B S hS g G H) (ξ' : ModuleFMap B S hS g G H')
    (h : ∀ (e : ChartDiagram B S hS Y.1 Z.1 g.hom) (t : H'.val.obj (op e.V)),
      ξ'.app e t = ξ.app e (b.val.app (op e.V) t))
    (η : ModuleFMap B S hS f F G) :
    moduleFMapHomComp B S hS f g F G H' ξ' η =
      b ≫ moduleFMapHomComp B S hS f g F G H ξ η := by
  unfold moduleFMapHomComp
  rw [moduleFMapHom_precomp B S hS g G b ξ ξ' h, Category.assoc]

/-- Moving a morphism of modules on `Y` from the source of the outer linear map of sections to
the target of the inner one does not change the morphism of modules of the composite. -/
theorem moduleFMapHomComp_middle (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) {G G' : Modules.{u, u} B S hS Y.1 Y.2}
    (A : G ⟶ G') (H : Modules.{u, u} B S hS Z.1 Z.2)
    (ξ : ModuleFMap B S hS g G H) (ξ' : ModuleFMap B S hS g G' H)
    (hξ : ∀ (e : ChartDiagram B S hS Y.1 Z.1 g.hom) (t : H.val.obj (op e.V)),
      ξ'.app e t = A.val.app (op e.U) (ξ.app e t))
    (η : ModuleFMap B S hS f F G') (η' : ModuleFMap B S hS f F G)
    (hη : ∀ (d : ChartDiagram B S hS X.1 Y.1 f.hom) (s : G.val.obj (op d.V)),
      η'.app d s = η.app d (A.val.app (op d.V) s)) :
    moduleFMapHomComp B S hS f g F G' H ξ' η =
      moduleFMapHomComp B S hS f g F G H ξ η' := by
  unfold moduleFMapHomComp
  rw [moduleFMapHom_postcomp B S hS g A H ξ ξ' hξ,
    moduleFMapHom_precomp B S hS f F A η η' hη, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]

/-- Postcomposing the inner linear map of sections with a morphism of modules on `X` postcomposes
the morphism of modules of the composite with its direct image along `f ≫ g`: this is naturality
of the composition comparison. -/
theorem moduleFMapHomComp_postcomp (f : X ⟶ Y) (g : Y ⟶ Z)
    {F F' : Modules.{u, u} B S hS X.1 X.2} (a : F ⟶ F')
    (G : Modules.{u, u} B S hS Y.1 Y.2) (H : Modules.{u, u} B S hS Z.1 Z.2)
    (ξ : ModuleFMap B S hS g G H)
    (η : ModuleFMap B S hS f F G) (η' : ModuleFMap B S hS f F' G)
    (h : ∀ (d : ChartDiagram B S hS X.1 Y.1 f.hom) (s : G.val.obj (op d.V)),
      η'.app d s = a.val.app (op d.U) (η.app d s)) :
    moduleFMapHomComp B S hS f g F' G H ξ η' =
      moduleFMapHomComp B S hS f g F G H ξ η ≫
        (modulePushforward B S hS (f ≫ g)).map a := by
  unfold moduleFMapHomComp
  rw [moduleFMapHom_postcomp B S hS f a G η η' h, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  exact congrArg (fun m ↦ moduleFMapHom B S hS g G H ξ ≫
      (modulePushforward B S hS g).map (moduleFMapHom B S hS f F G η) ≫ m)
    ((modulePushforwardCompIso B S hS f g).hom.naturality a)

/-- **The composite is contravariantly functorial in the target module.**  Precomposing the outer
linear map of sections with a morphism of modules on `Z` precomposes the composite. -/
theorem ModuleFMap.comp_app_precomp (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) (G : Modules.{u, u} B S hS Y.1 Y.2)
    {H H' : Modules.{u, u} B S hS Z.1 Z.2} (b : H' ⟶ H)
    (ξ : ModuleFMap B S hS g G H) (ξ' : ModuleFMap B S hS g G H')
    (h : ∀ (e : ChartDiagram B S hS Y.1 Z.1 g.hom) (t : H'.val.obj (op e.V)),
      ξ'.app e t = ξ.app e (b.val.app (op e.V) t))
    (η : ModuleFMap B S hS f F G)
    (d : ChartDiagram B S hS X.1 Z.1 (f ≫ g).hom) (s : H'.val.obj (op d.V)) :
    (ModuleFMap.comp B S hS f g F G H' ξ' η).app d s =
      (ModuleFMap.comp B S hS f g F G H ξ η).app d (b.val.app (op d.V) s) := by
  unfold ModuleFMap.comp
  rw [moduleFMapHomComp_precomp B S hS f g F G b ξ ξ' h η]
  exact modulePushforwardHomFMap_precomp B S hS (f ≫ g) F H H' b _ d s

/-- **The composite does not see where the middle module morphism sits.**  Moving a morphism of
modules on `Y` from the source of the outer linear map of sections to the target of the inner one
leaves the composite unchanged.  This is the step that compares the counit of a composite of
direct images at two different modules. -/
theorem ModuleFMap.comp_middle (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) {G G' : Modules.{u, u} B S hS Y.1 Y.2}
    (A : G ⟶ G') (H : Modules.{u, u} B S hS Z.1 Z.2)
    (ξ : ModuleFMap B S hS g G H) (ξ' : ModuleFMap B S hS g G' H)
    (hξ : ∀ (e : ChartDiagram B S hS Y.1 Z.1 g.hom) (t : H.val.obj (op e.V)),
      ξ'.app e t = A.val.app (op e.U) (ξ.app e t))
    (η : ModuleFMap B S hS f F G') (η' : ModuleFMap B S hS f F G)
    (hη : ∀ (d : ChartDiagram B S hS X.1 Y.1 f.hom) (s : G.val.obj (op d.V)),
      η'.app d s = η.app d (A.val.app (op d.V) s)) :
    ModuleFMap.comp B S hS f g F G' H ξ' η = ModuleFMap.comp B S hS f g F G H ξ η' :=
  congrArg (modulePushforwardHomFMap B S hS (f ≫ g) F H)
    (moduleFMapHomComp_middle B S hS f g F A H ξ ξ' hξ η η' hη)

/-- **The composite is covariantly functorial in the source module.**  Postcomposing the inner
linear map of sections with a morphism of modules on `X` postcomposes the composite. -/
theorem ModuleFMap.comp_app_postcomp (f : X ⟶ Y) (g : Y ⟶ Z)
    {F F' : Modules.{u, u} B S hS X.1 X.2} (a : F ⟶ F')
    (G : Modules.{u, u} B S hS Y.1 Y.2) (H : Modules.{u, u} B S hS Z.1 Z.2)
    (ξ : ModuleFMap B S hS g G H)
    (η : ModuleFMap B S hS f F G) (η' : ModuleFMap B S hS f F' G)
    (h : ∀ (d : ChartDiagram B S hS X.1 Y.1 f.hom) (s : G.val.obj (op d.V)),
      η'.app d s = a.val.app (op d.U) (η.app d s))
    (d : ChartDiagram B S hS X.1 Z.1 (f ≫ g).hom) (s : H.val.obj (op d.V)) :
    (ModuleFMap.comp B S hS f g F' G H ξ η').app d s =
      a.val.app (op d.U) ((ModuleFMap.comp B S hS f g F G H ξ η).app d s) := by
  unfold ModuleFMap.comp
  rw [moduleFMapHomComp_postcomp B S hS f g a G H ξ η η' h]
  exact modulePushforwardHomFMap_comp_map B S hS (f ≫ g) a H _ d s

/-! ### The composite counit as a bijection -/

/-- The direct image along `g` of a functor satisfying the chartwise universal property of the
direct image along `f`, compared with the direct image along `f ≫ g`: the direct image along `g`
of the canonical isomorphism of `AlgebraicGeometry.Space.ModulePushforwardPresentation.objIso`,
followed by the composition comparison. -/
noncomputable def counitCompIso (f : X ⟶ Y) (g : Y ⟶ Z)
    {P : Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS Y.1 Y.2}
    (hP : ModulePushforwardPresentation B S hS f P)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (modulePushforward B S hS g).obj (P.obj F) ≅
      (modulePushforward B S hS (f ≫ g)).obj F :=
  (modulePushforward B S hS g).mapIso
      (ModulePushforwardPresentation.objIso B S hS hP
        (modulePushforwardPresentation B S hS f) F) ≪≫
    (modulePushforwardCompIso B S hS f g).app F

/-- The comparison of `AlgebraicGeometry.Space.counitCompIso` is the direct image along `g` of
the morphism of modules attached to the counit, followed by the composition comparison. -/
theorem counitCompIso_hom (f : X ⟶ Y) (g : Y ⟶ Z)
    {P : Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS Y.1 Y.2}
    (hP : ModulePushforwardPresentation B S hS f P)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (counitCompIso B S hS f g hP F).hom =
      (modulePushforward B S hS g).map
          (moduleFMapHom B S hS f F (P.obj F) (hP.counit F)) ≫
        (modulePushforwardCompIso B S hS f g).hom.app F := rfl

/-- The two directions of the module chart correspondence are mutually inverse, in the direction
that recovers a morphism of modules from its linear map of sections. -/
theorem moduleFMapHom_modulePushforwardHomFMap (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (G : Modules.{u, u} B S hS Y.1 Y.2)
    (c : G ⟶ (modulePushforward B S hS f).obj F) :
    moduleFMapHom B S hS f F G (modulePushforwardHomFMap B S hS f F G c) = c :=
  (modulePushforwardHomEquiv B S hS f F G).symm_apply_apply c

/-- The morphism of modules of a composite whose inner factor is the counit is the morphism of
modules of the outer factor, followed by `AlgebraicGeometry.Space.counitCompIso`. -/
theorem moduleFMapHomComp_counit (f : X ⟶ Y) (g : Y ⟶ Z)
    {P : Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS Y.1 Y.2}
    (hP : ModulePushforwardPresentation B S hS f P)
    (F : Modules.{u, u} B S hS X.1 X.2) (H : Modules.{u, u} B S hS Z.1 Z.2)
    (ξ : ModuleFMap B S hS g (P.obj F) H) :
    moduleFMapHomComp B S hS f g F (P.obj F) H ξ (hP.counit F) =
      moduleFMapHom B S hS g (P.obj F) H ξ ≫ (counitCompIso B S hS f g hP F).hom :=
  (congrArg (fun m ↦ moduleFMapHom B S hS g (P.obj F) H ξ ≫ m)
    (counitCompIso_hom B S hS f g hP F)).symm

/-- **Composition with the counit of the direct image along `f` is a bijection.**  Linear maps of
sections along `g` out of a functor satisfying the chartwise universal property of the direct
image along `f` are exactly linear maps of sections along `f ≫ g` out of the module, the
bijection being `AlgebraicGeometry.Space.ModuleFMap.comp` with the counit.

That it is a bijection is the module chart correspondence at `g`, the isomorphism
`AlgebraicGeometry.Space.counitCompIso`, and the module chart correspondence at `f ≫ g`, run in
succession; the inverse is written out rather than assembled from those three so that the forward
direction is composition with the counit on the nose. -/
noncomputable def modulePushforwardCounitCompEquiv (f : X ⟶ Y) (g : Y ⟶ Z)
    {P : Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS Y.1 Y.2}
    (hP : ModulePushforwardPresentation B S hS f P)
    (F : Modules.{u, u} B S hS X.1 X.2) (H : Modules.{u, u} B S hS Z.1 Z.2) :
    ModuleFMap B S hS g (P.obj F) H ≃ ModuleFMap B S hS (f ≫ g) F H where
  toFun ξ := ModuleFMap.comp B S hS f g F (P.obj F) H ξ (hP.counit F)
  invFun ζ := modulePushforwardHomFMap B S hS g (P.obj F) H
    (moduleFMapHom B S hS (f ≫ g) F H ζ ≫ (counitCompIso B S hS f g hP F).inv)
  left_inv ξ := by
    refine Eq.trans (congrArg (fun c ↦ modulePushforwardHomFMap B S hS g (P.obj F) H
      (c ≫ (counitCompIso B S hS f g hP F).inv))
      (Eq.trans (moduleFMapHom_modulePushforwardHomFMap B S hS (f ≫ g) F H
          (moduleFMapHomComp B S hS f g F (P.obj F) H ξ (hP.counit F)))
        (moduleFMapHomComp_counit B S hS f g hP F H ξ))) ?_
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact modulePushforwardHomFMap_moduleFMapHom B S hS g (P.obj F) H ξ
  right_inv ζ := by
    refine Eq.trans (congrArg (modulePushforwardHomFMap B S hS (f ≫ g) F H)
      (Eq.trans (moduleFMapHomComp_counit B S hS f g hP F H _)
        (congrArg (fun c ↦ c ≫ (counitCompIso B S hS f g hP F).hom)
          (moduleFMapHom_modulePushforwardHomFMap B S hS g (P.obj F) H _)))) ?_
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact modulePushforwardHomFMap_moduleFMapHom B S hS (f ≫ g) F H ζ

/-- The bijection of `AlgebraicGeometry.Space.modulePushforwardCounitCompEquiv` *is* composition
with the counit of the direct image along `f`. -/
theorem modulePushforwardCounitCompEquiv_apply (f : X ⟶ Y) (g : Y ⟶ Z)
    {P : Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS Y.1 Y.2}
    (hP : ModulePushforwardPresentation B S hS f P)
    (F : Modules.{u, u} B S hS X.1 X.2) (H : Modules.{u, u} B S hS Z.1 Z.2)
    (ξ : ModuleFMap B S hS g (P.obj F) H) :
    modulePushforwardCounitCompEquiv B S hS f g hP F H ξ =
      ModuleFMap.comp B S hS f g F (P.obj F) H ξ (hP.counit F) := by
  unfold modulePushforwardCounitCompEquiv
  rw [Equiv.coe_fn_mk]

/-! ### A constructor for the chartwise universal property -/

/-- The chartwise universal property of the direct image, built from the universal
correspondence alone.

Three components are asked for rather than the structure's four: the counit is *derived*, as the
correspondence at the identity, and the structure's `homEquiv_apply` and `naturality` fields are
then derived from `homEquiv_comp` at `a ≫ 𝟙` and from `homEquiv_comp` together with
`homEquiv_map`.  So this is not the structure's constructor re-spelled; deriving the counit is
what makes the two component hypotheses mention the correspondence only.

**What it does and does not get past the kernel.**  Applied to
`AlgebraicGeometry.Space.modulePushforwardHomEquiv` it reproduces
`AlgebraicGeometry.Space.modulePushforwardPresentation` in 2.5 s.  Applied to
`AlgebraicGeometry.Space.compHomEquiv` it times out in the kernel inside a *definition* and does
not inside a *theorem*; the implementation notes of this file record the cause — a proof lifted
out of the definition's value — and the route that follows from it.  So this constructor has no
consumer in this file; it is kept because it is the shape in which the owed declaration is
written. -/
noncomputable def presentationOfEquiv {k : X ⟶ Z}
    {R : Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS Z.1 Z.2}
    (homEquiv : ∀ (F : Modules.{u, u} B S hS X.1 X.2)
      (N : Modules.{u, u} B S hS Z.1 Z.2), (N ⟶ R.obj F) ≃ ModuleFMap B S hS k F N)
    (homEquiv_comp : ∀ (F : Modules.{u, u} B S hS X.1 X.2)
      (N N' : Modules.{u, u} B S hS Z.1 Z.2) (b : N' ⟶ N) (a : N ⟶ R.obj F)
      (d : ChartDiagram B S hS X.1 Z.1 k.hom) (s : N'.val.obj (op d.V)),
      (homEquiv F N' (b ≫ a)).app d s =
        (homEquiv F N a).app d (b.val.app (op d.V) s))
    (homEquiv_map : ∀ {F F' : Modules.{u, u} B S hS X.1 X.2} (a : F ⟶ F')
      (d : ChartDiagram B S hS X.1 Z.1 k.hom) (s : (R.obj F).val.obj (op d.V)),
      (homEquiv F' (R.obj F) (R.map a)).app d s =
        a.val.app (op d.U) ((homEquiv F (R.obj F) (𝟙 (R.obj F))).app d s)) :
    ModulePushforwardPresentation B S hS k R where
  counit F := homEquiv F (R.obj F) (𝟙 (R.obj F))
  homEquiv F N := homEquiv F N
  homEquiv_apply F N a d s :=
    (congrArg (fun c : N ⟶ R.obj F ↦ (homEquiv F N c).app d s)
        (Category.comp_id a).symm).trans
      (homEquiv_comp F (R.obj F) N a (𝟙 (R.obj F)) d s)
  naturality {F F'} a d s :=
    (((homEquiv_comp F' (R.obj F') (R.obj F) (R.map a) (𝟙 (R.obj F')) d s).symm).trans
        (congrArg (fun c : R.obj F ⟶ R.obj F' ↦ (homEquiv F' (R.obj F) c).app d s)
          (Category.comp_id (R.map a)))).trans
      (homEquiv_map a d s)

/-! ### The composition fields of Stacks 03LU -/

/-- The counit of a composite of direct images: the counit of the direct image along `g`, at the
direct image of the module along `f`, composed with the counit along `f`. -/
noncomputable def compCounit (f : X ⟶ Y) (g : Y ⟶ Z)
    {P : Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS Y.1 Y.2}
    {Pg : Modules.{u, u} B S hS Y.1 Y.2 ⥤ Modules.{u, u} B S hS Z.1 Z.2}
    (hP : ModulePushforwardPresentation B S hS f P)
    (hPg : ModulePushforwardPresentation B S hS g Pg)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    ModuleFMap B S hS (f ≫ g) F ((P ⋙ Pg).obj F) :=
  ModuleFMap.comp B S hS f g F (P.obj F) ((P ⋙ Pg).obj F)
    (hPg.counit (P.obj F)) (hP.counit F)

/-- The composite counit is the composite of the two counits.  This is the definition, named so
that it can be rewritten with rather than unfolded. -/
theorem compCounit_eq (f : X ⟶ Y) (g : Y ⟶ Z)
    {P : Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS Y.1 Y.2}
    {Pg : Modules.{u, u} B S hS Y.1 Y.2 ⥤ Modules.{u, u} B S hS Z.1 Z.2}
    (hP : ModulePushforwardPresentation B S hS f P)
    (hPg : ModulePushforwardPresentation B S hS g Pg)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    compCounit B S hS f g hP hPg F =
      ModuleFMap.comp B S hS f g F (P.obj F) ((P ⋙ Pg).obj F)
        (hPg.counit (P.obj F)) (hP.counit F) := rfl

/-- The universal correspondence of a composite of direct images: the correspondence of the
direct image along `g`, followed by composition with the counit along `f`. -/
noncomputable def compHomEquiv (f : X ⟶ Y) (g : Y ⟶ Z)
    {P : Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS Y.1 Y.2}
    {Pg : Modules.{u, u} B S hS Y.1 Y.2 ⥤ Modules.{u, u} B S hS Z.1 Z.2}
    (hP : ModulePushforwardPresentation B S hS f P)
    (hPg : ModulePushforwardPresentation B S hS g Pg)
    (F : Modules.{u, u} B S hS X.1 X.2) (N : Modules.{u, u} B S hS Z.1 Z.2) :
    (N ⟶ (P ⋙ Pg).obj F) ≃ ModuleFMap B S hS (f ≫ g) F N :=
  (hPg.homEquiv (P.obj F) N).trans
    (modulePushforwardCounitCompEquiv B S hS f g hP F N)

/-- The composite correspondence is the correspondence along `g` followed by composition with the
counit along `f`. -/
theorem compHomEquiv_apply (f : X ⟶ Y) (g : Y ⟶ Z)
    {P : Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS Y.1 Y.2}
    {Pg : Modules.{u, u} B S hS Y.1 Y.2 ⥤ Modules.{u, u} B S hS Z.1 Z.2}
    (hP : ModulePushforwardPresentation B S hS f P)
    (hPg : ModulePushforwardPresentation B S hS g Pg)
    (F : Modules.{u, u} B S hS X.1 X.2) (N : Modules.{u, u} B S hS Z.1 Z.2)
    (a : N ⟶ (P ⋙ Pg).obj F) :
    compHomEquiv B S hS f g hP hPg F N a =
      modulePushforwardCounitCompEquiv B S hS f g hP F N
        (hPg.homEquiv (P.obj F) N a) :=
  Equiv.trans_apply (hPg.homEquiv (P.obj F) N)
    (modulePushforwardCounitCompEquiv B S hS f g hP F N) a

/-- **The composite correspondence is composition with the composite counit.**  This is the
`homEquiv_apply` component of the composite universal property, and it is
`AlgebraicGeometry.Space.ModuleFMap.comp_app_precomp` — functoriality of the composite in its
target module — applied to the correspondence along `g`. -/
theorem compHomEquiv_app (f : X ⟶ Y) (g : Y ⟶ Z)
    {P : Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS Y.1 Y.2}
    {Pg : Modules.{u, u} B S hS Y.1 Y.2 ⥤ Modules.{u, u} B S hS Z.1 Z.2}
    (hP : ModulePushforwardPresentation B S hS f P)
    (hPg : ModulePushforwardPresentation B S hS g Pg)
    (F : Modules.{u, u} B S hS X.1 X.2) (N : Modules.{u, u} B S hS Z.1 Z.2)
    (a : N ⟶ (P ⋙ Pg).obj F)
    (d : ChartDiagram B S hS X.1 Z.1 (f ≫ g).hom) (s : N.val.obj (op d.V)) :
    (compHomEquiv B S hS f g hP hPg F N a).app d s =
      (compCounit B S hS f g hP hPg F).app d (a.val.app (op d.V) s) := by
  rw [compHomEquiv_apply, compCounit_eq, modulePushforwardCounitCompEquiv_apply]
  exact ModuleFMap.comp_app_precomp B S hS f g F (P.obj F)
    (H := (P ⋙ Pg).obj F) (H' := N) a (hPg.counit (P.obj F))
    (hPg.homEquiv (P.obj F) N a) (hPg.homEquiv_apply (P.obj F) N a)
    (hP.counit F) d s

/-- **The composite of two counits is natural in the module.**  A morphism of modules on `X` is
carried through the composite in three steps: out of the target slot by functoriality in the
target, across the middle slot, and into the source slot. -/
theorem ModuleFMap.comp_counit_naturality (f : X ⟶ Y) (g : Y ⟶ Z)
    {P : Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS Y.1 Y.2}
    {Pg : Modules.{u, u} B S hS Y.1 Y.2 ⥤ Modules.{u, u} B S hS Z.1 Z.2}
    (hP : ModulePushforwardPresentation B S hS f P)
    (hPg : ModulePushforwardPresentation B S hS g Pg)
    {F F' : Modules.{u, u} B S hS X.1 X.2} (a : F ⟶ F')
    (d : ChartDiagram B S hS X.1 Z.1 (f ≫ g).hom)
    (s : ((P ⋙ Pg).obj F).val.obj (op d.V)) :
    (ModuleFMap.comp B S hS f g F' (P.obj F') ((P ⋙ Pg).obj F')
          (hPg.counit (P.obj F')) (hP.counit F')).app d
        (((P ⋙ Pg).map a).val.app (op d.V) s) =
      a.val.app (op d.U)
        ((ModuleFMap.comp B S hS f g F (P.obj F) ((P ⋙ Pg).obj F)
          (hPg.counit (P.obj F)) (hP.counit F)).app d s) :=
  ((ModuleFMap.comp_app_precomp B S hS f g F' (P.obj F')
        (H := (P ⋙ Pg).obj F') (H' := (P ⋙ Pg).obj F) ((P ⋙ Pg).map a)
        (hPg.counit (P.obj F'))
        (hPg.homEquiv (P.obj F') ((P ⋙ Pg).obj F) ((P ⋙ Pg).map a))
        (hPg.homEquiv_apply (P.obj F') ((P ⋙ Pg).obj F) ((P ⋙ Pg).map a))
        (hP.counit F') d s).symm.trans
      (congrArg (fun ζ : ModuleFMap B S hS (f ≫ g) F' ((P ⋙ Pg).obj F) ↦ ζ.app d s)
        (ModuleFMap.comp_middle B S hS f g F' (P.map a) ((P ⋙ Pg).obj F)
          (hPg.counit (P.obj F))
          (hPg.homEquiv (P.obj F') ((P ⋙ Pg).obj F) ((P ⋙ Pg).map a))
          (fun e t ↦ (hPg.homEquiv_apply (P.obj F') ((P ⋙ Pg).obj F)
              ((P ⋙ Pg).map a) e t).trans (hPg.naturality (P.map a) e t))
          (hP.counit F') (hP.homEquiv F' (P.obj F) (P.map a))
          (hP.homEquiv_apply F' (P.obj F) (P.map a))))).trans
    (ModuleFMap.comp_app_postcomp B S hS f g a (P.obj F) ((P ⋙ Pg).obj F)
      (hPg.counit (P.obj F)) (hP.counit F) (hP.homEquiv F' (P.obj F) (P.map a))
      (fun d' s' ↦ (hP.homEquiv_apply F' (P.obj F) (P.map a) d' s').trans
        (hP.naturality a d' s')) d s)

/-- The composite counit is natural in the module.  This is the `naturality` component of the
composite universal property, `AlgebraicGeometry.Space.ModuleFMap.comp_counit_naturality` read
through `AlgebraicGeometry.Space.compCounit_eq`. -/
theorem compCounit_naturality (f : X ⟶ Y) (g : Y ⟶ Z)
    {P : Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS Y.1 Y.2}
    {Pg : Modules.{u, u} B S hS Y.1 Y.2 ⥤ Modules.{u, u} B S hS Z.1 Z.2}
    (hP : ModulePushforwardPresentation B S hS f P)
    (hPg : ModulePushforwardPresentation B S hS g Pg)
    {F F' : Modules.{u, u} B S hS X.1 X.2} (a : F ⟶ F')
    (d : ChartDiagram B S hS X.1 Z.1 (f ≫ g).hom)
    (s : ((P ⋙ Pg).obj F).val.obj (op d.V)) :
    (compCounit B S hS f g hP hPg F').app d
          (((P ⋙ Pg).map a).val.app (op d.V) s) =
      a.val.app (op d.U) ((compCounit B S hS f g hP hPg F).app d s) :=
  (congrArg (fun ζ : ModuleFMap B S hS (f ≫ g) F' ((P ⋙ Pg).obj F') ↦
        ζ.app d (((P ⋙ Pg).map a).val.app (op d.V) s))
      (compCounit_eq B S hS f g hP hPg F')).trans
    ((ModuleFMap.comp_counit_naturality B S hS f g hP hPg a d s).trans
      (congrArg (fun ζ : ModuleFMap B S hS (f ≫ g) F ((P ⋙ Pg).obj F) ↦
          a.val.app (op d.U) (ζ.app d s))
        (compCounit_eq B S hS f g hP hPg F).symm))

/-- **The composite correspondence is natural in the target module.**  Precomposing a morphism
of `𝒪_Z`-modules precomposes the linear map of sections that the composite correspondence
attaches to it.  This is functoriality of
`AlgebraicGeometry.Space.ModuleFMap.comp` in its target module, read through the composite
correspondence. -/
theorem compHomEquiv_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    {P : Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS Y.1 Y.2}
    {Pg : Modules.{u, u} B S hS Y.1 Y.2 ⥤ Modules.{u, u} B S hS Z.1 Z.2}
    (hP : ModulePushforwardPresentation B S hS f P)
    (hPg : ModulePushforwardPresentation B S hS g Pg)
    (F : Modules.{u, u} B S hS X.1 X.2)
    (N N' : Modules.{u, u} B S hS Z.1 Z.2) (b : N' ⟶ N) (a : N ⟶ (P ⋙ Pg).obj F)
    (d : ChartDiagram B S hS X.1 Z.1 (f ≫ g).hom) (s : N'.val.obj (op d.V)) :
    (compHomEquiv B S hS f g hP hPg F N' (b ≫ a)).app d s =
      (compHomEquiv B S hS f g hP hPg F N a).app d (b.val.app (op d.V) s) := by
  rw [compHomEquiv_app, compHomEquiv_app]
  exact congrArg ((compCounit B S hS f g hP hPg F).app d)
    (rfl : (b ≫ a).val.app (op d.V) s =
      a.val.app (op d.V) (b.val.app (op d.V) s))

/-- **The composite correspondence is natural in the source module.**  The linear map of sections
which the composite correspondence attaches to the composite functor's action on a morphism of
`𝒪_X`-modules is that morphism composed with the composite counit.  This is
`AlgebraicGeometry.Space.compCounit_naturality` in the form that
`AlgebraicGeometry.Space.presentationOfEquiv` consumes. -/
theorem compHomEquiv_map (f : X ⟶ Y) (g : Y ⟶ Z)
    {P : Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS Y.1 Y.2}
    {Pg : Modules.{u, u} B S hS Y.1 Y.2 ⥤ Modules.{u, u} B S hS Z.1 Z.2}
    (hP : ModulePushforwardPresentation B S hS f P)
    (hPg : ModulePushforwardPresentation B S hS g Pg)
    {F F' : Modules.{u, u} B S hS X.1 X.2} (a : F ⟶ F')
    (d : ChartDiagram B S hS X.1 Z.1 (f ≫ g).hom)
    (s : ((P ⋙ Pg).obj F).val.obj (op d.V)) :
    (compHomEquiv B S hS f g hP hPg F' ((P ⋙ Pg).obj F)
          ((P ⋙ Pg).map a)).app d s =
      a.val.app (op d.U) ((compHomEquiv B S hS f g hP hPg F ((P ⋙ Pg).obj F)
        (𝟙 ((P ⋙ Pg).obj F))).app d s) := by
  rw [compHomEquiv_app, compHomEquiv_app]
  refine Eq.trans (compCounit_naturality B S hS f g hP hPg a d s) ?_
  exact congrArg (fun z : F.val.obj (op d.U) ↦ a.val.app (op d.U) z)
    (congrArg ((compCounit B S hS f g hP hPg F).app d)
      (rfl : s = (𝟙 ((P ⋙ Pg).obj F) :
        (P ⋙ Pg).obj F ⟶ (P ⋙ Pg).obj F).val.app (op d.V) s))

/-- **The canonical isomorphism of two functors satisfying the universal property is natural in
the module.**  This is what upgrades the objectwise
`AlgebraicGeometry.Space.ModulePushforwardPresentation.objIso` to an isomorphism of functors, and
it follows from the two `naturality` fields alone: both sides, read through the universal
correspondence at the target functor, compute to the counit of the source functor composed with
the morphism of modules. -/
theorem ModulePushforwardPresentation.objIso_naturality {f : X ⟶ Y}
    {P Q : Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS Y.1 Y.2}
    (hP : ModulePushforwardPresentation B S hS f P)
    (hQ : ModulePushforwardPresentation B S hS f Q)
    {F F' : Modules.{u, u} B S hS X.1 X.2} (a : F ⟶ F') :
    P.map a ≫ (ModulePushforwardPresentation.objIso B S hS hP hQ F').hom =
      (ModulePushforwardPresentation.objIso B S hS hP hQ F).hom ≫ Q.map a := by
  refine (hQ.homEquiv F' (P.obj F)).injective ?_
  refine ModuleFMap.ext B S hS (funext fun d ↦ funext fun s ↦ ?_)
  have hL : (hQ.homEquiv F' (P.obj F) (P.map a ≫
      (ModulePushforwardPresentation.objIso B S hS hP hQ F').hom)).app d s =
      a.val.app (op d.U) ((hP.counit F).app d s) := by
    rw [hQ.homEquiv_apply]
    change (hQ.counit F').app d
      (((hQ.homEquiv F' (P.obj F')).symm (hP.counit F')).val.app (op d.V)
        ((P.map a).val.app (op d.V) s)) = _
    rw [ModulePushforwardPresentation.homEquiv_symm_apply B S hS hQ F' (P.obj F')
      (hP.counit F')]
    exact hP.naturality a d s
  have hR : (hQ.homEquiv F' (P.obj F)
      ((ModulePushforwardPresentation.objIso B S hS hP hQ F).hom ≫ Q.map a)).app d s =
      a.val.app (op d.U) ((hP.counit F).app d s) := by
    rw [hQ.homEquiv_apply]
    change (hQ.counit F').app d ((Q.map a).val.app (op d.V)
      (((hQ.homEquiv F (P.obj F)).symm (hP.counit F)).val.app (op d.V) s)) = _
    rw [hQ.naturality a d]
    exact congrArg (fun z ↦ a.val.app (op d.U) z)
      (ModulePushforwardPresentation.homEquiv_symm_apply B S hS hQ F (P.obj F)
        (hP.counit F) d s)
  exact hL.trans hR.symm

/-- **The universal property determines the direct image as a functor, not only objectwise.**
Two functors satisfying the chartwise universal property of the direct image along `f` are
canonically isomorphic as functors, by the isomorphism matching the two counits. -/
noncomputable def ModulePushforwardPresentation.natIso {f : X ⟶ Y}
    {P Q : Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS Y.1 Y.2}
    (hP : ModulePushforwardPresentation B S hS f P)
    (hQ : ModulePushforwardPresentation B S hS f Q) : P ≅ Q :=
  NatIso.ofComponents (fun F ↦ ModulePushforwardPresentation.objIso B S hS hP hQ F)
    (fun a ↦ ModulePushforwardPresentation.objIso_naturality B S hS hP hQ a)

/-- **Stacks 03LU: the composition comparison, normalized by the chartwise universal property.**
Given any functor satisfying the chartwise universal property of the direct image along `f ≫ g`,
and any functor satisfying it on a composite `P ⋙ Pg`, the two are isomorphic *as functors*, by
the isomorphism that the universal correspondence carries to the first counit.

This is the `composition` field of `AlgebraicGeometry.Space.ModuleImageData` with the field's own
`compositionPresentation` taken as the hypothesis `hPc`: the isomorphism is
`AlgebraicGeometry.Space.ModulePushforwardPresentation.natIso` and the normalization is then the
statement that the universal correspondence undoes its own inverse, so no choice is made and the
comparison is the unique one with that property.

Nothing in the statement or the proof uses that the first functor is a composite or that the
morphism is `f ≫ g`: both go through verbatim for an arbitrary morphism and an arbitrary functor,
giving the general fact that two functors satisfying the universal property are isomorphic
compatibly with their counits.  It is stated in this specialized shape because that is the shape
the `composition` field of `AlgebraicGeometry.Space.ModuleImageData` asks for. -/
noncomputable def ModulePushforwardPresentation.compositionComparison {f : X ⟶ Y} {g : Y ⟶ Z}
    {P : Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS Y.1 Y.2}
    {Pg : Modules.{u, u} B S hS Y.1 Y.2 ⥤ Modules.{u, u} B S hS Z.1 Z.2}
    {Pfg : Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS Z.1 Z.2}
    (hPc : ModulePushforwardPresentation B S hS (f ≫ g) (P ⋙ Pg))
    (hPfg : ModulePushforwardPresentation B S hS (f ≫ g) Pfg) :
    { e : P ⋙ Pg ≅ Pfg //
      ∀ F : Modules.{u, u} B S hS X.1 X.2,
        (hPfg.homEquiv F ((P ⋙ Pg).obj F)) (e.hom.app F) = hPc.counit F } :=
  ⟨ModulePushforwardPresentation.natIso B S hS hPc hPfg,
    fun F ↦ (hPfg.homEquiv F ((P ⋙ Pg).obj F)).apply_symm_apply _⟩

end AlgebraicGeometry.Space

end
