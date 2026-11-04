module

public import StacksFrontier.AlgebraicGeometry.ReflexiveDualHullInput.ModuleStalk
public import StacksFrontier.AlgebraicGeometry.ReflexiveHullCriterion.Basic
public import StacksFrontier.AlgebraicGeometry.ReflexiveHullCriterion.ModuleInput
public import StacksFrontier.AlgebraicGeometry.StalkFiniteType.Basic
public import StacksFrontier.AlgebraicGeometry.StalkFiniteType.FlatFinitePresentation
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.NormalizationQuotient.Skyscraper
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.FlatModuleSheavesAndStalks
public import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Reflexivity of a module on a scheme is reflexivity of its stalks

`StacksFrontier/AlgebraicGeometry/ReflexiveHullCriterion/Basic.lean` reduces the adjunction of
[Stacks, Tag 0EBH](https://stacks.math.columbia.edu/tag/0EBH) to a single statement about the
dual of a coherent module on an integral locally Noetherian scheme: that `F^∨` is coherent and
reflexive.  `ReflexiveHullCriterion/ModuleInput.lean` records that the *module*-level half of the
reflexivity assertion is already proved -- over a Noetherian domain the dual of a finite module
is reflexive -- and that what the sheaf-level statement still needs is the passage from the
module statement to the sheaf statement.

This file performs that passage, and it performs it at stalks rather than at affine sections.
The reflexivity predicate `IsReflexive F` is invertibility of the canonical map
`F ⟶ F^∨∨`, invertibility of a morphism of sheaves of modules is detected on stalks, and
`ReflexiveDualHullInput/ModuleStalk.lean` already identifies the stalk of `F^∨` with the
`𝒪_{X, x}`-linear dual of the stalk of `F` for `F` of finite presentation, with a germ formula.
So the only thing owed is that the stalk map of `F ⟶ F^∨∨` is, under those two identifications,
the module-level evaluation map `M ⟶ M^{∨∨}` -- which is `stalkDualEquiv_toDoubleDual` below,
proved from the defining local formula for the canonical map and nothing else.

That yields `isReflexive_of_forall_isReflexive_stalk`, which has no hypothesis on the scheme:
a module of finite presentation whose dual is of finite presentation is reflexive exactly when
every stalk is a reflexive module over the local ring there.  Specialised to a dual module on an
integral locally Noetherian scheme it gives `isReflexive_dualSheaf`, and that closes the
reflexivity half of Tag 0EBH's hull input.

## What remains owed, precisely

The coherence half is **not** closed here, and it is also what the reflexivity half still
assumes.  Both `isReflexive_dualSheaf` and `isCoherent_and_isReflexive_dualSheaf` need to know
that the dual of a coherent module is coherent -- `isReflexive_dualSheaf` because the stalk
identification of `F^∨` is available only for a module of finite presentation, and it is applied
to `F^∨` and to `F^∨∨`.  That statement is
[Stacks, Tag 01Y2](https://stacks.math.columbia.edu/tag/01Y2), internal Hom of coherent modules
is coherent, at target the structure sheaf; it reduces to
[Stacks, Tag 01CQ](https://stacks.math.columbia.edu/tag/01CQ), coherence of the internal Hom out
of a module of finite presentation, and nothing in this library or in Mathlib proves it: a search
for a declaration concluding `IsCoherent` or `IsFiniteType` of an internal Hom, a `sheafHom` or a
`dualSheaf`, under any spelling, returns only the hypotheses of the `ReflexiveHullCriterion`
family.

So `reflexiveHullAdjunction_of_isCoherent_dualSheaf` states Tag 0EBH's adjunction under exactly
one hypothesis, coherence of duals, and that hypothesis is Tag 01Y2.  No attribute for Tag
0EBH is attached anywhere in this file: the Stacks statement assumes only integrality and
local Noetherianity of the scheme, so a statement carrying `hcd` does not prove it.

## Main results

* `stalkDualEquiv_toDoubleDual`: under the stalk identifications of `F^∨` and `F^∨∨` with the
  module duals of the stalk of `F`, the stalk map of the canonical bidual map is evaluation.
* `isReflexive_of_forall_isReflexive_stalk`: reflexivity of a module of finite presentation with
  dual of finite presentation is reflexivity of all of its stalks as modules.  No hypothesis on
  the scheme.
* `isReflexive_dualSheaf`: on an integral locally Noetherian scheme the dual of a module of
  finite presentation is reflexive, given finite presentation of the dual and the double dual.
* `isCoherent_and_isReflexive_dualSheaf`: the hull input of Tag 0EBH, from coherence of duals.
* `reflexiveHullAdjunction_of_isCoherent_dualSheaf`: Tag 0EBH's adjunction, from coherence of
  duals.

## Implementation notes

Two spellings of a stalk meet here and both are needed.  `Stacks.SheafOfModules.SheafHomStalk`
spells the module stalk `modStalk F x` and the ring stalk `ringStalk X.sheaf x`, and the stalk
identification of the dual sheaf is stated there; `Stacks.OXModule` spells them
`OXModule.stalk F x` and `X.presheaf.stalk x`, and the stalk map of a morphism together with its
germ formula is stated there.  The carriers and the module structures agree on the nose, so
`OXModule.stalkLinearMap` is used directly at the `modStalk` spelling and
`OXModule.stalkMapAdd_germ` applies to `germAt` with no translation.  The one place where the
difference is visible is instance search: `IsDomain` and `IsNoetherianRing` of the local ring are
Mathlib instances at the `X.presheaf.stalk x` spelling and have to be transported by
`inferInstanceAs` to the `ringStalk X.sheaf x` spelling, exactly as
`ReflexiveDualHullInput/ModuleStalk.lean` warns.

`stalkDualEquiv_toDoubleDual` reduces to its germ form by bringing the two stalk elements to a
common open neighbourhood; the restriction step is written as two explicit `have`s rather than a
backwards rewrite of `germAt_resLE`, because the membership proof in that lemma's right-hand
side is a function application and higher-order matching against it is unreliable.

## References

* [Stacks Project, Tag 0EBH](https://stacks.math.columbia.edu/tag/0EBH)
* [Stacks Project, Tag 0AY4](https://stacks.math.columbia.edu/tag/0AY4)
* [Stacks Project, Tag 01CP](https://stacks.math.columbia.edu/tag/01CP)
* [Stacks Project, Tag 01Y2](https://stacks.math.columbia.edu/tag/01Y2)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.AlgebraicGeometry.ReflexiveDualHull
open Stacks.SheafOfModules.SheafHomStalk

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveStalkCriterion

variable {X : Scheme.{u}}

/-- **The stalk map of the canonical bidual map is evaluation, on germs.**  For a local section
`m` of `F` and a local section `t` of `F^∨` over the same open, the germ of `j m` paired against
the germ of `t` -- through the identification of the stalk of `F^∨∨` with the dual of the stalk
of `F^∨` -- is the germ of `t` evaluated at the germ of `m` through the identification of the
stalk of `F^∨` with the dual of the stalk of `F`.

Both sides are the germ of the function `t m`: on the left by the defining local formula for the
canonical map (`toDoubleDual_val_app_apply`) followed by the germ formula of the stalk
identification, on the right by that germ formula alone. -/
theorem stalkDualEquiv_toDoubleDual_germ (F : X.Modules) [F.IsFinitePresentation]
    [(dualSheaf F).IsFinitePresentation] (x : X) (U : X.Opens) (hx : x ∈ U)
    (m : Γ(F, U)) (t : Γ(dualSheaf F, U)) :
    dualSheafStalkDualEquiv X (dualSheaf F) x
        (OXModule.stalkLinearMap F (dualSheaf (dualSheaf F)) (toDoubleDual F) x
          (germAt F U x hx m)) (germAt (dualSheaf F) U x hx t)
      = dualSheafStalkDualEquiv X F x (germAt (dualSheaf F) U x hx t) (germAt F U x hx m) := by
  have hg : OXModule.stalkLinearMap F (dualSheaf (dualSheaf F)) (toDoubleDual F) x
        (germAt F U x hx m)
      = germAt (dualSheaf (dualSheaf F)) U x hx
          (Scheme.Modules.Hom.app (toDoubleDual F) U m) :=
    OXModule.stalkMapAdd_germ F (dualSheaf (dualSheaf F)) (toDoubleDual F) x U hx m
  have key : dualPairing (dualSheaf F) (Scheme.Modules.Hom.app (toDoubleDual F) U m)
      (Over.mk (𝟙 U)) t = dualPairing F t (Over.mk (𝟙 U)) m :=
    toDoubleDual_val_app_apply F U m t
  refine Eq.trans (congrArg (fun y => dualSheafStalkDualEquiv X (dualSheaf F) x y
    (germAt (dualSheaf F) U x hx t)) hg) ?_
  refine Eq.trans (dualSheafStalkDualEquiv_germ X (dualSheaf F) x U hx _ t) ?_
  refine Eq.trans (congrArg (fun y => X.presheaf.germ U x hx y) key) ?_
  exact (dualSheafStalkDualEquiv_germ X F x U hx t m).symm

/-- **The stalk map of the canonical bidual map is evaluation.**  The germ form above, for
arbitrary elements of the two stalks: both are germs of local sections, and restricting to the
intersection of their domains puts them over a common open. -/
theorem stalkDualEquiv_toDoubleDual (F : X.Modules) [F.IsFinitePresentation]
    [(dualSheaf F).IsFinitePresentation] (x : X)
    (m : ToType (modStalk F x)) (t : ToType (modStalk (dualSheaf F) x)) :
    dualSheafStalkDualEquiv X (dualSheaf F) x
        (OXModule.stalkLinearMap F (dualSheaf (dualSheaf F)) (toDoubleDual F) x m) t
      = dualSheafStalkDualEquiv X F x t m := by
  obtain ⟨U, hxU, m₀, rfl⟩ := exists_germ_eq F m
  obtain ⟨V, hxV, t₀, rfl⟩ := exists_germ_eq (dualSheaf F) t
  have hxW : x ∈ U ⊓ V := mem_inf hxU hxV
  rw [← germAt_resLE F (inf_le_left : (U ⊓ V : X.Opens) ≤ U) hxW m₀,
    ← germAt_resLE (dualSheaf F) (inf_le_right : (U ⊓ V : X.Opens) ≤ V) hxW t₀]
  exact stalkDualEquiv_toDoubleDual_germ F x (U ⊓ V) hxW _ _


/-- **The stalk map of the canonical bidual map is bijective at a point whose stalk is a
reflexive module.**

Injectivity: the stalk identification of `F^∨` is surjective, so two germs with the same image
are evaluated equally by *every* functional on the stalk, and injectivity of the module-level
evaluation map finishes.  Surjectivity: a section of the stalk of `F^∨∨`, transported along the
two identifications, is a functional on the dual of the stalk, hence the evaluation at some germ
by surjectivity of the module-level evaluation map; the identification of the stalk of `F^∨∨` is
injective, so that germ maps to the section itself. -/
theorem bijective_stalkLinearMap_toDoubleDual (F : X.Modules) [F.IsFinitePresentation]
    [(dualSheaf F).IsFinitePresentation] (x : X)
    (h : Module.IsReflexive (ToType (ringStalk X.sheaf x)) (ToType (modStalk F x))) :
    Function.Bijective
      (OXModule.stalkLinearMap F (dualSheaf (dualSheaf F)) (toDoubleDual F) x) := by
  have hev := @Module.bijective_dual_eval (ToType (ringStalk X.sheaf x))
    (ToType (modStalk F x)) _ _ _ h
  constructor
  · intro a b hab
    refine hev.injective (LinearMap.ext fun phi => ?_)
    obtain ⟨t, rfl⟩ := (dualSheafStalkDualEquiv X F x).surjective phi
    have := congrArg (fun f => dualSheafStalkDualEquiv X (dualSheaf F) x f t) hab
    rwa [stalkDualEquiv_toDoubleDual F x a t, stalkDualEquiv_toDoubleDual F x b t] at this
  · intro s
    obtain ⟨m, hm⟩ := hev.surjective ((dualSheafStalkDualEquiv X (dualSheaf F) x s).comp
      (dualSheafStalkDualEquiv X F x).symm.toLinearMap)
    refine ⟨m, (dualSheafStalkDualEquiv X (dualSheaf F) x).injective (LinearMap.ext fun t => ?_)⟩
    rw [stalkDualEquiv_toDoubleDual F x m t]
    simpa using LinearMap.congr_fun hm (dualSheafStalkDualEquiv X F x t)

/-- **Reflexivity of a module on a scheme is reflexivity of its stalks.**  A module of finite
presentation whose dual is of finite presentation is reflexive as soon as each of its stalks is a
reflexive module over the local ring at that point.

This is the sheafification of the module-level notion: no hypothesis on `X` is used, and the two
finite-presentation hypotheses are exactly what makes the stalk of a dual the dual of a stalk
(Stacks Tag 01CP).  Invertibility is recovered from the stalks by
`NormalizationQuotient.module_isIso_of_stalk_map_isIso`. -/
theorem isReflexive_of_forall_isReflexive_stalk (F : X.Modules) [F.IsFinitePresentation]
    [(dualSheaf F).IsFinitePresentation]
    (h : ∀ x : X, Module.IsReflexive (ToType (ringStalk X.sheaf x)) (ToType (modStalk F x))) :
    IsReflexive F := by
  show IsIso (toDoubleDual F)
  refine NormalizationQuotient.module_isIso_of_stalk_map_isIso (toDoubleDual F) fun x => ?_
  exact (ConcreteCategory.isIso_iff_bijective _).2
    (bijective_stalkLinearMap_toDoubleDual F x (h x))


/-! ### The reflexivity half of the hull input -/

/-- **Reflexivity of the dual of a module of finite presentation on an integral locally
Noetherian scheme**, given finite presentation of the dual and of the double dual.

This is the sheaf-level form of `Stacks.ReflexiveDual.isReflexive_dual_of_finite`: the local ring
at a point is a Noetherian domain (integrality and local Noetherianity of `X`), the stalk of `F`
there is a finite module (finite type of `F`), so the module dual of that stalk is reflexive; and
the stalk of `F^∨` *is* that module dual, by `dualSheafStalkDualEquiv`. -/
theorem isReflexive_dualSheaf [IsIntegral X] [IsLocallyNoetherian X] (F : X.Modules)
    [F.IsFinitePresentation] [(dualSheaf F).IsFinitePresentation]
    [(dualSheaf (dualSheaf F)).IsFinitePresentation] :
    IsReflexive (dualSheaf F) := by
  have hft : F.IsFiniteType := StalkFiniteType.isFiniteType_of_isFinitePresentation F
  refine isReflexive_of_forall_isReflexive_stalk (dualSheaf F) fun x => ?_
  have hfin : Module.Finite (ToType (ringStalk X.sheaf x)) (ToType (modStalk F x)) :=
    StalkFiniteType.finite_stalk F x
  have hdom : IsDomain (ToType (ringStalk X.sheaf x)) :=
    inferInstanceAs (IsDomain (ToType (X.presheaf.stalk x)))
  have hnoe : IsNoetherianRing (ToType (ringStalk X.sheaf x)) :=
    inferInstanceAs (IsNoetherianRing (ToType (X.presheaf.stalk x)))
  have hdual : Module.IsReflexive (ToType (ringStalk X.sheaf x))
      (Module.Dual (ToType (ringStalk X.sheaf x)) (ToType (modStalk F x))) :=
    Stacks.ReflexiveDual.isReflexive_dual_of_finite
  exact Module.equiv (dualSheafStalkDualEquiv X F x).symm

/-- **The hull input of Stacks Tag 0EBH, from coherence of duals alone.**  On an integral
locally Noetherian scheme, if the dual of every coherent module is coherent then the dual of a
coherent module is coherent *and reflexive* -- which is the single hypothesis of
`ReflexiveHullCriterion.reflexiveHullAdjunction_of_dualSheaf`.

The hypothesis is applied twice, to `F` and to `F^∨`, because the reflexivity half needs finite
presentation of `F^∨` and of `F^∨∨`; a coherent module on any scheme is of finite presentation
(`CoherentTFAE.isFinitePresentation_of_isCoherent'`). -/
theorem isCoherent_and_isReflexive_dualSheaf [IsIntegral X] [IsLocallyNoetherian X]
    (hcd : ∀ G : X.Modules, G.IsCoherent → (dualSheaf G).IsCoherent)
    (F : X.Modules) (hF : F.IsCoherent) :
    (dualSheaf F).IsCoherent ∧ IsReflexive (dualSheaf F) := by
  have h1 : (dualSheaf F).IsCoherent := hcd F hF
  have h2 : (dualSheaf (dualSheaf F)).IsCoherent := hcd (dualSheaf F) h1
  have fp := CoherentTFAE.isFinitePresentation_of_isCoherent' (X := X)
  have := fp F
  have := fp (dualSheaf F)
  have := fp (dualSheaf (dualSheaf F))
  exact ⟨h1, isReflexive_dualSheaf F⟩

/-- **Stacks Tag 0EBH, the adjunction, from coherence of duals alone.**  On an integral locally
Noetherian scheme, if the dual of every coherent module is coherent, then the double-dual functor
is left adjoint to the inclusion of coherent reflexive modules into coherent modules, with the
canonical bidual map as its unit.

This is the maximal reduction of Tag 0EBH available in this library: the one remaining hypothesis
is Stacks Tag 01Y2 at target the structure sheaf, and nothing proves it here.  The tag is
therefore withheld -- the Stacks statement assumes only integrality and local Noetherianity,
and a declaration carrying `hcd` does not prove it. -/
noncomputable def reflexiveHullAdjunction_of_isCoherent_dualSheaf (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X]
    (hcd : ∀ G : X.Modules, G.IsCoherent → (dualSheaf G).IsCoherent) :
    { p : (Σ L : ReflexiveHull.CoherentModules X ⥤ ReflexiveHull.CoherentReflexiveModules X,
        L ⊣ ReflexiveHull.inclusion X) //
      ∀ F : ReflexiveHull.CoherentModules X,
        ∃ h : (p.1.obj F).obj.obj = ReflexiveModules.reflexiveHull F.obj,
          (p.2.unit.app F).hom ≫ eqToHom h =
            (ReflexiveModules.toReflexiveHull F.obj).1 } :=
  ReflexiveHullCriterion.reflexiveHullAdjunction_of_dualSheaf X
    (fun F hF => isCoherent_and_isReflexive_dualSheaf hcd F hF)

end Stacks.AlgebraicGeometry.ReflexiveStalkCriterion

end
