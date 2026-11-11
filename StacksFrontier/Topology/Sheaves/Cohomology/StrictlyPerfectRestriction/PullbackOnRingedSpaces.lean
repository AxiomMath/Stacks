module

public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.FiniteFreeSummands
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfectRestriction.PullbackOverASite
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace

/-!
# Pullback of a strictly perfect complex along a morphism of ringed spaces

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and let `f^*` be the pullback of
sheaves of modules, `RingedSpaceModuleAdjunction.modulePullback f`. This file proves that `f^*`
carries direct summands of finite free `𝒪_Y`-modules to direct summands of finite free
`𝒪_X`-modules, and hence that the termwise pullback of a strictly perfect complex of
`𝒪_Y`-modules is a strictly perfect complex of `𝒪_X`-modules (Stacks 09U6).

## Main results

* `Stacks.StrictlyPerfect.Pullback.modulePullbackStructureModuleIso`: `f^* 𝒪_Y ≅ 𝒪_X`, i.e. the
  pullback of
  the structure sheaf viewed as a module over itself is again the structure sheaf.
* `Stacks.StrictlyPerfect.Pullback.modulePullbackFiniteFreeIso`: `f^* (𝒪_Y^{⊕ n}) ≅ 𝒪_X^{⊕ n}`.
* `Stacks.StrictlyPerfect.Pullback.isDirectSummandOfFiniteFree_modulePullback`: `f^*` preserves the
  property
  of being a direct summand of a finite free module.
* `Stacks.StrictlyPerfect.Pullback.isStrictlyPerfect_modulePullback`: **Stacks 09U6**, the pullback
  of a
  strictly perfect complex is strictly perfect.

## Implementation notes

This file carries the `@[stacks 09U6]` attribute. An older, self-contained universe-0
statement, `Stacks.Cohomology.StrictlyPerfectPullback.pullback_isStrictlyPerfect` in
`StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfectRestriction.PullbackOverASite`, is stated
at `AlgebraicGeometry.RingedSpace.{0, 0}` and in terms of another vocabulary (the `Modules`
and `pullback` of `StacksFrontier.Topology.Sheaves.RingedSpace.ModuleFunctors`, and
`Stacks.Cohomology.StrictlyPerfectPullback.IsStrictlyPerfect`), none of which is
the vocabulary of the strictly-perfect development. The consumers here need the statement at
`RingedSpace.{u, u}` for `StrictlyPerfect.OXMod` / `StrictlyPerfect.IsStrictlyPerfect` of
`StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.FiniteFreeSummands` and for
`RingedSpaceModuleAdjunction.modulePullback`, so the lemma is proved here against those
definitions. The mathematical argument of the universe-0 statement carries
over unchanged; what does not carry over is the bookkeeping, for two reasons.

First, `StrictlyPerfect.finiteFree Y n` is `⨁ (fun _ : Fin n => StrictlyPerfect.structureModule Y)`
rather than `SheafOfModules.free (Fin n)`, so Mathlib's `SheafOfModules.pullbackObjFreeIso` does
not apply directly. Instead `modulePullbackFiniteFreeIso` is assembled from
`Functor.mapBiproduct` -- available because `modulePullback f` is a left adjoint, hence additive,
hence preserves finite biproducts -- together with `modulePullbackStructureModuleIso`, which is
Mathlib's `SheafOfModules.pullbackObjUnitToUnit` (an isomorphism precisely because
`TopologicalSpace.Opens.map f.hom.base` is a final functor, which is why
`StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfectRestriction.PullbackOverASite` is
imported: it is the file in scope here declaring that finality as an instance).

Second, `StrictlyPerfect.OXMod.{u} X` and `SheafOfModules.{u} (structureSheafRing X)` are equal by
`rfl` but not by `instances`-transparency unification, and the finite-biproduct instances of
`Tag08C5` are stated only for the first spelling. Instance search therefore fails on any goal
phrased in the second, even though every goal here type-checks in either. The two constructions
below are consequently arranged so that each instance-bearing position is written in a single
spelling: `mapFiniteFreeIso` is stated for an arbitrary functor between `OXMod` categories and
takes additivity as an *explicit* argument (as an instance argument it would again be searched for
at the wrong spelling), and `modulePullbackStructureModuleIso` builds the isomorphism with
Mathlib's names under a type ascription, letting the ascription against the declared type do the
one defeq check that is needed.

## References

* [Stacks Project, Tag 09U6](https://stacks.math.columbia.edu/tag/09U6)
* [Stacks Project, Tag 08C4](https://stacks.math.columbia.edu/tag/08C4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open RingedSpaceModuleAdjunction StrictlyPerfect

namespace Stacks.StrictlyPerfect.Pullback

universe u

/-- **An additive functor carrying the structure sheaf to the structure sheaf carries finite free
modules to finite free modules.** If `F : Mod(𝒪_Y) ⥤ Mod(𝒪_X)` is additive and `e` identifies
`F 𝒪_Y` with `𝒪_X`, then `F (𝒪_Y^{⊕ n}) ≅ 𝒪_X^{⊕ n}`, because an additive functor preserves
finite biproducts and `StrictlyPerfect.finiteFree` is a biproduct of copies of
`StrictlyPerfect.structureModule`.

Additivity is an explicit argument rather than an instance argument: the intended `F` is
`RingedSpaceModuleAdjunction.modulePullback f`, whose additivity instance is stated for
`SheafOfModules (structureSheafRing _)`, a spelling of `StrictlyPerfect.OXMod` that instance search
does not see through. -/
def mapFiniteFreeIso {X Y : RingedSpace.{u, u}} (F : OXMod.{u} Y ⥤ OXMod.{u} X)
    (hF : F.Additive) (e : F.obj (structureModule Y) ≅ structureModule X) (n : ℕ) :
    F.obj (finiteFree Y n) ≅ finiteFree X n :=
  letI := hF
  (Functor.mapBiproduct F (fun _ : Fin n => structureModule Y)).trans
    (biproduct.mapIso (fun _ => e))

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **The pullback of the structure sheaf is the structure sheaf**, `f^* 𝒪_Y ≅ 𝒪_X`.

This is Mathlib's `SheafOfModules.pullbackObjUnitToUnit`, the morphism adjoint to
`f^♯ : 𝒪_Y ⟶ f_* 𝒪_X`; it is an isomorphism because the inverse-image functor on opens
`TopologicalSpace.Opens.map f.hom.base` is final. -/
def modulePullbackStructureModuleIso :
    (modulePullback f).obj (structureModule Y) ≅ structureModule X :=
  letI : (SheafOfModules.pushforward (structureSheafHom f)).IsRightAdjoint :=
    modulePushforward_isRightAdjoint f
  (asIso (SheafOfModules.pullbackObjUnitToUnit (structureSheafHom f)) :
    (SheafOfModules.pullback (structureSheafHom f)).obj
        (SheafOfModules.unit (structureSheafRing Y)) ≅
      SheafOfModules.unit (structureSheafRing X))

/-- **The pullback of a finite free module is finite free**, `f^* (𝒪_Y^{⊕ n}) ≅ 𝒪_X^{⊕ n}`. -/
def modulePullbackFiniteFreeIso (n : ℕ) :
    (modulePullback f).obj (finiteFree Y n) ≅ finiteFree X n :=
  mapFiniteFreeIso (X := X) (Y := Y) (modulePullback f) (modulePullback_additive f)
    (modulePullbackStructureModuleIso f) n

/-- **Pullback preserves direct summands of finite free modules.** If `M` is a retract of
`𝒪_Y^{⊕ n}` then `f^* M` is a retract of `f^* (𝒪_Y^{⊕ n}) ≅ 𝒪_X^{⊕ n}`, since a functor carries
a retract to a retract. -/
theorem isDirectSummandOfFiniteFree_modulePullback (M : OXMod.{u} Y)
    (hM : IsDirectSummandOfFiniteFree M) :
    IsDirectSummandOfFiniteFree ((modulePullback f).obj M) := by
  obtain ⟨n, ⟨ρ⟩⟩ := (isDirectSummandOfFiniteFree_iff_retract M).mp hM
  refine (isDirectSummandOfFiniteFree_iff_retract _).mpr ⟨n, ⟨?_⟩⟩
  exact (ρ.map (modulePullback f)).trans (modulePullbackFiniteFreeIso f n).retract

/-- **Stacks 09U6 (Lemma 20.46.4).** The termwise pullback of a strictly perfect complex of
`𝒪_Y`-modules along a morphism of ringed spaces `f : X ⟶ Y` is a strictly perfect complex of
`𝒪_X`-modules.

Boundedness is preserved because `f^*` preserves zero morphisms and so carries a zero object to a
zero object, hence cannot create a nonzero term; the termwise condition is
`Stacks.StrictlyPerfect.Pullback.isDirectSummandOfFiniteFree_modulePullback`.

This is the full lemma: `f` is an arbitrary morphism of ringed spaces, `f^*` is the pullback of
sheaves of modules (`f^{-1}G ⊗_{f^{-1}O_Y} O_X`), and strictly perfect is Definition 20.46.1
(tag 08C4): finitely many nonzero terms, each a direct summand of a finite free module. -/
@[stacks 09U6 "for every morphism of ringed spaces f : X ⟶ Y (rings and sections in one universe), \
  the termwise pullback f^* of a strictly perfect complex of O_Y-modules is strictly perfect"]
theorem isStrictlyPerfect_modulePullback (K : CochainComplex (OXMod.{u} Y) ℤ)
    (hK : IsStrictlyPerfect K) :
    IsStrictlyPerfect
      (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) where
  bounded := Set.Finite.subset hK.bounded fun _ hi h => hi ((modulePullback f).map_isZero h)
  directSummand i := isDirectSummandOfFiniteFree_modulePullback f _ (hK.directSummand i)

end Stacks.StrictlyPerfect.Pullback

end
