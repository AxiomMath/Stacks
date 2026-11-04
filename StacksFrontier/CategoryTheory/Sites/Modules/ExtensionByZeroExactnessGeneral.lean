module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SliceExtensionExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZero
public import Mathlib.CategoryTheory.Limits.ExactFunctor
import StacksCore.Tactic.StacksAttribute

/-!
# Exactness of extension by zero, with the universes free

Let `R` be a sheaf of rings on a site `(C, J)` and let `U` be an object of `C`. Restriction
along `Over.forget U` sends a sheaf of `R`-modules to a sheaf of `R_U`-modules on the localized
site `C/U`, and its left adjoint `j_{U!} = SheafOfModules.extensionByZero R U` is extension by
zero. This file proves that `j_{U!}` is exact with the universe of the site, the universe of
its morphisms, the universe of the sections of `R` and the extra module universe all
independent.

## Main results

* `SheafOfModules.extensionByZero_preservesMonomorphisms`: `j_{U!}` preserves monomorphisms.
* `SheafOfModules.extensionByZero_exact`: **Stacks 03DJ.** `j_{U!}` is exact.

## Implementation notes

The mathematics is the source's and is unchanged: right exactness is formal, since `j_{U!}` is
a left adjoint, and left exactness comes from the direct-sum formula of Stacks 03DI, which
makes `j_{U!}` on sections over `V` a coproduct of the components of the map over the maps
`V ⟶ U`, hence a monomorphism whenever the map is one, by Grothendieck's axiom AB4 for
`ModuleCat`. Preserving monomorphisms and cokernels makes a functor preserve homology, hence
finite limits.

What is new here is only that no universe is collapsed.
`Stacks.Sites.ExtensionByZero.extensionByZero_exact` proves the same statement for a site
`C : Type u` with `Category.{u} C` and a sheaf of rings in `RingCat.{u}`, which is too narrow
for the semi-representable lower shrieks: those live over a ringed site whose structure sheaf
has sections in a universe strictly larger than the site's. Specialising them to fit would
prove a different, weaker statement, so the lemma is generalised instead.

The direct-sum half of the argument is not redone: it is already available with the universes
free, at the level of presheaves of modules, as
`Stacks.Sites.OverModules.extension_exact` (part of Stacks 03EJ), which is stated for an
arbitrary left adjoint of restriction. Uniqueness of left adjoints identifies Mathlib's
`PresheafOfModules.pullback` with that one; `SheafOfModules.pullbackIso` then expresses
`j_{U!}` as "forget, extend as presheaves, sheafify", and each of the three steps preserves
monomorphisms.

The sheafification hypotheses for the localized topology `J.over U` are instance-implicit
arguments rather than derived: with the site and the modules in one universe they are the small-
site instances and are found by synthesis, which is why
`Stacks.Sites.ExtensionByZero.extensionByZero_exact` does not carry them, but at independent
universes nothing produces them. They are conditions for the two categories to be abelian at
all, not hypotheses on the site, and they specialise to the instances the narrow statement
uses.

The universe-free presheaf-level restriction adjoint is
`SheafOfModules.presheafOverRestriction`, which is why the instance is seated by hand: its
subject is `(𝟙 (R.over U)).hom`, which is the spelling Mathlib's sheaf-level API asks for only
after unfolding `Functor.sheafPushforwardContinuous`, a plain `def` that instance search cannot
unfold.

## References

* [Stacks Project, Tag 03DJ](https://stacks.math.columbia.edu/tag/03DJ)
* [Stacks Project, Tag 03DI](https://stacks.math.columbia.edu/tag/03DI)
* [Stacks Project, Tag 03EJ](https://stacks.math.columbia.edu/tag/03EJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe m w v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max u v m}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v m}]
  (R : Sheaf J RingCat.{w}) (U : C)
  [HasSheafify (J.over U) AddCommGrpCat.{max u v m}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v m}]

omit [HasSheafify (J.over U) AddCommGrpCat]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat] in
/-- **Extension by zero preserves monomorphisms**, with the site, ring and module universes
independent. By `SheafOfModules.pullbackIso` it is "forget, extend as presheaves, sheafify",
and each of the three steps preserves monomorphisms: the presheaf-level extension because
uniqueness of left adjoints identifies Mathlib's `PresheafOfModules.pullback` with the
extension functor of Stacks 03EJ, which is exact there with the universes already free. -/
@[sga "4 IV 11.3.1" "partial", sga "4 XVII 5.1.1" "partial"]
lemma extensionByZero_preservesMonomorphisms :
    (extensionByZero.{m, w, v, u} R U).PreservesMonomorphisms := by
  have := presheafOverRestriction.{m, w, v, u} R U
  have hex := Stacks.Sites.OverModules.extension_exact.{v, u, w, m} R.obj U
    (Stacks.Sites.OverModules.presheafModuleAdjunctionsOver.{v, u, w, m} R.obj U)
  have hfl : PreservesFiniteLimits
      (Stacks.Sites.OverModules.presheafModuleAdjunctionsOver.{v, u, w, m}
        R.obj U).extension :=
    ((exactFunctor_iff _).mp hex).1
  have hmono : (Stacks.Sites.OverModules.presheafModuleAdjunctionsOver.{v, u, w, m}
      R.obj U).extension.PreservesMonomorphisms := by
    have : PreservesLimitsOfShape WalkingCospan
        (Stacks.Sites.OverModules.presheafModuleAdjunctionsOver.{v, u, w, m}
          R.obj U).extension := hfl.preservesFiniteLimits WalkingCospan
    infer_instance
  have hadj :
      PresheafOfModules.pullback.{max u v m} (F := Over.forget U) (R := R.obj)
          (S := (R.over U).obj) (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom ⊣
        PresheafOfModules.pushforward₀.{max u v m} (Over.forget U) R.obj :=
    PresheafOfModules.pullbackPushforwardAdjunction.{max u v m} (F := Over.forget U)
      (R := R.obj) (S := (R.over U).obj)
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom
  have hpre : (PresheafOfModules.pullback.{max u v m} (F := Over.forget U) (R := R.obj)
      (S := (R.over U).obj)
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom).PreservesMonomorphisms :=
    (Functor.PreservesMonomorphisms.iso_iff
      (Adjunction.leftAdjointUniq hadj
        (Stacks.Sites.OverModules.presheafModuleAdjunctionsOver.{v, u, w, m}
          R.obj U).extensionRestriction)).2 hmono
  have hcomp : (SheafOfModules.forget.{max u v m} (R.over U) ⋙
      PresheafOfModules.pullback.{max u v m} (F := Over.forget U)
        (R := R.obj) (S := (R.over U).obj)
        (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom ⋙
      PresheafOfModules.sheafification.{max u v m}
        (𝟙 R.obj)).PreservesMonomorphisms := inferInstance
  exact Functor.PreservesMonomorphisms.of_iso
    (SheafOfModules.pullbackIso.{max u v m}
      (φ := (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)))).symm

/-- **Stacks 03DJ.** Extension by zero of sheaves of modules along the localization `C/U ⟶ C`
is exact, with the universe of the site, the universe of its morphisms, the universe of the
sections of the sheaf of rings and the extra module universe all independent. -/
@[stacks 03DJ "exactness of extension by zero, with the site, morphism, ring-section and \
module universes independent; this is the statement the semi-representable lower shrieks \
consume, their structure sheaves having sections in a universe larger than their sites"]
theorem extensionByZero_exact :
    exactFunctor _ _ (extensionByZero.{m, w, v, u} R U) := by
  have := presheafOverRestriction.{m, w, v, u} R U
  have hadj := extensionByZeroAdjunction.{m, w, v, u} R U
  rw [exactFunctor_iff]
  refine ⟨?_, ?_⟩
  · have hover : (overFunctor.{max u v m} R U).Additive := by
      constructor
      intro X Y f g
      ext V x
      rfl
    have : (extensionByZero.{m, w, v, u} R U).Additive := hadj.left_adjoint_additive
    have : (extensionByZero.{m, w, v, u} R U).PreservesMonomorphisms :=
      extensionByZero_preservesMonomorphisms.{m, w, v, u} R U
    have : PreservesColimits (extensionByZero.{m, w, v, u} R U) :=
      hadj.leftAdjoint_preservesColimits
    have := Functor.preservesHomology_of_preservesMonos_and_cokernels
      (extensionByZero.{m, w, v, u} R U)
    exact Functor.preservesFiniteLimits_of_preservesHomology _
  · have : PreservesColimitsOfSize.{0, 0} (extensionByZero.{m, w, v, u} R U) :=
      hadj.leftAdjoint_preservesColimits
    exact PreservesColimitsOfSize.preservesFiniteColimits _

end SheafOfModules

end
