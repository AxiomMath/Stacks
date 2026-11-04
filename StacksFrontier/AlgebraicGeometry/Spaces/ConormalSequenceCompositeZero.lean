module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceDerivationVanishing
import StacksCore.Tactic.StacksAttribute

/-!
# The composite of the conormal sequence, for an arbitrary sheaf of ideals

Let `B` be an algebraic space over a scheme `S`, let `f : X ⟶ Y` be a morphism of algebraic
spaces over `B` and let `g : Y ⟶ B` be the structure morphism.  Stacks 05ZA attaches to a closed
subspace `Z ⊆ X` with inclusion `i` the sequence
```
  𝒞_{Z/X} ⟶ i^*Ω_{X/B} ⟶ Ω_{Z/B} ⟶ 0
```
and asserts, among other things, that the composite of its two arrows is zero.  **This file
proves that clause**, both at an arbitrary sheaf of ideals in place of the defining ideal sheaf of
a closed subspace, which is the form a consumer instantiates, and at the tag's own datum.

## The statement proved

`AlgebraicGeometry.Space.submoduleTranspose_comp_pullbackDifferentialsMap_eq_zero`: let
`𝓘 ⊆ 𝒪_Y` be a subsheaf of the structure sheaf which the structure map
`f♯ : 𝒪_Y ⟶ f_*𝒪_X` annihilates, let `ψ : Ω_{Y/B} ⟶ f_*f^*Ω_{Y/B}` be the unit of `f^* ⊣ f_*`,
and let `u : 𝓘 ⟶ f_*f^*Ω_{Y/B}` be a morphism of `𝒪_Y`-modules whose value on a local section
`a` of `𝓘` is `ψ(d_{Y/B}(a))`.  Then the transpose `f^*𝓘 ⟶ f^*Ω_{Y/B}` of `u` followed by the
comparison map `c_f : f^*Ω_{Y/B} ⟶ Ω_{X/B}` of Stacks 04CX is zero.

Those hypotheses are exactly what Stacks 05ZA's datum satisfies: `𝓘` is the defining ideal sheaf
of `Z`, which is the kernel of `i♯` by `AlgebraicGeometry.Space.mem_definingIdealAt_iff`, `u` is
`AlgebraicGeometry.Space.conormalSequenceIdealDifferential`, `ψ` is the unit through which
`AlgebraicGeometry.Space.conormalSequenceUnitDerivation` is built, and the value hypothesis is
`AlgebraicGeometry.Space.conormalSequenceIdealDifferential_val_app_apply`, the clause of
that tag saying in what sense the first arrow is induced by `d_{X/B}`.  Instantiating it there is
`AlgebraicGeometry.Space.conormalSequenceIdealPullbackMap_comp_pullbackDifferentialsMap_eq_zero`
below, through the variant
`AlgebraicGeometry.Space.submoduleTranspose_comp_pullbackDifferentialsMap_eq_zero'`, which exists
so that the identification of `ψ` with the unit never has to be decided underneath a derivation
applied to a local section.

## Route

The composite is zero because its transpose is, and the transpose is computed by three steps,
each of which is available:

1. the transpose of the composite is the transpose of the first arrow followed by the direct
   image of the second (`CategoryTheory.Adjunction.homEquiv_naturality_right_symm`), and the
   transpose of the first arrow is `u` itself
   (`AlgebraicGeometry.Space.homEquiv_submoduleTranspose`);
2. on a local section `a` of `𝓘` that composite is the transpose of `c_f` applied to
   `d_{Y/B}(a)`, by the hypothesis on the values of `u` together with
   `PresheafOfModules.Derivation.postcomp_d_apply`; and the transpose of `c_f` carries
   `d_{Y/B}(a)` to `(f_*d_{X/B'})(f♯ a)`, which is the characterizing property
   `AlgebraicGeometry.Space.IsSheafOfDifferentialsMap` of Stacks 04CX, here
   `AlgebraicGeometry.Space.isSheafOfDifferentialsMap_pullbackDifferentialsMap`;
3. `f♯ a = 0`, so that value is zero, by
   `AlgebraicGeometry.Space.pushforwardUniversalDerivation_d_eq_zero`; and the transpose of the
   zero morphism is zero on sections, by
   `AlgebraicGeometry.Space.modulePullbackAdjunction_homEquiv_zero_val_app_apply`.

## Main results

* `AlgebraicGeometry.Space.isSheafOfDifferentialsMap_pullbackDifferentialsMap`: the second arrow
  of Stacks 05ZA has the characterizing property of Stacks 04CX, read at the square over the
  identity of the base, with no proof obligation left to the consumer.
* `AlgebraicGeometry.Space.homEquiv_pullbackDifferentialsMap_universalDerivation_eq_zero`: the
  transpose of the second arrow kills the universal differential of every local section that
  `f♯` kills.  This is the one non-formal step of the clause.
* `AlgebraicGeometry.Space.submoduleTranspose_comp_pullbackDifferentialsMap_eq_zero` and
  `AlgebraicGeometry.Space.submoduleTranspose_comp_pullbackDifferentialsMap_eq_zero'`: the
  composite-is-zero clause at an arbitrary sheaf of ideals, as described above; the primed form
  takes the derivation as a datum with its defining equation, which is what makes it
  instantiable at a concrete morphism of algebraic spaces.
* `AlgebraicGeometry.Space.conormalSequenceIdealPullbackMap_comp_pullbackDifferentialsMap_eq_zero`
  and `AlgebraicGeometry.Space.conormalSequenceFirstMap_comp_pullbackDifferentialsMap_eq_zero`:
  **Stacks 05ZA**, the clause at the tag's own datum, with the source of the first arrow written
  `i^*𝓘` and written `𝒞_{Z/X}`.

## Implementation notes

**Every statement below is made with the morphism of algebraic spaces a variable**, and the
statements are small on purpose.  The reason is the one the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePullbackSpellingBridge.lean` record for its own
splitting: at the concrete small étale ringed topoi of an algebraic space, identifying two
elaborations of one module category exhausts the heartbeat budget of a declaration, while the
same identification with the space a variable costs nothing.  The criteria below are therefore
stated at variables, and their hypotheses are stated on sections, which is the form in which the
statements of Stacks 05ZA supply them.  The one hypothesis that cannot be stated on
sections — that the derivation is `d_{Y/B}` followed by the unit — is stated as an equation of
derivations, for the reason the docstring of
`AlgebraicGeometry.Space.submoduleTranspose_comp_pullbackDifferentialsMap_eq_zero'` records.

**The arrow enters through `AlgebraicGeometry.Space.submoduleTranspose`** rather than as a
transposition written out.  That definition was introduced in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceDifferentials.lean` for this purpose; its
implementation notes say why, and `AlgebraicGeometry.Space.homEquiv_submoduleTranspose` is the
equation about it that step 1 of the route consumes.

## What is not proved

* **Exactness at the middle term is not proved and nothing below bears on it.**  The obstruction
  is mathematical, but it is *not* the invertibility clause of Stacks 04CS: that clause is
  proved, and so is the final sentence of Stacks 04CU which it supplies.
  What is missing is the descent of a `B`-derivation of `𝒪_X` that vanishes on the defining
  ideal sheaf along `i♯` to a `B`-derivation of `𝒪_Z`.  This is **not** the
  essential-surjectivity half of Stacks 04CJ(3) = Stacks 08M3 either: that
  clause is proved (registered under Stacks 08M3 with the key `essential_image`, on
  `Stacks.Sheaves.PushforwardEssentialImage.essImage_pushforwardModules_iff_of_isClosedImmersion`),
  and in any case it describes which *modules* are direct images, whereas a derivation is not a
  morphism of modules.  The "What is not proved" section of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceDifferentials.lean` gives the citations,
  the reduction that makes this the only missing step, and the two routes to it.
* **Exactness at the right term** is proved elsewhere:
  `AlgebraicGeometry.Space.epi_pullbackDifferentialsMap_of_isLocallySurjective` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceDifferentialsEpi.lean`, and with its
  hypothesis discharged for an immersion,
  `AlgebraicGeometry.Space.epi_pullbackDifferentialsMap_of_isImmersion` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceEpiImmersion.lean`.
* **The clause for an arbitrary immersion** rather than a closed subspace is
  `Space.conormalSequenceFirstMapOfImmersion_comp_pullbackDifferentialsMap_eq_zero` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceImmersionFirstMap.lean`, which reads the
  clause of `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceKernelIdealFirstMap.lean` out
  of the conormal module.

## References

* [Stacks Project, Tag 05ZA](https://stacks.math.columbia.edu/tag/05ZA), the conormal sequence of
  an immersion, whose composite-is-zero clause this file proves at an arbitrary sheaf of ideals.
* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX), the comparison map of a
  commutative square and its characterizing property.
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU), the adjunction
  `f^* ⊣ f_*` the transposition is taken along.
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB), the defining ideal sheaf
  of a closed subspace as the kernel of the structure map.
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y Bb : AlgebraicSpaces B S hS}

/-- **The second arrow of Stacks 05ZA has the characterizing property of Stacks 04CX.**  For
`f : X ⟶ Y` and `g : Y ⟶ B`, the comparison map
`AlgebraicGeometry.Space.pullbackDifferentialsMap` of the square with top edge `f`, right edge
`g`, left edge `f ≫ g` and bottom edge the identity of `B` satisfies
`AlgebraicGeometry.Space.IsSheafOfDifferentialsMap`: its transpose carries the universal
differential `d_{Y/B}(t)` of a local section `t` of `𝒪_Y` to `d_{X/B}(f♯ t)`.

This is `AlgebraicGeometry.Space.isSheafOfDifferentialsMap_sheafOfDifferentialsMap` at that
square, with the commutativity of the square discharged, so that a consumer reading the second
arrow of Stacks 05ZA on local sections has no side condition to supply. -/
theorem isSheafOfDifferentialsMap_pullbackDifferentialsMap (f : X ⟶ Y) (g : Y ⟶ Bb) :
    IsSheafOfDifferentialsMap B S hS f g (f ≫ g) (pullbackDifferentialsMap B S hS f g) :=
  isSheafOfDifferentialsMap_sheafOfDifferentialsMap B S hS f g (f ≫ g) (𝟙 Bb) (by simp)

/-- **The transpose of the second arrow of Stacks 05ZA kills the differentials of the sections
the structure map kills.**  If a local section `t` of `𝒪_Y` has `f♯ t = 0` — which is what it
means for `t` to be a section of the defining ideal sheaf of a closed subspace, by
`AlgebraicGeometry.Space.mem_definingIdealAt_iff` — then the transpose along `f^* ⊣ f_*` of the
comparison map carries `d_{Y/B}(t)` to zero.

This is the one non-formal step of the composite-is-zero clause of Stacks 05ZA: by the
characterizing property of Stacks 04CX that value is `(f_*d_{X/B})(f♯ t)`, and the `B`-derivation
`f_*d_{X/B} ∘ f♯` of Stacks 04CX annihilates whatever `f♯` annihilates, by
`AlgebraicGeometry.Space.pushforwardUniversalDerivation_d_eq_zero`. -/
theorem homEquiv_pullbackDifferentialsMap_universalDerivation_eq_zero (f : X ⟶ Y) (g : Y ⟶ Bb)
    (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    (t : ToType ((structureRingSheaf B S hS Y).obj.obj U))
    (ht : ((structureSharp B S hS f).hom.app U).hom t = 0) :
    (ModuleCat.Hom.hom
        (((modulePullbackAdjunction B S hS f).homEquiv (sheafOfDifferentials B S hS g)
          (sheafOfDifferentials B S hS (f ≫ g))
          (pullbackDifferentialsMap B S hS f g)).val.app U))
        ((universalDerivation B S hS g).d t) = 0 :=
  (isSheafOfDifferentialsMap_pullbackDifferentialsMap B S hS f g U t).trans
    ((pushforwardUniversalDerivation_d B S hS f g (f ≫ g) (𝟙 Bb) (by simp) U t).symm.trans
      (pushforwardUniversalDerivation_d_eq_zero B S hS f g (f ≫ g) (𝟙 Bb) (by simp) U t ht))

/-- **The composite-is-zero clause of Stacks 05ZA, at an arbitrary sheaf of ideals.**  Let
`f : X ⟶ Y` be a morphism of algebraic spaces, `g : Y ⟶ B` a structure morphism, and
`𝓘 ⊆ 𝒪_Y` a subsheaf of the structure sheaf.  Let `u : 𝓘 ⟶ f_*f^*Ω_{Y/B}` be a morphism of
`𝒪_Y`-modules such that

* `hu`: on a local section `a` of `𝓘`, `u(a)` is `ψ(d_{Y/B}(a))`, the universal differential of
  `a` followed by a morphism `ψ : Ω_{Y/B} ⟶ f_*f^*Ω_{Y/B}`;
* `hψ`: that `ψ` is the unit of the adjunction `f^* ⊣ f_*`;
* `hI`: every local section of `𝓘` is annihilated by `f♯ : 𝒪_Y ⟶ f_*𝒪_X`.

Then the transpose `α : f^*𝓘 ⟶ f^*Ω_{Y/B}` of `u` followed by the comparison map
`c_f : f^*Ω_{Y/B} ⟶ Ω_{X/B}` of Stacks 04CX is zero.

At the defining ideal sheaf of a closed subspace `Z ⊆ X` of Stacks 03MB, `hI` is
`AlgebraicGeometry.Space.mem_definingIdealAt_iff`, `α` is the first arrow
`AlgebraicGeometry.Space.conormalSequenceFirstMap` of Stacks 05ZA, `c_f` is its second arrow, and
`hu` is the clause
`AlgebraicGeometry.Space.conormalSequenceIdealDifferential_val_app_apply` of that tag; `hψ` holds
by the definition of `AlgebraicGeometry.Space.conormalSequenceUnitDerivation`, and is the one
thing standing between this statement and the clause of the tag — see the "What is not proved"
section of this file.

The arrow is given as `α` with its defining equation `hα` rather than written out, so that a
consumer instantiating this statement never has to identify two elaborations of the
transposition; the implementation notes of `AlgebraicGeometry.Space.submoduleTranspose` say why
that matters. -/
theorem submoduleTranspose_comp_pullbackDifferentialsMap_eq_zero (f : X ⟶ Y) (g : Y ⟶ Bb)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS Y)).Submodule)
    (u : I.toSheafOfModules ⟶ (modulePushforward B S hS f).obj
      ((modulePullback B S hS f).obj (sheafOfDifferentials B S hS g)))
    (ψ : sheafOfDifferentials B S hS g ⟶ (modulePushforward B S hS f).obj
      ((modulePullback B S hS f).obj (sheafOfDifferentials B S hS g)))
    (hu : ∀ (U : (SmallEtale B S hS Y.1)ᵒᵖ) (x : I.toSheafOfModules.val.obj U),
      (ModuleCat.Hom.hom (u.val.app U)) x =
        ((universalDerivation B S hS g).postcomp ψ.val).d x.1)
    (hψ : ψ = (modulePullbackAdjunction B S hS f).unit.app (sheafOfDifferentials B S hS g))
    (hI : ∀ (U : (SmallEtale B S hS Y.1)ᵒᵖ) (x : I.toSheafOfModules.val.obj U),
      ((structureSharp B S hS f).hom.app U).hom x.1 = 0)
    {α : (modulePullback B S hS f).obj I.toSheafOfModules ⟶
      (modulePullback B S hS f).obj (sheafOfDifferentials B S hS g)}
    (hα : α = submoduleTranspose B S hS f I
      ((modulePullback B S hS f).obj (sheafOfDifferentials B S hS g)) u) :
    α ≫ pullbackDifferentialsMap B S hS f g = 0 := by
  subst hα
  subst hψ
  unfold submoduleTranspose
  refine Eq.trans (Adjunction.homEquiv_naturality_right_symm _ _ _).symm ?_
  refine (Equiv.symm_apply_eq _).mpr ?_
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U ↦
    ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_))
  refine Eq.trans ?_
    (modulePullbackAdjunction_homEquiv_zero_val_app_apply B S hS f _ _ U x).symm
  refine Eq.trans (congrArg (fun y ↦ (ModuleCat.Hom.hom
      (((modulePushforward B S hS f).map
        (pullbackDifferentialsMap B S hS f g)).val.app U)) y)
    ((hu U x).trans (PresheafOfModules.Derivation.postcomp_d_apply _ _ _))) ?_
  exact homEquiv_pullbackDifferentialsMap_universalDerivation_eq_zero B S hS f g U x.1 (hI U x)

/-- **The composite-is-zero clause at an arbitrary sheaf of ideals, with the derivation named.**
This is `AlgebraicGeometry.Space.submoduleTranspose_comp_pullbackDifferentialsMap_eq_zero` with
`ψ` taken to be the unit of `f^* ⊣ f_*`, so that `hψ` becomes `rfl`, and with the derivation
supplied as a datum `D` together with its defining equation `hD` rather than written out.

**That shape is what makes the clause instantiable at a concrete morphism of algebraic spaces.**
A consumer has its hypothesis on the values of `u` stated against *its own* derivation — for
Stacks 05ZA, `AlgebraicGeometry.Space.conormalSequenceUnitDerivation` — so passing it to a
statement phrased with `AlgebraicGeometry.Space.pullbackUnitDerivation` would make the elaborator
identify the two *underneath* `PresheafOfModules.Derivation.d` applied to a local section, and at
the concrete small étale ringed topoi that does not fit in the heartbeat budget of a declaration.
Split as below, the consumer supplies its value hypothesis unchanged and discharges `hD` by
`rfl`, which is an equation of derivations at one and the same type and costs nothing. -/
theorem submoduleTranspose_comp_pullbackDifferentialsMap_eq_zero' (f : X ⟶ Y) (g : Y ⟶ Bb)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS Y)).Submodule)
    (u : I.toSheafOfModules ⟶ (modulePushforward B S hS f).obj
      ((modulePullback B S hS f).obj (sheafOfDifferentials B S hS g)))
    (D : ((modulePushforward B S hS f).obj
      ((modulePullback B S hS f).obj
        (sheafOfDifferentials B S hS g))).val.Derivation'
      (structureSharpInverseImage B S hS g).hom)
    (hD : D = pullbackUnitDerivation B S hS f g)
    (hu : ∀ (U : (SmallEtale B S hS Y.1)ᵒᵖ) (x : I.toSheafOfModules.val.obj U),
      (ModuleCat.Hom.hom (u.val.app U)) x = D.d x.1)
    (hI : ∀ (U : (SmallEtale B S hS Y.1)ᵒᵖ) (x : I.toSheafOfModules.val.obj U),
      ((structureSharp B S hS f).hom.app U).hom x.1 = 0)
    {α : (modulePullback B S hS f).obj I.toSheafOfModules ⟶
      (modulePullback B S hS f).obj (sheafOfDifferentials B S hS g)}
    (hα : α = submoduleTranspose B S hS f I
      ((modulePullback B S hS f).obj (sheafOfDifferentials B S hS g)) u) :
    α ≫ pullbackDifferentialsMap B S hS f g = 0 := by
  subst hD
  exact submoduleTranspose_comp_pullbackDifferentialsMap_eq_zero B S hS f g I u
    ((modulePullbackAdjunction B S hS f).unit.app (sheafOfDifferentials B S hS g))
    hu rfl hI hα

/-- **Stacks 05ZA, the composite of the two arrows is zero**, at a subspace inclusion
`i : Z ⟶ X` of `Z ⊆ X` with structure morphism `b : X ⟶ B`: the first arrow
`AlgebraicGeometry.Space.conormalSequenceIdealPullbackMap`, which is the first arrow
`𝒞_{Z/X} ⟶ i^*Ω_{X/B}` with its source written `i^*𝓘`, followed by the second arrow
`i^*Ω_{X/B} ⟶ Ω_{Z/B}` of Stacks 04CX, is the zero morphism.

Every hypothesis of
`AlgebraicGeometry.Space.submoduleTranspose_comp_pullbackDifferentialsMap_eq_zero'` is supplied
by a proved statement: `D` is `AlgebraicGeometry.Space.conormalSequenceUnitDerivation` and `hD`
its defining equation; `hu` is
`AlgebraicGeometry.Space.conormalSequenceIdealDifferential_val_app_apply`, the clause of this tag
saying in what sense `d_{X/B}` induces the first arrow; `hI` is
`AlgebraicGeometry.Space.mem_definingIdealAt_iff`, the defining ideal sheaf of Stacks 03MB being
the kernel of `i♯`; and `hα` is the definition of the first arrow. -/
theorem conormalSequenceIdealPullbackMap_comp_pullbackDifferentialsMap_eq_zero
    (Z : ClosedSubspaces B S hS Y.1) (b : Y ⟶ Bb) :
    conormalSequenceIdealPullbackMap B S hS Z b ≫
      pullbackDifferentialsMap B S hS (subspaceInclusion B S hS Y Z) b = 0 :=
  submoduleTranspose_comp_pullbackDifferentialsMap_eq_zero' B S hS
    (subspaceInclusion B S hS Y Z) b (definingIdealSheaf B S hS Y Z)
    (conormalSequenceIdealDifferential B S hS Z b)
    (conormalSequenceUnitDerivation B S hS Z b) rfl
    (conormalSequenceIdealDifferential_val_app_apply B S hS Z b)
    (fun U x ↦ (mem_definingIdealAt_iff B S hS Y Z U x.1).1 x.2)
    rfl

/-- **Stacks 05ZA, the composite of the two arrows is zero**, read at
`AlgebraicGeometry.Space.conormalSequenceFirstMap`, that is with the source of the first arrow
written as the conormal module `𝒞_{Z/X}` of Stacks 04CN rather than as `i^*𝓘`.  The two readings
are the same morphism, by `AlgebraicGeometry.Space.conormalModule_eq`.

This is the shape in which the clause is consumed: it is the `hzero` hypothesis carried by
`AlgebraicGeometry.Space.thickeningConormalSequence_exact` of Stacks 060F and by
`AlgebraicGeometry.Space.epi_thickeningConormalFirstMap` of Stacks 060G. -/
@[stacks 05ZA "the composite of the two arrows is zero, at a subspace inclusion, with the first \
arrow read out of the conormal module `𝒞_{Z/X}` of 04CN.  The same clause at the first arrow of \
an arbitrary immersion is \
`conormalSequenceFirstMapOfImmersion_comp_pullbackDifferentialsMap_eq_zero`"]
theorem conormalSequenceFirstMap_comp_pullbackDifferentialsMap_eq_zero
    (Z : ClosedSubspaces B S hS Y.1) (b : Y ⟶ Bb) :
    conormalSequenceFirstMap B S hS Z b ≫
      pullbackDifferentialsMap B S hS (subspaceInclusion B S hS Y Z) b = 0 :=
  conormalSequenceIdealPullbackMap_comp_pullbackDifferentialsMap_eq_zero B S hS Z b

end AlgebraicGeometry.Space

end
