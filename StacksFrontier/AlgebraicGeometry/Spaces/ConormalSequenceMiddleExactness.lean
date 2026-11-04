module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceComplex
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceDifferentialsEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureSharpInverseImage
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardDerivation
import StacksCore.Tactic.StacksAttribute

/-!
# Exactness at the middle term of the conormal sequence, reduced to one statement

Let `Z` be a closed subspace of an algebraic space `X` over `Bb` with inclusion `i : Z ⟶ X` and
defining ideal sheaf `𝓘 ⊆ 𝒪_X`.  Stacks 05ZA asserts that
```
  𝒞_{Z/X} ⟶ i^*Ω_{X/Bb} ⟶ Ω_{Z/Bb} ⟶ 0
```
is exact.  Two of its three clauses are proved in this tree: the composite of the two arrows is
zero (`AlgebraicGeometry.Space.conormalSequenceFirstMap_comp_pullbackDifferentialsMap` of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceComplex.lean`, unconditionally) and the
second arrow is an epimorphism
(`AlgebraicGeometry.Space.epi_pullbackDifferentialsMap_of_isLocallySurjective` of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceDifferentialsEpi.lean`).  Exactness at the
middle term is the one that is open.

This file does two things: it records that the clause at the right is **unconditional** for a
closed subspace, and it **reduces the clause at the middle to a single statement about
derivations** and proves the reduction.

**The clause at the right is unconditional.**  `ConormalSequenceDifferentialsEpi.lean` states it
at a hypothesis `hsharp`, local surjectivity of `i♯ : i⁻¹𝒪_X ⟶ 𝒪_Z`, and that hypothesis is
available:
`AlgebraicGeometry.Space.isLocallySurjective_structureSharpInverseImage` of
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionStructureSharpInverseImage.lean:145` is the
inverse-image form, for a closed immersion, and its own docstring names that `hsharp` as what it
discharges.  The inclusion of a closed subspace is a closed immersion, so
`AlgebraicGeometry.Space.epi_pullbackDifferentialsMap_subspaceInclusion` below needs no
hypothesis at all.

## The reduction

Over the epimorphism at the right, exactness at the middle says exactly that the second arrow is
a *cokernel* of the first, and the epimorphism makes the uniqueness half of that colimit free
(`CategoryTheory.Limits.CokernelCofork.IsColimit.ofπ'`).  So only the factorization has to be
produced: every `h : i^*Ω_{X/Bb} ⟶ M` of `𝒪_Z`-modules killed by the first arrow factors through
the second.  Both sides of that are translated into derivations and nothing else is used:

1. Equation 0619, `AlgebraicGeometry.Space.derivationDirectImageEquiv`, is a bijection from the
   morphisms `i^*Ω_{X/Bb} ⟶ M` onto the `Bb`-derivations of `𝒪_X` with values in `i_*M`.
2. Under it, *`h` is killed by the first arrow* becomes *the derivation vanishes on every local
   section of `𝓘`*.  That is
   `AlgebraicGeometry.Space.derivationDirectImageEquiv_d_eq_zero_of_comp_eq_zero`, proved from
   `AlgebraicGeometry.Space.conormalSequenceIdealDifferential_val_app_apply` (the first arrow is
   the transpose of `d_{X/Bb}` restricted to `𝓘`) together with
   `AlgebraicGeometry.Space.conormalSequenceUnitDerivation_d` and
   `AlgebraicGeometry.Space.modulePullbackAdjunction_homEquiv_zero_val_app_apply`.
3. Under it, *precomposition with the second arrow* becomes *the direct image of derivations*,
   by `AlgebraicGeometry.Space.derivationDirectImageEquiv_sheafOfDifferentialsMap_comp` of
   `StacksFrontier/AlgebraicGeometry/Spaces/PushforwardDerivation.lean`, the second arrow being
   the comparison map of Stacks 04CX for the square over the identity of `Bb`.
4. The universal property of `Ω_{Z/Bb}`, `AlgebraicGeometry.Space.differentialsHomEquiv`, turns
   a `Bb`-derivation of `𝒪_Z` back into a morphism `Ω_{Z/Bb} ⟶ M`.

What is left over is the hypothesis `hdesc` of
`AlgebraicGeometry.Space.exact_conormalSequence_of_exists_pushforwardDerivation`: *for every
`𝒪_Z`-module `M`, every `Bb`-derivation of `𝒪_X` with values in `i_*M` which vanishes on every
local section of `𝓘` is the direct image of a `Bb`-derivation of `𝒪_Z` with values in `M`.*
The injectivity half of that bijection is not needed — it is the epimorphism at the right, and
it is already proved.

## Main definitions

* `AlgebraicGeometry.Space.conormalPushforwardDerivation`: the direct image along `i` of a
  `Bb`-derivation of `𝒪_Z`, that is `AlgebraicGeometry.Space.pushforwardDerivation` for the
  square over the identity of `Bb`.

## Main results

* `AlgebraicGeometry.Space.derivationDirectImageEquiv_d_eq_zero_of_comp_eq_zero`: a morphism out
  of `i^*Ω_{X/Bb}` killed by the first arrow corresponds to a derivation vanishing on `𝓘`.
* `AlgebraicGeometry.Space.epi_pullbackDifferentialsMap_subspaceInclusion`: **Stacks 05ZA**,
  exactness at the right term, unconditionally for a closed subspace.
* `AlgebraicGeometry.Space.exact_conormalSequence_of_exists_pushforwardDerivation`: **exactness
  at the middle term**, granted `hdesc` and nothing else.

## What is not proved here

**The hypothesis `hdesc` is not discharged in this module**, and it is the whole of the
remaining content of the clause: the surjectivity of the direct image of derivations onto the
derivations vanishing on `𝓘`.

**It is discharged, unconditionally for a closed subspace,** in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceThickeningDescent.lean`, by
`AlgebraicGeometry.Space.exists_conormalPushforwardDerivation_eq`, which gives exactness at the
middle term there as `AlgebraicGeometry.Space.exact_conormalSequence`, and that is where
Stacks 05ZA is registered for the middle clause.  Only one step of the route uses anything about
the inclusion beyond its being a morphism — the vanishing of the transpose of the derivation on
the sections killed by `i^♯` in inverse-image form — and what it uses is that `i` is a closed
immersion, through the invertibility of the counit `i^{-1}i_*𝒪_Z ⟶ 𝒪_Z` of Stacks 04E5,
part (1).

### What is available for it

Both of the things it needs are available, and they are connected to each other.

* **The full faithfulness.**  A section of `𝒪_Z` over an object `V` of the small étale site of
  `Z` is not in the image of any structure map in general, so a derivation of `𝒪_Z` has to be
  built from the data on the base-changed objects.  Cover density of the chart base change along
  a closed immersion, `AlgebraicGeometry.Space.smallBaseChange_isCoverDense_of_isClosedImmersion`,
  with local fullness gives full faithfulness of the direct image at any coefficients,
  `AlgebraicGeometry.Space.fullyFaithfulSmallEtaleRestriction` of
  `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtalePushforwardFullyFaithful.lean:166` — at abelian
  coefficients this is `@[stacks 04E5]` part (2),
  `AlgebraicGeometry.Space.fullyFaithfulSmallEtaleAbelianPushforwardOfIsClosedImmersion` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionChartBaseChangeDense.lean:388`, at a free
  coefficient universe.
* **The comparison that made it inapplicable here.**  That direct image is *restriction along the
  chart base-change functor*, whereas the direct image in the sequence above is
  `AlgebraicGeometry.Space.modulePushforward`, built from the right Kan extension
  `AlgebraicGeometry.Space.smallEtaleDirectImageRan`.  The comparison of the two was available at
  sheaves of sets (`AlgebraicGeometry.Space.smallEtaleRingedToposHom_representable`), at sheaves
  of commutative rings (`AlgebraicGeometry.Space.smallEtaleRingedToposHom_representableRing`),
  both in `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleRingedToposHom.lean`, and at sheaves of
  modules (`AlgebraicGeometry.Space.modulePushforwardChartIso` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardChartComparison.lean:518`) — but not at
  sheaves of abelian groups, which is the one category 04E5, part (2) is stated in.  It is now
  `AlgebraicGeometry.Space.abelianPushforwardChartIso` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardAbelianChartComparison.lean:114`, and
  04E5, part (2) read through it is
  `AlgebraicGeometry.Space.abelianPushforwardPreimage` there at `:157`: for a closed immersion
  every morphism `i_*M ⟶ i_*N` of sheaves of abelian groups is the direct image of a *unique*
  morphism `M ⟶ N` of abelian sheaves
  (`AlgebraicGeometry.Space.abelianPushforward_map_abelianPushforwardPreimage` at `:170` and
  `AlgebraicGeometry.Space.abelianPushforwardPreimage_unique` at `:186`).  Unlike the
  module-level comparison it is built from, this one *does* have a reading on sections:
  `AlgebraicGeometry.Space.abelianPushforwardChartIso_hom_app` at `:134`, by `rfl`.

### The abelian route above is not the route, and the descent is already proved

**The abelian-cokernel route recorded above is the long way round, and it is blocked.**  Over
`AlgebraicGeometry.Space.abelianDesc` the two deliver an *additive* morphism `χ : 𝒪_Z ⟶ M` of
sheaves of abelian groups on the small étale site of `Z`, uniquely determined by `D`; an additive
morphism is not a derivation, and any reading of `χ` on sections has to go through
`AlgebraicGeometry.Space.abelianPushforward_map_abelianPushforwardPreimage`, an equality of
morphisms conjugated by `AlgebraicGeometry.Space.abelianPushforwardChartIso`.  **That
equality cannot be specialised to a concrete morphism inside the default heartbeat budget** — the
*statement* dies at `whnf` before any proof begins — and
`CategoryTheory.Functor.sheafPushforwardContinuous` at the inclusion loses its
`CategoryTheory.Functor.IsContinuous` instance there, which
`AlgebraicGeometry.Space.isContinuous_smallBaseChange` as a local instance does not restore.

What is *not* blocked is the reading on sections.
`AlgebraicGeometry.Space.abelianPushforwardChartIso_hom_app` moves the question to
`AlgebraicGeometry.Space.modulePushforwardChartIso`, exactly as its docstring says, and that
component *is* read on sections:
`AlgebraicGeometry.Space.modulePushforwardChartIso_hom_app_val_app` of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleBaseChangeChartUnit.lean` identifies it with the
chart projection `AlgebraicGeometry.Space.chartSetProj`, natural in the sheaf by
`AlgebraicGeometry.Space.chartSetProj_naturality`.  So the blockage is the conjugation of the
*abelian* equality, not the comparison itself.

**The short way is available.**
`StacksFrontier/AlgebraicGeometry/Spaces/LiftDifferenceDescent.lean` carries, at general-site level,
the structure `Stacks.Sites.QuotientDerivation q M` — sectionwise derivation data on a sheaf of
rings `A` through a morphism `q : A ⟶ O` with values in an `O`-module — together with
`Stacks.Sites.QuotientDerivation.descend`, `descend_app`, `descend_map`, `descend_eq_zero` and,
crucially, `descend_mul`: the Leibniz rule for the descended derivation, proved by comparing both
sides over the intersection of the two image sieves on which the two sections lift.  That is
exactly the pair-lifting the Leibniz rule needs, written out.

Applied at `q := i♯` it discharges residues 1 and 2 outright.
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceVanishingDerivationDescent.lean` is that
application: `AlgebraicGeometry.Space.conormalQuotientDerivation` converts `D` together with its
vanishing on `𝓘` into `QuotientDerivation` data — all four fields with no transport, the
`𝒪_X`-action on `i_*M` being by definition the `i_*𝒪_Z`-action through `i♯`, by
`AlgebraicGeometry.Space.restrictScalars_moduleDirectImage`, and the kernel of `i♯` being `𝓘` by
`AlgebraicGeometry.Space.mem_definingIdealAt_iff` — and
`AlgebraicGeometry.Space.conormalDescend` with
`AlgebraicGeometry.Space.conormalDescend_structureSharp`,
`AlgebraicGeometry.Space.conormalDescend_mul`, `AlgebraicGeometry.Space.conormalDescend_map` and
`AlgebraicGeometry.Space.conormalDescend_base_eq_zero` is the resulting derivation of `i_*𝒪_Z`
with values in `i_*M`, with its Leibniz rule, its naturality and its vanishing on the base.

### What is still missing

**One thing: the transfer from the site of `X` to the site of `Z`.**  The descent above is a
derivation of `i_*𝒪_Z` on the small étale site of `X`; `hdesc` asks for a derivation of `𝒪_Z` on
the small étale site of `Z`.  The bundling that would finish it is also available —
`AlgebraicGeometry.Space.descendedDerivation` of `LiftDifferenceDescent.lean` turns a
`QuotientDerivation q M` for a locally surjective `q : A ⟶ 𝒪_Y`, plus the vanishing on the base,
into a `CategoryTheory.PresheafOfModules.Derivation'` of `𝒪_Y`.  Instantiated at `Y := Z`,
`A := AlgebraicGeometry.Space.structureRingSheafInverseImage` at `i` and
`q := AlgebraicGeometry.Space.structureSharpRingInverseImage` at `i` — whose local surjectivity
at the inclusion of a closed subspace is an instance — it has exactly the type `hdesc` asks for,
and what it needs is the derivation data `(i^{-1}𝒪_X)(W) →+ M(W)`.

**The underlying function of that datum is available, and what is left is three pointwise
identities about it** — additivity, the Leibniz rule through `q`, and vanishing on the sections
`q` kills.  The implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceVanishingDerivationDescent.lean` record
the details: which identifications hold on the nose, which product-transport lemmas the
three identities have to be carried across, why the two remaining obligations (`hzero` and
`conormalPushforwardDerivation … D' = D`) need no chart comparison at all, and why the chart
route is open as well.

It must **not** be routed through a chart comparison of the *first* arrow: nothing relates
`AlgebraicGeometry.Space.conormalModule` on a chart to any scheme-level conormal sheaf, and the
re-anchoring needed to state one does not terminate.

Closure of local surjectivity under binary products, which `descend_mul` does by hand and which
Mathlib's `CategoryTheory.Presheaf.IsLocallySurjective` API does not have — the additive route
being blocked because `CategoryTheory.Limits.prod.map_epi` asks for binary *biproducts* — is now
available as a lemma in its own right: `CategoryTheory.Presheaf.isLocallySurjective_prodMap` of
`StacksFrontier/CategoryTheory/Sites/LocallySurjectiveProduct.lean`, proved by two base changes.

The general site-level bijection between derivations into a direct image and derivations of an
inverse-image ring sheaf, `Stacks.Sheaves.Differentials.directImageDerivationEquiv` of
`StacksFrontier/CategoryTheory/Sites/Modules/DifferentialsInverseImage.lean`, is **not** usable as a
substitute for that transfer: besides being for the inverse-image ring sheaf, it asks for
`[CategoryTheory.SmallCategory C]`, and the small étale site has its objects in `Type (u + 1)`
and its morphisms in `Type u`.

## What is registered, and what is not

Stacks 05ZA is registered on
`AlgebraicGeometry.Space.epi_pullbackDifferentialsMap_subspaceInclusion`, which is proved
outright.  It is **not** registered on
`AlgebraicGeometry.Space.exact_conormalSequence_of_exists_pushforwardDerivation`: that statement
is conditional on `hdesc`, and `hdesc` is not a clause of some other tag — it is this clause's
own content, so registering the tag there would assert what is not proved.  It is not registered
on the thickening case either: 05ZA is about an arbitrary immersion.

Consumers that carry the clause as a hypothesis call it `h05ZA`, and there are two:
`ConormalSequenceFormallyUnramified.lean:291` and `ConormalSequenceUnramifiedPair.lean:160`.
Where the consumer is stated at a universal first-order thickening the thickening case discharges
it, through `AlgebraicGeometry.Space.exact_conormalSequence_universalThickening` of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceFormallyUnramifiedMiddleExact.lean:71`;
`ConormalSequenceFormallySmoothSplitting.lean` carries it nowhere.

## References

* [Stacks Project, Tag 05ZA](https://stacks.math.columbia.edu/tag/05ZA)
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619), the bijection used in
  steps 1, 3 and 4.
* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX), the comparison map that
  the second arrow is.
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB), whose surjectivity
  clause in inverse-image form is what makes the clause at the right unconditional.
* [Stacks Project, Tag 01UZ](https://stacks.math.columbia.edu/tag/01UZ), the scheme case.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Bb : AlgebraicSpaces B S hS}

section Middle

variable (Z : ClosedSubspaces B S hS X.1) (b : X ⟶ Bb)

/-- The direct image along the inclusion of a closed subspace of a `Bb`-derivation of `𝒪_Z`. -/
noncomputable abbrev conormalPushforwardDerivation
    (M : Modules.{u, u} B S hS Z.1.toFunctor Z.2.1)
    (D : M.val.Derivation'
      (structureSharpInverseImage B S hS (subspaceInclusion B S hS X Z ≫ b)).hom) :
    ((modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj M).val.Derivation'
      (structureSharpInverseImage B S hS b).hom :=
  pushforwardDerivation B S hS (subspaceInclusion B S hS X Z ≫ b) M D
    (subspaceInclusion B S hS X Z) b (𝟙 Bb) (by simp)

/-- A morphism out of `i^*Ω_{X/Bb}` killed by the first arrow of Stacks 05ZA corresponds, under
Equation 0619, to a `Bb`-derivation of `𝒪_X` vanishing on every local section of the defining
ideal sheaf. -/
theorem derivationDirectImageEquiv_d_eq_zero_of_comp_eq_zero
    (M : Modules.{u, u} B S hS Z.1.toFunctor Z.2.1)
    (h : (modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
        (sheafOfDifferentials B S hS b) ⟶ M)
    (hh : conormalSequenceFirstMap B S hS Z b ≫ h = 0)
    (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : (definingIdealSheaf B S hS X Z).toSheafOfModules.val.obj U) :
    (derivationDirectImageEquiv B S hS (subspaceInclusion B S hS X Z) b M h).d x.1 = 0 := by
  have hh' : conormalSequenceIdealPullbackMap B S hS Z b ≫ h = 0 := hh
  -- the transpose of `h` precomposed with the adjoint form of the first arrow is the transpose
  -- of the zero morphism
  have key : conormalSequenceIdealDifferential B S hS Z b ≫
      (modulePushforward B S hS (subspaceInclusion B S hS X Z)).map h =
      (modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).homEquiv
        (definingIdealSheaf B S hS X Z).toSheafOfModules M
        (0 : (modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
            (definingIdealSheaf B S hS X Z).toSheafOfModules ⟶ M) := by
    refine (Equiv.symm_apply_eq _).mp ?_
    refine Eq.trans (Adjunction.homEquiv_naturality_right_symm
      (modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z))
      (conormalSequenceIdealDifferential B S hS Z b) h) ?_
    exact (congrArg (fun m ↦ m ≫ h)
      (conormalSequenceIdealPullbackMap_eq_homEquiv_symm B S hS Z b).symm).trans hh'
  have hvanish : (ModuleCat.Hom.hom
      ((conormalSequenceIdealDifferential B S hS Z b ≫
        (modulePushforward B S hS (subspaceInclusion B S hS X Z)).map h).val.app U)) x = 0 :=
    (congrArg (fun m ↦ (ModuleCat.Hom.hom (m.val.app U)) x) key).trans
      (modulePullbackAdjunction_homEquiv_zero_val_app_apply B S hS
        (subspaceInclusion B S hS X Z) (definingIdealSheaf B S hS X Z).toSheafOfModules M U x)
  refine Eq.trans ?_ hvanish
  refine Eq.trans (congrArg (fun m ↦ (ModuleCat.Hom.hom (m.val.app U))
      ((universalDerivation B S hS b).d x.1))
    (Adjunction.homEquiv_unit (adj :=
      modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z))
      (X := sheafOfDifferentials B S hS b) (Y := M) (f := h))) ?_
  refine congrArg (ModuleCat.Hom.hom
      (((modulePushforward B S hS (subspaceInclusion B S hS X Z)).map h).val.app U)) ?_
  exact (conormalSequenceUnitDerivation_d B S hS Z b U x.1).symm.trans
    (conormalSequenceIdealDifferential_val_app_apply B S hS Z b U x).symm

/-- **Stacks 05ZA, exactness at the right term, unconditionally for a closed subspace.**  The
second arrow `i^*Ω_{X/Bb} ⟶ Ω_{Z/Bb}` of the sequence of Stacks 05ZA is an epimorphism.

`AlgebraicGeometry.Space.epi_pullbackDifferentialsMap_of_isLocallySurjective` proves this from
local surjectivity of `i♯ : i⁻¹𝒪_X ⟶ 𝒪_Z`, which that module's implementation notes record as
*carried*; it is not carried any more, and for a closed immersion it is proved —
`AlgebraicGeometry.Space.isLocallySurjective_structureSharpInverseImage` of
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionStructureSharpInverseImage.lean`, the
inverse-image form of the surjectivity clause of Stacks 03MB — and the inclusion of a closed
subspace is a closed immersion by `Z.2.2`. -/
@[stacks 05ZA "exactness at the right term: the second arrow `i^*Ω_{X/Bb} ⟶ Ω_{Z/Bb}` is an \
epimorphism.  UNCONDITIONAL for a closed subspace: the local surjectivity of \
`i♯ : i⁻¹𝒪_X ⟶ 𝒪_Z` that `epi_pullbackDifferentialsMap_of_isLocallySurjective` carries as \
`hsharp` is `isLocallySurjective_structureSharpInverseImage`, the inverse-image form of the \
surjectivity clause of 03MB, applied to the closed immersion `Z.2.2`"]
theorem epi_pullbackDifferentialsMap_subspaceInclusion :
    Epi (pullbackDifferentialsMap B S hS (subspaceInclusion B S hS X Z) b) :=
  epi_pullbackDifferentialsMap_of_isLocallySurjective B S hS
    (subspaceInclusion B S hS X Z) b
    (isLocallySurjective_structureSharpInverseImage B S hS
      (subspaceInclusion B S hS X Z) Z.2.2)

/-- **Exactness at the middle term of the sequence of Stacks 05ZA, reduced to one statement
about derivations.**  Granted `hdesc` — that every `Bb`-derivation of `𝒪_X` with values in
`i_*M` which vanishes on every local section of the defining ideal sheaf is the direct image
`AlgebraicGeometry.Space.conormalPushforwardDerivation` of a `Bb`-derivation of `𝒪_Z` with
values in `M` — the short complex `𝒞_{Z/X} ⟶ i^*Ω_{X/Bb} ⟶ Ω_{Z/Bb}` is exact at the middle
term.

Nothing else is carried: the epimorphism at the right, which makes the uniqueness half of the
cokernel free, is `AlgebraicGeometry.Space.epi_pullbackDifferentialsMap_subspaceInclusion`
above, unconditional for a closed subspace. -/
theorem exact_conormalSequence_of_exists_pushforwardDerivation
    (hdesc : ∀ (M : Modules.{u, u} B S hS Z.1.toFunctor Z.2.1)
      (D : ((modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj M).val.Derivation'
        (structureSharpInverseImage B S hS b).hom),
      (∀ (U : (SmallEtale B S hS X.1)ᵒᵖ)
        (x : (definingIdealSheaf B S hS X Z).toSheafOfModules.val.obj U), D.d x.1 = 0) →
      ∃ D' : M.val.Derivation'
          (structureSharpInverseImage B S hS (subspaceInclusion B S hS X Z ≫ b)).hom,
        conormalPushforwardDerivation B S hS Z b M D' = D) :
    (ShortComplex.mk _ _
      (conormalSequenceFirstMap_comp_pullbackDifferentialsMap B S hS Z b)).Exact := by
  have := epi_pullbackDifferentialsMap_subspaceInclusion B S hS Z b
  refine ShortComplex.exact_of_g_is_cokernel _ (CokernelCofork.IsColimit.ofπ' _ _ ?_)
  intro N k hk
  have hex := hdesc N
    (derivationDirectImageEquiv B S hS (subspaceInclusion B S hS X Z) b N k)
    (derivationDirectImageEquiv_d_eq_zero_of_comp_eq_zero B S hS Z b N k hk)
  refine ⟨(differentialsHomEquiv B S hS
    (subspaceInclusion B S hS X Z ≫ b) N).symm hex.choose, ?_⟩
  refine (derivationDirectImageEquiv B S hS
    (subspaceInclusion B S hS X Z) b N).injective ?_
  refine Eq.trans ?_ hex.choose_spec
  refine Eq.trans (derivationDirectImageEquiv_sheafOfDifferentialsMap_comp B S hS
    (subspaceInclusion B S hS X Z) b (subspaceInclusion B S hS X Z ≫ b) (𝟙 Bb) (by simp) N
    ((differentialsHomEquiv B S hS (subspaceInclusion B S hS X Z ≫ b) N).symm
      hex.choose)) ?_
  exact congrArg (fun E ↦ conormalPushforwardDerivation B S hS Z b N E)
    (Equiv.apply_symm_apply
      (differentialsHomEquiv B S hS (subspaceInclusion B S hS X Z ≫ b) N) hex.choose)

end Middle

end AlgebraicGeometry.Space

end
