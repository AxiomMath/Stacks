module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatOpenRestriction
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TorAmplitudeStalkwise
public import StacksFrontier.Homology.Tor.DerivedTensorTor
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedTensor.Tor
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.FlatModuleSheavesAndStalks
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.DerivedTensorStalk
public import StacksFrontier.Topology.Sheaves.Modules.StalkTensorRing
import StacksCore.Tactic.StacksAttribute

/-!
# Tor measures the deviation of flatness

Let `(X, 𝒪_X)` be a ringed space and `ℱ` an `𝒪_X`-module. This file proves that `ℱ` is flat
exactly when the sheaf `Tor_1^{𝒪_X}(ℱ, 𝒢)` of [Stacks, Tag 08BP] vanishes for every
`𝒪_X`-module `𝒢`. This is [Stacks, Tag 08BQ], clause (2) being the tag's own `Tor_1`:
`Stacks.Cohomology.tor X 1 ℱ 𝒢`, the degree `-1` cohomology of `ℱ ⊗^{L}_{𝒪_X} 𝒢`.

## Main results

* `Stacks.Cohomology.flat_iff_forall_isZero_tor`: **[Stacks, Tag 08BQ]**, with clause (2) read
  as the vanishing of the sheaf `Tor_1` of Tag 08BP.
* `Stacks.SheafOfModules.DerivedTensorStalk.isZero_derivedTensorHomology_iff_forall_isZero_tor`:
  **the identification the tag's clause (2) needs.** The sheaf `Tor_p^{𝒪_X}(ℱ, 𝒢)` of Tag 08BP
  vanishes exactly when the classical module-theoretic `Tor_p` of the stalks vanishes at every
  point.
* `AlgebraicGeometry.SheafOfModules.flat_stalk_ringCat_iff_commRingCat`: flatness of the stalk
  of a sheaf of modules does not depend on which of the two stalk rings is used.
* `AlgebraicGeometry.SheafOfModules.isZero_homologyFunctor_obj_iff_forall_stalk`: a single
  cohomology sheaf of an object of `D(𝒪_X)` vanishes exactly when it vanishes at every stalk.

## Implementation notes

### The two `Tor`s, and why the identification was the missing step

Two notions of `Tor_1` are in play. The source's, Tag 08BP, is the sheaf
`H^{-1}(ℱ ⊗^{L}_{𝒪_X} 𝒢)`, which in this development is `Stacks.Cohomology.tor X 1 ℱ 𝒢`. The
other is the stalkwise, module-theoretic one `OXModule.Tor1Stalk`, over the local rings
`𝒪_{X,x}`, for which `OXModule.flatStalkwise_iff_forall_tor1` already proved the equivalence
with stalkwise flatness. `OXModule.flat_iff_tor1_eq_zero` is that equivalence composed with
Tag 05NE, and on its own it is strictly weaker than Tag 08BQ: it says nothing about the sheaf
`Tor_1` the tag's clause (2) is about. The identification of the two is what this file supplies,
and `Stacks.Cohomology.flat_iff_forall_isZero_tor` is the resulting statement of the tag.

The chain, at a point `x`, is: vanishing of a sheaf is stalkwise
(`AlgebraicGeometry.SheafOfModules.isZero_iff_forall_isZero_stalkFunctor_obj`, Tag 01AG); the
stalk functor is exact, so it commutes with `H^{-1}`
(`CategoryTheory.Functor.mapDerivedCategoryHomologyIso`); taking stalks carries the derived
tensor product of Tag 06YU to the canonical one over the stalk ring
(`Stacks.SheafOfModules.DerivedTensorStalk.derivedTensorStalkIso`, the derived form of
Tag 01CB); and `H^{-p}` of the derived tensor product of two modules over a commutative ring is
their `Tor_p` (`Stacks.DerivedTensor.homologyIsoTor`).

### The two stalk rings

A ringed space has two stalk rings at a point and they are not the same type: the colimit of
`𝒪_X` taken in `CommRingCat`, which `OXModule.stalk` and Tag 05NE are stated over, and the
colimit taken in `RingCat` after composing with `forget₂`, which is what the sheaf-of-modules
stalk functor and the derived tensor product of
`Stacks.SheafOfModules.DerivedTensorStalk` are formed relative to. The underlying abelian group
of the module stalk is literally the same in both; only the ring acting differs, and the two
actions correspond under `SemilinearStalk.commStalkRingEquiv`
(`AlgebraicGeometry.SheafOfModules.commStalk_smul_eq`). `flat_stalk_ringCat_iff_commRingCat`
moves `Module.Flat` across that gap.

Two things about that step are worth recording, because both cost real time to establish.

*Mathlib has no flatness transfer along a ring isomorphism at all* — there is no
`Module.Flat.of_ringEquiv` and no `Flat.congr`; every Mathlib transfer lemma
(`Module.Flat.of_linearEquiv`, `Module.Flat.equiv_iff`) keeps the base ring fixed.
`AlgebraicGeometry.SheafOfModules.isFlat_of_ringEquiv` is this repository's own and is the only
ring-changing one in the tree, so it is what the step below uses. (The repository also has
`Module.Flat.of_semilinearEquiv`, which is the same fact in the shape that bundles an additive
isomorphism; `isFlat_of_ringEquiv` is the special case of one carrier with two actions, which is
the case here.)

*The scalar-agreement input is universe-trapped, and is duplicated eight times over.* The lemma
wanted is "the two stalk actions agree through `SemilinearStalk.commStalkRingEquiv`". Its
original, `SemilinearStalk.comm_smul_eq`
(`StacksFrontier/Topology/Sheaves/Functors/Module/SemilinearStalk.lean:359`), writes the stalk's
abelian group as `Ab.{u}` with the universe left implicit, so it elaborates at `0` and the lemma
speaks only about spaces in `Type`; it cannot be applied at `TopCat.{u}`. The copy used here is
`AlgebraicGeometry.SheafOfModules.commStalk_smul_eq`
(`StacksFrontier/Topology/Sheaves/Modules/StalkTensorRing.lean:96`), which is universe-correct. Six
further copies of the same statement exist, three public and three private, each re-proved by
the same germ-chasing argument:
`AlgebraicGeometry.StalkFiniteType.RingCatStalk.comm_smul_eq` (`:88`, universe-correct),
`Stacks.SheafOfModules.TensorStalkRingedSpace.commStalk_smul_eq`
(`StacksFrontier/Topology/Sheaves/Modules/Generators/TensorGloballyGenerated.lean:57`, at a
`RingedSpace`), and the private `comm_smul_eq_universe`
(`StacksFrontier/AlgebraicGeometry/Morphisms/Flat/IsoTransport.lean:65`), `comm_smul_eq_at_stalk`
(`StacksFrontier/AlgebraicGeometry/Modules/FiniteLocallyFreeTFAE.lean:306`), `commStalk_smul_eq`
(`StacksFrontier/AlgebraicGeometry/Chow/PeriodicComplexHomologyCycles.lean:995`) and
`exists_commStalk_smul_eq`
(`StacksFrontier/AlgebraicGeometry/ProjectiveFromSections/FreePresentation.lean:118`). Only
`StalkTensorRing`'s and `RingCatStalk`'s are usable at a general universe. Anything new should
use `StalkTensorRing`'s and the rest should be retired onto it.

`flat_stalk_ringCat_iff_commRingCat` is stated at the presheaf spelling
`R ⋙ forget₂ CommRingCat RingCat`, which is the one `StacksDraft.StalkTensor.commRing_stalk` is
keyed on, so that the commutativity of the `RingCat`-valued stalk is found by synthesis.

For the same reason the stalkwise statements below are phrased over a sheaf of commutative rings
on `Opens X` — the ringed-site form — and not over an `AlgebraicGeometry.RingedSpace`; the
implementation notes of `StacksFrontier.Topology.Sheaves.Modules.StalkTensor` explain why no
`RingedSpace`-keyed `CommRing` instance for the stalk can exist. Consequently the ringed-space
statement of the tag mentions no stalk ring at all: `Stacks.Cohomology.flat_iff_forall_isZero_tor`
is phrased entirely in `OXModule.Flat` and `Stacks.Cohomology.tor`, and the stalk rings appear
only inside its proof, where the site lemmas are instantiated at `X.sheaf` and arrive with their
instances already resolved.

The stalk-level derived category is `CategoryTheory.HasDerivedCategory.standard`, because
`CochainComplex.DerivedTensor.canonicalDerivedTensorProduct` bakes that model in; the model on
`X` stays a binder.

### Why the exactness of the stalk functor is seated by hand

Nothing about the stalk functor is reproved below; every local binding names evidence that
already exists — `AlgebraicGeometry.SheafOfModules.stalkFunctor_additive`,
`AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesFiniteLimits` and
`AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits`, Tag 01AH — and hands it to
the elaborator as an explicitly typed term, in the signature where the statement needs it and in
the proof otherwise. No name is introduced for any of them. Each of those three is stated for an
opaque sheaf of rings `𝒪`, so its discrimination-tree key carries `𝒪.obj`; but
`Stacks.SheafOfModules.Tensor.ringSheaf` is an `abbrev` whose body is a `Sheaf` literal, so in
`(ringSheaf R).obj` the projection iota-reduces to `R.obj ⋙ forget₂ CommRingCat RingCat` while
the key is being computed. The two keys therefore disagree — the source and target categories
are implicit *type* arguments of `CategoryTheory.Functor.Additive` and of
`PreservesFiniteLimits`, hence part of the key — and instance *lookup* never offers the general
instance even though applying it succeeds. This is what the `letI`s of
`StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.DerivedTensorStalk` do for the same
statements there.

The `CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective` seatings are a different
matter and are not a spelling problem: that instance is found, in about 1500 heartbeats. But
`Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct` asks for
`∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj M).Additive`, and that is a single
synthesis goal inside whose binder the same search is repeated for every candidate tried, so the
20000-heartbeat typeclass budget is spent before any of them is settled. Having it in the local
context, where synthesis finds it without search, keeps the goal inside the budget; the limit
itself is untouched.

## References

* [Stacks Project, Lemma 20.26.16 (Tag 08BQ)](https://stacks.math.columbia.edu/tag/08BQ)
* [Stacks Project, Tag 08BP](https://stacks.math.columbia.edu/tag/08BP)
* [Stacks Project, Tag 05ND](https://stacks.math.columbia.edu/tag/05ND)
* [Stacks Project, Tag 05NE](https://stacks.math.columbia.edu/tag/05NE)
* [Stacks Project, Lemma 17.5.2 (Tag 01AG)](https://stacks.math.columbia.edu/tag/01AG)
* [Stacks Project, Lemma 17.16.1 (Tag 01CB)](https://stacks.math.columbia.edu/tag/01CB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u d d'

namespace AlgebraicGeometry.SheafOfModules

/-! ### A single cohomology sheaf vanishes exactly when it vanishes on stalks -/

section SingleDegree

variable {X : TopCat.{u}}
  (O : CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  [HasDerivedCategory.{d} (_root_.SheafOfModules.{u} O)]
  [∀ x : X, HasDerivedCategory.{d'}
    (ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) O.obj x))]

/-- **One cohomology sheaf at a time, detected on stalks.** For an object `E` of `D(O)` the
sheaf `H^i(E)` is zero exactly when `H^i(E_x)` is zero for every point `x`.

This is the single-degree companion of
`AlgebraicGeometry.SheafOfModules.isZero_homology_iff_forall_stalk`, which asks for the
vanishing in every degree outside an interval and so cannot isolate one degree: the complement
of an interval of integers is never a single point. Both are the same two steps —
`isZero_iff_forall_isZero_stalkFunctor_obj` (Tag 01AG) and the commutation of an exact functor
with the homology of the derived category. -/
theorem isZero_homologyFunctor_obj_iff_forall_stalk
    (E : DerivedCategory (_root_.SheafOfModules.{u} O)) (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor (_root_.SheafOfModules.{u} O) i).obj E) ↔
      ∀ x : X, IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((stalkFunctor O x).mapDerivedCategory.obj E)) := by
  rw [isZero_iff_forall_isZero_stalkFunctor_obj]
  exact forall_congr' fun x =>
    (Iso.isZero_iff (((stalkFunctor O x).mapDerivedCategoryHomologyIso i).app E)).symm

end SingleDegree

/-! ### Flatness of a stalk does not depend on which stalk ring is used -/

/-- **The two stalk rings detect the same flat modules.** The stalk of a presheaf of modules
over `R ⋙ forget₂ CommRingCat RingCat` carries two scalar actions — one by the `RingCat`-valued
stalk of `R ⋙ forget₂`, one by the `CommRingCat`-valued stalk of `R` — on one and the same
abelian group. They correspond under `SemilinearStalk.commStalkRingEquiv`
(`AlgebraicGeometry.SheafOfModules.commStalk_smul_eq`), so flatness over one is flatness over
the other. -/
theorem flat_stalk_ringCat_iff_commRingCat {X : TopCat.{u}}
    (R : TopCat.Presheaf CommRingCat.{u} X)
    (M : _root_.PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})) (x : X) :
    Module.Flat (TopCat.Presheaf.stalk (C := RingCat.{u})
          (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}) x)
        (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x) ↔
      Module.Flat (TopCat.Presheaf.stalk (C := CommRingCat.{u}) R x)
        (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x) := by
  refine ⟨fun _ => ?_, fun _ => isFlat_of_ringEquiv (SemilinearStalk.commStalkRingEquiv R x)
    (fun a m => (commStalk_smul_eq R x M a m).symm)⟩
  refine isFlat_of_ringEquiv (SemilinearStalk.commStalkRingEquiv R x).symm (fun a m => ?_)
  rw [← commStalk_smul_eq R x M ((SemilinearStalk.commStalkRingEquiv R x).symm a) m,
    RingEquiv.apply_symm_apply]

end AlgebraicGeometry.SheafOfModules

namespace Stacks.SheafOfModules.DerivedTensorStalk

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}}
  (R : CategoryTheory.Sheaf.{u, u, u, u + 1} (Opens.grothendieckTopology X) CommRingCat.{u})

/-! ### The stalk of the derived tensor product of two modules -/

section Site

variable [HasDerivedCategory.{d} (Stacks.DerivedTensor.RingedSite.Modules R)]

/-- **The stalk of `ℱ ⊗^{L} 𝒢` for two modules.** For two `R`-modules placed in degree zero,
the derived stalk of their derived tensor product is the canonical derived tensor product of
their stalks over the stalk ring.

This is `derivedTensorStalkIso`, the derived form of Tag 01CB, with the first argument also a
module placed in degree zero, so that `derivedStalkSingleIso` replaces its derived stalk by the
stalk placed in degree zero. -/
def stalkDerivedTensorSingleIso (x : X) (F G : Stacks.DerivedTensor.RingedSite.Modules R) :
    letI : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
      inferInstance
    letI : (AlgebraicGeometry.SheafOfModules.stalkFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).Additive :=
      AlgebraicGeometry.SheafOfModules.stalkFunctor_additive
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
    letI : PreservesFiniteLimits (AlgebraicGeometry.SheafOfModules.stalkFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x) :=
      AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesFiniteLimits
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
    letI : PreservesColimits (AlgebraicGeometry.SheafOfModules.stalkFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x) :=
      AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
    (AlgebraicGeometry.SheafOfModules.stalkFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).mapDerivedCategory.obj
        (((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct R).tensor.obj
            ((DerivedCategory.singleFunctor
              (Stacks.DerivedTensor.RingedSite.Modules R) 0).obj F)).obj
          ((DerivedCategory.singleFunctor
            (Stacks.DerivedTensor.RingedSite.Modules R) 0).obj G)) ≅
      ((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor
            (TopCat.Presheaf.stalk (C := RingCat.{u})
              (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R).obj x)).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((AlgebraicGeometry.SheafOfModules.stalkFunctor
              (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).obj F))).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).obj G)) :=
  letI : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    inferInstance
  letI : (AlgebraicGeometry.SheafOfModules.stalkFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).Additive :=
    AlgebraicGeometry.SheafOfModules.stalkFunctor_additive
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
  letI : PreservesFiniteLimits (AlgebraicGeometry.SheafOfModules.stalkFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x) :=
    AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesFiniteLimits
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
  letI : PreservesColimits (AlgebraicGeometry.SheafOfModules.stalkFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x) :=
    AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
  (derivedTensorStalkIso R x
      ((DerivedCategory.singleFunctor
        (Stacks.DerivedTensor.RingedSite.Modules R) 0).obj F) G).symm ≪≫
    ((stalkDerivedTensor R x).mapIso (derivedStalkSingleIso R x F).symm).app _

/-- **The sheaf `Tor_p` of Tag 08BP vanishes exactly when every stalkwise module `Tor_p`
vanishes.** -/
theorem isZero_derivedTensorHomology_iff_forall_isZero_tor
    (p : ℕ) (F G : Stacks.DerivedTensor.RingedSite.Modules R) :
    letI : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
      inferInstance
    IsZero ((DerivedCategory.homologyFunctor
          (Stacks.DerivedTensor.RingedSite.Modules R) (-(p : ℤ))).obj
        (((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct R).tensor.obj
            ((DerivedCategory.singleFunctor
              (Stacks.DerivedTensor.RingedSite.Modules R) 0).obj F)).obj
          ((DerivedCategory.singleFunctor
            (Stacks.DerivedTensor.RingedSite.Modules R) 0).obj G))) ↔
      ∀ x : X, IsZero
        (((Tor (ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u})
                (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R).obj x)) p).obj
            ((AlgebraicGeometry.SheafOfModules.stalkFunctor
              (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).obj F)).obj
          ((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).obj G)) := by
  let : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    inferInstance
  let : ∀ y : X, (AlgebraicGeometry.SheafOfModules.stalkFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) y).Additive := fun y =>
    AlgebraicGeometry.SheafOfModules.stalkFunctor_additive
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) y
  let : ∀ y : X, PreservesFiniteLimits (AlgebraicGeometry.SheafOfModules.stalkFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) y) := fun y =>
    AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesFiniteLimits
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) y
  let : ∀ y : X, PreservesColimits (AlgebraicGeometry.SheafOfModules.stalkFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) y) := fun y =>
    AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) y
  rw [AlgebraicGeometry.SheafOfModules.isZero_homologyFunctor_obj_iff_forall_stalk]
  exact forall_congr' fun x =>
    (Iso.isZero_iff ((DerivedCategory.homologyFunctor _ (-(p : ℤ))).mapIso
      (stalkDerivedTensorSingleIso R x F G))).trans
    (Stacks.DerivedTensor.isZero_homology_iff_isZero_tor _ _ _ p)

end Site

end Stacks.SheafOfModules.DerivedTensorStalk

/-! ### Tag 08BQ on a ringed space -/

namespace Stacks.Cohomology

open _root_.StrictlyPerfect AlgebraicGeometry
open Stacks.SheafOfModules.DerivedTensorStalk

variable (X : AlgebraicGeometry.RingedSpace.{u, u}) [HasDerivedCategory.{d} (OXMod.{u, u} X)]

attribute [local instance] _root_.Stacks.Cohomology.TorAmplitude.hasDerivedCategoryModules

/-- **Tag 08BQ: Tor measures the deviation of flatness.** Let `(X, 𝒪_X)` be a ringed space and
`ℱ` an `𝒪_X`-module. The following are equivalent:

1. `ℱ` is a flat `𝒪_X`-module, and
2. `Tor_1^{𝒪_X}(ℱ, 𝒢) = 0` for every `𝒪_X`-module `𝒢`.

Clause (1) is `OXModule.Flat`, Definition Tag 05ND: the genuine sheaf tensor endofunctor
`- ⊗_{𝒪_X} ℱ` preserves monomorphisms, hence is exact. Clause (2) is the source's own `Tor_1`,
the sheaf `Stacks.Cohomology.tor X 1 ℱ 𝒢` of Tag 08BP, which is `H^{-1}(ℱ ⊗^{L}_{𝒪_X} 𝒢)` —
not a stalkwise substitute for it.

*Proof.* Tag 05NE (`OXModule.flat_iff_flat_stalk`) replaces clause (1) by flatness of every
stalk, and `AlgebraicGeometry.SheafOfModules.flat_stalk_ringCat_iff_commRingCat` reads that over
the stalk ring the derived tensor product is formed relative to. Over that ring
`OXModule.module_flat_iff_tor1` turns flatness of a stalk into the vanishing of the
module-theoretic `Tor_1` against every module over it, every such module being a stalk by
`AlgebraicGeometry.SheafOfModules.stalkFunctor_essSurj`; and
`isZero_derivedTensorHomology_iff_forall_isZero_tor` turns the vanishing of those stalkwise
`Tor_1` into the vanishing of the sheaf `Tor_1`, which is clause (2).

No intermediate statement of stalkwise flatness over the `RingCat`-valued stalk ring is written
down, and that is deliberate: writing `Module.Flat Λ M` for that ring forces the `Semiring Λ`
inside the `Module` instance to be the one derived from
`StacksDraft.StalkTensor.commRing_stalk`, while the `ModuleCat Λ` that `M` lives in carries the
one derived from `RingCat`'s own `Ring`. The two are definitionally equal but not syntactically,
so instance synthesis fails on the resulting `Module Λ M` goal. Going through
`OXModule.module_flat_iff_tor1`, whose `ModuleCat` is formed from its own `CommRing` binder,
keeps the instances internally consistent. -/
@[stacks 08BQ "(1) ⟺ (2) for a ringed space, with clause (2) stated in the source's own terms:
the vanishing of the sheaf Tor_1^{O_X}(F, G) = H^{-1}(F ⊗^L_{O_X} G) of Tag 08BP, for every
O_X-module G, and clause (1) sheaf-level flatness of Tag 05ND."]
theorem flat_iff_forall_isZero_tor (F : OXMod.{u, u} X) :
    OXModule.Flat F ↔ ∀ G : OXMod.{u, u} X, IsZero (tor X 1 F G) := by
  have key := fun x : X => @OXModule.module_flat_iff_tor1 _
    (StacksDraft.StalkTensor.commRing_stalk_ringSheaf X.sheaf x)
    ((AlgebraicGeometry.SheafOfModules.stalkFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf) x).obj F)
  refine (OXModule.flat_iff_flat_stalk F).trans ⟨fun hF G => ?_, fun hT x => ?_⟩
  · rw [tor_eq X 1 F G]
    refine (isZero_derivedTensorHomology_iff_forall_isZero_tor X.sheaf 1 F G).2 (fun x => ?_)
    exact (key x).1 ((AlgebraicGeometry.SheafOfModules.flat_stalk_ringCat_iff_commRingCat
      X.presheaf F.val x).2 (hF x)) _
  · refine (AlgebraicGeometry.SheafOfModules.flat_stalk_ringCat_iff_commRingCat
      X.presheaf F.val x).1 ((key x).2 (fun N => ?_))
    obtain ⟨G, ⟨e⟩⟩ := AlgebraicGeometry.SheafOfModules.stalkFunctor_essSurj
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf) x N
    exact ((isZero_derivedTensorHomology_iff_forall_isZero_tor X.sheaf 1 F G).1 (hT G) x).of_iso
      (Functor.mapIso _ e.symm)

end Stacks.Cohomology

end
