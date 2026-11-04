module

public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.LocalCohomologyFiniteness
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.NaturalComplementComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The connecting map of the cohomology sequence of a zero locus, as a natural transformation

Let `A` be a ring, let `I ⊆ A` be an ideal, let `X = Spec A`, let `Z = V(I)` and let `U = X ∖ Z`.
The long exact cohomology sequence of `Z` has a connecting morphism
`H^n(U, -) ⟶ H^{n+1}_Z(X, -)`, and that morphism is a **natural transformation** of functors on
sheaves of modules on `X`: it is `CategoryTheory.rightDerivedDelta` for the short complex of
functors `Γ_Z(X, -) ⟶ Γ(X, -) ⟶ Γ(U, -)`, which is short exact on injective module sheaves.

`Stacks.LocalCohomologySequence.exact_cohomologyWithSupport_sequence` states the exactness of
that sequence with the connecting morphism existentially quantified, and
`Stacks.LocalCohomologySequence.nonempty_iso_complementCohomology` records only that the two
terms are isomorphic in degrees `≥ 1`. Neither can be used to transport a statement about an
inverse limit of a tower of modules from one side to the other, because such a transport needs
the comparison to be compatible with the transition maps of the tower, that is, to be natural in
the sheaf. This file supplies the named transformation and the resulting natural isomorphism.

## Main definitions

* `Stacks.LocalCohomologySequence.complementRightDerivedDelta` — the connecting natural
  transformation `H^n(U, -) ⟶ H^{n+1}_Z(X, -)`.
* `Stacks.LocalCohomologySequence.complementDeltaBaseNatIso` — **the comparison of Stacks 0DWR
  above degree zero, as a natural isomorphism of functors of the module.**

## Main results

* `Stacks.LocalCohomologySequence.isIso_complementDelta_app_tildeSheaf` — the connecting
  morphism is an isomorphism at `M̃` in every degree `p ≥ 1`: the two neighbouring terms
  `H^p(X, M̃)` and `H^{p+1}(X, M̃)` of the long exact sequence vanish by Serre vanishing, so it
  is both a monomorphism and an epimorphism.

## Implementation notes

The three functors of the sequence are the ones of
`StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.LocalCohomologySequence`, so the
transformation defined here is the connecting morphism of *that* sequence: the `delta` whose
existence `exact_cohomologyWithSupport_sequence` asserts is
`CategoryTheory.rightDerivedDelta` for the same four arguments, because
`Stacks.Cohomology.SectionsWithSupport.longExact_rightDerived_sectionsWithSupport` produces it by
`CategoryTheory.longExact_rightDerived_of_shortExact_on_injectives`, whose witness is exactly
that transformation.

No hypothesis on `A` is needed: Serre vanishing for `M̃` on the affine `Spec A` is
`Stacks.LocalCohomologySequence.isZero_ambientCohomology_tilde`, which is unconditional, and the
short exactness on injectives is `Tag 01EA`, also unconditional. In particular the Noetherian
hypothesis of the comparison with algebraic local cohomology is not needed here; it enters only
when `H^{n+1}_Z(X, M̃)` is replaced by `H^{n+1}_I(M)`.

The natural isomorphism is obtained from the transformation by
`CategoryTheory.NatIso.isIso_of_isIso_app`, so its components are the components of
`Stacks.LocalCohomologySequence.complementRightDerivedDelta` and nothing is chosen.

## References

* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 0G71](https://stacks.math.columbia.edu/tag/0G71)
* [Stacks Project, Tag 01EA](https://stacks.math.columbia.edu/tag/01EA)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.Cohomology.SectionsWithSupport
open Stacks.LocalCohomologyTilde
open RingedSpaceModuleAdjunction

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.LocalCohomologySequence

variable {A : CommRingCat.{u}}

/-! ### The connecting transformation -/

/-- The inclusion `Γ_{V(I)}(X, -) ⟶ Γ(X, -)` forgetting the support condition, named so that
the elaborator does not have to re-unfold `sectionsWithSupport` at every use. -/
def supportKernelHom (I : Ideal A) :
    sectionsWithSupport (Spec A).toRingedSpace (zeroLocusSubset I)
        (isClosed_zeroLocusSubset I) ⟶
      SheafOfModules.evaluation (structureSheafRing (Spec A).toRingedSpace) (op ⊤) :=
  kernel.ι (restrictionToComplement (Spec A).toRingedSpace (zeroLocusSubset I)
    (isClosed_zeroLocusSubset I))

/-- Restriction to the open complement of `V(I)`, named for the same reason. -/
def complementRestrictionHom (I : Ideal A) :
    SheafOfModules.evaluation (structureSheafRing (Spec A).toRingedSpace) (op ⊤) ⟶
      sectionsOnComplement (Spec A).toRingedSpace (zeroLocusSubset I)
        (isClosed_zeroLocusSubset I) :=
  restrictionToComplement (Spec A).toRingedSpace (zeroLocusSubset I)
    (isClosed_zeroLocusSubset I)

/-- The composite `Γ_{V(I)}(X, -) ⟶ Γ(X, -) ⟶ Γ(U, -)` of the two transformations of the
cohomology sequence of `V(I)` vanishes. -/
theorem supportKernelHom_comp_complementRestrictionHom (I : Ideal A) :
    supportKernelHom I ≫ complementRestrictionHom I = 0 :=
  kernel.condition _

/-- The short complex `Γ_{V(I)}(X, -) ⟶ Γ(X, -) ⟶ Γ(U, -)` is short exact at every injective
module sheaf: it is left exact by construction, sections with support being the kernel of
restriction to the complement, and restriction is surjective on an injective module sheaf by
Tag 01EA. -/
theorem shortExact_appShortComplex_zeroLocus (I : Ideal A)
    (F : ModuleSheaves (Spec A).toRingedSpace) (hF : CategoryTheory.Injective F) :
    (CategoryTheory.NatTrans.appShortComplex (supportKernelHom I) (complementRestrictionHom I)
      (supportKernelHom_comp_complementRestrictionHom I) F).ShortExact :=
  shortExact_appShortComplex_of_injective (Spec A).toRingedSpace (zeroLocusSubset I)
    (isClosed_zeroLocusSubset I) F hF

/-- **The connecting morphism of the cohomology sequence of `V(I)`, as a natural
transformation.** In degree `n` it is a transformation `H^n(U, -) ⟶ H^{n+1}_{V(I)}(X, -)` of
functors on sheaves of modules on `Spec A`.

This is `CategoryTheory.rightDerivedDelta` for the short complex
`Γ_{V(I)}(X, -) ⟶ Γ(X, -) ⟶ Γ(U, -)`, hence the very morphism whose existence
`Stacks.LocalCohomologySequence.exact_cohomologyWithSupport_sequence` asserts. -/
def complementRightDerivedDelta (I : Ideal A) (n : ℕ) :
    complementCohomology I n ⟶ cohomologyWithSupport I (n + 1) :=
  CategoryTheory.rightDerivedDelta (supportKernelHom I) (complementRestrictionHom I)
    (supportKernelHom_comp_complementRestrictionHom I)
    (fun F hF => shortExact_appShortComplex_zeroLocus I F hF) n

/-- The six-term window of the long exact sequence of `V(I)` around the connecting morphism,
with that morphism named. -/
theorem exact_complementDelta_window (I : Ideal A)
    (F : ModuleSheaves (Spec A).toRingedSpace) (n : ℕ) :
    (CategoryTheory.ComposableArrows.mk₅
      ((CategoryTheory.NatTrans.rightDerived (supportKernelHom I) n).app F)
      ((CategoryTheory.NatTrans.rightDerived (complementRestrictionHom I) n).app F)
      ((complementRightDerivedDelta I n).app F)
      ((CategoryTheory.NatTrans.rightDerived (supportKernelHom I) (n + 1)).app F)
      ((CategoryTheory.NatTrans.rightDerived (complementRestrictionHom I) (n + 1)).app F)).Exact :=
  CategoryTheory.exact_rightDerived_composableArrows₅ (supportKernelHom I)
    (complementRestrictionHom I) (supportKernelHom_comp_complementRestrictionHom I)
    (fun G hG => shortExact_appShortComplex_zeroLocus I G hG)
    (CategoryTheory.injectiveResolution F) n

/-- **The connecting morphism is an isomorphism at `M̃` in every degree `p ≥ 1`.** The terms of
the long exact sequence on either side of it are `H^p(X, M̃)` and `H^{p+1}(X, M̃)`, which vanish
by Serre vanishing on the affine `Spec A`; so the morphism is a monomorphism and an
epimorphism, and modules over a ring form a balanced category. -/
@[sga "2 II Corollary4" "more general"]
theorem isIso_complementDelta_app_tildeSheaf (I : Ideal A) (M : ModuleCat.{u} A) (p : ℕ)
    (hp : 0 < p) :
    IsIso ((complementRightDerivedDelta I p).app (tildeSheaf M)) := by
  have hmono : Mono ((complementRightDerivedDelta I p).app (tildeSheaf M)) :=
    ((exact_complementDelta_window I (tildeSheaf M) p).exact' 1 2 3).mono_g
      ((isZero_ambientCohomology_tilde M p hp).eq_zero_of_src _)
  have hepi : Epi ((complementRightDerivedDelta I p).app (tildeSheaf M)) :=
    ((exact_complementDelta_window I (tildeSheaf M) p).exact' 2 3 4).epi_f
      ((isZero_ambientCohomology_tilde M (p + 1) p.succ_pos).eq_zero_of_tgt _)
  exact isIso_of_mono_of_epi _

/-! ### The two sides as functors of the module, and the natural isomorphism

The two sides are the functors `M ↦ H^p(U, M̃)` and `M ↦ H^q_Z(X, M̃)` on `A`-modules, read over
`A`: `Stacks.LocalCohomologySequence.complementCohomologyBaseFunctor` and
`Stacks.LocalCohomologySequence.cohomologyWithSupportBaseFunctor` of
`NaturalComplementComparison.lean`.
-/

/-- The connecting morphism at the sheaves `M̃`, read over `A`, as a natural transformation of
functors of the `A`-module `M`. -/
def complementDeltaBase (I : Ideal A) (p : ℕ) :
    complementCohomologyBaseFunctor I p ⟶ cohomologyWithSupportBaseFunctor I (p + 1) :=
  Functor.whiskerRight
    (Functor.whiskerLeft (tildeSheafFunctor A) (complementRightDerivedDelta I p)) (globalToBase A)

/-- The component of `complementDeltaBase I p` at `M` is the connecting morphism at the sheaf
`M̃`, read over `A`. -/
theorem complementDeltaBase_app (I : Ideal A) (p : ℕ) (M : ModuleCat.{u} A) :
    (complementDeltaBase I p).app M =
      (globalToBase A).map ((complementRightDerivedDelta I p).app (tildeSheaf M)) :=
  rfl

/-- Every component of the connecting transformation, read over `A`, is invertible in degrees
`p ≥ 1`. -/
theorem isIso_complementDeltaBase_app (I : Ideal A) (p : ℕ) (hp : 0 < p)
    (M : ModuleCat.{u} A) : IsIso ((complementDeltaBase I p).app M) := by
  have := isIso_complementDelta_app_tildeSheaf I M p hp
  rw [complementDeltaBase_app]
  exact Functor.map_isIso (globalToBase A) _

/-- **The comparison of Stacks 0DWR above degree zero, as a natural isomorphism of functors of
the module.** For `p ≥ 1` the functors `M ↦ H^p(U, M̃)` and `M ↦ H^{p+1}_{V(I)}(X, M̃)` on
`A`-modules are isomorphic through the connecting morphism of the long exact cohomology sequence
of `V(I)`.

Naturality is not an extra property proved here: the comparison *is* a natural transformation,
and what the degree hypothesis buys is that each of its components is invertible. -/
def complementDeltaBaseNatIso (I : Ideal A) (p : ℕ) (hp : 0 < p) :
    complementCohomologyBaseFunctor I p ≅ cohomologyWithSupportBaseFunctor I (p + 1) :=
  haveI : ∀ M : ModuleCat.{u} A, IsIso ((complementDeltaBase I p).app M) := fun M =>
    isIso_complementDeltaBase_app I p hp M
  haveI : IsIso (complementDeltaBase I p) := NatIso.isIso_of_isIso_app _
  asIso (complementDeltaBase I p)

/-- The forward morphism of `complementDeltaBaseNatIso I p hp` is `complementDeltaBase I p`. -/
theorem complementDeltaBaseNatIso_hom (I : Ideal A) (p : ℕ) (hp : 0 < p) :
    (complementDeltaBaseNatIso I p hp).hom = complementDeltaBase I p :=
  rfl

/-! ### The middle term of the sequence in degree zero -/

/-- `M ↦ H^n(X, M̃)` as a functor from `A`-modules to `A`-modules, the middle term of the
cohomology sequence of `V(I)`. -/
def ambientCohomologyBaseFunctor (A : CommRingCat.{u}) (n : ℕ) :
    ModuleCat.{u} A ⥤ ModuleCat.{u} A :=
  tildeSheafFunctor A ⋙ ambientCohomology A n ⋙ globalToBase A

/-- The value of `ambientCohomologyBaseFunctor A n` at `M` is `H^n(X, M̃)` read over `A`. -/
theorem ambientCohomologyBaseFunctor_obj (A : CommRingCat.{u}) (n : ℕ) (M : ModuleCat.{u} A) :
    (ambientCohomologyBaseFunctor A n).obj M =
      (globalToBase A).obj ((ambientCohomology A n).obj (tildeSheaf M)) :=
  rfl

/-- **The degree-zero middle term of the cohomology sequence is the module itself, naturally.**
The degree-zero right derived functor of global sections is global sections, by
`Stacks.LocalCohomologySequence.ambientCohomologyZeroIso`, and `M ≅ Γ(Spec A, M̃)` is the unit of
the associated-sheaf adjunction, by `Stacks.LocalCohomologyTilde.globalSectionsTildeIso`; both
are isomorphisms of functors. -/
def ambientCohomologyBaseZeroNatIso (A : CommRingCat.{u}) :
    ambientCohomologyBaseFunctor A 0 ≅ 𝟭 (ModuleCat.{u} A) :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (tildeSheafFunctor A) (ambientCohomologyZeroIso (A := A)))
      (globalToBase A) ≪≫
    (globalSectionsTildeIso A).symm

/-- The component at `M` of `ambientCohomologyBaseZeroNatIso A` is the isomorphism
`ambientCohomologyZeroBaseIso M`. -/
theorem ambientCohomologyBaseZeroNatIso_hom_app (A : CommRingCat.{u}) (M : ModuleCat.{u} A) :
    (ambientCohomologyBaseZeroNatIso A).hom.app M = (ambientCohomologyZeroBaseIso M).hom :=
  rfl

end Stacks.LocalCohomologySequence

end
