module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomSiteEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.ChaoticComparisonBaseChangeAcyclic
public import StacksFrontier.CategoryTheory.Sites.Modules.UniverseLiftBaseChange
public import StacksFrontier.CategoryTheory.Sites.Modules.UniverseLiftCohomology

/-!
# The base-change acyclicity hypothesis of Stacks 0GZS along an equivalence of ringed sites

Let `C` carry a topology `J` and a sheaf of rings `O` with commutative sections. Hypothesis (2)
of Stacks 0GZS is reduced in
`Stacks.ModulesOnACategory.ChaoticComparison.isLocallyKFlatAcyclic_of_baseChange` to a statement
about single modules, in two halves: for every object `U` and every `O(U)`-module `N`,

* the presheaf `N ⊗_{O(U)} O_U` on the localized site `(C/U, J)` is a sheaf
  (`Stacks.UniverseLift.BaseChangeIsSheaf`), and
* its module-valued cohomology over every object of `C/U` vanishes in positive degrees
  (`Stacks.UniverseLift.BaseChangeAcyclic`).

This file proves that both halves are invariant under an equivalence of ringed sites with a
change of ring universe: if `e : C ≌ D` is an equivalence for which `e` and `e⁻¹` are
continuous, `O'` is a sheaf of rings on `D`, and `T : RingTransport e O O'` is a natural family
of ring isomorphisms `O'(Y) ≃+* O(e⁻¹ Y)`, then the two halves for `(C, O)` give the two halves
for `(D, O')`. The intended use is the passage from a large site `C` to its small model
`AsSmall C`, with the ring sheaf lifted to the universe of the modules.

## Main definitions

* `Stacks.UniverseLift.BaseChangeIsSheaf`: the sheaf half of the hypothesis.
* `Stacks.UniverseLift.BaseChangeAcyclic`: the acyclicity half of the hypothesis.

## Main results

* `Stacks.UniverseLift.RingTransport.baseChangeIsSheaf`: the sheaf half is transported along a
  ring transport.
* `Stacks.UniverseLift.RingTransport.baseChangeAcyclic`: the acyclicity half is transported
  along a ring transport.
* `Stacks.UniverseLift.isLocallyKFlatAcyclic_of_baseChangeAcyclic`: the two halves give
  hypothesis (2) of Stacks 0GZS.

## Implementation notes

At an object `U'` of `D` the comparison runs through the equivalence of slices
`C/e⁻¹(U') ≌ D/U'` and the ring transport it carries (`RingTransport.over`). The base change
`N' ⊗ O'_{U'}` is the transport of a base change `N ⊗ O_{e⁻¹ U'}`, because both are left adjoint
to evaluation at the terminal object (`RingTransport.baseChangeTransportIso`); the terminal
object of `C/e⁻¹(U')` reached from `D/U'` is identified with `id_{e⁻¹ U'}` by the uniqueness of
terminal objects, so no compatibility of `e⁻¹` with identities is needed. The sheaf half then
follows from the transport of sheaves along the slice equivalence, and the acyclicity half from
the transport of module cohomology (`RingTransport.isZero_rightDerived_evaluation_iff`).

The module universe of each side is `max t r`, with `r` the universe of its rings, as in the
binders of `isLocallyKFlatAcyclic_of_baseChange` (there `t = max u v w`). The two sides of the
transport are taken at `max t r₂` over `C` and at `max t r₁` over `D`, which is one and the same
module universe `max t r₁ r₂`.

## References

* [Stacks Project, Tag 0GZS](https://stacks.math.columbia.edu/tag/0GZS)
* [Stacks Project, Tag 0H0J](https://stacks.math.columbia.edu/tag/0H0J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.TerminalBaseChange
open Stacks.Sites.OverModules (overRingPresheaf)
open Stacks.ModulesOnACategory.ChaoticComparison (overRingSheaf)
open Stacks.ModulesOnACategory.MorphismsOverAnObject (comm_overRingPresheaf)
open Stacks.ModulesOnACategory.TerminalMorphismOfSites (commSections_of_comm)

-- The global instance `Stacks.Cohomology.SiteModules.moduleSheavesAbelian` is stated at a module
-- universe which is a `max` of four universe variables; at the module universe `max t r` used
-- here, instance search against it leaves a stuck universe constraint. The instance that
-- applies is Mathlib's `SheafOfModules.instAbelian`, to which it unfolds.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe t u v r u₁ v₁ u₂ v₂ r₁ r₂

namespace Stacks.UniverseLift

section Hypotheses

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r})
  (hO : ∀ (V : Cᵒᵖ) (x y : R.obj.obj V), x * y = y * x)

/-- **The sheaf half of the base-change hypothesis.** For every object `U` and every
`O(U)`-module `N`, the base change `N ⊗_{O(U)} O_U` along the terminal object `id_U` of `C/U`
is a sheaf for the localized topology `J.over U`. This is the hypothesis `hsheaf` of
`Stacks.ModulesOnACategory.ChaoticComparison.isLocallyKFlatAcyclic_of_baseChange`, at the module
universe `max t r`. -/
def BaseChangeIsSheaf : Prop :=
  ∀ (U : C) (N : ModuleCat.{max t r} ((overRingPresheaf R.obj U).obj (op (Over.mk (𝟙 U))))),
    letI := commSections_of_comm (overRingPresheaf R.obj U) (comm_overRingPresheaf R.obj U hO)
    Presheaf.IsSheaf (J.over U) ((baseChangePresheaf.{t} (overRingPresheaf R.obj U)
      (Over.mkIdTerminal (X := U))).obj N).presheaf

variable [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max t r}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max t r}]
  [∀ U : C, HasInjectiveResolutions (SheafOfModules.{max t r} (overRingSheaf R U))]

/-- **The acyclicity half of the base-change hypothesis.** For every object `U`, every
`O(U)`-module `N`, every object `V` of `C/U` and every `p > 0`, the `p`-th module-valued
cohomology over `V` of the sheaf `N ⊗_{O(U)} O_U` vanishes. This is the hypothesis `hacyc` of
`Stacks.ModulesOnACategory.ChaoticComparison.isLocallyKFlatAcyclic_of_baseChange`, at the module
universe `max t r`. -/
def BaseChangeAcyclic (hsheaf : BaseChangeIsSheaf.{t} R hO) : Prop :=
  ∀ (U : C) (N : ModuleCat.{max t r} ((overRingPresheaf R.obj U).obj (op (Over.mk (𝟙 U)))))
    (V : Over U) (p : ℕ), 0 < p →
    letI := commSections_of_comm (overRingPresheaf R.obj U) (comm_overRingPresheaf R.obj U hO)
    IsZero (((SheafOfModules.evaluation (overRingSheaf R U) (op V)).rightDerived p).obj
      ⟨(baseChangePresheaf.{t} (overRingPresheaf R.obj U) (Over.mkIdTerminal (X := U))).obj N,
        hsheaf U N⟩)

omit [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max t r}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max t r}]
  [∀ U : C, HasInjectiveResolutions (SheafOfModules.{max t r} (overRingSheaf R U))] in
/-- The sheaf half of the hypothesis depends on the parameter `t` only through the module
universe `max t r`. -/
theorem baseChangeIsSheaf_max_iff : BaseChangeIsSheaf.{max t r} R hO ↔ BaseChangeIsSheaf.{t} R hO :=
  Iff.rfl

/-- The acyclicity half of the hypothesis depends on the parameter `t` only through the module
universe `max t r`. -/
theorem baseChangeAcyclic_max_iff (hsheaf : BaseChangeIsSheaf.{t} R hO) :
    BaseChangeAcyclic.{max t r} R hO hsheaf ↔ BaseChangeAcyclic.{t} R hO hsheaf :=
  Iff.rfl

end Hypotheses

namespace RingTransport

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {e : C ≌ D}
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [e.functor.IsContinuous J K] [e.inverse.IsContinuous K J]
  {R : Sheaf J RingCat.{r₁}} {R' : Sheaf K RingCat.{r₂}} (T : RingTransport e R.obj R'.obj)
  (hO : ∀ (V : Cᵒᵖ) (x y : R.obj.obj V), x * y = y * x)
  (hO' : ∀ (V : Dᵒᵖ) (x y : R'.obj.obj V), x * y = y * x)

/-- The image of the terminal object `id_{U'}` of `D/U'` under the inverse of the equivalence
of slices `C/e⁻¹(U') ≌ D/U'` is identified with the terminal object `id_{e⁻¹ U'}`, by the
uniqueness of terminal objects. -/
noncomputable def overTerminalIso (U' : D) :
    (Over.postEquiv U' e.symm).symm.inverse.obj (Over.mk (𝟙 U')) ≅
      Over.mk (𝟙 (e.inverse.obj U')) :=
  IsTerminal.uniqueUpToIso
    (Over.mkIdTerminal.isTerminalObj (Over.postEquiv U' e.symm).symm.inverse _)
    Over.mkIdTerminal

/-- At an object `U'` of `D`, the base change `N' ⊗ O'_{U'}` is the transport, along the
equivalence of slices `C/e⁻¹(U') ≌ D/U'`, of the base change `N ⊗ O_{e⁻¹ U'}` of the
`O(e⁻¹ U')`-module `N` underlying `N'`. -/
noncomputable def overBaseChangeIso (U' : D)
    (N' : ModuleCat.{max t r₁ r₂} ((overRingPresheaf R'.obj U').obj (op (Over.mk (𝟙 U'))))) :
    letI := commSections_of_comm (overRingPresheaf R.obj (e.inverse.obj U'))
      (comm_overRingPresheaf R.obj (e.inverse.obj U') hO)
    letI := commSections_of_comm (overRingPresheaf R'.obj U') (comm_overRingPresheaf R'.obj U' hO')
    (T.over U').functor.obj ((baseChangePresheaf.{max t r₂}
        (overRingPresheaf R.obj (e.inverse.obj U')) (Over.mkIdTerminal (X := e.inverse.obj U'))).obj
          ((ModuleCat.restrictScalars
            ((T.over U').terminalRingEquiv (overTerminalIso (e := e) U')).symm.toRingHom).obj N')) ≅
      (baseChangePresheaf.{max t r₁} (overRingPresheaf R'.obj U')
        (Over.mkIdTerminal (X := U'))).obj N' :=
  letI := commSections_of_comm (overRingPresheaf R.obj (e.inverse.obj U'))
    (comm_overRingPresheaf R.obj (e.inverse.obj U') hO)
  letI := commSections_of_comm (overRingPresheaf R'.obj U') (comm_overRingPresheaf R'.obj U' hO')
  ((T.over U').baseChangeTransportIso (overTerminalIso (e := e) U') Over.mkIdTerminal
    Over.mkIdTerminal).app N'

omit [e.functor.IsContinuous J K] in
include T in
/-- **The sheaf half of the base-change hypothesis is transported along a ring transport.** -/
theorem baseChangeIsSheaf (hsheaf : BaseChangeIsSheaf.{max t r₂} R hO) :
    BaseChangeIsSheaf.{max t r₁} R' hO' := by
  intro U' N'
  let : (Over.post (X := U') e.inverse).IsContinuous (K.over U') (J.over (e.inverse.obj U')) :=
    Functor.isContinuous_overPost K J e.inverse U'
  let : (Over.postEquiv U' e.symm).symm.inverse.IsContinuous (K.over U')
      (J.over (e.inverse.obj U')) := inferInstanceAs
    ((Over.post (X := U') e.inverse).IsContinuous (K.over U') (J.over (e.inverse.obj U')))
  refine (Presheaf.isSheaf_of_iso_iff ((PresheafOfModules.toPresheaf _).mapIso
    (T.overBaseChangeIso hO hO' U' N'))).1 ?_
  exact (T.over U').isSheaf_functor_obj (R := overRingSheaf R (e.inverse.obj U'))
    (R' := overRingSheaf R' U') _ (hsheaf _ _)

variable [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max t r₁ r₂}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max t r₁ r₂}]
  [∀ U : C, HasInjectiveResolutions (SheafOfModules.{max t r₁ r₂} (overRingSheaf R U))]
  [∀ U' : D, HasSheafify (K.over U') AddCommGrpCat.{max t r₁ r₂}]
  [∀ U' : D, (K.over U').WEqualsLocallyBijective AddCommGrpCat.{max t r₁ r₂}]
  [∀ U' : D, HasInjectiveResolutions (SheafOfModules.{max t r₁ r₂} (overRingSheaf R' U'))]

include T in
/-- **The acyclicity half of the base-change hypothesis is transported along a ring
transport.** -/
theorem baseChangeAcyclic (hsheaf : BaseChangeIsSheaf.{max t r₂} R hO)
    (hacyc : BaseChangeAcyclic.{max t r₂} R hO hsheaf) :
    BaseChangeAcyclic.{max t r₁} R' hO' (T.baseChangeIsSheaf hO hO' hsheaf) := by
  intro U' N' V' p hp
  let : e.symm.functor.IsContinuous K J := inferInstanceAs (e.inverse.IsContinuous K J)
  let : e.symm.inverse.IsContinuous J K := inferInstanceAs (e.functor.IsContinuous J K)
  let : (Over.postEquiv U' e.symm).symm.inverse.IsContinuous (K.over U')
      (J.over (e.inverse.obj U')) :=
    Over.postEquivFunctorIsContinuous (J := K) (K := J) e.symm U'
  let : (Over.postEquiv U' e.symm).symm.functor.IsContinuous (J.over (e.inverse.obj U'))
      (K.over U') :=
    Over.postEquivInverseIsContinuous (J := K) (K := J) e.symm U'
  let := commSections_of_comm (overRingPresheaf R.obj (e.inverse.obj U'))
    (comm_overRingPresheaf R.obj (e.inverse.obj U') hO)
  let := commSections_of_comm (overRingPresheaf R'.obj U') (comm_overRingPresheaf R'.obj U' hO')
  let N := (ModuleCat.restrictScalars
    ((T.over U').terminalRingEquiv (overTerminalIso (e := e) U')).symm.toRingHom).obj N'
  let F : SheafOfModules.{max t r₁ r₂} (overRingSheaf R (e.inverse.obj U')) :=
    ⟨(baseChangePresheaf.{max t r₂} (overRingPresheaf R.obj (e.inverse.obj U'))
      (Over.mkIdTerminal (X := e.inverse.obj U'))).obj N, hsheaf _ N⟩
  let i := (SheafOfModules.fullyFaithfulForget (overRingSheaf R' U')).preimageIso
    (X := (T.over U').sheafFunctor (R := overRingSheaf R (e.inverse.obj U'))
      (R' := overRingSheaf R' U') |>.obj F)
    (Y := ⟨(baseChangePresheaf.{max t r₁} (overRingPresheaf R'.obj U')
      (Over.mkIdTerminal (X := U'))).obj N', T.baseChangeIsSheaf hO hO' hsheaf U' N'⟩)
    (T.overBaseChangeIso hO hO' U' N')
  refine IsZero.of_iso ?_ (((SheafOfModules.evaluation (overRingSheaf R' U')
    (op V')).rightDerived p).mapIso i).symm
  exact ((T.over U').isZero_rightDerived_evaluation_iff (R := overRingSheaf R (e.inverse.obj U'))
    (R' := overRingSheaf R' U') F (op V') p).2 (hacyc _ N _ p hp)

end RingTransport

section KFlatAcyclic

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r})
  [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{max u v r t}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{max u v r t}]
  [∀ U : C, HasInjectiveResolutions (SheafOfModules.{max u v r t} (overRingSheaf R U))]
  (hO : ∀ (V : Cᵒᵖ) (x y : R.obj.obj V), x * y = y * x)

/-- **Hypothesis (2) of Stacks 0GZS from the two halves of the base-change hypothesis**, in the
form `Stacks.ModulesOnACategory.ChaoticComparison.isLocallyKFlatAcyclic_of_baseChange` proves
it. -/
theorem isLocallyKFlatAcyclic_of_baseChangeAcyclic
    (hsheaf : BaseChangeIsSheaf.{max u v t} R hO)
    (hacyc : BaseChangeAcyclic.{max u v t} R hO hsheaf) :
    Stacks.ModulesOnACategory.ChaoticComparison.IsLocallyKFlatAcyclic.{t} R hO :=
  Stacks.ModulesOnACategory.ChaoticComparison.isLocallyKFlatAcyclic_of_baseChange R hO hsheaf hacyc

end KFlatAcyclic

end Stacks.UniverseLift
