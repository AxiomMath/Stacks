module

public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.FilteredColimit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.AbelianHigherDirectImageSheafification
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.AcyclicityAndBoundedBelow
import StacksCore.Tactic.StacksAttribute

/-!
# Higher direct images of the underlying abelian sheaf of an injective module sheaf

Let `u : 𝒟 ⥤ 𝒞` be a continuous functor between small sites, inducing the direct image
`f_* : Ab(𝒞) ⥤ Ab(𝒟)` of abelian sheaves, and let `R` be a sheaf of rings on `𝒞`. This file proves
that for an injective sheaf of `R`-modules `I` the higher direct images of the *underlying abelian
sheaf* `I_ab` vanish:

`R^(q+1) f_* I_ab = 0` for every `q ≥ 0`.

Injectivity of `I` in `Mod(R)` does **not** make `I_ab` an injective abelian sheaf, so this is not
`CategoryTheory.Functor.isZero_rightDerived_obj_injective_succ`. It is the higher-direct-image case
of the acyclicity that drives [Stacks, Tag 03FD], the agreement of cohomology computed in `Mod(R)`
and in `Ab(𝒞)`: that acyclicity says `H^(q+1)(V, I_ab) = 0` for every object `V` of `𝒞`, and the
higher direct image is the sheafification of the presheaf `V ↦ H^q(u(V), -)` by
[Stacks, Tag 072W], so the vanishing propagates.

## Main results

* `Stacks.Cohomology.ModuleInjectiveHigherDirectImage.isZero_rightDerived_sections_toSheaf_succ`:
  `H^(q+1)(V, I_ab) = 0`, the acyclicity of [Stacks, Tag 03FD] read as a vanishing of Mathlib's
  `ℕ`-indexed right derived functors of sections over `V`.
* `Stacks.Cohomology.ModuleInjectiveHigherDirectImage.isZero_rightDerived_cohomologyPresheaf_succ`:
  the whole presheaf `V ↦ H^(q+1)(u(V), I_ab)` on `𝒟` is zero.
* `Stacks.Cohomology.ModuleInjectiveHigherDirectImage.isZero_higherDirectImage_toSheaf_succ`:
  **`R^(q+1) f_* I_ab = 0`**, the higher-direct-image case of [Stacks, Tag 03FD].

## Implementation notes

**The three steps.** The acyclicity of `I_ab` for sections over `V` is
`Stacks.Cohomology.ModuleComparison.rightAcyclic_toSheaf_obj_of_injective`, which is stated in the
derived-category sense of [Stacks, Tag 0157]; [Stacks, Tag 015C]
(`CategoryTheory.Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus`) converts it into
vanishing of the `ℤ`-indexed `Functor.rightDerivedPlus` in positive degrees, and
`Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff` converts that into vanishing of Mathlib's
`ℕ`-indexed `Functor.rightDerived`. That is the first step. The second replaces `V` by `u(V)` and
reads the result as a value of the cohomology presheaf, using
`Stacks.Cohomology.SheafifiedHigherDirectImage.pushforwardCohomologyPresheafEvaluationIso`; a
presheaf all of whose values are zero is zero. The third sheafifies, using
`Stacks.Cohomology.SheafifiedHigherDirectImage.rightDerivedPushforwardIso`, which is
[Stacks, Tag 072W] for abelian sheaves.

**Smallness of the sites.** The acyclicity used in the first step is proved for a site whose
objects form a small type, so the statements here carry `[SmallCategory 𝒞]` and
`[SmallCategory 𝒟]`. For a site whose objects form a type above the universe of its morphisms —
the small étale site of a scheme, say — the same three steps give
`Stacks.Cohomology.InjectiveModuleSheafAcyclicity.isZero_higherDirectImage_toSheaf_succ`
from the acyclicity of `Stacks.Cohomology.ObjectSections.ext_eq_zero_of_isTorsionFree`, which has
the sheafification and `Ext` hypotheses as instance arguments instead.

**Spelling of the sections functor.** The cohomology presheaf evaluated at `V` is *definitionally*
the sections functor over `u(V)` — this is
`Stacks.Cohomology.SheafifiedHigherDirectImage.pushforwardCohomologyPresheaf_comp_evaluation`, an
equality of functors — but only the composite spelling has an `Additive` instance available by
synthesis, so the second step is stated for the composite and discharged by the first step
unchanged.

**The constant ring sheaf.** The source's hypothesis in [Stacks, Tag 0F03] is that `I` be an
injective sheaf of `ℤ/nℤ`-modules, which is this statement for `R` the constant sheaf of rings
`ℤ/nℤ`; the general sheaf of rings is [Stacks, Tag 03FD]'s own generality and is what is proved
here.

**Instance priorities.** `HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso` is
given a high local priority, as for
`Stacks.Cohomology.ModuleComparison.rightAcyclic_toSheaf_obj_of_injective`: without
it the instance argument of `CategoryTheory.Functor.rightAcyclic`, which asks that the right
derived functor be everywhere defined, exhausts the typeclass budget before it is found.

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
* [Stacks Project, Tag 0157](https://stacks.math.columbia.edu/tag/0157)
* [Stacks Project, Tag 015C](https://stacks.math.columbia.edu/tag/015C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.SheafifiedHigherDirectImage

namespace Stacks.Cohomology.ModuleInjectiveHigherDirectImage

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
  (J : GrothendieckTopology D) (K : GrothendieckTopology C)
  (u : D ⥤ C) [u.IsContinuous J K]
  (R : Sheaf K RingCat.{u}) (I : SheafOfModules.{u} R) [Injective I]

/-- **The acyclicity of [Stacks, Tag 03FD], in the `ℤ`-indexed derived functors.** The underlying
abelian sheaf of an injective sheaf of `R`-modules has vanishing higher cohomology over every
object of the site. The input is the derived-category acyclicity of [Stacks, Tag 0157] and the
conversion is [Stacks, Tag 015C]. -/
theorem isZero_rightDerivedPlus_sections_toSheaf (V : C) (i : ℤ) (hi : 0 < i) :
    IsZero ((((sheafSections K AddCommGrpCat.{u}).obj (op V)).rightDerivedPlus i).obj
      ((SheafOfModules.toSheaf R).obj I)) :=
  ((Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus
    ((sheafSections K AddCommGrpCat.{u}).obj (op V))
    ((SheafOfModules.toSheaf R).obj I)).1.1
      (Stacks.Cohomology.ModuleComparison.rightAcyclic_toSheaf_obj_of_injective K V R I
        inferInstance)).2 i hi

/-- **`H^(q+1)(V, I_ab) = 0`**: the higher cohomology over an object `V` of the site of the
underlying abelian sheaf of an injective sheaf of `R`-modules vanishes. This is the acyclicity of
[Stacks, Tag 03FD] in Mathlib's `ℕ`-indexed right derived functors. -/
theorem isZero_rightDerived_sections_toSheaf_succ (V : C) (q : ℕ) :
    IsZero ((((sheafSections K AddCommGrpCat.{u}).obj (op V)).rightDerived (q + 1)).obj
      ((SheafOfModules.toSheaf R).obj I)) :=
  (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff
    ((sheafSections K AddCommGrpCat.{u}).obj (op V))
    (m := ((q : ℤ) + 1)) (n := q + 1) (by push_cast; ring)
    ((SheafOfModules.toSheaf R).obj I)).1
      (isZero_rightDerivedPlus_sections_toSheaf K R I V ((q : ℤ) + 1) (by positivity))

/-- The same vanishing read at `u(V)` and spelled through the cohomology presheaf of the direct
image, which is definitionally the sections functor over `u(V)`. -/
theorem isZero_rightDerived_cohomologyPresheaf_obj_succ (V : D) (q : ℕ) :
    IsZero (((pushforwardCohomologyPresheaf (K := K) AddCommGrpCat.{u} u ⋙
        (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj (op V)).rightDerived (q + 1)).obj
      ((SheafOfModules.toSheaf R).obj I)) :=
  isZero_rightDerived_sections_toSheaf_succ K R I (u.obj V) q

/-- **The cohomology presheaf of the direct image vanishes in positive degrees** on the underlying
abelian sheaf of an injective sheaf of `R`-modules: the presheaf `V ↦ H^(q+1)(u(V), I_ab)` on `𝒟`
is the zero presheaf, all of its values being zero. -/
theorem isZero_rightDerived_cohomologyPresheaf_succ (q : ℕ) :
    IsZero (((pushforwardCohomologyPresheaf (K := K) AddCommGrpCat.{u} u).rightDerived
      (q + 1)).obj ((SheafOfModules.toSheaf R).obj I)) :=
  Functor.isZero_of_isZero_obj _ fun V ↦
    IsZero.of_iso (isZero_rightDerived_cohomologyPresheaf_obj_succ K u R I V.unop q)
      ((pushforwardCohomologyPresheafEvaluationIso AddCommGrpCat.{u} u (q + 1)
        V.unop).app ((SheafOfModules.toSheaf R).obj I)).symm

/-- **[Stacks, Tag 03FD] for higher direct images: `R^(q+1) f_* I_ab = 0`.** For a continuous
functor `u : 𝒟 ⥤ 𝒞` between small sites and an injective sheaf of `R`-modules `I` on `𝒞`, the
higher direct images of the underlying abelian sheaf of `I` vanish in positive degrees.

The underlying abelian sheaf of `I` need not be an injective abelian sheaf, so this does not
follow from `CategoryTheory.Functor.isZero_rightDerived_obj_injective_succ`. It follows instead
from the acyclicity of `I_ab` for sections over every object of `𝒞`, which is the content of
[Stacks, Tag 03FD], together with the description of `R^(q+1) f_*` as the sheafification of the
cohomology presheaf `V ↦ H^(q+1)(u(V), -)` ([Stacks, Tag 072W]). -/
theorem isZero_higherDirectImage_toSheaf_succ (q : ℕ) :
    IsZero (((u.sheafPushforwardContinuous AddCommGrpCat.{u} J K).rightDerived (q + 1)).obj
      ((SheafOfModules.toSheaf R).obj I)) :=
  IsZero.of_iso
    (Functor.map_isZero (presheafToSheaf J AddCommGrpCat.{u})
      (isZero_rightDerived_cohomologyPresheaf_succ K u R I q))
    ((rightDerivedPushforwardIso AddCommGrpCat.{u} u (q + 1)).app
      ((SheafOfModules.toSheaf R).obj I))

end Stacks.Cohomology.ModuleInjectiveHigherDirectImage

end
