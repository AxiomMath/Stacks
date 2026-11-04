module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismCohomologyCollapse
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSpaceModuleCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleCohomologyBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.PushforwardLargeSource
import StacksCore.Tactic.StacksAttribute

/-!
# The direct image of an injective module is acyclic for global sections over an affine space

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, with `Y` **affine**, and let `Z` be an injective `𝒪_X`-module.  Then all the higher
cohomology of `f_*Z` on `Y` vanishes.

## Main results

* `AlgebraicGeometry.Space.isZero_sheafH'_ringedToposPushforward_of_injective`: the abelian sheaf
  underlying the direct image of an injective `𝒪_X`-module along the morphism of small étale
  ringed topoi has no positive-degree `CategoryTheory.Sheaf.H'` over any étale chart of the target.
* `AlgebraicGeometry.Space.isZero_rightDerived_evaluation_modulePushforward_of_injective`: the
  derived module sections of `f_*Z` over any étale chart of `Y` vanish in positive degrees, for
  an injective `𝒪_X`-module `Z`.
* `AlgebraicGeometry.Space.acyclicPushforwardOfInjective_of_isAffineSpace`: for an affine `Y`,
  the direct image of an injective `𝒪_X`-module is acyclic for global sections.

## References

* [Stacks Project, Lemma 21.13.3 (Tag 072Z)](https://stacks.math.columbia.edu/tag/072Z)
* [Stacks Project, Lemma 21.14.1 (Tag 0731)](https://stacks.math.columbia.edu/tag/0731)
* [Stacks Project, Lemma 50.6.3 (Tag 08EX)](https://stacks.math.columbia.edu/tag/08EX)
* [Stacks Project, Lemma 69.6.3 (Tag 0D2U)](https://stacks.math.columbia.edu/tag/0D2U)
* [Stacks Project, Lemma 69.4.1 (Tag 03G8)](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian

noncomputable section

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- `Ext`-groups of the abelian sheaves on the small étale site of an algebraic space, at the
site's own morphism universe, at the spelling that goes through
`AlgebraicGeometry.Space.smallEtaleRingedSite`. -/
local instance hasExt_abelianSheafSite (W : AlgebraicSpaces B S hS) :
    HasExt.{u + 1} (Sheaf (smallEtaleRingedSite B S hS W.1 W.2).J AddCommGrpCat.{u}) :=
  hasExt_sheaf_smallEtale B S hS W.1

/-- Enough injective abelian sheaves on the small étale site of an algebraic space, at the
spelling that goes through `AlgebraicGeometry.Space.smallEtaleRingedSite`. -/
local instance enoughInjectives_abelianSheafSite (W : AlgebraicSpaces B S hS) :
    EnoughInjectives (Sheaf (smallEtaleRingedSite B S hS W.1 W.2).J AddCommGrpCat.{u}) :=
  enoughInjectives_sheaf_smallEtale B S hS W.1

/-- `Ext`-groups of the abelian sheaves on the small étale site, at the spelling that goes
through `AlgebraicGeometry.Space.smallEtaleRingedTopos`. -/
local instance hasExt_abelianSheafTopos (W : AlgebraicSpaces B S hS) :
    HasExt.{u + 1} (Sheaf (smallEtaleRingedTopos B S hS W).J AddCommGrpCat.{u}) :=
  hasExt_sheaf_smallEtale B S hS W.1

/-- Enough injective abelian sheaves on the small étale site, at the spelling that goes through
`AlgebraicGeometry.Space.smallEtaleRingedTopos`. -/
local instance enoughInjectives_abelianSheafTopos (W : AlgebraicSpaces B S hS) :
    EnoughInjectives (Sheaf (smallEtaleRingedTopos B S hS W).J AddCommGrpCat.{u}) :=
  enoughInjectives_sheaf_smallEtale B S hS W.1

variable {X Y : AlgebraicSpaces B S hS}

/-- The `Ext`-style sheaf cohomology of the abelian sheaf underlying the direct image of an
injective `𝒪_X`-module vanishes over every étale chart of `Y`, in every positive degree. The direct
image is the one along the morphism `AlgebraicGeometry.Space.smallEtaleRingedToposModulesHom` of
small étale ringed topoi. -/
theorem isZero_sheafH'_ringedToposPushforward_of_injective (f : X ⟶ Y)
    (Z : Modules.{u, u} B S hS X.1 X.2) (hZ : Injective Z)
    (V : SmallEtale B S hS Y.1) (p : ℕ) (hp : 0 < p) :
    IsZero (Sheaf.H'.{u + 1} ((SheafOfModules.toSheaf
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS Y).O)).obj
        ((Stacks.Sheaves.RingedToposModules.pushforwardModules
          (smallEtaleRingedToposModulesHom B S hS f)).obj Z)) p V) :=
  Stacks.Cohomology.isZero_sheafH'_pushforwardModules_of_injective
    (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
    (smallEtaleRingedToposModulesHom B S hS f) (I := Z) (hI := hZ) V p hp

/-- For an injective `𝒪_X`-module `Z`, a morphism `f : X ⟶ Y` of algebraic spaces and any étale
chart `V` of `Y`, the positive-degree derived sections of `f_*Z` over `V` vanish. -/
theorem isZero_rightDerived_evaluation_modulePushforward_of_injective (f : X ⟶ Y)
    (Z : Modules.{u, u} B S hS X.1 X.2) (hZ : Injective Z)
    (V : SmallEtale B S hS Y.1) (p : ℕ) (hp : 0 < p) :
    have := enoughInjectives_modules B S hS Y.1 Y.2
    IsZero (((SheafOfModules.evaluation
      (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)
      (op V)).rightDerived p).obj ((modulePushforward B S hS f).obj Z)) := by
  have := enoughInjectives_modules B S hS Y.1 Y.2
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp).symm⟩
  exact IsZero.of_iso (SmallEtale.isZero_rightDerived_moduleEvaluation_of_isZero_H'_chgUniv
      B S hS Y.1 Y.2 V q
      ((Stacks.Sheaves.RingedToposModules.pushforwardModules
        (smallEtaleRingedToposModulesHom B S hS f)).obj Z)
      (isZero_sheafH'_ringedToposPushforward_of_injective B S hS f Z hZ V (q + 1) hp))
    (((SheafOfModules.evaluation (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)
      (op V)).rightDerived (q + 1)).mapIso ((modulePushforwardIso B S hS f).app Z).symm)

/-- If `Y` is an affine algebraic space, the direct image along `f : X ⟶ Y` of an injective
`𝒪_X`-module is acyclic for global sections of `𝒪_Y`-modules, that is,
`AlgebraicGeometry.Space.AcyclicPushforwardOfInjective` holds for `f`. -/
@[stacks 072Z "at the small étale seating of algebraic spaces, in the shape 0731(3) puts it in:
acyclicity of the direct image of an injective for global sections over an affine base"]
theorem acyclicPushforwardOfInjective_of_isAffineSpace (f : X ⟶ Y)
    (hY : IsAffineSpace B S hS Y.1) : AcyclicPushforwardOfInjective B S hS f := by
  obtain ⟨V, ⟨hV⟩, -⟩ := exists_isTerminal_isAffine_chart B S hS Y hY
  intro Z hZ n hn
  exact isZero_rightDerived_globalSections_of_isTerminalChart B S hS Y hV _ n
    (isZero_rightDerived_evaluation_modulePushforward_of_injective B S hS f Z hZ V n hn)

end AlgebraicGeometry.Space

end

end
