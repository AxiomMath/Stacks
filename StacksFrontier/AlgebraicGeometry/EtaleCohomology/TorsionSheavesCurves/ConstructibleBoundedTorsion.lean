module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ConstructibleEtale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionEtaleCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CompactConstructibleAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.IntegerShriekPresentation

/-!
# A constructible torsion sheaf is killed by a positive integer

Let `X` be a quasi-compact quasi-separated scheme and `F` a constructible torsion abelian sheaf
on `X_étale`. Then `n • 𝟙 F = 0` for some `n > 0`. This is the bound on the torsion that the
source uses, in the proof of Stacks Tag 03SC, to split a constructible torsion sheaf into
finitely many `ℓ`-primary parts.

## Main results

* `Stacks.EtaleCohomology.isFinitelyPresentable_of_isConstructibleEtaleSheafIn`: a constructible
  abelian sheaf on Mathlib's small étale site of a quasi-compact quasi-separated scheme is a
  finitely presentable object (Stacks Tag 09Z4, transported from the site of Tag 021B).
* `Stacks.EtaleCohomology.exists_nsmul_id_eq_zero_of_isConstructibleEtaleSheaf`: the bound.

## Implementation notes

The sheaf is the colimit of its subsheaves `F[n!]` (`Stacks.Torsion.isIso_torsionFiltrationDesc`)
and is finitely presentable, so its identity factors through one of them; `n!` then kills it.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] Cardinal.fact_isRegular_aleph0

variable {X : Scheme.{u}}

attribute [local instance]
  Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-- Pushforward of sheaves of `ℤ`-modules along small étale base change is a right adjoint, at
the coefficient universe `u + 1`. -/
local instance isRightAdjoint_pushforward_int (B : BigEtaleSite.{u}) (S T : B.Scheme)
    (f : T ⟶ S) :
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} ℤ) (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint :=
  SmallEtale.isRightAdjointPushforward_moduleCat.{u, u + 1} B ℤ f

/-- Weak sheafification of presheaves of `ℤ`-modules on a localization of the small étale site,
at the coefficient universe `u + 1`. -/
local instance hasWeakSheafify_over_int (B : BigEtaleSite.{u}) (T : B.Scheme)
    (V : SmallEtale B T.obj T.property) :
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{u + 1} ℤ) :=
  SmallEtale.hasWeakSheafifyOver_moduleCat.{u, u + 1} B ℤ T V

/-- **A constructible abelian sheaf on Mathlib's small étale site of a quasi-compact
quasi-separated scheme is finitely presentable.** This is the library's Stacks Tag 09Z4 on the
site of Tag 021B, with Stacks Tag 095N at `ℤ` discharged, transported along
`AlgebraicGeometry.SmallEtale.sheafEquiv`. -/
theorem isFinitelyPresentable_of_isConstructibleEtaleSheafIn [CompactSpace X]
    [QuasiSeparatedSpace X] {B : BigEtaleSite.{u}} {hX : B.Contains X}
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (hF : IsConstructibleEtaleSheafIn B hX F) : IsFinitelyPresentable.{u + 1} F := by
  have : CompactSpace (B.obj X hX).1 := ‹CompactSpace X›
  have : QuasiSeparatedSpace (B.obj X hX).1 := ‹QuasiSeparatedSpace X›
  have : IsFinitelyPresentable.{u + 1} ((toBoundedSiteAb B hX).obj F) :=
    isFinitelyPresentable_of_isConstructibleAbelianSheaf B (B.obj X hX)
      (hasFiniteShriekPresentation_of_isConstructibleModuleSheaf_int B (B.obj X hX)) _ hF
  have : IsCardinalPresentable (((SmallEtale.sheafEquiv B X hX AddCommGrpCat.{u + 1}).inverse ⋙
      (SmallEtale.sheafEquiv B X hX AddCommGrpCat.{u + 1}).functor).obj F)
      Cardinal.aleph0.{u + 1} :=
    isCardinalPresentable_of_equivalence ((toBoundedSiteAb B hX).obj F)
      Cardinal.aleph0.{u + 1} (SmallEtale.sheafEquiv B X hX AddCommGrpCat.{u + 1})
  exact isCardinalPresentable_of_iso
    ((SmallEtale.sheafEquiv B X hX AddCommGrpCat.{u + 1}).counitIso.app F) _

/-- **A constructible torsion abelian sheaf on a quasi-compact quasi-separated scheme is killed
by a positive integer.** -/
theorem exists_nsmul_id_eq_zero_of_isConstructibleEtaleSheaf [CompactSpace X]
    [QuasiSeparatedSpace X] {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (hc : IsConstructibleSmallEtaleSheaf F)
    (ht : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) :
    ∃ n : ℕ, 0 < n ∧ n • 𝟙 F = 0 := by
  obtain ⟨B, hX, hB⟩ := hc
  have := isFinitelyPresentable_of_isConstructibleEtaleSheafIn hB
  have hcol : IsColimit (Cocone.mk F (Stacks.Torsion.torsionFiltrationι X.smallEtaleTopology F)) :=
    have : IsIso ((colimit.isColimit (Stacks.Torsion.torsionFiltration _ F)).desc
        (Cocone.mk F (Stacks.Torsion.torsionFiltrationι X.smallEtaleTopology F))) :=
      Stacks.Torsion.isIso_torsionFiltrationDesc X.smallEtaleTopology F ht
    IsColimit.ofPointIso (colimit.isColimit (Stacks.Torsion.torsionFiltration _ F))
  obtain ⟨j, r, hr⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hcol (𝟙 F)
  refine ⟨Nat.factorial j.down, Nat.factorial_pos _, ?_⟩
  calc (Nat.factorial j.down) • 𝟙 F
        = r ≫ ((Stacks.Torsion.torsionFiltrationι X.smallEtaleTopology F).app j ≫
          ((Nat.factorial j.down) • 𝟙 F)) := by rw [← Category.assoc, hr, Category.id_comp]
    _ = r ≫ 0 := congrArg (r ≫ ·) (kernel.condition _)
    _ = 0 := comp_zero

end Stacks.EtaleCohomology

end
