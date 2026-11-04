module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.FiniteLevelMatch
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelRestrictionSurjectivity
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MittagLefflerDerivedVanishing

/-!
# `R^p lim = 0` for the level sections of [Stacks, Tag 07JN]

Let `F` be a sheaf of `𝒪_{X/S}`-modules on the small crystalline site satisfying hypotheses (1)
and (2) of [Stacks, Tag 07JN]: `F` is locally quasi-coherent and its closed immersion comparison
maps are surjective, with `X` and `S` affine and `p` nilpotent on `Γ(X, ⊤)`. Then the level
restriction maps of the sections of `F` are surjective, and hence `R^p lim_e Γ(T_e, F) = 0` for
`p ≥ 1`, both for the system `(X, T(n)_e, δ(n))` on the small crystalline site and for the inverse
system `Crystalline.finiteLevelSections` of [Stacks, Tag 07JL] on the affine side.

## Main results

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `hasSurjectiveLevelRestrictions_wholeSpaceSystem_abelianSheaf` and
  `hasSurjectiveUniformLevelRestrictions_abelianSheaf`: the level restrictions of the sections of
  `F` are surjective, in the two forms `...SmallSite.HasSurjectiveLevelRestrictions` and
  `...SmallSite.HasSurjectiveUniformLevelRestrictions`.
* `isZero_firstDerivedLimit_sectionSystem_wholeSpaceSystem` and
  `isZero_homology_rightDerivedLimit_sectionSystem_wholeSpaceSystem`: `R^1 lim_e M(n)_e = 0` and
  `R^p lim_e M(n)_e = 0` for every `p ≥ 1`, for the system of [Stacks, Tag 07JN].
* `isZero_firstDerivedLimit_finiteLevelSections_affineSections` and
  `isZero_homology_rightDerivedLimit_finiteLevelSections_affineSections`: the same for
  `Crystalline.finiteLevelSections` of [Stacks, Tag 07JL], at an arbitrary completed thickening of
  the little affine crystalline category and an arbitrary finite-level system of it.

## References

* [Stacks Project, Tag 07JL](https://stacks.math.columbia.edu/tag/07JL)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07KW](https://stacks.math.columbia.edu/tag/07KW)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Simplicial
open scoped AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) (F : SheafOfModules.{u} (structureSheaf S))

/-! ### Surjectivity of the level restrictions -/

/-- **The level restrictions of the system `(X, T(n)_e, δ(n))` of [Stacks, Tag 07JN] are
surjective** for a locally quasi-coherent sheaf of `𝒪_{X/S}`-modules with surjective closed
immersion comparison maps. -/
theorem hasSurjectiveLevelRestrictions_wholeSpaceSystem_abelianSheaf
    (hF : IsLocallyQuasiCoherent F)
    (hM : CohomologyRestriction.IsSurjectiveComparison F.val) :
    HasSurjectiveLevelRestrictions (wholeSpaceSystem S hp) (abelianSheaf F).obj :=
  surjective_wholeSpaceSystem_level_map hp F hF hM

/-- **The uniform level restrictions on the affine side are surjective**: for a locally
quasi-coherent sheaf of `𝒪_{X/S}`-modules with surjective closed immersion comparison maps, the
restriction maps of the sections of `F` along the level drops
`D(n)/(p)^{N + e + 1} ⟶ D(n)/(p)^{N + e}` are surjective. -/
theorem hasSurjectiveUniformLevelRestrictions_abelianSheaf
    (hF : IsLocallyQuasiCoherent F)
    (hM : CohomologyRestriction.IsSurjectiveComparison F.val) :
    HasSurjectiveUniformLevelRestrictions S hp (abelianSheaf F).obj :=
  surjective_affineSections_level_map hp F hF hM

/-! ### The vanishing of the derived limits -/

/-- **`R^1 lim_e Γ((X, T(n)_e, δ(n)), F) = 0`** for a locally quasi-coherent sheaf of
`𝒪_{X/S}`-modules with surjective closed immersion comparison maps. -/
theorem isZero_firstDerivedLimit_sectionSystem_wholeSpaceSystem
    (hF : IsLocallyQuasiCoherent F)
    (hM : CohomologyRestriction.IsSurjectiveComparison F.val) (n : ℕ) :
    IsZero (Rlim.firstDerivedLimit
      ((sectionSystem (wholeSpaceSystem S hp) (abelianSheaf F).obj).obj ⦋n⦌)) :=
  isZero_firstDerivedLimit_sectionSystem _ _
    (hasSurjectiveLevelRestrictions_wholeSpaceSystem_abelianSheaf hp F hF hM) n

/-- **`R^p lim_e Γ((X, T(n)_e, δ(n)), F) = 0` for every `p ≥ 1`**, for an arbitrary right derived
functor of the inverse limit functor, for a locally quasi-coherent sheaf of `𝒪_{X/S}`-modules with
surjective closed immersion comparison maps. -/
theorem isZero_homology_rightDerivedLimit_sectionSystem_wholeSpaceSystem
    (hF : IsLocallyQuasiCoherent F)
    (hM : CohomologyRestriction.IsSurjectiveComparison F.val) (n : ℕ)
    (RF : DerivedCategory Rlim.InvSystemAb.{u + 1} ⥤ DerivedCategory Ab.{u + 1})
    (α : (lim : Rlim.InvSystemAb.{u + 1} ⥤ Ab.{u + 1}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    (hRF : RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso Rlim.InvSystemAb.{u + 1} (ComplexShape.up ℤ)))
    (q : ℤ) (hq : 1 ≤ q) :
    IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} q).obj
      (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{u + 1} 0).obj
        ((sectionSystem (wholeSpaceSystem S hp) (abelianSheaf F).obj).obj ⦋n⦌)))) :=
  isZero_homology_rightDerivedLimit_sectionSystem _ _
    (hasSurjectiveLevelRestrictions_wholeSpaceSystem_abelianSheaf hp F hF hM) n RF α hRF q hq

/-- **`R^1 lim_e Γ(T_e, F) = 0` for the inverse system of [Stacks, Tag 07JL]**, at an arbitrary
completed thickening of the little affine crystalline category and an arbitrary finite-level
system of it, applied to the sections of `F` read on that category through the affine-to-global
equivalence, for a locally quasi-coherent sheaf of `𝒪_{X/S}`-modules with surjective closed
immersion comparison maps. -/
theorem isZero_firstDerivedLimit_finiteLevelSections_affineSections
    (hF : IsLocallyQuasiCoherent F)
    (hM : CohomologyRestriction.IsSurjectiveComparison F.val)
    {X : _root_.Crystalline.CompletedCrystallineThickening.{u, u, u} (affineSituation S hp)}
    (T : _root_.Crystalline.FiniteLevelSystem X) :
    IsZero (Rlim.firstDerivedLimit
      (_root_.Crystalline.finiteLevelSections T (affineSections S hp (abelianSheaf F).obj))) :=
  _root_.Crystalline.isZero_firstDerivedLimit_finiteLevelSections T _
    fun e ↦ surjective_affineSections_finiteLevelSystem_transition hp F hF hM T (Nat.le_succ e)

/-- **`R^p lim_e Γ(T_e, F) = 0` for every `p ≥ 1` for the inverse system of
[Stacks, Tag 07JL]**, for an arbitrary right derived functor of the inverse limit functor, for a
locally quasi-coherent sheaf of `𝒪_{X/S}`-modules with surjective closed immersion comparison
maps. -/
theorem isZero_homology_rightDerivedLimit_finiteLevelSections_affineSections
    (hF : IsLocallyQuasiCoherent F)
    (hM : CohomologyRestriction.IsSurjectiveComparison F.val)
    {X : _root_.Crystalline.CompletedCrystallineThickening.{u, u, u} (affineSituation S hp)}
    (T : _root_.Crystalline.FiniteLevelSystem X)
    (RF : DerivedCategory Rlim.InvSystemAb.{u + 1} ⥤ DerivedCategory Ab.{u + 1})
    (α : (lim : Rlim.InvSystemAb.{u + 1} ⥤ Ab.{u + 1}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    (hRF : RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso Rlim.InvSystemAb.{u + 1} (ComplexShape.up ℤ)))
    (q : ℤ) (hq : 1 ≤ q) :
    IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} q).obj
      (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{u + 1} 0).obj
        (_root_.Crystalline.finiteLevelSections T
          (affineSections S hp (abelianSheaf F).obj))))) :=
  _root_.Crystalline.isZero_homology_rightDerivedLimit_finiteLevelSections T _
    (fun e ↦ surjective_affineSections_finiteLevelSystem_transition hp F hF hM T (Nat.le_succ e))
    RF α hRF q hq

end Crystalline.GlobalCrystallineSituation.SmallSite

end
