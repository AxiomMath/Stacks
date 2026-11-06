module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleCoefficientsConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleCoefficientsProperProjectionFormula
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantRingBridge
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatRetract
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The projection map of Tag 0F1J at a constructible sheaf of `𝔽_ℓ`-modules

The penultimate paragraph of the proof of [Stacks, Tag 0F1J] works with sheaves of
`𝔽_ℓ`-vector spaces, `ℓ` a prime invertible on the base: for a constructible `ℰ` on a
quasi-compact quasi-separated `X` it embeds `ℰ` into a finite sum of `π_{i,*}𝔽_ℓ` (Stacks 09Z7),
the cokernel being constructible again (Stacks 095R, 03RZ), and concludes by dimension shifting
from the case of `π_{i,*}𝔽_ℓ`, which is the projection formula for the finite `π_i` (Stacks 0F0G)
and base change over `X` and over the `X_i` (Stacks 0F1I).

This file assembles that argument on `D(-_étale, 𝔽_ℓ)`, `𝔽_ℓ = ℤ/ℓ`:

* every sheaf of `𝔽_ℓ̲`-modules is flat (`isFlat_of_fact_prime`), its sections being vector
  spaces over a field (Stacks 03ET);
* **the projection map of `h` at `p⁻¹ℰ[-j]` is invertible for every constructible `ℰ`**
  (`isIso_projectionMap_pullback_singleFunctor_of_isConstructibleEtaleModule`), from the
  dimension shifting `isIso_projectionMap_pullback_singleFunctor_of_exists_finite_embedding`, the
  embedding of Stacks 09Z7 (3) on the model `exists_shortExact_of_isConstructibleEtaleModule`, and
  Stacks 0F0G on `D(-_étale, ℤ/ℓ)` (`isIso_projectionFormulaMap_zmod_of_isProper`).

## Main results

All in the namespace `Stacks.EtaleCohomology.EtaleCoefficients`.

* `isFlat_of_fact_prime`
* `isIso_projectionMap_pullback_singleFunctor_of_isConstructibleEtaleModule` — not registered:
  derived base change along `X ⟶ S` and along the finite `X`-schemes ([Stacks, Tag 0F1I] for
  `S = Spec K`) are arguments.

## References

* [Stacks Project, Tag 0F1J](https://stacks.math.columbia.edu/tag/0F1J)
* [Stacks Project, Tag 09Z7](https://stacks.math.columbia.edu/tag/09Z7)
* [Stacks Project, Tag 03ET](https://stacks.math.columbia.edu/tag/03ET)
* [Stacks Project, Tag 0F0G](https://stacks.math.columbia.edu/tag/0F0G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology.EtaleCoefficients

-- `derivedPullback` and `derivedPushforward` (`StacksFrontier/CategoryTheory/Sites/Cohomology/
-- StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/AdjunctionForRingedTopoi.lean:394`), through `pullback` and `pushforward`,
-- are stated for the standard model of the derived category.
attribute [local instance] HasDerivedCategory.standard

-- The constructibility development imports `SheafOfModules.hasDerivedCategory`
-- (`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean:155`), the locally small model, which
-- would otherwise be found before `HasDerivedCategory.standard`.

open Stacks.EtaleCohomology.BaseChangeOverField

variable (ℓ : ℕ) [Fact ℓ.Prime] {X : Scheme.{u}}

/-- **Every sheaf of `𝔽_ℓ̲`-modules on `X_étale` is flat**, `ℓ` prime. It is the sheafification,
over the constant sheaf of rings `𝔽_ℓ̲`, of its own sections read as a presheaf of `𝔽_ℓ`-modules
(the right adjoint of that reading is fully faithful, so its counit is invertible), and those
sections are vector spaces over the field `𝔽_ℓ`, hence flat (Stacks 03ET,
`Stacks.ConstantSheaf.isFlat_sheafOfModulesOfConstantRing`). -/
@[sga "4 XVII 5.5.25.4" "special case"]
theorem isFlat_of_fact_prime
    (M : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod ℓ)) X).O)) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u + 1, u + 1, u + 1, u + 1}
      (O := (ringedTopos (ULift.{u + 1} (ZMod ℓ)) X).O) M := by
  haveI : HasSheafify (topology X) CommRingCat.{u + 1} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_commRingCat.{u + 1, u + 1, u + 1} _
  let a := Stacks.ConstantSheaf.constantRingSheafMap (topology X)
    (ULift.{u + 1, 0} (ZMod ℓ) : Type (u + 1))
  let adj := Stacks.ConstantSheaf.sheafOfModulesOfConstantRingAdjunction (topology X) a
  let G := Stacks.ConstantSheaf.moduleSheafOfConstantRing (topology X) a
  let e : G ⋙ sheafToPresheaf (topology X) (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) ≅
      (_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars a) ⋙
        Stacks.ConstantSheaf.constantRingPresheafOfModulesInverse _ _ :=
    NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)
  have h1 : (_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars a).Full :=
    (PresheafOfModules.sheafificationAdjunction.{u + 1} a).fullyFaithfulROfIsIsoCounit.full
  have h2 : (_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars a).Faithful :=
    (PresheafOfModules.sheafificationAdjunction.{u + 1} a).fullyFaithfulROfIsIsoCounit.faithful
  have : (Stacks.ConstantSheaf.constantRingPresheafOfModulesInverse (Site X)
      (ULift.{u + 1} (ZMod ℓ))).Full :=
    inferInstanceAs (Stacks.ConstantSheaf.constantRingPresheafEquivalence _ _).inverse.Full
  have : (Stacks.ConstantSheaf.constantRingPresheafOfModulesInverse (Site X)
      (ULift.{u + 1} (ZMod ℓ))).Faithful :=
    inferInstanceAs (Stacks.ConstantSheaf.constantRingPresheafEquivalence _ _).inverse.Faithful
  have : (G ⋙ sheafToPresheaf (topology X) (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).Full :=
    Functor.Full.of_iso e.symm
  have : (G ⋙ sheafToPresheaf (topology X) (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).Faithful :=
    Functor.Faithful.of_iso e.symm
  have : G.Full := Functor.Full.of_comp_faithful G (sheafToPresheaf _ _)
  have : G.Faithful := Functor.Faithful.of_comp G (sheafToPresheaf _ _)
  have : IsIso (adj.counit.app M) := inferInstance
  refine Stacks.SheafOfModules.FlatRetract.isFlat_of_iso _ (asIso (adj.counit.app M)) ?_
  exact Stacks.ConstantSheaf.isFlat_sheafOfModulesOfConstantRing _ a _ (fun U => inferInstance)


/-- **The projection map of Tag 0F1J at a constructible sheaf of `𝔽_ℓ`-modules.** In the setting
of [Stacks, Tag 0F1J] over an arbitrary base `S` (cartesian squares `X' = X ×_S S'`,
`Y = X' ×_{S'} T`, `g` quasi-compact and quasi-separated), let `X` be quasi-compact and
quasi-separated, `ℓ` a prime, and suppose derived base change holds for sheaves killed by `ℓ` along
`X ⟶ S` and along every finite `X`-scheme. Then for every constructible sheaf of `𝔽_ℓ̲`-modules
`ℰ` on `X_étale`, every `F ∈ D⁺(T_étale, 𝔽_ℓ)` and every `j`, the projection map

`p⁻¹ℰ[-j] ⊗^L Rh_*(e⁻¹F) ⟶ Rh_*(h⁻¹p⁻¹ℰ[-j] ⊗^L e⁻¹F)`

is an isomorphism. This is the dimension shifting of the source on the class of constructible
sheaves, every member of which embeds into a finite sum of `π_{i,*}𝔽_ℓ̲` with constructible
cokernel (Stacks 09Z7, 095R, 03RZ), with Stacks 0F0G for the finite `π_i`. -/
theorem isIso_projectionMap_pullback_singleFunctor_of_isConstructibleEtaleModule
    {S X' S' T Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] (πX : X ⟶ S)
    (s : S' ⟶ S) (p : X' ⟶ X) (f' : X' ⟶ S') (hX' : IsPullback p f' πX s) (g : T ⟶ S')
    (h : Y ⟶ X') (e : Y ⟶ T) (hY : IsPullback h e f' g) [QuasiCompact g] [QuasiSeparated g]
    (hBC : DerivedBaseChangeHolds πX ℓ)
    (hBCfin : ∀ {Z : Scheme.{u}} (π : Z ⟶ X) [IsFinite π], DerivedBaseChangeHolds (π ≫ πX) ℓ)
    (F : DerivedCategory.Plus (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod ℓ)) T).O)))
    (M : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod ℓ)) X).O)) (hM : IsConstructibleEtaleModule ℓ X M)
    (j : ℤ) :
    IsIso (projectionMap (ULift.{u + 1} (ZMod ℓ)) h
      ((pullback (ULift.{u + 1} (ZMod ℓ)) p).obj ((DerivedCategory.singleFunctor _ j).obj M))
      ((pullback (ULift.{u + 1} (ZMod ℓ)) e).obj (DerivedCategory.Plus.ι.obj F))) :=
  isIso_projectionMap_pullback_singleFunctor_of_exists_finite_embedding ℓ πX s p f' hX' g h e hY
    hBC hBCfin (fun f _ E K => isIso_projectionFormulaMap_zmod_of_isProper ℓ f E K)
    (IsConstructibleEtaleModule ℓ X) (fun M _ => isFlat_of_fact_prime ℓ M)
    (fun M hM => exists_shortExact_of_isConstructibleEtaleModule ℓ M hM) F M hM j

end Stacks.EtaleCohomology.EtaleCoefficients

end
