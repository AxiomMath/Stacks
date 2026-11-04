module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.RestrictionBaseChangeAb
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.RelativeCurveFirstBaseChangeAb
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.ModuleBaseChangeFromAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.ModuleSingleBaseChangeFromAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.RelativeCurveUnitIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.RelativeCurveHigherVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.AffineLineConstantUnit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.AffineLineField
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.RelativeCurvePurityInput
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZeroComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.InverseImageAlongMorphism
public import StacksFrontier.AlgebraicGeometry.Descent.OpenImmersionEtaleDescent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `(BC1)` of relative purity along an étale divisor of a smooth relative curve

Let `W` be smooth over a field `k`, `g : U ⟶ W` smooth of relative dimension one, `i : Z ⟶ U` a
closed immersion with `Z ⟶ W` étale, `j : U₀ ⟶ U` the open complement of `Z` and `N` invertible
in `k`. For `W' ⟶ W` with `W'` smooth over a field `k'`, `U' = U ×_W W'` and
`U₀' = U₀ ×_U U'`, the degree-one cohomology of the derived base change map
`u'⁻¹ R j_* ⟶ R j'_* u₀⁻¹` at `j⁻¹ H` is an isomorphism for every locally constant sheaf `H` of
finite type of `ℤ/N`-modules on `U` (`Stacks.EtaleCohomology.PurityFirstBaseChangeIso`).

In fact the whole derived base change map is invertible at `j⁻¹ H`. On the underlying abelian
sheaves it is checked degree by degree: in degree `0` from `(P0)` on `U` and on `U'`
(`Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_zero_restriction`), in degree `1` by the
étale local computation with Kummer generators
(`Stacks.EtaleCohomology.Purity.isIso_higherBaseChangeMapAb_one_of_relativeCurve`), and in degrees
`q ≥ 2` because both sides vanish by `(P2)` on `U` and on `U'`. The data on `U'` is again a
smooth relative curve with an étale divisor, `Z' = Z ×_U U'`, over `W'`, and `N` is invertible in
`k'` as soon as `U'` is nonempty; over an empty `U'` there is nothing to prove. The abelian
statement gives the statement for sheaves of modules
(`isIso_etaleModuleDerivedBaseChange_app_single_of_isIso_smallEtaleDerivedBaseChangeAb`).

Together with `(P0)` and `(P2)` this proves the sheaf-level part of relative purity,
`Stacks.EtaleCohomology.RelativeCurvePuritySheafInput`.

## Main results

* `Stacks.EtaleCohomology.Purity.purityFirstBaseChangeIso_of_relativeCurve`.
* `Stacks.EtaleCohomology.Purity.relativeCurvePuritySheafInput`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.Purity

attribute [local instance] HasDerivedCategory.standard

attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

variable (k : Type u) [Field k] (N : ℕ) (hN : IsUnit (N : k)) {U W Z U₀ : Scheme.{u}}
  (pW : W ⟶ Spec (.of k)) [Smooth pW] (g : U ⟶ W) [SmoothOfRelativeDimension 1 g]
  (i : Z ⟶ U) [IsClosedImmersion i] [Etale (i ≫ g)] (j : U₀ ⟶ U) [IsOpenImmersion j]
  (hj : Set.range j.base = (Set.range i.base)ᶜ)
  {k' : Type u} [Field k'] {W' U' U₀' : Scheme.{u}} (pW' : W' ⟶ Spec (.of k')) [Smooth pW']
  (uW : W' ⟶ W) (u' : U' ⟶ U) (g' : U' ⟶ W') (hU : IsPullback u' g' g uW)
  (j' : U₀' ⟶ U') [IsOpenImmersion j'] (u₀ : U₀' ⟶ U₀) (sq : IsPullback u₀ j' j u')

include hN hj hU pW pW' in
/-- **`(BC1)` of relative purity along an étale divisor of a smooth relative curve.** For `W`
smooth over `k`, `g : U ⟶ W` smooth of relative dimension one, `i : Z ⟶ U` a closed immersion
with `Z ⟶ W` étale, `j : U₀ ⟶ U` the open complement and `N` invertible in `k`, and for the base
change `U' = U ×_W W'`, `U₀' = U₀ ×_U U'` along `W' ⟶ W` with `W'` smooth over a field `k'`, the
degree-one cohomology of the derived base change map `u'⁻¹ R j_* ⟶ R j'_* u₀⁻¹` at `j⁻¹ H` is an
isomorphism for every locally constant sheaf `H` of finite type of `ℤ/N`-modules. -/
theorem purityFirstBaseChangeIso_of_relativeCurve : PurityFirstBaseChangeIso N j u' j' u₀ sq := by
  intro H hH
  by_cases hne : IsEmpty U'
  · have h0 := isZero_etaleModules_of_isEmpty (ZMod N) U'
    have key : ∀ {A B : EtaleModules.{u, 0} (ZMod N) U'} (f : A ⟶ B), IsIso f := fun f =>
      ⟨⟨(h0 _).to_ _, (h0 _).eq_of_src _ _, (h0 _).eq_of_src _ _⟩⟩
    exact key _
  obtain ⟨p⟩ := not_isEmpty_iff.1 hne
  -- `N` is invertible in `k'`
  have hN' : IsUnit (N : k') := by
    rw [isUnit_iff_ne_zero]
    intro hk0
    have hU1 := isUnit_natCast_globalSections_of_over (ℓ := N) (u' ≫ g ≫ pW) hN
    have h0 : ((N : ℕ) : Γ(U', ⊤)) = 0 := by
      have := map_natCast (((Scheme.ΓSpecIso (.of k')).inv ≫ (g' ≫ pW').appTop).hom) N
      rw [← this, hk0, map_zero]
    rw [h0] at hU1
    have := hU1.map (U'.presheaf.germ ⊤ p trivial).hom
    rw [map_zero] at this
    exact not_isUnit_zero this
  -- the relative curve `U' ⟶ W'` and its divisor `Z' = Z ×_U U'`
  have := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  have : SmoothOfRelativeDimension 1 g' :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension 1) hU inferInstance
  let i' := pullback.snd i u'
  have hZ : IsPullback (pullback.fst i u') i' i u' := IsPullback.of_hasPullback i u'
  have : Etale (i' ≫ g') :=
    MorphismProperty.of_isPullback (P := @Etale) (hZ.paste_vert hU) inferInstance
  have hj' : Set.range j'.base = (Set.range i'.base)ᶜ := by
    rw [range_snd_of_isPullback sq, range_snd_of_isPullback hZ, hj, Set.preimage_compl]
  -- `(P0)` and `(P2)` on `U` and on `U'`
  have hH' := lccModules_etaleModuleInverseImage N u' H hH
  have hP0 := purityUnitIso_of_affineLine k N hN (affineLineConstantUnitIso k) pW g i j hj H hH
  have hP0' := purityUnitIso_of_affineLine k' N hN' (affineLineConstantUnitIso k') pW' g' i' j'
    hj' _ hH'
  have hP2 := purityHigherDirectImageVanishing_of_affineLine k N hN (affineLineTorsionVanishing k)
    pW g i j hj H hH
  have hP2' := purityHigherDirectImageVanishing_of_affineLine k' N hN'
    (affineLineTorsionVanishing k') pW' g' i' j' hj' _ hH'
  -- the abelian base change maps in every degree
  have hq : ∀ q : ℕ, IsIso ((higherBaseChangeMapAb u' j j' u₀ sq.w.symm q).app
      ((etaleModuleForgetAb.{u, 0} (ZMod N) U₀).obj
        ((etaleModuleRestriction.{u, 0} (ZMod N) j).obj H))) := by
    intro q
    rcases q with _ | _ | q
    · exact isIso_higherBaseChangeMapAb_zero_restriction j j' u' u₀ (ZMod N) sq H hP0 hP0'
    · exact isIso_higherBaseChangeMapAb_one_of_relativeCurve k N hN pW g i j hj pW' uW u' g' hU
        j' u₀ sq H hH
    · exact isIso_higherBaseChangeMapAb_restriction_of_isZero j j' u' u₀ (ZMod N) sq H (q + 2)
        (hP2 (q + 2) (by omega)) (hP2' (q + 2) (by omega))
  have := isIso_etaleModuleDerivedBaseChange_app_single_of_isIso_smallEtaleDerivedBaseChangeAb
    (ZMod N) j sq _
    (isIso_smallEtaleDerivedBaseChangeAb_app_single_of_forall u' j j' u₀ sq.w.symm _ hq)
  exact Functor.map_isIso _ _

/-- **The sheaf-level part of relative purity along an étale divisor of a smooth relative
curve**: `(P0)` (`Stacks.EtaleCohomology.Purity.purityUnitIso_of_affineLine`), `(P2)`
(`Stacks.EtaleCohomology.Purity.purityHigherDirectImageVanishing_of_affineLine`) and `(BC1)`
(`Stacks.EtaleCohomology.Purity.purityFirstBaseChangeIso_of_relativeCurve`), the inputs along
`𝐆_m ⊆ 𝐀¹` being `Stacks.EtaleCohomology.Purity.affineLineConstantUnitIso` and
`Stacks.EtaleCohomology.Purity.affineLineTorsionVanishing`. -/
@[sga "4 XIX 3.2" "special case", sga "4½ Th_finitude 5.1.3" "1.3.3.2"]
theorem relativeCurvePuritySheafInput : RelativeCurvePuritySheafInput.{u} := by
  intro k _ N hN U W Z U₀ pW _ g _ i _ _ _ f hf j _ hj
  exact ⟨purityUnitIso_of_affineLine k N hN (affineLineConstantUnitIso k) pW g i j hj,
    purityHigherDirectImageVanishing_of_affineLine k N hN (affineLineTorsionVanishing k)
      pW g i j hj,
    fun k' _ W' U' U₀' pW' _ uW u' g' hU j' _ u₀ sq =>
      purityFirstBaseChangeIso_of_relativeCurve k N hN pW g i j hj pW' uW u' g' hU j' u₀ sq⟩

end Stacks.EtaleCohomology.Purity

end
