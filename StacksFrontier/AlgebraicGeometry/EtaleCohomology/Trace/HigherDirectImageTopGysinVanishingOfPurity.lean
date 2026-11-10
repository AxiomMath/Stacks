module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.HigherDirectImageTopGysinLevelOfPurity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.PurityComplexRestrictScalars
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.PurityComplexBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.PurityComplexFibreVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.RelativeCurveUnitIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.RelativeCurveHigherVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.AffineLineConstantUnit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.AffineLineField
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.InverseImageAlongMorphism
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.HomologyGeometricFibres
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportSpecialization

/-!
# The vanishing of `H²(R g_!(R j_*(j⁻¹ H)))`, from cohomological purity

Let `g : U ⟶ W` be smooth of relative dimension one over `W` smooth over a field `k`, `i : Z ⟶ U`
a closed immersion with `Z = V(f)` finite étale over `W` meeting every irreducible component of
every geometric fibre with two points, `j : U₀ ⟶ U` the open complement, and `H` a locally
constant sheaf of finite type of `ℤ/ℓⁿ⁺¹`-modules with `ℓ` invertible in `k`. The sheaf part of
relative purity (`Stacks.EtaleCohomology.RelativeCurvePuritySheafInput`) gives
`H²(R g_!(R j_*(j⁻¹ H))) = 0` (`Stacks.EtaleCohomology.LowerShriekPurityComplexVanishing`):

1. the vanishing may be checked with the coefficients `ℤ/ℓⁿ⁺¹` rather than `ℤ_ℓ`
   (`Stacks.EtaleCohomology.isZero_homology_derivedLowerShriek_purityComplex_restrictScalars`);
2. it may be checked on the geometric fibres `U_w̄` over the points `w` of `W`, by proper base
   change (`Stacks.EtaleCohomology.isZero_homology_derivedLowerShriek_of_geometricFibres`);
3. on a geometric fibre, `u⁻¹ R j_*(j⁻¹ H) ≅ R j'_*(j'⁻¹ u⁻¹ H)`: the base change map is an
   isomorphism by `(P0)` and `(P2)` on `U` and on `U_w̄` (unconditional:
   `Stacks.EtaleCohomology.Purity.purityUnitIso_of_affineLine`,
   `Stacks.EtaleCohomology.Purity.purityHigherDirectImageVanishing_of_affineLine`) and `(BC1)`
   (`Stacks.EtaleCohomology.isIso_etaleModuleDerivedBaseChange_app_single_restriction`);
4. `H²_c(U_w̄, R j'_* F) = 0` on the curve `U_w̄` over the algebraically closed `κ(w)‾`
   (`Stacks.EtaleCohomology.isZero_homology_two_derivedLowerShriek_purityComplex_of_isAlgClosed`).

Hence the Gysin input for the family `Rʳ g_! G` holds with only relative purity as input
(`Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageTopGysinMorphismInput_of_purity`): the Gysin
input of the Leray step of the reduction of the weight bound of Weil II to curves
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main results

* `Stacks.EtaleCohomology.lowerShriekPurityComplexVanishing_of_purity`.
* `Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageTopGysinMorphismInput_of_purity`.

## Implementation notes

The statements are made in the standard model `HasDerivedCategory.standard`, in which
`Stacks.EtaleCohomology.derivedLowerShriek` is defined.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

-- `AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives` has a free universe; with it in scope
-- the instance problems `EnoughInjectives (EtaleModules Λ X)` get stuck on a universe constraint.
attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

/-- `N • 𝟙` vanishes on `R j_*(j⁻¹ H)` for a sheaf `H` of `ℤ/N`-modules. -/
theorem nsmul_id_purityComplex_zmod (N : ℕ) {U U₀ : Scheme.{u}} (j : U₀ ⟶ U)
    [IsOpenImmersion j] (H : EtaleModules.{u, 0} (ZMod N) U) :
    N • 𝟙 ((purityComplex (ZMod N) j).obj H) = 0 := by
  have hF : N • 𝟙 ((etaleModuleRestriction.{u, 0} (ZMod N) j).obj H) = 0 := by
    rw [nsmul_id_sheaf_zmod_eq _ (a := N) (b := 0) (by simp), zero_smul]
  change N • 𝟙 ((etaleModuleDerivedDirectImage.{u, 0} (ZMod N) j).obj
    ((DerivedCategory.Plus.singleFunctor _ 0).obj
      ((etaleModuleRestriction.{u, 0} (ZMod N) j).obj H))) = 0
  rw [← CategoryTheory.Functor.map_id (etaleModuleDerivedDirectImage.{u, 0} (ZMod N) j),
    ← CategoryTheory.Functor.map_id (DerivedCategory.Plus.singleFunctor _ 0),
    ← Functor.map_nsmul, ← Functor.map_nsmul, hF, Functor.map_zero, Functor.map_zero]

/-- **The vanishing of `H²(R g_!(R j_*(j⁻¹ H)))`, from the sheaf part of relative purity.** -/
theorem lowerShriekPurityComplexVanishing_of_purity (ℓ : ℕ) [Fact ℓ.Prime]
    (hS : RelativeCurvePuritySheafInput.{u}) : LowerShriekPurityComplexVanishing.{u} ℓ := by
  intro k _ hℓk U W Z U₀ _ _ pW _ g _ _ _ _ _ jg i _ _ _ f hZ hfib j _ hj n H hH
  refine isZero_homology_derivedLowerShriek_purityComplex_restrictScalars
    (PadicInt.toZModPow (p := ℓ) (n + 1)) j g jg H 2 ?_
  have : NeZero (ℓ ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  have hN : IsUnit ((ℓ ^ (n + 1) : ℕ) : k) := by rw [Nat.cast_pow]; exact hℓk.pow _
  obtain ⟨hP0, hP2, hBC⟩ := hS k (ℓ ^ (n + 1)) hN U W Z U₀ pW g i f hZ j hj
  refine isZero_homology_derivedLowerShriek_of_geometricFibres (ZMod (ℓ ^ (n + 1))) g jg _
    (ℓ ^ (n + 1)) (NeZero.pos (ℓ ^ (n + 1)))
    (nsmul_id_purityComplex_zmod (ℓ ^ (n + 1)) j H) 2 fun y => ?_
  -- the geometric fibre over `y`
  let s := (GeometricPoint.ofPoint W y).hom
  let Ω := (GeometricPoint.ofPoint W y).residueField
  let u' := pullback.fst g s
  let g' := pullback.snd g s
  have hsq : IsPullback u' g' g s := IsPullback.of_hasPullback g s
  have := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  have : SmoothOfRelativeDimension 1 g' :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension 1) hsq inferInstance
  let U' : Scheme.{u} := pullback g s
  let j' := pullback.snd j u'
  let u₀ := pullback.fst j u'
  have sq : IsPullback u₀ j' j u' := IsPullback.of_hasPullback j u'
  let i' := pullback.snd i u'
  have sqi : IsPullback (pullback.fst i u') i' i u' := IsPullback.of_hasPullback i u'
  have sqig : IsPullback (pullback.fst i u') (i' ≫ g') (i ≫ g) s := sqi.paste_vert hsq
  have : IsFinite (i' ≫ g') := MorphismProperty.of_isPullback sqig inferInstance
  have : Etale (i' ≫ g') := MorphismProperty.of_isPullback sqig inferInstance
  have hj' : Set.range j'.base = (Set.range i'.base)ᶜ := by
    rw [Scheme.Pullback.range_snd, Scheme.Pullback.range_snd, hj, Set.preimage_compl]
  have hNΩ : IsUnit ((ℓ ^ (n + 1) : ℕ) : Ω) := by
    have hu := Purity.isUnit_natCast_globalSections_of_over (k := k) (ℓ := (ℓ ^ (n + 1)))
      (s ≫ pW) hN
    simpa using hu.map (Scheme.ΓSpecIso (.of Ω)).hom.hom
  have hH' := lccModules_etaleModuleInverseImage (ℓ ^ (n + 1)) u' H hH
  -- `u'⁻¹ R j_*(j⁻¹ H) ≅ R j'_*(u₀⁻¹ j⁻¹ H)`
  have h0' := Purity.purityUnitIso_of_affineLine Ω (ℓ ^ (n + 1)) hNΩ
    (Purity.affineLineConstantUnitIso Ω) (𝟙 (Spec (.of Ω))) g' i' j' hj' _ hH'
  have h2' := Purity.purityHigherDirectImageVanishing_of_affineLine Ω (ℓ ^ (n + 1)) hNΩ
    (Purity.affineLineTorsionVanishing Ω) (𝟙 (Spec (.of Ω))) g' i' j' hj' _ hH'
  have hβ := isIso_etaleModuleDerivedBaseChange_app_single_restriction (ZMod (ℓ ^ (n + 1)))
    j j' u' u₀ sq H (hP0 H hH) h0' (hBC Ω (Spec (.of Ω)) _ _ (𝟙 _) s u' g' hsq j' u₀ sq H hH)
    (hP2 H hH) h2'
  -- `H²_c` of `R j'_*` on the fibre
  have hdim : topologicalKrullDim U' ≤ 1 := by
    rcases isEmpty_or_nonempty U' with h | h
    · have : IsEmpty (TopologicalSpace.IrreducibleCloseds U') :=
        ⟨fun Z => h.elim Z.isIrreducible.nonempty.some⟩
      change Order.krullDim (TopologicalSpace.IrreducibleCloseds U') ≤ 1
      rw [Order.krullDim_eq_bot]; exact bot_le
    · rw [topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 1 g']; rfl
  have hfib' : ∀ C ∈ irreducibleComponents U', (∃ x ∈ C, ∃ y ∈ C, x ≠ y) →
      (C ∩ Set.range i'.base).Nonempty := by
    intro C hC h2
    rw [Scheme.Pullback.range_snd]
    exact hfib Ω s C hC h2
  have hV := isZero_homology_two_derivedLowerShriek_purityComplex_of_isAlgClosed Ω g'
    (jg.baseChange hsq) i' j' hj' hdim hfib' (ℓ ^ (n + 1))
    ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1))) u₀).obj
      ((etaleModuleRestriction.{u, 0} (ZMod (ℓ ^ (n + 1))) j).obj H))
  refine hV.of_iso ((DerivedCategory.Plus.homologyFunctor _ 2).mapIso
    ((derivedLowerShriek.{u, 0} g' (jg.baseChange hsq) (ZMod (ℓ ^ (n + 1)))).mapIso
      (asIso ((etaleModuleDerivedBaseChange.{u, 0} (ZMod (ℓ ^ (n + 1))) j j' u' u₀
          sq.w.symm).app _) ≪≫
        (etaleModuleDerivedDirectImage.{u, 0} (ZMod (ℓ ^ (n + 1))) j').mapIso
          ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
            u₀).mapDerivedCategoryPlusObjSingleIso _))))

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

/-- **The Gysin morphism of `R² g_!` along étale divisors, for the family `Rʳ g_! G`, from
relative purity alone**
(`Stacks.EtaleCohomology.LAdicSheaf.HigherDirectImageTopGysinMorphismInput`), with the Tate twist
`Stacks.EtaleCohomology.LAdicSheaf.twistNegOneOp`: the vanishing of `H²(R g_!(R j_*(j⁻¹ H)))`
follows from the sheaf part of purity
(`Stacks.EtaleCohomology.lowerShriekPurityComplexVanishing_of_purity`). -/
theorem LAdicSheaf.higherDirectImageTopGysinMorphismInput_of_purity
    (hPur : RelativeCurvePurityInput B ℓ (LAdicSheaf.twistNegOneOp B ℓ)) :
    LAdicSheaf.HigherDirectImageTopGysinMorphismInput
      (LAdicSheaf.higherDirectImageShriekFamily B ℓ) :=
  LAdicSheaf.higherDirectImageTopGysinMorphismInput_higherDirectImageShriekFamily B ℓ hPur
    (lowerShriekPurityComplexVanishing_of_purity ℓ hPur.1)

end Stacks.EtaleCohomology

end
