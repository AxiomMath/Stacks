module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFlatLevelZeroReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.HigherDirectImageTopGysinMorphismShriek
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModelBridges.ZModConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.RestrictionOfScalarsNoncomm
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LisseExtVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierTransformDegreeZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonOriginFibreScheme
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.ElementaryFibrationLowerShriek
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `R⁰ pr₂!` of the bottom flat level of Laumon's family sheaf vanishes

Let `f : P ⟶ T` be the base change of the affine line `𝔸¹_k ⟶ Spec k` along `t : T ⟶ Spec k`, and
`G` a sheaf of `Λ`-modules on `P` killed by a positive integer and locally constant of finite type.
Then `R⁰ f_! G = 0`: on a geometric fibre `𝔸¹_Ω` of `f`, connected and not proper over `Ω`, the
restriction of `G` is locally constant, so it has no compactly supported sections, and the
vanishing of `R⁰ f_! G` is checked on the geometric fibres by proper base change for `Rf_!`.

The levels of a lisse ℓ-adic sheaf, read as sheaves of `ℤ_ℓ`-modules on Mathlib's small étale
site, are locally constant of finite type. Applied to the bottom level `K'₀` of the flat model of
the family sheaf of Laumon's argument for [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) and
the projection `pr₂ : 𝔸² ⟶ 𝔸¹_t`, this is the first half `R⁰ pr₂! K'₀ = 0` of
`Stacks.EtaleCohomology.LaumonFamilyFlatLevelZeroVanishingInput`.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.isFiniteTypeLocallyConstant_padicTower_of_isLisse`.
* `Stacks.EtaleCohomology.connectedSpace_pullback_and_not_isProper_of_isPullback_affineLine`.
* `Stacks.EtaleCohomology.isZero_lowerShriekHomology_zero_of_isPullback_affineLine`.
* `Stacks.EtaleCohomology.isZero_lowerShriekHomology_zero_laumonFamilySheaf_flatModel`.

## Implementation notes

`Stacks.EtaleCohomology.derivedLowerShriek` lives in the standard model
`HasDerivedCategory.standard`, and so do the statements on `R⁰ f_!`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.LAdicTower AlgebraicGeometry
open AlgebraicGeometry.SmallEtale Stacks.ArtinSchreier

universe u

namespace Stacks.EtaleCohomology

section LocallyConstant

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [hW : ∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1] [Fact ℓ.Prime]

/-- **The levels of a lisse ℓ-adic sheaf are locally constant of finite type as sheaves of
`ℤ_ℓ`-modules on Mathlib's small étale site**: a level is finite locally constant
(`Stacks.EtaleCohomology.LAdicSheaf.isFiniteLocallyConstant_level_of_isLisse`), hence locally
constant with finitely generated `ℤ/ℓⁿ⁺¹`-values; restricting the scalars to `ℤ_ℓ` keeps the
values finite, and the condition transports along the equivalence of the two small étale sites. -/
theorem LAdicSheaf.isFiniteTypeLocallyConstant_padicTower_of_isLisse
    (F : LAdicSheaf.{u, u + 1} B X ℓ) (hF : F.IsLisse) (n : ℕ) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant.{u + 1} ℤ_[ℓ] X.1.smallEtaleTopology
      (towerObj (LAdicSheaf.padicTower B X ℓ F) n) := by
  let J := SmallEtale.topology B X.1 X.property
  let hWn : ∀ V, HasWeakSheafify (J.over V) (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) :=
    fun V => hW n X V
  have : J.HasSheafCompose
      (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) AddCommGrpCat.{u + 1}) :=
    ModuleSheaf.hasSheafCompose_forget₂.{u + 1} _ _
  have : ∀ V, (J.over V).HasSheafCompose
      (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) AddCommGrpCat.{u + 1}) := fun V =>
    ModuleSheaf.hasSheafCompose_forget₂.{u + 1} _ _
  have h₁ : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant.{u + 1} (ZMod (ℓ ^ (n + 1))) J
      (F.level n) :=
    ConstantSheaf.isFiniteTypeLocallyConstant_of_isFiniteLocallyConstant_forget.{u + 1, u, u + 1}
      J _ _
      (LAdicSheaf.isFiniteLocallyConstant_underlyingLAdicLevel_of_isLisse F hF n)
  have h₂ : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant.{u + 1} ℤ_[ℓ] J
      (LAdicSheaf.padicLevel B X ℓ F n) :=
    isFiniteTypeLocallyConstant_restrictScalarsSheafNoncomm.{u + 1}
      (PadicInt.toZModPow (n + 1)) J (fun E hE => by
        rw [ModuleCat.isFG_iff] at hE ⊢
        have hE' : Finite E := Module.finite_of_finite (ZMod (ℓ ^ (n + 1)))
        have : Finite ((ModuleCat.restrictScalars.{u + 1} (PadicInt.toZModPow (n + 1))).obj E) :=
          hE'
        exact Module.Finite.of_finite) _ h₁
  exact (SmallEtale.isFiniteTypeLocallyConstant_sheafEquiv_functor_iff B X ℤ_[ℓ] _).2 h₂

end LocallyConstant

section Geometry

variable (k : Type u) [Field k]

/-- **The fibres of a base change of the affine line over fields are connected and not proper**:
for a cartesian square `P = 𝔸¹_k ×_k T` and `s : Spec Ω ⟶ T`, the fibre `P ×_T Spec Ω` is
`𝔸¹_Ω`. -/
theorem connectedSpace_pullback_and_not_isProper_of_isPullback_affineLine {P T : Scheme.{u}}
    {a : P ⟶ Spec (.of (Polynomial k))} {f : P ⟶ T} {t : T ⟶ Spec (.of k)}
    (sq : IsPullback a f (affineLineStructureMap k) t) (Ω : Type u) [Field Ω]
    (s : Spec (.of Ω) ⟶ T) :
    ConnectedSpace ↥(pullback f s) ∧ ¬ IsProper (pullback.snd f s) := by
  have h := (IsPullback.of_hasPullback f s).paste_horiz sq
  let e := h.isoIsPullback _ _ (isPullback_affineLineBaseChange_of_hom k (s ≫ t))
  have he : e.hom ≫ (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of Ω)) ↘ Spec (.of Ω)) =
      pullback.snd f s :=
    IsPullback.isoIsPullback_hom_snd _ _ _ _
  have : IrreducibleSpace (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of Ω))) := inferInstance
  refine ⟨?_, fun hP => ?_⟩
  · let h' := Scheme.homeoOfIso e.symm
    exact h'.surjective.connectedSpace h'.continuous
  · refine not_isProper_affineSpace Ω (ULift.{u} (Fin 1)) ?_
    rw [← (Iso.inv_comp_eq e).2 he.symm]
    infer_instance

end Geometry

section DegreeZero

attribute [local instance] HasDerivedCategory.standard
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits

variable (k : Type u) [Field k] (Λ : Type) [Ring Λ]

/-- **`R⁰ f_! G = 0` on a relative affine line** `P = 𝔸¹_k ×_k T ⟶ T`, for a sheaf `G` locally
constant of finite type killed by a positive integer: on a geometric fibre `𝔸¹_Ω` of `f`, connected
and not proper, the restriction of `G` is locally constant and has no compactly supported sections
(`Stacks.EtaleCohomology.isZero_homology_zero_derivedLowerShriek_of_isLocallyConstantWith`), and
the vanishing is checked on the geometric fibres by proper base change
(`Stacks.EtaleCohomology.isZero_homology_derivedLowerShriek_of_geometricFibres`). -/
@[sga "5 VII 7.1.1" "b), special case"]
theorem isZero_lowerShriekHomology_zero_of_isPullback_affineLine {P T : Scheme.{u}}
    {a : P ⟶ Spec (.of (Polynomial k))} {f : P ⟶ T} {t : T ⟶ Spec (.of k)}
    (sq : IsPullback a f (affineLineStructureMap k) t) [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated f] (j : CompactificationOf (Over.mk f)) (G : EtaleModules.{u, 0} Λ P) (m : ℕ)
    (hm : 0 < m) (hG : m • 𝟙 G = 0)
    (hlc : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant.{u + 1} Λ P.smallEtaleTopology G) :
    IsZero ((lowerShriekHomology Λ f j 0).obj G) := by
  refine IsZero.of_iso ?_ ((singleHomologyPlusSingleIso (derivedLowerShriek.{u, 0} f j Λ) 0).app G)
  refine isZero_homology_derivedLowerShriek_of_geometricFibres Λ f j _ m hm ?_ 0 fun y => ?_
  · rw [← CategoryTheory.Functor.map_id (DerivedCategory.Plus.singleFunctor _ 0),
      ← Functor.map_nsmul, hG, Functor.map_zero]
  let s := (GeometricPoint.ofPoint T y).hom
  let Ω := (GeometricPoint.ofPoint T y).residueField
  let f' := pullback.snd f s
  let u' := pullback.fst f s
  have hp := IsPullback.of_hasPullback f s
  have : LocallyOfFiniteType f' := MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
    hp inferInstance
  have : IsSeparated f' := MorphismProperty.of_isPullback (P := @IsSeparated)
    hp inferInstance
  have : QuasiCompact f' := MorphismProperty.of_isPullback (P := @QuasiCompact)
    hp inferInstance
  obtain ⟨_, hnp⟩ := connectedSpace_pullback_and_not_isProper_of_isPullback_affineLine k sq Ω s
  let j' := j.baseChange hp
  exact IsZero.of_iso
    (isZero_homology_zero_derivedLowerShriek_of_isLocallyConstantWith Λ _ Ω f' j'
      (j'.not_isClosed_range_immersion_of_not_isProper hnp) _
      (isFiniteTypeLocallyConstant_etaleModuleInverseImage_of_hom u' Λ G hlc))
    ((DerivedCategory.Plus.homologyFunctor _ 0).mapIso ((derivedLowerShriek.{u, 0} f' j' Λ).mapIso
      ((Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
        (etaleModuleInverseImage.{u, 0} Λ u') 0).app G)))

end DegreeZero

section Laumon

attribute [local instance] HasDerivedCategory.standard

variable (k' : Type u) [Field k'] [Fintype k'] (B : BigEtaleSite.{u})
  (hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k')))))
  (hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k'))))
  {ℓ : ℕ} [Fact ℓ.Prime] {E : Type} [Field E] [Algebra ℚ_[ℓ] E] {d : ℕ}
  (b : Module.Basis (Fin d) ℚ_[ℓ] E) (ψ' : AddChar k' E) (n₀ : ℕ) (c : k')
  (z : GeometricPoint (Spec (.of (Polynomial (Polynomial k')))))
  (p₀ : (finiteEtaleFiberFunctor z).obj
    (Stacks.ArtinSchreier.cover k' (Polynomial (Polynomial k')) (laumonKernel k' n₀ c))) {m : ℕ}
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

omit [Fintype k'] in
/-- **`𝔸² = 𝔸¹_x ×_{k'} 𝔸¹_t` with `pr₂` the base change of the `x`-line**: the square of
`pr₁`, `pr₂` and the two structure morphisms of the affine line is cartesian. -/
theorem isPullback_laumonFamilyPr₁_laumonFamilyProjection :
    IsPullback (laumonFamilyPr₁ k') (B.inclusion.map (laumonFamilyProjection k' B hS hL))
      (affineLineStructureMap k') (affineLineStructureMap k') :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_C_mapRingHom_C k')

/-- **(B1) `R⁰pr₂! K'₀ = 0`** for the bottom level `K'₀` of the flat model of Laumon's family
sheaf ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)): the family sheaf is lisse, so is its
flat model, whose bottom level is locally constant of finite type and killed by `ℓ`, and `pr₂` is
the affine line over the `t`-line
(`Stacks.EtaleCohomology.isZero_lowerShriekHomology_zero_of_isPullback_affineLine`). -/
theorem isZero_lowerShriekHomology_zero_laumonFamilySheaf_flatModel
    (σ₁ : EtaleFundamentalGroup (Spec (.of (Polynomial k'))) (z.map (laumonFamilyPr₁ k')) →*
      GL (Fin m) E) (hσ₁ : Continuous (restrictScalarsRep b σ₁))
    (jg : CompactificationOf (Over.mk (B.inclusion.map (laumonFamilyProjection k' B hS hL)))) :
    haveI : IsNoetherian (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS).1 :=
      inferInstanceAs (IsNoetherian (Spec (.of (Polynomial (Polynomial k')))))
    IsZero ((lowerShriekHomology ℤ_[ℓ] (B.inclusion.map (laumonFamilyProjection k' B hS hL))
        jg 0).obj
        (towerObj (LAdicSheaf.padicTower B _ ℓ (LAdicSheaf.flatModel B ℓ
          (laumonFamilySheaf k' B hS b ψ' n₀ c z p₀ σ₁ hσ₁).toLAdicSheaf)) 0)) := by
  have : IsNoetherian (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS).1 :=
    inferInstanceAs (IsNoetherian (Spec (.of (Polynomial (Polynomial k')))))
  let X := Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS
  let K := (laumonFamilySheaf k' B hS b ψ' n₀ c z p₀ σ₁ hσ₁).toLAdicSheaf
  have hK : K.IsLisse := LAdicSheaf.representationSheaf_isLisse B X z _ _
  exact isZero_lowerShriekHomology_zero_of_isPullback_affineLine k' ℤ_[ℓ]
    (isPullback_laumonFamilyPr₁_laumonFamilyProjection k' B hS hL) jg _ (ℓ ^ (0 + 1))
    (pow_pos (Fact.out : ℓ.Prime).pos _) (LAdicSheaf.padicTower_annihilated B X ℓ _ 0)
    (LAdicSheaf.isFiniteTypeLocallyConstant_padicTower_of_isLisse B X ℓ _
      (LAdicSheaf.isLisse_flatModel B ℓ K hK) 0)

end Laumon

end Stacks.EtaleCohomology

end
