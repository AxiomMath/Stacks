module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFamilyNoPunctualSectionsCharNe
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFlatLevelZeroDegreeZero

/-!
# `H¹_c(𝔸²_k̄, K'₀)` through the first projection

For the bottom level `K'₀` of the flat model of the family sheaf of Laumon's argument
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)) on the plane `𝔸² = Spec k'[x][t]`, the
vanishing `H¹_c(𝔸²_k̄, K'₀) = 0` is read along the first projection `pr₁ : 𝔸² → 𝔸¹_x`
(`Stacks.EtaleCohomology.laumonFamilyFirstProjection`): both projections followed by the structure
morphism of the line are the structure morphism of the plane, so the Leray edge
`H⁰_c(𝔸¹_{x,k̄}, R¹pr₁! K'₀) ≅ H¹_c(𝔸²_k̄, K'₀)`, valid once `R⁰pr₁! K'₀ = 0`
(`LAdicSheaf.nonempty_compactSupportSheafCohomology_lowerShriekHomology_one_iso`),
shows that `H¹_c(𝔸²_k̄, K'₀) = 0` as soon as `R¹pr₁! K'₀ = 0`. The vanishing `R⁰pr₁! K'₀ = 0` holds
because `pr₁` is the affine line over the `x`-line and `K'₀` is locally constant
(`isZero_lowerShriekHomology_zero_laumonFamilySheaf_flatModel_firstProjection`).

So `Stacks.EtaleCohomology.LaumonFamilyFlatLevelZeroVanishingInput'` reduces to
`Stacks.EtaleCohomology.LaumonFamilyFirstProjectionVanishingInput'`: `R¹pr₁! K'₀ = 0` for
`ℓ ≠ char k'` (on the fibre over `x̄`, the `t`-line, `K'₀` is `M ⊗ L_ψ'(h(x̄) t)`: constant when
`h(x̄) = 0`, a nontrivial Artin–Schreier sheaf otherwise).

## Main definitions

* `laumonFamilyFirstProjection`.
* `LaumonFamilyFirstProjectionVanishingInput'`.

## Main results

* `isZero_compactSupportSheafCohomology_one_of_lowerShriekHomology`.
* `isZero_lowerShriekHomology_zero_laumonFamilySheaf_flatModel_firstProjection`.
* `laumonFamilyFlatLevelZeroVanishingInput'_of_firstProjection`.
* `laumonFamilyNoPunctualSectionsInput'_of_firstProjection`.

## Implementation notes

`Stacks.EtaleCohomology.derivedLowerShriek` lives in the standard model
`HasDerivedCategory.standard`, and so do the statements here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.LAdicTower AlgebraicGeometry
open AlgebraicGeometry.SmallEtale Stacks.ArtinSchreier

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section Leray

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime] {U W : B.Scheme} [IsNoetherian U.1]
  [IsNoetherian W.1] (g : U ⟶ W) [LocallyOfFiniteType (B.inclusion.map g)]
  [QuasiCompact (B.inclusion.map g)] [IsSeparated (B.inclusion.map g)]
  (jg : CompactificationOf (Over.mk (B.inclusion.map g))) {k : Type u} [Field k] [Finite k]
  (fW : W.1 ⟶ Spec (.of k)) [LocallyOfFiniteType fW] [QuasiCompact fW] [IsSeparated fW]
  (kbar : Type u) [Field kbar] [Algebra k kbar]

attribute [local instance] moduleCat_hasLimitsOfSize

/-- **`H¹_c(U_k̄, K) = 0` once `R⁰g_! K = 0` and `R¹g_! K = 0`**, for an ℓ-power torsion sheaf `K`
on `U`, `g : U ⟶ W` and any compactification of a morphism `φ = g ≫ f_W` to `Spec k`: by the Leray
edge, `H¹_c(U_k̄, K) ≅ H⁰_c(W_k̄, R¹g_! K)`. -/
theorem isZero_compactSupportSheafCohomology_one_of_lowerShriekHomology
    (K : (IsLPowerTorsion ℓ U.1).FullSubcategory)
    (h0 : IsZero ((lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg 0).obj K.obj))
    (h1 : IsZero ((lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg 1).obj K.obj))
    (φ : U.1 ⟶ Spec (.of k)) (hφ : B.inclusion.map g ≫ fW = φ) [LocallyOfFiniteType φ]
    [QuasiCompact φ] [IsSeparated φ] (jU : CompactificationOf (Over.mk φ)) :
    IsZero ((compactSupportSheafCohomology ℤ_[ℓ] φ jU kbar 1).obj K.obj) := by
  have := Fintype.ofFinite k
  subst hφ
  obtain ⟨jW⟩ : Nonempty (CompactificationOf (Over.mk fW)) := IsCofiltered.nonempty
  obtain ⟨e⟩ := LAdicSheaf.nonempty_compactSupportSheafCohomology_lowerShriekHomology_one_iso B ℓ g
    jg fW jW kbar K h0 jU
  have h₁ : (sheafSingleComplex ℤ_[ℓ] (X := W.1)).Additive := inferInstance
  have h₂ := additive_compactSupportFrobeniusFunctor ℤ_[ℓ] fW jW kbar
  have h₃ : (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ_[ℓ]) 0).Additive :=
    inferInstance
  have : (compactSupportSheafCohomology ℤ_[ℓ] fW jW kbar 0).Additive :=
    inferInstanceAs (Functor.Additive (_ ⋙ _ ⋙ _))
  have hpz : (compactSupportSheafCohomology ℤ_[ℓ] fW jW kbar 0).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  have hz := Functor.map_isZero (compactSupportSheafCohomology ℤ_[ℓ] fW jW kbar 0) h1
  exact hz.of_iso e.symm

end Leray

section Laumon

variable (k' : Type u) [Field k'] [Fintype k'] (B : BigEtaleSite.{u})
  (hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k')))))
  (hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k'))))

/-- **`pr₁ : Spec k'[x][t] → Spec k'[x]`**, as a morphism of the big étale site. -/
public abbrev laumonFamilyFirstProjection :
    Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS ⟶
      Stacks.ArtinSchreier.specObject (Polynomial k') B hL :=
  ObjectProperty.homMk (laumonFamilyPr₁ k')

/-- The first projection `pr₁ : 𝔸² → 𝔸¹_x` is locally of finite type. -/
public instance locallyOfFiniteType_laumonFamilyFirstProjection :
    LocallyOfFiniteType (B.inclusion.map (laumonFamilyFirstProjection k' B hS hL)) := by
  change LocallyOfFiniteType (laumonFamilyPr₁ k')
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  rw [CommRingCat.hom_ofHom]
  let : Algebra (Polynomial k') (Polynomial (Polynomial k')) := Polynomial.algebraOfAlgebra
  exact RingHom.finiteType_algebraMap.2 inferInstance

/-- The first projection `pr₁ : 𝔸² → 𝔸¹_x` is quasi-compact. -/
public instance quasiCompact_laumonFamilyFirstProjection :
    QuasiCompact (B.inclusion.map (laumonFamilyFirstProjection k' B hS hL)) :=
  inferInstanceAs (QuasiCompact (laumonFamilyPr₁ k'))

/-- The first projection `pr₁ : 𝔸² → 𝔸¹_x` is separated. -/
public instance isSeparated_laumonFamilyFirstProjection :
    IsSeparated (B.inclusion.map (laumonFamilyFirstProjection k' B hS hL)) :=
  inferInstanceAs (IsSeparated (laumonFamilyPr₁ k'))

omit [Fintype k'] in
/-- **Both projections of the plane lie over `Spec k'`**: `pr₁` and `pr₂` followed by the structure
morphism of the line are the structure morphism of `Spec k'[x][t]`. -/
public theorem laumonFamilyFirstProjection_comp_laumonLineStructure :
    B.inclusion.map (laumonFamilyFirstProjection k' B hS hL) ≫ laumonLineStructure k' B hL =
      B.inclusion.map (laumonFamilyProjection k' B hS hL) ≫ laumonLineStructure k' B hL :=
  (isPullback_laumonFamilyPr₁_laumonFamilyProjection k' B hS hL).w

end Laumon

section LaumonSheaf

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

/-- **`R⁰pr₁! K'₀ = 0`** for the bottom level `K'₀` of the flat model of Laumon's family sheaf
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)): `pr₁` is the affine line over the
`x`-line and `K'₀` is locally constant of finite type and killed by `ℓ`
(`Stacks.EtaleCohomology.isZero_lowerShriekHomology_zero_of_isPullback_affineLine`). -/
theorem isZero_lowerShriekHomology_zero_laumonFamilySheaf_flatModel_firstProjection
    (σ₁ : EtaleFundamentalGroup (Spec (.of (Polynomial k'))) (z.map (laumonFamilyPr₁ k')) →*
      GL (Fin m) E) (hσ₁ : Continuous (restrictScalarsRep b σ₁))
    (jg₁ : CompactificationOf
      (Over.mk (B.inclusion.map (laumonFamilyFirstProjection k' B hS hL)))) :
    haveI : IsNoetherian (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS).1 :=
      inferInstanceAs (IsNoetherian (Spec (.of (Polynomial (Polynomial k')))))
    IsZero ((lowerShriekHomology ℤ_[ℓ] (B.inclusion.map (laumonFamilyFirstProjection k' B hS hL))
        jg₁ 0).obj
      (towerObj (LAdicSheaf.padicTower B _ ℓ (LAdicSheaf.flatModel B ℓ
        (laumonFamilySheaf k' B hS b ψ' n₀ c z p₀ σ₁ hσ₁).toLAdicSheaf)) 0)) := by
  have : IsNoetherian (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS).1 :=
    inferInstanceAs (IsNoetherian (Spec (.of (Polynomial (Polynomial k')))))
  let X := Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS
  let K := (laumonFamilySheaf k' B hS b ψ' n₀ c z p₀ σ₁ hσ₁).toLAdicSheaf
  have sq : IsPullback (B.inclusion.map (laumonFamilyProjection k' B hS hL))
      (B.inclusion.map (laumonFamilyFirstProjection k' B hS hL))
      (affineLineStructureMap k') (affineLineStructureMap k') :=
    (isPullback_laumonFamilyPr₁_laumonFamilyProjection k' B hS hL).flip
  exact isZero_lowerShriekHomology_zero_of_isPullback_affineLine k' ℤ_[ℓ] sq jg₁ _ (ℓ ^ (0 + 1))
    (pow_pos (Fact.out : ℓ.Prime).pos _) (LAdicSheaf.padicTower_annihilated B X ℓ _ 0)
    (LAdicSheaf.isFiniteTypeLocallyConstant_padicTower_of_isLisse B X ℓ _
      (LAdicSheaf.isLisse_flatModel B ℓ K (LAdicSheaf.representationSheaf_isLisse B X z _ _)) 0)

end LaumonSheaf

/-- **`R¹pr₁! K'₀ = 0` for `ℓ ≠ char k'`** ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)):
for the bottom level `K'₀` of the flat model of the family sheaf
`K = pr₁^*ℱ_{σ₁} ⊗ L_ψ'(t h(x))` on `Spec k'[x][t]` (`h = xⁿ⁰ + c x ≠ 0`, `ψ'` nontrivial) and the
first projection `pr₁ : 𝔸² → 𝔸¹_x`, read as a sheaf of `ℤ_ℓ`-modules on Mathlib's small étale site,
`R¹pr₁! K'₀ = 0`: on the geometric fibre over `x̄`, the `t`-line, `K'₀` is `M ⊗ L_ψ'(h(x̄) t)`,
constant when `h(x̄) = 0` (no `H¹_c` on the affine line) and a nontrivial Artin–Schreier sheaf
otherwise (no `Hⁱ_c` at all, `p` being invertible in the coefficients). -/
public def LaumonFamilyFirstProjectionVanishingInput' : Prop :=
  ∀ (B : BigEtaleSite.{u}) (ℓ : ℕ)
    [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] [Fact ℓ.Prime]
    (k' : Type u) [Field k'] [Fintype k']
    (_ : ringChar k' ≠ ℓ)
    (hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k')))))
    (hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k'))))
    {E : Type} [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ_[ℓ] E) (ψ' : AddChar k' E) (_ : ψ' ≠ 1) (n₀ : ℕ) (c : k')
    (_ : (Polynomial.X ^ n₀ + Polynomial.C c * Polynomial.X : Polynomial k') ≠ 0)
    (z : GeometricPoint (Spec (.of (Polynomial (Polynomial k')))))
    (p₀ : (finiteEtaleFiberFunctor z).obj
      (Stacks.ArtinSchreier.cover k' (Polynomial (Polynomial k')) (laumonKernel k' n₀ c))) {m : ℕ}
    (σ₁ : EtaleFundamentalGroup (Spec (.of (Polynomial k'))) (z.map (laumonFamilyPr₁ k')) →*
      GL (Fin m) E) (hσ₁ : Continuous (restrictScalarsRep b σ₁))
    (jg₁ : CompactificationOf (Over.mk (B.inclusion.map (laumonFamilyFirstProjection k' B hS hL)))),
    haveI : IsNoetherian (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS).1 :=
      inferInstanceAs (IsNoetherian (Spec (.of (Polynomial (Polynomial k')))))
    IsZero ((lowerShriekHomology ℤ_[ℓ] (B.inclusion.map (laumonFamilyFirstProjection k' B hS hL))
        jg₁ 1).obj
      (towerObj (LAdicSheaf.padicTower B _ ℓ (LAdicSheaf.flatModel B ℓ
        (laumonFamilySheaf k' B hS b ψ' n₀ c z p₀ σ₁ hσ₁).toLAdicSheaf)) 0))

/-- **The vanishing on the bottom flat level from `R¹pr₁! K'₀ = 0`, for `ℓ ≠ char k'`**
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)): `R⁰pr₂! K'₀ = 0`
(`Stacks.EtaleCohomology.isZero_lowerShriekHomology_zero_laumonFamilySheaf_flatModel`), and
`H¹_c(𝔸²_k̄, K'₀) = 0` by the Leray edge along `pr₁`, `R⁰pr₁! K'₀` and `R¹pr₁! K'₀` vanishing. -/
public theorem laumonFamilyFlatLevelZeroVanishingInput'_of_firstProjection
    (h : LaumonFamilyFirstProjectionVanishingInput'.{u}) :
    LaumonFamilyFlatLevelZeroVanishingInput'.{u} := by
  intro B ℓ _ _ _ _ k' _ _ hℓ hS hL E _ _ _ d b ψ' hψ' n₀ c hh z p₀ m σ₁ hσ₁ jg
  have : IsNoetherian (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS).1 :=
    inferInstanceAs (IsNoetherian (Spec (.of (Polynomial (Polynomial k')))))
  have : IsNoetherian (Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1 :=
    inferInstanceAs (IsNoetherian (Spec (.of (Polynomial k'))))
  refine ⟨isZero_lowerShriekHomology_zero_laumonFamilySheaf_flatModel k' B hS hL b ψ' n₀ c z p₀
    σ₁ hσ₁ jg, fun kbar _ _ _ jU => ?_⟩
  have : CompactSpace (Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1 :=
    inferInstanceAs (CompactSpace (Spec (.of (Polynomial k'))))
  have : QuasiSeparatedSpace (Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1 :=
    inferInstanceAs (QuasiSeparatedSpace (Spec (.of (Polynomial k'))))
  have hcof := @isCofiltered_compactificationOf _ _
    (B.inclusion.map (laumonFamilyFirstProjection k' B hS hL))
    (inferInstanceAs (CompactSpace (Spec (.of (Polynomial k')))))
    (inferInstanceAs (QuasiSeparatedSpace (Spec (.of (Polynomial k'))))) inferInstance
    inferInstance inferInstance
  obtain ⟨jg₁⟩ : Nonempty (CompactificationOf
      (Over.mk (B.inclusion.map (laumonFamilyFirstProjection k' B hS hL)))) := IsCofiltered.nonempty
  have : QuasiCompact (laumonLineStructure k' B hL) := inferInstanceAs (QuasiCompact
    (Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k')))))
  have : IsSeparated (laumonLineStructure k' B hL) := inferInstanceAs (IsSeparated
    (Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k')))))
  let K : (IsLPowerTorsion ℓ
      (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS).1).FullSubcategory :=
    ⟨towerObj (LAdicSheaf.padicTower B _ ℓ (LAdicSheaf.flatModel B ℓ
      (laumonFamilySheaf k' B hS b ψ' n₀ c z p₀ σ₁ hσ₁).toLAdicSheaf)) 0,
      ⟨0 + 1, LAdicSheaf.padicTower_annihilated B _ ℓ _ 0⟩⟩
  exact isZero_compactSupportSheafCohomology_one_of_lowerShriekHomology B ℓ
    (laumonFamilyFirstProjection k' B hS hL) jg₁ (laumonLineStructure k' B hL) kbar K
    (isZero_lowerShriekHomology_zero_laumonFamilySheaf_flatModel_firstProjection k' B hS hL b ψ' n₀
      c z p₀ σ₁ hσ₁ jg₁)
    (h B ℓ k' hℓ hS hL b ψ' hψ' n₀ c hh z p₀ σ₁ hσ₁ jg₁) _
    (laumonFamilyFirstProjection_comp_laumonLineStructure k' B hS hL) jU

/-- **(H2) from `R¹pr₁! K'₀ = 0`, for `ℓ ≠ char k'`**
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)). -/
public theorem laumonFamilyNoPunctualSectionsInput'_of_firstProjection
    (h : LaumonFamilyFirstProjectionVanishingInput'.{u}) :
    LaumonFamilyNoPunctualSectionsInput'.{u} :=
  laumonFamilyNoPunctualSectionsInput'_of_levelZero'
    (laumonFamilyFlatLevelZeroVanishingInput'_of_firstProjection h)

end Stacks.EtaleCohomology

end
