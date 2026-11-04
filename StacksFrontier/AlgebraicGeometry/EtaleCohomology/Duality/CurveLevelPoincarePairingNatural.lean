module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveLevelPoincarePairing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportExtNaturality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTopCohomologyTransition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicTwistedTower

/-!
# The finite-level Poincaré pairing on a curve, natural in the coefficients

Let `X` be a `k`-scheme over a finite field with `p ^ q` elements, `j : X ⟶ X̄` a compactification
over `k`, `k̄` an extension of `k`, `Y = X̄_k̄` and `pr : Y ⟶ X̄` the projection. For an ℓ-adic
sheaf `F` on `X` and `N = ℓⁿ⁺¹`, the level `n` of `Hⁱ_c(X_k̄, F)` is identified with
`Ext^i_{ℤ/N}(ℤ/N_Y, pr^{-1}(j_! Fₙ))` by an explicit isomorphism
(`Stacks.EtaleCohomology.LAdicSheaf.levelExtEquiv`), the composite of the comparison of the
`ℤ_ℓ`-level with the `ℤ/N`-level, of the comparison of `Hⁱ_c` with restriction of scalars, and of
`Hⁱ_c(X_k̄, K) ≅ Ext^i(ℤ/N, (j_! K)|_Y)`. It carries the canonical geometric Frobenius to
`b ↦ θ(b ∘ τ)` (`Stacks.EtaleCohomology.LAdicSheaf.levelExtEquiv_frobenius`), and, unlike the
isomorphism chosen in `Stacks.EtaleCohomology.LAdicSheaf.exists_addEquiv_level_frobenius`, it is
natural in `F`: a morphism `φ : F ⟶ G` acts on the `Ext` side by composition with
`pr^{-1}(j_! φₙ)` (`Stacks.EtaleCohomology.LAdicSheaf.levelExtEquiv_naturality`).

With it, the cup product pairing
`εₙ(x, y) = t(x ∪_{μₙ} y) : H¹_c(X_k̄, Fₙ) × H¹_c(X_k̄, F'ₙ) → H²(Y, ℤ/N) → ℤ/N`
attached to pairings `μₙ : j_! Fₙ ⊗ j_! F'ₙ ⟶ ℤ/N` and a trace `t` is a definition
(`Stacks.EtaleCohomology.LAdicSheaf.curveLevelPairing`). On a curve it has bounded defect and is
scaled by `q` under Frobenius (`Stacks.EtaleCohomology.LAdicSheaf.curveLevelPairing_bounds`, the
finite-level Poincaré duality of `Stacks.EtaleCohomology.LAdicSheaf.exists_levelPairing_of_curve`
for this pairing), and morphisms of coefficients compatible with the pairings are adjoint for it
(`Stacks.EtaleCohomology.LAdicSheaf.curveLevelPairing_map`): if
`μ₂ ∘ (j_! φₙ ⊗ 1) = μ₁ ∘ (1 ⊗ j_! φ'ₙ)` then `ε₂(φ_* x, y) = ε₁(x, φ'_* y)`. This is the
adjointness of the intertwiners of a representation and of its contragredient used in Poincaré
duality on an affine curve, in the purity half of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main definitions

* `Stacks.EtaleCohomology.LAdicSheaf.levelExtEquiv`.
* `Stacks.EtaleCohomology.LAdicSheaf.curveLevelPairing`.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.levelExtEquiv_frobenius`.
* `Stacks.EtaleCohomology.LAdicSheaf.levelExtEquiv_naturality`.
* `Stacks.EtaleCohomology.exists_injective_levelTrace_of_curve`.
* `Stacks.EtaleCohomology.LAdicSheaf.curveLevelPairing_bounds`.
* `Stacks.EtaleCohomology.LAdicSheaf.curveLevelPairing_map`.

The statements consume objects defined in the standard model `HasDerivedCategory.standard` of the
derived category (the ℓ-adic compactly supported cohomology), which is therefore a local instance
here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  Sheaf.monoidalCategory
  etaleModuleInverseImageSheafPullbackMonoidal etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits
  etaleModuleDirectImage_preservesFiniteColimits_of_universalHomeomorphism

attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

/-- The morphisms inverted by sheafification form a monoidal class of étale module sheaves. -/
local instance isMonoidal_W_etaleModules_curveLevelPairingNatural (Λ : Type) [CommRing Λ]
    (S : Scheme.{u}) : (S.smallEtaleTopology.W (A := ModuleCat.{u + 1} Λ)).IsMonoidal :=
  isMonoidal_W_etaleModules (Λ := Λ) S

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1] [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar]

/-! ### The levels of `Hⁱ_c` as `Ext` groups, naturally -/

section LevelExt

/-- The level `Fₙ → Gₙ` of a morphism of ℓ-adic sheaves, read on Mathlib's small étale site. -/
abbrev LAdicSheaf.etaleLevelMap {F G : LAdicSheaf B X ℓ} (φ : F ⟶ G) (n : ℕ) :
    LAdicSheaf.etaleLevel B X ℓ F n ⟶ LAdicSheaf.etaleLevel B X ℓ G n :=
  (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).functor.map
    (φ.app n)

/-- **The level `n` of `Hⁱ_c(X_k̄, F)` is `Ext^i(ℤ/N_Y, pr^{-1}(j_! Fₙ))`**, `N = ℓⁿ⁺¹`,
`Y = X̄_k̄`: the comparison of the `ℤ_ℓ`-level with the `ℤ/N`-level complex, of `Hⁱ_c` with
restriction of scalars, and `Hⁱ_c(X_k̄, K) ≅ Ext^i(ℤ/N, (j_! K)|_Y)`. -/
def LAdicSheaf.levelExtEquiv (F : LAdicSheaf B X ℓ) (i n : ℕ) :
    (geometricCompactSupportPadicCohomology B X ℓ f j kbar i).obj
        (LAdicSheaf.padicLevel B X ℓ F n) ≃+
      Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChange (Over.mk j.toBase) kbar)))
        ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
          ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
            (LAdicSheaf.etaleLevel B X ℓ F n))) i :=
  (((compactSupportFrobeniusFunctor.{u, 0} ℤ_[ℓ] f j kbar ⋙
      DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ_[ℓ]) (i : ℤ)).mapIso
        (LAdicSheaf.padicCoefficientComplexLevelIso B X ℓ F n)).toLinearEquiv.toAddEquiv.trans
    (compactSupportFrobeniusCohomologyGroupRestrictScalarsIso (PadicInt.toZModPow (n + 1)) f j kbar
      (LAdicSheaf.levelComplex B X ℓ F n) (i : ℤ)).symm.toLinearEquiv.toAddEquiv).trans
    (compactSupportFrobeniusSingleIsoExt (ZMod (ℓ ^ (n + 1))) f j kbar
      (LAdicSheaf.etaleLevel B X ℓ F n) i).addCommGroupIsoToAddEquiv

omit [Fintype k] [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- **`LAdicSheaf.levelExtEquiv` is natural in the ℓ-adic sheaf**: a morphism `φ : F ⟶ G` acts on
the `Ext` side by composition with `pr^{-1}(j_! φₙ)`. -/
theorem LAdicSheaf.levelExtEquiv_naturality [Finite k] {F G : LAdicSheaf B X ℓ} (φ : F ⟶ G)
    (i n : ℕ) (x : (geometricCompactSupportPadicCohomology B X ℓ f j kbar i).obj
      (LAdicSheaf.padicLevel B X ℓ F n)) :
    LAdicSheaf.levelExtEquiv B X ℓ f j kbar G i n
        ((geometricCompactSupportPadicCohomology B X ℓ f j kbar i).map
          (LAdicSheaf.padicLevelMap φ n) x) =
      (LAdicSheaf.levelExtEquiv B X ℓ f j kbar F i n x).comp
        (Ext.mk₀ ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChangeProj (Over.mk j.toBase) kbar)).map
          ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).map
            (LAdicSheaf.etaleLevelMap B X ℓ φ n)))) (add_zero i) := by
  have := Fintype.ofFinite k
  let H := compactSupportFrobeniusFunctor.{u, 0} ℤ_[ℓ] f j kbar ⋙
    DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ_[ℓ]) (i : ℤ)
  have h₁ := LAdicSheaf.padicCoefficientComplexLevelIso_hom_naturality φ n
  have h₁' := (H.map_comp _ _).symm.trans ((congrArg H.map h₁).trans (H.map_comp _ _))
  have h₂ := compactSupportFrobeniusCohomologyGroupRestrictScalarsIso_naturality
    (PadicInt.toZModPow (n + 1)) f j kbar (LAdicSheaf.levelComplexMap φ n) (i : ℤ)
  have h₂' : (compactSupportFrobeniusCohomologyGroupRestrictScalarsIso (PadicInt.toZModPow (n + 1))
        f j kbar (LAdicSheaf.levelComplex B X ℓ F n) (i : ℤ)).inv ≫
      (ModuleCat.restrictScalars.{u + 1} (PadicInt.toZModPow (n + 1))).map
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) (i : ℤ)).map
          ((compactSupportFrobeniusFunctor.{u, 0} _ f j kbar).map
            (LAdicSheaf.levelComplexMap φ n))) =
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ_[ℓ]) (i : ℤ)).map
          ((compactSupportFrobeniusFunctor.{u, 0} ℤ_[ℓ] f j kbar).map
            ((etaleModuleRestrictScalars (PadicInt.toZModPow (n + 1)) X.1).mapCochainComplexPlus.map
              (LAdicSheaf.levelComplexMap φ n))) ≫
        (compactSupportFrobeniusCohomologyGroupRestrictScalarsIso (PadicInt.toZModPow (n + 1))
          f j kbar (LAdicSheaf.levelComplex B X ℓ G n) (i : ℤ)).inv :=
    (Iso.inv_comp_eq _).2 (((Iso.eq_comp_inv _).2 h₂).trans (Category.assoc _ _ _))
  have h₃ := compactSupportFrobeniusSingleIsoExt_hom_naturality (ZMod (ℓ ^ (n + 1))) f kbar j
    (LAdicSheaf.etaleLevelMap B X ℓ φ n) i
  let C := compactSupportFrobeniusFunctor.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
  let Hz := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) (i : ℤ)
  let res := etaleModuleRestrictScalars (PadicInt.toZModPow (p := ℓ) (n + 1)) X.1
  let e₁ := fun (F : LAdicSheaf B X ℓ) => H.mapIso
    (LAdicSheaf.padicCoefficientComplexLevelIso B X ℓ F n)
  let e₂ := fun (F : LAdicSheaf B X ℓ) => compactSupportFrobeniusCohomologyGroupRestrictScalarsIso
    (PadicInt.toZModPow (n + 1)) f j kbar (LAdicSheaf.levelComplex B X ℓ F n) (i : ℤ)
  let e₃ := fun (F : LAdicSheaf B X ℓ) => compactSupportFrobeniusSingleIsoExt (ZMod (ℓ ^ (n + 1)))
    f j kbar (LAdicSheaf.etaleLevel B X ℓ F n) i
  have s₁ : (e₁ G).hom.hom ((H.map ((padicCoefficientComplex B X ℓ).map
      (LAdicSheaf.padicLevelMap φ n))).hom x) =
      (H.map (res.mapCochainComplexPlus.map (LAdicSheaf.levelComplexMap φ n))).hom
        ((e₁ F).hom.hom x) :=
    congrArg (fun g => g.hom x) h₁'
  have s₂ : ∀ z, (e₂ G).inv.hom ((H.map (res.mapCochainComplexPlus.map
      (LAdicSheaf.levelComplexMap φ n))).hom z) =
      (Hz.map (C.map (LAdicSheaf.levelComplexMap φ n))).hom ((e₂ F).inv.hom z) :=
    fun z => (congrArg (fun g => g.hom z) h₂').symm
  have s₃ : ∀ z, (e₃ G).hom.hom ((Hz.map (C.map (LAdicSheaf.levelComplexMap φ n))).hom z) =
      ((e₃ F).hom.hom z).comp (Ext.mk₀ ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChangeProj (Over.mk j.toBase) kbar)).map
          ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).map
            (LAdicSheaf.etaleLevelMap B X ℓ φ n)))) (add_zero i) :=
    fun z => congrArg (fun g => g.hom z) h₃
  show (e₃ G).hom.hom ((e₂ G).inv.hom ((e₁ G).hom.hom ((H.map ((padicCoefficientComplex B X ℓ).map
      (LAdicSheaf.padicLevelMap φ n))).hom x))) = ((e₃ F).hom.hom ((e₂ F).inv.hom
        ((e₁ F).hom.hom x))).comp _ (add_zero i)
  rw [s₁, s₂]
  exact s₃ _

variable (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

omit [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- **`LAdicSheaf.levelExtEquiv` carries the canonical geometric Frobenius `π_X^*` to
`b ↦ θ(b ∘ τ)`**, with `τ : pr^{-1}(j_! Fₙ) ⟶ π̄_* pr^{-1}(j_! Fₙ)` the base change of the
Frobenius descent isomorphism and `θ` the `Ext` map of `π̄^{-1} ⊣ π̄_*`. -/
theorem LAdicSheaf.levelExtEquiv_frobenius (F : LAdicSheaf B X ℓ) (i n : ℕ)
    (x : (geometricCompactSupportPadicCohomology B X ℓ f j kbar i).obj
      (LAdicSheaf.padicLevel B X ℓ F n)) :
    LAdicSheaf.levelExtEquiv B X ℓ f j kbar F i n
        ((canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f j kbar p q hcard
          ((padicCoefficientComplex B X ℓ).obj (LAdicSheaf.padicLevel B X ℓ F n)) i).hom x) =
      Stacks.ExtCup.adjunctionExtMap
        (etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard))
        (etaleModuleDirectImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard))
        (etaleModuleInverseImageAdj.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard))
        ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
          ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
            (LAdicSheaf.etaleLevel B X ℓ F n)))
        ((LAdicSheaf.levelExtEquiv B X ℓ f j kbar F i n x).comp
          (Ext.mk₀ ((frobeniusBaseChangeTwist.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (Over.mk j.toBase) kbar p q hcard).app
            ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
              (LAdicSheaf.etaleLevel B X ℓ F n)))) (add_zero i)) := by
  let ρ := PadicInt.toZModPow (p := ℓ) (n + 1)
  let H := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ_[ℓ]) (i : ℤ)
  let C := compactSupportFrobeniusFunctor.{u, 0} ℤ_[ℓ] f j kbar
  let Fr := canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] f j kbar p q hcard
  let lv := LAdicSheaf.padicCoefficientComplexLevelIso B X ℓ F n
  let e₁ := (C ⋙ H).mapIso lv
  let e₂ := (compactSupportFrobeniusCohomologyGroupRestrictScalarsIso ρ f j kbar
    (LAdicSheaf.levelComplex B X ℓ F n) (i : ℤ)).symm
  let K := LAdicSheaf.etaleLevel B X ℓ F n
  let e₃ := (compactSupportFrobeniusSingleIsoExt (ZMod (ℓ ^ (n + 1))) f j kbar K
    i).addCommGroupIsoToAddEquiv
  have h₁ : e₁.hom.hom ((canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f j kbar p q hcard
      ((padicCoefficientComplex B X ℓ).obj (LAdicSheaf.padicLevel B X ℓ F n)) i).hom x) =
      (canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f j kbar p q hcard
        ((etaleModuleRestrictScalars ρ X.1).mapCochainComplexPlus.obj
          (LAdicSheaf.levelComplex B X ℓ F n)) i).hom (e₁.hom.hom x) := by
    have := congrArg H.map (Fr.naturality lv.hom)
    simp only [Functor.map_comp] at this
    exact (congrArg (fun g => g.hom x) this).symm
  have h₂ := restrictScalars_canonicalCompactSupportFrobeniusGroup ρ f j kbar p q hcard
    (LAdicSheaf.levelComplex B X ℓ F n) (i : ℤ)
  have h₂' : ∀ z, e₂.hom.hom ((canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f j kbar p q hcard
      ((etaleModuleRestrictScalars ρ X.1).mapCochainComplexPlus.obj
        (LAdicSheaf.levelComplex B X ℓ F n)) i).hom z) =
      (canonicalCompactSupportFrobeniusGroup.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar p q hcard
        (LAdicSheaf.levelComplex B X ℓ F n) i).hom (e₂.hom.hom z) := by
    intro z
    have hh : (compactSupportFrobeniusCohomologyGroupRestrictScalarsIso ρ f j kbar
          (LAdicSheaf.levelComplex B X ℓ F n) (i : ℤ)).inv ≫
        (ModuleCat.restrictScalars.{u + 1} ρ).map
          (canonicalCompactSupportFrobeniusGroup.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar p q hcard
            (LAdicSheaf.levelComplex B X ℓ F n) i) =
        canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f j kbar p q hcard
          ((etaleModuleRestrictScalars ρ X.1).mapCochainComplexPlus.obj
            (LAdicSheaf.levelComplex B X ℓ F n)) i ≫
        (compactSupportFrobeniusCohomologyGroupRestrictScalarsIso ρ f j kbar
          (LAdicSheaf.levelComplex B X ℓ F n) (i : ℤ)).inv := by
      rw [Iso.inv_comp_eq, ← Category.assoc, ← h₂, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
    exact (congrArg (fun g => g.hom z) hh).symm
  set y := e₂.hom.hom (e₁.hom.hom x)
  have h₃ := compactSupportFrobeniusSingleIsoExt_canonical_apply (ZMod (ℓ ^ (n + 1))) f j kbar p q
    hcard K i (e₃ y)
  have hB : ((compactSupportFrobeniusSingleIsoExt (ZMod (ℓ ^ (n + 1))) f j kbar K i).inv).hom
      (e₃ y) = y := e₃.symm_apply_apply y
  rw [hB] at h₃
  show e₃ (e₂.hom.hom (e₁.hom.hom _)) = _
  rw [h₁]
  exact (congrArg (fun z => e₃ z) (h₂' (e₁.hom.hom x))).trans h₃

end LevelExt

/-! ### The cup product pairing of the levels -/

section Pairing

variable {S T : Scheme.{u}} (g : T ⟶ S) (N : ℕ)

/-- **Pulled back pairings respect compatible morphisms**: if `μ₂ ∘ (a ⊗ 1) = μ₁ ∘ (1 ⊗ b)` then
the same holds for the pairings pulled back along `g`. -/
theorem whiskerRight_inverseImageConstantPairing {K₁ K₂ K₁' K₂' : EtaleModules.{u, 0} (ZMod N) S}
    (a : K₁ ⟶ K₂) (b : K₂' ⟶ K₁')
    (μ₁ : K₁ ⊗ K₁' ⟶ Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N)
      S.smallEtaleTopology)
    (μ₂ : K₂ ⊗ K₂' ⟶ Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N)
      S.smallEtaleTopology) (h : a ▷ K₂' ≫ μ₂ = K₁ ◁ b ≫ μ₁) :
    (etaleModuleInverseImage.{u, 0} (ZMod N) g).map a ▷
        (etaleModuleInverseImage.{u, 0} (ZMod N) g).obj K₂' ≫
        inverseImageConstantPairing g N μ₂ =
      (etaleModuleInverseImage.{u, 0} (ZMod N) g).obj K₁ ◁
        (etaleModuleInverseImage.{u, 0} (ZMod N) g).map b ≫ inverseImageConstantPairing g N μ₁ := by
  have hl := Functor.LaxMonoidal.μ_natural_left (etaleModuleInverseImage.{u, 0} (ZMod N) g) a K₂'
  have hr := Functor.LaxMonoidal.μ_natural_right (etaleModuleInverseImage.{u, 0} (ZMod N) g) K₁ b
  simp only [inverseImageConstantPairing]
  rw [reassoc_of% hl, reassoc_of% hr, ← Functor.map_comp_assoc, h, Functor.map_comp_assoc]

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1] [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- The base change of a proper morphism along any morphism is proper. -/
private theorem isProper_pullback_snd_of_isProper {A C D : Scheme.{u}} (g : A ⟶ D) (h : C ⟶ D)
    (hg : IsProper g) : IsProper (pullback.snd g h) :=
  MorphismProperty.of_isPullback (P := @IsProper) (IsPullback.of_hasPullback g h) hg

omit [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [AlgebraicGeometry.IsNoetherian X.1] [Fintype k] [LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated f] in
/-- **An injective trace on `H²(X̄_k̄, ℤ/ℓⁿ⁺¹)` at every level**, when `X̄_k̄` is a smooth proper
curve over the algebraically closed field `k̄` in which `ℓ` is invertible. -/
theorem exists_injective_curveLevelTrace [IsAlgClosed kbar]
    [IsCurve kbar (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))]
    [Smooth (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))]
    (hℓ : IsUnit (ℓ : kbar)) :
    ∃ t : ∀ n : ℕ, Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (fieldBaseChange (Over.mk j.toBase) kbar)))
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology) 2 →+ ZMod (ℓ ^ (n + 1)),
      ∀ n, Function.Injective (t n) := by
  have : IsProper (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)) :=
    isProper_pullback_snd_of_isProper _ _ (inferInstanceAs (IsProper j.toBase))
  choose t₀ ht₀ using fun n => exists_injective_trace_zmodPow_of_curve
    (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)) hℓ (ℓ := ℓ) (n + 1)
  exact ⟨t₀, ht₀⟩

/-- **The cup product pairing of the levels of `H¹_c(X_k̄, F)` and `H¹_c(X_k̄, F')`**: for pairings
`μₙ : j_! Fₙ ⊗ j_! F'ₙ ⟶ ℤ/N` on `X̄`, `N = ℓⁿ⁺¹`, and traces `tₙ` on `H²(X̄_k̄, ℤ/N)`,
`εₙ(x, y) = tₙ(Φ x ∪_{μₙ} Φ' y)`, with `Φ`, `Φ'` the natural identifications
`LAdicSheaf.levelExtEquiv` and the cup product along the pullback of `μₙ` to `Y = X̄_k̄`. The
flatness of the fibres of `G = (j_! F'ₙ)|_Y` makes `- ⊗ G` exact, on which the cup product is
defined. -/
def LAdicSheaf.curveLevelPairing
    (t : ∀ n : ℕ, Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (fieldBaseChange (Over.mk j.toBase) kbar)))
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology) 2 →+ ZMod (ℓ ^ (n + 1)))
    (F F' : LAdicSheaf B X ℓ)
    (μ : ∀ n, (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
        (LAdicSheaf.etaleLevel B X ℓ F n) ⊗
      (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
        (LAdicSheaf.etaleLevel B X ℓ F' n) ⟶
      Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
        j.space.smallEtaleTopology)
    (hflat : ∀ (n : ℕ) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (s : Spec (.of Ω) ⟶ fieldBaseChange (Over.mk j.toBase) kbar),
      Module.Flat (ZMod (ℓ ^ (n + 1)))
        ((((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
          (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
            ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
              (LAdicSheaf.etaleLevel B X ℓ F' n)))))
    (n : ℕ) :
    (geometricCompactSupportPadicCohomology B X ℓ f j kbar 1).obj
        (LAdicSheaf.padicLevel B X ℓ F n) →+
      (geometricCompactSupportPadicCohomology B X ℓ f j kbar 1).obj
        (LAdicSheaf.padicLevel B X ℓ F' n) →+ ZMod (ℓ ^ (n + 1)) :=
  haveI := (tensorRight_exact_of_flat _ (hflat n)).1
  haveI := (tensorRight_exact_of_flat _ (hflat n)).2.1
  haveI := (tensorRight_exact_of_flat _ (hflat n)).2.2
  AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y =>
      t n (Stacks.ExtCup.cup.{u + 1, _, _}
        (inverseImageConstantPairing (fieldBaseChangeProj (Over.mk j.toBase) kbar) (ℓ ^ (n + 1))
          (μ n))
        (LAdicSheaf.levelExtEquiv B X ℓ f j kbar F 1 n x)
        (LAdicSheaf.levelExtEquiv B X ℓ f j kbar F' 1 n y) (show 1 + 1 = 2 from rfl)))
      (fun y y' => by rw [map_add, Stacks.ExtCup.cup_add, map_add]))
    (fun x x' => by
      ext y
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add,
        Stacks.ExtCup.add_cup])

omit [Fintype k] [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- **Morphisms of coefficients compatible with the pairings are adjoint for the level
pairings.** For `φ : F₁ ⟶ F₂` and `φ' : F₂' ⟶ F₁'` with `μ₂ₙ ∘ (j_! φₙ ⊗ 1) = μ₁ₙ ∘ (1 ⊗ j_! φ'ₙ)`
on `X̄`, the induced maps on `H¹_c(X_k̄, -)` satisfy `ε₂(φ_* x, y) = ε₁(x, φ'_* y)`, for any traces
`t`. This is the cup product naturality, through the naturality of `LAdicSheaf.levelExtEquiv`. -/
theorem LAdicSheaf.curveLevelPairing_map [Finite k]
    (t : ∀ n : ℕ, Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (fieldBaseChange (Over.mk j.toBase) kbar)))
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology) 2 →+ ZMod (ℓ ^ (n + 1)))
    {F₁ F₂ F₁' F₂' : LAdicSheaf B X ℓ} (φ : F₁ ⟶ F₂) (φ' : F₂' ⟶ F₁')
    (μ₁ : ∀ n, (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
      (LAdicSheaf.etaleLevel B X ℓ F₁ n) ⊗
      (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
        (LAdicSheaf.etaleLevel B X ℓ F₁' n) ⟶
      Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
        j.space.smallEtaleTopology)
    (μ₂ : ∀ n, (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
      (LAdicSheaf.etaleLevel B X ℓ F₂ n) ⊗
      (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
        (LAdicSheaf.etaleLevel B X ℓ F₂' n) ⟶
      Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
        j.space.smallEtaleTopology)
    (hflat₁ : ∀ (n : ℕ) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (s : Spec (.of Ω) ⟶ fieldBaseChange (Over.mk j.toBase) kbar),
      Module.Flat (ZMod (ℓ ^ (n + 1)))
        ((((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
          (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
            ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
              (LAdicSheaf.etaleLevel B X ℓ F₁' n)))))
    (hflat₂ : ∀ (n : ℕ) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (s : Spec (.of Ω) ⟶ fieldBaseChange (Over.mk j.toBase) kbar),
      Module.Flat (ZMod (ℓ ^ (n + 1)))
        ((((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
          (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
            ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
              (LAdicSheaf.etaleLevel B X ℓ F₂' n)))))
    (h : ∀ n, (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).map
      (LAdicSheaf.etaleLevelMap B X ℓ φ n) ▷
        (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
          (LAdicSheaf.etaleLevel B X ℓ F₂' n) ≫ μ₂ n =
      (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
        (LAdicSheaf.etaleLevel B X ℓ F₁ n) ◁
        (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).map
          (LAdicSheaf.etaleLevelMap B X ℓ φ' n) ≫ μ₁ n)
    (n : ℕ) (x : (geometricCompactSupportPadicCohomology B X ℓ f j kbar 1).obj
      (LAdicSheaf.padicLevel B X ℓ F₁ n))
    (y : (geometricCompactSupportPadicCohomology B X ℓ f j kbar 1).obj
      (LAdicSheaf.padicLevel B X ℓ F₂' n)) :
    LAdicSheaf.curveLevelPairing B X ℓ f j kbar t F₂ F₂' μ₂ hflat₂ n
        ((geometricCompactSupportPadicCohomology B X ℓ f j kbar 1).map
          (LAdicSheaf.padicLevelMap φ n) x) y =
      LAdicSheaf.curveLevelPairing B X ℓ f j kbar t F₁ F₁' μ₁ hflat₁ n x
        ((geometricCompactSupportPadicCohomology B X ℓ f j kbar 1).map
          (LAdicSheaf.padicLevelMap φ' n) y) := by
  have := Fintype.ofFinite k
  obtain ⟨_, _, _⟩ := tensorRight_exact_of_flat _ (hflat₁ n)
  obtain ⟨_, _, _⟩ := tensorRight_exact_of_flat _ (hflat₂ n)
  show t n (Stacks.ExtCup.cup.{u + 1, _, _}
      (inverseImageConstantPairing
        (fieldBaseChangeProj (Over.mk j.toBase) kbar) (ℓ ^ (n + 1)) (μ₂ n))
      (LAdicSheaf.levelExtEquiv B X ℓ f j kbar F₂ 1 n
        ((geometricCompactSupportPadicCohomology B X ℓ f j kbar ((1 : ℕ) : ℤ)).map
          (LAdicSheaf.padicLevelMap φ n) x))
      (LAdicSheaf.levelExtEquiv B X ℓ f j kbar F₂' 1 n y) (show 1 + 1 = 2 from rfl)) =
    t n (Stacks.ExtCup.cup.{u + 1, _, _}
      (inverseImageConstantPairing
        (fieldBaseChangeProj (Over.mk j.toBase) kbar) (ℓ ^ (n + 1)) (μ₁ n))
      (LAdicSheaf.levelExtEquiv B X ℓ f j kbar F₁ 1 n x)
      (LAdicSheaf.levelExtEquiv B X ℓ f j kbar F₁' 1 n
        ((geometricCompactSupportPadicCohomology B X ℓ f j kbar ((1 : ℕ) : ℤ)).map
          (LAdicSheaf.padicLevelMap φ' n) y)) (show 1 + 1 = 2 from rfl))
  rw [LAdicSheaf.levelExtEquiv_naturality B X ℓ f j kbar φ 1 n x,
    LAdicSheaf.levelExtEquiv_naturality B X ℓ f j kbar φ' 1 n y,
    Stacks.ExtCup.comp_mk₀_cup, Stacks.ExtCup.cup_comp_mk₀_right]
  exact congrArg (fun μ => t n (Stacks.ExtCup.cup.{u + 1, _, _} μ
      (LAdicSheaf.levelExtEquiv B X ℓ f j kbar F₁ 1 n x)
      (LAdicSheaf.levelExtEquiv B X ℓ f j kbar F₂' 1 n y) (show 1 + 1 = 2 from rfl)))
    (whiskerRight_inverseImageConstantPairing _ _ _ _ _ _ (h n))

variable (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

omit [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- **Finite-level Poincaré duality on a curve over a finite field, for the explicit pairing.**
In the situation of `Stacks.EtaleCohomology.LAdicSheaf.exists_levelPairing_of_curve` (`X̄_k̄` a
smooth proper curve, `X` nonempty, `ℓ` invertible in `k̄`, `F'ₙ|_{X_k̄}` lisse,
`(j_! F'ₙ)|_{X̄_k̄}` with flat fibres, the pullback of `μₙ` to `X_k̄` perfect on fibres, the local
terms of `F` killed by `ℓ^K`), for injective traces `tₙ` on `H²(X̄_k̄, ℤ/ℓⁿ⁺¹)`
(`Stacks.EtaleCohomology.exists_injective_curveLevelTrace`), the pairing
`LAdicSheaf.curveLevelPairing` has left kernels killed by `ℓ^K`, right kernels killed by
`ℓ^K · ℓ^K`, and is scaled by `p ^ q` under the canonical geometric Frobenius. -/
theorem LAdicSheaf.curveLevelPairing_bounds [IsAlgClosed kbar]
    [IsCurve kbar (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))]
    [Smooth (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))]
    [Nonempty X.1] (hℓ : IsUnit (ℓ : kbar))
    (t : ∀ n : ℕ, Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (fieldBaseChange (Over.mk j.toBase) kbar)))
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology) 2 →+ ZMod (ℓ ^ (n + 1)))
    (ht : ∀ n, Function.Injective (t n))
    (F F' : LAdicSheaf B X ℓ) {K : ℕ} (hF : LAdicSheaf.LocalTermsKilledBy B X ℓ f j kbar F K)
    (μ : ∀ n, (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
        (LAdicSheaf.etaleLevel B X ℓ F n) ⊗
      (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
        (LAdicSheaf.etaleLevel B X ℓ F' n) ⟶
      Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
        j.space.smallEtaleTopology)
    (hlisse : ∀ n, Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod (ℓ ^ (n + 1)))
      (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology
      ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (fieldBaseChangeProj (Over.mk f) kbar)).obj
        (LAdicSheaf.etaleLevel B X ℓ F' n)))
    (hflat : ∀ (n : ℕ) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (s : Spec (.of Ω) ⟶ fieldBaseChange (Over.mk j.toBase) kbar),
      Module.Flat (ZMod (ℓ ^ (n + 1)))
        ((((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
          (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
            ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
              (LAdicSheaf.etaleLevel B X ℓ F' n)))))
    (hμ : ∀ (n : ℕ) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (s : Spec (.of Ω) ⟶ fieldBaseChange (Over.mk f) kbar),
      Function.Bijective (TensorProduct.curry (Functor.LaxMonoidal.μ
        (((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
          (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))))
        ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChangeMap j.obj.hom kbar)).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
            ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
              (LAdicSheaf.etaleLevel B X ℓ F n))))
        ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChangeMap j.obj.hom kbar)).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
            ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
              (LAdicSheaf.etaleLevel B X ℓ F' n)))) ≫
        (((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
          (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).map
          (inverseImageConstantPairing (fieldBaseChangeMap j.obj.hom kbar) (ℓ ^ (n + 1))
            (inverseImageConstantPairing (fieldBaseChangeProj (Over.mk j.toBase) kbar)
              (ℓ ^ (n + 1)) (μ n)))).hom)) :
    (∀ n x, (∀ y, LAdicSheaf.curveLevelPairing B X ℓ f j kbar t F F' μ hflat n x y = 0) →
        (ℓ ^ K) • x = 0) ∧
      (∀ n y, (∀ x, LAdicSheaf.curveLevelPairing B X ℓ f j kbar t F F' μ hflat n x y = 0) →
        (ℓ ^ K * ℓ ^ K) • y = 0) ∧
      ∀ n x y, LAdicSheaf.curveLevelPairing B X ℓ f j kbar t F F' μ hflat n
          ((canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f j kbar p q hcard
            ((padicCoefficientComplex B X ℓ).obj (LAdicSheaf.padicLevel B X ℓ F n)) 1).hom x)
          ((canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f j kbar p q hcard
            ((padicCoefficientComplex B X ℓ).obj (LAdicSheaf.padicLevel B X ℓ F' n)) 1).hom y) =
        ((p ^ q : ℕ) : ZMod (ℓ ^ (n + 1))) *
          LAdicSheaf.curveLevelPairing B X ℓ f j kbar t F F' μ hflat n x y := by
  have : IsProper (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)) :=
    isProper_pullback_snd_of_isProper _ _ (inferInstanceAs (IsProper j.toBase))
  have : Nonempty (fieldBaseChange (Over.mk f) kbar) := by
    obtain ⟨x⟩ := ‹Nonempty X.1›
    obtain ⟨y, -, -⟩ := Scheme.Pullback.exists_preimage_pullback x (default : Spec (.of kbar))
      (f := f) (g := specAlgebraMap k kbar) (Subsingleton.elim _ _)
    exact ⟨y⟩
  have hji : 1 + 1 = 2 := rfl
  let φ := fun n => LAdicSheaf.levelExtEquiv B X ℓ f j kbar F 1 n
  let φ' := fun n => LAdicSheaf.levelExtEquiv B X ℓ f j kbar F' 1 n
  let μY := fun n => inverseImageConstantPairing (fieldBaseChangeProj (Over.mk j.toBase) kbar)
    (ℓ ^ (n + 1)) (μ n)
  let G := fun n => (etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
    (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
      ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
        (LAdicSheaf.etaleLevel B X ℓ F' n))
  have hT₁ : ∀ n, (MonoidalCategory.tensorRight (G n)).Additive := fun n =>
    (tensorRight_exact_of_flat (G n) (hflat n)).1
  have hT₂ : ∀ n, PreservesFiniteLimits (MonoidalCategory.tensorRight (G n)) := fun n =>
    (tensorRight_exact_of_flat (G n) (hflat n)).2.1
  have hT₃ : ∀ n, PreservesFiniteColimits (MonoidalCategory.tensorRight (G n)) := fun n =>
    (tensorRight_exact_of_flat (G n) (hflat n)).2.2
  have hε : ∀ n x y, LAdicSheaf.curveLevelPairing B X ℓ f j kbar t F F' μ hflat n x y =
      t n (Stacks.ExtCup.cup.{u + 1, _, _} (μY n) (φ n x) (φ' n y) hji) := fun _ _ _ => rfl
  have hnd := fun n => LAdicSheaf.levelCup_bounds_of_curve B X ℓ f j kbar hℓ F F' hF n (μ n)
    (hlisse n) (hflat n) (hμ n) (t n) (ht n)
  refine ⟨fun n x hx => ?_, fun n y hy => ?_, fun n x y => ?_⟩
  · have h0 := (hnd n).1 (φ n x) fun b => by
      obtain ⟨y, rfl⟩ := (φ' n).surjective b
      exact (hε n x y).symm.trans (hx y)
    exact (φ n).injective (by rw [map_nsmul, h0, map_zero])
  · have h0 := (hnd n).2 (φ' n y) fun a => by
      obtain ⟨x, rfl⟩ := (φ n).surjective a
      exact (hε n x y).symm.trans (hy x)
    exact (φ' n).injective (by rw [map_nsmul, h0, map_zero])
  · let πb := geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard
    let G' := (etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1))) πb).obj (G n)
    have hG' := tensorRight_exact_of_flat G'
      (flat_sheafFiber_inverseImage πb (G n) (hflat n))
    obtain ⟨_, _, _⟩ := hG'
    have key := cup_adjunctionExtMap_frobeniusBaseChangeTwist (ℓ ^ (n + 1)) (Over.mk j.toBase) kbar
      p q hcard (μ n) hji (φ n x) (φ' n y)
    have h₁ : LAdicSheaf.curveLevelPairing B X ℓ f j kbar t F F' μ hflat n
          ((canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f j kbar p q hcard
            ((padicCoefficientComplex B X ℓ).obj (LAdicSheaf.padicLevel B X ℓ F n)) 1).hom x)
          ((canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f j kbar p q hcard
            ((padicCoefficientComplex B X ℓ).obj (LAdicSheaf.padicLevel B X ℓ F' n)) 1).hom y) =
        t n (constantExtRestriction (ZMod (ℓ ^ (n + 1))) πb 2
          (Stacks.ExtCup.cup.{u + 1, _, _} (μY n) (φ n x) (φ' n y) hji)) := by
      show t n (Stacks.ExtCup.cup.{u + 1, _, _} (μY n) (φ n _) (φ' n _) hji) = _
      rw [← key]
      exact congrArg₂ (fun a b => t n (Stacks.ExtCup.cup.{u + 1, _, _} (μY n) a b hji))
        (LAdicSheaf.levelExtEquiv_frobenius B X ℓ f j kbar p q hcard F 1 n x)
        (LAdicSheaf.levelExtEquiv_frobenius B X ℓ f j kbar p q hcard F' 1 n y)
    exact h₁.trans ((congrArg (t n)
      (constantExtRestriction_geometricFrobeniusBaseChange_two_of_curve (Over.mk j.toBase) kbar p q
        hcard hℓ (n + 1) _)).trans ((map_nsmul (t n) _ _).trans (nsmul_eq_mul _ _)))

end Pairing

end Stacks.EtaleCohomology

end
