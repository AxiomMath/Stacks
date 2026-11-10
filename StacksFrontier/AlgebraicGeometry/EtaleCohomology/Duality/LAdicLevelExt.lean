module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LAdicFrobeniusLevel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.BaseChangeTwistMonoidal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicTowerSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LAdicPoincarePurity

/-!
# The levels of `Hⁱ_c(X_k̄, F)` as `Ext` groups, with their Frobenius

Let `X` be a `k`-scheme over a finite field `k`, with a compactification `j : X ⟶ X̄`, `k̄` an
extension of `k`, `Y = X̄_k̄`, `pr : Y ⟶ X̄` the projection and `π̄ : Y ⟶ Y` the base change of the
geometric Frobenius. For an ℓ-adic sheaf `F` on `X` with levels `Fₙ` and `N = ℓⁿ⁺¹`, the level
`n` of `Hⁱ_c(X_k̄, F)` is `Ext^i_{ℤ/N}(ℤ/N_Y, pr^{-1}(j_! Fₙ))`, through an isomorphism carrying
the canonical geometric Frobenius `π_X^*` to `b ↦ θ(b ∘ τ)`, with
`τ : pr^{-1}(j_! Fₙ) ⟶ π̄_* pr^{-1}(j_! Fₙ)` the base change of the Frobenius descent isomorphism
and `θ` the `Ext` map of `π̄^{-1} ⊣ π̄_*`
(`Stacks.EtaleCohomology.LAdicSheaf.exists_addEquiv_level_frobenius`). This is
`Stacks.EtaleCohomology.LAdicSheaf.exists_addEquiv_constantLevel_frobenius` for an arbitrary
ℓ-adic sheaf, and the glue between the finite-level Poincaré duality on `Y` and the ℓ-adic
cohomology in the purity half of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

The statements consume objects defined in the standard model `HasDerivedCategory.standard` of the
derived category, which is therefore a local instance here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  Sheaf.monoidalCategory etaleModuleInverseImageSheafPullbackMonoidal
  etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits
  etaleModuleDirectImage_preservesFiniteColimits_of_universalHomeomorphism

/-- The morphisms of presheaves of `Λ`-modules on the small étale site of `S` that become
isomorphisms after sheafification form a monoidal class. -/
local instance (Λ : Type) [CommRing Λ] (S : Scheme.{u}) :
    (S.smallEtaleTopology.W (A := ModuleCat.{u + 1} Λ)).IsMonoidal :=
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
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

omit [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- **The level `n` of `Hⁱ_c(X_k̄, F)` is `Ext^i(ℤ/N_Y, pr^{-1}(j_! Fₙ))`, with its Frobenius.**
For an ℓ-adic sheaf `F` on `X`, `N = ℓⁿ⁺¹` and `Y = X̄_k̄`, there is an isomorphism of the level
`n` of `Hⁱ_c(X_k̄, F)` with `Ext^i_{ℤ/N}(ℤ/N_Y, pr^{-1}(j_! Fₙ))` carrying the canonical geometric
Frobenius `π_X^*` to `b ↦ θ(b ∘ τ)`. -/
theorem LAdicSheaf.exists_addEquiv_level_frobenius (F : LAdicSheaf B X ℓ) (i n : ℕ) :
    ∃ Φ : (geometricCompactSupportPadicCohomology B X ℓ f j kbar i).obj
        (LAdicSheaf.padicLevel B X ℓ F n) ≃+
      Ext (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology)
        ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
          ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
            (LAdicSheaf.etaleLevel B X ℓ F n))) i,
      ∀ x, Φ ((canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f j kbar p q hcard
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
          ((Φ x).comp (Ext.mk₀ ((frobeniusBaseChangeTwist.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (Over.mk j.toBase) kbar p q hcard).app
            ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
              (LAdicSheaf.etaleLevel B X ℓ F n)))) (add_zero i)) := by
  let ρ := PadicInt.toZModPow (p := ℓ) (n + 1)
  let H := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ_[ℓ]) (i : ℤ)
  let lv := LAdicSheaf.padicCoefficientComplexLevelIso B X ℓ F n
  let e₁ := (compactSupportFrobeniusFunctor.{u, 0} ℤ_[ℓ] f j kbar ⋙ H).mapIso lv
  let e₂ := (compactSupportFrobeniusCohomologyGroupRestrictScalarsIso ρ f j kbar
    (LAdicSheaf.levelComplex B X ℓ F n) (i : ℤ)).symm
  let K := LAdicSheaf.etaleLevel B X ℓ F n
  let e₃ := Iso.addCommGroupIsoToAddEquiv
    (compactSupportFrobeniusSingleIsoExt (ZMod (ℓ ^ (n + 1))) f j kbar K i)
  refine ⟨(e₁.toLinearEquiv.toAddEquiv.trans e₂.toLinearEquiv.toAddEquiv).trans e₃,
    fun x => ?_⟩
  have h₁ : e₁.hom.hom ((canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f j kbar p q hcard
      ((padicCoefficientComplex B X ℓ).obj (LAdicSheaf.padicLevel B X ℓ F n)) i).hom x) =
      (canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f j kbar p q hcard
        ((etaleModuleRestrictScalars ρ X.1).mapCochainComplexPlus.obj
          (LAdicSheaf.levelComplex B X ℓ F n)) i).hom (e₁.hom.hom x) := by
    have := congrArg H.map
      ((canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] f j kbar p q hcard).naturality lv.hom)
    simp only [Functor.map_comp] at this
    exact (congrArg (fun g => g.hom x) this).symm
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
    rw [Iso.inv_comp_eq, ← Category.assoc,
      ← restrictScalars_canonicalCompactSupportFrobeniusGroup ρ f j kbar p q hcard
        (LAdicSheaf.levelComplex B X ℓ F n) (i : ℤ), Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have h₂' : ∀ z, e₂.hom.hom ((canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f j kbar p q hcard
      ((etaleModuleRestrictScalars ρ X.1).mapCochainComplexPlus.obj
        (LAdicSheaf.levelComplex B X ℓ F n)) i).hom z) =
      (canonicalCompactSupportFrobeniusGroup.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar p q hcard
        (LAdicSheaf.levelComplex B X ℓ F n) i).hom (e₂.hom.hom z) := fun z =>
    (congrArg (fun g => g.hom z) hh).symm
  set y := e₂.hom.hom (e₁.hom.hom x)
  have h₃ := compactSupportFrobeniusSingleIsoExt_canonical_apply (ZMod (ℓ ^ (n + 1))) f j kbar p q
    hcard K i (e₃ y)
  have hB : ((compactSupportFrobeniusSingleIsoExt (ZMod (ℓ ^ (n + 1))) f j kbar K i).inv).hom
      (e₃ y) = y := e₃.symm_apply_apply y
  rw [hB] at h₃
  change e₃ (e₂.hom.hom (e₁.hom.hom _)) = _
  rw [h₁]
  exact (congrArg (fun z => e₃ z) (h₂' (e₁.hom.hom x))).trans h₃

end Stacks.EtaleCohomology

end
