module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.FrobeniusExtRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ConstantLevelExtComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportFrobeniusRestrictScalars
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Picard.MultiplicativeFirstCohomology

/-!
# The Frobenius on the levels of `Hⁱ(X_k̄, ℤ_ℓ)` is restriction along `π̄`

Let `X` be proper over a finite field `k`, compactified by itself, `ℓ` a prime and `N = ℓⁿ⁺¹`.
The level `n` of `Hⁱ(X_k̄, ℤ_ℓ)`
(`Stacks.EtaleCohomology.LAdicSheaf.geometricCompactlySupportedCohomology` of the constant ℓ-adic
sheaf) is, as an abelian group, `Ext^i_{ℤ/N}(ℤ/N, ℤ/N)` on `X_k̄`, through an isomorphism carrying
the canonical geometric Frobenius `π_X^*` to the restriction
`Stacks.EtaleCohomology.constantExtRestriction (ℤ/N) π̄ i` along `π̄ = π_X × id`
(`Stacks.EtaleCohomology.LAdicSheaf.exists_addEquiv_constantLevel_frobenius`). The isomorphism
reads the level with `ℤ/N`-coefficients (`LAdicSheaf.padicCoefficientComplexLevelIso` and
`compactSupportFrobeniusCohomologyGroupRestrictScalarsIso`, both compatible with `π_X^*`) and then
applies `Stacks.EtaleCohomology.compactSupportFrobeniusSingleIsoExt_canonical_constant`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

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
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [IsProper f]
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

omit [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- **The Frobenius on the level `n` of `Hⁱ(X_k̄, ℤ_ℓ)` is restriction along `π̄`.** For `X`
proper over the finite field `k`, compactified by itself, and `N = ℓⁿ⁺¹`, there is an isomorphism
of the level `n` of `Hⁱ(X_k̄, ℤ_ℓ)` with `Ext^i_{ℤ/N}(ℤ/N, ℤ/N)` on `X_k̄` carrying the canonical
geometric Frobenius `π_X^*` to the restriction along `π̄ = π_X × id`. -/
theorem LAdicSheaf.exists_addEquiv_constantLevel_frobenius (i n : ℕ) :
    ∃ Φ : (geometricCompactSupportPadicCohomology B X ℓ f (CompactificationOf.ofProper f) kbar
          i).obj (LAdicSheaf.padicLevel B X ℓ (LAdicSheaf.constantSystem B X ℓ) n) ≃+
      Ext (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology)
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology) i,
      ∀ x, Φ ((canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f (CompactificationOf.ofProper f)
          kbar p q hcard ((padicCoefficientComplex B X ℓ).obj
            (LAdicSheaf.padicLevel B X ℓ (LAdicSheaf.constantSystem B X ℓ) n)) i).hom x) =
        constantExtRestriction (ZMod (ℓ ^ (n + 1)))
          (geometricFrobeniusBaseChange (Over.mk f) kbar p q hcard) i (Φ x) := by
  let j := CompactificationOf.ofProper f
  let F := LAdicSheaf.constantSystem B X ℓ
  let ρ := PadicInt.toZModPow (p := ℓ) (n + 1)
  let H := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ_[ℓ]) (i : ℤ)
  let C := compactSupportFrobeniusFunctor.{u, 0} ℤ_[ℓ] f j kbar
  let Fr := canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] f j kbar p q hcard
  let lv := LAdicSheaf.padicCoefficientComplexLevelIso B X ℓ F n
  let e₁ := (C ⋙ H).mapIso lv
  let e₂ := (compactSupportFrobeniusCohomologyGroupRestrictScalarsIso ρ f j kbar
    (LAdicSheaf.levelComplex B X ℓ F n) (i : ℤ)).symm
  let K := LAdicSheaf.etaleLevel B X ℓ F n
  let γ : (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj K ≅
      Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
        (Over.mk j.toBase).left.smallEtaleTopology :=
    (etaleModuleExtensionByZeroIdIso (ZMod (ℓ ^ (n + 1))) X.1).app K ≪≫
      LAdicSheaf.etaleLevelConstantSystemIso B X ℓ n
  let δ := (etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
      (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapIso γ ≪≫
    inverseImageEtaleModuleConstantSheafIso.{u, 0} (ZMod (ℓ ^ (n + 1)))
      (ModuleCat.of (ZMod (ℓ ^ (n + 1))) (ULift.{u + 1} (ZMod (ℓ ^ (n + 1)))))
      (fieldBaseChangeProj (Over.mk j.toBase) kbar)
  let e₃ := Iso.addCommGroupIsoToAddEquiv
    (compactSupportFrobeniusSingleIsoExt (ZMod (ℓ ^ (n + 1))) f j kbar K i)
  let e₄ := SmallEtale.extPostcompIsoAddEquiv.{u + 1}
    (X := Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
      (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology) δ i
  refine ⟨((e₁.toLinearEquiv.toAddEquiv.trans e₂.toLinearEquiv.toAddEquiv).trans e₃).trans e₄,
    fun x => ?_⟩
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
  have h₃ := compactSupportFrobeniusSingleIsoExt_canonical_constant (ZMod (ℓ ^ (n + 1))) kbar p q
    hcard f j K γ (e₄ (e₃ y))
  have hA : (e₄ (e₃ y)).comp
      (Ext.mk₀ ((inverseImageEtaleModuleConstantSheafIso.{u, 0} (ZMod (ℓ ^ (n + 1)))
      (ModuleCat.of (ZMod (ℓ ^ (n + 1))) (ULift.{u + 1} (ZMod (ℓ ^ (n + 1)))))
      (fieldBaseChangeProj (Over.mk j.toBase) kbar)).inv ≫
      (etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (fieldBaseChangeProj (Over.mk j.toBase) kbar)).map γ.inv)) (add_zero i) = e₃ y :=
    e₄.symm_apply_apply (e₃ y)
  have hB : ((compactSupportFrobeniusSingleIsoExt (ZMod (ℓ ^ (n + 1))) f j kbar K i).inv).hom
      (e₃ y) = y := e₃.symm_apply_apply y
  rw [hA, hB] at h₃
  show e₄ (e₃ (e₂.hom.hom (e₁.hom.hom _))) = _
  rw [h₁]
  exact (congrArg (fun z => e₄ (e₃ z)) (h₂' (e₁.hom.hom x))).trans h₃

end Stacks.EtaleCohomology

end
