module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicTowerSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicLimitStep
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicCompactSupportFunctoriality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTopCohomologyTransition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportRestrictScalarsComp
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoefficientLevelTraceFormula

/-!
# The tower of `RΓ_c(X_k̄, Fₙ)` twisted by an endomorphism of `F`

Let `F` be an ℓ-adic sheaf with flat levels whose complexes `Kₙ = RΓ_c(X_k̄, Fₙ)` are perfect,
and `ψ : F ⟶ F` an endomorphism. The endomorphisms `π_X^* ≫ ψ_*` of the `Kₙ` are compatible with
the transitions, so `(Kₙ, π_X^* ≫ ψ_*)` is a tower of perfect complexes in the sense of
[Tag 03V4](https://stacks.math.columbia.edu/tag/03V4), and its ℓ-adic trace is the alternating
sum of the traces of `π_X^* ≫ ψ_*` on `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)`. This is the trace formula of
[Tag 03V2](https://stacks.math.columbia.edu/tag/03V2) twisted by `ψ`, on the cohomology side.

The statements consume objects defined in the standard model `HasDerivedCategory.standard` of the
derived category, which is therefore a local instance here.

## Main definitions

* `Stacks.EtaleCohomology.LAdicSheaf.geometricPerfectTowerTwist`

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.alternating_trace_comp_of_flat`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale
open Stacks.Frobenius Stacks.InverseSystem

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable {B : BigEtaleSite.{u}} {X : B.Scheme} {ℓ : ℕ}

variable [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
  ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [IsNoetherian X.1] [Fact ℓ.Prime]

/-- Pasting two commutative squares: `a ≫ b = c ≫ e` and `e ≫ y = x ≫ z` give
`a ≫ b ≫ y = (c ≫ x) ≫ z`. -/
private theorem comp_comp_eq_of_comm_squares {C : Type*} [Category C] {P Q R S T U : C}
    {a : P ⟶ Q} {b : Q ⟶ R} {c : P ⟶ S} {e : S ⟶ R} {y : R ⟶ T} {x : S ⟶ U} {z : U ⟶ T}
    (h₁ : a ≫ b = c ≫ e) (h₂ : e ≫ y = x ≫ z) : a ≫ b ≫ y = (c ≫ x) ≫ z := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]

/-- **A morphism of ℓ-adic sheaves commutes with the transitions of the level complexes.** -/
public theorem LAdicSheaf.levelComplexMap_levelComplexTransition {F G : LAdicSheaf.{u, u + 1} B X ℓ}
    (φ : F ⟶ G) (n : ℕ) :
    LAdicSheaf.levelComplexMap φ (n + 1) ≫ LAdicSheaf.levelComplexTransition B X ℓ G n =
      LAdicSheaf.levelComplexTransition B X ℓ F n ≫
        (etaleModuleRestrictScalars (levelCast ℓ n) X.1).mapCochainComplexPlus.map
          (LAdicSheaf.levelComplexMap φ n) := by
  let E := SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1 + 1))))
  have h₁ := congrArg E.functor.map (φ.naturality n)
  rw [Functor.map_comp, Functor.map_comp] at h₁
  have h₂ := (sheafEquivRestrictScalarsIso B X.1 X.property (levelCast ℓ n)).inv.naturality
    (φ.app n)
  have h₃ : E.functor.map (φ.app (n + 1)) ≫ LAdicSheaf.etaleTransition B X ℓ G n =
      LAdicSheaf.etaleTransition B X ℓ F n ≫
        (etaleModuleRestrictScalars (levelCast ℓ n) X.1).map
          ((SmallEtale.sheafEquiv B X.1 X.property
            (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).functor.map (φ.app n)) := by
    simp only [LAdicSheaf.etaleTransition]
    exact comp_comp_eq_of_comm_squares h₁ h₂
  have h₄ := (HomologicalComplex.singleMapHomologicalComplex
    (etaleModuleRestrictScalars (levelCast ℓ n) X.1) (ComplexShape.up ℤ) 0).inv.naturality
      ((SmallEtale.sheafEquiv B X.1 X.property
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).functor.map (φ.app n))
  have h₅ := congrArg (HomologicalComplex.single (EtaleModules.{u, 0}
    (ZMod (ℓ ^ (n + 1 + 1))) X.1) (ComplexShape.up ℤ) 0).map h₃
  rw [Functor.map_comp, Functor.map_comp] at h₅
  exact ObjectProperty.hom_ext _ (comp_comp_eq_of_comm_squares h₅ h₄)

variable {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- **The tower `Kₙ = RΓ_c(X_k̄, Fₙ)` twisted by `ψ : F ⟶ F`**: the endomorphisms are
`π_X^* ≫ ψ_*`. -/
public def LAdicSheaf.geometricPerfectTowerTwist (F : LAdicSheaf B X ℓ)
    (hF : ∀ n, PowExact ℓ (n + 1) (LAdicSheaf.etaleLevel B X ℓ F n))
    (hP : ∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
        (LAdicSheaf.levelComplex B X ℓ F n)))) (ψ : F ⟶ F) :
    PerfectTower.{u + 1} ℓ where
  obj := (LAdicSheaf.geometricPerfectTower B X ℓ f j kbar p q hcard F hF hP).obj
  isPerfect := (LAdicSheaf.geometricPerfectTower B X ℓ f j kbar p q hcard F hF hP).isPerfect
  endo n := DerivedCategory.Plus.ι.map
    (canonicalCompactSupportFrobenius.{u, 0} _ f j kbar p q hcard
        (LAdicSheaf.levelComplex B X ℓ F n) ≫
      (compactSupportFrobeniusFunctor.{u, 0} _ f j kbar).map (LAdicSheaf.levelComplexMap ψ n))
  transition := (LAdicSheaf.geometricPerfectTower B X ℓ f j kbar p q hcard F hF hP).transition
  comparison_isIso :=
    (LAdicSheaf.geometricPerfectTower B X ℓ f j kbar p q hcard F hF hP).comparison_isIso
  endo_compatible n := by
    have hψ₁ := congrArg (compactSupportFrobeniusFunctor.{u, 0} _ f j kbar).map
      (LAdicSheaf.levelComplexMap_levelComplexTransition ψ n)
    rw [Functor.map_comp, Functor.map_comp] at hψ₁
    have hψ₂ := compactSupportFrobeniusCohomologyRestrictScalarsIso_hom_naturality
      (ρ := levelCast ℓ n) (f := f) (j := j) (kbar := kbar) (LAdicSheaf.levelComplexMap ψ n)
    have hψ : DerivedCategory.Plus.ι.map ((compactSupportFrobeniusFunctor.{u, 0} _ f j kbar).map
          (LAdicSheaf.levelComplexMap ψ (n + 1))) ≫
          (LAdicSheaf.geometricPerfectTower B X ℓ f j kbar p q hcard F hF hP).transition n =
        (LAdicSheaf.geometricPerfectTower B X ℓ f j kbar p q hcard F hF hP).transition n ≫
          (levelRestrict.{u + 1} ℓ n).map (DerivedCategory.Plus.ι.map
            ((compactSupportFrobeniusFunctor.{u, 0} _ f j kbar).map
              (LAdicSheaf.levelComplexMap ψ n))) :=
      (DerivedCategory.Plus.ι.map_comp _ _).symm.trans ((congrArg DerivedCategory.Plus.ι.map
        (tower_endo_aux _ _ _ _ _ hψ₁.symm hψ₂)).trans (DerivedCategory.Plus.ι.map_comp _ _))
    exact ((congrArg (· ≫ _) (DerivedCategory.Plus.ι.map_comp _ _)).trans
      (Category.assoc _ _ _)).trans ((congrArg (_ ≫ ·) hψ).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) ((LAdicSheaf.geometricPerfectTower B X ℓ f j kbar p q hcard F hF
        hP).endo_compatible n)).trans ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
        (((levelRestrict.{u + 1} ℓ n).map_comp _ _).symm.trans
          (congrArg (levelRestrict.{u + 1} ℓ n).map
            (DerivedCategory.Plus.ι.map_comp _ _).symm)))))))

/-- **The identification of the `ℤ_ℓ`-level complex with the restriction of scalars of the level
complex is natural** in morphisms of ℓ-adic sheaves. -/
public theorem LAdicSheaf.padicCoefficientComplexLevelIso_hom_naturality
    {F G : LAdicSheaf.{u, u + 1} B X ℓ} (φ : F ⟶ G) (n : ℕ) :
    (padicCoefficientComplex B X ℓ).map (LAdicSheaf.padicLevelMap φ n) ≫
        (LAdicSheaf.padicCoefficientComplexLevelIso B X ℓ G n).hom =
      (LAdicSheaf.padicCoefficientComplexLevelIso B X ℓ F n).hom ≫
        (etaleModuleRestrictScalars (PadicInt.toZModPow (n + 1)) X.1).mapCochainComplexPlus.map
          (LAdicSheaf.levelComplexMap φ n) := by
  have h₂ :=
    (sheafEquivRestrictScalarsIso B X.1 X.property (PadicInt.toZModPow (n + 1))).inv.naturality
      (φ.app n)
  have h₄ := (HomologicalComplex.singleMapHomologicalComplex
    (etaleModuleRestrictScalars (PadicInt.toZModPow (n + 1)) X.1)
      (ComplexShape.up ℤ) 0).inv.naturality
      ((SmallEtale.sheafEquiv B X.1 X.property
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).functor.map (φ.app n))
  have h₅ := congrArg (HomologicalComplex.single (EtaleModules.{u, 0} ℤ_[ℓ] X.1)
    (ComplexShape.up ℤ) 0).map h₂
  rw [Functor.map_comp, Functor.map_comp] at h₅
  exact ObjectProperty.hom_ext _ (comp_comp_eq_of_comm_squares h₅ h₄)

/-- The endomorphism `Hⁱ(ψ_*)` of `Hⁱ_c(X_k̄, Fₙ)`, as a map of `ℤ_ℓ`-modules on the level
cohomology of the tower. -/
public def LAdicSheaf.levelCohomologyMap (F : LAdicSheaf B X ℓ)
    (hF : ∀ n, PowExact ℓ (n + 1) (LAdicSheaf.etaleLevel B X ℓ F n))
    (hP : ∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
        (LAdicSheaf.levelComplex B X ℓ F n)))) (ψ : F ⟶ F) (i : ℤ) (n : ℕ) :
    (levelCohomologySystem (LAdicSheaf.geometricPerfectTower B X ℓ f j kbar p q hcard F hF hP)
        i).obj (op n) ⟶
      (levelCohomologySystem (LAdicSheaf.geometricPerfectTower B X ℓ f j kbar p q hcard F hF hP)
        i).obj (op n) :=
  (ModuleCat.restrictScalars.{u + 1} (PadicInt.toZModPow (n + 1))).map
    ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) i).map
      ((compactSupportFrobeniusFunctor.{u, 0} _ f j kbar).map (LAdicSheaf.levelComplexMap ψ n)))

omit [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- **The level isomorphisms carry `ψ_*` to `Hⁱ(ψ_*)` on the level cohomology.** -/
public theorem LAdicSheaf.geometricLevelCohomologyIso_map (F : LAdicSheaf B X ℓ)
    (hF : ∀ n, PowExact ℓ (n + 1) (LAdicSheaf.etaleLevel B X ℓ F n))
    (hP : ∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
        (LAdicSheaf.levelComplex B X ℓ F n)))) (ψ : F ⟶ F) (i : ℤ) (n : ℕ) :
    (LAdicSheaf.geometricCompactlySupportedCohomologySystemMap f j kbar ψ i).app (op n) ≫
      (LAdicSheaf.geometricLevelCohomologyIso B X ℓ f j kbar p q hcard F hF hP i n).hom =
    (LAdicSheaf.geometricLevelCohomologyIso B X ℓ f j kbar p q hcard F hF hP i n).hom ≫
      LAdicSheaf.levelCohomologyMap f j kbar p q hcard F hF hP ψ i n := by
  let H := compactSupportFrobeniusFunctor.{u, 0} ℤ_[ℓ] f j kbar ⋙
    DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ_[ℓ]) i
  exact endo_transport_aux _ _ _ ((H.map_comp _ _).symm.trans ((congrArg H.map
    (LAdicSheaf.padicCoefficientComplexLevelIso_hom_naturality ψ n)).trans
      (H.map_comp _ _))).symm _ _
    (compactSupportFrobeniusCohomologyGroupRestrictScalarsIso_naturality
      (PadicInt.toZModPow (n + 1)) f j kbar (LAdicSheaf.levelComplexMap ψ n) i)

omit [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- The twisted endomorphisms of the level cohomology are `Hⁱ(ψ_*) ∘ Hⁱ(π_X^*)`. -/
public theorem LAdicSheaf.levelCohomologyEndoSystem_geometricPerfectTowerTwist
    (F : LAdicSheaf B X ℓ)
    (hF : ∀ n, PowExact ℓ (n + 1) (LAdicSheaf.etaleLevel B X ℓ F n))
    (hP : ∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
        (LAdicSheaf.levelComplex B X ℓ F n)))) (ψ : F ⟶ F) (i : ℤ) (n : ℕ) :
    (levelCohomologyEndoSystem (LAdicSheaf.geometricPerfectTowerTwist f j kbar p q hcard F hF hP ψ)
        i).app (op n) =
      (levelCohomologyEndoSystem (LAdicSheaf.geometricPerfectTower B X ℓ f j kbar p q hcard F hF hP)
        i).app (op n) ≫ LAdicSheaf.levelCohomologyMap f j kbar p q hcard F hF hP ψ i n := by
  ext x
  exact congrArg (fun g => g.hom x) ((congrArg
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) i).map
    (DerivedCategory.Plus.ι.map_comp (canonicalCompactSupportFrobenius.{u, 0} _ f j kbar p q hcard
        (LAdicSheaf.levelComplex B X ℓ F n))
      ((compactSupportFrobeniusFunctor.{u, 0} _ f j kbar).map
        (LAdicSheaf.levelComplexMap ψ n)))).trans
    ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) i).map_comp _ _))

omit [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- **The system isomorphism carries `π_X^* ≫ ψ_*` to the endomorphisms of the twisted tower.** -/
public theorem LAdicSheaf.geometricLevelCohomologySystemIso_twist (F : LAdicSheaf B X ℓ)
    (hF : ∀ n, PowExact ℓ (n + 1) (LAdicSheaf.etaleLevel B X ℓ F n))
    (hP : ∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
        (LAdicSheaf.levelComplex B X ℓ F n)))) (ψ : F ⟶ F) (i : ℤ) :
    (LAdicSheaf.geometricCompactlySupportedCohomologySystemPullback B X ℓ f j kbar F i
        (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] f j kbar p q hcard) ≫
        LAdicSheaf.geometricCompactlySupportedCohomologySystemMap f j kbar ψ i) ≫
      (LAdicSheaf.geometricLevelCohomologySystemIso B X ℓ f j kbar p q hcard F hF hP i).hom =
    (LAdicSheaf.geometricLevelCohomologySystemIso B X ℓ f j kbar p q hcard F hF hP i).hom ≫
      levelCohomologyEndoSystem (LAdicSheaf.geometricPerfectTowerTwist f j kbar p q hcard F hF hP ψ)
        i := by
  ext n : 2
  induction n using Opposite.rec with | op n => ?_
  have hπ := LAdicSheaf.geometricLevelCohomologyIso_frobenius B X ℓ f j kbar p q hcard F hF hP i n
  have hψ := LAdicSheaf.geometricLevelCohomologyIso_map f j kbar p q hcard F hF hP ψ i n
  have hT := LAdicSheaf.levelCohomologyEndoSystem_geometricPerfectTowerTwist f j kbar p q hcard F
    hF hP ψ i n
  exact (comp_comp_eq_of_comm_squares hπ.symm hψ.symm).symm.trans (congrArg (_ ≫ ·) hT.symm)

omit [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- **The trace formula twisted by `ψ`, on the cohomology side**: for an ℓ-adic sheaf with flat
levels whose `RΓ_c(X_k̄, Fₙ)` are perfect and `ψ : F ⟶ F`, the alternating sum of the traces of
`π_X^* ≫ ψ_*` on `Hⁱ_c(X_k̄, F) ⊗ ℚ_ℓ` is the ℓ-adic trace of the twisted tower. -/
public theorem LAdicSheaf.alternating_trace_comp_of_flat (F : LAdicSheaf B X ℓ)
    (hF : ∀ n, PowExact ℓ (n + 1) (LAdicSheaf.etaleLevel B X ℓ F n))
    (hP : ∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
        (LAdicSheaf.levelComplex B X ℓ F n)))) (ψ : F ⟶ F) :
    ∑ᶠ i : ℤ, (if Even i then (1 : ℚ_[ℓ]) else -1) *
        LinearMap.trace ℚ_[ℓ]
          (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)
          (LinearMap.baseChange ℚ_[ℓ] (limMap
            (LAdicSheaf.geometricCompactlySupportedCohomologySystemPullback B X ℓ f j kbar F i
                (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] f j kbar p q hcard) ≫
              LAdicSheaf.geometricCompactlySupportedCohomologySystemMap f j kbar ψ i)).hom) =
      (padicTrace (LAdicSheaf.geometricPerfectTowerTwist f j kbar p q hcard F hF hP ψ) : ℚ_[ℓ]) :=
  alternating_trace_rational_limit_of_iso _ _
    (fun i => LAdicSheaf.geometricLevelCohomologySystemIso B X ℓ f j kbar p q hcard F hF hP i)
    (fun i => LAdicSheaf.geometricLevelCohomologySystemIso_twist f j kbar p q hcard F hF hP ψ i)

end Stacks.EtaleCohomology

end
