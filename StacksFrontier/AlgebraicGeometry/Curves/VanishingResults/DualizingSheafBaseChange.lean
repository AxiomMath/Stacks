module

public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingTwistGenerationGeneralField
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.FlatTrace
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.FieldExtension
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeSubobjectColimit
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper
public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.PushforwardTExactness
public import StacksFrontier.AlgebraicGeometry.QuasicoherentBasicOpen.LocalSections
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.PushforwardAffine
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.StalkFormalFunctions
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CohomologyBridge
public import StacksFrontier.AlgebraicGeometry.TwistedCohomologyLocalization.OverFieldAction
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProjectiveEquivalenceAuxDegreeBound

/-!
# The dualizing sheaf of a proper curve under extension of the ground field

In Situation [Stacks, Tag 0B5D] let `K/k` be an extension of fields and `g : X_K ⟶ X` the
projection. Part (2) of [Stacks, Tag 0E32] says that `g^*ω_X` is the dualizing module of `X_K`.
This file builds the comparison of cohomology along `g` that the proof needs, at the sheaf level
and with no recourse to the twisted inverse image:

* `cohomologyBaseChange`: `K ⊗_k Hⁿ(X, ℱ) ⟶ Hⁿ(X_K, g^*ℱ)`, `a ⊗ x ↦ a • g^*x`, injective for
  every quasi-coherent `ℱ` (`cohomologyBaseChange_injective`, through the traces of
  `k`-linear functionals on `K` of `…/FlatBaseChangeCohomology/FlatTrace.lean`) and bijective as
  soon as `Hⁿ(X, ℱ)` is finite dimensional (dimension count of [Stacks, Tag 02KH] part (2));
* `baseChangeTraceForm`: the trace `t_K = K ⊗ t` on `H¹(X_K, g^*ω)` of a module `ω` with the
  duality of clause (5) of [Stacks, Tag 0BS2] and `dim H¹(X, ω) = 1`, and the identity
  `traceForm_traceCohomology` relating it to `t` through the traces;
* the naturality of the pullback map on cohomology.

## References

* [Stacks Project, Tag 0E32](https://stacks.math.columbia.edu/tag/0E32)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.SectionsBaseChange Stacks.Cohomology.AffineComparison
  Stacks.Cohomology.AffineBase
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

namespace CohenMacaulayCurveSituation

variable (S : CohenMacaulayCurveSituation.{u}) (K : Type u) [Field K] [Algebra S.k K]

/-! ### The base-change square -/

/-- The morphism `Spec K ⟶ Spec k` along which the situation is base changed. -/
abbrev baseChangeBase : Spec (.of K) ⟶ Spec (.of S.k) :=
  Spec.map (CommRingCat.ofHom (algebraMap S.k K))

/-- The cartesian square of the base change of the situation. -/
theorem isPullback_baseChange :
    IsPullback (S.baseChangeProj K) (S.baseChange K).f S.f (S.baseChangeBase K) :=
  IsPullback.of_hasPullback _ _

/-- The ring map `Γ(Spec k, ⊤) ⟶ Γ(Spec K, ⊤)` underlying the base change is flat. -/
theorem flat_baseChangeBase_appLE :
    RingHom.Flat ((S.baseChangeBase K).appLE ⊤ ⊤ (le_preimage_top _ ⊤)).hom := by
  have e : (S.baseChangeBase K).appLE ⊤ ⊤ (le_preimage_top _ ⊤) =
      (Scheme.ΓSpecIso (.of S.k)).hom ≫ CommRingCat.ofHom (algebraMap S.k K) ≫
        (Scheme.ΓSpecIso (.of K)).inv := by
    rw [Stacks.FormalFunctions.appLE_top_eq_appTop, ← Scheme.ΓSpecIso_naturality_assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [e]
  simp only [CommRingCat.hom_comp]
  refine RingHom.Flat.comp ?_ (RingHom.Flat.comp ?_ ?_)
  · exact RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)
  · exact RingHom.flat_algebraMap_iff.mpr inferInstance
  · exact RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)

/-- `Γ(Spec K, ⊤)` is a free `Γ(Spec k, ⊤)`-module: both are fields. -/
theorem free_baseChangeBase :
    letI := baseAlgebra (S.baseChangeBase K)
    Module.Free Γ(Spec (.of S.k), ⊤) Γ(Spec (.of K), ⊤) := by
  have h : IsField Γ(Spec (.of S.k), ⊤) :=
    MulEquiv.isField (Field.toIsField S.k)
      (Scheme.ΓSpecIso (.of S.k)).commRingCatIsoToRingEquiv.toMulEquiv
  let : Field Γ(Spec (.of S.k), ⊤) := h.toField
  let := baseAlgebra (S.baseChangeBase K)
  infer_instance

/-- The base change of the situation is affine over the situation. -/
theorem isAffineHom_baseChangeProj : IsAffineHom (S.baseChangeProj K) :=
  Stacks.Tag0CKW.isAffineHom_of_isPullback (S.isPullback_baseChange K)

/-- **Sections of a quasi-coherent module commute with the extension of the ground field, over
every open of the curve.** The curve is a Noetherian scheme separated over `k`, so every open is
quasi-compact. -/
theorem bijective_sectionsBaseChangeMap_baseChange (F : S.X.Modules) [F.IsQuasicoherent]
    (U : S.X.Opens) :
    letI := baseAlgebra (S.baseChangeBase K)
    letI := baseModule S.f F U
    letI := baseModule (S.baseChangeProj K ≫ S.f)
      ((Scheme.Modules.pullback (S.baseChangeProj K)).obj F) (S.baseChangeProj K ⁻¹ᵁ U)
    letI := baseModule (S.baseChange K).f
      ((Scheme.Modules.pullback (S.baseChangeProj K)).obj F) (S.baseChangeProj K ⁻¹ᵁ U)
    letI := baseTower (S.isPullback_baseChange K)
      ((Scheme.Modules.pullback (S.baseChangeProj K)).obj F) (S.baseChangeProj K ⁻¹ᵁ U)
    Function.Bijective (sectionsBaseChangeMap (S.isPullback_baseChange K) F U) := by
  have : IsNoetherian S.X := S.isNoetherian
  have := S.proper
  exact Stacks.FlatTrace.bijective_sectionsBaseChangeMap_of_isSeparated
    (S.isPullback_baseChange K) F (S.flat_baseChangeBase_appLE K) U
    (NoetherianSpace.isCompact _)

/-- **The trace of a functional on `K`**, as a morphism `g_* g^* ℱ ⟶ ℱ` for `g : X_K ⟶ X`. -/
abbrev baseChangeTrace (F : S.X.Modules) [F.IsQuasicoherent]
    (f : letI := baseAlgebra (S.baseChangeBase K)
      Γ(Spec (.of K), ⊤) →ₗ[Γ(Spec (.of S.k), ⊤)] Γ(Spec (.of S.k), ⊤)) :
    (Scheme.Modules.pushforward (S.baseChangeProj K)).obj
        ((Scheme.Modules.pullback (S.baseChangeProj K)).obj F) ⟶ F :=
  Stacks.FlatTrace.traceOf (S.isPullback_baseChange K) F
    (S.bijective_sectionsBaseChangeMap_baseChange K F) f

/-- The twisted unit followed by the trace of a functional is multiplication by its value. -/
theorem twistedUnit_comp_baseChangeTrace (F : S.X.Modules) [F.IsQuasicoherent]
    (f : letI := baseAlgebra (S.baseChangeBase K)
      Γ(Spec (.of K), ⊤) →ₗ[Γ(Spec (.of S.k), ⊤)] Γ(Spec (.of S.k), ⊤))
    (b : Γ(Spec (.of K), ⊤)) :
    Stacks.Tag0CKW.twistedUnit (S.baseChange K).f (S.baseChangeProj K) F b ≫
        S.baseChangeTrace K F f =
      (Scheme.smulEnd S.X ((S.f.appLE ⊤ ⊤ (le_preimage_top _ ⊤)).hom (f b))).asHom.app F :=
  Stacks.FlatTrace.twistedUnit_comp_traceOf _ F _ f b

/-! ### Cohomology along the extension of the ground field -/

attribute [local instance] HasDerivedCategory.standard

/-- The structure ring map `k ⟶ Γ(X, ⊤)` through which `cohomologyOverField` is a `k`-module. -/
abbrev structureRingHom : CommRingCat.of S.k ⟶ Γ(S.X, ⊤) :=
  (Scheme.ΓSpecIso (.of S.k)).inv ≫ S.f.appLE ⊤ ⊤ (by simp)

/-- `Γ(Spec k, ⊤) ⟶ Γ(Spec K, ⊤)` is `k ⟶ K` through the identifications `Γ(Spec R, ⊤) = R`. -/
theorem baseChangeBase_appLE_apply (c : S.k) :
    ((S.baseChangeBase K).appLE ⊤ ⊤ (le_preimage_top _ ⊤)).hom
        ((Scheme.ΓSpecIso (.of S.k)).inv.hom c) =
      (Scheme.ΓSpecIso (.of K)).inv.hom (algebraMap S.k K c) := by
  rw [Stacks.FormalFunctions.appLE_top_eq_appTop, ← CommRingCat.comp_apply,
    ← Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- The two structure maps `k ⟶ Γ(X_K, ⊤)` agree: through `Γ(X, ⊤)` and through `K`. -/
theorem baseChangeProj_appTop_structureRingHom (c : S.k) :
    (S.baseChangeProj K).appTop.hom ((S.structureRingHom).hom c) =
      ((S.baseChange K).structureRingHom).hom (algebraMap S.k K c) :=
  (Stacks.Tag0CKW.appTop_appLE_comm (S.isPullback_baseChange K)
    ((Scheme.ΓSpecIso (.of S.k)).inv.hom c)).trans
    (congrArg ((S.baseChange K).f.appLE ⊤ ⊤ (le_preimage_top _ ⊤)).hom
      (S.baseChangeBase_appLE_apply K c))

/-- **The pullback map `Hⁿ(X, ℱ) ⟶ Hⁿ(X_K, g^*ℱ)`** of cohomology along `g : X_K ⟶ X`: the unit
`ℱ ⟶ g_* g^* ℱ` on cohomology, followed by `Hⁿ(X, g_* -) = Hⁿ(X_K, -)` for the affine `g`. -/
def pullbackCohomology (F : S.X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    cohomologyOverField S.k S.f F n →+
      cohomologyOverField K (S.baseChange K).f
        ((Scheme.Modules.pullback (S.baseChangeProj K)).obj F) n :=
  (Stacks.Tag0CKW.cohomologyPullback (S.isPullback_baseChange K) F n).hom.toAddMonoidHom

/-- The pullback map on cohomology is the map `cohomologyPullback` of the base change square. -/
theorem pullbackCohomology_apply (F : S.X.Modules) [F.IsQuasicoherent] (n : ℕ)
    (x : cohomologyOverField S.k S.f F n) :
    S.pullbackCohomology K F n x =
      (Stacks.Tag0CKW.cohomologyPullback (S.isPullback_baseChange K) F n).hom x := rfl

/-- The pullback map on cohomology is semilinear along `k ⟶ K`: `g^*(c • x) = c • g^* x`. -/
theorem pullbackCohomology_smul (F : S.X.Modules) [F.IsQuasicoherent] (n : ℕ) (c : S.k)
    (x : cohomologyOverField S.k S.f F n) :
    S.pullbackCohomology K F n (c • x) = algebraMap S.k K c • S.pullbackCohomology K F n x := by
  let x' : ((moduleGlobalSections S.X).rightDerived n).obj F := x
  have h1 : S.pullbackCohomology K F n (c • x) =
      (Stacks.Tag0CKW.cohomologyPullback (S.isPullback_baseChange K) F n).hom
        ((S.structureRingHom).hom c • x') := rfl
  rw [h1, LinearMap.map_smul]
  change ((S.baseChangeProj K).appTop.hom ((S.structureRingHom).hom c)) •
      ((Stacks.Tag0CKW.cohomologyPullback (S.isPullback_baseChange K) F n).hom x' :
        ((moduleGlobalSections (S.baseChange K).X).rightDerived n).obj
          ((Scheme.Modules.pullback (S.baseChangeProj K)).obj F)) =
    ((S.baseChange K).structureRingHom).hom (algebraMap S.k K c) •
      ((Stacks.Tag0CKW.cohomologyPullback (S.isPullback_baseChange K) F n).hom x' :
        ((moduleGlobalSections (S.baseChange K).X).rightDerived n).obj
          ((Scheme.Modules.pullback (S.baseChangeProj K)).obj F))
  rw [S.baseChangeProj_appTop_structureRingHom K c]

/-- **The base change map `K ⊗_k Hⁿ(X, ℱ) ⟶ Hⁿ(X_K, g^*ℱ)`**, `a ⊗ x ↦ a • g^* x`. -/
def cohomologyBaseChange (F : S.X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    K ⊗[S.k] cohomologyOverField S.k S.f F n →ₗ[K]
      cohomologyOverField K (S.baseChange K).f
        ((Scheme.Modules.pullback (S.baseChangeProj K)).obj F) n :=
  letI : Module S.k (cohomologyOverField K (S.baseChange K).f
      ((Scheme.Modules.pullback (S.baseChangeProj K)).obj F) n) :=
    Module.compHom _ (algebraMap S.k K)
  haveI : IsScalarTower S.k K (cohomologyOverField K (S.baseChange K).f
      ((Scheme.Modules.pullback (S.baseChangeProj K)).obj F) n) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  LinearMap.liftBaseChange K
    { toFun := S.pullbackCohomology K F n
      map_add' := map_add _
      map_smul' := S.pullbackCohomology_smul K F n }

/-- The base change map sends `a ⊗ x` to `a • g^* x`. -/
theorem cohomologyBaseChange_tmul (F : S.X.Modules) [F.IsQuasicoherent] (n : ℕ) (a : K)
    (x : cohomologyOverField S.k S.f F n) :
    S.cohomologyBaseChange K F n (a ⊗ₜ x) = a • S.pullbackCohomology K F n x :=
  let : Module S.k (cohomologyOverField K (S.baseChange K).f
      ((Scheme.Modules.pullback (S.baseChangeProj K)).obj F) n) :=
    Module.compHom _ (algebraMap S.k K)
  have : IsScalarTower S.k K (cohomologyOverField K (S.baseChange K).f
      ((Scheme.Modules.pullback (S.baseChangeProj K)).obj F) n) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  LinearMap.liftBaseChange_tmul _ _ _ _

/-- A `k`-linear functional on `K`, read as a `Γ(Spec k, ⊤)`-linear functional on
`Γ(Spec K, ⊤)` through the two identifications `Γ(Spec R, ⊤) = R`. -/
def baseFunctional (l : K →ₗ[S.k] S.k) :
    letI := baseAlgebra (S.baseChangeBase K)
    Γ(Spec (.of K), ⊤) →ₗ[Γ(Spec (.of S.k), ⊤)] Γ(Spec (.of S.k), ⊤) :=
  letI := baseAlgebra (S.baseChangeBase K)
  { toFun := fun b => (Scheme.ΓSpecIso (.of S.k)).inv.hom (l ((Scheme.ΓSpecIso (.of K)).hom.hom b))
    map_add' := fun b b' => by simp only [map_add]
    map_smul' := fun α b => by
      change (Scheme.ΓSpecIso (.of S.k)).inv.hom (l ((Scheme.ΓSpecIso (.of K)).hom.hom
          (((S.baseChangeBase K).appLE ⊤ ⊤ (le_preimage_top _ ⊤)).hom α * b))) =
        α * (Scheme.ΓSpecIso (.of S.k)).inv.hom (l ((Scheme.ΓSpecIso (.of K)).hom.hom b))
      have e : ((Scheme.ΓSpecIso (.of K)).hom.hom
          (((S.baseChangeBase K).appLE ⊤ ⊤ (le_preimage_top _ ⊤)).hom α)) =
          algebraMap S.k K ((Scheme.ΓSpecIso (.of S.k)).hom.hom α) := by
        rw [Stacks.FormalFunctions.appLE_top_eq_appTop, ← CommRingCat.comp_apply,
          Scheme.ΓSpecIso_naturality]
        rfl
      rw [map_mul, e, ← Algebra.smul_def, map_smul, smul_eq_mul, map_mul]
      congr 1
      exact Iso.hom_inv_id_apply _ _ }

/-- Under the identifications `Γ(Spec R, ⊤) = R`, the functional `baseFunctional K l` is `l`. -/
theorem baseFunctional_apply_inv (l : K →ₗ[S.k] S.k) (a : K) :
    S.baseFunctional K l ((Scheme.ΓSpecIso (.of K)).inv.hom a) =
      (Scheme.ΓSpecIso (.of S.k)).inv.hom (l a) := by
  change (Scheme.ΓSpecIso (.of S.k)).inv.hom (l ((Scheme.ΓSpecIso (.of K)).hom.hom
    ((Scheme.ΓSpecIso (.of K)).inv.hom a))) = _
  rw [Iso.inv_hom_id_apply]

/-- The trace of `l : K ⟶ k` on cohomology, `Hⁿ(X_K, g^*ℱ) = Hⁿ(X, g_* g^* ℱ) ⟶ Hⁿ(X, ℱ)`. -/
def traceCohomology (F : S.X.Modules) [F.IsQuasicoherent] (n : ℕ) (l : K →ₗ[S.k] S.k) :
    cohomologyOverField K (S.baseChange K).f
        ((Scheme.Modules.pullback (S.baseChangeProj K)).obj F) n →+
      cohomologyOverField S.k S.f F n :=
  haveI := S.isAffineHom_baseChangeProj K
  ((((moduleGlobalSections S.X).rightDerived n).map
      (S.baseChangeTrace K F (S.baseFunctional K l))).hom.toAddMonoidHom).comp
    ((Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward (S.baseChangeProj K)
      ((Scheme.Modules.pullback (S.baseChangeProj K)).obj F) n).hom.hom.toAddMonoidHom)

/-- The trace of `l` on cohomology is the comparison `Hⁿ(X_K, g^*ℱ) ≅ Hⁿ(X, g_* g^*ℱ)`
followed by the map induced by the trace `g_* g^*ℱ ⟶ ℱ` of `l`. -/
theorem traceCohomology_apply (F : S.X.Modules) [F.IsQuasicoherent] (n : ℕ)
    (l : K →ₗ[S.k] S.k)
    (v : cohomologyOverField K (S.baseChange K).f
        ((Scheme.Modules.pullback (S.baseChangeProj K)).obj F) n) :
    haveI := S.isAffineHom_baseChangeProj K
    S.traceCohomology K F n l v = (((moduleGlobalSections S.X).rightDerived n).map
      (S.baseChangeTrace K F (S.baseFunctional K l))).hom
        ((Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward (S.baseChangeProj K)
          ((Scheme.Modules.pullback (S.baseChangeProj K)).obj F) n).hom.hom v) := rfl

/-- Multiplying the pullback of a class by `a ∈ K` is the cohomology of the twisted unit. -/
theorem smul_pullbackCohomology (F : S.X.Modules) [F.IsQuasicoherent] (n : ℕ) (a : K)
    (x : cohomologyOverField S.k S.f F n) :
    haveI := S.isAffineHom_baseChangeProj K
    a • S.pullbackCohomology K F n x =
      (Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward (S.baseChangeProj K)
          ((Scheme.Modules.pullback (S.baseChangeProj K)).obj F) n).inv.hom
        ((((moduleGlobalSections S.X).rightDerived n).map
          (Stacks.Tag0CKW.twistedUnit (S.baseChange K).f (S.baseChangeProj K) F
            ((Scheme.ΓSpecIso (.of K)).inv.hom a))).hom x) :=
  Stacks.Tag0CKW.smul_cohomologyPullback (S.isPullback_baseChange K) F n _ x

/-- **The trace undoes the base change up to the functional.** -/
theorem traceCohomology_cohomologyBaseChange_tmul (F : S.X.Modules) [F.IsQuasicoherent]
    (n : ℕ) (l : K →ₗ[S.k] S.k) (a : K) (x : cohomologyOverField S.k S.f F n) :
    S.traceCohomology K F n l (S.cohomologyBaseChange K F n (a ⊗ₜ x)) = l a • x := by
  have := S.isAffineHom_baseChangeProj K
  have h2 : S.traceCohomology K F n l (S.cohomologyBaseChange K F n (a ⊗ₜ x)) =
      (((moduleGlobalSections S.X).rightDerived n).map
        (S.baseChangeTrace K F (S.baseFunctional K l))).hom
        ((Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward (S.baseChangeProj K)
          ((Scheme.Modules.pullback (S.baseChangeProj K)).obj F) n).hom.hom
          ((Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward (S.baseChangeProj K)
            ((Scheme.Modules.pullback (S.baseChangeProj K)).obj F) n).inv.hom
          ((((moduleGlobalSections S.X).rightDerived n).map
            (Stacks.Tag0CKW.twistedUnit (S.baseChange K).f (S.baseChangeProj K) F
              ((Scheme.ΓSpecIso (.of K)).inv.hom a))).hom x))) := by
    rw [cohomologyBaseChange_tmul]
    exact congrArg (S.traceCohomology K F n l) (S.smul_pullbackCohomology K F n a x)
  rw [h2, Iso.inv_hom_id_apply]
  have h3 : (((moduleGlobalSections S.X).rightDerived n).map
        (S.baseChangeTrace K F (S.baseFunctional K l))).hom
        ((((moduleGlobalSections S.X).rightDerived n).map
          (Stacks.Tag0CKW.twistedUnit (S.baseChange K).f (S.baseChangeProj K) F
            ((Scheme.ΓSpecIso (.of K)).inv.hom a))).hom x) =
      (((moduleGlobalSections S.X).rightDerived n).map
        (Stacks.Tag0CKW.twistedUnit (S.baseChange K).f (S.baseChangeProj K) F
            ((Scheme.ΓSpecIso (.of K)).inv.hom a) ≫
          S.baseChangeTrace K F (S.baseFunctional K l))).hom x := by
    rw [Functor.map_comp]
    rfl
  rw [h3, twistedUnit_comp_baseChangeTrace]
  refine (Scheme.rightDerived_sectionsFunctor_map_smulEnd_apply S.X _ n F x).trans ?_
  let x' : ((moduleGlobalSections S.X).rightDerived n).obj F := x
  change _ = ((S.structureRingHom).hom (l a)) • x'
  congr 1
  rw [baseFunctional_apply_inv]
  rfl

/-- **The trace of `l` on `K ⊗_k Hⁿ(X, ℱ)` is `l ⊗ Hⁿ(X, ℱ)`.** -/
theorem traceCohomology_cohomologyBaseChange (F : S.X.Modules) [F.IsQuasicoherent]
    (n : ℕ) (l : K →ₗ[S.k] S.k) (z : K ⊗[S.k] cohomologyOverField S.k S.f F n) :
    S.traceCohomology K F n l (S.cohomologyBaseChange K F n z) =
      TensorProduct.lid S.k _ (LinearMap.rTensor _ l z) := by
  induction z with
  | tmul a x =>
    rw [traceCohomology_cohomologyBaseChange_tmul, LinearMap.rTensor_tmul,
      TensorProduct.lid_tmul]
  | add z w hz hw => simp only [map_add, hz, hw]

/-- The pulled-back module is quasi-coherent. -/
theorem isQuasicoherent_pullback_baseChangeProj (F : S.X.Modules) [F.IsQuasicoherent] :
    ((Scheme.Modules.pullback (S.baseChangeProj K)).obj F).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback _ F

/-- The inverse image of a coherent module on `X` is coherent on `X_K`. -/
theorem isCoherent_pullback_baseChangeProj (F : S.X.Modules) (hF : F.IsCoherent) :
    ((Scheme.Modules.pullback (S.baseChangeProj K)).obj F).IsCoherent := by
  have : IsLocallyNoetherian (S.baseChange K).X :=
    LocallyOfFiniteType.isLocallyNoetherian (S.baseChange K).f
  have : IsLocallyNoetherian S.X := LocallyOfFiniteType.isLocallyNoetherian S.f
  have := hF
  have hq : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  have hft : F.IsFiniteType := SheafOfModules.IsCoherent.isFiniteType
  have : ((Scheme.Modules.pullback (S.baseChangeProj K)).obj F).IsFiniteType :=
    @SheafOfModules.pullback_isFiniteType _ _ (S.baseChangeProj K).toLRSHom.toShHom _ hft
  have := S.isQuasicoherent_pullback_baseChangeProj K F
  exact Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_isQuasicoherent_of_isFiniteType
    _

/-- **The base change map on cohomology is injective**, for every quasi-coherent `ℱ`. -/
theorem cohomologyBaseChange_injective (F : S.X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    Function.Injective (S.cohomologyBaseChange K F n) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  refine Stacks.FlatTrace.eq_zero_of_forall_lid_rTensor_eq_zero z fun l => ?_
  rw [← traceCohomology_cohomologyBaseChange, hz, map_zero]

/-- The base change map on cohomology is bijective when both sides are finite dimensional. -/
private theorem cohomologyBaseChange_bijective_of_finiteDimensional (F : S.X.Modules)
    [F.IsQuasicoherent] (n : ℕ) [FiniteDimensional S.k (cohomologyOverField S.k S.f F n)]
    [FiniteDimensional K (cohomologyOverField K (S.baseChange K).f
      ((Scheme.Modules.pullback (S.baseChangeProj K)).obj F) n)] :
    Function.Bijective (S.cohomologyBaseChange K F n) := by
  have := S.proper
  have hdim := finrank_cohomologyOverField_baseChange_field S.k K (S.baseChangeProj K)
    (S.baseChange K).f S.f (S.isPullback_baseChange K) F n
  refine ⟨S.cohomologyBaseChange_injective K F n, ?_⟩
  refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1
    (S.cohomologyBaseChange_injective K F n)
  rw [Module.finrank_baseChange]
  exact hdim.symm

/-- **[Stacks, Tag 02KH] part (2) for an extension of the ground field, with its map.** For a
coherent `ℱ` the base change map `K ⊗_k Hⁿ(X, ℱ) ⟶ Hⁿ(X_K, g^*ℱ)`, `a ⊗ x ↦ a • g^* x`, is
bijective: it is injective, and both sides have the same finite dimension. -/
theorem cohomologyBaseChange_bijective (F : S.X.Modules) [F.IsQuasicoherent] (hF : F.IsCoherent)
    (n : ℕ) :
    Function.Bijective (S.cohomologyBaseChange K F n) := by
  have : FiniteDimensional S.k (cohomologyOverField S.k S.f F n) :=
    forall_finiteDimensional_cohomologyOverField_of_isProper S.k S.f F hF n
  have := S.proper
  have : FiniteDimensional K (cohomologyOverField K (S.baseChange K).f
      ((Scheme.Modules.pullback (S.baseChangeProj K)).obj F) n) :=
    forall_finiteDimensional_cohomologyOverField_of_isProper (S.baseChange K).k (S.baseChange K).f
      _ (S.isCoherent_pullback_baseChangeProj K F hF) n
  exact S.cohomologyBaseChange_bijective_of_finiteDimensional K F n

/-- **The base change map on cohomology is bijective when `Hⁿ(X, ℱ)` is finite dimensional and
nonzero**: the target then has the same positive finite dimension. -/
theorem cohomologyBaseChange_bijective_of_finrank_pos (F : S.X.Modules) [F.IsQuasicoherent]
    (n : ℕ) [FiniteDimensional S.k (cohomologyOverField S.k S.f F n)]
    (hpos : 0 < Module.finrank S.k (cohomologyOverField S.k S.f F n)) :
    Function.Bijective (S.cohomologyBaseChange K F n) := by
  have := S.proper
  have hdim := finrank_cohomologyOverField_baseChange_field S.k K (S.baseChangeProj K)
    (S.baseChange K).f S.f (S.isPullback_baseChange K) F n
  have : FiniteDimensional K (cohomologyOverField K (S.baseChange K).f
      ((Scheme.Modules.pullback (S.baseChangeProj K)).obj F) n) :=
    FiniteDimensional.of_finrank_pos (hdim ▸ hpos)
  exact S.cohomologyBaseChange_bijective_of_finiteDimensional K F n

/-! ### Naturality -/

section Naturality

variable {S K}

/-- **[Stacks, Tag 089W] read backwards is natural.** -/
theorem cohomologyIsoPushforward_inv_naturality {M M' : (S.baseChange K).X.Modules}
    [M.IsQuasicoherent] [M'.IsQuasicoherent] (φ : M ⟶ M') (n : ℕ)
    (y : ((moduleGlobalSections S.X).rightDerived n).obj
      ((Scheme.Modules.pushforward (S.baseChangeProj K)).obj M)) :
    haveI := S.isAffineHom_baseChangeProj K
    (((moduleGlobalSections (S.baseChange K).X).rightDerived n).map φ).hom
        ((Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward
          (S.baseChangeProj K) M n).inv.hom y) =
      (Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward
          (S.baseChangeProj K) M' n).inv.hom
        ((((moduleGlobalSections S.X).rightDerived n).map
          ((Scheme.Modules.pushforward (S.baseChangeProj K)).map φ)).hom y) := by
  have := S.isAffineHom_baseChangeProj K
  have hnat := Stacks.Tag0CKW.cohomologyIsoPushforward_hom_naturality (S.baseChangeProj K) φ n
  have hinv : (Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward
        (S.baseChangeProj K) M n).inv ≫
      (ModuleCat.restrictScalars (S.baseChangeProj K).appTop.hom).map
        (((moduleGlobalSections (S.baseChange K).X).rightDerived n).map φ) =
      ((moduleGlobalSections S.X).rightDerived n).map
          ((Scheme.Modules.pushforward (S.baseChangeProj K)).map φ) ≫
        (Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward
          (S.baseChangeProj K) M' n).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hnat, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  exact congrArg (fun m => m.hom y) hinv

/-- **The pullback map on cohomology is natural.** -/
theorem cohomologyOverFieldMap_pullback_pullbackCohomology {F G : S.X.Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (u : F ⟶ G) (n : ℕ)
    (x : cohomologyOverField S.k S.f F n) :
    cohomologyOverFieldMap K (S.baseChange K).f
        ((Scheme.Modules.pullback (S.baseChangeProj K)).map u) n (S.pullbackCohomology K F n x) =
      S.pullbackCohomology K G n (cohomologyOverFieldMap S.k S.f u n x) := by
  have := S.isAffineHom_baseChangeProj K
  have := S.isQuasicoherent_pullback_baseChangeProj K F
  have := S.isQuasicoherent_pullback_baseChangeProj K G
  refine (cohomologyOverFieldMap_apply (S.baseChange K).k (S.baseChange K).f _ n _).trans ?_
  refine Eq.trans ?_ (congrArg (S.pullbackCohomology K G n)
    (cohomologyOverFieldMap_apply S.k S.f u n x).symm)
  change (((moduleGlobalSections (S.baseChange K).X).rightDerived n).map
      ((Scheme.Modules.pullback (S.baseChangeProj K)).map u)).hom
      ((Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward
          (S.baseChangeProj K) _ n).inv.hom
        ((((moduleGlobalSections S.X).rightDerived n).map
          ((Scheme.Modules.pullbackPushforwardAdjunction
            (S.baseChangeProj K)).unit.app F)).hom x)) =
    (Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward (S.baseChangeProj K) _ n).inv.hom
        ((((moduleGlobalSections S.X).rightDerived n).map
          ((Scheme.Modules.pullbackPushforwardAdjunction (S.baseChangeProj K)).unit.app G)).hom
          ((((moduleGlobalSections S.X).rightDerived n).map u).hom x))
  rw [cohomologyIsoPushforward_inv_naturality]
  congr 1
  have e : ((Scheme.Modules.pullbackPushforwardAdjunction (S.baseChangeProj K)).unit.app F ≫
      (Scheme.Modules.pushforward (S.baseChangeProj K)).map
        ((Scheme.Modules.pullback (S.baseChangeProj K)).map u)) =
      u ≫ (Scheme.Modules.pullbackPushforwardAdjunction (S.baseChangeProj K)).unit.app G :=
    ((Scheme.Modules.pullbackPushforwardAdjunction (S.baseChangeProj K)).unit.naturality u).symm
  have := congrArg (fun m => (((moduleGlobalSections S.X).rightDerived n).map m).hom x) e
  simp only [Functor.map_comp, ModuleCat.hom_comp] at this
  exact this

/-- Multiplication by `a ∈ K` on `X_K` acts on cohomology as `a`. -/
theorem cohomologyOverFieldMap_smulEnd (M : (S.baseChange K).X.Modules) (n : ℕ) (a : K)
    (y : cohomologyOverField K (S.baseChange K).f M n) :
    cohomologyOverFieldMap K (S.baseChange K).f
        ((Scheme.smulEnd (S.baseChange K).X
          (((S.baseChange K).structureRingHom).hom a)).asHom.app M) n y =
      a • y :=
  (cohomologyOverFieldMap_apply (S.baseChange K).k (S.baseChange K).f _ n y).trans
    (Scheme.rightDerived_sectionsFunctor_map_smulEnd_apply _ _ n M y)

end Naturality

/-! ### Duality transported along the extension of the ground field -/

section Duality

variable {S K}
variable {ω : S.X.Modules} [hωq : ω.IsQuasicoherent]
  (hone : Module.finrank S.k (cohomologyOverField S.k S.f ω 1) = 1)
  (h : S.FirstCohomologyDuality ω)

/-- The trace `t : H¹(X, ω) ⟶ k` of the duality: the functional that `𝟙_ω` corresponds to. -/
def traceForm : cohomologyOverField S.k S.f ω 1 →ₗ[S.k] S.k :=
  h.dual ω hωq (𝟙 ω)

include hωq in
/-- The duality pairs `u : ℱ ⟶ ω` with `t ∘ H¹(u)`. -/
theorem dual_eq_traceForm_comp (F : S.X.Modules) (hF : F.IsQuasicoherent) (u : F ⟶ ω) :
    h.dual F hF u = (traceForm h).comp (cohomologyOverFieldMap S.k S.f u 1).hom := by
  have := h.dual_comp F ω hF hωq u (𝟙 ω)
  rwa [Category.comp_id] at this

variable (K)

include hone in
/-- The base change map is bijective on `H¹(X, ω)`, which is a line. -/
theorem cohomologyBaseChange_bijective_one : Function.Bijective (S.cohomologyBaseChange K ω 1) :=
  have : FiniteDimensional S.k (cohomologyOverField S.k S.f ω 1) :=
    FiniteDimensional.of_finrank_pos (by omega)
  S.cohomologyBaseChange_bijective_of_finrank_pos K ω 1 (by omega)

/-- **The trace of the base change**, `t_K = K ⊗ t : H¹(X_K, g^*ω) = K ⊗_k H¹(X, ω) ⟶ K`. -/
def baseChangeTraceForm :
    cohomologyOverField K (S.baseChange K).f
        ((Scheme.Modules.pullback (S.baseChangeProj K)).obj ω) 1 →ₗ[K] K :=
  ((TensorProduct.AlgebraTensorModule.rid S.k K K).toLinearMap ∘ₗ
      LinearMap.baseChange K (traceForm h)) ∘ₗ
    (LinearEquiv.ofBijective (S.cohomologyBaseChange K ω 1)
      (S.cohomologyBaseChange_bijective_one K hone)).symm.toLinearMap

/-- Precomposed with the base change map `K ⊗_k H¹(X, ω) ⟶ H¹(X_K, g^*ω)`, the trace of the base
change is `K ⊗ t`. -/
theorem baseChangeTraceForm_cohomologyBaseChange
    (z : K ⊗[S.k] cohomologyOverField S.k S.f ω 1) :
    baseChangeTraceForm K hone h (S.cohomologyBaseChange K ω 1 z) =
      TensorProduct.AlgebraTensorModule.rid S.k K K (LinearMap.baseChange K (traceForm h) z) := by
  have : (LinearEquiv.ofBijective (S.cohomologyBaseChange K ω 1)
      (S.cohomologyBaseChange_bijective_one K hone)).symm (S.cohomologyBaseChange K ω 1 z) = z :=
    (LinearEquiv.ofBijective (S.cohomologyBaseChange K ω 1)
      (S.cohomologyBaseChange_bijective_one K hone)).symm_apply_apply z
  simp only [baseChangeTraceForm, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  rw [this]

/-- `t_K` restricts to `t` on the pulled-back classes. -/
theorem baseChangeTraceForm_pullbackCohomology (x : cohomologyOverField S.k S.f ω 1) :
    baseChangeTraceForm K hone h (S.pullbackCohomology K ω 1 x) =
      algebraMap S.k K (traceForm h x) := by
  have e : S.pullbackCohomology K ω 1 x = S.cohomologyBaseChange K ω 1 (1 ⊗ₜ x) := by
    rw [cohomologyBaseChange_tmul, one_smul]
  rw [e, baseChangeTraceForm_cohomologyBaseChange, LinearMap.baseChange_tmul,
    TensorProduct.AlgebraTensorModule.rid_tmul, Algebra.smul_def, mul_one]

/-- **The key identity**: the trace of `l : K ⟶ k`, followed by `t`, is `l ∘ t_K`. -/
theorem traceForm_traceCohomology (l : K →ₗ[S.k] S.k)
    (w : cohomologyOverField K (S.baseChange K).f
        ((Scheme.Modules.pullback (S.baseChangeProj K)).obj ω) 1) :
    traceForm h (S.traceCohomology K ω 1 l w) = l (baseChangeTraceForm K hone h w) := by
  obtain ⟨z, rfl⟩ := (S.cohomologyBaseChange_bijective_one K hone).2 w
  rw [traceCohomology_cohomologyBaseChange, baseChangeTraceForm_cohomologyBaseChange]
  induction z with
  | tmul a x =>
    rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, LinearMap.baseChange_tmul,
      TensorProduct.AlgebraTensorModule.rid_tmul, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
      mul_comm]
  | add z w hz hw => simp only [map_add, hz, hw]

/-- The pairing of a map `ψ : ℱ ⟶ g^*ω` on `X_K` with `t_K`. -/
def basePairing {F : (S.baseChange K).X.Modules}
    (ψ : F ⟶ (Scheme.Modules.pullback (S.baseChangeProj K)).obj ω) :
    cohomologyOverField K (S.baseChange K).f F 1 →ₗ[K] K :=
  (baseChangeTraceForm K hone h).comp (cohomologyOverFieldMap K (S.baseChange K).f ψ 1).hom

end Duality

end CohenMacaulayCurveSituation

end AlgebraicGeometry

end
