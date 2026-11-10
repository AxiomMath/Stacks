module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DirectImageFrobeniusTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.BaseChangeQuasiIsoOfDerived
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusTraceQuasiIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ExtensionByZeroIntegralDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.LowerShriekUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TraceFormulaOpenClosedDevissage
public import StacksFrontier.Homology.HomComplex.DerivedAdjunctionResolution

/-!
# The canonical Frobenius trace under a proper direct image, unconditionally

For a proper morphism `h : Z ⟶ Y` of schemes over a finite field `k`, a finite coefficient ring
`Λ` and a bounded below complex `J` of injective sheaves of `Λ`-modules on `Z`, proper base change
([Stacks, Tag 095T], in the form
`Stacks.EtaleCohomology.isIso_etaleModuleUnboundedDerivedBaseChange_of_isProper`) makes the base
change map `(h_* J)|_{Y_k̄} ⟶ (h_k̄)_*(J|_{Z_k̄})` a quasi-isomorphism after resolving, so the
canonical Frobenius traces on `RΓ(Y_k̄, (h_* J)|_{Y_k̄})` and `RΓ(Z_k̄, J|_{Z_k̄})` agree. This is
used in the fibration step of the trace formula in any dimension, [Stacks, Tag 03UI] (1).

The torsion hypothesis of proper base change is carried as `hT`, the statement that every object
of the derived category of sheaves of `Λ`-modules has torsion cohomology sheaves after forgetting
the module structure, which holds for every finite `Λ`.

## Main results

* `baseChangeQuasiIsoAt_fieldBaseChange_of_isProper`.
* `perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_directImage_of_isProper_of_torsion`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.FilteredDerived Stacks.Frobenius

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology

variable (Λ : Type) [Ring Λ]
  (hT : ∀ (X : Scheme.{u}) (E : DerivedCategory (EtaleModules.{u, 0} Λ X)),
    Stacks.Torsion.torsionCohomologyProperty.{u + 1} X.smallEtaleTopology
      ((etaleModuleForgetDerived.{u, 0} Λ X).obj E))
  {k : Type u} [Field k] [Fintype k] {Z Y : Over (Spec (.of k))} (i : Z ⟶ Y) [IsProper i.left]
  (kbar : Type u) [Field kbar] [Algebra k kbar]

omit [Fintype k] in
include hT in
/-- **Proper base change along `Y_k̄ ⟶ Y`, at a bounded below complex of injectives.** -/
theorem baseChangeQuasiIsoAt_fieldBaseChange_of_isProper
    (J : CochainComplex.Plus (EtaleModules.{u, 0} Λ Z.left)) (hJ : ∀ n, Injective (J.obj.X n)) :
    Functor.BaseChangeQuasiIsoAt
      (etaleModuleDirectImage.{u, 0} Λ (fieldBaseChangeMap i kbar))
      (etaleModuleDirectImage.{u, 0} Λ i.left)
      (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar))
      (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Z kbar))
      (etaleModuleBaseChange Λ i.left (fieldBaseChangeMap i kbar)
        (fieldBaseChangeProj Y kbar) (fieldBaseChangeProj Z kbar)
        (fieldBaseChangeMap_comp_fst i kbar)) J := by
  obtain ⟨a, _⟩ := J.property
  exact baseChangeQuasiIsoAt_of_isIso_etaleModuleDerivedBaseChange Λ i.left
    (fieldBaseChangeProj Y kbar) (fieldBaseChangeProj Z kbar) (fieldBaseChangeMap i kbar)
    (fieldBaseChangeMap_comp_fst i kbar) J hJ
    (isIso_etaleModuleUnboundedDerivedBaseChange_of_isProper Λ i.left
      (isPullback_fieldBaseChangeMap i kbar).flip (DerivedCategory.Q.obj J.obj) a
      (hT _ _))

variable (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

include hT in
/-- **The canonical Frobenius trace under a proper direct image.** For a proper morphism
`h : Z ⟶ Y` over `k` and a bounded below complex `J` of injective sheaves on `Z`,
`RΓ(Y_k̄, (h_* J)|_{Y_k̄})` and `RΓ(Z_k̄, J|_{Z_k̄})` are perfect together and the traces of their
canonical Frobenius endomorphisms agree. -/
theorem perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_directImage_of_isProper_of_torsion
    (J : CochainComplex.Plus (EtaleModules.{u, 0} Λ Z.left)) (hJ : ∀ n, Injective (J.obj.X n)) :
    (StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
        ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).obj
          ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
            (fieldBaseChangeRestriction.{u, 0} Λ Y kbar
              ((etaleModuleDirectImage.{u, 0} Λ i.left).mapCochainComplexPlus.obj J))))) ↔
      StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
        ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).obj
          ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Z.hom (specAlgebraMap k kbar))).obj
            (fieldBaseChangeRestriction.{u, 0} Λ Z kbar J))))) ∧
      ∀ hY hZ, perfectDerivedTrace Λ ⟨_, hY⟩ (DerivedCategory.Plus.ι.map
          (frobeniusRestrictionCohomologyEndo.{u, 0} Λ Y kbar p q hcard
            ((etaleModuleDirectImage.{u, 0} Λ i.left).mapCochainComplexPlus.obj J))) =
        perfectDerivedTrace Λ ⟨_, hZ⟩ (DerivedCategory.Plus.ι.map
          (frobeniusRestrictionCohomologyEndo.{u, 0} Λ Z kbar p q hcard J)) := by
  obtain ⟨hiff, htr⟩ :=
    perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_directImage_of_quasiIso Λ i p q hcard
      kbar J (baseChangeQuasiIsoAt_fieldBaseChange_of_isProper Λ hT i kbar J hJ)
  exact ⟨hiff, htr⟩

section Compactification

variable [Finite Λ] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f))

/-- The structure morphism of a compactification, as a morphism of schemes over `k` to `Spec k`. -/
abbrev compactificationToPoint : Over.mk j.toBase ⟶ Over.mk (𝟙 (Spec (.of k))) :=
  Over.homMk j.toBase (Category.comp_id _)

include hT in
/-- **Step A1: `RΓ_c` through `j` is `RΓ(Spec k_k̄, (π_X̄)_* I)`** for a resolution `I` of `j_! K`
by injectives, with the canonical Frobenius: perfect together, with the same trace. -/
theorem canonicalCompactSupportLefschetzNumber_eq_directImage
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X))
    (I : CochainComplex.Plus (EtaleModules.{u, 0} Λ j.space))
    (ψ : (etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.obj K ⟶ I)
    [QuasiIso ψ.hom] (hI : ∀ n, Injective (I.obj.X n)) :
    (StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
        (compactSupportFrobeniusCohomology.{u, 0} Λ f j kbar K)) ↔
      StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
        ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).obj
          ((etaleModuleDerivedDirectImage.{u, 0} Λ
              (pullback.snd (Over.mk (𝟙 (Spec (.of k)))).hom (specAlgebraMap k kbar))).obj
            (fieldBaseChangeRestriction.{u, 0} Λ (Over.mk (𝟙 (Spec (.of k)))) kbar
              ((etaleModuleDirectImage.{u, 0} Λ j.toBase).mapCochainComplexPlus.obj I)))))) ∧
      ∀ h₁ h₂, canonicalCompactSupportLefschetzNumber.{u, 0} Λ f j kbar p q hcard K h₁ =
        perfectDerivedTrace Λ ⟨_, h₂⟩ (DerivedCategory.Plus.ι.map
          (frobeniusRestrictionCohomologyEndo.{u, 0} Λ (Over.mk (𝟙 (Spec (.of k)))) kbar p q hcard
            ((etaleModuleDirectImage.{u, 0} Λ j.toBase).mapCochainComplexPlus.obj I))) := by
  have : IsProper (compactificationToPoint f j).left := inferInstanceAs (IsProper j.toBase)
  obtain ⟨hiff₂, htr₂⟩ :=
    perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_directImage_of_isProper_of_torsion
      Λ hT (compactificationToPoint f j) kbar p q hcard I hI
  have hiff₁ := isPerfect_frobeniusRestriction_iff_of_quasiIso Λ (Over.mk j.toBase) kbar ψ
  refine ⟨hiff₁.trans hiff₂.symm, fun h₁ h₂ => ?_⟩
  have hI' := hiff₁.1 h₁
  exact (perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_of_quasiIso_of_isPerfect Λ
    (Over.mk j.toBase) kbar p q hcard ψ h₁ hI').trans (htr₂ h₂ hI').symm

omit [Finite Λ] [Fintype k] in
/-- **Step A2: `Rf_! K ≅ Q((π_X̄)_* I)`** on the unbounded derived category of `Spec k`, for a
resolution `I` of `j_! K` by injectives. -/
theorem nonempty_derivedLowerShriekUnboundedIsoDirectImage
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X))
    (I : CochainComplex.Plus (EtaleModules.{u, 0} Λ j.space))
    (ψ : (etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.obj K ⟶ I)
    [QuasiIso ψ.hom] (hI : ∀ n, Injective (I.obj.X n)) :
    Nonempty (DerivedCategory.Q.obj
        ((etaleModuleDirectImage.{u, 0} Λ j.toBase).mapCochainComplexPlus.obj I).obj ≅
      (derivedLowerShriekUnbounded.{u, 0} f j Λ).obj (DerivedCategory.Q.obj K.obj)) := by
  obtain ⟨b, _⟩ := I.property
  have := hI
  have : I.obj.IsKInjective := CochainComplex.isKInjective_of_injective I.obj b
  -- `Rj_!(Q K) ≅ Q(j_! K)`, through an injective resolution of `K`
  have : EnoughInjectives (EtaleModules.{u, 0} Λ X) := etaleModules_enoughInjectives.{u, 0} Λ X
  obtain ⟨R, ρ, hρ, hR, -, -⟩ := Functor.exists_twist_lift_of_injectiveResolution
    (𝟭 (EtaleModules.{u, 0} Λ X)) K (𝟙 _)
  obtain ⟨c, _⟩ := R.property
  have := hR
  have : R.obj.IsKInjective := CochainComplex.isKInjective_of_injective R.obj c
  have := isIso_etaleModuleDerivedExtensionByZeroUnboundedUnit_app.{u, 0} Λ j.immersion R.obj
    inferInstance
  have : IsIso (DerivedCategory.Q.map ρ.hom) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ ρ.hom).2 hρ
  have : QuasiIso (((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapHomologicalComplex
      (ComplexShape.up ℤ)).map ρ.hom) := inferInstance
  have : IsIso (DerivedCategory.Q.map (((etaleModuleExtensionByZero.{u, 0} Λ
      j.immersion).mapHomologicalComplex (ComplexShape.up ℤ)).map ρ.hom)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  have hnat :=
    (etaleModuleDerivedExtensionByZeroUnboundedUnit.{u, 0} Λ j.immersion).naturality ρ.hom
  simp only [Functor.comp_map] at hnat
  have hu₁ : IsIso
      ((etaleModuleDerivedExtensionByZeroUnboundedUnit.{u, 0} Λ j.immersion).app K.obj) := by
    have : IsIso ((etaleModuleDerivedExtensionByZeroUnboundedUnit.{u, 0} Λ j.immersion).app K.obj ≫
        (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ j.immersion).map
          (DerivedCategory.Q.map ρ.hom)) := by
      rw [← hnat]; infer_instance
    exact IsIso.of_isIso_comp_right _ ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
      j.immersion).map (DerivedCategory.Q.map ρ.hom))
  have hu₂ := isIso_etaleModuleDerivedDirectImageUnboundedUnit_app.{u, 0} Λ j.toBase I.obj
    inferInstance
  have hψQ : IsIso (DerivedCategory.Q.map ψ.hom) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ ψ.hom).2 inferInstance
  exact ⟨@asIso _ _ _ _ _ hu₂ ≪≫
    (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ j.toBase).mapIso
      ((@asIso _ _ _ _ _ hψQ).symm ≪≫ @asIso _ _ _ _ _ hu₁)⟩

end Compactification

section Independence

variable [Finite Λ] [IsAlgClosed kbar] [CharP kbar p] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [QuasiCompact f]

include hT in
/-- **Independence of the compactification, one direction.** -/
theorem canonicalTraceFormula_of_compactification (j₁ j₂ : CompactificationOf (Over.mk f))
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X))
    (h : CanonicalTraceFormula Λ kbar p q hcard f j₁ K) :
    CanonicalTraceFormula Λ kbar p q hcard f j₂ K := by
  obtain ⟨hX₁, hs, heq⟩ := h
  have : EnoughInjectives (EtaleModules.{u, 0} Λ j₁.space) :=
    etaleModules_enoughInjectives.{u, 0} Λ j₁.space
  have : EnoughInjectives (EtaleModules.{u, 0} Λ j₂.space) :=
    etaleModules_enoughInjectives.{u, 0} Λ j₂.space
  obtain ⟨I₁, ψ₁, hψ₁, hI₁, -, -⟩ := Functor.exists_twist_lift_of_injectiveResolution
    (𝟭 (EtaleModules.{u, 0} Λ j₁.space))
    ((etaleModuleExtensionByZero.{u, 0} Λ j₁.immersion).mapCochainComplexPlus.obj K) (𝟙 _)
  obtain ⟨I₂, ψ₂, hψ₂, hI₂, -, -⟩ := Functor.exists_twist_lift_of_injectiveResolution
    (𝟭 (EtaleModules.{u, 0} Λ j₂.space))
    ((etaleModuleExtensionByZero.{u, 0} Λ j₂.immersion).mapCochainComplexPlus.obj K) (𝟙 _)
  obtain ⟨hiff₁, htr₁⟩ := canonicalCompactSupportLefschetzNumber_eq_directImage Λ hT kbar p q hcard
    f j₁ K I₁ ψ₁ hI₁
  obtain ⟨hiff₂, htr₂⟩ := canonicalCompactSupportLefschetzNumber_eq_directImage Λ hT kbar p q hcard
    f j₂ K I₂ ψ₂ hI₂
  obtain ⟨E₁⟩ := nonempty_derivedLowerShriekUnboundedIsoDirectImage Λ f j₁ K I₁ ψ₁ hI₁
  obtain ⟨E₂⟩ := nonempty_derivedLowerShriekUnboundedIsoDirectImage Λ f j₂ K I₂ ψ₂ hI₂
  obtain ⟨n, _⟩ := K.property
  have : (DerivedCategory.Q.obj K.obj).IsGE n :=
    (DerivedCategory.isGE_Q_obj_iff _ _).2 inferInstance
  let e := E₁ ≪≫ derivedLowerShriekUnboundedIndependenceIso Λ j₁ j₂ (DerivedCategory.Q.obj K.obj)
    n (hT _ _) ≪≫ E₂.symm
  -- the target is K-injective
  let C₂ := (etaleModuleDirectImage.{u, 0} Λ j₂.toBase).mapCochainComplexPlus.obj I₂
  obtain ⟨b, _⟩ := C₂.property
  have : ∀ m, Injective (C₂.obj.X m) := fun m =>
    have := hI₂ m
    inferInstanceAs (Injective ((etaleModuleDirectImage.{u, 0} Λ j₂.toBase).obj (I₂.obj.X m)))
  have : C₂.obj.IsKInjective := CochainComplex.isKInjective_of_injective C₂.obj b
  obtain ⟨φ, hφ⟩ := StacksDraft.DerivedHom.exists_eq_Q_map_of_isKInjective _ C₂.obj e.hom
  have hφq : QuasiIso φ := (DerivedCategory.isIso_Q_map_iff_quasiIso _ φ).1 (hφ ▸ inferInstance)
  let Φ : (etaleModuleDirectImage.{u, 0} Λ j₁.toBase).mapCochainComplexPlus.obj I₁ ⟶ C₂ :=
    ObjectProperty.homMk φ
  have : QuasiIso Φ.hom := hφq
  have hiffΦ := isPerfect_frobeniusRestriction_iff_of_quasiIso Λ (Over.mk (𝟙 (Spec (.of k)))) kbar Φ
  have hC₁ := hiff₁.1 hX₁
  have hC₂ := hiffΦ.1 hC₁
  have hX₂ := hiff₂.2 hC₂
  refine ⟨hX₂, hs, ?_⟩
  rw [htr₂ hX₂ hC₂,
    ← perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_of_quasiIso_of_isPerfect Λ
      (Over.mk (𝟙 (Spec (.of k)))) kbar p q hcard Φ hC₁ hC₂, ← htr₁ hX₁ hC₁, heq]

include hT in
/-- **The trace formula does not depend on the compactification**, in any dimension: it holds
for `K` through one compactification of `X` over `k` exactly when it holds through any other. -/
theorem canonicalTraceFormula_iff_of_compactifications (j₁ j₂ : CompactificationOf (Over.mk f))
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) :
    CanonicalTraceFormula Λ kbar p q hcard f j₁ K ↔ CanonicalTraceFormula Λ kbar p q hcard f j₂ K :=
  ⟨canonicalTraceFormula_of_compactification Λ hT kbar p q hcard f j₁ j₂ K,
    canonicalTraceFormula_of_compactification Λ hT kbar p q hcard f j₂ j₁ K⟩

end Independence

end Stacks.EtaleCohomology

end
