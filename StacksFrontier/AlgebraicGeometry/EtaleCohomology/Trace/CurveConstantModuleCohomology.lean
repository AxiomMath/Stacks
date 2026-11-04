module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveConstantSecondCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleCohomologyIntComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafForgetAbelian
public import Mathlib.Algebra.Group.Shrink
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveBoundaryCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapCohomologyExt
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.FinitePointsCohomology
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage

/-!
# `H²` of a smooth proper curve with constant coefficients in modules over a finite ring

Let `C` be a smooth proper curve over an algebraically closed field `K`, let `Λ` be a finite ring
whose cardinality `n` is invertible in `K`, and let `ζ ∈ K` be a primitive `n`-th root of unity.
For a finite `Λ`-module `E` this file gives the `Λ`-linear isomorphism

`τ_E : H²(C, E_C) ≅ E`

of the computation `H²(C, M) = M` in the proof of Tag 03VK, where the cohomology is computed in
sheaves of `Λ`-modules. It is the composite of three identifications:

1. `H²(C, E_C) ≃+ H²(C, (E_C)_ab)`, the cohomology of the underlying abelian sheaf
   (`Stacks.EtaleCohomology.etaleModuleCohomologyAddEquivSheafH`);
2. `(E_C)_ab ≅ E̲`, the constant abelian sheaf (`Stacks.ModuleCatLift.constantSheafForget₂Iso`),
   on a copy of `E` in `Type`;
3. `H²(C, E̲) ≅ Hom(ℤ/n, E) ≅ E`, pushing the fundamental class along `ℤ/n → E`
   (`Stacks.EtaleCohomology.curveConstantClass`) and evaluating at `1`.

The composite is `Λ`-linear because each identification carries multiplication by `a ∈ Λ` to
multiplication by `a` (`Stacks.EtaleCohomology.etaleModuleCohomologyAddEquivSheafH_smul`,
`Stacks.ModuleCatLift.constantSheafForget₂Iso_hom_app_scalar`,
`Stacks.EtaleCohomology.curveConstantClass_naturality`).

## Main definitions

* `Stacks.EtaleCohomology.sheafHAddEquivOfIso` — `Sheaf.H` of an isomorphism of sheaves.
* `Stacks.EtaleCohomology.underlyingConstantSheafIso` — `(E_C)_ab ≅ E̲` through a copy of `E`.
* `Stacks.EtaleCohomology.curveConstantModuleTrace` — `τ_E`.

## Implementation notes

The abelian computation of `H²(C, A)` is stated for groups `A : Type`, while the values of a
sheaf of `Λ`-modules on the small étale site lie in `Type (u + 1)`. A finite `E` is moved to
`Shrink.{0} E` along `Shrink.addEquiv`; nothing depends on the copy chosen.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.EtaleCohomology

/-- `etaleModules_enoughInjectives` at the coefficient universe `0` of this file, which instance
search cannot otherwise reach through the universe `max (u + 1) r`. -/
local instance etaleModulesEnoughInjectivesZero (Λ : Type) [Ring Λ] (Y : Scheme.{u}) :
    EnoughInjectives (EtaleModules.{u, 0} Λ Y) :=
  etaleModules_enoughInjectives.{u, 0} Λ Y

section SheafH

variable {D : Type*} [Category D] {J : GrothendieckTopology D}
  [HasSheafify J AddCommGrpCat.{u + 1}] [HasExt.{u + 1} (Sheaf J AddCommGrpCat.{u + 1})]

/-- **Sheaf cohomology of isomorphic sheaves**: `Hᵐ(F) ≃+ Hᵐ(G)` for `F ≅ G`. -/
def sheafHAddEquivOfIso {F G : Sheaf J AddCommGrpCat.{u + 1}} (e : F ≅ G) (m : ℕ) :
    Sheaf.H.{u + 1} F m ≃+ Sheaf.H.{u + 1} G m where
  toFun := Sheaf.H.map e.hom m
  invFun := Sheaf.H.map e.inv m
  left_inv x := by rw [← Sheaf.H.map_comp_apply, e.hom_inv_id, Sheaf.H.map_id_apply]
  right_inv x := by rw [← Sheaf.H.map_comp_apply, e.inv_hom_id, Sheaf.H.map_id_apply]
  map_add' := map_add _

/-- The equivalence `sheafHAddEquivOfIso e m` acts as the map `Sheaf.H.map e.hom m` on
cohomology. -/
lemma sheafHAddEquivOfIso_apply {F G : Sheaf J AddCommGrpCat.{u + 1}} (e : F ≅ G) (m : ℕ)
    (x : Sheaf.H.{u + 1} F m) : sheafHAddEquivOfIso e m x = Sheaf.H.map e.hom m x := rfl

end SheafH

section Underlying

variable {Λ : Type} [Ring Λ] (Y : Scheme.{u})

/-- **The abelian sheaf underlying the constant sheaf `E_Y` of `Λ`-modules is the constant
abelian sheaf** on a copy `E₀ : Type` of the abelian group underlying `E`. -/
def underlyingConstantSheafIso (E : ModuleCat.{u + 1} Λ) {E₀ : Type} [AddCommGroup E₀]
    (e : E ≃+ E₀) :
    (etaleModuleUnderlyingAbelian Y ℤ).obj ((etaleModuleRestrictScalars (Int.castRingHom Λ) Y).obj
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E)) ≅
      etaleConstantSheaf.{u, 0} Y E₀ :=
  (Stacks.ModuleCatLift.constantSheafForget₂Iso.{u + 1} Λ Y.smallEtaleTopology).app E ≪≫
    (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).mapIso
      (e.trans (AddEquiv.ulift.{0, u + 1} (α := E₀)).symm).toAddCommGrpIso

/-- **The comparison carries multiplication by `a ∈ Λ` to the constant sheaf of the transported
multiplication by `a`.** -/
theorem underlyingConstantSheafIso_hom_smul (E : ModuleCat.{u + 1} Λ) {E₀ : Type}
    [AddCommGroup E₀] (e : E ≃+ E₀) (a : Λ) :
    (etaleModuleUnderlyingAbelian Y ℤ).map
        ((etaleModuleRestrictScalarsNatTrans (Int.castRingHom Λ) (restrictScalarsIntSMul a) Y).app
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E)) ≫
        (underlyingConstantSheafIso Y E e).hom =
      (underlyingConstantSheafIso Y E e).hom ≫
        etaleConstantSheafMap Y (e.toAddMonoidHom.comp
          ((DistribSMul.toAddMonoidHom E a).comp e.symm.toAddMonoidHom)) := by
  show Stacks.ModuleCatLift.sheafScalarEnd.{u + 1} Λ Y.smallEtaleTopology _ a ≫ _ = _
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
    (Stacks.ModuleCatLift.constantSheafForget₂Iso_hom_app_scalar.{u + 1} Λ
      Y.smallEtaleTopology E a)).trans ?_)
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ?_).trans (Category.assoc _ _ _).symm)
  rw [Functor.mapIso_hom, etaleConstantSheafMap, ← Functor.map_comp, ← Functor.map_comp]
  refine congrArg _ ?_
  ext (x : E)
  show e (a • x) = e (a • e.symm (e x))
  rw [e.symm_apply_apply]

/-- **The comparison is natural in the module.** -/
theorem underlyingConstantSheafIso_hom_naturality {E E' : ModuleCat.{u + 1} Λ} (g : E ⟶ E')
    {E₀ E₀' : Type} [AddCommGroup E₀] [AddCommGroup E₀'] (e : E ≃+ E₀) (e' : E' ≃+ E₀') :
    (etaleModuleUnderlyingAbelian Y ℤ).map ((etaleModuleRestrictScalars (Int.castRingHom Λ) Y).map
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map g)) ≫
        (underlyingConstantSheafIso Y E' e').hom =
      (underlyingConstantSheafIso Y E e).hom ≫
        etaleConstantSheafMap Y (e'.toAddMonoidHom.comp
          (g.hom.toAddMonoidHom.comp e.symm.toAddMonoidHom)) := by
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
    ((Stacks.ModuleCatLift.constantSheafForget₂Iso.{u + 1} Λ
      Y.smallEtaleTopology).hom.naturality g)).trans ?_)
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ?_).trans (Category.assoc _ _ _).symm)
  rw [Functor.comp_map, Functor.mapIso_hom, etaleConstantSheafMap, ← Functor.map_comp]
  refine (congrArg (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).map ?_).trans
    (Functor.map_comp (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) _ _)
  ext (x : E)
  show e' (g x) = e' (g (e.symm (e x)))
  rw [e.symm_apply_apply]

end Underlying

section Trace

variable {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}} (q : C ⟶ Spec (.of K))
  [IsCurve K q] [Smooth q] [IsProper q] (Λ : Type) [Ring Λ] [Fintype Λ]
  (hn : IsUnit ((Fintype.card Λ : ℕ) : K)) {ζ : K} (hζ : IsPrimitiveRoot ζ (Fintype.card Λ))

omit [Fintype Λ] in
/-- A module over a finite ring is killed by the cardinality of the ring. -/
lemma card_nsmul_eq_zero_of_module [Fintype Λ] {E : Type*} [AddCommGroup E] [Module Λ E] (x : E) :
    Fintype.card Λ • x = 0 := by
  rw [← smul_one_smul Λ (Fintype.card Λ) x, card_nsmul_eq_zero, zero_smul]

/-- **`Hom(ℤ/n, A) ≃+ A`, `φ ↦ φ(1)`**, for a group `A` killed by `n`. -/
def zmodEvalAddEquiv {n : ℕ} {A : Type} [AddCommGroup A] (hA : ∀ a : A, n • a = 0) :
    (ZMod n →+ A) ≃+ A where
  toFun φ := φ 1
  invFun a := zmodHomOfTorsion hA a
  left_inv φ := zmod_addMonoidHom_ext (by rw [zmodHomOfTorsion_one])
  right_inv a := zmodHomOfTorsion_one hA a
  map_add' _ _ := rfl

/-- The copy in `Type` of a finite `Λ`-module is killed by `#Λ`. -/
lemma shrink_card_nsmul_eq_zero (E : ModuleCat.{u + 1} Λ) [Finite E] (a : Shrink.{0} E) :
    Fintype.card Λ • a = 0 := by
  apply Shrink.addEquiv.injective
  rw [map_nsmul, card_nsmul_eq_zero_of_module Λ, map_zero]

/-- **`τ_E` as an isomorphism of abelian groups**: `H²(C, E_C) ≃+ E`. -/
def curveConstantModuleTraceAddEquiv (E : ModuleCat.{u + 1} Λ) [Finite E] :
    ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).obj
        ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E) ≃+ E :=
  (etaleModuleCohomologyAddEquivSheafH C _ 2).trans
    ((sheafHAddEquivOfIso (underlyingConstantSheafIso C E Shrink.addEquiv.symm) 2).trans
      ((AddEquiv.ofBijective (curveConstantClass q hn hζ (Shrink.{0} E))
          (bijective_curveConstantClass q hn hζ (shrink_card_nsmul_eq_zero Λ E))).symm.trans
        ((zmodEvalAddEquiv (shrink_card_nsmul_eq_zero Λ E)).trans Shrink.addEquiv)))

/-- Evaluating `Θ⁻¹` at `1` is natural in the coefficient group `Shrink E`. -/
private theorem zmodEval_symm_constantSheafMap {E E' : ModuleCat.{u + 1} Λ} [Finite E] [Finite E']
    (g : Shrink.{0} E →+ Shrink.{0} E') (z : Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} C _) 2) :
    zmodEvalAddEquiv (shrink_card_nsmul_eq_zero Λ E')
      ((AddEquiv.ofBijective (curveConstantClass q hn hζ (Shrink.{0} E'))
        (bijective_curveConstantClass q hn hζ (shrink_card_nsmul_eq_zero Λ E'))).symm
          (Sheaf.H.map (etaleConstantSheafMap C g) 2 z)) =
      g (zmodEvalAddEquiv (shrink_card_nsmul_eq_zero Λ E)
        ((AddEquiv.ofBijective (curveConstantClass q hn hζ (Shrink.{0} E))
          (bijective_curveConstantClass q hn hζ (shrink_card_nsmul_eq_zero Λ E))).symm z)) := by
  obtain ⟨φ, rfl⟩ := (AddEquiv.ofBijective (curveConstantClass q hn hζ (Shrink.{0} E))
    (bijective_curveConstantClass q hn hζ (shrink_card_nsmul_eq_zero Λ E))).surjective z
  rw [AddEquiv.symm_apply_apply]
  change _ = zmodEvalAddEquiv (shrink_card_nsmul_eq_zero Λ E') (g.comp φ)
  refine congrArg _ ((AddEquiv.symm_apply_eq
    (AddEquiv.ofBijective (curveConstantClass q hn hζ (Shrink.{0} E'))
      (bijective_curveConstantClass q hn hζ (shrink_card_nsmul_eq_zero Λ E')))).2 ?_)
  exact (curveConstantClass_naturality q hn hζ g φ).symm

/-- **`τ_E` is `Λ`-linear.** -/
theorem curveConstantModuleTraceAddEquiv_smul (E : ModuleCat.{u + 1} Λ) [Finite E] (a : Λ)
    (x : ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).obj
        ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E)) :
    curveConstantModuleTraceAddEquiv q Λ hn hζ E (a • x) =
      a • curveConstantModuleTraceAddEquiv q Λ hn hζ E x := by
  let c : Shrink.{0} E →+ Shrink.{0} E := (Shrink.addEquiv.{0} (α := E)).symm.toAddMonoidHom.comp
    ((DistribSMul.toAddMonoidHom E a).comp (Shrink.addEquiv.{0} (α := E)).symm.symm.toAddMonoidHom)
  simp only [curveConstantModuleTraceAddEquiv, AddEquiv.trans_apply]
  rw [etaleModuleCohomologyAddEquivSheafH_smul, sheafHAddEquivOfIso_apply,
    sheafHAddEquivOfIso_apply, ← Sheaf.H.map_comp_apply, underlyingConstantSheafIso_hom_smul,
    Sheaf.H.map_comp_apply]
  generalize Sheaf.H.map (underlyingConstantSheafIso C E Shrink.addEquiv.symm).hom 2
    (etaleModuleCohomologyAddEquivSheafH C _ 2 x) = z
  rw [zmodEval_symm_constantSheafMap q Λ hn hζ c]
  simp [c]

/-- **`τ_E` is natural in `E`.** -/
theorem curveConstantModuleTraceAddEquiv_naturality {E E' : ModuleCat.{u + 1} Λ} [Finite E]
    [Finite E'] (g : E ⟶ E')
    (x : ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).obj
        ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E)) :
    curveConstantModuleTraceAddEquiv q Λ hn hζ E'
        ((((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
          ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map g)).hom x) =
      g (curveConstantModuleTraceAddEquiv q Λ hn hζ E x) := by
  let c : Shrink.{0} E →+ Shrink.{0} E' := (Shrink.addEquiv.{0} (α := E')).symm.toAddMonoidHom.comp
    (g.hom.toAddMonoidHom.comp (Shrink.addEquiv.{0} (α := E)).symm.symm.toAddMonoidHom)
  simp only [curveConstantModuleTraceAddEquiv, AddEquiv.trans_apply]
  rw [etaleModuleCohomologyAddEquivSheafH_naturality, sheafHAddEquivOfIso_apply,
    sheafHAddEquivOfIso_apply, ← Sheaf.H.map_comp_apply,
    underlyingConstantSheafIso_hom_naturality C g Shrink.addEquiv.symm Shrink.addEquiv.symm,
    Sheaf.H.map_comp_apply]
  generalize Sheaf.H.map (underlyingConstantSheafIso C E Shrink.addEquiv.symm).hom 2
    (etaleModuleCohomologyAddEquivSheafH C _ 2 x) = z
  rw [zmodEval_symm_constantSheafMap q Λ hn hζ c]
  simp [c]

/-- **`τ_E : H²(C, E_C) ≅ E`**, `Λ`-linearly, for a finite `Λ`-module `E`: the computation
`H²(C, M) = M` of the proof of Tag 03VK, through the fundamental class of `C` attached to `ζ`. -/
def curveConstantModuleTrace (E : ModuleCat.{u + 1} Λ) [Finite E] :
    ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).obj
        ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E) ≃ₗ[Λ] E :=
  { curveConstantModuleTraceAddEquiv q Λ hn hζ E with
    map_smul' := curveConstantModuleTraceAddEquiv_smul q Λ hn hζ E }

section Boundary

variable {U : Scheme.{u}} (jC : U ⟶ C) [IsOpenImmersion jC]
  (hfin : ((Set.range jC.base)ᶜ).Finite)

omit [Fintype Λ] [IsCurve K q] [IsProper q] in
include q hfin in
/-- The closed complement of an open immersion into a curve over an algebraically closed field
with finite complement is an affine scheme of closed points with separably closed residue
fields. -/
theorem complement_isAffine_and_isClosed_and_isSepClosed :
    IsAffine (Scheme.IdealSheafData.vanishingIdeal
      ⟨(Set.range jC.base)ᶜ, jC.isOpenEmbedding.isOpen_range.isClosed_compl⟩).subscheme ∧
      (∀ z : (Scheme.IdealSheafData.vanishingIdeal
        ⟨(Set.range jC.base)ᶜ, jC.isOpenEmbedding.isOpen_range.isClosed_compl⟩).subscheme,
        IsClosed ({z} : Set _)) ∧
      ∀ z : (Scheme.IdealSheafData.vanishingIdeal
        ⟨(Set.range jC.base)ᶜ, jC.isOpenEmbedding.isOpen_range.isClosed_compl⟩).subscheme,
        IsSepClosed ↥(Scheme.residueField _ z) := by
  let ι := (Scheme.IdealSheafData.vanishingIdeal
      ⟨(Set.range jC.base)ᶜ, jC.isOpenEmbedding.isOpen_range.isClosed_compl⟩).subschemeι
  have : Finite (Scheme.IdealSheafData.vanishingIdeal
      ⟨(Set.range jC.base)ᶜ, jC.isOpenEmbedding.isOpen_range.isClosed_compl⟩).subscheme := by
    have hr : (Set.range ι.base).Finite := by
      rwa [Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal, TopologicalSpace.Closeds.coe_mk]
    have := hr.to_subtype
    exact Finite.of_injective (fun z => (⟨ι.base z, ⟨z, rfl⟩⟩ : Set.range ι.base))
      fun _ _ h => ι.isClosedEmbedding.injective (congrArg Subtype.val h :)
  -- instance search for `LocallyOfFiniteType` of this closed immersion times out, so the
  -- instance is assembled from `IsClosedImmersion ⇒ IsFinite ⇒ LocallyOfFiniteType`
  have : IsClosedImmersion ι := inferInstanceAs
    (IsClosedImmersion (Scheme.IdealSheafData.vanishingIdeal
      ⟨(Set.range jC.base)ᶜ, jC.isOpenEmbedding.isOpen_range.isClosed_compl⟩).subschemeι)
  have : LocallyOfFiniteType ι :=
    ((IsFinite.iff_isIntegralHom_and_locallyOfFiniteType ι).mp
      ((IsClosedImmersion.iff_isFinite_and_mono ι).mp ‹IsClosedImmersion ι›).1).2
  have : LocallyOfFiniteType q := inferInstance
  have : LocallyOfFiniteType (ι ≫ q) :=
    MorphismProperty.comp_mem @LocallyOfFiniteType _ _ ‹_› ‹_›
  exact isAffine_and_isClosed_and_isSepClosed_of_finite (ι ≫ q)

omit [Fintype Λ] [IsCurve K q] [IsProper q] in
include q hfin in
/-- `H²(C, j_! j^{-1} N) ≅ H²(C, N)` through the counit, for an open `j : U ⟶ C` with finite
complement. -/
theorem isIso_rightDerivedPlus_two_counit_of_finite_compl (N : EtaleModules.{u, 0} Λ C) :
    IsIso (((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus 2).map
      ((etaleModuleExtensionByZeroAdj.{u, 0} Λ jC).counit.app N)) :=
  have h := complement_isAffine_and_isClosed_and_isSepClosed q jC hfin
  have := h.1
  isIso_rightDerivedPlus_two_extensionByZero_counit Λ jC h.2.1 h.2.2 N

/-- **`H²(C, j_!(E_U)) ≅ E`**, `Λ`-linearly, for an open `j : U ⟶ C` with finite complement and a
finite `Λ`-module `E`: `j^{-1}` of the constant sheaf is the constant sheaf, the boundary does not
contribute to `H²`, and `τ_E`. -/
def curveExtensionByZeroConstantTrace (E : ModuleCat.{u + 1} Λ) [Finite E] :
    ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ jC).obj
          ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E)) ≃ₗ[Λ] E :=
  haveI := isIso_rightDerivedPlus_two_counit_of_finite_compl q Λ jC hfin
    ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E)
  ((((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).mapIso
      ((etaleModuleExtensionByZero.{u, 0} Λ jC).mapIso
        (((etaleModuleInverseImageConstantIso.{u, 0} Λ jC).app E).symm ≪≫
          (etaleModuleInverseImageRestrictionIso.{u, 0} Λ jC).app _)) ≪≫
    asIso (((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus 2).map
      ((etaleModuleExtensionByZeroAdj.{u, 0} Λ jC).counit.app
        ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E)))).toLinearEquiv).trans
    (curveConstantModuleTrace q Λ hn hζ E)

/-- **`H²(C, j_!(E_U)) ≅ E` is natural in `E`.** -/
theorem curveExtensionByZeroConstantTrace_naturality {E E' : ModuleCat.{u + 1} Λ} [Finite E]
    [Finite E'] (g : E ⟶ E')
    (x : ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ jC).obj
          ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E))) :
    curveExtensionByZeroConstantTrace q Λ hn hζ jC hfin E'
        ((((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
          ((etaleModuleExtensionByZero.{u, 0} Λ jC).map
            ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map g))).hom x) =
      g (curveExtensionByZeroConstantTrace q Λ hn hζ jC hfin E x) := by
  let J := etaleModuleExtensionByZero.{u, 0} Λ jC
  let cU := constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let cC := constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let a : ∀ E : ModuleCat.{u + 1} Λ,
      cU.obj E ⟶ (etaleModuleRestriction.{u, 0} Λ jC).obj (cC.obj E) :=
    fun E => ((etaleModuleInverseImageConstantIso.{u, 0} Λ jC).app E).inv ≫
      ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ jC).app _).hom
  have ha : cU.map g ≫ a E' = a E ≫ (etaleModuleRestriction.{u, 0} Λ jC).map (cC.map g) := by
    have h1 := (etaleModuleInverseImageConstantIso.{u, 0} Λ jC).inv.naturality g
    have h2 := (etaleModuleInverseImageRestrictionIso.{u, 0} Λ jC).hom.naturality (cC.map g)
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h1).trans
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h2).trans (Category.assoc _ _ _).symm)))
  have key : J.map (cU.map g) ≫ J.map (a E') ≫
        (etaleModuleExtensionByZeroAdj.{u, 0} Λ jC).counit.app (cC.obj E') =
      (J.map (a E) ≫ (etaleModuleExtensionByZeroAdj.{u, 0} Λ jC).counit.app (cC.obj E)) ≫
        cC.map g := by
    rw [← Functor.map_comp_assoc, ha, Functor.map_comp, Category.assoc, Category.assoc]
    exact congrArg (_ ≫ ·)
      ((etaleModuleExtensionByZeroAdj.{u, 0} Λ jC).counit.naturality (cC.map g))
  have hx := congrArg (fun f => f.hom x)
    (congrArg ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map key)
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at hx
  simp only [curveExtensionByZeroConstantTrace, LinearEquiv.trans_apply]
  refine (congrArg (curveConstantModuleTraceAddEquiv q Λ hn hζ E') ?_).trans
    (curveConstantModuleTraceAddEquiv_naturality q Λ hn hζ g _)
  exact hx

end Boundary

end Trace

end Stacks.EtaleCohomology

end
