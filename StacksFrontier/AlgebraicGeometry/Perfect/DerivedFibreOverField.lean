module

public import StacksFrontier.AlgebraicGeometry.ModuleSpecGammaAdditive
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFibreEulerCharacteristic
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.EulerCharacteristic
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# The derived fibre of a direct image over a field is the cohomology

Let `K` be a field, `g : Y ⟶ Spec K` a morphism of schemes and `ℱ` an `𝒪_Y`-module. The object
`Rg_*ℱ` of `D(𝒪_{Spec K})` has derived fibre at the unique point of `Spec K`, and the dimension
of its `i`-th cohomology is the dimension of the sheaf cohomology `H^i(Y, ℱ)` over `K`:

`dim_{κ(s)} H^i(Rg_*ℱ ⊗^L κ(s)) = dim_K H^i(Y, ℱ)`.

## Main definitions

* `AlgebraicGeometry.DerivedFibreOverField.pushforwardCompSectionsIso`: global sections over
  `Spec K` of a direct image are global sections over `Y`, `K`-linearly.
* `AlgebraicGeometry.DerivedFibreOverField.sectionsHomologyDerivedPushforwardIso`: the
  `K`-linear isomorphism `Γ(Spec K, H^n(Rg_*ℱ)) ≅ H^n(Y, ℱ)`, the target being
  `AlgebraicGeometry.cohomologyOverField`.

## Main results

* `AlgebraicGeometry.DerivedFibreOverField.derivedFiberBetti_specField`: on the spectrum of a
  field the derived-fibre Betti number is the dimension of the global sections of the
  cohomology.
* `AlgebraicGeometry.DerivedFibreOverField.derivedFiberBetti_derivedPushforwardModule`:
  the derived-fibre Betti number of `Rg_*ℱ` in degree `n ≥ 0` is `dim_K H^n(Y, ℱ)`, and
  `derivedFiberBetti_derivedPushforwardModule_of_neg` that it vanishes in negative degrees.
* `AlgebraicGeometry.DerivedFibreOverField.chiDerivedFibre_derivedPushforwardModule`: the
  derived-fibre Euler characteristic of `Rg_*ℱ` is `∑ (-1)^n dim_K H^n(Y, ℱ)`, and
  `chiDerivedFibre_derivedPushforwardModule_eq_eulerCharacteristic` that it is
  `AlgebraicGeometry.eulerCharacteristic` for `g` proper and `ℱ` coherent.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

namespace AlgebraicGeometry.DerivedFibreOverField

universe u

attribute [local instance] HasDerivedCategory.standard

variable (K : Type u) [Field K] {Y : Scheme.{u}} (g : Y ⟶ Spec (.of K))

/-- The structure homomorphism `K → Γ(Y, 𝒪_Y)` of a scheme over `K`. -/
abbrev sectionsRingHom : CommRingCat.of K →+* Y.ringCatSheaf.obj.obj (op ⊤) :=
  ((Scheme.ΓSpecIso (.of K)).inv ≫ g.appLE ⊤ ⊤ (by simp)).hom

/-- Global sections over `Spec K` of a direct image are global sections over `Y`, as
`K`-modules: `Γ(Spec K, g_*ℱ) = Γ(g⁻¹(Spec K), ℱ) = Γ(Y, ℱ)`, the identity on elements. -/
def pushforwardCompSectionsIso :
    modulePushforward g.toLRSHom.toShHom ⋙ moduleSpecΓFunctor ≅
      SheafOfModules.evaluation Y.ringCatSheaf (op ⊤) ⋙
        ModuleCat.restrictScalars (sectionsRingHom K g) :=
  NatIso.ofComponents (fun F =>
    let A := (modulePushforward g.toLRSHom.toShHom ⋙ moduleSpecΓFunctor).obj F
    let B := (SheafOfModules.evaluation Y.ringCatSheaf (op ⊤) ⋙
        ModuleCat.restrictScalars (sectionsRingHom K g)).obj F
    let e : A →ₗ[CommRingCat.of K] B :=
      { toFun := fun x => x
        map_add' := fun _ _ => rfl
        map_smul' := fun k x => by
          change HSMul.hSMul (α := (structureSheafRing Y.toRingedSpace).obj.obj (op ⊤))
            (β := F.val.obj (op ⊤)) _ x =
            HSMul.hSMul (α := (structureSheafRing Y.toRingedSpace).obj.obj (op ⊤))
            (β := F.val.obj (op ⊤)) _ x
          congr 1
          have h₁ : (initialOpOfTerminal isTerminalTop).to (op (⊤ : (Spec (.of K)).Opens)) =
            𝟙 _ := Subsingleton.elim _ _
          have h₂ : (homOfLE (le_refl (⊤ : Y.Opens))).op = 𝟙 (op ⊤) := Subsingleton.elim _ _
          rw [h₁]
          simp only [ObjectProperty.ι_obj, Functor.comp_obj, Functor.op_obj, Opens.map_top,
            RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, CategoryTheory.Functor.map_id,
            RingCat.hom_id, RingHom.coe_monoidHom_id, MonoidHom.toOneHom_coe, MonoidHom.coe_id,
            ZeroHom.coe_mk, id_eq, CommRingCat.hom_comp, Scheme.Hom.appLE, homOfLE_leOfHom, h₂,
            RingHom.id_apply]
          rfl }
    { hom := ModuleCat.ofHom (X := A) (Y := B) e
      inv := ModuleCat.ofHom (X := B) (Y := A)
        { toFun := fun x => x
          map_add' := fun _ _ => rfl
          map_smul' := fun k x => (e.map_smul k x).symm }
      hom_inv_id := rfl
      inv_hom_id := rfl }) (fun _ => rfl)

variable (F : Y.Modules)

/-- With `J` the chosen injective resolution of `ℱ` extended by zero to `ℤ`, `Rg_*ℱ ≅ g_*J` in
`D(𝒪_{Spec K})`. -/
def derivedPushforwardModuleIsoResolution :
    ProperFlatFibreEulerCharacteristic.derivedPushforwardModule g F ≅
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj
        (((modulePushforward g.toLRSHom.toShHom).mapHomologicalComplex (.up ℤ)).obj
          (injectiveResolution F).cochainComplex)) :=
  have hQ : IsIso (DerivedCategory.Q.map (injectiveResolution F).ι') :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  have hK : (injectiveResolution F).cochainComplex.IsKInjective :=
    CochainComplex.isKInjective_of_injective _ 0
  have : IsIso ((derivedPushforwardUnit g.toLRSHom.toShHom).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj (injectiveResolution F).cochainComplex)) :=
    isIso_derivedPushforwardUnit_app_of_isKInjective g.toLRSHom.toShHom _ hK
  (derivedPushforward g.toLRSHom.toShHom).mapIso
      (@asIso _ _ _ _ (DerivedCategory.Q.map (injectiveResolution F).ι') hQ ≪≫
        (DerivedCategory.quotientCompQhIso _).symm.app _) ≪≫
    (asIso ((derivedPushforwardUnit g.toLRSHom.toShHom).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj (injectiveResolution F).cochainComplex))).symm

/-- The direct image `g_*J` of the chosen injective resolution, as a complex of
`𝒪_{Spec K}`-modules. -/
abbrev pushforwardResolution : HomologicalComplex (Spec (.of K)).Modules (.up ℤ) :=
  ((modulePushforward g.toLRSHom.toShHom).mapHomologicalComplex (.up ℤ)).obj
    (injectiveResolution F).cochainComplex

/-- The global sections `Γ(Y, J)` of the chosen injective resolution, as a complex of
`Γ(Y, 𝒪_Y)`-modules. -/
abbrev sectionsResolution :
    HomologicalComplex (ModuleCat (Y.ringCatSheaf.obj.obj (op ⊤))) (.up ℤ) :=
  ((SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)).mapHomologicalComplex (.up ℤ)).obj
    (injectiveResolution F).cochainComplex

/-- The cohomology sheaves of `Rg_*ℱ` are the homology of `g_*J`. -/
def homologyDerivedPushforwardModuleIso (i : ℤ) :
    (DerivedCategory.homologyFunctor (Spec (.of K)).Modules i).obj
        (ProperFlatFibreEulerCharacteristic.derivedPushforwardModule g F) ≅
      (pushforwardResolution K g F).homology i :=
  (DerivedCategory.homologyFunctor _ i).mapIso (derivedPushforwardModuleIsoResolution K g F) ≪≫
    (DerivedCategory.homologyFunctorFactorsh _ i).app _ ≪≫
    (HomotopyCategory.homologyFunctorFactors _ _ i).app _

/-- `Γ(Spec K, g_*J) ≅ Γ(Y, J)` as complexes of `K`-modules, termwise
`pushforwardCompSectionsIso`. -/
def sectionsComplexIso :
    (moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj (pushforwardResolution K g F) ≅
      ((ModuleCat.restrictScalars (sectionsRingHom K g)).mapHomologicalComplex (.up ℤ)).obj
        (sectionsResolution F) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (pushforwardCompSectionsIso K g).app ((injectiveResolution F).cochainComplex.X n))
    (fun i j _ => ((pushforwardCompSectionsIso K g).hom.naturality
      ((injectiveResolution F).cochainComplex.d i j)).symm)

/-- Global sections over `Spec K` of the homology of `g_*J` are the homology of `Γ(Y, J)`,
`K`-linearly. -/
def sectionsHomologyIso (i : ℤ) :
    moduleSpecΓFunctor.obj ((pushforwardResolution K g F).homology i) ≅
      (ModuleCat.restrictScalars (sectionsRingHom K g)).obj
        ((sectionsResolution F).homology i) :=
  have : (moduleSpecΓFunctor (R := .of K)).IsEquivalence :=
    (SpecField.modulesEquiv (Field.toIsField K)).isEquivalence_inverse
  have hexact : PreservesFiniteLimits (ModuleCat.restrictScalars (sectionsRingHom K g)) ∧
      PreservesFiniteColimits (ModuleCat.restrictScalars (sectionsRingHom K g)) :=
    ((Functor.exact_tfae (ModuleCat.restrictScalars (sectionsRingHom K g))).out 2 4).mp
      fun S hS => by
        rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
        exact hS
  have := hexact.1
  have := hexact.2
  ((pushforwardResolution K g F).sc i |>.mapHomologyIso moduleSpecΓFunctor).symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ i).mapIso (sectionsComplexIso K g F) ≪≫
    ((sectionsResolution F).sc i |>.mapHomologyIso
      (ModuleCat.restrictScalars (sectionsRingHom K g)))

/-- `H^n(Y, ℱ)` over `K` is the homology of `Γ(Y, J)`, with scalars restricted to `K`. -/
def cohomologyOverFieldIsoHomology (n : ℕ) :
    cohomologyOverField K g F n ≅
      (ModuleCat.restrictScalars (sectionsRingHom K g)).obj
        ((sectionsResolution F).homology n) :=
  (ModuleCat.restrictScalars (sectionsRingHom K g)).mapIso
    ((Stacks.DerivedIndexing.rightDerivedIsoRes
        (SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)) n).app F ≪≫
      (HomotopyCategory.homologyFunctorFactors _ _ (n : ℤ)).app _)

/-- `Γ(Spec K, H^n(Rg_*ℱ)) ≅ H^n(Y, ℱ)` as `K`-modules, for `n ≥ 0`. -/
def sectionsHomologyDerivedPushforwardIso (n : ℕ) :
    moduleSpecΓFunctor.obj ((DerivedCategory.homologyFunctor (Spec (.of K)).Modules n).obj
        (ProperFlatFibreEulerCharacteristic.derivedPushforwardModule g F)) ≅
      cohomologyOverField K g F n :=
  moduleSpecΓFunctor.mapIso (homologyDerivedPushforwardModuleIso K g F n) ≪≫
    sectionsHomologyIso K g F n ≪≫ (cohomologyOverFieldIsoHomology K g F n).symm

/-- `Rg_*ℱ` has no cohomology in negative degrees. -/
theorem isZero_homology_derivedPushforwardModule_of_neg {i : ℤ} (hi : i < 0) :
    IsZero ((DerivedCategory.homologyFunctor (Spec (.of K)).Modules i).obj
        (ProperFlatFibreEulerCharacteristic.derivedPushforwardModule g F)) :=
  IsZero.of_iso (((pushforwardResolution K g F).sc i).isZero_homology_of_isZero_X₂
      ((modulePushforward g.toLRSHom.toShHom).map_isZero
        ((injectiveResolution F).cochainComplex.isZero_of_isStrictlyGE 0 i hi)))
    (homologyDerivedPushforwardModuleIso K g F i)

/-- On the spectrum of a field the derived-fibre Betti number is the dimension of the global
sections of the cohomology. -/
theorem derivedFiberBetti_specField (E : DerivedCategory (Spec (.of K)).Modules)
    (hE : RingedSpace.IsPseudoCoherent (X := (Spec (.of K)).toRingedSpace) E) (i : ℤ)
    (pt : Spec (.of K)) :
    DerivedFibreBetti.derivedFiberBetti (Spec (.of K)) E hE i pt =
      Module.finrank K (moduleSpecΓFunctor.obj
        ((DerivedCategory.homologyFunctor (Spec (.of K)).Modules i).obj E)) := by
  rw [DerivedFibreBetti.derivedFiberBetti_apply]
  have key : ∀ {S : CommRingCat.{u}} (hS : IsField S) (f : Spec S ⟶ Spec (.of K)),
      Module.finrank S ((moduleSpecΓFunctor (R := S)).obj
        ((DerivedCategory.homologyFunctor (Spec S).Modules i).obj
          ((derivedPullback f.toLRSHom.toShHom).obj E))) =
      Module.finrank K (moduleSpecΓFunctor.obj
        ((DerivedCategory.homologyFunctor (Spec (.of K)).Modules i).obj E)) := by
    intro S hS f
    obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ = f := ⟨_, Spec.map_preimage f⟩
    have := SpecField.hasLeftDerivedFunctor_pullbackOnHomotopy_SpecMap (Field.toIsField K) hS φ
    exact SpecField.finrank_derivedPullback (Field.toIsField K) hS φ E i
  exact key (Field.toIsField _) _

variable (hE : RingedSpace.IsPseudoCoherent (X := (Spec (.of K)).toRingedSpace)
  (ProperFlatFibreEulerCharacteristic.derivedPushforwardModule g F))

/-- For `n ≥ 0`, the `n`-th derived-fibre Betti number of `Rg_*ℱ` at the point of `Spec K` is
`dim_K H^n(Y, ℱ)`. -/
theorem derivedFiberBetti_derivedPushforwardModule (n : ℕ) (pt : Spec (.of K)) :
    DerivedFibreBetti.derivedFiberBetti (Spec (.of K))
        (ProperFlatFibreEulerCharacteristic.derivedPushforwardModule g F) hE n pt =
      Module.finrank K (cohomologyOverField K g F n) := by
  rw [derivedFiberBetti_specField]
  exact (sectionsHomologyDerivedPushforwardIso K g F n).toLinearEquiv.finrank_eq

/-- The derived-fibre Betti numbers of `Rg_*ℱ` at the point of `Spec K` vanish in negative
degrees. -/
theorem derivedFiberBetti_derivedPushforwardModule_of_neg {i : ℤ} (hi : i < 0)
    (pt : Spec (.of K)) :
    DerivedFibreBetti.derivedFiberBetti (Spec (.of K))
        (ProperFlatFibreEulerCharacteristic.derivedPushforwardModule g F) hE i pt = 0 := by
  rw [derivedFiberBetti_specField]
  have := ModuleCat.subsingleton_of_isZero
    (moduleSpecΓFunctor.map_isZero (isZero_homology_derivedPushforwardModule_of_neg K g F hi))
  exact Module.finrank_zero_of_subsingleton

/-- The derived-fibre Euler characteristic of `Rg_*ℱ` at the point of `Spec K` is
`∑ (-1)^n dim_K H^n(Y, ℱ)`. -/
theorem chiDerivedFibre_derivedPushforwardModule (pt : Spec (.of K)) :
    DerivedFibreBetti.chiDerivedFibre (Spec (.of K))
        (ProperFlatFibreEulerCharacteristic.derivedPushforwardModule g F) hE pt =
      ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank K (cohomologyOverField K g F n) : ℤ) := by
  rw [DerivedFibreBetti.chiDerivedFibre_apply]
  set f : ℤ → ℤ := fun i => (i.negOnePow : ℤ) *
    (DerivedFibreBetti.derivedFiberBetti (Spec (.of K))
      (ProperFlatFibreEulerCharacteristic.derivedPushforwardModule g F) hE i pt : ℤ)
  have hsupp : Set.univ ∩ Function.support f = Set.range ((↑) : ℕ → ℤ) ∩ Function.support f := by
    ext i
    simp only [Set.univ_inter, Set.mem_inter_iff, Set.mem_range, Function.mem_support,
      iff_and_self]
    intro hi
    refine ⟨i.toNat, Int.toNat_of_nonneg (not_lt.1 fun hneg => hi ?_)⟩
    simp only [f, derivedFiberBetti_derivedPushforwardModule_of_neg K g F hE hneg,
      Nat.cast_zero, mul_zero]
  rw [← finsum_mem_univ, finsum_mem_inter_support_eq f _ _ hsupp,
    finsum_mem_range Nat.cast_injective]
  refine finsum_congr fun n => ?_
  simp only [f, derivedFiberBetti_derivedPushforwardModule, Int.coe_negOnePow_natCast]

/-- The derived-fibre Euler characteristic of `Rg_*ℱ` over a field is the Euler characteristic
`χ(Y, ℱ)` of `AlgebraicGeometry.eulerCharacteristic`, for `g` proper and `ℱ` coherent. -/
theorem chiDerivedFibre_derivedPushforwardModule_eq_eulerCharacteristic [IsProper g]
    [F.IsCoherent] (pt : Spec (.of K)) :
    DerivedFibreBetti.chiDerivedFibre (Spec (.of K))
        (ProperFlatFibreEulerCharacteristic.derivedPushforwardModule g F) hE pt =
      eulerCharacteristic K g F :=
  chiDerivedFibre_derivedPushforwardModule K g F hE pt

end AlgebraicGeometry.DerivedFibreOverField
