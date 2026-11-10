module

public import StacksFrontier.AlgebraicGeometry.Perfect.CohomologyAndBaseChangeVanishing
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatGlobalSectionsKernelModel
public import StacksFrontier.Homology.MappingConeSingle
public import StacksFrontier.Homology.Perfect.PerfectConeDegreeZeroLift
public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsBaseRing
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ReducedConnected
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingExtension
public import StacksFrontier.AlgebraicGeometry.Cohomology.LocallyNoetherian.StructureSheafCoherent
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres
public import StacksFrontier.AlgebraicGeometry.Flatness.ExtendingFromOpen.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Cohomology.MinimalComplexFunctoriality.FibreCycleLift

/-!
# The Čech cohomology of a proper smooth family of curves is locally free

Let `A` be a Noetherian ring, `f : X ⟶ Spec A` a proper morphism, `F` a coherent `𝒪_X`-module flat
over `A` and `s` a global section of `F`, and let `U` be a finite affine cover of `X` with affine
finite intersections. If over the fibre `X_p` at a prime `p` the map `κ(p) ⟶ Γ(X_p, F_p)`,
`c ↦ c • s` is bijective and `F_p` has no cohomology in degrees `≥ 2`, then near `p` the
`A`-linear alternating Čech complex of `F` has free homology of finite rank in every degree.

The argument is that of the proof of [Stacks, Tag 0GKA]. The map `A ⟶ RΓ(X, F)` of `s` has a
mapping cone `K` which is perfect ([Stacks, Tag 07VK] (1) and [Stacks, Tag 066R]) and whose
derived fibre at `p` is concentrated in degree `1`, the fibre of the map being an isomorphism in
degree `0`. So near `p` the cone is a free module placed in degree `1`
(`StacksDraft.Perfect.exists_away_iso_singleFunctor_free_of_fibre_concentrated`), and the long
exact sequence of the cone gives `H⁰ = A_g`, `H¹` free and `Hⁱ = 0` for `i ≥ 2`.

For `f` proper smooth with geometrically connected fibres of dimension at most `1` and
`(F, s) = (𝒪_X, 1)` the two fibre conditions are [Stacks, Tag 0BUG] and [Stacks, Tag 02UZ].

## Main results

* `Stacks.AlgebraicGeometry.CurveCechCohomology.quasiIsoAt_zero_baseChange_sectionUnit`: after a
  base change, the map of a section is a quasi-isomorphism in degree `0` when the section is a
  basis of the global sections.
* `Stacks.AlgebraicGeometry.CurveCechCohomology.exists_away_free_homology`: the general
  statement.
* `Stacks.AlgebraicGeometry.CurveCechCohomology.exists_away_free_homology_of_smooth`: the case
  of a proper smooth family of geometrically connected curves.

## References

* [Stacks Project, Tag 0GKA](https://stacks.math.columbia.edu/tag/0GKA)
* [Stacks Project, Tag 07VK](https://stacks.math.columbia.edu/tag/07VK)
* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ProperFlatGlobalSections
open StacksDraft.Perfect.FibreCycleLift (unitComplex)

universe u

namespace Stacks.AlgebraicGeometry.CurveCechCohomology

attribute [local instance 10000] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
  {I : Type u} [Fintype I] [LinearOrder I] (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i)

/-- The structure sheaf of `X`, as a module over itself. -/
abbrev unitModule (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

/-- A global section `s` of `F` as a degree-`0` cocycle of the Čech model. -/
def sectionCochain (F : X.Modules) (s : Γ(F, ⊤)) : (baseAlternatingCechComplex f U hU F).X 0 :=
  sectionsToModel f U hU F s

omit [Fintype I] [LinearOrder I] in
/-- The cochain of a global section is a cocycle. -/
theorem sectionCochain_mem_ker (F : X.Modules) (s : Γ(F, ⊤)) :
    sectionCochain f U hU F s ∈
      LinearMap.ker ((baseAlternatingCechComplex f U hU F).d 0 1).hom := by
  rw [← range_sectionsToModel]
  exact ⟨s, rfl⟩

/-- The degree-`0` component of `sectionUnit`: `a ↦ a • s`, read in the Čech cochains. -/
def sectionUnitZero (F : X.Modules) (s : Γ(F, ⊤)) :
    ModuleCat.of A A ⟶ (baseAlternatingCechComplex f U hU F).X 0 :=
  ConcreteCategory.ofHom (C := ModuleCat.{u} A) (X := ModuleCat.of A A)
    (Y := (baseAlternatingCechComplex f U hU F).X 0) (@LinearMap.toSpanSingleton A
      ((baseAlternatingCechComplex f U hU F).X 0) _ _
      ((baseAlternatingCechComplex f U hU F).X 0).isModule (sectionCochain f U hU F s))

omit [Fintype I] [LinearOrder I] in
/-- `sectionUnitZero f U hU F s` sends `a` to `a • sectionCochain f U hU F s`. -/
theorem sectionUnitZero_apply (F : X.Modules) (s : Γ(F, ⊤)) (a : A) :
    sectionUnitZero f U hU F s a = a • sectionCochain f U hU F s := rfl

/-- **The map `A ⟶ RΓ(X, F)` of a global section `s`**, from `A` placed in degree `0` to the Čech
model, sending `a` to the cocycle `a • s`. -/
def sectionUnit (F : X.Modules) (s : Γ(F, ⊤)) :
    (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj (ModuleCat.of A A) ⟶
      baseAlternatingCechComplex f U hU F :=
  HomologicalComplex.mkHomFromSingle (sectionUnitZero f U hU F s) (by
    rintro k (rfl : (0 : ℤ) + 1 = k)
    refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
    refine (congrArg ((baseAlternatingCechComplex f U hU F).d 0 (0 + 1)).hom
      (one_smul A (sectionCochain f U hU F s))).trans ?_
    exact LinearMap.mem_ker.1 (sectionCochain_mem_ker f U hU F s))

omit [Fintype I] [LinearOrder I] in
/-- The degree-`0` component of `sectionUnit` is `sectionUnitZero`, through the identification of
the degree-`0` term of `A[0]` with `A`. -/
theorem sectionUnit_f_zero (F : X.Modules) (s : Γ(F, ⊤)) :
    (sectionUnit f U hU F s).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)).hom ≫
        sectionUnitZero f U hU F s :=
  HomologicalComplex.mkHomFromSingle_f _ _

/-- **The unit `A ⟶ RΓ(X, 𝒪_X)`.** -/
abbrev cechUnit : (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj
    (ModuleCat.of A A) ⟶ baseAlternatingCechComplex f U hU (unitModule X) :=
  sectionUnit f U hU (unitModule X) (show Γ(unitModule X, ⊤) from (1 : Γ(X, ⊤)))

section Algebra

/-- The cycles map of a morphism of short complexes of modules, read through the identification of
cycles with kernels, is the restriction of its middle component. -/
theorem moduleCatCyclesIso_inv_cyclesMap_hom {R : Type u} [CommRing R]
    {S₁ S₂ : ShortComplex (ModuleCat.{u} R)} (φ : S₁ ⟶ S₂) :
    S₁.moduleCatCyclesIso.inv ≫ ShortComplex.cyclesMap φ ≫ S₂.moduleCatCyclesIso.hom =
      ModuleCat.ofHom (φ.τ₂.hom.restrict (p := LinearMap.ker S₁.g.hom)
        (q := LinearMap.ker S₂.g.hom) (map_mem_ker_g φ)) := by
  have key : ∀ x, φ.τ₂.hom.restrict (p := LinearMap.ker S₁.g.hom)
      (q := LinearMap.ker S₂.g.hom) (map_mem_ker_g φ) x =
      (S₁.moduleCatCyclesIso.inv ≫ ShortComplex.cyclesMap φ ≫ S₂.moduleCatCyclesIso.hom) x :=
    fun x => by
      apply Subtype.ext
      rw [LinearMap.coe_restrict_apply]
      have a1 := congr($(S₂.moduleCatCyclesIso_hom_i).hom
        (ShortComplex.cyclesMap φ (S₁.moduleCatCyclesIso.inv x)))
      have a2 := congr($(ShortComplex.cyclesMap_i φ).hom (S₁.moduleCatCyclesIso.inv x))
      have a3 := congr($(S₁.moduleCatCyclesIso_inv_iCycles).hom x)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at a1 a2 a3
      exact (congrArg φ.τ₂.hom a3.symm).trans (a2.symm.trans a1.symm)
  ext x
  exact (key x).symm

/-- **A morphism of short complexes of modules with vanishing first maps is a
quasi-isomorphism** when it is bijective on the kernels of the second maps. -/
theorem quasiIso_of_bijective_restrict {R : Type u} [CommRing R]
    {S₁ S₂ : ShortComplex (ModuleCat.{u} R)} (φ : S₁ ⟶ S₂)
    (hf₁ : S₁.f = 0) (hf₂ : S₂.f = 0)
    (h : Function.Bijective (φ.τ₂.hom.restrict (p := LinearMap.ker S₁.g.hom)
      (q := LinearMap.ker S₂.g.hom) (map_mem_ker_g φ))) :
    ShortComplex.QuasiIso φ := by
  have h1 := S₁.isIso_homologyπ hf₁
  have h2 := S₂.isIso_homologyπ hf₂
  have hr : IsIso (ModuleCat.ofHom (φ.τ₂.hom.restrict (p := LinearMap.ker S₁.g.hom)
      (q := LinearMap.ker S₂.g.hom) (map_mem_ker_g φ))) :=
    (ConcreteCategory.isIso_iff_bijective _).2 h
  have hc : IsIso (ShortComplex.cyclesMap φ) := by
    have e : ShortComplex.cyclesMap φ = S₁.moduleCatCyclesIso.hom ≫
        (S₁.moduleCatCyclesIso.inv ≫ ShortComplex.cyclesMap φ ≫ S₂.moduleCatCyclesIso.hom) ≫
          S₂.moduleCatCyclesIso.inv := by
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
    rw [e, moduleCatCyclesIso_inv_cyclesMap_hom]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance
      (@IsIso.comp_isIso _ _ _ _ _ _ _ hr inferInstance)
  refine ⟨?_⟩
  have e : ShortComplex.homologyMap φ =
      inv S₁.homologyπ ≫ ShortComplex.cyclesMap φ ≫ S₂.homologyπ := by
    rw [← ShortComplex.homologyπ_naturality, IsIso.inv_hom_id_assoc]
  rw [e]
  infer_instance

/-- **A morphism of cochain complexes of modules whose differentials into degree `0` vanish is a
quasi-isomorphism in degree `0`** when it is bijective on the kernels of the differentials out of
degree `0`. This is the converse of `bijective_kerRestrict`. -/
theorem quasiIsoAt_zero_of_bijective_kerRestrict {R : Type u} [CommRing R]
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (T : K ⟶ L) (hK : K.d (-1) 0 = 0)
    (hL : L.d (-1) 0 = 0) (h : Function.Bijective (kerRestrict T)) : QuasiIsoAt T 0 :=
  (quasiIsoAt_iff' T (-1) 0 1 (by simp) (by simp)).2
    (quasiIso_of_bijective_restrict
      ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} R) (ComplexShape.up ℤ) (-1) 0 1).map
        T) hK hL h)

end Algebra

section BaseChangeUnit

open scoped ChangeOfRings _root_.TensorProduct

variable {B B' : Type u} [CommRing B] [CommRing B'] (ψ : B →+* B')

variable {X' X'' : Scheme.{u}} {f' : X' ⟶ Spec (.of B)} [IsSeparated f']
  {f'' : X'' ⟶ Spec (.of B')} {g'' : X'' ⟶ X'}
  (hsq : IsPullback g'' f'' f' (Spec.map (CommRingCat.ofHom ψ))) (F : X'.Modules)
  [F.IsQuasicoherent] {J : Type u} [Finite J] [LinearOrder J] (V : J → X'.Opens)
  (hV : (⊤ : X'.Opens) = ⨆ i, V i) (hVaff : ∀ i, IsAffineOpen (V i)) (s : Γ(F, ⊤))

/-- `c ⊗ x` in `B' ⊗_B M`, typed as an element of the extension of scalars. -/
abbrev extTmul {M : ModuleCat.{u} B} (c : B') (x : M) :
    (ModuleCat.extendScalars.{u, u, u} ψ).obj M :=
  c ⊗ₜ[B, ψ] x

/-- `1 ⊗ (b • x) = ψ b • (1 ⊗ x)` in `B' ⊗_B M`. -/
theorem extTmul_smul {M : ModuleCat.{u} B} (b : B) (x : M) :
    extTmul ψ (1 : B') (b • x) = ψ b • extTmul ψ (1 : B') x :=
  map_smul ((ModuleCat.extendRestrictScalarsAdj ψ).unit.app M).hom b x

/-- `c ↦ c • g^* s`, followed by the Čech cochain of a section. -/
def pulledSectionMap (f'' : X'' ⟶ Spec (.of B')) (g'' : X'' ⟶ X') :
    ModuleCat.of B' B' ⟶ (baseAlternatingCechComplex f'' (fun j => g'' ⁻¹ᵁ V j)
      (top_eq_iSup_preimage g'' V hV) ((Scheme.Modules.pullback g'').obj F)).X 0 :=
  letI M := (baseAlternatingCechComplex f'' (fun j => g'' ⁻¹ᵁ V j)
    (top_eq_iSup_preimage g'' V hV) ((Scheme.Modules.pullback g'').obj F)).X 0
  ConcreteCategory.ofHom (C := ModuleCat.{u} B') (X := ModuleCat.of B' B') (Y := M)
    (@LinearMap.toSpanSingleton B' M _ _ M.isModule
      (sectionsToModel f'' (fun j => g'' ⁻¹ᵁ V j) (top_eq_iSup_preimage g'' V hV)
        ((Scheme.Modules.pullback g'').obj F)
        (AlgebraicGeometry.pullbackSectionHom g'' F ⊤ ⊤ (by simp) s)))

omit [SheafOfModules.IsQuasicoherent F] [Finite J] [LinearOrder J] in
/-- `pulledSectionMap` sends `c` to the Čech cochain of `c • g^* s`. -/
theorem pulledSectionMap_apply (f'' : X'' ⟶ Spec (.of B')) (g'' : X'' ⟶ X') (c : B') :
    letI := Stacks.Cech.sectionsModule f'' ((Scheme.Modules.pullback g'').obj F) ⊤
    pulledSectionMap F V hV s f'' g'' c =
      sectionsToModel f'' (fun j => g'' ⁻¹ᵁ V j) (top_eq_iSup_preimage g'' V hV)
        ((Scheme.Modules.pullback g'').obj F)
        (c • AlgebraicGeometry.pullbackSectionHom g'' F ⊤ ⊤ (by simp) s) := by
  let := Stacks.Cech.sectionsModule f'' ((Scheme.Modules.pullback g'').obj F) ⊤
  exact (LinearMap.map_smul _ c _).symm

omit [LinearOrder J] in
include hsq hVaff in
/-- The base change of the degree-`0` component of the map of `s` is `c ↦ c • g^* s`. -/
theorem extendScalars_map_sectionUnitZero_comp :
    (ModuleCat.extendScalars.{u, u, u} ψ).map (sectionUnitZero f' V hV F s) ≫
      (baseAlternatingCechComplexBaseChangeIso ψ hsq F V hV hVaff).hom.f 0 =
      (ModuleCat.ExtendScalars.objSelfIso ψ).hom ≫ pulledSectionMap F V hV s f'' g'' := by
  refine ModuleCat.ExtendScalars.hom_ext_one_tmul ψ fun m => ?_
  change (baseAlternatingCechComplexBaseChangeIso ψ hsq F V hV hVaff).hom.f 0
      (extTmul ψ (1 : B') (m • sectionCochain f' V hV F s)) =
    pulledSectionMap F V hV s f'' g'' ((ModuleCat.ExtendScalars.objSelfIso ψ).hom (extTmul ψ 1 m))
  refine (congrArg ((baseAlternatingCechComplexBaseChangeIso ψ hsq F V hV hVaff).hom.f 0)
    (extTmul_smul ψ m (sectionCochain f' V hV F s))).trans ?_
  refine (LinearMap.map_smul _ _ _).trans ?_
  refine (congrArg (ψ m • ·) (baseChangeIso_sectionsToModel ψ hsq F V hV hVaff s)).trans ?_
  refine Eq.trans ?_
    (congrArg (pulledSectionMap F V hV s f'' g'')
      (ModuleCat.ExtendScalars.objSelfIso_hom_tmul ψ 1 m)).symm
  exact congrArg (· • _) (one_mul (ψ m)).symm

omit [LinearOrder J] in
include hsq hVaff in
/-- The degree-`0` component of the base change of the map of `s` is `c ↦ c • g^* s`. -/
private theorem extendScalars_map_sectionUnit_comp_f_zero :
    (((ModuleCat.extendScalars.{u, u, u} ψ).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (sectionUnit f' V hV F s) ≫
      (baseAlternatingCechComplexBaseChangeIso ψ hsq F V hV hVaff).hom).f 0 =
      ((ModuleCat.extendScalars.{u, u, u} ψ).mapIso
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of B B)) ≪≫
        ModuleCat.ExtendScalars.objSelfIso ψ).hom ≫ pulledSectionMap F V hV s f'' g'' := by
  rw [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, sectionUnit_f_zero,
    Functor.map_comp, Category.assoc, extendScalars_map_sectionUnitZero_comp ψ hsq F V hV hVaff s]
  rfl

/-- After any extension of scalars, `B[0]` has no differential into degree `0`. -/
private theorem extendScalars_single_d_neg_one_zero :
    (((ModuleCat.extendScalars.{u, u, u} ψ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((HomologicalComplex.single (ModuleCat.{u} B) (ComplexShape.up ℤ) 0).obj
        (ModuleCat.of B B))).d (-1) 0 = 0 :=
  ((ModuleCat.extendScalars.{u, u, u} ψ).map_isZero
    (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega))).eq_of_src _ _

/-- After any extension of scalars, `B[0]` has no differential out of degree `0`. -/
private theorem extendScalars_single_d_zero_one :
    (((ModuleCat.extendScalars.{u, u, u} ψ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((HomologicalComplex.single (ModuleCat.{u} B) (ComplexShape.up ℤ) 0).obj
        (ModuleCat.of B B))).d 0 1 = 0 :=
  ((ModuleCat.extendScalars.{u, u, u} ψ).map_isZero
    (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by decide))).eq_of_tgt _ _

omit [LinearOrder J] in
/-- **After a base change, the map of a global section is a quasi-isomorphism in degree `0`**
when scalar multiplication on the pulled back section, `c ↦ c • g^* s`, is a bijection from the
new base ring onto the global sections of `g^* F`. -/
theorem quasiIsoAt_zero_baseChange_sectionUnit
    (hbij : Function.Bijective (fun c : B' =>
      letI := Stacks.Cech.sectionsModule f'' ((Scheme.Modules.pullback g'').obj F) ⊤
      c • AlgebraicGeometry.pullbackSectionHom g'' F ⊤ ⊤ (by simp) s)) :
    QuasiIsoAt (((ModuleCat.extendScalars.{u, u, u} ψ).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (sectionUnit f' V hV F s) ≫
      (baseAlternatingCechComplexBaseChangeIso ψ hsq F V hV hVaff).hom) 0 := by
  let := Stacks.Cech.sectionsModule f'' ((Scheme.Modules.pullback g'').obj F) ⊤
  let eB := baseAlternatingCechComplexBaseChangeIso ψ hsq F V hV hVaff
  let V'' := fun j => g'' ⁻¹ᵁ V j
  let hV'' := top_eq_iSup_preimage g'' V hV
  let F'' := (Scheme.Modules.pullback g'').obj F
  let t : Γ(F'', ⊤) := AlgebraicGeometry.pullbackSectionHom g'' F ⊤ ⊤ (by simp) s
  let Ψ := pulledSectionMap F V hV s f'' g''
  have hΨ : ∀ c : B', Ψ c = sectionsToModel f'' V'' hV'' F'' (c • t) :=
    pulledSectionMap_apply F V hV s f'' g''
  let θ : (((ModuleCat.extendScalars.{u, u, u} ψ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((HomologicalComplex.single (ModuleCat.{u} B) (ComplexShape.up ℤ) 0).obj
        (ModuleCat.of B B))).X 0 ≅ ModuleCat.of B' B' :=
    (ModuleCat.extendScalars.{u, u, u} ψ).mapIso
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of B B)) ≪≫
      ModuleCat.ExtendScalars.objSelfIso ψ
  have hf0 : ∀ x, (((ModuleCat.extendScalars.{u, u, u} ψ).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (sectionUnit f' V hV F s) ≫ eB.hom).f 0 x = Ψ (θ.hom x) := by
    have h : (((ModuleCat.extendScalars.{u, u, u} ψ).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (sectionUnit f' V hV F s) ≫ eB.hom).f 0 = θ.hom ≫ Ψ :=
      extendScalars_map_sectionUnit_comp_f_zero ψ hsq F V hV hVaff s
    intro x
    rw [h]
    rfl
  have hC : (baseAlternatingCechComplex f'' V'' hV'' F'').d (-1) 0 = 0 :=
    (isZero_baseAlternatingCechComplex_X_of_neg f'' V'' hV'' F'' (-1) (by omega)).eq_of_src _ _
  refine quasiIsoAt_zero_of_bijective_kerRestrict _ (extendScalars_single_d_neg_one_zero ψ) hC
    ⟨?_, ?_⟩
  · intro x y hxy
    have hxy' := congrArg Subtype.val hxy
    simp only [kerRestrict_apply_coe] at hxy'
    rw [hf0, hf0, hΨ, hΨ] at hxy'
    exact Subtype.ext (θ.toLinearEquiv.injective
      (hbij.1 (sectionsToModel_injective f'' V'' hV'' F'' hxy')))
  · rintro ⟨y, hy⟩
    rw [← range_sectionsToModel] at hy
    obtain ⟨t', rfl⟩ := hy
    obtain ⟨c, hc⟩ := hbij.2 t'
    refine ⟨⟨θ.inv c, ?_⟩, Subtype.ext ?_⟩
    · rw [LinearMap.mem_ker, extendScalars_single_d_zero_one ψ]
      rfl
    · simp only [kerRestrict_apply_coe]
      rw [hf0, hΨ]
      change sectionsToModel f'' V'' hV'' F'' ((θ.hom (θ.inv c)) • t) = _
      rw [← ModuleCat.comp_apply θ.inv, Iso.inv_hom_id, ModuleCat.id_apply]
      exact congrArg _ hc

end BaseChangeUnit

section Derived

open CochainComplex.DerivedExtensionScalars

/-- A module isomorphic to the zero module is free and finite. -/
theorem free_finite_of_isZero {R : Type u} [CommRing R] {M : ModuleCat.{u} R} (hM : IsZero M) :
    Module.Free R M ∧ Module.Finite R M := by
  have := ModuleCat.subsingleton_of_isZero hM
  exact ⟨inferInstance, inferInstance⟩

/-- Freeness and finiteness are invariant under isomorphism of modules. -/
theorem free_finite_of_iso {R : Type u} [CommRing R] {M N : ModuleCat.{u} R} (e : M ≅ N)
    (h : Module.Free R N ∧ Module.Finite R N) : Module.Free R M ∧ Module.Finite R M :=
  have := h.1
  have := h.2
  ⟨Module.Free.of_equiv e.toLinearEquiv.symm, Module.Finite.equiv e.toLinearEquiv.symm⟩

variable {B : Type u} [CommRing B] (φ : A →+* B)

/-- The terms of `A[0]` in nonzero degrees are zero. -/
theorem isZero_singleA_X (n : ℤ) (hn : n ≠ 0) : IsZero ((unitComplex A).X n) :=
  HomologicalComplex.isZero_single_obj_X _ _ _ _ hn

/-- After any extension of scalars, `A[0]` has homology only in degree `0`. -/
theorem isZero_homology_extendScalars_singleA (n : ℤ) (hn : n ≠ 0) :
    IsZero ((((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (unitComplex A)).homology n) :=
  ShortComplex.isZero_homology_of_isZero_X₂ _
    ((ModuleCat.extendScalars.{u, u, u} φ).map_isZero (isZero_singleA_X (A := A) n hn))

/-- After any extension of scalars, the degree-`0` homology of `A[0]` is free and finite. -/
private theorem free_finite_homology_zero_extendScalars_singleA :
    Module.Free B ((((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (unitComplex A)).homology 0) ∧
      Module.Finite B ((((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (unitComplex A)).homology 0) := by
  let E := (ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℤ)
  let e0 : (E.obj (unitComplex A)).homology 0 ≅ ModuleCat.of B B :=
    ((E.obj (unitComplex A)).isoHomologyπ (-1) 0 (by simp)
        (extendScalars_single_d_neg_one_zero φ)).symm ≪≫
      (E.obj (unitComplex A)).iCyclesIso 0 1 (by simp) (extendScalars_single_d_zero_one φ) ≪≫
      (ModuleCat.extendScalars.{u, u, u} φ).mapIso
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)) ≪≫
      ModuleCat.ExtendScalars.objSelfIso φ
  exact free_finite_of_iso e0 ⟨inferInstance, inferInstance⟩

/-- `A[0]` is perfect. -/
theorem isPerfect_Q_singleA :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj (unitComplex A)) := by
  refine ⟨unitComplex A, 0, 0, inferInstance, inferInstance, fun i => ?_, fun i => ?_, ⟨Iso.refl _⟩⟩
  · rcases eq_or_ne i 0 with rfl | hi
    · exact Module.Finite.equiv (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (ModuleCat.of A A)).toLinearEquiv.symm
    · exact (free_finite_of_isZero (isZero_singleA_X (A := A) i hi)).2
  · rcases eq_or_ne i 0 with rfl | hi
    · exact Module.Projective.of_equiv (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (ModuleCat.of A A)).toLinearEquiv.symm
    · have := (free_finite_of_isZero (isZero_singleA_X (A := A) i hi)).1
      infer_instance

/-- Every term of `A[0]` is a flat `A`-module. -/
instance flat_singleA_X (i : ℤ) : Module.Flat A ((unitComplex A).X i) := by
  rcases eq_or_ne i 0 with rfl | hi
  · exact Module.Flat.of_linearEquiv (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (ModuleCat.of A A)).toLinearEquiv
  · have := (free_finite_of_isZero (isZero_singleA_X (A := A) i hi)).1
    infer_instance

/-- The homology of a bounded above complex of flat modules after derived extension of scalars
is that of its termwise extension of scalars. -/
def homologyTotalDerivedExtensionScalarsIso (K : CochainComplex (ModuleCat.{u} A) ℤ) (b : ℤ)
    [K.IsStrictlyLE b] [∀ i, Module.Flat A (K.X i)] (j : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} B) j).obj
        ((totalDerivedExtensionScalars.{u, u, u} φ).functor.obj (DerivedCategory.Q.obj K)) ≅
      (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K).homology j :=
  have := TotalDerivedExtensionScalars.comparison_isIso_of_flat
    (totalDerivedExtensionScalars.{u, u, u} φ) K b
  (DerivedCategory.homologyFunctor (ModuleCat.{u} B) j).mapIso (@asIso _ _ _ _ _ this) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} B) j).app _

end Derived

section Main

open CochainComplex.DerivedExtensionScalars

variable (F : X.Modules) [F.IsQuasicoherent]

/-- The alternating Čech complex of a cover indexed by `I` vanishes above degree `#I`. -/
instance isStrictlyLE_baseAlternatingCechComplex :
    (baseAlternatingCechComplex f U hU F).IsStrictlyLE (Fintype.card I : ℤ) := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact isZero_baseAlternatingCechComplex_X_of_card_le f U hU F i (by omega)

/-- `A[0]` vanishes above degree `#I`. -/
instance isStrictlyLE_singleA : (unitComplex A).IsStrictlyLE (Fintype.card I : ℤ) := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact isZero_singleA_X (A := A) i (by omega)

/-- The homology of the derived extension of scalars of a mapping cone of flat modules is the
homology of the mapping cone of the termwise extension of scalars. -/
private def homologyDerivedMappingConeIso {B : Type u} [CommRing B] (φ : A →+* B)
    {K L : CochainComplex (ModuleCat.{u} A) ℤ} (η : K ⟶ L) (b : ℤ)
    [∀ i, Module.Flat A ((CochainComplex.mappingCone η).X i)]
    [(CochainComplex.mappingCone η).IsStrictlyLE b] (j : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} B) j).obj
        ((totalDerivedExtensionScalars.{u, u, u} φ).functor.obj
          (DerivedCategory.Q.obj (CochainComplex.mappingCone η))) ≅
      (CochainComplex.mappingCone
        (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).map
          η)).homology j :=
  homologyTotalDerivedExtensionScalarsIso φ (CochainComplex.mappingCone η) b j ≪≫
    (HomologicalComplex.homologyFunctor _ _ j).mapIso
      (CochainComplex.mappingCone.mapHomologicalComplexIso η
        (ModuleCat.extendScalars.{u, u, u} φ))

omit [Fintype I] in
/-- **The cone of the map of a section has its fibre cohomology in degree `1` only.** -/
theorem finrank_derivedFibreHomology_mappingCone_eq_zero [Finite I] [IsSeparated f]
    (hUaff : ∀ i, IsAffineOpen (U i)) (hflat : IsFlatOver f.toLRSHom.toShHom F) (s : Γ(F, ⊤))
    (p : Ideal A) [p.IsPrime] {Xp : Scheme.{u}} {fp : Xp ⟶ Spec (.of p.ResidueField)}
    {gp : Xp ⟶ X}
    (hsq : IsPullback gp fp f (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))))
    (hbij : Function.Bijective (fun c : p.ResidueField =>
      letI := Stacks.Cech.sectionsModule fp ((Scheme.Modules.pullback gp).obj F) ⊤
      c • AlgebraicGeometry.pullbackSectionHom gp F ⊤ ⊤ (by simp) s))
    (hvan : ∀ i : ℕ, 2 ≤ i → Subsingleton
      (((moduleGlobalSections Xp).rightDerived i).obj ((Scheme.Modules.pullback gp).obj F)))
    (j : ℤ) (hj : j ≠ 1) :
    Module.finrank p.ResidueField (StacksDraft.Perfect.derivedFibreHomology.{u, u} p
      (DerivedCategory.Q.obj (CochainComplex.mappingCone (sectionUnit f U hU F s))) j) = 0 := by
  let _ : Fintype I := Fintype.ofFinite I
  have : ((Scheme.Modules.pullback gp).obj F).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback gp F
  let ψ := algebraMap A p.ResidueField
  let E := (ModuleCat.extendScalars.{u, u, u} ψ).mapHomologicalComplex (ComplexShape.up ℤ)
  let η := sectionUnit f U hU F s
  have : ∀ i, Module.Flat A ((baseAlternatingCechComplex f U hU F).X i) :=
    flat_baseAlternatingCechComplex_X f U hU F hUaff hflat
  have : ∀ i, Module.Flat A ((CochainComplex.mappingCone η).X i) :=
    StacksDraft.ConeLift.flat_mappingCone_X η
  have := StacksDraft.ConeLift.isStrictlyLE_mappingCone η (Fintype.card I : ℤ)
  let eB := baseAlternatingCechComplexBaseChangeIso ψ hsq F U hU hUaff
  have hC : ∀ n : ℤ, n ≠ 0 → n ≠ 1 →
      IsZero ((E.obj (baseAlternatingCechComplex f U hU F)).homology n) := by
    intro n h0 h1
    rcases lt_or_gt_of_ne h0 with hneg | hpos
    · exact ShortComplex.isZero_homology_of_isZero_X₂ _
        ((ModuleCat.extendScalars.{u, u, u} ψ).map_isZero
          (isZero_baseAlternatingCechComplex_X_of_neg f U hU F n hneg))
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hpos.le
      refine IsZero.of_iso ?_ ((HomologicalComplex.homologyFunctor _ _ (m : ℤ)).mapIso eB ≪≫
        homologyBaseAlternatingCechComplexIso fp _ (top_eq_iSup_preimage gp U hU) _
          (iInf_preimage_isAffineOpen ψ hsq U hUaff) m)
      exact @ModuleCat.isZero_of_subsingleton _ _ _ (hvan m (by omega))
  have hiso : IsIso (HomologicalComplex.homologyMap (E.map η) 0) := by
    have hq := quasiIsoAt_zero_baseChange_sectionUnit ψ hsq F U hU hUaff s hbij
    rw [quasiIsoAt_iff_isIso_homologyMap, HomologicalComplex.homologyMap_comp] at hq
    exact IsIso.of_isIso_comp_right _ (HomologicalComplex.homologyMap eB.hom 0)
  have hL := isZero_homology_extendScalars_singleA (A := A) ψ
  have hcone : IsZero ((CochainComplex.mappingCone (E.map η)).homology j) := by
    have hS := Stacks.MappingConeSingle.isZero_homology_of_isIso (E.map η) hL
      (hC (-1) (by omega) (by omega)) hiso
    rcases eq_or_ne j 0 with rfl | hj0
    · exact hS.2
    rcases eq_or_ne j (-1) with rfl | hj1
    · exact hS.1
    have := Stacks.MappingConeSingle.isIso_homologyMap_inr (E.map η) hL j hj0 hj1
    exact (hC j hj0 hj).of_iso (asIso (HomologicalComplex.homologyMap
      (CochainComplex.mappingCone.inr (E.map η)) j)).symm
  have := ModuleCat.subsingleton_of_isZero
    (hcone.of_iso (homologyDerivedMappingConeIso ψ η (Fintype.card I : ℤ) j))
  exact Module.finrank_zero_of_subsingleton

/-- The free module `R^n` is free and finite. -/
theorem free_finite_ulift (R : Type u) [CommRing R] (n : ℕ) :
    Module.Free R (ModuleCat.of R (ULift.{u} (Fin n → R))) ∧
      Module.Finite R (ModuleCat.of R (ULift.{u} (Fin n → R))) :=
  ⟨Module.Free.of_equiv (ULift.moduleEquiv (R := R)).symm,
    Module.Finite.equiv (ULift.moduleEquiv (R := R)).symm⟩

/-- The homology of an object placed in degree `n` of the derived category is that object in
degree `n` and zero elsewhere. -/
theorem isZero_homology_singleFunctor {R : Type u} [CommRing R] (M : ModuleCat.{u} R) (n j : ℤ)
    (h : j ≠ n) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) j).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) n).obj M)) :=
  (HomologicalComplex.isZero_single_obj_homology _ _ _ _ h).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) j).mapIso
        (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) n).app M)) ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) j).app _)

omit [Fintype I] in
include hU in
/-- **Near a point whose fibre has the cohomology of a curve, the Čech model has free homology.**
Let `A` be Noetherian, `f : X ⟶ Spec A` proper and `F` a coherent `𝒪_X`-module flat over `A` with
a global section `s`, and let `p` be a prime of `A` such that on the fibre `X_p` the map
`κ(p) ⟶ Γ(X_p, F_p)`, `c ↦ c • s` is bijective and `F_p` has no cohomology in degrees `≥ 2`. Then
there is `g ∉ p` such that the base change to `A_g` of the Čech model of `RΓ(X, F)` has free
homology of finite rank in every degree. -/
theorem exists_away_free_homology [Finite I] [IsNoetherianRing A] [IsProper f] [F.IsCoherent]
    (hUaff : ∀ i, IsAffineOpen (U i))
    (haff : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, U (s k)))
    (hflat : IsFlatOver f.toLRSHom.toShHom F) (s : Γ(F, ⊤))
    (p : Ideal A) [p.IsPrime] {Xp : Scheme.{u}} {fp : Xp ⟶ Spec (.of p.ResidueField)}
    {gp : Xp ⟶ X}
    (hsq : IsPullback gp fp f (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))))
    (hbij : Function.Bijective (fun c : p.ResidueField =>
      letI := Stacks.Cech.sectionsModule fp ((Scheme.Modules.pullback gp).obj F) ⊤
      c • AlgebraicGeometry.pullbackSectionHom gp F ⊤ ⊤ (by simp) s))
    (hvan : ∀ i : ℕ, 2 ≤ i → Subsingleton
      (((moduleGlobalSections Xp).rightDerived i).obj ((Scheme.Modules.pullback gp).obj F))) :
    ∃ g : A, g ∉ p ∧ ∀ j : ℤ,
      Module.Free (Localization.Away g)
        ((((ModuleCat.extendScalars.{u, u, u}
          (algebraMap A (Localization.Away g))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (baseAlternatingCechComplex f U hU F)).homology j) ∧
      Module.Finite (Localization.Away g)
        ((((ModuleCat.extendScalars.{u, u, u}
          (algebraMap A (Localization.Away g))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (baseAlternatingCechComplex f U hU F)).homology j) := by
  let _ : Fintype I := Fintype.ofFinite I
  let η := sectionUnit f U hU F s
  have : ∀ i, Module.Flat A ((baseAlternatingCechComplex f U hU F).X i) :=
    flat_baseAlternatingCechComplex_X f U hU F hUaff hflat
  have : ∀ i, Module.Flat A ((CochainComplex.mappingCone η).X i) :=
    StacksDraft.ConeLift.flat_mappingCone_X η
  have := StacksDraft.ConeLift.isStrictlyLE_mappingCone η (Fintype.card I : ℤ)
  have hperf : StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Q.obj (CochainComplex.mappingCone η)) :=
    (StacksDraft.Perfect.isPerfect_of_distinguished _
      (DerivedCategory.mappingCone_triangle_distinguished η)).1 (isPerfect_Q_singleA (A := A))
      (isPerfect_Q_baseAlternatingCechComplex f U hU F hUaff haff hflat)
  obtain ⟨g, hg, ⟨e⟩⟩ :=
    StacksDraft.Perfect.exists_away_iso_singleFunctor_free_of_fibre_concentrated.{u, u} p
      (DerivedCategory.Q.obj (CochainComplex.mappingCone η)) hperf 1
      (fun j hj => finrank_derivedFibreHomology_mappingCone_eq_zero f U hU F hUaff hflat s p hsq
        hbij hvan j hj)
  refine ⟨g, hg, ?_⟩
  let ψ := algebraMap A (Localization.Away g)
  let E := (ModuleCat.extendScalars.{u, u, u} ψ).mapHomologicalComplex (ComplexShape.up ℤ)
  let n := Module.finrank p.ResidueField (StacksDraft.Perfect.derivedFibreHomology.{u, u} p
    (DerivedCategory.Q.obj (CochainComplex.mappingCone η)) 1)
  let Fr := ModuleCat.of (Localization.Away g) (ULift.{u} (Fin n → Localization.Away g))
  have hconeIso : ∀ j : ℤ, (CochainComplex.mappingCone (E.map η)).homology j ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (Localization.Away g)) j).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} (Localization.Away g)) 1).obj Fr) := fun j =>
    (homologyDerivedMappingConeIso ψ η (Fintype.card I : ℤ) j).symm ≪≫
      (DerivedCategory.homologyFunctor _ j).mapIso e
  have hcone : ∀ j : ℤ, j ≠ 1 → IsZero ((CochainComplex.mappingCone (E.map η)).homology j) :=
    fun j hj => (isZero_homology_singleFunctor Fr 1 j hj).of_iso (hconeIso j)
  have hL := isZero_homology_extendScalars_singleA (A := A) ψ
  intro j
  rcases lt_trichotomy j 0 with hj | rfl | hj
  · exact free_finite_of_isZero (ShortComplex.isZero_homology_of_isZero_X₂ _
      ((ModuleCat.extendScalars.{u, u, u} ψ).map_isZero
        (isZero_baseAlternatingCechComplex_X_of_neg f U hU F j hj)))
  · have := Stacks.MappingConeSingle.isIso_homologyMap_of_isZero (E.map η)
      (hcone (-1) (by omega)) (hcone 0 (by omega))
    exact free_finite_of_iso (asIso (HomologicalComplex.homologyMap (E.map η) 0)).symm
      (free_finite_homology_zero_extendScalars_singleA ψ)
  · have := Stacks.MappingConeSingle.isIso_homologyMap_inr (E.map η) hL j (by omega) (by omega)
    let e1 := asIso (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr (E.map η)) j)
    rcases eq_or_ne j 1 with rfl | hj1
    · exact free_finite_of_iso (e1 ≪≫ hconeIso 1 ≪≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 1).app Fr)
        (free_finite_ulift (Localization.Away g) n)
    · exact free_finite_of_isZero ((hcone j hj1).of_iso e1)

end Main

section Unit

variable {Y Z : Scheme.{u}} (h : Y ⟶ Z)

/-- **The pullback of the unit section of `𝒪_Z` is the unit section of `𝒪_Y`**, through the
identification `h^* 𝒪_Z ≅ 𝒪_Y`. -/
theorem pullbackUnitIso_pullbackSectionHom_one :
    (Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso h).hom.val.app (op ⊤)
      (AlgebraicGeometry.pullbackSectionHom h (unitModule Z) ⊤ ⊤ (by simp)
        (show Γ(unitModule Z, ⊤) from (1 : Γ(Z, ⊤)))) = (1 : Γ(Y, ⊤)) := by
  let t := Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso h
  have h1 := congr(
    $(Stacks.AlgebraicGeometry.AffineBaseChange.unit_comp_map_pullbackUnitIso h).val.app
    (op (⊤ : Z.Opens)) (show Γ(unitModule Z, ⊤) from (1 : Γ(Z, ⊤))))
  have h2 := Stacks.AlgebraicGeometry.AffineBaseChange.structureUnitHom_val_app_top h
    (1 : Γ(Z, ⊤))
  have hn := congr($(t.hom.val.naturality (homOfLE (show (⊤ : Y.Opens) ≤ h ⁻¹ᵁ ⊤ by simp)).op)
    (((Scheme.Modules.pullbackPushforwardAdjunction h).unit.app (unitModule Z)).val.app
      (op ⊤) (show Γ(unitModule Z, ⊤) from (1 : Γ(Z, ⊤)))))
  refine hn.trans ?_
  change Y.presheaf.map (homOfLE (show (⊤ : Y.Opens) ≤ h ⁻¹ᵁ ⊤ by simp)).op
    (t.hom.val.app (op (h ⁻¹ᵁ ⊤)) _) = 1
  have h3 : t.hom.val.app (op (h ⁻¹ᵁ ⊤))
      (((Scheme.Modules.pullbackPushforwardAdjunction h).unit.app (unitModule Z)).val.app
        (op ⊤) (show Γ(unitModule Z, ⊤) from (1 : Γ(Z, ⊤)))) =
        (show Γ(unitModule Y, h ⁻¹ᵁ ⊤) from (1 : Γ(Y, h ⁻¹ᵁ ⊤))) :=
    h1.trans (h2.trans (h.appTop).hom.map_one)
  rw [h3]
  exact (Y.presheaf.map (homOfLE (show (⊤ : Y.Opens) ≤ h ⁻¹ᵁ ⊤ by simp)).op).hom.map_one

/-- **On a proper, geometrically reduced and geometrically connected scheme over a field `k`,
`c ↦ c • g^* 1` is a bijection from `k` onto the global sections of the pullback of the structure
sheaf** along any `g`. This is `H⁰(X_k, 𝒪) = k` ([Stacks, Tag 0BUG]) read through
`g^* 𝒪 ≅ 𝒪`. -/
theorem bijective_smul_pullbackSectionHom_one {k : Type u} [Field k] {Xp : Scheme.{u}}
    (fp : Xp ⟶ Spec (.of k)) [IsProper fp] [GeometricallyReduced fp] [GeometricallyConnected fp]
    (gp : Xp ⟶ Z) :
    Function.Bijective (fun c : k =>
      letI := Stacks.Cech.sectionsModule fp ((Scheme.Modules.pullback gp).obj (unitModule Z)) ⊤
      c • AlgebraicGeometry.pullbackSectionHom gp (unitModule Z) ⊤ ⊤ (by simp)
        (show Γ(unitModule Z, ⊤) from (1 : Γ(Z, ⊤)))) := by
  let := Stacks.Cech.sectionsModule fp ((Scheme.Modules.pullback gp).obj (unitModule Z)) ⊤
  have hb : Function.Bijective (Stacks.Cech.baseRingHom fp ⊤).hom := by
    have := Stacks.AlgebraicGeometry.ProperSectionsGeom.isIso_globalSections_of_isProper k fp
    have heq : Stacks.Cech.baseRingHom fp ⊤ = (Scheme.ΓSpecIso (.of k)).inv ≫ fp.appTop := by
      rw [Stacks.Cech.baseRingHom,
        show (homOfLE le_top : (⊤ : Xp.Opens) ⟶ ⊤) = 𝟙 _ from Subsingleton.elim _ _, op_id,
        Xp.presheaf.map_id, Category.comp_id]
      rfl
    rw [heq]
    exact ConcreteCategory.bijective_of_isIso _
  let t := Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso gp
  let x := AlgebraicGeometry.pullbackSectionHom gp (unitModule Z) ⊤ ⊤ (by simp)
    (show Γ(unitModule Z, ⊤) from (1 : Γ(Z, ⊤)))
  have hT : ∀ c : k, t.hom.app ⊤ (c • x) = (Stacks.Cech.baseRingHom fp ⊤).hom c := by
    intro c
    refine (Scheme.Modules.Hom.app_smul t.hom ((Stacks.Cech.baseRingHom fp ⊤).hom c) x).trans ?_
    have h2 : t.hom.app ⊤ x = (show Γ(unitModule Xp, ⊤) from (1 : Γ(Xp, ⊤))) :=
      pullbackUnitIso_pullbackSectionHom_one gp
    rw [h2]
    exact mul_one ((Stacks.Cech.baseRingHom fp ⊤).hom c)
  have hinj : Function.Injective (t.hom.app ⊤) := fun a b hab => by
    have := congrArg (t.inv.app ⊤) hab
    rwa [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply, ← Scheme.Modules.Hom.comp_app,
      t.hom_inv_id, Scheme.Modules.Hom.id_app, CategoryTheory.id_apply,
      CategoryTheory.id_apply] at this
  refine ⟨fun c d hcd => hb.1 ((hT c).symm.trans ((congrArg (t.hom.app ⊤) hcd).trans (hT d))),
    fun y => ?_⟩
  obtain ⟨c, hc⟩ := hb.2 (t.hom.app ⊤ y)
  exact ⟨c, hinj ((hT c).trans hc)⟩

end Unit

section Curve

omit [Fintype I] in
include hU in
/-- **The Čech model of `RΓ(X, 𝒪_X)` for a proper smooth family of geometrically connected curves
over a Noetherian affine base has, Zariski locally on the base, free homology of finite rank in
every degree.** Let `A` be Noetherian and `f : X ⟶ Spec A` proper and smooth with geometrically
connected fibres of dimension at most `1`, and let `U` be a finite affine cover of `X` with affine
intersections. Every prime `p` of `A` has `g ∉ p` such that the base change to `A_g` of the
`A`-linear alternating Čech complex of `𝒪_X` has free homology of finite rank in each degree.

This is the cohomological content of parts (a)–(c) of [Stacks, Tag 0GKA] for a smooth family:
on the fibre `X_p` the functions are the constants ([Stacks, Tag 0BUG]) and there is no
cohomology above the dimension `1` ([Stacks, Tag 02UZ]). -/
theorem exists_away_free_homology_of_smooth [Finite I] [IsNoetherianRing A] [IsProper f] [Smooth f]
    [GeometricallyConnected f]
    (hdim : ∀ s, topologicalKrullDim (f.fiber s) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (hUaff : ∀ i, IsAffineOpen (U i))
    (haff : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, U (s k)))
    (p : Ideal A) [p.IsPrime] :
    ∃ g : A, g ∉ p ∧ ∀ j : ℤ,
      Module.Free (Localization.Away g)
        ((((ModuleCat.extendScalars.{u, u, u}
          (algebraMap A (Localization.Away g))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (baseAlternatingCechComplex f U hU (unitModule X))).homology j) ∧
      Module.Finite (Localization.Away g)
        ((((ModuleCat.extendScalars.{u, u, u}
          (algebraMap A (Localization.Away g))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
            (baseAlternatingCechComplex f U hU (unitModule X))).homology j) := by
  have : GeometricallyReduced f := geometricallyReduced_of_smooth f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : (unitModule X).IsCoherent := Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_unit X
  let x : Spec (.of A) := ⟨p, inferInstance⟩
  let e := Scheme.Spec.residueFieldIso (.of A) x
  have hsq : IsPullback (pullback.fst f ((Spec (.of A)).fromSpecResidueField x))
      (pullback.snd f ((Spec (.of A)).fromSpecResidueField x) ≫ Spec.map e.inv) f
      (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))) :=
    (IsPullback.of_hasPullback f ((Spec (.of A)).fromSpecResidueField x)).of_iso
      (Iso.refl _) (Iso.refl _) (asIso (Spec.map e.inv)) (Iso.refl _) (by simp) (by simp)
      (by simp) (by rw [Iso.refl_hom, Category.comp_id, asIso_hom,
        ← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField])
  let fp := pullback.snd f ((Spec (.of A)).fromSpecResidueField x) ≫ Spec.map e.inv
  have : IsProper fp := MorphismProperty.of_isPullback (P := @IsProper) hsq ‹_›
  have : GeometricallyReduced fp :=
    MorphismProperty.of_isPullback (P := @GeometricallyReduced) hsq ‹_›
  have : GeometricallyConnected fp :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) hsq ‹_›
  refine exists_away_free_homology f U hU (unitModule X) hUaff haff (isFlatOver_unit_of_flat f)
    (show Γ(unitModule X, ⊤) from (1 : Γ(X, ⊤))) p hsq
    (bijective_smul_pullbackSectionHom_one fp _) (fun i hi => ?_)
  have hz := AlgebraicGeometry.isZero_cohomologyOverField_of_topologicalKrullDim_le
    p.ResidueField fp ((Scheme.Modules.pullback (pullback.fst f
      ((Spec (.of A)).fromSpecResidueField x))).obj (unitModule X)) (d := 1) (hdim x)
      (by omega : 1 < i)
  have := ModuleCat.subsingleton_of_isZero hz
  exact this

end Curve

end Stacks.AlgebraicGeometry.CurveCechCohomology

end
