module

public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.Double
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitByPointResolutionLargeSite
public import StacksFrontier.Cotangent.FilteredColimitVanishing
public import StacksFrontier.Cotangent.PolynomialAlgebraSiteConormalPresheaves
public import StacksFrontier.Cotangent.PolynomialAlgebraSitePointValuesLargeSite
public import StacksFrontier.Cotangent.ResolutionPointCriterionPolynomialSite
public import StacksFrontier.Homology.DoubleExtend

/-!
# Remark 08R7: `Lπ_!(𝒥) = 0` and the map `(J → Ω_{P/A} ⊗_P B) → L_{B/A}`

Let `A → B` be a ring map and work on the site `C_{B/A}` of [Stacks, Tag 08PR]. Let
`𝒥 = ker(𝒪 → B̲)` and `Ω = Ω_{𝒪/A} ⊗_𝒪 B̲`. The first half of Remark 08R7 asserts

* `Lπ_!(𝒥) = 0`;
* `Lπ_!(𝒥 → Ω) = Lπ_!(Ω) = L_{B/A}`;
* hence, for every object `U = (P → B)` of `C_{B/A}`, a map
  `(J → Ω_{P/A} ⊗_P B) ⟶ L_{B/A}` in `D(A)`, where `J = ker(P → B)` (the display (08R8)),
  obtained from the canonical map of [Stacks, Tag 08Q6].

This file proves all three, in `D(A)`, at the site `C_{B/A}` itself.

## Main results

* `CommAlgCat.isZero_polynomialSiteDerivedLowerShriek_ideal`: **`Lπ_!(𝒥) = 0`** in `D(A)`.
* `CommAlgCat.polynomialSiteDerivedLowerShriekCotangentOverBaseIso`: **`Lπ_!(Ω) = L_{B/A}`** in
  `D(A)`.
* `CommAlgCat.polynomialSiteDerivedLowerShriekIdealComplexIso`:
  **`Lπ_!(𝒥 → Ω) = L_{B/A}`** in `D(A)`, the two-term complex `𝒥 → Ω` sitting in degrees
  `-1, 0`.
* `CommAlgCat.idealComplexToCotangentComplex`: **the map (08R8)**,
  `(J → Ω_{P/A} ⊗_P B) ⟶ L_{B/A}` in `D(A)`, for every object `U = (P → B)` of `C_{B/A}`.

## Implementation notes

**Which derived categories.** The objects of `C_{B/A}` live in `Type (u + 1)` and its morphisms
in `Type u`, so `π_!` -- the colimit over the site -- is formed for coefficients in
`Type (u + 1)`, exactly as in Tags 08PS and 08QK at this site
(`CommAlgCat.polynomialSiteResolutionModuleDerivedColimitNatIso`,
`CommAlgCat.polynomialSiteDerivedLowerShriekCotangentIso`). `D(A)` is therefore
`D(ModuleCat.{u+1} (ULift A))`, and every sheaf of `A`-modules with sections in `Type u`, and the
cotangent complex itself, is read there through the universe lift
`CommAlgCat.liftModuleFunctor`, which is exact and fully faithful.

**The proof of `Lπ_!(𝒥) = 0`.** The source deduces it from Tag 08QK. Here it is read on the
standard resolution `P_•`, which computes `Lπ_!` by Tag 08PS: `𝒥(P_•) = ker(P_• → B)`, the
augmentation is surjective in every degree, and it is a quasi-isomorphism on Moore complexes by
Tag 08QI; so `0 → 𝒥(P_•) → P_• → B → 0` is a short exact sequence of complexes whose second map
is a quasi-isomorphism, and `𝒥(P_•)` is acyclic.

**The two-term complex.** `𝒥 → Ω` is `HomologicalComplex.double` of `d`, in degrees `-1, 0`. It
is identified with the mapping cone of `d` placed in degree `0`
(`CochainComplex.doubleIsoMappingConeSingle`), whose distinguished triangle
`Ω → (𝒥 → Ω) → 𝒥[1]` is what turns `Lπ_!(𝒥) = 0` into `Lπ_!(Ω) ≅ Lπ_!(𝒥 → Ω)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology Simplicial

universe u

/-! ### Two-term complexes -/

namespace CochainComplex

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  {X₀ X₁ : C} (f : X₀ ⟶ X₁)

/-- The two-term complex `X₀ → X₁` in cohomological degrees `-1, 0`. -/
abbrev doubleNegOneZero : CochainComplex C ℤ :=
  HomologicalComplex.double f ComplexShape.upIntRelNegOneZero

/-- The map from the two-term complex `X₀ → X₁` to the mapping cone of `f` placed in degree
zero. -/
def doubleToMappingConeSingle :
    doubleNegOneZero f ⟶
      mappingCone ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map f) :=
  HomologicalComplex.mkHomFromDouble _ (by norm_num)
    ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X₀).inv ≫
      (mappingCone.inl _).v 0 (-1) (by norm_num))
    ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X₁).inv ≫
      (mappingCone.inr _).f 0)
    (by
      rw [Category.assoc, mappingCone.inl_v_d _ 0 (-1) 1 (by norm_num) (by norm_num),
        HomologicalComplex.single_obj_d, zero_comp, sub_zero,
        HomologicalComplex.single_map_f_self, Category.assoc, Category.assoc,
        Iso.inv_hom_id_assoc])
    (by
      intro k hk
      have hk' : k = 1 := by simpa using hk.symm
      subst hk'
      refine ((mappingCone.isZero_X_iff _ 1).2 ⟨?_, ?_⟩).eq_of_tgt _ _
      · exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by norm_num)
      · exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by norm_num))

/-- The map from the two-term complex `X₀ → X₁` to the mapping cone of `f` placed in degree
zero is an isomorphism. -/
instance isIso_doubleToMappingConeSingle : IsIso (doubleToMappingConeSingle f) := by
  suffices h : ∀ n, IsIso ((doubleToMappingConeSingle f).f n) from
    HomologicalComplex.Hom.isIso_of_components _
  intro n
  by_cases h₀ : n = -1
  · subst h₀
    rw [doubleToMappingConeSingle, HomologicalComplex.mkHomFromDouble_f₀]
    refine IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' inferInstance ⟨⟨
      (mappingCone.fst _).1.v (-1) 0 (by norm_num), mappingCone.inl_v_fst_v _ _ _ _, ?_⟩⟩)
    rw [← mappingCone.id_X _ (-1) 0 (by norm_num),
      (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by norm_num)).eq_zero_of_tgt
        ((mappingCone.snd _).v (-1) (-1) (by norm_num)), zero_comp, add_zero]
  by_cases h₁ : n = 0
  · subst h₁
    rw [doubleToMappingConeSingle, HomologicalComplex.mkHomFromDouble_f₁]
    refine IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' inferInstance ⟨⟨
      (mappingCone.snd _).v 0 0 (by norm_num), mappingCone.inr_f_snd_v _ _, ?_⟩⟩)
    rw [← mappingCone.id_X _ 0 1 (by norm_num),
      (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by norm_num)).eq_zero_of_tgt
        ((mappingCone.fst _).1.v 0 1 (by norm_num)), zero_comp]
    exact (zero_add _).symm
  · refine ⟨⟨0, (HomologicalComplex.isZero_double_X _ _ _ h₀ h₁).eq_of_src _ _, ?_⟩⟩
    refine ((mappingCone.isZero_X_iff _ n).2 ⟨?_, ?_⟩).eq_of_src _ _
    · exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
    · exact HomologicalComplex.isZero_single_obj_X _ _ _ _ h₁

/-- **The two-term complex `X₀ → X₁` is the mapping cone of `f` placed in degree zero.** -/
def doubleIsoMappingConeSingle :
    doubleNegOneZero f ≅
      mappingCone ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map f) :=
  asIso (doubleToMappingConeSingle f)

variable {D : Type*} [Category* D] [Preadditive D] [HasZeroObject D] (F : C ⥤ D) [F.Additive]

/-- The comparison map from the two-term complex `F X₀ → F X₁` to the image under `F` of the
two-term complex `X₀ → X₁`. -/
def doubleToMapDouble :
    doubleNegOneZero (F.map f) ⟶
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (doubleNegOneZero f) :=
  HomologicalComplex.mkHomFromDouble _ (by norm_num)
    (F.map (HomologicalComplex.doubleXIso₀ f ComplexShape.upIntRelNegOneZero).inv)
    (F.map (HomologicalComplex.doubleXIso₁ f ComplexShape.upIntRelNegOneZero (by norm_num)).inv)
    (by
      dsimp
      rw [← F.map_comp, ← F.map_comp, HomologicalComplex.double_d _ _ (by norm_num),
        Iso.inv_hom_id_assoc])
    (by
      intro k hk
      dsimp
      rw [HomologicalComplex.double_d_eq_zero₀ _ _ _ _ (by norm_num), F.map_zero, comp_zero])

/-- The comparison map from `F X₀ → F X₁` to the image under `F` of `X₀ → X₁` is an
isomorphism. -/
instance isIso_doubleToMapDouble : IsIso (doubleToMapDouble f F) := by
  suffices h : ∀ n, IsIso ((doubleToMapDouble f F).f n) from
    HomologicalComplex.Hom.isIso_of_components _
  intro n
  by_cases h₀ : n = -1
  · subst h₀
    rw [doubleToMapDouble, HomologicalComplex.mkHomFromDouble_f₀]
    infer_instance
  by_cases h₁ : n = 0
  · subst h₁
    rw [doubleToMapDouble, HomologicalComplex.mkHomFromDouble_f₁]
    infer_instance
  · exact ⟨⟨0, (HomologicalComplex.isZero_double_X _ _ _ h₀ h₁).eq_of_src _ _,
      (F.map_isZero (HomologicalComplex.isZero_double_X _ _ _ h₀ h₁)).eq_of_src _ _⟩⟩

/-- **An additive functor carries the two-term complex `X₀ → X₁` to `F X₀ → F X₁`.** -/
def mapDoubleNegOneZeroIso :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (doubleNegOneZero f) ≅
      doubleNegOneZero (F.map f) :=
  (asIso (doubleToMapDouble f F)).symm

end CochainComplex

namespace CommAlgCat

open Stacks.CategoryHomology

attribute [local instance] HasDerivedCategory.standard

/-! ### The universe lift of modules -/

section Lift

variable (R : Type u) [Ring R]

/-- The universe lift `ModuleCat.{u} R ⥤ ModuleCat.{u+1} (ULift R)`, along which a module with
elements in `Type u` is read at the coefficient universe of the site `C_{B/A}`. It is exact and
fully faithful. -/
abbrev liftModuleFunctor : ModuleCat.{u} R ⥤ ModuleCat.{u + 1} (ULift.{u + 1} R) :=
  ModuleCat.uliftFunctor.{u + 1, u} R ⋙
    ModuleCat.restrictScalars.{u + 1} (ULift.ringEquiv : ULift.{u + 1} R ≃+* R).toRingHom

/-- The universe lift `liftModuleFunctor R` preserves homology. -/
instance : (liftModuleFunctor R).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ fun S hS => by
    have h := ModuleCat.uliftFunctor_map_exact R S hS
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h ⊢
    exact h

/-- An exact functor reflecting isomorphisms detects quasi-isomorphisms of Moore complexes. -/
theorem quasiIso_alternatingFaceMapComplex_whiskerRight_iff
    {C₁ C₂ : Type*} [Category* C₁] [Abelian C₁] [Category* C₂] [Abelian C₂]
    (G : C₁ ⥤ C₂) [G.Additive] [G.PreservesHomology] [G.ReflectsIsomorphisms]
    {X Y : SimplicialObject C₁} (g : X ⟶ Y) :
    QuasiIso ((alternatingFaceMapComplex C₂).map (Functor.whiskerRight g G)) ↔
      QuasiIso ((alternatingFaceMapComplex C₁).map g) := by
  have e := AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso G
  have harr : Arrow.mk ((alternatingFaceMapComplex C₂).map (Functor.whiskerRight g G)) ≅
      Arrow.mk ((G.mapHomologicalComplex (ComplexShape.down ℕ)).map
        ((alternatingFaceMapComplex C₁).map g)) :=
    Arrow.isoMk (e.app _).symm (e.app _).symm (e.inv.naturality g).symm
  rw [quasiIso_iff_of_arrow_mk_iso _ _ harr]
  exact HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ G

end Lift

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)

/-! ### The standard resolution and `Lπ_!` at module coefficients -/

/-- `Lπ_! : D(Mod_R(C_{B/A})) ⥤ D(R)` at module coefficients over a ring `R` in the coefficient
universe of the site: the total left derived functor of the colimit over the site, which is the
`π_!` of Tag 08PF on a chaotic site. -/
abbrev polynomialSiteModuleDerivedLowerShriek (R : Type (u + 1)) [Ring R]
    [HasExactColimitsOfShape ℕ (ModuleCat.{u + 1} R)] :
    DerivedCategory ((polynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u + 1} R) ⥤
      DerivedCategory (ModuleCat.{u + 1} R) :=
  totalDerivedColimit' (polynomialSite A B) (ModuleCat.{u + 1} R)

/-- Colimits indexed by `ℕ` are exact in the category of `ULift A`-modules. -/
instance hasExactColimitsOfShapeNat_polynomialBaseModules :
    HasExactColimitsOfShape ℕ (ModuleCat.{u + 1} (ULift.{u + 1} A)) :=
  hasExactColimitsOfShapeNatModuleCat.{u + 1, u + 1} _

/-- **Tag 08PS at module coefficients**, applied to a single presheaf: `Lπ_!(ℱ) = Q(ℱ(P_•))` for
the standard resolution `P_•`. -/
def polynomialSiteModuleDerivedLowerShriekIso (R : Type (u + 1)) [Ring R]
    [HasExactColimitsOfShape ℕ (ModuleCat.{u + 1} R)]
    (F : (polynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u + 1} R) :
    (polynomialSiteModuleDerivedLowerShriek A B R).obj
        (DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F)) ≅
      DerivedCategory.Q.obj ((Stacks.ChaoticSite.GeneralValued.mooreCochainComplex'
        (standardResolutionPolynomialSiteCosimplicialObject A B) (ModuleCat.{u + 1} R)).obj F) :=
  ((Stacks.ChaoticSite.ModuleValued.mooreCochainNatIsoDerivedColimitOfLarge (B := R)
      (standardResolutionPolynomialSiteCosimplicialObject A B)
      (isPointResolution_standardResolutionPolynomialSiteCosimplicialObject A B)).app F).symm

/-- **The extended Moore complex of a lifted presheaf is the lift of the extended Moore complex**:
for a presheaf `F` of `R`-modules with sections in `Type u`, the complex computing `Lπ_!` of its
universe lift on the standard resolution is the lift of the extended Moore complex of
`F(P_•)`. -/
def polynomialSiteLiftMooreComplexIso {R : Type u} [Ring R]
    (F : (polynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} R) :
    (Stacks.ChaoticSite.GeneralValued.mooreCochainComplex'
          (standardResolutionPolynomialSiteCosimplicialObject A B)
          (ModuleCat.{u + 1} (ULift.{u + 1} R))).obj (F ⋙ liftModuleFunctor R) ≅
      ((liftModuleFunctor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((alternatingFaceMapComplex (ModuleCat.{u} R)).obj
          ((standardResolutionPolynomialSiteCosimplicialObject A B).op ⋙ F)).extend
            (ComplexShape.embeddingUpIntLE (0 : ℤ))) :=
  ((ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctor _).mapIso
      ((AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso
        (liftModuleFunctor R)).app
          ((standardResolutionPolynomialSiteCosimplicialObject A B).op ⋙ F)).symm ≪≫
    HomologicalComplex.mapHomologicalComplexExtendIso (liftModuleFunctor R) _
      (ComplexShape.embeddingUpIntLE (0 : ℤ))

/-- **`Lπ_!` of a lifted presheaf is the lifted extended Moore complex of its values on the
standard resolution.** -/
def polynomialSiteLiftDerivedLowerShriekIso {R : Type u} [Ring R]
    [HasExactColimitsOfShape ℕ (ModuleCat.{u + 1} (ULift.{u + 1} R))]
    (F : (polynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} R) :
    (polynomialSiteModuleDerivedLowerShriek A B (ULift.{u + 1} R)).obj
        (DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
          (F ⋙ liftModuleFunctor R))) ≅
      DerivedCategory.Q.obj (((liftModuleFunctor R).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (((alternatingFaceMapComplex (ModuleCat.{u} R)).obj
          ((standardResolutionPolynomialSiteCosimplicialObject A B).op ⋙ F)).extend
            (ComplexShape.embeddingUpIntLE (0 : ℤ)))) :=
  polynomialSiteModuleDerivedLowerShriekIso A B _ _ ≪≫
    DerivedCategory.Q.mapIso (polynomialSiteLiftMooreComplexIso A B F)

/-! ### `Lπ_!(Ω) = L_{B/A}` at module coefficients -/

/-- **The Moore complex of `Ω(P_•)` is the complex of `L_{B/A}`**, after any additive functor
out of `B`-modules; at `C_{B/A}` itself this is an identification of complexes, through
`CommAlgCat.standardResolutionOverDifferentialsIso`. -/
def polynomialSiteCotangentMooreComplexIsoOf {D : Type*} [Category* D] [Abelian D]
    (G : ModuleCat.{u} (B : Type u) ⥤ D) [G.Additive] :
    (Stacks.ChaoticSite.GeneralValued.mooreCochainComplex'
          (standardResolutionPolynomialSiteCosimplicialObject A B) D).obj
        (polynomialCotangentModulePresheaf A B ⋙ G) ≅
      (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj (cotangentComplex.{u, u} A B) :=
  ((ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctor D).mapIso
      ((alternatingFaceMapComplex D).mapIso
          (Functor.isoWhiskerRight (standardResolutionOverDifferentialsIso A B) G) ≪≫
        ((AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso G).app
            (cotangentSimplicialModule.{u, u} A B).object).symm) ≪≫
    HomologicalComplex.mapHomologicalComplexExtendIso G
      ((alternatingFaceMapComplex (ModuleCat.{u} (B : Type u))).obj
        (cotangentSimplicialModule.{u, u} A B).object)
      (ComplexShape.embeddingUpIntLE (0 : ℤ))

/-- The functor reading a `B`-module as an `A`-module at the coefficient universe of the site. -/
abbrev baseModuleToCoefficients :
    ModuleCat.{u} (B : Type u) ⥤ ModuleCat.{u + 1} (ULift.{u + 1} A) :=
  ModuleCat.restrictScalars (algebraMap A B) ⋙ liftModuleFunctor A

/-- `L_{B/A}`, the cotangent complex of Tag 08PN, as an object of `D(A)` at the coefficient
universe of the site. -/
abbrev cotangentComplexOverBase : DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} A)) :=
  DerivedCategory.Q.obj (((baseModuleToCoefficients A B).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (cotangentComplex.{u, u} A B))

/-- `Ω = Ω_{𝒪/A} ⊗_𝒪 B̲` on `C_{B/A}`, as a sheaf of `A`-modules at the coefficient universe of
the site. -/
abbrev polynomialSiteCotangentSheafOverBase :
    (polynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u + 1} (ULift.{u + 1} A) :=
  polynomialCotangentModulePresheaf A B ⋙ baseModuleToCoefficients A B

/-- **`Lπ_!(Ω) = L_{B/A}` in `D(A)`** at the site `C_{B/A}` itself: Tag 08PU, read with
coefficients in `A`-modules. This is the identification Remark 08R7 starts from. -/
def polynomialSiteDerivedLowerShriekCotangentOverBaseIso :
    (polynomialSiteModuleDerivedLowerShriek A B (ULift.{u + 1} A)).obj
        (DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
          (polynomialSiteCotangentSheafOverBase A B))) ≅
      cotangentComplexOverBase A B :=
  polynomialSiteModuleDerivedLowerShriekIso A B _ _ ≪≫
    DerivedCategory.Q.mapIso (polynomialSiteCotangentMooreComplexIsoOf A B _)

/-! ### `Lπ_!(𝒥) = 0` -/

/-- The augmentation ideal `𝒥` on `C_{B/A}`, as a sheaf of `A`-modules at the coefficient universe
of the site. -/
abbrev polynomialSiteIdealSheaf : (polynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u + 1} (ULift.{u + 1} A) :=
  polynomialSiteIdealPresheaf A B ⋙ liftModuleFunctor A

/-- The short complex `𝒥(P_•) → 𝒪(P_•) → B̲(P_•)` of simplicial `A`-modules, on the standard
resolution. -/
abbrev standardResolutionIdealShortComplex :
    ShortComplex (SimplicialObject (ModuleCat.{u} A)) :=
  ShortComplex.mk
    (Functor.whiskerLeft (standardResolutionPolynomialSiteCosimplicialObject A B).op
      (polynomialSiteIdealInclusion A B))
    (Functor.whiskerLeft (standardResolutionPolynomialSiteCosimplicialObject A B).op
      (polynomialSiteModuleAugmentation A B))
    (by
      ext n : 1
      exact overIdealInclusion_comp_augmentation (B := B) _)

/-- The augmentation of the standard resolution is surjective in every simplicial degree. -/
private theorem surjective_standardResolution_hom_app (n : SimplexCategoryᵒᵖ) :
    Function.Surjective ((standardResolution.{u, u} A B).hom.app n).hom := by
  have hn : n = op (SimplexCategory.mk n.unop.len) := by rw [SimplexCategory.mk_len]
  rw [hn]
  exact surjective_standardResolution_augmentation A B n.unop.len

/-- In every simplicial degree, `0 → ker(εₙ) → Pₙ → B → 0` is short exact, the augmentation of
the standard resolution being surjective. -/
theorem standardResolutionIdealShortComplex_shortExact_app (n : SimplexCategoryᵒᵖ) :
    ((standardResolutionIdealShortComplex A B).map
      ((evaluation SimplexCategoryᵒᵖ (ModuleCat.{u} A)).obj n)).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    refine fun p => ⟨fun hp => ⟨⟨p, hp⟩, rfl⟩, ?_⟩
    rintro ⟨j, rfl⟩
    exact j.2
  · rw [ModuleCat.mono_iff_injective]
    exact fun _ _ => Subtype.ext
  · rw [ModuleCat.epi_iff_surjective]
    exact surjective_standardResolution_hom_app A B n

/-- The Moore complexes of `0 → 𝒥(P_•) → 𝒪(P_•) → B̲(P_•) → 0` form a short exact sequence. -/
theorem standardResolutionIdealShortComplex_map_shortExact :
    ((standardResolutionIdealShortComplex A B).map
      (alternatingFaceMapComplex (ModuleCat.{u} A))).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n =>
    standardResolutionIdealShortComplex_shortExact_app A B (op ⦋n⦌)

/-- **The augmentation `𝒪(P_•) → B̲(P_•)` is a quasi-isomorphism of Moore complexes of
`A`-modules**: [Stacks, Tag 08QI] for the standard resolution, which is stated on underlying
abelian groups; the forgetful functor to abelian groups detects quasi-isomorphisms. -/
theorem quasiIso_standardResolutionModuleAugmentation :
    QuasiIso ((alternatingFaceMapComplex (ModuleCat.{u} A)).map
      (standardResolutionIdealShortComplex A B).g) := by
  rw [← quasiIso_alternatingFaceMapComplex_whiskerRight_iff
    (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})]
  exact ((isResolution_quasiIso_homotopyEquivalence_tfae A B _
    (standardResolution.{u, u} A B).hom
    (fun n => (standardResolution_isPolynomialAlgebraBelow A B n).isPolynomialAlgebra)
    (surjective_standardResolution_hom_app A B)).out 1 2).mp
    (standardResolution_isResolution.{u, u} A B)

/-- **`𝒥(P_•) = ker(P_• → B)` has acyclic Moore complex.** -/
theorem acyclic_standardResolutionIdealMooreComplex :
    ((alternatingFaceMapComplex (ModuleCat.{u} A)).obj
      ((standardResolutionPolynomialSiteCosimplicialObject A B).op ⋙
        polynomialSiteIdealPresheaf A B)).Acyclic :=
  (standardResolutionIdealShortComplex_map_shortExact A B).acyclic_X₁
    (quasiIso_standardResolutionModuleAugmentation A B)

/-- The lift of the extended Moore complex of an acyclic complex is acyclic. -/
theorem acyclic_lift_extend {R : Type u} [Ring R] (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (hK : K.Acyclic) :
    (((liftModuleFunctor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (K.extend (ComplexShape.embeddingUpIntLE (0 : ℤ)))).Acyclic := by
  have hext : (K.extend (ComplexShape.embeddingUpIntLE (0 : ℤ))).Acyclic := by
    intro n
    by_cases hn : ∃ m : ℕ, (ComplexShape.embeddingUpIntLE (0 : ℤ)).f m = n
    · obtain ⟨m, rfl⟩ := hn
      exact (K.extend_exactAt_iff _ rfl).2 (hK m)
    · exact K.extend_exactAt _ n fun m hm => hn ⟨m, hm⟩
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (Functor.map_isZero _ ((hext n).isZero_homology)).of_iso
    (Stacks.mapHomologicalComplexHomologyIso _ _ n)

/-- **`Lπ_!(𝒥) = 0` in `D(A)`**, the first assertion of Remark 08R7, at the site `C_{B/A}`
itself, for the augmentation ideal `𝒥 = ker(𝒪 → B̲)` read as a sheaf of `A`-modules. -/
@[stacks 08R7 "Lπ_!(𝒥) = 0 for 𝒥 = ker(𝒪 → B̲), in D(A), at the site C_{B/A} of Tag 08PR \
  itself, with Lπ_! the total left derived functor of the colimit over the site (the π_! of \
  Tag 08PF) and the coefficients at the universe of the site's objects"]
theorem isZero_polynomialSiteDerivedLowerShriek_ideal :
    IsZero ((polynomialSiteModuleDerivedLowerShriek A B (ULift.{u + 1} A)).obj
      (DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        (polynomialSiteIdealSheaf A B)))) :=
  (CochainComplex.isZero_Q_obj_of_acyclic _
    (acyclic_lift_extend _ (acyclic_standardResolutionIdealMooreComplex A B))).of_iso
    (polynomialSiteLiftDerivedLowerShriekIso A B _)

/-! ### `Lπ_!(𝒥 → Ω) = L_{B/A}` and the map (08R8) -/

/-- The differential `d : 𝒥 → Ω` at the coefficient universe of the site. -/
abbrev polynomialSiteIdealSheafToCotangent :
    polynomialSiteIdealSheaf A B ⟶ polynomialSiteCotangentSheafOverBase A B :=
  Functor.whiskerRight (polynomialSiteIdealToCotangent A B) (liftModuleFunctor A)

/-- **The two-term complex `𝒥 → Ω`** of sheaves of `A`-modules on `C_{B/A}`, in degrees `-1, 0`. -/
abbrev polynomialSiteIdealComplex :
    CochainComplex ((polynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u + 1} (ULift.{u + 1} A)) ℤ :=
  CochainComplex.doubleNegOneZero (polynomialSiteIdealSheafToCotangent A B)

/-- The inclusion `Ω → (𝒥 → Ω)` becomes an isomorphism after `Lπ_!`, the third vertex of its
triangle being `Lπ_!(𝒥)[1] = 0`. -/
instance isIso_polynomialSiteDerivedLowerShriek_map_inr :
    IsIso ((polynomialSiteModuleDerivedLowerShriek A B (ULift.{u + 1} A)).map
      (DerivedCategory.Q.map (CochainComplex.mappingCone.inr
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
          (polynomialSiteIdealSheafToCotangent A B))))) := by
  let L := polynomialSiteModuleDerivedLowerShriek A B (ULift.{u + 1} A)
  let T := L.mapTriangle.obj (DerivedCategory.Q.mapTriangle.obj
    (CochainComplex.mappingCone.triangle ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
      (polynomialSiteIdealSheafToCotangent A B))))
  have hT : T ∈ distTriang _ := L.map_distinguished _
    (DerivedCategory.mappingCone_triangle_distinguished _)
  exact (Pretriangulated.Triangle.isZero₁_iff_isIso₂ T hT).1
    (isZero_polynomialSiteDerivedLowerShriek_ideal A B)

/-- **`Lπ_!(Ω) = Lπ_!(𝒥 → Ω)`** in `D(A)`, induced by the inclusion `Ω → (𝒥 → Ω)`. -/
@[stacks 08R7 "Lπ_!(𝒥 → Ω) = Lπ_!(Ω) in D(A), at the site C_{B/A} of Tag 08PR itself, as the \
  isomorphism induced by the inclusion Ω → (𝒥 → Ω) of the degree-zero term"]
def polynomialSiteDerivedLowerShriekCotangentIdealComplexIso :
    (polynomialSiteModuleDerivedLowerShriek A B (ULift.{u + 1} A)).obj
        (DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
          (polynomialSiteCotangentSheafOverBase A B))) ≅
      (polynomialSiteModuleDerivedLowerShriek A B (ULift.{u + 1} A)).obj
        (DerivedCategory.Q.obj (polynomialSiteIdealComplex A B)) :=
  asIso ((polynomialSiteModuleDerivedLowerShriek A B (ULift.{u + 1} A)).map
      (DerivedCategory.Q.map (CochainComplex.mappingCone.inr
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
          (polynomialSiteIdealSheafToCotangent A B))))) ≪≫
    (polynomialSiteModuleDerivedLowerShriek A B (ULift.{u + 1} A)).mapIso
      (DerivedCategory.Q.mapIso (CochainComplex.doubleIsoMappingConeSingle _).symm)

/-- **`Lπ_!(𝒥 → Ω) = L_{B/A}` in `D(A)`**, Remark 08R7, at the site `C_{B/A}` itself: the
two-term complex `𝒥 → Ω` of sheaves of `A`-modules, in degrees `-1, 0`, has `Lπ_!` the cotangent
complex of Tag 08PN. -/
@[stacks 08R7 "Lπ_!(𝒥 → Ω) = Lπ_!(Ω) = L_{B/A} in D(A), at the site C_{B/A} of Tag 08PR \
  itself, for the two-term complex 𝒥 → Ω in degrees -1, 0, Ω = Ω_{𝒪/A} ⊗_𝒪 B̲, the \
  identification being the inverse of the one induced by Ω → (𝒥 → Ω) followed by Tag 08PU"]
def polynomialSiteDerivedLowerShriekIdealComplexIso :
    (polynomialSiteModuleDerivedLowerShriek A B (ULift.{u + 1} A)).obj
        (DerivedCategory.Q.obj (polynomialSiteIdealComplex A B)) ≅
      cotangentComplexOverBase A B :=
  (polynomialSiteDerivedLowerShriekCotangentIdealComplexIso A B).symm ≪≫
    polynomialSiteDerivedLowerShriekCotangentOverBaseIso A B

/-- **The map (08R8) of Remark 08R7**: for an object `U = (P → B)` of `C_{B/A}`, with
`J = ker(P → B)`, the map `(J → Ω_{P/A} ⊗_P B) ⟶ L_{B/A}` in `D(A)`. It is the canonical map
`K(U) ⟶ Lπ_!(K)` of Tag 08Q6 for the two-term complex `K = (𝒥 → Ω)`, followed by
`Lπ_!(𝒥 → Ω) = L_{B/A}`; the two-term complex `J → Ω_{P/A} ⊗_P B` of `A`-modules is the value of
`𝒥 → Ω` at `U`. -/
@[stacks 08R7 "the map (08R8): (J → Ω_{P/A} ⊗_P B) → L_{B/A} in D(A) for every object \
  U = (P → B) of C_{B/A}, J = ker(P → B), as the canonical map of Tag 08Q6 followed by \
  Lπ_!(𝒥 → Ω) = L_{B/A}"]
def idealComplexToCotangentComplex (U : polynomialSite A B) :
    DerivedCategory.Q.obj (CochainComplex.doubleNegOneZero
        ((liftModuleFunctor A).map ((polynomialSiteIdealToCotangent A B).app (op U)))) ⟶
      cotangentComplexOverBase A B :=
  DerivedCategory.Q.map (CochainComplex.mapDoubleNegOneZeroIso
      (polynomialSiteIdealSheafToCotangent A B)
      ((evaluation (polynomialSite A B)ᵒᵖ (ModuleCat.{u + 1} (ULift.{u + 1} A))).obj
        (op U))).inv ≫
    (evaluationToTotalDerivedColimit' (polynomialSite A B)
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) U).app (polynomialSiteIdealComplex A B) ≫
    (polynomialSiteDerivedLowerShriekIdealComplexIso A B).hom

end CommAlgCat

end
