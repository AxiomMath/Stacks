module

public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.QuasicoherentIdeal
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportPushforwardInternalHom
public import StacksFrontier.AlgebraicGeometry.RingedSpaceModuleSpellings
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraDegreeZero
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedConormalModule
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleAssociatedModuleBaseChangeComposition

/-!
# The Zariski model of modules on a representable algebraic space

Let `T` be an object of the big fppf site over a scheme `S`, with underlying scheme `T₀`.  The
associated-module functor of Stacks 03DU, followed by the identification of the small étale site
of the scheme `T₀` with the small étale site of the algebraic space `yoneda.obj T`, is a functor
`Φ_T` from the Zariski `𝒪_{T₀}`-modules to the `𝒪`-modules on the small étale site of
`yoneda.obj T`.  It is left adjoint to restriction `R_T` to the Zariski opens of `T₀`.

For a morphism `g : T' ⟶ T` of the site, with underlying morphism of schemes `g₀`, the direct
images commute with the restrictions: `R_T ∘ g_* ≅ g₀_* ∘ R_{T'}`.  The conjugate isomorphism of
left adjoints is the identification `Φ_{T'} ∘ g₀^* ≅ g^* ∘ Φ_T` of the inverse images.  Defined as
a conjugate, it is natural for free, and it is compatible with the structure maps
`g₀^*𝒪_{T₀} ⟶ 𝒪_{T'₀}` and `g^*𝒪 ⟶ 𝒪`.  That compatibility is what lets a map of ideal sheaves
induced by a commutative square of closed immersions of schemes be compared with the map of
defining ideal sheaves of the corresponding square of closed subspaces of algebraic spaces.

## Main definitions

* `AlgebraicGeometry.Space.zariskiModel`, `AlgebraicGeometry.Space.zariskiRestriction` and
  `AlgebraicGeometry.Space.zariskiModelAdjunction`: the functor `Φ_T`, its right adjoint `R_T`
  and the adjunction.
* `AlgebraicGeometry.Space.zariskiRestrictionPushforwardIso`: `R_T ∘ g_* ≅ g₀_* ∘ R_{T'}`.
* `AlgebraicGeometry.Space.zariskiModelPullbackIso`: `Φ_T ⋙ g^* ≅ g₀^* ⋙ Φ_{T'}`, its conjugate.
* `AlgebraicGeometry.Space.definingIdealSheafZariskiModelIso`: the defining ideal sheaf of a
  closed subspace of `yoneda.obj T` is the Zariski model of the ideal sheaf of the corresponding
  closed immersion of schemes.

## Main results

* `AlgebraicGeometry.Space.zariskiModelPullbackIso_inv_app_unit_comp`: the identification of
  inverse images is compatible with the structure maps.
* `AlgebraicGeometry.Space.definingIdealSheafZariskiModelIso_inv_comp_ι`: the identification of
  defining ideal sheaves is compatible with the inclusions into the structure sheaves.
* `AlgebraicGeometry.Space.idealSheafMap_eq_zariskiModel`: the map of defining ideal sheaves of a
  square of closed subspaces of representable algebraic spaces is the Zariski model of the map of
  ideal sheaves of the corresponding square of closed immersions of schemes.

## Implementation notes

The comparison of the two maps of ideal sheaves never computes either of them: both are the
unique maps lifting the inverse image of an inclusion of ideals followed by a structure map
through a monomorphism (`CategoryTheory.comp_eq_of_square_of_mono`), so it suffices that the
identifications in play respect the inclusions and the structure maps.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Sheaves.ToposPullback

universe u

namespace CategoryTheory

/-- **Transposition across a conjugate pair.**  For adjunctions `L₁ ⊣ R₁` and `L₂ ⊣ R₂` and a
transformation `α : L₂ ⟶ L₁`, transposing `α.app c ≫ f` along the second adjunction is
transposing `f` along the first and then applying the conjugate of `α`. -/
theorem Adjunction.homEquiv_app_comp_conjugateEquiv {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁)
    {c : C} {d : D} (f : L₁.obj c ⟶ d) :
    adj₂.homEquiv c d (α.app c ≫ f) =
      adj₁.homEquiv c d f ≫ (conjugateEquiv adj₁ adj₂ α).app d := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    ← unit_conjugateEquiv adj₁ adj₂ α c, Category.assoc, Category.assoc]
  exact congrArg (adj₁.unit.app c ≫ ·) ((conjugateEquiv adj₁ adj₂ α).naturality f).symm

/-- The transpose along a composite adjunction of a map of the form `H u ≫ v`. -/
private theorem Adjunction.comp_homEquiv_map_comp {C D E : Type*} [Category C] [Category D]
    [Category E] {F : C ⥤ D} {G : D ⥤ C} {H : D ⥤ E} {I : E ⥤ D} (adj₁ : F ⊣ G) (adj₂ : H ⊣ I)
    {X : C} {A : D} {Y : E} (u : F.obj X ⟶ A) (v : H.obj A ⟶ Y) :
    (adj₁.comp adj₂).homEquiv X Y (H.map u ≫ v) =
      adj₁.homEquiv X A u ≫ G.map (adj₂.homEquiv A Y v) := by
  rw [Adjunction.comp_homEquiv_apply, Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right]

/-- **Two maps into subobjects, compared across a square of functors.**  Let
`γ : Φ_B ⋙ G ≅ F ⋙ Φ_A` be an isomorphism of functors.  On the source side let `ι₀_B : I_B ⟶ O_B`
and `ι₀_A : I_A ⟶ O_A` be maps, and `φ₀ : F I_B ⟶ I_A` a map lying over `σ₀ : F O_B ⟶ O_A`; on the
target side let `ι_B : 𝓘_B ⟶ 𝒪_B` and `ι_A : 𝓘_A ⟶ 𝒪_A` be maps with `ι_A` a monomorphism, and
`φ : G 𝓘_B ⟶ 𝓘_A` a map lying over `σ : G 𝒪_B ⟶ 𝒪_A`.  Suppose isomorphisms
`a_B : 𝓘_B ≅ Φ_B I_B` and `a_A : 𝓘_A ≅ Φ_A I_A` and maps `u_B : Φ_B O_B ⟶ 𝒪_B`,
`u_A : Φ_A O_A ⟶ 𝒪_A` are compatible with the maps `ι`, and that `γ` carries `σ₀` to `σ` through
`u_B` and `u_A`.  Then `γ` carries `φ₀` to `φ` through `a_B` and `a_A`. -/
theorem comp_eq_of_square_of_mono {C₁ C₂ D₁ D₂ : Type*} [Category C₁] [Category C₂]
    [Category D₁] [Category D₂] {Φ_B : C₁ ⥤ D₁} {G : D₁ ⥤ D₂} {F : C₁ ⥤ C₂} {Φ_A : C₂ ⥤ D₂}
    (γ : Φ_B ⋙ G ≅ F ⋙ Φ_A) {I_B O_B : C₁} {I_A O_A : C₂} (ι₀_B : I_B ⟶ O_B)
    (ι₀_A : I_A ⟶ O_A) (φ₀ : F.obj I_B ⟶ I_A) (σ₀ : F.obj O_B ⟶ O_A)
    (hφ₀ : φ₀ ≫ ι₀_A = F.map ι₀_B ≫ σ₀) {𝓘_B 𝒪_B : D₁} {𝓘_A 𝒪_A : D₂} (ι_B : 𝓘_B ⟶ 𝒪_B)
    (ι_A : 𝓘_A ⟶ 𝒪_A) [Mono ι_A] (φ : G.obj 𝓘_B ⟶ 𝓘_A) (σ : G.obj 𝒪_B ⟶ 𝒪_A)
    (hφ : φ ≫ ι_A = G.map ι_B ≫ σ) (a_B : 𝓘_B ≅ Φ_B.obj I_B) (a_A : 𝓘_A ≅ Φ_A.obj I_A)
    (u_B : Φ_B.obj O_B ⟶ 𝒪_B) (u_A : Φ_A.obj O_A ⟶ 𝒪_A)
    (ha_B : a_B.inv ≫ ι_B = Φ_B.map ι₀_B ≫ u_B) (ha_A : a_A.inv ≫ ι_A = Φ_A.map ι₀_A ≫ u_A)
    (hu : γ.inv.app O_B ≫ G.map u_B ≫ σ = Φ_A.map σ₀ ≫ u_A) :
    γ.inv.app I_B ≫ G.map a_B.inv ≫ φ = Φ_A.map φ₀ ≫ a_A.inv := by
  have hnat := γ.inv.naturality ι₀_B
  simp only [Functor.comp_map] at hnat
  rw [← cancel_mono ι_A]
  simp only [Category.assoc]
  rw [hφ, ← G.map_comp_assoc, ha_B, G.map_comp, Category.assoc, ha_A, ← Φ_A.map_comp_assoc, hφ₀,
    Φ_A.map_comp, Category.assoc, ← hu, ← Category.assoc, ← hnat, Category.assoc]

/-- Rearranging a square through two isomorphisms: if `θ.hom ≫ ιₛ = f ≫ c.inv` then
`θ.inv ≫ f = ιₛ ≫ c.hom`. -/
theorem Iso.inv_comp_eq_comp_hom_of_hom_comp_eq {C : Type*} [Category C] {A B X Y : C}
    (θ : A ≅ B) (c : Y ≅ X) {f : A ⟶ X} {ιₛ : B ⟶ Y} (h : θ.hom ≫ ιₛ = f ≫ c.inv) :
    θ.inv ≫ f = ιₛ ≫ c.hom := by
  rw [Iso.inv_comp_eq, ← Category.assoc, h, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The transpose of an isomorphism `R I ≅ J` along an adjunction whose counit is invertible at
`I`, compared with maps out of `I` and `J`. -/
theorem Adjunction.mapIso_symm_trans_counit_hom_comp {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {I O : D} {J U : C} (ι : I ⟶ O) (θ : R.obj I ≅ J)
    (ιₛ : J ⟶ U) (u : U ⟶ R.obj O) (h : θ.inv ≫ R.map ι = ιₛ ≫ u) [IsIso (adj.counit.app I)] :
    (L.mapIso θ.symm ≪≫ asIso (adj.counit.app I)).symm.inv ≫ ι =
      L.map ιₛ ≫ (adj.homEquiv _ _).symm u := by
  rw [Iso.symm_inv]
  have hn : adj.counit.app I ≫ ι = L.map (R.map ι) ≫ adj.counit.app O :=
    (adj.counit.naturality ι).symm
  rw [Iso.trans_hom, Functor.mapIso_hom, asIso_hom, Iso.symm_hom, Category.assoc, hn,
    ← Category.assoc, ← L.map_comp, h, L.map_comp, Category.assoc, Adjunction.homEquiv_counit]

end CategoryTheory

namespace SheafOfModules

section Unit

variable {C : Type*} [Category C] {D : Type*} [Category D] {E : Type*} [Category E]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {L : GrothendieckTopology E}

/-- The unit map of a composite morphism of ringed sites is the unit map of the first followed
by the direct image of the unit map of the second. -/
theorem unitToPushforwardObjUnit_comparisonComp {F : C ⥤ D} {G : D ⥤ E} [F.IsContinuous J K]
    [G.IsContinuous K L] [(F ⋙ G).IsContinuous J L]
    {R : Sheaf J RingCat.{u}} {R' : Sheaf K RingCat.{u}} {R'' : Sheaf L RingCat.{u}}
    (φ : R ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R')
    (ψ : R' ⟶ (G.sheafPushforwardContinuous RingCat.{u} K L).obj R'') :
    unitToPushforwardObjUnit φ ≫ (pushforward.{u} φ).map (unitToPushforwardObjUnit ψ) ≫
        (pushforwardComp.{u} φ ψ).hom.app (unit R'') =
      unitToPushforwardObjUnit (comparisonComp φ ψ) :=
  rfl

/-- The unit map is carried by `CategoryTheory.SheafOfModules.pushforwardCongr₂` to the unit map
of the transported structure map. -/
theorem unitToPushforwardObjUnit_pushforwardCongr₂ {F G : C ⥤ D} [F.IsContinuous J K]
    [G.IsContinuous J K] {R : Sheaf J RingCat.{u}} {R' : Sheaf K RingCat.{u}}
    (φ : R ⟶ (G.sheafPushforwardContinuous RingCat.{u} J K).obj R')
    {ψ : R ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R'} (e : F ≅ G)
    (he : φ ≫ (Functor.sheafPushforwardContinuousNatTrans e.hom _ _ _).app R' = ψ) :
    unitToPushforwardObjUnit φ ≫ (pushforwardCongr₂.{u} φ e he).hom.app (unit R') =
      unitToPushforwardObjUnit ψ := by
  subst he
  rfl

/-- The inverse of `CategoryTheory.SheafOfModules.pushforwardCongr₂` carries the unit map of the
transported structure map back to the unit map. -/
theorem unitToPushforwardObjUnit_pushforwardCongr₂_inv {F G : C ⥤ D} [F.IsContinuous J K]
    [G.IsContinuous J K] {R : Sheaf J RingCat.{u}} {R' : Sheaf K RingCat.{u}}
    (φ : R ⟶ (G.sheafPushforwardContinuous RingCat.{u} J K).obj R')
    {ψ : R ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R'} (e : F ≅ G)
    (he : φ ≫ (Functor.sheafPushforwardContinuousNatTrans e.hom _ _ _).app R' = ψ) :
    unitToPushforwardObjUnit ψ ≫ (pushforwardCongr₂.{u} φ e he).inv.app (unit R') =
      unitToPushforwardObjUnit φ := by
  rw [← unitToPushforwardObjUnit_pushforwardCongr₂ φ e he, Category.assoc, ← NatTrans.comp_app,
    Iso.hom_inv_id, NatTrans.id_app, Category.comp_id]

end Unit

end SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pulling a function on an open `O` of `Y` back along a morphism `b : P ⟶ O` is pulling it back
along `f` to `f⁻¹(O)` and then along `a : P ⟶ f⁻¹(O)`, as soon as `a` and `b` agree over `Y`. -/
theorem _root_.AlgebraicGeometry.Scheme.Opens.topIso_inv_appTop_of_preimage {X Y P : Scheme.{u}}
    (f : X ⟶ Y) (O : Y.Opens) (a : P ⟶ (f ⁻¹ᵁ O).toScheme) (b : P ⟶ O.toScheme)
    (h : a ≫ (f ⁻¹ᵁ O).ι ≫ f = b ≫ O.ι) :
    f.app O ≫ (f ⁻¹ᵁ O).topIso.inv ≫ a.appTop = O.topIso.inv ≫ b.appTop := by
  have hb : b = a ≫ f.resLE O (f ⁻¹ᵁ O) le_rfl := by
    rw [← cancel_mono O.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, ← h]
  have h2 := Scheme.Opens.topIso_inv_appTop_of_comp f O (f.resLE O (f ⁻¹ᵁ O) le_rfl)
    (Scheme.Hom.resLE_comp_ι _ _)
  rw [hb, Scheme.Hom.comp_appTop, ← Category.assoc, ← h2, Category.assoc]

section Spelling

variable (X : AlgebraicSpaces B S hS)

/-- Sheaves of modules over the structure sheaf of rings of an algebraic space, read as its
`𝒪`-modules: the identity on objects and morphisms between two spellings of one category. -/
noncomputable def structureModulesToModules :
    SheafOfModules.{u} (structureRingSheaf B S hS X) ⥤ Modules.{u, u} B S hS X.1 X.2 where
  obj M := M
  map f := f

/-- The inverse of `AlgebraicGeometry.Space.structureModulesToModules`. -/
noncomputable def modulesToStructureModules :
    Modules.{u, u} B S hS X.1 X.2 ⥤ SheafOfModules.{u} (structureRingSheaf B S hS X) where
  obj M := M
  map f := f

/-- The two spellings of the `𝒪`-modules of an algebraic space are equivalent, by the
identity. -/
noncomputable def structureModulesEquivalence :
    SheafOfModules.{u} (structureRingSheaf B S hS X) ≌ Modules.{u, u} B S hS X.1 X.2 where
  functor := structureModulesToModules B S hS X
  inverse := modulesToStructureModules B S hS X
  unitIso := Iso.refl _
  counitIso := Iso.refl _

end Spelling

section IdealMap

variable {X X' : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
  (Z' : ClosedSubspaces B S hS X'.1) (g : X ⟶ X')
  (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))
  (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z')

/-- `AlgebraicGeometry.Space.idealSheafMap`, between the defining ideal sheaves read as
`𝒪`-modules. -/
noncomputable def definingIdealModuleMap :
    (modulePullback B S hS g).obj
        ((structureModulesToModules B S hS X').obj
            (definingIdealSheaf B S hS X' Z').toSheafOfModules) ⟶
      (structureModulesToModules B S hS X).obj (definingIdealSheaf B S hS X Z).toSheafOfModules :=
  idealSheafMap B S hS Z Z' g f hsq

/-- `AlgebraicGeometry.Space.idealSheafMap_comp_definingIdealSheaf_ι`, for the defining ideal
sheaves read as `𝒪`-modules. -/
theorem definingIdealModuleMap_comp_ι :
    definingIdealModuleMap B S hS Z Z' g f hsq ≫
        (structureModulesToModules B S hS X).map (definingIdealSheaf B S hS X Z).ι =
      (modulePullback B S hS g).map
          ((structureModulesToModules B S hS X').map (definingIdealSheaf B S hS X' Z').ι) ≫
        structureModulePullbackMap B S hS g :=
  idealSheafMap_comp_definingIdealSheaf_ι B S hS Z Z' g f hsq

/-- The inclusion of the defining ideal sheaf, read as a map of `𝒪`-modules, is a
monomorphism. -/
theorem mono_map_definingIdealSheaf_ι :
    Mono ((structureModulesToModules B S hS X).map (definingIdealSheaf B S hS X Z).ι) :=
  (definingIdealShortComplex_shortExact B S hS X Z).mono_f

end IdealMap


section Model

variable (T : BigFppfOver B S hS)

/-- The Zariski model functor of a representable algebraic space: the associated-module functor
of the small étale site of the scheme underlying `T`, read on the small étale site of
`yoneda.obj T`. -/
noncomputable abbrev zariskiModel :
    SheafOfModules.{u} (chartScheme (idEtaleChart B S hS T)).ringCatSheaf ⥤
      Modules.{u, u} B S hS
        (⟨yoneda.obj T, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T⟩ :
            AlgebraicSpaces B S hS).1
        (⟨yoneda.obj T, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T⟩ :
            AlgebraicSpaces B S hS).2 :=
  (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property ⋙
    (representedSmallEtaleModuleEquivalence B S hS T).functor) ⋙
    structureModulesToModules B S hS ⟨yoneda.obj T,
        AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T⟩

/-- The structure map of restriction to the Zariski opens: over an open `V` of the scheme
underlying `T`, the identification of the functions on `V` with the global functions of the
étale chart `V` cuts out. -/
noncomputable abbrev zariskiRestrictionSharp :
    (chartScheme (idEtaleChart B S hS T)).ringCatSheaf ⟶
      ((openChartFunctor B S hS (yoneda.obj T) (idEtaleChart B S hS T)).sheafPushforwardContinuous
        RingCat.{u} (Opens.grothendieckTopology ↥(chartScheme (idEtaleChart B S hS T)))
        (SmallEtale.topology B S hS (yoneda.obj T))).obj
        (representedStructureRingSheaf B S hS T) :=
  chartSchemeRestrictionSheafHom B S hS (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T)
    (idEtaleChart B S hS T)

/-- Restriction of an `𝒪`-module on the small étale site of `yoneda.obj T` to the Zariski opens
of the scheme underlying `T`, read as étale charts of `yoneda.obj T`; this is
`AlgebraicGeometry.Space.chartSchemePushforward` at the identity chart. -/
noncomputable abbrev zariskiRestriction₀ :
    SheafOfModules.{u} (representedStructureRingSheaf B S hS T) ⥤
      SheafOfModules.{u} (chartScheme (idEtaleChart B S hS T)).ringCatSheaf :=
  SheafOfModules.pushforward.{u} (zariskiRestrictionSharp B S hS T)

/-- Restriction of an `𝒪`-module on the small étale site of `yoneda.obj T` to the Zariski opens
of the scheme underlying `T`, read as étale charts of `yoneda.obj T`. -/
noncomputable abbrev zariskiRestriction :
    Modules.{u, u} B S hS
        (⟨yoneda.obj T, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T⟩ :
            AlgebraicSpaces B S hS).1
        (⟨yoneda.obj T, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T⟩ :
            AlgebraicSpaces B S hS).2 ⥤
      SheafOfModules.{u} (chartScheme (idEtaleChart B S hS T)).ringCatSheaf :=
  modulesToStructureModules B S hS ⟨yoneda.obj T,
      AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T⟩ ⋙ zariskiRestriction₀ B S hS T

/-- The two structure maps of the Zariski opens of the scheme underlying `T`, read as étale charts
of `yoneda.obj T` directly and through the identification of the two small étale sites, agree. -/
theorem selfOpensStructureMap_comp_selfOpensFunctorIso :
    selfOpensStructureMap B S hS T ≫
        (Functor.sheafPushforwardContinuousNatTrans (selfOpensFunctorIso B S hS T).hom
          RingCat.{u} (Opens.grothendieckTopology ↥(chartScheme (idEtaleChart B S hS T)))
          (SmallEtale.topology B S hS (yoneda.obj T))).app
          (representedStructureRingSheaf B S hS T) =
      chartSchemeRestrictionSheafHom B S hS
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T) (idEtaleChart B S hS T) := by
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun O => ?_)
  have h1 : (representedSmallEtaleEquivalence B S hS T).counit.app
      (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property O.unop) = 𝟙 _ :=
    @Subsingleton.elim _ (_root_.AlgebraicGeometry.SmallEtale.subsingleton_hom_opensToSmallEtale
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T) T.left.property _ O.unop)
      _ _
  have h2 : ((((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T)
        T.left.property).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology ↥((BigFppfOver.toScheme B S hS).obj T))
        (representedSchemeSmallEtaleTopology B S hS T)).map
        (Stacks.SheafOfModules.reindexBackSharp
          (J' := SmallEtale.topology B S hS (yoneda.obj T))
          (representedSmallEtaleEquivalence B S hS T)
          (representedSchemeStructureSheaf B S hS T))).hom.app O) = 𝟙 _ := by
    change (representedSchemeStructureSheaf B S hS T).obj.map
        ((representedSmallEtaleEquivalence B S hS T).counit.app
          (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj T) T.left.property O.unop)).op = 𝟙 _
    exact (congrArg (fun k => (representedSchemeStructureSheaf B S hS T).obj.map
          (Quiver.Hom.op k)) h1).trans
      ((congrArg (representedSchemeStructureSheaf B S hS T).obj.map op_id).trans
        ((representedSchemeStructureSheaf B S hS T).obj.map_id _))
  have h3 : ((Functor.sheafPushforwardContinuousNatTrans (selfOpensFunctorIso B S hS T).hom
        RingCat.{u} (Opens.grothendieckTopology ↥(chartScheme (idEtaleChart B S hS T)))
        (SmallEtale.topology B S hS (yoneda.obj T))).app
        (representedStructureRingSheaf B S hS T)).hom.app O = 𝟙 _ := by
    change (representedStructureRingSheaf B S hS T).obj.map
      (eqToHom (selfOpensFunctor_obj B S hS T O.unop).symm).op = 𝟙 _
    exact (congrArg (representedStructureRingSheaf B S hS T).obj.map (eqToHom_op _)).trans
      ((eqToHom_map (representedStructureRingSheaf B S hS T).obj _).trans rfl)
  change (_ ≫ _) ≫ _ = _
  rw [h2, h3]
  exact (Category.comp_id _).trans (Category.comp_id _)

/-- Restriction to the Zariski opens through the identification of the two small étale sites is
restriction to the Zariski opens read as étale charts directly. -/
noncomputable def zariskiRestrictionIso :
    (representedSmallEtaleModuleEquivalence B S hS T).inverse ⋙
        _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T) T.left.property ≅
      zariskiRestriction₀ B S hS T :=
  SheafOfModules.pushforwardComp.{u}
      (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property)
      (Stacks.SheafOfModules.reindexBackSharp
        (J' := SmallEtale.topology B S hS (yoneda.obj T))
        (representedSmallEtaleEquivalence B S hS T)
        (representedSchemeStructureSheaf B S hS T)) ≪≫
    SheafOfModules.pushforwardCongr₂.{u} (selfOpensStructureMap B S hS T)
      (ψ := zariskiRestrictionSharp B S hS T)
      (selfOpensFunctorIso B S hS T)
      (selfOpensStructureMap_comp_selfOpensFunctorIso B S hS T)

/-- The Zariski model functor is left adjoint to restriction to the Zariski opens. -/
noncomputable def zariskiModelAdjunction :
    zariskiModel B S hS T ⊣ zariskiRestriction B S hS T :=
  (((_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property).comp
    (representedSmallEtaleModuleEquivalence B S hS T).toAdjunction).comp
    (structureModulesEquivalence B S hS ⟨yoneda.obj T,
        AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T⟩).toAdjunction).ofNatIsoRight
    (Functor.isoWhiskerLeft (modulesToStructureModules B S hS
        ⟨yoneda.obj T, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T⟩)
      (zariskiRestrictionIso B S hS T))

/-- **The counit of the Zariski model is an isomorphism at a quasi-coherent module**
([Stacks, Tag 03DX]). -/
theorem isIso_zariskiModelAdjunction_counit_app
    (N : Modules.{u, u} B S hS
        (⟨yoneda.obj T, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T⟩ :
            AlgebraicSpaces B S hS).1
        (⟨yoneda.obj T, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T⟩ :
            AlgebraicSpaces B S hS).2)
    (hN : N.IsQuasicoherentOnSite) :
    IsIso ((zariskiModelAdjunction B S hS T).counit.app N) := by
  let E := representedSmallEtaleModuleEquivalence B S hS T
  have hG : (E.inverse.obj N).IsQuasicoherentOnSite :=
    (isQuasicoherentOnSite_representedSmallEtaleModule_iff B S hS T _).1
      (SheafOfModules.IsQuasicoherentOnSite.of_iso (E.counitIso.app N).symm hN)
  have hc := _root_.AlgebraicGeometry.SmallEtale.isIso_counit (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj T) T.left.property (E.inverse.obj N) hG
    (_root_.AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule _ _ _ _ hG)
  have h : (zariskiModelAdjunction B S hS T).counit.app N =
      (zariskiModel B S hS T).map ((zariskiRestrictionIso B S hS T).inv.app N) ≫
        (structureModulesToModules B S hS
            ⟨yoneda.obj T, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T⟩).map
          (E.functor.map ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction
            (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T)
            T.left.property).counit.app (E.inverse.obj N)) ≫ E.counit.app N) := by
    simp [zariskiModelAdjunction, structureModulesEquivalence]
    rfl
  rw [h]
  have h2 : IsIso ((zariskiModel B S hS T).map ((zariskiRestrictionIso B S hS T).inv.app N)) :=
    Iso.isIso_hom ((zariskiModel B S hS T).mapIso ((zariskiRestrictionIso B S hS T).app N).symm)
  have h3 : IsIso (E.functor.map ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T)
      T.left.property).counit.app (E.inverse.obj N))) := Functor.map_isIso _ _
  have h4 : IsIso (E.counit.app N) := Iso.isIso_hom (E.counitIso.app N)
  have h5 : IsIso ((structureModulesToModules B S hS
      ⟨yoneda.obj T, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T⟩).map
      (E.functor.map ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction
        (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T)
        T.left.property).counit.app (E.inverse.obj N)) ≫ E.counit.app N)) :=
    Functor.map_isIso _ _
  exact IsIso.comp_isIso' h2 h5

/-- The structure map `Φ_T 𝒪_{T₀} ⟶ 𝒪` of the Zariski model: the transpose of the identification
of `𝒪_{T₀}` with the restriction of `𝒪` to the Zariski opens. -/
noncomputable def zariskiUnitMap :
    (zariskiModel B S hS T).obj
        (SheafOfModules.unit (chartScheme (idEtaleChart B S hS T)).ringCatSheaf) ⟶
      SheafOfModules.unit (representedStructureRingSheaf B S hS T) :=
  ((zariskiModelAdjunction B S hS T).homEquiv _ _).symm
    (SheafOfModules.unitToPushforwardObjUnit (zariskiRestrictionSharp B S hS T))

/-- The transpose of `AlgebraicGeometry.Space.zariskiUnitMap` is the identification of `𝒪_{T₀}`
with the restriction of `𝒪`. -/
theorem homEquiv_zariskiUnitMap :
    (zariskiModelAdjunction B S hS T).homEquiv _ _ (zariskiUnitMap B S hS T) =
      SheafOfModules.unitToPushforwardObjUnit (zariskiRestrictionSharp B S hS T) :=
  Equiv.apply_symm_apply _ _

end Model

section Ideal

variable (T : BigFppfOver B S hS) (Z : ClosedSubspaces B S hS (yoneda.obj T))

/-- The closed immersion of schemes cut out of the scheme underlying `T` by a closed subspace of
`yoneda.obj T`. -/
noncomputable abbrev zariskiClosedImmersion :
    (BigFppfOver.toScheme B S hS).obj (Z.2.2.rep.pullback (idEtaleChart B S hS T).1.hom) ⟶
      chartScheme (idEtaleChart B S hS T) :=
  chartBaseChangeHom B S hS ⟨yoneda.obj T, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T⟩
      Z (idEtaleChart B S hS T)

/-- The identification of the restriction of the defining ideal sheaf to the Zariski opens with
the ideal sheaf of the closed immersion respects the inclusions into the structure sheaves. -/
theorem chartSchemePushforwardDefiningIdealIso_hom_comp_ι :
    (chartSchemePushforwardDefiningIdealIso B S hS ⟨yoneda.obj T,
        AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T⟩ (idEtaleChart B S hS T) Z).hom ≫
        Stacks.ClosedImmersion.idealSheafι (zariskiClosedImmersion B S hS T Z).toLRSHom.toShHom =
      chartIdealToUnit B S hS ⟨yoneda.obj T, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T⟩
          (idEtaleChart B S hS T) Z := by
  have h := Stacks.ClosedImmersion.idealSheafKerObjIso_hom_comp_kerIota
    (zariskiClosedImmersion B S hS T Z)
  have h' : (Stacks.Conormal.idealSheafKerObjIso (zariskiClosedImmersion B S hS T Z)).inv ≫
      Stacks.ClosedImmersion.idealSheafι (zariskiClosedImmersion B S hS T Z).toLRSHom.toShHom =
      SheafOfModules.kerIota (SheafOfModules.unitToPushforwardObjUnit
        (zariskiClosedImmersion B S hS T Z).toRingCatSheafHom) :=
    (Iso.inv_comp_eq _).2 h.symm
  change (chartIdealToKer B S hS ⟨yoneda.obj T, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T⟩
      (idEtaleChart B S hS T) Z ≫
    (Stacks.Conormal.idealSheafKerObjIso (zariskiClosedImmersion B S hS T Z)).inv) ≫ _ = _
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (chartIdealToKer B S hS ⟨yoneda.obj T, AlgebraicGeometry.isAlgebraicSpace_yoneda
      B S hS T⟩ (idEtaleChart B S hS T) Z ≫ ·) h').trans ?_
  exact SheafOfModules.kerLift_comp _ _

/-- The defining ideal sheaf of a closed subspace of `yoneda.obj T`, as an `𝒪`-module. -/
noncomputable abbrev representedDefiningIdealModule :
    Modules.{u, u} B S hS
      (⟨yoneda.obj T, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T⟩ :
          AlgebraicSpaces B S hS).1
      (⟨yoneda.obj T, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T⟩ :
          AlgebraicSpaces B S hS).2 :=
  (structureModulesToModules B S hS ⟨yoneda.obj T,
      AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T⟩).obj
    (definingIdealSheaf B S hS ⟨yoneda.obj T,
        AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T⟩ Z).toSheafOfModules

/-- The inclusion of the defining ideal sheaf into the structure sheaf, as a morphism of
`𝒪`-modules. -/
noncomputable abbrev representedDefiningIdealι :
    representedDefiningIdealModule B S hS T Z ⟶
      (structureModulesToModules B S hS ⟨yoneda.obj T,
          AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T⟩).obj
        (SheafOfModules.unit (structureRingSheaf B S hS
            ⟨yoneda.obj T, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T⟩)) :=
  (structureModulesToModules B S hS ⟨yoneda.obj T,
      AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T⟩).map
    (definingIdealSheaf B S hS ⟨yoneda.obj T,
        AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T⟩ Z).ι

/-- The restriction of the defining ideal sheaf to the Zariski opens is the ideal sheaf of the
closed immersion. -/
noncomputable def zariskiRestrictionDefiningIdealIso :
    (zariskiRestriction B S hS T).obj (representedDefiningIdealModule B S hS T Z) ≅
      Stacks.ClosedImmersion.idealSheaf (zariskiClosedImmersion B S hS T Z).toLRSHom.toShHom :=
  chartSchemePushforwardDefiningIdealIso B S hS
      ⟨yoneda.obj T, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T⟩ (idEtaleChart B S hS T) Z

/-- The identification of the restricted defining ideal sheaf with the ideal sheaf of the closed
immersion respects the inclusions into the structure sheaves. -/
theorem zariskiRestrictionDefiningIdealIso_inv_comp :
    (zariskiRestrictionDefiningIdealIso B S hS T Z).inv ≫
        (zariskiRestriction B S hS T).map (representedDefiningIdealι B S hS T Z) =
      Stacks.ClosedImmersion.idealSheafι (zariskiClosedImmersion B S hS T Z).toLRSHom.toShHom ≫
        SheafOfModules.unitToPushforwardObjUnit (zariskiRestrictionSharp B S hS T) :=
  Iso.inv_comp_eq_comp_hom_of_hom_comp_eq _
    (chartUnitIso B S hS ⟨yoneda.obj T, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T⟩
        (idEtaleChart B S hS T))
    (chartSchemePushforwardDefiningIdealIso_hom_comp_ι B S hS T Z)

/-- **The defining ideal sheaf of a closed subspace of a representable algebraic space is the
Zariski model of the ideal sheaf of the corresponding closed immersion of schemes**: the
transpose of the identification of its restriction to the Zariski opens with that ideal sheaf,
an isomorphism because the counit of the Zariski model is one at a quasi-coherent module. -/
noncomputable def definingIdealSheafZariskiModelIso :
    representedDefiningIdealModule B S hS T Z ≅
      (zariskiModel B S hS T).obj
        (Stacks.ClosedImmersion.idealSheaf (zariskiClosedImmersion B S hS T Z).toLRSHom.toShHom) :=
  ((zariskiModel B S hS T).mapIso (zariskiRestrictionDefiningIdealIso B S hS T Z).symm ≪≫
    @asIso _ _ _ _ ((zariskiModelAdjunction B S hS T).counit.app
      (representedDefiningIdealModule B S hS T Z))
      (isIso_zariskiModelAdjunction_counit_app B S hS T
        (representedDefiningIdealModule B S hS T Z)
        (isQuasicoherentOnSite_definingIdealSheaf B S hS
            ⟨yoneda.obj T, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T⟩ Z))).symm

/-- The identification of the defining ideal sheaf with the Zariski model of the ideal sheaf is
compatible with the inclusions into the structure sheaves. -/
theorem definingIdealSheafZariskiModelIso_inv_comp_ι :
    (definingIdealSheafZariskiModelIso B S hS T Z).inv ≫ representedDefiningIdealι B S hS T Z =
      (zariskiModel B S hS T).map
          (Stacks.ClosedImmersion.idealSheafι
              (zariskiClosedImmersion B S hS T Z).toLRSHom.toShHom) ≫
        zariskiUnitMap B S hS T  := by
  have := isIso_zariskiModelAdjunction_counit_app B S hS T
    (representedDefiningIdealModule B S hS T Z)
    (isQuasicoherentOnSite_definingIdealSheaf B S hS
      ⟨yoneda.obj T, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T⟩ Z)
  have h := (zariskiModelAdjunction B S hS T).mapIso_symm_trans_counit_hom_comp
    (representedDefiningIdealι B S hS T Z) (zariskiRestrictionDefiningIdealIso B S hS T Z) _ _
    (zariskiRestrictionDefiningIdealIso_inv_comp B S hS T Z)
  exact h

end Ideal

section Pushforward

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

variable {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
  (hg : yoneda.relativelyRepresentable (yoneda.map g))

/-- The morphism of schemes underlying `g`, between the schemes of the two identity charts. -/
noncomputable abbrev idChartSchemeHom :
    chartScheme (idEtaleChart B S hS T') ⟶ chartScheme (idEtaleChart B S hS T) :=
  (BigFppfOver.toScheme B S hS).map g

/-- Reading a Zariski open as an étale chart and base changing along `g` is continuous. -/
instance isContinuous_openChartFunctor_comp_smallBaseChange :
    (openChartFunctor B S hS (yoneda.obj T) (idEtaleChart B S hS T) ⋙
        smallBaseChange B S hS (representedSpaceMap B S hS g) hg).IsContinuous
      (Opens.grothendieckTopology ↥(chartScheme (idEtaleChart B S hS T)))
      (SmallEtale.topology B S hS (yoneda.obj T')) :=
  @Functor.isContinuous_comp _ _ _ _ _ _ _ _ _ _ _
    (isContinuous_openChartFunctor_idEtaleChart B S hS T)
    (isContinuous_smallBaseChange B S hS (representedSpaceMap B S hS g) hg)

/-- Taking the preimage along `g` of a Zariski open and reading it as an étale chart is
continuous. -/
instance isContinuous_opensMap_comp_openChartFunctor :
    (Opens.map (idChartSchemeHom B S hS g).base ⋙
        openChartFunctor B S hS (yoneda.obj T') (idEtaleChart B S hS T')).IsContinuous
      (Opens.grothendieckTopology ↥(chartScheme (idEtaleChart B S hS T)))
      (SmallEtale.topology B S hS (yoneda.obj T')) :=
  @Functor.isContinuous_comp _ _ _ _ _ _ _ _ _ _ _
    (instIsContinuousOpensCarrierMapGrothendieckTopology _)
    (isContinuous_openChartFunctor_idEtaleChart B S hS T')

/-- **Base change of the chart cut out by a Zariski open is the chart cut out by its preimage.**
Reading a Zariski open `O` of the scheme underlying `T` as an étale chart of `yoneda.obj T` and
base changing along `g` is reading `g⁻¹(O)` as an étale chart of `yoneda.obj T'`. -/
noncomputable def openChartFunctorBaseChangeIso :
    openChartFunctor B S hS (yoneda.obj T) (idEtaleChart B S hS T) ⋙
        smallBaseChange B S hS (representedSpaceMap B S hS g) hg ≅
      Opens.map (idChartSchemeHom B S hS g).base ⋙
        openChartFunctor B S hS (yoneda.obj T') (idEtaleChart B S hS T') :=
  Functor.isoWhiskerRight (selfOpensFunctorIso B S hS T) _ ≪≫
    (Iso.isoCompInverse (H := representedSmallEtaleEquivalence B S hS T')
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (representedSmallEtaleBaseChangeIso B S hS g hg) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (Functor.associator _ _ _) _ ≪≫
        Functor.isoWhiskerRight (Functor.isoWhiskerLeft _
          (representedSmallEtaleEquivalence B S hS T).counitIso) _ ≪≫
        Functor.isoWhiskerRight (Functor.rightUnitor _) _ ≪≫
        (_root_.AlgebraicGeometry.SmallEtale.baseChangeOpensIso
          (associatedBigEtaleSite B) g.left).symm)) ≪≫
    Functor.isoWhiskerLeft _ (selfOpensFunctorIso B S hS T').symm

/-- The component of `AlgebraicGeometry.Space.openChartFunctorBaseChangeIso` at a Zariski open `V`,
followed by the inclusion of `g⁻¹(V)` and `g`, is the cartesian projection to `V` followed by the
inclusion of `V`. -/
theorem openChartFunctorBaseChangeIso_hom_app_comp
    (V : (chartScheme (idEtaleChart B S hS T)).Opens) :
    (BigFppfOver.toScheme B S hS).map
        ((openChartFunctorBaseChangeIso B S hS g hg).hom.app V).hom.left ≫
      Scheme.Opens.ι (idChartSchemeHom B S hS g ⁻¹ᵁ V) ≫ idChartSchemeHom B S hS g =
    (BigFppfOver.toScheme B S hS).map
      (hg.snd ((openChartFunctor B S hS (yoneda.obj T) (idEtaleChart B S hS T)).obj V).1.hom) ≫
      Scheme.Opens.ι V := by
  let g₀ := idChartSchemeHom B S hS g
  let k := (openChartFunctorBaseChangeIso B S hS g hg).hom.app V
  let X := (openChartFunctor B S hS (yoneda.obj T) (idEtaleChart B S hS T)).obj V
  have hw := CostructuredArrow.w k.hom
  have e₁ : ((Opens.map (idChartSchemeHom B S hS g).base ⋙
      openChartFunctor B S hS (yoneda.obj T') (idEtaleChart B S hS T')).obj V).obj.hom =
      yoneda.map (openSubHom
        ((SmallEtale.toOver B S hS (yoneda.obj T')).obj (idEtaleChart B S hS T')) (g₀ ⁻¹ᵁ V)) ≫
        𝟙 _ := rfl
  have e₂ : ((openChartFunctor B S hS (yoneda.obj T) (idEtaleChart B S hS T) ⋙
      smallBaseChange B S hS (representedSpaceMap B S hS g) hg).obj V).obj.hom =
      hg.fst X.1.hom := rfl
  have e₃ : X.1.hom = yoneda.map (openSubHom
      ((SmallEtale.toOver B S hS (yoneda.obj T)).obj (idEtaleChart B S hS T)) V) ≫ 𝟙 _ := rfl
  rw [e₁, e₂, Category.comp_id] at hw
  have w₁ : yoneda.map k.hom.left ≫ yoneda.map (openSubHom
      ((SmallEtale.toOver B S hS (yoneda.obj T')).obj (idEtaleChart B S hS T')) (g₀ ⁻¹ᵁ V)) =
        hg.fst X.1.hom := hw
  have w₂ : hg.fst X.1.hom ≫ yoneda.map g = yoneda.map (hg.snd X.1.hom) ≫ yoneda.map (openSubHom
      ((SmallEtale.toOver B S hS (yoneda.obj T)).obj (idEtaleChart B S hS T)) V) := by
    have := hg.w X.1.hom
    rw [e₃, Category.comp_id] at this
    exact this
  have w₃ : k.hom.left ≫ openSubHom
      ((SmallEtale.toOver B S hS (yoneda.obj T')).obj (idEtaleChart B S hS T')) (g₀ ⁻¹ᵁ V) ≫ g =
      hg.snd X.1.hom ≫ openSubHom
        ((SmallEtale.toOver B S hS (yoneda.obj T)).obj (idEtaleChart B S hS T)) V :=
    yoneda.map_injective (((yoneda.map_comp _ _).trans
      (congrArg (yoneda.map k.hom.left ≫ ·) (yoneda.map_comp _ _))).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ yoneda.map g) w₁).trans
        (w₂.trans (yoneda.map_comp _ _).symm))))
  have w₄ := congrArg (BigFppfOver.toScheme B S hS).map w₃
  refine (congrArg ((BigFppfOver.toScheme B S hS).map k.hom.left ≫ ·)
    (congrArg (· ≫ g₀) (toScheme_map_openSubHom B S hS _ _).symm)).trans ?_
  refine (congrArg ((BigFppfOver.toScheme B S hS).map k.hom.left ≫ ·)
    ((BigFppfOver.toScheme B S hS).map_comp _ _).symm).trans ?_
  refine ((BigFppfOver.toScheme B S hS).map_comp _ _).symm.trans ?_
  refine w₄.trans ?_
  refine ((BigFppfOver.toScheme B S hS).map_comp _ _).trans ?_
  exact congrArg (_ ≫ ·) (toScheme_map_openSubHom B S hS _ _)

/-- The two composite structure maps round the square of
`AlgebraicGeometry.Space.openChartFunctorBaseChangeIso` agree: over a Zariski open `O` both pull a
function on `O` back to the base change of the chart `O` cuts out. -/
theorem structureMap_comp_openChartBaseChangeIso :
    SheafOfModules.comparisonComp
        (idChartSchemeHom B S hS g).toRingCatSheafHom
        (zariskiRestrictionSharp B S hS T') ≫
      (Functor.sheafPushforwardContinuousNatTrans (openChartFunctorBaseChangeIso B S hS g hg).hom
        RingCat.{u} (Opens.grothendieckTopology ↥(chartScheme (idEtaleChart B S hS T)))
        (SmallEtale.topology B S hS (yoneda.obj T'))).app
        (representedStructureRingSheaf B S hS T') =
    SheafOfModules.comparisonComp
      (zariskiRestrictionSharp B S hS T)
      (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg) := by
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun V => ?_)
  obtain ⟨V⟩ := V
  ext x
  let g₀ := idChartSchemeHom B S hS g
  let k := (openChartFunctorBaseChangeIso B S hS g hg).hom.app V
  have hk := openChartFunctorBaseChangeIso_hom_app_comp B S hS g hg V
  have H := ConcreteCategory.congr_hom
    (Scheme.Opens.topIso_inv_appTop_of_preimage g₀ V _ _ hk) x
  have hR : (SheafOfModules.comparisonComp (zariskiRestrictionSharp B S hS T)
        (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg)).hom.app (op V) =
      (forget₂ CommRingCat RingCat).map ((Scheme.Opens.topIso V).inv ≫
        Scheme.Hom.appTop ((BigFppfOver.toScheme B S hS).map
          (hg.snd ((openChartFunctor B S hS (yoneda.obj T)
              (idEtaleChart B S hS T)).obj V).1.hom))) := by
    rfl
  have hL : (SheafOfModules.comparisonComp (idChartSchemeHom B S hS g).toRingCatSheafHom
          (zariskiRestrictionSharp B S hS T') ≫
        (Functor.sheafPushforwardContinuousNatTrans (openChartFunctorBaseChangeIso B S hS g hg).hom
          RingCat.{u} (Opens.grothendieckTopology ↥(chartScheme (idEtaleChart B S hS T)))
          (SmallEtale.topology B S hS (yoneda.obj T'))).app
          (representedStructureRingSheaf B S hS T')).hom.app (op V) =
      (forget₂ CommRingCat RingCat).map (Scheme.Hom.app g₀ V ≫ (g₀ ⁻¹ᵁ V).topIso.inv ≫
        Scheme.Hom.appTop ((BigFppfOver.toScheme B S hS).map k.hom.left)) := by
    rfl
  rw [hL, hR]
  exact H
/-- The direct image of sheaves of modules along `g₀` has a left adjoint. -/
instance isRightAdjoint_pushforward_idChartSchemeHom :
    (SheafOfModules.pushforward.{u} (idChartSchemeHom B S hS g).toRingCatSheafHom).IsRightAdjoint :=
  inferInstanceAs (Scheme.Modules.pushforward (idChartSchemeHom B S hS g)).IsRightAdjoint

/-- **The direct images commute with restriction to the Zariski opens**:
`R_T ∘ g_* ≅ g₀_* ∘ R_{T'}`, for `g₀` the morphism of schemes underlying `g`. -/
noncomputable def zariskiRestrictionPushforwardIso :
    modulePushforward B S hS (representedSpaceMap B S hS g) ⋙ zariskiRestriction B S hS T ≅
      zariskiRestriction B S hS T' ⋙
        SheafOfModules.pushforward.{u} (idChartSchemeHom B S hS g).toRingCatSheafHom :=
  Functor.isoWhiskerRight (modulePushforwardChartIso B S hS (representedSpaceMap B S hS g) hg) _ ≪≫
    SheafOfModules.pushforwardComp.{u} (zariskiRestrictionSharp B S hS T)
      (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg) ≪≫
    (SheafOfModules.pushforwardCongr₂.{u}
      (SheafOfModules.comparisonComp (idChartSchemeHom B S hS g).toRingCatSheafHom
        (zariskiRestrictionSharp B S hS T'))
      (openChartFunctorBaseChangeIso B S hS g hg)
      (structureMap_comp_openChartBaseChangeIso B S hS g hg)).symm ≪≫
    (SheafOfModules.pushforwardComp.{u} (idChartSchemeHom B S hS g).toRingCatSheafHom
      (zariskiRestrictionSharp B S hS T')).symm

/-- **The Zariski model commutes with inverse images**: `Φ_T ⋙ g^* ≅ g₀^* ⋙ Φ_{T'}`, the
conjugate of `AlgebraicGeometry.Space.zariskiRestrictionPushforwardIso`. -/
noncomputable def zariskiModelPullbackIso :
    zariskiModel B S hS T ⋙ modulePullback B S hS (representedSpaceMap B S hS g) ≅
      RingedSpaceModuleAdjunction.modulePullback (idChartSchemeHom B S hS g).toLRSHom.toShHom ⋙
        zariskiModel B S hS T' :=
  (conjugateIsoEquiv
    ((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
          (idChartSchemeHom B S hS g).toLRSHom.toShHom).comp
      (zariskiModelAdjunction B S hS T'))
    ((zariskiModelAdjunction B S hS T).comp
      (modulePullbackAdjunction B S hS (representedSpaceMap B S hS g)))).symm
    (zariskiRestrictionPushforwardIso B S hS g hg).symm

/-- **The transpose of the structure map, read on the base-changed charts, is pullback of
functions along the cartesian projection**: the transpose `𝒪 ⟶ g_*𝒪` of the structure map
`g^*𝒪 ⟶ 𝒪`, followed by the identification of the direct image with restriction along base
change of charts, is the unit map of `AlgebraicGeometry.Space.smallBaseChangeSharp`. -/
theorem structureModulePullbackMap_transpose_comp_chartIso :
    ((modulePullbackAdjunction B S hS (representedSpaceMap B S hS g)).homEquiv _ _
        (structureModulePullbackMap B S hS (representedSpaceMap B S hS g))) ≫
      (modulePushforwardChartIso B S hS (representedSpaceMap B S hS g) hg).hom.app
        (SheafOfModules.unit (structureRingSheaf B S hS
          ⟨yoneda.obj T', AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T'⟩)) =
      SheafOfModules.unitToPushforwardObjUnit
        (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg) := by
  apply (Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheaf B S hS
      ⟨yoneda.obj T, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T⟩)).map_injective
  refine ((Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheaf B S hS
      ⟨yoneda.obj T, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T⟩)).map_comp _ _).trans ?_
  have h1 := moduleSheafFunctor_map_homEquiv_structureModulePullbackMap B S hS
    (representedSpaceMap B S hS g)
  have h2 := moduleSheafFunctor_map_modulePushforwardChartIso_hom_app B S hS
      (representedSpaceMap B S hS g) hg
      (SheafOfModules.unit (structureRingSheaf B S hS
          ⟨yoneda.obj T', AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T'⟩))
  rw [chartComparison_hom_app (f := representedSpaceMap B S hS g) (hf := hg)] at h2
  have h3 := congrArg (fun m ↦ (sheafCompose (SmallEtale.topology B S hS (yoneda.obj T))
    (forget RingCat.{u})).map m)
    (structureSharp_comp_chartRanIso B S hS (representedSpaceMap B S hS g) hg)
  simp only [CategoryTheory.Functor.map_comp, ringSheafMap_pullbackRingSheafMapOfNatTrans,
    restrictionRingIso_hom_ringSheafMap] at h3
  exact (congrArg₂ (· ≫ ·) h1 h2).trans h3

/-- The components of `AlgebraicGeometry.Space.zariskiRestrictionPushforwardIso`. -/
theorem zariskiRestrictionPushforwardIso_hom_app
    (M : SheafOfModules.{u} (representedStructureRingSheaf B S hS T')) :
    (zariskiRestrictionPushforwardIso B S hS g hg).hom.app M =
      (zariskiRestriction B S hS T).map
          ((modulePushforwardChartIso B S hS (representedSpaceMap B S hS g) hg).hom.app M) ≫
        (SheafOfModules.pushforwardComp.{u} (zariskiRestrictionSharp B S hS T)
          (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg)).hom.app M ≫
        (SheafOfModules.pushforwardCongr₂.{u}
          (SheafOfModules.comparisonComp (idChartSchemeHom B S hS g).toRingCatSheafHom
            (zariskiRestrictionSharp B S hS T'))
          (openChartFunctorBaseChangeIso B S hS g hg)
          (structureMap_comp_openChartBaseChangeIso B S hS g hg)).inv.app M ≫
        (SheafOfModules.pushforwardComp.{u} (idChartSchemeHom B S hS g).toRingCatSheafHom
          (zariskiRestrictionSharp B S hS T')).inv.app M :=
  rfl

/-- The unit map of the composite of the structure maps of restriction and base change is carried
by the identification of the two composites of chart functors to the unit map of the other
composite. -/
theorem unitToPushforwardObjUnit_comp_openChartBaseChangeIso_inv :
    SheafOfModules.unitToPushforwardObjUnit
        (SheafOfModules.comparisonComp (zariskiRestrictionSharp B S hS T)
          (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg)) ≫
        (SheafOfModules.pushforwardCongr₂.{u}
          (SheafOfModules.comparisonComp (idChartSchemeHom B S hS g).toRingCatSheafHom
            (zariskiRestrictionSharp B S hS T'))
          (openChartFunctorBaseChangeIso B S hS g hg)
          (structureMap_comp_openChartBaseChangeIso B S hS g hg)).inv.app
          (SheafOfModules.unit (representedStructureRingSheaf B S hS T')) =
      SheafOfModules.unitToPushforwardObjUnit
        (SheafOfModules.comparisonComp (idChartSchemeHom B S hS g).toRingCatSheafHom
          (zariskiRestrictionSharp B S hS T')) :=
  SheafOfModules.unitToPushforwardObjUnit_pushforwardCongr₂_inv
    (SheafOfModules.comparisonComp (idChartSchemeHom B S hS g).toRingCatSheafHom
      (zariskiRestrictionSharp B S hS T'))
    (openChartFunctorBaseChangeIso B S hS g hg)
    (structureMap_comp_openChartBaseChangeIso B S hS g hg)

/-- The unit map of the composite of `g₀` with restriction to the Zariski opens is the unit map of
`g₀` followed by the direct image of the unit map of restriction. -/
theorem unitToPushforwardObjUnit_comparisonComp_comp_inv :
    SheafOfModules.unitToPushforwardObjUnit
        (SheafOfModules.comparisonComp (idChartSchemeHom B S hS g).toRingCatSheafHom
          (zariskiRestrictionSharp B S hS T')) ≫
        (SheafOfModules.pushforwardComp.{u} (idChartSchemeHom B S hS g).toRingCatSheafHom
          (zariskiRestrictionSharp B S hS T')).inv.app
          (SheafOfModules.unit (representedStructureRingSheaf B S hS T')) =
      SheafOfModules.unitToPushforwardObjUnit (idChartSchemeHom B S hS g).toRingCatSheafHom ≫
        (SheafOfModules.pushforward.{u} (idChartSchemeHom B S hS g).toRingCatSheafHom).map
          (SheafOfModules.unitToPushforwardObjUnit (zariskiRestrictionSharp B S hS T')) :=
  rfl

/-- A morphism `𝒪 ⟶ g_*𝒪` which is the unit map of base change of charts after the chart
identification is carried by the identification `R_T g_* ≅ g₀_* R_{T'}` to the unit map of `g₀`. -/
theorem unitToPushforwardObjUnit_comp_zariskiRestrictionPushforwardIso_of_comp_chartIso
    (τ : SheafOfModules.unit (representedStructureRingSheaf B S hS T) ⟶
      (modulePushforward B S hS (representedSpaceMap B S hS g)).obj
        (SheafOfModules.unit (representedStructureRingSheaf B S hS T')))
    (hτ : τ ≫ (modulePushforwardChartIso B S hS (representedSpaceMap B S hS g) hg).hom.app
        (SheafOfModules.unit (representedStructureRingSheaf B S hS T')) =
      SheafOfModules.unitToPushforwardObjUnit
        (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg)) :
    SheafOfModules.unitToPushforwardObjUnit (zariskiRestrictionSharp B S hS T) ≫
        (zariskiRestriction B S hS T).map τ ≫
        (zariskiRestrictionPushforwardIso B S hS g hg).hom.app
          (SheafOfModules.unit (representedStructureRingSheaf B S hS T')) =
      SheafOfModules.unitToPushforwardObjUnit (idChartSchemeHom B S hS g).toRingCatSheafHom ≫
        (SheafOfModules.pushforward.{u} (idChartSchemeHom B S hS g).toRingCatSheafHom).map
          (SheafOfModules.unitToPushforwardObjUnit (zariskiRestrictionSharp B S hS T')) := by
  rw [zariskiRestrictionPushforwardIso_hom_app]
  have k1 := (Functor.map_comp_assoc (zariskiRestriction B S hS T) τ
    ((modulePushforwardChartIso B S hS (representedSpaceMap B S hS g) hg).hom.app
      (SheafOfModules.unit (representedStructureRingSheaf B S hS T')))
    ((SheafOfModules.pushforwardComp.{u} (zariskiRestrictionSharp B S hS T)
      (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg)).hom.app
      (SheafOfModules.unit (representedStructureRingSheaf B S hS T')) ≫
    (SheafOfModules.pushforwardCongr₂.{u}
      (SheafOfModules.comparisonComp (idChartSchemeHom B S hS g).toRingCatSheafHom
        (zariskiRestrictionSharp B S hS T'))
      (openChartFunctorBaseChangeIso B S hS g hg)
      (structureMap_comp_openChartBaseChangeIso B S hS g hg)).inv.app
      (SheafOfModules.unit (representedStructureRingSheaf B S hS T')) ≫
    (SheafOfModules.pushforwardComp.{u} (idChartSchemeHom B S hS g).toRingCatSheafHom
      (zariskiRestrictionSharp B S hS T')).inv.app
      (SheafOfModules.unit (representedStructureRingSheaf B S hS T')))).symm.trans
    (congrArg (fun t => (zariskiRestriction B S hS T).map t ≫ _) hτ)
  refine (congrArg (_ ≫ ·) k1).trans ?_
  have k2 : ∀ {Q} (X : _ ⟶ Q),
      SheafOfModules.unitToPushforwardObjUnit (zariskiRestrictionSharp B S hS T) ≫
        (zariskiRestriction B S hS T).map (SheafOfModules.unitToPushforwardObjUnit
          (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg)) ≫
        (SheafOfModules.pushforwardComp.{u} (zariskiRestrictionSharp B S hS T)
          (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg)).hom.app
          (SheafOfModules.unit (representedStructureRingSheaf B S hS T')) ≫ X =
      SheafOfModules.unitToPushforwardObjUnit
        (SheafOfModules.comparisonComp (zariskiRestrictionSharp B S hS T)
          (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg)) ≫ X := fun X =>
    ((Category.assoc _ _ _).symm.trans ((Category.assoc _ _ _).symm)).trans (congrArg (· ≫ X)
      ((Category.assoc _ _ _).trans (SheafOfModules.unitToPushforwardObjUnit_comparisonComp _ _)))
  refine (k2 _).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _)
      (unitToPushforwardObjUnit_comp_openChartBaseChangeIso_inv B S hS g hg)).trans ?_
  exact unitToPushforwardObjUnit_comparisonComp_comp_inv B S hS g

/-- `AlgebraicGeometry.Space.structureModulePullbackMap_transpose_comp_chartIso`, with the
structure sheaf of `yoneda.obj T'` written as
`AlgebraicGeometry.Space.representedStructureRingSheaf`. -/
theorem structureModulePullbackMap_transpose_comp_chartIso' :
    (modulePullbackAdjunction B S hS (representedSpaceMap B S hS g)).homEquiv _ _
        (structureModulePullbackMap B S hS (representedSpaceMap B S hS g)) ≫
      (modulePushforwardChartIso B S hS (representedSpaceMap B S hS g) hg).hom.app
        (SheafOfModules.unit (representedStructureRingSheaf B S hS T')) =
      SheafOfModules.unitToPushforwardObjUnit
        (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg) :=
  structureModulePullbackMap_transpose_comp_chartIso B S hS g hg

/-- The transpose of the structure map `g^*𝒪 ⟶ 𝒪`, restricted to the Zariski opens and read
through `AlgebraicGeometry.Space.zariskiRestrictionPushforwardIso`, is the transpose of the
structure map of `g₀`. -/
theorem unitToChartPushforward_comp_zariskiRestrictionPushforwardIso :
    SheafOfModules.unitToPushforwardObjUnit (zariskiRestrictionSharp B S hS T) ≫
        (zariskiRestriction B S hS T).map
          ((modulePullbackAdjunction B S hS (representedSpaceMap B S hS g)).homEquiv _ _
            (structureModulePullbackMap B S hS (representedSpaceMap B S hS g))) ≫
        (zariskiRestrictionPushforwardIso B S hS g hg).hom.app
          (SheafOfModules.unit (representedStructureRingSheaf B S hS T')) =
      SheafOfModules.unitToPushforwardObjUnit (idChartSchemeHom B S hS g).toRingCatSheafHom ≫
        (SheafOfModules.pushforward.{u} (idChartSchemeHom B S hS g).toRingCatSheafHom).map
          (SheafOfModules.unitToPushforwardObjUnit (zariskiRestrictionSharp B S hS T')) :=
  unitToPushforwardObjUnit_comp_zariskiRestrictionPushforwardIso_of_comp_chartIso B S hS g hg _
    (structureModulePullbackMap_transpose_comp_chartIso' B S hS g hg)

/-- The conjugate of the inverse of `AlgebraicGeometry.Space.zariskiModelPullbackIso` is the
identification of the direct images. -/
theorem conjugateEquiv_zariskiModelPullbackIso_inv :
    conjugateEquiv
        ((zariskiModelAdjunction B S hS T).comp
          (modulePullbackAdjunction B S hS (representedSpaceMap B S hS g)))
        ((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
          (idChartSchemeHom B S hS g).toLRSHom.toShHom).comp
            (zariskiModelAdjunction B S hS T'))
        (zariskiModelPullbackIso B S hS g hg).inv =
      (zariskiRestrictionPushforwardIso B S hS g hg).hom := by
  rw [zariskiModelPullbackIso]
  exact Equiv.apply_symm_apply _ _

/-- **The identification of inverse images is compatible with the structure maps**: read on
`𝒪_{T₀}`, the identification `Φ_{T'} g₀^* ≅ g^* Φ_T` carries the structure map of `g₀` to the
structure map of `g`, through the structure maps of the two Zariski models. -/
theorem zariskiModelPullbackIso_inv_app_unit_comp :
    (zariskiModelPullbackIso B S hS g hg).inv.app
        (SheafOfModules.unit (structureSheafRing
          (chartScheme (idEtaleChart B S hS T)).toLocallyRingedSpace.toSheafedSpace)) ≫
      ((modulePullback B S hS (representedSpaceMap B S hS g)).map (zariskiUnitMap B S hS T) ≫
        structureModulePullbackMap B S hS (representedSpaceMap B S hS g) :
          _ ⟶ SheafOfModules.unit (representedStructureRingSheaf B S hS T')) =
    (zariskiModel B S hS T').map
        (RingedSpaceModuleAdjunction.modulePullbackUnitToUnit
            (idChartSchemeHom B S hS g).toLRSHom.toShHom) ≫
      zariskiUnitMap B S hS T' := by
  let adj₁ := (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
          (idChartSchemeHom B S hS g).toLRSHom.toShHom).comp (zariskiModelAdjunction B S hS T')
  let adj₂ := (zariskiModelAdjunction B S hS T).comp
    (modulePullbackAdjunction B S hS (representedSpaceMap B S hS g))
  apply (adj₁.homEquiv _ _).injective
  refine (Adjunction.homEquiv_app_comp_conjugateEquiv adj₂ adj₁
    (zariskiModelPullbackIso B S hS g hg).inv _).trans ?_
  refine (congrArg (_ ≫ ·) (congrArg (fun t => NatTrans.app t _)
    (conjugateEquiv_zariskiModelPullbackIso_inv B S hS g hg))).trans ?_
  have h₂ : adj₂.homEquiv _ (SheafOfModules.unit (representedStructureRingSheaf B S hS T'))
      ((modulePullback B S hS (representedSpaceMap B S hS g)).map (zariskiUnitMap B S hS T) ≫
        structureModulePullbackMap B S hS (representedSpaceMap B S hS g)) =
      SheafOfModules.unitToPushforwardObjUnit (zariskiRestrictionSharp B S hS T) ≫
        (zariskiRestriction B S hS T).map
          ((modulePullbackAdjunction B S hS (representedSpaceMap B S hS g)).homEquiv _ _
            (structureModulePullbackMap B S hS (representedSpaceMap B S hS g))) := by
    exact (Adjunction.comp_homEquiv_map_comp _ _ _ _).trans
      (congrArg (· ≫ _) (homEquiv_zariskiUnitMap B S hS T))
  have h₁ : adj₁.homEquiv _ (SheafOfModules.unit (representedStructureRingSheaf B S hS T'))
      ((zariskiModel B S hS T').map
        (RingedSpaceModuleAdjunction.modulePullbackUnitToUnit
            (idChartSchemeHom B S hS g).toLRSHom.toShHom) ≫
      zariskiUnitMap B S hS T') =
      SheafOfModules.unitToPushforwardObjUnit (idChartSchemeHom B S hS g).toRingCatSheafHom ≫
        (SheafOfModules.pushforward.{u} (idChartSchemeHom B S hS g).toRingCatSheafHom).map
          (SheafOfModules.unitToPushforwardObjUnit (zariskiRestrictionSharp B S hS T')) := by
    refine (Adjunction.comp_homEquiv_map_comp _ _ _ _).trans ?_
    exact congrArg₂ (· ≫ ·) (RingedSpaceModuleAdjunction.homEquiv_modulePullbackUnitToUnit _)
      (congrArg _ (homEquiv_zariskiUnitMap B S hS T'))
  refine (congrArg (· ≫ _) h₂).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (unitToChartPushforward_comp_zariskiRestrictionPushforwardIso B S hS g hg).trans ?_
  exact h₁.symm

end Pushforward

section Key

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

variable {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
  (hg : yoneda.relativelyRepresentable (yoneda.map g))
  (Z : ClosedSubspaces B S hS (yoneda.obj T')) (Z' : ClosedSubspaces B S hS (yoneda.obj T))
  (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))
  (hsq : subspaceInclusion B S hS
      ⟨yoneda.obj T', AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T'⟩ Z ≫
        representedSpaceMap B S hS g =
      f ≫ subspaceInclusion B S hS
        ⟨yoneda.obj T, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T⟩ Z')
  (f₀ : (BigFppfOver.toScheme B S hS).obj (Z.2.2.rep.pullback (idEtaleChart B S hS T').1.hom) ⟶
    (BigFppfOver.toScheme B S hS).obj (Z'.2.2.rep.pullback (idEtaleChart B S hS T).1.hom))
  (comm : zariskiClosedImmersion B S hS T' Z ≫ idChartSchemeHom B S hS g =
    f₀ ≫ zariskiClosedImmersion B S hS T Z')


include comm in
/-- The square of ringed spaces underlying `comm`. -/
theorem zariskiClosedImmersion_toShHom_square :
    (zariskiClosedImmersion B S hS T' Z).toLRSHom.toShHom ≫
        (idChartSchemeHom B S hS g).toLRSHom.toShHom =
      f₀.toLRSHom.toShHom ≫ (zariskiClosedImmersion B S hS T Z').toLRSHom.toShHom :=
  congrArg (fun p => p.toLRSHom.toShHom) comm

/-- `AlgebraicGeometry.Space.zariskiModelPullbackIso_inv_app_unit_comp`, read with the
structure sheaf of `yoneda.obj T'` as the target of the structure maps. -/
theorem zariskiModelPullbackIso_inv_app_unit_comp' :
    (zariskiModelPullbackIso B S hS g hg).inv.app
        (SheafOfModules.unit (structureSheafRing
          (chartScheme (idEtaleChart B S hS T)).toLocallyRingedSpace.toSheafedSpace)) ≫
      (modulePullback B S hS (representedSpaceMap B S hS g)).map (zariskiUnitMap B S hS T) ≫
        structureModulePullbackMap B S hS (representedSpaceMap B S hS g) =
    (zariskiModel B S hS T').map
        (RingedSpaceModuleAdjunction.modulePullbackUnitToUnit
          (idChartSchemeHom B S hS g).toLRSHom.toShHom) ≫
      (zariskiUnitMap B S hS T' : _ ⟶ (structureModulesToModules B S hS
        ⟨yoneda.obj T', AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T'⟩).obj
          (SheafOfModules.unit (structureRingSheaf B S hS
            ⟨yoneda.obj T', AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T'⟩))) :=
  zariskiModelPullbackIso_inv_app_unit_comp B S hS g hg

/-- The map of defining ideal sheaves `g^*𝓘_{Z'} ⟶ 𝓘_Z` of a square of closed subspaces of
representable algebraic spaces, `AlgebraicGeometry.Space.idealSheafMap`, read between the
defining ideal sheaves as `𝒪`-modules. -/
noncomputable def representedIdealSheafMap :
    (modulePullback B S hS (representedSpaceMap B S hS g)).obj
        (representedDefiningIdealModule B S hS T Z') ⟶
      representedDefiningIdealModule B S hS T' Z :=
  definingIdealModuleMap B S hS
    (X := ⟨yoneda.obj T', AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T'⟩)
    (X' := ⟨yoneda.obj T, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T⟩)
    Z Z' (representedSpaceMap B S hS g) f hsq

/-- `AlgebraicGeometry.Space.representedIdealSheafMap` followed by the inclusion of the defining
ideal sheaf is the inverse image of the inclusion followed by the structure map. -/
theorem representedIdealSheafMap_comp_ι :
    representedIdealSheafMap B S hS g Z Z' f hsq ≫ representedDefiningIdealι B S hS T' Z =
      (modulePullback B S hS (representedSpaceMap B S hS g)).map
          (representedDefiningIdealι B S hS T Z') ≫
        structureModulePullbackMap B S hS (representedSpaceMap B S hS g) :=
  definingIdealModuleMap_comp_ι B S hS
    (X := ⟨yoneda.obj T', AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T'⟩)
    (X' := ⟨yoneda.obj T, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T⟩)
    Z Z' (representedSpaceMap B S hS g) f hsq

/-- **The map of defining ideal sheaves of a square of closed subspaces of representable
algebraic spaces is the Zariski model of the map of ideal sheaves of the corresponding square of
closed immersions of schemes**, read through `AlgebraicGeometry.Space.zariskiModelPullbackIso`
and the identifications `AlgebraicGeometry.Space.definingIdealSheafZariskiModelIso`. -/
theorem idealSheafMap_eq_zariskiModel :
    (zariskiModelPullbackIso B S hS g hg).inv.app
        (Stacks.ClosedImmersion.idealSheaf
          (zariskiClosedImmersion B S hS T Z').toLRSHom.toShHom) ≫
      (modulePullback B S hS (representedSpaceMap B S hS g)).map
        (definingIdealSheafZariskiModelIso B S hS T Z').inv ≫
      representedIdealSheafMap B S hS g Z Z' f hsq =
    (zariskiModel B S hS T').map
        (Stacks.ClosedImmersion.idealSheafMap
          (zariskiClosedImmersion_toShHom_square B S hS g Z Z' f₀ comm)) ≫
      (definingIdealSheafZariskiModelIso B S hS T' Z).inv := by
  have hφ := representedIdealSheafMap_comp_ι B S hS g Z Z' f hsq
  have hφ₀ := Stacks.ClosedImmersion.idealSheafMap_comp_ι
    (zariskiClosedImmersion_toShHom_square B S hS g Z Z' f₀ comm)
  have ha_B := definingIdealSheafZariskiModelIso_inv_comp_ι B S hS T Z'
  have ha_A := definingIdealSheafZariskiModelIso_inv_comp_ι B S hS T' Z
  have hu := zariskiModelPullbackIso_inv_app_unit_comp' B S hS g hg
  have := mono_map_definingIdealSheaf_ι B S hS
    (X := ⟨yoneda.obj T', AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T'⟩) Z
  have key := comp_eq_of_square_of_mono (zariskiModelPullbackIso B S hS g hg)
    (ι₀_B := Stacks.ClosedImmersion.idealSheafι
      (zariskiClosedImmersion B S hS T Z').toLRSHom.toShHom)
    (ι₀_A := Stacks.ClosedImmersion.idealSheafι
      (zariskiClosedImmersion B S hS T' Z).toLRSHom.toShHom)
    (φ₀ := Stacks.ClosedImmersion.idealSheafMap
          (zariskiClosedImmersion_toShHom_square B S hS g Z Z' f₀ comm))
    (σ₀ := RingedSpaceModuleAdjunction.modulePullbackUnitToUnit
        (idChartSchemeHom B S hS g).toLRSHom.toShHom)
    hφ₀
    (ι_B := representedDefiningIdealι B S hS T Z')
    (ι_A := representedDefiningIdealι B S hS T' Z)
    (φ := representedIdealSheafMap B S hS g Z Z' f hsq)
    (σ := structureModulePullbackMap B S hS (representedSpaceMap B S hS g))
    hφ (definingIdealSheafZariskiModelIso B S hS T Z')
    (definingIdealSheafZariskiModelIso B S hS T' Z)
    (zariskiUnitMap B S hS T) (zariskiUnitMap B S hS T') ha_B ha_A hu
  exact key

end Key


end AlgebraicGeometry.Space

end
