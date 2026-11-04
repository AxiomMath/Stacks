module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.TowerHoms
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorDegreeZero
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorHomologyEdge
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.AffineMorphism
public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.DirectImageInDerivedCategory
public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionTwistedInverseImage
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.DerivedStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.Exactness
public import StacksFrontier.AlgebraicGeometry.Duality.KoszulRegularRightAdjoint.SheafHom
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.ProperRestriction
public import StacksFrontier.AlgebraicGeometry.Modules.AffineOpenHomOfUnit

/-!
# The trace of the twisted inverse image of an affine morphism

Let `g : Y ⟶ X` be an affine morphism of quasi-compact quasi-separated schemes and `a` the right
adjoint of `Rg_* : D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)`. For `E ∈ D_QCoh(𝒪_X)` with `E` and `a(E)` in
`D^{≥0}`, the counit `Rg_* a(E) ⟶ E` induces in degree `0` a map
`t_E : g_* H⁰(a(E)) ⟶ H⁰(E)`, and `φ ↦ t_E ∘ g_*φ` is a bijection
`Hom(M, H⁰(a(E))) ≃ Hom(g_*M, H⁰(E))` for every quasi-coherent `𝒪_Y`-module `M`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits DerivedCategory

universe u

namespace Stacks.Duality.FiniteTrace

section Zero

variable {X Y : Scheme.{u}} (g : Y ⟶ X)

/-- `R⁰g_* = g_*`, naturally on `𝒪_Y`-modules. -/
def singleDerivedPushforwardHomologyIso :
    singleFunctor Y.Modules 0 ⋙ derivedPushforward g ⋙ homologyFunctor X.Modules 0 ≅
      Scheme.Modules.pushforward g :=
  Stacks.DerivedFunctor.derivedZeroNatIso (Scheme.Modules.pushforward g) (derivedPushforward g)
    (derivedPushforwardUnit g)
    (fun _ => isGE_derivedPushforward_obj' g _ 0)
    (fun J hJ => Stacks.DerivedFunctor.isIso_unit_app_single_of_injective
      (Scheme.Modules.pushforward g) (derivedPushforward g) (derivedPushforwardUnit g)
      (exists_quasiIso_isKInjective_ringCatSheaf Y) J hJ)

/-- For `g` affine and `M` quasi-coherent, `Rg_*(M[0])` is concentrated in degree `0`. -/
theorem isLE_derivedPushforward_single [IsAffineHom g] (M : Y.Modules) [M.IsQuasicoherent] :
    ((derivedPushforward g).obj ((singleFunctor Y.Modules 0).obj M)).IsLE 0 := by
  rw [isLE_iff]
  intro i hi
  exact Stacks.AlgebraicGeometry.DerivedAffinePushforward.isZero_homology_derivedPushforwardSingle
    g M (by omega)

end Zero

section Trace

variable {X Y : Scheme.{u}} (g : Y ⟶ X) [QuasiCompact g] [QuasiSeparated g]
  [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]

/-- The twisted inverse image `a` of `g`: the right adjoint of `Rg_*` on `D_QCoh`. -/
abbrev twisted : quasiCoherentDerivedCategory X ⥤ quasiCoherentDerivedCategory Y :=
  twistedInverseImage g (isQuasicoherent_homology_derivedPushforward_of_qcqs g)

/-- The adjunction `Rg_* ⊣ a`. -/
abbrev twistedAdj :=
  twistedInverseImageAdjunction g (isQuasicoherent_homology_derivedPushforward_of_qcqs g)

/-- `H⁰(a(E))`. -/
abbrev zeroTwisted (E : quasiCoherentDerivedCategory X) : Y.Modules :=
  (homologyFunctor Y.Modules 0).obj ((twisted g).obj E).obj

variable {g} (E : quasiCoherentDerivedCategory X) [((twisted g).obj E).obj.IsGE 0]

/-- The morphism `M[0] ⟶ a(E)` whose `H⁰` is a given `M ⟶ H⁰(a(E))`. -/
def liftSingle {M : Y.Modules} (φ : M ⟶ zeroTwisted g E) :
    (singleFunctor Y.Modules 0).obj M ⟶ ((twisted g).obj E).obj :=
  (Equiv.ofBijective _ (bijective_homologyFunctor_map_of_isLE_of_isGE
    ((singleFunctor Y.Modules 0).obj M) ((twisted g).obj E).obj 0)).symm
      ((singleFunctorCompHomologyFunctorIso Y.Modules 0).hom.app M ≫ φ)

/-- `H⁰` of `liftSingle E φ` is `φ`, up to the identification `H⁰(M[0]) ≅ M`. -/
theorem homology_map_liftSingle {M : Y.Modules} (φ : M ⟶ zeroTwisted g E) :
    (homologyFunctor Y.Modules 0).map (liftSingle E φ) =
      (singleFunctorCompHomologyFunctorIso Y.Modules 0).hom.app M ≫ φ :=
  (Equiv.ofBijective _ (bijective_homologyFunctor_map_of_isLE_of_isGE
    ((singleFunctor Y.Modules 0).obj M) ((twisted g).obj E).obj 0)).apply_symm_apply _

/-- `liftSingle` is natural in `M`: `liftSingle E (ψ ≫ φ) = ψ[0] ≫ liftSingle E φ`. -/
theorem liftSingle_comp {M M' : Y.Modules} (ψ : M' ⟶ M) (φ : M ⟶ zeroTwisted g E) :
    liftSingle E (ψ ≫ φ) = (singleFunctor Y.Modules 0).map ψ ≫ liftSingle E φ := by
  apply (bijective_homologyFunctor_map_of_isLE_of_isGE
    ((singleFunctor Y.Modules 0).obj M') ((twisted g).obj E).obj 0).1
  dsimp only
  rw [homology_map_liftSingle, Functor.map_comp, homology_map_liftSingle]
  have h := (singleFunctorCompHomologyFunctorIso Y.Modules 0).hom.naturality ψ
  simp only [Functor.comp_map, Functor.id_map] at h
  rw [reassoc_of% h]

/-- **The duality map** `Hom(M, H⁰(a(E))) ⟶ Hom(g_*M, H⁰(E))`: lift to `M[0] ⟶ a(E)`, apply
`Rg_*`, compose with the counit and take `H⁰`, using `R⁰g_* = g_*`. -/
def dualityMap {M : Y.Modules} (φ : M ⟶ zeroTwisted g E) :
    (Scheme.Modules.pushforward g).obj M ⟶ (homologyFunctor X.Modules 0).obj E.obj :=
  ((singleDerivedPushforwardHomologyIso g).app M).inv ≫
    (homologyFunctor X.Modules 0).map ((derivedPushforward g).map (liftSingle E φ) ≫
      ((twistedAdj g).counit.app E).hom)

/-- The duality map is natural in `M`: `dualityMap E (ψ ≫ φ) = g_*ψ ≫ dualityMap E φ`. -/
theorem dualityMap_comp {M M' : Y.Modules} (ψ : M' ⟶ M) (φ : M ⟶ zeroTwisted g E) :
    dualityMap E (ψ ≫ φ) = (Scheme.Modules.pushforward g).map ψ ≫ dualityMap E φ := by
  simp only [dualityMap, liftSingle_comp, Functor.map_comp, Category.assoc, Iso.app_inv]
  have h := (singleDerivedPushforwardHomologyIso g).inv.naturality ψ
  simp only [Functor.comp_map] at h
  rw [reassoc_of% h]

/-- The trace `t_E : g_*H⁰(a(E)) ⟶ H⁰(E)`. -/
def trace : (Scheme.Modules.pushforward g).obj (zeroTwisted g E) ⟶
    (homologyFunctor X.Modules 0).obj E.obj :=
  dualityMap E (𝟙 _)

/-- The duality map sends `φ : M ⟶ H⁰(a(E))` to `t_E ∘ g_*φ`. -/
theorem dualityMap_eq {M : Y.Modules} (φ : M ⟶ zeroTwisted g E) :
    dualityMap E φ = (Scheme.Modules.pushforward g).map φ ≫ trace E := by
  rw [trace, ← dualityMap_comp, Category.comp_id]

/-- The trace is natural in `E`: for `η : E ⟶ E'`, `t_{E'} ∘ g_*H⁰(a(η)) = H⁰(η) ∘ t_E`. -/
theorem trace_naturality (E' : quasiCoherentDerivedCategory X)
    [((twisted g).obj E').obj.IsGE 0] (η : E ⟶ E') :
    (Scheme.Modules.pushforward g).map ((homologyFunctor Y.Modules 0).map
        ((twisted g).map η).hom) ≫ trace E' =
      trace E ≫ (homologyFunctor X.Modules 0).map η.hom := by
  rw [← dualityMap_eq, trace, dualityMap, dualityMap]
  have hl : liftSingle E' ((homologyFunctor Y.Modules 0).map ((twisted g).map η).hom) =
      liftSingle E (𝟙 _) ≫ ((twisted g).map η).hom := by
    apply (bijective_homologyFunctor_map_of_isLE_of_isGE _ ((twisted g).obj E').obj 0).1
    dsimp only
    rw [homology_map_liftSingle, Functor.map_comp, homology_map_liftSingle]
    simp
  have hc := congrArg (fun φ => φ.hom) ((twistedAdj g).counit.naturality η)
  have key : (derivedPushforward g).map (liftSingle E (𝟙 _) ≫ ((twisted g).map η).hom) ≫
      ((twistedAdj g).counit.app E').hom =
      ((derivedPushforward g).map (liftSingle E (𝟙 _)) ≫ ((twistedAdj g).counit.app E).hom) ≫
        η.hom := by
    rw [Functor.map_comp, Category.assoc, Category.assoc]
    congr 1
  rw [hl, key, Functor.map_comp, Category.assoc]

omit [QuasiCompact g] [QuasiSeparated g] [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace Y] [QuasiSeparatedSpace Y] in
private theorem bijective_iso_comp {C : Type*} [Category C] {A B Z : C} (e : A ≅ B) :
    Function.Bijective (fun φ : B ⟶ Z => e.hom ≫ φ) :=
  ⟨fun _ _ h => (cancel_epi e.hom).1 h, fun φ => ⟨e.inv ≫ φ, by simp⟩⟩

/-- **Duality for an affine morphism in degree `0`.** For `E` and `a(E)` in `D^{≥0}` and `M`
quasi-coherent, `φ ↦ t_E ∘ g_*φ` is a bijection `Hom(M, H⁰(a(E))) ≃ Hom(g_*M, H⁰(E))`. -/
theorem bijective_dualityMap [IsAffineHom g] [E.obj.IsGE 0] (M : Y.Modules) [M.IsQuasicoherent] :
    Function.Bijective (dualityMap (g := g) E (M := M)) := by
  let Mq : quasiCoherentDerivedCategory Y :=
    ⟨(singleFunctor Y.Modules 0).obj M,
      DerivedPushforward.derivedCategoryB_singleFunctor_obj M inferInstance⟩
  have hlift : Function.Bijective (liftSingle (g := g) E (M := M)) := by
    refine (Equiv.ofBijective _ (bijective_homologyFunctor_map_of_isLE_of_isGE
      ((singleFunctor Y.Modules 0).obj M) ((twisted g).obj E).obj 0)).symm.bijective.comp ?_
    exact bijective_iso_comp ((singleFunctorCompHomologyFunctorIso Y.Modules 0).app M)
  have hadj : Function.Bijective (fun ψ : (singleFunctor Y.Modules 0).obj M ⟶
      ((twisted g).obj E).obj =>
        (derivedPushforward g).map ψ ≫ ((twistedAdj g).counit.app E).hom) := by
    have e : (fun ψ : (singleFunctor Y.Modules 0).obj M ⟶ ((twisted g).obj E).obj =>
        (derivedPushforward g).map ψ ≫ ((twistedAdj g).counit.app E).hom) =
        (fun χ => χ.hom) ∘ ((twistedAdj g).homEquiv Mq E).symm ∘
          (fun ψ => ObjectProperty.homMk ψ) := by
      funext ψ
      simp [Adjunction.homEquiv_counit]
      rfl
    rw [e]
    refine Function.Bijective.comp ?_ (((twistedAdj g).homEquiv Mq E).symm.bijective.comp ?_)
    · exact ⟨fun _ _ h => ObjectProperty.hom_ext _ h,
        fun χ => ⟨ObjectProperty.homMk χ, rfl⟩⟩
    · exact ⟨fun _ _ h => congrArg (fun χ => χ.hom) h,
        fun χ => ⟨χ.hom, ObjectProperty.hom_ext _ rfl⟩⟩
  have hH : Function.Bijective (fun χ : (derivedPushforward g).obj
      ((singleFunctor Y.Modules 0).obj M) ⟶ E.obj => (homologyFunctor X.Modules 0).map χ) := by
    have := isLE_derivedPushforward_single g M
    exact bijective_homologyFunctor_map_of_isLE_of_isGE _ _ 0
  have hpre : Function.Bijective (fun χ : (homologyFunctor X.Modules 0).obj
      ((derivedPushforward g).obj ((singleFunctor Y.Modules 0).obj M)) ⟶
        (homologyFunctor X.Modules 0).obj E.obj =>
      ((singleDerivedPushforwardHomologyIso g).app M).inv ≫ χ) :=
    bijective_iso_comp ((singleDerivedPushforwardHomologyIso g).app M).symm
  exact hpre.comp (hH.comp (hadj.comp hlift))

end Trace

section Restriction

open OpenImmersion

variable {X Y : Scheme.{u}} (g : Y ⟶ X) [IsProper g] [IsNoetherian X] [IsNoetherian Y]
  (U : X.Opens)

/-- An open subscheme of a Noetherian scheme is quasi-compact. -/
instance (U : X.Opens) : CompactSpace U :=
  haveI := isNoetherian_of_isOpenImmersion U.ι
  inferInstance

/-- The inclusion of an open subscheme of a Noetherian scheme is quasi-compact. -/
instance (U : X.Opens) : QuasiCompact U.ι := quasiCompact_of_compactSpace _

/-- An open subscheme of a Noetherian scheme is quasi-compact. -/
instance (V : Y.Opens) : CompactSpace V :=
  haveI := isNoetherian_of_isOpenImmersion V.ι
  inferInstance

/-- The inclusion of an open subscheme of a Noetherian scheme is quasi-compact. -/
instance (V : Y.Opens) : QuasiCompact V.ι := quasiCompact_of_compactSpace _

/-- The restriction `j^*` along `U ⟶ X` on `D_QCoh`. -/
abbrev restrictU : quasiCoherentDerivedCategory X ⥤ quasiCoherentDerivedCategory U :=
  quasiCoherentDerivedRestrict U.ι (isQuasicoherent_homology_derivedRestrict U.ι)

/-- `Rj_*` for `U ⟶ X` on `D_QCoh`. -/
abbrev pushU : quasiCoherentDerivedCategory U ⥤ quasiCoherentDerivedCategory X :=
  quasiCoherentDerivedPushforward U.ι (isQuasicoherent_homology_derivedPushforward_of_qcqs U.ι)

/-- The adjunction `j^* ⊣ Rj_*` for `U ⟶ X`. -/
abbrev adjU : restrictU U ⊣ pushU U :=
  quasiCoherentDerivedRestrictAdjunction U.ι (isQuasicoherent_homology_derivedRestrict U.ι)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs U.ι)

/-- The restriction `j'^*` along `g⁻¹U ⟶ Y`. -/
abbrev restrictV : quasiCoherentDerivedCategory Y ⥤ quasiCoherentDerivedCategory (g ⁻¹ᵁ U) :=
  quasiCoherentDerivedRestrict (g ⁻¹ᵁ U).ι (isQuasicoherent_homology_derivedRestrict _)

/-- The unit `𝒪_X ⟶ Rj_* j^* 𝒪_X`. -/
abbrev structureUnit : DerivedPushforward.derivedStructureSheaf X ⟶
    (pushU U).obj ((restrictU U).obj (DerivedPushforward.derivedStructureSheaf X)) :=
  (adjU U).unit.app _

/-- **`(j')^*` of `a(𝒪_X ⟶ Rj_*j^*𝒪_X)` is invertible** for a proper `g` over a Noetherian
base: this is [Stacks, Tag 0A9P] at `𝒪_X`, read through Tag 0A9N. -/
theorem isIso_restrictV_map_twisted_map_structureUnit :
    IsIso ((restrictV g U).map ((twisted g).map (structureUnit U))) := by
  have sq := (isPullback_morphismRestrict g U).flip
  exact (isIso_twistedInverseImageRestrictionMap_app_iff (g ⁻¹ᵁ U).ι (g ∣_ U) g U.ι
    (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs _) sq _).1
    (isIso_twistedInverseImageRestrictionMap_app_of_isProper (g ⁻¹ᵁ U).ι (g ∣_ U) g U.ι sq _
      (KoszulRegular.isBoundedBelow_singleFunctor_obj _))

/-- **The comparison `H⁰(a(𝒪_X)) ⟶ H⁰(a(Rj_*j^*𝒪_X))` is invertible over `g⁻¹U`.** -/
theorem isIso_restrict_homology_twisted_map_structureUnit :
    IsIso ((Scheme.Modules.restrictFunctor (g ⁻¹ᵁ U).ι).map
      ((homologyFunctor Y.Modules 0).map ((twisted g).map (structureUnit U)).hom)) := by
  have h := isIso_restrictV_map_twisted_map_structureUnit g U
  have h₁ : IsIso ((derivedRestrict (g ⁻¹ᵁ U).ι).map ((twisted g).map (structureUnit U)).hom) :=
    inferInstanceAs (IsIso ((ObjectProperty.ι _).map
      ((restrictV g U).map ((twisted g).map (structureUnit U)))))
  have h₂ : IsIso ((homologyFunctor _ 0).map
      ((derivedRestrict (g ⁻¹ᵁ U).ι).map ((twisted g).map (structureUnit U)).hom)) :=
    inferInstance
  exact (NatIso.isIso_map_iff
    ((Scheme.Modules.restrictFunctor (g ⁻¹ᵁ U).ι).mapDerivedCategoryHomologyIso 0) _).1 h₂

omit [IsProper g] [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y] in
/-- The base change square of `U ⟶ X` along `g`. -/
theorem isPullback_restrict : IsPullback (g ⁻¹ᵁ U).ι (g ∣_ U) g U.ι :=
  (isPullback_morphismRestrict g U).flip

/-- The restriction `g⁻¹U ⟶ U` of a proper morphism is proper. -/
instance : IsProper (g ∣_ U) :=
  MorphismProperty.of_isPullback (isPullback_restrict g U) inferInstance

/-- The map `(j')^* a ⟶ a' j^*` of [Stacks, Tag 0A9L] for the square over `U`. -/
abbrev restrictionMap :=
  twistedInverseImageRestrictionMap (g ⁻¹ᵁ U).ι (g ∣_ U) g U.ι
    (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
    (isQuasicoherent_homology_derivedRestrict U.ι)
    (isQuasicoherent_homology_derivedRestrict _) (isPullback_restrict g U)

/-- The map `(j')^* a(𝒪_X) ⟶ a'(j^* 𝒪_X)` is an isomorphism. -/
instance : IsIso ((restrictionMap g U).app (DerivedPushforward.derivedStructureSheaf X)) :=
  isIso_twistedInverseImageRestrictionMap_app_of_isProper _ _ _ _ (isPullback_restrict g U) _
    (KoszulRegular.isBoundedBelow_singleFunctor_obj _)

/-- The comparison `ξ : Rj'_* a' ⟶ a Rj_*` of [Stacks, Tag 0A9K] for the square over `U`. -/
abbrev baseChangeMap :=
  twistedInverseImagePushforwardBaseChange (g ⁻¹ᵁ U).ι (g ∣_ U) g U.ι
    (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs _) (isPullback_restrict g U)

variable [((twisted g).obj (DerivedPushforward.derivedStructureSheaf X)).obj.IsGE 0]

omit [IsProper g] [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y] in
/-- An object isomorphic to one in `D^{≥n}` lies in `D^{≥n}`. -/
theorem isGE_of_iso' {Z : Scheme.{u}} {K L : DerivedCategory Z.Modules} (e : K ≅ L) (n : ℤ)
    (h : K.IsGE n) : L.IsGE n :=
  DerivedCategory.TStructure.t.isGE_of_iso e n

/-- The structure sheaf, placed in degree `0`, lies in `D^{≥0}`. -/
instance isGE_derivedStructureSheaf (Z : Scheme.{u}) :
    (DerivedPushforward.derivedStructureSheaf Z).obj.IsGE 0 := by
  rw [DerivedCategory.isGE_iff]
  intro i hi
  exact (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0
    (SheafOfModules.unit Z.ringCatSheaf) i (ne_of_lt hi)).of_iso
    ((homologyFunctor Z.Modules i).mapIso
        ((singleFunctorIsoCompQ Z.Modules 0).app (SheafOfModules.unit Z.ringCatSheaf)) ≪≫
      (homologyFunctorFactors Z.Modules i).app _)

/-- `a'(j^*𝒪_X)` lies in `D^{≥0}`. -/
instance isGE_twisted_restrict :
    ((twisted (g ∣_ U)).obj ((restrictU U).obj
      (DerivedPushforward.derivedStructureSheaf X))).obj.IsGE 0 := by
  have : TStructure.t.IsGE ((ObjectProperty.ι _).obj ((restrictV g U).obj
      ((twisted g).obj (DerivedPushforward.derivedStructureSheaf X)))) 0 :=
    @isGE_derivedRestrict_obj _ _ _ _ _ 0 ‹_›
  exact isGE_of_iso' ((ObjectProperty.ι _).mapIso
    (asIso ((restrictionMap g U).app (DerivedPushforward.derivedStructureSheaf X)))) 0 this

/-- `Rj_* j^*𝒪_X` lies in `D^{≥0}`. -/
instance isGE_unitTarget :
    ((pushU U).obj ((restrictU U).obj
      (DerivedPushforward.derivedStructureSheaf X))).obj.IsGE 0 := by
  have : TStructure.t.IsGE ((ObjectProperty.ι _).obj
      ((restrictU U).obj (DerivedPushforward.derivedStructureSheaf X))) 0 :=
    @isGE_derivedRestrict_obj _ _ _ _ _ 0 (isGE_derivedStructureSheaf X)
  exact @isGE_derivedPushforward_obj' _ _ _ _ 0 this

/-- `a(Rj_* j^*𝒪_X)` lies in `D^{≥0}`. -/
instance isGE_twisted_unitTarget :
    ((twisted g).obj ((pushU U).obj ((restrictU U).obj
      (DerivedPushforward.derivedStructureSheaf X)))).obj.IsGE 0 := by
  have : TStructure.t.IsGE ((ObjectProperty.ι _).obj
      ((twisted (g ∣_ U) ⋙ quasiCoherentDerivedPushforward (g ⁻¹ᵁ U).ι
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj ((restrictU U).obj
          (DerivedPushforward.derivedStructureSheaf X)))) 0 :=
    @isGE_derivedPushforward_obj' _ _ _ _ 0 (isGE_twisted_restrict g U)
  exact isGE_of_iso' ((ObjectProperty.ι _).mapIso
    (asIso ((baseChangeMap g U).app
      ((restrictU U).obj (DerivedPushforward.derivedStructureSheaf X))))) 0 this

omit [IsProper g] [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y] in
/-- A sheaf of modules isomorphic to a pushforward along an open immersion is recovered from its
restriction: the unit of `ι^* ⊣ ι_*` is invertible at it. -/
theorem isIso_restrictAdjunction_unit_of_iso {Z : Scheme.{u}} (V : Z.Opens) {F : Z.Modules}
    {Q : V.toScheme.Modules} (e : F ≅ (Scheme.Modules.pushforward V.ι).obj Q) :
    IsIso ((Scheme.Modules.restrictAdjunction V.ι).unit.app F) := by
  have h₁ : IsIso ((Scheme.Modules.restrictAdjunction V.ι).unit.app
      ((Scheme.Modules.pushforward V.ι).obj Q)) := by
    have h := (Scheme.Modules.restrictAdjunction V.ι).right_triangle_components Q
    have hu : (Scheme.Modules.restrictAdjunction V.ι).unit.app
        ((Scheme.Modules.pushforward V.ι).obj Q) = inv ((Scheme.Modules.pushforward V.ι).map
          ((Scheme.Modules.restrictAdjunction V.ι).counit.app Q)) := by
      rw [← cancel_mono ((Scheme.Modules.pushforward V.ι).map
        ((Scheme.Modules.restrictAdjunction V.ι).counit.app Q)), h, IsIso.inv_hom_id]
      rfl
    rw [hu]
    infer_instance
  have hn := (Scheme.Modules.restrictAdjunction V.ι).unit.naturality e.hom
  simp only [Functor.id_map, Functor.comp_map] at hn
  have h₂ : IsIso (e.hom ≫ (Scheme.Modules.restrictAdjunction V.ι).unit.app
      ((Scheme.Modules.pushforward V.ι).obj Q)) := inferInstance
  rw [hn] at h₂
  exact IsIso.of_isIso_comp_right _
    ((Scheme.Modules.pushforward V.ι).map ((Scheme.Modules.restrictFunctor V.ι).map e.hom))

omit [IsProper g] [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y] in
/-- `H⁰(Rι_* W) ≅ ι_* H⁰(W)` for `W ∈ D^{≥0}` and an open immersion `ι`. -/
def homologyPushforwardIso {Z : Scheme.{u}} (V : Z.Opens) (W : DerivedCategory V.toScheme.Modules)
    [W.IsGE 0] :
    (homologyFunctor Z.Modules 0).obj ((derivedPushforward V.ι).obj W) ≅
      (Scheme.Modules.pushforward V.ι).obj ((homologyFunctor V.toScheme.Modules 0).obj W) :=
  haveI := Stacks.DerivedFunctor.isIso_homologyEdge_app_of_isGE (Scheme.Modules.pushforward V.ι)
    (derivedPushforward V.ι) (fun Z n h => @isGE_derivedPushforward_obj' _ _ V.ι Z n h) 0
    (singleDerivedPushforwardHomologyIso V.ι) W
  asIso ((Stacks.DerivedFunctor.homologyEdge (Scheme.Modules.pushforward V.ι)
    (derivedPushforward V.ι) (fun Z n h => @isGE_derivedPushforward_obj' _ _ V.ι Z n h) 0
    (singleDerivedPushforwardHomologyIso V.ι)).app W)

omit [IsProper g] [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y] in
/-- A morphism of sheaves of modules whose restriction to an open is invertible is bijective on
sections over that open. -/
theorem bijective_app_of_isIso_restrict {Z : Scheme.{u}} {M N : Z.Modules} (φ : M ⟶ N)
    (V : Z.Opens) [IsIso ((Scheme.Modules.restrictFunctor V.ι).map φ)] :
    Function.Bijective (φ.app V) := by
  have h :=
    Stacks.Algebraization.bijective_app_of_isIso ((Scheme.Modules.restrictFunctor V.ι).map φ) ⊤
  change Function.Bijective (φ.app (V.ι ''ᵁ ⊤)) at h
  rwa [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι] at h

omit [((twisted g).obj (DerivedPushforward.derivedStructureSheaf X)).obj.IsGE 0] in
/-- `H⁰(a(𝒪_X)) ⟶ H⁰(a(Rj_*j^*𝒪_X))` is bijective on sections over `g⁻¹U`. -/
theorem bijective_app_homology_twisted_map_structureUnit :
    Function.Bijective (((homologyFunctor Y.Modules 0).map
      ((twisted g).map (structureUnit U)).hom).app (g ⁻¹ᵁ U)) := by
  have := isIso_restrict_homology_twisted_map_structureUnit g U
  exact bijective_app_of_isIso_restrict _ _

omit [IsProper g] [AlgebraicGeometry.IsNoetherian Y] in
/-- `H⁰(𝒪_X ⟶ Rj_*j^*𝒪_X)` is bijective on sections over `U`. -/
theorem bijective_app_homology_structureUnit :
    Function.Bijective (((homologyFunctor X.Modules 0).map (structureUnit U).hom).app U) := by
  have h₁ : (structureUnit U).hom = (derivedRestrictPushforwardAdjunction U.ι).unit.app
      (DerivedPushforward.derivedStructureSheaf X).obj :=
    map_liftDerivedRestrictPushforwardAdjunction_unit_app U.ι _ _ _ _ _
  have h₂ :
      IsIso ((homologyFunctor _ 0).map ((derivedRestrict U.ι).map (structureUnit U).hom)) := by
    rw [h₁]
    have := isIso_derivedRestrict_map_unit_app U.ι (DerivedPushforward.derivedStructureSheaf X).obj
    infer_instance
  have : IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      ((homologyFunctor X.Modules 0).map (structureUnit U).hom)) :=
    (NatIso.isIso_map_iff
      ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategoryHomologyIso 0) _).1 h₂
  exact bijective_app_of_isIso_restrict _ _

/-- `j^*𝒪_X` lies in `D^{≥0}`. -/
instance isGE_restrictU_structureSheaf :
    ((restrictU U).obj (DerivedPushforward.derivedStructureSheaf X)).obj.IsGE 0 :=
  @isGE_derivedRestrict_obj _ _ _ _ _ 0 (isGE_derivedStructureSheaf X)

omit [IsProper g] [AlgebraicGeometry.IsNoetherian Y] in
/-- The unit of `j^* ⊣ j_*` is invertible at `H⁰(Rj_* j^*𝒪_X)`. -/
theorem isIso_unit_homology_unitTarget :
    IsIso ((Scheme.Modules.restrictAdjunction U.ι).unit.app ((homologyFunctor X.Modules 0).obj
      ((pushU U).obj ((restrictU U).obj (DerivedPushforward.derivedStructureSheaf X))).obj)) :=
  isIso_restrictAdjunction_unit_of_iso U
    (homologyPushforwardIso U ((restrictU U).obj (DerivedPushforward.derivedStructureSheaf X)).obj)

/-- The unit of `j'^* ⊣ j'_*` is invertible at `H⁰(a(Rj_* j^*𝒪_X))`. -/
theorem isIso_unit_zeroTwisted_unitTarget :
    IsIso ((Scheme.Modules.restrictAdjunction (g ⁻¹ᵁ U).ι).unit.app
      (zeroTwisted g ((pushU U).obj ((restrictU U).obj
        (DerivedPushforward.derivedStructureSheaf X))))) :=
  isIso_restrictAdjunction_unit_of_iso (g ⁻¹ᵁ U)
    ((homologyFunctor Y.Modules 0).mapIso ((ObjectProperty.ι _).mapIso (asIso
      ((baseChangeMap g U).app ((restrictU U).obj
        (DerivedPushforward.derivedStructureSheaf X))))).symm ≪≫
      homologyPushforwardIso (g ⁻¹ᵁ U) ((twisted (g ∣_ U)).obj ((restrictU U).obj
        (DerivedPushforward.derivedStructureSheaf X))).obj)

omit [((twisted g).obj (DerivedPushforward.derivedStructureSheaf X)).obj.IsGE 0] in
/-- The duality map of `φ : 𝒪_Y ⟶ H⁰(a(E))` on sections over `U` is the trace of `φ`. -/
theorem dualityMap_app_eq (E : quasiCoherentDerivedCategory X)
    [((twisted g).obj E).obj.IsGE 0]
    (φ : (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ⟶ zeroTwisted g E)
    (b : Γ((Scheme.Modules.pushforward g).obj (SheafOfModules.unit Y.ringCatSheaf), U)) :
    (dualityMap E φ).app U b =
      (trace (g := g) E).app U (Scheme.Modules.Hom.app φ (g ⁻¹ᵁ U) b) :=
  ConcreteCategory.congr_hom (congrArg (fun χ => Scheme.Modules.Hom.app χ U) (dualityMap_eq E φ)) b

omit [IsProper g] [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y] in
/-- The unit section of the structure sheaf, as a section of the unit sheaf of modules. -/
def unitOne {Z : Scheme.{u}} (V : Z.Opens) : Γ(SheafOfModules.unit Z.ringCatSheaf, V) :=
  (1 : Γ(Z, V))

/-- The trace of the structure sheaf is compatible with `structureUnit` on sections over `U`. -/
private theorem trace_app_smul_structureUnit (b : Γ(Y, g ⁻¹ᵁ U))
    (n : Γ(zeroTwisted g (DerivedPushforward.derivedStructureSheaf X), g ⁻¹ᵁ U)) :
    (trace (g := g) ((pushU U).obj ((restrictU U).obj
        (DerivedPushforward.derivedStructureSheaf X)))).app U
      (b • ((homologyFunctor Y.Modules 0).map ((twisted g).map (structureUnit U)).hom).app
        (g ⁻¹ᵁ U) n) =
      ((homologyFunctor X.Modules 0).map (structureUnit U).hom).app U
        ((trace (g := g) (DerivedPushforward.derivedStructureSheaf X)).app U (b • n)) := by
  have e₁ := congrArg (fun χ => χ.app U (b • n)) (trace_naturality (g := g)
    (DerivedPushforward.derivedStructureSheaf X) _ (structureUnit U))
  simp only [Scheme.Modules.Hom.comp_app] at e₁
  change (trace (g := g) ((pushU U).obj ((restrictU U).obj
    (DerivedPushforward.derivedStructureSheaf X)))).app U
    (((homologyFunctor Y.Modules 0).map ((twisted g).map (structureUnit U)).hom).app
      (g ⁻¹ᵁ U) (b • n)) = _ at e₁
  rw [Scheme.Modules.Hom.app_smul] at e₁
  exact e₁

/-- The values of the trace on the multiples of a section over `g⁻¹U` determine the section,
for `U` affine. -/
theorem eq_of_trace_smul_eq [IsAffineHom g] (hU : IsAffineOpen U)
    (m m₀ : Γ(zeroTwisted g (DerivedPushforward.derivedStructureSheaf X), g ⁻¹ᵁ U))
    (h : ∀ b : Γ(Y, g ⁻¹ᵁ U), (trace (DerivedPushforward.derivedStructureSheaf X)).app U (b • m) =
      (trace (DerivedPushforward.derivedStructureSheaf X)).app U (b • m₀)) : m = m₀ := by
  let O := DerivedPushforward.derivedStructureSheaf X
  let E := (pushU U).obj ((restrictU U).obj O)
  let hη := (homologyFunctor Y.Modules 0).map ((twisted g).map (structureUnit U)).hom
  let κ := (homologyFunctor X.Modules 0).map (structureUnit U).hom
  have hV : IsAffineOpen (g ⁻¹ᵁ U) := hU.preimage g
  have key := trace_app_smul_structureUnit g U
  have hunitP := isIso_unit_zeroTwisted_unitTarget g U
  have hunitE := isIso_unit_homology_unitTarget U
  have : (zeroTwisted g E).IsQuasicoherent := ((twisted g).obj E).2 0
  have : ((homologyFunctor X.Modules 0).obj E.obj).IsQuasicoherent := E.2 0
  obtain ⟨φ₁, hφ₁⟩ := Stacks.AlgebraicGeometry.exists_hom_app_affineOpen_of_isIso_unit (g ⁻¹ᵁ U)
    hV hunitP (N := SheafOfModules.unit Y.ringCatSheaf)
    (LinearMap.toSpanSingleton Γ(Y, g ⁻¹ᵁ U) _ (hη.app (g ⁻¹ᵁ U) m))
  obtain ⟨φ₂, hφ₂⟩ := Stacks.AlgebraicGeometry.exists_hom_app_affineOpen_of_isIso_unit (g ⁻¹ᵁ U)
    hV hunitP (N := SheafOfModules.unit Y.ringCatSheaf)
    (LinearMap.toSpanSingleton Γ(Y, g ⁻¹ᵁ U) _ (hη.app (g ⁻¹ᵁ U) m₀))
  have hdφ : dualityMap (g := g) E φ₁ = dualityMap (g := g) E φ₂ := by
    refine Stacks.AlgebraicGeometry.hom_ext_of_app_affineOpen_of_isIso_unit U hU hunitE
      fun b => ?_
    refine (dualityMap_app_eq g U E φ₁ b).trans (Eq.trans ?_ (dualityMap_app_eq g U E φ₂ b).symm)
    refine (congrArg _ (hφ₁ b)).trans (Eq.trans ?_ (congrArg _ (hφ₂ b)).symm)
    exact (key b m).trans ((congrArg (κ.app U) (h b)).trans (key b m₀).symm)
  have hφ : φ₁ = φ₂ := (bijective_dualityMap (g := g) E (SheafOfModules.unit Y.ringCatSheaf)).1 hdφ
  have h₃ := (hφ₁ (unitOne _)).symm.trans
    ((congrArg (fun φ => φ.app (g ⁻¹ᵁ U) (unitOne _)) hφ).trans (hφ₂ (unitOne _)))
  have h₄ : hη.app (g ⁻¹ᵁ U) m = hη.app (g ⁻¹ᵁ U) m₀ := by
    have e₁ := LinearMap.toSpanSingleton_apply_one Γ(Y, g ⁻¹ᵁ U) _ (hη.app (g ⁻¹ᵁ U) m)
    have e₂ := LinearMap.toSpanSingleton_apply_one Γ(Y, g ⁻¹ᵁ U) _ (hη.app (g ⁻¹ᵁ U) m₀)
    exact e₁.symm.trans (h₃.trans e₂)
  exact (bijective_app_homology_twisted_map_structureUnit g U).1 h₄

omit [IsProper g] [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y] in
/-- A morphism `ψ : 𝒪_Z ⟶ M` sends a section `b` over `V` to `b • ψ(1)`. -/
theorem app_eq_smul_app_one {Z : Scheme.{u}} {M : Z.Modules}
    (ψ : (SheafOfModules.unit Z.ringCatSheaf : Z.Modules) ⟶ M) (V : Z.Opens) (b : Γ(Z, V)) :
    Scheme.Modules.Hom.app ψ V b = b • Scheme.Modules.Hom.app ψ V (unitOne V) :=
  (congrArg (fun z : Γ(Z, V) => Scheme.Modules.Hom.app ψ V z) (mul_one b)).symm.trans
    (Scheme.Modules.Hom.app_smul ψ b (unitOne V))

omit [IsProper g] [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y] in
/-- The action of a morphism of sheaves of modules on sections over `V`, as a linear map. -/
def appLinear {Z : Scheme.{u}} {M N : Z.Modules} (φ : M ⟶ N) (V : Z.Opens) :
    Γ(M, V) →ₗ[Γ(Z, V)] Γ(N, V) where
  toFun := φ.app V
  map_add' := map_add _
  map_smul' := Scheme.Modules.Hom.app_smul φ

omit [IsProper g] [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y] in
/-- `appLinear φ V` acts as `φ` on sections over `V`. -/
theorem appLinear_apply {Z : Scheme.{u}} {M N : Z.Modules} (φ : M ⟶ N) (V : Z.Opens)
    (x : Γ(M, V)) : appLinear φ V x = φ.app V x := rfl

/-- Every `Γ(X, U)`-linear form on `Γ(Y, g⁻¹U)` is `b ↦ t(b • m)` for a section `m` of
`H⁰(a(𝒪_X))` over `g⁻¹U`, for `U` affine. -/
theorem exists_trace_smul_eq [IsAffineHom g] (hU : IsAffineOpen U)
    (l : Γ((Scheme.Modules.pushforward g).obj (SheafOfModules.unit Y.ringCatSheaf), U) →ₗ[Γ(X, U)]
      Γ((homologyFunctor X.Modules 0).obj (DerivedPushforward.derivedStructureSheaf X).obj, U)) :
    ∃ m : Γ(zeroTwisted g (DerivedPushforward.derivedStructureSheaf X), g ⁻¹ᵁ U),
      ∀ b : Γ(Y, g ⁻¹ᵁ U),
        (trace (g := g) (DerivedPushforward.derivedStructureSheaf X)).app U (b • m) = l b := by
  let O := DerivedPushforward.derivedStructureSheaf X
  let E := (pushU U).obj ((restrictU U).obj O)
  let hη := (homologyFunctor Y.Modules 0).map ((twisted g).map (structureUnit U)).hom
  let κ := (homologyFunctor X.Modules 0).map (structureUnit U).hom
  have key := trace_app_smul_structureUnit g U
  have hunitE := isIso_unit_homology_unitTarget U
  have : ((homologyFunctor X.Modules 0).obj E.obj).IsQuasicoherent := E.2 0
  obtain ⟨φ, hφ⟩ := Stacks.AlgebraicGeometry.exists_hom_app_affineOpen_of_isIso_unit U hU hunitE
    ((appLinear κ U).comp l)
  obtain ⟨ψ, hψ⟩ := (bijective_dualityMap (g := g) E (SheafOfModules.unit Y.ringCatSheaf)).2 φ
  obtain ⟨m, hm⟩ := (bijective_app_homology_twisted_map_structureUnit g U).2
    (ψ.app (g ⁻¹ᵁ U) (unitOne _))
  refine ⟨m, fun b => (bijective_app_homology_structureUnit U).1 ?_⟩
  calc κ.app U ((trace (g := g) O).app U (b • m))
      = (trace (g := g) E).app U (b • hη.app (g ⁻¹ᵁ U) m) := (key b m).symm
    _ = (trace (g := g) E).app U (b • ψ.app (g ⁻¹ᵁ U) (unitOne _)) :=
        congrArg (fun z : Γ(zeroTwisted g E, g ⁻¹ᵁ U) => (trace (g := g) E).app U (b • z)) hm
    _ = (trace (g := g) E).app U (ψ.app (g ⁻¹ᵁ U) b) :=
        congrArg ((trace (g := g) E).app U) (app_eq_smul_app_one ψ _ b).symm
    _ = (dualityMap (g := g) E ψ).app U b := (dualityMap_app_eq g U E ψ b).symm
    _ = φ.app U b := by rw [hψ]
    _ = κ.app U (l b) := (hφ b).trans ((LinearMap.comp_apply _ _ _).trans (appLinear_apply κ U _))

end Restriction

end Stacks.Duality.FiniteTrace
