module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticExtensionHomotopy
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticExtensionQuasiIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticDerivedPullback

/-!
# Extension and restriction of differential graded modules along a subcategory of a chaotic site

Let `F : C' ⥤ C` be a functor of chaotic sites such that every category `U/F` of arrows
`U → F U'` is cofiltered, let `(A, d)` be a sheaf of differential graded algebras on `C` and
`(A', d)` its restriction to `C'`. This file assembles, at the level of right differential graded
modules,

* the restriction `M ↦ M|_{C'}`, whose sections over `U'` are the sections of `M` over `F U'`,
* the extension `M' ↦ E(M')` with `E(M')(U) = colim_{U → F U'} M'(U') ⊗_{A'(U')} A(U)`,

and shows that the extension is left adjoint to the restriction, with unit an isomorphism when
`F` is fully faithful, that both carry homotopies to homotopies, and that the restriction is
exact.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.ChaoticExtension.restriction`: **restriction of right
  differential graded modules along `F`.**
* `SheafOfModules.DifferentialGradedModule.ChaoticExtension.extension`: **the extension.**
* `SheafOfModules.DifferentialGradedModule.ChaoticExtension.moduleAdjunction`: the extension is
  left adjoint to the restriction.

## Main results

* `SheafOfModules.DifferentialGradedModule.ChaoticExtension.isIso_moduleAdjunction_unit_app`: the
  unit is an isomorphism for a fully faithful `F`.
* `SheafOfModules.DifferentialGradedModule.ChaoticExtension.quasiIso_restriction_map` and
  `quasiIso_extension_map`: restriction is exact, and the extension inverts quasi-isomorphisms
  between good modules.
* `SheafOfModules.DifferentialGradedModule.ChaoticExtension.quasiIso_moduleAdjunction_counit_app`:
  the counit is a quasi-isomorphism at a good module satisfying the quasi-coherence condition.

## References

* [Stacks Project, Lemma 24.34.1 (Tag 0GZE)](https://stacks.math.columbia.edu/tag/0GZE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf
open DifferentialGradedModule (forgetToCochainComplex acyclic' toHomotopyCategory)

universe u

namespace SheafOfModules

attribute [local instance] GradedAlgebra.sectionsGOne GradedAlgebra.sectionsGMul
  GradedAlgebra.sectionsGRing Stacks.uliftIntAlgebra

namespace DifferentialGradedModule

/-- **A morphism of presheaves of section modules which is a quasi-isomorphism over every object
realizes to a quasi-isomorphism.** -/
theorem SectionSystem.quasiIso_realizeMap {C : Type u} [Category.{u} C]
    [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {Osharp : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u}}
    {B : DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}
    {X Y : SectionSystem B} (f : X ⟶ Y)
    (hf : ∀ U, QuasiIso ((forgetToCochainComplex (B.sectionAlgebra U)).map (f.app U))) :
    QuasiIso (SectionSystem.realizeMap f).toHomologicalComplex := by
  refine quasiIso_of_forall_quasiIso_sectionMap _ fun U => ?_
  have e : Arrow.mk (sectionMap (SectionSystem.realizeMap f) U) ≅ Arrow.mk (f.app U) :=
    Arrow.isoMk (X.sectionsIso U) (Y.sectionsIso U)
      (SectionSystem.sectionsIso_naturality f U).symm
  exact (quasiIso_iff_of_arrow_mk_iso _ _
    ((forgetToCochainComplex (B.sectionAlgebra U)).mapArrow.mapIso e)).2 (hf U)

namespace ChaoticExtension

variable {C : Type u} [Category.{u} C] {C' : Type u} [Category.{u} C'] (F : C' ⥤ C)
  [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {Osharp : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u}}
  (A : DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp))
  [∀ U : C, IsCofiltered (StructuredArrow U F)]

/-- **Restriction of right differential graded modules along `F`**: the module over the
restriction `A'` whose sections over `U'` are the sections over `F U'`. -/
def restriction : DifferentialGradedModule.{u, u, u} A ⥤
    DifferentialGradedModule.{u, u, u} (A.restrict F) :=
  sectionSystemFunctor A ⋙ (restrictFunctor F A ⋙ (ofAlong F A ⋙
    SectionSystem.realizeFunctor (A.restrict F)))

/-- **Restriction is literally restriction, on sections**: the sections over `U'` of the
restriction of `M` are the sections `M(F U')` of `M` over `F U'`, read over
`A'(U') = A(F U')` through `restrictSectionHom`. -/
def restriction_sectionModuleIso (M : DifferentialGradedModule.{u, u, u} A) (U' : C'ᵒᵖ) :
    ((restriction F A).obj M).sectionModule U' ≅
      _root_.DifferentialGradedModule.restrictScalars (A.restrictSectionHom F U')
        (M.sectionModule (F.op.obj U')) :=
  ((ofAlong F A).obj ((restrictFunctor F A).obj ((sectionSystemFunctor A).obj M))).sectionsIso U'

/-- The identification of the sections of a restriction is natural in the module. -/
theorem restriction_sectionModuleIso_naturality {M N : DifferentialGradedModule.{u, u, u} A}
    (f : M ⟶ N) (U' : C'ᵒᵖ) :
    sectionMap ((restriction F A).map f) U' ≫ (restriction_sectionModuleIso F A N U').hom =
      (restriction_sectionModuleIso F A M U').hom ≫
        _root_.DifferentialGradedModule.restrictScalarsHom (A.restrictSectionHom F U')
          (sectionMap f (F.op.obj U')) :=
  SectionSystem.sectionsIso_naturality _ U'

/-- **The extension of right differential graded modules from `C'` to `C`**: over `U` its
sections are `colim_{U → F U'} M'(U') ⊗_{A'(U')} A(U)`. -/
def extension : DifferentialGradedModule.{u, u, u} (A.restrict F) ⥤
    DifferentialGradedModule.{u, u, u} A :=
  ((sectionSystemFunctor (A.restrict F) ⋙ toAlong F A) ⋙ extFunctor F A) ⋙
    SectionSystem.realizeFunctor A

/-- **The extension is left adjoint to the restriction.** -/
def moduleAdjunction : extension F A ⊣ restriction F A :=
  (((sectionSystemEquivalence (A.restrict F)).toAdjunction.comp
    (alongEquivalence F A).toAdjunction).comp adjunction).comp (SectionSystem.realizeAdjunction A)

/-- The unit of an equivalence of categories is an isomorphism at each object. -/
theorem isIso_equivalence_unit_app {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (e : 𝒞 ≌ 𝒟)
    (X : 𝒞) : IsIso (e.unit.app X) :=
  (e.unitIso.app X).isIso_hom

/-- The counit of an equivalence of categories is an isomorphism at each object. -/
theorem isIso_equivalence_counit_app {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (e : 𝒞 ≌ 𝒟)
    (Y : 𝒟) : IsIso (e.counit.app Y) :=
  (e.counitIso.app Y).isIso_hom

/-- **For a fully faithful `F` the unit of the adjunction is an isomorphism.** -/
instance isIso_moduleAdjunction_unit_app [F.Full] [F.Faithful]
    (M : DifferentialGradedModule.{u, u, u} (A.restrict F)) :
    IsIso ((moduleAdjunction F A).unit.app M) := by
  simp only [moduleAdjunction, Adjunction.comp_unit_app, Equivalence.toAdjunction_unit]
  refine IsIso.comp_isIso' (IsIso.comp_isIso' (IsIso.comp_isIso' ?_ ?_) ?_) ?_
  · exact isIso_equivalence_unit_app _ _
  · haveI := isIso_equivalence_unit_app (alongEquivalence F A)
      ((sectionSystemEquivalence (A.restrict F)).functor.obj M)
    infer_instance
  · haveI : IsIso ((adjunction (F := F) (A := A)).unit.app
        (((sectionSystemEquivalence (A.restrict F)).functor ⋙ (alongEquivalence F A).functor).obj
          M)) := isIso_unit _
    infer_instance
  · exact @Functor.map_isIso _ _ _ _ _ _ _ _
      (isIso_equivalence_unit_app (sectionSystemEquivalence A).symm _)

/-! ### Homotopies -/

/-- Restriction along `F` carries homotopic morphisms to homotopic morphisms. -/
theorem preservesHomotopic_restriction : PreservesHomotopic (restriction F A) :=
  fun _ _ ⟨h⟩ => SectionSystem.realizeMap_homotopic
    (ofAlongHomotopy (restrictHomotopy (sectionSystemHomotopy h)))

/-- The extension along `F` carries homotopic morphisms to homotopic morphisms. -/
theorem preservesHomotopic_extension : PreservesHomotopic (extension F A) :=
  fun _ _ ⟨h⟩ => SectionSystem.realizeMap_homotopic
    (extHomotopy (toAlongHomotopy (sectionSystemHomotopy h)))

/-! ### Quasi-isomorphisms -/

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [∀ U : C, IsCofiltered (StructuredArrow U F)] in
/-- An isomorphism of right differential graded modules is a quasi-isomorphism. -/
theorem quasiIso_of_isIso' {B : DifferentialGradedAlgebra.{u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}
    {M N : DifferentialGradedModule.{u, u, u} B} (f : M ⟶ N) [IsIso f] :
    QuasiIso f.toHomologicalComplex := by
  have : IsIso f.toHomologicalComplex :=
    ⟨(inv f).toHomologicalComplex, congrArg Hom.toHomologicalComplex (IsIso.hom_inv_id f),
      congrArg Hom.toHomologicalComplex (IsIso.inv_hom_id f)⟩
  infer_instance

attribute [local irreducible] DifferentialGradedAlgebra.sectionAlgebra in
/-- **Restriction is exact**: it carries quasi-isomorphisms to quasi-isomorphisms. -/
theorem quasiIso_restriction_map {M N : DifferentialGradedModule.{u, u, u} A} (f : M ⟶ N)
    (hf : QuasiIso f.toHomologicalComplex) :
    QuasiIso ((restriction F A).map f).toHomologicalComplex :=
  SectionSystem.quasiIso_realizeMap _ fun U' => quasiIso_sectionMap f (F.op.obj U') hf

attribute [local irreducible] DifferentialGradedAlgebra.sectionAlgebra in
/-- **Restriction preserves goodness.** -/
theorem restriction_isSectionGood {P : DifferentialGradedModule.{u, u, u} A}
    (hP : ∀ U : Cᵒᵖ, (acyclic' (A.sectionAlgebra U)).leftOrthogonal
      ((toHomotopyCategory (A.sectionAlgebra U)).obj (P.sectionModule U))) (U' : C'ᵒᵖ) :
    (acyclic' ((A.restrict F).sectionAlgebra U')).leftOrthogonal
      ((toHomotopyCategory ((A.restrict F).sectionAlgebra U')).obj
        (((restriction F A).obj P).sectionModule U')) :=
  ObjectProperty.prop_of_iso _ ((toHomotopyCategory _).mapIso
      (((ofAlong F A).obj ((restrictFunctor F A).obj
        ((sectionSystemFunctor A).obj P))).sectionsIso U').symm)
    (DifferentialGraded.Bimodule.leftOrthogonal_restrictScalars_of_inverse
      (A.restrictSectionInv F U') (A.restrictSectionHom F U') (A.restrictSectionHom_inv F U')
      (A.restrictSectionInv_hom F U') _ (hP (F.op.obj U')))

attribute [local irreducible] DifferentialGradedAlgebra.sectionAlgebra in
/-- **The extension carries a quasi-isomorphism between good modules to a quasi-isomorphism.** -/
theorem quasiIso_extension_map {M N : DifferentialGradedModule.{u, u, u} (A.restrict F)}
    (f : M ⟶ N) (hf : QuasiIso f.toHomologicalComplex)
    (hM : ∀ U' : C'ᵒᵖ, (acyclic' ((A.restrict F).sectionAlgebra U')).leftOrthogonal
      ((toHomotopyCategory ((A.restrict F).sectionAlgebra U')).obj (M.sectionModule U')))
    (hN : ∀ U' : C'ᵒᵖ, (acyclic' ((A.restrict F).sectionAlgebra U')).leftOrthogonal
      ((toHomotopyCategory ((A.restrict F).sectionAlgebra U')).obj (N.sectionModule U'))) :
    QuasiIso ((extension F A).map f).toHomologicalComplex :=
  SectionSystem.quasiIso_realizeMap _ fun _ =>
    _root_.DifferentialGradedModule.FilteredColimit.quasiIso_map _ fun j =>
      DifferentialGraded.Bimodule.quasiIso_tensorCompFunctor_map_of_leftOrthogonal _ _
        (quasiIso_sectionMap f (Opposite.op j.unop.right) hf)
        (DifferentialGraded.Bimodule.leftOrthogonal_restrictScalars_of_inverse
          (A.restrictSectionHom F _) (A.restrictSectionInv F _) (A.restrictSectionInv_hom F _)
          (A.restrictSectionHom_inv F _) _ (hM _))
        (DifferentialGraded.Bimodule.leftOrthogonal_restrictScalars_of_inverse
          (A.restrictSectionHom F _) (A.restrictSectionInv F _) (A.restrictSectionInv_hom F _)
          (A.restrictSectionHom_inv F _) _ (hN _))

/-! ### The counit -/

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [∀ U : C, IsCofiltered (StructuredArrow U F)] in
/-- The component over `U` of an isomorphism of presheaves of section modules is an
isomorphism. -/
theorem SectionSystem.isIso_app_of_isIso {B : DifferentialGradedAlgebra.{u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}
    {X Y : SectionSystem B} (f : X ⟶ Y) [IsIso f] (U : Cᵒᵖ) : IsIso (f.app U) :=
  ⟨(inv f).app U, congrArg (fun g => SectionSystem.Hom.app g U) (IsIso.hom_inv_id f),
    congrArg (fun g => SectionSystem.Hom.app g U) (IsIso.inv_hom_id f)⟩

omit [∀ U : C, IsCofiltered (StructuredArrow U F)] in
/-- The counit of the composite of the adjunctions given by `sectionSystemEquivalence` and
`alongEquivalence` is an isomorphism at every object of `AlongSystem F A`. -/
theorem isIso_alongCounit (Z : AlongSystem F A) :
    IsIso ((((sectionSystemEquivalence (A.restrict F)).toAdjunction.comp
      (alongEquivalence F A).toAdjunction)).counit.app Z) := by
  rw [Adjunction.comp_counit_app, Equivalence.toAdjunction_counit,
    Equivalence.toAdjunction_counit]
  have := isIso_equivalence_counit_app (sectionSystemEquivalence (A.restrict F))
    ((alongEquivalence F A).inverse.obj Z)
  have := isIso_equivalence_counit_app (alongEquivalence F A) Z
  infer_instance

/-- **The counit of the adjunction is a quasi-isomorphism at a good module satisfying the
quasi-coherence condition.** Over every object `U` it is the counit of the adjunction on
presheaves of section modules, a filtered colimit of the comparison maps
`N(F U') ⊗_{A(F U')} A(U) ⟶ N(U)`, each of them a quasi-isomorphism. -/
theorem quasiIso_moduleAdjunction_counit_app (N : DifferentialGradedModule.{u, u, u} A)
    (hgood : ∀ U : Cᵒᵖ, (acyclic' (A.sectionAlgebra U)).leftOrthogonal
      ((toHomotopyCategory (A.sectionAlgebra U)).obj (N.sectionModule U)))
    (hqc : Chaotic.IsQCModule N) :
    QuasiIso ((moduleAdjunction F A).counit.app N).toHomologicalComplex := by
  let adj := (sectionSystemEquivalence (A.restrict F)).toAdjunction.comp
    (alongEquivalence F A).toAdjunction
  let Z := (restrictFunctor F A).obj ((sectionSystemFunctor A).obj N)
  have e := Adjunction.comp_counit_app (adj.comp adjunction) (SectionSystem.realizeAdjunction A) N
  have e2 := Adjunction.comp_counit_app adj (adjunction (F := F) (A := A))
    ((sectionSystemFunctor A).obj N)
  show QuasiIso (((adj.comp adjunction).comp
    (SectionSystem.realizeAdjunction A)).counit.app N).toHomologicalComplex
  rw [e]
  have : IsIso ((SectionSystem.realizeAdjunction A).counit.app N) :=
    isIso_equivalence_counit_app (sectionSystemEquivalence A).symm N
  have := quasiIso_of_isIso' ((SectionSystem.realizeAdjunction A).counit.app N)
  have : QuasiIso ((SectionSystem.realizeFunctor A).map
      ((adj.comp adjunction).counit.app
        ((sectionSystemFunctor A).obj N))).toHomologicalComplex := by
    refine SectionSystem.quasiIso_realizeMap _ fun U => ?_
    rw [e2, SectionSystem.comp_app, Functor.map_comp]
    have := isIso_alongCounit F A Z
    have h0 := SectionSystem.isIso_app_of_isIso ((extFunctor F A).map (adj.counit.app Z)) U
    have h1 : QuasiIso ((forgetToCochainComplex (A.sectionAlgebra U)).map
        (((extFunctor F A).map (adj.counit.app Z)).app U)) := quasiIso_of_isIso _
    have h2 := quasiIso_counitApp (F := F) ((sectionSystemFunctor A).obj N)
      (fun {U} (b : StructuredArrow U.unop F) =>
        (Chaotic.isIso_sectionComparison_iff_quasiIso N b.hom.op (hgood _)).1 (hqc b.hom.op)) U
    exact @quasiIso_comp _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2
  show QuasiIso (((SectionSystem.realizeFunctor A).map _).toHomologicalComplex ≫
    ((SectionSystem.realizeAdjunction A).counit.app N).toHomologicalComplex)
  infer_instance

end ChaoticExtension

end DifferentialGradedModule

end SheafOfModules

end
