module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticExtensionQuasiCoherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticSheafInstances
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticPullbackQuasiCoherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedPushforwardAdjunction
public import StacksFrontier.CategoryTheory.Localization.AbsoluteLeftDerivedAdjunction
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import StacksCore.Tactic.StacksAttribute

/-!
# Restriction to a cofiltered subcategory is an equivalence on quasi-coherent objects

Let `C` be a category with the chaotic topology, `O` a sheaf of commutative rings and `(A, d)` a
sheaf of differential graded `O`-algebras on it, as in Section 0GZ8. Let `C' ⊆ C` be a full
subcategory such that for every object `U` of `C` the category `U/C'` of arrows `U → U'` is
cofiltered, and let `O'`, `A'` be the restrictions of `O`, `A` to `C'`. Tag 0GZE says that
restriction induces an equivalence `QC(A, d) → QC(A', d)`.

The proof is the source's. Restriction of differential graded modules is exact, so it induces a
functor `D(A, d) ⥤ D(A', d)`. Its quasi-inverse is the derived functor of the colimit extension
`M' ↦ M`, `M(U) = colim_{U → U' ∈ U/C'} M'(U') ⊗_{A'(U')} A(U)`, computed on good modules; the
extension is left adjoint to restriction on modules, and the adjunction derives to an adjunction
between `D(A', d)` and `D(A, d)`. The unit of that adjunction is an isomorphism, the extension
being followed by restriction is the identity on modules. The counit is an isomorphism at the
objects of `QC(A, d)`: over `U` it is the filtered colimit of the comparison maps along the arrows
`U → U'`, which quasi-coherence makes quasi-isomorphisms. Both functors preserve quasi-coherence,
and the adjunction restricts to the equivalence.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.ChaoticExtension.derivedRestriction`: restriction on
  the derived categories.
* `SheafOfModules.DifferentialGradedModule.ChaoticExtension.derivedExtension`: the derived
  extension, and `derivedAdjunction` the adjunction between them.
* `SheafOfModules.DifferentialGradedModule.ChaoticExtension.qcRestriction`: restriction
  `QC(A, d) ⥤ QC(A', d)`.

## Main results

* `SheafOfModules.DifferentialGradedModule.ChaoticExtension.isEquivalence_qcRestriction`:
  **Tag 0GZE.**

## References

* [Stacks Project, Lemma 24.34.1 (Tag 0GZE)](https://stacks.math.columbia.edu/tag/0GZE)
* [Stacks Project, Definition 24.33.1 (Tag 0GZ9)](https://stacks.math.columbia.edu/tag/0GZ9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf CategoryTheory.Functor
open DifferentialGradedModule (acyclic' toHomotopyCategory)

universe u

namespace SheafOfModules

attribute [local instance] GradedAlgebra.sectionsGOne GradedAlgebra.sectionsGMul
  GradedAlgebra.sectionsGRing Stacks.uliftIntAlgebra
  Stacks.SheafOfModules.botWEqualsLocallyBijective

namespace DifferentialGradedModule.ChaoticExtension

/-- The class of a quasi-isomorphism of differential graded modules is invertible in `D(B, d)`. -/
private theorem isIso_toDerivedCategory_map_quotient_map {C : Type u} [Category.{u} C]
    {Osharp : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u}}
    {B : DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}
    {M N : DifferentialGradedModule.{u, u, u} B} (f : M ⟶ N)
    (hf : QuasiIso f.toHomologicalComplex) :
    IsIso ((toDerivedCategory.{u, u, u} B).map ((HomotopyCategory.quotient B).map f)) :=
  (quasiIsomorphisms.{u, u, u} B).Q_inverts _ ((quasiIsomorphisms_quotient_map_iff f).2 hf)

variable {C : Type u} [Category.{u} C] {C' : Type u} [Category.{u} C'] (F : C' ⥤ C)
  [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {Osharp : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u}}
  (A : DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp))
  [∀ U : C, IsCofiltered (StructuredArrow U F)]

/-! ### The functors on homotopy categories -/

/-- Restriction on the homotopy categories. -/
abbrev homotopyRestriction :
    HomotopyCategory.{u, u, u} A ⥤ HomotopyCategory.{u, u, u} (A.restrict F) :=
  HomotopyCategory.descend (restriction F A) (preservesHomotopic_restriction F A)

/-- The extension on the homotopy categories. -/
abbrev homotopyExtension :
    HomotopyCategory.{u, u, u} (A.restrict F) ⥤ HomotopyCategory.{u, u, u} A :=
  HomotopyCategory.descend (extension F A) (preservesHomotopic_extension F A)

/-- The adjunction on the homotopy categories. -/
abbrev homotopyAdjunction : homotopyExtension F A ⊣ homotopyRestriction F A :=
  HomotopyCategory.descendAdjunction (moduleAdjunction F A) (preservesHomotopic_restriction F A)
    (preservesHomotopic_extension F A)

/-! ### Restriction on the derived categories -/


/-- Restriction followed by the localization `K(A') ⥤ D(A', d)` inverts quasi-isomorphisms. -/
theorem quasiIsomorphisms_isInvertedBy_restriction :
    (quasiIsomorphisms.{u, u, u} A).IsInvertedBy
      (homotopyRestriction F A ⋙ toDerivedCategory.{u, u, u} (A.restrict F)) := by
  intro X Y s hs
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient A).map_surjective s
  exact isIso_toDerivedCategory_map_quotient_map _
    (quasiIso_restriction_map F A f ((quasiIsomorphisms_quotient_map_iff f).1 hs))

/-- **Restriction on the derived categories** `D(A, d) ⥤ D(A', d)`: restriction is exact, so it
descends through the localization. -/
def derivedRestriction :
    derivedCategory.{u, u, u} A ⥤ derivedCategory.{u, u, u} (A.restrict F) :=
  Localization.lift _ (quasiIsomorphisms_isInvertedBy_restriction F A)
    (toDerivedCategory.{u, u, u} A)

/-- The identification of restriction on the derived categories with restriction of modules. -/
def derivedRestrictionFac :
    toDerivedCategory.{u, u, u} A ⋙ derivedRestriction F A ≅
      homotopyRestriction F A ⋙ toDerivedCategory.{u, u, u} (A.restrict F) :=
  Localization.fac _ (quasiIsomorphisms_isInvertedBy_restriction F A) _

/-! ### The derived extension -/

/-- The extension followed by the localization functor `K(A) ⥤ D(A, d)`. -/
abbrev extensionToDerived :
    HomotopyCategory.{u, u, u} (A.restrict F) ⥤ derivedCategory.{u, u, u} A :=
  homotopyExtension F A ⋙ toDerivedCategory.{u, u, u} A

/-- The extension followed by localization inverts a quasi-isomorphism between good modules. -/
theorem isIso_extensionToDerived_map {X Y : HomotopyCategory.{u, u, u} (A.restrict F)}
    (s : X ⟶ Y) (hs : quasiIsomorphisms.{u, u, u} (A.restrict F) s)
    (hX : sectionGoodProperty (A.restrict F) X) (hY : sectionGoodProperty (A.restrict F) Y) :
    IsIso ((extensionToDerived F A).map s) := by
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient (A.restrict F)).map_surjective s
  exact isIso_toDerivedCategory_map_quotient_map _
    (quasiIso_extension_map F A f ((quasiIsomorphisms_quotient_map_iff f).1 hs) hX hY)

/-- The extension followed by localization has a left derived functor with respect to
quasi-isomorphisms. -/
theorem hasLeftDerivedFunctor_extensionToDerived :
    (extensionToDerived F A).HasLeftDerivedFunctor (quasiIsomorphisms.{u, u, u} (A.restrict F)) :=
  have := LeftDerivedByResolutions.hasPointwiseLeftDerivedFunctor_of_resolutions
    (quasiIsomorphisms.{u, u, u} (A.restrict F)) (sectionGoodProperty (A.restrict F))
    (exists_sectionGoodProperty (A.restrict F)) _
    (fun s hs hX hY => isIso_extensionToDerived_map F A s hs hX hY)
  Functor.hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor _ _

/-- **The derived extension** `D(A', d) ⥤ D(A, d)`, the left derived functor of the colimit
extension, computed on good modules. -/
def derivedExtension :
    derivedCategory.{u, u, u} (A.restrict F) ⥤ derivedCategory.{u, u, u} A :=
  haveI := hasLeftDerivedFunctor_extensionToDerived F A
  (extensionToDerived F A).totalLeftDerived (toDerivedCategory.{u, u, u} (A.restrict F))
    (quasiIsomorphisms.{u, u, u} (A.restrict F))

/-- The counit of the derived extension. -/
def derivedExtensionCounit :
    toDerivedCategory.{u, u, u} (A.restrict F) ⋙ derivedExtension F A ⟶ extensionToDerived F A :=
  haveI := hasLeftDerivedFunctor_extensionToDerived F A
  (extensionToDerived F A).totalLeftDerivedCounit (toDerivedCategory.{u, u, u} (A.restrict F))
    (quasiIsomorphisms.{u, u, u} (A.restrict F))

/-- `derivedExtension F A` is the left derived functor of `extensionToDerived F A`, with counit
`derivedExtensionCounit F A`. -/
instance isLeftDerivedFunctor_derivedExtension :
    (derivedExtension F A).IsLeftDerivedFunctor (derivedExtensionCounit F A)
      (quasiIsomorphisms.{u, u, u} (A.restrict F)) :=
  haveI := hasLeftDerivedFunctor_extensionToDerived F A
  show ((extensionToDerived F A).totalLeftDerived (toDerivedCategory.{u, u, u} (A.restrict F))
      (quasiIsomorphisms.{u, u, u} (A.restrict F))).IsLeftDerivedFunctor
    ((extensionToDerived F A).totalLeftDerivedCounit (toDerivedCategory.{u, u, u} (A.restrict F))
      (quasiIsomorphisms.{u, u, u} (A.restrict F))) (quasiIsomorphisms.{u, u, u} (A.restrict F))
    from inferInstance

/-- The counit of the derived extension is an isomorphism at a good module. -/
theorem isIso_derivedExtensionCounit_app {X : HomotopyCategory.{u, u, u} (A.restrict F)}
    (hX : sectionGoodProperty (A.restrict F) X) :
    IsIso ((derivedExtensionCounit F A).app X) :=
  LeftDerivedByResolutions.isIso_app_of_resolutions (quasiIsomorphisms.{u, u, u} (A.restrict F))
    (sectionGoodProperty (A.restrict F)) (exists_sectionGoodProperty (A.restrict F)) _
    (fun s hs hX hY => isIso_extensionToDerived_map F A s hs hX hY)
    (toDerivedCategory.{u, u, u} (A.restrict F)) (derivedExtension F A)
    (derivedExtensionCounit F A) X hX

/-! ### The derived adjunction -/

/-- `derivedRestriction F A` is the right derived functor of restriction followed by
localization. -/
instance isRightDerivedFunctor_derivedRestriction :
    (derivedRestriction F A).IsRightDerivedFunctor (derivedRestrictionFac F A).inv
      (quasiIsomorphisms.{u, u, u} A) :=
  Functor.isRightDerivedFunctor_of_inverts _ _ (derivedRestrictionFac F A)

/-- The derived extension followed by derived restriction is the left derived functor of the
extension followed by derived restriction. -/
instance isLeftDerivedFunctor_derivedExtension_comp :
    (derivedExtension F A ⋙ derivedRestriction F A).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (derivedExtensionCounit F A) (derivedRestriction F A))
      (quasiIsomorphisms.{u, u, u} (A.restrict F)) :=
  LeftDerivedByResolutions.isLeftDerivedFunctor_comp_of_resolutions
    (quasiIsomorphisms.{u, u, u} (A.restrict F)) (sectionGoodProperty (A.restrict F))
    (exists_sectionGoodProperty (A.restrict F)) _
    (fun s hs hX hY => isIso_extensionToDerived_map F A s hs hX hY)
    (toDerivedCategory.{u, u, u} (A.restrict F)) (derivedExtension F A)
    (derivedExtensionCounit F A) (derivedRestriction F A)

/-- Derived restriction followed by the derived extension is the right derived functor of
restriction followed by the derived extension. -/
instance isRightDerivedFunctor_derivedRestriction_comp :
    (derivedRestriction F A ⋙ derivedExtension F A).IsRightDerivedFunctor
      (Functor.whiskerRight (derivedRestrictionFac F A).inv (derivedExtension F A) ≫
        (Functor.associator _ _ _).hom)
      (quasiIsomorphisms.{u, u, u} A) :=
  Functor.isRightDerivedFunctor_of_inverts _ _
    (asIso (Functor.whiskerRight (derivedRestrictionFac F A).inv (derivedExtension F A) ≫
      (Functor.associator _ _ _).hom)).symm

/-- **The derived extension is left adjoint to restriction** on the derived categories. -/
def derivedAdjunction : derivedExtension F A ⊣ derivedRestriction F A :=
  (homotopyAdjunction F A).derived (quasiIsomorphisms.{u, u, u} (A.restrict F))
    (quasiIsomorphisms.{u, u, u} A) (derivedExtensionCounit F A) (derivedRestrictionFac F A).inv

/-! ### Representing objects by good modules -/

omit [∀ U : C, IsCofiltered (StructuredArrow U F)] in
/-- A natural transformation invertible at an object is invertible at every isomorphic object. -/
theorem isIso_app_of_iso {𝒟 ℰ : Type*} [Category 𝒟] [Category ℰ] {G H : 𝒟 ⥤ ℰ} (τ : G ⟶ H)
    {X Y : 𝒟} (e : X ≅ Y) [IsIso (τ.app X)] : IsIso (τ.app Y) := by
  have h : τ.app Y = G.map e.inv ≫ τ.app X ≫ H.map e.hom := by
    rw [τ.naturality_assoc, ← H.map_comp, e.inv_hom_id, H.map_id, Category.comp_id]
  rw [h]
  infer_instance

omit [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
omit [∀ U : C, IsCofiltered (StructuredArrow U F)] in
/-- **Every object of `D(A, d)` is represented by a good module**, one whose sections are
orthogonal on the left to the acyclic modules. -/
theorem exists_good_iso {B : DifferentialGradedAlgebra.{u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)} (K : derivedCategory.{u, u, u} B) :
    ∃ P : DifferentialGradedModule.{u, u, u} B,
      (∀ U : Cᵒᵖ, (acyclic' (B.sectionAlgebra U)).leftOrthogonal
        ((toHomotopyCategory (B.sectionAlgebra U)).obj (P.sectionModule U))) ∧
      Nonempty ((toDerivedCategory.{u, u, u} B).obj ((HomotopyCategory.quotient B).obj P) ≅ K) := by
  obtain ⟨M, rfl⟩ := exists_toDerivedCategory_obj_eq B K
  obtain ⟨P, f, hf, -, -, hP⟩ := exists_flat_quasiIso_sectionwise (A := B) M
  have := isIso_toDerivedCategory_map_quotient_map f hf
  exact ⟨P, hP, ⟨asIso ((toDerivedCategory.{u, u, u} B).map ((HomotopyCategory.quotient B).map f))⟩⟩

omit [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
omit [∀ U : C, IsCofiltered (StructuredArrow U F)] in
/-- The class of a module lies in `QC(A, d)` exactly when the module satisfies the
quasi-coherence condition. -/
theorem qc_toDerivedCategory_iff {B : DifferentialGradedAlgebra.{u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)} (P : DifferentialGradedModule.{u, u, u} B) :
    Chaotic.QC B ((toDerivedCategory.{u, u, u} B).obj ((HomotopyCategory.quotient B).obj P)) ↔
      Chaotic.IsQCModule P :=
  (qc_iff_isQC_sectionDatum B _).trans (isQC_sectionDatum_iff P)

/-- A quasi-coherent object of `D(B, d)` is the class of a good quasi-coherent module. -/
private theorem exists_good_isQCModule_iso {B : DifferentialGradedAlgebra.{u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)} {K : derivedCategory.{u, u, u} B}
    (hK : Chaotic.QC B K) :
    ∃ P : DifferentialGradedModule.{u, u, u} B,
      (∀ U : Cᵒᵖ, (acyclic' (B.sectionAlgebra U)).leftOrthogonal
        ((toHomotopyCategory (B.sectionAlgebra U)).obj (P.sectionModule U))) ∧
      Chaotic.IsQCModule P ∧
      Nonempty ((toDerivedCategory.{u, u, u} B).obj ((HomotopyCategory.quotient B).obj P) ≅ K) := by
  obtain ⟨P, hP, ⟨e⟩⟩ := exists_good_iso K
  exact ⟨P, hP, (qc_toDerivedCategory_iff P).1 ((Chaotic.QC B).prop_of_iso e.symm hK), ⟨e⟩⟩

/-! ### The unit and the counit -/

/-- The unit of `homotopyAdjunction F A` at the class of a module is the class of the unit of
`moduleAdjunction F A`. -/
theorem homotopyAdjunction_unit_app (M : DifferentialGradedModule.{u, u, u} (A.restrict F)) :
    (homotopyAdjunction F A).unit.app ((HomotopyCategory.quotient (A.restrict F)).obj M) =
      (HomotopyCategory.quotient (A.restrict F)).map ((moduleAdjunction F A).unit.app M) :=
  rfl

/-- The counit of `homotopyAdjunction F A` at the class of a module is the class of the counit of
`moduleAdjunction F A`. -/
theorem homotopyAdjunction_counit_app (N : DifferentialGradedModule.{u, u, u} A) :
    (homotopyAdjunction F A).counit.app ((HomotopyCategory.quotient A).obj N) =
      (HomotopyCategory.quotient A).map ((moduleAdjunction F A).counit.app N) :=
  rfl

/-- **The unit of the derived adjunction is an isomorphism**, `F` being fully faithful. -/
theorem isIso_derivedAdjunction_unit_app [F.Full] [F.Faithful]
    (K : derivedCategory.{u, u, u} (A.restrict F)) :
    IsIso ((derivedAdjunction F A).unit.app K) := by
  obtain ⟨P, hP, ⟨e⟩⟩ := exists_good_iso K
  let X := (HomotopyCategory.quotient (A.restrict F)).obj P
  have := isIso_derivedExtensionCounit_app F A (X := X) hP
  have : IsIso ((toDerivedCategory.{u, u, u} (A.restrict F)).map
      ((homotopyAdjunction F A).unit.app X)) := by
    rw [homotopyAdjunction_unit_app]
    exact @Functor.map_isIso _ _ _ _ _ _ _ _ (@Functor.map_isIso _ _ _ _ _ _ _ _
      (isIso_moduleAdjunction_unit_app F A P))
  have : IsIso ((derivedAdjunction F A).unit.app
        ((toDerivedCategory.{u, u, u} (A.restrict F)).obj X)) :=
    IsIso.of_isIso_fac_right ((homotopyAdjunction F A).derivedη_fac_app
      (quasiIsomorphisms.{u, u, u} (A.restrict F)) (derivedExtensionCounit F A)
      (derivedRestrictionFac F A).inv X)
  exact isIso_app_of_iso ((derivedAdjunction F A).unit) e

/-- **The counit of the derived adjunction is an isomorphism at a quasi-coherent object.** -/
theorem isIso_derivedAdjunction_counit_app (K : derivedCategory.{u, u, u} A)
    (hK : Chaotic.QC A K) : IsIso ((derivedAdjunction F A).counit.app K) := by
  obtain ⟨N, hN, hqc, ⟨e⟩⟩ := exists_good_isQCModule_iso hK
  let X := (HomotopyCategory.quotient A).obj N
  have := isIso_derivedExtensionCounit_app F A
    (X := (homotopyRestriction F A).obj X) (restriction_isSectionGood F A hN)
  have : IsIso ((toDerivedCategory.{u, u, u} A).map ((homotopyAdjunction F A).counit.app X)) := by
    rw [homotopyAdjunction_counit_app]
    exact isIso_toDerivedCategory_map_quotient_map _
      (quasiIso_moduleAdjunction_counit_app F A N hN hqc)
  have : IsIso ((derivedAdjunction F A).counit.app ((toDerivedCategory.{u, u, u} A).obj X)) :=
    IsIso.of_isIso_fac_left ((homotopyAdjunction F A).derivedε_fac_app
      (quasiIsomorphisms.{u, u, u} A) (derivedExtensionCounit F A)
      (derivedRestrictionFac F A).inv X)
  exact isIso_app_of_iso ((derivedAdjunction F A).counit) e

/-! ### Quasi-coherence -/

/-- **Restriction preserves quasi-coherence.** -/
theorem qc_derivedRestriction (K : derivedCategory.{u, u, u} A) (hK : Chaotic.QC A K) :
    Chaotic.QC (A.restrict F) ((derivedRestriction F A).obj K) := by
  obtain ⟨N, hN, hqc, ⟨e⟩⟩ := exists_good_isQCModule_iso hK
  refine (Chaotic.QC (A.restrict F)).prop_of_iso ((derivedRestriction F A).mapIso e) ?_
  refine (Chaotic.QC (A.restrict F)).prop_of_iso ((derivedRestrictionFac F A).app _).symm ?_
  exact (qc_toDerivedCategory_iff ((restriction F A).obj N)).2 (isQCModule_restriction F A hN hqc)

/-- **The derived extension preserves quasi-coherence.** -/
theorem qc_derivedExtension (K : derivedCategory.{u, u, u} (A.restrict F))
    (hK : Chaotic.QC (A.restrict F) K) : Chaotic.QC A ((derivedExtension F A).obj K) := by
  obtain ⟨M, hM, hqc, ⟨e⟩⟩ := exists_good_isQCModule_iso hK
  refine (Chaotic.QC A).prop_of_iso ((derivedExtension F A).mapIso e) ?_
  have := isIso_derivedExtensionCounit_app F A
    (X := (HomotopyCategory.quotient (A.restrict F)).obj M) hM
  refine (Chaotic.QC A).prop_of_iso (asIso ((derivedExtensionCounit F A).app _)).symm ?_
  exact (qc_toDerivedCategory_iff ((extension F A).obj M)).2 (isQCModule_extension F A hM hqc)

/-! ### The equivalence -/

/-- **Restriction `QC(A, d) ⥤ QC(A', d)`.** -/
def qcRestriction :
    (Chaotic.QC A).FullSubcategory ⥤ (Chaotic.QC (A.restrict F)).FullSubcategory :=
  ObjectProperty.lift _ ((Chaotic.QC A).ι ⋙ derivedRestriction F A)
    fun K => qc_derivedRestriction F A K.obj K.property

/-- The derived extension `QC(A', d) ⥤ QC(A, d)`. -/
def qcExtension :
    (Chaotic.QC (A.restrict F)).FullSubcategory ⥤ (Chaotic.QC A).FullSubcategory :=
  ObjectProperty.lift _ ((Chaotic.QC (A.restrict F)).ι ⋙ derivedExtension F A)
    fun K => qc_derivedExtension F A K.obj K.property

/-- **The equivalence `QC(A, d) ≌ QC(A', d)`** given by restriction, with quasi-inverse the
derived extension. -/
def qcEquivalence [F.Full] [F.Faithful] :
    (Chaotic.QC A).FullSubcategory ≌ (Chaotic.QC (A.restrict F)).FullSubcategory :=
  CategoryTheory.Equivalence.mk (qcRestriction F A) (qcExtension F A)
    (NatIso.ofComponents (fun K => ObjectProperty.isoMk _
        (@asIso _ _ _ _ ((derivedAdjunction F A).counit.app K.obj)
          (isIso_derivedAdjunction_counit_app F A K.obj K.property)))
      fun f => by
        apply ObjectProperty.hom_ext
        exact (derivedAdjunction F A).counit.naturality ((Chaotic.QC A).ι.map f)).symm
    (NatIso.ofComponents (fun K => ObjectProperty.isoMk _
        (@asIso _ _ _ _ ((derivedAdjunction F A).unit.app K.obj)
          (isIso_derivedAdjunction_unit_app F A K.obj)))
      fun f => by
        apply ObjectProperty.hom_ext
        exact (derivedAdjunction F A).unit.naturality ((Chaotic.QC (A.restrict F)).ι.map f)).symm

end DifferentialGradedModule.ChaoticExtension

namespace DifferentialGradedModule.ChaoticExtension

section Subcategory

variable {C : Type u} [Category.{u} C] {Osharp : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u}}
  (A : DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp))
  (P : ObjectProperty C)

/-- *Let `C, O, A` be as in Section 0GZ8. Let `C' ⊂ C` be a full subcategory with the following
property: for every `U ∈ Ob(C)` the category `U/C'` of arrows `U → U'` is cofiltered. Denote
`O', A'` the restrictions of `O, A` to `C'`. Then restriction induces an equivalence
`QC(A, d) → QC(A', d)`.*

Here `C` carries the chaotic topology, `O` is a sheaf of commutative rings and `A` a sheaf of
differential graded `O`-algebras on it; the full subcategory `C'` is `P.FullSubcategory` for a
property `P` of objects, `U/C'` is `StructuredArrow U P.ι`, `O'` is
`SheafOfModules.restrictRingSheaf P.ι O` and `A'` is `A.restrict P.ι`. `QC(A, d)` is the full
subcategory `Chaotic.QC A` of `D(A, d)` of Definition 0GZ9, and the functor is restriction
`D(A, d) ⥤ D(A', d)`, the functor induced by restriction of differential graded modules, which is
exact. That functor is the literal restriction up to the canonical isomorphism
`restriction_sectionModuleIso : (M|_{C'})(U') ≅ M(F U')` (read over `A'(U') = A(F U')`), natural
in `M` by `restriction_sectionModuleIso_naturality`. -/
@[stacks 0GZE]
theorem isEquivalence_qcRestriction [∀ U : C, IsCofiltered (StructuredArrow U P.ι)] :
    (qcRestriction P.ι A).IsEquivalence :=
  (qcEquivalence P.ι A).isEquivalence_functor

end Subcategory

end DifferentialGradedModule.ChaoticExtension

end SheafOfModules

end
