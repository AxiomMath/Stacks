module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticRestrictionQuasiCoherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedQuasiIsoDerivedEquivalence

/-!
# `QC(A, d) ≃ QC(B, d)` for a quasi-isomorphism of sheaves of differential graded algebras

Let `C` be a category with the chaotic topology, `O` a sheaf of commutative rings on it and
`φ : A ⟶ B` a homomorphism of sheaves of differential graded `O`-algebras which induces an
isomorphism on cohomology sheaves. By Tag 0FTZ derived extension of scalars
`D(A, d) ⥤ D(B, d)`, `M ↦ M ⊗^𝐋_A B`, is an equivalence, with derived restriction of scalars as
quasi-inverse. Tag 0GZF says that this equivalence carries `QC(A, d)` of Tag 0GZ9 onto
`QC(B, d)`, and so induces an equivalence `QC(A, d) ≌ QC(B, d)`.

The source reduces the lemma to the fact that `A(U) ⟶ B(U)` is a quasi-isomorphism of
differential graded algebras for every object `U`. The argument here runs through the
quasi-inverse rather than through the functor itself: restriction of scalars does not change the
underlying complexes, so the sections of the restriction `N_A` of a module `N` are the
restriction of the sections of `N`, and its restriction maps are those of `N`
(`SheafOfModules.DifferentialGradedModule.isQCModule_restrictionObj_iff`). Derived restriction
of scalars along the quasi-isomorphisms `A(U) ⟶ B(U)` is an equivalence by Tag 09S6, which turns
the comparison maps of `N_A` into those of `N`; so derived restriction preserves and reflects
quasi-coherence (`SheafOfModules.DifferentialGradedModule.Chaotic.qc_derivedRestriction_iff`),
and through the unit of the adjoint equivalence of Tag 0FTZ so does derived extension.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.Chaotic.qcDerivedExtension`: the functor
  `QC(A, d) ⥤ QC(B, d)` induced by derived extension of scalars.
* `SheafOfModules.DifferentialGradedModule.Chaotic.qcDerivedExtensionEquivalence`: the
  equivalence `QC(A, d) ≌ QC(B, d)`, with the functor induced by derived restriction of scalars
  as quasi-inverse.

## Main results

* `SheafOfModules.DifferentialGradedModule.Chaotic.qc_derivedExtension_iff`: derived extension
  of scalars preserves and reflects quasi-coherence.
* `SheafOfModules.DifferentialGradedModule.Chaotic.qcDerivedExtension_comp_ι`: the induced
  functor lies over derived extension of scalars.
* `SheafOfModules.DifferentialGradedModule.Chaotic.isEquivalence_qcDerivedExtension`: the
  induced functor is an equivalence.
* `SheafOfModules.DifferentialGradedModule.Chaotic.qc_derivedExtension_iff_and_isEquivalence`:
  **Tag 0GZF**, the three statements together.

## Implementation notes

The homomorphism `φ` is unit-preserving (`hφ`): homomorphisms of algebras preserve the unit in
the conventions of the source, and Tag 0FTZ is stated for such homomorphisms. "Induces an
isomorphism on cohomology sheaves" is `SheafOfModules.DifferentialGradedAlgebra.Hom.IsQuasiIso`,
the hypothesis of Tag 0FTZ: the underlying map of complexes of sheaves of `O`-modules is a
quasi-isomorphism. The site, the sheaf of rings and the differential graded algebras live in one
universe `u`, the setting of Tag 0FTZ.

## References

* [Stacks Project, Lemma 24.34.2 (Tag 0GZF)](https://stacks.math.columbia.edu/tag/0GZF)
* [Stacks Project, Definition 24.33.1 (Tag 0GZ9)](https://stacks.math.columbia.edu/tag/0GZ9)
* [Stacks Project, Lemma 24.30.1 (Tag 0FTZ)](https://stacks.math.columbia.edu/tag/0FTZ)
* [Stacks Project, Lemma 22.35.6 (Tag 09S6)](https://stacks.math.columbia.edu/tag/09S6)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace SheafOfModules.DifferentialGradedModule.Chaotic

attribute [local instance] Stacks.SheafOfModules.botWEqualsLocallyBijective

variable {C : Type u} [Category.{u} C] {O : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u}}
  {A B : DifferentialGradedAlgebra.{u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (chaoticRingedSite O).O)}
  (φ : A ⟶ B) (hφ : φ.PreservesOne) (hqis : φ.IsQuasiIso)

include hqis

/-- Derived extension of scalars along a homomorphism of sheaves of
differential graded `O`-algebras which induces an isomorphism on cohomology sheaves preserves and
reflects quasi-coherence: an object `M` of `D(A, d)` lies in `QC(A, d)` exactly when
`M ⊗^𝐋_A B` lies in `QC(B, d)`. -/
theorem qc_derivedExtension_iff (M : derivedCategory.{u, u, u} A) :
    QC B ((derivedExtension φ hφ).obj M) ↔ QC A M := by
  have := isIso_derivedExtensionAdjunction_unit_app φ hφ hqis M
  rw [← qc_derivedRestriction_iff φ hφ hqis]
  exact ((QC A).prop_iff_of_iso (asIso ((derivedExtensionAdjunction φ hφ).unit.app M))).symm

/-- Derived restriction of scalars along a quasi-isomorphism carries `QC(B, d)` into
`QC(A, d)`. -/
theorem qc_derivedRestriction {X : derivedCategory.{u, u, u} B} (hX : QC B X) :
    QC A ((derivedRestriction.{u, u, u} φ hφ).obj X) :=
  (qc_derivedRestriction_iff φ hφ hqis X).2 hX

/-- **The functor `QC(A, d) ⥤ QC(B, d)` induced by derived extension of scalars.** -/
def qcDerivedExtension : QCFullSubcategory A ⥤ QCFullSubcategory B :=
  ObjectProperty.lift _ (QCι A ⋙ derivedExtension φ hφ)
    fun M ↦ (qc_derivedExtension_iff φ hφ hqis M.obj).2 M.property

/-- The functor `QC(B, d) ⥤ QC(A, d)` induced by derived restriction of scalars. -/
def qcDerivedRestriction : QCFullSubcategory B ⥤ QCFullSubcategory A :=
  ObjectProperty.lift _ (QCι B ⋙ derivedRestriction.{u, u, u} φ hφ)
    fun X ↦ qc_derivedRestriction φ hφ hqis X.property

/-- The induced functor lies over derived extension of scalars: composing it
with the inclusion of `QC(B, d)` into `D(B, d)` is the inclusion of `QC(A, d)` into `D(A, d)`
followed by derived extension of scalars. This is the sense in which the equivalence of
Tag 0FTZ *induces* the functor on quasi-coherent objects. -/
theorem qcDerivedExtension_comp_ι :
    qcDerivedExtension φ hφ hqis ⋙ QCι B = QCι A ⋙ derivedExtension φ hφ :=
  rfl

/-- **The equivalence `QC(A, d) ≌ QC(B, d)`** induced by the equivalence of Tag 0FTZ: derived
extension of scalars, with derived restriction of scalars as quasi-inverse. -/
def qcDerivedExtensionEquivalence : QCFullSubcategory A ≌ QCFullSubcategory B :=
  (derivedExtensionEquivalence φ hφ hqis).congrFullSubcategory
    (funext fun M ↦ propext (qc_derivedExtension_iff φ hφ hqis M))

/-- The functor of `qcDerivedExtensionEquivalence` is the functor induced by derived extension
of scalars. -/
theorem qcDerivedExtensionEquivalence_functor :
    (qcDerivedExtensionEquivalence φ hφ hqis).functor = qcDerivedExtension φ hφ hqis :=
  rfl

/-- The quasi-inverse of `qcDerivedExtensionEquivalence` is the functor induced by derived
restriction of scalars. -/
theorem qcDerivedExtensionEquivalence_inverse :
    (qcDerivedExtensionEquivalence φ hφ hqis).inverse = qcDerivedRestriction φ hφ hqis :=
  rfl

/-- The functor `QC(A, d) ⥤ QC(B, d)` induced by derived extension of scalars along a
quasi-isomorphism is an equivalence. -/
theorem isEquivalence_qcDerivedExtension : (qcDerivedExtension φ hφ hqis).IsEquivalence := by
  have := isEquivalence_derivedExtension φ hφ hqis
  have : (qcDerivedExtension φ hφ hqis).Faithful :=
    (qcDerivedExtension_comp_ι φ hφ hqis).faithful_of_comp
  have : (qcDerivedExtension φ hφ hqis).Full :=
    Functor.Full.of_comp_faithful_iso (eqToIso (qcDerivedExtension_comp_ι φ hφ hqis)) (G := QCι B)
  have : (qcDerivedExtension φ hφ hqis).EssSurj := by
    refine ⟨fun N ↦ ⟨⟨(derivedRestriction.{u, u, u} φ hφ).obj N.obj,
      qc_derivedRestriction φ hφ hqis N.property⟩, ⟨(QCι B).preimageIso ?_⟩⟩⟩
    exact @asIso _ _ _ _ ((derivedExtensionAdjunction φ hφ).counit.app N.obj)
      (isIso_derivedExtensionAdjunction_counit_app φ hφ hqis N.obj)
  exact { }

/-- **Stacks 0GZF.** Let `C` be a category with the chaotic topology, `O` a sheaf of rings on it
and `φ : A ⟶ B` a homomorphism of sheaves of differential graded `O`-algebras which induces an
isomorphism on cohomology sheaves. Then the equivalence `D(A, d) ⥤ D(B, d)`, `M ↦ M ⊗^𝐋_A B`, of
Tag 0FTZ induces an equivalence `QC(A, d) ⥤ QC(B, d)`.

The three conjuncts are: an object `M` of `D(A, d)` lies in `QC(A, d)` exactly when `M ⊗^𝐋_A B`
lies in `QC(B, d)`, so that the functor induces a functor `QC(A, d) ⥤ QC(B, d)`; that functor
lies over derived extension of scalars; and it is an equivalence.

The source's functor `M ↦ M ⊗^𝐋_A B` is defined only for a homomorphism `φ` preserving `1`,
since `B` is made a left `A`-module through `φ`; so `PreservesOne` is implicit in the
statement. -/
@[stacks 0GZF]
theorem qc_derivedExtension_iff_and_isEquivalence :
    (∀ M : derivedCategory.{u, u, u} A, QC B ((derivedExtension φ hφ).obj M) ↔ QC A M) ∧
      qcDerivedExtension φ hφ hqis ⋙ QCι B = QCι A ⋙ derivedExtension φ hφ ∧
      (qcDerivedExtension φ hφ hqis).IsEquivalence :=
  ⟨qc_derivedExtension_iff φ hφ hqis, qcDerivedExtension_comp_ι φ hφ hqis,
    isEquivalence_qcDerivedExtension φ hφ hqis⟩

end SheafOfModules.DifferentialGradedModule.Chaotic

end
