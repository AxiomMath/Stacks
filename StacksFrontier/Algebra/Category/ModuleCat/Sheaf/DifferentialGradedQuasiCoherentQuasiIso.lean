module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedQuasiCoherent
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedEquivalenceQuasiIso
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorHomAdjunction

/-!
# Quasi-coherence and a quasi-isomorphism, for carried section data

Let `C` be a category with the chaotic topology, `O` a sheaf of rings on it and
`φ : A ⟶ B` a homomorphism of sheaves of differential graded `O`-algebras which is a
quasi-isomorphism on sections. This file proves, for the *carried* section data of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedQuasiCoherent.lean`, the
equivalence of the two conditions to which the source reduces Lemma 24.34.2:

1. `RΓ(V, M) ⊗^𝐋_{A(V)} A(U) ⟶ RΓ(U, M)` is an isomorphism of `D(A(U), d)`, and
2. `RΓ(V, M ⊗^𝐋_A B) ⊗^𝐋_{B(V)} B(U) ⟶ RΓ(U, M ⊗^𝐋_A B)` is an isomorphism of `D(B(U), d)`.

The implication (1) ⟹ (2) is `isQC_derivedPullback` for the identity functor of `C`; the
implication (2) ⟹ (1) writes the comparison map of (2) as the comparison map of (1) pushed along
base change `- ⊗^𝐋_{A(U)} B(U)` and conjugated by isomorphisms, and base change along a
quasi-isomorphism of differential graded algebras is an equivalence by Tag 09S6, hence reflects
isomorphisms. The functor of derived categories is the one carried by a
`SheafOfModules.DifferentialGradedModule.DerivedTensorData`, and the computation of its derived
sections a `SheafOfModules.DifferentialGradedModule.DerivedPullbackSectionData`.

Tag 0GZF itself, for the derived extension of scalars of Tag 0FTZ and the subcategories
`QC(A, d)` of Tag 0GZ9, is
`SheafOfModules.DifferentialGradedModule.Chaotic.isEquivalence_qcDerivedExtension` of
the file `DifferentialGradedChaoticQuasiCoherentQuasiIso.lean` in the directory
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/`.

## Main results

* `SheafOfModules.DifferentialGradedModule.sectionComparison_naturality`: the comparison map
  `RΓ(V, -) ⊗^𝐋_{A(V)} A(U) ⟶ RΓ(U, -)` is natural, so quasi-coherence is invariant under
  isomorphism (`isQC_of_iso`).
* `SheafOfModules.DifferentialGradedModule.isEquivalence_baseChange_of_bijective_cohomologyMap`:
  base change along a structure homomorphism which is a quasi-isomorphism is an equivalence of
  derived categories. This is Tag 09S6 for the section algebras.
* `SheafOfModules.DifferentialGradedModule.isQC_derivedPullback_iff`: conditions (1) and (2)
  above are equivalent.
* `SheafOfModules.DifferentialGradedModule.qcPullback_comp_QCι`: the induced functor on
  quasi-coherent objects lies over the functor `D(A, d) ⥤ D(B, d)`.
* `SheafOfModules.DifferentialGradedModule.isEquivalence_qcPullback_of_bijective_cohomologyMap`:
  if the carried functor `D(A, d) ⥤ D(B, d)` is an equivalence, so is the induced functor on
  quasi-coherent objects.

## Implementation notes

UNIVERSES. The two sheaves of differential graded algebras live over possibly different sheaves
of rings on the one site `C`, with independent universes for their algebra and module components,
for the two derived categories, and for the coefficient ring of the section algebras, as in
`DifferentialGradedQuasiCoherent`.

## References

* [Stacks Project, Lemma 24.34.2 (Tag 0GZF)](https://stacks.math.columbia.edu/tag/0GZF)
* [Stacks Project, Definition 24.33.1 (Tag 0GZ9)](https://stacks.math.columbia.edu/tag/0GZ9)
* [Stacks Project, Lemma 24.33.4 (Tag 0GZC)](https://stacks.math.columbia.edu/tag/0GZC)
* [Stacks Project, Lemma 22.35.6 (Tag 09S6)](https://stacks.math.columbia.edu/tag/09S6)
-/

@[expose] public noncomputable section

open CategoryTheory

universe s t a m v u t' a' m' d e d' e'

namespace SheafOfModules.DifferentialGradedModule

/-! ### Naturality of the comparison map, and invariance of quasi-coherence -/

section Naturality

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {Λ : Type s} [CommRing Λ] {A : DifferentialGradedAlgebra.{t, a} R} {D : Type d}
  [Category.{e} D] {gA : GoodModuleData.{t, a, m, v, u, d, e} A D}

/-- The canonical map `RΓ(V, M) ⊗^𝐋_{A(V)} A(U) ⟶ RΓ(U, M)` of a morphism `a : V ⟶ U` of `Cᵒᵖ`
is natural in `M`: it is the adjoint transpose of a natural transformation. -/
theorem sectionComparison_naturality (sd : SectionData Λ gA) {U V : Cᵒᵖ} (a : V ⟶ U) {M N : D}
    (f : M ⟶ N) :
    (sd.baseChange a).map ((sd.derivedSections V).map f) ≫ sectionComparison sd a N =
      sectionComparison sd a M ≫ (sd.derivedSections U).map f := by
  rw [sectionComparison, sectionComparison, ← Adjunction.homEquiv_naturality_left_symm,
    ← Adjunction.homEquiv_naturality_right_symm]
  exact congrArg _ ((sd.restrictionMap a).naturality f)

/-- Quasi-coherence is invariant under isomorphism in `D(A, d)`. -/
theorem isQC_of_iso (sd : SectionData Λ gA) {M N : D} (e : M ≅ N) (h : IsQC sd M) : IsQC sd N := by
  intro U V a
  have : IsIso (sectionComparison sd a M) := h a
  have : IsIso ((sd.baseChange a).map ((sd.derivedSections V).map e.hom) ≫
      sectionComparison sd a N) := by
    rw [sectionComparison_naturality sd a e.hom]; infer_instance
  exact IsIso.of_isIso_comp_left ((sd.baseChange a).map ((sd.derivedSections V).map e.hom)) _

end Naturality

/-! ### Base change along a quasi-isomorphism of section algebras -/

section QuasiIso

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {R' : Sheaf J RingCat.{t'}} {Λ : Type s} [CommRing Λ]
  {A : DifferentialGradedAlgebra.{t, a} R} {B : DifferentialGradedAlgebra.{t', a'} R'}
  {D : Type d} [Category.{e} D] {D' : Type d'} [Category.{e'} D']
  {gA : GoodModuleData.{t, a, m, v, u, d, e} A D}
  {gB : GoodModuleData.{t', a', m', v, u, d', e'} B D'}
  {sd : SectionData Λ gA} {sd' : SectionData Λ gB}
  {msd : MorphismSectionData (𝟭 C) sd sd'} {Lg : DerivedTensorData gA gB}

/-- **Stacks 09S6 for the section algebras.** If the structure homomorphism `A(U) ⟶ B(U)` of a
morphism section datum induces an isomorphism on cohomology, then the derived base change
`- ⊗^𝐋_{A(U)} B(U) : D(A(U), d) ⥤ D(B(U), d)` it carries is an equivalence of categories.

The base change is pinned by its adjunction to derived restriction of scalars, so it is
canonically isomorphic to derived tensoring with the regular bimodule of the structure
homomorphism, which is the functor Tag 09S6 proves to be an equivalence. -/
theorem isEquivalence_baseChange_of_bijective_cohomologyMap (U : Cᵒᵖ)
    (h : ∀ k : ℤ, Function.Bijective ((msd.structureHom U).cohomologyMap k)) :
    (msd.baseChange U).IsEquivalence :=
  have := DifferentialGraded.Bimodule.isEquivalence_derivedTensorFunctor_regular
    (msd.structureHom U) h
  Functor.isEquivalence_of_iso
    ((DifferentialGraded.Bimodule.derivedTensorFunctor_adj_derivedRestriction
      (msd.structureHom U)).leftAdjointUniq (msd.adj U))

/-- **Condition (2) implies condition (1).** If the structure homomorphisms are
quasi-isomorphisms, then the derived functor `D(A, d) ⥤ D(B, d)` *reflects* quasi-coherence.

The comparison map of `Lg^*K` over a morphism `a` of `Cᵒᵖ` is, by
`sectionComparison_derivedPullback`, the comparison map of `K` over `a` pushed along the base
change at the target and conjugated by three isomorphisms; so its invertibility makes the pushed
map invertible, and base change reflects isomorphisms because it is an equivalence. -/
theorem isQC_of_isQC_derived (dp : DerivedPullbackSectionData msd Lg)
    (h : ∀ (U : Cᵒᵖ) (k : ℤ), Function.Bijective ((msd.structureHom U).cohomologyMap k))
    (K : D) (hK : IsQC sd' (Lg.derived.obj K)) : IsQC sd K := by
  intro U V a
  have := isEquivalence_baseChange_of_bijective_cohomologyMap (msd := msd) U (h U)
  have h' := hK a
  rw [sectionComparison_derivedPullback dp a K] at h'
  have : IsIso ((msd.baseChange U).map (sectionComparison sd ((𝟭 C).op.map a) K)) := by
    simpa using h'
  exact isIso_of_reflects_iso (sectionComparison sd ((𝟭 C).op.map a) K) (msd.baseChange U)

/-- **The equivalence of conditions (1) and (2) to which the source reduces Tag 0GZF.** For a
homomorphism of sheaves of differential graded algebras which is a quasi-isomorphism on sections,
an object `K` of `D(A, d)` is quasi-coherent exactly when `K ⊗^𝐋_A B` is. -/
theorem isQC_derivedPullback_iff (dp : DerivedPullbackSectionData msd Lg)
    (h : ∀ (U : Cᵒᵖ) (k : ℤ), Function.Bijective ((msd.structureHom U).cohomologyMap k))
    (K : D) : IsQC sd' (Lg.derived.obj K) ↔ IsQC sd K :=
  ⟨isQC_of_isQC_derived dp h K, isQC_derivedPullback dp K⟩

/-- **The induced functor lies over the functor of derived categories.** Composing
`qcPullback dp` with the inclusion of `QC(B, d)` into `D(B, d)` is the inclusion of `QC(A, d)`
into `D(A, d)` followed by `D(A, d) ⥤ D(B, d)`. This is the sense in which the equivalence of
Tag 0FTZ *induces* the functor of Tag 0GZF below. -/
theorem qcPullback_comp_QCι (dp : DerivedPullbackSectionData msd Lg) :
    qcPullback dp ⋙ QCι sd' = QCι sd ⋙ Lg.derived := rfl

/-- **The functor induced on carried quasi-coherent objects is an equivalence** as soon as the
carried functor `D(A, d) ⥤ D(B, d)` is one and the structure homomorphisms are
quasi-isomorphisms. It is fully faithful because the functor of derived categories is and the
quasi-coherent objects form a full subcategory, and essentially surjective because an object of
`D(A, d)` whose image is quasi-coherent is itself quasi-coherent (`isQC_of_isQC_derived`). -/
theorem isEquivalence_qcPullback_of_bijective_cohomologyMap
    (dp : DerivedPullbackSectionData msd Lg)
    (h : ∀ (U : Cᵒᵖ) (k : ℤ), Function.Bijective ((msd.structureHom U).cohomologyMap k))
    (hLg : Lg.derived.IsEquivalence) : (qcPullback dp).IsEquivalence := by
  have := hLg
  have hc : (qcPullback dp ⋙ QCι sd').Faithful := by
    change (QCι sd ⋙ Lg.derived).Faithful; infer_instance
  have : (qcPullback dp).Faithful := Functor.Faithful.of_comp _ (QCι sd')
  have : (qcPullback dp ⋙ QCι sd').Full := by
    change (QCι sd ⋙ Lg.derived).Full; infer_instance
  have : (qcPullback dp).Full := Functor.Full.of_comp_faithful _ (QCι sd')
  have : (qcPullback dp).EssSurj := by
    refine ⟨fun N ↦ ?_⟩
    refine ⟨⟨Lg.derived.objPreimage N.obj, ?_⟩, ⟨?_⟩⟩
    · exact (isQC_derivedPullback_iff dp h _).1
        (isQC_of_iso sd' (Lg.derived.objObjPreimageIso N.obj).symm N.property)
    · exact (QCι sd').preimageIso (Lg.derived.objObjPreimageIso N.obj)
  exact { }

end QuasiIso

end SheafOfModules.DifferentialGradedModule

end
