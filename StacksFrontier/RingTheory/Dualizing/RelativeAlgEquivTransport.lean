module

public import StacksFrontier.Homology.PseudoCoherent.Basic
public import StacksFrontier.Homology.TorAmplitude.DerivedComparison
public import StacksFrontier.RingTheory.Dualizing.MapDerivedCategory
public import StacksFrontier.RingTheory.Dualizing.RelativeBaseChange
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingDiagonal

/-!
# Transporting a relative dualizing complex along an isomorphism of algebras

Let `e : B ≃ₐ[R] C` be an isomorphism of `R`-algebras, both flat and of finite presentation over
`R`.  Restriction of scalars along `e.symm` is an equivalence `ModuleCat B ≌ ModuleCat C`, and it
carries a relative dualizing complex for `R → B` to one for `R → C`.  This file proves that, at
the transported complex rather than merely as an existence statement, which is what
[stacks 0E2F] (1) needs at the last step of its reduction to the Noetherian case: the Noetherian
stage produces a relative dualizing complex for `R → A₁ ⊗_{R₁} R`, and `A₁ ⊗_{R₁} R ≅ A`.

It is also what the Noetherian case of clause (2) needs in
`StacksFrontier.RingTheory.Dualizing.RelativeBaseChangeNoetherian`, where [stacks 0BZV] lands on
`R' ⊗_R A` and the clause is stated on `A ⊗_R R'`.

## Main results

* `Dualizing.RelativeExistence.isRelativeDualizingComplex_of_algEquiv` — **the transport**.

## The proof

Relative perfection transports because pseudo-coherence does and because the restriction to `R`
of the transported complex is the restriction of the original one.  The diagonal condition of
[stacks 0E2C] transports because `e` induces an isomorphism `Algebra.TensorProduct.congr e e` of
the two diagonals, compatibly with both multiplication maps and with both left coprojections;
those two compatibilities are the private isomorphisms below, each proved by uniqueness of
adjoints from the single comparison for restriction of scalars.

## References

* [Stacks Project, Tag 0E2C](https://stacks.math.columbia.edu/tag/0E2C)
* [Stacks Project, Tag 0E2F](https://stacks.math.columbia.edu/tag/0E2F)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct
open CochainComplex.DerivedExtensionScalars

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

namespace RelativeExistence

private noncomputable def derivedHomTransportIso
    {R B C : Type u} [CommRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] (e : B ≃ₐ[R] C) :
    derivedHom.{u, u}
        (Algebra.TensorProduct.lmul' R : B ⊗[R] B →ₐ[R] B).toRingHom ⋙
        (ModuleCat.restrictScalars e.symm.toRingEquiv.toRingHom).mapDerivedCategory ≅
    (ModuleCat.restrictScalars
        (Algebra.TensorProduct.congr e e).symm.toRingEquiv.toRingHom).mapDerivedCategory ⋙
      derivedHom.{u, u}
        (Algebra.TensorProduct.lmul' R : C ⊗[R] C →ₐ[R] C).toRingHom := by
  let μB : B ⊗[R] B →+* B :=
    (Algebra.TensorProduct.lmul' R : B ⊗[R] B →ₐ[R] B).toRingHom
  let μC : C ⊗[R] C →+* C :=
    (Algebra.TensorProduct.lmul' R : C ⊗[R] C →ₐ[R] C).toRingHom
  let d := Algebra.TensorProduct.congr e e
  let Ue : ModuleCat.{u} C ⥤ ModuleCat.{u} B :=
    ModuleCat.restrictScalars.{u} e.toRingEquiv.toRingHom
  let Uδ : ModuleCat.{u} (C ⊗[R] C) ⥤ ModuleCat.{u} (B ⊗[R] B) :=
    ModuleCat.restrictScalars.{u} d.toRingEquiv.toRingHom
  let UμB : ModuleCat.{u} B ⥤ ModuleCat.{u} (B ⊗[R] B) :=
    ModuleCat.restrictScalars.{u} μB
  let UμC : ModuleCat.{u} C ⥤ ModuleCat.{u} (C ⊗[R] C) :=
    ModuleCat.restrictScalars.{u} μC
  let f₁ := e.toRingEquiv.toRingHom.comp μB
  let f₂ := μC.comp d.toRingEquiv.toRingHom
  have hf : f₁ = f₂ := by
    refine RingHom.ext fun z => ?_
    induction z using TensorProduct.inductionOn with
    | tmul b₁ b₂ =>
        change e (b₁ * b₂) = e b₁ * e b₂
        exact map_mul e b₁ b₂
    | add x y hx hy => simp [hx, hy]
  let α₁ := ModuleCat.restrictScalarsComp' μB e.toRingEquiv.toRingHom f₁ rfl
  let α₂ := ModuleCat.restrictScalarsComp' d.toRingEquiv.toRingHom μC f₂ rfl
  let η := α₁.symm ≪≫ ModuleCat.restrictScalarsCongr hf ≪≫ α₂
  let leftIso :=
    mapDerivedCategoryCompNatIso Ue UμB (Ue ⋙ UμB) (Iso.refl _) ≪≫
      mapDerivedCategoryNatIso (Ue ⋙ UμB) (UμC ⋙ Uδ) η ≪≫
      (mapDerivedCategoryCompNatIso UμC Uδ (UμC ⋙ Uδ) (Iso.refl _)).symm
  let E := ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.toRingEquiv
  let Eδ := ModuleCat.restrictScalarsEquivalenceOfRingEquiv d.toRingEquiv
  let adj₁ := (CategoryTheory.Adjunction.mapDerivedCategory E.toAdjunction).comp
    (Classical.choice (restrictScalarsDerived_adj_derivedHom.{u, u} μB))
  let adj₂ := (Classical.choice
      (restrictScalarsDerived_adj_derivedHom.{u, u} μC)).comp
    (CategoryTheory.Adjunction.mapDerivedCategory Eδ.toAdjunction)
  exact Adjunction.rightAdjointUniq (adj₁.ofNatIsoLeft leftIso) adj₂

/-- **The left coprojection transports along an isomorphism of algebras.**  For `e : B ≃ₐ[R] C`,
restriction along `(e ⊗ e)⁻¹` of `K ⊗ᴸ_B (B ⊗_R B)` is `K_C ⊗ᴸ_C (C ⊗_R C)`, where `K_C` is `K`
restricted along `e⁻¹`. -/
noncomputable def diagonalExtensionTransportIso
    {R B C : Type u} [CommRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] [Module.Flat R B] [Module.Flat R C]
    (e : B ≃ₐ[R] C) (K : DerivedCategory (ModuleCat.{u} B)) :
    (ModuleCat.restrictScalars.{u}
        (Algebra.TensorProduct.congr e e).symm.toRingEquiv.toRingHom).mapDerivedCategory.obj
      ((diagonalDerivedExtension R B).obj K) ≅
    (diagonalDerivedExtension R C).obj
      ((ModuleCat.restrictScalars.{u} e.symm.toRingEquiv.toRingHom).mapDerivedCategory.obj K) := by
  let B₂ := B ⊗[R] B
  let C₂ := C ⊗[R] C
  let d := Algebra.TensorProduct.congr e e
  let iB : B →+* B₂ := Algebra.TensorProduct.includeLeftRingHom
  let iC : C →+* C₂ := Algebra.TensorProduct.includeLeftRingHom
  let F : ModuleCat.{u} B ⥤ ModuleCat.{u} C :=
    ModuleCat.restrictScalars.{u} e.symm.toRingEquiv.toRingHom
  let F₂ : ModuleCat.{u} B₂ ⥤ ModuleCat.{u} C₂ :=
    ModuleCat.restrictScalars.{u} d.symm.toRingHom
  let L : ModuleCat.{u} B ⥤ ModuleCat.{u} B₂ :=
    ModuleCat.extendScalars.{u, u, u} iB
  let L' : ModuleCat.{u} C ⥤ ModuleCat.{u} C₂ :=
    ModuleCat.extendScalars.{u, u, u} iC
  letI : Limits.PreservesFiniteLimits L :=
    extendScalars_preservesFiniteLimits_of_flat' iB
      (includeLeftRingHom_flat R B)
  letI : Limits.PreservesColimitsOfSize.{0, 0} L :=
    (ModuleCat.extendRestrictScalarsAdj iB).leftAdjoint_preservesColimits
  letI : Limits.PreservesFiniteColimits L :=
    Limits.PreservesColimitsOfSize.preservesFiniteColimits L
  letI : L.Additive := Functor.additive_of_preserves_binary_products L
  letI : Limits.PreservesFiniteLimits L' :=
    extendScalars_preservesFiniteLimits_of_flat' iC
      (includeLeftRingHom_flat R C)
  letI : Limits.PreservesColimitsOfSize.{0, 0} L' :=
    (ModuleCat.extendRestrictScalarsAdj iC).leftAdjoint_preservesColimits
  letI : Limits.PreservesFiniteColimits L' :=
    Limits.PreservesColimitsOfSize.preservesFiniteColimits L'
  letI : L'.Additive := Functor.additive_of_preserves_binary_products L'
  let E := ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.toRingEquiv
  let E₂ := ModuleCat.restrictScalarsEquivalenceOfRingEquiv d.toRingEquiv
  let extE : ModuleCat.extendScalars.{u, u, u} e.toRingEquiv.toRingHom ≅ F :=
    Adjunction.leftAdjointUniq (ModuleCat.extendRestrictScalarsAdj e.toRingEquiv.toRingHom)
      E.symm.toAdjunction
  let extE₂ : ModuleCat.extendScalars.{u, u, u} d.toRingEquiv.toRingHom ≅ F₂ :=
    Adjunction.leftAdjointUniq (ModuleCat.extendRestrictScalarsAdj d.toRingEquiv.toRingHom)
      E₂.symm.toAdjunction
  have hcomp : d.toRingEquiv.toRingHom.comp iB = iC.comp e.toRingEquiv.toRingHom := by
    ext b
    change (e b) ⊗ₜ[R] e 1 = (e b) ⊗ₜ[R] (1 : C)
    rw [map_one]
  let η : L ⋙ F₂ ≅ F ⋙ L' :=
    Functor.isoWhiskerLeft L extE₂.symm ≪≫
      (ModuleCat.extendScalarsComp iB d.toRingEquiv.toRingHom).symm ≪≫
      eqToIso (congrArg (fun f => ModuleCat.extendScalars.{u, u, u} f) hcomp) ≪≫
      ModuleCat.extendScalarsComp e.toRingEquiv.toRingHom iC ≪≫
      Functor.isoWhiskerRight extE L'
  let ηD :=
    mapDerivedCategoryCompNatIso L F₂ (L ⋙ F₂) (Iso.refl _) ≪≫
      mapDerivedCategoryNatIso (L ⋙ F₂) (F ⋙ L') η ≪≫
      (mapDerivedCategoryCompNatIso F L' (F ⋙ L') (Iso.refl _)).symm
  exact ηD.app K

/-- **Being a relative dualizing complex transports along an isomorphism of `R`-algebras, at the
transported complex.**  For `e : B ≃ₐ[R] C` the equivalence `ModuleCat B ≌ ModuleCat C` given by
restriction of scalars along `e.symm` carries a relative dualizing complex for `R → B` to one for
`R → C`.

Relative perfection transports because pseudo-coherence does
(`StacksDraft.PseudoCoherence.pseudoCoherent_iff_of_ringEquiv`) and because the restriction to `R`
of the transported complex is the restriction of the original one, the two structure maps being
compatible with `e`.  The diagonal condition transports because `e` induces an isomorphism
`Algebra.TensorProduct.congr e e` of the two diagonals, compatibly with both multiplication maps
and both left coprojections; those two compatibilities are the private isomorphisms of this
section. -/
theorem isRelativeDualizingComplex_of_algEquiv
    {R B C : Type u} [CommRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] [Module.Flat R B] [Module.Flat R C]
    [Algebra.FinitePresentation R B] [Algebra.FinitePresentation R C]
    (e : B ≃ₐ[R] C) (K : DerivedCategory (ModuleCat.{u} B))
    (hK : Dualizing.IsRelativeDualizingComplex R B K) :
    Dualizing.IsRelativeDualizingComplex R C
      ((ModuleCat.restrictScalars.{u}
        e.symm.toRingEquiv.toRingHom).mapDerivedCategory.obj K) := by
  let F : ModuleCat.{u} B ⥤ ModuleCat.{u} C :=
    ModuleCat.restrictScalars e.symm.toRingEquiv.toRingHom
  let K' := F.mapDerivedCategory.obj K
  let : F.IsEquivalence :=
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.symm.toRingEquiv).isEquivalence_functor
  have hperf : PseudoCoherence.IsRelativelyPerfect
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor
      (StacksDraft.TorAmplitude.canonicalTensorComparison R)
      (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived R) K' := by
    refine ⟨(StacksDraft.PseudoCoherence.pseudoCoherent_iff_of_ringEquiv
      e.symm.toRingEquiv K).2.mp hK.relativelyPerfect.1, ?_⟩
    obtain ⟨a, b, htor⟩ := hK.relativelyPerfect.2
    let f : R →+* C := algebraMap R C
    let g : C →+* B := e.symm.toRingEquiv
    let h : R →+* B := algebraMap R B
    have hh : h = g.comp f := RingHom.ext fun r => (e.symm.commutes r).symm
    let η := ModuleCat.restrictScalarsComp' f g h hh
    let H := ModuleCat.restrictScalars f
    let G := ModuleCat.restrictScalars g
    let I := ModuleCat.restrictScalars h
    let θ := (mapDerivedCategoryNatIso I (G ⋙ H) η).app K ≪≫
      (mapDerivedCategoryCompNatIso G H (G ⋙ H) (Iso.refl _)).symm.app K
    exact ⟨a, b, fun M i hi => (htor M i hi).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor.mapIso
          θ).app ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)).symm)⟩
  refine ⟨hperf, ?_⟩
  rcases hK.diagonalDerivedHom with ⟨hdiag⟩
  let hReg : F.mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} C) 0).obj (ModuleCat.of C C) :=
    (F.mapDerivedCategorySingleFunctor 0).app (ModuleCat.of B B) ≪≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} C) 0).mapIso
        (ModuleCat.restrictScalarsIsoOfEquiv e.symm.toRingEquiv)
  exact ⟨by
    simpa [K', F] using
      ((derivedHom.{u, u}
        (Algebra.TensorProduct.lmul' R : C ⊗[R] C →ₐ[R] C).toRingHom).mapIso
          (diagonalExtensionTransportIso e K).symm ≪≫
      ((derivedHomTransportIso e).app ((diagonalDerivedExtension R B).obj K)).symm ≪≫
      F.mapDerivedCategory.mapIso hdiag ≪≫ hReg)⟩

end RelativeExistence

end Dualizing

end
