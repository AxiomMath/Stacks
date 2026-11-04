module

public import StacksFrontier.Deformation.Artin.FiniteDimensional.AlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpaceGeneralCase
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation

/-!
# Finite-dimensionality at a point of an algebraic space locally of finite presentation

Let `S` be a locally Noetherian scheme and `B` an algebraic space over `S` which is locally of
finite presentation over `S`. Read as a category fibred in groupoids over the big fppf site of
`S` it is an algebraic stack (`AlgebraicGeometry.Stack.algebraicSpaceStack`), and an étale scheme
atlas `U ⟶ B` presents it by a smooth surjective `1`-morphism `(Sch/U) ⟶ B`. The scheme `U` is
locally of finite type over `S`, the atlas being étale and `B` locally of finite presentation over
`S`. So Stacks 07X1 applies: at every field point of finite type over `S`, the tangent space and
the infinitesimal automorphisms of `B` are finite-dimensional.

This is the step of the source's proof of Stacks 08W8 asserting that "the tangent space of `B`
is finite dimensional by Artin's Axioms, Lemma 07X1".

## Main results

* `AlgebraicGeometry.Space.locallyOfFiniteType_of_etale_atlas`: the scheme of an étale chart of an
  algebraic space locally of finite presentation over `S` is locally of finite type over `S`.
* `Deformation.Artin.isFiniteDimensionalDeformationCategory_algebraicSpaceStack`: Stacks 07X1 at a
  point of an algebraic space locally of finite presentation over `S`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The scheme of an étale chart of an algebraic space locally of finite presentation over `S`
is locally of finite presentation over `S`.** The chart and the terminal object of the site form
a commuting square of étale charts of the structure morphism, whose underlying morphism of
schemes is the structure morphism of the chart. -/
theorem locallyOfFinitePresentation_of_etale_chart {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hlfp : IsLocallyOfFinitePresentation B S hS (terminal.from F))
    (T : BigFppfOver B S hS) (a : yoneda.obj T ⟶ F)
    (ha : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    AlgebraicGeometry.LocallyOfFinitePresentation (B.inclusion.map T.hom) := by
  set O : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS)) with hO
  set τ : T ⟶ O := Over.homMk T.hom (Category.comp_id _) with hτ
  have hterm : IsTerminal (yoneda.obj O) :=
    (Over.mkIdTerminal (X := B.obj hS)).isTerminalObj yoneda _
  set e : yoneda.obj O ≅ ⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    hterm.uniqueUpToIso terminalIsTerminal with he
  have hb : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf e.hom := by
    simpa using MorphismProperty.RespectsIso.postcomp (MorphismProperty.presheaf _) e.hom
      (yoneda.map (𝟙 O)) ((presheaf_yoneda_map_etale_iff B S hS (𝟙 O)).2 (by
        rw [CategoryTheory.Functor.map_id]
        infer_instance))
  have hsq : yoneda.map τ ≫ e.hom = a ≫ terminal.from F := terminal.hom_ext _ _
  exact hlfp T O a e.hom τ ha hb hsq

/-- **The scheme of an étale chart of an algebraic space locally of finite presentation over `S`
is locally of finite type over `S`.** -/
theorem locallyOfFiniteType_of_etale_chart {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hlfp : IsLocallyOfFinitePresentation B S hS (terminal.from F))
    (T : BigFppfOver B S hS) (a : yoneda.obj T ⟶ F)
    (ha : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    AlgebraicGeometry.LocallyOfFiniteType (B.inclusion.map T.hom) := by
  have := locallyOfFinitePresentation_of_etale_chart B S hS hlfp T a ha
  infer_instance

end AlgebraicGeometry.Space

namespace Deformation.Artin

open AlgebraicGeometry

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 07X1 at a point of an algebraic space locally of finite presentation over `S`.** Let
`S` be locally Noetherian and `F` an algebraic space over `S` locally of finite presentation
over `S`. For every `𝓕 = 𝓕_{F,k,x₀}` as in Section 07T2 — `k` a field of finite type over `S`,
`Spec Λ ⊆ S` an affine open through which `Spec k ⟶ S` factors with `Λ → k` finite, `x₀` a
point of `F` over `Spec k` — the predeformation category `𝓕` is a deformation category whose
tangent space and infinitesimal automorphisms are finite-dimensional over `k`.

`F` is an algebraic stack by `AlgebraicGeometry.Stack.isAlgebraicStack_fibredCategory`, and an
étale scheme atlas of `F` presents it smoothly and surjectively by a scheme locally of finite
type over `S`; Stacks 07X1 is
`Deformation.Artin.isFiniteDimensionalDeformationCategory_of_algebraicStack`. -/
theorem isFiniteDimensionalDeformationCategory_algebraicSpaceStack [IsLocallyNoetherian S]
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from F))
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) (hiΛ : IsOpenImmersion iΛ)
    (x₀ : (Stack.algebraicSpaceStack.{u, w} B S hS F hF).val.val.obj)
    (hx₀ : ((Stack.algebraicSpaceStack.{u, w} B S hS F hF).val.val.p ⋙
      Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    letI := (predeformationCategory iΛ
      ((Stack.algebraicSpaceStack.{u, w} B S hS F hF).val.val.p ⋙ Over.post B.inclusion)
      x₀ hx₀).category
    IsFiniteDimensionalDeformationCategory
      (predeformationCategory iΛ
        ((Stack.algebraicSpaceStack.{u, w} B S hS F hF).val.val.p ⋙ Over.post B.inclusion)
        x₀ hx₀).projection := by
  obtain ⟨T, atl, hsurjp, hetalep⟩ := hF.exists_atlas
  have hsurj : Space.IsSurjective B S hS atl :=
    (Space.surjective_iff_surjective_pointsMap B S hS F hF T atl).1 hsurjp
  have hetale : Space.IsEtale B S hS atl :=
    (Space.isEtale_iff_presheaf_of_yoneda B S hS atl).2 hetalep
  have hsmooth : Space.IsSmooth B S hS atl := Space.isSmooth_of_isEtale B S hS hF hetale
  have := Space.locallyOfFiniteType_of_etale_chart B S hS hlfp T atl hetalep
  exact isFiniteDimensionalDeformationCategory_of_algebraicStack
    (Stack.algebraicSpaceStack.{u, w} B S hS F hF) T
    (Bicategory.InducedBicategory.mkHom (Stack.presentationBasedFunctor B S hS T atl))
    (Stack.isRepresentableFromSchemes_of_isRepresentableByAlgebraicSpace B S hS
      (Stack.fibredCategory B S hS F)
      (Stack.isRepresentableByAlgebraicSpace_fibredCategory B S hS F hF) T
      (Stack.presentationBasedFunctor B S hS T atl))
    (fun W yv hyv G hG he =>
      ⟨Stack.prop_presentationBasedFunctor B S hS (Space.surjectiveMorphismProperty B S hS) T hF
        atl hsurj W yv hyv G hG he,
       Stack.prop_presentationBasedFunctor B S hS (Space.smoothMorphismProperty B S hS) T hF
        atl hsmooth W yv hyv G hG he⟩)
    iΛ hiΛ x₀ hx₀ hfinite

end Deformation.Artin

end
