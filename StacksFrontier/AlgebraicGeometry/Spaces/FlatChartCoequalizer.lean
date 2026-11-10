module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeFiniteFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.Surjective

/-!
# Flat charts of an algebraic space as coequalizers of their kernel pairs

Part (3) of Stacks 0262 states that a surjective étale chart of an algebraic space exhibits it
as the coequalizer, in fppf sheaves of sets, of the two projections of the kernel pair of the
chart.  The proof uses étaleness only to make the chart a surjection of fppf sheaves, so the
same conclusion holds for a chart which is surjective, flat and locally of finite presentation,
and in particular for a surjective finite locally free chart.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.isCoequalizer_of_isLocallySurjective`: a chart of an algebraic space
  which is locally surjective for the fppf topology exhibits the space as the coequalizer of
  its kernel pair.
* `AlgebraicGeometry.Space.isCoequalizer_of_surjective_flat_locallyOfFinitePresentation`:
  **Stacks 0262**, part (3), for a surjective flat chart locally of finite presentation.
* `AlgebraicGeometry.Space.isCoequalizer_of_surjectiveFiniteLocallyFree`: **Stacks 0262**,
  part (3), for a surjective finite locally free chart.

## Implementation notes

The three statements share the generic coequalizer criterion
`CategoryTheory.Sheaf.nonempty_isColimitCoforkOfKernelPair`, whose two hypotheses are the
pointwise realisation of the kernel pair — supplied by the Yoneda lemma, a pair of sections of
`yoneda.obj U` with the same image being the pair of projections of the lift into `R` — and
local surjectivity of the chart.  Representables are sheaves because the big fppf site is
subcanonical.

Local surjectivity is where the hypothesis on the chart enters.  For a surjective flat chart
locally of finite presentation it is Tag 05VM, in the namespace
`AlgebraicGeometry.Space` as
`isLocallySurjective_of_representable_flat_locallyOfFinitePresentation_surjective`; its
hypothesis is a single relative morphism property asking all three conditions of each
represented base change at once, and the three separate hypotheses are assembled into it base
change by base change.  Finite local freeness is read in the representable sense, condition (1)
of Stacks 03ZW, and implies flatness and local finite presentation of each represented base
change by the scheme-level equivalence Tag 02KB.

Surjectivity is likewise the relative property of Tag 02YN rather than surjectivity of the map
on points: that is the form Tag 05VM consumes, and the form in which charts of an algebraic
space are produced.

## References

* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
* [Stacks Project, Tag 05VM](https://stacks.math.columbia.edu/tag/05VM)
* [Stacks Project, Tag 0416](https://stacks.math.columbia.edu/tag/0416)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {R U : BigFppfOver B S hS}

/-- Representable presheaves on the big fppf site over `S` are fppf sheaves. -/
private theorem isSheaf_yoneda_obj (X : BigFppfOver B S hS) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) (yoneda.obj X) := by
  let _ : B.topology.Subcanonical := BigFppfSite.subcanonical_topology B
  let _ : (BigFppfOver.topology B S hS).Subcanonical := inferInstance
  exact (isSheaf_iff_isSheaf_of_type _ _).mpr
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)

/-- A chart `f : U ⟶ F` of an algebraic space which is locally surjective for the fppf topology
exhibits `F` as the coequalizer, in fppf sheaves of sets, of the two projections of its kernel
pair: every map to a sheaf which identifies the two projections descends uniquely. -/
theorem isCoequalizer_of_isLocallySurjective
    (f : yoneda.obj U ⟶ F) (s t : R ⟶ U)
    (hR : IsPullback (yoneda.map s) (yoneda.map t) f f)
    (hF : IsAlgebraicSpace B S hS F)
    (hloc : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) f) :
    let J := BigFppfOver.topology B S hS
    ∃ (hRsh : Presheaf.IsSheaf J (yoneda.obj R))
      (hUsh : Presheaf.IsSheaf J (yoneda.obj U)),
      let RF : Sheaf J (Type u) := ⟨yoneda.obj R, hRsh⟩
      let UF : Sheaf J (Type u) := ⟨yoneda.obj U, hUsh⟩
      let FF : Sheaf J (Type u) := ⟨F, hF.isSheaf⟩
      let sf : RF ⟶ UF := ⟨yoneda.map s⟩
      let tf : RF ⟶ UF := ⟨yoneda.map t⟩
      let ff : UF ⟶ FF := ⟨f⟩
    let w : sf ≫ ff = tf ≫ ff := by
        apply Sheaf.hom_ext
        exact hR.w
      Nonempty (IsColimit (Cofork.ofπ ff w)) := by
  let J := BigFppfOver.topology B S hS
  have hRsh := isSheaf_yoneda_obj B S hS R
  have hUsh := isSheaf_yoneda_obj B S hS U
  refine ⟨hRsh, hUsh, ?_⟩
  let RF : Sheaf J (Type u) := ⟨yoneda.obj R, hRsh⟩
  let UF : Sheaf J (Type u) := ⟨yoneda.obj U, hUsh⟩
  let FF : Sheaf J (Type u) := ⟨F, hF.isSheaf⟩
  let sf : RF ⟶ UF := ⟨yoneda.map s⟩
  let tf : RF ⟶ UF := ⟨yoneda.map t⟩
  let ff : UF ⟶ FF := ⟨f⟩
  let w : sf ≫ ff = tf ≫ ff := Sheaf.hom_ext hR.w
  have hker : ∀ ⦃T : BigFppfOver B S hS⦄ (x y : UF.obj.obj (Opposite.op T)),
      ff.hom.app (Opposite.op T) x = ff.hom.app (Opposite.op T) y →
      ∃ r : RF.obj.obj (Opposite.op T),
        sf.hom.app (Opposite.op T) r = x ∧ tf.hom.app (Opposite.op T) r = y := by
    intro T x y hxy
    have hxy' : yoneda.map x ≫ f = yoneda.map y ≫ f := by
      apply yonedaEquiv.injective
      simpa only [yonedaEquiv_comp, yonedaEquiv_yoneda_map] using hxy
    let l := hR.lift (yoneda.map x) (yoneda.map y) hxy'
    refine ⟨yonedaEquiv l, ?_, ?_⟩
    · change (yoneda.map s).app (Opposite.op T) (yonedaEquiv l) = x
      rw [← yonedaEquiv_comp, show x = yonedaEquiv (yoneda.map x) from
        (yonedaEquiv_yoneda_map x).symm]
      exact congrArg yonedaEquiv (hR.lift_fst _ _ hxy')
    · change (yoneda.map t).app (Opposite.op T) (yonedaEquiv l) = y
      rw [← yonedaEquiv_comp, show y = yonedaEquiv (yoneda.map y) from
        (yonedaEquiv_yoneda_map y).symm]
      exact congrArg yonedaEquiv (hR.lift_snd _ _ hxy')
  exact Sheaf.nonempty_isColimitCoforkOfKernelPair sf tf ff w hker hloc

/-- **Stacks 0262**, part (3), with the étale hypothesis on the chart weakened to flatness
together with local finite presentation.  A surjective flat chart locally of finite
presentation of an algebraic space is the coequalizer, in fppf sheaves of sets, of its kernel
pair.

The three conditions are the relative properties of Tag 02YN: they are asked of every
represented base change of the chart. -/
@[stacks 0262 "part (3), with the étale chart of the source replaced by a surjective flat \
chart locally of finite presentation"]
theorem isCoequalizer_of_surjective_flat_locallyOfFinitePresentation
    (f : yoneda.obj U ⟶ F) (s t : R ⟶ U)
    (hR : IsPullback (yoneda.map s) (yoneda.map t) f f)
    (hF : IsAlgebraicSpace B S hS F)
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f)
    (hflat : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Flat.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f)
    (hlfp : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    let J := BigFppfOver.topology B S hS
    ∃ (hRsh : Presheaf.IsSheaf J (yoneda.obj R))
      (hUsh : Presheaf.IsSheaf J (yoneda.obj U)),
      let RF : Sheaf J (Type u) := ⟨yoneda.obj R, hRsh⟩
      let UF : Sheaf J (Type u) := ⟨yoneda.obj U, hUsh⟩
      let FF : Sheaf J (Type u) := ⟨F, hF.isSheaf⟩
      let sf : RF ⟶ UF := ⟨yoneda.map s⟩
      let tf : RF ⟶ UF := ⟨yoneda.map t⟩
      let ff : UF ⟶ FF := ⟨f⟩
    let w : sf ≫ ff = tf ≫ ff := by
        apply Sheaf.hom_ext
        exact hR.w
      Nonempty (IsColimit (Cofork.ofπ ff w)) := by
  have hUsh := isSheaf_yoneda_obj B S hS U
  have hall : (MorphismProperty.inverseImage
      ((fun _ _ g => AlgebraicGeometry.Flat g ∧
        AlgebraicGeometry.LocallyOfFinitePresentation g ∧ AlgebraicGeometry.Surjective g) :
          MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f :=
    ⟨hflat.1, fun _ _ g fst snd hpb =>
      ⟨hflat.2 g fst snd hpb, hlfp.2 g fst snd hpb, hsurj.2 g fst snd hpb⟩⟩
  exact isCoequalizer_of_isLocallySurjective B S hS f s t hR hF
    (isLocallySurjective_of_representable_flat_locallyOfFinitePresentation_surjective
      B S hS (F := ⟨yoneda.obj U, hUsh⟩) (G := ⟨F, hF.isSheaf⟩) ⟨f⟩ hall)

/-- **Stacks 0262**, part (3), for a surjective finite locally free chart in place of a
surjective étale one.  Such a chart of an algebraic space is the coequalizer, in fppf sheaves
of sets, of its kernel pair.

Finite local freeness is read in the representable sense, condition (1) of Stacks 03ZW, and
gives flatness and local finite presentation of every represented base change by the
scheme-level equivalence Tag 02KB. -/
@[stacks 0262 "part (3), for a surjective finite locally free chart of the source in place of \
a surjective étale one"]
theorem isCoequalizer_of_surjectiveFiniteLocallyFree
    (f : yoneda.obj U ⟶ F) (s t : R ⟶ U)
    (hR : IsPullback (yoneda.map s) (yoneda.map t) f f)
    (hF : IsAlgebraicSpace B S hS F)
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f)
    (hflf : (MorphismProperty.inverseImage
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    let J := BigFppfOver.topology B S hS
    ∃ (hRsh : Presheaf.IsSheaf J (yoneda.obj R))
      (hUsh : Presheaf.IsSheaf J (yoneda.obj U)),
      let RF : Sheaf J (Type u) := ⟨yoneda.obj R, hRsh⟩
      let UF : Sheaf J (Type u) := ⟨yoneda.obj U, hUsh⟩
      let FF : Sheaf J (Type u) := ⟨F, hF.isSheaf⟩
      let sf : RF ⟶ UF := ⟨yoneda.map s⟩
      let tf : RF ⟶ UF := ⟨yoneda.map t⟩
      let ff : UF ⟶ FF := ⟨f⟩
    let w : sf ≫ ff = tf ≫ ff := by
        apply Sheaf.hom_ext
        exact hR.w
      Nonempty (IsColimit (Cofork.ofπ ff w)) :=
  isCoequalizer_of_surjective_flat_locallyOfFinitePresentation B S hS f s t hR hF hsurj
    (presheaf_inverseImage_mono B S hS
      (fun p hp =>
        (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
          p).mp hp |>.2.1)
      hflf)
    (presheaf_inverseImage_mono B S hS
      (fun p hp =>
        (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
          p).mp hp |>.2.2)
      hflf)

end AlgebraicGeometry.Space

end
