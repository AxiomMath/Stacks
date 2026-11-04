module

public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation

/-!
# Two sheaves with a common surjective étale presentation are isomorphic

Let `f : U ⟶ F` and `f' : U ⟶ F'` be morphisms from the presheaf represented by an object `U` of
the big fppf site of `S` to two fppf sheaves, each surjective and étale after every
representable base change, with the same kernel pair `R ⇉ U`. Then `F ≅ F'` compatibly with `f`
and `f'`: both are the coequalizer of the kernel pair in fppf sheaves.

This is `AlgebraicGeometry.Space.exists_iso_of_common_presentation` with the algebraicity of the
two targets weakened to the sheaf property, which is all its proof uses. It is what identifies a
limit of algebraic spaces with a given algebraic space before the limit is known to be one, as in
the last step of the proof of absolute Noetherian approximation, Stacks 07SU.

## Main results

* `AlgebraicGeometry.Space.isCoequalizer_of_surjectiveEtale_of_isSheaf`: a surjective étale
  morphism from a representable presheaf to a sheaf is the coequalizer of its kernel pair.
* `AlgebraicGeometry.Space.exists_iso_of_common_presentation_of_isSheaf`: the uniqueness of the
  target of a common presentation.

## References

* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A surjective étale morphism from a representable presheaf to an fppf sheaf is the
coequalizer of its kernel pair**, in fppf sheaves of sets. -/
theorem isCoequalizer_of_surjectiveEtale_of_isSheaf
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {R U : BigFppfOver B S hS}
    (f : yoneda.obj U ⟶ F) (s t : R ⟶ U)
    (hR : IsPullback (yoneda.map s) (yoneda.map t) f f)
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f)
    (hetale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f) :
    let J := BigFppfOver.topology B S hS
    ∃ (hRsh : Presheaf.IsSheaf J (yoneda.obj R))
      (hUsh : Presheaf.IsSheaf J (yoneda.obj U)),
      let RF : Sheaf J (Type u) := ⟨yoneda.obj R, hRsh⟩
      let UF : Sheaf J (Type u) := ⟨yoneda.obj U, hUsh⟩
      let FF : Sheaf J (Type u) := ⟨F, hF⟩
      let sf : RF ⟶ UF := ⟨yoneda.map s⟩
      let tf : RF ⟶ UF := ⟨yoneda.map t⟩
      let ff : UF ⟶ FF := ⟨f⟩
    let w : sf ≫ ff = tf ≫ ff := by
        apply Sheaf.hom_ext
        exact hR.w
      Nonempty (IsColimit (Cofork.ofπ ff w)) := by
  classical
  let J := BigFppfOver.topology B S hS
  let _ : B.topology.Subcanonical := BigFppfSite.subcanonical_topology B
  let _ : J.Subcanonical := inferInstance
  have hsh (V : BigFppfOver B S hS) : Presheaf.IsSheaf J (yoneda.obj V) :=
    (isSheaf_iff_isSheaf_of_type J (yoneda.obj V)).mpr
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (J := J) (yoneda.obj V))
  refine ⟨hsh R, hsh U, ?_⟩
  intro RF UF FF sf tf ff w
  have hker : ∀ ⦃T : BigFppfOver B S hS⦄ (x y : UF.obj.obj (Opposite.op T)),
      ff.hom.app (Opposite.op T) x = ff.hom.app (Opposite.op T) y →
      ∃ r : RF.obj.obj (Opposite.op T),
        sf.hom.app (Opposite.op T) r = x ∧ tf.hom.app (Opposite.op T) r = y := by
    intro T x y hxy
    have hxy' : yoneda.map x ≫ f = yoneda.map y ≫ f := by
      apply yonedaEquiv.injective
      simpa only [yonedaEquiv_comp, yonedaEquiv_yoneda_map] using hxy
    let l := hR.lift (yoneda.map x) (yoneda.map y) hxy'
    have key (g : yoneda.obj R ⟶ yoneda.obj U) (z : yoneda.obj T ⟶ yoneda.obj R)
        (x : T ⟶ U) (h : z ≫ g = yoneda.map x) :
        g.app (Opposite.op T) (yonedaEquiv z) = x := by
      rw [← yonedaEquiv_comp, h, yonedaEquiv_yoneda_map]
    exact ⟨yonedaEquiv l, key (yoneda.map s) l x (hR.lift_fst _ _ hxy'),
      key (yoneda.map t) l y (hR.lift_snd _ _ hxy')⟩
  exact Sheaf.nonempty_isColimitCoforkOfKernelPair sf tf ff w hker
    (isLocallySurjective_of_surjective_etale B S hS f hsurj hetale)

/-- **Uniqueness of the target of a common presentation, for sheaves.** Two fppf sheaves `F`,
`F'` receiving surjective étale morphisms `f`, `f'` from the same representable presheaf, whose
kernel pairs are the same pair `s, t : R ⟶ U`, are isomorphic compatibly with `f` and `f'`. -/
theorem exists_iso_of_common_presentation_of_isSheaf
    {F F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {R U : BigFppfOver B S hS} {s t : R ⟶ U}
    {f : yoneda.obj U ⟶ F} {f' : yoneda.obj U ⟶ F'}
    (hR : IsPullback (yoneda.map s) (yoneda.map t) f f)
    (hR' : IsPullback (yoneda.map s) (yoneda.map t) f' f')
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (hF' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F')
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f)
    (hetale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f)
    (hsurj' : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f')
    (hetale' : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f') :
    ∃ e : F ≅ F', f ≫ e.hom = f' := by
  obtain ⟨_, _, ⟨h₁⟩⟩ :=
    isCoequalizer_of_surjectiveEtale_of_isSheaf B S hS f s t hR hF hsurj hetale
  obtain ⟨_, _, ⟨h₂⟩⟩ :=
    isCoequalizer_of_surjectiveEtale_of_isSheaf B S hS f' s t hR' hF' hsurj' hetale'
  exact ⟨(sheafToPresheaf _ _).mapIso (h₁.coconePointUniqueUpToIso h₂),
    congrArg InducedCategory.Hom.hom
      (h₁.comp_coconePointUniqueUpToIso_hom h₂ WalkingParallelPair.one)⟩

end AlgebraicGeometry.Space

end
