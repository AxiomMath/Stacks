module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Limits.Preserves.Over
public import StacksFrontier.RingTheory.Smoothing.IndSmooth

/-!
# Ind-smooth algebras as cofiltered limits of smooth affine schemes

An ind-smooth `R`-algebra `Λ` is by definition a filtered colimit of smooth `R`-algebras. Taking
spectra turns such a presentation into a cofiltered limit of affine schemes smooth over `Spec R`
whose limit is `Spec Λ`, compatibly with the canonical morphism `Spec Λ ⟶ Spec R`.

## Main results

* `AlgebraicGeometry.exists_cofiltered_smooth_limit_presentation`: if `Λ` is an ind-smooth
  `R`-algebra, then `Spec Λ` is the limit of a cofiltered diagram of affine schemes smooth
  over `Spec R`.

## Implementation notes

The filtered colimit supplied by `Stacks.Smoothing.IndSmooth` lives in `Under (CommRingCat.of R)`.
It is pushed to `CommRingCat` along `CategoryTheory.Under.forget`, which preserves filtered
colimits (an instance of `CategoryTheory.Limits.PreservesFilteredColimitsOfSize` in Mathlib), then
turned into a limit cone in `CommRingCatᵒᵖ` by `CategoryTheory.Limits.IsColimit.op`, and mapped
through `AlgebraicGeometry.Scheme.Spec`, which preserves limits as a right adjoint. The index
category of the limit is therefore the opposite of the filtered index category, which is cofiltered
and small. The tip of the resulting cone is `Spec Λ` on the nose, so the isomorphism `e` in the
statement is the identity.

The structure morphisms are the spectra of the structure maps of the diagram in
`Under (CommRingCat.of R)`; their naturality and their compatibility with the limit projections are
both instances of the triangle identity `CategoryTheory.Under.w`, and their smoothness is
`AlgebraicGeometry.HasRingHomProperty.Spec_iff` for `AlgebraicGeometry.Smooth`.

## References

* [Stacks Project, Tag 07C3](https://stacks.math.columbia.edu/tag/07C3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace SmoothLimitPresentation

variable {R₀ : CommRingCat.{u}} {X : Under R₀} {J : Type u} [SmallCategory J] [IsFiltered J]
  (pres : ColimitPresentation J X)

/-- The colimit presentation of the underlying ring of `X`, obtained from a colimit presentation
in `Under R₀` by forgetting the structure maps. -/
def ringPresentation : ColimitPresentation J X.right :=
  pres.map (Under.forget R₀)

/-- The diagram of affine schemes attached to a colimit presentation in `Under R₀`: the spectrum
of each stage, indexed by the opposite of the filtered index category. -/
def specDiagram : Jᵒᵖ ⥤ Scheme.{u} :=
  (pres.diag ⋙ Under.forget R₀).op ⋙ Scheme.Spec

/-- Every stage of `specDiagram pres` is an affine scheme. -/
instance (i : Jᵒᵖ) : IsAffine ((specDiagram pres).obj i) :=
  inferInstanceAs (IsAffine (Scheme.Spec.obj _))

/-- The cone over `specDiagram pres` with tip the spectrum of the underlying ring of `X`. -/
def specCone : Cone (specDiagram pres) :=
  Scheme.Spec.mapCone (ringPresentation pres).cocone.op

/-- The spectrum of the underlying ring of `X` is the limit of the spectra of the stages. -/
def isLimitSpecCone : IsLimit (specCone pres) :=
  isLimitOfPreserves Scheme.Spec (ringPresentation pres).isColimit.op

/-- The tip of `specCone pres` is the spectrum of the underlying ring of `X`. -/
theorem specCone_pt : (specCone pres).pt = Spec X.right := rfl

/-- The projection of `specCone pres` at a stage is the spectrum of the colimit inclusion of
`pres` at that stage. -/
theorem specCone_π_app (i : Jᵒᵖ) :
    (specCone pres).π.app i = Spec.map (pres.ι.app i.unop).right := by
  show Spec.map ((pres.ι.app i.unop).right ≫ 𝟙 _) = _
  rw [Category.comp_id]

/-- The morphisms from the stages of `specDiagram pres` down to `Spec R₀`, given by the spectra of
the structure maps of the diagram in `Under R₀`. -/
def specStructure : specDiagram pres ⟶ (Functor.const Jᵒᵖ).obj (Spec R₀) where
  app i := Spec.map (pres.diag.obj i.unop).hom
  naturality i i' f := by
    have hw := Under.w (pres.diag.map f.unop)
    change Spec.map (pres.diag.map f.unop).right ≫ Spec.map (pres.diag.obj i'.unop).hom
      = Spec.map (pres.diag.obj i.unop).hom ≫ 𝟙 _
    rw [Category.comp_id, ← Spec.map_comp, hw]

omit [IsFiltered J] in
/-- Each structure morphism of `specDiagram pres` is the spectrum of the structure map of the
corresponding stage. -/
theorem specStructure_app (i : Jᵒᵖ) :
    (specStructure pres).app i = Spec.map (pres.diag.obj i.unop).hom := rfl

/-- The limit projections of `specCone pres`, followed by the structure morphisms, are the
spectrum of the structure map of `X`. -/
theorem specCone_π_comp_specStructure (i : Jᵒᵖ) :
    (specCone pres).π.app i ≫ (specStructure pres).app i = Spec.map X.hom := by
  rw [specCone_π_app, specStructure_app]
  exact (Spec.map_comp _ _).symm.trans (congrArg Spec.map (Under.w (pres.ι.app i.unop)))

end SmoothLimitPresentation

/-- **An ind-smooth algebra is a cofiltered limit of affine schemes smooth over the base.** If `Λ`
is a filtered colimit of smooth `R`-algebras, then `Spec Λ` is the limit of a cofiltered diagram of
affine schemes, each of which is smooth over `Spec R`, and the limit projections composed with the
smooth structure morphisms all agree with the canonical morphism `Spec Λ ⟶ Spec R`. -/
theorem exists_cofiltered_smooth_limit_presentation
    {R Λ : Type u} [CommRing R] [CommRing Λ] [Algebra R Λ]
    (h : Stacks.Smoothing.IndSmooth R Λ) :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsCofiltered I)
      (D : I ⥤ Scheme.{u})
      (p : D ⟶ (Functor.const I).obj (Spec (CommRingCat.of R)))
      (c : Cone D) (_ : IsLimit c)
      (e : Spec (CommRingCat.of Λ) ≅ c.pt),
      (∀ i, IsAffine (D.obj i)) ∧
      (∀ i, Smooth (p.app i)) ∧
      (∀ i, e.hom ≫ c.π.app i ≫ p.app i =
        Spec.map (CommRingCat.ofHom (algebraMap R Λ))) := by
  obtain ⟨J, hJ, hfilt, pres, hsmooth⟩ := h
  refine ⟨Jᵒᵖ, inferInstance, inferInstance, SmoothLimitPresentation.specDiagram pres,
    SmoothLimitPresentation.specStructure pres, SmoothLimitPresentation.specCone pres,
    SmoothLimitPresentation.isLimitSpecCone pres, Iso.refl _,
    fun i ↦ inferInstance, fun i ↦ ?_, fun i ↦ ?_⟩
  · rw [SmoothLimitPresentation.specStructure_app]
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr (hsmooth i.unop)
  · exact (Category.id_comp _).trans
      (SmoothLimitPresentation.specCone_π_comp_specStructure pres i)

end AlgebraicGeometry

end
