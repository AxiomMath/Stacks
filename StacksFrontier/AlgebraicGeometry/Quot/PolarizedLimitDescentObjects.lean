module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedLimitDescent
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedStackUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStageDescent

/-!
# Descent of objects for the stack of polarized proper schemes

Over a cofiltered limit of affine schemes, every object of the fibre category of `𝒫olarized` at the
limit admits a morphism, lying over a cone projection, to an object of the fibre at a finite stage.

## References

* [Stacks Project, Tag 0D43](https://stacks.math.columbia.edu/tag/0D43)
* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Descent of objects for `𝒫olarized`.** Every polarized family over the limit of a cofiltered
inverse system of affine schemes admits a morphism, lying over a cone projection, to a polarized
family over a finite stage. -/
theorem descentObj_polarizedSliceProjection (B : BigFppfSite.{u}) {S : Scheme.{u}}
    (hS : B.Contains S) (hT : IsTerminal (B.obj hS)) {I : Type u} [Category.{u} I]
    [IsCofiltered I] (D : I ⥤ BigAffineFppf B S hS) (c : Cone D)
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) :
    Deformation.Artin.DescentObj (polarizedSliceProjection B hS hT)
      (D ⋙ BigAffineFppf.inclusion B S hS) ((BigAffineFppf.inclusion B S hS).mapCone c) := by
  intro x
  obtain ⟨xf, hxf⟩ := x
  obtain ⟨xb, xt, xtb, xpr, xfl, xfp, xL, xLi, xLa⟩ := xf
  have hb : xb = ((BigAffineFppf.inclusion B S hS).mapCone c).pt.left :=
    congrArg Comma.left hxf
  subst hb
  have := xpr
  have := xfl
  have hAffD : ∀ i : I, IsAffine ((D ⋙ BigAffineFppf.toScheme B S hS).obj i) :=
    fun i => BigAffineFppf.isAffine_toScheme_obj B S hS (D.obj i)
  obtain ⟨i, Xi, fi, Li, hLiinv, g, hpri, hfli, hfpi, hampi, hpbi, ⟨eLi⟩⟩ :=
    exists_stage_polarizedModel (D ⋙ BigAffineFppf.toScheme B S hS)
      ((BigAffineFppf.toScheme B S hS).mapCone c) hc xtb xfp xL xLi xLa
  refine ⟨i, ⟨
    { base := (D.obj i).obj.left
      total := Xi
      toBase := fi
      proper := hpri
      flat := hfli
      finitePresentation := hfpi
      lineBundle := Li
      invertible := hLiinv
      relativelyAmple := hampi }, ?_⟩, ?_⟩
  · exact (polarizedProjection B).sliceAtTerminal_obj_eq hT rfl
  refine ⟨
    { baseMap := (((BigAffineFppf.inclusion B S hS).mapCone c).π.app i).left
      totalMap := g
      cartesian := hpbi
      lineBundleIso := eLi }, ?_⟩
  refine IsHomLift.of_fac' _ (((BigAffineFppf.inclusion B S hS).mapCone c).π.app i) _
    hxf ((polarizedProjection B).sliceAtTerminal_obj_eq hT rfl) ?_
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left, Over.eqToHom_left, Over.eqToHom_left]
  simp only [polarizedSliceProjection, Functor.sliceAtTerminal_map_left,
    polarizedProjection_map]
  exact (Category.id_comp _).symm

/-- **Essential surjectivity of the comparison functor of Stacks 07XL for `𝒫olarized`.** For every
cofiltered inverse system of affine schemes over the terminal base with limit `T`, the canonical
functor `colim 𝒫olarized_{Tᵢ} ⥤ 𝒫olarized_T` is essentially surjective. -/
theorem essSurj_colimitComparison_polarized (B : BigFppfSite.{u}) {S : Scheme.{u}}
    (hS : B.Contains S) (hT : IsTerminal (B.obj hS)) {I : Type u} [Category.{u} I]
    [IsCofiltered I] (D : I ⥤ BigAffineFppf B S hS) (c : Cone D)
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) :
    letI : (polarizedSliceProjection B hS hT).IsFibered :=
      (polarizedProjection_isFiberedInGroupoids_unconditional.sliceAtTerminal hT).isFibered
    (Deformation.Artin.colimitComparison (polarizedSliceProjection B hS hT)
      (D ⋙ BigAffineFppf.inclusion B S hS)
      ((BigAffineFppf.inclusion B S hS).mapCone c)).EssSurj :=
  let : (polarizedSliceProjection B hS hT).IsFibered :=
    (polarizedProjection_isFiberedInGroupoids_unconditional.sliceAtTerminal hT).isFibered
  Deformation.Artin.essSurj_of_descentObj (polarizedSliceProjection B hS hT)
    (polarizedProjection_isFiberedInGroupoids_unconditional.sliceAtTerminal hT) _ _
    (descentObj_polarizedSliceProjection B hS hT D c hc)

end AlgebraicGeometry

end
