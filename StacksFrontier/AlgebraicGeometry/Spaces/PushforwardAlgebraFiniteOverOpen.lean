module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Finite
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardAlgebraChartIntegral

/-!
# The direct-image algebra is finite and of finite presentation over an open subspace

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` whose structure morphism is
representable, and let `V ⊆ Y` be an open subspace such that the base change
`f⁻¹(V) = X ×_Y V ⟶ V` is finite (Stacks 03ZP) and of finite presentation (Stacks 03XP).  Then on
every affine étale chart `U` of `Y` factoring through `V`, the structure-algebra map
`𝒪_Y(U) ⟶ (f_* 𝒪_X)(U)` of the direct-image algebra is finite and of finite presentation.  This
is the statement "`(f_* 𝒪_X)|_V` is a finite and finitely presented `𝒪_V`-algebra" of the source's
proof of Stacks 0GUM, read on charts.

The proof follows `AlgebraicGeometry.Space.isIntegral_pushforwardAlgebra_of_isIntegralHom`.  The
chart `U ⟶ Y` lifts to `ξ : U ⟶ V`; finiteness of `f⁻¹(V) ⟶ V` supplies an affine `W` finite over
`U` with a cartesian square over `ξ`, which pasted with the cartesian square of `f` along `V ⟶ Y`
is a cartesian square over `f` and `U ⟶ Y`.  That square is a square of étale charts of
`f⁻¹(V) ⟶ V` (the chart `ξ` is étale because `V ⟶ Y` is a monomorphism, and `W ⟶ f⁻¹(V)` is its
base change), so local finite presentation of `f⁻¹(V) ⟶ V` makes `W ⟶ U` locally of finite
presentation.  On global sections of affine schemes these give finite and finitely presented ring
maps, and the structure-algebra map differs from them by a ring isomorphism.

## Main results

* `Space.finite_and_finitePresentation_pushforwardAlgebra_algebraMap_of_range_le`:
  **the structure-algebra map of `f_* 𝒪_X` on an affine étale chart through `V` is finite and of
  finite presentation.**

## References

* [Stacks Project, Tag 03ZP](https://stacks.math.columbia.edu/tag/03ZP)
* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
* [Stacks Project, Tag 0GUM](https://stacks.math.columbia.edu/tag/0GUM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- **The direct image `f_* 𝒪_X` is finite and of finite presentation over an open subspace `V`
over which `f` is finite and of finite presentation**, on charts: if `f⁻¹(V) ⟶ V` is finite
(Stacks 03ZP) and of finite presentation (Stacks 03XP), then on every affine étale chart `U` of
`Y` factoring through `V` the structure-algebra map `𝒪_Y(U) ⟶ (f_* 𝒪_X)(U)` is finite and of
finite presentation.

The base change of `f` along `U` is represented by an affine scheme `W` finite and locally of
finite presentation over `U`, whose map on global sections is therefore finite and of finite
presentation; the structure-algebra map is that map followed by a ring isomorphism. -/
theorem finite_and_finitePresentation_pushforwardAlgebra_algebraMap_of_range_le
    (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)
    {V : Subfunctor Y.1} (hV : IsOpenImmersion B S hS V.ι)
    (hfin : IsFinite B S hS (pullback.snd f.hom V.ι))
    (hfp : IsFinitePresentation B S hS (pullback.snd f.hom V.ι))
    (U : SmallEtale B S hS Y.1)
    (hU : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj U))
    (hUV : Subfunctor.range U.obj.hom ≤ V) :
    RingHom.Finite ((pushforwardAlgebra B S hS (Over.mk f)).algebraMap (op U)) ∧
      RingHom.FinitePresentation
        ((pushforwardAlgebra B S hS (Over.mk f)).algebraMap (op U)) := by
  let ξ : yoneda.obj U.obj.left ⟶ V.toFunctor := Subfunctor.lift U.obj.hom hUV
  have := mono_of_isOpenImmersion B S hS V.ι hV
  have : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have hξ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf ξ :=
    MorphismProperty.presheaf_of_comp_mono _ (m := V.ι) (by
      rw [Subfunctor.lift_ι]
      exact U.property)
  obtain ⟨W, p, i, hW, hpfin, sq⟩ := hfin U.obj.left hU ξ
  have hi : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf i :=
    presheaf_of_isPullback B S hS sq.flip hξ
  have hplfp : AlgebraicGeometry.LocallyOfFinitePresentation
      ((BigFppfOver.toScheme B S hS).map p) :=
    hfp.1 W U.obj.left i ξ p hi hξ sq.w.symm
  have sq' : IsPullback (i ≫ pullback.fst f.hom V.ι) (yoneda.map p) f.hom U.obj.hom := by
    have h := sq.paste_horiz (IsPullback.of_hasPullback f.hom V.ι)
    rwa [Subfunctor.lift_ι] at h
  obtain ⟨e, he⟩ := exists_iso_comp_toScheme_map_snd B S hS f hf U.obj.hom p _ sq'
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U.obj.left) := hU
  have : AlgebraicGeometry.IsFinite
      ((BigFppfOver.toScheme B S hS).map (hf.snd U.obj.hom)) := by
    rw [he]
    infer_instance
  have : AlgebraicGeometry.LocallyOfFinitePresentation
      ((BigFppfOver.toScheme B S hS).map (hf.snd U.obj.hom)) := by
    rw [he]
    infer_instance
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (hf.pullback U.obj.hom)) :=
    isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map (hf.snd U.obj.hom))
  have hfpApp :
      ((BigFppfOver.toScheme B S hS).map (hf.snd U.obj.hom)).appTop.hom.FinitePresentation :=
    HasRingHomProperty.appTop @AlgebraicGeometry.LocallyOfFinitePresentation _ inferInstance
  have hbij := ConcreteCategory.bijective_of_isIso
    (pushforwardAlgebraSectionsIso B S hS (Over.mk f) hf U).inv
  change ((smallEtaleRingedToposHom B S hS (Over.mk f).hom).fSharp.hom.app (op U)).hom.Finite ∧
    ((smallEtaleRingedToposHom B S hS (Over.mk f).hom).fSharp.hom.app (op U)).hom.FinitePresentation
  rw [pushforwardAlgebra_algebraMap_eq_comp B S hS f hf U]
  exact ⟨RingHom.Finite.comp (RingHom.Finite.of_surjective _ hbij.2)
      ((BigFppfOver.toScheme B S hS).map (hf.snd U.obj.hom)).finite_appTop,
    RingHom.FinitePresentation.comp
      (RingHom.FinitePresentation.of_bijective hbij) hfpApp⟩

end AlgebraicGeometry.Space

end
