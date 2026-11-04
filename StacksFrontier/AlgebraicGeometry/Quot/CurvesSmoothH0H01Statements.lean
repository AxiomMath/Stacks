module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesH01Inputs
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmoothH0

/-!
# `Curves^{smooth,h0}` over the statements of the cohomological inputs of Stacks 0E6I

Stacks 0E81 for `Curves^{smooth,h0}`, assuming as hypotheses `hbetti` and `hstruct` the statements
of Stacks 0E0R (at `i = 0`, for `𝓕 = 𝒪_X`) and of Stacks 0E6B part (a) for algebraic spaces.

## Main results

* `AlgebraicGeometry.curvesSmoothH0_isOpenSubstack_and_factors_iff_and_tfae_of_h01Statements`:
  Stacks 0E81, the whole statement, under the hypotheses `hbetti` and `hstruct`.

## References

* [Stacks Project, Tag 0E81](https://stacks.math.columbia.edu/tag/0E81)
* [Stacks Project, Tag 0E6I](https://stacks.math.columbia.edu/tag/0E6I)
* [Stacks Project, Tag 0E0R](https://stacks.math.columbia.edu/tag/0E0R)
* [Stacks Project, Tag 0E6B](https://stacks.math.columbia.edu/tag/0E6B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- Assume that for a proper, flat morphism of finite presentation `f : X → U` the function
`p ↦ dim H⁰(X_p, 𝒪)` is upper semicontinuous (`hbetti`), and that if `f` induces bijections on
global functions of its fibres over field-valued points then `f_*𝒪_X = 𝒪_Y` universally
(`hstruct`). Then `Curves^{smooth,h0} ⊂ Curves` is an open substack, a morphism `U → Curves`
factors through it if and only if the family it classifies over `U` is smooth with `H⁰ = 𝒪`, and
for a curve over a field `k` the following are equivalent: it lies in `Curves^{smooth,h0}`; it is
smooth of dimension `1` with `Γ(X, 𝒪_X) = k`; it is smooth of dimension `1` and geometrically
connected; it is smooth of dimension `1` and geometrically integral; its base change to `k̄` is a
smooth curve. -/
theorem curvesSmoothH0_isOpenSubstack_and_factors_iff_and_tfae_of_h01Statements
    (hbetti : ∀ {U : BigFppfOver B integerBase hZ} {X : AlgebraicSpaces B integerBase hZ}
      (f : X ⟶ schemeSpace U), Space.IsProper B integerBase hZ f.hom →
      Space.IsFlat B integerBase hZ f.hom → Space.IsFinitePresentation B integerBase hZ f.hom →
      ∃ b : (BigFppfOver.toScheme B integerBase hZ).obj U → ℕ∞, UpperSemicontinuous b ∧
        ∀ p : Space.FieldValuedPoint B integerBase hZ (yoneda.obj U),
          Space.h0FibreRank B integerBase hZ f p = b (Space.schemePoint B integerBase hZ U p))
    (hstruct : ∀ {X Y : AlgebraicSpaces B integerBase hZ} (f : X ⟶ Y),
      Space.IsProper B integerBase hZ f.hom → Space.IsFlat B integerBase hZ f.hom →
      Space.IsFinitePresentation B integerBase hZ f.hom →
      (∀ p : Space.FieldValuedPoint B integerBase hZ Y.1, Function.Bijective
        (algebraMap p.carrier (Space.globalFunctions B (Spec (.of p.carrier)) p.contained
          (Space.fibreOverFieldValuedPoint B integerBase hZ f.hom p)))) →
      IsIso (Space.structureSharp B integerBase hZ f) ∧
        ∀ (Y' : AlgebraicSpaces B integerBase hZ) (g : Y' ⟶ Y),
          IsIso (Space.structureSharp B integerBase hZ (pullback.snd f g))) :
    ((ObjectProperty.IsClosedUnderIsomorphisms (IsSmoothH0CurveFamily B hZ) ∧
      Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (curvesSubstackInclusion B hZ (IsSmoothH0CurveFamily B hZ)
          (isOpenCurvesLocus_isSmoothH0CurveFamily_of
            (CurveFamily.isOpenCurvesLocus_isH01CurveFamily_of_h0FibreRank hbetti
              hstruct)).prop_of_hom).hom ∧
      Stack.IsOpenImmersion B integerBase hZ
        (curvesSubstackInclusion B hZ (IsSmoothH0CurveFamily B hZ)
          (isOpenCurvesLocus_isSmoothH0CurveFamily_of
            (CurveFamily.isOpenCurvesLocus_isH01CurveFamily_of_h0FibreRank hbetti
              hstruct)).prop_of_hom)) ∧
    ∀ (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
          ObjectProperty.FullSubcategory (IsSmoothH0CurveFamily B hZ),
          z ⋙ ObjectProperty.ι (IsSmoothH0CurveFamily B hZ) = y) ↔
        IsSmoothH0CurveFamily B hZ (y.obj (Over.mk (𝟙 U.left))))) ∧
    ∀ {T W : BigFppfOver B integerBase hZ} (g : T ⟶ W) (k : Type u) [Field k]
      (hW : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k))
      (hflat : Flat ((BigFppfOver.toScheme B integerBase hZ).map g))
      (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
      (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map g))
      (hqc : Space.IsQuasiCompact B integerBase hZ (schemeSpaceMap g).hom)
      (hsep : Space.IsSeparated B integerBase hZ (schemeSpaceMap g).hom)
      (hqsep : Space.IsQuasiSeparated B integerBase hZ (schemeSpaceMap g).hom)
      (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1)
      (y : BigFppfOver B W.left.1 W.left.2 ⥤ CurveFamily B hZ)
      (_hy : y ⋙ curvesProjectionOver B hZ = Over.map W.hom)
      (_e : y.obj (Over.mk (𝟙 W.left)) ≅
        curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim),
      List.TFAE [
        ∃ z : BigFppfOver B W.left.1 W.left.2 ⥤
            ObjectProperty.FullSubcategory (IsSmoothH0CurveFamily B hZ),
          z ⋙ ObjectProperty.ι (IsSmoothH0CurveFamily B hZ) = y,
        Smooth ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW) ∧
          topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) = 1 ∧
          IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫
            ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW).appTop),
        Smooth ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW) ∧
          topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) = 1 ∧
          GeometricallyConnected ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW),
        Smooth ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW) ∧
          topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) = 1 ∧
          GeometricallyIntegral ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW),
        IsCurve (AlgebraicClosure k)
            (pullback.snd ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW)
              (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) ∧
          Smooth (pullback.snd ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW)
            (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))] :=
  have hpush : ∀ X : CurveFamily B hZ,
      CurveFamily.HasBijectiveGlobalFunctionsOnFieldFibres B hZ X →
      HasUniversallyBijectiveGlobalFunctions B hZ X := fun _ hX =>
    CurveFamily.hasUniversallyBijectiveGlobalFunctions_of_hasBijectiveGlobalFunctionsOnFieldFibres
      hstruct hX
  curvesSmoothH0_isOpenSubstack_and_factors_iff_and_tfae_of
    (CurveFamily.isOpenCurvesLocus_isH01CurveFamily_of_h0FibreRank hbetti hstruct)
    (fun g k _ hW hflat hproper hlfp hqc hsep hqsep hdim =>
      CurveFamily.hasUniversallyBijectiveGlobalFunctions_curveFamilyOfSchemeMorphism_iff_of hpush
        g k hW hflat hproper hlfp hqc hsep hqsep hdim)

end AlgebraicGeometry

end
