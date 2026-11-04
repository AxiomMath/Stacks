module

public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjectionRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyInjectiveSmallEtale

/-!
# The direct-image algebra of an integral morphism is integral

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` whose structure morphism is
representable.  On an étale scheme chart `V` of `Y` the structure-algebra map
`𝒪_Y(V) ⟶ (f_* 𝒪_X)(V)` of the direct-image algebra is, after the identification
`(f_* 𝒪_X)(V) ≅ Γ(X ×_Y V)` of Stacks 03G8, the map on global sections of the cartesian
projection `X ×_Y V ⟶ V` (`AlgebraicGeometry.Space.fSharp_app_comp_pushforwardAlgebraSectionsIso`).
So a property of ring maps which is invariant under composition with an isomorphism holds for the
structure-algebra map on an affine chart as soon as it holds for the global sections of the
projection.  This file draws the two consequences the source's proof of Stacks 0GUM uses; that the
direct image of an integral morphism is integral is
`AlgebraicGeometry.Space.isIntegral_pushforwardAlgebra_of_isIntegralHom`.

## Main results

* `AlgebraicGeometry.Space.pushforwardAlgebra_algebraMap_eq_comp`: the structure-algebra map of
  `f_* 𝒪_X` on a chart is the global-sections map of the cartesian projection followed by the
  inverse of the identification of Stacks 03G8.
* `AlgebraicGeometry.Space.exists_iso_comp_toScheme_map_snd`: a representative of the base change
  of `f` along a chart, given by any cartesian square, is isomorphic over the chart to the one
  chosen by relative representability, so their morphisms of schemes share every property
  invariant under isomorphism.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 0GUM](https://stacks.math.columbia.edu/tag/0GUM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- **The structure-algebra map of `f_* 𝒪_X` on an étale chart `V` of `Y`** is the map on global
sections of the cartesian projection `X ×_Y V ⟶ V`, followed by the inverse of the
identification `(f_* 𝒪_X)(V) ≅ Γ(X ×_Y V)` of Stacks 03G8. -/
theorem pushforwardAlgebra_algebraMap_eq_comp (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1) :
    ((smallEtaleRingedToposHom B S hS (Over.mk f).hom).fSharp.hom.app (op V)).hom =
      (pushforwardAlgebraSectionsIso B S hS (Over.mk f) hf V).inv.hom.comp
        ((BigFppfOver.toScheme B S hS).map (hf.snd V.1.hom)).appTop.hom :=
  (congrArg CommRingCat.Hom.hom ((Iso.eq_comp_inv _).2
    (fSharp_app_comp_pushforwardAlgebraSectionsIso B S hS (Over.mk f) hf V))).trans
    (CommRingCat.hom_comp _ _)

/-- **Any cartesian square computing the base change of `f` along a chart has the same
projection, up to isomorphism, as the one chosen by relative representability.**  Precisely:
given a cartesian square `q, yoneda.map p` over `f` and a morphism `g : yoneda.obj Z ⟶ Y`, the
chosen projection `hf.snd g` is the composite of an isomorphism with `p`, after passage to schemes.
-/
theorem exists_iso_comp_toScheme_map_snd (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) {Z W : BigFppfOver B S hS}
    (g : yoneda.obj Z ⟶ Y.1) (p : W ⟶ Z) (q : yoneda.obj W ⟶ X.1)
    (hpb : IsPullback q (yoneda.map p) f.hom g) :
    ∃ e : (BigFppfOver.toScheme B S hS).obj (hf.pullback g) ≅
        (BigFppfOver.toScheme B S hS).obj W,
      (BigFppfOver.toScheme B S hS).map (hf.snd g) =
        e.hom ≫ (BigFppfOver.toScheme B S hS).map p := by
  refine ⟨(BigFppfOver.toScheme B S hS).mapIso
    (Yoneda.fullyFaithful.preimageIso (IsPullback.isoIsPullback _ _ (hf.isPullback g) hpb)), ?_⟩
  rw [Functor.mapIso_hom, ← Functor.map_comp]
  exact congrArg _ (yoneda.map_injective (by simp))

end AlgebraicGeometry.Space

end
