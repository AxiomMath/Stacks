module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackOpenVersalityFlat
public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.CoherentStackRelativeIdealSquareIdeals

/-!
# The ideal-square compatibility of `λ` at the test maps of square-zero thickenings

Let `x = (Spec A, ℱ)` be an object of `Coh_{X/B}` over an affine chart, with `Y` final and
`X → B` flat. For a morphism `f : A₁' → A₂'` of square-zero thickenings of `A`, the test maps
`Spec A ⊂ Spec Aₖ'` and `Spec A₂' ⟶ Spec A₁'` are morphisms of affine first order thickenings,
and the map `f'₁^*𝒥₁ ⟶ j_*f'₂^*𝒥₂` of `κ_g` is `j^♯` on the ideals there
(`AlgebraicGeometry.Space.CoherentSituation.relativeSquareIdealTranspose_idealMaps`). So the
ideal-square compatibility of
`AlgebraicGeometry.Space.CoherentSituation.relativeSquareIdealMap` at the test maps
(`AlgebraicGeometry.Space.CoherentSituation.TestRelativeIdealSquareCompatible`) follows from the
statement that this compatibility of the ideal maps gives the ideal-square compatibility of `λ`
for arbitrary morphisms of affine first order thickenings, which is taken here as a hypothesis.
With it, openness of versality for `Coh_{X/B}` with `X → B` flat (second proof of Stacks 08WA)
needs only the naturality of the tangent identification.

This module is a helper and carries no `@[stacks]` attribute.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.testRelativeIdealSquareCompatible_of_idealMaps`.
* `AlgebraicGeometry.Space.CoherentSituation.isOpenVersality_coherentCFG_of_isFlat_of_idealMaps`.

## References

* [Stacks Project, Tag 08WA](https://stacks.math.columbia.edu/tag/08WA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Deformation.Artin
open Deformation.ToposThickening

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Abelian.has_kernels Abelian.has_cokernels

universe u

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}

/-- **The ideal-square compatibility of `λ` from the ideal maps, for all affine first order
thickenings**: for morphisms `h₁ : T ⟶ T'₁`, `h₂ : T ⟶ T'₂`, `g : T'₂ ⟶ T'₁` of affine first
order thickenings with `h₂ ≫ g = h₁` and `X_{T'ₖ} → T'ₖ` flat, if the map
`f'₁^*𝒥₁ ⟶ j_*f'₂^*𝒥₂` of `κ_g` is `j^♯` on the ideals, then
`AlgebraicGeometry.Space.CoherentSituation.relativeSquareIdealMap` satisfies the ideal-square
compatibility of the relative squares of `h₁` and `h₂`. -/
abbrev RelativeIdealSquareCompatibleOfIdealMaps (D : CoherentSituation B S hS) : Prop :=
  ∀ {ξ : CoherentObject D} {T'₁ T'₂ : SchemesOver D.Y} (h₁ : ξ.T ⟶ T'₁) (h₂ : ξ.T ⟶ T'₂)
    (g : T'₂ ⟶ T'₁) (hg : h₂ ≫ g = h₁)
    (hh₁ : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h₁.left))
    (hh₂ : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h₂.left))
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ξ.T.left)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T'₁.left)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T'₂.left)]
    (hfl₁ : IsFlat B S hS (D.projection T'₁).hom) (hfl₂ : IsFlat B S hS (D.projection T'₂).hom),
    RelativeSquareIdealTransposeIdealMaps h₁ h₂ g hg hh₁ hh₂ →
      RelativeIdealSquareCompatible h₁ h₂ g hg hh₁ hh₂ hfl₁ hfl₂
        (relativeSquareIdealMap h₁ h₂ g hg hh₁ hh₂)

variable (hY : IsTerminal D.Y) (hflat : IsFlat B S hS D.f.hom)

/-- **The ideal-square compatibility of `λ` at the test maps**: for a morphism `f : A₁' → A₂'`
of square-zero thickenings of `A`, the map `λ` of the pulled-back ideals of the relative squares
of `Spec A ⊂ Spec A₁'` and `Spec A ⊂ Spec A₂'` is compatible with `Spec A₂' ⟶ Spec A₁'`, given
the ideal-square compatibility of `λ` from the ideal maps for all affine first order
thickenings. The surjectivity of `f` is not used. -/
theorem testRelativeIdealSquareCompatible_of_idealMaps
    (H : RelativeIdealSquareCompatibleOfIdealMaps D)
    (A : Type u) [CommRing A] (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
    (x : CoherentObject D) (hx : (coherentCFG D).val.p.obj x = algebraOver A B S hS toS hA)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj x.T.left)]
    (A₁ A₂ : Type u) [CommRing A₁] [CommRing A₂]
    (T₁ : SquareZeroThickening A B S hS toS hA A₁) (T₂ : SquareZeroThickening A B S hS toS hA A₂)
    (f : SquareZeroThickening.Hom T₁ T₂) (_ : Function.Surjective f.ringHom) :
    D.TestRelativeIdealSquareCompatible hY hflat hx f := by
  have hg := thickeningTestMap_comp_thickeningTestSchemeMap (hx := hx) hY f
  have h₁ := D.isFirstOrderThickening_thickeningTestMap hY x hx T₁
  have h₂ := D.isFirstOrderThickening_thickeningTestMap hY x hx T₂
  exact H _ _ _ hg h₁ h₂ (D.isFlat_projection_of_isFlat hflat _)
    (D.isFlat_projection_of_isFlat hflat _) (relativeSquareIdealTranspose_idealMaps _ _ _ hg h₁ h₂)

/-- **Openness of versality for `Coh_{X/B}` with `X → B` flat** (the second proof of Stacks
08WA), given the ideal-square compatibility of `λ` from the ideal maps for all affine first order
thickenings and the naturality of the tangent identification
`T_x(M) ≃ Ext¹_{X_A}(ℱ, ℱ ⊗ f^*M̃)` along surjections of modules, the latter granted the
ideal-square compatibility at `Spec A[N] ⟶ Spec A[M]`. -/
theorem isOpenVersality_coherentCFG_of_isFlat_of_idealMaps
    [_root_.AlgebraicGeometry.IsLocallyNoetherian S]
    (H : RelativeIdealSquareCompatibleOfIdealMaps D)
    (hτ : ∀ (A : Type u) [CommRing A] (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
      (x : CoherentObject D) (hx : (coherentCFG D).val.p.obj x = algebraOver A B S hS toS hA)
      [IsAffine ((BigFppfOver.toScheme B S hS).obj x.T.left)]
      {M N : SiteModule A B} (f : M ⟶ N), Function.Surjective f.hom →
      D.TestRelativeIdealSquareCompatible hY hflat hx
        (squareZeroModuleThickeningHom (S := S) (hS := hS) (toS := toS) (hA := hA) f) →
      ∀ (t : (tangentFunctor A B S hS toS hA (coherentCFG D).val.p x hx (coherentCFG D).2
        D.satisfiesRSStar_coherentCFG).functor.obj M),
      chartTangentEquiv hY hx N hflat D.satisfiesRSStar_coherentCFG
          ((tangentFunctor A B S hS toS hA (coherentCFG D).val.p x hx (coherentCFG D).2
            D.satisfiesRSStar_coherentCFG).functor.map f t) =
        D.extGroupMap x (D.chartRingEquiv x hx) f.hom 1
          (chartTangentEquiv hY hx M hflat D.satisfiesRSStar_coherentCFG t)) :
    HasOpenVersality ((coherentCFG D).val.p ⋙ Over.post B.inclusion) :=
  D.isOpenVersality_coherentCFG_of_isTerminal_of_isFlat hY hflat
    (testRelativeIdealSquareCompatible_of_idealMaps hY hflat H) hτ

end AlgebraicGeometry.Space.CoherentSituation

end
