module

public import StacksFrontier.AlgebraicGeometry.Descent.SurjectiveEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover

/-!
# Étaleness of a morphism of algebraic spaces is read off an étale chart

Étaleness of a morphism of algebraic spaces over `S` can be tested on one surjective étale
scheme chart of its source: the morphism is étale as soon as its composite with such a
chart is.

## Main results

* `AlgebraicGeometry.Space.isEtale_of_presheaf_etale_comp_chart`: a morphism of algebraic spaces
  whose composite with one surjective étale chart of its source is étale after every represented
  base change is étale.

## References

* [Stacks Project, Tag 03FS](https://stacks.math.columbia.edu/tag/03FS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Étaleness from one surjective étale chart of the source -/

variable {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A morphism of algebraic spaces over `S` is étale as soon as its composite with one
surjective étale chart of its source is étale after every represented base change. -/
theorem isEtale_of_presheaf_etale_comp_chart (hG : IsAlgebraicSpace B S hS G)
    {U : BigFppfOver B S hS} {p : yoneda.obj U ⟶ F}
    (hp_surj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p)
    (hp_etale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p)
    (f : F ⟶ G)
    (hpf : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (p ≫ f)) :
    IsEtale B S hS f := by
  intro T φ hφ
  set hrep := hp_etale.rep
  set χ := hrep.snd φ
  have sqp : IsPullback (hrep.fst φ) (yoneda.map χ) p φ := hrep.isPullback φ
  have hχsurj : Surjective ((BigFppfOver.toScheme B S hS).map χ) :=
    hp_surj.property φ (hrep.fst φ) χ sqp
  have hχetale : Etale ((BigFppfOver.toScheme B S hS).map χ) :=
    hp_etale.property φ (hrep.fst φ) χ sqp
  set δ := yoneda.preimage (hrep.fst φ) with hδdef
  have hδm : yoneda.map δ = hrep.fst φ := by simp [hδdef]
  have hδ : Etale ((BigFppfOver.toScheme B S hS).map δ) :=
    etale_of_comp_etale_chart B S hS (etale_comp_of_scheme B S hS χ φ hχetale hφ) hp_etale
      (by rw [hδm]; exact sqp.w)
  refine etale_of_comp_surjective_etale B S hS hG χ (φ ≫ f) ?_
  have h := etale_comp_of_scheme B S hS δ (p ≫ f) hδ hpf
  rwa [hδm, ← Category.assoc, sqp.w, Category.assoc] at h

end AlgebraicGeometry.Space

end
