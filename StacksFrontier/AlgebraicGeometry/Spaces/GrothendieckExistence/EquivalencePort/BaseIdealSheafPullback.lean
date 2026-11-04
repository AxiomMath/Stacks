module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.InverseImageIdealCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.BaseIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.DirectImageCompletionComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts

/-!
# The inverse image of `I 𝒪_X` is `I 𝒪_{X'}`

For a representable morphism `π : X' ⟶ X` of algebraic spaces over `Spec A` and an ideal `I` of
`A`, the inverse-image ideal `π⁻¹(I 𝒪_X) 𝒪_{X'}` is `I 𝒪_{X'}`.

## Main results

* `AlgebraicGeometry.Space.C1573.chartIdealPullbackHom_baseChartHom`: a scalar of the base pulls
  back to itself along small-chart base change.
* `AlgebraicGeometry.Space.C1573.inverseImageIdeal_baseIdealSheaf`: the inverse image of `I 𝒪_X`
  along a representable morphism `X' ⟶ X` is `I 𝒪_{X'}`.
-/

namespace Stacks.Ideal.C1573
end Stacks.Ideal.C1573
namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/-- Three successive extensions of an ideal along ring maps whose composite is `k`, starting from
the extension of `I` along the first, are the extension of `I` along `k`. -/
theorem Stacks.Ideal.C1573.map_map_map_of_comp {R₁ R₂ R₃ R₄ : Type*} [CommSemiring R₁]
    [CommSemiring R₂] [CommSemiring R₃] [CommSemiring R₄] (h : R₁ →+* R₂) (f : R₂ →+* R₃)
    (g : R₃ →+* R₄) (k : R₁ →+* R₄) (hk : ∀ a, g (f (h a)) = k a) (I : Ideal R₁) {J : Ideal R₂}
    (hJ : J = Ideal.map h I) : Ideal.map g (Ideal.map f J) = Ideal.map k I := by
  rw [hJ, Ideal.map_map, Ideal.map_map]
  congr 1
  exact RingHom.ext hk

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.Space.C1573
variable {B : BigFppfSite.{u}} {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))}

/-- A scalar of the base restricts to itself along a morphism of étale charts. -/
theorem C1573.chartSectionsRestrict_baseChartHom (X : AlgebraicSpaces B (Spec (.of A)) hA)
    {U V : SmallEtale B (Spec (.of A)) hA X.1} (mm : V ⟶ U) (a : A) :
    chartSectionsRestrict B (Spec (.of A)) hA X mm (specBaseChartHom X.1 X.2 U a) =
      specBaseChartHom X.1 X.2 V a :=
  (baseRingHom A B hA X.1 X.2 a).2 mm.op

/-- A scalar of the base pulls back to itself along small-chart base change. -/
theorem C1573.chartIdealPullbackHom_baseChartHom {X X' : AlgebraicSpaces B (Spec (.of A)) hA}
    (π : X' ⟶ X) (hπ : yoneda.relativelyRepresentable π.hom)
    (Q : SmallEtale B (Spec (.of A)) hA X.1) (a : A) :
    chartIdealPullbackHom B (Spec (.of A)) hA π hπ Q (specBaseChartHom X.1 X.2 Q a) =
      specBaseChartHom X'.1 X'.2 ((smallBaseChange B (Spec (.of A)) hA π hπ).obj Q) a := by
  have hw := Over.w (hπ.snd Q.1.hom)
  show (Scheme.Γ.map (B.inclusion.map (hπ.snd Q.1.hom).left).op)
      (((Scheme.ΓSpecIso (.of A)).inv ≫
        Scheme.Γ.map ((B.inclusion.map
          ((SmallEtale.toOver B (Spec (.of A)) hA X.1).obj Q).hom).op)).hom a) =
    ((Scheme.ΓSpecIso (.of A)).inv ≫ Scheme.Γ.map ((B.inclusion.map
      ((SmallEtale.toOver B (Spec (.of A)) hA X'.1).obj
        ((smallBaseChange B (Spec (.of A)) hA π hπ).obj Q)).hom).op)).hom a
  have hw' : ((SmallEtale.toOver B (Spec (.of A)) hA X'.1).obj
      ((smallBaseChange B (Spec (.of A)) hA π hπ).obj Q)).hom =
        (hπ.snd Q.1.hom).left ≫ ((SmallEtale.toOver B (Spec (.of A)) hA X.1).obj Q).hom := hw.symm
  rw [hw']
  rfl

/-- **The inverse image of `I 𝒪_X` along a representable morphism is `I 𝒪_{X'}`.** -/
theorem C1573.inverseImageIdeal_baseIdealSheaf {X X' : AlgebraicSpaces B (Spec (.of A)) hA}
    (π : X' ⟶ X) (hπ : yoneda.relativelyRepresentable π.hom) (I : Ideal A) :
    inverseImageIdeal B (Spec (.of A)) hA π hπ (baseIdealSubmodule X.1 X.2 I) =
      baseIdealSubmodule X'.1 X'.2 I := by
  have hI : IsCartesianOnAffineCharts (hF := X.2) (baseIdealSubmodule X.1 X.2 I).toSheafOfModules :=
    isCartesianOnAffineCharts_of_isQuasicoherentOnSite B (Spec (.of A)) hA X.1 X.2 _
      (isQuasicoherentOnSite_baseIdealSubmodule (X := X.1) (hX := X.2) I)
  have key : ∀ (T₁ : SmallEtale B (Spec (.of A)) hA X'.1), IsAffine (chartScheme T₁) →
      ∀ (Q : SmallEtale B (Spec (.of A)) hA X.1), IsAffine (chartScheme Q) →
        (T₁ ⟶ (smallBaseChange B (Spec (.of A)) hA π hπ).obj Q) →
        (inverseImageIdeal B (Spec (.of A)) hA π hπ (baseIdealSubmodule X.1 X.2 I)).obj (op T₁) =
          (baseIdealSubmodule X'.1 X'.2 I).obj (op T₁) := by
    intro T₁ hT₁ Q hQ v
    have h1 := pullbackIdealSubsheaf_obj_of_isAffine B (Spec (.of A)) hA π hπ _ hI Q hQ T₁ v hT₁
    have h2 := chartIdeal_baseIdealSubmodule_of_isAffine (hX := X.2) I Q hQ
    have h3 := chartIdeal_baseIdealSubmodule_of_isAffine (hX := X'.2) I T₁ hT₁
    refine h1.trans (Eq.trans ?_ h3.symm)
    show Ideal.map (chartSectionsRestrict B (Spec (.of A)) hA X' v)
      (Ideal.map (chartIdealPullbackHom B (Spec (.of A)) hA π hπ Q)
        (chartIdeal B (Spec (.of A)) hA X (baseIdealSubmodule X.1 X.2 I) Q)) = _
    refine Stacks.Ideal.C1573.map_map_map_of_comp (specBaseChartHom X.1 X.2 Q) _ _
      (specBaseChartHom X'.1 X'.2 T₁) (fun a => ?_) I h2
    show chartSectionsRestrict B (Spec (.of A)) hA X' v
      (chartIdealPullbackHom B (Spec (.of A)) hA π hπ Q (specBaseChartHom X.1 X.2 Q a)) =
        specBaseChartHom X'.1 X'.2 T₁ a
    rw [chartIdealPullbackHom_baseChartHom, chartSectionsRestrict_baseChartHom]
  have hle : ∀ {N₁ N₂ : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of A)) hA X'.1 X'.2).O))).Submodule},
      (∀ (T₁ : SmallEtale B (Spec (.of A)) hA X'.1), IsAffine (chartScheme T₁) →
        ∀ (Q : SmallEtale B (Spec (.of A)) hA X.1), IsAffine (chartScheme Q) →
          (T₁ ⟶ (smallBaseChange B (Spec (.of A)) hA π hπ).obj Q) →
          N₁.obj (op T₁) = N₂.obj (op T₁)) → N₁ ≤ N₂ := by
    intro N₁ N₂ h U s hs
    refine N₂.isSheaf s ?_
    exact mem_topology_of_affine_over_smallBaseChange B (Spec (.of A)) hA π hπ U.unop _
      fun g hT₁ Q hQ v => by
        exact (SetLike.ext_iff.1 (h _ hT₁ Q hQ v) _).1 (N₁.map_mem g.op hs)
  exact le_antisymm (hle key) (hle fun T₁ hT₁ Q hQ v => (key T₁ hT₁ Q hQ v).symm)

end AlgebraicGeometry.Space

end
