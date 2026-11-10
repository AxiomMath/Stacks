module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImageDimensionShift

/-!
# Higher direct images along a limit: the inductive step

The inductive step of the first proof of [Stacks, Tag 0EYM]: the colimit assertion in degree
`p + 1` for a system `ℱ_•` follows from the assertion in degree `p` for a system `𝒢_•` of
injective sheaves containing it and for the quotient `𝒬_•`, together with the vanishing of
`R^{p+1}g_*` at the colimit of `𝒢_•`. The compatibilities of the connecting morphisms with the
maps of the diagram and of the cocone are
`Stacks.EtaleCohomology.LimitHigherDirectImage.higherDirectImageDiagramMap_comp_δ` and
`Stacks.EtaleCohomology.LimitHigherDirectImage.projectionMap_comp_δ`; what remains is that
cokernels commute with colimits of systems,
`CategoryTheory.Limits.IsSystemColimit.of_cokernel`.

## Main results

* `Stacks.EtaleCohomology.LimitHigherDirectImage.isHigherDirectImageColimit_succ` — **the
  dimension shift**.

## References

* [Stacks Project, Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe v u

namespace Stacks.EtaleCohomology.LimitHigherDirectImage

attribute [local instance] HasDerivedCategory.standard

variable {I : Type v} [Preorder I] {DX DS : Iᵒᵖ ⥤ Scheme.{u}} (γ : DX ⟶ DS) (p : ℕ)
  (cX : Cone DX) (cS : Cone DS) (hcS : IsLimit cS)
  {F G Q : EtaleSheafSystem DX Ab.{u + 1}} (α : ∀ i, F.obj i ⟶ G.obj i)
  (β : ∀ i, G.obj i ⟶ Q.obj i) (hαβ : ∀ i, α i ≫ β i = 0)
  (hE : ∀ i, (ShortComplex.mk (α i) (β i) (hαβ i)).ShortExact)
  {𝓕 𝓖 𝓠 : Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1}}
  (ιF : ∀ i, (smallEtalePullbackAb (cX.π.app i)).obj (F.obj i) ⟶ 𝓕)
  (ιG : ∀ i, (smallEtalePullbackAb (cX.π.app i)).obj (G.obj i) ⟶ 𝓖)
  (ιQ : ∀ i, (smallEtalePullbackAb (cX.π.app i)).obj (Q.obj i) ⟶ 𝓠)
  (u : 𝓕 ⟶ 𝓖) (v : 𝓖 ⟶ 𝓠) (huv : u ≫ v = 0) (hlim : (ShortComplex.mk u v huv).ShortExact)
  (hu : ∀ i, (smallEtalePullbackAb (cX.π.app i)).map (α i) ≫ ιG i = ιF i ≫ u)
  (hv : ∀ i, (smallEtalePullbackAb (cX.π.app i)).map (β i) ≫ ιQ i = ιG i ≫ v)

include hE in
/-- In positive degree the connecting morphism of the higher direct images of a short exact
sequence whose middle term is injective is an epimorphism, and so is its inverse image. -/
theorem epi_map_δ_of_injective [∀ i, Injective (G.obj i)] (i : Iᵒᵖ) :
    Epi ((smallEtalePullbackAb (cS.π.app i)).map
      ((Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
        (smallEtalePushforwardAb (γ.app i))).δ (hE i) p)) := by
  have : Epi ((Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
      (smallEtalePushforwardAb (γ.app i))).δ (hE i) p) :=
    DeltaFunctor.epi_δ_of_map_f_eq_zero _ (hE i) p
      ((Functor.isZero_rightDerived_obj_injective_succ _ p (G.obj i)).eq_of_tgt _ _)
  infer_instance

include hE in
/-- The inverse image of the map `R^p g_{i,*} 𝒢_i ⟶ R^p g_{i,*} 𝒬_i` composed with the inverse
image of the connecting morphism `R^p g_{i,*} 𝒬_i ⟶ R^{p+1} g_{i,*} ℱ_i` is zero. -/
theorem map_comp_map_δ (i : Iᵒᵖ) :
    (smallEtalePullbackAb (cS.π.app i)).map
        (((smallEtalePushforwardAb (γ.app i)).rightDerived p).map (β i)) ≫
      (smallEtalePullbackAb (cS.π.app i)).map
        ((Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
          (smallEtalePushforwardAb (γ.app i))).δ (hE i) p) = 0 :=
  ((smallEtalePullbackAb (cS.π.app i)).map_comp _ _).symm.trans
    ((congrArg (smallEtalePullbackAb (cS.π.app i)).map
      ((Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
        (smallEtalePushforwardAb (γ.app i))).map_g_δ (hE i) p)).trans (Functor.map_zero _ _ _))

variable {α β} in
include hE hu hv hlim in
/-- **The dimension shift of the first proof of [Stacks, Tag 0EYM].** Let
`0 ⟶ ℱ_• ⟶ 𝒢_• ⟶ 𝒬_• ⟶ 0` be a short exact sequence of systems with injective `𝒢_i`, and let
`0 ⟶ ℱ ⟶ 𝒢 ⟶ 𝒬 ⟶ 0` be a short exact sequence on the limit presenting the three colimits
compatibly. If `R^{p+1}g_*𝒢 = 0` and the colimit assertion holds in degree `p` for `𝒢_•` and for
`𝒬_•`, then it holds in degree `p + 1` for `ℱ_•`. -/
theorem isHigherDirectImageColimit_succ [∀ i, Injective (G.obj i)]
    (hα : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      (systemPullback DX Ab.{u + 1} a).map (α j) ≫ G.map a = F.map a ≫ α i)
    (hβ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      (systemPullback DX Ab.{u + 1} a).map (β j) ≫ Q.map a = G.map a ≫ β i)
    (hvan : IsZero (((smallEtalePushforwardAb (limitMorphism γ cX cS hcS)).rightDerived
      (p + 1)).obj 𝓖))
    (hG : IsHigherDirectImageColimit γ p cX cS hcS 𝓖 G ιG)
    (hQ : IsHigherDirectImageColimit γ p cX cS hcS 𝓠 Q ιQ) :
    IsHigherDirectImageColimit γ (p + 1) cX cS hcS 𝓕 F ιF :=
  isHigherDirectImageColimit_iff_isSystemColimit.mpr <| IsSystemColimit.of_cokernel
    (A := fun i => (smallEtalePullbackAb (cS.π.app i)).obj
      (((smallEtalePushforwardAb (γ.app i)).rightDerived p).obj (G.obj i)))
    (B := fun i => (smallEtalePullbackAb (cS.π.app i)).obj
      (((smallEtalePushforwardAb (γ.app i)).rightDerived p).obj (Q.obj i)))
    (C := fun i => (smallEtalePullbackAb (cS.π.app i)).obj
      (((smallEtalePushforwardAb (γ.app i)).rightDerived (p + 1)).obj (F.obj i)))
    (TA := fun a => higherDirectImageDiagramMap γ p cS G a)
    (TB := fun a => higherDirectImageDiagramMap γ p cS Q a)
    (TC := fun a => higherDirectImageDiagramMap γ (p + 1) cS F a)
    (α := projectionMap γ cX cS hcS p 𝓖 G ιG)
    (β := projectionMap γ cX cS hcS p 𝓠 Q ιQ)
    (fun i => (smallEtalePullbackAb (cS.π.app i)).map
      (((smallEtalePushforwardAb (γ.app i)).rightDerived p).map (β i)))
    (fun i => (smallEtalePullbackAb (cS.π.app i)).map
      ((Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
        (smallEtalePushforwardAb (γ.app i))).δ (hE i) p))
    (map_comp_map_δ γ p cS α β hαβ hE) (epi_map_δ_of_injective γ p cS α β hαβ hE)
    (fun a => higherDirectImageDiagramMap_comp_δ γ p cS hαβ hE hα hβ a)
    (projectionMap γ cX cS hcS (p + 1) 𝓕 F ιF)
    (isHigherDirectImageColimit_iff_isSystemColimit.mp hG)
    (isHigherDirectImageColimit_iff_isSystemColimit.mp hQ)
    (((smallEtalePushforwardAb (limitMorphism γ cX cS hcS)).rightDerived p).map v)
    ((Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
      (smallEtalePushforwardAb (limitMorphism γ cX cS hcS))).δ hlim p)
    (fun i => (projectionMap_naturality γ cX cS hcS p 𝓖 ιG ιQ β v hv i).symm)
    (fun i => projectionMap_comp_δ γ p cX cS hcS α β hαβ hE ιF ιG ιQ u v huv hlim hu hv i)
    ((Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
      (smallEtalePushforwardAb (limitMorphism γ cX cS hcS))).δIsCokernel hlim p
        (hvan.eq_of_tgt _ _))

end Stacks.EtaleCohomology.LimitHigherDirectImage
