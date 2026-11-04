module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardPushforwardUnitIso
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackSection

/-!
# Rigidity of invertible modules along a section

Let `f : X ⟶ B` be a morphism of algebraic spaces over a scheme `S`, the standing data of
Stacks 0D25, with a section `σ : B ⟶ X`, and let `T` be a test scheme over `B` for which the
structure map `𝒪_T ⟶ f_{T, *}𝒪_{X_T}` is an isomorphism.  This file proves that restriction
along the induced section `σ_T : T ⟶ X_T` is **bijective on homomorphisms between two isomorphic
invertible `𝒪_{X_T}`-modules**.

This is the step of the proof of Stacks 0D28 in which the units `u_{ij}` and the functions
`f_{ijk}` appear: an automorphism of an invertible module on `X_T` is multiplication by an
invertible function on `X_T`, the hypothesis identifies those functions with the functions on
`T`, and so an automorphism is determined by — and can be prescribed through — its pullback by
`σ_T`.  Here no units are named.  The argument is categorical:

* `σ_T^* ∘ f_T^*` is isomorphic to the identity, because `σ_T` is a section of `f_T`;
* `f_T^*` is bijective on the endomorphisms of `𝒪_T`, because the unit `𝒪_T ⟶ f_{T, *}f_T^*𝒪_T`
  is an isomorphism (`AlgebraicGeometry.Space.modulePushforwardUnitIso`, the first paragraph of
  the proof of Stacks 0D27);
* hence `σ_T^*` is bijective on the endomorphisms of `f_T^*𝒪_T ≅ 𝒪_{X_T}`, and tensoring by an
  invertible module carries this to every invertible module
  (`AlgebraicGeometry.Space.bijective_modulePullback_map_end_of_isInvertibleModule`).

## Main results

* `CategoryTheory.Functor.bijective_map_of_retraction`: if `F ⋙ G ≅ 𝟭` and `F` is bijective
  on the endomorphisms of `d`, then `G` is bijective on the endomorphisms of `F d`.
* `AlgebraicGeometry.Space.PicardSituation.bijective_sectionPullback_map_end_structureModule`:
  `σ_T^*` is bijective on the endomorphisms of `𝒪_{X_T}`.
* `AlgebraicGeometry.Space.PicardSituation.bijective_sectionPullback_map`: **`σ_T^*` is
  bijective on the homomorphisms between two isomorphic invertible `𝒪_{X_T}`-modules.**

## References

* [Stacks Project, Tag 0D28](https://stacks.math.columbia.edu/tag/0D28)
* [Stacks Project, Tag 0D27](https://stacks.math.columbia.edu/tag/0D27)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

/-- **Bijectivity on endomorphisms passes to a retraction.**  If `F ⋙ G` is isomorphic to the
identity and `F` is bijective on the endomorphisms of `d`, then `G` is bijective on the
endomorphisms of `F d`: on `End(d)` the composite `G ∘ F` is conjugation by the isomorphism
`G (F d) ≅ d`. -/
theorem bijective_map_of_retraction (F : D ⥤ C) (G : C ⥤ D) (e : F ⋙ G ≅ 𝟭 D) (d : D)
    (hF : Function.Bijective (fun φ : d ⟶ d ↦ F.map φ)) :
    Function.Bijective (fun φ : F.obj d ⟶ F.obj d ↦ G.map φ) := by
  have h : (fun φ : F.obj d ⟶ F.obj d ↦ G.map φ) ∘ (fun φ : d ⟶ d ↦ F.map φ) =
      ((e.app d).homCongr (e.app d)).symm := by
    funext φ
    exact (NatIso.naturality_2 e φ).symm
  rw [← Function.Bijective.of_comp_iff _ hF, h]
  exact Equiv.bijective _

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space.PicardSituation

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {s : PicardSituation B S hS} (σ : s.base ⟶ s.X) (hσ : σ ≫ s.f = 𝟙 s.base)

/-- **Restriction along the section retracts pullback along the projection**: `σ_T^* ∘ f_T^*`
is isomorphic to the identity of the `𝒪_T`-modules, through the comparison of Stacks 03LU for
`σ_T ≫ f_T = 𝟙_T`. -/
def sectionPullbackRetraction (T : s.SchemesOver) :
    modulePullback B S hS (baseChangeInclusion s.f T) ⋙
        modulePullback B S hS (baseChangeSection σ hσ T) ≅ 𝟭 _ :=
  modulePullbackCompIso B S hS (baseChangeSection σ hσ T) (baseChangeInclusion s.f T) ≪≫
    eqToIso (congrArg (modulePullback B S hS) (baseChangeSection_comp_inclusion σ hσ T)) ≪≫
    (modulePushforwardCoherence B S hS).modulePullbackIdIso _

/-- **`σ_T^*` is bijective on the endomorphisms of `𝒪_{X_T}`** when the structure map
`𝒪_T ⟶ f_{T, *}𝒪_{X_T}` is an isomorphism. -/
theorem bijective_sectionPullback_map_end_structureModule {T : s.SchemesOver}
    (h : IsIso (s.structureSheafMap T)) :
    Function.Bijective (fun φ : structureModule (s.baseChange T) ⟶
        structureModule (s.baseChange T) ↦
      (modulePullback B S hS (baseChangeSection σ hσ T)).map φ) := by
  have hF := bijective_modulePullback_map_of_isInvertibleModule (baseChangeInclusion s.f T) h
    (structureModule (s.baseSpaceAt T)) (isInvertibleModule_structureModule (s.baseSpaceAt T))
  have hG := Functor.bijective_map_of_retraction _ _ (sectionPullbackRetraction σ hσ T) _ hF
  exact (Functor.bijective_map_iff_of_iso _
    (modulePullbackUnitIso B S hS (baseChangeInclusion s.f T))
    (modulePullbackUnitIso B S hS (baseChangeInclusion s.f T))).1 hG

/-- **Rigidity along the section.**  When the structure map `𝒪_T ⟶ f_{T, *}𝒪_{X_T}` is an
isomorphism, restriction along `σ_T` is a bijection from the homomorphisms `P ⟶ Q` between two
isomorphic invertible `𝒪_{X_T}`-modules to the homomorphisms `σ_T^*P ⟶ σ_T^*Q`. -/
theorem bijective_sectionPullback_map {T : s.SchemesOver} (h : IsIso (s.structureSheafMap T))
    {P Q : Modules.{u, u} B S hS (s.baseChange T).1 (s.baseChange T).2}
    (hP : IsInvertibleModule (s.baseChange T) P) (e : P ≅ Q) :
    Function.Bijective (fun φ : P ⟶ Q ↦
      (modulePullback B S hS (baseChangeSection σ hσ T)).map φ) := by
  have hend := bijective_modulePullback_map_end_of_isInvertibleModule
    (baseChangeSection σ hσ T) hP (bijective_sectionPullback_map_end_structureModule σ hσ h)
  exact (Functor.bijective_map_iff_of_iso _ (Iso.refl P) e).1 hend

end AlgebraicGeometry.Space.PicardSituation

end
