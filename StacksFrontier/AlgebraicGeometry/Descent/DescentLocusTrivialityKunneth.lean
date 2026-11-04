module

public import StacksFrontier.AlgebraicGeometry.Descent.DescentLocusTriviality0BF3
public import StacksFrontier.AlgebraicGeometry.Descent.KunnethFirstCohomology
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatPushforwardPerfectBaseChange
public import StacksFrontier.AlgebraicGeometry.Cohomology.MinimalComplexFunctoriality.TrivialNearFibre
import StacksCore.Tactic.StacksAttribute

/-!
# Triviality near a fibre from trivial faces, by the Künneth formula

Let `f : X ⟶ S` and `g : Y ⟶ S` be flat, proper and of finite presentation, with
`𝒪_T ≅ f_{T,*}𝒪` and `𝒪_T ≅ g_{T,*}𝒪` after every base change and with sections `σ` of `f` and
`τ` of `g`. An invertible module `L` on `X ×_S Y` which is trivial on the two faces
`(1, τ ∘ f)` and `(σ ∘ g, 1)` and on the fibre over a point `s` of `S` is trivial over
`U ×_S (X ×_S Y)` for an open neighbourhood `U` of `s`: this is
[Stacks, Tag 0BF3](https://stacks.math.columbia.edu/tag/0BF3).

## Main results

* `AlgebraicGeometry.SheafOfModules.exists_isTrivial_on_open_of_isTrivial_faces`: Tag 0BF3,
  with the hypotheses of the source.

## References

* [Stacks Project, Tag 0BF3](https://stacks.math.columbia.edu/tag/0BF3)
* [Stacks Project, Tag 0BF2](https://stacks.math.columbia.edu/tag/0BF2)
* [Stacks Project, Tag 0BED](https://stacks.math.columbia.edu/tag/0BED)
* [Stacks Project, Tag 0FLQ](https://stacks.math.columbia.edu/tag/0FLQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

namespace SheafOfModules

section CohomologicalCriterion

open TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)
open Stacks.Cohomology.GlobalKunneth (sectionsOverBase baseRing sectionsPullbackMap)
open AlgebraicGeometry.ProperFlatBaseChange

attribute [local instance 10000] HasDerivedCategory.standard

/-- Let `f : X ⟶ S` and `g : Y ⟶ S` be flat, proper and of finite presentation with
`𝒪_T ≅ f_{T,*}𝒪` and `𝒪_T ≅ g_{T,*}𝒪` after every base change, with sections `σ` of `f` and `τ`
of `g`, and let `L` be invertible on `X ×_S Y`. If `L` is trivial on the two faces
`(1, τ ∘ f) : X ⟶ X ×_S Y` and `(σ ∘ g, 1) : Y ⟶ X ×_S Y` and on the fibre over `s`, then `L` is
trivial over `U ×_S (X ×_S Y)` for an open neighbourhood `U` of `s`. -/
@[stacks 0BF3]
theorem exists_isTrivial_on_open_of_isTrivial_faces
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [Flat f] [IsProper f] (hfp : FinitePresentation f)
    (hfO : ∀ {T : Scheme.{u}} (a : T ⟶ S),
      IsIso (structureSheafHom (pullback.snd f a).toLRSHom.toShHom))
    [Flat g] [IsProper g] (hgp : FinitePresentation g)
    (hgO : ∀ {T : Scheme.{u}} (a : T ⟶ S),
      IsIso (structureSheafHom (pullback.snd g a).toLRSHom.toShHom))
    (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)
    (τ : S ⟶ Y) (hτ : τ ≫ g = 𝟙 S)
    (s : S)
    (L : _root_.SheafOfModules.{u} (structureSheafRing (pullback f g).toRingedSpace))
    [IsInvertible (pullback f g).presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
        (pullback f g).IsSheaf) L]
    (hfaceX :
      let i : X ⟶ pullback f g :=
        pullback.lift (𝟙 X) (f ≫ τ) (by simp [Category.assoc, hτ])
      IsTrivial X.presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) X.IsSheaf)
        ((modulePullback i.toLRSHom.toShHom).obj L))
    (hfaceY :
      let i : Y ⟶ pullback f g :=
        pullback.lift (g ≫ σ) (𝟙 Y) (by simp [Category.assoc, hσ])
      IsTrivial Y.presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) Y.IsSheaf)
        ((modulePullback i.toLRSHom.toShHom).obj L))
    (hfiber :
      let P := pullback f g
      let p : P ⟶ S := pullback.fst f g ≫ f
      let W := pullback p (S.fromSpecResidueField s)
      IsTrivial W.presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) W.IsSheaf)
        ((modulePullback (pullback.fst p (S.fromSpecResidueField s)).toLRSHom.toShHom).obj L)) :
    ∃ U : S.Opens, s ∈ U ∧
      (let P := pullback f g
       let p : P ⟶ S := pullback.fst f g ≫ f
       let W := pullback p U.ι
       IsTrivial W.presheaf
         (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) W.IsSheaf)
         ((modulePullback (pullback.fst p U.ι).toLRSHom.toShHom).obj L)) := by
  let i₀ : X ⟶ pullback f g := pullback.lift (𝟙 X) (f ≫ τ) (by simp [Category.assoc, hτ])
  let i₁ : Y ⟶ pullback f g := pullback.lift (g ≫ σ) (𝟙 Y) (by simp [Category.assoc, hσ])
  have hi₀ : i₀ ≫ (pullback.fst f g ≫ f) = f := by
    rw [← Category.assoc, pullback.lift_fst, Category.id_comp]
  have hi₁ : i₁ ≫ (pullback.fst f g ≫ f) = g := by
    rw [← Category.assoc, pullback.lift_fst, Category.assoc, hσ, Category.comp_id]
  have := hfp.1
  have := hfp.2.1
  have := hfp.2.2
  have := hgp.1
  have := hgp.2.1
  have := hgp.2.2
  have hpfp : FinitePresentation (pullback.fst f g ≫ f) :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  let Xι : ULift.{u} Bool → Scheme.{u} := fun k => cond k.down X Y
  let iι : ∀ k, Xι k ⟶ pullback f g := fun k =>
    Bool.rec (motive := fun b => cond b X Y ⟶ pullback f g) i₁ i₀ k.down
  refine exists_isTrivial_modulePullback_fst_ι_of_injective_H1 (pullback.fst f g ≫ f) hpfp
    (KunnethFirstCohomology.isIso_structureSheafHom_pullback_snd_fst_comp f g hfO hgO)
    Xι iι ?_ ?_ ?_ ?_ L ?_ s hfiber ?hinj
  case hinj =>
    intro c hc
    exact KunnethFirstCohomology.eq_zero_of_sectionsPullbackMap_faces f g hfO hgO σ hσ τ hτ s
      c (hc ⟨true⟩) (hc ⟨false⟩)
  all_goals
    rintro ⟨_ | _⟩ <;> (try rw [hi₀]) <;> (try rw [hi₁]) <;> first | infer_instance | assumption

end CohomologicalCriterion

end SheafOfModules

end AlgebraicGeometry

end
