module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Composition
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Perfect
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.RegularImmersion
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Syntomic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.Implications
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeRegularImmersion.SyntomicIntoSmooth
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.AffineSpaceImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Properties
public import StacksFrontier.AlgebraicGeometry.Morphisms.SyntomicScheme

/-!
# Zariski locality of the Koszul property, and its syntomic source locality

The property of being a local complete intersection morphism of schemes is Zariski local on the
source and on the target, and it is preserved by precomposition with a syntomic morphism. It is
therefore syntomic local on the source provided that a morphism of affine schemes is Koszul as
soon as its precomposition with a surjective syntomic morphism of affine schemes is.

## Main results

* `AlgebraicGeometry.isZariskiLocalAtSource_isLocalCompleteIntersectionMorphism`: the Koszul
  property is Zariski local on the source.
* `AlgebraicGeometry.isZariskiLocalAtTarget_isLocalCompleteIntersectionMorphism`: the Koszul
  property is Zariski local on the target.
* `AlgebraicGeometry.respectsLeft_syntomic_isLocalCompleteIntersectionMorphism`: the Koszul
  property is preserved by precomposition with a syntomic morphism.
* `AlgebraicGeometry.isLocalCompleteIntersectionMorphism_isLocalAtSource_syntomic`: the Koszul
  property is syntomic local on the source, given the affine case of the descent as the
  hypothesis `hAffine`.
* `AlgebraicGeometry.affine_descent_of_isLocalAtSource_syntomic`: conversely, syntomic locality
  on the source implies the affine case of the descent.

## References

* [The Stacks Project, Lemma 35.26.4 (036H)](https://stacks.math.columbia.edu/tag/036H)
* [The Stacks Project, Definition 37.62.2 (069F)](https://stacks.math.columbia.edu/tag/069F)
* [The Stacks Project, Lemma 37.62.6 (069I)](https://stacks.math.columbia.edu/tag/069I)
* [The Stacks Project, Lemma 37.62.7 (069J)](https://stacks.math.columbia.edu/tag/069J)
* [The Stacks Project, Lemma 37.62.8 (069K)](https://stacks.math.columbia.edu/tag/069K)
* [The Stacks Project, Lemma 37.62.20 (069P)](https://stacks.math.columbia.edu/tag/069P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace AlgebraicGeometry

/-- Being a local complete intersection morphism is invariant under isomorphisms of the source
and of the target. -/
private instance respectsIso_koszul :
    MorphismProperty.RespectsIso
      (@IsLocalCompleteIntersectionMorphism.{u} : MorphismProperty Scheme.{u}) :=
  MorphismProperty.RespectsIso.mk _
    (fun e f hf ↦ isLocalCompleteIntersectionMorphism_comp e.hom f
      (isLocalCompleteIntersectionMorphism_of_isOpenImmersion e.hom) hf)
    fun e f hf ↦ isLocalCompleteIntersectionMorphism_comp f e.hom hf
      (isLocalCompleteIntersectionMorphism_of_isOpenImmersion e.hom)

/-- If a Koszul-regular immersion `j` of an open `V` of an open `U` of the source of `f` into a
scheme smooth over the target factors the restriction of `f`, then `f` is Koszul at every point
of `V`. -/
private theorem koszulAt_of_opens {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (U : X.Opens) {P : Scheme.{u}} {V : U.toScheme.Opens} (j : V.toScheme ⟶ P) [IsImmersion j]
    (π : P ⟶ S) [Smooth π] (hkos : IsKoszulRegularImmersion j)
    (hfac : V.ι ≫ U.ι ≫ f = j ≫ π) (x : U.toScheme) (hxV : x ∈ V) :
    KoszulAt f (U.ι x) := by
  have hrange : Set.range (V.ι ≫ U.ι).base = Set.range (U.ι ''ᵁ V).ι.base := by
    have h₁ : (V.ι ≫ U.ι).opensRange = U.ι ''ᵁ V := by
      rw [← Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.comp_image,
        Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
    have h₂ : (U.ι ''ᵁ V).ι.opensRange = U.ι ''ᵁ V := Scheme.Opens.opensRange_ι _
    exact congrArg (fun W : X.Opens => (W : Set X)) (h₁.trans h₂.symm)
  let e : V.toScheme ≅ (U.ι ''ᵁ V).toScheme :=
    IsOpenImmersion.isoOfRangeEq (V.ι ≫ U.ι) (U.ι ''ᵁ V).ι hrange
  have he : e.hom ≫ (U.ι ''ᵁ V).ι = V.ι ≫ U.ι :=
    IsOpenImmersion.isoOfRangeEq_hom_fac (V.ι ≫ U.ι) (U.ι ''ᵁ V).ι hrange
  have hι : (U.ι ''ᵁ V).ι = e.inv ≫ V.ι ≫ U.ι := by
    rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  refine ⟨finiteTypeAt_of_locallyOfFiniteType f _, U.ι ''ᵁ V,
    (Scheme.Opens.mem_ι_image_iff U).mpr hxV, P, e.inv ≫ j, π, inferInstance,
    isKoszulRegularImmersion_comp_iso e.symm j hkos, inferInstance, ?_⟩
  rw [hι, Category.assoc, Category.assoc, hfac, Category.assoc]

/-- The Koszul property of morphisms of schemes is Zariski local on the source: a morphism is a
local complete intersection morphism exactly when its restriction to every member of an open
cover of its source is. -/
instance isZariskiLocalAtSource_isLocalCompleteIntersectionMorphism :
    IsZariskiLocalAtSource
      (@IsLocalCompleteIntersectionMorphism.{u} : MorphismProperty Scheme.{u}) := by
  refine IsZariskiLocalAtSource.mk' (fun {X Y} f U hf => ?_) (fun {X Y} f {ι} U hU hf => ?_)
  · exact isLocalCompleteIntersectionMorphism_comp U.ι f
      (isLocalCompleteIntersectionMorphism_of_isOpenImmersion U.ι) hf
  · have hft : LocallyOfFiniteType f := by
      let : IsZariskiLocalAtSource (@LocallyOfFiniteType) :=
        HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FiniteType)
      refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @LocallyOfFiniteType) U hU fun i => ?_
      exact locallyOfFiniteType_of_isLocalCompleteIntersectionMorphism (hf i)
    intro x
    obtain ⟨i, hxi⟩ : ∃ i, x ∈ U i := by
      simpa using show x ∈ (⨆ i, U i : X.Opens) from hU ▸ trivial
    obtain ⟨-, V, hxV, P, j, π, hj, hkos, hπ, hfacV⟩ := hf i ⟨x, hxi⟩
    let _ : IsImmersion j := hj
    let _ : Smooth π := hπ
    exact koszulAt_of_opens f (U i) j π hkos (by rwa [← Category.assoc]) ⟨x, hxi⟩ hxV

/-- The Koszul property of morphisms of schemes is Zariski local on the target: a morphism is a
local complete intersection morphism exactly when its restriction over every member of an open
cover of its target is. -/
instance isZariskiLocalAtTarget_isLocalCompleteIntersectionMorphism :
    IsZariskiLocalAtTarget
      (@IsLocalCompleteIntersectionMorphism.{u} : MorphismProperty Scheme.{u}) := by
  refine IsZariskiLocalAtTarget.mk' (fun {X Y} f U hf => ?_) (fun {X Y} f {ι} U hU hf => ?_)
  · have hpb := (isPullback_morphismRestrict f U).flip
    rw [← hpb.isoPullback_hom_snd, MorphismProperty.cancel_left_of_respectsIso
      (@IsLocalCompleteIntersectionMorphism.{u} : MorphismProperty Scheme.{u})
      hpb.isoPullback.hom (pullback.snd f U.ι)]
    exact isLocalCompleteIntersectionMorphism_pullback_snd f U.ι hf
  · have hft : LocallyOfFiniteType f := by
      let : IsZariskiLocalAtTarget (@LocallyOfFiniteType) :=
        HasRingHomProperty.instIsZariskiLocalAtTarget (P := @LocallyOfFiniteType)
          (Q := RingHom.FiniteType)
      refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @LocallyOfFiniteType) U hU fun i => ?_
      exact locallyOfFiniteType_of_isLocalCompleteIntersectionMorphism (hf i)
    intro x
    obtain ⟨i, hxi⟩ : ∃ i, f.base x ∈ U i := by
      simpa using show f.base x ∈ (⨆ i, U i : Y.Opens) from hU ▸ trivial
    have hxpre : x ∈ f ⁻¹ᵁ U i := hxi
    obtain ⟨-, V, hxV, P, j, π, hj, hkos, hπ, hfacV⟩ := hf i ⟨x, hxpre⟩
    let _ : IsImmersion j := hj
    let _ : Smooth π := hπ
    have hsm : Smooth (π ≫ (U i).ι) := MorphismProperty.comp_mem _ _ _ hπ inferInstance
    have hfac : V.ι ≫ (f ⁻¹ᵁ U i).ι ≫ f = j ≫ π ≫ (U i).ι := by
      rw [← morphismRestrict_ι f (U i), ← Category.assoc, ← Category.assoc, hfacV,
        Category.assoc]
    exact koszulAt_of_opens f (f ⁻¹ᵁ U i) j (π ≫ (U i).ι) hkos hfac ⟨x, hxpre⟩ hxV

/-- The Koszul property of morphisms of schemes is preserved by precomposition with a syntomic
morphism. -/
instance respectsLeft_syntomic_isLocalCompleteIntersectionMorphism :
    MorphismProperty.RespectsLeft
      (@IsLocalCompleteIntersectionMorphism.{u} : MorphismProperty Scheme.{u})
      (@Syntomic.{u} : MorphismProperty Scheme.{u}) :=
  ⟨fun i hi f hf => isLocalCompleteIntersectionMorphism_comp i f
    (isLocalCompleteIntersectionMorphism_of_syntomic hi) hf⟩

/-- Suppose that, for every surjective syntomic morphism `g` of affine schemes, a morphism `f` of
affine schemes is a local complete intersection morphism as soon as `g ≫ f` is (`hAffine`).
Then the property of being a local complete intersection morphism of schemes is syntomic local
on the source: a morphism is Koszul exactly when its composites with the members of a syntomic
covering of its source are. -/
theorem isLocalCompleteIntersectionMorphism_isLocalAtSource_syntomic
    (hAffine : ∀ {X' X Y : Scheme.{u}} [IsAffine X'] [IsAffine X] [IsAffine Y]
      (g : X' ⟶ X) (f : X ⟶ Y), Surjective g → Syntomic g →
        IsLocalCompleteIntersectionMorphism (g ≫ f) →
        IsLocalCompleteIntersectionMorphism f) :
    MorphismProperty.IsLocalAtSource
      (@IsLocalCompleteIntersectionMorphism.{u} : MorphismProperty Scheme.{u})
      (Scheme.precoverage (@Syntomic.{u})) :=
  isLocalAtSource_syntomic_of_affine_descent
    (@IsLocalCompleteIntersectionMorphism.{u} : MorphismProperty Scheme.{u}) hAffine

/-- If the property of being a local complete intersection morphism is syntomic local on the
source, then `f` is a local complete intersection morphism as soon as `g ≫ f` is, for a
surjective syntomic morphism `g`. -/
theorem affine_descent_of_isLocalAtSource_syntomic
    (hsrc : MorphismProperty.IsLocalAtSource
      (@IsLocalCompleteIntersectionMorphism.{u} : MorphismProperty Scheme.{u})
      (Scheme.precoverage (@Syntomic.{u})))
    {X' X Y : Scheme.{u}} (g : X' ⟶ X) (f : X ⟶ Y) (hgsurj : Surjective g) (hg : Syntomic g)
    (hcomp : IsLocalCompleteIntersectionMorphism (g ≫ f)) :
    IsLocalCompleteIntersectionMorphism f := by
  let 𝒰 : X.Cover (Scheme.precoverage (@Syntomic.{u})) :=
    Scheme.Cover.mkOfCovers PUnit.{u + 1} (fun _ => X') (fun _ => g)
      (fun x => ⟨⟨⟩, hgsurj.surj x⟩) (fun _ => hg)
  refine MorphismProperty.IsLocalAtSource.of_forall_comp
    (P := (@IsLocalCompleteIntersectionMorphism.{u} : MorphismProperty Scheme.{u}))
    𝒰.mem₀ ?_
  rintro U g' ⟨i⟩
  exact hcomp

end AlgebraicGeometry

end
