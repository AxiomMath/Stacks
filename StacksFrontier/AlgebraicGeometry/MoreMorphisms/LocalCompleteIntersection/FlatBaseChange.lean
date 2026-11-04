module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Defs
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularIdealSheaf.FlatBaseChange
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flat base change of a local complete intersection morphism

A local complete intersection morphism of schemes stays one after base change along a flat
morphism, because a base change of a smooth morphism is smooth and a flat base change of a
Koszul-regular immersion is Koszul-regular.

## Main results

* `AlgebraicGeometry.isLocalCompleteIntersectionMorphism_pullback_snd`: Stacks 069I.

## Implementation notes

The base-changed morphism is the second projection out of the categorical pullback of schemes.

Fix a point `y` of the pullback and let `x` be its image in the source. A factorization of `f`
near `x` through a Koszul-regular immersion `i : U ⟶ P` and a smooth `π : P ⟶ S` base changes to
a factorization near `y`: the open neighbourhood is the preimage `U'` of `U`, the smooth morphism
is `pullback.snd π g` and the Koszul-regular immersion is the induced map `U' ⟶ P ×_S S'`. The
latter is a base change of `i` along `pullback.fst π g`, which is flat because `g` is, so Stacks
067P applies to it; `U'` is identified with the relevant pullback through
`AlgebraicGeometry.pullbackRestrictIsoRestrict` and the two pullback-rearrangement isomorphisms,
and that identification is fed to the base-change lemma as a cartesian square rather than used to
transport the conclusion.

Finite type at `y` is read off an affine open neighbourhood inside `U'`, on which the composite
`U' ⟶ P ×_S S' ⟶ S'` is locally of finite type.

## References

* [The Stacks Project, Lemma 37.62.5 (069I)](https://stacks.math.columbia.edu/tag/069I)
* [The Stacks Project, Definition 37.62.1 (069F)](https://stacks.math.columbia.edu/tag/069F)
* [The Stacks Project, Lemma 31.21.4 (067P)](https://stacks.math.columbia.edu/tag/067P)
-/

public section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RegularIdealSheaf

namespace AlgebraicGeometry

universe u

private lemma finiteTypeAt_iff_exists_restrict {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    (∃ (V : X.affineOpens) (_hxV : x ∈ V.1), LocallyOfFiniteType (V.1.ι ≫ f)) →
      finiteTypeAt f x := by
  rintro ⟨V, hxV, hft⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, hfxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  let xV : V.1.toScheme := ⟨x, hxV⟩
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ :=
    V.1.toScheme.isBasis_affineOpens.exists_subset_of_mem_open
      (a := xV) (show f x ∈ U from hfxU) ((V.1.ι ≫ f) ⁻¹ᵁ U).isOpen
  change IsAffineOpen W at hW
  let W' : X.affineOpens := ⟨V.1.ι ''ᵁ W, hW.image_of_isOpenImmersion V.1.ι⟩
  have hW'U : W'.1 ≤ f ⁻¹ᵁ U := by
    rintro _ ⟨z, hz, rfl⟩
    exact hWU hz
  refine ⟨⟨U, hU⟩, W', ⟨xV, hxW, rfl⟩, hW'U, ?_⟩
  have ht := (V.1.ι ≫ f).finiteType_appLE hU hW hWU
  have eW : W ≤ V.1.ι ⁻¹ᵁ W'.1 := by
    simp [W']
  have : IsIso (V.1.ι.appLE W'.1 W eW) :=
    inferInstanceAs (IsIso (V.1.ι.app W'.1 ≫ V.1.toScheme.presheaf.map
      (eqToHom (V.1.ι.preimage_image_eq W).symm).op))
  rwa [← Scheme.Hom.appLE_comp_appLE V.1.ι f U W'.1 W hW'U eW, CommRingCat.hom_comp,
    RingHom.finiteType_respectsIso.cancel_right_isIso] at ht

@[reassoc (attr := simp)] private lemma pullback_congrHom_hom_fst {X Y S : Scheme.{u}}
    {f₁ f₂ : X ⟶ S} (g : Y ⟶ S) (h : f₁ = f₂) :
    (pullback.congrHom h rfl).hom ≫ pullback.fst f₂ g = pullback.fst f₁ g := by
  dsimp [pullback.congrHom]
  simp only [pullback.map, pullback.lift_fst, Category.comp_id]

@[reassoc (attr := simp)] private lemma pullback_congrHom_hom_snd {X Y S : Scheme.{u}}
    {f₁ f₂ : X ⟶ S} (g : Y ⟶ S) (h : f₁ = f₂) :
    (pullback.congrHom h rfl).hom ≫ pullback.snd f₂ g = pullback.snd f₁ g := by
  dsimp [pullback.congrHom]
  simp only [pullback.map, pullback.lift_snd, Category.comp_id]

/-- A flat base change of a local complete intersection morphism is a local
complete intersection morphism. -/
@[stacks 069I, sga "6 VIII 1.6" "flat base change stable"]
public theorem isLocalCompleteIntersectionMorphism_pullback_snd
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) [Flat g]
    (hf : IsLocalCompleteIntersectionMorphism f) :
    IsLocalCompleteIntersectionMorphism (pullback.snd f g) := by
  intro y
  let x := (pullback.fst f g) y
  obtain ⟨_, U, hxU, P, i, π, hi, hkos, hsmooth, hcomp⟩ := hf x
  let X' := pullback f g
  let r := pullback.fst π g
  let π' := pullback.snd π g
  let U' : X'.Opens := (pullback.fst f g) ⁻¹ᵁ U
  have hyU' : y ∈ U' := hxU
  let e₁ : pullback i r ≅ pullback (i ≫ π) g :=
    pullbackRightPullbackFstIso π g i
  let e₂₀ : pullback (pullback.fst f g) U.ι ≅ pullback (U.ι ≫ f) g :=
    (pullbackSymmetry (pullback.fst f g) U.ι).trans
      (pullbackRightPullbackFstIso f g U.ι)
  let e₂ : pullback (pullback.fst f g) U.ι ≅ pullback (i ≫ π) g :=
    e₂₀.trans (pullback.congrHom hcomp rfl)
  let e₃ : pullback (pullback.fst f g) U.ι ≅ U'.toScheme :=
    pullbackRestrictIsoRestrict (pullback.fst f g) U
  let a : U'.toScheme ≅ pullback i r :=
    (e₁.trans (e₂.symm.trans e₃)).symm
  let u : U'.toScheme ⟶ U.toScheme := a.hom ≫ pullback.fst i r
  let q₀ : U'.toScheme ⟶ pullback π g := a.hom ≫ pullback.snd i r
  have he₂snd : e₂.hom ≫ pullback.snd (i ≫ π) g =
      pullback.fst (pullback.fst f g) U.ι ≫ pullback.snd f g := by
    simp only [e₂, e₂₀, Iso.trans_hom, Category.assoc, pullback_congrHom_hom_snd,
      pullbackRightPullbackFstIso_hom_snd, pullbackSymmetry_hom_comp_snd_assoc]
  have he₁snd : e₁.inv ≫ pullback.snd i r ≫ pullback.snd π g =
      pullback.snd (i ≫ π) g := by
    dsimp [e₁, r]
    exact pullbackRightPullbackFstIso_inv_snd_snd π g i
  have hqπ : q₀ ≫ π' = U'.ι ≫ pullback.snd f g := by
    simp only [q₀, π', a, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, Category.assoc, he₁snd,
      he₂snd]
    rw [← Category.assoc e₃.inv]
    congr 1
    exact pullbackRestrictIsoRestrict_inv_fst (pullback.fst f g) U
  let : IsImmersion i := hi
  let : MorphismProperty.IsStableUnderBaseChangeAlong @Flat π :=
    ⟨fun pb hp => (Flat.isStableUnderBaseChange).of_isPullback pb hp⟩
  let : Flat r := by
    exact MorphismProperty.pullback_fst π g (inferInstance : Flat g)
  have hsq : IsPullback u q₀ i r :=
    IsPullback.of_iso_pullback ⟨by simp [u, q₀, pullback.condition]⟩ a rfl rfl
  have hqkos : IsKoszulRegularImmersion q₀ :=
    Stacks.AlgebraicGeometry.isKoszulRegularImmersion_of_isPullback_of_flat hsq.flip hkos
  let : MorphismProperty.IsStableUnderBaseChangeAlong @Smooth g :=
    ⟨fun pb hp => smooth_isStableUnderBaseChange.of_isPullback pb hp⟩
  let : Smooth π' := MorphismProperty.pullback_snd π g hsmooth
  let : LocallyOfFiniteType q₀ := by infer_instance
  let : LocallyOfFiniteType π' := by infer_instance
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWU'⟩ :=
    X'.isBasis_affineOpens.exists_subset_of_mem_open hyU' U'.2
  change IsAffineOpen W at hW
  let W' : X'.affineOpens := ⟨W, hW⟩
  let m : W'.1.toScheme ⟶ U'.toScheme :=
    Scheme.Hom.resLE (𝟙 X') U' W'.1 (by simpa using hWU')
  have hm : m ≫ U'.ι = W'.1.ι := by
    dsimp [m]
    simp
  let : LocallyOfFiniteType m := by infer_instance
  have hLft : LocallyOfFiniteType (W'.1.ι ≫ pullback.snd f g) := by
    let : LocallyOfFiniteType (m ≫ q₀ ≫ π') := inferInstance
    have hcomp' : m ≫ q₀ ≫ π' = W'.1.ι ≫ pullback.snd f g := by
      rw [hqπ, ← Category.assoc, hm]
    rw [← hcomp']
    infer_instance
  refine ⟨finiteTypeAt_iff_exists_restrict (pullback.snd f g) y ⟨⟨W', hW⟩, hyW, hLft⟩,
    U', hyU', pullback π g, q₀, π', ?_, hqkos, ?_, hqπ.symm⟩
  · infer_instance
  · infer_instance

end AlgebraicGeometry

end
