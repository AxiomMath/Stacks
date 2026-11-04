module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.RegularImmersionFpqc
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Composition
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.ImmersionIntoSmooth
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Perfect
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.RegularImmersion
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.SmoothTargetPermanence
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.AffineSpaceImmersion
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection.ImmersionIntoSmooth

/-!
# Local complete intersection morphisms are fpqc local on the target

Being a local complete intersection morphism of schemes can be checked after an fpqc covering of
the target: a morphism `f : X ⟶ S` is Koszul if and only if its base change along every member
of an fpqc covering of `S` is Koszul. This is **Stacks 069N**.

## Main results

* `AlgebraicGeometry.isLocalCompleteIntersectionMorphism_respectsIso`: being a local complete
  intersection morphism is invariant under isomorphisms of the source and of the target.
* `AlgebraicGeometry.isLocalCompleteIntersectionMorphism_isLocalAtTarget_fpqc`: **Stacks 069N**.
* `AlgebraicGeometry.isLocalCompleteIntersectionMorphism_iff_of_fpqcCover`: the same statement
  spelled out as an iff over a given fpqc covering.

## Implementation notes

The criterion used is `CategoryTheory.MorphismProperty.IsLocalAtTarget.mk_of_iff_of_zeroHypercover`,
which asks for both directions over an arbitrary fpqc `0`-hypercover of the target and needs
only invariance under isomorphisms; Zariski locality on the target is not used, and the
descent criterion of Stacks 02KP is not invoked.

The forward direction is Stacks 069I, `isLocalCompleteIntersectionMorphism_pullback_snd`, the
members of an fpqc covering being flat.

For the converse, let `f : X ⟶ S` have all its base changes `f_i` Koszul. Then `f` is locally of
finite type, since each `f_i` is locally of finite presentation by Stacks 069H and being locally
of finite type is fpqc local on the target by Stacks 02KX. Fix `x : X`, an affine open `W` around
its image and an affine open `V ⊆ f ⁻¹ᵁ W` around `x`, and use Stacks 04II to obtain an immersion
`i : V ⟶ 𝔸ⁿ_W` over `W`; composing the structure morphism of `𝔸ⁿ_W` with the inclusion of `W`
gives a smooth `π : 𝔸ⁿ_W ⟶ S` through which `V.ι ≫ f` factors. What remains is that `i` is
Koszul-regular, and that is fpqc descent for quasi-compact Koszul-regular immersions, Stacks
0694, applied to the covering of `𝔸ⁿ_W` obtained by pulling the given covering back along `π`:
the base change of `i` along a member is, up to the comparison isomorphisms of iterated
pullbacks, an immersion of an open subscheme of the base change of `X` into the base change of
`𝔸ⁿ_W`, which is smooth over the base change of `S`, so Stacks 069G applies to the Koszul
morphism `f_i`. Quasi-compactness of `i` is automatic, `V` being affine.

Stacks 069G is stated in this library with the Koszul case of Stacks 0693 as the explicit
hypothesis `AlgebraicGeometry.KoszulRegularCompSmooth`. That case *is* available, as
`Stacks.AlgebraicGeometry.RegularIdealSheaf.isKoszulRegularImmersion_comp_of_smooth`, so the
hypothesis is discharged here by `AlgebraicGeometry.koszulRegularCompSmooth_of_smoothTarget`
rather than carried: the statement of Stacks 069N below has no input beyond the morphism and the
covering.

## References

* [The Stacks Project, Lemma 37.62.19 (069N)](https://stacks.math.columbia.edu/tag/069N)
* [The Stacks Project, Lemma 37.62.3 (069G)](https://stacks.math.columbia.edu/tag/069G)
* [The Stacks Project, Lemma 37.62.4 (069H)](https://stacks.math.columbia.edu/tag/069H)
* [The Stacks Project, Lemma 37.62.6 (069I)](https://stacks.math.columbia.edu/tag/069I)
* [The Stacks Project, Lemma 37.62.7 (069J)](https://stacks.math.columbia.edu/tag/069J)
* [The Stacks Project, Lemma 31.23.12 (0693)](https://stacks.math.columbia.edu/tag/0693)
* [The Stacks Project, Lemma 35.23.34 (0694)](https://stacks.math.columbia.edu/tag/0694)
* [The Stacks Project, Lemma 35.23.12 (02KX)](https://stacks.math.columbia.edu/tag/02KX)
* [The Stacks Project, Lemma 29.39.2 (04II)](https://stacks.math.columbia.edu/tag/04II)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RegularIdealSheaf

universe w u

namespace AlgebraicGeometry

/-- The restriction of a morphism locally of finite type, over an open of the target and to an
open of the source contained in its preimage, is locally of finite type. -/
private theorem locallyOfFiniteType_resLE {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (U : S.Opens) (V : X.Opens) (hVU : V ≤ f ⁻¹ᵁ U) :
    LocallyOfFiniteType (f.resLE U V hVU) := by
  delta Scheme.Hom.resLE
  infer_instance

/-- Being a local complete intersection morphism is invariant under isomorphisms of the source
and of the target: an isomorphism is an open immersion, hence Koszul, and Koszul morphisms
compose by Stacks 069J. -/
instance isLocalCompleteIntersectionMorphism_respectsIso :
    MorphismProperty.RespectsIso
      (@IsLocalCompleteIntersectionMorphism : MorphismProperty Scheme.{u}) := by
  apply MorphismProperty.RespectsIso.mk
  · intro X Y Z e f hf
    exact isLocalCompleteIntersectionMorphism_comp e.hom f
      (isLocalCompleteIntersectionMorphism_of_isOpenImmersion e.hom) hf
  · intro X Y Z e f hf
    exact isLocalCompleteIntersectionMorphism_comp f e.hom hf
      (isLocalCompleteIntersectionMorphism_of_isOpenImmersion e.hom)

/-- **The Koszul case of Stacks 0693**, in the packaged form
`AlgebraicGeometry.KoszulRegularCompSmooth` that Stacks 069G takes as a hypothesis: a
Koszul-regular immersion followed by a smooth morphism of its target is Koszul-regular as soon as
the composite is an immersion.

This is the Koszul-regular clause of Stacks 0693,
`Stacks.AlgebraicGeometry.RegularIdealSheaf.isKoszulRegularImmersion_comp_of_smooth`, repackaged;
it discharges the hypothesis of Stacks 069G, and hence of Stacks 069N below. -/
private alias koszulRegularCompSmooth_of_smoothTarget := koszulRegularCompSmooth

/-- **Stacks 069N.** Being a local complete intersection morphism of schemes is fpqc local on the
target: a morphism is Koszul if and only if its base change along every member of an fpqc
covering of its target is Koszul. -/
@[stacks 069N, sga "2 XII 4.10" "partial"]
theorem isLocalCompleteIntersectionMorphism_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget
      (@IsLocalCompleteIntersectionMorphism : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage := by
  refine MorphismProperty.IsLocalAtTarget.mk_of_iff_of_zeroHypercover fun {X S} f 𝒰 ↦
    ⟨fun hf i ↦ ?_, fun hf ↦ ?_⟩
  · have hflat : Flat (𝒰.f i) := 𝒰.mem₀.2.2 ⟨i⟩
    have _ : Flat (𝒰.f i) := hflat
    exact isLocalCompleteIntersectionMorphism_pullback_snd f (𝒰.f i) hf
  · have hft : LocallyOfFiniteType f := by
      refine MorphismProperty.IsLocalAtTarget.of_zeroHypercover (P := @LocallyOfFiniteType) 𝒰 ?_
      intro i
      have _ := locallyOfFinitePresentation_of_isLocalCompleteIntersectionMorphism (hf i)
      infer_instance
    have _ : LocallyOfFiniteType f := hft
    intro x
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hxW (f ⁻¹ᵁ W).2
    have _ : IsAffine (Scheme.Opens.toScheme V) := hV
    have _ : IsAffine (Scheme.Opens.toScheme W) := hW
    let g : Scheme.Opens.toScheme V ⟶ Scheme.Opens.toScheme W := f.resLE W V hVW
    have _ : LocallyOfFiniteType g := locallyOfFiniteType_resLE f W V hVW
    obtain ⟨n, i, hi, hig⟩ := exists_immersion_affineSpace g
    let P := AffineSpace (ULift.{u} (Fin n)) (Scheme.Opens.toScheme W)
    let π : P ⟶ S := (P ↘ Scheme.Opens.toScheme W) ≫ Scheme.Opens.ι W
    have _ : Smooth (P ↘ Scheme.Opens.toScheme W) := smooth_affineSpace_over _ _
    have _ : IsImmersion i := hi
    have hcomm : i ≫ π = Scheme.Opens.ι V ≫ f :=
      calc i ≫ π = (i ≫ (P ↘ Scheme.Opens.toScheme W)) ≫ Scheme.Opens.ι W := by
            rw [Category.assoc]
        _ = g ≫ Scheme.Opens.ι W := by rw [hig]
        _ = Scheme.Opens.ι V ≫ f := Scheme.Hom.resLE_comp_ι f hVW
    have hreg : IsKoszulRegularImmersion i := by
      let Q : MorphismProperty Scheme.{u} :=
        (fun _ _ j ↦ ∃ hj : IsImmersion j, @IsKoszulRegularImmersion _ _ j hj) ⊓ @QuasiCompact
      have hQloc : Q.IsLocalAtTarget Scheme.fpqcPrecoverage :=
        isLocalAtTarget_koszulRegularImmersion_inf_quasiCompact_fpqc
      have _ : Q.RespectsIso := hQloc.toRespects
      have hdesc : Q i := by
        refine MorphismProperty.IsLocalAtTarget.of_zeroHypercover (P := Q) (𝒰.pullback₁ π) ?_
        intro k
        let c := 𝒰.f k
        let fV : Scheme.Opens.toScheme V ⟶ S := Scheme.Opens.ι V ≫ f
        let Vk := pullback fV c
        let e : pullback i (pullback.fst π c) ≅ Vk :=
          pullbackRightPullbackFstIso π c i ≪≫ pullback.congrHom hcomm rfl
        let jbar : Vk ⟶ pullback π c := e.inv ≫ pullback.snd i (pullback.fst π c)
        have heq : e.hom ≫ jbar = pullback.snd i (pullback.fst π c) := by simp [jbar]
        let fVk : Vk ⟶ 𝒰.X k := pullback.snd fV c
        let vMap : Vk ⟶ pullback f c :=
          (pullbackRightPullbackFstIso f c (Scheme.Opens.ι V)).inv ≫
            pullback.snd (Scheme.Opens.ι V) (pullback.fst f c)
        have _ : IsOpenImmersion vMap := by infer_instance
        have hvMap : vMap ≫ pullback.snd f c = fVk := by
          simp [vMap, fVk, fV, pullbackRightPullbackFstIso_inv_snd_snd, Category.assoc]
        have hfVk : IsLocalCompleteIntersectionMorphism fVk := by
          rw [← hvMap]
          exact isLocalCompleteIntersectionMorphism_comp vMap (pullback.snd f c)
            (isLocalCompleteIntersectionMorphism_of_isOpenImmersion vMap) (hf k)
        let top : Vk.Opens := ⊤
        let j0 : top.toScheme ⟶ pullback π c := top.ι ≫ jbar
        have _ : Smooth (pullback.snd π c) := by infer_instance
        have _ : IsImmersion j0 := by infer_instance
        have hjbar : jbar ≫ pullback.snd π c = fVk := by
          simp [jbar, e, fVk, fV, pullback.congrHom, pullback.map, Category.assoc,
            pullbackRightPullbackFstIso_inv_snd_snd, pullback.lift_snd]
        have hj0 : top.ι ≫ fVk = j0 ≫ pullback.snd π c := by
          simp [j0, Category.assoc, hjbar]
        have hkos : IsKoszulRegularImmersion j0 :=
          isKoszulRegularImmersion_of_isLocalCompleteIntersectionMorphism
            koszulRegularCompSmooth_of_smoothTarget fVk
            (pullback.snd π c) top j0 hfVk hj0
        have _ : IsIso top.ι := (Scheme.topIso Vk).isIso_hom
        change Q (pullback.snd i (pullback.fst π c))
        rw [← heq]
        exact (MorphismProperty.cancel_left_of_respectsIso Q e.hom jbar).mpr
          ((MorphismProperty.cancel_left_of_respectsIso Q top.ι jbar).mp
            ⟨⟨inferInstance, hkos⟩, inferInstance⟩)
      exact hdesc.1.choose_spec
    exact ⟨finiteTypeAt_of_locallyOfFiniteType f x, V, hxV, P, i, π, hi, hreg, inferInstance,
      hcomm.symm⟩

/-- A morphism of schemes is a local complete intersection morphism if and only if its base
change along every member of a given fpqc covering of its target is one.

This spells out both directions of
`AlgebraicGeometry.isLocalCompleteIntersectionMorphism_isLocalAtTarget_fpqc`. -/
@[sga "2 XII 4.10" "partial"]
theorem isLocalCompleteIntersectionMorphism_iff_of_fpqcCover {X S : Scheme.{u}} (f : X ⟶ S)
    (𝒰 : Precoverage.ZeroHypercover.{w} Scheme.fpqcPrecoverage S) :
    IsLocalCompleteIntersectionMorphism f ↔
      ∀ i, IsLocalCompleteIntersectionMorphism (pullback.snd f (𝒰.f i)) :=
  have := isLocalCompleteIntersectionMorphism_isLocalAtTarget_fpqc
  MorphismProperty.IsLocalAtTarget.iff_of_zeroHypercover
    (P := (@IsLocalCompleteIntersectionMorphism : MorphismProperty Scheme.{u})) 𝒰

end AlgebraicGeometry

end
