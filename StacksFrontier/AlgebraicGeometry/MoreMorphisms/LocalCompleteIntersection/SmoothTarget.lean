module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Defs
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.SmoothPermanence
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.ImmersionIntoSmooth

/-!
# Local complete intersection morphisms into a smooth target

In a commutative triangle `X ⟶ Y ⟶ S` of schemes with `Y ⟶ S` smooth, if the structure morphism
`X ⟶ S` is a local complete intersection morphism then so is `X ⟶ Y`.

## Main results

* `AlgebraicGeometry.isLocalCompleteIntersectionMorphism_of_comp_of_smooth`: Stacks 069M.

## Implementation notes

The commutative triangle is recorded by writing the structure morphism of `X` as the composite
`f ≫ g`.

A factorization of `f ≫ g` near a point through a Koszul-regular immersion `i : U ⟶ P` and a
smooth `π : P ⟶ S` is turned into a factorization of `f` by base change: the smooth morphism is
`P ×_S Y ⟶ Y`, a base change of `π`, and the immersion is the morphism `U ⟶ P ×_S Y` induced by
`i` and `U ⟶ X ⟶ Y`.  That morphism is Koszul-regular by Stacks 067S, applied over the projection
`P ×_S Y ⟶ P`, which is a base change of `g` and hence smooth.

Finite type at the point is read off the same factorization: the restriction of `f` to `U`
factors through an immersion followed by a smooth morphism, so it is locally of finite type, and
finite type at a point only needs that on an affine neighbourhood.

## References

* [The Stacks Project, Lemma 37.62.9 (069M)](https://stacks.math.columbia.edu/tag/069M)
* [The Stacks Project, Lemma 31.22.6 (067S)](https://stacks.math.columbia.edu/tag/067S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RegularIdealSheaf

namespace AlgebraicGeometry

universe u

/-- A morphism whose restriction to an open neighbourhood of a point is locally of finite type is
of finite type at that point. -/
private lemma finiteTypeAt_of_locallyOfFiniteType_restrict {X Y : Scheme.{u}} (f : X ⟶ Y) {x : X}
    {U : X.Opens} (hxU : x ∈ U) (hf : LocallyOfFiniteType (U.ι ≫ f)) : finiteTypeAt f x := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hfxW, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  let xU : U.toScheme := ⟨x, hxU⟩
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
    U.toScheme.isBasis_affineOpens.exists_subset_of_mem_open
      (a := xU) (by change f x ∈ W; exact hfxW) ((U.ι ≫ f) ⁻¹ᵁ W).isOpen
  change IsAffineOpen V at hV
  let V' : X.affineOpens := ⟨U.ι ''ᵁ V, hV.image_of_isOpenImmersion U.ι⟩
  have hV'W : V'.1 ≤ f ⁻¹ᵁ W := by
    rintro _ ⟨z, hz, rfl⟩
    exact hVW hz
  refine ⟨⟨W, hW⟩, V', ⟨xU, hxV, rfl⟩, hV'W, ?_⟩
  have ht := (U.ι ≫ f).finiteType_appLE hW hV hVW
  have eV : V ≤ U.ι ⁻¹ᵁ V'.1 := by simp [V']
  have : IsIso (U.ι.appLE V'.1 V eV) :=
    inferInstanceAs (IsIso (U.ι.app V'.1 ≫ U.toScheme.presheaf.map
      (eqToHom (U.ι.preimage_image_eq V).symm).op))
  rw [← Scheme.Hom.appLE_comp_appLE U.ι f W V'.1 V hV'W eV, CommRingCat.hom_comp,
    RingHom.finiteType_respectsIso.cancel_right_isIso] at ht
  exact ht

/-- **Stacks 069M.**  In a commutative triangle of morphisms of schemes with `g : Y ⟶ S` smooth,
if the composite `f ≫ g` is a local complete intersection morphism then so is `f : X ⟶ Y`. -/
@[stacks 069M]
theorem isLocalCompleteIntersectionMorphism_of_comp_of_smooth {X Y S : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ S) [Smooth g] (h : IsLocalCompleteIntersectionMorphism (f ≫ g)) :
    IsLocalCompleteIntersectionMorphism f := by
  intro x
  obtain ⟨-, U, hxU, P, i, π, _, hkos, _, hfac⟩ := h x
  have hw : i ≫ π = (U.ι ≫ f) ≫ g := by rw [Category.assoc]; exact hfac.symm
  have hfst : pullback.lift i (U.ι ≫ f) hw ≫ pullback.fst π g = i := pullback.lift_fst _ _ _
  have hsnd : pullback.lift i (U.ι ≫ f) hw ≫ pullback.snd π g = U.ι ≫ f :=
    pullback.lift_snd _ _ _
  have hcomp : IsImmersion (pullback.lift i (U.ι ≫ f) hw ≫ pullback.fst π g) := by
    rw [hfst]; infer_instance
  have hlift : IsImmersion (pullback.lift i (U.ι ≫ f) hw) :=
    IsImmersion.of_comp _ (pullback.fst π g)
  have hkos' : IsKoszulRegularImmersion
      (pullback.lift i (U.ι ≫ f) hw ≫ pullback.fst π g) :=
    isKoszulRegularImmersion_of_eq hfst.symm hkos
  have hft : LocallyOfFiniteType (U.ι ≫ f) := by rw [← hsnd]; infer_instance
  exact ⟨finiteTypeAt_of_locallyOfFiniteType_restrict f hxU hft, U, hxU, pullback π g,
    pullback.lift i (U.ι ≫ f) hw, pullback.snd π g, inferInstance,
    Stacks.AlgebraicGeometry.RegularIdealSheaf.isKoszulRegularImmersion_of_comp_of_smooth
      (pullback.lift i (U.ι ≫ f) hw) (pullback.fst π g) hkos',
    inferInstance, hsnd.symm⟩

end AlgebraicGeometry

end
