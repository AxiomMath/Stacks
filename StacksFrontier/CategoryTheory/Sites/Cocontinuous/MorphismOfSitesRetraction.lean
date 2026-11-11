module

public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.MorphismsOfTopoi
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.RingedToposOfAMorphism
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSitesLimits
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A fully faithful cocontinuous and continuous functor defines a retraction of topoi

Let `(C, J)` and `(D, K)` be sites and let `u : C ⥤ D` be a functor which is cocontinuous,
continuous and fully faithful, such that `C` has fibre products which `u` preserves and a final
object `e` whose image `u(e)` is final in `D`. Let `g : Sh(C) → Sh(D)` be the morphism of topoi
attached to the cocontinuous functor `u` (Stacks 00XO), with `g_* = {}_su`, `g^{-1} = u^s` and
`g_!` the left adjoint of `g^{-1}` (Stacks 00XR, 00XS). Then `u` defines a morphism of sites
`f : D → C` with `f_* = g^{-1}` and `f^{-1} = g_!`, the composition
`Sh(C) --g--> Sh(D) --f--> Sh(C)` is isomorphic to the identity morphism of `Sh(C)`, and `f^{-1}`
is fully faithful. So `g` identifies `Sh(C)` with a subtopos of `Sh(D)`, and that embedding has
the retraction `f`.

## Main results

* `CategoryTheory.Functor.exists_isMorphismOfSites_comp_iso_id_of_isTerminal`: Stacks 00XU.

## Implementation notes

* `g` is `CategoryTheory.Functor.morphismOfTopoiOfCocontinuous`, whose inverse image is
  restriction `u^s = u.sheafPushforwardContinuous` along `u`, the form Stacks 00XR (1) gives to
  `g^{-1} = (u^p -)^#` for a continuous `u`; its direct image is `{}_su`,
  `u.sheafPushforwardCocontinuous`. `f` is the morphism of topoi
  `CategoryTheory.Functor.IsMorphismOfSites.morphismOfTopoi` of the morphism of sites (Stacks
  00XC).
* `g_!` is the left adjoint `(u^s).leftAdjoint` of `g^{-1} = u^s`, and the identity `f^{-1} = g_!`
  is stated in that form, together with the adjunction `f^{-1} ⊣ g^{-1}` which characterizes `g_!`
  up to unique isomorphism; `f^{-1} = u_s` is Mathlib's `CategoryTheory.Functor.sheafPullback`,
  which is defined as that left adjoint.
* "Isomorphic to the identity morphism of `Sh(C)`" is an invertible 2-morphism of topoi (Stacks
  04IA, `TwoMorphismOfTopoi`), i.e. an isomorphism of the pushforwards `(f ∘ g)_* ≅ id`; the
  corresponding isomorphism of inverse images `(f ∘ g)^{-1} = g^{-1} ∘ f^{-1} ≅ id`, the second
  display of the source's proof, is stated as well.
* Sites are small and sheaves are sheaves of sets in the universe of the sites, the source's
  standing setting and that of `CategoryTheory.Functor.IsMorphismOfSites`.

## References

* [Stacks 00XU](https://stacks.math.columbia.edu/tag/00XU), in the section "Cocontinuous functors
  and morphisms of topoi".
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace CategoryTheory.Functor

/-- **Stacks 00XU.** Let `(C, J)` and `(D, K)` be sites and let `u : C ⥤ D` be a functor such that
(a) `u` is cocontinuous, (b) `u` is continuous, (c) `u` is fully faithful, (d) fibre products
exist in `C` and `u` commutes with them, and (e) there are final objects `e` of `C` and `u(e)` of
`D`. Let `g : Sh(C) → Sh(D)` be the morphism of topoi of the cocontinuous functor `u`
(`morphismOfTopoiOfCocontinuous`), with `g^{-1} = u^s` and `g_! = (u^s).leftAdjoint` the left
adjoint of `g^{-1}`.

Then `u` defines a morphism of sites `f : D → C` with `f_* = g^{-1}` and `f^{-1} = g_!`, the
latter both as an equality with the chosen left adjoint `(u^s).leftAdjoint` and as an adjunction
`f^{-1} ⊣ g^{-1}`; the
composition `f ∘ g : Sh(C) → Sh(D) → Sh(C)` is isomorphic to the identity morphism of `Sh(C)`,
both on pushforwards (an invertible 2-morphism of topoi) and on inverse images; and `f^{-1}` is
fully faithful. -/
@[stacks 00XU "`f ∘ g ≅ id` is an invertible 2-morphism of topoi, an isomorphism of pushforwards
  `(f ∘ g)_* ≅ id`; the isomorphism `(f ∘ g)^{-1} ≅ id` of inverse images is also stated. Here
  `g^{-1}` is restriction along `u` (Stacks 00XR (1)) and `g_!` is the left adjoint of `g^{-1}`.",
  sga "4 III 2.6" "u ff ⇒ u_! ff",
  sga "4 I 5.14" "special case"]
public theorem exists_isMorphismOfSites_comp_iso_id_of_isTerminal
    {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D] (u : C ⥤ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [u.IsCocontinuous J K] [u.IsContinuous J K] [u.Full] [u.Faithful]
    [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u]
    {e : C} (he : IsTerminal e) (hue : IsTerminal (u.obj e)) :
    ∃ h : u.IsMorphismOfSites J K,
      h.morphismOfTopoi.pushforward = (u.morphismOfTopoiOfCocontinuous J K).inverseImage ∧
      h.morphismOfTopoi.inverseImage = (u.sheafPushforwardContinuous (Type u) J K).leftAdjoint ∧
      Nonempty (h.morphismOfTopoi.inverseImage ⊣
        (u.morphismOfTopoiOfCocontinuous J K).inverseImage) ∧
      Nonempty ((h.morphismOfTopoi.comp (u.morphismOfTopoiOfCocontinuous J K)).pushforward ≅
        (MorphismOfTopoi.id (Sheaf J (Type u))).pushforward) ∧
      Nonempty ((h.morphismOfTopoi.comp (u.morphismOfTopoiOfCocontinuous J K)).inverseImage ≅
        (MorphismOfTopoi.id (Sheaf J (Type u))).inverseImage) ∧
      h.morphismOfTopoi.inverseImage.Full ∧ h.morphismOfTopoi.inverseImage.Faithful :=
  have hff := full_and_faithful_sheafPullback u (Type u) J K
  have := isIso_unit_of_sheafPushforwardContinuous u (Type u) J K
    (u.sheafAdjunctionContinuous (Type u) J K)
  ⟨isMorphismOfSites_of_isTerminal u J K he hue, rfl, rfl,
    ⟨u.sheafAdjunctionContinuous (Type u) J K⟩,
    ⟨@asIso _ _ _ _ _ (isIso_sheafAdjunctionCocontinuous_counit u (Type u) J K)⟩,
    ⟨(asIso (u.sheafAdjunctionContinuous (Type u) J K).unit).symm⟩, hff.1, hff.2⟩

end CategoryTheory.Functor
