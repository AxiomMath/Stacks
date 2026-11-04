module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurj
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationConstruction
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningFlatDeformation
public import StacksFrontier.AlgebraicGeometry.Thickenings.Affine
public import StacksFrontier.AlgebraicGeometry.Thickenings.BaseChange

/-!
# Affineness across a thickening of the base, for spaces étale over it

Let `S` be a scheme contained in a big fppf site `B`, let `i : T₀ ⟶ T` be a thickening of
objects of the site, and let `V` be an algebraic space étale over `T`. If the base change
`V ×_T T₀` is an affine scheme, then so is `V`.

## Main results

* `AlgebraicGeometry.Space.isAffineSpace_of_isEtale_of_isThickening_of_isAffineSpace_pullback`:
  the statement above.

## Implementation notes

The affine scheme `U₀ = V ×_T T₀` is étale over `T₀`, so the topological invariance of the
étale site (Stacks 039R, in the size-controlled form
`Stacks.Etale.exists_bigFppfOver_etale_pullback_iso_of_isClosedImmersion_of_surjective`) lifts
it to a scheme `U` of the site étale over `T` with `U ×_T T₀ ≅ U₀`. That `U` is affine is
Stacks 06AD (`Stacks.Thickenings.isAffine_of_isThickening`), `U₀ ⟶ U` being a base change of
the thickening `i`. The two objects `V` and `U` of the spaces-étale site of `T` then have
isomorphic base changes to `T₀`, and the isomorphism extends across the thickening, together
with its inverse, by the existence and uniqueness halves of full faithfulness of base change
along a thickening of arbitrary order (Stacks 05ZH),
`AlgebraicGeometry.Space.exists_hom_presheaf_of_isThickening` and
`AlgebraicGeometry.Space.hom_ext_presheaf_of_isThickening`.

## References

* [Stacks Project, Tag 039R](https://stacks.math.columbia.edu/tag/039R)
* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Affineness across a thickening of the base, for a space étale over it.** Let
`i : T₀ ⟶ T` be a morphism of the big fppf site of `S` whose underlying morphism of schemes is
a thickening, and let `p : V ⟶ T` be an étale morphism from an algebraic space. If the base
change `V ×_T T₀` is an affine scheme, then `V` is an affine scheme. -/
theorem isAffineSpace_of_isEtale_of_isThickening_of_isAffineSpace_pullback
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hV : IsAlgebraicSpace B S hS V)
    {T₀ T : BigFppfOver B S hS} (i : T₀ ⟶ T)
    (hi : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i))
    (p : V ⟶ yoneda.obj T) (hp : IsEtale B S hS p)
    (h₀ : IsAffineSpace B S hS (pullback p (yoneda.map i))) :
    IsAffineSpace B S hS V := by
  let Tsch := BigFppfOver.toScheme B S hS
  have : _root_.AlgebraicGeometry.IsClosedImmersion (Tsch.map i) := hi.1
  obtain ⟨U₀, hU₀, ⟨e₀⟩⟩ := h₀
  -- the chart `U₀ ⟶ T₀` underlying the base change, which is étale
  have hsnd : IsEtale B S hS (pullback.snd p (yoneda.map i)) :=
    isEtale_pullback_snd B S hS (isAlgebraicSpace_yoneda B S hS T₀)
      (isAlgebraicSpace_yoneda B S hS T) hV p (yoneda.map i) hp
  let k : U₀ ⟶ T₀ := yoneda.preimage (e₀.inv ≫ pullback.snd p (yoneda.map i))
  have hkmap : yoneda.map k = e₀.inv ≫ pullback.snd p (yoneda.map i) := yoneda.map_preimage _
  have hkE : IsEtale B S hS (yoneda.map k) := by
    rw [hkmap]
    intro W φ hφ
    rw [← Category.assoc]
    exact hsnd W _ (MorphismProperty.RespectsIso.postcomp _ e₀.inv _ hφ)
  have hk : _root_.AlgebraicGeometry.Etale (Tsch.map k) := etale_of_isEtale_yoneda_map B S hS hkE
  -- Stacks 039R lifts it to an étale scheme `U` over `T`
  obtain ⟨U, q, hqE, e, he⟩ :=
    Stacks.Etale.exists_bigFppfOver_etale_pullback_iso_of_isClosedImmersion_of_surjective
      B S hS i hi.2 U₀ (Tsch.map k) hk
  obtain ⟨p', hsq⟩ := exists_isPullback_of_iso_pullback_toScheme B S hS q i k e he
  -- `U` is affine, being a thickening of the affine `U₀`
  have hUaff : IsAffine (Tsch.obj U) := by
    have hth := Stacks.Thickenings.isThickening_of_isPullback
      (IsPullback.of_hasPullback (Tsch.map q) (Tsch.map i)) hi
    have : IsAffine (pullback (Tsch.map q) (Tsch.map i)) := IsAffine.of_isIso e.hom
    exact Stacks.Thickenings.isAffine_of_isThickening hth
  -- the thickening of `T` as a subspace
  let Y : AlgebraicSpaces B S hS := ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩
  have hclosed : IsClosedImmersion B S hS (yoneda.map i) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ i).2 hi.1
  have hG : IsThickening B S hS Y (Subfunctor.range (yoneda.map i)) :=
    isThickening_range_of_isClosedImmersion_isSurjective B S hS
      (isAlgebraicSpace_yoneda B S hS T₀) Y (yoneda.map i) hclosed
      (isSurjective_yoneda_map B S hS i ⟨hi.2⟩)
  have : Mono (yoneda.map i) := mono_of_isClosedImmersion B S hS _ hclosed
  have hι : (IsThickening.inclusion B S hS hG).hom =
      (Subfunctor.range (yoneda.map i)).ι := rfl
  have hpb : ∀ {P X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {a : P ⟶ X} {b : P ⟶ yoneda.obj T₀}
      {c : X ⟶ yoneda.obj T}, IsPullback a b c (yoneda.map i) →
      IsPullback a (b ≫ Subfunctor.toRange (yoneda.map i)) c
        (IsThickening.inclusion B S hS hG).hom := fun h => by
    rw [hι]
    exact h.of_iso (Iso.refl _) (Iso.refl _) (asIso (Subfunctor.toRange (yoneda.map i)))
      (Iso.refl _) (by simp) (by simp) (by simp) (by simp)
  have hpbV := hpb (IsPullback.of_hasPullback p (yoneda.map i))
  have hpbU := hpb (hsq.map yoneda)
  have hqEt : IsEtale B S hS (yoneda.map q) :=
    (isEtale_iff_presheaf_of_yoneda B S hS (yoneda.map q)).2
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ q).2 hqE)
  have hUalg := isAlgebraicSpace_yoneda B S hS U
  have hpq : p' ≫ q = k ≫ i := hsq.w
  -- the comparison morphisms in both directions
  obtain ⟨α, hα₁, hα₂⟩ := exists_hom_presheaf_of_isThickening B S hS hG hV hUalg hp hpbV
    (yoneda.map q) hqEt (e₀.hom ≫ yoneda.map p') (by
      rw [Category.assoc, ← Functor.map_comp, hpq, Functor.map_comp, hkmap]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      exact pullback.condition.symm)
  obtain ⟨β, hβ₁, hβ₂⟩ := exists_hom_presheaf_of_isThickening B S hS hG hUalg hV hqEt hpbU
    p hp (e₀.inv ≫ pullback.fst p (yoneda.map i)) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, ← hkmap, ← Functor.map_comp,
        ← Functor.map_comp, hpq])
  have hαβ : α ≫ β = 𝟙 V :=
    hom_ext_presheaf_of_isThickening B S hS hG hV hV hpbV p (isUnramified_of_isEtale B S hS hp)
      _ _ (by rw [Category.assoc, hβ₂, hα₂]) (Category.id_comp _) (by
        rw [← Category.assoc, hα₁, Category.assoc, hβ₁, Iso.hom_inv_id_assoc,
          Category.comp_id])
  have hβα : β ≫ α = 𝟙 (yoneda.obj U) :=
    hom_ext_presheaf_of_isThickening B S hS hG hUalg hUalg hpbU (yoneda.map q)
      (isUnramified_of_isEtale B S hS hqEt) _ _ (by rw [Category.assoc, hα₂, hβ₂])
      (Category.id_comp _) (by
        rw [← Category.assoc, hβ₁, Category.assoc, hα₁, Iso.inv_hom_id_assoc,
          Category.comp_id])
  exact ⟨U, hUaff, ⟨⟨α, β, hαβ, hβα⟩⟩⟩

end AlgebraicGeometry.Space

end
