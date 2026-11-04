module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentThree.TorIndependenceAtPoints

/-!
# Base change of the geometric data of the derived Chow lemma

Let `s : S ⟶ S'` be a morphism of schemes, and let `f : X ⟶ S`, `g : P ⟶ S` be the base changes
of `f' : X' ⟶ S'`, `g' : P' ⟶ S'` along `s`. Then `T = X ×_S P` is the base change of
`T' = X' ×_{S'} P'`, and a closed subscheme `Z' ⊆ T'` pulls back to a closed subscheme
`Z = Z' ×_{T'} T` of `T`. This file proves the facts about this situation that the first paragraph
of the proof of [Stacks, Tag 0CSJ] uses: the two projections of `Z` are the base changes of the
two projections of `Z'`, the base change of a pullback square restricts to a pullback square
over an open, and — when `g'` is flat and `Z'` is flat over `X'` near a point — the
Tor independence of [Stacks, Tag 0CTA] in the form needed for Tor-independent base change.

## Main results

* `AlgebraicGeometry.isPullback_resLE_morphismRestrict`: a pullback square restricts to a
  pullback square over an open of its bottom right corner.
* `AlgebraicGeometry.isPullback_chowBaseChangeMap_fst` and
  `AlgebraicGeometry.isPullback_chowBaseChangeMap_snd`: the induced morphism `T ⟶ T'` is the base
  change of `X ⟶ X'` and of `P ⟶ P'`.
* `AlgebraicGeometry.torIndependent_morphismRestrict_chowBaseChangeMap`: [Stacks, Tag 0CTA] in the
  form used by [Stacks, Tag 0CSJ]: the part of `Z'` over an open `V' ⊆ P'` and the part of `T`
  over `V'` are Tor independent over the part of `T'` over `V'`.
* `AlgebraicGeometry.torIndependent_ι_chowBaseChangeMap`: the same Tor independence, with `Z'`
  itself in place of its part over `V'`, which is the form Tor-independent base change along the
  closed immersion `Z' ⟶ T'` consumes.

## References

* [Stacks Project, Tag 0CSJ](https://stacks.math.columbia.edu/tag/0CSJ)
* [Stacks Project, Tag 0CTA](https://stacks.math.columbia.edu/tag/0CTA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Restricting a pullback square to an open -/

section Restrict

variable {A B C D : Scheme.{u}} {t : A ⟶ B} {l : A ⟶ C} {r : B ⟶ D} {bo : C ⟶ D}

/-- The part of the top left corner of a commutative square lying over an open `O` of the bottom
right corner maps into the part of the top right corner lying over `O`. -/
theorem preimage_le_preimage_of_comm_square (h : t ≫ r = l ≫ bo) (O : D.Opens) :
    l ⁻¹ᵁ (bo ⁻¹ᵁ O) ≤ t ⁻¹ᵁ (r ⁻¹ᵁ O) := by
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, h]

/-- **A pullback square restricts to a pullback square over an open.** If
`A = B ×_D C` and `O ⊆ D` is open, then the part of `A` over `O` is the fibre product of the
parts of `B` and `C` over `O`. -/
theorem isPullback_resLE_morphismRestrict (h : IsPullback t l r bo) (O : D.Opens) :
    IsPullback (t.resLE (r ⁻¹ᵁ O) (l ⁻¹ᵁ (bo ⁻¹ᵁ O)) (preimage_le_preimage_of_comm_square h.w O))
      (l ∣_ (bo ⁻¹ᵁ O)) (r ∣_ O) (bo ∣_ O) := by
  refine IsPullback.of_right ?_ ?_ (isPullback_morphismRestrict r O).flip
  · rw [Scheme.Hom.resLE_comp_ι, morphismRestrict_ι]
    exact (isPullback_morphismRestrict l (bo ⁻¹ᵁ O)).flip.paste_horiz h
  · rw [← cancel_mono O.ι]
    simp only [Category.assoc, morphismRestrict_ι, Scheme.Hom.resLE_comp_ι_assoc]
    rw [h.w, morphismRestrict_ι_assoc]

/-- A property of morphisms stable under base change passes from the right edge of a pullback
square, restricted over an open, to the left edge restricted over the preimage of that open. -/
theorem of_isPullback_morphismRestrict (Q : MorphismProperty Scheme.{u})
    [Q.IsStableUnderBaseChange] (h : IsPullback t l r bo) (O : D.Opens) (hr : Q (r ∣_ O)) :
    Q (l ∣_ (bo ⁻¹ᵁ O)) :=
  Q.of_isPullback (isPullback_resLE_morphismRestrict h O) hr

end Restrict

/-! ### The base change of a fibre product -/

section BaseChange

variable {S S' X X' P P' : Scheme.{u}} {s : S ⟶ S'} {f : X ⟶ S} {f' : X' ⟶ S'} {g : P ⟶ S}
  {g' : P' ⟶ S'} {φ : X ⟶ X'} {ψ : P ⟶ P'}

/-- The morphism `X ×_S P ⟶ X' ×_{S'} P'` induced by the two base-change squares. -/
noncomputable abbrev chowBaseChangeMap (hX : IsPullback φ f f' s) (hP : IsPullback ψ g g' s) :
    pullback f g ⟶ pullback f' g' :=
  pullback.map f g f' g' φ ψ s hX.w.symm hP.w.symm

/-- **The induced morphism of fibre products is the base change of `X ⟶ X'`.** -/
theorem isPullback_chowBaseChangeMap_fst (hX : IsPullback φ f f' s) (hP : IsPullback ψ g g' s) :
    IsPullback (chowBaseChangeMap hX hP) (pullback.fst f g) (pullback.fst f' g') φ := by
  refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback f' g').flip
  rw [pullback.lift_snd, hX.w]
  exact (IsPullback.of_hasPullback f g).flip.paste_horiz hP

/-- **The induced morphism of fibre products is the base change of `P ⟶ P'`.** -/
theorem isPullback_chowBaseChangeMap_snd (hX : IsPullback φ f f' s) (hP : IsPullback ψ g g' s) :
    IsPullback (chowBaseChangeMap hX hP) (pullback.snd f g) (pullback.snd f' g') ψ := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f' g')
  rw [pullback.lift_fst, hP.w]
  exact (IsPullback.of_hasPullback f g).paste_horiz hX

/-- The comparison of `X ×_S P` with the fibre product of the base changes of `X'` and `P'`
along `s`, in the form in which [Stacks, Tag 0CTA] is stated. -/
noncomputable def chowBaseChangeMapIso (hX : IsPullback φ f f' s) (hP : IsPullback ψ g g' s) :
    pullback f g ≅ pullback (pullback.snd f' s) (pullback.snd g' s) :=
  asIso (pullback.map f g (pullback.snd f' s) (pullback.snd g' s) hX.isoPullback.hom
    hP.isoPullback.hom (𝟙 S) (by simp) (by simp))

/-- The comparison `chowBaseChangeMapIso` is compatible with the maps to `X' ×_{S'} P'`. -/
theorem chowBaseChangeMapIso_hom_comp (hX : IsPullback φ f f' s) (hP : IsPullback ψ g g' s) :
    (chowBaseChangeMapIso hX hP).hom ≫
        pullback.lift
          (pullback.fst (pullback.snd f' s) (pullback.snd g' s) ≫ pullback.fst f' s)
          (pullback.snd (pullback.snd f' s) (pullback.snd g' s) ≫ pullback.fst g' s)
          (by simp only [Category.assoc, pullback.condition,
            pullback.condition_assoc]) =
      chowBaseChangeMap hX hP := by
  apply pullback.hom_ext <;>
    simp only [chowBaseChangeMapIso, asIso_hom, chowBaseChangeMap, pullback.map, Category.assoc,
      pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc,
      IsPullback.isoPullback_hom_fst]

end BaseChange

/-! ### Tor independence -/

section TorIndependence

variable {S S' X X' P P' Z' : Scheme.{u}} {s : S ⟶ S'} {f : X ⟶ S} {f' : X' ⟶ S'} {g : P ⟶ S}
  {g' : P' ⟶ S'} {φ : X ⟶ X'} {ψ : P ⟶ P'}

/-- Applying the underlying maps of both sides of a commutative square to a point. -/
private theorem base_apply_eq_of_comp_eq {A B C D : Scheme.{u}} {a : A ⟶ B} {b : B ⟶ D}
    {c : A ⟶ C} {d : C ⟶ D} (h : a ≫ b = c ≫ d) (x : A) :
    b.base (a.base x) = d.base (c.base x) := by
  simp only [← Scheme.Hom.comp_apply, h]

/-- **[Stacks, Tag 0CTA] as used in [Stacks, Tag 0CSJ].** In the base-change situation, let
`iZ' : Z' ⟶ X' ×_{S'} P'` be a morphism and `V' ⊆ P'` an open; write `O'` for the part of
`X' ×_{S'} P'` over `V'` and `W'` for the part of `Z'` over `O'`. If `g'` is flat and `W'` is
flat over `X'`, then `W'` and the part of `X ×_S P` over `O'` are Tor independent over `O'`. -/
theorem torIndependent_morphismRestrict_chowBaseChangeMap (hX : IsPullback φ f f' s)
    (hP : IsPullback ψ g g' s) (iZ' : Z' ⟶ pullback f' g') (V' : P'.Opens) [Flat g']
    (hflat : Flat ((iZ' ⁻¹ᵁ (pullback.snd f' g' ⁻¹ᵁ V')).ι ≫ iZ' ≫ pullback.fst f' g')) :
    TorIndependent (iZ' ∣_ (pullback.snd f' g' ⁻¹ᵁ V'))
      (chowBaseChangeMap hX hP ∣_ (pullback.snd f' g' ⁻¹ᵁ V')) := by
  let O' := pullback.snd f' g' ⁻¹ᵁ V'
  let W' := iZ' ⁻¹ᵁ O'
  let zx := W'.ι ≫ iZ' ≫ pullback.fst f' g'
  let zy := W'.ι ≫ iZ' ≫ pullback.snd f' g'
  have hz : zx ≫ f' = zy ≫ g' := by simp only [zx, zy, Category.assoc, pullback.condition]
  have : Flat zx := hflat
  have H0 : TorIndependent
      (pullback.lift
          (pullback.fst (pullback.snd f' s) (pullback.snd g' s) ≫ pullback.fst f' s)
          (pullback.snd (pullback.snd f' s) (pullback.snd g' s) ≫ pullback.fst g' s)
          (by simp only [Category.assoc, pullback.condition, pullback.condition_assoc]))
      (pullback.lift zx zy hz) :=
    torIndependent_pullback_product_of_flat s f' g' zx zy hz
  have hzl : pullback.lift zx zy hz = W'.ι ≫ iZ' :=
    pullback.hom_ext (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  intro w o h
  let a := (chowBaseChangeMap hX hP ⁻¹ᵁ O').ι ≫ (chowBaseChangeMapIso hX hP).hom
  have ha : a ≫ pullback.lift
        (pullback.fst (pullback.snd f' s) (pullback.snd g' s) ≫ pullback.fst f' s)
        (pullback.snd (pullback.snd f' s) (pullback.snd g' s) ≫ pullback.fst g' s)
        (by simp only [Category.assoc, pullback.condition, pullback.condition_assoc]) =
      (chowBaseChangeMap hX hP ∣_ O') ≫ O'.ι := by
    simp only [a, Category.assoc, chowBaseChangeMapIso_hom_comp, morphismRestrict_ι]
  have hb : 𝟙 W'.toScheme ≫ pullback.lift zx zy hz = (iZ' ∣_ O') ≫ O'.ι := by
    rw [Category.id_comp, hzl, morphismRestrict_ι]
  refine torIndependentAt_symm _
    ((torIndependentAt_iff_of_isIso_stalkMap a (𝟙 W'.toScheme) O'.ι ha hb h.symm
      ?hpt).1 (H0 _ _ ?hpt))
  rw [base_apply_eq_of_comp_eq ha, base_apply_eq_of_comp_eq hb, h]

/-- The part of `X ×_S P` over the preimage of `V' ⊆ P'` in `P` is the part over the part of
`X' ×_{S'} P'` over `V'`. -/
theorem chowBaseChangeMap_preimage (hX : IsPullback φ f f' s) (hP : IsPullback ψ g g' s)
    (V' : P'.Opens) :
    chowBaseChangeMap hX hP ⁻¹ᵁ (pullback.snd f' g' ⁻¹ᵁ V') = pullback.snd f g ⁻¹ᵁ (ψ ⁻¹ᵁ V') := by
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.lift_snd]

/-- **[Stacks, Tag 0CTA] as used in [Stacks, Tag 0CSJ], globally on `Z'`.** In the situation of
`AlgebraicGeometry.torIndependent_morphismRestrict_chowBaseChangeMap`, `Z'` itself and the part of
`X ×_S P` over the preimage of `V'` in `P` are Tor independent over `X' ×_{S'} P'`. -/
theorem torIndependent_ι_chowBaseChangeMap (hX : IsPullback φ f f' s) (hP : IsPullback ψ g g' s)
    (iZ' : Z' ⟶ pullback f' g') (V' : P'.Opens) [Flat g']
    (hflat : Flat ((iZ' ⁻¹ᵁ (pullback.snd f' g' ⁻¹ᵁ V')).ι ≫ iZ' ≫ pullback.fst f' g')) :
    TorIndependent iZ' ((pullback.snd f g ⁻¹ᵁ (ψ ⁻¹ᵁ V')).ι ≫ chowBaseChangeMap hX hP) := by
  let O' := pullback.snd f' g' ⁻¹ᵁ V'
  have hTV := chowBaseChangeMap_preimage hX hP V'
  let b := ((pullback f g).isoOfEq hTV).hom
  have hb : b ≫ (pullback.snd f g ⁻¹ᵁ (ψ ⁻¹ᵁ V')).ι ≫ chowBaseChangeMap hX hP =
      (chowBaseChangeMap hX hP ∣_ O') ≫ O'.ι := by
    rw [morphismRestrict_ι, ← Category.assoc, Scheme.isoOfEq_hom_ι]
  have ha : (iZ' ⁻¹ᵁ O').ι ≫ iZ' = (iZ' ∣_ O') ≫ O'.ι := (morphismRestrict_ι _ _).symm
  intro z t hzt
  have hz : z ∈ iZ' ⁻¹ᵁ O' := by
    show iZ'.base z ∈ O'
    rw [hzt, Scheme.Hom.comp_apply]
    show ((pullback.snd f g ⁻¹ᵁ (ψ ⁻¹ᵁ V')).ι).base t ∈ chowBaseChangeMap hX hP ⁻¹ᵁ O'
    rw [hTV]
    exact t.2
  obtain ⟨w, rfl⟩ : z ∈ Set.range (iZ' ⁻¹ᵁ O').ι := by rwa [Scheme.Opens.range_ι]
  obtain ⟨t', rfl⟩ : ∃ t', b.base t' = t :=
    ⟨((pullback f g).isoOfEq hTV).inv.base t, by
      rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
      rfl⟩
  have h₀ : (iZ' ∣_ O').base w = (chowBaseChangeMap hX hP ∣_ O').base t' := by
    apply O'.ι.isOpenEmbedding.injective
    rw [← base_apply_eq_of_comp_eq ha, ← base_apply_eq_of_comp_eq hb, hzt]
  exact (torIndependentAt_iff_of_isIso_stalkMap (iZ' ⁻¹ᵁ O').ι b O'.ι ha hb h₀ hzt).2
    (torIndependent_morphismRestrict_chowBaseChangeMap hX hP iZ' V' hflat w t' h₀)

end TorIndependence

end AlgebraicGeometry

end
