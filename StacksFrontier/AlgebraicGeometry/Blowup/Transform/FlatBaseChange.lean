module

public import StacksFrontier.AlgebraicGeometry.Blowup.ClassifyingMorphism
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic

/-!
# Blowing up commutes with flat base change

Let `g : X₁ ⟶ X₂` be a flat morphism of schemes and let `Z₂ ⊆ X₂` be the closed subscheme cut
out by a quasi-coherent ideal `I`. The inverse image of `Z₂` in `X₁` is cut out by `I.comap g`,
and the blowup of `X₁` in it is the base change along `g` of the blowup of `X₂` in `I`.

## Main results

* `AlgebraicGeometry.exists_isPullback_blowUpToBase_comap`: the square formed by the two blowup
  morphisms and `g` is cartesian.
* `AlgebraicGeometry.exists_iso_blowUp_comap_opens_exceptionalIdeal`: the case of an open
  immersion, stated as an identification rather than a cartesian square — blowing up commutes
  with restricting the base to an open, and the exceptional ideal restricts along it.

## Implementation notes

The comparison morphism between the two blowups comes from the universal property of the
blowup (`Stacks.Blowup.isTerminal_blowUp`): the composite `X₁' ⟶ X₁ ⟶ X₂` makes `I` an
effective Cartier divisor, so it factors through `X₂'`. Flatness is used exactly once, to see
that `I` stays an effective Cartier divisor after pulling back along the second projection of
`X₁ ×_{X₂} X₂'`, which is a base change of the flat morphism `g`; that makes the pullback an
object of the same category, and terminality identifies it with `X₁'`.

## References

* [Stacks Project, Tag 0805](https://stacks.math.columbia.edu/tag/0805)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Two morphisms into a terminal object of `CartierOver I` over the same base agree. -/
private theorem left_ext_of_isTerminal {X : Scheme.{u}} {I : X.IdealSheafData}
    {T : Stacks.Blowup.CartierOver I} (t : IsTerminal T) {Y : Stacks.Blowup.CartierOver I}
    (u v : Y.obj.left ⟶ T.obj.left) (hu : u ≫ T.obj.hom = Y.obj.hom)
    (hv : v ≫ T.obj.hom = Y.obj.hom) : u = v :=
  congrArg (fun q : Y ⟶ T => q.hom.left)
    (t.hom_ext ⟨Over.homMk u hu⟩ ⟨Over.homMk v hv⟩)

/-- **Stacks Project, Tag 0805.** Blowing up commutes with flat base change: for a flat
`g : X₁ ⟶ X₂` and a quasi-coherent ideal `I` on `X₂`, the blowup of `X₁` in the inverse image
of `I` sits in a cartesian square over the blowup of `X₂` in `I`. -/
@[stacks 0805]
theorem exists_isPullback_blowUpToBase_comap {X₁ X₂ : Scheme.{u}} (g : X₁ ⟶ X₂) [Flat g]
    (I : X₂.IdealSheafData) :
    ∃ h : blowUp (I.comap g) ⟶ blowUp I,
      IsPullback (blowUpToBase (I.comap g)) h g (blowUpToBase I) := by
  obtain ⟨h₁, ⟨t₁⟩⟩ := Stacks.Blowup.isTerminal_blowUp (I.comap g)
  obtain ⟨h₂, ⟨t₂⟩⟩ := Stacks.Blowup.isTerminal_blowUp I
  set b₁ := blowUpToBase (I.comap g)
  set b₂ := blowUpToBase I
  let o₁ : Stacks.Blowup.CartierOver (I.comap g) := ⟨Over.mk b₁, h₁⟩
  have h₁₂ : Stacks.Blowup.IsCartierOver I (Over.mk (b₁ ≫ g)) := by
    show Stacks.Divisors.IsEffectiveCartierDivisor (I.comap (b₁ ≫ g))
    rwa [Scheme.IdealSheafData.comap_comp]
  let f : blowUp (I.comap g) ⟶ blowUp I := (t₂.from ⟨Over.mk (b₁ ≫ g), h₁₂⟩).hom.left
  have hf : f ≫ b₂ = b₁ ≫ g := Over.w (t₂.from ⟨Over.mk (b₁ ≫ g), h₁₂⟩).hom
  let p₁ := pullback.fst g b₂
  let p₂ := pullback.snd g b₂
  have hP2 : Stacks.Divisors.IsEffectiveCartierDivisor (I.comap (p₂ ≫ b₂)) := by
    rw [Scheme.IdealSheafData.comap_comp]
    exact Stacks.Divisors.isPullbackDefined_of_flat p₂ (I.comap b₂) h₂
  have hP : Stacks.Divisors.IsEffectiveCartierDivisor ((I.comap g).comap p₁) := by
    rwa [← Scheme.IdealSheafData.comap_comp, pullback.condition]
  let k : pullback g b₂ ⟶ blowUp (I.comap g) := (t₁.from ⟨Over.mk p₁, hP⟩).hom.left
  have hk : k ≫ b₁ = p₁ := Over.w (t₁.from ⟨Over.mk p₁, hP⟩).hom
  let h : blowUp (I.comap g) ⟶ pullback g b₂ := pullback.lift b₁ f hf.symm
  have hfst : h ≫ p₁ = b₁ := pullback.lift_fst b₁ f hf.symm
  have hsnd : h ≫ p₂ = f := pullback.lift_snd b₁ f hf.symm
  let oP₂ : Stacks.Blowup.CartierOver I := ⟨Over.mk (p₂ ≫ b₂), hP2⟩
  have hkf : k ≫ f = p₂ :=
    left_ext_of_isTerminal t₂ (Y := oP₂) _ _
      (by
        change (k ≫ f) ≫ b₂ = p₂ ≫ b₂
        rw [Category.assoc, hf, ← Category.assoc, hk, pullback.condition]) rfl
  have hcompP : k ≫ h = 𝟙 _ :=
    pullback.hom_ext (by rw [Category.assoc, hfst, hk, Category.id_comp])
      (by rw [Category.assoc, hsnd, hkf, Category.id_comp])
  have hcompB₁ : h ≫ k = 𝟙 _ :=
    left_ext_of_isTerminal t₁ (Y := o₁) _ _
      (by change (h ≫ k) ≫ b₁ = b₁; rw [Category.assoc, hk, hfst]) (Category.id_comp _)
  exact ⟨f, IsPullback.iff_exists_over_iso.2
    ⟨Over.isoMk ⟨h, k, hcompB₁, hcompP⟩ hfst, hsnd.symm⟩⟩

/-! ### Restricting the base to an open -/

/-- **Blowing up commutes with restricting the base to an open subscheme.** For `W` an open
subscheme of `S` and `I` a quasi-coherent ideal sheaf on `S`, the blowup of `W` in the restricted
centre `I.comap W.ι` *is* the preimage of `W` in the blowup of `S` in `I`: there is an
isomorphism `e` between them which is compatible with the two morphisms to `W`, hence with the
two morphisms to `S`, and which identifies the exceptional ideal of the restricted blowup with
the restriction of the exceptional ideal.

This is [Stacks, Tag 0805] (`AlgebraicGeometry.exists_isPullback_blowUpToBase_comap`) for the
open immersion `W.ι`, which is flat, read against
`AlgebraicGeometry.isPullback_morphismRestrict`, which exhibits the preimage of `W` as the same
base change; the two cartesian squares have the same cospan, so their upper left corners agree.
The clause on the exceptional ideal is then formal, both sides being the inverse image of `I`
along the two equal composites to `S`. -/
theorem exists_iso_blowUp_comap_opens_exceptionalIdeal {S : Scheme.{u}} (I : S.IdealSheafData)
    (W : S.Opens) :
    ∃ e : blowUp (I.comap W.ι) ≅ (blowUpToBase I ⁻¹ᵁ W : (blowUp I).Opens).toScheme,
      e.hom ≫ blowUpToBase I ∣_ W = blowUpToBase (I.comap W.ι) ∧
        e.hom ≫ (blowUpToBase I ⁻¹ᵁ W : (blowUp I).Opens).ι ≫ blowUpToBase I =
          blowUpToBase (I.comap W.ι) ≫ W.ι ∧
        exceptionalIdeal (I.comap W.ι) =
          (exceptionalIdeal I).comap
            (e.hom ≫ (blowUpToBase I ⁻¹ᵁ W : (blowUp I).Opens).ι) := by
  obtain ⟨c, hP⟩ := exists_isPullback_blowUpToBase_comap W.ι I
  have hR := isPullback_morphismRestrict (blowUpToBase I) W
  refine ⟨hP.isoIsPullback _ _ hR, hP.isoIsPullback_hom_fst _ _ hR, ?_, ?_⟩
  · rw [← morphismRestrict_ι (blowUpToBase I) W, ← Category.assoc,
      hP.isoIsPullback_hom_fst _ _ hR]
  · rw [exceptionalIdeal, exceptionalIdeal, ← Scheme.IdealSheafData.comap_comp,
      ← Scheme.IdealSheafData.comap_comp, Category.assoc,
      ← morphismRestrict_ι (blowUpToBase I) W, ← Category.assoc,
      hP.isoIsPullback_hom_fst _ _ hR]

end AlgebraicGeometry

end
