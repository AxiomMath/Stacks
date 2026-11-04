module

public import StacksFrontier.AlgebraicGeometry.Blowup.TwoStepTower
public import StacksFrontier.AlgebraicGeometry.StrictTransform.Quasicoherent

/-!
# Two-step blow-up towers over an open of the base

Let `W` be a scheme, `I`, `J` quasi-coherent ideal sheaves on `W`, and `g : W₁ ⟶ W` an open
immersion (typically the inclusion of an open `V ⊆ W`). The tower
`AlgebraicGeometry.TwoStepTower.strictTower I J` blows up `I` and then the strict transform of
`V(J)`. This file shows that forming the tower commutes with restriction to `W₁`: the tower of
the restricted centres `I.comap g`, `J.comap g` is the base change along `g` of the tower over
`W`. This is the form in which "the tower over `Y - Q`, restricted over `Y - {P, Q}`" is compared
with "the tower over `Y - {P, Q}`" in Hironaka's example (the source of [Stacks, Tag 08J1]).

## Main results

* `AlgebraicGeometry.TwoStepTower.ker_eq_comap_of_isPullback`: the kernel of a quasi-compact
  morphism pulls back along an open immersion of the target to the kernel of its base change.
* `AlgebraicGeometry.TwoStepTower.strictCentre_eq_ker`: the strict-transform centre is the
  scheme-theoretic image in `Bl_I W` of the part of `V(J) ×_W Bl_I W` off the exceptional
  divisor.
* `AlgebraicGeometry.TwoStepTower.comap_strictCentre_of_isPullback`: **the strict-transform
  centre restricts.** Along the open immersion `Bl_{I|W₁} W₁ ⟶ Bl_I W` of [Stacks, Tag 0805], the
  strict-transform centre of `(I, J)` pulls back to that of `(I|W₁, J|W₁)`.
* `AlgebraicGeometry.TwoStepTower.exists_isPullback_strictTower`: **the tower restricts.** The
  tower over `W₁` sits in a cartesian square over the tower over `W`.
* `AlgebraicGeometry.TwoStepTower.nonempty_restrictIso`: for an open `V ⊆ W`, the restriction of
  the tower over `V` is, over `V`, the tower of the restricted centres.

## Implementation notes

The strict transform is the scheme-theoretic image of the open complement of the exceptional
preimage (`Stacks.StrictTransform.ideal_eq_ker_ι`), so its ideal on `Bl_I W` is the kernel of
`U ⟶ V(J) ×_W Bl_I W ⟶ Bl_I W`, with `U` that open. Kernels of quasi-compact morphisms commute
with restriction to opens (`AlgebraicGeometry.Scheme.ker_ideal_of_isPullback_of_isOpenImmersion`),
so it suffices that `U₁ ⟶ Bl_{I|W₁} W₁` is the base change of `U ⟶ Bl_I W` along the open
immersion of blow-ups. That is a pasting of cartesian squares: `V(J|W₁)` is the base change of
`V(J)` (`AlgebraicGeometry.Scheme.IdealSheafData.comapIso`), so `V(J|W₁) ×_{W₁} Bl_{I|W₁} W₁` is
the base change of `V(J) ×_W Bl_I W` along the open immersion of blow-ups, and the two
exceptional complements correspond because the square of blow-ups commutes.

## References

* [Stacks Project, Tag 08J1](https://stacks.math.columbia.edu/tag/08J1)
* [Stacks Project, Tag 0805](https://stacks.math.columbia.edu/tag/0805)
* [Stacks Project, Tag 080D](https://stacks.math.columbia.edu/tag/080D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.TwoStepTower

variable {W : Scheme.{u}}

/-- The kernel of a quasi-compact morphism `f : X ⟶ Y` pulls back along an open immersion
`iV : V ⟶ Y` to the kernel of the base change of `f`. -/
theorem ker_eq_comap_of_isPullback {X Y U V : Scheme.{u}} {f : X ⟶ Y} {f' : U ⟶ V}
    {iU : U ⟶ X} {iV : V ⟶ Y} [IsOpenImmersion iV] [QuasiCompact f]
    (H : IsPullback f' iU iV f) : f'.ker = f.ker.comap iV := by
  ext W
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.ker_ideal_of_isPullback_of_isOpenImmersion f f' iU iV H]

/-- The strict-transform centre is the kernel of the composite of the inclusion of the
complement of the exceptional preimage in `V(J) ×_W Bl_I W` with the projection to `Bl_I W`:
the strict transform is the scheme-theoretic image of that open. -/
theorem strictCentre_eq_ker (I J : W.IdealSheafData) :
    strictCentre I J =
      ((Stacks.StrictTransform.exceptionalComplement J.subschemeι (blowUpToBase I)
        (exceptionalIdeal I)).ι ≫ pullback.snd J.subschemeι (blowUpToBase I)).ker := by
  rw [strictCentre, Scheme.Hom.ker_comp, Scheme.Hom.ker_comp,
    Scheme.IdealSheafData.ker_subschemeι, Stacks.StrictTransform.ideal_eq_ker_ι]

section Restriction

variable {W₁ : Scheme.{u}} (g : W₁ ⟶ W) [IsOpenImmersion g] (I J : W.IdealSheafData)
  {h : blowUp (I.comap g) ⟶ blowUp I}

/-- The morphism of blow-ups in the cartesian square of [Stacks, Tag 0805] along an open
immersion is an open immersion. -/
theorem isOpenImmersion_of_isPullback
    (H : IsPullback (blowUpToBase (I.comap g)) h g (blowUpToBase I)) : IsOpenImmersion h :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion) H
    inferInstance

/-- The comparison morphism `V(J|W₁) ×_{W₁} Bl_{I|W₁} W₁ ⟶ V(J) ×_W Bl_I W` of the two base
changes on which the strict transforms live. -/
def baseChangeMap (H : IsPullback (blowUpToBase (I.comap g)) h g (blowUpToBase I)) :
    pullback (J.comap g).subschemeι (blowUpToBase (I.comap g)) ⟶
      pullback J.subschemeι (blowUpToBase I) :=
  pullback.lift
    (pullback.fst _ _ ≫ (J.comapIso g).hom ≫ pullback.snd g J.subschemeι)
    (pullback.snd _ _ ≫ h) (by
      simp only [Category.assoc]
      rw [← pullback.condition, Scheme.IdealSheafData.comapIso_hom_fst_assoc,
        pullback.condition_assoc, H.w])

omit [IsOpenImmersion g] in
/-- `V(J|W₁)` is the base change of `V(J)` along `g`. -/
theorem isPullback_subschemeι_comap :
    IsPullback (J.comap g).subschemeι ((J.comapIso g).hom ≫ pullback.snd g J.subschemeι) g
      J.subschemeι :=
  IsPullback.of_iso_pullback
    ⟨by rw [← Scheme.IdealSheafData.comapIso_hom_fst, Category.assoc, Category.assoc,
      pullback.condition]⟩
    (J.comapIso g) (Scheme.IdealSheafData.comapIso_hom_fst J g) rfl

omit [IsOpenImmersion g] in
/-- The base change on which the strict transform over `W₁` lives is the base change, along the
open immersion of blow-ups, of the one over `W`. -/
theorem isPullback_baseChangeMap
    (H : IsPullback (blowUpToBase (I.comap g)) h g (blowUpToBase I)) :
    IsPullback (baseChangeMap g I J H) (pullback.snd _ _) (pullback.snd _ _) h := by
  have h₁ := (IsPullback.of_hasPullback (J.comap g).subschemeι
    (blowUpToBase (I.comap g))).paste_horiz (isPullback_subschemeι_comap g J).flip
  rw [H.w] at h₁
  refine IsPullback.of_right (h₁₂ := pullback.fst J.subschemeι (blowUpToBase I)) ?_
    (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback J.subschemeι (blowUpToBase I))
  rw [baseChangeMap, pullback.lift_fst]
  exact h₁

/-- The comparison morphism of base changes is an open immersion. -/
theorem isOpenImmersion_baseChangeMap
    (H : IsPullback (blowUpToBase (I.comap g)) h g (blowUpToBase I)) :
    IsOpenImmersion (baseChangeMap g I J H) :=
  haveI := isOpenImmersion_of_isPullback g I H
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion)
    (isPullback_baseChangeMap g I J H).flip inferInstance

omit [IsOpenImmersion g] in
/-- The exceptional complement over `W₁` is the inverse image of the one over `W`. -/
theorem preimage_exceptionalComplement
    (H : IsPullback (blowUpToBase (I.comap g)) h g (blowUpToBase I)) :
    baseChangeMap g I J H ⁻¹ᵁ
        Stacks.StrictTransform.exceptionalComplement J.subschemeι (blowUpToBase I)
          (exceptionalIdeal I) =
      Stacks.StrictTransform.exceptionalComplement (J.comap g).subschemeι
        (blowUpToBase (I.comap g)) (exceptionalIdeal (I.comap g)) := by
  ext x
  change (pullback.snd J.subschemeι (blowUpToBase I)).base ((baseChangeMap g I J H).base x) ∈
      ((I.comap (blowUpToBase I)).support : Set (blowUp I))ᶜ ↔
    (pullback.snd (J.comap g).subschemeι (blowUpToBase (I.comap g))).base x ∈
      (((I.comap g).comap (blowUpToBase (I.comap g))).support : Set (blowUp (I.comap g)))ᶜ
  rw [← Scheme.Hom.comp_apply, baseChangeMap, pullback.lift_snd,
    ← Scheme.IdealSheafData.comap_comp, H.w, Scheme.IdealSheafData.comap_comp,
    Scheme.Hom.comp_apply]
  simp only [Scheme.IdealSheafData.support_comap]
  rfl

/-- **The strict-transform centre restricts to opens.** Along the open immersion
`Bl_{I|W₁} W₁ ⟶ Bl_I W` of the cartesian square of [Stacks, Tag 0805], the ideal of the strict
transform of `V(J)` pulls back to the ideal of the strict transform of `V(J|W₁)`. -/
theorem comap_strictCentre_of_isPullback
    (H : IsPullback (blowUpToBase (I.comap g)) h g (blowUpToBase I)) :
    (strictCentre I J).comap h = strictCentre (I.comap g) (J.comap g) := by
  have := isOpenImmersion_of_isPullback g I H
  have hsq := (isPullback_morphismRestrict (baseChangeMap g I J H)
    (Stacks.StrictTransform.exceptionalComplement J.subschemeι (blowUpToBase I)
      (exceptionalIdeal I))).paste_vert (isPullback_baseChangeMap g I J H)
  have hk := ker_eq_comap_of_isPullback hsq.flip
  rw [preimage_exceptionalComplement g I J H] at hk
  rw [strictCentre_eq_ker, strictCentre_eq_ker, hk]

/-- **The tower restricts to opens.** For an open immersion `g : W₁ ⟶ W`, the tower of the
restricted centres over `W₁` is the base change along `g` of the tower over `W`. -/
theorem exists_isPullback_strictTower :
    ∃ t : blowUp (strictCentre (I.comap g) (J.comap g)) ⟶ blowUp (strictCentre I J),
      IsPullback (strictTower (I.comap g) (J.comap g)) t g (strictTower I J) := by
  obtain ⟨h, H⟩ := exists_isPullback_blowUpToBase_comap g I
  have := isOpenImmersion_of_isPullback g I H
  have := exists_isPullback_blowUpToBase_comap h (strictCentre I J)
  rw [comap_strictCentre_of_isPullback g I J H] at this
  obtain ⟨t, T⟩ := this
  exact ⟨t, T.paste_horiz H⟩

end Restriction

/-- **The restriction of the tower over an open.** For an open `V ⊆ W`, the restriction of the
tower `strictTower I J` over `V` is, as a scheme over `V`, the tower of the restricted centres
`I|V` and `J|V`. -/
theorem nonempty_restrictIso (I J : W.IdealSheafData) (V : W.Opens) :
    Nonempty (Over.mk (strictTower (I.comap V.ι) (J.comap V.ι)) ≅
      Over.mk (strictTower I J ∣_ V)) := by
  obtain ⟨t, T⟩ := exists_isPullback_strictTower V.ι I J
  let e := T.isoIsPullback _ _ (isPullback_morphismRestrict (strictTower I J) V)
  exact ⟨Over.isoMk e (T.isoIsPullback_hom_fst _ _ _)⟩

end AlgebraicGeometry.TwoStepTower

end
