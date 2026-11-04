module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.UniqueExtensionCover
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.UniqueExtensionDepth
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.UniqueExtensionUniqueness
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProperFiniteCase
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityPowerSeriesRestriction
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.Permanence
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.EtaleAt

/-!
# A finite extension that is trivial along the zero section of a power series ring

Let `(A, 𝔪)` be a Noetherian local ring of depth at least two, `T = Spec A[[x_1, …, x_d]]`, and
`s : Spec A ⟶ T` the zero section `x = 0`. Let `V ⊆ T` be an open whose inverse image under `s`
is the punctured spectrum of `A`, and let `W` be a finite étale cover of `V` whose restriction
along `s` to the punctured spectrum is the restriction of a finite étale cover `F₀` of `Spec A`.
Then every finite morphism `E ⟶ T` restricting to `W` over `V`, with local rings of depth at
least two above `T ∖ V`, is étale.

This is the last paragraph of the proof of [Stacks, Tag 0EYJ]. By [Stacks, Tag 0EY9] restriction
along `s` is fully faithful on finite étale covers of `V`, so `W` is the restriction of the base
change `F` of `F₀` along `T ⟶ Spec A`. Both `E` and `F` are then the extension of `W` across
`T ∖ V` by the uniqueness clause of [Stacks, Tag 0EY6], so `E ≅ F` is étale.

## Main results

* `AlgebraicGeometry.etale_of_isPullback_of_zeroSection_iso`.

## References

* [Stacks Project, Tag 0EY6](https://stacks.math.columbia.edu/tag/0EY6)
* [Stacks Project, Tag 0EY9](https://stacks.math.columbia.edu/tag/0EY9)
* [Stacks Project, Tag 0EYJ](https://stacks.math.columbia.edu/tag/0EYJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing
open Stacks.FundamentalGroup.ExtendedEtaleFold Stacks.RelativeSpec

universe u

namespace AlgebraicGeometry

/-- Base change of finite étale covers along the restriction of the zero section
`Spec A ⟶ Spec A[[x_1, …, x_d]]` to an open `V` with `s⁻¹(V)` the punctured spectrum is fully
faithful: for `d ≥ 1` this is [Stacks, Tag 0EY9], and for `d = 0` the zero section is an
isomorphism. -/
theorem nonempty_fullyFaithful_finiteEtaleBaseChange_zeroSection (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (d : ℕ)
    (hdepth : (2 : ℕ∞) ≤ Module.depth A (maximalIdeal A) A)
    (V : (Spec (.of (MvPowerSeries (Fin d) A))).Opens)
    (hV : (Spec.map (CommRingCat.ofHom
        (MvPowerSeries.constantCoeff : MvPowerSeries (Fin d) A →+* A)) ⁻¹ᵁ V :
      Set (Spec (.of A))) = {closedPoint A}ᶜ) :
    Nonempty (finiteEtaleBaseChange (Spec.map (CommRingCat.ofHom
      (MvPowerSeries.constantCoeff : MvPowerSeries (Fin d) A →+* A)) ∣_ V)).FullyFaithful := by
  obtain rfl | hd := Nat.eq_zero_or_pos d
  · have : IsIso (CommRingCat.ofHom
        (MvPowerSeries.constantCoeff : MvPowerSeries (Fin 0) A →+* A)) :=
      (MvPowerSeries.isEmptyEquiv (Fin 0) A).toRingEquiv.toCommRingCatIso.isIso_hom
    have := isEquivalence_finiteEtaleBaseChange_of_isIso (Spec.map (CommRingCat.ofHom
      (MvPowerSeries.constantCoeff : MvPowerSeries (Fin 0) A →+* A)) ∣_ V)
    exact ⟨Functor.FullyFaithful.ofFullyFaithful _⟩
  · exact Stacks.FundamentalGroup.fullyFaithful_finiteEtaleBaseChange_restrict_mvPowerSeries A d hd
      hdepth V hV

/-- **A finite extension trivial along the zero section is étale.** Let `(A, 𝔪)` be a Noetherian
local ring of depth at least two, `T = Spec A[[x_1, …, x_d]]`, `s : Spec A ⟶ T` the zero section
and `V ⊆ T` an open with `s⁻¹(V)` the punctured spectrum of `A`, such that the local rings of `T`
at the points outside `V` have depth at least two. Let `g : E ⟶ T` be finite whose restriction
over `V` is a finite étale cover `W` of `V`, with local rings of depth at least two above
`T ∖ V`. If the restriction of `W` along `s` is the restriction of a finite étale cover `F₀` of
`Spec A` to the punctured spectrum, then `g` is étale.

Let `p : T ⟶ Spec A` be the structure map and `F = p^* F₀`. Since `s ≫ p = 𝟙`, the restrictions
of `F` and of `W` along `s` agree, so `F|_V ≅ W` by
`nonempty_fullyFaithful_finiteEtaleBaseChange_zeroSection` ([Stacks, Tag 0EY9]). `F` is étale over
`T`, so its local rings above `T ∖ V` have depth at least two ([Stacks, Tag 039T]); hence both `E`
and `F` are the extension of `W` of [Stacks, Tag 0EY6], `E ≅ F` over `T`, and `g` is étale. -/
theorem etale_of_isPullback_of_zeroSection_iso (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (d : ℕ)
    (hdepth : (2 : ℕ∞) ≤ Module.depth A (maximalIdeal A) A)
    (V : (Spec (.of (MvPowerSeries (Fin d) A))).Opens)
    (hV : (Spec.map (CommRingCat.ofHom
        (MvPowerSeries.constantCoeff : MvPowerSeries (Fin d) A →+* A)) ⁻¹ᵁ V :
      Set (Spec (.of A))) = {closedPoint A}ᶜ)
    (hdepthT : ∀ q : Spec (.of (MvPowerSeries (Fin d) A)), q ∉ V →
      (2 : ℕ∞) ≤ Module.depth ((Spec (.of (MvPowerSeries (Fin d) A))).presheaf.stalk q)
        (maximalIdeal ((Spec (.of (MvPowerSeries (Fin d) A))).presheaf.stalk q))
        ((Spec (.of (MvPowerSeries (Fin d) A))).presheaf.stalk q))
    {E : Scheme.{u}} (g : E ⟶ Spec (.of (MvPowerSeries (Fin d) A))) [IsFinite g]
    (hdepthE : ∀ e : E, g e ∉ V →
      (2 : ℕ∞) ≤ Module.depth (E.presheaf.stalk e) (maximalIdeal (E.presheaf.stalk e))
        (E.presheaf.stalk e))
    (W : FiniteEtaleOver V.toScheme) (c : W.left ⟶ E) (hc : IsPullback W.hom c V.ι g)
    (F₀ : FiniteEtaleOver (Spec (.of A)))
    (e₀ : (finiteEtaleBaseChange (Spec.map (CommRingCat.ofHom
        (MvPowerSeries.constantCoeff : MvPowerSeries (Fin d) A →+* A)) ∣_ V)).obj W ≅
      (finiteEtaleBaseChange (Spec.map (CommRingCat.ofHom
        (MvPowerSeries.constantCoeff : MvPowerSeries (Fin d) A →+* A)) ⁻¹ᵁ V).ι).obj F₀) :
    Etale g := by
  classical
  let T : Scheme.{u} := Spec (.of (MvPowerSeries (Fin d) A))
  let s : Spec (.of A) ⟶ T := Spec.map (CommRingCat.ofHom
    (MvPowerSeries.constantCoeff : MvPowerSeries (Fin d) A →+* A))
  let p : T ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom
    (MvPowerSeries.C : A →+* MvPowerSeries (Fin d) A))
  have hsp : s ≫ p = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
  let i := s ∣_ V
  have hk : (s ⁻¹ᵁ V).ι = (i ≫ V.ι) ≫ p := by
    rw [morphismRestrict_ι, Category.assoc, hsp, Category.comp_id]
  obtain ⟨hff⟩ := nonempty_fullyFaithful_finiteEtaleBaseChange_zeroSection A d hdepth V hV
  -- the cover `F = p^* F₀` of `T`
  let F : FiniteEtaleOver T := (finiteEtaleBaseChange p).obj F₀
  have : IsFinite F.hom := F.prop.1
  have : Etale F.hom := F.prop.2
  -- its restriction to `V` is `W`
  let I1 : (finiteEtaleBaseChange i).obj ((finiteEtaleBaseChange V.ι).obj F) ≅
      (finiteEtaleBaseChange i).obj W :=
    ((finiteEtaleBaseChangeComp i V.ι).app F).symm ≪≫
      ((finiteEtaleBaseChangeComp (i ≫ V.ι) p _ hk).app F₀).symm ≪≫ e₀.symm
  let ψ : (finiteEtaleBaseChange V.ι).obj F ≅ W := hff.preimageIso I1
  let ψL : ((finiteEtaleBaseChange V.ι).obj F).left ≅ W.left :=
    (MorphismProperty.Over.forget _ _ _ ⋙ Over.forget _).mapIso ψ
  have hF : IsPullback W.hom (ψ.inv.left ≫ pullback.fst F.hom V.ι) V.ι F.hom := by
    refine (IsPullback.of_hasPullback F.hom V.ι).flip.of_iso ψL (Iso.refl _) (Iso.refl _)
      (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [Iso.refl_hom, Category.comp_id]
      exact (MorphismProperty.Over.w ψ.hom).symm
    · rw [Iso.refl_hom, Category.comp_id]
      exact (ψL.hom_inv_id_assoc (pullback.fst F.hom V.ι)).symm
    · simp
    · simp
  -- depth of `F` above the complement of `V`
  have hdepthF : ∀ y : F.left, F.hom y ∉ V →
      (2 : ℕ∞) ≤ Module.depth (F.left.presheaf.stalk y) (maximalIdeal (F.left.presheaf.stalk y))
        (F.left.presheaf.stalk y) := by
    intro y hy
    have : IsLocallyNoetherian ((Functor.fromPUnit T).obj F.right) :=
      inferInstanceAs (IsLocallyNoetherian T)
    have : IsLocallyNoetherian F.left := LocallyOfFiniteType.isLocallyNoetherian F.hom
    have : IsLocallyNoetherian ((𝟭 Scheme).obj F.left) := this
    exact (hdepthT _ hy).trans_eq (RingHom.depth_eq_of_isEtaleLocalHom (F.hom.stalkMap y).hom
      ((AlgebraicGeometry.etale_iff_forall_isEtaleAt F.hom).mp inferInstance y))
  have hr : ∀ {x : T}, x ∉ (V.ι.opensRange : Set T) → x ∉ V := fun hx => by
    rwa [Scheme.Opens.opensRange_ι] at hx
  have hdV := fun x (hx : x ∉ (V.ι.opensRange : Set T)) => hdepthT x (hr hx)
  have : IsFinite W.hom := W.prop.1
  have : Etale W.hom := W.prop.2
  have : IsLocallyNoetherian T := inferInstance
  obtain ⟨eE, ⟨hEE, -⟩, -⟩ := extendedEtale_unique V.ι W.hom hdV g c hc
    (fun e he => hdepthE e (hr he))
  obtain ⟨eF, ⟨hFF, -⟩, -⟩ := extendedEtale_unique V.ι W.hom hdV F.hom _ hF
    (fun y hy => hdepthF y (hr hy))
  have hg : g = eE.hom ≫ eF.inv ≫ F.hom :=
    hEE.symm.trans (congrArg (eE.hom ≫ ·) ((Iso.eq_inv_comp eF).mpr hFF))
  rw [hg]
  infer_instance

end AlgebraicGeometry

end
