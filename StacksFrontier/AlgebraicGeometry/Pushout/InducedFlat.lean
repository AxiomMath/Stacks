module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Pushout.InducedMorphism
public import StacksFrontier.RingTheory.MilnorPatching.Algebras

/-!
# Flatness of the morphism between pushouts induced by compatible morphisms

Let `i : Z ⟶ X` and `j : Z ⟶ Y` be closed immersions of schemes, let `f : X' ⟶ X` and
`g : Y' ⟶ Y` be morphisms and let the two inverse images of `Z` be identified over `Z`, as in
`AlgebraicGeometry.CompatiblePushoutMorphismSituation`.  This file compares flatness, and
flatness together with local finite presentation, of the induced morphism
`X' ⨿ Y' ⟶ Y ⨿_Z X` with the same properties of `f` and of `g`.

## Main results

* `AlgebraicGeometry.flat_induced_iff`: the induced morphism is flat if and only if both
  morphisms on the pieces are flat.
* `AlgebraicGeometry.flat_locallyOfFinitePresentation_induced_iff`: the induced morphism is flat
  and locally of finite presentation if and only if both morphisms on the pieces are.

## Implementation notes

Both clauses use the same reduction, so it is carried out once and its conclusion records the
two equivalences side by side.

## References

* [Stacks Project, Tag 0CYY](https://stacks.math.columbia.edu/tag/0CYY)
* [Stacks Project, Tag 08KQ](https://stacks.math.columbia.edu/tag/08KQ)
* [Stacks Project, Tag 0E25](https://stacks.math.columbia.edu/tag/0E25)
* [Stacks Project, Tag 0B7M](https://stacks.math.columbia.edu/tag/0B7M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Flatness is stable under composition with a localization away from an element on the
source. -/
private lemma flat_localizationAwaySource :
    RingHom.StableUnderCompositionWithLocalizationAwaySource RingHom.Flat :=
  (RingHom.Flat.stableUnderComposition.stableUnderCompositionWithLocalizationAway
    RingHom.Flat.holdsForLocalizationAway).left

/-- Finite presentation is stable under composition with a localization away from an element on
the source. -/
private lemma finitePresentation_localizationAwaySource :
    RingHom.StableUnderCompositionWithLocalizationAwaySource @RingHom.FinitePresentation :=
  (RingHom.finitePresentation_stableUnderComposition.stableUnderCompositionWithLocalizationAway
    RingHom.finitePresentation_holdsForLocalizationAway).left

/-- A map `h : R ⟶ R'` between two fibre products of rings whose two base changes are `f` and `g`
is flat exactly when `f` and `g` are, and is flat and of finite presentation exactly when `f` and
`g` are.  This is [Stacks Project, Tag 08KQ] transported along the identification of `R` and `R'`
with the standard fibre products. -/
private lemma flat_and_finitePresentation_iff_of_isPullback
    {R A B C R' A' B' C' : CommRingCat.{u}}
    {a : R ⟶ A} {b : R ⟶ B} {i : A ⟶ C} {j : B ⟶ C}
    {a' : R' ⟶ A'} {b' : R' ⟶ B'} {i' : A' ⟶ C'} {j' : B' ⟶ C'}
    (h : R ⟶ R') (f : A ⟶ A') (g : B ⟶ B') (k : C ⟶ C')
    (H : IsPullback a b i j) (H' : IsPullback a' b' i' j')
    (Hf : IsPushout f i i' k) (Hg : IsPushout g j j' k)
    (hj : Function.Surjective j)
    (ha : a ≫ f = h ≫ a') (hb : b ≫ g = h ≫ b') :
    (h.hom.Flat ↔ f.hom.Flat ∧ g.hom.Flat) ∧
      ((h.hom.Flat ∧ h.hom.FinitePresentation) ↔
        (f.hom.Flat ∧ f.hom.FinitePresentation) ∧
          (g.hom.Flat ∧ g.hom.FinitePresentation)) := by
  let base : RingFibreProduct.Situation i.hom j.hom (RingHom.ker j.hom) := ⟨hj, rfl⟩
  have H₀ := IsPullback.of_isLimit (CommRingCat.pullbackConeIsLimit i j)
  have H₁ := IsPullback.of_isLimit (CommRingCat.pullbackConeIsLimit i' j')
  let e := H.isoIsPullback A B H₀
  let e' := H'.isoIsPullback A' B' H₁
  have hf := MilnorPatching.ringPushout_of_isPushout f.hom i.hom i'.hom k.hom Hf
  have hg := MilnorPatching.ringPushout_of_isPushout g.hom j.hom j'.hom k.hom Hg
  have criterion := MilnorPatching.ringHom_properties_pullback_iff_and_reconstruction
    i.hom j.hom (RingHom.ker j.hom) base f.hom g.hom k.hom i'.hom j'.hom hf hg
  dsimp only at criterion
  let t := RingHom.codRestrict
    ((f.hom.comp base.pullbackCone.fst.hom).prod
      (g.hom.comp base.pullbackCone.snd.hom)) (RingHom.pullback i'.hom j'.hom)
    (fun x => by
      show i'.hom (f.hom x.1.1) = j'.hom (g.hom x.1.2)
      have hf' := congrArg (fun q : A ⟶ C' => q.hom x.1.1) Hf.w
      have hg' := congrArg (fun q : B ⟶ C' => q.hom x.1.2) Hg.w
      exact hf'.trans ((congrArg k.hom x.2).trans hg'.symm))
  have ht : h ≫ e'.hom = e.hom ≫ CommRingCat.ofHom t := by
    apply H₁.hom_ext
    · have ht₁ : CommRingCat.ofHom t ≫ (CommRingCat.pullbackCone i' j').fst =
          (CommRingCat.pullbackCone i j).fst ≫ f := rfl
      calc
        _ = h ≫ a' := by simp [e']
        _ = a ≫ f := ha.symm
        _ = e.hom ≫ ((CommRingCat.pullbackCone i j).fst ≫ f) := by simp [e]
        _ = _ := (congrArg (fun q => e.hom ≫ q) ht₁.symm).trans (Category.assoc _ _ _).symm
    · have ht₂ : CommRingCat.ofHom t ≫ (CommRingCat.pullbackCone i' j').snd =
          (CommRingCat.pullbackCone i j).snd ≫ g := rfl
      calc
        _ = h ≫ b' := by simp [e']
        _ = b ≫ g := hb.symm
        _ = e.hom ≫ ((CommRingCat.pullbackCone i j).snd ≫ g) := by simp [e]
        _ = _ := (congrArg (fun q => e.hom ≫ q) ht₂.symm).trans (Category.assoc _ _ _).symm
  let ea : Arrow.mk h ≅ Arrow.mk (CommRingCat.ofHom t) := Arrow.isoMk e e' ht.symm
  exact ⟨(RingHom.Flat.respectsIso.arrow_mk_iso_iff ea).trans criterion.2.1,
    ((RingHom.Flat.respectsIso.and RingHom.finitePresentation_respectsIso).arrow_mk_iso_iff
      ea).trans criterion.2.2.1⟩

/-- The sections of a pushout of a closed immersion `j` along an integral morphism `i` over an
open `U`, in the shape in which the map induced by `j` is the restriction to the inverse image
of the inverse image of `U` under the other leg.  This is
[Stacks Project, Tag 0E25] with the two legs of the cospan interchanged. -/
private lemma isPullback_appLE_of_isPushout
    {X Y Z P : Scheme.{u}} {i : Z ⟶ X} {j : Z ⟶ Y}
    {a : X ⟶ P} {b : Y ⟶ P} [IsIntegralHom i] [IsClosedImmersion j]
    [IsAffineHom b] (H : IsPushout i j a b) (U : P.Opens) :
    IsPullback (a.app U) (b.app U) (i.app (a ⁻¹ᵁ U))
      (j.appLE (b ⁻¹ᵁ U) (i ⁻¹ᵁ (a ⁻¹ᵁ U)) (by
        rw [← Scheme.Hom.comp_preimage, H.w, Scheme.Hom.comp_preimage])) := by
  have h := structureSheaf_isPullback_of_isPushout_of_isAffineHom H.flip U
  convert h using 1
  simp only [Scheme.Hom.appLE]
  congr 1
  have he : j ⁻¹ᵁ (b ⁻¹ᵁ U) = i ⁻¹ᵁ (a ⁻¹ᵁ U) :=
    congrArg (fun f : Z ⟶ P => f ⁻¹ᵁ U) H.w.symm
  convert eqToHom_map Z.presheaf (congrArg Opposite.op he) using 1
  congr 1

/-- For a morphism `h` of pushouts coming from a cartesian pair of morphisms `f` and `g` of the
pieces, the map on sections over an affine open is flat, resp. flat and of finite presentation,
exactly when the corresponding maps induced by `f` and `g` are. -/
private lemma flat_and_finitePresentation_appLE_iff
    {X Y Z P X' Y' Z' P' : Scheme.{u}}
    {i : Z ⟶ X} {j : Z ⟶ Y} {a : X ⟶ P} {b : Y ⟶ P}
    {i' : Z' ⟶ X'} {j' : Z' ⟶ Y'} {a' : X' ⟶ P'} {b' : Y' ⟶ P'}
    [IsIntegralHom i] [IsClosedImmersion j]
    [IsIntegralHom i'] [IsClosedImmersion j']
    [IsAffineHom a] [IsAffineHom b] [IsAffineHom a'] [IsAffineHom b']
    (h : P' ⟶ P) (f : X' ⟶ X) (g : Y' ⟶ Y) (k : Z' ⟶ Z)
    (H : IsPushout i j a b) (H' : IsPushout i' j' a' b')
    (Hf : IsPullback i' k f i) (Hg : IsPullback j' k g j)
    (ha : a' ≫ h = f ≫ a) (hb : b' ≫ h = g ≫ b)
    (U : P.Opens) (V : P'.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (e : V ≤ h ⁻¹ᵁ U) :
    ((h.appLE U V e).hom.Flat ↔
        (f.appLE (a ⁻¹ᵁ U) (a' ⁻¹ᵁ V) (preimage_le_preimage_of_comm ha e)).hom.Flat ∧
        (g.appLE (b ⁻¹ᵁ U) (b' ⁻¹ᵁ V) (preimage_le_preimage_of_comm hb e)).hom.Flat) ∧
      (((h.appLE U V e).hom.Flat ∧ (h.appLE U V e).hom.FinitePresentation) ↔
        ((f.appLE (a ⁻¹ᵁ U) (a' ⁻¹ᵁ V) (preimage_le_preimage_of_comm ha e)).hom.Flat ∧
            (f.appLE (a ⁻¹ᵁ U) (a' ⁻¹ᵁ V)
              (preimage_le_preimage_of_comm ha e)).hom.FinitePresentation) ∧
          ((g.appLE (b ⁻¹ᵁ U) (b' ⁻¹ᵁ V) (preimage_le_preimage_of_comm hb e)).hom.Flat ∧
            (g.appLE (b ⁻¹ᵁ U) (b' ⁻¹ᵁ V)
              (preimage_le_preimage_of_comm hb e)).hom.FinitePresentation)) := by
  let UX := a ⁻¹ᵁ U
  let UY := b ⁻¹ᵁ U
  let UZ := i ⁻¹ᵁ UX
  let VX := a' ⁻¹ᵁ V
  let VY := b' ⁻¹ᵁ V
  let VZ := i' ⁻¹ᵁ VX
  have hUZ : UZ = j ⁻¹ᵁ UY := congrArg (fun q : Z ⟶ P => q ⁻¹ᵁ U) H.w
  have hVZ : VZ = j' ⁻¹ᵁ VY := congrArg (fun q : Z' ⟶ P' => q ⁻¹ᵁ V) H'.w
  have ef : VX ≤ f ⁻¹ᵁ UX := preimage_le_preimage_of_comm ha e
  have eg : VY ≤ g ⁻¹ᵁ UY := preimage_le_preimage_of_comm hb e
  have ek : VZ ≤ k ⁻¹ᵁ UZ := (i'.preimage_mono ef).trans_eq
    (congrArg (fun q : Z' ⟶ X => q ⁻¹ᵁ UX) Hf.w)
  have sqf : IsPushout (f.appLE UX VX ef) (i.appLE UX UZ le_rfl)
      (i'.appLE VX VZ le_rfl) (k.appLE UZ VZ ek) := by
    have hv : VZ = i' ⁻¹ᵁ VX ⊓ k ⁻¹ᵁ UZ := (inf_eq_left.mpr ek).symm
    exact (isIso_pushoutSection_iff Hf le_rfl ef hv).mp
      (isIso_pushoutSection_of_isAffineOpen Hf (hUST := le_rfl) (hUSX := ef)
        hv (hU.preimage a) ((hU.preimage a).preimage i) (hV.preimage a'))
  have sqg : IsPushout (g.appLE UY VY eg) (j.appLE UY UZ hUZ.le)
      (j'.appLE VY VZ hVZ.le) (k.appLE UZ VZ ek) := by
    have hv : VZ = j' ⁻¹ᵁ VY ⊓ k ⁻¹ᵁ UZ := by rw [← hVZ, inf_eq_left.mpr ek]
    exact (isIso_pushoutSection_iff Hg hUZ.le eg hv).mp
      (isIso_pushoutSection_of_isAffineOpen Hg (hUST := hUZ.le) (hUSX := eg)
        hv (hU.preimage b) ((hU.preimage a).preimage i) (hV.preimage b'))
  have hj : Function.Surjective (j.appLE UY UZ hUZ.le) := by
    have hs : ∀ (W : Z.Opens) (hW : W = j ⁻¹ᵁ UY),
        Function.Surjective (j.appLE UY W hW.le) := by
      intro W hW
      subst W
      simpa only [Scheme.Hom.appLE_eq_app] using j.app_surjective UY (hU.preimage b)
    exact hs UZ hUZ
  refine flat_and_finitePresentation_iff_of_isPullback (h.appLE U V e)
    (f.appLE UX VX ef) (g.appLE UY VY eg) (k.appLE UZ VZ ek)
    (isPullback_appLE_of_isPushout H U) (isPullback_appLE_of_isPushout H' V)
    (by simpa only [UZ, VZ, UX, VX, Scheme.Hom.appLE_eq_app] using sqf) sqg hj ?_ ?_
  · dsimp only [UX, VX]
    simp only [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, ha]
  · dsimp only [UY, VY]
    simp only [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, hb]

namespace CompatiblePushoutMorphismSituation

variable (S : CompatiblePushoutMorphismSituation.{u})

/-- The map on sections of the induced morphism over an affine open is flat, resp. flat and of
finite presentation, exactly when the corresponding maps induced by `f` and `g` are. -/
private lemma flat_and_finitePresentation_induced_appLE_iff
    (U : (pushout S.i S.j).Opens) (V : S.sourcePushout.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (e : V ≤ S.induced ⁻¹ᵁ U) :
    ((S.induced.appLE U V e).hom.Flat ↔
        (S.f.appLE (pushout.inl S.i S.j ⁻¹ᵁ U) (pushout.inl S.toX' S.toY' ⁻¹ᵁ V)
          (preimage_le_preimage_of_comm (inl_comp_induced S) e)).hom.Flat ∧
        (S.g.appLE (pushout.inr S.i S.j ⁻¹ᵁ U) (pushout.inr S.toX' S.toY' ⁻¹ᵁ V)
          (preimage_le_preimage_of_comm (inr_comp_induced S) e)).hom.Flat) ∧
      (((S.induced.appLE U V e).hom.Flat ∧ (S.induced.appLE U V e).hom.FinitePresentation) ↔
        ((S.f.appLE (pushout.inl S.i S.j ⁻¹ᵁ U) (pushout.inl S.toX' S.toY' ⁻¹ᵁ V)
              (preimage_le_preimage_of_comm (inl_comp_induced S) e)).hom.Flat ∧
            (S.f.appLE (pushout.inl S.i S.j ⁻¹ᵁ U) (pushout.inl S.toX' S.toY' ⁻¹ᵁ V)
              (preimage_le_preimage_of_comm (inl_comp_induced S) e)).hom.FinitePresentation) ∧
          ((S.g.appLE (pushout.inr S.i S.j ⁻¹ᵁ U) (pushout.inr S.toX' S.toY' ⁻¹ᵁ V)
              (preimage_le_preimage_of_comm (inr_comp_induced S) e)).hom.Flat ∧
            (S.g.appLE (pushout.inr S.i S.j ⁻¹ᵁ U) (pushout.inr S.toX' S.toY' ⁻¹ᵁ V)
              (preimage_le_preimage_of_comm (inr_comp_induced S) e)).hom.FinitePresentation)) := by
  have Hf : IsPullback S.toX' (pullback.snd S.f S.i) S.f S.i :=
    IsPullback.of_hasPullback S.f S.i
  have Hg : IsPullback S.toY' (pullback.snd S.f S.i) S.g S.j := by
    apply (IsPullback.of_hasPullback S.g S.j).of_iso'
      S.φ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · simp [toY']
    · simpa using S.φ_over
    · simp
    · simp
  exact flat_and_finitePresentation_appLE_iff S.induced S.f S.g (pullback.snd S.f S.i)
    (IsPushout.of_hasPushout S.i S.j) (IsPushout.of_hasPushout S.toX' S.toY')
    Hf Hg (inl_comp_induced S) (inr_comp_induced S) U V hU hV e

/-- A property detected on sections holds for both `f` and `g` as soon as it holds for the maps on
sections induced by `f` and `g` over the inverse images of affine opens of the pushouts. -/
private lemma of_forall_appLE_induced {P : MorphismProperty Scheme.{u}}
    {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    [HasRingHomProperty P Q] (hQ : RingHom.StableUnderCompositionWithLocalizationAwaySource Q)
    (H : ∀ (U : (pushout S.i S.j).Opens) (V : S.sourcePushout.Opens),
      IsAffineOpen U → IsAffineOpen V → ∀ e : V ≤ S.induced ⁻¹ᵁ U,
        Q (S.f.appLE (pushout.inl S.i S.j ⁻¹ᵁ U) (pushout.inl S.toX' S.toY' ⁻¹ᵁ V)
            (preimage_le_preimage_of_comm (inl_comp_induced S) e)).hom ∧
        Q (S.g.appLE (pushout.inr S.i S.j ⁻¹ᵁ U) (pushout.inr S.toX' S.toY' ⁻¹ᵁ V)
            (preimage_le_preimage_of_comm (inr_comp_induced S) e)).hom) :
    P S.f ∧ P S.g :=
  ⟨of_forall_appLE_preimage hQ S.f S.induced (pushout.inl S.i S.j) (pushout.inl S.toX' S.toY')
      (inl_comp_induced S) fun U V hU hV e => (H U V hU hV e).1,
    of_forall_appLE_preimage hQ S.g S.induced (pushout.inr S.i S.j) (pushout.inr S.toX' S.toY')
      (inr_comp_induced S) fun U V hU hV e => (H U V hU hV e).2⟩

end CompatiblePushoutMorphismSituation

open CompatiblePushoutMorphismSituation in
/-- In the situation of `AlgebraicGeometry.CompatiblePushoutMorphismSituation`, the induced
morphism between the two pushouts is flat if and only if both morphisms on the pieces are flat. -/
@[stacks 0CYY "flat"]
theorem flat_induced_iff (S : CompatiblePushoutMorphismSituation.{u}) :
    Flat S.induced ↔ Flat S.f ∧ Flat S.g := by
  constructor
  · intro _
    exact of_forall_appLE_induced (P := @Flat) S flat_localizationAwaySource fun U V hU hV e =>
      (flat_and_finitePresentation_induced_appLE_iff S U V hU hV e).1.mp
        (S.induced.flat_appLE hU hV e)
  · rintro ⟨_, _⟩
    refine ⟨?_⟩
    intro U hU V hV e
    exact (flat_and_finitePresentation_induced_appLE_iff S U V hU hV e).1.mpr
      ⟨S.f.flat_appLE (hU.preimage _) (hV.preimage _) _,
        S.g.flat_appLE (hU.preimage _) (hV.preimage _) _⟩

open CompatiblePushoutMorphismSituation in
/-- In the situation of `AlgebraicGeometry.CompatiblePushoutMorphismSituation`, the induced
morphism between the two pushouts is flat and locally of finite presentation if and only if both
morphisms on the pieces are flat and locally of finite presentation. -/
@[stacks 0CYY "flat_locally_of_finite_presentation"]
theorem flat_locallyOfFinitePresentation_induced_iff
    (S : CompatiblePushoutMorphismSituation.{u}) :
    (Flat S.induced ∧ LocallyOfFinitePresentation S.induced) ↔
      ((Flat S.f ∧ LocallyOfFinitePresentation S.f) ∧
        (Flat S.g ∧ LocallyOfFinitePresentation S.g)) := by
  constructor
  · rintro ⟨_, _⟩
    have key (U : (pushout S.i S.j).Opens) (V : S.sourcePushout.Opens)
        (hU : IsAffineOpen U) (hV : IsAffineOpen V) (e : V ≤ S.induced ⁻¹ᵁ U) :=
      (flat_and_finitePresentation_induced_appLE_iff S U V hU hV e).2.mp
        ⟨S.induced.flat_appLE hU hV e, S.induced.finitePresentation_appLE hU hV e⟩
    obtain ⟨hf, hg⟩ := of_forall_appLE_induced (P := @Flat) S flat_localizationAwaySource
      fun U V hU hV e => ⟨(key U V hU hV e).1.1, (key U V hU hV e).2.1⟩
    obtain ⟨hf', hg'⟩ := of_forall_appLE_induced (P := @LocallyOfFinitePresentation) S
      finitePresentation_localizationAwaySource
      fun U V hU hV e => ⟨(key U V hU hV e).1.2, (key U V hU hV e).2.2⟩
    exact ⟨⟨hf, hf'⟩, hg, hg'⟩
  · rintro ⟨⟨_, _⟩, ⟨_, _⟩⟩
    have key (U : (pushout S.i S.j).Opens) (V : S.sourcePushout.Opens)
        (hU : IsAffineOpen U) (hV : IsAffineOpen V) (e : V ≤ S.induced ⁻¹ᵁ U) :
        (S.induced.appLE U V e).hom.Flat ∧
          (S.induced.appLE U V e).hom.FinitePresentation :=
      (flat_and_finitePresentation_induced_appLE_iff S U V hU hV e).2.mpr
        ⟨⟨S.f.flat_appLE (hU.preimage _) (hV.preimage _) _,
            S.f.finitePresentation_appLE (hU.preimage _) (hV.preimage _) _⟩,
          ⟨S.g.flat_appLE (hU.preimage _) (hV.preimage _) _,
            S.g.finitePresentation_appLE (hU.preimage _) (hV.preimage _) _⟩⟩
    refine ⟨⟨?_⟩, ⟨?_⟩⟩
    · intro U hU V hV e
      exact (key U V hU hV e).1
    · intro U hU V hV e
      exact (key U V hU hV e).2

end AlgebraicGeometry

end
