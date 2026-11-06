module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Thickenings

/-!
# Stability of thickenings under base change and composition

A thickening of schemes stays a thickening after an arbitrary base change, and so do the
first-order and finite-order variants. The pullback square itself is the canonical morphism
from the base-changed thickening to the original one. Thickenings are also stable under
composition.

## Main definitions

* `Stacks.Thickenings.baseChangeHom`: the canonical morphism of arrows given by a pullback
  square, from the base change of a thickening to the thickening itself.

## Main results

* `Stacks.Thickenings.isThickening_isStableUnderBaseChange`: thickenings are stable under
  arbitrary base change.
* `Stacks.Thickenings.isFirstOrderThickening_isStableUnderBaseChange` and
  `Stacks.Thickenings.isFiniteOrderThickening_isStableUnderBaseChange`: the same for the
  first-order and finite-order conditions.
* `Stacks.Thickenings.isFirstOrderThickening_isZariskiLocalAtTarget`: the first-order condition
  is Zariski local on the target.
* `Stacks.Thickenings.isThickening_comp` and
  `Stacks.Thickenings.isThickening_isStableUnderComposition`: a composite of thickenings is a
  thickening, as a statement and as the corresponding morphism-property instance.
* `Stacks.Thickenings.isThickening_respectsIso`: thickenings respect isomorphisms of arrows.

## References

* [Stacks Project, Tag 09ZU](https://stacks.math.columbia.edu/tag/09ZU)
* [Stacks Project, Tag 0BPE](https://stacks.math.columbia.edu/tag/0BPE)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Stacks.Thickenings

universe u

open scoped TensorProduct

/-- For a surjective `R`-algebra map `f : R → B` whose kernel has vanishing `n`th power, the
kernel of `A → A ⊗[R] B` also has vanishing `n`th power. -/
private theorem ring_baseChange_ker_pow
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    (f : R →ₐ[R] B) (hf : Function.Surjective f) (n : ℕ)
    (hn : RingHom.ker f.toRingHom ^ n = ⊥) :
    RingHom.ker (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := B)) ^ n = ⊥ := by
  let g := Algebra.TensorProduct.map (AlgHom.id R A) f
  let e := Algebra.TensorProduct.rid R R A
  have hker := Algebra.TensorProduct.lTensor_ker (A := A) f hf
  have heq : g.toRingHom.comp e.symm.toRingHom =
      Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := B) := by
    ext a
    simp [g, e, Algebra.TensorProduct.map, Algebra.TensorProduct.rid_symm_apply]
  rw [← heq]
  let J := RingHom.ker f.toRingHom
  let K := RingHom.ker (g.toRingHom.comp e.symm.toRingHom)
  apply (Ideal.map_eq_bot_iff_of_injective e.symm.injective).mp
  show Ideal.map e.symm.toRingHom (K ^ n) = ⊥
  rw [Ideal.map_pow, show Ideal.map e.symm.toRingHom K =
    Ideal.map Algebra.TensorProduct.includeRight.toRingHom J from by
      rw [show K = Ideal.comap e.symm.toRingHom (RingHom.ker g.toRingHom) from by
        simpa [K] using (RingHom.comap_ker g.toRingHom e.symm.toRingHom).symm,
        Ideal.map_comap_of_surjective e.symm.toRingHom e.symm.surjective]
      convert hker <;> rfl, ← Ideal.map_pow, hn, Ideal.map_bot]

/-- A ring map is *good of order `n`* if it is surjective with `n`th power of the kernel
zero. -/
private def GoodRingHom (n : ℕ) {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) : Prop := Function.Surjective f ∧ RingHom.ker f ^ n = ⊥

private theorem goodRingHom_respectsIso (n : ℕ) :
    RingHom.RespectsIso (GoodRingHom n) := by
  constructor
  · intro R S T _ _ _ f e hf
    exact ⟨e.surjective.comp hf.1, by rw [RingHom.ker_comp_of_injective f e.injective]; exact hf.2⟩
  · intro R S T _ _ _ f e hf
    have hmap : Ideal.map e.toRingHom (RingHom.ker (f.comp e.toRingHom) ^ n) = ⊥ := by
      rw [Ideal.map_pow, ← RingHom.comap_ker f e.toRingHom,
        Ideal.map_comap_of_surjective e.toRingHom e.surjective, hf.2]
    exact ⟨hf.1.comp e.surjective, (Ideal.map_eq_bot_iff_of_injective e.injective).mp hmap⟩

private theorem goodRingHom_stable (n : ℕ) :
    RingHom.IsStableUnderBaseChange (GoodRingHom n) := by
  apply RingHom.IsStableUnderBaseChange.mk (goodRingHom_respectsIso n)
  intro R T A _ _ _ _ _ hf
  let _ : Algebra T (T ⊗[R] A) := Algebra.TensorProduct.leftAlgebra (S := T)
  refine ⟨?_, ?_⟩
  · exact RingHom.IsStableUnderBaseChange.tensorProduct
      (P := fun {R S} [CommRing R] [CommRing S] (f : R →+* S) => Function.Surjective f)
      RingHom.surjective_isStableUnderBaseChange T hf.1
  · simpa [GoodRingHom, Algebra.TensorProduct.algebraMap_def] using
      ring_baseChange_ker_pow (Algebra.ofId R A) (by convert hf.1; rfl) n
        (by convert hf.2; rfl)

/-- If an ideal sheaf has vanishing `n`th power, so does its ideal over every affine open. -/
private theorem ideal_pow_eq_bot {X : Scheme.{u}} {I : X.IdealSheafData} {n : ℕ}
    (h : I ^ n = ⊥) (U : X.affineOpens) : I.ideal U ^ n = ⊥ :=
  congrArg (fun J : X.IdealSheafData => J.ideal U) h

/-- Every point of a scheme `A` has, under an open immersion `g : A ⟶ B`, its image contained in
the image of some affine open of `A`. -/
private theorem exists_affineOpen_image {A B : Scheme.{u}} (g : A ⟶ B) [IsOpenImmersion g]
    (a : A) : ∃ W : A.affineOpens, g a ∈ g ''ᵁ W.1 := by
  obtain ⟨W, hW⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_affineOpens_eq_top A).ge (Set.mem_univ a))
  exact ⟨W, a, hW, rfl⟩

private theorem kerPow_pullback_affine {X Y S : Scheme.{u}} [IsAffine X] [IsAffine S]
    (f : X ⟶ S) (g : Y ⟶ S) [IsClosedImmersion g] (n : ℕ)
    (hg : g.ker ^ n = (⊥ : S.IdealSheafData)) :
    (pullback.fst f g).ker ^ n = (⊥ : X.IdealSheafData) := by
  let _ : IsAffine Y := (IsClosedImmersion.isAffine_surjective_of_isAffine g).1
  have hker : RingHom.ker g.appTop.hom ^ n = ⊥ := by
    have hp := ideal_pow_eq_bot hg ⟨⊤, isAffineOpen_top S⟩
    rw [Scheme.Hom.ker_apply g _] at hp
    convert hp using 1; rfl
  have hbc : GoodRingHom n (pullback.fst f g).appTop.hom :=
    RingHom.IsStableUnderBaseChange.pullback_fst_appTop (P := GoodRingHom n)
      (goodRingHom_stable n) (goodRingHom_respectsIso n) f g
        ⟨(IsClosedImmersion.isAffine_surjective_of_isAffine g).2, hker⟩
  apply Scheme.IdealSheafData.ext_of_isAffine
  let U : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  show ((pullback.fst f g).ker.ideal U) ^ n = ⊥
  rw [Scheme.Hom.ker_apply]
  convert hbc.2 using 1; rfl

private theorem kerPow_restrict {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    (U : Y.Opens) (n : ℕ) (hf : f.ker ^ n = (⊥ : Y.IdealSheafData)) :
    (f ∣_ U).ker ^ n = (⊥ : U.toScheme.IdealSheafData) := by
  apply Scheme.IdealSheafData.ext
  funext V
  let W : Y.affineOpens := ⟨U.ι ''ᵁ V.1, V.2.image_of_isOpenImmersion U.ι⟩
  have h := ideal_pow_eq_bot hf W
  show (f ∣_ U).ker.ideal V ^ n = ⊥
  rwa [Scheme.ker_morphismRestrict_ideal f U V]

private theorem kerPow_of_target_openCover {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] (n : ℕ) {ι : Type*} (U : ι → Y.Opens)
    (hU : ⨆ i, U i = ⊤)
    (H : ∀ i, (f ∣_ U i).ker ^ n = (⊥ : (U i).toScheme.IdealSheafData)) :
    f.ker ^ n = (⊥ : Y.IdealSheafData) := by
  let V (p : Σ i, (U i).toScheme.affineOpens) : Y.affineOpens :=
    ⟨(U p.1).ι ''ᵁ p.2.1, p.2.2.image_of_isOpenImmersion _⟩
  have hV : (⨆ p, (V p).1) = ⊤ := by
    ext x
    simp only [TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion]
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hU.ge (by trivial))
    obtain ⟨W, hW⟩ := exists_affineOpen_image (U i).ι ⟨x, hi⟩
    exact ⟨⟨i, W⟩, hW⟩
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top V hV
  rintro ⟨i, W⟩
  let V' : (U i).toScheme.affineOpens := W
  let W' : Y.affineOpens := V ⟨i, V'⟩
  have h := ideal_pow_eq_bot (H i) V'
  show f.ker.ideal W' ^ n = ⊥
  rwa [← Scheme.ker_morphismRestrict_ideal f (U i) V']

/-- The property of being a closed immersion whose kernel ideal sheaf has vanishing `n`th
power. Being an `n`th-order thickening is this property at `n + 1`. -/
private def ThickeningPowProperty (n : ℕ) : MorphismProperty Scheme.{u} :=
  fun _ _ f => IsClosedImmersion f ∧ f.ker ^ n = ⊥

private theorem thickeningPowProperty_respectsIso (n : ℕ) :
    (ThickeningPowProperty n).RespectsIso := by
  apply MorphismProperty.RespectsIso.mk
  · intro X Y Z e f hf
    let _ : IsClosedImmersion f := hf.1
    refine ⟨inferInstance, ?_⟩
    rw [Scheme.Hom.ker_comp_of_isIso]
    exact hf.2
  · intro X Y Z e f hf
    let _ : IsClosedImmersion f := hf.1
    refine ⟨inferInstance, ?_⟩
    apply Scheme.IdealSheafData.ext_of_iSup_eq_top
      (fun U : Y.affineOpens =>
        (⟨e.hom ''ᵁ U.1, U.2.image_of_isOpenImmersion e.hom⟩ : Z.affineOpens)) ?_
    · intro U
      let W : Z.affineOpens :=
        ⟨e.hom ''ᵁ U.1, U.2.image_of_isOpenImmersion e.hom⟩
      have hker : f.ker.ideal U =
          ((f ≫ e.hom).ker.ideal W).comap (e.hom.appIso U).inv.hom :=
        Scheme.ker_ideal_of_isPullback_of_isOpenImmersion (f ≫ e.hom) f (𝟙 X) e.hom
          (IsPullback.of_vert_isIso ⟨by simp⟩) U
      have hmap : Ideal.map (e.hom.appIso U).inv.hom (f.ker.ideal U ^ n) = ⊥ := by
        rw [ideal_pow_eq_bot hf.2, Ideal.map_bot]
      rwa [Ideal.map_pow, hker, Ideal.map_comap_of_surjective _
        (ConcreteCategory.bijective_of_isIso (e.hom.appIso U).inv).2] at hmap
    · ext z
      simp only [TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion]
      refine ⟨fun _ => trivial, fun _ => ?_⟩
      obtain ⟨U, hz⟩ := exists_affineOpen_image e.hom (e.inv z)
      exact ⟨U, (by simp : e.hom (e.inv z) = z) ▸ hz⟩

private theorem thickeningPowProperty_isZariskiLocalAtTarget (n : ℕ) :
    IsZariskiLocalAtTarget (ThickeningPowProperty n) := by
  let _ := thickeningPowProperty_respectsIso n
  apply IsZariskiLocalAtTarget.mk'
  · intro X Y f U hf
    have := hf.1
    exact ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @IsClosedImmersion) (isPullback_morphismRestrict f U).flip hf.1,
      kerPow_restrict f U n hf.2⟩
  · intro X Y f ι U hU H
    have : IsClosedImmersion f :=
      IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsClosedImmersion) U hU fun i => (H i).1
    exact ⟨this, kerPow_of_target_openCover f n U hU fun i => (H i).2⟩

open AffineTargetMorphismProperty in
private theorem thickeningPowProperty_stable (n : ℕ) :
    (ThickeningPowProperty n).IsStableUnderBaseChange := by
  let _ := thickeningPowProperty_isZariskiLocalAtTarget n
  apply isStableUnderBaseChange_of_isStableUnderBaseChangeOnAffine_of_isZariskiLocalAtTarget
  apply AffineTargetMorphismProperty.IsStableUnderBaseChange.mk
  intro X Y S _ _ f g hg
  have := hg.1
  exact ⟨IsClosedImmersion.isStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback f g).flip hg.1, kerPow_pullback_affine f g n hg.2⟩

/-- The canonical morphism from the base change of a thickening `i : S ⟶ S'` along
`f : X' ⟶ S'` to `i` itself: the commutative square given by the pullback. -/
@[stacks 09ZU "canonical morphism of thickenings"]
noncomputable def baseChangeHom {S S' X' : Scheme.{u}}
    (i : S ⟶ S') (f : X' ⟶ S') :
    Arrow.mk (pullback.snd i f) ⟶ Arrow.mk i :=
  Arrow.homMk' (pullback.fst i f) f pullback.condition

/-- Thickenings of schemes are stable under arbitrary base change. -/
@[stacks 09ZU "base change of thickenings"]
instance isThickening_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange
      (@IsThickening : MorphismProperty Scheme.{u}) := by
  refine ⟨fun sq hg => ⟨IsClosedImmersion.isStableUnderBaseChange.of_isPullback sq hg.1, ?_⟩⟩
  exact (MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @AlgebraicGeometry.Surjective) sq ⟨hg.2⟩).surj

/-- First-order thickenings of schemes are stable under arbitrary base change. -/
@[stacks 09ZU "base change of first-order thickenings"]
instance isFirstOrderThickening_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange
      (@IsFirstOrderThickening : MorphismProperty Scheme.{u}) := by
  change MorphismProperty.IsStableUnderBaseChange (ThickeningPowProperty 2)
  exact thickeningPowProperty_stable 2

/-- Being a first-order thickening is Zariski local on the target: a morphism is a first-order
thickening as soon as its restrictions over the members of an open cover of the target are. -/
theorem isFirstOrderThickening_isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget (@IsFirstOrderThickening : MorphismProperty Scheme.{u}) :=
  thickeningPowProperty_isZariskiLocalAtTarget 2

/-- Finite-order thickenings of schemes are stable under arbitrary base change. -/
@[stacks 09ZU "base change of finite-order thickenings"]
instance isFiniteOrderThickening_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange
      (@IsFiniteOrderThickening : MorphismProperty Scheme.{u}) := by
  refine ⟨fun sq ⟨hc, n, hn⟩ => ⟨IsClosedImmersion.isStableUnderBaseChange.of_isPullback sq hc, n,
    ((thickeningPowProperty_stable (n + 1)).of_isPullback sq ⟨hc, hn⟩).2⟩⟩

/-- A composite of thickenings is a thickening. -/
@[stacks 0BPE]
theorem isThickening_comp {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsThickening f) (hg : IsThickening g) : IsThickening (f ≫ g) :=
  ⟨@IsClosedImmersion.comp X Y Z f g hf.1 hg.1, hg.2.comp hf.2⟩

/-- An isomorphism is a thickening. -/
theorem isThickening_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    IsThickening f := ⟨inferInstance, Scheme.Hom.surjective f⟩

/-- Thickenings of schemes are stable under composition, as a morphism property. -/
instance isThickening_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition
      (@IsThickening : MorphismProperty Scheme.{u}) :=
  ⟨fun _ _ hf hg => isThickening_comp hf hg⟩

/-- Thickenings of schemes respect isomorphisms of arrows. -/
instance isThickening_respectsIso :
    MorphismProperty.RespectsIso (@IsThickening : MorphismProperty Scheme.{u}) :=
  .mk _ (fun e _ hf => isThickening_comp (isThickening_of_isIso e.hom) hf)
    fun e _ hf => isThickening_comp hf (isThickening_of_isIso e.hom)

end Stacks.Thickenings

end
