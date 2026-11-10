module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionULiftTransfer
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalProperty
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableCancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedFiniteType

/-!
# Cancelling an étale factor of a representable étale morphism

Let `S` be a scheme contained in a big fppf site `B`. If `k : U ⟶ W` and `q : W ⟶ X` are
morphisms of fppf sheaves over `S` such that `q` and `k ≫ q` are representable by algebraic
spaces and étale, and `W` is an affine formal algebraic space, then `k` is representable by
algebraic spaces and étale.

This is the formal-space form of **Stacks 05W3** (equivalently **Stacks 03FV**): a morphism
between two algebraic spaces étale over a third is étale.

## Main results

* `AlgebraicGeometry.Space.isEtaleULift_of_comp`: Stacks 03FV for algebraic spaces with values
  in the larger universe `Type (u + 1)`.
* `AlgebraicGeometry.Space.isEtaleULift_of_isPullback`: the base change of an étale morphism of
  algebraic spaces with values in `Type (u + 1)` is étale.
* `AlgebraicGeometry.FormalSpace.isRepresentableEtale_of_comp`: the cancellation statement above.

## Implementation notes

The two statements about algebraic spaces with values in `Type (u + 1)` are transported from the
corresponding statements in the value universe of the site,
`AlgebraicGeometry.Space.isEtale_of_isEtale_over` and
`AlgebraicGeometry.Space.isEtale_of_isPullback`, along the universe lift: an algebraic space with
values in `Type (u + 1)` is the universe lift of one with values in `Type u`
(`AlgebraicGeometry.Space.exists_comp_uliftFunctor_iso_of_isAlgebraicSpaceULift`), and étaleness is
unchanged by the lift (`AlgebraicGeometry.Space.isEtaleULift_whiskerRight_iff`).

For the cancellation, representability of `k` is Stacks 0AQ0 for the affine formal algebraic
space `W`. For étaleness, let `ξ : T ⟶ W` be a scheme-valued point. The base change of `k`
along `ξ` is the base change of the morphism `T ×_X U ⟶ T ×_X W` induced by `k` along the
section `T ⟶ T ×_X W` given by `ξ`; that morphism goes between algebraic spaces étale over `T`,
so it is étale by Stacks 03FV, and étaleness is stable under base change.

## References

* [Stacks Project, Tag 03FV](https://stacks.math.columbia.edu/tag/03FV)
* [Stacks Project, Tag 05W3](https://stacks.math.columbia.edu/tag/05W3)
* [Stacks Project, Tag 0AQ0](https://stacks.math.columbia.edu/tag/0AQ0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Étaleness of a morphism between algebraic spaces with values in `Type (u + 1)` is the
étaleness of any morphism of algebraic spaces in the value universe of the site whose universe
lift is the given morphism conjugated by isomorphisms. -/
private theorem isEtaleULift_iff_of_whiskerRight_eq
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (eX : X' ⋙ uliftFunctor.{u + 1} ≅ X) (eY : Y' ⋙ uliftFunctor.{u + 1} ≅ Y)
    (k : X ⟶ Y) (k' : X' ⟶ Y')
    (hk : Functor.whiskerRight k' uliftFunctor.{u + 1} = eX.hom ≫ k ≫ eY.inv) :
    IsEtaleULift.{u + 1} B S hS k ↔ IsEtale B S hS k' := by
  rw [← isEtaleULift_whiskerRight_iff B S hS k', hk, isEtaleULift_isIso_comp_iff,
    isEtaleULift_comp_isIso_iff]

/-- **Stacks 03FV** for algebraic spaces with values in `Type (u + 1)`: if `f ≫ h` and `h` are
étale morphisms of algebraic spaces, then so is `f`. -/
theorem isEtaleULift_of_comp {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (hF : IsAlgebraicSpaceULift.{u + 1} B S hS F) (hG : IsAlgebraicSpaceULift.{u + 1} B S hS G)
    (hH : IsAlgebraicSpaceULift.{u + 1} B S hS H) (f : F ⟶ G) (h : G ⟶ H)
    (hfh : IsEtaleULift.{u + 1} B S hS (f ≫ h)) (hh : IsEtaleULift.{u + 1} B S hS h) :
    IsEtaleULift.{u + 1} B S hS f := by
  obtain ⟨F', hF', ⟨eF⟩⟩ := exists_comp_uliftFunctor_iso_of_isAlgebraicSpaceULift B S hS hF
  obtain ⟨G', hG', ⟨eG⟩⟩ := exists_comp_uliftFunctor_iso_of_isAlgebraicSpaceULift B S hS hG
  obtain ⟨H', hH', ⟨eH⟩⟩ := exists_comp_uliftFunctor_iso_of_isAlgebraicSpaceULift B S hS hH
  obtain ⟨f', hf'⟩ := exists_whiskerRight_eq B S hS (eF.hom ≫ f ≫ eG.inv)
  obtain ⟨h', hh'⟩ := exists_whiskerRight_eq B S hS (eG.hom ≫ h ≫ eH.inv)
  have hfh' : Functor.whiskerRight (f' ≫ h') uliftFunctor.{u + 1} =
      eF.hom ≫ (f ≫ h) ≫ eH.inv := by
    rw [Functor.whiskerRight_comp, hf', hh']
    simp
  rw [isEtaleULift_iff_of_whiskerRight_eq B S hS eF eG f f' hf']
  rw [isEtaleULift_iff_of_whiskerRight_eq B S hS eF eH (f ≫ h) (f' ≫ h') hfh'] at hfh
  rw [isEtaleULift_iff_of_whiskerRight_eq B S hS eG eH h h' hh'] at hh
  exact isEtale_of_isEtale_over B S hS hF' hG' hH' f' (f' ≫ h') h' hfh hh rfl

/-- The base change of an étale morphism of algebraic spaces with values in `Type (u + 1)` along
a morphism of algebraic spaces is étale. -/
theorem isEtaleULift_of_isPullback {P X Z Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (hP : IsAlgebraicSpaceULift.{u + 1} B S hS P) (hX : IsAlgebraicSpaceULift.{u + 1} B S hS X)
    (hZ : IsAlgebraicSpaceULift.{u + 1} B S hS Z) (hY : IsAlgebraicSpaceULift.{u + 1} B S hS Y)
    {p : P ⟶ X} {f' : P ⟶ Z} {f : X ⟶ Y} {g : Z ⟶ Y} (sq : IsPullback p f' f g)
    (hf : IsEtaleULift.{u + 1} B S hS f) : IsEtaleULift.{u + 1} B S hS f' := by
  obtain ⟨P', hP', ⟨eP⟩⟩ := exists_comp_uliftFunctor_iso_of_isAlgebraicSpaceULift B S hS hP
  obtain ⟨X', hX', ⟨eX⟩⟩ := exists_comp_uliftFunctor_iso_of_isAlgebraicSpaceULift B S hS hX
  obtain ⟨Z', hZ', ⟨eZ⟩⟩ := exists_comp_uliftFunctor_iso_of_isAlgebraicSpaceULift B S hS hZ
  obtain ⟨Y', hY', ⟨eY⟩⟩ := exists_comp_uliftFunctor_iso_of_isAlgebraicSpaceULift B S hS hY
  obtain ⟨p', hp'⟩ := exists_whiskerRight_eq B S hS (eP.hom ≫ p ≫ eX.inv)
  obtain ⟨f'', hf''⟩ := exists_whiskerRight_eq B S hS (eP.hom ≫ f' ≫ eZ.inv)
  obtain ⟨ff, hff⟩ := exists_whiskerRight_eq B S hS (eX.hom ≫ f ≫ eY.inv)
  obtain ⟨g', hg'⟩ := exists_whiskerRight_eq B S hS (eZ.hom ≫ g ≫ eY.inv)
  rw [isEtaleULift_iff_of_whiskerRight_eq B S hS eX eY f ff hff] at hf
  rw [isEtaleULift_iff_of_whiskerRight_eq B S hS eP eZ f' f'' hf'']
  let L := (Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u) (Type (u + 1))).obj
    uliftFunctor.{u + 1}
  have hcomm : p' ≫ ff = f'' ≫ g' := by
    apply L.map_injective
    change Functor.whiskerRight (p' ≫ ff) uliftFunctor.{u + 1} =
      Functor.whiskerRight (f'' ≫ g') uliftFunctor.{u + 1}
    rw [Functor.whiskerRight_comp, Functor.whiskerRight_comp, hp', hff, hf'', hg']
    simp [sq.w_assoc]
  have hL : IsPullback (L.map p') (L.map f'') (L.map ff) (L.map g') :=
    IsPullback.of_iso sq eP.symm eX.symm eZ.symm eY.symm
      (by simp [L, hp']) (by simp [L, hf'']) (by simp [L, hff]) (by simp [L, hg'])
  have hsp : IsPullback
      (ObjectProperty.homMk p' : (⟨P', hP'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X', hX'⟩)
      (ObjectProperty.homMk f'' : (⟨P', hP'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Z', hZ'⟩)
      (ObjectProperty.homMk ff : (⟨X', hX'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y', hY'⟩)
      (ObjectProperty.homMk g' : (⟨Z', hZ'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y', hY'⟩) :=
    IsPullback.of_map (ObjectProperty.ι _) (by ext1; exact hcomm) (hL.of_map L hcomm)
  exact isEtale_of_isPullback B S hS _ _ _ _ hsp hf

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Cancellation of an étale factor**, the formal-space form of Stacks 05W3. Let
`k : U ⟶ W` and `q : W ⟶ X` be morphisms of fppf sheaves over `S` with `W` an affine formal
algebraic space. If `q` and `k ≫ q` are representable by algebraic spaces and étale, then so
is `k`.

Representability is Stacks 0AQ0 for the affine formal algebraic space `W`. For a scheme-valued
point `ξ : T ⟶ W`, the base change of `k` along `ξ` is the base change, along the section
`T ⟶ T ×_X W` given by `ξ`, of the morphism `T ×_X U ⟶ T ×_X W` induced by `k`; that morphism
goes between algebraic spaces étale over `T`, so it is étale by Stacks 03FV. -/
theorem isRepresentableEtale_of_comp {U W X : FppfSheaf B S hS} (k : U ⟶ W) (q : W ⟶ X)
    (hW : IsAffineFormalAlgebraicSpace B S hS W) (hq : IsRepresentableEtale B S hS q)
    (hkq : IsRepresentableEtale B S hS (k ≫ q)) : IsRepresentableEtale B S hS k := by
  obtain ⟨hkqrep, hkqet⟩ := hkq
  obtain ⟨hqrep, hqet⟩ := hq
  have hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS k.hom :=
    isRepresentableByAlgebraicSpacesULift_of_comp_of_isAffineFormal B S hS k q hW hkqrep
  refine ⟨hrep, fun T ξ => ?_⟩
  dsimp only [ObjectProperty.homMk]
  let ξq := ξ ≫ q.hom
  let a := k.hom ≫ q.hom
  have hP1 : Space.IsAlgebraicSpaceULift.{u + 1} B S hS (pullback ξq a) := hkqrep T ξq
  have hP2 : Space.IsAlgebraicSpaceULift.{u + 1} B S hS (pullback ξq q.hom) := hqrep T ξq
  have hT := Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS T
  let m : pullback ξq a ⟶ pullback ξq q.hom :=
    pullback.lift (pullback.fst ξq a) (pullback.snd ξq a ≫ k.hom)
      (by rw [pullback.condition]; simp [a])
  have hm1 : m ≫ pullback.fst ξq q.hom = pullback.fst ξq a := pullback.lift_fst _ _ _
  have hm2 : m ≫ pullback.snd ξq q.hom = pullback.snd ξq a ≫ k.hom := pullback.lift_snd _ _ _
  have hmet : Space.IsEtaleULift.{u + 1} B S hS m :=
    Space.isEtaleULift_of_comp B S hS hP1 hP2 hT m (pullback.fst ξq q.hom)
      (by rw [hm1]; exact hkqet T ξq) (hqet T ξq)
  let σ : (uliftYoneda.{u + 1}).obj T ⟶ pullback ξq q.hom :=
    pullback.lift (𝟙 _) ξ (by simp [ξq])
  let j : pullback ξ k.hom ⟶ pullback ξq a :=
    pullback.lift (pullback.fst ξ k.hom) (pullback.snd ξ k.hom)
      (by simp only [ξq, a, ← Category.assoc, pullback.condition])
  -- the square `T ×_X U → U, T ×_X U → T ×_X W, U → W, T ×_X W → W` is cartesian
  have hR : IsPullback (pullback.snd ξq a) m k.hom (pullback.snd ξq q.hom) := by
    refine IsPullback.of_bot ?_ hm2.symm (IsPullback.of_hasPullback ξq q.hom).flip
    rw [hm1]
    exact (IsPullback.of_hasPullback ξq a).flip
  have hL : IsPullback j (pullback.fst ξ k.hom) m σ := by
    refine IsPullback.of_right ?_ ?_ hR
    · rw [show j ≫ pullback.snd ξq a = pullback.snd ξ k.hom from pullback.lift_snd _ _ _,
        show σ ≫ pullback.snd ξq q.hom = ξ from pullback.lift_snd _ _ _]
      exact (IsPullback.of_hasPullback ξ k.hom).flip
    · apply pullback.hom_ext
      · rw [Category.assoc, hm1, Category.assoc]
        change pullback.lift _ _ _ ≫ pullback.fst ξq a =
          pullback.fst ξ k.hom ≫ pullback.lift _ _ _ ≫ pullback.fst ξq q.hom
        rw [pullback.lift_fst, pullback.lift_fst, Category.comp_id]
      · rw [Category.assoc, hm2, Category.assoc]
        change (pullback.lift _ _ _ ≫ pullback.snd ξq a) ≫ k.hom =
          pullback.fst ξ k.hom ≫ pullback.lift _ _ _ ≫ pullback.snd ξq q.hom
        rw [pullback.lift_snd, pullback.lift_snd, pullback.condition]
  exact Space.isEtaleULift_of_isPullback B S hS (hrep T ξ) hP1 hT hP2 hL hmet

end AlgebraicGeometry.FormalSpace

end
