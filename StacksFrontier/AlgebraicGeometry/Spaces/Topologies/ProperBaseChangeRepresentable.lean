module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BoundedSetBaseChangeTransfer
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.ProperBaseChangeReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.RepresentableBaseChangeComparison

/-!
# Base change for a proper morphism of representable algebraic spaces

Let
```
X' --i--> X
|f'       |f
Y' --g--> Y
```
be a cartesian square of algebraic spaces over `S` with `f` proper and `X`, `Y`, `Y'`
representable. This file shows that the base-change map `g⁻¹ f_* ⟶ f'_* i⁻¹` of sheaves of sets is
invertible, granted proper base change for sheaves of sets on the small étale sites of schemes,
Stacks 0A3U (taken as the hypothesis `h0A3U`). Granted Stacks 0A3U alone, it deduces the
base-change theorem Stacks 0DG0 for sheaves of sets on algebraic spaces.

## Main results

All names below are in the namespace `AlgebraicGeometry.Space`.

* `isIso_spacesToposBaseChangeSquare_of_iso`: invertibility of the base-change map is invariant
  under an isomorphism of cartesian squares.
* `isIso_spacesToposBaseChangeSquare_yonedaSpaceHom_of_properBaseChange`: the case of a cartesian
  square of the big fppf site with proper right edge.
* `isIso_spacesToposBaseChangeSquare_of_isRepresentable_of_properBaseChange`: the case of
  representable `X`, `Y`, `Y'`.
* `properSurjectivePrestackOverSchemes_of_properBaseChange`: full faithfulness of descent along
  proper surjections of schemes, granted Stacks 0A3U.
* `isIso_spacesToposBaseChangeSquare_of_isProper_of_properBaseChange`: Stacks 0DG0, granted
  Stacks 0A3U.

## References

* [Stacks Project, Tag 0DG0](https://stacks.math.columbia.edu/tag/0DG0)
* [Stacks Project, Tag 0A3U](https://stacks.math.columbia.edu/tag/0A3U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The underlying morphism of presheaves of an isomorphism of algebraic spaces is invertible. -/
private theorem isIso_hom_hom_of_iso {F G : AlgebraicSpaces B S hS} (e : F ≅ G) :
    IsIso e.hom.hom :=
  inferInstanceAs (IsIso ((ObjectProperty.ι _).map e.hom))

/-- An isomorphism of algebraic spaces over `S` is étale. -/
theorem isEtale_hom_of_iso {F G : AlgebraicSpaces B S hS} (e : F ≅ G) : IsEtale B S hS e.hom.hom :=
  have := isIso_hom_hom_of_iso B S hS e
  isEtale_of_isIso B S hS e.hom.hom

/-- **Invertibility of the base-change map is invariant under isomorphisms of cartesian
squares.** If two cartesian squares are isomorphic through isomorphisms of their four corners
compatible with their four edges, and the base-change map of the first is invertible, so is that
of the second. -/
theorem isIso_spacesToposBaseChangeSquare_of_iso {X Y X' Y' X₁ Y₁ X₁' Y₁' : AlgebraicSpaces B S hS}
    {i : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback i f' f g)
    {i₁ : X₁' ⟶ X₁} {f₁' : X₁' ⟶ Y₁'} {f₁ : X₁ ⟶ Y₁} {g₁ : Y₁' ⟶ Y₁}
    (sq₁ : IsPullback i₁ f₁' f₁ g₁) (eX : X₁ ≅ X) (eY : Y₁ ≅ Y) (eX' : X₁' ≅ X')
    (eY' : Y₁' ≅ Y') (hi : i₁ ≫ eX.hom = eX'.hom ≫ i) (hf' : f₁' ≫ eY'.hom = eX'.hom ≫ f')
    (hf : f₁ ≫ eY.hom = eX.hom ≫ f) (hg : g₁ ≫ eY.hom = eY'.hom ≫ g)
    (h₁ : IsIso (spacesToposBaseChangeSquare B S hS i₁ f₁' f₁ g₁ sq₁)) :
    IsIso (spacesToposBaseChangeSquare B S hS i f' f g sq) := by
  have sqR : IsPullback eX.hom f₁ f eY.hom := IsPullback.of_horiz_isIso ⟨hf.symm⟩
  have hR := isIso_spacesToposBaseChangeSquare B S hS eX.hom f₁ f eY.hom sqR
    (isEtale_hom_of_iso B S hS eY)
  have hout₁ := isIso_spacesToposBaseChangeSquare_paste_horiz B S hS eX.hom f₁ f eY.hom i₁ f₁' g₁
    sqR sq₁ hR h₁
  have sqO : IsPullback (eX'.hom ≫ i) f₁' f (eY'.hom ≫ g) := by
    rw [← hi, ← hg]
    exact sq₁.paste_horiz sqR
  have hout₂ := (isIso_spacesToposBaseChangeSquare_congr B S hS hi rfl hg _ sqO).mp hout₁
  have sqL : IsPullback eX'.inv f' f₁' eY'.inv := IsPullback.of_horiz_isIso
    ⟨by rw [Iso.inv_comp_eq, ← Category.assoc, ← hf', Category.assoc, Iso.hom_inv_id,
      Category.comp_id]⟩
  have hL := isIso_spacesToposBaseChangeSquare B S hS eX'.inv f' f₁' eY'.inv sqL
    (isEtale_hom_of_iso B S hS eY'.symm)
  have hout₃ := isIso_spacesToposBaseChangeSquare_paste_horiz B S hS (eX'.hom ≫ i) f₁' f
    (eY'.hom ≫ g) eX'.inv f' eY'.inv sqO sqL hout₂ hL
  exact (isIso_spacesToposBaseChangeSquare_congr B S hS (Iso.inv_hom_id_assoc eX' i) rfl
    (Iso.inv_hom_id_assoc eY' g) _ sq).mp hout₃

variable {B S hS}

/-- **Base change for a cartesian square of the big fppf site with proper right edge**, granted
Stacks 0A3U. For a cartesian square `n' ≫ m = m' ≫ n` of the big fppf site of `S` whose image
under the Yoneda embedding is cartesian and whose right edge has proper underlying morphism of
schemes, the base-change map of the square of represented algebraic spaces is invertible. -/
theorem isIso_spacesToposBaseChangeSquare_yonedaSpaceHom_of_properBaseChange
    (h0A3U : ∀ {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (sq : IsPullback g' f' f g), _root_.AlgebraicGeometry.IsProper f →
        IsIso (Stacks.EtaleCohomology.smallEtaleSetBaseChange.{u, 0} g' f' f g sq.w))
    {V W V' W' : BigFppfOver B S hS} (m : W ⟶ V) (n : V' ⟶ V) (n' : W' ⟶ W) (m' : W' ⟶ V')
    (hsite : IsPullback n' m' m n)
    (hm : _root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map m))
    (sq : IsPullback (yonedaSpaceHom n') (yonedaSpaceHom m') (yonedaSpaceHom m)
      (yonedaSpaceHom n)) :
    IsIso (spacesToposBaseChangeSquare B S hS (yonedaSpaceHom n') (yonedaSpaceHom m')
      (yonedaSpaceHom m) (yonedaSpaceHom n) sq) := by
  have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    comp_preservesLimitsOfShape _ _
  have hsch := hsite.map (BigFppfOver.toScheme B S hS)
  refine (isIso_spacesToposBaseChangeSquare_iff m n n' m' hsite.w sq).mpr ?_
  exact SmallEtale.isIso_smallEtaleBaseChangeNatTrans_of_isIso_smallEtaleSetBaseChange
    (associatedBigEtaleSite B) m.left n.left n'.left m'.left _ (h0A3U _ _ _ _ hsch hm)

/-- **Base change for a proper morphism of representable algebraic spaces**, granted Stacks 0A3U.
Let `(i, f', f, g)` be a cartesian square of algebraic spaces over `S` with `f` proper and `X`,
`Y`, `Y'` representable. Then the base-change map `g⁻¹ f_* ⟶ f'_* i⁻¹` of sheaves of sets is
invertible. -/
theorem isIso_spacesToposBaseChangeSquare_of_isRepresentable_of_properBaseChange
    (h0A3U : ∀ {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (sq : IsPullback g' f' f g), _root_.AlgebraicGeometry.IsProper f →
        IsIso (Stacks.EtaleCohomology.smallEtaleSetBaseChange.{u, 0} g' f' f g sq.w))
    ⦃X Y X' Y' : AlgebraicSpaces B S hS⦄ (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
    (g : Y' ⟶ Y) (sq : IsPullback i f' f g) (hX : X.1.IsRepresentable)
    (hY : Y.1.IsRepresentable) (hY' : Y'.1.IsRepresentable) (hf : IsProper B S hS f.hom) :
    IsIso (spacesToposBaseChangeSquare B S hS i f' f g sq) := by
  have hX' : X'.1.IsRepresentable := isRepresentable_of_iso B S hS
    (isRepresentable_pullback_algebraicSpaces B S hS hX hY' f g)
    ((ObjectProperty.ι _).mapIso sq.isoPullback.symm)
  obtain ⟨W, ⟨rX⟩⟩ := hX.has_representation
  obtain ⟨V, ⟨rY⟩⟩ := hY.has_representation
  obtain ⟨V', ⟨rY'⟩⟩ := hY'.has_representation
  obtain ⟨W', ⟨rX'⟩⟩ := hX'.has_representation
  let eX : yonedaSpace B S hS W ≅ X := (ObjectProperty.fullyFaithfulι _).preimageIso rX.toIso
  let eY : yonedaSpace B S hS V ≅ Y := (ObjectProperty.fullyFaithfulι _).preimageIso rY.toIso
  let eY' : yonedaSpace B S hS V' ≅ Y' := (ObjectProperty.fullyFaithfulι _).preimageIso rY'.toIso
  let eX' : yonedaSpace B S hS W' ≅ X' := (ObjectProperty.fullyFaithfulι _).preimageIso rX'.toIso
  have pre : ∀ {T T' : BigFppfOver B S hS} (k : yonedaSpace B S hS T ⟶ yonedaSpace B S hS T'),
      yonedaSpaceHom (Yoneda.fullyFaithful.preimage k.hom) = k := fun k ↦
    ObjectProperty.hom_ext _ (Yoneda.fullyFaithful.map_preimage k.hom)
  let m : W ⟶ V := Yoneda.fullyFaithful.preimage (eX.hom ≫ f ≫ eY.inv).hom
  let n : V' ⟶ V := Yoneda.fullyFaithful.preimage (eY'.hom ≫ g ≫ eY.inv).hom
  let n' : W' ⟶ W := Yoneda.fullyFaithful.preimage (eX'.hom ≫ i ≫ eX.inv).hom
  let m' : W' ⟶ V' := Yoneda.fullyFaithful.preimage (eX'.hom ≫ f' ≫ eY'.inv).hom
  have hm : yonedaSpaceHom m ≫ eY.hom = eX.hom ≫ f := by rw [pre]; simp
  have hn : yonedaSpaceHom n ≫ eY.hom = eY'.hom ≫ g := by rw [pre]; simp
  have hn' : yonedaSpaceHom n' ≫ eX.hom = eX'.hom ≫ i := by rw [pre]; simp
  have hm' : yonedaSpaceHom m' ≫ eY'.hom = eX'.hom ≫ f' := by rw [pre]; simp
  have sqrep : IsPullback (yonedaSpaceHom n') (yonedaSpaceHom m') (yonedaSpaceHom m)
      (yonedaSpaceHom n) :=
    sq.of_iso eX'.symm eX.symm eY'.symm eY.symm
      (by simp [Iso.eq_inv_comp, ← reassoc_of% hn'])
      (by simp [Iso.eq_inv_comp, ← reassoc_of% hm'])
      (by simp [Iso.eq_inv_comp, ← reassoc_of% hm])
      (by simp [Iso.eq_inv_comp, ← reassoc_of% hn])
  have hcomm : n' ≫ m = m' ≫ n := Yoneda.fullyFaithful.map_injective
    (congrArg (fun k ↦ k.hom) sqrep.w)
  have hsite : IsPullback n' m' m n :=
    IsPullback.of_map yoneda hcomm (AlgebraicSpaces.isPullback_hom B S hS sqrep)
  have hrel : yoneda.relativelyRepresentable f.hom := by
    have h₀ : yoneda.relativelyRepresentable (eX.hom.hom ≫ f.hom) :=
      Y.2.diagonal_representable.of_diag _
    have hfe : f.hom = eX.inv.hom ≫ (eX.hom.hom ≫ f.hom) := by
      rw [← Category.assoc, ← ObjectProperty.FullSubcategory.comp_hom, Iso.inv_hom_id]
      rfl
    have := isIso_hom_hom_of_iso B S hS eX.symm
    rw [hfe]
    exact MorphismProperty.RespectsIso.precomp _ eX.inv.hom _ h₀
  have hpb : IsPullback eX.hom.hom (yoneda.map m) f.hom eY.hom.hom := by
    have := isIso_hom_hom_of_iso B S hS eX
    have := isIso_hom_hom_of_iso B S hS eY
    exact IsPullback.of_horiz_isIso ⟨congrArg (fun k ↦ k.hom) hm.symm⟩
  have hmp : _root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map m) :=
    ((presheaf_isProper_iff B S hS f.hom X.2 Y.2 hrel).mp hf).property eY.hom.hom eX.hom.hom m hpb
  exact isIso_spacesToposBaseChangeSquare_of_iso B S hS sq sqrep eX eY eX' eY' hn' hm' hm hn
    (isIso_spacesToposBaseChangeSquare_yonedaSpaceHom_of_properBaseChange h0A3U m n n' m' hsite hmp
      sqrep)

variable (B S hS) in
/-- **Descent along proper surjections of schemes is fully faithful, granted Stacks 0A3U.** For
every morphism `m : W ⟶ V` of the big fppf site of `S` whose underlying morphism of schemes is
proper and surjective, the pseudofunctor of spaces-étale inverse images is a prestack for the sieve
generated by the represented morphism of algebraic spaces. -/
theorem properSurjectivePrestackOverSchemes_of_properBaseChange
    (h0A3U : ∀ {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (sq : IsPullback g' f' f g), _root_.AlgebraicGeometry.IsProper f →
        IsIso (Stacks.EtaleCohomology.smallEtaleSetBaseChange.{u, 0} g' f' f g sq.w)) :
    ProperSurjectivePrestackOverSchemes B S hS := by
  refine properSurjectivePrestackOverSchemes_of_fullyFaithful B S hS fun E _ _ h hsurj hprop ↦ ?_
  have :=
    smallEtaleSheafInverseImageDescentFunctor_isEquivalence_of_surjective_proper_of_properBaseChange
      E h h0A3U
  exact ⟨.ofFullyFaithful _⟩

variable (B S hS) in
/-- **Base change for a proper morphism of algebraic spaces, granted Stacks 0A3U** (the set-level
statement of Stacks 0DG0, with Stacks 0A3U as its single input). Let
```
Y' --g'--> Y
|f'        |f
v          v
X' --g---> X
```
be a cartesian square of algebraic spaces over `S` with `f` proper. Then the base-change map
`g⁻¹ f_* ⟶ f'_* (g')⁻¹` of spaces-étale sheaves of sets is invertible. -/
theorem isIso_spacesToposBaseChangeSquare_of_isProper_of_properBaseChange
    (h0A3U : ∀ {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (sq : IsPullback g' f' f g), _root_.AlgebraicGeometry.IsProper f →
        IsIso (Stacks.EtaleCohomology.smallEtaleSetBaseChange.{u, 0} g' f' f g sq.w))
    ⦃X Y X' Y' : AlgebraicSpaces B S hS⦄ (f : Y ⟶ X) (hf : IsProper B S hS f.hom)
    (g : X' ⟶ X) (g' : Y' ⟶ Y) (f' : Y' ⟶ X') (sq : IsPullback g' f' f g) :
    IsIso (spacesToposBaseChangeSquare B S hS g' f' f g sq) :=
  isIso_spacesToposBaseChangeSquare_of_isProper B S hS
    (properSurjectivePrestackOverSchemes_of_properBaseChange B S hS h0A3U)
    (isIso_spacesToposBaseChangeSquare_of_isRepresentable_of_properBaseChange h0A3U) g' f' f g sq hf

end AlgebraicGeometry.Space

end
