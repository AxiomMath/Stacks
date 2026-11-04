module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.RegularImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.EtaleAffineSpace
public import
  StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.SmoothTargetPermanence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quasi-regularity of an immersion into a scheme smooth over the base

Let `Y ⟶ X ⟶ S` with `X ⟶ S` smooth and both `Y ⟶ X` and `Y ⟶ S` immersions. If `Y ⟶ X` is a
quasi-regular immersion, then so is `Y ⟶ S`.

## Main results

* `isQuasiRegularImmersion_comp_isOpenImmersion`: a quasi-regular immersion followed by an open
  immersion is a quasi-regular immersion.
* `isQuasiRegularImmersion_comp_of_etale`: a quasi-regular immersion followed by an étale
  morphism is a quasi-regular immersion as soon as the composite is an immersion.
* `isQuasiRegularImmersion_comp_of_smooth`: a quasi-regular immersion followed by a smooth
  morphism is a quasi-regular immersion as soon as the composite is an immersion.

## References

* [Stacks Project, Lemma 31.23.12 (Tag 0693)](https://stacks.math.columbia.edu/tag/0693)
* [Stacks Project, Lemma 29.36.20 (Tag 054L)](https://stacks.math.columbia.edu/tag/054L)
* [Stacks Project, Lemma 35.26.1 (Tag 0694)](https://stacks.math.columbia.edu/tag/0694)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace Stacks.AlgebraicGeometry.RegularIdealSheaf

/-- The property of being a quasi-regular immersion, as a property of morphisms of schemes. -/
@[ega "IV 16.9.2"]
private abbrev quasiRegularImmersionProperty : MorphismProperty Scheme.{u} :=
  fun _ _ f => ∃ hf : IsImmersion f, @IsQuasiRegularImmersion _ _ f hf

private instance : MorphismProperty.IsLocalAtTarget quasiRegularImmersionProperty.{u}
    Scheme.etalePrecoverage.{u} :=
  _root_.AlgebraicGeometry.isLocalAtTarget_quasiRegularImmersion_etale.{u}

/-- Postcomposing a quasi-regular immersion with an isomorphism gives a quasi-regular
immersion. -/
private theorem isQuasiRegularImmersion_comp_iso_hom {A B C : Scheme.{u}} (f : A ⟶ B)
    [IsImmersion f] (e : B ≅ C) (hf : IsQuasiRegularImmersion f) :
    IsQuasiRegularImmersion (f ≫ e.hom) :=
  Stacks.AlgebraicGeometry.isQuasiRegularImmersion_of_isPullback_of_flat
    (IsPullback.of_horiz_isIso (f := f) (g := e.inv)
      ⟨by rw [Category.id_comp, Category.assoc, e.hom_inv_id, Category.comp_id]⟩).flip hf

/-- An immersion with empty source is a quasi-regular immersion. -/
private theorem isQuasiRegularImmersion_of_isEmpty {Y X : Scheme.{u}} (i : Y ⟶ X)
    [IsImmersion i] [IsEmpty Y] : IsQuasiRegularImmersion i := by
  refine (isQuasiRegularImmersion_iff_of_open i ⊥
    (IsOpenImmersion.lift (⊥ : X.Opens).ι i (by rintro - ⟨y, rfl⟩; exact isEmptyElim y))
    (IsOpenImmersion.lift_fac _ _ _)).mpr fun x => ?_
  exact False.elim x.2

/-- Composing a quasi-regular immersion with an open immersion gives a quasi-regular
immersion. -/
theorem isQuasiRegularImmersion_comp_isOpenImmersion {Y X S : Scheme.{u}} (i : Y ⟶ X)
    (f : X ⟶ S) [IsImmersion i] [IsOpenImmersion f] (hi : IsQuasiRegularImmersion i) :
    IsQuasiRegularImmersion (i ≫ f) := by
  have hcl : IsQuasiRegularImmersion i.liftCoborder :=
    isQuasiRegularImmersion_of_comp_of_smooth i.liftCoborder i.coborderRange.ι
      (by simpa only [Scheme.Hom.liftCoborder_ι] using hi)
  set e : i.coborderRange.toScheme ⟶ S := i.coborderRange.ι ≫ f with he
  have hki : (i.liftCoborder ≫ e.isoOpensRange.hom) ≫ e.opensRange.ι = i ≫ f := by
    rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, he, ← Category.assoc,
      Scheme.Hom.liftCoborder_ι]
  exact (isQuasiRegularImmersion_iff_of_open (i ≫ f) e.opensRange
      (i.liftCoborder ≫ e.isoOpensRange.hom) hki).mpr
    (isQuasiRegularIdealSheaf_definingIdealOfHom _
      (isQuasiRegularImmersion_comp_iso_hom i.liftCoborder e.isoOpensRange hcl))

/-- If `g ≫ u = i` for an open immersion `u` and `i` is quasi-regular, then so is `g`. -/
private theorem isImmersion_and_isQuasiRegularImmersion_of_comp_isOpenImmersion
    {Y U X : Scheme.{u}} (g : Y ⟶ U) (u : U ⟶ X) (i : Y ⟶ X) [IsOpenImmersion u] [IsImmersion i]
    (h : g ≫ u = i) (hi : IsQuasiRegularImmersion i) :
    ∃ _ : IsImmersion g, IsQuasiRegularImmersion g := by
  subst h
  have : IsImmersion (g ≫ u) := ‹_›
  have := IsImmersion.of_comp g u
  exact ⟨this, isQuasiRegularImmersion_of_comp_of_smooth g u hi⟩

/-- A morphism is a quasi-regular immersion if its lift to the coborder is. -/
private theorem isQuasiRegularImmersion_of_liftCoborder {Y S : Scheme.{u}} (j : Y ⟶ S)
    [IsImmersion j] (h : IsQuasiRegularImmersion j.liftCoborder) : IsQuasiRegularImmersion j := by
  simpa only [Scheme.Hom.liftCoborder_ι] using
    isQuasiRegularImmersion_comp_isOpenImmersion j.liftCoborder j.coborderRange.ι h

/-- A quasi-regular immersion `i` followed by `f` factors through the preimage of the coborder
of `i ≫ f` by a quasi-regular immersion `g` lifting the coborder map of `i ≫ f`. -/
private theorem exists_isQuasiRegularImmersion_comp_morphismRestrict_eq_liftCoborder
    {Y X S : Scheme.{u}} (i : Y ⟶ X) (f : X ⟶ S) [IsImmersion i] [IsImmersion (i ≫ f)]
    (hi : IsQuasiRegularImmersion i) :
    ∃ (g : Y ⟶ (f ⁻¹ᵁ (i ≫ f).coborderRange).toScheme) (_ : IsImmersion g),
      IsQuasiRegularImmersion g ∧ g ≫ (f ∣_ (i ≫ f).coborderRange) = (i ≫ f).liftCoborder := by
  have hUr : Set.range i ⊆ Set.range (f ⁻¹ᵁ (i ≫ f).coborderRange).ι := by
    rw [Scheme.Opens.range_ι]
    rintro - ⟨y, rfl⟩
    exact subset_coborder ⟨y, rfl⟩
  have hgi := IsOpenImmersion.lift_fac (f ⁻¹ᵁ (i ≫ f).coborderRange).ι i hUr
  obtain ⟨hgim, hgq⟩ := isImmersion_and_isQuasiRegularImmersion_of_comp_isOpenImmersion _ _ i hgi hi
  refine ⟨_, hgim, hgq, (cancel_mono (i ≫ f).coborderRange.ι).mp ?_⟩
  rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hgi, Scheme.Hom.liftCoborder_ι]

/-- **An immersion with étale ambient closed composite is a base change.** If `e : X ⟶ S` is
étale and `i ≫ e` is a closed immersion, then `i` factors through an open `U` of `X` by a
morphism exhibiting `Y` as the fibre product of `i ≫ e` and `U ⟶ S`. -/
private theorem exists_isPullback_of_etale_of_isClosedImmersion {Y X S : Scheme.{u}} (i : Y ⟶ X)
    (e : X ⟶ S) [Etale e] [IsClosedImmersion (i ≫ e)] :
    ∃ (U : X.Opens) (g : Y ⟶ U.toScheme),
      g ≫ U.ι = i ∧ IsPullback (𝟙 Y) g (i ≫ e) (U.ι ≫ e) := by
  set j : Y ⟶ S := i ≫ e with hj
  set d : Y ⟶ pullback j e := pullback.lift (𝟙 Y) i (by rw [Category.id_comp, hj]) with hd
  have hdi : IsOpenImmersion d :=
    MorphismProperty.of_isPullback (pullback_lift_diagonal_isPullback i e)
      (inferInstance : IsOpenImmersion (pullback.diagonal e))
  set p : pullback j e ⟶ X := pullback.snd j e with hp
  have hpc : IsClosedImmersion p := inferInstance
  set U : X.Opens := ⟨(p '' (Set.range d)ᶜ)ᶜ,
    (p.isClosedMap _ hdi.base_open.isOpen_range.isClosed_compl).isOpen_compl⟩ with hU
  have hUr : Set.range i ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro - ⟨y, rfl⟩ ⟨z, hz, hzy⟩
    refine hz ⟨y, p.isEmbedding.injective ?_⟩
    have hdy : p (d y) = i y := by
      rw [← Scheme.Hom.comp_apply, hd, hp, pullback.lift_snd]
    exact hdy.trans hzy.symm
  set g : Y ⟶ U.toScheme := IsOpenImmersion.lift U.ι i hUr with hg
  have hgi : g ≫ U.ι = i := IsOpenImmersion.lift_fac _ _ _
  have heq : p ⁻¹ᵁ U.ι.opensRange = d.opensRange := by
    ext z
    show p z ∈ Set.range U.ι ↔ z ∈ Set.range d
    rw [Scheme.Opens.range_ι]
    show p z ∉ p '' (Set.range d)ᶜ ↔ z ∈ Set.range d
    refine ⟨fun hz => by_contra fun hzd => hz ⟨z, hzd, rfl⟩, ?_⟩
    rintro hz ⟨w, hw, hwz⟩
    exact hw (p.isEmbedding.injective hwz ▸ hz)
  have H := IsOpenImmersion.isPullback g d U.ι p
    (by rw [hgi, hd, hp, pullback.lift_snd]) heq
  have hdfst : d ≫ pullback.fst j e = 𝟙 Y := by rw [hd, pullback.lift_fst]
  refine ⟨U, g, hgi, ?_⟩
  rw [← hdfst]
  simpa only [hj, hp] using H.flip.paste_horiz (IsPullback.of_hasPullback j e)

/-- **Étale postcomposition, for a closed composite.** A quasi-regular immersion `i` followed by
an étale morphism `e` with `i ≫ e` a closed immersion is a quasi-regular immersion. -/
private theorem isQuasiRegularImmersion_comp_of_etale_of_isClosedImmersion {Y X S : Scheme.{u}}
    (i : Y ⟶ X) (e : X ⟶ S) [IsImmersion i] [Etale e] [IsClosedImmersion (i ≫ e)]
    (hi : IsQuasiRegularImmersion i) : IsQuasiRegularImmersion (i ≫ e) := by
  classical
  obtain ⟨U, g, hgi, H⟩ := exists_isPullback_of_etale_of_isClosedImmersion i e
  obtain ⟨hgim, hg⟩ := isImmersion_and_isQuasiRegularImmersion_of_comp_isOpenImmersion g U.ι i
    hgi hi
  set j : Y ⟶ S := i ≫ e with hj
  set V : S.Opens := ⟨(Set.range j)ᶜ, j.isClosedEmbedding.isClosed_range.isOpen_compl⟩ with hV
  set obj : Bool → Scheme.{u} := fun b => if b then U.toScheme else V.toScheme with hobj
  set maps : (b : Bool) → obj b ⟶ S := fun b =>
    match b with
    | true => U.ι ≫ e
    | false => V.ι with hmaps
  set C : S.Cover Scheme.etalePrecoverage.{u} :=
    Scheme.Cover.mkOfCovers (P := @Etale) Bool obj maps
      (by
        intro s
        by_cases hs : s ∈ Set.range j
        · obtain ⟨y, rfl⟩ := hs
          exact ⟨true, g y, by rw [← Scheme.Hom.comp_apply, ← Category.assoc, hgi]⟩
        · exact ⟨false, ⟨s, hs⟩, rfl⟩)
      (by intro b; cases b <;> infer_instance) with hC
  have hP : quasiRegularImmersionProperty j := by
    refine MorphismProperty.IsLocalAtTarget.of_zeroHypercover
      (P := quasiRegularImmersionProperty.{u}) ⟨C.toPreZeroHypercover, C.mem₀⟩ fun b => ?_
    cases b
    · show quasiRegularImmersionProperty.{u} (pullback.snd j V.ι)
      have : IsEmpty (pullback j V.ι : Scheme.{u}) := by
        refine ⟨fun z => ?_⟩
        have hz := congrArg (fun h : pullback j V.ι ⟶ S => h z)
          (pullback.condition (f := j) (g := V.ι))
        exact (pullback.snd j V.ι z).2 ⟨pullback.fst j V.ι z, hz⟩
      exact ⟨inferInstance, isQuasiRegularImmersion_of_isEmpty _⟩
    · show quasiRegularImmersionProperty.{u} (pullback.snd j (U.ι ≫ e))
      rw [← H.isoPullback_inv_snd]
      exact (MorphismProperty.cancel_left_of_respectsIso quasiRegularImmersionProperty.{u}
        H.isoPullback.inv g).mpr ⟨inferInstance, hg⟩
  exact hP.choose_spec

/-- **Étale postcomposition.** A quasi-regular immersion followed by an étale morphism is a
quasi-regular immersion as soon as the composite is an immersion. -/
theorem isQuasiRegularImmersion_comp_of_etale {Y X S : Scheme.{u}} (i : Y ⟶ X) (e : X ⟶ S)
    [IsImmersion i] [Etale e] [IsImmersion (i ≫ e)] (hi : IsQuasiRegularImmersion i) :
    IsQuasiRegularImmersion (i ≫ e) := by
  obtain ⟨g, hgim, hgq, hgf⟩ := exists_isQuasiRegularImmersion_comp_morphismRestrict_eq_liftCoborder
    i e hi
  have : IsClosedImmersion (g ≫ (e ∣_ (i ≫ e).coborderRange)) := by rw [hgf]; infer_instance
  exact isQuasiRegularImmersion_of_liftCoborder _ <| isQuasiRegularImmersion_of_eq_hom hgf
    (isQuasiRegularImmersion_comp_of_etale_of_isClosedImmersion g _ hgq)

/-- **Smooth postcomposition, for closed immersions.** If `i` is a quasi-regular closed immersion,
`f` is smooth and `i ≫ f` is a closed immersion, then `i ≫ f` is a quasi-regular immersion. -/
private theorem isQuasiRegularImmersion_comp_of_smooth_of_isClosedImmersion
    {Y X S : Scheme.{u}} (i : Y ⟶ X) (f : X ⟶ S) [IsClosedImmersion i] [Smooth f]
    [IsClosedImmersion (i ≫ f)] (hi : IsQuasiRegularImmersion i) :
    IsQuasiRegularImmersion (i ≫ f) := by
  classical
  refine isQuasiRegularImmersion_of_forall_exists_opens (i ≫ f) fun y => ?_
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset
    (show (i ≫ f) y ∈ (⊤ : S.Opens) from trivial)
  obtain ⟨n, U, hU, hyU, hUV, π, hπ, hπf⟩ :=
    _root_.AlgebraicGeometry.exists_affine_open_etale_affineSpace f (i y) V hV hyV
      (InfinitesimalLifting.smoothAt_of_smooth f (i y))
  have : Etale π := hπ
  set W : Y.Opens := i ⁻¹ᵁ U with hW
  have hyW : y ∈ W := hyU
  set a : W.toScheme ⟶ Y := W.ι with ha
  have hai : IsQuasiRegularImmersion (a ≫ i) :=
    Stacks.AlgebraicGeometry.isQuasiRegularImmersion_comp_of_isH1RegularImmersion a i
      (isH1RegularImmersion_of_isOpenImmersion a) hi
  set g : W.toScheme ⟶ U.toScheme := i.resLE U W le_rfl with hg
  have hgi : g ≫ U.ι = a ≫ i := Scheme.Hom.resLE_comp_ι i le_rfl
  obtain ⟨hgim, hgq⟩ := isImmersion_and_isQuasiRegularImmersion_of_comp_isOpenImmersion g U.ι
    (a ≫ i) hgi hai
  have hWV : W ≤ (i ≫ f) ⁻¹ᵁ V := fun w hw => hUV hw
  have hWi : (g ≫ π) ≫ (AffineSpace (ULift.{u} (Fin n)) V.toScheme ↘ V.toScheme) =
      (i ≫ f).resLE V W hWV := by
    rw [Category.assoc, hπf, hg, Scheme.Hom.resLE_comp_resLE]
  have hgπbase : IsImmersion
      ((g ≫ π) ≫ (AffineSpace (ULift.{u} (Fin n)) V.toScheme ↘ V.toScheme)) := by
    rw [hWi]; infer_instance
  have hgπim : IsImmersion (g ≫ π) :=
    IsImmersion.of_comp (g ≫ π) (AffineSpace (ULift.{u} (Fin n)) V.toScheme ↘ V.toScheme)
  have hgπ : IsQuasiRegularImmersion (g ≫ π) :=
    isQuasiRegularImmersion_comp_of_etale g π hgq
  have hbase : IsQuasiRegularImmersion
      ((g ≫ π) ≫ (AffineSpace (ULift.{u} (Fin n)) V.toScheme ↘ V.toScheme)) :=
    isQuasiRegularImmersion_comp_affineSpace n (g ≫ π) hgπ
  refine ⟨W, hyW, ?_⟩
  have hfinal : IsQuasiRegularImmersion ((i ≫ f).resLE V W hWV) :=
    isQuasiRegularImmersion_of_eq_hom hWi hbase
  have hcomp : ((i ≫ f).resLE V W hWV) ≫ V.ι = W.ι ≫ (i ≫ f) :=
    Scheme.Hom.resLE_comp_ι (i ≫ f) hWV
  exact isQuasiRegularImmersion_of_eq_hom hcomp
    (isQuasiRegularImmersion_comp_isOpenImmersion _ V.ι hfinal)

/-- **Smooth postcomposition.** In a commutative triangle `Y ⟶ X ⟶ S` with `X ⟶ S` smooth and
both `Y ⟶ X` and `Y ⟶ S` immersions, the composite `Y ⟶ S` of a quasi-regular immersion `Y ⟶ X`
is a quasi-regular immersion. -/
@[stacks 0693 "quasi_regular"]
theorem isQuasiRegularImmersion_comp_of_smooth {Y X S : Scheme.{u}} (i : Y ⟶ X) (f : X ⟶ S)
    [IsImmersion i] [IsImmersion (i ≫ f)] [Smooth f] (hi : IsQuasiRegularImmersion i) :
    IsQuasiRegularImmersion (i ≫ f) := by
  obtain ⟨g, hgim, hgq, hgf⟩ := exists_isQuasiRegularImmersion_comp_morphismRestrict_eq_liftCoborder
    i f hi
  have hkq : g.liftCoborder ≫ (g.coborderRange.ι ≫ (f ∣_ (i ≫ f).coborderRange)) =
      (i ≫ f).liftCoborder := by
    rw [← Category.assoc, Scheme.Hom.liftCoborder_ι, hgf]
  have : IsClosedImmersion (g.liftCoborder ≫ (g.coborderRange.ι ≫ (f ∣_ (i ≫ f).coborderRange))) :=
    by rw [hkq]; infer_instance
  have hk : IsQuasiRegularImmersion g.liftCoborder :=
    isQuasiRegularImmersion_of_comp_of_smooth g.liftCoborder g.coborderRange.ι
      (by simpa only [Scheme.Hom.liftCoborder_ι] using hgq)
  exact isQuasiRegularImmersion_of_liftCoborder _ <| isQuasiRegularImmersion_of_eq_hom hkq
    (isQuasiRegularImmersion_comp_of_smooth_of_isClosedImmersion g.liftCoborder _ hk)

end Stacks.AlgebraicGeometry.RegularIdealSheaf

end
