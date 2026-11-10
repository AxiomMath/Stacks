module

public import StacksFrontier.AlgebraicGeometry.Etale.FpqcDescentApplication.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Pushout.ThickeningAffineGluingSquare
public import StacksFrontier.AlgebraicGeometry.Size.Basic
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover

namespace Stacks.Pushout.C1573
end Stacks.Pushout.C1573
namespace CategoryTheory.EquivalenceRelation.C1573
end CategoryTheory.EquivalenceRelation.C1573

/-!
# Gluing an étale relation across a pushout along a thickening

Let `k : U ⟶ U'` be a thickening and `g : U ⟶ V` an affine morphism of schemes, with pushout
`P = U' ⨿_U V` ([Stacks Project, Tag 07RT]).  This file collects the scheme-level facts about
schemes étale over `P` that the construction of a pushout of algebraic spaces along a thickening
and an affine morphism ([Stacks Project, Tag 07VX]) runs on, and glues compatible étale
equivalence relations on `U'` and on `V` to one on `P`.

## Main results

* `Stacks.Pushout.C1573.isPullback_of_isPushout_of_isPullback`: for an arbitrary cocartesian square
  `E₁ ⨿_{E₀} E₂` lying over `P` by cartesian squares, the two comparison squares over `U'` and
  over `V` are cartesian, and the induced map to `P` is étale when both pieces are; this is the
  identity `F ∘ G ≅ id` of [Stacks Project, Tag 07RV] and the étale clause of
  [Stacks Project, Tag 07RX], on arbitrary squares.
* `Stacks.Pushout.C1573.isPushout_of_etale_of_isPullback`: a scheme étale over `P` is the pushout
  of its restrictions to `U'` and to `V`, the closing paragraph of [Stacks Project, Tag 07RX] on
  arbitrary squares.
* `Stacks.Pushout.C1573.eq_of_comp_eq_of_surjective`: two morphisms into a scheme unramified over a
  base which agree after composing with a surjection, and have the same image in the base, are
  equal.
* `Stacks.Pushout.C1573.size_le_of_isPushout`: the pushout is no bigger than its two pieces.
* `Stacks.Pushout.C1573.isEquivalenceRelation_of_isPushout`: étale equivalence relations `R' ⇉ U'`
  and `T ⇉ V` restricting to the same relation on `U` glue to an étale equivalence relation
  `R' ⨿_{R₀} T ⇉ U' ⨿_U V`, the step of the proof of [Stacks Project, Tag 07VX] whose details
  the source omits.

## Implementation notes

Joint monicity of the glued relation is the source's argument: the pair is unramified, because
one of its projections is étale, and it is monic on the closed subscheme `T`, of which the glued
relation is a thickening; `Stacks.Pushout.C1573.eq_of_comp_eq_of_surjective` is the step from the
thickening to the whole.  Transitivity uses that the fibre product of the glued relation with
itself over `P` is étale over `P`, hence the pushout of its two restrictions, on which the
compositions of `R'` and of `T` are available.

## References

* [Stacks Project, Tag 07RT](https://stacks.math.columbia.edu/tag/07RT)
* [Stacks Project, Tag 07RV](https://stacks.math.columbia.edu/tag/07RV)
* [Stacks Project, Tag 07RX](https://stacks.math.columbia.edu/tag/07RX)
* [Stacks Project, Tag 07VX](https://stacks.math.columbia.edu/tag/07VX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Thickenings Cardinal

universe u

namespace Stacks.Pushout

open _root_.AlgebraicGeometry

/-! ### The comparison squares over a pushout, on arbitrary squares -/

open _root_.Stacks.Pushout.C1573
/-- **[Stacks Project, Tag 07RV], `F ∘ G ≅ id`, and the étale clause of
[Stacks Project, Tag 07RX], on arbitrary squares.**  Let `i : X ⟶ X'` be a thickening, `f : X ⟶ Y`
affine and `P` any scheme carrying their pushout square.  Let `E₁ ⟶ X'` and `E₂ ⟶ Y` restrict to
the same `E₀ ⟶ X` by two cartesian squares, let `W` carry any pushout square of `E₀ ⟶ E₁` and
`E₀ ⟶ E₂`, and let `w : W ⟶ P` be compatible with the two pieces.  Then both comparison squares
are cartesian, and `w` is étale when both pieces are. -/
theorem C1573.isPullback_of_isPushout_of_isPullback {X X' Y P E₀ E₁ E₂ W : Scheme.{u}}
    {i : X ⟶ X'} {f : X ⟶ Y} {a : X' ⟶ P} {b : Y ⟶ P}
    (hi : IsThickening i) [IsAffineHom f] (hP : IsPushout i f a b)
    {iE : E₀ ⟶ E₁} {fE : E₀ ⟶ E₂} {p₀ : E₀ ⟶ X} {p₁ : E₁ ⟶ X'} {p₂ : E₂ ⟶ Y}
    (hcart₁ : IsPullback iE p₀ p₁ i) (hcart₂ : IsPullback fE p₀ p₂ f)
    {u₁ : E₁ ⟶ W} {u₂ : E₂ ⟶ W} (hE : IsPushout iE fE u₁ u₂) {w : W ⟶ P}
    (hw₁ : u₁ ≫ w = p₁ ≫ a) (hw₂ : u₂ ≫ w = p₂ ≫ b) :
    IsPullback u₁ p₁ w a ∧ IsPullback u₂ p₂ w b ∧ (Etale p₁ → Etale p₂ → Etale w) := by
  have : HasPushout i f := hP.hasPushout
  let rightRestriction : (Over.pullback f).obj (Over.mk p₂) ≅ Over.mk p₀ :=
    Over.isoMk hcart₂.isoPullback.symm (by exact hcart₂.isoPullback_inv_snd)
  let leftRestriction : (Over.pullback i).obj (Over.mk p₁) ≅ Over.mk p₀ :=
    Over.isoMk hcart₁.isoPullback.symm (by exact hcart₁.isoPullback_inv_snd)
  let TglueComma : Comma (Over.pullback f) (Over.pullback i) :=
    ⟨Over.mk p₂, Over.mk p₁, (rightRestriction ≪≫ leftRestriction.symm).hom⟩
  have hTglueIso : IsIso TglueComma.hom := by
    dsimp [TglueComma]
    infer_instance
  let Tglue : gluingData i f := ⟨TglueComma, hTglueIso⟩
  let := gluingHasPushout i f hi Tglue
  obtain ⟨hd, hc⟩ := gluing_components_isPullback i f hi Tglue
  have hcompat : hcart₁.isoPullback.hom ≫ (inv Tglue.obj.hom).left =
      hcart₂.isoPullback.hom := by
    have hTglueHom : Tglue.obj.hom = rightRestriction.hom ≫ leftRestriction.inv := rfl
    have hTglueInv : inv Tglue.obj.hom = leftRestriction.hom ≫ rightRestriction.inv := by
      apply (IsIso.eq_inv_of_hom_inv_id _).symm
      rw [hTglueHom]
      simp
    have hLeftInv : (inv Tglue.obj.hom).left =
        leftRestriction.hom.left ≫ rightRestriction.inv.left :=
      congrArg (fun m ↦ m.left) hTglueInv
    rw [hLeftInv]
    simp [leftRestriction, rightRestriction, Over.isoMk]
  have hsource : hcart₁.isoPullback.hom ≫ gluingSourceMap i f Tglue = fE := by
    change hcart₁.isoPullback.hom ≫
      (inv Tglue.obj.hom).left ≫ pullback.fst Tglue.obj.left.hom f = fE
    rw [← Category.assoc, hcompat]
    exact hcart₂.isoPullback_hom_fst
  let inlG := pushout.inl (pullback.fst Tglue.obj.right.hom i) (gluingSourceMap i f Tglue)
  let inrG := pushout.inr (pullback.fst Tglue.obj.right.hom i) (gluingSourceMap i f Tglue)
  have hglue : IsPushout iE fE inlG inrG := by
    refine (IsPushout.of_hasPushout (pullback.fst Tglue.obj.right.hom i)
      (gluingSourceMap i f Tglue)).of_iso hcart₁.isoPullback.symm
      (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · change pullback.fst p₁ i ≫ 𝟙 _ = hcart₁.isoPullback.inv ≫ iE
      rw [Category.comp_id]
      exact hcart₁.isoPullback_inv_fst.symm
    · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
      apply (cancel_epi hcart₁.isoPullback.hom).mp
      simpa using hsource
    · simp [inlG]
    · simp [inrG]
  let gG : pushout (pullback.fst Tglue.obj.right.hom i) (gluingSourceMap i f Tglue) ⟶
      pushout i f := ((gluingFunctor i f hi).obj Tglue).hom
  let φ := hE.isoIsPushout _ _ hglue
  have hφ₁ : u₁ ≫ φ.hom = inlG := hE.inl_isoIsPushout_hom _ _ hglue
  have hφ₂ : u₂ ≫ φ.hom = inrG := hE.inr_isoIsPushout_hom _ _ hglue
  have hGinl : inlG ≫ gG = p₁ ≫ pushout.inl i f := hc.w
  have hGinr : inrG ≫ gG = p₂ ≫ pushout.inr i f := hd.w
  have hφw : φ.hom ≫ gG = w ≫ hP.isoPushout.hom := by
    apply hE.hom_ext
    · rw [reassoc_of% hφ₁, hGinl, reassoc_of% hw₁, hP.inl_isoPushout_hom]
    · rw [reassoc_of% hφ₂, hGinr, reassoc_of% hw₂, hP.inr_isoPushout_hom]
  have hc' : IsPullback inlG p₁ gG (pushout.inl i f) := hc
  have hd' : IsPullback inrG p₂ gG (pushout.inr i f) := hd
  have hφw' : gG ≫ hP.isoPushout.inv = φ.inv ≫ w := by
    rw [Iso.eq_inv_comp, reassoc_of% hφw, Iso.hom_inv_id, Category.comp_id]
  have key : ∀ {E A : Scheme.{u}} {pA : E ⟶ A} {uE : E ⟶ W} {inl : E ⟶ _}
      {c : A ⟶ P} {q : A ⟶ pushout i f}, IsPullback inl pA gG q → uE ≫ φ.hom = inl →
      c ≫ hP.isoPushout.hom = q → IsPullback uE pA w c := by
    rintro E A pA uE inl c q hc rfl rfl
    refine hc.of_iso (Iso.refl _) φ.symm (Iso.refl _) hP.isoPushout.symm ?_ ?_ ?_ ?_
    · simp
    · simp
    · exact hφw'
    · simp
  refine ⟨key hc' hφ₁ hP.inl_isoPushout_hom, key hd' hφ₂ hP.inr_isoPushout_hom, ?_⟩
  · intro h₁ h₂
    have hG : Etale gG := (etale_gluingFunctor_obj_iff i f hi Tglue).2 ⟨h₂, h₁⟩
    have hw : w = φ.hom ≫ gG ≫ hP.isoPushout.inv := by
      rw [hφw', Iso.hom_inv_id_assoc]
    rw [hw]
    infer_instance

/-! ### A scheme étale over the pushout is glued from its two restrictions -/

/-- An étale morphism `m` is an isomorphism as soon as some thickening `j` into its source stays a
thickening after composing with `m`: then `m` is universally injective, hence an open immersion,
and it is surjective. -/
theorem C1573.isIso_of_etale_of_isThickening_comp {Z W U : Scheme.{u}} (m : W ⟶ U) [Etale m]
    (j : Z ⟶ W) (hjm : IsThickening (j ≫ m)) (hj : IsThickening j) : IsIso m := by
  have : Surjective j := ⟨hj.2⟩
  have : IsClosedImmersion (j ≫ m) := hjm.1
  have : UniversallyInjective m := by
    constructor
    intro W' U' s t m' h
    have hsurj : Surjective (pullback.snd j s) := inferInstance
    have hinj := (inferInstance : UniversallyInjective (j ≫ m)).universally_injective
      _ _ _ ((IsPullback.of_hasPullback j s).flip.paste_horiz h)
    intro x y hxy
    obtain ⟨a, rfl⟩ := hsurj.surj x
    obtain ⟨b, rfl⟩ := hsurj.surj y
    exact congrArg (pullback.snd j s) (hinj hxy)
  have : Surjective m := ⟨fun x ↦ by
    obtain ⟨z, hz⟩ := hjm.2 x
    exact ⟨j z, hz⟩⟩
  exact (isIso_iff_isOpenImmersion_and_surjective m).2 ⟨inferInstance, inferInstance⟩

/-- **The closing paragraph of [Stacks Project, Tag 07RX] for étale schemes, on arbitrary
squares.**  Let `P` carry the pushout square of a thickening `i : X ⟶ X'` and an affine morphism
`f : X ⟶ Y`, and let `π : W ⟶ P` be étale.  Its restrictions `E₁ = W ×_P X'` and `E₂ = W ×_P Y`,
over their common restriction `E₀`, form a pushout square with apex `W`. -/
theorem C1573.isPushout_of_etale_of_isPullback {X X' Y P W E₀ E₁ E₂ : Scheme.{u}}
    {i : X ⟶ X'} {f : X ⟶ Y} {a : X' ⟶ P} {b : Y ⟶ P}
    (hi : IsThickening i) [IsAffineHom f] (hP : IsPushout i f a b) (π : W ⟶ P) [Etale π]
    {u₁ : E₁ ⟶ W} {u₂ : E₂ ⟶ W} {p₁ : E₁ ⟶ X'} {p₂ : E₂ ⟶ Y}
    (h₁ : IsPullback u₁ p₁ π a) (h₂ : IsPullback u₂ p₂ π b)
    {iE : E₀ ⟶ E₁} {fE : E₀ ⟶ E₂} {p₀ : E₀ ⟶ X}
    (hcart₁ : IsPullback iE p₀ p₁ i) (hcart₂ : IsPullback fE p₀ p₂ f)
    (hw : iE ≫ u₁ = fE ≫ u₂) : IsPushout iE fE u₁ u₂ := by
  have hiE : IsThickening iE := isThickening_of_isPullback hcart₁ hi
  have : IsAffineHom fE := MorphismProperty.of_isPullback hcart₂.flip inferInstance
  have : HasPushout iE fE := hasPushout_of_isThickening_of_isAffineHom' iE fE hiE
  have hE := IsPushout.of_hasPushout iE fE
  let m := pushout.desc u₁ u₂ hw
  have hm₁ : pushout.inl iE fE ≫ m = u₁ := pushout.inl_desc _ _ _
  have hm₂ : pushout.inr iE fE ≫ m = u₂ := pushout.inr_desc _ _ _
  obtain ⟨-, -, he⟩ := isPullback_of_isPushout_of_isPullback hi hP hcart₁ hcart₂ hE
    (w := m ≫ π) (by rw [← Category.assoc, hm₁, h₁.w]) (by rw [← Category.assoc, hm₂, h₂.w])
  have : Etale (m ≫ π) := he (MorphismProperty.of_isPullback h₁ inferInstance)
    (MorphismProperty.of_isPullback h₂ inferInstance)
  have : Etale m := Etale.of_comp m π
  have hu₂ : IsThickening (pushout.inr iE fE ≫ m) := by
    rw [hm₂]
    exact isThickening_of_isPullback h₂ (isThickening_of_isPushout_of_isThickening hP hi)
  have : IsIso m := isIso_of_etale_of_isThickening_comp m _ hu₂
    (isThickening_of_isPushout_of_isThickening hE hiE)
  exact hE.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (asIso m) (by simp) (by simp)
    (by simpa using hm₁) (by simpa using hm₂)

/-! ### Rigidity of morphisms into an unramified scheme -/

/-- Two morphisms `φ, ψ : W ⟶ R` into a scheme unramified over `P`, with the same composite to
`P`, are equal as soon as they agree after composing with a surjection `W₀ ⟶ W`: the locus where
they agree is the preimage of the diagonal, which is open, and it contains every point. -/
theorem C1573.eq_of_comp_eq_of_surjective {W W₀ R P : Scheme.{u}} (s : R ⟶ P)
    [FormallyUnramified s] [LocallyOfFiniteType s] {φ ψ : W ⟶ R} (h : φ ≫ s = ψ ≫ s)
    (w₀ : W₀ ⟶ W) (hw₀ : Function.Surjective w₀) (h₀ : w₀ ≫ φ = w₀ ≫ ψ) : φ = ψ := by
  let l := pullback.lift φ ψ h
  have hl : w₀ ≫ l = (w₀ ≫ φ) ≫ pullback.diagonal s := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.diagonal_fst,
        Category.comp_id]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.diagonal_snd,
        Category.comp_id, h₀]
  have hrange : Set.range l ⊆ Set.range (pullback.diagonal s) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := hw₀ x
    refine ⟨(w₀ ≫ φ) y, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hl, Scheme.Hom.comp_apply]
  let m := IsOpenImmersion.lift (pullback.diagonal s) l hrange
  have hm : m ≫ pullback.diagonal s = l := IsOpenImmersion.lift_fac _ _ _
  calc φ = l ≫ pullback.fst s s := (pullback.lift_fst _ _ _).symm
    _ = m := by rw [← hm, Category.assoc, pullback.diagonal_fst, Category.comp_id]
    _ = l ≫ pullback.snd s s := by
      rw [← hm, Category.assoc, pullback.diagonal_snd, Category.comp_id]
    _ = ψ := pullback.lift_snd _ _ _

/-! ### The size of the pushout -/

/-- The scheme carrying a pushout square of a thickening `i : X ⟶ X'` and an affine morphism
`f : X ⟶ Y` is no bigger than `X'` and `Y`: its affine opens are determined by their preimages in
`Y`, and its sections are a fibre product of sections on `Y` and on `X'`
([Stacks Project, Tag 07RT]). -/
theorem C1573.size_le_of_isPushout {X X' Y P : Scheme.{u}} {i : X ⟶ X'} {f : X ⟶ Y}
    {a : X' ⟶ P} {b : Y ⟶ P} (hi : IsThickening i) [IsAffineHom f] (hP : IsPushout i f a b) :
    P.size ≤ max X'.size Y.size := by
  classical
  have hb : IsThickening b := isThickening_of_isPushout_of_isThickening hP hi
  have : IsAffineHom a := isAffineHom_of_isPushout_of_isThickening hP hi
  have : IsClosedImmersion b := hb.1
  have h0 : ℵ₀ ≤ max X'.size Y.size := (Scheme.aleph0_le_size Y).trans (le_max_right _ _)
  refine Scheme.size_le_of_bounds h0 ?_ ?_
  · let φ : P.affineOpens → Y.affineOpens := fun U ↦ ⟨b ⁻¹ᵁ U.1, U.2.preimage b⟩
    have hφ : Function.Injective φ := by
      intro U V h
      apply Subtype.ext
      ext p
      obtain ⟨y, rfl⟩ := hb.2 p
      have hpre : b ⁻¹ᵁ U.1 = b ⁻¹ᵁ V.1 := congrArg Subtype.val h
      change y ∈ (b ⁻¹ᵁ U.1 : Set Y) ↔ y ∈ (b ⁻¹ᵁ V.1 : Set Y)
      rw [hpre]
    exact (Cardinal.mk_le_of_injective hφ).trans
      ((Scheme.mk_affineOpens_le_size Y).trans (le_max_right _ _))
  · intro U
    let hPB := (AlgebraicGeometry.ThickeningAffinePushoutSituation.sections_isPullback_of_isPushout
      hi hP U.1).map (forget CommRingCat)
    let g : Γ(P, U.1) → Γ(Y, b ⁻¹ᵁ U.1) × Γ(X', a ⁻¹ᵁ U.1) := fun x ↦
      (b.app U.1 x, a.app U.1 x)
    have hg : Function.Injective g := fun x y hxy ↦
      PullbackCone.IsLimit.type_ext hPB.isLimit (congrArg Prod.fst hxy) (congrArg Prod.snd hxy)
    have hY : #Γ(Y, b ⁻¹ᵁ U.1) ≤ max X'.size Y.size :=
      (Scheme.mk_sections_le_size Y ⟨b ⁻¹ᵁ U.1, U.2.preimage b⟩).trans (le_max_right _ _)
    have hX : #Γ(X', a ⁻¹ᵁ U.1) ≤ max X'.size Y.size :=
      (Scheme.mk_sections_le_size X' ⟨a ⁻¹ᵁ U.1, U.2.preimage a⟩).trans (le_max_left _ _)
    calc #(Γ(P, U.1)) ≤ #(Γ(Y, b ⁻¹ᵁ U.1) × Γ(X', a ⁻¹ᵁ U.1)) :=
          Cardinal.mk_le_of_injective hg
      _ = #Γ(Y, b ⁻¹ᵁ U.1) * #Γ(X', a ⁻¹ᵁ U.1) := by simp [Cardinal.mk_prod]
      _ ≤ max (max #Γ(Y, b ⁻¹ᵁ U.1) #Γ(X', a ⁻¹ᵁ U.1)) ℵ₀ := Cardinal.mul_le_max _ _
      _ ≤ max X'.size Y.size := max_le (max_le hY hX) h0

/-! ### Gluing an equivalence relation across the pushout -/

/-- Transitivity of an internal equivalence relation `p₁, p₂ : R ⇉ U`, read on points: two points
`x, y` of `R` with `p₂ x = p₁ y` compose to a point of `R` from `p₁ x` to `p₂ y`. -/
theorem _root_.CategoryTheory.EquivalenceRelation.C1573.exists_trans {C : Type*} [Category C]
    {R U : C} {p₁ p₂ : R ⟶ U} (e : EquivalenceRelation p₁ p₂) {Z : C} (x y : Z ⟶ R)
    (h : x ≫ p₂ = y ≫ p₁) : ∃ z : Z ⟶ R, z ≫ p₁ = x ≫ p₁ ∧ z ≫ p₂ = y ≫ p₂ := by
  let m := PullbackCone.IsLimit.lift e.isLimit x y h
  have hm₁ : m ≫ e.c.fst = x := PullbackCone.IsLimit.lift_fst _ _ _ _
  have hm₂ : m ≫ e.c.snd = y := PullbackCone.IsLimit.lift_snd _ _ _ _
  refine ⟨m ≫ e.t, ?_, ?_⟩
  · rw [Category.assoc, e.transitivity₁, ← Category.assoc, hm₁]
  · rw [Category.assoc, e.transitivity₂, ← Category.assoc, hm₂]

/-- Composing two points `x, y` of a relation `Rel` glued over `R'` along `R' ⟶ Rel`, with
`x` and `y` over the same point of `U'`, yields a point of `R'` compatible with both. -/
private theorem exists_comp_of_isPullback {R' Rel U' P Z : Scheme.{u}} {s' t' : R' ⟶ U'}
    {a : U' ⟶ P} {aR : R' ⟶ Rel} {s t : Rel ⟶ P} (e : EquivalenceRelation t' s')
    (hs : IsPullback aR s' s a) (ht : IsPullback aR t' t a) (x y : Z ⟶ Rel) (σ : Z ⟶ U')
    (hx : x ≫ s = σ ≫ a) (hy : y ≫ t = σ ≫ a) :
    ∃ z : Z ⟶ R', z ≫ aR ≫ t = x ≫ t ∧ z ≫ aR ≫ s = y ≫ s := by
  obtain ⟨z, hzt, hzs⟩ := (CategoryTheory.EquivalenceRelation.C1573.exists_trans (e := e))
    (hs.lift x σ hx) (ht.lift y σ hy) ((hs.lift_snd _ _ _).trans (ht.lift_snd _ _ _).symm)
  refine ⟨z, ?_, ?_⟩
  · rw [ht.w, reassoc_of% hzt, ← ht.w, ← Category.assoc, hs.lift_fst]
  · rw [hs.w, reassoc_of% hzs, ← hs.w, ← Category.assoc, ht.lift_fst]

section Relation

variable {U U' V R₀ R' T P Rel : Scheme.{u}} {k : U ⟶ U'} {g : U ⟶ V}
  {s₀ t₀ : R₀ ⟶ U} {s' t' : R' ⟶ U'} {sY tY : T ⟶ V} {kR : R₀ ⟶ R'} {gR : R₀ ⟶ T}
  {a : U' ⟶ P} {b : V ⟶ P} {aR : R' ⟶ Rel} {bR : T ⟶ Rel} {s t : Rel ⟶ P}

/-- **An étale equivalence relation glued across a pushout along a thickening.**  Let
`k : U ⟶ U'` be a thickening and `g : U ⟶ V` affine, with pushout `P = U' ⨿_U V`.  Let
`R' ⇉ U'` and `T ⇉ V` be étale equivalence relations restricting to the same relation `R₀ ⇉ U`,
in the sense that the four squares comparing `R₀` with `R'` over `k` and with `T` over `g` are
cartesian.  Then the two projections `s, t : R' ⨿_{R₀} T ⇉ P` glued from them form an étale
equivalence relation on `P`.

This is the paragraph of the proof of [Stacks Project, Tag 07VX] whose details the source omits.
The projections are étale by [Stacks Project, Tag 07RX], and the four comparison squares over `P`
are cartesian by [Stacks Project, Tag 07RV].  The pair is jointly monic because on the closed
subscheme `T`, a thickening of `R' ⨿_{R₀} T`, it is, and `s` is unramified.  Reflexivity and
symmetry come from the functoriality of pushouts, and transitivity from gluing the compositions
of `R'` and of `T` across the restrictions of `(R' ⨿_{R₀} T) ×_P (R' ⨿_{R₀} T)` to `U'` and to
`V`, a scheme étale over `P` being the pushout of its two restrictions. -/
theorem C1573.isEquivalenceRelation_of_isPushout (hk : IsThickening k) [IsAffineHom g]
    (hP : IsPushout k g a b) (hRel : IsPushout kR gR aR bR)
    (h₁ : IsPullback kR s₀ s' k) (h₂ : IsPullback kR t₀ t' k)
    (h₃ : IsPullback gR s₀ sY g) (h₄ : IsPullback gR t₀ tY g)
    [Etale s'] [Etale t'] [Etale sY] [Etale tY]
    (eR : IsEquivalenceRelation t' s') (eT : IsEquivalenceRelation tY sY)
    (has : aR ≫ s = s' ≫ a) (hat : aR ≫ t = t' ≫ a)
    (hbs : bR ≫ s = sY ≫ b) (hbt : bR ≫ t = tY ≫ b) :
    IsEquivalenceRelation t s ∧ Etale s ∧ Etale t := by
  obtain ⟨ER⟩ := eR.nonempty_equivalenceRelation
  obtain ⟨ET⟩ := eT.nonempty_equivalenceRelation
  have hb : IsThickening b := isThickening_of_isPushout_of_isThickening hP hk
  have : IsClosedImmersion b := hb.1
  have : IsClosedImmersion k := hk.1
  obtain ⟨CRas, CRbs, hEs⟩ := isPullback_of_isPushout_of_isPullback hk hP h₁ h₃ hRel has hbs
  obtain ⟨CRat, CRbt, hEt⟩ := isPullback_of_isPushout_of_isPullback hk hP h₂ h₄ hRel hat hbt
  have : Etale s := hEs inferInstance inferInstance
  have : Etale t := hEt inferInstance inferInstance
  -- joint monicity
  have hjm : ∀ {Z : Scheme.{u}} (x y : Z ⟶ Rel), x ≫ t = y ≫ t → x ≫ s = y ≫ s → x = y := by
    intro Z x y hxt hxs
    have hw₀ : IsThickening (pullback.fst (x ≫ s) b) :=
      isThickening_of_isPullback (IsPullback.of_hasPullback _ _) hb
    refine eq_of_comp_eq_of_surjective s hxs (pullback.fst (x ≫ s) b) hw₀.2 ?_
    have hcx : (pullback.fst (x ≫ s) b ≫ x) ≫ s = pullback.snd (x ≫ s) b ≫ b := by
      rw [Category.assoc, pullback.condition]
    have hcy : (pullback.fst (x ≫ s) b ≫ y) ≫ s = pullback.snd (x ≫ s) b ≫ b := by
      rw [Category.assoc, ← hxs, pullback.condition]
    have hx₁ := CRbs.lift_fst _ _ hcx
    have hx₂ := CRbs.lift_snd _ _ hcx
    have hy₁ := CRbs.lift_fst _ _ hcy
    have hy₂ := CRbs.lift_snd _ _ hcy
    have hxy : CRbs.lift _ _ hcx = CRbs.lift _ _ hcy := by
      refine ET.right_cancellation _ _ ?_ (hx₂.trans hy₂.symm)
      rw [← cancel_mono b]
      simp only [Category.assoc, ← hbt]
      simp only [← Category.assoc, hx₁, hy₁]
      simp only [Category.assoc, hxt]
    rw [← hx₁, ← hy₁, hxy]
  -- reflexivity
  let e₀ : U ⟶ R₀ := h₁.lift (k ≫ ER.r) (𝟙 U) (by
    rw [Category.assoc, ER.reflexivity₂, Category.comp_id, Category.id_comp])
  have he₀k : e₀ ≫ kR = k ≫ ER.r := h₁.lift_fst _ _ _
  have he₀s : e₀ ≫ s₀ = 𝟙 U := h₁.lift_snd _ _ _
  have he₀t : e₀ ≫ t₀ = 𝟙 U := by
    rw [← cancel_mono k, Category.assoc, ← h₂.w, ← Category.assoc, he₀k, Category.assoc,
      ER.reflexivity₁, Category.comp_id, Category.id_comp]
  have he₀g : e₀ ≫ gR = g ≫ ET.r := by
    refine ET.right_cancellation _ _ ?_ ?_
    · rw [Category.assoc, h₄.w, ← Category.assoc, he₀t, Category.assoc, ET.reflexivity₁,
        Category.id_comp, Category.comp_id]
    · rw [Category.assoc, h₃.w, ← Category.assoc, he₀s, Category.assoc, ET.reflexivity₂,
        Category.id_comp, Category.comp_id]
  let eP : P ⟶ Rel := hP.desc (ER.r ≫ aR) (ET.r ≫ bR) (by
    rw [← Category.assoc, ← he₀k, Category.assoc, hRel.w, ← Category.assoc, he₀g,
      Category.assoc])
  have heP₁ : a ≫ eP = ER.r ≫ aR := hP.inl_desc _ _ _
  have heP₂ : b ≫ eP = ET.r ≫ bR := hP.inr_desc _ _ _
  have hreft : eP ≫ t = 𝟙 P := by
    apply hP.hom_ext
    · rw [reassoc_of% heP₁, hat, reassoc_of% ER.reflexivity₁, Category.comp_id]
    · rw [reassoc_of% heP₂, hbt, reassoc_of% ET.reflexivity₁, Category.comp_id]
  have hrefs : eP ≫ s = 𝟙 P := by
    apply hP.hom_ext
    · rw [reassoc_of% heP₁, has, reassoc_of% ER.reflexivity₂, Category.comp_id]
    · rw [reassoc_of% heP₂, hbs, reassoc_of% ET.reflexivity₂, Category.comp_id]
  -- symmetry
  let σ₀ : R₀ ⟶ R₀ := h₁.lift (kR ≫ ER.s) t₀ (by
    rw [Category.assoc, ER.symmetry₂, h₂.w])
  have hσ₀k : σ₀ ≫ kR = kR ≫ ER.s := h₁.lift_fst _ _ _
  have hσ₀s : σ₀ ≫ s₀ = t₀ := h₁.lift_snd _ _ _
  have hσ₀t : σ₀ ≫ t₀ = s₀ := by
    rw [← cancel_mono k, Category.assoc, ← h₂.w, ← Category.assoc, hσ₀k, Category.assoc,
      ER.symmetry₁, h₁.w]
  have hσ₀g : σ₀ ≫ gR = gR ≫ ET.s := by
    refine ET.right_cancellation _ _ ?_ ?_
    · rw [Category.assoc, h₄.w, ← Category.assoc, hσ₀t, Category.assoc, ET.symmetry₁, h₃.w]
    · rw [Category.assoc, h₃.w, ← Category.assoc, hσ₀s, Category.assoc, ET.symmetry₂, h₄.w]
  let σ : Rel ⟶ Rel := hRel.desc (ER.s ≫ aR) (ET.s ≫ bR) (by
    rw [← Category.assoc, ← hσ₀k, Category.assoc, hRel.w, ← Category.assoc, hσ₀g,
      Category.assoc])
  have hσ₁ : aR ≫ σ = ER.s ≫ aR := hRel.inl_desc _ _ _
  have hσ₂ : bR ≫ σ = ET.s ≫ bR := hRel.inr_desc _ _ _
  have hsymt : σ ≫ t = s := by
    apply hRel.hom_ext
    · rw [reassoc_of% hσ₁, hat, reassoc_of% ER.symmetry₁, has]
    · rw [reassoc_of% hσ₂, hbt, reassoc_of% ET.symmetry₁, hbs]
  have hsyms : σ ≫ s = t := by
    apply hRel.hom_ext
    · rw [reassoc_of% hσ₁, has, reassoc_of% ER.symmetry₂, hat]
    · rw [reassoc_of% hσ₂, hbs, reassoc_of% ET.symmetry₂, hbt]
  -- transitivity
  let μ : pullback s t ⟶ P := pullback.fst s t ≫ s
  have : Etale (pullback.fst s t) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback s t).flip inferInstance
  have : Etale μ := inferInstance
  let ι₁ := pullback.fst μ a
  let σ₁ := pullback.snd μ a
  let ι₂ := pullback.fst μ b
  let σ₂ := pullback.snd μ b
  let iE := pullback.fst σ₁ k
  let p₀ := pullback.snd σ₁ k
  have hc₁ : IsPullback iE p₀ σ₁ k := IsPullback.of_hasPullback _ _
  have hfE : (iE ≫ ι₁) ≫ μ = (p₀ ≫ g) ≫ b := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
      Category.assoc, hP.w, Category.assoc]
  let fE : pullback σ₁ k ⟶ pullback μ b := pullback.lift (iE ≫ ι₁) (p₀ ≫ g) hfE
  have hfE₁ : fE ≫ ι₂ = iE ≫ ι₁ := pullback.lift_fst _ _ _
  have hfE₂ : fE ≫ σ₂ = p₀ ≫ g := pullback.lift_snd _ _ _
  have hc₂ : IsPullback fE p₀ σ₂ g := by
    have hbig : IsPullback (iE ≫ ι₁) p₀ μ (k ≫ a) :=
      hc₁.paste_horiz (IsPullback.of_hasPullback μ a)
    rw [hP.w, ← hfE₁] at hbig
    exact IsPullback.of_right hbig hfE₂ (IsPullback.of_hasPullback μ b)
  have hW : IsPushout iE fE ι₁ ι₂ :=
    isPushout_of_etale_of_isPullback hk hP μ (IsPullback.of_hasPullback μ a)
      (IsPullback.of_hasPullback μ b) hc₁ hc₂ hfE₁.symm
  -- the composition over `U'`
  obtain ⟨z₁, hl₁t, hl₁s⟩ := exists_comp_of_isPullback ER CRas CRat (ι₁ ≫ pullback.fst s t)
    (ι₁ ≫ pullback.snd s t) σ₁ (by rw [Category.assoc, pullback.condition])
    (by rw [Category.assoc, ← pullback.condition, pullback.condition])
  -- the composition over `V`
  obtain ⟨z₂, hl₂t, hl₂s⟩ := exists_comp_of_isPullback ET CRbs CRbt (ι₂ ≫ pullback.fst s t)
    (ι₂ ≫ pullback.snd s t) σ₂ (by rw [Category.assoc, pullback.condition])
    (by rw [Category.assoc, ← pullback.condition, pullback.condition])
  let τ : pullback s t ⟶ Rel := hW.desc (z₁ ≫ aR) (z₂ ≫ bR) (by
    apply hjm
    · simp only [Category.assoc, hl₁t, hl₂t]
      rw [reassoc_of% hfE₁]
    · simp only [Category.assoc, hl₁s, hl₂s]
      rw [reassoc_of% hfE₁])
  have hτ₁ : ι₁ ≫ τ = z₁ ≫ aR := hW.inl_desc _ _ _
  have hτ₂ : ι₂ ≫ τ = z₂ ≫ bR := hW.inr_desc _ _ _
  have htrt : τ ≫ t = pullback.fst s t ≫ t := by
    apply hW.hom_ext
    · rw [reassoc_of% hτ₁, hl₁t, Category.assoc]
    · rw [reassoc_of% hτ₂, hl₂t, Category.assoc]
  have htrs : τ ≫ s = pullback.snd s t ≫ s := by
    apply hW.hom_ext
    · rw [reassoc_of% hτ₁, hl₁s, Category.assoc]
    · rw [reassoc_of% hτ₂, hl₂s, Category.assoc]
  refine ⟨EquivalenceRelation.isEquivalenceRelation
    { right_cancellation := fun _ x y h₁ h₂ => hjm x y h₁ h₂
      r := eP
      reflexivity₁ := hreft
      reflexivity₂ := hrefs
      s := σ
      symmetry₁ := hsymt
      symmetry₂ := hsyms
      c := pullback.cone s t
      isLimit := pullback.isLimit s t
      t := τ
      transitivity₁ := htrt
      transitivity₂ := htrs }, inferInstance, inferInstance⟩

end Relation

end Stacks.Pushout

end
