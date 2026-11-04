module

public import StacksFrontier.AlgebraicGeometry.Etale.FpqcDescentApplication.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutGluing
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.Colimits
public import StacksFrontier.AlgebraicGeometry.Thickenings.Affine
public import StacksFrontier.AlgebraicGeometry.Topologies.EtaleDescentIntegral
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Scheme pushouts along a thickening remain pushouts of algebraic spaces

Let `X ⟶ X'` be a thickening of schemes over `S` and `X ⟶ Y` an affine morphism of schemes over
`S`.  The pushout `Y' = Y ⨿_X X'` in schemes is again a pushout in the much larger category of
algebraic spaces over `S`: the three hypotheses of the general colimit criterion are supplied by
the étale-gluing description of schemes over `Y'`.

## Main results

* `AlgebraicGeometry.Space.isPushout_algebraicSpaces_of_isThickening_of_isAffineHom`:
  **Stacks 07SY**, the scheme pushout is a pushout of algebraic spaces over `S`.

## References

* [Stacks Project, Tag 07SY](https://stacks.math.columbia.edu/tag/07SY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Thickenings
open Stacks.Thickenings

namespace AlgebraicGeometry

universe u

namespace Space

/-- A morphism becomes universally injective as soon as its composite with a surjection on the
left is universally injective. -/
@[ega "IV 6.15.3.1" "(i)"]
private lemma universallyInjective_of_surjective_comp
    {Z W U : Scheme.{u}} (j : Z ⟶ W) (m : W ⟶ U)
    [Surjective j] [UniversallyInjective (j ≫ m)] : UniversallyInjective m := by
  constructor
  intro W' U' s t m' h
  have hsurj : Surjective (pullback.snd j s) := inferInstance
  have hinj := (inferInstance : UniversallyInjective (j ≫ m)).universally_injective
    _ _ _ ((IsPullback.of_hasPullback j s).flip.paste_horiz h)
  intro x y hxy
  obtain ⟨a, rfl⟩ := hsurj.surj x
  obtain ⟨b, rfl⟩ := hsurj.surj y
  exact congrArg (pullback.snd j s) (hinj hxy)

/-- An étale morphism that turns a thickening into a thickening is an isomorphism. -/
private lemma isIso_of_etale_of_thickening_comp
    {Z W U : Scheme.{u}} (j : Z ⟶ W) (m : W ⟶ U)
    (hj : IsThickening j) [Etale m] (hjm : IsThickening (j ≫ m)) : IsIso m := by
  have : Surjective j := ⟨hj.2⟩
  have : _root_.AlgebraicGeometry.IsClosedImmersion (j ≫ m) := hjm.1
  have : UniversallyInjective m := universallyInjective_of_surjective_comp j m
  have : Surjective m := ⟨fun x ↦ by
    obtain ⟨z, hz⟩ := hjm.2 x
    exact ⟨j z, hz⟩⟩
  have : _root_.AlgebraicGeometry.IsOpenImmersion m :=
    isOpenImmersion_of_etale_universallyInjective m
  exact (isIso_iff_isOpenImmersion_and_surjective m).2 ⟨inferInstance, inferInstance⟩

/-- In a pushout square whose upper map is a thickening and whose left map is affine, the map
out of the affine target is again a thickening. -/
private lemma isThickening_inr_of_isPushout
    (H : ∀ (Z Z' : Scheme.{u}) (k : Z ⟶ Z'), IsThickening k → IsAffine Z → IsAffine Z')
    {X X' Y P : Scheme.{u}} {i : X ⟶ X'} {f : X ⟶ Y} {a : X' ⟶ P} {b : Y ⟶ P}
    (h : IsPushout i f a b) (hi : IsThickening i) [IsAffineHom f] : IsThickening b := by
  have := h.hasPushout
  have hb := Stacks.Pushout.pushout_inr_isThickening H i f hi
  have he : b = pushout.inr i f ≫ h.isoPushout.inv := h.inr_isoPushout_inv.symm
  rw [he]
  have : _root_.AlgebraicGeometry.IsClosedImmersion (pushout.inr i f) := hb.1
  exact ⟨inferInstance, (ConcreteCategory.bijective_of_isIso h.isoPushout.inv.base).2.comp hb.2⟩

/-- A morphism of étale schemes over `S` that becomes an isomorphism after restriction along a
surjective closed immersion `S₀ ⟶ S` is itself an isomorphism. -/
private lemma isIso_of_pullback_isIso_of_etale
    {S S₀ : Scheme.{u}} (i : S₀ ⟶ S) [_root_.AlgebraicGeometry.IsClosedImmersion i]
    (hi : Function.Surjective i.base) {X Y : Over S} (f : X ⟶ Y)
    [Etale X.hom] [Etale Y.hom] (h : IsIso ((Over.pullback i).map f)) : IsIso f := by
  let f₀ := (Over.pullback i).map f
  let g₀ := inv f₀
  have hg : ∃ g : Y ⟶ X, (Over.pullback i).map g = g₀ :=
    (Stacks.Etale.bijective_pullbackHom_of_etale i hi X Y).2 g₀
  let g := Classical.choose hg
  have hbg : (Over.pullback i).map g = g₀ := Classical.choose_spec hg
  have hgf : g ≫ f = 𝟙 Y := by
    apply (Stacks.Etale.bijective_pullbackHom_of_etale i hi Y Y).1
    simp [f₀, g₀, hbg]
  have hfg : f ≫ g = 𝟙 X := by
    apply (Stacks.Etale.bijective_pullbackHom_of_etale i hi X X).1
    simp [f₀, g₀, hbg]
  exact ⟨⟨g, hfg, hgf⟩⟩

/-- A scheme carrying a surjective closed immersion from a scheme of bounded size and locally of
finite type over a target of bounded size again has bounded size. -/
private lemma size_lt_of_surjective_closedImmersion_of_locallyOfFiniteType
    {Z W P : Scheme.{u}} (j : Z ⟶ W) (v : W ⟶ P)
    [_root_.AlgebraicGeometry.IsClosedImmersion j] (hj : Function.Surjective j)
    [LocallyOfFiniteType v] {κ : Cardinal.{u}} (hZ : Z.size < κ) (hP : P.size < κ) :
    W.size < κ := by
  have hAffinePreimage (V : W.affineOpens) : IsAffine ((j ⁻¹ᵁ V.1 : Z.Opens) : Scheme.{u}) := by
    let f := j ∣_ V.1
    have hf : _root_.AlgebraicGeometry.IsClosedImmersion f := by infer_instance
    let := hf
    exact isAffine_of_isAffineHom f
  let φ : W.affineOpens → Z.affineOpens := fun V => ⟨j ⁻¹ᵁ V.1, hAffinePreimage V⟩
  have hφ : Function.Injective φ := by
    intro V₁ V₂ h
    apply Subtype.ext
    apply TopologicalSpace.Opens.ext
    apply Set.ext
    intro x
    obtain ⟨z, rfl⟩ := hj x
    have heq := congrArg Subtype.val h
    have hmem := Iff.of_eq (congrArg (fun U : Z.Opens => z ∈ U) heq)
    change (j z ∈ V₁.1) ↔ (j z ∈ V₂.1) at hmem
    exact hmem
  let c := max Z.size P.size
  have hc₀ : Cardinal.aleph0 ≤ c := (Scheme.aleph0_le_size Z).trans (le_max_left _ _)
  have hc₁ : Cardinal.mk W.affineOpens ≤ c :=
    (Cardinal.mk_le_of_injective hφ).trans
      ((Scheme.mk_affineOpens_le_size Z).trans (le_max_left _ _))
  have hc₂ : ∀ V : W.affineOpens, Cardinal.mk (Γ(W, V.1)) ≤ c := by
    intro V
    rw [← Scheme.mk_sections_coe_opens W V.1]
    let : IsAffine (↑V.1 : Scheme.{u}) := V.2
    have hV : (↑V.1 : Scheme.{u}).size ≤ P.size :=
      Scheme.size_le_of_locallyOfFiniteType (V.1.ι ≫ v)
    exact (Scheme.mk_sections_le_size (↑V.1 : Scheme.{u})
      ⟨⊤, isAffineOpen_top _⟩).trans (hV.trans (le_max_right _ _))
  have hsize : W.size ≤ c := Scheme.size_le_of_bounds hc₀ hc₁ hc₂
  exact hsize.trans_lt (max_lt hZ hP)

/-- Gluing a cartesian family over the span `X' ⟵ X ⟶ Y` of étale schemes produces an étale
scheme over the pushout whose two restrictions recover the family. -/
private lemma exists_glued_of_pullbacks
    (h07RX : ∀ {Z Z' W : Scheme.{u}} (k : Z ⟶ Z') (g : Z ⟶ W) (hk : IsThickening k)
      [IsAffineHom g] [HasPushout k g] (T : Stacks.Pushout.gluingData k g),
      Etale ((Stacks.Pushout.gluingFunctor k g hk).obj T).hom ↔
        (Etale T.obj.left.hom ∧ Etale T.obj.right.hom))
    {X X' Y E₀ E₁ E₂ : Scheme.{u}} {iS : X ⟶ X'} {fS : X ⟶ Y}
    (hi : IsThickening iS) [IsAffineHom fS] [HasPushout iS fS]
    {iE : E₀ ⟶ E₁} {fE : E₀ ⟶ E₂} {p₀ : E₀ ⟶ X} {p₁ : E₁ ⟶ X'} {p₂ : E₂ ⟶ Y}
    (hEtale₁ : Etale p₁) (hEtale₂ : Etale p₂)
    (hcart₁ : IsPullback iE p₀ p₁ iS) (hcart₂ : IsPullback fE p₀ p₂ fS) :
    ∃ (W : Scheme.{u}) (w : W ⟶ pushout iS fS) (u₁ : E₁ ⟶ W) (u₂ : E₂ ⟶ W),
      Etale w ∧ IsPushout iE fE u₁ u₂ ∧
      u₁ ≫ w = p₁ ≫ pushout.inl iS fS ∧ u₂ ≫ w = p₂ ≫ pushout.inr iS fS := by
  let rightRestriction : (Over.pullback fS).obj (Over.mk p₂) ≅ Over.mk p₀ :=
    Over.isoMk hcart₂.isoPullback.symm (by exact hcart₂.isoPullback_inv_snd)
  let leftRestriction : (Over.pullback iS).obj (Over.mk p₁) ≅ Over.mk p₀ :=
    Over.isoMk hcart₁.isoPullback.symm (by exact hcart₁.isoPullback_inv_snd)
  let TglueComma : Comma (Over.pullback fS) (Over.pullback iS) :=
    ⟨Over.mk p₂, Over.mk p₁, (rightRestriction ≪≫ leftRestriction.symm).hom⟩
  have hTglueIso : IsIso TglueComma.hom := by
    dsimp [TglueComma]
    infer_instance
  let Tglue : Stacks.Pushout.gluingData iS fS := ⟨TglueComma, hTglueIso⟩
  let := Tglue.property
  let W := (Stacks.Pushout.gluingFunctor iS fS hi).obj Tglue
  have hGluedEtale : Etale W.hom := (h07RX iS fS hi Tglue).2 ⟨hEtale₂, hEtale₁⟩
  obtain ⟨glueInY, glueInX, hGluedPushout, hGlueY, hGlueX⟩ :=
    Stacks.Pushout.gluingFunctor_obj_isPushout iS fS hi Tglue
  have hcompat : hcart₁.isoPullback.hom ≫ (inv Tglue.obj.hom).left =
      hcart₂.isoPullback.hom := by
    have hTglueHom : Tglue.obj.hom = rightRestriction.hom ≫ leftRestriction.inv := rfl
    have hTglueInv : inv Tglue.obj.hom = leftRestriction.hom ≫ rightRestriction.inv := by
      apply (IsIso.eq_inv_of_hom_inv_id _).symm
      rw [hTglueHom]
      calc
        (rightRestriction.hom ≫ leftRestriction.inv) ≫
            leftRestriction.hom ≫ rightRestriction.inv =
            (rightRestriction.hom ≫ (leftRestriction.inv ≫ leftRestriction.hom)) ≫
              rightRestriction.inv := by cat_disch
        _ = (rightRestriction.hom ≫ 𝟙 _) ≫ rightRestriction.inv := by rw [Iso.inv_hom_id]
        _ = 𝟙 _ := by simp
    have hLeftInv : (inv Tglue.obj.hom).left =
        leftRestriction.hom.left ≫ rightRestriction.inv.left :=
      congrArg (fun m ↦ m.left) hTglueInv
    rw [hLeftInv]
    simp [leftRestriction, rightRestriction, Over.isoMk]
  have hsource : hcart₁.isoPullback.hom ≫
      Stacks.Pushout.gluingSourceMap iS fS Tglue = fE := by
    show hcart₁.isoPullback.hom ≫
      (inv Tglue.obj.hom).left ≫ pullback.fst Tglue.obj.left.hom fS = fE
    rw [← Category.assoc, hcompat]
    exact hcart₂.isoPullback_hom_fst
  have hglue : IsPushout iE fE glueInX glueInY := by
    refine hGluedPushout.flip.of_iso hcart₁.isoPullback.symm
      (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · show pullback.fst Tglue.obj.right.hom iS ≫ 𝟙 _ = hcart₁.isoPullback.inv ≫ iE
      rw [Category.comp_id]
      exact hcart₁.isoPullback_inv_fst.symm
    · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
      apply (cancel_epi hcart₁.isoPullback.hom).mp
      simpa using hsource
    · simp
    · simp
  exact ⟨W.left, W.hom, glueInX, glueInY, hGluedEtale, hglue, hGlueX, hGlueY⟩

/-- A cartesian family of étale schemes over the span `X' ⟵ X ⟶ Y`, equipped with a compatible
family of maps to a scheme étale over the pushout, is itself a pushout square. -/
private lemma isPushout_of_etale_pullbacks
    (H : ∀ (Z Z' : Scheme.{u}) (k : Z ⟶ Z'), IsThickening k → IsAffine Z → IsAffine Z')
    (h07RX : ∀ {Z Z' W : Scheme.{u}} (k : Z ⟶ Z') (g : Z ⟶ W) (hk : IsThickening k)
      [IsAffineHom g] [HasPushout k g] (T : Stacks.Pushout.gluingData k g),
      Etale ((Stacks.Pushout.gluingFunctor k g hk).obj T).hom ↔
        (Etale T.obj.left.hom ∧ Etale T.obj.right.hom))
    {X X' Y P U E₀ E₁ E₂ : Scheme.{u}} {iS : X ⟶ X'} {fS : X ⟶ Y}
    {aS : X' ⟶ P} {bS : Y ⟶ P} (hi : IsThickening iS) [IsAffineHom fS]
    (hP : IsPushout iS fS aS bS) {vS : U ⟶ P} (hv : Etale vS)
    {iE : E₀ ⟶ E₁} {fE : E₀ ⟶ E₂} {p₀ : E₀ ⟶ X} {p₁ : E₁ ⟶ X'} {p₂ : E₂ ⟶ Y}
    {q₀ : E₀ ⟶ U} {q₁ : E₁ ⟶ U} {q₂ : E₂ ⟶ U}
    (hsq₁ : IsPullback p₁ q₁ aS vS) (hsq₂ : IsPullback p₂ q₂ bS vS)
    (hcart₁ : IsPullback iE p₀ p₁ iS) (hcart₂ : IsPullback fE p₀ p₂ fS)
    (hqNat₁ : iE ≫ q₁ = q₀) (hqNat₂ : fE ≫ q₂ = q₀) :
    IsPushout iE fE q₁ q₂ := by
  have := hP.hasPushout
  let isoP := hP.isoPushout
  let vP := vS ≫ isoP.hom
  have hEtale₁ : Etale p₁ := MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq₁.flip hv
  have hEtale₂ : Etale p₂ := MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq₂.flip hv
  obtain ⟨W, w, u₁, u₂, hWEtale, hglue, hw₁, hw₂⟩ :=
    exists_glued_of_pullbacks h07RX hi hEtale₁ hEtale₂ hcart₁ hcart₂
  have hsq₁P : p₁ ≫ pushout.inl iS fS = q₁ ≫ vP := by
    rw [← hP.inl_isoPushout_hom, ← Category.assoc, hsq₁.w, Category.assoc]
  have hsq₂P : p₂ ≫ pushout.inr iS fS = q₂ ≫ vP := by
    rw [← hP.inr_isoPushout_hom, ← Category.assoc, hsq₂.w, Category.assoc]
  have hiE := Stacks.Thickenings.isThickening_of_isPullback hcart₁ hi
  have hAffineFE : IsAffineHom fE :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hcart₂.flip inferInstance
  have hj := isThickening_inr_of_isPushout (f := fE) H hglue hiE
  let m := hglue.desc q₁ q₂ (hqNat₁.trans hqNat₂.symm)
  have hm₁ : u₁ ≫ m = q₁ := hglue.inl_desc _ _ _
  have hm₂ : u₂ ≫ m = q₂ := hglue.inr_desc _ _ _
  have hm : m ≫ vP = w := by
    apply hglue.hom_ext
    · rw [← Category.assoc, hm₁]
      exact hsq₁P.symm.trans hw₁.symm
    · rw [← Category.assoc, hm₂]
      exact hsq₂P.symm.trans hw₂.symm
  have : Etale vP := by
    have : MorphismProperty.RespectsIso (@Etale : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    exact MorphismProperty.RespectsIso.postcomp (P := @Etale.{u}) isoP.hom vS hv
  have : Etale (m ≫ vP) := hm.symm ▸ hWEtale
  have : Etale m := Etale.of_comp m vP
  have hq₂ : IsThickening q₂ :=
    Stacks.Thickenings.isThickening_of_isPullback hsq₂.flip
      (isThickening_inr_of_isPushout H hP hi)
  have : IsIso m := isIso_of_etale_of_thickening_comp u₂ m hj (hm₂.symm ▸ hq₂)
  exact hglue.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (asIso m)
    (by simp) (by simp) (by simpa using hm₁) (by simpa using hm₂)

/-- A cartesian family of separated étale schemes over the span `X' ⟵ X ⟶ Y` descends to a
scheme étale over the pushout, with cartesian comparison squares. -/
private lemma exists_etale_descent_of_isPushout
    (H : ∀ (Z Z' : Scheme.{u}) (k : Z ⟶ Z'), IsThickening k → IsAffine Z → IsAffine Z')
    (h07RX : ∀ {Z Z' W : Scheme.{u}} (k : Z ⟶ Z') (g : Z ⟶ W) (hk : IsThickening k)
      [IsAffineHom g] [HasPushout k g] (T : Stacks.Pushout.gluingData k g),
      Etale ((Stacks.Pushout.gluingFunctor k g hk).obj T).hom ↔
        (Etale T.obj.left.hom ∧ Etale T.obj.right.hom))
    {X X' Y P E₀ E₁ E₂ : Scheme.{u}} {iS : X ⟶ X'} {fS : X ⟶ Y}
    {aS : X' ⟶ P} {bS : Y ⟶ P} (hi : IsThickening iS) [IsAffineHom fS]
    (hP : IsPushout iS fS aS bS)
    {iE : E₀ ⟶ E₁} {fE : E₀ ⟶ E₂} {p₀ : E₀ ⟶ X} {p₁ : E₁ ⟶ X'} {p₂ : E₂ ⟶ Y}
    (hEtale₁ : Etale p₁) (hEtale₂ : Etale p₂)
    (hcart₁ : IsPullback iE p₀ p₁ iS) (hcart₂ : IsPullback fE p₀ p₂ fS)
    {κ : Cardinal.{u}} (hE₂ : E₂.size < κ) (hPsize : P.size < κ) :
    ∃ (W : Scheme.{u}) (vS : W ⟶ P) (u₁ : E₁ ⟶ W) (u₂ : E₂ ⟶ W),
      W.size < κ ∧ Etale vS ∧ iE ≫ u₁ = fE ≫ u₂ ∧
      IsPullback p₁ u₁ aS vS ∧ IsPullback p₂ u₂ bS vS := by
  have := hP.hasPushout
  let isoP := hP.isoPushout
  obtain ⟨W, w, u₁, u₂, hWEtale, hglue, hw₁, hw₂⟩ :=
    exists_glued_of_pullbacks h07RX hi hEtale₁ hEtale₂ hcart₁ hcart₂
  let vS := w ≫ isoP.inv
  have hvEtale : Etale vS := by
    have : MorphismProperty.RespectsIso (@Etale : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    exact MorphismProperty.RespectsIso.postcomp (P := @Etale.{u}) isoP.inv w hWEtale
  have hu₁ : u₁ ≫ vS = p₁ ≫ aS := by
    show u₁ ≫ w ≫ isoP.inv = _
    rw [← Category.assoc, hw₁, Category.assoc, hP.inl_isoPushout_inv]
  have hu₂ : u₂ ≫ vS = p₂ ≫ bS := by
    show u₂ ≫ w ≫ isoP.inv = _
    rw [← Category.assoc, hw₂, Category.assoc, hP.inr_isoPushout_inv]
  have hAffineFE : IsAffineHom fE :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hcart₂.flip inferInstance
  have hThickU₂ := isThickening_inr_of_isPushout (f := fE) H hglue
    (Stacks.Thickenings.isThickening_of_isPullback hcart₁ hi)
  have : _root_.AlgebraicGeometry.IsClosedImmersion u₂ := hThickU₂.1
  have : Etale vS := hvEtale
  have hWSize : W.size < κ :=
    size_lt_of_surjective_closedImmersion_of_locallyOfFiniteType u₂ vS hThickU₂.2 hE₂ hPsize
  have hThickbS : IsThickening bS := isThickening_inr_of_isPushout H hP hi
  have hPB₂ : IsPullback p₂ u₂ bS vS := by
    let α : E₂ ⟶ pullback bS vS := pullback.lift p₂ u₂ (hu₂.symm)
    have hαFst : α ≫ pullback.fst bS vS = p₂ := pullback.lift_fst _ _ _
    have hαSnd : α ≫ pullback.snd bS vS = u₂ := pullback.lift_snd _ _ _
    have hαEtale : Etale α := by
      have : Etale (α ≫ pullback.fst bS vS) := hαFst ▸ hEtale₂
      exact Etale.of_comp α (pullback.fst bS vS)
    have : _root_.AlgebraicGeometry.IsClosedImmersion (pullback.snd bS vS) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback bS vS) hThickbS.1
    have hαClosed : _root_.AlgebraicGeometry.IsClosedImmersion α := by
      have : _root_.AlgebraicGeometry.IsClosedImmersion (α ≫ pullback.snd bS vS) :=
        hαSnd ▸ hThickU₂.1
      exact IsClosedImmersion.of_comp_isClosedImmersion α (pullback.snd bS vS)
    have hαSurj : Function.Surjective α.base := by
      intro z
      obtain ⟨x, hx⟩ := hThickU₂.2 ((pullback.snd bS vS).base z)
      refine ⟨x, ?_⟩
      apply (IsClosedImmersion.isClosedEmbedding (pullback.snd bS vS)).injective
      show (α ≫ pullback.snd bS vS).base x = (pullback.snd bS vS).base z
      rw [hαSnd]
      exact hx
    have : Etale α := hαEtale
    have : Flat α := inferInstance
    have : Mono α := inferInstance
    have : Surjective α := ⟨hαSurj⟩
    have : QuasiCompact α := inferInstance
    have : IsIso α := AlgebraicGeometry.Flat.isIso_of_surjective_of_mono α
    exact IsPullback.of_iso_pullback ⟨hu₂.symm⟩ (asIso α) hαFst hαSnd
  have hsq₀ : IsPullback p₀ (iE ≫ u₁) (iS ≫ aS) vS := by
    rw [hglue.w, hP.w]
    exact hcart₂.flip.paste_vert hPB₂
  have hPB₁ : IsPullback p₁ u₁ aS vS := by
    let α : E₁ ⟶ pullback aS vS := pullback.lift p₁ u₁ hu₁.symm
    have hαFst : α ≫ pullback.fst aS vS = p₁ := pullback.lift_fst _ _ _
    have hαSnd : α ≫ pullback.snd aS vS = u₁ := pullback.lift_snd _ _ _
    have hTarget : IsPullback (pullback.fst aS vS) (pullback.snd aS vS) aS vS :=
      IsPullback.of_hasPullback _ _
    have : Etale (pullback.fst aS vS) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback hTarget.flip hvEtale
    have hRestrict : IsIso ((Over.pullback iS).map
        (Over.homMk α hαFst : Over.mk p₁ ⟶ Over.mk (pullback.fst aS vS))) := by
      have hNested : IsPullback
          (pullback.fst (pullback.fst aS vS) iS) (pullback.snd (pullback.fst aS vS) iS)
          (pullback.fst aS vS) iS := IsPullback.of_hasPullback _ _
      have hBig : IsPullback (pullback.snd (pullback.fst aS vS) iS)
          (pullback.fst (pullback.fst aS vS) iS ≫ pullback.snd aS vS) (iS ≫ aS) vS :=
        (hNested.paste_horiz hTarget.flip).flip
      have hBeta : ((Over.pullback iS).map
          (Over.homMk α hαFst : Over.mk p₁ ⟶ Over.mk (pullback.fst aS vS))).left =
          hcart₁.isoPullback.inv ≫ hsq₀.isoPullback.hom ≫ hBig.isoPullback.inv := by
        apply hBig.hom_ext
        · rw [Category.assoc, Category.assoc, hBig.isoPullback_inv_fst,
            hsq₀.isoPullback_hom_fst, hcart₁.isoPullback_inv_snd]
          exact pullback.lift_snd _ _ _
        · rw [Category.assoc, Category.assoc, hBig.isoPullback_inv_snd,
            hsq₀.isoPullback_hom_snd]
          conv_rhs => rw [← Category.assoc, hcart₁.isoPullback_inv_fst]
          have hlf : ((Over.pullback iS).map
              (Over.homMk α hαFst : Over.mk p₁ ⟶ Over.mk (pullback.fst aS vS))).left ≫
              pullback.fst (pullback.fst aS vS) iS = pullback.fst p₁ iS ≫ α :=
            pullback.lift_fst _ _ _
          rw [← Category.assoc, hlf, Category.assoc, hαSnd]
      have hUnderlying : IsIso ((Over.pullback iS).map
          (Over.homMk α hαFst : Over.mk p₁ ⟶ Over.mk (pullback.fst aS vS))).left := by
        rw [hBeta]; infer_instance
      have : IsIso ((Over.forget X).map ((Over.pullback iS).map
          (Over.homMk α hαFst : Over.mk p₁ ⟶ Over.mk (pullback.fst aS vS)))) := hUnderlying
      exact isIso_of_reflects_iso _ (Over.forget X)
    have : _root_.AlgebraicGeometry.IsClosedImmersion iS := hi.1
    have hEtalePiece₁ : Etale (Over.mk p₁).hom := hEtale₁
    have hEtalePiece₂ : Etale (Over.mk (pullback.fst aS vS)).hom :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback hTarget.flip hvEtale
    have hOverIso : IsIso (Over.homMk α hαFst : Over.mk p₁ ⟶ Over.mk (pullback.fst aS vS)) :=
      isIso_of_pullback_isIso_of_etale iS hi.2 _ hRestrict
    have : IsIso α := by
      have := Functor.map_isIso (Over.forget X')
        (Over.homMk α hαFst : Over.mk p₁ ⟶ Over.mk (pullback.fst aS vS))
      simpa using this
    exact IsPullback.of_iso_pullback ⟨hu₁.symm⟩ (asIso α) hαFst hαSnd
  exact ⟨W, vS, u₁, u₂, hWSize, hvEtale, hglue.w, hPB₁, hPB₂⟩

/-! ### The span diagram on a `u`-small index category -/

/-- A `u`-small model of the walking span, usable as an index category at the universe level of
the big fppf site. -/
private abbrev SpanIndex : Type u := ULiftHom.{u} (AsSmall.{u} WalkingSpan)

/-- The walking span is equivalent to its `u`-small model. -/
private abbrev spanIndexEquiv : WalkingSpan ≌ SpanIndex.{u} :=
  let e₁ : WalkingSpan ≌ AsSmall.{u} WalkingSpan := AsSmall.equiv
  let e₂ : AsSmall.{u} WalkingSpan ≌ SpanIndex.{u} := ULiftHom.equiv
  e₁.trans e₂

/-- A span of schemes over `S`, read as a diagram on the `u`-small index category. -/
private abbrev spanDiagram (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' Y : BigFppfOver B S hS} (i : X ⟶ X') (f : X ⟶ Y) :
    SpanIndex.{u} ⥤ BigFppfOver B S hS :=
  spanIndexEquiv.{u}.inverse ⋙ span i f

/-- A commuting square on a span, read as a cocone on the `u`-small span diagram. -/
private abbrev spanCocone (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' Y Y' : BigFppfOver B S hS} (i : X ⟶ X') (f : X ⟶ Y) (a : X' ⟶ Y') (b : Y ⟶ Y')
    (w : i ≫ a = f ≫ b) : Cocone (spanDiagram B S hS i f) :=
  (PushoutCocone.mk a b w).whisker spanIndexEquiv.{u}.inverse

/-- The image of a pushout cocone is a colimit cocone iff the pushout cocone on the images is. -/
private noncomputable def isColimit_pushoutCocone_map_equiv.{v₂, u₂}
    {C : Type*} {D : Type u₂} [Category.{u} C] [Category.{v₂} D] (F : C ⥤ D) {X X' Y Y' : C}
    (i : X ⟶ X') (f : X ⟶ Y) (a : X' ⟶ Y') (b : Y ⟶ Y') (w : i ≫ a = f ≫ b)
    (w' : F.map i ≫ F.map a = F.map f ≫ F.map b) :
    IsColimit (F.mapCocone (PushoutCocone.mk a b w)) ≃
      IsColimit (PushoutCocone.mk (F.map a) (F.map b) w') := by
  let c₀ : PushoutCocone i f := PushoutCocone.mk a b w
  let cS : PushoutCocone (F.map i) (F.map f) := PushoutCocone.mk (F.map a) (F.map b) w'
  let α := spanCompIso F i f
  let c' := (Cocone.precompose α.inv).obj (F.mapCocone c₀)
  have hpt : c'.pt = cS.pt := by
    dsimp [c', c₀]
    rfl
  have hptHom : (eqToIso hpt).hom = 𝟙 c'.pt := by rfl
  have hw : c' ≅ cS :=
    Cocone.ext (c := c') (c' := cS) (eqToIso hpt) (by
      intro j
      rw [hptHom]
      rcases j with _ | _ | _
      · dsimp [c', cS, c₀, α, spanCompIso]
        simp only [Category.id_comp]
        exact (Category.comp_id _).trans (F.map_comp i a)
      all_goals
        dsimp [c', cS, c₀, α, spanCompIso]
        simp only [Category.id_comp]
        exact Category.comp_id (F.map _))
  exact IsColimit.equivOfNatIsoOfIso α (F.mapCocone c₀) cS hw

/-- A pushout square of the underlying schemes is a colimit of the `u`-small span diagram. -/
private noncomputable def isColimit_mapCocone_spanCocone
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' Y Y' : BigFppfOver B S hS}
    (i : X ⟶ X') (f : X ⟶ Y) (a : X' ⟶ Y') (b : Y ⟶ Y') (w : i ≫ a = f ≫ b)
    (hPushout : IsPushout ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map f) ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b)) :
    IsColimit ((BigFppfOver.toScheme B S hS).mapCocone (spanCocone B S hS i f a b w)) := by
  let T := BigFppfOver.toScheme B S hS
  let iS := T.map i
  let fS := T.map f
  let aS := T.map a
  let bS := T.map b
  let I := SpanIndex.{u}
  let e₁ : WalkingSpan ≌ AsSmall.{u} WalkingSpan := AsSmall.equiv
  let e₂ : AsSmall.{u} WalkingSpan ≌ I := ULiftHom.equiv
  let e : WalkingSpan ≌ I := e₁.trans e₂
  let D : I ⥤ BigFppfOver B S hS := e.inverse ⋙ span i f
  let c₀ : PushoutCocone i f := PushoutCocone.mk a b w
  let c : Cocone D := c₀.whisker e.inverse
  change IsColimit (T.mapCocone c)
  have hc : IsColimit (T.mapCocone c₀) :=
    (isColimit_pushoutCocone_map_equiv T i f a b w hPushout.w).symm hPushout.isColimit
  change IsColimit (Cocone.whisker e.inverse (T.mapCocone c₀))
  exact hc.whiskerEquivalence e.symm

/-- Every point of the pushout is hit by one of the two legs of the span. -/
private lemma cover_spanCocone
    (H : ∀ (Z Z' : Scheme.{u}) (k : Z ⟶ Z'), IsThickening k → IsAffine Z → IsAffine Z')
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' Y Y' : BigFppfOver B S hS}
    (i : X ⟶ X') (f : X ⟶ Y) (a : X' ⟶ Y') (b : Y ⟶ Y') (w : i ≫ a = f ≫ b)
    (hi : IsThickening ((BigFppfOver.toScheme B S hS).map i))
    [IsAffineHom ((BigFppfOver.toScheme B S hS).map f)]
    (hPushout : IsPushout ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map f) ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b)) :
    ∀ x : (BigFppfOver.toScheme B S hS).obj (spanCocone B S hS i f a b w).pt,
      ∃ (j : SpanIndex.{u})
        (y : (BigFppfOver.toScheme B S hS).obj ((spanDiagram B S hS i f).obj j)),
        (BigFppfOver.toScheme B S hS).map ((spanCocone B S hS i f a b w).ι.app j) y = x := by
  let T := BigFppfOver.toScheme B S hS
  let iS := T.map i
  let fS := T.map f
  let aS := T.map a
  let bS := T.map b
  let I := SpanIndex.{u}
  let e₁ : WalkingSpan ≌ AsSmall.{u} WalkingSpan := AsSmall.equiv
  let e₂ : AsSmall.{u} WalkingSpan ≌ I := ULiftHom.equiv
  let e : WalkingSpan ≌ I := e₁.trans e₂
  let D : I ⥤ BigFppfOver B S hS := e.inverse ⋙ span i f
  let c₀ : PushoutCocone i f := PushoutCocone.mk a b w
  let c : Cocone D := c₀.whisker e.inverse
  have : HasPushout iS fS := hPushout.hasPushout
  have hAffineF : IsAffineHom fS := by
    show IsAffineHom (T.map f)
    infer_instance
  let := hAffineF
  show ∀ x : T.obj c.pt, ∃ (j : I) (y : T.obj (D.obj j)), T.map (c.ι.app j) y = x
  intro x
  let isoP := hPushout.isoPushout
  have hsurj : Function.Surjective (pushout.inr iS fS) :=
    (Stacks.Pushout.pushout_inr_isThickening H iS fS hi).2
  obtain ⟨y, hy⟩ := hsurj (isoP.hom x)
  refine ⟨e.functor.obj WalkingSpan.right, y, ?_⟩
  have hinj : Function.Injective isoP.hom := by
    intro x₁ x₂ hx
    have hx' := congrArg isoP.inv hx
    simpa using hx'
  have hleg : T.map (c.ι.app (e.functor.obj WalkingSpan.right)) = bS := by
    have hι : c.ι.app (e.functor.obj WalkingSpan.right) = b := by
      let j := e.inverse.obj (e.functor.obj WalkingSpan.right)
      have hj' : j = WalkingSpan.right := by
        show (e₁.inverse.obj (e₁.functor.obj WalkingSpan.right)) = _
        simp [e₁]
      show c₀.ι.app j = b
      subst j
      rfl
    rw [hι]
    rfl
  apply hinj
  calc
    isoP.hom (T.map (c.ι.app (e.functor.obj WalkingSpan.right)) y) =
        (bS ≫ isoP.hom) y := by rw [hleg]; rfl
    _ = (pushout.inr iS fS) y := by rw [hPushout.inr_isoPushout_hom]
    _ = isoP.hom x := hy

/-- Naturality of `unitInv` for an equivalence out of the walking span, after applying a functor. -/
private lemma map_inverse_functor_unitInv_comp
    {C : Type*} [Category C] {I : Type*} [Category I] (e : WalkingSpan ≌ I)
    (F : WalkingSpan ⥤ C) {x y : WalkingSpan} (g : x ⟶ y) :
    F.map (e.inverse.map (e.functor.map g) ≫ e.unitInv.app y) =
      F.map (e.unitInv.app x) ≫ F.map g := by
  rw [← F.map_comp]
  exact congrArg F.map (e.unitInv.naturality g)

/-- Applying a functor to the legs of a cocone, compared along the unit of an equivalence. -/
private lemma map_unitInv_comp_map_ι
    {J C D I : Type*} [Category J] [Category C] [Category D] [Category I] (T : C ⥤ D)
    {F : J ⥤ C} (c : Cocone F) (e : J ≌ I) (x : J) :
    T.map (F.map (e.unitInv.app x)) ≫ T.map (c.ι.app x) =
      T.map (c.ι.app (e.inverse.obj (e.functor.obj x))) := by
  rw [← T.map_comp]
  exact congrArg T.map (c.w _)

/-- Étale base change along a map to the pushout preserves the colimit of the span. -/
private noncomputable def etaleColimit_spanCocone
    (H : ∀ (Z Z' : Scheme.{u}) (k : Z ⟶ Z'), IsThickening k → IsAffine Z → IsAffine Z')
    (h07RX : ∀ {Z Z' W : Scheme.{u}} (k : Z ⟶ Z') (g : Z ⟶ W) (hk : IsThickening k)
      [IsAffineHom g] [HasPushout k g] (T : Stacks.Pushout.gluingData k g),
      Etale ((Stacks.Pushout.gluingFunctor k g hk).obj T).hom ↔
        (Etale T.obj.left.hom ∧ Etale T.obj.right.hom))
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' Y Y' : BigFppfOver B S hS}
    (i : X ⟶ X') (f : X ⟶ Y) (a : X' ⟶ Y') (b : Y ⟶ Y') (w : i ≫ a = f ≫ b)
    (hi : IsThickening ((BigFppfOver.toScheme B S hS).map i))
    [IsAffineHom ((BigFppfOver.toScheme B S hS).map f)]
    (hPushout : IsPushout ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map f) ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b)) :
    ∀ (U : BigFppfOver B S hS) (v : U ⟶ (spanCocone B S hS i f a b w).pt),
      Etale ((BigFppfOver.toScheme B S hS).map v) →
      ∀ (E : SpanIndex.{u} ⥤ BigFppfOver B S hS) (p : E ⟶ spanDiagram B S hS i f)
        (q : E ⟶ (Functor.const SpanIndex.{u}).obj U),
        (∀ j, IsPullback (p.app j) (q.app j)
          ((spanCocone B S hS i f a b w).ι.app j) v) →
        IsColimit ((BigFppfOver.toScheme B S hS).mapCocone ({ pt := U, ι := q } : Cocone E)) := by
  let T := BigFppfOver.toScheme B S hS
  let iS := T.map i
  let fS := T.map f
  let aS := T.map a
  let bS := T.map b
  let I := SpanIndex.{u}
  let e₁ : WalkingSpan ≌ AsSmall.{u} WalkingSpan := AsSmall.equiv
  let e₂ : AsSmall.{u} WalkingSpan ≌ I := ULiftHom.equiv
  let e : WalkingSpan ≌ I := e₁.trans e₂
  let D : I ⥤ BigFppfOver B S hS := e.inverse ⋙ span i f
  let c₀ : PushoutCocone i f := PushoutCocone.mk a b w
  let c : Cocone D := c₀.whisker e.inverse
  have : HasPushout iS fS := hPushout.hasPushout
  have hAffineF : IsAffineHom fS := by
    change IsAffineHom (T.map f)
    infer_instance
  let := hAffineF
  change ∀ (U : BigFppfOver B S hS) (v : U ⟶ c.pt), Etale (T.map v) →
    ∀ (E : I ⥤ BigFppfOver B S hS) (p : E ⟶ D) (q : E ⟶ (Functor.const I).obj U),
      (∀ j, IsPullback (p.app j) (q.app j) (c.ι.app j) v) →
      IsColimit (T.mapCocone ({ pt := U, ι := q } : Cocone E))
  intro U v hv E p q hpull
  apply Classical.choice
  let j₀ := e.functor.obj WalkingSpan.zero
  let j₁ := e.functor.obj WalkingSpan.left
  let j₂ := e.functor.obj WalkingSpan.right
  let g₁ := e.functor.map WalkingSpan.Hom.fst
  let g₂ := e.functor.map WalkingSpan.Hom.snd
  let d₀ := T.mapIso ((span i f).mapIso (asIso (e.unitInv.app WalkingSpan.zero)))
  let d₁ := T.mapIso ((span i f).mapIso (asIso (e.unitInv.app WalkingSpan.left)))
  let d₂ := T.mapIso ((span i f).mapIso (asIso (e.unitInv.app WalkingSpan.right)))
  let p₀ := T.map (p.app j₀) ≫ d₀.hom
  let p₁ := T.map (p.app j₁) ≫ d₁.hom
  let p₂ := T.map (p.app j₂) ≫ d₂.hom
  let q₀ := T.map (q.app j₀)
  let q₁ := T.map (q.app j₁)
  let q₂ := T.map (q.app j₂)
  let vS : T.obj U ⟶ T.obj c.pt := T.map v
  let isoP := hPushout.isoPushout
  let vP := vS ≫ isoP.hom
  have hci₀ : d₀.hom ≫ iS ≫ aS = T.map (c.ι.app j₀) :=
    map_unitInv_comp_map_ι T c₀ e WalkingSpan.zero
  have hci₁ : d₁.hom ≫ aS = T.map (c.ι.app j₁) :=
    map_unitInv_comp_map_ι T c₀ e WalkingSpan.left
  have hci₂ : d₂.hom ≫ bS = T.map (c.ι.app j₂) :=
    map_unitInv_comp_map_ι T c₀ e WalkingSpan.right
  have hsq₀ : IsPullback p₀ q₀ (iS ≫ aS) vS := by
    refine ((hpull j₀).map T).of_iso (Iso.refl _) d₀ (Iso.refl _) (Iso.refl _)
      ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · exact hci₀.symm
    · change T.map v ≫ 𝟙 (T.obj c.pt) = 𝟙 (T.obj U) ≫ T.map v
      simp
  have hsq₁ : IsPullback p₁ q₁ aS vS := by
    refine ((hpull j₁).map T).of_iso (Iso.refl _) d₁ (Iso.refl _) (Iso.refl _)
      ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · exact hci₁.symm
    · change T.map v ≫ 𝟙 (T.obj c.pt) = 𝟙 (T.obj U) ≫ T.map v
      simp
  have hsq₂ : IsPullback p₂ q₂ bS vS := by
    refine ((hpull j₂).map T).of_iso (Iso.refl _) d₂ (Iso.refl _) (Iso.refl _)
      ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · exact hci₂.symm
    · change T.map v ≫ 𝟙 (T.obj c.pt) = 𝟙 (T.obj U) ≫ T.map v
      simp
  let iE := T.map (E.map g₁)
  let fE := T.map (E.map g₂)
  have hqNat₁ : iE ≫ q₁ = q₀ := by
    have h := q.naturality g₁
    change E.map g₁ ≫ q.app j₁ = q.app j₀ at h
    simpa [iE, q₀, q₁] using congrArg T.map h
  have hqNat₂ : fE ≫ q₂ = q₀ := by
    have h := q.naturality g₂
    change E.map g₂ ≫ q.app j₂ = q.app j₀ at h
    simpa [fE, q₀, q₂] using congrArg T.map h
  have hpNat₁ : iE ≫ p₁ = p₀ ≫ iS := by
    have hNat : T.map (E.map g₁) ≫ T.map (p.app j₁) =
        T.map (p.app j₀) ≫ T.map (D.map g₁) := by
      simpa only [← T.map_comp] using congrArg T.map (p.naturality g₁)
    have hDiagram : T.map (D.map g₁) ≫ d₁.hom = d₀.hom ≫ iS := by
      dsimp [D, g₁, d₀, d₁, iS]
      exact congrArg T.map (map_inverse_functor_unitInv_comp e (span i f) WalkingSpan.Hom.fst)
    calc
      iE ≫ p₁ = T.map (E.map g₁) ≫ T.map (p.app j₁) ≫ d₁.hom := by
        simp [iE, p₁]
      _ = T.map (p.app j₀) ≫ T.map (D.map g₁) ≫ d₁.hom := by
        simpa [Category.assoc] using congrArg (fun k ↦ k ≫ d₁.hom) hNat
      _ = T.map (p.app j₀) ≫ d₀.hom ≫ iS := by
        simpa [Category.assoc] using
          congrArg (fun k ↦ T.map (p.app j₀) ≫ k) hDiagram
      _ = p₀ ≫ iS := rfl
  have hpNat₂ : fE ≫ p₂ = p₀ ≫ fS := by
    have hNat : T.map (E.map g₂) ≫ T.map (p.app j₂) =
        T.map (p.app j₀) ≫ T.map (D.map g₂) := by
      simpa only [← T.map_comp] using congrArg T.map (p.naturality g₂)
    have hDiagram : T.map (D.map g₂) ≫ d₂.hom = d₀.hom ≫ fS := by
      dsimp [D, g₂, d₀, d₂, fS]
      exact congrArg T.map (map_inverse_functor_unitInv_comp e (span i f) WalkingSpan.Hom.snd)
    calc
      fE ≫ p₂ = T.map (E.map g₂) ≫ T.map (p.app j₂) ≫ d₂.hom := by
        simp [fE, p₂]
      _ = T.map (p.app j₀) ≫ T.map (D.map g₂) ≫ d₂.hom := by
        simpa [Category.assoc] using congrArg (fun k ↦ k ≫ d₂.hom) hNat
      _ = T.map (p.app j₀) ≫ d₀.hom ≫ fS := by
        simpa [Category.assoc] using
          congrArg (fun k ↦ T.map (p.app j₀) ≫ k) hDiagram
      _ = p₀ ≫ fS := rfl
  have hsq₀' : IsPullback p₀ q₀ (fS ≫ bS) vS := by
    rw [← hPushout.w]
    exact hsq₀
  have hcart₁ : IsPullback iE p₀ p₁ iS := by
    have h : IsPullback p₀ (iE ≫ q₁) (iS ≫ aS) vS := by
      rw [hqNat₁]
      exact hsq₀
    exact (IsPullback.of_bot h hpNat₁.symm hsq₁).flip
  have hcart₂ : IsPullback fE p₀ p₂ fS := by
    have h : IsPullback p₀ (fE ≫ q₂) (fS ≫ bS) vS := by
      rw [hqNat₂]
      exact hsq₀'
    exact (IsPullback.of_bot h hpNat₂.symm hsq₂).flip
  have hpush : IsPushout iE fE q₁ q₂ :=
    isPushout_of_etale_pullbacks H h07RX hi hPushout hv hsq₁ hsq₂ hcart₁ hcart₂
      hqNat₁ hqNat₂
  refine ⟨IsColimit.mk
    (fun s ↦ hpush.desc (s.ι.app j₁) (s.ι.app j₂)
      ((s.w g₁).trans (s.w g₂).symm)) ?_ ?_⟩
  · intro s j
    have hf₁ := hpush.inl_desc (s.ι.app j₁) (s.ι.app j₂)
      ((s.w g₁).trans (s.w g₂).symm)
    have hf₂ := hpush.inr_desc (s.ι.app j₁) (s.ι.app j₂)
      ((s.w g₁).trans (s.w g₂).symm)
    rcases j with ⟨_ | (_ | _)⟩
    · change q₀ ≫ _ = s.ι.app j₀
      rw [← hqNat₁, Category.assoc, hf₁]
      exact s.w g₁
    · exact hf₁
    · exact hf₂
  · intro s m' hm'
    apply hpush.hom_ext
    · exact (hm' j₁).trans (hpush.inl_desc _ _ _).symm
    · exact (hm' j₂).trans (hpush.inr_desc _ _ _).symm

/-- A cartesian family of separated étale schemes over the span descends to a scheme étale
over the pushout, with cartesian comparison squares. -/
private lemma etaleDescent_spanCocone
    (H : ∀ (Z Z' : Scheme.{u}) (k : Z ⟶ Z'), IsThickening k → IsAffine Z → IsAffine Z')
    (h07RX : ∀ {Z Z' W : Scheme.{u}} (k : Z ⟶ Z') (g : Z ⟶ W) (hk : IsThickening k)
      [IsAffineHom g] [HasPushout k g] (T : Stacks.Pushout.gluingData k g),
      Etale ((Stacks.Pushout.gluingFunctor k g hk).obj T).hom ↔
        (Etale T.obj.left.hom ∧ Etale T.obj.right.hom))
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' Y Y' : BigFppfOver B S hS}
    (i : X ⟶ X') (f : X ⟶ Y) (a : X' ⟶ Y') (b : Y ⟶ Y') (w : i ≫ a = f ≫ b)
    (hi : IsThickening ((BigFppfOver.toScheme B S hS).map i))
    [IsAffineHom ((BigFppfOver.toScheme B S hS).map f)]
    (hPushout : IsPushout ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map f) ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b)) :
    ∀ (E : SpanIndex.{u} ⥤ BigFppfOver B S hS) (p : E ⟶ spanDiagram B S hS i f),
      (∀ j, Etale ((BigFppfOver.toScheme B S hS).map (p.app j))) →
      (∀ j, _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map (p.app j))) →
      (∀ {j k : SpanIndex.{u}} (g : j ⟶ k),
        IsPullback (E.map g) (p.app j) (p.app k) ((spanDiagram B S hS i f).map g)) →
      ∃ (U : BigFppfOver B S hS) (v : U ⟶ (spanCocone B S hS i f a b w).pt)
        (q : E ⟶ (Functor.const SpanIndex.{u}).obj U),
        Etale ((BigFppfOver.toScheme B S hS).map v) ∧
        (∀ j, IsPullback (p.app j) (q.app j)
          ((spanCocone B S hS i f a b w).ι.app j) v) := by
  let T := BigFppfOver.toScheme B S hS
  let iS := T.map i
  let fS := T.map f
  let aS := T.map a
  let bS := T.map b
  let I := SpanIndex.{u}
  let e₁ : WalkingSpan ≌ AsSmall.{u} WalkingSpan := AsSmall.equiv
  let e₂ : AsSmall.{u} WalkingSpan ≌ I := ULiftHom.equiv
  let e : WalkingSpan ≌ I := e₁.trans e₂
  let D : I ⥤ BigFppfOver B S hS := e.inverse ⋙ span i f
  let c₀ : PushoutCocone i f := PushoutCocone.mk a b w
  let c : Cocone D := c₀.whisker e.inverse
  have : HasPushout iS fS := hPushout.hasPushout
  have hAffineF : IsAffineHom fS := by
    show IsAffineHom (T.map f)
    infer_instance
  let := hAffineF
  show ∀ (E : I ⥤ BigFppfOver B S hS) (p : E ⟶ D),
    (∀ j, Etale (T.map (p.app j))) →
    (∀ j, _root_.AlgebraicGeometry.IsSeparated (T.map (p.app j))) →
    (∀ {j k : I} (g : j ⟶ k), IsPullback (E.map g) (p.app j) (p.app k) (D.map g)) →
    ∃ (U : BigFppfOver B S hS) (v : U ⟶ c.pt) (q : E ⟶ (Functor.const I).obj U),
      Etale (T.map v) ∧ (∀ j, IsPullback (p.app j) (q.app j) (c.ι.app j) v)
  intro E p hp hsep hcart
  let j₀ := e.functor.obj WalkingSpan.zero
  let j₁ := e.functor.obj WalkingSpan.left
  let j₂ := e.functor.obj WalkingSpan.right
  let g₁ := e.functor.map WalkingSpan.Hom.fst
  let g₂ := e.functor.map WalkingSpan.Hom.snd
  let iE := T.map (E.map g₁)
  let fE := T.map (E.map g₂)
  let d₀ : T.obj (D.obj j₀) ≅ (T.obj ((span i f).obj WalkingSpan.zero)) :=
    T.mapIso ((span i f).mapIso (asIso (e.unitInv.app WalkingSpan.zero)))
  let d₁ : T.obj (D.obj j₁) ≅ (T.obj ((span i f).obj WalkingSpan.left)) :=
    T.mapIso ((span i f).mapIso (asIso (e.unitInv.app WalkingSpan.left)))
  let d₂ : T.obj (D.obj j₂) ≅ (T.obj ((span i f).obj WalkingSpan.right)) :=
    T.mapIso ((span i f).mapIso (asIso (e.unitInv.app WalkingSpan.right)))
  let p₀ := T.map (p.app j₀) ≫ d₀.hom
  let p₁ := T.map (p.app j₁) ≫ d₁.hom
  let p₂ := T.map (p.app j₂) ≫ d₂.hom
  have hpull₁ : IsPullback iE p₀ p₁ iS := by
    refine ((hcart g₁).map T).of_iso (Iso.refl _) (Iso.refl _) d₀ d₁ ?_ ?_ ?_ ?_
    · simp [iE]
    · simp [p₀, d₀, j₀]
    · simp [p₁, d₁, j₁]
    · dsimp [iS, d₀, d₁]
      rw [← T.map_comp, ← T.map_comp]
      dsimp [D, g₁]
      exact congrArg T.map (map_inverse_functor_unitInv_comp e (span i f) WalkingSpan.Hom.fst)
  have hpull₂ : IsPullback fE p₀ p₂ fS := by
    refine ((hcart g₂).map T).of_iso (Iso.refl _) (Iso.refl _) d₀ d₂ ?_ ?_ ?_ ?_
    · simp [fE]
    · simp [p₀, d₀, j₀]
    · simp [p₂, d₂, j₂]
    · dsimp [fS, d₀, d₂]
      rw [← T.map_comp, ← T.map_comp]
      dsimp [D, g₂]
      exact congrArg T.map (map_inverse_functor_unitInv_comp e (span i f) WalkingSpan.Hom.snd)
  have hEtale₁ : Etale p₁ := by
    have : MorphismProperty.RespectsIso (@Etale : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    dsimp [p₁]
    exact (MorphismProperty.cancel_right_of_respectsIso
      (P := @Etale) (T.map (p.app j₁)) d₁.hom).mpr (hp j₁)
  have hEtale₂ : Etale p₂ := by
    have : MorphismProperty.RespectsIso (@Etale : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    dsimp [p₂]
    exact (MorphismProperty.cancel_right_of_respectsIso
      (P := @Etale) (T.map (p.app j₂)) d₂.hom).mpr (hp j₂)
  obtain ⟨Wsch, vSch, u₁, u₂, hWSize, hVEtaleScheme, hOverlap, hPB₁, hPB₂⟩ :=
    exists_etale_descent_of_isPushout H h07RX hi hPushout hEtale₁ hEtale₂ hpull₁ hpull₂
      (κ := B.cutoff)
      (E.obj j₂).left.2
      (by
        show (T.obj c.pt).size < B.cutoff
        exact c.pt.left.2)
  let uObject : B.Schemes := ⟨Wsch, hWSize⟩
  let vBase : uObject ⟶ c.pt.left := B.inclusion.preimage vSch
  let U : BigFppfOver B S hS := Over.mk (vBase ≫ c.pt.hom)
  let v : U ⟶ c.pt := Over.homMk vBase (by rfl)
  have hVMap : T.map v = vSch := by
    show B.inclusion.map vBase = vSch
    exact B.inclusion.map_preimage _
  have hVEtale : Etale (T.map v) := by
    rw [hVMap]
    exact hVEtaleScheme
  have hGlueY'' : u₂ ≫ vSch = p₂ ≫ bS := hPB₂.w.symm
  have hGlueX'' : u₁ ≫ vSch = p₁ ≫ aS := hPB₁.w.symm
  have hUHom : B.inclusion.map U.hom =
      vSch ≫ B.inclusion.map c.pt.hom := by
    show B.inclusion.map (vBase ≫ c.pt.hom) = _
    rw [B.inclusion.map_comp]
    change B.inclusion.map vBase = vSch at hVMap
    rw [hVMap]
    rfl
  have haBase : aS ≫ B.inclusion.map c.pt.hom = B.inclusion.map X'.hom := by
    dsimp [aS]
    show B.inclusion.map a.left ≫ B.inclusion.map Y'.hom = _
    exact congrArg B.inclusion.map a.w
  have hbBase : bS ≫ B.inclusion.map c.pt.hom = B.inclusion.map Y.hom := by
    dsimp [bS]
    show B.inclusion.map b.left ≫ B.inclusion.map Y'.hom = _
    exact congrArg B.inclusion.map b.w
  have hpOver₁ : T.map (p.app j₁) ≫ B.inclusion.map (D.obj j₁).hom =
      B.inclusion.map (E.obj j₁).hom := by
    show B.inclusion.map (p.app j₁).left ≫
      B.inclusion.map (D.obj j₁).hom = B.inclusion.map (E.obj j₁).hom
    exact congrArg B.inclusion.map (p.app j₁).w
  have hpOver₂ : T.map (p.app j₂) ≫ B.inclusion.map (D.obj j₂).hom =
      B.inclusion.map (E.obj j₂).hom := by
    show B.inclusion.map (p.app j₂).left ≫
      B.inclusion.map (D.obj j₂).hom = B.inclusion.map (E.obj j₂).hom
    exact congrArg B.inclusion.map (p.app j₂).w
  let d₁Over := (span i f).mapIso (asIso (e.unitInv.app WalkingSpan.left))
  let d₂Over := (span i f).mapIso (asIso (e.unitInv.app WalkingSpan.right))
  have hd₁Base : d₁.hom ≫ B.inclusion.map X'.hom =
      B.inclusion.map (D.obj j₁).hom := by
    dsimp [d₁, d₁Over]
    show B.inclusion.map d₁Over.hom.left ≫ B.inclusion.map X'.hom =
      B.inclusion.map (D.obj j₁).hom
    exact congrArg B.inclusion.map d₁Over.hom.w
  have hd₂Base : d₂.hom ≫ B.inclusion.map Y.hom =
      B.inclusion.map (D.obj j₂).hom := by
    dsimp [d₂, d₂Over]
    show B.inclusion.map d₂Over.hom.left ≫ B.inclusion.map Y.hom =
      B.inclusion.map (D.obj j₂).hom
    exact congrArg B.inclusion.map d₂Over.hom.w
  let q₁Base : (E.obj j₁).left ⟶ U.left := B.inclusion.preimage
    (show B.inclusion.obj (E.obj j₁).left ⟶ B.inclusion.obj U.left from u₁)
  let q₂Base : (E.obj j₂).left ⟶ U.left := B.inclusion.preimage
    (show B.inclusion.obj (E.obj j₂).left ⟶ B.inclusion.obj U.left from u₂)
  have hq₁Over : q₁Base ≫ U.hom = (E.obj j₁).hom := by
    apply B.inclusion.map_injective
    show B.inclusion.map q₁Base ≫ B.inclusion.map U.hom = _
    rw [B.inclusion.map_preimage, hUHom, ← Category.assoc, hGlueX'', Category.assoc, haBase]
    dsimp only [p₁]
    rw [Category.assoc, hd₁Base]
    exact hpOver₁
  have hq₂Over : q₂Base ≫ U.hom = (E.obj j₂).hom := by
    apply B.inclusion.map_injective
    show B.inclusion.map q₂Base ≫ B.inclusion.map U.hom = _
    rw [B.inclusion.map_preimage, hUHom, ← Category.assoc, hGlueY'', Category.assoc, hbBase]
    dsimp only [p₂]
    rw [Category.assoc, hd₂Base]
    exact hpOver₂
  let q₁ : E.obj j₁ ⟶ U := Over.homMk q₁Base hq₁Over
  let q₂ : E.obj j₂ ⟶ U := Over.homMk q₂Base hq₂Over
  have hq0 : E.map g₁ ≫ q₁ = E.map g₂ ≫ q₂ := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    show B.inclusion.map (E.map g₁).left ≫ B.inclusion.map q₁Base =
      B.inclusion.map (E.map g₂).left ≫ B.inclusion.map q₂Base
    rw [B.inclusion.map_preimage, B.inclusion.map_preimage]
    show T.map (E.map g₁) ≫ u₁ = T.map (E.map g₂) ≫ u₂
    exact hOverlap
  let q₀ := E.map g₁ ≫ q₁
  let q : E ⟶ (Functor.const I).obj U := {
    app := fun j ↦ by
      cases j with
      | up j =>
        cases j with
        | none =>
            show E.obj j₀ ⟶ U
            exact q₀
        | some j => cases j with
          | left =>
              show E.obj j₁ ⟶ U
              exact q₁
          | right =>
              show E.obj j₂ ⟶ U
              exact q₂
    naturality := by
      intro j k g
      cases j with
      | up j =>
        cases j with
        | none =>
          cases k with
          | up k =>
            cases k with
            | none =>
              have hg : g = 𝟙 j₀ := by
                apply e.inverse.map_injective
                exact Subsingleton.elim _ _
              subst g
              show E.map (𝟙 j₀) ≫ q₀ = q₀
              rw [E.map_id]
              simp
            | some k =>
              cases k with
              | left =>
                have hg : g = g₁ := by
                  apply e.inverse.map_injective
                  exact Subsingleton.elim _ _
                subst g
                show E.map g₁ ≫ q₁ = q₀
                rfl
              | right =>
                have hg : g = g₂ := by
                  apply e.inverse.map_injective
                  exact Subsingleton.elim _ _
                subst g
                show E.map g₂ ≫ q₂ = E.map g₁ ≫ q₁
                exact hq0.symm
        | some j =>
          cases j with
          | left =>
            cases k with
            | up k =>
              cases k with
              | none =>
                  have g' : (WalkingSpan.left : WalkingSpan) ⟶ WalkingSpan.zero :=
                    g.down.down
                  nomatch g'
              | some k =>
                cases k with
                | left =>
                    have hg : g = 𝟙 j₁ := by
                      apply e.inverse.map_injective
                      exact Subsingleton.elim _ _
                    subst g
                    show E.map (𝟙 j₁) ≫ q₁ = q₁
                    rw [E.map_id]
                    simp
                | right =>
                    have g' : (WalkingSpan.left : WalkingSpan) ⟶ WalkingSpan.right :=
                    g.down.down
                    nomatch g'
          | right =>
            cases k with
            | up k =>
              cases k with
              | none =>
                  have g' : (WalkingSpan.right : WalkingSpan) ⟶ WalkingSpan.zero :=
                    g.down.down
                  nomatch g'
              | some k =>
                cases k with
                | left =>
                    have g' : (WalkingSpan.right : WalkingSpan) ⟶ WalkingSpan.left :=
                    g.down.down
                    nomatch g'
                | right =>
                    have hg : g = 𝟙 j₂ := by
                      apply e.inverse.map_injective
                      exact Subsingleton.elim _ _
                    subst g
                    show E.map (𝟙 j₂) ≫ q₂ = q₂
                    rw [E.map_id]
                    simp
  }
  have hci₂ : d₂.hom ≫ bS = T.map (c.ι.app j₂) :=
    map_unitInv_comp_map_ι T c₀ e WalkingSpan.right
  have hq₂Scheme : T.map (q.app j₂) = u₂ := by
    show B.inclusion.map (q.app j₂).left = u₂
    have hq₂app : q.app j₂ = q₂ := by
      dsimp [q, j₂, e, e₁, e₂]
      rfl
    rw [hq₂app]
    show B.inclusion.map q₂Base = u₂
    exact B.inclusion.map_preimage _
  have hsq₂Scheme : IsPullback (T.map (p.app j₂)) (T.map (q.app j₂))
      (T.map (c.ι.app j₂)) (T.map v) := by
    let eP : T.obj Y' ≅ T.obj (((Functor.const I).obj c.pt).obj j₂) :=
      Iso.refl _
    apply hPB₂.of_iso (Iso.refl _) d₂.symm (Iso.refl _) eP
    · dsimp [p₂]
      simp
    · exact hq₂Scheme.symm
    · calc
        bS ≫ eP.hom = (d₂.inv ≫ d₂.hom) ≫ bS ≫ eP.hom := by simp
        _ = d₂.inv ≫ (d₂.hom ≫ bS) ≫ eP.hom := by cat_disch
        _ = d₂.inv ≫ T.map (c.ι.app j₂) := by
          rw [hci₂]
          exact Category.comp_id (d₂.inv ≫ T.map (c.ι.app j₂))
    · show vSch ≫ 𝟙 (T.obj Y') = T.map v
      rw [Category.comp_id]
      exact hVMap.symm
  have hsq₂ : IsPullback (p.app j₂) (q.app j₂) (c.ι.app j₂) v :=
    IsPullback.of_map_of_faithful T hsq₂Scheme
  have hsq₀Scheme : IsPullback (T.map (p.app j₀)) (T.map (q.app j₀))
      (T.map (c.ι.app j₀)) (T.map v) := by
    have hpaste := (((hcart g₂).map T).paste_horiz hsq₂Scheme.flip).flip
    have hqNat : E.map g₂ ≫ q.app j₂ = q.app j₀ := by
      have h := q.naturality g₂
      change E.map g₂ ≫ q.app j₂ = q.app j₀ ≫ 𝟙 U at h
      exact h.trans (Category.comp_id (q.app j₀))
    have hcNat : D.map g₂ ≫ c.ι.app j₂ = c.ι.app j₀ := c.w g₂
    simpa only [← T.map_comp, hqNat, hcNat] using hpaste
  have hsq₀ : IsPullback (p.app j₀) (q.app j₀) (c.ι.app j₀) v :=
    IsPullback.of_map_of_faithful T hsq₀Scheme
  have hj₀ : j₀ = (ULift.up (none : Option WalkingPair) : I) := by
    dsimp [j₀, e, e₁, e₂]
    rfl
  have hj₂ : j₂ = (ULift.up (some WalkingPair.right) : I) := by
    dsimp [j₂, e, e₁, e₂]
    rfl
  have hci₁ : d₁.hom ≫ aS = T.map (c.ι.app j₁) :=
    map_unitInv_comp_map_ι T c₀ e WalkingSpan.left
  exact ⟨U, v, q, hVEtale, by
    intro j
    cases j with
    | up j =>
      cases j with
      | none =>
        rw [hj₀] at hsq₀
        exact hsq₀
      | some j =>
        cases j with
        | left =>
          have hq₁app : q.app j₁ = q₁ := by
            dsimp [q, j₁, e, e₁, e₂]
            rfl
          have hq₁Scheme : T.map (q.app j₁) = u₁ := by
            show B.inclusion.map (q.app j₁).left = u₁
            rw [hq₁app]
            show B.inclusion.map q₁Base = u₁
            exact B.inclusion.map_preimage _
          have hsq₁Scheme : IsPullback (T.map (p.app j₁)) (T.map (q.app j₁))
              (T.map (c.ι.app j₁)) (T.map v) := by
            let eP : T.obj Y' ≅ T.obj (((Functor.const I).obj c.pt).obj j₁) := Iso.refl _
            apply hPB₁.of_iso (Iso.refl _) d₁.symm (Iso.refl _) eP
            · dsimp [p₁]
              simp
            · exact hq₁Scheme.symm
            · calc
                aS ≫ eP.hom = (d₁.inv ≫ d₁.hom) ≫ aS ≫ eP.hom := by simp
                _ = d₁.inv ≫ (d₁.hom ≫ aS) ≫ eP.hom := by cat_disch
                _ = d₁.inv ≫ T.map (c.ι.app j₁) := by
                  rw [hci₁]
                  exact Category.comp_id (d₁.inv ≫ T.map (c.ι.app j₁))
            · show vSch ≫ 𝟙 (T.obj Y') = T.map v
              rw [Category.comp_id]
              exact hVMap.symm
          exact IsPullback.of_map_of_faithful T hsq₁Scheme
        | right =>
          rw [hj₂] at hsq₂
          exact hsq₂⟩

/-- **Stacks 07SY.** The pushout `Y' = Y ⨿_X X'` of a thickening `X ⟶ X'` and an affine morphism
`X ⟶ Y` of schemes over `S` is also a pushout in the category of algebraic spaces over `S`. -/
@[stacks 07SY "granted the étale clause of Tag 07RX, carried as a hypothesis; Tag 06AD is \
  discharged from `Stacks.Thickenings.forall_isAffine_of_isThickening`"]
public theorem isPushout_algebraicSpaces_of_isThickening_of_isAffineHom
    (h07RX : ∀ {Z Z' W : Scheme.{u}} (k : Z ⟶ Z') (g : Z ⟶ W) (hk : IsThickening k)
      [IsAffineHom g] [HasPushout k g] (T : Stacks.Pushout.gluingData k g),
      Etale ((Stacks.Pushout.gluingFunctor k g hk).obj T).hom ↔
        (Etale T.obj.left.hom ∧ Etale T.obj.right.hom))
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' Y Y' : BigFppfOver B S hS}
    (i : X ⟶ X') (f : X ⟶ Y) (a : X' ⟶ Y') (b : Y ⟶ Y')
    (hi : IsThickening ((BigFppfOver.toScheme B S hS).map i))
    [IsAffineHom ((BigFppfOver.toScheme B S hS).map f)]
    (hPushout : IsPushout ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map f)
      ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b)) :
    IsPushout
      (ObjectProperty.homMk (yoneda.map i) :
        (⟨yoneda.obj X, isAlgebraicSpace_yoneda B S hS X⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨yoneda.obj X', isAlgebraicSpace_yoneda B S hS X'⟩ : AlgebraicSpaces B S hS))
      (ObjectProperty.homMk (yoneda.map f) :
        (⟨yoneda.obj X, isAlgebraicSpace_yoneda B S hS X⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨yoneda.obj Y, isAlgebraicSpace_yoneda B S hS Y⟩ : AlgebraicSpaces B S hS))
      (ObjectProperty.homMk (yoneda.map a) :
        (⟨yoneda.obj X', isAlgebraicSpace_yoneda B S hS X'⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨yoneda.obj Y', isAlgebraicSpace_yoneda B S hS Y'⟩ : AlgebraicSpaces B S hS))
      (ObjectProperty.homMk (yoneda.map b) :
        (⟨yoneda.obj Y, isAlgebraicSpace_yoneda B S hS Y⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨yoneda.obj Y', isAlgebraicSpace_yoneda B S hS Y'⟩ : AlgebraicSpaces B S hS)) := by
  have w : i ≫ a = f ≫ b := by
    apply Functor.map_injective (BigFppfOver.toScheme B S hS)
    exact hPushout.w
  let T := BigFppfOver.toScheme B S hS
  let iS := T.map i
  let fS := T.map f
  let aS := T.map a
  let bS := T.map b
  let I := SpanIndex.{u}
  let e₁ : WalkingSpan ≌ AsSmall.{u} WalkingSpan := AsSmall.equiv
  let e₂ : AsSmall.{u} WalkingSpan ≌ I := ULiftHom.equiv
  let e : WalkingSpan ≌ I := e₁.trans e₂
  let D : I ⥤ BigFppfOver B S hS := e.inverse ⋙ span i f
  let c₀ : PushoutCocone i f := PushoutCocone.mk a b w
  let c : Cocone D := c₀.whisker e.inverse
  have hUniversal := isColimit_algebraicSpaces_of_scheme B S hS D c
    (isColimit_mapCocone_spanCocone B S hS i f a b w hPushout)
    (cover_spanCocone Stacks.Thickenings.forall_isAffine_of_isThickening
      B S hS i f a b w hi hPushout)
    (etaleColimit_spanCocone Stacks.Thickenings.forall_isAffine_of_isThickening
      h07RX B S hS i f a b w hi hPushout)
    (etaleDescent_spanCocone Stacks.Thickenings.forall_isAffine_of_isThickening
      h07RX B S hS i f a b w hi hPushout)
  let V : BigFppfOver B S hS ⥤ AlgebraicSpaces B S hS := {
    obj := fun Z ↦ ⟨yoneda.obj Z, isAlgebraicSpace_yoneda B S hS Z⟩
    map := fun g ↦ ObjectProperty.homMk (yoneda.map g)
    map_id := by intro Z; ext; simp
    map_comp := by intro Z W Q g h; ext; simp }
  have hColimitAS : IsColimit (V.mapCocone c) := by
    let maps (s : Cocone (D ⋙ V)) :
        ∀ j, yoneda.obj (D.obj j) ⟶ s.pt.1 := fun j ↦ (s.ι.app j).hom
    have hcompat (s : Cocone (D ⋙ V)) :
        ∀ {j k} (g : j ⟶ k),
          yoneda.map (D.map g) ≫ maps s k = maps s j := by
      intro j k g
      have hw := congrArg (fun m ↦ m.hom) (s.w g)
      simpa [maps, V] using hw
    let result (s : Cocone (D ⋙ V)) :=
      hUniversal s.pt.1 s.pt.2 (maps s) (hcompat s)
    refine IsColimit.mk (fun s ↦ ObjectProperty.homMk (Classical.choose (result s))) ?_ ?_
    · intro s j
      apply ObjectProperty.hom_ext
      exact (Classical.choose_spec (result s)).1 j
    · intro s m hm
      apply ObjectProperty.hom_ext
      exact (Classical.choose_spec (result s)).2 m.hom (by
        intro j
        have hj := congrArg (fun q ↦ q.hom) (hm j)
        simpa [V, maps] using hj)
  have hColimitAS₀ : IsColimit (V.mapCocone c₀) := by
    change IsColimit (Cocone.whisker e.inverse (V.mapCocone c₀)) at hColimitAS
    exact hColimitAS.whiskerEquivalence e
  have hColimitAS' : IsColimit (PushoutCocone.mk (V.map a) (V.map b) (by
      simpa using congrArg V.map w)) :=
    isColimit_pushoutCocone_map_equiv V i f a b w _ hColimitAS₀
  exact IsPushout.of_isColimit hColimitAS'

end Space

end AlgebraicGeometry

end
