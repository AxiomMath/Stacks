module

public import Mathlib.AlgebraicGeometry.RelativeGluing

/-!
# Gluing two charts of a morphism along a twist

Let `Ω₁` and `Ω₂` be opens of a scheme `Z`, let `p : X ⟶ Z` be a morphism, and let `τ` be an
automorphism of the part of `X` lying over `Ω₁ ⊓ Ω₂` which commutes with `p`. Then the part of
`X` over `Ω₁` and the part of `X` over `Ω₂` glue along `τ` to a scheme over `Ω₁ ⊔ Ω₂` whose part
over each of `Ω₁`, `Ω₂` and `Ω₁ ⊓ Ω₂` is the corresponding part of `X`.

This is Mathlib's relative gluing [Stacks, Tag 01LH] specialised to a cover of `Ω₁ ⊔ Ω₂` by three
opens, indexed by `CategoryTheory.Limits.WalkingSpan`: the cover is locally directed because the
family `{Ω₁ ⊓ Ω₂, Ω₁, Ω₂}` is closed under pairwise intersection, and the gluing datum is the
span of the two inclusions of charts, the right-hand one composed with `τ`.

## Main results

* `Stacks.TwoChartGluing.exists_glued`: the glued scheme, with three cartesian squares
  identifying each chart with the part of the glued scheme over the corresponding open, and two
  identities expressing the overlap chart through the `Ω₁` chart and, after the twist, through
  the `Ω₂` chart.
* `Stacks.TwoChartGluing.isPullback_restrict_chart`: such a cartesian square stays cartesian
  when the open is shrunk.

## References

* [Stacks Project, Tag 01LH](https://stacks.math.columbia.edu/tag/01LH)
-/

@[expose] public section

namespace Stacks.TwoChartGluing

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace

universe u

noncomputable section

variable {Z : Scheme.{u}} (Ω₁ Ω₂ : Z.Opens)

/-- The three opens of the two-chart cover, indexed by `WalkingSpan`. -/
def baseOpen : WalkingSpan → Z.Opens
  | none => Ω₁ ⊓ Ω₂
  | some WalkingPair.left => Ω₁
  | some WalkingPair.right => Ω₂

/-- Each open of the two-chart cover is contained in `Ω₁ ⊔ Ω₂`. -/
lemma baseOpen_le (i : WalkingSpan) : baseOpen Ω₁ Ω₂ i ≤ Ω₁ ⊔ Ω₂ := by
  cases i with
  | none => exact le_trans inf_le_left le_sup_left
  | some j => cases j with
    | left => exact le_sup_left
    | right => exact le_sup_right

/-- `baseOpen` is monotone along the morphisms of `WalkingSpan`. -/
lemma baseOpen_mono {i j : WalkingSpan} (h : i ⟶ j) : baseOpen Ω₁ Ω₂ i ≤ baseOpen Ω₁ Ω₂ j := by
  cases h with
  | id => exact le_rfl
  | init k => cases k with
    | left => exact inf_le_left
    | right => exact inf_le_right

/-- The intersection of any two opens of the two-chart cover is again an open of the cover,
indexed by an object mapping to both indices. -/
lemma exists_baseOpen_inf (i j : WalkingSpan) :
    ∃ (k : WalkingSpan) (_ : k ⟶ i) (_ : k ⟶ j),
      baseOpen Ω₁ Ω₂ k = baseOpen Ω₁ Ω₂ i ⊓ baseOpen Ω₁ Ω₂ j := by
  cases i with
  | none =>
      cases j with
      | none => exact ⟨none, WidePushoutShape.Hom.id _, WidePushoutShape.Hom.id _,
          (inf_idem _).symm⟩
      | some b => exact ⟨none, WidePushoutShape.Hom.id _, WidePushoutShape.Hom.init b, by
          cases b <;> simp [baseOpen]⟩
  | some a =>
      cases j with
      | none => exact ⟨none, WidePushoutShape.Hom.init a, WidePushoutShape.Hom.id _, by
          cases a <;> simp [baseOpen]⟩
      | some b =>
          cases a with
          | left =>
              cases b with
              | left => exact ⟨some WalkingPair.left, WidePushoutShape.Hom.id _,
                  WidePushoutShape.Hom.id _, by simp [baseOpen]⟩
              | right => exact ⟨none, WidePushoutShape.Hom.init _,
                  WidePushoutShape.Hom.init _, by simp [baseOpen]⟩
          | right =>
              cases b with
              | left => exact ⟨none, WidePushoutShape.Hom.init _,
                  WidePushoutShape.Hom.init _, by simp [baseOpen, inf_comm]⟩
              | right => exact ⟨some WalkingPair.right, WidePushoutShape.Hom.id _,
                  WidePushoutShape.Hom.id _, by simp [baseOpen]⟩

/-- Every point of the fibre product of two members of the cover comes from the member
equal to their intersection. -/
lemma exists_lift_eq {T U V W : Z.Opens} (hUT : U ≤ T) (hVT : V ≤ T) (hW : W = U ⊓ V)
    (hU : W ≤ U) (hV : W ≤ V)
    (x : (pullback (Z.homOfLE hUT) (Z.homOfLE hVT)).carrier) :
    ∃ y : W.toScheme, pullback.lift (Z.homOfLE hU) (Z.homOfLE hV)
      (by rw [Scheme.homOfLE_homOfLE, Scheme.homOfLE_homOfLE]) y = x := by
  subst hW
  have h := isPullback_opens_inf_le (X := Z) hUT hVT
  have hlift : pullback.lift (Z.homOfLE hU) (Z.homOfLE hV)
      (by rw [Scheme.homOfLE_homOfLE, Scheme.homOfLE_homOfLE]) = h.isoPullback.hom := by
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, h.isoPullback_hom_fst]
    · rw [pullback.lift_snd, h.isoPullback_hom_snd]
  refine ⟨h.isoPullback.inv x, ?_⟩
  rw [hlift, ← Scheme.Hom.comp_apply, h.isoPullback.inv_hom_id]
  rfl

/-- The functor on `WalkingSpan` given by the three opens of the cover and their inclusions. -/
def baseFunctor : WalkingSpan ⥤ Scheme.{u} where
  obj i := (baseOpen Ω₁ Ω₂ i).toScheme
  map h := Z.homOfLE (baseOpen_mono Ω₁ Ω₂ h)
  map_id i := by
    rw [← cancel_mono (baseOpen Ω₁ Ω₂ i).ι, Scheme.homOfLE_ι, Category.id_comp]
  map_comp h h' := by rw [Scheme.homOfLE_homOfLE]

/-- The inclusion `Ω₁ ⟶ Ω₁ ⊔ Ω₂` sends a point of `Ω₁` to itself. -/
lemma homOfLE_sup_apply_left (x : (Ω₁ ⊔ Ω₂ : Z.Opens).toScheme) (h : x.1 ∈ Ω₁) :
    Z.homOfLE (le_sup_left (a := Ω₁) (b := Ω₂)) ⟨x.1, h⟩ = x := by
  rw [Scheme.homOfLE_apply']
  rfl

/-- The inclusion `Ω₂ ⟶ Ω₁ ⊔ Ω₂` sends a point of `Ω₂` to itself. -/
lemma homOfLE_sup_apply_right (x : (Ω₁ ⊔ Ω₂ : Z.Opens).toScheme) (h : x.1 ∈ Ω₂) :
    Z.homOfLE (le_sup_right (a := Ω₁) (b := Ω₂)) ⟨x.1, h⟩ = x := by
  rw [Scheme.homOfLE_apply']
  rfl

/-- The cover of `Ω₁ ⊔ Ω₂` by `Ω₁`, `Ω₂` and their intersection. -/
abbrev baseCover : (Ω₁ ⊔ Ω₂ : Z.Opens).toScheme.OpenCover where
  I₀ := WalkingSpan
  X i := (baseOpen Ω₁ Ω₂ i).toScheme
  f i := Z.homOfLE (baseOpen_le Ω₁ Ω₂ i)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun i ↦ inferInstance⟩
    have hx : x.1 ∈ Ω₁ ∨ x.1 ∈ Ω₂ := by simpa using x.2
    rcases hx with h | h
    · exact ⟨some WalkingPair.left, ⟨x.1, h⟩, homOfLE_sup_apply_left Ω₁ Ω₂ x h⟩
    · exact ⟨some WalkingPair.right, ⟨x.1, h⟩, homOfLE_sup_apply_right Ω₁ Ω₂ x h⟩

/-- The two-chart cover is locally directed, with transition maps the inclusions of opens. -/
instance : (baseCover Ω₁ Ω₂).LocallyDirected where
  trans h := Z.homOfLE (baseOpen_mono Ω₁ Ω₂ h)
  trans_id i := by
    rw [← cancel_mono (baseOpen Ω₁ Ω₂ i).ι, Scheme.homOfLE_ι, Category.id_comp]
  trans_comp h h' := by rw [Scheme.homOfLE_homOfLE]
  w h := by rw [Scheme.homOfLE_homOfLE]
  directed {i j} x := by
    obtain ⟨k, hki, hkj, heq⟩ := exists_baseOpen_inf Ω₁ Ω₂ i j
    obtain ⟨y, hy⟩ := exists_lift_eq (baseOpen_le Ω₁ Ω₂ i) (baseOpen_le Ω₁ Ω₂ j) heq
      (baseOpen_mono Ω₁ Ω₂ hki) (baseOpen_mono Ω₁ Ω₂ hkj) x
    exact ⟨k, hki, hkj, y, hy⟩
  property_trans h := inferInstance

section Charts

variable {X : Scheme.{u}} (p : X ⟶ Z)

/-- Taking preimages under `p` is monotone. -/
lemma preimage_mono {Ω' Ω : Z.Opens} (h : Ω' ≤ Ω) : p ⁻¹ᵁ Ω' ≤ p ⁻¹ᵁ Ω := fun _ hx ↦ h hx

/-- Restrictions of `p` to nested opens commute with the inclusions. -/
lemma homOfLE_morphismRestrict {Ω' Ω : Z.Opens} (h : Ω' ≤ Ω) :
    X.homOfLE (preimage_mono p h) ≫ p ∣_ Ω = p ∣_ Ω' ≫ Z.homOfLE h := by
  rw [← cancel_mono Ω.ι, Category.assoc, Category.assoc, morphismRestrict_ι,
    Scheme.homOfLE_ι_assoc, Scheme.homOfLE_ι, morphismRestrict_ι]

/-- For opens `Ω' ≤ Ω`, the square formed by the restrictions of `p` to `Ω'` and `Ω` and the
inclusions is cartesian. -/
lemma isPullback_homOfLE_morphismRestrict {Ω' Ω : Z.Opens} (h : Ω' ≤ Ω) :
    IsPullback (X.homOfLE (preimage_mono p h)) (p ∣_ Ω') (p ∣_ Ω) (Z.homOfLE h) := by
  have s : IsPullback (X.homOfLE (preimage_mono p h) ≫ (p ⁻¹ᵁ Ω).ι) (p ∣_ Ω') p
      (Z.homOfLE h ≫ Ω.ι) := by
    rw [Scheme.homOfLE_ι, Scheme.homOfLE_ι]
    exact (isPullback_morphismRestrict p Ω').flip
  exact IsPullback.of_right s (homOfLE_morphismRestrict p h)
    (isPullback_morphismRestrict p Ω).flip

/-- The inclusion of an open into itself is the identity. -/
lemma homOfLE_self {U : Z.Opens} (h : U ≤ U) : Z.homOfLE h = 𝟙 _ :=
  Z.homOfLE_rfl U

/-- The maps of the chart functor: inclusions of preimages, twisted by `τ` on the right leg. -/
def chartMap (τ : (p ⁻¹ᵁ (Ω₁ ⊓ Ω₂)).toScheme ⟶ (p ⁻¹ᵁ (Ω₁ ⊓ Ω₂)).toScheme) :
    {i j : WalkingSpan} → (i ⟶ j) →
      ((p ⁻¹ᵁ baseOpen Ω₁ Ω₂ i).toScheme ⟶ (p ⁻¹ᵁ baseOpen Ω₁ Ω₂ j).toScheme)
  | _, _, WidePushoutShape.Hom.id _ => 𝟙 _
  | _, _, WidePushoutShape.Hom.init WalkingPair.left =>
      X.homOfLE (preimage_mono p (inf_le_left : Ω₁ ⊓ Ω₂ ≤ Ω₁))
  | _, _, WidePushoutShape.Hom.init WalkingPair.right =>
      τ ≫ X.homOfLE (preimage_mono p (inf_le_right : Ω₁ ⊓ Ω₂ ≤ Ω₂))

/-- The chart functor of the two-chart gluing datum. -/
abbrev chartFunctor (τ : (p ⁻¹ᵁ (Ω₁ ⊓ Ω₂)).toScheme ⟶ (p ⁻¹ᵁ (Ω₁ ⊓ Ω₂)).toScheme) :
    WalkingSpan ⥤ Scheme.{u} where
  obj i := (p ⁻¹ᵁ baseOpen Ω₁ Ω₂ i).toScheme
  map := chartMap Ω₁ Ω₂ p τ
  map_id i := rfl
  map_comp f g := by
    cases f with
    | id _ =>
        cases g with
        | id _ => exact (Category.id_comp _).symm
        | init b => exact (Category.id_comp _).symm
    | init b =>
        cases g with
        | id _ => exact (Category.comp_id _).symm

variable (τ : (p ⁻¹ᵁ (Ω₁ ⊓ Ω₂)).toScheme ⟶ (p ⁻¹ᵁ (Ω₁ ⊓ Ω₂)).toScheme)
  (hτ : τ ≫ p ∣_ (Ω₁ ⊓ Ω₂) = p ∣_ (Ω₁ ⊓ Ω₂))

/-- The structure maps of the chart functor down to the cover. -/
def chartNat : chartFunctor Ω₁ Ω₂ p τ ⟶ (baseCover Ω₁ Ω₂).functorOfLocallyDirected where
  app i := p ∣_ (baseOpen Ω₁ Ω₂ i)
  naturality i j h := by
    cases h with
    | id =>
        have hid : (baseCover Ω₁ Ω₂).functorOfLocallyDirected.map (WidePushoutShape.Hom.id i)
            = 𝟙 ((baseCover Ω₁ Ω₂).functorOfLocallyDirected.obj i) := homOfLE_self le_rfl
        rw [hid]
        exact (Category.id_comp _).trans (Category.comp_id _).symm
    | init k =>
        cases k with
        | left =>
            exact homOfLE_morphismRestrict p (inf_le_left : Ω₁ ⊓ Ω₂ ≤ Ω₁)
        | right =>
            change (τ ≫ X.homOfLE (preimage_mono p (inf_le_right : Ω₁ ⊓ Ω₂ ≤ Ω₂))) ≫ p ∣_ Ω₂
              = p ∣_ (Ω₁ ⊓ Ω₂) ≫ Z.homOfLE (inf_le_right : Ω₁ ⊓ Ω₂ ≤ Ω₂)
            rw [Category.assoc, homOfLE_morphismRestrict p (inf_le_right : Ω₁ ⊓ Ω₂ ≤ Ω₂),
              ← Category.assoc, hτ]

/-- When `τ` is an isomorphism, the natural transformation `chartNat` is equifibered. -/
lemma chartNat_equifibered [IsIso τ] : (chartNat Ω₁ Ω₂ p τ hτ).Equifibered := by
  intro i j h
  cases h with
  | id =>
      change IsPullback (𝟙 _) (p ∣_ _) (p ∣_ _) (Z.homOfLE (baseOpen_mono Ω₁ Ω₂ (𝟙 i)))
      rw [homOfLE_self]
      exact .of_id_fst
  | init k =>
      cases k with
      | left => exact isPullback_homOfLE_morphismRestrict p (inf_le_left : Ω₁ ⊓ Ω₂ ≤ Ω₁)
      | right =>
          change IsPullback (τ ≫ X.homOfLE (preimage_mono p (inf_le_right : Ω₁ ⊓ Ω₂ ≤ Ω₂)))
            (p ∣_ (Ω₁ ⊓ Ω₂)) (p ∣_ Ω₂) (Z.homOfLE (inf_le_right : Ω₁ ⊓ Ω₂ ≤ Ω₂))
          have hsq : IsPullback τ (p ∣_ (Ω₁ ⊓ Ω₂)) (p ∣_ (Ω₁ ⊓ Ω₂)) (𝟙 _) :=
            IsPullback.of_horiz_isIso ⟨by rw [hτ, Category.comp_id]⟩
          have hpaste := hsq.paste_horiz
            (isPullback_homOfLE_morphismRestrict p (inf_le_right : Ω₁ ⊓ Ω₂ ≤ Ω₂))
          rwa [Category.id_comp] at hpaste

/-- The relative gluing datum of the two-chart situation. -/
def gluingData [IsIso τ] : (baseCover Ω₁ Ω₂).RelativeGluingData where
  functor := chartFunctor Ω₁ Ω₂ p τ
  natTrans := chartNat Ω₁ Ω₂ p τ hτ
  equifibered := chartNat_equifibered Ω₁ Ω₂ p τ hτ

variable [IsIso τ]

/-- Postcomposing the right and bottom edges of a cartesian square with a monomorphism keeps it
cartesian. -/
lemma isPullback_comp_mono {A B C D E : Scheme.{u}} {fst : A ⟶ B} {snd : A ⟶ C} {f : B ⟶ D}
    {g : C ⟶ D} (h : IsPullback fst snd f g) (m : D ⟶ E) [Mono m] {f' : B ⟶ E}
    (hf' : f ≫ m = f') : IsPullback fst snd f' (g ≫ m) := by
  subst hf'
  have t : IsPullback g (𝟙 _) m (g ≫ m) :=
    IsPullback.of_vert_isIso_mono ⟨by rw [Category.id_comp]⟩
  simpa only [Category.comp_id] using h.paste_vert t

include hτ in
/-- **The two-chart relative gluing.** Given a morphism `p : X ⟶ Z`, two opens `Ω₁`, `Ω₂` of `Z`
and an automorphism `τ` of the part of `X` over `Ω₁ ⊓ Ω₂` commuting with `p`, the two pieces
`p ⁻¹ᵁ Ω₁` and `p ⁻¹ᵁ Ω₂` glue along `τ` to a scheme over `Ω₁ ⊔ Ω₂` whose part over each of the
three opens is the corresponding piece of `X`. -/
theorem exists_glued :
    ∃ (V : Scheme.{u}) (f : V ⟶ (Ω₁ ⊔ Ω₂ : Z.Opens).toScheme)
      (κ : ∀ i : WalkingSpan, (p ⁻¹ᵁ baseOpen Ω₁ Ω₂ i).toScheme ⟶ V),
      (∀ i, IsPullback (p ∣_ baseOpen Ω₁ Ω₂ i) (κ i) (baseOpen Ω₁ Ω₂ i).ι
          (f ≫ (Ω₁ ⊔ Ω₂ : Z.Opens).ι)) ∧
        X.homOfLE (preimage_mono p (inf_le_left : Ω₁ ⊓ Ω₂ ≤ Ω₁)) ≫ κ (some WalkingPair.left)
          = κ none ∧
        τ ≫ X.homOfLE (preimage_mono p (inf_le_right : Ω₁ ⊓ Ω₂ ≤ Ω₂)) ≫
            κ (some WalkingPair.right) = κ none := by
  refine ⟨(gluingData Ω₁ Ω₂ p τ hτ).glued, (gluingData Ω₁ Ω₂ p τ hτ).toBase,
    fun i ↦ colimit.ι (gluingData Ω₁ Ω₂ p τ hτ).functor i, fun i ↦ ?_, ?_, ?_⟩
  · exact isPullback_comp_mono
      ((gluingData Ω₁ Ω₂ p τ hτ).isPullback_natTrans_ι_toBase i)
      ((Ω₁ ⊔ Ω₂ : Z.Opens).ι) (Scheme.homOfLE_ι Z (baseOpen_le Ω₁ Ω₂ i))
  · exact colimit.w (gluingData Ω₁ Ω₂ p τ hτ).functor (WidePushoutShape.Hom.init WalkingPair.left)
  · exact (Category.assoc _ _ _).symm.trans
      (colimit.w (gluingData Ω₁ Ω₂ p τ hτ).functor (WidePushoutShape.Hom.init WalkingPair.right))

/-- Shrinking the open in a chart square of a morphism `q` keeps it cartesian. -/
lemma isPullback_restrict_chart {V : Scheme.{u}} (q : V ⟶ Z) {Ω Ω' : Z.Opens}
    (h : Ω' ≤ Ω) {κ : (p ⁻¹ᵁ Ω).toScheme ⟶ V} (hκ : IsPullback (p ∣_ Ω) κ Ω.ι q) :
    IsPullback (p ∣_ Ω') (X.homOfLE (preimage_mono p h) ≫ κ) Ω'.ι q := by
  have hpaste := (isPullback_homOfLE_morphismRestrict p h).flip.paste_vert hκ
  rw [Scheme.homOfLE_ι] at hpaste
  exact hpaste

end Charts

end

end Stacks.TwoChartGluing
