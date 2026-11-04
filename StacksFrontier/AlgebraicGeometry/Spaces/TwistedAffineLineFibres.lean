module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedAffineLine

/-!
# Points of the affine line over a scheme

Over a point `v` of a scheme `V`, the fibre of the affine line `𝔸¹_V ⟶ V` is the affine line over
the residue field of `v`. It is irreducible of dimension one, so a point of the fibre with a
proper specialization inside the fibre is its generic point. This file records that fact,
together with the constant sections of the affine line and the zero loci of the coordinate.

## Main definitions

* `AlgebraicGeometry.TwistedAffineLine.constSection`: the section of `𝔸¹_V ⟶ V` with constant
  coordinate a given global section.

## Main results

* `AlgebraicGeometry.TwistedAffineLine.specializes_of_specializes_of_ne`: a point of a fibre of
  the affine line with a proper specialization in that fibre specializes to every point of the
  fibre.
* `AlgebraicGeometry.TwistedAffineLine.exists_generic_fibre`: every fibre has a generic point.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.TwistedAffineLine

open _root_.AlgebraicGeometry.AffineSpace

variable {V : Scheme.{u}}

/-! ### Constant sections -/

/-- The section of the affine line over `V` whose coordinate is the global section `c`. -/
noncomputable def constSection (c : Γ(V, ⊤)) : V ⟶ 𝔸(Idx; V) :=
  homOfVector (𝟙 V) fun _ ↦ c

/-- The constant section is a section of the projection `𝔸¹_V ⟶ V`. -/
@[reassoc (attr := simp)]
theorem constSection_over (c : Γ(V, ⊤)) : constSection c ≫ 𝔸(Idx; V) ↘ V = 𝟙 V :=
  homOfVector_over _ _

/-- The constant section pulls the coordinate back to `c`. -/
@[simp]
theorem constSection_appTop_coord (c : Γ(V, ⊤)) (i : Idx.{u}) :
    (constSection c).appTop (coord V i) = c :=
  homOfVector_appTop_coord _ _ _

/-- The constant section at a point `v` lies over `v`. -/
@[simp]
theorem constSection_apply_over (c : Γ(V, ⊤)) (v : V) :
    (𝔸(Idx; V) ↘ V) (constSection c v) = v := by
  rw [← Scheme.Hom.comp_apply, constSection_over]
  rfl

/-- The constant section at a point lies in the nonvanishing locus of the coordinate exactly when
its value does not vanish at the point. -/
theorem constSection_mem_basicOpen_iff (c : Γ(V, ⊤)) (v : V) (a : Γ(𝔸(Idx; V), ⊤))
    (b : Γ(V, ⊤)) (ha : (constSection c).appTop a = b) :
    constSection c v ∈ (𝔸(Idx; V)).basicOpen a ↔ v ∈ V.basicOpen b := by
  change v ∈ constSection c ⁻¹ᵁ (𝔸(Idx; V)).basicOpen a ↔ _
  rw [Scheme.preimage_basicOpen_top, ha]

/-- The zero section lies in the vanishing locus of the coordinate. -/
theorem constSection_zero_notMem_basicOpen_coord (v : V) :
    constSection 0 v ∉ (𝔸(Idx; V)).basicOpen (coord V c₀) := by
  rw [constSection_mem_basicOpen_iff 0 v _ 0 (constSection_appTop_coord 0 c₀),
    Scheme.basicOpen_zero]
  exact fun h ↦ h

/-- The one section lies in the nonvanishing locus of the coordinate. -/
theorem constSection_one_mem_basicOpen_coord (v : V) :
    constSection 1 v ∈ (𝔸(Idx; V)).basicOpen (coord V c₀) := by
  rw [constSection_mem_basicOpen_iff 1 v _ 1 (constSection_appTop_coord 1 c₀),
    Scheme.basicOpen_one]
  trivial

/-- The zero and one sections take distinct values at every point. -/
theorem constSection_zero_ne_one (v : V) : constSection 0 v ≠ constSection 1 v := fun h ↦
  constSection_zero_notMem_basicOpen_coord v (h ▸ constSection_one_mem_basicOpen_coord v)

/-- The constant sections are natural along a morphism of bases. -/
theorem constSection_comp_map {W : Scheme.{u}} (f : V ⟶ W) (c : Γ(W, ⊤)) :
    constSection (f.appTop c) ≫ AffineSpace.map Idx f = f ≫ constSection c := by
  ext1
  · simp
  · rename_i i
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.map_appTop_coord,
      constSection_appTop_coord, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      constSection_appTop_coord]

/-! ### The affine line over a field -/

/-- In the spectrum of a one-dimensional domain, a prime with a proper specialization is the zero
ideal. -/
theorem eq_bot_of_lt_of_ringKrullDim_eq_one {A : Type u} [CommRing A] [IsDomain A]
    (hdim : ringKrullDim A = 1) {p q : PrimeSpectrum A} (hpq : p < q) : p.asIdeal = ⊥ := by
  by_contra hne
  let b : PrimeSpectrum A := ⟨⊥, Ideal.isPrime_bot⟩
  have hbp : b < p := lt_of_le_of_ne (fun _ h ↦ by simp_all [b]) fun h ↦ hne (by rw [← h])
  let c₁ : LTSeries (PrimeSpectrum A) := (RelSeries.singleton _ b).snoc p (by simpa using hbp)
  let c : LTSeries (PrimeSpectrum A) := c₁.snoc q (by simpa [c₁] using hpq)
  have hlen : (c.length : WithBot ℕ∞) ≤ ringKrullDim A := Order.LTSeries.length_le_krullDim c
  rw [hdim, show c.length = 2 by simp [c, c₁]] at hlen
  exact absurd hlen (by decide)

/-- The polynomial ring in one variable over a field has Krull dimension one. -/
theorem ringKrullDim_mvPolynomial_idx (K : Type u) [CommRing K] (hK : IsField K) :
    ringKrullDim (MvPolynomial Idx.{u} K) = 1 := by
  let := hK.toField
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

/-- **On the affine line over a field**, a point with a proper specialization specializes to every
point. -/
theorem specializes_of_specializes_of_ne_field {K : CommRingCat.{u}} (hK : IsField K)
    {p q : 𝔸(Idx; Spec K)} (hpq : p ⤳ q) (hne : p ≠ q) (r : 𝔸(Idx; Spec K)) : p ⤳ r := by
  set e := SpecIso Idx K
  have hdim : ringKrullDim (CommRingCat.of (MvPolynomial Idx.{u} K)) = 1 :=
    ringKrullDim_mvPolynomial_idx K hK
  let : IsDomain (MvPolynomial Idx.{u} K) := by
    let := hK.toField
    infer_instance
  have h1 : e.hom p ⤳ e.hom q := hpq.map e.hom.continuous
  have h2 : e.hom p ≠ e.hom q := fun h ↦ hne (e.hom.homeomorph.injective h)
  have hle : (e.hom p).asIdeal ≤ (e.hom q).asIdeal :=
    (PrimeSpectrum.le_iff_specializes (e.hom p) (e.hom q)).2 h1
  have hlt : (⟨(e.hom p).asIdeal, (e.hom p).isPrime⟩ :
        PrimeSpectrum (CommRingCat.of (MvPolynomial Idx.{u} K))) <
      ⟨(e.hom q).asIdeal, (e.hom q).isPrime⟩ := by
    refine lt_of_le_of_ne hle fun h ↦ h2 ?_
    have h' := congrArg PrimeSpectrum.asIdeal h
    exact PrimeSpectrum.ext h'
  have hbot := eq_bot_of_lt_of_ringKrullDim_eq_one hdim hlt
  have h3 : e.hom p ⤳ e.hom r := by
    refine (PrimeSpectrum.le_iff_specializes (e.hom p) (e.hom r)).1 ?_
    change (e.hom p).asIdeal ≤ (e.hom r).asIdeal
    rw [show (e.hom p).asIdeal = ⊥ from hbot]
    exact bot_le
  have := h3.map e.inv.continuous
  rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, e.hom_inv_id] at this

/-! ### Fibres of the affine line over a scheme -/

/-- The affine line over the residue field of a point maps onto the fibre of the affine line over
that point, as a preimmersion. -/
theorem isPreimmersion_map_fromSpecResidueField (v : V) :
    IsPreimmersion (AffineSpace.map Idx (V.fromSpecResidueField v)) :=
  MorphismProperty.of_isPullback (AffineSpace.isPullback_map _).flip inferInstance

/-- The range of the affine line over a morphism is the preimage of the range of the morphism. -/
private theorem range_map_aux {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Set.range (AffineSpace.map Idx f) = (𝔸(Idx; Y) ↘ Y) ⁻¹' Set.range f := by
  have h := AffineSpace.isPullback_map (n := Idx.{u}) f
  have hsurj : Function.Surjective h.isoPullback.hom := h.isoPullback.hom.homeomorph.surjective
  rw [← h.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    hsurj.range_eq, Set.image_univ, Scheme.Pullback.range_fst]

/-- The affine line over the residue field of `v` has image the fibre of `𝔸¹_V ⟶ V` over `v`. -/
theorem range_map_fromSpecResidueField (v : V) :
    Set.range (AffineSpace.map Idx (V.fromSpecResidueField v)) = (𝔸(Idx; V) ↘ V) ⁻¹' {v} := by
  rw [range_map_aux, Scheme.range_fromSpecResidueField]

/-- Every point of the fibre of `𝔸¹_V ⟶ V` over `v` comes from a point of the affine line over the
residue field of `v`. -/
theorem exists_map_fromSpecResidueField_eq {v : V} {p : 𝔸(Idx; V)}
    (hp : (𝔸(Idx; V) ↘ V) p = v) :
    ∃ p' : 𝔸(Idx; Spec (V.residueField v)),
      AffineSpace.map Idx (V.fromSpecResidueField v) p' = p := by
  have : p ∈ Set.range (AffineSpace.map Idx (V.fromSpecResidueField v)) := by
    rw [range_map_fromSpecResidueField]
    exact hp
  exact this

/-- **A point of a fibre of the affine line with a proper specialization in the fibre specializes
to every point of the fibre**: the fibre is the affine line over a field, which has dimension
one. -/
theorem specializes_of_specializes_of_ne {p q : 𝔸(Idx; V)} (hpq : p ⤳ q) (hne : p ≠ q)
    (hfib : (𝔸(Idx; V) ↘ V) q = (𝔸(Idx; V) ↘ V) p) (r : 𝔸(Idx; V))
    (hr : (𝔸(Idx; V) ↘ V) r = (𝔸(Idx; V) ↘ V) p) : p ⤳ r := by
  obtain ⟨v, hv⟩ : ∃ v, (𝔸(Idx; V) ↘ V) p = v := ⟨_, rfl⟩
  rw [hv] at hfib hr
  have := isPreimmersion_map_fromSpecResidueField v
  set m := AffineSpace.map Idx (V.fromSpecResidueField v)
  obtain ⟨p', rfl⟩ := exists_map_fromSpecResidueField_eq (v := v) (p := p) hv
  obtain ⟨q', rfl⟩ := exists_map_fromSpecResidueField_eq (v := v) hfib
  obtain ⟨r', rfl⟩ := exists_map_fromSpecResidueField_eq (v := v) hr
  have hemb := m.isEmbedding
  have hpq' : p' ⤳ q' := hemb.isInducing.specializes_iff.1 hpq
  have hne' : p' ≠ q' := fun h ↦ hne (by rw [h])
  have hK : IsField (V.residueField v) := Field.toIsField _
  exact (specializes_of_specializes_of_ne_field hK hpq' hne' r').map m.continuous

/-- **Every fibre of the affine line has a generic point.** -/
theorem exists_generic_fibre (v : V) :
    ∃ g : 𝔸(Idx; V), (𝔸(Idx; V) ↘ V) g = v ∧
      ∀ r : 𝔸(Idx; V), (𝔸(Idx; V) ↘ V) r = v → g ⤳ r := by
  set m := AffineSpace.map Idx (V.fromSpecResidueField v)
  set g' := genericPoint 𝔸(Idx; Spec (V.residueField v))
  have hg' : (𝔸(Idx; V) ↘ V) (m g') = v := by
    rw [← Set.mem_singleton_iff, ← Set.mem_preimage, ← range_map_fromSpecResidueField]
    exact ⟨g', rfl⟩
  refine ⟨m g', hg', fun r hr ↦ ?_⟩
  obtain ⟨r', rfl⟩ := exists_map_fromSpecResidueField_eq (v := v) hr
  exact ((genericPoint_spec 𝔸(Idx; Spec (V.residueField v))).specializes
    (Set.mem_univ r')).map m.continuous

/-- A point of a fibre which specializes to two distinct points of that fibre specializes to
every point of the fibre. -/
theorem specializes_of_specializes_two {g a b : 𝔸(Idx; V)} (hga : g ⤳ a) (hgb : g ⤳ b)
    (hab : a ≠ b) (ha : (𝔸(Idx; V) ↘ V) a = (𝔸(Idx; V) ↘ V) g)
    (hb : (𝔸(Idx; V) ↘ V) b = (𝔸(Idx; V) ↘ V) g) (r : 𝔸(Idx; V))
    (hr : (𝔸(Idx; V) ↘ V) r = (𝔸(Idx; V) ↘ V) g) : g ⤳ r := by
  by_cases hg : g = a
  · subst hg
    exact specializes_of_specializes_of_ne hgb hab hb r hr
  · exact specializes_of_specializes_of_ne hga hg ha r hr

/-- Two points of a fibre which both specialize to every point of the fibre are equal. -/
theorem eq_of_fibre_generic {g g' : 𝔸(Idx; V)}
    (hfib : (𝔸(Idx; V) ↘ V) g' = (𝔸(Idx; V) ↘ V) g)
    (hg : ∀ r : 𝔸(Idx; V), (𝔸(Idx; V) ↘ V) r = (𝔸(Idx; V) ↘ V) g → g ⤳ r)
    (hg' : ∀ r : 𝔸(Idx; V), (𝔸(Idx; V) ↘ V) r = (𝔸(Idx; V) ↘ V) g → g' ⤳ r) : g = g' :=
  ((hg g' hfib).antisymm (hg' g rfl)).eq

/-- The range of the affine line over a morphism is the preimage of the range of the morphism. -/
theorem range_map {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Set.range (AffineSpace.map Idx f) = (𝔸(Idx; Y) ↘ Y) ⁻¹' Set.range f :=
  range_map_aux f

/-! ### Points of the twisted relation, at the level of schemes -/

section TwistedPoints

variable {E : Scheme.{u}} (s t : E ⟶ V) (e : Γ(E, ⊤))

/-- The affine line over `s` pulls the coordinate back to the coordinate. -/
theorem map_mem_basicOpen_coord_iff (r : 𝔸(Idx; E)) :
    AffineSpace.map Idx s r ∈ (𝔸(Idx; V)).basicOpen (coord V c₀) ↔
      r ∈ (𝔸(Idx; E)).basicOpen (coord E c₀) := by
  change r ∈ AffineSpace.map Idx s ⁻¹ᵁ (𝔸(Idx; V)).basicOpen (coord V c₀) ↔ _
  rw [Scheme.preimage_basicOpen_top, AffineSpace.map_appTop_coord]

/-- The twisted target projection pulls the coordinate back to `c + e (1 - 2c)`. -/
theorem twist_map_appTop_coord :
    (twist e ≫ AffineSpace.map Idx t).appTop (coord V c₀) =
      coord E c₀ + (𝔸(Idx; E) ↘ E).appTop e * (1 - 2 * coord E c₀) := by
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.map_appTop_coord,
    twist_appTop_coord]

/-- The constant section followed by the twisted target projection is the section over `t` with
coordinate `c + e (1 - 2c)`. -/
theorem constSection_twist_map (c : Γ(E, ⊤)) :
    constSection c ≫ twist e ≫ AffineSpace.map Idx t =
      homOfVector t fun _ ↦ c + e * (1 - 2 * c) := by
  rw [← Category.assoc, constSection, homOfVector_comp_twist, homOfVector_comp_map]
  simp

end TwistedPoints

/-- A point lies in the nonvanishing locus of a global section exactly when the pullback of that
section along a morphism is a unit in the stalk at the point. -/
private theorem map_mem_basicOpen_iff_isUnit_germ {X Y : Scheme.{u}} (f : X ⟶ Y) (g : Γ(Y, ⊤))
    (r : X) : f r ∈ Y.basicOpen g ↔ IsUnit (X.presheaf.germ ⊤ r trivial (f.appTop g)) := by
  rw [← Scheme.mem_basicOpen_top, ← Scheme.preimage_basicOpen_top]
  rfl

/-- A point of `𝔸¹_E` lies in the nonvanishing locus of `e` exactly when its image in `E` does. -/
private theorem mem_basicOpen_appTop_iff {E : Scheme.{u}} (e : Γ(E, ⊤)) (r : 𝔸(Idx; E)) :
    r ∈ (𝔸(Idx; E)).basicOpen ((𝔸(Idx; E) ↘ E).appTop e) ↔ (𝔸(Idx; E) ↘ E) r ∈ E.basicOpen e := by
  rw [← Scheme.preimage_basicOpen_top]
  rfl

section TwistedZeroLocus

variable {E : Scheme.{u}} (t : E ⟶ V) {e : Γ(E, ⊤)} (he : IsIdempotentElem e)
include he

/-- **The twisted target projection on the zero locus of the coordinate, away from the twisting
idempotent.** A point of the zero locus of the coordinate of `𝔸¹_E` lying over a point where `e`
vanishes is carried to the zero locus of the coordinate of `𝔸¹_V`. -/
theorem twist_map_notMem_basicOpen_coord {r : 𝔸(Idx; E)}
    (hr : r ∉ (𝔸(Idx; E)).basicOpen (coord E c₀))
    (he₀ : (𝔸(Idx; E) ↘ E) r ∉ E.basicOpen e) :
    (twist e ≫ AffineSpace.map Idx t) r ∉ (𝔸(Idx; V)).basicOpen (coord V c₀) := by
  have he' : IsIdempotentElem ((𝔸(Idx; E) ↘ E).appTop e) := he.map _
  rw [← mem_basicOpen_appTop_iff] at he₀
  intro h
  rw [map_mem_basicOpen_iff_isUnit_germ, twist_map_appTop_coord, map_add, map_mul,
    Scheme.germ_eq_zero_of_isIdempotentElem_of_notMem he' r he₀, zero_mul, add_zero,
    ← Scheme.mem_basicOpen_top] at h
  exact hr h

/-- **The twisted target projection on the zero locus of the coordinate, where the twisting
idempotent is one.** A point of the zero locus of the coordinate of `𝔸¹_E` lying over a point
where `e` is one is carried to the zero locus of `coord - 1` on `𝔸¹_V`. -/
theorem twist_map_notMem_basicOpen_coord_sub_one {r : 𝔸(Idx; E)}
    (hr : r ∉ (𝔸(Idx; E)).basicOpen (coord E c₀))
    (he₁ : (𝔸(Idx; E) ↘ E) r ∈ E.basicOpen e) :
    (twist e ≫ AffineSpace.map Idx t) r ∉ (𝔸(Idx; V)).basicOpen (coord V c₀ - 1) := by
  have he' : IsIdempotentElem ((𝔸(Idx; E) ↘ E).appTop e) := he.map _
  rw [← mem_basicOpen_appTop_iff] at he₁
  intro h
  rw [map_mem_basicOpen_iff_isUnit_germ, map_sub, map_one, twist_map_appTop_coord, map_sub,
    map_add, map_mul, map_sub, map_mul, map_one, map_ofNat,
    (Scheme.germ_eq_one_iff_mem_basicOpen_of_isIdempotentElem he' r).2 he₁,
    show ∀ x : ((𝔸(Idx; E)).presheaf.stalk r), x + 1 * (1 - 2 * x) - 1 = -x from fun x ↦ by ring,
    IsUnit.neg_iff, ← Scheme.mem_basicOpen_top] at h
  exact hr h

end TwistedZeroLocus

/-- The zero section lies in the nonvanishing locus of `coord - 1`. -/
theorem constSection_zero_mem_basicOpen_coord_sub_one (v : V) :
    constSection 0 v ∈ (𝔸(Idx; V)).basicOpen (coord V c₀ - 1) := by
  rw [constSection_mem_basicOpen_iff 0 v (coord V c₀ - 1) (-1) (by
      rw [map_sub, map_one, constSection_appTop_coord]; ring)]
  rw [Scheme.basicOpen_of_isUnit V (isUnit_one.neg)]
  trivial

end AlgebraicGeometry.TwistedAffineLine

end
