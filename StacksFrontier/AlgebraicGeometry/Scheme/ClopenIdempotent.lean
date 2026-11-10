module

public import StacksFrontier.AlgebraicGeometry.ProperGeomConnected.Sections

/-!
# The idempotent global section of a clopen set of a scheme

A clopen subset `U` of a scheme `X` is the nonvanishing locus of exactly one idempotent global
section, the section which is `1` on `U` and `0` on its complement. This file constructs that
section and records how it behaves under pullback and under the "exclusive or" of two
idempotents.

## Main definitions

* `AlgebraicGeometry.Scheme.clopenIdempotent`: the idempotent global section with nonvanishing
  locus a given clopen set.

## Main results

* `AlgebraicGeometry.Scheme.isIdempotentElem_clopenIdempotent` and
  `AlgebraicGeometry.Scheme.coe_basicOpen_clopenIdempotent`: it is idempotent with nonvanishing
  locus the given set.
* `AlgebraicGeometry.Scheme.eq_of_isIdempotentElem_of_basicOpen_eq`: an idempotent global
  section is determined by its nonvanishing locus.
* `AlgebraicGeometry.Scheme.appTop_clopenIdempotent`: pulling the section back along a morphism
  gives the section of the preimage.
* `AlgebraicGeometry.Scheme.coe_basicOpen_xor`: the nonvanishing locus of `e + e' - 2 e e'` is
  the symmetric difference of those of two idempotents `e` and `e'`.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- At every point the germ of an idempotent global section is `0` or `1`, and it is `1` exactly
at the points of the nonvanishing locus. -/
theorem germ_eq_one_iff_mem_basicOpen_of_isIdempotentElem {e : Γ(X, ⊤)}
    (he : IsIdempotentElem e) (x : X) :
    X.presheaf.germ ⊤ x trivial e = 1 ↔ x ∈ X.basicOpen e := by
  have ha := he.map (X.presheaf.germ ⊤ x trivial).hom
  rw [mem_basicOpen_top]
  exact ⟨fun h ↦ h ▸ isUnit_one, fun h ↦ (IsIdempotentElem.iff_eq_one_of_isUnit h).1 ha⟩

/-- The germ of an idempotent global section at a point outside its nonvanishing locus is `0`. -/
theorem germ_eq_zero_of_isIdempotentElem_of_notMem {e : Γ(X, ⊤)} (he : IsIdempotentElem e)
    (x : X) (hx : x ∉ X.basicOpen e) : X.presheaf.germ ⊤ x trivial e = 0 := by
  have hu := (IsLocalRing.isUnit_or_isUnit_one_sub_self _).resolve_left
    (by rwa [← mem_basicOpen_top] : ¬ IsUnit (X.presheaf.germ ⊤ x trivial e))
  exact hu.mul_left_eq_zero.1 (he.map (X.presheaf.germ ⊤ x trivial).hom).mul_one_sub_self

/-- The germ of an idempotent global section at `x` is `1` or `0` according as `x` lies in its
nonvanishing locus. -/
private theorem germ_eq_ite_of_isIdempotentElem {e : Γ(X, ⊤)} (he : IsIdempotentElem e) (x : X)
    [Decidable (x ∈ X.basicOpen e)] :
    X.presheaf.germ ⊤ x trivial e = if x ∈ X.basicOpen e then 1 else 0 := by
  split_ifs with hx
  exacts [(germ_eq_one_iff_mem_basicOpen_of_isIdempotentElem he x).2 hx,
    germ_eq_zero_of_isIdempotentElem_of_notMem he x hx]

/-- An idempotent global section is determined by its nonvanishing locus. -/
theorem eq_of_isIdempotentElem_of_basicOpen_eq {e e' : Γ(X, ⊤)} (he : IsIdempotentElem e)
    (he' : IsIdempotentElem e') (h : (X.basicOpen e : Set X) = X.basicOpen e') : e = e' := by
  classical
  refine TopCat.Presheaf.section_ext X.sheaf ⊤ e e' fun x _ ↦ ?_
  change X.presheaf.germ ⊤ x trivial e = X.presheaf.germ ⊤ x trivial e'
  rw [germ_eq_ite_of_isIdempotentElem he, germ_eq_ite_of_isIdempotentElem he']
  exact if_congr (Set.ext_iff.1 h x) rfl rfl

/-- **The idempotent of a clopen set exists.** A clopen subset of a scheme is the nonvanishing
locus of an idempotent global section. -/
theorem exists_isIdempotentElem_basicOpen_eq (U : Set X) (hU : IsClopen U) :
    ∃ e : Γ(X, ⊤), IsIdempotentElem e ∧ (X.basicOpen e : Set X) = U := by
  classical
  let W : ULift.{u} Bool → X.Opens := fun i ↦
    if i.down then ⟨U, hU.isOpen⟩ else ⟨Uᶜ, hU.isClosed.isOpen_compl⟩
  have hcover : ⊤ ≤ ⨆ i, W i := by
    intro x _
    rw [Opens.mem_iSup]
    by_cases hx : x ∈ U
    · exact ⟨⟨true⟩, hx⟩
    · exact ⟨⟨false⟩, hx⟩
  have hdisj : ∀ i j, i ≠ j → W i ⊓ W j = ⊥ := by
    rintro ⟨i⟩ ⟨j⟩ hij
    have hij' : i ≠ j := fun h ↦ hij (congrArg ULift.up h)
    rw [eq_bot_iff]
    intro x hx
    have h1 : x ∈ W ⟨i⟩ := hx.1
    have h2 : x ∈ W ⟨j⟩ := hx.2
    cases i <;> cases j
    · exact absurd rfl hij'
    · exact absurd (show x ∈ U from h2) (show x ∈ Uᶜ from h1)
    · exact absurd (show x ∈ U from h1) (show x ∈ Uᶜ from h2)
    · exact absurd rfl hij'
  have hbij := Stacks.AlgebraicGeometry.ProperGeomConnected.bijective_piRestrict W hcover hdisj
  obtain ⟨e, he⟩ := hbij.2 fun i ↦ if i.down then 1 else 0
  have hres : ∀ i, (X.presheaf.map (homOfLE (le_top : W i ≤ ⊤)).op).hom e =
      if i.down then 1 else 0 := fun i ↦ congrFun he i
  refine ⟨e, ?_, ?_⟩
  · apply hbij.1
    funext i
    simp only [RingHom.pi_apply, map_mul, hres i]
    by_cases hi : i.down <;> simp [hi]
  · ext x
    have hmem : x ∈ X.basicOpen e ↔ ∀ i (hxi : x ∈ W i),
        IsUnit (X.presheaf.germ (W i) x hxi
          ((X.presheaf.map (homOfLE (le_top : W i ≤ ⊤)).op).hom e)) := by
      rw [mem_basicOpen_top]
      refine ⟨fun h i hxi ↦ ?_, fun h ↦ ?_⟩
      · rwa [← CommRingCat.comp_apply, TopCat.Presheaf.germ_res]
      · obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hcover (Set.mem_univ x))
        have := h i hi
        rwa [← CommRingCat.comp_apply, TopCat.Presheaf.germ_res] at this
    change x ∈ X.basicOpen e ↔ x ∈ U
    rw [hmem]
    by_cases hx : x ∈ U
    · refine ⟨fun _ ↦ hx, fun _ i hxi ↦ ?_⟩
      rcases i with ⟨_ | _⟩
      · exact absurd hx hxi
      · rw [hres]; simp
    · refine ⟨fun h ↦ ?_, fun h ↦ absurd h hx⟩
      have := h ⟨false⟩ hx
      rw [hres] at this
      simp at this

/-- **The idempotent global section of a clopen set**: the section which is `1` on the set and
`0` on its complement. -/
noncomputable def clopenIdempotent (U : Set X) (hU : IsClopen U) : Γ(X, ⊤) :=
  (exists_isIdempotentElem_basicOpen_eq U hU).choose

/-- The section `clopenIdempotent U hU` is idempotent. -/
theorem isIdempotentElem_clopenIdempotent (U : Set X) (hU : IsClopen U) :
    IsIdempotentElem (clopenIdempotent U hU) :=
  (exists_isIdempotentElem_basicOpen_eq U hU).choose_spec.1

/-- The nonvanishing locus of `clopenIdempotent U hU` is `U`. -/
@[simp]
theorem coe_basicOpen_clopenIdempotent (U : Set X) (hU : IsClopen U) :
    (X.basicOpen (clopenIdempotent U hU) : Set X) = U :=
  (exists_isIdempotentElem_basicOpen_eq U hU).choose_spec.2

/-- An idempotent global section is the idempotent of its own nonvanishing locus. -/
theorem eq_clopenIdempotent_of_isIdempotentElem {e : Γ(X, ⊤)} (he : IsIdempotentElem e)
    (U : Set X) (hU : IsClopen U) (h : (X.basicOpen e : Set X) = U) :
    e = clopenIdempotent U hU :=
  eq_of_isIdempotentElem_of_basicOpen_eq he (isIdempotentElem_clopenIdempotent U hU)
    (by rw [h, coe_basicOpen_clopenIdempotent])

/-- **Pulling back the idempotent of a clopen set** along a morphism gives the idempotent of the
preimage. -/
theorem appTop_clopenIdempotent {Y : Scheme.{u}} (f : Y ⟶ X) (U : Set X) (hU : IsClopen U) :
    f.appTop (clopenIdempotent U hU) =
      clopenIdempotent (f ⁻¹' U) (hU.preimage f.continuous) := by
  refine eq_clopenIdempotent_of_isIdempotentElem ?_ _ _ ?_
  · change f.appTop _ * f.appTop _ = f.appTop _
    rw [← map_mul, isIdempotentElem_clopenIdempotent U hU]
  · rw [← preimage_basicOpen_top]
    change f ⁻¹' (X.basicOpen _ : Set X) = _
    rw [coe_basicOpen_clopenIdempotent]

/-- The "exclusive or" `e + e' - 2 e e'` of two idempotents of a commutative ring is
idempotent. -/
theorem isIdempotentElem_xor {R : Type*} [CommRing R] {e e' : R} (he : IsIdempotentElem e)
    (he' : IsIdempotentElem e') : IsIdempotentElem (e + e' - 2 * e * e') := by
  unfold IsIdempotentElem at he he' ⊢
  linear_combination (1 + 4 * e' * e' - 4 * e') * he + he'

/-- **The nonvanishing locus of an exclusive or** of two idempotent global sections is the
symmetric difference of their nonvanishing loci. -/
theorem coe_basicOpen_xor {e e' : Γ(X, ⊤)} (he : IsIdempotentElem e)
    (he' : IsIdempotentElem e') :
    (X.basicOpen (e + e' - 2 * e * e') : Set X) =
      symmDiff (X.basicOpen e : Set X) (X.basicOpen e') := by
  classical
  ext x
  change x ∈ X.basicOpen _ ↔ _
  rw [← germ_eq_one_iff_mem_basicOpen_of_isIdempotentElem (isIdempotentElem_xor he he') x]
  simp only [map_sub, map_add, map_mul, map_ofNat, Set.mem_symmDiff, SetLike.mem_coe]
  rw [germ_eq_ite_of_isIdempotentElem he, germ_eq_ite_of_isIdempotentElem he']
  by_cases h1 : x ∈ X.basicOpen e <;> by_cases h2 : x ∈ X.basicOpen e' <;> simp [h1, h2]
  norm_num

end AlgebraicGeometry.Scheme

end
