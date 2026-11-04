module

public import StacksFrontier.CategoryTheory.Localization.Saturated.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The smallest saturated multiplicative system containing a given one

Let `W` be a multiplicative system on a category `C` and let `Q : C ⥤ W⁻¹C` be the
localization functor. Consider the following classes of morphisms:

* `W.invertedClosure`, written `Ŝ`, the morphisms `f` of `C` for which
  `Q f` is an isomorphism;
* `W.satClosure`, written `S'`, the morphisms `f` admitting `g` and `h` with
  `W (f ≫ g)` and `W (h ≫ f)`.

They coincide, that `W ≤ W.invertedClosure`, that `W.invertedClosure` is a
saturated multiplicative system, and that it is the smallest one containing `W`; in
particular `W.invertedClosure = W` when `W` is already saturated.

The inclusion `W.satClosure ≤ W.invertedClosure` is formal: a morphism with a left and a
right inverse in the localization is invertible there. The converse is where the calculus
of fractions is used: writing the inverse of `Q f` as a fraction and cancelling produces
the required partner of `f` in `W` — once on the left, using the left calculus, and once on
the right, using the right one. That `W.invertedClosure` is again a multiplicative system is
proved by the same device: an `invertedClosure`-morphism `s` has a `W`-partner `s ≫ p`, so
an Ore square or a cancellation for `s` can be obtained from `W`'s own and transported back
along `W ≤ W.invertedClosure`.

Saturation — a multiplicative system satisfying MS4 — is `MorphismProperty.IsSaturated`. The
weaker conjunction of MS1 and MS4 is `IsSaturatedMultiplicative` below; the minimality statement
is proved for it as well, since MS4 is all that the argument uses.

## Main definitions

* `CategoryTheory.MorphismProperty.invertedClosure`: the morphisms inverted by the localization.
* `CategoryTheory.MorphismProperty.satClosure`: the morphisms with a `W`-partner on each side.
* `CategoryTheory.MorphismProperty.IsSaturatedMultiplicative`: MS1 together with MS4.

## Main results

* `CategoryTheory.MorphismProperty.invertedClosure_eq_satClosure`: `Ŝ = S'`.
* `CategoryTheory.MorphismProperty.isSaturated_invertedClosure`: `Ŝ` is a saturated
  multiplicative system.
* `CategoryTheory.MorphismProperty.invertedClosure_le_of_isSaturated`: `Ŝ` is the smallest
  saturated multiplicative system containing `W`.
* `CategoryTheory.MorphismProperty.IsSaturated.invertedClosure_eq`: `Ŝ = W` when `W` is
  saturated.

## References

* [Stacks, Tag 05Q9](https://stacks.math.columbia.edu/tag/05Q9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.MorphismProperty

namespace CategoryTheory.MorphismProperty

universe v u

variable {C : Type u} [Category.{v} C]

/-- A `MorphismProperty` `W` is multiplicative (MS1) and satisfies the saturation axiom
MS4: whenever `f ≫ g ∈ W` and `g ≫ h ∈ W` for composable `f, g, h`, also `g ∈ W`.

This is weaker than `IsSaturated`, which asks for a full multiplicative system, i.e. also the
Ore and cancellation conditions MS2 and MS3. -/
structure IsSaturatedMultiplicative (W : MorphismProperty C) : Prop
    extends W.IsMultiplicative where
  /-- MS4: if `f ≫ g` and `g ≫ h` lie in `W`, so does `g`. -/
  mem_of_comp_mem_comp :
    ∀ {X Y Z T : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T),
      W (f ≫ g) → W (g ≫ h) → W g

/-- A saturated multiplicative system is in particular multiplicative and satisfies MS4. -/
lemma IsSaturated.isSaturatedMultiplicative {W : MorphismProperty C} (hW : IsSaturated W) :
    IsSaturatedMultiplicative W :=
  { hW.isMultiplicative with mem_of_comp_mem_comp := hW.mem_of_comp_mem_comp }

/-- `Ŝ`: the morphisms of `C` that become isomorphisms in `W.Localization`. -/
@[sga "4 XVII 5.5.4.1" "partial", sga "5 V 2.4.5" "more general"]
def invertedClosure (W : MorphismProperty C) : MorphismProperty C :=
  (MorphismProperty.isomorphisms _).inverseImage W.Q

/-- A morphism lies in `Ŝ` exactly when `Q` sends it to an isomorphism. -/
lemma mem_invertedClosure_iff (W : MorphismProperty C) {X Y : C} (f : X ⟶ Y) :
    W.invertedClosure f ↔ IsIso (W.Q.map f) := by
  rw [invertedClosure, inverseImage_iff, isomorphisms.iff]

/-- `S'`: the morphisms `f` admitting both a left witness `g` with `f ≫ g ∈ W` and a right
witness `h` with `h ≫ f ∈ W`. -/
def satClosure (W : MorphismProperty C) : MorphismProperty C :=
  fun X Y f => (∃ (Z : C) (g : Y ⟶ Z), W (f ≫ g)) ∧ (∃ (T : C) (h : T ⟶ X), W (h ≫ f))

/-- A morphism with both a right- and a left-inverse is an isomorphism. -/
private lemma isIso_of_left_and_right_inverse {D : Type*} [Category D]
    {X Y : D} (f : X ⟶ Y) (s t : Y ⟶ X)
    (h1 : f ≫ s = 𝟙 X) (h2 : t ≫ f = 𝟙 Y) : IsIso f :=
  ⟨t, by
    rw [show t = s by rw [← Category.comp_id t, ← h1, ← Category.assoc, h2, Category.id_comp]]
    exact h1, h2⟩

/-- If `f ≫ g` and `g ≫ h` are isomorphisms, then so is `g`. -/
private lemma isIso_of_isIso_comp_of_isIso_comp {D : Type*} [Category D]
    {X Y Z T : D} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    (hfg : IsIso (f ≫ g)) (hgh : IsIso (g ≫ h)) : IsIso g :=
  isIso_of_left_and_right_inverse g (h ≫ inv (g ≫ h)) (inv (f ≫ g) ≫ f)
    (by rw [← Category.assoc]; exact IsIso.hom_inv_id _)
    (by rw [Category.assoc]; exact IsIso.inv_hom_id _)

/-- If `f ∈ satClosure W`, then `W.Q.map f` is an isomorphism. -/
private lemma isIso_Q_map_of_satClosure
    (W : MorphismProperty C) [W.IsMultiplicative]
    {X Y : C} (f : X ⟶ Y) (hf : W.satClosure f) :
    IsIso (W.Q.map f) := by
  obtain ⟨⟨_, g, hg⟩, ⟨_, h, hh⟩⟩ := hf
  refine isIso_of_isIso_comp_of_isIso_comp (W.Q.map h) (W.Q.map f) (W.Q.map g) ?_ ?_
  · rw [← W.Q.map_comp]; exact Localization.inverts W.Q W _ hh
  · rw [← W.Q.map_comp]; exact Localization.inverts W.Q W _ hg

/-- If `W.Q.map f` is an iso, then `f` admits a left witness `g` with `f ≫ g ∈ W`. -/
private lemma exists_postcomp_mem_of_isIso_Q_map
    (W : MorphismProperty C)
    [W.HasLeftCalculusOfFractions]
    {X Y : C} (f : X ⟶ Y) (hf : IsIso (W.Q.map f)) :
    ∃ (Z : C) (g : Y ⟶ Z), W (f ≫ g) := by
  obtain ⟨φ, hφ⟩ := Localization.exists_leftFraction W.Q W (inv (W.Q.map f))
  have : IsIso (W.Q.map φ.s) := Q_inverts W _ φ.hs
  have h1 : W.Q.map f ≫ (W.Q.map φ.f ≫ inv (W.Q.map φ.s)) = 𝟙 _ := by
    have htri : W.Q.map f ≫ inv (W.Q.map f) = 𝟙 _ := IsIso.hom_inv_id _
    rw [hφ] at htri
    exact htri
  have h2 : W.Q.map (f ≫ φ.f) = W.Q.map φ.s := by
    rw [Functor.map_comp]
    have h3 : (W.Q.map f ≫ W.Q.map φ.f) ≫ inv (W.Q.map φ.s) = 𝟙 _ := by
      rw [Category.assoc]
      exact h1
    rw [← IsIso.eq_comp_inv] at h3
    simpa using h3
  obtain ⟨Z, u, hu, heq⟩ := (map_eq_iff_postcomp W.Q W (f ≫ φ.f) φ.s).mp h2
  refine ⟨Z, φ.f ≫ u, ?_⟩
  rw [show f ≫ (φ.f ≫ u) = φ.s ≫ u by rw [← Category.assoc]; exact heq]
  exact W.comp_mem _ _ φ.hs hu

/-- If `W.Q.map f` is an iso, then `f` admits a right witness `h` with `h ≫ f ∈ W`. -/
private lemma exists_precomp_mem_of_isIso_Q_map
    (W : MorphismProperty C)
    [W.HasRightCalculusOfFractions]
    {X Y : C} (f : X ⟶ Y) (hf : IsIso (W.Q.map f)) :
    ∃ (T : C) (h : T ⟶ X), W (h ≫ f) := by
  obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction W.Q W (inv (W.Q.map f))
  have : IsIso (W.Q.map φ.s) := Localization.inverts W.Q W _ φ.hs
  have hsf : W.Q.map φ.s ≫ inv (W.Q.map f) = W.Q.map φ.f := by
    rw [hφ]
    exact φ.map_s_comp_map _ _
  have key : W.Q.map (φ.f ≫ f) = W.Q.map φ.s := by
    rw [W.Q.map_comp, ← hsf, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [MorphismProperty.map_eq_iff_precomp W.Q W _ _] at key
  obtain ⟨T, s, hs, hseq⟩ := key
  refine ⟨T, s ≫ φ.f, ?_⟩
  rw [Category.assoc, hseq]
  exact W.comp_mem _ _ hs φ.hs

variable (W : MorphismProperty C)
    [W.HasLeftCalculusOfFractions] [W.HasRightCalculusOfFractions]

/-- `Ŝ = S'`: a morphism becomes invertible in the localization exactly
when it has a `W`-partner on each side. -/
@[stacks 05Q9]
theorem invertedClosure_eq_satClosure : W.invertedClosure = W.satClosure := by
  ext X Y f
  exact ⟨fun hf => ⟨exists_postcomp_mem_of_isIso_Q_map W f hf,
    exists_precomp_mem_of_isIso_Q_map W f hf⟩, isIso_Q_map_of_satClosure W f⟩

omit [W.HasLeftCalculusOfFractions] [W.HasRightCalculusOfFractions] in
/-- `W ≤ Ŝ`: every morphism of `W` is inverted by `Q`. -/
@[stacks 05Q9]
theorem le_invertedClosure : W ≤ W.invertedClosure :=
  fun _ _ f hf => Localization.inverts W.Q W f hf

omit [W.HasLeftCalculusOfFractions] [W.HasRightCalculusOfFractions] in
/-- `Ŝ` is multiplicative and satisfies MS4. -/
theorem isSaturatedMultiplicative_invertedClosure :
    IsSaturatedMultiplicative W.invertedClosure := by
  refine { id_mem := ?_, comp_mem := ?_, mem_of_comp_mem_comp := ?_ }
  · intro X
    rw [mem_invertedClosure_iff, W.Q.map_id]
    infer_instance
  · intro X Y Z f g hf hg
    rw [mem_invertedClosure_iff] at hf hg ⊢
    rw [W.Q.map_comp]
    infer_instance
  · intro X Y Z T f g h hfg hgh
    rw [mem_invertedClosure_iff] at hfg hgh ⊢
    rw [W.Q.map_comp] at hfg hgh
    exact isIso_of_isIso_comp_of_isIso_comp _ _ _ hfg hgh

/-- `Ŝ` has a left calculus of fractions. -/
theorem hasLeftCalculusOfFractions_invertedClosure :
    W.invertedClosure.HasLeftCalculusOfFractions := by
  have : W.invertedClosure.IsMultiplicative :=
    (isSaturatedMultiplicative_invertedClosure W).toIsMultiplicative
  have hchar : W.invertedClosure = W.satClosure := invertedClosure_eq_satClosure W
  apply MorphismProperty.HasLeftCalculusOfFractions.mk
  · intro X Y φ
    have hs : W.satClosure φ.s := hchar ▸ φ.hs
    obtain ⟨⟨Z, p, hp⟩, -⟩ := hs
    let ψ₀ : W.RightFraction Z Y := MorphismProperty.RightFraction.mk (φ.s ≫ p) hp φ.f
    obtain ⟨ψ, hψ⟩ := MorphismProperty.HasLeftCalculusOfFractions.exists_leftFraction ψ₀
    refine ⟨MorphismProperty.LeftFraction.mk (p ≫ ψ.f) ψ.s
      (le_invertedClosure W ψ.s ψ.hs), ?_⟩
    dsimp [ψ₀, MorphismProperty.RightFraction.mk] at hψ
    rw [← Category.assoc]
    exact hψ
  · intro X' X Y f₁ f₂ s hs hcomp
    have hs' : W.satClosure s := hchar ▸ hs
    obtain ⟨-, ⟨T, h, hh⟩⟩ := hs'
    have hu : (h ≫ s) ≫ f₁ = (h ≫ s) ≫ f₂ := by
      rw [Category.assoc, Category.assoc, hcomp]
    obtain ⟨Y', t, ht, hft⟩ :=
      MorphismProperty.HasLeftCalculusOfFractions.ext (W := W) f₁ f₂ (h ≫ s) hh hu
    exact ⟨Y', t, le_invertedClosure W t ht, hft⟩

/-- `Ŝ` has a right calculus of fractions. -/
theorem hasRightCalculusOfFractions_invertedClosure :
    W.invertedClosure.HasRightCalculusOfFractions := by
  have : W.invertedClosure.IsMultiplicative :=
    (isSaturatedMultiplicative_invertedClosure W).toIsMultiplicative
  have hchar : W.invertedClosure = W.satClosure := invertedClosure_eq_satClosure W
  apply MorphismProperty.HasRightCalculusOfFractions.mk
  · intro X Y φ
    have hs : W.satClosure φ.s := hchar ▸ φ.hs
    obtain ⟨-, ⟨T, h, hh⟩⟩ := hs
    let χ₀ : W.LeftFraction X T := MorphismProperty.LeftFraction.mk φ.f (h ≫ φ.s) hh
    obtain ⟨χ, hχ⟩ := MorphismProperty.HasRightCalculusOfFractions.exists_rightFraction χ₀
    refine ⟨MorphismProperty.RightFraction.mk χ.s (le_invertedClosure W χ.s χ.hs)
      (χ.f ≫ h), ?_⟩
    dsimp [χ₀, MorphismProperty.LeftFraction.mk] at hχ
    rw [Category.assoc]
    exact hχ
  · intro X Y Y' f₁ f₂ s hs hcomp
    have hs' : W.satClosure s := hchar ▸ hs
    obtain ⟨⟨Z, p, hp⟩, -⟩ := hs'
    have hu : f₁ ≫ (s ≫ p) = f₂ ≫ (s ≫ p) := by
      rw [← Category.assoc, ← Category.assoc, hcomp]
    obtain ⟨X', t, ht, hft⟩ :=
      MorphismProperty.HasRightCalculusOfFractions.ext (W := W) f₁ f₂ (s ≫ p) hp hu
    exact ⟨X', t, le_invertedClosure W t ht, hft⟩

/-- `Ŝ` is itself a saturated multiplicative system: it has a left and a right calculus of
fractions and satisfies MS4. -/
@[stacks 05Q9]
theorem isSaturated_invertedClosure : IsSaturated W.invertedClosure where
  hasLeftCalculusOfFractions := hasLeftCalculusOfFractions_invertedClosure W
  hasRightCalculusOfFractions := hasRightCalculusOfFractions_invertedClosure W
  mem_of_comp_mem_comp := (isSaturatedMultiplicative_invertedClosure W).mem_of_comp_mem_comp

/-- Minimality of `Ŝ`, in the strongest form the argument gives: `Ŝ` is contained in every
`W'` containing `W` that is multiplicative and satisfies MS4. -/
theorem invertedClosure_le_of_isSaturatedMultiplicative (W' : MorphismProperty C)
    (hW' : IsSaturatedMultiplicative W') (hWW' : W ≤ W') : W.invertedClosure ≤ W' := by
  intro X Y f hf
  rw [invertedClosure_eq_satClosure] at hf
  obtain ⟨⟨Z, g, hg⟩, ⟨T, h, hh⟩⟩ := hf
  exact hW'.mem_of_comp_mem_comp h f g (hWW' _ hh) (hWW' _ hg)

/-- `Ŝ` is the *smallest* saturated multiplicative system containing `W`:
it is contained in every saturated multiplicative system containing `W`. -/
@[stacks 05Q9]
theorem invertedClosure_le_of_isSaturated (W' : MorphismProperty C)
    (hW' : IsSaturated W') (hWW' : W ≤ W') : W.invertedClosure ≤ W' :=
  invertedClosure_le_of_isSaturatedMultiplicative W W' hW'.isSaturatedMultiplicative hWW'

/-- If `W` is already saturated then `Ŝ = W`. -/
@[stacks 05Q9]
theorem IsSaturated.invertedClosure_eq (hW : IsSaturated W) :
    W.invertedClosure = W :=
  le_antisymm (invertedClosure_le_of_isSaturated W W hW le_rfl) (le_invertedClosure W)

end CategoryTheory.MorphismProperty
