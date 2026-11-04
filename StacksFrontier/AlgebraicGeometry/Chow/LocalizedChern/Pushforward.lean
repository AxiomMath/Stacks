module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.ClosedCover
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ProperPushforwardOfInvertible

/-!
# Pushing forward the extension of a class from one member of a closed cover

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme locally
of finite type over `S`, and let `i₁ : X₁ ⟶ X` and `i₂ : X₂ ⟶ X` be closed immersions whose images
cover `X`. A class `a ∈ A^p(X₂)` vanishing over `X₁ ×_X X₂` extends to a class
`a' ∈ A^p(X₂ ⟶ X)` (`Stacks.Chow.closedCoverExtension`, the construction of Stacks 0F9H). This
file proves the two compatibilities of the extension with proper pushforward (Stacks 0EPK) which
the source records as Stacks 0F9I and Stacks 0FAI, for every class `a`.

* If `q ∈ A^p(X)` vanishes over `X₁`, then its restriction `q|_{X₂}` vanishes over `X₁ ×_X X₂`,
  and `i_{2,*} ∘ (q|_{X₂})' = q` in `A^p(X)`. Indeed, writing a class on a test scheme as
  `α = j_{1,*} α₁ + j_{2,*} α₂`, the left side caps it to `j_{2,*}(q ∩ α₂)`, and so does the
  right side, because `q ∩ j_{1,*} α₁ = j_{1,*}(q ∩ α₁) = 0` by proper naturality of `q`.
* If `j : X'₂ ⟶ X₂` and `i'₁ : X'₁ ⟶ X` are closed immersions with `X = X'₁ ∪ X'₂` and `a`
  vanishes over `X'₁ ×_X X₂`, then `j_* ∘ (a|_{X'₂})' = a'`, the extension on the left being
  taken along the cover `X = X'₁ ∪ X'₂`. Both sides satisfy the two formulas characterizing the
  extension of `a` along the cover `X = X'₁ ∪ X₂`.

## Main definitions

* `Stacks.Chow.properPushforwardChowCohomology` — for a proper `f : Y ⟶ X` and
  `c ∈ A^p(Y ⟶ X)`, the class `f_* ∘ c ∈ A^p(X)` of Stacks 0EPK.

## Main results

* `Stacks.Chow.idRule_properPushforwardChowCohomology` — the operation of `f_* ∘ c` on a test
  scheme `T ⟶ X` is `α ↦ f'_*(c ∩ α)`, with `f' : Y ×_X T ⟶ T` the base change of `f`.
* `Stacks.Chow.chowPush_pullbackSnd_bivariantProperPushforward_cap` — pushed forward to the test
  scheme, the cap product of `f₁_* ∘ c` is that of `c`.
* `Stacks.Chow.BivariantClass.idRule_chowPush_of_eq` — proper naturality of the operation of a
  class of `A^p(Z)`, for an arbitrary structure morphism of the source.
* `Stacks.Chow.BivariantClass.VanishesOver.chowCohomologyRestriction_of_comp` — a class vanishing
  over `z : W ⟶ Z` restricts, along `Z' ⟶ Z`, to a class vanishing over every `W' ⟶ Z'` whose
  composite to `Z` factors through `z`.
* `Stacks.Chow.chowPush_closedCoverExtension_cap` and
  `Stacks.Chow.properPushforwardChowCohomology_closedCoverExtension` — the generic form of
  Stacks 0F9I: `i_{2,*} ∘ (q|_{X₂})' = q`.
* `Stacks.Chow.closedCoverExtension_chowCohomologyRestriction_add` — `(q|_{X₂})'` is additive
  in `q`.
* `Stacks.Chow.bivariantProperPushforward_closedCoverExtension` — the generic form of
  Stacks 0FAI: `j_* ∘ (a|_{X'₂})' = a'`.

## Implementation notes

The source states Stacks 0F9I and Stacks 0FAI for the localized Chern classes `P'_p(E₂)` and
`c'_p(E₂)` of a perfect object; those are the extensions of the classes `P_p(E₂)` and `c_p(E₂)`,
and the two statements hold for the extension of every class satisfying the vanishing hypothesis.
They are proved here in that generality, from which the statements of the source follow by
specialization.

In Stacks 0FAI the source assumes `X₁ ⊆ X'₁`; it is used only to see that the extension `a'`
along `X = X₁ ∪ X₂` is defined, which here is part of the data, and the extension does not depend
on the first member of the cover (`Stacks.Chow.closedCoverExtension_eq_of_closedCover`), so the
inclusion is not needed.

## References

* [Stacks Project, Tag 0F9H](https://stacks.math.columbia.edu/tag/0F9H)
* [Stacks Project, Tag 0F9I](https://stacks.math.columbia.edu/tag/0F9I)
* [Stacks Project, Tag 0FAI](https://stacks.math.columbia.edu/tag/0FAI)
* [Stacks Project, Tag 0EPK](https://stacks.math.columbia.edu/tag/0EPK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The pushforward of a bivariant class to a Chow cohomology class -/

section PushforwardChowCohomology

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : Y ⟶ X) [IsProper f] (hf : f ≫ sX = sY) {p : ℤ}

/-- **Stacks 0EPK for `𝟙 X`.** For a proper morphism `f : Y ⟶ X` and a class
`c ∈ A^p(Y ⟶ X)`, the class `f_* ∘ c ∈ A^p(X) = A^p(X ⟶ X)`; the class `c` is read as a class for
`f ≫ 𝟙 X`. -/
abbrev properPushforwardChowCohomology
    (c : BivariantClass C (gysinSystemOfInvertible C) sY sX f hf p) :
    chowCohomologyComponent C (gysinSystemOfInvertible C) sX p :=
  bivariantProperPushforwardOfInvertible C sY sX sX f (𝟙 X) hf (Category.id_comp sX) p
    (c.congrHom (Category.comp_id f).symm
      (comp_comp_structureMorphism_eq hf (Category.id_comp sX)))

/-- The operation of `f_* ∘ c ∈ A^p(X)` on a test scheme `g : T ⟶ X` is `α ↦ f'_*(c ∩ α)`, with
`f' : Y ×_X T ⟶ T` the base change of `f`. -/
theorem idRule_properPushforwardChowCohomology
    (c : BivariantClass C (gysinSystemOfInvertible C) sY sX f hf p) {T : Scheme.{u}}
    (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sX) k) :
    (properPushforwardChowCohomology C sX sY f hf c).idRule C sX (gysinSystemOfInvertible C) g k
        α =
      chowPush C (pullback.fst f g ≫ sY) (g ≫ sX) (pullback.snd f g)
        (pullbackSnd_comp_structureMorphism hf g) (k - p) (c.cap g k α) := by
  have hu := pullback_congrHom_hom_comp_fst_comp (sX := sY) (Category.comp_id f).symm g
  have hv := bivariantPushforwardBaseChange_comp_structure hf (𝟙 X) g
  have hw := pullbackSnd_comp_structureMorphism (Category.id_comp sX) g
  have hvw : (bivariantPushforwardBaseChange f (𝟙 X) g ≫ pullback.snd (𝟙 X) g) ≫ (g ≫ sX) =
      pullback.fst (f ≫ 𝟙 X) g ≫ sY := by
    rw [Category.assoc, hw, hv]
  have huvw : ((pullback.congrHom (Category.comp_id f).symm rfl).hom ≫
      bivariantPushforwardBaseChange f (𝟙 X) g ≫ pullback.snd (𝟙 X) g) ≫ (g ≫ sX) =
        pullback.fst f g ≫ sY := by
    rw [Category.assoc, hvw, hu]
  have hmor : (pullback.congrHom (Category.comp_id f).symm rfl).hom ≫
      bivariantPushforwardBaseChange f (𝟙 X) g ≫ pullback.snd (𝟙 X) g = pullback.snd f g := by
    simp
  rw [BivariantClass.idRule_apply, bivariantProperPushforwardOfInvertible_cap,
    bivariantProperPushforwardCap_apply, BivariantClass.congrHom_cap]
  exact (properChowPushforward_comp₃_apply C (pullback.fst f g ≫ sY)
    (pullback.fst (f ≫ 𝟙 X) g ≫ sY) (pullback.fst (𝟙 X) g ≫ sX) (g ≫ sX)
    (pullback.congrHom (Category.comp_id f).symm rfl).hom
    (bivariantPushforwardBaseChange f (𝟙 X) g) (pullback.snd (𝟙 X) g) hu hv hw hvw huvw (k - p)
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    (c.cap g k α)).symm.trans (chowPush_congr C _ _ hmor _ _ (k - p) (c.cap g k α))

/-- Pushing the cap product of `f₁_* ∘ c` forward along the base change of `f₂` is pushing the cap
product of `c ∈ A^p(E ⟶ X)` forward along the base change of `f₁ ≫ f₂`, for proper morphisms
`f₁ : E ⟶ Y` and `f₂ : Y ⟶ X`. -/
theorem chowPush_pullbackSnd_bivariantProperPushforward_cap {E : Scheme.{u}} (sE : E ⟶ C.S)
    [LocallyOfFiniteType sE] (f₁ : E ⟶ Y) [IsProper f₁] (hf₁ : f₁ ≫ sY = sE)
    (c : BivariantClass C (gysinSystemOfInvertible C) sE sX (f₁ ≫ f)
      (comp_comp_structureMorphism_eq hf₁ hf) p) {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sX) k) :
    chowPush C (pullback.fst f g ≫ sY) (g ≫ sX) (pullback.snd f g)
        (pullbackSnd_comp_structureMorphism hf g) (k - p)
        ((bivariantProperPushforwardOfInvertible C sE sY sX f₁ f hf₁ hf p c).cap g k α) =
      chowPush C (pullback.fst (f₁ ≫ f) g ≫ sE) (g ≫ sX) (pullback.snd (f₁ ≫ f) g)
        (pullbackSnd_comp_structureMorphism (comp_comp_structureMorphism_eq hf₁ hf) g) (k - p)
        (c.cap g k α) := by
  rw [bivariantProperPushforwardOfInvertible_cap, bivariantProperPushforwardCap_apply]
  exact chowPush_comp C _ _ _ (bivariantPushforwardBaseChange f₁ f g) (pullback.snd f g) _
    (bivariantPushforwardBaseChange_snd f₁ f g) _ _ _ (k - p) (c.cap g k α)

end PushforwardChowCohomology

/-! ### Restriction and vanishing -/

section Restriction

variable {C : ChowSituation.{u}} {Z Z' W W' : Scheme.{u}} {sZ : Z ⟶ C.S}
  [LocallyOfFiniteType sZ] {p : ℤ}

/-- The operation of a class `a ∈ A^p(Z)` on a pushforward along a proper morphism `h : T' ⟶ T`
of test schemes, the structure morphism of `T'` being an arbitrary one equal to `m ≫ sZ`. -/
theorem BivariantClass.idRule_chowPush_of_eq
    (a : chowCohomologyComponent C (gysinSystemOfInvertible C) sZ p) {T T' : Scheme.{u}}
    (g : T ⟶ Z) [LocallyOfFiniteType g] (h : T' ⟶ T) [IsProper h] (m : T' ⟶ Z)
    [LocallyOfFiniteType m] (hm : h ≫ g = m) (sT' : T' ⟶ C.S) [LocallyOfFiniteType sT']
    (hs : m ≫ sZ = sT') (hh : h ≫ g ≫ sZ = sT') (k : ℤ) (x : chowGroup C sT' k) :
    a.idRule C sZ (gysinSystemOfInvertible C) g k (chowPush C sT' (g ≫ sZ) h hh k x) =
      chowPush C sT' (g ≫ sZ) h hh (k - p)
        (chowGroupCongr C hs (k - p)
          (a.idRule C sZ (gysinSystemOfInvertible C) m k (chowGroupCongr C hs.symm k x))) := by
  subst hs
  exact a.idRule_chowPush C _ sZ g h m hm k x

/-- A class `a ∈ A^p(Z)` vanishing over `z : W ⟶ Z` restricts, along `f : Z' ⟶ Z`, to a class of
`A^p(Z')` vanishing over every `w : W' ⟶ Z'` such that `w ≫ f` factors through `z`. -/
theorem BivariantClass.VanishesOver.chowCohomologyRestriction_of_comp
    {a : chowCohomologyComponent C (gysinSystemOfInvertible C) sZ p} {z : W ⟶ Z}
    [LocallyOfFiniteType z] (ha : BivariantClass.VanishesOver a z) (f : Z' ⟶ Z)
    [LocallyOfFiniteType f] (w : W' ⟶ Z') [LocallyOfFiniteType w] (l : W' ⟶ W)
    (hl : l ≫ z = w ≫ f) :
    BivariantClass.VanishesOver
      (Stacks.Chow.chowCohomologyRestriction C (gysinSystemOfInvertible C) sZ f p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) a) w := by
  intro T t _ k α
  refine chowPushforwardOfIso_injective C _ _ (pullback.snd (𝟙 _) _)
    (pullbackSnd_comp_structureMorphism (Category.id_comp _) _) (k - p) ?_
  rw [map_zero]
  show BivariantClass.idRule C (f ≫ sZ) (gysinSystemOfInvertible C) _ _ k α = 0
  rw [chowCohomologyRestriction_idRule]
  exact ha.idRule_eq_zero (t ≫ l) _ (by rw [Category.assoc, hl, Category.assoc]) k _

end Restriction

/-! ### The generic form of Stacks 0F9I -/

section RestrictionExtension

variable (C : ChowSituation.{u}) {X X₁ X₂ : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (i₁ : X₁ ⟶ X) (i₂ : X₂ ⟶ X) [IsClosedImmersion i₁]
  [IsClosedImmersion i₂] {p : ℤ} {q : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p}

/-- If `q ∈ A^p(X)` vanishes over `X₁`, its restriction to `X₂` vanishes over `X₁ ×_X X₂`. -/
theorem BivariantClass.VanishesOver.chowCohomologyRestriction_snd
    (hq : BivariantClass.VanishesOver q i₁) :
    BivariantClass.VanishesOver
      (Stacks.Chow.chowCohomologyRestriction C (gysinSystemOfInvertible C) sX i₂ p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) q) (pullback.snd i₁ i₂) :=
  hq.chowCohomologyRestriction_of_comp i₂ (pullback.snd i₁ i₂) (pullback.fst i₁ i₂)
    pullback.condition

/-- **The generic form of Stacks 0F9I, on the test schemes.** Let `q ∈ A^p(X)` vanish over `X₁`.
On every test scheme `g : T ⟶ X`, pushing the cap product of the extension of `q|_{X₂}` forward
along `T ×_X X₂ ⟶ T` is the operation of `q`. -/
theorem chowPush_closedCoverExtension_cap (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)
    (hq : BivariantClass.VanishesOver q i₁) {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sX) k) :
    chowPush C (pullback.fst i₂ g ≫ (i₂ ≫ sX)) (g ≫ sX) (pullback.snd i₂ g)
        (pullbackSnd_comp_structureMorphism rfl g) (k - p)
        ((closedCoverExtension C sX i₁ i₂ (i₂ ≫ sX) rfl
          (Stacks.Chow.chowCohomologyRestriction C (gysinSystemOfInvertible C) sX i₂ p
            (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) q) hcover
          (hq.chowCohomologyRestriction_snd C sX i₁ i₂)).cap g k α) =
      q.idRule C sX (gysinSystemOfInvertible C) g k α := by
  obtain ⟨⟨α₁, α₂⟩, rfl⟩ := surjective_closedCoverPullbackSum C sX i₁ i₂ (i₂ ≫ sX) rfl hcover g k α
  rw [closedCoverSum_apply]
  dsimp only
  rw [map_add, map_add, closedCoverExtension_cap_first,
    closedCoverExtension_cap_second, map_zero, zero_add, map_add,
    BivariantClass.idRule_chowPush_of_eq q g (pullback.snd i₁ g) (pullback.fst i₁ g ≫ i₁)
      pullback.condition.symm _ (Category.assoc _ _ _),
    hq.idRule_eq_zero (pullback.fst i₁ g) _ rfl, map_zero, map_zero, zero_add,
    BivariantClass.idRule_chowPush_of_eq q g (pullback.snd i₂ g) (pullback.fst i₂ g ≫ i₂)
      pullback.condition.symm _ (Category.assoc _ _ _),
    chowCohomologyRestriction_idRule]
  rfl

/-- **The generic form of Stacks 0F9I.** Let `i₁ : X₁ ⟶ X` and `i₂ : X₂ ⟶ X` be closed immersions
whose images cover `X`, and let `q ∈ A^p(X)` vanish over `X₁`. Then the restriction `q|_{X₂}`
vanishes over `X₁ ×_X X₂`, and its extension `(q|_{X₂})' ∈ A^p(X₂ ⟶ X)` along the cover satisfies
`i_{2,*} ∘ (q|_{X₂})' = q` in `A^p(X)`. -/
theorem properPushforwardChowCohomology_closedCoverExtension
    (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ) (hq : BivariantClass.VanishesOver q i₁) :
    properPushforwardChowCohomology C sX (i₂ ≫ sX) i₂ rfl
        (closedCoverExtension C sX i₁ i₂ (i₂ ≫ sX) rfl
          (Stacks.Chow.chowCohomologyRestriction C (gysinSystemOfInvertible C) sX i₂ p
            (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) q) hcover
          (hq.chowCohomologyRestriction_snd C sX i₁ i₂)) = q :=
  BivariantClass.eq_of_idRule_eq C sX _ _ _ fun g _ k α ↦ by
    rw [idRule_properPushforwardChowCohomology]
    exact chowPush_closedCoverExtension_cap C sX i₁ i₂ hcover hq g k α

/-- The extension of the restriction to `X₂` is additive: for `q₃ = q₁ + q₂`, the extension of
`q₃|_{X₂}` is the sum of the extensions of `q₁|_{X₂}` and `q₂|_{X₂}`. -/
theorem closedCoverExtension_chowCohomologyRestriction_add
    (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)
    {q₁ q₂ q₃ : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p} (h : q₃ = q₁ + q₂)
    (ha₁ : BivariantClass.VanishesOver
      (Stacks.Chow.chowCohomologyRestriction C (gysinSystemOfInvertible C) sX i₂ p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) q₁) (pullback.snd i₁ i₂))
    (ha₂ : BivariantClass.VanishesOver
      (Stacks.Chow.chowCohomologyRestriction C (gysinSystemOfInvertible C) sX i₂ p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) q₂) (pullback.snd i₁ i₂))
    (ha₃ : BivariantClass.VanishesOver
      (Stacks.Chow.chowCohomologyRestriction C (gysinSystemOfInvertible C) sX i₂ p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) q₃) (pullback.snd i₁ i₂)) :
    closedCoverExtension C sX i₁ i₂ (i₂ ≫ sX) rfl
        (Stacks.Chow.chowCohomologyRestriction C (gysinSystemOfInvertible C) sX i₂ p
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) q₃) hcover ha₃ =
      closedCoverExtension C sX i₁ i₂ (i₂ ≫ sX) rfl
          (Stacks.Chow.chowCohomologyRestriction C (gysinSystemOfInvertible C) sX i₂ p
            (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) q₁) hcover ha₁ +
        closedCoverExtension C sX i₁ i₂ (i₂ ≫ sX) rfl
          (Stacks.Chow.chowCohomologyRestriction C (gysinSystemOfInvertible C) sX i₂ p
            (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) q₂) hcover ha₂ := by
  subst h
  rw [← closedCoverExtension_add]
  congr 1
  exact map_add _ _ _

end RestrictionExtension

/-! ### The generic form of Stacks 0FAI -/

section SmallerCover

variable (C : ChowSituation.{u}) {X X₁ X₁' X₂ X₂' : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (i₁ : X₁ ⟶ X) (i₁' : X₁' ⟶ X) (i₂ : X₂ ⟶ X) (j : X₂' ⟶ X₂)
  [IsClosedImmersion i₁] [IsClosedImmersion i₁'] [IsClosedImmersion i₂] [IsClosedImmersion j]
  (sX₂ : X₂ ⟶ C.S) [LocallyOfFiniteType sX₂] (hi₂ : i₂ ≫ sX = sX₂) {p : ℤ}
  {a : chowCohomologyComponent C (gysinSystemOfInvertible C) sX₂ p}

omit [IsClosedImmersion i₂] in
/-- If `a ∈ A^p(X₂)` vanishes over `X'₁ ×_X X₂`, its restriction to a closed subscheme
`j : X'₂ ⟶ X₂` vanishes over `X'₁ ×_X X'₂`. -/
theorem BivariantClass.VanishesOver.chowCohomologyRestriction_pullbackSnd
    (ha : BivariantClass.VanishesOver a (pullback.snd i₁' i₂)) :
    BivariantClass.VanishesOver
      (Stacks.Chow.chowCohomologyRestriction C (gysinSystemOfInvertible C) sX₂ j p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) a) (pullback.snd i₁' (j ≫ i₂)) :=
  ha.chowCohomologyRestriction_of_comp j (pullback.snd i₁' (j ≫ i₂))
    (pullback.lift (pullback.fst i₁' (j ≫ i₂)) (pullback.snd i₁' (j ≫ i₂) ≫ j)
      (by rw [pullback.condition, Category.assoc]))
    (pullback.lift_snd _ _ _)

/-- **The generic form of Stacks 0FAI.** Let `X = X₁ ∪ X₂` be a closed cover, `a ∈ A^p(X₂)` a
class vanishing over `X₁ ×_X X₂`, and `a' ∈ A^p(X₂ ⟶ X)` its extension. Let `j : X'₂ ⟶ X₂` and
`i'₁ : X'₁ ⟶ X` be closed immersions with `X = X'₁ ∪ X'₂`, such that `a` vanishes over
`X'₁ ×_X X₂`. Then the restriction `a|_{X'₂}` vanishes over `X'₁ ×_X X'₂`, and its extension along
the cover `X = X'₁ ∪ X'₂` pushes forward to `a'`: `j_* ∘ (a|_{X'₂})' = a'` in `A^p(X₂ ⟶ X)`. -/
theorem bivariantProperPushforward_closedCoverExtension
    (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)
    (ha : BivariantClass.VanishesOver a (pullback.snd i₁ i₂))
    (hcover' : Set.range i₁' ∪ Set.range (j ≫ i₂) = Set.univ)
    (ha' : BivariantClass.VanishesOver a (pullback.snd i₁' i₂)) :
    bivariantProperPushforwardOfInvertible C (j ≫ sX₂) sX₂ sX j i₂ rfl hi₂ p
        (closedCoverExtension C sX i₁' (j ≫ i₂) (j ≫ sX₂) (by rw [Category.assoc, hi₂])
          (Stacks.Chow.chowCohomologyRestriction C (gysinSystemOfInvertible C) sX₂ j p
            (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) a) hcover'
          (ha'.chowCohomologyRestriction_pullbackSnd C i₁' i₂ j)) =
      closedCoverExtension C sX i₁ i₂ sX₂ hi₂ a hcover ha := by
  have hj₂ : (j ≫ i₂) ≫ sX = j ≫ sX₂ := by rw [Category.assoc, hi₂]
  have hcover₂ : Set.range i₁' ∪ Set.range i₂ = Set.univ := by
    refine Set.eq_univ_of_forall fun x ↦ ?_
    rcases (hcover' ▸ Set.mem_univ x : x ∈ Set.range i₁' ∪ Set.range (j ≫ i₂)) with h | ⟨y, rfl⟩
    · exact Or.inl h
    · exact Or.inr ⟨j y, rfl⟩
  rw [closedCoverExtension_eq_of_closedCover C sX i₁ i₁' i₂ sX₂ hi₂ hcover hcover₂ ha ha']
  refine IsClosedCoverExtension.eq_closedCoverExtension hcover₂ ha'
    ⟨fun {T} g _ k α ↦ ?_, fun {T} g _ k α ↦ ?_⟩
  · -- classes pushed forward from `T ×_X X₂`
    have hb : pullback.fst i₂ g ≫ sX₂ = (pullback.snd i₂ g ≫ g) ≫ sX := by
      rw [Category.assoc, pullbackSnd_comp_structureMorphism hi₂ g]
    obtain ⟨γ, rfl⟩ : ∃ γ, α = chowGroupCongr C hb.symm k γ :=
      ⟨chowGroupCongr C hb k α, by rw [chowGroupCongr_chowGroupCongr]; rfl⟩
    obtain ⟨⟨β₁, β₂⟩, rfl⟩ := surjective_closedCoverPullbackSum C sX i₁' (j ≫ i₂) (j ≫ sX₂) hj₂
      hcover' (pullback.snd i₂ g ≫ g) k γ
    have hm : ∀ {Y : Scheme.{u}} (i : Y ⟶ X), pullback.fst i (pullback.snd i₂ g ≫ g) ≫ i =
        (pullback.snd i (pullback.snd i₂ g ≫ g) ≫ pullback.snd i₂ g) ≫ g := fun i ↦ by
      rw [pullback.condition, Category.assoc]
    have hmj : pullback.snd (j ≫ i₂) (pullback.snd i₂ g ≫ g) ≫ pullback.fst i₂ g =
        pullback.fst (j ≫ i₂) (pullback.snd i₂ g ≫ g) ≫ j := by
      refine (cancel_mono i₂).1 ?_
      rw [Category.assoc, pullback.condition (f := i₂) (g := g), Category.assoc, hm (j ≫ i₂),
        Category.assoc]
    have hl₁ : pullback.fst i₁' (pullback.snd i₂ g ≫ g) ≫ i₁' =
        (pullback.snd i₁' (pullback.snd i₂ g ≫ g) ≫ pullback.fst i₂ g) ≫ i₂ := by
      rw [pullback.condition (f := i₁'), Category.assoc, pullback.condition (f := i₂) (g := g)]
    have hlv : pullback.lift (pullback.fst (j ≫ i₂) (pullback.snd i₂ g ≫ g))
        (pullback.snd (j ≫ i₂) (pullback.snd i₂ g ≫ g) ≫ pullback.snd i₂ g) (hm _) ≫
          bivariantPushforwardBaseChange j i₂ g =
        pullback.snd (j ≫ i₂) (pullback.snd i₂ g ≫ g) := by
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, bivariantPushforwardBaseChange_fst, ← Category.assoc,
          pullback.lift_fst, hmj]
      · rw [Category.assoc, bivariantPushforwardBaseChange_snd, pullback.lift_snd]
    -- the class pushed forward to `T`, decomposed along the cover `X = X'₁ ∪ X'₂`
    have hL : chowPush C (pullback.fst i₂ g ≫ sX₂) (g ≫ sX) (pullback.snd i₂ g)
        (pullbackSnd_comp_structureMorphism hi₂ g) k
        (chowGroupCongr C hb.symm k (closedCoverPullbackSum C sX i₁' (j ≫ i₂) (j ≫ sX₂) hj₂
          (pullback.snd i₂ g ≫ g) k (β₁, β₂))) =
        chowPush C _ (g ≫ sX) (pullback.snd i₁' (pullback.snd i₂ g ≫ g) ≫ pullback.snd i₂ g)
          (by rw [← Category.assoc, ← hm i₁', Category.assoc]) k β₁ +
        chowPush C _ (g ≫ sX)
          (pullback.snd (j ≫ i₂) (pullback.snd i₂ g ≫ g) ≫ pullback.snd i₂ g)
          (by rw [← hj₂, ← Category.assoc, ← hm (j ≫ i₂), Category.assoc]) k β₂ := by
      rw [← properChowPushforward_chowGroupCongr C hb.symm rfl (pullback.snd i₂ g)
        (Category.assoc _ _ _).symm (pullbackSnd_comp_structureMorphism hi₂ g) k
        (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)]
      rw [closedCoverSum_apply]
      dsimp only
      rw [map_add]
      exact congrArg₂ (· + ·)
        (chowPush_comp C (pullback.fst i₁' (pullback.snd i₂ g ≫ g) ≫ (i₁' ≫ sX))
          ((pullback.snd i₂ g ≫ g) ≫ sX) (g ≫ sX) (pullback.snd i₁' (pullback.snd i₂ g ≫ g))
          (pullback.snd i₂ g) _ rfl _ _ _ k β₁)
        (chowPush_comp C (pullback.fst (j ≫ i₂) (pullback.snd i₂ g ≫ g) ≫ (j ≫ sX₂))
          ((pullback.snd i₂ g ≫ g) ≫ sX) (g ≫ sX)
          (pullback.snd (j ≫ i₂) (pullback.snd i₂ g ≫ g)) (pullback.snd i₂ g) _ rfl _ _ _ k β₂)
    -- the same class on `T ×_X X₂`
    have hR : chowGroupCongr C hb.symm k (closedCoverPullbackSum C sX i₁' (j ≫ i₂) (j ≫ sX₂) hj₂
          (pullback.snd i₂ g ≫ g) k (β₁, β₂)) =
        chowPush C _ (pullback.fst i₂ g ≫ sX₂) (pullback.snd i₁' (pullback.snd i₂ g ≫ g))
          (by rw [hb, pullbackSnd_comp_structureMorphism rfl]) k β₁ +
        chowPush C _ (pullback.fst i₂ g ≫ sX₂) (pullback.snd (j ≫ i₂) (pullback.snd i₂ g ≫ g))
          (by rw [hb, pullbackSnd_comp_structureMorphism hj₂]) k β₂ := by
      rw [closedCoverSum_apply]
      dsimp only
      rw [map_add]
      congr 1 <;> exact properChowPushforward_chowGroupCongr C rfl hb.symm _ _ _ k _ _ _
    rw [hL, hR]
    simp only [map_add, bivariantProperPushforwardOfInvertible_cap,
      bivariantProperPushforwardCap_apply, closedCoverExtension_cap]
    rw [closedCoverExtensionCap_chowPush_first C _ sX i₁' (j ≫ i₂) (j ≫ sX₂) hj₂ hcover' _ g
        _ _ (hm i₁') k β₁,
      closedCoverExtensionCap_chowPush_second C _ sX i₁' (j ≫ i₂) (j ≫ sX₂) hj₂ hcover' _ g
        _ _ (hm (j ≫ i₂)) k β₂, map_zero, zero_add,
      BivariantClass.idRule_chowPush_of_eq a (pullback.fst i₂ g)
        (pullback.snd i₁' (pullback.snd i₂ g ≫ g))
        (pullback.snd i₁' (pullback.snd i₂ g ≫ g) ≫ pullback.fst i₂ g) rfl _
        (by rw [← hi₂, ← Category.assoc, ← hl₁, Category.assoc]),
      ha'.idRule_eq_zero (pullback.lift _ _ hl₁) _ (pullback.lift_snd _ _ _), map_zero, map_zero,
      zero_add]
    refine Eq.trans ?_ (BivariantClass.idRule_chowPush_of_eq a (pullback.fst i₂ g)
      (pullback.snd (j ≫ i₂) (pullback.snd i₂ g ≫ g))
      (pullback.fst (j ≫ i₂) (pullback.snd i₂ g ≫ g) ≫ j) hmj _ (Category.assoc _ _ _) _ k
      β₂).symm
    rw [chowCohomologyRestriction_idRule]
    exact (properChowPushforward_comp_apply C _ _ _ _ _ _ hlv _ _ _ (k - p) _ _ _ _).symm
  · -- classes pushed forward from `T ×_X X'₁`
    rw [bivariantProperPushforwardOfInvertible_cap, bivariantProperPushforwardCap_apply,
      closedCoverExtension_cap_first, map_zero]

end SmallerCover

end Stacks.Chow

end
