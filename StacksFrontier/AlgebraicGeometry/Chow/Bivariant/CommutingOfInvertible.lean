module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Commuting
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.TotalClass
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Transport
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.ProperPushforwardDescent
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.BaseChangeIsoGysinSystem

/-!
# Commuting bivariant classes at the canonical Gysin system

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S` and for `i = 1, 2` let `fᵢ : Zᵢ ⟶ X` be a morphism of schemes
locally of finite type, with bivariant classes `cᵢ ∈ A^{pᵢ}(Zᵢ ⟶ X)`. **Stacks 0FA2** says that
`c₁` and `c₂` commute exactly when

  `res(c₁) ∘ c₂ = res(c₂) ∘ c₁`   in   `A^{p₁ + p₂}(Z₁ ×_X Z₂ ⟶ X)`,

where `res(c₁) ∈ A^{p₁}(Z₁ ×_X Z₂ ⟶ Z₂)` is the restriction of `c₁` along `f₂` (Stacks 0F9Z) and
similarly for `res(c₂)`.

This file states that equivalence for bivariant classes at the canonical Gysin system
`Stacks.Chow.gysinSystemOfInvertible`, the Gysin system of the first Chern class rule of an
invertible module. The restrictions are `Stacks.Chow.bivariantRestrictionOfInvertible` and the
composites `Stacks.Chow.bivariantCompositeOfInvertible`. The two composites live in
`A^{p₁ + p₂}(Z₁ ×_X Z₂ ⟶ X)` and `A^{p₂ + p₁}(Z₂ ×_X Z₁ ⟶ X)`, and the second is read in the
first along the symmetry `Z₂ ×_X Z₁ ≅ Z₁ ×_X Z₂` of the fibre product
(`Stacks.Chow.bivariantTransport`) and the equality `p₂ + p₁ = p₁ + p₂` of degrees
(`Stacks.Chow.bivariantClassDegreeCongr`).

## Main definitions

* `Stacks.Chow.commuteCompositeOfInvertible` — the composite `res(c₁) ∘ c₂`, a bivariant class in
  `A^{p₁ + p₂}(Z₁ ×_X Z₂ ⟶ X)`.

## Main results

* `Stacks.Chow.bivariantCommute_iff_commuteCompositeOfInvertible_eq` — **Stacks 0FA2**: `c₁` and
  `c₂` commute if and only if `res(c₁) ∘ c₂ = res(c₂) ∘ c₁` as bivariant classes in
  `A^{p₁ + p₂}(Z₁ ×_X Z₂ ⟶ X)`.

## References

* [Stacks Project, Tag 0FA2](https://stacks.math.columbia.edu/tag/0FA2)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- A transport of a bivariant class along an equality of degrees caps by the transport of its
cap operation along the induced equality of degrees. -/
theorem bivariantClassDegreeCongr_cap_eq (C : ChowSituation.{u}) (G : GysinSystem C)
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : f ≫ sY = sX) {p p' : ℤ}
    (h : p = p') (c : BivariantClass C G sX sY f hf p) {T : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sY) k) :
    (bivariantClassDegreeCongr C G sX sY f hf h c).cap g k α =
      chowGroupDegreeEquiv C (pullback.fst f g ≫ sX) (by rw [h]) (c.cap g k α) := by
  subst h
  rfl

/-- Pushing forward along an isomorphism `e` over the base, after transporting along equalities
of degrees, matches a class exactly when the class is the pushforward of it along an inverse
`e'` of `e`, transported along the remaining equality of degrees. -/
theorem chowPushforwardOfIso_chowGroupDegreeEquiv_eq_iff (C : ChowSituation.{u})
    {P Q : Scheme.{u}} (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (sQ : Q ⟶ C.S)
    [LocallyOfFiniteType sQ] (e : P ⟶ Q) [IsIso e] (he : e ≫ sQ = sP) (e' : Q ⟶ P) [IsIso e']
    (he' : e' ≫ sP = sQ) (hee' : e ≫ e' = 𝟙 P) (he'e : e' ≫ e = 𝟙 Q) {a b c : ℤ} (hac : a = c)
    (hbc : b = c) (hba : b = a) (x : chowGroup C sP a) (y : chowGroup C sQ b) :
    chowPushforwardOfIso C sP sQ e he c (chowGroupDegreeEquiv C sP hac x) =
        chowGroupDegreeEquiv C sQ hbc y ↔
      x = chowGroupDegreeEquiv C sP hba (chowPushforwardOfIso C sQ sP e' he' b y) := by
  subst hac hbc
  show chowPushforwardOfIso C sP sQ e he _ x = y ↔ x = chowPushforwardOfIso C sQ sP e' he' _ y
  constructor
  · rintro rfl
    rw [chowPushforwardOfIso_comp_apply,
      chowPushforwardOfIso_congr_apply C sP sP _ (𝟙 P) hee' _ (Category.id_comp sP),
      chowPushforwardOfIso_id]
  · rintro rfl
    rw [chowPushforwardOfIso_comp_apply,
      chowPushforwardOfIso_congr_apply C sQ sQ _ (𝟙 Q) he'e _ (Category.id_comp sQ),
      chowPushforwardOfIso_id]

section Composite

variable (C : ChowSituation.{u}) {X Z₁ Z₂ : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (f₁ : Z₁ ⟶ X) [LocallyOfFiniteType f₁] (f₂ : Z₂ ⟶ X)
  [LocallyOfFiniteType f₂] (p₁ p₂ : ℤ)

/-- The composite `res(c₁) ∘ c₂ ∈ A^{p₁ + p₂}(Z₁ ×_X Z₂ ⟶ X)` at the Gysin system of the first
Chern class rule, where `res(c₁) ∈ A^{p₁}(Z₁ ×_X Z₂ ⟶ Z₂)` is the restriction of `c₁` along
`f₂` (Stacks 0F9Z) and the composite is that of Stacks 0B75. -/
def commuteCompositeOfInvertible
    (c₁ : BivariantClass C (gysinSystemOfInvertible C) (f₁ ≫ sX) sX f₁ rfl p₁)
    (c₂ : BivariantClass C (gysinSystemOfInvertible C) (f₂ ≫ sX) sX f₂ rfl p₂) :
    BivariantClass C (gysinSystemOfInvertible C) (pullback.fst f₁ f₂ ≫ (f₁ ≫ sX)) sX
      (pullback.snd f₁ f₂ ≫ f₂)
      (comp_comp_structureMorphism_eq
        (pullbackSnd_comp_structureMorphism_eq C (f₁ ≫ sX) sX f₁ rfl f₂) rfl) (p₁ + p₂) :=
  bivariantCompositeOfInvertible C (pullback.fst f₁ f₂ ≫ (f₁ ≫ sX)) (f₂ ≫ sX) sX
    (pullback.snd f₁ f₂) f₂ (pullbackSnd_comp_structureMorphism_eq C (f₁ ≫ sX) sX f₁ rfl f₂) rfl
    p₁ p₂ (bivariantRestrictionOfInvertible C (f₁ ≫ sX) sX f₁ rfl f₂ p₁ c₁) c₂

omit [LocallyOfFiniteType f₁] [LocallyOfFiniteType f₂] in
/-- The isomorphism of base changes induced by the symmetry of the fibre product is the
comparison morphism of the two composites. -/
theorem transportPullbackIso_pullbackSymmetry_hom {T : Scheme.{u}} (t : T ⟶ X) :
    (transportPullbackIso (pullback.snd f₂ f₁ ≫ f₁) (pullback.snd f₁ f₂ ≫ f₂)
        (pullbackSymmetry f₂ f₁) (by rw [pullbackSymmetry_hom_comp_snd_assoc, pullback.condition])
        t).hom =
      compositeComparisonHom f₂ f₁ t := by
  refine pullback.hom_ext ?_ ?_ <;> simp

/-- **Stacks 0FA2.** Two bivariant classes `c₁ ∈ A^{p₁}(Z₁ ⟶ X)` and `c₂ ∈ A^{p₂}(Z₂ ⟶ X)` at
the Gysin system of the first Chern class rule commute if and only if

  `res(c₁) ∘ c₂ = res(c₂) ∘ c₁`   in   `A^{p₁ + p₂}(Z₁ ×_X Z₂ ⟶ X)`,

where `res(cᵢ)` is the restriction of Stacks 0F9Z and `∘` the composition of Stacks 0B75. The
right-hand side, a class in `A^{p₂ + p₁}(Z₂ ×_X Z₁ ⟶ X)`, is read in `A^{p₁ + p₂}(Z₁ ×_X Z₂ ⟶ X)`
through the symmetry of the fibre product and the equality of degrees. -/
@[stacks 0FA2 "commuting is the equality res(c₁) ∘ c₂ = res(c₂) ∘ c₁ of bivariant classes, at \
the canonical Gysin system, with nothing assumed"]
theorem bivariantCommute_iff_commuteCompositeOfInvertible_eq
    (c₁ : BivariantClass C (gysinSystemOfInvertible C) (f₁ ≫ sX) sX f₁ rfl p₁)
    (c₂ : BivariantClass C (gysinSystemOfInvertible C) (f₂ ≫ sX) sX f₂ rfl p₂) :
    BivariantCommute C (gysinSystemOfInvertible C) sX f₁ f₂ p₁ p₂ c₁ c₂ ↔
      commuteCompositeOfInvertible C sX f₁ f₂ p₁ p₂ c₁ c₂ =
        bivariantClassDegreeCongr C (gysinSystemOfInvertible C)
          (pullback.fst f₁ f₂ ≫ (f₁ ≫ sX)) sX (pullback.snd f₁ f₂ ≫ f₂)
          (comp_comp_structureMorphism_eq
            (pullbackSnd_comp_structureMorphism_eq C (f₁ ≫ sX) sX f₁ rfl f₂) rfl)
          (add_comm p₂ p₁)
          (bivariantTransport C (gysinSystemOfInvertible C) (pullback.fst f₂ f₁ ≫ (f₂ ≫ sX))
            (pullback.fst f₁ f₂ ≫ (f₁ ≫ sX)) sX (pullback.snd f₂ f₁ ≫ f₁)
            (comp_comp_structureMorphism_eq
              (pullbackSnd_comp_structureMorphism_eq C (f₂ ≫ sX) sX f₂ rfl f₁) rfl)
            (pullback.snd f₁ f₂ ≫ f₂)
            (comp_comp_structureMorphism_eq
              (pullbackSnd_comp_structureMorphism_eq C (f₁ ≫ sX) sX f₁ rfl f₂) rfl)
            (pullbackSymmetry f₂ f₁)
            (by rw [pullbackSymmetry_hom_comp_snd_assoc, pullback.condition]) (p₂ + p₁)
            (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
            (commuteCompositeOfInvertible C sX f₂ f₁ p₂ p₁ c₂ c₁)) := by
  rw [bivariantCommute_iff_cap_eq_of_isBivariantClassComposition C (gysinSystemOfInvertible C)
    sX f₁ f₂ p₁ p₂ c₁ c₂ (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
    (properPushforwardDescends C) _ _
    (isBivariantClassComposition_bivariantCompositeOfInvertible C _ _ _ _ _ _ _ _ _ _ _)
    (isBivariantClassComposition_bivariantCompositeOfInvertible C _ _ _ _ _ _ _ _ _ _ _)]
  refine Iff.trans (forall_congr' fun T ↦ forall_congr' fun t ↦ forall_congr' fun _ ↦
    forall_congr' fun k ↦ forall_congr' fun α ↦ ?_) BivariantClass.ext_iff.symm
  rw [bivariantClassDegreeCongr_cap_eq, bivariantTransport_cap, bivariantTransportCap_apply,
    chowPushforwardOfIso_congr_apply C _ _ _ (compositeComparisonHom f₂ f₁ t)
      (transportPullbackIso_pullbackSymmetry_hom f₁ f₂ t) _
      (compositeComparisonHom_comp_structureMorphism C sX f₂ f₁ t)]
  exact chowPushforwardOfIso_chowGroupDegreeEquiv_eq_iff C _ _ _ _ _
    (compositeComparisonHom_comp_structureMorphism C sX f₂ f₁ t)
    (compositeComparisonHom_comp_compositeComparisonHom f₁ f₂ t)
    (compositeComparisonHom_comp_compositeComparisonHom f₂ f₁ t) _ _ _ _ _

end Composite

end Stacks.Chow

end
