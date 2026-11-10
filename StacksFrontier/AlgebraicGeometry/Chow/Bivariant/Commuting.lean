module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Restriction
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Basic

/-!
# Commuting bivariant Chow classes

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S` and for `i = 1, 2` let `fᵢ : Zᵢ ⟶ X` be a morphism of schemes
locally of finite type. Given bivariant classes `cᵢ ∈ A^{pᵢ}(Zᵢ ⟶ X)` one may ask, for
`α ∈ CH_k(X)`, whether

  `c₁ ∩ c₂ ∩ α = c₂ ∩ c₁ ∩ α`   in   `CH_{k - p₁ - p₂}(Z₁ ×_X Z₂)`,

and whether this persists after every base change `X' ⟶ X` locally of finite type. When it does,
`c₁` and `c₂` are said to **commute**. **Stacks 0FA2** records that this is the same as the
equality of composites

  `res(c₁) ∘ c₂ = res(c₂) ∘ c₁`   in   `A^{p₁ + p₂}(Z₁ ×_X Z₂ ⟶ X)`,

where `res(c₁) ∈ A^{p₁}(Z₁ ×_X Z₂ ⟶ Z₂)` is the restriction of `c₁` along `f₂` in the sense of
Stacks 0F9Z and `res(c₂) ∈ A^{p₂}(Z₂ ×_X Z₁ ⟶ Z₁)` is the restriction of `c₂` along `f₁`.

## Main definitions

* `Stacks.Chow.commuteComparisonHom` — the canonical isomorphism
  `Z₁ ×_X (Z₂ ×_X T) ≅ Z₂ ×_X (Z₁ ×_X T)` on which the two iterated cap operations land.
* `Stacks.Chow.bivariantIteratedCap` — the iterated cap operation `α ↦ c₁ ∩ (c₂ ∩ α)`.
* `Stacks.Chow.BivariantCommute` — **Stacks 0FA2**, the assertion that `c₁` and `c₂` commute.
* `Stacks.Chow.compositeComparisonHom` — the canonical isomorphism
  `(Z₁ ×_X Z₂) ×_X T ≅ (Z₂ ×_X Z₁) ×_X T` induced by the symmetry of the fibre product, which is
  the identification under which the two composites of the tag are compared.
* `Stacks.Chow.commuteCompositeCap` — the cap operation of the composite `res(c₁) ∘ c₂`.

## Main results

* `Stacks.Chow.bivariantCommute_iff_commuteCompositeCap_eq` — **Stacks 0FA2**, the equivalence of
  the tag: `c₁` and `c₂` commute if and only if the cap operations of `res(c₁) ∘ c₂` and of
  `res(c₂) ∘ c₁` agree under the canonical identification of `Z₁ ×_X Z₂` with `Z₂ ×_X Z₁`.
* `Stacks.Chow.bivariantCommute_iff_cap_eq_of_isBivariantClassComposition` — **Stacks 0FA2**, the
  same equivalence read on bivariant classes `d₁`, `d₂` that are the two composites: `c₁` and `c₂`
  commute if and only if `d₁ = d₂` under that identification.

## References

* [Stacks Project, Tag 0FA2](https://stacks.math.columbia.edu/tag/0FA2)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 0GU8](https://stacks.math.columbia.edu/tag/0GU8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Transport along an equality of degrees and pushforward -/

/-- Pushforward along an isomorphism over the base commutes with the transport of a Chow group
along an equality of degrees. -/
theorem chowGroupDegreeEquiv_chowPushforwardOfIso (C : ChowSituation.{u}) {A B : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (u : A ⟶ B)
    [IsIso u] (hu : u ≫ sB = sA) {k l : ℤ} (hkl : k = l) (x : chowGroup C sA k) :
    chowGroupDegreeEquiv C sB hkl (chowPushforwardOfIso C sA sB u hu k x) =
      chowPushforwardOfIso C sA sB u hu l (chowGroupDegreeEquiv C sA hkl x) := by
  subst hkl
  rfl

/-- Two successive transports along equalities of degrees compose to the transport along the
composite equality. -/
theorem chowGroupDegreeEquiv_chowGroupDegreeEquiv (C : ChowSituation.{u}) {A : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] {i j l : ℤ} (hij : i = j) (hjl : j = l)
    (x : chowGroup C sA i) :
    chowGroupDegreeEquiv C sA hjl (chowGroupDegreeEquiv C sA hij x) =
      chowGroupDegreeEquiv C sA (hij.trans hjl) x := by
  subst hij hjl
  rfl

/-! ### The comparison isomorphism of the two iterated base changes -/

section Comparison

variable (C : ChowSituation.{u}) {X Z₁ Z₂ : Scheme.{u}} (sX : X ⟶ C.S) (f₁ : Z₁ ⟶ X)
  (f₂ : Z₂ ⟶ X)

/-- The canonical morphism `Z₁ ×_X (Z₂ ×_X T) ⟶ Z₂ ×_X (Z₁ ×_X T)` over a test scheme
`t : T ⟶ X`: it sends a point to the same triple of points of `Z₁`, `Z₂` and `T`, read in the
other order. It is an isomorphism, with inverse the same morphism for the pair `(f₂, f₁)`. -/
def commuteComparisonHom {T : Scheme.{u}} (t : T ⟶ X) :
    pullback f₁ (pullback.fst f₂ t ≫ f₂) ⟶ pullback f₂ (pullback.fst f₁ t ≫ f₁) :=
  pullback.lift (pullback.snd f₁ (pullback.fst f₂ t ≫ f₂) ≫ pullback.fst f₂ t)
    (pullback.lift (pullback.fst f₁ (pullback.fst f₂ t ≫ f₂))
      (pullback.snd f₁ (pullback.fst f₂ t ≫ f₂) ≫ pullback.snd f₂ t)
      (by
        rw [Category.assoc, ← pullback.condition (f := f₂) (g := t)]
        exact pullback.condition))
    (by
      rw [← Category.assoc, pullback.lift_fst, Category.assoc]
      exact pullback.condition.symm)

/-- The first projection of the comparison morphism: the point of `Z₂`. -/
@[reassoc (attr := simp)]
theorem commuteComparisonHom_fst {T : Scheme.{u}} (t : T ⟶ X) :
    commuteComparisonHom f₁ f₂ t ≫ pullback.fst f₂ (pullback.fst f₁ t ≫ f₁) =
      pullback.snd f₁ (pullback.fst f₂ t ≫ f₂) ≫ pullback.fst f₂ t :=
  pullback.lift_fst _ _ _

/-- The second projection of the comparison morphism, followed by the projection to `Z₁`. -/
@[reassoc (attr := simp)]
theorem commuteComparisonHom_snd_fst {T : Scheme.{u}} (t : T ⟶ X) :
    commuteComparisonHom f₁ f₂ t ≫ pullback.snd f₂ (pullback.fst f₁ t ≫ f₁) ≫
        pullback.fst f₁ t =
      pullback.fst f₁ (pullback.fst f₂ t ≫ f₂) := by
  simp [commuteComparisonHom]

/-- The second projection of the comparison morphism, followed by the projection to the test
scheme. -/
@[reassoc (attr := simp)]
theorem commuteComparisonHom_snd_snd {T : Scheme.{u}} (t : T ⟶ X) :
    commuteComparisonHom f₁ f₂ t ≫ pullback.snd f₂ (pullback.fst f₁ t ≫ f₁) ≫
        pullback.snd f₁ t =
      pullback.snd f₁ (pullback.fst f₂ t ≫ f₂) ≫ pullback.snd f₂ t := by
  simp [commuteComparisonHom]

/-- The comparison morphisms of the two orders are mutually inverse. -/
@[simp]
theorem commuteComparisonHom_comp_commuteComparisonHom {T : Scheme.{u}} (t : T ⟶ X) :
    commuteComparisonHom f₁ f₂ t ≫ commuteComparisonHom f₂ f₁ t =
      𝟙 (pullback f₁ (pullback.fst f₂ t ≫ f₂)) := by
  refine pullback.hom_ext ?_ (pullback.hom_ext ?_ ?_) <;> simp

/-- The comparison morphism of the two iterated base changes is an isomorphism. -/
instance isIso_commuteComparisonHom {T : Scheme.{u}} (t : T ⟶ X) :
    IsIso (commuteComparisonHom f₁ f₂ t) :=
  ⟨⟨commuteComparisonHom f₂ f₁ t, commuteComparisonHom_comp_commuteComparisonHom f₁ f₂ t,
    commuteComparisonHom_comp_commuteComparisonHom f₂ f₁ t⟩⟩

/-- The inverse of the comparison morphism is the comparison morphism of the other order. -/
@[simp]
theorem inv_commuteComparisonHom {T : Scheme.{u}} (t : T ⟶ X) :
    inv (commuteComparisonHom f₁ f₂ t) = commuteComparisonHom f₂ f₁ t :=
  IsIso.inv_eq_of_hom_inv_id (commuteComparisonHom_comp_commuteComparisonHom f₁ f₂ t)

/-- The comparison isomorphism is compatible with the structure morphisms of the two iterated
fibre products over the base. -/
theorem commuteComparisonHom_comp_structureMorphism {T : Scheme.{u}} (t : T ⟶ X) :
    commuteComparisonHom f₁ f₂ t ≫
        (pullback.fst f₂ (pullback.fst f₁ t ≫ f₁) ≫ (f₂ ≫ sX)) =
      pullback.fst f₁ (pullback.fst f₂ t ≫ f₂) ≫ (f₁ ≫ sX) := by
  rw [commuteComparisonHom_fst_assoc, pullback.condition_assoc (f := f₁), Category.assoc]

/-! ### The comparison isomorphism of the two composites -/

/-- The canonical morphism `(Z₁ ×_X Z₂) ×_X T ⟶ (Z₂ ×_X Z₁) ×_X T` over a test scheme
`t : T ⟶ X`, induced by the symmetry `Z₁ ×_X Z₂ ≅ Z₂ ×_X Z₁` of the fibre product. It is an
isomorphism, with inverse the same morphism for the pair `(f₂, f₁)`. -/
def compositeComparisonHom {T : Scheme.{u}} (t : T ⟶ X) :
    pullback (pullback.snd f₁ f₂ ≫ f₂) t ⟶ pullback (pullback.snd f₂ f₁ ≫ f₁) t :=
  pullback.lift
    (pullback.fst (pullback.snd f₁ f₂ ≫ f₂) t ≫ (pullbackSymmetry f₁ f₂).hom)
    (pullback.snd (pullback.snd f₁ f₂ ≫ f₂) t)
    (by simp [pullback.condition])

/-- The first projection of the comparison morphism of the two composites. -/
@[reassoc (attr := simp)]
theorem compositeComparisonHom_fst {T : Scheme.{u}} (t : T ⟶ X) :
    compositeComparisonHom f₁ f₂ t ≫ pullback.fst (pullback.snd f₂ f₁ ≫ f₁) t =
      pullback.fst (pullback.snd f₁ f₂ ≫ f₂) t ≫ (pullbackSymmetry f₁ f₂).hom :=
  pullback.lift_fst _ _ _

/-- The second projection of the comparison morphism of the two composites. -/
@[reassoc (attr := simp)]
theorem compositeComparisonHom_snd {T : Scheme.{u}} (t : T ⟶ X) :
    compositeComparisonHom f₁ f₂ t ≫ pullback.snd (pullback.snd f₂ f₁ ≫ f₁) t =
      pullback.snd (pullback.snd f₁ f₂ ≫ f₂) t :=
  pullback.lift_snd _ _ _

/-- The comparison morphisms of the two composites, in the two orders, are mutually inverse. -/
@[simp]
theorem compositeComparisonHom_comp_compositeComparisonHom {T : Scheme.{u}} (t : T ⟶ X) :
    compositeComparisonHom f₁ f₂ t ≫ compositeComparisonHom f₂ f₁ t =
      𝟙 (pullback (pullback.snd f₁ f₂ ≫ f₂) t) := by
  refine pullback.hom_ext (pullback.hom_ext ?_ ?_) ?_ <;> simp

/-- The comparison morphism of the two composites is an isomorphism. -/
instance isIso_compositeComparisonHom {T : Scheme.{u}} (t : T ⟶ X) :
    IsIso (compositeComparisonHom f₁ f₂ t) :=
  ⟨⟨compositeComparisonHom f₂ f₁ t,
    compositeComparisonHom_comp_compositeComparisonHom f₁ f₂ t,
    compositeComparisonHom_comp_compositeComparisonHom f₂ f₁ t⟩⟩

/-- The comparison isomorphism of the two composites is compatible with the structure morphisms
of the two base changes over the base. -/
theorem compositeComparisonHom_comp_structureMorphism {T : Scheme.{u}} (t : T ⟶ X) :
    compositeComparisonHom f₁ f₂ t ≫
        (pullback.fst (pullback.snd f₂ f₁ ≫ f₁) t ≫ (pullback.fst f₂ f₁ ≫ (f₂ ≫ sX))) =
      pullback.fst (pullback.snd f₁ f₂ ≫ f₂) t ≫ (pullback.fst f₁ f₂ ≫ (f₁ ≫ sX)) := by
  simp [pullback.condition_assoc]

/-! ### The comparison of the restricted-composite target with the iterated base change -/

/-- The isomorphism identifying `Z₁ ×_X (Z₂ ×_X T)`, where the iterated cap operation lands, with
`(Z₁ ×_X Z₂) ×_X T`, where the cap operation of the composite `res(c₁) ∘ c₂` lands: the two
pastings of the same pair of fibre squares. -/
abbrev compositeTargetHom {T : Scheme.{u}} (t : T ⟶ X) :
    pullback f₁ (pullback.fst f₂ t ≫ f₂) ⟶ pullback (pullback.snd f₁ f₂ ≫ f₂) t :=
  (pullbackLeftPullbackSndIso f₁ f₂ (pullback.fst f₂ t)).inv ≫
    (pullbackRightPullbackFstIso f₂ t (pullback.snd f₁ f₂)).hom

/-- The comparison of the two targets is compatible with the structure morphisms over the
base. -/
theorem compositeTargetHom_comp_structureMorphism {T : Scheme.{u}} (t : T ⟶ X) :
    compositeTargetHom f₁ f₂ t ≫
        (pullback.fst (pullback.snd f₁ f₂ ≫ f₂) t ≫ (pullback.fst f₁ f₂ ≫ (f₁ ≫ sX))) =
      pullback.fst f₁ (pullback.fst f₂ t ≫ f₂) ≫ (f₁ ≫ sX) := by
  simp

/-- The two comparison isomorphisms are compatible: transporting the iterated cap operation to
the target of the composite and then exchanging the two factors is the same as exchanging the two
factors first. -/
theorem compositeTargetHom_comp_compositeComparisonHom {T : Scheme.{u}} (t : T ⟶ X) :
    compositeTargetHom f₁ f₂ t ≫ compositeComparisonHom f₁ f₂ t =
      commuteComparisonHom f₁ f₂ t ≫ compositeTargetHom f₂ f₁ t := by
  refine pullback.hom_ext (pullback.hom_ext ?_ ?_) ?_ <;> simp

end Comparison

/-! ### The iterated cap operation -/

section Iterated

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Z₁ Z₂ : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (f₁ : Z₁ ⟶ X) [LocallyOfFiniteType f₁] (f₂ : Z₂ ⟶ X)
  [LocallyOfFiniteType f₂] (p₁ p₂ : ℤ)
  (c₁ : BivariantClass C G (f₁ ≫ sX) sX f₁ rfl p₁)
  (c₂ : BivariantClass C G (f₂ ≫ sX) sX f₂ rfl p₂)

/-- The iterated cap operation `α ↦ c₁ ∩ (c₂ ∩ α)` at a test scheme `t : T ⟶ X`. Capping with
`c₂` produces a class on `Z₂ ×_X T`, which is a test scheme over `X` through
`pullback.fst f₂ t ≫ f₂`, and capping that with `c₁` produces a class on
`Z₁ ×_X (Z₂ ×_X T)`. -/
def bivariantIteratedCap {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ) :
    chowGroup C (t ≫ sX) k →+
      chowGroup C (pullback.fst f₁ (pullback.fst f₂ t ≫ f₂) ≫ (f₁ ≫ sX)) ((k - p₂) - p₁) :=
  (c₁.cap (pullback.fst f₂ t ≫ f₂) (k - p₂)).comp
    (((chowGroupCongr C (Category.assoc (pullback.fst f₂ t) f₂ sX).symm
      (k - p₂)).toAddMonoidHom).comp (c₂.cap t k))

/-- The iterated cap operation sends `α` to `c₁ ∩ (c₂ ∩ α)`, where `c₂ ∩ α` is regarded as a class
on `Z₂ ×_X T` viewed as a scheme over `X` through `pullback.fst f₂ t ≫ f₂`. -/
@[simp]
theorem bivariantIteratedCap_apply {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ)
    (α : chowGroup C (t ≫ sX) k) :
    bivariantIteratedCap C G sX f₁ f₂ p₁ p₂ c₁ c₂ t k α =
      c₁.cap (pullback.fst f₂ t ≫ f₂) (k - p₂)
        (chowGroupCongr C (Category.assoc (pullback.fst f₂ t) f₂ sX).symm (k - p₂)
          (c₂.cap t k α)) :=
  rfl

/-! ### Commuting classes -/

/-- Two bivariant classes `c₁ ∈ A^{p₁}(Z₁ ⟶ X)` and `c₂ ∈ A^{p₂}(Z₂ ⟶ X)` *commute* when

  `c₁ ∩ c₂ ∩ α = c₂ ∩ c₁ ∩ α`

for every morphism `t : T ⟶ X` locally of finite type and every `α ∈ CH_k(T)`; this is the
identity for every `α ∈ CH_k(X)` and after every base change `X' ⟶ X` locally of finite type.

The two sides live on the two iterated fibre products `Z₁ ×_X (Z₂ ×_X T)` and `Z₂ ×_X (Z₁ ×_X T)`
and in the two degrees `(k - p₂) - p₁` and `(k - p₁) - p₂`; they are compared by pushing the
first forward along `Stacks.Chow.commuteComparisonHom` and transporting the second along the
equality of degrees. -/
@[stacks 0FA2 "the definition of commuting bivariant classes"]
def BivariantCommute : Prop :=
  ∀ {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ)
    (α : chowGroup C (t ≫ sX) k),
    chowPushforwardOfIso C (pullback.fst f₁ (pullback.fst f₂ t ≫ f₂) ≫ (f₁ ≫ sX))
        (pullback.fst f₂ (pullback.fst f₁ t ≫ f₁) ≫ (f₂ ≫ sX)) (commuteComparisonHom f₁ f₂ t)
        (commuteComparisonHom_comp_structureMorphism C sX f₁ f₂ t) ((k - p₂) - p₁)
        (bivariantIteratedCap C G sX f₁ f₂ p₁ p₂ c₁ c₂ t k α) =
      chowGroupDegreeEquiv C (pullback.fst f₂ (pullback.fst f₁ t ≫ f₁) ≫ (f₂ ≫ sX))
        (by ring : (k - p₁) - p₂ = (k - p₂) - p₁)
        (bivariantIteratedCap C G sX f₂ f₁ p₂ p₁ c₂ c₁ t k α)

end Iterated

/-! ### The cap operation of the composite `res(c₁) ∘ c₂` -/

section Composite

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Z₁ Z₂ : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (f₁ : Z₁ ⟶ X) [LocallyOfFiniteType f₁] (f₂ : Z₂ ⟶ X)
  [LocallyOfFiniteType f₂] (p₁ p₂ : ℤ)
  (c₁ : BivariantClass C G (f₁ ≫ sX) sX f₁ rfl p₁)
  (c₂ : BivariantClass C G (f₂ ≫ sX) sX f₂ rfl p₂)
  (hgys : G.IsNaturalUnderBaseChangeIso) (hpp : ProperPushforwardDescends C)

/-- The cap operation of the composite `res(c₁) ∘ c₂ ∈ A^{p₁ + p₂}(Z₁ ×_X Z₂ ⟶ X)`, where
`res(c₁) ∈ A^{p₁}(Z₁ ×_X Z₂ ⟶ Z₂)` is the restriction of `c₁` along `f₂`. -/
def commuteCompositeCap {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ) :
    chowGroup C (t ≫ sX) k →+
      chowGroup C (pullback.fst (pullback.snd f₁ f₂ ≫ f₂) t ≫
        (pullback.fst f₁ f₂ ≫ (f₁ ≫ sX))) ((k - p₂) - p₁) :=
  bivariantCompositeCap C G (pullback.fst f₁ f₂ ≫ (f₁ ≫ sX)) (f₂ ≫ sX) sX
    (pullback.snd f₁ f₂) f₂
    (pullbackSnd_comp_structureMorphism_eq C (f₁ ≫ sX) sX f₁ rfl f₂) rfl hpp p₁ p₂
    (bivariantRestriction C G (f₁ ≫ sX) sX f₁ rfl f₂ p₁ hgys c₁) c₂ t k

/-- The cap operation of `res(c₁) ∘ c₂` is the cap operation of the composite of the restriction
of `c₁` with `c₂`, by definition. -/
theorem commuteCompositeCap_eq_bivariantCompositeCap {T : Scheme.{u}} (t : T ⟶ X)
    [LocallyOfFiniteType t] (k : ℤ) :
    commuteCompositeCap C G sX f₁ f₂ p₁ p₂ c₁ c₂ hgys hpp t k =
      bivariantCompositeCap C G (pullback.fst f₁ f₂ ≫ (f₁ ≫ sX)) (f₂ ≫ sX) sX
        (pullback.snd f₁ f₂) f₂
        (pullbackSnd_comp_structureMorphism_eq C (f₁ ≫ sX) sX f₁ rfl f₂) rfl hpp p₁ p₂
        (bivariantRestriction C G (f₁ ≫ sX) sX f₁ rfl f₂ p₁ hgys c₁) c₂ t k :=
  rfl

/-- The cap operation of `res(c₁) ∘ c₂` is the iterated cap operation `c₁ ∩ (c₂ ∩ -)`, pushed
forward along the comparison isomorphism of the two fibre products. -/
theorem commuteCompositeCap_apply {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ)
    (α : chowGroup C (t ≫ sX) k) :
    commuteCompositeCap C G sX f₁ f₂ p₁ p₂ c₁ c₂ hgys hpp t k α =
      chowPushforwardOfIso C (pullback.fst f₁ (pullback.fst f₂ t ≫ f₂) ≫ (f₁ ≫ sX))
        (pullback.fst (pullback.snd f₁ f₂ ≫ f₂) t ≫ (pullback.fst f₁ f₂ ≫ (f₁ ≫ sX)))
        (compositeTargetHom f₁ f₂ t)
        (compositeTargetHom_comp_structureMorphism C sX f₁ f₂ t) ((k - p₂) - p₁)
        (bivariantIteratedCap C G sX f₁ f₂ p₁ p₂ c₁ c₂ t k α) := by
  rw [commuteCompositeCap_eq_bivariantCompositeCap, bivariantCompositeCap_apply,
    properChowPushforward_eq_chowPushforwardOfIso, bivariantRestriction_cap,
    bivariantRestrictionCap_apply, bivariantIteratedCap_apply, chowPushforwardOfIso_comp_apply]

/-! ### The equivalence of Stacks 0FA2 -/

/-- At a single test scheme `t : T ⟶ X` and a single `α ∈ CH_k(T)`, the equality of the cap
operations of the two composites `res(c₁) ∘ c₂` and `res(c₂) ∘ c₁`, read under the canonical
identification `Z₁ ×_X Z₂ ≅ Z₂ ×_X Z₁`, is the equality of the two iterated cap operations
`c₁ ∩ (c₂ ∩ α)` and `c₂ ∩ (c₁ ∩ α)` read under `Stacks.Chow.commuteComparisonHom`. -/
theorem commuteCompositeCap_eq_iff_bivariantIteratedCap_eq :
    ∀ {T : Scheme.{u}} (t : T ⟶ X) (_ : LocallyOfFiniteType t) (k : ℤ)
      (α : chowGroup C (t ≫ sX) k),
      (chowPushforwardOfIso C
          (pullback.fst (pullback.snd f₁ f₂ ≫ f₂) t ≫ (pullback.fst f₁ f₂ ≫ (f₁ ≫ sX)))
          (pullback.fst (pullback.snd f₂ f₁ ≫ f₁) t ≫ (pullback.fst f₂ f₁ ≫ (f₂ ≫ sX)))
          (compositeComparisonHom f₁ f₂ t)
          (compositeComparisonHom_comp_structureMorphism C sX f₁ f₂ t) ((k - p₂) - p₁)
          (commuteCompositeCap C G sX f₁ f₂ p₁ p₂ c₁ c₂ hgys hpp t k α) =
        chowGroupDegreeEquiv C
          (pullback.fst (pullback.snd f₂ f₁ ≫ f₁) t ≫ (pullback.fst f₂ f₁ ≫ (f₂ ≫ sX)))
          (by ring : (k - p₁) - p₂ = (k - p₂) - p₁)
          (commuteCompositeCap C G sX f₂ f₁ p₂ p₁ c₂ c₁ hgys hpp t k α)) ↔
      chowPushforwardOfIso C (pullback.fst f₁ (pullback.fst f₂ t ≫ f₂) ≫ (f₁ ≫ sX))
          (pullback.fst f₂ (pullback.fst f₁ t ≫ f₁) ≫ (f₂ ≫ sX)) (commuteComparisonHom f₁ f₂ t)
          (commuteComparisonHom_comp_structureMorphism C sX f₁ f₂ t) ((k - p₂) - p₁)
          (bivariantIteratedCap C G sX f₁ f₂ p₁ p₂ c₁ c₂ t k α) =
        chowGroupDegreeEquiv C (pullback.fst f₂ (pullback.fst f₁ t ≫ f₁) ≫ (f₂ ≫ sX))
          (by ring : (k - p₁) - p₂ = (k - p₂) - p₁)
          (bivariantIteratedCap C G sX f₂ f₁ p₂ p₁ c₂ c₁ t k α) := by
  intro T t _ k α
  have key :
      chowPushforwardOfIso C
          (pullback.fst (pullback.snd f₁ f₂ ≫ f₂) t ≫ (pullback.fst f₁ f₂ ≫ (f₁ ≫ sX)))
          (pullback.fst (pullback.snd f₂ f₁ ≫ f₁) t ≫ (pullback.fst f₂ f₁ ≫ (f₂ ≫ sX)))
          (compositeComparisonHom f₁ f₂ t)
          (compositeComparisonHom_comp_structureMorphism C sX f₁ f₂ t) ((k - p₂) - p₁)
          (commuteCompositeCap C G sX f₁ f₂ p₁ p₂ c₁ c₂ hgys hpp t k α) =
        chowPushforwardOfIso C (pullback.fst f₂ (pullback.fst f₁ t ≫ f₁) ≫ (f₂ ≫ sX))
          (pullback.fst (pullback.snd f₂ f₁ ≫ f₁) t ≫ (pullback.fst f₂ f₁ ≫ (f₂ ≫ sX)))
          (compositeTargetHom f₂ f₁ t)
          (compositeTargetHom_comp_structureMorphism C sX f₂ f₁ t) ((k - p₂) - p₁)
          (chowPushforwardOfIso C
            (pullback.fst f₁ (pullback.fst f₂ t ≫ f₂) ≫ (f₁ ≫ sX))
            (pullback.fst f₂ (pullback.fst f₁ t ≫ f₁) ≫ (f₂ ≫ sX))
            (commuteComparisonHom f₁ f₂ t)
            (commuteComparisonHom_comp_structureMorphism C sX f₁ f₂ t) ((k - p₂) - p₁)
            (bivariantIteratedCap C G sX f₁ f₂ p₁ p₂ c₁ c₂ t k α)) := by
    rw [commuteCompositeCap_apply, chowPushforwardOfIso_comp_apply,
      chowPushforwardOfIso_comp_apply]
    exact chowPushforwardOfIso_congr_apply C _ _ _ _
      (compositeTargetHom_comp_compositeComparisonHom f₁ f₂ t) _ _ ((k - p₂) - p₁) _
  have key₂ :
      chowGroupDegreeEquiv C
          (pullback.fst (pullback.snd f₂ f₁ ≫ f₁) t ≫ (pullback.fst f₂ f₁ ≫ (f₂ ≫ sX)))
          (by ring : (k - p₁) - p₂ = (k - p₂) - p₁)
          (commuteCompositeCap C G sX f₂ f₁ p₂ p₁ c₂ c₁ hgys hpp t k α) =
        chowPushforwardOfIso C (pullback.fst f₂ (pullback.fst f₁ t ≫ f₁) ≫ (f₂ ≫ sX))
          (pullback.fst (pullback.snd f₂ f₁ ≫ f₁) t ≫ (pullback.fst f₂ f₁ ≫ (f₂ ≫ sX)))
          (compositeTargetHom f₂ f₁ t)
          (compositeTargetHom_comp_structureMorphism C sX f₂ f₁ t) ((k - p₂) - p₁)
          (chowGroupDegreeEquiv C
            (pullback.fst f₂ (pullback.fst f₁ t ≫ f₁) ≫ (f₂ ≫ sX))
            (by ring : (k - p₁) - p₂ = (k - p₂) - p₁)
            (bivariantIteratedCap C G sX f₂ f₁ p₂ p₁ c₂ c₁ t k α)) := by
    rw [commuteCompositeCap_apply, chowGroupDegreeEquiv_chowPushforwardOfIso]
  rw [key, key₂]
  exact (chowGroupEquivOfIso C
    (pullback.fst f₂ (pullback.fst f₁ t ≫ f₁) ≫ (f₂ ≫ sX))
    (pullback.fst (pullback.snd f₂ f₁ ≫ f₁) t ≫ (pullback.fst f₂ f₁ ≫ (f₂ ≫ sX)))
    (compositeTargetHom f₂ f₁ t)
    (compositeTargetHom_comp_structureMorphism C sX f₂ f₁ t)
    ((k - p₂) - p₁)).injective.eq_iff

/-- Two bivariant classes commute if and only if the cap operations of the two
composites `res(c₁) ∘ c₂` and `res(c₂) ∘ c₁` agree, under the canonical identification
`Z₁ ×_X Z₂ ≅ Z₂ ×_X Z₁` of their sources and the equality `p₁ + p₂ = p₂ + p₁` of their degrees. -/
@[stacks 0FA2 "commuting is the equality of the two composites"]
theorem bivariantCommute_iff_commuteCompositeCap_eq :
    BivariantCommute C G sX f₁ f₂ p₁ p₂ c₁ c₂ ↔
      ∀ {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ)
        (α : chowGroup C (t ≫ sX) k),
        chowPushforwardOfIso C
            (pullback.fst (pullback.snd f₁ f₂ ≫ f₂) t ≫ (pullback.fst f₁ f₂ ≫ (f₁ ≫ sX)))
            (pullback.fst (pullback.snd f₂ f₁ ≫ f₁) t ≫ (pullback.fst f₂ f₁ ≫ (f₂ ≫ sX)))
            (compositeComparisonHom f₁ f₂ t)
            (compositeComparisonHom_comp_structureMorphism C sX f₁ f₂ t) ((k - p₂) - p₁)
            (commuteCompositeCap C G sX f₁ f₂ p₁ p₂ c₁ c₂ hgys hpp t k α) =
          chowGroupDegreeEquiv C
            (pullback.fst (pullback.snd f₂ f₁ ≫ f₁) t ≫ (pullback.fst f₂ f₁ ≫ (f₂ ≫ sX)))
            (by ring : (k - p₁) - p₂ = (k - p₂) - p₁)
            (commuteCompositeCap C G sX f₂ f₁ p₂ p₁ c₂ c₁ hgys hpp t k α) :=
  ⟨fun h _ t _ k α ↦ (commuteCompositeCap_eq_iff_bivariantIteratedCap_eq C G sX f₁ f₂ p₁ p₂
      c₁ c₂ hgys hpp t inferInstance k α).2 (h t k α),
    fun h _ t _ k α ↦ (commuteCompositeCap_eq_iff_bivariantIteratedCap_eq C G sX f₁ f₂ p₁ p₂
      c₁ c₂ hgys hpp t inferInstance k α).1 (h t k α)⟩

/-- If `d₁` is the composite `res(c₁) ∘ c₂` and `d₂` is the composite `res(c₂) ∘ c₁` in the sense
of Stacks 0FE0, then `c₁` and `c₂` commute exactly when `d₁` and `d₂` agree under the canonical
identification `Z₁ ×_X Z₂ ≅ Z₂ ×_X Z₁`. -/
@[stacks 0FA2 "commuting is the equality of the two composite classes"]
theorem bivariantCommute_iff_cap_eq_of_isBivariantClassComposition
    (d₁ : BivariantClass C G (pullback.fst f₁ f₂ ≫ (f₁ ≫ sX)) sX (pullback.snd f₁ f₂ ≫ f₂)
      (comp_comp_structureMorphism_eq
        (pullbackSnd_comp_structureMorphism_eq C (f₁ ≫ sX) sX f₁ rfl f₂) rfl) (p₁ + p₂))
    (d₂ : BivariantClass C G (pullback.fst f₂ f₁ ≫ (f₂ ≫ sX)) sX (pullback.snd f₂ f₁ ≫ f₁)
      (comp_comp_structureMorphism_eq
        (pullbackSnd_comp_structureMorphism_eq C (f₂ ≫ sX) sX f₂ rfl f₁) rfl) (p₂ + p₁))
    (h₁ : IsBivariantClassComposition C G (pullback.fst f₁ f₂ ≫ (f₁ ≫ sX)) (f₂ ≫ sX) sX
      (pullback.snd f₁ f₂) f₂
      (pullbackSnd_comp_structureMorphism_eq C (f₁ ≫ sX) sX f₁ rfl f₂) rfl hpp p₁ p₂
      (bivariantRestriction C G (f₁ ≫ sX) sX f₁ rfl f₂ p₁ hgys c₁) c₂ d₁)
    (h₂ : IsBivariantClassComposition C G (pullback.fst f₂ f₁ ≫ (f₂ ≫ sX)) (f₁ ≫ sX) sX
      (pullback.snd f₂ f₁) f₁
      (pullbackSnd_comp_structureMorphism_eq C (f₂ ≫ sX) sX f₂ rfl f₁) rfl hpp p₂ p₁
      (bivariantRestriction C G (f₂ ≫ sX) sX f₂ rfl f₁ p₂ hgys c₂) c₁ d₂) :
    BivariantCommute C G sX f₁ f₂ p₁ p₂ c₁ c₂ ↔
      ∀ {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ)
        (α : chowGroup C (t ≫ sX) k),
        chowPushforwardOfIso C
            (pullback.fst (pullback.snd f₁ f₂ ≫ f₂) t ≫ (pullback.fst f₁ f₂ ≫ (f₁ ≫ sX)))
            (pullback.fst (pullback.snd f₂ f₁ ≫ f₁) t ≫ (pullback.fst f₂ f₁ ≫ (f₂ ≫ sX)))
            (compositeComparisonHom f₁ f₂ t)
            (compositeComparisonHom_comp_structureMorphism C sX f₁ f₂ t) ((k - p₂) - p₁)
            (chowGroupDegreeEquiv C
              (pullback.fst (pullback.snd f₁ f₂ ≫ f₂) t ≫ (pullback.fst f₁ f₂ ≫ (f₁ ≫ sX)))
              (by ring : k - (p₁ + p₂) = (k - p₂) - p₁) (d₁.cap t k α)) =
          chowGroupDegreeEquiv C
            (pullback.fst (pullback.snd f₂ f₁ ≫ f₁) t ≫ (pullback.fst f₂ f₁ ≫ (f₂ ≫ sX)))
            (by ring : k - (p₂ + p₁) = (k - p₂) - p₁) (d₂.cap t k α) := by
  rw [isBivariantClassComposition_iff] at h₁ h₂
  rw [bivariantCommute_iff_commuteCompositeCap_eq C G sX f₁ f₂ p₁ p₂ c₁ c₂ hgys hpp]
  unfold commuteCompositeCap
  refine ⟨fun h T t _ k α ↦ ?_, fun h T t _ k α ↦ ?_⟩
  · rw [h₁ t k α, h t k α, ← h₂ t k α, chowGroupDegreeEquiv_chowGroupDegreeEquiv]
  · rw [← h₁ t k α, h t k α, ← h₂ t k α, chowGroupDegreeEquiv_chowGroupDegreeEquiv]

end Composite

end Stacks.Chow

end
