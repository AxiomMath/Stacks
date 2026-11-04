module

public import StacksFrontier.AlgebraicGeometry.Chow.BabyLocalizedChern.LocalizedPowerSumAtInfinity
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinity.BaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinity.Commuting
public import StacksCore.Tactic.StacksAttribute

/-!
# The classes of Stacks 0F9K commute with base change (Stacks 0GUI)

Let `(S, δ)` be as in Situation 02QL and let `X`, `Z ⊆ X`, `b : W ⟶ 𝐏¹_X`, `Q ∈ D(𝒪_W)` and
`T ⊆ W_∞` be as in Stacks 0F9K, so that `P'_p(Q)`, resp. `c'_p(Q) ∈ A^p(Z ⟶ X)` is the class
`(E ⟶ Z)_* ∘ P'_p(Q|_E) ∘ C`, resp. `(E ⟶ Z)_* ∘ c'_p(Q|_E) ∘ C`. For `q : X' ⟶ X` locally of
finite type let `Z' = Z ×_X X'`, `b' : W' = W ×_{𝐏¹_X} 𝐏¹_{X'} ⟶ 𝐏¹_{X'}` and
`T' = T ×_{W_∞} W'_∞ ⊆ W'_∞` be the base changes and `Q' = (W' ⟶ W)^*Q`. **Stacks 0GUI** asserts
that the class `P'_p(Q')`, resp. `c'_p(Q')` in `A^p(Z' ⟶ X')` built as in Stacks 0F9K from `b'`,
`Q'` and `T'` is the restriction (Remark 0F9Z) of `P'_p(Q)`, resp. `c'_p(Q)`.

The proof is the source's: the construction is the composite of three factors, and each commutes
with the base change — the class `C` of Stacks 0F9J by Stacks 0GUH, the class of Stacks 0F9H by
the argument of Stacks 0GUG, and the pushforward along `E ⟶ Z` by the functoriality of proper
pushforward (the source's "small detail omitted"). Everything is read on the cap operations of a
test scheme `T₀ ⟶ X'`, where the base change of each factor is the identification
`W'_∞ ×_{X'} T₀ ≅ W_∞ ×_X T₀`.

## Main results

* `Stacks.Chow.chowPush_closedCoverLocalizedClass_cap_baseChange` — the localized class of
  Stacks 0F9H caps compatibly along a morphism of closed covers and of test schemes.
* `Stacks.Chow.GysinAtInfinity.localizedChernClassAtInfinity_baseChange` — **Stacks 0GUI** for
  `c'_p`.
* `Stacks.Chow.GysinAtInfinity.localizedPowerSumClassAtInfinity_baseChange` — **Stacks 0GUI**
  for `P'_p`.

## References

* [Stacks Project, Tag 0GUI](https://stacks.math.columbia.edu/tag/0GUI)
* [Stacks Project, Tag 0F9K](https://stacks.math.columbia.edu/tag/0F9K)
* [Stacks Project, Tag 0GUG](https://stacks.math.columbia.edu/tag/0GUG)
* [Stacks Project, Tag 0GUH](https://stacks.math.columbia.edu/tag/0GUH)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The localized class of a closed cover along a morphism of covers -/

section ClosedCover

variable (C : ChowSituation.{u}) {X X₁ X₂ X' X₁' X₂' : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sX₁ : X₁ ⟶ C.S) [LocallyOfFiniteType sX₁] (sX₂ : X₂ ⟶ C.S)
  [LocallyOfFiniteType sX₂] (i₁ : X₁ ⟶ X) [IsClosedImmersion i₁] (hi₁ : i₁ ≫ sX = sX₁)
  (i₂ : X₂ ⟶ X) [IsClosedImmersion i₂] (hi₂ : i₂ ≫ sX = sX₂)
  (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ) {p : ℤ}
  (κ : chowCohomologyComponent C (gysinSystemOfInvertible C) sX₂ p)
  (hκ : chowCohomologyRestriction C (gysinSystemOfInvertible C) sX₂ (pullback.snd i₁ i₂) p
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) κ = 0)
  (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (sX₁' : X₁' ⟶ C.S) [LocallyOfFiniteType sX₁']
  (sX₂' : X₂' ⟶ C.S) [LocallyOfFiniteType sX₂'] (i₁' : X₁' ⟶ X') [IsClosedImmersion i₁']
  (hi₁' : i₁' ≫ sX' = sX₁') (i₂' : X₂' ⟶ X') [IsClosedImmersion i₂'] (hi₂' : i₂' ≫ sX' = sX₂')
  (hcover' : Set.range i₁'.base ∪ Set.range i₂'.base = Set.univ)
  (κ' : chowCohomologyComponent C (gysinSystemOfInvertible C) sX₂' p)
  (hκ' : chowCohomologyRestriction C (gysinSystemOfInvertible C) sX₂' (pullback.snd i₁' i₂') p
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) κ' = 0)
  (φ : X' ⟶ X) (hφ : φ ≫ sX = sX') (a₁ : X₁' ⟶ X₁) (ha₁ : a₁ ≫ i₁ = i₁' ≫ φ)
  (a₂ : X₂' ⟶ X₂) [LocallyOfFiniteType a₂] (ha₂ : a₂ ≫ i₂ = i₂' ≫ φ)
  {V V' : Scheme.{u}} (t : V ⟶ X) [LocallyOfFiniteType t] (t' : V' ⟶ X') [LocallyOfFiniteType t']
  (m : V' ⟶ V) [IsProper m] (hm : m ≫ t = t' ≫ φ)

/-- The map `X'₂ ×_{X'} V' ⟶ X₂ ×_X V` induced by `a₂` and `m`. -/
def closedCoverTestMap :
    pullback i₂' t' ⟶ pullback i₂ t :=
  pullback.lift (pullback.fst i₂' t' ≫ a₂) (pullback.snd i₂' t' ≫ m) (by
    rw [Category.assoc, ha₂, ← Category.assoc, pullback.condition, Category.assoc,
      Category.assoc, hm])

omit [IsClosedImmersion i₂] [IsClosedImmersion i₂'] [LocallyOfFiniteType a₂]
  [LocallyOfFiniteType t] [LocallyOfFiniteType t'] [IsProper m] in
/-- The map `X'₂ ×_{X'} V' ⟶ X₂ ×_X V` followed by the projection to `X₂` is the projection to
`X'₂` followed by `a₂`. -/
@[reassoc (attr := simp)]
theorem closedCoverTestMap_fst :
    closedCoverTestMap i₂ i₂' φ a₂ ha₂ t t' m hm ≫ pullback.fst i₂ t =
      pullback.fst i₂' t' ≫ a₂ :=
  pullback.lift_fst _ _ _

omit [IsClosedImmersion i₂] [IsClosedImmersion i₂'] [LocallyOfFiniteType a₂]
  [LocallyOfFiniteType t] [LocallyOfFiniteType t'] [IsProper m] in
/-- The map `X'₂ ×_{X'} V' ⟶ X₂ ×_X V` followed by the projection to `V` is the projection to
`V'` followed by `m`. -/
@[reassoc (attr := simp)]
theorem closedCoverTestMap_snd :
    closedCoverTestMap i₂ i₂' φ a₂ ha₂ t t' m hm ≫ pullback.snd i₂ t =
      pullback.snd i₂' t' ≫ m :=
  pullback.lift_snd _ _ _

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sX₂] [IsClosedImmersion i₂]
  [LocallyOfFiniteType sX'] [LocallyOfFiniteType sX₂'] [IsClosedImmersion i₂']
  [LocallyOfFiniteType a₂] in
include hi₂ hi₂' hφ ha₂ in
/-- `a₂ : X'₂ ⟶ X₂` lies over the base. -/
theorem closedCover_a₂_comp_structure : a₂ ≫ sX₂ = sX₂' := by
  rw [← hi₂, ← hi₂', ← hφ, ← Category.assoc, ha₂, Category.assoc]

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sX₂] [LocallyOfFiniteType sX']
  [LocallyOfFiniteType sX₂'] [IsClosedImmersion i₂] [IsClosedImmersion i₂']
  [LocallyOfFiniteType a₂] [LocallyOfFiniteType t] [LocallyOfFiniteType t'] [IsProper m] in
include hi₂ hi₂' hφ in
/-- The map `X'₂ ×_{X'} V' ⟶ X₂ ×_X V` lies over the base. -/
theorem closedCoverTestMap_comp_structure :
    closedCoverTestMap i₂ i₂' φ a₂ ha₂ t t' m hm ≫ pullback.fst i₂ t ≫ sX₂ =
      pullback.fst i₂' t' ≫ sX₂' := by
  rw [← Category.assoc, closedCoverTestMap_fst, Category.assoc,
    closedCover_a₂_comp_structure C sX sX₂ i₂ hi₂ sX' sX₂' i₂' hi₂' φ hφ a₂ ha₂]

/-- The map `X'₂ ×_{X'} V' ⟶ X₂ ×_X V` is proper when `m` is. -/
instance isProper_closedCoverTestMap : IsProper (closedCoverTestMap i₂ i₂' φ a₂ ha₂ t t' m hm) := by
  have : IsProper (closedCoverTestMap i₂ i₂' φ a₂ ha₂ t t' m hm ≫ pullback.snd i₂ t) := by
    rw [closedCoverTestMap_snd]
    infer_instance
  exact IsProper.of_comp _ (pullback.snd i₂ t)

/-- A class operates the same way at two equal test morphisms. -/
theorem idRule_heq_of_eq {Y V₀ : Scheme.{u}} {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {n : ℤ}
    (c : chowCohomologyComponent C (gysinSystemOfInvertible C) sY n) {v v' : V₀ ⟶ Y}
    [LocallyOfFiniteType v] [LocallyOfFiniteType v'] (h : v = v') (k : ℤ)
    {x : chowGroup C (v ≫ sY) k} {x' : chowGroup C (v' ≫ sY) k} (hx : x ≍ x') :
    c.idRule C sY (gysinSystemOfInvertible C) v k x ≍
      c.idRule C sY (gysinSystemOfInvertible C) v' k x' := by
  subst h
  cases hx
  rfl

include hcover hcover' hφ ha₁ in
/-- **The localized class of Stacks 0F9H along a morphism of closed covers.** Let `φ : X' ⟶ X`
carry the cover `X' = X'₁ ∪ X'₂` into `X = X₁ ∪ X₂` (by `a_j : X'_j ⟶ X_j`), let `κ' ∈ A^p(X'₂)`
operate as `κ ∈ A^p(X₂)` does through `a₂`, and let `m : V' ⟶ V` be a proper morphism of test
schemes over `φ`. Then pushing `κ'_{loc} ∩ y'` forward along `X'₂ ×_{X'} V' ⟶ X₂ ×_X V` gives
`κ_{loc} ∩ m_* y'`. -/
theorem chowPush_closedCoverLocalizedClass_cap_baseChange
    (hres : ∀ {U : Scheme.{u}} (v : U ⟶ X₂') [LocallyOfFiniteType v] (k : ℤ)
      (α : chowGroup C (v ≫ sX₂') k) (α' : chowGroup C ((v ≫ a₂) ≫ sX₂) k), α ≍ α' →
      κ'.idRule C sX₂' (gysinSystemOfInvertible C) v k α ≍
        κ.idRule C sX₂ (gysinSystemOfInvertible C) (v ≫ a₂) k α')
    (k : ℤ) (y' : chowGroup C (t' ≫ sX') k) :
    chowPush C (pullback.fst i₂' t' ≫ sX₂') (pullback.fst i₂ t ≫ sX₂)
        (closedCoverTestMap i₂ i₂' φ a₂ ha₂ t t' m hm)
        (closedCoverTestMap_comp_structure C sX sX₂ i₂ hi₂ sX' sX₂' i₂' hi₂' φ hφ a₂ ha₂ t t' m hm)
        (k - p)
        ((closedCoverLocalizedClass C sX' sX₁' sX₂' i₁' hi₁' i₂' hi₂' hcover' κ' hκ').cap t' k y') =
      (closedCoverLocalizedClass C sX sX₁ sX₂ i₁ hi₁ i₂ hi₂ hcover κ hκ).cap t k
        (chowPush C (t' ≫ sX') (t ≫ sX) m (by rw [← Category.assoc, hm, Category.assoc, hφ]) k
          y') := by
  have hs₂ : a₂ ≫ sX₂ = sX₂' :=
    closedCover_a₂_comp_structure C sX sX₂ i₂ hi₂ sX' sX₂' i₂' hi₂' φ hφ a₂ ha₂
  have hs₂' := closedCoverTestMap_comp_structure C sX sX₂ i₂ hi₂ sX' sX₂' i₂' hi₂' φ hφ a₂ ha₂
    t t' m hm
  obtain ⟨x₁, x₂, rfl⟩ := exists_chowPush_add_chowPush_eq C (t' ≫ sX')
    (pullback.fst i₁' t' ≫ sX₁') (pullback.fst i₂' t' ≫ sX₂') (pullback.snd i₁' t')
    (pullbackSnd_comp_structureMorphism_eq C sX₁' sX' i₁' hi₁' t') (pullback.snd i₂' t')
    (pullbackSnd_comp_structureMorphism_eq C sX₂' sX' i₂' hi₂' t')
    (range_pullbackSnd_union_range_pullbackSnd i₁' i₂' hcover' t') k y'
  rw [map_add, closedCoverLocalizedClass_cap_pushforward_left,
    closedCoverLocalizedClass_cap_pushforward_right, zero_add]
  rw [map_add,
    chowPush_comp C _ _ _ (pullback.snd i₁' t') m (pullback.snd i₁' t' ≫ m) rfl _ _
      (by rw [Category.assoc, ← Category.assoc m, hm, Category.assoc, hφ,
        pullbackSnd_comp_structureMorphism_eq C sX₁' sX' i₁' hi₁' t']),
    chowPush_comp C _ _ _ (pullback.snd i₂' t') m (pullback.snd i₂' t' ≫ m) rfl _ _
      (by rw [Category.assoc, ← Category.assoc m, hm, Category.assoc, hφ,
        pullbackSnd_comp_structureMorphism_eq C sX₂' sX' i₂' hi₂' t'])]
  have e : ∀ z, (closedCoverLocalizedClass C sX sX₁ sX₂ i₁ hi₁ i₂ hi₂ hcover κ hκ).cap t k z =
      closedCoverLocalizedCap C sX sX₁ sX₂ i₁ hi₁ i₂ hi₂ hcover κ hκ t k z := fun _ ↦ rfl
  simp only [e]
  rw [map_add, closedCoverLocalizedCap_chowPush_left C sX sX₁ sX₂ i₁ hi₁ i₂ hi₂ hcover κ hκ t _
      (closedCoverTestMap i₁ i₁' φ a₁ ha₁ t t' m hm)
      (closedCoverTestMap_comp_structure C sX sX₁ i₁ hi₁ sX' sX₁' i₁' hi₁' φ hφ a₁ ha₁ t t' m hm)
      _ (closedCoverTestMap_snd i₁ i₁' φ a₁ ha₁ t t' m hm), zero_add,
    closedCoverLocalizedCap_chowPush_right C sX sX₁ sX₂ i₁ hi₁ i₂ hi₂ hcover κ hκ t _
      (closedCoverTestMap i₂ i₂' φ a₂ ha₂ t t' m hm)
      hs₂' _ (closedCoverTestMap_snd i₂ i₂' φ a₂ ha₂ t t' m hm),
    idRule_chowPush_of_eq C sX₂ κ (pullback.fst i₂ t)
      (closedCoverTestMap i₂ i₂' φ a₂ ha₂ t t' m hm ≫ pullback.fst i₂ t)
      (closedCoverTestMap i₂ i₂' φ a₂ ha₂ t t' m hm) rfl _
      (by rwa [Category.assoc])]
  refine eq_of_heq (properChowPushforward_heq_congr_base C _
    (by rw [Category.assoc, hs₂']) rfl _ _ rfl _ _ _ _ ?_)
  have hs : pullback.fst i₂' t' ≫ sX₂' = (pullback.fst i₂' t' ≫ a₂) ≫ sX₂ := by
    rw [Category.assoc, hs₂]
  refine (hres (pullback.fst i₂' t') k x₂ (chowGroupCongr C hs k x₂)
    (chowGroupCongr_heq C _ _ _).symm).trans ?_
  exact idRule_heq_of_eq C κ (closedCoverTestMap_fst i₂ i₂' φ a₂ ha₂ t t' m hm).symm k
    ((chowGroupCongr_heq C _ _ _).trans (chowGroupCongr_heq C _ _ _).symm)

end ClosedCover

/-! ### The cap operation of the recipe of Stacks 0F9K -/

section Recipe

variable (C : ChowSituation.{u}) (G : GysinSystem C)

/-- Pushing the cap of a class forward out of the base change does not see the presentation of its
morphism by an equal one. -/
theorem chowPush_bivariantClassCongr_cap {Y X T A : Scheme.{u}} (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (sX : X ⟶ C.S) [LocallyOfFiniteType sX] {f f' : Y ⟶ X}
    [LocallyOfFiniteType f] [LocallyOfFiniteType f'] (hff : f = f') (hf : f ≫ sX = sY)
    (hf' : f' ≫ sX = sY) (n : ℤ) (a : BivariantClass C G sY sX f hf n) (t : T ⟶ X)
    [LocallyOfFiniteType t] (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (v : pullback f' t ⟶ A)
    [IsProper v] (v₀ : pullback f t ⟶ A) [IsProper v₀]
    (hv₀ : v₀ = (pullback.congrHom hff rfl).hom ≫ v) (hv : v ≫ sA = pullback.fst f' t ≫ sY)
    (hv₀' : v₀ ≫ sA = pullback.fst f t ≫ sY) (k : ℤ) (α : chowGroup C (t ≫ sX) k) :
    chowPush C (pullback.fst f' t ≫ sY) sA v hv (k - n)
        ((bivariantClassCongr C G sY sX hff hf hf' n a).cap t k α) =
      chowPush C (pullback.fst f t ≫ sY) sA v₀ hv₀' (k - n) (a.cap t k α) := by
  subst hff
  obtain rfl : v₀ = v := by
    rw [hv₀, show (pullback.congrHom (rfl : f = f) (rfl : t = t)).hom = 𝟙 _ by
      refine pullback.hom_ext ?_ ?_ <;> simp, Category.id_comp]
  rfl

end Recipe

namespace GysinAtInfinity

attribute [local instance] lineInfinityDivisor_isEffectiveCartierDivisor

section TestMap

variable {X W Z S : Scheme.{u}} (f : X ⟶ S) (b : W ⟶ projectiveLineProduct f) (jZ : Z ⟶ X)

/-- On a test scheme `t : T₀ ⟶ X`, the base change `E ×_{W_∞} (W_∞ ×_X T₀) ⟶ Z ×_X T₀` of the
morphism `E ⟶ Z`. -/
def preimageTestMap {T₀ : Scheme.{u}} (t : T₀ ⟶ X) :
    pullback (preimageInclusion f b jZ) (pullback.fst (modificationProjectionAtInfinity f b) t) ⟶
      pullback jZ t :=
  pullback.lift (pullback.fst _ _ ≫ preimageProjection f b jZ)
    (pullback.snd _ _ ≫ pullback.snd (modificationProjectionAtInfinity f b) t) (by
      rw [Category.assoc, ← pullback.condition, ← Category.assoc, pullback.condition,
        Category.assoc, Category.assoc, pullback.condition])

/-- The base change `E ×_{W_∞} (W_∞ ×_X T₀) ⟶ Z ×_X T₀` followed by the projection to `Z` is the
projection to `E` followed by `E ⟶ Z`. -/
@[reassoc (attr := simp)]
theorem preimageTestMap_fst {T₀ : Scheme.{u}} (t : T₀ ⟶ X) :
    preimageTestMap f b jZ t ≫ pullback.fst jZ t =
      pullback.fst _ _ ≫ preimageProjection f b jZ :=
  pullback.lift_fst _ _ _

/-- The base change `E ×_{W_∞} (W_∞ ×_X T₀) ⟶ Z ×_X T₀` followed by the projection to `T₀` is the
projection to `W_∞ ×_X T₀` followed by the projection to `T₀`. -/
@[reassoc (attr := simp)]
theorem preimageTestMap_snd {T₀ : Scheme.{u}} (t : T₀ ⟶ X) :
    preimageTestMap f b jZ t ≫ pullback.snd jZ t =
      pullback.snd _ _ ≫ pullback.snd (modificationProjectionAtInfinity f b) t :=
  pullback.lift_snd _ _ _

/-- The base change of `E ⟶ Z` is the associativity isomorphism, followed by the identification
of the two fibre products of `E ⟶ X` and the base change of Stacks 0EPK. -/
theorem preimageTestMap_eq {T₀ : Scheme.{u}} (t : T₀ ⟶ X) :
    preimageTestMap f b jZ t =
      (pullbackRightPullbackFstIso (modificationProjectionAtInfinity f b) t
          (preimageInclusion f b jZ)).hom ≫
        (pullback.congrHom pullback.condition rfl).hom ≫
          bivariantPushforwardBaseChange (preimageProjection f b jZ) jZ t := by
  refine pullback.hom_ext ?_ ?_ <;> simp

/-- If `W_∞ ⟶ X` is proper, the base change `E ×_{W_∞} (W_∞ ×_X T₀) ⟶ Z ×_X T₀` is proper. -/
instance isProper_preimageTestMap [IsProper (modificationProjectionAtInfinity f b)]
    {T₀ : Scheme.{u}} (t : T₀ ⟶ X) : IsProper (preimageTestMap f b jZ t) := by
  rw [preimageTestMap_eq]
  infer_instance

/-- The base change of `E ⟶ Z` lies over the base. -/
theorem preimageTestMap_comp_structure {S' : Scheme.{u}} (s : X ⟶ S') {T₀ : Scheme.{u}}
    (t : T₀ ⟶ X) :
    preimageTestMap f b jZ t ≫ pullback.fst jZ t ≫ jZ ≫ s =
      pullback.fst (preimageInclusion f b jZ)
          (pullback.fst (modificationProjectionAtInfinity f b) t) ≫
        preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b ≫ s := by
  rw [preimageTestMap_fst_assoc, ← Category.assoc (preimageProjection f b jZ),
    ← pullback.condition, Category.assoc]

end TestMap

section CapFormula

variable (C : ChowSituation.{u}) {X W Z : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))
  (jZ : Z ⟶ X) [IsClosedImmersion jZ] (p : ℤ)

/-- **The cap operation of the recipe of Stacks 0F9K.** For a class `a ∈ A^p(E ⟶ W_∞)`, the class
`(E ⟶ Z)_* ∘ a ∘ C ∈ A^p(Z ⟶ X)` caps, on a test scheme `t : T₀ ⟶ X`, as
`α ↦ (E ⟶ Z)'_*(a ∩ (C ∩ α))`. -/
theorem cap_localizedClassAtInfinity
    (a : BivariantClass C (gysinSystemOfInvertible C)
      (preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b ≫ f)
      (modificationProjectionAtInfinity f b ≫ f) (preimageInclusion f b jZ) rfl p)
    {T₀ : Scheme.{u}} (t : T₀ ⟶ X) [LocallyOfFiniteType t] (k : ℤ)
    (α : chowGroup C (t ≫ f) k) :
    (canonicalBivariantProperPushforward C
      (preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b ≫ f) (jZ ≫ f) f
      (preimageProjection f b jZ) jZ (preimageProjection_comp C f b jZ) rfl p
      (bivariantClassCongr C (gysinSystemOfInvertible C)
        (preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b ≫ f) f
        pullback.condition
        (comp_comp_structureMorphism_eq rfl rfl)
        (comp_comp_structureMorphism_eq (preimageProjection_comp C f b jZ) rfl) p
        (bivariantClassCongrDeg C (gysinSystemOfInvertible C)
          (preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b ≫ f) f
          (preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b)
          (comp_comp_structureMorphism_eq rfl rfl) (add_zero p)
          (bivariantCompositeOfInvertible C
            (preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b ≫ f)
            (modificationProjectionAtInfinity f b ≫ f) f (preimageInclusion f b jZ)
            (modificationProjectionAtInfinity f b) rfl rfl p 0 a
            (gysinAtInfinityClass C f b hA))))).cap t k α =
      chowGroupDegreeEquiv C (pullback.fst jZ t ≫ jZ ≫ f) (by ring)
        (chowPush C (pullback.fst (preimageInclusion f b jZ)
              (pullback.fst (modificationProjectionAtInfinity f b) t) ≫
            preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b ≫ f)
          (pullback.fst jZ t ≫ jZ ≫ f) (preimageTestMap f b jZ t)
          (preimageTestMap_comp_structure f b jZ f t) (k - 0 - p)
          (a.cap (pullback.fst (modificationProjectionAtInfinity f b) t) (k - 0)
            ((gysinAtInfinityClass C f b hA).cap t k α))) := by
  have hv : ((pullback.congrHom pullback.condition rfl).hom ≫
      bivariantPushforwardBaseChange (preimageProjection f b jZ) jZ t) ≫
        (pullback.fst jZ t ≫ jZ ≫ f) =
      pullback.fst (preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b) t ≫
        (preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b ≫ f) := by
    simp only [Category.assoc, bivariantPushforwardBaseChange_fst_assoc, pullback.congrHom_hom,
      pullback.lift_fst_assoc, Category.id_comp]
    rw [preimageProjection_comp C f b jZ]
    rfl
  have hw : ((pullbackRightPullbackFstIso (modificationProjectionAtInfinity f b) t
        (preimageInclusion f b jZ)).hom ≫ (pullback.congrHom pullback.condition rfl).hom ≫
      bivariantPushforwardBaseChange (preimageProjection f b jZ) jZ t) ≫
        (pullback.fst jZ t ≫ jZ ≫ f) =
      pullback.fst (preimageInclusion f b jZ)
          (pullback.fst (modificationProjectionAtInfinity f b) t) ≫
        preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b ≫ f := by
    rw [← preimageTestMap_eq]
    exact preimageTestMap_comp_structure f b jZ f t
  refine eq_of_heq (HEq.trans ?_ (chowGroupDegreeEquiv_heq C _ _ _).symm)
  refine HEq.trans (heq_of_eq (canonicalBivariantProperPushforward_cap C _ (jZ ≫ f) f
    (preimageProjection f b jZ) jZ (preimageProjection_comp C f b jZ) rfl p _ t k α)) ?_
  refine HEq.trans (heq_of_eq (chowPush_bivariantClassCongr_cap C (gysinSystemOfInvertible C) _ f
    pullback.condition _ _ p _ t _ _
    ((pullback.congrHom pullback.condition rfl).hom ≫
      bivariantPushforwardBaseChange (preimageProjection f b jZ) jZ t) rfl
    (bivariantPushforwardBaseChange_comp_structure (preimageProjection_comp C f b jZ) jZ t)
    hv k α)) ?_
  rw [bivariantClassCongrDeg_cap, bivariantCompositeOfInvertible, bivariantComposite_cap,
    bivariantCompositeCap_apply]
  refine HEq.trans (properChowPushforward_heq C _ _ _ _ (by ring : k - p = k - 0 - p) _
    (properPushforwardDescends C _ _ _ _ _)
    (HEq.trans (chowGroupDegreeEquiv_heq C _ _ _) (chowGroupDegreeEquiv_heq C _ _ _)))
    (heq_of_eq ?_)
  refine Eq.trans ?_ (chowPush_congr C _ _ (preimageTestMap_eq f b jZ t).symm hw _ _ _)
  exact chowPush_comp C _ _ _ _ _ _ rfl (pullbackRightPullbackFstIso_hom_comp_fst_comp _ _ _ t)
    hv hw (k - 0 - p) _

end CapFormula

/-! ### The base change of the data of Stacks 0F9K -/

section Geometry

variable {X X' W Z S : Scheme.{u}} (f : X ⟶ S) (b : W ⟶ projectiveLineProduct f) (jZ : Z ⟶ X)
  (q : X' ⟶ X)

/-- The morphism `E' ⟶ E` from the inverse image of `Z' = Z ×_X X'` in `W'_∞` to the inverse image
of `Z` in `W_∞`. -/
def preimageBaseChangeMap :
    pullback (modificationProjectionAtInfinity (q ≫ f) (baseChangedModification f b q))
        (pullback.snd jZ q) ⟶
      pullback (modificationProjectionAtInfinity f b) jZ :=
  pullback.lift (preimageInclusion (q ≫ f) (baseChangedModification f b q) (pullback.snd jZ q) ≫
      baseChangedInfinityMap f b q)
    (preimageProjection (q ≫ f) (baseChangedModification f b q) (pullback.snd jZ q) ≫
      pullback.fst jZ q) (by
    rw [Category.assoc, (isPullback_baseChangedInfinityMap f b q).w, ← Category.assoc,
      pullback.condition, Category.assoc, Category.assoc, pullback.condition])

/-- The morphism `E' ⟶ E` followed by `E ⟶ W_∞` is `E' ⟶ W'_∞ ⟶ W_∞`. -/
@[reassoc (attr := simp)]
theorem preimageBaseChangeMap_fst :
    preimageBaseChangeMap f b jZ q ≫ preimageInclusion f b jZ =
      preimageInclusion (q ≫ f) (baseChangedModification f b q) (pullback.snd jZ q) ≫
        baseChangedInfinityMap f b q :=
  pullback.lift_fst _ _ _

/-- The morphism `E' ⟶ E` followed by `E ⟶ Z` is `E' ⟶ Z' ⟶ Z`. -/
@[reassoc (attr := simp)]
theorem preimageBaseChangeMap_snd :
    preimageBaseChangeMap f b jZ q ≫ preimageProjection f b jZ =
      preimageProjection (q ≫ f) (baseChangedModification f b q) (pullback.snd jZ q) ≫
        pullback.fst jZ q :=
  pullback.lift_snd _ _ _

/-- `W'_∞ ⟶ W_∞ ⟶ X ⟶ S` is `W'_∞ ⟶ X' ⟶ X ⟶ S`. -/
theorem baseChangedInfinityMap_comp_structure {S' : Scheme.{u}} (s : X ⟶ S') :
    baseChangedInfinityMap f b q ≫ (modificationProjectionAtInfinity f b ≫ s) =
      modificationProjectionAtInfinity (q ≫ f) (baseChangedModification f b q) ≫ (q ≫ s) := by
  rw [← Category.assoc, (isPullback_baseChangedInfinityMap f b q).w, Category.assoc]

end Geometry

/-! ### The hypotheses of Stacks 0F9K after base change -/

section Hypotheses

variable {X X' W Z V : Scheme.{u}} {S : Scheme.{u}} (f : X ⟶ S) (b : W ⟶ projectiveLineProduct f)
  (jZ : Z ⟶ X) (iV : V ⟶ modificationFibreAtInfinity f b) (q : X' ⟶ X)

/-- If `T ⊆ W_∞` contains every point over `X \ Z`, then `T' = T ×_{W_∞} W'_∞` contains every
point of `W'_∞` over `X' \ Z'`. -/
theorem baseChange_mem_range
    (hV : ∀ w, (modificationProjectionAtInfinity f b).base w ∉ Set.range jZ.base →
      w ∈ Set.range iV.base) :
    ∀ w, (modificationProjectionAtInfinity (q ≫ f) (baseChangedModification f b q)).base w ∉
        Set.range (pullback.snd jZ q).base →
      w ∈ Set.range (pullback.snd iV (baseChangedInfinityMap f b q)).base := by
  intro w hw
  rw [Scheme.Pullback.range_snd]
  refine hV _ fun hZ ↦ hw ?_
  rw [Scheme.Pullback.range_snd]
  have key : q ((modificationProjectionAtInfinity (q ≫ f) (baseChangedModification f b q)) w) =
      (modificationProjectionAtInfinity f b) ((baseChangedInfinityMap f b q) w) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
      (isPullback_baseChangedInfinityMap f b q).w]
  rwa [Set.mem_preimage, key]

/-- `Q'|_{W'_∞} = (W'_∞ ⟶ W)^* Q` is the pullback of `Q|_{W_∞}` along `W'_∞ ⟶ W_∞`. -/
theorem nonempty_restrictionAtInfinity_baseChange_iso (Q : DerivedCategory W.Modules) :
    Nonempty (restrictionAtInfinity (q ≫ f) (baseChangedModification f b q)
        ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (pullback.fst b (familyBaseChange f q)).toLRSHom.toShHom).obj Q) ≅
      (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (baseChangedInfinityMap f b q).toLRSHom.toShHom).obj (restrictionAtInfinity f b Q)) :=
  nonempty_derivedPullback_iso_of_comp_eq _ _ _ _ (baseChangedInfinityMap_fst f b q).symm Q

/-- If `Q|_T` is finite locally free of rank `< p` in degree `0`, so is `Q'|_{T'}`. -/
theorem restrictionIsLocallyFreeOfRankLT_baseChange {Q : DerivedCategory W.Modules} {p : ℕ}
    (hres : RestrictionIsLocallyFreeOfRankLT f b iV Q p) :
    RestrictionIsLocallyFreeOfRankLT (q ≫ f) (baseChangedModification f b q)
      (pullback.snd iV (baseChangedInfinityMap f b q))
      ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (pullback.fst b (familyBaseChange f q)).toLRSHom.toShHom).obj Q) p := by
  obtain ⟨M, hM, ⟨e⟩⟩ := exists_iso_single_derivedPullback_of_comp_eq
    (pullback.snd iV (baseChangedInfinityMap f b q)) (baseChangedInfinityMap f b q)
    (pullback.fst iV (baseChangedInfinityMap f b q)) iV pullback.condition.symm
    (restrictionAtInfinity f b Q) hres
  exact ⟨M, hM, ⟨(Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
    (pullback.snd iV (baseChangedInfinityMap f b q)).toLRSHom.toShHom).mapIso
      (nonempty_restrictionAtInfinity_baseChange_iso f b q Q).some ≪≫ e⟩⟩

/-- If `Q|_T` is zero, so is `Q'|_{T'}`. -/
theorem isZero_restriction_baseChange {Q : DerivedCategory W.Modules}
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      iV.toLRSHom.toShHom).obj (restrictionAtInfinity f b Q))) :
    IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (pullback.snd iV (baseChangedInfinityMap f b q)).toLRSHom.toShHom).obj
      (restrictionAtInfinity (q ≫ f) (baseChangedModification f b q)
        ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (pullback.fst b (familyBaseChange f q)).toLRSHom.toShHom).obj Q))) :=
  (isZero_derivedPullback_of_comp_eq (pullback.snd iV (baseChangedInfinityMap f b q))
    (baseChangedInfinityMap f b q) (pullback.fst iV (baseChangedInfinityMap f b q)) iV
    pullback.condition.symm (restrictionAtInfinity f b Q) hzero).of_iso
    ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (pullback.snd iV (baseChangedInfinityMap f b q)).toLRSHom.toShHom).mapIso
        (nonempty_restrictionAtInfinity_baseChange_iso f b q Q).some)

/-- `Q'|_{E'}` is the pullback of `Q|_E` along `E' ⟶ E`. -/
theorem nonempty_restriction_preimageBaseChangeMap_iso (Q : DerivedCategory W.Modules) :
    Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (preimageBaseChangeMap f b jZ q).toLRSHom.toShHom).obj
        ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (preimageInclusion f b jZ).toLRSHom.toShHom).obj (restrictionAtInfinity f b Q)) ≅
      (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (preimageInclusion (q ≫ f) (baseChangedModification f b q)
            (pullback.snd jZ q)).toLRSHom.toShHom).obj
        (restrictionAtInfinity (q ≫ f) (baseChangedModification f b q)
          ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
            (pullback.fst b (familyBaseChange f q)).toLRSHom.toShHom).obj Q))) :=
  ⟨(nonempty_derivedPullback_iso_of_comp_eq _ _ _ _ (preimageBaseChangeMap_fst f b jZ q).symm
      (restrictionAtInfinity f b Q)).some.symm ≪≫
    (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (preimageInclusion (q ≫ f) (baseChangedModification f b q)
        (pullback.snd jZ q)).toLRSHom.toShHom).mapIso
      (nonempty_restrictionAtInfinity_baseChange_iso f b q Q).some.symm⟩

end Hypotheses

section BaseChange

variable (C : ChowSituation.{u}) {X X' W Z : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  [IsIso (pullback.snd b (projectiveLineAffineChart f))]
  (jZ : Z ⟶ X) [IsClosedImmersion jZ] (q : X' ⟶ X) [LocallyOfFiniteType q] (p : ℤ)

attribute [local instance] isIso_baseChangedModification_chart

/-- The morphism `E' ⟶ E` is locally of finite type. -/
instance locallyOfFiniteType_preimageBaseChangeMap :
    LocallyOfFiniteType (preimageBaseChangeMap f b jZ q) :=
  have : LocallyOfFiniteType (preimageBaseChangeMap f b jZ q ≫
      (preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b ≫ f)) := by
    rw [preimageBaseChangeMap_fst_assoc, ← Category.assoc (baseChangedInfinityMap f b q),
      (isPullback_baseChangedInfinityMap f b q).w]
    infer_instance
  locallyOfFiniteType_of_comp _
    (preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b ≫ f)

/-- On a test scheme `g : T₀ ⟶ X'`, the comparison
`E' ×_{W'_∞} (W'_∞ ×_{X'} T₀) ⟶ E ×_{W_∞} (W_∞ ×_X T₀)` of the base changes of `E' ⟶ W'_∞` and
of `E ⟶ W_∞`. -/
abbrev preimageTestComparison {T₀ : Scheme.{u}} (g : T₀ ⟶ X') :=
  closedCoverTestMap (preimageInclusion f b jZ)
    (preimageInclusion (q ≫ f) (baseChangedModification f b q) (pullback.snd jZ q))
    (baseChangedInfinityMap f b q) (preimageBaseChangeMap f b jZ q)
    (preimageBaseChangeMap_fst f b jZ q)
    (pullback.fst (modificationProjectionAtInfinity f b) (g ≫ q))
    (pullback.fst (modificationProjectionAtInfinity (q ≫ f) (baseChangedModification f b q)) g)
    (baseChangeTestInfinityMap f b q g) (pullbackLiftOfIsPullback_fst _ g)

/-- **The base change of the recipe of Stacks 0F9K.** Let `K ∈ A^p(Z ⟶ X)` cap as
`(E ⟶ Z)_* ∘ a ∘ C` and `K' ∈ A^p(Z' ⟶ X')` as `(E' ⟶ Z')_* ∘ a' ∘ C'`, where `a' ∈ A^p(E' ⟶ W'_∞)`
caps compatibly with `a ∈ A^p(E ⟶ W_∞)` under the identifications `W'_∞ ×_{X'} T₀ ≅ W_∞ ×_X T₀`.
Then `K'` is the restriction of `K` (Remark 0F9Z), read on `Z' ⟶ X'`. -/
theorem eq_bivariantTransport_bivariantRestriction_of_cap
    (a : BivariantClass C (gysinSystemOfInvertible C)
      (preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b ≫ f)
      (modificationProjectionAtInfinity f b ≫ f) (preimageInclusion f b jZ) rfl p)
    (a' : BivariantClass C (gysinSystemOfInvertible C)
      (preimageInclusion (q ≫ f) (baseChangedModification f b q) (pullback.snd jZ q) ≫
        modificationProjectionAtInfinity (q ≫ f) (baseChangedModification f b q) ≫ q ≫ f)
      (modificationProjectionAtInfinity (q ≫ f) (baseChangedModification f b q) ≫ q ≫ f)
      (preimageInclusion (q ≫ f) (baseChangedModification f b q) (pullback.snd jZ q)) rfl p)
    (ha : ∀ {T₀ : Scheme.{u}} (g : T₀ ⟶ X') [LocallyOfFiniteType g] (k : ℤ)
      (y : chowGroup C (pullback.fst (modificationProjectionAtInfinity (q ≫ f)
        (baseChangedModification f b q)) g ≫
          (modificationProjectionAtInfinity (q ≫ f) (baseChangedModification f b q) ≫ q ≫ f)) k),
      chowPush C _ _ (preimageTestComparison C f b jZ q g)
          (closedCoverTestMap_comp_structure C _ _ _ rfl _ _ _ rfl _
            (baseChangedInfinityMap_comp_structure f b q f) _
            (preimageBaseChangeMap_fst f b jZ q) _ _ _ _) (k - p)
          (a'.cap (pullback.fst (modificationProjectionAtInfinity (q ≫ f)
            (baseChangedModification f b q)) g) k y) =
        a.cap (pullback.fst (modificationProjectionAtInfinity f b) (g ≫ q)) k
          (chowPush C _ _ (baseChangeTestInfinityMap f b q g)
            (baseChangeTestInfinityMap_comp_structure C f b q g) k y))
    (K : BivariantClass C (gysinSystemOfInvertible C) (jZ ≫ f) f jZ rfl p)
    (hK : ∀ {T₀ : Scheme.{u}} (t : T₀ ⟶ X) [LocallyOfFiniteType t] (k : ℤ)
      (α : chowGroup C (t ≫ f) k),
      K.cap t k α = chowGroupDegreeEquiv C (pullback.fst jZ t ≫ jZ ≫ f) (by ring)
        (chowPush C _ _ (preimageTestMap f b jZ t) (preimageTestMap_comp_structure f b jZ f t)
          (k - 0 - p)
          (a.cap (pullback.fst (modificationProjectionAtInfinity f b) t) (k - 0)
            ((gysinAtInfinityClass C f b inferInstance).cap t k α))))
    (K' : BivariantClass C (gysinSystemOfInvertible C) (pullback.snd jZ q ≫ q ≫ f) (q ≫ f)
      (pullback.snd jZ q) rfl p)
    (hK' : ∀ {T₀ : Scheme.{u}} (t : T₀ ⟶ X') [LocallyOfFiniteType t] (k : ℤ)
      (α : chowGroup C (t ≫ q ≫ f) k),
      K'.cap t k α = chowGroupDegreeEquiv C
        (pullback.fst (pullback.snd jZ q) t ≫ pullback.snd jZ q ≫ q ≫ f) (by ring)
        (chowPush C _ _ (preimageTestMap (q ≫ f) (baseChangedModification f b q)
            (pullback.snd jZ q) t)
          (preimageTestMap_comp_structure (q ≫ f) (baseChangedModification f b q)
            (pullback.snd jZ q) (q ≫ f) t)
          (k - 0 - p)
          (a'.cap (pullback.fst (modificationProjectionAtInfinity (q ≫ f)
              (baseChangedModification f b q)) t) (k - 0)
            ((gysinAtInfinityClass C (q ≫ f) (baseChangedModification f b q) inferInstance).cap
              t k α)))) :
    K' = bivariantTransport C (gysinSystemOfInvertible C) (pullback.fst jZ q ≫ jZ ≫ f)
      (pullback.snd jZ q ≫ q ≫ f) (q ≫ f) (pullback.snd jZ q)
      (pullbackSnd_comp_structureMorphism_eq C (jZ ≫ f) f jZ rfl q) (pullback.snd jZ q) rfl
      (Iso.refl _) (Category.id_comp _) p (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
      (bivariantRestrictionOfInvertible C (jZ ≫ f) f jZ rfl q p K) := by
  refine BivariantClass.ext C _ _ _ _ _ _ ?_
  intro T₀ g _ k α
  rw [bivariantTransport_cap, bivariantTransportCap_apply, bivariantRestrictionOfInvertible_cap,
    bivariantRestrictionCap_apply, hK, hK', ← baseChangeTestInfinityMap_cap C f b q g k α, ← ha]
  have hmor : preimageTestComparison C f b jZ q g ≫ preimageTestMap f b jZ (g ≫ q) ≫
      (pullbackLeftPullbackSndIso jZ q g).inv ≫
        (transportPullbackIso (pullback.snd jZ q) (pullback.snd jZ q) (Iso.refl _)
          (Category.id_comp _) g).hom =
      preimageTestMap (q ≫ f) (baseChangedModification f b q) (pullback.snd jZ q) g := by
    refine pullback.hom_ext (pullback.hom_ext ?_ ?_) ?_
    · simp
    · simp only [Category.assoc, transportPullbackIso_hom_fst_assoc, Iso.refl_hom,
        Category.id_comp, pullbackLeftPullbackSndIso_inv_fst_snd, preimageTestMap_snd_assoc,
        closedCoverTestMap_snd_assoc, pullbackLiftOfIsPullback_snd_assoc, preimageTestMap_fst_assoc]
      conv_rhs => rw [← pullback.condition, ← Category.assoc, pullback.condition, Category.assoc,
        pullback.condition]
    · simp
  have hw1 : (preimageTestComparison C f b jZ q g ≫ preimageTestMap f b jZ (g ≫ q)) ≫
      (pullback.fst jZ (g ≫ q) ≫ jZ ≫ f) =
      pullback.fst (preimageInclusion (q ≫ f) (baseChangedModification f b q) (pullback.snd jZ q))
          (pullback.fst (modificationProjectionAtInfinity (q ≫ f)
            (baseChangedModification f b q)) g) ≫
        preimageInclusion (q ≫ f) (baseChangedModification f b q) (pullback.snd jZ q) ≫
          modificationProjectionAtInfinity (q ≫ f) (baseChangedModification f b q) ≫ q ≫ f := by
    rw [Category.assoc, preimageTestMap_comp_structure f b jZ f (g ≫ q)]
    exact closedCoverTestMap_comp_structure C _ _ _ rfl _ _ _ rfl _
      (baseChangedInfinityMap_comp_structure f b q f) _ (preimageBaseChangeMap_fst f b jZ q) _ _ _ _
  refine eq_of_heq ((chowGroupDegreeEquiv_heq C _ _ _).trans ?_)
  refine HEq.symm ((chowPushforwardOfIso_heq_of_heq C _ _
    (by ring : k - p = k - 0 - p) (chowPushforwardOfIso_heq_of_heq C _ _
      (by ring : k - p = k - 0 - p) (chowGroupDegreeEquiv_heq C _ _ _))).trans (heq_of_eq ?_))
  rw [chowPush_comp C _ _ _ (preimageTestComparison C f b jZ q g)
    (preimageTestMap f b jZ (g ≫ q)) _ rfl _ _ hw1]
  exact properChowPushforward_comp₃_eq C _ _ _ _
    (by rwa [Category.assoc]) _ _ _ _ _ _ _ _ _ _

end BaseChange

/-! ### Stacks 0GUI -/

section Statement

variable (C : ChowSituation.{u}) {X X' W Z V : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))
  (jZ : Z ⟶ X) [IsClosedImmersion jZ]
  (iV : V ⟶ modificationFibreAtInfinity f b) [IsClosedImmersion iV]
  (q : X' ⟶ X) [LocallyOfFiniteType q] {Q : DerivedCategory W.Modules}
  (hQ : HasDefinedChernClasses Q) (p : ℕ)

omit [LocallyOfFiniteType f] [IsProper b] [IsClosedImmersion jZ] [LocallyOfFiniteType q] in
/-- `E' ⟶ E` lies over the base. -/
theorem preimageBaseChangeMap_comp_structure :
    preimageBaseChangeMap f b jZ q ≫
        (preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b ≫ f) =
      preimageInclusion (q ≫ f) (baseChangedModification f b q) (pullback.snd jZ q) ≫
        modificationProjectionAtInfinity (q ≫ f) (baseChangedModification f b q) ≫ q ≫ f := by
  rw [preimageBaseChangeMap_fst_assoc, baseChangedInfinityMap_comp_structure]

/-- `c_p(Q'|_{E'})` operates as `c_p(Q|_E)` does through `E' ⟶ E`. -/
theorem idRule_chernClassOnPreimage_baseChange_heq {U : Scheme.{u}}
    (v : U ⟶ pullback (modificationProjectionAtInfinity (q ≫ f) (baseChangedModification f b q))
      (pullback.snd jZ q)) [LocallyOfFiniteType v] (k : ℤ)
    (α : chowGroup C (v ≫ (preimageInclusion (q ≫ f) (baseChangedModification f b q)
      (pullback.snd jZ q) ≫ modificationProjectionAtInfinity (q ≫ f)
        (baseChangedModification f b q) ≫ q ≫ f)) k)
    (α' : chowGroup C ((v ≫ preimageBaseChangeMap f b jZ q) ≫
      (preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b ≫ f)) k) (hα : α ≍ α') :
    (chernClassOnPreimage C (q ≫ f) (baseChangedModification f b q) (pullback.snd jZ q)
        (hasDefinedChernClasses_derivedPullback (pullback.fst b (familyBaseChange f q)) hQ)
        p).idRule C _ (gysinSystemOfInvertible C) v k α ≍
      (chernClassOnPreimage C f b jZ hQ p).idRule C _ (gysinSystemOfInvertible C)
        (v ≫ preimageBaseChangeMap f b jZ q) k α' :=
  idRule_heq_of_res_eq C _ (preimageBaseChangeMap f b jZ q)
    (preimageBaseChangeMap_comp_structure C f b jZ q)
    ((res_perfectChernClass_derivedPullback_of_eq C _ (preimageBaseChangeMap f b jZ q)
      (preimageBaseChangeMap_comp_structure C f b jZ q) _
      (hasDefinedChernClasses_derivedPullback _ (hasDefinedChernClasses_derivedPullback
        (preimageInclusion f b jZ) (hasDefinedChernClasses_restrictionAtInfinity f b hQ)))).trans
      (perfectChernClass_congr C _ _ _
        (nonempty_restriction_preimageBaseChangeMap_iso f b jZ q Q).some)) p v k α α' hα

/-- `P_p(Q'|_{E'})` operates as `P_p(Q|_E)` does through `E' ⟶ E`. -/
theorem idRule_powerSumOnPreimage_baseChange_heq
    (perfect : RingedSpace.IsPerfect.{u, u + 1} (X := W.toRingedSpace) Q) {U : Scheme.{u}}
    (v : U ⟶ pullback (modificationProjectionAtInfinity (q ≫ f) (baseChangedModification f b q))
      (pullback.snd jZ q)) [LocallyOfFiniteType v] (k : ℤ)
    (α : chowGroup C (v ≫ (preimageInclusion (q ≫ f) (baseChangedModification f b q)
      (pullback.snd jZ q) ≫ modificationProjectionAtInfinity (q ≫ f)
        (baseChangedModification f b q) ≫ q ≫ f)) k)
    (α' : chowGroup C ((v ≫ preimageBaseChangeMap f b jZ q) ≫
      (preimageInclusion f b jZ ≫ modificationProjectionAtInfinity f b ≫ f)) k) (hα : α ≍ α') :
    (powerSumOnPreimage C (q ≫ f) (baseChangedModification f b q) (pullback.snd jZ q)
        (hasDefinedChernClasses_derivedPullback (pullback.fst b (familyBaseChange f q)) hQ)
        p).idRule C _ (gysinSystemOfInvertible C) v k α ≍
      (powerSumOnPreimage C f b jZ hQ p).idRule C _ (gysinSystemOfInvertible C)
        (v ≫ preimageBaseChangeMap f b jZ q) k α' := by
  have perfE := RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
    (preimageInclusion f b jZ).toLRSHom.toShHom _ (isPerfect_restrictionAtInfinity C f b perfect)
  have hE := hasDefinedChernClasses_derivedPullback (preimageInclusion f b jZ)
    (hasDefinedChernClasses_restrictionAtInfinity f b hQ)
  have heq : powerSumOnPreimage C (q ≫ f) (baseChangedModification f b q) (pullback.snd jZ q)
      (hasDefinedChernClasses_derivedPullback (pullback.fst b (familyBaseChange f q)) hQ) p =
      perfectPowerSumComponent C (preimageInclusion (q ≫ f) (baseChangedModification f b q)
          (pullback.snd jZ q) ≫ modificationProjectionAtInfinity (q ≫ f)
            (baseChangedModification f b q) ≫ q ≫ f)
        (hasDefinedChernClasses_derivedPullback (preimageBaseChangeMap f b jZ q) hE) p :=
    (perfectPowerSumComponent_congr C _ _ _
      (nonempty_restriction_preimageBaseChangeMap_iso f b jZ q Q).some p).symm
  rw [heq]
  exact idRule_perfectPowerSumComponent_derivedPullback_heq C _ _ (preimageBaseChangeMap f b jZ q)
    (preimageBaseChangeMap_comp_structure C f b jZ q) perfE hE _ p v k α α' hα

/-- **Stacks 0GUI, for the Chern classes.** In the situation of Stacks 0F9K, with `Q|_T` finite
locally free of rank `< p` in degree `0`, let `q : X' ⟶ X` be a morphism locally of finite type.
Let `Z' = Z ×_X X'`, `b' : W' = W ×_{𝐏¹_X} 𝐏¹_{X'} ⟶ 𝐏¹_{X'}` and `T' = T ×_{W_∞} W'_∞ ⊆ W'_∞`
be the base changes of `Z`, `b` and `T`, and let `Q' = (W' ⟶ W)^*Q`. Then `b'`, `Q'` and `T'`
satisfy the assumptions of Stacks 0F9K, and the class `c'_p(Q') ∈ A^p(Z' ⟶ X')` constructed as in
Stacks 0F9K using `b'`, `Q'` and `T'` is the restriction (Remark 0F9Z) of
`c'_p(Q) ∈ A^p(Z ⟶ X)`.

The restriction is a class for `Z' ⟶ X'` whose source carries the structure morphism
`Z' ⟶ Z ⟶ S`, while the class constructed at `X'` carries `Z' ⟶ X' ⟶ S`; the two are equal, and
the restriction is read with the second one by `Stacks.Chow.bivariantTransport` along the
identity. -/
@[stacks 0GUI "the classes c'_p: c'_p(Q') built as in Stacks 0F9K from b', Q' and T' is the \
restriction of c'_p(Q)"]
theorem localizedChernClassAtInfinity_baseChange
    (hV : ∀ w, (modificationProjectionAtInfinity f b).base w ∉ Set.range jZ.base →
      w ∈ Set.range iV.base)
    (hres : RestrictionIsLocallyFreeOfRankLT f b iV Q p) :
    localizedChernClassAtInfinity C (haveI := hA; isIso_baseChangedModification_chart f b q)
        (pullback.snd jZ q)
        (hasDefinedChernClasses_derivedPullback (pullback.fst b (familyBaseChange f q)) hQ)
        (baseChange_mem_range f b jZ iV q hV)
        (restrictionIsLocallyFreeOfRankLT_baseChange f b iV q hres) =
      bivariantTransport C (gysinSystemOfInvertible C) (pullback.fst jZ q ≫ jZ ≫ f)
        (pullback.snd jZ q ≫ q ≫ f) (q ≫ f) (pullback.snd jZ q)
        (pullbackSnd_comp_structureMorphism_eq C (jZ ≫ f) f jZ rfl q) (pullback.snd jZ q) rfl
        (Iso.refl _) (Category.id_comp _) (p : ℤ)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (bivariantRestrictionOfInvertible C (jZ ≫ f) f jZ rfl q (p : ℤ)
          (localizedChernClassAtInfinity C hA jZ hQ hV hres)) := by
  have := hA
  refine eq_bivariantTransport_bivariantRestriction_of_cap C f b jZ q (p : ℤ)
    (localizedChernClassOnPreimage C jZ hQ hV hres)
    (localizedChernClassOnPreimage C (pullback.snd jZ q)
      (hasDefinedChernClasses_derivedPullback (pullback.fst b (familyBaseChange f q)) hQ)
      (baseChange_mem_range f b jZ iV q hV)
      (restrictionIsLocallyFreeOfRankLT_baseChange f b iV q hres))
    (fun g _ k y ↦ ?_) _ (fun t _ k α ↦ cap_localizedClassAtInfinity C f b hA jZ (p : ℤ) _ t k α)
    _ (fun t _ k α ↦ cap_localizedClassAtInfinity C (q ≫ f) (baseChangedModification f b q)
      (isIso_baseChangedModification_chart f b q) (pullback.snd jZ q) (p : ℤ) _ t k α)
  exact chowPush_closedCoverLocalizedClass_cap_baseChange C _ _ _ iV rfl _ rfl
    (range_union_range_preimageInclusion f b jZ iV hV) _
    (chowCohomologyRestriction_chernClassOnPreimage_eq_zero C jZ hQ hres) _ _ _
    (pullback.snd iV (baseChangedInfinityMap f b q)) rfl _ rfl
    (range_union_range_preimageInclusion _ _ _ _ (baseChange_mem_range f b jZ iV q hV)) _
    (chowCohomologyRestriction_chernClassOnPreimage_eq_zero C (pullback.snd jZ q) _
      (restrictionIsLocallyFreeOfRankLT_baseChange f b iV q hres))
    (baseChangedInfinityMap f b q) (baseChangedInfinityMap_comp_structure f b q f)
    (pullback.fst iV (baseChangedInfinityMap f b q)) pullback.condition
    (preimageBaseChangeMap f b jZ q) (preimageBaseChangeMap_fst f b jZ q) _ _ _
    (pullbackLiftOfIsPullback_fst _ g)
    (fun v _ k α α' hα ↦ idRule_chernClassOnPreimage_baseChange_heq C f b jZ q hQ p v k α α' hα)
    k y

/-- **Stacks 0GUI, for the classes `P_p`.** In the situation of Stacks 0F9K, with `Q|_T` zero,
let `q : X' ⟶ X` be a morphism locally of finite type. Let `Z' = Z ×_X X'`,
`b' : W' = W ×_{𝐏¹_X} 𝐏¹_{X'} ⟶ 𝐏¹_{X'}` and `T' = T ×_{W_∞} W'_∞ ⊆ W'_∞` be the base changes of
`Z`, `b` and `T`, and let `Q' = (W' ⟶ W)^*Q`. Then `b'`, `Q'` and `T'` satisfy the assumptions of
Stacks 0F9K, and the class `P'_p(Q') ∈ A^p(Z' ⟶ X')` constructed as in Stacks 0F9K using `b'`,
`Q'` and `T'` is the restriction (Remark 0F9Z) of `P'_p(Q) ∈ A^p(Z ⟶ X)`, read with the structure
morphism `Z' ⟶ X' ⟶ S` as in `localizedChernClassAtInfinity_baseChange`. -/
@[stacks 0GUI "the classes P'_p: P'_p(Q') built as in Stacks 0F9K from b', Q' and T' is the \
restriction of P'_p(Q)"]
theorem localizedPowerSumClassAtInfinity_baseChange
    (perfect : RingedSpace.IsPerfect.{u, u + 1} (X := W.toRingedSpace) Q)
    (hV : ∀ w, (modificationProjectionAtInfinity f b).base w ∉ Set.range jZ.base →
      w ∈ Set.range iV.base)
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      iV.toLRSHom.toShHom).obj (restrictionAtInfinity f b Q))) :
    localizedPowerSumClassAtInfinity C (haveI := hA; isIso_baseChangedModification_chart f b q)
        (pullback.snd jZ q)
        (hasDefinedChernClasses_derivedPullback (pullback.fst b (familyBaseChange f q)) hQ)
        (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ Q perfect)
        (baseChange_mem_range f b jZ iV q hV) (isZero_restriction_baseChange f b iV q hzero)
        (p := p) =
      bivariantTransport C (gysinSystemOfInvertible C) (pullback.fst jZ q ≫ jZ ≫ f)
        (pullback.snd jZ q ≫ q ≫ f) (q ≫ f) (pullback.snd jZ q)
        (pullbackSnd_comp_structureMorphism_eq C (jZ ≫ f) f jZ rfl q) (pullback.snd jZ q) rfl
        (Iso.refl _) (Category.id_comp _) (p : ℤ)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (bivariantRestrictionOfInvertible C (jZ ≫ f) f jZ rfl q (p : ℤ)
          (localizedPowerSumClassAtInfinity C hA jZ hQ perfect hV hzero (p := p))) := by
  have := hA
  refine eq_bivariantTransport_bivariantRestriction_of_cap C f b jZ q (p : ℤ)
    (localizedPowerSumOnPreimage C jZ hQ perfect hV hzero (p := p))
    (localizedPowerSumOnPreimage C (pullback.snd jZ q)
      (hasDefinedChernClasses_derivedPullback (pullback.fst b (familyBaseChange f q)) hQ)
      (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ Q perfect)
      (baseChange_mem_range f b jZ iV q hV) (isZero_restriction_baseChange f b iV q hzero)
      (p := p))
    (fun g _ k y ↦ ?_) _ (fun t _ k α ↦ cap_localizedClassAtInfinity C f b hA jZ (p : ℤ) _ t k α)
    _ (fun t _ k α ↦ cap_localizedClassAtInfinity C (q ≫ f) (baseChangedModification f b q)
      (isIso_baseChangedModification_chart f b q) (pullback.snd jZ q) (p : ℤ) _ t k α)
  exact chowPush_closedCoverLocalizedClass_cap_baseChange C _ _ _ iV rfl _ rfl
    (range_union_range_preimageInclusion f b jZ iV hV) _
    (chowCohomologyRestriction_powerSumOnPreimage_eq_zero C f b jZ iV hQ perfect p hzero) _ _ _
    (pullback.snd iV (baseChangedInfinityMap f b q)) rfl _ rfl
    (range_union_range_preimageInclusion _ _ _ _ (baseChange_mem_range f b jZ iV q hV)) _
    (chowCohomologyRestriction_powerSumOnPreimage_eq_zero C _ _ _ _ _
      (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
        (pullback.fst b (familyBaseChange f q)).toLRSHom.toShHom Q perfect) p
      (isZero_restriction_baseChange f b iV q hzero))
    (baseChangedInfinityMap f b q) (baseChangedInfinityMap_comp_structure f b q f)
    (pullback.fst iV (baseChangedInfinityMap f b q)) pullback.condition
    (preimageBaseChangeMap f b jZ q) (preimageBaseChangeMap_fst f b jZ q) _ _ _
    (pullbackLiftOfIsPullback_fst _ g)
    (fun v _ k α α' hα ↦
      idRule_powerSumOnPreimage_baseChange_heq C f b jZ q hQ p perfect v k α α' hα)
    k y

end Statement

end GysinAtInfinity

end Stacks.Chow

end
