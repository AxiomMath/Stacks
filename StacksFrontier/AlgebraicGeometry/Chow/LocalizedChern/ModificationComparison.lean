module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.Preparation
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinityComparison
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.GysinAtInfinityClassProperPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.SupportedIntersectionProduct

/-!
# Comparing the localized classes of two modifications

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project. For `i = 1, 2` let
`b_i : W_i ⟶ 𝐏¹_{X_i}` be proper and an isomorphism over `𝐀¹_{X_i}`, let `Z_i ⊆ X_i` and
`T_i ⊆ W_{i,∞}` be closed with `W_{i,∞} = T_i ∪ E_i` for `E_i = W_{i,∞} ×_{X_i} Z_i`, and let
`q_i ∈ A^p(W_i)` vanish over `T_i`. Stacks 0F9K attaches to these data the localized class

  `q_i' = (E_i ⟶ Z_i)_* ∘ (q_i|_{E_i})' ∘ C_i ∈ A^p(Z_i ⟶ X_i)`

(`Stacks.Chow.localizedModificationClass`), where `C_i` is the class of Stacks 0F9J. This file
compares two such classes on a test scheme `V`, given a morphism `W₁ ⟶ W₂` along which `q₁` is the
restriction of `q₂`, compatible morphisms of the fibres at infinity, of the `E_i` and of the
`T_i`, and a proper morphism `φ : W₁ ×_{X₁} V ⟶ W₂ ×_{X₂} V` over `V` and over `𝐏¹_S`:

* the class at infinity satisfies `C₂ ∩ α = φ_{∞,*}(C₁ ∩ α)` (Stacks 0FAQ and 0GUH, in the form
  of `Stacks.Chow.gysinCapOfLift_comparison`);
* the extension `(q₂|_{E₂})'` caps along `W_{1,∞} ⟶ W_{2,∞}` as `(q₁|_{E₁})'` does, pushed forward
  along `E₁ ⟶ E₂`: on the members of the closed cover `W_{1,∞} = T₁ ∪ E₁` both sides vanish,
  resp. are the operation of `q₂` (Stacks 0F9H and 0B7F);
* hence `ψ_*(q₁' ∩ α) = q₂' ∩ α` for the induced `ψ : Z₁ ×_{X₁} V ⟶ Z₂ ×_{X₂} V`.

The case `X₁ = X₂`, `W₁ = W'` with `g : W' ⟶ W` proper and an isomorphism over `𝐀¹_X`, and
`φ = g ×_X V` is the second assertion of Stacks 0FAU; the case of a base change `X' ⟶ X` is
Stacks 0GUI and is in `StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.ModificationBaseChange`.

## Main results

* `Stacks.Chow.localizedModificationClass_cap_heq` — the cap operation of the localized class:
  `q' ∩ α` is the pushforward along `E ×_{W_∞} (W_∞ ×_X V) ⟶ Z ×_X V` of `(q|_E)' ∩ (C ∩ α)`.
* `Stacks.Chow.modificationExtension_cap_comparison` — the extension of a restriction is the
  restriction of the extension, on cap operations.
* `Stacks.Chow.localizedModificationClass_cap_comparison` — `ψ_*(q₁' ∩ α) = q₂' ∩ α`.
* `Stacks.Chow.localizedModificationClass_eq_of_modification` — the generic form of the second
  assertion of Stacks 0FAU, for every class `q`.
* `Stacks.Chow.modificationPowerSum_eq_of_modification`,
  `Stacks.Chow.modificationChernClass_eq_of_modification` — **the second assertion of
  Stacks 0FAU**: `P'_p(g^*Q) = P'_p(Q)` and `c'_p(g^*Q) = c'_p(Q)`.

## Implementation notes

The relation between `q₁` and `q₂` is taken as a hypothesis on their operations on the test
schemes over `W₁`, so that it covers `q₁ = g^* q₂` for any spelling of the structure morphism of
`W₁`; the classes `P_p(g^*Q)` and `c_p(g^*Q)` satisfy it by
`Stacks.Chow.res_perfectPowerSum_derivedPullback` and
`Stacks.Chow.res_perfectChernClass_derivedPullback_of_comp_eq`. In the second assertion of
Stacks 0FAU the closed subscheme `T' ⊆ W'_∞` is arbitrary among those with the properties of
Stacks 0F9K: by the first assertion of Stacks 0FAU
(`Stacks.Chow.localizedModificationClass_eq`) it may be replaced by
`g_∞^{-1}(T)`, which is what the source uses. The hypothesis that `g` is an isomorphism over
`𝐀¹_X` enters only through `b ∘ g` being one, which is what the statements assume.

## References

* [Stacks Project, Tag 0FAU](https://stacks.math.columbia.edu/tag/0FAU)
* [Stacks Project, Tag 0F9K](https://stacks.math.columbia.edu/tag/0F9K)
* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 0FAQ](https://stacks.math.columbia.edu/tag/0FAQ)
* [Stacks Project, Tag 0GUH](https://stacks.math.columbia.edu/tag/0GUH)
* [Stacks Project, Tag 0F9H](https://stacks.math.columbia.edu/tag/0F9H)
* [Stacks Project, Tag 0B7F](https://stacks.math.columbia.edu/tag/0B7F)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The cap operation of the localized class -/

section CapFormula

variable {C : ChowSituation.{u}}

/-- Pushed forward along a proper morphism, the cap product of a class read for an equal morphism
and an equal degree (`Stacks.Chow.BivariantClass.copy`) is that of the class, pushed forward along
the corresponding morphism out of the other fibre product. -/
theorem chowPush_copy_cap_heq {A B Y : Scheme.{u}} {sA : A ⟶ C.S} [LocallyOfFiniteType sA]
    {sB : B ⟶ C.S} [LocallyOfFiniteType sB] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]
    {G : GysinSystem C} {F F' : A ⟶ Y} [LocallyOfFiniteType F] [LocallyOfFiniteType F']
    (hFF' : F = F') (hF : F ≫ sY = sA) (hF' : F' ≫ sY = sA) {p p' : ℤ} (hpp' : p = p')
    (c : BivariantClass C G sA sY F hF p) {V : Scheme.{u}} (g : V ⟶ Y) [LocallyOfFiniteType g]
    (φ : pullback F' g ⟶ B) [IsProper φ] (hφ : φ ≫ sB = pullback.fst F' g ≫ sA)
    (ψ : pullback F g ⟶ B) [IsProper ψ] (hψ : ψ ≫ sB = pullback.fst F g ≫ sA)
    (hφψ : (pullback.congrHom hFF' rfl).hom ≫ φ = ψ) (k : ℤ) (α : chowGroup C (g ≫ sY) k) :
    chowPush C _ sB φ hφ (k - p') ((BivariantClass.copy C G sA sY hFF' hF hF' hpp' c).cap g k α) ≍
      chowPush C _ sB ψ hψ (k - p) (c.cap g k α) := by
  subst hFF' hpp'
  have hid : (pullback.congrHom (rfl : F = F) (rfl : g = g)).hom = 𝟙 _ := by
    apply pullback.hom_ext <;> simp
  rw [hid, Category.id_comp] at hφψ
  subst hφψ
  rfl

/-- For `π : I ⟶ X`, `z : Z ⟶ X` and `g : V ⟶ X`, the morphism
`(I ×_X Z) ×_I (I ×_X V) ⟶ Z ×_X V` induced by the two projections. -/
def exceptionalBaseChangeMap {I X Z V : Scheme.{u}} (π : I ⟶ X) (z : Z ⟶ X) (g : V ⟶ X) :
    pullback (pullback.fst π z) (pullback.fst π g) ⟶ pullback z g :=
  pullback.lift (pullback.fst _ _ ≫ pullback.snd π z) (pullback.snd _ _ ≫ pullback.snd π g) (by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, pullback.condition,
      Category.assoc, pullback.condition, Category.assoc])

/-- The first projection of `exceptionalBaseChangeMap π z g` is the first projection followed by
`pullback.snd π z`. -/
@[reassoc (attr := simp)]
theorem exceptionalBaseChangeMap_fst {I X Z V : Scheme.{u}} (π : I ⟶ X) (z : Z ⟶ X)
    (g : V ⟶ X) :
    exceptionalBaseChangeMap π z g ≫ pullback.fst z g =
      pullback.fst _ _ ≫ pullback.snd π z :=
  pullback.lift_fst _ _ _

/-- The second projection of `exceptionalBaseChangeMap π z g` is the second projection followed
by `pullback.snd π g`. -/
@[reassoc (attr := simp)]
theorem exceptionalBaseChangeMap_snd {I X Z V : Scheme.{u}} (π : I ⟶ X) (z : Z ⟶ X)
    (g : V ⟶ X) :
    exceptionalBaseChangeMap π z g ≫ pullback.snd z g =
      pullback.snd _ _ ≫ pullback.snd π g :=
  pullback.lift_snd _ _ _

/-- The morphism `(I ×_X Z) ×_I (I ×_X V) ⟶ Z ×_X V` lies over the base. -/
theorem exceptionalBaseChangeMap_comp_structure {S I X Z V : Scheme.{u}} (π : I ⟶ X) (z : Z ⟶ X)
    (g : V ⟶ X) (s : X ⟶ S) :
    exceptionalBaseChangeMap π z g ≫ (pullback.fst z g ≫ (z ≫ s)) =
      pullback.fst (pullback.fst π z) (pullback.fst π g) ≫ (pullback.fst π z ≫ π ≫ s) := by
  rw [exceptionalBaseChangeMap_fst_assoc, pullback.condition_assoc (f := π) (g := z)]

/-- The morphism `(I ×_X Z) ×_I (I ×_X V) ⟶ Z ×_X V` is proper when `π` is proper and `z` is a
closed immersion. -/
instance isProper_exceptionalBaseChangeMap {I X Z V : Scheme.{u}} (π : I ⟶ X) [IsProper π]
    (z : Z ⟶ X) [IsClosedImmersion z] (g : V ⟶ X) :
    IsProper (exceptionalBaseChangeMap π z g) := by
  have : IsProper (exceptionalBaseChangeMap π z g ≫ pullback.snd z g) := by
    rw [exceptionalBaseChangeMap_snd]
    infer_instance
  exact IsProper.of_comp _ (pullback.snd z g)

/-- The operation of a Chow cohomology class on two equal test morphisms agrees, up to the
transports between their Chow groups. -/
theorem BivariantClass.idRule_heq_congr {G : GysinSystem C} {Z : Scheme.{u}} {sZ : Z ⟶ C.S}
    [LocallyOfFiniteType sZ] {p : ℤ} (a : chowCohomologyComponent C G sZ p) {T : Scheme.{u}}
    {n n' : T ⟶ Z} [LocallyOfFiniteType n] [LocallyOfFiniteType n'] (h : n = n') (k : ℤ)
    (α : chowGroup C (n ≫ sZ) k) (α' : chowGroup C (n' ≫ sZ) k) (hα : α ≍ α') :
    a.idRule C sZ G n k α ≍ a.idRule C sZ G n' k α' := by
  subst h
  cases eq_of_heq hα
  rfl

/-- A class `a ∈ A^p(Z)` vanishes over `z : W ⟶ Z` as soon as its operation on every test scheme
factoring through `z` vanishes. -/
theorem BivariantClass.VanishesOver.of_idRule_eq_zero {G : GysinSystem C} {Z W : Scheme.{u}}
    {sZ : Z ⟶ C.S} [LocallyOfFiniteType sZ] {p : ℤ} {a : chowCohomologyComponent C G sZ p}
    {z : W ⟶ Z} [LocallyOfFiniteType z]
    (h : ∀ {T : Scheme.{u}} (t : T ⟶ W) [LocallyOfFiniteType t] (k : ℤ)
      (x : chowGroup C ((t ≫ z) ≫ sZ) k), a.idRule C sZ G (t ≫ z) k x = 0) :
    BivariantClass.VanishesOver a z := fun t _ k α ↦
  chowPushforwardOfIso_injective C _ _ _ _ (k - p) ((h t k α).trans (map_zero _).symm)

/-- A Chow class heterogeneously equal to the zero class of the Chow group of an equal structure
morphism is zero. -/
theorem chowGroup_eq_zero_of_heq_zero_of_base_eq {X : Scheme.{u}} {s s' : X ⟶ C.S}
    [LocallyOfFiniteType s] [LocallyOfFiniteType s'] (h : s = s') {k : ℤ} {x : chowGroup C s k}
    (hx : x ≍ (0 : chowGroup C s' k)) : x = 0 := by
  subst h
  exact eq_of_heq hx

/-- The operation of a component of the restriction of a total class along `h : Y' ⟶ Y` on a
test scheme `y : T ⟶ Y'` is the operation of the component on `y ≫ h`. -/
theorem TotalChowClass.idRule_res_apply_heq {Y Y' : Scheme.{u}} {sY : Y ⟶ C.S}
    [LocallyOfFiniteType sY] {sY' : Y' ⟶ C.S} [LocallyOfFiniteType sY'] (h : Y' ⟶ Y)
    [LocallyOfFiniteType h] (hs : h ≫ sY = sY') (c : TotalChowClass C sY) (p : ℕ)
    {T : Scheme.{u}} (y : T ⟶ Y') [LocallyOfFiniteType y] [LocallyOfFiniteType (y ≫ h)] (k : ℤ)
    (γ : chowGroup C (y ≫ sY') k) (γ' : chowGroup C ((y ≫ h) ≫ sY) k) (hγ : γ ≍ γ') :
    (TotalChowClass.res h hs c p).idRule C sY' (gysinSystemOfInvertible C) y k γ ≍
      (c p).idRule C sY (gysinSystemOfInvertible C) (y ≫ h) k γ' := by
  subst hs
  rw [TotalChowClass.res_apply_eq_bivariantClassCongrBase,
    BivariantClass.idRule_bivariantClassCongrBase]
  refine (chowGroupCongr_heq C _ _ _).trans ?_
  exact BivariantClass.idRule_chowCohomologyRestriction_heq h (c p) y k _ γ'
    ((chowGroupCongr_heq C _ _ _).trans hγ)

/-- A morphism `Z₁ ×_{X₁} V ⟶ Z₂ ×_{X₂} V` over `V`, for test schemes `V ⟶ X_i` over the same
morphism to the base, lies over the base. -/
theorem pullbackFst_comp_structure_of_comp_snd {S X₁ X₂ Z₁ Z₂ V : Scheme.{u}} {f₁ : X₁ ⟶ S}
    {f₂ : X₂ ⟶ S} (z₁ : Z₁ ⟶ X₁) (z₂ : Z₂ ⟶ X₂) {g₁ : V ⟶ X₁} {g₂ : V ⟶ X₂}
    (hT : g₁ ≫ f₁ = g₂ ≫ f₂) (ψ : pullback z₁ g₁ ⟶ pullback z₂ g₂)
    (hψ : ψ ≫ pullback.snd z₂ g₂ = pullback.snd z₁ g₁) :
    ψ ≫ (pullback.fst z₂ g₂ ≫ (z₂ ≫ f₂)) = pullback.fst z₁ g₁ ≫ (z₁ ≫ f₁) := by
  rw [pullback.condition_assoc, reassoc_of% hψ, ← hT, ← pullback.condition_assoc]

end CapFormula

section LocalizedCap

variable {C : ChowSituation.{u}} {X W Z T : Scheme.{u}} {f : X ⟶ C.S} [LocallyOfFiniteType f]
  {b : W ⟶ projectiveLineProduct f} [IsProper b]
  {hA : IsIso (pullback.snd b (projectiveLineAffineChart f))}
  (D : GysinAtInfinityData C (gysinSystemOfInvertible C) f b hA)
  (z : Z ⟶ X) [IsClosedImmersion z] (t : T ⟶ modificationFibreAtInfinity f b)
  [IsClosedImmersion t] {p : ℤ}
  {q : chowCohomologyComponent C (gysinSystemOfInvertible C) (modificationProjection f b ≫ f) p}

/-- **The cap operation of the localized class.** On a test scheme `g : V ⟶ X`, the cap product
of `q' = (E ⟶ Z)_* ∘ (q|_E)' ∘ C` is the pushforward along `E ×_{W_∞} (W_∞ ×_X V) ⟶ Z ×_X V` of
`(q|_E)' ∩ (C ∩ α)`. The two sides lie in the degrees `k - p` and `(k - 0) - p`. -/
theorem localizedModificationClass_cap_heq
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (hq : BivariantClass.VanishesOver q (t ≫ modificationInclusionAtInfinity f b))
    {V : Scheme.{u}} (g : V ⟶ X) [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ f) k) :
    (localizedModificationClass D z t hT hq).cap g k α ≍
      chowPush C (pullback.fst (pullback.fst (modificationProjectionAtInfinity f b) z)
          (pullback.fst (modificationProjectionAtInfinity f b) g) ≫
            (pullback.fst (modificationProjectionAtInfinity f b) z ≫
              modificationProjectionAtInfinity f b ≫ f))
        (pullback.fst z g ≫ (z ≫ f))
        (exceptionalBaseChangeMap (modificationProjectionAtInfinity f b) z g)
        (exceptionalBaseChangeMap_comp_structure _ z g f)
        ((k - 0) - p)
        ((modificationExtension z t hT hq).cap
          (pullback.fst (modificationProjectionAtInfinity f b) g) (k - 0)
          (D.bivariantClass.cap g k α)) := by
  set π := modificationProjectionAtInfinity f b
  set ψ := (pullbackRightPullbackFstIso π g (pullback.fst π z)).inv ≫
    exceptionalBaseChangeMap π z g with hψdef
  have hψ : ψ ≫ (pullback.fst z g ≫ (z ≫ f)) =
      pullback.fst (pullback.fst π z ≫ π) g ≫ (pullback.fst π z ≫ π ≫ f) := by
    rw [hψdef, Category.assoc, exceptionalBaseChangeMap_comp_structure,
      pullbackRightPullbackFstIso_inv_fst_assoc]
  have hφψ : (pullback.congrHom (pullback.condition (f := π) (g := z)) rfl).hom ≫
      bivariantPushforwardBaseChange (pullback.snd π z) z g = ψ := by
    apply pullback.hom_ext <;> simp [ψ, bivariantPushforwardBaseChange]
  unfold localizedModificationClass
  rw [bivariantProperPushforwardOfInvertible_cap, bivariantProperPushforwardCap_apply]
  refine (chowPush_copy_cap_heq pullback.condition _ _ (add_zero p) _ g
    (bivariantPushforwardBaseChange (pullback.snd π z) z g) _ ψ hψ hφψ k α).trans ?_
  have hc := isBivariantClassComposition_bivariantCompositeOfInvertible C _ _ f
    (pullback.fst π z) π rfl rfl p 0 (modificationExtension z t hT hq) D.bivariantClass g k α
  refine (heq_map_index (by ring : k - (p + 0) = (k - 0) - p) hc fun n x ↦
    chowPush C _ (pullback.fst z g ≫ (z ≫ f)) ψ hψ n x).trans (heq_of_eq ?_)
  rw [bivariantCompositeCap_apply]
  exact chowPush_comp C _ _ _ _ _ _ (by simp [ψ]; rfl) _ _ _ _ _

/-- The cap operation of `(q|_E)'` is the cap operation of the extension along the closed cover
`W_∞ = T ∪ E`. -/
theorem modificationExtension_cap
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (hq : BivariantClass.VanishesOver q (t ≫ modificationInclusionAtInfinity f b))
    {Y : Scheme.{u}} (y : Y ⟶ modificationFibreAtInfinity f b) [LocallyOfFiniteType y] (k : ℤ) :
    (modificationExtension z t hT hq).cap y k =
      closedCoverExtensionCap C (gysinSystemOfInvertible C)
        (modificationProjectionAtInfinity f b ≫ f) t
        (pullback.fst (modificationProjectionAtInfinity f b) z) _ rfl
        (range_union_range_pullbackFst_eq_univ z t hT)
        (BivariantClass.VanishesOver.chowCohomologyRestriction_snd C _ t _
          (hq.chowCohomologyRestriction_modificationInclusionAtInfinity t)) y k :=
  rfl

/-- `(q|_E)'` caps a class pushed forward from `E ×_{W_∞} Y` as `q|_E` does. -/
theorem modificationExtension_cap_second
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (hq : BivariantClass.VanishesOver q (t ≫ modificationInclusionAtInfinity f b))
    {Y : Scheme.{u}} (y : Y ⟶ modificationFibreAtInfinity f b) [LocallyOfFiniteType y] (k : ℤ)
    (α : chowGroup C (pullback.fst (pullback.fst (modificationProjectionAtInfinity f b) z) y ≫
      (pullback.fst (modificationProjectionAtInfinity f b) z ≫
        modificationProjectionAtInfinity f b ≫ f)) k) :
    (modificationExtension z t hT hq).cap y k
        (chowPush C _ _ (pullback.snd _ y) (pullbackSnd_comp_structureMorphism rfl y) k α) =
      (Stacks.Chow.chowCohomologyRestriction C (gysinSystemOfInvertible C)
        (modificationProjectionAtInfinity f b ≫ f)
        (pullback.fst (modificationProjectionAtInfinity f b) z) p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (Stacks.Chow.chowCohomologyRestriction C (gysinSystemOfInvertible C)
          (modificationProjection f b ≫ f) (modificationInclusionAtInfinity f b) p
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) q)).idRule C _
        (gysinSystemOfInvertible C) (pullback.fst _ y) k α :=
  closedCoverExtension_cap_second C _ t _ _ rfl _
    (BivariantClass.VanishesOver.chowCohomologyRestriction_snd C _ t _
      (hq.chowCohomologyRestriction_modificationInclusionAtInfinity t)) y k α

/-- `(q|_E)'` kills the classes pushed forward from `T ×_{W_∞} Y`. -/
theorem modificationExtension_cap_first
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (hq : BivariantClass.VanishesOver q (t ≫ modificationInclusionAtInfinity f b))
    {Y : Scheme.{u}} (y : Y ⟶ modificationFibreAtInfinity f b) [LocallyOfFiniteType y] (k : ℤ)
    (α : chowGroup C (pullback.fst t y ≫ (t ≫ modificationProjectionAtInfinity f b ≫ f)) k) :
    (modificationExtension z t hT hq).cap y k
        (chowPush C _ _ (pullback.snd t y) (pullbackSnd_comp_structureMorphism rfl y) k α) = 0 :=
  closedCoverExtension_cap_first C _ t _ _ rfl _
    (BivariantClass.VanishesOver.chowCohomologyRestriction_snd C _ t _
      (hq.chowCohomologyRestriction_modificationInclusionAtInfinity t)) y k α

/-- The operation of the restriction `q|_E` of `q ∈ A^p(W)` to `E = W_∞ ×_X Z` on a test scheme
`n : Y ⟶ E` is the operation of `q` on `Y ⟶ E ⟶ W_∞ ⟶ W`. -/
theorem modificationRestriction_idRule_heq
    (q : chowCohomologyComponent C (gysinSystemOfInvertible C) (modificationProjection f b ≫ f) p)
    {Y : Scheme.{u}} (n : Y ⟶ pullback (modificationProjectionAtInfinity f b) z)
    [LocallyOfFiniteType n] (k : ℤ)
    (α : chowGroup C (n ≫ (pullback.fst (modificationProjectionAtInfinity f b) z ≫
      modificationProjectionAtInfinity f b ≫ f)) k)
    (α' : chowGroup C (((n ≫ pullback.fst (modificationProjectionAtInfinity f b) z) ≫
      modificationInclusionAtInfinity f b) ≫ (modificationProjection f b ≫ f)) k) (hα : α ≍ α') :
    (Stacks.Chow.chowCohomologyRestriction C (gysinSystemOfInvertible C)
        (modificationProjectionAtInfinity f b ≫ f)
        (pullback.fst (modificationProjectionAtInfinity f b) z) p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (Stacks.Chow.chowCohomologyRestriction C (gysinSystemOfInvertible C)
          (modificationProjection f b ≫ f) (modificationInclusionAtInfinity f b) p
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) q)).idRule C _
        (gysinSystemOfInvertible C) n k α ≍
      q.idRule C _ (gysinSystemOfInvertible C)
        ((n ≫ pullback.fst (modificationProjectionAtInfinity f b) z) ≫
          modificationInclusionAtInfinity f b) k α' := by
  refine (BivariantClass.idRule_chowCohomologyRestriction_heq
    (sY := modificationProjectionAtInfinity f b ≫ f)
    (pullback.fst (modificationProjectionAtInfinity f b) z)
    (Stacks.Chow.chowCohomologyRestriction C (gysinSystemOfInvertible C)
      (modificationProjection f b ≫ f) (modificationInclusionAtInfinity f b) p
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) q) n k α
    (chowGroupCongr C (Category.assoc _ _ _).symm k α) (chowGroupCongr_heq C _ _ _).symm).trans ?_
  exact BivariantClass.idRule_chowCohomologyRestriction_heq (sY := modificationProjection f b ≫ f)
    (modificationInclusionAtInfinity f b) q _ k _ _
    ((chowGroupCongr_heq C _ _ _).trans hα)

end LocalizedCap

/-! ### Comparing the extensions of two restrictions -/

section ExtensionComparison

variable {C : ChowSituation.{u}}

/-- `Stacks.Chow.closedCoverExtensionCap_chowPush_second` for a pushforward from an arbitrary
structure morphism of the source, equal to the one through the second member of the cover. -/
theorem closedCoverExtensionCap_chowPush_second_of_eq {X X₁ X₂ : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (i₁ : X₁ ⟶ X) (i₂ : X₂ ⟶ X) [IsClosedImmersion i₁]
    [IsClosedImmersion i₂] (sX₂ : X₂ ⟶ C.S) [LocallyOfFiniteType sX₂] (hi₂ : i₂ ≫ sX = sX₂)
    {p : ℤ} {a : chowCohomologyComponent C (gysinSystemOfInvertible C) sX₂ p}
    (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)
    (ha : BivariantClass.VanishesOver a (pullback.snd i₁ i₂)) {T T₀ : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (e : T₀ ⟶ T) [IsProper e] (sT₀ : T₀ ⟶ C.S) [LocallyOfFiniteType sT₀]
    (hse : e ≫ (g ≫ sX) = sT₀) (m : T₀ ⟶ X₂) [LocallyOfFiniteType m] (hm : m ≫ i₂ = e ≫ g)
    (hms : m ≫ sX₂ = sT₀) (k : ℤ) (γ : chowGroup C sT₀ k) :
    closedCoverExtensionCap C (gysinSystemOfInvertible C) sX i₁ i₂ sX₂ hi₂ hcover ha g k
        (chowPush C sT₀ (g ≫ sX) e hse k γ) =
      chowPush C sT₀ (pullback.fst i₂ g ≫ sX₂) (pullback.lift m e hm)
        (by rw [← hms, ← Category.assoc, pullback.lift_fst]) (k - p)
        (chowGroupCongr C hms (k - p) (a.idRule C sX₂ (gysinSystemOfInvertible C) m k
          (chowGroupCongr C hms.symm k γ))) := by
  subst hms
  exact closedCoverExtensionCap_chowPush_second C _ sX i₁ i₂ sX₂ hi₂ hcover ha g e m hm k γ

/-- `Stacks.Chow.closedCoverExtensionCap_chowPush_first` for a pushforward from an arbitrary
structure morphism of the source. -/
theorem closedCoverExtensionCap_chowPush_first_of_eq {X X₁ X₂ : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (i₁ : X₁ ⟶ X) (i₂ : X₂ ⟶ X) [IsClosedImmersion i₁]
    [IsClosedImmersion i₂] (sX₂ : X₂ ⟶ C.S) [LocallyOfFiniteType sX₂] (hi₂ : i₂ ≫ sX = sX₂)
    {p : ℤ} {a : chowCohomologyComponent C (gysinSystemOfInvertible C) sX₂ p}
    (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)
    (ha : BivariantClass.VanishesOver a (pullback.snd i₁ i₂)) {T T₀ : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (e : T₀ ⟶ T) [IsProper e] (sT₀ : T₀ ⟶ C.S) [LocallyOfFiniteType sT₀]
    (hse : e ≫ (g ≫ sX) = sT₀) (m : T₀ ⟶ X₁) [LocallyOfFiniteType m] (hm : m ≫ i₁ = e ≫ g)
    (k : ℤ) (γ : chowGroup C sT₀ k) :
    closedCoverExtensionCap C (gysinSystemOfInvertible C) sX i₁ i₂ sX₂ hi₂ hcover ha g k
        (chowPush C sT₀ (g ≫ sX) e hse k γ) = 0 := by
  have hms : m ≫ (i₁ ≫ sX) = sT₀ := by rw [← hse, ← Category.assoc, hm, Category.assoc]
  subst hms
  exact closedCoverExtensionCap_chowPush_first C _ sX i₁ i₂ sX₂ hi₂ hcover ha g e m hm k γ

variable {X₁ X₂ W₁ W₂ Z₁ Z₂ T₁ T₂ : Scheme.{u}}
  {f₁ : X₁ ⟶ C.S} [LocallyOfFiniteType f₁] {f₂ : X₂ ⟶ C.S} [LocallyOfFiniteType f₂]
  {b₁ : W₁ ⟶ projectiveLineProduct f₁} [IsProper b₁]
  {b₂ : W₂ ⟶ projectiveLineProduct f₂} [IsProper b₂]
  {z₁ : Z₁ ⟶ X₁} [IsClosedImmersion z₁] {z₂ : Z₂ ⟶ X₂} [IsClosedImmersion z₂]
  {t₁ : T₁ ⟶ modificationFibreAtInfinity f₁ b₁} [IsClosedImmersion t₁]
  {t₂ : T₂ ⟶ modificationFibreAtInfinity f₂ b₂} [IsClosedImmersion t₂] {p : ℤ}
  {q₁ : chowCohomologyComponent C (gysinSystemOfInvertible C)
    (modificationProjection f₁ b₁ ≫ f₁) p}
  {q₂ : chowCohomologyComponent C (gysinSystemOfInvertible C)
    (modificationProjection f₂ b₂ ≫ f₂) p}
  {κW : W₁ ⟶ W₂} [LocallyOfFiniteType κW]
  {κ : modificationFibreAtInfinity f₁ b₁ ⟶ modificationFibreAtInfinity f₂ b₂}
  {eκ : pullback (modificationProjectionAtInfinity f₁ b₁) z₁ ⟶
    pullback (modificationProjectionAtInfinity f₂ b₂) z₂} [LocallyOfFiniteType eκ]
  {lT : T₁ ⟶ T₂} [LocallyOfFiniteType lT]

omit [LocallyOfFiniteType f₁] [LocallyOfFiniteType f₂] [IsProper b₁] [IsProper b₂]
  [LocallyOfFiniteType κW] in
include κW in
/-- A morphism of fibres at infinity compatible with a morphism of the modifications over the
base is a morphism over the base. -/
theorem comp_modificationProjectionAtInfinity_comp_eq
    (hκW : κ ≫ modificationInclusionAtInfinity f₂ b₂ = modificationInclusionAtInfinity f₁ b₁ ≫ κW)
    (hκf : κW ≫ (modificationProjection f₂ b₂ ≫ f₂) = modificationProjection f₁ b₁ ≫ f₁) :
    κ ≫ (modificationProjectionAtInfinity f₂ b₂ ≫ f₂) =
      modificationProjectionAtInfinity f₁ b₁ ≫ f₁ := by
  have h : modificationProjectionAtInfinity f₂ b₂ ≫ f₂ =
      modificationInclusionAtInfinity f₂ b₂ ≫ (modificationProjection f₂ b₂ ≫ f₂) :=
    Category.assoc _ _ _
  rw [h, ← Category.assoc, hκW, Category.assoc, hκf]
  exact (Category.assoc _ _ _).symm

omit [LocallyOfFiniteType f₁] [LocallyOfFiniteType f₂] [IsProper b₁] [IsProper b₂]
  [LocallyOfFiniteType κW] in
include κW in
/-- A test scheme over `W'_∞`, read over `W_∞` through `κ`, has the same structure morphism. -/
theorem comp_comp_modificationProjectionAtInfinity_comp_eq
    (hκW : κ ≫ modificationInclusionAtInfinity f₂ b₂ = modificationInclusionAtInfinity f₁ b₁ ≫ κW)
    (hκf : κW ≫ (modificationProjection f₂ b₂ ≫ f₂) = modificationProjection f₁ b₁ ≫ f₁)
    {Y : Scheme.{u}} (y : Y ⟶ modificationFibreAtInfinity f₁ b₁) :
    y ≫ (modificationProjectionAtInfinity f₁ b₁ ≫ f₁) =
      (y ≫ κ) ≫ (modificationProjectionAtInfinity f₂ b₂ ≫ f₂) := by
  rw [Category.assoc]
  exact (congrArg (y ≫ ·) (comp_modificationProjectionAtInfinity_comp_eq hκW hκf)).symm

/-- The morphism `E' ×_{W'_∞} Y ⟶ E ×_{W_∞} Y` induced by a morphism `E' ⟶ E` over
`κ : W'_∞ ⟶ W_∞` is proper when `E' ⟶ W'_∞` is proper and `E ⟶ W_∞` is separated. -/
instance isProper_pullbackMap_id {E₁ E₂ I₁ I₂ Y : Scheme.{u}} (e₁ : E₁ ⟶ I₁) [IsProper e₁]
    (e₂ : E₂ ⟶ I₂) [IsSeparated e₂] (y : Y ⟶ I₁) (y' : Y ⟶ I₂) (eκ : E₁ ⟶ E₂) (κ : I₁ ⟶ I₂)
    (h₁ : e₁ ≫ κ = eκ ≫ e₂) (h₂ : y ≫ κ = 𝟙 Y ≫ y') :
    IsProper (pullback.map e₁ y e₂ y' eκ (𝟙 Y) κ h₁ h₂) := by
  have : IsProper (pullback.map e₁ y e₂ y' eκ (𝟙 Y) κ h₁ h₂ ≫ pullback.snd e₂ y') := by
    rw [pullback.lift_snd, Category.comp_id]
    infer_instance
  exact IsProper.of_comp _ (pullback.snd e₂ y')

omit [LocallyOfFiniteType f₁] [LocallyOfFiniteType f₂] [IsProper b₁] [IsProper b₂]
  [LocallyOfFiniteType κW] [IsClosedImmersion z₁] [IsClosedImmersion z₂]
  [LocallyOfFiniteType eκ] in
/-- The morphism `E' ×_{W'_∞} Y ⟶ E ×_{W_∞} Y` lies over the base. -/
theorem pullbackMap_exceptional_comp_structure
    (hκW : κ ≫ modificationInclusionAtInfinity f₂ b₂ = modificationInclusionAtInfinity f₁ b₁ ≫ κW)
    (hκf : κW ≫ (modificationProjection f₂ b₂ ≫ f₂) = modificationProjection f₁ b₁ ≫ f₁)
    (heκ : eκ ≫ pullback.fst (modificationProjectionAtInfinity f₂ b₂) z₂ =
      pullback.fst (modificationProjectionAtInfinity f₁ b₁) z₁ ≫ κ)
    {Y : Scheme.{u}} (y : Y ⟶ modificationFibreAtInfinity f₁ b₁)
    (y₂ : Y ⟶ modificationFibreAtInfinity f₂ b₂) (hy : y ≫ κ = y₂) :
    pullback.map _ y _ y₂ eκ (𝟙 Y) κ heκ.symm (by rw [Category.id_comp, hy]) ≫
        (pullback.fst (pullback.fst (modificationProjectionAtInfinity f₂ b₂) z₂) y₂ ≫
          (pullback.fst (modificationProjectionAtInfinity f₂ b₂) z₂ ≫
            modificationProjectionAtInfinity f₂ b₂ ≫ f₂)) =
      pullback.fst (pullback.fst (modificationProjectionAtInfinity f₁ b₁) z₁) y ≫
        (pullback.fst (modificationProjectionAtInfinity f₁ b₁) z₁ ≫
          modificationProjectionAtInfinity f₁ b₁ ≫ f₁) := by
  rw [pullback.lift_fst_assoc, Category.assoc, reassoc_of% heκ,
    comp_modificationProjectionAtInfinity_comp_eq hκW hκf]

/-- **The extension of a restriction is the restriction of the extension, on cap operations.**
Let `κ : W'_∞ ⟶ W_∞` be compatible with a morphism `W' ⟶ W` over the base, let `E' ⟶ E` be a
morphism over `κ` of the inverse images of `Z' ⊆ X'` and `Z ⊆ X`, and let `T' ⟶ T` be a morphism
over `κ` of the closed subschemes of the fibres at infinity. If `q' ∈ A^p(W')` operates on every
test scheme over `W'` as `q ∈ A^p(W)` does, then on every test scheme `y : Y ⟶ W'_∞` the extension
`(q|_E)'` caps along `y ≫ κ` as `(q'|_{E'})'` caps along `y`, pushed forward along
`E' ×_{W'_∞} Y ⟶ E ×_{W_∞} Y`. -/
theorem modificationExtension_cap_comparison
    (hT₁ : ∀ w, modificationProjectionAtInfinity f₁ b₁ w ∉ Set.range z₁ → w ∈ Set.range t₁)
    (hT₂ : ∀ w, modificationProjectionAtInfinity f₂ b₂ w ∉ Set.range z₂ → w ∈ Set.range t₂)
    (hq₁ : BivariantClass.VanishesOver q₁ (t₁ ≫ modificationInclusionAtInfinity f₁ b₁))
    (hq₂ : BivariantClass.VanishesOver q₂ (t₂ ≫ modificationInclusionAtInfinity f₂ b₂))
    (hκW : κ ≫ modificationInclusionAtInfinity f₂ b₂ = modificationInclusionAtInfinity f₁ b₁ ≫ κW)
    (hκf : κW ≫ (modificationProjection f₂ b₂ ≫ f₂) = modificationProjection f₁ b₁ ≫ f₁)
    (heκ : eκ ≫ pullback.fst (modificationProjectionAtInfinity f₂ b₂) z₂ =
      pullback.fst (modificationProjectionAtInfinity f₁ b₁) z₁ ≫ κ)
    (hlT : lT ≫ t₂ = t₁ ≫ κ)
    (hq : ∀ {Y : Scheme.{u}} (y : Y ⟶ W₁) [LocallyOfFiniteType y] [LocallyOfFiniteType (y ≫ κW)]
      (k : ℤ) (γ : chowGroup C (y ≫ (modificationProjection f₁ b₁ ≫ f₁)) k)
      (γ' : chowGroup C ((y ≫ κW) ≫ (modificationProjection f₂ b₂ ≫ f₂)) k), γ ≍ γ' →
        q₁.idRule C _ (gysinSystemOfInvertible C) y k γ ≍
          q₂.idRule C _ (gysinSystemOfInvertible C) (y ≫ κW) k γ')
    {Y : Scheme.{u}} (y : Y ⟶ modificationFibreAtInfinity f₁ b₁) [LocallyOfFiniteType y]
    (y₂ : Y ⟶ modificationFibreAtInfinity f₂ b₂) [LocallyOfFiniteType y₂] (hy : y ≫ κ = y₂)
    (k : ℤ) (γ : chowGroup C (y ≫ (modificationProjectionAtInfinity f₁ b₁ ≫ f₁)) k) :
    (modificationExtension z₂ t₂ hT₂ hq₂).cap y₂ k
        (chowGroupCongr C (hy ▸ comp_comp_modificationProjectionAtInfinity_comp_eq hκW hκf y)
          k γ) =
      chowPush C _ _ (pullback.map _ y _ y₂ eκ (𝟙 Y) κ heκ.symm (by rw [Category.id_comp, hy]))
        (pullbackMap_exceptional_comp_structure hκW hκf heκ y y₂ hy)
        (k - p) ((modificationExtension z₁ t₁ hT₁ hq₁).cap y k γ) := by
  subst hy
  have hcover₁ := range_union_range_pullbackFst_eq_univ z₁ t₁ hT₁
  have hY := comp_comp_modificationProjectionAtInfinity_comp_eq hκW hκf y
  obtain ⟨⟨γA, γB⟩, rfl⟩ := surjective_closedCoverPullbackSum C _ t₁
    (pullback.fst (modificationProjectionAtInfinity f₁ b₁) z₁) _ rfl hcover₁ y k γ
  rw [closedCoverSum_apply, map_add, map_add, map_add]
  dsimp only
  rw [modificationExtension_cap_first]
  simp only [zero_add]
  rw [modificationExtension_cap_second z₁ t₁ hT₁ hq₁ y k γB]
  have hcover₂ := range_union_range_pullbackFst_eq_univ z₂ t₂ hT₂
  have eA := properChowPushforward_chowGroupCongr C rfl hY (pullback.snd t₁ y)
    (pullbackSnd_comp_structureMorphism (f := t₁) rfl y)
    (by rw [← hY, pullbackSnd_comp_structureMorphism (f := t₁) rfl y])
    k (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _) γA
  have eB := properChowPushforward_chowGroupCongr C rfl hY
    (pullback.snd (pullback.fst (modificationProjectionAtInfinity f₁ b₁) z₁) y)
    (pullbackSnd_comp_structureMorphism
      (f := pullback.fst (modificationProjectionAtInfinity f₁ b₁) z₁) rfl y)
    (by rw [← hY, pullbackSnd_comp_structureMorphism
      (f := pullback.fst (modificationProjectionAtInfinity f₁ b₁) z₁) rfl y])
    k (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _) γB
  refine (congrArg₂ (· + ·) ?_ ?_).trans (zero_add _)
  · refine (congrArg _ eA).trans ?_
    rw [modificationExtension_cap]
    exact closedCoverExtensionCap_chowPush_first_of_eq _ _ _ _ _ hcover₂ _ (y ≫ κ)
      (pullback.snd t₁ y) _ _ (pullback.fst t₁ y ≫ lT) (by rw [Category.assoc, hlT,
        ← Category.assoc, pullback.condition, Category.assoc]) k γA
  · refine (congrArg _ eB).trans ?_
    rw [modificationExtension_cap]
    refine (closedCoverExtensionCap_chowPush_second_of_eq _ _ _ _ _ hcover₂ _ (y ≫ κ)
      (pullback.snd (pullback.fst (modificationProjectionAtInfinity f₁ b₁) z₁) y) _ _
      (pullback.fst _ y ≫ eκ) (by rw [Category.assoc, heκ, ← Category.assoc,
        pullback.condition, Category.assoc]) (by rw [Category.assoc, reassoc_of% heκ,
          comp_modificationProjectionAtInfinity_comp_eq hκW hκf]) k γB).trans ?_
    refine (chowPush_congr C _ _ ?_ _ _ _ _).trans (congrArg _ (eq_of_heq ?_))
    · apply pullback.hom_ext
      · exact (pullback.lift_fst _ _ _).trans (pullback.lift_fst _ _ _).symm
      · exact (pullback.lift_snd _ _ _).trans ((pullback.lift_snd _ _ _).trans
          (Category.comp_id _)).symm
    have h1 := hκf
    have h2 := hκW
    have h3 := heκ
    simp only [Category.assoc] at h1 h2 h3
    refine (chowGroupCongr_heq C _ _ _).trans ?_
    refine (modificationRestriction_idRule_heq z₂ q₂
      (pullback.fst (pullback.fst (modificationProjectionAtInfinity f₁ b₁) z₁) y ≫ eκ) k _
      (chowGroupCongr C (by simp only [Category.assoc]; rw [reassoc_of% h3, reassoc_of% h2, h1])
        k γB) ((chowGroupCongr_heq C _ _ _).trans (chowGroupCongr_heq C _ _ _).symm)).trans ?_
    refine HEq.symm ((modificationRestriction_idRule_heq z₁ q₁
      (pullback.fst (pullback.fst (modificationProjectionAtInfinity f₁ b₁) z₁) y) k _
      (chowGroupCongr C (by simp only [Category.assoc]) k γB)
        (chowGroupCongr_heq C _ _ _).symm).trans
      ((hq _ k _ (chowGroupCongr C (by simp only [Category.assoc]; rw [h1]) k γB) ?_).trans
      (BivariantClass.idRule_heq_congr q₂ ?_ k _ _ ?_)))
    · exact (chowGroupCongr_heq C _ _ _).trans (chowGroupCongr_heq C _ _ _).symm
    · simp only [Category.assoc]
      rw [reassoc_of% h3, h2]
    · exact (chowGroupCongr_heq C _ _ _).trans (chowGroupCongr_heq C _ _ _).symm

/-- **Comparing the localized classes of two modifications, on a test scheme.** Let
`b₁ : W₁ ⟶ 𝐏¹_{X₁}` and `b₂ : W₂ ⟶ 𝐏¹_{X₂}` be proper and isomorphisms over the affine charts,
with closed subschemes `Z_i ⊆ X_i`, `T_i ⊆ W_{i,∞}` and classes `q_i ∈ A^p(W_i)` as in
Stacks 0F9K, and let `κ : W_{1,∞} ⟶ W_{2,∞}` be compatible with a morphism `W₁ ⟶ W₂` along which
`q₁` operates as `q₂`, with `E₁ ⟶ E₂` and `T₁ ⟶ T₂` over `κ`. Let `g_i : V ⟶ X_i` be test schemes
over the same morphism to the base, and `φ : W₁ ×_{X₁} V ⟶ W₂ ×_{X₂} V` proper, over `V` and
`𝐏¹_S`, with a compatible `φ_∞` on the fibres at infinity lying over `κ`. Then the localized
classes satisfy `ψ_*(q₁' ∩ α) = q₂' ∩ α` for every proper `ψ : Z₁ ×_{X₁} V ⟶ Z₂ ×_{X₂} V` over
`V`. -/
theorem localizedModificationClass_cap_comparison
    (hA₁ : IsIso (pullback.snd b₁ (projectiveLineAffineChart f₁)))
    (hA₂ : IsIso (pullback.snd b₂ (projectiveLineAffineChart f₂)))
    (hT₁ : ∀ w, modificationProjectionAtInfinity f₁ b₁ w ∉ Set.range z₁ → w ∈ Set.range t₁)
    (hT₂ : ∀ w, modificationProjectionAtInfinity f₂ b₂ w ∉ Set.range z₂ → w ∈ Set.range t₂)
    (hq₁ : BivariantClass.VanishesOver q₁ (t₁ ≫ modificationInclusionAtInfinity f₁ b₁))
    (hq₂ : BivariantClass.VanishesOver q₂ (t₂ ≫ modificationInclusionAtInfinity f₂ b₂))
    (hκW : κ ≫ modificationInclusionAtInfinity f₂ b₂ = modificationInclusionAtInfinity f₁ b₁ ≫ κW)
    (hκf : κW ≫ (modificationProjection f₂ b₂ ≫ f₂) = modificationProjection f₁ b₁ ≫ f₁)
    (heκ : eκ ≫ pullback.fst (modificationProjectionAtInfinity f₂ b₂) z₂ =
      pullback.fst (modificationProjectionAtInfinity f₁ b₁) z₁ ≫ κ)
    (hlT : lT ≫ t₂ = t₁ ≫ κ)
    (hq : ∀ {Y : Scheme.{u}} (y : Y ⟶ W₁) [LocallyOfFiniteType y] [LocallyOfFiniteType (y ≫ κW)]
      (k : ℤ) (γ : chowGroup C (y ≫ (modificationProjection f₁ b₁ ≫ f₁)) k)
      (γ' : chowGroup C ((y ≫ κW) ≫ (modificationProjection f₂ b₂ ≫ f₂)) k), γ ≍ γ' →
        q₁.idRule C _ (gysinSystemOfInvertible C) y k γ ≍
          q₂.idRule C _ (gysinSystemOfInvertible C) (y ≫ κW) k γ')
    {V : Scheme.{u}} (g₁ : V ⟶ X₁) [LocallyOfFiniteType g₁] (g₂ : V ⟶ X₂)
    [LocallyOfFiniteType g₂] (hT : g₁ ≫ f₁ = g₂ ≫ f₂)
    (φ : modificationBaseChange f₁ b₁ g₁ ⟶ modificationBaseChange f₂ b₂ g₂) [IsProper φ]
    (hφT : φ ≫ pullback.snd (modificationProjection f₂ b₂) g₂ =
      pullback.snd (modificationProjection f₁ b₁) g₁)
    (hφ : φ ≫ modificationBaseChangeToRelativeLine f₂ b₂ g₂ =
      modificationBaseChangeToRelativeLine f₁ b₁ g₁)
    (φInf : pullback (modificationProjectionAtInfinity f₁ b₁) g₁ ⟶
      pullback (modificationProjectionAtInfinity f₂ b₂) g₂) [IsProper φInf]
    (hφInf : φInf ≫ modificationInfinityBaseChange f₂ b₂ g₂ =
      modificationInfinityBaseChange f₁ b₁ g₁ ≫ φ)
    (hφκ : φInf ≫ pullback.fst (modificationProjectionAtInfinity f₂ b₂) g₂ =
      pullback.fst (modificationProjectionAtInfinity f₁ b₁) g₁ ≫ κ)
    (ψ : pullback z₁ g₁ ⟶ pullback z₂ g₂) [IsProper ψ]
    (hψ : ψ ≫ pullback.snd z₂ g₂ = pullback.snd z₁ g₁) (k : ℤ) (α : chowGroup C (g₁ ≫ f₁) k) :
    chowPush C _ _ ψ (pullbackFst_comp_structure_of_comp_snd z₁ z₂ hT ψ hψ) (k - p)
        ((localizedModificationClass (gysinAtInfinityData C f₁ b₁ hA₁) z₁ t₁ hT₁ hq₁).cap
          g₁ k α) =
      (localizedModificationClass (gysinAtInfinityData C f₂ b₂ hA₂) z₂ t₂ hT₂ hq₂).cap g₂ k
        (chowGroupCongr C hT k α) := by
  have hψs := pullbackFst_comp_structure_of_comp_snd z₁ z₂ hT ψ hψ
  have hφover := comp_modificationBaseChangeOver_of_comp_snd φ hT hφT
  have hInfOver := comp_modificationInfinityBaseChangeOver_of_comp φ hφover φInf hφInf
  have hφInfT : φInf ≫ pullback.snd (modificationProjectionAtInfinity f₂ b₂) g₂ =
      pullback.snd (modificationProjectionAtInfinity f₁ b₁) g₁ := by
    rw [← modificationInfinityBaseChange_comp_snd f₂ b₂ g₂, reassoc_of% hφInf, hφT,
      modificationInfinityBaseChange_comp_snd]
  -- the class at infinity: `C₂ ∩ α = φ_{∞,*}(C₁ ∩ α)`
  have hC : chowPush C _ _ φInf hInfOver (k - 0)
        ((gysinAtInfinityData C f₁ b₁ hA₁).bivariantClass.cap g₁ k α) =
      (gysinAtInfinityData C f₂ b₂ hA₂).bivariantClass.cap g₂ k (chowGroupCongr C hT k α) := by
    have key := gysinCapOfLift_comparison C φ φInf hT hA₁ hA₂ hφT hφ hφInf k α
    refine eq_of_heq ((chowPush_heq C φInf hInfOver hInfOver rfl rfl (sub_zero k)
      (chowGroupDegreeEquiv_heq C _ _ _)).trans ?_)
    exact (heq_of_eq key.symm).trans (chowGroupDegreeEquiv_heq C _ _ _).symm
  have hβ' : pullback.fst (modificationProjectionAtInfinity f₁ b₁) g₁ ≫
      (modificationProjectionAtInfinity f₁ b₁ ≫ f₁) =
        (φInf ≫ pullback.fst (modificationProjectionAtInfinity f₂ b₂) g₂) ≫
          (modificationProjectionAtInfinity f₂ b₂ ≫ f₂) := by
    rw [hφκ]
    exact comp_comp_modificationProjectionAtInfinity_comp_eq hκW hκf _
  have hC' : chowPush C _ (pullback.fst (modificationProjectionAtInfinity f₂ b₂) g₂ ≫
        (modificationProjectionAtInfinity f₂ b₂ ≫ f₂)) φInf (Category.assoc _ _ _).symm (k - 0)
        (chowGroupCongr C hβ' (k - 0)
          ((gysinAtInfinityData C f₁ b₁ hA₁).bivariantClass.cap g₁ k α)) =
      (gysinAtInfinityData C f₂ b₂ hA₂).bivariantClass.cap g₂ k (chowGroupCongr C hT k α) :=
    eq_of_heq ((chowPush_heq C φInf _ hInfOver hβ'.symm rfl rfl
      (chowGroupCongr_heq C _ _ _)).trans (heq_of_eq hC))
  -- proper naturality of the extension along `φ_∞`
  have hN := (modificationExtension z₂ t₂ hT₂ hq₂).proper_naturality_of_test_eq
    (pullback.fst (modificationProjectionAtInfinity f₂ b₂) g₂) φInf
    (φInf ≫ pullback.fst (modificationProjectionAtInfinity f₂ b₂) g₂) rfl
    (bivariantBaseChangeMap (pullback.fst (modificationProjectionAtInfinity f₂ b₂) z₂)
      (pullback.fst (modificationProjectionAtInfinity f₂ b₂) g₂) φInf)
    (isPullback_bivariantBaseChangeMap _ _ _) (by simp [bivariantBaseChangeMap]) (k - 0)
    (Category.assoc _ _ _).symm
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    (chowGroupCongr C hβ' (k - 0) ((gysinAtInfinityData C f₁ b₁ hA₁).bivariantClass.cap g₁ k α))
  -- the extension of the restriction
  have hL := modificationExtension_cap_comparison hT₁ hT₂ hq₁ hq₂ hκW hκf heκ hlT hq
    (pullback.fst (modificationProjectionAtInfinity f₁ b₁) g₁)
    (φInf ≫ pullback.fst (modificationProjectionAtInfinity f₂ b₂) g₂) hφκ.symm (k - 0)
    ((gysinAtInfinityData C f₁ b₁ hA₁).bivariantClass.cap g₁ k α)
  have hcap₁ := localizedModificationClass_cap_heq (gysinAtInfinityData C f₁ b₁ hA₁) z₁ t₁ hT₁
    hq₁ g₁ k α
  have hcap₂ := localizedModificationClass_cap_heq (gysinAtInfinityData C f₂ b₂ hA₂) z₂ t₂ hT₂
    hq₂ g₂ k (chowGroupCongr C hT k α)
  refine eq_of_heq (((chowPush_heq C ψ hψs hψs rfl rfl (by ring : k - p = (k - 0) - p)
    hcap₁).trans ?_).trans hcap₂.symm)
  refine heq_of_eq ?_
  rw [← hC', hN, hL]
  have hmor : exceptionalBaseChangeMap (modificationProjectionAtInfinity f₁ b₁) z₁ g₁ ≫ ψ =
      (pullback.map (pullback.fst (modificationProjectionAtInfinity f₁ b₁) z₁)
        (pullback.fst (modificationProjectionAtInfinity f₁ b₁) g₁)
        (pullback.fst (modificationProjectionAtInfinity f₂ b₂) z₂)
        (φInf ≫ pullback.fst (modificationProjectionAtInfinity f₂ b₂) g₂) eκ (𝟙 _) κ heκ.symm
          (by rw [Category.id_comp, hφκ]) ≫
        bivariantBaseChangeMap (pullback.fst (modificationProjectionAtInfinity f₂ b₂) z₂)
          (pullback.fst (modificationProjectionAtInfinity f₂ b₂) g₂) φInf) ≫
      exceptionalBaseChangeMap (modificationProjectionAtInfinity f₂ b₂) z₂ g₂ := by
    refine (cancel_mono (pullback.snd z₂ g₂)).1 ?_
    simp only [Category.assoc, hψ, exceptionalBaseChangeMap_snd,
      bivariantBaseChangeMap, pullback.lift_snd_assoc, hφInfT, Category.comp_id]
  have hw₁ : (exceptionalBaseChangeMap (modificationProjectionAtInfinity f₁ b₁) z₁ g₁ ≫ ψ) ≫
      (pullback.fst z₂ g₂ ≫ (z₂ ≫ f₂)) =
        pullback.fst (pullback.fst (modificationProjectionAtInfinity f₁ b₁) z₁)
          (pullback.fst (modificationProjectionAtInfinity f₁ b₁) g₁) ≫
            (pullback.fst (modificationProjectionAtInfinity f₁ b₁) z₁ ≫
              modificationProjectionAtInfinity f₁ b₁ ≫ f₁) := by
    rw [Category.assoc, hψs, exceptionalBaseChangeMap_comp_structure]
  have hw₃ : (bivariantBaseChangeMap (pullback.fst (modificationProjectionAtInfinity f₂ b₂) z₂)
        (pullback.fst (modificationProjectionAtInfinity f₂ b₂) g₂) φInf ≫
      exceptionalBaseChangeMap (modificationProjectionAtInfinity f₂ b₂) z₂ g₂) ≫
        (pullback.fst z₂ g₂ ≫ (z₂ ≫ f₂)) =
      pullback.fst (pullback.fst (modificationProjectionAtInfinity f₂ b₂) z₂)
          (φInf ≫ pullback.fst (modificationProjectionAtInfinity f₂ b₂) g₂) ≫
        (pullback.fst (modificationProjectionAtInfinity f₂ b₂) z₂ ≫
          modificationProjectionAtInfinity f₂ b₂ ≫ f₂) := by
    rw [Category.assoc, exceptionalBaseChangeMap_comp_structure, bivariantBaseChangeMap,
      pullback.lift_fst_assoc, Category.comp_id]
  rw [Category.assoc] at hmor
  have hbb : bivariantBaseChangeMap (pullback.fst (modificationProjectionAtInfinity f₂ b₂) z₂)
        (pullback.fst (modificationProjectionAtInfinity f₂ b₂) g₂) φInf ≫
      (pullback.fst (pullback.fst (modificationProjectionAtInfinity f₂ b₂) z₂)
          (pullback.fst (modificationProjectionAtInfinity f₂ b₂) g₂) ≫
        (pullback.fst (modificationProjectionAtInfinity f₂ b₂) z₂ ≫
          modificationProjectionAtInfinity f₂ b₂ ≫ f₂)) =
      pullback.fst (pullback.fst (modificationProjectionAtInfinity f₂ b₂) z₂)
          (φInf ≫ pullback.fst (modificationProjectionAtInfinity f₂ b₂) g₂) ≫
        (pullback.fst (modificationProjectionAtInfinity f₂ b₂) z₂ ≫
          modificationProjectionAtInfinity f₂ b₂ ≫ f₂) := by
    rw [bivariantBaseChangeMap, pullback.lift_fst_assoc, Category.comp_id]
  have e1 := chowPush_comp C _ _ (pullback.fst z₂ g₂ ≫ (z₂ ≫ f₂))
    (bivariantBaseChangeMap (pullback.fst (modificationProjectionAtInfinity f₂ b₂) z₂)
      (pullback.fst (modificationProjectionAtInfinity f₂ b₂) g₂) φInf)
    (exceptionalBaseChangeMap (modificationProjectionAtInfinity f₂ b₂) z₂ g₂) _ rfl hbb
    (exceptionalBaseChangeMap_comp_structure _ z₂ g₂ f₂) hw₃ ((k - 0) - p)
    (chowPush C _ _ (pullback.map (pullback.fst (modificationProjectionAtInfinity f₁ b₁) z₁)
        (pullback.fst (modificationProjectionAtInfinity f₁ b₁) g₁)
        (pullback.fst (modificationProjectionAtInfinity f₂ b₂) z₂)
        (φInf ≫ pullback.fst (modificationProjectionAtInfinity f₂ b₂) g₂) eκ (𝟙 _) κ heκ.symm
          (by rw [Category.id_comp, hφκ]))
      (pullbackMap_exceptional_comp_structure hκW hκf heκ _ _ hφκ.symm) ((k - 0) - p)
      ((modificationExtension z₁ t₁ hT₁ hq₁).cap
        (pullback.fst (modificationProjectionAtInfinity f₁ b₁) g₁) (k - 0)
        ((gysinAtInfinityData C f₁ b₁ hA₁).bivariantClass.cap g₁ k α)))
  have e2 := chowPush_comp C _ _ (pullback.fst z₂ g₂ ≫ (z₂ ≫ f₂))
    (pullback.map (pullback.fst (modificationProjectionAtInfinity f₁ b₁) z₁)
        (pullback.fst (modificationProjectionAtInfinity f₁ b₁) g₁)
        (pullback.fst (modificationProjectionAtInfinity f₂ b₂) z₂)
        (φInf ≫ pullback.fst (modificationProjectionAtInfinity f₂ b₂) g₂) eκ (𝟙 _) κ heκ.symm
          (by rw [Category.id_comp, hφκ]))
    (bivariantBaseChangeMap (pullback.fst (modificationProjectionAtInfinity f₂ b₂) z₂)
        (pullback.fst (modificationProjectionAtInfinity f₂ b₂) g₂) φInf ≫
      exceptionalBaseChangeMap (modificationProjectionAtInfinity f₂ b₂) z₂ g₂) _ rfl
    (pullbackMap_exceptional_comp_structure hκW hκf heκ _ _ hφκ.symm) hw₃ (hmor ▸ hw₁)
    ((k - 0) - p)
    ((modificationExtension z₁ t₁ hT₁ hq₁).cap
        (pullback.fst (modificationProjectionAtInfinity f₁ b₁) g₁) (k - 0)
        ((gysinAtInfinityData C f₁ b₁ hA₁).bivariantClass.cap g₁ k α))
  rw [chowPush_comp C _ _ _
    (exceptionalBaseChangeMap (modificationProjectionAtInfinity f₁ b₁) z₁ g₁) ψ _ rfl _ _ hw₁,
    chowPush_congr C _ _ hmor hw₁ (hmor ▸ hw₁), ← e2]
  exact e1.symm

end ExtensionComparison

/-! ### Invariance under a further modification: the second assertion of Stacks 0FAU -/


section FurtherModification

variable {C : ChowSituation.{u}} {X W W' Z T T' : Scheme.{u}} {f : X ⟶ C.S}
  [LocallyOfFiniteType f] {b : W ⟶ projectiveLineProduct f} [IsProper b]
  {b' : W' ⟶ projectiveLineProduct f} [IsProper b'] (z : Z ⟶ X) [IsClosedImmersion z]
  {p : ℤ}

/-- **The localized class is invariant under a further modification**, the generic form of the
second assertion of Stacks 0FAU. Let `b : W ⟶ 𝐏¹_X` be proper and an isomorphism over `𝐀¹_X`,
let `g : W' ⟶ W` be proper with `b' = b ∘ g` an isomorphism over `𝐀¹_X` (as it is when `g` is
one, `Stacks.Chow.isIso_pullbackSnd_comp_projectiveLineAffineChart`). Let
`q ∈ A^p(W)` vanish over a closed `T ⊆ W_∞` containing every point of `W_∞` over `X ∖ Z`, and let
`q' ∈ A^p(W')` operate on every test scheme over `W'` as `q` does through `g` (for instance
`q' = g^* q`). Then for every closed `T' ⊆ W'_∞` containing every point of `W'_∞` over `X ∖ Z`
over which `q'` vanishes, the localized classes of Stacks 0F9K agree: `q'' = q'` in `A^p(Z ⟶ X)`,
where `q''` is built from `b'`, `q'` and `T'`. -/
theorem localizedModificationClass_eq_of_modification
    (hA : IsIso (pullback.snd b (projectiveLineAffineChart f))) (g : W' ⟶ W) [IsProper g]
    (hb : g ≫ b = b') (hA' : IsIso (pullback.snd b' (projectiveLineAffineChart f)))
    (t : T ⟶ modificationFibreAtInfinity f b) [IsClosedImmersion t]
    (t' : T' ⟶ modificationFibreAtInfinity f b') [IsClosedImmersion t']
    {q : chowCohomologyComponent C (gysinSystemOfInvertible C) (modificationProjection f b ≫ f) p}
    {q' : chowCohomologyComponent C (gysinSystemOfInvertible C)
      (modificationProjection f b' ≫ f) p}
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (hT' : ∀ w, modificationProjectionAtInfinity f b' w ∉ Set.range z → w ∈ Set.range t')
    (hq : BivariantClass.VanishesOver q (t ≫ modificationInclusionAtInfinity f b))
    (hq' : BivariantClass.VanishesOver q' (t' ≫ modificationInclusionAtInfinity f b'))
    (hqq' : ∀ {Y : Scheme.{u}} (y : Y ⟶ W') [LocallyOfFiniteType y] [LocallyOfFiniteType (y ≫ g)]
      (k : ℤ) (γ : chowGroup C (y ≫ (modificationProjection f b' ≫ f)) k)
      (γ' : chowGroup C ((y ≫ g) ≫ (modificationProjection f b ≫ f)) k), γ ≍ γ' →
        q'.idRule C _ (gysinSystemOfInvertible C) y k γ ≍
          q.idRule C _ (gysinSystemOfInvertible C) (y ≫ g) k γ') :
    localizedModificationClass (gysinAtInfinityData C f b' hA') z t' hT' hq' =
      localizedModificationClass (gysinAtInfinityData C f b hA) z t hT hq := by
  subst hb
  set κ := modificationFibreAtInfinityMap f b g
  have hκπ : κ ≫ modificationProjectionAtInfinity f b =
      modificationProjectionAtInfinity f (g ≫ b) :=
    (modificationProjectionAtInfinity_comp_eq f b g).symm
  -- the closed subscheme `g_∞⁻¹(T) ⊆ W'_∞`
  have hT'' : ∀ w, modificationProjectionAtInfinity f (g ≫ b) w ∉ Set.range z →
      w ∈ Set.range (pullback.snd t κ) := by
    intro w hw
    rw [Scheme.Pullback.range_snd]
    refine hT (κ w) ?_
    rwa [← Scheme.Hom.comp_apply, hκπ]
  have hq'' : BivariantClass.VanishesOver q'
      (pullback.snd t κ ≫ modificationInclusionAtInfinity f (g ≫ b)) := by
    refine BivariantClass.VanishesOver.of_idRule_eq_zero fun {Y} y _ k x ↦ ?_
    have hm : (y ≫ pullback.fst t κ) ≫ (t ≫ modificationInclusionAtInfinity f b) =
        (y ≫ pullback.snd t κ ≫ modificationInclusionAtInfinity f (g ≫ b)) ≫ g := by
      simp only [Category.assoc]
      rw [pullback.condition_assoc, modificationFibreAtInfinityMap_fst]
    have : LocallyOfFiniteType
        ((y ≫ pullback.snd t κ ≫ modificationInclusionAtInfinity f (g ≫ b)) ≫ g) := by
      rw [← hm]
      infer_instance
    refine chowGroup_eq_zero_of_heq_zero_of_base_eq (by simp only [Category.assoc]) ((hqq' _ k x
      (chowGroupCongr C (by simp [modificationProjection]) k x)
      (chowGroupCongr_heq C _ _ _).symm).trans (heq_of_eq ?_))
    exact hq.idRule_eq_zero _ _ hm k _
  rw [localizedModificationClass_eq _ z t' (pullback.snd t κ) hT' hT'' hq' hq'']
  refine BivariantClass.ext _ _ _ _ _ _ _ fun {V} v _ k α ↦ ?_
  let eκ : pullback (modificationProjectionAtInfinity f (g ≫ b)) z ⟶
      pullback (modificationProjectionAtInfinity f b) z :=
    pullback.map _ z _ z κ (𝟙 Z) (𝟙 X) (by rw [Category.comp_id, hκπ]) (by simp)
  have : LocallyOfFiniteType eκ := by
    have : LocallyOfFiniteType (eκ ≫ pullback.snd (modificationProjectionAtInfinity f b) z) := by
      rw [pullback.lift_snd, Category.comp_id]
      infer_instance
    exact locallyOfFiniteType_of_comp eκ (pullback.snd _ z)
  have key := localizedModificationClass_cap_comparison (κW := g) (κ := κ) (eκ := eκ)
    (lT := pullback.fst t κ) hA' hA hT'' hT hq'' hq (modificationFibreAtInfinityMap_fst f b g)
    (by simp [modificationProjection]) (pullback.lift_fst _ _ _) pullback.condition hqq' v v rfl
    (modificationMapBaseChange f b g v) (modificationMapBaseChange_snd f b g v)
    (modificationMapBaseChange_toRelativeLine f b g v) (modificationInfinityMapBaseChange f b g v)
    (modificationInfinityMapBaseChange_comp f b g v) (by simp [κ]) (𝟙 _) (Category.id_comp _) k α
  rw [chowPush_id] at key
  exact key

end FurtherModification

/-- If the restriction of a total class `c` along `g` is `c'`, the operation of `c' p` on a test
scheme `y` is that of `c p` on `y ≫ g`. -/
private theorem idRule_heq_of_res_eq {C : ChowSituation.{u}} {Y Y' : Scheme.{u}}
    {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {sY' : Y' ⟶ C.S} [LocallyOfFiniteType sY']
    (g : Y' ⟶ Y) [LocallyOfFiniteType g] (hs : g ≫ sY = sY') (c : TotalChowClass C sY)
    (c' : TotalChowClass C sY') (h : TotalChowClass.res g hs c = c') (p : ℕ) {T : Scheme.{u}}
    (y : T ⟶ Y') [LocallyOfFiniteType y] [LocallyOfFiniteType (y ≫ g)] (k : ℤ)
    (γ : chowGroup C (y ≫ sY') k) (γ' : chowGroup C ((y ≫ g) ≫ sY) k) (hγ : γ ≍ γ') :
    (c' p).idRule C sY' (gysinSystemOfInvertible C) y k γ ≍
      (c p).idRule C sY (gysinSystemOfInvertible C) (y ≫ g) k γ' := by
  subst h
  exact TotalChowClass.idRule_res_apply_heq g hs c p y k γ γ' hγ

section PerfectFurtherModification

attribute [local instance 10000] HasDerivedCategory.standard

variable (C : ChowSituation.{u}) {X W W' Z T T' : Scheme.{u}} (f : X ⟶ C.S)
  [LocallyOfFiniteType f] (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (b' : W' ⟶ projectiveLineProduct f) [IsProper b']
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f))) (g : W' ⟶ W) [IsProper g]
  (hb : g ≫ b = b') (hA' : IsIso (pullback.snd b' (projectiveLineAffineChart f)))
  (z : Z ⟶ X) [IsClosedImmersion z]
  (t : T ⟶ modificationFibreAtInfinity f b) [IsClosedImmersion t]
  (t' : T' ⟶ modificationFibreAtInfinity f b') [IsClosedImmersion t']
  {Q : DerivedCategory W.Modules} (hQ : HasDefinedChernClasses Q) (p : ℕ)

omit [LocallyOfFiniteType f] [IsProper b] [IsProper g] in
include hb in
/-- The structure morphism of `W'` over the base factors through `g`. -/
theorem comp_modificationProjection_comp_eq :
    g ≫ (modificationProjection f b ≫ f) = modificationProjection f b' ≫ f := by
  subst hb
  simp [modificationProjection]

include hb in
/-- **The second assertion of Stacks 0FAU, for `P'_p`.** Let `b : W ⟶ 𝐏¹_X` be proper and an
isomorphism over `𝐀¹_X`, let `g : W' ⟶ W` be proper with `b' = b ∘ g` an isomorphism over `𝐀¹_X`
(as it is when `g` is one, `Stacks.Chow.isIso_pullbackSnd_comp_projectiveLineAffineChart`), and
set `Q' = Lg^*Q`. Then `P'_p(Q') = P'_p(Q)` in `A^p(Z ⟶ X)`, the left side built from
`b'`, `Q'` and any closed `T' ⊆ W'_∞` with the properties of Stacks 0F9K, the right side from `b`,
`Q` and `T ⊆ W_∞`. -/
@[stacks 0FAU "second assertion, for P'_p: for g : W' ⟶ W proper with b ∘ g an isomorphism \
over A^1_X (as when g is one), P'_p(g^*Q) = P'_p(Q)"]
theorem modificationPowerSum_eq_of_modification
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (hT' : ∀ w, modificationProjectionAtInfinity f b' w ∉ Set.range z → w ∈ Set.range t')
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (t ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q))
    (hzero' : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (t' ≫ modificationInclusionAtInfinity f b').toLRSHom.toShHom).obj
        ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g.toLRSHom.toShHom).obj Q))) :
    modificationPowerSum C f b' hA' z t' (hQ.derivedPullback g) p hT' hzero' =
      modificationPowerSum C f b hA z t hQ p hT hzero := by
  refine localizedModificationClass_eq_of_modification z hA g hb hA' t t' hT hT'
    (vanishesOver_perfectPowerSumClass_of_isZero C _ _ hQ p hzero)
    (vanishesOver_perfectPowerSumClass_of_isZero C _ _ (hQ.derivedPullback g) p hzero') ?_
  intro Y y _ _ k γ γ' hγ
  have hs := comp_modificationProjection_comp_eq C f b b' g hb
  exact idRule_heq_of_res_eq g hs _ _
    (res_perfectPowerSum_derivedPullback C _ hQ g hs (hQ.derivedPullback g) p) p y k γ γ' hγ

include hb in
/-- **The second assertion of Stacks 0FAU, for `c'_p`.** Let `b : W ⟶ 𝐏¹_X` be proper and an
isomorphism over `𝐀¹_X`, let `g : W' ⟶ W` be proper with `b' = b ∘ g` an isomorphism over `𝐀¹_X`
(as it is when `g` is one, `Stacks.Chow.isIso_pullbackSnd_comp_projectiveLineAffineChart`), and
set `Q' = Lg^*Q`. Then `c'_p(Q') = c'_p(Q)` in `A^p(Z ⟶ X)`, the left side built from
`b'`, `Q'` and any closed `T' ⊆ W'_∞` with the properties of Stacks 0F9K, the right side from `b`,
`Q` and `T ⊆ W_∞`. -/
@[stacks 0FAU "second assertion, for c'_p: for g : W' ⟶ W proper with b ∘ g an isomorphism \
over A^1_X (as when g is one), c'_p(g^*Q) = c'_p(Q)"]
theorem modificationChernClass_eq_of_modification
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (hT' : ∀ w, modificationProjectionAtInfinity f b' w ∉ Set.range z → w ∈ Set.range t')
    (hrank : ∃ M : T.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (t ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q ≅
          (DerivedCategory.singleFunctor _ 0).obj M))
    (hrank' : ∃ M : T'.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (t' ≫ modificationInclusionAtInfinity f b').toLRSHom.toShHom).obj
          ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g.toLRSHom.toShHom).obj Q) ≅
          (DerivedCategory.singleFunctor _ 0).obj M)) :
    modificationChernClass C f b' hA' z t' (hQ.derivedPullback g) p hT' hrank' =
      modificationChernClass C f b hA z t hQ p hT hrank := by
  refine localizedModificationClass_eq_of_modification z hA g hb hA' t t' hT hT'
    (vanishesOver_perfectChernClass_of_rankLT C _ _ hQ p hrank)
    (vanishesOver_perfectChernClass_of_rankLT C _ _ (hQ.derivedPullback g) p hrank') ?_
  intro Y y _ _ k γ γ' hγ
  have hs := comp_modificationProjection_comp_eq C f b b' g hb
  exact idRule_heq_of_res_eq g hs _ _
    (res_perfectChernClass_derivedPullback_of_comp_eq C _ hQ g hs (hQ.derivedPullback g)) p y k γ γ'
      hγ

end PerfectFurtherModification

end Stacks.Chow

end
