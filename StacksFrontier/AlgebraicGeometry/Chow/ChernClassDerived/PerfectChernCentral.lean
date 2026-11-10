module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.PerfectChernCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BivariantChernCentral
public import StacksFrontier.AlgebraicGeometry.Chow.BabyLocalizedChern.ClosedCoverClass
public import StacksFrontier.AlgebraicGeometry.Chow.BabyLocalizedChern.LocalizedChernGysinCommute
public import StacksFrontier.AlgebraicGeometry.Chow.BabyLocalizedChern.LocalizedPowerSumAtInfinity
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinity.Commuting
public import StacksCore.Tactic.StacksAttribute

/-!
# The Chern classes of a perfect object are central and commute with bivariant classes

Let `(S, δ)` be a Chow situation, let `X` be locally of finite type over `S` and let
`E ∈ D(𝒪_X)` be a perfect object whose Chern classes are defined. Then:

1. `c_p(E)` is in the center of the Chow cohomology ring `A^*(X)`,
   `Stacks.Chow.chowCohomologyRingOfInvertible`;
2. if `g : X' ⟶ X` is locally of finite type and `c ∈ A^q(X' ⟶ X)` is a bivariant class
   (`Stacks.Chow.BivariantChowClass`), then `c ∘ c_p(E) = c_p(Lg^*E) ∘ c`, the composites being
   `Stacks.Chow.BivariantChowClass.comp`.

The same holds for the classes `P_p(E) ∈ A^p(X)` and `ch_p(E) ∈ A^p(X) ⊗ 𝐐`.

## Main definitions

* `Stacks.Chow.BivariantChowClass.compRightHom`, `Stacks.Chow.BivariantChowClass.compLeftHom`:
  composition with a bivariant class on the right and on the left, as homomorphisms of groups.

## Main results

* `Stacks.Chow.comp_perfectChernClass`: `c ∘ c_p(E) = c_p(Lg^*E) ∘ c`.
* `Stacks.Chow.perfectChernClass_mem_center`: `c_p(E)` is central.
* `Stacks.Chow.comp_perfectPowerSumComponent`,
  `Stacks.Chow.perfectPowerSumComponent_mem_center`: the same for `P_p(E)`.
* `Stacks.Chow.comp_perfectChernCharacterComponent`,
  `Stacks.Chow.perfectChernCharacterComponent_mem_center`: the same for `ch_p(E) = P_p(E)/p!`, the
  composites with a rational class being the rational extensions of
  `Stacks.Chow.BivariantChowClass.compRightHom` and `Stacks.Chow.BivariantChowClass.compLeftHom`,
  and the center being that of `A^*(X) ⊗ 𝐐`.

## Implementation notes

The two composites of clause (2) are classes for `g ≫ 𝟙 X` and `𝟙 X' ≫ g`, of degrees `q + p`
and `p + q`; the second is read as a class for `g ≫ 𝟙 X` of degree `q + p` through
`Stacks.Chow.BivariantChowClass.degreeCongr` and the transport along the identity of `X'`.

## References

* [Stacks Project, Tag 0FAC](https://stacks.math.columbia.edu/tag/0FAC)
* [Stacks Project, Tag 0F9E](https://stacks.math.columbia.edu/tag/0F9E)
* [Stacks Project, Tag 02UA](https://stacks.math.columbia.edu/tag/02UA)
* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
* [Stacks Project, Tag 0GUF](https://stacks.math.columbia.edu/tag/0GUF)
* [Stacks Project, Tag 0B7E](https://stacks.math.columbia.edu/tag/0B7E)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Reading a class of `A^*(X)` on the test schemes -/

section General

variable {C : ChowSituation.{u}} {X : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]

/-- The cap operation of a class `κ ∈ A^p(X)` at a test scheme `t : T ⟶ X` is its operation on
`T`, read on `X ×_X T` through the identification with `T`. -/
theorem cap_eq_chowPushforwardOfIso_idRule {p : ℤ}
    (κ : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p) {T : Scheme.{u}}
    (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sX) k) :
    κ.cap t k α =
      chowPushforwardOfIso C (t ≫ sX) (pullback.fst (𝟙 X) t ≫ sX) (identityBaseChangeIso t).inv
        (GenuineChern.identityBaseChangeIso_inv_comp_base t) (k - p)
        (κ.idRule C sX (gysinSystemOfInvertible C) t k α) := by
  rw [BivariantClass.idRule_apply, pullbackSndPush, chowPushforwardOfIso_comp_apply,
    chowPushforwardOfIso_congr_apply C _ _ _ (𝟙 _) (by simp) _ (Category.id_comp _),
    chowPushforwardOfIso_id]

variable {X' : Scheme.{u}} {sX' : X' ⟶ C.S} [LocallyOfFiniteType sX']

/-- The comparison of `T ×_X X'` with `(X ×_X T) ×_X X'` over the identification `T ≅ X ×_X T`. -/
private abbrev identityTestComparison (g : X' ⟶ X) {T : Scheme.{u}} (t : T ⟶ X) :
    pullback g t ⟶ pullback g (pullback.fst (𝟙 X) t) :=
  pullback.map g t g (pullback.fst (𝟙 X) t) (𝟙 X') (identityBaseChangeIso t).inv (𝟙 X)
    (by simp) (by rw [Category.comp_id, fst_eq_identityBaseChangeIso_hom t, Iso.inv_hom_id_assoc])

/-- **Commuting on the test schemes gives equal composites.** Let `κ ∈ A^p(X)`,
`κ' ∈ A^p(X')` and `c ∈ A^q(X' ⟶ X)`. If on every test scheme `t : T ⟶ X`
`c ∩ (κ ∩ α) = κ' ∩ (c ∩ α)`, then `c ∘ κ = κ' ∘ c` in `A^{q+p}(X' ⟶ X)`. -/
theorem comp_eq_of_cap_idRule_heq {p q : ℤ}
    (κ : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p)
    (κ' : chowCohomologyComponent C (gysinSystemOfInvertible C) sX' p) (g : X' ⟶ X)
    (hg : g ≫ sX = sX') (c : BivariantChowClass C sX' sX g hg q)
    (H : ∀ {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ)
      (α : chowGroup C (t ≫ sX) k),
      c.cap t (k - p) (κ.idRule C sX (gysinSystemOfInvertible C) t k α) ≍
        κ'.idRule C sX' (gysinSystemOfInvertible C) (pullback.fst g t) (k - q) (c.cap t k α)) :
    c.comp (BivariantChowClass.equivBivariantClass.symm κ) =
      (((BivariantChowClass.equivBivariantClass.symm κ').comp c).degreeCongr
        (add_comm p q)).transport (comp_comp_structureMorphism_eq hg (Category.id_comp sX))
        (Iso.refl X') (by simp) := by
  have := BivariantChowClass.locallyOfFiniteType_of_structure sX g hg
  refine BivariantChowClass.ext fun {T} t _ k α ↦ ?_
  have hcore := H t k α
  have hw₁ : identityTestComparison g t ≫ pullback.fst g (pullback.fst (𝟙 X) t) =
      pullback.fst g t := by
    simp [identityTestComparison]
  have hw₂ : identityTestComparison g t ≫ pullback.snd g (pullback.fst (𝟙 X) t) =
      pullback.snd g t ≫ (identityBaseChangeIso t).inv := by
    simp [identityTestComparison]
  have hwX : identityTestComparison g t ≫ pullback.fst g (pullback.fst (𝟙 X) t) ≫ sX' =
      pullback.fst g t ≫ sX' := by
    rw [← Category.assoc, hw₁]
  rw [BivariantChowClass.comp_cap, BivariantChowClass.equivBivariantClass_symm_cap,
    cap_eq_chowPushforwardOfIso_idRule, c.cap_chowPushforwardOfIso (pullback.fst (𝟙 X) t) t
      (identityBaseChangeIso t).inv (by rw [fst_eq_identityBaseChangeIso_hom t,
        Iso.inv_hom_id_assoc]) (GenuineChern.identityBaseChangeIso_inv_comp_base t)
      (identityTestComparison g t) hw₁ hw₂ hwX, chowPushforwardOfIso_comp_apply]
  rw [BivariantChowClass.transport_cap]
  refine eq_of_heq ((chowGroupDegreeEquiv_heq C _ _ _).trans ?_)
  refine (GysinAtInfinity.chowPushforwardOfIso_heq_of_heq C _ _ (by omega) hcore).trans ?_
  refine HEq.symm ((GysinAtInfinity.chowPushforwardOfIso_heq_of_heq C _ _ (by omega)
    (BivariantChowClass.degreeCongr_cap _ _ t k α)).trans ?_)
  rw [BivariantChowClass.comp_cap, BivariantChowClass.equivBivariantClass_symm_cap,
    cap_eq_chowPushforwardOfIso_idRule, chowPushforwardOfIso_comp_apply]
  refine (GysinAtInfinity.chowPushforwardOfIso_heq_of_heq C _ _ (by omega)
    (chowGroupDegreeEquiv_heq C _ _ _)).trans ?_
  rw [chowPushforwardOfIso_comp_apply]
  refine heq_of_eq (chowPushforwardOfIso_congr_apply C _ _ _ _ ?_ _ _ _ _)
  apply pullback.hom_ext <;> simp [identityTestComparison, transportPullbackIso]

/-- The operation of a class `κ ∈ A^p(X)` on a test scheme, as the operation of the induced
identity cap rule. -/
theorem toIdentityCapRule_eq_idRule {p : ℤ}
    (κ : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p) {T : Scheme.{u}}
    (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sX) k) :
    BivariantClass.toIdentityCapRule C (gysinSystemOfInvertible C) sX p κ t k α =
      κ.idRule C sX (gysinSystemOfInvertible C) t k α :=
  rfl

/-- **Commuting on the test schemes gives commuting products.** If `b ∈ A^q(X)` and
`κ ∈ A^p(X)` satisfy `b ∩ (κ ∩ α) = κ ∩ (b ∩ α)` on every test scheme, read on `X ×_X T`, then
`b · κ = κ · b`, as classes of `A^{q+p}(X)` and `A^{p+q}(X)`. -/
theorem chowCohomologyMulOfInvertible_heq_of_cap_idRule_heq {p q : ℤ}
    (κ : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p)
    (b : chowCohomologyComponent C (gysinSystemOfInvertible C) sX q)
    (H : ∀ {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ)
      (α : chowGroup C (t ≫ sX) k),
      b.cap t (k - p) (κ.idRule C sX (gysinSystemOfInvertible C) t k α) ≍
        κ.idRule C sX (gysinSystemOfInvertible C) (pullback.snd (𝟙 X) t ≫ t) (k - q)
          (chowGroupCongr C (by rw [Category.assoc]; exact
            (pullbackSnd_comp_structureMorphism (Category.id_comp sX) t).symm)
            (k - q) (b.cap t k α))) :
    chowCohomologyMulOfInvertible C sX q p b κ ≍ chowCohomologyMulOfInvertible C sX p q κ b := by
  rw [← chowCohomologyRingMul_gysinSystemOfInvertible,
    ← chowCohomologyRingMul_gysinSystemOfInvertible]
  refine BivariantClass.heq_of_toIdentityCapRule_heq C _ sX (add_comm q p) _ _
    fun {T} t _ k α ↦ ?_
  refine (chowCohomologyMul_toIdentityCapRule_heq C _ sX _ b κ t k α).trans ?_
  refine HEq.trans ?_ (chowCohomologyMul_toIdentityCapRule_heq C _ sX _ κ b t k α).symm
  simp only [toIdentityCapRule_eq_idRule]
  rw [BivariantClass.idRule_apply C sX _ b t (k - p), BivariantClass.idRule_apply C sX _ b t k α]
  have hpush := idRule_chowPush_of_eq C sX κ t (pullback.snd (𝟙 X) t ≫ t) (pullback.snd (𝟙 X) t)
    rfl (pullback.fst (𝟙 X) t ≫ sX) (by rw [Category.assoc]; exact
      pullbackSnd_comp_structureMorphism (Category.id_comp sX) t)
    (pullbackSnd_comp_structureMorphism (Category.id_comp sX) t) (k - q) (b.cap t k α)
  refine HEq.trans ?_ (heq_of_eq hpush).symm
  rw [pullbackSndPush]
  exact properChowPushforward_heq_congr_base C _
    (by
      rw [Category.assoc]
      exact (pullbackSnd_comp_structureMorphism (Category.id_comp sX) t).symm)
    rfl _ _ (by omega) (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ _ _)
    (properPushforwardFactorsThroughRationalEquivalence C _ _ _ _ _) _ _ (H t k α)

/-- Membership in the center of `A^*(X)` is commutation with every homogeneous class. -/
theorem mem_center_of_chowCohomologyMulOfInvertible_heq {p : ℤ}
    (κ : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p)
    (H : ∀ {q : ℤ} (b : chowCohomologyComponent C (gysinSystemOfInvertible C) sX q),
      chowCohomologyMulOfInvertible C sX q p b κ ≍ chowCohomologyMulOfInvertible C sX p q κ b) :
    letI : Ring (chowCohomology C (gysinSystemOfInvertible C) sX) :=
      chowCohomologyRingOfInvertible C sX
    DirectSum.of (fun q : ℤ ↦ chowCohomologyComponent C (gysinSystemOfInvertible C) sX q) p κ ∈
      Subring.center (chowCohomology C (gysinSystemOfInvertible C) sX) := by
  let : DirectSum.GRing fun q : ℤ ↦ chowCohomologyComponent C (gysinSystemOfInvertible C) sX q :=
    chowCohomologyGRingOfInvertible C sX
  let : Ring (chowCohomology C (gysinSystemOfInvertible C) sX) :=
    chowCohomologyRingOfInvertible C sX
  rw [Subring.mem_center_iff]
  intro x
  induction x using DirectSum.induction_on with
  | zero => rw [zero_mul, mul_zero]
  | of q b =>
    rw [DirectSum.of_mul_of, DirectSum.of_mul_of]
    exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.ext (add_comm _ _) (H b))
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]

end General

/-! ### Additivity of the operations on bivariant classes -/

namespace BivariantChowClass

variable {C : ChowSituation.{u}}

/-- Reindexing the degree of bivariant classes along `p = p'` is additive. -/
theorem degreeCongr_add {X Y : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sY : Y ⟶ C.S}
    [LocallyOfFiniteType sY] {f : X ⟶ Y} [LocallyOfFiniteType f] {hf : f ≫ sY = sX} {p p' : ℤ}
    (h : p = p') (a b : BivariantChowClass C sX sY f hf p) :
    (a + b).degreeCongr h = a.degreeCongr h + b.degreeCongr h := by
  subst h
  rfl

/-- Reindexing the degree of the zero bivariant class along `p = p'` gives zero. -/
theorem degreeCongr_zero {X Y : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]
    {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {f : X ⟶ Y} [LocallyOfFiniteType f]
    {hf : f ≫ sY = sX} {p p' : ℤ} (h : p = p') :
    (0 : BivariantChowClass C sX sY f hf p).degreeCongr h = 0 := by
  subst h
  rfl

/-- Transport of bivariant classes along an isomorphism `θ : A ≅ B` of sources is additive. -/
theorem transport_add {A B W : Scheme.{u}} {sA : A ⟶ C.S} [LocallyOfFiniteType sA]
    {sB : B ⟶ C.S} [LocallyOfFiniteType sB] {sW : W ⟶ C.S} [LocallyOfFiniteType sW] {v : A ⟶ W}
    [LocallyOfFiniteType v] {hv : v ≫ sW = sA} {u : B ⟶ W} [LocallyOfFiniteType u] {p : ℤ}
    (hu : u ≫ sW = sB) (θ : A ≅ B) (hθ : θ.hom ≫ u = v) (a b : BivariantChowClass C sA sW v hv p) :
    (a + b).transport hu θ hθ = a.transport hu θ hθ + b.transport hu θ hθ := by
  refine ext fun t _ k α ↦ ?_
  rw [add_cap, Pi.add_apply, transport_cap, transport_cap, transport_cap, add_cap, Pi.add_apply,
    map_add]

/-- Transporting the zero bivariant class along an isomorphism `θ : A ≅ B` gives zero. -/
theorem transport_zero {A B W : Scheme.{u}} {sA : A ⟶ C.S} [LocallyOfFiniteType sA]
    {sB : B ⟶ C.S} [LocallyOfFiniteType sB] {sW : W ⟶ C.S} [LocallyOfFiniteType sW] {v : A ⟶ W}
    [LocallyOfFiniteType v] {hv : v ≫ sW = sA} {u : B ⟶ W} [LocallyOfFiniteType u] {p : ℤ}
    (hu : u ≫ sW = sB) (θ : A ≅ B) (hθ : θ.hom ≫ u = v) :
    (0 : BivariantChowClass C sA sW v hv p).transport hu θ hθ = 0 := by
  refine ext fun t _ k α ↦ ?_
  rw [zero_cap, transport_cap, zero_cap]
  exact map_zero _

/-- Composition of bivariant classes is additive in the first factor:
`(a + a').comp b = a.comp b + a'.comp b`. -/
theorem add_comp {X Y Z : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sY : Y ⟶ C.S}
    [LocallyOfFiniteType sY] {sZ : Z ⟶ C.S} [LocallyOfFiniteType sZ] {f : X ⟶ Y} {g : Y ⟶ Z}
    {hf : f ≫ sY = sX} {hg : g ≫ sZ = sY} [LocallyOfFiniteType f] [LocallyOfFiniteType g]
    {p q : ℤ}
    (a a' : BivariantChowClass C sX sY f hf p) (b : BivariantChowClass C sY sZ g hg q) :
    (a + a').comp b = a.comp b + a'.comp b := by
  refine ext fun t _ k α ↦ ?_
  rw [add_cap, Pi.add_apply, comp_cap, comp_cap, comp_cap, add_cap, Pi.add_apply, map_add,
    map_add]

/-- The composite of the zero bivariant class with any bivariant class `b` is zero. -/
theorem zero_comp {X Y Z : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sY : Y ⟶ C.S}
    [LocallyOfFiniteType sY] {sZ : Z ⟶ C.S} [LocallyOfFiniteType sZ] {f : X ⟶ Y} {g : Y ⟶ Z}
    {hf : f ≫ sY = sX} {hg : g ≫ sZ = sY} [LocallyOfFiniteType f] [LocallyOfFiniteType g]
    {p q : ℤ}
    (b : BivariantChowClass C sY sZ g hg q) :
    (0 : BivariantChowClass C sX sY f hf p).comp b = 0 := by
  refine ext fun t _ k α ↦ ?_
  rw [zero_cap, comp_cap, zero_cap, Pi.zero_apply, map_zero, map_zero]
  rfl

/-- Composition of bivariant classes is additive in the second factor:
`a.comp (b + b') = a.comp b + a.comp b'`. -/
theorem comp_add {X Y Z : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sY : Y ⟶ C.S}
    [LocallyOfFiniteType sY] {sZ : Z ⟶ C.S} [LocallyOfFiniteType sZ] {f : X ⟶ Y} {g : Y ⟶ Z}
    {hf : f ≫ sY = sX} {hg : g ≫ sZ = sY} [LocallyOfFiniteType f] [LocallyOfFiniteType g]
    {p q : ℤ} (a : BivariantChowClass C sX sY f hf p) (b b' : BivariantChowClass C sY sZ g hg q) :
    a.comp (b + b') = a.comp b + a.comp b' := by
  refine ext fun t _ k α ↦ ?_
  rw [add_cap, Pi.add_apply, comp_cap, comp_cap, comp_cap, add_cap, Pi.add_apply, cap_add,
    map_add, map_add]

/-- The composite of any bivariant class `a` with the zero bivariant class is zero. -/
theorem comp_zero {X Y Z : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sY : Y ⟶ C.S}
    [LocallyOfFiniteType sY] {sZ : Z ⟶ C.S} [LocallyOfFiniteType sZ] {f : X ⟶ Y} {g : Y ⟶ Z}
    {hf : f ≫ sY = sX} {hg : g ≫ sZ = sY} [LocallyOfFiniteType f] [LocallyOfFiniteType g]
    {p q : ℤ} (a : BivariantChowClass C sX sY f hf p) :
    a.comp (0 : BivariantChowClass C sY sZ g hg q) = 0 := by
  refine ext fun t _ k α ↦ ?_
  rw [zero_cap, comp_cap, zero_cap, Pi.zero_apply,
    show a.cap _ _ 0 = 0 from map_zero ((equivBivariantClass a).cap _ _), map_zero, map_zero]
  rfl

end BivariantChowClass

/-! ### Total classes commuting with every bivariant class -/

namespace TotalChowClass

variable {C : ChowSituation.{u}} {X : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]
  {X' : Scheme.{u}} {sX' : X' ⟶ C.S} [LocallyOfFiniteType sX']

/-- If a total class `x` of `X` commutes with every bivariant class along `𝟙 X`, then each of its
components `x_n` satisfies `c ∩ (x_n ∩ α) = x_n ∩ (c ∩ α)` for every `c ∈ A^q(X' ⟶ X)`, with the
right side read on `X' ×_X T` as a test scheme over `X` through `X'`. -/
theorem cap_idRule_heq_of_commutesWith (x : TotalChowClass C sX)
    (hx : ∀ {X₁ : Scheme.{u}} (g₁ : X₁ ⟶ X) [LocallyOfFiniteType g₁] {q : ℤ}
      (c : BivariantClass C (gysinSystemOfInvertible C) (g₁ ≫ sX) sX g₁ rfl q),
      x.CommutesWith C sX g₁ c (𝟙 X) sX (Category.id_comp sX))
    (n : ℕ) (g : X' ⟶ X) (hg : g ≫ sX = sX') {q : ℤ} (c : BivariantChowClass C sX' sX g hg q)
    {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sX) k)
    {W : Scheme.{u}} (w : W ⟶ X) [LocallyOfFiniteType w] (hw : pullback g t = W)
    (hwt : pullback.snd g t ≫ t ≍ w)
    (β : chowGroup C (w ≫ sX) (k - q)) (hβ : β ≍ c.cap t k α) :
    c.cap t (k - n) ((x n).idRule C sX (gysinSystemOfInvertible C) t k α) ≍
      (x n).idRule C sX (gysinSystemOfInvertible C) w (k - q) β := by
  subst hg hw
  obtain rfl := eq_of_heq hwt
  have := BivariantChowClass.locallyOfFiniteType_of_structure sX g rfl
  set c' := BivariantChowClass.equivBivariantClass c
  have H := (commutesWith_iff C sX g c' (𝟙 X) sX (Category.id_comp sX) x).1 (hx g c') t n k α
  have e : t ≫ 𝟙 X = t := Category.comp_id t
  have hcap : ∀ (j : ℤ) (γ : chowGroup C (t ≫ sX) j),
      capAlong C sX g c' (𝟙 X) sX (Category.id_comp sX) t j γ ≍ c.cap t j γ := fun j γ ↦
    (capAlong_heq C sX g c' (𝟙 X) sX _ t j γ (chowGroupCongr C (by rw [e]) j γ)
      (chowGroupCongr_heq C _ _ _).symm).trans
      (cap_heq_of_eq c' e j (chowGroupCongr_heq C _ _ _))
  refine HEq.trans (hcap (k - n) _).symm (HEq.trans H ?_)
  exact op_snd_heq_of_eq x e t (k - q) n ((hcap k α).trans hβ.symm)

end TotalChowClass

/-! ### Centrality of the Chern classes of a perfect object -/

section Statement

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  {X' : Scheme.{u}} {sX' : X' ⟶ C.S} [LocallyOfFiniteType sX'] {E : DerivedCategory X.Modules}

/-- The Chern class `c(E)` of an object whose Chern classes are defined commutes with every
bivariant class along `𝟙 X`. -/
theorem commutesWith_perfectChernClass_id (hE : HasDefinedChernClasses E) {X₁ : Scheme.{u}}
    (g₁ : X₁ ⟶ X) [LocallyOfFiniteType g₁] {q : ℤ}
    (c : BivariantClass C (gysinSystemOfInvertible C) (g₁ ≫ sX) sX g₁ rfl q) :
    (perfectChernClass C sX hE).CommutesWith C sX g₁ c (𝟙 X) sX (Category.id_comp sX) :=
  TotalChowClass.commutesWith_perfectChernClass C sX g₁ c (𝟙 X) sX (Category.id_comp sX) hE

/-- The classes `P_p(E)` of a perfect object whose Chern classes are defined commute with every
bivariant class along `𝟙 X`. -/
theorem commutesWith_perfectPowerSumTotal_id
    (perfect : RingedSpace.IsPerfect.{u, u + 1} (X := X.toRingedSpace) E)
    (hE : HasDefinedChernClasses E) {X₁ : Scheme.{u}} (g₁ : X₁ ⟶ X) [LocallyOfFiniteType g₁]
    {q : ℤ} (c : BivariantClass C (gysinSystemOfInvertible C) (g₁ ≫ sX) sX g₁ rfl q) :
    (perfectPowerSumTotal C sX hE).CommutesWith C sX g₁ c (𝟙 X) sX
      (Category.id_comp sX) :=
  TotalChowClass.commutesWith_perfectPowerSumTotal C sX g₁ c (𝟙 X) sX (Category.id_comp sX)
    perfect hE

/-- A component `x_n` of a total class commuting with all bivariant classes along `𝟙 X` commutes
with `c ∈ A^q(X' ⟶ X)` as soon as a class `κ'` of `X'` has the operation of `x_n` on `X'`-test
schemes. -/
private theorem comp_eq_of_commutesWith_of_idRule_heq (x : TotalChowClass C sX)
    (hx : ∀ {X₁ : Scheme.{u}} (g₁ : X₁ ⟶ X) [LocallyOfFiniteType g₁] {q : ℤ}
      (c : BivariantClass C (gysinSystemOfInvertible C) (g₁ ≫ sX) sX g₁ rfl q),
      x.CommutesWith C sX g₁ c (𝟙 X) sX (Category.id_comp sX))
    (n : ℕ) (κ' : chowCohomologyComponent C (gysinSystemOfInvertible C) sX' n) (g : X' ⟶ X)
    [LocallyOfFiniteType g] (hg : g ≫ sX = sX') {q : ℤ} (c : BivariantChowClass C sX' sX g hg q)
    (hκ : ∀ {V : Scheme.{u}} (v : V ⟶ X') [LocallyOfFiniteType v] (k : ℤ)
      (α : chowGroup C (v ≫ sX') k) (α' : chowGroup C ((v ≫ g) ≫ sX) k), α ≍ α' →
      κ'.idRule C sX' (gysinSystemOfInvertible C) v k α ≍
        (x n).idRule C sX (gysinSystemOfInvertible C) (v ≫ g) k α') :
    c.comp (BivariantChowClass.equivBivariantClass.symm (x n)) =
      (((BivariantChowClass.equivBivariantClass.symm κ').comp c).degreeCongr
        (add_comm (n : ℤ) q)).transport
        (comp_comp_structureMorphism_eq hg (Category.id_comp sX)) (Iso.refl X') (by simp) := by
  refine comp_eq_of_cap_idRule_heq _ _ g hg c fun {T} t _ k α ↦ ?_
  have hβ : pullback.fst g t ≫ sX' = (pullback.fst g t ≫ g) ≫ sX := by
    rw [Category.assoc, hg]
  exact (TotalChowClass.cap_idRule_heq_of_commutesWith x hx n g hg c t k α
    (pullback.fst g t ≫ g) rfl (heq_of_eq pullback.condition.symm)
    (chowGroupCongr C hβ (k - q) (c.cap t k α)) (chowGroupCongr_heq C _ _ _)).trans
    (hκ (pullback.fst g t) (k - q) _ _ (chowGroupCongr_heq C _ _ _).symm).symm

/-- A component `x_n` of a total class commuting with all bivariant classes along `𝟙 X` is in the
center of the Chow cohomology ring. -/
private theorem of_mem_center_of_commutesWith (x : TotalChowClass C sX)
    (hx : ∀ {X₁ : Scheme.{u}} (g₁ : X₁ ⟶ X) [LocallyOfFiniteType g₁] {q : ℤ}
      (c : BivariantClass C (gysinSystemOfInvertible C) (g₁ ≫ sX) sX g₁ rfl q),
      x.CommutesWith C sX g₁ c (𝟙 X) sX (Category.id_comp sX))
    (n : ℕ) :
    letI : Ring (chowCohomology C (gysinSystemOfInvertible C) sX) :=
      chowCohomologyRingOfInvertible C sX
    DirectSum.of (fun q : ℤ ↦ chowCohomologyComponent C (gysinSystemOfInvertible C) sX q)
        (n : ℤ) (x n) ∈ Subring.center (chowCohomology C (gysinSystemOfInvertible C) sX) := by
  refine mem_center_of_chowCohomologyMulOfInvertible_heq _ fun {q} b ↦ ?_
  refine chowCohomologyMulOfInvertible_heq_of_cap_idRule_heq _ b fun {T} t _ k α ↦ ?_
  exact TotalChowClass.cap_idRule_heq_of_commutesWith x hx n (𝟙 X) (Category.id_comp sX)
    (BivariantChowClass.equivBivariantClass.symm b) t k α _ rfl HEq.rfl _
    (chowGroupCongr_heq C _ _ _)

/-- Let `E ∈ D(𝒪_X)` be perfect with defined Chern classes, let `g : X' ⟶ X` be locally of finite
type and let `c ∈ A^q(X' ⟶ X)` be a bivariant class. Then

  `c ∘ c_p(E) = c_p(Lg^*E) ∘ c`   in   `A^{q+p}(X' ⟶ X)`,

with `c_p(E) ∈ A^p(X)` and `c_p(Lg^*E) ∈ A^p(X')`. The left side is a class for `g ≫ 𝟙 X` of
degree `q + p`; the right side, a class for `𝟙 X' ≫ g` of degree `p + q`, is read as one for
`g ≫ 𝟙 X` of degree `q + p` along the identity of `X'`. -/
@[stacks 0FAC "(2): c ∘ c_p(E) = c_p(Lg^*E) ∘ c in A^*(X' → X) for every g : X' → X locally of \
finite type and every bivariant class c in A^q(X' → X) of Stacks 0B76"]
theorem comp_perfectChernClass
    (_perfect : RingedSpace.IsPerfect.{u, u + 1} (X := X.toRingedSpace) E)
    (hE : HasDefinedChernClasses E) (p : ℕ) (g : X' ⟶ X) (hg : g ≫ sX = sX') {q : ℤ}
    (c : BivariantChowClass C sX' sX g hg q) :
    c.comp (BivariantChowClass.equivBivariantClass.symm (perfectChernClass C sX hE p)) =
      (((BivariantChowClass.equivBivariantClass.symm
          (perfectChernClass C sX' (hasDefinedChernClasses_derivedPullback g hE)
            p)).comp c).degreeCongr (add_comm (p : ℤ) q)).transport
        (comp_comp_structureMorphism_eq hg (Category.id_comp sX)) (Iso.refl X') (by simp) := by
  have := BivariantChowClass.locallyOfFiniteType_of_structure sX g hg
  exact comp_eq_of_commutesWith_of_idRule_heq C sX (perfectChernClass C sX hE)
    (commutesWith_perfectChernClass_id C sX hE) p _ g hg c fun v _ k α α' hα ↦
    idRule_perfectChernClass_derivedPullback_heq C sX sX' g hg hE _ p v k α α' hα

/-- Let `E ∈ D(𝒪_X)` be perfect with defined Chern classes. Then `c_p(E) ∈ A^p(X)` lies in the
center of the Chow cohomology ring `A^*(X)`. -/
@[stacks 0FAC "(1): c_p(E) is in the center of the Chow cohomology ring A^*(X) of Stacks 0B7E"]
theorem perfectChernClass_mem_center
    (_perfect : RingedSpace.IsPerfect.{u, u + 1} (X := X.toRingedSpace) E)
    (hE : HasDefinedChernClasses E) (p : ℕ) :
    letI : Ring (chowCohomology C (gysinSystemOfInvertible C) sX) :=
      chowCohomologyRingOfInvertible C sX
    DirectSum.of (fun q : ℤ ↦ chowCohomologyComponent C (gysinSystemOfInvertible C) sX q)
        (p : ℤ) (perfectChernClass C sX hE p) ∈
      Subring.center (chowCohomology C (gysinSystemOfInvertible C) sX) :=
  of_mem_center_of_commutesWith C sX _ (commutesWith_perfectChernClass_id C sX hE) p

/-- Let `E ∈ D(𝒪_X)` be perfect with defined Chern classes, let `g : X' ⟶ X` be locally of finite
type and let `c ∈ A^q(X' ⟶ X)`. Then `c ∘ P_p(E) = P_p(Lg^*E) ∘ c` in `A^{q+p}(X' ⟶ X)`, the
composites being read as in `Stacks.Chow.comp_perfectChernClass`. -/
theorem comp_perfectPowerSumComponent
    (perfect : RingedSpace.IsPerfect.{u, u + 1} (X := X.toRingedSpace) E)
    (hE : HasDefinedChernClasses E) (p : ℕ) (g : X' ⟶ X) (hg : g ≫ sX = sX') {q : ℤ}
    (c : BivariantChowClass C sX' sX g hg q) :
    c.comp (BivariantChowClass.equivBivariantClass.symm
        (perfectPowerSumComponent C sX hE p)) =
      (((BivariantChowClass.equivBivariantClass.symm
          (perfectPowerSumComponent C sX'
            (hasDefinedChernClasses_derivedPullback g hE) p)).comp c).degreeCongr
        (add_comm (p : ℤ) q)).transport
        (comp_comp_structureMorphism_eq hg (Category.id_comp sX)) (Iso.refl X') (by simp) := by
  have := BivariantChowClass.locallyOfFiniteType_of_structure sX g hg
  exact comp_eq_of_commutesWith_of_idRule_heq C sX (perfectPowerSumTotal C sX hE)
    (commutesWith_perfectPowerSumTotal_id C sX perfect hE) p _ g hg c fun v _ k α α' hα ↦
    idRule_perfectPowerSumComponent_derivedPullback_heq C sX sX' g hg perfect hE _ p v k α α' hα

/-- Let `E ∈ D(𝒪_X)` be perfect with defined Chern classes. Then `P_p(E) ∈ A^p(X)` lies in the
center of the Chow cohomology ring `A^*(X)`. -/
theorem perfectPowerSumComponent_mem_center
    (perfect : RingedSpace.IsPerfect.{u, u + 1} (X := X.toRingedSpace) E)
    (hE : HasDefinedChernClasses E) (p : ℕ) :
    letI : Ring (chowCohomology C (gysinSystemOfInvertible C) sX) :=
      chowCohomologyRingOfInvertible C sX
    DirectSum.of (fun q : ℤ ↦ chowCohomologyComponent C (gysinSystemOfInvertible C) sX q)
        (p : ℤ) (perfectPowerSumComponent C sX hE p) ∈
      Subring.center (chowCohomology C (gysinSystemOfInvertible C) sX) := by
  exact of_mem_center_of_commutesWith C sX _ (commutesWith_perfectPowerSumTotal_id C sX perfect hE)
    p

/-! ### The Chern character -/

variable {C sX} in
/-- The composite `κ ↦ c ∘ κ` of a bivariant class `c ∈ A^q(X' ⟶ X)` with the classes of
`A^p(X)`, as a homomorphism of groups to `A^{q+p}(X' ⟶ X)`. -/
def BivariantChowClass.compRightHom (g : X' ⟶ X) [LocallyOfFiniteType g] (hg : g ≫ sX = sX')
    {q : ℤ}
    (c : BivariantChowClass C sX' sX g hg q) (p : ℤ) :
    chowCohomologyComponent C (gysinSystemOfInvertible C) sX p →+
      BivariantChowClass C sX' sX (g ≫ 𝟙 X) (comp_comp_structureMorphism_eq hg
        (Category.id_comp sX)) (q + p) where
  toFun κ := c.comp (BivariantChowClass.equivBivariantClass.symm κ)
  map_zero' := by
    rw [show BivariantChowClass.equivBivariantClass.symm (0 : chowCohomologyComponent C
      (gysinSystemOfInvertible C) sX p) = 0 from rfl, BivariantChowClass.comp_zero]
  map_add' κ κ' := by
    rw [show BivariantChowClass.equivBivariantClass.symm (κ + κ') =
      BivariantChowClass.equivBivariantClass.symm κ +
        BivariantChowClass.equivBivariantClass.symm κ' from rfl, BivariantChowClass.comp_add]

variable {C sX} in
/-- The composite `κ' ↦ κ' ∘ c` of the classes of `A^p(X')` with a bivariant class
`c ∈ A^q(X' ⟶ X)`, read in `A^{q+p}(X' ⟶ X)` as in `Stacks.Chow.comp_perfectChernClass`, as a
homomorphism of groups. -/
def BivariantChowClass.compLeftHom (g : X' ⟶ X) [LocallyOfFiniteType g] (hg : g ≫ sX = sX')
    {q : ℤ}
    (c : BivariantChowClass C sX' sX g hg q) (p : ℤ) :
    chowCohomologyComponent C (gysinSystemOfInvertible C) sX' p →+
      BivariantChowClass C sX' sX (g ≫ 𝟙 X) (comp_comp_structureMorphism_eq hg
        (Category.id_comp sX)) (q + p) where
  toFun κ' := (((BivariantChowClass.equivBivariantClass.symm κ').comp c).degreeCongr
    (add_comm p q)).transport (comp_comp_structureMorphism_eq hg (Category.id_comp sX))
    (Iso.refl X') (by simp)
  map_zero' := by
    rw [show BivariantChowClass.equivBivariantClass.symm (0 : chowCohomologyComponent C
      (gysinSystemOfInvertible C) sX' p) = 0 from rfl, BivariantChowClass.zero_comp,
      BivariantChowClass.degreeCongr_zero, BivariantChowClass.transport_zero]
  map_add' κ κ' := by
    rw [show BivariantChowClass.equivBivariantClass.symm (κ + κ') =
      BivariantChowClass.equivBivariantClass.symm κ +
        BivariantChowClass.equivBivariantClass.symm κ' from rfl, BivariantChowClass.add_comp,
      BivariantChowClass.degreeCongr_add, BivariantChowClass.transport_add]

/-- Let `E ∈ D(𝒪_X)` be perfect with defined Chern classes, let `g : X' ⟶ X` be locally of finite
type and let `c ∈ A^q(X' ⟶ X)`. Then `c ∘ ch_p(E) = ch_p(Lg^*E) ∘ c` in `A^{q+p}(X' ⟶ X) ⊗ 𝐐`, the
composites with a rational class being the rational extensions of those of
`Stacks.Chow.comp_perfectChernClass`. -/
theorem comp_perfectChernCharacterComponent
    (perfect : RingedSpace.IsPerfect.{u, u + 1} (X := X.toRingedSpace) E)
    (hE : HasDefinedChernClasses E) (p : ℕ) (g : X' ⟶ X) [LocallyOfFiniteType g]
    (hg : g ≫ sX = sX') {q : ℤ} (c : BivariantChowClass C sX' sX g hg q) :
    LinearMap.lTensor ℚ (c.compRightHom g hg (p : ℤ)).toIntLinearMap
        (perfectChernCharacterComponent C sX hE p) =
      LinearMap.lTensor ℚ (c.compLeftHom g hg (p : ℤ)).toIntLinearMap
        (perfectChernCharacterComponent C sX'
          (hasDefinedChernClasses_derivedPullback g hE) p) := by
  simp only [perfectChernCharacterComponent, LinearMap.lTensor_tmul]
  congr 1
  exact comp_perfectPowerSumComponent C sX perfect hE p g hg c

/-- Let `E ∈ D(𝒪_X)` be perfect with defined Chern classes. Then `ch_p(E) ∈ A^p(X) ⊗ 𝐐` lies in
the center of the algebra `A^*(X) ⊗ 𝐐`. -/
theorem perfectChernCharacterComponent_mem_center
    (perfect : RingedSpace.IsPerfect.{u, u + 1} (X := X.toRingedSpace) E)
    (hE : HasDefinedChernClasses E) (p : ℕ) :
    letI : Ring (chowCohomology C (gysinSystemOfInvertible C) sX) :=
      chowCohomologyRingOfInvertible C sX
    LinearMap.lTensor ℚ (DirectSum.lof ℤ ℤ
        (fun q : ℤ ↦ chowCohomologyComponent C (gysinSystemOfInvertible C) sX q) (p : ℤ))
        (perfectChernCharacterComponent C sX hE p) ∈
      Subring.center (TensorProduct ℤ ℚ (chowCohomology C (gysinSystemOfInvertible C) sX)) := by
  let : Ring (chowCohomology C (gysinSystemOfInvertible C) sX) :=
    chowCohomologyRingOfInvertible C sX
  have hP := perfectPowerSumComponent_mem_center C sX perfect hE p
  simp only [perfectChernCharacterComponent, LinearMap.lTensor_tmul]
  rw [Subring.mem_center_iff]
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul r a =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_comm r,
      DirectSum.lof_eq_of, Subring.mem_center_iff.1 hP a]
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]

end Statement

end Stacks.Chow

end
