module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TotalClassCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.BabyLocalizedChern.CompositeCaps
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.PointClassCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Vanishing
public import StacksFrontier.AlgebraicGeometry.Chow.ChowGroupsEnvelopes.BirationalModification

/-!
# Commuting with a bivariant class is checked on integral test schemes

Let `c ∈ A^q(X' ⟶ X)`, let `h : Y ⟶ X` and let `x` be a total Chow cohomology class of `Y`.
For each index `p` the difference of the two composites

  `res(c) ∘ x_p - x_p|_{X' ×_X Y} ∘ res(c)   ∈   A^{q+p}(X' ×_X Y ⟶ Y)`,

with `res(c)` the restriction of `c` along `h` (Remark 0F9Z), is a bivariant class, and `x`
commutes with `c` along `h` exactly when all these classes vanish. By Stacks 02UC a bivariant
class vanishes as soon as it kills the fundamental class of a proper birational modification of
every integral test scheme. This gives two descent statements:

* along an envelope `Y₁ ⟶ Y` (Stacks 0GUF provides the modifications), and
* along a decomposition of `Y` into open and closed subschemes (an integral test scheme maps to
  one piece).

## Main results

* `Stacks.Chow.TotalChowClass.commutator_cap_eq_zero_iff` — the difference of the composites
  kills `α` exactly when `c ∩ (x_p ∩ α) = x_p ∩ (c ∩ α)`.
* `Stacks.Chow.TotalChowClass.CommutesWith.of_isEnvelope` — descent along an envelope.
* `Stacks.Chow.TotalChowClass.CommutesWith.of_isClopenDecomposition` — gluing over a
  decomposition into open and closed subschemes.

## References

* [Stacks Project, Tag 0FAC](https://stacks.math.columbia.edu/tag/0FAC)
* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
* [Stacks Project, Tag 0GUF](https://stacks.math.columbia.edu/tag/0GUF)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

namespace TotalChowClass

variable (C : ChowSituation.{u}) {X X' Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (g : X' ⟶ X) [LocallyOfFiniteType g] {q : ℤ}
  (c : BivariantClass C (gysinSystemOfInvertible C) (g ≫ sX) sX g rfl q)
  (h : Y ⟶ X) [LocallyOfFiniteType h] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (hY : h ≫ sX = sY)

/-! ### Commuting, one index at a time -/

/-- `c ∩ (κ ∩ α) = κ ∩ (c ∩ α)` for one class `κ ∈ A^p(Y)`, one test scheme `m : W ⟶ Y` and one
`α ∈ A_k(W)`, the two sides compared in `A_{k-p-q} = A_{k-q-p}` of `X' ×_X W`. -/
def ComponentCommutesAt {p : ℤ} (κ : chowCohomologyComponent C (gysinSystemOfInvertible C) sY p)
    {W : Scheme.{u}} (m : W ⟶ Y) [LocallyOfFiniteType m] (k : ℤ) (α : chowGroup C (m ≫ sY) k) :
    Prop :=
  capAlong C sX g c h sY hY m (k - p) (κ.idRule C sY (gysinSystemOfInvertible C) m k α) ≍
    κ.idRule C sY (gysinSystemOfInvertible C) (pullback.snd g (m ≫ h) ≫ m) (k - q)
      (capAlong C sX g c h sY hY m k α)

/-- A total class commutes with `c` exactly when each of its components does on every test
scheme and every class. -/
theorem commutesWith_iff (x : TotalChowClass C sY) :
    x.CommutesWith C sX g c h sY hY ↔
      ∀ {W : Scheme.{u}} (m : W ⟶ Y) [LocallyOfFiniteType m] (n : ℕ) (k : ℤ)
        (α : chowGroup C (m ≫ sY) k), ComponentCommutesAt C sX g c h sY hY (x n) m k α :=
  ⟨fun hx _ m _ n k α ↦ (hx m).heq k n α,
    fun hx _ m _ ↦ GradedCapFamily.Intertwines.iff_heq.2 fun k n α ↦ hx m n k α⟩

/-! ### The restriction of `c` to `Y` -/

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType g] [LocallyOfFiniteType h]
  [LocallyOfFiniteType sY] in
include hY in
/-- The two structure morphisms `X' ×_X Y ⟶ S`, through `X'` and through `Y`, agree. -/
theorem restrictionAlong_source_eq :
    pullback.fst g h ≫ (g ≫ sX) = pullback.snd g h ≫ sY := by
  rw [← hY, ← Category.assoc, pullback.condition, Category.assoc]

/-- The restriction `res(c) ∈ A^q(X' ×_X Y ⟶ Y)` of `c` along `h` (Remark 0F9Z), read with the
structure morphisms `X' ×_X Y ⟶ Y ⟶ S` and `sY`. -/
def restrictionAlong :
    BivariantClass C (gysinSystemOfInvertible C) (pullback.snd g h ≫ sY) sY (pullback.snd g h)
      rfl q :=
  bivariantClassCongrBase C (gysinSystemOfInvertible C) (pullback.snd g h)
    (restrictionAlong_source_eq C sX g h sY hY) hY q
    (bivariantRestriction C (gysinSystemOfInvertible C) (g ≫ sX) sX g rfl h q
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c)

/-- The cap operation of `res(c)` at `m : W ⟶ Y` is that of `c` at `W ⟶ Y ⟶ X`, read through the
canonical isomorphism `(X' ×_X Y) ×_Y W ≅ X' ×_X W`. -/
theorem restrictionAlong_cap_heq {W : Scheme.{u}} (m : W ⟶ Y) [LocallyOfFiniteType m] (k : ℤ)
    (β : chowGroup C (m ≫ sY) k) :
    (restrictionAlong C sX g c h sY hY).cap m k β ≍
      chowPushforwardOfIso C (pullback.fst g (m ≫ h) ≫ (g ≫ sX))
        (pullback.fst (pullback.snd g h) m ≫ (pullback.fst g h ≫ (g ≫ sX)))
        (pullbackLeftPullbackSndIso g h m).inv (by simp) (k - q)
        (c.cap (m ≫ h) k (chowGroupCongr C (comp_structure_eq C sX h sY hY m) k β)) := by
  have hβ₀ : m ≫ sY = m ≫ (h ≫ sX) := by rw [hY]
  refine (bivariantClassCongrBase_cap C (gysinSystemOfInvertible C) (pullback.snd g h)
    (restrictionAlong_source_eq C sX g h sY hY) hY q _ m k (chowGroupCongr C hβ₀ k β) β
    (chowGroupCongr_heq C hβ₀ k β)).trans ?_
  rw [bivariantRestriction_cap, bivariantRestrictionCap_apply]
  refine heq_of_eq (congrArg _ (congrArg _ (eq_of_heq ?_)))
  exact (chowGroupCongr_heq C _ k _).trans ((chowGroupCongr_heq C hβ₀ k β).trans
    (chowGroupCongr_heq C _ k β).symm)

/-! ### The difference of the two composites -/

/-- **The difference of the two composites** `res(c) ∘ κ - κ|_{X' ×_X Y} ∘ res(c)` in
`A^{q+p}(X' ×_X Y ⟶ Y)`, for `κ ∈ A^p(Y)`. -/
def commutator {p : ℤ} (κ : chowCohomologyComponent C (gysinSystemOfInvertible C) sY p) :
    BivariantClass C (gysinSystemOfInvertible C) (pullback.snd g h ≫ sY) sY (pullback.snd g h)
      rfl (q + p) :=
  bivariantCompositeIdRightHom C (gysinSystemOfInvertible C) sY (pullback.snd g h)
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
      (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C) p q
      (restrictionAlong C sX g c h sY hY) κ -
    bivariantCompositeIdLeftHom C (gysinSystemOfInvertible C) sY (pullback.snd g h)
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
      (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C) p q
      (restrictionAlong C sX g c h sY hY)
      (chowCohomologyRestriction C (gysinSystemOfInvertible C) sY (pullback.snd g h) p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) κ)

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType g] [LocallyOfFiniteType h] in
/-- The canonical isomorphism `X' ×_X W ≅ (X' ×_X Y) ×_Y W` followed by the projection to
`X' ×_X Y` and then to `Y` is the composite `X' ×_X W ⟶ W ⟶ Y`. -/
theorem pullbackLeftPullbackSndIso_inv_comp_test {W : Scheme.{u}} (m : W ⟶ Y) :
    (pullbackLeftPullbackSndIso g h m).inv ≫
        (pullback.fst (pullback.snd g h) m ≫ pullback.snd g h) =
      pullback.snd g (m ≫ h) ≫ m := by
  simp

/-- **The difference of the composites kills `α` exactly when `c ∩ (κ ∩ α) = κ ∩ (c ∩ α)`.**
Both composites cap at `m : W ⟶ Y` to the pushforward along the canonical isomorphism
`X' ×_X W ≅ (X' ×_X Y) ×_Y W` of the two sides of the identity, the second by the projection
formula for `κ`. -/
theorem commutator_cap_eq_zero_iff {p : ℤ}
    (κ : chowCohomologyComponent C (gysinSystemOfInvertible C) sY p) {W : Scheme.{u}}
    (m : W ⟶ Y) [LocallyOfFiniteType m] (k : ℤ) (α : chowGroup C (m ≫ sY) k) :
    (commutator C sX g c h sY hY κ).cap m k α = 0 ↔
      ComponentCommutesAt C sX g c h sY hY κ m k α := by
  set w := pullbackLeftPullbackSndIso g h m
  set n := pullback.fst (pullback.snd g h) m ≫ pullback.snd g h
  set t' := pullback.snd g (m ≫ h) ≫ m
  have hwt : w.inv ≫ n = t' := pullbackLeftPullbackSndIso_inv_comp_test g h m
  set sB := pullback.fst (pullback.snd g h) m ≫ (pullback.snd g h ≫ sY)
  have hΨ : w.inv ≫ sB = t' ≫ sY := by
    rw [← hwt]
    simp only [sB, n, Category.assoc]
  set Ψ := chowPushforwardOfIso C (t' ≫ sY) sB w.inv hΨ (k - (q + p))
  set L := chowGroupDegreeEquiv C (t' ≫ sY) (by ring : k - p - q = k - (q + p))
    (capAlong C sX g c h sY hY m (k - p) (κ.idRule C sY (gysinSystemOfInvertible C) m k α))
  set R := chowGroupDegreeEquiv C (t' ≫ sY) (by ring : k - q - p = k - (q + p))
    (κ.idRule C sY (gysinSystemOfInvertible C) t' (k - q) (capAlong C sX g c h sY hY m k α))
  have hsA : pullback.fst g (m ≫ h) ≫ (g ≫ sX) = t' ≫ sY := testStructure_eq C sX g h sY hY m
  have hsB : pullback.fst (pullback.snd g h) m ≫ (pullback.fst g h ≫ (g ≫ sX)) = sB := by
    simp only [sB, restrictionAlong_source_eq C sX g h sY hY]
  have h₁ : (bivariantCompositeIdRightHom C (gysinSystemOfInvertible C) sY (pullback.snd g h)
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
      (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C) p q
      (restrictionAlong C sX g c h sY hY) κ).cap m k α = Ψ L := by
    refine eq_of_heq ((bivariantCompositeIdRightHom_cap_heq_idRule C _ sY _ _ _ p q _ κ m k
      α).trans ((restrictionAlong_cap_heq C sX g c h sY hY m (k - p) _).trans ?_))
    refine chowPushforwardOfIso_heq w.inv _ _ hsA hsB (by ring) ?_
    refine HEq.symm ((chowGroupDegreeEquiv_heq C _ _ _).trans ?_)
    exact capAlong_heq C sX g c h sY hY m (k - p) _ _ (chowGroupCongr_heq C _ _ _).symm
  have hpush : chowGroupCongr C (by simp only [n, Category.assoc]) (k - q)
      ((restrictionAlong C sX g c h sY hY).cap m k α) =
      chowPushforwardOfIso C (t' ≫ sY) (n ≫ sY) w.inv (by rw [← Category.assoc, hwt]) (k - q)
        (capAlong C sX g c h sY hY m k α) := by
    refine eq_of_heq ((chowGroupCongr_heq C _ _ _).trans
      ((restrictionAlong_cap_heq C sX g c h sY hY m k α).trans ?_))
    refine chowPushforwardOfIso_heq w.inv _ _ hsA
      (by simp only [n, hsB, sB, Category.assoc]) rfl ?_
    exact (capAlong_heq C sX g c h sY hY m k α _ (chowGroupCongr_heq C _ _ _).symm).symm
  have h₂ : (bivariantCompositeIdLeftHom C (gysinSystemOfInvertible C) sY (pullback.snd g h)
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
      (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C) p q
      (restrictionAlong C sX g c h sY hY)
      (chowCohomologyRestriction C (gysinSystemOfInvertible C) sY (pullback.snd g h) p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) κ)).cap m k α = Ψ R := by
    refine eq_of_heq ((bivariantCompositeIdLeftHom_cap_heq_idRule C _ sY _ _ _ p q _ _ m k
      α).trans ?_)
    refine (BivariantClass.idRule_chowCohomologyRestriction_heq (pullback.snd g h) κ
      (pullback.fst (pullback.snd g h) m) (k - q) _ _
      (chowGroupCongr_heq C (by simp only [Category.assoc]) (k - q) _).symm).trans ?_
    rw [hpush]
    have key := idRule_chowPush_of_eq C sY κ n t' w.inv hwt (t' ≫ sY) rfl
      (by rw [← Category.assoc, hwt]) (k - q) (capAlong C sX g c h sY hY m k α)
    refine (heq_of_eq key).trans ?_
    refine chowPushforwardOfIso_heq w.inv _ _ rfl (by simp only [n, sB, Category.assoc])
      (by ring) ?_
    exact (chowGroupDegreeEquiv_heq C _ _ _).symm
  have hinj := chowPushforwardOfIso_injective C (t' ≫ sY) sB w.inv hΨ (k - (q + p))
  rw [commutator, BivariantClass.sub_cap, h₁, h₂, sub_eq_zero]
  refine ⟨fun hLR ↦ ?_, fun hc ↦ ?_⟩
  · exact (chowGroupDegreeEquiv_heq C _ _ _).symm.trans
      ((heq_of_eq (hinj hLR)).trans (chowGroupDegreeEquiv_heq C _ _ _))
  · exact congrArg Ψ (eq_of_heq ((chowGroupDegreeEquiv_heq C _ _ _).trans
      (hc.trans (chowGroupDegreeEquiv_heq C _ _ _).symm)))

/-! ### Descent -/

namespace CommutesWith

variable {C sX g c h sY hY}

/-- A total class commutes with `c` as soon as all the differences of composites vanish. -/
theorem of_commutator_eq_zero {x : TotalChowClass C sY}
    (hx : ∀ n : ℕ, commutator C sX g c h sY hY (x n) = 0) :
    x.CommutesWith C sX g c h sY hY :=
  (commutesWith_iff C sX g c h sY hY x).2 fun m _ n k α ↦
    (commutator_cap_eq_zero_iff C sX g c h sY hY (x n) m k α).1 (by
      rw [hx n, BivariantClass.zero_cap])

/-- **Descent along an envelope.** If `f₁ : Y₁ ⟶ Y` is an envelope and the restriction of `x`
to `Y₁` commutes with `c` along `f₁ ≫ h`, then `x` commutes with `c` along `h`. Every integral
test scheme of `Y` has a proper birational modification factoring through `f₁` (Stacks 0GUF),
whose fundamental class is then killed by each difference of composites; Stacks 02UC concludes. -/
theorem of_isEnvelope {Y₁ : Scheme.{u}} (f₁ : Y₁ ⟶ Y) [LocallyOfFiniteType f₁]
    (hf₁ : IsEnvelope f₁) (sY₁ : Y₁ ⟶ C.S) [LocallyOfFiniteType sY₁] (hs : f₁ ≫ sY = sY₁)
    {x : TotalChowClass C sY}
    (hx : (res f₁ hs x).CommutesWith C sX g c (f₁ ≫ h) sY₁ (by rw [Category.assoc, hY, hs])) :
    x.CommutesWith C sX g c h sY hY := by
  refine of_commutator_eq_zero fun n ↦ ?_
  refine BivariantClass.eq_zero_of_capsIntegralFundamentalClassesToZero C _ _ _ _ _ _
    (BivariantClass.capsIntegralFundamentalClassesToZero_of_hasBirationalModification C _ _ _ _ _
      _ ?_)
  intro T t _ _
  obtain ⟨T', b, a, _, hb, hbir, hfac⟩ := hf₁.exists_properBirational_modification t
  have := hb
  have : LocallyOfFiniteType (a ≫ f₁) := by
    rw [← hfac]
    infer_instance
  have : LocallyOfFiniteType a := locallyOfFiniteType_of_comp a f₁
  refine ⟨T', b, hb, hbir, fun k ↦ ?_⟩
  rw [commutator_cap_eq_zero_iff]
  exact (intertwines_of_res c hY f₁ sY₁ hs x hx a (b ≫ t) hfac.symm).heq k n _

/-- **Gluing over a decomposition into open and closed subschemes.** If the restriction of `x` to
each piece `U_i` of a decomposition of `Y` commutes with `c` along `U_i ⟶ Y ⟶ X`, then `x`
commutes with `c` along `h`: an integral test scheme maps into a single piece. -/
theorem of_isClopenDecomposition {I : Type*} {U : I → Y.Opens} (hU : IsClopenDecomposition U)
    {x : TotalChowClass C sY}
    (hx : ∀ i, (res (U i).ι rfl x).CommutesWith C sX g c ((U i).ι ≫ h) ((U i).ι ≫ sY)
      (by rw [Category.assoc, hY])) :
    x.CommutesWith C sX g c h sY hY := by
  refine of_commutator_eq_zero fun n ↦ ?_
  refine BivariantClass.eq_zero_of_capsIntegralFundamentalClassesToZero C _ _ _ _ _ _ ?_
  intro T t _ _ k
  obtain ⟨z⟩ := (inferInstance : Nonempty T)
  obtain ⟨i, hi⟩ := hU.exists_mem (t.base z)
  have hirr : IsPreirreducible (Set.range t.base) := by
    rw [← Set.image_univ]
    exact ((IrreducibleSpace.isIrreducible_univ T).image t.base
      t.base.hom.continuous.continuousOn).isPreirreducible
  have hrange : Set.range t.base ⊆ Set.range (U i).ι.base := by
    rw [Scheme.Opens.range_ι]
    exact hU.subset_of_isPreirreducible hirr ⟨z, rfl⟩ hi
  set a := IsOpenImmersion.lift (U i).ι t hrange
  have ha : a ≫ (U i).ι = t := IsOpenImmersion.lift_fac _ _ _
  have : LocallyOfFiniteType (a ≫ (U i).ι) := by
    rw [ha]
    infer_instance
  have : LocallyOfFiniteType a := locallyOfFiniteType_of_comp a (U i).ι
  rw [commutator_cap_eq_zero_iff]
  exact (intertwines_of_res c hY (U i).ι ((U i).ι ≫ sY) rfl x (hx i) a t ha).heq k n _

end CommutesWith

end TotalChowClass

end Stacks.Chow

end
