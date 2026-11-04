module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.GysinSystemOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.PointClassCommuting

/-!
# The operations of a Chow cohomology class on the test schemes, and products

A bivariant class `c ∈ A^p(X) = A^p(X ⟶ X)` caps, on a test scheme `g : T ⟶ X`, into the Chow
group of the chosen pullback `X ×_X T`; pushing forward along the isomorphism
`X ×_X T ⟶ T` reads it as an operation `A_k(T) ⟶ A_{k-p}(T)` on `T` itself. This file records that
operation (`Stacks.Chow.BivariantClass.idRule`), that it determines the class, that it commutes
with proper pushforward along every proper morphism of test schemes, and that it turns the
product of Chow cohomology classes into composition: the product `c · d ∈ A^{p+q}(X)` is the
composite of Stacks 0B75 along `𝟙 X ≫ 𝟙 X = 𝟙 X`, and its operation is the composite of the two
operations (`Stacks.Chow.BivariantClass.idRule_mulId`). So identities in `A^*(X)` may be checked
as identities of operations on the Chow groups of all test schemes.

## Main definitions

* `Stacks.Chow.BivariantClass.idRule` — the operation of a class of `A^p(X)` on the test schemes.
* `Stacks.Chow.BivariantClass.mulId` — the product `A^p(X) × A^q(X) ⟶ A^{p+q}(X)`, the composite
  of Stacks 0B75 at the Gysin system of the first Chern class rule, read for `𝟙 X`.

## Main results

* `Stacks.Chow.BivariantClass.eq_of_idRule_eq` — a class is determined by its operations.
* `Stacks.Chow.BivariantClass.idRule_properNaturality` — the operation commutes with proper
  pushforward, which is axiom (1) of Stacks 0B76 read on the test schemes.
* `Stacks.Chow.BivariantClass.idRule_mulId` — the operation of a product is the composite of the
  operations.

## References

* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-! ### Pushing forward to the test scheme -/

/-- Pushforward along the second projection `X ×_{f,X} T ⟶ T` of the chosen pullback, for an
isomorphism `f : X ⟶ X` over the base: an isomorphism of Chow groups. -/
def pullbackSndPush {f : X ⟶ X} [IsIso f] (hf : f ≫ sX = sX) {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (k : ℤ) :
    chowGroup C (pullback.fst f g ≫ sX) k →+ chowGroup C (g ≫ sX) k :=
  chowPushforwardOfIso C (pullback.fst f g ≫ sX) (g ≫ sX) (pullback.snd f g)
    (pullbackSnd_comp_structureMorphism hf g) k

/-- Pushing forward to the test scheme is invariant under replacing `f` by an equal morphism,
as a heterogeneous equality. -/
theorem pullbackSndPush_heq_congr {f f' : X ⟶ X} [IsIso f] [IsIso f'] (hff : f = f')
    (hf : f ≫ sX = sX) (hf' : f' ≫ sX = sX) {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] {k k' : ℤ} (hk : k = k')
    {x : chowGroup C (pullback.fst f g ≫ sX) k} {x' : chowGroup C (pullback.fst f' g ≫ sX) k'}
    (hx : x ≍ x') : pullbackSndPush C sX hf g k x ≍ pullbackSndPush C sX hf' g k' x' := by
  subst hff hk
  cases hx
  rfl

variable (G : GysinSystem C)

/-! ### The operation of a class on the test schemes -/

/-- The operation on the test schemes of a bivariant class for an isomorphism `f : X ⟶ X`: cap,
then push forward to the test scheme. -/
def BivariantClass.isoRule {f : X ⟶ X} [IsIso f] [LocallyOfFiniteType f] (hf : f ≫ sX = sX)
    {p : ℤ} (c : BivariantClass C G sX sX f hf p) : IdentityCapRule C sX p :=
  fun {_T} g _ k ↦ (pullbackSndPush C sX hf g (k - p)).comp (c.cap g k)

/-- **The operation of a Chow cohomology class on the test schemes.** For `c ∈ A^p(X)` and a test
scheme `g : T ⟶ X`, the operation `A_k(T) ⟶ A_{k-p}(T)` obtained by capping into the Chow group
of `X ×_X T` and pushing forward along the isomorphism `X ×_X T ⟶ T`. -/
def BivariantClass.idRule {p : ℤ} (c : BivariantClass C G sX sX (𝟙 X) (Category.id_comp sX) p) :
    IdentityCapRule C sX p :=
  c.isoRule C sX G (Category.id_comp sX)

/-- The operation of `c ∈ A^p(X)` on a test scheme `g : T ⟶ X` sends `α` to the pushforward to
`T` of `c ∩ α`. -/
theorem BivariantClass.idRule_apply {p : ℤ}
    (c : BivariantClass C G sX sX (𝟙 X) (Category.id_comp sX) p) {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sX) k) :
    c.idRule C sX G g k α = pullbackSndPush C sX (Category.id_comp sX) g (k - p) (c.cap g k α) :=
  rfl

/-- The operation of the transport of a class along an equality of morphisms is the operation of
the class. -/
theorem BivariantClass.isoRule_bivariantClassCongr_heq {f f' : X ⟶ X} [IsIso f] [IsIso f']
    [LocallyOfFiniteType f] [LocallyOfFiniteType f'] (hff : f = f') (hf : f ≫ sX = sX)
    (hf' : f' ≫ sX = sX) {p : ℤ} (c : BivariantClass C G sX sX f hf p) {T : Scheme.{u}}
    (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sX) k) :
    (bivariantClassCongr C G sX sX hff hf hf' p c).isoRule C sX G hf' g k α ≍
      c.isoRule C sX G hf g k α := by
  subst hff
  rfl

/-- **A Chow cohomology class is determined by its operations on the test schemes.** -/
theorem BivariantClass.eq_of_idRule_eq {p : ℤ}
    (c d : BivariantClass C G sX sX (𝟙 X) (Category.id_comp sX) p)
    (h : ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
      (α : chowGroup C (g ≫ sX) k), c.idRule C sX G g k α = d.idRule C sX G g k α) :
    c = d :=
  BivariantClass.eq_of_pushforward_cap_eq C sX p G c d fun g _ k α ↦ by
    simpa only [identityBaseChangeIso, asIso_hom, BivariantClass.idRule_apply, pullbackSndPush]
      using h g k α

/-- An identity cap rule takes heterogeneously equal arguments over equal test morphisms to
heterogeneously equal values. -/
theorem IdentityCapRule.heq_congr {p : ℤ} (op : IdentityCapRule C sX p) {T : Scheme.{u}}
    {g g' : T ⟶ X} [LocallyOfFiniteType g] [LocallyOfFiniteType g'] (hg : g = g') {k k' : ℤ}
    (hk : k = k') {α : chowGroup C (g ≫ sX) k} {α' : chowGroup C (g' ≫ sX) k'} (hα : α ≍ α') :
    op g k α ≍ op g' k' α' := by
  subst hg hk
  cases hα
  rfl

/-- Proper pushforward along two factorizations of the same morphism agrees. -/
private theorem properChowPushforward_comp_eq_comp {A B B' D : Scheme.{u}} (sA : A ⟶ C.S)
    [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (sB' : B' ⟶ C.S)
    [LocallyOfFiniteType sB'] (sD : D ⟶ C.S) [LocallyOfFiniteType sD] (u : A ⟶ B) [IsProper u]
    (v : B ⟶ D) [IsProper v] (u' : A ⟶ B') [IsProper u'] (v' : B' ⟶ D) [IsProper v']
    (huv : u ≫ v = u' ≫ v') (hu : u ≫ sB = sA) (hv : v ≫ sD = sB) (hu' : u' ≫ sB' = sA)
    (hv' : v' ≫ sD = sB') {k : ℤ}
    (hfacu : ProperPushforwardFactorsThroughRationalEquivalence C sA sB u hu k)
    (hfacv : ProperPushforwardFactorsThroughRationalEquivalence C sB sD v hv k)
    (hfacu' : ProperPushforwardFactorsThroughRationalEquivalence C sA sB' u' hu' k)
    (hfacv' : ProperPushforwardFactorsThroughRationalEquivalence C sB' sD v' hv' k)
    (x : chowGroup C sA k) :
    properChowPushforward C sB sD v hv k hfacv (properChowPushforward C sA sB u hu k hfacu x) =
      properChowPushforward C sB' sD v' hv' k hfacv'
        (properChowPushforward C sA sB' u' hu' k hfacu' x) := by
  rw [← properChowPushforward_comp_apply C sA sB sD u v (u ≫ v) rfl hu hv
      (by rw [Category.assoc, hv, hu]) k hfacu hfacv (properPushforwardDescends C _ _ _ _ _),
    ← properChowPushforward_comp_apply C sA sB' sD u' v' (u' ≫ v') rfl hu' hv'
      (by rw [Category.assoc, hv', hu']) k hfacu' hfacv' (properPushforwardDescends C _ _ _ _ _)]
  exact congrFun (congrArg DFunLike.coe (properChowPushforward_congr C _ _ _ _ huv _ _ k _ _)) x

/-- **Axiom (1) of Stacks 0B76, read on the test schemes.** The operation of a Chow cohomology
class commutes with proper pushforward along a proper morphism of test schemes over `X`. -/
theorem BivariantClass.idRule_properNaturality {p : ℤ}
    (c : BivariantClass C G sX sX (𝟙 X) (Category.id_comp sX) p) :
    IdentityCapRule.ProperNaturality C sX p (c.idRule C sX G) := by
  intro T T' g _ h _ k hfac hfacp α
  let h' : pullback (𝟙 X) (h ≫ g) ⟶ pullback (𝟙 X) g :=
    pullback.lift (pullback.fst (𝟙 X) (h ≫ g)) (pullback.snd (𝟙 X) (h ≫ g) ≫ h)
      (by rw [Category.assoc, ← pullback.condition])
  have hfst : h' ≫ pullback.fst (𝟙 X) g = pullback.fst (𝟙 X) (h ≫ g) := pullback.lift_fst _ _ _
  have hsnd : h' ≫ pullback.snd (𝟙 X) g = pullback.snd (𝟙 X) (h ≫ g) ≫ h :=
    pullback.lift_snd _ _ _
  have sq : IsPullback (pullback.snd (𝟙 X) (h ≫ g)) h' h (pullback.snd (𝟙 X) g) :=
    IsPullback.of_horiz_isIso ⟨hsnd.symm⟩
  have : IsProper h' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
  have hm : h' ≫ pullback.fst (𝟙 X) g ≫ sX = pullback.fst (𝟙 X) (h ≫ g) ≫ sX := by
    rw [← Category.assoc, hfst]
  have hfac' : ProperPushforwardFactorsThroughRationalEquivalence C
      (pullback.fst (𝟙 X) (h ≫ g) ≫ sX) (pullback.fst (𝟙 X) g ≫ sX) h' hm (k - p) :=
    properPushforwardDescends C _ _ _ _ _
  rw [BivariantClass.idRule_apply, c.proper_naturality g h h' sq hfst k hfac hfac' α,
    BivariantClass.idRule_apply]
  simp only [pullbackSndPush, chowPushforwardOfIso]
  exact properChowPushforward_comp_eq_comp C _ _ _ _ _ _ _ _ hsnd _ _ _ _ _ _ _ _ _

/-! ### Products of Chow cohomology classes -/

/-- **The product `A^p(X) × A^q(X) ⟶ A^{p+q}(X)`.** The composite of Stacks 0B75 at the Gysin
system of the first Chern class rule, which is a class for `𝟙 X ≫ 𝟙 X`, read as a class for
`𝟙 X`. -/
def BivariantClass.mulId {p q : ℤ}
    (c : BivariantClass C (gysinSystemOfInvertible C) sX sX (𝟙 X) (Category.id_comp sX) p)
    (d : BivariantClass C (gysinSystemOfInvertible C) sX sX (𝟙 X) (Category.id_comp sX) q) :
    BivariantClass C (gysinSystemOfInvertible C) sX sX (𝟙 X) (Category.id_comp sX) (p + q) :=
  bivariantClassCongr C (gysinSystemOfInvertible C) sX sX (Category.comp_id (𝟙 X))
    (comp_comp_structureMorphism_eq (Category.id_comp sX) (Category.id_comp sX))
    (Category.id_comp sX) (p + q)
    (bivariantCompositeOfInvertible C sX sX sX (𝟙 X) (𝟙 X) (Category.id_comp sX)
      (Category.id_comp sX) p q c d)

/-- Chow groups of two equal structure morphisms are equal types. -/
theorem chowGroup_congr_structureMorphism {A : Scheme.{u}} {s s' : A ⟶ C.S}
    [LocallyOfFiniteType s] [LocallyOfFiniteType s'] (h : s = s') (k : ℤ) :
    chowGroup C s k = chowGroup C s' k := by
  subst h
  rfl

/-- **The operation of a product is the composite of the operations.** For `c ∈ A^p(X)` and
`d ∈ A^q(X)`, the operation of `c · d` on a test scheme `g : T ⟶ X` is `c ∩ (d ∩ -)`; the two
sides lie in `A_{k-(p+q)}(T)` and `A_{(k-q)-p}(T)`, whence the heterogeneous equality. -/
theorem BivariantClass.idRule_mulId {p q : ℤ}
    (c : BivariantClass C (gysinSystemOfInvertible C) sX sX (𝟙 X) (Category.id_comp sX) p)
    (d : BivariantClass C (gysinSystemOfInvertible C) sX sX (𝟙 X) (Category.id_comp sX) q)
    {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sX) k) :
    (c.mulId C sX d).idRule C sX (gysinSystemOfInvertible C) g k α ≍
      c.idRule C sX (gysinSystemOfInvertible C) g (k - q)
        (d.idRule C sX (gysinSystemOfInvertible C) g k α) := by
  have hg' : pullback.fst (𝟙 X) g = pullback.snd (𝟙 X) g ≫ g := by
    simpa only [Category.comp_id] using
      (pullback.condition : pullback.fst (𝟙 X) g ≫ 𝟙 X = pullback.snd (𝟙 X) g ≫ g)
  have h1 := BivariantClass.isoRule_bivariantClassCongr_heq C sX (gysinSystemOfInvertible C)
    (Category.comp_id (𝟙 X))
    (comp_comp_structureMorphism_eq (Category.id_comp sX) (Category.id_comp sX))
    (Category.id_comp sX)
    (bivariantCompositeOfInvertible C sX sX sX (𝟙 X) (𝟙 X) (Category.id_comp sX)
      (Category.id_comp sX) p q c d) g k α
  refine h1.trans ?_
  have hff : (𝟙 X ≫ 𝟙 X) ≫ sX = sX :=
    comp_comp_structureMorphism_eq (Category.id_comp sX) (Category.id_comp sX)
  show pullbackSndPush C sX hff g (k - (p + q))
      (chowGroupDegreeEquiv C (pullback.fst (𝟙 X ≫ 𝟙 X) g ≫ sX) (by ring : k - q - p = k - (p + q))
        (properChowPushforward C (pullback.fst (𝟙 X) (pullback.fst (𝟙 X) g) ≫ sX)
          (pullback.fst (𝟙 X ≫ 𝟙 X) g ≫ sX)
          (pullbackRightPullbackFstIso (𝟙 X) g (𝟙 X)).hom
          (pullbackRightPullbackFstIso_hom_comp_fst_comp sX (𝟙 X) (𝟙 X) g) ((k - q) - p)
          (properPushforwardDescends C _ _ _ _ _)
          (c.cap (pullback.fst (𝟙 X) g) (k - q) (d.cap g k α)))) ≍ _
  refine HEq.trans (b := pullbackSndPush C sX hff g ((k - q) - p)
      (properChowPushforward C (pullback.fst (𝟙 X) (pullback.fst (𝟙 X) g) ≫ sX)
        (pullback.fst (𝟙 X ≫ 𝟙 X) g ≫ sX)
        (pullbackRightPullbackFstIso (𝟙 X) g (𝟙 X)).hom
        (pullbackRightPullbackFstIso_hom_comp_fst_comp sX (𝟙 X) (𝟙 X) g) ((k - q) - p)
        (properPushforwardDescends C _ _ _ _ _)
        (c.cap (pullback.fst (𝟙 X) g) (k - q) (d.cap g k α)))) ?_ ?_
  · exact properChowPushforward_heq_congr_base C (pullback.snd (𝟙 X ≫ 𝟙 X) g) rfl rfl
      (pullbackSnd_comp_structureMorphism hff g) (pullbackSnd_comp_structureMorphism hff g)
      (by ring) (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ _ _)
      (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ _ _) _ _
      (chowGroupDegreeEquiv_heq C _ _ _)
  have hassoc : (pullbackRightPullbackFstIso (𝟙 X) g (𝟙 X)).hom ≫ pullback.snd (𝟙 X ≫ 𝟙 X) g =
      pullback.snd (𝟙 X) (pullback.fst (𝟙 X) g) ≫ pullback.snd (𝟙 X) g :=
    pullbackRightPullbackFstIso_hom_snd _ _ _
  have e3 : pullbackSndPush C sX hff g ((k - q) - p)
      (properChowPushforward C (pullback.fst (𝟙 X) (pullback.fst (𝟙 X) g) ≫ sX)
        (pullback.fst (𝟙 X ≫ 𝟙 X) g ≫ sX)
        (pullbackRightPullbackFstIso (𝟙 X) g (𝟙 X)).hom
        (pullbackRightPullbackFstIso_hom_comp_fst_comp sX (𝟙 X) (𝟙 X) g) ((k - q) - p)
        (properPushforwardDescends C _ _ _ _ _)
        (c.cap (pullback.fst (𝟙 X) g) (k - q) (d.cap g k α))) =
      pullbackSndPush C sX (Category.id_comp sX) g ((k - q) - p)
        (c.idRule C sX (gysinSystemOfInvertible C) (pullback.fst (𝟙 X) g) (k - q)
          (d.cap g k α)) := by
    simp only [pullbackSndPush, chowPushforwardOfIso, BivariantClass.idRule_apply]
    exact properChowPushforward_comp_eq_comp C _ _ _ _ _ _ _ _ hassoc _ _ _ _ _ _ _ _ _
  rw [e3]
  have htype : chowGroup C (pullback.fst (𝟙 X) g ≫ sX) (k - q) =
      chowGroup C ((pullback.snd (𝟙 X) g ≫ g) ≫ sX) (k - q) :=
    chowGroup_congr_structureMorphism C (congrArg (· ≫ sX) hg') (k - q)
  have key := c.idRule_properNaturality C sX (gysinSystemOfInvertible C) g
    (pullback.snd (𝟙 X) g) (k - q) (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _)
    (cast htype (d.cap g k α))
  have hpush : pullbackSndPush C sX (Category.id_comp sX) g (k - q) (d.cap g k α) =
      properChowPushforward C ((pullback.snd (𝟙 X) g ≫ g) ≫ sX) (g ≫ sX) (pullback.snd (𝟙 X) g)
        (by simp [Category.assoc]) (k - q) (properPushforwardDescends C _ _ _ _ _)
        (cast htype (d.cap g k α)) :=
    eq_of_heq (properChowPushforward_heq_congr_base C (pullback.snd (𝟙 X) g)
      (congrArg (· ≫ sX) hg') rfl _ _ rfl
      (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ _ _)
      (properPushforwardDescends C _ _ _ _ _) _ _ (cast_heq _ _).symm)
  rw [BivariantClass.idRule_apply C sX (gysinSystemOfInvertible C) d g k α, hpush, key]
  exact properChowPushforward_heq_congr_base C (pullback.snd (𝟙 X) g)
    (congrArg (· ≫ sX) hg') rfl _ _ rfl
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _) _ _
    (IdentityCapRule.heq_congr C sX (c.idRule C sX (gysinSystemOfInvertible C)) hg' rfl
      (cast_heq _ _).symm)

end Stacks.Chow

end
