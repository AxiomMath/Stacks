module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomologyOverFieldUnconditional
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.IdentityRule
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.SmoothCapFundamentalThroughBase
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDivisorClass
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductCapCommutingEveryCap
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductFundamentalClassBivariant
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.IsomorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.IntersectionProduct
public import StacksFrontier.AlgebraicGeometry.Chow.IntersectionProductRegularImmersion

/-!
# Composition in `A^*(X)` is the intersection product

Let `k` be a field and let `X` be smooth over `k`, equidimensional of dimension `d`, with
structure morphism `g : X ⟶ Spec k`. **Stacks 0FC2** asserts that

  `Θ : A^p(X) ⟶ CH_{d-p}(X)`,  `c ↦ c ∩ [X]_d`,

is an isomorphism, and that via `Θ` composition of bivariant classes turns into the intersection
product of Stacks 0FC0. The source proves the second clause by computing the inverse of `Θ`:
`Θ` is `c ↦ c ∘ g^*` (Stacks 0FBT) followed by `c' ↦ c' ∩ [Spec k]` (Stacks 0FBW); the inverse of
the second arrow sends `α` to the class `β ↦ α × β`, and the inverse of the first sends a class
`c'` to `res(Δ^!) ∘ res(c')`. So the class `c` with `Θ(c) = α` acts by `β ↦ Δ^!(α × β) = α · β`,
which is the second clause.

This file carries out that computation. Its first step is Stacks 0FBW in its exterior-product
form over a field: every `c' ∈ A^q(X ⟶ Spec k)` caps as `γ ↦ (c' ∩ [Spec k]) × γ`. Its second
step is the action of `A^p(X)` on `CH_*(X)`: `c ∩ β = Θ(c) · β`. The second clause of Stacks 0FC2
follows: `Θ(a · b) = a ∩ Θ(b) = Θ(a) · Θ(b)`.

## Main results

* `Stacks.Chow.BivariantClass.capBase_eq_chowExteriorProduct_of_field` — **Stacks 0FBW in its
  exterior-product form**: over a field, `c' ∩ γ = (c' ∩ [Spec k]) × γ` for every
  `c' ∈ A^q(X ⟶ Spec k)`.
* `Stacks.Chow.isExteriorProductBivariantClass_bivariantToBaseEval_of_field`,
  `Stacks.Chow.exteriorProductRepresentedByBivariantClasses_of_field` — the same, in the form of
  the predicates `Stacks.Chow.IsExteriorProductBivariantClass` and
  `Stacks.Chow.ExteriorProductRepresentedByBivariantClasses`.
* `Stacks.Chow.cap_id_eq_intersectionProduct`,
  `Stacks.Chow.chowCohomologyCap_eq_intersectionProduct` — the action of `c ∈ A^p(X)` on
  `CH_n(X)` is the intersection product with `Θ(c)`: `c ∩ β = Θ(c) · β`, on `X ×_X X` and on
  `X`.
* `Stacks.Chow.chowCohomologyCapFundamentalClass_mulId` — **Stacks 0FC2, second clause**:
  `Θ(a · b) = Θ(a) · Θ(b)`.

## Implementation notes

### The class of the diagonal

The intersection product of Stacks 0FC0 is `Stacks.Chow.intersectionProduct`, which is formed
with a class of the diagonal carried as an argument. Here that class is a class
`D ∈ A^d(X ⟶ X ×_k X)` in the presentation of `Stacks.Chow.smoothShiftBackward`, whose source
is indexed by `Δ ≫ pr₁ ≫ g` rather than by `g`; `Stacks.Chow.bivariantClassCongrBase` reads it
in the presentation `Stacks.Chow.intersectionProduct` consumes. The source takes `D` to be the
Gysin class `Δ^!` of the diagonal, and the proof uses two of its properties, which are hypotheses
of the statements below exactly as in `Stacks.Chow.smoothShiftBackward_smoothShiftForward`:
`D` commutes with every bivariant class over `X ×_k X` (Stacks 0FBP, through Stacks 0FF6), and
`D ∘ pr₂^* = 1` (Stacks 0FBS). The third property `D ∘ pr₁^* = 1` of Stacks 0FBT is not needed:
only the identity `res(D) ∘ res(c ∘ g^*) = c` is used, not its converse. Smoothness of `X` enters
only through these properties of `D`; what is assumed of `X` itself is that it is flat of
relative dimension `d` over `k`, which is what the flat pullback class `g^*` needs.

### The order of the product, and the product of `A^*(X)`

The product `a · b` of `A^*(X)` is `Stacks.Chow.BivariantClass.mulId`, the composite of
Stacks 0B75 read for `𝟙 X`, whose action on test schemes is `a ∩ (b ∩ -)`
(`Stacks.Chow.BivariantClass.idRule_mulId`). With the action `c ∩ β = Θ(c) · β` it is carried to
`Θ(a) · Θ(b)`, the factor `Θ(a)` in the first slot of the exterior product.

### Identifications

The intersection product of `α, β ∈ CH_*(X)` lands on `X ×_X X`, read on `X` through
`Stacks.Chow.chowGroupSelfProductUnitCollapse`, and in degree `(d - p) + n - d`, matched with
`n - p` by `Stacks.Chow.chowGroupDegreeEquiv`. The action of `A^p(X)` on `CH_*(X)` is
`Stacks.Chow.chowCohomologyCap`.

## References

* [Stacks Project, Tag 0FC2](https://stacks.math.columbia.edu/tag/0FC2)
* [Stacks Project, Tag 0FC0](https://stacks.math.columbia.edu/tag/0FC0)
* [Stacks Project, Tag 0FBT](https://stacks.math.columbia.edu/tag/0FBT)
* [Stacks Project, Tag 0FBW](https://stacks.math.columbia.edu/tag/0FBW)
* [Stacks Project, Tag 0FBY](https://stacks.math.columbia.edu/tag/0FBY)
* [Stacks Project, Tag 0FBP](https://stacks.math.columbia.edu/tag/0FBP)
* [Stacks Project, Tag 0FBS](https://stacks.math.columbia.edu/tag/0FBS)
* [Stacks Project, Tag 0B0R](https://stacks.math.columbia.edu/tag/0B0R)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Exterior products of heterogeneously equal classes -/

/-- The exterior product `x × y` depends on the class `x` only up to heterogeneous equality: the
structure morphism of the first factor and the degree of `x` may be replaced by equal ones. -/
theorem chowExteriorProduct_tmul_heq_of_heq (C : ChowSituation.{u}) [Subsingleton C.S]
    [IsIntegral C.S] [JacobsonSpace C.S]
    (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0) {A T : Scheme.{u}}
    {sA sA' : A ⟶ C.S} [LocallyOfFiniteType sA] [LocallyOfFiniteType sA'] (hA : sA = sA')
    (sT : T ⟶ C.S) [LocallyOfFiniteType sT] {n n' : ℤ} (hn : n = n') (m : ℤ)
    (x : chowGroup C sA n) (x' : chowGroup C sA' n') (hx : x ≍ x') (y : chowGroup C sT m) :
    chowExteriorProduct C hδ sA sT n m (x ⊗ₜ[ℤ] y) ≍
      chowExteriorProduct C hδ sA' sT n' m (x' ⊗ₜ[ℤ] y) := by
  subst hA hn
  obtain rfl := eq_of_heq hx
  rfl

/-! ### Reading a bivariant class for an equal morphism, up to heterogeneous equality -/

/-- The cap operation of a bivariant class read for an equal morphism is the cap operation of the
class, up to heterogeneous equality: the two values live on the base changes of two equal
morphisms. -/
theorem BivariantClass.congrHom_cap_heq {C : ChowSituation.{u}} {G : GysinSystem C}
    {X Y : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sY : Y ⟶ C.S}
    [LocallyOfFiniteType sY] {f f' : X ⟶ Y} [LocallyOfFiniteType f] [LocallyOfFiniteType f']
    {hf : f ≫ sY = sX} {p : ℤ} (e : f = f') (hf' : f' ≫ sY = sX)
    (c : BivariantClass C G sX sY f hf p) {T : Scheme.{u}} (t : T ⟶ Y) [LocallyOfFiniteType t]
    (k : ℤ) (α : chowGroup C (t ≫ sY) k) :
    (c.congrHom e hf').cap t k α ≍ c.cap t k α := by
  subst e
  rfl

/-! ### The action of `A^p(X)` on `CH_*(X)`, read through the second projection -/

/-- The action `α ↦ c ∩ α` of `c ∈ A^p(X)` on `CH_*(X)` is the operation of `c` on the test
scheme `𝟙 X`: the first and the second projection of `X ×_X X` agree. -/
theorem chowCohomologyCap_heq_idRule_ofGysinSystem (C : ChowSituation.{u}) (G : GysinSystem C)
    {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (p : ℤ)
    (c : chowCohomologyComponent C G sX p) (k : ℤ) (x : chowGroup C sX k) :
    chowCohomologyCap C G sX p c k x ≍
      c.idRule C sX G (𝟙 X) k (chowGroupCongr C (Category.id_comp sX).symm k x) := by
  have hfs : pullback.fst (𝟙 X) (𝟙 X) = pullback.snd (𝟙 X) (𝟙 X) := by
    simpa only [Category.comp_id] using (pullback.condition (f := 𝟙 X) (g := 𝟙 X))
  simp only [chowCohomologyCap, AddMonoidHom.coe_comp, Function.comp_apply,
    AddEquiv.coe_toAddMonoidHom, chowGroupEquivOfIso_apply, BivariantClass.idRule_apply,
    pullbackSndPush]
  refine (chowPushforwardOfIso_heq _ _ (by rw [Category.id_comp]) rfl
    (Category.id_comp sX).symm rfl HEq.rfl).trans (heq_of_eq ?_)
  exact chowPushforwardOfIso_congr_apply _ _ _ _ _ hfs _ _ _ _

/-! ### Stacks 0FBW in its exterior-product form, over a field -/

section Field

variable (k : Type u) [Field k]

/-- The exterior product with the class of the point: for `γ ∈ CH_m(T)`, the product
`[Spec k] × γ` on `Spec k ×_k T` is `γ` carried along the inverse of the second projection, which
is an isomorphism. -/
theorem chowExteriorProduct_fundamentalChowClass_base_tmul_heq {T : Scheme.{u}}
    (sT : T ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sT] (m : ℤ)
    (γ : chowGroup (fieldChowSituation k) sT m) :
    chowExteriorProduct (fieldChowSituation k) (fun _ _ ↦ rfl) (𝟙 (fieldChowSituation k).S) sT
        0 m
        (fundamentalChowClass (fieldChowSituation k) (𝟙 (fieldChowSituation k).S) 0 ⊗ₜ[ℤ] γ) ≍
      chowPushforwardOfIso (fieldChowSituation k) sT
        (pullback.fst (𝟙 (fieldChowSituation k).S) sT ≫ 𝟙 (fieldChowSituation k).S)
        (inv (pullback.snd (𝟙 (fieldChowSituation k).S) sT))
        (by rw [pullback.condition, IsIso.inv_hom_id_assoc]) m γ := by
  have hrel : AlgebraicGeometry.RelativeDimension
      (pullback.snd (𝟙 (fieldChowSituation k).S) sT) 0 :=
    relativeDimension_pullbackSnd (𝟙 (fieldChowSituation k).S)
      (relativeDimension_identity (fieldChowSituation k).S) sT
  have hd : relativeDimension (fieldChowSituation k).dimensionFunction
      (𝟙 (fieldChowSituation k).S) (genericPoint (fieldChowSituation k).S) = ((0 : ℕ) : ℤ) := by
    rw [relativeDimension_id]
    rfl
  have hfac := flatPullbackDescends (fieldChowSituation k)
    (pullback.fst (𝟙 (fieldChowSituation k).S) sT ≫ 𝟙 (fieldChowSituation k).S) sT
    (pullback.snd (𝟙 (fieldChowSituation k).S) sT) pullback.condition.symm 0 hrel m
  have hprod := chowGroupDegreeEquiv_flatPullbackChowSnd_eq_chowExteriorProduct
    (fieldChowSituation k) (fun _ _ ↦ rfl) (𝟙 (fieldChowSituation k).S) sT 0 hrel hd m hfac γ
  -- the flat pullback along the isomorphism `pr_T` is the pushforward along its inverse
  have hiso := flatPullbackChow_chowPushforwardOfIso (fieldChowSituation k) sT sT sT
    (pullback.fst (𝟙 (fieldChowSituation k).S) sT ≫ 𝟙 (fieldChowSituation k).S) (𝟙 T)
    (Category.id_comp sT) (inv (pullback.snd (𝟙 (fieldChowSituation k).S) sT))
    (by rw [pullback.condition, IsIso.inv_hom_id_assoc]) (𝟙 T) (Category.id_comp sT)
    (pullback.snd (𝟙 (fieldChowSituation k).S) sT) pullback.condition.symm (by simp) 0
    (relativeDimension_identity T) hrel m
    (flatPullbackFactorsThroughRationalEquivalence_id (fieldChowSituation k) sT m) hfac γ
  rw [chowPushforwardOfIso_id, flatPullbackChow_id] at hiso
  refine HEq.trans (heq_of_eq hprod.symm) ?_
  refine (chowGroupDegreeEquiv_heq _ _ _ _).trans ?_
  rw [hiso]
  exact chowPushforwardOfIso_heq_congr _ _ _ _ _ (by simp) _ _ (cast_heq _ γ)

/-- **Stacks 0FBW in its exterior-product form, over a field.** Every bivariant class
`c ∈ A^q(X ⟶ Spec k)` caps as the exterior product with its value `c ∩ [Spec k] ∈ CH_{-q}(X)`:

  `c ∩ γ = (c ∩ [Spec k]) × γ`   in   `CH_{m-q}(X ×_k T)`

for every `T` locally of finite type over `k` and every `γ ∈ CH_m(T)`. This is the description of
the inverse of the map of Stacks 0FBW in its proof, `α ↦ (β ↦ α × β)`.

It is Stacks 0FBY over a field with the cap product in the first variable,
`Stacks.Chow.chowExteriorProduct_capTarget_eq_capExteriorProductFst_of_field`, read at
`ξ = [Spec k]`: there `c ∩ ([Spec k] × γ)` is the cap at `Spec k ×_k T`, and
`[Spec k] × γ` is `γ` carried along `T ≅ Spec k ×_k T`,
`Stacks.Chow.chowExteriorProduct_fundamentalChowClass_base_tmul_heq`. -/
theorem BivariantClass.capBase_eq_chowExteriorProduct_of_field {X : Scheme.{u}}
    (sX : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sX] (q : ℤ)
    (c : bivariantToBase (fieldChowSituation k) (gysinSystemOfInvertible (fieldChowSituation k))
      sX q)
    {T : Scheme.{u}} (sT : T ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sT] (m : ℤ)
    (γ : chowGroup (fieldChowSituation k) sT m) :
    c.capBase (fieldChowSituation k) (gysinSystemOfInvertible (fieldChowSituation k)) sX q sT m
        γ =
      chowGroupDegreeEquiv (fieldChowSituation k) (pullback.fst sX sT ≫ sX)
        (by ring : -q + m = m - q)
        (chowExteriorProduct (fieldChowSituation k) (fun _ _ ↦ rfl) sX sT (-q) m
          (bivariantToBaseEval (fieldChowSituation k)
            (gysinSystemOfInvertible (fieldChowSituation k)) sX q c ⊗ₜ[ℤ] γ)) := by
  have key := chowExteriorProduct_capTarget_eq_capExteriorProductFst_of_field k sT sX
    (𝟙 (fieldChowSituation k).S) sX (Category.comp_id sX) q c 0 m
    (fundamentalChowClass (fieldChowSituation k) (𝟙 (fieldChowSituation k).S) 0) γ
  unfold capExteriorProductFst at key
  -- the value of `c` at the point is its cap product against the class of the point
  have heval : bivariantToBaseEval (fieldChowSituation k)
      (gysinSystemOfInvertible (fieldChowSituation k)) sX q c ≍
      c.capTarget (fieldChowSituation k) (gysinSystemOfInvertible (fieldChowSituation k)) sX
        (𝟙 (fieldChowSituation k).S) sX (Category.comp_id sX) q 0
        (fundamentalChowClass (fieldChowSituation k) (𝟙 (fieldChowSituation k).S) 0) := by
    rw [bivariantToBaseEval_apply, chowGroupBaseUnitCollapse, AddEquiv.trans_apply,
      chowGroupEquivOfIso_apply, BivariantClass.capTarget, chowGroupCongr_fundamentalChowClass]
    refine (chowPushforwardOfIso_heq_congr _ _ _ _ _ (zero_sub q).symm _ _
      (chowGroupDegreeEquiv_heq _ _ _ _)).trans ?_
    exact heq_of_eq (chowPushforwardOfIso_congr_apply _ _ _ _ _
      (pullbackIdIso_inv_eq_fst sX).symm _ _ _ _)
  refine eq_of_heq (HEq.trans ?_ (chowGroupDegreeEquiv_heq _ _ _ _).symm)
  refine HEq.trans ?_ (chowExteriorProduct_tmul_heq_of_heq (fieldChowSituation k) _ rfl sT
    (zero_sub q) m _ _ heval.symm γ)
  rw [key]
  -- `[Spec k] × γ` is `γ` carried to `Spec k ×_k T`
  have hι : inv (pullback.snd (𝟙 (fieldChowSituation k).S) sT) ≫
      pullback.fst (𝟙 (fieldChowSituation k).S) sT = sT := by
    rw [← Category.comp_id (pullback.fst (𝟙 (fieldChowSituation k).S) sT), pullback.condition,
      IsIso.inv_hom_id_assoc]
  have hcap : c.cap (pullback.fst (𝟙 (fieldChowSituation k).S) sT) (0 + m)
      (chowExteriorProduct (fieldChowSituation k) (fun _ _ ↦ rfl) (𝟙 (fieldChowSituation k).S)
        sT 0 m (fundamentalChowClass (fieldChowSituation k) (𝟙 (fieldChowSituation k).S) 0 ⊗ₜ[ℤ]
          γ)) ≍
      c.capBase (fieldChowSituation k) (gysinSystemOfInvertible (fieldChowSituation k)) sX q
        (pullback.fst (𝟙 (fieldChowSituation k).S) sT) m
        (chowPushforwardOfIso (fieldChowSituation k) sT
          (pullback.fst (𝟙 (fieldChowSituation k).S) sT)
          (inv (pullback.snd (𝟙 (fieldChowSituation k).S) sT)) hι m γ) := by
    rw [BivariantClass.capBase_apply]
    refine c.cap_heq_congr _ (zero_add m) _ _ ?_
    refine (chowExteriorProduct_fundamentalChowClass_base_tmul_heq k sT m γ).trans ?_
    exact (chowPushforwardOfIso_heq _ _ _ rfl (Category.comp_id _) rfl HEq.rfl).trans
      (chowGroupCongr_heq _ _ _ _).symm
  have hbc := c.capBase_chowPushforwardOfTestIso (fieldChowSituation k)
    (gysinSystemOfInvertible (fieldChowSituation k)) sX q
    (pullback.fst (𝟙 (fieldChowSituation k).S) sT)
    (inv (pullback.snd (𝟙 (fieldChowSituation k).S) sT)) hι m γ
  refine HEq.symm ((chowPushforwardOfIso_heq_congr _ _ _ _ _ (by ring) _ _
    ((chowGroupDegreeEquiv_heq _ _ _ _).trans hcap)).trans ?_)
  rw [hbc, chowPushforwardOfIso_comp_apply]
  refine chowPushforwardOfIso_heq_of_eq_id _ ?_ _ _
  ext <;> simp

/-- **Stacks 0FBW in its exterior-product form, over a field, as the predicate.** Every class
`c ∈ A^{-n}(X ⟶ Spec k)` is the class of the exterior product with its value
`c ∩ [Spec k] ∈ CH_n(X)`, in the sense of `Stacks.Chow.IsExteriorProductBivariantClass`. -/
theorem isExteriorProductBivariantClass_bivariantToBaseEval_of_field {X : Scheme.{u}}
    (sX : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sX] (n : ℤ)
    (c : bivariantToBase (fieldChowSituation k) (gysinSystemOfInvertible (fieldChowSituation k))
      sX (-n)) :
    IsExteriorProductBivariantClass (fieldChowSituation k) (fun _ _ ↦ rfl)
      (gysinSystemOfInvertible (fieldChowSituation k)) sX n
      (chowGroupDegreeEquiv (fieldChowSituation k) sX (neg_neg n)
        (bivariantToBaseEval (fieldChowSituation k)
          (gysinSystemOfInvertible (fieldChowSituation k)) sX (-n) c)) c := by
  intro T sT _ m γ
  rw [BivariantClass.capBase_eq_chowExteriorProduct_of_field]
  refine eq_of_heq ((chowGroupDegreeEquiv_heq _ _ _ _).trans
    (HEq.trans ?_ (chowGroupDegreeEquiv_heq _ _ _ _).symm))
  exact chowExteriorProduct_tmul_heq_of_heq _ _ rfl sT (neg_neg n) m _ _
    (chowGroupDegreeEquiv_heq _ _ _ _).symm γ

/-- **Stacks 0FBW in its exterior-product form, over a field, quantified.** Over a field every
Chow class `α ∈ CH_n(X)` is represented by a bivariant class towards the point which caps as
`γ ↦ α × γ`: the class `c` with `c ∩ [Spec k] = α`, which exists by Stacks 0FBW. -/
theorem exteriorProductRepresentedByBivariantClasses_of_field :
    ExteriorProductRepresentedByBivariantClasses (fieldChowSituation k) (fun _ _ ↦ rfl)
      (gysinSystemOfInvertible (fieldChowSituation k)) := by
  intro X sX _ n α
  obtain ⟨c, hc⟩ := (bivariantToBaseEval_bijective_of_field sX (-n)).2
    (chowGroupDegreeEquiv (fieldChowSituation k) sX (neg_neg n).symm α)
  have hα : chowGroupDegreeEquiv (fieldChowSituation k) sX (neg_neg n)
      (bivariantToBaseEval (fieldChowSituation k)
        (gysinSystemOfInvertible (fieldChowSituation k)) sX (-n) c) = α := by
    rw [hc]
    exact eq_of_heq ((chowGroupDegreeEquiv_heq _ _ _ _).trans (chowGroupDegreeEquiv_heq _ _ _ _))
  exact ⟨c, hα ▸ isExteriorProductBivariantClass_bivariantToBaseEval_of_field k sX n c⟩

end Field

/-! ### The action of `A^*(X)` on `CH_*(X)` is the intersection product -/

section Product

variable (k : Type u) [Field k] {X : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
  [LocallyOfFiniteType sX] [Flat sX] (d : ℕ) (hd : AlgebraicGeometry.RelativeDimension sX d)
  (D : BivariantClass (fieldChowSituation k) (gysinSystemOfInvertible (fieldChowSituation k))
    (pullback.diagonal sX ≫ (pullback.fst sX sX ≫ sX)) (pullback.fst sX sX ≫ sX)
    (pullback.diagonal sX) rfl d)

/-- **The cap product of `A^p(X)` is the intersection product with the value on `[X]_d`, on
`X ×_X X`.** Let `X` be flat of relative dimension `d` over a field, and let
`D ∈ A^d(X ⟶ X ×_k X)` be a class of the diagonal which commutes with every bivariant class over
`X ×_k X` and satisfies `D ∘ pr₂^* = 1`. Then for `c ∈ A^p(X)` and `β ∈ CH_n(X)`

  `c ∩ β = (c ∩ [X]_d) · β`,

the intersection product of Stacks 0FC0 formed with `Δ^! = D`, both sides read on `X ×_X X`.

This is the computation of the proof of Stacks 0FC2: by Stacks 0FBT `c` is `res(D) ∘ res(c ∘ g^*)`
(`Stacks.Chow.smoothShiftBackward_smoothShiftForward`), and the class `c ∘ g^*` towards the point
caps as the exterior product with its value `c ∩ [X]_d`
(`Stacks.Chow.BivariantClass.capBase_eq_chowExteriorProduct_of_field`), so
`c ∩ β = D ∩ ((c ∩ [X]_d) × β)`, which is the intersection product. -/
theorem cap_id_eq_intersectionProduct
    (hcomm : ∀ {Z₂ : Scheme.{u}} (f₂ : Z₂ ⟶ pullback sX sX) [LocallyOfFiniteType f₂] (p₂ : ℤ)
      (c₂ : BivariantClass (fieldChowSituation k) (gysinSystemOfInvertible (fieldChowSituation k))
        (f₂ ≫ (pullback.fst sX sX ≫ sX)) (pullback.fst sX sX ≫ sX) f₂ rfl p₂),
      BivariantCommute (fieldChowSituation k) (gysinSystemOfInvertible (fieldChowSituation k))
        (pullback.fst sX sX ≫ sX) (pullback.diagonal sX) f₂ d p₂ D c₂)
    (hD₂ : D.CompFlatPullbackEqOne (pullback.snd sX sX)
      (smoothShift_pullback_snd_comp_structureMorphism (fieldChowSituation k) sX
        (𝟙 (fieldChowSituation k).S) sX (Category.comp_id sX)) (pullback.diagonal_snd sX)
      (relativeDimension_pullback_snd sX sX d hd))
    (p : ℤ)
    (c : chowCohomologyComponent (fieldChowSituation k)
      (gysinSystemOfInvertible (fieldChowSituation k)) sX p)
    (n : ℤ) (β : chowGroup (fieldChowSituation k) (𝟙 X ≫ sX) n) :
    c.cap (𝟙 X) n β =
      chowGroupDegreeEquiv (fieldChowSituation k) (pullback.fst (𝟙 X) (𝟙 X) ≫ sX)
        (by ring : ((d : ℤ) - p) + n - d = n - p)
        (chowGroupCongr (fieldChowSituation k) (by rw [Category.id_comp]) _
          (intersectionProduct (fieldChowSituation k) (fun _ _ ↦ rfl)
            (gysinSystemOfInvertible (fieldChowSituation k)) sX (𝟙 X) (𝟙 X) d
            (bivariantClassCongrBase (fieldChowSituation k)
              (gysinSystemOfInvertible (fieldChowSituation k)) (pullback.diagonal sX)
              (diagonal_comp_selfProductStructure (fieldChowSituation k) sX) rfl d D)
            ((d : ℤ) - p) n
            (chowGroupCongr (fieldChowSituation k) (Category.id_comp sX).symm ((d : ℤ) - p)
              (chowCohomologyCapFundamentalClass (fieldChowSituation k)
                (gysinSystemOfInvertible (fieldChowSituation k)) sX d p c) ⊗ₜ[ℤ] β))) := by
  have hback := smoothShiftBackward_smoothShiftForward (fieldChowSituation k) sX sX
    (𝟙 (fieldChowSituation k).S) (𝟙 X) sX (Category.id_comp sX) (Category.comp_id sX) d hd p D
    hcomm hD₂ c
  have hΞ : (smoothShiftCapIso (𝟙 X) sX (𝟙 X)).hom =
      (pullbackDiagonalMapIdIso (𝟙 X) (𝟙 X) sX).hom := by
    ext <;> simp
  have H1 := smoothShiftBackward_cap (fieldChowSituation k) sX sX (𝟙 (fieldChowSituation k).S)
    (𝟙 X) sX (Category.id_comp sX) (Category.comp_id sX) d p D
    (smoothShiftForward (fieldChowSituation k) sX sX (𝟙 (fieldChowSituation k).S) (𝟙 X) sX
      (Category.id_comp sX) (Category.comp_id sX) d hd p c) (𝟙 X) n β
    (pullbackDiagonalMapIdIso (𝟙 X) (𝟙 X) sX).hom (by simp) (by simp) (by
      rw [← hΞ, smoothShiftCapIso_hom_fst_assoc, pullback.diagonal_fst_assoc,
        smoothShift_diagonal_testMap_fst_eq_fst_assoc]
      simp only [Category.id_comp])
  rw [hback] at H1
  refine eq_of_heq (H1.trans ?_)
  refine HEq.trans ?_ ((chowGroupDegreeEquiv_heq _ _ _ _).trans (chowGroupCongr_heq _ _ _ _)).symm
  refine HEq.trans ?_ (heq_of_eq (intersectionProduct_apply (fieldChowSituation k)
    (fun _ _ ↦ rfl) _ sX (𝟙 X) (𝟙 X) _ _ _ _ _).symm)
  rw [properChowPushforward_eq_chowPushforwardOfIso]
  refine chowPushforwardOfIso_heq _ _ _
    (by rw [pullback.diagonal_fst_assoc]) (by rw [Category.id_comp])
    (by ring) ?_
  refine (D.cap_heq_congr _ (by ring) _ _ ?_).trans
    (bivariantClassCongrBase_cap (fieldChowSituation k)
      (gysinSystemOfInvertible (fieldChowSituation k)) (pullback.diagonal sX)
      (diagonal_comp_selfProductStructure (fieldChowSituation k) sX) rfl d D _ _ _ _
      HEq.rfl).symm
  refine (chowGroupCongr_heq _ _ _ _).trans (HEq.trans ?_ (chowGroupCongr_heq _ _ _ _).symm)
  -- the class `c ∘ g^*` towards the point caps as the exterior product with `c ∩ [X]_d`
  have hcap := BivariantClass.capBase_eq_chowExteriorProduct_of_field k sX (p + -(d : ℤ))
    (compStructureFlatPullbackClass (fieldChowSituation k) sX d hd p c) (𝟙 X ≫ sX) n β
  rw [BivariantClass.capBase_apply] at hcap
  have hΘ := chowCohomologyCapFundamentalClass_eq_bivariantToBaseEval (fieldChowSituation k) sX
    d hd p (schemeDeltaDimension_fieldChowSituation_base k) c
  have heval : bivariantToBaseEval (fieldChowSituation k)
      (gysinSystemOfInvertible (fieldChowSituation k)) sX (p + -(d : ℤ))
      (compStructureFlatPullbackClass (fieldChowSituation k) sX d hd p c) ≍
      chowGroupCongr (fieldChowSituation k) (Category.id_comp sX).symm ((d : ℤ) - p)
        (chowCohomologyCapFundamentalClass (fieldChowSituation k)
          (gysinSystemOfInvertible (fieldChowSituation k)) sX d p c) := by
    rw [hΘ]
    exact ((chowGroupCongr_heq _ _ _ _).trans (chowGroupDegreeEquiv_heq _ _ _ _)).symm
  refine (BivariantClass.congrHom_cap_heq (Category.id_comp sX) (Category.comp_id sX)
    (smoothShiftForward (fieldChowSituation k) sX sX (𝟙 (fieldChowSituation k).S) (𝟙 X) sX
      (Category.id_comp sX) (Category.comp_id sX) d hd p c) (𝟙 X ≫ sX) n _).symm.trans ?_
  refine (heq_of_eq hcap).trans ((chowGroupDegreeEquiv_heq _ _ _ _).trans ?_)
  exact chowExteriorProduct_tmul_heq_of_heq _ _ (Category.id_comp sX).symm _ (by ring) n _ _
    heval β

/-- **The action of `A^p(X)` on `CH_*(X)` is the intersection product with the value on
`[X]_d`.** Let `X` be flat of relative dimension `d` over a field, and let
`D ∈ A^d(X ⟶ X ×_k X)` be a class of the diagonal which commutes with every bivariant class over
`X ×_k X` and satisfies `D ∘ pr₂^* = 1`. Then for `c ∈ A^p(X)` and `β ∈ CH_n(X)`

  `c ∩ β = (c ∩ [X]_d) · β`   in   `CH_{n-p}(X)`,

the intersection product of Stacks 0FC0 being formed with `Δ^! = D` and read on `X` through the
collapse of `X ×_X X`, and the degrees `(d - p) + n - d` and `n - p` being matched.

The class `D` and its two properties are carried: for `X` smooth over `k` the Gysin class of the
diagonal has them, by Stacks 0FBP and Stacks 0FBS, and the form of Stacks 0FC2 for smooth `X`
instantiates `D` with that class. -/
theorem chowCohomologyCap_eq_intersectionProduct
    (hcomm : ∀ {Z₂ : Scheme.{u}} (f₂ : Z₂ ⟶ pullback sX sX) [LocallyOfFiniteType f₂] (p₂ : ℤ)
      (c₂ : BivariantClass (fieldChowSituation k) (gysinSystemOfInvertible (fieldChowSituation k))
        (f₂ ≫ (pullback.fst sX sX ≫ sX)) (pullback.fst sX sX ≫ sX) f₂ rfl p₂),
      BivariantCommute (fieldChowSituation k) (gysinSystemOfInvertible (fieldChowSituation k))
        (pullback.fst sX sX ≫ sX) (pullback.diagonal sX) f₂ d p₂ D c₂)
    (hD₂ : D.CompFlatPullbackEqOne (pullback.snd sX sX)
      (smoothShift_pullback_snd_comp_structureMorphism (fieldChowSituation k) sX
        (𝟙 (fieldChowSituation k).S) sX (Category.comp_id sX)) (pullback.diagonal_snd sX)
      (relativeDimension_pullback_snd sX sX d hd))
    (p : ℤ)
    (c : chowCohomologyComponent (fieldChowSituation k)
      (gysinSystemOfInvertible (fieldChowSituation k)) sX p)
    (n : ℤ) (β : chowGroup (fieldChowSituation k) sX n) :
    chowCohomologyCap (fieldChowSituation k) (gysinSystemOfInvertible (fieldChowSituation k)) sX p
        c n β =
      chowGroupDegreeEquiv (fieldChowSituation k) sX (by ring : ((d : ℤ) - p) + n - d = n - p)
        (chowGroupSelfProductUnitCollapse (fieldChowSituation k) sX (((d : ℤ) - p) + n - d)
          (intersectionProduct (fieldChowSituation k) (fun _ _ ↦ rfl)
            (gysinSystemOfInvertible (fieldChowSituation k)) sX (𝟙 X) (𝟙 X) d
            (bivariantClassCongrBase (fieldChowSituation k)
              (gysinSystemOfInvertible (fieldChowSituation k)) (pullback.diagonal sX)
              (diagonal_comp_selfProductStructure (fieldChowSituation k) sX) rfl d D)
            ((d : ℤ) - p) n
            (chowGroupCongr (fieldChowSituation k) (Category.id_comp sX).symm ((d : ℤ) - p)
              (chowCohomologyCapFundamentalClass (fieldChowSituation k)
                (gysinSystemOfInvertible (fieldChowSituation k)) sX d p c) ⊗ₜ[ℤ]
              chowGroupCongr (fieldChowSituation k) (Category.id_comp sX).symm n β))) := by
  simp only [chowCohomologyCap, AddMonoidHom.coe_comp, Function.comp_apply,
    AddEquiv.coe_toAddMonoidHom, chowGroupEquivOfIso_apply]
  rw [cap_id_eq_intersectionProduct k sX d hd D hcomm hD₂ p c n]
  refine eq_of_heq (HEq.trans ?_ (chowGroupDegreeEquiv_heq _ _ _ _).symm)
  rw [chowGroupSelfProductUnitCollapse, chowGroupEquivOfIso_apply]
  exact chowPushforwardOfIso_heq _ _ _ (by rw [Category.id_comp]) rfl (by ring)
    ((chowGroupDegreeEquiv_heq _ _ _ _).trans (chowGroupCongr_heq _ _ _ _))

/-- **Stacks 0FC2, second clause: composition of bivariant classes is the intersection
product.** Let `X` be flat of relative dimension `d` over a field, and let
`D ∈ A^d(X ⟶ X ×_k X)` be a class of the diagonal which commutes with every bivariant class over
`X ×_k X` and satisfies `D ∘ pr₂^* = 1`. Then the map `Θ : A^p(X) ⟶ CH_{d-p}(X)`,
`c ↦ c ∩ [X]_d`, carries the product `a · b` of `A^*(X)` (the composite of Stacks 0B75, whose
action is `a ∩ (b ∩ -)`) to the intersection product of Stacks 0FC0 formed with `Δ^! = D`:

  `Θ(a · b) = Θ(a) · Θ(b)`   in   `CH_{d-(p+q)}(X)`.

Indeed `Θ(a · b) = a ∩ (b ∩ [X]_d) = a ∩ Θ(b)`, which is `Θ(a) · Θ(b)` by
`Stacks.Chow.chowCohomologyCap_eq_intersectionProduct`.

The class `D` and its two properties are carried: for `X` smooth over `k` and equidimensional of
dimension `d` the Gysin class of the diagonal has them, by Stacks 0FBP and Stacks 0FBS, and the
form of Stacks 0FC2 for smooth `X` instantiates `D` with that class. -/
theorem chowCohomologyCapFundamentalClass_mulId
    (hcomm : ∀ {Z₂ : Scheme.{u}} (f₂ : Z₂ ⟶ pullback sX sX) [LocallyOfFiniteType f₂] (p₂ : ℤ)
      (c₂ : BivariantClass (fieldChowSituation k) (gysinSystemOfInvertible (fieldChowSituation k))
        (f₂ ≫ (pullback.fst sX sX ≫ sX)) (pullback.fst sX sX ≫ sX) f₂ rfl p₂),
      BivariantCommute (fieldChowSituation k) (gysinSystemOfInvertible (fieldChowSituation k))
        (pullback.fst sX sX ≫ sX) (pullback.diagonal sX) f₂ d p₂ D c₂)
    (hD₂ : D.CompFlatPullbackEqOne (pullback.snd sX sX)
      (smoothShift_pullback_snd_comp_structureMorphism (fieldChowSituation k) sX
        (𝟙 (fieldChowSituation k).S) sX (Category.comp_id sX)) (pullback.diagonal_snd sX)
      (relativeDimension_pullback_snd sX sX d hd))
    (p q : ℤ)
    (a : chowCohomologyComponent (fieldChowSituation k)
      (gysinSystemOfInvertible (fieldChowSituation k)) sX p)
    (b : chowCohomologyComponent (fieldChowSituation k)
      (gysinSystemOfInvertible (fieldChowSituation k)) sX q) :
    chowCohomologyCapFundamentalClass (fieldChowSituation k)
        (gysinSystemOfInvertible (fieldChowSituation k)) sX d (p + q)
        (a.mulId (fieldChowSituation k) sX b) =
      chowGroupDegreeEquiv (fieldChowSituation k) sX
        (by ring : ((d : ℤ) - p) + (d - q) - d = d - (p + q))
        (chowGroupSelfProductUnitCollapse (fieldChowSituation k) sX
          (((d : ℤ) - p) + (d - q) - d)
          (intersectionProduct (fieldChowSituation k) (fun _ _ ↦ rfl)
            (gysinSystemOfInvertible (fieldChowSituation k)) sX (𝟙 X) (𝟙 X) d
            (bivariantClassCongrBase (fieldChowSituation k)
              (gysinSystemOfInvertible (fieldChowSituation k)) (pullback.diagonal sX)
              (diagonal_comp_selfProductStructure (fieldChowSituation k) sX) rfl d D)
            ((d : ℤ) - p) ((d : ℤ) - q)
            (chowGroupCongr (fieldChowSituation k) (Category.id_comp sX).symm ((d : ℤ) - p)
              (chowCohomologyCapFundamentalClass (fieldChowSituation k)
                (gysinSystemOfInvertible (fieldChowSituation k)) sX d p a) ⊗ₜ[ℤ]
              chowGroupCongr (fieldChowSituation k) (Category.id_comp sX).symm ((d : ℤ) - q)
                (chowCohomologyCapFundamentalClass (fieldChowSituation k)
                  (gysinSystemOfInvertible (fieldChowSituation k)) sX d q b)))) := by
  have h1 := chowCohomologyCap_eq_intersectionProduct k sX d hd D hcomm hD₂ p a ((d : ℤ) - q)
    (chowCohomologyCapFundamentalClass (fieldChowSituation k)
      (gysinSystemOfInvertible (fieldChowSituation k)) sX d q b)
  refine eq_of_heq (HEq.trans ?_ (((heq_of_eq h1).trans (chowGroupDegreeEquiv_heq _ _ _ _)).trans
    (chowGroupDegreeEquiv_heq _ _ _ _).symm))
  rw [← chowCohomologyCap_fundamentalChowClass, ← chowCohomologyCap_fundamentalChowClass]
  refine (chowCohomologyCap_heq_idRule_ofGysinSystem _ _ sX (p + q) _ d _).trans ?_
  refine (BivariantClass.idRule_mulId _ sX a b (𝟙 X) d _).trans ?_
  refine HEq.trans ?_ (chowCohomologyCap_heq_idRule_ofGysinSystem _ _ sX p a _ _).symm
  refine IdentityCapRule.heq_congr _ sX _ rfl (by ring) ?_
  exact ((chowCohomologyCap_heq_idRule_ofGysinSystem _ _ sX q b d _).symm.trans
    (chowGroupCongr_heq _ _ _ _).symm)

end Product

end Stacks.Chow

end
