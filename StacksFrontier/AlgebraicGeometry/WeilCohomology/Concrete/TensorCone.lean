module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.Tensor
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.Associativity

/-!
# Products of pulled back classes on a product

Let `W = W₁ ×_k W₂` be a product of smooth schemes over a field `k`, with projections
`p₁ : W ⟶ W₁` and `p₂ : W ⟶ W₂`. For `a ∈ CH_*(W₁)` and `b ∈ CH_*(W₂)` the class
`p₁^* a · p₂^* b ∈ CH_*(W)` is the building block of both the tensor product of correspondences
(`c ⊗ c' = pr₁₃^* c · pr₂₄^* c'`) and the computations behind Stacks 0FG7. This file proves its
three rules, which together reduce the laws of the tensor product to the laws of the
intersection product:

* flat pullback: for morphisms of products `h = h₁ × h₂` with `h₁`, `h₂` flat,
  `h^*(p₁^* a · p₂^* b) = p₁^* h₁^* a · p₂^* h₂^* b`;
* products: `(p₁^* a · p₂^* b) · (p₁^* a' · p₂^* b') = p₁^*(a · a') · p₂^*(b · b')`;
* proper pushforward: for `h = h₁ × h₂` with `h₁`, `h₂` flat and proper,
  `h_*(p₁^* a · p₂^* b) = p₁^* h₁,* a · p₂^* h₂,* b`.

They come from Stacks 02RD (functoriality of flat pullback), 0FFB (flat pullback is
multiplicative), 0FC1 and the commutativity of the intersection product, Stacks 02RG (flat base
change) and the projection formula of Stacks 0FFC.

The statements are heterogeneous equalities: both sides are equal integers written differently
as degrees.

## References

* [Stacks Project, Tag 0FG7](https://stacks.math.columbia.edu/tag/0FG7)
* [Stacks Project, Tag 0FFB](https://stacks.math.columbia.edu/tag/0FFB)
* [Stacks Project, Tag 0FFC](https://stacks.math.columbia.edu/tag/0FFC)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace Stacks.WeilCohomology

section Cone

variable {k : Type u} [Field k] {Δ : DiagonalClassFamily k}

local notation "μ" =>
  selfIntersectionProduct (fieldChowSituation k)
      (Stacks.Chow.fieldChowSituation_dimensionFunction_of_isClosed k)
    (fieldGysinSystem k)

local notation "pb[" sA ", " sB ", " v ", " hv ", " r ", " hr ", " n "]" =>
  flatPullbackChow (fieldChowSituation k) sA sB v hv r hr n
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)

local notation "pf[" sA ", " sB ", " v ", " hv ", " n "]" =>
  properChowPushforward (fieldChowSituation k) sA sB v hv n
    (properPushforwardDescends _ _ _ _ _ _)

/-- **Stacks 02RD across a commuting square**: flat pullback along the two factorizations of a
commuting square of flat morphisms agrees, up to heterogeneous equality, with arbitrary relative
dimensions on the four sides. -/
theorem flatPullbackChow_heq_of_comp_eq {A B B' D : Scheme.{u}}
    (sA : A ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sA]
    (sB : B ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sB]
    (sB' : B' ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sB']
    (sD : D ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sD]
    (u : A ⟶ B) [LocallyOfFiniteType u] [Flat u] (y : B ⟶ D) [LocallyOfFiniteType y] [Flat y]
    (x : A ⟶ B') [LocallyOfFiniteType x] [Flat x] (v : B' ⟶ D) [LocallyOfFiniteType v] [Flat v]
    (hu : u ≫ sB = sA) (hy : y ≫ sD = sB) (hx : x ≫ sB' = sA) (hv : v ≫ sD = sB')
    {m n m' n' : ℕ} (hum : RelativeDimension u m) (hyn : RelativeDimension y n)
    (hxm : RelativeDimension x m') (hvn : RelativeDimension v n') (hcomm : u ≫ y = x ≫ v)
    (hdim : m + n = m' + n') (j : ℤ) (α : chowGroup (fieldChowSituation k) sD j) :
    pb[sA, sB, u, hu, m, hum, j + (n : ℤ)] (pb[sB, sD, y, hy, n, hyn, j] α) ≍
      pb[sA, sB', x, hx, m', hxm, j + (n' : ℤ)] (pb[sB', sD, v, hv, n', hvn, j] α) :=
  (flatPullbackChow_comp _ sA sB sD u y hu hy m n hum hyn j _ _
      (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) α).trans
    ((flatPullbackChow_heq_congr _ sA sD (u ≫ y) (x ≫ v) _ _ hcomm hdim _ _ rfl
      (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
      (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) α α
      HEq.rfl).trans
    (flatPullbackChow_comp _ sA sB' sD x v hx hv m' n' hxm hvn j _ _
      (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) α).symm)

/-- Flat pullback along a morphism `w = u ≫ f` is the iterated flat pullback along `f`, then `u`. -/
private theorem flatPullbackChow_heq_comp {A B D : Scheme.{u}}
    (sA : A ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sA]
    (sB : B ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sB]
    (sD : D ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sD]
    (w : A ⟶ D) [LocallyOfFiniteType w] [Flat w] (u : A ⟶ B) [LocallyOfFiniteType u] [Flat u]
    (f : B ⟶ D) [LocallyOfFiniteType f] [Flat f] (hw : w ≫ sD = sA) (hu : u ≫ sB = sA)
    (hf : f ≫ sD = sB) {r t n : ℕ} (hwr : RelativeDimension w r) (hut : RelativeDimension u t)
    (hfn : RelativeDimension f n) (hwuf : w = u ≫ f) (hr : r = t + n) (j : ℤ)
    (α : chowGroup (fieldChowSituation k) sD j) :
    pb[sA, sD, w, hw, r, hwr, j] α ≍
      pb[sA, sB, u, hu, t, hut, j + (n : ℤ)] (pb[sB, sD, f, hf, n, hfn, j] α) :=
  (flatPullbackChow_heq_congr _ sA sD w (u ≫ f) hw (by rw [Category.assoc, hf, hu]) hwuf hr hwr
    (RelativeDimension.comp_of_flat u f hut hfn) rfl
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) α α HEq.rfl).trans
    (flatPullbackChow_comp _ sA sB sD u f hu hf t n hut hfn j _ _
      (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) α).symm

/-- **Flat pullback of a product of pulled back classes**: for a commuting square of products
`h ≫ q₁ = p₁ ≫ h₁`, `h ≫ q₂ = p₂ ≫ h₂` of flat morphisms,
`h^*(q₁^* a · q₂^* b) = p₁^* h₁^* a · p₂^* h₂^* b`. -/
theorem flatPullbackChow_selfIntersectionProduct_heq (hmul : Δ.FlatPullbackMul)
    {V V₁ V₂ W W₁ W₂ : Scheme.{u}} (sV : V ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sV]
    [Smooth sV] (sV₁ : V₁ ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sV₁]
    (sV₂ : V₂ ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sV₂]
    (sW : W ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW] [Smooth sW] [IsSeparated sW]
    (sW₁ : W₁ ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW₁]
    (sW₂ : W₂ ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW₂]
    (q₁ : V ⟶ V₁) [LocallyOfFiniteType q₁] [Flat q₁] (q₂ : V ⟶ V₂) [LocallyOfFiniteType q₂]
    [Flat q₂] (p₁ : W ⟶ W₁) [LocallyOfFiniteType p₁] [Flat p₁] (p₂ : W ⟶ W₂)
    [LocallyOfFiniteType p₂] [Flat p₂] (h : W ⟶ V) [LocallyOfFiniteType h] [Flat h]
    (h₁ : W₁ ⟶ V₁) [LocallyOfFiniteType h₁] [Flat h₁] (h₂ : W₂ ⟶ V₂) [LocallyOfFiniteType h₂]
    [Flat h₂] (hq₁ : q₁ ≫ sV₁ = sV) (hq₂ : q₂ ≫ sV₂ = sV) (hp₁ : p₁ ≫ sW₁ = sW)
    (hp₂ : p₂ ≫ sW₂ = sW) (hh : h ≫ sV = sW) (hh₁ : h₁ ≫ sV₁ = sW₁) (hh₂ : h₂ ≫ sV₂ = sW₂)
    (hc₁ : h ≫ q₁ = p₁ ≫ h₁) (hc₂ : h ≫ q₂ = p₂ ≫ h₂)
    {nq₁ nq₂ np₁ np₂ t t₁ t₂ N M : ℕ} (hq₁d : RelativeDimension q₁ nq₁)
    (hq₂d : RelativeDimension q₂ nq₂) (hp₁d : RelativeDimension p₁ np₁)
    (hp₂d : RelativeDimension p₂ np₂) (ht : RelativeDimension h t)
    (ht₁ : RelativeDimension h₁ t₁) (ht₂ : RelativeDimension h₂ t₂)
    (hN : RelativeDimension sV N) (hM' : RelativeDimension sW M) (hM : M = t + N)
    (e₁ : t + nq₁ = np₁ + t₁) (e₂ : t + nq₂ = np₂ + t₂) (i j : ℤ)
    (a : chowGroup (fieldChowSituation k) sV₁ i) (b : chowGroup (fieldChowSituation k) sV₂ j) :
    pb[sW, sV, h, hh, t, ht, (i + nq₁) + (j + nq₂) - N]
        (μ sV N (Δ sV N hN) (i + nq₁) (j + nq₂) (pb[sV, sV₁, q₁, hq₁, nq₁, hq₁d, i] a)
          (pb[sV, sV₂, q₂, hq₂, nq₂, hq₂d, j] b)) ≍
      μ sW M (Δ sW M hM') (i + t₁ + np₁) (j + t₂ + np₂)
        (pb[sW, sW₁, p₁, hp₁, np₁, hp₁d, i + t₁] (pb[sW₁, sV₁, h₁, hh₁, t₁, ht₁, i] a))
        (pb[sW, sW₂, p₂, hp₂, np₂, hp₂d, j + t₂] (pb[sW₂, sV₂, h₂, hh₂, t₂, ht₂, j] b)) := by
  refine (hmul.heq sV sW h hh hM ht hN hM' _ _ _ _).trans ?_
  exact selfIntersectionProduct_heq _ _ _ _ rfl HEq.rfl (by omega)
    (by omega)
    (flatPullbackChow_heq_of_comp_eq _ _ _ _ h q₁ p₁ h₁ hh hq₁ hp₁ hh₁ ht hq₁d hp₁d ht₁ hc₁ e₁ i a)
    (flatPullbackChow_heq_of_comp_eq _ _ _ _ h q₂ p₂ h₂ hh hq₂ hp₂ hh₂ ht hq₂d hp₂d ht₂ hc₂ e₂ j b)

/-- **The middle-four interchange of the intersection product**, from associativity and
commutativity: `(x · y) · (x' · y') = (x · x') · (y · y')`. -/
theorem selfIntersectionProduct_middleFour_heq (hassoc : Δ.IntersectionAssoc)
    (hsymm : Δ.IsSymmetric) {W : Scheme.{u}} (sW : W ⟶ (fieldChowSituation k).S)
    [LocallyOfFiniteType sW] [Smooth sW] [IsSeparated sW] {N : ℕ} (hN : RelativeDimension sW N)
    (i j i' j' : ℤ) (x : chowGroup (fieldChowSituation k) sW i)
    (y : chowGroup (fieldChowSituation k) sW j) (x' : chowGroup (fieldChowSituation k) sW i')
    (y' : chowGroup (fieldChowSituation k) sW j') :
    μ sW N (Δ sW N hN) (i + j - N) (i' + j' - N) (μ sW N (Δ sW N hN) i j x y)
        (μ sW N (Δ sW N hN) i' j' x' y') ≍
      μ sW N (Δ sW N hN) (i + i' - N) (j + j' - N) (μ sW N (Δ sW N hN) i i' x x')
        (μ sW N (Δ sW N hN) j j' y y') := by
  have hs : ∀ (a b : ℤ) (u : chowGroup (fieldChowSituation k) sW a)
      (v : chowGroup (fieldChowSituation k) sW b),
      μ sW N (Δ sW N hN) a b u v ≍ μ sW N (Δ sW N hN) b a v u := fun a b u v ↦
    (heq_of_eq (hsymm sW N hN a b u v)).trans (chowGroupDegreeEquiv_heq _ _ _ _)
  -- `y · (x' · y') = x' · (y · y')`
  have h₁ : μ sW N (Δ sW N hN) j (i' + j' - N) y (μ sW N (Δ sW N hN) i' j' x' y') ≍
      μ sW N (Δ sW N hN) i' (j + j' - N) x' (μ sW N (Δ sW N hN) j j' y y') :=
    (hassoc.heq sW hN j i' j' y x' y').symm.trans
      ((selfIntersectionProduct_heq _ _ _ _ rfl HEq.rfl (by ring) rfl (hs j i' y x')
        HEq.rfl).trans (hassoc.heq sW hN i' j j' x' y y'))
  refine (hassoc.heq sW hN i j _ x y _).trans ?_
  refine HEq.trans ?_ (hassoc.heq sW hN i i' _ x x' _).symm
  exact selfIntersectionProduct_heq _ _ _ _ rfl HEq.rfl rfl (by ring) HEq.rfl h₁

/-- **Product of two products of pulled back classes**:
`(p₁^* a · p₂^* b) · (p₁^* a' · p₂^* b') = p₁^*(a · a') · p₂^*(b · b')` on `W`, for flat
`p₁ : W ⟶ W₁` and `p₂ : W ⟶ W₂`. -/
theorem selfIntersectionProduct_pullback_pullback_heq (hmul : Δ.FlatPullbackMul)
    (hassoc : Δ.IntersectionAssoc) (hsymm : Δ.IsSymmetric) {W W₁ W₂ : Scheme.{u}}
    (sW : W ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW] [Smooth sW] [IsSeparated sW]
    (sW₁ : W₁ ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW₁] [Smooth sW₁]
    [IsSeparated sW₁]
    (sW₂ : W₂ ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW₂] [Smooth sW₂]
    [IsSeparated sW₂]
    (p₁ : W ⟶ W₁) [LocallyOfFiniteType p₁] [Flat p₁] (p₂ : W ⟶ W₂) [LocallyOfFiniteType p₂]
    [Flat p₂] (hp₁ : p₁ ≫ sW₁ = sW) (hp₂ : p₂ ≫ sW₂ = sW) {n₁ n₂ N₁ N₂ M : ℕ}
    (hp₁d : RelativeDimension p₁ n₁) (hp₂d : RelativeDimension p₂ n₂)
    (hN₁ : RelativeDimension sW₁ N₁) (hN₂ : RelativeDimension sW₂ N₂)
    (hM : RelativeDimension sW M) (e₁ : M = n₁ + N₁) (e₂ : M = n₂ + N₂) (i j i' j' : ℤ)
    (a : chowGroup (fieldChowSituation k) sW₁ i) (b : chowGroup (fieldChowSituation k) sW₂ j)
    (a' : chowGroup (fieldChowSituation k) sW₁ i')
    (b' : chowGroup (fieldChowSituation k) sW₂ j') :
    μ sW M (Δ sW M hM) (i + n₁ + (j + n₂) - M) (i' + n₁ + (j' + n₂) - M)
        (μ sW M (Δ sW M hM) (i + n₁) (j + n₂) (pb[sW, sW₁, p₁, hp₁, n₁, hp₁d, i] a)
          (pb[sW, sW₂, p₂, hp₂, n₂, hp₂d, j] b))
        (μ sW M (Δ sW M hM) (i' + n₁) (j' + n₂) (pb[sW, sW₁, p₁, hp₁, n₁, hp₁d, i'] a')
          (pb[sW, sW₂, p₂, hp₂, n₂, hp₂d, j'] b')) ≍
      μ sW M (Δ sW M hM) (i + i' - N₁ + n₁) (j + j' - N₂ + n₂)
        (pb[sW, sW₁, p₁, hp₁, n₁, hp₁d, i + i' - N₁] (μ sW₁ N₁ (Δ sW₁ N₁ hN₁) i i' a a'))
        (pb[sW, sW₂, p₂, hp₂, n₂, hp₂d, j + j' - N₂] (μ sW₂ N₂ (Δ sW₂ N₂ hN₂) j j' b b')) := by
  refine (selfIntersectionProduct_middleFour_heq hassoc hsymm sW hM _ _ _ _ _ _ _ _).trans ?_
  exact selfIntersectionProduct_heq _ _ _ _ rfl HEq.rfl (by omega)
    (by omega) (hmul.heq sW₁ sW p₁ hp₁ e₁ hp₁d hN₁ hM i i' a a').symm
    (hmul.heq sW₂ sW p₂ hp₂ e₂ hp₂d hN₂ hM j j' b b').symm

/-- **Proper pushforward of a product of pulled back classes**: for products
`W = W₁ ×_k W₂` and `V = V₁ ×_k V₂` and a morphism `h : W ⟶ V` with `h ≫ q₁ = p₁ ≫ h₁` and
`h ≫ q₂ = p₂ ≫ h₂`, where `h₁` and `h₂` are flat and proper,
`h_*(p₁^* a · p₂^* b) = q₁^* h₁,* a · q₂^* h₂,* b`.

The proof factors `h` through `M = V₁ ×_k W₂` as `h₁ × 1` followed by `1 × h₂`. Each step is
Stacks 02RG on a cartesian square, followed by the projection formula of Stacks 0FFC. -/
theorem properChowPushforward_selfIntersectionProduct_heq (hproj : Δ.ProjectionFormula)
    {V V₁ V₂ W W₁ W₂ : Scheme.{u}} (sV : V ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sV]
    [Smooth sV] [IsSeparated sV] (sV₁ : V₁ ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sV₁]
    [Smooth sV₁] [IsSeparated sV₁]
    (sV₂ : V₂ ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sV₂]
    (sW : W ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW] [Smooth sW] [IsSeparated sW]
    (sW₁ : W₁ ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW₁]
    (sW₂ : W₂ ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW₂] [Smooth sW₂]
    [IsSeparated sW₂] (q₁ : V ⟶ V₁) (q₂ : V ⟶ V₂) (p₁ : W ⟶ W₁) (p₂ : W ⟶ W₂)
    [LocallyOfFiniteType q₁] [Flat q₁] [LocallyOfFiniteType q₂] [Flat q₂]
    [LocallyOfFiniteType p₁] [Flat p₁] [LocallyOfFiniteType p₂] [Flat p₂]
    (hV : IsPullback q₁ q₂ sV₁ sV₂) (hW : IsPullback p₁ p₂ sW₁ sW₂)
    (h : W ⟶ V) [IsProper h] (h₁ : W₁ ⟶ V₁) [IsProper h₁] [Flat h₁] (h₂ : W₂ ⟶ V₂) [IsProper h₂]
    [Flat h₂] (hq₁ : q₁ ≫ sV₁ = sV) (hq₂ : q₂ ≫ sV₂ = sV) (hp₁ : p₁ ≫ sW₁ = sW)
    (hp₂ : p₂ ≫ sW₂ = sW) (hh : h ≫ sV = sW) (hh₁ : h₁ ≫ sV₁ = sW₁) (hh₂ : h₂ ≫ sV₂ = sW₂)
    (hc₁ : h ≫ q₁ = p₁ ≫ h₁) (hc₂ : h ≫ q₂ = p₂ ≫ h₂)
    {n₁ n₂ m₁ m₂ t₁ t₂ NV NW : ℕ} (hq₁d : RelativeDimension q₁ n₂)
    (hq₂d : RelativeDimension q₂ n₁) (hp₁d : RelativeDimension p₁ m₂)
    (hp₂d : RelativeDimension p₂ m₁) (ht₁ : RelativeDimension h₁ t₁)
    (ht₂ : RelativeDimension h₂ t₂) (hn₁ : RelativeDimension sV₁ n₁)
    (hm₂ : RelativeDimension sW₂ m₂) (hNV : RelativeDimension sV NV)
    (hNW : RelativeDimension sW NW) (e₁ : m₁ = t₁ + n₁) (e₂ : m₂ = t₂ + n₂)
    (eV : NV = n₂ + n₁) (eW : NW = m₂ + m₁) (i j : ℤ)
    (a : chowGroup (fieldChowSituation k) sW₁ i) (b : chowGroup (fieldChowSituation k) sW₂ j) :
    pf[sW, sV, h, hh, (i + m₂) + (j + m₁) - NW]
        (μ sW NW (Δ sW NW hNW) (i + m₂) (j + m₁) (pb[sW, sW₁, p₁, hp₁, m₂, hp₁d, i] a)
          (pb[sW, sW₂, p₂, hp₂, m₁, hp₂d, j] b)) ≍
      μ sV NV (Δ sV NV hNV) (i + n₂) (j + n₁)
        (pb[sV, sV₁, q₁, hq₁, n₂, hq₁d, i] (pf[sW₁, sV₁, h₁, hh₁, i] a))
        (pb[sV, sV₂, q₂, hq₂, n₁, hq₂d, j] (pf[sW₂, sV₂, h₂, hh₂, j] b)) := by
  -- the intermediate product `M = V₁ ×_k W₂`
  set f₁ := Limits.pullback.fst sV₁ sW₂
  set f₂ := Limits.pullback.snd sV₁ sW₂
  have hsM : IsPullback f₁ f₂ sV₁ sW₂ := IsPullback.of_hasPullback sV₁ sW₂
  have hf₂ : f₂ ≫ sW₂ = f₁ ≫ sV₁ := Limits.pullback.condition.symm
  set u : W ⟶ Limits.pullback sV₁ sW₂ :=
    Limits.pullback.lift (p₁ ≫ h₁) p₂ (by rw [Category.assoc, hh₁, hp₁, hp₂])
  set v : Limits.pullback sV₁ sW₂ ⟶ V := hV.lift f₁ (f₂ ≫ h₂) (by rw [Category.assoc, hh₂, hf₂])
  have hu₁ : u ≫ f₁ = p₁ ≫ h₁ := Limits.pullback.lift_fst _ _ _
  have hu₂ : u ≫ f₂ = p₂ := Limits.pullback.lift_snd _ _ _
  have hv₁ : v ≫ q₁ = f₁ := hV.lift_fst _ _ _
  have hv₂ : v ≫ q₂ = f₂ ≫ h₂ := hV.lift_snd _ _ _
  have huv : u ≫ v = h := hV.hom_ext (by rw [Category.assoc, hv₁, hu₁, hc₁])
    (by rw [Category.assoc, hv₂, ← Category.assoc, hu₂, hc₂])
  -- the two cartesian squares
  have hS₁ : IsPullback u p₁ f₁ h₁ :=
    IsPullback.of_right (by rw [hu₂, hh₁]; exact hW.flip) hu₁ hsM.flip
  have hS₂ : IsPullback v f₂ q₂ h₂ :=
    IsPullback.of_right (by rw [hv₁, hh₂]; exact hsM) hv₂ hV
  have : IsProper u := MorphismProperty.of_isPullback hS₁.flip inferInstance
  have : Flat u := MorphismProperty.of_isPullback hS₁.flip inferInstance
  have : IsProper v := MorphismProperty.of_isPullback hS₂.flip inferInstance
  have : Flat v := MorphismProperty.of_isPullback hS₂.flip inferInstance
  have hud : RelativeDimension u t₁ := RelativeDimension.of_isPullback hS₁.flip ht₁
  have hvd : RelativeDimension v t₂ := RelativeDimension.of_isPullback hS₂.flip ht₂
  have hf₁d : RelativeDimension f₁ m₂ := RelativeDimension.of_isPullback hsM.flip hm₂
  have hf₂d : RelativeDimension f₂ n₁ := RelativeDimension.of_isPullback hsM hn₁
  have hNM : RelativeDimension (f₁ ≫ sV₁) (m₂ + n₁) := RelativeDimension.comp_of_flat _ _ hf₁d hn₁
  have hus : u ≫ (f₁ ≫ sV₁) = sW := by rw [← Category.assoc, hu₁, Category.assoc, hh₁, hp₁]
  have hvs : v ≫ sV = f₁ ≫ sV₁ := by rw [← hq₁, ← Category.assoc, hv₁]
  -- `h_* = v_* u_*`
  rw [properChowPushforward_comp_apply _ sW (f₁ ≫ sV₁) sV u v h huv hus hvs hh _
    (properPushforwardDescends _ _ _ _ _ _) (properPushforwardDescends _ _ _ _ _ _)
    (properPushforwardDescends _ _ _ _ _ _)]
  -- the step along `u = h₁ × 1`
  have hb := flatPullbackChow_heq_comp sW (f₁ ≫ sV₁) sW₂ p₂ u f₂ hp₂ hus hf₂ hp₂d hud hf₂d
    hu₂.symm (by omega) j b
  have hU : pf[sW, f₁ ≫ sV₁, u, hus, (i + m₂) + (j + m₁) - NW]
      (μ sW NW (Δ sW NW hNW) (i + m₂) (j + m₁) (pb[sW, sW₁, p₁, hp₁, m₂, hp₁d, i] a)
        (pb[sW, sW₂, p₂, hp₂, m₁, hp₂d, j] b)) ≍
      μ (f₁ ≫ sV₁) (m₂ + n₁) (Δ (f₁ ≫ sV₁) (m₂ + n₁) hNM) (i + m₂) (j + n₁)
        (pb[f₁ ≫ sV₁, sV₁, f₁, rfl, m₂, hf₁d, i] (pf[sW₁, sV₁, h₁, hh₁, i] a))
        (pb[f₁ ≫ sV₁, sW₂, f₂, hf₂, n₁, hf₂d, j] b) := by
    refine (properChowPushforward_heq_congr _ _ _ _ _ (by omega)
      (properPushforwardDescends _ _ _ _ _ _) (properPushforwardDescends _ _ _ _ _ _) _ _
      (selfIntersectionProduct_heq _ _ _ _ rfl HEq.rfl rfl (by omega) HEq.rfl
        hb)).trans ?_
    refine (hproj.heq_right (f₁ ≫ sV₁) sW u hus (by omega) hud hNM hNW _ _ _ _).symm.trans ?_
    refine selfIntersectionProduct_heq _ _ _ _ rfl HEq.rfl rfl rfl ?_ HEq.rfl
    exact heq_of_eq (flatPullbackChow_properChowPushforward_of_isProper (fieldChowSituation k)
      sW₁ sV₁ sW (f₁ ≫ sV₁) h₁ f₁ p₁ u hS₁.flip hh₁ rfl hp₁ m₂ hf₁d i a).symm
  -- the step along `v = 1 × h₂`
  have ha := flatPullbackChow_heq_comp (f₁ ≫ sV₁) sV sV₁ f₁ v q₁ rfl hvs hq₁ hf₁d hvd hq₁d
    hv₁.symm (by omega) i (pf[sW₁, sV₁, h₁, hh₁, i] a)
  refine (properChowPushforward_heq_congr _ _ _ _ _ (by omega)
    (properPushforwardDescends _ _ _ _ _ _) (properPushforwardDescends _ _ _ _ _ _) _ _
    hU).trans ?_
  refine (properChowPushforward_heq_congr _ _ _ _ _ (by omega)
    (properPushforwardDescends _ _ _ _ _ _) (properPushforwardDescends _ _ _ _ _ _) _ _
    (selfIntersectionProduct_heq _ _ _ _ rfl HEq.rfl (by omega) rfl ha
      HEq.rfl)).trans ?_
  refine (hproj.heq_left sV (f₁ ≫ sV₁) v hvs (by omega) hvd hNV hNM _ _ _ _).symm.trans ?_
  refine selfIntersectionProduct_heq _ _ _ _ rfl HEq.rfl rfl rfl HEq.rfl ?_
  exact heq_of_eq (flatPullbackChow_properChowPushforward_of_isProper (fieldChowSituation k)
    sW₂ sV₂ (f₁ ≫ sV₁) sV h₂ q₂ f₂ v hS₂.flip hh₂ hq₂ hf₂ n₁ hq₂d j b).symm

end Cone

end Stacks.WeilCohomology

end
