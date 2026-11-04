module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinCompatibility
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinProperPushforwardGenericPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.InfiniteSumsRationalEquivalence

/-!
# Stacks 0ER5 in the Chow group, assembled from its prime cycles by Stacks 0EQ8

In Situation 0EDT let `X/B` and `X'/B` be good, let `f : X' ⟶ X` be proper, let
`(ℒ, s, i : E → X)` be as in Definition 0ER1 and form the diagram of Remark 0ER3

```
E' --i'--> X'
|          |
g          f
|          |
v          v
E  --i-->  X
```

**Stacks 0ER5** is the identity `i^* f_* α' = g_* (i')^* α'` **in `CH_k(E)`**, for every
`(k+1)`-cycle `α'` on `X'`.  This module proves that identity from the source's two prime-cycle
cases, the passage to a general cycle being Stacks 0EQ8 (Remark 82.15.3):

* the first case, `W' ⊄ D'`, is an identity of cycles; at the canonical component rule it is the
  degree count `deg(W'/W) · m_T(E ∩ W) = ∑_{T'} m_{T'}(E' ∩ W') · deg(T'/T)`;
* the second case, `W' ⊆ D'`, is an identity in `CH_k(W)`, the cap product of Stacks 0EQJ being
  defined up to rational equivalence: the second assertion of Stacks 0EQS,
  `f_*(c₁(ℒ|_{W'}) ∩ [W']) = c₁(ℒ|_W) ∩ [W]`, for the proper dominant morphism `W' → W`.

## Main definitions

* `AlgebraicGeometry.Space.gysinProperPushforwardTerm`,
  `AlgebraicGeometry.Space.properPushforwardGysinTerm`: the `W'`-th summands `n_{W'} i^* f_*[W']`
  and `n_{W'} g_* (i')^*[W']` of the two sides, as `k`-cycles on `E`.
* `AlgebraicGeometry.Space.gysinProperPushforwardTermSupport`: the closed subset
  `|i|^{-1}(closure(|f|(|W'|)))` of `|E|` carrying both summands.

## Main results

* `AlgebraicGeometry.Space.locallyFinite_gysinProperPushforwardTermSupport`: those subsets form
  a locally finite collection, by Stacks 0ENZ for `f` and Stacks 0EP6 for `i`.
* `AlgebraicGeometry.Space.locallyFiniteCycleSum_gysinProperPushforwardTerm`,
  `AlgebraicGeometry.Space.locallyFiniteCycleSum_properPushforwardGysinTerm`: the two sums are
  `i^* f_* α'` and `g_* (i')^* α'`.
* `AlgebraicGeometry.Space.chowClass_gysinCycleMap_properPushforward_eq_of_rationallyEquivalentOn`
  and `AlgebraicGeometry.Space.chowClass_gysinCycleMap_properPushforward_eq_of_contained`:
  **Stacks 0ER5 in `CH_k(E)`**, from the source's two prime-cycle cases.
* `AlgebraicGeometry.Space.chowClass_gysinCycleMap_properPushforward_eq_of_genericPointData`:
  the same at the canonical component rules, with the source's first case replaced by a
  generic-point dictionary.

## Implementation notes

The second case is false as an identity of cycles at the canonical component rule
`AlgebraicGeometry.Space.canonicalGysinComponentRule`, which takes the cycle `div_{ℒ|_W}(t_W)` of a
regular meromorphic section `t_W` chosen on each `W` independently.  Indeed `t_{W'}` and the
pullback of `t_W` to `W'` differ by a nonzero rational function `u ∈ R(W')^*`, so
`f_*div(t_{W'}) = f_*div(f^*t_W) + f_*div(u) = deg(W'/W) · div(t_W) + div(Nm_{R(W')/R(W)}(u))`
by Stacks 0EQ4, and the second summand is a nonzero principal divisor in general.  This is why the
identity is stated in `CH_k(E)` rather than in `Z_k(E)`; the same holds for Stacks 0ER6, which the
source also states in a Chow group.

The right-hand side `g_* (i')^* α'` uses proper pushforward on Chow groups (Stacks 0EQC). It is
the class of the cycle-level pushforward of the representative `∑ n_{W'} (i')^*[W']` of
`(i')^* α'` given by Stacks 0ER1(2), since the pushforward of a class is the class of the
pushforward of a representative.

The witness universe of rational equivalence is `u + 1`, the universe of
`AlgebraicGeometry.Space.IntegralClosedSubspace`: Stacks 0EQ8 as formalised here indexes the
combined family of witnesses by `Σ i, J i` for `i` ranging over the index type of the locally
finite collection, here the integral closed subspaces of `X'`.

## References

* [Stacks Project, Tag 0ER5](https://stacks.math.columbia.edu/tag/0ER5)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0ENZ](https://stacks.math.columbia.edu/tag/0ENZ)
* [Stacks Project, Tag 0EP1](https://stacks.math.columbia.edu/tag/0EP1)
* [Stacks Project, Tag 0EP6](https://stacks.math.columbia.edu/tag/0EP6)
* [Stacks Project, Tag 0EQ4](https://stacks.math.columbia.edu/tag/0EQ4)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQ8](https://stacks.math.columbia.edu/tag/0EQ8)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Tag 0EQS](https://stacks.math.columbia.edu/tag/0EQS)
* [Stacks Project, Tag 0ER1](https://stacks.math.columbia.edu/tag/0ER1)
* [Stacks Project, Tag 0ER3](https://stacks.math.columbia.edu/tag/0ER3)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Rational equivalence on a subset, for equal cycles -/

/-- Two equal cycles are rationally equivalent on any subset of `|X|`, via the empty family of
witnesses. -/
theorem rationallyEquivalentOn_of_eq {D : BaseSpaceDimensionSituation.{u}}
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (k : ℤ) (T : Set (points D.site D.base D.base_mem X))
    {α β : CycleGroup D sX k} (h : α = β) :
    RationallyEquivalentOn.{v} D sX hX k T α β := by
  refine ⟨PEmpty.{v + 1}, (fun j => nomatch j), locallyFinite_of_finite _,
    (fun j => nomatch j), (fun j => nomatch j), (fun j => nomatch j), (fun j => nomatch j),
    Subtype.ext ?_⟩
  have hzero : cycleFamilySumCoeff D sX hX (fun j : PEmpty.{v + 1} => nomatch j) k
      (fun j => nomatch j) = 0 := funext fun _ => finsum_of_isEmpty _
  rw [h, sub_self]
  exact hzero.symm


/-! ### The summands of the two sides, and the subsets of `|E|` carrying them -/

/-- The closed subset `|i|^{-1}(closure(|f|(|W'|)))` of `|E|` carrying both `W'`-th summands of
Stacks 0ER5.  It is the inverse image along `i : E → X` of the point set of the closure of the
image of `W'` under `f`, which is the integral closed subspace `W` of the source's proof. -/
def gysinProperPushforwardTermSupport (D : BaseSpaceDimensionSituation.{u})
    {X X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (f : X' ⟶ X)
    (E : ClosedSubspaces D.site D.base D.base_mem X) {p' : X' ⟶ D.space} {k : ℤ}
    (α' : CycleGroup D p' (k + 1))
    (W' : IntegralClosedSubspace D.site D.base D.base_mem X') :
    Set (points D.site D.base D.base_mem E.1.toFunctor) :=
  pointsMap D.site D.base D.base_mem E.1.toFunctor E.1.ι ⁻¹'
    closure (pointsMap D.site D.base D.base_mem X' f '' cycleSupportFamily D α'.1 W')

section ChowClass

variable (D : BaseSpaceDimensionSituation.{u})
    {X X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p) (p' : X' ⟶ D.space) (hp' : D.IsGood p')
    {f : X' ⟶ X} (hfbase : f ≫ p = p')
    (hfqc : IsQuasiCompact D.site D.base D.base_mem f)
    (E : ClosedSubspaces D.site D.base D.base_mem X) (hE : D.IsGood (E.1.ι ≫ p))
    (E' : ClosedSubspaces D.site D.base D.base_mem X') (hE' : D.IsGood (E'.1.ι ≫ p'))
    {g : E'.1.toFunctor ⟶ E.1.toFunctor} (hgbase : g ≫ (E.1.ι ≫ p) = E'.1.ι ≫ p')
    (hgqc : IsQuasiCompact D.site D.base D.base_mem g)
    (k : ℤ) (rule : GysinComponentRule D p E k) (rule' : GysinComponentRule D p' E' k)
    (α' : CycleGroup D p' (k + 1))

/-- The `W'`-th summand `n_{W'} · i^* f_*[W']` of the left-hand side of Stacks 0ER5, as a
`k`-cycle on `E`; it is zero when the coefficient `n_{W'} = α'_{W'}` is. -/
def gysinProperPushforwardTerm (W' : IntegralClosedSubspace D.site D.base D.base_mem X') :
    CycleGroup D (E.1.ι ≫ p) k :=
  if h : α'.1 W' = 0 then 0 else
    α'.1 W' • gysinCycleMap D p E hE k rule
      (properCyclePushforward D p' hp' p hp hfbase hfqc (k + 1)
        (integralCycle D p' (k + 1) W' (α'.2.2 W' h)))

/-- The `W'`-th summand `n_{W'} · g_* (i')^*[W']` of the right-hand side of Stacks 0ER5, as a
`k`-cycle on `E`; it is zero when the coefficient `n_{W'} = α'_{W'}` is. -/
def properPushforwardGysinTerm (W' : IntegralClosedSubspace D.site D.base D.base_mem X') :
    CycleGroup D (E.1.ι ≫ p) k :=
  if h : α'.1 W' = 0 then 0 else
    α'.1 W' • properCyclePushforward D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE hgbase hgqc k
      (gysinCycleMap D p' E' hE' k rule'
        (integralCycle D p' (k + 1) W' (α'.2.2 W' h)))

include hp hp' hfbase hfqc hE hE' hgbase hgqc rule rule'

/-- The coefficient of `n_{W'} · i^* f_*[W']` at an integral closed subspace `T ⊆ E`. -/
theorem gysinProperPushforwardTerm_coe
    (W' : IntegralClosedSubspace D.site D.base D.base_mem X')
    (T : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor) :
    (gysinProperPushforwardTerm D p hp p' hp' hfbase hfqc E hE k rule α' W').1 T =
      α'.1 W' * ∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem X,
        properCycleMult D p' hp' p hp f W' W *
          (gysinComponentCycle D p E hE k rule W).1 T := by
  rw [gysinProperPushforwardTerm]
  by_cases h : α'.1 W' = 0
  · rw [dif_pos h, h, zero_mul]
    rfl
  · rw [dif_neg h, AddSubgroup.coe_zsmul, Pi.smul_apply, smul_eq_mul,
      gysinCoeff_properPushforward_integralCycle D p hp p' hp' hfbase hfqc E hE E' hE' hgbase
        hgqc k rule rule' (α'.2.2 W' h) T]

/-- The coefficient of `n_{W'} · g_* (i')^*[W']` at an integral closed subspace `T ⊆ E`. -/
theorem properPushforwardGysinTerm_coe
    (W' : IntegralClosedSubspace D.site D.base D.base_mem X')
    (T : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor) :
    (properPushforwardGysinTerm D p p' E hE E' hE' hgbase hgqc k rule' α' W').1 T =
      α'.1 W' * ∑ᶠ T' : IntegralClosedSubspace D.site D.base D.base_mem E'.1.toFunctor,
        (gysinComponentCycle D p' E' hE' k rule' W').1 T' *
          properCycleMult D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE g T' T := by
  rw [properPushforwardGysinTerm]
  by_cases h : α'.1 W' = 0
  · rw [dif_pos h, h, zero_mul]
    rfl
  · rw [dif_neg h, AddSubgroup.coe_zsmul, Pi.smul_apply, smul_eq_mul,
      properPushforward_gysinCoeff_integralCycle D p hp p' hp' hfbase hfqc E hE E' hE' hgbase
        hgqc k rule rule' (α'.2.2 W' h) T]

omit hE' hgbase hgqc rule rule' in
/-- **Stacks 0ENZ and Stacks 0EP6.** The subsets of `|E|` carrying the summands form a locally
finite collection: the closures of the images under `|f|` of the supports of `α'` are locally
finite on `|X|` by Stacks 0ENZ, and their inverse images along `|i|` are locally finite on `|E|`
by Stacks 0EP6. -/
theorem locallyFinite_gysinProperPushforwardTermSupport :
    LocallyFinite (gysinProperPushforwardTermSupport D f E α') := by
  refine locallyFinite_preimage_pointsMap D.site D.base D.base_mem hE.1 hp.1 E.1.ι _ ?_
  exact (locallyFinite_closure_image_pointsMap D p' hp' p hp hfbase hfqc
    (cycleSupportFamily D α'.1) (isClosed_cycleSupportFamily D p' hp' α'.1) α'.2.1).1

/-- The summand `n_{W'} · i^* f_*[W']` is carried by `|i|^{-1}(closure(|f|(|W'|)))`: only the
closure `W` of the image of `W'` contributes to the pushforward, and the component cycle of `W`
is carried by `i^{-1}(W)`. -/
theorem subspacePointSet_subset_of_gysinProperPushforwardTerm_ne_zero
    (W' : IntegralClosedSubspace D.site D.base D.base_mem X')
    (T : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor)
    (hT : (gysinProperPushforwardTerm D p hp p' hp' hfbase hfqc E hE k rule α' W').1 T ≠ 0) :
    subspacePointSet D.site D.base D.base_mem E.1.toFunctor T.subspace ⊆
      gysinProperPushforwardTermSupport D f E α' W' := by
  rw [gysinProperPushforwardTerm_coe D p hp p' hp' hfbase hfqc E hE E' hE' hgbase hgqc k rule
    rule' α' W' T] at hT
  have hα : α'.1 W' ≠ 0 := left_ne_zero_of_mul hT
  have hsingle : (∑ᶠ V : IntegralClosedSubspace D.site D.base D.base_mem X,
      properCycleMult D p' hp' p hp f W' V *
        (gysinComponentCycle D p E hE k rule V).1 T) =
      properCycleMult D p' hp' p hp f W'
          (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hp.1
            (D.isDecentSpace_of_isGood p hp) f W') *
        (gysinComponentCycle D p E hE k rule
          (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hp.1
            (D.isDecentSpace_of_isGood p hp) f W')).1 T :=
    finsum_eq_single _ _ fun V hV => by
      rw [properCycleMult_eq_zero_of_ne D p' hp' p hp f W' (Ne.symm hV), zero_mul]
  rw [hsingle] at hT
  have hcomp : (gysinComponentCycle D p E hE k rule
      (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hp.1
        (D.isDecentSpace_of_isGood p hp) f W')).1 T ≠ 0 :=
    right_ne_zero_of_mul (right_ne_zero_of_mul hT)
  refine (subspacePointSet_subset_of_gysinComponentCycle_ne_zero D p E hE k rule _ T
    hcomp).trans ?_
  rw [gysinProperPushforwardTermSupport, cycleSupportFamily_of_ne_zero D α'.1 hα,
    ← IntegralClosedSubspace.subspacePointSet_closureImage D.site D.base D.base_mem hp.1
      (D.isDecentSpace_of_isGood p hp) f W']

/-- The summand `n_{W'} · g_* (i')^*[W']` is carried by `|i|^{-1}(closure(|f|(|W'|)))`: a
contributing `T' ⊆ E'` lies in `|i'|^{-1}(|W'|)` and has `T` for the closure of its image under
`g`, and `i ∘ g = f ∘ i'`. -/
theorem subspacePointSet_subset_of_properPushforwardGysinTerm_ne_zero
    (hsq : IsPullback g E'.1.ι E.1.ι f)
    (W' : IntegralClosedSubspace D.site D.base D.base_mem X')
    (T : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor)
    (hT : (properPushforwardGysinTerm D p p' E hE E' hE' hgbase hgqc k rule' α' W').1 T ≠ 0) :
    subspacePointSet D.site D.base D.base_mem E.1.toFunctor T.subspace ⊆
      gysinProperPushforwardTermSupport D f E α' W' := by
  rw [properPushforwardGysinTerm_coe D p hp p' hp' hfbase hfqc E hE E' hE' hgbase hgqc k rule
    rule' α' W' T] at hT
  have hα : α'.1 W' ≠ 0 := left_ne_zero_of_mul hT
  have hsum : (∑ᶠ T' : IntegralClosedSubspace D.site D.base D.base_mem E'.1.toFunctor,
      (gysinComponentCycle D p' E' hE' k rule' W').1 T' *
        properCycleMult D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE g T' T) ≠ 0 :=
    right_ne_zero_of_mul hT
  have hex : ∃ T' : IntegralClosedSubspace D.site D.base D.base_mem E'.1.toFunctor,
      (gysinComponentCycle D p' E' hE' k rule' W').1 T' *
        properCycleMult D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE g T' T ≠ 0 := by
    by_contra hall
    exact hsum (finsum_eq_zero_of_forall_eq_zero fun T' => not_not.1 (not_exists.1 hall T'))
  obtain ⟨T', hT'⟩ := hex
  have hcomp : (gysinComponentCycle D p' E' hE' k rule' W').1 T' ≠ 0 := left_ne_zero_of_mul hT'
  have hTeq : IntegralClosedSubspace.closureImage D.site D.base D.base_mem hE.1
      (D.isDecentSpace_of_isGood (E.1.ι ≫ p) hE) g T' = T :=
    ((properCycleMult_ne_zero_iff D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE g T' T).1
      (right_ne_zero_of_mul hT')).1
  have hT'sub : subspacePointSet D.site D.base D.base_mem E'.1.toFunctor T'.subspace ⊆
      pointsMap D.site D.base D.base_mem E'.1.toFunctor E'.1.ι ⁻¹'
        subspacePointSet D.site D.base D.base_mem X' W'.subspace :=
    subspacePointSet_subset_of_gysinComponentCycle_ne_zero D p' E' hE' k rule' W' T' hcomp
  have hTpts : subspacePointSet D.site D.base D.base_mem E.1.toFunctor T.subspace =
      closure (pointsMap D.site D.base D.base_mem E'.1.toFunctor g ''
        subspacePointSet D.site D.base D.base_mem E'.1.toFunctor T'.subspace) := by
    rw [← hTeq, IntegralClosedSubspace.subspacePointSet_closureImage D.site D.base D.base_mem
      hE.1 (D.isDecentSpace_of_isGood (E.1.ι ≫ p) hE) g T']
  rw [gysinProperPushforwardTermSupport, cycleSupportFamily_of_ne_zero D α'.1 hα, hTpts]
  have hcts : Continuous (pointsMap D.site D.base D.base_mem E.1.toFunctor E.1.ι) :=
    continuous_pointsMap D.site D.base D.base_mem E.1.ι
  intro x hx
  have hmem : pointsMap D.site D.base D.base_mem E.1.toFunctor E.1.ι x ∈
      closure (pointsMap D.site D.base D.base_mem E.1.toFunctor E.1.ι ''
        (pointsMap D.site D.base D.base_mem E'.1.toFunctor g ''
          subspacePointSet D.site D.base D.base_mem E'.1.toFunctor T'.subspace)) :=
    image_closure_subset_closure_image hcts ⟨x, hx, rfl⟩
  refine closure_mono ?_ hmem
  rintro y ⟨z, ⟨w, hw, rfl⟩, rfl⟩
  refine ⟨pointsMap D.site D.base D.base_mem E'.1.toFunctor E'.1.ι w, hT'sub hw, ?_⟩
  have h1 : pointsMap D.site D.base D.base_mem E.1.toFunctor E.1.ι
      (pointsMap D.site D.base D.base_mem E'.1.toFunctor g w) =
      pointsMap D.site D.base D.base_mem E'.1.toFunctor (g ≫ E.1.ι) w := by
    rw [pointsMap_comp]
    rfl
  have h2 : pointsMap D.site D.base D.base_mem X' f
      (pointsMap D.site D.base D.base_mem E'.1.toFunctor E'.1.ι w) =
      pointsMap D.site D.base D.base_mem E'.1.toFunctor (E'.1.ι ≫ f) w := by
    rw [pointsMap_comp]
    rfl
  rw [h2, ← hsq.w, ← h1]

/-- The sum of the summands `n_{W'} · i^* f_*[W']` is `i^* f_* α'`. -/
theorem locallyFiniteCycleSum_gysinProperPushforwardTerm :
    locallyFiniteCycleSum D (E.1.ι ≫ p) k (gysinProperPushforwardTermSupport D f E α')
        (locallyFinite_gysinProperPushforwardTermSupport D p hp p' hp' hfbase hfqc E hE k α')
        (gysinProperPushforwardTerm D p hp p' hp' hfbase hfqc E hE k rule α')
        (subspacePointSet_subset_of_gysinProperPushforwardTerm_ne_zero D p hp p' hp' hfbase hfqc
          E hE E' hE' hgbase hgqc k rule rule' α') =
      gysinCycleMap D p E hE k rule
        (properCyclePushforward D p' hp' p hp hfbase hfqc (k + 1) α') := by
  refine Subtype.ext (funext fun T => ?_)
  rw [locallyFiniteCycleSum_apply, gysinCoeff_properPushforward D p hp p' hp' hfbase hfqc E hE E'
    hE' hgbase hgqc k rule rule' α' T]
  exact finsum_congr fun W' => gysinProperPushforwardTerm_coe D p hp p' hp' hfbase hfqc E hE E'
    hE' hgbase hgqc k rule rule' α' W' T

/-- The sum of the summands `n_{W'} · g_* (i')^*[W']` is `g_* (i')^* α'`. -/
theorem locallyFiniteCycleSum_properPushforwardGysinTerm (hsq : IsPullback g E'.1.ι E.1.ι f) :
    locallyFiniteCycleSum D (E.1.ι ≫ p) k (gysinProperPushforwardTermSupport D f E α')
        (locallyFinite_gysinProperPushforwardTermSupport D p hp p' hp' hfbase hfqc E hE k α')
        (properPushforwardGysinTerm D p p' E hE E' hE' hgbase hgqc k rule' α')
        (subspacePointSet_subset_of_properPushforwardGysinTerm_ne_zero D p hp p' hp' hfbase hfqc
          E hE E' hE' hgbase hgqc k rule rule' α' hsq) =
      properCyclePushforward D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE hgbase hgqc k
        (gysinCycleMap D p' E' hE' k rule' α') := by
  refine Subtype.ext (funext fun T => ?_)
  rw [locallyFiniteCycleSum_apply, properPushforward_gysinCoeff D p hp p' hp' hfbase hfqc E hE E'
    hE' hgbase hgqc k rule rule' α' T]
  exact finsum_congr fun W' => properPushforwardGysinTerm_coe D p hp p' hp' hfbase hfqc E hE E'
    hE' hgbase hgqc k rule rule' α' W' T

/-- **Stacks 0ER5 in `CH_k(E)`, from the prime-cycle identity up to rational equivalence.**  If
for every integral closed subspace `W' ⊆ X'` the two `k`-cycles `n_{W'} i^* f_*[W']` and
`n_{W'} g_* (i')^*[W']` on `E` are rationally equivalent on the closed subset
`|i|^{-1}(closure(|f|(|W'|)))` of `|E|` carrying them, then

`i^* f_* α' = g_* (i')^* α'` in `CH_k(E)`.

The passage from the prime cycles to an arbitrary `(k+1)`-cycle is Stacks 0EQ8, applied to the
locally finite collection of those subsets. -/
theorem chowClass_gysinCycleMap_properPushforward_eq_of_rationallyEquivalentOn
    (hsq : IsPullback g E'.1.ι E.1.ι f)
    (hre : ∀ W' : IntegralClosedSubspace D.site D.base D.base_mem X',
      RationallyEquivalentOn.{u + 1} D (E.1.ι ≫ p) hE k
        (gysinProperPushforwardTermSupport D f E α' W')
        (gysinProperPushforwardTerm D p hp p' hp' hfbase hfqc E hE k rule α' W')
        (properPushforwardGysinTerm D p p' E hE E' hE' hgbase hgqc k rule' α' W')) :
    chowClass.{u + 1} D (E.1.ι ≫ p) hE k
        (gysinCycleMap D p E hE k rule
          (properCyclePushforward D p' hp' p hp hfbase hfqc (k + 1) α')) =
      chowClass.{u + 1} D (E.1.ι ≫ p) hE k
        (properCyclePushforward D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE hgbase hgqc k
          (gysinCycleMap D p' E' hE' k rule' α')) := by
  rw [chowClass_eq_iff_rationallyEquivalent,
    ← locallyFiniteCycleSum_gysinProperPushforwardTerm D p hp p' hp' hfbase hfqc E hE E' hE'
      hgbase hgqc k rule rule' α',
    ← locallyFiniteCycleSum_properPushforwardGysinTerm D p hp p' hp' hfbase hfqc E hE E' hE'
      hgbase hgqc k rule rule' α' hsq]
  exact rationallyEquivalent_locallyFiniteCycleSum D (E.1.ι ≫ p) hE k _
    (locallyFinite_gysinProperPushforwardTermSupport D p hp p' hp' hfbase hfqc E hE k α') _ _ _ _
      hre

/-- **Stacks 0ER5 in `CH_k(E)`, from the source's two cases.**  In Situation 0EDT let
`f : X' ⟶ X` be a quasi-compact morphism of good algebraic spaces over `B`, let `E ⊆ X` be a
closed subspace, and form the diagram of Remark 0ER3, with `E' ⊆ X'` sitting in the cartesian
square `hsq` with `g : E' ⟶ E`.  Then for every `(k+1)`-cycle `α'` on `X'`

`i^* f_* α' = g_* (i')^* α'` in `CH_k(E)`,

for the refined Gysin maps of Stacks 0ER1 built on any component rules on `X` and on `X'`,
provided the two cases of the source's proof hold:

* `hnot`, the case `W' ⊄ D'`: the coefficientwise identity of cycles
  `deg(W'/W) · m_T(E ∩ W) = ∑_{T'} m_{T'}(E' ∩ W') · deg(T'/T)`;
* `hcont`, the case `W' ⊆ D'`: the two `W'`-th summands are rationally equivalent on
  `|i|^{-1}(closure(|f|(|W'|)))`, as in the second assertion of Stacks 0EQS for the proper
  dominant morphism `W' → W`. -/
theorem chowClass_gysinCycleMap_properPushforward_eq_of_contained
    (hsq : IsPullback g E'.1.ι E.1.ι f)
    (hnot : ∀ W' : IntegralClosedSubspace D.site D.base D.base_mem X',
      deltaDimension D p' W' = k + 1 → ¬ W'.subspace ≤ E'.1 →
      ∀ T : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor,
        (∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem X,
            properCycleMult D p' hp' p hp f W' W *
              (gysinComponentCycle D p E hE k rule W).1 T) =
          ∑ᶠ T' : IntegralClosedSubspace D.site D.base D.base_mem E'.1.toFunctor,
            (gysinComponentCycle D p' E' hE' k rule' W').1 T' *
              properCycleMult D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE g T' T)
    (hcont : ∀ W' : IntegralClosedSubspace D.site D.base D.base_mem X', α'.1 W' ≠ 0 →
      W'.subspace ≤ E'.1 →
      RationallyEquivalentOn.{u + 1} D (E.1.ι ≫ p) hE k
        (gysinProperPushforwardTermSupport D f E α' W')
        (gysinProperPushforwardTerm D p hp p' hp' hfbase hfqc E hE k rule α' W')
        (properPushforwardGysinTerm D p p' E hE E' hE' hgbase hgqc k rule' α' W')) :
    chowClass.{u + 1} D (E.1.ι ≫ p) hE k
        (gysinCycleMap D p E hE k rule
          (properCyclePushforward D p' hp' p hp hfbase hfqc (k + 1) α')) =
      chowClass.{u + 1} D (E.1.ι ≫ p) hE k
        (properCyclePushforward D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE hgbase hgqc k
          (gysinCycleMap D p' E' hE' k rule' α')) := by
  refine chowClass_gysinCycleMap_properPushforward_eq_of_rationallyEquivalentOn D p hp p' hp'
    hfbase hfqc E hE E' hE' hgbase hgqc k rule rule' α' hsq fun W' => ?_
  by_cases hc : α'.1 W' ≠ 0 ∧ W'.subspace ≤ E'.1
  · exact hcont W' hc.1 hc.2
  · refine rationallyEquivalentOn_of_eq (E.1.ι ≫ p) hE k _ (Subtype.ext (funext fun T => ?_))
    rw [gysinProperPushforwardTerm_coe D p hp p' hp' hfbase hfqc E hE E' hE' hgbase hgqc k rule
      rule' α' W' T, properPushforwardGysinTerm_coe D p hp p' hp' hfbase hfqc E hE E' hE' hgbase
      hgqc k rule rule' α' W' T]
    by_cases h0 : α'.1 W' = 0
    · rw [h0, zero_mul, zero_mul]
    · rw [hnot W' (α'.2.2 W' h0) (fun hle => hc ⟨h0, hle⟩) T]

end ChowClass

/-! ### Stacks 0ER5 in `CH_k(E)` at the canonical component rules -/

section GenericPointData

variable (D : BaseSpaceDimensionSituation.{u})
    {X X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p) (p' : X' ⟶ D.space) (hp' : D.IsGood p')
    {f : X' ⟶ X} (hfbase : f ≫ p = p')
    (hfqc : IsQuasiCompact D.site D.base D.base_mem f)
    (E : ClosedSubspaces D.site D.base D.base_mem X) (hE : D.IsGood (E.1.ι ≫ p))
    (E' : ClosedSubspaces D.site D.base D.base_mem X') (hE' : D.IsGood (E'.1.ι ≫ p'))
    {g : E'.1.toFunctor ⟶ E.1.toFunctor} (hgbase : g ≫ (E.1.ι ≫ p) = E'.1.ι ≫ p')
    (hgqc : IsQuasiCompact D.site D.base D.base_mem g)
    (k : ℤ) (chern : FirstChernComponentCycleRule D p k)
    (chern' : FirstChernComponentCycleRule D p' k)
    (α' : CycleGroup D p' (k + 1))

/-- **Stacks 0ER5 in `CH_k(E)` at the canonical component rules.**  For the refined Gysin maps at
the canonical component rules, `i^* f_* α' = g_* (i')^* α'` in `CH_k(E)`, provided that
`|E'| = |f|^{-1}(|E|)`, that for every `W' ⊄ E'` and every `T` the generic-point dictionary `hdata`
of the fibre of `E' ∩ W' → E ∩ W` over the generic point of `T` exists, and that the source's
second case `hcont`, `W' ⊆ E'`, holds as a rational equivalence. -/
theorem chowClass_gysinCycleMap_properPushforward_eq_of_genericPointData
    (hsq : IsPullback g E'.1.ι E.1.ι f)
    (hpt : subspacePointSet D.site D.base D.base_mem X' E'.1 =
      pointsMap D.site D.base D.base_mem X' f ⁻¹'
        subspacePointSet D.site D.base D.base_mem X E.1)
    (hdata : ∀ (W' : IntegralClosedSubspace D.site D.base D.base_mem X')
        (T : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor),
      ¬ W'.subspace ≤ E'.1 →
        Nonempty (GysinProperPushforwardGenericPointDatum.{u, v} D p hp p' hp' f E hE E' hE' g k
            W' T))
    (hcont : ∀ W' : IntegralClosedSubspace D.site D.base D.base_mem X', α'.1 W' ≠ 0 →
      W'.subspace ≤ E'.1 →
      RationallyEquivalentOn.{u + 1} D (E.1.ι ≫ p) hE k
        (gysinProperPushforwardTermSupport D f E α' W')
        (gysinProperPushforwardTerm D p hp p' hp' hfbase hfqc E hE k
          (canonicalGysinComponentRule D p hp E hE k chern) α' W')
        (properPushforwardGysinTerm D p p' E hE E' hE' hgbase hgqc k
          (canonicalGysinComponentRule D p' hp' E' hE' k chern') α' W')) :
    chowClass.{u + 1} D (E.1.ι ≫ p) hE k
        (gysinCycleMap D p E hE k (canonicalGysinComponentRule D p hp E hE k chern)
          (properCyclePushforward D p' hp' p hp hfbase hfqc (k + 1) α')) =
      chowClass.{u + 1} D (E.1.ι ≫ p) hE k
        (properCyclePushforward D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE hgbase hgqc k
          (gysinCycleMap D p' E' hE' k (canonicalGysinComponentRule D p' hp' E' hE' k chern')
            α')) :=
  chowClass_gysinCycleMap_properPushforward_eq_of_contained D p hp p' hp' hfbase hfqc E hE E'
    hE' hgbase hgqc k _ _ α' hsq
    (fun W' hW' hle T => gysinCoeff_comm_of_genericPointData_of_not_le D p hp p' hp' f E hE E'
      hE' g k hpt chern chern' W' hW' hle T (hdata W' T hle).some)
    hcont

end GenericPointData

end AlgebraicGeometry.Space

end
