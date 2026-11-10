module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalDivisorCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardClosedImmersionSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardDimensionDrop
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardPrincipalDivisorCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackRationalEquivalenceCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalenceCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalenceSums

/-!
# Proper pushforward respects rational equivalence on algebraic spaces

In Situation 0EDT let `X/B` and `Y/B` be good and let `p : X ⟶ Y` be proper over the base.
**Stacks 0EQC** says that if `α, β ∈ Z_k(X)` are rationally equivalent then so are `p_*α` and
`p_*β`, and hence that `p_*` descends to `CH_k(X) → CH_k(Y)`. Rational equivalence is read at the
canonical embeddings `R(W) → Q(𝒪^h_{W,ξ})` of Stacks 0ENK
(`AlgebraicGeometry.Space.IsRationallyEquivalentToZeroCanonical`), where `div(f)` is a function
of `f` alone, as in the source.

The source's argument:

1. It suffices to show that `p_*(∑_j i_{j,*} div(f_j))` is rationally equivalent to zero, for a
   locally finite family `{W_j ⊆ X}` of integral closed subspaces of δ-dimension `k + 1` and
   `f_j ∈ R(W_j)^*`.
2. Pushforward commutes with that sum, and the family of images `W'_j = p(W_j)` is again locally
   finite in `Y` (Stacks 0ENZ).
3. `p_* i_{j,*} div(f_j) = i'_{j,*} (p'_j)_* div(f_j)` for the morphism `p'_j : W_j ⟶ W'_j` of
   Stacks 0EEG — the square form of Stacks 0EP2.
4. `(p'_j)_* div(f_j)` is zero when `dim_δ(W'_j) < k`, zero when `dim_δ(W'_j) = k`
   (`AlgebraicGeometry.Space.properCyclePushforward_eq_zero_of_deltaValue_drop`), and the
   principal divisor of the norm when `dim_δ(W'_j) = k + 1` (Stacks 0EQ4).

## Main results

* `AlgebraicGeometry.Space.locallyFinite_subspacePointSet_closureImage_of_isQuasiCompact`:
  step 2, Stacks 0ENZ for the family of images.
* `AlgebraicGeometry.Space.properCyclePushforward_cycleFamilySum_apply`: step 2, pushforward
  commutes with the locally finite sum of Stacks 0EQ6, part (1).
* `AlgebraicGeometry.Space.properCyclePushforward_integralClosedSubspacePushforward_closureImage`:
  step 3.
* `AlgebraicGeometry.Space.subspaceProperCyclePushforward_eq_zero_of_deltaDimension_eq`: the
  branch `dim_δ(W') = k` of step 4.
* `AlgebraicGeometry.Space.cycleGroup_eq_zero_of_deltaDimension_lt`: the branch `dim_δ(W') < k`.
* `AlgebraicGeometry.Space.isPrincipalDivisorCycleOfGood_subspaceProperCyclePushforward`: the
  branch `dim_δ(W') = k + 1`, from Stacks 0EQ4.
* `AlgebraicGeometry.Space.rationallyEquivalentCanonical_properCyclePushforward`: **Stacks 0EQC**.
* `AlgebraicGeometry.Space.chowGroupCanonicalProperPushforward`: the induced homomorphism
  `p_* : CH_k(X) → CH_k(Y)`.

## Implementation notes

Steps 1–3, the case `dim_δ(W') < k` and the descent to Chow groups follow the source; the
case analysis of step 4 is discharged rather than assumed.

## References

* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EEG](https://stacks.math.columbia.edu/tag/0EEG)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0ENZ](https://stacks.math.columbia.edu/tag/0ENZ)
* [Stacks Project, Tag 0EP1](https://stacks.math.columbia.edu/tag/0EP1)
* [Stacks Project, Tag 0EP2](https://stacks.math.columbia.edu/tag/0EP2)
* [Stacks Project, Tag 0EQ4](https://stacks.math.columbia.edu/tag/0EQ4)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQC](https://stacks.math.columbia.edu/tag/0EQC)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Local finiteness of the family of integral closed images -/

section Images

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- **Step 2 of Stacks 0EQC, which is Stacks 0ENZ.** The integral closed images in `Y` of a
locally finite family of integral closed subspaces of `X` along a quasi-compact morphism
`p : X ⟶ Y` of good algebraic spaces over the base again have locally finite point sets.

The point set of the integral closed image is the closure of the image of the point set, so this
is `AlgebraicGeometry.Space.locallyFinite_closure_image_pointsMap` — Stacks 0ENZ — applied to the
family of point sets, which are closed. -/
theorem locallyFinite_subspacePointSet_closureImage_of_isQuasiCompact (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) {p : X ⟶ Y} (hpB : p ≫ sY = sX)
    (hp : IsQuasiCompact D.site D.base D.base_mem p) {J : Type v}
    (W : J → IntegralClosedSubspace D.site D.base D.base_mem X)
    (hWfin : LocallyFinite fun j : J =>
      subspacePointSet D.site D.base D.base_mem X (W j).subspace) :
    LocallyFinite fun j : J => subspacePointSet D.site D.base D.base_mem Y
      (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
        (D.isDecentSpace_of_isGood sY hY) p (W j)).subspace := by
  obtain ⟨hlf, -⟩ := locallyFinite_closure_image_pointsMap D sX hX sY hY hpB hp
    (fun j : J => subspacePointSet D.site D.base D.base_mem X (W j).subspace)
    (fun j => isClosed_range_pointsMap_integralClosedSubspace D.site D.base D.base_mem hX.1
      (W j))
    hWfin
  have heq : (fun j : J => subspacePointSet D.site D.base D.base_mem Y
        (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
          (D.isDecentSpace_of_isGood sY hY) p (W j)).subspace) =
      fun j : J => closure (pointsMap D.site D.base D.base_mem X p ''
        subspacePointSet D.site D.base D.base_mem X (W j).subspace) :=
    funext fun j => IntegralClosedSubspace.subspacePointSet_closureImage D.site D.base D.base_mem
      hY.1 (D.isDecentSpace_of_isGood sY hY) p (W j)
  rw [heq]
  exact hlf

end Images

/-! ### Proper pushforward commutes with a locally finite sum of cycles -/

section FamilySum

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- **Step 2 of Stacks 0EQC.** The coefficient of the pushforward of the locally finite sum
`∑_j i_{j,*} c_j` of Stacks 0EQ6, part (1), at an integral closed subspace `Z' ⊆ Y` is the sum
over `j` of the coefficients of the pushforwards `p_*(i_{j,*} c_j)`.

Both sides are a double sum, over the integral closed subspaces `Z ⊆ X` and over `J`, in the two
orders. The terms vanish outside a product of two finite sets: an index `j` contributing at `Z'`
has `|W'_j|` containing the generic point of `Z'`, so there are finitely many such `j` by
Stacks 0ENZ for the family of images, and for each of them the subspaces `Z` contributing are
finitely many by `AlgebraicGeometry.Space.finite_properCycleFibre`. -/
theorem properCyclePushforward_cycleFamilySum_apply (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) {p : X ⟶ Y} (hpB : p ≫ sY = sX)
    (hp : IsQuasiCompact D.site D.base D.base_mem p) (k : ℤ) {J : Type v}
    (W : J → IntegralClosedSubspace D.site D.base D.base_mem X)
    (hWfin : LocallyFinite fun j : J =>
      subspacePointSet D.site D.base D.base_mem X (W j).subspace)
    (c : ∀ j, CycleGroup D ((W j).subspace.ι ≫ sX) k)
    (Z' : IntegralClosedSubspace D.site D.base D.base_mem Y) :
    (properCyclePushforward D sX hX sY hY hpB hp k
        (cycleFamilySum D sX hX W hWfin k c)).1 Z' =
      ∑ᶠ j : J, (properCyclePushforward D sX hX sY hY hpB hp k
        (integralClosedSubspacePushforward D sX hX (W j) k (c j))).1 Z' := by
  obtain ⟨V, hV, hVfin⟩ := locallyFinite_subspacePointSet_closureImage_of_isQuasiCompact D sX hX
    sY hY hpB hp W hWfin (Z'.ambientGenericPoint D.site D.base D.base_mem)
  have hηZ' : Z'.ambientGenericPoint D.site D.base D.base_mem ∈
      subspacePointSet D.site D.base D.base_mem Y Z'.subspace := by
    rw [← Z'.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hY.1]
    exact subset_closure rfl
  set T : Set J := {j : J | (subspacePointSet D.site D.base D.base_mem Y
      (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
        (D.isDecentSpace_of_isGood sY hY) p (W j)).subspace ∩ V).Nonempty} with hT
  set S : Set (IntegralClosedSubspace D.site D.base D.base_mem X) :=
    ⋃ j ∈ T, {Z | (integralClosedSubspacePushforward D sX hX (W j) k (c j)).1 Z ≠ 0 ∧
      IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
        (D.isDecentSpace_of_isGood sY hY) p Z = Z'} with hS
  have hSfin : S.Finite := hVfin.biUnion fun j _ =>
    finite_properCycleFibre D sX hX sY hY hpB hp
      (integralClosedSubspacePushforward D sX hX (W j) k (c j)).1
      (integralClosedSubspacePushforward D sX hX (W j) k (c j)).2.1 Z'
  have hvan : (Function.support fun s : IntegralClosedSubspace D.site D.base D.base_mem X × J =>
        (integralClosedSubspacePushforward D sX hX (W s.2) k (c s.2)).1 s.1 *
          properCycleMult D sX hX sY hY p s.1 Z') ⊆ S ×ˢ T := by
    rintro ⟨Z, j⟩ hmem
    have hne : (integralClosedSubspacePushforward D sX hX (W j) k (c j)).1 Z *
        properCycleMult D sX hX sY hY p Z Z' ≠ 0 := hmem
    have hZne := left_ne_zero_of_mul hne
    have him := ((properCycleMult_ne_zero_iff D sX hX sY hY p Z Z').1
      (right_ne_zero_of_mul hne)).1
    have hZW := subspacePointSet_subset_of_pushforward_ne_zero D sX hX (W j) k (c j) Z hZne
    have hjT : j ∈ T := by
      refine ⟨Z'.ambientGenericPoint D.site D.base D.base_mem, ?_, mem_of_mem_nhds hV⟩
      have hηim : Z'.ambientGenericPoint D.site D.base D.base_mem ∈
          closure (pointsMap D.site D.base D.base_mem X p ''
            subspacePointSet D.site D.base D.base_mem X Z.subspace) := by
        rw [← IntegralClosedSubspace.subspacePointSet_closureImage D.site D.base D.base_mem hY.1
          (D.isDecentSpace_of_isGood sY hY) p Z, him]
        exact hηZ'
      rw [IntegralClosedSubspace.subspacePointSet_closureImage D.site D.base D.base_mem hY.1
        (D.isDecentSpace_of_isGood sY hY) p (W j)]
      exact closure_mono (Set.image_mono hZW) hηim
    exact ⟨Set.mem_biUnion hjT ⟨hZne, him⟩, hjT⟩
  rw [properPushforward_apply]
  have hterm : ∀ Z : IntegralClosedSubspace D.site D.base D.base_mem X,
      (cycleFamilySum D sX hX W hWfin k c).1 Z * properCycleMult D sX hX sY hY p Z Z' =
        ∑ᶠ j : J, (integralClosedSubspacePushforward D sX hX (W j) k (c j)).1 Z *
          properCycleMult D sX hX sY hY p Z Z' := fun Z => by
    rw [cycleFamilySum_apply, finsum_mul]
  rw [finsum_congr hterm,
    Stacks.Chow.finsum_finsum_comm_of_finite_support
      (fun (Z : IntegralClosedSubspace D.site D.base D.base_mem X) (j : J) =>
        (integralClosedSubspacePushforward D sX hX (W j) k (c j)).1 Z *
          properCycleMult D sX hX sY hY p Z Z')
      ((hSfin.prod hVfin).subset hvan)]
  exact finsum_congr fun j => (properPushforward_apply D sX hX sY hY hpB hp k _ Z').symm

end FamilySum

/-! ### Pushforward along the morphism of Stacks 0EEG -/

section Square

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- The pushforward of `k`-cycles along a morphism `q : W ⟶ W'` of integral closed subspaces
over a proper morphism `p : X ⟶ Y` of good algebraic spaces over the base, that is along the
morphism of Stacks 0EEG.

Only `p` and the commuting square `q ≫ i' = i ≫ p` are data. Goodness of `W/B` and `W'/B` is
`AlgebraicGeometry.Space.isGood_integralClosedSubspace`, the factorization of `q` over the base
is read off the square, and properness of `q` — which is what lets the pushforward of
Stacks 0EP1 be formed — is Stacks 0EEG,
`AlgebraicGeometry.Space.IntegralClosedSubspace.isProper_of_comp_ι_eq`. -/
def subspaceProperCyclePushforward (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) {p : X ⟶ Y} (hpB : p ≫ sY = sX)
    (hp : IsProper D.site D.base D.base_mem p)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (W' : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (q : W.subspace.toFunctor ⟶ W'.subspace.toFunctor)
    (hq : q ≫ W'.subspace.ι = W.subspace.ι ≫ p) (k : ℤ) :
    CycleGroup D (W.subspace.ι ≫ sX) k →+ CycleGroup D (W'.subspace.ι ≫ sY) k :=
  properCyclePushforward D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
    (W'.subspace.ι ≫ sY) (isGood_integralClosedSubspace D sY hY W')
    (show q ≫ W'.subspace.ι ≫ sY = W.subspace.ι ≫ sX by
      rw [← Category.assoc, hq, Category.assoc, hpB])
    (IntegralClosedSubspace.isProper_of_comp_ι_eq D.site D.base D.base_mem hX.1 hY.1 p hp
      W W' q hq).2.1.2 k

/-- **Step 3 of Stacks 0EQC: the square form of Stacks 0EP2, read at the morphism of
Stacks 0EEG.** For an integral closed subspace `W ⊆ X`, an integral closed subspace `W' ⊆ Y` and
a morphism `q : W ⟶ W'` over `p`, the pushforward along `p` of a cycle pushed forward from `W` is
the cycle pushed forward from `W'` of its pushforward along `q`. -/
theorem properCyclePushforward_integralClosedSubspacePushforward_closureImage (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) {p : X ⟶ Y} (hpB : p ≫ sY = sX)
    (hp : IsProper D.site D.base D.base_mem p)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (W' : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (q : W.subspace.toFunctor ⟶ W'.subspace.toFunctor)
    (hq : q ≫ W'.subspace.ι = W.subspace.ι ≫ p) (k : ℤ)
    (c : CycleGroup D (W.subspace.ι ≫ sX) k) :
    properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k
        (integralClosedSubspacePushforward D sX hX W k c) =
      integralClosedSubspacePushforward D sY hY W' k
        (subspaceProperCyclePushforward D sX hX sY hY hpB hp W W' q hq k c) :=
  properCyclePushforward_integralClosedSubspacePushforward D sX sY hX hY hpB hp W W' q hq k c

/-- The δ-value at a point of an integral closed subspace `W ⊆ X`, over the base through the
inclusion, is the δ-value of its image in `X`: the inclusion is an immersion, hence locally
quasi-finite. -/
private theorem deltaValue_comp_ι_apply (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (t : points D.site D.base D.base_mem W.subspace.toFunctor) :
    D.deltaValue (W.subspace.ι ≫ sX) t =
      D.deltaValue sX (pointsMap D.site D.base D.base_mem _ W.subspace.ι t) :=
  D.deltaValue_comp_of_isLocallyQuasiFinite W.isClosedSubspace.1 hX.1 W.subspace.ι sX
    (isLocallyQuasiFinite_of_isImmersion D.site D.base D.base_mem W.subspace.ι
      (isImmersion_of_isClosedImmersion D.site D.base D.base_mem W.isClosedSubspace.2))
    hX.2.2 t

end Square

section DeltaDimension

variable (D : BaseSpaceDimensionSituation.{u})
    {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- The δ-dimension of an integral closed subspace `T` of the algebraic space underlying an
integral closed subspace `W' ⊆ Y`, taken over the base through `W'`, is at most the
δ-dimension of `W'`.

The inclusion `W' ⟶ Y` is an immersion, hence locally quasi-finite, so the dimension function it
induces on `|W'|` is the restriction of the one on `|Y|`; and the image in `|Y|` of the generic
point of `T` lies in `|W'| = closure{η_{W'}}`, so it is a specialization of `η_{W'}`, at which a
dimension function is strictly larger unless the two points agree. -/
theorem IntegralClosedSubspace.deltaDimension_comp_ι_le (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (W' : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (T : IntegralClosedSubspace D.site D.base D.base_mem W'.subspace.toFunctor) :
    deltaDimension D (W'.subspace.ι ≫ sY) T ≤ deltaDimension D sY W' := by
  set x := pointsMap D.site D.base D.base_mem W'.subspace.toFunctor W'.subspace.ι
    (T.ambientGenericPoint D.site D.base D.base_mem) with hx
  have hstep : deltaDimension D (W'.subspace.ι ≫ sY) T = D.deltaValue sY x :=
    deltaValue_comp_ι_apply D sY hY W' _
  have hmem : x ∈ subspacePointSet D.site D.base D.base_mem Y W'.subspace := ⟨_, rfl⟩
  have hspec : W'.ambientGenericPoint D.site D.base D.base_mem ⤳ x :=
    (W'.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hY.1).specializes hmem
  have hW' : deltaDimension D sY W' =
      D.deltaValue sY (W'.ambientGenericPoint D.site D.base D.base_mem) := rfl
  rcases eq_or_ne x (W'.ambientGenericPoint D.site D.base D.base_mem) with heq | hne
  · rw [hstep, hW', heq]
  · have hlt := (deltaDimensionFunction D sY hY).strictAnti_specializes hspec (Ne.symm hne)
    rw [deltaDimensionFunction_apply, deltaDimensionFunction_apply] at hlt
    rw [hstep, hW']
    exact hlt.le

/-- A `k`-cycle on an integral closed subspace `W' ⊆ Y` of δ-dimension less than `k` is zero:
every integral closed subspace of `W'` has δ-dimension at most `dim_δ(W') < k`, so none may
carry a nonzero coefficient. -/
theorem cycleGroup_eq_zero_of_deltaDimension_lt (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (W' : IntegralClosedSubspace D.site D.base D.base_mem Y) (k : ℤ)
    (hk : deltaDimension D sY W' < k) (c : CycleGroup D (W'.subspace.ι ≫ sY) k) : c = 0 := by
  refine Subtype.ext (funext fun T => ?_)
  by_contra hne
  have hdim := c.2.2 T hne
  have hle := IntegralClosedSubspace.deltaDimension_comp_ι_le D sY hY W' T
  rw [hdim] at hle
  exact absurd (hle.trans_lt hk) (lt_irrefl k)

end DeltaDimension

/-! ### Descending a homomorphism of cycle groups to the canonical Chow groups -/

section Descent

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- A homomorphism `φ : Z_m(Y) → Z_n(X)` of cycle groups which carries cycles rationally
equivalent to zero to cycles rationally equivalent to zero respects rational equivalence, at the
canonical embeddings of Stacks 0ENK: `α ∼_rat β` gives `φ(α) ∼_rat φ(β)`, because
`φ(α) - φ(β) = φ(α - β)`.

This is `AlgebraicGeometry.Space.rationallyEquivalent_cycleHom` read at
`AlgebraicGeometry.Space.IsRationallyEquivalentToZeroCanonical`. -/
theorem rationallyEquivalentCanonical_cycleHom (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) (m n : ℤ) (φ : CycleGroup D sY m →+ CycleGroup D sX n)
    (hφ : ∀ γ : CycleGroup D sY m, IsRationallyEquivalentToZeroCanonical.{v} D sY hY m γ →
      IsRationallyEquivalentToZeroCanonical.{v} D sX hX n (φ γ))
    {α β : CycleGroup D sY m} (h : RationallyEquivalentCanonical.{v} D sY hY m α β) :
    RationallyEquivalentCanonical.{v} D sX hX n (φ α) (φ β) := by
  have hsub := hφ (α - β) h
  rwa [map_sub] at hsub

/-- The homomorphism `CH_m(Y) → CH_n(X)` of Chow groups induced by a homomorphism
`φ : Z_m(Y) → Z_n(X)` of cycle groups which carries cycles rationally equivalent to zero to
cycles rationally equivalent to zero, at the canonical embeddings of Stacks 0ENK.

The Chow groups are `AlgebraicGeometry.Space.chowGroupCanonical` of part (4) of Stacks 0EQ6 at
those embeddings, and the map is the one induced on the quotients. -/
def chowGroupCanonicalHomOfCycleHom (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (m n : ℤ) (φ : CycleGroup D sY m →+ CycleGroup D sX n)
    (hφ : ∀ γ : CycleGroup D sY m, IsRationallyEquivalentToZeroCanonical.{v} D sY hY m γ →
      IsRationallyEquivalentToZeroCanonical.{v} D sX hX n (φ γ)) :
    chowGroupCanonical.{v} D sY hY m →+ chowGroupCanonical.{v} D sX hX n :=
  QuotientAddGroup.map (rationalEquivalencesCanonical.{v} D sY hY m)
    (rationalEquivalencesCanonical.{v} D sX hX n) φ fun γ hγ => hφ γ hγ

/-- The induced map on Chow groups takes the class of a cycle to the class of its image. -/
@[simp]
theorem chowGroupCanonicalHomOfCycleHom_chowClassCanonical (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) (m n : ℤ) (φ : CycleGroup D sY m →+ CycleGroup D sX n)
    (hφ : ∀ γ : CycleGroup D sY m, IsRationallyEquivalentToZeroCanonical.{v} D sY hY m γ →
      IsRationallyEquivalentToZeroCanonical.{v} D sX hX n (φ γ)) (α : CycleGroup D sY m) :
    chowGroupCanonicalHomOfCycleHom.{v} D sX hX sY hY m n φ hφ
        (chowClassCanonical.{v} D sY hY m α) =
      chowClassCanonical.{v} D sX hX n (φ α) :=
  rfl

end Descent

/-! ### The dimension-drop branch for an integral closed subspace -/

section DimensionDrop

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- The image of the generic point of an integral closed subspace, as an algebraic space, is the
generic point of its point set. -/
theorem IntegralClosedSubspace.pointsMap_ι_genericPoint
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW : IsAlgebraicSpace D.site D.base D.base_mem W.subspace.toFunctor) :
    pointsMap D.site D.base D.base_mem _ W.subspace.ι
        (Space.genericPoint D.site D.base D.base_mem hW W.isIntegralSpace) =
      W.ambientGenericPoint D.site D.base D.base_mem := by
  rw [genericPoint_eq_genericPoint_integralClosedSubspace]
  rfl

/-- The δ-value of the generic point of an integral closed subspace, measured through the
inclusion, is its δ-dimension: the inclusion is an immersion, hence locally quasi-finite. -/
theorem IntegralClosedSubspace.deltaValue_comp_ι_genericPoint (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hWg : D.IsGood (W.subspace.ι ≫ sX)) :
    D.deltaValue (W.subspace.ι ≫ sX)
        (Space.genericPoint D.site D.base D.base_mem hWg.1 W.isIntegralSpace) =
      deltaDimension D sX W := by
  rw [deltaValue_comp_ι_apply D sX hX, IntegralClosedSubspace.pointsMap_ι_genericPoint D W hWg.1]
  rfl

/-- A morphism `q : W ⟶ W'` of integral closed subspaces over `p`, where `p` sends the ambient
generic point of `W` to that of `W'`, sends the generic point of `W` to that of `W'`. -/
private theorem pointsMap_genericPoint_eq_of_comp_ι_eq {p : X ⟶ Y}
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (W' : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (q : W.subspace.toFunctor ⟶ W'.subspace.toFunctor)
    (hq : q ≫ W'.subspace.ι = W.subspace.ι ≫ p)
    (hgen : W'.ambientGenericPoint D.site D.base D.base_mem =
      pointsMap D.site D.base D.base_mem X p (W.ambientGenericPoint D.site D.base D.base_mem))
    (hW : IsAlgebraicSpace D.site D.base D.base_mem W.subspace.toFunctor)
    (hW' : IsAlgebraicSpace D.site D.base D.base_mem W'.subspace.toFunctor) :
    pointsMap D.site D.base D.base_mem _ q
        (Space.genericPoint D.site D.base D.base_mem hW W.isIntegralSpace) =
      Space.genericPoint D.site D.base D.base_mem hW' W'.isIntegralSpace := by
  refine pointsMap_injective_of_mono D.site D.base D.base_mem W'.subspace.ι ?_
  rw [← pointsMap_comp_apply, hq, pointsMap_comp_apply,
    IntegralClosedSubspace.pointsMap_ι_genericPoint D W hW,
    IntegralClosedSubspace.pointsMap_ι_genericPoint D W' hW', hgen]

/-- The closed δ-dimension of the whole of an integral closed subspace `W ⊆ X` is `n` when its
δ-dimension is `n`. -/
private theorem deltaDimensionClosed_univ_eq_of_deltaDimension_eq (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hWg : D.IsGood (W.subspace.ι ≫ sX)) (n : ℤ) (h : deltaDimension D sX W = n) :
    deltaDimensionClosed D (W.subspace.ι ≫ sX) hWg Set.univ isClosed_univ = (n : EInt) :=
  (deltaDimensionClosed_univ_eq_inducedDimensionValue_genericPoint D _ hWg
    W.isIntegralSpace).trans (congrArg (fun n : ℤ => (n : EInt))
      ((IntegralClosedSubspace.deltaValue_comp_ι_genericPoint D sX hX W hWg).trans h))

/-- **The branch `dim_δ(W') = k` of Stacks 0EQC**, for a morphism `q : W ⟶ W'` of integral
closed subspaces over `p` sending the generic point of `W` to that of `W'`. -/
theorem properCyclePushforward_subspace_eq_zero_of_deltaDimension_eq (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) {p : X ⟶ Y}
    (hp : IsProper D.site D.base D.base_mem p) (k : ℤ)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (W' : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (q : W.subspace.toFunctor ⟶ W'.subspace.toFunctor)
    (hq : q ≫ W'.subspace.ι = W.subspace.ι ≫ p)
    (hqB : q ≫ W'.subspace.ι ≫ sY = W.subspace.ι ≫ sX)
    (hgen : W'.ambientGenericPoint D.site D.base D.base_mem =
      pointsMap D.site D.base D.base_mem X p (W.ambientGenericPoint D.site D.base D.base_mem))
    (hWd : deltaDimension D sX W = k + 1) (hW'd : deltaDimension D sY W' = k)
    (c : CycleGroup D (W.subspace.ι ≫ sX) k)
    (hc : IsPrincipalDivisorCycleOfGood D (W.subspace.ι ≫ sX)
      (isGood_integralClosedSubspace D sX hX W) W.isIntegralSpace k c) :
    properCyclePushforward D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
      (W'.subspace.ι ≫ sY) (isGood_integralClosedSubspace D sY hY W') hqB
      (IntegralClosedSubspace.isProper_of_comp_ι_eq D.site D.base D.base_mem hX.1 hY.1 p hp W W'
        q hq).2.1.2 k c = 0 := by
  have hWg := isGood_integralClosedSubspace D sX hX W
  have hW'g := isGood_integralClosedSubspace D sY hY W'
  have hqp : IsProper D.site D.base D.base_mem q :=
    IntegralClosedSubspace.isProper_of_comp_ι_eq D.site D.base D.base_mem hX.1 hY.1 p hp W W' q hq
  have hqgen := pointsMap_genericPoint_eq_of_comp_ι_eq D W W' q hq hgen hWg.1 hW'g.1
  exact properCyclePushforward_eq_zero_of_deltaValue_drop D (W.subspace.ι ≫ sX) hWg
    W.isIntegralSpace (W'.subspace.ι ≫ sY) hW'g W'.isIntegralSpace q hqB hqp hqgen k
    ((IntegralClosedSubspace.deltaValue_comp_ι_genericPoint D sX hX W hWg).trans hWd)
    ((IntegralClosedSubspace.deltaValue_comp_ι_genericPoint D sY hY W' hW'g).trans hW'd) c hc

/-- **The branch `dim_δ(W') = k` of Stacks 0EQC.** For an integral closed subspace `W ⊆ X` of
δ-dimension `k + 1` whose integral closed image `W' = p(W) ⊆ Y` has δ-dimension `k`, and the
morphism `q : W ⟶ W'` over `p` of Stacks 0EEG, the pushforward along `q` of a principal divisor
on `W` is zero. -/
theorem subspaceProperCyclePushforward_eq_zero_of_deltaDimension_eq (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) {p : X ⟶ Y} (hpB : p ≫ sY = sX)
    (hp : IsProper D.site D.base D.base_mem p) (k : ℤ)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (q : W.subspace.toFunctor ⟶ (IntegralClosedSubspace.closureImage D.site D.base D.base_mem
      hY.1 (D.isDecentSpace_of_isGood sY hY) p W).subspace.toFunctor)
    (hq : q ≫ (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
        (D.isDecentSpace_of_isGood sY hY) p W).subspace.ι = W.subspace.ι ≫ p)
    (hWd : deltaDimension D sX W = k + 1)
    (hW'd : deltaDimension D sY (IntegralClosedSubspace.closureImage D.site D.base D.base_mem
      hY.1 (D.isDecentSpace_of_isGood sY hY) p W) = k)
    (c : CycleGroup D (W.subspace.ι ≫ sX) k)
    (hc : IsPrincipalDivisorCycleOfGood D (W.subspace.ι ≫ sX)
      (isGood_integralClosedSubspace D sX hX W) W.isIntegralSpace k c) :
    subspaceProperCyclePushforward D sX hX sY hY hpB hp W
      (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
        (D.isDecentSpace_of_isGood sY hY) p W) q hq k c = 0 :=
  properCyclePushforward_subspace_eq_zero_of_deltaDimension_eq D sX hX sY hY hp k W _ q hq
    (by rw [← Category.assoc, hq, Category.assoc, hpB])
    (IntegralClosedSubspace.ambientGenericPoint_closureImage_eq D.site D.base D.base_mem hX.1
      hY.1 _ p W) hWd hW'd c hc

/-- **The branch `dim_δ(W') = k + 1` of Stacks 0EQC**, for a morphism `q : W ⟶ W'` of integral
closed subspaces over `p` sending the generic point of `W` to that of `W'`: the pushforward along
`q` of a principal divisor `div(f)` on `W` is the principal divisor `div(Nm_{R(W)/R(W')}(f))`
on `W'`, by Stacks 0EQ4
(`AlgebraicGeometry.Space.properCyclePushforward_rationalFunctionPrincipalDivisorCycle`). -/
theorem isPrincipalDivisorCycleOfGood_properCyclePushforward_subspace (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) {p : X ⟶ Y}
    (hp : IsProper D.site D.base D.base_mem p) (k : ℤ)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (W' : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (q : W.subspace.toFunctor ⟶ W'.subspace.toFunctor)
    (hq : q ≫ W'.subspace.ι = W.subspace.ι ≫ p)
    (hqB : q ≫ W'.subspace.ι ≫ sY = W.subspace.ι ≫ sX)
    (hgen : W'.ambientGenericPoint D.site D.base D.base_mem =
      pointsMap D.site D.base D.base_mem X p (W.ambientGenericPoint D.site D.base D.base_mem))
    (hWd : deltaDimension D sX W = k + 1) (hW'd : deltaDimension D sY W' = k + 1)
    (c : CycleGroup D (W.subspace.ι ≫ sX) k)
    (hc : IsPrincipalDivisorCycleOfGood D (W.subspace.ι ≫ sX)
      (isGood_integralClosedSubspace D sX hX W) W.isIntegralSpace k c) :
    IsPrincipalDivisorCycleOfGood D (W'.subspace.ι ≫ sY)
      (isGood_integralClosedSubspace D sY hY W') W'.isIntegralSpace k
      (properCyclePushforward D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
        (W'.subspace.ι ≫ sY) (isGood_integralClosedSubspace D sY hY W') hqB
        (IntegralClosedSubspace.isProper_of_comp_ι_eq D.site D.base D.base_mem hX.1 hY.1 p hp W
          W' q hq).2.1.2 k c) := by
  have hWg := isGood_integralClosedSubspace D sX hX W
  have hW'g := isGood_integralClosedSubspace D sY hY W'
  have hqp : IsProper D.site D.base D.base_mem q :=
    IntegralClosedSubspace.isProper_of_comp_ι_eq D.site D.base D.base_mem hX.1 hY.1 p hp W W' q hq
  have hqgen := pointsMap_genericPoint_eq_of_comp_ι_eq D W W' q hq hgen hWg.1 hW'g.1
  have hdom : IsDominant D.site D.base D.base_mem q := by
    have _ : IrreducibleSpace (points D.site D.base D.base_mem W'.subspace.toFunctor) :=
      W'.isIntegralSpace.2.2
    change DenseRange _
    rw [DenseRange, dense_iff_closure_eq, Set.eq_univ_iff_forall]
    intro y
    have hmem : Space.genericPoint D.site D.base D.base_mem hW'g.1 W'.isIntegralSpace ∈
        Set.range (pointsMap D.site D.base D.base_mem _ q) := ⟨_, hqgen⟩
    refine closure_mono (Set.singleton_subset_iff.2 hmem) ?_
    exact specializes_iff_mem_closure.1
      ((isGenericPoint_genericPoint D.site D.base D.base_mem hW'g.1 W'.isIntegralSpace).specializes
        (Set.mem_univ y))
  have hnX := deltaDimensionClosed_univ_eq_of_deltaDimension_eq D sX hX W hWg _ hWd
  have hnY := deltaDimensionClosed_univ_eq_of_deltaDimension_eq D sY hY W' hW'g _ hW'd
  obtain ⟨g, hg⟩ :=
    IsPrincipalDivisorCycleOfGood.exists_eq_rationalFunctionPrincipalDivisorCycle D hc hnX
  have h0EQ4 := properCyclePushforward_rationalFunctionPrincipalDivisorCycle D
    (W.subspace.ι ≫ sX) hWg (W'.subspace.ι ≫ sY) hW'g W.isIntegralSpace W'.isIntegralSpace hqB
    hqp hdom hnX hnY g
  exact IsPrincipalDivisorCycleOfGood.of_coe_eq D
    (isPrincipalDivisorCycleOfGood_rationalFunctionPrincipalDivisorCycle D _ hW'g
      W'.isIntegralSpace hnY (rationalFunctionNormUnit D.site D.base D.base_mem hWg.1 hW'g.1
        W.isIntegralSpace W'.isIntegralSpace q
        (pointsMap_genericPoint_of_isDominant D.site D.base D.base_mem hWg.1 hW'g.1
          W.isIntegralSpace W'.isIntegralSpace q hdom) g)) (funext fun Z' => by
    have e := congrArg (fun γ : CycleGroup D (W'.subspace.ι ≫ sY) ((k + 1) - 1) =>
      (γ : IntegralClosedSubspace D.site D.base D.base_mem W'.subspace.toFunctor → ℤ) Z') h0EQ4
    rw [← e, properPushforward_apply, properPushforward_apply]
    refine finsum_congr fun Z => ?_
    rw [hg])

/-- **The branch `dim_δ(W') = k + 1` of Stacks 0EQC**, at the integral closed image `W' = p(W)`
and the morphism `q : W ⟶ W'` of Stacks 0EEG. -/
theorem isPrincipalDivisorCycleOfGood_subspaceProperCyclePushforward (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) {p : X ⟶ Y} (hpB : p ≫ sY = sX)
    (hp : IsProper D.site D.base D.base_mem p) (k : ℤ)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (q : W.subspace.toFunctor ⟶ (IntegralClosedSubspace.closureImage D.site D.base D.base_mem
      hY.1 (D.isDecentSpace_of_isGood sY hY) p W).subspace.toFunctor)
    (hq : q ≫ (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
        (D.isDecentSpace_of_isGood sY hY) p W).subspace.ι = W.subspace.ι ≫ p)
    (hWd : deltaDimension D sX W = k + 1)
    (hW'd : deltaDimension D sY (IntegralClosedSubspace.closureImage D.site D.base D.base_mem
      hY.1 (D.isDecentSpace_of_isGood sY hY) p W) = k + 1)
    (c : CycleGroup D (W.subspace.ι ≫ sX) k)
    (hc : IsPrincipalDivisorCycleOfGood D (W.subspace.ι ≫ sX)
      (isGood_integralClosedSubspace D sX hX W) W.isIntegralSpace k c) :
    IsPrincipalDivisorCycleOfGood D
      ((IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
        (D.isDecentSpace_of_isGood sY hY) p W).subspace.ι ≫ sY)
      (isGood_integralClosedSubspace D sY hY
        (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
          (D.isDecentSpace_of_isGood sY hY) p W))
      (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
        (D.isDecentSpace_of_isGood sY hY) p W).isIntegralSpace k
      (subspaceProperCyclePushforward D sX hX sY hY hpB hp W
        (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
          (D.isDecentSpace_of_isGood sY hY) p W) q hq k c) :=
  isPrincipalDivisorCycleOfGood_properCyclePushforward_subspace D sX hX sY hY hp k W _ q hq
    (by rw [← Category.assoc, hq, Category.assoc, hpB])
    (IntegralClosedSubspace.ambientGenericPoint_closureImage_eq D.site D.base D.base_mem hX.1
      hY.1 _ p W) hWd hW'd c hc

end DimensionDrop

/-! ### Stacks 0EQC, step 4 -/

section RationalEquivalence

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- **Steps 1–4 of Stacks 0EQC, reduced to the equal-dimension branch.** Let `p : X ⟶ Y` be
proper over the base. Suppose that for every integral closed subspace `W ⊆ X` of δ-dimension
`k + 1` whose integral closed image `W' = p(W)` has δ-dimension `k + 1`, the pushforward along
the morphism `q : W ⟶ W'` of Stacks 0EEG of a principal divisor on `W` is a principal divisor on
`W'` (the existence form of Stacks 0EQ4). Then proper pushforward carries a `k`-cycle rationally
equivalent to zero to a `k`-cycle rationally equivalent to zero, both read at the canonical
embeddings of Stacks 0ENK.

The other two branches of step 4 are proved:
`AlgebraicGeometry.Space.subspaceProperCyclePushforward_eq_zero_of_deltaDimension_eq` when
`dim_δ(W') = k`, and `AlgebraicGeometry.Space.cycleGroup_eq_zero_of_deltaDimension_lt` when
`dim_δ(W') < k`; `dim_δ(W') > k + 1` does not occur, by
`AlgebraicGeometry.Space.IntegralClosedSubspace.deltaDimension_closureImage_le`. The hypothesis
is discharged by Stacks 0EQ4 in
`AlgebraicGeometry.Space.isRationallyEquivalentToZeroCanonical_properCyclePushforward`. -/
theorem isRationallyEquivalentToZeroCanonical_properCyclePushforward_of_principal
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) {p : X ⟶ Y}
    (hpB : p ≫ sY = sX) (hp : IsProper D.site D.base D.base_mem p) (k : ℤ)
    (hnorm : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X)
      (q : W.subspace.toFunctor ⟶ (IntegralClosedSubspace.closureImage D.site D.base D.base_mem
        hY.1 (D.isDecentSpace_of_isGood sY hY) p W).subspace.toFunctor)
      (hq : q ≫ (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
          (D.isDecentSpace_of_isGood sY hY) p W).subspace.ι = W.subspace.ι ≫ p),
      deltaDimension D sX W = k + 1 →
      deltaDimension D sY (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
        (D.isDecentSpace_of_isGood sY hY) p W) = k + 1 →
      ∀ c : CycleGroup D (W.subspace.ι ≫ sX) k,
        IsPrincipalDivisorCycleOfGood D (W.subspace.ι ≫ sX)
            (isGood_integralClosedSubspace D sX hX W) W.isIntegralSpace k c →
          IsPrincipalDivisorCycleOfGood D
            ((IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
              (D.isDecentSpace_of_isGood sY hY) p W).subspace.ι ≫ sY)
            (isGood_integralClosedSubspace D sY hY
              (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
                (D.isDecentSpace_of_isGood sY hY) p W))
            (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
              (D.isDecentSpace_of_isGood sY hY) p W).isIntegralSpace k
            (subspaceProperCyclePushforward D sX hX sY hY hpB hp W
              (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
                (D.isDecentSpace_of_isGood sY hY) p W) q hq k c))
    (α : CycleGroup D sX k) (hα : IsRationallyEquivalentToZeroCanonical.{v} D sX hX k α) :
    IsRationallyEquivalentToZeroCanonical.{v} D sY hY k
      (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k α) := by
  obtain ⟨J, W, hWfin, c, hWdim, hWprin, rfl⟩ := hα
  choose q hq using fun j : J => IntegralClosedSubspace.exists_hom_closureImage D.site D.base
    D.base_mem hY.1 (D.isDecentSpace_of_isGood sY hY) p (W j)
  set W' : J → IntegralClosedSubspace D.site D.base D.base_mem Y := fun j =>
    IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
      (D.isDecentSpace_of_isGood sY hY) p (W j) with hW'
  set d : ∀ j : J, CycleGroup D ((W' j).subspace.ι ≫ sY) k := fun j =>
    subspaceProperCyclePushforward D sX hX sY hY hpB hp (W j) (W' j) (q j) (hq j) k (c j) with hd
  have hW'fin := locallyFinite_subspacePointSet_closureImage_of_isQuasiCompact D sX hX sY hY hpB
    hp.2.1.2 W hWfin
  have hdich : ∀ j : J,
      (deltaDimension D sY (W' j) = k + 1 →
          IsPrincipalDivisorCycleOfGood D ((W' j).subspace.ι ≫ sY)
            (isGood_integralClosedSubspace D sY hY (W' j)) (W' j).isIntegralSpace k (d j)) ∧
        (deltaDimension D sY (W' j) ≠ k + 1 → d j = 0) := by
    intro j
    refine ⟨fun h => hnorm (W j) (q j) (hq j) (hWdim j) h (c j) (hWprin j), fun h => ?_⟩
    have hle : deltaDimension D sY (W' j) ≤ k + 1 := by
      rw [← hWdim j]
      exact IntegralClosedSubspace.deltaDimension_closureImage_le D sX sY hX hY p hpB (W j)
    rcases eq_or_lt_of_le (show deltaDimension D sY (W' j) ≤ k by omega) with heq | hlt
    · exact subspaceProperCyclePushforward_eq_zero_of_deltaDimension_eq D sX hX sY hY hpB hp k
        (W j) (q j) (hq j) (hWdim j) heq (c j) (hWprin j)
    · exact cycleGroup_eq_zero_of_deltaDimension_lt D sY hY (W' j) k hlt (d j)
  set S : Set J := {j : J | deltaDimension D sY (W' j) = k + 1} with hSdef
  have hsupp : ∀ j : J,
      (integralClosedSubspacePushforward D sY hY (W' j) k (d j)).1
        ≠ (0 : IntegralClosedSubspace D.site D.base D.base_mem Y → ℤ) → j ∈ S := by
    intro j hj
    by_contra hjS
    refine hj ?_
    rw [(hdich j).2 hjS, map_zero]
    rfl
  refine ⟨↥S, fun jj => W' jj.1, hW'fin.comp_injective Subtype.val_injective,
    fun jj => d jj.1, fun jj => jj.2, fun jj => (hdich jj.1).1 jj.2, ?_⟩
  refine Subtype.ext (funext fun Z' => ?_)
  rw [properCyclePushforward_cycleFamilySum_apply D sX hX sY hY hpB hp.2.1.2 k W hWfin c Z',
    cycleFamilySum_apply]
  have hGsub : (∑ᶠ j : J, (integralClosedSubspacePushforward D sY hY (W' j) k (d j)).1 Z') =
      ∑ᶠ jj : ↥S, (integralClosedSubspacePushforward D sY hY (W' jj.1) k (d jj.1)).1 Z' :=
    ((finsum_mem_univ _).symm.trans
        (finsum_mem_inter_support_eq' _ Set.univ S fun j hj =>
          ⟨fun _ => hsupp j fun hzero => hj (by rw [hzero]; rfl),
            fun _ => Set.mem_univ j⟩)).trans
      (finsum_set_coe_eq_finsum_mem S).symm
  refine (finsum_congr fun j => ?_).trans hGsub
  exact congrArg (fun β : CycleGroup D sY k => β.1 Z')
    (properCyclePushforward_integralClosedSubspacePushforward_closureImage D sX hX sY hY hpB hp
      (W j) (W' j) (q j) (hq j) k (c j))


end RationalEquivalence

/-! ### Stacks 0EQC -/

section Final

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- **Stacks 0EQC, for cycles rationally equivalent to zero.** Let `p : X ⟶ Y` be a proper
morphism of good algebraic spaces over the base. If `α ∈ Z_k(X)` is rationally equivalent to
zero then so is `p_*α`. -/
theorem isRationallyEquivalentToZeroCanonical_properCyclePushforward (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) {p : X ⟶ Y} (hpB : p ≫ sY = sX)
    (hp : IsProper D.site D.base D.base_mem p) (k : ℤ) (α : CycleGroup D sX k)
    (hα : IsRationallyEquivalentToZeroCanonical.{v} D sX hX k α) :
    IsRationallyEquivalentToZeroCanonical.{v} D sY hY k
      (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k α) :=
  isRationallyEquivalentToZeroCanonical_properCyclePushforward_of_principal D sX hX sY hY hpB hp k
    (fun W q hq hWd hW'd c hc =>
      isPrincipalDivisorCycleOfGood_subspaceProperCyclePushforward D sX hX sY hY hpB hp k W q hq
        hWd hW'd c hc) α hα

/-- **Stacks 0EQC.** In Situation 0EDT let `X/B` and `Y/B` be good and let `p : X ⟶ Y` be a
proper morphism over the base. If `α, β ∈ Z_k(X)` are rationally equivalent, then `p_*α` is
rationally equivalent to `p_*β`.

Rational equivalence is that of Stacks 0EQ6 with the summands `div(f_j)` read at the canonical
embeddings `R(W_j) → Q(𝒪^h_{W_j,ξ})` of Stacks 0ENK
(`AlgebraicGeometry.Space.RationallyEquivalentCanonical`), and `p_*` is the proper pushforward of
cycles of Stacks 0EP1. -/
@[stacks 0EQC]
theorem rationallyEquivalentCanonical_properCyclePushforward (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) {p : X ⟶ Y} (hpB : p ≫ sY = sX)
    (hp : IsProper D.site D.base D.base_mem p) (k : ℤ) {α β : CycleGroup D sX k}
    (h : RationallyEquivalentCanonical.{v} D sX hX k α β) :
    RationallyEquivalentCanonical.{v} D sY hY k
      (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k α)
      (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k β) :=
  rationallyEquivalentCanonical_cycleHom.{v} D sY hY sX hX k k
    (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k)
    (isRationallyEquivalentToZeroCanonical_properCyclePushforward.{v} D sX hX sY hY hpB hp k) h

/-- **Proper pushforward on Chow groups (Stacks 0EQC).** The homomorphism
`p_* : CH_k(X) → CH_k(Y)` induced by the proper pushforward of cycles of Stacks 0EP1, on the
Chow groups of Stacks 0EQ6 at the canonical embeddings of Stacks 0ENK. -/
def chowGroupCanonicalProperPushforward (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) {p : X ⟶ Y} (hpB : p ≫ sY = sX)
    (hp : IsProper D.site D.base D.base_mem p) (k : ℤ) :
    chowGroupCanonical.{v} D sX hX k →+ chowGroupCanonical.{v} D sY hY k :=
  chowGroupCanonicalHomOfCycleHom.{v} D sY hY sX hX k k
    (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k)
    (isRationallyEquivalentToZeroCanonical_properCyclePushforward.{v} D sX hX sY hY hpB hp k)

/-- The class of `p_*α` in `CH_k(Y)` is the image of the class of `α` in `CH_k(X)` under
`AlgebraicGeometry.Space.chowGroupCanonicalProperPushforward`. -/
@[simp]
theorem chowGroupCanonicalProperPushforward_chowClassCanonical (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) {p : X ⟶ Y} (hpB : p ≫ sY = sX)
    (hp : IsProper D.site D.base D.base_mem p) (k : ℤ) (α : CycleGroup D sX k) :
    chowGroupCanonicalProperPushforward.{v} D sX hX sY hY hpB hp k
        (chowClassCanonical.{v} D sX hX k α) =
      chowClassCanonical.{v} D sY hY k (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k α) :=
  rfl

end Final

end AlgebraicGeometry.Space

end
