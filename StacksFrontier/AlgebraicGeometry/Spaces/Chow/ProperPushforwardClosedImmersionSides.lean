module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardClosedImmersionSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardFirstChernCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ResidueFieldDegree
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion

/-!
# Proper pushforward along a square with closed immersions on two sides

In Situation 0EDT consider a commutative square of good algebraic spaces over `B`

```
T  --g-->  T'
|i         |i'
v          v
X  --p-->  Y
```

in which `i` and `i'` are closed immersions and `p`, `g` are quasi-compact. Stacks 0EP2 says
that proper pushforward of cycles is functorial; for this square it gives

`p_* ∘ i_* = i'_* ∘ g_*` on `Z_k(T)`,

where `i_*` and `i'_*` are the pushforwards along closed immersions of the localization sequence
(`AlgebraicGeometry.Space.cycleGroupClosedPushforward`) and `p_*`, `g_*` those of Stacks 0EP1
(`AlgebraicGeometry.Space.properCyclePushforward`). This is the square through which the source
reduces Stacks 0EQT to the case of integral spaces: `T = W ⊆ X` is an integral closed subspace,
`T' = W' ⊆ Y` the closure of its image and `g = p|_W`.

Three facts about a closed immersion `i` enter. The residue fields of `T` and `X` agree along `i`
(Stacks 0EMX), so `i` has residue degree `1` at every point; the image along `i` of an integral
closed subspace has the same δ-dimension; and `|i|` is a closed embedding, so the closure of the
image along `p ∘ i = i' ∘ g` of an integral closed subspace `V ⊆ T` is the image along `i'` of the
closure of the image of `V` along `g`. Multiplicativity of residue degrees in a tower then gives
`deg(i(V)/p(i(V))) = deg(V/g(V))`, which is the coefficient identity behind the square.

## Main results

* `AlgebraicGeometry.Space.IntegralClosedSubspace.closureImage_pushforward_of_comp_eq`: the closure
  of the image of `i(V)` along `p` is the image along `i'` of the closure of the image of `V`
  along `g`.
* `AlgebraicGeometry.Space.properCycleDegree_pushforward_of_comp_eq`: the degree of Stacks 0EP1,
  part (1), of `i(V)` along `p` is that of `V` along `g`.
* `AlgebraicGeometry.Space.properCyclePushforward_cycleGroupClosedPushforward_of_comp_eq`:
  `p_*(i_* c) = i'_*(g_* c)` for every `k`-cycle `c` on `T`.
* `AlgebraicGeometry.Space.properCyclePushforward_integralClosedSubspacePushforward_of_comp_ι_eq`:
  the same for the square of an integral closed subspace `W ⊆ X` over an integral closed
  subspace `W' ⊆ Y`.
* `AlgebraicGeometry.Space.ProperPushforwardChernComparison.of_componentCycle_comm`: the first of
  the two inputs of `AlgebraicGeometry.Space.ProperPushforwardChernComparison` holds, so that
  structure is determined by its second input alone.

## References

* [Stacks Project, Tag 0EP1](https://stacks.math.columbia.edu/tag/0EP1)
* [Stacks Project, Tag 0EP2](https://stacks.math.columbia.edu/tag/0EP2)
* [Stacks Project, Tag 0EMX](https://stacks.math.columbia.edu/tag/0EMX)
* [Stacks Project, Tag 0EQT](https://stacks.math.columbia.edu/tag/0EQT)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Residue degrees and closures of images along closed immersions -/

section OverBase

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y T T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The closure of an image across a square with closed immersions on two sides.** Let
`g ≫ i' = i ≫ p` with `i : T → X` and `i' : T' → Y` closed immersions. For an integral closed
subspace `V ⊆ T`, the closure of the image along `p` of its image `i(V) ⊆ X` is the image along
`i'` of the closure of the image of `V` along `g`: on point sets, `|i'|` is a closed embedding, so
it carries the closure of `|g|(|V|)` to the closure of `|i'|(|g|(|V|)) = |p|(|i|(|V|))`. -/
theorem IntegralClosedSubspace.closureImage_pushforward_of_comp_eq
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hT : IsAlgebraicSpace B S hS T) (hT' : IsAlgebraicSpace B S hS T')
    (hXdec : IsDecentSpace B S hS X) (hYdec : IsDecentSpace B S hS Y)
    (hT'dec : IsDecentSpace B S hS T') {i : T ⟶ X} (hi : IsClosedImmersion B S hS i)
    {i' : T' ⟶ Y} (hi' : IsClosedImmersion B S hS i') {p : X ⟶ Y} {g : T ⟶ T'}
    (hsq : g ≫ i' = i ≫ p) (V : IntegralClosedSubspace B S hS T) :
    IntegralClosedSubspace.closureImage B S hS hY hYdec p
        (IntegralClosedSubspace.pushforward B S hS hX hT hXdec hi V) =
      IntegralClosedSubspace.pushforward B S hS hY hT' hYdec hi'
        (IntegralClosedSubspace.closureImage B S hS hT' hT'dec g V) := by
  refine injective_integralClosedSubspaceSupport B S hS hY (IrreducibleCloseds.ext ?_)
  calc subspacePointSet B S hS Y (IntegralClosedSubspace.closureImage B S hS hY hYdec p
          (IntegralClosedSubspace.pushforward B S hS hX hT hXdec hi V)).subspace
      = closure (pointsMap B S hS X p '' (pointsMap B S hS T i ''
          subspacePointSet B S hS T V.subspace)) := by
        rw [IntegralClosedSubspace.subspacePointSet_closureImage,
          IntegralClosedSubspace.subspacePointSet_pushforward]
    _ = closure (pointsMap B S hS T (i ≫ p) '' subspacePointSet B S hS T V.subspace) := by
        rw [pointsMap_comp, Set.image_comp]
    _ = closure (pointsMap B S hS T' i' '' (pointsMap B S hS T g ''
          subspacePointSet B S hS T V.subspace)) := by
        rw [← hsq, pointsMap_comp, Set.image_comp]
    _ = pointsMap B S hS T' i' '' closure (pointsMap B S hS T g ''
          subspacePointSet B S hS T V.subspace) :=
        (isClosedEmbedding_pointsMap_of_isClosedImmersion B S hS hY hi').closure_image_eq _
    _ = subspacePointSet B S hS Y (IntegralClosedSubspace.pushforward B S hS hY hT' hYdec hi'
          (IntegralClosedSubspace.closureImage B S hS hT' hT'dec g V)).subspace := by
        rw [IntegralClosedSubspace.subspacePointSet_pushforward,
          IntegralClosedSubspace.subspacePointSet_closureImage]

end OverBase

/-! ### The degree of Stacks 0EP1 across the square -/

section Square

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y T T' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    {sX : X ⟶ D.space} (hX : D.IsGood sX) {sY : Y ⟶ D.space} (hY : D.IsGood sY)
    {sT : T ⟶ D.space} (hT : D.IsGood sT) {sT' : T' ⟶ D.space} (hT' : D.IsGood sT')
    {i : T ⟶ X} (hi : IsClosedImmersion D.site D.base D.base_mem i) (hiB : i ≫ sX = sT)
    {i' : T' ⟶ Y} (hi' : IsClosedImmersion D.site D.base D.base_mem i') (hi'B : i' ≫ sY = sT')
    {p : X ⟶ Y} {g : T ⟶ T'} (hsq : g ≫ i' = i ≫ p)

/-- `IntegralClosedSubspace.closureImage_pushforward_of_comp_eq` for good spaces. -/
private theorem closureImage_pushforward_of_comp_eq_of_isGood
    (hsq : g ≫ i' = i ≫ p) (V : IntegralClosedSubspace D.site D.base D.base_mem T) :
    IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
        (D.isDecentSpace_of_isGood sY hY) p
        (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hT.1
          (D.isDecentSpace_of_isGood sX hX) hi V) =
      IntegralClosedSubspace.pushforward D.site D.base D.base_mem hY.1 hT'.1
        (D.isDecentSpace_of_isGood sY hY) hi'
        (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hT'.1
          (D.isDecentSpace_of_isGood sT' hT') g V) :=
  IntegralClosedSubspace.closureImage_pushforward_of_comp_eq D.site D.base D.base_mem hX.1
    hY.1 hT.1 hT'.1 (D.isDecentSpace_of_isGood sX hX) (D.isDecentSpace_of_isGood sY hY)
    (D.isDecentSpace_of_isGood sT' hT') hi hi' hsq V

include hi' hsq in
/-- The degree of the extension of function fields of the image `i(V) ⊆ X` of an integral closed
subspace `V ⊆ T` along `p` is that of `V` along `g`: both are read off the tower of residue
fields along `i ≫ p = g ≫ i'`, in which the two closed immersions have degree `1`. -/
theorem functionFieldDegree_pushforward_of_comp_eq
    (V : IntegralClosedSubspace D.site D.base D.base_mem T) :
    functionFieldDegree D sX hX sY hY p
        (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hT.1
          (D.isDecentSpace_of_isGood sX hX) hi V) =
      functionFieldDegree D sT hT sT' hT' g V := by
  have hXdec := D.isDecentSpace_of_isGood sX hX
  have hYdec := D.isDecentSpace_of_isGood sY hY
  have hTdec := D.isDecentSpace_of_isGood sT hT
  have hT'dec := D.isDecentSpace_of_isGood sT' hT'
  have h₁ := residueDegree_comp D.site D.base D.base_mem T X Y hX.1 hY.1 hTdec hXdec hYdec i p
    (V.ambientGenericPoint D.site D.base D.base_mem)
  have h₂ := residueDegree_comp D.site D.base D.base_mem T T' Y hT'.1 hY.1 hTdec hT'dec hYdec g i'
    (V.ambientGenericPoint D.site D.base D.base_mem)
  rw [residueDegree_eq_one_of_isClosedImmersion D.site D.base D.base_mem hX.1 hXdec hTdec hi,
    mul_one] at h₁
  rw [residueDegree_eq_one_of_isClosedImmersion D.site D.base D.base_mem hY.1 hYdec hT'dec hi',
    one_mul, hsq, h₁] at h₂
  change residueDegree D.site D.base D.base_mem X Y hY.1 hXdec hYdec p
      ((IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hT.1 hXdec hi
        V).ambientGenericPoint D.site D.base D.base_mem) =
    residueDegree D.site D.base D.base_mem T T' hT'.1 hTdec hT'dec g
      (V.ambientGenericPoint D.site D.base D.base_mem)
  rwa [IntegralClosedSubspace.ambientGenericPoint_pushforward]

include hi' hsq hiB hi'B in
/-- **The degree of Stacks 0EP1, part (1), across the square.** The coefficient of the closure
of the image in the pushforward along `p` of the image `i(V) ⊆ X` of an integral closed subspace
`V ⊆ T` is the corresponding coefficient for `V` along `g`. The closures of the images correspond
under `i'` (`AlgebraicGeometry.Space.IntegralClosedSubspace.closureImage_pushforward_of_comp_eq`),
images along closed immersions over the base keep their δ-dimension, and the degrees of the
function field extensions agree
(`AlgebraicGeometry.Space.functionFieldDegree_pushforward_of_comp_eq`). -/
theorem properCycleDegree_pushforward_of_comp_eq
    (V : IntegralClosedSubspace D.site D.base D.base_mem T) :
    properCycleDegree D sX hX sY hY p
        (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hT.1
          (D.isDecentSpace_of_isGood sX hX) hi V) =
      properCycleDegree D sT hT sT' hT' g V := by
  unfold properCycleDegree
  rw [closureImage_pushforward_of_comp_eq_of_isGood D hX hY hT hT' hi hi' hsq V,
    IntegralClosedSubspace.deltaDimension_pushforward D sY hY.2.2 hY.1 hT'.1
      (D.isDecentSpace_of_isGood sY hY) hi',
    IntegralClosedSubspace.deltaDimension_pushforward D sX hX.2.2 hX.1 hT.1
      (D.isDecentSpace_of_isGood sX hX) hi, hiB, hi'B,
    functionFieldDegree_pushforward_of_comp_eq D hX hY hT hT' hi hi' hsq V]

include hi' hsq hiB hi'B in
/-- The multiplicity of the image `i'(V') ⊆ Y` of an integral closed subspace `V' ⊆ T'` in the
pushforward along `p` of the image `i(V) ⊆ X` is the multiplicity of `V'` in the pushforward of
`V` along `g`. -/
theorem properCycleMult_pushforward_pushforward_of_comp_eq
    (V : IntegralClosedSubspace D.site D.base D.base_mem T)
    (V' : IntegralClosedSubspace D.site D.base D.base_mem T') :
    properCycleMult D sX hX sY hY p
        (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hT.1
          (D.isDecentSpace_of_isGood sX hX) hi V)
        (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hY.1 hT'.1
          (D.isDecentSpace_of_isGood sY hY) hi' V') =
      properCycleMult D sT hT sT' hT' g V V' := by
  unfold properCycleMult
  rw [closureImage_pushforward_of_comp_eq_of_isGood D hX hY hT hT' hi hi' hsq V,
    properCycleDegree_pushforward_of_comp_eq D hX hY hT hT' hi hiB hi' hi'B hsq V]
  by_cases h : IntegralClosedSubspace.closureImage D.site D.base D.base_mem hT'.1
      (D.isDecentSpace_of_isGood sT' hT') g V = V'
  · rw [ite_eq_left (congrArg _ h), ite_eq_left h]
  · rw [ite_eq_right fun h' => h (IntegralClosedSubspace.injective_pushforward D.site D.base
      D.base_mem hY.1 hT'.1 (D.isDecentSpace_of_isGood sY hY) hi' h'), ite_eq_right h]

include hi' hsq in
/-- An integral closed subspace of `Y` which is not the image of one of `T'` has multiplicity
zero in the pushforward along `p` of the image `i(V) ⊆ X`: the closure of that image lies in the
image of `i'`. -/
theorem properCycleMult_pushforward_of_comp_eq_of_forall_ne
    (V : IntegralClosedSubspace D.site D.base D.base_mem T)
    (Z' : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (hZ' : ∀ V', IntegralClosedSubspace.pushforward D.site D.base D.base_mem hY.1 hT'.1
      (D.isDecentSpace_of_isGood sY hY) hi' V' ≠ Z') :
    properCycleMult D sX hX sY hY p
        (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hT.1
          (D.isDecentSpace_of_isGood sX hX) hi V) Z' = 0 := by
  refine properCycleMult_eq_zero_of_ne D sX hX sY hY p _ ?_
  rw [closureImage_pushforward_of_comp_eq_of_isGood D hX hY hT hT' hi hi' hsq V]
  exact hZ' _

/-! ### Stacks 0EP2 for the square -/

include hi' hsq hiB hi'B in
/-- **Stacks 0EP2 for a square with closed immersions on two sides.** Let `g ≫ i' = i ≫ p` be a
commutative square of good algebraic spaces over `B`, with `i : T → X` and `i' : T' → Y` closed
immersions over `B` and `p : X → Y`, `g : T → T'` quasi-compact over `B`. For every `k`-cycle `c`
on `T`,

`p_*(i_* c) = i'_*(g_* c)` in `Z_k(Y)`.

At the image `i'(V')` of an integral closed subspace `V' ⊆ T'` both coefficients are
`∑_V c_V · m(V, V')`, the multiplicity `m(V, V')` of `V'` in `g_*[V]` being that of `i'(V')` in
`p_*[i(V)]` (`AlgebraicGeometry.Space.properCycleMult_pushforward_pushforward_of_comp_eq`); at an
integral closed subspace of `Y` not of that form both coefficients vanish. -/
theorem properCyclePushforward_cycleGroupClosedPushforward_of_comp_eq (hpB : p ≫ sY = sX)
    (hp : IsQuasiCompact D.site D.base D.base_mem p) (hgB : g ≫ sT' = sT)
    (hg : IsQuasiCompact D.site D.base D.base_mem g) (k : ℤ) (c : CycleGroup D sT k) :
    properCyclePushforward D sX hX sY hY hpB hp k
        (cycleGroupClosedPushforward D hX.1 hT.1 (D.isDecentSpace_of_isGood sX hX) hi sX hX.2.2
          sT hiB k c) =
      cycleGroupClosedPushforward D hY.1 hT'.1 (D.isDecentSpace_of_isGood sY hY) hi' sY hY.2.2
        sT' hi'B k (properCyclePushforward D sT hT sT' hT' hgB hg k c) := by
  have hXdec := D.isDecentSpace_of_isGood sX hX
  have hYdec := D.isDecentSpace_of_isGood sY hY
  refine Subtype.ext (funext fun Z' => ?_)
  change (∑ᶠ Z, cycleClosedPushforward D hX.1 hT.1 hXdec hi c.1 Z *
      properCycleMult D sX hX sY hY p Z Z') =
    cycleClosedPushforward D hY.1 hT'.1 hYdec hi' (properCyclePushforward D sT hT sT' hT' hgB hg k
      c).1 Z'
  have hsupp : (Function.support fun Z => cycleClosedPushforward D hX.1 hT.1 hXdec hi c.1 Z *
      properCycleMult D sX hX sY hY p Z Z') ⊆
      Set.range (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hT.1 hXdec hi) :=
    fun Z hZ => by
      by_contra hne
      refine hZ ?_
      change cycleClosedPushforward D hX.1 hT.1 hXdec hi c.1 Z * _ = 0
      rw [cycleClosedPushforward_apply_of_forall_ne D hX.1 hT.1 hXdec hi _ Z
        fun V hV => hne ⟨V, hV⟩, zero_mul]
  rw [← finsum_mem_univ, ← finsum_mem_inter_support_eq _ (Set.range
      (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hT.1 hXdec hi)) Set.univ
      (by rw [Set.univ_inter, Set.inter_eq_right.2 hsupp]),
    finsum_mem_range (IntegralClosedSubspace.injective_pushforward D.site D.base D.base_mem hX.1
      hT.1 hXdec hi)]
  simp_rw [cycleClosedPushforward_apply_pushforward]
  by_cases hZ' : ∃ V', IntegralClosedSubspace.pushforward D.site D.base D.base_mem hY.1 hT'.1
      hYdec hi' V' = Z'
  · obtain ⟨V', rfl⟩ := hZ'
    rw [cycleClosedPushforward_apply_pushforward, properPushforward_apply]
    refine finsum_congr fun V => ?_
    rw [properCycleMult_pushforward_pushforward_of_comp_eq D hX hY hT hT' hi hiB hi' hi'B hsq]
  · rw [cycleClosedPushforward_apply_of_forall_ne D hY.1 hT'.1 hYdec hi' _ Z'
      fun V' hV' => hZ' ⟨V', hV'⟩]
    refine finsum_eq_zero_of_forall_eq_zero fun V => ?_
    rw [properCycleMult_pushforward_of_comp_eq_of_forall_ne D hX hY hT hT' hi hi' hsq V
      Z' fun V' hV' => hZ' ⟨V', hV'⟩, mul_zero]

end Square

/-! ### Integral closed subspaces -/

section IntegralSubspaces

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    {sX : X ⟶ D.space} (hX : D.IsGood sX) {sY : Y ⟶ D.space} (hY : D.IsGood sY)

/-- **Stacks 0EP2 for the square of an integral closed subspace over an integral closed
subspace.** Let `W ⊆ X` and `W' ⊆ Y` be integral closed subspaces and `g : W → W'` a morphism over
`p : X → Y`, both `p` and `g` quasi-compact over `B`. Pushing a `k`-cycle on `W` forward along
`W → X → Y` is pushing it forward along `W → W' → Y`. -/
theorem properCyclePushforward_integralClosedSubspacePushforward_of_comp_ι_eq {p : X ⟶ Y}
    (hpB : p ≫ sY = sX) (hp : IsQuasiCompact D.site D.base D.base_mem p)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (W' : IntegralClosedSubspace D.site D.base D.base_mem Y)
    {g : W.subspace.toFunctor ⟶ W'.subspace.toFunctor} (hg : g ≫ W'.subspace.ι = W.subspace.ι ≫ p)
    (hgq : IsQuasiCompact D.site D.base D.base_mem g) (k : ℤ)
    (c : CycleGroup D (W.subspace.ι ≫ sX) k) :
    properCyclePushforward D sX hX sY hY hpB hp k
        (integralClosedSubspacePushforward D sX hX W k c) =
      integralClosedSubspacePushforward D sY hY W' k
        (properCyclePushforward D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
          (W'.subspace.ι ≫ sY) (isGood_integralClosedSubspace D sY hY W')
          (IntegralClosedSubspace.comp_structure_of_comp_ι_eq D hpB hg) hgq k c) :=
  properCyclePushforward_cycleGroupClosedPushforward_of_comp_eq D hX hY
    (isGood_integralClosedSubspace D sX hX W) (isGood_integralClosedSubspace D sY hY W')
    W.isClosedSubspace.2 rfl W'.isClosedSubspace.2 rfl hg hpB hp _ hgq k c

/-- **The first input of `AlgebraicGeometry.Space.ProperPushforwardChernComparison` holds.** For a
proper `p : X → Y` over `B` and component rules `chernX`, `chernY` of Stacks 0EQJ, the structure
is determined by its second field, Stacks 0EQS along the component morphisms of Stacks 0EEG: its
first field, Stacks 0EP2 for the square of the source's reduction, is
`AlgebraicGeometry.Space.properCyclePushforward_integralClosedSubspacePushforward_of_comp_ι_eq`. -/
theorem ProperPushforwardChernComparison.of_componentCycle_comm {p : X ⟶ Y} (hpB : p ≫ sY = sX)
    (hp : IsProper D.site D.base D.base_mem p) (k : ℤ)
    (chernX : FirstChernComponentCycleRule D sX k) (chernY : FirstChernComponentCycleRule D sY k)
    (h : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X)
      (hW : deltaDimension D sX W = k + 1)
      (W' : IntegralClosedSubspace D.site D.base D.base_mem Y)
      (g : W.subspace.toFunctor ⟶ W'.subspace.toFunctor)
      (hg : g ≫ W'.subspace.ι = W.subspace.ι ≫ p)
      (_hdom : IsDominant D.site D.base D.base_mem g),
      properCyclePushforward D (W.subspace.ι ≫ sX)
            (isGood_integralClosedSubspace D sX hX W) (W'.subspace.ι ≫ sY)
            (isGood_integralClosedSubspace D sY hY W')
            (IntegralClosedSubspace.comp_structure_of_comp_ι_eq D hpB hg)
            (IntegralClosedSubspace.isQuasiCompact_of_comp_ι_eq D hX hY hp hg) k (chernX W hW) =
        properCycleDegree D sX hX sY hY p W • chernComponentCycleOrZero D sY k chernY W') :
    ProperPushforwardChernComparison D hX hY hpB hp k chernX chernY where
  properPushforward_pushforward W W' _g hg _ c :=
    properCyclePushforward_integralClosedSubspacePushforward_of_comp_ι_eq D hX hY hpB hp.2.1.2 W W'
      hg _ k c
  componentCycle_comm := h

end IntegralSubspaces

end AlgebraicGeometry.Space

end
