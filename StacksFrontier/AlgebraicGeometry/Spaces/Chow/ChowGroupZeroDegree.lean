module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChowGroupOfPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChow.ProperPushforwardChow
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ZeroCycleDegree

/-!
# The degree of a zero cycle on a proper algebraic space over a field

Let `k` be a field and `p : X ⟶ Spec(k)` a proper morphism of algebraic spaces. **Stacks 0ESG**
defines the *degree of a zero cycle* on `X` as the composite of proper pushforward

  `p_* : CH_0(X) ⟶ CH_0(Spec(k))`

(Stacks 0EQC) with the natural isomorphism `CH_0(Spec(k)) ≅ ℤ` which sends `[Spec(k)]` to `1`.

Here proper pushforward of cycles is Stacks 0EP1,
`AlgebraicGeometry.Space.properCyclePushforward`, and its descent to Chow groups is
`AlgebraicGeometry.Space.chowGroupProperPushforward`, well defined by Stacks 0EQC. The natural
isomorphism is `AlgebraicGeometry.Space.chowGroupZeroEquivInt`.

## Main definitions

* `AlgebraicGeometry.Space.chowGroupZeroDegree`: **Stacks 0ESG**, the degree
  `deg : CH_0(X) ⟶ ℤ`.

## Main results

* `AlgebraicGeometry.Space.properCyclePushforward_apply_eq_cycleDegree`: the coefficient of the
  pushforward of a zero cycle to a target with one point is its degree.
* `AlgebraicGeometry.Space.chowGroupZeroDegree_chowClass`: the degree of the class of a zero
  cycle is the degree of the cycle, `AlgebraicGeometry.Space.cycleDegree`.
* `AlgebraicGeometry.Space.chowGroupZeroDegree_chowClass_eq_finsum`: the degree of the class of
  `∑ n_Z [Z]` is `∑ n_Z deg(Z)`, the computation of Stacks 0ESH.

## Implementation notes

As in `StacksFrontier.AlgebraicGeometry.Spaces.Chow.ZeroCycleDegree`, the target `Spec(k)` is a good
algebraic space `Y` over the base of Situation 0EDT with the two properties of `Spec(k)` that are
used: its space of points is a single point, and the dimension function vanishes there, which is
what makes `[Spec(k)]` a zero cycle and `CH_0(Spec(k))` a copy of `ℤ`. The unique integral closed
subspace of `Y`, at which the isomorphism `CH_0(Y) ≅ ℤ` reads the coefficient, is an argument;
supplying it is how nonemptiness of `Y` enters.

## References

* [Stacks Project, Tag 0ESG](https://stacks.math.columbia.edu/tag/0ESG)
* [Stacks Project, Tag 0EQC](https://stacks.math.columbia.edu/tag/0EQC)
* [Stacks Project, Tag 0EP1](https://stacks.math.columbia.edu/tag/0EP1)
* [Stacks Project, Tag 0ESH](https://stacks.math.columbia.edu/tag/0ESH)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- Over a target with one point at which the dimension function vanishes, the coefficient of
the proper pushforward of a zero cycle is its degree. -/
theorem properCyclePushforward_apply_eq_cycleDegree (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) {p : X ⟶ Y} (hbase : p ≫ sY = sX)
    (hp : IsProper D.site D.base D.base_mem p)
    (hpt : Subsingleton (points D.site D.base D.base_mem Y))
    (hδ : ∀ y : points D.site D.base D.base_mem Y, D.deltaValue sY y = 0)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y) (α : CycleGroup D sX 0) :
    (properCyclePushforward D sX hX sY hY hbase hp.2.1.2 0 α).1 W =
      cycleDegree D sX hX sY hY hbase hp W α := by
  rw [cycleDegree_eq_finsum D sX hX sY hY hbase hp hpt hδ W α]
  show ∑ᶠ Z, α.1 Z * properCycleMult D sX hX sY hY p Z W = _
  refine finsum_congr fun Z => ?_
  by_cases hZ : α.1 Z = 0
  · rw [hZ, zero_mul, zero_mul]
  · have himg : IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
        (D.isDecentSpace_of_isGood sY hY) p Z = W :=
      IntegralClosedSubspace.eq_of_subsingleton_points D.site D.base D.base_mem hY.1 hpt _ _
    have hdim : deltaDimension D sY (IntegralClosedSubspace.closureImage D.site D.base
        D.base_mem hY.1 (D.isDecentSpace_of_isGood sY hY) p Z) = deltaDimension D sX Z := by
      rw [α.2.2 Z hZ]
      exact hδ _
    rw [properCycleMult, if_pos himg, properCycleDegree, if_pos hdim]
    rfl

/-- Let `p : X ⟶ Y` be a proper morphism of good algebraic spaces over the base,
where `Y` plays the role of `Spec(k)`: its space of points is a single point, the dimension
function vanishes there, and `W` is its integral closed subspace. The *degree of a zero cycle* on
`X` is the composite

  `deg : CH_0(X) ⟶ CH_0(Y) ⟶ ℤ`

of proper pushforward `p_*`, `AlgebraicGeometry.Space.chowGroupProperPushforward`, with the
natural isomorphism `CH_0(Y) ≅ ℤ` sending the class of `[W]` to `1`,
`AlgebraicGeometry.Space.chowGroupZeroEquivInt`. -/
@[stacks 0ESG]
def chowGroupZeroDegree (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) {p : X ⟶ Y} (hbase : p ≫ sY = sX)
    (hp : IsProper D.site D.base D.base_mem p)
    (hpt : Subsingleton (points D.site D.base D.base_mem Y))
    (hδ : ∀ y : points D.site D.base D.base_mem Y, D.deltaValue sY y = 0)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y) :
    chowGroup.{v} D sX hX 0 →+ ℤ :=
  (chowGroupZeroEquivInt.{v} D sY hY hpt hδ W).toAddMonoidHom.comp
    (chowGroupProperPushforward.{v} D sX hX sY hY hbase hp 0)

/-- The degree of the class of a zero cycle is its degree as a cycle, the coefficient of its
pushforward at the point. -/
@[simp]
theorem chowGroupZeroDegree_chowClass (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) {p : X ⟶ Y} (hbase : p ≫ sY = sX)
    (hp : IsProper D.site D.base D.base_mem p)
    (hpt : Subsingleton (points D.site D.base D.base_mem Y))
    (hδ : ∀ y : points D.site D.base D.base_mem Y, D.deltaValue sY y = 0)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y) (α : CycleGroup D sX 0) :
    chowGroupZeroDegree.{v} D sX hX sY hY hbase hp hpt hδ W (chowClass.{v} D sX hX 0 α) =
      cycleDegree D sX hX sY hY hbase hp W α :=
  properCyclePushforward_apply_eq_cycleDegree D sX hX sY hY hbase hp hpt hδ W α

/-- The degree of the class of `α = ∑ n_Z [Z]` is `∑ n_Z deg(Z)`, the sum running over the
integral closed subspaces of `X` and `deg(Z)` being the degree `[R(Z) : k]` of `Z → Spec(k)`;
this is the computation of Stacks 0ESH. -/
theorem chowGroupZeroDegree_chowClass_eq_finsum (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) {p : X ⟶ Y} (hbase : p ≫ sY = sX)
    (hp : IsProper D.site D.base D.base_mem p)
    (hpt : Subsingleton (points D.site D.base D.base_mem Y))
    (hδ : ∀ y : points D.site D.base D.base_mem Y, D.deltaValue sY y = 0)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y) (α : CycleGroup D sX 0) :
    chowGroupZeroDegree.{v} D sX hX sY hY hbase hp hpt hδ W (chowClass.{v} D sX hX 0 α) =
      ∑ᶠ Z : IntegralClosedSubspace D.site D.base D.base_mem X, α.1 Z *
        (cycleResidueDegree D sX hX sY hY p
          (Z.ambientGenericPoint D.site D.base D.base_mem) : ℤ) := by
  rw [chowGroupZeroDegree_chowClass, cycleDegree_eq_finsum D sX hX sY hY hbase hp hpt hδ W α]

end AlgebraicGeometry.Space

end
