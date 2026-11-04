module

public import StacksFrontier.AlgebraicGeometry.Duality.NormalizedDualizingDimensionFunction
public import
  StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.AssociatedShiftFunctionRestrict
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.NormalizedStalksOfClosedPoints
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekDualizingComplexOfCharts
public import StacksFrontier.AlgebraicGeometry.Scheme.FibreResidueField

/-!
# The dimension function of a relatively normalized dualizing complex

Let `S` be a Noetherian scheme with a dualizing complex `ω_S^•`, let `p : X ⟶ S` be of finite type
and let `ω_X^•` be normalized relative to `ω_S^•`: near every point of `X` there is an affine open
`U` with `ω_X^•|_U ≅ (U ⟶ S)^! ω_S^•`. Then the dimension functions of [Stacks, Tag 0AWF] satisfy

`δ_X(x) - δ_S(p x) = trdeg_{κ(p x)} κ(x)`

for every `x ∈ X`. This is [Stacks, Tag 0AWM].

The source reduces to `X` proper over `S` by a compactification. Here the argument stays on an
affine open `U ∋ x` with `ω_X^•|_U ≅ (U ⟶ S)^! ω_S^•`: both `δ_U` and
`y ↦ δ_S(p y) + trdeg_{κ(p y)} κ(y)` are dimension functions on `U` ([Stacks, Tag 0AWF] and
[Stacks, Tag 02JW]), so their difference is constant along specializations; every point of `U`
specializes to a closed point of `U`, where the transcendence degree vanishes
([Stacks, Tag 01TF]) and `δ_U = δ_S ∘ p` because on affine charts `(U ⟶ S)^! ω_S^•` is the
algebraic upper shriek of a model of `ω_S^•` ([Stacks, Tag 0BV2]), whose dimension function at a
maximal ideal is that of the model at the prime below. Finally `δ` and the transcendence degree
do not change under restriction to `U`.

## Main results

* `Stacks.Duality.associatedShiftFunction_sub_eq_trdeg_of_upperShriek` — [Stacks, Tag 0AWM].
* `Stacks.Duality.dimensionFunction_sub_eq_trdeg_of_eq_at_closedPoints` — its dimension-function
  form, from the identity at the closed points of `X`.

## References

* [Stacks Project, Tag 0AWM](https://stacks.math.columbia.edu/tag/0AWM)
* [Stacks Project, Tag 0AWF](https://stacks.math.columbia.edu/tag/0AWF)
* [Stacks Project, Tag 02JW](https://stacks.math.columbia.edu/tag/02JW)
* [Stacks Project, Tag 0BV2](https://stacks.math.columbia.edu/tag/0BV2)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Duality

open ChartCompactification _root_.Stacks.Duality.ProjectiveSpace
  _root_.AlgebraicGeometry.ProjectiveSpace Stacks.AlgebraicGeometry.ProjPolyChart

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **The dimension-function form of [Stacks, Tag 0AWM], from the closed points of `X`.** Let
`S` be a locally Noetherian universally catenary scheme, let `f : X ⟶ S` be locally of finite
type with `X` locally Noetherian, and let `δ_S` and `δ_X` be dimension functions on `S` and on
`X` with `δ_X(y) = δ_S(f y)` at every closed point `y` of `X`. Then for every `x ∈ X`

`δ_X(x) - δ_S(f x) = trdeg_{κ(f x)} κ(x)`:

every point specializes to a closed point, where the transcendence degree vanishes. -/
theorem dimensionFunction_sub_eq_trdeg_of_eq_at_closedPoints {X S : Scheme.{u}}
    [IsLocallyNoetherian S] [IsLocallyNoetherian X]
    (hS : Scheme.IsUniversallyCatenary S) (f : X ⟶ S) [LocallyOfFiniteType f]
    (δS : TopologicalSpace.DimensionFunction S) (δX : TopologicalSpace.DimensionFunction X)
    (hClosedPoint : ∀ y : X, IsClosed ({y} : Set X) → δX y = δS (f y))
    (x : X) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    δX x - δS (f x) =
      (Cardinal.toNat (Algebra.trdeg (S.residueField (f x)) (X.residueField x)) : ℤ) := by
  obtain ⟨d, hd⟩ := Stacks.Chow.relativeDimension_isDimensionFunction hS δS f
  obtain ⟨y, hy, hxy⟩ := AlgebraicGeometry.exists_specializes_closedPoint X x
  have hyc : IsClosed ({y} : Set X) := hy
  have hsub := δX.sub_eq_of_specializes d hxy
  have hdy : d y = δS (f y) := by
    rw [hd y]
    simp only [Stacks.Chow.relativeDimension]
    rw [trdeg_eq_zero_of_isClosed f y hyc]
    simp
  have hzero : δX y - d y = 0 := by
    rw [hdy, hClosedPoint y hyc]
    ring
  rw [hzero] at hsub
  rw [hd x] at hsub
  simp only [Stacks.Chow.relativeDimension] at hsub
  omega

/-- **[Stacks, Tag 0AWM] read as an equality of functions, from the closed points of `X`**: `δ_X`
is the relative dimension function `Stacks.Chow.relativeDimension δ_S f` of [Stacks, Tag 02JW].
Same hypotheses as `Stacks.Duality.dimensionFunction_sub_eq_trdeg_of_eq_at_closedPoints`. -/
theorem dimensionFunction_eq_relativeDimension_of_eq_at_closedPoints {X S : Scheme.{u}}
    [IsLocallyNoetherian S] [IsLocallyNoetherian X]
    (hS : Scheme.IsUniversallyCatenary S) (f : X ⟶ S) [LocallyOfFiniteType f]
    (δS : TopologicalSpace.DimensionFunction S) (δX : TopologicalSpace.DimensionFunction X)
    (hClosedPoint : ∀ y : X, IsClosed ({y} : Set X) → δX y = δS (f y))
    (x : X) : δX x = Stacks.Chow.relativeDimension δS f x := by
  have h := dimensionFunction_sub_eq_trdeg_of_eq_at_closedPoints hS f δS δX hClosedPoint x
  simp only [Stacks.Chow.relativeDimension]
  omega

/-- **Stacks Project, Tag 0AWM (Lemma 48.21.2).** Let `S` be a Noetherian scheme with a
dualizing complex `ω_S^•`, let `p : X ⟶ S` be of finite type, and let `ω_X^•` be normalized
relative to `ω_S^•`: every point has an affine open neighbourhood `U` with
`ω_X^•|_U ≅ (U ⟶ S)^! ω_S^•` for a compactification of `U` over `S`. Then for every `x ∈ X`,
`δ_X(x) - δ_S(p x) = trdeg_{κ(p x)} κ(x)`, where `δ_X`, `δ_S` are the dimension functions of
`ω_X^•`, `ω_S^•` ([Stacks, Tag 0AWF]). -/
@[stacks 0AWM]
theorem associatedShiftFunction_sub_eq_trdeg_of_upperShriek
    {S X : Scheme.{u}} [AlgebraicGeometry.IsNoetherian S] (p : X ⟶ S) [LocallyOfFiniteType p]
    (ωS : quasiCoherentDerivedCategory S) (hωS : IsDualizingComplex ωS.obj)
    (ωX : DerivedCategory X.Modules)
    (hωX : ∀ x : X, ∃ (U : X.Opens) (_ : IsAffine U.toScheme) (_ : x ∈ U)
      (j : CompactificationOf (Over.mk (ftsHomToBase (U.ι ≫ p)).left)),
      Nonempty ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj ωX ≅
        ((upperShriek (ftsHomToBase (U.ι ≫ p)) j).obj ωS).obj))
    (x : X) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
    letI := (p.residueFieldMap x).hom.toAlgebra
    associatedShiftFunction ωX x - associatedShiftFunction ωS.obj (p x) =
      (Cardinal.toNat (Algebra.trdeg (S.residueField (p x)) (X.residueField x)) : ℤ) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  obtain ⟨U, hUa, hxU, j, ⟨e⟩⟩ := hωX x
  let g := ftsHomToBase (U.ι ≫ p)
  let L := (upperShriek g j).obj ωS
  have hcharts : HasUpperShriekCharts (U.ι ≫ p) ωS.obj L.obj :=
    UpperShriekCharts.hasUpperShriekCharts g j
      (upperShriekCharts g j ωS (isBoundedBelow_of_isDualizingComplex _ hωS))
  have hLdual : IsDualizingComplex L.obj :=
    isDualizingComplex_of_isTildeModelOn_upperShriekFunctor (U.ι ≫ p) ωS.obj L.obj hcharts hωS
  let x' : U.toScheme := ⟨x, hxU⟩
  obtain ⟨-, -, dS, hdS⟩ :=
    isUniversallyCatenary_and_isDimensionFunction_associatedShiftFunction hωS
  obtain ⟨-, -, dL, hdL⟩ :=
    isUniversallyCatenary_and_isDimensionFunction_associatedShiftFunction hLdual
  have key := dimensionFunction_sub_eq_trdeg_of_eq_at_closedPoints
    (isUniversallyCatenary_of_isDualizingComplex hωS)
    (U.ι ≫ p) dS dL (fun y hy => (hdL y).trans
      ((associatedShiftFunction_eq_of_hasUpperShriekCharts (U.ι ≫ p) hωS hcharts hy).trans
        (hdS _).symm)) x'
  have hδ : dL x' = associatedShiftFunction ωX x :=
    (hdL x').trans ((congrFun (associatedShiftFunction_congr e) x').symm.trans
      (associatedShiftFunction_restrict_of_isOpenImmersion U.ι ωX x'))
  have htr := trdeg_residueField_comp_of_surjectiveOnStalks U.ι p x'
  rw [hδ, hdS] at key
  refine key.trans ?_
  exact congrArg (fun c => (Cardinal.toNat c : ℤ)) htr

end Stacks.Duality

end
