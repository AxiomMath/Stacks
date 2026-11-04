module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.AssociatedShiftFunction
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.UniversallyCatenary
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.ClosedPointResidueField
public import StacksFrontier.AlgebraicGeometry.Properties.NoetherianClosedPoints
public import StacksFrontier.Topology.Dimension.DimensionFunctionDifference

/-!
# The dimension function of a relatively normalized dualizing complex

Let `S` be a Noetherian scheme carrying a dualizing complex `ω_S^•`, let `f : X ⟶ S` be of
finite type and let `ω_X^•` be the dualizing complex normalized relative to `ω_S^•`. Writing
`δ_S` and `δ_X` for the dimension functions of `ω_S^•` and `ω_X^•` — these exist by
[Stacks, Tag 0AWF] — the content of [Stacks, Tag 0AWM] is the identity

`δ_X(x) - δ_S(f x) = trdeg_{κ(f x)} κ(x)`

at every point `x` of `X`.

## Main results

* `Stacks.Duality.trdeg_eq_zero_of_isClosed` — for `f` locally of finite type the residue field
  extension at a point closed in `X` is finite, so its transcendence degree vanishes.
* `Stacks.Duality.dimensionFunction_sub_eq_trdeg` — **[Stacks, Tag 0AWM]**, the identity above.
* `Stacks.Duality.dimensionFunction_eq_relativeDimension` — the same identity read as
  `δ_X = relativeDimension δ_S f`, the function of [Stacks, Tag 02JW].

## Implementation notes

*What the proof is.* Both `δ_X` and `x ↦ δ_S(f x) + trdeg_{κ(f x)} κ(x)` are dimension
functions on `X`: the first by hypothesis, the second by [Stacks, Tag 02JW]
(`Stacks.Chow.relativeDimension_isDimensionFunction`), whose input — universal catenarity of
`S` — is supplied for a scheme with a dualizing complex by [Stacks, Tag 0AWF]
(`Stacks.Duality.isUniversallyCatenary_of_isDualizingComplex`). The difference of two dimension
functions is constant along specializations
(`TopologicalSpace.DimensionFunction.sub_eq_of_specializes`, the local-constancy of
[Stacks, Tag 02IB] in the form actually used), every point of a locally Noetherian scheme
specializes to a closed point ([Stacks, Tag 02IL],
`AlgebraicGeometry.exists_specializes_closedPoint`), and at a closed point the transcendence
degree vanishes by [Stacks, Tag 01TF]. So it is enough to know the identity at closed points,
where it reads `δ_X(x) = δ_S(f x)`.

Note that this route does not need the source's reduction to a connected `X`: rather than
arguing that the difference is locally constant hence globally constant and evaluating it once,
each point is compared with a closed point it specializes to.

*What is carried, and why.* Two inputs of the source are explicit hypotheses rather than
conclusions.

* `hClosedImage` — that `f` carries closed points of `X` to closed points of `S`. The source
  obtains this by replacing `X` by a compactification over `S` ([Stacks, Tag 0F41]) and so
  reducing to `f` proper; that reduction rests on Nagata compactification and on the invariance
  of `ω_X^•` under restriction to an open ([Stacks, Tag 0AUC]), neither of which is available
  here. For a proper `f` the hypothesis is just `Scheme.Hom.isClosedMap`.
* `hClosedPoint` — the identity at a closed point `x` whose image is closed. This is
  [Stacks, Tag 0AWL], proved in this repository as
  `Stacks.Duality.isNormalizedDualizingComplex_derivedStalkOfComplex_normalizedDualizingComplex`;
  converting that statement about normalized dualizing complexes on stalks into the equation
  `δ_X(x) = δ_S(f x)` needs the function `δ` of [Stacks, Tag 0AWF] to be tied to the complex
  *through its derived stalk*. Both halves of 0AWF are proved — universal catenarity as
  `Stacks.Duality.isUniversallyCatenary_of_isDualizingComplex` and the construction of `δ` as
  `Stacks.Duality.exists_isDualizingShiftFunction` — but the `δ` that construction produces is
  tied to `ω^•` through the *dualizing models over affine opens*, not through the derived stalk,
  and `Stacks.Duality.isNormalizedDualizingComplex_derivedStalkOfComplex_normalizedDualizingComplex`
  speaks of the derived stalk; identifying the two readings is the stalk-versus-localization
  dictionary, which this repository does not carry. The two dimension functions are therefore
  parameters, and `hClosedPoint` is the only thing relating them.

Neither hypothesis makes the statement vacuous: `hClosedPoint` says nothing at a non-closed
point, and the conclusion at a non-closed point — where the transcendence degree is in general
nonzero — is exactly what the dimension-function argument supplies.

## References

* [Stacks Project, Tag 0AWM](https://stacks.math.columbia.edu/tag/0AWM)
* [Stacks Project, Tag 0AWF](https://stacks.math.columbia.edu/tag/0AWF)
* [Stacks Project, Tag 0AWL](https://stacks.math.columbia.edu/tag/0AWL)
* [Stacks Project, Tag 02JW](https://stacks.math.columbia.edu/tag/02JW)
* [Stacks Project, Tag 02IB](https://stacks.math.columbia.edu/tag/02IB)
* [Stacks Project, Tag 02IL](https://stacks.math.columbia.edu/tag/02IL)
* [Stacks Project, Tag 01TF](https://stacks.math.columbia.edu/tag/01TF)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Duality

/-- **The transcendence degree vanishes at a closed point.** For `f : X ⟶ S` locally of finite
type and `x` closed in `X`, the residue field `κ(x)` is finite over `κ(f x)` — this is
`AlgebraicGeometry.finite_residueField_of_isClosed`, the closed-point case of
[Stacks, Tag 01TF] — so the extension has transcendence degree zero. -/
theorem trdeg_eq_zero_of_isClosed {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (x : X) (hx : IsClosed ({x} : Set X)) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    Algebra.trdeg (S.residueField (f x)) (X.residueField x) = 0 := by
  let := (f.residueFieldMap x).hom.toAlgebra
  let := AlgebraicGeometry.finite_residueField_of_isClosed f hx
  exact trdeg_eq_zero

/-- **The dimension-function form of [Stacks, Tag 0AWM].** Let `S` be a locally Noetherian
universally catenary scheme — which a Noetherian scheme carrying a dualizing complex is, by
[Stacks, Tag 0AWF] — let `f : X ⟶ S` be locally of finite type with `X` locally Noetherian, and
let `δ_S` and `δ_X` be dimension functions on `S` and on `X`. Then for every `x ∈ X`

`δ_X(x) - δ_S(f x) = trdeg_{κ(f x)} κ(x)`.

Two inputs are carried as hypotheses: `hClosedImage`, that `f` sends closed points to closed
points, which the source arranges by passing to a compactification, and `hClosedPoint`, the
identity at such a closed point, which is [Stacks, Tag 0AWL]. See the module documentation.

`Stacks.Duality.associatedShiftFunction_sub_eq_trdeg` is the specialization to the two
dimension functions of the source, those attached to `ω_S^•` and `ω_X^•`; it is the statement
that carries the tag. -/
theorem dimensionFunction_sub_eq_trdeg {X S : Scheme.{u}}
    [IsLocallyNoetherian S] [IsLocallyNoetherian X]
    (hS : Scheme.IsUniversallyCatenary S) (f : X ⟶ S) [LocallyOfFiniteType f]
    (δS : DimensionFunction S) (δX : DimensionFunction X)
    (hClosedImage : ∀ y : X, IsClosed ({y} : Set X) → IsClosed ({f y} : Set S))
    (hClosedPoint : ∀ y : X, IsClosed ({y} : Set X) → IsClosed ({f y} : Set S) →
      δX y = δS (f y))
    (x : X) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    δX x - δS (f x) =
      (Cardinal.toNat (Algebra.trdeg (S.residueField (f x)) (X.residueField x)) : ℤ) := by
  obtain ⟨d, hd⟩ := Stacks.Chow.relativeDimension_isDimensionFunction hS δS f
  obtain ⟨y, hy, hxy⟩ := AlgebraicGeometry.exists_specializes_closedPoint X x
  have hyc : IsClosed ({y} : Set X) := hy
  -- the difference of the two dimension functions is the same at `x` and at `y`
  have hsub := δX.sub_eq_of_specializes d hxy
  -- at the closed point `y` the difference vanishes
  have hdy : d y = δS (f y) := by
    rw [hd y]
    simp only [Stacks.Chow.relativeDimension]
    rw [trdeg_eq_zero_of_isClosed f y hyc]
    simp
  have hzero : δX y - d y = 0 := by
    rw [hdy, hClosedPoint y hyc (hClosedImage y hyc)]
    ring
  rw [hzero] at hsub
  rw [hd x] at hsub
  simp only [Stacks.Chow.relativeDimension] at hsub
  omega

/-- **[Stacks, Tag 0AWM] read as an equality of functions**: `δ_X` is the relative dimension
function `Stacks.Chow.relativeDimension δ_S f` of [Stacks, Tag 02JW], which at `x` is
`δ_S(f x) + trdeg_{κ(f x)} κ(x)`. Same hypotheses as
`Stacks.Duality.dimensionFunction_sub_eq_trdeg`, of which this is a restatement. -/
theorem dimensionFunction_eq_relativeDimension {X S : Scheme.{u}}
    [IsLocallyNoetherian S] [IsLocallyNoetherian X]
    (hS : Scheme.IsUniversallyCatenary S) (f : X ⟶ S) [LocallyOfFiniteType f]
    (δS : DimensionFunction S) (δX : DimensionFunction X)
    (hClosedImage : ∀ y : X, IsClosed ({y} : Set X) → IsClosed ({f y} : Set S))
    (hClosedPoint : ∀ y : X, IsClosed ({y} : Set X) → IsClosed ({f y} : Set S) →
      δX y = δS (f y))
    (x : X) : δX x = Stacks.Chow.relativeDimension δS f x := by
  have h := dimensionFunction_sub_eq_trdeg hS f δS δX hClosedImage hClosedPoint x
  simp only [Stacks.Chow.relativeDimension]
  omega

/-- **Stacks Project, Tag 0AWM.** Let `S` be a Noetherian scheme and let `ω_S^•` be a dualizing
complex. Let `f : X ⟶ S` be of finite type and let `ω_X^•` be the dualizing complex normalized
relative to `ω_S^•`. For all `x ∈ X`

`δ_X(x) - δ_S(f x) = trdeg_{κ(f x)} κ(x)`

where `δ_S`, resp. `δ_X`, is the dimension function of `ω_S^•`, resp. `ω_X^•`, of
[Stacks, Tag 0AWF] — here `Stacks.Duality.associatedShiftFunction`.

Universal catenarity of `S`, which [Stacks, Tag 02JW] needs, is *derived* from `hωS` by
[Stacks, Tag 0AWF] (`Stacks.Duality.isUniversallyCatenary_of_isDualizingComplex`). What is
carried are the three things this repository does not have:

* `δS`, `δX` with `hδS`, `hδX` — that the shift functions *are* dimension functions. This is
  the companion half of [Stacks, Tag 0AWF], which
  `StacksFrontier/AlgebraicGeometry/Duality/RelativeDualizing/AssociatedShiftFunction.lean` states
  explicitly that it does not prove; only the universally-catenary half is proved.
* `hClosedImage` — that `f` carries closed points to closed points, the source's reduction to a
  proper `f`.
* `hClosedPoint` — the identity at a closed point over a closed point, [Stacks, Tag 0AWL],
  proved as
  `Stacks.Duality.isNormalizedDualizingComplex_derivedStalkOfComplex_normalizedDualizingComplex`;
  what is missing is the bridge from that statement about normalized stalks to a value of
  `Stacks.Duality.associatedShiftFunction`.

The relation between `ω_X^•` and `ω_S^•` enters only through `hClosedPoint`, which is exactly
where the source uses it; the complex `ω_X^•` is otherwise a parameter. -/
@[stacks 0AWM "RESTRICTED: three inputs are explicit hypotheses. That the shift functions of the
two dualizing complexes are dimension functions is the unproved half of Tag 0AWF, carried as
dimension functions delta_S and delta_X together with hdS and hdX. That f carries closed points
to closed points -- the source's reduction to a proper f, through Nagata compactification and
Tag 0AUC -- is hClosedImage. The identity at a closed point over a closed point, Tag 0AWL, is
hClosedPoint; 0AWL itself is proved, but the bridge from normalized stalks to a value of
associatedShiftFunction is not. What is proved is the body of the lemma: universal catenarity
of S from Tag 0AWF, then that the difference of the two functions is determined by its values at
closed points, by Tag 02JW and Tag 02IB and Tag 02IL, and that the transcendence degree vanishes
at a closed point, by Tag 01TF"]
theorem associatedShiftFunction_sub_eq_trdeg {X S : Scheme.{u}}
    [IsLocallyNoetherian S] [IsLocallyNoetherian X]
    [HasDerivedCategory S.Modules] [HasDerivedCategory X.Modules]
    (f : X ⟶ S) [LocallyOfFiniteType f]
    {ωS : DerivedCategory S.Modules} (hωS : IsDualizingComplex ωS)
    (ωX : DerivedCategory X.Modules)
    (δS : DimensionFunction S) (hδS : ∀ s : S, δS s = associatedShiftFunction ωS s)
    (δX : DimensionFunction X) (hδX : ∀ y : X, δX y = associatedShiftFunction ωX y)
    (hClosedImage : ∀ y : X, IsClosed ({y} : Set X) → IsClosed ({f y} : Set S))
    (hClosedPoint : ∀ y : X, IsClosed ({y} : Set X) → IsClosed ({f y} : Set S) →
      associatedShiftFunction ωX y = associatedShiftFunction ωS (f y))
    (x : X) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    associatedShiftFunction ωX x - associatedShiftFunction ωS (f x) =
      (Cardinal.toNat (Algebra.trdeg (S.residueField (f x)) (X.residueField x)) : ℤ) := by
  have h := dimensionFunction_sub_eq_trdeg
    (isUniversallyCatenary_of_isDualizingComplex hωS) f δS δX hClosedImage
    (fun y hy hfy => by rw [hδX y, hδS (f y)]; exact hClosedPoint y hy hfy) x
  rw [hδX x, hδS (f x)] at h
  exact h

end Stacks.Duality

end
