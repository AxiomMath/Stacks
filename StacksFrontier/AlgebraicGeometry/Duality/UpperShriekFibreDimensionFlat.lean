module

public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekBounded
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekFibreDimension
public import StacksFrontier.AlgebraicGeometry.Flatness.FiniteOverSmooth
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.FibreDimensionBoundUpper

/-!
# The relative dualizing complex of a flat morphism is concentrated in `[-dim, 0]`

Let `S` be a Noetherian scheme and let `f : X ⟶ Y` be a **flat** morphism of
`AlgebraicGeometry.FTS S`, the category of schemes separated and of finite type over `S` of
[Stacks, Tag 0F42]. Let `x ∈ X` with image `y ∈ Y`. This file proves the stalk assertion of
[Stacks, Tag 0BV6] (Lemma 48.21.2):

  `H^i(f^!𝒪_Y)_x ≠ 0  ⟹  -dim_x(X_y) ≤ i ≤ 0`,

where `f^!` is `Stacks.Duality.upperShriek`, `𝒪_Y` is
`Stacks.Duality.DerivedPushforward.derivedStructureSheaf` and `dim_x(X_y)` is the local
dimension of the scheme-theoretic fibre of `f` through `x`, at `x`. It also proves the
cohomological concentration that goes with it: if every fibre of `f` has dimension at most
`d`, then the cohomology *sheaf* `H^i(f^!𝒪_Y)` is zero for every `i` outside `[-d, 0]`.

This sharpens [Stacks, Tag 0BV5],
`Stacks.Duality.neg_fibreDim_le_of_nontrivial_stalk_homology_upperShriek`, which has the lower
bound `-dim_x(X_y) ≤ i` with no flatness hypothesis.

## Main results

* `Stacks.Duality.fibreDim_bounds_of_nontrivial_stalk_homology_upperShriek_of_flat` — the
  **stalk assertion of [Stacks, Tag 0BV6]**: the two-sided bound `-dim_x(X_y) ≤ i ≤ 0`.
* `Stacks.Duality.isZero_homology_upperShriek_derivedStructureSheaf_of_notMem_Icc` — the
  cohomological concentration of `f^!𝒪_Y` in `[-d, 0]` under a bound `d` on every fibre
  dimension. This is the `𝒪_Y`-instance of the Tor-amplitude assertion of
  [Stacks, Tag 0BV6]; see below for why the Tor-amplitude assertion itself is not claimed.

## Implementation notes

*The source's proof.* It reads: the statement is local on `X`, so one may assume `X = Spec(A)`
and `Y = Spec(R)` affine; then `f^!𝒪_Y` is the relative dualizing complex `ω^•_{A/R}` of
[Stacks, Tag 0E9M] by Remark [Stacks, Tag 0BV2]; and the assertion is [Stacks, Tag 0E9Q].

*What is carried.* One hypothesis is carried, `h0BV2`, in exactly the shape that
[Stacks, Tag 0BV5] and part (a) of [Stacks, Tag 0B6U] carry it: on an affine open `U ∋ x` of
`X` inside the preimage of an affine open `V` of `Y`, the restriction of `f^!𝒪_Y` to `U` is the
associated sheaf of the *algebraic* upper shriek, along a polynomial presentation of the chart
ring map `f.appLE V U`, of `Γ(Y, V)` placed in degree zero. That is clause (b) of the source's
Remark [Stacks, Tag 0BV2], the affine formula, which is unavailable here: the repository's
Tag 0BV2, `Stacks.Duality.restrictedUpperShriekIsoOfOpenSquare`, proves only clause (a),
because [Stacks, Tag 0AA1] — `f^! ≅ Lf^*[1]` for `𝔸¹_V ⟶ V` — is absent. The hypothesis names
one isomorphism of complexes and asserts nothing about any degree.

Flatness of `f` is **not** carried: the chart-level `Module.Flat Γ(Y, V) Γ(X, U)` that the
ring-level bounds consume is discharged from the instance `[Flat f.left]` through
`AlgebraicGeometry.Flat.flat_appLE`.

*The ring-level bounds of [Stacks, Tag 0E9Q] are imported.* The chart input is the two-sided
bound `-d ≤ i ≤ 0` for the algebraic upper shriek of a flat finite type homomorphism of
Noetherian rings, together with the concentration statement under a uniform bound on the fibre
dimensions. Those are the ring-level statements of Tag 0E9Q, and they are
`Dualizing.upperShriekFunctor_relativeDimensionAt_bounds_of_nontrivial_localizedHomology` and
`Dualizing.isZero_homology_upperShriekFunctor_unit_of_notMem_Icc` of
`StacksFrontier.RingTheory.Dualizing.UpperShriek.FibreDimensionBoundUpper`.

*The Tor-amplitude assertion of Tag 0BV6 is NOT claimed.* The source adds: if all fibres of `f`
have dimension at most `d` then `f^!𝒪_Y` has Tor-amplitude in `[-d, 0]` as an object of
`D(X, f^{-1}𝒪_Y)`. That statement is expressible in this repository —
`Stacks.Cohomology.TorAmplitude.HasTorAmplitude` on the ringed space
`AlgebraicGeometry.RingedSpace.inverseImage Y.left.toRingedSpace f.left.base`, applied to
`AlgebraicGeometry.Scheme.Hom.derivedScalarRestriction f.left` of `f^!𝒪_Y` — but it is not
provable from what the library has. The missing input is the affine-locality assembly that
passes from a chart to the sheaf-level Tor-amplitude predicate over the inverse-image structure
sheaf, whose absence is already recorded in
`StacksFrontier.AlgebraicGeometry.Duality.UpperShriekRelativePerfection`. What is proved below
instead is the `𝒪_Y`-instance of that assertion, which is the degreewise vanishing of the
cohomology sheaves outside `[-d, 0]`.

The *ring-level* Tor-amplitude clause of Tag 0E9Q — Tor amplitude of `ω^•_{A/R}` over `R`, not
merely cohomological concentration — is not missing. It is
`Dualizing.upperShriekFunctor_hasTorAmplitude_of_fiber_dimension_le` of
`StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingTorAmplitude`.

*The two derived categories.* `Stacks.Duality.upperShriek` lives on
`Stacks.Duality.quasiCoherentDerivedCategory`, read at the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, while the derived category of a chart ring
is read at `CategoryTheory.HasDerivedCategory.standard`. As in
`StacksFrontier.AlgebraicGeometry.Duality.UpperShriekBounded`, the two are never compared: the
derived universes keep them apart and the only traffic between them is through `h0BV2` and the
sheafification functor `AlgebraicGeometry.tilde.functor`.

## References

* [Stacks Project, Tag 0BV6](https://stacks.math.columbia.edu/tag/0BV6)
* [Stacks Project, Tag 0BV5](https://stacks.math.columbia.edu/tag/0BV5)
* [Stacks Project, Tag 0E9Q](https://stacks.math.columbia.edu/tag/0E9Q)
* [Stacks Project, Tag 0E9P](https://stacks.math.columbia.edu/tag/0E9P)
* [Stacks Project, Tag 0E9M](https://stacks.math.columbia.edu/tag/0E9M)
* [Stacks Project, Tag 0BV2](https://stacks.math.columbia.edu/tag/0BV2)
* [Stacks Project, Tag 0AA1](https://stacks.math.columbia.edu/tag/0AA1)
* [Stacks Project, Tag 0B6U](https://stacks.math.columbia.edu/tag/0B6U)
* [Stacks Project, Tag 0F42](https://stacks.math.columbia.edu/tag/0F42)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

universe u

/-! ## Tag 0BV6 for a flat morphism of `FTS S` -/

section Geometric

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Duality

attribute [local instance 5000] HasDerivedCategory.standard
attribute [local instance 10000] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

namespace Stacks.Duality

open DerivedPushforward

/-! ### Tag 0BV6 -/

section Shriek

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : AlgebraicGeometry.FTS S} (f : X ⟶ Y)
  (j : AlgebraicGeometry.CompactificationOf (Over.mk f.left))

/-- Every prime of the ring of sections of an affine open is the prime of a point of it. -/
private theorem exists_mem_primeIdealOf_eq {Z : Scheme.{u}} {U : Z.Opens}
    (hU : IsAffineOpen U) (q : PrimeSpectrum Γ(Z, U)) :
    ∃ (z : Z) (hz : z ∈ U), hU.primeIdealOf ⟨z, hz⟩ = q := by
  have hoi : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  have hz : hU.fromSpec q ∈ U := hU.range_fromSpec.le ⟨q, rfl⟩
  refine ⟨hU.fromSpec q, hz, hU.fromSpec.isOpenEmbedding.injective ?_⟩
  exact hU.fromSpec_primeIdealOf ⟨hU.fromSpec q, hz⟩

/-- The source scheme of an object of `FTS S` is locally Noetherian. -/
private theorem isLocallyNoetherian_left (Z : AlgebraicGeometry.FTS S) :
    IsLocallyNoetherian Z.left := by
  have : IsLocallyNoetherian ((Functor.fromPUnit S).obj Z.right) :=
    inferInstanceAs (IsLocallyNoetherian S)
  exact LocallyOfFiniteType.isLocallyNoetherian Z.hom

omit [AlgebraicGeometry.IsNoetherian S] in
/-- The chart ring map of a flat morphism is flat. -/
private theorem flat_chart (hflat : Flat f.left) {U : X.left.Opens} (hU : IsAffineOpen U)
    {V : Y.left.Opens} (hV : IsAffineOpen V) (hUV : U ≤ f.left ⁻¹ᵁ V) :
    letI := (f.left.appLE V U hUV).hom.toAlgebra
    Module.Flat Γ(Y.left, V) Γ(X.left, U) :=
  f.left.flat_appLE hV hU hUV

/-- **Stacks Project, Tag 0BV6 (Lemma 48.21.2), the stalk assertion.** In Situation 48.16.1, let
`f : X ⟶ Y` be a **flat** morphism of `FTS S` and let `x ∈ X` with image `y ∈ Y`. Then

  `H^i(f^!𝒪_Y)_x ≠ 0  ⟹  -dim_x(X_y) ≤ i ≤ 0`,

the local dimension `dim_x(X_y)` of the scheme-theoretic fibre being named by the hypothesis
`hd` that identifies it with a natural number `d`.

The affine identification of `f^!𝒪_Y` of Remark [Stacks, Tag 0BV2] is the carried hypothesis
`h0BV2`; it names an isomorphism on an affine chart through `x` and asserts nothing about any
degree. Both halves of the bound are proved: the lower one is [Stacks, Tag 0E9P] and
the upper one the ring-level Tag 0E9Q,
`Dualizing.upperShriekFunctor_relativeDimensionAt_bounds_of_nontrivial_localizedHomology`, moved
to the chart by the stalk dictionary
`Stacks.Duality.nontrivial_stalk_homology_iff_nontrivial_localizedHomology` and the
fibre-dimension dictionary `Stacks.Flatness.topologicalKrullDimAt_fiber_eq_relativeDimensionAt`.
Flatness is used only through the chart-level flatness of `f.appLE V U`.

This is the flat sharpening of [Stacks, Tag 0BV5],
`Stacks.Duality.neg_fibreDim_le_of_nontrivial_stalk_homology_upperShriek`, which proves the
lower bound alone and for an arbitrary morphism of `FTS S`. The Tor-amplitude assertion of
Tag 0BV6 is not claimed; see the module documentation. -/
-- The Stacks 0BV6 attribute is not placed on this declaration: the binder `h0BV2` is clause (b)
-- of Stacks 0BV2, an assumed prerequisite tag, so this declaration cannot carry the tag while
-- that hypothesis is assumed. The tag is registered instead via `add_to_stacks` at the end of
-- this file, recording what is proved and what is assumed.
-- The root prerequisite is Stacks 0AA1 (f^! = Lf^*[1] for A^1_V -> V), which is not available
-- here, so the result is stated with that hypothesis explicit.
theorem fibreDim_bounds_of_nontrivial_stalk_homology_upperShriek_of_flat
    [Flat f.left] (x : X.left)
    (h0BV2 : ∃ (U : X.left.Opens) (hU : IsAffineOpen U) (V : Y.left.Opens)
      (_hV : IsAffineOpen V) (hUV : U ≤ f.left ⁻¹ᵁ V), x ∈ U ∧
      ∃ p : Dualizing.PolynomialPresentation (f.left.appLE V U hUV).hom,
        Nonempty ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj
            (((upperShriek f j).obj (derivedStructureSheaf Y.left)).obj) ≅
          (tilde.functor Γ(X.left, U) ⋙
            Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj
              (p.upperShriekFunctor.{u, u}.obj (structureModel (Y := Y) V))))
    (d : ℕ)
    (hd : topologicalKrullDimAt (f.left.fiber (f.left x)) (f.left.asFiber x) =
      (d : WithBot ℕ∞))
    (i : ℤ)
    (hi : Nontrivial (((DerivedCategory.homologyFunctor X.left.Modules i).obj
      (((upperShriek f j).obj
        (derivedStructureSheaf Y.left)).obj)).presheaf.stalk x)) :
    -(d : ℤ) ≤ i ∧ i ≤ 0 := by
  obtain ⟨U, hU, V, hV, hUV, hxU, p, he⟩ := h0BV2
  have hYn := isLocallyNoetherian_left Y
  have hXn := isLocallyNoetherian_left X
  have hVn : IsNoetherianRing Γ(Y.left, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have hUn : IsNoetherianRing Γ(X.left, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let _ : Algebra Γ(Y.left, V) Γ(X.left, U) := (f.left.appLE V U hUV).hom.toAlgebra
  have hfl : Module.Flat Γ(Y.left, V) Γ(X.left, U) := flat_chart f ‹Flat f.left› hU hV hUV
  -- The prime of the chart ring corresponding to `x`.
  let q : PrimeSpectrum Γ(X.left, U) := hU.primeIdealOf ⟨x, hxU⟩
  -- The fibre-dimension dictionary.
  have hdq : Algebra.relativeDimensionAt Γ(Y.left, V) q.asIdeal = (d : WithBot ℕ∞) :=
    (Stacks.Flatness.topologicalKrullDimAt_fiber_eq_relativeDimensionAt
      f.left ⟨V, hV⟩ ⟨U, hU⟩ hUV x hxU).symm.trans hd
  -- The stalk dictionary.
  have hloc := (nontrivial_stalk_homology_iff_nontrivial_localizedHomology hU he.some
    (⟨x, hxU⟩ : U.toScheme) q rfl i).mp hi
  -- The ring-level Tag 0E9Q on the chart.
  exact Dualizing.upperShriekFunctor_relativeDimensionAt_bounds_of_nontrivial_localizedHomology
    p q d hdq i hloc

/-- **The cohomological concentration of `f^!𝒪_Y` in `[-d, 0]`.** In Situation 48.16.1, let
`f : X ⟶ Y` be a **flat** morphism of `FTS S` all of whose fibres have dimension at most `d`.
Then the cohomology sheaf `H^i(f^!𝒪_Y)` is zero for every `i` outside `[-d, 0]`.

This is the `𝒪_Y`-instance of the Tor-amplitude assertion of [Stacks, Tag 0BV6], that assertion
itself not being claimed here; see the module documentation. It is strictly stronger than the
stalk assertion above read at every point, which only says that the stalks are not nontrivial.

The carried hypothesis `h0BV2` is the one of part (a) of [Stacks, Tag 0B6U], quantified over
every point of `X`; vanishing of a sheaf of modules is local, so the charts it provides suffice
with no quasi-compactness. -/
theorem isZero_homology_upperShriek_derivedStructureSheaf_of_notMem_Icc
    [Flat f.left]
    (h0BV2 : ∀ x : X.left, ∃ (U : X.left.Opens) (hU : IsAffineOpen U) (V : Y.left.Opens)
      (_hV : IsAffineOpen V) (hUV : U ≤ f.left ⁻¹ᵁ V), x ∈ U ∧
      ∃ p : Dualizing.PolynomialPresentation (f.left.appLE V U hUV).hom,
        Nonempty ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj
            (((upperShriek f j).obj (derivedStructureSheaf Y.left)).obj) ≅
          (tilde.functor Γ(X.left, U) ⋙
            Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj
              (p.upperShriekFunctor.{u, u}.obj (structureModel (Y := Y) V))))
    (d : ℕ)
    (hd : ∀ z : X.left, topologicalKrullDimAt (f.left.fiber (f.left z)) (f.left.asFiber z) ≤
      (d : WithBot ℕ∞))
    (i : ℤ) (hi : i ∉ Set.Icc (-(d : ℤ)) 0) :
    IsZero ((DerivedCategory.homologyFunctor X.left.Modules i).obj
      (((upperShriek f j).obj (derivedStructureSheaf Y.left)).obj)) := by
  have hYn := isLocallyNoetherian_left Y
  have hXn := isLocallyNoetherian_left X
  choose U hU V hV hUV hxU p he using h0BV2
  have hcov : ⨆ z : X.left, U z = ⊤ := by
    refine SetLike.ext fun y => ⟨fun _ => trivial, fun _ => ?_⟩
    simpa only [Opens.mem_iSup] using ⟨y, hxU y⟩
  refine Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_of_isZero_restrict_cover
    U hcov _ fun z => ?_
  have hVn : IsNoetherianRing Γ(Y.left, V z) :=
    IsLocallyNoetherian.component_noetherian ⟨V z, hV z⟩
  have hUn : IsNoetherianRing Γ(X.left, U z) :=
    IsLocallyNoetherian.component_noetherian ⟨U z, hU z⟩
  let _ : Algebra Γ(Y.left, V z) Γ(X.left, U z) := (f.left.appLE (V z) (U z) (hUV z)).hom.toAlgebra
  have hfl : Module.Flat Γ(Y.left, V z) Γ(X.left, U z) :=
    flat_chart f ‹Flat f.left› (hU z) (hV z) (hUV z)
  have hdq : ∀ r : PrimeSpectrum Γ(X.left, U z),
      Algebra.relativeDimensionAt Γ(Y.left, V z) r.asIdeal ≤ (d : WithBot ℕ∞) := by
    intro r
    obtain ⟨w, hw, rfl⟩ := exists_mem_primeIdealOf_eq (hU z) r
    exact (Stacks.Flatness.topologicalKrullDimAt_fiber_eq_relativeDimensionAt
      f.left ⟨V z, hV z⟩ ⟨U z, hU z⟩ (hUV z) w hw).symm.trans_le (hd w)
  exact isZero_restrict_homology_of_tildeModel i
    (Dualizing.isZero_homology_upperShriekFunctor_unit_of_notMem_Icc (p z) d hdq i hi) (he z)

end Shriek

end Stacks.Duality

end Geometric

/-! ### Registration against Stacks 0BV6

Stacks 0BV6 is **not** proved unconditionally.  The first assertion is proved in full, but under
an assumed prerequisite tag; the tor-amplitude assertion is not proved at all.
-/

add_to_stacks 0BV6 "THE FIRST ASSERTION, both halves, BUT UNDER AN ASSUMED PREREQUISITE TAG, and
NOT the tor-amplitude assertion. Proved: for f flat and x over y, if the stalk at x of
H^i(f^! O_Y) is nontrivial then -dim_x(X_y) <= i <= 0, with no affineness on X or Y and flatness
an instance. ASSUMED: h0BV2, the affine-chart description of f^! O_Y, which is clause (b) of
Stacks 0BV2 and rests on Stacks 0AA1 (f^! = Lf^*[1] for A^1_V -> V). Tag 0AA1 is not proved in
this library; this result becomes unconditional by composing with a proof of it. Note the
same hypothesis is carried in the identical shape by the
statements of Tags 0BV5 and 0B6U and by Duality/UpperShriekBounded.lean, so discharging 0AA1
unconditionalises those too. NOT PROVED: f^! O_Y has tor-amplitude in [-d,0] in
D(X, f-inverse O_Y). Only its O_Y instance is proved, the vanishing of the cohomology SHEAVES
outside [-d,0], as isZero_homology_upperShriek_derivedStructureSheaf_of_notMem_Icc below; the
ring-level version at base is itself conditional on Tag 0BZV and the chart-to-sheaf assembly is
absent."
  Stacks.Duality.fibreDim_bounds_of_nontrivial_stalk_homology_upperShriek_of_flat

end
