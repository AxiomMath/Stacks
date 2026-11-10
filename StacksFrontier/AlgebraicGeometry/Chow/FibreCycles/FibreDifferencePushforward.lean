module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant42.FlatPullbackComponent
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.FibreDivisorPrincipal
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullbackCycles.SchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisor.ZeroIdeal
public import StacksFrontier.AlgebraicGeometry.Divisors.SplitClosedImmersionIdeal

/-!
# Part (2) of Stacks 02S4 when the family dominates a subscheme of its own dimension

Stacks Tag 02S4 part (2) says that for an integral closed subscheme `W ⊆ X ×_S ℙ¹_S` of
delta-dimension `k + 1` contained in neither distinguished section, the cycles of the two fibres
`W₀` and `W_∞`, viewed as closed subschemes of `X`, are rationally equivalent on `X`. The source
proves it in three steps: the difference of the two fibre cycles *on `W`* is the principal
divisor of the chart coordinate, which is
`Stacks.Chow.principalDivisorCycle_eq_sub_fibreDivisorCycles`; the proper pushforward along
`p : W ⟶ X` carries each fibre cycle on `W` to the corresponding fibre cycle on `X`; and proper
pushforward preserves rational equivalence, which is Stacks 02S2.

This file does the second step outright and the third step **in the case Stacks 02S2 does not
need Stacks 02RU** — namely when the scheme-theoretic image of `W` in `X` still has
delta-dimension `k + 1`, equivalently when `p` is generically finite. There the pushforward of a
principal divisor is the principal divisor of the norm along the finite extension of function
fields, which is Stacks 02RT, and nothing else is required. The remaining case, in
which the image drops delta-dimension and the generic fibre of `p` is a curve, is exactly where
Stacks 02S2 invokes Stacks 02RU over the function field of the image; it is a hypothesis of
`Stacks.Chow.fibreCyclesRationallyEquivalentWithin_of_fibreDifference_eq_zero_of_dimension_drop`,
whose other hypothesis-free half is the content of this file.

## Main definitions

* `Stacks.Chow.fibreBaseProjection` — the first projection `W ⟶ X` of a closed subscheme of
  `X ×_S ℙ¹_S`; it is proper.
* `Stacks.Chow.fibrePrincipalDivisorCycle` — the principal divisor of the chart coordinate on an
  integral `W` of delta-dimension `k + 1`, as a `k`-cycle on `W`.

## Main results

* `Stacks.Chow.cycleAssociatedToClosedSubscheme_ker` — the cycle of a closed immersion is the
  cycle of the closed subscheme it cuts out, since a closed immersion factors through its
  scheme-theoretic image by an isomorphism.
* `Stacks.Chow.ker_zeroDivisor_subschemeι_comp` and
  `Stacks.Chow.ker_infinityDivisor_subschemeι_comp` — the image in `X` of the zero, resp.
  infinity, divisor of `W` is the zero, resp. infinity, fibre of `W`.
* `Stacks.Chow.properPushforward_cycleAssociatedToClosedSubscheme_zeroDivisor` and its infinity
  twin — proper pushforward along `W ⟶ X` carries the cycle of a fibre on `W` to the cycle of the
  corresponding fibre on `X`.
* `Stacks.Chow.fibreDifference_eq_properPushforward` — the fibre difference of `W` on `X` is the
  proper pushforward of a principal divisor on `W`.
* `Stacks.Chow.isRationallyEquivalentToZeroWithin_properPushforward_principalCycle` — the
  Stacks 02RT branch of Stacks 02S2 for a single principal divisor on an integral scheme, with
  the carrier of the resulting rational equivalence retained.
* `Stacks.Chow.schemeDeltaDimension_ker_fibreBaseProjection` — the delta-dimension of the
  scheme-theoretic image of `W` in `X` is the relative dimension of `X` at the image of the
  generic point of `W`, so the hypothesis below is a condition at one point.
* `Stacks.Chow.fibreCyclesRationallyEquivalentWithin_of_schemeDeltaDimension_ker_eq` and
  `Stacks.Chow.fibreCyclesRationallyEquivalentWithin_of_relativeDimension_genericPoint` —
  **part (2) of Stacks 02S4 when the image of `W` in `X` keeps the delta-dimension**, in the
  carrier-refined form the family statement of part (3) consumes.
* `Stacks.Chow.fibreCycles_rationallyEquivalent_of_schemeDeltaDimension_ker_eq` and
  `Stacks.Chow.fibreCycles_rationallyEquivalent_of_relativeDimension_genericPoint` — the same, in
  the two-cycle form the tag states.
* `Stacks.Chow.fibreCyclesRationallyEquivalentWithin_of_fibreDifference_eq_zero_of_dimension_drop`
  and `Stacks.Chow.…_of_relativeDimension_ne` — part (2) in general, granted only that the fibre
  difference vanishes when the projection drops delta-dimension at the generic point.
* `Stacks.Chow.relativeDimension_genericPoint_of_isDominant` and
  `Stacks.Chow.fibreCycles_rationallyEquivalent_of_isDominant` — the hypothesis holds whenever the
  projection `W ⟶ X` is dominant and `X` is irreducible of delta-dimension `k + 1`, so part (2) is
  unconditional in that case. This is the case the graph construction of part (4) of Stacks 02RQ
  produces, and it is what shows the hypothesis is satisfiable.

## Implementation notes

### The two structures on a fibre, and why no new geometry is needed to compare them

The fibre `W₀` appears twice: as `Stacks.Chow.zeroDivisor`, a closed subscheme of `W`, and as
`Stacks.Chow.zeroFiber`, a closed subscheme of `X` — the inverse image of `W` along the zero
section. Comparing their cycles is a kernel computation and the ideal correspondence for a
closed immersion, `Stacks.IdealSheaf.map_comap_of_isClosedImmersion`, which the proof of part (1)
already needed: pushing the zero divisor of `W` forward to `X` gives
`(zeroSection f).ker ⊔ W`, which is in turn the pushforward along the zero section of
`W.comap (zeroSection f)`, and the zero section is a section of the first projection, so pushing
forward along the first projection undoes it. That the cycle of a closed subscheme is unchanged
by presenting it through a different closed immersion is
`Stacks.Chow.cycleAssociatedToClosedSubscheme_eq_of_iso`, the cycle-level form of
`Stacks.Chow.closedSubschemeCycleCoeff_eq_of_iso` in
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant42.FlatPullbackComponent`.

### Grading

`Stacks.Chow.principalDivisorCycle` is indexed by `n - 1` where `n` is the delta-dimension, so at
`n = k + 1` it lands in `CycleGroup C _ (k + 1 - 1)`, a type not syntactically
`CycleGroup C _ k`. `Stacks.Chow.fibrePrincipalDivisorCycle` is the same cycle at index `k`, the
index being transported through the membership predicate, which is where the arithmetic can be
done — this is the device that
`Stacks.Chow.isRationallyEquivalentToZero_of_eq_principalCycle` uses for the same reason.

### What the dimension hypothesis is

The hypothesis of the main theorem is that the scheme-theoretic image of `W` in `X` has
delta-dimension `k + 1`, i.e. the same as `W`. It is **not** a scheme-theoretic condition in
disguise: `Stacks.Chow.schemeDeltaDimension_ker_fibreBaseProjection` identifies that
delta-dimension with the relative dimension of `X` at the single point `p(η)`, the image of the
generic point of `W`, so the hypothesis says exactly that the projection does not drop
delta-dimension at the generic point — the pointwise form of "generically finite". The
reformulation is a kernel computation: `W` is reduced, so the kernel of `p` is the vanishing
ideal of its own support, and that support is the closure of `p(η)`; the delta-dimension of the
reduced closure of a point is the relative dimension at that point
(`Stacks.Chow.schemeDeltaDimension_integralComponentAt`).

The two versions `…_of_schemeDeltaDimension_ker_eq` and `…_of_relativeDimension_genericPoint`
state the hypothesis in the two forms; the second is the one a consumer can check.

### `AlgebraicGeometry.Spec`

A root-level `Spec` is in scope through the transitive imports of this chapter; the name is not
used here, but any addition must write it out in full.

## References

* [Stacks Project, Tag 02S4](https://stacks.math.columbia.edu/tag/02S4)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 02RT](https://stacks.math.columbia.edu/tag/02RT)
* [Stacks Project, Tag 02RU](https://stacks.math.columbia.edu/tag/02RU)
* [Stacks Project, Tag 02R6](https://stacks.math.columbia.edu/tag/02R6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The cycle of a closed subscheme does not depend on its presentation -/

/-- The cycle of a closed immersion is the cycle of the closed subscheme it cuts out: a closed
immersion factors through its scheme-theoretic image by an isomorphism. -/
theorem cycleAssociatedToClosedSubscheme_ker (C : ChowSituation.{u}) {Y Z : Scheme.{u}}
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (j : Z ⟶ Y) [IsClosedImmersion j] (k : ℤ) :
    cycleAssociatedToClosedSubscheme C sY j k =
      cycleAssociatedToClosedSubscheme C sY j.ker.subschemeι k :=
  cycleAssociatedToClosedSubscheme_eq_of_iso C sY j j.ker.subschemeι (asIso j.toImage)
    j.toImage_imageι k

/-! ### The first projection of a closed subscheme of the family -/

section Base

variable {X S : Scheme.{u}} (f : X ⟶ S) (W : (projectiveLineProduct f).IdealSheafData)

/-- The first projection `W ⟶ X` of a closed subscheme `W ⊆ X ×_S ℙ¹_S`. Composed with the
structure morphism of `X` it is `Stacks.Chow.familyBase`. -/
def fibreBaseProjection : W.subscheme ⟶ X :=
  W.subschemeι ≫ pullback.fst f (relativeProjectiveLine S ↘ S)

/-- The first projection of `W` is the inclusion of `W` followed by the first projection of the
family. Named so that no proof has to unfold the definition. -/
theorem fibreBaseProjection_def :
    fibreBaseProjection f W = W.subschemeι ≫ pullback.fst f (relativeProjectiveLine S ↘ S) :=
  rfl

/-- The first projection of `W` is proper: a closed immersion followed by the first projection of
the family, which is proper because `ℙ¹_S ⟶ S` is. -/
instance isProper_fibreBaseProjection : IsProper (fibreBaseProjection f W) := by
  rw [fibreBaseProjection_def]
  infer_instance

/-- The first projection of `W` followed by the structure morphism of `X` is the structure
morphism of `W`. -/
theorem fibreBaseProjection_comp : fibreBaseProjection f W ≫ f = familyBase f W := by
  rw [fibreBaseProjection_def]
  exact Category.assoc _ _ _

/-- The zero divisor of a reduced `W`, included into `X`, is a closed subscheme of `X`. -/
instance isClosedImmersion_zeroDivisor_subschemeι_comp [IsReduced W.subscheme] :
    IsClosedImmersion ((zeroDivisor f W).subschemeι ≫ fibreBaseProjection f W) := by
  rw [zeroDivisor_eq_comap_lineZeroDivisor f W, fibreLineProjection_def, fibreBaseProjection_def]
  exact isClosedImmersion_comap_lineConstantSection_ker_comp f integralZeroSection W.subschemeι

/-- The infinity divisor of a reduced `W`, included into `X`, is a closed subscheme of `X`. -/
instance isClosedImmersion_infinityDivisor_subschemeι_comp [IsReduced W.subscheme] :
    IsClosedImmersion ((infinityDivisor f W).subschemeι ≫ fibreBaseProjection f W) := by
  rw [infinityDivisor_eq_comap_lineInfinityDivisor f W, fibreLineProjection_def,
    fibreBaseProjection_def]
  exact isClosedImmersion_comap_lineConstantSection_ker_comp f integralInfinitySection
    W.subschemeι

/-- The image in `X` of the pullback of the kernel of a section of the first projection to a
reduced `W` is the pullback of `W` along the section. -/
private theorem ker_comp_fibreBaseProjection_of_eq_comap_ker [IsReduced W.subscheme]
    (σ : X ⟶ projectiveLineProduct f) [IsClosedImmersion σ]
    (hσ : σ ≫ pullback.fst f (relativeProjectiveLine S ↘ S) = 𝟙 X)
    (D : W.subscheme.IdealSheafData) (hD : D = σ.ker.comap W.subschemeι) :
    (D.subschemeι ≫ fibreBaseProjection f W).ker = W.comap σ := by
  have hsplit : σ.ker ⊔ W = (W.comap σ).map σ := by
    rw [Stacks.IdealSheaf.map_comap_of_isClosedImmersion σ W, sup_comm]
  rw [← Scheme.IdealSheafData.map_ker, Scheme.IdealSheafData.ker_subschemeι,
    fibreBaseProjection_def, Scheme.IdealSheafData.map_comp, hD,
    Stacks.IdealSheaf.map_comap_of_isClosedImmersion W.subschemeι σ.ker,
    Scheme.IdealSheafData.ker_subschemeι, hsplit, ← Scheme.IdealSheafData.map_comp, hσ,
    Scheme.IdealSheafData.map_id]

/-- **The zero divisor of `W` and the zero fibre of `W` are the same closed subscheme of `X`.**
The scheme-theoretic image in `X` of the zero divisor of a reduced `W` is the zero fibre of `W`.

The zero divisor pushes forward from `W` to `(zeroSection f).ker ⊔ W` by the ideal
correspondence for the closed immersion `W ⟶ X ×_S ℙ¹_S`; that ideal sheaf is in turn the
pushforward along the zero section of `W.comap (zeroSection f)`, again by the ideal
correspondence; and the zero section is a section of the first projection, so pushing forward
along the first projection undoes it. -/
theorem ker_zeroDivisor_subschemeι_comp [IsReduced W.subscheme] :
    ((zeroDivisor f W).subschemeι ≫ fibreBaseProjection f W).ker = zeroFiber f W :=
  ker_comp_fibreBaseProjection_of_eq_comap_ker f W (zeroSection f) (zeroSection_comp_fst f) _
    (zeroDivisor_eq_comap_ker f W)

/-- **The infinity divisor of `W` and the infinity fibre of `W` are the same closed subscheme of
`X`.** -/
theorem ker_infinityDivisor_subschemeι_comp [IsReduced W.subscheme] :
    ((infinityDivisor f W).subschemeι ≫ fibreBaseProjection f W).ker = infinityFiber f W :=
  ker_comp_fibreBaseProjection_of_eq_comap_ker f W (infinitySection f)
    (infinitySection_comp_fst f) _ (infinityDivisor_eq_comap_ker f W)

end Base

/-! ### Pushing the two fibre cycles down to `X` -/

section Push

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (W : (projectiveLineProduct f).IdealSheafData) (k : ℤ)

/-- Proper pushforward along the first projection of `W` carries the cycle of a closed subscheme
of `W` to the cycle of the closed subscheme of `X` cut out by the kernel of the composite. -/
private theorem properPushforward_cycleAssociatedToClosedSubscheme_fibreBaseProjection
    {Z : Scheme.{u}} (i : Z ⟶ W.subscheme) [IsClosedImmersion i]
    [IsClosedImmersion (i ≫ fibreBaseProjection f W)] (V : X.IdealSheafData)
    (hV : (i ≫ fibreBaseProjection f W).ker = V) :
    properPushforward C (familyBase f W) f (fibreBaseProjection f W)
        (fibreBaseProjection_comp f W) k
        (cycleAssociatedToClosedSubscheme C (familyBase f W) i k) =
      cycleAssociatedToClosedSubscheme C f V.subschemeι k := by
  rw [properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp C
      (familyBase f W) f (fibreBaseProjection f W) (fibreBaseProjection_comp f W) i k,
    cycleAssociatedToClosedSubscheme_ker C f (i ≫ fibreBaseProjection f W) k, hV]

/-- **Proper pushforward carries the cycle of the zero divisor on `W` to the cycle of the zero
fibre on `X`.** This is the closed-immersion case of Stacks 02R6 together with the identification
of the two structures on the fibre. -/
theorem properPushforward_cycleAssociatedToClosedSubscheme_zeroDivisor
    [IsReduced W.subscheme] :
    properPushforward C (familyBase f W) f (fibreBaseProjection f W)
        (fibreBaseProjection_comp f W) k
        (cycleAssociatedToClosedSubscheme C (familyBase f W) (zeroDivisor f W).subschemeι k) =
      cycleAssociatedToClosedSubscheme C f (zeroFiber f W).subschemeι k :=
  properPushforward_cycleAssociatedToClosedSubscheme_fibreBaseProjection C f W k _ _
    (ker_zeroDivisor_subschemeι_comp f W)

/-- **Proper pushforward carries the cycle of the infinity divisor on `W` to the cycle of the
infinity fibre on `X`.** -/
theorem properPushforward_cycleAssociatedToClosedSubscheme_infinityDivisor
    [IsReduced W.subscheme] :
    properPushforward C (familyBase f W) f (fibreBaseProjection f W)
        (fibreBaseProjection_comp f W) k
        (cycleAssociatedToClosedSubscheme C (familyBase f W)
          (infinityDivisor f W).subschemeι k) =
      cycleAssociatedToClosedSubscheme C f (infinityFiber f W).subschemeι k :=
  properPushforward_cycleAssociatedToClosedSubscheme_fibreBaseProjection C f W k _ _
    (ker_infinityDivisor_subschemeι_comp f W)

/-! ### The principal divisor of the chart coordinate, at index `k` -/

/-- The principal divisor of the chart coordinate on an integral `W` of delta-dimension `k + 1`,
as a `k`-cycle on `W`.

This is `Stacks.Chow.principalDivisorCycle`, whose index is `k + 1 - 1` rather than `k`; the
index is transported through the membership predicate, where the arithmetic can be done. -/
def fibrePrincipalDivisorCycle [IsIntegral W.subscheme]
    (hdim : schemeDeltaDimension C (familyBase f W) = ((k + 1 : ℤ) : EInt))
    (hInf : ¬ Set.range W.subschemeι ⊆ Set.range (infinitySection f)) :
    CycleGroup C (familyBase f W) k :=
  letI : IsLocallyNoetherian W.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (familyBase f W)
  ⟨principalCycle W.subscheme (fibreCoordinate C f W hInf), by
    have h := principalCycle_mem_cyclesOfDimension C (familyBase f W) hdim
      (fibreCoordinate C f W hInf)
    rwa [show (k + 1 - 1 : ℤ) = k by ring] at h⟩

/-- **The difference of the two fibre cycles on `W` is the principal divisor of the chart
coordinate, at index `k`.** This is
`Stacks.Chow.principalDivisorCycle_eq_sub_fibreDivisorCycles` with the index moved from
`k + 1 - 1` to `k`. -/
theorem fibrePrincipalDivisorCycle_eq_sub [IsIntegral W.subscheme]
    (hdim : schemeDeltaDimension C (familyBase f W) = ((k + 1 : ℤ) : EInt))
    (h₀ : ¬ Set.range W.subschemeι ⊆ Set.range (zeroSection f))
    (hInf : ¬ Set.range W.subschemeι ⊆ Set.range (infinitySection f)) :
    fibrePrincipalDivisorCycle C f W k hdim hInf =
      cycleAssociatedToClosedSubscheme C (familyBase f W) (zeroDivisor f W).subschemeι k -
        cycleAssociatedToClosedSubscheme C (familyBase f W)
          (infinityDivisor f W).subschemeι k := by
  have _ : IsLocallyNoetherian W.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (familyBase f W)
  have h := congrArg Subtype.val
    (principalDivisorCycle_eq_sub_fibreDivisorCycles C f W hdim h₀ hInf)
  rw [AddSubgroup.coe_sub,
    show (principalDivisorCycle C (familyBase f W) hdim (fibreCoordinate C f W hInf) :
      AlgebraicCycle W.subscheme ℤ) =
      principalCycle W.subscheme (fibreCoordinate C f W hInf) from rfl] at h
  rw [show (k + 1 - 1 : ℤ) = k by ring] at h
  exact Subtype.ext (by rwa [AddSubgroup.coe_sub])

/-- **The fibre difference of `W` on `X` is the proper pushforward of a principal divisor on
`W`.** This is the first two steps of the source's proof of part (2) of Stacks 02S4: the
difference of the two fibre cycles on `W` is a principal divisor, and proper pushforward carries
each fibre cycle on `W` to the corresponding one on `X`. -/
theorem fibreDifference_eq_properPushforward [IsIntegral W.subscheme]
    (hdim : schemeDeltaDimension C (familyBase f W) = ((k + 1 : ℤ) : EInt))
    (h₀ : ¬ Set.range W.subschemeι ⊆ Set.range (zeroSection f))
    (hInf : ¬ Set.range W.subschemeι ⊆ Set.range (infinitySection f)) :
    fibreDifference C f k W =
      properPushforward C (familyBase f W) f (fibreBaseProjection f W)
        (fibreBaseProjection_comp f W) k (fibrePrincipalDivisorCycle C f W k hdim hInf) := by
  rw [fibrePrincipalDivisorCycle_eq_sub C f W k hdim h₀ hInf, properPushforward_sub,
    properPushforward_cycleAssociatedToClosedSubscheme_zeroDivisor C f W k,
    properPushforward_cycleAssociatedToClosedSubscheme_infinityDivisor C f W k]
  rfl

end Push

/-! ### One principal divisor, pushed forward -/

section OnePrincipal

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]

/-- A `k`-cycle which is the pushforward of the principal divisor of a rational function on a
single integral closed subscheme `V` of delta-dimension `k + 1` is rationally equivalent to zero
within any set containing the support of `V`: the one-element family `{V}` is a witnessing
family for Stacks 02RW. -/
theorem isRationallyEquivalentToZeroWithin_of_eq_principalDivisorPushforward {k : ℤ}
    (V : Y.IdealSheafData) (hV : IsIntegral V.subscheme)
    (hdim : schemeDeltaDimension C (V.subschemeι ≫ sY) = ((k + 1 : ℤ) : EInt))
    (g : (rationalFunctions V.subscheme)ˣ) {T : Set Y} (hT : (V.support : Set Y) ⊆ T)
    (α : CycleGroup C sY k)
    (hα : (α : AlgebraicCycle Y ℤ) = principalDivisorPushforward C sY V hV g) :
    IsRationallyEquivalentToZeroWithin C sY k α T := by
  refine ⟨PUnit.{u + 1}, fun _ ↦ V, fun _ ↦ hV, fun _ ↦ hdim,
    fun y ↦ ⟨Set.univ, Filter.univ_mem, Set.toFinite _⟩, fun _ ↦ hT, fun _ ↦ g, fun y ↦ ?_⟩
  change (α : AlgebraicCycle Y ℤ) y = ∑ᶠ _ : PUnit.{u + 1}, _
  rw [finsum_unique, hα]

/-- **The Stacks 02RT branch of Stacks 02S2 for a single principal divisor.** Let `A` be integral
of delta-dimension `k + 1` over the base and let `p : A ⟶ Y` be proper over the base. If the
scheme-theoretic image of `p` again has delta-dimension `k + 1`, then the proper pushforward
along `p` of the principal divisor of a nonzero rational function on `A` is rationally equivalent
to zero within the closure of the image of `p`.

This is Stacks 02RT applied to `A ⟶ p(A)`, which is proper and dominant, together with the
functoriality of proper pushforward; the rational function produced on the image is the norm of
the given one in the finite extension of function fields. No case of Stacks 02RU is used, which
is why the hypothesis on the delta-dimension of the image is present. -/
theorem isRationallyEquivalentToZeroWithin_properPushforward_principalCycle
    {A : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA] [IsIntegral A]
    [IsLocallyNoetherian A] {k : ℤ}
    (p : A ⟶ Y) [IsProper p] (hp : p ≫ sY = sA)
    (hdim : schemeDeltaDimension C sA = ((k + 1 : ℤ) : EInt))
    (hdimT : schemeDeltaDimension C (p.ker.subschemeι ≫ sY) = ((k + 1 : ℤ) : EInt))
    {g : A.functionField} (hg : g ≠ 0) (α : CycleGroup C sA k)
    (hα : (α : AlgebraicCycle A ℤ) = principalCycle A g) :
    IsRationallyEquivalentToZeroWithin C sY k (properPushforward C sA sY p hp k α)
      (closure (Set.range p.base)) := by
  have hT : IsIntegral p.ker.subscheme := isIntegral_image p
  have _ : IsLocallyNoetherian p.ker.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (p.ker.subschemeι ≫ sY)
  -- the morphism onto the scheme-theoretic image
  have hπ : p.toImage ≫ p.ker.subschemeι = p := p.toImage_imageι
  have _ : IsProper p.toImage := isProper_toImage p
  have hπs : p.toImage ≫ (p.ker.subschemeι ≫ sY) = sA := by
    rw [← Category.assoc, hπ, hp]
  -- the norm of `g` along the extension of function fields
  let eT := (rationalFunctionsEquivFunctionField p.ker.subscheme).1
  let _ : Algebra p.ker.subscheme.functionField A.functionField :=
    (dominantFunctionFieldMap p.toImage).toAlgebra
  set nm : p.ker.subscheme.functionField := Algebra.norm p.ker.subscheme.functionField g
  have hnmne : nm ≠ 0 :=
    ((isUnit_iff_ne_zero.mpr hg).map (Algebra.norm p.ker.subscheme.functionField)).ne_zero
  set h : (rationalFunctions p.ker.subscheme)ˣ :=
    Units.mapEquiv eT.symm.toMulEquiv (isUnit_iff_ne_zero.mpr hnmne).unit with hhdef
  have hval : eT (h : rationalFunctions p.ker.subscheme) = nm := by simp [hhdef]
  -- Stacks 02RT for the restriction of `p` to its image
  have hcycle : AlgebraicCycle.map p.toImage
      (relativeDimension C.dimensionFunction sA)
      (relativeDimension C.dimensionFunction (p.ker.subschemeι ≫ sY))
      (principalCycle A g) = principalCycle p.ker.subscheme nm :=
    congrArg Subtype.val (properPushforward_principalDivisorCycle C sA (p.ker.subschemeι ≫ sY)
      hdim hdimT p.toImage hπs g hg)
  refine isRationallyEquivalentToZeroWithin_of_eq_principalDivisorPushforward C sY p.ker hT
    hdimT h (by rw [Scheme.Hom.support_ker]) _ ?_
  change AlgebraicCycle.map p (relativeDimension C.dimensionFunction sA)
    (relativeDimension C.dimensionFunction sY) (α : AlgebraicCycle A ℤ) =
      principalDivisorPushforward C sY p.ker hT h
  rw [hα]
  calc AlgebraicCycle.map p (relativeDimension C.dimensionFunction sA)
        (relativeDimension C.dimensionFunction sY) (principalCycle A g)
      = AlgebraicCycle.map (p.toImage ≫ p.ker.subschemeι)
          (relativeDimension C.dimensionFunction sA)
          (relativeDimension C.dimensionFunction sY) (principalCycle A g) :=
        algebraicCycle_map_congr hπ.symm _ _ _
    _ = AlgebraicCycle.map p.ker.subschemeι
          (relativeDimension C.dimensionFunction (p.ker.subschemeι ≫ sY))
          (relativeDimension C.dimensionFunction sY)
          (AlgebraicCycle.map p.toImage (relativeDimension C.dimensionFunction sA)
            (relativeDimension C.dimensionFunction (p.ker.subschemeι ≫ sY))
            (principalCycle A g)) :=
        (algebraicCycle_map_comp_relativeDimension C sA (p.ker.subschemeι ≫ sY) sY
          p.toImage p.ker.subschemeι hπs rfl _).symm
    _ = principalDivisorPushforward C sY p.ker hT h := by
        rw [hcycle, principalDivisorPushforward, hval]

end OnePrincipal

/-! ### Part (2) of Stacks 02S4 -/

section PartTwo

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]

omit [LocallyOfFiniteType f] in
/-- The closure of the image of the first projection of `W` is the carrier
`Stacks.Chow.fibreCarrier` of the fibre difference of `W`. -/
theorem closure_range_fibreBaseProjection (W : (projectiveLineProduct f).IdealSheafData) :
    closure (Set.range (fibreBaseProjection f W).base) = fibreCarrier C f W := by
  rw [fibreBaseProjection_def, range_comp_scheme, Scheme.IdealSheafData.range_subschemeι W]
  rfl

/-- **Part (2) of Stacks Tag 02S4 when the image of `W` in `X` keeps the delta-dimension**, in the
carrier-refined form. For an integral `W ⊆ X ×_S ℙ¹_S` of delta-dimension `k + 1` contained in
neither distinguished section, whose scheme-theoretic image in `X` again has delta-dimension
`k + 1`, the difference of the two fibre cycles is rationally equivalent to zero within
`Stacks.Chow.fibreCarrier`.

The hypothesis on the image is what makes the Stacks 02RT branch of Stacks 02S2 apply; it holds
exactly when `W ⟶ X` is generically finite. -/
theorem fibreCyclesRationallyEquivalentWithin_of_schemeDeltaDimension_ker_eq
    (W : (projectiveLineProduct f).IdealSheafData) [IsIntegral W.subscheme] (k : ℤ)
    (hdim : schemeDeltaDimension C (familyBase f W) = ((k + 1 : ℤ) : EInt))
    (hker : schemeDeltaDimension C ((fibreBaseProjection f W).ker.subschemeι ≫ f) =
      ((k + 1 : ℤ) : EInt))
    (h₀ : ¬ Set.range W.subschemeι ⊆ Set.range (zeroSection f))
    (hInf : ¬ Set.range W.subschemeι ⊆ Set.range (infinitySection f)) :
    IsRationallyEquivalentToZeroWithin C f k (fibreDifference C f k W) (fibreCarrier C f W) := by
  have _ : IsLocallyNoetherian W.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (familyBase f W)
  have hne : fibreCoordinate C f W hInf ≠ 0 := by
    have hmul := lineChartFunction_mul_lineYChartFunction (fibreLineProjection f W)
      (genericPoint_mem_preimage_chartOpen f W hInf)
      (genericPoint_mem_preimage_yChartOpen f W h₀)
    exact left_ne_zero_of_mul_eq_one hmul
  rw [fibreDifference_eq_properPushforward C f W k hdim h₀ hInf,
    ← closure_range_fibreBaseProjection C f W]
  exact isRationallyEquivalentToZeroWithin_properPushforward_principalCycle C f
    (familyBase f W) (fibreBaseProjection f W) (fibreBaseProjection_comp f W) hdim hker hne _ rfl

/-- **Part (2) of Stacks Tag 02S4 when the image of `W` in `X` keeps the delta-dimension**, in the
two-cycle form the tag states: the cycles of the two fibres, viewed as closed subschemes of `X`,
are rationally equivalent. -/
theorem fibreCycles_rationallyEquivalent_of_schemeDeltaDimension_ker_eq
    (W : (projectiveLineProduct f).IdealSheafData) [IsIntegral W.subscheme] (k : ℤ)
    (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension C.dimensionFunction (familyBase f W) ξ.1 = k + 1)
    (hker : schemeDeltaDimension C ((fibreBaseProjection f W).ker.subschemeι ≫ f) =
      ((k + 1 : ℤ) : EInt))
    (h₀ : ¬ Set.range W.subschemeι ⊆ Set.range (zeroSection f))
    (hInf : ¬ Set.range W.subschemeι ⊆ Set.range (infinitySection f)) :
    RationallyEquivalent C f k
      (cycleAssociatedToClosedSubscheme C f (zeroFiber f W).subschemeι k)
      (cycleAssociatedToClosedSubscheme C f (infinityFiber f W).subschemeι k) :=
  (fibreCyclesRationallyEquivalentWithin_of_schemeDeltaDimension_ker_eq C f W k
    (schemeDeltaDimension_familyBase C f W hDim) hker h₀
    hInf).isRationallyEquivalentToZero

/-- **Part (2) of Stacks Tag 02S4, granted only the delta-dimension-drop case.** The whole of the
one-member obligation `Stacks.Chow.FibreCyclesRationallyEquivalentWithin` — and hence, by
`Stacks.Chow.familyFibreDifferencesRationallyEquivalentToZero_of_within`, part (3) of the tag and
Stacks 02S5 — follows from the single statement that the fibre difference of `W` vanishes when
the scheme-theoretic image of `W` in `X` fails to keep the delta-dimension.

That case is where the source's proof of Stacks 02S2 invokes Stacks 02RU: the generic fibre of
`W ⟶ p(W)` is then a proper curve over the function field of the image, and the degree of a
principal divisor there vanishes. The library's Stacks 02RU
(`Stacks.Chow.properPushforward_principalDivisorCycle_eq_zero`) is the case of a base which is
the spectrum of a field with vanishing dimension function, so discharging the hypothesis needs
the generic fibre as a base change and not a rewording. -/
theorem fibreCyclesRationallyEquivalentWithin_of_fibreDifference_eq_zero_of_dimension_drop
    (k : ℤ)
    (hdrop : ∀ W : (projectiveLineProduct f).IdealSheafData, IsIntegral W.subscheme →
      schemeDeltaDimension C (familyBase f W) = ((k + 1 : ℤ) : EInt) →
      schemeDeltaDimension C ((fibreBaseProjection f W).ker.subschemeι ≫ f) ≠
        ((k + 1 : ℤ) : EInt) →
      fibreDifference C f k W = 0) :
    FibreCyclesRationallyEquivalentWithin C f k := by
  intro W hW hDim h₀ hInf
  have := hW
  have hdim := schemeDeltaDimension_familyBase C f W hDim
  by_cases hker : schemeDeltaDimension C ((fibreBaseProjection f W).ker.subschemeι ≫ f) =
      ((k + 1 : ℤ) : EInt)
  · exact fibreCyclesRationallyEquivalentWithin_of_schemeDeltaDimension_ker_eq C f W k hdim hker
      h₀ hInf
  · rw [hdrop W hW hdim hker]
    exact isRationallyEquivalentToZeroWithin_zero C f k _

/-! ### The dimension hypothesis as a condition at the generic point -/

omit [LocallyOfFiniteType f] in
/-- The scheme-theoretic image of `W` in `X` is the reduced closure of the image of the generic
point of `W`: an integral `W` is reduced, so the kernel of the projection is the vanishing ideal
of its own support, and that support is the closure of the image of the generic point. -/
theorem ker_fibreBaseProjection_eq_integralComponentAt
    (W : (projectiveLineProduct f).IdealSheafData) [IsIntegral W.subscheme] :
    (fibreBaseProjection f W).ker =
      integralComponentAt ((fibreBaseProjection f W).base (genericPoint W.subscheme)) := by
  have _ : IsReduced W.subscheme := isReduced_of_isIntegral W.subscheme
  have hsupp : ((fibreBaseProjection f W).ker.support : Set X) =
      closure {(fibreBaseProjection f W).base (genericPoint W.subscheme)} := by
    rw [Scheme.Hom.support_ker]
    exact (closure_range_eq_closure_generic_image (fibreBaseProjection f W).base
      (fibreBaseProjection f W).continuous (genericPoint W.subscheme)
      (genericPoint_spec W.subscheme)).symm
  refine (ker_eq_vanishingIdeal_support_of_isReduced (fibreBaseProjection f W)).trans ?_
  exact congrArg Scheme.IdealSheafData.vanishingIdeal (Closeds.ext hsupp)

/-- **The delta-dimension of the image of `W` in `X` is a quantity at one point**: the relative
dimension of `X` at the image of the generic point of `W`. -/
theorem schemeDeltaDimension_ker_fibreBaseProjection
    (W : (projectiveLineProduct f).IdealSheafData) [IsIntegral W.subscheme] :
    schemeDeltaDimension C ((fibreBaseProjection f W).ker.subschemeι ≫ f) =
      ((relativeDimension C.dimensionFunction f
        ((fibreBaseProjection f W).base (genericPoint W.subscheme)) : ℤ) : EInt) := by
  rw [ker_fibreBaseProjection_eq_integralComponentAt C f W,
    schemeDeltaDimension_integralComponentAt]

/-- **Part (2) of Stacks Tag 02S4 when the projection does not drop delta-dimension at the
generic point**, in the carrier-refined form. This is
`Stacks.Chow.fibreCyclesRationallyEquivalentWithin_of_schemeDeltaDimension_ker_eq` with its
hypothesis on the scheme-theoretic image rewritten as a condition at one point. -/
theorem fibreCyclesRationallyEquivalentWithin_of_relativeDimension_genericPoint
    (W : (projectiveLineProduct f).IdealSheafData) [IsIntegral W.subscheme] (k : ℤ)
    (hdim : schemeDeltaDimension C (familyBase f W) = ((k + 1 : ℤ) : EInt))
    (hgen : relativeDimension C.dimensionFunction f
      ((fibreBaseProjection f W).base (genericPoint W.subscheme)) = k + 1)
    (h₀ : ¬ Set.range W.subschemeι ⊆ Set.range (zeroSection f))
    (hInf : ¬ Set.range W.subschemeι ⊆ Set.range (infinitySection f)) :
    IsRationallyEquivalentToZeroWithin C f k (fibreDifference C f k W) (fibreCarrier C f W) :=
  fibreCyclesRationallyEquivalentWithin_of_schemeDeltaDimension_ker_eq C f W k hdim
    (by rw [schemeDeltaDimension_ker_fibreBaseProjection C f W, hgen]) h₀ hInf

/-- **Part (2) of Stacks Tag 02S4 when the projection does not drop delta-dimension at the
generic point**, in the two-cycle form the tag states. The statement is the tag's part (2)
verbatim with one hypothesis added, namely `hgen`. -/
theorem fibreCycles_rationallyEquivalent_of_relativeDimension_genericPoint
    (W : (projectiveLineProduct f).IdealSheafData) [IsIntegral W.subscheme] (k : ℤ)
    (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension C.dimensionFunction (familyBase f W) ξ.1 = k + 1)
    (hgen : relativeDimension C.dimensionFunction f
      ((fibreBaseProjection f W).base (genericPoint W.subscheme)) = k + 1)
    (h₀ : ¬ Set.range W.subschemeι ⊆ Set.range (zeroSection f))
    (hInf : ¬ Set.range W.subschemeι ⊆ Set.range (infinitySection f)) :
    RationallyEquivalent C f k
      (cycleAssociatedToClosedSubscheme C f (zeroFiber f W).subschemeι k)
      (cycleAssociatedToClosedSubscheme C f (infinityFiber f W).subschemeι k) :=
  (fibreCyclesRationallyEquivalentWithin_of_relativeDimension_genericPoint C f W k
    (schemeDeltaDimension_familyBase C f W hDim) hgen h₀
    hInf).isRationallyEquivalentToZero

/-- **Part (2) of Stacks Tag 02S4, granted only the case in which the projection drops
delta-dimension at the generic point.** This is
`Stacks.Chow.fibreCyclesRationallyEquivalentWithin_of_fibreDifference_eq_zero_of_dimension_drop`
with its hypothesis stated at one point. -/
theorem fibreCyclesRationallyEquivalentWithin_of_fibreDifference_eq_zero_of_relativeDimension_ne
    (k : ℤ)
    (hdrop : ∀ W : (projectiveLineProduct f).IdealSheafData, [IsIntegral W.subscheme] →
      schemeDeltaDimension C (familyBase f W) = ((k + 1 : ℤ) : EInt) →
      relativeDimension C.dimensionFunction f
          ((fibreBaseProjection f W).base (genericPoint W.subscheme)) ≠ k + 1 →
      fibreDifference C f k W = 0) :
    FibreCyclesRationallyEquivalentWithin C f k := by
  refine fibreCyclesRationallyEquivalentWithin_of_fibreDifference_eq_zero_of_dimension_drop C f k
    fun W hW hdim hker ↦ ?_
  have := hW
  exact hdrop W hdim fun hgen ↦
    hker (by rw [schemeDeltaDimension_ker_fibreBaseProjection C f W, hgen])

/-! ### The hypothesis is satisfiable: a dominant projection -/

/-- **The dimension hypothesis holds whenever the projection `W ⟶ X` is dominant** and `X` is
irreducible of delta-dimension `k + 1`: the image of the generic point of `W` is then a generic
point of `X`, hence the generic point of `X`, where the relative dimension is the
delta-dimension of `X` by Stacks 02QP.

This is what makes the hypothesis of the theorems above satisfiable rather than vacuous. The
graph construction of Stacks 02RQ produces exactly such a `W`: the closure of the graph of a
rational function on an integral closed subscheme of `X`, whose projection is dominant by
`Stacks.Chow.isDominant_graphProjection`. -/
theorem relativeDimension_genericPoint_of_isDominant
    (W : (projectiveLineProduct f).IdealSheafData) [IsIntegral W.subscheme]
    [IrreducibleSpace X] (hdom : IsDominant (fibreBaseProjection f W)) {k : ℤ}
    (hX : schemeDeltaDimension C f = ((k + 1 : ℤ) : EInt)) :
    relativeDimension C.dimensionFunction f
      ((fibreBaseProjection f W).base (genericPoint W.subscheme)) = k + 1 := by
  have hgp : IsGenericPoint ((fibreBaseProjection f W).base (genericPoint W.subscheme))
      (Set.univ : Set X) := by
    rw [IsGenericPoint, closure_range_eq_closure_generic_image (fibreBaseProjection f W).base
      (fibreBaseProjection f W).continuous (genericPoint W.subscheme)
      (genericPoint_spec W.subscheme)]
    exact hdom.denseRange.closure_range
  have heq : (fibreBaseProjection f W).base (genericPoint W.subscheme) = genericPoint X :=
    hgp.eq (genericPoint_spec X)
  have h := schemeDeltaDimension_eq_genericPoint C f
  rw [hX] at h
  rw [heq, ← WithBotTop.coe_injective h]

/-- **Part (2) of Stacks Tag 02S4 for an integral family whose projection to `X` is dominant**,
with no hypothesis beyond those of the tag and the irreducibility and delta-dimension of `X`.
This is the case the graph construction of part (4) of Stacks 02RQ produces. -/
theorem fibreCycles_rationallyEquivalent_of_isDominant
    (W : (projectiveLineProduct f).IdealSheafData) [IsIntegral W.subscheme]
    [IrreducibleSpace X] (k : ℤ)
    (hX : schemeDeltaDimension C f = ((k + 1 : ℤ) : EInt))
    (hdom : IsDominant (fibreBaseProjection f W))
    (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension C.dimensionFunction (familyBase f W) ξ.1 = k + 1)
    (h₀ : ¬ Set.range W.subschemeι ⊆ Set.range (zeroSection f))
    (hInf : ¬ Set.range W.subschemeι ⊆ Set.range (infinitySection f)) :
    RationallyEquivalent C f k
      (cycleAssociatedToClosedSubscheme C f (zeroFiber f W).subschemeι k)
      (cycleAssociatedToClosedSubscheme C f (infinityFiber f W).subschemeι k) :=
  fibreCycles_rationallyEquivalent_of_relativeDimension_genericPoint C f W k hDim
    (relativeDimension_genericPoint_of_isDominant C f W hdom hX) h₀ hInf

end PartTwo

end Stacks.Chow

end
