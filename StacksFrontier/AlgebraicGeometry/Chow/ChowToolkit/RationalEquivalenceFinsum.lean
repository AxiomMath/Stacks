module

public import StacksFrontier.AlgebraicGeometry.Chow.ChowToolkit.ClosedImmersionCarrier
public import StacksFrontier.AlgebraicGeometry.Chow.ChowToolkit.Properness
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.ChowGroup
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.PiecePushforward
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Functoriality

/-!
# Rational equivalence decomposes along a decomposition into open and closed pieces

Let `X` be a scheme locally of finite type over the base scheme of chapter 42 of the Stacks
Project. Stacks 02RZ, proved in
`StacksFrontier.AlgebraicGeometry.Chow.ChowToolkit.ClosedImmersionCarrier`, sums rational
equivalences over a locally finite family of **closed subschemes** of `X`. This file extends it to a
locally finite family of **arbitrary closed immersions** `j i : Z i ⟶ X`, and applies the result to
close the one gap in the decomposition of the Chow groups along a decomposition
`X = \coprod_i X_i` into open and closed subschemes.

The extension is free. A closed immersion factors through its scheme-theoretic image
`(Scheme.Hom.ker (j i)).subscheme` by an isomorphism, so a cycle on `Z i` rationally equivalent to
zero pushes forward to one on that closed subscheme, and the pushforward to `X` is unchanged by
`Stacks.Chow.properPushforward_comp`. The first step needs **no** instance of Stacks 02S2:
`Scheme.Hom.toImage (j i)` is a closed immersion, and Stacks 02S2 for a closed immersion is the
already-proved
`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion`.

The application is `Stacks.Chow.rationalEquivalenceDecomposes_mpr`, the **reverse** half of
`Stacks.Chow.RationalEquivalenceDecomposes`, which was the remaining gap in that development: the
inclusion of a piece is a closed immersion
(`Stacks.Chow.IsClopenDecomposition.isClosedImmersion_ι`), the pieces form a locally finite family
because they are disjoint and open, and a cycle is the locally finite sum of the pushforwards of its
restrictions to the pieces. It carries **no hypothesis at all**. Together with the already-proved
forward half it gives `Stacks.Chow.rationalEquivalenceDecomposes_of_flatPullbackFactors`, hence
`CH_k(X) = ∏_i CH_k(X_i)` through `Stacks.Chow.chowGroupClopenEquiv`, from Stacks 02S1 at the piece
inclusions alone.

## Main results

* `Stacks.Chow.rationallyEquivalentToZero_finsum_of_isClosedImmersion` — a locally finite sum of
  pushforwards along closed immersions of cycles rationally equivalent to zero is rationally
  equivalent to zero.
* `Stacks.Chow.IsClopenDecomposition.locallyFinite_coe`,
  `Stacks.Chow.IsClopenDecomposition.locallyFinite_range_ι` — the pieces of a decomposition into
  open and closed subschemes form a locally finite family.
* `Stacks.Chow.cycle_eq_finsum_properPushforward_opensRestrict` — a cycle is the locally finite sum
  of the pushforwards of its restrictions to the pieces.
* `Stacks.Chow.rationalEquivalenceDecomposes_mpr` — the reverse half of
  `Stacks.Chow.RationalEquivalenceDecomposes`, unconditionally.
* `Stacks.Chow.rationalEquivalenceDecomposes_of_flatPullbackFactors` — the whole of
  `Stacks.Chow.RationalEquivalenceDecomposes`, from Stacks 02S1 at the piece inclusions.

## Implementation notes

The index type of the pieces is restricted to `Type u`, the universe of the schemes, throughout
this file. That is forced and not a convenience: `Stacks.Chow.IsRationallyEquivalentToZero`
existentially quantifies the index type of the witnessing family over `Type u`, and the witness
assembled from a family indexed by `I` is indexed by a sigma type over `I`. So where the
decomposition of *cycles* (`Stacks.Chow.cycleGroupClopenEquiv`) allows the pieces to be indexed by
any universe, the decomposition of *rational equivalence* obtained here does not — a consumer
needing the Chow-group decomposition for pieces indexed outside `Type u` must supply
`Stacks.Chow.RationalEquivalenceDecomposes` by another route.

Properness of a piece inclusion is taken as an instance hypothesis where it is needed, rather than
derived, because it holds exactly when the piece is closed and that is a hypothesis rather than an
instance; a consumer writes `have := h.isProper_ι` and applies the result. This follows
`StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.PiecePushforward`.

No `@[stacks 02UC]` attribute is placed here. The covering set of that tag is its two statements,
`eq_zero_iff_cap_integral_eq_zero` and `eq_zero_iff_cap_proper_birational_eq_zero`, neither of which
is formalized in this repository; the results below are inputs to them.

## References

* [Stacks Project, Tag 02RZ](https://stacks.math.columbia.edu/tag/02RZ)
* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}}

/-! ### Summing along a family of closed immersions -/

/-- **A locally finite sum of pushforwards along closed immersions of cycles rationally equivalent
to zero is rationally equivalent to zero.**

The closed immersion `j i` is the composite of the isomorphism `Scheme.Hom.toImage (j i)` onto its
scheme-theoretic image with the inclusion of that image, so pushing `a i` forward in two steps
agrees with pushing it forward along `j i`. The first step preserves rational equivalence with no
hypothesis, since Stacks 02S2 for a closed immersion is proved outright as
`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion`; the second
step is Stacks 02RZ, `Stacks.Chow.rationallyEquivalentToZero_finsum_of_closedSupports`. -/
theorem rationallyEquivalentToZero_finsum_of_isClosedImmersion (C : ChowSituation.{u})
    (s : X ⟶ C.S) [LocallyOfFiniteType s] (k : ℤ)
    {I : Type u} {Z : I → Scheme.{u}} (j : ∀ i, Z i ⟶ X) [∀ i, IsClosedImmersion (j i)]
    (hfinite : LocallyFinite fun i ↦ Set.range (j i))
    (a : ∀ i, CycleGroup C (j i ≫ s) k)
    (ha : ∀ i, IsRationallyEquivalentToZero C (j i ≫ s) k (a i))
    (α : CycleGroup C s k)
    (hα : ∀ x : X, α.1 x = ∑ᶠ i : I,
      (properPushforward C (j i ≫ s) s (j i) rfl k (a i)).1 x) :
    IsRationallyEquivalentToZero C s k α := by
  have he (i : I) : (j i).toImage ≫ ((j i).ker).subschemeι = j i := (j i).toImage_imageι
  have hcomp (i : I) : (j i).toImage ≫ ((((j i).ker).subschemeι) ≫ s) = j i ≫ s := by
    rw [← Category.assoc, he]
  -- Push `a i` forward to the scheme-theoretic image of `j i`.
  set b : ∀ i, CycleGroup C ((((j i).ker).subschemeι) ≫ s) k := fun i ↦
    properPushforward C (j i ≫ s) ((((j i).ker).subschemeι) ≫ s) (j i).toImage (hcomp i) k (a i)
    with hb
  have hfinite' : LocallyFinite fun i ↦ ((((j i).ker)).support : Set X) := by
    refine hfinite.subset fun i ↦ ?_
    rw [Scheme.Hom.support_ker, (j i).isClosedMap.isClosed_range.closure_eq]
  have hbzero (i : I) : IsRationallyEquivalentToZero C ((((j i).ker).subschemeι) ≫ s) k (b i) := by
    have h02S2 := properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion
      (j i).toImage C (j i ≫ s) ((((j i).ker).subschemeι) ≫ s) (hcomp i) k
    exact h02S2 (a i) (ha i)
  refine rationallyEquivalentToZero_finsum_of_closedSupports C s k (fun i ↦ (j i).ker) hfinite'
    b hbzero fun x ↦ ?_
  rw [hα x]
  refine finsum_congr fun i ↦ ?_
  have hfun := congrFun (properPushforward_comp C (j i ≫ s) ((((j i).ker).subschemeι) ≫ s) s
    (j i).toImage (((j i).ker)).subschemeι (hcomp i) rfl k) (a i)
  simpa only [Function.comp_apply, he, hb] using
    (congrArg (fun z : CycleGroup C s k ↦ z.1 x) hfun).symm

/-! ### The pieces of a decomposition into open and closed subschemes -/

variable {I : Type u} {U : I → X.Opens}

namespace IsClopenDecomposition

/-- The pieces of a decomposition of `X` into open and closed subschemes form a locally finite
family: each is open, and the one containing a point is a neighbourhood of it meeting no other. -/
theorem locallyFinite_coe (h : IsClopenDecomposition U) :
    LocallyFinite fun i ↦ (U i : Set X) :=
  Stacks.Topology.locallyFinite_of_disjoint_open_cover _ (fun i ↦ (U i).2)
    (fun x ↦ h.exists_mem x) fun _ _ hij ↦ (Opens.coe_disjoint).2 (h.disjoint _ _ hij)

/-- The ranges of the inclusions of the pieces of a decomposition of `X` into open and closed
subschemes form a locally finite family. -/
theorem locallyFinite_range_ι (h : IsClopenDecomposition U) :
    LocallyFinite fun i ↦ Set.range (U i).ι := by
  simpa only [Scheme.Opens.range_ι] using h.locallyFinite_coe

end IsClopenDecomposition

/-- At a point of an open and closed subscheme `V`, the pushforward from `V` of the restriction of
a cycle to `V` has the cycle's own coefficient. This is
`Stacks.Chow.opensRestrictCycle_properPushforward_self` read coefficientwise. -/
theorem properPushforward_opensRestrict_apply_self (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (V : X.Opens) [IsProper V.ι] (k : ℤ) (c : CycleGroup C f k)
    (z : (V : Scheme.{u})) :
    (properPushforward C (V.ι ≫ f) f V.ι rfl k (cycleGroupOpensRestrict C f V k c)).1
      (V.ι.base z) = c.1 (V.ι.base z) :=
  DFunLike.congr_fun
    (opensRestrictCycle_properPushforward_self C f V k (cycleGroupOpensRestrict C f V k c)) z

/-- At a point of an open subscheme disjoint from `V`, the pushforward from an open and closed
subscheme `V` of the restriction of a cycle to `V` vanishes. This is
`Stacks.Chow.opensRestrictCycle_properPushforward_of_disjoint` read coefficientwise. -/
theorem properPushforward_opensRestrict_apply_of_disjoint (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (V W : X.Opens) [IsProper V.ι] (hVW : Disjoint V W) (k : ℤ)
    (c : CycleGroup C f k) (z : (W : Scheme.{u})) :
    (properPushforward C (V.ι ≫ f) f V.ι rfl k (cycleGroupOpensRestrict C f V k c)).1
      (W.ι.base z) = 0 :=
  DFunLike.congr_fun
    (opensRestrictCycle_properPushforward_of_disjoint C f V W hVW k
      (cycleGroupOpensRestrict C f V k c)) z

/-- **A cycle is the locally finite sum of the pushforwards of its restrictions to the pieces** of
a decomposition of `X` into open and closed subschemes. At a point `x` only the piece containing
`x` contributes: the fibre of the inclusion of any other piece over `x` is empty. -/
theorem cycle_eq_finsum_properPushforward_opensRestrict (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (h : IsClopenDecomposition U) [∀ i, IsProper (U i).ι] (k : ℤ)
    (c : CycleGroup C f k) (x : X) :
    c.1 x = ∑ᶠ i : I,
      (properPushforward C ((U i).ι ≫ f) f (U i).ι rfl k
        (cycleGroupOpensRestrict C f (U i) k c)).1 x := by
  have hvanish (i : I) (hi : i ≠ h.index x) :
      (properPushforward C ((U i).ι ≫ f) f (U i).ι rfl k
        (cycleGroupOpensRestrict C f (U i) k c)).1 x = 0 :=
    properPushforward_opensRestrict_apply_of_disjoint C f (U i) (U (h.index x))
      (h.disjoint _ _ hi) k c ⟨x, h.mem_index x⟩
  rw [finsum_eq_single _ (h.index x) hvanish]
  exact (properPushforward_opensRestrict_apply_self C f (U (h.index x)) k c
    ⟨x, h.mem_index x⟩).symm

/-! ### The decomposition of rational equivalence -/

/-- **The reverse half of `Stacks.Chow.RationalEquivalenceDecomposes`.** A cycle whose restriction
to every piece of a decomposition into open and closed subschemes is rationally equivalent to zero
is itself rationally equivalent to zero.

This carries no hypothesis. The inclusions of the pieces are closed immersions with locally finite
ranges, and the cycle is the locally finite sum of the pushforwards of its restrictions, so this is
`Stacks.Chow.rationallyEquivalentToZero_finsum_of_isClosedImmersion` at those inclusions. Together
with `Stacks.Chow.rationalEquivalenceDecomposes_mp` it gives
`Stacks.Chow.rationalEquivalenceDecomposes_of_flatPullbackFactors`. -/
theorem rationalEquivalenceDecomposes_mpr (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (h : IsClopenDecomposition U) (k : ℤ) {c : CycleGroup C f k}
    (hc : ∀ i, cycleGroupClopenEquiv C f h k c i ∈ rationalEquivalences C ((U i).ι ≫ f) k) :
    c ∈ rationalEquivalences C f k := by
  have : ∀ i, IsProper (U i).ι := h.isProper_ι
  have : ∀ i, IsClosedImmersion (U i).ι := h.isClosedImmersion_ι
  exact rationallyEquivalentToZero_finsum_of_isClosedImmersion C f k (fun i ↦ (U i).ι)
    h.locallyFinite_range_ι (fun i ↦ cycleGroupOpensRestrict C f (U i) k c) hc c
    (cycle_eq_finsum_properPushforward_opensRestrict C f h k c)

/-- **Rational equivalence decomposes along a decomposition into open and closed subschemes**,
granted Stacks 02S1 at the piece inclusions.

This discharges `Stacks.Chow.RationalEquivalenceDecomposes`, and hence — through
`Stacks.Chow.chowGroupClopenEquiv` — the identity `CH_k(X) = ∏_i CH_k(X_i)` that the proofs of
Stacks 0FDZ and Stacks 02UC use without comment. Only the forward half needs a hypothesis; the
reverse half is `Stacks.Chow.rationalEquivalenceDecomposes_mpr`, which needs none. -/
theorem rationalEquivalenceDecomposes_of_flatPullbackFactors (C : ChowSituation.{u})
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (h : IsClopenDecomposition U) (k : ℤ)
    (hfac : ∀ i, FlatPullbackFactorsThroughRationalEquivalence C ((U i).ι ≫ f) f (U i).ι rfl 0
      (relativeDimension_opensι (U i)) k) :
    RationalEquivalenceDecomposes C f h k := fun _ ↦
  ⟨fun hc i ↦ rationalEquivalenceDecomposes_mp C f h k hfac hc i,
    fun hc ↦ rationalEquivalenceDecomposes_mpr C f h k hc⟩

end Stacks.Chow

end
