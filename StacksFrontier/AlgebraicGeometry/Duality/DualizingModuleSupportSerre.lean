module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.Depth
public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModuleOfComplex
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian
public import StacksFrontier.RingTheory.Dualizing.CanonicalModuleDepth
public import StacksFrontier.Topology.Dimension.DimensionFunctionConnected
public import StacksFrontier.Topology.Sheaves.Modules.SupportSection

/-!
# Support and Serre's condition for the dualizing module of a dualizing complex

Let `X` be a connected Noetherian scheme with a dualizing complex `K` and let `ω` be the
associated dualizing module, the cohomology sheaf of `K` in the leftmost degree in which `K` has
nonvanishing cohomology (`Stacks.Duality.IsDualizingModuleOf`). Two further properties of `ω`
are recorded here: its support is the union of the irreducible components of `X` of maximal
dimension, measured by any dimension function on `X`; and `ω` satisfies Serre's condition `(S₂)`.

A component of `X` is named by the point of `TopologicalSpace.genericPoints X` whose closure it
is, and it has maximal dimension for the dimension function `δ` when `δ` takes its largest value
at that generic point.

## Main results

* `Stacks.Duality.IsDualizingModuleOf.sheafHasPropertySk_two` — **[Stacks, Tag 0AWK]** `ω`
  satisfies Serre's condition `(S₂)`.

## Implementation notes

The support clause is stated for an arbitrary dimension function `δ`, as in the source, and takes
as a hypothesis the same description for one dimension function `ε`: the content of the step is
that the description does not depend on which dimension function is used. That independence is
`TopologicalSpace.DimensionFunction.maximalComponents_eq`, hence ultimately
[Stacks, Tag 02IB] — two dimension functions on a locally Noetherian sober space differ by a
locally constant function, which on a connected space is a constant, so they order the generic
points in the same way. The source takes `ε` to be the dimension function attached to `K`, whose
value at `x` is the shift normalizing the derived stalk of `K` at `x`
(`Stacks.Duality.associatedShiftFunction`); that this function is a dimension function is
[Stacks, Tag 0AWF]. That tag's dimension-function clause is proved, as
`Stacks.Duality.exists_isDualizingShiftFunction` together with
`Stacks.Duality.exists_dimensionFunction_of_isDualizingShiftFunction`, but for the `δ` read off
the dualizing models over affine opens rather than off the derived stalk, so it does not apply
to `Stacks.Duality.associatedShiftFunction`; the hypothesis `hε` is the resulting statement of
the support clause for the latter.

Serre's condition is `AlgebraicGeometry.SheafHasPropertySk` of [Stacks, Tag 0341], a pointwise
condition on the stalks over the local rings of `X`. The local input is the hypothesis `hstalk`:
at every point the stalk of `ω` either vanishes or is the canonical module of the local ring
`𝒪_{X,x}`, that is, the cohomology of a normalized dualizing complex over `𝒪_{X,x}` in degree
`-dim 𝒪_{X,x}`. Given it the conclusion is the depth bound
`Dualizing.min_two_le_depth_canonicalModule` for the canonical module of a Noetherian local
ring, together with the bound of the dimension of the support of a module by the dimension of the
ring: a module with `depth ≥ min(dim 𝒪_{X,x}, 2)` and support of dimension at most
`dim 𝒪_{X,x}` satisfies the inequality defining `(S₂)` at that point, and a vanishing stalk
satisfies it because the dimension of its support is `⊥`.

`D(𝒪_X)` is an instance argument, inherited from `Stacks.Duality.IsDualizingModuleOf`, so no
model of the derived category of `X.Modules` is pinned. The derived category of
`ModuleCat 𝒪_{X,x}` is at `HasDerivedCategory.standard`, forced by
`Dualizing.IsNormalizedDualizingComplex`, which bakes that model into its own type.

## References

* [Stacks Project, Tag 0AWK](https://stacks.math.columbia.edu/tag/0AWK)
* [Stacks Project, Tag 0AWE](https://stacks.math.columbia.edu/tag/0AWE)
* [Stacks Project, Tag 0AWF](https://stacks.math.columbia.edu/tag/0AWF)
* [Stacks Project, Tag 02IB](https://stacks.math.columbia.edu/tag/02IB)
* [Stacks Project, Tag 0341](https://stacks.math.columbia.edu/tag/0341)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

attribute [local instance] HasDerivedCategory.standard

universe u w

namespace Stacks.Duality

/-- **Stacks Project, Tag 0AWK.** The dualizing module of a dualizing complex on a connected
Noetherian scheme satisfies Serre's condition `(S₂)`: at a point where its stalk is the canonical
module of the local ring the depth bound for canonical modules applies, and at a point where the
stalk vanishes the condition is empty. -/
@[stacks 0AWK "Serre's condition (S₂), granted that at every point the stalk either vanishes or \
is the canonical module of the local ring"]
public theorem IsDualizingModuleOf.sheafHasPropertySk_two {X : Scheme.{u}} [IsNoetherian X]
    [ConnectedSpace X] [HasDerivedCategory.{w} X.Modules] {ω : X.Modules}
    {K : DerivedCategory X.Modules} {n : ℤ} (h : IsDualizingModuleOf ω K n)
    (hstalk : ∀ x : X,
      Subsingleton ↑(TopCat.Presheaf.stalk
          (SheafOfModules.val
            (R := structureSheafRing
              X.toRingedSpace)
            ((DerivedCategory.homologyFunctor X.Modules n).obj K)).presheaf x) ∨
        ∃ (L : DerivedCategory (ModuleCat.{u} (X.presheaf.stalk x))) (d : ℕ),
          _root_.Dualizing.IsNormalizedDualizingComplex.{u, u} L ∧
            ringKrullDim (X.presheaf.stalk x) = (d : WithBot ℕ∞) ∧
              Nonempty (↑(TopCat.Presheaf.stalk
                  (SheafOfModules.val
                    (R := structureSheafRing
                      X.toRingedSpace)
                    ((DerivedCategory.homologyFunctor X.Modules n).obj K)).presheaf x) ≃ₗ[
                  X.presheaf.stalk x]
                ↑((DerivedCategory.homologyFunctor (ModuleCat.{u} (X.presheaf.stalk x))
                  (-(d : ℤ))).obj L))) :
    SheafHasPropertySk X ω 2 := by
  rw [h.eq_homology]
  intro x
  rcases hstalk x with hzero | ⟨L, d, hL, hd, ⟨e⟩⟩
  · have := hzero
    rw [Module.supportDim_eq_bot_of_subsingleton]
    exact (min_le_right _ _).trans bot_le
  · have hdepth := _root_.Dualizing.min_two_le_depth_canonicalModule d L hL hd
    rw [← Module.depth_eq_depth_of_linearEquiv _ e] at hdepth
    have hsupp := (Module.supportDim_eq_of_equiv e).trans_le
      ((Module.supportDim_le_ringKrullDim _ _).trans (le_of_eq hd))
    rcases le_total (d : ℕ∞) 2 with hle | hle
    · refine (min_le_right _ _).trans (hsupp.trans ?_)
      rw [min_eq_left hle] at hdepth
      exact_mod_cast hdepth
    · refine (min_le_left _ _).trans ?_
      rw [min_eq_right hle] at hdepth
      exact WithBot.coe_le_coe.mpr hdepth

end Stacks.Duality

end
