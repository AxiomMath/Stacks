module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Shift

/-!
# Derived completeness is stable under the shift

Let `(𝒞, 𝒪)` be a ringed site and `ℐ ⊂ 𝒪` a sheaf of ideals. The predicate
`AlgebraicGeometry.RingedSite.IsDerivedComplete` of [Stacks, Tag 0999] asks, for every object `U`
of `𝒞` and every section `f ∈ ℐ(U)`, that the Milnor difference `1 - f·shift` be invertible on
the countable power of the restriction `K|_U`. This file proves that the predicate is unchanged by
shifting `K` in the derived category, and records that as
`CategoryTheory.ObjectProperty.IsStableUnderShift ℤ`.

That typeclass is what Mathlib's
`CategoryTheory.ObjectProperty.leftOrthogonal` needs in order to be stable under the shift as
well, and through it to be a triangulated subcategory: the objects admitting no nonzero map to a
derived-complete object form a triangulated subcategory of `D(𝒪)` exactly because the
derived-complete objects are shift-stable.

## Main results

* `AlgebraicGeometry.RingedSite.isDerivedComplete_shiftFunctor_obj`: `K^∧`-completeness
  transfers to every shift `K⟦n⟧`.
* `AlgebraicGeometry.RingedSite.instIsStableUnderShiftIsDerivedComplete`: the same as the
  `IsStableUnderShift ℤ` instance.
* `AlgebraicGeometry.RingedSite.instIsClosedUnderIsomorphismsIsDerivedComplete`: derived
  completeness is closed under isomorphism, as an instance on the property of objects.

## Implementation notes

The proof is `StacksFrontier.Homology.DerivedComplete`'s transport of the Milnor condition along an
additive linear functor preserving the countable product, `isDerivedCompleteAt_map`, applied to
the shift functor of the derived category of the slice site: it is an equivalence, hence
preserves the product, it is additive, and it is linear over the centre of the abelian category
by `Mathlib.Algebra.Homology.DerivedCategory.Linear`. What has to be matched up first is the
restriction to the slice: `(K⟦n⟧)|_U` is `(K|_U)⟦n⟧` because the restriction is exact, so the
functor it induces on derived categories commutes with the shift
(`CategoryTheory.Functor.mapDerivedCategory.CommShift`), and then
`isDerivedCompleteAt_iff_of_iso` moves the condition across that identification.

The exactness data and the countable product that the predicate carries in its existential
clauses are reused verbatim from the hypothesis: shifting changes none of them, they are
properties of the slice restriction alone.

## References

* [Stacks Project, Tag 0999](https://stacks.math.columbia.edu/tag/0999)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped IsMulCommutative

attribute [local instance] HasDerivedCategory.standard

universe u v r w

namespace AlgebraicGeometry.RingedSite

/-- **Derived completeness along a sheaf of ideals is stable under the shift.** If `K ∈ D(𝒪)` is
derived complete along `ℐ` then so is `K⟦n⟧`, for every `n : ℤ`.

On each slice the Milnor difference `1 - f·shift` is carried from the countable power of `K|_U`
to that of `(K|_U)⟦n⟧` by the shift functor, which is additive, linear over the centre and an
equivalence, hence preserves the countable product; and `(K⟦n⟧)|_U` is `(K|_U)⟦n⟧` because the
restriction to the slice is exact. -/
theorem isDerivedComplete_shiftFunctor_obj (X : RingedSite.{u, v, r})
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    {K : DerivedCategory
      (SheafOfModules.{max u v w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))} (n : ℤ)
    (hK : IsDerivedComplete.{u, v, r, w} X I K) :
    IsDerivedComplete.{u, v, r, w} X I (K⟦n⟧) := by
  intro U f hf
  let R := ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U
  let A := SheafOfModules.{max u v w} R
  let : Linear (CatCenter A) A := Linear.ofRingMorphism (RingHom.id (CatCenter A))
  let : ∀ V : (Over U)ᵒᵖ, IsMulCommutative (R.obj.obj V) := fun V ↦ by
    show IsMulCommutative (X.O.obj.obj (Opposite.op V.unop.left))
    infer_instance
  let F := SheafOfModules.overFunctor.{max u v w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U
  obtain ⟨hAdd, hLim, hColim, hProducts, hComplete⟩ := hK U f hf
  let : F.Additive := hAdd
  let : PreservesFiniteLimits F := hLim
  let : PreservesFiniteColimits F := hColim
  let : HasProductsOfShape ℕ (DerivedCategory A) := hProducts
  refine ⟨hAdd, hLim, hColim, hProducts, ?_⟩
  refine (isDerivedCompleteAt_iff_of_iso ((F.mapDerivedCategory.commShiftIso n).app K)
    (Stacks.SheafOfModules.terminalSectionToEnd R (Over.mk (𝟙 U)) Over.mkIdTerminal f)).mpr ?_
  exact isDerivedCompleteAt_map (shiftFunctor (DerivedCategory A) n)
    (F.mapDerivedCategory.obj K) _ hComplete

/-- Derived completeness along a sheaf of ideals, as a property of objects of `D(𝒪)` stable under
the shift by `ℤ`. -/
instance (X : RingedSite.{u, v, r})
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) :
    ObjectProperty.IsStableUnderShift (IsDerivedComplete.{u, v, r, w} X I) ℤ where
  isStableUnderShiftBy n := ⟨fun _ hK ↦ isDerivedComplete_shiftFunctor_obj X I n hK⟩

/-- Derived completeness along a sheaf of ideals, as a property of objects of `D(𝒪)` closed
under isomorphism. -/
instance (X : RingedSite.{u, v, r})
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) :
    ObjectProperty.IsClosedUnderIsomorphisms (IsDerivedComplete.{u, v, r, w} X I) where
  of_iso e hK := (isDerivedComplete_iff_of_iso X I e).mp hK

end AlgebraicGeometry.RingedSite

end
