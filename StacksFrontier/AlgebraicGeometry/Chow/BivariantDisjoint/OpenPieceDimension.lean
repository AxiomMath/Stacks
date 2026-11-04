module

public import StacksFrontier.AlgebraicGeometry.Chow.Vocabulary
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.DimensionFormula

/-!
# Delta-dimension is insensitive to passing to an open subscheme

Let `f : X ⟶ S` be locally of finite type over a base carrying a dimension function `δ`, and
let `U ⊆ X` be an open subscheme. The relative dimension function of Stacks 02JW is computed
pointwise from the dimension function of the base and the transcendence degree of the residue
field extension, and an open immersion changes neither: a point of `U` has the same image in
`S` as the corresponding point of `X`, and the residue field map of an open immersion is an
isomorphism. Consequently the delta-dimension of an irreducible closed subset of `U` equals the
delta-dimension of its closure in `X`.

This identification is the first step of the decomposition `A_k(X) = ∏_i A_k(X_i)` along a
decomposition of `X` into open and closed subschemes — the step the proof of Stacks 0FDZ calls
"immediate from the definitions". Before cycles on `X` can be matched with families of cycles on
the pieces, the two notions of delta-dimension have to be identified.

## Main results

* `Stacks.Chow.relativeDimension_opensι_comp` — the relative dimension of a point of an open
  subscheme, computed there, is its relative dimension computed in the ambient scheme.
* `Stacks.Chow.deltaDimension_opensι_comp` — the delta-dimension of an irreducible closed subset
  of an open subscheme is the delta-dimension of its closure in the ambient scheme.

## References

* [Stacks Project, Tag 02JW](https://stacks.math.columbia.edu/tag/02JW)
* [Stacks Project, Tag 02QP](https://stacks.math.columbia.edu/tag/02QP)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Chow

/-- The relative dimension of Stacks 02JW does not see an open subscheme: for `x` a point of an
open `U ⊆ X`, the relative dimension of `x` for `U ⟶ X ⟶ S` is the relative dimension of the
corresponding point of `X` for `X ⟶ S`.

The base contributions agree because the two points have the same image in `S`, and the two
transcendence degrees agree because the residue field map of the open immersion `U.ι` is an
isomorphism compatible with the residue field of the image point in `S`. -/
theorem relativeDimension_opensι_comp {X S : Scheme.{u}} (δ : DimensionFunction S) (f : X ⟶ S)
    (U : X.Opens) (x : (U : Scheme.{u})) :
    relativeDimension δ (U.ι ≫ f) x = relativeDimension δ f (U.ι.base x) := by
  unfold relativeDimension
  congr 1
  refine congrArg (fun c : Cardinal.{u} => ((Cardinal.toNat c : ℕ) : ℤ)) ?_
  refine @Algebra.trdeg_eq_of_ringEquiv _ _ _ _ _ _ _ _ (_) (_) (RingEquiv.refl _)
    ((asIso (U.ι.residueFieldMap x)).commRingCatIsoToRingEquiv.symm) fun a => ?_
  rw [RingEquiv.symm_apply_eq]
  simp only [RingHom.algebraMap_toAlgebra, Scheme.residueFieldMap_comp]
  rfl

/-- The closure in `X` of the image of an irreducible closed subset of an open subscheme
`U ⊆ X`. -/
def opensIrreducibleClosure {X : Scheme.{u}} (U : X.Opens)
    (Z : IrreducibleCloseds (U : Scheme.{u})) : IrreducibleCloseds X where
  carrier := closure (U.ι.base '' (Z : Set (U : Scheme.{u})))
  isIrreducible' := (Z.isIrreducible.image _ U.ι.continuous.continuousOn).closure
  isClosed' := isClosed_closure

/-- The generic point of `Z` maps to the generic point of its closure in the ambient scheme. -/
theorem isGenericPoint_opensIrreducibleClosure {X : Scheme.{u}} (U : X.Opens)
    (Z : IrreducibleCloseds (U : Scheme.{u})) :
    IsGenericPoint (U.ι.base Z.isIrreducible.genericPoint)
      (opensIrreducibleClosure U Z : Set X) := by
  have hZ : closure ({Z.isIrreducible.genericPoint} : Set (U : Scheme.{u})) =
      (Z : Set (U : Scheme.{u})) :=
    Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed
  have hmem : Z.isIrreducible.genericPoint ∈ (Z : Set (U : Scheme.{u})) :=
    hZ.subset (subset_closure rfl)
  have himage := image_closure_subset_closure_image (f := U.ι.base) U.ι.continuous
    (s := {Z.isIrreducible.genericPoint})
  rw [hZ, Set.image_singleton] at himage
  exact subset_antisymm (closure_mono (Set.singleton_subset_iff.2 ⟨_, hmem, rfl⟩))
    (closure_minimal himage isClosed_closure)

/-- The delta-dimension of Stacks 02QP does not see an open subscheme: for `Z` an irreducible
closed subset of an open `U ⊆ X`, the delta-dimension of `Z` computed on `U` is the
delta-dimension of the closure of the image of `Z` computed on `X`. -/
theorem deltaDimension_opensι_comp (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (U : X.Opens) (Z : IrreducibleCloseds (U : Scheme.{u})) :
    deltaDimension C (U.ι ≫ f) Z = deltaDimension C f (opensIrreducibleClosure U Z) := by
  rw [deltaDimension_eq_of_isGenericPoint C f (opensIrreducibleClosure U Z) _
      (isGenericPoint_opensIrreducibleClosure U Z),
    deltaDimension, relativeDimension_opensι_comp]

end Stacks.Chow

end
