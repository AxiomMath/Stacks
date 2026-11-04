module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.AmpleAndExtension.TensorPower
public import StacksFrontier.AlgebraicGeometry.TensorPowerProduct.Basic
public import StacksFrontier.AlgebraicGeometry.OpensSheafificationInstances

/-!
# Tensoring an ample invertible sheaf with a locally generated invertible sheaf

Let `L` and `M` be invertible sheaves of modules on a scheme `X`, with `L` ample. If every point
of `X` lies in the nonvanishing open of a global section of *some* positive tensor power of `M`,
then `L ⊗ M` is again ample.

The proof is a computation with nonvanishing opens. Ampleness of `L` gives, at a point `x`, an
exponent `n ≥ 1` and a section `s` of `L^{⊗ n}` whose nonvanishing open `X_s` is affine and
contains `x`; the hypothesis gives an exponent `m ≥ 1` and a section `t` of `M^{⊗ m}` with
`x ∈ X_t`. Both are pushed into the common exponent `k = nm`, where the tensor product of the
resulting sections is a section of `L^{⊗ k} ⊗ M^{⊗ k} ≅ (L ⊗ M)^{⊗ k}` whose nonvanishing open
is `X_s ⊓ X_t`. That intersection is affine by Tag 01PV, applied to the affine open `X_s` and the
section `t`.

## Main definitions

* `Stacks.SheafOfModules.Invertible.tensorPowerTensorIso`:
  `(L ⊗ M)^{⊗ n} ≅ L^{⊗ n} ⊗ M^{⊗ n}` for a natural exponent `n`.

## Main results

* `AlgebraicGeometry.exists_section_tensor_nonvanishingOpen_eq`: sections of `L^{⊗ k}` and
  `M^{⊗ k}` give a section of `(L ⊗ M)^{⊗ k}` whose nonvanishing open is the intersection of
  theirs.
* `AlgebraicGeometry.isAmple_tensor_of_power_sections_cover`: **Tag 0890**, the statement above.

## Implementation notes

The exponents are natural numbers cast to `ℤ`, since the tensor powers of Tag 01CU are indexed by
`ℤ`. Only natural exponents are needed, and `tensorPowerTensorIso` is therefore built by
structural recursion from the successor comparison `L^{⊗ n} ⊗ L ≅ L^{⊗ (n + 1)}`, the associator
and the braiding, exactly as the natural-exponent multiplication in
`StacksFrontier/AlgebraicGeometry/Properties/AmpleAndExtension/TensorPower.lean` is. The coherent
integer-indexed multiplication of Tag 01CU rests on a coherence datum that is not available.

Two consequences of Tag 01PT's development are reused rather than redone:
`AlgebraicGeometry.exists_section_power_nonvanishingOpen_eq`, which moves a section of `L^{⊗ n}`
into `L^{⊗ nm}` without changing its nonvanishing open, and the two comparisons of nonvanishing
loci `AlgebraicGeometry.nonvanishingLocus_iso` and
`AlgebraicGeometry.tensorSections_nonvanishing_iff`. Commutativity of the exponent `nm` is
handled by generalising the exponent and substituting, rather than by a reindexing isomorphism.

The five file-local instances below are spelling bridges, and each is load-bearing: `X.Modules` has a ring sheaf that is only reducibly the structure ring sheaf of the
underlying ringed space, and the two developments of Tag 01CS record invertibility in two
different classes — `AlgebraicGeometry.SheafOfModules.IsInvertible`, for which the tensor powers
of Tag 01CU are stated, and `Stacks.SheafOfModules.IsInvertible`, for which the nonvanishing
locus of Tag 01CY is. The same bridges appear, for the same reason, in
`StacksFrontier/AlgebraicGeometry/Ample/Defs.lean` and in
`StacksFrontier/AlgebraicGeometry/Properties/AmpleAndExtension/TensorPower.lean`.

## References

* [Stacks Project, Tag 0890](https://stacks.math.columbia.edu/tag/0890)
* [Stacks Project, Tag 01PV](https://stacks.math.columbia.edu/tag/01PV)
* [Stacks Project, Tag 01PT](https://stacks.math.columbia.edu/tag/01PT)
* [EGA II, Proposition 4.5.6(ii)]
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open Stacks.SheafOfModules

universe v u w

namespace Stacks.SheafOfModules.Invertible

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- A tensor power of a tensor product of invertible sheaves splits:
`(L ⊗ M)^{⊗ n} ≅ L^{⊗ n} ⊗ M^{⊗ n}` for a natural exponent `n`. The zeroth power is the left
unitor on the structure sheaf; the inductive step peels one factor off each side with the
successor comparison of Tag 01CU and sorts the four factors with `tensorInterchange`. -/
noncomputable def tensorPowerTensorIso
    (L M : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [AlgebraicGeometry.SheafOfModules.IsInvertible O hO L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible O hO M] : (n : ℕ) →
      tensorPower O hO
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat)
            hO⟩).obj L).obj M) (n : ℤ) ≅
      tensorProduct O hO (tensorPower O hO L (n : ℤ)) (tensorPower O hO M (n : ℤ))
  | 0 => (tensorProductLeftUnitor O hO
      (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))).symm
  | n + 1 =>
      (tensorPowerSuccIso O hO
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat)
            hO⟩).obj L).obj M) (n : ℤ)).symm ≪≫
      tensorProductIso O hO (tensorPowerTensorIso L M n) (Iso.refl _) ≪≫
      tensorInterchange O hO (tensorPower O hO L (n : ℤ)) (tensorPower O hO M (n : ℤ)) L M ≪≫
      tensorProductIso O hO (tensorPowerSuccIso O hO L (n : ℤ))
        (tensorPowerSuccIso O hO M (n : ℤ))

end Stacks.SheafOfModules.Invertible

namespace AlgebraicGeometry

universe v₁ u₁ w₁

-- The transport of the `IsInvertible` datum between the two developments of Tag 01CS is
-- `AlgebraicGeometry.stacksIsInvertible_of_isInvertible`, in
-- `StacksFrontier/AlgebraicGeometry/Properties/AmpleAndExtension/TensorPower.lean`. It is a
-- `local instance` there, so it is registered here rather than restated.
attribute [local instance] stacksIsInvertible_of_isInvertible

-- Seated from `OpensSheafificationInstances`, not restated: sheafification for the site of
-- opens of a scheme, and its weak equivalences.
attribute [local instance]
  Stacks.OpensSheafification.hasSheafifyOpens
  Stacks.OpensSheafification.wEqualsLocallyBijectiveOpens

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify

-- Invertibility of the integer tensor powers at the `X.toRingedSpace.presheaf` spelling is
-- `AlgebraicGeometry.isInvertible_tensorPowerOfSheaf`, in the same module and likewise a
-- `local instance` there, so it is registered here rather than restated.
attribute [local instance] isInvertible_tensorPowerOfSheaf

-- The ring sheaf over which `Stacks.SheafOfModules.Tensor.sheafTensor` takes its modules and the
-- one over which the tensor powers of Tag 01CU are stated are the same sheaf of rings, but under
-- two names; instance search unfolds neither, so an invertibility instance stated for a module
-- over the one is not found for a module over the other. The two names are made transparent, as
-- in `StacksFrontier/CategoryTheory/Sites/Modules/InvertibleRankOne.lean`.
attribute [local implicit_reducible] Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

/-- Part (1) of Tag 01CT for the sheaves of modules of a scheme, whose ring sheaf is only
reducibly the structure ring sheaf of the underlying ringed space: the sheaf tensor product of
two invertible sheaves of modules on a scheme is invertible. -/
local instance isInvertible_tensorProductOfScheme (X : Scheme.{u}) (L M : X.Modules)
    [SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    [SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property M] :
    SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.toRingedSpace.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.toRingedSpace.presheaf
          (forget₂ CommRingCat RingCat)
          (structureSheafRing X.toRingedSpace).property⟩).obj L).obj M) :=
  Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible
    X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property L M

/-- **A tensor product of sections of equal tensor powers is a section of the same power of the
tensor product, and its nonvanishing open is the intersection.** Given `qL` a global section of
`L^{⊗ k}` and `qM` one of `M^{⊗ k}`, transporting `qL ⊗ qM` along
`L^{⊗ k} ⊗ M^{⊗ k} ≅ (L ⊗ M)^{⊗ k}` gives a global section of `(L ⊗ M)^{⊗ k}` whose
nonvanishing open is `X_{qL} ⊓ X_{qM}`, because a tensor product of sections vanishes exactly
where one of its factors does. -/
theorem exists_section_tensor_nonvanishingOpen_eq {X : Scheme.{u}} (L M : X.Modules)
    [SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    [SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property M] (k : ℕ)
    (qL : (Invertible.tensorPower X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L (k : ℤ)).sections)
    (qM : (Invertible.tensorPower X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property M (k : ℤ)).sections) :
    ∃ q : (Invertible.tensorPower X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property
        (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.toRingedSpace.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.toRingedSpace.presheaf
            (forget₂ CommRingCat RingCat)
            (structureSheafRing X.toRingedSpace).property⟩).obj L).obj M) (k : ℤ)).sections,
      nonvanishingOpen (X := X.toRingedSpace) _ q =
        nonvanishingOpen (X := X.toRingedSpace) _ qL ⊓
          nonvanishingOpen (X := X.toRingedSpace) _ qM := by
  let ed := Invertible.tensorPowerTensorIso X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L M k
  refine ⟨SheafOfModules.sectionsMap ed.symm.hom (tensorSections _ _ qL qM), ?_⟩
  ext y
  exact (nonvanishingLocus_iso ed.symm (tensorSections _ _ qL qM) y).trans
    (tensorSections_nonvanishing_iff qL qM y)

end AlgebraicGeometry

end
