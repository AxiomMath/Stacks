module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BoundedAbove
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Interface
public import StacksFrontier.Algebra.Homology.DerivedCategory.UniformUpperBounds
import StacksCore.Tactic.StacksAttribute

/-!
# Right t-exactness of a derived tensor product datum on a ringed site

Let `(C, O)` be a ringed site and `T` a derived tensor product on `D(O)` in the sense of
`Stacks.SheafOfModules.DerivedTensorProduct`. If the cohomology of `K` vanishes above `a` and
that of `L` vanishes above `b`, then the cohomology of `K ⊗^L_O L` vanishes above `a + b`.

## Main definitions

* `Stacks.SheafOfModules.DerivedTensorProduct.toRingedSiteDerivedTensorProduct`: a derived
  tensor product datum read as one over the structure sheaf alone.

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct.isLE_tensor`: right t-exactness, in the aisle
  spelling.
* `Stacks.SheafOfModules.DerivedTensorProduct.isBoundedAboveBy_tensor`: the same, in the
  cohomology-vanishing spelling.

## Implementation notes

Right t-exactness is proved in `Stacks.DerivedTensor.RingedSite.isLE_derivedTensorProduct`, for
the derived tensor product datum of `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct`,
which is indexed by the structure sheaf rather than by the ringed site and whose K-flatness
hypotheses are spelled `Stacks.SheafOfModules.KFlat.KFlat` rather than
`Stacks.SheafOfModules.IsKFlat`. The two spellings of K-flatness are the same abbreviation, so
the two structures have definitionally equal fields and
`toRingedSiteDerivedTensorProduct` copies them across; that is all that is needed to make the
result available in the interface the Tor-amplitude development is stated against.

The universes are all equal, as they are for right t-exactness itself; the derived category's
own hom universe stays independent.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u d

namespace Stacks.SheafOfModules.DerivedTensorProduct

variable {X : RingedSite.{u, u, u}}
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} X)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, u, u} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- A derived tensor product on `D(O)` read as a derived tensor product over the structure
sheaf of the ringed site. The two packagings differ only in which of two equal abbreviations
spells K-flatness, so every field is carried across unchanged. -/
def toRingedSiteDerivedTensorProduct (T : DerivedTensorProduct.{u, u, u, d} X) :
    Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.{d, u} X.O where
  tensor := T.tensor
  comparison := T.comparison
  comparison_naturality := T.comparison_naturality
  comparisonRight := T.comparisonRight
  comparisonRight_naturality := T.comparisonRight_naturality
  comparisonRight_eq_comparison := T.comparisonRight_eq_comparison
  comparisonLeft := T.comparisonLeft
  comparisonLeft_naturality := T.comparisonLeft_naturality
  comparisonLeft_eq_comparison := T.comparisonLeft_eq_comparison
  toTensor := T.toTensor
  toTensor_naturality := T.toTensor_naturality
  toTensor_eq_comparisonRight := T.toTensor_eq_comparisonRight
  toTensor_eq_comparisonLeft := T.toTensor_eq_comparisonLeft
  commShift₂ := T.commShift₂
  exact_left := T.exact_left
  exact_right := T.exact_right

/-- **The derived tensor product is right t-exact in both variables**: the derived tensor
product of an object of `D^{≤ a}(O)` with an object of `D^{≤ b}(O)` lies in
`D^{≤ a + b}(O)`. -/
theorem isLE_tensor (T : DerivedTensorProduct.{u, u, u, d} X)
    (K L : RingedSite.DerivedModules.{u, u, u, d} X) (a b : ℤ) [K.IsLE a] [L.IsLE b] :
    ((T.tensor.obj K).obj L).IsLE (a + b) :=
  Stacks.DerivedTensor.RingedSite.isLE_derivedTensorProduct X.O
    (toRingedSiteDerivedTensorProduct T) K L a b

/-- **An upper cohomological bound on each factor bounds the derived tensor product**, with the
two bounds added. -/
@[sga "6 I 2.16" "special case",
  sga "6 III 1.11" "(a), special case",
  sga "6 III 1.8" "special case"]
theorem isBoundedAboveBy_tensor (T : DerivedTensorProduct.{u, u, u, d} X)
    {K L : RingedSite.DerivedModules.{u, u, u, d} X} {a b : ℤ}
    (hK : Stacks.DerivedCategory.IsBoundedAboveBy K a)
    (hL : Stacks.DerivedCategory.IsBoundedAboveBy L b) :
    Stacks.DerivedCategory.IsBoundedAboveBy ((T.tensor.obj K).obj L) (a + b) := by
  rw [Stacks.DerivedCategory.isBoundedAboveBy_iff_isLE] at hK hL ⊢
  have := hK
  have := hL
  exact isLE_tensor T K L a b

end Stacks.SheafOfModules.DerivedTensorProduct

end
