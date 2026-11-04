module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.OnARingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.KFlatInBothVariables
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.LeftKFlatResolutions
public import StacksFrontier.Homology.KFlat.BifunctorToTotalComplex
public import StacksFrontier.Homology.KFlat.BifunctorCommShiftTwoInstances
import StacksCore.Tactic.StacksAttribute

/-!
# The derived tensor product on a ringed site exists

Stacks Tag 06YU: the derived tensor product of sheaves of modules on a ringed site, as a
bifunctor on the unbounded derived category, with its comparisons with the ordinary total
tensor product on K-flat complexes, its canonical map to that total tensor product for
arbitrary complexes, and exactness in each variable.

## Main results

* `Stacks.DerivedTensor.RingedSite.exists_derivedTensorProduct`: **the derived tensor product
  exists**, i.e.
  `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct` is inhabited.
* `Stacks.DerivedTensor.RingedSite.derivedTensorProductConstruction`: the construction, with
  the two-variable shift structure of the derived bifunctor.
* `Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct`: the derived tensor product,
  the construction made opaque with `irreducible_def` (defining equation
  `canonicalDerivedTensorProduct_def`, restated as `canonicalDerivedTensorProduct_eq`).
* `Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor`: its bifunctor, for clients.

## Implementation notes

The bifunctor is `CochainComplex.KFlatBifunctor.derivedBifunctor` at the tensor bifunctor
`Stacks.SheafOfModules.Tensor.sheafTensor`, i.e. the descent of `Tot(- ⊗_O -)` along the two K-flat
localizations of `Tag06YUPieces`. Instance search finds the two localizations it needs, from the
K-flat resolutions of Tag 06YS registered as
`Stacks.DerivedTensor.RingedSite.kFlatLocalizer_hasLeftResolutions` and
`Stacks.DerivedTensor.RingedSite.kFlatLocalizerLeft_hasLeftResolutions`. The resolutions that
`CochainComplex.KFlatBifunctor.toTensor` takes explicitly are
`Stacks.DerivedTensor.RingedSite.exists_kFlat_quasiIso`, stated at the narrowed universes of
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct`. That structure is what pins all four
universes of the source statement to a single `u` and asks `SmallCategory`, as recorded in
`Tag06YU`. **The statement is therefore narrower than the source in exactly one respect**: the
site's object, hom, ring and module universes are independent in Tag 06YU itself and are all `u`
here, and the site carries `SmallCategory`. The narrowing is inherited from that structure,
which was written against the tagged
`Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution` at the same universes, and is not
introduced here; the derived category's own hom universe stays independent, as
`HasDerivedCategory.{d}`. The universe-free counterpart of the structure,
`Stacks.SheafOfModules.DerivedTensorProduct`, is constructed by
`Stacks.SheafOfModules.FreeSections.derivedTensorProduct`.

The one design choice worth stating is which of the three comparison fields is taken as
primitive. The *right* one-sided comparison is, and it serves as the two-sided `comparison`
as well — a comparison isomorphism on two K-flat complexes natural in both variables is
exactly what that field asks for, so the two `_eq_comparison` fields on the right-hand side
hold by `rfl`. The *left* comparison is then not a second descent but
`asIso (CochainComplex.KFlatBifunctor.toTensor …)`: the canonical map to the total tensor
product is invertible as soon as the left factor is K-flat
(`isIso_toTensor_of_kFlatLeft`, which is `quasiIso_of_kFlatLeft` and nothing more), and with
that reading its naturality is `toTensor_naturality` and its agreement with the two-sided
comparison is `toTensor_eq_comparisonRight`. So the arithmetic of the statement is: the one
genuinely new construction is `toTensor`, and the six remaining fields follow from
its characterization.

K-flatness in the statement is right-K-flatness, so the left comparison's hypothesis has to be
carried across by `Stacks.DerivedTensor.RingedSite.kFlatLeft_of_kFlat`, the symmetry of `⊗_O`.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u d

namespace Stacks.DerivedTensor.RingedSite

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasDerivedCategory.{d} (Modules R)]
variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R).obj M).Additive]
  [∀ (K L : CochainComplex (Modules R) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)]

open CochainComplex.KFlatBifunctor in
/-- **The construction of the derived tensor product of sheaves of modules on a ringed site**:
the bifunctor is the descent `CochainComplex.KFlatBifunctor.derivedBifunctor` of `Tot(- ⊗_O -)`
along the two K-flat localizations, with its one-sided K-flat comparisons, its canonical map to
the ordinary total tensor product, and the two-variable shift structure obtained by descending
that of total complexes, for which it is exact in each variable. -/
def derivedTensorProductConstruction : DerivedTensorProduct R :=
  have hres := exists_kFlat_quasiIso R
  {
    tensor := derivedBifunctor (Stacks.SheafOfModules.Tensor.sheafTensor R)
    comparison := fun K L _ hL => comparisonRight (Stacks.SheafOfModules.Tensor.sheafTensor R) K L
      hL
    comparison_naturality := fun f g _ _ hL hL' =>
      comparisonRight_naturality_merged (Stacks.SheafOfModules.Tensor.sheafTensor R) f g hL hL'
    comparisonRight := fun K L hL => comparisonRight (Stacks.SheafOfModules.Tensor.sheafTensor R) K
      L hL
    comparisonRight_naturality := fun f g hL hL' =>
      comparisonRight_naturality_merged (Stacks.SheafOfModules.Tensor.sheafTensor R) f g hL hL'
    comparisonRight_eq_comparison := fun _ _ _ _ => rfl
    comparisonLeft := fun K L hK =>
      @asIso _ _ _ _ (toTensor (Stacks.SheafOfModules.Tensor.sheafTensor R) hres K L)
        (isIso_toTensor_of_kFlatLeft (Stacks.SheafOfModules.Tensor.sheafTensor R) hres
          (kFlatLeft_of_kFlat R hK) L)
    comparisonLeft_naturality := fun f g _ _ =>
      toTensor_naturality (Stacks.SheafOfModules.Tensor.sheafTensor R) hres f g
    comparisonLeft_eq_comparison := fun K _ _ hL =>
      Iso.ext (toTensor_eq_comparisonRight (Stacks.SheafOfModules.Tensor.sheafTensor R) hres K hL)
    toTensor := fun K L => toTensor (Stacks.SheafOfModules.Tensor.sheafTensor R) hres K L
    toTensor_naturality := fun f g =>
      toTensor_naturality (Stacks.SheafOfModules.Tensor.sheafTensor R) hres f g
    toTensor_eq_comparisonRight := fun K _ hL =>
      toTensor_eq_comparisonRight (Stacks.SheafOfModules.Tensor.sheafTensor R) hres K hL
    toTensor_eq_comparisonLeft := fun _ _ _ => rfl
    commShift₂ := inferInstance
    exact_left := fun _ => inferInstance
    exact_right := fun _ => inferInstance }

/-- **The derived tensor product of sheaves of modules on a ringed site exists**, with its
canonical natural map to the ordinary total tensor product, its one-sided K-flat comparisons,
and exactness in both variables. -/
@[stacks 06YU "existence and characterization",
  sga "4½ Etat_0 6.2" "existence of ⊗^L",
  sga "4 XVII 4.1.7" "(i)"]
theorem exists_derivedTensorProduct : Nonempty (DerivedTensorProduct R) :=
  ⟨derivedTensorProductConstruction R⟩

/-- The canonical derived tensor product of sheaves of modules on a ringed site, with its
natural map to the ordinary total tensor product, its K-flat comparisons, and exactness in
both variables. It is the construction `derivedTensorProductConstruction R`, made opaque with
`irreducible_def` so that definitional unfolding does not reach the construction;
`canonicalDerivedTensorProduct_def` is the defining equation. -/
@[stacks 06YU "the derived tensor product",
  sga "4½ Etat_0 6.2" "X ⊗^L Y on a site",
  sga "4 XVII 4.1.7" "(i)"]
irreducible_def canonicalDerivedTensorProduct : DerivedTensorProduct R :=
  derivedTensorProductConstruction R

/-- The canonical derived tensor product is the construction `derivedTensorProductConstruction`,
with its shift structure. -/
theorem canonicalDerivedTensorProduct_eq :
    canonicalDerivedTensorProduct R = derivedTensorProductConstruction R :=
  canonicalDerivedTensorProduct_def R

/-- The derived tensor bifunctor on the unbounded derived category of `X`. -/
abbrev derivedTensorProductFunctor := (canonicalDerivedTensorProduct R).tensor

end Stacks.DerivedTensor.RingedSite

end
