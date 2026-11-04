module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TensorSymmetry
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.UnitLeftIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.Defs

/-!
# Tensoring with the structure sheaf in a single degree, on the left, at free universes

Let `(C, O)` be a ringed site and let `T` be a derived tensor product on `D(O)` in the sense of
`Stacks.SheafOfModules.DerivedTensorProduct`. For every object `M` of `D(O)` and every `i : ℤ`

`O[i] ⊗^𝐋_O M ≅ M⟦-i⟧`,

with the structure sheaf in the **left** tensor slot, which is the slot
`Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude` measures. The three site universes
and the derived category's hom universe stay independent.

Together with the shift rule for Tor amplitude this computes the Tor amplitude of the left
factor `O[i]` and, more usefully, the interval in which `O[i] ⊗^𝐋_O M` has Tor amplitude once
`M` has one: the interval of `M` translated by `i`, shrunk or grown with
`Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude.mono`.

## Main definitions

* `Stacks.SheafOfModules.DerivedTensorProduct.unitLeftIso`: the unit constraint on the left,
  `O[0] ⊗^𝐋_O M ≅ M`.
* `Stacks.SheafOfModules.DerivedTensorProduct.shiftedUnitLeftIso`: `O[i] ⊗^𝐋_O M ≅ M⟦-i⟧`.

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_shift`: an object of Tor
  amplitude in `[a, b]` has translate of Tor amplitude in `[a - n, b - n]`.
* `Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_singleUnit`: the structure sheaf
  placed in degree `i` has Tor amplitude in `[i, i]`.
* `Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_tensor_singleUnit`: **the interval
  bookkeeping.** If `M` has Tor amplitude in `[a, b]` then `O[i] ⊗^𝐋_O M` has Tor amplitude in
  any interval `[c, d]` with `c ≤ a + i` and `b + i ≤ d`.

## Implementation notes

*Why a left unit constraint is built here rather than reused.*
`Stacks.SheafOfModules.DerivedTensorProduct.unitIso` is the unit constraint on the **right**,
`M ⊗^𝐋_O O[0] ≅ M`, and is the only unit law this interface carries; the left one,
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.leftUnitIso`, belongs to the other
derived-tensor interface and is stated on a ringed site with all three universes equal and with
`CategoryTheory.HasDerivedCategory.standard` in force, because it passes through
`AlgebraicGeometry.RingedSite.kFlatModel`. Neither is usable here. `unitLeftIso` below repeats
the construction of `unitIso` on the other side, and the two ingredients it needs are already
stated with the sections universe free: `Stacks.SheafOfModules.isKFlat_single_unit`, so that no
resolution of the unit is chosen, and the composite of
`Stacks.SheafOfModules.Tensor.tensorComplexFlipIso` with
`Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections`, which is the unit law for total
tensor complexes read on the left. The right-hand factor needs no model either: the
localization functor is essentially surjective, so `M` is `Q K` for a complex `K`, and
`comparisonLeft` asks K-flatness of the left factor only.

*Why the shift is taken in the left variable.* `shiftedUnitLeftIso` moves the translation out
of the left factor, so the shift datum it uses is
`Stacks.SheafOfModules.DerivedTensorProduct.commShift_left`, the `commShiftFlipObj` half of the
two-variable coherence, read at the functor `- ⊗^𝐋_O M`. The mirror statement in the right
variable is `AlgebraicGeometry.Space.derivedTensorSingleUnitIso`, which is the same bookkeeping
for `M ⊗^𝐋_O O[i]` on the small étale site of an algebraic space, at the universes
`{u + 1, u, u, u + 1}` that site forces.

*No `@[stacks]` attribute is attached.* This discharges the `hunit` hypothesis of
`Stacks.Cohomology.StrictlyPerfectDevissage.property_of_isStrictlyPerfect` for a Tor-amplitude
property, which is one step of the second assertion of [Stacks, Tag 0DKS], registered in
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativelyPerfectDerivedTensor`. Nothing below
mentions a morphism of sites or a relative Tor dimension.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w d

namespace Stacks.SheafOfModules.DerivedTensorProduct

variable {X : RingedSite.{u, v, w}}
  [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u, v, w} X)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, v, w} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- **`O[i] ⊗^𝐋_O M` is `M⟦-i⟧`.** The structure sheaf placed in degree `i` is the `(-i)`-fold
translate of the structure sheaf placed in degree zero, tensoring with `M` commutes with the
translation in the left variable, and the structure sheaf in degree zero is a unit. -/
def shiftedUnitLeftIso (T : DerivedTensorProduct.{u, v, w, d} X)
    (M : RingedSite.DerivedModules.{u, v, w, d} X) (i : ℤ) :
    (T.tensor.obj ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, v, w} X) i).obj
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).obj M ≅
      M⟦-i⟧ :=
  (T.tensor.mapIso (((DerivedCategory.singleFunctors
      (RingedSite.Modules.{u, v, w} X)).shiftIso (-i) i 0 (by omega)).app
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).symm).app M ≪≫
    ((T.tensor.flip.obj M).commShiftIso (-i)).app
      ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, v, w} X) 0).obj
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ≪≫
    (shiftFunctor (RingedSite.DerivedModules.{u, v, w, d} X) (-i)).mapIso (T.unitLeftIso M)

/-- **Tor amplitude shifts with the object.** If `E` has Tor amplitude in `[a, b]` then `E⟦n⟧`
has Tor amplitude in `[a - n, b - n]`.

Tensoring with a module in degree zero commutes with the translation in the left variable, and
`H^i` of an `n`-fold translate is `H^{n + i}`. -/
theorem hasTorAmplitude_shift {T : DerivedTensorProduct.{u, v, w, d} X}
    {E : RingedSite.DerivedModules.{u, v, w, d} X} {a b : ℤ} (n : ℤ)
    (h : HasTorAmplitude T E a b) : HasTorAmplitude T (E⟦n⟧) (a - n) (b - n) := by
  intro F i hi
  refine (h F (n + i) ?_).of_iso ?_
  · simp only [Set.mem_Icc, not_and_or, not_le] at hi ⊢
    omega
  · exact (DerivedCategory.homologyFunctor (RingedSite.Modules.{u, v, w} X) i).mapIso
      (((T.tensor.flip.obj ((DerivedCategory.singleFunctor
        (RingedSite.Modules.{u, v, w} X) 0).obj F)).commShiftIso n).app E) ≪≫
      (Functor.ShiftSequence.shiftIso
        (F := DerivedCategory.homologyFunctor (RingedSite.Modules.{u, v, w} X) 0)
        n i (n + i) rfl).app _

/-- **The structure sheaf in degree zero has Tor amplitude in `[0, 0]`.** Tensoring it with a
module placed in degree zero returns that module placed in degree zero, by `unitLeftIso`, and
the cohomology of a module placed in degree zero vanishes away from degree zero. -/
theorem hasTorAmplitude_unit (T : DerivedTensorProduct.{u, v, w, d} X) :
    HasTorAmplitude T ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, v, w} X) 0).obj
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0 0 := by
  intro F i hi
  have hi0 : i ≠ 0 := by
    simp only [Set.mem_Icc, not_and_or, not_le] at hi
    omega
  have hz : IsZero ((DerivedCategory.homologyFunctor (RingedSite.Modules.{u, v, w} X) i).obj
      ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, v, w} X) 0).obj F)) := by
    rcases lt_or_gt_of_ne hi0 with h | h
    · exact DerivedCategory.isZero_of_isGE _ 0 i h
    · exact DerivedCategory.isZero_of_isLE _ 0 i h
  exact hz.of_iso ((DerivedCategory.homologyFunctor (RingedSite.Modules.{u, v, w} X) i).mapIso
    (T.unitLeftIso ((DerivedCategory.singleFunctor
      (RingedSite.Modules.{u, v, w} X) 0).obj F)))

/-- **The structure sheaf placed in degree `i` has Tor amplitude in `[i, i]`.** It is the
`(-i)`-fold translate of the structure sheaf in degree zero, which has Tor amplitude in
`[0, 0]`. -/
theorem hasTorAmplitude_singleUnit (T : DerivedTensorProduct.{u, v, w, d} X) (i : ℤ) :
    HasTorAmplitude T ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, v, w} X) i).obj
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) i i :=
  (((hasTorAmplitude_shift (-i) (hasTorAmplitude_unit T)).mono (by omega) (by omega)).of_iso
    (((DerivedCategory.singleFunctors (RingedSite.Modules.{u, v, w} X)).shiftIso (-i) i 0
      (by omega)).app _))

/-- **The interval bookkeeping of the base case.** If `M` has Tor amplitude in `[a, b]` then
`O[i] ⊗^𝐋_O M` has Tor amplitude in every interval `[c, d]` containing the translate
`[a + i, b + i]`.

`shiftedUnitLeftIso` identifies `O[i] ⊗^𝐋_O M` with `M⟦-i⟧`, whose Tor amplitude is
`[a + i, b + i]` by `hasTorAmplitude_shift`, and
`Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude.mono` enlarges that to `[c, d]`. -/
theorem hasTorAmplitude_tensor_singleUnit (T : DerivedTensorProduct.{u, v, w, d} X)
    {M : RingedSite.DerivedModules.{u, v, w, d} X} {a b : ℤ} (i c d : ℤ)
    (hM : HasTorAmplitude T M a b) (hc : c ≤ a + i) (hd : b + i ≤ d) :
    HasTorAmplitude T ((T.tensor.obj ((DerivedCategory.singleFunctor
      (RingedSite.Modules.{u, v, w} X) i).obj
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).obj M) c d :=
  ((hasTorAmplitude_shift (-i) hM).mono (by omega) (by omega)).of_iso
    (T.shiftedUnitLeftIso M i).symm

end Stacks.SheafOfModules.DerivedTensorProduct

end
