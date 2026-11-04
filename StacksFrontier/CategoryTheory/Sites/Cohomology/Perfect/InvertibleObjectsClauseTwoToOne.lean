module

public import StacksFrontier.CategoryTheory.Limits.CoproductOffDiagonal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.InvertibleObjectsClauseThree
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.InvertibleObjectsFactorCoproduct
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.InvertibleObjectsFactorFlatness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.InvertibleObjectsOrthogonality
import StacksCore.Tactic.StacksAttribute

/-!
# Clause (2) of Stacks 0FPY implies clause (1)

Let `(C, O)` be a ringed site and `M` an object of `D(O)`.  If there is a locally finite direct
product decomposition `O = ∏_{n ∈ ℤ} O_n` of the structure sheaf and for each `n` an invertible
`O_n`-module `ℋ^n` with `M = ⨁_n ℋ^n[-n]` in `D(O)` — clause (2) — then `M` is an invertible
object of `D(O)` for the derived tensor product of Stacks 0FPT — clause (1).

This is the source's proof: tensor `M` against `N = ⨁_m (ℋ^m)^{-1}[m]`, distribute `⊗^𝐋` over
the two direct sums, kill every off-diagonal term by the orthogonality of the factors, cancel the
shifts in the diagonal terms and identify them with the factors, and sum to `⨁_n O_n = O`.

## Main results

* `...InvertibleDerived.ProductDecomposition.exists_derivedTensor_iso_of_isInvertibleModule`: the
  diagonal identification — an invertible `O_n`-module has a partner whose derived tensor product
  with it over `O`, both in degree zero, is `O_n` in degree zero.
* `...InvertibleDerived.isInvertibleObject_sigma_of_diagonalIso`: the assembly, for two families
  of modules over the factors whose diagonal terms are identified with the factors.
* `...InvertibleDerived.isInvertibleObject_sigma_toOMod_unit`: `⨁_n O_n[-n]` is invertible in
  `D(O)`, with inverse `⨁_m O_m[m]` — the case `ℋ^n = O_n` of clause (2).
* `...InvertibleDerived.isInvertibleObject_of_hasInvertibleModuleDecomposition`: **the
  implication `(2) ⟹ (1)` of Stacks 0FPY.**

The three dots abbreviate the namespace `AlgebraicGeometry.RingedSite`.

## Implementation notes

Every step is discharged, with nothing assumed beyond clause (2):

* the distribution of `⊗^𝐋` over the two coproducts —
  `Stacks.SheafOfModules.DerivedMonoidal.sigmaDerivedTensorLeftIso` and
  `sigmaDerivedTensorRightIso`.  These are stated at the index type `ℤ`, which does not lie in
  the site's universe, so a universe shrink is interposed inside them;
* the vanishing of the off-diagonal terms,
  `ProductDecomposition.isZero_derivedTensor_toOMod_of_ne`, which assumes nothing beyond `n ≠ m`,
  read through the shifts by
  `Stacks.SheafOfModules.DerivedMonoidal.isZero_derivedTensorSingle_shift`;
* the collapse of the double coproduct onto its diagonal,
  `CategoryTheory.Limits.sigmaIsoOfIsZeroOffDiagonal`;
* the cancellation of the shifts in the diagonal term,
  `Stacks.SheafOfModules.DerivedMonoidal.derivedTensorSingleShiftCancelIso`;
* the diagonal identification itself, which is the sheaf-level
  `ProductDecomposition.tensorObjIsoToOModUnit` carried into `D(O)` by
  `Stacks.SheafOfModules.DerivedMonoidal.derivedTensorSingleIso`, whose flatness input is
  `ProductDecomposition.isFlat_toOMod_of_isInvertibleModule`;
* the identification `⨁_n O_n ≅ O` of `ProductDecomposition.sigmaIsoUnit`, carried into `D(O)` by
  `Stacks.SheafOfModules.DerivedMonoidal.sigmaSingleIso` — placing a module in degree zero
  preserves `ℤ`-indexed direct sums — and the identification of `O[0]` with the monoidal unit of
  `D(O)`, which is `Stacks.SheafOfModules.DerivedMonoidal.derivedUnitIsoSingle`;
* the second isomorphism `N ⊗^𝐋 M ≅ O` of invertibility, which comes from the first by the
  commutativity constraint of Stacks 0FPT.

The representing object of clause (2) is the complex with `ℋ^n` in degree `n` and zero
differentials; `InvertibleDerived.iso_coproduct_zeroDifferentialComplex` identifies it with the
coproduct `∐_n ℋ^n[-n]` once `D(O)` has `ℤ`-indexed coproducts and `Q` preserves them, both of
which are supplied here from Tag 0A5L at the locally small model.

## References

* [Stacks Project, Tag 0FPY](https://stacks.math.columbia.edu/tag/0FPY) — the implication
  `(2) ⟹ (1)`.
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT) — the symmetric monoidal
  structure of `D(O)`.
* [Stacks Project, Tag 0FFN](https://stacks.math.columbia.edu/tag/0FFN) — invertibility in a
  monoidal category.
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K) — invertible modules.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open Opposite
open Stacks.SheafOfModules.DerivedMonoidal

universe u d

namespace AlgebraicGeometry.RingedSite.InvertibleDerived

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {X : RingedSite.{u, u, u}}
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (Mod X.O)]

/-! ### The diagonal identification -/

namespace ProductDecomposition

open Stacks.SheafOfModules.RingSheafProductFactor in
/-- **The diagonal identification of the implication `(2) ⟹ (1)` of Stacks 0FPY.**  An invertible
`O_n`-module `H` has a partner `H'` over the same factor with

`(H as an O-module)[0] ⊗^𝐋_O (H' as an O-module)[0] ≅ (O_n as an O-module)[0]`

in `D(O)`, and nothing is assumed beyond the decomposition.

Tag 0B8K supplies `H'` with `H ⊗_{O_n} H' ≅ O_n`; the sheaf-level identification
`tensorObjIsoToOModUnit` reads that over `O`; and
`Stacks.SheafOfModules.DerivedMonoidal.derivedTensorSingleIso` carries it into `D(O)`, its
flatness input being `isFlat_toOMod_of_isInvertibleModule`.

A step of the proof of an implication of Stacks 0FPY, not a clause of it, so it carries no
`@[stacks]` attribute. -/
theorem exists_derivedTensor_iso_of_isInvertibleModule (D : ProductDecomposition X) (n : ℤ)
    (H : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))
    (hH : Stacks.SheafOfModules.Tensor.IsInvertibleModule (D.factor n) H) :
    ∃ H' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)),
      letI := derivedMonoidal X.O
      Nonempty (MonoidalCategory.tensorObj
        ((DerivedCategory.singleFunctor (Mod X.O) 0).obj ((D.toOMod n).obj H))
        ((DerivedCategory.singleFunctor (Mod X.O) 0).obj ((D.toOMod n).obj H')) ≅
          (DerivedCategory.singleFunctor (Mod X.O) 0).obj ((D.toOMod n).obj
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n))))) := by
  let := SheafOfModules.monoidalCategorySheafTensor X.O
  let := SheafOfModules.monoidalCategorySheafTensor (D.factor n)
  obtain ⟨H', ⟨e⟩⟩ :=
    exists_tensorObj_iso_factorModule_of_isInvertibleModule D.presentation n H hH
  refine ⟨H', ⟨derivedTensorSingleIso.{u, d} X.O _ _
    (D.isFlat_toOMod_of_isInvertibleModule n H hH) ≪≫ ?_⟩⟩
  exact (DerivedCategory.singleFunctor (Mod X.O) 0).mapIso e

end ProductDecomposition

/-! ### The assembly -/

/-- **The assembly of the implication `(2) ⟹ (1)` of Stacks 0FPY.**  Let `O = ∏_n O_n` be a
locally finite direct product decomposition of the structure sheaf of a ringed site, let `L n` and
`L' n` be `O_n`-modules for each `n`, and suppose that for each `n` the `n`-th diagonal term is
identified with the factor,

`(L n)[0] ⊗^𝐋_O (L' n)[0] ≅ O_n[0]`,

all three modules being read as `O`-modules along the projection `O ⟶ O_n`.  Then `⨁_n (L n)[-n]`
is an invertible object of `D(O)`, with inverse `⨁_m (L' m)[m]`.

This is the source's proof; the module docstring lists the step each isomorphism below comes
from.  A step of the proof of an implication of Stacks 0FPY, not a clause of it, so it carries no
`@[stacks]` attribute. -/
theorem isInvertibleObject_sigma_of_diagonalIso (D : ProductDecomposition X)
    (L L' : (n : ℤ) → SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))
    (hdiag : ∀ n : ℤ,
      letI := derivedMonoidal X.O
      Nonempty (MonoidalCategory.tensorObj
        ((DerivedCategory.singleFunctor (Mod X.O) 0).obj ((D.toOMod n).obj (L n)))
        ((DerivedCategory.singleFunctor (Mod X.O) 0).obj ((D.toOMod n).obj (L' n))) ≅
          (DerivedCategory.singleFunctor (Mod X.O) 0).obj ((D.toOMod n).obj
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))))) :
    letI : HasCoproducts.{u} (DerivedCategory (Mod X.O)) :=
      Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory _
    IsInvertibleObject X (∐ fun n : ℤ =>
      (DerivedCategory.singleFunctor (Mod X.O) n).obj ((D.toOMod n).obj (L n))) := by
  let := derivedMonoidal X.O
  let := derivedSymmetric X.O
  let : HasCoproducts.{u} (DerivedCategory (Mod X.O)) :=
    Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory _
  set S : ℤ → DerivedCategory (Mod X.O) := fun n =>
    (DerivedCategory.singleFunctor (Mod X.O) n).obj ((D.toOMod n).obj (L n)) with hS
  set T : ℤ → DerivedCategory (Mod X.O) := fun m =>
    (DerivedCategory.singleFunctor (Mod X.O) (-m)).obj ((D.toOMod m).obj (L' m)) with hT
  -- the off-diagonal terms vanish
  have hoff : ∀ n m : ℤ, m ≠ n →
      IsZero (MonoidalCategory.tensorObj (S n) (T m)) := by
    intro n m hmn
    exact isZero_derivedTensorSingle_shift.{u, d} X.O _ _ n (-m)
      (D.isZero_derivedTensor_toOMod_of_ne.{u, d} hmn (L n) (L' m))
  -- the chain of identifications
  have e : MonoidalCategory.tensorObj (∐ S) (∐ T) ≅ 𝟙_ (DerivedCategory (Mod X.O)) :=
    sigmaDerivedTensorRightIso.{u, d} X.O (∐ T) S ≪≫
      HasColimit.isoOfNatIso
        (G := Discrete.functor fun n : ℤ => ∐ fun m : ℤ => MonoidalCategory.tensorObj (S n) (T m))
        (Discrete.natIso fun n =>
          sigmaDerivedTensorLeftIso.{u, d} X.O (S n.as) T) ≪≫
      (sigmaSigmaIso (fun _ : ℤ => ℤ)
        (fun n m => MonoidalCategory.tensorObj (S n) (T m))) ≪≫
      Sigma.whiskerEquiv
        (f := fun p : (_ : ℤ) × ℤ => MonoidalCategory.tensorObj (S p.1) (T p.2))
        (g := fun p : ℤ × ℤ => MonoidalCategory.tensorObj (S p.1) (T p.2))
        (Equiv.sigmaEquivProd ℤ ℤ) (fun _ => Iso.refl _) ≪≫
      sigmaIsoOfIsZeroOffDiagonal
        (fun n m => MonoidalCategory.tensorObj (S n) (T m)) hoff ≪≫
      HasColimit.isoOfNatIso
        (G := Discrete.functor fun n : ℤ => (DerivedCategory.singleFunctor (Mod X.O) 0).obj
          ((D.toOMod n).obj
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))))
        (Discrete.natIso fun n =>
          derivedTensorSingleShiftCancelIso.{u, d} X.O
            ((D.toOMod n.as).obj (L n.as)) ((D.toOMod n.as).obj (L' n.as)) n.as ≪≫
            (hdiag n.as).some) ≪≫
      (sigmaSingleIso.{u, d} X.O (fun n : ℤ => (D.toOMod n).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n))))).symm ≪≫
      (DerivedCategory.singleFunctor (Mod X.O) 0).mapIso D.sigmaIsoUnit ≪≫
      (derivedUnitIsoSingle.{u, d} X.O).symm
  exact ⟨{ inv := ∐ T
           isoLeft := e
           isoRight := BraidedCategory.braiding (∐ T) (∐ S) ≪≫ e }⟩

/-- **The sum of the factors of a product decomposition, each shifted into its own degree, is an
invertible object of `D(O)`**: `⨁_n O_n[-n]` is invertible, with inverse `⨁_m O_m[m]`.  Nothing is
assumed beyond the decomposition.

This is the implication `(2) ⟹ (1)` of Stacks 0FPY for the decomposition's own factors in place
of the invertible modules `ℋ^n` — the case `ℋ^n = O_n` of clause (2).  It is neither a clause of
the tag nor the full implication, so it carries no `@[stacks]` attribute. -/
theorem isInvertibleObject_sigma_toOMod_unit (D : ProductDecomposition X) :
    letI : HasCoproducts.{u} (DerivedCategory (Mod X.O)) :=
      Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory _
    IsInvertibleObject X (∐ fun n : ℤ => (DerivedCategory.singleFunctor (Mod X.O) n).obj
      ((D.toOMod n).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n))))) := by
  refine isInvertibleObject_sigma_of_diagonalIso.{u, d} D
    (fun n => SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))
    (fun n => SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))
    fun n => ?_
  let := SheafOfModules.monoidalCategorySheafTensor X.O
  let := SheafOfModules.monoidalCategorySheafTensor (D.factor n)
  exact ⟨derivedTensorSingleIso.{u, d} X.O _ _ (D.isFlat_toOMod_unit n) ≪≫
    (DerivedCategory.singleFunctor (Mod X.O) 0).mapIso
      (D.tensorObjIsoToOModUnit n _ _ (MonoidalCategory.leftUnitor _))⟩

/-! ### The implication -/

/-- **The implication `(2) ⟹ (1)` of Stacks 0FPY.**  Let `(C, O)` be a ringed site and `M` an
object of `D(O)`.  If there is a locally finite direct product decomposition
`O = ∏_{n ∈ ℤ} O_n` of the structure sheaf and for each `n` an invertible `O_n`-module `ℋ^n` with
`M = ⨁_n ℋ^n[-n]` in `D(O)`, then `M` is an invertible object of `D(O)` for the derived tensor
product of Stacks 0FPT.

The proof is `isInvertibleObject_sigma_of_diagonalIso`, its diagonal input being
`ProductDecomposition.exists_derivedTensor_iso_of_isInvertibleModule`, transported along the
identification of the representing complex of clause (2) with the coproduct
`∐_n ℋ^n[-n]`. -/
theorem isInvertibleObject_of_hasInvertibleModuleDecomposition (M : DerivedCategory (Mod X.O))
    (hM : HasInvertibleModuleDecomposition X M) : IsInvertibleObject X M := by
  let := derivedMonoidal X.O
  let : HasCoproducts.{u} (DerivedCategory (Mod X.O)) :=
    Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory _
  let : PreservesColimitsOfShape (Discrete ℤ) (DerivedCategory.Q (C := Mod X.O)) := by
    let : PreservesColimitsOfShape (Discrete (ULift.{u} ℤ))
        (DerivedCategory.Q (C := Mod X.O)) :=
      Stacks.SmallDerivedCategory.derivedCategoryQ_preservesCoproducts (Mod X.O) _
    exact preservesColimitsOfShape_discrete_shrink.{u} _ _
  obtain ⟨D, H, hinv, ⟨eM⟩⟩ := hM
  choose H' hH' using fun n : ℤ =>
    D.exists_derivedTensor_iso_of_isInvertibleModule.{u, d} n (H n) (hinv n)
  obtain ⟨hv⟩ := isInvertibleObject_sigma_of_diagonalIso.{u, d} D H H' hH'
  obtain ⟨eQ⟩ := iso_coproduct_zeroDifferentialComplex X D H
  refine ⟨{ inv := hv.inv
            isoLeft := MonoidalCategory.tensorIso (eM ≪≫ eQ.symm) (Iso.refl hv.inv) ≪≫ hv.isoLeft
            isoRight :=
              MonoidalCategory.tensorIso (Iso.refl hv.inv) (eM ≪≫ eQ.symm) ≪≫ hv.isoRight }⟩

end AlgebraicGeometry.RingedSite.InvertibleDerived

end
