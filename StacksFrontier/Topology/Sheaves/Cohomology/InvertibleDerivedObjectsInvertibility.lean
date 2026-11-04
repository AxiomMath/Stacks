module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingSheafProductFactorTensorIso
public import StacksFrontier.CategoryTheory.Limits.CoproductOffDiagonal
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorCoproducts
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorShiftCancel
public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedObjectsAssembly
public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedObjectsCoproduct

/-!
# The assembly of `(2) ⟹ (1)` for Stacks 0FPG

Let `(X, 𝒪_X)` be a ringed space with a locally finite direct product decomposition
`𝒪_X = ∏_{n ∈ ℤ} 𝒪_n` of its structure sheaf, let `ℋ^n` be an `𝒪_n`-module for each `n` and let
`M = ⨁_n ℋ^n[-n]` in `D(𝒪_X)`.  The source's proof of the implication `(2) ⟹ (1)` of Stacks 0FPG
tensors `M` against `N = ⨁_m (ℋ^m)^{-1}[m]`, distributes `⊗^𝐋` over the two direct sums, kills
every off-diagonal term and identifies the `n`-th diagonal term with `𝒪_n`, whose sum is `𝒪_X`.
This file carries out that assembly.

## Main results

* `Stacks.Cohomology.InvertibleDerived.isInvertibleObject_sigma_of_diagonalIso`: **the assembly.**
  Given a product decomposition, two families `L` and `L'` of modules over its factors and, for
  each `n`, an identification `L n[0] ⊗^𝐋 L' n[0] ≅ 𝒪_n[0]` in `D(𝒪_X)` of the `n`-th diagonal
  term, the object `⨁_n (L n)[-n]` is invertible in `D(𝒪_X)`, with inverse `⨁_m (L' m)[m]`.
* `Stacks.Cohomology.InvertibleDerived.isInvertibleObject_of_hasInvertibleModuleDecomposition`:
  the implication `(2) ⟹ (1)` itself, carrying the diagonal identification as a hypothesis.

## What is unconditional here, and what is not

Everything except the diagonal identification is discharged, with no hypothesis beyond the
decomposition:

* the distribution of `⊗^𝐋` over the two coproducts —
  `Stacks.Cohomology.MonoidalDerived.sigmaDerivedTensorLeftIso` and
  `sigmaDerivedTensorRightIso` below, off the preservation results of
  `StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorCoproducts`.  Those are
  stated for an index type in the site's universe `u`, while the index of Stacks 0FPG is `ℤ`, so
  a universe shrink along `Discrete.equivalence Equiv.ulift` is interposed: the cofan form
  `isColimit_tensorLeft_mapCocone` is *not* directly applicable at `ℤ`;
* the vanishing of the off-diagonal terms, which is
  `ProductDecomposition.isZero_derivedTensor_toOXMod_of_ne` — unconditional, in particular with
  no flatness — read through the shifts by `isZero_derivedTensorSingle_shift` below;
* the collapse of the double coproduct onto its diagonal,
  `CategoryTheory.Limits.sigmaIsoOfIsZeroOffDiagonal`;
* the cancellation of the shifts in the diagonal term,
  `Stacks.Cohomology.MonoidalDerived.derivedTensorSingleShiftCancelIso`;
* the identification `⨁_n 𝒪_n ≅ 𝒪_X` of `ProductDecomposition.sigmaIsoUnit`, carried into
  `D(𝒪_X)` by `sigmaSingleIso` below — placing a module in degree zero preserves `ℤ`-indexed
  direct sums — and the identification of `𝒪_X[0]` with the monoidal unit of `D(𝒪_X)`, which is
  the `unitIso` field of `Stacks.Cohomology.MonoidalDerived.symmetricMonoidalDerivedCategory`;
* the second isomorphism `N ⊗^𝐋 M ≅ 𝒪_X` of invertibility, which comes from the first by the
  commutativity constraint of Stacks 0FPB.

**The diagonal identification is the one thing not discharged**, and it is carried as an explicit
hypothesis.  For the invertible `ℋ^n` of clause (2) it says

`(ℋ^n as an 𝒪_X-module)[0] ⊗^𝐋_{𝒪_X} ((ℋ^n)^{-1} as an 𝒪_X-module)[0] ≅ (𝒪_n as an 𝒪_X-module)[0]`,

and what is missing for it is *not* the `𝒪_n`-module statement `ℋ^n ⊗_{𝒪_n} (ℋ^n)^{-1} ≅ 𝒪_n`,
which is the definition of invertibility
(`Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit`), but the comparison of the two
tensor products: the restriction of scalars along the surjection `𝒪_X ⟶ 𝒪_n` commutes with the
tensor product of `𝒪_n`-modules, and the derived and ordinary `𝒪_X`-tensor products of two
`𝒪_n`-modules agree.  Neither is in the library.  The comparison *map* is
`Stacks.SheafOfModules.TensorRestrictScalars.laxComparison`, with naturality in both variables,
but nothing asserts it is invertible at a surjective map of ring sheaves; and the derived
comparison needs the flatness over `𝒪_X` of a module over a factor, which is available over
`𝒪_n` only (`Stacks.SheafOfModules.isFlat_of_isInvertible`) and would need the transitivity of
flatness along a restriction of scalars, also absent.  See the module docstring of
`StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedObjectsAssembly`, where the same
comparison is what the *off*-diagonal vanishing avoided by using the idempotent instead.

Nothing here is a clause of Stacks 0FPG: the implication `(2) ⟹ (1)` is an assertion of the tag,
but the form proved below carries the diagonal hypothesis, so no declaration carries the project
tag and the four existing attribute sites of that tag are untouched.

## References

* [Stacks Project, Tag 0FPG](https://stacks.math.columbia.edu/tag/0FPG) — the implication
  `(2) ⟹ (1)`.
* [Stacks Project, Tag 0FPB](https://stacks.math.columbia.edu/tag/0FPB) — the derived tensor
  product on `D(𝒪_X)` and its commutativity constraint.
* [Stacks Project, Tag 0FFN](https://stacks.math.columbia.edu/tag/0FFN) — invertibility in a
  monoidal category.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open Opposite TopologicalSpace
open Stacks.SheafOfModules.DerivedMonoidal

universe u d

namespace Stacks.Cohomology.MonoidalDerived

variable (X : RingedSpace.{u, u}) [HasDerivedCategory.{d} (Mod X.sheaf)]

/-- **Placing a module in degree zero preserves `ℤ`-indexed direct sums.**  The single functor on
complexes preserves all colimits and `Q` preserves direct sums indexed by the site's universe
(Tag 0A5L at the locally small model), so the composite preserves those indexed by
`ULift.{u} ℤ`, hence by `ℤ`.

This is the ringed-space analogue of
`Stacks.Duality.DerivedPushforward.preservesColimitsOfShape_discrete_singleFunctor`, which says
the same for the modules on a scheme and is proved the same way; the two categories of modules
are not interchangeable by instance search. -/
public theorem preservesColimitsOfShape_singleFunctor (a : ℤ) :
    PreservesColimitsOfShape (Discrete ℤ) (DerivedCategory.singleFunctor (Mod X.sheaf) a) := by
  have h₁ : PreservesColimitsOfShape (Discrete (ULift.{u} ℤ))
      (CochainComplex.singleFunctor (Mod X.sheaf) a) :=
    inferInstanceAs (PreservesColimitsOfShape (Discrete (ULift.{u} ℤ))
      (HomologicalComplex.single (Mod X.sheaf) (ComplexShape.up ℤ) a))
  have h₂ : PreservesColimitsOfShape (Discrete (ULift.{u} ℤ))
      (DerivedCategory.Q (C := Mod X.sheaf)) :=
    Stacks.SmallDerivedCategory.derivedCategoryQ_preservesCoproducts (Mod X.sheaf) _
  have h₃ : PreservesColimitsOfShape (Discrete (ULift.{u} ℤ))
      (CochainComplex.singleFunctor (Mod X.sheaf) a ⋙ DerivedCategory.Q) :=
    comp_preservesColimitsOfShape _ _
  have h₄ : PreservesColimitsOfShape (Discrete (ULift.{u} ℤ))
      (DerivedCategory.singleFunctor (Mod X.sheaf) a) :=
    (preservesColimitsOfShape_iff_of_natIso
      (DerivedCategory.singleFunctorIsoCompQ (Mod X.sheaf) a)).2 h₃
  exact preservesColimitsOfShape_discrete_shrink.{u} _ _

/-- **The direct sum of a family of modules, placed in degree zero**: `⨁_n (G n)[0] ≅ (⨁_n G n)[0]`
in `D(𝒪_X)`, for a `ℤ`-indexed family of `𝒪_X`-modules.  This is
`preservesColimitsOfShape_singleFunctor`, read as an isomorphism. -/
public def sigmaSingleIso (G : ℤ → Mod X.sheaf) [HasCoproduct G] :
    letI : HasCoproducts.{u} (DerivedModules X.sheaf) :=
      Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory _
    (DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj (∐ G) ≅
      ∐ fun n : ℤ => (DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj (G n) :=
  letI : HasCoproducts.{u} (DerivedModules X.sheaf) :=
    Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory _
  letI := preservesColimitsOfShape_singleFunctor.{u, d} X 0
  preservesColimitIso (DerivedCategory.singleFunctor (Mod X.sheaf) 0) (Discrete.functor G) ≪≫
    HasColimit.isoOfNatIso (Discrete.natIso fun _ => Iso.refl _)

/-- **The unit of `D(𝒪_X)` is the structure sheaf in degree zero.**  This is the `unitIso` field
of `symmetricMonoidalDerivedCategory`, read through the identification of
`DerivedCategory.singleFunctor` with the single functor on complexes followed by `Q`. -/
public def derivedUnitIsoSingle :
    letI := derivedCategoryMonoidalCategory.{u, d} X
    𝟙_ (DerivedModules X.sheaf) ≅
      (DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) :=
  letI := derivedCategoryMonoidalCategory.{u, d} X
  (symmetricMonoidalDerivedCategory.{u, d} X).unitIso ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ (Mod X.sheaf) 0).app
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))).symm

/-- **`K ⊗^𝐋_{𝒪_X} -` preserves `ℤ`-indexed direct sums.**  This is
`preservesCoproducts_derivedTensorLeft` at `ULift.{u} ℤ`, shrunk to `ℤ`; the index type of the
generic statement must lie in the site's universe, and `ℤ` does not. -/
public theorem preservesCoproductsInt_derivedTensorLeft (K : DerivedModules X.sheaf) :
    letI := derivedCategoryMonoidalCategory.{u, d} X
    letI : HasCoproducts.{u} (DerivedModules X.sheaf) :=
      Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory _
    PreservesColimitsOfShape (Discrete ℤ) (MonoidalCategory.tensorLeft K) := by
  let := derivedCategoryMonoidalCategory.{u, d} X
  let : HasCoproducts.{u} (DerivedModules X.sheaf) :=
    Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory _
  let := preservesCoproducts_derivedTensorLeft.{u, d} X K (ULift.{u} ℤ)
  exact preservesColimitsOfShape_discrete_shrink.{u} _ _

/-- **`- ⊗^𝐋_{𝒪_X} K` preserves `ℤ`-indexed direct sums**, the variable in which the assembly of
`(2) ⟹ (1)` of Stacks 0FPG distributes over `⨁_n ℋ^n[-n]`. -/
public theorem preservesCoproductsInt_derivedTensorRight (K : DerivedModules X.sheaf) :
    letI := derivedCategoryMonoidalCategory.{u, d} X
    letI := derivedCategorySymmetricCategory.{u, d} X
    letI : HasCoproducts.{u} (DerivedModules X.sheaf) :=
      Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory _
    PreservesColimitsOfShape (Discrete ℤ) (MonoidalCategory.tensorRight K) := by
  let := derivedCategoryMonoidalCategory.{u, d} X
  let := derivedCategorySymmetricCategory.{u, d} X
  let : HasCoproducts.{u} (DerivedModules X.sheaf) :=
    Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory _
  let := preservesCoproducts_derivedTensorRight.{u, d} X K (ULift.{u} ℤ)
  exact preservesColimitsOfShape_discrete_shrink.{u} _ _

/-- **Distributing `⊗^𝐋` over a direct sum in the second variable**:
`K ⊗^𝐋 ⨁_n A n ≅ ⨁_n (K ⊗^𝐋 A n)` in `D(𝒪_X)`. -/
public def sigmaDerivedTensorLeftIso (K : DerivedModules X.sheaf)
    (A : ℤ → DerivedModules X.sheaf) :
    letI := derivedCategoryMonoidalCategory.{u, d} X
    letI : HasCoproducts.{u} (DerivedModules X.sheaf) :=
      Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory _
    MonoidalCategory.tensorObj K (∐ A) ≅
      ∐ fun n : ℤ => MonoidalCategory.tensorObj K (A n) :=
  letI := derivedCategoryMonoidalCategory.{u, d} X
  letI : HasCoproducts.{u} (DerivedModules X.sheaf) :=
    Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory _
  letI := preservesCoproductsInt_derivedTensorLeft.{u, d} X K
  preservesColimitIso (MonoidalCategory.tensorLeft K) (Discrete.functor A) ≪≫
    HasColimit.isoOfNatIso (Discrete.natIso fun _ => Iso.refl _)

/-- **Distributing `⊗^𝐋` over a direct sum in the first variable**:
`(⨁_n A n) ⊗^𝐋 K ≅ ⨁_n (A n ⊗^𝐋 K)` in `D(𝒪_X)`. -/
public def sigmaDerivedTensorRightIso (K : DerivedModules X.sheaf)
    (A : ℤ → DerivedModules X.sheaf) :
    letI := derivedCategoryMonoidalCategory.{u, d} X
    letI : HasCoproducts.{u} (DerivedModules X.sheaf) :=
      Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory _
    MonoidalCategory.tensorObj (∐ A) K ≅
      ∐ fun n : ℤ => MonoidalCategory.tensorObj (A n) K :=
  letI := derivedCategoryMonoidalCategory.{u, d} X
  letI := derivedCategorySymmetricCategory.{u, d} X
  letI : HasCoproducts.{u} (DerivedModules X.sheaf) :=
    Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory _
  letI := preservesCoproductsInt_derivedTensorRight.{u, d} X K
  preservesColimitIso (MonoidalCategory.tensorRight K) (Discrete.functor A) ≪≫
    HasColimit.isoOfNatIso (Discrete.natIso fun _ => Iso.refl _)

/-- A shift of a zero object of `D(𝒪_X)` is a zero object: the shift is an additive functor, so it
carries the zero object to the zero object. -/
public theorem isZero_shift {Z : DerivedModules X.sheaf} (hZ : IsZero Z) (k : ℤ) :
    IsZero ((shiftFunctor (DerivedModules X.sheaf) k).obj Z) :=
  IsZero.of_iso (isZero_zero _)
    ((shiftFunctor (DerivedModules X.sheaf) k).mapIso hZ.isoZero ≪≫
      (shiftFunctor (DerivedModules X.sheaf) k).mapZeroObject)

/-- **The vanishing of a derived tensor product of two modules in degree zero propagates to every
pair of degrees**: if `A[0] ⊗^𝐋 B[0]` is a zero object of `D(𝒪_X)` then so is `A[a] ⊗^𝐋 B[b]`,
for all integers `a` and `b`.

Both single functors are shifts of the degree-zero one
(`DerivedCategory.singleFunctors`), both tensor functors commute with the shift
(`commShift_derivedTensorLeft` and `commShift_derivedTensorRight`), and a shift of a zero object
is a zero object.  The off-diagonal terms of the assembly of `(2) ⟹ (1)` of Stacks 0FPG are
killed in the degrees `a = n`, `b = -m`, while the vanishing available is in degree zero. -/
public theorem isZero_derivedTensorSingle_shift (A B : Mod X.sheaf) (a b : ℤ)
    (hz : letI := derivedCategoryMonoidalCategory.{u, d} X
      IsZero (MonoidalCategory.tensorObj
        ((DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj A)
        ((DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj B))) :
    letI := derivedCategoryMonoidalCategory.{u, d} X
    IsZero (MonoidalCategory.tensorObj
      ((DerivedCategory.singleFunctor (Mod X.sheaf) a).obj A)
      ((DerivedCategory.singleFunctor (Mod X.sheaf) b).obj B)) := by
  let := derivedCategoryMonoidalCategory.{u, d} X
  let := fun K : DerivedModules X.sheaf => commShift_derivedTensorLeft.{u, d} X K
  let := fun K : DerivedModules X.sheaf => commShift_derivedTensorRight.{u, d} X K
  refine IsZero.of_iso (isZero_shift.{u, d} X (isZero_shift.{u, d} X hz (-b)) (-a)) ?_
  refine MonoidalCategory.tensorIso
      (((DerivedCategory.singleFunctors (Mod X.sheaf)).shiftIso (-a) a 0 (by omega)).app A).symm
      (((DerivedCategory.singleFunctors (Mod X.sheaf)).shiftIso (-b) b 0 (by omega)).app B).symm ≪≫
    ?_
  refine ((MonoidalCategory.tensorRight
      ((shiftFunctor (DerivedModules X.sheaf) (-b)).obj
        ((DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj B))).commShiftIso (-a)).app
      ((DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj A) ≪≫ ?_
  exact (shiftFunctor (DerivedModules X.sheaf) (-a)).mapIso
    (((MonoidalCategory.tensorLeft
      ((DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj A)).commShiftIso (-b)).app
      ((DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj B))

end Stacks.Cohomology.MonoidalDerived

namespace Stacks.Cohomology.InvertibleDerived

variable {X : RingedSpace.{u, u}} [HasDerivedCategory.{d} (Mod X.sheaf)]

/-- **The assembly of the implication `(2) ⟹ (1)` of Stacks 0FPG.**  Let `𝒪_X = ∏_n 𝒪_n` be a
locally finite direct product decomposition of the structure sheaf of a ringed space, let `L n`
and `L' n` be `𝒪_n`-modules for each `n`, and suppose that for each `n` the `n`-th diagonal term
is identified with the factor,

`(L n)[0] ⊗^𝐋_{𝒪_X} (L' n)[0] ≅ 𝒪_n[0]`,

all three modules being read as `𝒪_X`-modules by restriction of scalars along the projection
`𝒪_X ⟶ 𝒪_n`.  Then `⨁_n (L n)[-n]` is an invertible object of `D(𝒪_X)`, with inverse
`⨁_m (L' m)[m]`.

This is the source's proof: distribute `⊗^𝐋` over the two direct sums, kill the off-diagonal
terms by the orthogonality of the factors, cancel the shifts in the diagonal terms, identify them
by the hypothesis, and sum to `⨁_n 𝒪_n = 𝒪_X`.  Every step but the hypothesis is unconditional —
see the module docstring, which also says what the hypothesis is waiting on.

A step of the proof of an implication of Stacks 0FPG carrying a hypothesis of its own, not a
clause of the tag, so it carries no `@[stacks]` attribute. -/
public theorem isInvertibleObject_sigma_of_diagonalIso (D : ProductDecomposition X)
    (L L' : (n : ℤ) → SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))
    (hdiag : ∀ n : ℤ,
      letI := MonoidalDerived.derivedCategoryMonoidalCategory.{u, d} X
      Nonempty (MonoidalCategory.tensorObj
        ((DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj ((D.toOXMod n).obj (L n)))
        ((DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj ((D.toOXMod n).obj (L' n))) ≅
          (DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj ((D.toOXMod n).obj
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))))) :
    letI : HasCoproducts.{u} (DerivedModules X.sheaf) :=
      Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory _
    IsInvertibleObject (∐ fun n : ℤ =>
      (DerivedCategory.singleFunctor (Mod X.sheaf) n).obj ((D.toOXMod n).obj (L n))) := by
  let := MonoidalDerived.derivedCategoryMonoidalCategory.{u, d} X
  let := MonoidalDerived.derivedCategorySymmetricCategory.{u, d} X
  let : HasCoproducts.{u} (DerivedModules X.sheaf) :=
    Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory _
  set S : ℤ → DerivedModules X.sheaf := fun n =>
    (DerivedCategory.singleFunctor (Mod X.sheaf) n).obj ((D.toOXMod n).obj (L n)) with hS
  set T : ℤ → DerivedModules X.sheaf := fun m =>
    (DerivedCategory.singleFunctor (Mod X.sheaf) (-m)).obj ((D.toOXMod m).obj (L' m)) with hT
  -- the off-diagonal terms vanish
  have hoff : ∀ n m : ℤ, m ≠ n →
      IsZero (MonoidalCategory.tensorObj (S n) (T m)) := by
    intro n m hmn
    exact MonoidalDerived.isZero_derivedTensorSingle_shift.{u, d} X _ _ n (-m)
      (D.isZero_derivedTensor_toOXMod_of_ne.{u, d} hmn (L n) (L' m))
  -- the chain of identifications
  have e : MonoidalCategory.tensorObj (∐ S) (∐ T) ≅ 𝟙_ (DerivedModules X.sheaf) :=
    MonoidalDerived.sigmaDerivedTensorRightIso.{u, d} X (∐ T) S ≪≫
      HasColimit.isoOfNatIso
        (G := Discrete.functor fun n : ℤ => ∐ fun m : ℤ => MonoidalCategory.tensorObj (S n) (T m))
        (Discrete.natIso fun n =>
          MonoidalDerived.sigmaDerivedTensorLeftIso.{u, d} X (S n.as) T) ≪≫
      (sigmaSigmaIso (fun _ : ℤ => ℤ)
        (fun n m => MonoidalCategory.tensorObj (S n) (T m))) ≪≫
      Sigma.whiskerEquiv
        (f := fun p : (_ : ℤ) × ℤ => MonoidalCategory.tensorObj (S p.1) (T p.2))
        (g := fun p : ℤ × ℤ => MonoidalCategory.tensorObj (S p.1) (T p.2))
        (Equiv.sigmaEquivProd ℤ ℤ) (fun _ => Iso.refl _) ≪≫
      sigmaIsoOfIsZeroOffDiagonal
        (fun n m => MonoidalCategory.tensorObj (S n) (T m)) hoff ≪≫
      HasColimit.isoOfNatIso
        (G := Discrete.functor fun n : ℤ => (DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj
          ((D.toOXMod n).obj
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))))
        (Discrete.natIso fun n =>
          MonoidalDerived.derivedTensorSingleShiftCancelIso.{u, d} X
            ((D.toOXMod n.as).obj (L n.as)) ((D.toOXMod n.as).obj (L' n.as)) n.as ≪≫
            (hdiag n.as).some) ≪≫
      (MonoidalDerived.sigmaSingleIso.{u, d} X (fun n : ℤ => (D.toOXMod n).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n))))).symm ≪≫
      (DerivedCategory.singleFunctor (Mod X.sheaf) 0).mapIso D.sigmaIsoUnit ≪≫
      (MonoidalDerived.derivedUnitIsoSingle.{u, d} X).symm
  exact ⟨{ inv := ∐ T
           isoLeft := e
           isoRight := BraidedCategory.braiding (∐ T) (∐ S) ≪≫ e }⟩

/-- **A factor is its own tensor product with itself over the structure sheaf**, and more
generally `𝒪_n ⊗_{𝒪_X} L ≅ L` for every `𝒪_n`-module `L` read as an `𝒪_X`-module.

This is the ringed-space reading of
`Stacks.SheafOfModules.RingSheafProductFactor.tensorObjIsoRestrictScalars` at the product
presentation that `ProductDecomposition.iso` supplies.  It is the isomorphism of which
`ProductDecomposition.nonempty_retract_tensor_toOXMod` is the retract half.

A step of the proof of an implication of Stacks 0FPG, not a clause of it, so it carries no
`@[stacks]` attribute. -/
public def ProductDecomposition.tensorIso_toOXMod (D : ProductDecomposition X) (n : ℤ)
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n))) :
    letI := SheafOfModules.monoidalCategorySheafTensor X.sheaf
    (D.toOXMod n).obj L ≅ MonoidalCategory.tensorObj
      ((D.toOXMod n).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n))))
      ((D.toOXMod n).obj L) :=
  -- pinned by name, as in the sibling statements of
  -- `StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedObjectsAssembly`: the general
  -- instance applies, but resolving it by search from this file's context exhausts the budget.
  letI : HasBinaryBiproducts
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) :=
    inferInstanceAs (HasBinaryBiproducts (StrictlyPerfect.OXMod.{u, u} X))
  Stacks.SheafOfModules.RingSheafProductFactor.tensorObjIsoRestrictScalars
    (Stacks.SheafOfModules.RingSheafProductFactor.ProductPresentation.ofIso D.iso) n L

/-- **The diagonal identification at the factors themselves**: `𝒪_n[0] ⊗^𝐋_{𝒪_X} 𝒪_n[0] ≅ 𝒪_n[0]`
in `D(𝒪_X)`.

The factor is flat over `𝒪_X` (`ProductDecomposition.isFlat_toOXMod_unit`), so the derived tensor
product of the two copies in degree zero is their ordinary tensor product in degree zero
(`Stacks.Cohomology.MonoidalDerived.derivedTensorSingleIso`), and that is the factor by
`ProductDecomposition.tensorIso_toOXMod`.

This is the hypothesis of `isInvertibleObject_sigma_of_diagonalIso` discharged for the families
`L = L' = 𝒪_n`, with nothing assumed. -/
public def ProductDecomposition.derivedTensorIso_toOXMod_unit (D : ProductDecomposition X)
    (n : ℤ) :
    letI := MonoidalDerived.derivedCategoryMonoidalCategory.{u, d} X
    MonoidalCategory.tensorObj
        ((DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj ((D.toOXMod n).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))))
        ((DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj ((D.toOXMod n).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n))))) ≅
      (DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj ((D.toOXMod n).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))) :=
  MonoidalDerived.derivedTensorSingleIso.{u, d} X _ _ (D.isFlat_toOXMod_unit n) ≪≫
    (DerivedCategory.singleFunctor (Mod X.sheaf) 0).mapIso
      (D.tensorIso_toOXMod n
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))).symm

/-- **The sum of the factors of a product decomposition, each shifted into its own degree, is an
invertible object of `D(𝒪_X)`**: `⨁_n 𝒪_n[-n]` is invertible, with inverse `⨁_m 𝒪_m[m]`.  Nothing
is assumed beyond the decomposition.

This is the implication `(2) ⟹ (1)` of Stacks 0FPG for the decomposition's own factors in place
of the invertible modules `ℋ^n` — the case `ℋ^n = 𝒪_n` of clause (2) — and it is unconditional:
`isInvertibleObject_sigma_of_diagonalIso` with its diagonal hypothesis discharged by
`ProductDecomposition.derivedTensorIso_toOXMod_unit`.

It is not a clause of Stacks 0FPG and not the full implication, so it carries no `@[stacks]`
attribute.  Note that it is not the invertibility of a shift of the unit: as soon as two factors
are nonzero, no single summand `𝒪_n[-n]` is invertible (see the module docstring of
`StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedObjects`), and the sum is. -/
public theorem isInvertibleObject_sigma_toOXMod_unit (D : ProductDecomposition X) :
    letI : HasCoproducts.{u} (DerivedModules X.sheaf) :=
      Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory _
    IsInvertibleObject (∐ fun n : ℤ => (DerivedCategory.singleFunctor (Mod X.sheaf) n).obj
      ((D.toOXMod n).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n))))) :=
  isInvertibleObject_sigma_of_diagonalIso.{u, d} D
    (fun n => SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))
    (fun n => SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))
    (fun n => ⟨D.derivedTensorIso_toOXMod_unit.{u, d} n⟩)

/-- **The implication `(2) ⟹ (1)` of Stacks 0FPG, modulo the diagonal identification.**  If `M`
admits a locally finite invertible module decomposition — clause (2) — then `M` is an invertible
object of `D(𝒪_X)` — clause (1) — provided that for every product decomposition of the structure
sheaf and every invertible module `H` over a factor `𝒪_n` there is an `𝒪_n`-module `H'` with

`(H as an 𝒪_X-module)[0] ⊗^𝐋_{𝒪_X} (H' as an 𝒪_X-module)[0] ≅ (𝒪_n as an 𝒪_X-module)[0]`.

That hypothesis is the diagonal identification of `isInvertibleObject_sigma_of_diagonalIso`, in
the form in which clause (2) supplies its data; the module docstring says what it is waiting on
and why it is not simply the invertibility of `H`.  It is implied by — and is weaker than — the
conjunction of `Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit` over `𝒪_n` with
the invertibility of the base-change comparison
`Stacks.SheafOfModules.TensorRestrictScalars.laxComparison` at the projection `𝒪_X ⟶ 𝒪_n` and
the agreement of the derived and ordinary `𝒪_X`-tensor products of two `𝒪_n`-modules.

Because it carries that hypothesis this is not yet the tag's implication, so it carries no
`@[stacks]` attribute; the decomposition, the distribution, the orthogonality, the shifts and the
sum `⨁_n 𝒪_n = 𝒪_X` are all discharged inside it. -/
public theorem isInvertibleObject_of_hasInvertibleModuleDecomposition
    (hdiag : ∀ (D : ProductDecomposition X) (n : ℤ)
      (H : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n))),
      Stacks.SheafOfModules.Tensor.IsInvertibleModule (D.factor n) H →
      ∃ H' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)),
        letI := MonoidalDerived.derivedCategoryMonoidalCategory.{u, d} X
        Nonempty (MonoidalCategory.tensorObj
          ((DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj ((D.toOXMod n).obj H))
          ((DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj ((D.toOXMod n).obj H')) ≅
            (DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj ((D.toOXMod n).obj
              (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n))))))
    (M : DerivedModules X.sheaf) (hM : HasInvertibleModuleDecomposition X M) :
    IsInvertibleObject M := by
  let := MonoidalDerived.derivedCategoryMonoidalCategory.{u, d} X
  let : HasCoproducts.{u} (DerivedModules X.sheaf) :=
    Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory _
  obtain ⟨D, H, hinv, ⟨e⟩⟩ := hM
  choose H' hH' using fun n : ℤ => hdiag D n (H n) (hinv n)
  obtain ⟨hv⟩ := isInvertibleObject_sigma_of_diagonalIso.{u, d} D H H' hH'
  exact ⟨{ inv := hv.inv
           isoLeft := MonoidalCategory.tensorIso e (Iso.refl hv.inv) ≪≫ hv.isoLeft
           isoRight := MonoidalCategory.tensorIso (Iso.refl hv.inv) e ≪≫ hv.isoRight }⟩

end Stacks.Cohomology.InvertibleDerived

end
