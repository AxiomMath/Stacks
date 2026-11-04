module

public import StacksFrontier.Homology.DerivedCategory.ZeroDifferentialCoproduct
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorCoproducts
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorShiftCancel

/-!
# Distributing the derived tensor product over `ℤ`-indexed direct sums on a ringed site

Let `(C, O)` be a ringed site.  The implication `(2) ⟹ (1)` of [Stacks, Tag 0FPY] tensors
`M = ⨁_n ℋ^n[-n]` against `N = ⨁_m (ℋ^m)^{-1}[m]` in `D(O)` and has to move `⊗^𝐋` past the two
direct sums, cancel the shifts in the diagonal terms and recognise the sum of the factors as the
monoidal unit.  This file provides those four moves, for a ringed site and at the index type `ℤ`.

The index type is the point.  The preservation results of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorCoproducts` are stated for an
index type in the site's own universe `u`, while the index of Tag 0FPY is `ℤ`, which is not in
`u`; a universe shrink along `Discrete.equivalence Equiv.ulift`
(`CategoryTheory.Limits.preservesColimitsOfShape_discrete_shrink`) is therefore interposed in
every statement below.

## Main results

* `Stacks.SheafOfModules.DerivedMonoidal.preservesColimitsOfShape_derivedTensorRight`: the
  right-hand tensor functor preserves direct sums indexed by the site's universe, which the
  commutativity constraint of Tag 0FPT reduces to the left-hand statement.
* `Stacks.SheafOfModules.DerivedMonoidal.preservesCoproductsInt_derivedTensorLeft` and
  `preservesCoproductsInt_derivedTensorRight`: the same at `ℤ`.
* `Stacks.SheafOfModules.DerivedMonoidal.preservesColimitsOfShape_singleFunctor`: placing a
  module in a fixed degree preserves `ℤ`-indexed direct sums.
* `Stacks.SheafOfModules.DerivedMonoidal.isZero_tensorObj_of_isZero_left` and
  `isZero_tensorObj_of_isZero_right`: a zero object of `D(O)` tensored with anything is a zero
  object.

## Main definitions

* `Stacks.SheafOfModules.DerivedMonoidal.sigmaDerivedTensorLeftIso` and
  `sigmaDerivedTensorRightIso`: `K ⊗^𝐋 ⨁_n A n ≅ ⨁_n (K ⊗^𝐋 A n)` and the same in the first
  variable.
* `Stacks.SheafOfModules.DerivedMonoidal.sigmaSingleIso`: `(⨁_n G n)[0] ≅ ⨁_n (G n)[0]`.
* `Stacks.SheafOfModules.DerivedMonoidal.derivedUnitIsoSingle`: the unit of `D(O)` is the
  structure sheaf in degree zero.
* `Stacks.SheafOfModules.DerivedMonoidal.derivedTensorShiftCancelIso` and
  `derivedTensorSingleShiftCancelIso`: `M⟦-n⟧ ⊗^𝐋 N⟦n⟧ ≅ M ⊗^𝐋 N`, and its reading on two
  modules placed in the degrees `n` and `-n`.

## Implementation notes

Every statement here is the ringed-site form of a statement that the library already had at a
ringed space only, in `Stacks.Cohomology.MonoidalDerived`; the ringed-space declarations are
reduced to these, since `Stacks.Cohomology.MonoidalDerived.derivedCategoryMonoidalCategory X` is
`derivedMonoidal X.sheaf` at the site of opens of `X`, so nothing is transported in either
direction.  The generalisation is what the ringed-site implication `(2) ⟹ (1)` of Tag 0FPY
consumes: a general site has no points, so the ringed-space statements are not applicable to it
and were not usable as they stood.

`HasCoproducts.{u} (DerivedModules R)` is introduced by `letI` in every statement that mentions a
direct sum, from `Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory`: it is not an
instance, because the derived category is only locally small after Tag 0A5L.

## References

* [Stacks Project, Tag 0FPY](https://stacks.math.columbia.edu/tag/0FPY) — the implication
  `(2) ⟹ (1)` on a ringed site, whose assembly consumes all of this.
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT) — the symmetric monoidal
  structure of `D(O)`.
* [Stacks Project, Tag 0A5L](https://stacks.math.columbia.edu/tag/0A5L) — direct sums in the
  derived category.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry

universe u d

namespace Stacks.SheafOfModules.DerivedMonoidal

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasDerivedCategory.{d} (Mod R)]

/-! ### Preservation of direct sums by the two tensor functors -/

/-- **`- ⊗^𝐋 K` preserves direct sums indexed by the site's universe.**  The commutativity
constraint of Tag 0FPT identifies it with `K ⊗^𝐋 -`, which is
`preservesColimitsOfShape_derivedTensorLeft`. -/
theorem preservesColimitsOfShape_derivedTensorRight (K : DerivedModules R) (ι : Type u) :
    letI := derivedMonoidal R
    letI := derivedSymmetric R
    PreservesColimitsOfShape (Discrete ι) (MonoidalCategory.tensorRight K) := by
  let := derivedMonoidal R
  let := derivedSymmetric R
  let := preservesColimitsOfShape_derivedTensorLeft R K ι
  exact preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight K)

/-- **`K ⊗^𝐋 -` preserves `ℤ`-indexed direct sums.**  This is
`preservesColimitsOfShape_derivedTensorLeft` at `ULift.{u} ℤ`, shrunk to `ℤ`: the index type of
the generic statement must lie in the site's universe, and `ℤ` does not. -/
theorem preservesCoproductsInt_derivedTensorLeft (K : DerivedModules R) :
    letI := derivedMonoidal R
    PreservesColimitsOfShape (Discrete ℤ) (MonoidalCategory.tensorLeft K) := by
  let := derivedMonoidal R
  let := preservesColimitsOfShape_derivedTensorLeft R K (ULift.{u} ℤ)
  exact preservesColimitsOfShape_discrete_shrink.{u} _ _

/-- **`- ⊗^𝐋 K` preserves `ℤ`-indexed direct sums**, the variable in which the assembly of
`(2) ⟹ (1)` of Tag 0FPY distributes over `⨁_n ℋ^n[-n]`. -/
theorem preservesCoproductsInt_derivedTensorRight (K : DerivedModules R) :
    letI := derivedMonoidal R
    letI := derivedSymmetric R
    PreservesColimitsOfShape (Discrete ℤ) (MonoidalCategory.tensorRight K) := by
  let := derivedMonoidal R
  let := derivedSymmetric R
  let := preservesColimitsOfShape_derivedTensorRight R K (ULift.{u} ℤ)
  exact preservesColimitsOfShape_discrete_shrink.{u} _ _

/-! ### The distribution isomorphisms -/

/-- **Distributing `⊗^𝐋` over a direct sum in the second variable**:
`K ⊗^𝐋 ⨁_n A n ≅ ⨁_n (K ⊗^𝐋 A n)` in `D(O)`. -/
def sigmaDerivedTensorLeftIso (K : DerivedModules R) (A : ℤ → DerivedModules R) :
    letI := derivedMonoidal R
    letI : HasCoproducts.{u} (DerivedModules R) :=
      Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory _
    MonoidalCategory.tensorObj K (∐ A) ≅
      ∐ fun n : ℤ => MonoidalCategory.tensorObj K (A n) :=
  letI := derivedMonoidal R
  letI : HasCoproducts.{u} (DerivedModules R) :=
    Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory _
  letI := preservesCoproductsInt_derivedTensorLeft.{u, d} R K
  preservesColimitIso (MonoidalCategory.tensorLeft K) (Discrete.functor A) ≪≫
    HasColimit.isoOfNatIso (Discrete.natIso fun _ => Iso.refl _)

/-- **Distributing `⊗^𝐋` over a direct sum in the first variable**:
`(⨁_n A n) ⊗^𝐋 K ≅ ⨁_n (A n ⊗^𝐋 K)` in `D(O)`. -/
def sigmaDerivedTensorRightIso (K : DerivedModules R) (A : ℤ → DerivedModules R) :
    letI := derivedMonoidal R
    letI : HasCoproducts.{u} (DerivedModules R) :=
      Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory _
    MonoidalCategory.tensorObj (∐ A) K ≅
      ∐ fun n : ℤ => MonoidalCategory.tensorObj (A n) K :=
  letI := derivedMonoidal R
  letI := derivedSymmetric R
  letI : HasCoproducts.{u} (DerivedModules R) :=
    Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory _
  letI := preservesCoproductsInt_derivedTensorRight.{u, d} R K
  preservesColimitIso (MonoidalCategory.tensorRight K) (Discrete.functor A) ≪≫
    HasColimit.isoOfNatIso (Discrete.natIso fun _ => Iso.refl _)

/-! ### Zero objects and the tensor product -/

/-- **A zero object of `D(O)` tensored on the right with anything is a zero object.**

`MonoidalPreadditive (DerivedModules R)` is not available for the derived tensor product of Tag
0FPT, so this cannot be read off `MonoidalCategory.whiskerRight_zero`.  What is available is
that `- ⊗^𝐋 B` preserves direct sums indexed by any type of the site's universe
(`preservesColimitsOfShape_derivedTensorRight`); an empty index gives preservation of the initial
object, and in a category with a zero object an initial object is a zero object. -/
theorem isZero_tensorObj_of_isZero_left (B : DerivedModules R) {Z : DerivedModules R}
    (hZ : IsZero Z) :
    letI := derivedMonoidal R
    IsZero (MonoidalCategory.tensorObj Z B) := by
  let := derivedMonoidal R
  let := derivedSymmetric R
  let := preservesColimitsOfShape_derivedTensorRight R B PEmpty.{u + 1}
  let : PreservesColimitsOfShape (Discrete PEmpty.{1}) (MonoidalCategory.tensorRight B) :=
    preservesColimitsOfShape_of_equiv
      (Discrete.equivalence (Equiv.equivOfIsEmpty PEmpty.{u + 1} PEmpty.{1})) _
  exact (hZ.isInitial.isInitialObj (MonoidalCategory.tensorRight B) Z).isZero

/-- **A zero object of `D(O)` tensored on the left with anything is a zero object.** -/
theorem isZero_tensorObj_of_isZero_right (B : DerivedModules R) {Z : DerivedModules R}
    (hZ : IsZero Z) :
    letI := derivedMonoidal R
    IsZero (MonoidalCategory.tensorObj B Z) := by
  let := derivedMonoidal R
  let := derivedSymmetric R
  exact (isZero_tensorObj_of_isZero_left.{u, d} R B hZ).of_iso (β_ B Z)

/-! ### Modules in a single degree and direct sums -/

/-- **Placing a module in a fixed degree preserves `ℤ`-indexed direct sums.**  The single functor
on complexes preserves all colimits and `Q` preserves direct sums indexed by the site's universe
(Tag 0A5L at the locally small model), so the composite preserves those indexed by
`ULift.{u} ℤ`, hence by `ℤ`. -/
theorem preservesColimitsOfShape_singleFunctor (a : ℤ) :
    PreservesColimitsOfShape (Discrete ℤ) (DerivedCategory.singleFunctor (Mod R) a) := by
  have h₁ : PreservesColimitsOfShape (Discrete (ULift.{u} ℤ))
      (CochainComplex.singleFunctor (Mod R) a) :=
    inferInstanceAs (PreservesColimitsOfShape (Discrete (ULift.{u} ℤ))
      (HomologicalComplex.single (Mod R) (ComplexShape.up ℤ) a))
  have h₂ : PreservesColimitsOfShape (Discrete (ULift.{u} ℤ))
      (DerivedCategory.Q (C := Mod R)) :=
    Stacks.SmallDerivedCategory.derivedCategoryQ_preservesCoproducts (Mod R) _
  have h₃ : PreservesColimitsOfShape (Discrete (ULift.{u} ℤ))
      (CochainComplex.singleFunctor (Mod R) a ⋙ DerivedCategory.Q) :=
    comp_preservesColimitsOfShape _ _
  have h₄ : PreservesColimitsOfShape (Discrete (ULift.{u} ℤ))
      (DerivedCategory.singleFunctor (Mod R) a) :=
    (preservesColimitsOfShape_iff_of_natIso
      (DerivedCategory.singleFunctorIsoCompQ (Mod R) a)).2 h₃
  exact preservesColimitsOfShape_discrete_shrink.{u} _ _

/-- **The direct sum of a family of modules, placed in degree zero**: `(⨁_n G n)[0] ≅ ⨁_n (G n)[0]`
in `D(O)`, for a `ℤ`-indexed family of `O`-modules.  This is
`preservesColimitsOfShape_singleFunctor`, read as an isomorphism. -/
def sigmaSingleIso (G : ℤ → Mod R) [HasCoproduct G] :
    letI : HasCoproducts.{u} (DerivedModules R) :=
      Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory _
    (DerivedCategory.singleFunctor (Mod R) 0).obj (∐ G) ≅
      ∐ fun n : ℤ => (DerivedCategory.singleFunctor (Mod R) 0).obj (G n) :=
  letI : HasCoproducts.{u} (DerivedModules R) :=
    Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory _
  letI := preservesColimitsOfShape_singleFunctor.{u, d} R 0
  preservesColimitIso (DerivedCategory.singleFunctor (Mod R) 0) (Discrete.functor G) ≪≫
    HasColimit.isoOfNatIso (Discrete.natIso fun _ => Iso.refl _)

/-- **The unit of `D(O)` is the structure sheaf in degree zero.**  This is the `unitIso` field of
`symmetricMonoidalDerived`, read through the identification of `DerivedCategory.singleFunctor`
with the single functor on complexes followed by `Q`. -/
def derivedUnitIsoSingle :
    letI := derivedMonoidal R
    𝟙_ (DerivedModules R) ≅
      (DerivedCategory.singleFunctor (Mod R) 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
  letI := derivedMonoidal R
  (symmetricMonoidalDerived R).unitIso ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ (Mod R) 0).app
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R))).symm

/-! ### Cancelling the shifts -/

/-- **Opposite shifts cancel in the derived tensor product**: `M⟦-n⟧ ⊗^𝐋 N⟦n⟧ ≅ M ⊗^𝐋 N` in
`D(O)`.

This is `CategoryTheory.MonoidalCategory.shiftNegTensorShiftIso` at the monoidal structure of Tag
0FPT, whose two hypotheses are `commShift_derivedTensorLeft` and `commShift_derivedTensorRight`.
No coherence between the two commutations is used. -/
def derivedTensorShiftCancelIso (M N : DerivedModules R) (n : ℤ) :
    letI := derivedMonoidal R
    MonoidalCategory.tensorObj ((shiftFunctor (DerivedModules R) (-n)).obj M)
        ((shiftFunctor (DerivedModules R) n).obj N) ≅
      MonoidalCategory.tensorObj M N :=
  letI := derivedMonoidal R
  letI := fun K : DerivedModules R => commShift_derivedTensorLeft.{u, d} R K
  letI := fun K : DerivedModules R => commShift_derivedTensorRight.{u, d} R K
  MonoidalCategory.shiftNegTensorShiftIso M N n

/-- **The cancellation of the shifts in the diagonal term of `(2) ⟹ (1)` of Tag 0FPY**:
`A[n] ⊗^𝐋 B[-n] ≅ A[0] ⊗^𝐋 B[0]` in `D(O)`, for two `O`-modules `A` and `B`.

This is `derivedTensorShiftCancelIso` composed with the identification `A[n] = (A[0])⟦-n⟧` of
`DerivedCategory.singleFunctors`, which is `SingleFunctors.shiftIso` at `(-n) + n = 0`. -/
def derivedTensorSingleShiftCancelIso (A B : Mod R) (n : ℤ) :
    letI := derivedMonoidal R
    MonoidalCategory.tensorObj ((DerivedCategory.singleFunctor (Mod R) n).obj A)
        ((DerivedCategory.singleFunctor (Mod R) (-n)).obj B) ≅
      MonoidalCategory.tensorObj ((DerivedCategory.singleFunctor (Mod R) 0).obj A)
        ((DerivedCategory.singleFunctor (Mod R) 0).obj B) :=
  letI := derivedMonoidal R
  MonoidalCategory.tensorIso
      (((DerivedCategory.singleFunctors (Mod R)).shiftIso (-n) n 0 (by omega)).app A).symm
      (((DerivedCategory.singleFunctors (Mod R)).shiftIso n (-n) 0 (by omega)).app B).symm ≪≫
    derivedTensorShiftCancelIso.{u, d} R _ _ n

/-- A shift of a zero object of `D(O)` is a zero object: the shift is an additive functor, so it
carries the zero object to the zero object. -/
theorem isZero_shift {Z : DerivedModules R} (hZ : IsZero Z) (k : ℤ) :
    IsZero ((shiftFunctor (DerivedModules R) k).obj Z) :=
  IsZero.of_iso (isZero_zero _)
    ((shiftFunctor (DerivedModules R) k).mapIso hZ.isoZero ≪≫
      (shiftFunctor (DerivedModules R) k).mapZeroObject)

/-- **The vanishing of a derived tensor product of two modules in degree zero propagates to every
pair of degrees**: if `A[0] ⊗^𝐋 B[0]` is a zero object of `D(O)` then so is `A[a] ⊗^𝐋 B[b]`, for
all integers `a` and `b`.

Both single functors are shifts of the degree-zero one (`DerivedCategory.singleFunctors`), both
tensor functors commute with the shift (`commShift_derivedTensorLeft` and
`commShift_derivedTensorRight`), and a shift of a zero object is a zero object.  The off-diagonal
terms of the assembly of `(2) ⟹ (1)` of Tag 0FPY are killed in the degrees `a = n`, `b = -m`,
while the vanishing available is in degree zero. -/
theorem isZero_derivedTensorSingle_shift (A B : Mod R) (a b : ℤ)
    (hz : letI := derivedMonoidal R
      IsZero (MonoidalCategory.tensorObj
        ((DerivedCategory.singleFunctor (Mod R) 0).obj A)
        ((DerivedCategory.singleFunctor (Mod R) 0).obj B))) :
    letI := derivedMonoidal R
    IsZero (MonoidalCategory.tensorObj
      ((DerivedCategory.singleFunctor (Mod R) a).obj A)
      ((DerivedCategory.singleFunctor (Mod R) b).obj B)) := by
  let := derivedMonoidal R
  let := fun K : DerivedModules R => commShift_derivedTensorLeft.{u, d} R K
  let := fun K : DerivedModules R => commShift_derivedTensorRight.{u, d} R K
  refine IsZero.of_iso (isZero_shift.{u, d} R (isZero_shift.{u, d} R hz (-b)) (-a)) ?_
  refine MonoidalCategory.tensorIso
      (((DerivedCategory.singleFunctors (Mod R)).shiftIso (-a) a 0 (by omega)).app A).symm
      (((DerivedCategory.singleFunctors (Mod R)).shiftIso (-b) b 0 (by omega)).app B).symm ≪≫
    ?_
  refine ((MonoidalCategory.tensorRight
      ((shiftFunctor (DerivedModules R) (-b)).obj
        ((DerivedCategory.singleFunctor (Mod R) 0).obj B))).commShiftIso (-a)).app
      ((DerivedCategory.singleFunctor (Mod R) 0).obj A) ≪≫ ?_
  exact (shiftFunctor (DerivedModules R) (-a)).mapIso
    (((MonoidalCategory.tensorLeft
      ((DerivedCategory.singleFunctor (Mod R) 0).obj A)).commShiftIso (-b)).app
      ((DerivedCategory.singleFunctor (Mod R) 0).obj B))

end Stacks.SheafOfModules.DerivedMonoidal

end
