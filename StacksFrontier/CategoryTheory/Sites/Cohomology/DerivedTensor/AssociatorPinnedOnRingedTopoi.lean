module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RelativeCupProductCoherence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorReseatConstraints
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormula

/-!
# The constraints of Tag 0FPT on a ringed topos, at the total-complex spelling

Let `(Sh(C), 𝒪)` be a ringed topos.  [Stacks, Tag 0FPT] gives `D(𝒪)` a symmetric monoidal
structure whose tensor product is the derived tensor product of [Stacks, Tag 06YU] on the nose,
and `Stacks.SheafOfModules.DerivedMonoidal.canonicalComparison_associator` says that on K-flat
complexes its associativity constraint is the associator of `Comp(Mod(𝒪))`, carried across by
the comparison of [Stacks, Tag 06YU].

This file states that associativity clause with the derived tensor bifunctor read on pairs,
`Stacks.Cohomology.RelativeCupProductOnRingedTopoi.uncurriedDerivedTensor`, and with every total
tensor complex written as `Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair` applied to
`Stacks.SheafOfModules.Tensor.sheafTensor`, the uncurried form of
`HomologicalComplex.mapBifunctor`.

## Main definitions

* `Stacks.Cohomology.RelativeCupProductOnRingedTopoi.totalComplexMapRight` and
  `Stacks.Cohomology.RelativeCupProductOnRingedTopoi.totalComplexMapLeft`: the total tensor
  complex of a cochain map and an identity, pinned at the total-complex spelling.
* `Stacks.Cohomology.RelativeCupProductOnRingedTopoi.complexAssociatorPair`: the associator of
  `Comp(Mod(𝒪))` with source and target at that spelling.
* `Stacks.Cohomology.RelativeCupProductOnRingedTopoi.comparisonPair`: the K-flat comparison of
  [Stacks, Tag 06YU] with its source read on the uncurried bifunctor and its target at that
  spelling.
* `Stacks.Cohomology.RelativeCupProductOnRingedTopoi.UncurriedComparisonAssociator`: the
  associativity clause of [Stacks, Tag 0FPT] in that vocabulary, as a proposition.

## Main results

* `Stacks.Cohomology.RelativeCupProductOnRingedTopoi.uncurry_derivedTensor_map_id_right` and
  `Stacks.Cohomology.RelativeCupProductOnRingedTopoi.uncurry_derivedTensor_map_id_left`: the
  uncurried derived tensor bifunctor on a one-sided morphism is a whiskering of [Stacks, Tag
  0FPT].
* `Stacks.Cohomology.RelativeCupProductOnRingedTopoi.canonicalAssociatorHom_naturality`: the
  associativity constraint of [Stacks, Tag 0FPT] is natural in its three variables, with the
  bifunctor written uncurried.
* `Stacks.Cohomology.RelativeCupProductOnRingedTopoi.isIso_comparisonPair`,
  `Stacks.Cohomology.RelativeCupProductOnRingedTopoi.comparisonPair_naturality_right`,
  `Stacks.Cohomology.RelativeCupProductOnRingedTopoi.comparisonPair_naturality_left`: the
  comparison of [Stacks, Tag 06YU] is an isomorphism on K-flat complexes and is natural in each
  variable separately, at the pinned spelling.
* `Stacks.Cohomology.RelativeCupProductOnRingedTopoi.canonicalComparison_associator_uncurried`:
  **the associativity clause of [Stacks, Tag 0FPT]**, in the uncurried, pinned vocabulary.

## References

* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 0FPL](https://stacks.math.columbia.edu/tag/0FPL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Stacks.SheafOfModules.DerivedMonoidal
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.RelativeCupProductOnRingedTopoi

universe u

attribute [local instance] HasDerivedCategory.standard

section Pinned

variable (W : RingedTopos.{u, u, u})
  [HasSheafify W.J AddCommGrpCat.{u}] [W.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.O).obj M).Additive]
  [∀ (P Q : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf W.O)) ℤ),
    HomologicalComplex.HasMapBifunctor P Q
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.O) (ComplexShape.up ℤ)]

/-! ### The total tensor complex of a one-sided cochain map -/

/-- **The total tensor complex of a cochain map and an identity in the second variable**: the
image of `(a, 𝟙 B)` under `Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair`. -/
def totalComplexMapRight {A A' : Complexes W.O} (a : A ⟶ A') (B : Complexes W.O) :
    (DerivedPullbackTensor.totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.O)).obj (A, B) ⟶
      (DerivedPullbackTensor.totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.O)).obj (A', B) :=
  (DerivedPullbackTensor.totalComplexPair
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.O)).map (a ×ₘ 𝟙 B)

/-- **The total tensor complex of an identity and a cochain map in the second variable**: the
image of `(𝟙 A, b)` under `Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair`. -/
def totalComplexMapLeft (A : Complexes W.O) {B B' : Complexes W.O} (b : B ⟶ B') :
    (DerivedPullbackTensor.totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.O)).obj (A, B) ⟶
      (DerivedPullbackTensor.totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.O)).obj (A, B') :=
  (DerivedPullbackTensor.totalComplexPair
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.O)).map (𝟙 A ×ₘ b)

/-- `Stacks.Cohomology.RelativeCupProductOnRingedTopoi.totalComplexMapRight` is the total tensor
complex `HomologicalComplex.mapBifunctorMap a (𝟙 B)` of the pair `(a, 𝟙 B)`. -/
theorem totalComplexMapRight_eq_mapBifunctorMap {A A' : Complexes W.O} (a : A ⟶ A')
    (B : Complexes W.O) :
    totalComplexMapRight W a B =
      HomologicalComplex.mapBifunctorMap a (𝟙 B)
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.O) (ComplexShape.up ℤ) :=
  DerivedPullbackTensor.totalComplexPair_map
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.O) a (𝟙 B)

/-- `Stacks.Cohomology.RelativeCupProductOnRingedTopoi.totalComplexMapLeft` is the total tensor
complex `HomologicalComplex.mapBifunctorMap (𝟙 A) b` of the pair `(𝟙 A, b)`. -/
theorem totalComplexMapLeft_eq_mapBifunctorMap (A : Complexes W.O) {B B' : Complexes W.O}
    (b : B ⟶ B') :
    totalComplexMapLeft W A b =
      HomologicalComplex.mapBifunctorMap (𝟙 A) b
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.O) (ComplexShape.up ℤ) :=
  DerivedPullbackTensor.totalComplexPair_map
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.O) (𝟙 A) b

/-- **The total tensor complex of two K-flat complexes is K-flat**, with the total tensor complex
written through `Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair`. -/
theorem kFlat_totalComplexPair (K L : Complexes W.O)
    (hK : Stacks.SheafOfModules.KFlat.KFlat W.O K)
    (hL : Stacks.SheafOfModules.KFlat.KFlat W.O L) :
    Stacks.SheafOfModules.KFlat.KFlat W.O
      ((DerivedPullbackTensor.totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.O)).obj (K, L)) :=
  kFlat_tensor_complexes W.O hK hL

/-- **The associator of total tensor complexes** for
`Stacks.SheafOfModules.DerivedMonoidal.monoidalCategoryStructComplexes`, with its source and
target written through `Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair` rather than
through `⊗`. -/
def complexAssociatorPair (K L M : Complexes W.O) :
    (DerivedPullbackTensor.totalComplexPair
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.O)).obj
        ((DerivedPullbackTensor.totalComplexPair
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.O)).obj (K, L), M) ⟶
      (DerivedPullbackTensor.totalComplexPair
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.O)).obj
        (K, (DerivedPullbackTensor.totalComplexPair
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.O)).obj (L, M)) :=
  letI := monoidalCategoryStructComplexes W.O
  (α_ K L M).hom

/-- `Stacks.Cohomology.RelativeCupProductOnRingedTopoi.complexAssociatorPair` *is* the associator
of the total tensor product of complexes. -/
theorem complexAssociatorPair_eq (K L M : Complexes W.O) :
    letI := monoidalCategoryStructComplexes W.O
    complexAssociatorPair W K L M = (α_ K L M).hom :=
  rfl

/-- The image of
`Stacks.Cohomology.RelativeCupProductOnRingedTopoi.complexAssociatorPair` in the derived category
is `Stacks.SheafOfModules.DerivedMonoidal.complexAssociatorHom`, the right-hand map of the
associativity clause of [Stacks, Tag 0FPT]. -/
theorem Q_map_complexAssociatorPair (K L M : Complexes W.O) :
    DerivedCategory.Q.map (complexAssociatorPair W K L M) = complexAssociatorHom W.O K L M :=
  rfl

/-! ### The comparison and the constraints of Tag 0FPT on one ringed topos -/

/-- **The uncurried derived tensor bifunctor on a morphism which is the identity in the second
variable is the right whiskering `Stacks.SheafOfModules.DerivedMonoidal.canonicalWhiskerRight` of
[Stacks, Tag 0FPT].** -/
theorem uncurry_derivedTensor_map_id_right {G H : DerivedModules W.O} (u : G ⟶ H)
    (Z : DerivedModules W.O) :
    (uncurriedDerivedTensor W).map (u ×ₘ 𝟙 Z) = canonicalWhiskerRight W.O u Z :=
  Stacks.Cohomology.DerivedProjectionFormula.uncurry_map_id_right
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor W.O) u Z

/-- **The uncurried derived tensor bifunctor on a morphism which is the identity in the first
variable is the left whiskering `Stacks.SheafOfModules.DerivedMonoidal.canonicalWhiskerLeft` of
[Stacks, Tag 0FPT].** -/
theorem uncurry_derivedTensor_map_id_left (G : DerivedModules W.O) {H Z : DerivedModules W.O}
    (v : H ⟶ Z) :
    (uncurriedDerivedTensor W).map (𝟙 G ×ₘ v) = canonicalWhiskerLeft W.O G v :=
  Stacks.Cohomology.DerivedProjectionFormula.uncurry_map_id_left
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor W.O) G v

/-- **The associativity constraint
`Stacks.SheafOfModules.DerivedMonoidal.canonicalAssociatorHom` of [Stacks, Tag 0FPT] is natural
in all three derived modules**, with the derived tensor bifunctor written uncurried. -/
theorem canonicalAssociatorHom_naturality {G G' G'' H H' H'' : DerivedModules W.O}
    (u : G ⟶ H) (v : G' ⟶ H') (w : G'' ⟶ H'') :
    (uncurriedDerivedTensor W).map ((uncurriedDerivedTensor W).map (u ×ₘ v) ×ₘ w) ≫
        canonicalAssociatorHom W.O H H' H'' =
      canonicalAssociatorHom W.O G G' G'' ≫
        (uncurriedDerivedTensor W).map (u ×ₘ (uncurriedDerivedTensor W).map (v ×ₘ w)) :=
  let := canonicalDerivedMonoidal W.O
  MonoidalCategory.associator_naturality u v w

/-- **The comparison of [Stacks, Tag 06YU], with its source read on the uncurried derived tensor
bifunctor and its target at the pinned spelling of the total tensor complex.** -/
def comparisonPair (K L : Complexes W.O)
    (hK : Stacks.SheafOfModules.KFlat.KFlat W.O K)
    (hL : Stacks.SheafOfModules.KFlat.KFlat W.O L) :
    (uncurriedDerivedTensor W).obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ⟶
      DerivedCategory.Q.obj
        ((DerivedPullbackTensor.totalComplexPair
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.O)).obj (K, L)) :=
  canonicalComparisonHom W.O K L hK hL

/-- `Stacks.Cohomology.RelativeCupProductOnRingedTopoi.comparisonPair` *is* the comparison of
[Stacks, Tag 06YU] at the pinned spelling of [Stacks, Tag 0FPT]. -/
theorem comparisonPair_eq (K L : Complexes W.O)
    (hK : Stacks.SheafOfModules.KFlat.KFlat W.O K)
    (hL : Stacks.SheafOfModules.KFlat.KFlat W.O L) :
    comparisonPair W K L hK hL = canonicalComparisonHom W.O K L hK hL :=
  rfl

/-- `Stacks.Cohomology.RelativeCupProductOnRingedTopoi.comparisonPair` is the `comparison` field
of the canonical derived tensor product of [Stacks, Tag 06YU]. -/
theorem comparisonPair_eq_comparison (K L : Complexes W.O)
    (hK : Stacks.SheafOfModules.KFlat.KFlat W.O K)
    (hL : Stacks.SheafOfModules.KFlat.KFlat W.O L) :
    comparisonPair W K L hK hL =
      ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct W.O).comparison
        K L hK hL).hom :=
  rfl

/-- The comparison of [Stacks, Tag 06YU] is an isomorphism on K-flat complexes, at the pinned
spelling. -/
theorem isIso_comparisonPair (K L : Complexes W.O)
    (hK : Stacks.SheafOfModules.KFlat.KFlat W.O K)
    (hL : Stacks.SheafOfModules.KFlat.KFlat W.O L) :
    IsIso (comparisonPair W K L hK hL) :=
  (canonicalComparison W.O K L hK hL).isIso_hom

/-- The comparison of [Stacks, Tag 06YU] is natural in a pair of cochain maps. -/
private theorem comparisonPair_naturality {A A' B B' : Complexes W.O} (a : A ⟶ A')
    (b : B ⟶ B') (hA : Stacks.SheafOfModules.KFlat.KFlat W.O A)
    (hA' : Stacks.SheafOfModules.KFlat.KFlat W.O A')
    (hB : Stacks.SheafOfModules.KFlat.KFlat W.O B)
    (hB' : Stacks.SheafOfModules.KFlat.KFlat W.O B') :
    (uncurriedDerivedTensor W).map (DerivedCategory.Q.map a ×ₘ DerivedCategory.Q.map b) ≫
        comparisonPair W A' B' hA' hB' =
      comparisonPair W A B hA hB ≫ DerivedCategory.Q.map
        ((DerivedPullbackTensor.totalComplexPair
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.O)).map (a ×ₘ b)) := by
  have h := (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
    W.O).comparison_naturality a b hA hA' hB hB'
  rw [DerivedPullbackTensor.totalComplexPair_map, Functor.uncurry_obj_map, Category.assoc]
  exact h

/-- **The comparison of [Stacks, Tag 06YU] is natural in a cochain map of the first variable.** -/
theorem comparisonPair_naturality_right {A A' B : Complexes W.O} (a : A ⟶ A')
    (hA : Stacks.SheafOfModules.KFlat.KFlat W.O A)
    (hA' : Stacks.SheafOfModules.KFlat.KFlat W.O A')
    (hB : Stacks.SheafOfModules.KFlat.KFlat W.O B) :
    (uncurriedDerivedTensor W).map
        (DerivedCategory.Q.map a ×ₘ 𝟙 (DerivedCategory.Q.obj B)) ≫
        comparisonPair W A' B hA' hB =
      comparisonPair W A B hA hB ≫
        DerivedCategory.Q.map (totalComplexMapRight W a B) := by
  simpa [totalComplexMapRight] using comparisonPair_naturality W a (𝟙 B) hA hA' hB hB

/-- **The comparison of [Stacks, Tag 06YU] is natural in a cochain map of the second
variable.** -/
theorem comparisonPair_naturality_left {A B B' : Complexes W.O} (b : B ⟶ B')
    (hA : Stacks.SheafOfModules.KFlat.KFlat W.O A)
    (hB : Stacks.SheafOfModules.KFlat.KFlat W.O B)
    (hB' : Stacks.SheafOfModules.KFlat.KFlat W.O B') :
    (uncurriedDerivedTensor W).map
        (𝟙 (DerivedCategory.Q.obj A) ×ₘ DerivedCategory.Q.map b) ≫
        comparisonPair W A B' hA hB' =
      comparisonPair W A B hA hB ≫
        DerivedCategory.Q.map (totalComplexMapLeft W A b) := by
  simpa [totalComplexMapLeft] using comparisonPair_naturality W (𝟙 A) b hA hA hB hB'

/-- **The associativity clause of [Stacks, Tag 0FPT] with the two whiskerings written as the
uncurried bifunctor applied to a pair and every total-complex term at the pinned spelling**, as a
proposition about K-flat complexes `K`, `L`, `M`. -/
def UncurriedComparisonAssociator (K L M : Complexes W.O)
    (hK : Stacks.SheafOfModules.KFlat.KFlat W.O K)
    (hL : Stacks.SheafOfModules.KFlat.KFlat W.O L)
    (hM : Stacks.SheafOfModules.KFlat.KFlat W.O M) : Prop :=
  (uncurriedDerivedTensor W).map
        (comparisonPair W K L hK hL ×ₘ 𝟙 (DerivedCategory.Q.obj M)) ≫
      comparisonPair W
          ((DerivedPullbackTensor.totalComplexPair
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.O)).obj (K, L)) M
          (kFlat_totalComplexPair W K L hK hL) hM ≫
        DerivedCategory.Q.map (complexAssociatorPair W K L M) =
    canonicalAssociatorHom W.O (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
        (DerivedCategory.Q.obj M) ≫
      (uncurriedDerivedTensor W).map
          (𝟙 (DerivedCategory.Q.obj K) ×ₘ comparisonPair W L M hL hM) ≫
        comparisonPair W K
          ((DerivedPullbackTensor.totalComplexPair
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.O)).obj (L, M)) hK
          (kFlat_totalComplexPair W L M hL hM)

/-- **The associativity clause of [Stacks, Tag 0FPT], uncurried and pinned**: the equation
`Stacks.Cohomology.RelativeCupProductOnRingedTopoi.UncurriedComparisonAssociator` holds for all
K-flat complexes `K`, `L`, `M`. -/
theorem canonicalComparison_associator_uncurried (K L M : Complexes W.O)
    (hK : Stacks.SheafOfModules.KFlat.KFlat W.O K)
    (hL : Stacks.SheafOfModules.KFlat.KFlat W.O L)
    (hM : Stacks.SheafOfModules.KFlat.KFlat W.O M) :
    UncurriedComparisonAssociator W K L M hK hL hM := by
  unfold UncurriedComparisonAssociator
  rw [uncurry_derivedTensor_map_id_right, uncurry_derivedTensor_map_id_left]
  exact canonicalComparison_associator W.O K L M hK hL hM

end Pinned

end Stacks.Cohomology.RelativeCupProductOnRingedTopoi

end
