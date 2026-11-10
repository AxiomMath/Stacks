module

public import StacksFrontier.CategoryTheory.BifunctorComparisonAssocModels
public import StacksFrontier.CategoryTheory.BifunctorComparisonConstraints
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorReseatConstraints
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.KFlatTripleDescent
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComplexAssociator
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComparisonBraiding
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorIsoAlongAComposite
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormula

/-!
# The derived pullback–tensor comparison is associative

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces.  The comparison of
[Stacks, Tag 079U],

`Lf^*(K ⊗^L_{𝒪_Y} L) ≅ Lf^*K ⊗^L_{𝒪_X} Lf^*L`,

carries the associativity constraint of the monoidal derived category of [Stacks, Tag 0FPT] on
`D(𝒪_Y)` to the one on `D(𝒪_X)`: `Lf^*` is a *monoidal* functor for the derived tensor product of
[Stacks, Tag 06YU], and not merely a functor with a comparison.

This is the fusion of the three inputs that were available separately.  On a triple of K-flat
complexes the comparison is computed by the ordinary total tensor complex
(`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_hom_app_comp_derivedToTensor`),
the associativity constraint of Tag 0FPT is computed there by the associator of complexes
(`Stacks.SheafOfModules.DerivedMonoidal.canonicalComparison_associator`), and the comparison of
total tensor complexes of [Stacks, Tag 01CD] is compatible with that associator
(`Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexIso_associator`).  The diagram
chase joining them is `CategoryTheory.bifunctor_comparison_assoc_of_models`, applied through the
bundles of `CategoryTheory.bifunctor_comparison_assoc_of_bundles`, and the passage from K-flat
representatives to all of `D(𝒪_Y)³` is
`Stacks.Cohomology.DerivedPullbackTensor.natTrans_ext_of_kFlat₃`.

## Main results

* `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_associator_app_of_kFlat`: the
  compatibility at a triple of K-flat complexes.
* `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_associator`: **the
  compatibility for arbitrary `M, N, R ∈ D(𝒪_Y)`**, with no finiteness, flatness or
  quasi-coherence hypothesis.

## Implementation notes

*Where the content is.*  Not here.  Each of the three inputs above is proved, the chase that
joins them is carried out for an arbitrary functor and arbitrary bifunctors in
`StacksFrontier.CategoryTheory.BifunctorComparisonConstraints`, and this file supplies the
instantiation: the comparison of Tag 06YU read at the pinned spelling `comparisonPair` and in
the uncurried form the chase consumes, the naturality of the associativity constraint, and the
complex-level identity carried into the derived category along
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackNatTrans`.

*The two models of the triple tensor product.*  The model identification of Tag 079U at a pair of
complexes lands in `Q(f^*Tot(K ⊗ L))`, while the associativity square needs it against
`Q(Tot(f^*K ⊗ f^*L))`.  `CategoryTheory.bifunctor_comparison_model_comp_left` and `_right` re-read
it against the further model, along the naturality of the comparison of Tag 06YU in one variable
(`comparisonPair_naturality_left`, `_right`); what is left over is the identity
`pullbackTensorModel_assoc_pair`, which is the associativity coherence of the comparison of
Tag 01CD pushed into the derived category.

*The inverse direction of the comparison of total complexes.*
`Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexIso_associator` is stated for the
tensorator `pullbackTensorComplexMu`, which points `f^*K ⊗ f^*L ⟶ f^*(K ⊗ L)`; the model
identification of Tag 079U has the *other* direction.
`Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexMuHom` names that direction, and
`pullbackTensorComplexIso_associator_hom` is the coherence read on it: all six arrows of the
coherence are isomorphisms, so the identity transposes.  No total complex is taken apart.

*Pinning.*  The two spellings of the total tensor complex — `⊗` of the monoidal structure on
complexes, which the associator and the tensorator are written at, and
`Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair`, which the model identification of
Tag 079U uses — are the same object, but the identification is a conversion the
`HomologicalComplex` instance arguments make expensive and `getColimitCocone` is not exposed, so
it cannot be finished by unfolding.  `complexAssociatorPair`, `totalComplexMapRight`,
`totalComplexMapLeft` and `comparisonPair` pay for it **once** each, with a `rfl` lemma or a
degreewise identification recording what they are, and every statement downstream of them is
written so that no further occurrence of the identification is needed.  For the same reason the
long equations — the associativity clause of Tag 0FPT in uncurried form, the two re-read model
identifications, and the compatibility at a triple of K-flat complexes — have their statements
in `Prop`-valued `def`s, separate from their proofs.  The same device carries the five bundles
of the chase: `AssocLaws`, `AssocPairs`, `AssocTripleLeft`, `AssocTripleRight` and `AssocLink`
name the objects and maps, and the theorem of each name proves its fields.

*Seating.*  The instances are those of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComplexAssociator`,
re-attributed rather than re-declared: a second copy of any of them would be a second instance
term, and the statements of the files this one builds on mention the first.

## References

* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  TopologicalSpace
open Stacks.SheafOfModules.KFlatPullback (kFlat_modulePullback_unconditional)
open scoped CategoryTheory.Prod
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.SheafOfModules.DerivedMonoidal

namespace Stacks.Cohomology.DerivedPullbackTensor

universe u

section Pinned

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] abelianModulesSheafTensor monoidalModules symmetricModules
  monoidalPreadditiveModules monoidalClosedModules hasTensorModules monoidalComplexes
  modulePullback_preservesAntidiagonalCoproducts liftMonoidal CochainComplex.symmetricCategory

-- `TopCat.Sheaf` and `TopCat.Presheaf.IsSheaf` join the list because the canonical tensor
-- product's ring sheaf is `Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf`, whose argument has
-- type `TopCat.Sheaf CommRingCat Z.carrier` while `ringSheaf` asks for a
-- `CategoryTheory.Sheaf (Opens.grothendieckTopology Z.carrier) CommRingCat`.  The two are the
-- same type, but only once `TopCat.Sheaf` is unfolded, so without the attribute the statements
-- here are ill-typed at `implicit` transparency and `rw` reports that it did not find a pattern
-- the goal visibly contains.
--
-- `structureSheafRing` is deliberately *not* in the list.  It is globally
-- `@[instance_reducible]`, a status that already unfolds at `implicit` transparency, so naming
-- it here adds nothing; and `[implicit_reducible]` is the strictly higher status, so naming it
-- here would move it off `instances` transparency and hide it from typeclass *search* -- the
-- one thing its own declaration site asks for, the instances on `SheafOfModules R` being found
-- only while `R` reduces to a closed term.
attribute [local implicit_reducible]
  StacksDraft.KFlat.modulePullback CategoryTheory.sheafCompose AlgebraicGeometry.SheafedSpace.sheaf
  TopCat.Sheaf TopCat.Presheaf.IsSheaf Stacks.SheafOfModules.Tensor.ringSheaf

/-- The image of a three-fold composite under a functor.  It is used below on `DerivedCategory.Q`
applied to a coherence of complexes, where splitting the composite inside the proof would cost
more than the declaration can afford. -/
private lemma map_comp₃ {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B B' E : C} (a : A ⟶ B) (b : B ⟶ B') (c : B' ⟶ E) :
    F.map (a ≫ b ≫ c) = F.map a ≫ F.map b ≫ F.map c := by
  rw [F.map_comp, F.map_comp]

/-! ### The total tensor complex of a one-sided cochain map -/

section TotalComplexMaps

variable (Z : RingedSpace.{u, u})

/-- **The total tensor complex of a cochain map and an identity in the second variable**, pinned.
It is the morphism the naturality of the comparison of Tag 06YU in its first variable produces,
and it is ascribed here at the `Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair`
spelling of its source and target, so that the statements that mention it do not have to
elaborate the total tensor complex of a pair of morphisms against the `⊗` spelling. -/
def totalComplexMapRight
    {A A' : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ}
    (a : A ⟶ A')
    (B : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ) :
    (totalComplexPair
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf)).obj (A, B) ⟶
      (totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf)).obj (A', B) :=
  (totalComplexPair
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf)).map (a ×ₘ 𝟙 B)

/-- **The total tensor complex of an identity and a cochain map in the second variable**, pinned;
the companion of `totalComplexMapRight`. -/
def totalComplexMapLeft
    (A : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ)
    {B B' : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ}
    (b : B ⟶ B') :
    (totalComplexPair
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf)).obj (A, B) ⟶
      (totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf)).obj (A, B') :=
  (totalComplexPair
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf)).map (𝟙 A ×ₘ b)

/-- `Stacks.Cohomology.DerivedPullbackTensor.totalComplexMapRight` is the right whiskering of the
monoidal structure on complexes.  This is not `rfl`: `totalComplexPair` is built from
`Stacks.SheafOfModules.Tensor.sheafTensor` and the whiskering from
`CategoryTheory.MonoidalCategory.curriedTensor`, and the two bifunctors agree only after the
re-seating of the monoidal structure on `Mod(𝒪_Z)` is unfolded, which is why the identification
is made degreewise. -/
theorem totalComplexMapRight_eq_whiskerRight
    {A A' : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ}
    (a : A ⟶ A')
    (B : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ) :
    totalComplexMapRight Z a B = a ▷ B :=
  HomologicalComplex.hom_ext _ _ fun n =>
    (congrArg (fun φ => HomologicalComplex.Hom.f φ n)
        (totalComplexPair_map
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf) a (𝟙 B))).trans
      (HomologicalComplex.Monoidal.whiskerRight_f a B n).symm

/-- `Stacks.Cohomology.DerivedPullbackTensor.totalComplexMapLeft` is the left whiskering of the
monoidal structure on complexes; the companion of `totalComplexMapRight_eq_whiskerRight`. -/
theorem totalComplexMapLeft_eq_whiskerLeft
    (A : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ)
    {B B' : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ}
    (b : B ⟶ B') :
    totalComplexMapLeft Z A b = A ◁ b :=
  HomologicalComplex.hom_ext _ _ fun n =>
    (congrArg (fun φ => HomologicalComplex.Hom.f φ n)
        (totalComplexPair_map
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf) (𝟙 A) b)).trans
      (HomologicalComplex.Monoidal.whiskerLeft_f A b n).symm

/-- **The associator of total tensor complexes**, with its source and target written through
`Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair` rather than through `⊗`.

The two spellings of the total tensor complex are the same object, but the identification is a
conversion the `HomologicalComplex` instance arguments make expensive, and `getColimitCocone` is
not exposed, so it cannot be finished by unfolding.  Everything below is written at the
`totalComplexPair` spelling, which is the one the model identification of Tag 079U uses, and
this definition pays for the identification **once**. -/
def complexAssociatorPair
    (K L M : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ) :
    (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf)).obj
        ((totalComplexPair
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf)).obj (K, L), M) ⟶
      (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf)).obj
        (K, (totalComplexPair
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf)).obj (L, M)) :=
  (α_ K L M).hom

/-- `Stacks.Cohomology.DerivedPullbackTensor.complexAssociatorPair` is the associator of the
total tensor product of complexes. -/
theorem complexAssociatorPair_eq
    (K L M : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ) :
    complexAssociatorPair Z K L M = (α_ K L M).hom :=
  rfl

/-- **K-flatness of a total tensor complex of K-flat complexes**, at the `totalComplexPair`
spelling.  `Stacks.Cohomology.DerivedPullbackTensor.kFlat_tensorComplex` concludes at the
`Stacks.SheafOfModules.Tensor.tensorComplex` spelling; the two are definitionally equal, but the
conversion is expensive enough that the statements below cannot afford one occurrence of it each,
so it is done once, here. -/
theorem kFlat_totalComplexPair
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z K)
    (hL : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z L) :
    AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z
      ((totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf)).obj (K, L)) :=
  kFlat_tensorComplex Z K L hK hL

end TotalComplexMaps

/-! ### The comparison and the constraints of Tag 0FPT on one ringed space -/

section Comparison

variable (Z : RingedSpace.{u, u})
  [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The uncurried derived tensor bifunctor on a morphism which is the identity in the second
variable is the right whiskering of Tag 0FPT.**  The coherence clauses of Tag 0FPT are written
with `Stacks.SheafOfModules.DerivedMonoidal.canonicalWhiskerRight`, while the comparison of
Tag 079U is a transformation of the uncurried bifunctor; this is the bridge. -/
theorem uncurry_derivedTensor_map_id_right
    {G H : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z)}
    (u : G ⟶ H)
    (W : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z)) :
    (Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf)).map
        (u ×ₘ 𝟙 W) =
      canonicalWhiskerRight Z.sheaf u W :=
  Stacks.Cohomology.DerivedProjectionFormula.uncurry_map_id_right
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf) u W

/-- **The uncurried derived tensor bifunctor on a morphism which is the identity in the first
variable is the left whiskering of Tag 0FPT**; the companion of
`uncurry_derivedTensor_map_id_right`. -/
theorem uncurry_derivedTensor_map_id_left
    (G : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z))
    {H W : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z)}
    (v : H ⟶ W) :
    (Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf)).map
        (𝟙 G ×ₘ v) =
      canonicalWhiskerLeft Z.sheaf G v :=
  Stacks.Cohomology.DerivedProjectionFormula.uncurry_map_id_left
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf) G v

/-- **The associativity constraint of Tag 0FPT is natural in all three derived modules**, at the
pinned spelling `Stacks.SheafOfModules.DerivedMonoidal.canonicalAssociatorHom` and with the
bifunctor written uncurried, which is the shape the comparison of Tag 079U is a transformation
of. -/
theorem canonicalAssociatorHom_naturality
    {G G' G'' H H' H'' :
      DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z)}
    (u : G ⟶ H) (v : G' ⟶ H') (w : G'' ⟶ H'') :
    (Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf)).map
        ((Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf)).map
            (u ×ₘ v) ×ₘ w) ≫
        canonicalAssociatorHom Z.sheaf H H' H'' =
      canonicalAssociatorHom Z.sheaf G G' G'' ≫
        (Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf)).map
            (u ×ₘ (Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf)).map
                (v ×ₘ w)) :=
  letI := canonicalDerivedMonoidal Z.sheaf
  MonoidalCategory.associator_naturality u v w

/-- **The canonical map to the ordinary total tensor complex is natural in a cochain map of the
first variable.**  This is the naturality field of Tag 06YU, read on
`Stacks.Cohomology.DerivedPullbackTensor.derivedToTensorNatTrans` with the identity component of
the pair reduced. -/
theorem derivedToTensorNatTrans_naturality_right
    {A A' B : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ}
    (a : A ⟶ A') :
    (Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf)).map
        (DerivedCategory.Q.map a ×ₘ 𝟙 (DerivedCategory.Q.obj B)) ≫
        (derivedToTensorNatTrans Z).app (A', B) =
      (derivedToTensorNatTrans Z).app (A, B) ≫
        DerivedCategory.Q.map (totalComplexMapRight Z a B) :=
  (congrArg
        (fun t => (Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf)).map
            (DerivedCategory.Q.map a ×ₘ t) ≫ (derivedToTensorNatTrans Z).app (A', B))
        (DerivedCategory.Q.map_id B)).symm.trans
    ((derivedToTensorNatTrans Z).naturality (a ×ₘ 𝟙 B))

/-- **The canonical map to the ordinary total tensor complex is natural in a cochain map of the
second variable**; the companion of `derivedToTensorNatTrans_naturality_right`. -/
theorem derivedToTensorNatTrans_naturality_left
    {A B B' : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ}
    (b : B ⟶ B') :
    (Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf)).map
        (𝟙 (DerivedCategory.Q.obj A) ×ₘ DerivedCategory.Q.map b) ≫
        (derivedToTensorNatTrans Z).app (A, B') =
      (derivedToTensorNatTrans Z).app (A, B) ≫
        DerivedCategory.Q.map (totalComplexMapLeft Z A b) :=
  (congrArg
        (fun t => (Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf)).map
            (t ×ₘ DerivedCategory.Q.map b) ≫ (derivedToTensorNatTrans Z).app (A, B'))
        (DerivedCategory.Q.map_id A)).symm.trans
    ((derivedToTensorNatTrans Z).naturality (𝟙 A ×ₘ b))

/-- **The comparison of Tag 06YU, with its target at the `totalComplexPair` spelling of the
total tensor complex.**

`Stacks.SheafOfModules.DerivedMonoidal.canonicalComparisonHom` lands in `Q(K ⊗ L)`, while
everything the comparison of Tag 079U is known against is written at the `totalComplexPair`
spelling; the two objects are the same but the identification is an expensive conversion.  This
definition pays for it **once**, and every statement below is written so that no further
occurrence of it is needed. -/
def comparisonPair
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z K)
    (hL : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z L) :
    (Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf)).obj
        (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ⟶
      DerivedCategory.Q.obj
        ((totalComplexPair
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf)).obj (K, L)) :=
  canonicalComparisonHom Z.sheaf K L hK hL

/-- `Stacks.Cohomology.DerivedPullbackTensor.comparisonPair` *is* the comparison of Tag 06YU at
the pinned spelling of Tag 0FPT. -/
theorem comparisonPair_eq
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z K)
    (hL : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z L) :
    comparisonPair Z K L hK hL = canonicalComparisonHom Z.sheaf K L hK hL :=
  rfl

/-- `Stacks.Cohomology.DerivedPullbackTensor.comparisonPair` is the canonical map to the ordinary
total tensor complex of Tag 06YU. -/
theorem comparisonPair_eq_app
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z K)
    (hL : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z L) :
    comparisonPair Z K L hK hL = (derivedToTensorNatTrans Z).app (K, L) :=
  (derivedToTensorNatTrans_app_eq_canonicalComparisonHom Z K L hK hL).symm

/-- The comparison of Tag 06YU is an isomorphism on K-flat complexes, at the pinned spelling. -/
theorem isIso_comparisonPair
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z K)
    (hL : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z L) :
    IsIso (comparisonPair Z K L hK hL) :=
  isIso_canonicalComparisonHom Z K L hK hL

/-- **The comparison of Tag 06YU is natural in a cochain map of the first variable.** -/
theorem comparisonPair_naturality_right
    {A A' B : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ}
    (a : A ⟶ A')
    (hA : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z A)
    (hA' : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z A')
    (hB : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z B) :
    (Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf)).map
        (DerivedCategory.Q.map a ×ₘ 𝟙 (DerivedCategory.Q.obj B)) ≫
        comparisonPair Z A' B hA' hB =
      comparisonPair Z A B hA hB ≫
        DerivedCategory.Q.map (totalComplexMapRight Z a B) := by
  rw [comparisonPair_eq_app, comparisonPair_eq_app]
  exact derivedToTensorNatTrans_naturality_right Z a

/-- **The comparison of Tag 06YU is natural in a cochain map of the second variable.** -/
theorem comparisonPair_naturality_left
    {A B B' : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ}
    (b : B ⟶ B')
    (hA : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z A)
    (hB : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z B)
    (hB' : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z B') :
    (Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf)).map
        (𝟙 (DerivedCategory.Q.obj A) ×ₘ DerivedCategory.Q.map b) ≫
        comparisonPair Z A B' hA hB' =
      comparisonPair Z A B hA hB ≫
        DerivedCategory.Q.map (totalComplexMapLeft Z A b) := by
  rw [comparisonPair_eq_app, comparisonPair_eq_app]
  exact derivedToTensorNatTrans_naturality_left Z b

/-- **The associativity clause of Tag 0FPT with the two whiskerings written as the uncurried
bifunctor applied to a pair**, which is the shape the diagram chase of
`CategoryTheory.bifunctor_comparison_assoc_of_models` consumes.

The statement is a `def` rather than being inlined in the theorem below for a mechanical reason:
elaborating it and then the proof in one declaration exceeds the heartbeat budget. -/
def UncurriedComparisonAssociator
    (K L M : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z K)
    (hL : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z L)
    (hM : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z M) : Prop :=
  (Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf)).map
        (comparisonPair Z K L hK hL ×ₘ 𝟙 (DerivedCategory.Q.obj M)) ≫
      comparisonPair Z
          ((totalComplexPair
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf)).obj (K, L)) M
          (kFlat_totalComplexPair Z K L hK hL) hM ≫
        DerivedCategory.Q.map (complexAssociatorPair Z K L M) =
    canonicalAssociatorHom Z.sheaf (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
        (DerivedCategory.Q.obj M) ≫
      (Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf)).map
          (𝟙 (DerivedCategory.Q.obj K) ×ₘ comparisonPair Z L M hL hM) ≫
        comparisonPair Z K
          ((totalComplexPair
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf)).obj (L, M)) hK
          (kFlat_totalComplexPair Z L M hL hM)

/-- **The associativity clause of Tag 0FPT, uncurried.**  This is
`Stacks.SheafOfModules.DerivedMonoidal.canonicalComparison_associator` with the two whiskerings
rewritten through `uncurry_derivedTensor_map_id_right` and `uncurry_derivedTensor_map_id_left`;
the equation it proves is spelled out in `UncurriedComparisonAssociator`. -/
theorem canonicalComparison_associator_uncurried
    (K L M : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z K)
    (hL : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z L)
    (hM : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z M) :
    UncurriedComparisonAssociator Z K L M hK hL hM := by
  have h := canonicalComparison_associator Z.sheaf K L M hK hL hM
  unfold UncurriedComparisonAssociator
  rw [uncurry_derivedTensor_map_id_right, uncurry_derivedTensor_map_id_left]
  exact h

end Comparison

/-! ### The comparison of total tensor complexes, in the direction Tag 079U presents -/

section Complexes

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **The comparison `f^*Tot(K ⊗ L) ⟶ Tot(f^*K ⊗ f^*L)` of Tag 01CD is compatible with the
associator of total tensor complexes.**  This is
`Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexIso_associator`, which is stated
for the tensorator, read on the inverse comparison: all six arrows of the coherence are
isomorphisms, so the identity transposes. -/
theorem pullbackTensorComplexIso_associator_hom
    (K L M : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    pullbackTensorComplexMuHom f (K ⊗ L) M ≫
        pullbackTensorComplexMuHom f K L ▷ (pullbackComplex f).obj M ≫
          (α_ ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
            ((pullbackComplex f).obj M)).hom =
      (pullbackComplex f).map (α_ K L M).hom ≫
        pullbackTensorComplexMuHom f K (L ⊗ M) ≫
          (pullbackComplex f).obj K ◁ pullbackTensorComplexMuHom f L M := by
  have h := pullbackTensorComplexIso_associator f K L M
  have hu : pullbackTensorComplexMuHom f K L ▷ (pullbackComplex f).obj M ≫
      pullbackTensorComplexMu f K L ▷ (pullbackComplex f).obj M = 𝟙 _ := by
    rw [← MonoidalCategory.comp_whiskerRight, pullbackTensorComplexMuHom_comp_mu,
      MonoidalCategory.id_whiskerRight]
  have hv : pullbackTensorComplexMuHom f (K ⊗ L) M ≫ pullbackTensorComplexMu f (K ⊗ L) M = 𝟙 _ :=
    pullbackTensorComplexMuHom_comp_mu f (K ⊗ L) M
  have hq : (pullbackComplex f).obj K ◁ pullbackTensorComplexMu f L M ≫
      (pullbackComplex f).obj K ◁ pullbackTensorComplexMuHom f L M = 𝟙 _ := by
    rw [← MonoidalCategory.whiskerLeft_comp, mu_comp_pullbackTensorComplexMuHom,
      MonoidalCategory.whiskerLeft_id]
  have hr : pullbackTensorComplexMu f K (L ⊗ M) ≫ pullbackTensorComplexMuHom f K (L ⊗ M) = 𝟙 _ :=
    mu_comp_pullbackTensorComplexMuHom f K (L ⊗ M)
  have h₂ : pullbackTensorComplexMu f K L ▷ (pullbackComplex f).obj M ≫
        pullbackTensorComplexMu f (K ⊗ L) M ≫
          (pullbackComplex f).map (α_ K L M).hom ≫
            pullbackTensorComplexMuHom f K (L ⊗ M) ≫
              (pullbackComplex f).obj K ◁ pullbackTensorComplexMuHom f L M =
      (α_ ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
        ((pullbackComplex f).obj M)).hom := by
    rw [show pullbackTensorComplexMu f K L ▷ (pullbackComplex f).obj M ≫
          pullbackTensorComplexMu f (K ⊗ L) M ≫
            (pullbackComplex f).map (α_ K L M).hom ≫
              pullbackTensorComplexMuHom f K (L ⊗ M) ≫
                (pullbackComplex f).obj K ◁ pullbackTensorComplexMuHom f L M =
        (pullbackTensorComplexMu f K L ▷ (pullbackComplex f).obj M ≫
            pullbackTensorComplexMu f (K ⊗ L) M ≫
              (pullbackComplex f).map (α_ K L M).hom) ≫
          pullbackTensorComplexMuHom f K (L ⊗ M) ≫
            (pullbackComplex f).obj K ◁ pullbackTensorComplexMuHom f L M from by
      simp only [Category.assoc], h]
    simp only [Category.assoc]
    rw [reassoc_of% hr, hq, Category.comp_id]
  rw [← h₂, reassoc_of% hu, reassoc_of% hv]

/-- **The left-hand side of the coherence of Tag 01CD, read at the `totalComplexPair`
spelling.**  Splitting the identification of the two spellings into the two sides of the
coherence separately is what keeps each declaration inside the heartbeat budget. -/
theorem pullbackTensorComplexIso_associator_lhs
    (K L M : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    (pullbackTensorComplexNatIso f).hom.app
          ((totalComplexPair
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).obj (K, L), M) ≫
        totalComplexMapRight X ((pullbackTensorComplexNatIso f).hom.app (K, L))
            ((pullbackComplex f).obj M) ≫
          complexAssociatorPair X ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
            ((pullbackComplex f).obj M) =
      pullbackTensorComplexMuHom f (K ⊗ L) M ≫
        pullbackTensorComplexMuHom f K L ▷ (pullbackComplex f).obj M ≫
          (α_ ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
            ((pullbackComplex f).obj M)).hom := by
  rw [totalComplexMapRight_eq_whiskerRight]
  rfl

/-- **The right-hand side of the coherence of Tag 01CD, read at the `totalComplexPair`
spelling**; the companion of `pullbackTensorComplexIso_associator_lhs`. -/
theorem pullbackTensorComplexIso_associator_rhs
    (K L M : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    (pullbackComplex f).map (complexAssociatorPair Y K L M) ≫
        (pullbackTensorComplexNatIso f).hom.app
            (K, (totalComplexPair
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).obj
              (L, M)) ≫
          totalComplexMapLeft X ((pullbackComplex f).obj K)
            ((pullbackTensorComplexNatIso f).hom.app (L, M)) =
      (pullbackComplex f).map (α_ K L M).hom ≫
        pullbackTensorComplexMuHom f K (L ⊗ M) ≫
          (pullbackComplex f).obj K ◁ pullbackTensorComplexMuHom f L M := by
  rw [totalComplexMapLeft_eq_whiskerLeft]
  rfl

/-- **The comparison of Tag 01CD is compatible with the associator**, with every term written at
the `totalComplexPair` spelling of the total tensor complex.  This is
`pullbackTensorComplexIso_associator_hom` read through
`pullbackTensorComplexIso_associator_lhs` and `pullbackTensorComplexIso_associator_rhs`, and
nothing below mentions `⊗`. -/
theorem pullbackTensorComplexIso_associator_pair
    (K L M : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    (pullbackTensorComplexNatIso f).hom.app
          ((totalComplexPair
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).obj (K, L), M) ≫
        totalComplexMapRight X ((pullbackTensorComplexNatIso f).hom.app (K, L))
            ((pullbackComplex f).obj M) ≫
          complexAssociatorPair X ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
            ((pullbackComplex f).obj M) =
      (pullbackComplex f).map (complexAssociatorPair Y K L M) ≫
        (pullbackTensorComplexNatIso f).hom.app
            (K, (totalComplexPair
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).obj
              (L, M)) ≫
          totalComplexMapLeft X ((pullbackComplex f).obj K)
            ((pullbackTensorComplexNatIso f).hom.app (L, M)) :=
  (pullbackTensorComplexIso_associator_lhs f K L M).trans
    ((pullbackTensorComplexIso_associator_hom f K L M).trans
      (pullbackTensorComplexIso_associator_rhs f K L M).symm)

/-- `pullbackTensorComplexIso_associator_pair` in the derived category, with the three factors of
each side carried across `DerivedCategory.Q` separately.  Splitting this off keeps the
declaration that uses it inside the heartbeat budget. -/
theorem pullbackTensorComplexIso_associator_pair_Q
    (K L M : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    DerivedCategory.Q.map
          ((pullbackTensorComplexNatIso f).hom.app
            ((totalComplexPair
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).obj (K, L),
              M)) ≫
        DerivedCategory.Q.map
            (totalComplexMapRight X ((pullbackTensorComplexNatIso f).hom.app (K, L))
              ((pullbackComplex f).obj M)) ≫
          DerivedCategory.Q.map
            (complexAssociatorPair X ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
              ((pullbackComplex f).obj M)) =
      DerivedCategory.Q.map ((pullbackComplex f).map (complexAssociatorPair Y K L M)) ≫
        DerivedCategory.Q.map
            ((pullbackTensorComplexNatIso f).hom.app
              (K, (totalComplexPair
                (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).obj
                (L, M))) ≫
          DerivedCategory.Q.map
            (totalComplexMapLeft X ((pullbackComplex f).obj K)
              ((pullbackTensorComplexNatIso f).hom.app (L, M))) :=
  (map_comp₃ DerivedCategory.Q _ _ _).symm.trans
    ((congrArg DerivedCategory.Q.map
        (pullbackTensorComplexIso_associator_pair f K L M)).trans
      (map_comp₃ DerivedCategory.Q _ _ _))

end Complexes

/-! ### The compatibility on K-flat representatives -/

section KFlat

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The model of `Lf^*(QK ⊗^L QL)` carries the associator of complexes to the associator of
complexes**, at the `totalComplexPair` spelling.  The derived pullback of a complex is natural,
and the comparison of total tensor complexes is compatible with the associator
(`pullbackTensorComplexIso_associator_pair`).  This is the identity linking the two models of the
triple tensor product that the diagram chase asks for. -/
theorem pullbackTensorModel_assoc_pair
    (K L M : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    (pullbackTensorModel f
            ((totalComplexPair
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).obj (K, L)) M ≫
          DerivedCategory.Q.map
            (totalComplexMapRight X ((pullbackTensorComplexNatIso f).hom.app (K, L))
              ((pullbackComplex f).obj M))) ≫
        DerivedCategory.Q.map
          (complexAssociatorPair X ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
            ((pullbackComplex f).obj M)) =
      (derivedPullback f).map
          (DerivedCategory.Q.map (complexAssociatorPair Y K L M)) ≫
        (pullbackTensorModel f K
              ((totalComplexPair
                (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).obj
                (L, M)) ≫
          DerivedCategory.Q.map
            (totalComplexMapLeft X ((pullbackComplex f).obj K)
              ((pullbackTensorComplexNatIso f).hom.app (L, M)))) := by
  have hnat := (derivedPullbackNatTrans f).naturality (complexAssociatorPair Y K L M)
  dsimp only [pullbackTensorModel]
  simp only [Category.assoc]
  rw [pullbackTensorComplexIso_associator_pair_Q f K L M, reassoc_of% hnat]

/-- **The model identification of Tag 079U at a pair of K-flat complexes**, with the comparison
of Tag 06YU at the pinned spelling `comparisonPair`.  This is
`derivedPullbackTensorIso_hom_app_comp_canonicalComparisonHom`, read so that both sides are
written at the `totalComplexPair` spelling of the total tensor complex. -/
theorem derivedPullbackTensorIso_hom_app_comp_comparisonPair
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y K)
    (hL : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y L) :
    (derivedPullbackTensorIso f).hom.app
          (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≫
        (Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)).map
            ((derivedPullbackNatTrans f).app K ×ₘ (derivedPullbackNatTrans f).app L) ≫
          comparisonPair X ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
            (kFlat_modulePullback_unconditional f K hK)
            (kFlat_modulePullback_unconditional f L hL) =
      (derivedPullback f).map (comparisonPair Y K L hK hL) ≫ pullbackTensorModel f K L :=
  derivedPullbackTensorIso_hom_app_comp_canonicalComparisonHom f K L hK hL

/-- The statement of `derivedPullbackTensorIso_hom_app_comp_comparisonPair_left`, as a
`Prop`-valued `def` so that it and the proof term are elaborated in separate
declarations. -/
def ModelIdentificationLeft
    (K L M : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y K)
    (hL : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y L)
    (hM : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y M) : Prop :=
    (derivedPullbackTensorIso f).hom.app
          (DerivedCategory.Q.obj
            ((totalComplexPair
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).obj (K, L)),
              DerivedCategory.Q.obj M) ≫
        (Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)).map
            (pullbackTensorModel f K L ×ₘ (derivedPullbackNatTrans f).app M) ≫
          comparisonPair X
            ((totalComplexPair
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)).obj
              ((pullbackComplex f).obj K, (pullbackComplex f).obj L))
            ((pullbackComplex f).obj M)
            (kFlat_totalComplexPair X ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
              (kFlat_modulePullback_unconditional f K hK)
              (kFlat_modulePullback_unconditional f L hL))
            (kFlat_modulePullback_unconditional f M hM) =
      (derivedPullback f).map
          (comparisonPair Y
            ((totalComplexPair
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).obj (K, L)) M
            (kFlat_totalComplexPair Y K L hK hL) hM) ≫
        (pullbackTensorModel f
            ((totalComplexPair
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).obj (K, L)) M ≫
          DerivedCategory.Q.map
            (totalComplexMapRight X ((pullbackTensorComplexNatIso f).hom.app (K, L))
              ((pullbackComplex f).obj M)))

/-- **The model identification of Tag 079U at the pair `(Tot(K ⊗ L), M)`, re-read against the
model `Tot(f^*K ⊗ f^*L)` of the first factor.**  The model identification itself lands in
`Q(f^*Tot(K ⊗ L))`; the associativity square needs it against `Q(Tot(f^*K ⊗ f^*L))`, and
`CategoryTheory.bifunctor_comparison_model_comp_left` re-reads it there along the naturality of
the comparison of Tag 06YU in its first variable. -/
theorem derivedPullbackTensorIso_hom_app_comp_comparisonPair_left
    (K L M : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y K)
    (hL : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y L)
    (hM : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y M) :
    ModelIdentificationLeft f K L M hK hL hM :=
  bifunctor_comparison_model_comp_left
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf))
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf))
    (derivedPullbackTensorIso f).hom
    (derivedPullbackTensorIso_hom_app_comp_comparisonPair f
      ((totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).obj (K, L)) M
      (kFlat_totalComplexPair Y K L hK hL) hM)
    (comparisonPair_naturality_right X ((pullbackTensorComplexNatIso f).hom.app (K, L))
      (kFlat_modulePullback_unconditional f
        ((totalComplexPair
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).obj (K, L))
        (kFlat_totalComplexPair Y K L hK hL))
      (kFlat_totalComplexPair X ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
        (kFlat_modulePullback_unconditional f K hK) (kFlat_modulePullback_unconditional f L hL))
      (kFlat_modulePullback_unconditional f M hM))

/-- The statement of `derivedPullbackTensorIso_hom_app_comp_comparisonPair_right`, as
a `Prop`-valued `def` so that it and the proof term are elaborated in separate
declarations. -/
def ModelIdentificationRight
    (K L M : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y K)
    (hL : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y L)
    (hM : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y M) : Prop :=
    (derivedPullbackTensorIso f).hom.app
          (DerivedCategory.Q.obj K,
            DerivedCategory.Q.obj
              ((totalComplexPair
                (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).obj
                (L, M))) ≫
        (Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)).map
            ((derivedPullbackNatTrans f).app K ×ₘ pullbackTensorModel f L M) ≫
          comparisonPair X ((pullbackComplex f).obj K)
            ((totalComplexPair
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)).obj
              ((pullbackComplex f).obj L, (pullbackComplex f).obj M))
            (kFlat_modulePullback_unconditional f K hK)
            (kFlat_totalComplexPair X ((pullbackComplex f).obj L) ((pullbackComplex f).obj M)
              (kFlat_modulePullback_unconditional f L hL)
              (kFlat_modulePullback_unconditional f M hM)) =
      (derivedPullback f).map
          (comparisonPair Y K
            ((totalComplexPair
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).obj (L, M)) hK
            (kFlat_totalComplexPair Y L M hL hM)) ≫
        (pullbackTensorModel f K
              ((totalComplexPair
                (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).obj
                (L, M)) ≫
          DerivedCategory.Q.map
            (totalComplexMapLeft X ((pullbackComplex f).obj K)
              ((pullbackTensorComplexNatIso f).hom.app (L, M))))

/-- **The model identification of Tag 079U at the pair `(K, Tot(L ⊗ M))`, re-read against the
model `Tot(f^*L ⊗ f^*M)` of the second factor**; the companion of
`derivedPullbackTensorIso_hom_app_comp_comparisonPair_left`. -/
theorem derivedPullbackTensorIso_hom_app_comp_comparisonPair_right
    (K L M : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y K)
    (hL : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y L)
    (hM : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y M) :
    ModelIdentificationRight f K L M hK hL hM :=
  bifunctor_comparison_model_comp_right
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf))
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf))
    (derivedPullbackTensorIso f).hom
    (derivedPullbackTensorIso_hom_app_comp_comparisonPair f K
      ((totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).obj (L, M)) hK
      (kFlat_totalComplexPair Y L M hL hM))
    (comparisonPair_naturality_left X ((pullbackTensorComplexNatIso f).hom.app (L, M))
      (kFlat_modulePullback_unconditional f K hK)
      (kFlat_modulePullback_unconditional f
        ((totalComplexPair
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).obj (L, M))
        (kFlat_totalComplexPair Y L M hL hM))
      (kFlat_totalComplexPair X ((pullbackComplex f).obj L) ((pullbackComplex f).obj M)
        (kFlat_modulePullback_unconditional f L hL) (kFlat_modulePullback_unconditional f M hM)))

omit [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The composite the associativity chase cancels is an isomorphism.**  It is the pair of
derived pullbacks of the last two factors, tensored, followed by the comparison of Tag 06YU: each
factor is invertible on K-flat complexes, so the composite is, and in particular it is a
monomorphism. -/
theorem isIso_modelCorner
    (K L M : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y K)
    (hL : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y L)
    (hM : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y M) :
    IsIso ((Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)).map
          ((derivedPullbackNatTrans f).app K ×ₘ
            ((Functor.uncurry.obj
                  (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)).map
                ((derivedPullbackNatTrans f).app L ×ₘ (derivedPullbackNatTrans f).app M) ≫
              comparisonPair X ((pullbackComplex f).obj L)
                ((pullbackComplex f).obj M) (kFlat_modulePullback_unconditional f L hL)
                (kFlat_modulePullback_unconditional f M hM))) ≫
        comparisonPair X ((pullbackComplex f).obj K)
          ((totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)).obj
            ((pullbackComplex f).obj L, (pullbackComplex f).obj M))
          (kFlat_modulePullback_unconditional f K hK)
          (kFlat_totalComplexPair X ((pullbackComplex f).obj L) ((pullbackComplex f).obj M)
            (kFlat_modulePullback_unconditional f L hL)
            (kFlat_modulePullback_unconditional f M hM))) := by
  have hKx := kFlat_modulePullback_unconditional f K hK
  have hLx := kFlat_modulePullback_unconditional f L hL
  have hMx := kFlat_modulePullback_unconditional f M hM
  have h₁ := isIso_derivedPullbackNatTrans_app f K hK
  have h₂ := isIso_derivedPullbackNatTrans_app f L hL
  have h₃ := isIso_derivedPullbackNatTrans_app f M hM
  have key : ∀ {A A' B B' : DerivedCategory
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X)}
      (a : A ⟶ A') (b : B ⟶ B'), IsIso a → IsIso b → IsIso
        ((Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)).map (a ×ₘ b)) :=
    fun a b ha hb =>
      @Functor.map_isIso _ _ _ _ _ _ _ _ ((isIso_prod_iff (f := a ×ₘ b)).mpr ⟨ha, hb⟩)
  exact IsIso.comp_isIso'
    (key _ _ h₁ (IsIso.comp_isIso' (key _ _ h₂ h₃)
      (isIso_comparisonPair X ((pullbackComplex f).obj L) ((pullbackComplex f).obj M) hLx hMx)))
    (isIso_comparisonPair X ((pullbackComplex f).obj K)
      ((totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)).obj
        ((pullbackComplex f).obj L, (pullbackComplex f).obj M))
      hKx (kFlat_totalComplexPair X ((pullbackComplex f).obj L) ((pullbackComplex f).obj M)
        hLx hMx))

omit [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The composite the associativity chase cancels is a monomorphism.  It is an isomorphism
(`isIso_modelCorner`); stating the consequence in its own declaration is what keeps the instance
search off the diagram chase, where the morphism it would have to be found for is still half
unknown. -/
theorem mono_modelCorner
    (K L M : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y K)
    (hL : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y L)
    (hM : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y M) :
    Mono ((Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)).map
          ((derivedPullbackNatTrans f).app K ×ₘ
            ((Functor.uncurry.obj
                  (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)).map
                ((derivedPullbackNatTrans f).app L ×ₘ (derivedPullbackNatTrans f).app M) ≫
              comparisonPair X ((pullbackComplex f).obj L)
                ((pullbackComplex f).obj M) (kFlat_modulePullback_unconditional f L hL)
                (kFlat_modulePullback_unconditional f M hM))) ≫
        comparisonPair X ((pullbackComplex f).obj K)
          ((totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)).obj
            ((pullbackComplex f).obj L, (pullbackComplex f).obj M))
          (kFlat_modulePullback_unconditional f K hK)
          (kFlat_totalComplexPair X ((pullbackComplex f).obj L) ((pullbackComplex f).obj M)
            (kFlat_modulePullback_unconditional f L hL)
            (kFlat_modulePullback_unconditional f M hM))) := by
  have := isIso_modelCorner f K L M hK hL hM
  infer_instance

/-- **The comparison of Tag 079U carries the associativity constraint of Tag 0FPT on `D(𝒪_Y)` to
the one on `D(𝒪_X)`, at a triple of K-flat complexes**, as a proposition.  The statement is a
`def` so that it and the proof term are elaborated in separate declarations. -/
def DerivedPullbackTensorIsoAssociatorApp
    (K L M : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    Prop :=
  (derivedPullbackTensorIso f).hom.app
        ((Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf)).obj
          (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L), DerivedCategory.Q.obj M) ≫
      (Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)).map
          ((derivedPullbackTensorIso f).hom.app
              (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ×ₘ
            𝟙 ((derivedPullback f).obj (DerivedCategory.Q.obj M))) ≫
        canonicalAssociatorHom X.sheaf
          ((derivedPullback f).obj (DerivedCategory.Q.obj K))
          ((derivedPullback f).obj (DerivedCategory.Q.obj L))
          ((derivedPullback f).obj (DerivedCategory.Q.obj M)) =
    (derivedPullback f).map
        (canonicalAssociatorHom Y.sheaf (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
          (DerivedCategory.Q.obj M)) ≫
      (derivedPullbackTensorIso f).hom.app
          (DerivedCategory.Q.obj K,
            (Functor.uncurry.obj
                (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf)).obj
              (DerivedCategory.Q.obj L, DerivedCategory.Q.obj M)) ≫
        (Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)).map
            (𝟙 ((derivedPullback f).obj (DerivedCategory.Q.obj K)) ×ₘ
              (derivedPullbackTensorIso f).hom.app
                (DerivedCategory.Q.obj L, DerivedCategory.Q.obj M))

end KFlat

end Pinned

/-! ### The fusion

The diagram chase of `CategoryTheory.bifunctor_comparison_assoc_of_models` is applied here, in a
section carrying none of the `implicit_reducible` attributions of `section Pinned` --
`StacksDraft.KFlat.modulePullback`, `Stacks.SheafOfModules.Tensor.ringSheaf` and the three
names that reach `Z.sheaf` are *not* reducible at implicit transparency here.  (The one
exception is not an attribution of this file's: `structureSheafRing` is `@[instance_reducible]`
where it is declared, so it unfolds at implicit transparency in every section below as well.)
Every term the chase is given is one of the declarations above, already elaborated, so nothing
here needs those definitions unfolded to be stated; and keeping them folded is what brings the
unifications the chase costs inside the heartbeat budget.

The chase's nine hypotheses are handed to it in the five bundles of
`StacksFrontier.CategoryTheory.BifunctorComparisonAssocModels`, and the eleven objects and sixteen
maps are named once in the `Prop`-valued `def` of each bundle.  That is not a mathematical
choice: the heartbeat budget is per declaration, and elaborating the nine arguments of the one
application in a single declaration exceeds it, as does grouping the two model identifications
at the triples and the linking identity together.  Nothing is assumed and nothing is weakened;
the application is paid for in instalments. -/

section Fusion

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] abelianModulesSheafTensor monoidalModules symmetricModules
  monoidalPreadditiveModules monoidalClosedModules hasTensorModules monoidalComplexes
  modulePullback_preservesAntidiagonalCoproducts liftMonoidal CochainComplex.symmetricCategory

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The objects and maps of the associativity chase, and the two laws its models satisfy**, as
a `Prop`-valued `def` so that naming the eleven objects and sixteen maps and proving the three
fields are elaborated in separate declarations.  The source models are the comparison of Tag
06YU on `D(𝒪_Y)` at the pinned spelling `comparisonPair`, the target models are the same on
`D(𝒪_X)`, the two re-bracketings are the associator of total tensor complexes
`complexAssociatorPair` on each side, and the constraint is `canonicalAssociatorHom` of Tag
0FPT. -/
def AssocLaws
    (K L M : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y K)
    (hL : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y L)
    (hM : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y M) : Prop :=
  AssocModelLaws (derivedPullback f)
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf))
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf))
    (canonicalAssociatorHom Y.sheaf (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
      (DerivedCategory.Q.obj M))
    (canonicalAssociatorHom X.sheaf (DerivedCategory.Q.obj ((pullbackComplex f).obj K))
      (DerivedCategory.Q.obj ((pullbackComplex f).obj L))
      (DerivedCategory.Q.obj ((pullbackComplex f).obj M)))
    (canonicalAssociatorHom X.sheaf ((derivedPullback f).obj (DerivedCategory.Q.obj K))
      ((derivedPullback f).obj (DerivedCategory.Q.obj L))
      ((derivedPullback f).obj (DerivedCategory.Q.obj M)))
    ((derivedPullbackNatTrans f).app K) ((derivedPullbackNatTrans f).app L)
    ((derivedPullbackNatTrans f).app M)
    (comparisonPair Y K L hK hL) (comparisonPair Y L M hL hM)
    (comparisonPair Y
      ((totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).obj (K, L)) M
      (kFlat_totalComplexPair Y K L hK hL) hM)
    (comparisonPair Y K
      ((totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).obj (L, M)) hK
      (kFlat_totalComplexPair Y L M hL hM))
    (DerivedCategory.Q.map (complexAssociatorPair Y K L M))
    (comparisonPair X ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
      (kFlat_modulePullback_unconditional f K hK) (kFlat_modulePullback_unconditional f L hL))
    (comparisonPair X ((pullbackComplex f).obj L) ((pullbackComplex f).obj M)
      (kFlat_modulePullback_unconditional f L hL) (kFlat_modulePullback_unconditional f M hM))
    (comparisonPair X
      ((totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)).obj
        ((pullbackComplex f).obj K, (pullbackComplex f).obj L))
      ((pullbackComplex f).obj M)
      (kFlat_totalComplexPair X ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
        (kFlat_modulePullback_unconditional f K hK) (kFlat_modulePullback_unconditional f L hL))
      (kFlat_modulePullback_unconditional f M hM))
    (comparisonPair X ((pullbackComplex f).obj K)
      ((totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)).obj
        ((pullbackComplex f).obj L, (pullbackComplex f).obj M))
      (kFlat_modulePullback_unconditional f K hK)
      (kFlat_totalComplexPair X ((pullbackComplex f).obj L) ((pullbackComplex f).obj M)
        (kFlat_modulePullback_unconditional f L hL) (kFlat_modulePullback_unconditional f M hM)))
    (DerivedCategory.Q.map (complexAssociatorPair X ((pullbackComplex f).obj K)
      ((pullbackComplex f).obj L) ((pullbackComplex f).obj M)))

/-- **The two associativity laws of the models and the naturality of the constraint of Tag
0FPT.**  Both laws are the associativity clause of Tag 0FPT in uncurried form
(`canonicalComparison_associator_uncurried`), read on `Y` and on `X`; the naturality is
`canonicalAssociatorHom_naturality` at the three components of `derivedPullbackNatTrans`. -/
theorem assocModelLaws
    (K L M : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y K)
    (hL : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y L)
    (hM : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y M) :
    AssocLaws f K L M hK hL hM :=
  ⟨canonicalComparison_associator_uncurried Y K L M hK hL hM,
    canonicalComparison_associator_uncurried X ((pullbackComplex f).obj K)
      ((pullbackComplex f).obj L) ((pullbackComplex f).obj M)
      (kFlat_modulePullback_unconditional f K hK)
      (kFlat_modulePullback_unconditional f L hL) (kFlat_modulePullback_unconditional f M hM),
    canonicalAssociatorHom_naturality X ((derivedPullbackNatTrans f).app K)
      ((derivedPullbackNatTrans f).app L) ((derivedPullbackNatTrans f).app M)⟩

/-- The statement of `assocModelPairs`, as a `Prop`-valued `def` for the same reason as
`AssocLaws`. -/
def AssocPairs
    (K L M : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y K)
    (hL : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y L)
    (hM : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y M) : Prop :=
  AssocModelPairs (derivedPullback f)
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf))
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf))
    (derivedPullbackTensorIso f).hom
    ((derivedPullbackNatTrans f).app K) ((derivedPullbackNatTrans f).app L)
    ((derivedPullbackNatTrans f).app M)
    (comparisonPair Y K L hK hL) (comparisonPair Y L M hL hM)
    (comparisonPair X ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
      (kFlat_modulePullback_unconditional f K hK) (kFlat_modulePullback_unconditional f L hL))
    (comparisonPair X ((pullbackComplex f).obj L) ((pullbackComplex f).obj M)
      (kFlat_modulePullback_unconditional f L hL) (kFlat_modulePullback_unconditional f M hM))
    (pullbackTensorModel f K L) (pullbackTensorModel f L M)

/-- **The model identifications of Tag 079U at the pairs `(K, L)` and `(L, M)`**, which are
`derivedPullbackTensorIso_hom_app_comp_comparisonPair` at those two pairs. -/
theorem assocModelPairs
    (K L M : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y K)
    (hL : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y L)
    (hM : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y M) :
    AssocPairs f K L M hK hL hM :=
  ⟨derivedPullbackTensorIso_hom_app_comp_comparisonPair f K L hK hL,
    derivedPullbackTensorIso_hom_app_comp_comparisonPair f L M hL hM⟩

/-- The statement of `assocModelTripleLeft`, as a `Prop`-valued `def` for the same reason as
`AssocLaws`. -/
def AssocTripleLeft
    (K L M : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y K)
    (hL : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y L)
    (hM : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y M) : Prop :=
  AssocModelTripleLeft (derivedPullback f)
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf))
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf))
    (derivedPullbackTensorIso f).hom
    ((derivedPullbackNatTrans f).app M)
    (comparisonPair Y
      ((totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).obj (K, L)) M
      (kFlat_totalComplexPair Y K L hK hL) hM)
    (comparisonPair X
      ((totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)).obj
        ((pullbackComplex f).obj K, (pullbackComplex f).obj L))
      ((pullbackComplex f).obj M)
      (kFlat_totalComplexPair X ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
        (kFlat_modulePullback_unconditional f K hK) (kFlat_modulePullback_unconditional f L hL))
      (kFlat_modulePullback_unconditional f M hM))
    (pullbackTensorModel f K L)
    (pullbackTensorModel f
        ((totalComplexPair
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).obj (K, L)) M ≫
      DerivedCategory.Q.map
        (totalComplexMapRight X ((pullbackTensorComplexNatIso f).hom.app (K, L))
          ((pullbackComplex f).obj M)))

/-- **The model identification of Tag 079U at `(Tot(K ⊗ L), M)`, read against the model
`Tot(f^*K ⊗ f^*L)` of the first factor**, which is
`derivedPullbackTensorIso_hom_app_comp_comparisonPair_left`. -/
theorem assocModelTripleLeft
    (K L M : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y K)
    (hL : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y L)
    (hM : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y M) :
    AssocTripleLeft f K L M hK hL hM :=
  ⟨derivedPullbackTensorIso_hom_app_comp_comparisonPair_left f K L M hK hL hM⟩

/-- The statement of `assocModelTripleRight`, as a `Prop`-valued `def` for the same reason as
`AssocLaws`. -/
def AssocTripleRight
    (K L M : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y K)
    (hL : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y L)
    (hM : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y M) : Prop :=
  AssocModelTripleRight (derivedPullback f)
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf))
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf))
    (derivedPullbackTensorIso f).hom
    ((derivedPullbackNatTrans f).app K)
    (comparisonPair Y K
      ((totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).obj (L, M)) hK
      (kFlat_totalComplexPair Y L M hL hM))
    (comparisonPair X ((pullbackComplex f).obj K)
      ((totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)).obj
        ((pullbackComplex f).obj L, (pullbackComplex f).obj M))
      (kFlat_modulePullback_unconditional f K hK)
      (kFlat_totalComplexPair X ((pullbackComplex f).obj L) ((pullbackComplex f).obj M)
        (kFlat_modulePullback_unconditional f L hL) (kFlat_modulePullback_unconditional f M hM)))
    (pullbackTensorModel f L M)
    (pullbackTensorModel f K
        ((totalComplexPair
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).obj (L, M)) ≫
      DerivedCategory.Q.map
        (totalComplexMapLeft X ((pullbackComplex f).obj K)
          ((pullbackTensorComplexNatIso f).hom.app (L, M))))

/-- **The model identification of Tag 079U at `(K, Tot(L ⊗ M))`, read against the model
`Tot(f^*L ⊗ f^*M)` of the second factor**, which is
`derivedPullbackTensorIso_hom_app_comp_comparisonPair_right`. -/
theorem assocModelTripleRight
    (K L M : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y K)
    (hL : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y L)
    (hM : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y M) :
    AssocTripleRight f K L M hK hL hM :=
  ⟨derivedPullbackTensorIso_hom_app_comp_comparisonPair_right f K L M hK hL hM⟩

/-- The statement of `assocModelLink`, as a `Prop`-valued `def` for the same reason as
`AssocLaws`. -/
def AssocLink
    (K L M : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    Prop :=
  AssocModelLink (derivedPullback f)
    (DerivedCategory.Q.map (complexAssociatorPair Y K L M))
    (DerivedCategory.Q.map (complexAssociatorPair X ((pullbackComplex f).obj K)
      ((pullbackComplex f).obj L) ((pullbackComplex f).obj M)))
    (pullbackTensorModel f
        ((totalComplexPair
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).obj (K, L)) M ≫
      DerivedCategory.Q.map
        (totalComplexMapRight X ((pullbackTensorComplexNatIso f).hom.app (K, L))
          ((pullbackComplex f).obj M)))
    (pullbackTensorModel f K
        ((totalComplexPair
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).obj (L, M)) ≫
      DerivedCategory.Q.map
        (totalComplexMapLeft X ((pullbackComplex f).obj K)
          ((pullbackTensorComplexNatIso f).hom.app (L, M))))

/-- **The identity linking the two models of the triple tensor product**, which is
`pullbackTensorModel_assoc_pair`: the associativity coherence of the comparison of Tag 01CD,
pushed into the derived category. -/
theorem assocModelLink
    (K L M : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    AssocLink f K L M :=
  ⟨pullbackTensorModel_assoc_pair f K L M⟩

/-- **The comparison of Tag 079U carries the associativity constraint of Tag 0FPT on `D(𝒪_Y)` to
the one on `D(𝒪_X)`, at a triple of K-flat complexes.**  The chase is
`CategoryTheory.bifunctor_comparison_assoc_of_bundles`; the models are the comparison of Tag
06YU on both sides, their compatibility with the constraints is the associativity clause of Tag
0FPT, and the identity linking the two models of the triple tensor product is
`pullbackTensorModel_assoc_pair`.  The equation it proves is spelled out in
`DerivedPullbackTensorIsoAssociatorApp`. -/
theorem derivedPullbackTensorIso_associator_app_of_kFlat
    (K L M : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y K)
    (hL : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y L)
    (hM : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y M) :
    DerivedPullbackTensorIsoAssociatorApp f K L M :=
  bifunctor_comparison_assoc_of_bundles (mono_modelCorner f K L M hK hL hM)
    (assocModelLaws f K L M hK hL hM) (assocModelPairs f K L M hK hL hM)
    (assocModelTripleLeft f K L M hK hL hM) (assocModelTripleRight f K L M hK hL hM)
    (assocModelLink f K L M)

end Fusion

/-! ### The compatibility for arbitrary derived modules -/

section Descended

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] abelianModulesSheafTensor monoidalModules symmetricModules
  monoidalPreadditiveModules monoidalClosedModules hasTensorModules monoidalComplexes
  modulePullback_preservesAntidiagonalCoproducts liftMonoidal CochainComplex.symmetricCategory

-- `structureSheafRing` is omitted here for the reason given at the list in `section Pinned`:
-- it is globally `@[instance_reducible]`, so it already unfolds at `implicit` transparency, and
-- raising it to `[implicit_reducible]` would only take it off `instances` transparency and out
-- of typeclass search.
attribute [local implicit_reducible]
  StacksDraft.KFlat.modulePullback TopCat.Sheaf TopCat.Presheaf.IsSheaf
  Stacks.SheafOfModules.Tensor.ringSheaf

section Triple


variable (Z : RingedSpace.{u, u})
  [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The first of three derived modules. -/
abbrev tripleFst :
    DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ×
        DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ×
          DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ⥤
      DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) :=
  CategoryTheory.Prod.fst _ _

/-- The second of three derived modules. -/
abbrev tripleSnd :
    DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ×
        DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ×
          DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ⥤
      DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) :=
  CategoryTheory.Prod.snd _ _ ⋙ CategoryTheory.Prod.fst _ _

/-- The third of three derived modules. -/
abbrev tripleThd :
    DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ×
        DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ×
          DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ⥤
      DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) :=
  CategoryTheory.Prod.snd _ _ ⋙ CategoryTheory.Prod.snd _ _

/-- The functor `(M, N, R) ↦ (M ⊗^L_{𝒪_Z} N) ⊗^L_{𝒪_Z} R` on `D(𝒪_Z)³`. -/
abbrev tripleTensorLeft :=
  Functor.prod'
      (Functor.prod' (tripleFst Z) (tripleSnd Z) ⋙
        Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf))
      (tripleThd Z) ⋙
    Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf)

/-- The functor `(M, N, R) ↦ M ⊗^L_{𝒪_Z} (N ⊗^L_{𝒪_Z} R)` on `D(𝒪_Z)³`. -/
abbrev tripleTensorRight :=
  Functor.prod' (tripleFst Z)
      (Functor.prod' (tripleSnd Z) (tripleThd Z) ⋙
        Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf)) ⋙
    Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf)

/-- **The associativity constraint of Tag 0FPT as a natural transformation** on `D(𝒪_Z)³`.  Its
components are `Stacks.SheafOfModules.DerivedMonoidal.canonicalAssociatorHom` and its naturality
is `canonicalAssociatorHom_naturality`; packaging it this way is what lets the two sides of the
associativity compatibility be assembled by whiskering, so that their naturality costs
nothing. -/
def canonicalAssociatorNatTrans : tripleTensorLeft Z ⟶ tripleTensorRight Z where
  app W := canonicalAssociatorHom Z.sheaf W.1 W.2.1 W.2.2
  naturality _ _ g := canonicalAssociatorHom_naturality Z g.1 g.2.1 g.2.2

end Triple

section Descent

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The derived pullback in all three variables. -/
abbrev pullbackTriple :=
  (derivedPullback f).prod ((derivedPullback f).prod (derivedPullback f))

/-- The left-hand side of the associativity compatibility, as a transformation
`(M, N, R) ↦ Lf^*((M ⊗^L N) ⊗^L R) ⟶ Lf^*M ⊗^L (Lf^*N ⊗^L Lf^*R)` on `D(𝒪_Y)³`: the comparison
of Tag 079U in the outer and then the inner tensor factor, then the associativity constraint of
the derived pullbacks. -/
def comparisonThenAssociator :
    tripleTensorLeft Y ⋙ derivedPullback f ⟶ pullbackTriple f ⋙ tripleTensorRight X :=
  Functor.whiskerLeft
      (Functor.prod'
        (Functor.prod' (tripleFst Y) (tripleSnd Y) ⋙
          Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf))
        (tripleThd Y))
      (derivedPullbackTensorIso f).hom ≫
    Functor.whiskerRight
        (NatTrans.prod'
          (Functor.whiskerLeft (Functor.prod' (tripleFst Y) (tripleSnd Y))
            (derivedPullbackTensorIso f).hom)
          (NatTrans.id (tripleThd Y ⋙ derivedPullback f)))
        (Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)) ≫
      Functor.whiskerLeft (pullbackTriple f) (canonicalAssociatorNatTrans X)

/-- The right-hand side: the derived pullback of the associativity constraint, then the
comparison of Tag 079U in the outer and then the inner tensor factor. -/
def associatorThenComparison :
    tripleTensorLeft Y ⋙ derivedPullback f ⟶ pullbackTriple f ⋙ tripleTensorRight X :=
  Functor.whiskerRight (canonicalAssociatorNatTrans Y) (derivedPullback f) ≫
    Functor.whiskerLeft
        (Functor.prod' (tripleFst Y)
          (Functor.prod' (tripleSnd Y) (tripleThd Y) ⋙
            Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf)))
        (derivedPullbackTensorIso f).hom ≫
      Functor.whiskerRight
        (NatTrans.prod' (NatTrans.id (tripleFst Y ⋙ derivedPullback f))
          (Functor.whiskerLeft (Functor.prod' (tripleSnd Y) (tripleThd Y))
            (derivedPullbackTensorIso f).hom))
        (Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf))

/-- The components of `comparisonThenAssociator`. -/
theorem comparisonThenAssociator_app
    (M N R : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) :
    (comparisonThenAssociator f).app (M, N, R) =
      (derivedPullbackTensorIso f).hom.app
          ((Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf)).obj (M, N),
            R) ≫
        (Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)).map
            ((derivedPullbackTensorIso f).hom.app (M, N) ×ₘ
              𝟙 ((derivedPullback f).obj R)) ≫
          canonicalAssociatorHom X.sheaf ((derivedPullback f).obj M)
            ((derivedPullback f).obj N) ((derivedPullback f).obj R) :=
  rfl

/-- The components of `associatorThenComparison`. -/
theorem associatorThenComparison_app
    (M N R : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) :
    (associatorThenComparison f).app (M, N, R) =
      (derivedPullback f).map (canonicalAssociatorHom Y.sheaf M N R) ≫
        (derivedPullbackTensorIso f).hom.app
            (M, (Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf)).obj (N, R)) ≫
          (Functor.uncurry.obj
                (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)).map
              (𝟙 ((derivedPullback f).obj M) ×ₘ
                (derivedPullbackTensorIso f).hom.app (N, R)) :=
  rfl

/-- **The derived pullback–tensor comparison of Tag 079U is associative**, as an identity of
natural transformations on `D(𝒪_Y)³`.

Both sides are transformations `Lf^*((M ⊗^L N) ⊗^L R) ⟶ Lf^*M ⊗^L (Lf^*N ⊗^L Lf^*R)`, and
`D(𝒪_Y)` is the localization of the K-flat objects of the homotopy category at the
quasi-isomorphisms (Stacks 06YS), so they agree as soon as they agree at a triple of K-flat
representatives. -/
theorem comparisonThenAssociator_eq :
    comparisonThenAssociator f = associatorThenComparison f :=
  natTrans_ext_of_kFlat₃ Y _ _ fun K L M hK hL hM =>
    (comparisonThenAssociator_app f _ _ _).trans
      ((derivedPullbackTensorIso_associator_app_of_kFlat f K L M hK hL hM).trans
        (associatorThenComparison_app f _ _ _).symm)

/-- **The derived pullback–tensor comparison of Tag 079U carries the associativity constraint of
the monoidal derived category of Tag 0FPT on `D(𝒪_Y)` to the one on `D(𝒪_X)`**, for arbitrary
`M, N, R ∈ D(𝒪_Y)` and with no finiteness, flatness or quasi-coherence hypothesis.

Equivalently: `Lf^*` is a monoidal functor for the derived tensor product of Tag 06YU. -/
theorem derivedPullbackTensorIso_associator
    (M N R : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) :
    (derivedPullbackTensorIso f).hom.app
          ((Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf)).obj (M, N),
            R) ≫
        (Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)).map
            ((derivedPullbackTensorIso f).hom.app (M, N) ×ₘ
              𝟙 ((derivedPullback f).obj R)) ≫
          canonicalAssociatorHom X.sheaf ((derivedPullback f).obj M)
            ((derivedPullback f).obj N) ((derivedPullback f).obj R) =
      (derivedPullback f).map (canonicalAssociatorHom Y.sheaf M N R) ≫
        (derivedPullbackTensorIso f).hom.app
            (M, (Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf)).obj (N, R)) ≫
          (Functor.uncurry.obj
                (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)).map
              (𝟙 ((derivedPullback f).obj M) ×ₘ
                (derivedPullbackTensorIso f).hom.app (N, R)) :=
  (comparisonThenAssociator_app f M N R).symm.trans
    ((congrArg (fun τ => τ.app (M, N, R)) (comparisonThenAssociator_eq f)).trans
      (associatorThenComparison_app f M N R))

end Descent

end Descended

end Stacks.Cohomology.DerivedPullbackTensor

end
