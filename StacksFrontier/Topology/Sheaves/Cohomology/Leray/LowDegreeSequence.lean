module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import StacksFrontier.Homology.Injectives.Sheaf.AbelianSheavesOnSpace
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.Algebra.Homology.RightDerivedEdge
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.AbelianSheafSpectralSequence
public import Mathlib.Algebra.Category.Grp.EpiMono
public import StacksFrontier.Algebra.Homology.RightDerivedCoEdge
public import StacksFrontier.Algebra.Homology.RightDerivedDeltaOne
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.AbelianCohomologySheafOnSections
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The low-degree Leray sequence for abelian sheaves

For a continuous map `f : X ⟶ Y` and an abelian sheaf `F` on `X` the Leray spectral sequence has
a five-term exact sequence in low degrees; its first nontrivial piece is

  `0 ⟶ H¹(Y, f_* F) ⟶ H¹(X, F) ⟶ Γ(Y, R¹ f_* F)`.

This file sets up the abelian-sheaf side of [Stacks, Tag 01F2]: the cohomology functors
`Hⁿ(U, -)` on abelian sheaves in a coefficient universe that may be larger than the universe of
the space, the structure `AbelianLerayLowDegreeData` recording the two edge maps together with
their characterisations and the exactness between them, and the construction of the first edge
map `Hⁿ(Y, f_* F) ⟶ Hⁿ(X, F)`.

The first edge map is the instance `P := f_*`, `Q := Γ(Y, -)` of the general edge morphism
`Stacks.Cohomology.RightDerivedEdge.edge`, which is possible because `Γ(Y, -) ∘ f_*` is
*literally* `Γ(X, -)`: taking global sections of `f_* F` means evaluating `F` on
`(Opens.map f).obj ⊤`, which is `⊤` by `TopologicalSpace.Opens.map_top`, and that is a
definitional equality (`abelianPushforward_comp_abelianSections`).  The only input the
construction needs beyond the general edge morphism is that `f_*` preserves injective objects.

## Main definitions

* `Stacks.Cohomology.LerayLowDegree.abelianSections`, `abelianPushforward`,
  `abelianCohomology`, `abelianCohomologyRestriction`, `abelianSectionsCycles`: the abelian-sheaf
  vocabulary, at a coefficient universe containing that of the space.
* `Stacks.Cohomology.LerayLowDegree.AbelianLerayLowDegreeData`: the low-degree Leray data.
* `Stacks.Cohomology.LerayLowDegree.abelianEdgeMap`: the first edge map
  `Hⁿ(Y, f_* -) ⟶ Hⁿ(X, -)`, i.e. the `edgeMap` field of `AbelianLerayLowDegreeData`.

## Main results

* `Stacks.Cohomology.LerayLowDegree.abelianPushforward_comp_abelianSections`: global sections on
  `X` *are* global sections on `Y` of the direct image.
* `Stacks.Cohomology.LerayLowDegree.abelianEdgeMap_eq`: any augmentation-preserving comparison of
  injective resolutions computes the first edge map, i.e. the `edgeMap_eq` field.
* `Stacks.Cohomology.LerayLowDegree.AbelianLerayLowDegreeData.mem_range_edgeMap_iff`: the image of
  the injective first edge map consists exactly of the classes that vanish over the inverse
  images of neighbourhoods of every point of `Y`.

## References

* [Stacks Project, Tag 01F2](https://stacks.math.columbia.edu/tag/01F2)
* [Stacks Project, Tag 01DG](https://stacks.math.columbia.edu/tag/01DG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u v

namespace Stacks.Cohomology.LerayLowDegree

/-- Abelian sheaves in any universe containing that of the space admit sheafification. -/
theorem abelianSheafHasSheafify (X : TopCat.{u}) :
    HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v} := by
  let : PreservesLimits (forget AddCommGrpCat.{max u v}) :=
    AddCommGrpCat.forget_preservesLimits
  let : ∀ U : Opens X, Small.{u} ((Opens.grothendieckTopology X).Cover U)ᵒᵖ :=
    fun U ↦ inferInstance
  exact hasSheafifyEssentiallySmallSite (Opens.grothendieckTopology X) AddCommGrpCat

attribute [local instance] abelianSheafHasSheafify

/-- **Abelian sheaves have enough injectives** ([Stacks, Tag 01DG]), in any coefficient universe
containing that of the space.  The site `Opens X` is `u`-small, hence essentially small in the
larger universe, and `AddCommGrpCat` is a Grothendieck abelian category there, so the sheaf
category is Grothendieck abelian and therefore has enough injectives. -/
@[stacks 01DG "enough injectives",
  sga "4 II 6.9" "site of opens of a space",
  sga "4 V 0.1.1" "sheaves on a space"]
instance abelianSheafEnoughInjectives (X : TopCat.{u}) :
    EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}) :=
  Stacks.Injectives.abelianSheaf_enoughInjectives.{u, v} X

/-- Sections of an abelian sheaf on an open subset. -/
abbrev abelianSections (X : TopCat.{u}) (U : Opens X) :=
  (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{v}).obj (op U)

/-- Taking sections is additive. -/
instance abelianSections_additive (X : TopCat.{u}) (U : Opens X) :
    (abelianSections.{u, v} X U).Additive := by
  change (sheafToPresheaf _ _ ⋙ (evaluation _ _).obj _).Additive
  infer_instance

/-- The ordinary direct image of abelian sheaves. -/
abbrev abelianPushforward {X Y : TopCat.{u}} (f : X ⟶ Y) :=
  (Opens.map f).sheafPushforwardContinuous AddCommGrpCat.{v}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)

/-- Direct image of abelian sheaves is additive. -/
instance abelianPushforward_additive {X Y : TopCat.{u}} (f : X ⟶ Y) :
    (abelianPushforward.{u, v} f).Additive where
  map_add := by intros; rfl

/-- Abelian-sheaf cohomology on an open subset, computed by injective resolutions. -/
abbrev abelianCohomology (X : TopCat.{u}) (U : Opens X) (n : ℕ) :=
  (abelianSections.{u, max u v} X U).rightDerived n

/-- Restriction on cohomology is induced by ordinary restriction of sections. -/
def abelianCohomologyRestriction (X : TopCat.{u}) {U V : Opens X} (h : U ≤ V) (n : ℕ) :
    abelianCohomology.{u, v} X V n ⟶ abelianCohomology.{u, v} X U n :=
  ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}).map
    (homOfLE h).op).rightDerived n

/-- Sections of the cycles map canonically to cycles of the sections complex. -/
def abelianSectionsCycles (Y : TopCat.{u})
    (K : CochainComplex (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{max u v}) ℕ)
    (n : ℕ) :
    (abelianSections Y ⊤).obj (K.cycles n) ⟶
      (((abelianSections Y ⊤).mapHomologicalComplex (.up ℕ)).obj K).cycles n :=
  HomologicalComplex.liftCycles _ ((abelianSections Y ⊤).map (K.iCycles n))
    (n + 1) (by simp) (by
      change (abelianSections.{u, max u v} Y ⊤).map (K.iCycles n) ≫
        (abelianSections Y ⊤).map (K.d n (n + 1)) = 0
      rw [← CategoryTheory.Functor.map_comp, K.iCycles_d, CategoryTheory.Functor.map_zero])

/-- The natural exact sequence `0 → H¹(Y, f_*F) → H¹(X, F) → Γ(Y, R¹f_*F)`.
The comparison formulas specify the actual Leray maps, and the local vanishing
criterion makes its exactness applicable to locally trivial cohomology classes. -/
structure AbelianLerayLowDegreeData {X Y : TopCat.{u}} (f : X ⟶ Y) where
  /-- The canonical comparison from cohomology of the direct image. -/
  edgeMap (n : ℕ) :
    abelianPushforward.{u, max u v} f ⋙ abelianCohomology.{u, v} Y ⊤ n ⟶
      abelianCohomology.{u, v} X ⊤ n
  /-- Any augmentation-preserving comparison of resolutions computes the edge map. -/
  edgeMap_eq (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}) (n : ℕ)
      (I : InjectiveResolution F)
      (J : InjectiveResolution ((abelianPushforward f).obj F))
      (φ : J.cocomplex ⟶
        ((abelianPushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex)
      (hφ : J.ι.f 0 ≫ φ.f 0 = (abelianPushforward f).map (I.ι.f 0)) :
    (edgeMap n).app F = (J.isoRightDerivedObj (abelianSections Y ⊤) n).hom ≫
      HomologicalComplex.homologyMap
        (((abelianSections Y ⊤).mapHomologicalComplex (.up ℕ)).map φ) n ≫
          (I.isoRightDerivedObj (abelianSections X ⊤) n).inv
  /-- The first edge map is injective in degree one. -/
  edgeMap_injective (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}) :
    Function.Injective ((edgeMap 1).app F)
  /-- The second edge map sends a cohomology class to its section of `R¹f_*F`. -/
  secondEdgeMap : abelianCohomology.{u, v} X ⊤ 1 ⟶
    (abelianPushforward.{u, max u v} f).rightDerived 1 ⋙ abelianSections Y ⊤
  /-- On cycles, the second edge map is the quotient to the cohomology sheaf. -/
  secondEdgeMap_eq (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v})
      (I : InjectiveResolution F) :
    let K := ((abelianPushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex
    abelianSectionsCycles Y K 1 ≫
      (((abelianSections Y ⊤).mapHomologicalComplex (.up ℕ)).obj K).homologyπ 1 ≫
        (I.isoRightDerivedObj (abelianSections X ⊤) 1).inv ≫ secondEdgeMap.app F =
      (abelianSections Y ⊤).map (K.homologyπ 1) ≫
        (abelianSections Y ⊤).map (I.isoRightDerivedObj (abelianPushforward f) 1).inv
  /-- Consecutive edge maps compose to zero. -/
  edgeMap_secondEdgeMap (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}) :
    (edgeMap 1).app F ≫ secondEdgeMap.app F = 0
  /-- Exactness at first cohomology on the source. -/
  exact (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}) :
    (ShortComplex.mk ((edgeMap 1).app F) (secondEdgeMap.app F)
      (edgeMap_secondEdgeMap F)).Exact
  /-- A class maps to zero precisely when it vanishes locally over the target. -/
  secondEdgeMap_eq_zero_iff
      (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v})
      (ξ : (abelianCohomology.{u, v} X ⊤ 1).obj F) :
    secondEdgeMap.app F ξ = 0 ↔
      ∀ y : Y, ∃ V : Opens Y, y ∈ V ∧
        (abelianCohomologyRestriction X
          (show (Opens.map f).obj V ≤ ⊤ from le_top) 1).app F ξ = 0

/-- The image of the injective first edge map consists exactly of the classes
that vanish over the inverse images of neighbourhoods of every point. -/
theorem AbelianLerayLowDegreeData.mem_range_edgeMap_iff
    {X Y : TopCat.{u}} {f : X ⟶ Y} (D : AbelianLerayLowDegreeData.{u, v} f)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v})
    (ξ : (abelianCohomology.{u, v} X ⊤ 1).obj F) :
    (∃ η, (D.edgeMap 1).app F η = ξ) ↔
      ∀ y : Y, ∃ V : Opens Y, y ∈ V ∧
        (abelianCohomologyRestriction X
          (show (Opens.map f).obj V ≤ ⊤ from le_top) 1).app F ξ = 0 :=
  ((ShortComplex.ab_exact_iff_function_exact _).mp (D.exact F) ξ).symm.trans
    (D.secondEdgeMap_eq_zero_iff F ξ)

section EdgeMap

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

/-- **Global sections on `X` are global sections on `Y` of the direct image**:
`Γ(Y, -) ∘ f_* = Γ(X, -)`, because `(f_* F)(⊤_Y) = F((Opens.map f).obj ⊤) = F(⊤_X)` and
`TopologicalSpace.Opens.map_top` is a definitional equality.  This is what lets the Leray edge
map be an instance of the general edge morphism of a composite of right derived functors with no
further comparison. -/
theorem abelianPushforward_comp_abelianSections :
    abelianPushforward.{u, max u v} f ⋙ abelianSections.{u, max u v} Y ⊤ =
      abelianSections.{u, max u v} X ⊤ :=
  rfl

variable [(abelianPushforward.{u, max u v} f).PreservesInjectiveObjects]

/-- **The first Leray edge map** `Hⁿ(Y, f_* F) ⟶ Hⁿ(X, F)` for abelian sheaves, natural in `F`:
the `edgeMap` field of `AbelianLerayLowDegreeData`.  It is the edge morphism of the composite
`Γ(Y, -) ∘ f_* = Γ(X, -)` of right derived functors, which requires no exactness hypothesis on
`f_*`, only that `f_*` preserves injective objects. -/
def abelianEdgeMap (n : ℕ) :
    abelianPushforward.{u, max u v} f ⋙ abelianCohomology.{u, v} Y ⊤ n ⟶
      abelianCohomology.{u, v} X ⊤ n :=
  RightDerivedEdge.edge (abelianPushforward.{u, max u v} f)
    (abelianSections.{u, max u v} Y ⊤) n

/-- **Any augmentation-preserving comparison of resolutions computes the first Leray edge map**:
the `edgeMap_eq` field of `AbelianLerayLowDegreeData`.  Given an injective resolution `I` of `F`
on `X`, an injective resolution `J` of `f_* F` on `Y`, and any map of complexes
`φ : J ⟶ f_* I` extending `f_*` applied to the augmentation of `I`, the edge map in degree `n` is
the map induced by `φ` on the `n`-th cohomology of global sections. -/
theorem abelianEdgeMap_eq
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}) (n : ℕ)
    (I : InjectiveResolution F)
    (J : InjectiveResolution ((abelianPushforward.{u, max u v} f).obj F))
    (φ : J.cocomplex ⟶
      ((abelianPushforward.{u, max u v} f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex)
    (hφ : J.ι.f 0 ≫ φ.f 0 = (abelianPushforward.{u, max u v} f).map (I.ι.f 0)) :
    (abelianEdgeMap.{u, v} f n).app F =
      (J.isoRightDerivedObj (abelianSections.{u, max u v} Y ⊤) n).hom ≫
      HomologicalComplex.homologyMap
        (((abelianSections.{u, max u v} Y ⊤).mapHomologicalComplex (.up ℕ)).map φ) n ≫
          (I.isoRightDerivedObj (abelianSections.{u, max u v} X ⊤) n).inv :=
  RightDerivedEdge.edge_app_eq (abelianPushforward.{u, max u v} f)
    (abelianSections.{u, max u v} Y ⊤) n I J φ hφ

end EdgeMap

/-- **The direct image of abelian sheaves preserves injective objects** when the coefficient
universe is that of the space, which is the case the construction of the Leray edge map needs as
an input.  This is `Stacks.Cohomology.Leray.pushforward_preservesInjectiveObjects`; it is
recorded here in the `abelianPushforward` spelling. -/
instance abelianPushforward_preservesInjectiveObjects {X Y : TopCat.{u}} (f : X ⟶ Y) :
    (abelianPushforward.{u, u} f).PreservesInjectiveObjects :=
  Leray.pushforward_preservesInjectiveObjects f

end Stacks.Cohomology.LerayLowDegree

end

-- ===== merged from StacksDraft.Ch20.Sec13.Tag01F2LowDegree2 =====

/-!
# The second Leray edge map for abelian sheaves

This file instantiates the co-edge morphism of
`Stacks.Cohomology.RightDerivedCoEdge.secondEdge` at `P = f_*`, `Q = Γ(Y, -)` and so supplies the
`secondEdgeMap` and `secondEdgeMap_eq` fields of
`Stacks.Cohomology.LerayLowDegree.AbelianLerayLowDegreeData`, the second nontrivial map

  `Hⁿ(X, F) ⟶ Γ(Y, Rⁿ f_* F)`

of the five-term exact sequence of [Stacks, Tag 01F2].  It also supplies the `edgeMap_injective`
field, by instantiating `Stacks.Cohomology.RightDerivedCoEdge.mono_edge_app_one` at the same pair
and reading a monomorphism of abelian groups as an injective map.

The only input beyond the general construction is that `Γ(Y, -)` is left exact.  That is true for a
structural reason: taking sections over an open subset is `sheafToPresheaf` followed by evaluation,
and both of those preserve limits, the first because `Sheaf` limits are computed in presheaves.
Note that, unlike the first edge map
`Stacks.Cohomology.LerayLowDegree.abelianEdgeMap`, the second one needs *no* hypothesis that `f_*`
preserve injective objects, so it is available at the full universe generality
`AddCommGrpCat.{max u v}` with no instance side condition.

The identity `Γ(Y, -) ∘ f_* = Γ(X, -)` is `rfl`
(`Stacks.Cohomology.LerayLowDegree.abelianPushforward_comp_abelianSections`), which is what makes
the source of the co-edge morphism literally `Hⁿ(X, -)`.

## Main definitions

* `Stacks.Cohomology.LerayLowDegree.abelianSecondEdgeMap`: the second edge map
  `Hⁿ(X, -) ⟶ Γ(Y, Rⁿ f_* -)`, i.e. the `secondEdgeMap` field of
  `AbelianLerayLowDegreeData`.

## Main results

* `Stacks.Cohomology.LerayLowDegree.abelianSections_preservesFiniteLimits`: taking sections of an
  abelian sheaf over an open subset is left exact.
* `Stacks.Cohomology.LerayLowDegree.abelianSecondEdgeMap_eq`: on sections of the cycles, the
  second edge map is `Γ(Y, -)` applied to the projection onto the cohomology sheaf, i.e. the
  `secondEdgeMap_eq` field of `AbelianLerayLowDegreeData`.
* `Stacks.Cohomology.LerayLowDegree.abelianEdgeMap_injective`: the first edge map
  `H¹(Y, f_* F) ⟶ H¹(X, F)` is injective, i.e. the `edgeMap_injective` field of
  `AbelianLerayLowDegreeData`.
* `Stacks.Cohomology.LerayLowDegree.abelianEdgeMap_comp_abelianSecondEdgeMap`: the two edge maps
  compose to zero, i.e. the `edgeMap_secondEdgeMap` field of `AbelianLerayLowDegreeData`.

## References

* [Stacks Project, Tag 01F2](https://stacks.math.columbia.edu/tag/01F2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u v

namespace Stacks.Cohomology.LerayLowDegree

attribute [local instance] abelianSheafHasSheafify

/-- **Taking sections of an abelian sheaf over an open subset is left exact.**  Sections are the
inclusion of sheaves into presheaves followed by evaluation at the open subset; the inclusion
preserves limits because limits of sheaves are computed in presheaves, and evaluation preserves
limits because limits of presheaves are computed pointwise. -/
instance abelianSections_preservesFiniteLimits (X : TopCat.{u}) (U : Opens X) :
    PreservesFiniteLimits (abelianSections.{u, v} X U) := by
  change PreservesFiniteLimits (sheafToPresheaf _ _ ⋙ (evaluation _ _).obj _)
  infer_instance

section SecondEdgeMap

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

/-- **The second Leray edge map** `Hⁿ(X, F) ⟶ Γ(Y, Rⁿ f_* F)` for abelian sheaves, natural in
`F`: the `secondEdgeMap` field of `AbelianLerayLowDegreeData`.  It is the co-edge morphism of the
composite `Γ(Y, -) ∘ f_* = Γ(X, -)` of right derived functors, which requires only that
`Γ(Y, -)` be left exact. -/
def abelianSecondEdgeMap (n : ℕ) :
    abelianCohomology.{u, v} X ⊤ n ⟶
      (abelianPushforward.{u, max u v} f).rightDerived n ⋙ abelianSections.{u, max u v} Y ⊤ :=
  RightDerivedCoEdge.secondEdge (abelianPushforward.{u, max u v} f)
    (abelianSections.{u, max u v} Y ⊤) n

/-- The comparison `Γ(Y, Zⁿ K) ⟶ Zⁿ Γ(Y, K)` of
`Stacks.Cohomology.LerayLowDegree.abelianSectionsCycles` is the general comparison of cycles under
a functor. -/
theorem abelianSectionsCycles_eq (Z : TopCat.{u})
    (K : CochainComplex (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{max u v}) ℕ)
    (n : ℕ) :
    abelianSectionsCycles.{u, v} Z K n =
      RightDerivedCoEdge.mapCycles (abelianSections.{u, max u v} Z ⊤) K n :=
  rfl

/-- **On sections of the cycles, the second Leray edge map is `Γ(Y, -)` applied to the projection
onto the cohomology sheaf**: the `secondEdgeMap_eq` field of `AbelianLerayLowDegreeData`.  Given
an injective resolution `I` of `F` on `X`, the complex `K = f_* I` computes the higher direct
images, and `Γ(Y, K)` computes the cohomology of `X`; the second edge map is the map these two
descriptions of a class induce on `Γ(Y, Hⁿ K)`. -/
theorem abelianSecondEdgeMap_eq (n : ℕ)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v})
    (I : InjectiveResolution F) :
    letI K := ((abelianPushforward.{u, max u v} f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex
    abelianSectionsCycles.{u, v} Y K n ≫
      (((abelianSections.{u, max u v} Y ⊤).mapHomologicalComplex (.up ℕ)).obj K).homologyπ n ≫
        (I.isoRightDerivedObj (abelianSections.{u, max u v} X ⊤) n).inv ≫
          (abelianSecondEdgeMap.{u, v} f n).app F =
      (abelianSections.{u, max u v} Y ⊤).map (K.homologyπ n) ≫
        (abelianSections.{u, max u v} Y ⊤).map
          (I.isoRightDerivedObj (abelianPushforward.{u, max u v} f) n).inv :=
  RightDerivedCoEdge.secondEdge_app_eq (abelianPushforward.{u, max u v} f)
    (abelianSections.{u, max u v} Y ⊤) n I

end SecondEdgeMap

section BothEdgeMaps

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
  [(abelianPushforward.{u, max u v} f).PreservesInjectiveObjects]

/-- **The first Leray edge map `H¹(Y, f_* F) ⟶ H¹(X, F)` is injective**: the `edgeMap_injective`
field of `AbelianLerayLowDegreeData`.  This is the general monomorphy of the degree-one edge
morphism of a composite of right derived functors with a left exact inner functor; `f_*` is left
exact because it is a right adjoint. -/
@[sga "3 XXIV 8.5" "injectivity of H¹(S"]
theorem abelianEdgeMap_injective
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}) :
    Function.Injective ((abelianEdgeMap.{u, v} f 1).app F) :=
  (AddCommGrpCat.mono_iff_injective _).1
    (RightDerivedCoEdge.mono_edge_app_one (abelianPushforward.{u, max u v} f)
      (abelianSections.{u, max u v} Y ⊤) F)

/-- **The two Leray edge maps compose to zero**: the `edgeMap_secondEdgeMap` field of
`AbelianLerayLowDegreeData`.  A class in `H¹(X, F)` pulled back from `H¹(Y, f_* F)` induces the
zero section of `R¹ f_* F`, because both maps are computed from one injective resolution of `F`
and the comparison of resolutions factors through the vanishing `H¹` of a resolution. -/
theorem abelianEdgeMap_comp_abelianSecondEdgeMap
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}) :
    (abelianEdgeMap.{u, v} f 1).app F ≫ (abelianSecondEdgeMap.{u, v} f 1).app F = 0 :=
  RightDerivedCoEdge.edge_comp_secondEdge (abelianPushforward.{u, max u v} f)
    (abelianSections.{u, max u v} Y ⊤) 0 F

end BothEdgeMaps

end Stacks.Cohomology.LerayLowDegree

end

-- ===== merged from StacksDraft.Ch20.Sec13.Tag01F2LowDegree3 =====

/-!
# Exactness of the low-degree Leray sequence for abelian sheaves

This file supplies the `exact` field of
`Stacks.Cohomology.LerayLowDegree.AbelianLerayLowDegreeData`, the exactness

  `H¹(Y, f_* F) ⟶ H¹(X, F) ⟶ Γ(Y, R¹ f_* F)`

at the middle term, by instantiating
`Stacks.Cohomology.RightDerivedDeltaOne.exact_edge_secondEdge` at `P = f_*`, `Q = Γ(Y, -)`.  The
two inputs beyond the general statement are that `f_*` is left exact — it is a right adjoint — and
that `Γ(Y, -)` is left exact, which is
`Stacks.Cohomology.LerayLowDegree.abelianSections_preservesFiniteLimits`.

As with the first edge map, the only hypothesis that is not available at the full universe
generality `AddCommGrpCat.{max u v}` is that `f_*` preserves injective objects, which is carried
as an instance argument.

## Main results

* `Stacks.Cohomology.LerayLowDegree.abelianPushforward_preservesFiniteLimits`: the direct image of
  abelian sheaves is left exact.
* `Stacks.Cohomology.LerayLowDegree.abelianExact`: the `exact` field of
  `AbelianLerayLowDegreeData`.

## References

* [Stacks Project, Tag 01F2](https://stacks.math.columbia.edu/tag/01F2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u v

namespace Stacks.Cohomology.LerayLowDegree

attribute [local instance] abelianSheafHasSheafify

/-- **The direct image of abelian sheaves is left exact**, at any coefficient universe containing
that of the space: it is a right adjoint.  Unlike the preservation of injective objects, this needs
no universe restriction. -/
@[sga "4 IV 3.1.2" "special case"]
instance abelianPushforward_preservesFiniteLimits {X Y : TopCat.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (abelianPushforward.{u, max u v} f) := by
  have := ((Opens.map f).sheafAdjunctionContinuous AddCommGrpCat.{max u v}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).rightAdjoint_preservesLimits
  infer_instance

section Exactness

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
  [(abelianPushforward.{u, max u v} f).PreservesInjectiveObjects]

/-- **Exactness of the low-degree Leray sequence at `H¹(X, F)`**: the `exact` field of
`AbelianLerayLowDegreeData`.  A class of `H¹(X, F)` inducing the zero section of `R¹ f_* F` comes
from `H¹(Y, f_* F)`.  This is the instance `P = f_*`, `Q = Γ(Y, -)` of the general exactness of the
five-term sequence of a composite of right derived functors; `f_*` is left exact because it is a
right adjoint, and `Γ(Y, -)` is left exact because sections are an inclusion followed by an
evaluation. -/
@[sga "3 XXIV 8.5" "exactness at H¹(S',G')"]
theorem abelianExact (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}) :
    (ShortComplex.mk ((abelianEdgeMap.{u, v} f 1).app F)
      ((abelianSecondEdgeMap.{u, v} f 1).app F)
      (abelianEdgeMap_comp_abelianSecondEdgeMap.{u, v} f F)).Exact :=
  RightDerivedDeltaOne.exact_edge_secondEdge (abelianPushforward.{u, max u v} f)
    (abelianSections.{u, max u v} Y ⊤) F

end Exactness

end Stacks.Cohomology.LerayLowDegree

end

-- ===== merged from StacksDraft.Ch20.Sec13.Tag01F2LowDegree4 =====

/-!
# The local vanishing criterion of the low-degree Leray sequence for abelian sheaves

This file supplies the last field of
`Stacks.Cohomology.LerayLowDegree.AbelianLerayLowDegreeData`, the criterion

  `ξ ↦ 0 in Γ(Y, R¹ f_* F)` ⟺ `ξ|_{f⁻¹V} = 0` for some neighbourhood `V` of every point of `Y`,

and assembles the eight fields into the data itself.

Everything is read off one injective resolution `I` of `F`.  Writing `K = f_* I`, the second
edge map is, through the comparison isomorphisms, the canonical map
`H¹(Γ(Y, K)) ⟶ Γ(Y, H¹ K)` of
`Stacks.Cohomology.RightDerivedCoEdge.homologyToMapHomology`
(`Stacks.Cohomology.RightDerivedCoEdge.isoRightDerivedObjComp_inv_comp_secondEdgeApp`), and the
restriction map in cohomology is, through the same comparison on the left, the map induced on
homology by restricting sections from `Y` to `V`
(`CategoryTheory.InjectiveResolution.rightDerived_app_eq`).  Both comparison isomorphisms are
isomorphisms of abelian groups, so they may be cancelled from a vanishing statement, and what is
left is exactly
`Stacks.Cohomology.AbelianHigherDirectImage.homologyToMapHomology_eq_zero_iff`.

The identification of the two restriction maps is definitional: taking sections of `f_* G` over
`V` *is* taking sections of `G` over `f⁻¹V`, and the two inclusions `f⁻¹V ⟶ f⁻¹⊤ = ⊤` involved
are the same morphism of `Opens X`.

As with the second edge map itself, no hypothesis that `f_*` preserve injective objects is
needed for the criterion; it is needed only to have the first edge map, so the assembled data
carries it as an instance argument.

## Main definitions

* `Stacks.Cohomology.LerayLowDegree.abelianLerayLowDegreeData`: the low-degree Leray data for
  abelian sheaves, with all eight fields supplied.

## Main results

* `Stacks.Cohomology.LerayLowDegree.abelianSecondEdgeMap_app_eq_zero_iff`: the
  `secondEdgeMap_eq_zero_iff` field of `AbelianLerayLowDegreeData`.

## References

* [Stacks Project, Tag 01F2](https://stacks.math.columbia.edu/tag/01F2)
* [Stacks Project, Tag 01E4](https://stacks.math.columbia.edu/tag/01E4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.RightDerivedCoEdge Stacks.Cohomology.AbelianHigherDirectImage

universe u v

namespace Stacks.Cohomology.LerayLowDegree

attribute [local instance] abelianSheafHasSheafify

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

/-- **A first cohomology class induces the zero section of `R¹ f_* F` exactly when it vanishes
over the inverse image of a neighbourhood of every point of `Y`**: the
`secondEdgeMap_eq_zero_iff` field of `AbelianLerayLowDegreeData`.  Through an injective
resolution `I` of `F` and the complex `K = f_* I`, the second edge map becomes the canonical
comparison `H¹(Γ(Y, K)) ⟶ Γ(Y, H¹ K)` and restriction to `f⁻¹V` becomes restriction of sections
of `K` from `Y` to `V`; the criterion is then the local description of the cohomology sheaf
`H¹ K`. -/
theorem abelianSecondEdgeMap_app_eq_zero_iff
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v})
    (ξ : (abelianCohomology.{u, v} X ⊤ 1).obj F) :
    (abelianSecondEdgeMap.{u, v} f 1).app F ξ = 0 ↔
      ∀ y : Y, ∃ V : Opens Y, y ∈ V ∧
        (abelianCohomologyRestriction.{u, v} X
          (show (Opens.map f).obj V ≤ ⊤ from le_top) 1).app F ξ = 0 := by
  set I : InjectiveResolution F := InjectiveResolution.of F
  set K := ((abelianPushforward.{u, max u v} f).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj I.cocomplex
  set ζ : (((abelianSections.{u, max u v} Y ⊤).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K).homology 1 :=
    (I.isoRightDerivedObj (abelianSections.{u, max u v} X ⊤) 1).hom ξ
  -- if `a = e ≫ b ≫ g` with `g` an isomorphism, then `a x = 0 ↔ b (e x) = 0`
  have key {A B C D : AddCommGrpCat.{max u v}} {a : A ⟶ D} (e : A ⟶ B) (b : B ⟶ C) (g : C ⟶ D)
      [IsIso g] (h : a = e ≫ b ≫ g) (x : ToType A) : a x = 0 ↔ b (e x) = 0 := by
    subst h
    exact eq_zero_iff_of_isIso g (b (e x))
  have hA : (abelianSecondEdgeMap.{u, v} f 1).app F ξ = 0 ↔
      homologyToMapHomology (abelianSections.{u, max u v} Y ⊤) K 1 ζ = 0 := by
    have h := (Iso.inv_comp_eq _).mp (isoRightDerivedObjComp_inv_comp_secondEdgeApp
      (abelianPushforward.{u, max u v} f) (abelianSections.{u, max u v} Y ⊤) 1 I)
    exact @key _ _ _ _ _ _ _ _ (@Functor.map_isIso _ _ _ _ _ _ _ _ (Iso.isIso_inv _)) h ξ
  have hC (V : Opens Y) (hV : V ≤ ⊤) :
      ((abelianCohomologyRestriction.{u, v} X
        (show (Opens.map f).obj V ≤ ⊤ from le_top) 1).app F ξ = 0 ↔
      HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex
        (resAb.{u, max u v} hV) (ComplexShape.up ℕ)).app K) 1 ζ = 0) :=
    key _ _ _ (InjectiveResolution.rightDerived_app_eq
      ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}).map
        (homOfLE (show (Opens.map f).obj V ≤ ⊤ from le_top)).op) I 1) ξ
  refine hA.trans ((homologyToMapHomology_eq_zero_iff K 1 ⊤ ζ).trans ?_)
  refine ⟨fun h y ↦ ?_, fun h y _ ↦ ?_⟩
  · obtain ⟨V, hV, hyV, hz⟩ := h y (by trivial)
    exact ⟨V, hyV, (hC V hV).mpr hz⟩
  · obtain ⟨V, hyV, hz⟩ := h y
    exact ⟨V, le_top, hyV, (hC V le_top).mp hz⟩

/-- **The low-degree Leray data for abelian sheaves**, assembled from the two edge maps, their
characterisations through an arbitrary injective resolution, the injectivity of the first edge
map, the exactness between them, and the local vanishing criterion.  The only input that is not
available at the full coefficient generality `AddCommGrpCat.{max u v}` is that `f_*` preserves
injective objects, which is carried here as an instance argument; it holds unconditionally when
the coefficient universe is that of the space
(`Stacks.Cohomology.LerayLowDegree.abelianPushforward_preservesInjectiveObjects`). -/
@[sga "3 XXIV 8.5" "special case"]
def abelianLerayLowDegreeData
    [(abelianPushforward.{u, max u v} f).PreservesInjectiveObjects] :
    AbelianLerayLowDegreeData.{u, v} f where
  edgeMap n := abelianEdgeMap.{u, v} f n
  edgeMap_eq F n I J φ hφ := abelianEdgeMap_eq.{u, v} f F n I J φ hφ
  edgeMap_injective F := abelianEdgeMap_injective.{u, v} f F
  secondEdgeMap := abelianSecondEdgeMap.{u, v} f 1
  secondEdgeMap_eq F I := abelianSecondEdgeMap_eq.{u, v} f 1 F I
  edgeMap_secondEdgeMap F := abelianEdgeMap_comp_abelianSecondEdgeMap.{u, v} f F
  exact F := abelianExact.{u, v} f F
  secondEdgeMap_eq_zero_iff F ξ := abelianSecondEdgeMap_app_eq_zero_iff.{u, v} f F ξ

end Stacks.Cohomology.LerayLowDegree

end
