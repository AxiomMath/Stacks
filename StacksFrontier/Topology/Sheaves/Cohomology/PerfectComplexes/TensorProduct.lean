module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.RestrictionToAnOpen
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.TensorProduct
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.LocalCriterion
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PseudoCoherentIso
import StacksCore.Algebra.Homology.QuasiIso
import StacksCore.Tactic.EgaSgaAttribute
import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.MappingCone

/-!
# The derived tensor product of two perfect complexes

Let `X` be a ringed space.  An object of `D(𝒪_X)` is *perfect* when it is represented by a
complex which, on an open covering of `X`, receives quasi-isomorphisms from strictly perfect
complexes.  This file proves that the derived tensor product of two perfect objects is perfect.

## Main results

* `AlgebraicGeometry.RingedSpace.isPerfectComplex_tensorComplex`: the total tensor complex of two
  perfect complexes, the second of which is K-flat, is perfect.
* `AlgebraicGeometry.RingedSpace.isPerfect_derivedTensorProduct` ([stacks 09J5]): the derived
  tensor product of two perfect objects of `D(𝒪_X)` is perfect.
* `AlgebraicGeometry.RingedSpace.isPerfect_canonicalDerivedTensorProduct`: the same for the
  canonical derived tensor product of Tag 06YU.

## Implementation notes

The proof is the source's, carried out on complexes: locally both factors receive
quasi-isomorphisms from strictly perfect complexes, the tensor product of two strictly perfect
complexes is strictly perfect (Tag 09J2, read on a ringed space by
`StrictlyPerfect.isStrictlyPerfect_tensorComplex`), and a strictly perfect complex is K-flat, so
tensoring with it preserves quasi-isomorphisms.  No derived category of an open subspace occurs.

* `AlgebraicGeometry.RingedSpace.isPerfectComplex_tensorComplex` is the statement on complexes.
  Near a point, the two factors `A` and `B` receive quasi-isomorphisms `p : P ⟶ A|_W` and
  `q : Q ⟶ B|_W` from strictly perfect complexes over a common open `W`, and
  `Tot(P ⊗ Q) ⟶ Tot(P ⊗ B|_W) ⟶ Tot(A|_W ⊗ B|_W)` is a quasi-isomorphism: the first map because
  `P` is K-flat, hence K-flat in the first variable by the symmetry of the tensor product
  (`Stacks.DerivedTensor.RingedSite.kFlatLeft_of_kFlat`), the second because `B|_W` is K-flat
  (`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.kFlat_restrictComplex`, Tag 06YC at the
  open immersion).  Restriction to `W` commutes with the total tensor complex
  (`Stacks.Cohomology.RestrictionTensor.restrictComplexTensorIso`), so `Tot(A ⊗ B)|_W` receives a
  quasi-isomorphism from the strictly perfect complex `Tot(P ⊗ Q)`.
* For Tag 09J5, a K-flat resolution `B → F` of a representative of the second object exists
  (Tag 06YS), and `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.comparisonRight`
  identifies the derived tensor product with the class of `Tot(E ⊗ B)` for a representative `E`
  of the first object.  Taking `E` perfect, `B` is perfect because perfectness of complexes is
  invariant under quasi-isomorphisms
  (`AlgebraicGeometry.RingedSpace.isPerfectComplex_iff_of_quasiIso`), and `Tot(E ⊗ B)` is the
  global perfect representative.

The bifunctor `⊗` of the open subspace is passed explicitly to
`CochainComplex.KFlatBifunctor.quasiIso_of_kFlatLeft` and
`CochainComplex.KFlatBifunctor.quasiIso_of_kFlat`, and the K-flatness of `B|_W`, which
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.kFlat_restrictComplex` states at the
`Stacks.Cohomology.HigherDirectImage.restrictToOpen` spelling of the open subspace, is restated
at the `X.restrict` spelling: otherwise the categories are read off complexes at another spelling
than the one the additivity instances of `⊗` are stated at, and instance search does not find
them.  Quasi-isomorphisms are handled degreewise, through the isomorphisms they induce on
cohomology, as in `StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.MappingCone`.

The statement of Tag 09J5 is for an arbitrary
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct X.sheaf` rather than for the canonical one:
only the `comparisonRight` field is used, so this is the natural generality, and
`AlgebraicGeometry.RingedSpace.isPerfect_canonicalDerivedTensorProduct` is the specialization a
consumer holding the canonical one needs.  It is the shape
`CategoryTheory.Pretriangulated.K0.TensorStructure.restrict` consumes: a hypothesis
`∀ Y Z, P Y → P Z → P ((T.tensor.obj Y).obj Z)` for the bifunctor of the tensor structure and
`P` the perfectness property, with no further hypothesis on `Y` or `Z`.

The derived category of `X` is a hypothesis with an arbitrary universe, and it is stated at the
`Stacks.DerivedTensor.RingedSite.Modules` spelling of the category of `𝒪_X`-modules, which is
the one the derived tensor product is stated at;
`AlgebraicGeometry.RingedSpace.hasDerivedCategoryOXMod` carries it across to the
`StrictlyPerfect.OXMod` spelling, which is the one perfectness is stated at.  The two are equal
by `rfl` but instance search does not cross them, the `Category` instances reaching the
structure sheaf of rings by different routes.

## References

* [Stacks Project, Lemma 20.46.6 (Tag 09J5)](https://stacks.math.columbia.edu/tag/09J5)
* [Stacks Project, Lemma 20.46.3 (Tag 09J2)](https://stacks.math.columbia.edu/tag/09J2)
* [Stacks Project, Lemma 20.26.9 (Tag 06YS)](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YC](https://stacks.math.columbia.edu/tag/06YC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.RingedSpace.KFlatDerivedPullback
open StrictlyPerfect

namespace AlgebraicGeometry.RingedSpace

universe d u

/-! ### The total tensor complex of two perfect complexes -/

/-- **The total tensor complex of two perfect complexes, the second of which is K-flat, is
perfect.**

Near a point, take quasi-isomorphisms `p : P ⟶ A|_W` and `q : Q ⟶ B|_W` from strictly perfect
complexes over a common open `W`.  The composite `Tot(P ⊗ Q) ⟶ Tot(P ⊗ B|_W) ⟶ Tot(A|_W ⊗ B|_W)`
is a quasi-isomorphism, since `P` and `B|_W` are K-flat; its source is strictly perfect
(Tag 09J2), and its target is `Tot(A ⊗ B)|_W`. -/
theorem isPerfectComplex_tensorComplex {X : RingedSpace.{u, u}}
    {A B : CochainComplex (KFlatDerivedPullback.Modules X) ℤ} (hA : IsPerfectComplex A)
    (hB : IsPerfectComplex B) (hB' : KFlat X B) :
    IsPerfectComplex (((Stacks.SheafOfModules.Tensor.tensorComplex X.sheaf).obj A).obj B) := by
  refine isPerfectComplex_of_forall_exists fun x => ?_
  obtain ⟨U₁, hx₁, P₁, hP₁, p₁, hp₁⟩ := hA.exists_local x
  obtain ⟨U₂, hx₂, Q₁, hQ₁, q₁, hq₁⟩ := hB.exists_local x
  obtain ⟨P, hP, p, hp⟩ := exists_restricted_quasiIso (inf_le_left : U₁ ⊓ U₂ ≤ U₁) A P₁ hP₁ p₁ hp₁
  obtain ⟨Q, hQ, q, hq⟩ := exists_restricted_quasiIso (inf_le_right : U₁ ⊓ U₂ ≤ U₂) B Q₁ hQ₁ q₁ hq₁
  have hBW : KFlat (X.restrict (U₁ ⊓ U₂).isOpenEmbedding) (restrictComplex B (U₁ ⊓ U₂)) :=
    kFlat_restrictComplex _ B hB'
  have hq' := CochainComplex.KFlatBifunctor.quasiIso_of_kFlatLeft
    (Stacks.SheafOfModules.Tensor.sheafTensor (X.restrict (U₁ ⊓ U₂).isOpenEmbedding).sheaf) P
    (Stacks.DerivedTensor.RingedSite.kFlatLeft_of_kFlat _ (kFlat_of_isStrictlyPerfect P hP)) q hq
  have hp' := CochainComplex.KFlatBifunctor.quasiIso_of_kFlat
    (Stacks.SheafOfModules.Tensor.sheafTensor (X.restrict (U₁ ⊓ U₂).isOpenEmbedding).sheaf) _ hBW
    p hp
  refine ⟨U₁ ⊓ U₂, ⟨hx₁, hx₂⟩, _, isStrictlyPerfect_tensorComplex _ P Q hP hQ,
    ((Stacks.SheafOfModules.Tensor.tensorComplex
        (X.restrict (U₁ ⊓ U₂).isOpenEmbedding).sheaf).obj P).map q ≫
      ((Stacks.SheafOfModules.Tensor.tensorComplex
        (X.restrict (U₁ ⊓ U₂).isOpenEmbedding).sheaf).map p).app _ ≫
      (Stacks.Cohomology.RestrictionTensor.restrictComplexTensorIso X (U₁ ⊓ U₂) A B).inv, ?_⟩
  exact (quasiIso_iff_isIso_homologyMap _).2 fun j => isIso_homologyMap_comp _ _ j
    ((quasiIso_iff_isIso_homologyMap _).1 hq' j) (isIso_homologyMap_comp _ _ j
      ((quasiIso_iff_isIso_homologyMap _).1 hp' j) (isIso_homologyMap_iso_hom
        (Stacks.Cohomology.RestrictionTensor.restrictComplexTensorIso X (U₁ ⊓ U₂) A B).symm j))

/-! ### The derived tensor product of perfect objects -/

section Main

variable (X : RingedSpace.{u, u})
  [HasDerivedCategory.{d} (Stacks.DerivedTensor.RingedSite.Modules X.sheaf)]

/-- The derived category of `𝒪_X`-modules, at the `StrictlyPerfect.OXMod` spelling of that
category.  It is the same category as `Stacks.DerivedTensor.RingedSite.Modules X.sheaf`, by
`rfl`, but instance search does not cross the two spellings: their `Category` instances reach
the structure sheaf of rings through `StrictlyPerfect.structureSheafOfRings` and through
`Stacks.SheafOfModules.Tensor.ringSheaf` respectively.

Its priority is low: it is needed only to elaborate the statements below, and it must never be
preferred to a derived category a consumer has already fixed on `StrictlyPerfect.OXMod X` by
other means. -/
instance (priority := low) hasDerivedCategoryOXMod : HasDerivedCategory.{d} (OXMod.{u, u} X) :=
  inferInstanceAs (HasDerivedCategory.{d} (Stacks.DerivedTensor.RingedSite.Modules X.sheaf))

/-- **The derived tensor product of two perfect objects of `D(𝒪_X)` is perfect.**

Represent the objects by perfect complexes `E` and `F`, and replace `F` by a K-flat resolution
`B`, which is perfect as well.  The derived tensor product is then the class of the total tensor
complex `Tot(E ⊗_{𝒪_X} B)`, which is perfect by
`AlgebraicGeometry.RingedSpace.isPerfectComplex_tensorComplex`.

Stated for an arbitrary derived tensor product, since only its `comparisonRight` field is used. -/
@[stacks 09J5, sga "6 I 4.19" "single ringed space", sga "6 0 4.2" "more general"]
theorem isPerfect_derivedTensorProduct
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct X.sheaf)
    (K L : DerivedCategory (OXMod.{u, u} X)) (hK : IsPerfect K) (hL : IsPerfect L) :
    IsPerfect ((T.tensor.obj K).obj L) := by
  obtain ⟨E, hE, ⟨eK⟩⟩ := hK
  obtain ⟨F, hF, ⟨eL⟩⟩ := hL
  obtain ⟨B, q, hB, -, hq, -⟩ := exists_kFlatResolution X F
  have eG : (DerivedCategory.Q (C := OXMod.{u, u} X)).obj
      (((Stacks.SheafOfModules.Tensor.tensorComplex X.sheaf).obj E).obj B) ≅
      (T.tensor.obj K).obj L :=
    (T.comparisonRight E B hB).symm ≪≫ (T.tensor.mapIso eK).app _ ≪≫
      (T.tensor.obj K).mapIso (_root_.CochainComplex.derivedIsoOfQuasiIso q hq ≪≫ eL)
  exact ⟨_, isPerfectComplex_tensorComplex hE ((isPerfectComplex_iff_of_quasiIso q hq).2 hF) hB,
    ⟨eG⟩⟩

/-- **The canonical derived tensor product of two perfect objects of `D(𝒪_X)` is perfect.**
`AlgebraicGeometry.RingedSpace.isPerfect_derivedTensorProduct` at the derived tensor product of
Tag 06YU. -/
theorem isPerfect_canonicalDerivedTensorProduct
    (K L : DerivedCategory (OXMod.{u, u} X)) (hK : IsPerfect K) (hL : IsPerfect L) :
    IsPerfect
      (((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
        X.sheaf).tensor.obj K).obj L) :=
  isPerfect_derivedTensorProduct X _ K L hK hL

end Main

end AlgebraicGeometry.RingedSpace

end
