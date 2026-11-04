module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.OnePointSectionsMonoidal
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComparison
public import StacksFrontier.Homology.Tor.DerivedTensorComparisonLeft

/-!
# K-flatness is stable under the one-point identification

Let `R` be a commutative ring and let `({*}, R)` be the one-point ringed space.  The
identification `E : Mod(Γ({*}, 𝒪)) ≌ Mod(𝒪_{({*}, R)})` of
`Stacks.Cohomology.DerivedSectionsOnAPoint.onePointSectionsEquivalence` carries the tensor
product of modules to the tensor product of sheaves of modules, by
`Stacks.Cohomology.DerivedSectionsOnAPoint.onePointTensorComparisonIso`.  This file assembles
that degreewise comparison on total complexes and deduces that `E` carries a K-flat complex of
modules to a K-flat complex of sheaves of modules.

## Main definitions

* `Stacks.Cohomology.DerivedSectionsOnAPoint.onePointSheafFunctor` — the one-point
  identification, with its target written at the spelling of the tensor product of sheaves of
  modules.
* `Stacks.Cohomology.DerivedSectionsOnAPoint.onePointComplexEquivalence` — `E` on cochain
  complexes, as an equivalence.
* `Stacks.Cohomology.DerivedSectionsOnAPoint.onePointTensorComplexIso` — **the comparison of
  total tensor complexes**, `E(Tot(K ⊗_{Γ({*}, 𝒪)} L)) ≅ Tot(E K ⊗_{𝒪} E L)`, as an isomorphism
  of bifunctors on pairs of cochain complexes.

## Main results

* `Stacks.Cohomology.DerivedSectionsOnAPoint.acyclic_map_iff` — a complex of modules is acyclic
  exactly when its image under `E` is.
* `Stacks.Cohomology.DerivedSectionsOnAPoint.kFlat_onePointSections` — **`E` carries K-flat
  complexes to K-flat complexes.**

## Implementation notes

*Why the degreewise comparison suffices.*
`Stacks.Cohomology.DerivedPullbackTensor.totalComplexPairTransport` asks exactly for what
`onePointTensorComparisonIso` provides: an additive functor, a degreewise comparison of the two
bifunctors, and its naturality in each variable separately.  No monoidal coherence is used, which
is what makes the explicit refusal of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.OnePointSectionsMonoidal` to claim a
`CategoryTheory.Functor.Monoidal` structure harmless here.

*The two spellings of the structure sheaf.*  `structureSheafRing X` and
`Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf` are the same sheaf of rings by `rfl`, but the
first is a `def`, so a statement naming both is not type-correct at `implicit` transparency; and
the instances of the tensor product are stated at the second spelling while those of the
one-point identification are stated at the first.  Making the first `implicit_reducible`, which
is what `StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComparison` does,
is not available here: it changes the discrimination-tree keys of
`Stacks.Cohomology.DerivedSectionsOnAPoint.onePointSectionsEquivalence_functor_additive`, and that
instance is then invisible.  So the identification is re-ascribed once, in
`onePointSheafFunctor`, whose type ascription is checked at default transparency, and everything
below is written at the tensor product's spelling.

*Why acyclicity transfers.*  `E` is an equivalence, so it reflects isomorphisms and preserves
homology, and `CategoryTheory.JointlyReflectIsomorphisms.exactAt_iff` at the one-element family
`fun _ : Unit => E` turns that into the equivalence of acyclicity on both sides.  The other
direction of the K-flatness argument needs an acyclic *preimage* of an acyclic complex of sheaves,
which is the counit of `onePointComplexEquivalence`.

## References

* [Stacks Project, Tag 06YN](https://stacks.math.columbia.edu/tag/06YN)
* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.AssociatedSheaf
open Stacks.Cohomology.DerivedPullbackTensor
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.GlobalKunneth
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.DerivedSectionsOnAPoint

variable (R : Type u) [CommRing R]

/-! ### The one-point identification at the tensor product's spelling -/

/-- `Γ({*}, 𝒪)`-modules. -/
abbrev onePointModuleCat := ModuleCat.{u} (baseRing (onePointRingedSpace R))

/-- Sheaves of modules on `({*}, R)`, in the spelling the tensor product of sheaves of modules
is stated at. -/
abbrev onePointSheafCat :=
  AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules (onePointRingedSpace R)

/-- **The one-point identification**, with its target re-ascribed to the spelling of the tensor
product of sheaves of modules.  It is the functor of
`Stacks.Cohomology.DerivedSectionsOnAPoint.onePointSectionsEquivalence`, and the ascription
holds at default transparency. -/
abbrev onePointSheafFunctor : onePointModuleCat R ⥤ onePointSheafCat R :=
  (onePointSectionsEquivalence R).functor

/-- The re-ascribed identification is an equivalence.  The instance has to be restated: its
target category is spelled differently from the one
`Stacks.Cohomology.DerivedSectionsOnAPoint.onePointSectionsEquivalence` is stated at, and the
two spellings do not share a discrimination-tree key. -/
instance onePointSheafFunctor_isEquivalence : (onePointSheafFunctor R).IsEquivalence :=
  inferInstanceAs (onePointSectionsEquivalence R).functor.IsEquivalence

/-- The re-ascribed identification is additive, for the same reason. -/
instance onePointSheafFunctor_additive : (onePointSheafFunctor R).Additive :=
  inferInstanceAs (onePointSectionsEquivalence R).functor.Additive

/-- The re-ascribed identification preserves the antidiagonal coproducts a total complex is
assembled from: it is an equivalence, so it preserves every colimit. -/
instance onePointSheafFunctor_preservesAntidiagonalCoproducts (n : ℤ) :
    PreservesColimitsOfShape
      (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) ⁻¹' {n})) (onePointSheafFunctor R) :=
  inferInstanceAs (PreservesColimitsOfShape
    (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) ⁻¹' {n})) (onePointSectionsEquivalence R).functor)

/-- The total complex of the image under the re-ascribed identification of a tensor double
complex exists. -/
instance hasTotal_mapBicomplex_onePointSheafFunctor
    (K L : CochainComplex (onePointModuleCat R) ℤ) :
    HomologicalComplex₂.HasTotal
      (HomologicalComplex₂.mapBicomplex (onePointSheafFunctor R)
        ((((MonoidalCategory.curriedTensor (onePointModuleCat R)
          ).mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
            (ComplexShape.up ℤ)).obj K).obj L)) (ComplexShape.up ℤ) :=
  inferInstance

/-! ### Acyclicity across the one-point identification -/

/-- The one-element family consisting of the one-point identification jointly reflects
isomorphisms: an equivalence reflects them. -/
theorem onePointSections_jointlyReflectIsomorphisms :
    JointlyReflectIsomorphisms (fun _ : Unit => onePointSheafFunctor R) where
  isIso f h :=
    have : IsIso ((onePointSheafFunctor R).map f) := h ()
    isIso_of_reflects_iso f (onePointSheafFunctor R)

/-- **A complex of `Γ({*}, 𝒪)`-modules is acyclic exactly when its image under the one-point
identification is.**  The identification is an equivalence, hence exact and reflecting
isomorphisms. -/
theorem acyclic_map_iff (K : CochainComplex (onePointModuleCat R) ℤ) :
    K.Acyclic ↔
      (((onePointSheafFunctor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic :=
  forall_congr' fun n =>
    ((onePointSections_jointlyReflectIsomorphisms R).exactAt_iff K n).trans
      ⟨fun h => h (), fun h _ => h⟩

/-! ### The one-point identification on cochain complexes -/

/-- **The one-point identification on cochain complexes**, as an equivalence
`Comp(Mod(Γ({*}, 𝒪))) ≌ Comp(Mod(𝒪_{({*}, R)}))`. -/
abbrev onePointComplexEquivalence :=
  (onePointSectionsEquivalence R).mapHomologicalComplex (ComplexShape.up ℤ)

/-- **The comparison of total tensor complexes.**  The one-point identification carries the
total tensor complex of two complexes of modules to the total tensor complex of their images:

`E(Tot(K ⊗_{Γ({*}, 𝒪)} L)) ≅ Tot(E K ⊗_{𝒪} E L)`,

naturally in the pair `(K, L)`.  This is
`Stacks.Cohomology.DerivedPullbackTensor.totalComplexPairTransport` at the degreewise comparison
`Stacks.Cohomology.DerivedSectionsOnAPoint.onePointTensorIso`. -/
def onePointTensorComplexIso :
    totalComplexPair (MonoidalCategory.curriedTensor (onePointModuleCat R)) ⋙
        (onePointSheafFunctor R).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      ((onePointSheafFunctor R).mapHomologicalComplex (ComplexShape.up ℤ)).prod
          ((onePointSheafFunctor R).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
        totalComplexPair
          (Stacks.SheafOfModules.Tensor.sheafTensor (onePointRingedSpace R).sheaf) :=
  totalComplexPairTransport
    (MonoidalCategory.curriedTensor (onePointModuleCat R))
    (Stacks.SheafOfModules.Tensor.sheafTensor (onePointRingedSpace R).sheaf)
    (onePointSheafFunctor R)
    (onePointTensorIso R)
    (fun {_ _} u N => onePointTensorIso_naturality_left R u N)
    (fun M {_ _} v => onePointTensorIso_naturality_right R M v)

/-! ### K-flatness is stable under the one-point identification -/

/-- **The one-point identification carries K-flat complexes to K-flat complexes.**

If `K` is a K-flat complex of `Γ({*}, 𝒪)`-modules then `E K` is a K-flat complex of
`𝒪_{({*}, R)}`-modules.  Given an acyclic complex `G` of sheaves of modules, `G` is the image of
an acyclic complex `M` of modules — the one-point identification on complexes is an equivalence
and reflects acyclicity — and `Tot(E M ⊗_{𝒪} E K)` is then the image of `Tot(M ⊗ K)`, acyclic
because `K` is K-flat. -/
theorem kFlat_onePointSections (K : CochainComplex (onePointModuleCat R) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (MonoidalCategory.curriedTensor (onePointModuleCat R)) K) :
    AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat (onePointRingedSpace R)
      (((onePointSheafFunctor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
  intro G hG
  set M := (onePointComplexEquivalence R).inverse.obj G with hM
  have eG : ((onePointSheafFunctor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj M ≅ G :=
    (onePointComplexEquivalence R).counitIso.app G
  have hMacyclic : M.Acyclic := fun n =>
    (acyclic_map_iff R M).2 (fun m => HomologicalComplex.ExactAt.of_iso (hG m) eG.symm) n
  have key : (CochainComplex.KFlatBifunctor.totalComplex
      (Stacks.SheafOfModules.Tensor.sheafTensor (onePointRingedSpace R).sheaf)
      (((onePointSheafFunctor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)
      (((onePointSheafFunctor R).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K)).Acyclic := fun n =>
    HomologicalComplex.ExactAt.of_iso
      ((acyclic_map_iff R _).1 (hK M hMacyclic) n) ((onePointTensorComplexIso R).app (M, K))
  intro n
  refine HomologicalComplex.ExactAt.of_iso (key n) ?_
  exact (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (onePointRingedSpace R).sheaf
      ).map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).mapIso eG).app
    (((onePointSheafFunctor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)

end Stacks.Cohomology.DerivedSectionsOnAPoint

end
