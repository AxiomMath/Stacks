module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.StructureSheafAsADerivedUnit
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportBaseChangeHomComparison
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportFlatBaseChangeMap
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.UnitComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ClosedEmbeddingProjectionFormulaRightIso
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackMap
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaRightBaseChange

/-!
# The base change map of Stacks 0E2K is the internal-Hom base change map of Stacks 08I3

Consider a cartesian diagram of schemes

```
Z' --i'--> X'
|g         |f
Z --i----> X
```

with `i` a closed immersion and `Z`, `X'` Tor independent over `X`.  [Stacks, Tag 0E2L] says
that the map `Lg^* R ℰom(𝒪_Z, K) ⟶ R ℰom(𝒪_{Z'}, Lf^*K)` of [Stacks, Tag 0E2K] is an
isomorphism if and only if the base change map

`Lf^* R SheafHom_{𝒪_X}(𝒪_Z, K) ⟶ R SheafHom_{𝒪_{X'}}(Lf^*𝒪_Z, Lf^*K)`

of Cohomology, Remark [Stacks, Tag 08I3] is.  The source reduces this to `Ri'_*` and omits the
verification that the two maps then agree; this file supplies it.

## Main definitions

* `derivedPushforwardSheafHomAdjunction`: the adjunction `Ri_* ⊣ R ℰom(𝒪_Z, -)` of
  [Stacks, Tag 0A76] for a closed immersion of schemes, with the total right derived `Ri_*` as
  left adjoint.
* `pullbackUnitRightUnitor`: the right unit constraint of `D(𝒪_{Z'})` for the unit
  `Lg^*𝒪_Z[0]`, through the unit comparison of the derived pullback.

## Main results

* `baseChangeSheafHomExactSupportMap_app_eq_mate`: the map of [Stacks, Tag 0E2K] is the mate of
  the inverse of the base change map of [Stacks, Tag 08HY] for
  `derivedPushforwardSheafHomAdjunction`.
* `isIso_baseChangeSheafHomExactSupportMap_app_iff_isIso_derivedPullbackSheafHomMap`:
  **[Stacks, Tag 0E2L]**, and `…_comp`, the same with the target `R SheafHom(𝒪_{Z'}, Lf^*K)`.
* `tensorHomEquiv_naturalLeft`: the naturality of the bijection of [Stacks, Tag 08DI] in its
  source variable, at the spelling the map of [Stacks, Tag 08I3] is built over.

## Implementation notes

The identification the source omits is carried out over abstract data in
`StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportBaseChangeHomComparison`
(`isIso_mate_iff_isIso_homComparison_of_projection`). Its geometric inputs are: the right-handed
projection formula of [Stacks, Tag 0B53] and its invertibility along a closed immersion
([Stacks, Tag 0B55], right-handed form), the compatibility of that map with base change
(the right-handed [Stacks, Tag 0B6B]), the adjoint description of the base change map of
[Stacks, Tag 08HY], the naturality of the right unit constraint of [Stacks, Tag 0FPT], and the
naturality in the source variable of the tensor–internal-Hom bijection of [Stacks, Tag 08DI].
Through the projection formula at `𝒪_Z[0]` followed by the unit constraint, `R SheafHom(𝒪_Z, -)`
is identified with `Ri_* R ℰom(𝒪_Z, -)` by representability, without passing through
[Stacks, Tag 0A77]; the unit coherence of [Stacks, Tag 079U] is not needed, its failure being
absorbed by an automorphism of `Lg^*` (`unitDiscrepancy`).

The derived categories are written with the spaces `X.toSheafedSpace`, the spelling the
morphisms `f.toLRSHom.toShHom` produce, and the object `R ℰom(𝒪_Z, K)` is written with the
categories of that spelling where it meets the abstract statement: the kernel does not identify
the two spellings of the same category quickly enough inside the final comparison.

## References

* [Stacks Project, Tag 0E2L](https://stacks.math.columbia.edu/tag/0E2L)
* [Stacks Project, Tag 0E2K](https://stacks.math.columbia.edu/tag/0E2K)
* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 0B55](https://stacks.math.columbia.edu/tag/0B55)
* [Stacks Project, Tag 0B6B](https://stacks.math.columbia.edu/tag/0B6B)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Prod
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedProjectionFormula
open Stacks.Cohomology.DerivedInternalHomPullback
open Stacks.DerivedTensor.RingedSite
open Stacks.ClosedImmersion

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Duality.ExactSupportBaseChange

/-- The structure sheaf in degree zero, `𝒪_W[0] ∈ D(𝒪_W)`, in the spelling of the right unit
constraint of the derived tensor product. -/
abbrev unitObject (W : RingedSpace.{u, u}) :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing W)) :=
  (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing W)) 0).obj
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf W.sheaf))

/-- The right unit constraint `B ⊗^L 𝒪_W[0] ≅ B` of the derived tensor product. -/
abbrev rightUnitor {W : RingedSpace.{u, u}}
    (B : DerivedCategory (SheafOfModules.{u} (structureSheafRing W))) :
    (Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf)).obj (B, unitObject W) ≅ B :=
  (Stacks.RingedSpace.derivedTensorRightUnitorNatIso W).app B

/-! ### The unit constraint for `Lg^*𝒪_Z[0]`, and the map of Stacks 0E2K as a mate -/

variable {Z' X' Z X : Scheme.{u}} {i' : Z' ⟶ X'} {g : Z' ⟶ Z} {f : X' ⟶ X} {i : Z ⟶ X}

/-- The right unit constraint for the unit `Lg^*𝒪_Z[0]` of `D(𝒪_{Z'})`:
`B ⊗^L Lg^*𝒪_Z[0] ⟶ B ⊗^L 𝒪_{Z'}[0] ⟶ B`, through the unit comparison of the derived
pullback. -/
def pullbackUnitRightUnitor (g : Z' ⟶ Z)
    (B : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z'.toSheafedSpace))) :
    (Functor.uncurry.obj (derivedTensorProductFunctor Z'.toSheafedSpace.sheaf)).obj
        (B, (derivedPullback g.toLRSHom.toShHom).obj (unitObject Z.toSheafedSpace)) ≅ B :=
  (Functor.uncurry.obj (derivedTensorProductFunctor Z'.toSheafedSpace.sheaf)).mapIso
      (Iso.prod (Iso.refl B)
        (Stacks.RingedSpace.derivedPullbackSingleUnitIso g.toLRSHom.toShHom)) ≪≫
    rightUnitor B

/-- The unit constraint for `Lg^*𝒪_Z[0]` is natural. -/
theorem pullbackUnitRightUnitor_naturality (g : Z' ⟶ Z)
    {B B' : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z'.toSheafedSpace))}
    (x : B ⟶ B') :
    (Functor.uncurry.obj (derivedTensorProductFunctor Z'.toSheafedSpace.sheaf)).map
        (x ×ₘ 𝟙 ((derivedPullback g.toLRSHom.toShHom).obj (unitObject Z.toSheafedSpace))) ≫
        (pullbackUnitRightUnitor g B').hom = (pullbackUnitRightUnitor g B).hom ≫ x := by
  simp only [pullbackUnitRightUnitor]
  exact unitor_comp_naturality _
    (Stacks.RingedSpace.derivedPullbackSingleUnitIso g.toLRSHom.toShHom).hom
    (fun B => (rightUnitor B).hom)
    (fun x => Stacks.RingedSpace.derivedTensorRightUnitor_naturality Z'.toSheafedSpace x) x

/-- The adjunction `Ri_* ⊣ R ℰom(𝒪_Z, -)` of [Stacks, Tag 0A76] for a closed immersion of schemes,
with the total right derived functor `Ri_*` as its left adjoint. -/
def derivedPushforwardSheafHomAdjunction (i : Z ⟶ X) [IsClosedImmersion i] :
    derivedPushforward i.toLRSHom.toShHom ⊣
      (closedQuotientOfClosedImmersion i).derivedSheafHomExactSupport :=
  (closedQuotientOfClosedImmersion i).derivedSheafHomAdjunction.ofNatIsoLeft
    (closedQuotientOfClosedImmersion i).derivedPushforwardComparison

/-- **The map of [Stacks, Tag 0E2K] is the mate of the base change isomorphism**: its component
at `K` is the transpose, under `Ri'_* ⊣ R ℰom(𝒪_{Z'}, -)`, of the inverse of the derived base
change map of [Stacks, Tag 08HY] at `R ℰom(𝒪_Z, K)` followed by `Lf^*` of the counit of
`Ri_* ⊣ R ℰom(𝒪_Z, -)`, both adjunctions read with the total right derived pushforward. -/
theorem baseChangeSheafHomExactSupportMap_app_eq_mate (sq : IsPullback i' g f i)
    [IsClosedImmersion i] (htor : AlgebraicGeometry.TorIndependent i f)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) :
    (baseChangeSheafHomExactSupportMap sq htor).app K =
      ((@derivedPushforwardSheafHomAdjunction _ _ i'
        (Stacks.Cohomology.ClosedImmersionBaseChange.isClosedImmersion_of_isPullback sq)).homEquiv
          _ _)
        ((Stacks.Cohomology.ClosedImmersionBaseChange.derivedBaseChangeSquareIso sq
            htor).symm.hom.app
              ((closedQuotientOfClosedImmersion i).derivedSheafHomExactSupport.obj K) ≫
          (derivedPullback f.toLRSHom.toShHom).map
            ((derivedPushforwardSheafHomAdjunction i).counit.app
              K)) :=
  homEquiv_ofNatIsoLeft_counit (closedQuotientOfClosedImmersion i).derivedSheafHomAdjunction
    (closedQuotientOfClosedImmersion i).derivedPushforwardComparison
    (closedQuotientOfBaseChange sq).derivedSheafHomAdjunction
    (closedQuotientOfBaseChange sq).derivedPushforwardComparison
    (derivedPullback f.toLRSHom.toShHom) (derivedPullback g.toLRSHom.toShHom)
    (Stacks.Cohomology.ClosedImmersionBaseChange.derivedBaseChangeSquareIso sq htor).symm K

/-! ### Stacks 0E2L -/

/-- The adjoint description of the base change map of [Stacks, Tag 08HY] for the square, in the
shape the comparison consumes. -/
theorem derivedBaseChangeMap_homEquiv_symm (sq : IsPullback i' g f i)
    (V : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toSheafedSpace))) :
    ((derivedAdjunction i'.toLRSHom.toShHom).homEquiv _ _).symm
        (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap g.toLRSHom.toShHom
          i'.toLRSHom.toShHom i.toLRSHom.toShHom f.toLRSHom.toShHom
          (Stacks.Cohomology.ClosedImmersionBaseChange.comp_toShHom_of_isPullback sq) V) =
      (Stacks.Cohomology.DerivedProjectionFormula.derivedPullbackSquareIso g.toLRSHom.toShHom
          i'.toLRSHom.toShHom i.toLRSHom.toShHom f.toLRSHom.toShHom
          (Stacks.Cohomology.ClosedImmersionBaseChange.comp_toShHom_of_isPullback sq)).hom.app
          ((derivedPushforward i.toLRSHom.toShHom).obj V) ≫
        (derivedPullback g.toLRSHom.toShHom).map
          ((derivedAdjunction i.toLRSHom.toShHom).counit.app V) :=
  (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_adjoint g.toLRSHom.toShHom
    i'.toLRSHom.toShHom i.toLRSHom.toShHom f.toLRSHom.toShHom
    (Stacks.Cohomology.ClosedImmersionBaseChange.comp_toShHom_of_isPullback sq) V).trans
    (Category.assoc _ _ _).symm

section InternalHomSpelling

attribute [local implicit_reducible] structureSheafRing
attribute [local instance_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

/-- The naturality in the source variable of the bijection of [Stacks, Tag 08DI], at the
spelling `tensorHomEquiv` the map of [Stacks, Tag 08I3] is built over: the bijection is, as a
family, the currying bijection of [Stacks, Tag 08J8] whose naturality is
`Stacks.Cohomology.DerivedInternalHomPullback.tensorHomEquivNaturalLeft_ringedSpace`. -/
theorem tensorHomEquiv_naturalLeft (W : RingedSpace.{u, u}) :
    Transpose.TensorHomEquivNaturalLeft (Stacks.SheafOfModules.derivedSheafHom W.sheaf)
      (internalHomTensorUncurried W)
      (Stacks.Cohomology.DerivedInternalHomPullback.tensorHomEquiv W) := by
  have h : Stacks.Cohomology.DerivedInternalHomPullback.tensorHomEquiv W =
      fun A B C => (RingedSite.derivedCurryHomEquiv
        (Stacks.SheafOfModules.ringedSite W.sheaf) A B C).toEquiv := rfl
  rw [h]
  exact Stacks.Cohomology.DerivedInternalHomPullback.tensorHomEquivNaturalLeft_ringedSpace W

end InternalHomSpelling

-- Declared outside the section below, so that its type is elaborated in the spelling of the
-- derived categories of [Stacks, Tag 0E2K].
variable (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))

section InternalHomSpelling

-- As in `StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackMap`: the
-- derived pullback and the derived internal Hom name the structure sheaf of a ringed space
-- differently, and the two spellings agree only after unfolding these definitions.
attribute [local implicit_reducible] structureSheafRing
attribute [local instance_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

/-- **Stacks Project, Tag 0E2L.** Consider a cartesian square of schemes

```
Z' --i'--> X'
|g         |f
Z --i----> X
```

with `i` a closed immersion and `Z`, `X'` Tor independent over `X`, and `K ∈ D(𝒪_X)`. The base
change map `Lg^* R ℰom(𝒪_Z, K) ⟶ R ℰom(𝒪_{Z'}, Lf^*K)` of [Stacks, Tag 0E2K] is an isomorphism
if and only if the base change map

`Lf^* R SheafHom_{𝒪_X}(𝒪_Z, K) ⟶ R SheafHom_{𝒪_{X'}}(Lf^*𝒪_Z, Lf^*K)`

of Cohomology, Remark [Stacks, Tag 08I3] is an isomorphism, `𝒪_Z` standing for `Ri_*𝒪_Z[0]`.
The source writes the target as `R SheafHom_{𝒪_{X'}}(𝒪_{Z'}, Lf^*K)`, through
`𝒪_{Z'} = Lf^*𝒪_Z` (Tor independence); the map of [Stacks, Tag 08I3] has `Lf^*𝒪_Z` there, and
that is the map stated here.

The source proves this by applying `Ri'_*` and omits the verification that the result is the map
of [Stacks, Tag 08I3]. Here that verification is
`isIso_mate_iff_isIso_homComparison_of_projection`: both maps are read off the projection formula
of [Stacks, Tag 0B55] in its right-handed form, whose compatibility with base change is the
right-handed [Stacks, Tag 0B6B]. -/
@[stacks 0E2L]
theorem isIso_baseChangeSheafHomExactSupportMap_app_iff_isIso_derivedPullbackSheafHomMap
    (sq : IsPullback i' g f i) [IsClosedImmersion i]
    (htor : AlgebraicGeometry.TorIndependent i f) :
    IsIso ((baseChangeSheafHomExactSupportMap sq htor).app K) ↔
      IsIso (derivedPullbackSheafHomMap f.toLRSHom.toShHom
        ((derivedPushforward i.toLRSHom.toShHom).obj (unitObject Z.toSheafedSpace)) K) := by
  have : IsClosedImmersion i' :=
    Stacks.Cohomology.ClosedImmersionBaseChange.isClosedImmersion_of_isPullback sq
  have hm := baseChangeSheafHomExactSupportMap_app_eq_mate sq htor K
  have hbi : ∀ N : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toSheafedSpace)),
      IsIso (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap g.toLRSHom.toShHom
        i'.toLRSHom.toShHom i.toLRSHom.toShHom f.toLRSHom.toShHom
        (Stacks.Cohomology.ClosedImmersionBaseChange.comp_toShHom_of_isPullback sq) N) :=
    fun N => Iso.isIso_hom
      ((Stacks.Cohomology.ClosedImmersionBaseChange.derivedBaseChangeSquareIso sq htor).app N)
  have := hbi
  have hinv : (Stacks.Cohomology.ClosedImmersionBaseChange.derivedBaseChangeSquareIso sq
      htor).symm.hom.app (@Functor.obj
            (DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toSheafedSpace))) _
            (DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toSheafedSpace))) _
            (closedQuotientOfClosedImmersion i).derivedSheafHomExactSupport K) =
      inv (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap g.toLRSHom.toShHom
        i'.toLRSHom.toShHom i.toLRSHom.toShHom f.toLRSHom.toShHom
        (Stacks.Cohomology.ClosedImmersionBaseChange.comp_toShHom_of_isPullback sq)
        (@Functor.obj
          (DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toSheafedSpace))) _
          (DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toSheafedSpace))) _
          (closedQuotientOfClosedImmersion i).derivedSheafHomExactSupport K)) :=
    (IsIso.Iso.inv_hom ((Stacks.Cohomology.ClosedImmersionBaseChange.derivedBaseChangeSquareIso
      sq htor).app _)).symm
  have happ :=
    (isIso_mate_iff_isIso_homComparison_of_projection (derivedAdjunction i.toLRSHom.toShHom)
    (derivedPushforwardSheafHomAdjunction i)
    (derivedAdjunction i'.toLRSHom.toShHom)
    (derivedPushforwardSheafHomAdjunction i')
    (derivedPullback f.toLRSHom.toShHom) (derivedPullback g.toLRSHom.toShHom)
    (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap g.toLRSHom.toShHom
        i'.toLRSHom.toShHom i.toLRSHom.toShHom f.toLRSHom.toShHom
        (Stacks.Cohomology.ClosedImmersionBaseChange.comp_toShHom_of_isPullback sq))
    (Stacks.Cohomology.DerivedProjectionFormula.derivedPullbackSquareIso
      g.toLRSHom.toShHom i'.toLRSHom.toShHom i.toLRSHom.toShHom f.toLRSHom.toShHom
      (Stacks.Cohomology.ClosedImmersionBaseChange.comp_toShHom_of_isPullback sq))
    (Functor.uncurry.obj (derivedTensorProductFunctor X.toSheafedSpace.sheaf))
    (Functor.uncurry.obj (derivedTensorProductFunctor X'.toSheafedSpace.sheaf))
    (Functor.uncurry.obj (derivedTensorProductFunctor Z.toSheafedSpace.sheaf))
    (Functor.uncurry.obj (derivedTensorProductFunctor Z'.toSheafedSpace.sheaf))
    (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso f.toLRSHom.toShHom)
    (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso g.toLRSHom.toShHom)
    (fun K N => projectionFormulaMapRight i.toLRSHom.toShHom K N)
    (fun K N => projectionFormulaMapRight i'.toLRSHom.toShHom K N)
    (unitObject Z.toSheafedSpace) rightUnitor (pullbackUnitRightUnitor g)
    (Stacks.SheafOfModules.derivedSheafHom X.toSheafedSpace.sheaf)
    (Stacks.SheafOfModules.derivedSheafHom X'.toSheafedSpace.sheaf)
    (internalHomTensorUncurried X.toSheafedSpace) (internalHomTensorUncurried X'.toSheafedSpace)
    (Stacks.Cohomology.DerivedInternalHomPullback.tensorHomEquiv X.toSheafedSpace)
    (Stacks.Cohomology.DerivedInternalHomPullback.tensorHomEquiv X'.toSheafedSpace)
    (tensorBridge X.toSheafedSpace) (tensorBridge X'.toSheafedSpace)
    hbi
    (fun W => isIso_projectionFormulaMapRight_of_isClosedEmbedding i.toLRSHom.toShHom
      (Stacks.ClosedImmersion.isClosedEmbedding_base_toShHom i) W _)
    (fun W => isIso_projectionFormulaMapRight_of_isClosedEmbedding i'.toLRSHom.toShHom
      (Stacks.ClosedImmersion.isClosedEmbedding_base_toShHom i') W _)
    ⟨fun {A B} φ hφ => by
      have : IsIso ((modulePushforward (closedQuotientOfBaseChange sq).i).mapDerivedCategory.map
          φ) :=
        (NatIso.isIso_map_iff (closedQuotientOfBaseChange sq).derivedPushforwardComparison φ).2 hφ
      exact isIso_of_isIso_modulePushforward_map (closedQuotientOfBaseChange sq) φ this⟩
    (fun x => Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_naturality
      g.toLRSHom.toShHom i'.toLRSHom.toShHom i.toLRSHom.toShHom f.toLRSHom.toShHom
      (Stacks.Cohomology.ClosedImmersionBaseChange.comp_toShHom_of_isPullback sq) x)
    (fun x => Stacks.RingedSpace.derivedTensorRightUnitor_naturality Z.toSheafedSpace x)
    (fun x => pullbackUnitRightUnitor_naturality g x)
    (fun x => projectionFormulaMapRight_natural i.toLRSHom.toShHom x (𝟙 _))
    (fun x => projectionFormulaMapRight_natural i'.toLRSHom.toShHom x (𝟙 _))
    (fun K N => projectionFormulaMapRight_derivedBaseChangeMap_eq g.toLRSHom.toShHom
      i'.toLRSHom.toShHom i.toLRSHom.toShHom f.toLRSHom.toShHom
      (Stacks.Cohomology.ClosedImmersionBaseChange.comp_toShHom_of_isPullback sq) N K)
    (fun V => derivedBaseChangeMap_homEquiv_symm sq V)
    (tensorHomEquiv_naturalLeft X.toSheafedSpace)
    (tensorHomEquiv_naturalLeft X'.toSheafedSpace) K)
  have hm' := hm.trans (congrArg (fun t =>
      ((derivedPushforwardSheafHomAdjunction i').homEquiv
        ((derivedPullback g.toLRSHom.toShHom).obj
          ((closedQuotientOfClosedImmersion i).derivedSheafHomExactSupport.obj K))
        ((derivedPullback f.toLRSHom.toShHom).obj K))
        (t ≫ (derivedPullback f.toLRSHom.toShHom).map
          ((derivedPushforwardSheafHomAdjunction i).counit.app
            K))) hinv)
  exact (iff_of_eq (congrArg IsIso hm')).trans (happ.trans (iff_of_eq rfl))

/-- **The identification `𝒪_{Z'} = Lf^*𝒪_Z` of the source**, in `D(𝒪_{X'})`:
`Ri'_*𝒪_{Z'}[0] ≅ Ri'_* Lg^*𝒪_Z[0] ≅ Lf^* Ri_*𝒪_Z[0]`, by the unit comparison of the derived
pullback along `g` and the Tor-independent base change isomorphism of [Stacks, Tag 0E23]. -/
def pushforwardStructureSheafBaseChangeIso (sq : IsPullback i' g f i) [IsClosedImmersion i]
    (htor : AlgebraicGeometry.TorIndependent i f) :
    (derivedPushforward i'.toLRSHom.toShHom).obj (unitObject Z'.toSheafedSpace) ≅
      (derivedPullback f.toLRSHom.toShHom).obj
        ((derivedPushforward i.toLRSHom.toShHom).obj (unitObject Z.toSheafedSpace)) :=
  (derivedPushforward i'.toLRSHom.toShHom).mapIso
      (Stacks.RingedSpace.derivedPullbackSingleUnitIso g.toLRSHom.toShHom).symm ≪≫
    ((Stacks.Cohomology.ClosedImmersionBaseChange.derivedBaseChangeSquareIso sq htor).app
      (unitObject Z.toSheafedSpace)).symm

/-- **Stacks Project, Tag 0E2L**, with the target written as the source writes it. In the
situation of
`isIso_baseChangeSheafHomExactSupportMap_app_iff_isIso_derivedPullbackSheafHomMap`, the map of
[Stacks, Tag 0E2K] is an isomorphism if and only if the base change map

`Lf^* R SheafHom_{𝒪_X}(𝒪_Z, K) ⟶ R SheafHom_{𝒪_{X'}}(Lf^*𝒪_Z, Lf^*K)`
`= R SheafHom_{𝒪_{X'}}(𝒪_{Z'}, Lf^*K)`

of Cohomology, Remark [Stacks, Tag 08I3] is, the equality being the identification
`pushforwardStructureSheafBaseChangeIso` of `𝒪_{Z'}` with `Lf^*𝒪_Z` by Tor independence. -/
@[stacks 0E2L "the same statement, with the target written R SheafHom(O_{Z'}, Lf^*K) through \
the identification O_{Z'} = Lf^*O_Z of Tor independence, as the source writes it"]
theorem isIso_baseChangeSheafHomExactSupportMap_app_iff_isIso_derivedPullbackSheafHomMap_comp
    (sq : IsPullback i' g f i) [IsClosedImmersion i]
    (htor : AlgebraicGeometry.TorIndependent i f) :
    IsIso ((baseChangeSheafHomExactSupportMap sq htor).app K) ↔
      IsIso (derivedPullbackSheafHomMap f.toLRSHom.toShHom
          ((derivedPushforward i.toLRSHom.toShHom).obj (unitObject Z.toSheafedSpace)) K ≫
        ((Stacks.SheafOfModules.derivedSheafHom X'.toSheafedSpace.sheaf).map
          (pushforwardStructureSheafBaseChangeIso sq htor).hom.op).app
          ((derivedPullback f.toLRSHom.toShHom).obj K)) := by
  refine (isIso_baseChangeSheafHomExactSupportMap_app_iff_isIso_derivedPullbackSheafHomMap
    K sq htor).trans ?_
  have hγ : IsIso (((Stacks.SheafOfModules.derivedSheafHom X'.toSheafedSpace.sheaf).map
      (pushforwardStructureSheafBaseChangeIso sq htor).hom.op).app
        ((derivedPullback f.toLRSHom.toShHom).obj K)) :=
    Iso.isIso_hom (((Stacks.SheafOfModules.derivedSheafHom X'.toSheafedSpace.sheaf).mapIso
      (pushforwardStructureSheafBaseChangeIso sq htor).op).app
        ((derivedPullback f.toLRSHom.toShHom).obj K))
  exact (@isIso_comp_right_iff _ _ _ _ _ _ _ hγ).symm

end InternalHomSpelling

end Stacks.Duality.ExactSupportBaseChange

end
