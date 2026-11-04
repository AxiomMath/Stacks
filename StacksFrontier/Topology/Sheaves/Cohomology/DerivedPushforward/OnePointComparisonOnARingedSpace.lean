module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.CategoryTheory.Functor.UncurryComposition
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.CanonicalDerivedTensorComparison
public import StacksFrontier.Homology.KFlat.ScalarEquivalenceDerivedTensor
public import StacksFrontier.Homology.Tor.CanonicalTensorDerivedBifunctor
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.DerivedSectionsLeftAdjoint
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalCupProduct
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.OnePointDerivedTensor
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormula

/-!
# The one-point comparison on an arbitrary ringed space

Let `(S, 𝒪_S)` be a ringed space and `A = Γ(S, 𝒪_S)`. We construct
`Stacks.Cohomology.DerivedGlobalCupProduct.OnePointComparison S`, the input of the global cup
product of [Stacks, Section 0FKU], on an **arbitrary** ringed space, with an **invertible** third
field.

The structure has three fields: a functor `L : D(A) ⥤ D(𝒪_S)`, an adjunction `L ⊣ RΓ(S, -)`, and
a comparison of bifunctors `L(x ⊗^𝐋_A y) ⟶ L x ⊗^𝐋_{𝒪_S} L y`. The first two are
`Stacks.Cohomology.DerivedSectionsLeftAdjoint.derivedBaseExtension` and
`derivedSectionsAdjunction`; the third is the `hom` of an isomorphism of bifunctors,

`L(x ⊗^𝐋_A y) ≅ L x ⊗^𝐋_{𝒪_S} L y`.

Here `L` is the composite of restriction of scalars along `π^♯`, the one-point identification,
and the derived pullback along the structure morphism `π : S ⟶ ({*}, A)` of [Stacks, Tag 01BH],
and the isomorphism is the composite of the comparisons of derived tensor products along each of
the three factors, from the derived tensor product over `A` of [Stacks, Tag 064M], through the
derived tensor product of [Stacks, Tag 06YU] on the one-point space, to the derived
pullback-tensor comparison of [Stacks, Tag 079U] along `Lπ^*`.

## Main definitions

* `Stacks.Cohomology.DerivedSectionsLeftAdjoint.derivedSectionsTensorIso` — **the comparison as
  an isomorphism of bifunctors**: `L(x ⊗^𝐋_A y) ≅ L x ⊗^𝐋_{𝒪_S} L y`, on arbitrary objects of
  `D(A)` and natural in both of them.
* `Stacks.Cohomology.DerivedSectionsLeftAdjoint.onePointComparisonOnARingedSpace` — **the
  one-point comparison on an arbitrary ringed space**, with fields `derivedBaseExtension`,
  `derivedSectionsAdjunction` and the `hom` of `derivedSectionsTensorIso`.
* `Stacks.Cohomology.DerivedSectionsLeftAdjoint.tensorComparisonComp` — the pasting of two
  comparisons of uncurried bifunctors along a composite of functors.

## Main results

* `isIso_onePointComparisonOnARingedSpace_tensorComparison_app`, in the namespace
  `Stacks.Cohomology.DerivedSectionsLeftAdjoint` — **the third field is invertible at every
  pair**, being the `hom` of an isomorphism of bifunctors.

## References

* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 064M](https://stacks.math.columbia.edu/tag/064M)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TopologicalSpace
open CochainComplex.KFlatBifunctor
open Stacks.AssociatedSheaf
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedGlobalCupProduct
open Stacks.Cohomology.DerivedSectionsOnAPoint
open Stacks.Cohomology.GlobalKunneth
open Stacks.DerivedTensor.RingedSite

universe u

namespace Stacks.Cohomology.DerivedSectionsLeftAdjoint

attribute [local instance] HasDerivedCategory.standard

/-! ### Pasting two comparisons of bifunctors -/

/-- **A comparison of uncurried bifunctors pastes along a composite of functors.**  If `U` carries
the bifunctor `P` to the bifunctor `Q` and `V` carries `Q` to `R`, then `U ⋙ V` carries `P` to
`R`: whisker the first comparison with `V`, then the second with `U × U`. -/
def tensorComparisonComp {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂] [Category C₃]
    (P : C₁ × C₁ ⥤ C₁) (Q : C₂ × C₂ ⥤ C₂) (R : C₃ × C₃ ⥤ C₃) (U : C₁ ⥤ C₂) (V : C₂ ⥤ C₃)
    (α : P ⋙ U ≅ U.prod U ⋙ Q) (β : Q ⋙ V ≅ V.prod V ⋙ R) :
    P ⋙ U ⋙ V ≅ (U ⋙ V).prod (U ⋙ V) ⋙ R :=
  Functor.isoWhiskerRight α V ≪≫ Functor.isoWhiskerLeft (U.prod U) β

variable (S : RingedSpace.{u, u})

/-! ### The spelling bridge -/

/-- **Restriction of scalars along `π^♯` on derived categories is restriction of scalars along
the ring isomorphism `Γ({*}, 𝒪) ≃+* A`**, the inverse of
`Stacks.AssociatedSheaf.coefficientRingEquiv`. -/
def baseRestrictMapDerivedIso :
    (baseRestrict S).mapDerivedCategory ≅
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
        ((coefficientRingEquiv (R := (baseRing S : Type u))).symm :
          (baseRing (basePoint S) : Type u) ≃+*
            (baseRing S : Type u))).functor.mapDerivedCategory :=
  Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _ (eqToIso (baseRestrict_eq S))

/-! ### The three stages of the comparison -/

/-- **The derived tensor product of `A`-modules is carried to that of `Γ({*}, 𝒪)`-modules by
restriction of scalars along `π^♯`**, as an isomorphism of bifunctors on `D(A) × D(A)`. -/
def baseRestrictDerivedTensorIso :
    Functor.uncurry.obj (derivedBifunctor (curriedTensor (ModuleCat.{u} (baseRing S)))) ⋙
        (baseRestrict S).mapDerivedCategory ≅
      ((baseRestrict S).mapDerivedCategory).prod ((baseRestrict S).mapDerivedCategory) ⋙
        Functor.uncurry.obj
          (derivedBifunctor (curriedTensor (ModuleCat.{u} (baseRing (basePoint S))))) :=
  Functor.isoWhiskerLeft _ (baseRestrictMapDerivedIso S) ≪≫
    (Functor.uncurryCompRightIso _ _).symm ≪≫
    Functor.uncurry.mapIso
      (CochainComplex.KFlatBifunctor.restrictScalarsDerivedTensorIso
        (R := (baseRing (basePoint S) : Type u)) (S := (baseRing S : Type u))
        (coefficientRingEquiv (R := (baseRing S : Type u))).symm) ≪≫
    eqToIso (Functor.uncurry_whiskeringLeft_comp _ _ _) ≪≫
    Functor.isoWhiskerRight
      (NatIso.prod (baseRestrictMapDerivedIso S) (baseRestrictMapDerivedIso S)).symm _

/-- **The derived tensor product of `Γ({*}, 𝒪)`-modules is carried to the derived tensor product
of [Stacks, Tag 06YU] on the one-point space `({*}, A)` by the one-point identification**, as an
isomorphism of bifunctors on `D(Γ({*}, 𝒪)) × D(Γ({*}, 𝒪))`. -/
def onePointDerivedTensorUncurriedIso :
    Functor.uncurry.obj
          (derivedBifunctor (curriedTensor (ModuleCat.{u} (baseRing (basePoint S))))) ⋙
        (onePointIdentificationFunctor (baseRing S)).mapDerivedCategory ≅
      ((onePointIdentificationFunctor (baseRing S)).mapDerivedCategory).prod
          ((onePointIdentificationFunctor (baseRing S)).mapDerivedCategory) ⋙
        Functor.uncurry.obj (derivedTensorProductFunctor (basePoint S).sheaf) :=
  (Functor.uncurryCompRightIso _ _).symm ≪≫
    Functor.uncurry.mapIso
      (derivedTransportIsoOfEquivalence
        (curriedTensor (ModuleCat.{u} (baseRing (basePoint S))))
        (Stacks.SheafOfModules.Tensor.sheafTensor (basePoint S).sheaf)
        (onePointSectionsEquivalence (baseRing S))
        (onePointTensorIso (baseRing S))
        (fun f N => onePointTensorIso_naturality_left (baseRing S) f N)
        (fun M {_ _} g => onePointTensorIso_naturality_right (baseRing S) M g)) ≪≫
    eqToIso (Functor.uncurry_whiskeringLeft_comp _ _ _) ≪≫
    Functor.isoWhiskerLeft _
      (Functor.uncurry.mapIso
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalTensorIso (basePoint S).sheaf))

/-! ### The comparison, and the one-point comparison it completes -/

/-- **The left adjoint of derived global sections is monoidal**: the isomorphism of bifunctors

`L(x ⊗^𝐋_A y) ≅ L x ⊗^𝐋_{𝒪_S} L y`

on `D(A) × D(A)` for `A = Γ(S, 𝒪_S)` and `L = derivedBaseExtension S`, on arbitrary objects
and natural in both of them, over an arbitrary ringed space. -/
def derivedSectionsTensorIso :
    Functor.uncurry.obj (tensorBase S) ⋙ derivedBaseExtension S ≅
      (derivedBaseExtension S).prod (derivedBaseExtension S) ⋙
        Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf) :=
  Functor.isoWhiskerRight
      (Functor.uncurry.mapIso
        (CochainComplex.DerivedTensor.derivedBifunctorCanonicalTensorIso (baseRing S))).symm
      (derivedBaseExtension S) ≪≫
    tensorComparisonComp
      (Functor.uncurry.obj (derivedBifunctor (curriedTensor (ModuleCat.{u} (baseRing S)))))
      (Functor.uncurry.obj (derivedTensorProductFunctor (basePoint S).sheaf))
      (Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf))
      ((baseRestrict S).mapDerivedCategory ⋙
        (onePointIdentificationFunctor (baseRing S)).mapDerivedCategory)
      (derivedPullback (toBasePoint S))
      (tensorComparisonComp _ _ _ _ _ (baseRestrictDerivedTensorIso S)
        (onePointDerivedTensorUncurriedIso S))
      (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso (toBasePoint S))

/-- **The one-point comparison of [Stacks, Section 0FKU] on an arbitrary ringed space.**  The
left adjoint and the adjunction are
`Stacks.Cohomology.DerivedSectionsLeftAdjoint.derivedBaseExtension` and
`derivedSectionsAdjunction`, and the tensor comparison is the `hom` of
`Stacks.Cohomology.DerivedSectionsLeftAdjoint.derivedSectionsTensorIso`, hence invertible. -/
def onePointComparisonOnARingedSpace : OnePointComparison S where
  pullback := derivedBaseExtension S
  adjunction := derivedSectionsAdjunction S
  tensorComparison := (derivedSectionsTensorIso S).hom

/-- **The tensor comparison of
`Stacks.Cohomology.DerivedSectionsLeftAdjoint.onePointComparisonOnARingedSpace` is invertible at
every pair**, being the `hom` of an isomorphism of bifunctors. -/
instance isIso_onePointComparisonOnARingedSpace_tensorComparison_app
    (xy : DerivedCategory (ModuleCat.{u} (baseRing S)) ×
      DerivedCategory (ModuleCat.{u} (baseRing S))) :
    IsIso ((onePointComparisonOnARingedSpace S).tensorComparison.app xy) :=
  inferInstanceAs (IsIso ((derivedSectionsTensorIso S).hom.app xy))

end Stacks.Cohomology.DerivedSectionsLeftAdjoint

end
