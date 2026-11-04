module

public import Mathlib.Topology.Constructible
public import StacksFrontier.Algebra.Homology.DerivedCategory.Coproducts
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.SupportedDirectSums
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasiCoherentDirectSums
public import
  StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.QuasicoherentSupportedComplexes
public import StacksFrontier.AlgebraicGeometry.RingedSpace.DerivedPushforward
public import StacksFrontier.CategoryTheory.Triangulated.Elementary
public import StacksFrontier.Homology.Injectives.DerivedCategory.ProductsAndCoproducts
public import
  StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsCanonicalMaps
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cohomology with support in a closed subset commutes with direct sums

Let `X` be a scheme and let `T ⊆ X` be a closed subset whose complement `U = X ∖ T` is a
retrocompact open.  Then the derived functor `R𝓗_T : D(𝒪_X) ⥤ D(𝒪_X|_T)` of sections supported
on `T` commutes with arbitrary direct sums of objects of `D_QCoh(𝒪_X)`.

## Main results

* `preservesColimitsOfShape_discrete_of_distTriang`: a two-out-of-three principle.  If three
  functors into a pre-triangulated category are related by a distinguished triangle of natural
  transformations, and the second and third preserve `I`-indexed coproducts, then so does the
  first.
* `preservesColimitsOfShape_discrete_jStarQuasicoherent`: restriction to an open subspace
  preserves `I`-indexed direct sums of `D_QCoh`.
* `preservesColimitsOfShape_discrete_ι_comp_derivedPushforward`: the derived direct image of a
  quasi-compact quasi-separated morphism of schemes, read on the unbounded derived category of
  modules over the underlying ringed space, preserves `I`-indexed direct sums of `D_QCoh`.
* `preservesColimitsOfShape_discrete_ι_comp_derivedRestrictPush`: the third term `ℱ ↦ Rj_*(ℱ|_U)`
  of the triangle of Stacks 0G72 preserves `I`-indexed direct sums of objects of `D_QCoh(𝒪_X)`.
* `preservesColimitsOfShape_discrete_derivedSupportedPushforward`: the same for the first term
  `i_* ∘ R𝓗_T`, restricted to `D_QCoh(𝒪_X)`.
* `preservesColimitsOfShape_discrete_derivedSupportedSectionsOnClosed`: the same for `R𝓗_T`
  itself.

## References

* [Stacks Project, Lemma 36.6.3 (Tag 0G7H)](https://stacks.math.columbia.edu/tag/0G7H)
* [Stacks Project, Lemma 20.34.6 (Tag 0G72)](https://stacks.math.columbia.edu/tag/0G72)
* [Stacks Project, Lemma 36.4.5 (Tag 08DZ)](https://stacks.math.columbia.edu/tag/08DZ)
* [Stacks Project, Lemma 20.34.2 (Tag 0AEF)](https://stacks.math.columbia.edu/tag/0AEF)
* [Stacks Project, Lemma 13.34.1 (Tag 0CRG)](https://stacks.math.columbia.edu/tag/0CRG)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.Pretriangulated
open ExtensionByZeroModules
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.RestrictionCover
open Stacks.Cohomology.SectionsWithSupport (openComplement)
open Stacks.Duality.DerivedPushforward
  (preservesColimitsOfShape_discrete_qcqsQuasiCoherentDerivedPushforward)
open Stacks.Perfect.SupportedQuasicoherent (derivedQuasiCoherent_jStar_mapDerivedCategory
  derivedRestrictPush derivedRestrictPushUnit derivedSupportedPushforward
  derivedSupportedPushforwardUnit quasiCompact_ι_of_isRetrocompact)
open Stacks.SheafOfModules.SupportedSections

universe u

namespace Stacks.Cohomology.SupportedComplexes

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### A two-out-of-three principle for coproduct preservation -/

/-- **Two out of three along a distinguished triangle of functors.** Let `A`, `M`, `B` be
functors from a category `S` with `I`-indexed coproducts to a pre-triangulated category `C`
with `I`-indexed coproducts, and let `a : A ⟶ M`, `b : M ⟶ B` and `c : B ⟶ A⟦1⟧` be natural
transformations whose components form a distinguished triangle at every object.  If `M` and `B`
preserve `I`-indexed coproducts, then so does `A`. -/
theorem preservesColimitsOfShape_discrete_of_distTriang
    {S : Type*} [Category* S]
    {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]
    (A M B : S ⥤ C) (a : A ⟶ M) (b : M ⟶ B)
    (c : B ⟶ A ⋙ CategoryTheory.shiftFunctor C (1 : ℤ))
    (h : ∀ K : S, Triangle.mk (a.app K) (b.app K) (c.app K) ∈ distTriang C)
    (I : Type*) [HasColimitsOfShape (Discrete I) S] [HasColimitsOfShape (Discrete I) C]
    [PreservesColimitsOfShape (Discrete I) M]
    [PreservesColimitsOfShape (Discrete I) B] :
    PreservesColimitsOfShape (Discrete I) A := by
  have : PreservesColimitsOfShape (Discrete I) (CategoryTheory.shiftFunctor C (1 : ℤ)) :=
    (shiftFunctor_preservesProductsCoproducts_and_productCoproductTriangle_distinguished
      (C := C) I).2.1 1
  have key : ∀ K : I → S, PreservesColimit (Discrete.functor K) A := by
    intro K
    let T : I → Triangle C := fun i ↦ Triangle.mk (a.app (K i)) (b.app (K i)) (c.app (K i))
    let T' : Triangle C := Triangle.mk (a.app (∐ K)) (b.app (∐ K)) (c.app (∐ K))
    let α : (∐ fun i ↦ A.obj (K i)) ⟶ A.obj (∐ K) := Sigma.desc fun i ↦ A.map (Sigma.ι K i)
    let β : (∐ fun i ↦ M.obj (K i)) ⟶ M.obj (∐ K) := Sigma.desc fun i ↦ M.map (Sigma.ι K i)
    let γ : (∐ fun i ↦ B.obj (K i)) ⟶ B.obj (∐ K) := Sigma.desc fun i ↦ B.map (Sigma.ι K i)
    have hβ : IsIso β :=
      (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc _).mp
        ⟨isColimitOfHasCoproductOfPreservesColimit M K⟩
    have hγ : IsIso γ :=
      (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc _).mp
        ⟨isColimitOfHasCoproductOfPreservesColimit B K⟩
    let TSigma : Triangle C := Triangle.mk (Limits.Sigma.map fun i ↦ (T i).mor₁)
      (Limits.Sigma.map fun i ↦ (T i).mor₂)
      (Sigma.desc fun i ↦ (T i).mor₃ ≫ (Sigma.ι (fun i ↦ (T i).obj₁) i)⟦(1 : ℤ)⟧')
    have hTSigma : TSigma ∈ distTriang C :=
      (shiftFunctor_preservesProductsCoproducts_and_productCoproductTriangle_distinguished
        (C := C) I).2.2.2 T fun i ↦ h (K i)
    have hT' : T' ∈ distTriang C := h (∐ K)
    have h₁ : TSigma.mor₁ ≫ β = α ≫ T'.mor₁ := by
      refine Sigma.hom_ext _ _ fun i ↦ ?_
      simp [TSigma, T', T, α, β]
    have h₂ : TSigma.mor₂ ≫ γ = β ≫ T'.mor₂ := by
      refine Sigma.hom_ext _ _ fun i ↦ ?_
      simp [TSigma, T', T, β, γ]
    have h₃ : TSigma.mor₃ ≫ α⟦(1 : ℤ)⟧' = γ ≫ T'.mor₃ := by
      refine Sigma.hom_ext _ _ fun i ↦ ?_
      simp [TSigma, T', T, α, γ, Category.assoc, ← Functor.map_comp]
    have hα : IsIso α :=
      isIso₁_of_isIso₂₃ (Triangle.homMk TSigma T' α β γ h₁ h₂ h₃) hTSigma hT' hβ hγ
    have hc : IsColimit (Cofan.mk (A.obj (∐ K)) fun i ↦ A.map (Sigma.ι K i)) := by
      have : IsIso (Sigma.desc (Cofan.mk (A.obj (∐ K)) fun i ↦ A.map (Sigma.ι K i)).inj) := by
        simpa [Cofan.inj, α] using hα
      exact Cofan.isColimitOfIsIsoSigmaDesc _
    exact preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct K)
      ((isColimitMapCoconeCofanMkEquiv A K _).symm hc)
  exact preservesColimitsOfShape_of_discrete A

/-! ### Restriction to an open subspace -/

/-- **Restriction to an open subspace, read on unbounded derived categories, preserves
`I`-indexed direct sums.** -/
instance preservesColimitsOfShape_discrete_jStar_mapDerivedCategory
    (X : RingedSpace.{u, u}) (U : Opens X.carrier) (I : Type u) :
    PreservesColimitsOfShape (Discrete I) (jStar U (structureSheafRing X)).mapDerivedCategory := by
  have : (jStar U (structureSheafRing X)).IsLeftAdjoint :=
    (jStarAdjunction U (structureSheafRing X)).isLeftAdjoint
  have : PreservesColimitsOfShape (Discrete I) (jStar U (structureSheafRing X)) :=
    inferInstance
  have : PreservesColimitsOfShape (Discrete I)
      ((jStar U (structureSheafRing X)).mapHomologicalComplex (ComplexShape.up ℤ)) := inferInstance
  have : PreservesColimitsOfShape (Discrete I)
      (DerivedCategory.Q ⋙ (jStar U (structureSheafRing X)).mapDerivedCategory) :=
    preservesColimitsOfShape_of_natIso
      (jStar U (structureSheafRing X)).mapDerivedCategoryFactors.symm
  exact preservesColimitsOfShape_discrete_of_essSurj_comp DerivedCategory.Q
    (jStar U (structureSheafRing X)).mapDerivedCategory I

/-! ### Stacks 0G7H -/

/-- `D_QCoh(𝒪_X)` for a scheme `X`, as a property of objects of the unbounded derived category
of `𝒪_X`-modules taken over the underlying ringed space: the objects all of whose cohomology
sheaves are quasi-coherent.

This is `Stacks.Duality.derivedQuasiCoherent X` with the base sheaf of rings spelled
`structureSheafRing X.toRingedSpace` rather than `X.ringCatSheaf`, which is the spelling the rest
of this directory uses. -/
@[sga "6 II 3.7"]
abbrev quasicoherentDerivedProperty (X : Scheme.{u}) :
    ObjectProperty
      (DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) :=
  DerivedCategoryB.derivedCategoryB
    (A := _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (SheafOfModules.isQuasicoherent X.ringCatSheaf)

section Main

variable (X : Scheme.{u}) (I : Type u)

/-- `D_QCoh(𝒪_X)` is closed under `I`-indexed direct sums. -/
theorem quasicoherentDerivedProperty_isClosedUnderCoproducts :
    (quasicoherentDerivedProperty X).IsClosedUnderColimitsOfShape (Discrete I) :=
  Stacks.Duality.Supported.derivedQuasiCoherent_isClosedUnderCoproducts X I

/-- The inclusion of `D_QCoh(𝒪_X)` followed by restriction to an open subspace preserves
`I`-indexed direct sums. -/
theorem preservesColimitsOfShape_discrete_ι_comp_jStar_mapDerivedCategory (U : X.Opens) :
    PreservesColimitsOfShape (Discrete I)
      ((quasicoherentDerivedProperty X).ι ⋙
        (jStar U (structureSheafRing X.toRingedSpace)).mapDerivedCategory) := by
  have := quasicoherentDerivedProperty_isClosedUnderCoproducts X I
  have : PreservesColimitsOfShape (Discrete I) (quasicoherentDerivedProperty X).ι := inferInstance
  infer_instance

/-- Restriction to an open subspace of a scheme, corestricted to the quasi-coherent derived
categories: `D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_U)`. -/
def jStarQuasicoherent (U : X.Opens) :
    (quasicoherentDerivedProperty X).FullSubcategory ⥤
      (quasicoherentDerivedProperty U.toScheme).FullSubcategory :=
  (quasicoherentDerivedProperty U.toScheme).lift
    ((quasicoherentDerivedProperty X).ι ⋙
      (jStar U (structureSheafRing X.toRingedSpace)).mapDerivedCategory)
    fun E ↦ derivedQuasiCoherent_jStar_mapDerivedCategory X U E.obj E.property

/-- Corestricting and then including is including and then restricting, on the nose. -/
theorem jStarQuasicoherent_comp_ι (U : X.Opens) :
    jStarQuasicoherent X U ⋙ (quasicoherentDerivedProperty U.toScheme).ι =
      (quasicoherentDerivedProperty X).ι ⋙
        (jStar U (structureSheafRing X.toRingedSpace)).mapDerivedCategory :=
  rfl

/-- Restriction to an open subspace preserves `I`-indexed direct sums of `D_QCoh`. -/
theorem preservesColimitsOfShape_discrete_jStarQuasicoherent (U : X.Opens) :
    PreservesColimitsOfShape (Discrete I) (jStarQuasicoherent X U) := by
  have := quasicoherentDerivedProperty_isClosedUnderCoproducts U.toScheme I
  have : ReflectsColimitsOfShape (Discrete I)
      (quasicoherentDerivedProperty U.toScheme).ι := inferInstance
  have : PreservesColimitsOfShape (Discrete I)
      (jStarQuasicoherent X U ⋙ (quasicoherentDerivedProperty U.toScheme).ι) := by
    rw [jStarQuasicoherent_comp_ι]
    exact preservesColimitsOfShape_discrete_ι_comp_jStar_mapDerivedCategory X I U
  exact preservesColimitsOfShape_of_reflects_of_preserves (jStarQuasicoherent X U)
    (quasicoherentDerivedProperty U.toScheme).ι

end Main

/-! ### Stacks 08DZ for the derived direct image of a morphism of ringed spaces -/

section Pushforward

variable {V W : Scheme.{u}} (g : V ⟶ W) [QuasiCompact g] [QuasiSeparated g]

/-- The derived direct image along a quasi-compact quasi-separated morphism of schemes `g`,
corestricted to the quasi-coherent derived categories: `D_QCoh(𝒪_V) ⥤ D_QCoh(𝒪_W)`. -/
def derivedPushforwardQuasicoherent :
    (quasicoherentDerivedProperty V).FullSubcategory ⥤
      (quasicoherentDerivedProperty W).FullSubcategory :=
  (quasicoherentDerivedProperty W).lift
    ((quasicoherentDerivedProperty V).ι ⋙
      AlgebraicGeometry.RingedSpace.derivedPushforward g.toLRSHom.toShHom)
    fun E ↦ AlgebraicGeometry.isQuasicoherent_derivedPushforward g E

/-- For a quasi-compact quasi-separated morphism of schemes `g`, the unbounded derived direct image
`Rg_*` preserves `I`-indexed direct sums of objects of `D_QCoh(𝒪_V)`. -/
theorem preservesColimitsOfShape_discrete_ι_comp_derivedPushforward (I : Type u) :
    PreservesColimitsOfShape (Discrete I)
      ((quasicoherentDerivedProperty V).ι ⋙
        AlgebraicGeometry.RingedSpace.derivedPushforward g.toLRSHom.toShHom) := by
  have := quasicoherentDerivedProperty_isClosedUnderCoproducts W I
  have : PreservesColimitsOfShape (Discrete I) (derivedPushforwardQuasicoherent g) :=
    preservesColimitsOfShape_discrete_qcqsQuasiCoherentDerivedPushforward g I
  have : PreservesColimitsOfShape (Discrete I) (quasicoherentDerivedProperty W).ι := inferInstance
  exact comp_preservesColimitsOfShape (derivedPushforwardQuasicoherent g)
    (quasicoherentDerivedProperty W).ι

end Pushforward

section Triangle

variable (X : Scheme.{u}) (I : Type u)

/-- **`ℱ ↦ Rj_*(ℱ|_U)` preserves `I`-indexed direct sums of objects of `D_QCoh(𝒪_X)`**, for `U` a
retrocompact open of a scheme `X`. -/
theorem preservesColimitsOfShape_discrete_ι_comp_derivedRestrictPush (U : X.Opens)
    (hU : IsRetrocompact (U : Set X)) :
    PreservesColimitsOfShape (Discrete I)
      ((quasicoherentDerivedProperty X).ι ⋙ derivedRestrictPush X.toRingedSpace U) := by
  let : QuasiCompact U.ι := quasiCompact_ι_of_isRetrocompact X U hU
  let : QuasiSeparated U.ι := inferInstance
  have := preservesColimitsOfShape_discrete_jStarQuasicoherent X I U
  have := preservesColimitsOfShape_discrete_ι_comp_derivedPushforward U.ι I
  exact (inferInstance : PreservesColimitsOfShape (Discrete I)
    (jStarQuasicoherent X U ⋙ ((quasicoherentDerivedProperty U.toScheme).ι ⋙
      AlgebraicGeometry.RingedSpace.derivedPushforward U.ι.toLRSHom.toShHom)))

variable (T : Set X) (hT : IsClosed T)

/-- Let `T` be a closed subset of a scheme `X` whose open complement `U = X ∖ T` is retrocompact.
Then `K ↦ i_* R𝓗_T(K)`, restricted to `D_QCoh(𝒪_X)`, preserves `I`-indexed direct sums. -/
theorem preservesColimitsOfShape_discrete_derivedSupportedPushforward
    (hTc : IsRetrocompact (Tᶜ : Set X)) :
    PreservesColimitsOfShape (Discrete I)
      ((quasicoherentDerivedProperty X).ι ⋙
        derivedSupportedPushforward X.toRingedSpace T hT) := by
  have := quasicoherentDerivedProperty_isClosedUnderCoproducts X I
  have := preservesColimitsOfShape_discrete_ι_comp_derivedRestrictPush X I
    (openComplement T hT) hTc
  have : PreservesColimitsOfShape (Discrete I)
      ((quasicoherentDerivedProperty X).ι ⋙
        Functor.id (DerivedCategory
          (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))) :=
    preservesColimitsOfShape_of_natIso
      (quasicoherentDerivedProperty X).ι.rightUnitor.symm
  exact preservesColimitsOfShape_discrete_of_distTriang
    ((quasicoherentDerivedProperty X).ι ⋙ derivedSupportedPushforward X.toRingedSpace T hT)
    ((quasicoherentDerivedProperty X).ι ⋙
      Functor.id (DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))))
    ((quasicoherentDerivedProperty X).ι ⋙
      derivedRestrictPush X.toRingedSpace (openComplement T hT))
    (Functor.whiskerLeft _ (derivedSupportedSectionsToId X.toRingedSpace T
      (derivedSupportedPushforward X.toRingedSpace T hT)
      (derivedSupportedPushforwardUnit X.toRingedSpace T hT)))
    (Functor.whiskerLeft _ (idToDerivedRestrictPush X.toRingedSpace T hT
      (derivedRestrictPush X.toRingedSpace (openComplement T hT))
      (derivedRestrictPushUnit X.toRingedSpace (openComplement T hT))))
    (Functor.whiskerLeft _ (derivedSupportedSectionsTriangleδ X.toRingedSpace T hT
      (derivedSupportedPushforward X.toRingedSpace T hT)
      (derivedRestrictPush X.toRingedSpace (openComplement T hT))
      (derivedSupportedPushforwardUnit X.toRingedSpace T hT)
      (derivedRestrictPushUnit X.toRingedSpace (openComplement T hT))))
    (fun E ↦ derivedSupportedSectionsTriangle_distinguished X.toRingedSpace T hT
      (derivedSupportedPushforward X.toRingedSpace T hT)
      (derivedRestrictPush X.toRingedSpace (openComplement T hT))
      (derivedSupportedPushforwardUnit X.toRingedSpace T hT)
      (derivedRestrictPushUnit X.toRingedSpace (openComplement T hT)) E.obj) I

/-- Let `X` be a scheme and let `T ⊆ X` be a closed subset such that `X ∖ T` is a retrocompact
open of `X`.  Then for a family `Eᵢ`, `i ∈ I`, of objects of `D_QCoh(𝒪_X)` we have
`R𝓗_T(⊕ Eᵢ) = ⊕ R𝓗_T(Eᵢ)`: the derived functor `R𝓗_T` of sections supported on `T`, restricted
to `D_QCoh(𝒪_X)`, preserves `I`-indexed direct sums. -/
@[stacks 0G7H "for families indexed by a type of the scheme universe, the only index universe \
at which `D_QCoh(𝒪_X)` has direct sums"]
theorem preservesColimitsOfShape_discrete_derivedSupportedSectionsOnClosed
    (hTc : IsRetrocompact (Tᶜ : Set X)) :
    PreservesColimitsOfShape (Discrete I)
      ((quasicoherentDerivedProperty X).ι ⋙
        derivedSupportedSectionsOnClosed X.toRingedSpace T hT) := by
  have := pushforward_preservesFiniteLimits X.toRingedSpace T
  have := pushforward_preservesFiniteColimits X.toRingedSpace T hT
  have : PreservesColimitsOfShape (Discrete I)
      ((quasicoherentDerivedProperty X).ι ⋙
        (derivedSupportedSectionsOnClosed X.toRingedSpace T hT ⋙
          (modulePushforward
            (closedSubsetInclusion X.toRingedSpace T)).mapDerivedCategory)) :=
    preservesColimitsOfShape_discrete_derivedSupportedPushforward X I T hT hTc
  have : PreservesColimitsOfShape (Discrete I)
      (((quasicoherentDerivedProperty X).ι ⋙
          derivedSupportedSectionsOnClosed X.toRingedSpace T hT) ⋙
        (modulePushforward (closedSubsetInclusion X.toRingedSpace T)).mapDerivedCategory) :=
    preservesColimitsOfShape_of_natIso
      (Functor.associator (quasicoherentDerivedProperty X).ι
        (derivedSupportedSectionsOnClosed X.toRingedSpace T hT)
        (modulePushforward (closedSubsetInclusion X.toRingedSpace T)).mapDerivedCategory).symm
  have : ((modulePushforward
      (closedSubsetInclusion X.toRingedSpace T)).mapDerivedCategory).ReflectsIsomorphisms :=
    (derivedPushforwardAdjunction X.toRingedSpace T
      hT).fullyFaithfulLOfIsIsoUnit.reflectsIsomorphisms
  have : PreservesColimitsOfShape (Discrete I)
      ((modulePushforward (closedSubsetInclusion X.toRingedSpace T)).mapDerivedCategory) :=
    (derivedPushforwardAdjunction X.toRingedSpace T
      hT).leftAdjoint_preservesColimits.preservesColimitsOfShape
  have : ReflectsColimitsOfShape (Discrete I)
      ((modulePushforward (closedSubsetInclusion X.toRingedSpace T)).mapDerivedCategory) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  exact preservesColimitsOfShape_of_reflects_of_preserves _
    ((modulePushforward (closedSubsetInclusion X.toRingedSpace T)).mapDerivedCategory)

end Triangle

end Stacks.Cohomology.SupportedComplexes

end
