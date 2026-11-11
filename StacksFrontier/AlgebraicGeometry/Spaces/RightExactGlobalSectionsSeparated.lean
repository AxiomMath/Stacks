module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafIsos
public import StacksFrontier.AlgebraicGeometry.AmpleH1Vanishing.SectionsEpi
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Etale.NeighborhoodStalkFiber
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.OverField
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.ResidueField
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureSheafCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyDegreeZero
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishingBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishingClosedPoints
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.SerreAffinenessCriterion.VanishingCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishingSeparation
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraDegreeZero
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ClosedPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibresCardinality
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Specializations
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.DiagonalProper
import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisorSumEffective
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFinitePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsRightExact
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ImageSystemProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ValuativeCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionSurjectiveOnPointsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspaceDefiningIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedAffineBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SpecGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.GlobalFunctionsAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Unramified
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiMainTheoremGeneral
public import StacksFrontier.AlgebraicGeometry.Topologies.CartesianOfGlobalPresentation
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels

import all StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishingClosedPoints
import all StacksFrontier.AlgebraicGeometry.Spaces.Decent.ClosedPoints

/-!
# Right exact global sections make an algebraic space separated over `Spec Γ(X, 𝒪_X)`

Let `X` be a quasi-compact, quasi-separated algebraic space over `S` whose global sections are
right exact on quasi-coherent modules, and let `q : X ⟶ Spec A` be a morphism to an affine scheme
inducing a surjection `A ⟶ Γ(X, 𝒪_X)`. Then `q` is universally injective (Stacks 07V4) and
separated (Stacks 07V5).

## Main results

* `AlgebraicGeometry.Space.isClosed_singleton_class_of_isAlgebraic_residueFieldMap`: a
  field-valued point lying over a closed point of a scheme of the site, with algebraic residue
  field extension, is a closed point (Stacks 07U5).
* `AlgebraicGeometry.Space.isClosed_singleton_class_of_comp_eq_id`: a field-valued point which is
  a section of a morphism to the spectrum of its field is a closed point.
* `exists_subset_compl_sectionSupport_of_disjoint_of_surjective_sectionsMap`:
  two disjoint closed subsets of `|X|` are separated by a global function (Stacks 07V1).
* `AlgebraicGeometry.Space.universallyInjective_of_surjective_pullbackToGlobalFunctions`: `q` is
  universally injective.
* `AlgebraicGeometry.Space.isClosedImmersion_of_section`: every section of `q` is a closed
  immersion.
* `AlgebraicGeometry.Space.isSeparated_of_surjective_pullbackToGlobalFunctions`: `q` is
  separated.

## References

* [Stacks Project, Tag 07V6](https://stacks.math.columbia.edu/tag/07V6)
* [Stacks Project, Tag 07V4](https://stacks.math.columbia.edu/tag/07V4)
* [Stacks Project, Tag 07V5](https://stacks.math.columbia.edu/tag/07V5)
* [Stacks Project, Tag 07V1](https://stacks.math.columbia.edu/tag/07V1)
* [Stacks Project, Tag 07U5](https://stacks.math.columbia.edu/tag/07U5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Closed points above a closed point of a scheme of the site -/

/-- Let `b : Spec K ⟶ W` be a morphism from the spectrum of a field whose image is a closed point
of `W` with algebraic residue field extension, and let `j ≫ v = q ≫ b` with `q : Z ⟶ Spec K`
étale. Then the image under `j` of every point of `Z` is a closed point of `V`. -/
private theorem isClosed_singleton_image_of_etale_of_isAlgebraic_residueFieldMap
    {W : Scheme.{u}} {K : Type u} [Field K] {Z V : Scheme.{u}}
    (b : Spec (CommRingCat.of K) ⟶ W) (q : Z ⟶ Spec (CommRingCat.of K)) (j : Z ⟶ V)
    (v : V ⟶ W) (hq : Etale q) (hcomm : j ≫ v = q ≫ b) (z : Z)
    (hclosed : IsClosed ({b (IsLocalRing.closedPoint K)} : Set W))
    (halg : letI := (b.residueFieldMap (IsLocalRing.closedPoint K)).hom.toAlgebra
      Algebra.IsAlgebraic (W.residueField (b (IsLocalRing.closedPoint K)))
        ((Spec (CommRingCat.of K)).residueField (IsLocalRing.closedPoint K))) :
    IsClosed ({j z} : Set V) := by
  have := hq
  have hqz : q z = IsLocalRing.closedPoint K :=
    Subsingleton.elim (α := Spec (CommRingCat.of K)) _ _
  have hbase : v (j z) = b (IsLocalRing.closedPoint K) := by
    have hpt := congrArg (fun k : Z ⟶ W ↦ k z) hcomm
    change v (j z) = b (q z) at hpt
    rw [hpt, hqz]
  have halgZ : let := ((q ≫ b).residueFieldMap z).hom.toAlgebra
      Algebra.IsAlgebraic (W.residueField ((q ≫ b) z)) (Z.residueField z) :=
    isAlgebraic_residueField_comp_of_comp_eq (q ≫ b) q b z rfl (hqz ▸ halg) (by infer_instance)
  have halgV : let := (v.residueFieldMap (j z)).hom.toAlgebra
      Algebra.IsAlgebraic (W.residueField (v (j z))) (V.residueField (j z)) :=
    isAlgebraic_residueField_of_comp_eq (q ≫ b) j v z hcomm halgZ
  exact isClosed_of_isAlgebraic_residueField v (j z) halgV (by rw [hbase]; exact hclosed)

variable {B S hS} in
/-- A point of an étale chart of `X` lying above the image point of a field-valued point `p`, for
a morphism `π : X ⟶ h_T` to a scheme `T` of the site under which `p` lands on a closed point with
algebraic residue field extension, is a closed point of the scheme underlying the chart. -/
private theorem isClosed_singleton_pointsToScheme_of_isAlgebraic_residueFieldMap
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (T : BigFppfOver B S hS) (π : X ⟶ yoneda.obj T) (p : FieldValuedPoint B S hS X)
    (hclosed : IsClosed ({(BigFppfOver.toScheme B S hS).map
                            (yoneda.preimage (fieldMorphism B S hS X p ≫ π))
                            (IsLocalRing.closedPoint p.carrier)} :
      Set ((BigFppfOver.toScheme B S hS).obj T)))
    (halg : letI := (((BigFppfOver.toScheme B S hS).map
        (yoneda.preimage (fieldMorphism B S hS X p ≫ π))).residueFieldMap
          (IsLocalRing.closedPoint p.carrier)).hom.toAlgebra
      Algebra.IsAlgebraic (((BigFppfOver.toScheme B S hS).obj T).residueField
          ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (fieldMorphism B S hS X p ≫ π))
            (IsLocalRing.closedPoint p.carrier)))
        (((BigFppfOver.toScheme B S hS).obj p.siteObject).residueField
          (IsLocalRing.closedPoint p.carrier)))
    (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X)
    (hφ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ)
    (a : points B S hS (yoneda.obj U))
    (ha : pointsMap B S hS (yoneda.obj U) φ a = p.class B S hS X) :
    IsClosed ({pointsToScheme B S hS U a} :
      Set ((BigFppfOver.toScheme B S hS).obj U)) := by
  obtain ⟨T', m, j, hmEtale, hpb⟩ :
      ∃ (T' : BigFppfOver B S hS) (m : T' ⟶ p.siteObject) (j : T' ⟶ U),
        Etale ((BigFppfOver.toScheme B S hS).map m) ∧
        IsPullback (yoneda.map j) (yoneda.map m) φ (fieldMorphism B S hS X p) := by
    have hrep : yoneda.relativelyRepresentable φ :=
      (Functor.relativelyRepresentable.diag_iff (F := yoneda) (X := X)).1
        hX.diagonal_representable φ
    refine ⟨hrep.pullback (fieldMorphism B S hS X p), hrep.snd (fieldMorphism B S hS X p),
      hrep.fst' (fieldMorphism B S hS X p), ?_,
      hrep.isPullback' (fieldMorphism B S hS X p)⟩
    exact hφ.property (fieldMorphism B S hS X p)
      (yoneda.map (hrep.fst' (fieldMorphism B S hS X p)))
      (hrep.snd (fieldMorphism B S hS X p))
      (hrep.isPullback' (fieldMorphism B S hS X p))
  obtain ⟨t, htj, -⟩ := exists_points_of_isPullback B S hS hpb a
    ((p.tautologicalPoint B S hS X).class B S hS (yoneda.obj p.siteObject))
    (ha.trans (pointsMap_fieldMorphism_tautologicalPoint B S hS X p).symm)
  have hcomm : (BigFppfOver.toScheme B S hS).map j ≫
        (BigFppfOver.toScheme B S hS).map (yoneda.preimage (φ ≫ π)) =
      (BigFppfOver.toScheme B S hS).map m ≫
        (BigFppfOver.toScheme B S hS).map (yoneda.preimage (fieldMorphism B S hS X p ≫ π)) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    apply yoneda.map_injective
    rw [Functor.map_comp, Functor.map_comp, Functor.map_preimage, Functor.map_preimage,
      ← Category.assoc, ← Category.assoc, hpb.w]
  rw [show pointsToScheme B S hS U a =
      (BigFppfOver.toScheme B S hS).map j (pointsToScheme B S hS T' t) by
    rw [← htj]; exact pointsToScheme_pointsMap B S hS j t]
  exact isClosed_singleton_image_of_etale_of_isAlgebraic_residueFieldMap
    ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (fieldMorphism B S hS X p ≫ π)))
    ((BigFppfOver.toScheme B S hS).map m) ((BigFppfOver.toScheme B S hS).map j)
    ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (φ ≫ π))) hmEtale hcomm
    (pointsToScheme B S hS T' t) hclosed halg

variable {B S hS} in
/-- Let `X` be an algebraic space satisfying condition `(α)` of Stacks 03JX, let `π : X ⟶ h_T` be
a morphism to a scheme `T` of the site and let `p` be a field-valued point of `X`, with field `k`.
If the image point `t` of `Spec k ⟶ X ⟶ T` is a closed point of `T` and the residue field
extension `κ(t) ⟶ k` is algebraic, then the image of `Spec k ⟶ X` is a closed point of `|X|`. -/
theorem isClosed_singleton_class_of_isAlgebraic_residueFieldMap
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdecent : HasFiniteChartFibersAtEveryPoint B S hS X)
    (T : BigFppfOver B S hS) (π : X ⟶ yoneda.obj T) (p : FieldValuedPoint B S hS X)
    (hclosed : IsClosed ({(BigFppfOver.toScheme B S hS).map
                            (yoneda.preimage (fieldMorphism B S hS X p ≫ π))
                            (IsLocalRing.closedPoint p.carrier)} :
      Set ((BigFppfOver.toScheme B S hS).obj T)))
    (halg : letI := (((BigFppfOver.toScheme B S hS).map
        (yoneda.preimage (fieldMorphism B S hS X p ≫ π))).residueFieldMap
          (IsLocalRing.closedPoint p.carrier)).hom.toAlgebra
      Algebra.IsAlgebraic (((BigFppfOver.toScheme B S hS).obj T).residueField
          ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (fieldMorphism B S hS X p ≫ π))
            (IsLocalRing.closedPoint p.carrier)))
        (((BigFppfOver.toScheme B S hS).obj p.siteObject).residueField
          (IsLocalRing.closedPoint p.carrier))) :
    IsClosed ({p.class B S hS X} : Set (points B S hS X)) := by
  rw [← closure_subset_iff_isClosed]
  intro y hy
  rw [Set.mem_singleton_iff]
  rw [← specializes_iff_mem_closure] at hy
  obtain ⟨U, φ, hsurj, hφ⟩ := hX.exists_atlas
  obtain ⟨a, ha⟩ := (surjective_iff_surjective_pointsMap B S hS X hX U φ).1 hsurj y
  obtain ⟨a', ha'spec, ha'⟩ := exists_specializes_pointsMap_eq_of_isEtale B S hS hX hy
    (hdecent (p.class B S hS X)) U φ hφ a ha
  have hclosedPt : IsClosed ({a'} : Set (points B S hS (yoneda.obj U))) :=
    (isClosed_singleton_iff_isClosed_singleton_pointsToScheme B S hS U a').2
      (isClosed_singleton_pointsToScheme_of_isAlgebraic_residueFieldMap hX T π p hclosed
        halg U φ hφ a' ha')
  have haa' : a = a' := by
    simpa [hclosedPt.closure_eq] using ha'spec.mem_closure
  rw [← ha, haa', ha']

/-- The residue field extension of the identity is algebraic. -/
private theorem isAlgebraic_residueFieldMap_id (Y : Scheme.{u}) (y : Y) :
    letI := ((𝟙 Y : Y ⟶ Y).residueFieldMap y).hom.toAlgebra
    Algebra.IsAlgebraic (Y.residueField ((𝟙 Y : Y ⟶ Y) y)) (Y.residueField y) := by
  let := ((𝟙 Y : Y ⟶ Y).residueFieldMap y).hom.toAlgebra
  have hsurj := (ConcreteCategory.bijective_of_isIso
    ((𝟙 Y : Y ⟶ Y).residueFieldMap y)).2
  have := Algebra.isIntegral_of_surjective hsurj
  exact Algebra.IsIntegral.isAlgebraic

variable {B S hS} in
/-- Let `X` be an algebraic space satisfying condition `(α)` of Stacks 03JX and let `p` be a
field-valued point of `X`, with field `k`, which is a section of a morphism `π : X ⟶ Spec k`: the
composite `Spec k ⟶ X ⟶ Spec k` is the identity. Then the image of `p` is a closed point of
`|X|`. -/
theorem isClosed_singleton_class_of_comp_eq_id
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdecent : HasFiniteChartFibersAtEveryPoint B S hS X)
    (p : FieldValuedPoint B S hS X) (π : X ⟶ yoneda.obj p.siteObject)
    (hπ : fieldMorphism B S hS X p ≫ π = 𝟙 _) :
    IsClosed ({p.class B S hS X} : Set (points B S hS X)) := by
  have hid : (BigFppfOver.toScheme B S hS).map
      (yoneda.preimage (fieldMorphism B S hS X p ≫ π)) = 𝟙 _ := by
    rw [hπ, yoneda.preimage_id, CategoryTheory.Functor.map_id]
  refine isClosed_singleton_class_of_isAlgebraic_residueFieldMap hX hdecent p.siteObject π p
    ?_ ?_
  · rw [hid]
    convert isClosed_univ
    exact Set.eq_univ_of_forall fun _ =>
      Subsingleton.elim (α := Spec (CommRingCat.of p.carrier)) _ _
  · generalize (BigFppfOver.toScheme B S hS).map
      (yoneda.preimage (fieldMorphism B S hS X p ≫ π)) = b at hid ⊢
    subst hid
    exact isAlgebraic_residueFieldMap_id _ _

end AlgebraicGeometry.Space

end

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.SiteModules

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-! ### Comaximal defining ideals and the structure projection -/

section Comaximal

variable (X : AlgebraicSpaces B S hS)

attribute [local instance] pointTopology

/-- Let `X` be an algebraic space whose global sections are right exact on quasi-coherent
modules, and let `W₀, W₁` be closed subspaces whose defining ideals are comaximal on every affine
étale chart over a surjective étale chart `Uc`. Then there is `a ∈ Γ(X, 𝒪_X)` which is a section
of `𝓘_{W₀}` over every étale chart and whose difference from `1` is a section of `𝓘_{W₁}` over
every étale chart. -/
theorem exists_mem_definingIdealAt_and_sub_one_mem_of_surjective_sectionsMap
    (hX : ∀ ⦃M N : Modules.{u, u} B S hS X.1 X.2⦄ (g : M ⟶ N), Epi g →
      M.IsQuasicoherentOnSite → N.IsQuasicoherentOnSite →
        Function.Surjective (SheafOfModules.sectionsMap g))
    (W₀ W₁ : ClosedSubspaces B S hS X.1)
    (Uc : SmallEtale B S hS X.1)
    (hsurj : IsSurjective B S hS Uc.1.hom)
    (hcom : ∀ A : SmallEtale B S hS X.1,
      IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS X.1).obj A)) →
      (A ⟶ Uc) →
      definingIdealAt B S hS X W₀ (op A) ⊔ definingIdealAt B S hS X W₁ (op A) = ⊤) :
    ∃ a : globalFunctions B S hS X.1,
      (∀ V : (SmallEtale B S hS X.1)ᵒᵖ, a.val V ∈ definingIdealAt B S hS X W₀ V) ∧
      ∀ V : (SmallEtale B S hS X.1)ᵒᵖ, a.val V - 1 ∈ definingIdealAt B S hS X W₁ V := by
  obtain ⟨s, hs⟩ := hX
    ((definingIdealSheaf B S hS X W₀).ι ≫ structureProjection B S hS X W₁)
    (epi_ι_comp_structureProjection B S hS X W₀ W₁ Uc hsurj hcom)
    (isQuasicoherentOnSite_definingIdealSheaf B S hS X W₀)
    (isQuasicoherentOnSite_structureSheafPushforward B S hS (subspaceInclusion B S hS X W₁)
      W₁.2.2)
    (SheafOfModules.sectionsMap (structureProjection B S hS X W₁) (oneSections B S hS X))
  refine ⟨SheafOfModules.sectionsMap (definingIdealSheaf B S hS X W₀).ι s,
    fun V => (s.val V).2, fun V => ?_⟩
  change _ - 1 ∈ (definingIdealSheaf B S hS X W₁).obj V
  rw [← ker_structureProjection B S hS X W₁]
  refine (PresheafOfModules.Submodule.mem_ker (structureProjection B S hS X W₁).val V _).2 ?_
  have hV : PresheafOfModules.Hom.app (structureProjection B S hS X W₁).val V
        ((SheafOfModules.sectionsMap (definingIdealSheaf B S hS X W₀).ι s).val V) =
      PresheafOfModules.Hom.app (structureProjection B S hS X W₁).val V
        (1 : (structurePresheaf B S hS X.1 ⋙ forget CommRingCat).obj V) :=
    congrFun (congrArg Subtype.val hs) V
  exact ((ConcreteCategory.hom (PresheafOfModules.Hom.app
    (structureProjection B S hS X W₁).val V)).map_sub _ _).trans (by rw [hV]; exact sub_self _)

/-- Let `X` be an algebraic space whose global sections are right exact on quasi-coherent
modules. Two disjoint closed subsets `Z₀, Z₁` of the points of `X` are separated by a global
regular function: there is `a ∈ Γ(X, 𝒪_X)` with `Z₀ ⊆ V(a)` and `Z₁ ⊆ V(a - 1)`. -/
theorem exists_subset_compl_sectionSupport_of_disjoint_of_surjective_sectionsMap
    (hX : ∀ ⦃M N : Modules.{u, u} B S hS X.1 X.2⦄ (g : M ⟶ N), Epi g →
      M.IsQuasicoherentOnSite → N.IsQuasicoherentOnSite →
        Function.Surjective (SheafOfModules.sectionsMap g))
    {Z₀ Z₁ : Set (points B S hS X.1)}
    (hZ₀ : IsClosed Z₀) (hZ₁ : IsClosed Z₁) (hdisj : Disjoint Z₀ Z₁) :
    ∃ a : globalFunctions B S hS X.1,
      Z₀ ⊆ (sectionSupport B S hS X.1 a)ᶜ ∧ Z₁ ⊆ (sectionSupport B S hS X.1 (a - 1))ᶜ := by
  obtain ⟨a, ha₀, ha₁⟩ := exists_mem_definingIdealAt_and_sub_one_mem_of_surjective_sectionsMap
    B S hS X hX
    ⟨reducedClosedSubspace B S hS X.1 X.2 Z₀ hZ₀,
      isClosedSubspace_reducedClosedSubspace B S hS X.1 X.2 Z₀ hZ₀⟩
    ⟨reducedClosedSubspace B S hS X.1 X.2 Z₁ hZ₁,
      isClosedSubspace_reducedClosedSubspace B S hS X.1 X.2 Z₁ hZ₁⟩
    ⟨CostructuredArrow.mk (Classical.choose (Classical.choose_spec X.2.exists_atlas)),
      (Classical.choose_spec (Classical.choose_spec X.2.exists_atlas)).2⟩
    ((presheafSurjective_iff_isSurjective_yoneda B S hS X.1 X.2 _ _).1
        (Classical.choose_spec (Classical.choose_spec X.2.exists_atlas)).1)
    (fun A hA m => sup_definingIdealAt_reducedClosedSubspace_of_disjoint B S hS X Z₀ Z₁
      hZ₀ hZ₁ hdisj A hA m)
  refine ⟨a, ?_, ?_⟩
  · rw [← range_pointsMap_ι_reducedClosedSubspace B S hS X.1 X.2 Z₀ hZ₀]
    exact subset_compl_sectionSupport_of_forall_mem_definingIdealAt B S hS X _ a ha₀
  · rw [← range_pointsMap_ι_reducedClosedSubspace B S hS X.1 X.2 Z₁ hZ₁]
    exact subset_compl_sectionSupport_of_forall_mem_definingIdealAt B S hS X _ (a - 1) ha₁

end Comaximal

end Space

end AlgebraicGeometry

end

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (T : BigFppfOver B S hS)
    (f : X ⟶ _root_.AlgebraicGeometry.schemeSpace T)
    (s : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks in the presheaf category of the big fppf site is heavy
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
instance hasPullbacks_presheaf_rightExactGlobalSectionsSeparated :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

instance (priority := high) hasPullback_presheaf_rightExactGlobalSectionsSeparated
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

section RightExact

attribute [local instance] pointTopology

variable {B S hS} (hZ : B.Contains (⊤_ Scheme.{u})) {X : AlgebraicSpaces B S hS}
    (hX : ∀ ⦃M N : Modules.{u, u} B S hS X.1 X.2⦄ (g : M ⟶ N), Epi g →
      M.IsQuasicoherentOnSite → N.IsQuasicoherentOnSite →
        Function.Surjective (SheafOfModules.sectionsMap g))
    (hqc : IsQuasiCompactSpace B S hS X.1) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    {V : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    (p : X ⟶ _root_.AlgebraicGeometry.schemeSpace V)
    (hp : Function.Surjective (pullbackToGlobalFunctions B S hS X V p))

include hX hp in
include hX hqc hqs hp in
/-- Let `X` be a quasi-compact, quasi-separated algebraic space over `S` whose global sections are
right exact on quasi-coherent modules, and let `p : X ⟶ V` be a morphism to an affine object of
the site such that every global function on `X` is pulled back from `V`. Then `p` is universally
injective. -/
theorem universallyInjective_of_surjective_pullbackToGlobalFunctions :
    _root_.AlgebraicGeometry.Space.UniversallyInjective B S hS
      p.hom := by
  refine universallyInjective_of_fieldPoints B S hS p.hom fun pt y hpy => ?_
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (pt.siteObject B S hS X.1)) :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of pt.carrier)))
  let τ : pt.siteObject B S hS X.1 ⟶ V := p.hom.app (op _) pt.value
  let XK := AlgebraicSpaces.fiberProduct B S hS (schemeSpaceMap τ) p
  let pr' : XK ⟶ schemeSpace (pt.siteObject B S hS X.1) :=
    ObjectProperty.homMk (pullback.fst _ _)
  let pr : XK ⟶ X := ObjectProperty.homMk (pullback.snd _ _)
  have sq : IsPullback pr' pr (schemeSpaceMap τ) p :=
    AlgebraicSpaces.isPullback_fiberProduct B S hS _ _
  have hpr : IsAffineHom B S hS pr.hom :=
    IsAffineHom.of_isPullback (AlgebraicSpaces.isPullback_hom _ _ _ sq)
      (isAffineHom_yoneda_map B S hS τ)
  have hXK := surjective_sectionsMap_of_isAffineHom B S hS pr hpr hX
  have hΓ : Function.Surjective (pullbackToGlobalFunctions B S hS XK _ pr') :=
    surjective_pullbackToGlobalFunctions_of_isPullback B S hS hX hqc p hp τ sq
  have hqsK : IsAbsolutelyQuasiSeparated B S hS hZ XK.1 :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ XK.2 hqs
      (isQuasiSeparated_of_isAffineHom B S hS pr.hom XK.2 X.2 hpr)
  have hdec : HasFiniteChartFibersAtEveryPoint B S hS XK.1 :=
    hasFiniteChartFibersAtEveryPoint_of_isDecentSpace B S hS
      (isDecentSpace_of_isAbsolutelyQuasiSeparated B S hS XK.1 XK.2 hqsK)
  have hlift : ∀ x : X.1.obj (op (pt.siteObject B S hS X.1)), p.hom.app _ x = τ →
      ∃ m : yoneda.obj (pt.siteObject B S hS X.1) ⟶ XK.1,
        m ≫ pr'.hom = 𝟙 _ ∧ pr.hom.app _ (yonedaEquiv m) = x := fun x hx => by
    have hw : 𝟙 _ ≫ (schemeSpaceMap τ).hom = yonedaEquiv.symm x ≫ p.hom := by
      apply yonedaEquiv.injective
      rw [Category.id_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, hx]
      exact yonedaEquiv_yoneda_map τ
    obtain ⟨m, hm', hm⟩ : ∃ m : yoneda.obj (pt.siteObject B S hS X.1) ⟶ XK.1,
        m ≫ pr'.hom = 𝟙 _ ∧ m ≫ pr.hom = yonedaEquiv.symm x :=
      ⟨pullback.lift (𝟙 _) (yonedaEquiv.symm x) hw, pullback.lift_fst _ _ _,
        pullback.lift_snd _ _ _⟩
    exact ⟨m, hm', by rw [← yonedaEquiv_comp, hm, Equiv.apply_symm_apply]⟩
  obtain ⟨xm, hxm', hxm⟩ := hlift pt.value rfl
  obtain ⟨ym, hym', hym⟩ := hlift y hpy.symm
  let P : (yoneda.obj (pt.siteObject B S hS X.1) ⟶ XK.1) → FieldValuedPoint B S hS XK.1 :=
    fun m => ⟨pt.carrier, pt.contained, pt.toBase, yonedaEquiv m⟩
  have hc : ∀ m : yoneda.obj (pt.siteObject B S hS X.1) ⟶ XK.1, m ≫ pr'.hom = 𝟙 _ →
      IsClosed ({(P m).class B S hS XK.1} : Set (points B S hS XK.1)) := fun m hm =>
    isClosed_singleton_class_of_comp_eq_id XK.2 hdec (P m) pr'.hom (by
      change yonedaEquiv.symm (yonedaEquiv m) ≫ pr'.hom = _
      rw [Equiv.symm_apply_apply, hm]
      rfl)
  have hcl : (P xm).class B S hS XK.1 = (P ym).class B S hS XK.1 := by
    by_contra hne
    obtain ⟨a, ha₁, ha₂⟩ :=
      exists_subset_compl_sectionSupport_of_disjoint_of_surjective_sectionsMap B S hS
        XK hXK (hc xm hxm') (hc ym hym') (Set.disjoint_singleton.2 hne)
    obtain ⟨μ, rfl⟩ := hΓ a
    have h₁ := ha₁ rfl
    have h₂ := ha₂ rfl
    rw [Set.mem_compl_iff, mem_sectionSupport_pullbackToGlobalFunctions_iff] at h₁
    rw [Set.mem_compl_iff, ← map_one (pullbackToGlobalFunctions B S hS XK _ pr'), ← map_sub,
      mem_sectionSupport_pullbackToGlobalFunctions_iff] at h₂
    let t : (yoneda.obj (pt.siteObject B S hS X.1) ⟶ XK.1) →
        Spec (CommRingCat.of pt.carrier) := fun m =>
      pointsToScheme B S hS _ (pointsMap B S hS XK.1 pr'.hom ((P m).class B S hS XK.1))
    rcases Scheme.mem_basicOpen_or_mem_basicOpen_sub_one _ μ (t xm) with h | h
    · exact h₁ h
    · have hpt : t ym = t xm := Subsingleton.elim (α := Spec (CommRingCat.of pt.carrier)) _ _
      exact h₂ (by change t ym ∈ _; rwa [hpt])
  obtain ⟨r, ⟨f₁, hf₁⟩, ⟨f₂, hf₂⟩⟩ :=
    (FieldValuedPoint.class_eq_class_iff B S hS XK.1 (P xm) (P ym)).1 hcl
  have key : ∀ (m : yoneda.obj (pt.siteObject B S hS X.1) ⟶ XK.1)
      (f : r.siteObject B S hS XK.1 ⟶ pt.siteObject B S hS X.1), m ≫ pr'.hom = 𝟙 _ →
      XK.1.map f.op (yonedaEquiv m) = r.value →
      pr'.hom.app _ r.value = f ∧
        X.1.map f.op (pr.hom.app _ (yonedaEquiv m)) = pr.hom.app _ r.value := by
    intro m f hm hf
    have hpr'm : pr'.hom.app _ (yonedaEquiv m) = 𝟙 _ := by
      rw [← yonedaEquiv_comp, hm]
      rfl
    rw [← hf]
    exact ⟨(NatTrans.naturality_apply pr'.hom f.op _).trans
      ((congrArg _ hpr'm).trans (Category.comp_id f)),
      (NatTrans.naturality_apply pr.hom f.op _).symm⟩
  obtain ⟨e₁, g₁⟩ := key xm f₁ hxm' hf₁
  obtain ⟨e₂, g₂⟩ := key ym f₂ hym' hf₂
  refine ⟨⟨r.carrier, r.contained, r.toBase, pr.hom.app _ r.value⟩, f₁, ?_, ?_⟩
  · exact (congrArg _ hxm.symm).trans g₁
  · rw [e₁.symm.trans e₂]
    exact (congrArg _ hym.symm).trans g₂

end RightExact

end Space

end AlgebraicGeometry

end

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace NormalizationInData

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}

/-- Let `f : X ⟶ Y` be a quasi-finite separated morphism of algebraic spaces and let `Y'` be the
normalization of `Y` in `X`, with `f' : X ⟶ Y'` an open immersion. A global function on `Y'`
which vanishes on every étale chart of `Y'` factoring through `f'` is zero. -/
theorem eq_zero_of_forall_val_eq_zero (N : NormalizationInData B S hS f)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hqf : IsQuasiFinite B S hS f) (hsep : IsSeparated B S hS f)
    (hopen : IsOpenImmersion B S hS N.toNorm) (t : globalFunctions B S hS N.space)
    (ht : ∀ (V : SmallEtale B S hS N.space) (a : yoneda.obj V.obj.left ⟶ X),
      V.obj.hom = a ≫ N.toNorm → t.val (op V) = 0) :
    t = 0 := by
  obtain ⟨W, w, hwsurj, hwet⟩ := hY.exists_atlas
  have hrep : yoneda.relativelyRepresentable f :=
    relativelyRepresentable_of_isLocallyQuasiFinite_isSeparated B S hS f hX hY hqf.1 hsep
  have hsq : IsPullback (hrep.fst w) (yoneda.map (hrep.snd w)) f w := hrep.isPullback w
  have hgsep : _root_.AlgebraicGeometry.IsSeparated
      ((BigFppfOver.toScheme B S hS).map (hrep.snd w)) :=
    ((isSeparated_iff_presheaf B S hS f hX hY hrep).1 hsep).property w (hrep.fst w)
      (hrep.snd w) hsq
  have hgqc : QuasiCompact ((BigFppfOver.toScheme B S hS).map (hrep.snd w)) :=
    ((presheaf_quasiCompact_iff_isQuasiCompact B S hS hrep).2 hqf.2).property w (hrep.fst w)
      (hrep.snd w) hsq
  have hgqs : QuasiSeparated ((BigFppfOver.toScheme B S hS).map (hrep.snd w)) := inferInstance
  obtain ⟨W', q, b, r, e, hbq, hrb, hre, -⟩ :=
    N.chart W (hrep.pullback w) w (hrep.snd w) (hrep.fst w) hwet hsq
  have hbcE := MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) (F := yoneda)
  have hbcS := MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) (F := yoneda)
  have hbet := hbcE.of_isPullback hbq.flip hwet
  have hbsurj := hbcS.of_isPullback hbq.flip hwsurj
  have haet := hbcE.of_isPullback hsq.flip hwet
  have hcet : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (hrep.fst w ≫ N.toNorm) :=
    MorphismProperty.comp_mem _ _ _ haet (presheaf_etale_of_isOpenImmersion B S hS hopen)
  let Vb : SmallEtale B S hS N.space := ⟨CostructuredArrow.mk b, hbet⟩
  let Vc : SmallEtale B S hS N.space := ⟨CostructuredArrow.mk (hrep.fst w ≫ N.toNorm), hcet⟩
  let m : Vc ⟶ Vb := ObjectProperty.homMk (CostructuredArrow.homMk r hrb)
  have hc : t.val (op Vc) = 0 := ht Vc (hrep.fst w) rfl
  have hcomp := t.property m.op
  rw [hc] at hcomp
  have : IsSchemeTheoreticallyDominant
      ((BigFppfOver.toScheme B S hS).map (hrep.snd w)).toNormalization :=
    ⟨Scheme.Hom.ker_toNormalization _⟩
  have key : ∀ z, e.hom.appTop (e.inv.appTop z) = z := by
    intro z
    have h := congrArg (fun φ => φ.appTop) e.hom_inv_id
    simp only [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop] at h
    exact congrArg (fun φ => φ.hom z) h
  have hinj : Function.Injective ((BigFppfOver.toScheme B S hS).map r).appTop := by
    intro x y hxy
    have hn : Function.Injective
        ((BigFppfOver.toScheme B S hS).map (hrep.snd w)).toNormalization.appTop :=
      Scheme.Hom.app_injective _ ⊤
    rw [← hre, Scheme.Hom.comp_appTop] at hn
    have hxy' : e.inv.appTop x = e.inv.appTop y := hn (by
      change ((BigFppfOver.toScheme B S hS).map r).appTop (e.hom.appTop (e.inv.appTop x)) =
        ((BigFppfOver.toScheme B S hS).map r).appTop (e.hom.appTop (e.inv.appTop y))
      rw [key, key]
      exact hxy)
    rw [← key x, ← key y, hxy']
  have hb0 : t.val (op Vb) = 0 := hinj (hcomp.trans (map_zero _).symm)
  exact injective_globalFunctions_val_of_isSurjective B S hS N.space N.isAlgebraicSpace Vb
    ((presheafSurjective_iff_isSurjective_yoneda B S hS N.space N.isAlgebraicSpace _ b).1
      hbsurj) hb0

/-- The normalization of `Y` in `X`, as an object of the category of algebraic spaces. -/
abbrev toAlgebraicSpaces (N : NormalizationInData B S hS f) : AlgebraicSpaces B S hS :=
  ⟨N.space, N.isAlgebraicSpace⟩

/-- Let `q : Y ⟶ T` be a morphism from an algebraic space to an object of the site, let `s` be a
section of `q` which is quasi-finite and separated, and let `Y'` be the normalization of `Y` in
`T` along `s`, with `ν : Y' ⟶ Y` and `s' : T ⟶ Y'` an open immersion. Then every global function
on `Y'` is pulled back from `T` along `ν ≫ q`. -/
theorem surjective_pullbackToGlobalFunctions_of_section {Y : AlgebraicSpaces B S hS}
    {T : BigFppfOver B S hS} (q : Y ⟶ _root_.AlgebraicGeometry.schemeSpace T)
    (s : _root_.AlgebraicGeometry.schemeSpace T ⟶ Y) (hs : s ≫ q = 𝟙 _)
    (N : NormalizationInData B S hS s.hom) (hqf : IsQuasiFinite B S hS s.hom)
    (hsep : IsSeparated B S hS s.hom) (hopen : IsOpenImmersion B S hS N.toNorm) :
    Function.Surjective (pullbackToGlobalFunctions B S hS N.toAlgebraicSpaces T
      (ObjectProperty.homMk N.fromNorm ≫ q)) := by
  intro φ
  let E := (globalFunctionsChartEquiv B S hS N.toAlgebraicSpaces).val φ
  have hE : ∀ V : SmallEtale B S hS N.space,
      E.val (op ((SmallEtale.inclusion B S hS N.space).obj V)) = φ.val (op V) := fun V =>
    congrArg (fun x => x.val (op V)) ((globalFunctionsChartEquiv B S hS N.toAlgebraicSpaces).2 φ)
  let c : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) := E.val (op (CostructuredArrow.mk N.toNorm))
  refine ⟨c, ?_⟩
  have hsq : s.hom ≫ q.hom = 𝟙 _ := congrArg (fun k => k.hom) hs
  rw [← sub_eq_zero]
  refine N.eq_zero_of_forall_val_eq_zero (isAlgebraicSpace_yoneda B S hS T) Y.2 hqf hsep hopen _
    (fun V a ha => ?_)
  change (pullbackToGlobalFunctions B S hS N.toAlgebraicSpaces T
      (ObjectProperty.homMk N.fromNorm ≫ q) c).val (op V) - φ.val (op V) = 0
  rw [sub_eq_zero, pullbackToGlobalFunctions_apply_chart]
  have hpre : yoneda.preimage (V.obj.hom ≫
      ((ObjectProperty.homMk N.fromNorm : N.toAlgebraicSpaces ⟶ Y) ≫ q).hom) =
      yoneda.preimage a := by
    congr 1
    change V.obj.hom ≫ N.fromNorm ≫ q.hom = a
    rw [ha, Category.assoc, ← Category.assoc N.toNorm, N.fac, hsq, Category.comp_id]
  rw [hpre, ← hE V]
  let a' : yoneda.obj V.obj.left ⟶ yoneda.obj T := a
  let g : (SmallEtale.inclusion B S hS N.space).obj V ⟶ CostructuredArrow.mk N.toNorm :=
    CostructuredArrow.homMk (yoneda.preimage a') (by
      change yoneda.map (yoneda.preimage a') ≫ N.toNorm = V.obj.hom
      rw [yoneda.map_preimage, ha]
      rfl)
  exact E.property g.op

end NormalizationInData

section RightExact

variable (hZ : B.Contains (⊤_ Scheme.{u})) {Y : AlgebraicSpaces B S hS}
    (hY : ∀ ⦃M N : Modules.{u, u} B S hS Y.1 Y.2⦄ (g : M ⟶ N), Epi g →
      M.IsQuasicoherentOnSite → N.IsQuasicoherentOnSite →
        Function.Surjective (SheafOfModules.sectionsMap g))
    (hqc : IsQuasiCompactSpace B S hS Y.1) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
    {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (q : Y ⟶ _root_.AlgebraicGeometry.schemeSpace T)
    (hq : Function.Surjective (pullbackToGlobalFunctions B S hS Y T q))

include hY hqc hqs in
/-- Let `Y` be a quasi-compact, quasi-separated algebraic space whose global sections are right
exact on quasi-coherent modules, and let `q : Y ⟶ T` be a morphism to an affine object of the
site such that every global function on `Y` is pulled back along `q`. Then every section of `q`
is a closed immersion. -/
theorem isClosedImmersion_of_section (s : _root_.AlgebraicGeometry.schemeSpace T ⟶ Y)
    (hs : s ≫ q = 𝟙 _) : IsClosedImmersion B S hS s.hom := by
  have hsq : s.hom ≫ q.hom = 𝟙 _ := congrArg (fun k => k.hom) hs
  have hTalg := isAlgebraicSpace_yoneda B S hS T
  have hqqs : IsQuasiSeparated B S hS q.hom :=
    isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ Y.2 hqs q.hom
  have hqf : IsQuasiFinite B S hS s.hom :=
    ⟨isLocallyQuasiFinite_of_section B S hS q.hom Y.2 s.hom hsq,
      isQuasiCompact_of_isQuasiSeparated_of_section B S hS q.hom hqqs s.hom hsq⟩
  have hsep : IsSeparated B S hS s.hom := isSeparated_of_section B S hS q.hom s.hom hsq
  obtain ⟨-, N, hfac, hopen, -, hint⟩ := zariskiMainTheorem B S hS s.hom hTalg Y.2 hqf hsep
  let ν : N.toAlgebraicSpaces ⟶ Y := ObjectProperty.homMk N.fromNorm
  obtain ⟨hνaff, hνuc⟩ := (isIntegralHom_iff_isAffineHom_and_universallyClosed B S hS
    N.isAlgebraicSpace Y.2 N.fromNorm).1 hint
  have hY' := surjective_sectionsMap_of_isAffineHom B S hS ν hνaff hY
  have hY'qc : IsQuasiCompactSpace B S hS N.space :=
    isQuasiCompactSpace_source_of_isQuasiCompact B S hS Y.2 hqc
      (isQuasiCompact_of_universallyClosed B S hS N.isAlgebraicSpace Y.2 N.fromNorm hνuc)
  have hY'qs : IsAbsolutelyQuasiSeparated B S hS hZ N.space :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ N.isAlgebraicSpace hqs
      (isQuasiSeparated_of_isAffineHom B S hS N.fromNorm N.isAlgebraicSpace Y.2 hνaff)
  have hΓ := N.surjective_pullbackToGlobalFunctions_of_section q s hs hqf hsep hopen
  have hui := universallyInjective_of_surjective_pullbackToGlobalFunctions hZ hY' hY'qc hY'qs
    (ν ≫ q) hΓ
  have hinj := injective_pointsMap_of_universallyInjective B S hS hTalg hui
  let q' : N.space ⟶ yoneda.obj T := N.fromNorm ≫ q.hom
  let j : yoneda.obj T ⟶ N.space := N.toNorm
  have hid : j ≫ q' = 𝟙 _ := by
    change N.toNorm ≫ N.fromNorm ≫ q.hom = 𝟙 _
    rw [← Category.assoc, N.fac, hsq]
  have hsurj : Function.Surjective (pointsMap B S hS (yoneda.obj T) j) := by
    intro y
    refine ⟨pointsMap B S hS N.space q' y, hinj ?_⟩
    change pointsMap B S hS N.space q' (pointsMap B S hS (yoneda.obj T) j
      (pointsMap B S hS N.space q' y)) = pointsMap B S hS N.space q' y
    rw [← pointsMap_comp_apply, hid, pointsMap_id]
    rfl
  have hiso : IsIso N.toNorm :=
    isIso_of_isOpenImmersion_of_surjective_pointsMap B S hS N.toNorm hopen hsurj
  have hint' := (isIntegralHom_iff_representable B S hS N.fromNorm N.isAlgebraicSpace Y.2).1 hint
  have hUC : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.UniversallyClosed.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf s.hom := by
    rw [← N.fac]
    refine (((MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.UniversallyClosed.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative yoneda).cancel_left_of_respectsIso
      N.toNorm N.fromNorm).2 ?_
    exact MorphismProperty.relative_monotone (fun _ _ _ h => by
      change _root_.AlgebraicGeometry.UniversallyClosed _
      have : _root_.AlgebraicGeometry.IsIntegralHom _ := h
      infer_instance) _ hint'.2
  exact isClosedImmersion_of_mono_of_charts B S hS s.hom (mono_of_section B S hS q.hom s.hom hsq)
    (locallyOfFiniteType_presheaf_section B S hS q.hom Y.2 s.hom hsq) hUC

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for limits of presheaves on the big fppf site, used throughout the proof
include hY hqc hqs hq in
/-- Let `Y` be a quasi-compact, quasi-separated algebraic space whose global sections are right
exact on quasi-coherent modules, and let `q : Y ⟶ T` be a morphism to a reduced affine object of
the site such that every global function on `Y` is pulled back along `q`. Then any two sections
of `q` are equal. -/
theorem eq_of_section [IsReduced ((BigFppfOver.toScheme B S hS).obj T)]
    (a b : _root_.AlgebraicGeometry.schemeSpace T ⟶ Y) (ha : a ≫ q = 𝟙 _) (hb : b ≫ q = 𝟙 _) :
    a = b := by
  have hTalg := isAlgebraicSpace_yoneda B S hS T
  let a' : yoneda.obj T ⟶ Y.1 := a.hom
  let b' : yoneda.obj T ⟶ Y.1 := b.hom
  let q' : Y.1 ⟶ yoneda.obj T := q.hom
  have hsa : a' ≫ q' = 𝟙 _ := congrArg (fun k => k.hom) ha
  have hsb : b' ≫ q' = 𝟙 _ := congrArg (fun k => k.hom) hb
  have hbci : IsClosedImmersion B S hS b' := isClosedImmersion_of_section hZ hY hqc hqs q b hb
  have hrep := hbci.rep
  let E := hrep.pullback a'
  let fst := hrep.fst a'
  let snd := hrep.snd a'
  have hpb : IsPullback fst (yoneda.map snd) b' a' := hrep.isPullback a'
  have hci : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map snd) := hbci.property a' fst snd hpb
  have hqinj : Function.Injective (pointsMap B S hS Y.1 q') :=
    injective_pointsMap_of_universallyInjective B S hS hTalg
      (universallyInjective_of_surjective_pullbackToGlobalFunctions hZ hY hqc hqs q hq)
  have hEalg := isAlgebraicSpace_yoneda B S hS E
  have hsurjE : IsSurjective B S hS (yoneda.map snd) := by
    intro x
    have hab : pointsMap B S hS (yoneda.obj T) b' x = pointsMap B S hS (yoneda.obj T) a' x := by
      apply hqinj
      rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, hsa, hsb]
    obtain ⟨w, -, hw⟩ := exists_point_of_isPullback B S hS
      (isPullback_homMk B S hS hTalg hTalg Y.2 hEalg hpb) x x hab
    exact ⟨w, hw⟩
  have hsurj : _root_.AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map snd) :=
    MorphismProperty.of_relative_map (P := MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))
      ((presheafSurjective_iff_isSurjective_yoneda B S hS (yoneda.obj T) hTalg E
        (yoneda.map snd)).2 hsurjE)
  have : IsIso ((BigFppfOver.toScheme B S hS).map snd) :=
    isIso_of_isClosedImmersion_of_surjective _
  have : IsIso snd := isIso_of_reflects_iso snd (BigFppfOver.toScheme B S hS)
  have hfs : fst = yoneda.map snd := by
    simpa [hsa, hsb] using hpb.w =≫ q'
  apply ObjectProperty.hom_ext
  have hw : yoneda.map snd ≫ b' = yoneda.map snd ≫ a' := by
    rw [← hpb.w, hfs]
  have : IsIso (yoneda.map snd) := Functor.map_isIso yoneda snd
  have : Epi (yoneda.map snd) := IsIso.epi_of_iso _
  exact ((cancel_epi (yoneda.map snd)).1 hw).symm

include hY hqc hqs hq in
/-- A morphism `q : Y ⟶ T` from a quasi-compact, quasi-separated algebraic space with right exact
global sections on quasi-coherent modules to an affine object of the site, every global function
on `Y` being pulled back along `q`, has at most one lift in every valuative square. -/
theorem valuativeCriterion_uniqueness_of_surjective_pullbackToGlobalFunctions :
    ValuativeCriterion.Uniqueness q.hom := by
  intro vs
  refine ⟨fun l₁ l₂ => ?_⟩
  let R := vs.R
  let U := siteObject B S hS vs.ring_mem vs.base
  have hUaff : IsAffine ((BigFppfOver.toScheme B S hS).obj U) :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of R)))
  have hUred : IsReduced ((BigFppfOver.toScheme B S hS).obj U) :=
    inferInstanceAs (IsReduced (Spec (CommRingCat.of R)))
  let τ : U ⟶ T := yoneda.preimage vs.special
  let YU := AlgebraicSpaces.fiberProduct B S hS (_root_.AlgebraicGeometry.schemeSpaceMap τ) q
  let pr' : YU ⟶ _root_.AlgebraicGeometry.schemeSpace U := ObjectProperty.homMk (pullback.fst _ _)
  let pr : YU ⟶ Y := ObjectProperty.homMk (pullback.snd _ _)
  have sq : IsPullback pr' pr (_root_.AlgebraicGeometry.schemeSpaceMap τ) q :=
    AlgebraicSpaces.isPullback_fiberProduct B S hS _ _
  have hpr : IsAffineHom B S hS pr.hom :=
    IsAffineHom.of_isPullback (AlgebraicSpaces.isPullback_hom _ _ _ sq)
      (isAffineHom_yoneda_map B S hS τ)
  have hYU := surjective_sectionsMap_of_isAffineHom B S hS pr hpr hY
  have hΓ : Function.Surjective (pullbackToGlobalFunctions B S hS YU U pr') :=
    surjective_pullbackToGlobalFunctions_of_isPullback B S hS hY hqc q hq τ sq
  have hYUqc : IsQuasiCompactSpace B S hS YU.1 :=
    isQuasiCompactSpace_source_of_isQuasiCompact B S hS Y.2 hqc
      (isQuasiCompact_of_isAffineHom' B S hS pr.hom YU.2 Y.2 hpr)
  have hYUqs : IsAbsolutelyQuasiSeparated B S hS hZ YU.1 :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ YU.2 hqs
      (isQuasiSeparated_of_isAffineHom B S hS pr.hom YU.2 Y.2 hpr)
  have hτ : yoneda.map τ = vs.special := yoneda.map_preimage _
  let sec : vs.Lift → (_root_.AlgebraicGeometry.schemeSpace U ⟶ YU) := fun l =>
    ObjectProperty.homMk (pullback.lift (𝟙 _) l.map (by
      change 𝟙 _ ≫ yoneda.map τ = l.map ≫ q.hom
      rw [Category.id_comp, l.special_comm]
      exact hτ))
  have hsec : ∀ l, sec l ≫ pr' = 𝟙 _ := fun l =>
    ObjectProperty.hom_ext _ (pullback.lift_fst _ _ _)
  have hsnd : ∀ l, (sec l).hom ≫ pr.hom = l.map := fun l => pullback.lift_snd _ _ _
  have heq := eq_of_section hZ hYU hYUqc hYUqs pr' hΓ (sec l₁) (sec l₂) (hsec l₁) (hsec l₂)
  have hmap : l₁.map = l₂.map := by
    rw [← hsnd l₁, ← hsnd l₂, heq]
  cases l₁
  cases l₂
  cases hmap
  rfl

include hY hqc hqs hq in
/-- A morphism `q : Y ⟶ T` from a quasi-compact, quasi-separated algebraic space with right exact
global sections on quasi-coherent modules to an affine object of the site, every global function
on `Y` being pulled back along `q`, is separated. -/
theorem isSeparated_of_surjective_pullbackToGlobalFunctions : IsSeparated B S hS q.hom :=
  isSeparated_of_isQuasiSeparated_of_valuativeCriterion_uniqueness Y.2
    (isAlgebraicSpace_yoneda B S hS T) q.hom
    (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ Y.2 hqs q.hom)
    (valuativeCriterion_uniqueness_of_surjective_pullbackToGlobalFunctions hZ hY hqc hqs q hq)

end RightExact

end AlgebraicGeometry.Space

end
