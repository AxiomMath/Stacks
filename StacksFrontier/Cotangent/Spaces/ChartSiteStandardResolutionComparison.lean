module

public import StacksFrontier.Cotangent.ChartSiteStandardResolutionComparison
public import StacksFrontier.Cotangent.SheavesOfRings.PolynomialChartSpaceStandardResolution
public import StacksFrontier.Cotangent.Spaces.ChartSiteDifferentialsPresheaf
public import StacksFrontier.Cotangent.Spaces.ConstantBaseRing
public import StacksFrontier.Cotangent.Spaces.SpaceOverRingSectionwise
public import StacksFrontier.Cotangent.StandardResolutionULift

/-!
# The sections of `Ω_{𝒪/Λ̲} ⊗_𝒪 π⁻¹𝒪_X` on the charts of the standard resolutions, for spaces

Let `Λ` be a ring and `X` an algebraic space over `Λ`. For an object `U` of the small étale site
`X_étale` let `P_{•,U}` be the standard resolution of `𝒪_X(U)` over `Λ` and
`𝐀_{n,U} = Spec(P_{n,U})` the corresponding polynomial charts of Tag 08VL. The proof of Tag 08VM
computes the value of the presheaf `(U ⟶ A) ↦ 𝒪_X(U) ⊗_{Γ(A)} Ω_{Γ(A)/Λ}` of the chart site, whose
sheafification is `Ω_{𝒪/Λ̲} ⊗_𝒪 π⁻¹𝒪_X`, on these charts: it is `𝒪_X(U) ⊗_{P_{n,U}} Ω_{P_{n,U}/Λ}`,
the degree `-n` term of the cotangent complex `L_{𝒪_X(U)/Λ}`. This file proves that identification
at a single chart; its compatibility with the simplicial structure and with restriction along
arrows of `X_étale` is `StacksFrontier/Cotangent/Spaces/ChartSiteStandardResolutionNaturality.lean`,
and the resulting isomorphism of complexes of presheaves is
`StacksFrontier/Cotangent/Spaces/ChartSiteStandardResolutionEvaluation.lean`.

## Main definitions

* `AlgebraicGeometry.Space.PolynomialChart.liftedSectionsAlgebra`: `ULift 𝒪_X(U)` as an algebra
  over `ULift Λ` through the structure morphism `U ⟶ Spec Λ`.
* `AlgebraicGeometry.Space.PolynomialChart.chartBaseHom`: the structure maps `U ↦ (Λ → 𝒪_X(U))`,
  lifted, as a homomorphism of sheaves on the chaotic site.
* `AlgebraicGeometry.Space.PolynomialChart.chartResolutionIso`: `ULift Γ(𝐀_{n,U}) ≅ P'_n` for
  `P'_•` the standard resolution of `ULift 𝒪_X(U)` over `ULift Λ`.
* `AlgebraicGeometry.Space.PolynomialChart.chartToCotangent` and
  `AlgebraicGeometry.Space.PolynomialChart.cotangentToChart`: the two maps
  `𝒪_X(U) ⊗_{Γ(𝐀_{n,U})} Ω_{Γ(𝐀_{n,U})/Λ} ⇄ L^{-n}_{𝒪_X(U)/Λ}`, `b ⊗ d p ↦ b ⊗ d p`.

## Main results

* `AlgebraicGeometry.Space.PolynomialChart.chartResolutionIso_hom_augmentation`,
  `chartResolutionIso_hom_basePresheafMap`, `chartResolutionIso_hom_naturality` and
  `chartResolutionIso_hom_restriction`: the identification of the charts' rings lies over
  `ULift 𝒪_X(U)` and under `ULift Λ`, and is natural in both variables.
* `AlgebraicGeometry.Space.PolynomialChart.chartToCotangent_cotangentToChart` and
  `AlgebraicGeometry.Space.PolynomialChart.cotangentToChart_chartToCotangent`: the two maps are
  inverse to each other.

## Implementation notes

The sheaves of the chart site and the cotangent complex of Tag 08VD are formed for sections in
the universe `u + 1` of the site, so the comparison is with the cotangent complex of
`ULift Λ → ULift 𝒪_X(U)`. The charts are spectra of the standard resolution of `𝒪_X(U)` over `Λ`
in the universe `u`; the lift of that resolution is the standard resolution of the lifted algebra
by `CommAlgCat.standardResolutionULiftTermIso`.

## References

* [Stacks Project, Tag 08VM](https://stacks.math.columbia.edu/tag/08VM)
* [Stacks Project, Tag 08VL](https://stacks.math.columbia.edu/tag/08VL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped ChangeOfRings TensorProduct
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace AlgebraicGeometry.Space.PolynomialChart

variable (Λ : Type u) [CommRing Λ] (B : BigFppfSite.{u})
  (hS : B.Contains (Spec (CommRingCat.of Λ)))
  (X : (BigFppfOver B (Spec (CommRingCat.of Λ)) hS)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B (Spec (CommRingCat.of Λ)) hS X)

/-- The chart `𝐀_{n,U} = Spec(P_{n,U})` of the standard resolution of `𝒪_X(U)` over `Λ`. -/
abbrev resolutionChart (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X) (n : SimplexCategory) :
    PolynomialChart Λ B hS X hX :=
  ((standardResolutionChart Λ B hS X hX).obj U).obj n

/-- The lifted ring of functions `ULift Γ(𝐀_{n,U})` of the chart `𝐀_{n,U}`. -/
abbrev resolutionChartRing (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X)
    (n : SimplexCategory) : CommRingCat.{u + 1} :=
  (liftedAffinePresheaf Λ B hS X hX).obj (op (resolutionChart Λ B hS X hX U n))

/-- The sections `ULift 𝒪_X(U)` as an algebra over `ULift Λ`, through the structure morphism
`U ⟶ Spec Λ`: the algebra whose cotangent complex is the term over `U` of `U ↦ L_{𝒪_X(U)/Λ}`. -/
abbrev liftedSectionsAlgebra (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X) :
    CommAlgCat.{u + 1} (ULift.{u + 1} Λ) :=
  (CommAlgCat.uliftBaseFunctor Λ).obj (sectionsAlgebra Λ B hS X U)

/-- The degree `n` term `P'_n` of the standard resolution of `ULift 𝒪_X(U)` over `ULift Λ`. -/
abbrev resolutionTermAlgebra (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X)
    (n : SimplexCategory) : CommAlgCat.{u + 1} (ULift.{u + 1} Λ) :=
  (CommAlgCat.standardResolution.{u + 1, u + 1} (ULift.{u + 1} Λ)
    (liftedSectionsAlgebra Λ B hS X U)).left.obj (op n)

/-- The lifted module of differentials `Ω_{ULift Γ(𝐀_{n,U})/ULift Λ}` of the chart `𝐀_{n,U}`. -/
abbrev resolutionChartDifferentials (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X)
    (n : SimplexCategory) : ModuleCat.{u + 1} (resolutionChartRing Λ B hS X hX U n) :=
  CommRingCat.KaehlerDifferential
    ((liftedBasePresheafMap Λ B hS X hX).app (op (resolutionChart Λ B hS X hX U n)))

/-- **The lifted ring of functions of the chart `𝐀_{n,U}` is `P'_n`**: `Γ(Spec P_n) = P_n` for the
standard resolution `P_•` of `𝒪_X(U)` over `Λ`, and the universe lift of `P_n` is the degree `n`
term of the standard resolution of `ULift 𝒪_X(U)` over `ULift Λ`. -/
def chartResolutionIso (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X) (n : SimplexCategory) :
    resolutionChartRing Λ B hS X hX U n ≅
      (forget₂ (CommAlgCat.{u + 1} (ULift.{u + 1} Λ)) CommRingCat.{u + 1}).obj
        (resolutionTermAlgebra Λ B hS X U n) :=
  liftRing.mapIso (Scheme.ΓSpecIso _) ≪≫
    (forget₂ (CommAlgCat.{u + 1} (ULift.{u + 1} Λ)) CommRingCat.{u + 1}).mapIso
      (CommAlgCat.standardResolutionULiftTermIso Λ (sectionsAlgebra Λ B hS X U) n.len)

/-- The structure map `U ↦ (Λ → 𝒪_X(U))` of the charts, from the constant presheaf `U ↦ Λ`, with
all sections lifted into the universe of the site, read as a homomorphism of sheaves on the
chaotic site: the sectionwise constructions of Tag 08SX at it are `U ↦ L_{𝒪_X(U)/Λ}`. -/
abbrev chartBaseHom :
    CategoryTheory.Sheaf.presheafBaseSheaf.{u + 1, u, u}
        (etaleConstantBasePresheaf Λ B hS ⟨X, hX⟩) ⟶
      CategoryTheory.Sheaf.presheafBaseSheaf.{u + 1, u, u}
        (smallEtaleStructureSheafULift B (Spec (CommRingCat.of Λ)) hS ⟨X, hX⟩).obj :=
  ⟨Functor.whiskerRight (etaleConstantStructurePresheafMap Λ B hS X)
    AlgebraicGeometry.SheafOfModules.commRingCatULift.{u, u + 1}⟩

variable {Λ B hS X} in
/-- The sectionwise algebra of Tag 08SX at `chartBaseHom` over `U` is `ULift 𝒪_X(U)` over `ULift Λ`
through the structure morphism of `U`. -/
theorem sectionsAlgebra_chartBaseHom (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X) :
    CategoryTheory.Sheaf.sectionsAlgebra.{u + 1, u, u} ⊥ (chartBaseHom Λ B hS X hX) (op U) =
      liftedSectionsAlgebra Λ B hS X U :=
  rfl

/-- The comparison of `chartResolutionIso` lies over `ULift 𝒪_X(U)`: followed by the augmentation
of the standard resolution it is pullback of functions along the chart `U ⟶ 𝐀_{n,U}`. -/
theorem chartResolutionIso_hom_augmentation (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X)
    (n : SimplexCategory) :
    (chartResolutionIso Λ B hS X hX U n).hom ≫
        (forget₂ (CommAlgCat.{u + 1} (ULift.{u + 1} Λ)) CommRingCat.{u + 1}).map
          ((CommAlgCat.standardResolution.{u + 1, u + 1} (ULift.{u + 1} Λ)
            (liftedSectionsAlgebra Λ B hS X U)).hom.app (op n)) =
      (liftedEvaluation Λ B hS X hX).app (op (resolutionChart Λ B hS X hX U n)) := by
  have h1 := congrArg (forget₂ (CommAlgCat.{u + 1} (ULift.{u + 1} Λ)) CommRingCat.{u + 1}).map
    (CommAlgCat.standardResolutionULiftIso_hom_app_comp_augmentation Λ
      (sectionsAlgebra Λ B hS X U) n.len)
  rw [Functor.map_comp] at h1
  have h2 : (Scheme.ΓSpecIso _).hom ≫ (forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).map
      ((CommAlgCat.standardResolution.{u, u} Λ (sectionsAlgebra Λ B hS X U)).hom.app (op n)) =
      Scheme.Γ.map (resolutionChart Λ B hS X hX U n).toAffine.op := by
    have h := appTop_toSpecΓ_specMap
      ((forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).map
        ((CommAlgCat.standardResolution.{u, u} Λ (sectionsAlgebra Λ B hS X U)).hom.app (op n)))
    rw [← h]
    exact Iso.hom_inv_id_assoc _ _
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) h1).trans ?_
  refine (liftRing.map_comp _ _).symm.trans ?_
  exact congrArg liftRing.map h2

/-- `chartResolutionIso` sends the image of `ULift Λ` to the image of `ULift Λ`. -/
theorem chartResolutionIso_hom_basePresheafMap (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X)
    (n : SimplexCategory) (r : ULift.{u + 1} Λ) :
    (chartResolutionIso Λ B hS X hX U n).hom
        ((liftedBasePresheafMap Λ B hS X hX).app (op (resolutionChart Λ B hS X hX U n)) r) =
      algebraMap (ULift.{u + 1} Λ) (resolutionTermAlgebra Λ B hS X U n) r := by
  have h : (Scheme.ΓSpecIso (CommRingCat.of Λ)).inv ≫
      Scheme.Γ.map (resolutionChart Λ B hS X hX U n).toBase.op ≫ (Scheme.ΓSpecIso _).hom =
      CommRingCat.ofHom (algebraMap Λ ((CommAlgCat.standardResolution.{u, u} Λ
        (sectionsAlgebra Λ B hS X U)).left.obj (op n))) := by
    rw [show (resolutionChart Λ B hS X hX U n).toBase = Spec.map (CommRingCat.ofHom
        (algebraMap Λ ((CommAlgCat.standardResolution.{u, u} Λ
          (sectionsAlgebra Λ B hS X U)).left.obj (op n)))) from specChart_toBase Λ B hS X hX U _]
    exact (congrArg ((Scheme.ΓSpecIso (CommRingCat.of Λ)).inv ≫ ·)
      (Scheme.ΓSpecIso_naturality _)).trans (Iso.inv_hom_id_assoc _ _)
  have h' := commRingCat_apply_congr h r.down
  change (CommAlgCat.standardResolutionULiftTermIso Λ (sectionsAlgebra Λ B hS X U) n.len).hom
      (ULift.up ((Scheme.ΓSpecIso _).hom ((Scheme.Γ.map (resolutionChart Λ B hS X hX U n).toBase.op)
        ((Scheme.ΓSpecIso (CommRingCat.of Λ)).inv r.down)))) = _
  rw [show (Scheme.ΓSpecIso _).hom ((Scheme.Γ.map (resolutionChart Λ B hS X hX U n).toBase.op)
      ((Scheme.ΓSpecIso (CommRingCat.of Λ)).inv r.down)) = _ from h']
  exact (CommAlgCat.standardResolutionULiftTermIso Λ (sectionsAlgebra Λ B hS X U)
    n.len).hom.hom.commutes r

/-- The comparison of `chartResolutionIso` is compatible with the simplicial structure: the
cosimplicial structure maps of `𝐀_{•,U}` correspond to the simplicial structure maps of `P'_•`. -/
theorem chartResolutionIso_hom_naturality (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X)
    {m n : SimplexCategory} (θ : m ⟶ n) :
    (liftedAffinePresheaf Λ B hS X hX).map (((standardResolutionChart Λ B hS X hX).obj U).map θ).op
      ≫
        (chartResolutionIso Λ B hS X hX U m).hom =
      (chartResolutionIso Λ B hS X hX U n).hom ≫
        (forget₂ (CommAlgCat.{u + 1} (ULift.{u + 1} Λ)) CommRingCat.{u + 1}).map
          ((CommAlgCat.standardResolution.{u + 1, u + 1} (ULift.{u + 1} Λ)
            (liftedSectionsAlgebra Λ B hS X U)).left.map θ.op) := by
  have h1 : Scheme.Γ.map (((standardResolutionChart Λ B hS X hX).obj U).map θ).affine.op ≫
      (Scheme.ΓSpecIso _).hom = (Scheme.ΓSpecIso _).hom ≫
        (forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).map
          ((CommAlgCat.standardResolution.{u, u} Λ (sectionsAlgebra Λ B hS X U)).left.map θ.op) :=
    Scheme.ΓSpecIso_naturality _
  have h2 := congrArg (forget₂ (CommAlgCat.{u + 1} (ULift.{u + 1} Λ)) CommRingCat.{u + 1}).map
    ((CommAlgCat.standardResolutionULiftIso Λ (sectionsAlgebra Λ B hS X U)).hom.naturality θ.op)
  rw [Functor.map_comp, Functor.map_comp] at h2
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) ((liftRing.map_comp _ _).symm.trans
    ((congrArg liftRing.map h1).trans (liftRing.map_comp _ _)))).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact (congrArg (_ ≫ ·) h2).trans (Category.assoc _ _ _).symm

/-- The comparison of `chartResolutionIso` is natural in the object of the small étale site: the
maps of charts `𝐀_{n,V} ⟶ 𝐀_{n,U}` over `V ⟶ U` correspond to the maps of standard resolutions
induced by the restriction `ULift 𝒪_X(U) ⟶ ULift 𝒪_X(V)`. -/
theorem chartResolutionIso_hom_restriction {U V : SmallEtale B (Spec (CommRingCat.of Λ)) hS X}
    (h : V ⟶ U) (n : SimplexCategory) :
    (liftedAffinePresheaf Λ B hS X hX).map (((standardResolutionChart Λ B hS X hX).map h).app n).op
      ≫
        (chartResolutionIso Λ B hS X hX V n).hom =
      (chartResolutionIso Λ B hS X hX U n).hom ≫
        (forget₂ (CommAlgCat.{u + 1} (ULift.{u + 1} Λ)) CommRingCat.{u + 1}).map
          (((CommAlgCat.standardResolutionFunctor.{u + 1, u + 1} (ULift.{u + 1} Λ)).map
            ((CommAlgCat.uliftBaseFunctor Λ).map
              (sectionsAlgebraRestrict Λ B hS X h))).left.app (op n)) := by
  have h1 : Scheme.Γ.map (((standardResolutionChart Λ B hS X hX).map h).app n).affine.op ≫
      (Scheme.ΓSpecIso _).hom = (Scheme.ΓSpecIso _).hom ≫
        (forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).map
          (((CommAlgCat.standardResolutionFunctor.{u, u} Λ).map
            (sectionsAlgebraRestrict Λ B hS X h)).left.app (op n)) :=
    Scheme.ΓSpecIso_naturality _
  have h2 := congrArg (forget₂ (CommAlgCat.{u + 1} (ULift.{u + 1} Λ)) CommRingCat.{u + 1}).map
    (CommAlgCat.standardResolutionULiftTermIso_naturality Λ
      (sectionsAlgebraRestrict Λ B hS X h) n.len)
  rw [Functor.map_comp, Functor.map_comp] at h2
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) ((liftRing.map_comp _ _).symm.trans
    ((congrArg liftRing.map h1).trans (liftRing.map_comp _ _)))).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact (congrArg (_ ≫ ·) h2).trans (Category.assoc _ _ _).symm

/-! ### The comparison of `𝒪_X(U) ⊗_{Γ(𝐀_{n,U})} Ω_{Γ(𝐀_{n,U})/Λ}` with `L^{-n}_{𝒪_X(U)/Λ}` -/

/-- The ring map `ULift Γ(𝐀_{n,U}) → ULift 𝒪_X(U)` through which the cotangent term
`L^{-n}_{𝒪_X(U)/Λ}` is a module over the lifted functions of the chart: `chartResolutionIso`
followed by the augmentation. -/
def chartAugmentationHom (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X) (n : SimplexCategory) :
    resolutionChartRing Λ B hS X hX U n →+* liftedSectionsAlgebra Λ B hS X U :=
  (CommAlgCat.standardResolutionAugmentationHom.{u + 1, u + 1} (ULift.{u + 1} Λ)
      (liftedSectionsAlgebra Λ B hS X U) (op n)).comp
    (chartResolutionIso Λ B hS X hX U n).hom.hom

/-- Evaluation along the chart `U ⟶ 𝐀_{n,U}` is `chartAugmentationHom`. -/
theorem evaluation_app_apply (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X)
    (n : SimplexCategory) (p : resolutionChartRing Λ B hS X hX U n) :
    (liftedEvaluation Λ B hS X hX).app (op (resolutionChart Λ B hS X hX U n)) p =
      chartAugmentationHom Λ B hS X hX U n p :=
  (commRingCat_apply_congr (chartResolutionIso_hom_augmentation Λ B hS X hX U n) p).symm

/-- The inverse of `chartResolutionIso`, as a ring map from `P'_n` to the lifted functions of the
chart `𝐀_{n,U}`. -/
abbrev resolutionToChartHom (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X)
    (n : SimplexCategory) :
    resolutionTermAlgebra Λ B hS X U n →+* resolutionChartRing Λ B hS X hX U n :=
  (chartResolutionIso Λ B hS X hX U n).inv.hom

/-- `chartResolutionIso` carries the image of `ULift Λ` back to the image of `ULift Λ`. -/
theorem chartResolutionIso_inv_algebraMap (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X)
    (n : SimplexCategory) (r : ULift.{u + 1} Λ) :
    (chartResolutionIso Λ B hS X hX U n).inv
        (algebraMap (ULift.{u + 1} Λ) (resolutionTermAlgebra Λ B hS X U n) r) =
      (liftedBasePresheafMap Λ B hS X hX).app (op (resolutionChart Λ B hS X hX U n)) r := by
  rw [← chartResolutionIso_hom_basePresheafMap]
  exact Iso.hom_inv_id_apply _ _

/-- The derivation `p ↦ 1 ⊗ d(p)` of the lifted functions of the chart `𝐀_{n,U}` over `ULift Λ`
with values in `L^{-n}_{𝒪_X(U)/Λ} = 𝒪_X(U) ⊗_{P'_n} Ω_{P'_n/Λ}`. -/
def chartCotangentDerivation (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X)
    (n : SimplexCategory) :
    ((ModuleCat.restrictScalars (chartAugmentationHom Λ B hS X hX U n)).obj
        (CommAlgCat.cotangentTerm.{u + 1, u + 1} (ULift.{u + 1} Λ)
          (liftedSectionsAlgebra Λ B hS X U) (op n))).Derivation
      ((liftedBasePresheafMap Λ B hS X hX).app (op (resolutionChart Λ B hS X hX U n))) :=
  ModuleCat.Derivation.mk
    (fun p => CommAlgCat.cotangentTermDifferential.{u + 1, u + 1} (ULift.{u + 1} Λ)
      (liftedSectionsAlgebra Λ B hS X U) (op n) ((chartResolutionIso Λ B hS X hX U n).hom p))
    (fun p p' => by
      change CommAlgCat.cotangentTermDifferential.{u + 1, u + 1} (ULift.{u + 1} Λ) _ (op n)
        ((chartResolutionIso Λ B hS X hX U n).hom (p + p')) = _
      rw [map_add, CommAlgCat.cotangentTermDifferential_add]
      rfl)
    (fun p p' => by
      change CommAlgCat.cotangentTermDifferential.{u + 1, u + 1} (ULift.{u + 1} Λ) _ (op n)
        ((chartResolutionIso Λ B hS X hX U n).hom (p * p')) = _
      rw [map_mul, CommAlgCat.cotangentTermDifferential_mul]
      rfl)
    (fun r => by
      change CommAlgCat.cotangentTermDifferential.{u + 1, u + 1} (ULift.{u + 1} Λ) _ (op n)
        ((chartResolutionIso Λ B hS X hX U n).hom
          ((liftedBasePresheafMap Λ B hS X hX).app _ r)) = 0
      exact (congrArg _ (chartResolutionIso_hom_basePresheafMap Λ B hS X hX U n r)).trans
        (CommAlgCat.cotangentTermDifferential_algebraMap.{u + 1, u + 1} (ULift.{u + 1} Λ)
          (liftedSectionsAlgebra Λ B hS X U) (op n) r))

/-- The map of Kähler differentials `Ω_{P'_n/ULift Λ} → Ω_{ULift Γ(𝐀_{n,U})/ULift Λ}` induced by
the inverse of `chartResolutionIso`. -/
def resolutionToChartDifferentials (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X)
    (n : SimplexCategory) :
    Ω[resolutionTermAlgebra Λ B hS X U n⁄ULift.{u + 1} Λ] →+
      resolutionChartDifferentials Λ B hS X hX U n := by
  letI : Algebra (((Functor.const _).obj (liftRing.obj (CommRingCat.of Λ))).obj
      (op (resolutionChart Λ B hS X hX U n))) (resolutionChartRing Λ B hS X hX U n) :=
    ((liftedBasePresheafMap Λ B hS X hX).app (op (resolutionChart Λ B hS X hX U n))).hom.toAlgebra
  letI : Algebra (ULift.{u + 1} Λ) (((Functor.const _).obj (liftRing.obj
      (CommRingCat.of Λ))).obj (op (resolutionChart Λ B hS X hX U n))) :=
    (RingHom.id (ULift.{u + 1} Λ)).toAlgebra
  letI : Algebra (resolutionTermAlgebra Λ B hS X U n) (resolutionChartRing Λ B hS X hX U n) :=
    (resolutionToChartHom Λ B hS X hX U n).toAlgebra
  letI : Algebra (ULift.{u + 1} Λ) (resolutionChartRing Λ B hS X hX U n) :=
    ((algebraMap (resolutionTermAlgebra Λ B hS X U n) (resolutionChartRing Λ B hS X hX U n)).comp
      (algebraMap (ULift.{u + 1} Λ) _)).toAlgebra
  haveI : IsScalarTower (ULift.{u + 1} Λ) (resolutionTermAlgebra Λ B hS X U n)
      (resolutionChartRing Λ B hS X hX U n) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (ULift.{u + 1} Λ) (((Functor.const _).obj (liftRing.obj
      (CommRingCat.of Λ))).obj (op (resolutionChart Λ B hS X hX U n)))
      (resolutionChartRing Λ B hS X hX U n) :=
    IsScalarTower.of_algebraMap_eq fun r =>
      chartResolutionIso_inv_algebraMap Λ B hS X hX U n r
  haveI : SMulCommClass (((Functor.const _).obj (liftRing.obj
      (CommRingCat.of Λ))).obj (op (resolutionChart Λ B hS X hX U n)))
      (resolutionTermAlgebra Λ B hS X U n) (resolutionChartRing Λ B hS X hX U n) :=
    ⟨fun a b c => by simp only [Algebra.smul_def, mul_left_comm]⟩
  exact (KaehlerDifferential.map (ULift.{u + 1} Λ) _ (resolutionTermAlgebra Λ B hS X U n)
    (resolutionChartRing Λ B hS X hX U n)).toAddMonoidHom

/-- `resolutionToChartDifferentials` is compatible with `d` and semilinear along the inverse of
`chartResolutionIso`. -/
private theorem resolutionToChartDifferentials_D_and_smul
    (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X) (n : SimplexCategory) :
    (∀ q : resolutionTermAlgebra Λ B hS X U n,
      resolutionToChartDifferentials Λ B hS X hX U n
          (KaehlerDifferential.D (ULift.{u + 1} Λ) (resolutionTermAlgebra Λ B hS X U n) q) =
        CommRingCat.KaehlerDifferential.d (resolutionToChartHom Λ B hS X hX U n q)) ∧
    ∀ (q : resolutionTermAlgebra Λ B hS X U n)
      (ω : Ω[resolutionTermAlgebra Λ B hS X U n⁄ULift.{u + 1} Λ]),
      resolutionToChartDifferentials Λ B hS X hX U n (q • ω) =
        resolutionToChartHom Λ B hS X hX U n q •
          resolutionToChartDifferentials Λ B hS X hX U n ω := by
  let : Algebra (((Functor.const _).obj (liftRing.obj (CommRingCat.of Λ))).obj
      (op (resolutionChart Λ B hS X hX U n))) (resolutionChartRing Λ B hS X hX U n) :=
    ((liftedBasePresheafMap Λ B hS X hX).app (op (resolutionChart Λ B hS X hX U n))).hom.toAlgebra
  let : Algebra (ULift.{u + 1} Λ) (((Functor.const _).obj (liftRing.obj
      (CommRingCat.of Λ))).obj (op (resolutionChart Λ B hS X hX U n))) :=
    (RingHom.id (ULift.{u + 1} Λ)).toAlgebra
  let : Algebra (resolutionTermAlgebra Λ B hS X U n) (resolutionChartRing Λ B hS X hX U n) :=
    (resolutionToChartHom Λ B hS X hX U n).toAlgebra
  let : Algebra (ULift.{u + 1} Λ) (resolutionChartRing Λ B hS X hX U n) :=
    ((algebraMap (resolutionTermAlgebra Λ B hS X U n) (resolutionChartRing Λ B hS X hX U n)).comp
      (algebraMap (ULift.{u + 1} Λ) _)).toAlgebra
  have : IsScalarTower (ULift.{u + 1} Λ) (resolutionTermAlgebra Λ B hS X U n)
      (resolutionChartRing Λ B hS X hX U n) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower (ULift.{u + 1} Λ) (((Functor.const _).obj (liftRing.obj
      (CommRingCat.of Λ))).obj (op (resolutionChart Λ B hS X hX U n)))
      (resolutionChartRing Λ B hS X hX U n) :=
    IsScalarTower.of_algebraMap_eq fun r =>
      chartResolutionIso_inv_algebraMap Λ B hS X hX U n r
  have : SMulCommClass (((Functor.const _).obj (liftRing.obj
      (CommRingCat.of Λ))).obj (op (resolutionChart Λ B hS X hX U n)))
      (resolutionTermAlgebra Λ B hS X U n) (resolutionChartRing Λ B hS X hX U n) :=
    ⟨fun a b c => by simp only [Algebra.smul_def, mul_left_comm]⟩
  exact ⟨fun q => KaehlerDifferential.map_D (ULift.{u + 1} Λ) _
    (resolutionTermAlgebra Λ B hS X U n) (resolutionChartRing Λ B hS X hX U n) q,
    fun q ω => (KaehlerDifferential.map (ULift.{u + 1} Λ) _ (resolutionTermAlgebra Λ B hS X U n)
      (resolutionChartRing Λ B hS X hX U n)).map_smul q ω⟩

/-- `resolutionToChartDifferentials` sends `d q` to `d` of the corresponding function on the
chart. -/
theorem resolutionToChartDifferentials_D (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X)
    (n : SimplexCategory) (q : resolutionTermAlgebra Λ B hS X U n) :
    resolutionToChartDifferentials Λ B hS X hX U n
        (KaehlerDifferential.D (ULift.{u + 1} Λ) (resolutionTermAlgebra Λ B hS X U n) q) =
      CommRingCat.KaehlerDifferential.d (resolutionToChartHom Λ B hS X hX U n q) :=
  (resolutionToChartDifferentials_D_and_smul Λ B hS X hX U n).1 q

/-- `resolutionToChartDifferentials` is semilinear along the inverse of `chartResolutionIso`. -/
theorem resolutionToChartDifferentials_smul (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X)
    (n : SimplexCategory) (q : resolutionTermAlgebra Λ B hS X U n)
    (ω : Ω[resolutionTermAlgebra Λ B hS X U n⁄ULift.{u + 1} Λ]) :
    resolutionToChartDifferentials Λ B hS X hX U n (q • ω) =
      resolutionToChartHom Λ B hS X hX U n q •
        resolutionToChartDifferentials Λ B hS X hX U n ω :=
  (resolutionToChartDifferentials_D_and_smul Λ B hS X hX U n).2 q ω

/-- The lifted sections `ULift 𝒪_X(U)` of the chart `𝐀_{n,U}`, read as the algebra
`liftedSectionsAlgebra`: the identity. -/
def chartSectionsDown (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X) (n : SimplexCategory) :
    (liftedEtalePresheaf Λ B hS X hX).obj (op (resolutionChart Λ B hS X hX U n)) →+*
      liftedSectionsAlgebra Λ B hS X U :=
  RingHom.id _

/-- `liftedSectionsAlgebra`, read as the lifted sections of the chart `𝐀_{n,U}`: the identity. -/
def chartSectionsUp (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X) (n : SimplexCategory) :
    liftedSectionsAlgebra Λ B hS X U →+*
      (liftedEtalePresheaf Λ B hS X hX).obj (op (resolutionChart Λ B hS X hX U n)) :=
  RingHom.id _

/-- `chartSectionsUp`, landing in the ring `𝒪̲_X(𝐀_{n,U})` over which the sections of the chart
site presheaves are modules. -/
def chartScalarUp (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X) (n : SimplexCategory) :
    liftedSectionsAlgebra Λ B hS X U →+*
      (chartStructureRing Λ B hS X hX).obj.obj (op (resolutionChart Λ B hS X hX U n)) :=
  RingHom.id _

/-- The additive map `Ω_{Γ(𝐀_{n,U})/Λ} → L^{-n}_{𝒪_X(U)/Λ}`, `d p ↦ 1 ⊗ d p`, induced by
`chartCotangentDerivation`. -/
def chartCotangentDesc (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X) (n : SimplexCategory) :
    resolutionChartDifferentials Λ B hS X hX U n →+
      CommAlgCat.cotangentTerm.{u + 1, u + 1} (ULift.{u + 1} Λ)
        (liftedSectionsAlgebra Λ B hS X U) (op n) :=
  letI := ((liftedBasePresheafMap Λ B hS X hX).app
    (op (resolutionChart Λ B hS X hX U n))).hom.toAlgebra
  letI := Module.compHom
    ((ModuleCat.restrictScalars (chartAugmentationHom Λ B hS X hX U n)).obj
      (CommAlgCat.cotangentTerm.{u + 1, u + 1} (ULift.{u + 1} Λ)
        (liftedSectionsAlgebra Λ B hS X U) (op n)))
    ((liftedBasePresheafMap Λ B hS X hX).app (op (resolutionChart Λ B hS X hX U n))).hom
  haveI : IsScalarTower
      (((Functor.const _).obj (liftRing.obj (CommRingCat.of Λ))).obj
        (op (resolutionChart Λ B hS X hX U n)))
      (resolutionChartRing Λ B hS X hX U n)
      ((ModuleCat.restrictScalars (chartAugmentationHom Λ B hS X hX U n)).obj
        (CommAlgCat.cotangentTerm.{u + 1, u + 1} (ULift.{u + 1} Λ)
          (liftedSectionsAlgebra Λ B hS X U) (op n))) :=
    IsScalarTower.of_compHom _ _ _
  (Derivation.liftKaehlerDifferential
    (chartCotangentDerivation Λ B hS X hX U n)).toAddMonoidHom

/-- `chartCotangentDesc` sends `d p` to `1 ⊗ d p` and is semilinear along
`chartAugmentationHom`. -/
private theorem chartCotangentDesc_d_and_smul (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X)
    (n : SimplexCategory) :
    (∀ p : resolutionChartRing Λ B hS X hX U n,
      chartCotangentDesc Λ B hS X hX U n (CommRingCat.KaehlerDifferential.d p) =
        CommAlgCat.cotangentTermDifferential.{u + 1, u + 1} (ULift.{u + 1} Λ)
          (liftedSectionsAlgebra Λ B hS X U) (op n)
          ((chartResolutionIso Λ B hS X hX U n).hom p)) ∧
    ∀ (p : resolutionChartRing Λ B hS X hX U n)
      (m : resolutionChartDifferentials Λ B hS X hX U n),
      chartCotangentDesc Λ B hS X hX U n (p • m) =
        chartAugmentationHom Λ B hS X hX U n p • chartCotangentDesc Λ B hS X hX U n m := by
  let := ((liftedBasePresheafMap Λ B hS X hX).app
    (op (resolutionChart Λ B hS X hX U n))).hom.toAlgebra
  let := Module.compHom
    ((ModuleCat.restrictScalars (chartAugmentationHom Λ B hS X hX U n)).obj
      (CommAlgCat.cotangentTerm.{u + 1, u + 1} (ULift.{u + 1} Λ)
        (liftedSectionsAlgebra Λ B hS X U) (op n)))
    ((liftedBasePresheafMap Λ B hS X hX).app (op (resolutionChart Λ B hS X hX U n))).hom
  have : IsScalarTower
      (((Functor.const _).obj (liftRing.obj (CommRingCat.of Λ))).obj
        (op (resolutionChart Λ B hS X hX U n)))
      (resolutionChartRing Λ B hS X hX U n)
      ((ModuleCat.restrictScalars (chartAugmentationHom Λ B hS X hX U n)).obj
        (CommAlgCat.cotangentTerm.{u + 1, u + 1} (ULift.{u + 1} Λ)
          (liftedSectionsAlgebra Λ B hS X U) (op n))) :=
    IsScalarTower.of_compHom _ _ _
  exact ⟨fun p => Derivation.liftKaehlerDifferential_comp_D
      (chartCotangentDerivation Λ B hS X hX U n) p,
    fun p m => (Derivation.liftKaehlerDifferential
      (chartCotangentDerivation Λ B hS X hX U n)).map_smul p m⟩

/-- `chartCotangentDesc` sends `d p` to `1 ⊗ d p`. -/
theorem chartCotangentDesc_d (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X)
    (n : SimplexCategory) (p : resolutionChartRing Λ B hS X hX U n) :
    chartCotangentDesc Λ B hS X hX U n (CommRingCat.KaehlerDifferential.d p) =
      CommAlgCat.cotangentTermDifferential.{u + 1, u + 1} (ULift.{u + 1} Λ)
        (liftedSectionsAlgebra Λ B hS X U) (op n) ((chartResolutionIso Λ B hS X hX U n).hom p) :=
  (chartCotangentDesc_d_and_smul Λ B hS X hX U n).1 p

/-- `chartCotangentDesc` is semilinear along `chartAugmentationHom`. -/
theorem chartCotangentDesc_smul (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X)
    (n : SimplexCategory) (p : resolutionChartRing Λ B hS X hX U n)
    (m : resolutionChartDifferentials Λ B hS X hX U n) :
    chartCotangentDesc Λ B hS X hX U n (p • m) =
      chartAugmentationHom Λ B hS X hX U n p • chartCotangentDesc Λ B hS X hX U n m :=
  (chartCotangentDesc_d_and_smul Λ B hS X hX U n).2 p m

/-- The additive map `𝒪_X(U) ⊗_{Γ(𝐀_{n,U})} Ω_{Γ(𝐀_{n,U})/Λ} → L^{-n}_{𝒪_X(U)/Λ}`,
`b ⊗ d p ↦ b ⊗ d p`, of the computation in the proof of Tag 08VM, on the lifted sections. -/
def chartToCotangent (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X) (n : SimplexCategory) :
    (chartBaseChangePresheaf Λ B hS X hX).obj (op (resolutionChart Λ B hS X hX U n)) →+
      CommAlgCat.cotangentTerm.{u + 1, u + 1} (ULift.{u + 1} Λ)
        (liftedSectionsAlgebra Λ B hS X U) (op n) :=
  by
  letI := ((liftedEvaluation Λ B hS X hX).app
    (op (resolutionChart Λ B hS X hX U n))).hom.toAlgebra
  exact TensorProduct.liftAddHom (R := resolutionChartRing Λ B hS X hX U n)
    (M := (liftedEtalePresheaf Λ B hS X hX).obj (op (resolutionChart Λ B hS X hX U n)))
    (N := ULift.{u + 1} (resolutionChartDifferentials Λ B hS X hX U n))
    (P := CommAlgCat.cotangentTerm.{u + 1, u + 1} (ULift.{u + 1} Λ)
      (liftedSectionsAlgebra Λ B hS X U) (op n))
    (AddMonoidHom.mk' (fun b => AddMonoidHom.mk'
        (fun m => chartSectionsDown Λ B hS X hX U n b •
          chartCotangentDesc Λ B hS X hX U n m.down)
        (fun m m' => by
          rw [← smul_add]
          exact congrArg (chartSectionsDown Λ B hS X hX U n b • ·)
            (map_add (chartCotangentDesc Λ B hS X hX U n) _ _)))
      (fun b b' => by ext m; exact (congrArg (· • _) (map_add _ _ _)).trans (add_smul _ _ _)))
    (fun r b m => by
      change chartSectionsDown Λ B hS X hX U n (algebraMap _ _ r * b) • _ =
        chartSectionsDown Λ B hS X hX U n b •
          chartCotangentDesc Λ B hS X hX U n (r • m.down)
      rw [map_mul, chartCotangentDesc_smul, mul_comm, mul_smul]
      congr 2
      exact evaluation_app_apply Λ B hS X hX U n r)

/-- The augmentation of the chart undoes `resolutionToChartHom`. -/
theorem chartAugmentationHom_resolutionToChartHom
    (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X) (n : SimplexCategory)
    (q : resolutionTermAlgebra Λ B hS X U n) :
    chartAugmentationHom Λ B hS X hX U n (resolutionToChartHom Λ B hS X hX U n q) =
      CommAlgCat.standardResolutionAugmentationHom.{u + 1, u + 1} (ULift.{u + 1} Λ)
        (liftedSectionsAlgebra Λ B hS X U) (op n) q :=
  (rfl : _ = CommAlgCat.standardResolutionAugmentationHom.{u + 1, u + 1} (ULift.{u + 1} Λ)
        (liftedSectionsAlgebra Λ B hS X U) (op n)
        ((chartResolutionIso Λ B hS X hX U n).hom
          ((chartResolutionIso Λ B hS X hX U n).inv q))).trans
    (by rw [Iso.inv_hom_id_apply])

/-- The additive map `L^{-n}_{𝒪_X(U)/Λ} → 𝒪_X(U) ⊗_{Γ(𝐀_{n,U})} Ω_{Γ(𝐀_{n,U})/Λ}`,
`b ⊗ d q ↦ b ⊗ d q`, inverse to `chartToCotangent`. -/
def cotangentToChart (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X) (n : SimplexCategory) :
    CommAlgCat.cotangentTerm.{u + 1, u + 1} (ULift.{u + 1} Λ)
        (liftedSectionsAlgebra Λ B hS X U) (op n) →+
      (chartBaseChangePresheaf Λ B hS X hX).obj (op (resolutionChart Λ B hS X hX U n)) :=
  by
  letI := ((liftedEvaluation Λ B hS X hX).app
    (op (resolutionChart Λ B hS X hX U n))).hom.toAlgebra
  exact TensorProduct.liftAddHom (R := resolutionTermAlgebra Λ B hS X U n)
    (M := (ModuleCat.restrictScalars (CommAlgCat.standardResolutionAugmentationHom.{u + 1, u + 1}
      (ULift.{u + 1} Λ) (liftedSectionsAlgebra Λ B hS X U) (op n))).obj
        (ModuleCat.of _ (liftedSectionsAlgebra Λ B hS X U)))
    (N := Ω[resolutionTermAlgebra Λ B hS X U n⁄ULift.{u + 1} Λ])
    (P := TensorProduct (resolutionChartRing Λ B hS X hX U n)
      ((liftedEtalePresheaf Λ B hS X hX).obj (op (resolutionChart Λ B hS X hX U n)))
      (ULift.{u + 1} (resolutionChartDifferentials Λ B hS X hX U n)))
    (AddMonoidHom.mk' (fun b => AddMonoidHom.mk'
        (fun ω => chartSectionsUp Λ B hS X hX U n b ⊗ₜ[resolutionChartRing Λ B hS X hX U n]
          (ULift.up (resolutionToChartDifferentials Λ B hS X hX U n ω) :
            ULift.{u + 1} (resolutionChartDifferentials Λ B hS X hX U n)))
        (fun ω ω' => by rw [map_add]; exact TensorProduct.tmul_add _ _ _))
      (fun b b' => AddMonoidHom.ext fun ω =>
        (congrArg (· ⊗ₜ[resolutionChartRing Λ B hS X hX U n] _) (map_add _ _ _)).trans
          (TensorProduct.add_tmul _ _ _)))
    (fun q b ω => by
      change chartSectionsUp Λ B hS X hX U n
          (CommAlgCat.standardResolutionAugmentationHom.{u + 1, u + 1} (ULift.{u + 1} Λ) _
            (op n) q * (show liftedSectionsAlgebra Λ B hS X U from b)) ⊗ₜ _ =
        chartSectionsUp Λ B hS X hX U n b ⊗ₜ[resolutionChartRing Λ B hS X hX U n]
          (ULift.up (resolutionToChartDifferentials Λ B hS X hX U n (q • ω)) :
            ULift.{u + 1} (resolutionChartDifferentials Λ B hS X hX U n))
      rw [resolutionToChartDifferentials_smul]
      change _ = chartSectionsUp Λ B hS X hX U n b ⊗ₜ[resolutionChartRing Λ B hS X hX U n]
        (resolutionToChartHom Λ B hS X hX U n q •
          (ULift.up (resolutionToChartDifferentials Λ B hS X hX U n ω) :
            ULift.{u + 1} (resolutionChartDifferentials Λ B hS X hX U n)))
      rw [← TensorProduct.smul_tmul, Algebra.smul_def, map_mul]
      congr 2
      exact ((evaluation_app_apply Λ B hS X hX U n _).trans
        (chartAugmentationHom_resolutionToChartHom Λ B hS X hX U n q)).symm)

/-- `cotangentToChart` is linear along `chartSectionsUp`. -/
theorem cotangentToChart_smul (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X)
    (n : SimplexCategory) (b : liftedSectionsAlgebra Λ B hS X U)
    (x : CommAlgCat.cotangentTerm.{u + 1, u + 1} (ULift.{u + 1} Λ)
      (liftedSectionsAlgebra Λ B hS X U) (op n)) :
    cotangentToChart Λ B hS X hX U n (b • x) =
      chartScalarUp Λ B hS X hX U n b • cotangentToChart Λ B hS X hX U n x := by
  let := ((liftedEvaluation Λ B hS X hX).app
    (op (resolutionChart Λ B hS X hX U n))).hom.toAlgebra
  induction x using TensorProduct.inductionOn (R := resolutionTermAlgebra Λ B hS X U n)
      (M := (ModuleCat.restrictScalars (CommAlgCat.standardResolutionAugmentationHom.{u + 1, u + 1}
        (ULift.{u + 1} Λ) (liftedSectionsAlgebra Λ B hS X U) (op n))).obj
          (ModuleCat.of _ (liftedSectionsAlgebra Λ B hS X U)))
      (N := Ω[resolutionTermAlgebra Λ B hS X U n⁄ULift.{u + 1} Λ]) with
  | add x x' hx hx' =>
    exact (congrArg _ (smul_add (A := CommAlgCat.cotangentTerm.{u + 1, u + 1} (ULift.{u + 1} Λ)
      (liftedSectionsAlgebra Λ B hS X U) (op n)) b x x')).trans ((map_add _ _ _).trans
      ((congrArg₂ (· + ·) hx hx').trans ((smul_add (A := (chartBaseChangePresheaf Λ B hS X
        hX).obj (op (resolutionChart Λ B hS X hX U n))) _ _ _).symm.trans
        (congrArg _ (map_add _ _ _).symm))))
  | tmul b' ω =>
    exact (congrArg (fun z => z ⊗ₜ[resolutionChartRing Λ B hS X hX U n]
      (ULift.up (resolutionToChartDifferentials Λ B hS X hX U n ω) :
        ULift.{u + 1} (resolutionChartDifferentials Λ B hS X hX U n)))
      ((map_mul (chartSectionsUp Λ B hS X hX U n) b b').trans
        (smul_eq_mul _ _).symm)).trans (TensorProduct.smul_tmul' _ _ _).symm

/-- `chartCotangentDesc` undoes `resolutionToChartDifferentials`: the composite
`Ω_{P'_n/ULift Λ} → Ω_{ULift Γ(𝐀_{n,U})/ULift Λ} → L^{-n}_{𝒪_X(U)/Λ}` is `ω ↦ 1 ⊗ ω`. -/
theorem chartCotangentDesc_resolutionToChartDifferentials
    (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X) (n : SimplexCategory)
    (ω : Ω[resolutionTermAlgebra Λ B hS X U n⁄ULift.{u + 1} Λ]) :
    chartCotangentDesc Λ B hS X hX U n
        (resolutionToChartDifferentials Λ B hS X hX U n ω) =
      ((1 : liftedSectionsAlgebra Λ B hS X U) ⊗ₜ[resolutionTermAlgebra Λ B hS X U n,
        CommAlgCat.standardResolutionAugmentationHom.{u + 1, u + 1} (ULift.{u + 1} Λ) _ (op n)] ω :
        CommAlgCat.cotangentTerm.{u + 1, u + 1} (ULift.{u + 1} Λ)
          (liftedSectionsAlgebra Λ B hS X U) (op n)) := by
  have hω : ω ∈ Submodule.span (resolutionTermAlgebra Λ B hS X U n)
      (Set.range (KaehlerDifferential.D (ULift.{u + 1} Λ)
        (resolutionTermAlgebra Λ B hS X U n))) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q, rfl⟩ := hx
    rw [resolutionToChartDifferentials_D, chartCotangentDesc_d, Iso.inv_hom_id_apply]
    rfl
  | zero => rw [map_zero, map_zero]; exact (TensorProduct.tmul_zero _ _).symm
  | add x y _ _ hx hy =>
    rw [map_add, map_add, hx, hy]; exact (TensorProduct.tmul_add _ _ _).symm
  | smul q x _ hx =>
    rw [resolutionToChartDifferentials_smul, chartCotangentDesc_smul, hx]
    rw [chartAugmentationHom_resolutionToChartHom]
    let : Algebra (resolutionTermAlgebra Λ B hS X U n) (liftedSectionsAlgebra Λ B hS X U) :=
      (CommAlgCat.standardResolutionAugmentationHom.{u + 1, u + 1} (ULift.{u + 1} Λ)
        (liftedSectionsAlgebra Λ B hS X U) (op n)).toAlgebra
    change CommAlgCat.standardResolutionAugmentationHom.{u + 1, u + 1} (ULift.{u + 1} Λ)
        (liftedSectionsAlgebra Λ B hS X U) (op n) q •
        ((1 : liftedSectionsAlgebra Λ B hS X U) ⊗ₜ[resolutionTermAlgebra Λ B hS X U n] x) =
      (1 : liftedSectionsAlgebra Λ B hS X U) ⊗ₜ[resolutionTermAlgebra Λ B hS X U n] (q • x)
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
    congr 1

/-- `cotangentToChart` undoes `chartCotangentDesc`: the composite
`Ω_{ULift Γ(𝐀_{n,U})/ULift Λ} → L^{-n}_{𝒪_X(U)/Λ} → ULift 𝒪_X(U) ⊗ Ω_{ULift Γ(𝐀_{n,U})/ULift Λ}` is
`m ↦ 1 ⊗ m`. -/
theorem cotangentToChart_chartCotangentDesc (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X)
    (n : SimplexCategory) (m : resolutionChartDifferentials Λ B hS X hX U n) :
    cotangentToChart Λ B hS X hX U n (chartCotangentDesc Λ B hS X hX U n m) =
      letI := ((liftedEvaluation Λ B hS X hX).app
        (op (resolutionChart Λ B hS X hX U n))).hom.toAlgebra
      ((1 : (liftedEtalePresheaf Λ B hS X hX).obj
          (op (resolutionChart Λ B hS X hX U n))) ⊗ₜ[resolutionChartRing Λ B hS X hX U n]
        (ULift.up m : ULift.{u + 1} (resolutionChartDifferentials Λ B hS X hX U n)) :
        TensorProduct (resolutionChartRing Λ B hS X hX U n)
          ((liftedEtalePresheaf Λ B hS X hX).obj (op (resolutionChart Λ B hS X hX U n)))
          (ULift.{u + 1} (resolutionChartDifferentials Λ B hS X hX U n))) := by
  let := ((liftedEvaluation Λ B hS X hX).app
    (op (resolutionChart Λ B hS X hX U n))).hom.toAlgebra
  let := ((liftedBasePresheafMap Λ B hS X hX).app
    (op (resolutionChart Λ B hS X hX U n))).hom.toAlgebra
  have hm : m ∈ Submodule.span (resolutionChartRing Λ B hS X hX U n)
      (Set.range (KaehlerDifferential.D (((Functor.const _).obj (liftRing.obj
        (CommRingCat.of Λ))).obj (op (resolutionChart Λ B hS X hX U n)))
        (resolutionChartRing Λ B hS X hX U n))) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    change cotangentToChart Λ B hS X hX U n
      (chartCotangentDesc Λ B hS X hX U n (CommRingCat.KaehlerDifferential.d p)) = _
    rw [chartCotangentDesc_d]
    change chartSectionsUp Λ B hS X hX U n 1 ⊗ₜ[resolutionChartRing Λ B hS X hX U n]
      (ULift.up (resolutionToChartDifferentials Λ B hS X hX U n
        (KaehlerDifferential.D (ULift.{u + 1} Λ) _
          ((chartResolutionIso Λ B hS X hX U n).hom p))) :
          ULift.{u + 1} (resolutionChartDifferentials Λ B hS X hX U n)) = _
    have hp : resolutionToChartHom Λ B hS X hX U n
        ((chartResolutionIso Λ B hS X hX U n).hom p) = p :=
      Iso.hom_inv_id_apply (chartResolutionIso Λ B hS X hX U n) p
    rw [resolutionToChartDifferentials_D, map_one, hp]
    rfl
  | zero =>
    rw [map_zero, map_zero]
    exact (TensorProduct.tmul_zero _ _).symm
  | add x y _ _ hx hy =>
    rw [map_add, map_add, hx, hy]
    exact (TensorProduct.tmul_add _ _ _).symm
  | smul p x _ hx =>
    refine (congrArg (cotangentToChart Λ B hS X hX U n)
      (chartCotangentDesc_smul Λ B hS X hX U n p x)).trans ?_
    refine (cotangentToChart_smul Λ B hS X hX U n _ _).trans ?_
    rw [hx]
    have hp : chartSectionsUp Λ B hS X hX U n (chartAugmentationHom Λ B hS X hX U n p) =
        algebraMap _ _ p :=
      (evaluation_app_apply Λ B hS X hX U n p).symm
    change chartSectionsUp Λ B hS X hX U n (chartAugmentationHom Λ B hS X hX U n p) •
        ((1 : (liftedEtalePresheaf Λ B hS X hX).obj
          (op (resolutionChart Λ B hS X hX U n))) ⊗ₜ[resolutionChartRing Λ B hS X hX U n]
            (ULift.up x : ULift.{u + 1} (resolutionChartDifferentials Λ B hS X hX U n))) =
      (1 : (liftedEtalePresheaf Λ B hS X hX).obj
          (op (resolutionChart Λ B hS X hX U n))) ⊗ₜ[resolutionChartRing Λ B hS X hX U n]
        (p • (ULift.up x : ULift.{u + 1} (resolutionChartDifferentials Λ B hS X hX U n)))
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul', hp]
    rfl

/-- `chartToCotangent` is a left inverse of `cotangentToChart`. -/
theorem chartToCotangent_cotangentToChart (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X)
    (n : SimplexCategory)
    (x : CommAlgCat.cotangentTerm.{u + 1, u + 1} (ULift.{u + 1} Λ)
      (liftedSectionsAlgebra Λ B hS X U) (op n)) :
    chartToCotangent Λ B hS X hX U n (cotangentToChart Λ B hS X hX U n x) = x := by
  induction x using TensorProduct.inductionOn (R := resolutionTermAlgebra Λ B hS X U n)
      (M := (ModuleCat.restrictScalars (CommAlgCat.standardResolutionAugmentationHom.{u + 1, u + 1}
        (ULift.{u + 1} Λ) (liftedSectionsAlgebra Λ B hS X U) (op n))).obj
          (ModuleCat.of _ (liftedSectionsAlgebra Λ B hS X U)))
      (N := Ω[resolutionTermAlgebra Λ B hS X U n⁄ULift.{u + 1} Λ]) with
  | add x y hx hy =>
    exact (congrArg _ (map_add _ x y)).trans ((map_add _ _ _).trans (congrArg₂ (· + ·) hx hy))
  | tmul b ω =>
    change chartSectionsDown Λ B hS X hX U n (chartSectionsUp Λ B hS X hX U n b) •
      chartCotangentDesc Λ B hS X hX U n
        (resolutionToChartDifferentials Λ B hS X hX U n ω) = _
    rw [chartCotangentDesc_resolutionToChartDifferentials]
    exact (ModuleCat.ExtendScalars.smul_tmul
      (f := CommAlgCat.standardResolutionAugmentationHom.{u + 1, u + 1}
      (ULift.{u + 1} Λ) (liftedSectionsAlgebra Λ B hS X U) (op n))
      (M := ModuleCat.of _ Ω[resolutionTermAlgebra Λ B hS X U n⁄ULift.{u + 1} Λ]) _ 1 ω).trans
      (congrArg (fun z => (z ⊗ₜ[resolutionTermAlgebra Λ B hS X U n,
        CommAlgCat.standardResolutionAugmentationHom.{u + 1, u + 1} (ULift.{u + 1} Λ) _ (op n)] ω :
          CommAlgCat.cotangentTerm.{u + 1, u + 1} (ULift.{u + 1} Λ)
            (liftedSectionsAlgebra Λ B hS X U) (op n)))
        (mul_one (show liftedSectionsAlgebra Λ B hS X U from b)))

/-- `chartToCotangent` is a right inverse of `cotangentToChart`. -/
theorem cotangentToChart_chartToCotangent (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X)
    (n : SimplexCategory)
    (t : (chartBaseChangePresheaf Λ B hS X hX).obj (op (resolutionChart Λ B hS X hX U n))) :
    cotangentToChart Λ B hS X hX U n (chartToCotangent Λ B hS X hX U n t) = t := by
  let := ((liftedEvaluation Λ B hS X hX).app
    (op (resolutionChart Λ B hS X hX U n))).hom.toAlgebra
  induction t using TensorProduct.inductionOn (R := resolutionChartRing Λ B hS X hX U n)
      (M := (liftedEtalePresheaf Λ B hS X hX).obj (op (resolutionChart Λ B hS X hX U n)))
      (N := ULift.{u + 1} (resolutionChartDifferentials Λ B hS X hX U n)) with
  | add x y hx hy =>
    exact (congrArg _ (map_add _ x y)).trans ((map_add _ _ _).trans (congrArg₂ (· + ·) hx hy))
  | tmul b m =>
    change cotangentToChart Λ B hS X hX U n (chartSectionsDown Λ B hS X hX U n b •
      chartCotangentDesc Λ B hS X hX U n m.down) = _
    rw [cotangentToChart_smul, cotangentToChart_chartCotangentDesc]
    change b • ((1 : (liftedEtalePresheaf Λ B hS X hX).obj
        (op (resolutionChart Λ B hS X hX U n))) ⊗ₜ[resolutionChartRing Λ B hS X hX U n]
          m) = b ⊗ₜ[resolutionChartRing Λ B hS X hX U n] m
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end AlgebraicGeometry.Space.PolynomialChart
