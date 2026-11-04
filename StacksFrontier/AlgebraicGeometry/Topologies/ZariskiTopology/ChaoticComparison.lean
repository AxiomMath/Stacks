module

public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.AffineZariskiSheafCriterion
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.ChaoticRingedSites
public import StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietoris.DescentForAFamilyOfSquares
import StacksCore.Tactic.StacksAttribute

/-!
# Derived Zariski descent on the affine opens of a scheme

Let `B` be a big Zariski site containing a scheme `S`, let `𝒪` be a sheaf of commutative rings
for the Zariski topology on the affine opens of `S`, and let `ε` be the comparison from the
Zariski topology to the chaotic topology, for which every presheaf is a sheaf. A bounded-below
object `K` of the derived category of module sheaves for the chaotic topology lies in the
essential image of `Rε_*` exactly when its derived sections vanish over every empty affine open
and the canonical Mayer–Vietoris map of Stacks 0F16 is an isomorphism at `K` for every square
exhibiting an affine open as the union of two standard opens.

## Main results

* `AlgebraicGeometry.SmallAffineZariski.essImage_iff_isZero_derivedSections_and_isCSquareIso` —
  **Stacks 0F1L.**

## Implementation notes

The criterion of Stacks 0F18 does not apply to the chaotic topology directly, because a presheaf
turning the standard open cover squares into cartesian squares of sections need not be a Zariski
sheaf: nothing forces its sections over an empty affine open to be a single point. It does apply
to the almost chaotic topology, in which the empty sieve covers the empty affine opens, and
module sheaves for the almost chaotic topology are the same as module sheaves for the chaotic
one, so the criterion transfers along that equivalence.

## References

* [Stacks Project, Tag 0F1L](https://stacks.math.columbia.edu/tag/0F1L)
* [Stacks Project, Tag 0F16](https://stacks.math.columbia.edu/tag/0F16)
* [Stacks Project, Tag 0F18](https://stacks.math.columbia.edu/tag/0F18)
* [Stacks Project, Tag 0F19](https://stacks.math.columbia.edu/tag/0F19)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.MayerVietoris Stacks.Sites.CoarserTopology

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.SmallAffineZariski

section Transfer

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E] (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
  [hF : F.Additive] [hG : G.Additive] [hH : H.Additive] [hGe : G.IsEquivalence]
  (iso : F ⋙ G ≅ H) (RF : DerivedCategory C ⥤ DerivedCategory D)
  (unit : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RF)

/-- The unit exhibiting a right derived functor of `F`, followed by an exact equivalence `G`, as a
right derived functor of a functor `H` identified with `F ⋙ G`. -/
private def compDerivedUnit :
    H.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF ⋙ G.mapDerivedCategory :=
  (Functor.mapHomotopyCategoryQhCompMapDerivedCategoryIso F G H iso).hom ≫
    Functor.whiskerRight unit G.mapDerivedCategory ≫ (Functor.associator _ _ _).hom

/-- A right derived functor of `F`, followed by an exact equivalence `G`, is a right derived
functor of any functor identified with `F ⋙ G`. -/
private lemma isRightDerivedFunctor_compDerivedUnit
    [hRD : RF.IsRightDerivedFunctor unit (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))] :
    (RF ⋙ G.mapDerivedCategory).IsRightDerivedFunctor
      (compDerivedUnit F G H iso RF unit)
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) := by
  have : G.mapDerivedCategory.IsEquivalence := Functor.isEquivalence_mapDerivedCategory G
  have : (RF ⋙ G.mapDerivedCategory).IsRightDerivedFunctor
      (Functor.whiskerRight unit G.mapDerivedCategory ≫ (Functor.associator _ _ _).hom)
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) := by
    rw [Functor.isRightDerivedFunctor_iff_isLeftKanExtension]
    exact (Functor.isLeftKanExtension_postcompose₂_iff RF unit G.mapDerivedCategory).mpr
      (Functor.IsRightDerivedFunctor.isLeftKanExtension RF unit
        (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)))
  exact Functor.isRightDerivedFunctor_of_iso _ _ _
    (Functor.mapHomotopyCategoryQhCompMapDerivedCategoryIso F G H iso)

end Transfer

variable (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (O : Sheaf (topology B S hS) CommRingCat.{u + 1})
  (Rε : DerivedCategory (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite B S hS O).O)) ⥤
    DerivedCategory (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (trivialRingedSite B S hS O).O)))
  (η : letI := modulePushforward_additive.{u + 1, u + 1, u, u + 1} (trivial_le_topology B S hS)
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite B S hS O).O)
      (modulePushforward.{u + 1, u + 1, u, u + 1} (trivial_le_topology B S hS)
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite B S hS O).O)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rε)

/-- The derived direct image to the almost chaotic topology: the derived direct image to the
chaotic topology, followed by the equivalence of the two categories of module sheaves. -/
private def almostChaoticDerivedPushforward :
    DerivedCategory (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite B S hS O).O)) ⥤
      DerivedCategory (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (almostChaoticRingedSite B S hS O).O)) :=
  Rε ⋙ trivialModulesToAlmostChaoticDerived B S hS O

include η in
/-- The unit exhibiting the derived direct image to the almost chaotic topology as a right derived
functor of the direct image to that topology. -/
private def almostChaoticDerivedUnit :
    letI := modulePushforward_additive.{u + 1, u + 1, u, u + 1} (almostChaotic_le_topology B S hS)
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite B S hS O).O)
    (modulePushforward.{u + 1, u + 1, u, u + 1} (almostChaotic_le_topology B S hS)
          (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite B S hS O).O)).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ almostChaoticDerivedPushforward B S hS O Rε :=
  compDerivedUnit
    (modulePushforward.{u + 1, u + 1, u, u + 1} (trivial_le_topology B S hS)
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite B S hS O).O))
    (trivialModulesToAlmostChaotic B S hS O)
    (modulePushforward.{u + 1, u + 1, u, u + 1} (almostChaotic_le_topology B S hS)
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite B S hS O).O))
    (modulePushforwardAlmostChaoticIso B S hS O) Rε η
    (hF := modulePushforward_additive.{u + 1, u + 1, u, u + 1}
      (trivial_le_topology B S hS) (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite B S hS O).O))
    (hG := trivialModulesToAlmostChaotic_additive B S hS O)
    (hH := modulePushforward_additive.{u + 1, u + 1, u, u + 1}
      (almostChaotic_le_topology B S hS)
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite B S hS O).O))
    (hGe := trivialModulesToAlmostChaotic_isEquivalence B S hS O)

variable [hRε : Rε.IsRightDerivedFunctor η
  (HomotopyCategory.quasiIso
    (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite B S hS O).O))
    (ComplexShape.up ℤ))]

/-- A derived direct image to the chaotic topology, read through the equivalence of the two
categories of module sheaves, is a derived direct image to the almost chaotic topology. -/
private instance isRightDerivedFunctor_almostChaoticDerivedUnit :
    (almostChaoticDerivedPushforward B S hS O Rε).IsRightDerivedFunctor
      (almostChaoticDerivedUnit B S hS O Rε η)
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite B S hS O).O))
        (ComplexShape.up ℤ)) :=
  by
    unfold almostChaoticDerivedUnit
    exact isRightDerivedFunctor_compDerivedUnit _ _ _ _ _ _ (hF := _) (hG := _) (hH := _) (hGe := _)
      (hRD := hRε)

include η in
/-- On the essential image of the derived direct image to the almost chaotic topology the
canonical map of a standard open cover square is an isomorphism, by Stacks 0F19. -/
private lemma isCSquareIso_almostChaotic_of_essImage
    (K : DerivedCategory (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (almostChaoticRingedSite B S hS O).O)))
    (hK : (almostChaoticDerivedPushforward B S hS O Rε).essImage K)
    (sq : Square (SmallAffineZariski B S hS)) (hsq : IsStandardOpenCoverSquare B S hS sq) :
    (Stacks.MayerVietoris.CanonicalMapOfComplexes.derivedCSquareData.{u + 1, u + 1}
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf (almostChaoticRingedSite B S hS O).O))
      sq).IsCSquareIso K :=
  isCSquareIso_ofLe_of_isPushout.{u + 1, u + 1, u, u + 1}
    (S := ringedSite B S hS O) (J' := almostChaotic B S hS)
    (almostChaotic_le_topology B S hS) sq
    hsq.isPushout_sheafifiedYoneda hsq.mono_sheafifiedYoneda_map_f₁₂
    (almostChaoticDerivedPushforward B S hS O Rε) (almostChaoticDerivedUnit B S hS O Rε η) K hK

include η in
/-- **Stacks 0F18 for the almost chaotic topology.** A bounded-below object of the derived category
of module sheaves for the almost chaotic topology lies in the essential image of the derived
direct image exactly when the canonical map of every standard open cover square is an isomorphism
at it. -/
private lemma essImage_almostChaotic_iff_isCSquareIso
    (K : DerivedCategory (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (almostChaoticRingedSite B S hS O).O)))
    (hK : (DerivedCategory.TStructure.t (C := SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (almostChaoticRingedSite B S hS O).O))).plus K) :
    (almostChaoticDerivedPushforward B S hS O Rε).essImage K ↔
      ∀ a : {sq : Square (SmallAffineZariski B S hS) // IsStandardOpenCoverSquare B S hS sq},
        (Stacks.MayerVietoris.CanonicalMapOfComplexes.derivedCSquareData.{u + 1, u + 1}
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf (almostChaoticRingedSite B S hS O).O))
          (a : Square (SmallAffineZariski B S hS))).IsCSquareIso K :=
  @essImage_iff_forall_isCSquareIso.{u + 1, u + 1, u, u + 1, u + 1}
    (ringedSite B S hS O) (almostChaotic B S hS) (almostChaotic_le_topology B S hS)
    _ _ _ _ _ _ _
    {sq : Square (SmallAffineZariski B S hS) // IsStandardOpenCoverSquare B S hS sq}
    (fun a => (a : Square (SmallAffineZariski B S hS)))
    (fun F hF => isSheaf_smallAffineZariski_of_almostChaotic B S hS F
      fun sq hsq => hF ⟨sq, hsq⟩)
    (almostChaoticDerivedPushforward B S hS O Rε) (almostChaoticDerivedUnit B S hS O Rε η)
    (isRightDerivedFunctor_almostChaoticDerivedUnit B S hS O Rε η)
    (fun K' hK' a => isCSquareIso_almostChaotic_of_essImage B S hS O Rε η K' hK' _ a.2) K hK

include η in
/-- **Stacks 0F1L.** Let `𝒪` be a sheaf of rings for the Zariski topology on the affine opens of a
scheme `S` and let `ε` be the comparison from the Zariski topology to the chaotic topology, in
which every presheaf is a sheaf. A bounded-below object `K` of `D(𝒪_chaotic)` lies in the
essential image of the derived direct image `Rε_*` if and only if the derived sections of `K` over
every empty affine open vanish and the canonical map `c^K_{U,V,W,V ∩ W}` of Stacks 0F16 is an
isomorphism for every square exhibiting an affine open `U` as the union of two standard opens `V`
and `W` with intersection `V ∩ W`. -/
@[stacks 0F1L]
theorem essImage_iff_isZero_derivedSections_and_isCSquareIso
    (K : DerivedCategory (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (trivialRingedSite B S hS O).O)))
    (hK : (DerivedCategory.TStructure.t
      (C := SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (trivialRingedSite B S hS O).O))).plus K) :
    Rε.essImage K ↔
      ((∀ (sq : Square (SmallAffineZariski B S hS)) (U : SmallAffineZariski B S hS),
          IsEmpty ((toScheme B S hS).obj U) →
            IsZero (((Stacks.MayerVietoris.CanonicalMapOfComplexes.derivedCSquareData.{u + 1,
              u + 1} (R := (Stacks.SheafOfModules.Tensor.ringSheaf (trivialRingedSite B S hS O).O))
              sq).derivedSections U).obj K)) ∧
        ∀ sq : Square (SmallAffineZariski B S hS), IsStandardOpenCoverSquare B S hS sq →
          (Stacks.MayerVietoris.CanonicalMapOfComplexes.derivedCSquareData.{u + 1, u + 1}
            (R := (Stacks.SheafOfModules.Tensor.ringSheaf (trivialRingedSite B S hS O).O))
            sq).IsCSquareIso K) := by
  have descent := essImage_almostChaotic_iff_isCSquareIso B S hS O Rε η
    ((trivialModulesToAlmostChaoticDerived B S hS O).obj K)
    (Functor.plus_mapDerivedCategory_obj (trivialModulesToAlmostChaotic B S hS O) K hK)
  have hequiv : (trivialModulesToAlmostChaoticDerived B S hS O).IsEquivalence :=
    Functor.isEquivalence_mapDerivedCategory (trivialModulesToAlmostChaotic B S hS O)
  refine ⟨fun himage => ⟨fun sq U hU =>
    (isZero_derivedSections_of_isEmpty B S hS O sq U hU).obj K, fun sq hsq => ?_⟩, ?_⟩
  · refine (isCSquareIso_trivial_iff_almostChaotic B S hS O sq K).mpr (descent.mp ?_ ⟨sq, hsq⟩)
    obtain ⟨M, ⟨iso⟩⟩ := himage
    exact ⟨M, ⟨(trivialModulesToAlmostChaoticDerived B S hS O).mapIso iso⟩⟩
  · rintro ⟨-, hsquares⟩
    obtain ⟨M, ⟨iso⟩⟩ := descent.mpr fun a =>
      (isCSquareIso_trivial_iff_almostChaotic B S hS O _ K).mp (hsquares _ a.2)
    have hiso : (trivialModulesToAlmostChaoticDerived B S hS O).obj (Rε.obj M) ≅
        (trivialModulesToAlmostChaoticDerived B S hS O).obj K := iso
    exact ⟨M, ⟨(trivialModulesToAlmostChaoticDerived B S hS O).preimageIso hiso⟩⟩

end AlgebraicGeometry.SmallAffineZariski

end
