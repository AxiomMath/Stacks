module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerivedComparison.ConnectingMorphism
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeUnit
public import StacksFrontier.Algebra.Homology.RightDerivedDelta

/-!
# The canonical map `(G X)[0] ⟶ RG(X[0])` and the connecting morphisms

Let `G : 𝒜' ⥤ 𝒜` be an additive functor, `𝒜'` with enough injectives. The canonical map
`(G X)[0] ⟶ RG(X[0])` of `Stacks.DerivedIndexing.rightDerivedPlusUnitSingle` is, on an
injective resolution `X → I`, the class of `G` applied to the augmentation. Consequently it is
compatible with connecting morphisms: for short exact sequences `S` of `𝒜` and `S'` of `𝒜'` and a
morphism of short complexes `μ : S ⟶ G(S')` (where `G(S')` need not be exact), the maps
`S.Xᵢ[0] ⟶ G(S'.Xᵢ)[0] ⟶ RG(S'.Xᵢ[0])` carry the connecting morphism `S.X₃[0] ⟶ S.X₁[0]⟦1⟧` of
`S` to the image under `RG` of that of `S'`.

## Main results

* `Stacks.DerivedIndexing.ι_map_unitSingle_comp_resolutionDerivedComparison`: the canonical map
  read on an injective resolution.
* `Stacks.DerivedIndexing.singleδPlus_comp_unitSingle`: **the compatibility with the connecting
  morphisms.**
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

namespace Stacks.DerivedIndexing

section

attribute [local instance] HasDerivedCategory.standard

variable {A A' : Type*} [Category* A] [Category* A'] [Abelian A] [Abelian A']
  [EnoughInjectives A'] (G : A' ⥤ A) [G.Additive]

open Stacks.Cohomology.HigherDirectImagePresheaf

/-- The canonical map `(G X)[0] ⟶ RG(X[0])` followed by `RG` of the comparison of `X[0]` with an
injective resolution `I` is the class of `G` applied to the augmentation, followed by the unit of
`RG` at `I`. -/
theorem unitSingle_comp_map_resolutionDerivedIso {X : A'} (I : InjectiveResolution X) :
    (rightDerivedPlusUnitSingle G).app X ≫
        G.rightDerivedFunctorPlus.map (resolutionDerivedIso I).hom =
      (Functor.mapSingleFunctorCompQhIso G).inv.app X ≫
        DerivedCategory.Plus.Qh.map (G.mapHomotopyCategoryPlus.map
          ((singlePlusToCochainQuotientIso (A := A')).hom.app X ≫
            (HomotopyCategory.Plus.quotient A').map (resolutionSinglePlusHom I))) ≫
        G.rightDerivedFunctorPlusUnit.app
          ((HomotopyCategory.Plus.quotient A').obj (resolutionCochainPlus I)) := by
  have hn := G.rightDerivedFunctorPlusUnit.naturality
    ((singlePlusToCochainQuotientIso (A := A')).hom.app X ≫
      (HomotopyCategory.Plus.quotient A').map (resolutionSinglePlusHom I))
  rw [Functor.comp_map, Functor.comp_map] at hn
  simp only [rightDerivedPlusUnitSingle, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  rw [resolutionDerivedIso_hom_eq', assoc, assoc,
    ← G.rightDerivedFunctorPlus.map_comp, Iso.inv_hom_id_app_assoc,
    ← DerivedCategory.Plus.Qh.map_comp, hn]

omit [EnoughInjectives A'] in
/-- Two morphisms of complexes, read through the comparison of the two localizations. -/
theorem quotientCompQhIso_conj_comp {K L M : CochainComplex A ℤ} (a : K ⟶ L) (b : L ⟶ M) :
    (((DerivedCategory.quotientCompQhIso A).inv.app K ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map a)) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map b)) ≫
        (DerivedCategory.quotientCompQhIso A).hom.app M =
      DerivedCategory.Q.map (a ≫ b) := by
  rw [assoc, assoc, DerivedCategory.quotientCompQhIso_hom_naturality,
    ← assoc (DerivedCategory.Qh.map _), DerivedCategory.quotientCompQhIso_hom_naturality,
    ← assoc, ← assoc, Iso.inv_hom_id_app, id_comp, Functor.map_comp]

/-- The class of `G` applied to the augmentation of an injective resolution `I` of `X`, as a
morphism of cochain complexes `(G X)[0] ⟶ G(I)`. -/
abbrev resolutionMapSingle {X : A'} (I : InjectiveResolution X) :
    (HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj (G.obj X) ⟶
      (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (I.cocomplex.extend ComplexShape.embeddingUpNat) :=
  (HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).inv.app X ≫
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).map (resolutionSingleHom I)

/-- **The canonical map `(G X)[0] ⟶ RG(X[0])` read on an injective resolution `I` of `X`**: in
the derived category of `𝒜`, followed by the comparison of `RG(X[0])` with `G(I)`, it is the
class of `G` applied to the augmentation. -/
theorem ι_map_unitSingle_comp_resolutionDerivedComparison {X : A'}
    (I : InjectiveResolution X) :
    DerivedCategory.Plus.ι.map ((rightDerivedPlusUnitSingle G).app X) ≫
        (resolutionDerivedComparison G I).hom =
      DerivedCategory.Q.map (resolutionMapSingle G I) := by
  have h1 := unitSingle_comp_map_resolutionDerivedIso G I
  have h2 : DerivedCategory.Plus.ι.map ((rightDerivedPlusUnitSingle G).app X) ≫
      DerivedCategory.Plus.ι.map (derivedPlusResolutionIso G I).hom =
      DerivedCategory.Plus.ι.map ((Functor.mapSingleFunctorCompQhIso G).inv.app X ≫
        DerivedCategory.Plus.Qh.map (G.mapHomotopyCategoryPlus.map
          ((singlePlusToCochainQuotientIso (A := A')).hom.app X ≫
            (HomotopyCategory.Plus.quotient A').map (resolutionSinglePlusHom I)))) := by
    rw [← Functor.map_comp, derivedPlusResolutionIso_hom, ← assoc, h1, assoc, assoc,
      IsIso.hom_inv_id, comp_id]
  have hc : (HomotopyCategory.Plus.ι A').map
      ((singlePlusToCochainQuotientIso (A := A')).hom.app X ≫
        (HomotopyCategory.Plus.quotient A').map (resolutionSinglePlusHom I)) =
      (HomotopyCategory.quotient A' (ComplexShape.up ℤ)).map (resolutionSingleHom I) := by
    rw [Functor.map_comp, ι_map_singlePlusToCochainQuotientIso,
      singleFunctorPostcompQuotientIso_hom_app]
    exact Category.id_comp _
  have hd : DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Qh.map
      (G.mapHomotopyCategoryPlus.map
        ((singlePlusToCochainQuotientIso (A := A')).hom.app X ≫
          (HomotopyCategory.Plus.quotient A').map (resolutionSinglePlusHom I)))) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map (resolutionSingleHom I))) := by
    refine (congrArg (fun z => DerivedCategory.Qh.map
      ((G.mapHomotopyCategory (ComplexShape.up ℤ)).map z)) hc).trans ?_
    exact congrArg DerivedCategory.Qh.map
      (Functor.mapHomotopyCategory_map G (resolutionSingleHom I))
  have hsing := singleFunctorIsoCompQh_hom_app (C := A) 0 (G.obj X)
  refine (congrArg (DerivedCategory.Plus.ι.map ((rightDerivedPlusUnitSingle G).app X) ≫ ·)
    (resolutionDerivedComparison_hom G I)).trans ?_
  refine (assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) h2).trans ?_
  rw [Functor.map_comp, ι_map_mapSingleFunctorCompQhIso_inv_app, hsing, hd]
  exact quotientCompQhIso_conj_comp _ _

attribute [local instance] Functor.commShiftRightDerivedFunctorPlus
  Functor.natTransCommShiftRightDerivedFunctorPlusUnit
  Functor.isTriangulated_rightDerivedFunctorPlus

/-- The morphism of short exact sequences of cochain complexes from `S` placed in degree zero to
`G` applied to the extension of a resolution of `S'`, induced by `μ : S ⟶ G(S')`. -/
abbrev resolutionShortComplexHom {S : ShortComplex A} {S' : ShortComplex A'}
    (μ : S ⟶ S'.map G) (J : Stacks.Cohomology.RightDerivedDelta.Horseshoe S') :
    S.map (HomologicalComplex.single A (ComplexShape.up ℤ) 0) ⟶
      (extendShortComplex (ShortComplex.mk J.f J.g J.w)).map
        (G.mapHomologicalComplex (ComplexShape.up ℤ)) :=
  (HomologicalComplex.single A (ComplexShape.up ℤ) 0).mapShortComplex.map μ ≫
    (S'.mapNatIso (HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0)).inv ≫
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).mapShortComplex.map
      (augmentationShortComplexHom J.J₁ J.J₂ J.J₃ J.f J.g J.w J.comm₁ J.comm₂)

/-- **The canonical maps `(G X)[0] ⟶ RG(X[0])` are compatible with the connecting morphisms.**
For short exact sequences `S` of `𝒜` and `S'` of `𝒜'` and a morphism of short complexes
`μ : S ⟶ G(S')`, the composites `S.Xᵢ[0] ⟶ G(S'.Xᵢ)[0] ⟶ RG(S'.Xᵢ[0])` carry the connecting
morphism of `S` to the connecting morphism of the `RG`-image of the triangle of `S'`. -/
theorem singleδPlus_comp_unitSingle {S : ShortComplex A} (hS : S.ShortExact)
    {S' : ShortComplex A'} (hS' : S'.ShortExact) (μ : S ⟶ S'.map G) :
    singleδPlus hS ≫ ((DerivedCategory.Plus.singleFunctor A 0).map μ.τ₁ ≫
        (rightDerivedPlusUnitSingle G).app S'.X₁)⟦(1 : ℤ)⟧' =
      ((DerivedCategory.Plus.singleFunctor A 0).map μ.τ₃ ≫
        (rightDerivedPlusUnitSingle G).app S'.X₃) ≫ (derivedDeltaFunctorStructure G).δ hS' := by
  let J := Stacks.Cohomology.RightDerivedDelta.horseshoe hS'
  have hFR : ((ShortComplex.mk J.f J.g J.w).map
      (G.mapHomologicalComplex (ComplexShape.up ℕ))).ShortExact := J.shortExact_mapSequence G
  have hc3 := comm₃_resolutionDerivedComparison G hS' J.J₁ J.J₂ J.J₃ J.f J.g J.w J.comm₁
    J.comm₂ J.shortExact hFR
  have hδ' : Functor.mapδ DerivedCategory.Plus.ι ((derivedDeltaFunctorStructure G).δ hS') =
      Functor.mapδ (G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι)
        (Stacks.Cohomology.CechDelta.singlePlusδ hS') :=
    (mapδ_rightDerivedFunctorPlus_comp_ι_singlePlusδ G hS').symm
  have hs : Functor.mapδ DerivedCategory.Plus.ι (singleδPlus hS) =
      DerivedCategory.triangleOfSESδ
        (hS.map_of_exact (HomologicalComplex.single A (ComplexShape.up ℤ) 0)) :=
    ι_map_singleδPlus hS
  have hnat := DerivedCategory.triangleOfSESδ_naturality
    (hS.map_of_exact (HomologicalComplex.single A (ComplexShape.up ℤ) 0))
    (shortExact_mapExtend G hFR) (resolutionShortComplexHom G μ J)
  have hu₁ := ι_map_unitSingle_comp_resolutionDerivedComparison G J.J₁
  have hu₃ := ι_map_unitSingle_comp_resolutionDerivedComparison G J.J₃
  have hv₁ : DerivedCategory.Plus.ι.map ((DerivedCategory.Plus.singleFunctor A 0).map μ.τ₁ ≫
        (rightDerivedPlusUnitSingle G).app S'.X₁) ≫ (resolutionDerivedComparison G J.J₁).hom =
      DerivedCategory.Q.map (resolutionShortComplexHom G μ J).τ₁ := by
    rw [Functor.map_comp, assoc, hu₁]
    exact (DerivedCategory.Q.map_comp _ _).symm
  have hv₃ : DerivedCategory.Plus.ι.map ((DerivedCategory.Plus.singleFunctor A 0).map μ.τ₃ ≫
        (rightDerivedPlusUnitSingle G).app S'.X₃) ≫ (resolutionDerivedComparison G J.J₃).hom =
      DerivedCategory.Q.map (resolutionShortComplexHom G μ J).τ₃ := by
    rw [Functor.map_comp, assoc, hu₃]
    exact (DerivedCategory.Q.map_comp _ _).symm
  refine Functor.mapδ_cancel DerivedCategory.Plus.ι _ _ _ _ ?_
  refine (cancel_mono (((resolutionDerivedComparison G J.J₁).hom)⟦(1 : ℤ)⟧')).1 ?_
  rw [hδ', assoc, ← Functor.map_comp, hv₁, assoc, ← hc3, ← assoc, hv₃]
  exact (congrArg (· ≫ _) hs).trans hnat

end

end Stacks.DerivedIndexing
