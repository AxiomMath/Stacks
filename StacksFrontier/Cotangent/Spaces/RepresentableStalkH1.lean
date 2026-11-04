module

public import StacksFrontier.Cotangent.Spaces.RepresentableComparison
public import StacksFrontier.Cotangent.Spaces.RepresentableStalks
public import StacksFrontier.Cotangent.SheavesOfRings.HenselianStalkVanishing
public import StacksFrontier.Cotangent.SheavesOfRings.PointStalkCotangentComplex
public import StacksFrontier.Cotangent.CotangentComplexHomologyNegOne
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SitePointStalkAcyclic
public import StacksFrontier.Homology.ExtendScalars.IndependentUniverses
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSlicePointsOfFamily
public import StacksFrontier.Cotangent.H1CotangentRingEquiv

/-!
# `H⁻¹` of the cotangent complex of a morphism of represented algebraic spaces, on stalks

Let `h : T₁ ⟶ T₂` be a morphism of the big fppf site of a scheme `S`, with underlying morphism of
schemes `f₀ : X₀ ⟶ Y₀`, and let `f : X ⟶ Y` be the morphism of the algebraic spaces it
represents. This file shows that the cohomology sheaf `H⁻¹(L_{X/Y})` of the cotangent complex of
Stacks 08VD vanishes exactly when, at every point `x` of `X₀`, `H¹` of the naive cotangent complex
of the stalk map `𝒪_{Y₀, f₀ x} → 𝒪_{X₀, x}` vanishes.

The chain of identifications is:

1. Stacks 08VF, `AlgebraicGeometry.Space.quasiIso_representedCotangentComparison`, together with
   the identification of `ε^*L_{X₀/Y₀}` with `L_{ε⁻¹𝒪_{X₀}/ε⁻¹f₀⁻¹𝒪_{Y₀}} ⊗ 𝒪_X`, reads
   `H⁻¹(L_{X/Y})` on the latter complex, `ε` being the comparison morphism of Section 071P.
2. Exactness is tested at the geometric points of the small étale site of `X`, which form a
   conservative family; the stalk of the base-changed complex is the base change along the
   stalk of `ε♯` of the cotangent complex of the stalk ring map (Stacks 08T0), and the stalk of
   `ε♯` is a strict henselization, so faithfully flat, so the base change detects vanishing.
3. `H⁻¹` of the cotangent complex of a ring map is `H¹` of its naive cotangent complex, and the
   stalk ring map at a geometric point is, up to the ring isomorphisms of Stacks 05V1, the stalk
   map of `f₀` at the point of `X₀` under it; every point of `X₀` arises in this way.

## Main results

* `CategoryTheory.Sheaf.isZero_homology_negOne_stalk_baseChangedCotangentComplex_iff`:
  `H⁻¹` of a stalk of `L_{R/A} ⊗_R D` along a faithfully flat stalk map is `H¹` of the stalk ring
  map `A_Φ → R_Φ`.
* `Space.isZero_homology_negOne_cotangentComplex_representedSpaceMap_iff_stalkMap`, in the
  namespace `AlgebraicGeometry`: `H⁻¹(L_{X/Y}) = 0` if and only if
  `H¹(L_{𝒪_{X₀,x}/𝒪_{Y₀,f₀ x}}) = 0` for every `x`.

## Implementation notes

As in `StacksFrontier/Cotangent/Spaces/RepresentableComparison.lean`, three instances on
categories of sheaves of modules and of abelian groups are removed in the namespace of algebraic
spaces, and the sheafification instances of the small étale ringed topos are supplied locally.

## References

* [Stacks Project, Tag 08VF](https://stacks.math.columbia.edu/tag/08VF)
* [Stacks Project, Tag 08T0](https://stacks.math.columbia.edu/tag/08T0)
* [Stacks Project, Tag 05V1](https://stacks.math.columbia.edu/tag/05V1)
* [Stacks Project, Tag 0D12](https://stacks.math.columbia.edu/tag/0D12)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward TopologicalSpace

universe u

namespace CategoryTheory.Sheaf

universe v₁ u₁ w₁

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [LocallySmall.{max u₁ v₁ w₁} C] (Φ : J.Point.{max u₁ v₁ w₁})
  [HasSheafify J AddCommGrpCat.{max u₁ v₁ w₁}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u₁ v₁ w₁}]
  {A R D : Sheaf J CommRingCat.{max u₁ v₁ w₁}} (g : A ⟶ R) (k : R ⟶ D)

/-- **`H⁻¹` of a stalk of `L_{R/A} ⊗_R D` along a faithfully flat stalk map.** If the stalk map
of `k : R ⟶ D` at `Φ` is faithfully flat, `H⁻¹` of the stalk complex of `L_{R/A} ⊗_R D` at `Φ`
vanishes exactly when `H¹` of the naive cotangent complex of the stalk ring map `A_Φ → R_Φ`
does. -/
theorem isZero_homology_negOne_stalk_baseChangedCotangentComplex_iff
    (hff : (Stacks.SitePointBaseChange.stalkRingHom.{max u₁ v₁ w₁, v₁, u₁} k.hom
      Φ).FaithfullyFlat) :
    IsZero ((((Stacks.sheafModuleFiberOfCommRing Φ D).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (baseChangedCotangentComplex.{u₁, v₁, w₁} J g k)).homology (-1)) ↔
      Subsingleton (@Algebra.H1Cotangent _ (pointStalkAlgebra.{u₁, v₁, w₁} J Φ g) _ _
        (CommAlgCat.algebra _)) := by
  have e₁ := HomologicalComplex.homologyMapIso
    (stalkBaseChangedCotangentComplexIso.{u₁, v₁, w₁} Φ g k) (-1)
  have e₂ := ModuleCat.extendScalarsHomologyIso _ hff.flat
    (((Stacks.sheafModuleFiberOfCommRing Φ R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (cotangentComplex.{u₁, v₁, w₁} J g)) (-1)
  have e₃ := HomologicalComplex.homologyMapIso (pointStalkCotangentComplexIso.{u₁, v₁, w₁} J Φ g)
    (-1) ≪≫ Stacks.Cotangent.cotangentComplexHomologyNegOneIsoH1Cotangent _ _
  exact ⟨fun hz ↦ ModuleCat.isZero_iff_subsingleton.mp
      ((ModuleCat.isZero_of_isZero_extendScalars _ hff _
        ((hz.of_iso e₁.symm).of_iso e₂.symm)).of_iso e₃.symm),
    fun hs ↦ (((ModuleCat.extendScalars _).map_isZero
      ((ModuleCat.isZero_iff_subsingleton.mpr hs).of_iso e₃)).of_iso e₂).of_iso e₁⟩

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The inverse-image form of `f♯` on the image of a section under the unit of
`f⁻¹ ⊣ f_*`** is the pullback of that section along `f`: on an open `V` of `Y`, the inverse-image
structure map `f⁻¹𝒪_Y ⟶ 𝒪_X` of the Zariski ringed topoi sends the image under the unit of a
function `b` on `V` to `f^♯ b` on `f⁻¹V`. -/
theorem fSharpInverseImage_app_zariskiInverseImageAdjunction_unit (V : Y.Opens) (b : Γ(Y, V)) :
    (zariskiRingedToposHom f).fSharpInverseImage.hom.app (op (f ⁻¹ᵁ V))
        ((((zariskiInverseImageAdjunction f).homEquiv _ _ (𝟙 _)).hom.app (op V)) b) =
      f.app V b := by
  let JY := Opens.grothendieckTopology Y
  let JX := Opens.grothendieckTopology X
  let adj := commRingImageAdjunction (zariskiRingedToposHom f).toToposHom
  let rN := restrictionCommRingNatIso JY JX (Opens.map f.base)
  have key : (adj.ofNatIsoRight rN).homEquiv Y.zariskiRingedTopos.O _ (𝟙 _) ≫
      ((Opens.map f.base).sheafPushforwardContinuous CommRingCat.{u} JY JX).map
        (zariskiRingedToposHom f).fSharpInverseImage = zariskiSharp f := by
    refine ((adj.ofNatIsoRight rN).homEquiv_naturality_right (𝟙 _)
      (zariskiRingedToposHom f).fSharpInverseImage).symm.trans ?_
    refine (congrArg _ (Category.id_comp _)).trans ?_
    refine (Adjunction.homEquiv_ofNatIsoRight_apply adj rN _).trans ?_
    refine (congrArg (· ≫ rN.hom.app X.sheaf) (Equiv.apply_symm_apply _ _)).trans ?_
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
      (restrictionCommRingIso JY JX (Opens.map f.base) X.sheaf).inv_hom_id).trans
        (Category.comp_id _))
  exact ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg InducedCategory.Hom.hom key)
    (op V)) b

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {T₁ T₂ : BigFppfOver B S hS} (h : T₁ ⟶ T₂)

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  CategoryTheory.Sheaf.hasSheafifyAddCommGrpCat
  CategoryTheory.Sheaf.wEqualsLocallyBijectiveAddCommGrpCat

/-- `H⁻¹` of the cotangent complex of a morphism of represented algebraic spaces is `H⁻¹` of
`ε^*L_{X₀/Y₀} = L_{ε⁻¹𝒪_{X₀}/ε⁻¹f₀⁻¹𝒪_{Y₀}} ⊗ 𝒪_X`. -/
theorem isZero_homology_negOne_cotangentComplex_representedSpaceMap_iff_baseChanged :
    IsZero ((cotangentComplex B S hS (representedSpaceMap B S hS h)).homology (-1)) ↔
      IsZero ((Sheaf.baseChangedCotangentComplex.{u + 1, u, u}
        (SmallEtale.topology B S hS (yoneda.obj T₁))
        (representedInverseImageStructureMap B S hS h)
        (representedToZariskiRingedToposHom B S hS T₁).fSharpInverseImage).homology (-1)) := by
  have := quasiIso_representedCotangentComparison B S hS h
  exact ((asIso (HomologicalComplex.homologyMap
    (representedCotangentComparison B S hS h) (-1))).symm ≪≫
      HomologicalComplex.homologyMapIso
        (representedPulledBackCotangentComplexIso B S hS h) (-1)).isZero_iff

/-- The point of the small étale site of the represented algebraic space attached to a
geometric point, with fibres in the universe of the coefficients. -/
noncomputable abbrev representedSitePoint (xb : GeometricPoint B S hS (yoneda.obj T₁)) :
    (SmallEtale.topology B S hS (yoneda.obj T₁)).Point.{u + 1} :=
  (etaleSitePoint B S hS (yoneda.obj T₁) xb (isAlgebraicSpace_yoneda B S hS T₁)).ulift.{u + 1}

/-- A cohomology sheaf of a complex of `𝒪_X`-modules on a represented algebraic space vanishes
exactly when the corresponding cohomology of every stalk complex at a geometric point does. -/
theorem isZero_homology_iff_forall_representedSitePoint
    (K : CochainComplex (smallEtaleModulesULift B S hS
      ⟨yoneda.obj T₁, isAlgebraicSpace_yoneda B S hS T₁⟩) ℤ) (i : ℤ) :
    IsZero (K.homology i) ↔ ∀ xb : GeometricPoint B S hS (yoneda.obj T₁),
      IsZero ((((Stacks.sheafModuleFiberOfCommRing (representedSitePoint B S hS xb)
        (smallEtaleStructureSheafULift B S hS
          ⟨yoneda.obj T₁, isAlgebraicSpace_yoneda B S hS T₁⟩)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K).homology i) := by
  let := hasSheafify_smallEtaleRingedTopos B S hS
    ⟨yoneda.obj T₁, isAlgebraicSpace_yoneda B S hS T₁⟩
  let := wEqualsLocallyBijective_smallEtaleRingedTopos B S hS
    ⟨yoneda.obj T₁, isAlgebraicSpace_yoneda B S hS T₁⟩
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  refine (Stacks.exactAt_iff_forall_exactAt_mapSheafModuleFiberOfCommRing
    (smallEtaleStructureSheafULift B S hS ⟨yoneda.obj T₁, isAlgebraicSpace_yoneda B S hS T₁⟩) K
    (isConservativeFamilyOfPoints_uliftEtaleSitePoint B S hS (yoneda.obj T₁)
      (isAlgebraicSpace_yoneda B S hS T₁)) i).trans ?_
  exact ⟨fun hK xb ↦ (HomologicalComplex.exactAt_iff_isZero_homology _ i).mp (hK ⟨_, ⟨xb⟩⟩),
    fun hK ⟨_, ⟨xb⟩⟩ ↦ (HomologicalComplex.exactAt_iff_isZero_homology _ i).mpr (hK xb)⟩

/-- **The stalk of `ε♯` at a geometric point is faithfully flat**: it is a strict
henselization (`AlgebraicGeometry.Space.representedToZariskiRingedToposHom_stalk_isHenselization`),
up to ring isomorphisms of source and target. -/
theorem faithfullyFlat_stalkRingHom_representedToZariskiRingedToposHom
    (xb : GeometricPoint B S hS (yoneda.obj T₁)) :
    (Stacks.SitePointBaseChange.stalkRingHom.{u + 1, u, u + 1}
      (representedToZariskiRingedToposHom B S hS T₁).fSharpInverseImage.hom
      (representedSitePoint B S hS xb)).FaithfullyFlat := by
  obtain ⟨A₀, A, _, _, _, _, _, L, _, _, hH, e₀, e, he⟩ :=
    representedToZariskiRingedToposHom_stalk_isHenselization B S hS T₁ xb
  have hfac : Stacks.SitePointBaseChange.stalkRingHom.{u + 1, u, u + 1}
      (representedToZariskiRingedToposHom B S hS T₁).fSharpInverseImage.hom
      (representedSitePoint B S hS xb) =
      e.symm.toRingHom.comp ((algebraMap A₀ A).comp e₀.toRingHom) := by
    ext y
    exact e.injective ((he y).trans (e.apply_symm_apply _).symm)
  rw [hfac]
  exact RingHom.FaithfullyFlat.stableUnderComposition _ _
    (RingHom.FaithfullyFlat.stableUnderComposition _ _
      (RingHom.FaithfullyFlat.of_bijective e₀.bijective)
      (RingHom.faithfullyFlat_algebraMap_iff.mpr
        (IsLocalRing.IsHenselization.faithfullyFlat (L := L))))
    (RingHom.FaithfullyFlat.of_bijective e.symm.bijective)

/-- **`H⁻¹` of the cotangent complex of a morphism of represented algebraic spaces, read at the
geometric points.** `H⁻¹(L_{X/Y})` vanishes exactly when, at every geometric point of `X`, `H¹` of
the naive cotangent complex of the stalk ring map of `ε⁻¹f₀⁻¹𝒪_{Y₀} ⟶ ε⁻¹𝒪_{X₀}` vanishes. -/
theorem isZero_homology_negOne_cotangentComplex_representedSpaceMap_iff_forall :
    IsZero ((cotangentComplex B S hS (representedSpaceMap B S hS h)).homology (-1)) ↔
      ∀ xb : GeometricPoint B S hS (yoneda.obj T₁),
        Subsingleton (@Algebra.H1Cotangent _ (Sheaf.pointStalkAlgebra.{u + 1, u, u}
          (SmallEtale.topology B S hS (yoneda.obj T₁)) (representedSitePoint B S hS xb)
          (representedInverseImageStructureMap B S hS h)) _ _ (CommAlgCat.algebra _)) := by
  let := hasSheafify_smallEtaleRingedTopos B S hS
    ⟨yoneda.obj T₁, isAlgebraicSpace_yoneda B S hS T₁⟩
  let := wEqualsLocallyBijective_smallEtaleRingedTopos B S hS
    ⟨yoneda.obj T₁, isAlgebraicSpace_yoneda B S hS T₁⟩
  refine
    (isZero_homology_negOne_cotangentComplex_representedSpaceMap_iff_baseChanged B S hS h).trans
    ((isZero_homology_iff_forall_representedSitePoint B S hS _ (-1)).trans
      (forall_congr' fun xb ↦ ?_))
  exact Sheaf.isZero_homology_negOne_stalk_baseChangedCotangentComplex_iff
    (representedSitePoint B S hS xb) _ _
    (faithfullyFlat_stalkRingHom_representedToZariskiRingedToposHom B S hS xb)

/-- **The comparison map to `ε⁻¹` is natural in the sheaf.** -/
theorem representedImageRestrictionToInverseImage_naturality (T : BigFppfOver B S hS)
    {M M' : Sheaf (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T))
      CommRingCat.{u + 1}} (β : M ⟶ M') :
    representedImageRestrictionToInverseImage B S hS T M ≫
        ((inverseImageCommRingFunctor (representedToZariskiMorphismOfTopoi B S hS T)).map β).hom =
      Functor.whiskerLeft (representedImageOpenFunctor B S hS T).op β.hom ≫
        representedImageRestrictionToInverseImage B S hS T M' := by
  let ε := representedToZariskiMorphismOfTopoi B S hS T
  let adj := commRingImageAdjunction ε
  rw [representedImageRestrictionToInverseImage_comp]
  have h₁ : adj.homEquiv M _ ((inverseImageCommRingFunctor ε).map β) =
      β ≫ adj.unit.app M' := by
    rw [← Category.comp_id ((inverseImageCommRingFunctor ε).map β),
      Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_id]
  rw [h₁]
  exact (representedRestrictionAdjunction B S hS T).homEquiv_naturality_left_symm β.hom
    ((adj.unit.app M' ≫ (restrictionCommRingIso
      (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T))
      (SmallEtale.topology B S hS (yoneda.obj T)) (representedOpensToSmallEtale B S hS T)
      ((inverseImageCommRingFunctor ε).obj M')).hom).hom)

/-- **The stalk of `ε⁻¹f₀⁻¹𝒪_{Y₀} ⟶ ε⁻¹𝒪_{X₀}` on germs**: read through the identifications of
the two stalks with `𝒪_{Y₀, f₀ x}` and `𝒪_{X₀, x}` (Stacks 05V1), it is the stalk map of `f₀` at
`x`. -/
theorem representedInverseImageStalkIso_stalk_structureMap_germ
    (xb : GeometricPoint B S hS (yoneda.obj T₁))
    (V : ((BigFppfOver.toScheme B S hS).obj T₂).Opens)
    (hy : (BigFppfOver.toScheme B S hS).map h
      (chartPoint B S hS (yoneda.obj T₁) (yonedaIdentityNeighborhood T₁ xb)) ∈ V)
    (b : Γ((BigFppfOver.toScheme B S hS).obj T₂, V)) :
    (representedInverseImageStalkIso B S hS T₁ xb ((BigFppfOver.toScheme B S hS).obj T₁).sheaf).hom
      ((((etaleSitePoint B S hS (yoneda.obj T₁) xb
        (isAlgebraicSpace_yoneda B S hS T₁)).ulift.{u + 1}).presheafFiber
          (A := CommRingCat.{u + 1})).map (representedInverseImageStructureMap B S hS h).hom
        (representedBaseMapSourceGerm B S hS h xb V hy b)) =
      ULift.up (((BigFppfOver.toScheme B S hS).map h).stalkMap
        (chartPoint B S hS (yoneda.obj T₁) (yonedaIdentityNeighborhood T₁ xb))
        (TopCat.Presheaf.germ (X := ((BigFppfOver.toScheme B S hS).obj T₂).toTopCat)
          ((BigFppfOver.toScheme B S hS).obj T₂).presheaf V _ hy b)) := by
  let f₀ := (BigFppfOver.toScheme B S hS).map h
  let Φ₀ := etaleSitePoint B S hS (yoneda.obj T₁) xb (isAlgebraicSpace_yoneda B S hS T₁)
  let Φ := Φ₀.ulift.{u + 1}
  let G₁ := representedImageOpenFunctor B S hS T₁
  let x := chartPoint B S hS (yoneda.obj T₁) (yonedaIdentityNeighborhood T₁ xb)
  let N := (inverseImageCommRingFunctor (Scheme.Hom.zariskiRingedToposHom f₀).toToposHom).obj
    ((BigFppfOver.toScheme B S hS).obj T₂).zariskiRingedTopos.O
  let L := sheafCompose (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁))
    SheafOfModules.commRingCatULift.{u, u + 1}
  let M := L.obj N
  let O₁ := ((BigFppfOver.toScheme B S hS).obj T₁).sheaf
  let α := (Scheme.Hom.zariskiRingedToposHom f₀).fSharpInverseImage
  let unitZ := (Scheme.Hom.zariskiInverseImageAdjunction f₀).homEquiv
    ((BigFppfOver.toScheme B S hS).obj T₂).zariskiRingedTopos.O N (𝟙 N)
  let W := f₀ ⁻¹ᵁ V
  let Nx := chartOpenNeighborhood B S hS (yonedaIdentityNeighborhood T₁ xb) W hy
  let U := (representedOpensToSmallEtale B S hS T₁).obj W
  let s : Φ₀.fiber.obj U := ⟨Nx.point, Nx.point_comp⟩
  let res : G₁.obj U ⟶ W := (representedImageOpenAdjunction B S hS T₁).counit.app W
  let c' := N.obj.map res.op (unitZ.hom.app (op V) b)
  -- the stalk of the structure map on the germ
  have h1 : ((Φ.presheafFiber (A := CommRingCat.{u + 1})).map
      (representedInverseImageStructureMap B S hS h).hom
        (representedBaseMapSourceGerm B S hS h xb V hy b)) =
      (Φ.presheafFiber (A := CommRingCat.{u + 1})).map
        (representedImageRestrictionToInverseImage B S hS T₁ (L.obj O₁))
        (Φ.toPresheafFiber U (ULift.up s) (G₁.op ⋙ (L.obj O₁).obj)
          (ULift.up (α.hom.app (op (G₁.obj U)) c'))) := by
    refine (ConcreteCategory.congr_hom
      ((Φ.presheafFiber (A := CommRingCat.{u + 1})).map_comp
        (representedImageRestrictionToInverseImage B S hS T₁ M)
        ((inverseImageCommRingFunctor (representedToZariskiMorphismOfTopoi B S hS T₁)).map
          (L.map α)).hom).symm
      (Φ.toPresheafFiber U (ULift.up s) (G₁.op ⋙ M.obj) (ULift.up c'))).trans ?_
    rw [representedImageRestrictionToInverseImage_naturality B S hS T₁ (L.map α),
      Functor.map_comp]
    refine (ConcreteCategory.comp_apply _ _ _).trans (congrArg _ ?_)
    exact Φ.toPresheafFiber_naturality_apply (A := CommRingCat.{u + 1})
      (Functor.whiskerLeft G₁.op (L.map α).hom) U (ULift.up s) (ULift.up c')
  have h3 : α.hom.app (op (G₁.obj U)) c' =
      O₁.obj.map res.op (α.hom.app (op W) (unitZ.hom.app (op V) b)) :=
    ConcreteCategory.congr_hom (α.hom.naturality res.op) (unitZ.hom.app (op V) b)
  rw [h1]
  refine (ConcreteCategory.congr_hom (representedInverseImageStalkIso_germ B S hS T₁ xb O₁ U s)
    (ULift.up (α.hom.app (op (G₁.obj U)) c'))).trans (congrArg ULift.up ?_)
  rw [h3, Scheme.Hom.fSharpInverseImage_app_zariskiInverseImageAdjunction_unit f₀ V b]
  refine (TopCat.Presheaf.germ_res_apply (X := ((BigFppfOver.toScheme B S hS).obj T₁).toTopCat)
    O₁.obj res x (chartPoint_yonedaIdentityNeighborhood_mem B S hS T₁ xb U s) (f₀.app V b)).trans ?_
  exact (Scheme.Hom.germ_stalkMap_apply f₀ V x hy b).symm

/-- Every element of the stalk of `ε⁻¹f₀⁻¹𝒪_{Y₀}` at the point attached to `x̄` is the germ
of a function on an open of `Y₀` containing the image point. -/
theorem exists_representedBaseMapSourceGerm_eq (xb : GeometricPoint B S hS (yoneda.obj T₁))
    (r : (((etaleSitePoint B S hS (yoneda.obj T₁) xb
      (isAlgebraicSpace_yoneda B S hS T₁)).ulift.{u + 1}).presheafFiber
        (A := CommRingCat.{u + 1})).obj
      ((representedToZariskiRingedToposHom B S hS T₁).toToposHom.inverseImageRing.obj
        ((sheafCompose (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁))
          SheafOfModules.commRingCatULift.{u, u + 1}).obj
          ((inverseImageCommRingFunctor (Scheme.Hom.zariskiRingedToposHom
            ((BigFppfOver.toScheme B S hS).map h)).toToposHom).obj
            ((BigFppfOver.toScheme B S hS).obj T₂).zariskiRingedTopos.O))).obj) :
    ∃ (V : ((BigFppfOver.toScheme B S hS).obj T₂).Opens)
      (hy : (BigFppfOver.toScheme B S hS).map h
        (chartPoint B S hS (yoneda.obj T₁) (yonedaIdentityNeighborhood T₁ xb)) ∈ V)
      (b : Γ((BigFppfOver.toScheme B S hS).obj T₂, V)),
      representedBaseMapSourceGerm B S hS h xb V hy b = r := by
  obtain ⟨V, hy, b, hb⟩ := TopCat.Presheaf.exists_germ_eq
    (X := ((BigFppfOver.toScheme B S hS).obj T₂).toTopCat)
    ((BigFppfOver.toScheme B S hS).obj T₂).presheaf (x := (BigFppfOver.toScheme B S hS).map h
        (chartPoint B S hS (yoneda.obj T₁) (yonedaIdentityNeighborhood T₁ xb)))
    (representedBaseMapSourceStalkEquiv B S hS h xb r).down
  refine ⟨V, hy, b, (representedBaseMapSourceStalkEquiv B S hS h xb).injective ?_⟩
  rw [representedBaseMapSourceStalkEquiv_germ]
  exact congrArg ULift.up hb

/-- The stalk of `ε⁻¹f₀⁻¹𝒪_{Y₀} ⟶ ε⁻¹𝒪_{X₀}` at the point attached to `x̄`, read through the
identifications of Stacks 05V1 of its source and target with `𝒪_{Y₀, f₀ x}` and `𝒪_{X₀, x}`, is the
stalk map of `f₀` at `x`. -/
theorem representedInverseImageStalkIso_stalk_structureMap
    (xb : GeometricPoint B S hS (yoneda.obj T₁))
    (r : (((etaleSitePoint B S hS (yoneda.obj T₁) xb
      (isAlgebraicSpace_yoneda B S hS T₁)).ulift.{u + 1}).presheafFiber
        (A := CommRingCat.{u + 1})).obj
      ((representedToZariskiRingedToposHom B S hS T₁).toToposHom.inverseImageRing.obj
        ((sheafCompose (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁))
          SheafOfModules.commRingCatULift.{u, u + 1}).obj
          ((inverseImageCommRingFunctor (Scheme.Hom.zariskiRingedToposHom
            ((BigFppfOver.toScheme B S hS).map h)).toToposHom).obj
            ((BigFppfOver.toScheme B S hS).obj T₂).zariskiRingedTopos.O))).obj) :
    ((representedInverseImageStalkIso B S hS T₁ xb ((BigFppfOver.toScheme B S hS).obj T₁).sheaf).hom
      ((((etaleSitePoint B S hS (yoneda.obj T₁) xb
        (isAlgebraicSpace_yoneda B S hS T₁)).ulift.{u + 1}).presheafFiber
          (A := CommRingCat.{u + 1})).map (representedInverseImageStructureMap B S hS h).hom
        r)).down =
      ((BigFppfOver.toScheme B S hS).map h).stalkMap
        (chartPoint B S hS (yoneda.obj T₁) (yonedaIdentityNeighborhood T₁ xb))
        (representedBaseMapSourceStalkEquiv B S hS h xb r).down := by
  obtain ⟨V, hy, b, rfl⟩ := exists_representedBaseMapSourceGerm_eq B S hS h xb r
  refine (congrArg ULift.down
    (representedInverseImageStalkIso_stalk_structureMap_germ B S hS h xb V hy b)).trans ?_
  rw [representedBaseMapSourceStalkEquiv_germ]

/-- **`H¹` at a geometric point is `H¹` of the stalk map of `f₀` at the point under it.** The
stalk ring map of `ε⁻¹f₀⁻¹𝒪_{Y₀} ⟶ ε⁻¹𝒪_{X₀}` at the point attached to `x̄` is, up to the ring
isomorphisms of Stacks 05V1, the stalk map `𝒪_{Y₀, f₀ x} → 𝒪_{X₀, x}` of `f₀` at the point `x` of
`X₀` under `x̄`, so the two have the same `H¹` of the naive cotangent complex. -/
theorem subsingleton_h1Cotangent_pointStalkAlgebra_iff
    (xb : GeometricPoint B S hS (yoneda.obj T₁)) :
    Subsingleton (@Algebra.H1Cotangent _ (Sheaf.pointStalkAlgebra.{u + 1, u, u}
        (SmallEtale.topology B S hS (yoneda.obj T₁)) (representedSitePoint B S hS xb)
        (representedInverseImageStructureMap B S hS h)) _ _ (CommAlgCat.algebra _)) ↔
      letI := (((BigFppfOver.toScheme B S hS).map h).stalkMap
        (chartPoint B S hS (yoneda.obj T₁) (yonedaIdentityNeighborhood T₁ xb))).hom.toAlgebra
      Subsingleton (Algebra.H1Cotangent
        (((BigFppfOver.toScheme B S hS).obj T₂).presheaf.stalk ((BigFppfOver.toScheme B S hS).map h
          (chartPoint B S hS (yoneda.obj T₁) (yonedaIdentityNeighborhood T₁ xb))))
        (((BigFppfOver.toScheme B S hS).obj T₁).presheaf.stalk
          (chartPoint B S hS (yoneda.obj T₁) (yonedaIdentityNeighborhood T₁ xb)))) := by
  let := (((BigFppfOver.toScheme B S hS).map h).stalkMap
    (chartPoint B S hS (yoneda.obj T₁) (yonedaIdentityNeighborhood T₁ xb))).hom.toAlgebra
  let eR := (representedBaseMapSourceStalkEquiv B S hS h xb).trans ULift.ringEquiv
  let eS := (representedInverseImageStalkIso B S hS T₁ xb
    ((BigFppfOver.toScheme B S hS).obj T₁).sheaf).commRingCatIsoToRingEquiv.trans ULift.ringEquiv
  exact @Algebra.subsingleton_h1Cotangent_iff_of_ringEquiv _ _ _ _ _ _ _ _ (CommAlgCat.algebra _) _
    eR eS (representedInverseImageStalkIso_stalk_structureMap B S hS h xb)

/-- **Every point of a scheme of the site lies under a geometric point** of the algebraic space
it represents, as the point of the identity chart attached to that geometric point. -/
theorem exists_chartPoint_yonedaIdentityNeighborhood_eq (T : BigFppfOver B S hS)
    (z : (BigFppfOver.toScheme B S hS).obj T) :
    ∃ xb : GeometricPoint B S hS (yoneda.obj T),
      chartPoint B S hS (yoneda.obj T) (yonedaIdentityNeighborhood T xb) = z := by
  obtain ⟨xb, ξ, hξ, z', hz⟩ := exists_geometricPoint_hom_of_point B S hS T (𝟙 _) z
  refine ⟨xb, ?_⟩
  obtain rfl : ξ = xb.val.value := hξ
  rw [← hz]
  exact congrArg _ (Subsingleton.elim _ _)

/-- **Vanishing of `H⁻¹(L_{X/Y})` for a morphism of represented algebraic spaces, on the local
rings of the schemes.** For a morphism `h` of the big fppf site of `S` with underlying morphism
of schemes `f₀ : X₀ ⟶ Y₀`, the cohomology sheaf `H⁻¹` of the cotangent complex of the morphism
of algebraic spaces `yoneda h` vanishes exactly when `H¹` of the naive cotangent complex of every
stalk map `𝒪_{Y₀, f₀ x} → 𝒪_{X₀, x}` does. -/
theorem isZero_homology_negOne_cotangentComplex_representedSpaceMap_iff_stalkMap :
    IsZero ((cotangentComplex B S hS (representedSpaceMap B S hS h)).homology (-1)) ↔
      ∀ x : (BigFppfOver.toScheme B S hS).obj T₁,
        letI := (((BigFppfOver.toScheme B S hS).map h).stalkMap x).hom.toAlgebra
        Subsingleton (Algebra.H1Cotangent
          (((BigFppfOver.toScheme B S hS).obj T₂).presheaf.stalk
            ((BigFppfOver.toScheme B S hS).map h x))
          (((BigFppfOver.toScheme B S hS).obj T₁).presheaf.stalk x)) := by
  refine (isZero_homology_negOne_cotangentComplex_representedSpaceMap_iff_forall B S hS h).trans
    ⟨fun H x ↦ ?_, fun H xb ↦ (subsingleton_h1Cotangent_pointStalkAlgebra_iff B S hS h xb).2
      (H _)⟩
  obtain ⟨xb, rfl⟩ := exists_chartPoint_yonedaIdentityNeighborhood_eq B S hS T₁ x
  exact (subsingleton_h1Cotangent_pointStalkAlgebra_iff B S hS h xb).1 (H xb)

end AlgebraicGeometry.Space

end
