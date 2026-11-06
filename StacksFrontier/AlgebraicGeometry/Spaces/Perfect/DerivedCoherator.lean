module

public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.DerivedAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedCoheratorAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPushforwardQuasicoherent
public import StacksFrontier.CategoryTheory.Triangulated.AdmissibleSubcategories

/-!
# The coherator `DQ_X` of a quasi-compact quasi-separated algebraic space

Let `X` be a quasi-compact and quasi-separated algebraic space over a scheme `S`.  Stacks 0CR4
asserts that the inclusion `D_QCoh(𝒪_X) ⥤ D(𝒪_X)` has a right adjoint, written `DQ_X` in the
source.  This file proves it by the source's first proof:

* by Stacks 0CQS the right adjoint exists if and only if every object `K` of `D(𝒪_X)` sits in a
  distinguished triangle `E' ⟶ K ⟶ Q ⟶ E'[1]` with `E'` in `D_QCoh(𝒪_X)` and `Q` right orthogonal
  to `D_QCoh(𝒪_X)`, and by Stacks 0CQR such objects form a triangulated subcategory;
* for an étale `j : Y ⟶ W` such that the coherator of `Y` exists and `Rj_*` preserves
  quasi-coherent cohomology, `Rj_*L` is of that form for every `L`: push forward the triangle of
  `L`, and use `Hom(M, Rj_*Q) = Hom(j^*M, Q) = 0` for `M` in `D_QCoh(𝒪_W)` (Stacks 08F4);
* across an elementary distinguished square the three vertices of the Mayer–Vietoris triangle of
  Stacks 08GW are of that form, and so is the object itself;
* the induction principle of Stacks 08GP, from the affine case of
  `StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedCoheratorAffine`, gives the statement for
  `X`.

The quasi-coherence of the derived direct images along the three étale morphisms of a square is
`AlgebraicGeometry.Space.exists_derivedPushforwardQuasicoherentBounded`.

## Main results

All in the namespace `AlgebraicGeometry.Space`.

* `extensionProduct_derivedPushforward_of_isEtale`: the étale step.
* `isLeftAdjoint_ι_of_elementaryDistinguishedSquare`: the inductive step.
* `isLeftAdjoint_ι_of_forall_isAffineSpace`: the induction, granted the affine case.
* `isLeftAdjoint_ι_derivedCategoryB_isQuasicoherentOnSite`: **Stacks 0CR4**, at every model of
  `D(𝒪_X)`.
* `exists_isTriangulated_rightAdjoint_ι_derivedCategoryB_isQuasicoherentOnSite`: the same, with
  the coherator exhibited as an exact functor.

## References

* [Stacks Project, Tag 0CR4](https://stacks.math.columbia.edu/tag/0CR4)
* [Stacks Project, Tag 0CQS](https://stacks.math.columbia.edu/tag/0CQS)
* [Stacks Project, Tag 0CQR](https://stacks.math.columbia.edu/tag/0CQR)
* [Stacks Project, Tag 08GW](https://stacks.math.columbia.edu/tag/08GW)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Tag 08F4](https://stacks.math.columbia.edu/tag/08F4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.ObjectProperty
open Stacks.SheafOfModules.Tensor (ringSheaf)
open CategoryTheory.PushforwardMayerVietoris

attribute [local instance 5000] SheafOfModules.instAbelian

universe w u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] isGrothendieckAbelian_modules
attribute [local instance] enoughInjectives_modules
attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

/-- The derived direct image `Rj_*` of a morphism has a shift commutation making it exact. -/
private theorem exists_commShift_isTriangulated {Y W : AlgebraicSpaces B S hS} (j : Y ⟶ W)
    (Rj : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (αj : (modulePushforward B S hS j).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rj)
    [Rj.IsRightDerivedFunctor αj
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ))] :
    ∃ _ : Rj.CommShift ℤ, Rj.IsTriangulated :=
  ⟨Functor.IsRightDerivedFunctor.commShift Rj αj
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ)) ℤ,
    Stacks.Perfect.CechAugmentation.isTriangulated_of_isRightDerivedFunctor
      (modulePushforward B S hS j) Rj αj⟩

section EtaleStep

variable {Y W : AlgebraicSpaces B S hS} (j : Y ⟶ W) (hj : IsEtale B S hS j.hom)
  (Rj : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤
    DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
  (αj : (modulePushforward B S hS j).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rj)
  [Rj.IsRightDerivedFunctor αj
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ))]

include hj αj in
/-- For an étale `j : Y ⟶ W`, the derived direct image carries the right orthogonal of
`D_QCoh(𝒪_Y)` into the right orthogonal of `D_QCoh(𝒪_W)`: a morphism `M ⟶ Rj_*Q` corresponds
under `j^* ⊣ Rj_*` to a morphism `j^*M ⟶ Q`, and `j^*M` has quasi-coherent cohomology
(Stacks 08F4). -/
theorem rightOrthogonal_derivedPushforward_of_isEtale
    (Q : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (hQ : (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).rightOrthogonal Q) :
    (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O))).rightOrthogonal (Rj.obj Q) := by
  intro M g hM
  obtain ⟨_, _⟩ := exists_commShift_isTriangulated B S hS j Rj αj
  let adj := Stacks.DerivedFunctor.derivedAdjunction (etaleModulePullbackAdjunction B S hS j hj)
    Rj αj (exists_quasiIso_isKInjective_modules B S hS Y.1 Y.2)
  have h0 : (adj.homEquiv M Q).symm g = 0 :=
    hQ _ (derivedQuasicoherent_etaleModulePullback B S hS j hj M hM)
  rw [← (adj.homEquiv M Q).apply_symm_apply g, h0, Adjunction.homEquiv_unit,
    Functor.map_zero, comp_zero]

include hj αj in
/-- **The étale step of the first proof of Stacks 0CR4.**  If `D_QCoh(𝒪_Y) ⥤ D(𝒪_Y)` has a right
adjoint and `Rj_*` carries `D_QCoh(𝒪_Y)` into `D_QCoh(𝒪_W)`, then `Rj_*L` is an extension of an
object right orthogonal to `D_QCoh(𝒪_W)` by an object of `D_QCoh(𝒪_W)`, for every `L`. -/
theorem extensionProduct_derivedPushforward_of_isEtale
    (hY : (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).ι.IsLeftAdjoint)
    (hqc : ∀ E : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2),
      DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)) E →
      DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)) (Rj.obj E))
    (L : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)) :
    (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O))).extensionProduct
      (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O))).rightOrthogonal (Rj.obj L) := by
  have hL : (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).extensionProduct
      (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).rightOrthogonal L := by
    rw [((isLeftAdjoint_ι_iff_extensionProduct_rightOrthogonal_eq_top_and_isSaturated _).1).1 hY]
    trivial
  obtain ⟨E, Q, f, g, h, hTr, hE, hQ⟩ := hL
  obtain ⟨_, _⟩ := exists_commShift_isTriangulated B S hS j Rj αj
  exact ⟨_, _, _, _, _, Rj.map_distinguished _ hTr, hqc E hE,
    rightOrthogonal_derivedPushforward_of_isEtale B S hS j hj Rj αj Q hQ⟩

end EtaleStep

/-- `R(j_*((-)|_Y))` is `Rj_*` after restriction, on objects. -/
theorem nonempty_restrictPush_obj_iso {Y W : AlgebraicSpaces B S hS} (j : Y ⟶ W)
    (hj : IsEtale B S hS j.hom)
    (R : DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (αR : (etaleModulePullback.{u, u} B S hS j hj ⋙ modulePushforward B S hS j).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ R)
    [R.IsRightDerivedFunctor αR
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))]
    (Rj : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (αj : (modulePushforward B S hS j).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rj)
    [Rj.IsRightDerivedFunctor αj
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ))]
    (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) :
    Nonempty (R.obj E ≅
      Rj.obj ((etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategory.obj E)) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := exists_isKInjective_representative_of_universe
    (exists_quasiIso_isKInjective_modules B S hS W.1 W.2) E
  have hjI := isKInjective_etaleModulePullback_mapHomologicalComplex B S hS j hj I hI
  let K := ((etaleModulePullback.{u, u} B S hS j hj).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj I
  have e₁ : R.obj (DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj (((modulePushforward B S hS j).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) :=
    (rightDerivedObjIsoOfKInjective
      (exists_quasiIso_isKInjective_modules B S hS W.1 W.2)
      (etaleModulePullback.{u, u} B S hS j hj ⋙ modulePushforward B S hS j) inferInstance
      R αR inferInstance I hI).symm
  have e₂ : DerivedCategory.Q.obj (((modulePushforward B S hS j).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) ≅ Rj.obj (DerivedCategory.Q.obj K) :=
    derivedPushforwardObjIsoOfIsKInjective B S hS j Rj αj K hjI
  have e₃ : DerivedCategory.Q.obj K ≅
      (etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategory.obj E :=
    ((etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategoryFactors.app I).symm ≪≫
      (etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategory.mapIso e
  exact ⟨R.mapIso e.symm ≪≫ e₁ ≪≫ e₂ ≪≫ Rj.mapIso e₃⟩

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_DerivedCoherator :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Limits of cospans of presheaves on the big fppf site, found directly. -/
local instance (priority := high) hasPullback_presheaf_DerivedCoherator
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- An open subspace of an absolutely quasi-separated algebraic space is absolutely
quasi-separated. -/
theorem isAbsolutelyQuasiSeparated_of_isOpenSubspace (hZ : B.Contains (⊤_ Scheme.{u}))
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hFqs : IsAbsolutelyQuasiSeparated B S hS hZ F)
    (U : Subfunctor F) (hU : IsOpenSubspace B S hS U) :
    IsAbsolutelyQuasiSeparated B S hS hZ U.toFunctor := by
  have hmono : Mono U.ι := inferInstance
  have hqsmor : IsQuasiSeparated B S hS U.ι := by
    intro Z hZalg hZqc g
    have hdiag : IsIso (pullback.diagonal U.ι) :=
      (pullback.isIso_diagonal_iff U.ι).2 hmono
    let : IsIso (pullback.diagonal U.ι) := hdiag
    have hfst : IsIso (pullback.fst g (pullback.diagonal U.ι)) := by infer_instance
    exact IsQuasiCompactSpace.of_iso B S hS hZqc
      (asIso (pullback.fst g (pullback.diagonal U.ι))).symm
  exact isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hU.1 hFqs hqsmor

section Square

attribute [local instance] smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat
  hasRightDerivedFunctor_mapHomotopyCategory_modules hasRightDerivedFunctor_modulePushforward

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- One vertex of the Mayer–Vietoris triangle of Stacks 08GW is decomposable, given the coherator
of the étale space and the quasi-coherence of its derived direct image. -/
theorem extensionProduct_restrictPush {Y : AlgebraicSpaces B S hS} (j : Y ⟶ W)
    (hj : IsEtale B S hS j.hom)
    (hY : (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).ι.IsLeftAdjoint)
    {N : ℤ} (hb : DerivedPushforwardQuasicoherentBounded B S hS j N)
    (R : DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (αR : (etaleModulePullback.{u, u} B S hS j hj ⋙ modulePushforward B S hS j).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ R)
    [R.IsRightDerivedFunctor αR
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))]
    (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) :
    (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O))).extensionProduct
      (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O))).rightOrthogonal (R.obj E) := by
  let Rj := ((modulePushforward B S hS j).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ))
  let αj := ((modulePushforward B S hS j).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ))
  obtain ⟨e⟩ := nonempty_restrictPush_obj_iso B S hS j hj R αR Rj αj E
  exact ObjectProperty.prop_of_iso _ e.symm
    (extensionProduct_derivedPushforward_of_isEtale B S hS j hj Rj αj hY
      (fun E hE => (hb Rj αj inferInstance E hE).1) _)

/-- **The inductive step of the first proof of Stacks 0CR4.**  Across an elementary distinguished
square `(U ⊆ W, V ⟶ W)`, if the coherators of `U`, `V` and `U ×_W V` exist and the derived direct
images along the three étale morphisms preserve quasi-coherence, then the coherator of `W`
exists: every object of `D(𝒪_W)` is decomposable, by the Mayer–Vietoris triangle of Stacks 08GW
and Stacks 0CQR. -/
theorem isLeftAdjoint_ι_of_elementaryDistinguishedSquare
    (hU : (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS (edsOpen B S hS hsq).1
        (edsOpen B S hS hsq).2).O))).ι.IsLeftAdjoint)
    (hV : (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS (edsEtale B S hS hsq).1
        (edsEtale B S hS hsq).2).O))).ι.IsLeftAdjoint)
    (hP : (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS (edsInter B S hS hsq).1
        (edsInter B S hS hsq).2).O))).ι.IsLeftAdjoint)
    {NU NV NP : ℤ}
    (bU : DerivedPushforwardQuasicoherentBounded B S hS (edsOpenHom B S hS hsq) NU)
    (bV : DerivedPushforwardQuasicoherentBounded B S hS (edsEtaleHom B S hS hsq) NV)
    (bP : DerivedPushforwardQuasicoherentBounded B S hS (edsInterHom B S hS hsq) NP) :
    (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O))).ι.IsLeftAdjoint := by
  let QW := DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    (ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O))
  have : (QW.extensionProduct QW.rightOrthogonal).IsTriangulated :=
    isTriangulated_extensionProduct_of_le_rightOrthogonal _ _ le_rfl
  rw [((isLeftAdjoint_ι_iff_extensionProduct_rightOrthogonal_eq_top_and_isSaturated QW).1)]
  rw [eq_top_iff]
  intro E _
  obtain ⟨δ, hT⟩ :=
    exists_mem_distTriang_edsDerivedRestrictPushMayerVietorisLowerShriek B S hS hsq E
  have h₁ := extensionProduct_restrictPush B S hS (edsOpenHom B S hS hsq)
    (isEtale_edsOpenHom B S hS hsq) hU bU (edsDerivedRestrictPushOpen B S hS hsq)
    (edsTotalRightDerivedUnitOpen B S hS hsq) E
  have h₂ := extensionProduct_restrictPush B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq) hV bV (edsDerivedRestrictPushEtale B S hS hsq)
    (edsTotalRightDerivedUnitEtale B S hS hsq) E
  have h₃ := extensionProduct_restrictPush B S hS (edsInterHom B S hS hsq)
    (isEtale_edsInterHom B S hS hsq) hP bP (edsDerivedRestrictPushInter B S hS hsq)
    (edsTotalRightDerivedUnitInter B S hS hsq) E
  have hmid := (QW.extensionProduct QW.rightOrthogonal).ext_of_isTriangulatedClosed₂ _
    (binaryBiproductTriangle_distinguished _ _) h₁ h₂
  exact (QW.extensionProduct QW.rightOrthogonal).ext_of_isTriangulatedClosed₁ _ hT hmid h₃

end Square

/-! ### The induction -/

/-- **The first proof of Stacks 0CR4, granted the affine case.**  If the inclusion
`D_QCoh(𝒪_Y) ⥤ D(𝒪_Y)` has a right adjoint for every affine algebraic space `Y`, then it has one
for every quasi-compact quasi-separated algebraic space `X`: induction on `X` by Stacks 08GP,
with the inductive step
`AlgebraicGeometry.Space.isLeftAdjoint_ι_of_elementaryDistinguishedSquare`. -/
theorem isLeftAdjoint_ι_of_forall_isAffineSpace (hZ : B.Contains (⊤_ Scheme.{u}))
    (haff : ∀ Y : AlgebraicSpaces B S hS, IsAffineSpace B S hS Y.1 →
      (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).ι.IsLeftAdjoint)
    (X : AlgebraicSpaces B S hS) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) :
    (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).ι.IsLeftAdjoint := by
  have key := qcqs_induction_on_self B S hS hZ X hXqc hXqs
    (fun T _ => ∀ hT : IsAlgebraicSpace B S hS T,
      (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS T hT).O))).ι.IsLeftAdjoint)
    (fun V hV hT => haff ⟨V.1.left.1, hT⟩ hV)
    (fun W V U f hf hsq hWqc hWqs hUqc hVa hU hV hP hT => ?_)
  · exact key X.2
  · let W' : AlgebraicSpaces B S hS := ⟨W.1.left.1, hT⟩
    have hsq' : IsElementaryDistinguishedSquare B S hS W'.2 U f := hsq
    have hUqs : IsAbsolutelyQuasiSeparated B S hS hZ U.toFunctor :=
      isAbsolutelyQuasiSeparated_of_isOpenSubspace B S hS hZ hWqs U hsq'.isOpenSubspace
    have hVqc : IsQuasiCompactSpace B S hS V.1.left.1 := hVa.isQuasiCompactSpace
    have hVqs : IsAbsolutelyQuasiSeparated B S hS hZ V.1.left.1 :=
      IsAffineSpace.isAbsolutelyQuasiSeparated B S hS hZ hVa
    have sq₀ : IsPullback (pullback.fst U.ι f) (pullback.snd U.ι f) U.ι f :=
      IsPullback.of_hasPullback _ _
    have hιqc : IsQuasiCompact B S hS U.ι :=
      isQuasiCompact_of_isQuasiCompactSpace B S hS hZ hT hWqs hUqc U.ι
    have hιqs : IsQuasiSeparated B S hS U.ι :=
      isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ hsq'.isOpenSubspace.1
        hUqs U.ι
    have hPqc : IsQuasiCompactSpace B S hS (pullback U.ι f) :=
      isQuasiCompactSpace_of_isQuasiCompact_of_isAffineSpace B S hS (pullback.snd U.ι f) hVa
        (isQuasiCompact_of_isPullback B S hS sq₀ hιqc)
    have hPqs : IsAbsolutelyQuasiSeparated B S hS hZ (pullback U.ι f) :=
      isAbsolutelyQuasiSeparated_of_isQuasiSeparated_of_isAffineSpace B S hS hZ
        (pullback.snd U.ι f) (edsInter B S hS hsq').2 hVa
        (isQuasiSeparated_of_isPullback B S hS sq₀ hιqs)
    obtain ⟨NU, bU⟩ := exists_derivedPushforwardQuasicoherentBounded B S hS hZ
      (Y := edsOpen B S hS hsq') (W := W') hUqc hUqs hWqc hWqs (edsOpenHom B S hS hsq')
    obtain ⟨NV, bV⟩ := exists_derivedPushforwardQuasicoherentBounded B S hS hZ
      (Y := edsEtale B S hS hsq') (W := W') hVqc hVqs hWqc hWqs (edsEtaleHom B S hS hsq')
    obtain ⟨NP, bP⟩ := exists_derivedPushforwardQuasicoherentBounded B S hS hZ
      (Y := edsInter B S hS hsq') (W := W') hPqc hPqs hWqc hWqs (edsInterHom B S hS hsq')
    exact isLeftAdjoint_ι_of_elementaryDistinguishedSquare B S hS hsq'
      (hU (edsOpen B S hS hsq').2) (hV (edsEtale B S hS hsq').2) (hP (edsInter B S hS hsq').2)
      bU bV bP

/-! ### Stacks 0CR4 -/

/-- **Stacks 0CR4.**  Let `S` be a scheme and `X` a quasi-compact and quasi-separated algebraic
space over `S`.  The inclusion functor `D_QCoh(𝒪_X) ⥤ D(𝒪_X)` has a right adjoint, the coherator
`DQ_X`.

This is the source's first proof: the induction principle of Stacks 08GP
(`AlgebraicGeometry.Space.isLeftAdjoint_ι_of_forall_isAffineSpace`) from the affine case
(`AlgebraicGeometry.Space.isLeftAdjoint_ι_of_isAffineSpace`).  The statement holds at every model
of the derived category `D(𝒪_X)`, by the model comparison
`StacksDraft.DerivedModel.isLeftAdjoint_ι_derivedCategoryB_of_model`. -/
@[stacks 0CR4]
theorem isLeftAdjoint_ι_derivedCategoryB_isQuasicoherentOnSite
    (X : AlgebraicSpaces B S hS) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1)
    (h : HasDerivedCategory.{w} (Modules.{u, u} B S hS X.1 X.2)) :
    (@DerivedCategoryB.derivedCategoryB _ _ _ h
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).ι.IsLeftAdjoint :=
  have := isLeftAdjoint_ι_of_forall_isAffineSpace B S hS B.contains_terminal
    (fun Y hY => isLeftAdjoint_ι_of_isAffineSpace B S hS Y hY) X hXqc hXqs
  StacksDraft.DerivedModel.isLeftAdjoint_ι_derivedCategoryB_of_model _ _ h this

/-- **Stacks 0CR4, with the coherator exhibited as an exact functor.**  For a quasi-compact
quasi-separated algebraic space `X` the inclusion `D_QCoh(𝒪_X) ⥤ D(𝒪_X)` has a right adjoint
`DQ_X` together with a `Functor.CommShift ℤ` structure making the adjunction triangulated: a right
adjoint of an exact functor is exact. -/
theorem exists_isTriangulated_rightAdjoint_ι_derivedCategoryB_isQuasicoherentOnSite
    (X : AlgebraicSpaces B S hS) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1) :
    ∃ (DQ : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
        (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).FullSubcategory)
      (adj : (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).ι ⊣ DQ)
      (_ : DQ.CommShift ℤ), adj.IsTriangulated := by
  have := isLeftAdjoint_ι_derivedCategoryB_isQuasicoherentOnSite B S hS X hXqc hXqs
    (HasDerivedCategory.standard _)
  let adj := Adjunction.ofIsLeftAdjoint (DerivedCategoryB.derivedCategoryB
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).ι
  let : (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).ι.rightAdjoint.CommShift ℤ :=
    adj.rightAdjointCommShift ℤ
  let : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  exact ⟨_, adj, inferInstance, Adjunction.IsTriangulated.mk' adj⟩

end AlgebraicGeometry.Space

end
