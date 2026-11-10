module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationAmplitudeBound
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisGlueingTag
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SupportTriangles
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ElementaryDistinguishedSquareCover
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DistinguishedTrianglesGeneral
public import StacksFrontier.AlgebraicGeometry.Spaces.CommonLemmas

/-!
# The induction step of Stacks 08HN

Let `(U ⊆ X, j : V ⟶ X)` be an elementary distinguished square with `V` affine and `U ×_X V`
quasi-compact, let `T ⊆ |X|` be closed with quasi-compact open complement, and let `E` be an
object of `D_QCoh(𝒪_X)` with `Hⁱ(E)|_U = 0` for `i > t`.  Given an approximation `α : P ⟶ E|_U`
of `(T ∩ |U|, E|_U, t)`, the source produces a perfect `R` supported on `T` with a morphism
`R ⟶ E` whose restriction to `U` is `P ⊕ P[1] ⟶ P ⟶ E|_U`:

* on `V`, Stacks 08EK and 08EH give a perfect `Q` supported on `j^{-1}T` with
  `Q|_{U ×_X V} ≅ (P ⊕ P[1])|_{U ×_X V}` and a morphism `Q ⟶ E|_V` lifting the composite
  (`AlgebraicGeometry.Space.supportedLiftProperty_edsSnd`);
* Stacks 08HB glues `P ⊕ P[1]` and `Q` to `R` and the two morphisms to `R ⟶ E`.

In a distinguished triangle `R ⟶ E ⟶ E' ⟶ R[1]` the object `E'` then has `Hⁱ(E')|_U = 0` for
`i ≥ t`, which is what makes the induction on `t` run.

## Main results

* `AlgebraicGeometry.Space.exists_approximation_step`

## References

* [Stacks Project, Tag 08HN](https://stacks.math.columbia.edu/tag/08HN)
* [Stacks Project, Tag 08HB](https://stacks.math.columbia.edu/tag/08HB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance 10000] HasDerivedCategory.standard smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective smallEtaleRingedSite_hasSheafify_over
  smallEtaleRingedSite_wEqualsLocallyBijective_over

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for `HasPullbacks` of presheaves on the big fppf site times out otherwise
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance hasPullbacks_presheaf_ApproximationSquareStep :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_ApproximationSquareStep
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

section Generic

variable (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- `P ⊕ P[1]` is perfect when `P` is: the binary biproduct triangle is distinguished, and
perfectness is stable under shifts and two-out-of-three (Stacks 08G9). -/
theorem isPerfect_biprod_shift (P : DerivedCategory (Modules.{u, u} B S hS F hF))
    (hP : (smallEtaleRingedSite B S hS F hF).IsPerfect P) :
    (smallEtaleRingedSite B S hS F hF).IsPerfect (P ⊞ P⟦(1 : ℤ)⟧) :=
  RingedSite.isPerfect_obj₂_of_distinguished_general _ (binaryBiproductTriangle P (P⟦(1 : ℤ)⟧))
    (binaryBiproductTriangle_distinguished _ _) hP
    (RingedSite.isPerfect_shift_general _ hP 1)

/-- Support on `T` is stable under the shift by one: `P ⟶ 0 ⟶ P[1] ⟶ P[1]` is distinguished,
so `Hⁱ(P[1])` is supported where `Hⁱ⁺¹(P)` is. -/
theorem cohomologySupportedOn_shift_one (T : Set (points B S hS F))
    (P : DerivedCategory (Modules.{u, u} B S hS F hF))
    (hP : CohomologySupportedOn B S hS F hF T P) :
    CohomologySupportedOn B S hS F hF T (P⟦(1 : ℤ)⟧) := fun i x hx => by
  have h := supportOfSheaf_homology_obj₃_subset B S hS F hF (contractibleTriangle P).rotate
    (rot_of_distTriang _ (contractible_distinguished P)) i hx
  rcases h with h | h
  · have h0 : supportOfSheaf B S hS F ((SheafOfModules.toSheaf.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).obj
          ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS F hF) i).obj
            (contractibleTriangle P).rotate.obj₂)) = ∅ :=
      (supportOfSheaf_eq_empty_iff_isZero B S hS ⟨F, hF⟩ _).2
        ((DerivedCategory.homologyFunctor _ i).map_isZero (isZero_zero _))
    rw [h0] at h
    exact absurd h (Set.notMem_empty x)
  · exact hP (i + 1) h

/-- `P ⊕ P[1]` is supported on `T` when `P` is. -/
theorem cohomologySupportedOn_biprod_shift (T : Set (points B S hS F))
    (P : DerivedCategory (Modules.{u, u} B S hS F hF))
    (hP : CohomologySupportedOn B S hS F hF T P) :
    CohomologySupportedOn B S hS F hF T (P ⊞ P⟦(1 : ℤ)⟧) := by
  have h1 := cohomologySupportedOn_shift_one B S hS F hF T P hP
  have h2 := binaryBiproductTriangle_distinguished P (P⟦(1 : ℤ)⟧)
  have h3 := cohomologySupportedOn_obj₂_of_distinguished B S hS F hF T
    (binaryBiproductTriangle P (P⟦(1 : ℤ)⟧)) h2 hP h1
  exact h3

/-- Quasi-coherence on the small étale site of an algebraic space, as a weak Serre subcategory in
the five-term form. -/
theorem isWeakSerre_quasicoherentSheaves_smallEtaleRingedSite :
    WeakSerre.IsWeakSerre (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))) := by
  have := isWeakSerreClass_quasicoherentSheaves B S hS ⟨F, hF⟩
  refine ⟨inferInstance, ObjectProperty.exists_prop_of_isWeakSerreClass _,
    fun E h₀ h₁ h₃ h₄ => ?_⟩
  exact ObjectProperty.prop_mid_of_exact₄ (ObjectProperty.prop_obj₂_of_exact _)
    E.zero₀ E.zero₁ E.zero₂ E.exact₁ E.exact₂ E.exact₃ h₀ h₁ h₃ h₄

/-- In a distinguished triangle of `D(𝒪_F)` whose first two vertices have quasi-coherent
cohomology, so does the third. -/
theorem derivedCategoryB_quasicoherent_obj₃
    (Tri : Triangle (DerivedCategory (Modules.{u, u} B S hS F hF)))
    (hTri : Tri ∈ distTriang (DerivedCategory (Modules.{u, u} B S hS F hF)))
    (h₁ : DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))) Tri.obj₁)
    (h₂ : DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))) Tri.obj₂) :
    DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))) Tri.obj₃ :=
  DerivedCategoryB.derivedCategoryB_mem_obj₂_of_distinguished _
    (isWeakSerre_quasicoherentSheaves_smallEtaleRingedSite B S hS F hF) Tri.rotate
    (rot_of_distTriang Tri hTri) h₂
    (DerivedCategoryB.derivedCategoryB_shift_mem _
      (isWeakSerre_quasicoherentSheaves_smallEtaleRingedSite B S hS F hF)
      1 h₁)

end Generic

section Square

attribute [local instance] etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback

variable {W : AlgebraicSpaces B S hS} {Ve : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : Ve ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- The support of `Hⁱ` of the étale restriction of `F` is the preimage of the support of
`Hⁱ(F)`. -/
private theorem mem_supportOfSheaf_homology_mapDerivedCategory_iff {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (F : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)) (i : ℤ) (y : points B S hS X.1) :
    y ∈ supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj
          ((etaleModulePullback B S hS f hf).mapDerivedCategory.obj F))) ↔
      pointsMap B S hS X.1 f.hom y ∈ supportOfSheaf B S hS Y.1 ((SheafOfModules.toSheaf _).obj
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).obj F)) := by
  exact (Set.ext_iff.1 (supportOfSheaf_eq_of_iso B S hS X
    (((etaleModulePullback B S hS f hf).mapDerivedCategoryHomologyIso i).app F)) y).trans
    (Set.ext_iff.1 (supportOfSheaf_toSheaf_etaleModulePullback B S hS f hf _) y)

/-- **Support on an elementary distinguished square is tested on its two members**: an object
of `D(𝒪_X)` whose restrictions to `U` and to `V` are supported over `T` is supported on `T`,
the points of `U` and of `V` covering those of `X`. -/
theorem cohomologySupportedOn_of_edsRestrict (T : Set (points B S hS W.1))
    (F : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (hU : CohomologySupportedOn B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2
      (pointsMap B S hS (edsOpen B S hS hsq).1 (edsOpenHom B S hS hsq).hom ⁻¹' T)
      ((edsRestrictOpen B S hS hsq).mapDerivedCategory.obj F))
    (hV : CohomologySupportedOn B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2
      (pointsMap B S hS (edsEtale B S hS hsq).1 (edsEtaleHom B S hS hsq).hom ⁻¹' T)
      ((edsRestrictEtale B S hS hsq).mapDerivedCategory.obj F)) :
    CohomologySupportedOn B S hS W.1 W.2 T F := by
  intro i x hx
  rcases mem_range_edsOpenHom_or_mem_range_edsEtaleHom B S hS hsq x with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · exact hU i ((mem_supportOfSheaf_homology_mapDerivedCategory_iff B S hS _ _ _ i y).2 hx)
  · exact hV i ((mem_supportOfSheaf_homology_mapDerivedCategory_iff B S hS _ _ _ i y).2 hx)

/-- Support is invariant under isomorphism in the derived category. -/
theorem cohomologySupportedOn_of_iso' {Y : AlgebraicSpaces B S hS} {T : Set (points B S hS Y.1)}
    {K L : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)} (e : K ≅ L)
    (hK : CohomologySupportedOn B S hS Y.1 Y.2 T K) : CohomologySupportedOn B S hS Y.1 Y.2 T L :=
  fun i => (supportOfSheaf_eq_of_iso B S hS Y
    ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).mapIso e)).ge.trans (hK i)

/-- Perfectness is invariant under isomorphism in the derived category. -/
theorem isPerfect_of_iso' {Y : AlgebraicSpaces B S hS}
    {K L : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)} (e : K ≅ L)
    (hK : (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect K) :
    (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect L := by
  obtain ⟨E, hE, ⟨i⟩⟩ := hK
  exact ⟨E, hE, ⟨i ≪≫ e⟩⟩

/-- An additive functor commuting with the shift carries `P ⊕ P[1]` to `F P ⊕ (F P)[1]`,
compatibly with the first projection. -/
def mapBiprodShiftIso {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D] [HasShift C ℤ] [HasShift D ℤ]
    (Fn : C ⥤ D) [Fn.Additive] [Fn.CommShift ℤ] (P : C) :
    Fn.obj (P ⊞ P⟦(1 : ℤ)⟧) ≅ Fn.obj P ⊞ (Fn.obj P)⟦(1 : ℤ)⟧ :=
  haveI : PreservesBinaryBiproducts Fn := preservesBinaryBiproducts_of_preservesBiproducts Fn
  Fn.mapBiprod _ _ ≪≫ biprod.mapIso (Iso.refl _) ((Fn.commShiftIso (1 : ℤ)).app P)

/-- The isomorphism `mapBiprodShiftIso Fn P`, followed by the first projection of
`Fn P ⊕ (Fn P)[1]`, is the image under `Fn` of the first projection of `P ⊕ P[1]`. -/
theorem mapBiprodShiftIso_hom_fst {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] [HasBinaryBiproducts C] [HasBinaryBiproducts D] [HasShift C ℤ]
    [HasShift D ℤ] (Fn : C ⥤ D) [Fn.Additive] [Fn.CommShift ℤ] (P : C) :
    (mapBiprodShiftIso Fn P).hom ≫ biprod.fst = Fn.map biprod.fst := by
  simp only [mapBiprodShiftIso, Iso.trans_hom, Functor.mapBiprod_hom, biprod.mapIso_hom,
    Iso.refl_hom, Category.assoc, biprod.map_fst, Category.comp_id, biprod.lift_fst]

/-- **The gluing of the step of Stacks 08HN.**  Given a perfect `P` on `U` supported over `T` and
`α : P ⟶ E|_U`, there are a perfect `R` on `X` supported on `T`, an isomorphism
`f : R|_U ≅ P ⊕ P[1]` and `φ : R ⟶ E` with `φ|_U = f ≫ pr₁ ≫ α`.  On `V` this is the supported
lifting property of `U ×_X V ⟶ V` (Stacks 08EK and 08EH); the two halves are glued by
Stacks 08HB. -/
theorem exists_glued_approximation (T : Set (points B S hS W.1))
    (hlift : SupportedLiftProperty B S hS (edsSnd B S hS hsq) (isEtale_edsSnd B S hS hsq)
      (pointsMap B S hS (edsEtale B S hS hsq).1 (edsEtaleHom B S hS hsq).hom ⁻¹' T))
    (E : QuasicoherentDerivedCategory.{u, u} B S hS W.1 W.2)
    (P : DerivedCategory (Modules.{u, u} B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2))
    (hP : (smallEtaleRingedSite B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2).IsPerfect P)
    (hPT : CohomologySupportedOn B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2
      (pointsMap B S hS (edsOpen B S hS hsq).1 (edsOpenHom B S hS hsq).hom ⁻¹' T) P)
    (α : P ⟶ (edsRestrictOpen B S hS hsq).mapDerivedCategory.obj E.obj) :
    ∃ (R : DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) (φ : R ⟶ E.obj)
      (f : (edsRestrictOpen B S hS hsq).mapDerivedCategory.obj R ≅ P ⊞ P⟦(1 : ℤ)⟧),
      (smallEtaleRingedSite B S hS W.1 W.2).IsPerfect R ∧
      CohomologySupportedOn B S hS W.1 W.2 T R ∧
      (edsRestrictOpen B S hS hsq).mapDerivedCategory.map φ = f.hom ≫ biprod.fst ≫ α := by
  let Fst := (edsRestrictFst B S hS hsq).mapDerivedCategory
  let Snd := (edsRestrictSnd B S hS hsq).mapDerivedCategory
  let PI := Fst.obj P
  have hPI : (smallEtaleRingedSite B S hS (edsInter B S hS hsq).1
      (edsInter B S hS hsq).2).IsPerfect PI :=
    isPerfect_etaleModulePullback_standard B S hS (edsFst B S hS hsq)
      (isEtale_edsFst B S hS hsq) P hP
  have hsq' : (edsFst B S hS hsq).hom ≫ (edsOpenHom B S hS hsq).hom =
      (edsSnd B S hS hsq).hom ≫ (edsEtaleHom B S hS hsq).hom := pullback.condition
  have hPIZ : CohomologySupportedOn B S hS (edsInter B S hS hsq).1 (edsInter B S hS hsq).2
      (pointsMap B S hS (edsInter B S hS hsq).1 (edsSnd B S hS hsq).hom ⁻¹'
        (pointsMap B S hS (edsEtale B S hS hsq).1 (edsEtaleHom B S hS hsq).hom ⁻¹' T)) PI := by
    have h := cohomologySupportedOn_etaleModulePullback B S hS (edsFst B S hS hsq)
      (isEtale_edsFst B S hS hsq) _ P hPT
    rwa [← Set.preimage_comp, ← pointsMap_comp, hsq', pointsMap_comp, Set.preimage_comp] at h
  let G := (edsRestrictEtale B S hS hsq).mapDerivedCategory.obj E.obj
  have hG := derivedQuasicoherent_etaleModulePullback B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq) E.obj E.property
  let α' : PI ⟶ Snd.obj G := Fst.map α ≫ (edsDerivedRestrictCompOpen B S hS hsq).hom.app E.obj ≫
    (edsDerivedRestrictCompEtale B S hS hsq).inv.app E.obj
  obtain ⟨Q, hQ, hQT, c, b, hcb⟩ := hlift PI hPI hPIZ G hG α'
  let cA := mapBiprodShiftIso Fst P ≪≫ c
  obtain ⟨R, f, g, -, hglue⟩ := exists_glued_object_and_hom B S hS hsq (P ⊞ P⟦(1 : ℤ)⟧) Q cA
  have hab : Fst.map (biprod.fst ≫ α) ≫ (edsDerivedRestrictCompOpen B S hS hsq).hom.app E.obj =
      cA.hom ≫ Snd.map b ≫ (edsDerivedRestrictCompEtale B S hS hsq).hom.app E.obj := by
    simp only [cA, Iso.trans_hom, Category.assoc]
    rw [reassoc_of% hcb]
    simp only [α', Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    rw [reassoc_of% (mapBiprodShiftIso_hom_fst Fst P), Functor.map_comp, Category.assoc]
  obtain ⟨φ, hφU, hφV⟩ := hglue E.obj (biprod.fst ≫ α) b hab
  refine ⟨R, φ, f, ?_, ?_, hφU⟩
  · exact isPerfect_of_isPerfect_edsRestrict B S hS hsq R
      (isPerfect_of_iso' B S hS f.symm (isPerfect_biprod_shift B S hS _ _ P hP))
      (isPerfect_of_iso' B S hS g.symm hQ)
  · exact cohomologySupportedOn_of_edsRestrict B S hS hsq T R
      (cohomologySupportedOn_of_iso' B S hS f.symm
        (cohomologySupportedOn_biprod_shift B S hS _ _ _ P hPT))
      (cohomologySupportedOn_of_iso' B S hS g.symm hQT)

/-- The cohomology of `P ⊕ P[1]` vanishes in degree `j` as soon as that of `P` vanishes in
degrees `j` and `j + 1`. -/
theorem isZero_homology_biprod_shift {Y : AlgebraicSpaces B S hS}
    (P : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)) (j : ℤ)
    (h₀ : IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) j).obj P))
    (h₁ : IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2)
      (j + 1)).obj P)) :
    IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) j).obj
      (P ⊞ P⟦(1 : ℤ)⟧)) := by
  have hsh : IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) j).obj
      (P⟦(1 : ℤ)⟧)) := by
    have hex := DerivedCategory.HomologySequence.exact₃ _
      (rot_of_distTriang _ (contractible_distinguished P)) j (j + 1)
    exact hex.isZero_X₂ (((DerivedCategory.homologyFunctor _ j).map_isZero
      (isZero_zero _)).eq_of_src _ _) (h₁.eq_of_tgt _ _)
  have hex := DerivedCategory.HomologySequence.exact₂ _
    (binaryBiproductTriangle_distinguished P (P⟦(1 : ℤ)⟧)) j
  exact hex.isZero_X₂ (h₀.eq_of_src _ _) (hsh.eq_of_tgt _ _)

/-- If `α` is surjective on `Hⁱ`, so is `A ≅ P ⊕ P[1] ⟶ P ⟶ E`. -/
theorem epi_homologyFunctor_map_iso_fst_comp {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] {A P E : DerivedCategory C} (f : A ≅ P ⊞ P⟦(1 : ℤ)⟧) (α : P ⟶ E)
    (i : ℤ) (hα : Epi ((DerivedCategory.homologyFunctor C i).map α)) :
    Epi ((DerivedCategory.homologyFunctor C i).map (f.hom ≫ biprod.fst ≫ α)) := by
  have : IsSplitEpi ((DerivedCategory.homologyFunctor C i).map
      (biprod.fst : P ⊞ P⟦(1 : ℤ)⟧ ⟶ P)) :=
    IsSplitEpi.mk' ⟨(DerivedCategory.homologyFunctor C i).map biprod.inl, by
      rw [← Functor.map_comp, biprod.inl_fst, CategoryTheory.Functor.map_id]⟩
  rw [Functor.map_comp, Functor.map_comp]
  infer_instance

/-- **The induction step of Stacks 08HN.**  Let `T ⊆ |X|` be closed with the supported lifting
property for `U ×_X V ⟶ V` at `j^{-1}T`, and let `r_U` be the integer of Stacks 08HJ for
`(U, T ∩ |U|)`.  Let `r ≥ r_U + r'` and let `E` be `(m - r)`-pseudo-coherent with `Hⁱ(E)`
supported on `T` for `i ≥ m - r` and `Hⁱ(E)|_U = 0` for `i > t`, where `t > m - r'`.  Then `E`
sits in a distinguished triangle `R ⟶ E ⟶ E' ⟶ R[1]` with `R` perfect and supported on `T`, `E'`
again `(m - r)`-pseudo-coherent and supported on `T` from degree `m - r` on, and
`Hⁱ(E')|_U = 0` for `i ≥ t`.

The approximation of `E|_U` is taken at the degree `t`, where the source writes `m`: the
surjectivity it needs is on `Hᵗ`, and `E|_U` is `(t - r_U)`-pseudo-coherent because
`t - r_U > m - r`. -/
theorem exists_approximation_step (T : Set (points B S hS W.1))
    (hlift : SupportedLiftProperty B S hS (edsSnd B S hS hsq) (isEtale_edsSnd B S hS hsq)
      (pointsMap B S hS (edsEtale B S hS hsq).1 (edsEtaleHom B S hS hsq).hom ⁻¹' T))
    (rU : ℤ)
    (hrU : ∀ (E : QuasicoherentDerivedCategory.{u, u} B S hS (edsOpen B S hS hsq).1
        (edsOpen B S hS hsq).2) (m : ℤ),
      (smallEtaleRingedSite B S hS (edsOpen B S hS hsq).1
        (edsOpen B S hS hsq).2).IsPseudoCoherentFrom E.obj (m - rU) →
      (∀ i : ℤ, m - rU ≤ i →
        supportOfSheaf B S hS (edsOpen B S hS hsq).1
          ((SheafOfModules.toSheaf
              ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
                (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2).O))).obj
            ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS (edsOpen B S hS hsq).1
              (edsOpen B S hS hsq).2) i).obj E.obj)) ⊆
          pointsMap B S hS (edsOpen B S hS hsq).1 (edsOpenHom B S hS hsq).hom ⁻¹' T) →
      ApproximationHolds B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2
        (pointsMap B S hS (edsOpen B S hS hsq).1 (edsOpenHom B S hS hsq).hom ⁻¹' T) E m)
    (r r' : ℤ) (hrr : rU + r' ≤ r) (m t : ℤ)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS W.1 W.2) (ht : m - r' < t)
    (hE : ApproximationInput B S hS W.1 W.2 T r m E)
    (hamp : CohomologySupportedOnFrom B S hS W.1 W.2 (edsComplementPoints B S hS Uo) (t + 1)
      E.obj) :
    ∃ (Tri : Triangle (DerivedCategory (Modules.{u, u} B S hS W.1 W.2)))
      (E' : QuasicoherentDerivedCategory.{u, u} B S hS W.1 W.2),
      Tri ∈ distTriang (DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) ∧
        (smallEtaleRingedSite B S hS W.1 W.2).IsPerfect Tri.obj₁ ∧
        CohomologySupportedOn B S hS W.1 W.2 T Tri.obj₁ ∧
        E.obj = Tri.obj₂ ∧ E'.obj = Tri.obj₃ ∧
        ApproximationInput B S hS W.1 W.2 T r m E' ∧
        CohomologySupportedOnFrom B S hS W.1 W.2 (edsComplementPoints B S hS Uo) t E'.obj := by
  let O := (edsRestrictOpen B S hS hsq).mapDerivedCategory
  let EU := (quasicoherentDerivedEtalePullback B S hS (edsOpenHom B S hS hsq)
    (isEtale_edsOpenHom B S hS hsq)).obj E
  have hpc : (smallEtaleRingedSite B S hS (edsOpen B S hS hsq).1
      (edsOpen B S hS hsq).2).IsPseudoCoherentFrom EU.obj (t - rU) :=
    isPseudoCoherentFrom_mono B S hS _ _ (isPseudoCoherentFrom_etaleModulePullback B S hS
      (edsOpenHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq) E.obj (m - r) hE.1) (by omega)
  have hsupp : ∀ i : ℤ, t - rU ≤ i →
      supportOfSheaf B S hS (edsOpen B S hS hsq).1
        ((SheafOfModules.toSheaf
            ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
              (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2).O))).obj
          ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS (edsOpen B S hS hsq).1
            (edsOpen B S hS hsq).2) i).obj EU.obj)) ⊆
        pointsMap B S hS (edsOpen B S hS hsq).1 (edsOpenHom B S hS hsq).hom ⁻¹' T := by
    intro i hi p hp
    have hp'' := (mem_supportOfSheaf_homology_mapDerivedCategory_iff B S hS _ _ _ i p).1 hp
    exact hE.2 i (by omega) hp''
  obtain ⟨P, hP, hPT, α, hαiso, hαepi⟩ := hrU EU t hpc hsupp
  obtain ⟨R, φ, f, hR, hRT, hφ⟩ :=
    exists_glued_approximation B S hS hsq T hlift E P hP hPT α
  obtain ⟨Z, g, h, hTri⟩ := distinguished_cocone_triangle φ
  have hRq := derivedCategoryB_of_isPseudoCoherent_unconditional B S hS W.1 W.2 R
    (RingedSite.isPseudoCoherent_of_isPerfect_general _ hR)
  have hZq := derivedCategoryB_quasicoherent_obj₃ B S hS W.1 W.2 (Triangle.mk φ g h) hTri hRq
    E.property
  refine ⟨Triangle.mk φ g h, ⟨Z, hZq⟩, hTri, hR, hRT, rfl, rfl, ⟨?_, ?_⟩, ?_⟩
  · exact RingedSite.isPseudoCoherentFrom_of_distinguished_one_general _ (m - r)
      (Triangle.mk φ g h) hTri
      (RingedSite.isPseudoCoherentFrom_of_isPerfect_anyModuleUniverse _ hR _) hE.1
  · intro i hi x hx
    rcases supportOfSheaf_homology_obj₃_subset B S hS W.1 W.2 _ hTri i hx with h' | h'
    · exact hE.2 i hi h'
    · exact hRT (i + 1) h'
  · -- the amplitude over `U` drops
    have hEU0 : ∀ j : ℤ, t < j → IsZero ((DerivedCategory.homologyFunctor _ j).obj EU.obj) := by
      intro j hj
      refine IsZero.of_iso ?_ (((edsRestrictOpen B S hS hsq).mapDerivedCategoryHomologyIso j).app
        E.obj)
      refine (isZero_etaleModulePullback_iff_disjoint_supportOfSheaf B S hS
        (edsOpenHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq) _).2 ?_
      exact Set.disjoint_left.2 fun x hx hx' => hamp j (by omega) hx hx'
    have hP0 : ∀ j : ℤ, t < j → IsZero ((DerivedCategory.homologyFunctor _ j).obj P) :=
      fun j hj => (hEU0 j hj).of_iso (@asIso _ _ _ _ _ (hαiso j hj))
    refine cohomologySupportedOnFrom_compl_range_of_isZero B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq) t Z fun i hi => ?_
    refine IsZero.of_iso ?_
      (((edsRestrictOpen B S hS hsq).mapDerivedCategoryHomologyIso i).app Z).symm
    have hTriO := O.map_distinguished _ hTri
    have hR0 : IsZero ((DerivedCategory.homologyFunctor _ (i + 1)).obj (O.obj R)) :=
      (isZero_homology_biprod_shift B S hS P (i + 1) (hP0 _ (by omega))
        (hP0 _ (by omega))).of_iso ((DerivedCategory.homologyFunctor _ (i + 1)).mapIso f)
    have hαi : Epi ((DerivedCategory.homologyFunctor _ i).map α) := by
      rcases eq_or_lt_of_le hi with rfl | hlt
      · exact hαepi
      · exact @IsIso.epi_of_iso _ _ _ _ _ (hαiso i hlt)
    have hepi : Epi ((DerivedCategory.homologyFunctor _ i).map (O.map φ)) := by
      rw [hφ]
      exact epi_homologyFunctor_map_iso_fst_comp f α i hαi
    have hex₂ := DerivedCategory.HomologySequence.exact₂ _ hTriO i
    have hex₃ := DerivedCategory.HomologySequence.exact₃ _ hTriO i (i + 1)
    have hg0 := hex₂.epi_f_iff.1 hepi
    exact hex₃.isZero_X₂ hg0 (hR0.eq_of_tgt _ _)

end Square

end AlgebraicGeometry.Space
