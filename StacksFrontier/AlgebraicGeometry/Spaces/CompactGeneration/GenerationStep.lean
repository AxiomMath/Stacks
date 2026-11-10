module

public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.AffineLift
public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.CompactLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.ExcisionDerived
public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.SquareQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.UnitLocus

/-!
# The induction step for compact generation of `D_QCoh`

Let `(U ⊆ W, j : V ⟶ W)` be an elementary distinguished square of algebraic spaces with `W`
quasi-separated, `U` quasi-compact and `V` affine, and `P = U ×_W V`. If `D_QCoh(𝒪_U)` has a
compact weak generator `G`, so has `D_QCoh(𝒪_W)`:

* choose global functions `f_1, …, f_r` on `V` cutting out `V ∖ P`, and their Koszul object
  `K`, compact in `D_QCoh(𝒪_V)`, zero on `P`, detecting the objects of `D_QCoh(𝒪_V)` zero on `P`;
* lift `(G ⊕ G[1])|_P` to a compact `c` on `V` ([Stacks, Tag 08EK]) and glue `G ⊕ G[1]` on `U`
  with `c` on `V` to an object `E` of `D_QCoh(𝒪_W)` ([Stacks, Tag 08HB]);
* then `E ⊕ j_! K` is a compact weak generator of `D_QCoh(𝒪_W)`.

This is the induction step of the proof of [Stacks, Tag 09IY].

## Main results

* `AlgebraicGeometry.Space.isZero_restrictSnd_koszul`: the Koszul object vanishes on `P`.
* `AlgebraicGeometry.Space.exists_compact_generator_of_eds`: the induction step.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Pretriangulated

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

attribute [local instance] smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}

/-- **The Koszul object of functions whose unit loci cover `P` vanishes on `P`.** -/
theorem isZero_restrictSnd_koszul (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
    (l : List (Stacks.Cohomology.SiteModules.GlobalSectionRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS V hsq.isAlgebraicSpace).O))))
    (hb : ∀ U' : SmallEtale B S hS (edsInter B S hS hsq).1,
      unitLocusSieve B S hS hsq l U' ∈ SmallEtale.topology B S hS (edsInter B S hS hsq).1 U') :
    IsZero ((etaleModulePullback.{u, u} B S hS (edsSnd B S hS hsq)
      (isEtale_edsSnd B S hS hsq)).mapDerivedCategory.obj (koszul hsq.isAlgebraicSpace l)) := by
  rw [DerivedCategory.isZero_iff_forall_isZero_homology]
  intro q
  refine IsZero.of_iso (isZero_of_forall_exists_sieve (edsInter B S hS hsq) _
    fun U' => ⟨_, hb U', fun Y g hg => ?_⟩)
    (((etaleModulePullback.{u, u} B S hS (edsSnd B S hS hsq)
      (isEtale_edsSnd B S hS hsq)).mapDerivedCategoryHomologyIso q).app _)
  obtain ⟨a, ha, hu⟩ := hg
  exact subsingleton_homology_koszul_sections l _ ⟨a, ha, hu⟩ q

section Square

variable (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- **Étale base change on `D_QCoh` for the square**: `(Rj_{U*}A)|_V ≅ R(P ⟶ V)_*(A|_P)` for `A`
in `D_QCoh(𝒪_U)` ([Stacks, Tag 08GE]). -/
def qcohEdsBaseChangeIso (hUq : IsQuasiCompact B S hS (edsOpenHom B S hS hsq).hom)
    (hUs : IsQuasiSeparated B S hS (edsOpenHom B S hS hsq).hom)
    (hPq : IsQuasiCompact B S hS (edsSnd B S hS hsq).hom)
    (hPs : IsQuasiSeparated B S hS (edsSnd B S hS hsq).hom)
    (A : QuasicoherentDerivedCategory.{u, u} B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2) :
    (quasicoherentDerivedEtalePullback B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).obj
      ((quasicoherentDerivedPushforward B S hS (edsOpenHom B S hS hsq) hUq hUs).obj A) ≅
    (quasicoherentDerivedPushforward B S hS (edsSnd B S hS hsq) hPq hPs).obj
      ((quasicoherentDerivedEtalePullback B S hS (edsFst B S hS hsq)
        (isEtale_edsFst B S hS hsq)).obj A) :=
  (ObjectProperty.fullyFaithfulι _).preimageIso
    ((quasicoherentDerivedEtalePullbackCompιIso B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).app _ ≪≫
      (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.mapIso
        ((quasicoherentDerivedPushforwardCompιIso B S hS (edsOpenHom B S hS hsq) hUq hUs).app A) ≪≫
      (derivedPushforwardEtaleBaseChangeIso B S hS (isPullback_edsInter B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).app A.obj ≪≫
      (derivedModulePushforward B S hS (edsSnd B S hS hsq)).mapIso
        ((quasicoherentDerivedEtalePullbackCompιIso B S hS (edsFst B S hS hsq)
          (isEtale_edsFst B S hS hsq)).app A).symm ≪≫
      ((quasicoherentDerivedPushforwardCompιIso B S hS (edsSnd B S hS hsq) hPq hPs).app _).symm)

/-- Restricting to `U` and then to `P` is restricting to `V` and then to `P`, on `D_QCoh`. -/
def qcohEdsRestrictInterIso :
    quasicoherentDerivedEtalePullback B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq) ⋙
      quasicoherentDerivedEtalePullback B S hS (edsFst B S hS hsq) (isEtale_edsFst B S hS hsq) ≅
    quasicoherentDerivedEtalePullback B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq) ⋙
      quasicoherentDerivedEtalePullback B S hS (edsSnd B S hS hsq) (isEtale_edsSnd B S hS hsq) :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (quasicoherentDerivedEtalePullbackCompιIso B S hS
        (edsFst B S hS hsq) (isEtale_edsFst B S hS hsq)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (quasicoherentDerivedEtalePullbackCompιIso B S hS
        (edsOpenHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (edsDerivedRestrictInterIso B S hS hsq).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (quasicoherentDerivedEtalePullbackCompιIso B S hS
        (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq)).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (quasicoherentDerivedEtalePullbackCompιIso B S hS
        (edsSnd B S hS hsq) (isEtale_edsSnd B S hS hsq)).symm ≪≫
      (Functor.associator _ _ _).symm)

/-- **Vanishing in `D_QCoh(𝒪_W)` is local for the square.** -/
theorem isZero_of_isZero_qcohRestrict_eds (N : QuasicoherentDerivedCategory.{u, u} B S hS W.1 W.2)
    (hU : IsZero ((quasicoherentDerivedEtalePullback B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq)).obj N))
    (hV : IsZero ((quasicoherentDerivedEtalePullback B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).obj N)) : IsZero N :=
  IsZero.of_full_of_faithful_of_isZero (QcohDerived B S hS W).ι N
    (isZero_of_isZero_derivedRestrict_eds B S hS hsq N.obj
      (((QcohDerived B S hS _).ι.map_isZero hU).of_iso
        ((quasicoherentDerivedEtalePullbackCompιIso B S hS _ _).app N).symm)
      (((QcohDerived B S hS _).ι.map_isZero hV).of_iso
        ((quasicoherentDerivedEtalePullbackCompιIso B S hS _ _).app N).symm))

end Square

/-- **Gluing a compact object across the square.** Let `(U ⊆ W, j : V ⟶ W)` be an elementary
distinguished square with `W` quasi-separated, `U` quasi-compact and `V` affine. For every compact
object `G` of `D_QCoh(𝒪_U)` there is a compact object `E` of `D_QCoh(𝒪_W)` with
`E|_U ≅ G ⊕ G[1]`. -/
theorem exists_isCompactObject_restrictOpen_iso_biprod_shift (hZ : B.Contains (⊤_ Scheme.{u}))
    (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV) (hVa : IsAffineSpace B S hS V)
    (hUqc : IsQuasiCompactSpace B S hS Uo.toFunctor)
    (hWqs : IsAbsolutelyQuasiSeparated B S hS hZ W.1)
    (G : QuasicoherentDerivedCategory.{u, u} B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2)
    (hGc : IsCompactObject.{u} G) :
    ∃ E : QuasicoherentDerivedCategory.{u, u} B S hS W.1 W.2, IsCompactObject.{u} E ∧
      Nonempty ((quasicoherentDerivedEtalePullback B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq)).obj E ≅ G ⊞ G⟦(1 : ℤ)⟧) := by
  have hVqc : IsQuasiCompactSpace B S hS V := hVa.isQuasiCompactSpace
  have hVqs := isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ hVa
  have hPqc := isQuasiCompactSpace_edsInter B S hS hZ hsq hUqc hVqc hWqs
  have hUq := isQuasiCompact_edsOpenHom B S hS hZ (hsq := hsq) hWqs hUqc
  have hUs := isQuasiSeparated_edsOpenHom B S hS hsq
  have hVq := isQuasiCompact_edsEtaleHom B S hS hZ (hsq := hsq) hWqs hVqc
  have hVs := isQuasiSeparated_edsEtaleHom B S hS hZ (hsq := hsq) hVqs
  have hSq := isQuasiCompact_edsSnd B S hS hZ (hsq := hsq) hVqs hPqc
  have hSs := isQuasiSeparated_edsSnd B S hS hsq
  obtain ⟨l, ha, hb⟩ := exists_list_globalRing_unitLocus B S hS hsq hZ hVa hUqc hWqs
  obtain ⟨T₀, hT₀, ⟨i⟩⟩ := hVa
  have hTa : IsAffineChart B S hS V (chartOfIso B S hS T₀ i) := hT₀
  let Kd := koszul (edsEtale B S hS hsq).2 l
  have hKP : IsZero ((edsDerivedRestrictSnd B S hS hsq).obj Kd) :=
    isZero_restrictSnd_koszul hsq l hb
  have := hasCoproducts_quasicoherentDerivedCategory_ringUniverse B S hS W.1 W.2
  have := hasCoproducts_quasicoherentDerivedCategory_ringUniverse B S hS
    (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2
  have := hasCoproducts_quasicoherentDerivedCategory_ringUniverse B S hS
    (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2
  have := hasCoproducts_quasicoherentDerivedCategory_ringUniverse B S hS
    (edsInter B S hS hsq).1 (edsInter B S hS hsq).2
  let aU := quasicoherentDerivedEtalePullback B S hS (edsOpenHom B S hS hsq)
    (isEtale_edsOpenHom B S hS hsq)
  let aV := quasicoherentDerivedEtalePullback B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq)
  let bU := quasicoherentDerivedEtalePullback B S hS (edsFst B S hS hsq) (isEtale_edsFst B S hS hsq)
  let bV := quasicoherentDerivedEtalePullback B S hS (edsSnd B S hS hsq) (isEtale_edsSnd B S hS hsq)
  let adjU := quasicoherentDerivedEtaleAdjunction B S hS _ (isEtale_edsOpenHom B S hS hsq) hUq hUs
  let adjV := quasicoherentDerivedEtaleAdjunction B S hS _ (isEtale_edsEtaleHom B S hS hsq) hVq hVs
  let adjι := quasicoherentDerivedEtaleAdjunction B S hS _ (isEtale_edsSnd B S hS hsq) hSq hSs
  -- the compact lift of `(G ⊕ G[1])|_P` to `V`
  obtain ⟨c, hc, ⟨ec⟩⟩ := exists_isCompactObject_restrict_iso_biprod_shift
    (X := edsEtale B S hS hsq) (Y := edsInter B S hS hsq) (chartOfIso B S hS T₀ i)
    (isTerminalChartOfIso (B := B) (S := S) (hS := hS) T₀ i) hTa
    (edsSnd B S hS hsq) (isEtale_edsSnd B S hS hsq) hSq hSs l ha hKP (bU.obj G)
    (isCompactObject_quasicoherentDerivedEtalePullback_obj B S hS _ _
      (isQuasiCompact_edsFst B S hS hZ (hsq := hsq) hWqs hPqc)
      (isQuasiSeparated_edsFst B S hS hZ (hsq := hsq) hVqs) hGc)
  -- the glued object
  let A := G ⊞ G⟦(1 : ℤ)⟧
  have hA : IsCompactObject.{u} A := isCompactObject_biprod hGc (isCompactObject_shift hGc 1)
  have : bU.Additive := inferInstance
  have := preservesBinaryBiproducts_of_preservesBiproducts bU
  let eA : bU.obj A ≅ bV.obj c :=
    bU.mapBiprod G (G⟦(1 : ℤ)⟧) ≪≫
      biprod.mapIso (Iso.refl _) ((bU.commShiftIso (1 : ℤ)).app G) ≪≫ ec.symm
  have hUV : ∀ N, IsZero (bV.obj N) → IsZero (aU.obj ((quasicoherentDerivedPushforward B S hS
      (edsEtaleHom B S hS hsq) hVq hVs).obj N)) := fun N hN =>
    IsZero.of_full_of_faithful_of_isZero (QcohDerived B S hS _).ι _
      (isZero_restrictOpen_derivedPushforwardEtale B S hS hsq N.obj
        ((QcohDerived B S hS _).ι.map_isZero hN))
  have hexc : ∀ N, IsZero (bV.obj N) → IsIso (adjV.counit.app N) := fun N hN =>
    isIso_quasicoherentDerivedEtaleAdjunction_counit_app B S hS _ _ hVq hVs N
      (isIso_etaleDerivedModuleAdjunction_counit_edsEtale B S hS hsq N.obj
        ((QcohDerived B S hS _).ι.map_isZero hN))
  obtain ⟨E₁, ⟨eU⟩, ⟨eV⟩⟩ := exists_glue_of_excision adjU adjV adjι
    (qcohEdsBaseChangeIso hsq hUq hUs hSq hSs) hUV hexc A c eA
  have hE₁ : IsCompactObject.{u} E₁ := by
    refine isCompactObject_of_isQcohCompact_restrict_eds hsq E₁
      (isQcohCompact_of_isCompactObject B S hS _ (aU.obj E₁) (isCompactObject_of_iso eU hA))
      (isQcohCompact_of_isCompactObject B S hS _ (aV.obj E₁) (isCompactObject_of_iso eV hc)) ?_
    have hP := isQcohCompact_of_isCompactObject B S hS _ (bV.obj (aV.obj E₁))
      (isCompactObject_of_iso (bV.mapIso eV)
        (isCompactObject_quasicoherentDerivedEtalePullback_obj B S hS _ _ hSq hSs hc))
    exact hP.of_iso ((Dualizing.mapDerivedCategoryCompNatIso _ _ _
      (edsFactorIsoEtale B S hS hsq)).app E₁.obj)
  exact ⟨E₁, hE₁, ⟨eU⟩⟩

/-- **The induction step for compact generation of `D_QCoh`.** Let `(U ⊆ W, j : V ⟶ W)` be an
elementary distinguished square with `W` quasi-separated, `U` quasi-compact and `V` affine. If
`D_QCoh(𝒪_U)` has a compact object which is a weak triangulated generator, so has
`D_QCoh(𝒪_W)`. -/
theorem exists_compact_generator_of_eds (hZ : B.Contains (⊤_ Scheme.{u}))
    (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV) (hVa : IsAffineSpace B S hS V)
    (hUqc : IsQuasiCompactSpace B S hS Uo.toFunctor)
    (hWqs : IsAbsolutelyQuasiSeparated B S hS hZ W.1)
    (G : QuasicoherentDerivedCategory.{u, u} B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2)
    (hGc : IsCompactObject.{u} G) (hG : (ObjectProperty.singleton G).IsWeakTriangulatedGenerator) :
    ∃ E : QuasicoherentDerivedCategory.{u, u} B S hS W.1 W.2,
      IsCompactObject.{u} E ∧ (ObjectProperty.singleton E).IsWeakTriangulatedGenerator := by
  obtain ⟨E₁, hE₁, ⟨eU⟩⟩ :=
    exists_isCompactObject_restrictOpen_iso_biprod_shift hZ hsq hVa hUqc hWqs G hGc
  have hVqc : IsQuasiCompactSpace B S hS V := hVa.isQuasiCompactSpace
  have hVqs := isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ hVa
  have hVq := isQuasiCompact_edsEtaleHom B S hS hZ (hsq := hsq) hWqs hVqc
  have hVs := isQuasiSeparated_edsEtaleHom B S hS hZ (hsq := hsq) hVqs
  have hUq := isQuasiCompact_edsOpenHom B S hS hZ (hsq := hsq) hWqs hUqc
  have hUs := isQuasiSeparated_edsOpenHom B S hS hsq
  have hPqc := isQuasiCompactSpace_edsInter B S hS hZ hsq hUqc hVqc hWqs
  have hSq := isQuasiCompact_edsSnd B S hS hZ (hsq := hsq) hVqs hPqc
  have hSs := isQuasiSeparated_edsSnd B S hS hsq
  obtain ⟨l, ha, hb⟩ := exists_list_globalRing_unitLocus B S hS hsq hZ hVa hUqc hWqs
  obtain ⟨T₀, hT₀, ⟨i⟩⟩ := hVa
  have hT := isTerminalChartOfIso (B := B) (S := S) (hS := hS) T₀ i
  have hTa : IsAffineChart B S hS V (chartOfIso B S hS T₀ i) := hT₀
  let Kd := koszul (edsEtale B S hS hsq).2 l
  have hKP : IsZero ((edsDerivedRestrictSnd B S hS hsq).obj Kd) :=
    isZero_restrictSnd_koszul hsq l hb
  have := hasCoproducts_quasicoherentDerivedCategory_ringUniverse B S hS W.1 W.2
  have := hasCoproducts_quasicoherentDerivedCategory_ringUniverse B S hS
    (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2
  let aU := quasicoherentDerivedEtalePullback B S hS (edsOpenHom B S hS hsq)
    (isEtale_edsOpenHom B S hS hsq)
  let aV := quasicoherentDerivedEtalePullback B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq)
  let adjU := quasicoherentDerivedEtaleAdjunction B S hS _ (isEtale_edsOpenHom B S hS hsq) hUq hUs
  let adjι := quasicoherentDerivedEtaleAdjunction B S hS _ (isEtale_edsSnd B S hS hsq) hSq hSs
  -- the Koszul generator `j_! K`
  have hK'qc : QcohDerived B S hS W ((edsDerivedShriekEtale B S hS hsq).obj Kd) :=
    have := isIso_derivedShriekToPushforwardEtale B S hS hsq Kd hKP
    (QcohDerived B S hS W).prop_of_iso
      (asIso (derivedShriekToPushforwardEtale B S hS hsq Kd hKP)).symm
      (qcohDerived_derivedModulePushforward_obj B S hS _ hVq hVs Kd (qcohDerived_koszul l))
  let K' : QuasicoherentDerivedCategory.{u, u} B S hS W.1 W.2 := ⟨_, hK'qc⟩
  -- compactness
  have hK' : IsCompactObject.{u} K' :=
    isCompactObject_of_isQcohCompact B S hS W K' (isQcohCompact_lowerShriek _ _
      (isQcohCompact_of_isCompactObject B S hS (edsEtale B S hS hsq)
        (koszulQuasicoherent (edsEtale B S hS hsq).2 l)
        (isCompactObject_koszulQuasicoherent _ hT hTa l)))
  refine ⟨E₁ ⊞ K', isCompactObject_biprod hE₁ hK', fun M hM => ?_⟩
  -- generation
  have hEn : ∀ (n : ℤ) (y : (E₁ ⊞ K')⟦n⟧ ⟶ M), y = 0 := fun n y =>
    hM y ⟨E₁ ⊞ K', n, Iso.refl _, (ObjectProperty.singleton_iff _ _).2 rfl⟩
  have hret : ∀ {X : QuasicoherentDerivedCategory.{u, u} B S hS W.1 W.2}
      (i : X ⟶ E₁ ⊞ K') (r : E₁ ⊞ K' ⟶ X), i ≫ r = 𝟙 X → ∀ (n : ℤ) (x : X⟦n⟧ ⟶ M), x = 0 :=
    fun i r hir n x => by
      rw [← Category.id_comp x, ← (shiftFunctor _ n).map_id, ← hir, Functor.map_comp,
        Category.assoc, hEn n (r⟦n⟧' ≫ x), comp_zero]
  have hEM := hret biprod.inl biprod.fst biprod.inl_fst
  have hKM := hret biprod.inr biprod.snd biprod.inr_snd
  have hK : ∀ (n : ℤ) (y : (koszulQuasicoherent (edsEtale B S hS hsq).2 l)⟦n⟧ ⟶ aV.obj M),
      y = 0 := by
    intro n y
    let ιV := (QcohDerived B S hS (edsEtale B S hS hsq)).ι
    let ιW := (QcohDerived B S hS W).ι
    let adjS := (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory
    let y₁ : (ιV.obj (koszulQuasicoherent (edsEtale B S hS hsq).2 l))⟦n⟧ ⟶
        ιV.obj (aV.obj M) :=
      (ιV.commShiftIso n).inv.app (koszulQuasicoherent (edsEtale B S hS hsq).2 l) ≫ ιV.map y
    let y₂ := (adjS.homEquiv _ _).symm y₁
    let eZ : ιW.obj (K'⟦n⟧) ≅ (edsDerivedShriekEtale B S hS hsq).obj
        ((ιV.obj (koszulQuasicoherent (edsEtale B S hS hsq).2 l))⟦n⟧) :=
      (ιW.commShiftIso n).app K' ≪≫
        (((edsDerivedShriekEtale B S hS hsq).commShiftIso n).app Kd).symm
    let y₃ : K'⟦n⟧ ⟶ M := ιW.preimage (eZ.hom ≫ y₂)
    have h3 : ιW.map y₃ = 0 := by rw [hKM n y₃, Functor.map_zero]
    have h2 : y₂ = 0 := by
      rw [Functor.map_preimage] at h3
      exact (cancel_epi eZ.hom).1 (h3.trans comp_zero.symm)
    have h1 : y₁ = 0 := by
      rw [← (adjS.homEquiv _ _).apply_symm_apply y₁]
      change adjS.homEquiv _ _ y₂ = 0
      rw [h2, Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]
    have h0 : ιV.map y = 0 := (cancel_epi _).1 (h1.trans comp_zero.symm)
    exact ιV.map_injective (h0.trans (Functor.map_zero _ _ _).symm)
  have hGgen : ∀ A' : QuasicoherentDerivedCategory.{u, u} B S hS (edsOpen B S hS hsq).1
      (edsOpen B S hS hsq).2, (∀ (n : ℤ) (x : G⟦n⟧ ⟶ A'), x = 0) → IsZero A' := by
    intro A' h
    refine hG A' fun X f hX => ?_
    obtain ⟨Y, a, e, hY⟩ := hX
    rw [ObjectProperty.singleton_iff] at hY
    subst hY
    rw [← Category.id_comp f, ← e.hom_inv_id, Category.assoc, h a (e.inv ≫ f), comp_zero]
  exact isZero_of_orthogonal_glue adjU adjι (qcohEdsRestrictInterIso hsq)
    (qcohEdsBaseChangeIso hsq hUq hUs hSq hSs) (isZero_of_isZero_qcohRestrict_eds hsq)
    (koszulQuasicoherent (edsEtale B S hS hsq).2 l)
    (IsZero.of_full_of_faithful_of_isZero (QcohDerived B S hS _).ι _ hKP)
    (fun N hN horth => isZero_of_hom_koszulQuasicoherent_shift_eq_zero_of_isZero_restrict
      (X := edsEtale B S hS hsq) _ hT hTa (edsSnd B S hS hsq) (isEtale_edsSnd B S hS hsq) l ha N hN
      horth)
    G hGgen E₁ eU M hEM hK

end AlgebraicGeometry.Space

end
