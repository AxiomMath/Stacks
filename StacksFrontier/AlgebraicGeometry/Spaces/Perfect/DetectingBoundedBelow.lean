module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectRetract
public import StacksFrontier.AlgebraicGeometry.Duality.KoszulTruncatedOrthogonality
public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.QcqsCompactGeneration
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedGlobalSectionsCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffinePullbackGenerator
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectTensorFlatPullbackBound
import StacksCore.Tactic.StacksAttribute

/-!
# Detecting boundedness below on a quasi-compact quasi-separated algebraic space

Let `X` be a quasi-compact and quasi-separated algebraic space and `E` an object of
`D_QCoh(𝒪_X)`. If for every perfect object `P` of `D(𝒪_X)` the groups `Hom(P[-i], E)` vanish for
`i ≪ 0`, then `E` is bounded below. This is the implication "(7) ⇒ (1)" of Stacks 0GFI.

## Main results

* `CategoryTheory.Pretriangulated.lowHomVanishing`: the objects `P` with `Hom(P[-i], M) = 0` for
  `i ≪ 0`, a triangulated subcategory stable under retracts.
* `AlgebraicGeometry.Space.exists_isLE_of_isPerfect`: a perfect object on a quasi-compact
  algebraic space is bounded above.
* `AlgebraicGeometry.Space.exists_isGE_of_lowHomVanishingOnCompact`: the implication above, with
  the hypothesis asked of the compact — equivalently perfect — objects of `D_QCoh(𝒪_X)`.

## References

* [Stacks Project, Tag 0GFI](https://stacks.math.columbia.edu/tag/0GFI)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Tag 09SR](https://stacks.math.columbia.edu/tag/09SR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Pretriangulated

namespace CategoryTheory.Pretriangulated

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The objects `P` with `Hom(P[-i], M) = 0` for all sufficiently negative `i`. -/
def lowHomVanishing (M : C) : ObjectProperty C :=
  fun P => ∃ N : ℤ, ∀ i : ℤ, i ≤ N → Subsingleton (P⟦-i⟧ ⟶ M)

variable (M : C)

/-- `lowHomVanishing M` is stable under retracts. -/
instance : (lowHomVanishing M).IsStableUnderRetracts where
  of_retract {X Y} r := by
    rintro ⟨N, hN⟩
    refine ⟨N, fun i hi => ⟨fun f g => ?_⟩⟩
    have key : ∀ f : X⟦-i⟧ ⟶ M, f = (r.i⟦-i⟧') ≫ (r.r⟦-i⟧' ≫ f) := fun f => by
      rw [← Category.assoc, ← Functor.map_comp, r.retract, Functor.map_id, Category.id_comp]
    rw [key f, key g, (hN i hi).elim (r.r⟦-i⟧' ≫ f) (r.r⟦-i⟧' ≫ g)]

/-- `lowHomVanishing M` is closed under isomorphisms. -/
instance : (lowHomVanishing M).IsClosedUnderIsomorphisms where
  of_iso e h := (lowHomVanishing M).prop_of_retract
    { i := e.inv, r := e.hom, retract := e.inv_hom_id } h

/-- `lowHomVanishing M` contains a zero object. -/
instance : (lowHomVanishing M).ContainsZero where
  exists_zero := by
    obtain ⟨Z, hZ⟩ := HasZeroObject.zero (C := C)
    exact ⟨Z, hZ, 0, fun i _ => ⟨fun f g => ((shiftFunctor C (-i)).map_isZero hZ).eq_of_src f g⟩⟩

/-- `lowHomVanishing M` is stable under shifts. -/
instance : (lowHomVanishing M).IsStableUnderShift ℤ where
  isStableUnderShiftBy a := ⟨fun P => by
    rintro ⟨N, hN⟩
    refine ⟨N + a, fun i hi => ?_⟩
    exact (Iso.homCongr ((shiftFunctorAdd' C a (-i) (-(i - a)) (by omega)).app P)
      (Iso.refl M)).subsingleton_congr.1 (hN (i - a) (by omega))⟩

/-- `lowHomVanishing M` contains the middle object of a distinguished triangle whose other two
objects it contains. -/
instance : (lowHomVanishing M).IsTriangulatedClosed₂ :=
  ObjectProperty.IsTriangulatedClosed₂.mk' (fun T hT ⟨N₁, h₁⟩ ⟨N₃, h₃⟩ => by
    refine ⟨min N₁ N₃, fun i hi => ⟨fun f g => ?_⟩⟩
    have hT' := Triangle.shift_distinguished T hT (-i)
    have key : ∀ f : T.obj₂⟦-i⟧ ⟶ M,
        ∃ w : ((shiftFunctor (Triangle C) (-i)).obj T).obj₃ ⟶ M,
          f = ((shiftFunctor (Triangle C) (-i)).obj T).mor₂ ≫ w := fun f =>
      Triangle.yoneda_exact₂ _ hT' f ((h₁ i (le_trans hi (min_le_left _ _))).elim _ _)
    obtain ⟨w, rfl⟩ := key f
    obtain ⟨w', rfl⟩ := key g
    rw [(h₃ i (le_trans hi (min_le_right _ _))).elim w w'])

/-- `lowHomVanishing M` is a triangulated subcategory. -/
instance : (lowHomVanishing M).IsTriangulated where

end CategoryTheory.Pretriangulated

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

attribute [local instance] smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Homology of `M` vanishes if that of its pullback along a faithful étale `w` does. -/
private theorem isZero_homology_of_isZero_homology_pullback {X Y : AlgebraicSpaces B S hS}
    (w : Y ⟶ X) (hw : IsEtale B S hS w.hom) [(modulePullback B S hS w).Faithful]
    (M : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    {N : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)}
    (e : (smallEtaleDerivedModulePullback B S hS w).obj M ≅ N) (k : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor _ k).obj N)) :
    IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) k).obj M) := by
  have hz := (h.of_iso ((DerivedCategory.homologyFunctor _ k).mapIso e)).of_iso
    (smallEtaleDerivedModulePullbackHomologyIsoOfIsEtale w hw M k).symm
  exact (IsZero.iff_id_eq_zero _).2 ((modulePullback B S hS w).map_injective (hz.eq_of_src _ _))

/-- **A perfect object of `D(𝒪_X)` is bounded** when `X` is quasi-compact. -/
theorem exists_isGE_isLE_of_isPerfect {X : AlgebraicSpaces B S hS}
    (hX : IsQuasiCompactSpace B S hS X.1) (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E) :
    ∃ a b : ℤ, E.IsGE a ∧ E.IsLE b := by
  obtain ⟨U, φ, hUa, hsurj, het⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X.1 X.2).1 hX
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hUa
  let w : schemeSpace U ⟶ X := ObjectProperty.homMk φ
  have hw : IsEtale B S hS w.hom := het
  have := faithful_modulePullback B S hS U w hw hsurj
  have hEW := isPerfect_smallEtaleDerivedModulePullback w E hE
  obtain ⟨P, hP, ⟨c, d, hc, hd⟩, ⟨eP⟩⟩ := hasStrictlyPerfectModel_of_isCompactObject_yoneda U
    ⟨_, qcohDerived_of_isPerfect_derivedCategoryB (schemeSpace U) _ hEW⟩
    (isCompactObject_of_isPerfect_yoneda U _ hEW)
  have key : ∀ k : ℤ, IsZero ((DerivedCategory.homologyFunctor _ k).obj (DerivedCategory.Q.obj P)) →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) k).obj E) := fun k hPk =>
    isZero_homology_of_isZero_homology_pullback w hw E eP k hPk
  have hPc : (DerivedCategory.Q.obj P).IsGE c := by
    rw [DerivedCategory.isGE_Q_obj_iff]
    have := hc
    infer_instance
  have hPd : (DerivedCategory.Q.obj P).IsLE d := by
    rw [DerivedCategory.isLE_Q_obj_iff]
    have := hd
    infer_instance
  refine ⟨c, d, ?_, ?_⟩
  · rw [DerivedCategory.isGE_iff] at hPc ⊢
    exact fun k hk => key k (hPc k hk)
  · rw [DerivedCategory.isLE_iff] at hPd ⊢
    exact fun k hk => key k (hPd k hk)

/-- **A perfect object of `D(𝒪_X)` is bounded above** when `X` is quasi-compact. -/
theorem exists_isLE_of_isPerfect {X : AlgebraicSpaces B S hS} (hX : IsQuasiCompactSpace B S hS X.1)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E) :
    ∃ m : ℤ, E.IsLE m :=
  let ⟨_, b, _, hb⟩ := exists_isGE_isLE_of_isPerfect hX E hE
  ⟨b, hb⟩

/-- `Hom(P[-i], E)` and `Hom(P, E[i])` vanish together. -/
theorem subsingleton_hom_shift_neg_iff {X : AlgebraicSpaces B S hS}
    (P E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (i : ℤ) :
    Subsingleton (P⟦-i⟧ ⟶ E) ↔ Subsingleton (P ⟶ E⟦i⟧) :=
  ((shiftEquiv' (DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (-i) i
    (by omega)).toAdjunction.homEquiv P E).subsingleton_congr

/-- The property of an object `E` of `D_QCoh(𝒪_X)` that `Hom(P[-i], E) = 0` for `i ≪ 0` for every
compact, that is perfect, object `P` of `D_QCoh(𝒪_X)`. -/
def LowHomVanishingOnCompact (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (E : DerivedCategory (Modules.{u, u} B S hS X hX)) : Prop :=
  ∀ P : QuasicoherentDerivedCategory.{u, u} B S hS X hX, IsCompactObject.{u} P →
    lowHomVanishing E P.obj

/-- **The affine case.** On an affine algebraic space an object `E` of `D_QCoh(𝒪_X)` with
`Hom(𝒪_X[-i], E) = 0` for `i ≪ 0` is bounded below. -/
theorem exists_isGE_of_lowHomVanishing_of_isAffineSpace
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hX : IsAlgebraicSpace B S hS X}
    (hXa : IsAffineSpace B S hS X) (E : QuasicoherentDerivedCategory.{u, u} B S hS X hX)
    (hE : LowHomVanishingOnCompact X hX E.obj) : ∃ a : ℤ, E.obj.IsGE a := by
  obtain ⟨T₀, hT₀, ⟨i⟩⟩ := hXa
  have hT := isTerminalChartOfIso (B := B) (S := S) (hS := hS) T₀ i
  have hTa : IsAffineChart B S hS X (chartOfIso B S hS T₀ i) := hT₀
  obtain ⟨N, hN⟩ := hE _ (isCompactObject_unitQuasicoherent (hX := hX) _ hT hTa)
  refine ⟨N + 1, ?_⟩
  rw [DerivedCategory.isGE_iff]
  intro q hq
  refine isZero_homology_of_forall_homFromUnit_eq_zero _ hT hTa E.obj E.property q fun g => ?_
  exact ((subsingleton_hom_shift_neg_iff (X := ⟨X, hX⟩) _ _ q).1 (hN q (by omega))).elim _ _

section Step

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}

/-- **The induction step.** Let `(U ⊆ W, j : V ⟶ W)` be an elementary distinguished square with
`W` quasi-separated, `U` quasi-compact and `V` affine, and assume that on `U` every object of
`D_QCoh` with `Hom(P[-i], -) = 0` for `i ≪ 0` and all perfect `P` is bounded below. Then the same
holds on `W`. -/
theorem exists_isGE_of_lowHomVanishing_of_eds (hZ : B.Contains (⊤_ Scheme.{u}))
    (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV) (hVa : IsAffineSpace B S hS V)
    (hUqc : IsQuasiCompactSpace B S hS Uo.toFunctor)
    (hWqs : IsAbsolutelyQuasiSeparated B S hS hZ W.1)
    (hWqc : IsQuasiCompactSpace B S hS W.1)
    (hIH : ∀ E : QuasicoherentDerivedCategory.{u, u} B S hS (edsOpen B S hS hsq).1
      (edsOpen B S hS hsq).2, LowHomVanishingOnCompact _ _ E.obj → ∃ a : ℤ, E.obj.IsGE a)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS W.1 W.2)
    (hE : LowHomVanishingOnCompact W.1 W.2 E.obj) : ∃ a : ℤ, E.obj.IsGE a := by
  have hVqc : IsQuasiCompactSpace B S hS V := hVa.isQuasiCompactSpace
  have hVqs := isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ hVa
  have hUq := isQuasiCompact_edsOpenHom B S hS hZ (hsq := hsq) hWqs hUqc
  have hUs := isQuasiSeparated_edsOpenHom B S hS hsq
  have hVq := isQuasiCompact_edsEtaleHom B S hS hZ (hsq := hsq) hWqs hVqc
  have hVs := isQuasiSeparated_edsEtaleHom B S hS hZ (hsq := hsq) hVqs
  obtain ⟨l, ha, hb⟩ := exists_list_globalRing_unitLocus B S hS hsq hZ hVa hUqc hWqs
  obtain ⟨T₀, hT₀, ⟨i⟩⟩ := hVa
  have hT := isTerminalChartOfIso (B := B) (S := S) (hS := hS) T₀ i
  have hTa : IsAffineChart B S hS V (chartOfIso B S hS T₀ i) := hT₀
  let Kd := koszul (edsEtale B S hS hsq).2 l
  have hKP : IsZero ((edsDerivedRestrictSnd B S hS hsq).obj Kd) :=
    isZero_restrictSnd_koszul hsq l hb
  have hK'qc : QcohDerived B S hS W ((edsDerivedShriekEtale B S hS hsq).obj Kd) :=
    have := isIso_derivedShriekToPushforwardEtale B S hS hsq Kd hKP
    (QcohDerived B S hS W).prop_of_iso
      (asIso (derivedShriekToPushforwardEtale B S hS hsq Kd hKP)).symm
      (qcohDerived_derivedModulePushforward_obj B S hS _ hVq hVs Kd (qcohDerived_koszul l))
  let K' : QuasicoherentDerivedCategory.{u, u} B S hS W.1 W.2 := ⟨_, hK'qc⟩
  have hK' : IsCompactObject.{u} K' :=
    isCompactObject_of_isQcohCompact B S hS W K' (isQcohCompact_lowerShriek _ _
      (isQcohCompact_of_isCompactObject B S hS (edsEtale B S hS hsq)
        (koszulQuasicoherent (edsEtale B S hS hsq).2 l)
        (isCompactObject_koszulQuasicoherent _ hT hTa l)))
  obtain ⟨N₀, hN₀⟩ := hE K' hK'
  let j := edsOpenHom B S hS hsq
  let hj := isEtale_edsOpenHom B S hS hsq
  let L := (etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategory
  let adjD := etaleDerivedModuleAdjunction B S hS j hj
  let Eu := L.obj E.obj
  let RjE := (derivedModulePushforward B S hS j).obj Eu
  obtain ⟨C, g, h, hTr⟩ := distinguished_cocone_triangle (adjD.unit.app E.obj)
  have := isIso_etaleDerivedModuleAdjunction_counit_of_mono B S hS j hj
  have hLC : IsZero (L.obj C) :=
    Triangle.isZero₃_of_isIso₁ _ (L.map_distinguished _ hTr)
      (ObjectProperty.isIso_map_unit_of_isIso_counit adjD E.obj inferInstance)
  have hsubR : ∀ n : ℤ, Subsingleton (K'.obj⟦-n⟧ ⟶ RjE) := fun n => by
    have hz : IsZero (L.obj (K'.obj⟦-n⟧)) :=
      ((shiftFunctor _ (-n)).map_isZero
        (isZero_restrictOpen_derivedShriekEtale B S hS hsq Kd hKP)).of_iso
        ((L.commShiftIso (-n)).app K'.obj)
    exact (adjD.homEquiv _ _).symm.subsingleton_congr.2 ⟨fun a b => hz.eq_of_src a b⟩
  have hsubC : ∀ n : ℤ, n + 1 ≤ N₀ → ∀ x : K'.obj⟦-n⟧ ⟶ C, x = 0 := fun n hn x => by
    have hshift : Subsingleton (K'.obj⟦-n⟧ ⟶ E.obj⟦(1 : ℤ)⟧) :=
      Stacks.DerivedTruncation.subsingleton_hom_shift_one_of_subsingleton_hom (-n) (-(n + 1))
        (by omega) (hN₀ (n + 1) hn)
    obtain ⟨v, hv⟩ := Triangle.coyoneda_exact₃ _ hTr x (hshift.elim _ _)
    rw [hv, (hsubR n).elim v 0, zero_comp]
  have hRjE : QcohDerived B S hS W RjE :=
    qcohDerived_derivedModulePushforward_obj B S hS j hUq hUs Eu
      (derivedQuasicoherent_etaleModulePullback B S hS j hj E.obj E.property)
  have hCq : QcohDerived B S hS W C :=
    (QcohDerived B S hS W).ext_of_isTriangulatedClosed₃ _ hTr E.property hRjE
  let LV := edsDerivedRestrictEtale B S hS hsq
  let M := LV.obj C
  have hMq : QcohDerived B S hS (edsEtale B S hS hsq) M :=
    derivedQuasicoherent_etaleModulePullback B S hS _ _ C hCq
  have hMP : IsZero ((edsDerivedRestrictSnd B S hS hsq).obj M) :=
    (((etaleModulePullback.{u, u} B S hS (edsFst B S hS hsq)
      (isEtale_edsFst B S hS hsq)).mapDerivedCategory.map_isZero hLC).of_iso
      ((edsDerivedRestrictInterIso B S hS hsq).app C))
  let adjS := (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory
  have horth : ∀ n : ℤ, n ≤ N₀ - 1 → ∀ x : Kd ⟶ M⟦n⟧, x = 0 := fun n hn x => by
    let φ := (LV.commShiftIso n).app C
    let y : Kd ⟶ LV.obj (C⟦n⟧) := x ≫ φ.inv
    let z : K'.obj ⟶ C⟦n⟧ := (adjS.homEquiv _ _).symm y
    let e := (shiftEquiv' (DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) (-n) n
      (by omega)).toAdjunction.homEquiv K'.obj C
    have hz : z = 0 :=
      e.symm.injective ((hsubC n (by omega) _).trans (hsubC n (by omega) _).symm)
    have hy : y = 0 := by
      rw [← (adjS.homEquiv _ _).apply_symm_apply y]
      change adjS.homEquiv _ _ z = 0
      rw [hz, Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]
    have hx : x = y ≫ φ.hom := by
      simp only [y, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hx, hy, zero_comp]
  have hMH := isZero_homology_of_hom_koszul_eq_zero (X := V) (hX := (edsEtale B S hS hsq).2)
    _ hT hTa (· ≤ N₀ - 1) l M hMq
    (vanishesWhereUnit_of_isZero_restrict (edsSnd B S hS hsq) (isEtale_edsSnd B S hS hsq) l ha
      M hMP) horth
  have hCge : C.IsGE N₀ := by
    rw [DerivedCategory.isGE_iff]
    intro q hq
    refine isZero_of_isZero_restrict_eds B S hS hsq _ ?_ ?_
    · exact ((DerivedCategory.homologyFunctor _ q).map_isZero hLC).of_iso
        (((etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategoryHomologyIso q).app C).symm
    · exact (hMH q (show q ≤ N₀ - 1 by omega)).of_iso
        (((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
          (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategoryHomologyIso q).app C).symm
  let aU := quasicoherentDerivedEtalePullback B S hS j hj
  have hEU : LowHomVanishingOnCompact _ _ (aU.obj E).obj := by
    intro P' hP'
    obtain ⟨Q, hQc, ⟨eQ⟩⟩ :=
      exists_isCompactObject_restrictOpen_iso_biprod_shift hZ hsq ⟨T₀, hT₀, ⟨i⟩⟩ hUqc hWqs P' hP'
    obtain ⟨b, hb⟩ :=
      exists_isLE_of_isPerfect hWqc Q.obj (isPerfect_of_isCompactObject W hWqs Q hQc)
    obtain ⟨NQ, hNQ⟩ := hE Q hQc
    have hLQ : lowHomVanishing Eu (L.obj Q.obj) := by
      refine ⟨min NQ (N₀ - b - 1), fun k hk => ⟨fun f₁ f₂ => ?_⟩⟩
      have hR : ∀ f' : Q.obj⟦-k⟧ ⟶ RjE, f' = 0 := fun f' => by
        have hb' : (Q.obj⟦-k⟧).IsLE (b + k) :=
          DerivedCategory.TStructure.t.isLE_shift Q.obj b (-k) (b + k) (by omega)
        have hfg : f' ≫ g = 0 :=
          DerivedCategory.TStructure.t.zero_of_isLE_of_isGE _ (b + k) N₀ (by omega) hb' hCge
        obtain ⟨v, hv⟩ := Triangle.coyoneda_exact₂ _ hTr f' hfg
        have hv0 : v = 0 := (hNQ k (le_trans hk (min_le_left _ _))).elim _ _
        rw [hv, hv0, zero_comp]
      have hsub : Subsingleton (L.obj (Q.obj⟦-k⟧) ⟶ Eu) :=
        (adjD.homEquiv _ _).subsingleton_congr.2 ⟨fun x y => (hR x).trans (hR y).symm⟩
      exact (cancel_epi ((L.commShiftIso (-k)).hom.app Q.obj)).1 (hsub.elim _ _)
    let ιU := (QcohDerived B S hS (edsOpen B S hS hsq)).ι
    let eL : L.obj Q.obj ≅ ιU.obj (P' ⊞ P'⟦(1 : ℤ)⟧) :=
      ((quasicoherentDerivedEtalePullbackCompιIso B S hS j hj).app Q).symm ≪≫ ιU.mapIso eQ
    have r : Retract P'.obj (ιU.obj (P' ⊞ P'⟦(1 : ℤ)⟧)) :=
      (Retract.mk (biprod.inl : P' ⟶ P' ⊞ P'⟦(1 : ℤ)⟧) biprod.fst biprod.inl_fst).map ιU
    exact (lowHomVanishing Eu).prop_of_retract r ((lowHomVanishing Eu).prop_of_iso eL hLQ)
  obtain ⟨m, hm⟩ := hIH (aU.obj E) hEU
  have hRm : RjE.IsGE m := by
    change DerivedCategory.TStructure.t.IsGE RjE m
    rw [DerivedCategory.TStructure.t.isGE_iff_orthogonal (m - 1) m (by omega)]
    intro A f hA
    have hA' : A.IsLE (m - 1) := hA
    have hLA : (L.obj A).IsLE (m - 1) := by
      rw [DerivedCategory.isLE_iff] at hA' ⊢
      intro q hq
      exact ((etaleModulePullback.{u, u} B S hS j hj).map_isZero (hA' q hq)).of_iso
        (((etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategoryHomologyIso q).app A)
    have : DerivedCategory.TStructure.t.IsGE Eu m := hm
    have hsub : Subsingleton (L.obj A ⟶ Eu) := ⟨fun x y => by
      rw [DerivedCategory.TStructure.t.zero x (m - 1) m (by omega),
        DerivedCategory.TStructure.t.zero y (m - 1) m (by omega)]⟩
    exact ((adjD.homEquiv A Eu).subsingleton_congr.1 hsub).elim _ _
  refine ⟨min (N₀ + 1) m, ?_⟩
  have h₁ : (C⟦(-1 : ℤ)⟧).IsGE (N₀ + 1) :=
    DerivedCategory.TStructure.t.isGE_shift C N₀ (-1) (N₀ + 1) (by omega)
  have h₁' : (C⟦(-1 : ℤ)⟧).IsGE (min (N₀ + 1) m) :=
    DerivedCategory.TStructure.t.isGE_of_ge _ _ _ (min_le_left _ _)
  have h₂' : RjE.IsGE (min (N₀ + 1) m) :=
    DerivedCategory.TStructure.t.isGE_of_ge _ _ _ (min_le_right _ _)
  exact DerivedCategory.TStructure.t.isGE₂ _ (inv_rot_of_distTriang _ hTr) _ h₁' h₂'

end Step

attribute [-instance] CategoryTheory.Limits.Types.instHasPushoutsType in
/-- **Detecting boundedness below by perfect objects.** Let `X` be a quasi-compact and
quasi-separated algebraic space and `E` an object of `D_QCoh(𝒪_X)` such that for every compact
(equivalently perfect) object `P` of `D_QCoh(𝒪_X)` the groups `Hom(P[-i], E)` vanish for
`i ≪ 0`. Then `E` is bounded below. -/
theorem exists_isGE_of_lowHomVanishingOnCompact (X : AlgebraicSpaces B S hS)
    (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    (hE : LowHomVanishingOnCompact X.1 X.2 E.obj) : ∃ a : ℤ, E.obj.IsGE a :=
  qcqs_induction_on_self B S hS B.contains_terminal X hqc hqs
    (fun Z _ => ∀ hZ' : IsAlgebraicSpace B S hS Z,
      ∀ E : QuasicoherentDerivedCategory.{u, u} B S hS Z hZ',
        LowHomVanishingOnCompact Z hZ' E.obj → ∃ a : ℤ, E.obj.IsGE a)
    (fun _ hV _ E hE => exists_isGE_of_lowHomVanishing_of_isAffineSpace hV E hE)
    (fun _ _ _ _ _ hsq hWqc hWqs hUqc hVa hPU _ _ _ E hE =>
      exists_isGE_of_lowHomVanishing_of_eds B.contains_terminal hsq hVa hUqc hWqs hWqc
        (hPU hsq.isOpenSubspace.1) E hE)
    X.2 E hE

/-- A perfect object `G` of `D(𝒪_X)` such that an object `E` of `D_QCoh(𝒪_X)` receiving no nonzero
morphism from any shift of `G` is zero is a compact weak generator of `D_QCoh(𝒪_X)`. -/
theorem isCompactObject_and_isWeakTriangulatedGenerator_of_isPerfect (X : AlgebraicSpaces B S hS)
    (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1)
    (G : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hG : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect G)
    (hgen : ∀ E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2,
      (∀ n : ℤ, Subsingleton (G⟦n⟧ ⟶ E.obj)) → IsZero E.obj) :
    IsCompactObject.{u} (⟨G, qcohDerived_of_isPerfect_derivedCategoryB X G hG⟩ :
        QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) ∧
      (ObjectProperty.singleton (⟨G, qcohDerived_of_isPerfect_derivedCategoryB X G hG⟩ :
        QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)).IsWeakTriangulatedGenerator := by
  refine ⟨isCompactObject_of_isPerfect X hqc hqs _ hG, fun K hK => ?_⟩
  let ι := (QcohDerived B S hS X).ι
  refine ObjectProperty.isZero_fullSubcategory_of_isZero_obj (hgen K fun n => ⟨fun a b => ?_⟩)
  have key : ∀ x : G⟦n⟧ ⟶ K.obj, x = 0 := fun x => by
    let G' : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2 :=
      ⟨G, qcohDerived_of_isPerfect_derivedCategoryB X G hG⟩
    have h0 := hK (ι.preimage ((ι.commShiftIso n).hom.app G' ≫ x))
      ⟨G', n, Iso.refl _, (ObjectProperty.singleton_iff _ _).2 rfl⟩
    have h1 : (ι.commShiftIso n).hom.app G' ≫ x = 0 := by
      have := congrArg ι.map h0
      rwa [Functor.map_preimage, Functor.map_zero] at this
    exact (cancel_epi ((ι.commShiftIso n).hom.app G')).1 (h1.trans comp_zero.symm)
  rw [key a, key b]

/-- **From one perfect generator to all perfect objects.** Let `G` be a compact weak generator of
`D_QCoh(𝒪_X)` and `E` an object of `D(𝒪_X)` with `Hom(G[-i], E) = 0` for `i ≪ 0`. Then
`Hom(P[-i], E) = 0` for `i ≪ 0` for every compact object `P` of `D_QCoh(𝒪_X)`. -/
theorem lowHomVanishingOnCompact_of_generator {X : AlgebraicSpaces B S hS}
    (G : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) (hGc : IsCompactObject.{u} G)
    (hG : (ObjectProperty.singleton G).IsWeakTriangulatedGenerator)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (hE : lowHomVanishing E G.obj) :
    LowHomVanishingOnCompact X.1 X.2 E := fun P hP => by
  have := isStableUnderRetracts_inverseImage (lowHomVanishing E) (QcohDerived B S hS X).ι
  exact prop_of_isCompactObject_of_isWeakTriangulatedGenerator G hGc hG
    ((lowHomVanishing E).inverseImage (QcohDerived B S hS X).ι) hE P hP

/-- **`Hom(𝒪_X[0], R𝓗om(P, E)[i]) = Hom(P, E[i])`**, as an equivalence of types: the shift
adjunction, Stacks 08J8, the compatibility of `- ⊗^L P` with the shift and `𝒪_X[0] ⊗^L P ≅ P`. -/
def homUnitShiftSmallEtaleDerivedSheafHomEquiv (X : AlgebraicSpaces B S hS)
    (P E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (i : ℤ) :
    ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj
        (SheafOfModules.unit
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) ⟶
      (((smallEtaleDerivedSheafHom B S hS X).obj (op P)).obj E)⟦i⟧) ≃ (P ⟶ E⟦i⟧) :=
  let T := smallEtaleDerivedTensorProduct B S hS X
  letI : ((smallEtaleDerivedTensor B S hS X).flip.obj P).CommShift ℤ := T.commShift_left P
  let O := (DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj
    (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)))
  let lu : ((smallEtaleDerivedTensor B S hS X).flip.obj P).obj O ≅ P :=
    ((smallEtaleDerivedTensor B S hS X).mapIso
        ((DerivedCategory.singleFunctorIsoCompQ _ 0).app _)).app P ≪≫
      (T.leftSingleUnitNatIso 0).app P ≪≫ (shiftFunctorZero' _ (-0 : ℤ) (by simp)).app P
  let e₃ : ((smallEtaleDerivedTensor B S hS X).flip.obj P).obj (O⟦-i⟧) ≅ P⟦-i⟧ :=
    (((smallEtaleDerivedTensor B S hS X).flip.obj P).commShiftIso (-i)).app O ≪≫
      (shiftFunctor _ (-i)).mapIso lu
  ((shiftEquiv' (DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (-i) i
      (by omega)).toAdjunction.homEquiv O _).symm.trans
    (((smallEtaleDerivedTensorSheafHomAdjunction B S hS X P).homEquiv _ E).symm.trans
      ((Iso.homCongr e₃ (Iso.refl E)).trans
        ((shiftEquiv' (DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (-i) i
          (by omega)).toAdjunction.homEquiv P E)))

/-- **`P ⊗^L E` is bounded below uniformly in `E`** for a perfect `P` on a quasi-compact `X`: there
is `c` with `P ⊗^L E ∈ D^{≥ a + c}` whenever `E ∈ D^{≥ a}`. -/
theorem exists_isGE_smallEtaleDerivedTensor_of_isPerfect {X : AlgebraicSpaces B S hS}
    (hX : IsQuasiCompactSpace B S hS X.1)
    (P : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hP : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) P) :
    ∃ c : ℤ, ∀ (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (a : ℤ), E.IsGE a →
      (((smallEtaleDerivedTensor B S hS X).obj P).obj E).IsGE (a + c) := by
  obtain ⟨U, φ, hUa, hsurj, het⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X.1 X.2).1 hX
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hUa
  let w : schemeSpace U ⟶ X := ObjectProperty.homMk φ
  have hw : IsEtale B S hS w.hom := het
  have := faithful_modulePullback B S hS U w hw hsurj
  have hPW := isPerfect_smallEtaleDerivedModulePullback w P hP
  obtain ⟨Q, hQ, ⟨c, d, hc, hd⟩, ⟨eQ⟩⟩ := hasStrictlyPerfectModel_of_isCompactObject_yoneda U
    ⟨_, qcohDerived_of_isPerfect_derivedCategoryB (schemeSpace U) _ hPW⟩
    (isCompactObject_of_isPerfect_yoneda U _ hPW)
  have hQb : {i : ℤ | ¬ IsZero (Q.X i)}.Finite :=
    (Set.finite_Icc c d).subset fun i hi =>
      ⟨not_lt.1 fun h => hi (Q.isZero_of_isStrictlyGE c i h),
        not_lt.1 fun h => hi (Q.isZero_of_isStrictlyLE d i h)⟩
  refine ⟨c, fun E a hE => ?_⟩
  let TW := smallEtaleDerivedTensorProduct B S hS (schemeSpace U)
  let EW := (smallEtaleDerivedModulePullback B S hS w).obj E
  let OW := (DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (schemeSpace U).1
      (schemeSpace U).2).O))
  have hEW : EW.IsGE a := by
    rw [DerivedCategory.isGE_iff] at hE ⊢
    intro k hk
    exact ((modulePullback B S hS w).map_isZero (hE k hk)).of_iso
      (smallEtaleDerivedModulePullbackHomologyIsoOfIsEtale w hw E k)
  have hHL : (((smallEtaleDerivedTensor B S hS (schemeSpace U)).obj EW).obj OW).IsGE a :=
    DerivedCategory.TStructure.t.isGE_of_iso (TW.unitIso EW).symm a
  have hW := isGE_smallEtaleDerivedTensor_tensor_of_strictlyPerfect Q hQ hQb c
    (fun i hi => Q.isZero_of_isStrictlyGE c i hi) EW OW a hHL
  let M := ((smallEtaleDerivedTensor B S hS X).obj P).obj E
  let e : (smallEtaleDerivedModulePullback B S hS w).obj M ≅
      ((smallEtaleDerivedTensor B S hS (schemeSpace U)).obj
        (((smallEtaleDerivedTensor B S hS (schemeSpace U)).obj (DerivedCategory.Q.obj Q)).obj
          EW)).obj OW :=
    (smallEtaleDerivedPullbackTensorIso w).app (P, E) ≪≫
      ((smallEtaleDerivedTensor B S hS (schemeSpace U)).mapIso eQ).app _ ≪≫
      (TW.unitIso _).symm
  rw [DerivedCategory.isGE_iff] at hW ⊢
  intro k hk
  exact isZero_homology_of_isZero_homology_pullback w hw M e k (hW k (by omega))

/-- **`P ⊗^L E` is bounded above** for a perfect `P` on a quasi-compact `X` and `E` bounded
above. -/
theorem exists_isLE_smallEtaleDerivedTensor_of_isPerfect_of_isLE {X : AlgebraicSpaces B S hS}
    (hX : IsQuasiCompactSpace B S hS X.1)
    (P : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hP : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) P)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (a : ℤ) (hE : E.IsLE a) :
    ∃ m : ℤ, (((smallEtaleDerivedTensor B S hS X).obj P).obj E).IsLE m := by
  obtain ⟨K, hK, ⟨eK⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE E a
  obtain ⟨m, hm⟩ := exists_isLE_smallEtaleDerivedTensor_of_isPerfect hX P hP K a
    (fun i hi => K.isZero_of_isStrictlyLE a i hi)
  refine ⟨m, ?_⟩
  rw [DerivedCategory.isLE_iff] at hm ⊢
  intro q hq
  exact (hm q hq).of_iso ((DerivedCategory.homologyFunctor _ q).mapIso
    (((smallEtaleDerivedTensor B S hS X).obj P).mapIso eK))

end AlgebraicGeometry.Space

end
