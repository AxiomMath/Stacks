module

public import StacksFrontier.AlgebraicGeometry.Spaces.DualityRightAdjointBoundedBelow
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CompactHomVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffinePerfectSectionsLocalModels
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSetBaseChangeMateIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.InterfaceUnitNaturality
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposFlatModule

/-!
# Detecting boundedness above on a quasi-compact quasi-separated algebraic space

Let `X` be a quasi-compact and quasi-separated algebraic space and `E` an object of
`D_QCoh(𝒪_X)`. If for every perfect object `P` of `D(𝒪_X)` the groups `Hom(P[-i], E)` vanish for
`i ≫ 0`, then `E` is bounded above. This is the implication "(7) ⇒ (1)" of Stacks 0GFH, proved by
the induction principle of Stacks 08GP exactly as its bounded-below sibling
`AlgebraicGeometry.Space.exists_isGE_of_lowHomVanishingOnCompact`, with Stacks 08FA bounding
`Rj_*(E|_U)` above and the bound of Stacks 09MB on morphisms out of a compact object replacing the
t-structure orthogonality.

## Main results

* `CategoryTheory.Pretriangulated.highHomVanishing`: the objects `P` with `Hom(P[-i], M) = 0` for
  `i ≫ 0`, a triangulated subcategory stable under retracts.
* `AlgebraicGeometry.Space.exists_isLE_of_highHomVanishingOnCompact`: the implication above.

## References

* [Stacks Project, Tag 0GFH](https://stacks.math.columbia.edu/tag/0GFH)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Pretriangulated

namespace CategoryTheory.Pretriangulated

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The objects `P` with `Hom(P[-i], M) = 0` for all sufficiently large `i`. -/
def highHomVanishing (M : C) : ObjectProperty C :=
  fun P => ∃ N : ℤ, ∀ i : ℤ, N ≤ i → Subsingleton (P⟦-i⟧ ⟶ M)

variable (M : C)

/-- `highHomVanishing M` is stable under retracts. -/
instance : (highHomVanishing M).IsStableUnderRetracts where
  of_retract {X Y} r := by
    rintro ⟨N, hN⟩
    refine ⟨N, fun i hi => ⟨fun f g => ?_⟩⟩
    have key : ∀ f : X⟦-i⟧ ⟶ M, f = (r.i⟦-i⟧') ≫ (r.r⟦-i⟧' ≫ f) := fun f => by
      rw [← Category.assoc, ← Functor.map_comp, r.retract, Functor.map_id, Category.id_comp]
    rw [key f, key g, (hN i hi).elim (r.r⟦-i⟧' ≫ f) (r.r⟦-i⟧' ≫ g)]

/-- `highHomVanishing M` is closed under isomorphisms. -/
instance : (highHomVanishing M).IsClosedUnderIsomorphisms where
  of_iso e h := (highHomVanishing M).prop_of_retract
    { i := e.inv, r := e.hom, retract := e.inv_hom_id } h

/-- `highHomVanishing M` contains a zero object. -/
instance : (highHomVanishing M).ContainsZero where
  exists_zero := by
    obtain ⟨Z, hZ⟩ := HasZeroObject.zero (C := C)
    exact ⟨Z, hZ, 0, fun i _ => ⟨fun f g => ((shiftFunctor C (-i)).map_isZero hZ).eq_of_src f g⟩⟩

/-- `highHomVanishing M` is stable under all shifts `[a]`, `a : ℤ`. -/
instance : (highHomVanishing M).IsStableUnderShift ℤ where
  isStableUnderShiftBy a := ⟨fun P => by
    rintro ⟨N, hN⟩
    refine ⟨N + a, fun i hi => ?_⟩
    have e := (shiftFunctorAdd' C a (-i) (-(i - a)) (by omega)).app P
    exact (Iso.homCongr e (Iso.refl M)).subsingleton_congr.1 (hN (i - a) (by omega))⟩

/-- If `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁[1]` is distinguished and `X₁`, `X₃` satisfy `highHomVanishing M`, then so
does `X₂`. -/
instance : (highHomVanishing M).IsTriangulatedClosed₂ :=
  ObjectProperty.IsTriangulatedClosed₂.mk' (fun T hT ⟨N₁, h₁⟩ ⟨N₃, h₃⟩ => by
    refine ⟨max N₁ N₃, fun i hi => ⟨fun f g => ?_⟩⟩
    have hT' := Triangle.shift_distinguished T hT (-i)
    have key : ∀ f : T.obj₂⟦-i⟧ ⟶ M,
        ∃ w : ((shiftFunctor (Triangle C) (-i)).obj T).obj₃ ⟶ M,
          f = ((shiftFunctor (Triangle C) (-i)).obj T).mor₂ ≫ w := fun f =>
      Triangle.yoneda_exact₂ _ hT' f ((h₁ i (le_trans (le_max_left _ _) hi)).elim _ _)
    obtain ⟨w, rfl⟩ := key f
    obtain ⟨w', rfl⟩ := key g
    rw [(h₃ i (le_trans (le_max_right _ _) hi)).elim w w'])

/-- `highHomVanishing M` is a triangulated subcategory. -/
instance : (highHomVanishing M).IsTriangulated where

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

/-- The property of an object `E` of `D_QCoh(𝒪_X)` that `Hom(P[-i], E) = 0` for `i ≫ 0` for every
compact, that is perfect, object `P` of `D_QCoh(𝒪_X)`. -/
def HighHomVanishingOnCompact (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (E : DerivedCategory (Modules.{u, u} B S hS X hX)) : Prop :=
  ∀ P : QuasicoherentDerivedCategory.{u, u} B S hS X hX, IsCompactObject.{u} P →
    highHomVanishing E P.obj

/-- **The affine case.** On an affine algebraic space an object `E` of `D_QCoh(𝒪_X)` with
`Hom(𝒪_X[-i], E) = 0` for `i ≫ 0` is bounded above. -/
theorem exists_isLE_of_highHomVanishing_of_isAffineSpace
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hX : IsAlgebraicSpace B S hS X}
    (hXa : IsAffineSpace B S hS X) (E : QuasicoherentDerivedCategory.{u, u} B S hS X hX)
    (hE : HighHomVanishingOnCompact X hX E.obj) : ∃ a : ℤ, E.obj.IsLE a := by
  obtain ⟨T₀, hT₀, ⟨i⟩⟩ := hXa
  have hT := isTerminalChartOfIso (B := B) (S := S) (hS := hS) T₀ i
  have hTa : IsAffineChart B S hS X (chartOfIso B S hS T₀ i) := hT₀
  obtain ⟨N, hN⟩ := hE _ (isCompactObject_unitQuasicoherent (hX := hX) _ hT hTa)
  refine ⟨N - 1, ?_⟩
  rw [DerivedCategory.isLE_iff]
  intro q hq
  refine isZero_homology_of_forall_homFromUnit_eq_zero _ hT hTa E.obj E.property q fun g => ?_
  exact ((subsingleton_hom_shift_neg_iff (X := ⟨X, hX⟩) _ _ q).1 (hN q (by omega))).elim _ _

section Step

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}

/-- **The induction step.** Let `(U ⊆ W, j : V ⟶ W)` be an elementary distinguished square with
`W` quasi-compact and quasi-separated, `U` quasi-compact and `V` affine, and assume that on `U`
every object of `D_QCoh` with `Hom(P[-i], -) = 0` for `i ≫ 0` and all perfect `P` is bounded
above. Then the same holds on `W`. -/
theorem exists_isLE_of_highHomVanishing_of_eds (hZ : B.Contains (⊤_ Scheme.{u}))
    (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV) (hVa : IsAffineSpace B S hS V)
    (hUqc : IsQuasiCompactSpace B S hS Uo.toFunctor)
    (hWqs : IsAbsolutelyQuasiSeparated B S hS hZ W.1)
    (hWqc : IsQuasiCompactSpace B S hS W.1)
    (hIH : ∀ E : QuasicoherentDerivedCategory.{u, u} B S hS (edsOpen B S hS hsq).1
      (edsOpen B S hS hsq).2, HighHomVanishingOnCompact _ _ E.obj → ∃ a : ℤ, E.obj.IsLE a)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS W.1 W.2)
    (hE : HighHomVanishingOnCompact W.1 W.2 E.obj) : ∃ a : ℤ, E.obj.IsLE a := by
  have hUq := isQuasiCompact_edsOpenHom B S hS hZ (hsq := hsq) hWqs hUqc
  have hUs := isQuasiSeparated_edsOpenHom B S hS hsq
  have hVq := isQuasiCompact_edsEtaleHom B S hS hZ (hsq := hsq) hWqs hVa.isQuasiCompactSpace
  have hVs := isQuasiSeparated_edsEtaleHom B S hS hZ (hsq := hsq)
    (isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ hVa)
  obtain ⟨l, ha, hb⟩ := exists_list_globalRing_unitLocus B S hS hsq hZ hVa hUqc hWqs
  obtain ⟨T₀, hT₀, ⟨i⟩⟩ := hVa
  have hT := isTerminalChartOfIso (B := B) (S := S) (hS := hS) T₀ i
  have hTa : IsAffineChart B S hS V (chartOfIso B S hS T₀ i) := hT₀
  let Kd := koszul (edsEtale B S hS hsq).2 l
  have hKP : IsZero ((edsDerivedRestrictSnd B S hS hsq).obj Kd) :=
    isZero_restrictSnd_koszul hsq l hb
  -- the Koszul object extended by zero to `W`, a compact object of `D_QCoh(𝒪_W)`
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
  -- the cone `C` of `E ⟶ Rj_*(E|_U)`
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
  -- `Hom((j_!K)[-n], Rj_*(E|_U)) = 0`
  have hsubR : ∀ n : ℤ, Subsingleton (K'.obj⟦-n⟧ ⟶ RjE) := fun n => by
    have hz : IsZero (L.obj (K'.obj⟦-n⟧)) :=
      ((shiftFunctor _ (-n)).map_isZero
        (isZero_restrictOpen_derivedShriekEtale B S hS hsq Kd hKP)).of_iso
        ((L.commShiftIso (-n)).app K'.obj)
    exact (adjD.homEquiv _ _).symm.subsingleton_congr.2 ⟨fun a b => hz.eq_of_src a b⟩
  -- `Hom((j_!K)[-n], C) = 0` for `n ≥ N₀ - 1`
  have hsubC : ∀ n : ℤ, N₀ ≤ n + 1 → ∀ x : K'.obj⟦-n⟧ ⟶ C, x = 0 := fun n hn x => by
    have hshift : Subsingleton (K'.obj⟦-n⟧ ⟶ E.obj⟦(1 : ℤ)⟧) :=
      Stacks.DerivedTruncation.subsingleton_hom_shift_one_of_subsingleton_hom (-n) (-(n + 1))
        (by omega) (hN₀ (n + 1) hn)
    obtain ⟨v, hv⟩ := Triangle.coyoneda_exact₃ _ hTr x (hshift.elim _ _)
    rw [hv, (hsubR n).elim v 0, zero_comp]
  -- `C` has quasi-coherent cohomology
  have hRjE : QcohDerived B S hS W RjE :=
    qcohDerived_derivedModulePushforward_obj B S hS j hUq hUs Eu
      (derivedQuasicoherent_etaleModulePullback B S hS j hj E.obj E.property)
  have hCq : QcohDerived B S hS W C :=
    (QcohDerived B S hS W).ext_of_isTriangulatedClosed₃ _ hTr E.property hRjE
  -- restriction of `C` to `V`
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
  have horth : ∀ n : ℤ, N₀ - 1 ≤ n → ∀ x : Kd ⟶ M⟦n⟧, x = 0 := fun n hn x => by
    let φ := (LV.commShiftIso n).app C
    let y : Kd ⟶ LV.obj (C⟦n⟧) := x ≫ φ.inv
    let z : K'.obj ⟶ C⟦n⟧ := (adjS.homEquiv _ _).symm y
    have hz : z = 0 :=
      ((subsingleton_hom_shift_neg_iff (X := W) K'.obj C n).1
        ⟨fun a b => (hsubC n (by omega) a).trans (hsubC n (by omega) b).symm⟩).elim _ _
    have hy : y = 0 := by
      rw [← (adjS.homEquiv _ _).apply_symm_apply y]
      show adjS.homEquiv _ _ z = 0
      rw [hz, Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]
    have hx : x = y ≫ φ.hom := by
      simp only [y, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hx, hy, zero_comp]
  have hMH := isZero_homology_of_hom_koszul_eq_zero (X := V) (hX := (edsEtale B S hS hsq).2)
    _ hT hTa (N₀ - 1 ≤ ·) l M hMq
    (vanishesWhereUnit_of_isZero_restrict (edsSnd B S hS hsq) (isEtale_edsSnd B S hS hsq) l ha
      M hMP) horth
  -- `C` is bounded above by `N₀ - 2`
  have hCle : C.IsLE (N₀ - 2) := by
    rw [DerivedCategory.isLE_iff]
    intro q hq
    refine isZero_of_isZero_restrict_eds B S hS hsq _ ?_ ?_
    · exact ((DerivedCategory.homologyFunctor _ q).map_isZero hLC).of_iso
        (((etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategoryHomologyIso q).app C).symm
    · exact (hMH q (show N₀ - 1 ≤ q by omega)).of_iso
        (((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
          (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategoryHomologyIso q).app C).symm
  -- the restriction of `E` to `U` satisfies the hypothesis on `U`
  let aU := quasicoherentDerivedEtalePullback B S hS j hj
  have hEU : HighHomVanishingOnCompact _ _ (aU.obj E).obj := by
    intro P' hP'
    obtain ⟨Q, hQc, ⟨eQ⟩⟩ :=
      exists_isCompactObject_restrictOpen_iso_biprod_shift hZ hsq ⟨T₀, hT₀, ⟨i⟩⟩ hUqc hWqs P' hP'
    obtain ⟨b, hb⟩ := exists_hom_eq_zero_of_isCompactObject W hWqc hWqs Q hQc
    obtain ⟨NQ, hNQ⟩ := hE Q hQc
    have hLQ : highHomVanishing Eu (L.obj Q.obj) := by
      refine ⟨max NQ (N₀ - 2 + b), fun k hk => ⟨fun f₁ f₂ => ?_⟩⟩
      have hR : ∀ f' : Q.obj⟦-k⟧ ⟶ RjE, f' = 0 := fun f' => by
        have hfg : f' ≫ g = 0 := by
          have hC'' : (C⟦k⟧).IsLE (N₀ - 2 - k) :=
            DerivedCategory.TStructure.t.isLE_shift C (N₀ - 2) k (N₀ - 2 - k) (by omega)
          have hC' : (C⟦k⟧).IsLE (-b) :=
            DerivedCategory.TStructure.t.isLE_of_le _ (N₀ - 2 - k) (-b)
              (by have := le_trans (le_max_right _ _) hk; omega)
          have h0 := hb (C⟦k⟧) (qcohDerived_shift C k hCq) hC'
          exact ((subsingleton_hom_shift_neg_iff Q.obj C k).2
            ⟨fun x y => (h0 x).trans (h0 y).symm⟩).elim _ _
        obtain ⟨v, hv⟩ := Triangle.coyoneda_exact₂ _ hTr f' hfg
        rw [hv, (hNQ k (le_trans (le_max_left _ _) hk)).elim v 0, zero_comp]
      have hsub : Subsingleton (L.obj (Q.obj⟦-k⟧) ⟶ Eu) :=
        (adjD.homEquiv _ _).subsingleton_congr.2 ⟨fun x y => (hR x).trans (hR y).symm⟩
      exact (cancel_epi ((L.commShiftIso (-k)).hom.app Q.obj)).1 (hsub.elim _ _)
    let ιU := (QcohDerived B S hS (edsOpen B S hS hsq)).ι
    let eL : L.obj Q.obj ≅ ιU.obj (P' ⊞ P'⟦(1 : ℤ)⟧) :=
      ((quasicoherentDerivedEtalePullbackCompιIso B S hS j hj).app Q).symm ≪≫ ιU.mapIso eQ
    have r : Retract P'.obj (ιU.obj (P' ⊞ P'⟦(1 : ℤ)⟧)) :=
      (Retract.mk (biprod.inl : P' ⟶ P' ⊞ P'⟦(1 : ℤ)⟧) biprod.fst biprod.inl_fst).map ιU
    exact (highHomVanishing Eu).prop_of_retract r ((highHomVanishing Eu).prop_of_iso eL hLQ)
  obtain ⟨m, hm⟩ := hIH (aU.obj E) hEU
  -- `Rj_*(E|_U)` is bounded above
  obtain ⟨Nj, hNj⟩ := exists_isLE_derivedModulePushforward_obj j hUq hUs hWqc
  have hRm : RjE.IsLE (m + Nj) := hNj Eu (derivedQuasicoherent_etaleModulePullback B S hS j hj
    E.obj E.property) m hm
  refine ⟨max (N₀ - 1) (m + Nj), ?_⟩
  have h₁ : (C⟦(-1 : ℤ)⟧).IsLE (N₀ - 1) :=
    DerivedCategory.TStructure.t.isLE_shift C (N₀ - 2) (-1) (N₀ - 1) (by omega)
  have h₁' : (C⟦(-1 : ℤ)⟧).IsLE (max (N₀ - 1) (m + Nj)) :=
    DerivedCategory.TStructure.t.isLE_of_le _ _ _ (le_max_left _ _)
  have h₂' : RjE.IsLE (max (N₀ - 1) (m + Nj)) :=
    DerivedCategory.TStructure.t.isLE_of_le _ _ _ (le_max_right _ _)
  exact DerivedCategory.TStructure.t.isLE₂ _ (inv_rot_of_distTriang _ hTr) _ h₁' h₂'

end Step

attribute [-instance] CategoryTheory.Limits.Types.instHasPushoutsType in
/-- **Detecting boundedness above by perfect objects.** Let `X` be a quasi-compact and
quasi-separated algebraic space and `E` an object of `D_QCoh(𝒪_X)` such that for every compact
(equivalently perfect) object `P` of `D_QCoh(𝒪_X)` the groups `Hom(P[-i], E)` vanish for
`i ≫ 0`. Then `E` is bounded above. -/
theorem exists_isLE_of_highHomVanishingOnCompact (X : AlgebraicSpaces B S hS)
    (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    (hE : HighHomVanishingOnCompact X.1 X.2 E.obj) : ∃ a : ℤ, E.obj.IsLE a :=
  qcqs_induction_on_self B S hS B.contains_terminal X hqc hqs
    (fun Z _ => ∀ hZ' : IsAlgebraicSpace B S hS Z,
      ∀ E : QuasicoherentDerivedCategory.{u, u} B S hS Z hZ',
        HighHomVanishingOnCompact Z hZ' E.obj → ∃ a : ℤ, E.obj.IsLE a)
    (fun _ hV _ E hE => exists_isLE_of_highHomVanishing_of_isAffineSpace hV E hE)
    (fun _ _ _ _ _ hsq hWqc hWqs hUqc hVa hPU _ _ _ E hE =>
      exists_isLE_of_highHomVanishing_of_eds B.contains_terminal hsq hVa hUqc hWqs hWqc
        (hPU hsq.isOpenSubspace.1) E hE)
    X.2 E hE

/-- **From one perfect generator to all perfect objects.** Let `G` be a compact weak generator of
`D_QCoh(𝒪_X)` and `E` an object of `D(𝒪_X)` with `Hom(G[-i], E) = 0` for `i ≫ 0`. Then
`Hom(P[-i], E) = 0` for `i ≫ 0` for every compact object `P` of `D_QCoh(𝒪_X)` (Stacks 09SR). -/
theorem highHomVanishingOnCompact_of_generator {X : AlgebraicSpaces B S hS}
    (G : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) (hGc : IsCompactObject.{u} G)
    (hG : (ObjectProperty.singleton G).IsWeakTriangulatedGenerator)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (hE : highHomVanishing E G.obj) :
    HighHomVanishingOnCompact X.1 X.2 E := fun P hP => by
  have := isStableUnderRetracts_inverseImage (highHomVanishing E) (QcohDerived B S hS X).ι
  exact prop_of_isCompactObject_of_isWeakTriangulatedGenerator G hGc hG
    ((highHomVanishing E).inverseImage (QcohDerived B S hS X).ι) hE P hP

end AlgebraicGeometry.Space

end
