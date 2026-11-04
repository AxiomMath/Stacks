module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DetectingBoundedBelow
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisExtTag

/-!
# Morphisms from a perfect object into objects bounded far above

Let `X` be a quasi-compact and quasi-separated algebraic space and `P` a perfect, equivalently
compact, object of `D_QCoh(𝒪_X)`. There is an integer `N` such that every morphism `P ⟶ L` into an
object `L` of `D_QCoh(𝒪_X)` with `H^i(L) = 0` for `i > -N` vanishes. This is the half of
Stacks 09MB (1) bounding the degrees from above.

## Main results

* `CategoryTheory.Pretriangulated.upHomVanishing`: the objects `P` with `Hom(P, L) = 0` for every
  `L` of a shift-stable class lying far enough to the left.
* `AlgebraicGeometry.Space.exists_hom_eq_zero_of_isCompactObject`: the bound.

## References

* [Stacks Project, Tag 09MB](https://stacks.math.columbia.edu/tag/09MB)
* [Stacks Project, Tag 08H9](https://stacks.math.columbia.edu/tag/08H9)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Pretriangulated

namespace CategoryTheory.Pretriangulated

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- The objects `P` of `D(C)` such that `Hom(P, L) = 0` for all `L` satisfying `Q` and lying in
degrees `≤ -N`, for some `N`. -/
def upHomVanishing (Q : ObjectProperty (DerivedCategory C)) : ObjectProperty (DerivedCategory C) :=
  fun P => ∃ N : ℤ, ∀ L : DerivedCategory C, Q L → L.IsLE (-N) → Subsingleton (P ⟶ L)

variable (Q : ObjectProperty (DerivedCategory C)) [Q.IsStableUnderShift ℤ]

/-- `upHomVanishing Q` is stable under retracts. -/
instance : (upHomVanishing Q).IsStableUnderRetracts where
  of_retract {X Y} r := by
    rintro ⟨N, hN⟩
    refine ⟨N, fun L hL hLN => ⟨fun f g => ?_⟩⟩
    have key : ∀ f : X ⟶ L, f = r.i ≫ (r.r ≫ f) := fun f => by
      rw [← Category.assoc, r.retract, Category.id_comp]
    rw [key f, key g, (hN L hL hLN).elim (r.r ≫ f) (r.r ≫ g)]

/-- `upHomVanishing Q` is closed under isomorphisms. -/
instance : (upHomVanishing Q).IsClosedUnderIsomorphisms where
  of_iso e h := (upHomVanishing Q).prop_of_retract
    { i := e.inv, r := e.hom, retract := e.inv_hom_id } h

/-- `upHomVanishing Q` contains a zero object. -/
instance : (upHomVanishing Q).ContainsZero where
  exists_zero := by
    obtain ⟨Z, hZ⟩ := HasZeroObject.zero (C := DerivedCategory C)
    exact ⟨Z, hZ, 0, fun _ _ _ => ⟨fun f g => hZ.eq_of_src f g⟩⟩

/-- `upHomVanishing Q` is stable under shifts. -/
instance : (upHomVanishing Q).IsStableUnderShift ℤ where
  isStableUnderShiftBy a := ⟨fun P => by
    rintro ⟨N, hN⟩
    refine ⟨N + a, fun L hL hLN => ?_⟩
    have h₁ : (L⟦-a⟧).IsLE (-N) :=
      DerivedCategory.TStructure.t.isLE_shift L (-(N + a)) (-a) (-N) (by omega)
    exact ((shiftEquiv' (DerivedCategory C) a (-a) (by omega)).toAdjunction.homEquiv P L
      ).subsingleton_congr.2 (hN _ (Q.le_shift (-a) L hL) h₁)⟩

/-- `upHomVanishing Q` contains the middle object of a distinguished triangle whose other two
objects it contains. -/
instance : (upHomVanishing Q).IsTriangulatedClosed₂ :=
  ObjectProperty.IsTriangulatedClosed₂.mk' (fun T hT ⟨N₁, h₁⟩ ⟨N₃, h₃⟩ => by
    refine ⟨max N₁ N₃, fun L hL hLN => ⟨fun f g => ?_⟩⟩
    have key : ∀ f : T.obj₂ ⟶ L, ∃ w : T.obj₃ ⟶ L, f = T.mor₂ ≫ w := fun f =>
      Triangle.yoneda_exact₂ _ hT f ((h₁ L hL
        (DerivedCategory.TStructure.t.isLE_of_le L (-max N₁ N₃) (-N₁) (by omega))).elim _ _)
    obtain ⟨w, rfl⟩ := key f
    obtain ⟨w', rfl⟩ := key g
    rw [(h₃ L hL (DerivedCategory.TStructure.t.isLE_of_le L (-max N₁ N₃) (-N₃)
      (by omega))).elim w w'])

/-- `upHomVanishing Q` is a triangulated subcategory. -/
instance : (upHomVanishing Q).IsTriangulated where

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

/-- The bound for one compact object `K` of `D_QCoh(𝒪_X)`. -/
def HomVanishingFarLeft (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (K : DerivedCategory (Modules.{u, u} B S hS X hX)) : Prop :=
  ∃ N : ℤ, ∀ L : DerivedCategory (Modules.{u, u} B S hS X hX), QcohDerived B S hS ⟨X, hX⟩ L →
    L.IsLE (-N) → ∀ f : K ⟶ L, f = 0

/-- The objects of `D(𝒪_X)` with quasi-coherent cohomology are stable under shifts. -/
instance (X : AlgebraicSpaces B S hS) : (QcohDerived B S hS X).IsStableUnderShift ℤ where
  isStableUnderShiftBy a := ⟨fun E hE => qcohDerived_shift E a hE⟩

/-- `HomVanishingFarLeft` is `upHomVanishing` for the objects with quasi-coherent cohomology. -/
theorem homVanishingFarLeft_iff (X : AlgebraicSpaces B S hS)
    (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) :
    HomVanishingFarLeft X.1 X.2 K ↔ upHomVanishing (QcohDerived B S hS X) K :=
  ⟨fun ⟨N, h⟩ => ⟨N, fun L hL hLN => ⟨fun f g => (h L hL hLN f).trans (h L hL hLN g).symm⟩⟩,
    fun ⟨N, h⟩ => ⟨N, fun L hL hLN f => (h L hL hLN).elim f 0⟩⟩

/-- **The affine case**: on an affine algebraic space every compact object of `D_QCoh(𝒪_X)` has the
bound, `𝒪_X` having it with `N = 1`. -/
theorem homVanishingFarLeft_of_isAffineSpace {X : AlgebraicSpaces B S hS}
    (hXa : IsAffineSpace B S hS X.1) (K : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    (hK : IsCompactObject.{u} K) : HomVanishingFarLeft X.1 X.2 K.obj := by
  obtain ⟨hOc, hOg⟩ := isCompactObject_and_isWeakTriangulatedGenerator_unitQuasicoherent
    (hX := X.2) hXa
  have := isStableUnderRetracts_inverseImage (upHomVanishing (QcohDerived B S hS X))
    (QcohDerived B S hS X).ι
  rw [homVanishingFarLeft_iff]
  refine prop_of_isCompactObject_of_isWeakTriangulatedGenerator _ hOc hOg
    ((upHomVanishing (QcohDerived B S hS X)).inverseImage (QcohDerived B S hS X).ι) ?_ K hK
  obtain ⟨T₀, hT₀, ⟨i⟩⟩ := hXa
  have hT := isTerminalChartOfIso (B := B) (S := S) (hS := hS) T₀ i
  have hTa : IsAffineChart B S hS X.1 (chartOfIso B S hS T₀ i) := hT₀
  refine (homVanishingFarLeft_iff X _).1 ⟨1, fun L hL hLN f => ?_⟩
  exact homFromUnit_eq_zero_of_isLE _ hT hTa L hL hLN f

/-- Restriction along an étale morphism preserves the vanishing of the cohomology sheaves above a
degree. -/
theorem isLE_etaleModulePullback_mapDerivedCategory_obj {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hf : IsEtale B S hS f.hom) (L : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (n : ℤ)
    (hL : L.IsLE n) :
    ((etaleModulePullback.{u, u} B S hS f hf).mapDerivedCategory.obj L).IsLE n := by
  rw [DerivedCategory.isLE_iff] at hL ⊢
  intro q hq
  exact ((etaleModulePullback.{u, u} B S hS f hf).map_isZero (hL q hq)).of_iso
    (((etaleModulePullback.{u, u} B S hS f hf).mapDerivedCategoryHomologyIso q).app L)

/-- A shift of an object bounded above by `m` is bounded above by `n` if `m ≤ n + a`. -/
private theorem isLE_shift_of_isLE_of_le {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (L : DerivedCategory C) (a : ℤ) {m n : ℤ} (h : L.IsLE m) (hmn : m ≤ n + a) :
    (L⟦a⟧).IsLE n :=
  have := DerivedCategory.TStructure.t.isLE_shift L m a (m - a) (by omega)
  DerivedCategory.TStructure.t.isLE_of_le _ (m - a) n (by omega)

section Step

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}

/-- **The induction step.** Let `(U ⊆ W, V ⟶ W)` be an elementary distinguished square with `W`
quasi-separated, `U` quasi-compact and `V` affine. If every compact object of `D_QCoh` on `U`, on
`V` and on `U ×_W V` has the bound, then so does every compact object of `D_QCoh(𝒪_W)`. -/
theorem homVanishingFarLeft_of_eds (hZ : B.Contains (⊤_ Scheme.{u}))
    (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV) (hVa : IsAffineSpace B S hS V)
    (hUqc : IsQuasiCompactSpace B S hS Uo.toFunctor)
    (hWqs : IsAbsolutelyQuasiSeparated B S hS hZ W.1)
    (hU : ∀ K : QuasicoherentDerivedCategory.{u, u} B S hS (edsOpen B S hS hsq).1
      (edsOpen B S hS hsq).2, IsCompactObject.{u} K → HomVanishingFarLeft _ _ K.obj)
    (hV : ∀ K : QuasicoherentDerivedCategory.{u, u} B S hS (edsEtale B S hS hsq).1
      (edsEtale B S hS hsq).2, IsCompactObject.{u} K → HomVanishingFarLeft _ _ K.obj)
    (hP : ∀ K : QuasicoherentDerivedCategory.{u, u} B S hS (edsInter B S hS hsq).1
      (edsInter B S hS hsq).2, IsCompactObject.{u} K → HomVanishingFarLeft _ _ K.obj)
    (K : QuasicoherentDerivedCategory.{u, u} B S hS W.1 W.2) (hK : IsCompactObject.{u} K) :
    HomVanishingFarLeft W.1 W.2 K.obj := by
  have hVqc : IsQuasiCompactSpace B S hS V := hVa.isQuasiCompactSpace
  have hVqs := isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ hVa
  have hUq := isQuasiCompact_edsOpenHom B S hS hZ (hsq := hsq) hWqs hUqc
  have hUs := isQuasiSeparated_edsOpenHom B S hS hsq
  have hVq := isQuasiCompact_edsEtaleHom B S hS hZ (hsq := hsq) hWqs hVqc
  have hVs := isQuasiSeparated_edsEtaleHom B S hS hZ (hsq := hsq) hVqs
  have hPqc := isQuasiCompactSpace_edsInter B S hS hZ (hsq := hsq) hUqc hVqc hWqs
  have hFq := isQuasiCompact_edsFst B S hS hZ (hsq := hsq) hWqs hPqc
  have hFs := isQuasiSeparated_edsFst B S hS hZ (hsq := hsq) hVqs
  let aU := quasicoherentDerivedEtalePullback B S hS (edsOpenHom B S hS hsq)
    (isEtale_edsOpenHom B S hS hsq)
  let aV := quasicoherentDerivedEtalePullback B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq)
  let bU := quasicoherentDerivedEtalePullback B S hS (edsFst B S hS hsq) (isEtale_edsFst B S hS hsq)
  have hKU := isCompactObject_quasicoherentDerivedEtalePullback_obj B S hS _
    (isEtale_edsOpenHom B S hS hsq) hUq hUs hK
  have hKV := isCompactObject_quasicoherentDerivedEtalePullback_obj B S hS _
    (isEtale_edsEtaleHom B S hS hsq) hVq hVs hK
  have hKP := isCompactObject_quasicoherentDerivedEtalePullback_obj B S hS _
    (isEtale_edsFst B S hS hsq) hFq hFs hKU
  obtain ⟨NU, hNU⟩ := hU (aU.obj K) hKU
  obtain ⟨NV, hNV⟩ := hV (aV.obj K) hKV
  obtain ⟨NP, hNP⟩ := hP (bU.obj (aU.obj K)) hKP
  refine ⟨max NU (max NV (NP + 1)), fun L hL hLN f => ?_⟩
  obtain ⟨res, dif, bd, hex⟩ :=
    exists_mayerVietoris_derivedHom_longExactSequence_of_eds_lowerShriek B S hS hsq K.obj L
  let rU := (etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
    (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategory
  let rV := (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory
  let rF := (etaleModulePullback.{u, u} B S hS (edsFst B S hS hsq)
    (isEtale_edsFst B S hS hsq)).mapDerivedCategory
  let rP := (etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
    (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory
  have hLU : QcohDerived B S hS (edsOpen B S hS hsq) (rU.obj L) :=
    derivedQuasicoherent_etaleModulePullback B S hS _ _ L hL
  have hLV : QcohDerived B S hS (edsEtale B S hS hsq) (rV.obj L) :=
    derivedQuasicoherent_etaleModulePullback B S hS _ _ L hL
  have hLP : QcohDerived B S hS (edsInter B S hS hsq) (rF.obj (rU.obj L)) :=
    derivedQuasicoherent_etaleModulePullback B S hS _ _ _ hLU
  have hLU' : ((rU.obj L)⟦(-1 : ℤ) + 1⟧).IsLE (-NU) :=
    isLE_shift_of_isLE_of_le _ _ (isLE_etaleModulePullback_mapDerivedCategory_obj
      (edsOpenHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq) L _ hLN) (by omega)
  have hLV' : ((rV.obj L)⟦(-1 : ℤ) + 1⟧).IsLE (-NV) :=
    isLE_shift_of_isLE_of_le _ _ (isLE_etaleModulePullback_mapDerivedCategory_obj
      (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq) L _ hLN) (by omega)
  have hLP' : ((rF.obj (rU.obj L))⟦(-1 : ℤ)⟧).IsLE (-NP) :=
    isLE_shift_of_isLE_of_le _ _ (isLE_etaleModulePullback_mapDerivedCategory_obj
      (edsFst B S hS hsq) (isEtale_edsFst B S hS hsq) _ _
      (isLE_etaleModulePullback_mapDerivedCategory_obj (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq) L _ hLN)) (by omega)
  have h0 : ((-1 : ℤ) + 1) = 0 := by norm_num
  let x : K.obj ⟶ L⟦(-1 : ℤ) + 1⟧ := f ≫ (shiftFunctorZero' _ ((-1 : ℤ) + 1) h0).inv.app L
  have hres : res (-1 + 1) x = 0 := Prod.ext
    (hNU _ (qcohDerived_shift _ _ hLU) hLU' _) (hNV _ (qcohDerived_shift _ _ hLV) hLV' _)
  obtain ⟨y, hy⟩ := ((hex (-1)).2.2 x).1 hres
  let e : rP ≅ rU ⋙ rF :=
    (Dualizing.mapDerivedCategoryCompNatIso _ _ _ (edsFactorIsoOpen B S hS hsq)).symm
  have hy0 : y = 0 := by
    let φ := Iso.homCongr (e.app K.obj) ((shiftFunctor _ (-1 : ℤ)).mapIso (e.app L))
    have h := hNP _ (qcohDerived_shift _ _ hLP) hLP'
    exact (φ.subsingleton_congr.2 ⟨fun a b => (h a).trans (h b).symm⟩).elim _ _
  have hx : x = 0 := by rw [← hy, hy0, map_zero]
  have : f = x ≫ (shiftFunctorZero' _ ((-1 : ℤ) + 1) h0).hom.app L := by
    simp only [x, Category.assoc, Iso.inv_hom_id_app]
    exact (Category.comp_id f).symm
  rw [this, hx, zero_comp]

end Step

attribute [-instance] CategoryTheory.Limits.Types.instHasPushoutsType in
/-- **Morphisms from a compact object into objects far to the left vanish** (half of Stacks 09MB
(1)). Let `X` be a quasi-compact and quasi-separated algebraic space and `K` a compact object of
`D_QCoh(𝒪_X)`. There is `N` such that every morphism `K ⟶ L` into an object `L` of `D_QCoh(𝒪_X)`
with `H^i(L) = 0` for `i > -N` is zero. -/
theorem exists_hom_eq_zero_of_isCompactObject (X : AlgebraicSpaces B S hS)
    (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1)
    (K : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) (hK : IsCompactObject.{u} K) :
    HomVanishingFarLeft X.1 X.2 K.obj :=
  qcqs_induction_on_self B S hS B.contains_terminal X hqc hqs
    (fun Z _ => ∀ hZ' : IsAlgebraicSpace B S hS Z,
      ∀ K : QuasicoherentDerivedCategory.{u, u} B S hS Z hZ', IsCompactObject.{u} K →
        HomVanishingFarLeft Z hZ' K.obj)
    (fun _ hV hZ' K hK => homVanishingFarLeft_of_isAffineSpace (X := ⟨_, hZ'⟩) hV K hK)
    (fun _ _ _ _ _ hsq _ hWqs hUqc hVa hPU hPV hPP _ K hK =>
      homVanishingFarLeft_of_eds B.contains_terminal hsq hVa hUqc hWqs
        (hPU hsq.isOpenSubspace.1) (hPV hsq.isAlgebraicSpace) (hPP (edsInter B S hS hsq).2) K hK)
    X.2 K hK

end AlgebraicGeometry.Space

end
