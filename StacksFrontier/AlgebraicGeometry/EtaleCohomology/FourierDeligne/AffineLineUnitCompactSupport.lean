module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.CurveOpenConstantExt
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.CompactSupportGeometricVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyExt
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.Independence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicCompactSupport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.ArtinSchreierCompactSupportVanishing

/-!
# `Hⁱ_c(𝔸¹_k̄, ℤ/ℓ)` is `ℤ/ℓ` in degree two and zero otherwise

Let `k` be a finite field, `k̄` an algebraically closed extension of `k`, `ℓ` a prime invertible
in `k̄` and `j` any compactification of `𝔸¹_k = Spec k[X]` over `k`. Then
`Hⁱ_c(𝔸¹_k̄, ℤ/ℓ)` (`Stacks.EtaleCohomology.compactSupportSheafCohomology`) vanishes for
`i ≠ 2` and has `ℓ` elements for `i = 2`.

Indeed `Hⁱ_c(𝔸¹_k̄, -)` is compactly supported cohomology over `k̄` of the base change
`𝔸¹_k ×_k k̄` (`compactSupportSheafCohomologyIsoCompactlySupportedCohomologyGroup`), which does
not depend on the compactification (Tag 0F7I). The base change is `𝔸¹_{k̄}`
(`AlgebraicGeometry.AffineSpace.isPullback_map`), compactified by the first chart of `ℙ¹_{k̄}`,
and there compactly supported cohomology is `Ext^i_{ℙ¹}(Λ, j_! Λ)`
(`Stacks.EtaleCohomology.compactlySupportedCohomologyGroupSingleIsoExt`), computed in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.CurveOpenConstantExt`.

## Main results

* `Stacks.EtaleCohomology.affineLineIsoAffineSpace`: `Spec k[X] ≅ 𝔸¹_k`.
* `Stacks.EtaleCohomology.affineLineBaseChangeIso`: `𝔸¹_k ×_k k̄ ≅ 𝔸¹_k̄` over `k̄`.
* `Stacks.EtaleCohomology.affineLineBaseChangeCompactification`: `𝔸¹_k ×_k k̄ ⊆ ℙ¹_{k̄}` over `k̄`.
* `Stacks.EtaleCohomology.subsingleton_compactSupportSheafCohomology_unitSheaf_affineLine`.
* `Stacks.EtaleCohomology.natCard_compactSupportSheafCohomology_two_unitSheaf_affineLine`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Polynomial
open Stacks.EtaleCohomology.ExtensionTorsor Stacks.ArtinSchreier

universe u

namespace Stacks.EtaleCohomology

/-! ### The base change of the affine line -/

section Geometry

variable (k : Type u) [Field k] (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- **`Spec k[X] ≅ 𝔸¹_k`**, the affine line as Mathlib's affine space on one coordinate. -/
def affineLineIsoAffineSpace : Spec (.of k[X]) ≅ AffineSpace (ULift.{u} (Fin 1)) (Spec (.of k)) :=
  Scheme.Spec.mapIso
      (MvPolynomial.uniqueAlgEquiv k (ULift.{u} (Fin 1))).toRingEquiv.toCommRingCatIso.op ≪≫
    (AffineSpace.SpecIso (ULift.{u} (Fin 1)) (.of k)).symm

/-- The isomorphism `affineLineIsoAffineSpace` lies over `Spec k`. -/
theorem affineLineIsoAffineSpace_hom_over :
    (affineLineIsoAffineSpace k).hom ≫
        (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of k)) ↘ Spec (.of k)) =
      affineLineStructureMap k := by
  simp only [affineLineIsoAffineSpace, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    AffineSpace.SpecIso_inv_over, Functor.mapIso_hom, Iso.op_hom, Scheme.Spec_map,
    Quiver.Hom.unop_op, ← Spec.map_comp]
  congr 1
  ext a : 2
  exact (MvPolynomial.uniqueAlgEquiv k (ULift.{u} (Fin 1))).commutes a

/-- The base change of `𝔸¹_k` to `k̄` is a pullback of `𝔸¹_k̄ ⟶ Spec k̄`. -/
theorem isPullback_affineLineBaseChange :
    IsPullback (AffineSpace.map (ULift.{u} (Fin 1)) (Stacks.Frobenius.specAlgebraMap k kbar) ≫
        (affineLineIsoAffineSpace k).inv)
      (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of kbar)) ↘ Spec (.of kbar))
      (affineLineStructureMap k) (Stacks.Frobenius.specAlgebraMap k kbar) := by
  have hsq : IsPullback (affineLineIsoAffineSpace k).inv
      (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of k)) ↘ Spec (.of k)) (affineLineStructureMap k)
      (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by
      rw [Category.comp_id, Iso.inv_comp_eq, affineLineIsoAffineSpace_hom_over]⟩
  simpa using (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1))
    (Stacks.Frobenius.specAlgebraMap k kbar)).paste_horiz hsq

/-- **`𝔸¹_k ×_k k̄ ≅ 𝔸¹_k̄`** over `k̄`. -/
def affineLineBaseChangeIso :
    pullback (affineLineStructureMap k) (Stacks.Frobenius.specAlgebraMap k kbar) ≅
      AffineSpace (ULift.{u} (Fin 1)) (Spec (.of kbar)) :=
  (IsPullback.of_hasPullback _ _).isoIsPullback _ _ (isPullback_affineLineBaseChange k kbar)

/-- The isomorphism `affineLineBaseChangeIso` lies over `Spec k̄`. -/
@[reassoc (attr := simp)]
theorem affineLineBaseChangeIso_hom_over :
    (affineLineBaseChangeIso k kbar).hom ≫
        (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of kbar)) ↘ Spec (.of kbar)) =
      pullback.snd (affineLineStructureMap k) (Stacks.Frobenius.specAlgebraMap k kbar) :=
  IsPullback.isoIsPullback_hom_snd _ _ _ (isPullback_affineLineBaseChange k kbar)

/-- The open immersion `𝔸¹_k ×_k k̄ ≅ 𝔸¹_k̄ ⟶ ℙ¹_k̄` onto the first chart. -/
def affineLineBaseChangeChart :
    pullback (affineLineStructureMap k) (Stacks.Frobenius.specAlgebraMap k kbar) ⟶
      projectiveSpaceOver 1 (Spec (.of kbar)) :=
  (affineLineBaseChangeIso k kbar).hom ≫
    (ProjectiveSpace.fromAffineSpace.{u} 1 0 (Spec (.of kbar)) :
      AffineSpace (ULift.{u} (Fin 1)) (Spec (.of kbar)) ⟶ projectiveSpaceOver 1 (Spec (.of kbar)))

/-- The chart is an open immersion. -/
instance isOpenImmersion_affineLineBaseChangeChart :
    IsOpenImmersion (affineLineBaseChangeChart k kbar) := by
  have : IsOpenImmersion (ProjectiveSpace.fromAffineSpace.{u} 1 0 (Spec (.of kbar))) :=
    ProjectiveSpace.isOpenImmersion_fromAffineSpace 1 0 (Spec (.of kbar))
  exact IsOpenImmersion.comp _ (ProjectiveSpace.fromAffineSpace.{u} 1 0 (Spec (.of kbar)))

/-- The chart `affineLineBaseChangeChart` lies over `Spec k̄`. -/
theorem affineLineBaseChangeChart_over :
    affineLineBaseChangeChart k kbar ≫ (projectiveSpaceOver 1 (Spec (.of kbar)) ↘ Spec (.of kbar)) =
      pullback.snd (affineLineStructureMap k) (Stacks.Frobenius.specAlgebraMap k kbar) :=
  (Category.assoc _ _ _).trans <| ((affineLineBaseChangeIso k kbar).hom ≫=
    ProjectiveSpace.fromAffineSpace_over 1 0 (Spec (.of kbar))).trans
      (affineLineBaseChangeIso_hom_over k kbar)

/-- The image of `affineLineBaseChangeChart` is the image of the first affine chart of `ℙ¹_k̄`. -/
theorem range_affineLineBaseChangeChart :
    Set.range (affineLineBaseChangeChart k kbar).base =
      Set.range (ProjectiveSpace.fromAffineSpace.{u} 1 0 (Spec (.of kbar))).base := by
  let e := affineLineBaseChangeIso k kbar
  let V := ProjectiveSpace.fromAffineSpace.{u} 1 0 (Spec (.of kbar))
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨e.hom.base x, rfl⟩
  · rintro ⟨a, rfl⟩
    refine ⟨e.inv.base a, ?_⟩
    show V.base ((e.inv ≫ e.hom).base a) = V.base a
    rw [Iso.inv_hom_id]
    rfl

/-- **`𝔸¹_k ×_k k̄ ⊆ ℙ¹_k̄`**, a compactification over `k̄` of the base change of `𝔸¹_k`. -/
def affineLineBaseChangeCompactification :
    CompactificationOf (Over.mk
      (pullback.snd (affineLineStructureMap k) (Stacks.Frobenius.specAlgebraMap k kbar))) where
  obj := StructuredArrow.mk
    (Y := Over.mk (projectiveSpaceOver 1 (Spec (.of kbar)) ↘ Spec (.of kbar)))
    (Over.homMk (affineLineBaseChangeChart k kbar) (affineLineBaseChangeChart_over k kbar))
  property := ⟨isOpenImmersion_affineLineBaseChangeChart k kbar,
    inferInstanceAs (IsProper (projectiveSpaceOver 1 (Spec (.of kbar)) ↘ Spec (.of kbar)))⟩

end Geometry

/-! ### `Hⁱ_c(𝔸¹_k̄, ℤ/ℓ)` -/

section Cohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

variable (k : Type u) [Field k] [Fintype k] (kbar : Type u) [Field kbar] [Algebra k kbar]
  {ℓ : ℕ} [Fact ℓ.Prime]

omit [Fintype k] in
/-- **`Hⁱ_c(𝔸¹_k̄, ℤ/ℓ) ≅ Ext^i_{ℙ¹_k̄}(Λ, j_! Λ)`** for every compactification of `𝔸¹_k`,
`j` the first chart. -/
theorem nonempty_compactSupportSheafCohomology_unitSheaf_affineLine_iso_ext
    (j : CompactificationOf (Over.mk (affineLineStructureMap k))) (i : ℕ) :
    Nonempty ((forget₂ (ModuleCat.{u + 1} (ZMod ℓ)) AddCommGrpCat.{u + 1}).obj
        ((compactSupportSheafCohomology (ZMod ℓ) (affineLineStructureMap k) j kbar i).obj
          (unitSheaf (X := Spec (.of k[X])) ℓ)) ≅
      AddCommGrpCat.of (Ext (unitSheaf (X := projectiveSpaceOver 1 (Spec (.of kbar))) ℓ)
        ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ)
          (affineLineBaseChangeChart k kbar)).obj
            (unitSheaf (X := projectiveSpaceOver 1 (Spec (.of kbar))) ℓ)) i)) := by
  have : LocallyOfFiniteType (affineLineStructureMap k) := locallyOfFiniteType_specPolynomial k
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  let g := Stacks.Frobenius.specAlgebraMap k kbar
  let f' := pullback.snd (affineLineStructureMap k) g
  let j' := affineLineBaseChangeCompactification k kbar
  let ι := affineLineBaseChangeChart k kbar
  let G := (etaleModuleInverseImage.{u, 0} (ZMod ℓ) (pullback.fst (affineLineStructureMap k) g)).obj
    (unitSheaf (X := Spec (.of k[X])) ℓ)
  let K := (DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} (ZMod ℓ) _) 0).obj G
  let e₂ := compactSupportSheafCohomologyIsoCompactlySupportedCohomologyGroup (ZMod ℓ)
    (affineLineStructureMap k) j kbar (unitSheaf (X := Spec (.of k[X])) ℓ) i
  let e₃ : (compactlySupportedCohomologyGroup.{u, 0} kbar f'
        (compactificationFieldBaseChange (affineLineStructureMap k) j kbar) (ZMod ℓ) i).obj K ≅
      (compactlySupportedCohomologyGroup.{u, 0} kbar f' j' (ZMod ℓ) i).obj K :=
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} (ZMod ℓ)) i).mapIso
      ((etaleModuleDerivedGlobalSections.{u, 0} (ZMod ℓ) (Spec (.of kbar))).mapIso
        ((derivedLowerShriekCompactificationIso f'
          (compactificationFieldBaseChange (affineLineStructureMap k) j kbar) j'
            (ZMod ℓ)).app ⟨K, isTorsionPlus_of_finite (ZMod ℓ) _ K⟩))
  let e₄ := compactlySupportedCohomologyGroupSingleIsoExt (ZMod ℓ) kbar f' j' G i
  let eG : G ≅ (etaleModuleRestriction.{u, 0} (ZMod ℓ) ι).obj
      (unitSheaf (X := projectiveSpaceOver 1 (Spec (.of kbar))) ℓ) :=
    (etaleModuleInverseImageConstantIso.{u, 0} (ZMod ℓ)
        (pullback.fst (affineLineStructureMap k) g)).app
      (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ))) ≪≫
      unitSheafIsoRestrictionOfIsOpenImmersion (ℓ := ℓ) ι
  exact ⟨(forget₂ (ModuleCat.{u + 1} (ZMod ℓ)) AddCommGrpCat.{u + 1}).mapIso (e₂ ≪≫ e₃) ≪≫ e₄ ≪≫
    (extFunctorObj (unitSheaf (X := projectiveSpaceOver 1 (Spec (.of kbar))) ℓ) i).mapIso
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) ι).mapIso eG)⟩

variable [IsAlgClosed kbar]

omit [Fintype k] in
/-- **`Hⁱ_c(𝔸¹_k̄, ℤ/ℓ) = 0` for `i ≠ 2`**, `ℓ` invertible in `k̄`, for every compactification of
`𝔸¹_k`. -/
theorem subsingleton_compactSupportSheafCohomology_unitSheaf_affineLine (hℓ : IsUnit (ℓ : kbar))
    (j : CompactificationOf (Over.mk (affineLineStructureMap k))) (i : ℤ) (hi : i ≠ 2) :
    Subsingleton ((compactSupportSheafCohomology (ZMod ℓ) (affineLineStructureMap k) j kbar i).obj
      (unitSheaf (X := Spec (.of k[X])) ℓ)) := by
  have : LocallyOfFiniteType (affineLineStructureMap k) := locallyOfFiniteType_specPolynomial k
  rcases lt_or_ge i 0 with hneg | hpos
  · have h := isZero_compactlySupportedCohomologyGroup_single_of_neg kbar
      (pullback.snd (affineLineStructureMap k) (Stacks.Frobenius.specAlgebraMap k kbar))
      (compactificationFieldBaseChange (affineLineStructureMap k) j kbar) (ZMod ℓ)
      ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) (pullback.fst (affineLineStructureMap k)
        (Stacks.Frobenius.specAlgebraMap k kbar))).obj (unitSheaf (X := Spec (.of k[X])) ℓ)) i hneg
    exact ModuleCat.subsingleton_of_isZero (h.of_iso
      (compactSupportSheafCohomologyIsoCompactlySupportedCohomologyGroup (ZMod ℓ)
        (affineLineStructureMap k) j kbar _ i))
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hpos
    obtain ⟨e⟩ := nonempty_compactSupportSheafCohomology_unitSheaf_affineLine_iso_ext k kbar
      (ℓ := ℓ) j n
    have := subsingleton_ext_unitSheaf_extensionByZeroOfRestriction_affineChart kbar hℓ
      (affineLineBaseChangeChart k kbar) (range_affineLineBaseChangeChart k kbar) n
      (by omega)
    exact e.addCommGroupIsoToAddEquiv.toEquiv.subsingleton

omit [Fintype k] in
/-- **`H²_c(𝔸¹_k̄, ℤ/ℓ)` has `ℓ` elements**, `ℓ` invertible in `k̄`, for every compactification of
`𝔸¹_k`. -/
theorem natCard_compactSupportSheafCohomology_two_unitSheaf_affineLine (hℓ : IsUnit (ℓ : kbar))
    (j : CompactificationOf (Over.mk (affineLineStructureMap k))) :
    Nat.card ((compactSupportSheafCohomology (ZMod ℓ) (affineLineStructureMap k) j kbar 2).obj
      (unitSheaf (X := Spec (.of k[X])) ℓ)) = ℓ := by
  obtain ⟨e⟩ := nonempty_compactSupportSheafCohomology_unitSheaf_affineLine_iso_ext k kbar
    (ℓ := ℓ) j 2
  exact (Nat.card_congr e.addCommGroupIsoToAddEquiv.toEquiv).trans
    (natCard_ext_two_unitSheaf_extensionByZeroOfRestriction_affineChart kbar hℓ
      (affineLineBaseChangeChart k kbar) (range_affineLineBaseChangeChart k kbar))

end Cohomology

end Stacks.EtaleCohomology

end
