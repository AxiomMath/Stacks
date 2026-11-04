module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.PoincareDualityFibrationInputs
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LowerShriekDualityTranspose
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CompositionIso
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.HomologicalDualityExt

/-!
# Moving Poincaré duality along an elementary fibration

Let `f : U → S` be an elementary fibration over `S` affine and smooth over `k`, `q : S → Spec k`,
`ℓ` a prime invertible in `k` and `Λ = ℤ/ℓ`. Write `H_U = Hom(Λ_k[0], R(q ∘ f)_! -)` on `D⁺(U)` and
`H_S = Hom(Λ_k[0], Rq_! -)` on `D⁺(S)`, the compactly supported cohomology functors over the base
field, and `t_f : Rf_!(f⁻¹ Λ_S) ⟶ Λ_S[-2]` for the top-degree trace
(`Stacks.EtaleCohomology.lowerShriekTopTrace`). By
[Tag 0F7J](https://stacks.math.columbia.edu/tag/0F7J) `H_U ≅ H_S ∘ Rf_!`
(`Stacks.EtaleCohomology.lowerShriekCoyonedaCompIso`), and relative Poincaré duality
(`Stacks.EtaleCohomology.RelativeCurveDualityInput`) says that `y ↦ t_f[j] ∘ Rf_!(y)` is bijective
`Hom(Λ_U[0], Λ_U[0][j]) → Hom(Rf_! Λ_U, Λ_S[0][j - 2])` for `j ≥ 0`; for `j < 0` both sides
vanish, `Rf_! Λ_U` living in degrees `≤ 2`
(`Stacks.EtaleCohomology.bijective_transferMap_lowerShriekTopTrace`). So duality on `U` for the
trace transferred along `t_f` is duality on `S` for the complex `Rf_! Λ_U`
(`Stacks.EtaleCohomology.isPerfect_lowerShriek_comp_iff`). This is a step of the fibration step
of Poincaré duality in the proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

The statements consume `Rf_!`, defined in the standard model `HasDerivedCategory.standard` of the
derived category, which is therefore a local instance here.

## Main definitions

* `Stacks.EtaleCohomology.lowerShriekCoyonedaCompIso`.
* `Stacks.EtaleCohomology.lowerShriekTopTraceTheta`.

## Main results

* `Stacks.EtaleCohomology.bijective_transferMap_lowerShriekTopTrace`.
* `Stacks.EtaleCohomology.isPerfect_lowerShriek_comp_iff`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology

open ExtensionTorsor

attribute [local instance] HasDerivedCategory.standard

section Composition

variable {k : Type u} [Field k] (ℓ : ℕ) [NeZero ℓ] {U S : Scheme.{u}} (f : U ⟶ S)
  (q : S ⟶ Spec (.of k)) [CompactSpace U] [QuasiSeparatedSpace U] [CompactSpace S]
  [QuasiSeparatedSpace S] [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated q]
  [LocallyOfFiniteType q]
  (jf : CompactificationOf (Over.mk f)) (jS : CompactificationOf (Over.mk q))
  (jU : CompactificationOf (Over.mk (f ≫ q)))

/-- **`Hom(Λ_k[0], R(q ∘ f)_! -) ≅ Hom(Λ_k[0], Rq_! Rf_! -)`** on `D⁺(U, ℤ/ℓ)`, by
[Tag 0F7J](https://stacks.math.columbia.edu/tag/0F7J) (every complex of `ℤ/ℓ`-modules is
torsion). -/
def lowerShriekCoyonedaCompIso :
    derivedLowerShriek.{u, 0} (f ≫ q) jU (ZMod ℓ) ⋙ preadditiveCoyoneda.obj
        (op ((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := Spec (.of k)) ℓ))) ≅
      derivedLowerShriek.{u, 0} f jf (ZMod ℓ) ⋙ (derivedLowerShriek.{u, 0} q jS (ZMod ℓ) ⋙
        preadditiveCoyoneda.obj
          (op ((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := Spec (.of k)) ℓ)))) :=
  let L := (isTorsionPlus.{u, 0} (ZMod ℓ) U).lift (𝟭 _) (fun _ _ =>
    isTorsionEtaleModule_of_natCast_eq_zero (ZMod ℓ) ℓ (Nat.pos_of_ne_zero (NeZero.ne ℓ))
      (ZMod.natCast_self ℓ) _)
  let e : derivedLowerShriek.{u, 0} (f ≫ q) jU (ZMod ℓ) ≅
      derivedLowerShriek.{u, 0} f jf (ZMod ℓ) ⋙ derivedLowerShriek.{u, 0} q jS (ZMod ℓ) :=
    (Functor.isoWhiskerLeft L (derivedLowerShriekCompIso (ZMod ℓ) f q jf jS jU) :
      L ⋙ (isTorsionPlus.{u, 0} (ZMod ℓ) U).ι ⋙ derivedLowerShriek.{u, 0} (f ≫ q) jU (ZMod ℓ) ≅
        L ⋙ (isTorsionPlus.{u, 0} (ZMod ℓ) U).ι ⋙ derivedLowerShriek.{u, 0} f jf (ZMod ℓ) ⋙
          derivedLowerShriek.{u, 0} q jS (ZMod ℓ))
  Functor.isoWhiskerRight e _ ≪≫ Functor.associator _ _ _

end Composition

section Transfer

variable {k : Type u} [Field k] [IsAlgClosed k] (ℓ : ℕ) [Fact ℓ.Prime] {U S : Scheme.{u}}
  (f : U ⟶ S) (jf : CompactificationOf (Over.mk f))
  (hf : ∀ y : S, topologicalKrullDim (jf.toBase.fiber y) ≤ 1)
  (ν : etaleModuleInverseImage.{u, 0} (ZMod ℓ) f ⋙ DerivedCategory.Plus.singleFunctor _ 0 ⋙
    derivedLowerShriek.{u, 0} f jf (ZMod ℓ) ⋙ DerivedCategory.Plus.homologyFunctor _ 2 ≅
      𝟭 (EtaleModules.{u, 0} (ZMod ℓ) S))

/-- The top-degree trace `t_f : Rf_!(f⁻¹ Λ_S[0]) ⟶ Λ_S[0][-2]`, as a morphism of `D⁺(S)`. -/
def lowerShriekTopTraceTheta :
    (derivedLowerShriek.{u, 0} f jf (ZMod ℓ)).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).obj (unitSheaf (X := S) ℓ))) ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ))⟦(-2 : ℤ)⟧ :=
  DerivedCategory.Plus.ι.preimage (lowerShriekTopTrace f jf ℓ hf ν (unitSheaf (X := S) ℓ) ≫
    (DerivedCategory.Plus.ι.commShiftIso (-2 : ℤ)).inv.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)))

/-- `ShiftedHom.map` along `D⁺ ⥤ D` sends the preimage of `g ≫ (commShiftIso a).inv` back to `g`. -/
private lemma map_ι_preimage_comp_commShiftIso_inv
    {P Q : DerivedCategory.Plus (EtaleModules.{u, 0} (ZMod ℓ) S)} {a : ℤ}
    (g : DerivedCategory.Plus.ι.obj P ⟶ (DerivedCategory.Plus.ι.obj Q)⟦a⟧) :
    ShiftedHom.map (DerivedCategory.Plus.ι.preimage
      (g ≫ (DerivedCategory.Plus.ι.commShiftIso a).inv.app Q) : ShiftedHom P Q a)
        DerivedCategory.Plus.ι = g := by
  simp only [ShiftedHom.map, Functor.map_preimage, Category.assoc, Iso.inv_hom_id_app]
  exact Category.comp_id _

/-- The image of `lowerShriekTopTraceTheta` under the inclusion `D⁺(S) ⥤ D(S)` is the top-degree
trace `lowerShriekTopTrace` at `Λ_S`. -/
lemma lowerShriekTopTraceTheta_map_ι :
    ShiftedHom.map (lowerShriekTopTraceTheta ℓ f jf hf ν : ShiftedHom _ _ (-2 : ℤ))
        DerivedCategory.Plus.ι = lowerShriekTopTrace f jf ℓ hf ν (unitSheaf (X := S) ℓ) :=
  map_ι_preimage_comp_commShiftIso_inv ℓ _

/-- `ShiftedHom.map` along the inclusion `D⁺ ⥤ D` is bijective. -/
lemma bijective_map_ι {P Q : DerivedCategory.Plus (EtaleModules.{u, 0} (ZMod ℓ) S)} {a : ℤ} :
    Function.Bijective (fun φ : ShiftedHom P Q a => φ.map DerivedCategory.Plus.ι) :=
  ⟨fun _ _ h => DerivedCategory.Plus.ι.map_injective ((cancel_mono
    ((DerivedCategory.Plus.ι.commShiftIso a).hom.app Q)).1 h), fun g =>
      ⟨_, map_ι_preimage_comp_commShiftIso_inv ℓ g⟩⟩

omit [IsAlgClosed k] in
/-- **Relative duality as bijectivity of the transfer maps along `Rf_!`**: for an elementary
fibration, `y ↦ t_f[j] ∘ Rf_!(y)` is bijective
`Hom(Λ_U[0], Λ_U[0][j]) → Hom(Rf_! Λ_U[0], Λ_S[0][j - 2])` for every integer `j`: in degrees
`j ≥ 0` this is relative Poincaré duality, and in degrees `j < 0` both sides vanish. -/
theorem bijective_transferMap_lowerShriekTopTrace (hPD : RelativeCurveDualityInput ℓ k)
    (hℓ : IsUnit (ℓ : k)) (q : S ⟶ Spec (.of k)) (e : ℕ) [SmoothOfRelativeDimension e q]
    [IsAffine S] (hfib : IsElementaryFibration f) (j : ℤ) :
    Function.Bijective (HomologicalDuality.transferMap (derivedLowerShriek.{u, 0} f jf (ZMod ℓ))
      (lowerShriekTopTraceTheta ℓ f jf hf ν) ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).obj (unitSheaf (X := S) ℓ))) j) := by
  have hmap : ∀ y, ShiftedHom.map (HomologicalDuality.transferMap
      (derivedLowerShriek.{u, 0} f jf (ZMod ℓ)) (lowerShriekTopTraceTheta ℓ f jf hf ν)
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).obj (unitSheaf (X := S) ℓ))) j y :
            ShiftedHom _ _ (j + -2)) DerivedCategory.Plus.ι =
      (ShiftedHom.map (y : ShiftedHom _ _ j)
        (derivedLowerShriek.{u, 0} f jf (ZMod ℓ) ⋙ DerivedCategory.Plus.ι)).comp
          (lowerShriekTopTrace f jf ℓ hf ν (unitSheaf (X := S) ℓ)) (add_comm (-2) j) := by
    intro y
    have h : (HomologicalDuality.transferMap (derivedLowerShriek.{u, 0} f jf (ZMod ℓ))
        (lowerShriekTopTraceTheta ℓ f jf hf ν) ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).obj (unitSheaf (X := S) ℓ))) j y :
            ShiftedHom _ _ (j + -2)) =
        (ShiftedHom.map (y : ShiftedHom _ _ j) (derivedLowerShriek.{u, 0} f jf (ZMod ℓ))).comp
          (lowerShriekTopTraceTheta ℓ f jf hf ν : ShiftedHom _ _ (-2 : ℤ)) (add_comm (-2) j) := by
      simp only [HomologicalDuality.transferMap_apply, ShiftedHom.comp, ShiftedHom.map,
        Category.assoc]
    rw [h, ShiftedHom.map_comp, ← ShiftedHom.comp_map, lowerShriekTopTraceTheta_map_ι]
    rfl
  rw [← Function.Bijective.of_comp_iff' (bijective_map_ι ℓ)]
  show Function.Bijective (fun y => ShiftedHom.map (HomologicalDuality.transferMap
      (derivedLowerShriek.{u, 0} f jf (ZMod ℓ)) (lowerShriekTopTraceTheta ℓ f jf hf ν)
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).obj (unitSheaf (X := S) ℓ))) j y :
            ShiftedHom _ _ (j + -2)) DerivedCategory.Plus.ι)
  simp only [hmap]
  rcases lt_or_ge j 0 with hj | hj
  · have := HomologicalDuality.subsingleton_hom_single_shift_of_neg
      ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).obj (unitSheaf (X := S) ℓ))
      ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).obj (unitSheaf (X := S) ℓ)) hj
    have hT : ∀ φ ψ : ShiftedHom (DerivedCategory.Plus.ι.obj
        ((derivedLowerShriek.{u, 0} f jf (ZMod ℓ)).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).obj (unitSheaf (X := S) ℓ)))))
        ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) (j + -2), φ = ψ := by
      intro φ ψ
      have := isLE_derivedLowerShriek_inverseImage_single f jf ℓ hf (unitSheaf (X := S) ℓ)
      have : (((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ))⟦j + -2⟧).IsGE
          (-(j + -2)) :=
        DerivedCategory.TStructure.t.isGE_shift _ 0 (j + -2) (-(j + -2)) (by omega)
      rw [DerivedCategory.TStructure.t.zero φ 2 (-(j + -2)) (by omega),
        DerivedCategory.TStructure.t.zero ψ 2 (-(j + -2)) (by omega)]
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, hT _ _⟩⟩
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hj
    refine (Function.Bijective.of_comp_iff _ (HomologicalDuality.extPlus_bijective _ _ m)).1 ?_
    exact hPD hℓ U S q f e hfib jf hf ν m _ (add_comm _ _)

variable (q : S ⟶ Spec (.of k)) [CompactSpace U] [QuasiSeparatedSpace U] [CompactSpace S]
  [QuasiSeparatedSpace S] [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated q]
  [LocallyOfFiniteType q] (jS : CompactificationOf (Over.mk q))
  (jU : CompactificationOf (Over.mk (f ≫ q)))

omit [IsAlgClosed k] in
/-- **Duality on `U` is duality on `S` for `Rf_! Λ_U`**: for an elementary fibration `f : U → S`,
duality for `Hom(Λ_k[0], R(q ∘ f)_! -)` at `Λ_U[0]` (dualizing object `Λ_U[0]`, degree `N`, the
trace `τ_S ∘ t_f` transferred along the top-degree trace) holds exactly when duality for
`Hom(Λ_k[0], Rq_! -)` holds at `Rf_! Λ_U[0]` (dualizing object `Λ_S[0]`, degree `N - 2`,
trace `τ_S`). -/
theorem isPerfect_lowerShriek_comp_iff (hPD : RelativeCurveDualityInput ℓ k)
    (hℓ : IsUnit (ℓ : k)) (e : ℕ) [SmoothOfRelativeDimension e q] [IsAffine S]
    (hfib : IsElementaryFibration f) {N N' : ℤ} (hN : N + -2 = N')
    (τ : (derivedLowerShriek.{u, 0} q jS (ZMod ℓ) ⋙ preadditiveCoyoneda.obj
        (op ((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := Spec (.of k)) ℓ)))).obj
      (((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ))⟦N'⟧) →+ ZMod ℓ) :
    HomologicalDuality.IsPerfect (derivedLowerShriek.{u, 0} (f ≫ q) jU (ZMod ℓ) ⋙
        preadditiveCoyoneda.obj
          (op ((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := Spec (.of k)) ℓ))))
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).obj (unitSheaf (X := S) ℓ))) N
      (HomologicalDuality.transferTrace (derivedLowerShriek.{u, 0} f jf (ZMod ℓ))
        (lowerShriekCoyonedaCompIso ℓ f q jf jS jU) (lowerShriekTopTraceTheta ℓ f jf hf ν) hN τ)
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).obj (unitSheaf (X := S) ℓ))) ↔
    HomologicalDuality.IsPerfect (derivedLowerShriek.{u, 0} q jS (ZMod ℓ) ⋙
        preadditiveCoyoneda.obj
          (op ((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := Spec (.of k)) ℓ))))
      ((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) N' τ
      ((derivedLowerShriek.{u, 0} f jf (ZMod ℓ)).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).obj (unitSheaf (X := S) ℓ)))) :=
  HomologicalDuality.isPerfect_iff_of_transfer _ _ _ hN τ _
    (bijective_transferMap_lowerShriekTopTrace ℓ f jf hf ν hPD hℓ q e hfib)

end Transfer

end Stacks.EtaleCohomology

end
