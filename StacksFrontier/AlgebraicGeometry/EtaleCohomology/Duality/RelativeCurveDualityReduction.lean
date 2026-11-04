module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.PoincareDualityFibrationInputs
public import StacksFrontier.Algebra.Homology.DerivedCategory.RelativeTraceMap
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.HomologicalDualityDegreeZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.TopDirectImageBoundary
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.ElementaryFibrationLowerShriek
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.CategoryTheory.Abelian.ExtAdjunction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Relative Poincaré duality for an elementary fibration, reduced to the compactification

Let `k` be algebraically closed, `ℓ` a prime invertible in `k`, `Λ = ℤ/ℓ`, and `f : U → S` an
elementary fibration over `S` affine and smooth over `k`: `f = f̄ ∘ j` with `f̄ : X̄ → S` smooth
projective of relative dimension one with geometrically irreducible fibres, `j : U → X̄` the
complement of a closed `i : Z → X̄` finite étale over `S`. Relative duality
(`Stacks.EtaleCohomology.RelativeCurveDualityInput`) asks that for every `m` the map
`Hom_U(Λ, Λ[m]) → Hom_S(Rf_! Λ, Λ[m - 2])`, `y ↦ t_f[m] ∘ Rf_!(y)`, be bijective, `t_f` the
top-degree trace.

This file reduces it to two statements on the compactification `X̄`, for any top-degree trace
`t : Rf̄_* Λ ⟶ Λ[-2]` (one inducing an isomorphism on `R²`): the map
`y ↦ t[m] ∘ Rf̄_*(y)`, `Hom_X̄(A, Λ[m]) → Hom_S(Rf̄_* A, Λ[m - 2])`, is bijective

* at `A = Λ_X̄`: relative Poincaré duality for the smooth proper curve `f̄`
  (`Stacks.EtaleCohomology.ProperCurveRelativeDualityInput`);
* at `A = i_* Λ_Z`: duality along the étale boundary divisor
  (`Stacks.EtaleCohomology.BoundaryDivisorDualityInput`; by purity
  `Hom_X̄(i_* Λ_Z, Λ[m]) = H^{m - 2}(Z, Λ(-1))`, and `Hom_S(π_* Λ_Z, Λ[m - 2]) = H^{m - 2}(Z, Λ)`
  for the finite étale `π = f̄ ∘ i`).

The reduction (`Stacks.EtaleCohomology.relativeCurveDualityInput_of_inputs`) is formal:

* `Rf_!` does not depend on the compactification up to isomorphism (Tag 0F7I); the isomorphism
  need not commute with the shifts, but the defect is an automorphism of `Rf_! Λ`, absorbed by the
  rigidity of top-degree traces (`Stacks.RelativeDuality.exists_traceMap_eq_of_iso`,
  `Stacks.RelativeDuality.bijective_traceMap_iff_of_isIso_homology`);
* through the compactification `j`, `Rf_! = Rf̄_* ∘ Rj_!`, and `Rj_!` is `j_!` in degree zero,
  which is bijective on `Ext` (the unit of `j_! ⊣ j⁻¹` is invertible), so the map is that of
  `Rf̄_*` at `A = B = j_! Λ` (`Stacks.EtaleCohomology.traceMap_derivedExtensionByZero_extPlus`);
* composing with the counit `j_! Λ ⟶ Λ_X̄` is bijective on `Ext^m(j_! Λ, -)` (the adjunction),
  and carries a top-degree trace on `Rf̄_* Λ` to one on `Rf̄_*(j_! Λ)`, the complement of `U` being
  finite over `S`;
* the five lemma on `0 → j_! Λ → Λ_X̄ → i_* Λ_Z → 0` (`Stacks.RelativeDuality.isBijectiveAt_obj₁`).

This is part of the proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

The statements consume `Rf_!`, defined in the standard model `HasDerivedCategory.standard` of the
derived category, as a local instance.

## Main definitions

* `Stacks.EtaleCohomology.ProperCurveRelativeDualityInput`.
* `Stacks.EtaleCohomology.BoundaryDivisorDualityInput`.

## Main results

* `Stacks.EtaleCohomology.relativeCurveDualityInput_of_inputs`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open Stacks.EtaleCohomology.ExtensionTorsor Stacks.RelativeDuality

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-! ### Extension by zero along an open immersion, in degree zero -/

section ExtensionByZero

variable (N : ℕ) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- `H⁰(Rj_!((-)[0])) ≅ j_!` for an open immersion `j`, extension by zero being exact. -/
def derivedExtensionByZeroTopHomologyIso :
    Stacks.TopTruncationExt.topHomology
        (etaleModuleDerivedExtensionByZero.{u, 0} (ZMod N) j ⋙ DerivedCategory.Plus.ι) 0 ≅
      etaleModuleExtensionByZero.{u, 0} (ZMod N) j :=
  (Iso.refl _ : _ ≅ (DerivedCategory.Plus.singleFunctor _ 0 ⋙
      etaleModuleDerivedExtensionByZero.{u, 0} (ZMod N) j) ⋙
        (DerivedCategory.Plus.ι ⋙ DerivedCategory.homologyFunctor _ 0)) ≪≫
    Functor.isoWhiskerRight (Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
      (etaleModuleExtensionByZero.{u, 0} (ZMod N) j) 0).symm _ ≪≫
    (Iso.refl _ : _ ≅ etaleModuleExtensionByZero.{u, 0} (ZMod N) j ⋙
      (DerivedCategory.singleFunctor _ 0 ⋙ DerivedCategory.homologyFunctor _ 0)) ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0) ≪≫
    Functor.rightUnitor _

/-- `Rj_!(M[0]) ≅ (j_! M)[0]` for an open immersion `j`, read in `D(X)`. -/
def derivedExtensionByZeroSingleIso (M : EtaleModules.{u, 0} (ZMod N) U) :
    DerivedCategory.Plus.ι.obj ((etaleModuleDerivedExtensionByZero.{u, 0} (ZMod N) j).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj M)) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod N) j).obj M) :=
  DerivedCategory.Plus.ι.mapIso ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
    (etaleModuleExtensionByZero.{u, 0} (ZMod N) j) 0).app M).symm

/-- `Rj_!(M[0])` lies in degrees `≤ 0` of `D(X)`. -/
theorem isLE_derivedExtensionByZero_single (M : EtaleModules.{u, 0} (ZMod N) U) :
    ((etaleModuleDerivedExtensionByZero.{u, 0} (ZMod N) j ⋙ DerivedCategory.Plus.ι).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj M)).IsLE 0 :=
  DerivedCategory.TStructure.t.isLE_of_iso (derivedExtensionByZeroSingleIso N j M).symm 0

/-- `Rj_!(M[0])` lies in degrees `≥ 0` of `D(X)`. -/
theorem isGE_derivedExtensionByZero_single (M : EtaleModules.{u, 0} (ZMod N) U) :
    ((etaleModuleDerivedExtensionByZero.{u, 0} (ZMod N) j ⋙ DerivedCategory.Plus.ι).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj M)).IsGE 0 :=
  DerivedCategory.TStructure.t.isGE_of_iso (derivedExtensionByZeroSingleIso N j M).symm 0

/-- `Rj_!(M[0]) ≅ (j_! M)[0]` in `D⁺(X)`, by the top-degree projection
(`Stacks.HomologicalDuality.degreeZeroIso`). -/
abbrev derivedExtensionByZeroDegreeZeroIso (M : EtaleModules.{u, 0} (ZMod N) U) :
    (etaleModuleDerivedExtensionByZero.{u, 0} (ZMod N) j).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj M) ≅
      (DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod N) j).obj M) :=
  HomologicalDuality.degreeZeroIso _ (isLE_derivedExtensionByZero_single N j)
    (isGE_derivedExtensionByZero_single N j) _ (derivedExtensionByZeroTopHomologyIso N j) M

/-- **The trace map of `R ∘ Rj_!` on `Ext` classes is that of `R` on their extensions by zero**:
for `y ∈ Ext^m_U(M, M')`, `t[m] ∘ R(Rj_!(y)) = t'[m] ∘ R(j_! y) ∘ R(κ_M)` with `κ` the
identification `Rj_!(-[0]) ≅ (j_! -)[0]` and `t' = t ∘ R(κ_{M'}⁻¹)`, everything read in `D`. -/
theorem traceMap_derivedExtensionByZero_extPlus {B : Type*} [Category* B] [Abelian B]
    [HasDerivedCategory B]
    (R : DerivedCategory.Plus (EtaleModules.{u, 0} (ZMod N) X) ⥤ DerivedCategory.Plus B)
    [R.CommShift ℤ] [R.Additive]
    {M M' : EtaleModules.{u, 0} (ZMod N) U} {L : DerivedCategory B} {c₀ : ℤ}
    (t : ShiftedHom (((etaleModuleDerivedExtensionByZero.{u, 0} (ZMod N) j ⋙ R) ⋙
      DerivedCategory.Plus.ι).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj M')) L c₀) (m : ℕ)
    {c : ℤ} (h : c₀ + (m : ℤ) = c) (y : Ext M M' m) :
    traceMap ((etaleModuleDerivedExtensionByZero.{u, 0} (ZMod N) j ⋙ R) ⋙ DerivedCategory.Plus.ι) t
        ((DerivedCategory.Plus.singleFunctor _ 0).obj M) m c h (Stacks.TopTruncationExt.extPlus y) =
      (ShiftedHom.mk₀ (0 : ℤ) rfl ((R ⋙ DerivedCategory.Plus.ι).map
          (derivedExtensionByZeroDegreeZeroIso N j M).hom)).comp
        (traceMap (R ⋙ DerivedCategory.Plus.ι) ((ShiftedHom.mk₀ (0 : ℤ) rfl
            ((R ⋙ DerivedCategory.Plus.ι).map
              (derivedExtensionByZeroDegreeZeroIso N j M').inv)).comp t (add_zero c₀))
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((etaleModuleExtensionByZero.{u, 0} (ZMod N) j).obj M)) m c h
          (Stacks.TopTruncationExt.extPlus
            (y.mapExactFunctor (etaleModuleExtensionByZero.{u, 0} (ZMod N) j) : Ext _ _ m)))
        (add_zero c) := by
  let := etaleModules_enoughInjectives.{u, 0} (ZMod N) U
  have k := HomologicalDuality.extPlus_map_degreeZeroIso
    (etaleModuleDerivedExtensionByZero.{u, 0} (ZMod N) j) (isLE_derivedExtensionByZero_single N j)
    (isGE_derivedExtensionByZero_single N j) _ (derivedExtensionByZeroTopHomologyIso N j) y
  have k' : (Stacks.TopTruncationExt.extPlus y).map
      (etaleModuleDerivedExtensionByZero.{u, 0} (ZMod N) j) =
      (ShiftedHom.mk₀ (0 : ℤ) rfl (derivedExtensionByZeroDegreeZeroIso N j M).hom).comp
        ((Stacks.TopTruncationExt.extPlus
            (y.mapExactFunctor (etaleModuleExtensionByZero.{u, 0} (ZMod N) j) : Ext _ _ m)).comp
          (ShiftedHom.mk₀ (0 : ℤ) rfl (derivedExtensionByZeroDegreeZeroIso N j M').inv)
          (zero_add _)) (add_zero _) := by
    rw [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀, ← Category.assoc, ← k, Category.assoc,
      ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.comp_id]
  rw [traceMap_apply, traceMap_apply, ShiftedHom.comp_map, ShiftedHom.comp_map, k',
    ShiftedHom.map_comp, ShiftedHom.map_comp, ShiftedHom.map_mk₀, ShiftedHom.map_mk₀,
    ShiftedHom.map_comp, ShiftedHom.map_comp, ShiftedHom.map_mk₀, ShiftedHom.map_mk₀,
    ← ShiftedHom.comp_map]
  simp only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀]
  simp only [ShiftedHom.comp, CategoryTheory.Functor.map_comp, Category.assoc, Functor.comp_map]

/-- **Composing with the counit `j_! j⁻¹ F ⟶ F` is bijective** on morphisms
`(j_! j⁻¹ F)[0] ⟶ (j_! j⁻¹ F)[0][m]`, `m ≥ 0`: on `Ext^m(j_! j⁻¹ F, -)` it is the adjunction
`Ext^m(j⁻¹ F, j⁻¹ F) ≅ Ext^m(j_! j⁻¹ F, F)` composed with the inverse of `j_!`, both bijective. -/
theorem bijective_comp_extensionByZero_counit (F₀ : EtaleModules.{u, 0} (ZMod N) X) (m : ℕ) :
    Function.Bijective (fun z : ShiftedHom ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod N) j).obj
          ((etaleModuleRestriction.{u, 0} (ZMod N) j).obj F₀)))
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleExtensionByZero.{u, 0} (ZMod N) j).obj
            ((etaleModuleRestriction.{u, 0} (ZMod N) j).obj F₀))) (m : ℤ) =>
      z.comp (ShiftedHom.mk₀ (0 : ℤ) rfl ((DerivedCategory.Plus.singleFunctor _ 0).map
        ((etaleModuleExtensionByZeroAdj.{u, 0} (ZMod N) j).counit.app F₀))) (zero_add _)) := by
  let adj := etaleModuleExtensionByZeroAdj.{u, 0} (ZMod N) j
  let M := (etaleModuleRestriction.{u, 0} (ZMod N) j).obj F₀
  have hExt : Function.Bijective (fun y : Ext ((etaleModuleExtensionByZero.{u, 0} (ZMod N) j).obj M)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod N) j).obj M) m =>
        y.comp (Ext.mk₀ (adj.counit.app F₀)) (add_zero m)) := by
    have h₁ := Stacks.ExtAdjunction.extMap_bijective adj M F₀ m
    have h₂ := Stacks.ExtAdjunction.mapExtAddHom_bijective adj M M m
    have hfac : ⇑(Stacks.ExtAdjunction.extMap adj M F₀ m) =
        (fun y : Ext ((etaleModuleExtensionByZero.{u, 0} (ZMod N) j).obj M)
          ((etaleModuleExtensionByZero.{u, 0} (ZMod N) j).obj M) m =>
            y.comp (Ext.mk₀ (adj.counit.app F₀)) (add_zero m)) ∘
          ⇑((etaleModuleExtensionByZero.{u, 0} (ZMod N) j).mapExtAddHom M M m) := rfl
    exact (Function.Bijective.of_comp_iff _ h₂).1 (hfac ▸ h₁)
  have key : ∀ y : Ext ((etaleModuleExtensionByZero.{u, 0} (ZMod N) j).obj M)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod N) j).obj M) m,
      (Stacks.TopTruncationExt.extPlus y).comp (ShiftedHom.mk₀ (0 : ℤ) rfl
        ((DerivedCategory.Plus.singleFunctor _ 0).map (adj.counit.app F₀))) (zero_add _) =
      Stacks.TopTruncationExt.extPlus (y.comp (Ext.mk₀ (adj.counit.app F₀)) (add_zero m)) := by
    intro y
    rw [Stacks.TopTruncationExt.extPlus_comp, Stacks.TopTruncationExt.extPlus_mk₀,
      ShiftedHom.comp_mk₀, ShiftedHom.comp_mk₀]
  have hfac : (fun z : ShiftedHom ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod N) j).obj M))
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleExtensionByZero.{u, 0} (ZMod N) j).obj M)) (m : ℤ) =>
      z.comp (ShiftedHom.mk₀ (0 : ℤ) rfl ((DerivedCategory.Plus.singleFunctor _ 0).map
        (adj.counit.app F₀))) (zero_add _)) ∘ Stacks.TopTruncationExt.extPlus =
      Stacks.TopTruncationExt.extPlus ∘
        (fun y : Ext ((etaleModuleExtensionByZero.{u, 0} (ZMod N) j).obj M)
          ((etaleModuleExtensionByZero.{u, 0} (ZMod N) j).obj M) m =>
          y.comp (Ext.mk₀ (adj.counit.app F₀)) (add_zero m)) :=
    funext key
  exact (Function.Bijective.of_comp_iff _ (HomologicalDuality.extPlus_bijective _ _ m)).1
    (by rw [hfac]; exact (HomologicalDuality.extPlus_bijective _ _ m).comp hExt)

end ExtensionByZero

/-! ### The top-degree trace -/

section TopTrace

variable {U S : Scheme.{u}} (f : U ⟶ S) (jf : CompactificationOf (Over.mk f)) (N : ℕ) [NeZero N]
  (hf : ∀ y : S, topologicalKrullDim (jf.toBase.fiber y) ≤ 1)
  (ν : etaleModuleInverseImage.{u, 0} (ZMod N) f ⋙ DerivedCategory.Plus.singleFunctor _ 0 ⋙
    derivedLowerShriek.{u, 0} f jf (ZMod N) ⋙ DerivedCategory.Plus.homologyFunctor _ 2 ≅
      𝟭 (EtaleModules.{u, 0} (ZMod N) S))

/-- **The top-degree trace of a family of curves is invertible on `R²`.** -/
theorem isIso_homologyFunctor_map_lowerShriekTopTrace (X : EtaleModules.{u, 0} (ZMod N) S) :
    IsIso ((DerivedCategory.homologyFunctor _ 2).map (lowerShriekTopTrace f jf N hf ν X)) := by
  dsimp only [lowerShriekTopTrace, Stacks.TopTruncationExt.topTrace]
  rw [CategoryTheory.Functor.map_comp]
  have h := Stacks.TopTruncationExt.homologyFunctor_map_topProj _ 2
    (isLE_derivedLowerShriek_inverseImage_single f jf N hf X)
  have : IsIso ((DerivedCategory.homologyFunctor _ 2).map
      (Stacks.TopTruncationExt.topProj _ 2
        (isLE_derivedLowerShriek_inverseImage_single f jf N hf X)) ≫
      (Stacks.TopTruncationExt.singleShiftHomologyIso
        (B := EtaleModules.{u, 0} (ZMod N) S) 2).hom.app _) := by
    rw [h]
    infer_instance
  have hA := IsIso.of_isIso_comp_right ((DerivedCategory.homologyFunctor _ 2).map
      (Stacks.TopTruncationExt.topProj _ 2
        (isLE_derivedLowerShriek_inverseImage_single f jf N hf X)))
    ((Stacks.TopTruncationExt.singleShiftHomologyIso
      (B := EtaleModules.{u, 0} (ZMod N) S) 2).hom.app _)
  have hB : IsIso ((DerivedCategory.homologyFunctor _ 2).map
      ((shiftFunctor (DerivedCategory (EtaleModules.{u, 0} (ZMod N) S)) (-2)).map
        ((DerivedCategory.singleFunctor _ 0).map (ν.hom.app X)))) := by
    infer_instance
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ hA hB

end TopTrace

/-! ### Changing the compactification -/

section Compactification

variable {U S : Scheme.{u}} (f : U ⟶ S) [CompactSpace S] [QuasiSeparatedSpace S] [IsSeparated f]
  [LocallyOfFiniteType f] [QuasiCompact f] (N : ℕ) [NeZero N]

/-- **The trace map of `Rf_!` along one compactification is that along another, up to an
isomorphism of `Rf_!(B)` composed into the trace** (Tag 0F7I; the comparison of the two
compactifications need not commute with the shifts, its defect is absorbed into the trace). -/
theorem exists_bijective_traceMap_iff_of_compactification (jf jc : CompactificationOf (Over.mk f))
    (B : DerivedCategory.Plus (EtaleModules.{u, 0} (ZMod N) U))
    {L : DerivedCategory (EtaleModules.{u, 0} (ZMod N) S)} {c₀ : ℤ}
    (t : ShiftedHom ((derivedLowerShriek.{u, 0} f jf (ZMod N) ⋙ DerivedCategory.Plus.ι).obj B) L c₀)
    (A : DerivedCategory.Plus (EtaleModules.{u, 0} (ZMod N) U)) (m c : ℤ) (h : c₀ + m = c) :
    ∃ g : (derivedLowerShriek.{u, 0} f jc (ZMod N) ⋙ DerivedCategory.Plus.ι).obj B ≅
        (derivedLowerShriek.{u, 0} f jf (ZMod N) ⋙ DerivedCategory.Plus.ι).obj B,
      Function.Bijective (traceMap (derivedLowerShriek.{u, 0} f jf (ZMod N) ⋙
          DerivedCategory.Plus.ι) t A m c h) ↔
        Function.Bijective (traceMap (derivedLowerShriek.{u, 0} f jc (ZMod N) ⋙
          DerivedCategory.Plus.ι) (g.hom ≫ t) A m c h) := by
  have hT : ∀ K, isTorsionPlus.{u, 0} (ZMod N) U K := fun K _ =>
    isTorsionEtaleModule_of_natCast_eq_zero (ZMod N) N (Nat.pos_of_ne_zero (NeZero.ne N))
      (ZMod.natCast_self N) _
  let α := derivedLowerShriekCompactificationIso f jc jf (ZMod N)
  let αX : ∀ K, (derivedLowerShriek.{u, 0} f jc (ZMod N) ⋙ DerivedCategory.Plus.ι).obj K ≅
      (derivedLowerShriek.{u, 0} f jf (ZMod N) ⋙ DerivedCategory.Plus.ι).obj K :=
    fun K => DerivedCategory.Plus.ι.mapIso (α.app ⟨K, hT K⟩)
  have hα : ∀ y : A ⟶ B⟦m⟧,
      (derivedLowerShriek.{u, 0} f jc (ZMod N) ⋙ DerivedCategory.Plus.ι).map y ≫ (αX (B⟦m⟧)).hom =
        (αX A).hom ≫ (derivedLowerShriek.{u, 0} f jf (ZMod N) ⋙ DerivedCategory.Plus.ι).map y := by
    intro y
    have := congrArg DerivedCategory.Plus.ι.map (α.hom.naturality
      (ObjectProperty.homMk y : (⟨A, hT A⟩ : (isTorsionPlus.{u, 0} (ZMod N) U).FullSubcategory) ⟶
        ⟨B⟦m⟧, hT _⟩))
    simp only [Functor.comp_map, ObjectProperty.ι_map, ObjectProperty.homMk_hom] at this
    exact this
  obtain ⟨s, hs⟩ := exists_traceMap_eq_of_iso
    (Φ := derivedLowerShriek.{u, 0} f jc (ZMod N) ⋙ DerivedCategory.Plus.ι)
    (derivedLowerShriek.{u, 0} f jf (ZMod N) ⋙ DerivedCategory.Plus.ι) (αX A) (αX B) (αX (B⟦m⟧))
    hα t
  refine ⟨s ≪≫ αX B, ?_⟩
  have e : ⇑(traceMap (derivedLowerShriek.{u, 0} f jf (ZMod N) ⋙ DerivedCategory.Plus.ι)
      t A m c h) =
      (fun x => (ShiftedHom.mk₀ (0 : ℤ) rfl (αX A).inv).comp x (add_zero c)) ∘
        traceMap (derivedLowerShriek.{u, 0} f jc (ZMod N) ⋙ DerivedCategory.Plus.ι)
          (s.hom ≫ (αX B).hom ≫ t) A m c h :=
    funext (hs c h)
  rw [e]
  simp only [Iso.trans_hom, Category.assoc]
  exact Function.Bijective.of_comp_iff' (bijective_mk₀_comp_of_iso (αX A).symm c) _

end Compactification

/-- Precomposing with a morphism that is invertible on `H²` keeps a trace invertible on `H²`. -/
private theorem isIso_homologyFunctor_map_mk₀_comp {B : Type*} [Category* B] [Abelian B]
    [HasDerivedCategory B] {K K' L : DerivedCategory B} (φ : K ⟶ K') (t : ShiftedHom K' L (-2))
    [IsIso ((DerivedCategory.homologyFunctor _ 2).map φ)]
    [IsIso ((DerivedCategory.homologyFunctor _ 2).map t)] :
    IsIso ((DerivedCategory.homologyFunctor _ 2).map
      ((ShiftedHom.mk₀ (0 : ℤ) rfl φ).comp t (add_zero _))) := by
  rw [ShiftedHom.mk₀_comp, CategoryTheory.Functor.map_comp]
  infer_instance

/-! ### Through the compactification of the fibration -/

section Factorization

variable {U S Xbar : Scheme.{u}} (f : U ⟶ S) (j : U ⟶ Xbar) [IsOpenImmersion j] (fbar : Xbar ⟶ S)
  (hjf : j ≫ fbar = f) [IsProper fbar] (N : ℕ)


/-- **Through the compactification `j : U → X̄` the trace map of `Rf_!` is that of `Rf̄_*` at
`j_! M`**, `j_!` being bijective on `Ext`; a top-degree trace on `Rf_! M` is one on
`Rf̄_*(j_! M)`. -/
theorem bijective_traceMap_factorization (M : EtaleModules.{u, 0} (ZMod N) U)
    (Λ : EtaleModules.{u, 0} (ZMod N) S)
    (t : ShiftedHom ((etaleModuleDerivedDirectImage.{u, 0} (ZMod N) fbar ⋙
      DerivedCategory.Plus.ι).obj ((etaleModuleDerivedExtensionByZero.{u, 0} (ZMod N) j).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj M)))
        ((DerivedCategory.singleFunctor _ 0).obj Λ) (-2))
    (ht : IsIso ((DerivedCategory.homologyFunctor _ 2).map t))
    (hK : DerivedCategory.TStructure.t.IsLE
      ((etaleModuleDerivedDirectImage.{u, 0} (ZMod N) fbar ⋙ DerivedCategory.Plus.ι).obj
        ((etaleModuleDerivedExtensionByZero.{u, 0} (ZMod N) j).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj M))) 2)
    (m : ℕ) {c : ℤ} (h : -2 + (m : ℤ) = c)
    (H : ((etaleModuleDerivedDirectImage.{u, 0} (ZMod N) fbar ⋙ DerivedCategory.Plus.ι).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleExtensionByZero.{u, 0} (ZMod N) j).obj M))).IsLE 2 →
      ∀ t₂ : ShiftedHom ((etaleModuleDerivedDirectImage.{u, 0} (ZMod N) fbar ⋙
          DerivedCategory.Plus.ι).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((etaleModuleExtensionByZero.{u, 0} (ZMod N) j).obj M)))
          ((DerivedCategory.singleFunctor _ 0).obj Λ) (-2),
        IsIso ((DerivedCategory.homologyFunctor _ 2).map t₂) →
        Function.Bijective (traceMap (etaleModuleDerivedDirectImage.{u, 0} (ZMod N) fbar ⋙
          DerivedCategory.Plus.ι) t₂ ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((etaleModuleExtensionByZero.{u, 0} (ZMod N) j).obj M)) m c h)) :
    Function.Bijective (traceMap (derivedLowerShriek.{u, 0} f
      (compactificationOfFactorization f j fbar hjf) (ZMod N) ⋙ DerivedCategory.Plus.ι) t
        ((DerivedCategory.Plus.singleFunctor _ 0).obj M) m c h) := by
  have hK₂ := DerivedCategory.TStructure.t.isLE_of_iso
    ((etaleModuleDerivedDirectImage.{u, 0} (ZMod N) fbar ⋙ DerivedCategory.Plus.ι).mapIso
      (derivedExtensionByZeroDegreeZeroIso N j M)) 2
  have H' := H hK₂ _ (isIso_homologyFunctor_map_mk₀_comp
    ((etaleModuleDerivedDirectImage.{u, 0} (ZMod N) fbar ⋙ DerivedCategory.Plus.ι).map
      (derivedExtensionByZeroDegreeZeroIso N j M).inv) t)
  rw [← Function.Bijective.of_comp_iff _ (HomologicalDuality.extPlus_bijective M M m)]
  have e₂ : ⇑(traceMap (derivedLowerShriek.{u, 0} f
      (compactificationOfFactorization f j fbar hjf) (ZMod N) ⋙ DerivedCategory.Plus.ι) t
        ((DerivedCategory.Plus.singleFunctor _ 0).obj M) m c h) ∘ Stacks.TopTruncationExt.extPlus =
      (fun x => (ShiftedHom.mk₀ (0 : ℤ) rfl
          ((etaleModuleDerivedDirectImage.{u, 0} (ZMod N) fbar ⋙ DerivedCategory.Plus.ι).map
            (derivedExtensionByZeroDegreeZeroIso N j M).hom)).comp x (add_zero c)) ∘
        ⇑(traceMap (etaleModuleDerivedDirectImage.{u, 0} (ZMod N) fbar ⋙ DerivedCategory.Plus.ι)
          ((ShiftedHom.mk₀ (0 : ℤ) rfl
            ((etaleModuleDerivedDirectImage.{u, 0} (ZMod N) fbar ⋙ DerivedCategory.Plus.ι).map
              (derivedExtensionByZeroDegreeZeroIso N j M).inv)).comp t (add_zero _))
            ((DerivedCategory.Plus.singleFunctor _ 0).obj
              ((etaleModuleExtensionByZero.{u, 0} (ZMod N) j).obj M)) m c h) ∘
          Stacks.TopTruncationExt.extPlus ∘
            ⇑((etaleModuleExtensionByZero.{u, 0} (ZMod N) j).mapExtAddHom M M m) := by
    funext y
    simp only [Function.comp_apply, Functor.mapExtAddHom_apply]
    exact traceMap_derivedExtensionByZero_extPlus N j
      (etaleModuleDerivedDirectImage.{u, 0} (ZMod N) fbar) t m h y
  rw [e₂]
  exact (bijective_mk₀_comp_of_iso
    ((etaleModuleDerivedDirectImage.{u, 0} (ZMod N) fbar ⋙ DerivedCategory.Plus.ι).mapIso
      (derivedExtensionByZeroDegreeZeroIso N j M)) c).comp
    (H'.comp ((HomologicalDuality.extPlus_bijective _ _ m).comp
      (Stacks.ExtAdjunction.mapExtAddHom_bijective
        (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod N) j) M M m)))

end Factorization

/-! ### Changing the dualizing object along the counit `j_! j⁻¹ Λ ⟶ Λ` -/

section Counit

variable {U S Xbar : Scheme.{u}} (j : U ⟶ Xbar) [IsOpenImmersion j] (fbar : Xbar ⟶ S) (N : ℕ)

/-- **From `F₀` to `j_! M` with `M ≅ j⁻¹ F₀`**: if the trace map of `Rf̄_*` is bijective at
`j_! j⁻¹ F₀` for every top-degree trace on `Rf̄_* F₀`, it is bijective at `j_! M` for every
top-degree trace on `Rf̄_*(j_! M)`, as soon as the counit `j_! j⁻¹ F₀ ⟶ F₀` is invertible on
`R²f̄_*`: composing with the counit is bijective on `Ext^m(j_! j⁻¹ F₀, -)`, and carries a
top-degree trace on `Rf̄_* F₀` to one on `Rf̄_*(j_! j⁻¹ F₀)`. -/
theorem bijective_traceMap_extensionByZero (F₀ : EtaleModules.{u, 0} (ZMod N) Xbar)
    (M : EtaleModules.{u, 0} (ZMod N) U)
    (eM : M ≅ (etaleModuleRestriction.{u, 0} (ZMod N) j).obj F₀)
    (Λ : EtaleModules.{u, 0} (ZMod N) S)
    (hK₀ : ((etaleModuleDerivedDirectImage.{u, 0} (ZMod N) fbar ⋙ DerivedCategory.Plus.ι).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F₀)).IsLE 2)
    (hK₂ : ((etaleModuleDerivedDirectImage.{u, 0} (ZMod N) fbar ⋙ DerivedCategory.Plus.ι).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod N) j).obj M))).IsLE 2)
    (hH : IsIso ((DerivedCategory.homologyFunctor _ 2).map
      ((etaleModuleDerivedDirectImage.{u, 0} (ZMod N) fbar ⋙ DerivedCategory.Plus.ι).map
        ((DerivedCategory.Plus.singleFunctor _ 0).map
          ((etaleModuleExtensionByZeroAdj.{u, 0} (ZMod N) j).counit.app F₀)))))
    (H₁ : ∀ t₃ : ShiftedHom ((etaleModuleDerivedDirectImage.{u, 0} (ZMod N) fbar ⋙
        DerivedCategory.Plus.ι).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F₀))
        ((DerivedCategory.singleFunctor _ 0).obj Λ) (-2),
      IsIso ((DerivedCategory.homologyFunctor _ 2).map t₃) →
        IsBijectiveAt (etaleModuleDerivedDirectImage.{u, 0} (ZMod N) fbar ⋙ DerivedCategory.Plus.ι)
          t₃ ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((etaleModuleExtensionByZero.{u, 0} (ZMod N) j).obj
              ((etaleModuleRestriction.{u, 0} (ZMod N) j).obj F₀))))
    (t₂ : ShiftedHom ((etaleModuleDerivedDirectImage.{u, 0} (ZMod N) fbar ⋙
        DerivedCategory.Plus.ι).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleExtensionByZero.{u, 0} (ZMod N) j).obj M)))
        ((DerivedCategory.singleFunctor _ 0).obj Λ) (-2))
    (ht₂ : IsIso ((DerivedCategory.homologyFunctor _ 2).map t₂)) (m : ℕ) {c : ℤ}
    (h : -2 + (m : ℤ) = c) :
    Function.Bijective (traceMap (etaleModuleDerivedDirectImage.{u, 0} (ZMod N) fbar ⋙
      DerivedCategory.Plus.ι) t₂ ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod N) j).obj M)) m c h) := by
  let G := etaleModuleDerivedDirectImage.{u, 0} (ZMod N) fbar ⋙ DerivedCategory.Plus.ι
  let P := DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} (ZMod N) Xbar) 0
  let ε := (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod N) j).counit.app F₀
  let E : P.obj ((etaleModuleExtensionByZero.{u, 0} (ZMod N) j).obj M) ≅
      P.obj ((etaleModuleExtensionByZero.{u, 0} (ZMod N) j).obj
        ((etaleModuleRestriction.{u, 0} (ZMod N) j).obj F₀)) :=
    P.mapIso ((etaleModuleExtensionByZero.{u, 0} (ZMod N) j).mapIso eM)
  let t₂' := (ShiftedHom.mk₀ (0 : ℤ) rfl (G.map E.inv)).comp t₂ (add_zero _)
  have ht₂e : (ShiftedHom.mk₀ (0 : ℤ) rfl (G.map E.hom)).comp t₂' (add_zero _) = t₂ := by
    simp only [t₂', ShiftedHom.mk₀_comp]
    rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have ht₂' : IsIso ((DerivedCategory.homologyFunctor _ 2).map t₂') :=
    isIso_homologyFunctor_map_mk₀_comp _ t₂
  rw [← ht₂e, bijective_traceMap_mk₀_map_comp_iff E t₂']
  refine bijective_traceMap_of_iso E.symm h ?_
  -- a top-degree trace on `Rf̄_* F₀`
  let σ := (Stacks.TopTruncationExt.singleShiftHomologyIso
    (B := EtaleModules.{u, 0} (ZMod N) S) 2).app Λ
  let g : (DerivedCategory.homologyFunctor _ 2).obj (G.obj (P.obj F₀)) ≅ Λ :=
    (asIso ((DerivedCategory.homologyFunctor _ 2).map (G.map (P.map ε)))).symm ≪≫
      asIso ((DerivedCategory.homologyFunctor _ 2).map t₂') ≪≫ σ
  obtain ⟨t₃, ht₃e⟩ := (Stacks.TopTruncationExt.bijective_homologyFunctor_map
    (G.obj (P.obj F₀)) 2 hK₀ Λ).2 g.hom
  replace ht₃e : (DerivedCategory.homologyFunctor _ 2).map t₃ ≫ σ.hom = g.hom := ht₃e
  have ht₃ : IsIso ((DerivedCategory.homologyFunctor _ 2).map t₃) := by
    have : IsIso ((DerivedCategory.homologyFunctor _ 2).map t₃ ≫ σ.hom) := by
      rw [ht₃e]
      infer_instance
    exact IsIso.of_isIso_comp_right _ σ.hom
  -- rigidity on `Rf̄_*(j_! j⁻¹ F₀)`
  have := hK₂
  have hK₂' : (G.obj (P.obj ((etaleModuleExtensionByZero.{u, 0} (ZMod N) j).obj
      ((etaleModuleRestriction.{u, 0} (ZMod N) j).obj F₀)))).IsLE 2 :=
    DerivedCategory.TStructure.t.isLE_of_iso (G.mapIso E) 2
  have hs := isIso_homologyFunctor_map_mk₀_comp (G.map (P.map ε)) t₃
  rw [bijective_traceMap_iff_of_isIso_homology G 2 hK₂' t₂' _ ht₂' hs]
  have e : ⇑(traceMap G ((ShiftedHom.mk₀ (0 : ℤ) rfl (G.map (P.map ε))).comp t₃ (add_zero _))
      (P.obj ((etaleModuleExtensionByZero.{u, 0} (ZMod N) j).obj
        ((etaleModuleRestriction.{u, 0} (ZMod N) j).obj F₀))) m c h) =
      ⇑(traceMap G t₃ (P.obj ((etaleModuleExtensionByZero.{u, 0} (ZMod N) j).obj
        ((etaleModuleRestriction.{u, 0} (ZMod N) j).obj F₀))) m c h) ∘
        (fun z => z.comp (ShiftedHom.mk₀ (0 : ℤ) rfl (P.map ε)) (zero_add _)) :=
    funext (traceMap_mk₀_map_comp (P.map ε) t₃ _ m c h)
  rw [e]
  exact (H₁ t₃ ht₃ m c h).comp (bijective_comp_extensionByZero_counit N j F₀ m)

end Counit

/-! ### The two inputs on the compactification -/

section Inputs

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [IsAlgClosed k]

/-- **Relative Poincaré duality for a smooth projective curve**: for `f̄ : X̄ → S` smooth
projective of relative dimension one with geometrically irreducible fibres, over `S` affine and
smooth over `k`, `ℓ` invertible in `k`, and every morphism `t : Rf̄_* Λ ⟶ Λ[-2]` inducing an
isomorphism `R²f̄_* Λ ≅ Λ` (a top-degree trace), the map
`Hom_X̄(Λ, Λ[m]) → Hom_S(Rf̄_* Λ, Λ[m - 2])`, `y ↦ t[m] ∘ Rf̄_*(y)`, is bijective for every
integer `m` (`Rf̄_* Λ ≅ R𝓗om(Rf̄_* Λ, Λ)[-2]` on global sections). -/
def ProperCurveRelativeDualityInput : Prop :=
  IsUnit (ℓ : k) → ∀ (S Xbar : Scheme.{u}) (q : S ⟶ Spec (.of k)) (e : ℕ)
    [SmoothOfRelativeDimension e q] [IsAffine S] (fbar : Xbar ⟶ S)
    [SmoothOfRelativeDimension 1 fbar] [GeometricallyIrreducible fbar], IsProjectiveMorphism fbar →
    ∀ t : ShiftedHom ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙
        DerivedCategory.Plus.ι).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) fbar).obj (unitSheaf (X := S) ℓ))))
        ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) (-2),
      IsIso ((DerivedCategory.homologyFunctor _ 2).map t) →
      IsBijectiveAt (etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙ DerivedCategory.Plus.ι) t
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) fbar).obj (unitSheaf (X := S) ℓ)))

/-- **Duality along an étale boundary divisor of a smooth projective curve**: in the setting of
`Stacks.EtaleCohomology.ProperCurveRelativeDualityInput`, for a closed immersion `i : Z → X̄` with
`Z → S` finite étale and every top-degree trace `t : Rf̄_* Λ ⟶ Λ[-2]`, the map
`Hom_X̄(i_* Λ_Z, Λ[m]) → Hom_S(Rf̄_* i_* Λ_Z, Λ[m - 2])`, `y ↦ t[m] ∘ Rf̄_*(y)`, is bijective
for every integer `m`. By cohomological purity `Hom_X̄(i_* Λ_Z, Λ[m]) ≅ H^{m - 2}(Z, Λ(-1))`, and
`Hom_S(π_* Λ_Z, Λ[m - 2]) ≅ H^{m - 2}(Z, Λ)` for the finite étale `π = f̄ ∘ i`. -/
def BoundaryDivisorDualityInput : Prop :=
  IsUnit (ℓ : k) → ∀ (S Xbar Z : Scheme.{u}) (q : S ⟶ Spec (.of k)) (e : ℕ)
    [SmoothOfRelativeDimension e q] [IsAffine S] (fbar : Xbar ⟶ S) (i : Z ⟶ Xbar)
    [SmoothOfRelativeDimension 1 fbar] [GeometricallyIrreducible fbar] [IsClosedImmersion i]
    [IsFinite (i ≫ fbar)] [Etale (i ≫ fbar)], IsProjectiveMorphism fbar →
    ∀ t : ShiftedHom ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙
        DerivedCategory.Plus.ι).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) fbar).obj (unitSheaf (X := S) ℓ))))
        ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) (-2),
      IsIso ((DerivedCategory.homologyFunctor _ 2).map t) →
      IsBijectiveAt (etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙ DerivedCategory.Plus.ι) t
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj
            ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) i).obj
              ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) fbar).obj (unitSheaf (X := S) ℓ)))))

omit [IsAlgClosed k] in
/-- **Relative Poincaré duality for an elementary fibration, from the compactification**: relative
duality for the smooth projective curve `f̄ : X̄ → S` (at `Λ_X̄`) and along the étale boundary
divisor `Z` (at `i_* Λ_Z`) give relative duality for `f : U = X̄ ∖ Z → S`. -/
@[sga "4½ Dualite 2.2" "special case"]
theorem relativeCurveDualityInput_of_inputs (hd : BoundaryDivisorDualityInput ℓ k)
    (he : ProperCurveRelativeDualityInput ℓ k) : RelativeCurveDualityInput ℓ k := by
  intro hℓ U S q f e _ _ hfib jf hf ν m c h₁
  obtain ⟨Xbar, Z, j, fbar, i, hj, hjf, hsm, hproj, hgi, hi, hZ, hrange, hfin, het, hsurj⟩ :=
    hfib.exists_compactification
  have := hj
  have := hsm
  have := hgi
  have := hi
  have := hfin
  have := het
  have : IsProper fbar := isProper_of_isProjectiveMorphism fbar hproj
  have : Smooth q := SmoothOfRelativeDimension.smooth e q
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian q
  have : IsNoetherian S := ⟨⟩
  have : CompactSpace Xbar := ⟨by
    simpa using QuasiCompact.isCompact_preimage (f := fbar) Set.univ isOpen_univ isCompact_univ⟩
  have : IsLocallyNoetherian Xbar := LocallyOfFiniteType.isLocallyNoetherian fbar
  have : IsNoetherian Xbar := ⟨⟩
  have : TopologicalSpace.NoetherianSpace U := j.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact f := by rw [← hjf]; infer_instance
  have : IsSeparated f := by rw [← hjf]; infer_instance
  have : LocallyOfFiniteType f := by rw [← hjf]; infer_instance
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have hij : Set.range j.base = (Set.range i.base)ᶜ := by rw [hrange, compl_compl]
  -- `f⁻¹ Λ ≅ j⁻¹ f̄⁻¹ Λ`
  let eU : (etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).obj (unitSheaf (X := S) ℓ) ≅
      (etaleModuleRestriction.{u, 0} (ZMod ℓ) j).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) fbar).obj (unitSheaf (X := S) ℓ)) :=
    (eqToIso (congrArg (etaleModuleInverseImage.{u, 0} (ZMod ℓ)) hjf.symm) ≪≫
      etaleModuleInverseImageCompIso.{u, 0} (ZMod ℓ) j fbar ≪≫
      Functor.isoWhiskerLeft (etaleModuleInverseImage.{u, 0} (ZMod ℓ) fbar)
        (etaleModuleInverseImageRestrictionIso.{u, 0} (ZMod ℓ) j)).app (unitSheaf (X := S) ℓ)
  -- the statement as the bijectivity of a trace map
  suffices H : Function.Bijective (traceMap
      (derivedLowerShriek.{u, 0} f jf (ZMod ℓ) ⋙ DerivedCategory.Plus.ι)
      (lowerShriekTopTrace f jf ℓ hf ν (unitSheaf (X := S) ℓ))
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).obj (unitSheaf (X := S) ℓ))) m c h₁) by
    exact H.comp (HomologicalDuality.extPlus_bijective _ _ m)
  -- change the compactification to `j`
  obtain ⟨g, hg⟩ := exists_bijective_traceMap_iff_of_compactification f ℓ jf
    (compactificationOfFactorization f j fbar hjf) _
    (lowerShriekTopTrace f jf ℓ hf ν (unitSheaf (X := S) ℓ)) _ m c h₁
  rw [hg]
  have hKU : DerivedCategory.TStructure.t.IsLE
      ((derivedLowerShriek.{u, 0} f jf (ZMod ℓ) ⋙ DerivedCategory.Plus.ι).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).obj (unitSheaf (X := S) ℓ)))) 2 :=
    isLE_derivedLowerShriek_inverseImage_single f jf ℓ hf (unitSheaf (X := S) ℓ)
  have hTU := isIso_homologyFunctor_map_lowerShriekTopTrace f jf ℓ hf ν (unitSheaf (X := S) ℓ)
  have ht : IsIso ((DerivedCategory.homologyFunctor _ 2).map
      (g.hom ≫ lowerShriekTopTrace f jf ℓ hf ν (unitSheaf (X := S) ℓ))) := by
    rw [CategoryTheory.Functor.map_comp]
    infer_instance
  -- through `Rf_! = Rf̄_* ∘ Rj_!`
  refine bijective_traceMap_factorization f j fbar hjf ℓ _ (unitSheaf (X := S) ℓ) _ ht
    (DerivedCategory.TStructure.t.isLE_of_iso g.symm 2) m h₁ (fun hK₂ t₂ ht₂ => ?_)
  -- the facts on `Rf̄_*`
  obtain ⟨hz, hS⟩ := shortExact_etaleModuleExtensionByZero_directImage (ZMod ℓ) i j hij
    ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) fbar).obj (unitSheaf (X := S) ℓ))
  have hT := (etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙
    DerivedCategory.Plus.ι).map_distinguished _
      (Stacks.TopTruncationExt.plusSingleTriangle_distinguished hS)
  have hK₁ : DerivedCategory.TStructure.t.IsLE
      ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙
        DerivedCategory.Plus.ι).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) j).obj
            ((etaleModuleRestriction.{u, 0} (ZMod ℓ) j).obj
              ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) fbar).obj (unitSheaf (X := S) ℓ)))))) 2 :=
    DerivedCategory.TStructure.t.isLE_of_iso
      ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙ DerivedCategory.Plus.ι).mapIso
        ((DerivedCategory.Plus.singleFunctor _ 0).mapIso
          ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) j).mapIso eU))) 2
  have hK₃ : DerivedCategory.TStructure.t.IsLE
      ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙
        DerivedCategory.Plus.ι).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj
            ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) i).obj
              ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) fbar).obj
                (unitSheaf (X := S) ℓ)))))) 2 := by
    refine (DerivedCategory.isLE_iff _ 2).2 fun p hp => ?_
    exact (isZero_singleHomology_directImage_of_isFinite (ZMod ℓ) i fbar _ p (by omega)).of_iso
      ((singleHomologyPlusSingleIso
        (etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar) p).app _).symm
  have hK₀ : ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙ DerivedCategory.Plus.ι).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) fbar).obj (unitSheaf (X := S) ℓ)))).IsLE 2 :=
    DerivedCategory.TStructure.t.isLE₂ _ hT 2 hK₁ hK₃
  have hH : IsIso ((DerivedCategory.homologyFunctor _ 2).map
      ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙ DerivedCategory.Plus.ι).map
        ((DerivedCategory.Plus.singleFunctor _ 0).map
          ((etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) j).counit.app
            ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) fbar).obj (unitSheaf (X := S) ℓ)))))) :=
    (NatIso.isIso_map_iff (singleHomologyPlusSingleIso
      (etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar) 2) _).1
      (isIso_singleHomology_map_extensionByZero_counit (ZMod ℓ) i j hij fbar _ 2 le_rfl)
  -- the five lemma on `0 → j_! j⁻¹ Λ → Λ → i_* i⁻¹ Λ → 0`
  have H₁ : ∀ t₃ : ShiftedHom ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙
        DerivedCategory.Plus.ι).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) fbar).obj (unitSheaf (X := S) ℓ))))
        ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) (-2),
      IsIso ((DerivedCategory.homologyFunctor _ 2).map t₃) →
        IsBijectiveAt (etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) fbar ⋙ DerivedCategory.Plus.ι)
          t₃ ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) j).obj
              ((etaleModuleRestriction.{u, 0} (ZMod ℓ) j).obj
                ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) fbar).obj (unitSheaf (X := S) ℓ))))) :=
    fun t₃ ht₃ => isBijectiveAt_obj₁ _ (Stacks.TopTruncationExt.plusSingleTriangle_distinguished hS)
      (he hℓ S Xbar q e fbar hproj t₃ ht₃) (hd hℓ S Xbar Z q e fbar i hproj t₃ ht₃)
  exact bijective_traceMap_extensionByZero j fbar ℓ _ _ eU _ hK₀ hK₂ hH H₁ t₂ ht₂ m h₁

end Inputs

end Stacks.EtaleCohomology

end
