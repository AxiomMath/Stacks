module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.StableModel.FibreMaps
public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.StableModel
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberComponentCartier
public import StacksFrontier.AlgebraicGeometry.Curves.Models.StableModel.SpecialFibreMorphism.AmpleFactorization
public import StacksFrontier.AlgebraicGeometry.Curves.Models.StableModel.SpecialFibreMorphism.NonContractedFinite
public import StacksFrontier.AlgebraicGeometry.PicardFibreTrivial.Basic

/-!
# The stable model of the special fibre maps finitely onto the special fibre of the contraction

In the situation of [Stacks, Tag 0C61] let `c₀ : X_k ⟶ Y₀` be a stable contraction of the special
fibre ([Stacks, Tag 0E7Q]) and `ℒ₀` an ample invertible module on `Y₀`. Let `φ : X ⟶ P` be a
morphism over `R` to a proper `R`-scheme with an ample invertible `A` such that
`c₀^*ℒ₀ ≅ (φ^*A)|_{X_k}`, and let `X ⟶ Y ⟶ P` be the Stein factorization of `φ`, with first factor
`c` and finite second factor `π`. Then the morphism of special fibres `c_k : X_k ⟶ Y_k` factors as
`c_k = h ∘ c₀` with `h : Y₀ ⟶ Y_k` finite.

The pullback `L` of `A` to `Y_k` is ample, `Y_k ⟶ P` being finite, and `c_k^*L ≅ c₀^*ℒ₀`; since
`𝒪_{Y₀} = c₀_*𝒪_{X_k}`, sections of powers of `L` pull back to sections descending to `Y₀`, which
produces `h` chart by chart
(`Stacks.ContractionComparison.exists_comp_eq_of_isAmple_of_isIso_unitToPushforwardObjUnit_left`,
which does not need `𝒪_{Y_k} = c_{k*}𝒪_{X_k}`). Then `h^*L ≅ ℒ₀`, pullback along `c₀` being
injective on invertible modules; so `h` contracts no component of `Y₀` (an ample module has
positive degree on each), hence is quasi-finite, and it is proper, hence finite
(`AlgebraicGeometry.Scheme.Hom.isFinite_of_pullback_iso_of_isAmple`).

## Main results

* `Stacks.Models.RegularProperModelSituation.exists_isFinite_comp_eq_specialFiberMap`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Models.RegularProperModelSituation

variable (S : RegularProperModelSituation.{u})

/-- **The special fibre of the Stein factorization receives a finite morphism from the stable
model of the special fibre**, through which the morphism of special fibres factors. -/
theorem exists_isFinite_comp_eq_specialFiberMap
    {Y₀ : Scheme.{u}} {g₀ : Y₀ ⟶ Spec (.of S.k)} {c₀ : S.specialFiber ⟶ Y₀}
    (hc₀ : Stacks.Curves.StableModel.IsStableContraction S.specialFiberToSpec g₀ c₀)
    (L₀ : Y₀.Modules) [SheafOfModules.IsInvertible Y₀.toRingedSpace.presheaf
      (structureSheafRing Y₀.toRingedSpace).property L₀]
    (hL₀ : Scheme.Modules.IsAmple Y₀ L₀)
    {P : Scheme.{u}} (q : P ⟶ Spec (.of S.R)) [IsProper q] (φ : S.X ⟶ P)
    (hφ : φ ≫ q = S.X_to_R) (A : P.Modules) [SheafOfModules.IsInvertible P.toRingedSpace.presheaf
      (structureSheafRing P.toRingedSpace).property A]
    (hA : Scheme.Modules.IsAmple P A)
    (α : (Scheme.Modules.pullback c₀).obj L₀ ≅
      (Scheme.Modules.pullback S.specialFiberι).obj ((Scheme.Modules.pullback φ).obj A))
    {Y : Scheme.{u}} (c : S.X ⟶ Y) (π : Y ⟶ P) (hcπ : c ≫ π = φ) [IsProper c] [IsFinite π]
    (_hsurj : Function.Surjective c)
    (_hO : IsIso (SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom)) :
    ∃ h : Y₀ ⟶ pullback (π ≫ q) (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k))),
      IsFinite h ∧
        c₀ ≫ h = S.specialFiberMap (π ≫ q) c (by rw [← Category.assoc, hcπ, hφ]) := by
  have hcq : c ≫ π ≫ q = S.X_to_R := by rw [← Category.assoc, hcπ, hφ]
  set pk := Spec.map (CommRingCat.ofHom (algebraMap S.R S.k))
  set ck := S.specialFiberMap (π ≫ q) c hcq
  let j := pullback.fst (π ≫ q) pk
  let gk := pullback.snd (π ≫ q) pk
  have hckj : ck ≫ j = S.specialFiberι ≫ c := S.specialFiberMap_fst (π ≫ q) c hcq
  have hckg : ck ≫ gk = S.specialFiberToSpec := S.specialFiberMap_snd (π ≫ q) c hcq
  -- the ample module `L` on `Y_k`
  have : IsClosedImmersion pk :=
    IsClosedImmersion.spec_of_surjective _ S.surjective_algebraMap_residueField
  have : IsClosedImmersion j := by dsimp [j]; infer_instance
  have : IsFinite (j ≫ π) := inferInstance
  have : IsProper gk := by dsimp [gk]; infer_instance
  have : CompactSpace (pullback (π ≫ q) pk : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace gk
  have : (pullback (π ≫ q) pk).IsSeparated := ⟨by rw [← terminal.comp_from gk]; infer_instance⟩
  let L := (Scheme.Modules.pullback (j ≫ π)).obj A
  have : AlgebraicGeometry.SheafOfModules.IsInvertible
      (pullback (π ≫ q) pk).toRingedSpace.presheaf
      (structureSheafRing (pullback (π ≫ q) pk).toRingedSpace).property L :=
    Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback (j ≫ π).toLRSHom.toShHom A
  have hL : Scheme.Modules.IsAmple _ L :=
    Scheme.Modules.isAmple_pullback_of_isAffineHom (j ≫ π) A hA
  -- `c₀^*L₀ ≅ c_k^*L`
  have hcomp : S.specialFiberι ≫ φ = ck ≫ j ≫ π := by
    rw [reassoc_of% hckj, hcπ]
  let φ' : (Scheme.Modules.pullback c₀).obj L₀ ≅ (Scheme.Modules.pullback ck).obj L :=
    α ≪≫ (Scheme.Modules.pullbackComp S.specialFiberι φ).app A ≪≫
      (Scheme.Modules.pullbackCongr hcomp).app A ≪≫
      ((Scheme.Modules.pullbackComp ck (j ≫ π)).app A).symm
  -- the factorization `c_k = c₀ ≫ h`
  have : IsProper g₀ := hc₀.isProper
  have : IsProper c₀ := Stacks.AlgebraicGeometry.BirationalCurveFinite.isProper_of_comp_eq
    (p := g₀) hc₀.comp_eq
  have : IsReduced Y₀ := hc₀.isReduced
  have happ : ∀ U : Y₀.Opens, IsIso (c₀.app U) := fun U =>
    Stacks.Curves.DualizingPullback.isIso_app_of_isIso_unitToPushforwardObjUnit c₀
      hc₀.isIso_unitToPushforwardObjUnit U
  have : Surjective c₀ := c₀.surjective_of_isIso_app happ
  obtain ⟨h, hh⟩ :=
    Stacks.ContractionComparison.exists_comp_eq_of_isAmple_of_isIso_unitToPushforwardObjUnit_left
      c₀ ck hc₀.isIso_unitToPushforwardObjUnit L₀ L φ' hL
  refine ⟨h, ?_, hh⟩
  -- `h` is finite
  have hhg : h ≫ gk = g₀ := hc₀.ext (gY' := 𝟙 _) (by rw [reassoc_of% hh, hckg, hc₀.comp_eq])
  have : IsProper h := Stacks.AlgebraicGeometry.BirationalCurveFinite.isProper_of_comp_eq hhg
  have e₀ : (Scheme.Modules.pullback c₀).obj ((Scheme.Modules.pullback h).obj L) ≅
      (Scheme.Modules.pullback c₀).obj L₀ :=
    (Scheme.Modules.pullbackComp c₀ h).app L ≪≫ (Scheme.Modules.pullbackCongr hh).app L ≪≫ φ'.symm
  have : Stacks.SheafOfModules.IsInvertible Y₀.presheaf
      (structureSheafRing Y₀.toRingedSpace).property ((Scheme.Modules.pullback h).obj L) :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
      (Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback h.toLRSHom.toShHom L)
  have : Stacks.SheafOfModules.IsInvertible Y₀.presheaf
      (structureSheafRing Y₀.toRingedSpace).property L₀ :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ inferInstance
  obtain ⟨e⟩ := Stacks.PicardFibreTrivial.nonempty_iso_of_pullback_iso c₀ happ _ _ e₀
  have hdim : topologicalKrullDim Y₀ ≤ 1 := hc₀.topologicalKrullDim_eq.le
  exact Scheme.Hom.isFinite_of_pullback_iso_of_isAmple S.k g₀ hdim h L L₀ hL₀ e

end Stacks.Models.RegularProperModelSituation

end
