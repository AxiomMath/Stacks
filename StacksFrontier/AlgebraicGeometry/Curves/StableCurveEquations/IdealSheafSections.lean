module

public import StacksFrontier.AlgebraicGeometry.AffineClosedUnion.TwistedUnit
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemeBaseChange.PullbackSections
public import StacksFrontier.AlgebraicGeometry.CohomologyZeroLinear.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.StableCurveEquations.IdealSheafRegularity

/-!
# The twisted ideal sheaf of a closed subscheme of projective space, on global sections

Let `φ : X ⟶ ℙⁿ_k` be a closed immersion and `ℐ` the kernel of `𝒪 ⟶ φ_* 𝒪_X`
(`AlgebraicGeometry.closedImmersionQuotient`). This file identifies the global sections of the
twist `ℐ(d)` inside `Γ(ℙⁿ_k, 𝒪(d))`: a global section `t` of `𝒪(d)` comes from `ℐ(d)` exactly when
its pullback `φ^* t` to `X` vanishes. The twisted sequence `0 ⟶ ℐ(d) ⟶ 𝒪(d) ⟶ (φ_* 𝒪_X)(d) ⟶ 0`
is exact on global sections at the middle, and `𝒪(d) ⟶ (φ_* 𝒪_X)(d) ≅ φ_* φ^* 𝒪(d)` is the unit of
`φ^* ⊣ φ_*` (`Stacks.AffineClosedUnion.twistedUnit_eq_unit`), whose effect on global sections is
the pullback of sections.

## Main definitions

* `AlgebraicGeometry.idealTwistIncl`: the inclusion `ℐ(d) ⟶ 𝒪(d)`.

## Main results

* `AlgebraicGeometry.exists_app_top_eq_of_shortExact`: global sections are exact at the middle of
  a short exact sequence.
* `AlgebraicGeometry.exists_idealTwistIncl_app_top_eq_iff`: `t` comes from `ℐ(d)` iff
  `φ^* t = 0`.

## References

* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 08AG](https://stacks.math.columbia.edu/tag/08AG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)

universe u

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **Global sections are exact at the middle of a short exact sequence.** A global section of the
middle term killed by the second map comes from the first term: degree-zero cohomology is global
sections, naturally, and the long exact cohomology sequence is exact there. -/
theorem exists_app_top_eq_of_shortExact {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) {S : ShortComplex Y.Modules} (hS : S.ShortExact) (t : Γ(S.X₂, ⊤))
    (ht : S.g.app ⊤ t = 0) : ∃ a : Γ(S.X₁, ⊤), S.f.app ⊤ a = t := by
  obtain ⟨-, -, hex, -, -⟩ := exists_cohomologyOverField_longExactSequence k f hS
  let E := fun M : Y.Modules => cohomologyOverFieldZeroEquivSections k f M
  have h0 : cohomologyOverFieldMap k f S.g 0 ((E S.X₂).symm t) = 0 := by
    apply (E S.X₃).injective
    rw [cohomologyOverFieldZeroEquivSections_cohomologyOverFieldMap, Equiv.apply_symm_apply, ht]
    have h := cohomologyOverFieldZeroEquivSections_cohomologyOverFieldMap k f
      (0 : S.X₃ ⟶ S.X₃) 0
    rw [map_zero, Scheme.Modules.Hom.zero_app] at h
    exact h.symm
  obtain ⟨b, hb⟩ := (hex 0 ((E S.X₂).symm t)).mp h0
  refine ⟨E S.X₁ b, ?_⟩
  rw [← cohomologyOverFieldZeroEquivSections_cohomologyOverFieldMap, hb, Equiv.apply_symm_apply]

variable {k : Type u} [Field k] {n : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ projectiveSpaceOverRing n (.of k)) [IsClosedImmersion φ]

/-- **The ideal sheaf `ℐ ⟶ 𝒪` of a closed subscheme of `ℙⁿ_k`**: the kernel of
`AlgebraicGeometry.closedImmersionQuotient`, included into `𝒪^{⊕ 1} ≅ 𝒪`. -/
def idealIncl : kernel (closedImmersionQuotient φ) ⟶
    Stacks.AlgebraicGeometry.PicardBaseChange.unitModule (projectiveSpaceOverRing n (.of k)) :=
  kernel.ι _ ≫ (coproductUniqueIso _).hom

/-- **The twisted ideal sheaf `ℐ(d) ⟶ 𝒪(d)`**: the inclusion of the ideal sheaf tensored with
`𝒪(d)`, followed by the left unit constraint `𝒪 ⊗ 𝒪(d) ≅ 𝒪(d)`. -/
def idealTwistIncl (d : ℤ) :
    projectiveTwist n (kernel (closedImmersionQuotient φ)) d ⟶ twistOver n (Spec (.of k)) d :=
  (Stacks.AffineClosedUnion.twistFunctor _ (twistOver n (Spec (.of k)) d)).map (idealIncl φ) ≫
    (Stacks.AffineClosedUnion.twistUnitIso (twistOver n (Spec (.of k)) d)).hom

omit [IsClosedImmersion φ] in
/-- The map `𝒪 ⟶ φ_* 𝒪_X` is `AlgebraicGeometry.closedImmersionQuotient` read on the one summand
of `𝒪^{⊕ 1}`. -/
theorem coproductUniqueIso_inv_comp_closedImmersionQuotient :
    (coproductUniqueIso _).inv ≫ closedImmersionQuotient φ =
      Stacks.AffineClosedUnion.unitToPushforwardStructureSheaf φ :=
  Sigma.ι_comp_desc _ _

/-- The inverse of an isomorphism of modules undoes it on sections. -/
private theorem Scheme.Modules.Iso.inv_app_hom_app {Y : Scheme.{u}} {M N : Y.Modules} (e : M ≅ N)
    {U : Y.Opens} (y : Γ(M, U)) : e.inv.app U (e.hom.app U y) = y := by
  rw [← CategoryTheory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id,
    Scheme.Modules.Hom.id_app, CategoryTheory.id_apply]

/-- An isomorphism of modules undoes its inverse on sections. -/
private theorem Scheme.Modules.Iso.hom_app_inv_app {Y : Scheme.{u}} {M N : Y.Modules} (e : M ≅ N)
    {U : Y.Opens} (y : Γ(N, U)) : e.hom.app U (e.inv.app U y) = y :=
  Scheme.Modules.Iso.inv_app_hom_app e.symm y

/-- The pullback of a global section of `𝒪(d)` to `X` is the twist of `𝒪 ⟶ φ_* 𝒪_X` applied to
it, read through `(φ_* 𝒪_X)(d) ≅ φ_* φ^* 𝒪(d)`. -/
private theorem pullbackGlobalSections_eq_twistPushforwardIso_hom_app (d : ℤ)
    (t : Γ(twistOver n (Spec (.of k)) d, ⊤)) :
    pullbackGlobalSections φ (twistOver n (Spec (.of k)) d) t =
      (Stacks.AffineClosedUnion.twistPushforwardIso φ (twistOver n (Spec (.of k)) d)).hom.app ⊤
        (((Stacks.AffineClosedUnion.twistFunctor _ (twistOver n (Spec (.of k)) d)).map
          ((coproductUniqueIso _).inv ≫ closedImmersionQuotient φ)).app ⊤
          ((Stacks.AffineClosedUnion.twistUnitIso (twistOver n (Spec (.of k)) d)).inv.app ⊤
            t)) := by
  rw [pullbackGlobalSections_eq_unit, ← Stacks.AffineClosedUnion.twistedUnit_eq_unit,
    coproductUniqueIso_inv_comp_closedImmersionQuotient]
  rfl

/-- **A global section of `𝒪(d)` comes from the twisted ideal sheaf `ℐ(d)` exactly when its
pullback to `X` vanishes.** -/
theorem exists_idealTwistIncl_app_top_eq_iff (d : ℤ) (t : Γ(twistOver n (Spec (.of k)) d, ⊤)) :
    (∃ a, (idealTwistIncl φ d).app ⊤ a = t) ↔
      pullbackGlobalSections φ (twistOver n (Spec (.of k)) d) t = 0 := by
  let L := twistOver n (Spec (.of k)) d
  let T := Stacks.AffineClosedUnion.twistFunctor (projectiveSpaceOverRing n (.of k)) L
  have : T.IsEquivalence := Stacks.SheafOfModules.Invertible.tensorRightFunctor_isEquivalence
    _ (structureSheafRing (projectiveSpaceOverRing n (.of k)).toRingedSpace).property L
  let q := closedImmersionQuotient φ
  let ε := coproductUniqueIso (fun _ : Fin 1 =>
    Stacks.Ample.unitModule (projectiveSpaceOverRing n (.of k)))
  have hzero : T.map (idealIncl φ) ≫ T.map (ε.inv ≫ q) = 0 := by
    rw [← T.map_comp, idealIncl, Category.assoc, Iso.hom_inv_id_assoc, kernel.condition,
      Functor.map_zero]
  constructor
  · rintro ⟨a, rfl⟩
    rw [pullbackGlobalSections_eq_twistPushforwardIso_hom_app]
    have h2 := congrArg (fun g => Scheme.Modules.Hom.app g ⊤ a) hzero
    simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.zero_app] at h2
    rw [CategoryTheory.comp_apply] at h2
    change (Stacks.AffineClosedUnion.twistPushforwardIso φ L).hom.app ⊤
      ((T.map (ε.inv ≫ q)).app ⊤ ((Stacks.AffineClosedUnion.twistUnitIso L).inv.app ⊤
        ((Stacks.AffineClosedUnion.twistUnitIso L).hom.app ⊤ ((T.map (idealIncl φ)).app ⊤ a)))) = 0
    rw [Scheme.Modules.Iso.inv_app_hom_app (Stacks.AffineClosedUnion.twistUnitIso L), h2]
    simp only [AddCommGrpCat.hom_zero, AddMonoidHom.zero_apply]
    exact map_zero _
  · intro h
    rw [pullbackGlobalSections_eq_twistPushforwardIso_hom_app] at h
    have h1 :
        (T.map (ε.inv ≫ q)).app ⊤ ((Stacks.AffineClosedUnion.twistUnitIso L).inv.app ⊤ t) = 0 := by
      rw [← Scheme.Modules.Iso.inv_app_hom_app (Stacks.AffineClosedUnion.twistPushforwardIso φ L)
        ((T.map (ε.inv ≫ q)).app ⊤ ((Stacks.AffineClosedUnion.twistUnitIso L).inv.app ⊤ t)), h]
      exact map_zero _
    let y := (T.map ε.inv).app ⊤ ((Stacks.AffineClosedUnion.twistUnitIso L).inv.app ⊤ t)
    have hy : (T.map q).app ⊤ y = 0 := by
      rw [← h1, T.map_comp, Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply]
    have hS : (ShortComplex.mk (kernel.ι q) q (kernel.condition q)).ShortExact :=
      { exact := ShortComplex.exact_kernel q }
    obtain ⟨a, ha⟩ := exists_app_top_eq_of_shortExact
      (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k)) (hS.map_of_exact T) y hy
    change (T.map (kernel.ι q)).app ⊤ a = y at ha
    refine ⟨a, ?_⟩
    change (Stacks.AffineClosedUnion.twistUnitIso L).hom.app ⊤
      ((T.map (kernel.ι q ≫ ε.hom)).app ⊤ a) = t
    rw [T.map_comp, Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply, ha,
      ← CategoryTheory.comp_apply (Scheme.Modules.Hom.app (T.map ε.inv) ⊤),
      ← Scheme.Modules.Hom.comp_app, ← T.map_comp, Iso.inv_hom_id, T.map_id,
      Scheme.Modules.Hom.id_app, CategoryTheory.id_apply, Scheme.Modules.Iso.hom_app_inv_app]

end AlgebraicGeometry

end
