module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModuleData0BVG
public import StacksFrontier.RingTheory.TateMap.DualizingBaseChange

/-!
# The chart identifications of `ω_{Y/X}` along basic-open restriction squares

Let `f : Y ⟶ X` be a flat locally quasi-finite morphism of locally Noetherian schemes and `ω`
chart data for its relative dualizing module (Tag 0BVG). For an affine chart `V ⊆ f⁻¹(U)` and
principal opens `D(b) ⊆ V`, `D(a) ⊆ U` with `D(b) ⊆ f⁻¹(D(a))`, the identification of the
sections of `ω` over `D(b)` with `ω_{Γ(D(b))/Γ(D(a))}` is the base change, along any chart base
change datum of that square, of the identification over `V`.

## Main results

* `Stacks.TateMap.localEquiv_restrict_eq_omegaBaseChange`: the statement above.

## Implementation notes

The chart data only records the two elementary moves, shrinking the source chart to a principal
open (Tag 0BT2, part (2)) and shrinking the base chart to a principal open (Tag 0BT2, part (1)).
The square is the composite of the two, and both sides are compared on the generators
`φ ⊗ c` of `ω_{Γ(V)/Γ(U)}`, where every map involved is given by an explicit formula.

## References

* [Stacks Project, Tag 0BVG](https://stacks.math.columbia.edu/tag/0BVG)
* [Stacks Project, Tag 0BT2](https://stacks.math.columbia.edu/tag/0BT2)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

open Stacks.Discriminant Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace Stacks.TateMap

attribute [local instance] algebraDualModule

variable {X Y : Scheme.{u}} {f : Y ⟶ X} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  [LocallyQuasiFinite f] [Flat f]

/-- **The chart identifications of `ω_{Y/X}` are compatible with base change on a basic-open
restriction square.** For `D(b) ⊆ V` and `D(a) ⊆ U` with `D(b) ⊆ f⁻¹(D(a))`, every chart base
change datum `D` of the square `Γ(U) → Γ(V)`, `Γ(D(a)) → Γ(D(b))`, and all finite-open
factorizations `F`, `G` of the two charts, the identification over `D(b)` of the restriction of
a section `t` over `V` is the base change of the identification of `t` over `V`. -/
theorem localEquiv_restrict_eq_omegaBaseChange (Dω : RelativeDualizingModuleData f)
    (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) (a : Γ(X, U.1))
    (b : Γ(Y, V.1)) (hba : Y.basicOpen b ≤ f ⁻¹ᵁ X.basicOpen a) :
    let Ua : X.affineOpens := ⟨X.basicOpen a, U.2.basicOpen a⟩
    let Vb : Y.affineOpens := ⟨Y.basicOpen b, V.2.basicOpen b⟩
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    letI : Algebra Γ(X, Ua.1) Γ(Y, Vb.1) := (f.appLE Ua Vb hba).hom.toAlgebra
    letI : Algebra Γ(X, U.1) Γ(X, Ua.1) :=
      (X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom.toAlgebra
    letI : Algebra Γ(Y, V.1) Γ(Y, Vb.1) :=
      (Y.presheaf.map (homOfLE (Y.basicOpen_le b)).op).hom.toAlgebra
    letI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    letI : IsNoetherianRing Γ(X, Ua.1) := IsLocallyNoetherian.component_noetherian Ua
    letI : Module.Flat Γ(X, U.1) Γ(Y, V.1) :=
      RingHom.flat_algebraMap_iff.mp (f.flat_appLE U.2 V.2 hVU)
    ∀ (D : ChartBaseChange Γ(X, U.1) Γ(Y, V.1) Γ(X, Ua.1) Γ(Y, Vb.1))
      (F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1))
      (G : FiniteOpenFactorization.{u, u, u} Γ(X, Ua.1) Γ(Y, Vb.1)) (t : Γ(Dω.sheaf, V.1)),
      Dω.localEquiv Ua Vb hba G (restrictₗ Dω.sheaf (Y.basicOpen_le b) t) =
        omegaBaseChange D F G (1 ⊗ₜ Dω.localEquiv U V hVU F t) := by
  intro Ua Vb D F G t
  have hVbU : Vb.1 ≤ f ⁻¹ᵁ U.1 := (Y.basicOpen_le b).trans hVU
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  let : Algebra Γ(X, Ua.1) Γ(Y, Vb.1) := (f.appLE Ua Vb hba).hom.toAlgebra
  let : Algebra Γ(X, U.1) Γ(X, Ua.1) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom.toAlgebra
  let : Algebra Γ(Y, V.1) Γ(Y, Vb.1) :=
    (Y.presheaf.map (homOfLE (Y.basicOpen_le b)).op).hom.toAlgebra
  let : Algebra Γ(X, U.1) Γ(Y, Vb.1) := (f.appLE U Vb hVbU).hom.toAlgebra
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  let : IsNoetherianRing Γ(X, Ua.1) := IsLocallyNoetherian.component_noetherian Ua
  let : IsNoetherianRing Γ(Y, V.1) := IsLocallyNoetherian.component_noetherian V
  let : IsNoetherianRing Γ(Y, Vb.1) := IsLocallyNoetherian.component_noetherian Vb
  let : Module.Flat Γ(X, U.1) Γ(Y, V.1) :=
    RingHom.flat_algebraMap_iff.mp (f.flat_appLE U.2 V.2 hVU)
  let : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
    RingHom.quasiFinite_algebraMap.mp (LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 hVU)
  let : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, Vb.1) :=
    RingHom.quasiFinite_algebraMap.mp (LocallyQuasiFinite.quasiFinite_appLE U.2 Vb.2 hVbU)
  let : IsLocalization.Away b Γ(Y, Vb.1) := V.2.isLocalization_basicOpen b
  let : IsLocalization.Away a Γ(X, Ua.1) := U.2.isLocalization_basicOpen a
  let : IsScalarTower Γ(X, U.1) Γ(Y, V.1) Γ(Y, Vb.1) :=
    IsScalarTower.of_algebraMap_eq' (by
      show (f.appLE U Vb hVbU).hom =
        ((Y.presheaf.map (homOfLE (Y.basicOpen_le b)).op).hom).comp (f.appLE U V hVU).hom
      rw [← CommRingCat.hom_comp, ← f.appLE_map hVU (homOfLE (Y.basicOpen_le b)).op])
  let : IsScalarTower Γ(X, U.1) Γ(X, Ua.1) Γ(Y, Vb.1) :=
    IsScalarTower.of_algebraMap_eq' (by
      show (f.appLE U Vb hVbU).hom =
        ((f.appLE Ua Vb hba).hom).comp
          (X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom
      rw [← CommRingCat.hom_comp, f.map_appLE hba (homOfLE (X.basicOpen_le a)).op])
  let F₁ : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, Vb.1) := locFact b F
  let : Module Γ(Y, V.1) (dualizingModule F₁) :=
    Module.compHom (dualizingModule F₁) (algebraMap Γ(Y, V.1) Γ(Y, Vb.1))
  let : IsScalarTower Γ(Y, V.1) Γ(Y, Vb.1) (dualizingModule F₁) :=
    IsScalarTower.of_compHom Γ(Y, V.1) Γ(Y, Vb.1) _
  obtain ⟨r, hr, hrestrict, hlocalId⟩ := Dω.localEquiv_basicOpen U V hVU b F F₁
  rw [Dω.localEquiv_baseBasicOpen U Vb hVbU a hba F₁ G, hrestrict]
  generalize Dω.localEquiv U V hVU F t = x
  induction x using dualizingModule.induction_on F with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, TensorProduct.tmul_add, map_add, hx, hy]
  | tmul φ c => ?_
  have h₁ : r (dualizingModule.tmul F φ c) =
      dualizingModule.tmul F₁ φ (algebraMap Γ(Y, V.1) Γ(Y, Vb.1) c) := by
    refine (hlocalId (r (dualizingModule.tmul F φ c))).symm.trans
      ((localizedModule_dualizingModule_equiv_apply b F F₁ r hr _).trans ?_)
    rw [dualizingTensorLocalizationEquiv_tmul, dualizingModuleEquiv_refl]
    rfl
  let H := omegaFactorization D F
  have h₂ := dualizingModule_equiv_of_isLocalization_away_natural a F₁ F₁ H G
    (dualizingModule.tmul F₁ φ (algebraMap Γ(Y, V.1) Γ(Y, Vb.1) c))
  rw [dualizingModuleEquiv_refl, LinearEquiv.refl_apply] at h₂
  rw [h₁, omegaBaseChange_one_tmul_tmul, ← h₂]
  congr 1
  let : Algebra Γ(X, U.1) H.middle :=
    (inferInstance : Algebra Γ(X, U.1) (Γ(X, Ua.1) ⊗[Γ(X, U.1)] F.middle))
  have : IsScalarTower Γ(X, U.1) Γ(X, Ua.1) H.middle :=
    (inferInstance : IsScalarTower Γ(X, U.1) Γ(X, Ua.1) (Γ(X, Ua.1) ⊗[Γ(X, U.1)] F.middle))
  let ι : F₁.middle →ₐ[Γ(X, U.1)] H.middle :=
    (Algebra.TensorProduct.includeRight : F.middle →ₐ[Γ(X, U.1)]
      Γ(X, Ua.1) ⊗[Γ(X, U.1)] F.middle)
  refine dualizingModule_equiv_of_isLocalization_away_tmul a F₁ H ι ?_
    (fun (c : F.middle) ↦ ?_) φ (omegaDual D F φ) (fun (c : F.middle) ↦ ?_) _
  · let := ι.toRingHom.toAlgebra
    have hloc := IsLocalization.tensorRight (R := Γ(X, U.1)) (S := F.middle) Γ(X, Ua.1)
      (Submonoid.powers a)
    rwa [Algebra.algebraMapSubmonoid, Submonoid.map_powers] at hloc
  · show algebraMap H.middle Γ(Y, Vb.1) (omegaTmul D F 1 c) = _
    rw [algebraMap_omegaFactorization, map_one, one_mul]
    rfl
  · show omegaDual D F φ (omegaTmul D F 1 c) = _
    rw [omegaDual_tmul, Algebra.algebraMap_eq_smul_one]
    rfl

end Stacks.TateMap
