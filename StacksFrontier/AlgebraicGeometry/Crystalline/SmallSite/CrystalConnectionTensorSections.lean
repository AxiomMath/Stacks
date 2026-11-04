module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalConnectionSecondOrderComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.UniversalThickeningTensorSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAnnihilation

/-!
# The canonical maps of [Stacks, Tag 07J6] on `Cris(X/S)`, on local pure tensors

Fix a global crystalline situation of [Stacks, Tag 07MF], a sheaf of `𝒪_{X/S}`-modules `F` on
`Cris(X/S)` and an object `(U, T, δ)` with first- and second-order universal thickenings
`T'` and `T''` of [Stacks, Tag 07J2] and [Stacks, Tag 07J3].  This module computes the two
canonical morphisms

`F_T ⊗_{𝒪_T} Ω_{T/S,δ} ⟶ p₀_* F_{T'}` and `F_T ⊗_{𝒪_T} Ω²_{T/S,δ} ⟶ q₀_* F_{T''}`

on local pure tensors: `x ⊗ ω ↦ (0, ω) · p₀^* x` and `x ⊗ η ↦ (0, 0, 0, η) · q₀^* x`, the
formulas by which the proof of [Stacks, Tag 07J6] reads `F_T ⊗ Ω` inside `F_{T'}` and
`F_T ⊗ Ω²` inside `F_{T''}`.  It also proves the tool every later computation runs on: two
compatible families of additive maps out of the sections of a tensor product sheaf that agree on
local pure tensors agree (`Crystalline.tensor_sections_ext`), a section of the tensor product
sheaf being locally a finite sum of local pure tensors.

## Main results

* `Crystalline.tensor_sections_ext` — local pure tensors determine additive maps out of a tensor
  product sheaf.
* `...SmallSite.firstOrderTensorInclusion_tmul` and `...SmallSite.secondOrderTensorComparison_tmul`
  — the two canonical morphisms on local pure tensors.

## References

* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07J3](https://stacks.math.columbia.edu/tag/07J3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite
open TopologicalSpace

universe u

noncomputable section

namespace Crystalline

attribute [local instance] monoidalCategorySchemeModules

/-! ### Local pure tensors determine additive maps out of a tensor product sheaf -/

section Ext

variable {X : Scheme.{u}} {M N G : X.Modules}

/-- **Two compatible families of additive maps out of the sections of a tensor product sheaf
which agree on the local pure tensors agree.**  The families are indexed by the opens contained
in a fixed open `W` and commute with restriction; a section of `M ⊗ N` over `W` is locally the
image of a finite sum of pure tensors, and the target is a sheaf. -/
theorem tensor_sections_ext {W : X.Opens}
    (φ ψ : ∀ V : X.Opens, V ≤ W → (M ⊗ N).val.obj (op V) →+ G.val.obj (op V))
    (hφ : ∀ (V V' : X.Opens) (hV : V ≤ W) (hV' : V' ≤ W) (h : V' ≤ V)
      (z : (M ⊗ N).val.obj (op V)),
      G.val.map (homOfLE h).op (φ V hV z) = φ V' hV' ((M ⊗ N).val.map (homOfLE h).op z))
    (hψ : ∀ (V V' : X.Opens) (hV : V ≤ W) (hV' : V' ≤ W) (h : V' ≤ V)
      (z : (M ⊗ N).val.obj (op V)),
      G.val.map (homOfLE h).op (ψ V hV z) = ψ V' hV' ((M ⊗ N).val.map (homOfLE h).op z))
    (htmul : ∀ (V : X.Opens) (hV : V ≤ W) (a : M.val.obj (op V)) (b : N.val.obj (op V)),
      φ V hV (Stacks.PullbackTensorCoherence.tmul X.toRingedSpace M N (op V) a b) =
        ψ V hV (Stacks.PullbackTensorCoherence.tmul X.toRingedSpace M N (op V) a b))
    (z : (M ⊗ N).val.obj (op W)) : φ W le_rfl z = ψ W le_rfl z := by
  set u := (PresheafOfModules.sheafificationAdjunction
        (R := Stacks.RingedSpace.structureRingSheaf X.toRingedSpace)
        (𝟙 (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace).obj)).unit.app
        (PresheafOfModules.tensorObj (O := X.toRingedSpace.presheaf) M.val N.val)
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map u) :=
    Stacks.SheafOfModules.isLocallySurjective_tensorSheafificationUnit
      (Opens.grothendieckTopology X) (Osharp := X.sheaf) M N
  refine sub_eq_zero.1 (Stacks.SheafOfModules.eq_zero_of_locally_eq_zero
    (J := Opens.grothendieckTopology X) _ (Presheaf.imageSieve_mem _
      ((PresheafOfModules.toPresheaf _).map u) z) ?_)
  rintro V g ⟨p, hp⟩
  have hVW : V ≤ W := leOfHom g
  obtain rfl : g = homOfLE hVW := Subsingleton.elim _ _
  have hp' : u.app (op V) p = (M ⊗ N).val.map (homOfLE hVW).op z := hp
  have hmain : ∀ q, φ V hVW (u.app (op V) q) = ψ V hVW (u.app (op V) q) := by
    have he : (φ V hVW).comp (u.app (op V)).hom.toAddMonoidHom =
        (ψ V hVW).comp (u.app (op V)).hom.toAddMonoidHom := by
      refine AddMonoidHom.ext fun q ↦ ?_
      induction q using TensorProduct.induction_on with
      | zero => exact (map_zero _).trans (map_zero _).symm
      | tmul a b => exact htmul V hVW a b
      | add p q hp hq =>
        exact (map_add _ p q).trans ((congrArg₂ (· + ·) hp hq).trans (map_add _ p q).symm)
    exact DFunLike.congr_fun he
  rw [map_sub, hφ W V le_rfl hVW hVW, hψ W V le_rfl hVW hVW, ← hp']
  exact sub_eq_zero.2 (hmain p)

/-- **A local pure tensor restricts to the pure tensor of the restrictions.** -/
theorem tmul_restrict {V V' : X.Opens} (h : V' ≤ V) (a : M.val.obj (op V))
    (b : N.val.obj (op V)) :
    (M ⊗ N).val.map (homOfLE h).op
        (Stacks.PullbackTensorCoherence.tmul X.toRingedSpace M N (op V) a b) =
      Stacks.PullbackTensorCoherence.tmul X.toRingedSpace M N (op V')
        (M.val.map (homOfLE h).op a) (N.val.map (homOfLE h).op b) :=
  (PresheafOfModules.naturality_apply
    ((PresheafOfModules.sheafificationAdjunction
      (R := Stacks.RingedSpace.structureRingSheaf X.toRingedSpace)
      (𝟙 (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace).obj)).unit.app
      (PresheafOfModules.tensorObj (O := X.toRingedSpace.presheaf) M.val N.val))
    (homOfLE h).op (a ⊗ₜ b)).symm

/-- **A local pure tensor is additive in its first factor.** -/
theorem tmul_add_left (V : X.Opens) (a a' : M.val.obj (op V)) (b : N.val.obj (op V)) :
    Stacks.PullbackTensorCoherence.tmul X.toRingedSpace M N (op V) (a + a') b =
      Stacks.PullbackTensorCoherence.tmul X.toRingedSpace M N (op V) a b +
        Stacks.PullbackTensorCoherence.tmul X.toRingedSpace M N (op V) a' b := by
  unfold Stacks.PullbackTensorCoherence.tmul
  rw [TensorProduct.add_tmul]
  exact ((PresheafOfModules.tensorSheafUnit M N).app (op V)).hom.map_add _ _

end Ext

namespace GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}} (M : SheafOfModules.{u} (structureSheaf S))
  (A : CrystallineThickening S)

/-! ### Sections of the universal thickenings over an open of `T` -/

/-- The sections of `F_{T'}` over an open of `T`, as a module over the sections of `𝒪_{T'}`. -/
abbrev FirstOrderSec (W : A.obj.thickening.target.scheme.Opens) : Type u :=
  (crysAmbientSchemeModules M (firstOrderThickeningCrysObject S A)).val.obj
    (op ((firstOrderThickeningCrysP₀ S A).hom.targetHom.hom ⁻¹ᵁ W))

/-- The sections of `𝒪_{T'}` over an open of `T`. -/
abbrev FirstOrderRing (W : A.obj.thickening.target.scheme.Opens) : Type u :=
  ↑((firstOrderThickeningCrysObject S A).obj.thickening.target.scheme.ringCatSheaf.obj.obj
    (op ((firstOrderThickeningCrysP₀ S A).hom.targetHom.hom ⁻¹ᵁ W)))

/-- The sections of `F_{T''}` over an open of `T`, as a module over the sections of `𝒪_{T''}`. -/
abbrev SecondOrderSec (W : A.obj.thickening.target.scheme.Opens) : Type u :=
  (crysAmbientSchemeModules M (secondOrderThickeningCrysObject S A)).val.obj
    (op ((secondOrderThickeningCrysQ₀ S A).hom.targetHom.hom ⁻¹ᵁ W))

/-- The sections of `𝒪_{T''}` over an open of `T`. -/
abbrev SecondOrderRing (W : A.obj.thickening.target.scheme.Opens) : Type u :=
  ↑((secondOrderThickeningCrysObject S A).obj.thickening.target.scheme.ringCatSheaf.obj.obj
    (op ((secondOrderThickeningCrysQ₀ S A).hom.targetHom.hom ⁻¹ᵁ W)))

/-- **`i^*` kills `(0, ω) · y`**: the diagonal `i : T ⟶ T'` acts on `𝒪_{T'}` by the projection
`(g, ω) ↦ g`. -/
theorem firstOrderAmbientProjMap₀_idealScalar_smul (W : (Opens ↑A.obj.thickening.target.scheme)ᵒᵖ)
    (ω : (dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.obj W)
    (y : (crysAmbientSchemeModules M (firstOrderThickeningCrysObject S A)).val.obj
            (op ((firstOrderThickeningCrysP₀ S A).hom.targetHom.hom ⁻¹ᵁ W.unop))) :
    (firstOrderAmbientProjMap₀ M A).val.app W
      ((show FirstOrderRing A W.unop from
          firstOrderIdealScalar A.obj.thickening.target S.S.scheme A.obj.toBase.hom W ω) • y) =
      0 := by
  have h := ((firstOrderAmbientProjMap M A).val.app
    (op ((firstOrderThickeningCrysP₀ S A).hom.targetHom.hom ⁻¹ᵁ W.unop))).hom.map_smul
    (show FirstOrderRing A W.unop from
          firstOrderIdealScalar A.obj.thickening.target S.S.scheme A.obj.toBase.hom W ω) y
  refine h.trans ?_
  show (0 : ↑(A.obj.thickening.target.scheme.ringCatSheaf.obj.obj
      (op ((firstOrderThickeningCrysι S A).hom.targetHom.hom ⁻¹ᵁ
        ((firstOrderThickeningCrysP₀ S A).hom.targetHom.hom ⁻¹ᵁ W.unop))))) •
    (show (crysAmbientSchemeModules M A).val.obj
      (op ((firstOrderThickeningCrysι S A).hom.targetHom.hom ⁻¹ᵁ
        ((firstOrderThickeningCrysP₀ S A).hom.targetHom.hom ⁻¹ᵁ W.unop))) from
      (firstOrderAmbientProjMap M A).val.app
        (op ((firstOrderThickeningCrysP₀ S A).hom.targetHom.hom ⁻¹ᵁ W.unop)) y) = 0
  exact zero_smul _ _

/-- **The canonical morphism `F_T ⊗_{𝒪_T} Ω_{T/S,δ} ⟶ p₀_* F_{T'}` on a local pure tensor**:
`x ⊗ ω ↦ (0, ω) · p₀^* x`, the formula by which [Stacks, Tag 07J6] reads `F_T ⊗ Ω` inside
`F_{T'}`. -/
theorem firstOrderTensorInclusion_tmul (W : (Opens ↑A.obj.thickening.target.scheme)ᵒᵖ)
    (x : (crysAmbientSchemeModules M A).val.obj W)
    (ω : (dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.obj W) :
    (firstOrderTensorInclusion M A).val.app W
        (Stacks.PullbackTensorCoherence.tmul A.obj.thickening.target.scheme.toRingedSpace
          (crysAmbientSchemeModules M A)
          (dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom) W x ω) =
      ((show FirstOrderRing A W.unop from
          firstOrderIdealScalar A.obj.thickening.target S.S.scheme A.obj.toBase.hom W ω) •
        (show FirstOrderSec M A W.unop from
          (firstOrderAmbientInclMap M A).val.app W x)) := by
  set z := Stacks.PullbackTensorCoherence.tmul A.obj.thickening.target.scheme.toRingedSpace
    (crysAmbientSchemeModules M A)
    (dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom) W x ω
  have hPF := firstOrderThickeningTensorInr_projectionFormulaMap_tmul A.obj.thickening.target
    S.S.scheme A.obj.toBase.hom (crysAmbientSchemeModules M A) W x ω
  have hunit := congrArg (fun φ ↦ (SheafOfModules.Hom.val φ).app W x)
    (unit_comp_map_ambientSchemeCrystalComparison M A)
  have e1 : (firstOrderTensorInclusion M A).val.app W z =
      (firstOrderAmbientRetraction M A ≫ kernel.ι (firstOrderAmbientProjMap₀ M A)).val.app W
        ((firstOrderTensorToAmbient M A).val.app W
          ((firstOrderThickeningTensorInr A.obj.thickening.target S.S.scheme A.obj.toBase.hom
            (crysAmbientSchemeModules M A)).val.app W z)) := rfl
  have e2 : (firstOrderTensorToAmbient M A).val.app W
          ((firstOrderThickeningTensorInr A.obj.thickening.target S.S.scheme A.obj.toBase.hom
            (crysAmbientSchemeModules M A)).val.app W z) =
      (ambientSchemeCrystalComparison M A).val.app _
        ((firstOrderThickeningProjectionFormulaMap A.obj.thickening.target S.S.scheme
          A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.app W
          ((firstOrderThickeningTensorInr A.obj.thickening.target S.S.scheme A.obj.toBase.hom
            (crysAmbientSchemeModules M A)).val.app W z)) := rfl
  have hy : (firstOrderTensorToAmbient M A).val.app W
          ((firstOrderThickeningTensorInr A.obj.thickening.target S.S.scheme A.obj.toBase.hom
            (crysAmbientSchemeModules M A)).val.app W z) =
      ((show FirstOrderRing A W.unop from
          firstOrderIdealScalar A.obj.thickening.target S.S.scheme A.obj.toBase.hom W ω) •
        (show FirstOrderSec M A W.unop from
          (firstOrderAmbientInclMap M A).val.app W x)) := by
    rw [e2, hPF]
    refine ((ambientSchemeCrystalComparison M A).val.app _).hom.map_smul _ _ |>.trans ?_
    exact congrArg (fun y : FirstOrderSec M A W.unop ↦ (show FirstOrderRing A W.unop from
          firstOrderIdealScalar A.obj.thickening.target S.S.scheme A.obj.toBase.hom W ω) • y) hunit
  have hsub : ∀ y, (firstOrderAmbientRetraction M A ≫
        kernel.ι (firstOrderAmbientProjMap₀ M A)).val.app W y =
      y - (firstOrderAmbientInclMap M A).val.app W ((firstOrderAmbientProjMap₀ M A).val.app W y) :=
    fun y ↦ (congrArg (fun φ ↦ (SheafOfModules.Hom.val φ).app W y)
      (firstOrderAmbientRetraction_ι M A)).trans rfl
  rw [e1, hsub, hy, firstOrderAmbientProjMap₀_idealScalar_smul, map_zero]
  exact sub_zero _

/-- **The degree-two canonical map of [Stacks, Tag 07J6] on a local pure tensor**: it carries
`x ⊗ η` to `(0, 0, 0, η) · q₀^* x`. -/
theorem secondOrderTensorComparison_tmul (W : (Opens ↑A.obj.thickening.target.scheme)ᵒᵖ)
    (x : (crysAmbientSchemeModules M A).val.obj W)
    (η : (dpSecondExteriorPower A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.obj W) :
    (secondOrderTensorComparison M A).val.app W
        (Stacks.PullbackTensorCoherence.tmul A.obj.thickening.target.scheme.toRingedSpace
          (crysAmbientSchemeModules M A)
          (dpSecondExteriorPower A.obj.thickening.target S.S.scheme A.obj.toBase.hom) W x η) =
      ((show SecondOrderRing A W.unop from
          secondOrderIdealScalar A.obj.thickening.target S.S.scheme A.obj.toBase.hom W η) •
        (show SecondOrderSec M A W.unop from
          (secondOrderAmbientInclMap M A).val.app W x)) := by
  have hPF := secondOrderThickeningTensorTopInr_projectionFormulaMap_tmul A.obj.thickening.target
    S.S.scheme A.obj.toBase.hom (crysAmbientSchemeModules M A) W x η
  have hunit := congrArg (fun φ ↦ (SheafOfModules.Hom.val φ).app W x)
    (unit_comp_map_ambientSchemeCrystalComparisonQ₀ M A)
  have e2 : (secondOrderTensorComparison M A).val.app W
        (Stacks.PullbackTensorCoherence.tmul A.obj.thickening.target.scheme.toRingedSpace
          (crysAmbientSchemeModules M A)
          (dpSecondExteriorPower A.obj.thickening.target S.S.scheme A.obj.toBase.hom) W x η) =
      (ambientSchemeCrystalComparisonQ₀ M A).val.app _
        ((secondOrderThickeningProjectionFormulaMap A.obj.thickening.target S.S.scheme
          A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.app W
          ((secondOrderThickeningTensorTopInr A.obj.thickening.target S.S.scheme
            A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.app W
            (Stacks.PullbackTensorCoherence.tmul A.obj.thickening.target.scheme.toRingedSpace
              (crysAmbientSchemeModules M A)
              (dpSecondExteriorPower A.obj.thickening.target S.S.scheme A.obj.toBase.hom)
              W x η))) := rfl
  rw [e2, hPF]
  refine ((ambientSchemeCrystalComparisonQ₀ M A).val.app _).hom.map_smul _ _ |>.trans ?_
  exact congrArg (fun y : SecondOrderSec M A W.unop ↦
      (show SecondOrderRing A W.unop from
          secondOrderIdealScalar A.obj.thickening.target S.S.scheme A.obj.toBase.hom W η) • y) hunit

end GlobalCrystallineSituation.SmallSite

end Crystalline

end

end
