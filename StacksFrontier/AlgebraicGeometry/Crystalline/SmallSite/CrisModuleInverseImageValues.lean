module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LowerShriekCrystalBaseChange

/-!
# The values of `f_cris^*` on a crystal in quasi-coherent modules

Let `f : X/S ⟶ X'/S'` be a morphism of crystalline situations (`fS : S ⟶ S'` on the divided
power bases, `fX : X ⟶ X'`), and let `ℱ` be a crystal in quasi-coherent modules on the small
crystalline site `Cris(X'/S')`.  Write `ℱ' = f_cris^* ℱ` for its module pullback,
`...SmallSite.crisModuleInverseImage fS fX hf` applied to the universe lift of `ℱ`.  For an object
`A'` of `Cris(X/S)` and a morphism

`τ : f_CRIS(A') ⟶ A`

of `CRIS(X'/S')` to an object `A` of `Cris(X'/S')` (`f_CRIS` being change of divided power base),
the **restriction along `τ`**, `crisInverseImageRestrict`, is a map `ℱ(A) ⟶ ℱ'(A')`, semilinear
over `τ^♯ : Γ(A, 𝒪) ⟶ Γ(A', 𝒪)`.  This file proves:

* `bijective_crisInverseImageBaseChange` — **when the ambient schemes of `A` and `A'` are affine,
  the base change `Γ(A', 𝒪) ⊗_{Γ(A, 𝒪)} ℱ(A) ⟶ ℱ'(A')`, `t ⊗ s ↦ t · τ^* s`, is bijective.**
  This is the identification `ℱ'_{T'} = h^* ℱ_T` that [Stacks, Tag 07Q9] uses without comment
  when it writes `ℱ' = f_cris^* ℱ`.
* `crisInverseImageRestrict_naturality` — the restrictions are natural in `(A, A', τ)`.

The input is `...SmallSite.bijective_lowerShriekBaseChange` at the object `f_CRIS(A')` of
`CRIS(X'/S')`, whose ambient scheme is that of `A'`: the sections of `ℱ'` over `A'` are by
definition the sections of `i_! ℱ` over `f_CRIS(A')`
(`...SmallSite.crisModuleInverseImage_obj_val_obj`).

## References

* [Stacks Project, Lemma 60.26.3, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Tag 07IK](https://stacks.math.columbia.edu/tag/07IK)
* [Stacks Project, Tag 07IJ](https://stacks.math.columbia.edu/tag/07IJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open scoped TensorProduct

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S S' : GlobalCrystallineSituation.{u}} (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
  (hf : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap fS = fX ≫ S'.toClosedFiber)
  (F : SheafOfModules.{u} (structureSheaf S'))

/-- **The restriction of `ℱ' = f_cris^* ℱ` along `τ : f_CRIS(A') ⟶ A`**: a section of `ℱ` over
`A` is carried by the unit of `i_! ⊣ i^{-1}` to `i_! ℱ` over `A`, and restricted along `τ` to the
sections of `i_! ℱ` over `f_CRIS(A')`, which are the sections of `ℱ'` over `A'`. -/
def crisInverseImageRestrict {A : CrystallineThickening S'} {A' : CrystallineThickening S}
    (τ : (changeBase S S' fS fX hf).obj ((CrystallineThickening.ι S).obj A') ⟶
      (CrystallineThickening.ι S').obj A) (s : F.val.obj (op A)) :
    ((crisModuleInverseImage fS fX hf).obj ((moduleULift S').obj F)).val.obj (op A') :=
  lowerShriekRestrict ((moduleULift S').obj F) τ (upSection F s)

/-- **The restriction along `τ` is semilinear** over `τ^♯ : Γ(A, 𝒪) ⟶ Γ(A', 𝒪)`. -/
lemma crisInverseImageRestrict_smul {A : CrystallineThickening S'}
    {A' : CrystallineThickening S}
    (τ : (changeBase S S' fS fX hf).obj ((CrystallineThickening.ι S).obj A') ⟶
      (CrystallineThickening.ι S').obj A)
    (c : (structureSheaf S').obj.obj (op A)) (s : F.val.obj (op A)) :
    crisInverseImageRestrict fS fX hf F τ (c • s) =
      (show (structureSheaf S).obj.obj (op A') from crysSheafRingMap τ c) •
        crisInverseImageRestrict fS fX hf F τ s :=
  lowerShriekRestrict_smul ((moduleULift S').obj F) τ c (upSection F s)

/-- **The restrictions along the morphisms `τ` are natural in `(A, A', τ)`**: for `g' : A'₁ ⟶ A'₂`
in `Cris(X/S)` and `g : A₁ ⟶ A₂` in `Cris(X'/S')` with `f_CRIS(g') ≫ τ₂ = τ₁ ≫ g`, restricting
along `τ₂` and then along `g'` is restricting along `τ₁` after `g^*`. -/
theorem crisInverseImageRestrict_naturality {A₁ A₂ : CrystallineThickening S'}
    {A'₁ A'₂ : CrystallineThickening S} (g : A₁ ⟶ A₂) (g' : A'₁ ⟶ A'₂)
    (τ₁ : (changeBase S S' fS fX hf).obj ((CrystallineThickening.ι S).obj A'₁) ⟶
      (CrystallineThickening.ι S').obj A₁)
    (τ₂ : (changeBase S S' fS fX hf).obj ((CrystallineThickening.ι S).obj A'₂) ⟶
      (CrystallineThickening.ι S').obj A₂)
    (w : (changeBase S S' fS fX hf).map ((CrystallineThickening.ι S).map g') ≫ τ₂ =
      τ₁ ≫ (CrystallineThickening.ι S').map g)
    (s : F.val.obj (op A₂)) :
    ((crisModuleInverseImage fS fX hf).obj ((moduleULift S').obj F)).val.restrictₛₗ g'.op
        (crisInverseImageRestrict fS fX hf F τ₂ s) =
      crisInverseImageRestrict fS fX hf F τ₁ (F.val.restrictₛₗ g.op s) := by
  change ((moduleLowerShriek S').obj ((moduleULift S').obj F)).val.restrictₛₗ
      ((changeBase S S' fS fX hf).map ((CrystallineThickening.ι S).map g')).op
      (lowerShriekRestrict ((moduleULift S').obj F) τ₂ (upSection F s)) = _
  rw [← lowerShriekRestrict_comp, w, lowerShriekRestrict_comp_ι]
  rfl

/-- **The base change of the sections of `ℱ'` along `τ`**,

`Γ(A', 𝒪) ⊗_{Γ(A, 𝒪)} ℱ(A) ⟶ ℱ'(A')`,  `t ⊗ s ↦ t · τ^* s`,

the tensor product being taken along `τ^♯`, as the carrier of `ModuleCat.extendScalars`. -/
def crisInverseImageBaseChange {A : CrystallineThickening S'} {A' : CrystallineThickening S}
    (τ : (changeBase S S' fS fX hf).obj ((CrystallineThickening.ι S).obj A') ⟶
      (CrystallineThickening.ι S').obj A) :
    (ModuleCat.extendScalars (tauRing τ).hom).obj (sectionsOver F A) →+
      ((crisModuleInverseImage fS fX hf).obj ((moduleULift S').obj F)).val.obj (op A') :=
  lowerShriekBaseChange F τ

/-- `crisInverseImageBaseChange` on a pure tensor: `t ⊗ s ↦ t · τ^* s`. -/
lemma crisInverseImageBaseChange_tmul {A : CrystallineThickening S'}
    {A' : CrystallineThickening S}
    (τ : (changeBase S S' fS fX hf).obj ((CrystallineThickening.ι S).obj A') ⟶
      (CrystallineThickening.ι S').obj A)
    (t : Γ(A'.obj.thickening.target.scheme, ⊤)) (s : sectionsOver F A) :
    crisInverseImageBaseChange fS fX hf F τ (Stacks.PullbackModel.tmul (tauRing τ).hom t s) =
      (show (structureSheaf S).obj.obj (op A') from t) •
        crisInverseImageRestrict fS fX hf F τ s := rfl

/-- **Stacks Project, Tag 07Q9, the identification `ℱ'_{T'} = h^* ℱ_T` on sections.**  For a
locally quasi-coherent crystal `ℱ` on `Cris(X'/S')`, an object `A'` of `Cris(X/S)` and a morphism
`τ : f_CRIS(A') ⟶ A` to an object `A` of `Cris(X'/S')`, both with affine ambient schemes, the base
change

`Γ(A', 𝒪) ⊗_{Γ(A, 𝒪)} ℱ(A) ⟶ (f_cris^* ℱ)(A')`,  `t ⊗ s ↦ t · τ^* s`,

is bijective. -/
theorem bijective_crisInverseImageBaseChange {A : CrystallineThickening S'}
    {A' : CrystallineThickening S} [IsAffine A.obj.thickening.target.scheme]
    [IsAffine A'.obj.thickening.target.scheme]
    (τ : (changeBase S S' fS fX hf).obj ((CrystallineThickening.ι S).obj A') ⟶
      (CrystallineThickening.ι S').obj A)
    (hF : IsLocallyQuasiCoherent F) (hcrys : IsSheafCrystal F) :
    Function.Bijective (crisInverseImageBaseChange fS fX hf F τ) :=
  have : IsAffine ((changeBase S S' fS fX hf).obj
      ((CrystallineThickening.ι S).obj A')).thickening.target.scheme :=
    inferInstanceAs (IsAffine A'.obj.thickening.target.scheme)
  bijective_lowerShriekBaseChange F τ hF hcrys

/-- `bijective_crisInverseImageBaseChange` for a quasi-coherent sheaf on `Cris(X'/S')`, which is
a crystal in quasi-coherent modules by [Stacks, Tag 07IT]. -/
theorem bijective_crisInverseImageBaseChange_of_isQuasicoherentOnSite
    {A : CrystallineThickening S'} {A' : CrystallineThickening S}
    [IsAffine A.obj.thickening.target.scheme] [IsAffine A'.obj.thickening.target.scheme]
    (τ : (changeBase S S' fS fX hf).obj ((CrystallineThickening.ι S).obj A') ⟶
      (CrystallineThickening.ι S').obj A)
    (hF : F.IsQuasicoherentOnSite) :
    Function.Bijective (crisInverseImageBaseChange fS fX hf F τ) :=
  bijective_crisInverseImageBaseChange fS fX hf F τ ((isQuasicoherentOnSite_iff F).1 hF).1
    ((isQuasicoherentOnSite_iff F).1 hF).2

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
