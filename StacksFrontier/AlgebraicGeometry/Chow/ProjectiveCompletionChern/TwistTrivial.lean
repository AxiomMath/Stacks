module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveCompletionChern.ZeroSection
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.TowerChow
public import StacksFrontier.AlgebraicGeometry.QcohRestrictEquiv.IsoLocality

/-!
# `𝒪_E(1)` is trivial on the vector bundle

Let `E = Proj_X(Sym^*(𝒞)[T])` and `j : C = Spec_X(Sym^*(𝒞)) ⟶ E` the inclusion of the open where
the section `T` of `𝒪_E(1)` does not vanish. Multiplication by `T` is an isomorphism
`𝒪_E ⟶ 𝒪_E(1)` over that open, so `j^* 𝒪_E(1) ≅ 𝒪_C`.

## Main definitions

* `Stacks.Chow.ProjectiveCompletion.mulT`: multiplication by `T`, `𝒪_E ⟶ 𝒪_E(1)`.
* `Stacks.Chow.ProjectiveCompletion.pullbackTwistIso`: `j^* 𝒪_E(1) ≅ 𝒪_C`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.Chow.ProjectiveCompletion

variable {X : Scheme.{u}} (𝒞 : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒞]

/-- The section `T` of `𝒪_E(1)`, as a section of the sheaf. -/
def sectionsT : (twist 𝒞).sections :=
  (exists_sections_eval_eq (twist 𝒞) (coordT 𝒞)).choose

/-- The global section of `sectionsT 𝒞` over `E` is `coordT 𝒞`. -/
theorem sectionsT_eval : (sectionsT 𝒞).eval (op ⊤) = coordT 𝒞 :=
  (exists_sections_eval_eq (twist 𝒞) (coordT 𝒞)).choose_spec

/-- **Multiplication by `T`**, `𝒪_E ⟶ 𝒪_E(1)`. -/
def mulT : SheafOfModules.unit (space 𝒞).ringCatSheaf ⟶ twist 𝒞 :=
  (twist 𝒞).unitHomEquiv.symm (sectionsT 𝒞)

/-- On an open `W`, `mulT 𝒞` sends a section `a` of `𝒪_E` to `a` times the restriction of `T` to
`W`. -/
theorem mulT_app (W : (space 𝒞).Opens) (a : Γ(space 𝒞, W)) :
    ((mulT 𝒞).val.app (op W)).hom a =
      a • (twist 𝒞).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (coordT 𝒞) := by
  have h := ((sectionsT 𝒞).property (homOfLE (le_top : W ≤ ⊤)).op).symm
  have h2 : (sectionsT 𝒞).val (op ⊤) = coordT 𝒞 := sectionsT_eval 𝒞
  rw [h2] at h
  exact congrArg (fun m : Γ(twist 𝒞, W) => a • m) h

variable (r : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒞 r]

include r in
/-- **Multiplication by `T` is an isomorphism over `C`.** -/
theorem isIso_restrict_mulT :
    IsIso ((Scheme.Modules.restrictFunctor (openT 𝒞).ι).map (mulT 𝒞)) := by
  refine Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_val_app _ fun W => ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  have h := bijective_smul_coordT 𝒞 r (Scheme.Opens.ι_image_le (openT 𝒞) W.unop)
  rw [← funext (mulT_app 𝒞 ((openT 𝒞).ι ''ᵁ W.unop))] at h
  exact h

/-- **`𝒪_E(1)` is trivial over `C = {T ≠ 0}`**, by multiplication by `T`. -/
def twistOpenTIso : (Scheme.Modules.pullback (openT 𝒞).ι).obj (twist 𝒞) ≅
    SheafOfModules.unit (openT 𝒞).toScheme.ringCatSheaf :=
  haveI := isIso_restrict_mulT 𝒞 r
  ((Scheme.Modules.restrictFunctorIsoPullback (openT 𝒞).ι).app (twist 𝒞)).symm ≪≫
    (asIso ((Scheme.Modules.restrictFunctor (openT 𝒞).ι).map (mulT 𝒞))).symm ≪≫
    Scheme.Modules.restrictUnitIso (openT 𝒞).ι

/-- **`j^* 𝒪_E(1) ≅ 𝒪_C`** for the inclusion `j : C = Spec_X(Sym^*(𝒞)) ⟶ E`. -/
def pullbackTwistIso : (Scheme.Modules.pullback (vectorBundleIncl 𝒞 r)).obj (twist 𝒞) ≅
    SheafOfModules.unit (Scheme.Modules.vectorBundle X 𝒞).ringCatSheaf :=
  ((Scheme.Modules.pullbackComp (inv (toVectorBundle 𝒞 r).left) (openT 𝒞).ι).app
      (twist 𝒞)).symm ≪≫
    (Scheme.Modules.pullback (inv (toVectorBundle 𝒞 r).left)).mapIso (twistOpenTIso 𝒞 r) ≪≫
    Scheme.Modules.pullbackUnitIso (inv (toVectorBundle 𝒞 r).left)

end Stacks.Chow.ProjectiveCompletion

end
