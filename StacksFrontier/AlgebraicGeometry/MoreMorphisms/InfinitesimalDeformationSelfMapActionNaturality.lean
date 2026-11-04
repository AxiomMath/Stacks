module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalDeformationSelfMapHomSectionValue
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalDeformationThickenedBaseActionNaturality

/-!
# The lift `θ ⬝ b` under a self-map of the thickening

Let `i : X ⟶ X'` be a first-order thickening and `b` a lift over an open `V` of `X'`. Let `σ`,
`w`, `v` be self-maps of `X'`, `V` and `Y'` fixing the closed subschemes and compatible with `b`,
such that `σ` acts on the conormal sections as multiplication by a section `r`. If the acting
section `θ₂` is `r` times `θ₁`, then `(θ₂ ⬝ b) ≫ v = w ≫ (θ₁ ⬝ b)`; the same holds for the
action `Stacks.Thickenings.liftsOverBaseVAddOfBase` on lifts over a base.

## Main results

* `Stacks.Thickenings.morphismRestrict_comp_self_of_comp_ι`: a self-map of an open lying over a
  self-map of the ambient scheme that fixes the closed subscheme restricts to the identity on
  the part of the subscheme cut out by that open.
* `Stacks.Thickenings.homSectionAct_comp_of_conormalSelfMap_eq_smul`: the lift `θ ⬝ b` commutes
  with the self-maps.
* `Stacks.Thickenings.liftsOverBaseVAddOfBase_comp_of_conormalSelfMap_eq_smul`: the action on
  lifts over a base commutes with the self-maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Thickenings

section SelfMapNaturality

variable {S X X' Y Y' : Scheme.{u}} {i : X ⟶ X'} {j : Y ⟶ Y'} {a : X ⟶ Y}
  [IsClosedImmersion i] [IsImmersion j]
  {V : X'.Opens} {b : V.toScheme ⟶ Y'} {σ : X' ⟶ X'} {w : V.toScheme ⟶ V.toScheme}
  {v : Y' ⟶ Y'}

omit [IsClosedImmersion i] [IsImmersion j] in
/-- A self-map `w` of an open `V` lying over a self-map `σ` of the ambient scheme with
`i ≫ σ = i` restricts to the identity on `i ⁻¹ᵁ V`: `i ∣_ V ≫ w = 𝟙 _ ≫ i ∣_ V`. -/
theorem morphismRestrict_comp_self_of_comp_ι (hσ : i ≫ σ = i) (hw : w ≫ V.ι = V.ι ≫ σ) :
    i ∣_ V ≫ w = 𝟙 (i ⁻¹ᵁ V).toScheme ≫ i ∣_ V := by
  rw [Category.id_comp, ← cancel_mono V.ι, Category.assoc, hw, ← Category.assoc,
    morphismRestrict_ι, Category.assoc, hσ]

/-- The lift `θ ⬝ b` commutes with a self-map of the thickening that scales the conormal
sections. Let `i : X ⟶ X'` be a first-order thickening, `b : V ⟶ Y'` a lift of `a : X ⟶ Y`
along `j` over an open `V` of `X'`, and let

* `σ : X' ⟶ X'` fix the closed subscheme, `i ≫ σ = i`;
* `w : V ⟶ V` lie over `σ`, `w ≫ V.ι = V.ι ≫ σ`;
* `v : Y' ⟶ Y'` fix `Y`, `j ≫ v = j`;
* the lift be compatible, `b ≫ v = w ≫ b`.

If `σ` induces multiplication by a section `r` of `𝒪_X` on the conormal sections and the acting
section `θ₂` is `r` times `θ₁`, then `(θ₂ ⬝ b) ≫ v = w ≫ (θ₁ ⬝ b)`. -/
theorem homSectionAct_comp_of_conormalSelfMap_eq_smul
    (hsq : i.ker ^ 2 = ⊥) (pY' : Y' ⟶ S) (hσ : i ≫ σ = i)
    (cb : i ∣_ V ≫ b = ((i ⁻¹ᵁ V).ι ≫ a) ≫ j)
    (hw : w ≫ V.ι = V.ι ≫ σ) (hv : j ≫ v = j) (cA : b ≫ v = w ≫ b)
    (θ₁ θ₂ : deformationHomSections i a (j ≫ pY') V) {r : Γ(X, i ⁻¹ᵁ V)}
    (hc : ∀ (A : X'.Opens) (hA : A ≤ V) (x : Γ(conormalModules i, i ⁻¹ᵁ A)),
      conormalSelfMap hsq hσ A x
        = (X.presheaf.map (homOfLE (i.preimage_mono hA)).op).hom r • x)
    (hθ : ∀ (U : X.Opens) (hU : U ≤ i ⁻¹ᵁ V)
        (y : Γ(Smooth.pullbackCotangentSheaf (j ≫ pY') a, U)),
      θ₂.app hU y = (X.presheaf.map (homOfLE hU).op).hom r • θ₁.app hU y) :
    homSectionAct hsq pY' cb θ₂ ≫ v = w ≫ homSectionAct hsq pY' cb θ₁ :=
  homSectionAct_comp_of_homSectionValue_comm hsq hsq pY' pY' cb cb
    (morphismRestrict_comp_self_of_comp_ι hσ hw)
    (by rw [Category.id_comp]; exact hv)
    (by rw [Category.comp_id, Category.id_comp]) cA θ₁ θ₂
    (homSectionValue_comm_of_conormalSelfMap_eq_smul hsq pY' hσ cb hw hv cA hc hθ)

end SelfMapNaturality

/-! ### The action on lifts over a base under a self-map of the thickening -/

section ActionSelfMapNaturality

variable {X X' Y Y' Z Z' : Scheme.{u}} {i : X ⟶ X'} {j : Y ⟶ Y'} {k : Z ⟶ Z'}
  [IsClosedImmersion i] [IsImmersion j] [IsImmersion k]
  {h : Y ⟶ Z} {h' : Y' ⟶ Z'} {g' : X' ⟶ Z'} {a : X ⟶ Y}
  {V : X'.Opens} {σ : X' ⟶ X'} {w : V.toScheme ⟶ V.toScheme} {v : Y' ⟶ Y'}

/-- The action `Stacks.Thickenings.liftsOverBaseVAddOfBase` on a lift fixed by the self-maps
commutes with them. For self-maps `σ`, `w`, `v` as in
`Stacks.Thickenings.homSectionAct_comp_of_conormalSelfMap_eq_smul`, a lift `c` compatible with
them (`c.1 ≫ v = w ≫ c.1`), and acting sections whose images under
`Stacks.Thickenings.baseDeformationHomSectionsEquiv` satisfy `θ₂ = r • θ₁`, the underlying
morphisms satisfy `(θ₂ ⬝ c) ≫ v = w ≫ (θ₁ ⬝ c)`. -/
theorem liftsOverBaseVAddOfBase_comp_of_conormalSelfMap_eq_smul
    (hsq : i.ker ^ 2 = ⊥) (sq : IsPullback j h h' k) (ci : i ≫ g' = (a ≫ h) ≫ k)
    {A : (modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
      immersionConormalSheaf i}
    (hA : IsBaseCompatibleConormalMap i j k h h' g' a sq.w ci A)
    (hσ : i ≫ σ = i) (hw : w ≫ V.ι = V.ι ≫ σ) (hv : j ≫ v = j)
    (θ₁ θ₂ : deformationHomSections i a h V) (c : liftsOverBase i j g' h' a V)
    (cA : c.1 ≫ v = w ≫ c.1) {r : Γ(X, i ⁻¹ᵁ V)}
    (hc : ∀ (B : X'.Opens) (hB : B ≤ V) (x : Γ(conormalModules i, i ⁻¹ᵁ B)),
      conormalSelfMap hsq hσ B x
        = (X.presheaf.map (homOfLE (i.preimage_mono hB)).op).hom r • x)
    (hθ : ∀ (U : X.Opens) (hU : U ≤ i ⁻¹ᵁ V)
        (y : Γ(Smooth.pullbackCotangentSheaf (j ≫ h') a, U)),
      (baseDeformationHomSectionsEquiv sq a V θ₂).app hU y
        = (X.presheaf.map (homOfLE hU).op).hom r •
            (baseDeformationHomSectionsEquiv sq a V θ₁).app hU y) :
    (liftsOverBaseVAddOfBase hsq sq ci hA V θ₂ c).1 ≫ v
      = w ≫ (liftsOverBaseVAddOfBase hsq sq ci hA V θ₁ c).1 := by
  rw [liftsOverBaseVAddOfBase_coe hsq sq ci hA V θ₁ c c.2.2,
    liftsOverBaseVAddOfBase_coe hsq sq ci hA V θ₂ c c.2.2]
  exact homSectionAct_comp_of_conormalSelfMap_eq_smul hsq h' hσ c.2.2 hw hv cA
    (baseDeformationHomSectionsEquiv sq a V θ₁) (baseDeformationHomSectionsEquiv sq a V θ₂)
    hc hθ

end ActionSelfMapNaturality

end Stacks.Thickenings

end
