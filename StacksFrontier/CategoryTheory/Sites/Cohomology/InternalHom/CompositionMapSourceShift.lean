module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCompositionUnit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomSourceCommShift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.TensorTotalShiftSections
import StacksCore.Tactic.StacksAttribute

/-!
# Composition of internal Hom complexes commutes with the shift of its source

Let `(C, O)` be a ringed site and let `E`, `J`, `I` be complexes of `O`-modules.  The
composition morphism of Stacks 0A91,

`SheafHom(E, I) ⟵ Tot(SheafHom(J, I) ⊗_O SheafHom(E, J))`,

is `AlgebraicGeometry.RingedSite.compositionMap`.  This file computes what happens to it when
the **source** `E` is shifted, which is the chain level of the compatibility of the canonical
map of Stacks 08JD with the shift of the dualized variable.

Three identifications are in play, and the content is that the signs they carry cancel:

* the source-shift identification `SheafHom(E, N)[c] ≅ SheafHom(E[b], N)` of
  `AlgebraicGeometry.RingedSite.sheafHomSourceShiftIso'`, used at `N = J` on the right tensor
  factor and at `N = I` on the target, which multiplies a degree-`n` cochain by
  `(-1)^(b n' + b (b - 1) / 2)` where `n + b = n'`;
* the Koszul comparison `Tot(A ⊗_O Z[c]) ≅ Tot(A ⊗_O Z)[c]` of
  `AlgebraicGeometry.RingedSite.tensorTotalShiftIso₂`, which multiplies the `(t, r)` summand by
  `(-1)^(t c)`.

On the local pure tensor of a degree-`t` section of `SheafHom(J, I)` with a degree-`(r + c)`
section of `SheafHom(E, J)` the first identification is paid twice, in the degrees `r` and
`t + r`, so the two source-shift signs differ by `(-1)^(b t)`; and `b t + t c = t (b + c) = 0`.
Hence the square commutes **on the nose**, with no residual sign.

## Main results

* `AlgebraicGeometry.RingedSite.cochainSourceShift_comp`: the cochain-level statement.  Shifting
  the source of a composite of cochains is `(-1)^(t c)` times composing the shifted first factor
  with the second, `t` being the degree of the second factor.
* `AlgebraicGeometry.RingedSite.compositionSection_sourceShiftFun`: the same on homogeneous
  local sections of the internal Hom complexes.
* `AlgebraicGeometry.RingedSite.compositionMap_sourceShift`: **the square of morphisms of
  complexes.**  Composition, read through the source-shift identification on its right tensor
  factor, is the Koszul comparison followed by the shift of composition and by the source-shift
  identification on the target.

## Implementation notes

The cochain-level statement is proved componentwise from
`AlgebraicGeometry.RingedSite.cochainSourceShift_v` rather than from Mathlib's
`CochainComplex.HomComplex.Cochain.leftShift_comp`: the shift of the source of a cochain between
*restricted* complexes is `Cochain.leftShift` conjugated by the zero-cochain
`AlgebraicGeometry.RingedSite.restrictComplexShiftIso`, whose insertion would have to be undone
before Mathlib's lemma applied, and the components are one rewrite each.

The two signs are equal as *integers*, not merely modulo `2`: the exponent
`b r + b (b - 1) / 2` of the right-hand side's inner shift and the exponent
`t c + (b (t + r) + b (b - 1) / 2)` of the left-hand side agree once `c = -b`, the term
`b (b - 1) / 2` — an integer division, which no `ring` normalisation would touch — occurring
unchanged on both sides.

The three statements are at the diagonal universes `RingedSite.{u, u, u}` with modules in `u`,
as the total tensor complex forces; the cochain-level one would hold at four independent
universes.

## References

* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
* [Stacks Project, Tag 08JD](https://stacks.math.columbia.edu/tag/08JD)
* [Stacks Project, Tag 0FLG](https://stacks.math.columbia.edu/tag/0FLG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms
  curriedTensorAdditive curriedTensorObjAdditive

section Cochains

variable {E J I :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- **Shifting the source of a composite cochain.**  Let `γ` be a cochain from `E|_U` to `J|_U`
of degree `r + c` and `β` a cochain from `J|_U` to `I|_U` of degree `t`, and let `b + c = 0`.
Composing the source-shifted `γ` with `β` is `(-1)^(t c)` times the source shift of the
composite of `γ` with `β`.

Both sides are, componentwise, the same morphism scaled by a sign; the two exponents differ by
`t c + b t = t (b + c)`, which vanishes. -/
lemma cochainSourceShift_comp (U : X.C) (b c t r : ℤ) (hc : b + c = 0)
    (γ : Cochain (restrictComplex X E U) (restrictComplex X J U) (r + c))
    (β : Cochain (restrictComplex X J U) (restrictComplex X I U) t) :
    (cochainSourceShift X (K := E) (M := J) U b (r + c) r (by omega) γ).comp β
        (show r + t = t + r by omega) =
      (t * c).negOnePow •
        cochainSourceShift X (K := E) (M := I) U b (t + r + c) (t + r) (by omega)
          (γ.comp β (show r + c + t = t + r + c by omega)) := by
  have hsign : ((t * c).negOnePow : ℤˣ) * (b * (t + r) + b * (b - 1) / 2).negOnePow =
      (b * r + b * (b - 1) / 2).negOnePow := by
    rw [← Int.negOnePow_add]
    congr 1
    obtain rfl : c = -b := by omega
    ring
  refine Cochain.ext _ _ fun p q hpq => ?_
  rw [Cochain.comp_v _ _ (show r + t = t + r by omega) p (p + r) q rfl (by omega),
    cochainSourceShift_v X U b (r + c) r (by omega) γ p (p + r) rfl,
    Cochain.units_smul_v, cochainSourceShift_v X U b (t + r + c) (t + r) (by omega) _ p q hpq,
    Cochain.comp_v _ _ (show r + c + t = t + r + c by omega) (p + b) (p + r) q (by omega)
      (by omega),
    Linear.units_smul_comp, smul_smul, hsign]

end Cochains

section Sections

/-- A morphism of sheaves of modules carries a unit-integer multiple of a local section to the
same multiple of its image: it is additive, and a unit of `ℤ` acts through `ℤ`.  This is
linearity in the *section*, and is not the naturality statement in which the unit scales the
morphism instead. -/
lemma val_app_unitsSmul {A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (φ : A ⟶ B) (ε : ℤˣ) (U : X.Cᵒᵖ) (x : A.val.obj U) :
    (φ.val.app U) (ε • x) = ε • (φ.val.app U) x :=
  map_zsmul _ (ε : ℤ) x

variable {E J I :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- **Composing with a source-shifted section.**  The composite of a degree-`t` section `β` of
`SheafHom(J, I)` with the source shift of a degree-`(r + c)` section `γ` of `SheafHom(E, J)` is
`(-1)^(t c)` times the source shift of their composite.  This is
`AlgebraicGeometry.RingedSite.cochainSourceShift_comp` read through the characterising
identification of sections of an internal Hom complex with cochains. -/
lemma compositionSection_sourceShiftFun (U : X.C) (b c t r : ℤ) (hc : b + c = 0)
    (β : ((sheafHomComplex X J I).obj.X t).val.obj (op U))
    (γ : ((sheafHomComplex X E J).obj.X (r + c)).val.obj (op U)) :
    compositionSection X U t r (t + r) rfl β
        (sourceShiftFun X (K := E) (M := J) b (r + c) r (by omega) U γ) =
      (t * c).negOnePow •
        sourceShiftFun X (K := E) (M := I) b (t + r + c) (t + r) (by omega) U
          (compositionSection X U t (r + c) (t + r + c) (by omega) β γ) := by
  apply ((sheafHomComplex X (E⟦b⟧) I).sectionsEquiv U (t + r)).injective
  have hsm : (sheafHomComplex X (E⟦b⟧) I).sectionsEquiv U (t + r)
        ((t * c).negOnePow •
          sourceShiftFun X (K := E) (M := I) b (t + r + c) (t + r) (by omega) U
            (compositionSection X U t (r + c) (t + r + c) (by omega) β γ)) =
      (t * c).negOnePow •
        (sheafHomComplex X (E⟦b⟧) I).sectionsEquiv U (t + r)
          (sourceShiftFun X (K := E) (M := I) b (t + r + c) (t + r) (by omega) U
            (compositionSection X U t (r + c) (t + r + c) (by omega) β γ)) :=
    map_zsmul _ (((t * c).negOnePow : ℤˣ) : ℤ) _
  rw [compositionSection_cochain, hsm, sectionsEquiv_sourceShiftFun, compositionSection_cochain]
  dsimp only [compositionCochain]
  rw [sectionsEquiv_sourceShiftFun]
  exact cochainSourceShift_comp X U b c t r hc _ _

end Sections

/-- **Composition of internal Hom complexes commutes with the shift of its source.**  For
complexes `E`, `J`, `I` and integers `b`, `c` with `b + c = 0`, the composition morphism of
Stacks 0A91 at source `E[b]`, read through the source-shift identification
`SheafHom(E, J)[c] ≅ SheafHom(E[b], J)` on its right tensor factor, is the Koszul comparison
`Tot(SheafHom(J, I) ⊗_O SheafHom(E, J)[c]) ≅ Tot(SheafHom(J, I) ⊗_O SheafHom(E, J))[c]`
followed by the shift of composition at source `E` and by the source-shift identification
`SheafHom(E, I)[c] ≅ SheafHom(E[b], I)` on the target.

There is no residual sign: the Koszul sign `(-1)^(t c)` of the comparison cancels the
discrepancy `(-1)^(b t)` between the two source-shift signs. -/
theorem compositionMap_sourceShift
    (E J I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (b c : ℤ) (hc : b + c = 0) :
    tensorTotalMap X (𝟙 (sheafHomComplex X J I).obj)
          (sheafHomSourceShiftIso' X (K := E) (M := J) b c hc).hom ≫
        compositionMap X (E⟦b⟧) J I =
      (tensorTotalShiftIso₂ X (sheafHomComplex X J I).obj (sheafHomComplex X E J).obj c).hom ≫
        (CategoryTheory.shiftFunctor (CochainComplex
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) c).map
            (compositionMap X E J I) ≫
          (sheafHomSourceShiftIso' X (K := E) (M := I) b c hc).hom := by
  refine tensorTotal_hom_ext X fun U t r β γ => ?_
  rw [HomologicalComplex.comp_f, comp_val_app_apply', tensorTotalMap_tensorTotalSection,
    compositionMap_tensorTotalSection, sheafHomSourceShiftIso'_hom_f]
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, comp_val_app_apply',
    comp_val_app_apply', tensorTotalShiftIso₂_tensorTotalSection, val_app_unitsSmul,
    CochainComplex.shiftFunctor_map_f',
    compositionMap_tensorTotalSectionAt X E J I U t (r + c) (t + r + c) (by omega) β γ,
    sheafHomSourceShiftIso'_hom_f, val_app_unitsSmul]
  exact compositionSection_sourceShiftFun X U b c t r hc β γ

end AlgebraicGeometry.RingedSite

end
