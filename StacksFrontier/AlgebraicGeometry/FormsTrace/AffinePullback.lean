module

public import StacksFrontier.AlgebraicGeometry.DeRham.Comparison.AffineSections
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteStratificationInvariant
public import StacksFrontier.RingTheory.FormsTrace.Defs
public import StacksFrontier.AlgebraicGeometry.Pushout.SquareSections

/-!
# Pull-back of absolute forms over affine opens, and pushouts of rings of sections

Two facts about affine charts of schemes, in the setting of Stacks, Lemma 0FLB.

* **Pull-back of forms over affine opens.** For `b : Y' ⟶ Y` and affine opens `V ⊆ Y`,
  `V' ⊆ Y'` with `V' ⊆ b⁻¹V`, the pull-back of absolute differential forms of schemes, restricted
  to `V'`, is the pull-back of forms `Ω^p_{Γ(Y, V)} → Ω^p_{Γ(Y', V')}` of rings
  (`Stacks.FormsTrace.formsMap`), under the identifications `Γ(Ω^p_{Y/ℤ}, V) = Ω^p_{Γ(Y, V)}`.
* **Cartesian squares over affines give pushouts of rings.** For a cartesian square
  `b ≫ f = f' ≫ a` of schemes with `f` affine, and affine opens `U ⊆ X`, `U' ⊆ X'` with
  `U' ⊆ a⁻¹U`, the square of rings `Γ(X, U) → Γ(Y, f⁻¹U)`, `Γ(X, U) → Γ(X', U')`,
  `Γ(Y, f⁻¹U) → Γ(Y', f'⁻¹U')`, `Γ(X', U') → Γ(Y', f'⁻¹U')` is a pushout of algebras.

## Main results

* `AlgebraicGeometry.Scheme.absoluteFormsSectionsEquiv_absoluteFormsPullback`: the first fact.
* `AlgebraicGeometry.Scheme.isPushout_chartAlgebra_of_isPullback`: the second fact, with the
  algebra structures `Scheme.Hom.chartAlgebra` and `Scheme.Hom.squareAlgebra` and the scalar
  towers `Scheme.Hom.isScalarTower_squareAlgebra_left` and
  `Scheme.Hom.isScalarTower_squareAlgebra_right`.

## References

* [Stacks Project, Tag 0FLB](https://stacks.math.columbia.edu/tag/0FLB)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme

section Forms

variable {Y Y' : Scheme.{u}} (b : Y' ⟶ Y) {V : Y.Opens} (hV : IsAffineOpen V) {V' : Y'.Opens}
  (hV' : IsAffineOpen V')

/-- **Pull-back of absolute forms over affine opens is the pull-back of forms of rings**: for
`b : Y' ⟶ Y` and affine opens `V' ⊆ b⁻¹V`, restricting the pull-back `b^*η` of a form `η` over
`V` to `V'` and identifying with `Ω^p_{Γ(Y', V')}` gives `formsMap Γ(Y, V) Γ(Y', V') p` of the
identification of `η`. -/
theorem absoluteFormsSectionsEquiv_absoluteFormsPullback (h : V' ≤ b ⁻¹ᵁ V) (p : ℕ)
    (η : Γ(absoluteDifferentialForms Y p, V)) :
    letI := (b.appLE V V' h).hom.toAlgebra
    absoluteFormsSectionsEquiv Y' hV' p ((absoluteDifferentialForms Y' p).presheaf.map
        (homOfLE h).op (b.absoluteFormsPullback p V η)) =
      Stacks.FormsTrace.formsMap Γ(Y, V) Γ(Y', V') p (absoluteFormsSectionsEquiv Y hV p η) :=
  (congrArg (absoluteFormsSectionsEquiv Y' hV' p)
    (absoluteFormsMap_app_pullbackSection b h p η).symm).trans
    (absoluteFormsSectionsEquiv_absoluteFormsMap_pullbackSection_kaehlerMapₛₗ hV b hV' h p η)

end Forms

section Pushout

variable {X Y X' Y' : Scheme.{u}} {f : Y ⟶ X} {f' : Y' ⟶ X'} {a : X' ⟶ X} {b : Y' ⟶ Y}

/-- **A cartesian square of schemes over affine opens gives a pushout of rings of sections.**
For a cartesian square `b ≫ f = f' ≫ a` with `f` affine and affine opens `U ⊆ X`, `U' ⊆ X'` with
`U' ⊆ a⁻¹U`, the square of rings of the charts `(U, f⁻¹U)` of `f` and `(U', f'⁻¹U')` of `f'` is
a pushout: `Γ(Y', f'⁻¹U') = Γ(X', U') ⊗_{Γ(X, U)} Γ(Y, f⁻¹U)`. -/
theorem isPushout_chartAlgebra_of_isPullback (H : IsPullback b f' f a) [IsAffineHom f]
    {U : X.Opens} (hU : IsAffineOpen U) {U' : X'.Opens} (hU' : IsAffineOpen U')
    (h : U' ≤ a ⁻¹ᵁ U) :
    letI := f.chartAlgebra (le_refl (f ⁻¹ᵁ U))
    letI := a.chartAlgebra h
    letI := f'.chartAlgebra (le_refl (f' ⁻¹ᵁ U'))
    letI := b.chartAlgebra (AlgebraicGeometry.preimage_le_preimage_of_comm H.w.symm h)
    letI := Hom.squareAlgebra f' a h (le_refl (f' ⁻¹ᵁ U'))
    haveI := Hom.isScalarTower_squareAlgebra_left h (le_refl (f' ⁻¹ᵁ U'))
    haveI := f.isScalarTower_squareAlgebra_right H.w (le_refl (f ⁻¹ᵁ U)) h
      (AlgebraicGeometry.preimage_le_preimage_of_comm H.w.symm h) (le_refl (f' ⁻¹ᵁ U'))
    Algebra.IsPushout Γ(X, U) Γ(Y, f ⁻¹ᵁ U) Γ(X', U') Γ(Y', f' ⁻¹ᵁ U') := by
  have hb := AlgebraicGeometry.preimage_le_preimage_of_comm H.w.symm h
  have hf' := le_refl (f' ⁻¹ᵁ U')
  let := f.chartAlgebra (le_refl (f ⁻¹ᵁ U))
  let := a.chartAlgebra h
  let := f'.chartAlgebra hf'
  let := b.chartAlgebra hb
  let := Hom.squareAlgebra f' a h hf'
  have := Hom.isScalarTower_squareAlgebra_left h hf'
  have := f.isScalarTower_squareAlgebra_right H.w (le_refl (f ⁻¹ᵁ U)) h hb hf'
  have hpo := Stacks.Morphisms.isPushout_appLE_of_isPullback H ⟨U, hU⟩ ⟨U', hU'⟩ h hb
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE] at hpo
  exact (CommRingCat.isPushout_iff_isPushout.mp hpo.flip).symm

end Pushout

end AlgebraicGeometry.Scheme

end
