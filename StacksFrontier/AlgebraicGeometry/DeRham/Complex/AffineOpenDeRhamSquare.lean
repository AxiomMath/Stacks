module

public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.AffineOpenDeRhamComplexIso

/-!
# The canonical map of de Rham complexes of a square, read on an affine open

Let

```
X' --f--> X
|         |
p'        p
v         v
S' --g--> S
```

be a commutative square of schemes, let `U ⊆ X` be an affine open whose inverse image
`f^{-1}U ⊆ X'` is again affine, and let `V ⊆ S` and `V' ⊆ S'` be affine opens with
`U ≤ p^{-1}V` and `f^{-1}U ≤ p'^{-1}V'`. The comparisons
`Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso` identify the sections of the
relative differential forms over `U` and over `f^{-1}U` with exterior powers of modules of Kähler
differentials. This file computes the canonical map `⋀ Ω_{X/S} ⟶ f_*(⋀ Ω_{X'/S'})` of
[Stacks, Tag 07HX] through those two identifications on the wedges `d a₁ ∧ ⋯ ∧ d a_n` of universal
differentials, and shows that the conjugated map is semilinear over the ring map
`f^♯ : Γ(X, U) ⟶ Γ(X', f^{-1}U)`. All declarations are in the namespace
`Stacks.AlgebraicGeometry.AffineOpenDeRham`.

## Main definitions

* `deRhamFormsPushforwardSections`: the canonical map on sections over `U`, with its target
  written as `Γ(Ω^n_{X'/S'}, f^{-1}U)`.

## Main results

* `deRhamFormsPushforwardHom_formsSectionsIso_inv`: read through the comparisons at `U` and at
  `f^{-1}U`, the canonical map carries `d a₁ ∧ ⋯ ∧ d a_n` to `d (f^♯ a₁) ∧ ⋯ ∧ d (f^♯ a_n)`.
* `formsSectionsIso_hom_deRhamFormsPushforwardHom_ιMulti_d`: the same computation with the
  comparison at `f^{-1}U` read in the forward direction.
* `appLE_square`: the two ring maps `Γ(S, V) ⟶ Γ(X', f^{-1}U)` given by the two routes around
  the square agree.
* `deRhamFormsPushforwardSections_add` and `deRhamFormsPushforwardSections_smul`: the canonical
  map on sections over `U` is additive and semilinear over `f^♯`.
* `formsSectionsIso_hom_pushforwardSections_smul`: the canonical map conjugated by the two
  comparisons is semilinear over `f^♯`.

## References

* [Stacks Project, Tag 07HX](https://stacks.math.columbia.edu/tag/07HX)
* [Stacks Project, Tag 0FUI](https://stacks.math.columbia.edu/tag/0FUI)
* [Stacks Project, Tag 0FLW](https://stacks.math.columbia.edu/tag/0FLW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.AffineOpenDeRham

variable {X' X S' S : Scheme.{u}} (f : X' ⟶ X) (p : X ⟶ S) (p' : X' ⟶ S') (g : S' ⟶ S)
  {U : X.Opens} {V : S.Opens} {V' : S'.Opens}
  (hU : IsAffineOpen U) (hU' : IsAffineOpen (f ⁻¹ᵁ U))
  (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
  (e : U ≤ p ⁻¹ᵁ V) (e' : f ⁻¹ᵁ U ≤ p' ⁻¹ᵁ V')

/-- **The canonical map of de Rham complexes of a commutative square, read over an affine open
on a wedge of universal differentials.** Let `U ⊆ X` be an affine open with `f^{-1}U` affine,
lying over an affine open `V ⊆ S`, and let `f^{-1}U` lie over an affine open `V' ⊆ S'`. Through
the degreewise comparison of `Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso` at `U`
and the one at `f^{-1}U`, the canonical map `⋀ Ω_{X/S} ⟶ f_*(⋀ Ω_{X'/S'})` of
[Stacks, Tag 07HX] carries `d a₁ ∧ ⋯ ∧ d a_n` to `d (f^♯ a₁) ∧ ⋯ ∧ d (f^♯ a_n)`, where
`f^♯ = f.app U : Γ(X, U) ⟶ Γ(X', f^{-1}U)`. -/
theorem deRhamFormsPushforwardHom_formsSectionsIso_inv (hcomm : f ≫ p = p' ≫ g) (n : ℕ)
    (a : Fin n → Γ(X, U)) :
    ((Scheme.Hom.deRhamFormsPushforwardHom f p p' g hcomm).app (n : ℤ)).val.app (op U)
        ((formsSectionsIso p hU hV e n).inv
          (exteriorPower.ιMulti Γ(X, U) n fun i ↦
            CommRingCat.KaehlerDifferential.d (a i))) =
      (formsSectionsIso p' hU' hV' e' n).inv
        (exteriorPower.ιMulti Γ(X', f ⁻¹ᵁ U) n fun i ↦
          CommRingCat.KaehlerDifferential.d ((f.app U).hom (a i))) := by
  rw [formsSectionsIso_inv_ιMulti_d, formsSectionsIso_inv_ιMulti_d]
  exact Scheme.Hom.deRhamFormsPushforwardHom_homogeneousProdLeft f p p' g hcomm (op U) n a

/-! ### The canonical map on sections, seated at `f^{-1}U` -/

/-- **The canonical map of the square, read on sections over `U`, with its target seated at
`Γ(Ω^n_{X'/S'}, f^{-1}U)`.** This is
`AlgebraicGeometry.Scheme.Hom.deRhamFormsPushforwardHom` over `U`, as a function:
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms` is an abbreviation for a piece of the
graded algebra, so the two sides differ only in how the open `f^{-1}U` is written. Seated here,
the target is a module over `Γ(X', f^{-1}U)`. -/
def deRhamFormsPushforwardSections (hcomm : f ≫ p = p' ≫ g) (n : ℕ)
    (ω : Γ(Scheme.Hom.relativeDifferentialForms p (n : ℤ), U)) :
    Γ(Scheme.Hom.relativeDifferentialForms p' (n : ℤ), f ⁻¹ᵁ U) :=
  ((Scheme.Hom.deRhamFormsPushforwardHom f p p' g hcomm).app (n : ℤ)).val.app (op U) ω

/-- The seated map is the canonical map; the seating changes no value. -/
theorem deRhamFormsPushforwardSections_apply (hcomm : f ≫ p = p' ≫ g) (n : ℕ)
    (ω : Γ(Scheme.Hom.relativeDifferentialForms p (n : ℤ), U)) :
    deRhamFormsPushforwardSections f p p' g hcomm n ω =
      ((Scheme.Hom.deRhamFormsPushforwardHom f p p' g hcomm).app (n : ℤ)).val.app (op U) ω :=
  rfl

/-- **The seated map is additive.** -/
theorem deRhamFormsPushforwardSections_add (hcomm : f ≫ p = p' ≫ g) (n : ℕ)
    (ω χ : Γ(Scheme.Hom.relativeDifferentialForms p (n : ℤ), U)) :
    deRhamFormsPushforwardSections f p p' g hcomm n (ω + χ) =
      deRhamFormsPushforwardSections f p p' g hcomm n ω +
        deRhamFormsPushforwardSections f p p' g hcomm n χ :=
  map_add (((Scheme.Hom.deRhamFormsPushforwardHom f p p' g hcomm).app
    (n : ℤ)).val.app (op U)).hom ω χ

/-- **The seated map is semilinear over `f^♯`**, with both scalar multiplications written over
the rings their modules are seated at. -/
theorem deRhamFormsPushforwardSections_smul (hcomm : f ≫ p = p' ≫ g) (n : ℕ) (b : Γ(X, U))
    (ω : Γ(Scheme.Hom.relativeDifferentialForms p (n : ℤ), U)) :
    deRhamFormsPushforwardSections f p p' g hcomm n (b • ω) =
      (f.app U).hom b • deRhamFormsPushforwardSections f p p' g hcomm n ω :=
  Scheme.Hom.deRhamFormsPushforwardHom_smul f p p' g hcomm (n : ℤ) (op U) b ω

/-- The same computation with the comparison at `f^{-1}U` turned around: the canonical map,
read over `U` through the comparison at `U` on the source and the comparison at `f^{-1}U` on the
target, carries `d a₁ ∧ ⋯ ∧ d a_n` to `d (f^♯ a₁) ∧ ⋯ ∧ d (f^♯ a_n)`. -/
theorem formsSectionsIso_hom_deRhamFormsPushforwardHom_ιMulti_d (hcomm : f ≫ p = p' ≫ g)
    (n : ℕ) (a : Fin n → Γ(X, U)) :
    (formsSectionsIso p' hU' hV' e' n).hom
        (((Scheme.Hom.deRhamFormsPushforwardHom f p p' g hcomm).app (n : ℤ)).val.app (op U)
          ((formsSectionsIso p hU hV e n).inv
            (exteriorPower.ιMulti Γ(X, U) n fun i ↦
              CommRingCat.KaehlerDifferential.d (a i)))) =
      exteriorPower.ιMulti Γ(X', f ⁻¹ᵁ U) n fun i ↦
        CommRingCat.KaehlerDifferential.d ((f.app U).hom (a i)) := by
  rw [deRhamFormsPushforwardHom_formsSectionsIso_inv f p p' g hU hU' hV hV' e e' hcomm n a,
    Iso.inv_hom_id_apply]

/-! ### The ring square of the square of schemes -/

/-- **The ring square of a commutative square of schemes, on sections.** The two routes from
`Γ(S, V)` to `Γ(X', f^{-1}U)` — down the left edge `p` and then across by `f`, or across the
bottom by `g` and then down the right edge `p'` — agree. -/
theorem appLE_square (hcomm : f ≫ p = p' ≫ g) (hVV' : V' ≤ g ⁻¹ᵁ V) :
    p.appLE V U e ≫ f.appLE U (f ⁻¹ᵁ U) le_rfl =
      g.appLE V V' hVV' ≫ p'.appLE V' (f ⁻¹ᵁ U) e' := by
  rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
  congr 1

/-! ### Semilinearity of the conjugated map -/

/-- **The canonical map of the square, conjugated by the two comparisons, is semilinear over
`f^♯`.** -/
theorem formsSectionsIso_hom_pushforwardSections_smul (hcomm : f ≫ p = p' ≫ g) (n : ℕ)
    (b : Γ(X, U))
    (ω : ↥(⋀[Γ(X, U)]^n ↥(CommRingCat.KaehlerDifferential (p.appLE V U e)))) :
    (formsSectionsIso p' hU' hV' e' n).hom
        (deRhamFormsPushforwardSections f p p' g hcomm n
          ((formsSectionsIso p hU hV e n).inv (b • ω))) =
      (f.app U).hom b • (formsSectionsIso p' hU' hV' e' n).hom
        (deRhamFormsPushforwardSections f p p' g hcomm n
          ((formsSectionsIso p hU hV e n).inv ω)) := by
  rw [map_smul, deRhamFormsPushforwardSections_smul, map_smul]

end Stacks.AlgebraicGeometry.AffineOpenDeRham

end
