module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import StacksFrontier.Algebra.DGA.DGCategory

/-!
# Cochain complexes of modules as a differential graded category over the base ring

Let `R` be a commutative ring. The cochain complexes of `R`-modules form a differential graded
category *over `R`*: a degree-`n` morphism `K ⟶ L` is a degree-`n` cochain, its differential is
the usual graded commutator with the differentials of `K` and `L`, and composition is the
componentwise composition of cochains.

This is the differential graded category in which the endomorphism differential graded algebra of
a complex of `R`-modules lives.

## Main definitions

* `CochainComplex.moduleCatDGCategory`: the differential graded `R`-category of cochain complexes
  of `R`-modules.

## Main results

* `CochainComplex.moduleCatDGCategory_leibniz_aux`: the Leibniz rule for the graded commutator
  differential, with the sign written as a scalar in `R`.

## Implementation notes

The homogeneous morphisms and their differential are Mathlib's
`CochainComplex.HomComplex.Cochain` and `CochainComplex.HomComplex.δ`, so clients can use the
existing componentwise API with no conversion. The ground ring is `R` rather than `ℤ`, which is
what makes the endomorphism construction below an `R`-algebra.

The Leibniz rule is factored out as `moduleCatDGCategory_leibniz_aux` because Mathlib's
`CochainComplex.HomComplex.δ_comp` states the sign as an action of `ℤˣ`, and converting it to the
`(-1 : R) ^ m.natAbs` scalar required by `DGCategory.leibniz` is the one step of the construction
that is not a direct field match.

## References

* [Stacks Project, Tag 0FQ3](https://stacks.math.columbia.edu/tag/0FQ3)
-/

@[expose] public section

open CategoryTheory CochainComplex CochainComplex.HomComplex

namespace CochainComplex

universe u

variable {R : Type u} [CommRing R]

/-- The Leibniz rule for the graded commutator differential on cochains, with the sign written as
the scalar `(-1 : R) ^ m.natAbs` rather than as an action of `ℤˣ`. -/
theorem moduleCatDGCategory_leibniz_aux
    {K L M : CochainComplex (ModuleCat.{u} R) ℤ} {m n k : ℤ} (h : m + n = k)
    (g : Cochain L M m) (f : Cochain K L n) :
    δ k (k + 1) (f.comp g (show n + m = k by omega)) =
      f.comp (δ m (m + 1) g) (show n + (m + 1) = k + 1 by omega) +
        (-1 : R) ^ m.natAbs •
          (δ n (n + 1) f).comp g (show n + 1 + m = k + 1 by omega) := by
  have hd := δ_comp f g (show n + m = k by omega) (n + 1) (m + 1) (k + 1)
    (by omega) (by omega) (by omega)
  rw [Units.smul_def] at hd
  rw [← Int.cast_smul_eq_zsmul R (m.negOnePow : ℤ), Int.coe_negOnePow R m] at hd
  exact hd

/-- The differential graded category over `R` whose objects are the cochain complexes of
`R`-modules, whose degree-`n` morphisms `K ⟶ L` are the degree-`n` cochains, whose differential is
`f ↦ δ n (n + 1) f` and whose composition is the composition of cochains. -/
def moduleCatDGCategory (R : Type u) [CommRing R] :
    DGCategory.{u, u + 1, u} R where
  Obj := CochainComplex (ModuleCat.{u} R) ℤ
  Hom K L n := Cochain K L n
  addCommGroup _ _ _ := inferInstance
  module _ _ _ := inferInstance
  d {_ _ n} f := δ n (n + 1) f
  d_add {_ _ n} f g := δ_add n (n + 1) f g
  d_smul {_ _ n} r f := δ_smul n (n + 1) r f
  d_d {_ _ n} f := δ_δ n (n + 1) (n + 1 + 1) f
  comp {_ _ _ m n k} _ g f := f.comp g (show n + m = k by omega)
  comp_add_left {_ _ _ m n k} _ g₁ g₂ f :=
    Cochain.comp_add f g₁ g₂ (show n + m = k by omega)
  comp_add_right {_ _ _ m n k} _ g f₁ f₂ :=
    Cochain.add_comp f₁ f₂ g (show n + m = k by omega)
  comp_smul_left {_ _ _ m n k} _ r g f :=
    Cochain.comp_smul f r g (show n + m = k by omega)
  comp_smul_right {_ _ _ m n k} _ r g f :=
    Cochain.smul_comp r f g (show n + m = k by omega)
  leibniz h g f := moduleCatDGCategory_leibniz_aux h g f
  assoc {_ _ _ _ l m n p q r} h₁ h₂ h₃ h₄ e g f :=
    Cochain.comp_assoc f g e (show n + m = p by omega) (show m + l = q by omega)
      (show n + m + l = r by omega)
  id K := Cochain.ofHom (𝟙 K)
  id_comp f := Cochain.comp_id f
  comp_id f := Cochain.id_comp f
  d_id K := δ_ofHom (p := (1 : ℤ)) (𝟙 K)

@[simp]
theorem moduleCatDGCategory_Obj :
    (moduleCatDGCategory R).Obj = CochainComplex (ModuleCat.{u} R) ℤ := rfl

@[simp]
theorem moduleCatDGCategory_Hom (K L : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (moduleCatDGCategory R).Hom K L n = Cochain K L n := rfl

end CochainComplex
