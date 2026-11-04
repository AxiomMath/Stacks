module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafIsom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafIsomSupplement
public import StacksFrontier.Algebra.Homology.HomotopyCategory.PrecompBijective
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.Linear
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.RowAdicTower

/-!
# Rigidity of the tower of termwise reductions

Let `(C, J)` be a site with a final object, `A` a commutative ring and `𝔞 ⊆ A` an ideal. For a
sheaf of `A`-modules `F`, the map `F ≅ F ⊗_A \underline{A} ⟶ F ⊗_A \underline{A/𝔞ʲ}` is the
quotient of `F` by `𝔞ʲ`: tensoring with `F` is a `A`-linear left adjoint, so it preserves the
quotient `\underline{A} ⟶ \underline{A/𝔞ʲ}`. Consequently, for `i ≤ j` and complexes `L` and `K`
of sheaves of `A`-modules, a morphism in the homotopy category from `L ⊗ \underline{A/𝔞ʲ}` to
`K ⊗ \underline{A/𝔞ⁱ}` (tensor products taken termwise) is the same as a morphism from `L`, by
composition with the cone map `L ⟶ L ⊗ \underline{A/𝔞ʲ}`: termwise, the target is killed by
`𝔞ⁱ ⊇ 𝔞ʲ`.

## Main results

* `Stacks.ModuleSheaf.isQuotientBy_whiskerLeft`: tensoring with a sheaf preserves quotients by an
  ideal.
* `Stacks.ModuleSheaf.isQuotientBy_rowAdicTowerCone_app_f`: each term of the cone map
  `L ⟶ L ⊗ \underline{A/𝔞ʲ}` is the quotient by `𝔞ʲ`.
* `Stacks.ModuleSheaf.bijective_rowAdicTowerCone_comp`: the rigidity statement in the homotopy
  category, for a constant complex `L = \underline{M}`.
* `Stacks.ModuleSheaf.acyclic_rowAdicTower_obj_zero`: the term `K ⊗ \underline{A/𝔞⁰}` of the
  tower is acyclic, `A/𝔞⁰` being zero.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

universe w v u

namespace Stacks.ModuleSheaf

attribute [local instance] Sheaf.monoidalCategory monoidalClosed

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {A : Type w} [CommRing A]
  [UnivLE.{max u v, w}]

/-- **Tensoring with a sheaf of modules preserves quotients by an ideal**: `F ⊗ -` is an
`A`-linear left adjoint. -/
theorem isQuotientBy_whiskerLeft (F : Sheaf J (ModuleCat.{w} A)) {𝔟 : Ideal A}
    {U U' : Sheaf J (ModuleCat.{w} A)} {q : U ⟶ U'} (h : IsQuotientBy J A 𝔟 U U' q) :
    IsQuotientBy J A 𝔟 (F ⊗ U) (F ⊗ U') (F ◁ q) :=
  IsQuotientBy.map (tensorLeft F) (ihom.adjunction F) h

/-- The reduction `\underline{A} ⟶ \underline{A/𝔞ⁿ}` is the quotient by `𝔞ⁿ`. -/
theorem isQuotientBy_constantAdicQuotientCone_app {T : C} (hT : IsTerminal T) (𝔞 : Ideal A)
    (n : ℕ) :
    IsQuotientBy J A (𝔞 ^ n) ((constantSheaf J (ModuleCat.{w} A)).obj (ModuleCat.of A A))
      ((constantAdicQuotientTower J A 𝔞 (ModuleCat.of A A)).obj (op n))
      ((constantAdicQuotientCone J A 𝔞 (ModuleCat.of A A)).app (op n)) :=
  have : HasTerminal C := hT.hasTerminal
  isQuotientBy_constantSheaf J A (𝔞 ^ n) (ModuleCat.of A A)

/-- The terms of the tower of termwise reductions `K ⊗ \underline{A/𝔞ⁱ}` are killed by `𝔞ⁱ`. -/
theorem isAnnihilatedBy_rowAdicTower_obj_X {T : C} (hT : IsTerminal T) (𝔞 : Ideal A)
    (K : CochainComplex (Sheaf J (ModuleCat.{w} A)) ℤ) (i : ℕ) (l : ℤ) :
    IsAnnihilatedBy J A (𝔞 ^ i) (((rowAdicTower J 𝔞 K).obj (op i)).X l) :=
  (isQuotientBy_whiskerLeft (K.X l) (isQuotientBy_constantAdicQuotientCone_app hT 𝔞 i)).1

/-- **Each term of the cone map `L ⟶ L ⊗ \underline{A/𝔞ʲ}` is the quotient by `𝔞ʲ`.** -/
theorem isQuotientBy_rowAdicTowerCone_app_f {T : C} (hT : IsTerminal T) (𝔞 : Ideal A)
    (L : CochainComplex (Sheaf J (ModuleCat.{w} A)) ℤ) (j : ℕ) (k : ℤ) :
    IsQuotientBy J A (𝔞 ^ j) (L.X k) (((rowAdicTower J 𝔞 L).obj (op j)).X k)
      (((rowAdicTowerCone J 𝔞 L).app (op j)).f k) := by
  rw [rowAdicTowerCone_app]
  exact isQuotientBy_of_iso (ρ_ (L.X k)).symm
    (isQuotientBy_whiskerLeft (L.X k) (isQuotientBy_constantAdicQuotientCone_app hT 𝔞 j))

/-- Termwise, for `i ≤ j`, composition with the cone map `L ⟶ L ⊗ \underline{A/𝔞ʲ}` is a
bijection on morphisms into the terms of `K ⊗ \underline{A/𝔞ⁱ}`. -/
theorem bijective_rowAdicTowerCone_app_f_comp {T : C} (hT : IsTerminal T) (𝔞 : Ideal A)
    (L K : CochainComplex (Sheaf J (ModuleCat.{w} A)) ℤ) {i j : ℕ} (hij : i ≤ j) (k l : ℤ) :
    Function.Bijective (fun f : ((rowAdicTower J 𝔞 L).obj (op j)).X k ⟶
        ((rowAdicTower J 𝔞 K).obj (op i)).X l => ((rowAdicTowerCone J 𝔞 L).app (op j)).f k ≫ f) :=
  (Function.bijective_iff_existsUnique _).2 ((isQuotientBy_rowAdicTowerCone_app_f hT 𝔞 L j k).2 _
    ((isAnnihilatedBy_rowAdicTower_obj_X hT 𝔞 K i l).mono (Ideal.pow_le_pow_right hij)))

/-- **Rigidity of the tower of termwise reductions.** For `i ≤ j`, a morphism in the homotopy
category from `\underline{M} ⊗ \underline{A/𝔞ʲ}` to `K ⊗ \underline{A/𝔞ⁱ}` (tensor products taken
termwise) is determined by its composite with the cone map
`\underline{M} ⟶ \underline{M} ⊗ \underline{A/𝔞ʲ}`, and every morphism out of `\underline{M}`
arises in this way. (Nothing is used about `\underline{M}` beyond being a complex of sheaves.) -/
theorem bijective_rowAdicTowerCone_comp {T : C} (hT : IsTerminal T) (𝔞 : Ideal A)
    (M : CochainComplex (ModuleCat.{w} A) ℤ) (K : CochainComplex (Sheaf J (ModuleCat.{w} A)) ℤ)
    {i j : ℕ} (hij : i ≤ j) :
    Function.Bijective (fun φ : (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        ((rowAdicTower J 𝔞 (((constantSheaf J (ModuleCat.{w} A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M)).obj (op j)) ⟶
        (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj ((rowAdicTower J 𝔞 K).obj (op i)) =>
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((rowAdicTowerCone J 𝔞 (((constantSheaf J (ModuleCat.{w} A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M)).app (op j)) ≫ φ) :=
  HomotopyCategory.bijective_quotient_map_comp _
    (bijective_rowAdicTowerCone_app_f_comp hT 𝔞 _ K hij)

/-- The constant sheaf `\underline{A/𝔞⁰}` is zero. -/
theorem isZero_constantAdicQuotientTower_obj_zero (𝔞 : Ideal A) :
    IsZero ((constantAdicQuotientTower J A 𝔞 (ModuleCat.of A A)).obj (op 0)) := by
  refine (constantSheaf J (ModuleCat.{w} A)).map_isZero (X := ModuleCat.of A
    (A ⧸ (𝔞 ^ 0 • ⊤ : Submodule A A))) ?_
  have : Subsingleton (A ⧸ (𝔞 ^ 0 • ⊤ : Submodule A A)) := by
    rw [Submodule.Quotient.subsingleton_iff, pow_zero, Ideal.one_eq_top, Submodule.top_smul]
  exact ModuleCat.isZero_of_subsingleton _

/-- **The term `K ⊗ \underline{A/𝔞⁰}` of the tower of termwise reductions is acyclic**: its terms
are zero, `A/𝔞⁰` being zero. -/
theorem acyclic_rowAdicTower_obj_zero (𝔞 : Ideal A)
    (K : CochainComplex (Sheaf J (ModuleCat.{w} A)) ℤ) :
    ((rowAdicTower J 𝔞 K).obj (op 0)).Acyclic := fun l =>
  ShortComplex.exact_of_isZero_X₂ _
    (Functor.map_isZero (tensorLeft (K.X l)) (isZero_constantAdicQuotientTower_obj_zero 𝔞))

end Stacks.ModuleSheaf
