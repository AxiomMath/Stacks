module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticConstantDerivedAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionExact
public import StacksFrontier.RingTheory.Koszul.ExtendSectionsCoefficientTower

/-!
# Extension of scalars to the Koszul sheaf preserves quasi-isomorphisms

Let `R` be a commutative ring, `f₁, …, f_r ∈ R`, and `ℬ = (K_{n+1})_n` the sheaf of differential
graded algebras on the chaotic site whose term `K_n` is the Koszul algebra on `f₁^n, …, f_r^n`.
Extension of scalars `K ↦ K ⊗_R ℬ` carries quasi-isomorphisms of complexes of `R`-modules to
quasi-isomorphisms of right differential graded `ℬ`-modules, and hence descends to the derived
categories.

## Main results

* `Koszul.quasiIso_extendFunctor_map`: `g ⊗ 1 : K ⊗_R ℬ ⟶ L ⊗_R ℬ` is a quasi-isomorphism when
  `g` is.
* `Koszul.extendInvertsQuasiIso`: extension of scalars to `ℬ`, followed by localization, inverts
  the quasi-isomorphisms of the homotopy category.

## References

* [Stacks Project, Proposition 24.35.4 (Tag 0GZK)](https://stacks.math.columbia.edu/tag/0GZK)
* [Stacks Project, Tag 091Z](https://stacks.math.columbia.edu/tag/091Z)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Stacks Stacks.ChaoticSite

universe u

namespace Koszul

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.SheafOfModules.botWEqualsLocallyBijective

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)

/-- For a quasi-isomorphism `g : K ⟶ L` of complexes of `R`-modules, `g ⊗ 1 : K ⊗_R ℬ ⟶ L ⊗_R ℬ`
is a quasi-isomorphism of the underlying complexes of sheaves. -/
theorem quasiIso_extendFunctor_map {K L : CochainComplex (ModuleCat.{u} R) ℤ} (g : K ⟶ L)
    [QuasiIso g] :
    QuasiIso ((extendFunctor (liftedPowAlg f)).map g).toHomologicalComplex := by
  rw [Stacks.SheafOfModules.quasiIso_iff_forall_quasiIso_evaluation]
  rintro ⟨⟨n⟩⟩
  exact quasiIso_extendSectionsTowerMap f g n

/-- Extension of scalars to `ℬ`, followed by localization, inverts the quasi-isomorphisms of the
homotopy category of complexes of `R`-modules. -/
theorem extendInvertsQuasiIso : ExtendInvertsQuasiIso (liftedPowSheafAlgebra f) := by
  unfold ExtendInvertsQuasiIso
  rw [HomotopyCategory.quasiIso_eq_quasiIso_map_quotient, MorphismProperty.IsInvertedBy.map_iff]
  intro K L g hg
  have : QuasiIso g := hg
  have h : (_root_.SheafOfModules.DifferentialGradedModule.quasiIsomorphisms.{u, u, u}
      (liftedPowSheafAlgebra f))
      ((_root_.SheafOfModules.DifferentialGradedModule.HomotopyCategory.quotient
        (liftedPowSheafAlgebra f)).map ((extendFunctor (liftedPowAlg f)).map g)) :=
    (_root_.SheafOfModules.DifferentialGradedModule.quasiIsomorphisms_quotient_map_iff _).2
      (quasiIso_extendFunctor_map f g)
  have e : (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ) ⋙
      homotopyExtend' (liftedPowSheafAlgebra f)).map g =
      (_root_.SheafOfModules.DifferentialGradedModule.HomotopyCategory.quotient
        (liftedPowSheafAlgebra f)).map ((extendFunctor (liftedPowAlg f)).map g) :=
    Functor.congr_hom (quotient_comp_homotopyExtend (castAlg (liftedPowSheafAlgebra f))) g
  show IsIso ((_root_.SheafOfModules.DifferentialGradedModule.toDerivedCategory.{u, u, u}
    (liftedPowSheafAlgebra f)).map ((HomotopyCategory.quotient (ModuleCat.{u} R)
      (ComplexShape.up ℤ) ⋙ homotopyExtend' (liftedPowSheafAlgebra f)).map g))
  rw [e]
  exact Localization.inverts _ _ _ h

end Koszul
