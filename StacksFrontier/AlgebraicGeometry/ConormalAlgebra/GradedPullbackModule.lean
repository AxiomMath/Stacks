module

public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.GradedPullback
public import StacksFrontier.AlgebraicGeometry.PullbackTensor.GradedModule

/-!
# Pullback of a right graded module along a morphism of schemes

`Stacks.RingedSpace.pullbackGradedModule` pulls a right graded module over a sheaf of graded
algebras back along a morphism of ringed spaces. This file reads that construction in the
vocabulary of schemes, over `Stacks.Conormal.gradedPullback`, and adds that the pieces stay
quasi-coherent ([Stacks, Tag 01BG]) and that vanishing pieces stay vanishing.

For a closed immersion `i : Z ⟶ X` cut out by a quasi-coherent sheaf of ideals `ℐ`, applying
this to the Rees module `⨁ₙ ℐⁿℱ` of `Stacks.Blowup.reesGradedModule` gives
`⨁ₙ ℐⁿℱ/ℐⁿ⁺¹ℱ` as a graded module over the conormal algebra `⨁ₙ ℐⁿ/ℐⁿ⁺¹`: the pullback along a
closed immersion of a quasi-coherent module is its quotient by the ideal
(`Stacks.Conormal.pullbackSection_eq_zero_iff`), and `ℐ · ℐⁿℱ = ℐⁿ⁺¹ℱ`.

## Main definitions

* `Stacks.Conormal.gradedPullbackModule`: the pullback of a right graded module along a
  morphism of schemes, a right graded module over the pulled-back graded algebra.

## Main results

* `Stacks.Conormal.gradedPullbackModule_isQuasicoherent`: the pieces of the pullback are
  quasi-coherent as soon as those of the module are.
* `Stacks.Conormal.gradedPullbackModule_negative_isZero`: the pullback of a nonnegatively
  graded module is nonnegatively graded.
* `Stacks.Conormal.gradedPullbackModule_smul_pullbackSection`: **the pulled-back action on
  pulled-back sections** is the pullback of the action.

## References

* [Stacks Project, Tag 0FQZ](https://stacks.math.columbia.edu/tag/0FQZ)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.Conormal

variable {Z X : Scheme.{u}} (g : Z ⟶ X) {A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf}

/-- **The pullback of a right graded module along a morphism of schemes.** -/
noncomputable def gradedPullbackModule (M : SheafOfModules.GradedModule.{u, u, u} A) :
    SheafOfModules.GradedModule.{u, u, u} (gradedPullback g A) :=
  Stacks.RingedSpace.pullbackGradedModule g.toLRSHom.toShHom A M

/-- The degree `n` piece of the pullback is the pullback of the degree `n` piece. -/
@[simp] lemma gradedPullbackModule_piece (M : SheafOfModules.GradedModule.{u, u, u} A) (n : ℤ) :
    (gradedPullbackModule g M).piece n = (Scheme.Modules.pullback g).obj (M.piece n) :=
  rfl

/-- The pieces of the pullback are quasi-coherent as soon as those of the module are. This is
[Stacks, Tag 01BG]. -/
lemma gradedPullbackModule_isQuasicoherent (M : SheafOfModules.GradedModule.{u, u, u} A)
    (hM : ∀ n : ℤ, (M.piece n).IsQuasicoherent) (n : ℤ) :
    ((gradedPullbackModule g M).piece n).IsQuasicoherent :=
  have := hM n
  Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback g (M.piece n)

/-- A piece of the pullback is zero wherever the corresponding piece is. -/
lemma gradedPullbackModule_isZero (M : SheafOfModules.GradedModule.{u, u, u} A) {n : ℤ}
    (hn : Limits.IsZero (M.piece n)) : Limits.IsZero ((gradedPullbackModule g M).piece n) :=
  (Scheme.Modules.pullback g).map_isZero hn

/-- The pullback of a nonnegatively graded module is nonnegatively graded. -/
lemma gradedPullbackModule_negative_isZero (M : SheafOfModules.GradedModule.{u, u, u} A)
    (hM : ∀ n : ℤ, n < 0 → Limits.IsZero (M.piece n)) (n : ℤ) (hn : n < 0) :
    Limits.IsZero ((gradedPullbackModule g M).piece n) :=
  gradedPullbackModule_isZero g M (hM n hn)

/-- **The pulled-back action on pulled-back sections.** The action of the pullback of a
homogeneous section of the algebra on the pullback of a homogeneous section of the module, over
the whole preimage of an open `U`, is the pullback of the action. -/
lemma gradedPullbackModule_smul_pullbackSection (M : SheafOfModules.GradedModule.{u, u, u} A)
    (n i : ℤ) (U : X.Opens) (x : (M.piece n).val.obj (op U)) (a : (A.piece i).val.obj (op U)) :
    (gradedPullbackModule g M).smul n i (op (g ⁻¹ᵁ U))
        (Scheme.Modules.pullbackSection g (M.piece n) U (g ⁻¹ᵁ U) le_rfl x)
        (Scheme.Modules.pullbackSection g (A.piece i) U (g ⁻¹ᵁ U) le_rfl a) =
      Scheme.Modules.pullbackSection g (M.piece (n + i)) U (g ⁻¹ᵁ U) le_rfl
        (M.smul n i (op U) x a) := by
  rw [pullbackSection_self g (M.piece n) U x, pullbackSection_self g (A.piece i) U a,
    pullbackSection_self g (M.piece (n + i)) U (M.smul n i (op U) x a)]
  exact Stacks.RingedSpace.pullbackGradedModule_smul_pullbackUnit g.toLRSHom.toShHom A M
    n i U x a

end Stacks.Conormal

end
