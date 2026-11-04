module

public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective

/-!
# The unit of a right derived functor, read off one K-injective resolution

Let `F` be a functor out of the unbounded homotopy category of an abelian category with enough
K-injective complexes, let `RF` be a right derived functor of `F` and let `α : F ⟶ L ⋙ RF` be
its unit. Stacks 070K says that `α` is invertible at the class of a K-injective complex. The
statement proved here is the consequence one uses to compute `RF` at an arbitrary complex `M`:
if some quasi-isomorphism `q : M ⟶ J` into a K-injective complex has `F(q)` invertible, then `α`
is invertible at the class of `M` as well.

This turns `F(M) = RF(M)` into a statement about one chosen resolution, which is how the
comparison between a direct image and its derived functor is actually established.

## Main results

* `CategoryTheory.Functor.isIso_rightDerivedUnit_app_of_quasiIso`: the criterion.

## Implementation notes

The hypothesis on `F` is the one of Stacks 070K, that every complex admits a quasi-isomorphism
into a K-injective one; it is passed as an argument rather than deduced from a Grothendieck
abelian structure, so that the statement applies verbatim in the two places the project needs it
and does not force a `IsGrothendieckAbelian` instance into contexts that only have the
resolutions.

The proof is the naturality square of `α` at the class of `q`. Its lower edge is invertible
because the localization functor inverts a quasi-isomorphism, its right edge is `α` at the
K-injective complex `J`, and its upper edge is invertible by hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor

/-- **The unit of a right derived functor is invertible wherever one resolution is sent to an
isomorphism.** If `q : M ⟶ J` is a quasi-isomorphism into a K-injective complex and `F` sends
the class of `q` to an isomorphism, then the unit `α` of a right derived functor of `F` is
invertible at the class of `M`. -/
theorem isIso_rightDerivedUnit_app_of_quasiIso
    {A : Type u₁} [Category.{v₁} A] [Abelian A] {H : Type u₂} [Category.{v₂} H]
    (F : HomotopyCategory A (ComplexShape.up ℤ) ⥤ H)
    (hA : ∀ X : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : X ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    {D : Type u₃} [Category.{v₃} D] (L : HomotopyCategory A (ComplexShape.up ℤ) ⥤ D)
    [L.IsLocalization (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (RF : D ⥤ H) (α : F ⟶ L ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    {M J : CochainComplex A ℤ} (hJ : J.IsKInjective) (q : M ⟶ J) (hq : QuasiIso q)
    (hF : IsIso (F.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map q))) :
    IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj M)) := by
  have hαJ : IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj J)) :=
    (hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      F hA).2 L RF α J hJ
  have hL : IsIso (L.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map q)) := by
    apply Localization.inverts L (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
    rwa [HomotopyCategory.quotient_map_mem_quasiIso_iff]
  have hLRF : IsIso ((L ⋙ RF).map
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map q)) := by
    rw [Functor.comp_map]
    have := hL
    infer_instance
  have hnat := α.naturality ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map q)
  have hcomp : IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj M) ≫
      (L ⋙ RF).map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map q)) := by
    rw [← hnat]
    have := hF
    have := hαJ
    infer_instance
  have := hLRF
  have := hcomp
  exact IsIso.of_isIso_comp_right
    (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj M))
    ((L ⋙ RF).map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map q))

end CategoryTheory.Functor

end
