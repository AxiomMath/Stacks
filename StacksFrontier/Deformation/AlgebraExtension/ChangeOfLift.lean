module

public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangentExtClass
public import StacksFrontier.Deformation.AlgebraExtension.Generators
import all StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangentExtClass

/-!
# Changing the lift of the generators

Let `α : ℰ ⟶ 𝒪` be a family of generators of `𝒪` over `𝒜` and let `β, β'` be two lifts of `α`
to an extension `Q` of `𝒜`-algebras of `𝒪` by `𝒩`. The two homomorphisms `𝒜[ℰ] ⟶ 𝒪'_Q` they
determine differ by a derivation of `𝒜[ℰ]` over `𝒜` with values in the square-zero ideal `𝒩`,
so — the degree `0` term `Ω = 𝒪 ⊗ Ω_{𝒜[ℰ]/𝒜}` of `NL(α)` being the free `𝒪`-module on `ℰ` —
there is a morphism `θ : Ω ⟶ 𝒩` with `β'(y) - β(y) = θ(1 ⊗ d y)` for every local section `y`.
On the relations `ℐ` this says that the two restrictions differ by `θ ∘ d`.

## Main results

* `Deformation.AlgebraExtension.GeneratorLift.exists_tensorHom_sub`: the morphism `θ`.
* `Deformation.AlgebraExtension.GeneratorLift.exists_tensorHom_restriction_sub`: its effect on the
  restrictions to the relations.

## References

* [Stacks Project, Tag 08UG](https://stacks.math.columbia.edu/tag/08UG)
* [Stacks Project, Tag 08UJ](https://stacks.math.columbia.edu/tag/08UJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.Differentials (underlyingRingSheaf)
open Stacks.Sites.Conormal (kernelIdeal tensorDifferential sectionsLeibnizDerivation
  underlyingRingHomForPullback)
open Stacks.Sites.FreeAlgebra
open Stacks.SheafOfModules (presentation presentationConormalSequence)

universe u

namespace Deformation.AlgebraExtension.GeneratorLift

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] [HasWeakSheafify J CommRingCat.{u}]
  {A O : Sheaf J CommRingCat.{u}} {a : A ⟶ O}
  {N : SheafOfModules.{u} (underlyingRingSheaf O)}
  {E : Cᵒᵖ ⥤ Type u} {α : E ⟶ underlyingPresheaf J O}
  {Q : AlgebraExtension a N} (β β' : GeneratorLift α Q)

/-- A lift reduces to the presentation map `𝒜[ℰ] ⟶ 𝒪` on local sections. -/
private theorem reduction_hom_app (U : Cᵒᵖ) (y : (freeAlgebraSheaf J A E).obj.obj U) :
    Q.reduction.hom.app U (β.hom.hom.app U y) = (presentation J A O a E α).hom.app U y :=
  congrArg (fun t : freeAlgebraSheaf J A E ⟶ O => t.hom.app U y) β.hom_reduction

/-- Two lifts reduce to the same section of `𝒪`. -/
theorem reduction_hom_sub (U : Cᵒᵖ) (y : (freeAlgebraSheaf J A E).obj.obj U) :
    Q.reduction.hom.app U (β'.hom.hom.app U y - β.hom.hom.app U y) = 0 := by
  rw [map_sub, β.reduction_hom_app, β'.reduction_hom_app, sub_self]

/-- **The difference of two lifts**, as a section of the square-zero ideal `𝒩`. -/
noncomputable def diff (U : Cᵒᵖ) (y : (freeAlgebraSheaf J A E).obj.obj U) : N.val.obj U :=
  Q.kernelPreimage ⟨β'.hom.hom.app U y - β.hom.hom.app U y, β.reduction_hom_sub β' U y⟩

/-- The image of `diff β β' U y` in `𝒪'_Q` is `β'(y) - β(y)`. -/
theorem incl_diff (U : Cᵒᵖ) (y : (freeAlgebraSheaf J A E).obj.obj U) :
    Q.incl (β.diff β' U y) = β'.hom.hom.app U y - β.hom.hom.app U y :=
  Q.incl_kernelPreimage _

/-- A section `n` of `𝒩` whose image in `𝒪'_Q` is `β'(y) - β(y)` is `diff β β' U y`. -/
theorem diff_eq (U : Cᵒᵖ) (y : (freeAlgebraSheaf J A E).obj.obj U) (n : N.val.obj U)
    (h : Q.incl n = β'.hom.hom.app U y - β.hom.hom.app U y) : β.diff β' U y = n :=
  Q.kernelPreimage_eq _ n h

variable [Presheaf.IsLocallySurjective J (presentation J A O a E α).hom]

/-- **The difference of two lifts is a derivation** of `𝒜[ℰ]` over `𝒜` with values in `𝒩`. -/
noncomputable def diffDerivation :
    ((_root_.SheafOfModules.pushforward
      (underlyingRingHomForPullback J (freeAlgebraSheaf J A E) O
        (presentation J A O a E α))).obj N).val.Derivation'
      (freeAlgebraSheafCoefficientMap J A E).hom :=
  sectionsLeibnizDerivation.{u, u, u, u} J A (freeAlgebraSheaf J A E) O
    (freeAlgebraSheafCoefficientMap J A E) (presentation J A O a E α) N (β.diff β')
    (fun U y z => β.diff_eq β' U _ _ (by
      rw [Q.incl_add, β.incl_diff, β.incl_diff, map_add, map_add]
      abel))
    (fun U y z => β.diff_eq β' U _ _ (by
      have hy := congrArg (fun t : freeAlgebraSheaf J A E ⟶ O => t.hom.app U y) β.hom_reduction
      have hz := congrArg (fun t : freeAlgebraSheaf J A E ⟶ O => t.hom.app U z) β'.hom_reduction
      dsimp only at hy hz
      rw [Q.incl_add]
      change Q.incl (scalar ((presentation J A O a E α).hom.app U y) • β.diff β' U z) +
        Q.incl (scalar ((presentation J A O a E α).hom.app U z) • β.diff β' U y) = _
      rw [← hy, ← hz]
      change Q.incl (scalar (Q.reduction.hom.app U (β.hom.hom.app U y)) • β.diff β' U z) +
        Q.incl (scalar (Q.reduction.hom.app U (β'.hom.hom.app U z)) • β.diff β' U y) = _
      rw [← Q.mul_incl, ← Q.mul_incl, β.incl_diff, β.incl_diff, map_mul, map_mul]
      ring))
    (fun U r => β.diff_eq β' U _ _ (by
      have h1 := congrArg (fun t : A ⟶ Q.extension => t.hom.app U r) β.coefficientMap_hom
      have h2 := congrArg (fun t : A ⟶ Q.extension => t.hom.app U r) β'.coefficientMap_hom
      dsimp only at h1 h2
      rw [Q.incl_zero]
      change 0 = (freeAlgebraSheafCoefficientMap J A E ≫ β'.hom).hom.app U r -
        (freeAlgebraSheafCoefficientMap J A E ≫ β.hom).hom.app U r
      rw [h1, h2, sub_self]))
    (fun U V f y => β.diff_eq β' V _ _ (by
      refine (Q.incl_naturality f (β.diff β' U y)).trans ?_
      rw [β.incl_diff, map_sub, NatTrans.naturality_apply β'.hom.hom,
        NatTrans.naturality_apply β.hom.hom]))

omit [Presheaf.IsLocallySurjective J (presentation J A O a E α).hom] in
/-- The derivation `diffDerivation β β'` sends a local section `y` of `𝒜[ℰ]` to `diff β β' U y`. -/
theorem diffDerivation_d (U : Cᵒᵖ) (y : (freeAlgebraSheaf J A E).obj.obj U) :
    (β.diffDerivation β').d y = β.diff β' U y :=
  rfl

/-- The difference of two lifts, as a map of presheaves of sets `𝒜[ℰ] ⟶ 𝒩`. -/
noncomputable def diffPresheafMap :
    underlyingPresheaf J (freeAlgebraSheaf J A E) ⟶ N.val.presheaf ⋙ forget AddCommGrpCat.{u} where
  app U := TypeCat.ofHom (β.diff β' U)
  naturality U V f := by
    ext y
    exact (β.diffDerivation β').d_map f y

variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective CommRingCat.{u}]

omit [HasSheafify J AddCommGrpCat.{u}] in
/-- **Two lifts differ by a morphism out of the degree `0` term of `NL(α)`**: there is
`θ : 𝒪 ⊗ Ω_{𝒜[ℰ]/𝒜} ⟶ 𝒩` with `β'(y) - β(y) = θ(1 ⊗ d y)` for every local section `y` of
`𝒜[ℰ]`. -/
theorem exists_tensorHom_sub :
    ∃ θ : (presentationConormalSequence.{u, u, u, u} J A O a E α).X₂ ⟶ N,
      ∀ (U : Cᵒᵖ) (y : (freeAlgebraSheaf J A E).obj.obj U),
        θ.val.app U (tensorDifferential.{u, u, u, u} J A (freeAlgebraSheaf J A E) O
          (freeAlgebraSheafCoefficientMap J A E) (presentation J A O a E α) U y) =
          β.diff β' U y := by
  have : Presheaf.IsLocallySurjective J
      ((toSheafification J CommRingCat.{u}).app (polynomialPresheaf J A E)) :=
    (J.W_toSheafify _).isLocallySurjective
  obtain ⟨θ, hθ⟩ := Stacks.SheafOfModules.exists_tensorHom_on_generators.{u, u, u} J A O a E α
    N (freeAlgebraSheafVariable J A E ≫ β.diffPresheafMap β')
  refine ⟨θ, fun U y => ?_⟩
  have hEq : Stacks.SheafOfModules.tensorHomEquivDerivation.{u, u, u} J A O a E α N θ =
      β.diffDerivation β' :=
    Stacks.SheafOfModules.freeAlgebraSheafDerivation_ext J A E _ _ _ fun V e =>
      (Stacks.SheafOfModules.tensorHomEquivDerivation_d.{u, u, u} J A O a E α N θ V _).trans
        (hθ V e)
  exact (Stacks.SheafOfModules.tensorHomEquivDerivation_d.{u, u, u} J A O a E α N θ U y).symm.trans
    (congrArg (fun D : ((_root_.SheafOfModules.pushforward
        (underlyingRingHomForPullback J (freeAlgebraSheaf J A E) O
          (presentation J A O a E α))).obj N).val.Derivation'
        (freeAlgebraSheafCoefficientMap J A E).hom => D.d (X := U) y) hEq)

omit [HasSheafify J AddCommGrpCat.{u}] in
/-- **The change-of-lift formula on the relations**: the restrictions of two lifts to the
relations `ℐ` differ by `θ ∘ d`, the differential of `NL(α)` followed by a morphism out of its
degree `0` term. -/
theorem exists_tensorHom_restriction_sub :
    ∃ θ : (presentationConormalSequence.{u, u, u, u} J A O a E α).X₂ ⟶ N,
      ∀ (U : Cᵒᵖ) (g : kernelIdeal (presentation J A O a E α).hom U),
        β'.restriction U g = β.restriction U g +
          θ.val.app U (((presentationConormalSequence.{u, u, u, u} J A O a E α).f.val.app U)
            (Stacks.Sites.Conormal.conormalClass.{u, u, u, u} J A (freeAlgebraSheaf J A E) O
              (freeAlgebraSheafCoefficientMap J A E) (presentation J A O a E α) U g)) := by
  obtain ⟨θ, hθ⟩ := β.exists_tensorHom_sub β'
  refine ⟨θ, fun U g => Q.incl_injective ?_⟩
  rw [Stacks.Sites.Conormal.conormalSequence_f_class, hθ, Q.incl_add, β.incl_diff,
    incl_restriction, incl_restriction]
  abel

end Deformation.AlgebraExtension.GeneratorLift

end
