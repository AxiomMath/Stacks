module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.HomotopyHomIntoPushforwardOfKInjective

/-!
# Postcomposition with a K-injective resolution of the direct image of a K-injective complex

Let `f : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)` be a morphism of ringed topoi, let `I` be a K-injective
complex of `𝒪_C`-modules, let `s : f_* I ⟶ J` be a quasi-isomorphism into a K-injective complex
of `𝒪_D`-modules, and let `P` be an object of the unbounded homotopy category of `𝒪_D`-modules at
which the comparison `Lf^* ⟶ f^*` of Tag 06YY is invertible. This file proves that
postcomposition

`Hom_{K(𝒪_D)}(P, (f_* I)⟦n⟧) ⟶ Hom_{K(𝒪_D)}(P, J⟦n⟧)`

with `s⟦n⟧` is **bijective** for every `n`.

Localization is bijective on both sides: on the right because `J⟦n⟧` is K-injective, on the left
by `bijective_qh_map_pushforward_of_isKInjective`, since `(f_* I)⟦n⟧` is the direct image of the
K-injective complex `I⟦n⟧` — degreewise direct image commutes with the shift, the comparison
having identity components. In the derived category postcomposition with `Q(s⟦n⟧)` is bijective
because `s⟦n⟧` is a quasi-isomorphism, so the fourth side of the square is bijective too.

## Main results

* `bijective_qh_map_shift_pushforward_of_isKInjective`: localization is bijective on morphisms
  into `(f_* I)⟦n⟧`.
* `bijective_postcomp_quotient_shift_of_isKInjective`: the bijectivity of postcomposition.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

namespace Stacks.Cohomology.DerivedPullbackOnRingedTopoi

universe u

/-- Postcomposition with an isomorphism, as a bijection on morphisms out of a fixed object. -/
def postcompIsoEquiv {C : Type*} [Category C] {W W' : C} (e : W ≅ W') (P : C) :
    (P ⟶ W) ≃ (P ⟶ W') where
  toFun a := a ≫ e.hom
  invFun b := b ≫ e.inv
  left_inv a := by simp
  right_inv b := by simp

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedToposSiteHom X Y) (hmos : f.u.IsMorphismOfSites Y.J X.J)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]

omit [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- Bijectivity of localization on morphisms out of `P` transports along an isomorphism of the
target. -/
theorem bijective_qh_map_of_iso
    {P W W' : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ)}
    (e : W ≅ W') (h : Function.Bijective (DerivedCategory.Qh.map : (P ⟶ W') → _)) :
    Function.Bijective (DerivedCategory.Qh.map : (P ⟶ W) → _) := by
  have hcomp : (fun b => b ≫ DerivedCategory.Qh.map e.hom) ∘
        (DerivedCategory.Qh.map : (P ⟶ W) → _) =
      (DerivedCategory.Qh.map : (P ⟶ W') → _) ∘ (fun a : P ⟶ W => a ≫ e.hom) :=
    funext fun a => (DerivedCategory.Qh.map_comp a e.hom).symm
  exact (Function.Bijective.of_comp_iff'
      (postcompIsoEquiv (DerivedCategory.Qh.mapIso e) (DerivedCategory.Qh.obj P)).bijective _).1
    (hcomp ▸ h.comp (postcompIsoEquiv e P).bijective)

/-- Degreewise direct image commutes with the shift: `(f_* I)⟦n⟧` is the direct image of
`I⟦n⟧`. The comparison has identity components. -/
noncomputable abbrev pushforwardShiftIso
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ) :
    (f.pushforwardTopos.mapHomologicalComplex (ComplexShape.up ℤ)).obj (I⟦n⟧) ≅
      ((f.pushforwardTopos.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)⟦n⟧ :=
  ((f.pushforwardTopos.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n).app I

include hmos in
/-- **Localization is bijective on morphisms into `(f_* I)⟦n⟧`.** The shift of the direct image
of a K-injective complex is the direct image of a K-injective complex, so this is
`bijective_qh_map_pushforward_of_isKInjective` at `I⟦n⟧`. -/
theorem bijective_qh_map_shift_pushforward_of_isKInjective
    (P : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))
    [IsIso ((derivedPullbackComparison f).app P)]
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hI : I.IsKInjective) (n : ℤ) :
    Function.Bijective (DerivedCategory.Qh.map :
      (P ⟶ (HomotopyCategory.quotient
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (ComplexShape.up ℤ)).obj
          (((f.pushforwardTopos.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)⟦n⟧)) → _) := by
  have := hI
  exact bijective_qh_map_of_iso
    ((HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (ComplexShape.up ℤ)).mapIso
      (pushforwardShiftIso f I n)).symm
    (bijective_qh_map_pushforward_of_isKInjective f hmos P (I⟦n⟧) inferInstance)

include hmos in
/-- **Postcomposition with a K-injective resolution of `f_* I`, shifted, is bijective.**
Localization is bijective on morphisms into `(f_* I)⟦n⟧` and into `J⟦n⟧`, and in the derived
category postcomposition with `Q(s⟦n⟧)` is bijective because `s⟦n⟧` is a quasi-isomorphism; so
postcomposition with `s⟦n⟧` is bijective in the homotopy category. -/
theorem bijective_postcomp_quotient_shift_of_isKInjective
    (P : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))
    [IsIso ((derivedPullbackComparison f).app P)]
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hI : I.IsKInjective)
    {J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
    (s : (f.pushforwardTopos.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ J)
    (hJ : J.IsKInjective) (hs : QuasiIso s) (n : ℤ) :
    Function.Bijective
      (fun a : P ⟶ (HomotopyCategory.quotient
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
            (ComplexShape.up ℤ)).obj
          (((f.pushforwardTopos.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)⟦n⟧) =>
        a ≫ (HomotopyCategory.quotient
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          (ComplexShape.up ℤ)).map (s⟦n⟧')) := by
  have := hJ
  have := hs
  have : IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          (ComplexShape.up ℤ)).map
        (s⟦n⟧'))) := by
    rw [DerivedCategory.isIso_Qh_map_iff, HomotopyCategory.quotient_map_mem_quasiIso_iff,
      HomologicalComplex.mem_quasiIso_iff]
    infer_instance
  have hleft := bijective_qh_map_shift_pushforward_of_isKInjective f hmos P I hI n
  have hright := CochainComplex.IsKInjective.Qh_map_bijective P (J⟦n⟧)
  have hcomp : (DerivedCategory.Qh.map : (P ⟶ _) → _) ∘
        (fun a : P ⟶ (HomotopyCategory.quotient
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
            (ComplexShape.up ℤ)).obj
            (((f.pushforwardTopos.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)⟦n⟧) =>
          a ≫ (HomotopyCategory.quotient
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
            (ComplexShape.up ℤ)).map (s⟦n⟧')) =
      (fun b => b ≫ DerivedCategory.Qh.map
          ((HomotopyCategory.quotient
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
            (ComplexShape.up ℤ)).map (s⟦n⟧'))) ∘ (DerivedCategory.Qh.map : (P ⟶ _) → _) :=
    funext fun a => DerivedCategory.Qh.map_comp a _
  exact (Function.Bijective.of_comp_iff' hright _).1
    (hcomp ▸ (postcompIsoEquiv (asIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          (ComplexShape.up ℤ)).map
        (s⟦n⟧')))) (DerivedCategory.Qh.obj P)).bijective.comp hleft)

end Stacks.Cohomology.DerivedPullbackOnRingedTopoi

end
