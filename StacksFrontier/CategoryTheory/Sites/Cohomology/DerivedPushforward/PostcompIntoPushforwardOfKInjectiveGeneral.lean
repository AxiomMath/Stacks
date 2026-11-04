module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.PostcompIntoPushforwardOfKInjective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.HomotopyHomIntoPushforwardOfKInjective
import all StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.PostcompIntoPushforwardOfKInjective

/-!
# Localization on morphisms and isomorphisms of the target

For an abelian category `A`, bijectivity of the localization functor
`DerivedCategory.Qh` on morphisms `P ⟶ W` in the homotopy category is invariant under
isomorphisms `W ≅ W'` of the target.

## Main results

* `bijective_qh_map_of_iso_general`: if `DerivedCategory.Qh.map` is bijective on morphisms
  `P ⟶ W'` and `W ≅ W'`, then it is bijective on morphisms `P ⟶ W`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

namespace Stacks.Cohomology.DerivedPullbackOnRingedTopoi

universe u

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

/-- Bijectivity of localization on morphisms out of `P` transports along an isomorphism of the
target, in the homotopy category of any abelian category. -/
theorem bijective_qh_map_of_iso_general {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    {P W W' : HomotopyCategory A (ComplexShape.up ℤ)}
    (e : W ≅ W') (h : Function.Bijective (DerivedCategory.Qh.map : (P ⟶ W') → _)) :
    Function.Bijective (DerivedCategory.Qh.map : (P ⟶ W) → _) := by
  have hcomp : (fun b => b ≫ DerivedCategory.Qh.map e.hom) ∘
        (DerivedCategory.Qh.map : (P ⟶ W) → _) =
      (DerivedCategory.Qh.map : (P ⟶ W') → _) ∘ (fun a : P ⟶ W => a ≫ e.hom) :=
    funext fun a => (DerivedCategory.Qh.map_comp a e.hom).symm
  exact (Function.Bijective.of_comp_iff'
      (postcompIsoEquiv (DerivedCategory.Qh.mapIso e) (DerivedCategory.Qh.obj P)).bijective _).1
    (hcomp ▸ h.comp (postcompIsoEquiv e P).bijective)

end Stacks.Cohomology.DerivedPullbackOnRingedTopoi

end
