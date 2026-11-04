module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import StacksFrontier.CategoryTheory.Adjunction.LeftAdjointUniqTranspose

/-!
# The unit of the pullback of sheaves of modules, before sheafification

Pullback of sheaves of modules along a continuous functor of sites is the abstract left adjoint
of the pushforward, so its unit is opaque; `SheafOfModules.pullbackIso` identifies
that left adjoint with the concrete composite "underlying presheaf of modules, pullback of
presheaves of modules, sheafification". This file reads the unit through that identification: on
underlying presheaves of modules it is the transpose, along the *presheaf-level*
pullback–pushforward adjunction, of the transpose of the inverse of `SheafOfModules.pullbackIso`
along the sheafification adjunction.

That is the form in which a computation with the unit can proceed, because both of those
transposes are concrete, whereas the unit itself is `CategoryTheory.Adjunction.ofIsRightAdjoint`
of an existence statement.

## Main results

* `SheafOfModules.pullbackPushforwardAdjunction_unit_app_val`: the unit of the pullback of
  sheaves of modules, read on underlying presheaves of modules as the transpose described above.

## Implementation notes

The proof is `CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_hom_app_comp` for the two
adjunctions `SheafOfModules.pullbackIso` compares — the abstract one and
`SheafOfModules.PullbackConstruction.adjunction` — at the inverse of the
comparison, which turns the unit into the concrete adjunction's transpose of the inverse;
the concrete adjunction is a `CategoryTheory.Adjunction.mkOfHomEquiv` whose hom bijection is the
composite of the three concrete ones, and `CategoryTheory.Adjunction.mkOfHomEquiv_homEquiv` reads
it off.

The two hom-set bijections of `CategoryTheory.Functor.FullyFaithful.homEquiv` have to have their
object arguments supplied by name. The target of the unit is `(pushforward φ).obj` of the
pullback, and the target of the composite bijection is the *presheaf-level* pushforward of the
underlying presheaf of modules; those are the same term, but unifying them from the shape of the
bijection is what the elaborator cannot do, and it reports the universe-annotated `Functor.obj`
mismatch rather than unfolding.

## References

* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u v₁ u₁ v₂ u₂

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
  [(PresheafOfModules.pushforward.{v} φ.hom).IsRightAdjoint]
  [HasWeakSheafify K AddCommGrpCat.{v}] [K.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- **The unit of `f^* ⊣ f_*` for sheaves of modules, on underlying presheaves of modules.** It
is the transpose, along the presheaf-level pullback–pushforward adjunction, of the transpose along
the sheafification adjunction of the inverse of `SheafOfModules.pullbackIso`.

Both of those transposes are concrete, whereas the unit itself is the unit of the abstract left
adjoint; this is what makes a computation with the unit possible. -/
theorem pullbackPushforwardAdjunction_unit_app_val (X : _root_.SheafOfModules.{v} S) :
    ((pullbackPushforwardAdjunction.{v} φ).unit.app X).val =
      (PresheafOfModules.pullbackPushforwardAdjunction.{v} φ.hom).homEquiv X.val
        ((pullback.{v} φ).obj X).val
        ((PresheafOfModules.sheafificationAdjunction.{v} (𝟙 R.obj)).homEquiv _ _
          ((pullbackIso.{v} φ).inv.app X)) := by
  have h1 : (pullbackPushforwardAdjunction.{v} φ).unit.app X =
      (PullbackConstruction.adjunction.{v} φ).homEquiv X ((pullback.{v} φ).obj X)
        ((pullbackIso.{v} φ).inv.app X) :=
    (Adjunction.homEquiv_id (pullbackPushforwardAdjunction.{v} φ) X).symm.trans
      ((congrArg ((pullbackPushforwardAdjunction.{v} φ).homEquiv X ((pullback.{v} φ).obj X))
          ((pullbackIso.{v} φ).hom_inv_id_app X).symm).trans
        (Adjunction.homEquiv_leftAdjointUniq_hom_app_comp
          (pullbackPushforwardAdjunction.{v} φ) (PullbackConstruction.adjunction.{v} φ)
          ((pullbackIso.{v} φ).inv.app X)))
  have h2 : (PullbackConstruction.adjunction.{v} φ).homEquiv X ((pullback.{v} φ).obj X)
        ((pullbackIso.{v} φ).inv.app X) =
      ((fullyFaithfulForget.{v} S).homEquiv
        (Y := (pushforward.{v} φ).obj ((pullback.{v} φ).obj X))).symm
        ((PresheafOfModules.pullbackPushforwardAdjunction.{v} φ.hom).homEquiv X.val
          ((pullback.{v} φ).obj X).val
          ((PresheafOfModules.sheafificationAdjunction.{v} (𝟙 R.obj)).homEquiv _ _
            ((pullbackIso.{v} φ).inv.app X))) :=
    congrArg (fun e : ((forget.{v} S ⋙ PresheafOfModules.pullback.{v} φ.hom ⋙
            PresheafOfModules.sheafification.{v} (R₀ := R.obj) (𝟙 R.obj)).obj X ⟶
          (pullback.{v} φ).obj X) ≃ (X ⟶ (pushforward.{v} φ).obj ((pullback.{v} φ).obj X)) =>
        e ((pullbackIso.{v} φ).inv.app X))
      (congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv _) X) ((pullback.{v} φ).obj X))
  refine Eq.trans (congrArg
    (fun z : X ⟶ (pushforward.{v} φ).obj ((pullback.{v} φ).obj X) => z.val) (h1.trans h2)) ?_
  exact (fullyFaithfulForget.{v} S).map_preimage (X := X)
      (Y := (pushforward.{v} φ).obj ((pullback.{v} φ).obj X))
    ((PresheafOfModules.pullbackPushforwardAdjunction.{v} φ.hom).homEquiv X.val
      ((pullback.{v} φ).obj X).val
      ((PresheafOfModules.sheafificationAdjunction.{v} (𝟙 R.obj)).homEquiv _ _
        ((pullbackIso.{v} φ).inv.app X)))

end SheafOfModules

end
