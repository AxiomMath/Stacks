module

public import StacksFrontier.CategoryTheory.Sites.SliceTopos.SubterminalSliceSheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The lower shriek of the slice at a subterminal sheaf

Let `F` be a sheaf of sets with subsingleton values on a site `(C, J)` and let `j : D ⥤ C` be a
fully faithful continuous functor whose essential image is the support of `F` and whose covering
sieves are exactly the sieves whose image covers, so that
`CategoryTheory.Stacks.Topos.Subterminal.sliceEquivalence` identifies `Sh(D)` with the slice
`Sh(C)/F`.  This file records the last assertion of [Stacks, Tag 0791] in that situation: the
composite of that equivalence with the forgetful functor of the slice — the functor `j_!` — is
left adjoint to restriction `j^{-1}` along `j`.

The adjunction is built from one bijection, `Subterminal.forgetHomEquiv`: for a sheaf `T` over
`F` and an arbitrary sheaf `P` on `C`, restriction along `j` is a bijection from the morphisms
`T ⟶ P` of `Sh(C)` to the morphisms `j^{-1}T ⟶ j^{-1}P` of `Sh(D)`.  It is injective because
`T` has no sections outside the essential image of `j`, and surjective because
`Subterminal.extendNatTrans` extends a morphism defined over that image; those are the two
halves of `faithful_sliceRestriction` and `full_sliceRestriction` read with an arbitrary target
in place of a second sheaf over `F`.

## Main definitions

* `CategoryTheory.Stacks.Topos.Subterminal.forgetHomEquiv` — restriction along `j` is a
  bijection on morphisms out of a sheaf over `F`.
* `CategoryTheory.Stacks.Topos.Subterminal.shriekAdjunction` — **[Stacks, Tag 0791]**, the last
  assertion: `j_! ⊣ j^{-1}`.

## References

* [Stacks Project, Tag 0791](https://stacks.math.columbia.edu/tag/0791)
-/

@[expose] public section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Stacks.Topos.Subterminal

open Opposite

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : Cᵒᵖ ⥤ Type w} {j : D ⥤ C} [j.Full] [j.Faithful]
  [∀ X : Cᵒᵖ, Subsingleton (F.obj X)]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} [j.IsContinuous K J]
  (hsupp : ∀ U : C, Nonempty (F.obj (op U)) → j.essImage U)
  (hmem : ∀ B : D, Nonempty (F.obj (op (j.obj B))))
  (hF : Presheaf.IsSheaf J F)

/-- **Restriction along `j` is a bijection on the morphisms out of a sheaf over `F`.**  A sheaf
`T` over `F` has no sections outside the essential image of `j`, so a morphism `T ⟶ P` into an
arbitrary sheaf on `C` is determined by its restriction along `j`, and every morphism of the
restrictions extends — there is no condition to check against `F`, the target `P` carrying none.

This is `faithful_sliceRestriction` and `full_sliceRestriction` with the second sheaf over `F`
replaced by an arbitrary sheaf on `C`; it is what makes the forgetful functor of the slice a
left adjoint to restriction. -/
noncomputable def forgetHomEquiv (T : Over (⟨F, hF⟩ : Sheaf J (Type w)))
    (P : Sheaf J (Type w)) :
    (T.left ⟶ P) ≃
      ((j.sheafPushforwardContinuous (Type w) K J).obj T.left ⟶
        (j.sheafPushforwardContinuous (Type w) K J).obj P) where
  toFun α := (j.sheafPushforwardContinuous (Type w) K J).map α
  invFun γ := Sheaf.homEquiv.symm (extendNatTrans T.left.obj P.obj
    (fun U t ↦ essImage_of_over hsupp hF T U t) (Sheaf.homEquiv γ))
  left_inv α := by
    apply Sheaf.homEquiv.injective
    refine natTrans_ext_of_essImage
      (fun {U} t ↦ essImage_of_over hsupp hF T (op U) t) fun B ↦ ?_
    exact congrArg (fun m ↦ NatTrans.app m (op B))
      (whiskerLeft_extendNatTrans T.left.obj P.obj
        (fun U t ↦ essImage_of_over hsupp hF T U t) (Sheaf.homEquiv ((j.sheafPushforwardContinuous
          (Type w) K J).map α)))
  right_inv γ := Sheaf.homEquiv.injective <| whiskerLeft_extendNatTrans T.left.obj P.obj
    (fun U t ↦ essImage_of_over hsupp hF T U t) (Sheaf.homEquiv γ)

variable (hcover : ∀ (A : D) (T : Sieve A), T ∈ K A ↔ T.functorPushforward j ∈ J (j.obj A))

include hsupp hmem hcover in
/-- The transposition bijection of the adjunction `j_! ⊣ j^{-1}`: restrict along `j` and
transport back along the unit of the slice equivalence. -/
noncomputable def shriekHomEquiv (H : Sheaf K (Type w)) (P : Sheaf J (Type w)) :
    (((sliceEquivalence hsupp hmem hF hcover).functor ⋙
          Over.forget (⟨F, hF⟩ : Sheaf J (Type w))).obj H ⟶ P) ≃
      (H ⟶ (j.sheafPushforwardContinuous (Type w) K J).obj P) :=
  (forgetHomEquiv (K := K) hsupp hF
      ((sliceEquivalence hsupp hmem hF hcover).functor.obj H) P).trans
    (Iso.homFromEquiv ((sliceEquivalence hsupp hmem hF hcover).unitIso.app H).symm)

include hsupp hmem hcover in
/-- Transposing a morphism out of `j_!H` is restricting it along `j` and composing with the
unit of the slice equivalence. -/
theorem shriekHomEquiv_apply (H : Sheaf K (Type w)) (P : Sheaf J (Type w))
    (α : ((sliceEquivalence hsupp hmem hF hcover).functor ⋙
      Over.forget (⟨F, hF⟩ : Sheaf J (Type w))).obj H ⟶ P) :
    shriekHomEquiv hsupp hmem hF hcover H P α =
      (sliceEquivalence hsupp hmem hF hcover).unitIso.hom.app H ≫
        (j.sheafPushforwardContinuous (Type w) K J).map α :=
  rfl

include hsupp hmem hcover in
/-- The inverse transposition, spelled through `forgetHomEquiv`. -/
theorem shriekHomEquiv_symm_apply (H : Sheaf K (Type w)) (P : Sheaf J (Type w))
    (β : H ⟶ (j.sheafPushforwardContinuous (Type w) K J).obj P) :
    (shriekHomEquiv hsupp hmem hF hcover H P).symm β =
      (forgetHomEquiv (K := K) hsupp hF
          ((sliceEquivalence hsupp hmem hF hcover).functor.obj H) P).symm
        ((sliceEquivalence hsupp hmem hF hcover).unitIso.inv.app H ≫ β) :=
  rfl

include hsupp hmem hcover in
/-- **[Stacks, Tag 0791] for a subterminal sheaf, the last assertion.**  The functor `j_!` — the
slice equivalence followed by the forgetful functor of the slice — is left adjoint to restriction
`j^{-1}` along `j`.

This is the analogue, in an arbitrary coefficient universe, of
`CategoryTheory.Stacks.Topos.Localized.shriekAdjunction`, and it is what identifies the arrow
`Sh(D) ⟶ Sh(C)` of the slice presentation with the localization morphism `j_F` of
[Stacks, Tag 04H1].

No attribute is placed here, as none is on `sliceEquivalence`: the covering set of
[Stacks, Tag 0791] is the general statement in
`StacksFrontier/CategoryTheory/Sites/Topos/LocalizationOfTopoi.lean`, of which this is the
subterminal special case, available where the general one is not for want of a universe. -/
@[sga "4 III 5.4" "special case"]
noncomputable def shriekAdjunction :
    (sliceEquivalence hsupp hmem hF hcover).functor ⋙
        Over.forget (⟨F, hF⟩ : Sheaf J (Type w)) ⊣
      j.sheafPushforwardContinuous (Type w) K J :=
  Adjunction.mkOfHomEquiv
    { homEquiv := shriekHomEquiv hsupp hmem hF hcover
      homEquiv_naturality_left_symm := fun {H' H P} f β ↦ by
        apply (forgetHomEquiv (K := K) hsupp hF
          ((sliceEquivalence hsupp hmem hF hcover).functor.obj H') P).injective
        rw [shriekHomEquiv_symm_apply, Equiv.apply_symm_apply]
        change _ = (j.sheafPushforwardContinuous (Type w) K J).map
          (((sliceEquivalence hsupp hmem hF hcover).functor ⋙
            Over.forget (⟨F, hF⟩ : Sheaf J (Type w))).map f ≫
              (shriekHomEquiv hsupp hmem hF hcover H P).symm β)
        rw [Functor.map_comp]
        change _ = _ ≫ forgetHomEquiv (K := K) hsupp hF
          ((sliceEquivalence hsupp hmem hF hcover).functor.obj H) P
            ((shriekHomEquiv hsupp hmem hF hcover H P).symm β)
        rw [shriekHomEquiv_symm_apply, Equiv.apply_symm_apply]
        have hnat := (sliceEquivalence hsupp hmem hF hcover).unitIso.inv.naturality f
        exact ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ β) hnat).trans (Category.assoc _ _ _))).symm
      homEquiv_naturality_right := fun {H P P'} α g ↦ by
        rw [shriekHomEquiv_apply, shriekHomEquiv_apply, Functor.map_comp]
        exact (Category.assoc _ _ _).symm }

end Stacks.Topos.Subterminal

end CategoryTheory

end
