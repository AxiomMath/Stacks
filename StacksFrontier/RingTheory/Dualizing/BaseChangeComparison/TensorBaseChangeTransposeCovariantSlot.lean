module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeTransposeKFlat

/-!
# The [stacks 068I] candidate's transpose, with the tensor base-change isomorphism in the
covariant slot

`Dualizing.tensorBaseChangeMor_transpose_eq_q_obj` values the [stacks 0A63] transpose over `A` of
the [stacks 068I] candidate at a pair of localizations of K-flat complexes: it is the transpose of
the tensor of the two model comparisons, the K-flat representation of the derived tensor product
over `A` and the ordinary tensor base-change isomorphism `e` of total complexes, followed by the
internal Hom of the inverse of `Stacks.DerivedHom.BaseChange.tensorKFlatComparisonIso`.  There `e`
stands *inside* the transpose, as the last factor of the transposed argument.

The two lemmas that move an occurrence of `e` out of the keystone's [stacks 0E1W] prefix --
`Stacks.DerivedHom.BaseChange.functor_map_comp_hom_map_comp_counit` and
`Stacks.DerivedHom.BaseChange.functor_map_comp_tensorKFlatKInjectiveLift_hom` -- both read it in
the *covariant slot* of the transported internal Hom over `A`, the first as the morphism `γ` it
takes out of the prefix and the second as the morphism `DerivedCategory.Q.map e.hom` composed with
that inverse.  Neither applies while `e` is inside the transpose.

This file moves it.  Naturality of the inverse transpose of [stacks 0A63] in its target variable
carries a trailing factor of the transposed argument out of the transpose and into the internal
Hom, and the internal Hom is a functor, so the factor merges with the inverse of the K-flat
description already standing there.  The result is the candidate's transpose written with
`DerivedCategory.Q.map e.hom` composed with that inverse as one morphism of the covariant slot --
which is the form both lemmas above read.

**What is not done here.**  Nothing is registered and no caveat is lifted.  The [stacks 068I]
identification stays open, and so does the companion hypothesis `h` of
`Dualizing.tensorComparisonCompatibility_of_tensorBaseChangeMor`, whose frontier is
`Dualizing.tensorComparisonCompatibility_of_kFlat_tail`.  What this file changes is where in the
candidate's transpose the tensor base-change isomorphism sits.

## Main results

* `StacksDraft.DerivedHom.DerivedHomAdjunction.homEquiv_symm_assoc_hom_map` -- **the move**, over
  an arbitrary derived tensor--Hom adjunction: the inverse transpose of a composite followed by
  the internal Hom of a morphism is the inverse transpose of the composite with its last factor
  dropped, followed by the internal Hom of that factor composed with the morphism.
* `Dualizing.tensorBaseChangeMor_transpose_eq_covariant_slot` -- the [stacks 0A63] transpose over
  `A` of the [stacks 068I] candidate at a pair of localizations of K-flat complexes, with the
  tensor base-change isomorphism in the covariant slot of the internal Hom rather than inside the
  transpose.

## Implementation notes

The move is stated over an arbitrary derived tensor--Hom adjunction and an arbitrary threefold
composite, and the concrete instance is obtained by `exact`.  The argument
`Dualizing.tensorBaseChangeMor_transpose_eq_q_obj` produces is associated to the right while
naturality of the inverse transpose splits off the *last* factor, so a rewrite in place would have
to reassociate first; stating the whole step abstractly lets definitional unification do that, and
keeps the two bifunctor arguments -- which are elaborated at the product category's `Quiver.Hom`,
against which keyed matching does not fire -- out of any rewrite.

The abstract statement is also the one a consumer of
`Dualizing.tensorBaseChangeMor_eq_of_unit_chain_prefix` needs: that theorem quantifies over the
tensor base-change isomorphism, so the existential form below does not apply to it, while the
abstract move instantiates at whichever isomorphism it was handed.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
* [Stacks Project, Tag 06XZ](https://stacks.math.columbia.edu/tag/06XZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor
open CochainComplex.DerivedTensor
open CochainComplex.DerivedExtensionScalars

universe uR uA uM u₁ u₂ u₃

namespace StacksDraft.DerivedHom.DerivedHomAdjunction

/-- **Moving the last factor of a transposed argument into the covariant slot.**

For a derived tensor--Hom adjunction `d`, the inverse transpose of a composite `u ≫ b ≫ h`
followed by the internal Hom of `g` is the inverse transpose of `u ≫ b` followed by the internal
Hom of `h ≫ g`: naturality of the inverse transpose in its target variable splits off `h`, and the
internal Hom is a functor.

This is the companion of
`StacksDraft.DerivedHom.DerivedHomAdjunction.homEquiv_symm_comp_hom_map`, which runs the other
way: that lemma absorbs an internal-Hom tail *into* the transpose, moving the contravariant slot
into the transposed argument, while this one takes the last factor of the transposed argument
*out*, into the covariant slot, leaving a transpose of the shortened argument.

Stated over an arbitrary adjunction and arbitrary morphisms so that a concrete instance is checked
at default transparency, with no rewrite against a pair-morphism argument -- those are elaborated
at the product category's `Quiver.Hom`, against which keyed matching does not fire. -/
public theorem homEquiv_symm_assoc_hom_map
    {B : Type u₁} [CommRing B] [HasDerivedCategory.{u₃} (ModuleCat.{u₂} B)]
    (d : DerivedHomAdjunction.{u₁, u₂, u₃} B)
    {X Y M₀ M₁ M₂ M₃ : DerivedCategory (ModuleCat.{u₂} B)}
    (u : d.tensor.obj (X, Y) ⟶ M₀) (b : M₀ ⟶ M₁) (h : M₁ ⟶ M₂) (g : M₂ ⟶ M₃) :
    (d.homEquiv X Y M₂).symm (u ≫ b ≫ h) ≫
        d.hom.map ((𝟙 (Opposite.op Y), g) :
          ((Opposite.op Y, M₂) : (DerivedCategory (ModuleCat.{u₂} B))ᵒᵖ ×
            DerivedCategory (ModuleCat.{u₂} B)) ⟶ (Opposite.op Y, M₃)) =
      (d.homEquiv X Y M₁).symm (u ≫ b) ≫
        d.hom.map ((𝟙 (Opposite.op Y), h ≫ g) :
          ((Opposite.op Y, M₁) : (DerivedCategory (ModuleCat.{u₂} B))ᵒᵖ ×
            DerivedCategory (ModuleCat.{u₂} B)) ⟶ (Opposite.op Y, M₃)) := by
  have hmap : d.hom.map ((𝟙 (Opposite.op Y), h) :
          ((Opposite.op Y, M₁) : (DerivedCategory (ModuleCat.{u₂} B))ᵒᵖ ×
            DerivedCategory (ModuleCat.{u₂} B)) ⟶ (Opposite.op Y, M₂)) ≫
        d.hom.map ((𝟙 (Opposite.op Y), g) :
          ((Opposite.op Y, M₂) : (DerivedCategory (ModuleCat.{u₂} B))ᵒᵖ ×
            DerivedCategory (ModuleCat.{u₂} B)) ⟶ (Opposite.op Y, M₃)) =
      d.hom.map ((𝟙 (Opposite.op Y), h ≫ g) :
        ((Opposite.op Y, M₁) : (DerivedCategory (ModuleCat.{u₂} B))ᵒᵖ ×
          DerivedCategory (ModuleCat.{u₂} B)) ⟶ (Opposite.op Y, M₃)) := by
    rw [← d.hom.map_comp, CategoryTheory.prod_comp, Category.id_comp]
  rw [← Category.assoc u b h, d.homEquiv_symm_naturality_right, Category.assoc, hmap]

end StacksDraft.DerivedHom.DerivedHomAdjunction

attribute [local instance] HasDerivedCategory.standard

namespace Dualizing

attribute [local instance] extendScalarsAdditiveOfRingHom

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
  (D : TotalDerivedExtensionScalars.{uR, max uR uA uM, uA} f)
  (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
    DerivedCategory (ModuleCat.{max uR uA uM} A))
  (comparison : DerivedCategory.Q ⋙ F ⟶
    (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [hF : F.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]

include hF in
/-- **The [stacks 0A63] transpose over `A` of the [stacks 068I] candidate, with the tensor
base-change isomorphism in the covariant slot.**

`Dualizing.tensorBaseChangeMor_transpose_eq_q_obj` reads the tensor base-change isomorphism `e`
inside the transpose, as the last factor of the transposed argument.  Naturality of the inverse
transpose of [stacks 0A63] in its target variable moves it out, where the functoriality of the
internal Hom merges it with the inverse of the K-flat description
`Stacks.DerivedHom.BaseChange.tensorKFlatComparisonIso` of `F (Q K ⊗ᴸ_R Q L)`.

So the transpose is the transpose of the tensor of the two model comparisons followed by the
K-flat representation of the derived tensor product over `A`, then the internal Hom of
`DerivedCategory.Q.map e.hom` composed with that inverse.  That single morphism of the covariant
slot is the `γ` of `Stacks.DerivedHom.BaseChange.functor_map_comp_hom_map_comp_counit` and the
morphism `Stacks.DerivedHom.BaseChange.functor_map_comp_tensorKFlatKInjectiveLift_hom` absorbs
into the chosen K-injective resolution. -/
theorem tensorBaseChangeMor_transpose_eq_covariant_slot
    (K L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (hK : IsKFlat.{uR, max uR uA uM} K) (hL : IsKFlat.{uR, max uR uA uM} L) :
    let dA := StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{uA, max uR uA uM,
      max uR uA uM + 1} A
    let W := (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{uR, max uR uA uM,
      max uR uA uM + 1} R).tensor.obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L)
    ∃ (hFL : IsKFlat.{uA, max uR uA uM}
          ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj L))
        (e : tensorComplex.{uA, max uR uA uM}
            ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj K)
            ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj L) ≅
          (extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj
            (tensorComplex.{uR, max uR uA uM} K L)),
      IsTensorBaseChangeIso.{uR, uA, max uR uA uM} f K L e ∧
        (dA.homEquiv (F.obj (DerivedCategory.Q.obj K)) (F.obj (DerivedCategory.Q.obj L))
              (F.obj W)).symm
            (tensorBaseChangeMor.{uR, uA, uM} f F comparison D (DerivedCategory.Q.obj K)
              (DerivedCategory.Q.obj L)) =
          (dA.homEquiv (F.obj (DerivedCategory.Q.obj K)) (F.obj (DerivedCategory.Q.obj L))
                (DerivedCategory.Q.obj (tensorComplex.{uA, max uR uA uM}
                  ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj K)
                  ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj L)))).symm
              (dA.tensor.map
                  ((CategoryTheory.Prod.mkHom (comparison.app K) (comparison.app L) :
                      ((F.obj (DerivedCategory.Q.obj K), F.obj (DerivedCategory.Q.obj L)) :
                        DerivedCategory (ModuleCat.{max uR uA uM} A) ×
                          DerivedCategory (ModuleCat.{max uR uA uM} A)) ⟶
                      (DerivedCategory.Q.obj ((extensionOfScalarsCochain.{uR, uA,
                          max uR uA uM} f).obj K),
                        DerivedCategory.Q.obj ((extensionOfScalarsCochain.{uR, uA,
                          max uR uA uM} f).obj L)))) ≫
                (derivedTensor_comparison.{uA, max uR uA uM} A
                    ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj K)
                    ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj L) hFL).hom) ≫
            dA.hom.map (𝟙 (Opposite.op (F.obj (DerivedCategory.Q.obj L))),
              DerivedCategory.Q.map e.hom ≫
                (_root_.Stacks.DerivedHom.BaseChange.tensorKFlatComparisonIso.{uR, uA, uM} f F
                  comparison K L hK hL).inv) := by
  intro dA W
  obtain ⟨hFL, e, he, heq⟩ :=
    tensorBaseChangeMor_transpose_eq_q_obj.{uR, uA, uM} f D F comparison K L hK hL
  exact ⟨hFL, e, he, heq.trans (dA.homEquiv_symm_assoc_hom_map _ _ _ _)⟩

end Dualizing

end
