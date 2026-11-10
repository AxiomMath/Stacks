module

public import StacksFrontier.CategoryTheory.Adjunction.Mates
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.BaseChange

/-!
# Base change along an open immersion of the target

For a morphism of schemes `f : X ⟶ S` and an open `V` of `S`, the square
```
f ⁻¹ᵁ V --ι--> X
|f ∣_ V        |f
V       --ι--> S
```
commutes, and this file proves that its canonical base-change morphism
`V.ι ^* f _* ⟶ (f ∣_ V) _* ((f ⁻¹ᵁ V).ι) ^*` is an isomorphism.  This is the step of Stacks
Tag 02KG which says that the base-change assertion is local on the base.

## Main definitions

* `Stacks.AlgebraicGeometry.AffineBaseChange.restrictSquare` is the commutative square above.
* `Stacks.AlgebraicGeometry.AffineBaseChange.restrictMate` is the base-change morphism of that
  square formed with respect to the restriction adjunctions
  `AlgebraicGeometry.Scheme.Modules.restrictAdjunction` rather than the
  pullback--pushforward adjunctions.

## Main results

* `Stacks.AlgebraicGeometry.AffineBaseChange.isIso_baseChangeNatTrans_restrictSquare`: the
  canonical base-change morphism of the restriction square is an isomorphism at every module.

## Implementation notes

The base-change morphism is the mate of `pushforwardSquareIso` under the two
pullback--pushforward adjunctions.  The proof replaces both of those adjunctions by the
restriction adjunctions, which have the same right adjoints, using
`Stacks.CategoryTheory.mateEquiv_symm_congr_left` and
`Stacks.CategoryTheory.mateEquiv_symm_congr_right`; the canonical comparison of the two left
adjoints is `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`, so this changes the
morphism only by whiskering with isomorphisms.

With the restriction adjunctions in place the mate becomes invertible for formal reasons.  Its
three factors are: the image under `f _* ⋙ (- ∣_ V)` of the unit of the restriction adjunction
at `f ⁻¹ᵁ V`, the image of `pushforwardSquareIso`, and the counit of the restriction adjunction
at `V`.  The last is invertible because `AlgebraicGeometry.Scheme.Modules.restrictAdjunction`
has invertible counit, the middle because `pushforwardSquareIso` is an isomorphism, and the
first because `restrictPushforwardIso` identifies `f _* ⋙ (- ∣_ V)` with
`(- ∣_ (f ⁻¹ᵁ V)) ⋙ (f ∣_ V) _*`, on which the unit becomes invertible by the triangle
identity and the invertibility of the counit.

## References

* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.AffineBaseChange

variable {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens)

/-- The square expressing that `f` restricted over an open `V` of the target is the base change
of `f` along the inclusion of `V`. -/
lemma restrictSquare : (f ⁻¹ᵁ V).ι ≫ f = (f ∣_ V) ≫ V.ι := (morphismRestrict_ι f V).symm

/-- The base-change morphism of the restriction square of `f` over `V`, formed with respect to
the restriction adjunctions instead of the pullback--pushforward adjunctions. -/
noncomputable def restrictMate :
    TwoSquare (Scheme.Modules.pushforward f) (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι)
      (Scheme.Modules.restrictFunctor V.ι) (Scheme.Modules.pushforward (f ∣_ V)) :=
  (mateEquiv (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ V).ι)
      (Scheme.Modules.restrictAdjunction V.ι)).symm
    (AffinePushforward.pushforwardSquareIso (restrictSquare f V)).hom

/-- The canonical base-change morphism of the restriction square is `restrictMate` whiskered
with the two comparisons of restriction and inverse image. -/
lemma baseChangeNatTrans_restrictSquare :
    AffinePushforward.baseChangeNatTrans (restrictSquare f V) =
      TwoSquare.whiskerLeft (TwoSquare.whiskerRight (restrictMate f V)
          (Adjunction.leftAdjointUniq (Scheme.Modules.pullbackPushforwardAdjunction V.ι)
            (Scheme.Modules.restrictAdjunction V.ι)).hom)
        (Adjunction.leftAdjointUniq (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ V).ι)
          (Scheme.Modules.pullbackPushforwardAdjunction (f ⁻¹ᵁ V).ι)).hom := by
  have e1 := Stacks.CategoryTheory.mateEquiv_symm_congr_left
    (Scheme.Modules.pullbackPushforwardAdjunction (f ⁻¹ᵁ V).ι)
    (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ V).ι)
    (Scheme.Modules.pullbackPushforwardAdjunction V.ι)
    (TwoSquare.mk _ _ _ _ (AffinePushforward.pushforwardSquareIso (restrictSquare f V)).hom)
  have e2 := Stacks.CategoryTheory.mateEquiv_symm_congr_right
    (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ V).ι)
    (Scheme.Modules.restrictAdjunction V.ι)
    (Scheme.Modules.pullbackPushforwardAdjunction V.ι)
    (TwoSquare.mk _ _ _ _ (AffinePushforward.pushforwardSquareIso (restrictSquare f V)).hom)
  rw [e2] at e1
  exact e1

/-- The three factors of `restrictMate`. -/
lemma restrictMate_app (M : X.Modules) :
    (restrictMate f V).app M =
      (Scheme.Modules.restrictFunctor V.ι).map ((Scheme.Modules.pushforward f).map
          ((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ V).ι).unit.app M)) ≫
        (Scheme.Modules.restrictFunctor V.ι).map
          ((AffinePushforward.pushforwardSquareIso (restrictSquare f V)).hom.app
            ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj M)) ≫
        (Scheme.Modules.restrictAdjunction V.ι).counit.app
          ((Scheme.Modules.pushforward (f ∣_ V)).obj
            ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj M)) := by
  simp [restrictMate, mateEquiv]

/-- The unit of the restriction adjunction at `f ⁻¹ᵁ V` becomes invertible after applying
`f _*` and restricting to `V`. -/
theorem isIso_unit_restrictPushforward (M : X.Modules) :
    IsIso ((Scheme.Modules.pushforward f ⋙ Scheme.Modules.restrictFunctor V.ι).map
      ((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ V).ι).unit.app M)) := by
  have ht := (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ V).ι).left_triangle_components M
  have h0 : IsIso ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).map
      ((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ V).ι).unit.app M) ≫
      (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ V).ι).counit.app
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj M)) := by
    rw [ht]
    infer_instance
  have h1 : IsIso ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).map
      ((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ V).ι).unit.app M)) :=
    IsIso.of_isIso_comp_right _
      ((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ V).ι).counit.app
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj M))
  have h2 : IsIso ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι ⋙
      Scheme.Modules.pushforward (f ∣_ V)).map
      ((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ V).ι).unit.app M)) :=
    Functor.map_isIso (Scheme.Modules.pushforward (f ∣_ V)) _
  have hnat := (AffinePushforward.restrictPushforwardIso f V).hom.naturality
    ((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ V).ι).unit.app M)
  have h3 : IsIso ((Scheme.Modules.pushforward f ⋙
      Scheme.Modules.restrictFunctor V.ι).map
      ((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ V).ι).unit.app M) ≫
      (AffinePushforward.restrictPushforwardIso f V).hom.app _) := by
    rw [hnat]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance h2
  exact IsIso.of_isIso_comp_right _ ((AffinePushforward.restrictPushforwardIso f V).hom.app _)

/-- `restrictMate` is invertible at every module. -/
theorem isIso_restrictMate_app (M : X.Modules) :
    IsIso ((restrictMate f V).app M) := by
  rw [restrictMate_app]
  have : IsIso ((Scheme.Modules.restrictFunctor V.ι).map ((Scheme.Modules.pushforward f).map
      ((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ V).ι).unit.app M))) :=
    isIso_unit_restrictPushforward f V M
  infer_instance

/-- The three factors of the canonical base-change morphism of the restriction square. -/
lemma baseChangeNatTrans_restrictSquare_app (M : X.Modules) :
    (AffinePushforward.baseChangeNatTrans (restrictSquare f V)).app M =
      (Adjunction.leftAdjointUniq (Scheme.Modules.pullbackPushforwardAdjunction V.ι)
          (Scheme.Modules.restrictAdjunction V.ι)).hom.app
          ((Scheme.Modules.pushforward f).obj M) ≫
        (restrictMate f V).app M ≫
        (Scheme.Modules.pushforward (f ∣_ V)).map
          ((Adjunction.leftAdjointUniq (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ V).ι)
            (Scheme.Modules.pullbackPushforwardAdjunction (f ⁻¹ᵁ V).ι)).hom.app M) := by
  rw [show (AffinePushforward.baseChangeNatTrans (restrictSquare f V)) = _ from
    baseChangeNatTrans_restrictSquare f V]
  simp [TwoSquare.whiskerLeft, TwoSquare.whiskerRight]

/-- The canonical base-change morphism of the square obtained by restricting `f` over an open
of its target is an isomorphism. -/
theorem isIso_baseChangeNatTrans_restrictSquare (M : X.Modules) :
    IsIso ((AffinePushforward.baseChangeNatTrans (restrictSquare f V)).app M) := by
  rw [baseChangeNatTrans_restrictSquare_app]
  have := isIso_restrictMate_app f V M
  infer_instance

end Stacks.AlgebraicGeometry.AffineBaseChange

end
