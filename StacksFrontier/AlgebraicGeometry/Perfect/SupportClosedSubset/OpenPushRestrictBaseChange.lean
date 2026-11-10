module

public import StacksFrontier.AlgebraicGeometry.AffinePushforward.BaseChange
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Units
public import StacksFrontier.AlgebraicGeometry.ConormalComparison.Restriction
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.GlobalEquationsComplexData

/-!
# Base change of a direct image of a restriction along an open immersion

Let `g : X' ⟶ X` be a morphism of schemes, let `W ⊆ X` be an open and let `W' = g^{-1}(W)`.
For an `𝒪_X`-module `ℱ` the canonical map

`g^*(j_{W,*}(ℱ|_W)) ⟶ j_{W',*}((g^*ℱ)|_{W'})`

is the base-change morphism of the square

```
W' --g|_W--> W
|j_{W'}      |j_W
X' ---g----> X
```

followed by the identification `(g|_W)^*(ℱ|_W) ≅ (g^*ℱ)|_{W'}` of
`Stacks.AlgebraicGeometry.AffinePushforward.pullbackRestrictIso`.

This is the termwise comparison the two extended alternating Čech complexes of
[Stacks, Tag 0G7U] are built from: the terms of the complex of Tag 0G7I are exactly the
`j_{W,*}(ℱ|_W)` for `W` a principal-open intersection, and its differentials are built from the
unit `ℱ ⟶ j_{W,*}(ℱ|_W)` and the restriction maps `j_{W,*}(ℱ|_W) ⟶ j_{W'',*}(ℱ|_{W''})` for
`W'' ≤ W`.  The two compatibilities proved here are therefore exactly what makes the termwise
comparison a map of complexes.

## Main definitions

* `Stacks.Perfect.OpenPushRestrictBaseChange.openBaseChange`: the comparison map.

## Main results

* `openBaseChange_unit`: the comparison is compatible with the units of the restriction
  adjunctions, so it respects the degree-`0` differential of the Čech complex.
* `openBaseChange_canPR`: the comparison is compatible with the restriction maps `canPR` between
  the direct images belonging to two nested opens, so it respects the higher differentials.
* `openBaseChange_naturality`: the comparison is natural in the coefficient module.

## Implementation notes

All three compatibilities are proved by transposing across an adjunction, since a map out of
`g^*A` is never computable on sections.

* `openBaseChange_unit` is the transpose, along `Scheme.Modules.pullbackPushforwardAdjunction g`,
  of the defining property of `pullbackRestrictIso`.  That isomorphism is an
  `CategoryTheory.Adjunction.leftAdjointUniq`, so it is characterised by the equality of the two
  composite units, `Stacks.Conormal.Restriction.unit_comp_map_pullbackRestrictIso_hom_app`; and
  `baseChangeNatTrans` is a mate, so its transpose is
  `Stacks.AlgebraicGeometry.AffineBaseChange.unit_comp_pushforward_baseChangeNatTrans`.  Spelling
  the two composite units out (`pullbackRestrictAdjunction_unit_app_eq` and
  `restrictPullbackAdjunction_unit_app_eq`) makes the two statements differ exactly by the
  comparison isomorphism `pullbackRestrictIso`, which is why the proof ends in a cancellation of
  that isomorphism (`pushforwardComp_pullbackRestrictIso_cancel`).
* `openBaseChange_canPR` is *deduced* from `openBaseChange_unit`: after restricting to
  `g^{-1}(A)`, the pullback of the unit `ℱ ⟶ j_{B,*}(ℱ|_B)` becomes an isomorphism
  (`isIso_restrictFunctor_map_pullback_map_unit`), so the two maps out of `g^*(j_{B,*}(ℱ|_B))`
  may be compared after composing with it, and both composites are the unit for `g^{-1}(A)` by
  `openBaseChange_unit` and `unit_comp_canPR`.
* `openBaseChange_naturality` is the naturality of `baseChangeNatTrans` and of
  `pullbackRestrictIso`.

## References

* [Stacks Project, Tag 0G7U](https://stacks.math.columbia.edu/tag/0G7U)
* [Stacks Project, Tag 0G7I](https://stacks.math.columbia.edu/tag/0G7I)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeMayerVietoris (pushRestrict res)
open Stacks.AlgebraicGeometry.AffinePushforward (baseChangeNatTrans pullbackRestrictIso
  pushforwardSquareIso pullbackRestrictAdjunction restrictPullbackAdjunction)
open Stacks.Perfect.ExtendedAlternatingCech (canPR imagePreimage_eq imagePreimage_mono collapse2
  canPR_app_apply)
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.OpenPushRestrictBaseChange

variable {X X' : Scheme.{u}} (g : X' ⟶ X) (F : X.Modules) (W : X.Opens)

/-- The square `(g|_W) ≫ j_W = j_{W'} ≫ g` cutting out the preimage of an open. -/
public theorem restrictSquare : (g ∣_ W) ≫ W.ι = (g ⁻¹ᵁ W).ι ≫ g :=
  morphismRestrict_ι g W

/-- **The base-change comparison `g^*(j_{W,*}(ℱ|_W)) ⟶ j_{W',*}((g^*ℱ)|_{W'})`.** -/
public def openBaseChange :
    (Scheme.Modules.pullback g).obj (pushRestrict F W) ⟶
      pushRestrict ((Scheme.Modules.pullback g).obj F) (g ⁻¹ᵁ W) :=
  (baseChangeNatTrans (restrictSquare g W)).app
      ((Scheme.Modules.restrictFunctor W.ι).obj F) ≫
    (Scheme.Modules.pushforward (g ⁻¹ᵁ W).ι).map ((pullbackRestrictIso g W).inv.app F)

/-! ### The two composite units entering the defining property of `pullbackRestrictIso` -/

/-- The unit of `pullbackRestrictAdjunction`, spelled out: it is the unit of the
pullback–pushforward adjunction of `g` followed by the unit of the restriction adjunction of
`j_{W'}`. -/
public theorem pullbackRestrictAdjunction_unit_app_eq (A : X.Modules) :
    (pullbackRestrictAdjunction g W).unit.app A =
      (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app A ≫
        (Scheme.Modules.pushforward g).map
          ((Scheme.Modules.restrictAdjunction (g ⁻¹ᵁ W).ι).unit.app
            ((Scheme.Modules.pullback g).obj A)) ≫
        (Scheme.Modules.pushforwardComp (g ⁻¹ᵁ W).ι g).hom.app
          ((Scheme.Modules.restrictFunctor (g ⁻¹ᵁ W).ι).obj
            ((Scheme.Modules.pullback g).obj A)) := by
  simp [pullbackRestrictAdjunction, Adjunction.comp_unit_app]

/-- The unit of `restrictPullbackAdjunction`, corrected by the equality of the two composites
around the restriction square, spelled out: it is the unit of the restriction adjunction of `j_W`
followed by the unit of the pullback–pushforward adjunction of `g|_W`. -/
public theorem restrictPullbackAdjunction_unit_app_eq (A : X.Modules) :
    ((restrictPullbackAdjunction g W).ofNatIsoRight
          (Scheme.Modules.pushforwardCongr (morphismRestrict_ι g W))).unit.app A =
      (Scheme.Modules.restrictAdjunction W.ι).unit.app A ≫
        (Scheme.Modules.pushforward W.ι).map
          ((Scheme.Modules.pullbackPushforwardAdjunction (g ∣_ W)).unit.app
            ((Scheme.Modules.restrictFunctor W.ι).obj A)) ≫
        (Scheme.Modules.pushforwardComp (g ∣_ W) W.ι).hom.app
          ((Scheme.Modules.pullback (g ∣_ W)).obj
            ((Scheme.Modules.restrictFunctor W.ι).obj A)) ≫
        (Scheme.Modules.pushforwardCongr (morphismRestrict_ι g W)).hom.app
          ((Scheme.Modules.pullback (g ∣_ W)).obj
            ((Scheme.Modules.restrictFunctor W.ι).obj A)) := by
  simp [restrictPullbackAdjunction, Adjunction.comp_unit_app]

/-- **The two comparison isomorphisms in the transposed base-change map cancel.**  Every
component of `Scheme.Modules.pushforwardComp` is the identity on sections and the preimage of an
open along a composition is the iterated preimage, so after taking sections this composite is
`pullbackRestrictIso` followed by its inverse. -/
public theorem pushforwardComp_pullbackRestrictIso_cancel :
    (Scheme.Modules.pushforwardComp (g ⁻¹ᵁ W).ι g).hom.app
          ((Scheme.Modules.restrictFunctor (g ⁻¹ᵁ W).ι).obj
            ((Scheme.Modules.pullback g).obj F)) ≫
        (Scheme.Modules.pushforward ((g ⁻¹ᵁ W).ι ≫ g)).map
          ((pullbackRestrictIso g W).hom.app F) ≫
        (Scheme.Modules.pushforwardComp (g ⁻¹ᵁ W).ι g).inv.app
          ((Scheme.Modules.pullback (g ∣_ W)).obj
            ((Scheme.Modules.restrictFunctor W.ι).obj F)) ≫
        (Scheme.Modules.pushforward g).map
          ((Scheme.Modules.pushforward (g ⁻¹ᵁ W).ι).map
            ((pullbackRestrictIso g W).inv.app F)) = 𝟙 _ := by
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforwardComp_hom_app_app,
    Scheme.Modules.pushforwardComp_inv_app_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.Hom.id_app]
  exact congrArg (fun z => Scheme.Modules.Hom.app z _)
    ((pullbackRestrictIso g W).hom_inv_id_app F)

/-! ### Compatibility with the units -/

/-- `openBaseChange` transposed along `Scheme.Modules.pullbackPushforwardAdjunction g`. -/
public theorem homEquiv_openBaseChange :
    (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _ (openBaseChange g F W) =
      (Scheme.Modules.pushforward W.ι).map
          ((Scheme.Modules.pullbackPushforwardAdjunction (g ∣_ W)).unit.app
            ((Scheme.Modules.restrictFunctor W.ι).obj F)) ≫
        (pushforwardSquareIso (restrictSquare g W)).hom.app
          ((Scheme.Modules.pullback (g ∣_ W)).obj
            ((Scheme.Modules.restrictFunctor W.ι).obj F)) ≫
        (Scheme.Modules.pushforward g).map
          ((Scheme.Modules.pushforward (g ⁻¹ᵁ W).ι).map
            ((pullbackRestrictIso g W).inv.app F)) := by
  simp only [openBaseChange]
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_unit,
    Stacks.AlgebraicGeometry.AffineBaseChange.unit_comp_pushforward_baseChangeNatTrans,
    Category.assoc]

/-- **The comparison is compatible with the units of the restriction adjunctions.** -/
public theorem openBaseChange_unit :
    (Scheme.Modules.pullback g).map ((Scheme.Modules.restrictAdjunction W.ι).unit.app F) ≫
        openBaseChange g F W =
      (Scheme.Modules.restrictAdjunction (g ⁻¹ᵁ W).ι).unit.app
        ((Scheme.Modules.pullback g).obj F) := by
  have hstar := Stacks.Conormal.Restriction.unit_comp_map_pullbackRestrictIso_hom_app g W F
  rw [pullbackRestrictAdjunction_unit_app_eq, restrictPullbackAdjunction_unit_app_eq] at hstar
  apply ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv F _).injective
  rw [Adjunction.homEquiv_naturality_left]
  simp only [Functor.comp_obj]
  rw [homEquiv_openBaseChange, Adjunction.homEquiv_unit, pushforwardSquareIso]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  have hstar' := congrArg
    (fun z => z ≫ (Scheme.Modules.pushforwardComp (g ⁻¹ᵁ W).ι g).inv.app
        ((Scheme.Modules.pullback (g ∣_ W)).obj
          ((Scheme.Modules.restrictFunctor W.ι).obj F)) ≫
      (Scheme.Modules.pushforward g).map
        ((Scheme.Modules.pushforward (g ⁻¹ᵁ W).ι).map
          ((pullbackRestrictIso g W).inv.app F))) hstar
  simp only [Category.assoc] at hstar'
  rw [← hstar', pushforwardComp_pullbackRestrictIso_cancel]
  simp only [Functor.comp_obj, Category.comp_id]

/-! ### Compatibility with the restriction maps between nested opens -/

/-- **The unit of the restriction adjunction of a smaller open factors through that of a larger
one.**  On sections both sides are the restriction map of `ℱ` from `V` to `A ⊓ V`. -/
public theorem unit_comp_canPR {Y : Scheme.{u}} (G : Y.Modules) {A B : Y.Opens} (hAB : A ≤ B) :
    (Scheme.Modules.restrictAdjunction B.ι).unit.app G ≫ canPR G hAB =
      (Scheme.Modules.restrictAdjunction A.ι).unit.app G := by
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => ?_)
  change (canPR G hAB).app V (((Scheme.Modules.restrictAdjunction B.ι).unit.app G).app V x) = _
  rw [canPR_app_apply, Scheme.Modules.restrictAdjunction_unit_app_app,
    Scheme.Modules.restrictAdjunction_unit_app_app]
  exact collapse2 G (homOfLE (B.ι.image_preimage_le V))
    (homOfLE (imagePreimage_mono hAB V)) (homOfLE (A.ι.image_preimage_le V)) x

/-- **Two morphisms into a direct image along an open immersion agree as soon as they agree after
composing with a morphism whose restriction is invertible.**  Transposing across
`Scheme.Modules.restrictAdjunction` turns precomposition with `φ` into precomposition with its
restriction, which is an epimorphism. -/
public theorem hom_ext_of_isIso_restrictFunctor_map {Y Y' : Scheme.{u}} (f : Y' ⟶ Y)
    [IsOpenImmersion f] {Z Z' : Y.Modules} {N : Y'.Modules} (φ : Z' ⟶ Z)
    (hφ : IsIso ((Scheme.Modules.restrictFunctor f).map φ))
    (α β : Z ⟶ (Scheme.Modules.pushforward f).obj N) (h : φ ≫ α = φ ≫ β) : α = β := by
  have := hφ
  apply ((Scheme.Modules.restrictAdjunction f).homEquiv Z N).symm.injective
  rw [← cancel_epi ((Scheme.Modules.restrictFunctor f).map φ),
    ← Adjunction.homEquiv_naturality_left_symm, ← Adjunction.homEquiv_naturality_left_symm, h]

/-- **The pullback of the unit `ℱ ⟶ j_{B,*}(ℱ|_B)` becomes invertible after restriction to
`g^{-1}(A)`, for any `A ≤ B`.**  Restricted to `B` the unit is inverse to the counit, which is an
isomorphism because `j_B` is an open immersion; restricting further to `A` and then transporting
along `pullbackRestrictIso` only applies functors to that isomorphism. -/
public theorem isIso_restrictFunctor_map_pullback_map_unit {A B : X.Opens} (hAB : A ≤ B) :
    IsIso ((Scheme.Modules.restrictFunctor (g ⁻¹ᵁ A).ι).map
      ((Scheme.Modules.pullback g).map
        ((Scheme.Modules.restrictAdjunction B.ι).unit.app F))) := by
  have h1 : IsIso ((Scheme.Modules.restrictFunctor B.ι).map
      ((Scheme.Modules.restrictAdjunction B.ι).unit.app F)) :=
    IsIso.of_isIso_fac_right
      ((Scheme.Modules.restrictAdjunction B.ι).left_triangle_components F)
  have h2 : IsIso ((Scheme.Modules.restrictFunctor A.ι).map
      ((Scheme.Modules.restrictAdjunction B.ι).unit.app F)) := by
    rw [← NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι hAB))
        ((Scheme.Modules.restrictAdjunction B.ι).unit.app F),
      NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorComp (X.homOfLE hAB) B.ι)]
    have := h1
    exact inferInstanceAs (IsIso ((Scheme.Modules.restrictFunctor (X.homOfLE hAB)).map
      ((Scheme.Modules.restrictFunctor B.ι).map
        ((Scheme.Modules.restrictAdjunction B.ι).unit.app F))))
  rw [show (Scheme.Modules.restrictFunctor (g ⁻¹ᵁ A).ι).map
        ((Scheme.Modules.pullback g).map ((Scheme.Modules.restrictAdjunction B.ι).unit.app F)) =
      (Scheme.Modules.pullback g ⋙ Scheme.Modules.restrictFunctor (g ⁻¹ᵁ A).ι).map
        ((Scheme.Modules.restrictAdjunction B.ι).unit.app F) from rfl,
    NatIso.isIso_map_iff (pullbackRestrictIso g A)]
  have := h2
  exact inferInstanceAs (IsIso ((Scheme.Modules.pullback (g ∣_ A)).map
    ((Scheme.Modules.restrictFunctor A.ι).map
      ((Scheme.Modules.restrictAdjunction B.ι).unit.app F))))

/-- **The comparison is compatible with the restriction maps between nested opens.** -/
public theorem openBaseChange_canPR {A B : X.Opens} (hAB : A ≤ B) :
    (Scheme.Modules.pullback g).map (canPR F hAB) ≫ openBaseChange g F A =
      openBaseChange g F B ≫
        canPR ((Scheme.Modules.pullback g).obj F) (Scheme.Hom.preimage_mono g hAB) := by
  have hkey : (Scheme.Modules.pullback g).map
        ((Scheme.Modules.restrictAdjunction B.ι).unit.app F) ≫
      ((Scheme.Modules.pullback g).map (canPR F hAB) ≫ openBaseChange g F A) =
    (Scheme.Modules.pullback g).map
        ((Scheme.Modules.restrictAdjunction B.ι).unit.app F) ≫
      (openBaseChange g F B ≫
        canPR ((Scheme.Modules.pullback g).obj F) (Scheme.Hom.preimage_mono g hAB)) := by
    rw [← Category.assoc, ← Functor.map_comp, unit_comp_canPR, openBaseChange_unit,
      ← Category.assoc, openBaseChange_unit, unit_comp_canPR]
  exact hom_ext_of_isIso_restrictFunctor_map (g ⁻¹ᵁ A).ι _
    (isIso_restrictFunctor_map_pullback_map_unit g F hAB) _ _ hkey

/-! ### Naturality in the coefficient module -/

/-- **The comparison is natural in the coefficient module.** -/
public theorem openBaseChange_naturality {F G : X.Modules} (φ : F ⟶ G) :
    (Scheme.Modules.pullback g).map
          ((Scheme.Modules.pushforward W.ι).map
            ((Scheme.Modules.restrictFunctor W.ι).map φ)) ≫
        openBaseChange g G W =
      openBaseChange g F W ≫
        (Scheme.Modules.pushforward (g ⁻¹ᵁ W).ι).map
          ((Scheme.Modules.restrictFunctor (g ⁻¹ᵁ W).ι).map
            ((Scheme.Modules.pullback g).map φ)) := by
  have h1 := (baseChangeNatTrans (restrictSquare g W)).naturality
    ((Scheme.Modules.restrictFunctor W.ι).map φ)
  have h2 := (pullbackRestrictIso g W).inv.naturality φ
  simp only [Functor.comp_map] at h1 h2
  simp only [openBaseChange]
  rw [← Category.assoc, h1, Category.assoc, ← Functor.map_comp, h2, Functor.map_comp]
  simp only [Category.assoc]

end Stacks.Perfect.OpenPushRestrictBaseChange

end
