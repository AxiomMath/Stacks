module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriekCocontinuousSquare
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizationCofinality
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Base change of sheaves of modules over a cartesian square of relocalizations

Let `(C, O)` be a ringed site and let
```
  X' --a--> X
  |b        |c
  V         V
  Y' --d--> Y
```
be a cartesian diagram of `C`. Each morphism `f : Z ⟶ W` of `C` gives a relocalization morphism of
topoi `j_{Z/W} : Sh(C/Z) ⟶ Sh(C/W)`, whose inverse image is restriction along `Over.map f` and
whose direct image is the right Kan extension along it, and `O|_Z` is the inverse image of `O|_W`;
so each column of the square carries a direct image of sheaves of modules and each row an inverse
image. This file proves that the two composites agree:
`j_{X'/Y',*} ∘ j_{X'/X}^* ≅ j_{Y'/Y}^* ∘ j_{X/Y,*}` as functors `Mod(O|_X) ⥤ Mod(O|_{Y'})`.

This is the underived statement behind Stacks 0FN5. It is Stacks 0FN3 on sheaves of modules —
`Stacks.SheafOfModules.nonempty_inverseImage_comp_cocontinuousPushforwardOf_iso` — read off at the
four functors `Over.map a`, `Over.map b`, `Over.map c`, `Over.map d`. All of that tag's hypotheses
are supplied here with nothing assumed beyond cartesianness: the continuity and cocontinuity of
`Over.map` are instances of Mathlib, the commutation of the square of slice functors is the
equality of functors `Stacks.Sites.RelocalizationCofinality.overMapSquareEq`, and the cofinality
condition — hypothesis (4) of Stacks 0FN1 — is
`Stacks.Sites.RelocalizationCofinality.final_costructuredArrow_map₂_overMap`, which is exactly
where cartesianness enters.

## Main definitions

* `Stacks.SheafOfModules.Relocalization.structureMap`: the structure map `j^♯ : O|_W ⟶ j_* O|_Z` of
  the relocalization morphism attached to `f : Z ⟶ W`, that is, the unit of the adjunction between
  restriction and the right Kan extension along `Over.map f`, read through
  `CategoryTheory.Sheaf.pushforwardOverMapIso`.
* `Stacks.SheafOfModules.Relocalization.pushforward`: the direct image `j_{Z/W,*}` of sheaves of
  modules along that relocalization, namely
  `Stacks.SheafOfModules.pushforwardCocontinuous` for that structure map.

## Main results

* `Stacks.SheafOfModules.Relocalization.overMap_eq_inverseImage`: the inverse image of sheaves of
  modules along a relocalization is Mathlib's `SheafOfModules.overMap`, as an equality of functors.
* `Stacks.SheafOfModules.Relocalization.nonempty_overMap_comp_pushforward_iso`: the base change
  over a cartesian square.
* `Stacks.SheafOfModules.Relocalization.structureMapSquare_eq_structureMap`: the structure map that
  the cartesian square induces on the left-hand column is the structure map of the relocalization
  at `b`.

## Implementation notes

The inverse image
`Stacks.SheafOfModules.inverseImage (J.over Z) (J.over W) (Over.map f) (O.over W)` of Stacks 0797
and Mathlib's `SheafOfModules.overMap O f` are the same functor **by definition**, which
`overMap_eq_inverseImage` records: both are `SheafOfModules.pushforward` along `Over.map f`, and
their two structure morphisms of sheaves of rings agree because the restriction of `O|_W` along
`Over.map f` is `O|_Z` on the nose, so that the comparison
`CategoryTheory.Sheaf.pushforwardOverMapIso` is the identity (`pushforwardOverMapIso_hom_eq_id`).
The statements below are therefore written with `overMap`, which is the inverse image a consumer
of the tag asks for, at no cost in the proof.

The direct image of the left-hand column is the one Stacks 0FN3 produces for the square, built
from the structure map of the right-hand column by restricting it along `Over.map d` and composing
with the base change of right Kan extensions of sheaves of rings
(`Stacks.SheafOfModules.structureMapSquare`). That it agrees with the structure map `structureMap`
of the relocalization `X' ⟶ Y'` is `structureMapSquare_eq_structureMap`, a coherence of the two
constructions rather than a consequence of the square: one side is a unit and the other a base
change, and they are compared leg by leg on the limit cones computing the right Kan extension
along `(Over.map b).op`. On a leg at `(U', ψ)` the unit side gives the restriction map of `O|_{Y'}`
along `ψ` (`structureMap_hom_app_comp_ranπ`, which is the triangle identity of the Kan extension
adjunction in the form `ranAdjunction_unit_app_app_comp_ranπ`), and the base-change side gives the
restriction map of `O|_Y` along the image of `(U', ψ)` under the comparison functor of the square
(`Stacks.SheafOfModules.structureBaseChange_π`); the two restriction maps agree because the
comparison functor is the identity on underlying objects of `C`.

The composites above are assembled out of `Eq.trans` and `congrArg` rather than rewritten with
`rw`: a morphism of sheaves of modules spelled through
`CategoryTheory.Functor.sheafPushforwardCocontinuous` and the same morphism spelled through
`CategoryTheory.Functor.ran` have source and target that agree only after unfolding the chosen
limit cones of the Kan extension, which is more unfolding than a rewrite's motive is checked with.

Instance search cannot find the pointwise right Kan extensions along `(Over.map f).op` on its own,
because the universe of the index categories is not determined by the goal until the coefficient
category is: `hasPointwiseRightKanExtension_op_overMap` supplies them with that universe pinned.

## References

* [Stacks Project, Tag 0FN3](https://stacks.math.columbia.edu/tag/0FN3), of which this is the
  instance at the slice functors of a cartesian square
* [Stacks Project, Tag 0FN1](https://stacks.math.columbia.edu/tag/0FN1), whose hypothesis (4)
  cartesianness supplies
* [Stacks Project, Tag 03EH](https://stacks.math.columbia.edu/tag/03EH), the relocalization
  morphism of topoi
* [Stacks Project, Tag 0797](https://stacks.math.columbia.edu/tag/0797), the inverse image of
  sheaves of modules along a continuous and cocontinuous functor of sites
-/

@[expose] public noncomputable section

open CategoryTheory

universe u uA vA uB vB uH vH

namespace Stacks.SheafOfModules

/-- **The unit of the Kan extension adjunction on a leg of the limit cone.** The unit
`T ⟶ L_*(L^{-1} T)` at `b`, followed by the leg of the limit cone computing the right Kan
extension at `(a, ψ : b ⟶ L(a))`, is the restriction map `T(ψ)`: the leg is restriction along
`ψ` followed by the counit, and the counit undoes the unit by the triangle identity. -/
theorem ranAdjunction_unit_app_app_comp_ranπ {A : Type uA} [Category.{vA} A] {B : Type uB}
    [Category.{vB} B] {H : Type uH} [Category.{vH} H] (L : A ⥤ B)
    [∀ F : A ⥤ H, L.HasRightKanExtension F] (T : B ⥤ H) (e : B) (j : StructuredArrow e L) :
    ((L.ranAdjunction H).unit.app T).app e ≫ ranπ L (L ⋙ T) e j = T.map j.hom := by
  have hnat : T.map j.hom ≫ ((L.ranAdjunction H).unit.app T).app (L.obj j.right)
      = ((L.ranAdjunction H).unit.app T).app e ≫ (L.ran.obj (L ⋙ T)).map j.hom :=
    ((L.ranAdjunction H).unit.app T).naturality j.hom
  dsimp only [ranπ]
  rw [← Category.assoc, ← hnat, Category.assoc,
    Functor.ranCounit_app_app_ranAdjunction_unit_app_app]
  exact Category.comp_id _

end Stacks.SheafOfModules

namespace Stacks.SheafOfModules.Relocalization

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)

/-- Pointwise right Kan extensions along `(Over.map f).op` exist for coefficients in any category
with limits of the size of the site. The universe of the index categories is fixed by the one of
the coefficients, which is why this is stated rather than left to instance search: in a goal whose
coefficient category is still a metavariable the smallness of `Over Z` is resolved at the wrong
universe. -/
local instance hasPointwiseRightKanExtension_op_overMap (A : Type (u + 1)) [Category.{u} A]
    [Limits.HasLimitsOfSize.{u, u} A] {Z W : C} (f : Z ⟶ W) (G : (Over Z)ᵒᵖ ⥤ A) :
    (Over.map f).op.HasPointwiseRightKanExtension G :=
  inferInstance

variable (O : Sheaf J RingCat.{u})

/-- The comparison of the restriction of `O|_W` along `Over.map f` with `O|_Z` is the identity:
both are the restriction of `O` along `Over.map f ⋙ Over.forget W = Over.forget Z`. -/
theorem pushforwardOverMapIso_hom_eq_id {Z W : C} (f : Z ⟶ W) :
    (Sheaf.pushforwardOverMapIso O f).hom = 𝟙 _ :=
  rfl

/-- **The inverse image of sheaves of modules along a relocalization is restriction along
`Over.map`.** The inverse image of Stacks 0797 for the continuous and cocontinuous functor
`Over.map f` and Mathlib's `SheafOfModules.overMap` are the same functor: both are the pushforward
of sheaves of modules along `Over.map f`, and the two structure morphisms of sheaves of rings are
the identity of the restriction of `O|_W` and the inverse of
`CategoryTheory.Sheaf.pushforwardOverMapIso`, which agree by
`pushforwardOverMapIso_hom_eq_id`. -/
theorem overMap_eq_inverseImage {Z W : C} (f : Z ⟶ W) :
    _root_.SheafOfModules.overMap.{u} O f =
      Stacks.SheafOfModules.inverseImage.{u} (J.over Z) (J.over W) (Over.map f) (O.over W) :=
  rfl

/-- **The structure map of a relocalization morphism of ringed topoi**, `j^♯ : O|_W ⟶ j_* O|_Z` for
`f : Z ⟶ W`: the unit of the adjunction between restriction along `Over.map f` and the right Kan
extension along it, evaluated at `O|_W`, read through the identification of the restriction of
`O|_W` with `O|_Z`. This is the sheaf-of-rings datum of Stacks 03EH that makes the relocalization a
morphism of ringed topoi. -/
def structureMap {Z W : C} (f : Z ⟶ W) :
    O.over W ⟶ ((Over.map f).sheafPushforwardCocontinuous RingCat.{u}
      (J.over Z) (J.over W)).obj (O.over Z) :=
  ((Over.map f).sheafAdjunctionCocontinuous RingCat.{u} (J.over Z) (J.over W)).unit.app
      (O.over W) ≫
    ((Over.map f).sheafPushforwardCocontinuous RingCat.{u} (J.over Z) (J.over W)).map
      (Sheaf.pushforwardOverMapIso O f).hom

/-- **The structure map of a relocalization on a leg of the limit cone.** For `f : Z ⟶ W` and an
object `(U', ψ : V' ⟶ (Over.map f)(U'))` of the index category of the right Kan extension along
`(Over.map f).op` at `V'`, the structure map `j^♯ : O|_W ⟶ j_* O|_Z` followed by the leg of that
limit cone is the restriction map of `O|_W` along `ψ`.

The structure map is the unit of the Kan extension adjunction followed by the comparison of the
restriction of `O|_W` along `Over.map f` with `O|_Z`; the comparison is the identity on each
object, so only the unit survives, and the unit on a leg is
`Stacks.SheafOfModules.ranAdjunction_unit_app_app_comp_ranπ`. -/
theorem structureMap_hom_app_comp_ranπ {Z W : C} (f : Z ⟶ W) (V : (Over W)ᵒᵖ)
    (j : StructuredArrow V (Over.map f).op) :
    (structureMap J O f).hom.app V ≫
        Stacks.SheafOfModules.ranπ (Over.map f).op (O.over Z).obj V j
      = (O.over W).obj.map j.hom := by
  have hid : ((Over.map f).op.ran.map (Sheaf.pushforwardOverMapIso O f).hom.hom).app V ≫
        Stacks.SheafOfModules.ranπ (Over.map f).op (O.over Z).obj V j
      = Stacks.SheafOfModules.ranπ (Over.map f).op ((Over.map f).op ⋙ (O.over W).obj) V j := by
    rw [Stacks.SheafOfModules.ranπ_map_functor]
    exact Category.comp_id _
  have hunit : (((Over.map f).sheafAdjunctionCocontinuous RingCat.{u}
        (J.over Z) (J.over W)).unit.app (O.over W)).hom
      = ((Over.map f).op.ranAdjunction RingCat.{u}).unit.app (O.over W).obj :=
    Functor.sheafAdjunctionCocontinuous_unit_app_hom _ _ _ _ _
  have hU : (structureMap J O f).hom.app V
      = (((Over.map f).op.ranAdjunction RingCat.{u}).unit.app (O.over W).obj).app V ≫
        ((Over.map f).op.ran.map (Sheaf.pushforwardOverMapIso O f).hom.hom).app V :=
    congrArg (fun x => x ≫ ((Over.map f).op.ran.map
      (Sheaf.pushforwardOverMapIso O f).hom.hom).app V) (congr_app hunit V)
  have s1 : (structureMap J O f).hom.app V ≫
        Stacks.SheafOfModules.ranπ (Over.map f).op (O.over Z).obj V j
      = ((((Over.map f).op.ranAdjunction RingCat.{u}).unit.app (O.over W).obj).app V ≫
            ((Over.map f).op.ran.map (Sheaf.pushforwardOverMapIso O f).hom.hom).app V) ≫
          Stacks.SheafOfModules.ranπ (Over.map f).op (O.over Z).obj V j :=
    congrArg (fun x => x ≫ Stacks.SheafOfModules.ranπ (Over.map f).op (O.over Z).obj V j) hU
  have s2 := Category.assoc
    ((((Over.map f).op.ranAdjunction RingCat.{u}).unit.app (O.over W).obj).app V)
    (((Over.map f).op.ran.map (Sheaf.pushforwardOverMapIso O f).hom.hom).app V)
    (Stacks.SheafOfModules.ranπ (Over.map f).op (O.over Z).obj V j)
  have s3 : (((Over.map f).op.ranAdjunction RingCat.{u}).unit.app (O.over W).obj).app V ≫
        (((Over.map f).op.ran.map (Sheaf.pushforwardOverMapIso O f).hom.hom).app V ≫
          Stacks.SheafOfModules.ranπ (Over.map f).op (O.over Z).obj V j)
      = (((Over.map f).op.ranAdjunction RingCat.{u}).unit.app (O.over W).obj).app V ≫
          Stacks.SheafOfModules.ranπ (Over.map f).op ((Over.map f).op ⋙ (O.over W).obj) V j :=
    congrArg (fun x => (((Over.map f).op.ranAdjunction RingCat.{u}).unit.app
      (O.over W).obj).app V ≫ x) hid
  have s4 : (((Over.map f).op.ranAdjunction RingCat.{u}).unit.app (O.over W).obj).app V ≫
        Stacks.SheafOfModules.ranπ (Over.map f).op ((Over.map f).op ⋙ (O.over W).obj) V j
      = (O.over W).obj.map j.hom :=
    Stacks.SheafOfModules.ranAdjunction_unit_app_app_comp_ranπ _ _ _ _
  exact s1.trans (s2.trans (s3.trans s4))

/-- **The direct image of sheaves of modules along a relocalization morphism of ringed topoi**,
`j_{Z/W,*} : Mod(O|_Z) ⥤ Mod(O|_W)` for `f : Z ⟶ W`: the direct image of
`Stacks.SheafOfModules.pushforwardCocontinuous` along the cocontinuous functor `Over.map f`, for
the structure map `structureMap`. Its underlying sheaf of abelian groups is the right Kan extension
along `Over.map f`. -/
@[sga "4 IV 13.2.1" "special case"]
def pushforward {Z W : C} (f : Z ⟶ W) :
    _root_.SheafOfModules.{u} (O.over Z) ⥤ _root_.SheafOfModules.{u} (O.over W) :=
  (Stacks.SheafOfModules.CocontinuousPushforward.of.{u} (J.over Z) (J.over W) (Over.map f)
    (structureMap J O f)).functor

variable {X' X Y' Y : C} {a : X' ⟶ X} {b : X' ⟶ Y'} {c : X ⟶ Y} {d : Y' ⟶ Y}

/-- **Base change over a cartesian square, on sheaves of modules.** For a cartesian diagram
`X' ⟶ X`, `X' ⟶ Y'`, `X ⟶ Y`, `Y' ⟶ Y` of a ringed site `(C, O)`, restriction along `Over.map d`
after the direct image along the relocalization at `c` is isomorphic to the direct image along the
relocalization at `b` after restriction along `Over.map a`.

This is Stacks 0FN3 on sheaves of modules at the four slice functors of the square. Its hypotheses
are discharged with nothing assumed beyond cartesianness: the square of slice functors commutes as
an equality of functors, and cartesianness gives the cofinality of every comparison functor of the
index categories of Section 00XF, which is hypothesis (4) of Stacks 0FN1.

The direct image of the left-hand column is the one the square induces on the structure map of the
right-hand column, `Stacks.SheafOfModules.structureMapSquare`; see the module's implementation
notes. The conclusion is asserted through `Nonempty`, as in Stacks 0FN1 and 0FN3, the comparison
being a base change of right Kan extensions. -/
theorem nonempty_overMap_comp_pushforward_iso (hsq : IsPullback a b c d) :
    Nonempty (_root_.SheafOfModules.overMap.{u} O a ⋙
        (Stacks.SheafOfModules.CocontinuousPushforward.of.{u} (J.over X') (J.over Y')
          (Over.map b) (Stacks.SheafOfModules.structureMapSquare
            (J' := J.over X') (K' := J.over Y') (structureMap J O c)
            (Stacks.Sites.RelocalizationCofinality.overMapSquareEq hsq.toCommSq))).functor ≅
      pushforward J O c ⋙ _root_.SheafOfModules.overMap.{u} O d) :=
  Stacks.SheafOfModules.nonempty_inverseImage_comp_cocontinuousPushforwardOf_iso
    (J.over X') (J.over X) (J.over Y') (J.over Y) (Over.map b) (Over.map c) (Over.map a)
    (Over.map d) (O.over X) (O.over Y) (structureMap J O c)
    (Stacks.Sites.RelocalizationCofinality.overMapSquareEq hsq.toCommSq)
    (Stacks.Sites.RelocalizationCofinality.final_costructuredArrow_map₂_overMap hsq)

/-- **The structure map that a cartesian square induces on its left-hand column is the structure
map of the relocalization at `b`.** For a cartesian diagram `X' ⟶ X`, `X' ⟶ Y'`, `X ⟶ Y`,
`Y' ⟶ Y`, the morphism of sheaves of rings `O|_{Y'} ⟶ j_{X'/Y',*} O|_{X'}` obtained from
`j^♯ : O|_Y ⟶ j_{X/Y,*} O|_X` by restricting along `Over.map d` and applying the base change of
right Kan extensions of Stacks 0FN1 is the unit `j^♯ : O|_{Y'} ⟶ j_{X'/Y',*} O|_{X'}` of the
relocalization at `b`.

Both sides are compared leg by leg on the limit cones computing the right Kan extension along
`(Over.map b).op`: the unit side gives the restriction map of `O|_{Y'}` along the leg, the
base-change side the restriction map of `O|_Y` along the image of the leg under the comparison
functor of the square, and the comparison functor is the identity on underlying objects of `C`. -/
theorem structureMapSquare_eq_structureMap (hsq : IsPullback a b c d) :
    Stacks.SheafOfModules.structureMapSquare (J' := J.over X') (K' := J.over Y')
        (structureMap J O c)
        (Stacks.Sites.RelocalizationCofinality.overMapSquareEq hsq.toCommSq) =
      structureMap J O b := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun V' => ?_))
  refine Stacks.SheafOfModules.ran_hom_ext (Over.map b).op (O.over X').obj (fun j => ?_)
  have hbc : (Stacks.SheafOfModules.structureBaseChange (J' := J.over X') (J := J.over X)
          (OC := O.over X)
          (Stacks.Sites.RelocalizationCofinality.overMapSquareEq hsq.toCommSq)).app V' ≫
        Stacks.SheafOfModules.ranπ (Over.map b).op (O.over X').obj V' j
      = Stacks.SheafOfModules.ranπ (Over.map c).op (O.over X).obj ((Over.map d).op.obj V')
          (Stacks.SheafOfModules.squareIndex
            (Stacks.Sites.RelocalizationCofinality.overMapSquareEq hsq.toCommSq) j) :=
    Stacks.SheafOfModules.structureBaseChange_π _ V' j
  have hassoc := Category.assoc
    ((structureMap J O c).hom.app ((Over.map d).op.obj V'))
    ((Stacks.SheafOfModules.structureBaseChange (J' := J.over X') (J := J.over X)
      (OC := O.over X)
      (Stacks.Sites.RelocalizationCofinality.overMapSquareEq hsq.toCommSq)).app V')
    (Stacks.SheafOfModules.ranπ (Over.map b).op (O.over X').obj V' j)
  have hL : (Stacks.SheafOfModules.structureMapSquare (J' := J.over X') (K' := J.over Y')
          (structureMap J O c)
          (Stacks.Sites.RelocalizationCofinality.overMapSquareEq hsq.toCommSq)).hom.app V' ≫
        Stacks.SheafOfModules.ranπ (Over.map b).op (O.over X').obj V' j
      = (O.over Y).obj.map (Stacks.SheafOfModules.squareIndex
          (Stacks.Sites.RelocalizationCofinality.overMapSquareEq hsq.toCommSq) j).hom :=
    hassoc.trans
      ((congrArg (fun x => (structureMap J O c).hom.app ((Over.map d).op.obj V') ≫ x) hbc).trans
        (structureMap_hom_app_comp_ranπ J O c _ _))
  have hR : (structureMap J O b).hom.app V' ≫
        Stacks.SheafOfModules.ranπ (Over.map b).op (O.over X').obj V' j
      = (O.over Y').obj.map j.hom := structureMap_hom_app_comp_ranπ J O b V' j
  refine hL.trans (Eq.trans ?_ hR.symm)
  have hnat : ((Stacks.Sites.CocontinuousExchange.twoSquare
        (Stacks.Sites.RelocalizationCofinality.overMapSquareEq
          hsq.toCommSq)).op.app j.right).unop.left = 𝟙 _ :=
    Stacks.Sites.RelocalizationCofinality.overMapSquare_app_left hsq.toCommSq j.right.unop
  have hleft : (Stacks.SheafOfModules.squareIndex
        (Stacks.Sites.RelocalizationCofinality.overMapSquareEq hsq.toCommSq) j).hom.unop.left
      = j.hom.unop.left := by
    rw [show (Stacks.SheafOfModules.squareIndex
          (Stacks.Sites.RelocalizationCofinality.overMapSquareEq hsq.toCommSq) j).hom.unop.left
        = ((Stacks.Sites.CocontinuousExchange.twoSquare
            (Stacks.Sites.RelocalizationCofinality.overMapSquareEq
              hsq.toCommSq)).op.app j.right).unop.left ≫ j.hom.unop.left from rfl,
      hnat, Category.id_comp]
  exact congrArg (fun g => O.obj.map (Opposite.op g)) hleft

end Stacks.SheafOfModules.Relocalization

end
