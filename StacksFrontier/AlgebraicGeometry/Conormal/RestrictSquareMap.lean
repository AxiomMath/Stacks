module

public import StacksFrontier.AlgebraicGeometry.Conormal.AmbientAffine
public import StacksFrontier.AlgebraicGeometry.Conormal.SquareMap

/-!
# The canonical map of conormal sheaves of a restriction square

Let `i : Z ⟶ X` be an immersion of schemes and let `V` be an open of `X`. The conormal sheaf of
the restriction `i ∣_ V` is the restriction of the conormal sheaf of `i` to `i⁻¹V`, by
`Stacks.Immersion.conormalSheafSelfRestrictIso`. This file identifies the comparison built from
that isomorphism with the canonical map of [Stacks Project, Tag 01R4] attached to the restriction
square
```
i⁻¹V --i∣_V--→ V
  |            |
 ι_{i⁻¹V}     ι_V
  ↓            ↓
  Z ----i----→ X
```
so that the restriction comparison inherits the composition law
`Stacks.Immersion.immersionConormalSheafMap_comp`.

The second half of the file proves the **associativity coherence** of the pullback composition
isomorphism `RingedSpaceModuleAdjunction.modulePullbackComp`: for three composable
morphisms of ringed spaces the two ways of comparing `r^* q^* p^*` with `(p ≫ q ≫ r)^*` agree.
Together with the restriction comparison this is what carries a map of conormal sheaves defined
over an open of the ambient scheme to a smaller open.

## Main results

* `Stacks.Immersion.modulePullbackRestrictIso_comp_conormalSheafSelfRestrictIso`: the composite
  of `AlgebraicGeometry.RingedSpace.modulePullbackRestrictIso`,
  `Stacks.Immersion.conormalSheafSelfRestrictIso` and `Stacks.Immersion.conormalSheafSelfIso` is
  the canonical map of the restriction square.
* `RingedSpaceModuleAdjunction.modulePullbackComp_assoc`: the associativity coherence of
  the pullback composition isomorphism.
* `RingedSpaceModuleAdjunction.modulePullbackComp_congr_left` and
  `Stacks.Immersion.immersionConormalSheafMap_congr`: the two transports along an equality of
  morphisms that a consumer of the previous two needs.
* `RingedSpaceModuleAdjunction.hom_ext_of_unit`: two morphisms out of a pullback agree as
  soon as their transposes do.

## Implementation notes

The restriction comparison is proved in **term mode**. Its statement mixes the two spellings of
a restricted ringed space that the implementation notes of
`StacksFrontier.AlgebraicGeometry.Conormal.AmbientAffine` describe — `Z.toSheafedSpace.ofRestrict`
on the side of `AlgebraicGeometry.RingedSpace.restrictHom` and `(i ⁻¹ᵁ V).ι` on the side of
`AlgebraicGeometry.morphismRestrict` — so the goal is not type-correct at `implicit`
transparency and no `rw` or `simp` can act on it; every step is a `congrArg` instead. The
re-association is factored through `Stacks.Immersion.comp_reassoc` so that the two large module
terms are written once.

The associativity coherence is proved by transposing along the adjunction, where the
corresponding statement for pushforward holds on the nose: pushforward along a composite *is* the
composite of the pushforwards, by
`RingedSpaceModuleAdjunction.modulePushforward_comp_map`. That is what makes the coherence
provable at all; for a pseudofunctorial pushforward it would be an independent assumption, as the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackAssoc.lean` record. Composition of
morphisms of ringed spaces is definitionally associative, so no transport along
`CategoryTheory.Category.assoc` appears in the statement.

The transposed identity is split across fifteen private steps. That is not stylistic: the single
combined proof exceeds the default heartbeat limit, because each junction between two spellings
of one object costs a definitional unfolding of the pullback of sheaves of modules, and a
declaration gets one heartbeat budget however many junctions it contains.

## References

* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction 
open AlgebraicGeometry AlgebraicGeometry.RingedSpace
open Stacks.ClosedImmersion Stacks.Thickenings

universe u

namespace RingedSpaceModuleAdjunction

/-! ### Two morphisms out of a pullback -/

/-- **Two morphisms out of a pullback agree as soon as their transposes do.** -/
theorem hom_ext_of_unit {Zr Wr : RingedSpace.{u, u}} (f : Zr ⟶ Wr)
    {Ms : SheafOfModules.{u} (structureSheafRing Wr)}
    {N : SheafOfModules.{u} (structureSheafRing Zr)}
    {α β : (modulePullback f).obj Ms ⟶ N}
    (h : (modulePullbackPushforwardAdjunction f).unit.app Ms ≫ (modulePushforward f).map α =
      (modulePullbackPushforwardAdjunction f).unit.app Ms ≫ (modulePushforward f).map β) :
    α = β :=
  ((modulePullbackPushforwardAdjunction f).homEquiv Ms N).injective
    (((modulePullbackPushforwardAdjunction f).homEquiv_unit Ms N α).trans
      (h.trans (((modulePullbackPushforwardAdjunction f).homEquiv_unit Ms N β).symm)))

/-- **Pullback along a morphism is transported along an equality of morphisms.** The pullback
composition isomorphism of `f` and `g` is carried to that of an equal `f'` by the two transports
of `CategoryTheory.eqToHom`. -/
theorem modulePullbackComp_congr_left {Zr Wr Vr : RingedSpace.{u, u}} {f f' : Zr ⟶ Wr}
    (hf : f = f') (g : Wr ⟶ Vr) (M : SheafOfModules.{u} (structureSheafRing Vr)) :
    (modulePullbackComp f' g).hom.app M ≫
        eqToHom (congrArg (fun z => (modulePullback z).obj ((modulePullback g).obj M)) hf.symm) =
      eqToHom (congrArg (fun z => (modulePullback (z ≫ g)).obj M) hf.symm) ≫
        (modulePullbackComp f g).hom.app M := by
  subst hf
  rw [eqToHom_refl, eqToHom_refl, Category.comp_id, Category.id_comp]

/-- **A pullback of a morphism of modules is transported along an equality of morphisms.** -/
theorem modulePullback_map_congr {Zr Wr : RingedSpace.{u, u}} {f f' : Zr ⟶ Wr} (hf : f = f')
    {M N : SheafOfModules.{u} (structureSheafRing Wr)} (φ : M ⟶ N) :
    (modulePullback f').map φ ≫
        eqToHom (congrArg (fun z => (modulePullback z).obj N) hf.symm) =
      eqToHom (congrArg (fun z => (modulePullback z).obj M) hf.symm) ≫
        (modulePullback f).map φ := by
  subst hf
  rw [eqToHom_refl, eqToHom_refl, Category.comp_id, Category.id_comp]

/-! ### The associativity coherence of the pullback composition isomorphism -/

section Assoc

variable {A B C D : RingedSpace.{u, u}} (p : A ⟶ B) (q : B ⟶ C) (r : C ⟶ D)
  (M : SheafOfModules.{u} (structureSheafRing D))

/-- Naturality of the unit of `p^* ⊣ p_*` at the pullback composition isomorphism of `q` and
`r`. -/
private theorem unit_naturality_modulePullbackComp :
    ((modulePullbackComp q r).hom.app M) ≫ (modulePullbackPushforwardAdjunction p).unit.app
        ((modulePullback q).obj ((modulePullback r).obj M)) =
      ((modulePullbackPushforwardAdjunction p).unit.app ((modulePullback (q ≫ r)).obj M)) ≫
          (modulePushforward p).map ((modulePullback p).map ((modulePullbackComp q r).hom.app M))
          :=
  (modulePullbackPushforwardAdjunction p).unit.naturality _

/-- A morphism followed by a functor applied to a composite splits into two successive steps. -/
private theorem comp_map_comp_eq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X : D} {Y Z W : C} (U : X ⟶ F.obj Y) (a : Y ⟶ Z) (b : Z ⟶ W) :
    U ≫ F.map (a ≫ b) = (U ≫ F.map a) ≫ F.map b := by
  rw [F.map_comp, Category.assoc]

private theorem sL12 :
    (modulePullbackPushforwardAdjunction (p ≫ q ≫ r)).unit.app M ≫
        (modulePushforward (p ≫ q ≫ r)).map (((modulePullbackComp p (q ≫ r)).hom.app M) ≫
            (modulePullback p).map ((modulePullbackComp q r).hom.app M)) =
      ((modulePullbackPushforwardAdjunction (p ≫ q ≫ r)).unit.app M ≫ (modulePushforward (p ≫ q ≫
          r)).map ((modulePullbackComp p (q ≫ r)).hom.app M)) ≫
        (modulePushforward (p ≫ q ≫ r)).map ((modulePullback p).map ((modulePullbackComp q
            r).hom.app M)) :=
  comp_map_comp_eq (modulePushforward (p ≫ q ≫ r)) _ _ _

private theorem sL3 :
    ((modulePullbackPushforwardAdjunction (p ≫ q ≫ r)).unit.app M ≫ (modulePushforward (p ≫ q ≫
        r)).map ((modulePullbackComp p (q ≫ r)).hom.app M)) ≫
        (modulePushforward (p ≫ q ≫ r)).map ((modulePullback p).map ((modulePullbackComp q
            r).hom.app M)) =
      ((modulePullbackPushforwardAdjunction (q ≫ r)).unit.app M ≫ (modulePushforward (q ≫ r)).map
          ((modulePullbackPushforwardAdjunction p).unit.app ((modulePullback (q ≫ r)).obj M))) ≫
        (modulePushforward (p ≫ q ≫ r)).map ((modulePullback p).map ((modulePullbackComp q
            r).hom.app M)) :=
  eq_whisker (unit_modulePullbackComp p (q ≫ r) M).symm _

private theorem sL4 :
    ((modulePullbackPushforwardAdjunction (q ≫ r)).unit.app M ≫ (modulePushforward (q ≫ r)).map
        ((modulePullbackPushforwardAdjunction p).unit.app ((modulePullback (q ≫ r)).obj M))) ≫
        (modulePushforward (p ≫ q ≫ r)).map ((modulePullback p).map ((modulePullbackComp q
            r).hom.app M)) =
      ((modulePullbackPushforwardAdjunction (q ≫ r)).unit.app M ≫ (modulePushforward (q ≫ r)).map
          ((modulePullbackPushforwardAdjunction p).unit.app ((modulePullback (q ≫ r)).obj M))) ≫
        (modulePushforward (q ≫ r)).map ((modulePushforward p).map ((modulePullback p).map
            ((modulePullbackComp q r).hom.app M))) :=
  whisker_eq _ (modulePushforward_comp_map p (q ≫ r) _)

private theorem sL56 :
    ((modulePullbackPushforwardAdjunction (q ≫ r)).unit.app M ≫ (modulePushforward (q ≫ r)).map
        ((modulePullbackPushforwardAdjunction p).unit.app ((modulePullback (q ≫ r)).obj M))) ≫
        (modulePushforward (q ≫ r)).map ((modulePushforward p).map ((modulePullback p).map
            ((modulePullbackComp q r).hom.app M))) =
      (modulePullbackPushforwardAdjunction (q ≫ r)).unit.app M ≫
        (modulePushforward (q ≫ r)).map (((modulePullbackPushforwardAdjunction p).unit.app
            ((modulePullback (q ≫ r)).obj M)) ≫ (modulePushforward p).map ((modulePullback p).map
            ((modulePullbackComp q r).hom.app M))) :=
  (comp_map_comp_eq _ _ _ _).symm

private theorem sL7 :
    (modulePullbackPushforwardAdjunction (q ≫ r)).unit.app M ≫
        (modulePushforward (q ≫ r)).map (((modulePullbackPushforwardAdjunction p).unit.app
            ((modulePullback (q ≫ r)).obj M)) ≫ (modulePushforward p).map ((modulePullback p).map
            ((modulePullbackComp q r).hom.app M))) =
      (modulePullbackPushforwardAdjunction (q ≫ r)).unit.app M ≫
        (modulePushforward (q ≫ r)).map (((modulePullbackComp q r).hom.app M) ≫
            (modulePullbackPushforwardAdjunction p).unit.app ((modulePullback q).obj
            ((modulePullback r).obj M))) :=
  whisker_eq _ (congrArg (modulePushforward (q ≫ r)).map
    (unit_naturality_modulePullbackComp p q r M).symm)

private theorem sL89 :
    (modulePullbackPushforwardAdjunction (q ≫ r)).unit.app M ≫
        (modulePushforward (q ≫ r)).map (((modulePullbackComp q r).hom.app M) ≫
            (modulePullbackPushforwardAdjunction p).unit.app ((modulePullback q).obj
            ((modulePullback r).obj M))) =
      ((modulePullbackPushforwardAdjunction (q ≫ r)).unit.app M ≫ (modulePushforward (q ≫ r)).map
          ((modulePullbackComp q r).hom.app M)) ≫
        (modulePushforward (q ≫ r)).map ((modulePullbackPushforwardAdjunction p).unit.app
            ((modulePullback q).obj ((modulePullback r).obj M))) :=
  comp_map_comp_eq (modulePushforward (q ≫ r)) _ _ _

private theorem sL10 :
    ((modulePullbackPushforwardAdjunction (q ≫ r)).unit.app M ≫ (modulePushforward (q ≫ r)).map
        ((modulePullbackComp q r).hom.app M)) ≫
        (modulePushforward (q ≫ r)).map ((modulePullbackPushforwardAdjunction p).unit.app
            ((modulePullback q).obj ((modulePullback r).obj M))) =
      ((modulePullbackPushforwardAdjunction r).unit.app M ≫ (modulePushforward r).map
          ((modulePullbackPushforwardAdjunction q).unit.app ((modulePullback r).obj M))) ≫
        (modulePushforward (q ≫ r)).map ((modulePullbackPushforwardAdjunction p).unit.app
            ((modulePullback q).obj ((modulePullback r).obj M))) :=
  eq_whisker (unit_modulePullbackComp q r M).symm _

private theorem sL11 :
    ((modulePullbackPushforwardAdjunction r).unit.app M ≫ (modulePushforward r).map
        ((modulePullbackPushforwardAdjunction q).unit.app ((modulePullback r).obj M))) ≫
        (modulePushforward (q ≫ r)).map ((modulePullbackPushforwardAdjunction p).unit.app
            ((modulePullback q).obj ((modulePullback r).obj M))) =
      ((modulePullbackPushforwardAdjunction r).unit.app M ≫ (modulePushforward r).map
          ((modulePullbackPushforwardAdjunction q).unit.app ((modulePullback r).obj M))) ≫
        (modulePushforward r).map ((modulePushforward q).map ((modulePullbackPushforwardAdjunction
            p).unit.app ((modulePullback q).obj ((modulePullback r).obj M)))) :=
  whisker_eq _ (modulePushforward_comp_map q r _)

private theorem sL1213 :
    ((modulePullbackPushforwardAdjunction r).unit.app M ≫ (modulePushforward r).map
        ((modulePullbackPushforwardAdjunction q).unit.app ((modulePullback r).obj M))) ≫
        (modulePushforward r).map ((modulePushforward q).map ((modulePullbackPushforwardAdjunction
            p).unit.app ((modulePullback q).obj ((modulePullback r).obj M)))) =
      (modulePullbackPushforwardAdjunction r).unit.app M ≫
        (modulePushforward r).map (((modulePullbackPushforwardAdjunction q).unit.app
            ((modulePullback r).obj M)) ≫ (modulePushforward q).map
            ((modulePullbackPushforwardAdjunction p).unit.app ((modulePullback q).obj
            ((modulePullback r).obj M)))) :=
  (comp_map_comp_eq _ _ _ _).symm

private theorem sR12 :
    (modulePullbackPushforwardAdjunction (p ≫ q ≫ r)).unit.app M ≫
        (modulePushforward (p ≫ q ≫ r)).map (((modulePullbackComp (p ≫ q) r).hom.app M) ≫
            (modulePullbackComp p q).hom.app ((modulePullback r).obj M)) =
      ((modulePullbackPushforwardAdjunction (p ≫ q ≫ r)).unit.app M ≫ (modulePushforward (p ≫ q ≫
          r)).map ((modulePullbackComp (p ≫ q) r).hom.app M)) ≫
        (modulePushforward (p ≫ q ≫ r)).map ((modulePullbackComp p q).hom.app ((modulePullback
            r).obj M)) :=
  comp_map_comp_eq (modulePushforward (p ≫ q ≫ r)) _ _ _

private theorem sR3 :
    ((modulePullbackPushforwardAdjunction (p ≫ q ≫ r)).unit.app M ≫ (modulePushforward (p ≫ q ≫
        r)).map ((modulePullbackComp (p ≫ q) r).hom.app M)) ≫
        (modulePushforward (p ≫ q ≫ r)).map ((modulePullbackComp p q).hom.app ((modulePullback
            r).obj M)) =
      ((modulePullbackPushforwardAdjunction r).unit.app M ≫ (modulePushforward r).map
          ((modulePullbackPushforwardAdjunction (p ≫ q)).unit.app ((modulePullback r).obj M))) ≫
        (modulePushforward (p ≫ q ≫ r)).map ((modulePullbackComp p q).hom.app ((modulePullback
            r).obj M)) :=
  eq_whisker (unit_modulePullbackComp (p ≫ q) r M).symm _

private theorem sR4 :
    ((modulePullbackPushforwardAdjunction r).unit.app M ≫ (modulePushforward r).map
        ((modulePullbackPushforwardAdjunction (p ≫ q)).unit.app ((modulePullback r).obj M))) ≫
        (modulePushforward (p ≫ q ≫ r)).map ((modulePullbackComp p q).hom.app ((modulePullback
            r).obj M)) =
      ((modulePullbackPushforwardAdjunction r).unit.app M ≫ (modulePushforward r).map
          ((modulePullbackPushforwardAdjunction (p ≫ q)).unit.app ((modulePullback r).obj M))) ≫
        (modulePushforward r).map ((modulePushforward (p ≫ q)).map ((modulePullbackComp p
            q).hom.app ((modulePullback r).obj M))) :=
  whisker_eq _ (modulePushforward_comp_map (p ≫ q) r _)

private theorem sR56 :
    ((modulePullbackPushforwardAdjunction r).unit.app M ≫ (modulePushforward r).map
        ((modulePullbackPushforwardAdjunction (p ≫ q)).unit.app ((modulePullback r).obj M))) ≫
        (modulePushforward r).map ((modulePushforward (p ≫ q)).map ((modulePullbackComp p
            q).hom.app ((modulePullback r).obj M))) =
      (modulePullbackPushforwardAdjunction r).unit.app M ≫
        (modulePushforward r).map (((modulePullbackPushforwardAdjunction (p ≫ q)).unit.app
            ((modulePullback r).obj M)) ≫ (modulePushforward (p ≫ q)).map ((modulePullbackComp p
            q).hom.app ((modulePullback r).obj M))) :=
  (comp_map_comp_eq _ _ _ _).symm

private theorem sR7 :
    (modulePullbackPushforwardAdjunction r).unit.app M ≫
        (modulePushforward r).map (((modulePullbackPushforwardAdjunction (p ≫ q)).unit.app
            ((modulePullback r).obj M)) ≫ (modulePushforward (p ≫ q)).map ((modulePullbackComp p
            q).hom.app ((modulePullback r).obj M))) =
      (modulePullbackPushforwardAdjunction r).unit.app M ≫
        (modulePushforward r).map (((modulePullbackPushforwardAdjunction q).unit.app
            ((modulePullback r).obj M)) ≫ (modulePushforward q).map
            ((modulePullbackPushforwardAdjunction p).unit.app ((modulePullback q).obj
            ((modulePullback r).obj M)))) :=
  whisker_eq _ (congrArg (modulePushforward r).map
    (unit_modulePullbackComp p q ((modulePullback r).obj M)).symm)

/-- The transpose of the inner comparison of the two ways to compare `r^* q^* p^*` with `(p ≫ q ≫
    r)^*`, computed as a composite of three units. -/
private theorem transpose_modulePullbackComp_assoc_left :
    (modulePullbackPushforwardAdjunction (p ≫ q ≫ r)).unit.app M ≫
        (modulePushforward (p ≫ q ≫ r)).map (((modulePullbackComp p (q ≫ r)).hom.app M) ≫
            (modulePullback p).map ((modulePullbackComp q r).hom.app M)) =
      (modulePullbackPushforwardAdjunction r).unit.app M ≫
        (modulePushforward r).map (((modulePullbackPushforwardAdjunction q).unit.app
            ((modulePullback r).obj M)) ≫ (modulePushforward q).map
            ((modulePullbackPushforwardAdjunction p).unit.app ((modulePullback q).obj
            ((modulePullback r).obj M)))) :=
  ((sL12 p q r M).trans ((sL3 p q r M).trans ((sL4 p q r M).trans ((sL56 p q r M).trans ((sL7 p q
      r M).trans ((sL89 p q r M).trans ((sL10 p q r M).trans ((sL11 p q r M).trans (sL1213 p q r
      M)))))))))

/-- The transpose of the outer comparison, computed as the same composite of three units. -/
private theorem transpose_modulePullbackComp_assoc_right :
    (modulePullbackPushforwardAdjunction (p ≫ q ≫ r)).unit.app M ≫
        (modulePushforward (p ≫ q ≫ r)).map (((modulePullbackComp (p ≫ q) r).hom.app M) ≫
            (modulePullbackComp p q).hom.app ((modulePullback r).obj M)) =
      (modulePullbackPushforwardAdjunction r).unit.app M ≫
        (modulePushforward r).map (((modulePullbackPushforwardAdjunction q).unit.app
            ((modulePullback r).obj M)) ≫ (modulePushforward q).map
            ((modulePullbackPushforwardAdjunction p).unit.app ((modulePullback q).obj
            ((modulePullback r).obj M)))) :=
  ((sR12 p q r M).trans ((sR3 p q r M).trans ((sR4 p q r M).trans ((sR56 p q r M).trans (sR7 p q r
      M)))))

/-- **The associativity coherence of the pullback composition isomorphism.** For three composable
morphisms of ringed spaces the two ways of comparing `r^* q^* p^*` with `(p ≫ q ≫ r)^*` agree:
comparing `p` against `q ≫ r` and then `q` against `r`, or comparing `p ≫ q` against `r` and then
`p` against `q`.

This is the pentagon coherence of `RingedSpaceModuleAdjunction.modulePullback`, and it is the only
coherence proved here. Together with the two unit laws
`AlgebraicGeometry.RingedSpaceThickening.modulePullbackComp_id_hom_app` and
`RingedSpaceModuleAdjunction.modulePullbackComp_id_right_hom_app` it is the whole coherence of a
pseudofunctor on ringed spaces whose composition isomorphism is
`RingedSpaceModuleAdjunction.modulePullbackComp` and whose unit isomorphism is
`RingedSpaceModuleAdjunction.modulePullbackId`. The bundled `CategoryTheory.Pseudofunctor` is not
assembled from them anywhere in this repository; the three coherences are used directly.

It is proved by transposing along the adjunction, where the corresponding pushforward statement is
`RingedSpaceModuleAdjunction.modulePushforward_comp_map`, an equality on the nose. -/
theorem modulePullbackComp_assoc :
    (modulePullbackComp p (q ≫ r)).hom.app M ≫
        (modulePullback p).map ((modulePullbackComp q r).hom.app M) =
      (modulePullbackComp (p ≫ q) r).hom.app M ≫
        (modulePullbackComp p q).hom.app ((modulePullback r).obj M) :=
  hom_ext_of_unit (p ≫ q ≫ r)
    ((transpose_modulePullbackComp_assoc_left p q r M).trans
      (transpose_modulePullbackComp_assoc_right p q r M).symm)

end Assoc

end RingedSpaceModuleAdjunction

namespace Stacks.ClosedImmersion

/-- **The conormal-sheaf map of a square is transported along an equality of its top edge.** The
`CategoryTheory.eqToHom` comparing the two conormal sheaves absorbs the change of edge; the two
squares are the same proposition, so the proofs of commutativity need not be related. -/
theorem conormalSheafMap_comp_eqToHom {Zr Zr' Wr Wr' : RingedSpace.{u, u}} {t t' : Zr ⟶ Zr'}
    {j : Wr ⟶ Wr'} {f : Zr ⟶ Wr} {k : Zr' ⟶ Wr'} (h : t = t')
    (comm : t ≫ k = f ≫ j) (comm' : t' ≫ k = f ≫ j) :
    conormalSheafMap comm ≫ eqToHom (congrArg (fun p => conormalSheaf p) h) =
      conormalSheafMap comm' := by
  subst h
  rw [eqToHom_refl, Category.comp_id]

end Stacks.ClosedImmersion

namespace Stacks.Immersion

variable {Z Z' X W W' : Scheme.{u}}

/-- **The map of conormal sheaves of a square is transported along equalities of its two vertical
edges.** Only the left edge changes the type of the map, through the pullback it is taken along;
the right edge enters only through the commutativity of the square, which is a proposition. -/
theorem immersionConormalSheafMap_congr (i : Z ⟶ Z') (j : W ⟶ W') [IsImmersion i]
    [IsImmersion j] {f f' : Z ⟶ W} (hf : f = f') {k k' : Z' ⟶ W'} (hk : k = k')
    (comm : i.toLRSHom.toShHom ≫ k.toLRSHom.toShHom =
      f.toLRSHom.toShHom ≫ j.toLRSHom.toShHom)
    (comm' : i.toLRSHom.toShHom ≫ k'.toLRSHom.toShHom =
      f'.toLRSHom.toShHom ≫ j.toLRSHom.toShHom) :
    immersionConormalSheafMap i j f' k' comm' =
      eqToHom (congrArg (fun p : Z ⟶ W =>
          (modulePullback p.toLRSHom.toShHom).obj (immersionConormalSheaf j)) hf.symm) ≫
        immersionConormalSheafMap i j f k comm := by
  subst hf
  subst hk
  rw [eqToHom_refl, Category.id_comp]

/-! ### The canonical map of a restriction square -/

/-- A re-association used twice in the proof of
`Stacks.Immersion.modulePullbackRestrictIso_comp_conormalSheafSelfRestrictIso`, stated so that
the two large module terms it is applied at are written once. -/
private theorem comp_reassoc {C : Type*} [Category C] {A A' B D E F : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : E ⟶ F) (u : A ⟶ A') (v : A' ⟶ D) (w : A' ⟶ F)
    (h1 : a ≫ b = u ≫ v) (h2 : v ≫ c ≫ d = w) :
    a ≫ (b ≫ c) ≫ d = u ≫ w := by
  subst h2
  simp only [Category.assoc]
  rw [← Category.assoc a b, h1, Category.assoc]

/-- **The restriction comparison of conormal sheaves is the conormal-sheaf map of the restriction
square, before the final identification.** The composite of
`AlgebraicGeometry.RingedSpace.modulePullbackRestrictIso` with
`Stacks.Immersion.conormalSheafSelfRestrictIso` is the pullback of
`Stacks.Immersion.conormalSheafSelfIso` followed by the ringed-space conormal-sheaf map of the
restriction square. -/
private theorem modulePullbackRestrictIso_comp_conormalSheafSelfRestrictIso_aux (i : Z ⟶ X)
    [IsImmersion i] (V : X.Opens) :
    (modulePullbackRestrictIso Z.toSheafedSpace
          ((Opens.map i.toLRSHom.toShHom.hom.base).obj V)).hom.app (immersionConormalSheaf i) ≫
        (conormalSheafSelfRestrictIso i V).hom =
      (modulePullback (i ⁻¹ᵁ V).ι.toLRSHom.toShHom).map (conormalSheafSelfIso i).inv ≫
        conormalSheafMap (toShHom_square (morphismRestrict_ι i V)) :=
  (congrArg (fun z => (modulePullbackRestrictIso Z.toSheafedSpace
        ((Opens.map i.toLRSHom.toShHom.hom.base).obj V)).hom.app (immersionConormalSheaf i) ≫ z)
      (conormalSheafSelfRestrictIso_hom i V)).trans
    (comp_reassoc _ _ _ _ _ _ _
      ((modulePullbackRestrictIso Z.toSheafedSpace
        ((Opens.map i.toLRSHom.toShHom.hom.base).obj V)).hom.naturality
          (conormalSheafSelfIso i).inv).symm
      ((Category.assoc _ _ _).symm.trans
        ((congrArg
            (fun z => z ≫ eqToHom (congrArg (fun p => conormalSheaf p)
              (restrictHom_eq_morphismRestrictShHom i V)))
            (conormalSheafMap_restrictHom_comp_ofRestrict i.toLRSHom.toShHom V).symm).trans
          (conormalSheafMap_comp_eqToHom (restrictHom_eq_morphismRestrictShHom i V) _ _))))

/-- **The restriction comparison of conormal sheaves is the canonical map of the restriction
square.** For an immersion of schemes `i : Z ⟶ X` and an open `V` of `X`, the composite
```
ι_{i⁻¹V}^* 𝒞_{Z/X} ≅ 𝒞_{Z/X}|_{i⁻¹V} ≅ 𝒞_{i ∣_ V}
```
of `AlgebraicGeometry.RingedSpace.modulePullbackRestrictIso`,
`Stacks.Immersion.conormalSheafSelfRestrictIso` and `Stacks.Immersion.conormalSheafSelfIso` is the
map of [Stacks Project, Tag 01R4] induced by the square `(i ∣_ V) ≫ ι_V = ι_{i⁻¹V} ≫ i`.

It is this identification that makes the composition law
`Stacks.Immersion.immersionConormalSheafMap_comp` available to the restriction comparison, and so
transports a map of conormal sheaves from an open of `X` to a smaller open. -/
theorem modulePullbackRestrictIso_comp_conormalSheafSelfRestrictIso (i : Z ⟶ X) [IsImmersion i]
    (V : X.Opens) :
    (modulePullbackRestrictIso Z.toSheafedSpace (i ⁻¹ᵁ V)).hom.app (immersionConormalSheaf i) ≫
        (conormalSheafSelfRestrictIso i V).hom ≫ (conormalSheafSelfIso (i ∣_ V)).hom =
      immersionConormalSheafMap (i ∣_ V) i (i ⁻¹ᵁ V).ι V.ι
        (toShHom_square (morphismRestrict_ι i V)) :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ (conormalSheafSelfIso (i ∣_ V)).hom)
        (modulePullbackRestrictIso_comp_conormalSheafSelfRestrictIso_aux i V)).trans
      (Category.assoc _ _ _))

end Stacks.Immersion

end
