module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModuleUnitCompLaw
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackCompUnit

/-!
# The comparison of the units of étale restriction along a composite

Let `h : D ⟶ A` and `g : A ⟶ C` be étale morphisms of algebraic spaces over a scheme `S` of a big
fppf site `B`, and let `M` be a module on the small étale site of `C`. This file carries the
composition law for the units of étale restriction of sheaves of sets,
`AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction_unit_comp_app`, over to modules: the
unit at `M` of the adjunction composed from the étale restrictions along `g` and `h` is read, on
a section, as the unit of étale restriction along `h ≫ g`.

## Main results

* `Stacks.comp_congr_right`, `Stacks.comp_map_id` and `Stacks.eq_atType`: postcomposition with an
  equal factor, absorption of a functor's image of an identity, and an equation read at a
  definitionally equal spelling of its type. All three are stated on variables, which is what
  makes each use **one** definitional step instead of a search.
* `AlgebraicGeometry.Space.etaleModulePullbackComp_hom_app_eq_id` and
  `AlgebraicGeometry.Space.modulePushforward_map_etaleModulePullbackComp_hom_app`: the comparison
  of iterated étale restriction with restriction along the composite is the identity, at a module
  and under the direct image.
* `AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforward_unit_app` and
  `AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforward_unit_val_app`: the direct
  image along `g` of the unit of étale restriction along `h`, as a morphism of sheaves of sets and
  on a section.
* `AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction_unit_comp_app_moduleSetSheaf` and
  `AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction_unit_comp_val_app`: the composition
  law of the units of étale restriction of sheaves of sets at the sheaf of sets underlying a
  module, and on a section.
* `AlgebraicGeometry.Space.etaleModulePullbackCompInner_unit_app`: the unit of the composite
  adjunction as a composite of three factors. The composite unit as the inner unit followed by the
  direct image of the comparison of iterated restrictions is
  `AlgebraicGeometry.Space.etaleModulePullbackCompAdjunction_unit_app` of
  `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackCompUnit.lean`, which this file
  imports and consumes rather than reproves.
* `AlgebraicGeometry.Space.modulePushforwardCompIso_hom_app_val_app_setRestriction`: the
  comparison of the two direct images of modules, on a section, with its target read as an
  iterated étale restriction of sheaves of sets.
* `AlgebraicGeometry.Space.innerUnitVal₁₂`, `AlgebraicGeometry.Space.innerUnitVal₃₄` and
  `AlgebraicGeometry.Space.innerUnitVal₅₆`: the value of the unit of the composite adjunction on a
  section, in three segments, the last ending at the unit of étale restriction along `h ≫ g`.

## Implementation notes

Several declarations here are `def`s whose type is inferred from a `.trans` of equations rather
than `theorem`s with a written statement. Writing such a statement makes the elaborator unify two
spellings of an object inside a `Quiver.Hom` or a section type, and it answers by unfolding
`AlgebraicGeometry.Space.smallEtaleDirectImage` or `AlgebraicGeometry.Space.modulePushforward` —
three functors deep — and exhausts the heartbeat budget; computing the type from a `.trans` of two
equations whose own types are already right costs nothing. So the rule throughout is: **never
write a statement that mixes two spellings; let `congrArg` and `Eq.trans` determine the type, and
move between spellings one definitional step at a time**, with `Stacks.eq_atType` or with the
three components of `AlgebraicGeometry.Space.smallToposMorphismTypeU_comp` stated below. The
measurements behind the rule: `moduleSetSheaf` (a reducible abbreviation) crosses a restriction
functor for free, while `(CategoryTheory.Sheaf.moduleSheafFunctor _).obj` at the same place does
not; one restriction functor crosses for free, two do not; and the composite of two free crossings
is not free, which is why those components come in three pieces instead of one.

## What this leaves

The comparison of the units

```
(etaleModulePullbackCompAdjunction B S hS h g hh hg hhg).unit =
  (etaleModulePullbackAdjunction B S hS (h ≫ g) hhg).unit
```

— and with it `ModulePullbackCompIsoEtaleRestriction` — is proved in
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleModuleUnitCompJoin.lean`. The absorption of the fourth
factor and the join of `innerUnitVal₁₂` with `innerUnitVal₃₄` are proved in
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleModuleUnitCompAbsorption.lean`, as
`AlgebraicGeometry.Space.innerUnit_comp_modulePushforward_map_eq_self` and
`AlgebraicGeometry.Space.innerUnitVal`; neither is closed by a transitivity on variables. The
absorption is closed by removing the mismatch at its source — the fourth factor is read at the
*endomorphism* hom type of the iterated spelling, after which `Stacks.comp_congr_right` and
`CategoryTheory.Category.comp_id` match syntactically — and the join is closed by decomposing the
inner unit's three factors in **one** step with a threefold `modulesHom_comp_comp_val_app_apply`
stated on variables, instead of two steps through the middle object.

## References

* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 04W6](https://stacks.math.columbia.edu/tag/04W6)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

universe u

/-- Postcomposition respects equality of the second factor. Stated on variables, so that the
composite is a clean application and not a beta-redex. -/
theorem Stacks.comp_congr_right {CC : Type*} [CategoryTheory.Category CC] {X Y Z : CC}
    (a : X ⟶ Y) {b c : Y ⟶ Z} (h : b = c) : a ≫ b = a ≫ c := by rw [h]

/-- A composite whose second factor is a functor's image of an identity is its first factor.
Stated on variables, so that no spelling of the identity's object has to be matched against a
concrete term. -/
theorem Stacks.comp_map_id {CC : Type*} [CategoryTheory.Category CC] {DD : Type*}
    [CategoryTheory.Category DD] (F : CC ⥤ DD) {X : CC} {V : DD} (a : V ⟶ F.obj X) :
    a ≫ F.map (CategoryTheory.CategoryStruct.id X) = a := by
  rw [F.map_id, CategoryTheory.Category.comp_id]

/-- An equation, read at a chosen definitionally equal spelling `α` of its type. Each use is one
definitional step, which is what keeps the unifier from unfolding a composite of functors. -/
theorem Stacks.eq_atType {α : Sort u} {a b : α} (e : a = b) : a = b := e

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {A C D : AlgebraicSpaces B S hS}
variable (h : D ⟶ A) (g : A ⟶ C) (hh : IsEtale B S hS h.hom) (hg : IsEtale B S hS g.hom)
    (hhg : IsEtale B S hS (h ≫ g).hom)
variable (M : Modules.{u, u} B S hS C.1 C.2)

/-! ### Components of the comparison of direct images of sheaves of sets -/

/-- The component of `smallToposMorphismTypeU_comp h g` at the sheaf of sets underlying the
iterated étale restriction of `M` along `g` and then `h`, spelled with `Sheaf.moduleSheafFunctor`,
is its component at the same sheaf spelled with `moduleSetSheaf`. -/
theorem smallToposMorphismTypeU_comp_hom_app_moduleSetSheaf :
    (smallToposMorphismTypeU_comp B S hS h g).hom.app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS D)).obj
          ((etaleModulePullback.{u, u} B S hS h hh).obj
            ((etaleModulePullback.{u, u} B S hS g hg).obj M))) =
      (smallToposMorphismTypeU_comp B S hS h g).hom.app
        (moduleSetSheaf B S hS D
          ((etaleModulePullback.{u, u} B S hS h hh).obj
            ((etaleModulePullback.{u, u} B S hS g hg).obj M))) := rfl

/-- The component of `smallToposMorphismTypeU_comp h g` at the sheaf of sets underlying the
iterated étale restriction of `M` along `g` and then `h` is its component at the étale restriction
along `h` of the sheaf of sets underlying the restriction of `M` along `g`. -/
theorem smallToposMorphismTypeU_comp_hom_app_setRestriction :
    (smallToposMorphismTypeU_comp B S hS h g).hom.app
        (moduleSetSheaf B S hS D
          ((etaleModulePullback.{u, u} B S hS h hh).obj
            ((etaleModulePullback.{u, u} B S hS g hg).obj M))) =
      (smallToposMorphismTypeU_comp B S hS h g).hom.app
        ((smallEtaleSetRestriction B S hS h hh).obj
          (moduleSetSheaf B S hS A ((etaleModulePullback.{u, u} B S hS g hg).obj M))) := rfl

/-- The component of `smallToposMorphismTypeU_comp h g` at the étale restriction along `h` of the
sheaf of sets underlying the restriction of `M` along `g` is its component at the iterated étale
restriction, along `g` and then `h`, of the sheaf of sets underlying `M`. -/
theorem smallToposMorphismTypeU_comp_hom_app_setRestriction_comp :
    (smallToposMorphismTypeU_comp B S hS h g).hom.app
        ((smallEtaleSetRestriction B S hS h hh).obj
          (moduleSetSheaf B S hS A ((etaleModulePullback.{u, u} B S hS g hg).obj M))) =
      (smallToposMorphismTypeU_comp B S hS h g).hom.app
        ((smallEtaleSetRestriction B S hS h hh).obj
          ((smallEtaleSetRestriction B S hS g hg).obj (moduleSetSheaf B S hS C M))) := rfl

/-! ### Units of étale restriction of modules along a composite -/

/-- The component at `M` of `etaleModulePullbackComp`, comparing iterated étale restriction along
`g` and then `h` with étale restriction along `h ≫ g`, is the identity. -/
theorem etaleModulePullbackComp_hom_app_eq_id :
    (etaleModulePullbackComp B S hS h g hh hg hhg).hom.app M =
      (show (etaleModulePullback.{u, u} B S hS h hh).obj
            ((etaleModulePullback.{u, u} B S hS g hg).obj M) ⟶
          (etaleModulePullback.{u, u} B S hS (h ≫ g) hhg).obj M from 𝟙 _) :=
  rfl

/-- The direct image along `h ≫ g` of the component at `M` of `etaleModulePullbackComp` is the
identity. -/
def modulePushforward_map_etaleModulePullbackComp_hom_app :=
  (congrArg (modulePushforward B S hS (h ≫ g)).map
      (etaleModulePullbackComp_hom_app_eq_id B S hS h g hh hg hhg M)).trans
    (CategoryTheory.Functor.map_id _ _)

/-- The morphism of sheaves of sets underlying the direct image along `g` of the unit of étale
restriction of modules along `h`, at the restriction of `M` along `g`, is the direct image along
`g` of the corresponding morphism of sheaves of sets given by
`moduleSheafFunctor_map_etaleModulePullbackAdjunction_unit_app`. -/
def moduleSheafFunctor_map_modulePushforward_unit_app :=
  (moduleSheafFunctor_map_modulePushforward_map B S hS g
      ((etaleModulePullbackAdjunction B S hS h hh).unit.app
        ((etaleModulePullback.{u, u} B S hS g hg).obj M))).trans
    (congrArg (smallEtaleDirectImage B S hS g).map
      (moduleSheafFunctor_map_etaleModulePullbackAdjunction_unit_app B S hS h hh
        ((etaleModulePullback.{u, u} B S hS g hg).obj M)))

/-- The unit at `M` of the composite of the étale restriction adjunctions along `g` and `h`,
transported along `modulePushforwardCompIso h g`, is the unit along `g`, followed by the direct
image along `g` of the unit along `h`, followed by the component of
`modulePushforwardCompIso h g`. -/
theorem etaleModulePullbackCompInner_unit_app :
    (((etaleModulePullbackAdjunction B S hS g hg).comp
          (etaleModulePullbackAdjunction B S hS h hh)).ofNatIsoRight
            (modulePushforwardCompIso B S hS h g)).unit.app M =
      (etaleModulePullbackAdjunction B S hS g hg).unit.app M ≫
        (modulePushforward B S hS g).map
          ((etaleModulePullbackAdjunction B S hS h hh).unit.app
            ((etaleModulePullback.{u, u} B S hS g hg).obj M)) ≫
        (modulePushforwardCompIso B S hS h g).hom.app
          ((etaleModulePullback.{u, u} B S hS h hh).obj
            ((etaleModulePullback.{u, u} B S hS g hg).obj M)) :=
  Adjunction.comp_ofNatIsoRight_unit_app (etaleModulePullbackAdjunction B S hS g hg)
    (etaleModulePullbackAdjunction B S hS h hh) (modulePushforwardCompIso B S hS h g) M

/-- At the sheaf of sets underlying `M`, the unit of étale restriction of sheaves of sets along
`g`, followed by the direct image along `g` of the unit along `h`, followed by the component of
`smallToposMorphismTypeU_comp h g`, is the unit of étale restriction along `h ≫ g`. -/
theorem smallEtaleSetRestrictionAdjunction_unit_comp_app_moduleSetSheaf :
    (smallEtaleSetRestrictionAdjunction B S hS g hg).unit.app
          (moduleSetSheaf B S hS C M) ≫
        (smallEtaleDirectImage B S hS g).map
          ((smallEtaleSetRestrictionAdjunction B S hS h hh).unit.app
            (moduleSetSheaf B S hS A ((etaleModulePullback.{u, u} B S hS g hg).obj M))) ≫
        (smallToposMorphismTypeU_comp B S hS h g).hom.app
          ((smallEtaleSetRestriction B S hS h hh).obj
            ((smallEtaleSetRestriction B S hS g hg).obj (moduleSetSheaf B S hS C M))) =
      (smallEtaleSetRestrictionAdjunction B S hS (h ≫ g) hhg).unit.app
        (moduleSetSheaf B S hS C M) :=
  smallEtaleSetRestrictionAdjunction_unit_comp_app B S hS h g hh hg hhg
    (moduleSetSheaf B S hS C M)

/-! ### Values on sections -/

variable (W : (SmallEtale B S hS C.1)ᵒᵖ)

/-- On a section `z` over `W`, the direct image along `g` of the unit of étale restriction of
modules along `h` takes the value of the morphism of sheaves of sets of
`moduleSheafFunctor_map_modulePushforward_unit_app`. -/
def moduleSheafFunctor_map_modulePushforward_unit_val_app (z : ((modulePushforward B S hS g).obj
    ((etaleModulePullback.{u, u} B S hS g hg).obj M)).val.obj W) :=
  (moduleSheafFunctor_map_hom_app
      ((modulePushforward B S hS g).map
        ((etaleModulePullbackAdjunction B S hS h hh).unit.app
          ((etaleModulePullback.{u, u} B S hS g hg).obj M))) W z).symm.trans
    (Sheaf.hom_app_congr (moduleSheafFunctor_map_modulePushforward_unit_app B S hS h g hh hg M) W z)

/-- On a section `v` over `W`, the component of `modulePushforwardCompIso h g` at the iterated
étale restriction of `M` takes the value of the morphism of sheaves of sets underlying the
corresponding component of `Functor.compIsoCongr` applied to `pushforwardModulesCompAt h g`. -/
theorem modulePushforwardCompIso_hom_app_val_app_compIsoCongr
    (v : ((modulePushforward B S hS h ⋙ modulePushforward B S hS g).obj
      ((etaleModulePullback.{u, u} B S hS h hh).obj
        ((etaleModulePullback.{u, u} B S hS g hg).obj M))).val.obj W) :
    ((modulePushforwardCompIso B S hS h g).hom.app
          ((etaleModulePullback.{u, u} B S hS h hh).obj
            ((etaleModulePullback.{u, u} B S hS g hg).obj M))).val.app W v =
      ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS C)).map
        ((CategoryTheory.Functor.compIsoCongr
          (pushforwardModules_eq_modulePushforward B S hS h)
          (pushforwardModules_eq_modulePushforward B S hS g)
          (pushforwardModules_eq_modulePushforward B S hS (h ≫ g))
          (pushforwardModulesCompAt B S hS h g)).hom.app
            ((etaleModulePullback.{u, u} B S hS h hh).obj
              ((etaleModulePullback.{u, u} B S hS g hg).obj M)))).hom.app W v :=
  (modulesHom_val_app_congr (modulePushforwardCompIso_hom_app_eq B S hS h g
        ((etaleModulePullback.{u, u} B S hS h hh).obj
          ((etaleModulePullback.{u, u} B S hS g hg).obj M))) W v).trans
    (moduleSheafFunctor_map_hom_app _ W v).symm

/-- On a section `v` over `W`, the morphism of sheaves of sets underlying the component of
`Functor.compIsoCongr` applied to `pushforwardModulesCompAt h g`, at the iterated étale restriction
of `M`, agrees with the component of `smallToposMorphismTypeU_comp h g` at its underlying sheaf of
sets. -/
theorem moduleSheafFunctor_map_compIsoCongr_hom_app_apply
    (v : ((modulePushforward B S hS h ⋙ modulePushforward B S hS g).obj
      ((etaleModulePullback.{u, u} B S hS h hh).obj
        ((etaleModulePullback.{u, u} B S hS g hg).obj M))).val.obj W) :
    ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS C)).map
          ((CategoryTheory.Functor.compIsoCongr
            (pushforwardModules_eq_modulePushforward B S hS h)
            (pushforwardModules_eq_modulePushforward B S hS g)
            (pushforwardModules_eq_modulePushforward B S hS (h ≫ g))
            (pushforwardModulesCompAt B S hS h g)).hom.app
              ((etaleModulePullback.{u, u} B S hS h hh).obj
                ((etaleModulePullback.{u, u} B S hS g hg).obj M)))).hom.app W v =
      ((smallToposMorphismTypeU_comp B S hS h g).hom.app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS D)).obj
          ((etaleModulePullback.{u, u} B S hS h hh).obj
            ((etaleModulePullback.{u, u} B S hS g hg).obj M)))).hom.app W v :=
  Sheaf.hom_app_congr (moduleSheafFunctor_map_compIsoCongr_hom_app B S hS h g
    ((etaleModulePullback.{u, u} B S hS h hh).obj
      ((etaleModulePullback.{u, u} B S hS g hg).obj M))) W v

/-- On a section `s` of `M` over `W`, the composite of
`smallEtaleSetRestrictionAdjunction_unit_comp_app_moduleSetSheaf` takes the value of the unit of
étale restriction of modules along `h ≫ g`. -/
def smallEtaleSetRestrictionAdjunction_unit_comp_app_val_app (s : M.val.obj W) :=
  (Sheaf.hom_app_congr
      (smallEtaleSetRestrictionAdjunction_unit_comp_app_moduleSetSheaf B S hS h g hh hg hhg M)
      W s).trans
    (Stacks.eq_atType (α := ((smallToposMorphismTypeU B S hS (h ≫ g)).pushforward.obj
          ((smallEtaleSetRestriction B S hS (h ≫ g) hhg).obj
            (moduleSetSheaf B S hS C M))).obj.obj W)
      (Stacks.eq_atType (α := ((smallEtaleDirectImage B S hS (h ≫ g)).obj
            ((smallEtaleSetRestriction B S hS (h ≫ g) hhg).obj
              (moduleSetSheaf B S hS C M))).obj.obj W)
        (Stacks.eq_atType (α := ((smallEtaleDirectImage B S hS (h ≫ g)).obj
              (moduleSetSheaf B S hS D
                ((etaleModulePullback.{u, u} B S hS (h ≫ g) hhg).obj M))).obj.obj W)
          (etaleModulePullbackAdjunction_unit_val_app_eq_setRestriction
            B S hS (h ≫ g) hhg M W s).symm)))

/-- On a section `s` of `M` over `W`, the three factors of
`smallEtaleSetRestrictionAdjunction_unit_comp_app_moduleSetSheaf`, applied one after another, take
`s` to the value of the unit of étale restriction of modules along `h ≫ g`. -/
def smallEtaleSetRestrictionAdjunction_unit_comp_val_app (s : M.val.obj W) :=
  ((Sheaf.comp_hom_app_apply
        ((smallEtaleDirectImage B S hS g).map
          ((smallEtaleSetRestrictionAdjunction B S hS h hh).unit.app
            (moduleSetSheaf B S hS A ((etaleModulePullback.{u, u} B S hS g hg).obj M))))
        ((smallToposMorphismTypeU_comp B S hS h g).hom.app
          ((smallEtaleSetRestriction B S hS h hh).obj
            ((smallEtaleSetRestriction B S hS g hg).obj (moduleSetSheaf B S hS C M)))) W
        (((smallEtaleSetRestrictionAdjunction B S hS g hg).unit.app
          (moduleSetSheaf B S hS C M)).hom.app W s)).symm.trans
      (Sheaf.comp_hom_app_apply
          ((smallEtaleSetRestrictionAdjunction B S hS g hg).unit.app
            (moduleSetSheaf B S hS C M))
          ((smallEtaleDirectImage B S hS g).map
              ((smallEtaleSetRestrictionAdjunction B S hS h hh).unit.app
                (moduleSetSheaf B S hS A
                  ((etaleModulePullback.{u, u} B S hS g hg).obj M))) ≫
            (smallToposMorphismTypeU_comp B S hS h g).hom.app
              ((smallEtaleSetRestriction B S hS h hh).obj
                ((smallEtaleSetRestriction B S hS g hg).obj
                  (moduleSetSheaf B S hS C M)))) W s).symm).trans
    (smallEtaleSetRestrictionAdjunction_unit_comp_app_val_app B S hS h g hh hg hhg M W s)

/-- On a section `v` over `W`, the component of `modulePushforwardCompIso h g` at the iterated
étale restriction of `M` takes the value of the component of `smallToposMorphismTypeU_comp h g` at
the étale restriction along `h` of the sheaf of sets underlying the restriction of `M` along
`g`. -/
def modulePushforwardCompIso_hom_app_val_app_setRestriction
    (v : ((modulePushforward B S hS h ⋙ modulePushforward B S hS g).obj
      ((etaleModulePullback.{u, u} B S hS h hh).obj
        ((etaleModulePullback.{u, u} B S hS g hg).obj M))).val.obj W) :=
  (((modulePushforwardCompIso_hom_app_val_app_compIsoCongr B S hS h g hh hg M W v).trans
        (moduleSheafFunctor_map_compIsoCongr_hom_app_apply B S hS h g hh hg M W v)).trans
      (Sheaf.hom_app_congr
        (smallToposMorphismTypeU_comp_hom_app_moduleSetSheaf B S hS h g hh hg M) W v)).trans
    (Sheaf.hom_app_congr
      (smallToposMorphismTypeU_comp_hom_app_setRestriction B S hS h g hh hg M) W v)

/-- `etaleModulePullbackCompAdjunction_unit_app`, with both sides read as morphisms from `M` to the
direct image along `h ≫ g` of the iterated étale restriction of `M` along `g` and then `h`. -/
def etaleModulePullbackCompAdjunction_unit_app_nested :=
  Stacks.eq_atType (α := (M ⟶ (modulePushforward B S hS (h ≫ g)).obj
      ((etaleModulePullback.{u, u} B S hS h hh).obj
        ((etaleModulePullback.{u, u} B S hS g hg).obj M))))
    (etaleModulePullbackCompAdjunction_unit_app B S hS h g hh hg hhg M)

/-- The direct image along `h ≫ g` of the component at `M` of `etaleModulePullbackComp` is the
direct image of the identity of the iterated étale restriction of `M`. -/
def modulePushforward_map_etaleModulePullbackComp_hom_app_id :=
  congrArg (modulePushforward B S hS (h ≫ g)).map
    (etaleModulePullbackComp_hom_app_eq_id B S hS h g hh hg hhg M)

/-- The unit at `M` of the composite adjunction, followed by the direct image along `h ≫ g` of the
component of `etaleModulePullbackComp`, is that unit followed by the direct image of an
identity. -/
def innerUnit_comp_modulePushforward_map_id :=
  Stacks.comp_congr_right ((((etaleModulePullbackAdjunction B S hS g hg).comp
        (etaleModulePullbackAdjunction B S hS h hh)).ofNatIsoRight
          (modulePushforwardCompIso B S hS h g)).unit.app M)
    (modulePushforward_map_etaleModulePullbackComp_hom_app_id B S hS h g hh hg hhg M)

/-- `innerUnit_comp_modulePushforward_map_id`, with both sides read as morphisms from `M` to the
direct image along `h ≫ g` of the iterated étale restriction of `M` along `g` and then `h`. -/
def innerUnit_comp_modulePushforward_map_id_nested :=
  Stacks.eq_atType (α := (M ⟶ (modulePushforward B S hS (h ≫ g)).obj
      ((etaleModulePullback.{u, u} B S hS h hh).obj
        ((etaleModulePullback.{u, u} B S hS g hg).obj M))))
    (innerUnit_comp_modulePushforward_map_id B S hS h g hh hg hhg M)

/-- The unit at `M` of the composite adjunction, followed by the direct image along `h ≫ g` of the
identity of the iterated étale restriction of `M`, is that unit. -/
def innerUnit_comp_map_id :=
  Stacks.comp_map_id (X := ((etaleModulePullback.{u, u} B S hS h hh).obj
      ((etaleModulePullback.{u, u} B S hS g hg).obj M)))
    (modulePushforward B S hS (h ≫ g)) ((((etaleModulePullbackAdjunction B S hS g hg).comp
        (etaleModulePullbackAdjunction B S hS h hh)).ofNatIsoRight
          (modulePushforwardCompIso B S hS h g)).unit.app M)

/-- On a section `s` of `M` over `W`, the unit of the composite adjunction takes the value of the
three-factor composite of `etaleModulePullbackCompInner_unit_app`. -/
def innerUnitStep₁ (s : M.val.obj W) :=
  modulesHom_val_app_congr (etaleModulePullbackCompInner_unit_app B S hS h g hh hg M) W s

/-- On a section `s` of `M` over `W`, the three-factor composite of
`etaleModulePullbackCompInner_unit_app` takes the value of its last two factors at the value of the
unit along `g` at `s`. -/
def innerUnitStep₂ (s : M.val.obj W) :=
  modulesHom_comp_val_app_apply
    ((etaleModulePullbackAdjunction B S hS g hg).unit.app M)
    ((modulePushforward B S hS g).map
        ((etaleModulePullbackAdjunction B S hS h hh).unit.app
          ((etaleModulePullback.{u, u} B S hS g hg).obj M)) ≫
      (modulePushforwardCompIso B S hS h g).hom.app
        ((etaleModulePullback.{u, u} B S hS h hh).obj
          ((etaleModulePullback.{u, u} B S hS g hg).obj M))) W s

/-- At the value of the unit along `g` at a section `s` of `M`, the direct image along `g` of the
unit along `h` followed by the component of `modulePushforwardCompIso h g` takes the value of that
component at the value of the direct image of the unit. -/
def innerUnitStep₃ (s : M.val.obj W) :=
  modulesHom_comp_val_app_apply
    ((modulePushforward B S hS g).map
      ((etaleModulePullbackAdjunction B S hS h hh).unit.app
        ((etaleModulePullback.{u, u} B S hS g hg).obj M)))
    ((modulePushforwardCompIso B S hS h g).hom.app
      ((etaleModulePullback.{u, u} B S hS h hh).obj
        ((etaleModulePullback.{u, u} B S hS g hg).obj M))) W
    (((etaleModulePullbackAdjunction B S hS g hg).unit.app M).val.app W s)

/-- The component of `smallToposMorphismTypeU_comp h g` applied to both sides of
`moduleSheafFunctor_map_modulePushforward_unit_val_app`, at the value of the unit along `g` at a
section `s` of `M`. -/
def innerUnitStep₄ (s : M.val.obj W) :=
  Sheaf.hom_app_apply_congr ((smallToposMorphismTypeU_comp B S hS h g).hom.app
      ((smallEtaleSetRestriction B S hS h hh).obj
        (moduleSetSheaf B S hS A ((etaleModulePullback.{u, u} B S hS g hg).obj M)))) W
    (moduleSheafFunctor_map_modulePushforward_unit_val_app B S hS h g hh hg M W
      (((etaleModulePullbackAdjunction B S hS g hg).unit.app M).val.app W s))

/-- The direct image along `g` of the unit of étale restriction of sheaves of sets along `h`, and
then the component of `smallToposMorphismTypeU_comp h g`, applied to the identification of the
value at a section `s` of `M` of the unit of étale restriction of modules along `g` with that of
sheaves of sets. -/
def innerUnitStep₅ (s : M.val.obj W) :=
  Sheaf.hom_app_apply_congr ((smallToposMorphismTypeU_comp B S hS h g).hom.app
      ((smallEtaleSetRestriction B S hS h hh).obj
        (moduleSetSheaf B S hS A ((etaleModulePullback.{u, u} B S hS g hg).obj M)))) W
    (Sheaf.hom_app_apply_congr
      ((smallEtaleDirectImage B S hS g).map
        ((smallEtaleSetRestrictionAdjunction B S hS h hh).unit.app
          (moduleSetSheaf B S hS A
            ((etaleModulePullback.{u, u} B S hS g hg).obj M)))) W
      (etaleModulePullbackAdjunction_unit_val_app_eq_setRestriction B S hS g hg M W s))

/-- At the image of a section `s` of `M` under the units of étale restriction of sheaves of sets
along `g` and then `h`, the component of `smallToposMorphismTypeU_comp h g` read at the iterated
étale restriction of the sheaf of sets underlying `M`. -/
def innerUnitStep₆ (s : M.val.obj W) :=
  Sheaf.hom_app_congr
    (smallToposMorphismTypeU_comp_hom_app_setRestriction_comp B S hS h g hh hg M) W
    (((smallEtaleDirectImage B S hS g).map
        ((smallEtaleSetRestrictionAdjunction B S hS h hh).unit.app
          (moduleSetSheaf B S hS A
            ((etaleModulePullback.{u, u} B S hS g hg).obj M)))).hom.app W
      (((smallEtaleSetRestrictionAdjunction B S hS g hg).unit.app
        (moduleSetSheaf B S hS C M)).hom.app W s))

/-- On a section `s` of `M` over `W`, the unit of the composite adjunction takes the value of the
direct image along `g` of the unit along `h`, followed by the component of
`modulePushforwardCompIso h g`, at the value of the unit along `g` at `s`. -/
def innerUnitVal₁₂ (s : M.val.obj W) :=
  (innerUnitStep₁ B S hS h g hh hg M W s).trans (innerUnitStep₂ B S hS h g hh hg M W s)

/-- At the value of the unit along `g` at a section `s` of `M`, the direct image along `g` of the
unit along `h` followed by the component of `modulePushforwardCompIso h g` takes the value of the
component of `smallToposMorphismTypeU_comp h g` at the value of the direct image of the unit. -/
def innerUnitVal₃₄ (s : M.val.obj W) :=
  (innerUnitStep₃ B S hS h g hh hg M W s).trans
    (modulePushforwardCompIso_hom_app_val_app_setRestriction B S hS h g hh hg M W _)

/-- At the value of the unit along `g` at a section `s` of `M`, the component of
`smallToposMorphismTypeU_comp h g` applied to the direct image along `g` of the unit along `h`
takes the value at `s` of the unit of étale restriction of modules along `h ≫ g`. -/
def innerUnitVal₅₆ (s : M.val.obj W) :=
  (innerUnitStep₄ B S hS h g hh hg M W s).trans
    ((innerUnitStep₅ B S hS h g hh hg M W s).trans
      ((innerUnitStep₆ B S hS h g hh hg M W s).trans
        (smallEtaleSetRestrictionAdjunction_unit_comp_val_app B S hS h g hh hg hhg M W s)))

end AlgebraicGeometry.Space

end
