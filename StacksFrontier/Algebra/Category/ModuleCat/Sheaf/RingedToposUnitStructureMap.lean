module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BaseChangeUnitor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullback
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# The structure map of a morphism of ringed topoi, read on unit modules

Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi in the sense of
Stacks 01D3, i.e. an `AlgebraicGeometry.RingedToposHom`. Its structure map
`f♯ : O_D ⟶ f_*O_C` is a map of sheaves of *rings*. This file reads it as a map of sheaves of
`O_D`-*modules*

`O_D ⟶ f_*O_C`

between the unit modules — the structure sheaves viewed as modules over themselves — and
transposes it across the adjunction `f^* ⊣ f_*` of Stacks 03D7 to the canonical comparison

`f^*O_D ⟶ O_C`.

The direct-image form is what makes a map of ideals out of a commutative square of morphisms of
ringed topoi (Stacks 08M7): a section of `O_D` killed by a further structure map has image
killed by that map pushed forward, and the two readings of the square identify the two
composites.

## The engine

A map of modules out of a unit module is pinned down by a global section of the target
(`SheafOfModules.unitHomEquiv`), and the global section wanted here is `1`: the direct image
`f_*O_C` is a sheaf of rings, so it has one. That is exactly
`Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit` applied to `f♯` read as a map
of sheaves of rings, because `f_*` of a unit module *is* the unit module of the direct-image
sheaf of rings — on the nose, module structure included, which is what
`Stacks.Sheaves.ToposPullback.pullbackModuleUnitIso` records. So the whole construction is one
application of an existing comparison, and what remains is to characterise it.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.unitStructureMap`: the structure map read on unit modules,
  `O_D ⟶ f_*O_C`.
* `AlgebraicGeometry.RingedToposHom.pullbackUnitStructureMap`: its adjoint transpose
  `f^*O_D ⟶ O_C`.

## Main results

* `Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit_val_app` and
  `AlgebraicGeometry.RingedToposHom.unitStructureMap_val_app`: the component formula. On a
  section `a` of `O_D` over an object of the site, the unit-module structure map is `f♯(a)`.
  This is what pins it down, and it is the form in which a vanishing hypothesis on `a` is used.
* `AlgebraicGeometry.RingedToposHom.moduleSheafFunctor_map_unitStructureMap`: on underlying
  sheaves of sets the unit-module structure map *is* `f♯`.
* `AlgebraicGeometry.RingedToposHom.unitStructureMap_comp`: the unit-module structure map of a
  composite is the composite of the unit-module structure maps, read through the comparison
  `AlgebraicGeometry.RingedToposHom.pushforwardModulesCompIso` of successive direct images.
* `AlgebraicGeometry.RingedToposHom.homEquiv_pullbackUnitStructureMap` and
  `AlgebraicGeometry.RingedToposHom.homEquiv_map_comp_pullbackUnitStructureMap`: the transpose
  of `f^*O_D ⟶ O_C` is the unit-module structure map, also after precomposition with the
  pullback of an arbitrary morphism. The second form is what turns a statement about
  `f^*M ⟶ O_C` into one about sections of `M`.

## Implementation notes

The component formula is stated with a type ascription on the left-hand side, as the
neighbouring modules do: the sections of `f_*O_C` as a sheaf of rings and as the unit module
over that sheaf of rings are the same type, but not the same spelling, and without the
ascription the elaborator has to guess which module structure the scalar action refers to.

The two ringed topoi keep independent universes for their sections, as they do throughout the
pullback and pushforward of sheaves of modules.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 08M7](https://stacks.math.columbia.edu/tag/08M7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.ToposPushforward Stacks.Sheaves.ToposPullback

namespace Stacks.SheafOfModules.ChangeOfRings

open _root_.SheafOfModules

universe v u w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R R' : Sheaf J RingCat.{w}} (α : R ⟶ R')

/-- **The component formula for the canonical morphism `unit R ⟶ (restrictScalars α).obj
(unit R')`**: on a section of `R` it is `α` itself.

`Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit_val_app_one` is the special case
of the unit section, and is how the morphism is built; this is the general statement, obtained
from it because a map out of a unit module carries `a` to `a • 1`, and the restricted scalar
action of `a` on `R'` is multiplication by `α a`. -/
lemma unitToRestrictScalarsUnit_val_app (U : Cᵒᵖ) (a : R.obj.obj U) :
    (show R'.obj.obj U from
      PresheafOfModules.Hom.app (unitToRestrictScalarsUnit α).val U a) = α.hom.app U a := by
  have h : (show R'.obj.obj U from
        PresheafOfModules.Hom.app (unitToRestrictScalarsUnit α).val U a) =
      (α.hom.app U) a * (1 : R'.obj.obj U) := rfl
  rw [h, mul_one]

variable [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]

/-- On underlying sheaves of sets, the canonical morphism `unit R ⟶ (restrictScalars α).obj
(unit R')` of sheaves of modules is `α` itself. -/
lemma moduleSheafFunctor_map_unitToRestrictScalarsUnit :
    (Sheaf.moduleSheafFunctor R).map (unitToRestrictScalarsUnit α) =
      (sheafCompose J (forget RingCat.{w})).map α :=
  Sheaf.hom_ext_sections fun U a ↦ unitToRestrictScalarsUnit_val_app α U a

end Stacks.SheafOfModules.ChangeOfRings

namespace AlgebraicGeometry.RingedToposHom

open Stacks.Sheaves.RingedToposModules

universe v u w v' u' w' v'' u'' w''

section Pushforward

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]

/-- The structure map `f♯ : O_D ⟶ f_*O_C` of a morphism of ringed topoi, read as a morphism of
sheaves of `O_D`-modules between the unit modules.

The direct image of the unit module of `O_C` is the unit module of the direct-image sheaf of
rings `f_*O_C`, with the scalars restricted along `f♯`; so this is the canonical comparison
`Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit` of unit modules along the ring
map `f♯`, and it carries the unit section to the unit section. -/
noncomputable def unitStructureMap (f : RingedToposHom X Y) :
    SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O) ⟶
      (pushforwardModules f).obj
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)) :=
  Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit f.structureRingMap

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})] in
/-- **The component formula for the unit-module structure map**: on a section `a` of `O_D` over
an object of the site it is `f♯(a)`. Since a morphism of sheaves of modules is determined by
its sections, this characterises `unitStructureMap`. -/
lemma unitStructureMap_val_app (f : RingedToposHom X Y) (U : Y.Cᵒᵖ) (a : Y.O.obj.obj U) :
    (show (pushforwardRingSheaf f.toToposHom
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)).obj.obj U from
      PresheafOfModules.Hom.app (unitStructureMap f).val U a) = f.fSharp.hom.app U a :=
  Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit_val_app f.structureRingMap U a

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- On underlying sheaves of sets, the unit-module structure map *is* the structure map `f♯`. -/
lemma moduleSheafFunctor_map_unitStructureMap (f : RingedToposHom X Y) :
    (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)).map
        (unitStructureMap f) =
      (sheafCompose Y.J (forget RingCat.{w'})).map f.fSharpRing :=
  Stacks.SheafOfModules.ChangeOfRings.moduleSheafFunctor_map_unitToRestrictScalarsUnit
    f.structureRingMap

end Pushforward

section Composition

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]

/-- **The unit-module structure map of a composite.** Read through the comparison
`AlgebraicGeometry.RingedToposHom.pushforwardModulesCompIso` of the direct image of a composite
with the composite of the direct images, the unit-module structure map of `g ∘ f` is the
unit-module structure map of `g` followed by the direct image under `g` of that of `f`.

Both sides are determined by their underlying morphisms of sheaves of sets, where the
comparison is the identity and the statement becomes the composition formula
`AlgebraicGeometry.RingedToposHom.comp_fSharpRing_underlying` for the structure map itself. -/
lemma unitStructureMap_comp (g : RingedToposHom Y Z) (f : RingedToposHom X Y) :
    unitStructureMap (g.comp f) ≫ (pushforwardModulesCompIso f g).hom.app
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)) =
      unitStructureMap g ≫ (pushforwardModules g).map (unitStructureMap f) := by
  refine hom_ext_moduleSheafFunctor ?_
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    moduleSheafFunctor_map_unitStructureMap, moduleSheafFunctor_map_unitStructureMap,
    moduleSheafFunctor_map_pushforwardModules_map g (unitStructureMap f),
    moduleSheafFunctor_map_unitStructureMap]
  have h1 : (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J)) Z.O)).map
      ((pushforwardModulesCompIso f g).hom.app
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))) = 𝟙 _ :=
    rfl
  rw [h1]
  exact (Category.comp_id _).trans (comp_fSharpRing_underlying g f)

end Composition

section Pullback

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : RingedToposHom X Y)

/-- **The canonical comparison `f^*O_D ⟶ O_C`** attached to a morphism of ringed topoi: the
adjoint transpose, under the adjunction `f^* ⊣ f_*` of Stacks 03D7, of the unit-module
structure map `O_D ⟶ f_*O_C`. -/
noncomputable def pullbackUnitStructureMap :
    (f.toModulesHom.pullbackModules).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  ((pullbackAdjPushforwardModules f).homEquiv _ _).symm (unitStructureMap f)

/-- **The characterisation of `f^*O_D ⟶ O_C`**: its adjoint transpose is the unit-module
structure map. Since the adjunction bijection is a bijection, this determines the
comparison. -/
lemma homEquiv_pullbackUnitStructureMap :
    (pullbackAdjPushforwardModules f).homEquiv
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))
        (pullbackUnitStructureMap f) =
      unitStructureMap f :=
  ((pullbackAdjPushforwardModules f).homEquiv _ _).apply_symm_apply _

/-- The transpose of `f^*M ⟶ f^*O_D ⟶ O_C`, for a morphism `ψ : M ⟶ O_D` of sheaves of
`O_D`-modules, is `ψ` followed by the unit-module structure map. This is the form in which a
map out of a pullback is reduced to a statement about sections of `M`: the right-hand side
lives on the target topos, where the structure map has a component formula. -/
lemma homEquiv_map_comp_pullbackUnitStructureMap
    {M : SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)}
    (ψ : M ⟶ SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)) :
    (pullbackAdjPushforwardModules f).homEquiv M
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        ((f.toModulesHom.pullbackModules).map ψ ≫ pullbackUnitStructureMap f) =
      ψ ≫ unitStructureMap f :=
  ((pullbackAdjPushforwardModules f).homEquiv_naturality_left ψ
    (pullbackUnitStructureMap f)).trans
    (congrArg (fun m ↦ ψ ≫ m) (homEquiv_pullbackUnitStructureMap f))

end Pullback

end AlgebraicGeometry.RingedToposHom

end
