module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.ToposThickening.Basic
public import StacksFrontier.Deformation.ToposThickening.ExtensionDifference

/-!
# Functoriality of extensions in the first order thickening

Let `(Sh(C), O)` be a ringed topos with two first order thickenings `O'₁` and `O'₂`, presented
on one site, and let `h^♯ : O'₂ ⟶ O'₁` be a morphism of thickenings over `(Sh(C), O)`. Then
`h^♯` carries the defining ideal `I₂` into `I₁` and so induces a map of `O`-modules
`I₂ ⟶ I₁`.

## Main definitions

* `Deformation.ToposThickening.MorphismOfFirstOrderThickenings`: the two thickenings and the
  morphism between them.
* `Deformation.ToposThickening.MorphismOfFirstOrderThickenings.idealMap`: the induced map of
  defining ideals `I₂ ⟶ I₁`, as a map of `O`-modules.

## Main results

* `Deformation.ToposThickening.MorphismOfFirstOrderThickenings.inclOne_idealMap`: the induced
  map of defining ideals is characterized, section by section, by sending a section of `I₂` to
  the section of `I₁` with the same image in `O'₁`.
* `Deformation.ToposThickening.MorphismOfFirstOrderThickenings.existsUnique_idealMap_section`:
  that section of `I₁` exists and is unique, which is where the commutativity of the square and
  the square-zero hypotheses enter.

## Scope

This is the setup sentence of [Stacks Project, Tag 08MJ].  That remark goes on to assert a
canonical functoriality: for an `O`-module `F`, modules `K₁`, `K₂` with action maps
`cₖ : Iₖ ⊗_O F ⟶ Kₖ` and a map `K₂ ⟶ K₁` making the square with `I₂ ⟶ I₁` commute, every
extension `F'₂` as in Stacks 08MB over the second thickening with `c₂ = c_{F'₂}` gives an
extension `F'₁` over the *first* thickening with `c₁ = c_{F'₁}`, whose middle term is the
pushout `F'₂ ⊔_{K₂} K₁`.  The source omits the one piece of content there, namely the
`O'₁`-module structure on that pushout, and it is not supplied here either, so nothing in this
file carries a 08MJ attribute.

## Implementation notes

Both thickenings are presented on the site of the base ringed topos, as in
`Deformation.ToposThickening.RingedToposExtensionProblem`: the source regards all the sheaves
involved as sheaves on `C`, which is also what makes the pushout of the remark a pushout of
sheaves on one site.  The second thickening is obtained from the first by replacing the
structure sheaf of the target ringed topos, which is `Deformation.ToposThickening.reshape`;
keeping that an `abbrev` is what makes the two defining ideals modules over one and the same
sheaf of rings, so that the induced map of ideals is a morphism in a single category.

The induced map of ideals is first constructed as a map of `O'₂`-modules, where both inclusions
are linear, and then transported across the bijection
`Deformation.ToposThickening.moduleHomEquivOfLocallySurjective` on morphisms given by the
locally surjective structure map.  Constructing it directly as a map of `O`-modules would need
a local lift of a section of `O` to `O'₂` for its linearity.

The two inclusions of defining ideals are read through
`Deformation.ToposThickening.MorphismOfFirstOrderThickenings.inclOne` and `.inclTwo`, which fix
the ring of sections in which their values are compared; the module structures on a sheaf of
modules over the underlying sheaf of rings and over the sheaf of commutative rings are
definitionally equal but not interchangeable for instance search, and pinning the spelling once
avoids choosing between them at every step.

## References

* [Stacks Project, Tag 08MJ](https://stacks.math.columbia.edu/tag/08MJ)
* [Stacks Project, Tag 08MB](https://stacks.math.columbia.edu/tag/08MB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

universe v u w v' u' w'

attribute [local implicit_reducible] SheafOfModules.unit PresheafOfModules.unit
  CategoryTheory.ConcreteCategory.hom

namespace Deformation.ToposThickening

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]

/-- The structure sheaf of the base ringed topos, read on the site of a thickening of it. -/
noncomputable abbrev baseRing (i : RingedToposHom X Y) : Sheaf Y.J CommRingCat.{w'} :=
  (pushforwardCommRingFunctor i.toToposHom).obj X.O

/-- The structure map of a thickening, on underlying sheaves of rings. -/
noncomputable abbrev structureRingMap (i : RingedToposHom X Y) :
    Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i) :=
  (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp

/-- The ringed topos on the site of `Z` with a prescribed structure sheaf. -/
abbrev reshape (Z : RingedTopos.{v', u', w'}) (O₂ : Sheaf Z.J CommRingCat.{w'}) :
    RingedTopos.{v', u', w'} :=
  { C := Z.C, J := Z.J, O := O₂ }

/-- A thickening of the base ringed topos presented on the site of `Y`: the same underlying
morphism of topoi as `i`, with a prescribed structure map. -/
abbrev reshapeHom (i : RingedToposHom X Y) (O₂ : Sheaf Y.J CommRingCat.{w'})
    (f₂ : O₂ ⟶ baseRing i) : RingedToposHom X (reshape Y O₂) where
  toToposHom := i.toToposHom
  fSharp := f₂

/-- Two first order thickenings of a ringed topos, presented on one site, and a morphism of
thickenings between them over the base: a map `h^♯ : O'₂ ⟶ O'₁` of the two thickened structure
sheaves compatible with the two structure maps. -/
structure MorphismOfFirstOrderThickenings (i : RingedToposHom X Y) where
  /-- The first thickening `O'₁ ⟶ O`, whose structure sheaf is that of `Y`. -/
  first : FirstOrderThickening i
  /-- The structure sheaf `O'₂` of the second thickening. -/
  O₂ : Sheaf Y.J CommRingCat.{w'}
  /-- The structure map `O'₂ ⟶ O` of the second thickening. -/
  fSharp₂ : O₂ ⟶ baseRing i
  /-- The morphism `h^♯ : O'₂ ⟶ O'₁` of thickened structure sheaves. -/
  hSharp : O₂ ⟶ Y.O
  /-- The morphism lies over the base ringed topos. -/
  comm : hSharp ≫ i.fSharp = fSharp₂
  /-- The second thickening is first order. -/
  second : FirstOrderThickening (reshapeHom i O₂ fSharp₂)

namespace MorphismOfFirstOrderThickenings

variable {i : RingedToposHom X Y} (D : MorphismOfFirstOrderThickenings i)

/-- The structure map of the second thickening, on underlying sheaves of rings. -/
noncomputable abbrev ringMap₂ :
    Stacks.SheafOfModules.Tensor.ringSheaf D.O₂ ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i) :=
  (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map D.fSharp₂

/-- The morphism `h^♯ : O'₂ ⟶ O'₁`, on underlying sheaves of rings. -/
noncomputable abbrev ringMapH :
    Stacks.SheafOfModules.Tensor.ringSheaf D.O₂ ⟶ Stacks.SheafOfModules.Tensor.ringSheaf Y.O :=
  (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map D.hSharp

/-- The morphism of thickenings lies over the base, on underlying sheaves of rings. -/
lemma ringMapH_comp_structureRingMap : D.ringMapH ≫ structureRingMap i = D.ringMap₂ := by
  change (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map D.hSharp ≫
      (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp =
    (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map D.fSharp₂
  rw [← Functor.map_comp, D.comm]

/-- The morphism of thickenings lies over the base, on local sections. -/
lemma fSharp_hSharp_apply (U : Y.Cᵒᵖ) (a : D.O₂.obj.obj U) :
    i.fSharp.hom.app U (show Y.O.obj.obj U from D.hSharp.hom.app U a) =
      D.fSharp₂.hom.app U a := by
  conv_rhs => rw [← D.comm]
  rfl

/-- The morphism of thickenings lies over the base, on local sections of the underlying sheaves
of rings. -/
lemma structureRingMap_ringMapH_apply (U : Y.Cᵒᵖ)
    (a : (Stacks.SheafOfModules.Tensor.ringSheaf D.O₂).obj.obj U) :
    (structureRingMap i).hom.app U
        (show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U from D.ringMapH.hom.app U a) =
      D.ringMap₂.hom.app U a :=
  D.fSharp_hSharp_apply U a

/-- A map out of a restricted-scalars module commutes with the restriction of local sections. -/
private lemma incl_val_app_map {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{w'}} (φ : S ⟶ R) (M : SheafOfModules.{w'} R)
    (incl : (SheafOfModules.restrictScalars φ).obj M ⟶ SheafOfModules.unit S)
    {U V : Cᵒᵖ} (g : U ⟶ V) (c : M.val.obj U) :
    incl.val.app V (M.val.map g c) = S.obj.map g (incl.val.app U c) := by
  exact (PresheafOfModules.naturality_apply incl.val g
    (show ((SheafOfModules.restrictScalars φ).obj M).val.obj U from c))

/-- The image in `O'₁` of a section of the defining ideal of the first thickening. -/
noncomputable def inclOne (U : Y.Cᵒᵖ) (c : D.first.I.val.obj U) :
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U :=
  D.first.incl.val.app U c

/-- The image in `O'₂` of a section of the defining ideal of the second thickening. -/
noncomputable def inclTwo (U : Y.Cᵒᵖ) (b : D.second.I.val.obj U) :
    (Stacks.SheafOfModules.Tensor.ringSheaf D.O₂).obj.obj U :=
  D.second.incl.val.app U b

/-- The defining ideal of the first thickening is a submodule of `O'₁`. -/
lemma inclOne_injective (U : Y.Cᵒᵖ) : Function.Injective (D.inclOne U) :=
  D.first.injective U

/-- The inclusion of the first defining ideal is additive. -/
lemma inclOne_add (U : Y.Cᵒᵖ) (c c' : D.first.I.val.obj U) :
    D.inclOne U (c + c') = D.inclOne U c + D.inclOne U c' :=
  map_add (D.first.incl.val.app U).hom c c'

/-- The inclusion of the second defining ideal is additive. -/
lemma inclTwo_add (U : Y.Cᵒᵖ) (b b' : D.second.I.val.obj U) :
    D.inclTwo U (b + b') = D.inclTwo U b + D.inclTwo U b' :=
  map_add (D.second.incl.val.app U).hom b b'

/-- The inclusion of the first defining ideal is linear over `O'₁`, which acts on the ideal
through the structure map of the thickening. -/
lemma inclOne_smul (U : Y.Cᵒᵖ) (s : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U)
    (c : D.first.I.val.obj U) :
    D.inclOne U ((structureRingMap i).hom.app U s • c) = s * D.inclOne U c :=
  map_smul (D.first.incl.val.app U).hom s
    (show ((SheafOfModules.restrictScalars (structureRingMap i)).obj D.first.I).val.obj U from c)

/-- The inclusion of the second defining ideal is linear over `O'₂`, which acts on the ideal
through the structure map of the thickening. -/
lemma inclTwo_smul (U : Y.Cᵒᵖ) (s : (Stacks.SheafOfModules.Tensor.ringSheaf D.O₂).obj.obj U)
    (b : D.second.I.val.obj U) :
    D.inclTwo U (D.ringMap₂.hom.app U s • b) = s * D.inclTwo U b :=
  map_smul (D.second.incl.val.app U).hom s
    (show ((SheafOfModules.restrictScalars D.ringMap₂).obj D.second.I).val.obj U from b)

/-- The inclusion of the first defining ideal commutes with restriction. -/
lemma inclOne_naturality {U V : Y.Cᵒᵖ} (g : U ⟶ V) (c : D.first.I.val.obj U) :
    D.inclOne V (D.first.I.val.map g c) =
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.map g (D.inclOne U c) :=
  incl_val_app_map _ _ _ g c

/-- The inclusion of the second defining ideal commutes with restriction. -/
lemma inclTwo_naturality {U V : Y.Cᵒᵖ} (g : U ⟶ V) (b : D.second.I.val.obj U) :
    D.inclTwo V (D.second.I.val.map g b) =
      (Stacks.SheafOfModules.Tensor.ringSheaf D.O₂).obj.map g (D.inclTwo U b) :=
  incl_val_app_map _ _ _ g b

/-- Sections of the defining ideal of the second thickening are killed by its structure map. -/
lemma ringMap₂_inclTwo (U : Y.Cᵒᵖ) (b : D.second.I.val.obj U) :
    D.ringMap₂.hom.app U (D.inclTwo U b) = 0 :=
  (D.second.kernel U _).2 ⟨b, rfl⟩

/-- The section of the defining ideal of the first thickening cut out by the image under `h^♯`
of a section of the defining ideal of the second: the image is killed by the structure map of
the first thickening, by the commutativity of the square. -/
lemma existsUnique_idealMap_section (U : Y.Cᵒᵖ) (b : D.second.I.val.obj U) :
    ∃! c : D.first.I.val.obj U,
      D.inclOne U c = D.ringMapH.hom.app U (D.inclTwo U b) := by
  obtain ⟨c, hc⟩ := (D.first.kernel U _).1
    ((D.structureRingMap_ringMapH_apply U _).trans (D.ringMap₂_inclTwo U b))
  exact ⟨c, hc, fun c' hc' => D.inclOne_injective U (hc'.trans hc.symm)⟩

/-- The map of defining ideals on local sections. -/
noncomputable def idealMapFun (U : Y.Cᵒᵖ) (b : D.second.I.val.obj U) : D.first.I.val.obj U :=
  (D.existsUnique_idealMap_section U b).choose

/-- The map of defining ideals is characterized, section by section, by sending a section of
`I₂` to the section of `I₁` with the same image under `h^♯`. -/
lemma inclOne_idealMapFun (U : Y.Cᵒᵖ) (b : D.second.I.val.obj U) :
    D.inclOne U (D.idealMapFun U b) = D.ringMapH.hom.app U (D.inclTwo U b) :=
  (D.existsUnique_idealMap_section U b).choose_spec.1

/-- A section of `I₁` whose image under the inclusion is the `h^♯`-image of a section of `I₂`
is the value of the map of defining ideals there. -/
lemma idealMapFun_eq (U : Y.Cᵒᵖ) (b : D.second.I.val.obj U) (c : D.first.I.val.obj U)
    (hc : D.inclOne U c = D.ringMapH.hom.app U (D.inclTwo U b)) :
    D.idealMapFun U b = c :=
  D.inclOne_injective U ((D.inclOne_idealMapFun U b).trans hc.symm)

/-- The structure map of the second thickening is locally surjective. -/
lemma fSharp₂_locallySurjective : Presheaf.IsLocallySurjective Y.J D.fSharp₂.hom :=
  D.second.surjective

/-- The structure map of the second thickening is locally surjective on the underlying sheaves
of rings. -/
lemma ringMap₂_locallySurjective : Presheaf.IsLocallySurjective Y.J D.ringMap₂.hom := by
  change Presheaf.IsLocallySurjective Y.J
    (Functor.whiskerRight D.fSharp₂.hom (forget₂ CommRingCat RingCat))
  refine ⟨?_⟩
  intro U s
  simpa [Presheaf.imageSieve] using D.fSharp₂_locallySurjective.imageSieve_mem s

/-- The map of defining ideals is additive on local sections. -/
lemma idealMapFun_add (U : Y.Cᵒᵖ) (b b' : D.second.I.val.obj U) :
    D.idealMapFun U (b + b') = D.idealMapFun U b + D.idealMapFun U b' := by
  refine D.idealMapFun_eq U (b + b') _ ?_
  rw [D.inclOne_add, D.inclOne_idealMapFun, D.inclOne_idealMapFun, D.inclTwo_add, map_add]

/-- The map of defining ideals is linear over the base, on local sections. -/
lemma idealMapFun_smul (U : Y.Cᵒᵖ) (s : (Stacks.SheafOfModules.Tensor.ringSheaf D.O₂).obj.obj U)
    (b : D.second.I.val.obj U) :
    D.idealMapFun U (D.ringMap₂.hom.app U s • b) =
      D.ringMap₂.hom.app U s • D.idealMapFun U b := by
  refine D.idealMapFun_eq U _ _ ?_
  rw [← D.structureRingMap_ringMapH_apply U s, D.inclOne_smul, D.inclOne_idealMapFun,
    D.structureRingMap_ringMapH_apply U s, D.inclTwo_smul, map_mul]

/-- The map of defining ideals commutes with restriction of local sections. -/
lemma idealMapFun_naturality {U V : Y.Cᵒᵖ} (g : U ⟶ V) (b : D.second.I.val.obj U) :
    D.idealMapFun V (D.second.I.val.map g b) = D.first.I.val.map g (D.idealMapFun U b) := by
  refine D.idealMapFun_eq V _ _ ?_
  rw [D.inclOne_naturality, D.inclOne_idealMapFun, D.inclTwo_naturality]
  exact (ConcreteCategory.congr_hom (D.ringMapH.hom.naturality g) (D.inclTwo U b)).symm

/-- The map of defining ideals, as a map of `O'₂`-modules: both inclusions are linear over the
thickened structure sheaf of the second thickening. -/
noncomputable def idealMapRestricted :
    (SheafOfModules.restrictScalars D.ringMap₂).obj D.second.I ⟶
      (SheafOfModules.restrictScalars D.ringMap₂).obj D.first.I :=
  ⟨{ app := fun U => ModuleCat.ofHom
      (X := ((SheafOfModules.restrictScalars D.ringMap₂).obj D.second.I).val.obj U)
      (Y := ((SheafOfModules.restrictScalars D.ringMap₂).obj D.first.I).val.obj U)
      { toFun := D.idealMapFun U
        map_add' := D.idealMapFun_add U
        map_smul' := D.idealMapFun_smul U }
     naturality := fun {U V} g => by
       ext b
       exact D.idealMapFun_naturality g b }⟩

/-- The map of `O`-modules `I₂ ⟶ I₁` induced by a morphism `h^♯ : O'₂ ⟶ O'₁` of first order
thickenings of a ringed topos: the structure map of the morphism carries the defining ideal of
the second thickening into that of the first.

No `@[stacks 08MJ]` attribute is carried.  That tag asserts a canonical functoriality carrying
extensions over the second thickening to extensions over the first; this map is the setup
sentence preceding the assertion. -/
noncomputable def idealMap : D.second.I ⟶ D.first.I :=
  moduleHomEquivOfLocallySurjective D.ringMap₂ D.ringMap₂_locallySurjective
    D.idealMapRestricted

/-- The induced map of defining ideals is the map of local sections constructed above. -/
lemma idealMap_val_app (U : Y.Cᵒᵖ) (b : D.second.I.val.obj U) :
    D.idealMap.val.app U b = D.idealMapFun U b := by
  have h : (SheafOfModules.restrictScalars D.ringMap₂).map D.idealMap = D.idealMapRestricted :=
    (moduleHomEquivOfLocallySurjective D.ringMap₂ D.ringMap₂_locallySurjective).left_inv _
  exact congrArg (fun m : (SheafOfModules.restrictScalars D.ringMap₂).obj D.second.I ⟶
    (SheafOfModules.restrictScalars D.ringMap₂).obj D.first.I => m.val.app U b) h

/-- The induced map of defining ideals is characterized, section by section, by sending a
section of `I₂` to the section of `I₁` with the same image under `h^♯`. -/
lemma inclOne_idealMap (U : Y.Cᵒᵖ) (b : D.second.I.val.obj U) :
    D.inclOne U (D.idealMap.val.app U b) = D.ringMapH.hom.app U (D.inclTwo U b) := by
  rw [D.idealMap_val_app]
  exact D.inclOne_idealMapFun U b

end MorphismOfFirstOrderThickenings



end Deformation.ToposThickening

end
