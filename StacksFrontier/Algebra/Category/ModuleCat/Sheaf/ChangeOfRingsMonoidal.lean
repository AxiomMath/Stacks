module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsLocalIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionMonoidal
public import StacksCore.Tactic.StacksAttribute

/-!
# Extension of scalars for sheaves of modules is monoidal

Let `θ : A₁ ⟶ A₂` be a morphism of presheaves of commutative rings on a site `(C, J)` whose
underlying presheaves of rings are both sheaves. Extension of scalars
`Stacks.Sheaves.RingedToposModules.extendScalars`, the functor `Mod(A₁) ⟶ Mod(A₂)` of Stacks
03CZ, is a **strong monoidal** functor for the tensor product of sheaves of modules of Tag
01CA: its tensorator is the base change of a tensor product,
`A₂ ⊗_{A₁} (F ⊗_{A₁} G) ≅ (A₂ ⊗_{A₁} F) ⊗_{A₂} (A₂ ⊗_{A₁} G)`.

The lift is one application of `CategoryTheory.Localization.Monoidal.functorMonoidalOfComp`, in
exactly the shape used for the ringed-space pullback in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackMonoidalSheaf`: the monoidal structure on
sheaves of modules *is* the localization of the objectwise monoidal structure on presheaves of
modules along sheafification, so a functor out of it is monoidal as soon as its composite with
sheafification is. That composite is change of rings followed by sheafification, monoidal by
`Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsMonoidal` of Tag 03CU and by monoidality of
sheafification; and the required lifting isomorphism
`sheafification ⋙ extendScalars ≅ changeOfRings ⋙ sheafification` is
`Stacks.Sheaves.RingedToposModules.extendScalarsSheafifyIso`, whose naturality is proved here.

The result is then transported to the *strict* monoidal structure of Tag 01CA, whose tensor
product is `Stacks.SheafOfModules.TensorSheafification.tensorSheaf` on the nose, by the two
identity-functor comparisons of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionMonoidal`. That is the structure
the graded-algebra machinery of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraFunctoriality` consumes.

## Main definitions

* `Stacks.Sheaves.RingedToposModules.extendScalarsFunctor`: extension of scalars, retyped over
  the `Stacks.SheafOfModules.TensorSheafification.structureSheaf` spelling of the two sheaves of
  rings, which is the spelling the monoidal structures are named at.
* `Stacks.Sheaves.RingedToposModules.sheafifyChangeOfRingsNatIso`: **extension of scalars
  commutes with sheafification**, as a natural isomorphism of functors. This is the lifting
  isomorphism of the localization.
* `Stacks.Sheaves.RingedToposModules.extendScalarsMonoidalLocalized`: **extension of scalars is
  monoidal** for the localized monoidal structure `Stacks.SheafOfModules.monoidalCategory`.
* `Stacks.Sheaves.RingedToposModules.extendScalarsStrictMonoidal`: **extension of scalars is
  monoidal for the monoidal structure of Tag 01CA**, whose tensor product is the tensor product
  sheaf on the nose.
* `Stacks.Sheaves.RingedToposModules.extendScalarsFSharpMonoidal`: the same statement for the
  extension of scalars along the inverse-image form `f⁻¹O_D ⟶ O_C` of the structure map of a
  morphism of ringed topoi.

## Main results

* `Stacks.Sheaves.RingedToposModules.extendScalarsSheafifyIso_naturality`: the comparison
  isomorphism of `extendScalarsSheafifyIso` is natural in the presheaf of modules. Both sides
  are the sheafification of the change-of-rings image of a composite, and the two composites
  agree by naturality of the sheafification unit.
* `Stacks.Sheaves.RingedToposModules.sheafifyMap_changeOfRings_unit_square`: the same square
  with every functor spelled out, which is where the work is done; the naturality statement is
  that square read through the definitions.

## Implementation notes

**Why the retyping is forced.** `Stacks.SheafOfModules.monoidalCategory` and its companions are
indexed by a presheaf of commutative rings `𝒪` together with a proof that
`𝒪 ⋙ forget₂ CommRingCat RingCat` is a sheaf, and their statements mention the sheaf of rings in
the spelling `Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪`, whereas
`Stacks.Sheaves.RingedToposModules.extendScalars` is indexed by
`Stacks.Sheaves.RingedToposModules.commRingSheaf`. The two are equal by `rfl`, but the
discrimination-tree key of an instance named at one spelling does not match a goal written in
the other, so `extendScalarsFunctor` carries an **ascribed** type and the defeq check of `:=` is
what crosses the boundary. This is the discipline of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackMonoidalSheaf`; no limit is raised
anywhere.

**What this file does not do.** It does not make the pullback of sheaves of modules along a
morphism of *ringed topoi* monoidal. That functor is the inverse image of Stacks 03D2 followed
by the extension of scalars treated here
(`Stacks.Sheaves.RingedToposModules.pullbackModules`), and the inverse-image half is a separate
piece of work: `Stacks.Sheaves.RingedToposModules.inverseImageModules` is built from the
abstract inverse image of a morphism of topoi, which is not the sheafification of any
presheaf-level functor, so the localization argument used here does not reach it. What is
available for that half is the transport of *bilinear* pairings across the adjunction
`f⁻¹ ⊣ f_*` in `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InverseImageTensor`; the
comparison isomorphism and its associativity coherence need in addition the transport of
*trilinear* pairings, which does not exist yet.

**Universes.** A single universe `w` carries the ring sections and the module sections, and the
site is arbitrary. This is inherited: Mathlib's monoidal structure on presheaves of modules
exists only for `PresheafOfModules.{w}` over a ring presheaf of the shape
`𝒪 ⋙ forget₂ CommRingCat.{w} RingCat.{w}`. Nothing is narrowed relative to the imports.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Localization CategoryTheory.Sheaf
open Stacks.PresheafOfModules.ChangeOfRings

universe w v u

namespace Stacks.Sheaves.RingedToposModules

section ExtendScalarsMonoidal

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {A₁ A₂ : Cᵒᵖ ⥤ CommRingCat.{w}} (θ : A₁ ⟶ A₂)
  (h₁ : Presheaf.IsSheaf J (ringPresheaf A₁)) (h₂ : Presheaf.IsSheaf J (ringPresheaf A₂))

/-- Extension of scalars along `θ`, with both sheaves of rings spelled over
`Stacks.SheafOfModules.TensorSheafification.structureSheaf`, which is the spelling at which the
monoidal structures on sheaves of modules are named. -/
noncomputable abbrev extendScalarsFunctor :
    SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf A₁ h₁) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf A₂ h₂) :=
  extendScalars J θ h₁ h₂

/-- Change of rings at the level of presheaves of modules, followed by sheafification of
presheaves of `A₂`-modules. This is the functor that `sheafification ⋙ extendScalars` lifts. -/
noncomputable abbrev changeOfRingsCompSheafify :
    PresheafOfModules.{w} (ringPresheaf A₁) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf A₂ h₂) :=
  changeOfRings θ ⋙ Stacks.SheafOfModules.sheafifyFunctor A₂ h₂

/-- **The square of sheafified change-of-rings maps behind the naturality of
`Stacks.Sheaves.RingedToposModules.extendScalarsSheafifyIso`.** Both sides are the sheafification
of the change-of-rings image of a composite of two morphisms of presheaves of modules, and the
two composites agree by naturality of the sheafification unit. Stated with every functor spelled
out, so that no `rw` has to see through a composite. -/
theorem sheafifyMap_changeOfRings_unit_square
    {P Q : PresheafOfModules.{w} (ringPresheaf A₁)} (u : P ⟶ Q) :
    (PresheafOfModules.sheafification (R := commRingSheaf J A₂ h₂) (𝟙 _)).map
            ((changeOfRings θ).map u) ≫
          (PresheafOfModules.sheafification (R := commRingSheaf J A₂ h₂) (𝟙 _)).map
            ((changeOfRings θ).map ((PresheafOfModules.sheafificationAdjunction
              (R := commRingSheaf J A₁ h₁) (𝟙 _)).unit.app Q)) =
      (PresheafOfModules.sheafification (R := commRingSheaf J A₂ h₂) (𝟙 _)).map
            ((changeOfRings θ).map ((PresheafOfModules.sheafificationAdjunction
              (R := commRingSheaf J A₁ h₁) (𝟙 _)).unit.app P)) ≫
          (PresheafOfModules.sheafification (R := commRingSheaf J A₂ h₂) (𝟙 _)).map
            ((changeOfRings θ).map
              (((PresheafOfModules.sheafification
                (R := commRingSheaf J A₁ h₁) (𝟙 _)).map u).val)) := by
  have h : u ≫ (PresheafOfModules.sheafificationAdjunction
        (R := commRingSheaf J A₁ h₁) (𝟙 _)).unit.app Q =
      (PresheafOfModules.sheafificationAdjunction
          (R := commRingSheaf J A₁ h₁) (𝟙 _)).unit.app P ≫
        ((PresheafOfModules.sheafification (R := commRingSheaf J A₁ h₁) (𝟙 _)).map u).val :=
    (PresheafOfModules.sheafificationAdjunction
      (R := commRingSheaf J A₁ h₁) (𝟙 _)).unit.naturality u
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp]
  exact congrArg
    (fun m => (PresheafOfModules.sheafification (R := commRingSheaf J A₂ h₂) (𝟙 _)).map m)
    ((congrArg (fun m => (changeOfRings θ).map m) h).trans
      (CategoryTheory.Functor.map_comp (changeOfRings θ) _ _))

/-- **The comparison isomorphism of `extendScalarsSheafifyIso` is natural.** This is
`sheafifyMap_changeOfRings_unit_square`, read through the definitions of extension of scalars
and of the comparison isomorphism. -/
theorem extendScalarsSheafifyIso_naturality
    {P Q : PresheafOfModules.{w} (ringPresheaf A₁)} (u : P ⟶ Q) :
    (changeOfRingsCompSheafify θ h₂).map u ≫ (extendScalarsSheafifyIso θ h₁ h₂ Q).hom =
      (extendScalarsSheafifyIso θ h₁ h₂ P).hom ≫
        (extendScalarsFunctor θ h₁ h₂).map
          ((Stacks.SheafOfModules.sheafifyFunctor A₁ h₁).map u) :=
  sheafifyMap_changeOfRings_unit_square θ h₁ h₂ u

/-- **Extension of scalars commutes with sheafification**, as a natural isomorphism
`A₂ ⊗_{p,A₁} (-) ⋙ (-)^# ≅ (-)^# ⋙ A₂ ⊗_{A₁} (-)`. This is the lifting isomorphism of the
localization. -/
noncomputable def sheafifyChangeOfRingsNatIso :
    changeOfRingsCompSheafify θ h₂ ≅
      Stacks.SheafOfModules.sheafifyFunctor A₁ h₁ ⋙ extendScalarsFunctor θ h₁ h₂ :=
  NatIso.ofComponents (fun P => extendScalarsSheafifyIso θ h₁ h₂ P)
    fun {_ _} u => extendScalarsSheafifyIso_naturality θ h₁ h₂ u

/-- Extension of scalars lifts change of rings followed by sheafification, along
sheafification. -/
noncomputable instance extendScalarsLifting :
    Localization.Lifting (Stacks.SheafOfModules.sheafifyFunctor A₁ h₁)
      (Stacks.SheafOfModules.localIso (J := J) A₁) (changeOfRingsCompSheafify θ h₂)
      (extendScalarsFunctor θ h₁ h₂) :=
  ⟨(sheafifyChangeOfRingsNatIso θ h₁ h₂).symm⟩

section Localized

attribute [local instance] Stacks.SheafOfModules.monoidalCategory

/-- Change of rings followed by sheafification is monoidal: the first factor is monoidal by Tag
03CU (`Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsMonoidal`) and the second is the
monoidal localization functor. -/
@[instance_reducible]
noncomputable def changeOfRingsCompSheafifyMonoidal :
    (changeOfRingsCompSheafify θ h₂).Monoidal :=
  letI := changeOfRingsMonoidal θ
  letI := Stacks.SheafOfModules.sheafifyFunctor_monoidal A₂ h₂
  inferInstance

/-- **Extension of scalars for sheaves of modules is a monoidal functor**, for the localized
monoidal structure `Stacks.SheafOfModules.monoidalCategory` on each side. -/
@[instance_reducible]
noncomputable def extendScalarsMonoidalLocalized :
    (extendScalarsFunctor θ h₁ h₂).Monoidal :=
  letI := Stacks.SheafOfModules.sheafifyFunctor_monoidal A₁ h₁
  letI := changeOfRingsCompSheafifyMonoidal θ h₂
  Localization.Monoidal.functorMonoidalOfComp (Stacks.SheafOfModules.sheafifyFunctor A₁ h₁)
    (Stacks.SheafOfModules.localIso (J := J) A₁) (extendScalarsFunctor θ h₁ h₂)
    (changeOfRingsCompSheafify θ h₂)

/-- Extension of scalars, retyped between the two type synonyms carrying the localized monoidal
structures. -/
noncomputable abbrev extendScalarsLocalized :
    Stacks.SheafOfModules.SliceRestriction.localizedSrc A₁ h₁ ⥤
      Stacks.SheafOfModules.SliceRestriction.localizedSrc A₂ h₂ :=
  extendScalarsFunctor θ h₁ h₂

/-- `extendScalarsMonoidalLocalized`, read at the type-synonym spelling. -/
@[instance_reducible]
noncomputable def extendScalarsLocalizedMonoidal :
    (extendScalarsLocalized θ h₁ h₂).Monoidal :=
  extendScalarsMonoidalLocalized θ h₁ h₂

end Localized

section Strict

attribute [local instance] Stacks.SheafOfModules.Strict.monoidalCategory

/-- **Extension of scalars for sheaves of modules is a monoidal functor for the monoidal
structure of Tag 01CA**, whose tensor product is the tensor product sheaf
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf` on the nose.

This is `extendScalarsMonoidalLocalized` composed with the two identity-functor comparisons
between the strict and the localized spellings of the monoidal structure on sheaves of
modules. -/
@[instance_reducible]
noncomputable def extendScalarsStrictMonoidal :
    (extendScalarsFunctor θ h₁ h₂).Monoidal :=
  letI := extendScalarsLocalizedMonoidal θ h₁ h₂
  letI := Stacks.SheafOfModules.SliceRestriction.toLocalizedMonoidalMonoidal A₁ h₁
  letI := Stacks.SheafOfModules.SliceRestriction.fromLocalizedMonoidalMonoidal A₂ h₂
  inferInstanceAs ((Stacks.SheafOfModules.Strict.toLocalizedMonoidal A₁ h₁ ⋙
    extendScalarsLocalized θ h₁ h₂ ⋙
      Stacks.SheafOfModules.SliceRestriction.fromLocalizedMonoidal A₂ h₂).Monoidal)

end Strict

end ExtendScalarsMonoidal

/-! ## Extension of scalars along the structure map of a morphism of ringed topoi -/

section RingedTopos

universe w' v' u'

open CategoryTheory.Sheaf AlgebraicGeometry Stacks.Sheaves.ToposPushforward

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : RingedToposHom X Y)

/-- The monoidal structure of Tag 01CA on sheaves of modules over the inverse image of the
structure sheaf of the target, named at the `inverseImageRingSheaf` spelling of that sheaf of
rings so that instance search finds it there. -/
@[instance_reducible]
noncomputable def inverseImageMonoidalCategory :
    MonoidalCategory
      (SheafOfModules.{w}
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :=
  Stacks.SheafOfModules.Strict.monoidalCategory (inverseImageStructureCommRing f)
    (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property

/-- The monoidal structure of Tag 01CA on sheaves of modules on a ringed topos, named at the
`Stacks.SheafOfModules.Tensor.ringSheaf` spelling of its sheaf of rings. -/
@[instance_reducible]
noncomputable def structureMonoidalCategory :
    MonoidalCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  Stacks.SheafOfModules.Strict.monoidalCategory X.O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property

/-- **Extension of scalars along the inverse-image form `f⁻¹O_D ⟶ O_C` of the structure map of a
morphism of ringed topoi is a monoidal functor**, for the monoidal structure of Tag 01CA on each
side. This is the second of the two factors of the pullback of Stacks 03D6 part (2); the first,
the inverse image of Stacks 03D2, is not treated here. -/
@[instance_reducible]
noncomputable def extendScalarsFSharpMonoidal :
    letI := inverseImageMonoidalCategory f
    letI := structureMonoidalCategory (X := X)
    (extendScalarsFSharp f).Monoidal :=
  extendScalarsStrictMonoidal (fSharpCommRing f)
    (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property

end RingedTopos

end Stacks.Sheaves.RingedToposModules

end
