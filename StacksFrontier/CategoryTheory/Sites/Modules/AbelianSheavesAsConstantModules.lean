module

public import StacksFrontier.CategoryTheory.Sites.Modules.TorsionSheavesAsZModModules
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Abelian sheaves are the modules over the constant sheaf of rings `ℤ`

Let `(C, J)` be a site. Reading an abelian sheaf as a sheaf of modules over the constant sheaf of
rings `ℤ/mℤ` is, on the `m`-torsion sheaves, an equivalence of categories:
`StacksFrontier.CategoryTheory.Sites.Modules.TorsionSheavesAsZModModules` builds the functor in one
direction, and this file proves that the forgetful functor

`SheafOfModules.toSheaf : SheafOfModules ℤ/mℤ̲ ⥤ Sheaf J AddCommGrpCat`

is fully faithful, hence -- at `m = 0`, where the torsion condition is vacuous -- an
**equivalence onto all abelian sheaves**.

The two halves are of different natures. Essential surjectivity is
`Stacks.Cohomology.ZModSheaf.torsionSheafToModulesIso`, already available. Full faithfulness is
the statement that an additive map between two sheaves of `ℤ/mℤ̲`-modules is automatically
`ℤ/mℤ̲`-linear, and it is *not* pointwise: a section of the constant sheaf of rings over an
object is only locally an integer, so linearity holds only after passing to a covering. The
local argument is Mathlib's, in the shape of the sheafification adjunction

```
PresheafOfModules.sheafification α ⊣
  SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars α
```

for `α` the sheafification map of the constant presheaf of rings: that adjunction has invertible
counit, so its right adjoint is fully faithful, which says exactly that restricting scalars along
`α` loses nothing on sheaves. Over the constant *presheaf* of rings, by contrast, linearity is
automatic and pointwise (`Stacks.Cohomology.ZModSheaf.map_smul_of_isAddHom`), which is the
content of `Stacks.Cohomology.ZModSheaf.toPresheafFullyFaithful` below.

## Main definitions

* `Stacks.Cohomology.ZModSheaf.toPresheafFullyFaithful`: over the constant *presheaf* of rings
  `ℤ/mℤ`, the forgetful functor to abelian presheaves is fully faithful.
* `Stacks.Cohomology.ZModSheaf.toSheafFullyFaithful`: over the constant *sheaf* of rings
  `ℤ/mℤ`, the forgetful functor to abelian sheaves is fully faithful.

## Main results

* `Stacks.Cohomology.ZModSheaf.toSheaf_isEquivalence`: at `m = 0` the forgetful functor
  `SheafOfModules.toSheaf ℤ̲ ⥤ Sheaf J AddCommGrpCat` is an **equivalence**.
* `Stacks.Cohomology.ZModSheaf.sectionsIso`: under it, the module of sections of a sheaf of
  modules over an object is the group of sections of the corresponding abelian sheaf.

## Implementation notes

`ZMod 0` is `ℤ`, so `m = 0` needs no separate construction: the annihilation hypothesis of
`torsionSheafToModules` is `0 • x = 0`, which `zero_smul` discharges, and the ring of scalars is
`ULift (ZMod 0)`, whose universe is therefore free of the universes of the site. This is why the
equivalence is stated for every `m` and specialised at the end rather than proved only for `ℤ`.

Full faithfulness is assembled through `CategoryTheory.Functor.FullyFaithful.ofCompFaithful` at
`sheafToPresheaf`, and the composite `SheafOfModules.toSheaf ⋙ sheafToPresheaf` is *not* given to
it directly: it is reached through the natural isomorphism `toSheafCompSheafToPresheafIso` with
the composite of the adjunction's right adjoint and `PresheafOfModules.toPresheaf`, both of which
are fully faithful. The two functors agree on objects and morphisms but are built from different
terms, so the isomorphism is `Iso.refl`-components rather than an equality.

## References

* [Stacks Project, Tag 0DD8](https://stacks.math.columbia.edu/tag/0DD8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t s v u

namespace Stacks.Cohomology.ZModSheaf

variable {C : Type u} [Category.{v} C]

/-- **Over the constant presheaf of rings `ℤ/mℤ`, forgetting the module structure of a presheaf
of modules loses nothing.** A scalar is the image of an integer, so an additive map between two
such presheaves of modules is linear, and that is the preimage of the morphism of abelian
presheaves. -/
@[sga "3 I 3.1.3" "full faithfulness"]
public def toPresheafFullyFaithful (m : ℕ) :
    (PresheafOfModules.toPresheaf (zmodPresheaf.{s} C m)).FullyFaithful where
  preimage {M N} φ := PresheafOfModules.homMk φ (by
    intro X r x
    let : Module (ULift.{s, 0} (ZMod m)) (ToType (M.obj X)) := (M.obj X).isModule
    let : Module (ULift.{s, 0} (ZMod m)) (ToType (N.obj X)) := (N.obj X).isModule
    let : Module (ULift.{s, 0} (ZMod m)) (ToType (M.presheaf.obj X)) := (M.obj X).isModule
    let : Module (ULift.{s, 0} (ZMod m)) (ToType (N.presheaf.obj X)) := (N.obj X).isModule
    exact map_smul_of_isAddHom (m := m) _ r x)
  map_preimage _ := rfl
  preimage_map _ := PresheafOfModules.hom_ext (fun _ ↦ rfl)

section Sheaves

variable (J : GrothendieckTopology C) (m : ℕ)
  [HasSheafify J CommRingCat.{s}] [J.WEqualsLocallyBijective CommRingCat.{s}]
  [HasWeakSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}]

/-- The underlying abelian presheaf of a sheaf of modules over the constant sheaf of rings
`ℤ/mℤ`, read in two ways: by forgetting the sheaf condition after forgetting the module
structure, and by restricting the scalars to the constant presheaf of rings first. -/
public def toSheafCompSheafToPresheafIso :
    SheafOfModules.toSheaf.{t} (zmodRingSheaf.{s} J m) ⋙
        sheafToPresheaf J AddCommGrpCat.{t} ≅
      (SheafOfModules.forget (zmodRingSheaf.{s} J m) ⋙
          PresheafOfModules.restrictScalars (zmodRingMap.{s} J m)) ⋙
        PresheafOfModules.toPresheaf (zmodPresheaf.{s} C m) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

/-- **Over the constant sheaf of rings `ℤ/mℤ`, forgetting the module structure of a sheaf of
modules loses nothing.** Restricting the scalars along the sheafification map of the constant
presheaf of rings is fully faithful, the counit of the sheafification adjunction being
invertible, and forgetting the module structure over the constant presheaf is fully faithful by
`Stacks.Cohomology.ZModSheaf.toPresheafFullyFaithful`. -/
public def toSheafFullyFaithful :
    (SheafOfModules.toSheaf.{t} (zmodRingSheaf.{s} J m)).FullyFaithful := by
  refine Functor.FullyFaithful.ofCompFaithful
    (G := sheafToPresheaf J AddCommGrpCat.{t}) ?_
  refine Functor.FullyFaithful.ofIso ?_ (toSheafCompSheafToPresheafIso.{t, s} J m).symm
  exact ((PresheafOfModules.sheafificationAdjunction
    (zmodRingMap.{s} J m)).fullyFaithfulROfIsIsoCounit).comp
      (toPresheafFullyFaithful.{s} m)

/-- **Every abelian sheaf is the underlying abelian sheaf of a sheaf of modules over the constant
sheaf of rings `ℤ`.** The annihilation hypothesis of
`Stacks.Cohomology.ZModSheaf.torsionSheafToModules` is vacuous at `m = 0`. -/
public instance toSheaf_essSurj :
    (SheafOfModules.toSheaf.{t} (zmodRingSheaf.{s} J 0)).EssSurj :=
  ⟨fun F ↦ ⟨torsionSheafToModules.{t, s} J 0 F (fun _ x ↦ zero_smul _ x),
    ⟨torsionSheafToModulesIso.{t, s} J 0 F (fun _ x ↦ zero_smul _ x)⟩⟩⟩

/-- **Abelian sheaves are the sheaves of modules over the constant sheaf of rings `ℤ`.** -/
public instance toSheaf_isEquivalence :
    (SheafOfModules.toSheaf.{t} (zmodRingSheaf.{s} J 0)).IsEquivalence :=
  letI ff := toSheafFullyFaithful.{t, s} J 0
  letI := ff.full
  letI := ff.faithful
  { }

/-- Under the identification of abelian sheaves with modules over the constant sheaf of rings
`ℤ/mℤ`, the module of sections over an object is the group of sections over that object. -/
public def sectionsIso (U : Cᵒᵖ) :
    SheafOfModules.evaluation (zmodRingSheaf.{s} J m) U ⋙
        forget₂ (ModuleCat.{t} (ToType ((zmodRingSheaf.{s} J m).obj.obj U)))
          AddCommGrpCat.{t} ≅
      SheafOfModules.toSheaf.{t} (zmodRingSheaf.{s} J m) ⋙
        (sheafSections J AddCommGrpCat.{t}).obj U :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

end Sheaves

end Stacks.Cohomology.ZModSheaf

end
