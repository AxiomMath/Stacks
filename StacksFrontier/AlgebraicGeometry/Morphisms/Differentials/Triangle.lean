module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Functoriality
public import StacksFrontier.Topology.Sheaves.Modules.Differentials.SectionwiseComparison

/-!
# The exact triangle of relative differentials of a composable pair of schemes

For morphisms of schemes `f : X ⟶ Y` and `g : Y ⟶ S` the canonical maps form an exact sequence

```
f^* Ω_{Y/S} ⟶ Ω_{X/S} ⟶ Ω_{X/Y} ⟶ 0
```

of `𝒪_X`-modules: the second map is an epimorphism, and the sequence is exact at `Ω_{X/S}`.

The content is a statement about ringed spaces, and it is proved there for the description of
`Ω` as the sheafification of sectionwise Kähler differentials. What this file adds is the
sequence for `AlgebraicGeometry.Scheme.Hom.relativeDifferentials`, which is the description of
`Ω` by corepresentability of relative derivations and is the one the rest of the scheme theory
is built on.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.sectionwiseRelativeDifferentials`, together with
  `AlgebraicGeometry.Scheme.Hom.sectionwiseRelativeDifferentialsMap` and
  `AlgebraicGeometry.Scheme.Hom.toSectionwiseRelativeDifferentials`: the sheafified description
  of `Ω` and its two canonical maps, read as a sheaf of modules on the scheme and morphisms of
  such.
* `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsIsoSectionwise`: the identification of the
  two descriptions.

## Main results

* `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsMap_eq_ringedSpace` and
  `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsMap_eq_sectionwise`: the canonical
  comparison map of a commutative square of schemes is the one of the underlying square of
  ringed spaces, and it agrees with the sheafified one under the identification.
* `AlgebraicGeometry.Scheme.Hom.toRelativeDifferentials_eq_sectionwise`: the same for the
  canonical map `Ω_{X/S} ⟶ Ω_{X/Y}` of a composable pair.
* `AlgebraicGeometry.Scheme.Hom.toRelativeDifferentials_epi` and
  `AlgebraicGeometry.Scheme.Hom.toRelativeDifferentials_exact`: the exact sequence above,
  which is Stacks Project, Tag 01UX.

## Implementation notes

The statements live at the scheme level rather than at the level of ringed spaces for a reason
of elaboration, not of mathematics. A sheaf of modules over the structure sheaf of a ringed
space `X` is written in two definitionally equal ways: over
`AlgebraicGeometry.structureSheafRing X`, whose type is
`CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat`, and over
`AlgebraicGeometry.SheafOfModules.underlyingRingSheaf X.sheaf`, whose type is
`TopCat.Sheaf RingCat X`. `TopCat.Sheaf` is a definition which instance search does not unfold
— `StacksFrontier/Topology/Sheaves/Modules/Differentials.lean:100` already records that hazard —
so a hom-set between two objects written over the second spelling is not recognised as living
in a category with zero morphisms, and `… = 0` does not elaborate there at all. At the scheme
level the ambient category is `AlgebraicGeometry.Scheme.Modules`, whose instances are declared,
and both statements elaborate.

Every comparison between the scheme level and the level of the underlying ringed spaces below
is definitional, so each object and map of the sheafified description is *defined* to be the
corresponding one for the underlying ringed spaces. Definitions rather than type ascriptions:
an ascription is discarded once elaboration is over, while a definition fixes the spelling of
the type for good, which is what the zero morphisms need. For the same reason the identification
of the two descriptions is assembled field by field rather than by ascribing the whole
isomorphism, which would ask the elaborator for one large definitional check instead of four
small ones.

## References

* [Stacks Project, Tag 01UX](https://stacks.math.columbia.edu/tag/01UX)
* [Stacks Project, Tag 08RU](https://stacks.math.columbia.edu/tag/08RU)
* [Stacks Project, Tag 0H79](https://stacks.math.columbia.edu/tag/0H79)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X' X Y S' S : Scheme.{u}}

/-- The sheaf of relative differentials of a morphism of schemes in the sheafified description:
the sheafification of the presheaf of sectionwise Kähler differentials of the structural map of
the underlying morphism of ringed spaces, read as a sheaf of modules on the source scheme. -/
noncomputable def sectionwiseRelativeDifferentials (f : X ⟶ S) : X.Modules :=
  Stacks.Sheaves.RingedSpaceDifferentials.moduleOfDifferentials f.toLRSHom.toShHom

/-- The canonical comparison map of a commutative square of schemes, in the sheafified
description. -/
noncomputable def sectionwiseRelativeDifferentialsMap (f : X' ⟶ X) (p : X ⟶ S) (p' : X' ⟶ S')
    (g : S' ⟶ S) (hcomm : f ≫ p = p' ≫ g) :
    (Scheme.Modules.pullback f).obj (sectionwiseRelativeDifferentials p) ⟶
      sectionwiseRelativeDifferentials p' :=
  Stacks.Sheaves.RingedSpaceDifferentials.differentialMap f.toLRSHom.toShHom p.toLRSHom.toShHom
    p'.toLRSHom.toShHom g.toLRSHom.toShHom (toShHom_comm hcomm)

/-- The canonical map `Ω_{X/S} ⟶ Ω_{X/Y}` of a composable pair of morphisms of schemes, in the
sheafified description. -/
noncomputable def toSectionwiseRelativeDifferentials (f : X ⟶ Y) (g : Y ⟶ S) :
    sectionwiseRelativeDifferentials (f ≫ g) ⟶ sectionwiseRelativeDifferentials f :=
  Stacks.Sheaves.RingedSpaceDifferentials.toRelativeDifferentials f.toLRSHom.toShHom
    g.toLRSHom.toShHom

/-- The sheaf of relative differentials of a morphism of schemes is the sheafification of the
presheaf of sectionwise Kähler differentials of its structural map. -/
noncomputable def relativeDifferentialsIsoSectionwise (f : X ⟶ S) :
    f.relativeDifferentials ≅ f.sectionwiseRelativeDifferentials where
  hom := (SheafOfModules.relativeDifferentialsIsoSectionwise f.toLRSHom.toShHom).hom
  inv := (SheafOfModules.relativeDifferentialsIsoSectionwise f.toLRSHom.toShHom).inv
  hom_inv_id := (SheafOfModules.relativeDifferentialsIsoSectionwise f.toLRSHom.toShHom).hom_inv_id
  inv_hom_id := (SheafOfModules.relativeDifferentialsIsoSectionwise f.toLRSHom.toShHom).inv_hom_id

/-- The canonical comparison map of a commutative square of schemes is the canonical comparison
map of the underlying square of ringed spaces. -/
theorem relativeDifferentialsMap_eq_ringedSpace (f : X' ⟶ X) (p : X ⟶ S) (p' : X' ⟶ S')
    (g : S' ⟶ S) (hcomm : f ≫ p = p' ≫ g) :
    relativeDifferentialsMap f p p' g hcomm =
      SheafOfModules.differentialMap f.toLRSHom.toShHom p.toLRSHom.toShHom
        p'.toLRSHom.toShHom g.toLRSHom.toShHom (toShHom_comm hcomm) :=
  ((isRelativeDifferentialsMap_iff_eq f p p' g hcomm _).mp
    (Classical.choose_spec (SheafOfModules.existsUnique_differentialMap
      f.toLRSHom.toShHom p.toLRSHom.toShHom p'.toLRSHom.toShHom g.toLRSHom.toShHom
      (toShHom_comm hcomm))).1).symm

/-- **The canonical comparison maps of the two descriptions agree.** -/
theorem relativeDifferentialsMap_eq_sectionwise (f : X' ⟶ X) (p : X ⟶ S) (p' : X' ⟶ S')
    (g : S' ⟶ S) (hcomm : f ≫ p = p' ≫ g) :
    relativeDifferentialsMap f p p' g hcomm =
      (Scheme.Modules.pullback f).map (relativeDifferentialsIsoSectionwise p).hom ≫
        sectionwiseRelativeDifferentialsMap f p p' g hcomm ≫
        (relativeDifferentialsIsoSectionwise p').inv := by
  rw [relativeDifferentialsMap_eq_ringedSpace]
  exact SheafOfModules.differentialMap_eq_sectionwise f.toLRSHom.toShHom p.toLRSHom.toShHom
    p'.toLRSHom.toShHom g.toLRSHom.toShHom (toShHom_comm hcomm)

/-- **The canonical maps to the differentials over an intermediate space agree.** -/
theorem toRelativeDifferentials_eq_sectionwise (f : X ⟶ Y) (g : Y ⟶ S) :
    f.toRelativeDifferentials g =
      (relativeDifferentialsIsoSectionwise (f ≫ g)).hom ≫
        toSectionwiseRelativeDifferentials f g ≫
        (relativeDifferentialsIsoSectionwise f).inv := by
  have hnat := ((Scheme.Modules.pullbackId X).inv.naturality
    (relativeDifferentialsIsoSectionwise (f ≫ g)).hom).symm
  rw [toRelativeDifferentials,
    relativeDifferentialsMap_eq_sectionwise (𝟙 X) (f ≫ g) f g (Category.id_comp (f ≫ g)),
    toSectionwiseRelativeDifferentials,
    Stacks.Sheaves.RingedSpaceDifferentials.toRelativeDifferentials, ← Category.assoc, hnat]
  simp only [Category.assoc]
  rfl

/-- In the sheafified description the canonical map `Ω_{X/S} ⟶ Ω_{X/Y}` of a composable pair is
an epimorphism. This is Stacks Project, Tag 0H79 for the underlying ringed spaces, read as a
statement about sheaves of modules on the scheme. -/
theorem toSectionwiseRelativeDifferentials_epi (f : X ⟶ Y) (g : Y ⟶ S) :
    Epi (toSectionwiseRelativeDifferentials f g) :=
  Stacks.Sheaves.RingedSpaceDifferentials.triangleDifferentials_epi
    f.toLRSHom.toShHom g.toLRSHom.toShHom

/-- In the sheafified description the two canonical maps of a composable pair compose to zero
and the resulting complex is exact at `Ω_{X/S}`. This is Stacks Project, Tag 0H79 for the
underlying ringed spaces, read as a statement about sheaves of modules on the scheme. -/
theorem toSectionwiseRelativeDifferentials_exact (f : X ⟶ Y) (g : Y ⟶ S) :
    ∃ h : sectionwiseRelativeDifferentialsMap f g (f ≫ g) (𝟙 S)
          (Category.comp_id (f ≫ g)).symm ≫ toSectionwiseRelativeDifferentials f g = 0,
      (ShortComplex.mk _ _ h).Exact := by
  obtain ⟨hsec, hexact⟩ :=
    Stacks.Sheaves.RingedSpaceDifferentials.triangleDifferentials_exact
      f.toLRSHom.toShHom g.toLRSHom.toShHom
  exact ⟨hsec, hexact⟩

/-- **Stacks Project, Tag 01UX.** The canonical map `Ω_{X/S} ⟶ Ω_{X/Y}` of a composable pair of
morphisms of schemes is an epimorphism; equivalently, the canonical sequence
`f^* Ω_{Y/S} ⟶ Ω_{X/S} ⟶ Ω_{X/Y} ⟶ 0` is exact at `Ω_{X/Y}`. For the underlying ringed spaces
this is Stacks Project, Tag 0H79. -/
@[stacks 01UX "exactness at the right term"]
theorem toRelativeDifferentials_epi (f : X ⟶ Y) (g : Y ⟶ S) :
    Epi (f.toRelativeDifferentials g) := by
  rw [toRelativeDifferentials_eq_sectionwise]
  exact epi_comp' inferInstance
    (epi_comp' (toSectionwiseRelativeDifferentials_epi f g) inferInstance)

/-- **Stacks Project, Tag 01UX.** For morphisms of schemes `f : X ⟶ Y` and `g : Y ⟶ S` the
canonical maps of relative differentials, both obtained from
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsMap`, form a complex
`f^* Ω_{Y/S} ⟶ Ω_{X/S} ⟶ Ω_{X/Y}` which is exact at `Ω_{X/S}`. Together with
`AlgebraicGeometry.Scheme.Hom.toRelativeDifferentials_epi` this is the exactness of
`f^* Ω_{Y/S} ⟶ Ω_{X/S} ⟶ Ω_{X/Y} ⟶ 0`. For the underlying ringed spaces this is Stacks
Project, Tag 0H79. -/
@[stacks 01UX "exactness at the middle term"]
theorem toRelativeDifferentials_exact (f : X ⟶ Y) (g : Y ⟶ S) :
    ∃ h : relativeDifferentialsMap f g (f ≫ g) (𝟙 S) (Category.comp_id (f ≫ g)).symm ≫
        f.toRelativeDifferentials g = 0,
      (ShortComplex.mk _ _ h).Exact := by
  obtain ⟨hsec, hexact⟩ := toSectionwiseRelativeDifferentials_exact f g
  have hdm := relativeDifferentialsMap_eq_sectionwise f g (f ≫ g) (𝟙 S)
    (Category.comp_id (f ≫ g)).symm
  have htr := toRelativeDifferentials_eq_sectionwise f g
  have hmono : Mono (relativeDifferentialsIsoSectionwise f).hom := inferInstance
  set c := relativeDifferentialsMap f g (f ≫ g) (𝟙 S) (Category.comp_id (f ≫ g)).symm
  set t := f.toRelativeDifferentials g
  set d := sectionwiseRelativeDifferentialsMap f g (f ≫ g) (𝟙 S)
    (Category.comp_id (f ≫ g)).symm
  set v := toSectionwiseRelativeDifferentials f g
  set e₂ := (relativeDifferentialsIsoSectionwise (f ≫ g)).hom
  set e₃ := (relativeDifferentialsIsoSectionwise f).hom
  set P := (Scheme.Modules.pullback f).map (relativeDifferentialsIsoSectionwise g).hom
  have hcomm₁₂ : P ≫ d = c ≫ e₂ := by
    rw [hdm]; simp
  have hcomm₂₃ : e₂ ≫ v = t ≫ e₃ := by
    rw [htr]; simp
  have hzero : c ≫ t = 0 := by
    rw [← cancel_mono e₃, Category.assoc, ← hcomm₂₃, ← Category.assoc, ← hcomm₁₂,
      Category.assoc, hsec, comp_zero, zero_comp]
  exact ⟨hzero, ShortComplex.exact_of_iso
    (ShortComplex.isoMk
        ((Scheme.Modules.pullback f).mapIso (relativeDifferentialsIsoSectionwise g))
        (relativeDifferentialsIsoSectionwise (f ≫ g))
        (relativeDifferentialsIsoSectionwise f) hcomm₁₂ hcomm₂₃
      (S₁ := ShortComplex.mk _ _ hzero) (S₂ := ShortComplex.mk d v hsec)).symm hexact⟩

end AlgebraicGeometry.Scheme.Hom

end
