module

public import StacksFrontier.AlgebraicGeometry.Cohomology.SectionsSurjective
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.ModuleAbelianVanishing
public import StacksFrontier.AlgebraicGeometry.Thickenings.SquareZeroPushforward

/-!
# The pushed-forward quotient map of a square-zero extension is surjective where `R¹` vanishes

`Stacks.Thickenings.SquareZeroExtension.pushforward` takes two hypotheses that are genuine
input rather than bookkeeping, and the first of them is local surjectivity of the pushed-forward
quotient map `g_*A ⟶ g_*𝒪_Z ≅ 𝒪_V`.  This file supplies it from a cohomological vanishing, which
is where it comes from in practice: the defining sequence

```
0 ⟶ I ⟶ A ⟶ 𝒪_Z ⟶ 0
```

of the extension is short exact as a sequence of sheaves of abelian groups
(`Stacks.Thickenings.SquareZeroExtension.kernelSheaf_sequence_shortExact`), direct image along a
continuous map is additive and left exact, and a left exact functor is right exact at a short
exact sequence whose first term has vanishing `R¹`
(`Stacks.Cohomology.shortExact_map_of_isZero_rightDerived_one`).  So `g_*A ⟶ g_*𝒪_Z` is an
epimorphism of sheaves of abelian groups, which is local surjectivity.

## Main results

* `Stacks.Thickenings.additive_sheafPushforward`: direct image of sheaves of abelian groups along
  a continuous map is additive.
* `Stacks.Thickenings.SquareZeroExtension.isLocallySurjective_pushforward_π`: **the pushed-forward
  quotient map is locally surjective** as soon as `R¹g_*` annihilates the kernel of the extension.
* `Stacks.Thickenings.SquareZeroExtension.isLocallySurjective_pushforward_π_comp`: the same
  statement in the exact shape the hypothesis `hπ` of
  `Stacks.Thickenings.SquareZeroExtension.pushforward` asks for.

## Implementation notes

The vanishing hypothesis is stated for the direct image of sheaves of *abelian groups*, because
that is the category in which the defining sequence of a square-zero extension lives: the
extension sheaf `A` is a sheaf of rings and not a sheaf of `𝒪_Z`-modules, there being no section
of the quotient map, so the sequence has no module-level form and the argument cannot be run in
`AlgebraicGeometry.Scheme.Modules`.  Only the kernel `I` is a module, and it enters the statement
through `SheafOfModules.toSheaf`.

Local surjectivity is a property of the underlying map of presheaves of types, so it passes
between the ring-valued quotient map and its additive part without any computation:
`CategoryTheory.Presheaf.isLocallySurjective_iff_whisker_forget` reduces both to the same
whiskered map, which is why the proof needs no comparison of the two sheaf-theoretic sequences.

## References

* [Stacks Project, Tag 05YV](https://stacks.math.columbia.edu/tag/05YV)
* [Stacks Project, Tag 0E3X](https://stacks.math.columbia.edu/tag/0E3X)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped AlgebraicGeometry

universe u

namespace Stacks.Thickenings

/-- **Direct image of sheaves of abelian groups along a continuous map is additive.** Addition
of morphisms of sheaves is computed on sections over each object, and the direct image only
reindexes those. -/
instance additive_sheafPushforward {X Y : TopCat.{u}} (φ : X ⟶ Y) :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} φ).Additive :=
  CategoryTheory.Functor.additive_of_preserves_binary_products _

variable {W Z S : Scheme.{u}} {f : W ⟶ S}

/-- **The pushed-forward quotient map of a square-zero extension is locally surjective where
`R¹` of the kernel vanishes.** For a square-zero extension `E` of `𝒪_W` and a morphism
`g : W ⟶ Z`, the direct image `g_*A ⟶ g_*𝒪_W` of the quotient map is locally surjective as soon
as the first right derived functor of the direct image annihilates the kernel of `E`.

The defining sequence of the extension is short exact
(`Stacks.Thickenings.SquareZeroExtension.kernelSheaf_sequence_shortExact`) and direct image is
additive and left exact, so `Stacks.Cohomology.shortExact_map_of_isZero_rightDerived_one` makes
the
pushed-forward sequence short exact; its third map is therefore an epimorphism, and an
epimorphism of sheaves of abelian groups is locally surjective. -/
theorem SquareZeroExtension.isLocallySurjective_pushforward_π (E : SquareZeroExtension f)
    (g : W ⟶ Z)
    (h : IsZero (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} g.base).rightDerived 1).obj
      ((SheafOfModules.toSheaf W.ringCatSheaf).obj E.I))) :
    TopCat.Presheaf.IsLocallySurjective
      ((TopCat.Presheaf.pushforward CommRingCat.{u} g.base).map E.π.hom) := by
  have hse := Stacks.Cohomology.shortExact_map_of_isZero_rightDerived_one
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} g.base)
    E.kernelSheaf_sequence_shortExact h
  have hepi : Epi ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} g.base).map
      E.quotientSheafMap) := hse.epi_g
  have hls : TopCat.Presheaf.IsLocallySurjective
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} g.base).map
        E.quotientSheafMap).hom :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi _).mpr hepi
  have htype : TopCat.Presheaf.IsLocallySurjective
      (Functor.whiskerRight ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} g.base).map
        E.quotientSheafMap).hom (forget AddCommGrpCat.{u})) :=
    (CategoryTheory.Presheaf.isLocallySurjective_iff_whisker_forget
      (Opens.grothendieckTopology (Z : TopCat)) _).mp hls
  refine (CategoryTheory.Presheaf.isLocallySurjective_iff_whisker_forget
    (Opens.grothendieckTopology (Z : TopCat))
    ((TopCat.Presheaf.pushforward CommRingCat.{u} g.base).map E.π.hom)).mpr ?_
  exact htype

/-- **The hypothesis `hπ` of the pushforward, from the vanishing of `R¹`.** This is
`Stacks.Thickenings.SquareZeroExtension.isLocallySurjective_pushforward_π` composed with the
inverse structure-sheaf comparison, which is the exact shape
`Stacks.Thickenings.SquareZeroExtension.pushforward` asks for. -/
theorem SquareZeroExtension.isLocallySurjective_pushforward_π_comp
    (E : SquareZeroExtension f) (g : W ⟶ Z) [IsIso g.c]
    (h : IsZero (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} g.base).rightDerived 1).obj
      ((SheafOfModules.toSheaf W.ringCatSheaf).obj E.I))) :
    TopCat.Presheaf.IsLocallySurjective
      ((TopCat.Presheaf.pushforward CommRingCat.{u} g.base).map E.π.hom
        ≫ structureComparisonInv g) :=
  isLocallySurjective_comp_structureComparisonInv g E.π.hom
    (E.isLocallySurjective_pushforward_π g h)

/-- **The hypothesis `hπ` of the pushforward, from a vanishing stated in sheaves of modules.**
This is the form a consumer meets it in: a vanishing theorem for `R¹g_*` is proved in sheaves of
modules, where the kernel of the extension lives, and
`Stacks.AlgebraicGeometry.HigherDirectImage.isZero_rightDerived_abelianPushforward_toSheaf`
carries it to the sheaves of abelian groups in which the defining sequence of the extension
lies. -/
theorem SquareZeroExtension.isLocallySurjective_pushforward_π_comp_of_isZero_rightDerived
    (E : SquareZeroExtension f) (g : W ⟶ Z) [IsIso g.c]
    (h : IsZero (((Scheme.Modules.pushforward g).rightDerived 1).obj E.I)) :
    TopCat.Presheaf.IsLocallySurjective
      ((TopCat.Presheaf.pushforward CommRingCat.{u} g.base).map E.π.hom
        ≫ structureComparisonInv g) :=
  E.isLocallySurjective_pushforward_π_comp g
    (Stacks.AlgebraicGeometry.HigherDirectImage.isZero_rightDerived_abelianPushforward_toSheaf
      g 1 E.I h)

end Stacks.Thickenings

end
