module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeFiniteFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFpqcLocality

/-!
# Finite local freeness of morphisms of algebraic spaces is fpqc local on the base

Let `S` be a scheme contained in a big fppf site `B`. Being finite locally free is, for a
morphism of algebraic spaces over `S`, local on the base for the fpqc topology of
**Stacks 03YH**: such a morphism is finite locally free exactly when its base change to every
member of some fpqc covering family of its target is finite locally free. This is
**Stacks 042C**.

A morphism of algebraic spaces is finite locally free exactly when it is finite, flat and
locally of finite presentation (**Stacks 0416**, conditions (1) and (2)); finiteness is fpqc
local on the base by **Stacks 0426**, flatness by **Stacks 041W** and local finite presentation
by **Stacks 041T**; and locality on the base passes to an infimum of morphism properties.

## Main definitions

* `AlgebraicGeometry.Space.finiteLocallyFreeMorphismProperty`: finite local freeness of a
  morphism of algebraic spaces over `S`, in the representable sense of Stacks 03ZW,
  condition (1), as a `CategoryTheory.MorphismProperty` on
  `AlgebraicGeometry.AlgebraicSpaces`, the spelling at which locality on the base is stated.

## Main results

* `AlgebraicGeometry.Space.finiteLocallyFreeMorphismProperty_eq_inf`: finite local freeness
  *is* finiteness together with flatness and local finite presentation, as morphism properties.
* `AlgebraicGeometry.Space.isFiniteLocallyFree_isLocalAtTarget_fpqc`: **Stacks 042C**.
* `AlgebraicGeometry.Space.isFiniteLocallyFree_isLocalAtTarget_fppf`: the same statement at the
  fppf precoverage, which is the form the relative properties of Stacks 03YK consume.

## Implementation notes

Finite local freeness is read, as throughout these files, in the representable sense of
Stacks 03ZW, condition (1): the morphism is representable and every represented base change of
it is a finite locally free morphism of schemes. That is
`CategoryTheory.MorphismProperty.presheaf` of the inverse image along
`AlgebraicGeometry.BigFppfOver.toScheme` of `Stacks.Morphisms.IsFiniteLocallyFree`, and it is
the side at which Stacks 0416 is available. The direct-image definition of Stacks 03ZV,
`AlgebraicGeometry.Space.IsFiniteLocallyFree`, is not used: comparing it with the representable
reading is Stacks 03ZU, which is proved — it is
`AlgebraicGeometry.Space.presheaf_iff_isFiniteLocallyFree` in
`StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRepresentableChart`, and the reduction it
rests on is `AlgebraicGeometry.Space.presheaf_iff_isFiniteLocallyFree_iff_chartComparison` — but
is not needed here, since both Stacks 0416 and the fpqc locality below are stated at the
representable reading, so no statement here mentions the direct image of the structure sheaf.

The three conjuncts are bracketed as `(finite ⊓ flat) ⊓ locally of finite presentation`, the
order in which the two instances supplied by
`CategoryTheory.MorphismProperty.IsLocalAtTarget.inf` compose without reassociation, which is
why the equivalence of Stacks 0416 is reassociated rather than used as it stands.

The index universe of a covering family is a free universe parameter of
`AlgebraicGeometry.Space.Topology.precoverage` and stays free here, as it does in Stacks 0426,
Stacks 041W and Stacks 041T.

## References

* [Stacks Project, Tag 03ZW](https://stacks.math.columbia.edu/tag/03ZW)
* [Stacks Project, Tag 0416](https://stacks.math.columbia.edu/tag/0416)
* [Stacks Project, Tag 041T](https://stacks.math.columbia.edu/tag/041T)
* [Stacks Project, Tag 041W](https://stacks.math.columbia.edu/tag/041W)
* [Stacks Project, Tag 0426](https://stacks.math.columbia.edu/tag/0426)
* [Stacks Project, Tag 042C](https://stacks.math.columbia.edu/tag/042C)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Being finite locally free in the representable sense of **Stacks 03ZW**, condition (1) — the
morphism is representable and every represented base change of it is a finite locally free
morphism of schemes — as a property of morphisms in the category of algebraic spaces over `S`.
This is the spelling at which locality on the base, Stacks 03YH, is stated. -/
abbrev finiteLocallyFreeMorphismProperty : MorphismProperty (AlgebraicSpaces B S hS) :=
  fun _ _ f => (MorphismProperty.inverseImage
    (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf f.hom

/-- **Stacks 0416, conditions (1) and (2), at the packaged spelling**: finite local freeness of
morphisms of algebraic spaces over `S` is the infimum of finiteness (Stacks 03ZP), flatness
(Stacks 03ML, part (1)) and local finite presentation (Stacks 03XP, part (1)) as morphism
properties. -/
theorem finiteLocallyFreeMorphismProperty_eq_inf :
    finiteLocallyFreeMorphismProperty B S hS =
      (finiteMorphismProperty B S hS ⊓
          fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) => IsFlat B S hS f.hom) ⊓
        fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) =>
          IsLocallyOfFinitePresentation B S hS f.hom := by
  funext X Y f
  exact propext
    ((isFiniteLocallyFree_presheaf_iff B S hS X.property Y.property f.hom).trans and_assoc.symm)

/-- **Stacks 042C.** Being finite locally free is, for morphisms of algebraic spaces over `S`,
local on the base for the fpqc topology of Stacks 03YH: such a morphism is finite locally free
exactly when its base change to every member of some fpqc covering family of its target is
finite locally free.

A morphism is finite locally free exactly when it is finite, flat and locally of finite
presentation (**Stacks 0416**), finiteness is fpqc local on the base by **Stacks 0426**,
flatness by **Stacks 041W** and local finite presentation by **Stacks 041T**, so their
conjunction is. -/
@[stacks 042C]
instance isFiniteLocallyFree_isLocalAtTarget_fpqc :
    (finiteLocallyFreeMorphismProperty B S hS).IsLocalAtTarget
      (Topology.precoverage.{u, v} .fpqc B S hS) := by
  have : MorphismProperty.IsLocalAtTarget
      (finiteMorphismProperty B S hS ⊓
        fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) => IsFlat B S hS f.hom)
      (Topology.precoverage.{u, v} .fpqc B S hS) :=
    MorphismProperty.IsLocalAtTarget.inf _ _
  rw [finiteLocallyFreeMorphismProperty_eq_inf]
  exact MorphismProperty.IsLocalAtTarget.inf _ _

/-- **Stacks 042C** at the fppf precoverage: being finite locally free is local on the target
for the fppf topology of algebraic spaces. This is the form in which Stacks 03YK's relative
properties ask for it, and it follows from the fpqc form because every fppf covering family of
algebraic spaces is an fpqc covering family. -/
instance isFiniteLocallyFree_isLocalAtTarget_fppf :
    (finiteLocallyFreeMorphismProperty B S hS).IsLocalAtTarget
      (Topology.precoverage.{u, v} .fppf B S hS) :=
  .of_le (fppfPrecoverage_le_fpqcPrecoverage B S hS)

end AlgebraicGeometry.Space

end
