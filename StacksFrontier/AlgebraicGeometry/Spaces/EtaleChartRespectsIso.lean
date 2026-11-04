module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType

/-!
# The étale-chart condition respects isomorphisms of presheaves

Let `P` be a property of morphisms of schemes. **Stacks 03MJ**, condition (1), attaches to a
morphism `f : F ⟶ G` of presheaves on the big fppf site over `S` the condition that `P` hold of
the scheme morphism underlying every commuting square of étale charts of `f`
(`AlgebraicGeometry.Space.HoldsOnEveryEtaleChart`). This module records that the condition is
invariant under pre- and post-composition with an isomorphism, so that it is a
`CategoryTheory.MorphismProperty.RespectsIso` on presheaves.

The proof is the one the chart condition always admits: an isomorphism composed with an étale
chart is again an étale chart, because the étale condition on charts is itself a
`RespectsIso` property, and the commuting square of the composite is the original square
reassociated.

## Main results

* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_respectsIso_presheaf`: the chart condition of
  Stacks 03MJ respects isomorphisms of presheaves.
* `AlgebraicGeometry.Space.isLocallyOfFiniteType_respectsIso`: the same at the
  locally-of-finite-type property of Stacks 03XF.
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_terminal_iff_of_iso`: isomorphic presheaves have
  structural morphisms with the same chart condition.
* `AlgebraicGeometry.Space.isLocallyOfFiniteType_terminal_iff_of_iso`: isomorphic presheaves have
  locally-of-finite-type structural morphisms together.

## Implementation notes

The library already carries `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_respectsIso`
(`StacksFrontier/AlgebraicGeometry/Spaces/FpqcSourceLocalityTransfer.lean`), which is this statement
for morphisms of the category
`AlgebraicGeometry.AlgebraicSpaces` of algebraic spaces over `S`, i.e. for `f.hom` with `f` a
morphism of that full subcategory. That form cannot be applied to a morphism of presheaves that
are not known to be algebraic spaces, and `HoldsOnEveryEtaleChart` is defined at presheaf
generality, so the statement here is the general one and the existing form is its restriction.
Nothing is changed in the restricted form: it is in active use by three source-locality transfer
modules, and repointing it at this lemma is a single-declaration simplification not performed
here.

No Stacks tag attribute is placed. The chart condition's invariance under isomorphism is not a
numbered assertion of the Stacks project — Stacks 03MJ states the equivalence of the chart
conditions, which is formalized elsewhere — and the properties these results are instantiated at,
Stacks 03MJ and 03XF, already carry their sites on the declarations that state them.
-/

@[expose] public section

open CategoryTheory Limits

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 03MJ**, condition (1), respects isomorphisms of presheaves: for any property `P` of
morphisms of schemes, the condition that `P` hold on every commuting square of étale charts is
invariant under composing with an isomorphism on either side.

An isomorphism absorbed into the chart of the source leaves an étale chart, since the étale
condition on charts respects isomorphisms; absorbed through its inverse into the chart of the
target it does the same, and in both cases the commuting square of the composite is the given
square reassociated. -/
theorem holdsOnEveryEtaleChart_respectsIso_presheaf (P : MorphismProperty Scheme.{u}) :
    MorphismProperty.RespectsIso
      (fun ⦃F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (f : F ⟶ G) =>
        HoldsOnEveryEtaleChart B S hS P f) := by
  let etale : MorphismProperty Scheme.{u} := @AlgebraicGeometry.Etale.{u}
  let E0 := MorphismProperty.inverseImage etale (BigFppfOver.toScheme B S hS)
  let E := E0.presheaf
  let : MorphismProperty.RespectsIso etale :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  let : E0.RespectsIso := MorphismProperty.RespectsIso.inverseImage _ _
  let : E.RespectsIso := MorphismProperty.relative_respectsIso E0
  refine MorphismProperty.RespectsIso.mk _ ?_ ?_
  · intro F G H e f hf U V a b h ha hb hcomm
    exact hf U V (a ≫ e.hom) b h
      (MorphismProperty.RespectsIso.postcomp E e.hom a ha) hb (by
        simpa only [Category.assoc] using hcomm)
  · intro F G H e f hf U V a b h ha hb hcomm
    exact hf U V a (b ≫ e.inv) h ha
      (MorphismProperty.RespectsIso.postcomp E e.inv b hb) (by
        simpa using congrArg (· ≫ e.inv) hcomm)

/-- **Stacks 03XF**, part (1), respects isomorphisms of presheaves: being locally of finite type
is invariant under composing with an isomorphism on either side.

This is `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_respectsIso_presheaf` at the
locally-of-finite-type property of schemes, which is what
`AlgebraicGeometry.Space.IsLocallyOfFiniteType` unfolds to. -/
theorem isLocallyOfFiniteType_respectsIso :
    MorphismProperty.RespectsIso
      (fun ⦃F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (f : F ⟶ G) =>
        IsLocallyOfFiniteType B S hS f) :=
  holdsOnEveryEtaleChart_respectsIso_presheaf B S hS _

/-- **Isomorphic presheaves on the big fppf site over `S` have structural morphisms with the same
chart condition**, for any property `P` of morphisms of schemes.

The structural morphism of the source factors through the isomorphism and that of the target,
because the terminal object admits exactly one morphism from each presheaf, and the chart
condition may then be cancelled across the isomorphism. -/
theorem holdsOnEveryEtaleChart_terminal_iff_of_iso (P : MorphismProperty Scheme.{u})
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G) :
    HoldsOnEveryEtaleChart B S hS P (terminal.from F) ↔
      HoldsOnEveryEtaleChart B S hS P (terminal.from G) := by
  let Q : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    fun _ _ f => HoldsOnEveryEtaleChart B S hS P f
  let : Q.RespectsIso := holdsOnEveryEtaleChart_respectsIso_presheaf B S hS P
  rw [show terminal.from F = e.hom ≫ terminal.from G from terminal.hom_ext _ _]
  exact Q.cancel_left_of_respectsIso e.hom (terminal.from G)

/-- Isomorphic presheaves on the big fppf site over `S` have locally-of-finite-type structural
morphisms together.

This is `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_terminal_iff_of_iso` at the
locally-of-finite-type property of schemes, which is what
`AlgebraicGeometry.Space.IsLocallyOfFiniteType` unfolds to. -/
theorem isLocallyOfFiniteType_terminal_iff_of_iso
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G) :
    IsLocallyOfFiniteType B S hS (terminal.from F) ↔
      IsLocallyOfFiniteType B S hS (terminal.from G) :=
  holdsOnEveryEtaleChart_terminal_iff_of_iso B S hS _ e

end AlgebraicGeometry.Space

end
