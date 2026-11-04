module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic

/-!
# Properties of morphisms of algebraic spaces

A morphism of algebraic spaces over a scheme `S` is a natural transformation of presheaves
on the big fppf site of `S`. This file defines the basic properties such a morphism can
have: the three immersion properties, étaleness, quasi-compactness and the three
separation properties, together with the two étale-chart conditions through which
properties of scheme morphisms are transferred to morphisms of algebraic spaces.

A subfunctor of an algebraic space is an open, closed or locally closed subspace when it
is itself an algebraic space and its inclusion is an immersion of the corresponding kind.

## Main definitions

* `AlgebraicGeometry.Space.IsOpenImmersion`,
  `AlgebraicGeometry.Space.IsClosedImmersion` and `AlgebraicGeometry.Space.IsImmersion`
  are the three immersion properties for morphisms of algebraic spaces.
* `AlgebraicGeometry.Space.IsOpenSubspace`, `AlgebraicGeometry.Space.IsClosedSubspace`
  and `AlgebraicGeometry.Space.IsLocallyClosedSubspace` are the corresponding properties
  of subfunctors.
* `AlgebraicGeometry.Space.IsEtale` is étaleness of a morphism of algebraic spaces.
* `AlgebraicGeometry.Space.HoldsOnEveryEtaleChart` and
  `AlgebraicGeometry.Space.HoldsOnSurjectiveEtaleChart` are the two chart conditions
  through which a property of scheme morphisms is tested on a morphism of algebraic
  spaces.
* `AlgebraicGeometry.Space.IsQuasiCompactSpace` is quasi-compactness of an algebraic
  space, and `AlgebraicGeometry.Space.IsQuasiCompact` is quasi-compactness of a morphism
  of algebraic spaces.
* `AlgebraicGeometry.Space.IsSeparated`, `AlgebraicGeometry.Space.IsLocallySeparated` and
  `AlgebraicGeometry.Space.IsQuasiSeparated` are the three separation properties of a
  morphism of algebraic spaces, expressed through its relative diagonal.

## Main results

There are no propositional results. The definitions make representability and the tested
property of every represented base change available through
`CategoryTheory.MorphismProperty.presheaf`.

## Implementation notes

The three immersion properties use `CategoryTheory.MorphismProperty.presheaf`, which
includes both representability of the morphism and the specified property of all of its
represented pullbacks. The tested scheme properties are the inverse images along
`AlgebraicGeometry.BigFppfOver.toScheme` of Mathlib's `AlgebraicGeometry.IsOpenImmersion`,
`AlgebraicGeometry.IsClosedImmersion` and `AlgebraicGeometry.IsImmersion`, exactly as the
atlas conditions of `AlgebraicGeometry.IsAlgebraicSpace` are formed.

The three subspace properties use Mathlib's `CategoryTheory.Subfunctor`: its `toFunctor`
is the subfunctor regarded as a presheaf and its `ι` is the canonical inclusion. The
ambient presheaf need not be algebraic for any of these predicates to make sense; when it
is algebraic, they are exactly the subspaces of the source definition. Every definition
here is an abbreviation, which exposes the existing morphism-property and subfunctor API
to composition, base change and inclusion tests without conversion lemmas.

Quasi-compactness occurs in two forms, distinguished as in Mathlib's topology library:
`AlgebraicGeometry.Space.IsQuasiCompactSpace` is a property of an algebraic space, in
terms of a quasi-compact surjective étale atlas, and
`AlgebraicGeometry.Space.IsQuasiCompact` is a property of a morphism, namely that every
base change along a morphism from a quasi-compact algebraic space has quasi-compact
source.

The relative diagonal used by the separation properties is Mathlib's
`CategoryTheory.Limits.pullback.diagonal`, formed in the presheaf category. Each of the
properties here is meaningful for an arbitrary morphism of presheaves; algebraicity of
the source and target is imposed by clients, exactly as in the source definitions.

## References

* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 03E3](https://stacks.math.columbia.edu/tag/03E3)
* [Stacks Project, Tag 03FR](https://stacks.math.columbia.edu/tag/03FR)
* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
* [Stacks Project, Tag 03HL](https://stacks.math.columbia.edu/tag/03HL)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Immersions and subspaces -/

/-- **Stacks 02YU, part (1).** A morphism of algebraic spaces over `S` is an *open
immersion* when it is representable and every represented base change of it is an open
immersion of schemes. -/
@[stacks 02YU "part (1): open immersions"]
abbrev IsOpenImmersion {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) : Prop :=
  (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS))) f

/-- An open immersion of presheaves on the big fppf site is a monomorphism: it is representable
by open immersions of schemes, and those are monomorphisms. -/
public theorem mono_of_isOpenImmersion {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hf : IsOpenImmersion B S hS f) : Mono f := by
  let Q := MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u} :
    MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)
  have hQmono : Q ≤ MorphismProperty.monomorphisms (BigFppfOver B S hS) :=
    fun _ _ a ha => (BigFppfOver.toScheme B S hS).mono_of_mono_map
      (AlgebraicGeometry.IsOpenImmersion.le_monomorphisms _ ha)
  exact MorphismProperty.presheaf_monomorphisms_le_monomorphisms _
    (MorphismProperty.relative_monotone hQmono _ hf)

/-- **Stacks 02YU, part (2).** A subfunctor of a presheaf on the big fppf site of `S` is
an *open subspace* when it is an algebraic space over `S` and its inclusion is an open
immersion. -/
@[stacks 02YU "part (2): open subspaces"]
abbrev IsOpenSubspace {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (G : Subfunctor F) : Prop :=
  IsAlgebraicSpace B S hS G.toFunctor ∧ IsOpenImmersion B S hS G.ι

/-- **Stacks 02YU, part (3).** A morphism of algebraic spaces over `S` is a *closed
immersion* when it is representable and every represented base change of it is a closed
immersion of schemes. -/
@[stacks 02YU "part (3): closed immersions"]
abbrev IsClosedImmersion {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) : Prop :=
  (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS))) f

/-- Being a closed immersion, as a property of morphisms of presheaves on the big fppf site of
`S` rather than a predicate on one morphism. This is where the relative diagonal of a separated
morphism of algebraic spaces lives. -/
abbrev closedImmersionPresheafProperty :
    MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS))

/-- **Stacks 02YU, part (4).** A subfunctor of a presheaf on the big fppf site of `S` is
a *closed subspace* when it is an algebraic space over `S` and its inclusion is a closed
immersion. -/
@[stacks 02YU "part (4): closed subspaces"]
abbrev IsClosedSubspace {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (G : Subfunctor F) : Prop :=
  IsAlgebraicSpace B S hS G.toFunctor ∧ IsClosedImmersion B S hS G.ι

/-- **Stacks 02YU, part (5).** A morphism of algebraic spaces over `S` is an *immersion*
when it is representable and every represented base change of it is an immersion of
schemes. -/
@[stacks 02YU "part (5): immersions"]
abbrev IsImmersion {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) : Prop :=
  (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS))) f

/-- Being an immersion, as a property of morphisms of presheaves on the big fppf site of `S`
rather than a predicate on one morphism. This is where the relative diagonal of a morphism of
algebraic spaces lives. -/
abbrev immersionPresheafProperty :
    MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS))

/-- **Stacks 02YU, part (6).** A subfunctor of a presheaf on the big fppf site of `S` is
a *locally closed subspace* when it is an algebraic space over `S` and its inclusion is
an immersion. -/
@[stacks 02YU "part (6): locally closed subspaces"]
abbrev IsLocallyClosedSubspace {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (G : Subfunctor F) : Prop :=
  IsAlgebraicSpace B S hS G.toFunctor ∧ IsImmersion B S hS G.ι

/-! ### Étaleness and étale charts -/

/-- **Stacks 03FR.** A morphism of algebraic spaces over `S` is *étale* when its composite
with every étale morphism from a representable presheaf into its source is again étale. -/
@[stacks 03FR]
abbrev IsEtale {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) : Prop :=
  ∀ (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ F),
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ →
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (φ ≫ f)

variable (P : MorphismProperty Scheme.{u})
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 03MJ, condition (1).** A property `P` of scheme morphisms *holds on every
étale chart* of `f : F ⟶ G` when, for every commuting square of étale charts `a` of `F`
and `b` of `G` over a morphism `h` of the site, the scheme morphism underlying `h` has
`P`. -/
abbrev HoldsOnEveryEtaleChart (f : F ⟶ G) : Prop :=
  ∀ (U V : BigFppfOver B S hS)
      (a : yoneda.obj U ⟶ F) (b : yoneda.obj V ⟶ G) (h : U ⟶ V),
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a →
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b →
    yoneda.map h ≫ b = a ≫ f →
    P ((BigFppfOver.toScheme B S hS).map h)

/-- **Stacks 03MJ, condition (2).** A property `P` of scheme morphisms *holds on a
surjective étale chart* of `f : F ⟶ G` when there is one commuting square of étale charts
whose chart of `F` is in addition surjective and whose underlying scheme morphism has
`P`. -/
abbrev HoldsOnSurjectiveEtaleChart (f : F ⟶ G) : Prop :=
  ∃ (U V : BigFppfOver B S hS)
      (a : yoneda.obj U ⟶ F) (b : yoneda.obj V ⟶ G) (h : U ⟶ V),
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a ∧
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b ∧
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a ∧
    yoneda.map h ≫ b = a ≫ f ∧
    P ((BigFppfOver.toScheme B S hS).map h)

/-! ### Quasi-compactness -/

/-- **Stacks 03E3.** An algebraic space over `S` is *quasi-compact* when it admits a
surjective étale morphism from a representable presheaf whose underlying scheme is
quasi-compact. -/
@[stacks 03E3]
abbrev IsQuasiCompactSpace (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  ∃ (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ F),
    CompactSpace ((BigFppfOver.toScheme B S hS).obj U) ∧
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f ∧
    IsEtale B S hS f

/-- **A scheme of the site whose underlying space is compact represents a quasi-compact
algebraic space.** Its identity chart is surjective and étale with compact source, which is
the atlas Stacks 03E3 asks for. -/
theorem isQuasiCompact_yoneda_of_compact (T : BigFppfOver B S hS)
    (hT : CompactSpace ((BigFppfOver.toScheme B S hS).obj T)) :
    IsQuasiCompactSpace B S hS (yoneda.obj T) := by
  refine ⟨T, 𝟙 _, hT, ⟨Functor.relativelyRepresentable.of_isIso yoneda _, ?_⟩,
    fun _ _ hφ => hφ⟩
  intro A D g fst snd hpb
  have : IsIso (yoneda.map snd) := hpb.isIso_snd_of_isIso
  have : IsIso snd := Yoneda.fullyFaithful.isIso_of_isIso_map snd
  exact (inferInstance : Surjective ((BigFppfOver.toScheme B S hS).map snd))

/-- **Stacks 03HE.** A morphism of algebraic spaces over `S` is *quasi-compact* when every
base change of it along a morphism from a quasi-compact algebraic space has quasi-compact
source. -/
@[stacks 03HE]
abbrev IsQuasiCompact (f : F ⟶ G) : Prop :=
  ∀ (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u),
    IsAlgebraicSpace B S hS Z →
    IsQuasiCompactSpace B S hS Z →
    ∀ (g : Z ⟶ G),
      IsQuasiCompactSpace B S hS (pullback g f)

/-! ### Separation properties of a morphism -/

/-- **Stacks 03HL, part (1).** A morphism of algebraic spaces over `S` is *separated* when
its relative diagonal is a closed immersion. -/
@[stacks 03HL "part (1): separated", ega "I 5.4.1"]
abbrev IsSeparated (f : F ⟶ G) : Prop :=
  IsClosedImmersion B S hS (pullback.diagonal f)

/-- **Stacks 03HL, part (2).** A morphism of algebraic spaces over `S` is *locally
separated* when its relative diagonal is an immersion. -/
@[stacks 03HL "part (2): locally separated"]
abbrev IsLocallySeparated (f : F ⟶ G) : Prop :=
  IsImmersion B S hS (pullback.diagonal f)

/-- **Stacks 03HL, part (3).** A morphism of algebraic spaces over `S` is
*quasi-separated* when its relative diagonal is quasi-compact. -/
@[stacks 03HL "part (3): quasi-separated", ega "IV 1.2.1", sga "4 VI 1.7" "quasi-separated"]
abbrev IsQuasiSeparated (f : F ⟶ G) : Prop :=
  IsQuasiCompact B S hS (pullback.diagonal f)

end AlgebraicGeometry.Space

/-! ### Morphisms of algebraic spaces

The algebraic-space condition is a property of a presheaf, not extra structure on its
morphisms, so the morphisms of algebraic spaces over a fixed base are exactly the natural
transformations of the underlying presheaves, with their usual identities and composition.
Mathlib's functor category supplies them, together with the notation `F ⟶ G`. -/

add_to_stacks 0260 CategoryTheory.NatTrans
add_to_sga "3 I 1.1" CategoryTheory.NatTrans
add_to_sga "3 I 2.1.1" "more general" CategoryTheory.NatTrans
add_to_sga "3 VIIB 2.3.2" "definition of Hom_k-Gr(G" CategoryTheory.NatTrans
add_to_sga "4 I 1.1.1" CategoryTheory.NatTrans
add_to_sga "4 I 4.3" CategoryTheory.NatTrans
add_to_ega "0 3.1.4" CategoryTheory.NatTrans
add_to_ega "0 3.2.3" "more general" CategoryTheory.NatTrans
add_to_ega "0 8.1.3" CategoryTheory.NatTrans
add_to_ega "0 8.2.1" CategoryTheory.NatTrans
add_to_stacks 0260 CategoryTheory.Functor.category
add_to_sga "4 I 1.1.1" CategoryTheory.Functor.category

end
