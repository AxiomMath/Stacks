module

public import StacksFrontier.Deformation.InfinitesimalAutomorphism.Basic.Object
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.Basic.Independence
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.Basic.Localization
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.Basic.DualNumbers

/-!
# Infinitesimal automorphisms

This file collects the parts `Object`, `Independence`, `Localization` and `DualNumbers`.

The infinitesimal automorphisms of an object of a predeformation
category, their independence of the chosen pushforward and of the chosen point, and their behaviour
under localization.

## Main definitions

* `pushforwardAutomorphismHom` is the canonical homomorphism between
  the fibre automorphism groups at the source and target of a morphism.
* `relativeInfinitesimalAutomorphisms` is its kernel.
* `canonicalRetraction` is the map back from a chosen pushforward.
* `IsCanonicalDualNumberPair` recognizes the constant inclusion and projection.
* `infinitesimalAutomorphisms` is its relative automorphism subgroup.
* `infinitesimalAutomorphismGroup`
  is the group of infinitesimal automorphisms at a chosen residue-field object.
* `ringEquivOfIso` is the ring isomorphism of carriers underlying an isomorphism of `𝒞_Λ`.
* `dualNumberRingHom` is the map of dual numbers induced by a map of coefficient rings.
* `dualNumberRingEquiv` is the isomorphism of dual numbers induced by an isomorphism of
  coefficient rings.
* `derivationDualNumberAlgHom` and `derivationDualNumberAlgEquiv` are the endomorphism and
  the automorphism `x + yε ↦ x + (D x + y)ε` of `P[ε]` attached to a derivation `D` of `P`.
* `derivationOfDualNumberAlgHom` is the derivation read off from an endomorphism of `P[ε]`
  that is the identity on constant parts.

## Main results

* `mem_relativeInfinitesimalAutomorphisms_iff` characterizes the
  kernel by the condition that an automorphism fixes the given morphism.
* `existsUnique_retraction` states existence and uniqueness of the map back.
* `mem_infinitesimalAutomorphisms_iff` characterizes membership by commuting
  with the map back.
* `existsUnique_pushforwardIso` gives the canonical comparison of
  pushforwards, including two choices for the same object.
* `existsUnique_infinitesimalAutomorphismsEquiv` gives the group
  isomorphism associated to a chosen isomorphism of original objects.
* `existsUnique_infinitesimalAutomorphismAction` gives the induced
  automorphism-group action.
* `subsingleton_aut_residueField` says that the
  automorphism group in the fibre over the residue field is trivial.
* `infinitesimalAutomorphisms_eq_top` identifies
  infinitesimal automorphisms with the whole automorphism group of the pushforward.
* `existsUnique_pointIso` gives the unique isomorphism
  between two points of the special fibre.
* `existsUnique_infinitesimalAutomorphismsEquiv`
  gives the canonical identification of their infinitesimal automorphism groups.
* `canonicalInfinitesimalAutomorphismsEquiv`
  is the resulting group isomorphism for use with chosen pushforwards.
* `infinitesimalAutomorphismGroup_objectsOverFunctor` identifies the two groups
  by forgetting the arrow to the fixed object.
* `dualNumberRingHom_fst` and `dualNumberRingHom_snd` compute the two coordinates of
  `dualNumberRingHom`.
* `maximalIdeal_eq_bot_of_isCanonicalDualNumberPair` says that the source of a canonical
  dual-number pair is a field object.
* `derivationDualNumberAlgHom_add` and `derivationDualNumberAlgHom_zero` say that addition of
  derivations corresponds to composition of the attached automorphisms.
* `derivationDualNumberAlgHom_derivationOfDualNumberAlgHom` says that an endomorphism of
  `P[ε]` fixing constant parts and `ε` comes from the derivation it defines.
* `artinianLocalAlgHom_bijective_of_isField` says that a morphism of `𝒞_Λ` between objects
  whose carriers are fields is bijective.

## Implementation notes

### Relative infinitesimal automorphisms

Automorphisms are taken in `Functor.Fiber`, so they lie over the identity of
the relevant base object. The induced automorphism of the target is obtained
from the strongly cocartesian universal property of the given morphism. This
construction is characterized by the equation
`a.hom ≫ f = f ≫ push(a).hom`, and the relative infinitesimal automorphism
group is literally `MonoidHom.ker` of the resulting homomorphism.

Although the Stacks Project uses the base category `C_Λ`, the construction
only uses its category structure, so it is stated for an arbitrary base
category.

### Infinitesimal automorphisms of an object

The generic retraction is constructed over any split pair. The tagged group and uniqueness
result require coordinates identifying the base arrows with the constant inclusion
`k → k[ε]` and the projection `k[ε] → k`. This allows any presentation of these objects
in `𝒞_Λ`, but not an arbitrary split pair. The group is a subgroup of the automorphisms
in the dual-number fibre, matching Tag 06JP.

### Independence of infinitesimal automorphisms from pushforward choices

The comparison of pushforwards is stated for any arrow in the base and any
isomorphism in its source fibre. The square with the pushforward arrows
characterizes it uniquely. The induced group equivalence is characterized by
conjugation through that comparison. The action is likewise characterized by
conjugation through the pushforward of each automorphism of the original
object. Thus the constructions depend only on the indicated isomorphism,
not on further choices.

### Automorphisms at a point of a predeformation category

The first part expresses triviality as a subsingleton automorphism group. The second
expresses equality with the entire automorphism group as equality of the subgroup from
Tag 06JQ with the top subgroup. A canonical dual-number pair specifies the maps
`k → k[ε] → k`, while the chosen lift specifies the pushforward object.

### Independence of the point for infinitesimal automorphisms

The infinitesimal automorphism groups of Tag 06JQ are formed using chosen pushforwards
to the dual numbers. The characterization of the identification quantifies over every
isomorphism of those pushforwards compatible with the unique isomorphism of points;
thus it records the independence of that choice as well as the induced conjugation.

### Infinitesimal automorphisms of a predeformation category

The choice of a pushforward to the dual numbers and of its underlying dual-number pair is
kept explicit, as in the definition of the pointwise group. The group is the carrier of the
pointwise subgroup of automorphisms; thus its group structure is inherited directly from
that subgroup. The canonical identification of the groups for two residue-field objects is
specified by conjugation along the unique compatible isomorphism of their pushforwards.

### Infinitesimal automorphisms of a localization

The groups are represented by automorphisms in different fibre categories, so
the source's equality is expressed as a group isomorphism. The point and its
dual-number pushforward in the slice are allowed to be any presentations
identified with the identity arrow and the canonical retraction. The formula
on automorphisms specifies the canonical isomorphism.

## References

* [Stacks Project, Tag 06JP](https://stacks.math.columbia.edu/tag/06JP)
* [Stacks Project, Tag 06JQ](https://stacks.math.columbia.edu/tag/06JQ)
* [Stacks Project, Tag 06JR](https://stacks.math.columbia.edu/tag/06JR)
* [Stacks Project, Tag 06JS](https://stacks.math.columbia.edu/tag/06JS)
-/
