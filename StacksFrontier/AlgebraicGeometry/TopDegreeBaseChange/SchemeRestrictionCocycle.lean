module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.MapDescentTransport
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SchemeRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.LocalizationCocycle

/-!
# Restriction along an inclusion of opens: the scheme and ringed-space vocabularies

[Stacks, Tag 01E5] is proved over a `AlgebraicGeometry.RingedSpace`, and its compatibility with
a nested pair of opens `W ≤ V` — the cocycle identity — is
`Stacks.Cohomology.HigherDirectImage.rightDerivedPushforwardRestrictIso_ofLE` and
`Stacks.Cohomology.HigherDirectImage.higherDirectImageRestrictIsoSucc_ofLE`.  Both are stated in
the ringed-space vocabulary, where restriction along `W ≤ V` is
`Stacks.Cohomology.HigherDirectImage.moduleRestrictionOfLE`.  The consumers over schemes use
`AlgebraicGeometry.Scheme.Modules.restrictFunctor (X.homOfLE h)` and its transitivity
isomorphism `Stacks.AlgebraicGeometry.ModuleLimits.restrictLEIso`.  Nothing connected the two,
and `Stacks.AlgebraicGeometry.SchemeHigherDirectImage.restrictFunctor_eq_moduleRestriction` does
*not* transcribe: it compares two pushforwards along the *same* functor of opens, whereas here
the two functors of opens differ — `(X.homOfLE h).opensFunctor` is the image functor of
`(X.homOfLE h).base`, and `AlgebraicGeometry.Scheme.homOfLE_base` identifies that base map with
the inclusion of subspaces only propositionally.

This file supplies that identification, and with it the cocycle identity itself, in both
indexings.

## Main results

* `Stacks.AlgebraicGeometry.SchemeRestrictionCocycle.opensFunctor_homOfLE`: the image functor of
  `X.homOfLE h` on opens is the image functor of the inclusion of subspaces.
* `Stacks.AlgebraicGeometry.SchemeRestrictionCocycle.restrictFunctor_homOfLE_eq`: **link (1):
  the scheme-level restriction along `W ≤ V` is the ringed-space one.**
* `Stacks.AlgebraicGeometry.SchemeRestrictionCocycle.heq_restrictLEIso` and
  `...restrictLEIso_hom`: **link (2): the two transitivity isomorphisms agree**, as a
  heterogeneous equality and read on the forward map through the two functor equalities.
* `Stacks.AlgebraicGeometry.SchemeRestrictionCocycle.higherDirectImageRestrictIso_hom` and
  `...higherDirectImageRestrictIso_hom_app`: **link (3): the scheme-level comparison of
  [Stacks, Tag 01E5] is the ringed-space one**, conjugated by the two functor equalities it is
  transported along, as an equality of natural transformations and at a module.  With the
  transport explicit in the definition (see the implementation notes of
  `StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/SchemeRestriction.lean`) the first holds by
  `rfl`.
* `Stacks.AlgebraicGeometry.SchemeRestrictionCocycle.higherDirectImageRestrictIsoOfLE`: the
  **middle comparison across a nested pair of opens, in the scheme vocabulary** — the
  ringed-space `Stacks.Cohomology.HigherDirectImage.higherDirectImageRestrictIsoSuccOfLE`
  transported along the two functor equalities
  `higherDirectImageRestrictIsoOfLE_source` and
  `Stacks.AlgebraicGeometry.SchemeHigherDirectImage.higherDirectImageRestrictIso_source`, with
  `...higherDirectImageRestrictIsoOfLE_hom` reading its forward map.
* `Stacks.AlgebraicGeometry.SchemeRestrictionCocycle.restrictLEIso_hom_app_rightDerived`: the
  scheme-level transitivity isomorphism at a higher direct image, through the transports.
* `Stacks.AlgebraicGeometry.SchemeRestrictionCocycle.higherDirectImageRestrictIsoSucc_ofLE_app`:
  the ringed-space cocycle of [Stacks, Tag 01E5] read at a module, and
  `...higherDirectImageRestrictIso_succ`: in positive degree the ringed-space comparison is the
  one the cocycle is about.
* `Stacks.AlgebraicGeometry.SchemeRestrictionCocycle.higherDirectImageRestrictIso_ofLE`:
  **[Stacks, Tag 01E5], compatibility across a nested pair of opens, in the scheme
  vocabulary** — the comparison for `V` restricted along `W ≤ V` and followed by
  `Stacks.AlgebraicGeometry.ModuleLimits.restrictLEIso` is the middle comparison followed by the
  comparison for `W` — and `...higherDirectImageRestrictIso_ofLE_app`, its component at a
  module.
* `Stacks.AlgebraicGeometry.SchemeRestrictionCocycle.rightDerivedPlusRestrictIsoOfLE` and
  `...rightDerivedPlusRestrictObjIso_ofLE`: **the same cocycle for the `ℤ`-indexed comparison
  `Stacks.AlgebraicGeometry.SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso`**, which is
  the spelling the consumers use.
* `obj_eq_of_functor_eq`, `map_eq_of_eq`, `map_eq_of_functor_eq`, `app_eq_of_eq` and
  `comp_eq_comp_of_transport` in the same namespace: the transport toolkit — reading a morphism,
  a functor image and a natural-transformation component through equalities of the functors, and
  the composition law that turns four such readings plus an identity between the transported
  composites into the identity between the original ones.
* `Stacks.AlgebraicGeometry.SchemeRestrictionCocycle.restrictSheafOfRings_eq_ringCatSheaf`: the
  structure sheaf of an open subscheme is the restriction of the structure sheaf, by `rfl`.
* `transportIso` and `transportIso_hom`, `transportIso_hom_app`,
  `map_transportIso_hom_app`, `whiskerRight_transportIso_hom`, `whiskerLeft_transportIso_hom`,
  `eq_transportIso_of_heq`: the *single-spelling* transport toolkit, and
  `restrictLEIso_eq_transport`, `higherDirectImageRestrictIso_eq_transport`,
  `...._eq_transport_succ`, `higherDirectImageRestrictIsoOfLE_eq_transport`: each scheme-level
  comparison read as the `transportIso` of the ringed-space one.  These are what make the
  cocycle reachable; see the implementation notes.

## Implementation notes

The equality of the two restriction functors is an equality of two
`SheafOfModules.pushforward`s along two different functors of opens, so it is not available to
`congr` as a single congruence: the morphism of sheaves of rings each is taken along lives over
its own functor.  The proof peels the equality apart with `congr 1`, feeding
`opensFunctor_homOfLE` to the functor component, `proof_irrel_heq` to the continuity instance
(`CategoryTheory.Functor.IsContinuous` is a `Prop`) and `heq_natTrans` to the comparison
morphism of sheaves of rings.  On components that morphism is, on both sides, a restriction map
of the structure sheaf along a morphism of `TopologicalSpace.Opens X` — on the scheme side by
`AlgebraicGeometry.Scheme.Hom.appIso_homOfLE_inv` — and `heq_presheaf_map` identifies two such
restriction maps, the opens being a thin category.

The comparison of the two transitivity isomorphisms is the same argument one level up.  Their
types differ by `restrictLE_source_eq`, so the statement that they agree is a heterogeneous
equality, and `heq_iso`, `heq_natTrans` and `heq_modules_hom` take it down to sections, where
both are restriction maps of the module along an identification of opens — in two steps on the
scheme side (`AlgebraicGeometry.Scheme.Modules.restrictFunctorComp` followed by
`AlgebraicGeometry.Scheme.Modules.restrictFunctorCongr`) and in one on the ringed-space side —
so `heq_presheaf_map_comp` finishes.  `restrictLEIso_hom` is the resulting equation between the
forward maps, which is the form a rewrite consumes.

**Mixed-spelling composites, and why the cocycle needs the transport section.**  The ambient
category of modules has two spellings: `AlgebraicGeometry.Scheme.Modules` over
`X.ringCatSheaf`, and `SheafOfModules` over
`Stacks.Cohomology.HigherDirectImage.structureSheafRing X.toRingedSpace`.  They are
*definitionally equal, and cheaply so*: `structureSheafRing X.toRingedSpace = X.ringCatSheaf`
and `structureSheafRing (Stacks.Cohomology.HigherDirectImage.restrictToOpen X.toRingedSpace V) =
V.toScheme.ringCatSheaf` hold by `rfl`, and so does the equality of the two `Category`
instances — the two spellings do not need to be identified, they already are.

What does not work is a composite whose factors were elaborated in *different* spellings.
`eqToHom h ≫ β ≫ eqToHom h'` with `β` a ringed-space morphism is such a composite: `≫` takes
its `Category` instance from its first argument, so the inner one is elaborated against the
ringed-space instance and the outer one against the scheme instance.  Two things then fail.
`rw` and `simp` cannot see through it, because matching the inner `≫` against a lemma stated in
the other spelling means unfolding a `Category` instance at reducible transparency, which does
not happen: inside such a composite `rw [CategoryTheory.Functor.map_comp]` reports that it
cannot find the pattern `Functor.map _ (_ ≫ _)` in a goal that plainly displays one.  And any
further composite built on top of it is rejected by the kernel with `(kernel) deterministic
timeout`, because reconciling the two instances there happens underneath `Functor.map` or
`NatTrans.app` applied to right-derived-functor objects.

`higherDirectImageRestrictIso_hom`, `higherDirectImageRestrictIsoOfLE_hom`, `restrictLEIso_hom`
and the `..._app` readings derived from them are composites of exactly that mixed shape.  They
are true and they type-check, but nothing can be built on them: the two readings the cocycle
still needed — `(Scheme.Modules.restrictFunctor (Y.homOfLE h)).map` of the comparison for `V`,
and the middle comparison at a module — both time out in the kernel however they are arranged,
and so does any restatement of them whose right-hand side is mixed.

The transport section removes the mixing at the source.  `transportIso hA hB β` forms
`eqToIso hA ≪≫ β ≪≫ eqToIso hB` inside a declaration with one ambient category, so the
composite carries one `Category` instance throughout and `β` enters only as an argument — a
crossing the kernel checks in one step.  Each scheme-level comparison is then *equal*, by
`rfl`, to the `transportIso` of its ringed-space counterpart
(`higherDirectImageRestrictIso_eq_transport` and the two others), and its forward map,
components and whiskerings are read off by lemmas in which every `≫`, `eqToHom`,
`Functor.map` and `NatTrans.app` is at a single instance.  With the four readings in that form,
`comp_eq_comp_of_transport` delivers `higherDirectImageRestrictIso_ofLE` from the ringed-space
cocycle, and `NatTrans.congr_app` delivers the objectwise form.  The cocycle is stated at the
level of natural transformations rather than objectwise for the same reason: there the
identifications are the functor equalities themselves, with no `.obj F` to reconcile.

## References

* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.HigherDirectImage

universe u

namespace Stacks.AlgebraicGeometry.SchemeRestrictionCocycle

/-! ### Heterogeneous comparisons -/

/-- Two natural transformations whose sources are equal and whose targets are equal are
heterogeneously equal as soon as all their components are.  The transports of the type of a
natural transformation along the two equalities are what the comparison of a scheme-level and a
ringed-space-level construction has to cross. -/
theorem heq_natTrans {C A : Type*} [Category C] [Category A] {P P' Q Q' : C ⥤ A}
    (hP : P = P') (hQ : Q = Q') (α : P ⟶ Q) (β : P' ⟶ Q')
    (hc : ∀ U, HEq (α.app U) (β.app U)) : HEq α β := by
  subst hP
  subst hQ
  exact heq_of_eq (NatTrans.ext (funext fun U => eq_of_heq (hc U)))

/-- The restriction maps of a presheaf on a space along two morphisms of opens with equal
sources and equal targets are heterogeneously equal: the opens of a space form a thin category,
so once the two morphisms have the same type they are the same morphism. -/
theorem heq_presheaf_map {Z : TopCat.{u}} {A : Type*} [Category A] (P : (Opens Z)ᵒᵖ ⥤ A)
    {B B' C C' : Opens Z} (hB : B = B') (hC : C = C')
    (p : (op B : (Opens Z)ᵒᵖ) ⟶ op C) (q : (op B' : (Opens Z)ᵒᵖ) ⟶ op C') :
    HEq (P.map p) (P.map q) := by
  subst hB
  subst hC
  rw [Subsingleton.elim p q]

/-- A two-step restriction map of a presheaf on a space is heterogeneously equal to a one-step
one with equal source and equal target: the opens of a space form a thin category, so the
composite and the one-step map are the same morphism once they have the same type. -/
theorem heq_presheaf_map_comp {Z : TopCat.{u}} {A : Type*} [Category A] (P : (Opens Z)ᵒᵖ ⥤ A)
    {B B' C C' D : Opens Z} (hB : B = B') (hC : C = C')
    (p : (op B : (Opens Z)ᵒᵖ) ⟶ op D) (p' : (op D : (Opens Z)ᵒᵖ) ⟶ op C)
    (q : (op B' : (Opens Z)ᵒᵖ) ⟶ op C') :
    HEq (P.map p ≫ P.map p') (P.map q) := by
  subst hB
  subst hC
  rw [← P.map_comp, Subsingleton.elim (p ≫ p') q]

/-- The third spelling of the structure sheaf of an open subscheme, the one the restriction
functors produce: restricting the structure sheaf of `X` along the open embedding of `V` gives
the structure sheaf of `V`, by `rfl`.  This is what makes the target of
`Stacks.Cohomology.HigherDirectImage.moduleRestrictionOfLE` the same category as the source of
the scheme-level restriction along an inclusion of opens; the other two spellings are compared
in `StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/SchemeRestriction.lean`. -/
theorem restrictSheafOfRings_eq_ringCatSheaf (X : Scheme.{u}) (V : X.Opens) :
    Stacks.SheafOfModules.restrictSheafOfRings (TopologicalSpace.Opens.isOpenEmbedding V)
        (structureSheafRing X.toRingedSpace) = V.toScheme.ringCatSheaf :=
  rfl

/-! ### Transport of an isomorphism along equalities of its source and target

The two vocabularies generate the same categories, and the comparison isomorphisms of
[Stacks, Tag 01E5] are proved in the ringed-space one and consumed in the scheme one.  The
identification is an *equality* of functors, so the comparison is transported by `eqToIso`; the
only question is how the transported isomorphism is written down.  Writing
`eqToIso h ≪≫ β ≪≫ eqToIso h'` by hand is what must be avoided: `β` is a morphism of the
ringed-space category, so the inner `≪≫` is elaborated against *its* `Category` instance while
the outer one is elaborated against the scheme instance, and the resulting composite mixes the
two.  `transportIso` forms the same composite inside a declaration with a single ambient
category, so every `≫`, `eqToHom`, `Functor.map` and `NatTrans.app` in it and in the lemmas
below carries one instance.  See the implementation notes. -/

/-- An isomorphism transported along an equality of its source and an equality of its target.
This is `eqToIso hA ≪≫ β ≪≫ eqToIso hB`, formed in the single ambient category `C` so that the
composite does not mix the `Category` instance `β` was elaborated against with the one the
transported isomorphism is used at. -/
def transportIso {C : Type*} [Category C] {A A' B B' : C} (hA : A = A') (hB : B' = B)
    (β : A' ≅ B') : A ≅ B :=
  eqToIso hA ≪≫ β ≪≫ eqToIso hB

/-- The forward map of a transported isomorphism. -/
theorem transportIso_hom {C : Type*} [Category C] {A A' B B' : C} (hA : A = A') (hB : B' = B)
    (β : A' ≅ B') : (transportIso hA hB β).hom = eqToHom hA ≫ β.hom ≫ eqToHom hB := rfl

/-- An isomorphism heterogeneously equal to another one, whose source and target are equal to
the other's, *is* the other transported.  This is `iso_hom_eq_of_heq` read as an equality of
isomorphisms rather than of forward maps, which is the form the readings below consume. -/
theorem eq_transportIso_of_heq {C : Type*} [Category C] {A A' B B' : C} (hA : A = A')
    (hB : B' = B) {α : A ≅ B} {β : A' ≅ B'} (hαβ : HEq α β) : α = transportIso hA hB β := by
  subst hA
  subst hB
  cases eq_of_heq hαβ
  exact Iso.ext (by simp [transportIso])

/-- The component at an object of the forward map of a transported isomorphism of functors, with
the two object identifications supplied.  Taking them as arguments rather than computing them from
the equalities of the functors keeps the unifier from having to guess them from a goal in which
the source and target are spelled with a different association of `⋙`; that is the convention the
rest of this toolkit follows, in `map_transportIso_hom_app`, `whiskerRight_transportIso_hom` and
`whiskerLeft_transportIso_hom`.  The identifications are proof-irrelevant, so the statement is
the same one a variant computing them by `CategoryTheory.Functor.congr_obj` would make. -/
theorem transportIso_hom_app {C D : Type*} [Category C] [Category D] {P P' Q Q' : C ⥤ D}
    (hP : P = P') (hQ : Q' = Q) (β : P' ≅ Q') (M : C) (hA : P.obj M = P'.obj M)
    (hB : Q'.obj M = Q.obj M) :
    (transportIso hP hQ β).hom.app M = eqToHom hA ≫ β.hom.app M ≫ eqToHom hB := by
  subst hP
  subst hQ
  simp [transportIso]

/-- The image under a functor of the component of a transported isomorphism of functors, read
through an equality of the functor itself.  This is the reading that `map_eq_of_eq` cannot
deliver across the two spellings: there the image of the ringed-space morphism is written with
the ringed-space `Functor.map`, and reconciling it with the scheme-level one is the definitional
equality that does not terminate. -/
theorem map_transportIso_hom_app {C D E : Type*} [Category C] [Category D] [Category E]
    {P P' Q Q' : C ⥤ D} (hP : P = P') (hQ : Q' = Q) (β : P' ≅ Q') {G G' : D ⥤ E}
    (hG : G = G') (M : C) (hA : G.obj (P.obj M) = G'.obj (P'.obj M))
    (hB : G.obj (Q.obj M) = G'.obj (Q'.obj M)) :
    G.map ((transportIso hP hQ β).hom.app M) =
      eqToHom hA ≫ G'.map (β.hom.app M) ≫ eqToHom hB.symm := by
  subst hP
  subst hQ
  subst hG
  simp [transportIso]

/-- A transported isomorphism of functors whiskered on the right, read through an equality of
the functor it is whiskered by. -/
theorem whiskerRight_transportIso_hom {C D E : Type*} [Category C] [Category D] [Category E]
    {P P' Q Q' : C ⥤ D} (hP : P = P') (hQ : Q' = Q) (β : P' ≅ Q') {G G' : D ⥤ E}
    (hG : G = G') (hA : P ⋙ G = P' ⋙ G') (hB : Q' ⋙ G' = Q ⋙ G) :
    Functor.whiskerRight (transportIso hP hQ β).hom G =
      eqToHom hA ≫ Functor.whiskerRight β.hom G' ≫ eqToHom hB := by
  subst hP
  subst hQ
  subst hG
  simp [transportIso]

/-- A transported isomorphism of functors whiskered on the left, read through an equality of the
functor it is whiskered by. -/
theorem whiskerLeft_transportIso_hom {C D E : Type*} [Category C] [Category D] [Category E]
    {K K' : C ⥤ D} (hK : K = K') {P P' Q Q' : D ⥤ E} (hP : P = P') (hQ : Q' = Q) (β : P' ≅ Q')
    (hA : K ⋙ P = K' ⋙ P') (hB : K' ⋙ Q' = K ⋙ Q) :
    Functor.whiskerLeft K (transportIso hP hQ β).hom =
      eqToHom hA ≫ Functor.whiskerLeft K' β.hom ≫ eqToHom hB := by
  subst hK
  subst hP
  subst hQ
  simp [transportIso]

/-! ### Restriction along an inclusion of opens -/

/-- The image functor on opens of the inclusion `X.homOfLE h : W ⟶ V` of open subschemes is the
image functor of the inclusion of the underlying open subspaces.  The two agree because
`AlgebraicGeometry.Scheme.homOfLE_base` identifies the two maps of spaces, and the opens of a
space form a thin category, so the action on morphisms carries no information. -/
theorem opensFunctor_homOfLE (X : Scheme.{u}) {W V : X.Opens} (h : W ≤ V) :
    (X.homOfLE h).opensFunctor = (Stacks.SheafOfModules.isOpenEmbedding_inclusionOfLE h).functor :=
  CategoryTheory.Functor.ext (fun U => by
      apply TopologicalSpace.Opens.ext
      change (X.homOfLE h).base.hom '' U.carrier = _
      rw [Scheme.homOfLE_base]
      rfl)
    (fun _ _ _ => Subsingleton.elim _ _)

/-- The image in `X` of an open of `W` under `X.homOfLE h` and then `V.ι` is its image under the
inclusion of subspaces. -/
private theorem image_homOfLE_eq (X : Scheme.{u}) {W V : X.Opens} (h : W ≤ V)
    (U : W.toScheme.Opens) :
    V.ι ''ᵁ (X.homOfLE h ''ᵁ U) =
      (TopologicalSpace.Opens.isOpenEmbedding V).functor.obj
        ((Stacks.SheafOfModules.isOpenEmbedding_inclusionOfLE h).functor.obj U) := by
  rw [opensFunctor_homOfLE X h]
  rfl

/-- **Link (1): restricting sheaves of modules along `W ≤ V` means the same thing over a scheme
and over its ringed space.**  The scheme-level restriction functor
`AlgebraicGeometry.Scheme.Modules.restrictFunctor (X.homOfLE h)` is the ringed-space
`Stacks.Cohomology.HigherDirectImage.moduleRestrictionOfLE`.

This is what
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.restrictFunctor_eq_moduleRestriction` does for
restriction to a single open, but it is not the same argument: there the two pushforwards are
taken along the same functor of opens and the comparison morphism of sheaves of rings is the
identity, while here the two functors of opens are different presentations of the inclusion of
subspaces and both comparison morphisms are nontrivial restriction maps. -/
theorem restrictFunctor_homOfLE_eq (X : Scheme.{u}) {W V : X.Opens} (h : W ≤ V) :
    Scheme.Modules.restrictFunctor (X.homOfLE h) = moduleRestrictionOfLE X.toRingedSpace h := by
  unfold Scheme.Modules.restrictFunctor moduleRestrictionOfLE
    Stacks.SheafOfModules.restrictSheafOfModulesOfLE
  congr 1
  · exact opensFunctor_homOfLE X h
  · exact proof_irrel_heq _ _
  · congr 1
    · congr 1
      congr 1
      exact opensFunctor_homOfLE X h
    · refine heq_natTrans rfl
        (congrArg (fun T : W.toScheme.Opens ⥤ V.toScheme.Opens => T.op ⋙
          (Stacks.SheafOfModules.restrictSheafOfRings (TopologicalSpace.Opens.isOpenEmbedding V)
            (structureSheafRing X.toRingedSpace)).obj) (opensFunctor_homOfLE X h)) _ _ (fun U => ?_)
      dsimp only [Functor.whiskerRight_app, NatTrans.op_app]
      rw [Scheme.Hom.appIso_homOfLE_inv]
      exact heq_presheaf_map (X.presheaf ⋙ forget₂ CommRingCat RingCat) rfl
        (image_homOfLE_eq X h U.unop) _ _

/-! ### The two transitivity isomorphisms -/

/-- An isomorphism whose source and target are equal to those of another one, and which is
heterogeneously equal to it, has for forward map the other's conjugated by the two
`CategoryTheory.eqToHom`s. -/
theorem iso_hom_eq_of_heq {C : Type*} [Category C] {A A' B B' : C} (hA : A = A') (hB : B = B')
    {α : A ≅ B} {β : A' ≅ B'} (hαβ : HEq α β) :
    α.hom = eqToHom hA ≫ β.hom ≫ eqToHom hB.symm := by
  subst hA
  subst hB
  cases eq_of_heq hαβ
  simp

/-- Two isomorphisms whose sources are equal and whose targets are equal are heterogeneously
equal as soon as their forward maps are. -/
theorem heq_iso {C : Type*} [Category C] {A A' B B' : C} (hA : A = A') (hB : B = B')
    (α : A ≅ B) (β : A' ≅ B') (hh : HEq α.hom β.hom) : HEq α β := by
  subst hA
  subst hB
  exact heq_of_eq (Iso.ext (eq_of_heq hh))

/-- Two morphisms of sheaves of modules on a scheme between equal sources and equal targets are
heterogeneously equal as soon as they agree on sections over every open. -/
theorem heq_modules_hom {Z : Scheme.{u}} {M N M' N' : Z.Modules}
    (hM : M = M') (hN : N = N') (α : M ⟶ N) (β : M' ⟶ N')
    (hc : ∀ O, HEq (α.app O) (β.app O)) : HEq α β := by
  subst hM
  subst hN
  exact heq_of_eq (Scheme.Modules.hom_ext _ _ (fun O => eq_of_heq (hc O)))

/-- The source of `Stacks.AlgebraicGeometry.ModuleLimits.restrictLEIso` in the ringed-space
vocabulary: restricting to `V` and then along `W ≤ V` is the ringed-space two-step
restriction. -/
theorem restrictLE_source_eq (X : Scheme.{u}) {W V : X.Opens} (h : W ≤ V) :
    Scheme.Modules.restrictFunctor V.ι ⋙ Scheme.Modules.restrictFunctor (X.homOfLE h) =
      moduleRestriction X.toRingedSpace V ⋙ moduleRestrictionOfLE X.toRingedSpace h := by
  rw [SchemeHigherDirectImage.restrictFunctor_eq_moduleRestriction X V,
    restrictFunctor_homOfLE_eq X h]
  rfl

/-- On sections over an open of `W`, the scheme-level and ringed-space-level transitivity
isomorphisms for `W ≤ V` are the same restriction map of the module.  Both are, on sections, the
restriction map along the identification of the image of that open in `X` computed in two steps
or in one — on the scheme side by Mathlib's `restrictFunctorComp` and `restrictFunctorCongr`,
on the ringed-space side by `Stacks.SheafOfModules.functorCompIsoOfLE`. -/
theorem heq_restrictLEIso_hom_app_app (X : Scheme.{u}) {W V : X.Opens} (h : W ≤ V)
    (M : X.Modules) (O : W.toScheme.Opens) :
    HEq (Scheme.Modules.Hom.app
        ((Stacks.AlgebraicGeometry.ModuleLimits.restrictLEIso h).hom.app M) O)
      (Scheme.Modules.Hom.app ((moduleRestrictionOfLEIso X.toRingedSpace h).hom.app M) O) := by
  have hR : Scheme.Modules.Hom.app ((moduleRestrictionOfLEIso X.toRingedSpace h).hom.app M) O
      = M.presheaf.map ((Stacks.SheafOfModules.functorCompIsoOfLE h).inv.app O).op := rfl
  rw [hR]
  simp only [Stacks.AlgebraicGeometry.ModuleLimits.restrictLEIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.restrictFunctorComp_inv_app_app,
    Scheme.Modules.restrictFunctorCongr_hom_app_app]
  exact heq_presheaf_map_comp M.presheaf (image_homOfLE_eq X h O) rfl _ _ _

/-- **Link (2): the two transitivity isomorphisms for `W ≤ V` agree.**  Mathlib's
`Stacks.AlgebraicGeometry.ModuleLimits.restrictLEIso` and the ringed-space
`Stacks.Cohomology.HigherDirectImage.moduleRestrictionOfLEIso` are the same isomorphism, up to
the transport of its type along `restrictLE_source_eq` and
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.restrictFunctor_eq_moduleRestriction`. -/
theorem heq_restrictLEIso (X : Scheme.{u}) {W V : X.Opens} (h : W ≤ V) :
    HEq (Stacks.AlgebraicGeometry.ModuleLimits.restrictLEIso h)
      (moduleRestrictionOfLEIso X.toRingedSpace h) := by
  refine heq_iso (restrictLE_source_eq X h)
    (SchemeHigherDirectImage.restrictFunctor_eq_moduleRestriction X W) _ _ ?_
  refine heq_natTrans (restrictLE_source_eq X h)
    (SchemeHigherDirectImage.restrictFunctor_eq_moduleRestriction X W) _ _ (fun M => ?_)
  exact heq_modules_hom
    (congrArg (fun T : X.Modules ⥤ W.toScheme.Modules => T.obj M) (restrictLE_source_eq X h))
    (congrArg (fun T : X.Modules ⥤ W.toScheme.Modules => T.obj M)
      (SchemeHigherDirectImage.restrictFunctor_eq_moduleRestriction X W)) _ _
    (fun O => heq_restrictLEIso_hom_app_app X h M O)

/-- **Link (2), read on the forward map.**  The scheme-level transitivity isomorphism for
`W ≤ V` is the ringed-space one, conjugated by the two functor equalities. -/
theorem restrictLEIso_hom (X : Scheme.{u}) {W V : X.Opens} (h : W ≤ V) :
    (Stacks.AlgebraicGeometry.ModuleLimits.restrictLEIso h).hom =
      eqToHom (restrictLE_source_eq X h) ≫
        (moduleRestrictionOfLEIso X.toRingedSpace h).hom ≫
        eqToHom (SchemeHigherDirectImage.restrictFunctor_eq_moduleRestriction X W).symm :=
  iso_hom_eq_of_heq (restrictLE_source_eq X h)
    (SchemeHigherDirectImage.restrictFunctor_eq_moduleRestriction X W) (heq_restrictLEIso X h)

/-- **Link (2), as a transport.**  The scheme-level transitivity isomorphism for `W ≤ V` *is*
the `transportIso` of the ringed-space one.  This is `restrictLEIso_hom` with the composite
formed in a single ambient category, which is what makes it usable: the forward map, its
components and its whiskerings can then be read off by the lemmas of the transport section
without any definitional equality between the two `Category` instances being demanded of a
morphism built over the right-derived-functor machinery. -/
theorem restrictLEIso_eq_transport (X : Scheme.{u}) {W V : X.Opens} (h : W ≤ V) :
    Stacks.AlgebraicGeometry.ModuleLimits.restrictLEIso h =
      transportIso (restrictLE_source_eq X h)
        (SchemeHigherDirectImage.restrictFunctor_eq_moduleRestriction X W).symm
        (moduleRestrictionOfLEIso X.toRingedSpace h) :=
  eq_transportIso_of_heq _ _ (heq_restrictLEIso X h)

/-! ### The nested-opens cocycle -/

attribute [local instance] HasDerivedCategory.standard

/-- The object equality induced by an equality of functors. -/
theorem obj_eq_of_functor_eq {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (hFG : F = G) (M : C) : F.obj M = G.obj M :=
  congrArg (fun T : C ⥤ D => T.obj M) hFG

/-- The image under a functor of a morphism, read through an equality of the functor and
equalities of the source and target objects. -/
theorem map_eq_of_eq {C D : Type*} [Category C] [Category D] {F G : C ⥤ D} (hFG : F = G)
    {M N M' N' : C} (hM : M = M') (hN : N = N') {u : M ⟶ N} {u' : M' ⟶ N'}
    (hu : u = eqToHom hM ≫ u' ≫ eqToHom hN.symm)
    (hA : F.obj M = G.obj M') (hB : F.obj N = G.obj N') :
    F.map u = eqToHom hA ≫ G.map u' ≫ eqToHom hB.symm := by
  subst hFG
  subst hM
  subst hN
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hu
  subst hu
  simp

/-- The image of a morphism under a functor, read through an equality of the functor. -/
theorem map_eq_of_functor_eq {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (hFG : F = G) {M N : C} (u : M ⟶ N) :
    F.map u = eqToHom (obj_eq_of_functor_eq hFG M) ≫ G.map u ≫
      eqToHom (obj_eq_of_functor_eq hFG N).symm := by
  subst hFG
  simp

/-- The component of a natural transformation, read through equalities of its source and target
functors. -/
theorem app_eq_of_eq {C D : Type*} [Category C] [Category D] {P Q P' Q' : C ⥤ D}
    (hP : P = P') (hQ : Q = Q') {α : P ⟶ Q} {β : P' ⟶ Q'}
    (hαβ : α = eqToHom hP ≫ β ≫ eqToHom hQ.symm) (M : C)
    (hA : P.obj M = P'.obj M) (hB : Q.obj M = Q'.obj M) :
    α.app M = eqToHom hA ≫ β.app M ≫ eqToHom hB.symm := by
  subst hP
  subst hQ
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hαβ
  subst hαβ
  simp

/-- A composable pair of morphisms whose composite is being compared with another one, with all
four objects and all four morphisms transported along equalities: the identity between the
composites follows from the identity between the transported composites.  This is the shape in
which the ringed-space cocycle of [Stacks, Tag 01E5] is read in the scheme vocabulary. -/
theorem comp_eq_comp_of_transport {C : Type*} [Category C] {A B B₂ D A₀ B₀ C₀ D₀ : C}
    (hA : A = A₀) (hB : B = B₀) (hB₂ : B₂ = C₀) (hD : D = D₀)
    {u₁ : A ⟶ B} {u₂ : B ⟶ D} {w₁ : A ⟶ B₂} {w₂ : B₂ ⟶ D}
    {v₁ : A₀ ⟶ B₀} {v₂ : B₀ ⟶ D₀} {z₁ : A₀ ⟶ C₀} {z₂ : C₀ ⟶ D₀}
    (h1 : u₁ = eqToHom hA ≫ v₁ ≫ eqToHom hB.symm)
    (h2 : u₂ = eqToHom hB ≫ v₂ ≫ eqToHom hD.symm)
    (h3 : w₁ = eqToHom hA ≫ z₁ ≫ eqToHom hB₂.symm)
    (h4 : w₂ = eqToHom hB₂ ≫ z₂ ≫ eqToHom hD.symm)
    (hR : v₁ ≫ v₂ = z₁ ≫ z₂) :
    u₁ ≫ u₂ = w₁ ≫ w₂ := by
  subst hA
  subst hB
  subst hB₂
  subst hD
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h1 h2 h3 h4
  rw [h1, h2, h3, h4, hR]

/-- The forward map of the scheme-level comparison of [Stacks, Tag 01E5] is the ringed-space
one, conjugated by the two functor equalities it is transported along.  This is link (3): the
`hom` of `SchemeHigherDirectImage.higherDirectImageRestrictIso_eq_eqToIso_trans`. -/
theorem higherDirectImageRestrictIso_hom {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (p : ℕ) :
    (SchemeHigherDirectImage.higherDirectImageRestrictIso f V p).hom =
      eqToHom (SchemeHigherDirectImage.higherDirectImageRestrictIso_source f V p) ≫
        (Stacks.Cohomology.HigherDirectImage.higherDirectImageRestrictIso
          f.toLRSHom.toShHom V p).hom ≫
        eqToHom (SchemeHigherDirectImage.higherDirectImageRestrictIso_target f V p).symm :=
  congrArg Iso.hom
    (SchemeHigherDirectImage.higherDirectImageRestrictIso_eq_eqToIso_trans f V p)

section Cocycle

open SchemeHigherDirectImage (higherDirectImageRestrictIso_source
  higherDirectImageRestrictIso_target restrictFunctor_eq_moduleRestriction)

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The comparison for `V` at a module is the ringed-space one, conjugated by the two functor
equalities it is transported along. -/
theorem higherDirectImageRestrictIso_hom_app (V : Y.Opens) (p : ℕ) (F : X.Modules) :
    (SchemeHigherDirectImage.higherDirectImageRestrictIso f V p).hom.app F =
      eqToHom (obj_eq_of_functor_eq (higherDirectImageRestrictIso_source f V p) F) ≫
        (Stacks.Cohomology.HigherDirectImage.higherDirectImageRestrictIso
          f.toLRSHom.toShHom V p).hom.app F ≫
        eqToHom (obj_eq_of_functor_eq (higherDirectImageRestrictIso_target f V p) F).symm :=
  app_eq_of_eq (higherDirectImageRestrictIso_source f V p)
    (higherDirectImageRestrictIso_target f V p) (higherDirectImageRestrictIso_hom f V p) F
    (obj_eq_of_functor_eq (higherDirectImageRestrictIso_source f V p) F)
    (obj_eq_of_functor_eq (higherDirectImageRestrictIso_target f V p) F)

variable {W V : Y.Opens} (h : W ≤ V) (p : ℕ)

/-- The source functor of the middle comparison across `W ≤ V`, in the ringed-space
vocabulary. -/
theorem higherDirectImageRestrictIsoOfLE_source :
    (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι ⋙
          (Scheme.Modules.pushforward (f ∣_ V)).rightDerived p) ⋙
        Scheme.Modules.restrictFunctor (Y.homOfLE h) =
      moduleRestriction X.toRingedSpace (preimageOpen f.toLRSHom.toShHom V) ⋙
        (modulePushforward (restrictedMorphism f.toLRSHom.toShHom V)).rightDerived p ⋙
        moduleRestrictionOfLE Y.toRingedSpace h := by
  rw [higherDirectImageRestrictIso_source f V p, restrictFunctor_homOfLE_eq Y h]
  rfl

/-- The target of the comparison for `V`, restricted along `W ≤ V`, in the ringed-space
vocabulary. -/
theorem higherDirectImageRestrictIso_target_ofLE :
    ((Scheme.Modules.pushforward f).rightDerived p ⋙ Scheme.Modules.restrictFunctor V.ι) ⋙
        Scheme.Modules.restrictFunctor (Y.homOfLE h) =
      ((modulePushforward f.toLRSHom.toShHom).rightDerived p ⋙
          moduleRestriction Y.toRingedSpace V) ⋙ moduleRestrictionOfLE Y.toRingedSpace h := by
  rw [higherDirectImageRestrictIso_target f V p, restrictFunctor_homOfLE_eq Y h]
  rfl

/-- **The middle comparison across a nested pair of opens, for schemes.**  Restricting the
comparison for `V` along `W ≤ V` lands on the source of the comparison for `W`.  It is the
ringed-space `Stacks.Cohomology.HigherDirectImage.higherDirectImageRestrictIsoSuccOfLE`
transported along `higherDirectImageRestrictIsoOfLE_source` and
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.higherDirectImageRestrictIso_source`. -/
noncomputable def higherDirectImageRestrictIsoOfLE :
    (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι ⋙
          (Scheme.Modules.pushforward (f ∣_ V)).rightDerived p) ⋙
        Scheme.Modules.restrictFunctor (Y.homOfLE h) ≅
      Scheme.Modules.restrictFunctor (f ⁻¹ᵁ W).ι ⋙
        (Scheme.Modules.pushforward (f ∣_ W)).rightDerived p :=
  eqToIso (higherDirectImageRestrictIsoOfLE_source f h p) ≪≫
    higherDirectImageRestrictIsoSuccOfLE f.toLRSHom.toShHom h p ≪≫
    eqToIso (higherDirectImageRestrictIso_source f W p).symm

/-- The forward map of the scheme-level middle comparison is the ringed-space one, conjugated by
the two functor equalities it is transported along. -/
theorem higherDirectImageRestrictIsoOfLE_hom :
    (higherDirectImageRestrictIsoOfLE f h p).hom =
      eqToHom (higherDirectImageRestrictIsoOfLE_source f h p) ≫
        (higherDirectImageRestrictIsoSuccOfLE f.toLRSHom.toShHom h p).hom ≫
        eqToHom (higherDirectImageRestrictIso_source f W p).symm :=
  rfl

/-- The scheme-level transitivity isomorphism at the higher direct image, through the
transports. -/
theorem restrictLEIso_hom_app_rightDerived (F : X.Modules) :
    (Stacks.AlgebraicGeometry.ModuleLimits.restrictLEIso h).hom.app
        (((Scheme.Modules.pushforward f).rightDerived p).obj F) =
      eqToHom (obj_eq_of_functor_eq (higherDirectImageRestrictIso_target_ofLE f h p) F) ≫
        (moduleRestrictionOfLEIso Y.toRingedSpace h).hom.app
          (((modulePushforward f.toLRSHom.toShHom).rightDerived p).obj F) ≫
        eqToHom (obj_eq_of_functor_eq (higherDirectImageRestrictIso_target f W p) F).symm :=
  app_eq_of_eq (restrictLE_source_eq Y h) (restrictFunctor_eq_moduleRestriction Y W)
    (restrictLEIso_hom Y h) (((Scheme.Modules.pushforward f).rightDerived p).obj F)
    (obj_eq_of_functor_eq (higherDirectImageRestrictIso_target_ofLE f h p) F)
    (obj_eq_of_functor_eq (higherDirectImageRestrictIso_target f W p) F)

/-- The ringed-space cocycle of [Stacks, Tag 01E5], read at a module. -/
theorem higherDirectImageRestrictIsoSucc_ofLE_app (F : X.Modules) :
    (moduleRestrictionOfLE Y.toRingedSpace h).map
          ((higherDirectImageRestrictIsoSucc f.toLRSHom.toShHom V p).hom.app F) ≫
        (moduleRestrictionOfLEIso Y.toRingedSpace h).hom.app
          (((modulePushforward f.toLRSHom.toShHom).rightDerived p).obj F) =
      (higherDirectImageRestrictIsoSuccOfLE f.toLRSHom.toShHom h p).hom.app F ≫
        (higherDirectImageRestrictIsoSucc f.toLRSHom.toShHom W p).hom.app F :=
  congrArg (fun t => NatTrans.app t F)
    (higherDirectImageRestrictIsoSucc_ofLE f.toLRSHom.toShHom h p)

/-- In positive degree the ringed-space comparison of [Stacks, Tag 01E5] is the one built from
the composite right derived functors. -/
theorem higherDirectImageRestrictIso_succ (V' : Opens Y.toRingedSpace) (q : ℕ) :
    Stacks.Cohomology.HigherDirectImage.higherDirectImageRestrictIso
        f.toLRSHom.toShHom V' (q + 1) =
      higherDirectImageRestrictIsoSucc f.toLRSHom.toShHom V' (q + 1) :=
  rfl

/-- **Link (3), as a transport.**  The scheme-level comparison of [Stacks, Tag 01E5] *is* the
`transportIso` of the ringed-space one.  Same statement as `higherDirectImageRestrictIso_hom`,
with the composite formed in a single ambient category. -/
theorem higherDirectImageRestrictIso_eq_transport (V : Y.Opens) (p : ℕ) :
    SchemeHigherDirectImage.higherDirectImageRestrictIso f V p =
      transportIso (higherDirectImageRestrictIso_source f V p)
        (higherDirectImageRestrictIso_target f V p).symm
        (Stacks.Cohomology.HigherDirectImage.higherDirectImageRestrictIso
          f.toLRSHom.toShHom V p) :=
  SchemeHigherDirectImage.higherDirectImageRestrictIso_eq_eqToIso_trans f V p

/-- `higherDirectImageRestrictIso_eq_transport` in positive degree, with the ringed-space
comparison already read as `higherDirectImageRestrictIsoSucc` — the spelling in which the
ringed-space cocycle `higherDirectImageRestrictIsoSucc_ofLE` states it. -/
theorem higherDirectImageRestrictIso_eq_transport_succ (V : Y.Opens) (q : ℕ) :
    SchemeHigherDirectImage.higherDirectImageRestrictIso f V (q + 1) =
      transportIso (higherDirectImageRestrictIso_source f V (q + 1))
        (higherDirectImageRestrictIso_target f V (q + 1)).symm
        (higherDirectImageRestrictIsoSucc f.toLRSHom.toShHom V (q + 1)) :=
  higherDirectImageRestrictIso_eq_transport f V (q + 1)

/-- The scheme-level middle comparison across `W ≤ V` *is* the `transportIso` of the
ringed-space one.  Same statement as `higherDirectImageRestrictIsoOfLE_hom`, with the composite
formed in a single ambient category. -/
theorem higherDirectImageRestrictIsoOfLE_eq_transport :
    higherDirectImageRestrictIsoOfLE f h p =
      transportIso (higherDirectImageRestrictIsoOfLE_source f h p)
        (higherDirectImageRestrictIso_source f W p).symm
        (higherDirectImageRestrictIsoSuccOfLE f.toLRSHom.toShHom h p) :=
  rfl

/-- **[Stacks, Tag 01E5], compatibility across a nested pair of opens, for schemes.**  The
comparison attached to `V`, restricted along `W ≤ V` and followed by the transitivity
isomorphism `Stacks.AlgebraicGeometry.ModuleLimits.restrictLEIso`, agrees with the middle
comparison `higherDirectImageRestrictIsoOfLE` followed by the comparison attached to `W`.

This is the ringed-space cocycle
`Stacks.Cohomology.HigherDirectImage.higherDirectImageRestrictIsoSucc_ofLE` read in the scheme
vocabulary.  All four morphisms are transports of ringed-space ones — by
`higherDirectImageRestrictIso_eq_transport_succ`, `restrictLEIso_eq_transport` and
`higherDirectImageRestrictIsoOfLE_eq_transport` — so the four readings the composition law
`comp_eq_comp_of_transport` consumes are the transport section's whiskering and forward-map
lemmas, and the identity between the transported composites is the ringed-space cocycle
itself. -/
theorem higherDirectImageRestrictIso_ofLE :
    Functor.whiskerRight
          (SchemeHigherDirectImage.higherDirectImageRestrictIso f V p).hom
          (Scheme.Modules.restrictFunctor (Y.homOfLE h)) ≫
        Functor.whiskerLeft ((Scheme.Modules.pushforward f).rightDerived p)
          (Stacks.AlgebraicGeometry.ModuleLimits.restrictLEIso h).hom =
      (higherDirectImageRestrictIsoOfLE f h p).hom ≫
        (SchemeHigherDirectImage.higherDirectImageRestrictIso f W p).hom := by
  have eA := higherDirectImageRestrictIsoOfLE_source f h p
  have eB := higherDirectImageRestrictIso_target_ofLE f h p
  have eC := higherDirectImageRestrictIso_source f W p
  have eD := higherDirectImageRestrictIso_target f W p
  rw [higherDirectImageRestrictIso_eq_transport f V p,
    higherDirectImageRestrictIso_eq_transport f W p,
    higherDirectImageRestrictIsoOfLE_eq_transport f h p,
    restrictLEIso_eq_transport Y h]
  exact comp_eq_comp_of_transport eA eB eC eD
    (whiskerRight_transportIso_hom _ _ _ (restrictFunctor_homOfLE_eq Y h) eA eB.symm)
    (whiskerLeft_transportIso_hom rfl _ _ _ eB eD.symm)
    (transportIso_hom _ _ _)
    (transportIso_hom _ _ _)
    (Stacks.Cohomology.HigherDirectImage.higherDirectImageRestrictIso_ofLE
      f.toLRSHom.toShHom h p)

/-- **The nested-opens cocycle at a module**, which is the spelling in which the consumers of
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso` meet it: the
component at `F` of `higherDirectImageRestrictIso_ofLE`. -/
theorem higherDirectImageRestrictIso_ofLE_app (F : X.Modules) :
    (Scheme.Modules.restrictFunctor (Y.homOfLE h)).map
          ((SchemeHigherDirectImage.higherDirectImageRestrictIso f V p).hom.app F) ≫
        (Stacks.AlgebraicGeometry.ModuleLimits.restrictLEIso h).hom.app
          (((Scheme.Modules.pushforward f).rightDerived p).obj F) =
      (higherDirectImageRestrictIsoOfLE f h p).hom.app F ≫
        (SchemeHigherDirectImage.higherDirectImageRestrictIso f W p).hom.app F := by
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    using NatTrans.congr_app (higherDirectImageRestrictIso_ofLE f h p) F

/-- **The middle comparison across a nested pair of opens, for the `ℤ`-indexed derived
functors.**  `higherDirectImageRestrictIsoOfLE` conjugated by
`Stacks.DerivedIndexing.rightDerivedIso` on either side, which is how
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.rightDerivedPlusRestrictIso` is built from
`...higherDirectImageRestrictIso`. -/
noncomputable def rightDerivedPlusRestrictIsoOfLE :
    (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι ⋙
          (Scheme.Modules.pushforward (f ∣_ V)).rightDerivedPlus (p : ℤ)) ⋙
        Scheme.Modules.restrictFunctor (Y.homOfLE h) ≅
      Scheme.Modules.restrictFunctor (f ⁻¹ᵁ W).ι ⋙
        (Scheme.Modules.pushforward (f ∣_ W)).rightDerivedPlus (p : ℤ) :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι)
        (Stacks.DerivedIndexing.rightDerivedIso
          (Scheme.Modules.pushforward (f ∣_ V)) p).symm)
      (Scheme.Modules.restrictFunctor (Y.homOfLE h)) ≪≫
    higherDirectImageRestrictIsoOfLE f h p ≪≫
    Functor.isoWhiskerLeft (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ W).ι)
      (Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward (f ∣_ W)) p)

/-- **[Stacks, Tag 01E5], compatibility across a nested pair of opens, for the comparison the
consumers use.**  The objectwise `ℤ`-indexed comparison
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso` attached to
`V`, restricted along `W ≤ V` and followed by the transitivity isomorphism, agrees with
`rightDerivedPlusRestrictIsoOfLE` followed by the comparison attached to `W`.

Both comparisons are the `ℕ`-indexed ones conjugated by
`Stacks.DerivedIndexing.rightDerivedIso`, so the two inner conjugations cancel and the
naturality of the transitivity isomorphism moves the outer one across the restriction; what
remains is `higherDirectImageRestrictIso_ofLE_app`.  No spelling is crossed here: everything is
in the scheme vocabulary. -/
theorem rightDerivedPlusRestrictObjIso_ofLE (F : X.Modules) :
    (Scheme.Modules.restrictFunctor (Y.homOfLE h)).map
          (SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso f V p F).hom ≫
        (Stacks.AlgebraicGeometry.ModuleLimits.restrictLEIso h).hom.app
          (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj F) =
      (rightDerivedPlusRestrictIsoOfLE f h p).hom.app F ≫
        (SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso f W p F).hom := by
  have key := higherDirectImageRestrictIso_ofLE_app f h p F
  have hnat := (Stacks.AlgebraicGeometry.ModuleLimits.restrictLEIso h).hom.naturality
    ((Stacks.DerivedIndexing.rightDerivedIso
      (Scheme.Modules.pushforward f) p).hom.app F)
  rw [SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso_eq_app,
    SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso_eq_app]
  dsimp only [SchemeHigherDirectImage.rightDerivedPlusRestrictIso, rightDerivedPlusRestrictIsoOfLE,
    Iso.app_hom, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.comp_map] at *
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hnat]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  simp only [SchemeHigherDirectImage.higherDirectImageRestrictIso_eq_eqToIso_trans] at key ⊢
  rw [reassoc_of% key]

end Cocycle

end Stacks.AlgebraicGeometry.SchemeRestrictionCocycle
