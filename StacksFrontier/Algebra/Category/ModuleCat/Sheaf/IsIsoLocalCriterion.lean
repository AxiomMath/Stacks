module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EvaluationConservative
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.Topology.Sheaves.Modules.StalkRestrictOpen

/-!
# Being an isomorphism is local on the base for a morphism of sheaves of modules

Let `Y` be a topological space, `O` a sheaf of rings on `Y` and `g : M ⟶ N` a morphism of
sheaves of `O`-modules. This file proves that `g` is an isomorphism as soon as its restriction
to each member of an open cover of `Y` is one, and records the stalkwise criterion in the
`IsIso`-of-the-stalk-map spelling.

## Main results

* `AlgebraicGeometry.SheafOfModules.isIso_iff_isIso_stalkMap`: **isomorphy is stalkwise**, with
  the stalk condition spelled `IsIso (stalkMap O y g)` rather than bijectivity of the
  underlying function.
* `AlgebraicGeometry.SheafOfModules.bijective_stalkMap_of_isIso_restrict`: if the restriction of
  `g` along an open embedding `f : Z ⟶ Y` is an isomorphism then the stalk map of `g` at `f z`
  is bijective, for every `z : Z`.
* `AlgebraicGeometry.SheafOfModules.isIso_of_forall_exists_isIso_restrict`: **the pointwise
  local criterion.** If every point of `Y` has an open neighbourhood to which `g` restricts to
  an isomorphism, then `g` is an isomorphism.
* `AlgebraicGeometry.SheafOfModules.isIso_of_isIso_restrict_of_iSup_eq_top` and
  `AlgebraicGeometry.SheafOfModules.isIso_iff_isIso_restrict`: **the open-cover criterion**, in
  the one-directional and in the two-sided form. For a family of opens covering `Y`, `g` is an
  isomorphism exactly when each of its restrictions is.

## Implementation notes

**Nothing stalkwise is reproved.** The stalkwise criterion for isomorphy of a morphism of
sheaves of modules on a space is already on this branch, as
`AlgebraicGeometry.SheafOfModules.isIso_iff_bijective_stalkMap` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/StalkwiseExactness.lean`, together with the
monomorphy and epimorphy criteria it is assembled from; and the comparison of the stalk of a
restriction with the stalk of the sheaf is already there too, as
`Stacks.SheafOfModules.restrictStalkAddIso` and its naturality
`Stacks.SheafOfModules.restrictStalkAddIso_hom_stalkMap` of
`StacksFrontier/Topology/Sheaves/Modules/StalkRestrictOpen.lean`. What this file adds is the
passage from the local hypothesis to the stalk hypothesis: the restriction of `g` to an open
`Z` has, at `z`, the *same* stalk map as `g` at `f z` up to the two stalk identifications, so
bijectivity transfers, and a cover of `Y` by opens over which `g` restricts to an isomorphism
reaches every point.

**Why the comparison is used on abelian groups.** `restrictStalkAddIso` identifies the stalks
as abelian groups, and its module refinement `Stacks.SheafOfModules.stalkRestrictIso` is
semilinear over an isomorphism of the stalk *rings*, not linear. Bijectivity is a statement
about the underlying functions, so the abelian-group form is the one that transfers it with no
transport of scalars; the conclusion is then fed to `isIso_iff_bijective_stalkMap`, which also
asks only for bijectivity.

**Restriction along an open embedding, not along an open immersion of schemes.** The
restriction functor is `Stacks.SheafOfModules.restrictSheafOfModules`, restriction along an
open embedding of topological spaces, which is what the stalk comparison of
`StacksFrontier/Topology/Sheaves/Modules/StalkRestrictOpen.lean` is stated for and what applies
to a sheaf of modules over a bare sheaf of rings. The two
`isIso_of_isIso_restrict`-style statements already in the repository
(`AlgebraicGeometry.InvertibleLocal.isIso_of_isIso_restrict_openCover` for morphisms of
schemes, and the residue-field statements of the tagged lemmas) are about other categories
entirely.

**Universes.** A single universe `u` carries the space, the sheaf of rings and the modules, as
everywhere in the stalk API for sheaves of modules on a space: Mathlib's module structure on
the stalk of a presheaf of modules is stated only at that combination, so
`AlgebraicGeometry.SheafOfModules.stalkFunctor` exists at no other.

## References

* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Topology TopologicalSpace

universe u

namespace AlgebraicGeometry.SheafOfModules

variable {Y : TopCat.{u}}
  {O : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) RingCat.{u}}

/-! ### Isomorphy as a condition on the stalk maps -/

/-- **Isomorphy is stalkwise**, with the condition on each stalk spelled as isomorphy of the
stalk map rather than bijectivity of its underlying function. This is
`AlgebraicGeometry.SheafOfModules.isIso_iff_bijective_stalkMap` composed with
`CategoryTheory.ConcreteCategory.isIso_iff_bijective` on the category of modules over the stalk
ring. -/
theorem isIso_iff_isIso_stalkMap {M N : _root_.SheafOfModules.{u} O} (g : M ⟶ N) :
    IsIso g ↔ ∀ y : Y, IsIso (stalkMap O y g) :=
  (isIso_iff_bijective_stalkMap g).trans
    (forall_congr' fun y => (ConcreteCategory.isIso_iff_bijective (stalkMap O y g)).symm)

/-! ### Transferring bijectivity of a stalk map across restriction to an open -/

/-- **The stalk map of a morphism which restricts to an isomorphism is bijective.** If the
restriction of `g` along an open embedding `f : Z ⟶ Y` is an isomorphism, then for every `z : Z`
the stalk map of `g` at `f z` is bijective.

The stalk at `z` of the restriction is the stalk at `f z` of the sheaf
(`Stacks.SheafOfModules.restrictStalkAddIso`) and the identification is natural in the sheaf of
modules, so the stalk map of the restriction is the stalk map of `g` conjugated by two
bijections. -/
theorem bijective_stalkMap_of_isIso_restrict {Z : TopCat.{u}} {f : Z ⟶ Y}
    (hf : IsOpenEmbedding f) {M N : _root_.SheafOfModules.{u} O} (g : M ⟶ N) (z : Z)
    (hg : IsIso ((Stacks.SheafOfModules.restrictSheafOfModules hf O).map g)) :
    Function.Bijective (stalkMap O (f z) g).hom := by
  have := hg
  have hT : Function.Bijective
      ((stalkFunctor (Stacks.SheafOfModules.restrictSheafOfRings hf O) z).map
        ((Stacks.SheafOfModules.restrictSheafOfModules hf O).map g)) :=
    ConcreteCategory.bijective_of_isIso _
  have ha : Function.Bijective (Stacks.SheafOfModules.restrictStalkAddIso hf O z M).hom :=
    ConcreteCategory.bijective_of_isIso _
  have hb : Function.Bijective (Stacks.SheafOfModules.restrictStalkAddIso hf O z N).hom :=
    ConcreteCategory.bijective_of_isIso _
  have key : ∀ m, (Stacks.SheafOfModules.restrictStalkAddIso hf O z N).hom
      ((stalkFunctor (Stacks.SheafOfModules.restrictSheafOfRings hf O) z).map
        ((Stacks.SheafOfModules.restrictSheafOfModules hf O).map g) m) =
      (stalkMap O (f z) g).hom
        ((Stacks.SheafOfModules.restrictStalkAddIso hf O z M).hom m) :=
    Stacks.SheafOfModules.restrictStalkAddIso_hom_stalkMap hf O z g
  refine ⟨fun a b hab => ?_, fun n => ?_⟩
  · obtain ⟨m, rfl⟩ := ha.surjective a
    obtain ⟨m', rfl⟩ := ha.surjective b
    exact congrArg _ (hT.injective (hb.injective ((key m).trans (hab.trans (key m').symm))))
  · obtain ⟨w, rfl⟩ := hb.surjective n
    obtain ⟨m, rfl⟩ := hT.surjective w
    exact ⟨(Stacks.SheafOfModules.restrictStalkAddIso hf O z M).hom m, (key m).symm⟩

/-! ### The local criteria -/

/-- **A morphism of sheaves of modules which is locally an isomorphism is an isomorphism.** If
every point of `Y` has an open neighbourhood `U` such that the restriction of `g` to `U` is an
isomorphism, then `g` is an isomorphism.

Isomorphy is stalkwise (`isIso_iff_bijective_stalkMap`) and the stalk map at a point is
bijective as soon as `g` restricts to an isomorphism over one neighbourhood of it
(`bijective_stalkMap_of_isIso_restrict`). -/
theorem isIso_of_forall_exists_isIso_restrict {M N : _root_.SheafOfModules.{u} O} (g : M ⟶ N)
    (h : ∀ y : Y, ∃ U : Opens Y, ∃ _ : y ∈ U,
      IsIso ((Stacks.SheafOfModules.restrictSheafOfModules U.isOpenEmbedding O).map g)) :
    IsIso g := by
  rw [isIso_iff_bijective_stalkMap]
  intro y
  obtain ⟨U, hy, hiso⟩ := h y
  exact bijective_stalkMap_of_isIso_restrict U.isOpenEmbedding g ⟨y, hy⟩ hiso

/-- **Being an isomorphism is local on the base**: a morphism of sheaves of modules whose
restriction to each member of a family of opens covering the space is an isomorphism is an
isomorphism. -/
theorem isIso_of_isIso_restrict_of_iSup_eq_top {ι : Type*} (U : ι → Opens Y)
    (hU : ⨆ i, U i = ⊤) {M N : _root_.SheafOfModules.{u} O} (g : M ⟶ N)
    (h : ∀ i, IsIso ((Stacks.SheafOfModules.restrictSheafOfModules
      (U i).isOpenEmbedding O).map g)) :
    IsIso g := by
  refine isIso_of_forall_exists_isIso_restrict g fun y => ?_
  have hy : y ∈ (⨆ i, U i : Opens Y) := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hy
  exact ⟨U i, hi, h i⟩

/-- **Being an isomorphism is local on the base**, as an equivalence: for a family of opens
covering the space, a morphism of sheaves of modules is an isomorphism exactly when each of its
restrictions is. The forward direction is functoriality of restriction. -/
theorem isIso_iff_isIso_restrict {ι : Type*} (U : ι → Opens Y) (hU : ⨆ i, U i = ⊤)
    {M N : _root_.SheafOfModules.{u} O} (g : M ⟶ N) :
    IsIso g ↔ ∀ i, IsIso ((Stacks.SheafOfModules.restrictSheafOfModules
      (U i).isOpenEmbedding O).map g) :=
  ⟨fun hg i => by have := hg; infer_instance,
    isIso_of_isIso_restrict_of_iSup_eq_top U hU g⟩

/-! ### The criteria in terms of the modules of sections -/

/-- **The restriction of `g` to an open `U` is an isomorphism as soon as `g` is bijective on
sections over every open contained in `U`.** The sections of the restriction over an open `V` of
`U` are the sections of the original sheaf over the image of `V`, which is an open contained in
`U`, so the hypothesis says exactly that the restriction is bijective on all of its modules of
sections; those detect isomorphy
(`Stacks.SheafOfModulesEvaluation.isIso_of_forall_isIso_evaluation`). -/
theorem isIso_restrict_of_bijective_app (U : Opens Y) {M N : _root_.SheafOfModules.{u} O}
    (g : M ⟶ N) (h : ∀ V : Opens Y, V ≤ U → Function.Bijective (g.val.app (op V))) :
    IsIso ((Stacks.SheafOfModules.restrictSheafOfModules U.isOpenEmbedding O).map g) := by
  refine Stacks.SheafOfModulesEvaluation.isIso_of_forall_isIso_evaluation _ _ fun V => ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  refine h ((Opens.isOpenEmbedding U).functor.obj V.unop) ?_
  rintro y ⟨⟨y, hy⟩, -, rfl⟩
  exact hy

/-- **Being an isomorphism is local on the base, in terms of sections**: a morphism of sheaves of
modules is an isomorphism as soon as it is bijective on the sections over every open contained in
a member of some family of opens covering the space.

This is the form that applies to a restriction functor other than
`Stacks.SheafOfModules.restrictSheafOfModules`: whichever restriction to an open is used, its
modules of sections over the opens of the subspace are the modules of sections of the original
sheaf over the opens contained in that open. -/
theorem isIso_of_bijective_app_of_iSup_eq_top {ι : Type*} (U : ι → Opens Y)
    (hU : ⨆ i, U i = ⊤) {M N : _root_.SheafOfModules.{u} O} (g : M ⟶ N)
    (h : ∀ (i : ι) (V : Opens Y), V ≤ U i → Function.Bijective (g.val.app (op V))) :
    IsIso g :=
  isIso_of_isIso_restrict_of_iSup_eq_top U hU g fun i =>
    isIso_restrict_of_bijective_app (U i) g (h i)

end AlgebraicGeometry.SheafOfModules

end
