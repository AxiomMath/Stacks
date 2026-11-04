module

public import StacksFrontier.AlgebraicGeometry.Cohomology.CechModules
public import StacksFrontier.CategoryTheory.Sites.CechCofreeProduct
public import StacksFrontier.CategoryTheory.Sites.Modules.CofreeSlice
public import StacksFrontier.CategoryTheory.Sites.Modules.Injective

/-!
# Positive-degree Čech cohomology of an injective sheaf of modules

Let `R` be a sheaf of rings on the open-cover site of a topological space `X`, let `V` be an
open subset, let `U : ι → Opens X` be a family with `V = ⨆ i, U i` and let `I` be an injective
sheaf of `R`-modules. This file proves that the cohomology of the module-valued Čech complex
`Stacks.Cohomology.cechComplex V U hU I` of
`StacksFrontier/AlgebraicGeometry/Cohomology/CechModules.lean` vanishes in every positive degree.

Together with the degree `0` identification of that file this is [Stacks, Tag 01EP].

## Main definitions

* `Stacks.Cohomology.hullData V M W` packages, for each open `W` of `X`, the member of the
  slice category over `V`, the module of sections, and the isomorphism identifying the
  restriction to the slice of the cofree presheaf of modules on `W`.

## Main results

* `Stacks.Cohomology.sliceFunctor_obj_val`: the functor
  `Stacks.CategoryTheory.PresheafOfModules.sliceFunctor V` computes `sectionsPresheaf V`.
* `Stacks.Cohomology.isZero_homology_cechComplex_of_injective` (Stacks Tag 01EP, positive
  degrees): **the module-valued Čech cohomology of an injective sheaf of modules vanishes in
  positive degrees.**

## The proof

The first step of the Stacks Project's proof is that an injective sheaf of modules is injective
as a presheaf of modules, which is `SheafOfModules.injective_val` of
`StacksFrontier/CategoryTheory/Sites/Modules/Injective.lean`. The splitting is therefore
manufactured *globally*, in the category of presheaves of `R`-modules on all of `Opens X`: the
presheaf `I.val` embeds into its cofree hull `cofreeHull I.val`, the product over all opens `W`
of `X` of the cofree presheaves of modules on `W`, and injectivity splits that embedding.

It is then pushed down to the slice over `V` by the functor
`Stacks.CategoryTheory.PresheafOfModules.sliceFunctor V`, which computes `sectionsPresheaf V`
and which preserves the product. Each factor of the pushed-down product is identified: for
`W ≤ V` it is a plain cofree presheaf on the slice, by
`Stacks.CategoryTheory.PresheafOfModules.sliceCofreeOneIso`, and for `W ⊄ V` it is zero,
because all its index sets are empty. A zero presheaf is the cofree presheaf on any object with
a zero value, so in both cases the factor is isomorphic to a single-object cofree presheaf, and
`Stacks.CategoryTheory.CechComplex.isZero_homology_cechComplex_of_retract_of_pi` concludes: the
positive-degree Čech cohomology of a cofree presheaf vanishes because the Čech differential
becomes the alternating sum of the face maps of tuples of factorisations, which prepending a
factorisation contracts.

In particular the `W ⊄ V` factors need no comparison with a cofree presheaf of modules, and no
factor has to be dropped from the product.

## Implementation notes

The statement carries two restatements of the tag, which Stacks Tag 01EP, mentioning no
universes and no sheafification, does not:

* `[UnivLE.{uX, uM}]`, relating the universe of the space to the universe of the modules. The
  cofree hull is a product indexed by the opens of `X`, and the cofree presheaf on one open is
  at each object a product indexed by a type of morphisms of `Opens X`, which is a
  `Category.{uX}`; those products exist in `ModuleCat.{uM}` exactly under this hypothesis. It is
  a restatement rather than a weakening: the tag fixes no universes, and the hypothesis holds
  automatically when the two universes agree.
* `[(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{uM}]` and
  `[HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{uM}]`, which are the hypotheses of
  `SheafOfModules.injective_val`, i.e. of the sheafification adjunction for presheaves of
  modules through which Stacks Tag 015Z is applied. They are not instances for
  `Opens.grothendieckTopology X` at a free module universe, and carrying them as hypotheses is
  this repository's standing convention; see
  `StacksFrontier/AlgebraicGeometry/PseudoCoherent/FinitePresentationNextCohomology.lean`.

`hullData` returns the member of the slice, the value and the comparison isomorphism *together*,
as one `PSigma`. The three are entangled by the case distinction on `W ≤ V`, so defining them
separately would make the comparison isomorphism a statement about `dite`s appearing inside the
type of a cofree presheaf, which is a dependent rewrite; returning them together removes the
case distinction from every subsequent statement.

`sliceFunctor_obj_val` is the single place where the two definitionally equal spellings of the
restriction to the slice are crossed: `sectionsPresheaf` is built from
`SheafOfModules.overFunctor`, hence from `PresheafOfModules.pushforward` along the identity
morphism of the presheaf of rings of the slice, whereas `sliceFunctor` is built from the plain
precomposition functor `PresheafOfModules.pushforward₀`. The crossing is a `rfl` in a theorem
body, checked at default transparency.

## References

* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
* [Stacks Project, Tag 01EP](https://stacks.math.columbia.edu/tag/01EP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.CategoryTheory.PresheafOfModules (sliceFunctor cofreeHull toCofreeHull
  mono_toCofreeHull sliceCofreeOneIso isZero_sliceFunctor_obj_cofreeOne)

universe uX uR uM uI

attribute [local instance] ModuleCat.hasLimitsOfSize

namespace Stacks.Cohomology

open Stacks.Cohomology.CechSheaf (SectionRing coverObject sectionsPresheaf)

variable {X : Type uX} [TopologicalSpace X]
  {R : Sheaf (Opens.grothendieckTopology X) RingCat.{uR}} {ι : Type uI}

/-- **The restriction to the slice over `V` of the presheaf of modules underlying a sheaf of
modules is `sectionsPresheaf V`.** -/
theorem sliceFunctor_obj_val (V : Opens X) (I : SheafOfModules.{uM} R) :
    (sliceFunctor V).obj I.val = sectionsPresheaf V I :=
  rfl

variable [UnivLE.{uX, uM}]

open ZeroObject in
/-- **The data identifying a factor of the pushed-down cofree hull.** For an open `W` of `X`
this is a member of the slice category over `V`, a module of sections over `V`, and an
isomorphism from the restriction to the slice of the cofree presheaf of modules on `W` to the
plain cofree presheaf on that member with that value.

For `W ≤ V` the member is `W` itself, viewed over `V`, and the value is the sections of `M`
over `W` regarded as a module over the sections on `V`. For `W ⊄ V` both sides are zero: the
index sets of the restriction to the slice are all empty, and the cofree presheaf with a zero
value is zero. -/
noncomputable def hullData (V : Opens X) (M : PresheafOfModules.{uM} R.obj) (W : Opens X) :
    Σ' (T : Over V) (Jv : ModuleCat.{uM} (SectionRing R V)),
      ((sliceFunctor V).obj
          (Stacks.CategoryTheory.PresheafOfModules.cofreeOne (op W) (M.obj (op W))) ≅
        Stacks.CategoryTheory.CechComplex.cofreeOne T Jv) := by
  by_cases hW : W ≤ V
  · exact ⟨Over.mk (homOfLE hW), _, sliceCofreeOneIso (homOfLE hW) (M.obj (op W))⟩
  · exact ⟨Over.mk (𝟙 V), 0,
      (isZero_sliceFunctor_obj_cofreeOne V W ⟨fun g ↦ hW (leOfHom g)⟩ (M.obj (op W))).iso
        (Stacks.CategoryTheory.CechComplex.isZero_cofreeOne _ _ (isZero_zero _))⟩

/-- **The restriction to the slice over `V` of the cofree hull is the product of the
restrictions of its factors**, because `sliceFunctor V` preserves that product. -/
noncomputable def hullProductIso (V : Opens X) (M : PresheafOfModules.{uM} R.obj) :
    (sliceFunctor V).obj (cofreeHull M) ≅
      ∏ᶜ fun W : Opens X ↦ (sliceFunctor V).obj
        (Stacks.CategoryTheory.PresheafOfModules.cofreeOne (op W) (M.obj (op W))) :=
  PreservesProduct.iso (sliceFunctor V) _

/-- The restriction to the slice over `V` of the canonical embedding of `I.val` into its cofree
hull, viewed as a morphism out of `sectionsPresheaf V I`. -/
noncomputable def hullSection (V : Opens X) (I : SheafOfModules.{uM} R) :
    sectionsPresheaf V I ⟶ (sliceFunctor V).obj (cofreeHull I.val) :=
  (sliceFunctor V).map (toCofreeHull I.val)

variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{uM}]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{uM}]

/-- The restriction to the slice over `V` of the retraction of the cofree hull of `I.val` onto
`I.val`, which exists because an injective sheaf of modules is injective as a presheaf of
modules. -/
noncomputable def hullRetraction (V : Opens X) (I : SheafOfModules.{uM} R) [Injective I] :
    (sliceFunctor V).obj (cofreeHull I.val) ⟶ sectionsPresheaf V I :=
  have : Mono (toCofreeHull I.val) := mono_toCofreeHull I.val
  (sliceFunctor V).map (Injective.factorThru (𝟙 I.val) (toCofreeHull I.val))

/-- **The sections presheaf is a retract of the restriction to the slice of the cofree hull.** -/
theorem hullSection_comp_hullRetraction (V : Opens X) (I : SheafOfModules.{uM} R)
    [Injective I] : hullSection V I ≫ hullRetraction V I = 𝟙 (sectionsPresheaf V I) :=
  have : Mono (toCofreeHull I.val) := mono_toCofreeHull I.val
  (((sliceFunctor V).map_comp (toCofreeHull I.val)
        (Injective.factorThru (𝟙 I.val) (toCofreeHull I.val))).symm.trans
      (congrArg (sliceFunctor V).map
        (Injective.comp_factorThru (𝟙 I.val) (toCofreeHull I.val)))).trans
    ((sliceFunctor V).map_id I.val)

variable [UnivLE.{uI, uM}]

/-- **Stacks Project, Tag 01EP, positive degrees.** The cohomology of the module-valued Čech
complex of an injective sheaf of modules, for a covering of an open subset `V` by a family
`U`, vanishes in every positive degree.

An injective sheaf of modules is injective as a presheaf of modules, so it splits off its
global cofree hull; the restriction of that hull to the opens over `V` is a product of cofree
presheaves of `R(V)`-modules and of zero presheaves, whose positive-degree Čech cohomology
vanishes. -/
@[stacks 01EP "positive degrees"]
theorem isZero_homology_cechComplex_of_injective (V : Opens X) (U : ι → Opens X)
    (hU : V = ⨆ i, U i) (I : SheafOfModules.{uM} R) [Injective I] (n : ℕ) (hn : 0 < n) :
    IsZero ((cechComplex V U hU I).homology n) :=
  Stacks.CategoryTheory.CechComplex.isZero_homology_cechComplex_of_retract_of_pi
    (coverObject U hU) (fun W ↦ (hullData V I.val W).1) (fun W ↦ (hullData V I.val W).2.1)
    (sectionsPresheaf V I) _ (fun W ↦ (hullData V I.val W).2.2)
    (hullSection V I ≫ (hullProductIso V I.val).hom)
    ((hullProductIso V I.val).inv ≫ hullRetraction V I)
    (by
      rw [Category.assoc, Iso.hom_inv_id_assoc]
      exact hullSection_comp_hullRetraction V I)
    n hn

end Stacks.Cohomology

end
