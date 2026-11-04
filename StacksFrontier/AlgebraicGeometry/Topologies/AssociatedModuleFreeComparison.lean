module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeConstSheafification
public import StacksFrontier.AlgebraicGeometry.Spaces.SliceAssociatedModuleEssSurj
public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleAffineOpenCovering
public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleGlobalGeneration
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiRefinementModuleIso
public import StacksFrontier.CategoryTheory.Sites.LocallyBijectiveUniverse

/-!
# The two comparison morphisms of the essential surjectivity of Tag 03OJ

Let `S` be a scheme and let a site `C` of schemes over `S` satisfy the four conditions of
Tag 03OJ. The essential-surjectivity assertion of that tag goes through two comparisons: one
identifying the free sheaf of `𝒪`-modules on the site with the associated module `(⊕_L 𝒪_S)ᵃ`
of the free module on `S`, and one expressing the right exactness of `F ↦ Fᵃ` at a presentation.
This file constructs both and proves both invertible, in each case by reducing to two
Zariski-local conditions which the Zariski-refinement condition (2) of the tag supplies.

Both comparisons have the same shape and the same obstruction. Neither is bijective on the
sections over an arbitrary object of the site, because in each case the *source* is a
sheafification: `SheafOfModules.free L` is a coproduct taken in sheaves, and a cokernel in sheaves
of modules is the sheafification of the cokernel of presheaves of modules. So in each case the
two local conditions are read on a comparison out of the corresponding *presheaf* — the free
presheaf of modules, respectively the presheaf cokernel — and the passage back is the criterion
`Stacks.SheafOfModules.isIso_sheafificationHomEquiv_symm_of_isLocallyBijective`.

## The sheafification classes, and where they come from

Mathlib's `SheafOfModules.free` is a coproduct taken in *sheaves*, so it exists only on a site
admitting sheafification of abelian presheaves:

```
[HasWeakSheafify J AddCommGrpCat.{u}]  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
```

Neither follows from conditions (1)–(4) of Tag 03OJ. Mathlib's sufficient condition for both
is that the site be **essentially small** at the universe of the sections:
`CategoryTheory.hasSheafifyEssentiallySmallSite` and
`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall`, packaged for
abelian groups in this repository as
`CategoryTheory.hasWeakSheafify_addCommGrpCat_of_essentiallySmall` and
`CategoryTheory.wEqualsLocallyBijective_addCommGrpCat_of_essentiallySmall`. At the shape of
this tag — `C : Type (u + 1)` with `Category.{u} C` — those two produce exactly the classes
above from `EssentiallySmall.{u} C`, and that is how they are supplied here.

`EssentiallySmall.{u} C` is **not** a strengthening of the source. It is what the source's own
condition (1) says, once `Sch/S` is read as the source reads it.

Sites, Definition 00VH asks only that the coverings `Cov(𝒞)` form a set, and says nothing about
the size of `Ob(𝒞)`; so the word "site" in the statement of Tag 03OJ is not by itself where the
smallness comes from. It comes from `Sch/S`. The `Sch/S` of condition (1) is the slice of one
of the big sites of Topologies, Section 34.2, and those are built by "appropriately choosing a
set of schemes and a set of coverings" — concretely by Set Theory, Section 3.9, which takes
`Sch_α` to be the full subcategory of schemes whose objects are elements of `V_α`, so that
`Ob(Sch_α)` is a set. Condition (1) therefore puts `C` inside a category with a `u`-small
collection of objects, and
`CategoryTheory.essentiallySmall_fullSubcategory` turns that into `EssentiallySmall.{u} C`.

Where the smallness is lost is in the *formalization* of condition (1), not in the source: this
tag renders `Sch/S` as `CategoryTheory.Over S` for the whole of `Scheme.{u}`, and that is not
essentially small. `Spec` embeds `CommRingCat.{u}ᵒᵖ` fully faithfully into `Scheme.{u}`, and the
free commutative rings on the types of `Type u` already give one isomorphism class per cardinal
of `Type u`, a collection which is not `u`-small; so
`CategoryTheory.essentiallySmall_of_fully_faithful` applied to `toOver` gives nothing. Taking
`C = Over S` itself, with its Zariski coverings, satisfies conditions (1)–(4) as formalized here
and fails `EssentiallySmall.{u} C` — and its covering sieves over an object are not `u`-small
either, which is the hypothesis Mathlib's plus-construction instance in
`Mathlib.CategoryTheory.Sites.LeftExact` actually consumes. On that `C` the sheafification the
conclusion of the tag speaks of is unavailable, which is exactly the case the source's choice of
a set of schemes rules out and the formalization's `Over S` does not.

So `EssentiallySmall.{u} C` is carried here as the fifth hypothesis which restores the strength
of condition (1) that the rendering of `Sch/S` as `Over S` drops. It adds nothing to the
source, and the count of places where this tag's formalization is stronger than its source is
unchanged by it.

## Main definitions

* `Stacks.Sites.freeAssociatedComparison`: **the comparison morphism of step one**, from the
  free sheaf of `𝒪`-modules on `L` to the associated module `(⊕_L 𝒪_S)ᵃ`.
* `Stacks.Sites.freeAssociatedPresheafComparison`: the same comparison with the sheafification
  removed from its source, out of the free **presheaf** of modules, whose sections over an
  object of the site are the finitely supported families `L →₀ Γ(T, 𝒪)`.
* `Stacks.Sites.siteAssociatedModuleMap`: the morphism `Fᵃ ⟶ Gᵃ` of sheaves of modules on the
  site induced by a morphism of quasi-coherent modules on `S`.
* `Stacks.Sites.cokernelAssociatedComparison`: **the comparison morphism of step two**, from the
  cokernel of `Fᵃ ⟶ Gᵃ` taken in the sheaves of `𝒪`-modules on the site to the associated module
  `coker(F ⟶ G)ᵃ`.
* `Stacks.Sites.cokernelAssociatedPresheafComparison`: the same comparison with the
  sheafification removed from its source, out of the cokernel taken in the **presheaves** of
  modules, whose sections over an object of the site are the quotients of the sections of `Gᵃ`.

## Main results

* `Stacks.Sites.freeAssociatedComparison_app_freeSectionsMap_single`: the comparison carries the
  section `Finsupp.single l r` of the objectwise direct sum to `r` times the restriction of the
  `l`-th tautological global section. This is the formula the geometric input is checked
  against.
* `Stacks.Sites.isIso_freeAssociatedComparison_of_zariskiRefinement`: **the comparison is an
  isomorphism as soon as it is Zariski-locally surjective and Zariski-locally injective**, which
  is step one of Tag 03OJ with its two geometric inputs isolated.
* `Stacks.Sites.isIso_freeAssociatedComparison_of_zariskiRefinement_finsupp`: **the same with
  both local conditions moved to finitely supported families**, which is the only shape in which
  the second of them can be checked; see the implementation notes.
* `Stacks.Sites.sections_eval_freeAssociatedSection_eq`: the value of the `l`-th tautological
  section over an object of the site is the `l`-th tautological section of the pullback of
  `⊕_L 𝒪_S` to the underlying scheme of that object.
* `Stacks.Sites.freeAssociatedPresheafComparison_app`: the free-presheaf comparison carries a
  finitely supported family to the corresponding finite sum of multiples of the tautological
  sections.
* `Stacks.Sites.isIso_freeAssociatedComparison`: **step one of Tag 03OJ, with both local
  conditions discharged** — the comparison morphism is an isomorphism on a site satisfying the
  conditions of the tag, the Zariski-refinement condition (2) being the only hypothesis
  carried.
* `Stacks.Sites.isLocallySurjective_cokernelAssociatedPresheafComparison` and
  `Stacks.Sites.isLocallyInjective_cokernelAssociatedPresheafComparison`: **the two local
  conditions of step two, discharged** from the two affine inputs
  `AlgebraicGeometry.Scheme.Modules.surjective_pullback_map_appTop_of_epi` and
  `AlgebraicGeometry.Scheme.Modules.exists_pullback_map_appTop_eq_of_cokernelπ_appTop_eq_zero`.
* `Stacks.Sites.isIso_cokernelAssociatedComparison`: **step two of Tag 03OJ** — the functor
  `F ↦ Fᵃ` is right exact at a presentation: the comparison from the cokernel of `Fᵃ ⟶ Gᵃ` to
  `coker(F ⟶ G)ᵃ` is an isomorphism, the Zariski-refinement condition (2) again being the only
  hypothesis carried beyond the sheaf conditions.
* `Stacks.Sites.surjective_siteAssociatedModuleMap_free` and
  `Stacks.Sites.surjective_associatedModuleMap_free`: **the surjectivity half of the free-source
  case of Descent, Lemma 0GN7 over an arbitrary base** — every morphism `(⊕_L 𝒪_S)ᵃ ⟶ Nᵃ` on the
  site is `φᵃ`. With the injectivity half
  `Stacks.Sites.associatedModuleMap_injective_of_epi_free`, whose generation hypothesis a free
  module satisfies, this is 0GN7 for a free source with no affineness of the base. The
  fullness half already in the tree,
  `Stacks.Sites.surjective_associatedModuleMap`, needs `IsAffine S` and is not available here;
  what replaces affineness is step one, which identifies the free sheaf of modules on the site
  with `(⊕_L 𝒪_S)ᵃ` and so lets the morphism be read off the terminal object.
* `Stacks.Sites.exists_siteAssociatedModuleMap_free_comp`: the same in the shape the essential
  surjectivity of Tag 03OJ consumes — **a map of free sheaves of `𝒪`-modules on the site comes
  from a map of free modules on `S`**, compatibly with the two comparison morphisms of step one.
  A global presentation of a quasi-coherent module on the site is such a map of coproducts, and
  this is what carries it downstairs; step two then identifies the cokernels.

## Implementation notes

The comparison is *defined* by the equivalence `Stacks.Sites.freeHomEquivSiteAssociatedModule`
already in the tree: morphisms out of a free sheaf of modules into `Nᵃ` are morphisms out of a
free sheaf of modules into the pullback of `N` to the underlying scheme of a terminal object of
the site, and the canonical one for `N = ⊕_L 𝒪_S` is the inverse of
`AlgebraicGeometry.Scheme.Modules.pullbackFreeIso`, the pullback of a free module being free.
Conditions (1) and (3) of the tag give the terminal object, through
`Stacks.Sites.isTerminalOfIsIsoHom`, and nothing else is used to construct the comparison; the
Zariski-refinement condition (2) enters only in its invertibility.

`Stacks.Sites.isIso_freeAssociatedComparison_of_zariskiRefinement` is
`Stacks.Sites.isIso_of_zariskiRefinement` at this comparison. The two local conditions are left
as hypotheses in the shape that criterion asks for them, with the Zariski covering depending on
the section: the objects condition (2) supplies lie over a member of a Zariski covering of the
underlying scheme and their own underlying schemes need be neither affine nor quasi-compact, so
bijectivity of the comparison *at* those objects is unavailable.

**Why the local conditions are read on finitely supported families.** The injectivity hypothesis
of `Stacks.Sites.isIso_freeAssociatedComparison_of_zariskiRefinement` cannot be discharged
directly, and the obstruction is on the *source* side of the comparison. `SheafOfModules.free L`
is a coproduct taken in sheaves, hence the sheafification of the objectwise direct sum, so its
sections over an object `T` of the site are in general strictly larger than `L →₀ Γ(T, 𝒪)`
(`StacksFrontier.AlgebraicGeometry.Spaces.FreeModuleSections`, module docstring). That injectivity
hypothesis quantifies over *those* sections, and no statement about the sections of a pullback of
a free module over an affine scheme, such as
`AlgebraicGeometry.Scheme.Modules.pullbackFreeSectionsEquiv_single`, says anything about them: a
section of `SheafOfModules.free L` is only locally a finite sum of tautological sections, so there
is nothing to restrict.

`Stacks.Sites.isIso_freeAssociatedComparison_of_zariskiRefinement_finsupp` therefore reads the
same two local conditions on `Stacks.Sites.freeAssociatedPresheafComparison`, whose source is the
free *presheaf* of modules `Stacks.PresheafOfModules.freeConst L`: over an object of the site its
sections are the finitely supported families on the nose, with
`Stacks.PresheafOfModules.freeConstBasis` as a basis, so both conditions are statements about
finite sums of multiples of the tautological sections and
`AlgebraicGeometry.Scheme.Modules.pullbackFreeSectionsEquiv_single` is on the right side of the
comparison to be used against them. The step from that statement to invertibility of the
comparison out of the free *sheaf* is
`Stacks.SheafOfModules.isIso_freeHomEquiv_symm_of_isLocallyBijective`, whose content is that the
canonical morphism from the free presheaf of modules to the free sheaf of modules is locally
bijective — i.e. that the free sheaf of modules is the sheafification of the free presheaf of
modules.

**The bridge.** Both hypotheses of
`Stacks.Sites.isIso_freeAssociatedComparison_of_zariskiRefinement_finsupp` are discharged in
`Stacks.Sites.isIso_freeAssociatedComparison`. What they need is that, for a morphism
`γ : V ⟶ W` of schemes over `S`, the pullback map on global sections
`AlgebraicGeometry.pullbackSectionsMap` carries the `l`-th tautological section of
`W.hom⁺(⊕_L 𝒪_S)` to the `l`-th tautological section of `V.hom⁺(⊕_L 𝒪_S)`. This is
`AlgebraicGeometry.Scheme.Modules.pullbackSectionsMap_freeTautologicalSection`, in
`StacksFrontier.AlgebraicGeometry.Topologies.ZariskiRefinementModuleIso`, resting on the
free-module composition compatibility `AlgebraicGeometry.Scheme.Modules.pullbackFreeIso_comp` at
an arbitrary index type. That is the free-module form of
`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_comp` of
`StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison`, the compatibility
of `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso` with
`AlgebraicGeometry.Scheme.Modules.pullbackComp`; there `pullbackUnitIso` is *defined* as
`CategoryTheory.asIso` of `SheafOfModules.pullbackObjUnitToUnit`, so the monoidal-unit spelling
and the pullback spelling are the same morphism. Over an object of the site, the tautological
global section of the pullback of `⊕_L 𝒪_S` is the scheme-level
`AlgebraicGeometry.Scheme.Modules.freeTautologicalSection` at the structure morphism of that
object.

**How the two conditions are discharged.** The Zariski covering is
`Stacks.Sites.affineOpenImmersionPresieve`, the open immersions with *affine* source; affineness
is needed and is available, because the affine opens cover. An arrow of the site whose image
factors through a member of it factors as `Z.left ⟶ U ⟶ T.left` with `U` affine, and the middle
object is read as a scheme over `S` by `CategoryTheory.Over.mk`: it is an object of `Over S` and
in general **not** an object of the site, which is why the factorization is taken apart with
`Stacks.Sites.pullbackSectionsMap_comp_any` (the `map_comp` law of
`AlgebraicGeometry.quasiCoherentPresheafConstruction`) and not with functoriality
of the associated module over the site. Over `U` the sections of the pullback of `⊕_L 𝒪_S` are
the finitely supported families
(`AlgebraicGeometry.Scheme.Modules.pullbackFreeSectionsEquiv`), matched with the finite sums of
multiples of the tautological sections by
`AlgebraicGeometry.Scheme.Modules.pullbackFreeSectionsEquiv_eq`; and the remaining arrow is
handled by `AlgebraicGeometry.Scheme.Modules.pullbackSectionsMap_freeSectionsCombination`, which
is where the bridge enters. On the source side the restriction maps of the free presheaf of
modules are `Finsupp.mapRange` of the restriction maps of the structure presheaf
(`Stacks.PresheafOfModules.freeConst_map_apply`), and the comparison itself is the finite sum of
multiples (`Stacks.PresheafOfModules.freeConstDesc_app_apply`).

**Step two.** The comparison morphism of step two needs the sheaf condition for the associated
presheaf of the cokernel as a further parameter, exactly as `Stacks.Sites.siteAssociatedModule`
needs one: `Stacks.Sites.cokernelAssociatedComparison` carries `hH`, whose type is
`CategoryTheory.Presheaf.IsSheaf K.toGrothendieck (Stacks.Sites.associatedPresheaf S
(CategoryTheory.Limits.cokernel φ) toOver)`. No analogue of
`AlgebraicGeometry.Scheme.Modules.pullbackSectionsMap_freeSectionsCombination` is needed, because
there is no basis to carry. What moves a section of `coker(φ)` across the factorisation is the
naturality of the pullback map on sections in the module,
`AlgebraicGeometry.pullbackSectionsMap_naturality`. Local surjectivity is discharged by the
affine input `AlgebraicGeometry.Scheme.Modules.surjective_pullback_map_appTop_of_epi`; local
*injectivity* of the cokernel comparison needs a second affine input, exactness in the middle,
`AlgebraicGeometry.Scheme.Modules.exists_pullback_map_appTop_eq_of_cokernelπ_appTop_eq_zero`,
which is where the exactness of the sections of a pullback over an affine scheme enters, through
`AlgebraicGeometry.surjective_app_of_epi_of_isAffineOpen` (the twin of
`Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen`) applied to
`CategoryTheory.Abelian.factorThruImage`.

The passage from the presheaf cokernel to the sheaf cokernel is the second place where this file's
two comparisons share their shape, and it is done once, generally:
`Stacks.SheafOfModules.isIso_sheafificationHomEquiv_symm_of_isLocallyBijective` makes the
transpose of the presheaf comparison invertible, and
`Stacks.Sites.sheafifyCokernelToCokernel` identifies the source of that transpose with the sheaf
cokernel. That identification is **not** proved by computing a colimit: it is an epimorphism
because the projection onto the sheaf cokernel factors through it
(`Stacks.SheafOfModules.epi_sheafificationHomEquiv_symm_forget_map`, the counit of the
sheafification adjunction being invertible), a monomorphism because composing it with the
comparison of step two gives the invertible transpose, and therefore invertible, the sheaves of
modules on the site being an abelian category. That last step is why
`Stacks.Sites.hasSheafify_toGrothendieck` is declared alongside
`Stacks.Sites.hasWeakSheafify_toGrothendieck`: the weak form supplies the cokernel, but only the
full form supplies `CategoryTheory.Abelian` and hence `CategoryTheory.Balanced`.

No `@[stacks]` attribute is claimed. The registration of Tag 03OJ remains the single one at
`StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.FpqcCoveringSiteSheaves`; the comparison is
a step in the proof of the second assertion, not an assertion of the source.

## References

* [Stacks Project, Tag 03OJ](https://stacks.math.columbia.edu/tag/03OJ)
* [Stacks Project, Tag 00VH](https://stacks.math.columbia.edu/tag/00VH)
* [Stacks Project, Tag 000H](https://stacks.math.columbia.edu/tag/000H)
* [Stacks Project, Tag 020M](https://stacks.math.columbia.edu/tag/020M)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Sites

open _root_.AlgebraicGeometry

variable (S : Scheme.{u}) {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u} C]
  (toOver : C ⥤ Over S) (K : Precoverage C)

/-- Abelian presheaves on a small site of schemes over `S` admit a sheafification. This is
`CategoryTheory.hasWeakSheafify_addCommGrpCat_of_essentiallySmall`, whose conclusion is at
`AddCommGrpCat.{max v₁ z}` and so at `AddCommGrpCat.{u}` for a site with objects in
`Type (u + 1)` and morphisms in `Type u`. -/
local instance hasWeakSheafify_toGrothendieck :
    HasWeakSheafify K.toGrothendieck AddCommGrpCat.{u} :=
  hasWeakSheafify_addCommGrpCat_of_essentiallySmall.{u} _

/-- On a small site of schemes over `S` the maps of abelian presheaves inverted by
sheafification are exactly the locally bijective ones. This is
`CategoryTheory.wEqualsLocallyBijective_addCommGrpCat_of_essentiallySmall`. -/
local instance wEqualsLocallyBijective_toGrothendieck :
    K.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  wEqualsLocallyBijective_addCommGrpCat_of_essentiallySmall.{u} _

/-- The canonical maps on global sections of pullbacks are contravariantly functorial, for an
arbitrary module. This is the `map_comp` law of the presheaf
`AlgebraicGeometry.quasiCoherentPresheafConstruction`, whose maps are
`AlgebraicGeometry.pullbackSectionsMap` by construction. -/
private lemma pullbackSectionsMap_comp_any {T : Scheme.{u}} (F : T.Modules) {X Y Z : Over T}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullbackSectionsMap F (f ≫ g) = pullbackSectionsMap F g ≫ pullbackSectionsMap F f :=
  (quasiCoherentPresheafConstruction T F).functor.map_comp g.op f.op

/-- A morphism of schemes over `T` whose underlying morphism factors through `ι : U ⟶ Y.left`
factors through `Over.mk (ι ≫ Y.hom)`, and the pullback map on sections of any module factors
accordingly. -/
private lemma exists_comp_homMk_pullbackSectionsMap {T : Scheme.{u}} {X Y : Over T} (f : X ⟶ Y)
    {U : Scheme.{u}} (h : X.left ⟶ U) (ι : U ⟶ Y.left) (hfac : h ≫ ι = f.left) :
    ∃ g : X ⟶ Over.mk (ι ≫ Y.hom), g.left = h ∧ ∀ (F : T.Modules) s,
      pullbackSectionsMap F f s = pullbackSectionsMap F g
        (pullbackSectionsMap F (Over.homMk ι rfl : Over.mk (ι ≫ Y.hom) ⟶ Y) s) := by
  have hw : h ≫ (Over.mk (ι ≫ Y.hom)).hom = X.hom := by
    change h ≫ ι ≫ Y.hom = X.hom
    rw [← Category.assoc, hfac]
    exact Over.w f
  refine ⟨Over.homMk h hw, rfl, fun F s => ?_⟩
  have hf : f = Over.homMk h hw ≫ (Over.homMk ι rfl : Over.mk (ι ≫ Y.hom) ⟶ Y) :=
    Over.OverMorphism.ext hfac.symm
  rw [hf, pullbackSectionsMap_comp_any]
  rfl

variable [toOver.Full] [toOver.Faithful] (L : Type u)
  (hR : Presheaf.IsSheaf K.toGrothendieck (structurePresheaf S toOver))
  (hM : Presheaf.IsSheaf K.toGrothendieck
    (associatedPresheaf S (SheafOfModules.free (R := S.ringCatSheaf) L) toOver))
  (e : C) [IsIso (toOver.obj e).hom]

/-- **The comparison morphism of step one of Tag 03OJ**: the free sheaf of `𝒪`-modules on `L`
over a site of schemes over `S` maps to the associated module of the free module `⊕_L 𝒪_S` on
`S`.

It is the morphism which `Stacks.Sites.freeHomEquivSiteAssociatedModule` matches with the
inverse of `AlgebraicGeometry.Scheme.Modules.pullbackFreeIso` at a terminal object of the site;
conditions (1) and (3) of the tag give that terminal object, by
`Stacks.Sites.isTerminalOfIsIsoHom`. -/
public noncomputable def freeAssociatedComparison :
    SheafOfModules.free (R := siteStructureSheaf S toOver K.toGrothendieck hR) L ⟶
      siteAssociatedModule S (SheafOfModules.free (R := S.ringCatSheaf) L) toOver
        K.toGrothendieck hR hM :=
  (freeHomEquivSiteAssociatedModule S toOver _ K.toGrothendieck hR hM
    (isTerminalOfIsIsoHom S toOver e) L).symm
    (Scheme.Modules.pullbackFreeIso (toOver.obj e).hom L).inv

/-- The `l`-th tautological global section of `⊕_L 𝒪_S`, read as a global section of the
associated module `(⊕_L 𝒪_S)ᵃ` on the site. On a site with a terminal object a global section
is its value there, by
`Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal`, and conditions (1) and (3) of
Tag 03OJ give that terminal object. -/
public noncomputable def freeAssociatedSection (l : L) :
    (siteAssociatedModule S (SheafOfModules.free (R := S.ringCatSheaf) L) toOver
      K.toGrothendieck hR hM).sections :=
  (Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal _
    (isTerminalOfIsIsoHom S toOver e)).symm
    (Scheme.Modules.freeTautologicalSection (toOver.obj e).hom L l)

omit [EssentiallySmall.{u} C] in
/-- The value of the `l`-th tautological section over an object of the site is the restriction
of the tautological global section along the unique morphism to the terminal object. -/
public theorem sections_eval_freeAssociatedSection (l : L) (T : C) :
    PresheafOfModules.sections.eval (freeAssociatedSection S toOver K L hR hM e l) (op T) =
      (siteAssociatedModule S (SheafOfModules.free (R := S.ringCatSheaf) L) toOver
        K.toGrothendieck hR hM).val.map ((isTerminalOfIsIsoHom S toOver e).from T).op
          (Scheme.Modules.freeTautologicalSection (toOver.obj e).hom L l) :=
  rfl

/-- The comparison morphism is the morphism out of the free sheaf of modules belonging, under
`SheafOfModules.freeHomEquiv`, to the family of tautological sections. -/
public theorem freeAssociatedComparison_eq :
    freeAssociatedComparison S toOver K L hR hM e =
      (SheafOfModules.freeHomEquiv _).symm (freeAssociatedSection S toOver K L hR hM e) :=
  rfl

/-- **The comparison morphism on the image of `Finsupp.single`.** Over an object `T` of the
site it carries the section `Finsupp.single l r` of the objectwise direct sum to `r` times the
restriction, along the unique morphism to the terminal object, of the `l`-th tautological global
section of `⊕_L 𝒪_S`.

This is the formula the geometric input of step one is checked against: it reduces the two local
conditions of `Stacks.Sites.isIso_of_zariskiRefinement` to the statement that a section of the
pullback of `⊕_L 𝒪_S` is Zariski-locally a finite sum of tautological sections, which over an
affine scheme is
`AlgebraicGeometry.Scheme.Modules.pullbackFreeSectionsEquiv_single`. -/
public theorem freeAssociatedComparison_app_freeSectionsMap_single (T : C) (l : L)
    (r : (siteStructureSheaf S toOver K.toGrothendieck hR).obj.obj (op T)) :
    ((freeAssociatedComparison S toOver K L hR hM e).val.app (op T)).hom
        ((freeSectionsMap (R := siteStructureSheaf S toOver K.toGrothendieck hR) L
          (op T)).hom (Finsupp.single l r)) =
      r • PresheafOfModules.sections.eval
            (freeAssociatedSection S toOver K L hR hM e l) (op T) := by
  rw [freeAssociatedComparison_eq]
  exact Stacks.SheafOfModules.freeHomEquiv_symm_val_app_freeSectionsMap_single _ _ (op T) l r

/-- **Step one of Tag 03OJ, reduced to its two geometric inputs.** On a site of schemes over
`S` whose Zariski coverings are refined by coverings of the site — condition (2) of the tag —
the comparison morphism from the free sheaf of `𝒪`-modules to the associated module of the free
module on `S` is an isomorphism as soon as every section of the target lifts, and every equality
of sections of the source holds, after restriction along the arrows factoring through a member of
a Zariski covering of the underlying scheme.

This is `Stacks.Sites.isIso_of_zariskiRefinement` at
`Stacks.Sites.freeAssociatedComparison`. The Zariski covering is allowed to depend on the
section, as that criterion allows: the objects condition (2) supplies lie over a member of the
covering and their underlying schemes need be neither affine nor quasi-compact. -/
public theorem isIso_freeAssociatedComparison_of_zariskiRefinement
    (hZariski : ∀ (T : C) (R : Presieve ((toOver.obj T).left)),
      R ∈ Scheme.zariskiPrecoverage.{u} ((toOver.obj T).left) →
        ∃ Q : Presieve T, Q ∈ K T ∧
          Presieve.map (toOver ⋙ Over.forget S) Q ≤ (Sieve.generate R).arrows)
    (hsurj : ∀ (T : C) (s : ToType ((siteAssociatedModule S
        (SheafOfModules.free (R := S.ringCatSheaf) L) toOver
          K.toGrothendieck hR hM).val.obj (op T))),
      ∃ R : Presieve ((toOver.obj T).left),
        R ∈ Scheme.zariskiPrecoverage.{u} ((toOver.obj T).left) ∧
          ∀ ⦃Z : C⦄ (f : Z ⟶ T),
            (Sieve.generate R).arrows ((toOver ⋙ Over.forget S).map f) →
              ∃ t : ToType ((SheafOfModules.free
                  (R := siteStructureSheaf S toOver K.toGrothendieck hR) L).val.obj (op Z)),
                (freeAssociatedComparison S toOver K L hR hM e).val.app (op Z) t =
                  (siteAssociatedModule S (SheafOfModules.free (R := S.ringCatSheaf) L) toOver
                    K.toGrothendieck hR hM).val.map f.op s)
    (hinj : ∀ (T : C) (x y : ToType ((SheafOfModules.free
        (R := siteStructureSheaf S toOver K.toGrothendieck hR) L).val.obj (op T))),
      (freeAssociatedComparison S toOver K L hR hM e).val.app (op T) x =
        (freeAssociatedComparison S toOver K L hR hM e).val.app (op T) y →
      ∃ R : Presieve ((toOver.obj T).left),
        R ∈ Scheme.zariskiPrecoverage.{u} ((toOver.obj T).left) ∧
          ∀ ⦃Z : C⦄ (f : Z ⟶ T),
            (Sieve.generate R).arrows ((toOver ⋙ Over.forget S).map f) →
              (SheafOfModules.free
                (R := siteStructureSheaf S toOver K.toGrothendieck hR) L).val.map f.op x =
                (SheafOfModules.free
                  (R := siteStructureSheaf S toOver K.toGrothendieck hR) L).val.map f.op y) :
    IsIso (freeAssociatedComparison S toOver K L hR hM e) :=
  isIso_of_zariskiRefinement S toOver K hZariski _ hsurj hinj

/-- **The comparison morphism of step one, read on the free *presheaf* of modules.** Its
sections over an object of the site are the finitely supported families `L →₀ Γ(T, 𝒪)`, and it
carries the `l`-th standard basis vector to the `l`-th tautological section
`Stacks.Sites.freeAssociatedSection`.

This is `Stacks.Sites.freeAssociatedComparison` with the sheafification removed from its source,
and it is the map the two local conditions of step one are checked on: a section of
`SheafOfModules.free L` over an object of the site is only locally a finite sum of tautological
sections, so neither condition can be checked on `Stacks.Sites.freeAssociatedComparison`
itself. -/
public noncomputable def freeAssociatedPresheafComparison :
    Stacks.PresheafOfModules.freeConst
        (R := (siteStructureSheaf S toOver K.toGrothendieck hR).obj) L ⟶
      (siteAssociatedModule S (SheafOfModules.free (R := S.ringCatSheaf) L) toOver
        K.toGrothendieck hR hM).val :=
  Stacks.PresheafOfModules.freeConstDesc (freeAssociatedSection S toOver K L hR hM e)

omit [EssentiallySmall.{u} C] in
/-- The free-presheaf comparison carries the `l`-th standard basis vector of the sections over an
object of the site to the `l`-th tautological section there. -/
public theorem freeAssociatedPresheafComparison_app_basis (T : Cᵒᵖ) (l : L) :
    (freeAssociatedPresheafComparison S toOver K L hR hM e).app T
        (Stacks.PresheafOfModules.freeConstBasis L T l) =
      PresheafOfModules.sections.eval (freeAssociatedSection S toOver K L hR hM e l) T :=
  Stacks.PresheafOfModules.freeConstDesc_app_basis _ T l

/-- **Step one of Tag 03OJ, reduced to two conditions on finitely supported families.** On a
site of schemes over `S` whose Zariski coverings are refined by coverings of the site —
condition (2) of the tag — the comparison morphism from the free sheaf of `𝒪`-modules to the
associated module of the free module on `S` is an isomorphism as soon as, after restriction along
the arrows factoring through a member of a Zariski covering of the underlying scheme, every
section of the target is a **finite sum of multiples of the tautological sections** and two such
finite sums which agree become equal.

This is the form in which the geometric input of step one is available, and
`Stacks.Sites.isIso_freeAssociatedComparison_of_zariskiRefinement` is not: the sections of
`SheafOfModules.free L` over an object of the site are not finitely supported families — the free
sheaf of modules is a coproduct of *sheaves*, hence a sheafification of the objectwise direct sum
— so the injectivity hypothesis of that statement quantifies over sections which no geometric
computation produces. The passage from the free presheaf to the free sheaf is
`Stacks.SheafOfModules.isIso_freeHomEquiv_symm_of_isLocallyBijective`, whose content is that the
canonical morphism between them is locally bijective. -/
public theorem isIso_freeAssociatedComparison_of_zariskiRefinement_finsupp
    (hZariski : ∀ (T : C) (R : Presieve ((toOver.obj T).left)),
      R ∈ Scheme.zariskiPrecoverage.{u} ((toOver.obj T).left) →
        ∃ Q : Presieve T, Q ∈ K T ∧
          Presieve.map (toOver ⋙ Over.forget S) Q ≤ (Sieve.generate R).arrows)
    (hsurj : ∀ (T : C) (s : ToType ((siteAssociatedModule S
        (SheafOfModules.free (R := S.ringCatSheaf) L) toOver
          K.toGrothendieck hR hM).val.obj (op T))),
      ∃ R : Presieve ((toOver.obj T).left),
        R ∈ Scheme.zariskiPrecoverage.{u} ((toOver.obj T).left) ∧
          ∀ ⦃Z : C⦄ (f : Z ⟶ T),
            (Sieve.generate R).arrows ((toOver ⋙ Over.forget S).map f) →
              ∃ c : ToType ((Stacks.PresheafOfModules.freeConst
                  (R := (siteStructureSheaf S toOver K.toGrothendieck hR).obj) L).obj (op Z)),
                (freeAssociatedPresheafComparison S toOver K L hR hM e).app (op Z) c =
                  (siteAssociatedModule S (SheafOfModules.free (R := S.ringCatSheaf) L) toOver
                    K.toGrothendieck hR hM).val.map f.op s)
    (hinj : ∀ (T : C) (x y : ToType ((Stacks.PresheafOfModules.freeConst
        (R := (siteStructureSheaf S toOver K.toGrothendieck hR).obj) L).obj (op T))),
      (freeAssociatedPresheafComparison S toOver K L hR hM e).app (op T) x =
        (freeAssociatedPresheafComparison S toOver K L hR hM e).app (op T) y →
      ∃ R : Presieve ((toOver.obj T).left),
        R ∈ Scheme.zariskiPrecoverage.{u} ((toOver.obj T).left) ∧
          ∀ ⦃Z : C⦄ (f : Z ⟶ T),
            (Sieve.generate R).arrows ((toOver ⋙ Over.forget S).map f) →
              (Stacks.PresheafOfModules.freeConst
                  (R := (siteStructureSheaf S toOver K.toGrothendieck hR).obj) L).map f.op x =
                (Stacks.PresheafOfModules.freeConst
                  (R := (siteStructureSheaf S toOver K.toGrothendieck hR).obj) L).map f.op y) :
    IsIso (freeAssociatedComparison S toOver K L hR hM e) := by
  rw [freeAssociatedComparison_eq]
  refine Stacks.SheafOfModules.isIso_freeHomEquiv_symm_of_isLocallyBijective _ ?_ ?_
  · exact isLocallyInjective_of_zariskiRefinement S toOver K hZariski _ hinj
  · exact isLocallySurjective_of_zariskiRefinement S toOver K hZariski _ hsurj


/-! ### Discharging the two local conditions -/

/-- The presieve of the open immersions into a scheme whose source is affine. It is a Zariski
covering: its members are open immersions by construction, and the affine opens cover. -/
public def affineOpenImmersionPresieve (X : Scheme.{u}) : Presieve X :=
  fun ⦃Z⦄ h => IsOpenImmersion h ∧ IsAffine Z

/-- **`Stacks.Sites.affineOpenImmersionPresieve` is a Zariski covering.** -/
public theorem affineOpenImmersionPresieve_mem_zariskiPrecoverage (X : Scheme.{u}) :
    affineOpenImmersionPresieve X ∈ Scheme.zariskiPrecoverage.{u} X := by
  refine ⟨fun x => ?_, fun {Z} h hh => hh.1⟩
  obtain ⟨V, hV, hxV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
  exact ⟨Scheme.forget.obj V.toScheme, Scheme.forget.map V.ι,
    Presieve.map_map (F := Scheme.forget) ⟨inferInstance, hV⟩, ⟨⟨x, hxV⟩, rfl⟩⟩

omit [EssentiallySmall.{u} C] in
/-- **The value of the `l`-th tautological section over an object of the site is the `l`-th
tautological section of the pullback of `⊕_L 𝒪_S` to the underlying scheme of that object.**
This is the bridge
`AlgebraicGeometry.Scheme.Modules.pullbackSectionsMap_freeTautologicalSection` at the unique
morphism to the terminal object: without it the comparison and the affine computation speak of
two unrelated families of sections. -/
public theorem sections_eval_freeAssociatedSection_eq (T : C) (l : L) :
    PresheafOfModules.sections.eval (freeAssociatedSection S toOver K L hR hM e l) (op T) =
      Scheme.Modules.freeTautologicalSection (toOver.obj T).hom L l :=
  (sections_eval_freeAssociatedSection S toOver K L hR hM e l T).trans
    ((siteAssociatedModule_map_apply _ toOver _ hR hM
        ((isTerminalOfIsIsoHom S toOver e).from T) _).trans
      (Scheme.Modules.pullbackSectionsMap_freeTautologicalSection L
        (toOver.map ((isTerminalOfIsIsoHom S toOver e).from T)) l))

omit [EssentiallySmall.{u} C] in
/-- **The free-presheaf comparison is the finite sum of multiples of the tautological
sections.** Its source over an object of the site is the finitely supported families
`L →₀ Γ(T, 𝒪)`, and it carries such a family to the corresponding finite sum of multiples of the
tautological sections of the pullback of `⊕_L 𝒪_S` to the underlying scheme. -/
public theorem freeAssociatedPresheafComparison_app (T : C)
    (c : L →₀ Γ((toOver.obj T).left, ⊤)) :
    (freeAssociatedPresheafComparison S toOver K L hR hM e).app (op T) c =
      Scheme.Modules.freeSectionsCombination (toOver.obj T).hom L c := by
  have hfam : (fun l => PresheafOfModules.sections.eval
        (freeAssociatedSection S toOver K L hR hM e l) (op T)) =
      Scheme.Modules.freeTautologicalSection (toOver.obj T).hom L :=
    funext fun l => sections_eval_freeAssociatedSection_eq S toOver K L hR hM e T l
  refine (Stacks.PresheafOfModules.freeConstDesc_app_apply
    (R := (siteStructureSheaf S toOver K.toGrothendieck hR).obj)
    (freeAssociatedSection S toOver K L hR hM e) (op T) c).trans ?_
  rw [hfam]
  rfl

/-- **Step one of Tag 03OJ.** On a site of schemes over `S` satisfying the four conditions of
that tag — condition (2) being the Zariski-refinement hypothesis below, conditions (1) and (3)
the terminal object, and condition (1) also the essential smallness which supplies the
sheafification classes — the comparison morphism from the free sheaf of `𝒪`-modules on `L` to
the associated module of the free module `⊕_L 𝒪_S` on `S` **is an isomorphism**.

Both local conditions of
`Stacks.Sites.isIso_freeAssociatedComparison_of_zariskiRefinement_finsupp` are discharged here,
at the Zariski covering `Stacks.Sites.affineOpenImmersionPresieve` of the underlying scheme of
the object. Each arrow of its refinement by the site factors through an open immersion with
**affine** source, and over an affine scheme the sections of the pullback of `⊕_L 𝒪_S` are the
finitely supported families of regular functions
(`AlgebraicGeometry.Scheme.Modules.pullbackFreeSectionsEquiv`), matched with the tautological
sections by `AlgebraicGeometry.Scheme.Modules.pullbackFreeSectionsEquiv_eq`. The factorisation
is then pushed down the remaining arrow by
`AlgebraicGeometry.Scheme.Modules.pullbackSectionsMap_freeSectionsCombination`, which is where
the bridge of
`AlgebraicGeometry.Scheme.Modules.pullbackSectionsMap_freeTautologicalSection` is used. The
intermediate object is the affine source read as a scheme over `S`; it is an object of
`CategoryTheory.Over S` and need not be an object of the site, which is why the factorisation is
taken apart with `Stacks.Sites.pullbackSectionsMap_comp_any` rather than with functoriality of
the associated module. -/
public theorem isIso_freeAssociatedComparison
    (hZariski : ∀ (T : C) (R : Presieve ((toOver.obj T).left)),
      R ∈ Scheme.zariskiPrecoverage.{u} ((toOver.obj T).left) →
        ∃ Q : Presieve T, Q ∈ K T ∧
          Presieve.map (toOver ⋙ Over.forget S) Q ≤ (Sieve.generate R).arrows) :
    IsIso (freeAssociatedComparison S toOver K L hR hM e) := by
  refine isIso_freeAssociatedComparison_of_zariskiRefinement_finsupp S toOver K L hR hM e
    hZariski ?_ ?_
  · intro T s
    refine ⟨affineOpenImmersionPresieve (toOver.obj T).left,
      affineOpenImmersionPresieve_mem_zariskiPrecoverage _, ?_⟩
    rintro Z f ⟨U, h, ι, ⟨hιo, hUaff⟩, hfac⟩
    have : IsAffine (Over.mk (ι ≫ (toOver.obj T).hom)).left := hUaff
    obtain ⟨g, rfl, hg⟩ := exists_comp_homMk_pullbackSectionsMap (toOver.map f) h ι hfac
    obtain ⟨c₀, hc₀⟩ := (Scheme.Modules.pullbackFreeSectionsEquiv
      (Over.mk (ι ≫ (toOver.obj T).hom)).hom L).surjective
      (pullbackSectionsMap (SheafOfModules.free (R := S.ringCatSheaf) L)
        (Over.homMk ι rfl : Over.mk (ι ≫ (toOver.obj T).hom) ⟶ toOver.obj T) s)
    refine ⟨Finsupp.mapRange g.left.appTop (map_zero _) c₀, ?_⟩
    refine (freeAssociatedPresheafComparison_app S toOver K L hR hM e Z _).trans ?_
    refine (Scheme.Modules.pullbackSectionsMap_freeSectionsCombination L g c₀).symm.trans ?_
    refine (congrArg (fun z => pullbackSectionsMap
      (SheafOfModules.free (R := S.ringCatSheaf) L) g z)
      ((Scheme.Modules.pullbackFreeSectionsEquiv_eq
        (Over.mk (ι ≫ (toOver.obj T).hom)).hom L c₀).symm.trans hc₀)).trans ?_
    exact (hg _ s).symm.trans (siteAssociatedModule_map_apply _ toOver _ hR hM f s).symm
  · intro T x y hxy
    refine ⟨affineOpenImmersionPresieve (toOver.obj T).left,
      affineOpenImmersionPresieve_mem_zariskiPrecoverage _, ?_⟩
    rintro Z f ⟨U, h, ι, ⟨hιo, hUaff⟩, hfac⟩
    have : IsAffine (Over.mk (ι ≫ (toOver.obj T).hom)).left := hUaff
    have hT2 : ∀ z : L →₀ Γ((toOver.obj T).left, ⊤),
        pullbackSectionsMap (SheafOfModules.free (R := S.ringCatSheaf) L)
            (Over.homMk ι rfl : Over.mk (ι ≫ (toOver.obj T).hom) ⟶ toOver.obj T)
            (Scheme.Modules.freeSectionsCombination (toOver.obj T).hom L z) =
          Scheme.Modules.freeSectionsCombination
            (Over.mk (ι ≫ (toOver.obj T).hom)).hom L
            (Finsupp.mapRange ι.appTop (map_zero _) z) :=
      fun z => Scheme.Modules.pullbackSectionsMap_freeSectionsCombination L
        (Over.homMk ι rfl : Over.mk (ι ≫ (toOver.obj T).hom) ⟶ toOver.obj T) z
    have h1 : Scheme.Modules.freeSectionsCombination
          (Over.mk (ι ≫ (toOver.obj T).hom)).hom L
          (Finsupp.mapRange ι.appTop (map_zero _) x) =
        Scheme.Modules.freeSectionsCombination
          (Over.mk (ι ≫ (toOver.obj T).hom)).hom L
          (Finsupp.mapRange ι.appTop (map_zero _) y) :=
      (hT2 x).symm.trans
        ((congrArg (fun z => pullbackSectionsMap
              (SheafOfModules.free (R := S.ringCatSheaf) L)
              (Over.homMk ι rfl : Over.mk (ι ≫ (toOver.obj T).hom) ⟶ toOver.obj T) z)
            (((freeAssociatedPresheafComparison_app S toOver K L hR hM e T x).symm.trans
              hxy).trans
                (freeAssociatedPresheafComparison_app S toOver K L hR hM e T y))).trans
          (hT2 y))
    have h2 : Finsupp.mapRange ι.appTop (map_zero _) x =
        Finsupp.mapRange ι.appTop (map_zero _) y := by
      refine (Scheme.Modules.pullbackFreeSectionsEquiv
        (Over.mk (ι ≫ (toOver.obj T).hom)).hom L).injective ?_
      rw [Scheme.Modules.pullbackFreeSectionsEquiv_eq,
        Scheme.Modules.pullbackFreeSectionsEquiv_eq]
      exact h1
    have hfun : ∀ r : Γ((toOver.obj T).left, ⊤),
        ((siteStructureSheaf S toOver K.toGrothendieck hR).obj.map f.op) r =
          h.appTop (ι.appTop r) := by
      have hc : ((toOver ⋙ Over.forget S).map f).appTop = ι.appTop ≫ h.appTop := by
        rw [← hfac, Scheme.Hom.comp_appTop]
      intro r
      exact congr($hc r)
    have h3 : ∀ z : L →₀ Γ((toOver.obj T).left, ⊤),
        (Stacks.PresheafOfModules.freeConst
            (R := (siteStructureSheaf S toOver K.toGrothendieck hR).obj) L).map f.op z =
          Finsupp.mapRange h.appTop (map_zero _)
            (Finsupp.mapRange ι.appTop (map_zero _) z) := by
      intro z
      refine (Stacks.PresheafOfModules.freeConst_map_apply
        (R := (siteStructureSheaf S toOver K.toGrothendieck hR).obj) L f.op z).trans ?_
      refine Finsupp.ext fun l => ?_
      simp only
      exact hfun (z l)
    exact (h3 x).trans
      ((congrArg (Finsupp.mapRange (ConcreteCategory.hom h.appTop) (map_zero _)) h2).trans
        (h3 y).symm)

/-! ### Step two of Tag 03OJ: right exactness of `F ↦ Fᵃ` at a presentation -/

section StepTwo

omit [toOver.Full] [toOver.Faithful]

omit [EssentiallySmall.{u} C] in
/-- **The projection onto a cokernel of presheaves of modules is surjective on sections.**
Cokernels of presheaves of modules are computed objectwise
(`PresheafOfModules.Finite.evaluation_preservesFiniteColimits`), and an epimorphism of modules is
surjective. -/
public theorem _root_.Stacks.PresheafOfModules.surjective_cokernelπ_app
    {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {M N : PresheafOfModules.{u} R₀} (α : M ⟶ N) (X : Cᵒᵖ) :
    Function.Surjective ((cokernel.π α).app X) := by
  have h : Epi ((PresheafOfModules.evaluation R₀ X).map (cokernel.π α)) := inferInstance
  exact (ModuleCat.epi_iff_surjective _).1 h

variable {F G : S.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G)

omit [EssentiallySmall.{u} C] in
/-- **`F ↦ Fᵃ` carries a presentation to a complex.** The associated module of a morphism of
quasi-coherent modules on `S`, followed by the associated module of the projection onto its
cokernel, is zero. -/
public theorem associatedModuleMap_comp_cokernelπ :
    associatedModuleMap S toOver φ ≫ associatedModuleMap S toOver (cokernel.π φ) = 0 := by
  rw [← associatedModuleMap_comp, cokernel.condition, associatedModuleMap_zero]

/-- **The comparison morphism of step two of Tag 03OJ, at the level of presheaves of modules**:
from the cokernel of `Fᵃ ⟶ Gᵃ`, taken in the presheaves of modules on the site, to the
associated presheaf of modules of the cokernel of `F ⟶ G`.

This is the map the two Zariski-local conditions are checked on, and the sheaf-level comparison
is not: the cokernel in sheaves of modules is a sheafification of this one, so its sections over
an object of the site are not quotients of the sections of `Gᵃ`, exactly as the sections of a
free sheaf of modules are not finitely supported families. -/
public noncomputable def cokernelAssociatedPresheafComparison :
    cokernel (associatedModuleMap S toOver φ) ⟶
      associatedModulePresheaf S (cokernel φ) toOver :=
  cokernel.desc _ (associatedModuleMap S toOver (cokernel.π φ))
    (associatedModuleMap_comp_cokernelπ S toOver φ)

omit [EssentiallySmall.{u} C] in
/-- The defining property of the presheaf comparison of step two. -/
public theorem cokernelAssociatedPresheafComparison_π :
    cokernel.π (associatedModuleMap S toOver φ) ≫
        cokernelAssociatedPresheafComparison S toOver φ =
      associatedModuleMap S toOver (cokernel.π φ) :=
  cokernel.π_desc _ _ _

omit [EssentiallySmall.{u} C] in
/-- The presheaf comparison of step two, on a section of `Gᵃ` pushed into the cokernel: it is the
map on global sections of the pullback of `G ⟶ coker(φ)`. -/
public theorem cokernelAssociatedPresheafComparison_app_cokernelπ (T : C)
    (t : (associatedModulePresheaf S G toOver).obj (op T)) :
    (cokernelAssociatedPresheafComparison S toOver φ).app (op T)
        ((cokernel.π (associatedModuleMap S toOver φ)).app (op T) t) =
      (associatedModuleMap S toOver (cokernel.π φ)).app (op T) t :=
  congr($(congrArg (fun ψ => PresheafOfModules.Hom.app ψ (op T))
    (cokernel.π_desc (associatedModuleMap S toOver φ)
      (associatedModuleMap S toOver (cokernel.π φ))
      (associatedModuleMap_comp_cokernelπ S toOver φ))) t)

omit [EssentiallySmall.{u} C] in
/-- **The comparison morphism of step two is Zariski-locally surjective.** A section of the
associated presheaf of `coker(φ)` over an object of the site is, after restriction along the
arrows factoring through a member of the affine Zariski covering
`Stacks.Sites.affineOpenImmersionPresieve`, the image of a section of `Gᵃ`.

The affine input is `AlgebraicGeometry.Scheme.Modules.surjective_pullback_map_appTop_of_epi`, and
the factorisation condition (2) supplies is taken apart with
`Stacks.Sites.pullbackSectionsMap_comp_any` and
`AlgebraicGeometry.pullbackSectionsMap_naturality`, the intermediate affine object being an
object of `CategoryTheory.Over S` and in general not of the site. -/
public theorem isLocallySurjective_cokernelAssociatedPresheafComparison
    (hZariski : ∀ (T : C) (R : Presieve ((toOver.obj T).left)),
      R ∈ Scheme.zariskiPrecoverage.{u} ((toOver.obj T).left) →
        ∃ Q : Presieve T, Q ∈ K T ∧
          Presieve.map (toOver ⋙ Over.forget S) Q ≤ (Sieve.generate R).arrows) :
    Presheaf.IsLocallySurjective K.toGrothendieck
      ((PresheafOfModules.toPresheaf (structurePresheaf S toOver)).map
        (cokernelAssociatedPresheafComparison S toOver φ)) := by
  refine isLocallySurjective_of_zariskiRefinement S toOver K hZariski _ ?_
  intro T s
  refine ⟨affineOpenImmersionPresieve (toOver.obj T).left,
    affineOpenImmersionPresieve_mem_zariskiPrecoverage _, ?_⟩
  rintro Z f ⟨U, h, ι, ⟨hιo, hUaff⟩, hfac⟩
  have : IsAffine (Over.mk (ι ≫ (toOver.obj T).hom)).left := hUaff
  obtain ⟨g, rfl, hg⟩ := exists_comp_homMk_pullbackSectionsMap (toOver.map f) h ι hfac
  obtain ⟨t₀, ht₀⟩ := Scheme.Modules.surjective_pullback_map_appTop_of_epi
    (Over.mk (ι ≫ (toOver.obj T).hom)).hom (cokernel.π φ)
    (pullbackSectionsMap (cokernel φ)
      (Over.homMk ι rfl : Over.mk (ι ≫ (toOver.obj T).hom) ⟶ toOver.obj T) s)
  refine ⟨(cokernel.π (associatedModuleMap S toOver φ)).app (op Z) (pullbackSectionsMap G g t₀),
    ?_⟩
  refine (cokernelAssociatedPresheafComparison_app_cokernelπ S toOver φ Z _).trans ?_
  exact (congr($(pullbackSectionsMap_naturality (cokernel.π φ) g) t₀)).trans
    ((congrArg (fun z => pullbackSectionsMap (cokernel φ) g z) ht₀).trans
      (hg (cokernel φ) s).symm)

omit [EssentiallySmall.{u} C] in
/-- **The comparison morphism of step two is Zariski-locally injective.** Two sections of the
presheaf cokernel of `Fᵃ ⟶ Gᵃ` over an object of the site with the same image become equal after
restriction along the arrows factoring through a member of the affine Zariski covering
`Stacks.Sites.affineOpenImmersionPresieve`.

The affine input is
`AlgebraicGeometry.Scheme.Modules.exists_pullback_map_appTop_eq_of_cokernelπ_appTop_eq_zero`: the
two sections lift to sections of `Gᵃ` over the object, their difference dies in the sections of
the pullback of `coker(φ)`, and over an affine open it is therefore the image of a section of the
pullback of `F`. -/
public theorem isLocallyInjective_cokernelAssociatedPresheafComparison
    (hZariski : ∀ (T : C) (R : Presieve ((toOver.obj T).left)),
      R ∈ Scheme.zariskiPrecoverage.{u} ((toOver.obj T).left) →
        ∃ Q : Presieve T, Q ∈ K T ∧
          Presieve.map (toOver ⋙ Over.forget S) Q ≤ (Sieve.generate R).arrows) :
    Presheaf.IsLocallyInjective K.toGrothendieck
      ((PresheafOfModules.toPresheaf (structurePresheaf S toOver)).map
        (cokernelAssociatedPresheafComparison S toOver φ)) := by
  refine isLocallyInjective_of_zariskiRefinement S toOver K hZariski _ ?_
  intro T x y hxy
  have hxy' : (cokernelAssociatedPresheafComparison S toOver φ).app (op T) x =
      (cokernelAssociatedPresheafComparison S toOver φ).app (op T) y := hxy
  obtain ⟨x₁, hx₁⟩ := Stacks.PresheafOfModules.surjective_cokernelπ_app
    (associatedModuleMap S toOver φ) (op T) x
  obtain ⟨y₁, hy₁⟩ := Stacks.PresheafOfModules.surjective_cokernelπ_app
    (associatedModuleMap S toOver φ) (op T) y
  have hzero : (associatedModuleMap S toOver (cokernel.π φ)).app (op T) (x₁ - y₁) = 0 := by
    rw [map_sub, ← cokernelAssociatedPresheafComparison_app_cokernelπ S toOver φ T x₁,
      ← cokernelAssociatedPresheafComparison_app_cokernelπ S toOver φ T y₁, hx₁, hy₁, hxy',
      sub_self]
  refine ⟨affineOpenImmersionPresieve (toOver.obj T).left,
    affineOpenImmersionPresieve_mem_zariskiPrecoverage _, ?_⟩
  rintro Z f ⟨U, h, ι, ⟨hιo, hUaff⟩, hfac⟩
  have : IsAffine (Over.mk (ι ≫ (toOver.obj T).hom)).left := hUaff
  obtain ⟨g, rfl, hg⟩ := exists_comp_homMk_pullbackSectionsMap (toOver.map f) h ι hfac
  have hzeroU : ((Scheme.Modules.pullback
        (Over.mk (ι ≫ (toOver.obj T).hom)).hom).map (cokernel.π φ)).app ⊤
      (pullbackSectionsMap G
        (Over.homMk ι rfl : Over.mk (ι ≫ (toOver.obj T).hom) ⟶ toOver.obj T) (x₁ - y₁)) = 0 :=
    (congr($(pullbackSectionsMap_naturality (cokernel.π φ)
        (Over.homMk ι rfl : Over.mk (ι ≫ (toOver.obj T).hom) ⟶ toOver.obj T))
      (x₁ - y₁))).trans
      ((congrArg (fun z => pullbackSectionsMap (cokernel φ)
          (Over.homMk ι rfl : Over.mk (ι ≫ (toOver.obj T).hom) ⟶ toOver.obj T) z) hzero).trans
        (map_zero _))
  obtain ⟨s₀, hs₀⟩ :=
    Scheme.Modules.exists_pullback_map_appTop_eq_of_cokernelπ_appTop_eq_zero
      (Over.mk (ι ≫ (toOver.obj T).hom)).hom φ _ hzeroU
  have hpush : ((Scheme.Modules.pullback (toOver.obj Z).hom).map φ).app ⊤
        (pullbackSectionsMap F g s₀) = pullbackSectionsMap G (toOver.map f) (x₁ - y₁) :=
    (congr($(pullbackSectionsMap_naturality φ g) s₀)).trans
      ((congrArg (fun z => pullbackSectionsMap G g z) hs₀).trans (hg G _).symm)
  have hnatπ := fun z => NatTrans.naturality_apply
    ((PresheafOfModules.toPresheaf (structurePresheaf S toOver)).map
      (cokernel.π (associatedModuleMap S toOver φ))) f.op z
  have hx₁' : ((PresheafOfModules.toPresheaf (structurePresheaf S toOver)).map
      (cokernel.π (associatedModuleMap S toOver φ))).app (op T) x₁ = x := hx₁
  have hy₁' : ((PresheafOfModules.toPresheaf (structurePresheaf S toOver)).map
      (cokernel.π (associatedModuleMap S toOver φ))).app (op T) y₁ = y := hy₁
  have hker : (associatedPresheaf S G toOver).map f.op (x₁ - y₁) =
      ((PresheafOfModules.toPresheaf (structurePresheaf S toOver)).map
        (associatedModuleMap S toOver φ)).app (op Z)
        (pullbackSectionsMap F g s₀) :=
    (associatedPresheaf_map_apply G toOver f (x₁ - y₁)).trans hpush.symm
  have hz0 : (PresheafOfModules.toPresheaf (structurePresheaf S toOver)).map
        (associatedModuleMap S toOver φ) ≫
      (PresheafOfModules.toPresheaf (structurePresheaf S toOver)).map
        (cokernel.π (associatedModuleMap S toOver φ)) = 0 := by
    rw [← Functor.map_comp, cokernel.condition, Functor.map_zero]
  have hzeroZ : ((PresheafOfModules.toPresheaf (structurePresheaf S toOver)).map
      (cokernel.π (associatedModuleMap S toOver φ))).app (op Z)
      ((associatedPresheaf S G toOver).map f.op (x₁ - y₁)) = 0 :=
    (congrArg (fun w => ((PresheafOfModules.toPresheaf (structurePresheaf S toOver)).map
        (cokernel.π (associatedModuleMap S toOver φ))).app (op Z) w) hker).trans
      (congr($(congrArg (fun α => NatTrans.app α (op Z)) hz0) _))
  calc ((PresheafOfModules.toPresheaf (structurePresheaf S toOver)).obj
          (cokernel (associatedModuleMap S toOver φ))).map f.op x
      = ((PresheafOfModules.toPresheaf (structurePresheaf S toOver)).map
            (cokernel.π (associatedModuleMap S toOver φ))).app (op Z)
          ((associatedPresheaf S G toOver).map f.op x₁) := by
        rw [← hx₁']; exact (hnatπ x₁).symm
    _ = ((PresheafOfModules.toPresheaf (structurePresheaf S toOver)).map
            (cokernel.π (associatedModuleMap S toOver φ))).app (op Z)
          ((associatedPresheaf S G toOver).map f.op y₁) :=
        sub_eq_zero.1 (Eq.trans ((map_sub _ _ _).symm.trans
          (congrArg (fun w => ((PresheafOfModules.toPresheaf (structurePresheaf S toOver)).map
              (cokernel.π (associatedModuleMap S toOver φ))).app (op Z) w)
            (map_sub _ x₁ y₁).symm)) hzeroZ)
    _ = ((PresheafOfModules.toPresheaf (structurePresheaf S toOver)).obj
          (cokernel (associatedModuleMap S toOver φ))).map f.op y := by
        rw [← hy₁']; exact hnatπ y₁

/-! #### The comparison at the level of sheaves of modules -/

/-- Abelian presheaves on a small site of schemes over `S` admit a sheafification which preserves
finite limits. This is the strengthening of `Stacks.Sites.hasWeakSheafify_toGrothendieck` which
makes the sheaves of modules on the site an abelian category, and hence balanced, which is what
identifies the comparison of step two. -/
local instance hasSheafify_toGrothendieck :
    HasSheafify K.toGrothendieck AddCommGrpCat.{u} :=
  hasSheafify_addCommGrpCat_of_essentiallySmall.{u} _

variable (hF : Presheaf.IsSheaf K.toGrothendieck (associatedPresheaf S F toOver))
  (hG : Presheaf.IsSheaf K.toGrothendieck (associatedPresheaf S G toOver))
  (hH : Presheaf.IsSheaf K.toGrothendieck (associatedPresheaf S (cokernel φ) toOver))

/-- The morphism `Fᵃ ⟶ Gᵃ` of **sheaves** of modules on the site induced by a morphism of
quasi-coherent modules on `S`. Its underlying morphism of presheaves of modules is
`Stacks.Sites.associatedModuleMap`; both sheaf conditions are parameters, as for
`Stacks.Sites.siteAssociatedModule`. -/
public noncomputable def siteAssociatedModuleMap :
    siteAssociatedModule S F toOver K.toGrothendieck hR hF ⟶
      siteAssociatedModule S G toOver K.toGrothendieck hR hG :=
  ⟨associatedModuleMap S toOver φ⟩

omit [EssentiallySmall.{u} C] in
/-- `F ↦ Fᵃ` carries a presentation to a complex, at the level of sheaves of modules. -/
public theorem siteAssociatedModuleMap_comp_cokernelπ :
    siteAssociatedModuleMap S toOver K hR φ hF hG ≫
        siteAssociatedModuleMap S toOver K hR (cokernel.π φ) hG hH = 0 :=
  SheafOfModules.hom_ext (associatedModuleMap_comp_cokernelπ S toOver φ)

/-- **The comparison morphism of step two of Tag 03OJ**: from the cokernel of `Fᵃ ⟶ Gᵃ`, taken
in the sheaves of `𝒪`-modules on the site, to the associated module of the cokernel of
`F ⟶ G`.

Right exactness of `F ↦ Fᵃ` is the assertion that this morphism is an isomorphism, which is
`Stacks.Sites.isIso_cokernelAssociatedComparison`. The sheaf condition for the associated
presheaf of the cokernel is a further parameter, exactly as
`Stacks.Sites.siteAssociatedModule` needs one; nothing here sheafifies the sections. -/
public noncomputable def cokernelAssociatedComparison :
    cokernel (siteAssociatedModuleMap S toOver K hR φ hF hG) ⟶
      siteAssociatedModule S (cokernel φ) toOver K.toGrothendieck hR hH :=
  cokernel.desc _ (siteAssociatedModuleMap S toOver K hR (cokernel.π φ) hG hH)
    (siteAssociatedModuleMap_comp_cokernelπ S toOver K hR φ hF hG hH)

/-- The defining property of the comparison of step two. -/
public theorem cokernelAssociatedComparison_π :
    cokernel.π (siteAssociatedModuleMap S toOver K hR φ hF hG) ≫
        cokernelAssociatedComparison S toOver K hR φ hF hG hH =
      siteAssociatedModuleMap S toOver K hR (cokernel.π φ) hG hH :=
  cokernel.π_desc _ _ _

/-- The canonical morphism from the presheaf cokernel of `Fᵃ ⟶ Gᵃ` to the underlying presheaf of
modules of the sheaf cokernel. -/
private noncomputable def cokernelValDesc :
    cokernel (associatedModuleMap S toOver φ) ⟶
      (PresheafOfModules.restrictScalars
          (𝟙 (siteStructureSheaf S toOver K.toGrothendieck hR).obj)).obj
        ((SheafOfModules.forget (siteStructureSheaf S toOver K.toGrothendieck hR)).obj
          (cokernel (siteAssociatedModuleMap S toOver K hR φ hF hG))) :=
  cokernel.desc _
    ((SheafOfModules.forget (siteStructureSheaf S toOver K.toGrothendieck hR) ⋙
        PresheafOfModules.restrictScalars
          (𝟙 (siteStructureSheaf S toOver K.toGrothendieck hR).obj)).map
      (cokernel.π (siteAssociatedModuleMap S toOver K hR φ hF hG)))
    (by
      have h : (SheafOfModules.forget (siteStructureSheaf S toOver K.toGrothendieck hR) ⋙
              PresheafOfModules.restrictScalars
                (𝟙 (siteStructureSheaf S toOver K.toGrothendieck hR).obj)).map
            (siteAssociatedModuleMap S toOver K hR φ hF hG) ≫
          (SheafOfModules.forget (siteStructureSheaf S toOver K.toGrothendieck hR) ⋙
              PresheafOfModules.restrictScalars
                (𝟙 (siteStructureSheaf S toOver K.toGrothendieck hR).obj)).map
            (cokernel.π (siteAssociatedModuleMap S toOver K hR φ hF hG)) = 0 := by
        rw [← Functor.map_comp, cokernel.condition, Functor.map_zero]
      exact h)

private theorem cokernelValDesc_π :
    cokernel.π (associatedModuleMap S toOver φ) ≫ cokernelValDesc S toOver K hR φ hF hG =
      (SheafOfModules.forget (siteStructureSheaf S toOver K.toGrothendieck hR) ⋙
          PresheafOfModules.restrictScalars
            (𝟙 (siteStructureSheaf S toOver K.toGrothendieck hR).obj)).map
        (cokernel.π (siteAssociatedModuleMap S toOver K hR φ hF hG)) :=
  cokernel.π_desc _ _ _

/-- The transpose of `Stacks.Sites.cokernelValDesc`: the comparison from the sheafification of
the presheaf cokernel to the sheaf cokernel. -/
private noncomputable def sheafifyCokernelToCokernel :
    (PresheafOfModules.sheafification
          (𝟙 (siteStructureSheaf S toOver K.toGrothendieck hR).obj)).obj
        (cokernel (associatedModuleMap S toOver φ)) ⟶
      cokernel (siteAssociatedModuleMap S toOver K hR φ hF hG) :=
  (PresheafOfModules.sheafificationHomEquiv _).symm (cokernelValDesc S toOver K hR φ hF hG)

/-- **The sheaf cokernel is covered by the sheafification of the presheaf cokernel.** The
projection onto the sheaf cokernel factors through the comparison, so the comparison is an
epimorphism. -/
private theorem epi_sheafifyCokernelToCokernel :
    Epi (sheafifyCokernelToCokernel S toOver K hR φ hF hG) := by
  have hepi : Epi ((PresheafOfModules.sheafificationHomEquiv
      (𝟙 (siteStructureSheaf S toOver K.toGrothendieck hR).obj)).symm
      ((SheafOfModules.forget (siteStructureSheaf S toOver K.toGrothendieck hR) ⋙
          PresheafOfModules.restrictScalars
            (𝟙 (siteStructureSheaf S toOver K.toGrothendieck hR).obj)).map
        (cokernel.π (siteAssociatedModuleMap S toOver K hR φ hF hG)))) :=
    Stacks.SheafOfModules.epi_sheafificationHomEquiv_symm_forget_map _
  have hcomp := (Stacks.SheafOfModules.sheafificationHomEquiv_symm_comp
        (cokernel.π (associatedModuleMap S toOver φ))
        (cokernelValDesc S toOver K hR φ hF hG)).symm.trans
      (congrArg (PresheafOfModules.sheafificationHomEquiv
          (𝟙 (siteStructureSheaf S toOver K.toGrothendieck hR).obj)).symm
        (cokernelValDesc_π S toOver K hR φ hF hG))
  exact @epi_of_epi_fac _ _ _ _ _ _ _ _ hepi hcomp

/-- **Step two of Tag 03OJ: the functor `F ↦ Fᵃ` is right exact at a presentation.** On a site
of schemes over `S` whose Zariski coverings are refined by coverings of the site — condition (2)
of the tag — the comparison morphism from the cokernel of `Fᵃ ⟶ Gᵃ` to `coker(F ⟶ G)ᵃ` **is an
isomorphism**.

The content is the Zariski-local bijectivity of the *presheaf* comparison
`Stacks.Sites.cokernelAssociatedPresheafComparison`, whose two affine inputs are
`AlgebraicGeometry.Scheme.Modules.surjective_pullback_map_appTop_of_epi` and
`AlgebraicGeometry.Scheme.Modules.exists_pullback_map_appTop_eq_of_cokernelπ_appTop_eq_zero`.
That bijectivity makes the *transpose* of the presheaf comparison an isomorphism, by
`Stacks.SheafOfModules.isIso_sheafificationHomEquiv_symm_of_isLocallyBijective`. The remaining
step is that the sheafification of the presheaf cokernel is the sheaf cokernel: the comparison
`Stacks.Sites.sheafifyCokernelToCokernel` between them is an epimorphism because the projection
onto the sheaf cokernel factors through it, it is a monomorphism because composing it with the
comparison of step two gives the isomorphism above, and the sheaves of modules on the site are an
abelian category, hence balanced. -/
public theorem isIso_cokernelAssociatedComparison
    (hZariski : ∀ (T : C) (R : Presieve ((toOver.obj T).left)),
      R ∈ Scheme.zariskiPrecoverage.{u} ((toOver.obj T).left) →
        ∃ Q : Presieve T, Q ∈ K T ∧
          Presieve.map (toOver ⋙ Over.forget S) Q ≤ (Sieve.generate R).arrows) :
    IsIso (cokernelAssociatedComparison S toOver K hR φ hF hG hH) := by
  have hiso := Stacks.SheafOfModules.isIso_sheafificationHomEquiv_symm_of_isLocallyBijective
    (N := siteAssociatedModule S (cokernel φ) toOver K.toGrothendieck hR hH)
    (cokernelAssociatedPresheafComparison S toOver φ)
    (isLocallyInjective_cokernelAssociatedPresheafComparison S toOver K φ hZariski)
    (isLocallySurjective_cokernelAssociatedPresheafComparison S toOver K φ hZariski)
  have hpre : cokernelValDesc S toOver K hR φ hF hG ≫
      (SheafOfModules.forget (siteStructureSheaf S toOver K.toGrothendieck hR) ⋙
          PresheafOfModules.restrictScalars
            (𝟙 (siteStructureSheaf S toOver K.toGrothendieck hR).obj)).map
        (cokernelAssociatedComparison S toOver K hR φ hF hG hH) =
      cokernelAssociatedPresheafComparison S toOver φ := by
    refine (cancel_epi (cokernel.π (associatedModuleMap S toOver φ))).1 ?_
    exact ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun m => m ≫
            (SheafOfModules.forget (siteStructureSheaf S toOver K.toGrothendieck hR) ⋙
                PresheafOfModules.restrictScalars
                  (𝟙 (siteStructureSheaf S toOver K.toGrothendieck hR).obj)).map
              (cokernelAssociatedComparison S toOver K hR φ hF hG hH))
          (cokernelValDesc_π S toOver K hR φ hF hG)).trans
        ((Functor.map_comp _ _ _).symm.trans
          (congrArg ((SheafOfModules.forget
                (siteStructureSheaf S toOver K.toGrothendieck hR) ⋙
              PresheafOfModules.restrictScalars
                (𝟙 (siteStructureSheaf S toOver K.toGrothendieck hR).obj)).map)
            (cokernelAssociatedComparison_π S toOver K hR φ hF hG hH))))).trans
      (cokernelAssociatedPresheafComparison_π S toOver φ).symm
  have hfac := (Stacks.SheafOfModules.sheafificationHomEquiv_symm_comp_right
        (cokernelValDesc S toOver K hR φ hF hG)
        (cokernelAssociatedComparison S toOver K hR φ hF hG hH)).symm.trans
      (congrArg (PresheafOfModules.sheafificationHomEquiv
          (𝟙 (siteStructureSheaf S toOver K.toGrothendieck hR).obj)).symm hpre)
  have := epi_sheafifyCokernelToCokernel S toOver K hR φ hF hG
  have : IsIso (sheafifyCokernelToCokernel S toOver K hR φ hF hG ≫
      cokernelAssociatedComparison S toOver K hR φ hF hG hH) := hfac ▸ hiso
  have : Mono (sheafifyCokernelToCokernel S toOver K hR φ hF hG) :=
    mono_of_mono _ (cokernelAssociatedComparison S toOver K hR φ hF hG hH)
  have : IsIso (sheafifyCokernelToCokernel S toOver K hR φ hF hG) :=
    isIso_of_mono_of_epi _
  exact IsIso.of_isIso_comp_left (sheafifyCokernelToCokernel S toOver K hR φ hF hG) _

end StepTwo

/-! ### The free-source case of Descent, Lemma 0GN7 over an arbitrary base: the surjectivity half

-/

section FreeFullness

variable {N : S.Modules} [N.IsQuasicoherent]
  (hN : Presheaf.IsSheaf K.toGrothendieck (associatedPresheaf S N toOver))

/-- The comparison morphism of step one is the one which
`Stacks.Sites.freeHomEquivSiteAssociatedModule` matches with the inverse of
`AlgebraicGeometry.Scheme.Modules.pullbackFreeIso`. This is its definition read forwards. -/
public theorem freeHomEquivSiteAssociatedModule_freeAssociatedComparison :
    freeHomEquivSiteAssociatedModule S toOver (SheafOfModules.free (R := S.ringCatSheaf) L)
        K.toGrothendieck hR hM (isTerminalOfIsIsoHom S toOver e) L
        (freeAssociatedComparison S toOver K L hR hM e) =
      (Scheme.Modules.pullbackFreeIso (toOver.obj e).hom L).inv :=
  (freeHomEquivSiteAssociatedModule S toOver (SheafOfModules.free (R := S.ringCatSheaf) L)
    K.toGrothendieck hR hM (isTerminalOfIsIsoHom S toOver e) L).apply_symm_apply _

include e in
/-- **The surjectivity half of the free-source case of Descent, Lemma 0GN7, over an arbitrary
base.** On a site of schemes over `S` satisfying the four conditions of Tag 03OJ, every morphism
`(⊕_L 𝒪_S)ᵃ ⟶ Nᵃ` of sheaves of `𝒪`-modules on the site is the associated module of a morphism
`⊕_L 𝒪_S ⟶ N` of quasi-coherent modules on `S`.

This is the companion of the injectivity half
`Stacks.Sites.associatedModuleMap_injective_of_epi_free`, and like it the base is arbitrary: the
module which has to be generated by global sections is the free one, and it is. The proof reads
the given morphism off the terminal object through
`Stacks.Sites.freeHomEquivSiteAssociatedModule`, whose value at the comparison morphism of step
one is `Stacks.Sites.freeHomEquivSiteAssociatedModule_freeAssociatedComparison`; the resulting
morphism downstairs is pulled back to `S` by fullness of pullback along the invertible structure
morphism of the terminal object; and the two morphisms upstairs agree because they agree after
composing with the comparison morphism, which step one
(`Stacks.Sites.isIso_freeAssociatedComparison`) makes an isomorphism. The Zariski-refinement
condition (2) of the tag is used only there. -/
public theorem surjective_siteAssociatedModuleMap_free
    (hZariski : ∀ (T : C) (R : Presieve ((toOver.obj T).left)),
      R ∈ Scheme.zariskiPrecoverage.{u} ((toOver.obj T).left) →
        ∃ Q : Presieve T, Q ∈ K T ∧
          Presieve.map (toOver ⋙ Over.forget S) Q ≤ (Sieve.generate R).arrows) :
    Function.Surjective fun φ : SheafOfModules.free (R := S.ringCatSheaf) L ⟶ N =>
      siteAssociatedModuleMap S toOver K hR φ hM hN := by
  intro a
  have := isIso_freeAssociatedComparison S toOver K L hR hM e hZariski
  obtain ⟨φ, hφ⟩ := Functor.Full.map_surjective
    (F := Scheme.Modules.pullback (toOver.obj e).hom)
    ((Scheme.Modules.pullbackFreeIso (toOver.obj e).hom L).hom ≫
      freeHomEquivSiteAssociatedModule S toOver N K.toGrothendieck hR hN
        (isTerminalOfIsIsoHom S toOver e) L
        (freeAssociatedComparison S toOver K L hR hM e ≫ a))
  refine ⟨φ, (cancel_epi (freeAssociatedComparison S toOver K L hR hM e)).1 ?_⟩
  refine (freeHomEquivSiteAssociatedModule S toOver N K.toGrothendieck hR hN
    (isTerminalOfIsIsoHom S toOver e) L).injective ?_
  have hnat := freeHomEquivSiteAssociatedModule_comp S toOver K.toGrothendieck hR hM hN
    (isTerminalOfIsIsoHom S toOver e) L (siteAssociatedModuleMap S toOver K hR φ hM hN)
    ((Scheme.Modules.pullback (toOver.obj e).hom).map φ) (fun _ => rfl)
    (freeAssociatedComparison S toOver K L hR hM e)
  rw [hnat, freeHomEquivSiteAssociatedModule_freeAssociatedComparison, hφ]
  exact Iso.inv_hom_id_assoc _ _

include e hR hM hN in
/-- **The surjectivity half of the free-source case of Descent, Lemma 0GN7, at the level of
presheaves of modules.** Every morphism of the associated presheaves of modules out of the
associated presheaf of a free module is `φᵃ`.

The two statements are the same: a morphism of sheaves of modules on the site is a morphism of
the underlying presheaves of modules, so this is
`Stacks.Sites.surjective_siteAssociatedModuleMap_free` with the sheaf wrapper removed from both
sides. Together with `Stacks.Sites.associatedModuleMap_injective_of_epi_free`, whose generation
hypothesis the free module satisfies, this is Descent, Lemma 0GN7 for a free source over an
arbitrary base. -/
public theorem surjective_associatedModuleMap_free
    (hZariski : ∀ (T : C) (R : Presieve ((toOver.obj T).left)),
      R ∈ Scheme.zariskiPrecoverage.{u} ((toOver.obj T).left) →
        ∃ Q : Presieve T, Q ∈ K T ∧
          Presieve.map (toOver ⋙ Over.forget S) Q ≤ (Sieve.generate R).arrows) :
    Function.Surjective fun φ : SheafOfModules.free (R := S.ringCatSheaf) L ⟶ N =>
      associatedModuleMap S toOver φ := by
  intro a
  obtain ⟨φ, hφ⟩ := surjective_siteAssociatedModuleMap_free S toOver K L hR hM e hN hZariski
    (⟨a⟩ : siteAssociatedModule S (SheafOfModules.free (R := S.ringCatSheaf) L) toOver
        K.toGrothendieck hR hM ⟶ siteAssociatedModule S N toOver K.toGrothendieck hR hN)
  exact ⟨φ, congrArg (fun ψ : siteAssociatedModule S
      (SheafOfModules.free (R := S.ringCatSheaf) L) toOver K.toGrothendieck hR hM ⟶
        siteAssociatedModule S N toOver K.toGrothendieck hR hN => ψ.val) hφ⟩

/-- **A morphism of free sheaves of `𝒪`-modules on the site comes from a morphism of free modules
on `S`.** This is the form in which the surjectivity half is consumed by the essential
surjectivity of Tag 03OJ: a global presentation of a quasi-coherent module on the site is a map
of coproducts of copies of `𝒪` *on the site*, and what has to be produced downstairs is a map of
free modules on the base, compatibly with the two comparison morphisms of step one.

It is `Stacks.Sites.surjective_siteAssociatedModuleMap_free` at `N = ⊕_L 𝒪_S`, applied to the
given morphism conjugated by the two comparisons. -/
public theorem exists_siteAssociatedModuleMap_free_comp (L' : Type u)
    (hM' : Presheaf.IsSheaf K.toGrothendieck
      (associatedPresheaf S (SheafOfModules.free (R := S.ringCatSheaf) L') toOver))
    (hZariski : ∀ (T : C) (R : Presieve ((toOver.obj T).left)),
      R ∈ Scheme.zariskiPrecoverage.{u} ((toOver.obj T).left) →
        ∃ Q : Presieve T, Q ∈ K T ∧
          Presieve.map (toOver ⋙ Over.forget S) Q ≤ (Sieve.generate R).arrows)
    (α : SheafOfModules.free (R := siteStructureSheaf S toOver K.toGrothendieck hR) L' ⟶
      SheafOfModules.free (R := siteStructureSheaf S toOver K.toGrothendieck hR) L) :
    ∃ φ : SheafOfModules.free (R := S.ringCatSheaf) L' ⟶
        SheafOfModules.free (R := S.ringCatSheaf) L,
      freeAssociatedComparison S toOver K L' hR hM' e ≫
          siteAssociatedModuleMap S toOver K hR φ hM' hM =
        α ≫ freeAssociatedComparison S toOver K L hR hM e := by
  have := isIso_freeAssociatedComparison S toOver K L' hR hM' e hZariski
  obtain ⟨φ, hφ⟩ := surjective_siteAssociatedModuleMap_free S toOver K L' hR hM' e hM hZariski
    (inv (freeAssociatedComparison S toOver K L' hR hM' e) ≫ α ≫
      freeAssociatedComparison S toOver K L hR hM e)
  exact ⟨φ, (congrArg (fun m => freeAssociatedComparison S toOver K L' hR hM' e ≫ m) hφ).trans
    (IsIso.hom_inv_id_assoc _ _)⟩

end FreeFullness

end Stacks.Sites

end
