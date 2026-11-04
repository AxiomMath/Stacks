module

public import Mathlib.Algebra.Category.Grp.Abelian
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AbelianUnconditional
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineCohomologyVanishingUnconditional
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineLocalUnconditional
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.WeakSerreAcrossTopologies

/-!
# The derived category of adequate modules does not depend on the topology

Let `S` be a scheme and let `τ` and `τ'` be two of the five topologies `Zar`, `étale`, `smooth`,
`syntomic`, `fppf`, with `τ` stronger than `τ'`. The structure sheaf `𝒪` of the big `τ`-site over
`S` is also the structure sheaf of the big `τ'`-site on the same underlying category of schemes
over `S`, and the two derived categories `D_Adeq(𝒪_τ)` and `D_Adeq(𝒪_τ')` of complexes with
adequate cohomology are canonically isomorphic.

This is the comparison of derived categories of a weak Serre class across a change of topology,
applied to the class of adequate modules on the big site, to the collection of affine objects of
the site, and to the vanishing of the higher cohomology of an adequate module on an affine
object. At the level of the abelian categories the comparison is already available, and
`Adeq(𝒪_τ) ≌ Adeq(𝒪_τ')` is proved here outright.

## Main definitions

* `Stacks.Adequate.BigSite.Coarsening` — a coarser topology on the underlying category of a
  chosen big site, itself the topology of a chosen big site for another of the five topologies.
* `Stacks.Adequate.BigSite.Coarsening.restrict` — `ε_*`, an `𝒪`-module for `τ` read as an
  `𝒪`-module for `τ'`.
* `Stacks.Adequate.BigSite.derivedAdequate` — the subcategory `D_Adeq(𝒪)` of the derived
  category of `𝒪`-modules on a chosen big site cut out by adequacy of the cohomology.
* `Stacks.Adequate.BigSite.Coarsening.AdequateIsFineSheaf` and
  `Stacks.Adequate.BigSite.Coarsening.AffineCoarseCovering` — the two inputs about the pair of
  topologies that the library does not supply, named as explicit hypotheses.

## Main results

* `Stacks.Adequate.adequate_isWeakSerreClass` — the adequate `𝒪`-modules on a chosen big site
  form a weak Serre subcategory of all `𝒪`-modules on the site.
* `Stacks.Adequate.BigSite.Coarsening.adequate_site_eq_imageOfLE` — adequacy does not depend on
  the topology: the adequate `𝒪`-modules for the coarser topology are exactly the restrictions
  of the adequate `𝒪`-modules for the finer one.
* `Stacks.Adequate.BigSite.Coarsening.adequateEquivalence` — `Adeq(𝒪_τ) ≌ Adeq(𝒪_τ')`.
* `Stacks.Adequate.BigSite.Coarsening.derivedAdequateEquivalence` — **[Stacks, Tag 070V]**.

## Implementation notes

*The two topologies share their underlying category.* The source takes `𝒞 = (Sch/S)_fppf` and
puts both topologies on it. Here a `Stacks.Adequate.BigSite.Coarsening` of `B : BigSite τ S`
carries a second Grothendieck topology on `B.category` itself, so the chosen big `τ'`-site
`Stacks.Adequate.BigSite.Coarsening.site` it determines has the same cutoff, the same base
scheme and the same category as `B`, and the structure sheaves of the two sites have the same
underlying presheaf of rings — `Stacks.Adequate.BigSite.Coarsening.restrict` is
`CategoryTheory.SheafOfModules.ofLE` for the two topologies. The affine-section functors of a
module and of its restriction are then literally the same, which is what makes adequacy
transfer in both directions.

*Why the containment of the topologies is data.* "`τ` is stronger than `τ'`" is recorded as the
field `Stacks.Adequate.BigSite.Coarsening.le`, a containment of the two Grothendieck topologies
on the common category, rather than derived from an ordering of
`AlgebraicGeometry.CoveringTopology`. The library carries no ordering of the five big-site
topologies over a base scheme: of the chain `Zar ≤ étale ≤ smooth ≤ syntomic ≤ fppf` only
`AlgebraicGeometry.Scheme.zariskiTopology_le_grothendieckTopology` and the comparisons with
`fppf` and `fpqc` are available, and none of them is stated for the localized topologies
`BigZariskiOver.topology`, `BigEtaleOver.topology` and their companions that a chosen big site
actually carries. Both `τ` and `τ'` range over all five topologies, as in the source.

*What is assumed, and why.* Three inputs of the source's argument are named as explicit
hypotheses.

The hypothesis `comparison` of
`Stacks.Adequate.BigSite.Coarsening.derivedAdequateEquivalence` is the *second* conclusion of
[Stacks, Tag 07A8], the equivalence of the two derived categories of complexes with cohomology
in a weak Serre class. The first conclusion of that tag, that the image class is again weak
Serre, is
`Stacks.Cohomology.CompareTopologies.isWeakSerreClass_imageOfLE`, and the equivalence of the
abelian categories which the source's proof establishes first is
`Stacks.Cohomology.CompareTopologies.isEquivalence_liftPushforward`; both are available and the
second is used here. The derived statement is not: the source obtains it from Stacks 0D7W,
available as
`Stacks.Cohomology.CohomologicalDescent.derivedPullbackEquivalenceUnboundedRelative`, which is
stated for a flat morphism of ringed sites at `AlgebraicGeometry.RingedSite.{u, u, u}` —
objects and morphisms in a single universe — whereas the objects of a chosen big site lie one
universe above its morphisms, so it does not apply to `ε`. For a site whose objects and
morphisms do share a universe the whole argument is carried out in
`StacksFrontier/CategoryTheory/Sites/Cohomology/ChangeOfTopology/CoarseningDerivedEquivalence.lean`,
as `Stacks.Cohomology.CompareTopologies.derivedPullbackEquivalenceImageOfLE`; the universe gap
of a big site is the only thing in the way here. An equivalence of the two abelian
categories does not give it,
because the morphisms of `D_𝒜(𝒪_τ)` are computed in the ambient `Mod(𝒪_τ)` and agree with those
of `D_𝒜(𝒪_τ')` only by virtue of the acyclicity, which is exactly what `Rε_*` is needed for.
The hypothesis is written out in the generality of the source — an arbitrary site with two
comparable topologies, an arbitrary sheaf of rings for the finer one, an arbitrary weak Serre
class and an arbitrary collection of objects, with the image class spelled by
`Stacks.Cohomology.CompareTopologies.imageOfLE` — so that it is the general lemma of cohomology
on sites and not the statement about adequate modules in disguise, and it is *data*, a function
producing the equivalence from the three assumptions, so that nothing is chosen out of an
existence proof.

`Stacks.Adequate.BigSite.Coarsening.AdequateIsFineSheaf` is assumption (1) of [Stacks,
Tag 07A8] for the adequate modules: an adequate `𝒪`-module for the coarser topology is already
a sheaf for the finer one. It is what makes the image of the restriction functor on adequate
modules the whole of the adequate modules for the coarser topology, and so what lets the
conclusion be stated for `D_Adeq(𝒪_τ')` itself.

`Stacks.Adequate.BigSite.Coarsening.AffineCoarseCovering` is assumption (3), that every object
of the site is covered in the coarser topology by affine objects of the site. It is written in
the shape in which `Stacks.Cohomology.CompareTopologies.isWeakSerre_imageOfLE` carries the same
assumption, and there too it is a hypothesis rather than a conclusion. Reaching it from the
definition of a chosen big site needs an affine covering of an arbitrary — not necessarily
affine — object in the coarser topology, which is the affine open cover of the underlying
scheme read as a covering for that topology.

Assumption (2), that the adequate modules form a weak Serre subcategory, is proved here as
`Stacks.Adequate.adequate_isWeakSerreClass` from the clauses of [Stacks, Tag 06VQ], with no
hypothesis; the clauses are available for `𝒪`-modules with values in the universe of the site,
so the comparison is stated there. Assumption (4) is discharged outright from
`Stacks.Adequate.BigSite.isZero_rightDerived_sections_of_isAdequate`, which is
**[Stacks, Tag 06VM] (3)** and carries no hypothesis. Assumption (4) is phrased
with the cohomology of the underlying abelian sheaf, which is the source's own `H^p_τ(U, ℱ)`
and the form in which Tag 06VM (3) is available, rather than with the module-valued
`Stacks.Cohomology.moduleCohomology` which the first conclusion uses. The two are
compared by [Stacks, Tag 03FD], `ModuleSheafCohomology.sectionsComparisonIso`.

*The equivalence is of categories.* [Stacks, Tag 07A8] gives an equivalence of *triangulated*
categories. Only the underlying equivalence of categories is asserted here, which is the
assertion of the remark, that the two derived categories are canonically isomorphic.

## References

* [Stacks Project, Tag 070V](https://stacks.math.columbia.edu/tag/070V)
* [Stacks Project, Tag 07A8](https://stacks.math.columbia.edu/tag/07A8)
* [Stacks Project, Tag 06VM](https://stacks.math.columbia.edu/tag/06VM)
* [Stacks Project, Tag 06VQ](https://stacks.math.columbia.edu/tag/06VQ)
* [Stacks Project, Tag 06UP](https://stacks.math.columbia.edu/tag/06UP)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.ObjectProperty

universe v u

/-- Two equal object properties have equivalent full subcategories. -/
public def equivalenceOfEq {A : Type u} [Category.{v} A] {P Q : ObjectProperty A} (h : P = Q) :
    P.FullSubcategory ≌ Q.FullSubcategory := by
  subst h; exact Equivalence.refl

end CategoryTheory.ObjectProperty

namespace Stacks.Adequate

universe u m d

/-! ### A coarser topology on a chosen big site -/

/-- A coarser topology on the underlying category of a chosen big `τ`-site over `S`, which is
itself the topology of a chosen big `τ'`-site over `S`. -/
public structure BigSite.Coarsening {τ : CoveringTopology} {S : Scheme.{u}}
    (B : BigSite τ S) (τ' : CoveringTopology) where
  /-- The coarser Grothendieck topology, on the same underlying category. -/
  topology : GrothendieckTopology B.category
  /-- The coarser topology is contained in the finer one: `τ` is stronger than `τ'`. -/
  le : topology ≤ B.topology
  /-- The coarser topology is the one of the corresponding accepted big-site construction. -/
  chosen :
    (τ' = .zariski ∧ ∃ C : BigZariskiSite.{u},
      ∃ hS : C.Contains S, ∃ _e : C.schemeCardinal = B.cutoff,
        HEq topology (BigZariskiOver.topology C S hS)) ∨
    (τ' = .etale ∧ ∃ C : BigEtaleSite.{u},
      ∃ hS : C.Contains S, ∃ _e : C.cutoff = B.cutoff,
        HEq topology (BigEtaleOver.topology C S hS)) ∨
    (τ' = .fppf ∧ ∃ C : BigFppfSite.{u},
      ∃ hS : C.Contains S, ∃ _e : C.cutoff = B.cutoff,
        HEq topology (BigFppfOver.topology C S hS)) ∨
    (τ' = .smooth ∧ ∃ C : BigSmoothSite.{u},
      ∃ hS : S.size < C.cutoff, ∃ _e : C.cutoff = B.cutoff,
        HEq topology (BigSmoothOver.topology C S hS)) ∨
    (τ' = .syntomic ∧ ∃ C : BigSyntomicSite.{u},
      ∃ hS : C.Contains S, ∃ _e : C.cutoff = B.cutoff,
        HEq topology (BigSyntomicOver.topology C S hS))

namespace BigSite.Coarsening

variable {τ τ' : CoveringTopology} {S : Scheme.{u}} {B : BigSite τ S} (c : B.Coarsening τ')

/-- The chosen big `τ'`-site determined by a coarsening: the same cutoff, the same base scheme
and the same underlying category, with the coarser topology. -/
public abbrev site : BigSite τ' S where
  cutoff := B.cutoff
  base_mem := B.base_mem
  topology := c.topology
  isSheaf := B.isSheaf.of_le c.le
  chosen := c.chosen

/-- The chosen big `τ'`-site of a coarsening has the cutoff of the big `τ`-site. -/
public theorem site_cutoff : c.site.cutoff = B.cutoff := rfl

/-- The chosen big `τ'`-site of a coarsening carries the coarser topology. -/
public theorem site_topology : c.site.topology = c.topology := rfl

/-- `ε_*`: restriction of an `𝒪`-module from the finer to the coarser topology. This is
`CategoryTheory.SheafOfModules.ofLE` for the two topologies of the coarsening. -/
public abbrev restrict : SheafOfModules.{max u m} B.structureSheaf ⥤
    SheafOfModules.{max u m} c.site.structureSheaf :=
  SheafOfModules.ofLE.{u + 1, u, u, max u m} c.le B.structureSheaf

/-- The restriction `ε_*` of an `𝒪`-module has the same underlying presheaf of modules. -/
@[simp] public theorem restrict_obj_val (F : SheafOfModules.{max u m} B.structureSheaf) :
    ((restrict.{u, m} c).obj F).val = F.val := rfl

/-! ### The two inputs about the pair of topologies -/

/-- Assumption (1) of [Stacks, Tag 07A8] for the adequate modules: an adequate `𝒪`-module for
the coarser topology is already a sheaf for the finer one. -/
public abbrev AdequateIsFineSheaf : Prop :=
  ∀ G : SheafOfModules.{max u m} c.site.structureSheaf, IsAdequate c.site G →
    Presheaf.IsSheaf B.topology G.val.presheaf

/-- Assumption (3) of [Stacks, Tag 07A8] for the affine objects: every object of the site has a
covering for the coarser topology whose members are affine objects of the site. This is the
hypothesis `hB` of `Stacks.Cohomology.CompareTopologies.isWeakSerre_imageOfLE`, in the same
shape, at the coarser topology of the coarsening and the affine objects of the site. -/
public abbrev AffineCoarseCovering : Prop :=
  ∀ U : B.category, ∃ 𝒰 : PreZeroHypercover.{u + 1} U,
    𝒰.sieve₀ ∈ c.topology U ∧ ∀ i, B.affineObjects (𝒰.X i)

/-! ### Adequacy does not depend on the topology -/

/-- The restriction of an adequate `𝒪`-module to the coarser topology is adequate: the
affine-section functors of a module and of its restriction are the same, and adequacy of all of
them implies adequacy. -/
public theorem isAdequate_restrict
    (F : SheafOfModules.{max u m} B.structureSheaf) (hF : IsAdequate B F) :
    IsAdequate c.site ((restrict.{u, m} c).obj F) :=
  isAdequate_of_forall_affineSectionFunctor.{u, max u m} c.site _
    fun A f hA => affineLocalAdequacy.{u, m} B F hF A f hA

/-- An adequate `𝒪`-module for the coarser topology which is a sheaf for the finer topology is
an adequate `𝒪`-module for the finer topology. -/
public theorem isAdequate_of_isAdequate_site
    (G : SheafOfModules.{max u m} c.site.structureSheaf) (hG : IsAdequate c.site G)
    (hs : Presheaf.IsSheaf B.topology G.val.presheaf) :
    IsAdequate B (⟨G.val, hs⟩ : SheafOfModules.{max u m} B.structureSheaf) :=
  isAdequate_of_forall_affineSectionFunctor.{u, max u m} B _
    fun A f hA => affineLocalAdequacy.{u, m} c.site G hG A f hA

/-- **Adequacy does not depend on the topology:** the image under `ε_*` of the adequate
`𝒪`-modules for the finer topology is the class of adequate `𝒪`-modules for the coarser one. -/
public theorem adequate_site_eq_imageOfLE (hfine : AdequateIsFineSheaf.{u, m} c) :
    Stacks.Cohomology.CompareTopologies.imageOfLE.{u + 1, u, u, max u m} c.le B.structureSheaf
        (adequate.{u, max u m} B) = adequate.{u, max u m} c.site := by
  funext G
  refine propext ⟨?_, fun hG => ?_⟩
  · rintro ⟨F, hF, ⟨e⟩⟩
    exact (adequate.{u, max u m} c.site).prop_of_iso e (c.isAdequate_restrict F hF)
  · exact ⟨⟨G.val, hfine G hG⟩, c.isAdequate_of_isAdequate_site G hG _, ⟨Iso.refl _⟩⟩

/-- **`Adeq(𝒪_τ) ≌ Adeq(𝒪_τ')`.** The abelian categories of adequate `𝒪`-modules for the two
topologies are equivalent, through `ε_*`. This is the first paragraph of the proof of
[Stacks, Tag 07A8] read for the adequate modules: `ε_*` is fully faithful and its image on the
adequate modules for the finer topology is all of the adequate modules for the coarser one. -/
public def adequateEquivalence (hfine : AdequateIsFineSheaf.{u, m} c) :
    (adequate.{u, max u m} B).FullSubcategory ≌
      (adequate.{u, max u m} c.site).FullSubcategory :=
  letI := Stacks.Cohomology.CompareTopologies.isEquivalence_liftPushforward.{u + 1, u, u,
    max u m} c.le B.structureSheaf (adequate.{u, max u m} B)
  (Functor.asEquivalence
    ((Stacks.Cohomology.CompareTopologies.imageOfLE.{u + 1, u, u, max u m} c.le B.structureSheaf
          (adequate.{u, max u m} B)).lift
      ((adequate.{u, max u m} B).ι ⋙
        Stacks.Cohomology.CompareTopologies.pushforward.{u + 1, u, u, max u m} c.le
          B.structureSheaf)
      (fun M => Stacks.Cohomology.CompareTopologies.imageOfLE_pushforward_obj.{u + 1, u, u,
        max u m} c.le B.structureSheaf (adequate.{u, max u m} B) M.property))).trans
    (ObjectProperty.equivalenceOfEq (c.adequate_site_eq_imageOfLE hfine))

end BigSite.Coarsening

/-! ### The adequate modules are a weak Serre subcategory -/

variable {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S)

/-- The step of the source's proof of [Stacks, Tag 06VQ] (3) read for every short exact
sequence whose outer terms are adequate: the induced sequences of affine-section functors are
exact. It is a theorem, `Stacks.Adequate.adequateSectionsShortExact`, and also follows from the
vanishing of `H¹` on affines of [Stacks, Tag 06VM] by
`Stacks.Adequate.shortExact_affineSections_of_isAdequate`. -/
public abbrev AdequateSectionsShortExact : Prop :=
  ∀ T : ShortComplex (SheafOfModules.{max u m} B.structureSheaf), T.ShortExact →
    IsAdequate B T.X₁ → IsAdequate B T.X₃ →
    ∀ (A : CommRingCat.{u}) (f : Spec A ⟶ S), schemeSizeBelow B.cutoff (Spec A) →
      (T.map (affineSectionsFunctor.{u, max u m} B A f)).ShortExact

/-- **[Stacks, Tag 06VQ] in the packaging of [Stacks, Tag 0754].** The adequate `𝒪`-modules on
a chosen big `τ`-site over `S` form a weak Serre subcategory of all `𝒪`-modules on the site:
they contain the zero module and are closed under isomorphisms, kernels, cokernels and
extensions. These are clauses (1)–(3) of [Stacks, Tag 06VQ]. -/
public theorem adequate_isWeakSerreClass : (adequate.{u, u} B).IsWeakSerreClass :=
  let := adequate_isClosedUnderKernels.{u, u} B
  let := adequate_isClosedUnderCokernels.{u, u} B
  let := adequate_isClosedUnderExtensions B
  { }

section Sheafify

/-! ### The derived category of adequate modules -/

variable [HasDerivedCategory.{d} (SheafOfModules.{max u m} B.structureSheaf)]

/-- `D_Adeq(𝒪)`: the complexes of `𝒪`-modules on a chosen big site all of whose cohomology
modules are adequate, the subcategory `D_B(A)` of [Stacks, Tag 06UP] at the adequate modules. -/
public abbrev BigSite.derivedAdequate :
    ObjectProperty (DerivedCategory (SheafOfModules.{max u m} B.structureSheaf)) :=
  DerivedCategoryB.derivedCategoryB (adequate.{u, max u m} B)

end Sheafify

/-! ### The comparison of the two derived categories -/

namespace BigSite.Coarsening

variable {τ τ' : CoveringTopology} {S : Scheme.{u}} {B : BigSite τ S} (c : B.Coarsening τ')

/-- **[Stacks, Tag 070V].** Let `S` be a scheme and let `τ` and `τ'` be two of the five
topologies `Zar`, `étale`, `smooth`, `syntomic`, `fppf`, with `τ` stronger than `τ'`, and
denote `𝒪_τ` and `𝒪_τ'` the structure sheaf `𝒪` viewed as a sheaf on the big `τ`-site, resp.
the big `τ'`-site, over `S`. Then `D_Adeq(𝒪_τ)` and `D_Adeq(𝒪_τ')` are canonically isomorphic.

The equivalence is the second conclusion of [Stacks, Tag 07A8] applied to the class of adequate
`𝒪_τ`-modules and to the collection of affine objects of the site. Its assumption (2) is
`Stacks.Adequate.adequate_isWeakSerreClass` and its assumption (4) is
`Stacks.Adequate.BigSite.isZero_rightDerived_sections_of_isAdequate`, which is
[Stacks, Tag 06VM] (3) and carries no hypothesis; assumptions (1) and (3) are `hfine` and
`hcover`.
That the two sides are the derived categories of the *adequate* modules for each topology,
rather than of the adequate modules for `τ` and their image under `ε_*`, is
`Stacks.Adequate.BigSite.Coarsening.adequate_site_eq_imageOfLE`.

The inputs this declaration takes are: `comparison`, the second conclusion of [Stacks, Tag 07A8]
in the generality of its source, which this library does not prove; `AdequateIsFineSheaf` and
`AffineCoarseCovering`, assumptions (1) and (3) of 07A8 for the adequate modules and the affine
objects. Assumption (2) is discharged outright by [Stacks, Tag 06VQ], and assumption (4) by
[Stacks, Tag 06VM] (3). The modules have values in the universe of the site, the universe at
which [Stacks, Tag 06VQ] is available. -/
@[stacks 070V "the canonical isomorphism of `D_Adeq(𝒪_τ)` and `D_Adeq(𝒪_τ')` as an equivalence
of categories, for a coarsening of a chosen big site; the inputs it takes, and the one proved
here, are listed in the docstring"]
public def derivedAdequateEquivalence
    [HasSheafify c.topology AddCommGrpCat.{u}]
    [c.topology.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasDerivedCategory.{d} (SheafOfModules.{u} B.structureSheaf)]
    [HasDerivedCategory.{d} (SheafOfModules.{u} c.site.structureSheaf)]
    (comparison : ∀ {C : Type (u + 1)} [Category.{u} C] {J J' : GrothendieckTopology C}
      (h : J' ≤ J) (R : Sheaf J RingCat.{u})
      [HasSheafify J AddCommGrpCat.{u}]
      [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
      [HasSheafify J' AddCommGrpCat.{u}]
      [J'.WEqualsLocallyBijective AddCommGrpCat.{u}]
      [EnoughInjectives (Sheaf J AddCommGrpCat.{u})]
      [HasDerivedCategory.{d} (SheafOfModules.{u} R)]
      [HasDerivedCategory.{d} (SheafOfModules.{u} (R.ofLE h))]
      (A : ObjectProperty (SheafOfModules.{u} R)) (ℬ : Set C), A.IsWeakSerreClass →
        (∀ U : C, ∃ 𝒰 : PreZeroHypercover.{u + 1} U, 𝒰.sieve₀ ∈ J' U ∧ ∀ i, ℬ (𝒰.X i)) →
        (∀ U ∈ ℬ, ∀ p : ℕ, 0 < p → ∀ F, A F →
          IsZero ((((sheafSections J AddCommGrpCat.{u}).obj (op U)).rightDerived p).obj
            ((SheafOfModules.toSheaf R).obj F))) →
        ((DerivedCategoryB.derivedCategoryB A).FullSubcategory ≌
          (DerivedCategoryB.derivedCategoryB
            (Stacks.Cohomology.CompareTopologies.imageOfLE.{u + 1, u, u, u} h R
              A)).FullSubcategory))
    (hfine : AdequateIsFineSheaf.{u, u} c) (hcover : AffineCoarseCovering.{u} c) :
    (BigSite.derivedAdequate.{u, u, d} B).FullSubcategory ≌
      (BigSite.derivedAdequate.{u, u, d} c.site).FullSubcategory :=
  letI : HasDerivedCategory.{d} (SheafOfModules.{u} (B.structureSheaf.ofLE c.le)) :=
    (inferInstance : HasDerivedCategory.{d} (SheafOfModules.{u} c.site.structureSheaf))
  (comparison c.le B.structureSheaf (adequate.{u, u} B) B.affineObjects
      (adequate_isWeakSerreClass B) hcover
      (fun U hU p hp F hF =>
        haveI : IsAffine U.left.obj := hU
        B.isZero_rightDerived_sections_of_isAdequate.{u, u} F hF U p hp)).trans
    (ObjectProperty.equivalenceOfEq
      (congrArg DerivedCategoryB.derivedCategoryB
        (c.adequate_site_eq_imageOfLE hfine)))

end BigSite.Coarsening

end Stacks.Adequate

end
