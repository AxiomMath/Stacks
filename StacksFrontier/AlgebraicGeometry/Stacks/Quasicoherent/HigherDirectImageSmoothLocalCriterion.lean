module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageFlatBaseChangeDegrees
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageLocallyQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStack

/-!
# Higher direct images of locally quasi-coherent modules, by the criterion of Stacks 076Z

Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact (**Stacks 050U**) and quasi-separated (**Stacks 04YW**)
1-morphism of algebraic stacks over `S`.

* **Stacks 075Z** says that the higher direct image `Rⁱf_*ℱ`, computed in the étale topology, of a
  locally quasi-coherent `𝒪_𝒳`-module `ℱ` on `𝒳_étale` (**Stacks 06WJ**) is locally
  quasi-coherent on `𝒴_étale`, for every degree `i`.
* **Stacks 0765** says that if `ℱ` is moreover in `LQCoh^fbc(𝒪_𝒳)`, that is locally
  quasi-coherent *and* with the flat base change property (**Stacks 0762**), then every `Rⁱf_*ℱ`
  has the flat base change property.

The source deduces both from one criterion, **Stacks 076Z**, applied to two different rules
assigning to an algebraic stack a subcategory of its étale modules: the locally quasi-coherent
modules for **Stacks 075Z**, and `LQCoh^fbc` for **Stacks 0765**. This file formalizes that
criterion as a statement about an arbitrary such rule, states the four hypotheses it asks of the
rule, and derives both tags from it.

**Stacks 076Z itself is not proved here**, and neither are three of the four hypotheses it asks of
the two rules; they are carried as explicit, individually named hypotheses of the two theorems
below, each one a clause of the criterion at one of the rules and each one naming the tag of the
source it is. Hypothesis (2) of the criterion for local quasi-coherence *is* proved, from
**Stacks 06WL**, and with it the forward half of hypothesis (3) for that rule. The conclusions are
the conclusions of the two tags, at every degree and with the source's hypothesis sets unchanged:
nothing is weakened, and what is missing is missing in the open and in the shape the source would
supply it.

## Main definitions

* `AlgebraicGeometry.Stack.StackEtaleModuleRule`: a *rule* in the sense of **Stacks 076Z**, a
  predicate on the étale modules of a category fibred in groupoids over `S` presented by its
  structure functor.
* `AlgebraicGeometry.Stack.StackEtaleModuleRule.IsWeakSerre`,
  `AlgebraicGeometry.Stack.StackEtaleModuleRule.IsStableUnderSmoothPullback`,
  `AlgebraicGeometry.Stack.StackEtaleModuleRule.IsSmoothLocal` and
  `AlgebraicGeometry.Stack.StackEtaleModuleRule.PreservesHigherDirectImagesOfAffine`: hypotheses
  (1), (2), (3) and (4) of **Stacks 076Z**.
* `AlgebraicGeometry.Stack.StackEtaleModuleRule.IsSmoothLocalConverse`: the converse half of
  hypothesis (3), which is the half the source proves separately.
* `AlgebraicGeometry.Stack.StackEtaleModuleRule.PreservedBy` and
  `AlgebraicGeometry.Stack.StackEtaleModuleRule.PreservesHigherDirectImages`: the conclusion of
  **Stacks 076Z** at a single 1-morphism and in general.
* `AlgebraicGeometry.Stack.SmoothLocalHigherDirectImageCriterion`: **Stacks 076Z**, as a
  statement about every rule.
* `AlgebraicGeometry.Stack.locallyQuasicoherentRule`,
  `AlgebraicGeometry.Stack.flatBaseChangePropertyRule` and
  `AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangeRule`: the rules carrying local
  quasi-coherence, the flat base change property, and `LQCoh^fbc`.
* `AlgebraicGeometry.Stack.HasFlatBaseChangePropertyHigherDirectImage`: the assertion of
  **Stacks 0765** at a 1-morphism and a degree, the counterpart for the flat base change property
  of `AlgebraicGeometry.Stack.IsLocallyQuasicoherentHigherDirectImage`.

## Main results

* `AlgebraicGeometry.Stack.isStableUnderSmoothPullback_locallyQuasicoherentRule`: hypothesis (2)
  of **Stacks 076Z** for local quasi-coherence, which is **Stacks 06WL**.
* `AlgebraicGeometry.Stack.isSmoothLocal_locallyQuasicoherentRule`: hypothesis (3) of
  **Stacks 076Z** for local quasi-coherence, from its converse half.
* `AlgebraicGeometry.Stack.isLocallyQuasicoherent_moduleSheafHigherDirectImage`:
  **Stacks 075Z**, from the criterion and the three of its hypotheses this library does not have.
* `AlgebraicGeometry.Stack.hasFlatBaseChangePropertyUnivLE_moduleSheafHigherDirectImage`:
  **Stacks 0765**, likewise.

## Implementation notes

### A rule, and why the criterion is quantified over all of them

A rule is indexed not by an algebraic stack but by a pair `(p, hp)` consisting of a structure
functor `p : 𝒳 ⥤ (Sch/S)_{fppf}` and a proof that it is fibred in groupoids, with the objects of
`𝒳` in `Type (u + 1)` and its morphisms in `Type u`, which is the seating of
`AlgebraicGeometry.Stack.AlgebraicStacks`. The reason is the strict presentation of a 1-morphism:
the inverse image of a module along `g : 𝒵 ⟶ 𝒳` is a module over the structure sheaf of
`CatFiberedInGroupoids.homFunctor g.hom ⋙ 𝒳.val.val.p`, which is the structure functor of `𝒵`
only up to the propositional equality `CatFiberedInGroupoids.homFunctor_comp_p`, so a rule indexed
by stacks could not be applied to it without transport. Both presentations occur below, and the
indexing by `(p, hp)` is what lets each clause use whichever one its inputs are stated in.

The criterion is quantified over *every* rule. That is what makes carrying it as a hypothesis
honest: **Stacks 076Z** is a single statement about an arbitrary rule, and its instances at the two
rules of this file are **Stacks 075Z** and **Stacks 0765**, so a conditional form of either tag
with *its own* criterion as the hypothesis would assume what it claims. The implementation notes of
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/HigherDirectImageLocallyQuasicoherent.lean`
record that objection, and the quantification over rules is what answers it: the hypothesis
`hcrit` below is strictly more general than either conclusion, and the clause hypotheses are
statements about the two particular rules which are not about higher direct images along a general
quasi-compact quasi-separated 1-morphism at all — except hypothesis (4), which is about higher
direct images between stacks representable by affine schemes, the one case the criterion does not
reduce.

### The four hypotheses, and which of them this library has

Hypothesis (1), that the rule cuts out a weak Serre subcategory, is stated with
`CategoryTheory.ObjectProperty.IsWeakSerreClass` on the category of *sheaves* of modules, which is
`Mod(𝒳_étale, 𝒪_𝒳)` and the category the source works in; it is abelian at section universe
`u + 1` because the associated étale site of a category whose objects lie in `Type (u + 1)` and
whose morphisms lie in `Type u` is essentially small there, which is
`AlgebraicGeometry.Stack.hasSheafify_associatedTopology_of_category_succ` together with
`AlgebraicGeometry.Stack.wEqualsLocallyBijective_associatedTopology_of_category_succ`. For local
quasi-coherence this hypothesis is parts (1) to (3) of **Stacks 06WM**, which are proved, at the
section universe `u` of the schemes, in
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentClosure`
(`AlgebraicGeometry.Stack.locallyQuasicoherentModules_abelian` and
`AlgebraicGeometry.Stack.isLocallyQuasicoherent_twoOutOfThree`); the hypothesis here is read at
section universe `u + 1`. For `LQCoh^fbc` it is those together with part (2) of **Stacks 0764**.

That hypothesis is asked only of algebraic stacks, as in the source, rather than of every category
fibred in groupoids; and hypothesis (3) is asked only of families indexed by a type in one fixed
universe `s`, rather than of families indexed in every universe. Both readings are implied by
**Stacks 076Z** — the second is an instance of it — so carrying the criterion in this shape is
carrying no more than the source's lemma, while the clause hypotheses the two theorems below carry
are correspondingly no stronger than the results of the source they are.

Hypotheses (2) and (3) are stated for a sheaf of modules, as the source's are, but take the
inverse image at the level of presheaves of modules,
`AlgebraicGeometry.Stack.stackModulePresheafPullback`, since that is the inverse image
**Stacks 06WL** and **Stacks 075Y** are stated for and the one the flat base change property of
**Stacks 0762** is formulated with. For a rule which contains the étale sheaf condition — as both
rules here do, local quasi-coherence carrying it — the presheaf-level inverse image of a member is
again a sheaf, so this is no departure.

Hypothesis (2) for local quasi-coherence is **Stacks 06WL** and is *proved* below, with no
smoothness of the 1-morphism needed, by
`AlgebraicGeometry.Stack.isLocallyQuasicoherent_stackModulePresheafPullback`. For the flat base
change property it is part (1) of **Stacks 0764**, which is not available; the implementation notes
of `StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/FlatBaseChangePullback.lean` record what
its proof would need.

Hypothesis (3) is a biconditional whose forward half is hypothesis (2), so for local
quasi-coherence that half is proved; the content is the converse half, which for local
quasi-coherence is **Stacks 075Y** and for the flat base change property is part (3) of
**Stacks 0764**. **Stacks 075Y** is proved, as
`AlgebraicGeometry.Stack.isLocallyQuasicoherent_of_isSmooth_jointlySurjective`, but at section
universe `u` only: the étale-locality of quasi-coherence it ends with consumes **Stacks 03DN** at
equal section and scalar universes, whereas the higher direct images of this library produce
modules with sections in `u + 1`. So the converse half is carried here too, and what carrying it
asks for is a universe generalization of **Stacks 03DN** rather than a new theorem of the source.

Hypothesis (4) is the affine case. For local quasi-coherence the source proves it from
**Stacks 075P**, the identification of the restriction of `Rⁱf_*ℱ` along a chart with a small
étale higher direct image, and from **Stacks 0720**; for `LQCoh^fbc` from **Stacks 075P** again
together with **Stacks 073K**, the base change isomorphism for a cartesian square of algebraic
spaces. Of these, **Stacks 073K** is proved, in
`StacksFrontier/AlgebraicGeometry/Spaces/CohomologyFlatBaseChange.lean`; **Stacks 075P** is formalized
only as the cartesian square of algebraic spaces it produces, not as the cohomological
identification, which is **Stacks 075H** — formalized at abelian coefficients only — together with
**Stacks 075N**; and **Stacks 0720** is not formalized. Hypothesis (4) is therefore carried, at both
rules.

"Representable by an affine scheme" is read as being the algebraic stack
`AlgebraicGeometry.Stack.schemeStack` of an object of the big fppf site whose underlying scheme is
affine. Every stack representable by an affine scheme is 2-isomorphic to one of these, and a rule
satisfying hypothesis (1) is closed under isomorphism, so this is the source's hypothesis; it is
the reading which avoids quantifying over 2-isomorphisms inside a hypothesis that is in any case
carried.

### Degrees and universes

Both conclusions are for every degree `i`, which is what the source asserts. The flat base change
property is read at section universe `u + 1`, where the higher direct images live, by
`AlgebraicGeometry.Stack.HasFlatBaseChangePropertyUnivLE`; the comparison map of **Stacks 06WC**
that `AlgebraicGeometry.Stack.HasFlatBaseChangeProperty` is built from is pinned to `u`, and the
`UnivLE` variant exists precisely so that **Stacks 0765** can be stated at the universes of the
2-category of algebraic stacks. Accordingly
`AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangeRule` is the reading at that section
universe of `AlgebraicGeometry.Stack.IsLocallyQuasicoherentWithFlatBaseChange`, which is pinned
to `u`.

## References

* [Stacks Project, Tag 02MO](https://stacks.math.columbia.edu/tag/02MO)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 050U](https://stacks.math.columbia.edu/tag/050U)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 06WL](https://stacks.math.columbia.edu/tag/06WL)
* [Stacks Project, Tag 06WM](https://stacks.math.columbia.edu/tag/06WM)
* [Stacks Project, Tag 0720](https://stacks.math.columbia.edu/tag/0720)
* [Stacks Project, Tag 072G](https://stacks.math.columbia.edu/tag/072G)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 075H](https://stacks.math.columbia.edu/tag/075H)
* [Stacks Project, Tag 075N](https://stacks.math.columbia.edu/tag/075N)
* [Stacks Project, Tag 075P](https://stacks.math.columbia.edu/tag/075P)
* [Stacks Project, Tag 075Y](https://stacks.math.columbia.edu/tag/075Y)
* [Stacks Project, Tag 075Z](https://stacks.math.columbia.edu/tag/075Z)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 0764](https://stacks.math.columbia.edu/tag/0764)
* [Stacks Project, Tag 0765](https://stacks.math.columbia.edu/tag/0765)
* [Stacks Project, Tag 076Z](https://stacks.math.columbia.edu/tag/076Z)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u t s

namespace AlgebraicGeometry.Stack

/-- **A rule in the sense of Stacks 076Z.** A predicate on the modules on the étale site of a
category fibred in groupoids over `S`, presented by its structure functor `p` together with a
proof `hp` that `p` is fibred in groupoids, at the seating of the 2-category of algebraic stacks:
objects in `Type (u + 1)`, morphisms in `Type u`, module sections in `u + 1`.

The source's rule assigns to an algebraic stack a subcategory of `Mod(𝒳_étale, 𝒪_𝒳)`. The
indexing by the structure functor rather than by the stack is what lets the clauses below be
applied to the strict presentation of the source of a 1-morphism; see the implementation notes. -/
abbrev StackEtaleModuleRule (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :=
  ∀ {𝒳 : Type (u + 1)} [Category.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
      (hp : p.IsFiberedInGroupoids),
    PresheafOfModules.{u + 1} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj → Prop

namespace StackEtaleModuleRule

/-- **Hypothesis (1) of Stacks 076Z.** At every algebraic stack, the rule cuts out a weak Serre
subcategory (**Stacks 0754**, which is **Stacks 02MO** part (2)) of the category of sheaves of
modules on the étale site.

The quantification is over algebraic stacks, as the source's is, and not over every category
fibred in groupoids: **Stacks 06WM**, which is this hypothesis for local quasi-coherence, is
stated for an algebraic stack, so a rule asked to satisfy it everywhere would be asked for more
than the source provides.

The ambient category is the sheaves of modules, which is `Mod(𝒳_étale, 𝒪_𝒳)`; it is abelian at
section universe `u + 1` because the associated étale site of a category whose objects lie in
`Type (u + 1)` and whose morphisms lie in `Type u` is essentially small there. -/
noncomputable abbrev IsWeakSerre (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (M : StackEtaleModuleRule B S hS) : Prop :=
  ∀ 𝒳 : AlgebraicStacks.{u, t} B S hS,
    letI := hasSheafify_associatedTopology_of_category_succ B S hS 𝒳.val.val.p
    letI := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS 𝒳.val.val.p
    ObjectProperty.IsWeakSerreClass
      (C := SheafOfModules.{u + 1} (ringStructureSheafCore B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)))
      (fun F => M 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F.val)

/-- **Hypothesis (2) of Stacks 076Z.** The inverse image of a member of the rule along a smooth
1-morphism of algebraic stacks is again a member.

The inverse image is the one of presheaves of modules,
`AlgebraicGeometry.Stack.stackModulePresheafPullback`, over the strict presentation
`CatFiberedInGroupoids.homFunctor g.hom ⋙ 𝒳.val.val.p` of the structure functor of the source. -/
noncomputable abbrev IsStableUnderSmoothPullback (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (M : StackEtaleModuleRule B S hS) : Prop :=
  ∀ {𝒵 𝒳 : AlgebraicStacks.{u, t} B S hS} (g : 𝒵 ⟶ 𝒳), AlgebraicStacks.IsSmooth B S hS g →
    ∀ F : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)),
      M 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F.val →
        M (CatFiberedInGroupoids.homFunctor g.hom ⋙ 𝒳.val.val.p)
          (isFiberedInGroupoids_homFunctor_comp B S hS g.hom)
          ((stackModulePresheafPullback.{u, t, u + 1} B S hS g).obj F.val)

/-- **The converse half of hypothesis (3) of Stacks 076Z.** Let `f j : 𝒲 j ⟶ 𝒳` be a family of
smooth 1-morphisms of algebraic stacks over `S` whose images cover the points of `𝒳`, that is
`|𝒳| = ⋃ j, |f j|(|𝒲 j|)`. If every inverse image of a sheaf of modules on `𝒳_étale` is a member
of the rule, then so is the sheaf itself.

This is the half of the biconditional which is not hypothesis (2); it is the half the source proves
separately, as **Stacks 075Y** for local quasi-coherence and as part (3) of **Stacks 0764** for
the flat base change property. -/
noncomputable abbrev IsSmoothLocalConverse (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (M : StackEtaleModuleRule B S hS) : Prop :=
  ∀ {J : Type s} {𝒲 : J → AlgebraicStacks.{u, t} B S hS} {𝒳 : AlgebraicStacks.{u, t} B S hS}
      (f : ∀ j, 𝒲 j ⟶ 𝒳), (∀ j, AlgebraicStacks.IsSmooth B S hS (f j)) →
      (Set.univ : Set (AlgebraicStacks.points B S hS 𝒳)) =
        ⋃ j, Set.range (AlgebraicStacks.pointsMap B S hS (f j)) →
      ∀ F : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)),
        (∀ j, M (CatFiberedInGroupoids.homFunctor (f j).hom ⋙ 𝒳.val.val.p)
            (isFiberedInGroupoids_homFunctor_comp B S hS (f j).hom)
            ((stackModulePresheafPullback.{u, t, u + 1} B S hS (f j)).obj F.val)) →
          M 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F.val

/-- **Hypothesis (3) of Stacks 076Z.** Membership in the rule is local for a jointly surjective
family of smooth 1-morphisms: a sheaf of modules on `𝒳_étale` is a member if and only if every
inverse image along the family is.

The forward half is hypothesis (2) and the converse half is
`AlgebraicGeometry.Stack.StackEtaleModuleRule.IsSmoothLocalConverse`. -/
noncomputable abbrev IsSmoothLocal (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (M : StackEtaleModuleRule B S hS) : Prop :=
  ∀ {J : Type s} {𝒲 : J → AlgebraicStacks.{u, t} B S hS} {𝒳 : AlgebraicStacks.{u, t} B S hS}
      (f : ∀ j, 𝒲 j ⟶ 𝒳), (∀ j, AlgebraicStacks.IsSmooth B S hS (f j)) →
      (Set.univ : Set (AlgebraicStacks.points B S hS 𝒳)) =
        ⋃ j, Set.range (AlgebraicStacks.pointsMap B S hS (f j)) →
      ∀ F : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)),
        M 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F.val ↔
          ∀ j, M (CatFiberedInGroupoids.homFunctor (f j).hom ⋙ 𝒳.val.val.p)
            (isFiberedInGroupoids_homFunctor_comp B S hS (f j).hom)
            ((stackModulePresheafPullback.{u, t, u + 1} B S hS (f j)).obj F.val)

/-- **The conclusion of Stacks 076Z at a single 1-morphism and a single degree.** For
`f : 𝒳 ⟶ 𝒴` and `i : ℕ`, the higher direct image `Rⁱf_*`, computed in the étale topology, carries
members of the rule on `𝒳_étale` to members of the rule on `𝒴_étale`.

The source of `f` is presented strictly, its structure functor written as the morphism's functor
followed by the structure functor of the target, which is the shape the higher direct images of
**Stacks 06WE** are stated in; the two sheafification hypotheses of that construction are supplied
from `AlgebraicGeometry.Stack.hasSheafify_associatedTopology_of_category_succ` and
`AlgebraicGeometry.Stack.wEqualsLocallyBijective_associatedTopology_of_category_succ`. -/
noncomputable abbrev PreservedBy (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (M : StackEtaleModuleRule B S hS) {𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS} (f : 𝒳 ⟶ 𝒴)
    (i : ℕ) : Prop :=
  letI := hasSheafify_associatedTopology_of_category_succ B S hS
    (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
  letI := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS
    (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
  letI := hasSheafify_associatedTopology_of_category_succ B S hS 𝒴.val.val.p
  letI := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS 𝒴.val.val.p
  ∀ F : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS f.hom)
      (etaleTopology B) (etaleTopology_le_topology B)),
    M (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
        (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) F.val →
      M 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
        ((moduleSheafHigherDirectImage.{u, u + 1, u, u + 1, u} B S hS
          (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p) 𝒴.val.val.p
          (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) 𝒴.val.isFiberedInGroupoids
          (CatFiberedInGroupoids.homFunctor f.hom) rfl (etaleTopology B)
          (etaleTopology_le_topology B) i).obj F).val

/-- **Hypothesis (4) of Stacks 076Z.** For a 1-morphism between algebraic stacks representable by
affine schemes, the higher direct images carry the rule into the rule, in every degree.

Representability by an affine scheme is read as being `AlgebraicGeometry.Stack.schemeStack` of an
object of the big fppf site whose underlying scheme is affine; see the implementation notes. -/
noncomputable abbrev PreservesHigherDirectImagesOfAffine (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (M : StackEtaleModuleRule B S hS) : Prop :=
  ∀ (X Y : BigFppfOver B S hS), IsAffine X.left.1 → IsAffine Y.left.1 →
    ∀ (f : schemeStack.{u, t} B S hS X ⟶ schemeStack.{u, t} B S hS Y) (i : ℕ),
      PreservedBy B S hS M f i

/-- **The conclusion of Stacks 076Z.** For every quasi-compact (**Stacks 050U**) and
quasi-separated (**Stacks 04YW**) 1-morphism of algebraic stacks over `S`, the higher direct
images carry the rule into the rule, in every degree. -/
noncomputable abbrev PreservesHigherDirectImages (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (M : StackEtaleModuleRule B S hS) : Prop :=
  ∀ {𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS} (f : 𝒳 ⟶ 𝒴), IsQuasiCompactMorphism B S hS f →
    AlgebraicStacks.IsQuasiSeparated B S hS f → ∀ i : ℕ, PreservedBy B S hS M f i

end StackEtaleModuleRule

/-- **Stacks 076Z**, as a statement. Let `M` be a rule assigning to a category fibred in groupoids
over `S` a predicate on the modules on its étale site. If `M` cuts out a weak Serre subcategory
everywhere, is stable under inverse image along a smooth 1-morphism, is local for a jointly
surjective family of smooth 1-morphisms, and is preserved by the higher direct images between
algebraic stacks representable by affine schemes, then it is preserved by the higher direct images
along every quasi-compact and quasi-separated 1-morphism of algebraic stacks, in every degree.

**This is a definition and asserts nothing.** The source proves it by running the first-quadrant
spectral sequence of **Stacks 072G** along a smooth cover and iterating the device to improve the
representability of the source from a stack to an algebraic space, a scheme, a separated scheme
and finally an affine one, using the diagonals; that spectral sequence has no formalization here.
It is carried as a hypothesis by the two theorems below, and the quantification over rules is what
keeps that from assuming their conclusions; see the implementation notes. -/
noncomputable abbrev SmoothLocalHigherDirectImageCriterion (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) : Prop :=
  ∀ M : StackEtaleModuleRule B S hS,
    StackEtaleModuleRule.IsWeakSerre.{u, t} B S hS M →
    StackEtaleModuleRule.IsStableUnderSmoothPullback.{u, t} B S hS M →
    StackEtaleModuleRule.IsSmoothLocal.{u, t, s} B S hS M →
    StackEtaleModuleRule.PreservesHigherDirectImagesOfAffine.{u, t} B S hS M →
    StackEtaleModuleRule.PreservesHigherDirectImages.{u, t} B S hS M

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- **The rule of local quasi-coherence.** The rule in the sense of **Stacks 076Z** assigning to a
category fibred in groupoids the locally quasi-coherent modules of **Stacks 06WJ** on its étale
site. **Stacks 075Z** is the conclusion of the criterion at this rule. -/
noncomputable abbrev locallyQuasicoherentRule : StackEtaleModuleRule B S hS :=
  fun {𝒳 : Type (u + 1)} [Category.{u} 𝒳] p hp F => IsLocallyQuasicoherent B E h S hS p hp F

/-- **The rule of the flat base change property.** The rule in the sense of **Stacks 076Z**
assigning to a category fibred in groupoids the modules on its étale site with the flat base
change property of **Stacks 0762**, read at section universe `u + 1` by
`AlgebraicGeometry.Stack.HasFlatBaseChangePropertyUnivLE`.

The source does not use this rule on its own; it is here so that the halves of the clauses of the
criterion for `LQCoh^fbc` which concern the flat base change property — parts (1) and (3) of
**Stacks 0764** — can be named as clauses at a rule rather than written out. -/
noncomputable abbrev flatBaseChangePropertyRule : StackEtaleModuleRule B S hS :=
  fun {𝒳 : Type (u + 1)} [Category.{u} 𝒳] p hp F =>
    HasFlatBaseChangePropertyUnivLE B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) F

/-- **The rule `LQCoh^fbc`.** The rule in the sense of **Stacks 076Z** assigning to a category
fibred in groupoids the modules on its étale site which are locally quasi-coherent
(**Stacks 06WJ**) and have the flat base change property (**Stacks 0762**). **Stacks 0765** is the
flat base change half of the conclusion of the criterion at this rule.

This is the reading at section universe `u + 1` of
`AlgebraicGeometry.Stack.IsLocallyQuasicoherentWithFlatBaseChange`, which is pinned to the universe
`u` of the schemes by the comparison map of **Stacks 06WC**, while the higher direct images produce
modules with sections in `u + 1`. -/
noncomputable abbrev locallyQuasicoherentFlatBaseChangeRule : StackEtaleModuleRule B S hS :=
  fun {𝒳 : Type (u + 1)} [Category.{u} 𝒳] p hp F =>
    locallyQuasicoherentRule B E h S hS p hp F ∧ flatBaseChangePropertyRule B E h S hS p hp F

/-- **Hypothesis (2) of Stacks 076Z for local quasi-coherence**, which is **Stacks 06WL**: the
inverse image of a locally quasi-coherent module along a 1-morphism of algebraic stacks is locally
quasi-coherent. No smoothness of the 1-morphism is needed. -/
theorem isStableUnderSmoothPullback_locallyQuasicoherentRule :
    StackEtaleModuleRule.IsStableUnderSmoothPullback.{u, t} B S hS
      (locallyQuasicoherentRule B E h S hS) :=
  fun g _ F hF => isLocallyQuasicoherent_stackModulePresheafPullback B E h S hS g F.val hF

/-- **Hypothesis (3) of Stacks 076Z for local quasi-coherence**, granted its converse half. The
forward half is **Stacks 06WL**, which is
`AlgebraicGeometry.Stack.isStableUnderSmoothPullback_locallyQuasicoherentRule`; the converse half
is **Stacks 075Y**, which this library has at section universe `u` only and which is the hypothesis
here. -/
theorem isSmoothLocal_locallyQuasicoherentRule
    (hconv : StackEtaleModuleRule.IsSmoothLocalConverse.{u, t, s} B S hS
      (locallyQuasicoherentRule B E h S hS)) :
    StackEtaleModuleRule.IsSmoothLocal.{u, t, s} B S hS (locallyQuasicoherentRule B E h S hS) :=
  fun f hsmooth hjs F =>
    ⟨fun hF j => isStableUnderSmoothPullback_locallyQuasicoherentRule B E h S hS (f j)
      (hsmooth j) F hF, hconv f hsmooth hjs F⟩

/-- **Hypothesis (2) of Stacks 076Z for `LQCoh^fbc`**, granted the half of it which concerns the
flat base change property. That half is part (1) of **Stacks 0764**, the hypothesis `hfbc` here;
the local quasi-coherence half is **Stacks 06WL**. -/
theorem isStableUnderSmoothPullback_locallyQuasicoherentFlatBaseChangeRule
    (hfbc : StackEtaleModuleRule.IsStableUnderSmoothPullback.{u, t} B S hS
      (flatBaseChangePropertyRule B E h S hS)) :
    StackEtaleModuleRule.IsStableUnderSmoothPullback.{u, t} B S hS
      (locallyQuasicoherentFlatBaseChangeRule B E h S hS) :=
  fun g hg F hF =>
    ⟨isStableUnderSmoothPullback_locallyQuasicoherentRule B E h S hS g hg F hF.1,
      hfbc g hg F hF.2⟩

/-- **Hypothesis (3) of Stacks 076Z for `LQCoh^fbc`**, granted the two converse halves. The
converse half for local quasi-coherence is **Stacks 075Y** and the one for the flat base change
property is part (3) of **Stacks 0764**; the forward half is
`AlgebraicGeometry.Stack.isStableUnderSmoothPullback_locallyQuasicoherentFlatBaseChangeRule`. -/
theorem isSmoothLocal_locallyQuasicoherentFlatBaseChangeRule
    (hfbcPull : StackEtaleModuleRule.IsStableUnderSmoothPullback.{u, t} B S hS
      (flatBaseChangePropertyRule B E h S hS))
    (hconvLqc : StackEtaleModuleRule.IsSmoothLocalConverse.{u, t, s} B S hS
      (locallyQuasicoherentRule B E h S hS))
    (hconvFbc : StackEtaleModuleRule.IsSmoothLocalConverse.{u, t, s} B S hS
      (flatBaseChangePropertyRule B E h S hS)) :
    StackEtaleModuleRule.IsSmoothLocal.{u, t, s} B S hS
      (locallyQuasicoherentFlatBaseChangeRule B E h S hS) :=
  fun f hsmooth hjs F =>
    ⟨fun hF j => isStableUnderSmoothPullback_locallyQuasicoherentFlatBaseChangeRule
        B E h S hS hfbcPull (f j) (hsmooth j) F hF,
      fun hall => ⟨hconvLqc f hsmooth hjs F fun j => (hall j).1,
        hconvFbc f hsmooth hjs F fun j => (hall j).2⟩⟩

/-- **The assertion of Stacks 0765** at a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` and
a degree `i`: the higher direct image `Rⁱf_*ℱ`, computed in the étale topology, of a sheaf of
`𝒪_𝒳`-modules `ℱ` on `𝒳_étale` which is locally quasi-coherent (**Stacks 06WJ**) and has the flat
base change property (**Stacks 0762**) has the flat base change property.

Both hypotheses on `ℱ` are those of the source, and only the flat base change property is asserted
of `Rⁱf_*ℱ`; its local quasi-coherence is **Stacks 075Z**, which is
`AlgebraicGeometry.Stack.IsLocallyQuasicoherentHigherDirectImage`. The property is read at section
universe `u + 1`, where the higher direct images live. -/
noncomputable abbrev HasFlatBaseChangePropertyHigherDirectImage
    {𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS} (f : 𝒳 ⟶ 𝒴) (i : ℕ) : Prop :=
  letI := hasSheafify_associatedTopology_of_category_succ B S hS
    (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
  letI := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS
    (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
  letI := hasSheafify_associatedTopology_of_category_succ B S hS 𝒴.val.val.p
  letI := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS 𝒴.val.val.p
  ∀ ℱ : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS f.hom)
      (etaleTopology B) (etaleTopology_le_topology B)),
    IsLocallyQuasicoherent B E h S hS
        (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
        (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) ℱ.val →
      HasFlatBaseChangePropertyUnivLE B E h S hS
          (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
          (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) (etaleTopology B)
          (etaleTopology_le_topology B) ℱ.val →
        HasFlatBaseChangePropertyUnivLE B E h S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
          (etaleTopology B) (etaleTopology_le_topology B)
          ((moduleSheafHigherDirectImage.{u, u + 1, u, u + 1, u} B S hS
            (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p) 𝒴.val.val.p
            (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) 𝒴.val.isFiberedInGroupoids
            (CatFiberedInGroupoids.homFunctor f.hom) rfl (etaleTopology B)
            (etaleTopology_le_topology B) i).obj ℱ).val

/-- **Stacks 075Z.** Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact (**Stacks 050U**) and quasi-separated
(**Stacks 04YW**) 1-morphism of algebraic stacks over `S` and let `ℱ` be a locally quasi-coherent
`𝒪_𝒳`-module on `𝒳_étale` (**Stacks 06WJ**). Then the higher direct image `Rⁱf_*ℱ`, computed in
the étale topology, is locally quasi-coherent on `𝒴_étale`, in every degree `i`.

The conclusion is `AlgebraicGeometry.Stack.IsLocallyQuasicoherentHigherDirectImage`, the
library's statement of the assertion of the source, unchanged and for every degree.

Three hypotheses are carried, each a clause of the criterion of **Stacks 076Z** at the rule of
local quasi-coherence and each one a result of the source this library does not have:

* `hcrit` is **Stacks 076Z**, quantified over every rule. Its proof runs the first-quadrant
  spectral sequence of **Stacks 072G**, which is not formalized here.
* `hserre` is hypothesis (1), the weak Serre condition, which is parts (1) to (3) of
  **Stacks 06WM**, proved at section universe `u` in
  `StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentClosure`; here it is
  read at section universe `u + 1`.
* `hconv` is the converse half of hypothesis (3), which is **Stacks 075Y**. That tag is proved, at
  section universe `u` only, and the higher direct images produce modules with sections in
  `u + 1`; closing this gap is a universe generalization of **Stacks 03DN**, not a new theorem of
  the source.
* `haffine` is hypothesis (4), the case of stacks representable by affine schemes, which the
  source proves from **Stacks 075P** and **Stacks 0720**; the cohomological content of
  **Stacks 075P** and all of **Stacks 0720** are absent.

Hypothesis (2) is not carried: it is **Stacks 06WL** and is supplied by
`AlgebraicGeometry.Stack.isStableUnderSmoothPullback_locallyQuasicoherentRule`, which also supplies
the forward half of hypothesis (3). -/
@[stacks 075Z "the whole statement, in every degree and with the source's hypotheses unweakened, \
  granted four named hypotheses: the criterion of Stacks 076Z quantified over every rule, the \
  weak Serre condition of Stacks 06WM parts (1)-(3), the converse half of the smooth-local \
  criterion Stacks 075Y at section universe u+1, and the affine case (Stacks 075P and \
  Stacks 0720). Hypothesis (2) of the criterion, Stacks 06WL, is proved rather than assumed"]
theorem isLocallyQuasicoherent_moduleSheafHigherDirectImage
    (hcrit : SmoothLocalHigherDirectImageCriterion.{u, t, s} B S hS)
    (hserre : StackEtaleModuleRule.IsWeakSerre.{u, t} B S hS (locallyQuasicoherentRule B E h S hS))
    (hconv : StackEtaleModuleRule.IsSmoothLocalConverse.{u, t, s} B S hS
      (locallyQuasicoherentRule B E h S hS))
    (haffine : StackEtaleModuleRule.PreservesHigherDirectImagesOfAffine.{u, t} B S hS
      (locallyQuasicoherentRule B E h S hS))
    {𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hqc : IsQuasiCompactMorphism B S hS f)
    (hqs : AlgebraicStacks.IsQuasiSeparated B S hS f) (i : ℕ) :
    IsLocallyQuasicoherentHigherDirectImage B E h S hS f i :=
  hcrit (locallyQuasicoherentRule B E h S hS) hserre
    (isStableUnderSmoothPullback_locallyQuasicoherentRule B E h S hS)
    (isSmoothLocal_locallyQuasicoherentRule B E h S hS hconv) haffine f hqc hqs i

/-- **Stacks 0765.** Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact (**Stacks 050U**) and quasi-separated
(**Stacks 04YW**) 1-morphism of algebraic stacks over `S` and let `ℱ` be a sheaf of `𝒪_𝒳`-modules
on `𝒳_étale` which is locally quasi-coherent (**Stacks 06WJ**) and has the flat base change
property (**Stacks 0762**). Then every higher direct image `Rⁱf_*ℱ`, computed in the étale
topology, has the flat base change property.

The conclusion is `AlgebraicGeometry.Stack.HasFlatBaseChangePropertyHigherDirectImage`: both
hypotheses on `ℱ` are the source's, the conclusion is about the flat base change property alone as
in the source, and it holds in every degree.

The route is the source's: the criterion of **Stacks 076Z** at the rule `LQCoh^fbc`, whose
conclusion gives local quasi-coherence of `Rⁱf_*ℱ` — which is **Stacks 075Z** — and the flat base
change property, of which only the latter is asserted. Five hypotheses are carried, each a clause
of that criterion at `LQCoh^fbc` or at the flat base change property alone, and each a result of
the source this library does not have:

* `hcrit` is **Stacks 076Z**, quantified over every rule.
* `hserre` is hypothesis (1) for `LQCoh^fbc`, which is parts (1) to (3) of **Stacks 06WM**
  together with part (2) of **Stacks 0764**.
* `hfbcPull` is the flat base change half of hypothesis (2), which is part (1) of **Stacks 0764**;
  its local quasi-coherence half is **Stacks 06WL** and is proved.
* `hconvLqc` and `hconvFbc` are the two halves of the converse of hypothesis (3), namely
  **Stacks 075Y** at section universe `u + 1` and part (3) of **Stacks 0764**.
* `haffine` is hypothesis (4) for `LQCoh^fbc`, which the source proves from **Stacks 075P** and
  **Stacks 073K**; **Stacks 073K** is proved but the cohomological content of **Stacks 075P** is
  not. -/
@[stacks 0765 "the whole statement, in every degree and with the source's hypotheses \
  unweakened, granted six named hypotheses: Stacks 076Z quantified over every rule; the weak \
  Serre condition for LQCoh^fbc (Stacks 06WM (1)-(3), Stacks 0764 (2)); Stacks 0764 (1) and (3); \
  Stacks 075Y at section universe u+1; and the affine case (Stacks 075P, Stacks 073K)"]
theorem hasFlatBaseChangePropertyUnivLE_moduleSheafHigherDirectImage
    (hcrit : SmoothLocalHigherDirectImageCriterion.{u, t, s} B S hS)
    (hserre : StackEtaleModuleRule.IsWeakSerre.{u, t} B S hS
      (locallyQuasicoherentFlatBaseChangeRule B E h S hS))
    (hfbcPull : StackEtaleModuleRule.IsStableUnderSmoothPullback.{u, t} B S hS
      (flatBaseChangePropertyRule B E h S hS))
    (hconvLqc : StackEtaleModuleRule.IsSmoothLocalConverse.{u, t, s} B S hS
      (locallyQuasicoherentRule B E h S hS))
    (hconvFbc : StackEtaleModuleRule.IsSmoothLocalConverse.{u, t, s} B S hS
      (flatBaseChangePropertyRule B E h S hS))
    (haffine : StackEtaleModuleRule.PreservesHigherDirectImagesOfAffine.{u, t} B S hS
      (locallyQuasicoherentFlatBaseChangeRule B E h S hS))
    {𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hqc : IsQuasiCompactMorphism B S hS f)
    (hqs : AlgebraicStacks.IsQuasiSeparated B S hS f) (i : ℕ) :
    HasFlatBaseChangePropertyHigherDirectImage B E h S hS f i :=
  fun ℱ hlqc hfbc =>
    (hcrit (locallyQuasicoherentFlatBaseChangeRule B E h S hS) hserre
      (isStableUnderSmoothPullback_locallyQuasicoherentFlatBaseChangeRule B E h S hS hfbcPull)
      (isSmoothLocal_locallyQuasicoherentFlatBaseChangeRule B E h S hS hfbcPull hconvLqc hconvFbc)
      haffine f hqc hqs i ℱ ⟨hlqc, hfbc⟩).2

end AlgebraicGeometry.Stack

end
