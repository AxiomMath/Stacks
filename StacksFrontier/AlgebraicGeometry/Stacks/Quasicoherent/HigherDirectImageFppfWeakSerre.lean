module

public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsToWeakSerreFirstQuadrant
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuleSheafHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Modules
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BaseSites
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Surjective
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.Criterion

/-!
# Higher direct images of a smooth-local weak Serre class on the fppf site (Stacks 0770)

**Stacks 0770** is a criterion. Let `M` be a rule assigning to every algebraic stack `𝒳` over a
base scheme `S` a subcategory `M_𝒳` of `Mod(𝒪_𝒳)`, the modules on the *fppf* site of `𝒳`
(**Stacks 06WB**), and suppose

1. `M_𝒳` is a weak Serre subcategory of `Mod(𝒪_𝒳)` (**Stacks 02MO**, **Stacks 0754**) for every
   algebraic stack `𝒳`;
2. for a smooth 1-morphism `f : 𝒳 ⟶ 𝒴` the inverse image `f^*` maps `M_𝒴` into `M_𝒳`;
3. `M` is smooth-local: for a family of smooth 1-morphisms `f j : 𝒳 j ⟶ 𝒴` with
   `|𝒴| = ⋃ j |f j|(|𝒳 j|)`, an object `F` of `Mod(𝒪_𝒴)` lies in `M_𝒴` if and only if every
   `(f j)^* F` lies in `M_{𝒳 j}`; and
4. for a 1-morphism `f : 𝒳 ⟶ 𝒴` of stacks *representable by affine schemes*, `Rⁱf_*` maps `M_𝒳`
   into `M_𝒴`.

Then `Rⁱf_*` maps `M_𝒳` into `M_𝒴` for every quasi-compact and quasi-separated `f : 𝒳 ⟶ 𝒴`
(**Stacks 050U**, **Stacks 04YW**). Clause (4), the affine case, is a *hypothesis* of the
statement; nothing below proves it or needs it proved. The mathematical content the criterion
asks for is the **reduction** of the general quasi-compact quasi-separated case to that affine
case, and that reduction is what this file formalizes and proves.

The source's proof of **Stacks 0770** is the proof of **Stacks 076Z** verbatim — the same
argument read in the fppf topology rather than the étale one — and it runs in two moves. First,
choose a smooth surjective presentation of the target by affine schemes; higher direct images
commute with that base change (**Stacks 075H**), the pullback of `F` to each base-changed source
stays in `M` by (2) because the projection is a base change of a smooth 1-morphism
(**Stacks 075W**), and (3) then lets the question be transported to the base-changed
1-morphisms, whose targets are representable by affine schemes. Second, over an affine target,
quasi-compactness of `f` makes the source quasi-compact, so it too has a smooth surjective
presentation by an affine scheme `g : 𝒱 ⟶ 𝒳`; the relative Čech pushforward spectral sequence of
that presentation (**Stacks 072G**, part (2) for the fppf topology) has
`E₂^{p,q} = R^q(f ∘ g_p)_* g_p^* F` with `g_p` the degree-`p` term of the Čech nerve, each
`𝒱_p` representable by an affine scheme, so (2) and (4) put every `E₂` term in `M_𝒴` and (1)
carries that to the abutment `R^{p+q} f_* F` by **Stacks 0132** part (4).

Both moves are proved here in full, as
`AlgebraicGeometry.Stack.AlgebraicStacks.higherDirectImagesMapInto_of_smoothAffineCover` and
`AlgebraicGeometry.Stack.AlgebraicStacks.higherDirectImagesMapInto_of_abutsTo`, and they are
composed into the statement of the criterion. The two geometric inputs the moves consume — the
base-changed presentation with its base-change isomorphisms, and the Čech spectral sequence over
an affine target — are carried as named hypotheses; see the implementation notes, which say which
tag each is.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.fppfModules`: `Mod(𝒪_𝒳)` for an algebraic stack,
  the modules of **Stacks 06WB** on the fppf site at the section universe the higher direct
  images of this library produce.
* `AlgebraicGeometry.Stack.AlgebraicStacks.fppfModulePullback` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.fppfHigherDirectImage`: the inverse image `f^*` of
  **Stacks 06WE** and the higher direct image `Rⁱf_*` for a 1-morphism of algebraic stacks.
* `AlgebraicGeometry.Stack.AlgebraicStacks.IsAffineRepresentable`: an algebraic stack
  representable by an affine scheme over the base.
* `AlgebraicGeometry.Stack.AlgebraicStacks.ModuleRule`,
  `AlgebraicGeometry.Stack.AlgebraicStacks.HigherDirectImagesMapInto`,
  `AlgebraicGeometry.Stack.AlgebraicStacks.IsSmoothPullbackStable`,
  `AlgebraicGeometry.Stack.AlgebraicStacks.IsSmoothLocal` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.AffineHigherDirectImagesMapInto`: the rule `M` of
  **Stacks 0770**, its conclusion at one 1-morphism, and clauses (2), (3) and (4) of its
  hypothesis.
* `AlgebraicGeometry.Stack.AlgebraicStacks.HasSmoothAffineBaseChange` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.HasFppfCechPresentation`: the two geometric
  prerequisites of the source's proof, **Stacks 075H** and **Stacks 072G** part (2), as
  propositions about a single 1-morphism.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.higherDirectImagesMapInto_of_smoothAffineCover`: the
  first move of the source's proof — the conclusion descends along a smooth jointly surjective
  cover of the target, given the base-change isomorphisms.
* `AlgebraicGeometry.Stack.AlgebraicStacks.higherDirectImagesMapInto_of_abutsTo`: the second
  move — over an affine-representable target, a first-quadrant spectral sequence whose `E₂` page
  is the higher direct images along a smooth affine presentation of the source puts the abutment
  in `M`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.higherDirectImage_mem_of_quasiCompact_quasiSeparated`:
  **Stacks 0770**, the criterion itself, from its four hypotheses together with the two named
  prerequisites.
* `AlgebraicGeometry.Stack.AlgebraicStacks.hasSheafify_fppfAssociatedTopology` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.wEqualsLocallyBijective_fppfAssociatedTopology`: the
  two sheafification conditions under which the higher direct images of modules exist hold at
  the seating of the 2-category of algebraic stacks, for the fppf topology.

## Implementation notes

The fppf topology enters as `B.topology` itself, which is the value of
`AlgebraicGeometry.BigFppfSite.baseTopology` at `AlgebraicGeometry.SiteKind.fppf` by definition;
the higher direct images of `AlgebraicGeometry.Stack.moduleSheafHigherDirectImage` are
parameterised not by a `SiteKind` but by an arbitrary topology on the common category of schemes
together with a proof that it is coarser than the fppf one, and `le_rfl` discharges that here.
Tag 076Z is the same statement for `AlgebraicGeometry.SiteKind.etale`; no comparison between the
two topologies is used or needed, because clause (4) supplies the affine case in whichever
topology the rule is stated for.

The source of a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks is presented *strictly*: the higher
direct images are constructed for a functor `g : 𝒳.cat ⥤ 𝒴.cat` with `g ⋙ q = p` on the nose,
and `CategoryTheory.CatFiberedInGroupoids.homFunctor_comp_p` — clause (2) of **Stacks 02XS** —
says the functor underlying a 1-morphism satisfies exactly that equation. So no strictification
is needed and `fppfModules` may be seated at `𝒳.val.val.p` itself.

The section universe is `u + 1`. At the seating of `AlgebraicGeometry.Stack.AlgebraicStacks` the
underlying category of a stack lies in `Type (u + 1)` with morphisms in `Type u`, and the direct
image of **Stacks 06WE** is computed by limits indexed by the two sites, so no smaller universe
is available for it. The index type of a smooth cover is correspondingly `Type (u + 1)`, the
universe of the objects of the site; clause (3) is stated for families indexed there.

The two sheafification conditions that the higher direct images are constructed under are
established for the fppf topology just as `AlgebraicGeometry.Stack` does for the étale one: the
underlying category of an algebraic stack is essentially small in `u + 1`, so both transport
from a small model. They are attached as *local* instances, which is what makes the Abelian
structure on `fppfModules` — and hence the weak Serre condition, the spectral sequences and the
abutments below — available in the statements of this file. Both are propositions, so a
consumer who reinstates them obtains the very same Abelian structure.

### What is carried, and why

Clauses (1) to (4) are the source's own hypotheses and are stated as such. Two further
hypotheses are carried, and neither is the conclusion of **Stacks 0770** nor anything that
yields it without the four clauses:

`AlgebraicGeometry.Stack.AlgebraicStacks.HasSmoothAffineBaseChange` is the first move's
geometric input: a family of smooth 1-morphisms `u j : 𝒰 j ⟶ 𝒴` from affine-representable
stacks, jointly surjective on points, with base-changed sources `𝒳' j`, the projections
`f' j : 𝒳' j ⟶ 𝒰 j` and `v j : 𝒳' j ⟶ 𝒳`, the smoothness of `v j` (**Stacks 075W**), the
stability of quasi-compactness and quasi-separatedness of `f` under that base change
(**Stacks 050U**, **Stacks 04YW**), and the base-change isomorphisms
`(u j)^* Rⁱf_* F ≅ Rⁱ(f' j)_* (v j)^* F` of **Stacks 075H**. **Stacks 075H** for sheaves of
modules is `AlgebraicGeometry.Stack.AlgebraicStacks.moduleHigherDirectImageBaseChangeIso`, stated
for the 2-fibre product square; it is not assembled into this package here, and the whole package
is hypothesised.

`AlgebraicGeometry.Stack.AlgebraicStacks.HasFppfCechPresentation` is the second move's input:
over an affine-representable target, a smooth presentation of the source by affine-representable
stacks together with the first-quadrant spectral sequence of **Stacks 072G** part (2) relating
the higher direct images along the terms of its Čech nerve to those along `f`. Part (2)(b) of
that tag, at module coefficients, is
`AlgebraicGeometry.Stack.AlgebraicStacks.exists_fppfModuleDirectImageSpectralSequence`; it is not
assembled into this package here. The affineness of the terms of the Čech nerve, which is where
quasi-separatedness of `f` is spent in the source, is part of the same package.

Both hypotheses are consumed, not merely stated: the first supplies the cover that clause (3) is
applied to and the isomorphism that clause (2) is transported along, the second supplies the
spectral sequence whose `E₂` terms clause (4) is applied to, and the conclusion follows from
clause (1) only through **Stacks 0132** part (4). Removing any one of the four clauses breaks
the proof.

### Degrees

The criterion is proved in every degree `i`, and in each degree separately: the first move is
degree-wise because the base-change isomorphism is, and the second move reads one abutment term
off a spectral sequence of modules. No vanishing or boundedness in `i` is used.

## References

* [Stacks Project, Tag 0132](https://stacks.math.columbia.edu/tag/0132)
* [Stacks Project, Tag 02MO](https://stacks.math.columbia.edu/tag/02MO)
* [Stacks Project, Tag 02XS](https://stacks.math.columbia.edu/tag/02XS)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 050U](https://stacks.math.columbia.edu/tag/050U)
* [Stacks Project, Tag 06TP](https://stacks.math.columbia.edu/tag/06TP)
* [Stacks Project, Tag 06WB](https://stacks.math.columbia.edu/tag/06WB)
* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
* [Stacks Project, Tag 072G](https://stacks.math.columbia.edu/tag/072G)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
* [Stacks Project, Tag 075H](https://stacks.math.columbia.edu/tag/075H)
* [Stacks Project, Tag 075U](https://stacks.math.columbia.edu/tag/075U)
* [Stacks Project, Tag 075W](https://stacks.math.columbia.edu/tag/075W)
* [Stacks Project, Tag 076Z](https://stacks.math.columbia.edu/tag/076Z)
* [Stacks Project, Tag 0770](https://stacks.math.columbia.edu/tag/0770)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Modules on the fppf site of an algebraic stack -/

/-- `Mod(𝒪_𝒳)`, the modules of **Stacks 06WB** on the fppf site of an algebraic stack `𝒳` over
`S`, at the section universe `u + 1` in which the direct images of **Stacks 06WE** and their
right derived functors are constructed at this seating. -/
abbrev fppfModules (𝒳 : AlgebraicStacks.{u, w} B S hS) :=
  modules.{u, u + 1, u, u + 1} B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids

/-- The inverse image `f^*` of **Stacks 06WE** along a 1-morphism of algebraic stacks over `S`,
on modules on the fppf sites.

The source is seated at its own structure functor: by clause (2) of **Stacks 02XS**, that is
`CategoryTheory.CatFiberedInGroupoids.homFunctor_comp_p`, the functor underlying `f` composed
with the structure functor of the target *equals* the structure functor of the source, which is
the strictness the inverse image asks for. -/
abbrev fppfModulePullback {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) :
    fppfModules B S hS 𝒴 ⥤ fppfModules B S hS 𝒳 :=
  modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS 𝒳.val.val.p 𝒴.val.val.p
    𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
    (CatFiberedInGroupoids.homFunctor f.hom)
    (CatFiberedInGroupoids.homFunctor_comp_p f.hom) B.topology le_rfl

/-- The associated fppf site of an algebraic stack over `S` admits sheafification of abelian
sheaves at section universe `u + 1`: the underlying category of the stack lies in `Type (u + 1)`
with morphisms in `Type u`, hence is essentially small there, so sheafification transports from
a small model.

This is one of the two conditions under which the higher direct images of modules are
constructed. -/
theorem hasSheafify_fppfAssociatedTopology (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    HasSheafify (associatedTopology B S hS 𝒳.val.val.p B.topology) AddCommGrpCat.{u + 1} :=
  have : EssentiallySmall.{u + 1} 𝒳.val.val.obj := inferInstance
  hasSheafifyEssentiallySmallSite _ _

/-- The associated fppf site of an algebraic stack over `S` has the property that the local
isomorphisms of abelian sheaves at section universe `u + 1` are the locally bijective morphisms,
for the same reason: the underlying category is essentially small in `u + 1`.

This is the second of the two conditions under which the higher direct images of modules are
constructed. -/
theorem wEqualsLocallyBijective_fppfAssociatedTopology (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    (associatedTopology B S hS 𝒳.val.val.p B.topology).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} :=
  have : EssentiallySmall.{u + 1} 𝒳.val.val.obj := inferInstance
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- The higher direct image `Rⁱf_*` of modules on the fppf sites along a 1-morphism of algebraic
stacks over `S`: the `i`-th right derived functor of the direct image of **Stacks 06WE**.

The two sheafification conditions are supplied from
`AlgebraicGeometry.Stack.AlgebraicStacks.hasSheafify_fppfAssociatedTopology` and
`AlgebraicGeometry.Stack.AlgebraicStacks.wEqualsLocallyBijective_fppfAssociatedTopology`, so no
instance argument is needed. -/
abbrev fppfHigherDirectImage {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (i : ℕ) :
    fppfModules B S hS 𝒳 ⥤ fppfModules B S hS 𝒴 :=
  letI := hasSheafify_fppfAssociatedTopology B S hS 𝒳
  letI := wEqualsLocallyBijective_fppfAssociatedTopology B S hS 𝒳
  letI := hasSheafify_fppfAssociatedTopology B S hS 𝒴
  letI := wEqualsLocallyBijective_fppfAssociatedTopology B S hS 𝒴
  moduleSheafHigherDirectImage.{u, u + 1, u, u + 1, u} B S hS 𝒳.val.val.p 𝒴.val.val.p
    𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
    (CatFiberedInGroupoids.homFunctor f.hom)
    (CatFiberedInGroupoids.homFunctor_comp_p f.hom) B.topology le_rfl i

attribute [local instance]
  hasSheafify_fppfAssociatedTopology wEqualsLocallyBijective_fppfAssociatedTopology

/-! ### Representability by an affine scheme -/

/-- An algebraic stack over `S` is **representable by an affine scheme** when it is equivalent,
over the big fppf category of schemes over `S`, to the category fibred in groupoids represented
by an object of that category whose underlying scheme is affine.

This is the condition clause (4) of **Stacks 0770** places on the source and the target of its
affine case. Nothing below unfolds it: it is used only to match clause (4) against the stacks a
smooth affine presentation produces. -/
abbrev IsAffineRepresentable (𝒳 : AlgebraicStacks.{u, w} B S hS) : Prop :=
  ∃ U : BigFppfOver B S hS,
    IsAffine ((BigFppfOver.toScheme B S hS).obj U) ∧
      Nonempty (StacksRepresentableCFG.EquivalenceOver 𝒳.val.val.p
        (schemeFibredCategory B S hS U).val.p)

/-! ### The rule `M` and the clauses of the hypothesis -/

/-- A **rule** in the sense of **Stacks 0770**: a subcategory `M_𝒳` of `Mod(𝒪_𝒳)`, expressed as
a property of its objects, for every algebraic stack `𝒳` over `S`. -/
abbrev ModuleRule :=
  ∀ 𝒳 : AlgebraicStacks.{u, w} B S hS, ObjectProperty (fppfModules B S hS 𝒳)

/-- The **conclusion of Stacks 0770 at a single 1-morphism**: every higher direct image of an
object of `M_𝒳` lies in `M_𝒴`. -/
abbrev HigherDirectImagesMapInto (M : ModuleRule.{u, w} B S hS)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ (i : ℕ) (F : fppfModules B S hS 𝒳), M 𝒳 F → M 𝒴 ((fppfHigherDirectImage B S hS f i).obj F)

/-- **Clause (2) of the hypothesis of Stacks 0770.** The inverse image along a smooth
1-morphism of algebraic stacks maps the rule into the rule. -/
abbrev IsSmoothPullbackStable (M : ModuleRule.{u, w} B S hS) : Prop :=
  ∀ {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴), IsSmooth B S hS f →
    ∀ F : fppfModules B S hS 𝒴, M 𝒴 F → M 𝒳 ((fppfModulePullback B S hS f).obj F)

/-- **Clause (3) of the hypothesis of Stacks 0770.** The rule is smooth-local on the target: for
a family of smooth 1-morphisms `f j : 𝒳 j ⟶ 𝒴` whose images cover the points of `𝒴`, an object
of `Mod(𝒪_𝒴)` lies in `M_𝒴` if and only if each of its inverse images lies in `M_{𝒳 j}`.

Joint surjectivity is `|𝒴| = ⋃ j |f j|(|𝒳 j|)`, written with the points of **Stacks 04XG** and
their functoriality, exactly as the smooth-local criteria of this development state it. The
index type lies in `Type (u + 1)`, the universe of the objects of the big fppf category of
schemes over `S`, which is where the index set of a smooth presentation lives. -/
abbrev IsSmoothLocal (M : ModuleRule.{u, w} B S hS) : Prop :=
  ∀ (𝒴 : AlgebraicStacks.{u, w} B S hS) {J : Type (u + 1)}
    (𝒳 : J → AlgebraicStacks.{u, w} B S hS) (f : ∀ j, 𝒳 j ⟶ 𝒴),
    (∀ j, IsSmooth B S hS (f j)) →
    (Set.univ : Set (points B S hS 𝒴)) = ⋃ j, Set.range (pointsMap B S hS (f j)) →
    ∀ F : fppfModules B S hS 𝒴,
      (M 𝒴 F ↔ ∀ j, M (𝒳 j) ((fppfModulePullback B S hS (f j)).obj F))

/-- **Clause (4) of the hypothesis of Stacks 0770**, the affine case: for a 1-morphism of
algebraic stacks both of which are representable by affine schemes, every higher direct image
maps the rule into the rule.

This is a hypothesis of the criterion. It is not proved anywhere in this file, and the reduction
below is exactly the passage from it to the quasi-compact quasi-separated case. -/
abbrev AffineHigherDirectImagesMapInto (M : ModuleRule.{u, w} B S hS) : Prop :=
  ∀ {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴), IsAffineRepresentable B S hS 𝒳 →
    IsAffineRepresentable B S hS 𝒴 → HigherDirectImagesMapInto B S hS M f

/-! ### The two geometric prerequisites -/

/-- **The geometric input of the first move of the source's proof**, for a 1-morphism
`f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S`: a smooth presentation of the target by
affine-representable stacks together with the base change of `f` along it.

Concretely, a family `u j : 𝒰 j ⟶ 𝒴` of smooth 1-morphisms from affine-representable stacks
which is jointly surjective on points, and for each `j` a stack `𝒳' j` with 1-morphisms
`f' j : 𝒳' j ⟶ 𝒰 j` and `v j : 𝒳' j ⟶ 𝒳` such that

* `v j` is smooth — the base change of the smooth `u j`, **Stacks 075W**;
* `f' j` inherits quasi-compactness and quasi-separatedness from `f` — **Stacks 050U** and
  **Stacks 04YW**; and
* `(u j)^* Rⁱf_* F ≅ Rⁱ(f' j)_* (v j)^* F` for every degree and every module — higher direct
  images commute with the base change, **Stacks 075H**.

The package is carried whole; see the implementation notes of this module. -/
abbrev HasSmoothAffineBaseChange {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∃ (J : Type (u + 1)) (𝒰 : J → AlgebraicStacks.{u, w} B S hS) (u : ∀ j, 𝒰 j ⟶ 𝒴)
    (𝒳' : J → AlgebraicStacks.{u, w} B S hS) (f' : ∀ j, 𝒳' j ⟶ 𝒰 j) (v : ∀ j, 𝒳' j ⟶ 𝒳),
    (∀ j, IsAffineRepresentable B S hS (𝒰 j)) ∧
    (∀ j, IsSmooth B S hS (u j)) ∧
    ((Set.univ : Set (points B S hS 𝒴)) = ⋃ j, Set.range (pointsMap B S hS (u j))) ∧
    (∀ j, IsSmooth B S hS (v j)) ∧
    (Stack.IsQuasiCompactMorphism B S hS f →
      ∀ j, Stack.IsQuasiCompactMorphism B S hS (f' j)) ∧
    (AlgebraicStacks.IsQuasiSeparated B S hS f →
      ∀ j, AlgebraicStacks.IsQuasiSeparated B S hS (f' j)) ∧
    ∀ (j : J) (i : ℕ) (F : fppfModules B S hS 𝒳),
      Nonempty ((fppfModulePullback B S hS (u j)).obj
          ((fppfHigherDirectImage B S hS f i).obj F) ≅
        (fppfHigherDirectImage B S hS (f' j) i).obj
          ((fppfModulePullback B S hS (v j)).obj F))

/-- **The geometric input of the second move of the source's proof**, for a 1-morphism
`f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` whose target is representable by an affine scheme: a
smooth presentation `g n : 𝒱 n ⟶ 𝒳` of the source by affine-representable stacks, with
1-morphisms `fg n : 𝒱 n ⟶ 𝒴`, together with the relative Čech pushforward spectral sequence of
**Stacks 072G** part (2) for the fppf topology — a cohomological spectral sequence of
`Mod(𝒪_𝒴)` starting at the second page, vanishing outside the first quadrant, with
`E₂^{p,q} ≅ R^q (fg p)_* (g p)^* F`, and abutting to the higher direct images `Rⁱf_* F`.

The family `𝒱` is the Čech nerve of a smooth surjective presentation of `𝒳` by an affine
scheme, `g n` its degree-`n` projection and `fg n` its composite with `f`; that the terms of the
nerve are again representable by affine schemes is where quasi-separatedness of `f` is spent in
the source. The package is carried whole; see the implementation notes of this module. -/
abbrev HasFppfCechPresentation {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∃ (𝒱 : ℕ → AlgebraicStacks.{u, w} B S hS) (g : ∀ n, 𝒱 n ⟶ 𝒳) (fg : ∀ n, 𝒱 n ⟶ 𝒴),
    (∀ n, IsAffineRepresentable B S hS (𝒱 n)) ∧
    (∀ n, IsSmooth B S hS (g n)) ∧
    ∀ (F : fppfModules B S hS 𝒳) (i : ℕ),
      ∃ (E : CohomologicalSpectralSequence (fppfModules B S hS 𝒴) 2)
        (H : ℤ → fppfModules B S hS 𝒴),
        SpectralSequence.AbutsTo E H ∧
        (∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((E.page 2 le_rfl).X (p, q))) ∧
        (∀ p q : ℕ, Nonempty ((E.page 2 le_rfl).X ((p : ℤ), (q : ℤ)) ≅
          (fppfHigherDirectImage B S hS (fg p) q).obj
            ((fppfModulePullback B S hS (g p)).obj F))) ∧
        Nonempty ((fppfHigherDirectImage B S hS f i).obj F ≅ H (i : ℤ))

/-! ### The first move: descent along a smooth cover of the target -/

/-- **The first move of the proof of Stacks 0770.** Let `M` be a rule satisfying clauses (1),
(2) and (3), let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks, and let `u j : 𝒰 j ⟶ 𝒴` be a
jointly surjective family of smooth 1-morphisms. Suppose each `u j` is complemented by a base
change: a stack `𝒳' j` over both `𝒰 j` and `𝒳`, with `v j : 𝒳' j ⟶ 𝒳` smooth and with
`(u j)^* Rⁱf_* F ≅ Rⁱ(f' j)_* (v j)^* F`. If the conclusion of **Stacks 0770** holds for every
`f' j`, it holds for `f`.

This is the reduction of the general case to the case of an affine-representable target: the
source takes the `𝒰 j` to be representable by affine schemes, and nothing here needs them to be,
so no representability hypothesis is imposed.

Clause (2) is what puts `(v j)^* F` in `M_{𝒳' j}`, which is the input the conclusion for
`f' j` consumes; clause (1) is used only through closure of a weak Serre subcategory under
isomorphisms, to transport along the base-change isomorphism; and clause (3) is the descent
itself. -/
theorem higherDirectImagesMapInto_of_smoothAffineCover (M : ModuleRule.{u, w} B S hS)
    (hSerre : ∀ 𝒳 : AlgebraicStacks.{u, w} B S hS, (M 𝒳).IsWeakSerreClass)
    (hSmooth : IsSmoothPullbackStable B S hS M) (hLocal : IsSmoothLocal B S hS M)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    {J : Type (u + 1)} {𝒰 : J → AlgebraicStacks.{u, w} B S hS} (u : ∀ j, 𝒰 j ⟶ 𝒴)
    (hu : ∀ j, IsSmooth B S hS (u j))
    (hcover : (Set.univ : Set (points B S hS 𝒴)) = ⋃ j, Set.range (pointsMap B S hS (u j)))
    {𝒳' : J → AlgebraicStacks.{u, w} B S hS} (f' : ∀ j, 𝒳' j ⟶ 𝒰 j) (v : ∀ j, 𝒳' j ⟶ 𝒳)
    (hv : ∀ j, IsSmooth B S hS (v j))
    (hbase : ∀ (j : J) (i : ℕ) (F : fppfModules B S hS 𝒳),
      (fppfModulePullback B S hS (u j)).obj ((fppfHigherDirectImage B S hS f i).obj F) ≅
        (fppfHigherDirectImage B S hS (f' j) i).obj
          ((fppfModulePullback B S hS (v j)).obj F))
    (hcase : ∀ j, HigherDirectImagesMapInto B S hS M (f' j)) :
    HigherDirectImagesMapInto B S hS M f := by
  intro i F hF
  refine (hLocal 𝒴 𝒰 u hu hcover _).2 fun j => ?_
  have := hSerre (𝒰 j)
  exact (M (𝒰 j)).prop_of_iso (hbase j i F).symm
    (hcase j i _ (hSmooth (v j) (hv j) F hF))

/-! ### The second move: the Čech spectral sequence over an affine-representable target -/

/-- **The second move of the proof of Stacks 0770.** Let `M` be a rule satisfying clauses (1),
(2) and (4) and let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks with `𝒴` representable by an
affine scheme. Let `g n : 𝒱 n ⟶ 𝒳` be smooth 1-morphisms from affine-representable stacks, with
1-morphisms `fg n : 𝒱 n ⟶ 𝒴`, and let `E` be a cohomological spectral sequence of `Mod(𝒪_𝒴)`
abutting to `H`, vanishing outside the first quadrant, with
`E₂^{p,q} ≅ R^q (fg p)_* (g p)^* F`. If `Rⁱf_* F` is identified with `H i`, then it lies in
`M_𝒴`.

Clause (2) puts each `(g p)^* F` in `M_{𝒱 p}` because `g p` is smooth; clause (4) applies to
`fg p`, a 1-morphism between affine-representable stacks, and puts every `E₂` term in `M_𝒴`;
clause (1) and **Stacks 0132** part (4) carry that to the abutment. The spectral sequence is
read on its second page, which is where **Stacks 072G** identifies its terms. -/
theorem higherDirectImagesMapInto_of_abutsTo (M : ModuleRule.{u, w} B S hS)
    (hSerre : ∀ 𝒳 : AlgebraicStacks.{u, w} B S hS, (M 𝒳).IsWeakSerreClass)
    (hSmooth : IsSmoothPullbackStable B S hS M)
    (hAffine : AffineHigherDirectImagesMapInto B S hS M)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (h𝒴 : IsAffineRepresentable B S hS 𝒴)
    {𝒱 : ℕ → AlgebraicStacks.{u, w} B S hS} (g : ∀ n, 𝒱 n ⟶ 𝒳) (fg : ∀ n, 𝒱 n ⟶ 𝒴)
    (h𝒱 : ∀ n, IsAffineRepresentable B S hS (𝒱 n)) (hg : ∀ n, IsSmooth B S hS (g n))
    (i : ℕ) (F : fppfModules B S hS 𝒳) (hF : M 𝒳 F)
    {E : CohomologicalSpectralSequence (fppfModules B S hS 𝒴) 2}
    {H : ℤ → fppfModules B S hS 𝒴} (hE : SpectralSequence.AbutsTo E H)
    (hzero : ∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((E.page 2 le_rfl).X (p, q)))
    (hpage : ∀ p q : ℕ, (E.page 2 le_rfl).X ((p : ℤ), (q : ℤ)) ≅
      (fppfHigherDirectImage B S hS (fg p) q).obj
        ((fppfModulePullback B S hS (g p)).obj F))
    (habut : (fppfHigherDirectImage B S hS f i).obj F ≅ H (i : ℤ)) :
    M 𝒴 ((fppfHigherDirectImage B S hS f i).obj F) := by
  have := hSerre 𝒴
  refine (M 𝒴).prop_of_iso habut.symm ?_
  refine hE.prop_of_prop_page_firstQuadrant (M 𝒴) le_rfl hzero (fun p q => ?_) (i : ℤ)
  exact (M 𝒴).prop_of_iso (hpage p q).symm
    (hAffine (fg p) (h𝒱 p) h𝒴 q _ (hSmooth (g p) (hg p) F hF))

/-! ### The criterion -/

/-- **Stacks 0770.** Let `M` be a rule which associates to every algebraic stack `𝒳` over `S` a
subcategory `M_𝒳` of `Mod(𝒪_𝒳)`, the modules on the fppf site of `𝒳`, such that

1. `M_𝒳` is a weak Serre subcategory of `Mod(𝒪_𝒳)` for every algebraic stack `𝒳`;
2. for a smooth 1-morphism `f : 𝒳 ⟶ 𝒴` the inverse image `f^*` maps `M_𝒴` into `M_𝒳`;
3. `M` is smooth-local on the target; and
4. for a 1-morphism of stacks representable by affine schemes, `Rⁱf_*` maps `M` into `M`.

Then for every quasi-compact and quasi-separated 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks and
every `F` in `M_𝒳`, the higher direct image `Rⁱf_* F`, computed in the fppf topology, lies in
`M_𝒴`.

The proof is the source's: the first move
(`AlgebraicGeometry.Stack.AlgebraicStacks.higherDirectImagesMapInto_of_smoothAffineCover`)
transports the question along a smooth presentation of `𝒴` by affine-representable stacks, using
clauses (1), (2), (3) and the base-change isomorphisms; the second
(`AlgebraicGeometry.Stack.AlgebraicStacks.higherDirectImagesMapInto_of_abutsTo`) settles each
base-changed 1-morphism, whose target is affine-representable and which is again quasi-compact
and quasi-separated, from clauses (1), (2), (4) and the Čech spectral sequence.

Two prerequisites beyond the four clauses are hypothesised, `hpres` and `hcech`: the base-change
isomorphisms of **Stacks 075H** and the Čech spectral sequence of **Stacks 072G** part (2). -/
@[stacks 0770 "the reduction of the quasi-compact quasi-separated case to the affine case,
  which is the source's own clause (4), from clauses (1) to (4) together with two hypothesised
  prerequisites, the base-change isomorphisms of Stacks 075H and the fppf relative Cech
  pushforward spectral sequence of Stacks 072G part (2)(b)"]
theorem higherDirectImage_mem_of_quasiCompact_quasiSeparated (M : ModuleRule.{u, w} B S hS)
    (hSerre : ∀ 𝒳 : AlgebraicStacks.{u, w} B S hS, (M 𝒳).IsWeakSerreClass)
    (hSmooth : IsSmoothPullbackStable B S hS M) (hLocal : IsSmoothLocal B S hS M)
    (hAffine : AffineHigherDirectImagesMapInto B S hS M)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hqc : Stack.IsQuasiCompactMorphism B S hS f)
    (hqs : AlgebraicStacks.IsQuasiSeparated B S hS f)
    (hpres : HasSmoothAffineBaseChange B S hS f)
    (hcech : ∀ {𝒳' 𝒴' : AlgebraicStacks.{u, w} B S hS} (f' : 𝒳' ⟶ 𝒴'),
      Stack.IsQuasiCompactMorphism B S hS f' →
      AlgebraicStacks.IsQuasiSeparated B S hS f' → IsAffineRepresentable B S hS 𝒴' →
      HasFppfCechPresentation B S hS f')
    (i : ℕ) (F : fppfModules B S hS 𝒳) (hF : M 𝒳 F) :
    M 𝒴 ((fppfHigherDirectImage B S hS f i).obj F) := by
  obtain ⟨J, 𝒰, u, 𝒳', f', v, haffine, husmooth, hcover, hvsmooth, hqc', hqs', hbase⟩ := hpres
  refine higherDirectImagesMapInto_of_smoothAffineCover B S hS M hSerre hSmooth hLocal f u
    husmooth hcover f' v hvsmooth (fun j i F => (hbase j i F).some) (fun j => ?_) i F hF
  intro i' G hG
  obtain ⟨𝒱, g, fg, h𝒱, hgsmooth, hdata⟩ :=
    hcech (f' j) (hqc' hqc j) (hqs' hqs j) (haffine j)
  obtain ⟨E, H, hE, hzero, hpage, habut⟩ := hdata G i'
  exact higherDirectImagesMapInto_of_abutsTo B S hS M hSerre hSmooth hAffine (f' j)
    (haffine j) g fg h𝒱 hgsmooth i' G hG hE hzero (fun p q => (hpage p q).some) habut.some

end AlgebraicGeometry.Stack.AlgebraicStacks

end
