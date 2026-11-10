module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleCompositionSections
public import StacksFrontier.AlgebraicGeometry.Thickenings.ConormalSheaf
public import StacksFrontier.AlgebraicGeometry.Thickenings.ConormalSheafSupplement

/-!
# The square comparison of the conormal sheaf, read at the structure sheaf

Part (2) of [Stacks Project, Tag 04G2] compares two canonical maps of conormal sheaves attached
to a commutative square, and the two are built in exactly mirroring ways.  On the small étale
site of an algebraic space, `AlgebraicGeometry.Space.conormalMap` of [Stacks Project, Tag 04CP]
is the square comparison `AlgebraicGeometry.Space.conormalPullbackCompIso` followed by the
inverse image along the inclusion of `AlgebraicGeometry.Space.idealSheafMap`; on a ringed space,
`Stacks.ClosedImmersion.conormalSheafMap` of [Stacks Project, Tag 01R4] is the square comparison
`Stacks.ClosedImmersion.pullbackCompIso` followed by the pullback along the inclusion of
`Stacks.ClosedImmersion.idealSheafMap`.  The agreement of the two maps therefore splits into the
agreement of the two maps of ideal sheaves and the agreement of the two **square comparisons**.

This file is about the second of those, in the one place where either square comparison can be
described: at the **unit module**, the structure sheaf read as a module over itself.  Both ideal
sheaves sit inside their structure sheaves by a monomorphism and both maps of ideal sheaves are
determined by their composite with that inclusion — that is how
`AlgebraicGeometry.Space.idealSheafMap_comp_definingIdealSheaf_ι` and
`Stacks.ClosedImmersion.idealSheafMap_comp_ι` are used — so the unit module is exactly where the
two square comparisons have to be compared.

The compatibility each square comparison has there is that it carries one of the two composites
of "pullback of regular functions" round the square to the other.  Ringed-space side those maps
are `RingedSpaceModuleAdjunction.modulePullbackUnitToUnit` and the statement is proved here,
`Stacks.ClosedImmersion.pullbackCompIso_hom_comp_modulePullbackUnitToUnit`.  Spaces-side they are
`AlgebraicGeometry.Space.structureModulePullbackMap`; that half is not proved in this file, but
it **is** proved —
`AlgebraicGeometry.Space.squarePullbackCompIso_hom_comp_structureModulePullbackMap`
of `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSquareComparisonSpacesUnit.lean`, at
`AlgebraicGeometry.Space.squarePullbackCompIso`, which is the comparison
`AlgebraicGeometry.Space.conormalMapOfImmersions` is built from and so the one part (2) needs.
The section "The spaces-side mirror is proved, and it needed no rename" below records what this
file's own bisection got wrong.

`CategoryTheory.eq_of_comp_eq_comp` is the compatibility stated once: two square comparisons
which carry one composite of unit maps to the other are equal, provided the composite they are
tested against is a monomorphism.  On a ringed space that composite is even invertible, since
`RingedSpaceModuleAdjunction.isIso_modulePullbackUnitToUnit` holds for every morphism; on the
small étale site the corresponding invertibility is reduced to a condition on the unit section by
`AlgebraicGeometry.Space.isIso_structureModulePullbackMap_of_unitSection` and is not proved in
this development.

## Main results

* `CategoryTheory.homEquiv_comp_conjugateEquiv_app` and
  `CategoryTheory.eq_comp_of_homEquiv_eq`: the mate of a transformation of left adjoints computes
  the transpose of a composite whose first factor is that transformation.  This is the handle on
  a comparison built by `CategoryTheory.Adjunction.leftAdjointUniq` or
  `CategoryTheory.Adjunction.leftAdjointCompIso`; it generalises
  `CategoryTheory.Adjunction.eq_leftAdjointUniq_hom_app_comp` to two adjunctions whose right
  adjoints are only isomorphic, which is what the composition comparison of pullbacks needs.
* `CategoryTheory.eq_of_comp_eq_comp`: **the compatibility of two square comparisons**, stated
  once.
* `CategoryTheory.natTrans_comp_comp_app`, `CategoryTheory.eq_square_comp_of_cancel`,
  `CategoryTheory.eq_app_comp_of_split` and `CategoryTheory.eq_of_cancel_comp`: the bookkeeping
  of a square comparison read at one object, done in an arbitrary category.  See the
  implementation notes for why none of it is done in the geometric goals.
* `RingedSpaceModuleAdjunction.modulePullbackComp_hom_app_unit_comp`: **the composition
  comparison of pullbacks of modules on ringed spaces is compatible with the maps to the
  structure sheaves.**
* `Stacks.ClosedImmersion.pullbackCompIso_hom_comp_modulePullbackUnitToUnit`: **the ringed-space
  square comparison at the unit module** — round the square one way the composite
  `f^*j^*𝒪_{W'} ⟶ f^*𝒪_W ⟶ 𝒪_Z` of the two maps of pullback of regular functions is, the other
  way, `Stacks.ClosedImmersion.pullbackCompIso` followed by `i^*k^*𝒪_{W'} ⟶ i^*𝒪_{Z'} ⟶ 𝒪_Z`.
* `AlgebraicGeometry.Space.eqToHom_app_comp_structureModulePullbackMap`: the transport of the
  spaces-side map along an equality of morphisms.  It is stated with the unit module written as
  `AlgebraicGeometry.Space.structureUnitModule` of
  `StacksFrontier/AlgebraicGeometry/Spaces/IdealSheafMapStructureSheaf.lean`, which is **the wrong
  spelling for the spaces-side mirror**; the twin that mirror uses is
  `AlgebraicGeometry.Space.eqToHom_app_unit_comp_structureModulePullbackMap` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSquareComparisonSpacesUnit.lean`.  See the
  section below for the reason.

## Route

Both square comparisons are built the same way — the composition comparison of inverse images
along one route, the transport along the commutativity of the square, and the composition
comparison along the other route — so both statements reduce to the composition law for the map
`g^*𝒪 ⟶ 𝒪` together with the transport of that map along an equality of morphisms.

Ringed-space side the composition law is
`RingedSpaceModuleAdjunction.modulePullbackComp_hom_app_unit_comp`, proved here through the mate
characterisation `RingedSpaceModuleAdjunction.conjugateEquiv_modulePullbackComp_hom` of the
composition comparison and the cocycle condition
`RingedSpaceModuleAdjunction.structureSheafModuleHom_comp` for the structure-sheaf map, which
holds on the nose; the transport is
`RingedSpaceModuleAdjunction.modulePullbackCongr_hom_app_comp_modulePullbackUnitToUnit`, and
`Stacks.ClosedImmersion.pullbackCompIso_hom` writes the square comparison out.

Spaces-side all three inputs are available too: the composition law is
`AlgebraicGeometry.Space.structureModulePullbackMap_comp`, the split of the square comparison
into its three factors is `AlgebraicGeometry.Space.conormalPullbackCompIso_hom` — or,
at the spelling the mirror is proved at,
`AlgebraicGeometry.Space.squarePullbackCompIso_hom` — and the transport is
`AlgebraicGeometry.Space.eqToHom_app_comp_structureModulePullbackMap` below, or rather its
unit-module twin named above.

## The spaces-side mirror is proved, and it needed no rename

**Neither a named object of `AlgebraicGeometry.AlgebraicSpaces` in place of the anonymous
constructor nor, therefore, a change to every `AlgebraicGeometry.Space.ClosedSubspaces` signature
in the library is needed.**  The mirror is
`AlgebraicGeometry.Space.squarePullbackCompIso_hom_comp_structureModulePullbackMap` of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSquareComparisonSpacesUnit.lean`, and that file
checks in 0.2 s.  Two facts explain this:

* **The statement part (2) of [Stacks Project, Tag 04G2] needs is not at
  `AlgebraicGeometry.Space.conormalPullbackCompIso`.**  Part (2) is registered at
  `AlgebraicGeometry.Space.conormalMapOfImmersions`, because that is where the source's
  hypotheses are, and that map is built from
  `AlgebraicGeometry.Space.conormalAlgebraSquarePieceMap`, whose middle factor is
  `AlgebraicGeometry.Space.squarePullbackCompIso` — the same three-factor comparison with the
  four spaces and the four morphisms of the square as plain variables.  So the anonymous
  constructor never appears on the chain, and the bisection below concerns a
  statement the tag does not need.
* **With that spelling the assembly is still a kernel timeout if it goes through
  `AlgebraicGeometry.Space.structureUnitModule`.**  Declaration by declaration: `rfl` between the
  two spellings of a single
  morphism,
  `(modulePullbackCompIso B S hS f i').inv.app (structureUnitModule B S hS X')` and
  `(modulePullbackCompIso B S hS f i').inv.app
  (SheafOfModules.unit (structureRingSheaf B S hS X'))`,
  elaborates and is then a **kernel** deterministic timeout, while every statement in the second
  spelling alone is free.  `AlgebraicGeometry.Space.eqToHom_app_comp_structureModulePullbackMap`
  below is stated in the first spelling, which is why it cannot be used on the chain; its twin
  in the second is
  `AlgebraicGeometry.Space.eqToHom_app_unit_comp_structureModulePullbackMap`, proved there from
  scratch.

The rest of this file records where the cost of the statement at
`AlgebraicGeometry.Space.conormalPullbackCompIso` lies.

## The cost of the statement at `conormalPullbackCompIso`

The spaces-side statement at `AlgebraicGeometry.Space.conormalPullbackCompIso` is

```
(modulePullbackCompIso f i').hom.app 𝒪_{X'} ≫ structureModulePullbackMap (f ≫ i') =
  (conormalPullbackCompIso Z Z' g f hsq).hom.app 𝒪_{X'} ≫
    (modulePullback i).map (structureModulePullbackMap g) ≫ structureModulePullbackMap i
```

together with its form with the left-hand side expanded by
`AlgebraicGeometry.Space.structureModulePullbackMap_comp`, which is
`f^*(i')^*𝒪_{X'} ⟶ f^*𝒪_{Z'} ⟶ 𝒪_Z` on the left.  Its three inputs are named in the route above
and nothing else is needed: assembling them is `CategoryTheory.eq_app_comp_of_split` at
`x = (modulePullbackCompIso f i').hom`, `y` the transport and
`z = (modulePullbackCompIso i g).inv`.
It is **not** a missing lemma but a cost, and the cost is bisected argument by argument below.

## Implementation notes

**The cost of the spaces-side statement.**  The statement itself is cheap: written as a
self-equality, or as the hypothesis of a `True`-valued theorem, it is kernel-checked in under two
seconds, and so is every one of its sub-terms separately, including
`(conormalPullbackCompIso …).hom.app` at the unit module and the split
`AlgebraicGeometry.Space.conormalPullbackCompIso_hom` read at the unit module by
`CategoryTheory.NatTrans.congr_app`.  What is not affordable is the assembly:

* `CategoryTheory.Category.assoc` with its three morphisms left to unification against such a
  goal exhausts the 200,000-heartbeat `whnf` budget, and `simp only [Category.assoc]` fails
  earlier still as not type-correct at `implicit` transparency.  Hence all the associativity is
  stated once in an arbitrary category, in the four generic lemmas of this file.
* Mathlib's `CategoryTheory.NatTrans.comp_app`, with its type written out at this instance, is
  rejected by the **kernel** with a deterministic timeout, while
  `CategoryTheory.natTrans_comp_comp_app` — the same equation proved generically — is free.  The
  pattern held throughout: writing out the type of an intermediate equation about these
  comparisons costs a budget each time, instantiating a generic lemma costs nothing.
* **The cost is not the two spellings of the category of modules**, that is, the reconciliation
  of `AlgebraicGeometry.Space.Modules` with `CategoryTheory.SheafOfModules` of the structure ring
  sheaf through the semireducible `AlgebraicGeometry.Space.smallEtaleRingedSite`.  A spelling of
  `AlgebraicGeometry.Space.structureModulePullbackMap` whose target lives in the first spelling
  exists —
  `AlgebraicGeometry.Space.structureUnitPullbackMap` of
  `StacksFrontier/AlgebraicGeometry/Spaces/IdealSheafMapStructureSheaf.lean` — and the assembly over
  it fails exactly as without it; so does the assembly written uniformly in the *other* spelling,
  with `CategoryTheory.SheafOfModules.unit` of the structure ring sheaf in the transport as well.
  The spelling clash is real and costs a budget of its own, which is why that map exists, but
  it is not what blocks this statement.
* **The cost is the middle factor of the split**, the transport
  `eqToHom (congrArg (fun h ↦ modulePullback h) hsq.symm)` of
  `AlgebraicGeometry.Space.conormalPullbackCompIso_hom`.  Bisected one argument of
  `CategoryTheory.eq_app_comp_of_split` at a time, each as its own declaration with its own
  budget: with all ten arguments variables and only the four inverse-image functors geometric,
  the whole probe checks in 1.4 s; with `x` the concrete
  `(AlgebraicGeometry.Space.modulePullbackCompIso f i').hom` it is still free; with `z` the
  concrete `(AlgebraicGeometry.Space.modulePullbackCompIso i g).inv` it is still free; with the
  transport concrete and everything else a variable it is a **kernel** deterministic timeout.
* **And the transport is expensive only because the closed subspace is written as an anonymous
  constructor.**  The same assembly, transport concrete, is free (0.2 s) when the two routes
  round the square are arbitrary morphisms `p, q` with `e : p = q`; free when they are arbitrary
  composites `a ≫ b` and `c ≫ d` between section variables; free when the source is the bundled
  subspace but the two routes are not composites; and a kernel timeout as soon as the two routes
  are *composites* and the subspace is written `(⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)`
  — whether the two inclusions are `AlgebraicGeometry.Space.subspaceInclusion` or arbitrary
  morphisms.  Give that object a name, by a `def` or equally by a reducible `abbrev`, write the
  statement over the name, and the same assembly is free again (0.2 s).  The anonymous
  constructor is what lets the kernel's conversion check take its first step; once it can, it
  reduces `AlgebraicGeometry.Space.modulePullback` towards its construction by sheafification,
  which is the non-termination recorded in the implementation notes of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleCompositionSections.lean`.  Against a
  variable the check is stuck at once and costs nothing.
* The fix does **not** transfer back: the same statement in the anonymous-constructor spelling,
  proved by the named-subspace lemma, is a kernel timeout again.  Nor can
  `attribute [local irreducible]` reach it — that keeps the *elaborator* off the same route in
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleCompositionLaw.lean`, whose own notes
  record that the kernel is unaffected by it.

So a statement of the square comparison **at `AlgebraicGeometry.Space.conormalPullbackCompIso`
itself** would need a named object of `AlgebraicGeometry.AlgebraicSpaces` for the closed
subspace, in the signatures of `AlgebraicGeometry.Space.subspaceInclusion` and
`conormalPullbackCompIso` in place of the anonymous constructor.  Two such names already exist
in the tree and neither is used on this chain:
`AlgebraicGeometry.Space.closedSubspaceSpace`
(`StacksFrontier/AlgebraicGeometry/Spaces/BlowupPropernessAndStrictTransformImage.lean`) and
`AlgebraicGeometry.Space.closedSubspaceToSpace`, with its inclusion
`AlgebraicGeometry.Space.closedSubspaceInclusion`
(`StacksFrontier/AlgebraicGeometry/Spaces/SchemeTheoreticSupport.lean`).  That is a change to the
shape of every `AlgebraicGeometry.Space.ClosedSubspaces` signature in the library, not a local one,
which is why it is recorded here rather than done — and, per the section above, **part (2) of
[Stacks Project, Tag 04G2] does not need it.**  Nothing else in the tree asks for the comparison
at that spelling.

**No `@[stacks]` attribute is placed.**  Part (2) of [Stacks Project, Tag 04G2] is registered,
when all of it is in, at `AlgebraicGeometry.Space.conormalMapOfImmersions`, because that is where
the source's hypotheses are; this file compares two of the repository's own constructions.

## References

* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0097](https://stacks.math.columbia.edu/tag/0097)
-/

@[expose] public section

open CategoryTheory

universe u

namespace CategoryTheory

/-- **Transposing a composite whose first factor is a transformation of left adjoints.**  For
`α : L₂ ⟶ L₁` between two left adjoints, the transpose along `L₂ ⊣ R₂` of `α.app x ≫ u` is the
transpose along `L₁ ⊣ R₁` of `u`, followed by the mate of `α`.

This is the description of a comparison of left adjoints that a consumer needs: the comparison
cannot describe its own values, but a composite whose first factor is the comparison has a
computable transpose. -/
theorem homEquiv_comp_conjugateEquiv_app {C : Type*} [Category C] {D : Type*} [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁)
    (x : C) (c : D) (u : L₁.obj x ⟶ c) :
    adj₂.homEquiv x c (α.app x ≫ u) =
      adj₁.homEquiv x c u ≫ (conjugateEquiv adj₁ adj₂ α).app c := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    ← unit_conjugateEquiv adj₁ adj₂ α x, Category.assoc, Category.assoc,
    (conjugateEquiv adj₁ adj₂ α).naturality u]

/-- **Two morphisms out of the two left adjoints whose transposes correspond under the mate of a
transformation of the left adjoints are carried to one another by that transformation.**

`CategoryTheory.Adjunction.eq_leftAdjointUniq_hom_app_comp` is the case of two adjunctions with
the same right adjoint and `α` the comparison of their left adjoints. -/
theorem eq_comp_of_homEquiv_eq {C : Type*} [Category C] {D : Type*} [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁)
    (x : C) (c : D) (u₁ : L₂.obj x ⟶ c) (u : L₁.obj x ⟶ c)
    (h : adj₂.homEquiv x c u₁ =
      adj₁.homEquiv x c u ≫ (conjugateEquiv adj₁ adj₂ α).app c) :
    u₁ = α.app x ≫ u :=
  (adj₂.homEquiv x c).injective
    (h.trans (homEquiv_comp_conjugateEquiv_app adj₁ adj₂ α x c u).symm)

/-- **Two square comparisons that carry one composite of unit maps to the other are equal**, as
soon as the composite they are tested against is a monomorphism.

This is the form in which the two statements of this file are the compatibility of the two square
comparisons: each says `p = Φ ≫ q` for its own comparison, with `p` and `q` the two composites of
pullback of regular functions round the square, so once an identification of the two developments
has put the two pairs `(p, q)` on top of one another the two comparisons coincide. -/
theorem eq_of_comp_eq_comp {C : Type*} [Category C] {U₀ U₁ V : C} {Φ Ψ : U₀ ⟶ U₁}
    (p : U₀ ⟶ V) (q : U₁ ⟶ V) [Mono q] (hΦ : p = Φ ≫ q) (hΨ : p = Ψ ≫ q) : Φ = Ψ :=
  (cancel_mono q).mp (hΦ.symm.trans hΨ)

/-- **A three-fold composite of natural transformations, read at an object.**  Stated here so
that a consumer instantiates it instead of writing the equation out: see the implementation
notes for what writing it out costs. -/
theorem natTrans_comp_comp_app {C : Type*} [Category C] {D : Type*} [Category D]
    {F G H K : C ⥤ D} (x : F ⟶ G) (y : G ⟶ H) (z : H ⟶ K) (M : C) :
    (x ≫ y ≫ z).app M = x.app M ≫ y.app M ≫ z.app M :=
  rfl

/-- **The bookkeeping of a square comparison read at one object.**  A square comparison is a
composite `a ≫ e ≫ c` of two comparisons of composite functors and a transport along the
commutativity of the square; `a` has a retraction `a'`, the composite `c ≫ r` along one route is
a named morphism `θ₂`, the transport carries it to `θ₁` and `θ₁` factors through `a'`.  Then the
square comparison carries the composite along the second route to the composite along the first.

Both statements of this file are this lemma; stating it in an arbitrary category is what keeps
the associativity out of the geometric goals, as the implementation notes record. -/
theorem eq_square_comp_of_cancel {C : Type*} [Category C] {U₀ U₁ U₂ U₃ V : C}
    (a : U₀ ⟶ U₁) (a' : U₁ ⟶ U₀) (e : U₁ ⟶ U₂) (c : U₂ ⟶ U₃) (r : U₃ ⟶ V)
    (p : U₀ ⟶ V) (θ₁ : U₁ ⟶ V) (θ₂ : U₂ ⟶ V)
    (ha : a ≫ a' = 𝟙 U₀) (h₁ : θ₂ = c ≫ r) (h₂ : e ≫ θ₂ = θ₁) (h₃ : θ₁ = a' ≫ p) :
    p = (a ≫ e ≫ c) ≫ r := by
  rw [Category.assoc, Category.assoc, ← h₁, h₂, h₃, ← Category.assoc, ha, Category.id_comp]

/-- **The bookkeeping for a square comparison given as a natural transformation**, read at one
object: it carries the map along the first of the two comparisons to the composite along the
other route.  Everything structural happens here, with the morphisms as variables, so that a
consumer supplies the geometric terms and nothing else; see the implementation notes for why
that matters. -/
theorem eq_app_comp_of_split {C : Type*} [Category C] {D : Type*} [Category D]
    {F G H K : C ⥤ D} {Φ : F ⟶ K} (x : F ⟶ G) (y : G ⟶ H) (z : H ⟶ K)
    (hΦ : Φ = x ≫ y ≫ z) (M : C) {V : D} (r : K.obj M ⟶ V)
    (θ₁ : G.obj M ⟶ V) (θ₂ : H.obj M ⟶ V)
    (h₁ : θ₂ = z.app M ≫ r) (h₂ : y.app M ≫ θ₂ = θ₁) :
    x.app M ≫ θ₁ = Φ.app M ≫ r := by
  subst hΦ
  rw [natTrans_comp_comp_app, Category.assoc, Category.assoc, ← h₁, h₂]

/-- **Cancelling a retraction off the front of such an identity.** -/
theorem eq_of_cancel_comp {C : Type*} [Category C] {U₀ U₁ W V : C}
    (a : U₀ ⟶ U₁) (a' : U₁ ⟶ U₀) (θ : U₁ ⟶ V) (p : U₀ ⟶ V) (Ψ : U₀ ⟶ W) (r : W ⟶ V)
    (ha : a ≫ a' = 𝟙 U₀) (h : a ≫ θ = Ψ ≫ r) (h' : θ = a' ≫ p) :
    p = Ψ ≫ r := by
  rw [← h, h', ← Category.assoc, ha, Category.id_comp]

end CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The comparison `p^*𝒪 ⟶ 𝒪` is transported along an equality of morphisms.**  For
`e : p = q` the transport `p^* ⟶ q^*` followed by the comparison of `q` is the comparison of
`p`. -/
theorem eqToHom_app_comp_structureModulePullbackMap {W Y : AlgebraicSpaces B S hS}
    {p q : W ⟶ Y} (e : p = q) :
    (eqToHom (congrArg (fun h : W ⟶ Y ↦ modulePullback B S hS h) e)).app
          (structureUnitModule B S hS Y) ≫
        structureModulePullbackMap B S hS q =
      structureModulePullbackMap B S hS p := by
  subst e
  exact Category.id_comp _

end AlgebraicGeometry.Space

namespace RingedSpaceModuleAdjunction

open AlgebraicGeometry

variable {R₀ R₁ R₂ : AlgebraicGeometry.RingedSpace.{u, u}}

/-- **The comparison `p^*𝒪 ⟶ 𝒪` of ringed spaces is transported along an equality of
morphisms.** -/
theorem modulePullbackCongr_hom_app_comp_modulePullbackUnitToUnit {p q : R₀ ⟶ R₁} (e : p = q) :
    (modulePullbackCongr e).hom.app (SheafOfModules.unit (structureSheafRing R₁)) ≫
        modulePullbackUnitToUnit q =
      modulePullbackUnitToUnit p := by
  subst e
  exact Category.id_comp _

/-- **The composition comparison of pullbacks of modules is compatible with the maps to the
structure sheaves.**  The comparison `(f ≫ g)^*𝒪 ≅ g^*f^*𝒪` of [Stacks Project, Tag 0097] (2)
carries the map `(f ≫ g)^*𝒪_{R₂} ⟶ 𝒪_{R₀}` of pullback of regular functions along `f ≫ g` to the
composite `f^*g^*𝒪_{R₂} ⟶ f^*𝒪_{R₁} ⟶ 𝒪_{R₀}` of the maps of `g` and of `f`.

Both sides are morphisms out of a pullback, hence determined by their transposes, and
`RingedSpaceModuleAdjunction.conjugateEquiv_modulePullbackComp_hom` says that the comparison is
the mate of `RingedSpaceModuleAdjunction.modulePushforwardComp`, whose components are identity
morphisms; what is left is the cocycle condition
`RingedSpaceModuleAdjunction.structureSheafModuleHom_comp`, which holds on the nose. -/
theorem modulePullbackComp_hom_app_unit_comp (f : R₀ ⟶ R₁) (g : R₁ ⟶ R₂) :
    modulePullbackUnitToUnit (f ≫ g) =
      (modulePullbackComp f g).hom.app (SheafOfModules.unit (structureSheafRing R₂)) ≫
        (modulePullback f).map (modulePullbackUnitToUnit g) ≫ modulePullbackUnitToUnit f := by
  refine eq_comp_of_homEquiv_eq
    ((modulePullbackPushforwardAdjunction g).comp (modulePullbackPushforwardAdjunction f))
    (modulePullbackPushforwardAdjunction (f ≫ g)) (modulePullbackComp f g).hom
    (SheafOfModules.unit (structureSheafRing R₂))
    (SheafOfModules.unit (structureSheafRing R₀)) _ _ ?_
  rw [conjugateEquiv_modulePullbackComp_hom f g, Adjunction.comp_homEquiv, Equiv.trans_apply,
    Adjunction.homEquiv_naturality_left, homEquiv_modulePullbackUnitToUnit f,
    Adjunction.homEquiv_naturality_right, homEquiv_modulePullbackUnitToUnit g,
    homEquiv_modulePullbackUnitToUnit (f ≫ g)]
  exact (Category.comp_id _).symm

end RingedSpaceModuleAdjunction

namespace Stacks.ClosedImmersion

open _root_.Stacks.AlgebraicGeometry RingedSpaceModuleAdjunction

variable {Z Z' W W' : AlgebraicGeometry.RingedSpace.{u, u}} {i : Z ⟶ Z'} {j : W ⟶ W'}
    {f : Z ⟶ W} {k : Z' ⟶ W'}

/-- **The square comparison of [Stacks Project, Tag 01R4], read at the structure sheaf.**  Going
round the square by `f` and then `i`, the composite `f^*j^*𝒪_{W'} ⟶ f^*𝒪_W ⟶ 𝒪_Z` of the two maps
`RingedSpaceModuleAdjunction.modulePullbackUnitToUnit` of pullback of regular functions is, going
round it by `k` and then `i`, the comparison `Stacks.ClosedImmersion.pullbackCompIso` followed by
`i^*k^*𝒪_{W'} ⟶ i^*𝒪_{Z'} ⟶ 𝒪_Z`.

The proof is the composition law
`RingedSpaceModuleAdjunction.modulePullbackComp_hom_app_unit_comp` once on each side, with the
transport along the square's commutativity in between.  The spaces-side mirror of this statement
is the half of the comparison this file does not prove; the module documentation writes it out
and records what it costs. -/
theorem pullbackCompIso_hom_comp_modulePullbackUnitToUnit (comm : i ≫ k = f ≫ j) :
    (modulePullback f).map (modulePullbackUnitToUnit j) ≫ modulePullbackUnitToUnit f =
      (pullbackCompIso comm (SheafOfModules.unit (structureSheafRing W'))).hom ≫
        (modulePullback i).map (modulePullbackUnitToUnit k) ≫ modulePullbackUnitToUnit i := by
  have hsplit := pullbackCompIso_hom comm (SheafOfModules.unit (structureSheafRing W'))
  have hik := modulePullbackComp_hom_app_unit_comp i k
  have hfj := modulePullbackComp_hom_app_unit_comp f j
  have htr := modulePullbackCongr_hom_app_comp_modulePullbackUnitToUnit comm.symm
  have hcancel := Iso.inv_hom_id_app (modulePullbackComp f j)
    (SheafOfModules.unit (structureSheafRing W'))
  exact Eq.symm (Eq.trans (eq_whisker hsplit _)
    (eq_square_comp_of_cancel _ _ _ _ _ _ _ _ hcancel hik htr hfj).symm)

end Stacks.ClosedImmersion

end
