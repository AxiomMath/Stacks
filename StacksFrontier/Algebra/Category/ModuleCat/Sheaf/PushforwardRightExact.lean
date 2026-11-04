module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.EpiMono
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalizedRingedTopos
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExact
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.AlmostCocontinuousDefs
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.MorphismDefs
public import StacksCore.Tactic.StacksAttribute

/-!
# Right exactness of the direct image along an almost cocontinuous morphism of sites

Let `(C, J)` and `(D, K)` be sites and let `v : C ⥤ D` be a continuous functor, so that
restriction along `v.op` is the direct image `v^s = f_* : Sh(D) ⥤ Sh(C)` of the associated
morphism of sites `f : D → C`. Stacks 04BD says that if `v` is *almost cocontinuous* then

1. `f_* : Ab(D) ⥤ Ab(C)` is exact, and
2. if `f` is made a morphism of ringed sites by `f^♯`, then
   `f_* : Mod(O_D) ⥤ Mod(O_C)` is exact.

The **left exact** halves of both are already in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PushforwardExact.lean`, where they are proved for
every continuous `v` with no use of almost cocontinuity. This file proves the **right exact**
halves, which is where almost cocontinuity is consumed, and assembles the two into the
`CategoryTheory.exactFunctor` statements of the source.

The route is not the source's. Stacks deduces (1) from Sites 04BA (`f_*` commutes with connected
colimits of sheaves of **sets**) through Sites 04D6 and Modules 04DB, and (2) from (1) through
Modules 03DB. Here almost cocontinuity is instead consumed once, directly on sections:
*almost cocontinuity transports local surjectivity along `f_*`*. That single lemma
(`CategoryTheory.Presheaf.isLocallySurjective_whiskerLeft_of_isAlmostCocontinuous`) holds for
sheaves valued in an arbitrary concrete category, so it serves (1) and (2) equally and neither has
to be deduced from the other; 04BA, 04D6, 04DB and 03DB are not used. Given it, an epimorphism of
sheaves is locally surjective, its direct image is locally surjective, hence an epimorphism; and a
left exact additive functor between abelian categories that preserves epimorphisms preserves
homology and is therefore right exact.

A final, independent section proves the two site-theoretic halves of Stacks 04J4 that were
outstanding, namely that postcomposition of sections `(U, g) ↦ (U, g ≫ s)` along a morphism of
sheaves `s : G ⟶ F` is continuous and cocontinuous for the topologies of the sites of elements. It
builds on `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/LocalizedRingedTopos.lean` and belongs
beside it; it is here because this is the module the author of 04BD owns.

## Main definitions

For 04BD this file introduces no new definitions. For 04J4 it introduces

* `Stacks.Sheaves.LocalizedRingedTopos.underlyingSieve` — the sieve on `Us.left` underlying a
  sieve on the object `Us` of the site of elements.
* `Stacks.Sheaves.LocalizedRingedTopos.liftedTopology` — the topology on the site of elements
  obtained by transporting `X.J` through that correspondence. It is `elementTopology`.
* `Stacks.Sheaves.LocalizedRingedTopos.elementPostcomp` — postcomposition of sections, as a
  functor between sites of elements.

## Main results

* `CategoryTheory.Presheaf.isLocallySurjective_whiskerLeft_of_isAlmostCocontinuous`: the
  mathematical core. For an almost cocontinuous `v : C ⥤ D` and a locally surjective morphism
  `α : P ⟶ Q` of `K`-sheaves valued in a concrete category, `v.op ⋙ α` is locally surjective for
  `J`. This is the only place almost cocontinuity is used.
* `CategoryTheory.Sheaf.preservesEpimorphisms_sheafPushforwardContinuous_of_isAlmostCocontinuous`:
  the direct image `Sheaf K A ⥤ Sheaf J A` preserves epimorphisms.
* `CategoryTheory.Functor.exactFunctor_sheafPushforwardContinuous_of_isAlmostCocontinuous`:
  **Stacks 04BD (1)**, the direct image on sheaves of abelian groups is exact.
* `Stacks.SheafOfModules.PushforwardRightExact.exactFunctor_pushforward_of_isAlmostCocontinuous`:
  **Stacks 04BD (2)**, the direct image on sheaves of modules is exact.
* `exactFunctor_pushforward_of_isAlmostCocontinuous_of_univLE` in the same namespace: the same,
  with the four sheafification hypotheses replaced by the one universe inequality
  `max uC vC uD vD ≤ m` they all follow from.
* The two `..._of_smallCategory` corollaries are those same two statements for sites that are
  small categories with sheaves in the site's own universe, i.e. the Stacks convention, where the
  sheafification hypotheses discussed below are discharged by instance resolution, so that the
  statements carry only the hypotheses of the source.
* `Stacks.Sheaves.LocalizedRingedTopos.underlyingSieve_mem`: **the harder half of Stacks 0791**
  for the site of elements, the converse of
  `Stacks.Sheaves.LocalizedRingedTopos.mem_elementTopology_of_forall_liftHom` — a covering sieve
  of the site of elements has covering underlying sieve.
* `Stacks.Sheaves.LocalizedRingedTopos.elementPostcomp_isContinuous` and
  `elementPostcomp_isCocontinuous`: **Stacks 04J4**, continuity and cocontinuity of
  postcomposition of sections. The `04J4` registration sits on the bare-site forms
  `Stacks.Sheaves.LocalizedRingedTopos.OverSite.elementPostcomp_isContinuous` and
  `OverSite.elementPostcomp_isCocontinuous`, which state the same results with no ringed
  structure in their hypotheses.

## Implementation notes

**Added hypotheses (sheafification), and why they are the source's.** Right exactness is a
statement about colimits, so unlike the left exact halves it needs the categories of sheaves to be
abelian, and Mathlib's `CategoryTheory.sheafIsAbelian` and the `Abelian (SheafOfModules R)`
instance supply that from `HasSheafify` together with
`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective` (sheafification inverts exactly the
locally bijective morphisms of presheaves). Those are facts, not restrictions, in the setting of
the source: Stacks' sites are small categories and its sheaves take values in the site's own
universe, and there both are theorems — which is what the `..._of_smallCategory` corollaries
record, since they state 04BD with no hypothesis the source does not have.

Neither is a hypothesis of **part (1)**. Mathlib's instances for both ask the carrier types to lie
in the site's own `Type (max u v)`, and `Type (max uC vC uD vD)` is not that for either site; but
neither argument needs the equality, only the inequality `max u v ≤ max uC vC uD vD`, which holds
for both sites by construction. The `UnivLE` forms are
`CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat` and
`CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat`, both in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PushforwardExact.lean`. So part (1) is stated over
four unrelated site universes with exactly the source's hypotheses.

**Part (2)** cannot be. Its module universe `m` is a variable unrelated to the sites, and for `m`
below them sheafification of `AddCommGrpCat.{m}`-valued presheaves need not exist at all. What the
`UnivLE` forms buy here is that all four instance hypotheses — `HasSheafify` and
`WEqualsLocallyBijective`, for each of the two sites — are consequences of the *single* inequality
`max uC vC uD vD ≤ m`, which is how
`exactFunctor_pushforward_of_isAlmostCocontinuous_of_univLE` states it. That inequality is an
instance at `m = max uC vC uD vD`, so at the module universe the two sites force, part (2) too
holds with no hypothesis beyond the source's. The four-hypothesis form is kept alongside it
because the four instances do not imply the inequality.

**Universes.** Nothing is narrowed relative to the source: the two sites keep four
unrelated universes, the value category of the core lemma and of the epimorphism-preservation
statement is arbitrary, and in part (2) the module universe `m` and the ring universe `r` stay
independent. The epimorphism/locally surjective dictionary for sheaves of modules that part (2)
consumes is cited from `Stacks.SheafOfModules.EpiMono` in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/EpiLocallySurjective.lean`, which states it with the
module universe independent of the ring universe, so no copy of it is needed here.

**Why `PreservesEpimorphisms` and not cokernels.**
`CategoryTheory.Functor.preservesHomology_of_preservesEpis_and_kernels` needs the functor to
preserve zero morphisms, and that cannot be had from left exactness without already knowing
additivity (`CategoryTheory.Functor.additive_of_preserves_binary_products` asks for
`PreservesZeroMorphisms`). Additivity is therefore established directly, by `rfl`: morphisms of
sheaves are morphisms of the underlying presheaves, addition of natural transformations is
pointwise, and restriction along `v.op` only reindexes components.

**The sheaf theoretically empty case.** Almost cocontinuity refines a covering of `v U` to a
covering of `U` each of whose members either maps into the given covering or has sheaf
theoretically empty image. On the second kind there is nothing to do, because a sheaf has exactly
one section over an object carried by the empty covering
(`CategoryTheory.Presheaf.exists_eq_section_of_sheafTheoreticallyEmptySite`), so there every
morphism of sheaves is surjective on sections. This is the step for which the source invokes Sites
04B7 and 04B8, and it is the only use of `[K.HasSheafCompose (forget A)]`: that hypothesis moves
the sheaf condition to the underlying presheaf of types, where "the empty sieve covers" literally
says the sections form a singleton.

**The site of elements (04J4).** Every arrow of `CostructuredArrow yoneda F.obj` with target `Us`
is determined by its underlying arrow of `X.C` with target `Us.left`, because the section over the
source is forced to be the restriction of `Us.hom`. Hence sieves on `Us` correspond to sieves on
`Us.left`, compatibly with pullback — that is `mem_sieve_iff_liftHom` and
`underlyingSieve_pullback`. Transporting `X.J` through the correspondence therefore *is* a
Grothendieck topology, `liftedTopology`, and since `elementTopology` is the coarsest topology
whose sieves push forward to coverings, `elementTopology ≤ liftedTopology`; the other inclusion is
`mem_elementTopology_of_forall_liftHom`. This is how the harder half of Stacks 0791 is
obtained without Mathlib's `Functor.mem_restrictedTopology_iff`, whose `IsLocallyFull` hypothesis
fails for the projection of the site of elements. Given it, cocontinuity and cover preservation of
`elementPostcomp` are immediate, since postcomposition does not change underlying arrows;
continuity then follows from cover preservation together with compatible preservation, which holds
because a map `W ⟶ v Y₁` of the site of elements of `F` exhibits `W.hom` as factoring through `s`,
so `W` is isomorphic to the image of an object of the site of elements of `G` by an isomorphism
that is the identity on underlying objects.

## References

* [Stacks Project, Tag 04BD](https://stacks.math.columbia.edu/tag/04BD)
* [Stacks Project, Tag 04B7](https://stacks.math.columbia.edu/tag/04B7)
* [Stacks Project, Tag 04BA](https://stacks.math.columbia.edu/tag/04BA)
* [Stacks Project, Tag 04J4](https://stacks.math.columbia.edu/tag/04J4)
* [Stacks Project, Tag 0791](https://stacks.math.columbia.edu/tag/0791)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u uC vC uD vD m r

namespace CategoryTheory.Presheaf

section Empty

variable {D : Type*} [Category* D] (K : GrothendieckTopology D)
  {A : Type*} [Category* A] {FA : A → A → Type*} {CA : A → Type w}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w} A FA]
  [K.HasSheafCompose (forget A)]

/-- A sheaf has exactly one section over a sheaf theoretically empty object (Stacks 04B5): the
empty sieve covers it, and the empty family of sections has a unique amalgamation. -/
@[sga "4 II 4.6.2" "partial"]
public theorem exists_eq_section_of_sheafTheoreticallyEmptySite
    {P : Dᵒᵖ ⥤ A} (hP : IsSheaf K P) {V : D} (hV : SheafTheoreticallyEmptySite K V) :
    ∃ t : ToType (P.obj (op V)), ∀ s : ToType (P.obj (op V)), s = t := by
  have h : Presieve.IsSheaf K (P ⋙ forget A) :=
    (isSheaf_iff_isSheaf_of_type K _).1 (GrothendieckTopology.HasSheafCompose.isSheaf P hP)
  obtain ⟨t, -, ht⟩ := h (⊥ : Sieve V) hV (fun _ _ h ↦ ((Sieve.bot_apply _).1 h).elim)
    (by intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ _; exact ((Sieve.bot_apply _).1 h₁).elim)
  exact ⟨t, fun s ↦ ht s (by intro Y f hf; exact ((Sieve.bot_apply _).1 hf).elim)⟩

/-- Over a sheaf theoretically empty object every morphism of sheaves is surjective on sections,
both source and target having exactly one section there. -/
public theorem exists_app_eq_of_sheafTheoreticallyEmptySite
    {P Q : Dᵒᵖ ⥤ A} (hP : IsSheaf K P) (hQ : IsSheaf K Q) (α : P ⟶ Q)
    {V : D} (hV : SheafTheoreticallyEmptySite K V) (s : ToType (Q.obj (op V))) :
    ∃ t : ToType (P.obj (op V)), α.app (op V) t = s := by
  obtain ⟨t, -⟩ := exists_eq_section_of_sheafTheoreticallyEmptySite K hP hV
  obtain ⟨tQ, hQ'⟩ := exists_eq_section_of_sheafTheoreticallyEmptySite K hQ hV
  exact ⟨t, (hQ' _).trans (hQ' s).symm⟩

end Empty

section Transfer

variable {C : Type*} [Category* C] {D : Type*} [Category* D]
  {A : Type*} [Category* A] {FA : A → A → Type*} {CA : A → Type w}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w} A FA]

/-- **The core of Stacks 04BD.** Let `v : C ⥤ D` be almost cocontinuous (Stacks 04B7) for the
topologies `J` on `C` and `K` on `D`, and let `α : P ⟶ Q` be a locally surjective morphism of
`K`-sheaves valued in a concrete category. Then the restriction of `α` along `v.op`, which is the
direct image of `α`, is locally surjective for `J`.

Given `U : C` and a section `s` of `Q` over `v U`, local surjectivity of `α` makes the sieve of
arrows into `v U` along which `s` lifts to `P` a covering sieve, and almost cocontinuity refines it
to a `J`-covering sieve of `U` each of whose arrows `f : W ⟶ U` either has `v f` in that sieve —
and then `s` lifts over `v W` — or has `v W` sheaf theoretically empty, in which case `s` lifts
over `v W` because there is only one section there. -/
public theorem isLocallySurjective_whiskerLeft_of_isAlmostCocontinuous
    {v : C ⥤ D} {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget A)] (hv : IsAlmostCocontinuous v J K)
    {P Q : Dᵒᵖ ⥤ A} (hP : IsSheaf K P) (hQ : IsSheaf K Q) {α : P ⟶ Q}
    (hα : IsLocallySurjective K α) :
    IsLocallySurjective J (Functor.whiskerLeft v.op α) := by
  have := hα
  constructor
  intro U s
  obtain ⟨T, hT, hle⟩ := hv U (imageSieve_mem K α (U := op (v.obj U)) s)
  refine J.superset_covering (fun W f hf ↦ ?_) hT
  rcases hle f hf with hemp | ⟨t, ht⟩
  · exact exists_app_eq_of_sheafTheoreticallyEmptySite K hP hQ α hemp _
  · exact ⟨t, ht⟩

end Transfer

end CategoryTheory.Presheaf

namespace CategoryTheory.Sheaf

variable {C : Type*} [Category* C] {D : Type*} [Category* D]
  {A : Type*} [Category* A] {FA : A → A → Type*} {CA : A → Type w}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w} A FA]
  (v : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [v.IsContinuous J K]

/-- The direct image along an almost cocontinuous continuous functor takes locally surjective
morphisms of sheaves to locally surjective morphisms. -/
public theorem isLocallySurjective_sheafPushforwardContinuous_map_of_isAlmostCocontinuous
    [K.HasSheafCompose (forget A)] (hv : IsAlmostCocontinuous v J K)
    {F G : Sheaf K A} {α : F ⟶ G} (hα : IsLocallySurjective α) :
    IsLocallySurjective ((v.sheafPushforwardContinuous A J K).map α) :=
  Presheaf.isLocallySurjective_whiskerLeft_of_isAlmostCocontinuous hv F.property G.property hα

/-- The direct image `Sheaf K A ⥤ Sheaf J A` along an almost cocontinuous continuous functor
preserves epimorphisms: an epimorphism of `K`-sheaves is locally surjective, local surjectivity is
preserved, and a locally surjective morphism of `J`-sheaves is an epimorphism. Only the first of
those three steps needs the sheafification hypotheses, and only on `K`. -/
public theorem preservesEpimorphisms_sheafPushforwardContinuous_of_isAlmostCocontinuous
    [HasSheafify K A] [K.WEqualsLocallyBijective A]
    [ConcreteCategory.HasFunctorialSurjectiveInjectiveFactorization A]
    [K.HasSheafCompose (forget A)] [J.HasSheafCompose (forget A)] [Balanced (Sheaf K A)]
    (hv : IsAlmostCocontinuous v J K) :
    (v.sheafPushforwardContinuous A J K).PreservesEpimorphisms where
  preserves {F G} α hα := by
    have := isLocallySurjective_sheafPushforwardContinuous_map_of_isAlmostCocontinuous v J K hv
      ((isLocallySurjective_iff_epi' (A := A) (φ := α)).2 hα)
    infer_instance

end CategoryTheory.Sheaf

namespace CategoryTheory.Functor

section General

variable {C : Type*} [Category* C] {D : Type*} [Category* D]
  (v : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [v.IsContinuous J K]

/-- The direct image of sheaves valued in a preadditive category is additive: on underlying
presheaves it is restriction along `v.op`, which only reindexes the components of a natural
transformation, and addition of natural transformations is pointwise. -/
public instance additive_sheafPushforwardContinuous
    (A : Type*) [Category* A] [Preadditive A] :
    (v.sheafPushforwardContinuous A J K).Additive where
  map_add := rfl

/-- **Right exact half of Stacks 04BD (1).** The direct image of sheaves of abelian groups along an
almost cocontinuous continuous functor preserves finite colimits: it is additive, it preserves
finite limits and hence kernels for every continuous functor, and it preserves epimorphisms by
almost cocontinuity, so it preserves homology and therefore finite colimits. -/
public theorem preservesFiniteColimits_sheafPushforwardContinuous_of_isAlmostCocontinuous
    [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (hv : IsAlmostCocontinuous v J K) :
    PreservesFiniteColimits (v.sheafPushforwardContinuous AddCommGrpCat.{w} J K) := by
  have := Sheaf.preservesEpimorphisms_sheafPushforwardContinuous_of_isAlmostCocontinuous
    (A := AddCommGrpCat.{w}) v J K hv
  have := preservesHomology_of_preservesEpis_and_kernels
    (L := v.sheafPushforwardContinuous AddCommGrpCat.{w} J K)
  exact preservesFiniteColimits_of_preservesHomology _

end General

/-- **Stacks 04BD (1).** Let `f : D → C` be a morphism of sites associated to the continuous
functor `v : C ⥤ D`, and assume `v` is almost cocontinuous. Then the direct image
`f_* = v^s : Ab(D) ⥤ Ab(C)`, restriction of sheaves of abelian groups along `v.op`, is exact.

The four site universes are unrelated and there is no hypothesis beyond the source's. Both
sheafification facts the right exact half needs — existence, and that sheafification inverts
exactly the locally bijective morphisms, which is what makes `Sheaf K AddCommGrpCat` abelian —
are available at the universe `max uC vC uD vD` that a statement about two sites at once is
forced to use, because that universe dominates each site's own `max u v`; see
`CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat` and
`CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat`. -/
@[stacks 04BD "part (1)"]
public theorem exactFunctor_sheafPushforwardContinuous_of_isAlmostCocontinuous
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {v : C ⥤ D}
    (hv : IsMorphismOfSites.{max uC vC uD vD} v J K)
    (ha : IsAlmostCocontinuous v J K) :
    letI : v.IsContinuous J K := hv.toIsContinuous
    exactFunctor (Sheaf K AddCommGrpCat.{max uC vC uD vD})
      (Sheaf J AddCommGrpCat.{max uC vC uD vD})
      (v.sheafPushforwardContinuous AddCommGrpCat.{max uC vC uD vD} J K) := by
  let : v.IsContinuous J K := hv.toIsContinuous
  have : UnivLE.{max uC vC, max uC vC uD vD} := ⟨fun α ↦ small_max.{max uD vD} α⟩
  have : UnivLE.{max uD vD, max uC vC uD vD} := ⟨fun α ↦ small_max.{max uC vC} α⟩
  have : HasSheafify J AddCommGrpCat.{max uC vC uD vD} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat J
  have : HasSheafify K AddCommGrpCat.{max uC vC uD vD} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat K
  have : K.WEqualsLocallyBijective AddCommGrpCat.{max uC vC uD vD} :=
    GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat K
  exact ⟨preservesFiniteLimits_sheafPushforwardContinuous J K v _,
    preservesFiniteColimits_sheafPushforwardContinuous_of_isAlmostCocontinuous v J K ha⟩

/-- **Stacks 04BD (1)** for sites that are small categories, with sheaves of abelian groups in the
site's own universe: the setting of the source, in which the hypotheses are exactly the source's,
namely a morphism of sites whose continuous functor is almost cocontinuous. -/
@[stacks 04BD "part (1), for small sites"]
public theorem exactFunctor_sheafPushforwardContinuous_of_isAlmostCocontinuous_of_smallCategory
    {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {v : C ⥤ D}
    (hv : IsMorphismOfSites.{u} v J K) (ha : IsAlmostCocontinuous v J K) :
    letI : v.IsContinuous J K := hv.toIsContinuous
    exactFunctor (Sheaf K AddCommGrpCat.{u}) (Sheaf J AddCommGrpCat.{u})
      (v.sheafPushforwardContinuous AddCommGrpCat.{u} J K) := by
  let : v.IsContinuous J K := hv.toIsContinuous
  exact ⟨preservesFiniteLimits_sheafPushforwardContinuous J K v _,
    preservesFiniteColimits_sheafPushforwardContinuous_of_isAlmostCocontinuous v J K ha⟩

end CategoryTheory.Functor

namespace Stacks.SheafOfModules.PushforwardRightExact

section Pushforward

variable {C : Type*} [Category* C] {D : Type*} [Category* D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} (v : C ⥤ D) [v.IsContinuous J K]
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  (φ : S ⟶ (v.sheafPushforwardContinuous RingCat.{u} J K).obj R)

/-- The direct image of sheaves of modules is additive, for the same reason as on sheaves of
abelian groups: on underlying presheaves it is restriction along `v.op`. -/
public instance additive_pushforward : (SheafOfModules.pushforward.{v} φ).Additive where
  map_add := rfl

variable [HasSheafify J AddCommGrpCat.{v}] [HasSheafify K AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}] [K.WEqualsLocallyBijective AddCommGrpCat.{v}]

omit [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}] in
/-- The direct image of sheaves of modules along an almost cocontinuous continuous functor
preserves epimorphisms. The underlying morphism of presheaves of abelian groups of the direct image
of `f` is the restriction of that of `f` along `v.op`, so this is the local surjectivity transfer
between the two halves of the epimorphism/locally surjective dictionary for sheaves of modules. -/
public theorem preservesEpimorphisms_pushforward_of_isAlmostCocontinuous
    (hv : IsAlmostCocontinuous v J K) :
    (SheafOfModules.pushforward.{v} φ).PreservesEpimorphisms where
  preserves {M N} f hf := by
    have h0 : Epi f := hf
    have h1 : Presheaf.IsLocallySurjective K
        ((PresheafOfModules.toPresheaf R.obj).map f.val) := EpiMono.isLocallySurjective_of_epi f
    have h2 : Presheaf.IsLocallySurjective J (Functor.whiskerLeft v.op
        ((PresheafOfModules.toPresheaf R.obj).map f.val)) :=
      Presheaf.isLocallySurjective_whiskerLeft_of_isAlmostCocontinuous hv M.isSheaf N.isSheaf h1
    exact EpiMono.epi_of_isLocallySurjective _ h2

/-- **Right exact half of Stacks 04BD (2).** The direct image of sheaves of modules along an almost
cocontinuous continuous functor preserves finite colimits. -/
public theorem preservesFiniteColimits_pushforward_of_isAlmostCocontinuous
    (hv : IsAlmostCocontinuous v J K) :
    PreservesFiniteColimits (SheafOfModules.pushforward.{v} φ) := by
  have := preservesEpimorphisms_pushforward_of_isAlmostCocontinuous v φ hv
  have := Functor.preservesHomology_of_preservesEpis_and_kernels
    (L := SheafOfModules.pushforward.{v} φ)
  exact Functor.preservesFiniteColimits_of_preservesHomology _

end Pushforward

/-- **Stacks 04BD (2).** Let `f : D → C` be a morphism of sites associated to the continuous
functor `v : C ⥤ D` with `v` almost cocontinuous, and let `f^♯ : S ⟶ f_* R` make `f` a morphism of
ringed sites. Then the direct image `f_* : Mod(R) ⥤ Mod(S)` is exact.

As in part (1) this additionally assumes that sheafification of `AddCommGrpCat.{m}`-valued
presheaves exists and inverts exactly the locally bijective morphisms, for both topologies; that is
what makes the two categories of sheaves of modules abelian, and it holds automatically in the
setting of the source, as recorded by
`exactFunctor_pushforward_of_isAlmostCocontinuous_of_smallCategory`. -/
@[stacks 04BD "part (2)"]
public theorem exactFunctor_pushforward_of_isAlmostCocontinuous
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {v : C ⥤ D}
    (hv : IsMorphismOfSites.{max uC vC uD vD} v J K)
    (ha : IsAlmostCocontinuous v J K)
    {S : Sheaf J RingCat.{r}} {R : Sheaf K RingCat.{r}}
    (φ : letI : v.IsContinuous J K := hv.toIsContinuous
      S ⟶ (v.sheafPushforwardContinuous RingCat.{r} J K).obj R)
    [HasSheafify J AddCommGrpCat.{m}] [HasSheafify K AddCommGrpCat.{m}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{m}] :
    letI : v.IsContinuous J K := hv.toIsContinuous
    exactFunctor (SheafOfModules.{m} R) (SheafOfModules.{m} S)
      (SheafOfModules.pushforward φ) := by
  let : v.IsContinuous J K := hv.toIsContinuous
  exact ⟨SheafOfModules.preservesFiniteLimits_pushforward φ,
    preservesFiniteColimits_pushforward_of_isAlmostCocontinuous v φ ha⟩

/-- **Stacks 04BD (2)** with the four sheafification hypotheses replaced by the single universe
inequality they follow from: the module universe `m` dominates both sites. This is the sharpest
form the statement takes with `m` still a variable — at `m = max uC vC uD vD` the inequality is
an instance, so there the statement holds with no hypothesis beyond the source's. -/
@[stacks 04BD "part (2)"]
public theorem exactFunctor_pushforward_of_isAlmostCocontinuous_of_univLE
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {v : C ⥤ D}
    (hv : IsMorphismOfSites.{max uC vC uD vD} v J K)
    (ha : IsAlmostCocontinuous v J K)
    {S : Sheaf J RingCat.{r}} {R : Sheaf K RingCat.{r}}
    (φ : letI : v.IsContinuous J K := hv.toIsContinuous
      S ⟶ (v.sheafPushforwardContinuous RingCat.{r} J K).obj R)
    [UnivLE.{max uC vC uD vD, m}] :
    letI : v.IsContinuous J K := hv.toIsContinuous
    exactFunctor (SheafOfModules.{m} R) (SheafOfModules.{m} S)
      (SheafOfModules.pushforward φ) := by
  have h₁ : UnivLE.{max uC vC, max uC vC uD vD} := ⟨fun α ↦ small_max.{max uD vD} α⟩
  have h₂ : UnivLE.{max uD vD, max uC vC uD vD} := ⟨fun α ↦ small_max.{max uC vC} α⟩
  have : UnivLE.{max uC vC, m} :=
    @UnivLE.trans.{max uC vC, max uC vC uD vD, m} h₁ inferInstance
  have : UnivLE.{max uD vD, m} :=
    @UnivLE.trans.{max uD vD, max uC vC uD vD, m} h₂ inferInstance
  have : HasSheafify J AddCommGrpCat.{m} := GrothendieckTopology.hasSheafify_addCommGrpCat J
  have : HasSheafify K AddCommGrpCat.{m} := GrothendieckTopology.hasSheafify_addCommGrpCat K
  have : J.WEqualsLocallyBijective AddCommGrpCat.{m} :=
    GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat J
  have : K.WEqualsLocallyBijective AddCommGrpCat.{m} :=
    GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat K
  exact exactFunctor_pushforward_of_isAlmostCocontinuous hv ha φ

/-- **Stacks 04BD (2)** for sites that are small categories, with the sheaf of rings and the
sheaves of modules in the site's own universe: the setting of the source, in which the hypotheses
are exactly the source's. -/
@[stacks 04BD "part (2), for small sites"]
public theorem exactFunctor_pushforward_of_isAlmostCocontinuous_of_smallCategory
    {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {v : C ⥤ D}
    (hv : IsMorphismOfSites.{u} v J K) (ha : IsAlmostCocontinuous v J K)
    {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
    (φ : letI : v.IsContinuous J K := hv.toIsContinuous
      S ⟶ (v.sheafPushforwardContinuous RingCat.{u} J K).obj R) :
    letI : v.IsContinuous J K := hv.toIsContinuous
    exactFunctor (SheafOfModules.{u} R) (SheafOfModules.{u} S)
      (SheafOfModules.pushforward φ) := by
  let : v.IsContinuous J K := hv.toIsContinuous
  exact ⟨SheafOfModules.preservesFiniteLimits_pushforward φ,
    preservesFiniteColimits_pushforward_of_isAlmostCocontinuous v φ ha⟩

end Stacks.SheafOfModules.PushforwardRightExact

namespace Stacks.Sheaves.LocalizedRingedTopos

open Stacks.Sheaves.LocallyRingedTopos

/-! ### The site of elements over a bare site

The constructions below repeat the ones of the main namespace over a bare site `(C, J)` and
sheaves of sets on it, with the object and morphism universes of the site left independent and no
structure sheaf involved. The `RingedTopos` versions in the main namespace are the ones the rest
of the library consumes and are kept exactly as they are. -/

namespace OverSite

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  {F G : Sheaf J (Type vC)}

/-- An arrow of the site of elements belongs to a sieve exactly when the canonical lift of its
underlying arrow does. -/
public theorem mem_sieve_iff_liftHom {Us : elementSite F} (T : Sieve Us)
    {A : elementSite F} (α : A ⟶ Us) : T α ↔ T (liftHom Us α.left) := by
  have e₁ : (CostructuredArrow.homMk (𝟙 A.left)
      (by simp) :
      CostructuredArrow.mk (yoneda.map α.left ≫ Us.hom) ⟶ A) ≫ α = liftHom Us α.left :=
    CostructuredArrow.hom_ext _ _ (by simp)
  have e₂ : (CostructuredArrow.homMk (𝟙 A.left)
      (by simp) :
      A ⟶ CostructuredArrow.mk (yoneda.map α.left ≫ Us.hom)) ≫ liftHom Us α.left = α :=
    CostructuredArrow.hom_ext _ _ (by simp)
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← e₁]; exact T.downward_closed h _
  · rw [← e₂]; exact T.downward_closed h _

/-- The sieve on `Us.left` underlying a sieve on the object `Us` of the site of elements: the
arrows whose canonical lift belongs to the given sieve. -/
public def underlyingSieve {Us : elementSite F} (T : Sieve Us) : Sieve Us.left where
  arrows _ g := T (liftHom Us g)
  downward_closed := by
    intro V W g hg k
    have e : (CostructuredArrow.homMk k (by simp) :
        CostructuredArrow.mk (yoneda.map (k ≫ g) ≫ Us.hom) ⟶
          CostructuredArrow.mk (yoneda.map g ≫ Us.hom)) ≫ liftHom Us g =
        liftHom Us (k ≫ g) :=
      CostructuredArrow.hom_ext _ _ (by simp)
    rw [show (liftHom Us (k ≫ g)) = _ from e.symm]
    exact T.downward_closed hg _

/-- `underlyingSieve` commutes with pullback: the underlying sieve of `T.pullback α` is the
pullback of the underlying sieve of `T` along `α.left`. -/
public lemma underlyingSieve_pullback {Us A : elementSite F} (T : Sieve Us) (α : A ⟶ Us) :
    underlyingSieve (T.pullback α) = (underlyingSieve T).pullback α.left :=
  Sieve.ext fun _ g ↦ mem_sieve_iff_liftHom T (liftHom A g ≫ α)

/-- The topology on the site of elements transported from `J` through the bijection between
sieves on `Us` and sieves on `Us.left`. It is `elementTopology F`; stating it separately is what
gives the harder half of that identification. -/
public def liftedTopology (F : Sheaf J (Type vC)) :
    GrothendieckTopology (elementSite F) where
  sieves Us := {T | underlyingSieve T ∈ J Us.left}
  top_mem' Us := by
    have e : underlyingSieve (⊤ : Sieve Us) = ⊤ := Sieve.ext fun _ _ ↦ Iff.rfl
    change underlyingSieve (⊤ : Sieve Us) ∈ J Us.left
    rw [e]
    exact J.top_mem _
  pullback_stable' Us A T α hT := by
    change underlyingSieve (T.pullback α) ∈ J A.left
    rw [underlyingSieve_pullback]
    exact J.pullback_stable α.left hT
  transitive' Us T hT R h := by
    change underlyingSieve R ∈ J Us.left
    refine J.transitive hT _ ?_
    intro V g hg
    have h2 : underlyingSieve (R.pullback (liftHom Us g)) ∈ J V := h (f := liftHom Us g) hg
    rw [underlyingSieve_pullback] at h2
    exact h2

/-- The topology on the site of elements is contained in `liftedTopology`: it is generated by the
sieves whose pushforward along the projection covers, and every such sieve has covering underlying
sieve because the pushforward is contained in it. -/
public theorem elementTopology_le_liftedTopology :
    elementTopology F ≤ liftedTopology F := by
  apply Precoverage.toGrothendieck_le_iff_le_toPrecoverage.mpr
  intro Us R hR
  rw [Precoverage.mem_comap_iff, GrothendieckTopology.mem_toPrecoverage_iff,
    Sieve.generate_map_eq_functorPushforward] at hR
  show underlyingSieve (Sieve.generate R) ∈ J Us.left
  refine J.superset_covering ?_ hR
  rintro _ g ⟨A, α, k, hα, rfl⟩
  exact (underlyingSieve (Sieve.generate R)).downward_closed
    ((mem_sieve_iff_liftHom _ α).1 hα) k

/-- **The harder half of Stacks 0791 for the site of elements**, and the converse of
`mem_elementTopology_of_forall_liftHom`: a covering sieve of the site of elements has covering
underlying sieve. -/
public theorem underlyingSieve_mem {Us : elementSite F} {T : Sieve Us}
    (hT : T ∈ elementTopology F Us) : underlyingSieve T ∈ J Us.left := by
  exact elementTopology_le_liftedTopology _ hT

/-- Postcomposition of sections with `s : G ⟶ F`, as a functor between the sites of elements. -/
public abbrev elementPostcomp (s : G ⟶ F) : elementSite G ⥤ elementSite F :=
  CostructuredArrow.map s.hom

/-- **Stacks 04J4, cocontinuity of postcomposition.** -/
@[stacks 04J4 "cocontinuity of postcomposition"]
public theorem elementPostcomp_isCocontinuous (s : G ⟶ F) :
    (elementPostcomp s).IsCocontinuous (elementTopology G) (elementTopology F) where
  cover_lift {U S} hS := by
    have hS' : underlyingSieve S ∈ J U.left := underlyingSieve_mem hS
    refine mem_elementTopology_of_forall_liftHom hS' ?_
    intro V g hg
    exact (mem_sieve_iff_liftHom S ((elementPostcomp s).map (liftHom U g))).2 hg

/-- Postcomposition of sections preserves covering sieves. -/
public theorem coverPreserving_elementPostcomp (s : G ⟶ F) :
    CoverPreserving (elementTopology G) (elementTopology F) (elementPostcomp s) where
  cover_preserve {U T} hT := by
    have hT' : underlyingSieve T ∈ J ((elementPostcomp s).obj U).left :=
      underlyingSieve_mem hT
    refine mem_elementTopology_of_forall_liftHom hT' ?_
    intro V g hg
    exact (mem_sieve_iff_liftHom _ ((elementPostcomp s).map (liftHom U g))).1
      ⟨_, liftHom U g, 𝟙 _, hg, by simp⟩

/-- Postcomposition of sections is compatible-preserving. -/
public theorem compatiblePreserving_elementPostcomp (s : G ⟶ F) :
    CompatiblePreserving.{max uC vC} (elementTopology F) (elementPostcomp s) where
  compatible ℱ {Z T x} hx {Y₁ Y₂ W} f₁ f₂ {g₁ g₂} hg₁ hg₂ e := by
    have el : f₁.left ≫ g₁.left = f₂.left ≫ g₂.left := congrArg CommaMorphism.left e
    let W' : elementSite G := CostructuredArrow.mk (yoneda.map f₁.left ≫ Y₁.hom)
    have w₂ : yoneda.map f₂.left ≫ Y₂.hom = yoneda.map f₁.left ≫ Y₁.hom := by
      rw [← CostructuredArrow.w g₁, ← CostructuredArrow.w g₂, ← Category.assoc,
        ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp, el]
    let h₁ : W' ⟶ Y₁ := CostructuredArrow.homMk f₁.left rfl
    let h₂ : W' ⟶ Y₂ := CostructuredArrow.homMk f₂.left w₂
    let ι : W ⟶ (elementPostcomp s).obj W' :=
      CostructuredArrow.homMk (𝟙 W.left) (by simpa [W'] using CostructuredArrow.w f₁)
    have ef₁ : f₁ = ι ≫ (elementPostcomp s).map h₁ :=
      CostructuredArrow.hom_ext _ _ (by simp [ι, h₁])
    have ef₂ : f₂ = ι ≫ (elementPostcomp s).map h₂ :=
      CostructuredArrow.hom_ext _ _ (by simp [ι, h₂])
    have hcomp : h₁ ≫ g₁ = h₂ ≫ g₂ :=
      CostructuredArrow.hom_ext _ _ (by simpa [h₁, h₂] using el)
    rw [ef₁, ef₂]
    simp only [op_comp, Functor.map_comp, types_comp_apply]
    exact congrArg _ (hx h₁ h₂ hg₁ hg₂ hcomp)

/-- **Stacks 04J4, continuity of postcomposition.** -/
@[stacks 04J4 "continuity of postcomposition"]
public theorem elementPostcomp_isContinuous (s : G ⟶ F) :
    (elementPostcomp s).IsContinuous (elementTopology G) (elementTopology F) :=
  Functor.isContinuous_of_coverPreserving (compatiblePreserving_elementPostcomp s)
    (coverPreserving_elementPostcomp s)

attribute [instance] elementPostcomp_isContinuous elementPostcomp_isCocontinuous

/-- Restriction of sheaves of sets along postcomposition of sections is left exact. This is the
left exactness that makes relocalization a morphism of topoi; it is the general left exactness of
`CategoryTheory.Functor.preservesFiniteLimits_sheafPushforwardContinuous`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/Relocalization.lean`, which carries the `04J4` tag
for it) specialized to `elementPostcomp`, and it needed only continuity, proved above. -/
public instance elementPostcomp_preservesFiniteLimits (s : G ⟶ F) :
    PreservesFiniteLimits ((elementPostcomp s).sheafPushforwardContinuous
      (Type vC) (elementTopology G) (elementTopology F)) :=
  Functor.preservesFiniteLimits_sheafPushforwardContinuous _ _ _ _

end OverSite

variable {X : RingedTopos.{u}} {F G : X.Topos}

/-- An arrow of the site of elements belongs to a sieve exactly when the canonical lift of its
underlying arrow does. -/
public theorem mem_sieve_iff_liftHom {Us : elementSite X F} (T : Sieve Us)
    {A : elementSite X F} (α : A ⟶ Us) : T α ↔ T (liftHom Us α.left) :=
  OverSite.mem_sieve_iff_liftHom T α

/-- The sieve on `Us.left` underlying a sieve on the object `Us` of the site of elements: the
arrows whose canonical lift belongs to the given sieve. -/
public def underlyingSieve {Us : elementSite X F} (T : Sieve Us) : Sieve Us.left where
  arrows _ g := T (liftHom Us g)
  downward_closed := by
    intro V W g hg k
    have e : (CostructuredArrow.homMk k (by simp) :
        CostructuredArrow.mk (yoneda.map (k ≫ g) ≫ Us.hom) ⟶
          CostructuredArrow.mk (yoneda.map g ≫ Us.hom)) ≫ liftHom Us g =
        liftHom Us (k ≫ g) :=
      CostructuredArrow.hom_ext _ _ (by simp)
    rw [show (liftHom Us (k ≫ g)) = _ from e.symm]
    exact T.downward_closed hg _

/-- `underlyingSieve` commutes with pullback: the underlying sieve of `T.pullback α` is the
pullback of the underlying sieve of `T` along `α.left`. -/
public lemma underlyingSieve_pullback {Us A : elementSite X F} (T : Sieve Us) (α : A ⟶ Us) :
    underlyingSieve (T.pullback α) = (underlyingSieve T).pullback α.left :=
  Sieve.ext fun _ g ↦ mem_sieve_iff_liftHom T (liftHom A g ≫ α)

/-- The topology on the site of elements transported from `X.J` through the bijection between
sieves on `Us` and sieves on `Us.left`. It is `elementTopology X F`; stating it separately is what
gives the harder half of that identification. -/
public def liftedTopology (X : RingedTopos.{u}) (F : X.Topos) :
    GrothendieckTopology (elementSite X F) where
  sieves Us := {T | underlyingSieve T ∈ X.J Us.left}
  top_mem' Us := by
    have e : underlyingSieve (⊤ : Sieve Us) = ⊤ := Sieve.ext fun _ _ ↦ Iff.rfl
    change underlyingSieve (⊤ : Sieve Us) ∈ X.J Us.left
    rw [e]
    exact X.J.top_mem _
  pullback_stable' Us A T α hT := by
    change underlyingSieve (T.pullback α) ∈ X.J A.left
    rw [underlyingSieve_pullback]
    exact X.J.pullback_stable α.left hT
  transitive' Us T hT R h := by
    change underlyingSieve R ∈ X.J Us.left
    refine X.J.transitive hT _ ?_
    intro V g hg
    have h2 : underlyingSieve (R.pullback (liftHom Us g)) ∈ X.J V := h (f := liftHom Us g) hg
    rw [underlyingSieve_pullback] at h2
    exact h2

/-- The topology on the site of elements is contained in `liftedTopology`: it is generated by the
sieves whose pushforward along the projection covers, and every such sieve has covering underlying
sieve because the pushforward is contained in it. -/
public theorem elementTopology_le_liftedTopology :
    elementTopology X F ≤ liftedTopology X F :=
  OverSite.elementTopology_le_liftedTopology

/-- **The harder half of Stacks 0791 for the site of elements**, and the converse of
`mem_elementTopology_of_forall_liftHom`: a covering sieve of the site of elements has covering
underlying sieve. -/
public theorem underlyingSieve_mem {Us : elementSite X F} {T : Sieve Us}
    (hT : T ∈ elementTopology X F Us) : underlyingSieve T ∈ X.J Us.left :=
  OverSite.underlyingSieve_mem hT

/-- Postcomposition of sections with `s : G ⟶ F`, as a functor between the sites of elements. -/
public abbrev elementPostcomp (s : G ⟶ F) : elementSite X G ⥤ elementSite X F :=
  CostructuredArrow.map s.hom

/-- **Stacks 04J4, cocontinuity of postcomposition.** The tag is registered on
`OverSite.elementPostcomp_isCocontinuous`, which states the same thing over a bare site. -/
@[stacks 04J4 "cocontinuity of postcomposition"]
public theorem elementPostcomp_isCocontinuous (s : G ⟶ F) :
    (elementPostcomp s).IsCocontinuous (elementTopology X G) (elementTopology X F) :=
  OverSite.elementPostcomp_isCocontinuous s

/-- Postcomposition of sections preserves covering sieves. -/
public theorem coverPreserving_elementPostcomp (s : G ⟶ F) :
    CoverPreserving (elementTopology X G) (elementTopology X F) (elementPostcomp s) :=
  OverSite.coverPreserving_elementPostcomp s

/-- Postcomposition of sections is compatible-preserving. -/
public theorem compatiblePreserving_elementPostcomp (s : G ⟶ F) :
    CompatiblePreserving.{u} (elementTopology X F) (elementPostcomp s) :=
  OverSite.compatiblePreserving_elementPostcomp s

/-- **Stacks 04J4, continuity of postcomposition.** The tag is registered on
`OverSite.elementPostcomp_isContinuous`, which states the same thing over a bare site. -/
@[stacks 04J4 "continuity of postcomposition"]
public theorem elementPostcomp_isContinuous (s : G ⟶ F) :
    (elementPostcomp s).IsContinuous (elementTopology X G) (elementTopology X F) :=
  Functor.isContinuous_of_coverPreserving (compatiblePreserving_elementPostcomp s)
    (coverPreserving_elementPostcomp s)

attribute [instance] elementPostcomp_isContinuous elementPostcomp_isCocontinuous

/-- Restriction of sheaves of sets along postcomposition of sections is left exact. This is the
left exactness that makes relocalization a morphism of topoi; it is the general left exactness of
`CategoryTheory.Functor.preservesFiniteLimits_sheafPushforwardContinuous`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/Relocalization.lean`, which carries the `04J4` tag
for it) specialized to `elementPostcomp`, and it needed only continuity, proved above. -/
public instance elementPostcomp_preservesFiniteLimits (s : G ⟶ F) :
    PreservesFiniteLimits ((elementPostcomp s).sheafPushforwardContinuous
      (Type u) (elementTopology X G) (elementTopology X F)) :=
  Functor.preservesFiniteLimits_sheafPushforwardContinuous _ _ _ _

end Stacks.Sheaves.LocalizedRingedTopos
