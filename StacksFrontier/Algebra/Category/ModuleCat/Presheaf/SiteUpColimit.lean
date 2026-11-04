module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Comma.LocallySmall
public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Limits.Filtered
public import StacksFrontier.CategoryTheory.Sites.Presheaf.Functoriality.StructuredArrowFiltered
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackPresheaf

/-!
# The colimit formula for `u_p` on presheaves of modules

Let `u : D ⥤ C` be a functor and let `O` be a presheaf of rings on `D`.  Stacks 00VC
defines the presheaf `u_p F` on `C`, for a presheaf `F` on `D`, by the colimit formula
`(u_p F)(U) = colim_{(I^u_U)ᵒᵖ} F(V)`, the colimit being over the index category
`I^u_U` whose objects are the pairs `(V, φ : U ⟶ u V)`.  In Lean `u_p` is the left Kan
extension `u.op.lan` along `u.op : Dᵒᵖ ⥤ Cᵒᵖ`, and `I^u_U` is `StructuredArrow U u`, whose
opposite is `CostructuredArrow u.op (op U)` (`CategoryTheory.structuredArrowOpEquivalence`).

This file proves that when `I^u_U` is cofiltered for every `U` — i.e. when `u` is
representably flat, which by Stacks 00X3 holds as soon as `D` has finite limits and `u`
preserves them — the abelian-group presheaf `u_p G` underlying a presheaf of `O`-modules `G`
carries a structure of presheaf of `u_p O`-modules, germwise, and that this is functorial in
`G`.  This is the module-level counterpart of the presheaf-of-types statement Stacks 00VD
(`CategoryTheory.Functor.lanUnit`, registered in
`StacksFrontier.CategoryTheory.Sites.Presheaf.Functoriality.RestrictionIndexCategory`), and it is
the step the proof of Stacks 05VD (pullback of a flat module is flat) turns on: that proof
picks representatives of finitely many sections of `f^{-1}F = (u_p F)^#` and of
`f^{-1}O = (u_p O)^#` at a common `(V, φ) ∈ I^u_U` and uses that `∑ f_a s_a` vanishes already
in `F(V)`.

## Main definitions

* `Stacks.ModuleUp.upRing`, `Stacks.ModuleUp.upAb`: the presheaves `u_p O` and `u_p G` of
  rings, resp. abelian groups, on `C`, i.e. `u.op.lan` applied to `O`, resp. to the presheaf
  of abelian groups underlying a presheaf of modules.
* `Stacks.ModuleUp.pbRingIso`, `Stacks.ModuleUp.pbAbIso`: **the colimit formula** — the
  comparison isomorphisms of `(u_p O)(U)` and `(u_p G)(U)` with the colimits of `O`, resp.
  `G`, over the index category of `U`.  Each is a composite of two halves,
  `pbRingColimIso`/`pbAbColimIso` and `upRingObjIso`/`upAbObjIso`, declared separately so that
  no statement crosses two spellings; see the implementation notes.
* `Stacks.ModuleUp.upModule`: the sectionwise `(u_p O)(U)`-module structure on `(u_p G)(U)`.
* `Stacks.ModuleUp.upModuleFunctor`: `u_p` as a functor
  `PresheafOfModules O ⥤ PresheafOfModules (u_p O)`, with
  `Stacks.ModuleUp.upModuleFunctorCompToPresheaf` identifying the underlying presheaf of
  abelian groups with `u.op.lan` of the underlying presheaf of abelian groups.
* `Stacks.ModuleUp.upRingUnit`, `Stacks.ModuleUp.upAbUnit`: the germ maps
  `O(V) ⟶ (u_p O)(u V)` and `G(V) ⟶ (u_p G)(u V)`, i.e. the units of the Kan extension.
* `Stacks.ModuleUp.ringUnit`: the Kan-extension unit as a morphism of presheaves of rings
  `O ⟶ u.op ⋙ u_p O`.  This is the `φ` along which Mathlib's module-level
  `PresheafOfModules.pushforward` and `PresheafOfModules.pullback` are taken.

## Main results

* `Stacks.ModuleUp.up_presheaf_module`: `u_p G` is the presheaf of abelian groups underlying a
  presheaf of `u_p O`-modules.
* `Stacks.ModuleUp.upModule_map_smul`: the restriction maps of `u_p G` are semilinear over
  those of `u_p O`, which is what makes the sectionwise structures a presheaf of modules.
* `Stacks.ModuleUp.upModule_unit_smul`: the germ formula `germ (a • m) = germ a • germ m` for
  the units, which is the elementwise content of the construction.
* `Stacks.ModuleUp.germ_jointly_surjective₂`, `Stacks.ModuleUp.germ_smul`,
  `Stacks.ModuleUp.abGerm_eq_zero_iff`: the germ calculus a consumer needs — every
  element of `(u_p G)(U)` is a germ, a scalar and a section can be represented at a common
  index, the germ formula at an arbitrary index, and a germ vanishes exactly when the section
  is killed by some morphism of the index category.

## Implementation notes

**The directedness hypothesis is not an added hypothesis.** `[RepresentablyFlat u]` says that
`StructuredArrow U u = I^u_U` is cofiltered for every `U`, equivalently that `(I^u_U)ᵒᵖ` is
directed.  This is exactly where the source states the colimit formula: the proof of 05VD
reaches it only after replacing the given situation by sites with finite limits and a
finite-limit-preserving `u` (Stacks 03CR), and then cites Stacks 00X3 for the directedness.
It is *weaker* than "`D` has finite limits and `u` preserves them": `isFiltered_op_structuredArrow`
(`StacksFrontier.CategoryTheory.Sites.Presheaf.Functoriality.StructuredArrowFiltered`) and
`CategoryTheory.preservesFiniteLimits_iff_flat` both produce it from those hypotheses.
Without directedness the colimit formula is false at the module level: the scalar action is
built from the canonical map `colim (O(V) × G(V)) ⟶ (colim O(V)) × (colim G(V))`, which is
invertible only for filtered colimits (Stacks 002W).

**One spelling per statement, pinned by a `def`'s result type.**  Three pairs of
definitionally-but-not-syntactically equal spellings meet in this file, and a statement that
mixes two of them elaborates (defeq is checked) and is then not type-correct at `implicit`
transparency, after which `rw` and `simp` refuse with a message naming a pattern rather than
the cause.  The three pairs are: `colimit (pbRdiag u O U)`, i.e.
`colimit ((E.functor ⋙ proj) ⋙ O)`, against `Functor.Final.colimitIso`'s
`colimit (E.functor ⋙ (proj ⋙ O))` — an associativity, and for the module side also the
`presheaf` projection of a `PresheafOfModules.ofPresheaf`; `colimit.pre`'s source
`colimit (CostructuredArrow.map i ⋙ proj V ⋙ P)` against `colimit (proj U ⋙ P)`; and
`u.op.lan.obj P` against `u.op.leftKanExtension P`, `Functor.lan` being a `def`.  A fourth,
on elements, is `((toPresheaf O).map φ).app _`, whose target `((toPresheaf O).obj G').obj _`
is not a spelling at which the levelwise `Module` instance is found.

Each is pinned by a **`def` whose result type is ascribed** at the spelling every statement
then uses — `pbRingColimIso`, `pbAbColimIso`, `pbRingPre`, `pbAbPre`, `pbAbWhisker`,
`upRingObjIso`, `upAbObjIso`, `upAbMap`, `pbMmodApp` — together with one bridging lemma per
boundary (`ι_pbRingColimIso_hom`, `ι_pbAbColimIso_hom`, `upRingObjIso_hom_map_inv`,
`upAbObjIso_hom_map_inv`, `upAbObjIso_hom_app_inv`) proved by `:=`/`exact`, which are
defeq-tolerant where `rw` is not.  A type *ascription* `(e : T)` does **not** work here —
`inferType` ignores it — and `show T from e` is unusable inside a statement; only a `def`'s
declared result type or a `let`'s declared binder type pins the spelling.  Where a Mathlib
lemma is stated at the other spelling (`ModuleColimit.smul_eq`, `jointly_surjective₂`, whose
conclusions use `ModuleColimit.ιR`/`ιM`), it is restated as a `have` with the type written out
at this file's spelling and proved by `:=`, and only then rewritten with.

This discipline is the reason the file contains **no `erw` and no `set_option`**.  The
topological counterpart `Stacks.PresheafOfModules.Pullback` it generalizes uses 13 of the former
  and 3 of the latter
for exactly these four boundaries; an A/B measurement here found that removing the three
options from a verbatim port produces 5 errors and that `rw`/`simp only` close none of the 13
sites, whereas pinning the spellings closes all of them.

**Universes.** Everything is at a single universe `w` carrying the two categories, the rings
and the module sections.  That is forced by the API, not chosen:
`PresheafOfModules.ModuleColimit` is stated for `{R : Cᵒᵖ ⥤ RingCat.{v}}`,
`{M : PresheafOfModules.{v} R}` with `[InitiallySmall.{v} C]` and `[LocallySmall.{v} C]`, so
the module universe, the ring universe and the smallness level of the index category all
coincide; and the index category `CostructuredArrow u.op U` is small exactly when `C` and `D`
are.  Mathlib imposes the same restriction where it constructs the module-level pullback
(`PresheafOfModules.pullback` is only shown to exist for `{C D : Type u} [SmallCategory C]
[SmallCategory D]` and `RingCat.{u}`), and so does the topological-space counterpart
`Stacks.PresheafOfModules.Pullback` in
`StacksFrontier.Topology.Sheaves.Functors.Module.PullbackPresheaf`, for the same reason.

**No `@[stacks]` attribute.**  The source has no tag for this statement: it is a step inside
the proof of 05VD, where the formula is recalled rather than proved, and the tagged
statements nearby are about something else — 00VD is the presheaf-of-*types* canonical map,
008T is the same construction for a continuous map of topological spaces, and 03D2 is the
module structure on `f^{-1}` for an abstract morphism of *topoi*, obtained by transporting
operations across finite-product comparisons rather than from a colimit formula.

**Relation to `Stacks.PullbackColimit`, which gives the *tensor* colimit model.**
`StacksFrontier.Algebra.Category.ModuleCat.Presheaf.PullbackColimit` already identifies Mathlib's
abstract `PresheafOfModules.pullback α`, for an arbitrary `α : S ⟶ F.op ⋙ R` of presheaves of
*commutative* rings, with objectwise extension of scalars followed by the objectwise colimit
`colim_{(V, U ⟶ F V)} R(U) ⊗_{R(F V)} N(V)` (`pullbackIso`, `pullbackObjIso`), together with
its adjunction and a germ calculus for pure tensors, and it needs no directedness.  That is a
*different* formula from the one the source uses: the source's `u_p F(U)` is
`colim_{(I^u_U)ᵒᵖ} F(V)` with **no tensor factor**, which is correct only because the ring is
itself `u_p O` and the index category is directed, so that the base changes
`O(V) → (u_p O)(U)` are absorbed by the colimit.  The present file builds that tensor-free
form directly, for `RingCat` rather than `CommRingCat`, and gives the germ calculus at that
spelling.

Consequently the two files meet at a single concrete comparison: the canonical map
`colim_{(V, φ)} F(V) ⟶ colim_{(V, φ)} (u_p O)(U) ⊗_{O(V)} F(V)`, `s ↦ 1 ⊗ s`, is an
isomorphism when the index category is filtered.  That is the discharge of the hypothesis of
`pullbackIsoUpModuleFunctor` below, and it is NOT proved here.

**What is still needed for `f^{-1}F = (u_p F)^#`, and what is not.**  The *sheaf*-level
identity is already Mathlib's `SheafOfModules.pullbackIso`, which exhibits the module-level
inverse image as `forget ⋙ PresheafOfModules.pullback φ.hom ⋙ sheafification`; and
`SheafOfModules.sheafificationCompPullback` is the compatibility of that pullback with
sheafification.  What those statements call `u_p` is `PresheafOfModules.pullback`, Mathlib's
*abstract* left adjoint of `PresheafOfModules.pushforward`, constructed by corepresentability
of the free modules on representables and carrying no colimit description whatever.  So the
source's `f^{-1}F = (u_p F)^#`, with `u_p` the *colimit*, is one step away from being
formally available, and that step is exactly

  `upModuleFunctor u O ⊣ PresheafOfModules.pushforward (ringUnit u O)`.

`Stacks.ModuleUp.pullbackIsoUpModuleFunctor` below discharges everything after it: given that
adjunction, `PresheafOfModules.pullback (ringUnit u O) ≅ upModuleFunctor u O` by uniqueness of
left adjoints, and composing with `SheafOfModules.pullbackIso` gives the source's statement.
The adjunction itself is NOT proved here.  Its two non-formal halves are the two linearity
checks: that the Ab-level adjunction `Functor.lanAdjunction` carries a `u_p O`-linear map to an
`O`-semilinear one (which is `upModule_unit_smul`), and that it carries an `O`-semilinear map
to a `u_p O`-linear one (which needs `germ_jointly_surjective₂` and `germ_smul` together with a
formula, not proved here, for the Kan-extension descent evaluated on a germ).

**Relation to `Stacks.PresheafOfModules.Pullback`.**  The six Kan-extension/colimit lemmas reused
  below
(`moduleOfAddEquiv`, `leftKanExtensionObjIsoColimit_naturality`, `lke_morphism_naturality`,
`ι_colimitIso_pre_colimitIso_inv`, `ι_colimitIso_colimMap_colimitIso_inv`,
`leftKanExtensionUnit_eq_ι_leftKanExtensionObjIsoColimit`) are stated there for an arbitrary
functor and are imported, not re-proved.  `Stacks.PresheafOfModules.Pullback` itself is the case
`u = Opens.map f`; a dedup pass should move those six lemmas here (or lower) and derive
`Stacks.PresheafOfModules.Pullback` from this file.

## References

* [Stacks Project, Tag 00VC](https://stacks.math.columbia.edu/tag/00VC)
* [Stacks Project, Tag 00VD](https://stacks.math.columbia.edu/tag/00VD)
* [Stacks Project, Tag 05VD](https://stacks.math.columbia.edu/tag/05VD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.ModuleUp

universe w

variable {C D : Type w} [SmallCategory C] [SmallCategory D] (u : D ⥤ C) [RepresentablyFlat u]

/-- The index category `I^u_U` of Stacks 00VC, read as `CostructuredArrow u.op U`, is
filtered: it is the opposite of `StructuredArrow U.unop u`, which is cofiltered because `u` is
representably flat. -/
instance isFilteredCostructuredArrowOp (U : Cᵒᵖ) :
    IsFiltered (CostructuredArrow u.op U) :=
  IsFiltered.of_equivalence (structuredArrowOpEquivalence u U.unop)

/-- The index category is small, hence finally small at the level of the sections.

**Local on purpose.**  `FinallySmall` has a broad head and Mathlib supplies it with a `haveI`
rather than an instance, so exporting it would widen instance search for every consumer.  What
consumers actually need is the handful of `HasColimit`s it produces for *this file's* diagrams,
and those are exported individually just below. -/
local instance finallySmallCostructuredArrowOp (U : Cᵒᵖ) :
    FinallySmall.{w} (CostructuredArrow u.op U) :=
  finallySmall_of_essentiallySmall _

/-- The colimit defining `(u_p P)(U)` exists, for a presheaf of rings `P`.  Exported so that a
consumer of the colimit formula does not need the broad `FinallySmall` instance above. -/
instance hasColimitProjCompRing (P : Dᵒᵖ ⥤ RingCat.{w}) (U : Cᵒᵖ) :
    HasColimit (CostructuredArrow.proj u.op U ⋙ P) := inferInstance

/-- The abelian-group analogue of `hasColimitProjCompRing`. -/
instance hasColimitProjCompAb (P : Dᵒᵖ ⥤ AddCommGrpCat.{w}) (U : Cᵒᵖ) :
    HasColimit (CostructuredArrow.proj u.op U ⋙ P) := inferInstance

/-- The pullback presheaf of rings `u_p O` (Stacks 00VC). Its sections are the filtered
colimits `(u_p O)(U) = colim_{(V, φ) ∈ I^u_U} O(V)`, carrying the colimit ring structure. -/
noncomputable def upRing (O : Dᵒᵖ ⥤ RingCat.{w}) :
    Cᵒᵖ ⥤ RingCat.{w} :=
  (u.op.lan).obj O

/-- The pullback presheaf of abelian groups `u_p G`. Its sections are
`(u_p G)(U) = colim_{(V, φ) ∈ I^u_U} G(V)`. -/
noncomputable def upAb (G : Dᵒᵖ ⥤ AddCommGrpCat.{w}) :
    Cᵒᵖ ⥤ AddCommGrpCat.{w} :=
  (u.op.lan).obj G

/-- The underlying presheaf of abelian groups of a presheaf of `O`-modules `G`
(forgetting the module structure), i.e. `G` viewed as a presheaf of abelian groups on `D`. -/
noncomputable def underlyingAb (O : Dᵒᵖ ⥤ RingCat.{w}) (G : PresheafOfModules.{w} O) :
    Dᵒᵖ ⥤ AddCommGrpCat.{w} :=
  (PresheafOfModules.toPresheaf O).obj G

/-- Index functor: the diagram shape for the colimit, written over the double opposite
`((CostructuredArrow ..)ᵒᵖ)ᵒᵖ` so that `ModuleColimit` (whose diagram lives over `Cᵒᵖ`)
applies with `C = (CostructuredArrow ..)ᵒᵖ`. -/
@[reducible] noncomputable def pbIdx
    (U : Cᵒᵖ) :
    ((CostructuredArrow u.op U)ᵒᵖ)ᵒᵖ ⥤ Dᵒᵖ :=
  (opOpEquivalence (CostructuredArrow u.op U)).functor ⋙
    CostructuredArrow.proj u.op U

/-- The diagram of rings `O(V)` over the index `pbIdx`. -/
@[reducible] noncomputable def pbRdiag (O : Dᵒᵖ ⥤ RingCat.{w})
    (U : Cᵒᵖ) :
    ((CostructuredArrow u.op U)ᵒᵖ)ᵒᵖ ⥤ RingCat.{w} :=
  pbIdx u U ⋙ O

/-- Sectionwise module structure of the diagram `pbIdx ⋙ G.presheaf` over `pbRdiag`. -/
noncomputable instance pbInstMod (O : Dᵒᵖ ⥤ RingCat.{w}) (G : PresheafOfModules.{w} O)
    (U : Cᵒᵖ) (c) :
    Module ((pbRdiag u O U).obj c) ((pbIdx u U ⋙ G.presheaf).obj c) :=
  (G.obj ((pbIdx u U).obj c)).isModule

/-- The presheaf of `pbRdiag`-modules whose underlying presheaf of abelian groups is
`pbIdx ⋙ G.presheaf`. -/
@[reducible] noncomputable def pbMmod (O : Dᵒᵖ ⥤ RingCat.{w})
    (G : PresheafOfModules.{w} O) (U : Cᵒᵖ) :
    PresheafOfModules.{w} (pbRdiag u O U) :=
  PresheafOfModules.ofPresheaf (R := pbRdiag u O U) (pbIdx u U ⋙ G.presheaf)
    (fun {_ _} h r m => G.map_smul ((pbIdx u U).map h) r m)

/-- The module structure on the colimit-abelian-group over the colimit-ring (germ formula),
from `ModuleColimit`. -/
@[reducible] noncomputable def pbInstCM (O : Dᵒᵖ ⥤ RingCat.{w})
    (G : PresheafOfModules.{w} O) (U : Cᵒᵖ) :
    Module ↑(colimit (pbRdiag u O U)) ↑(colimit (pbMmod u O G U).presheaf) :=
  PresheafOfModules.ModuleColimit.instModuleCarrierPtOppositeRingCat
    (colimit.isColimit (pbRdiag u O U)) (colimit.isColimit (pbMmod u O G U).presheaf)

/-- The comparison of the colimit over the double-opposite index with the colimit over the
index category itself, **with its result type ascribed at the `pbRdiag` spelling**.

This `def` is the one-spelling discipline of this file.  `Functor.Final.colimitIso` is stated
for `E.functor ⋙ (CostructuredArrow.proj u.op U ⋙ O)`, whereas `pbRdiag u O U` is
`(E.functor ⋙ CostructuredArrow.proj u.op U) ⋙ O`: the two are definitionally equal by
associativity of functor composition but not syntactically, so an `Iso.trans` that mixes them
elaborates (defeq is checked) and is then not type-correct at `implicit` transparency, after
which `rw` and `simp` refuse.  A type *ascription* does not help — `inferType` ignores it — but
a `def`'s declared result type does, because `:=` is defeq-tolerant and every later statement
then mentions only the ascribed spelling. -/
noncomputable def pbRingColimIso (O : Dᵒᵖ ⥤ RingCat.{w}) (U : Cᵒᵖ) :
    colimit (pbRdiag u O U) ≅ colimit (CostructuredArrow.proj u.op U ⋙ O) :=
  Functor.Final.colimitIso (opOpEquivalence (CostructuredArrow u.op U)).functor
    (CostructuredArrow.proj u.op U ⋙ O)

/-- The abelian-group analogue of `pbRingColimIso`, with its result type ascribed at the
`pbMmod` spelling.  Here the gap is a structure projection as well as an associativity:
`(pbMmod u O G U).presheaf` is the `presheaf` field of a `PresheafOfModules.ofPresheaf`. -/
noncomputable def pbAbColimIso (O : Dᵒᵖ ⥤ RingCat.{w}) (G : PresheafOfModules.{w} O)
    (U : Cᵒᵖ) :
    colimit (pbMmod u O G U).presheaf ≅ colimit (CostructuredArrow.proj u.op U ⋙ G.presheaf) :=
  Functor.Final.colimitIso (opOpEquivalence (CostructuredArrow u.op U)).functor
    (CostructuredArrow.proj u.op U ⋙ G.presheaf)

/-- `pbRingColimIso` carries the colimit injection at `c` to the injection at `c.unop.unop`. -/
lemma ι_pbRingColimIso_hom (O : Dᵒᵖ ⥤ RingCat.{w}) (U : Cᵒᵖ)
    (c : ((CostructuredArrow u.op U)ᵒᵖ)ᵒᵖ) :
    colimit.ι (pbRdiag u O U) c ≫ (pbRingColimIso u O U).hom
      = colimit.ι (CostructuredArrow.proj u.op U ⋙ O) c.unop.unop := by
  simp only [pbRingColimIso]
  exact Functor.Final.ι_colimitIso_hom
    (opOpEquivalence (CostructuredArrow u.op U)).functor
    (CostructuredArrow.proj u.op U ⋙ O) c

omit [RepresentablyFlat u] in
/-- `pbAbColimIso` carries the colimit injection at `c` to the injection at `c.unop.unop`. -/
lemma ι_pbAbColimIso_hom (O : Dᵒᵖ ⥤ RingCat.{w}) (G : PresheafOfModules.{w} O) (U : Cᵒᵖ)
    (c : ((CostructuredArrow u.op U)ᵒᵖ)ᵒᵖ) :
    colimit.ι (pbMmod u O G U).presheaf c ≫ (pbAbColimIso u O G U).hom
      = colimit.ι (CostructuredArrow.proj u.op U ⋙ G.presheaf) c.unop.unop := by
  simp only [pbAbColimIso]
  exact Functor.Final.ι_colimitIso_hom
    (opOpEquivalence (CostructuredArrow u.op U)).functor
    (CostructuredArrow.proj u.op U ⋙ G.presheaf) c

/-- The colimit reindexing along `CostructuredArrow.map i`, **with its source and target types
ascribed** at the `CostructuredArrow.proj` spelling.  `colimit.pre` has source
`colimit (CostructuredArrow.map i ⋙ CostructuredArrow.proj u.op V ⋙ O)`, which is
definitionally but not syntactically `colimit (CostructuredArrow.proj u.op U ⋙ O)`; this is the
second spelling crossing of the file, and the same `def`-with-ascribed-result-type cure
applies. -/
noncomputable def pbRingPre (O : Dᵒᵖ ⥤ RingCat.{w}) {U V : Cᵒᵖ} (i : U ⟶ V) :
    colimit (CostructuredArrow.proj u.op U ⋙ O) ⟶
      colimit (CostructuredArrow.proj u.op V ⋙ O) :=
  colimit.pre (CostructuredArrow.proj u.op V ⋙ O) (CostructuredArrow.map i)

/-- The abelian-group analogue of `pbRingPre`. -/
noncomputable def pbAbPre (O : Dᵒᵖ ⥤ RingCat.{w}) (G : PresheafOfModules.{w} O)
    {U V : Cᵒᵖ} (i : U ⟶ V) :
    colimit (CostructuredArrow.proj u.op U ⋙ G.presheaf) ⟶
      colimit (CostructuredArrow.proj u.op V ⋙ G.presheaf) :=
  colimit.pre (CostructuredArrow.proj u.op V ⋙ G.presheaf) (CostructuredArrow.map i)

/-- The levelwise colimit map of a morphism of modules, with its source and target types
ascribed at the `CostructuredArrow.proj` spelling. -/
noncomputable def pbAbWhisker (O : Dᵒᵖ ⥤ RingCat.{w}) {G G' : PresheafOfModules.{w} O}
    (φ : G ⟶ G') (U : Cᵒᵖ) :
    colimit (CostructuredArrow.proj u.op U ⋙ G.presheaf) ⟶
      colimit (CostructuredArrow.proj u.op U ⋙ G'.presheaf) :=
  colimMap (Functor.whiskerLeft (CostructuredArrow.proj u.op U)
    ((PresheafOfModules.toPresheaf O).map φ))

/-- The pointwise-colimit comparison of the Kan extension, **with its result type ascribed at
the `upRing` spelling**.  `Functor.lan` is a `def`, so `u.op.lan.obj O` and
`u.op.leftKanExtension O` are definitionally but not syntactically equal; this is the third and
last spelling crossing of the file. -/
noncomputable def upRingObjIso (O : Dᵒᵖ ⥤ RingCat.{w}) (U : Cᵒᵖ) :
    colimit (CostructuredArrow.proj u.op U ⋙ O) ≅ (upRing u O).obj U :=
  (u.op.leftKanExtensionObjIsoColimit O U).symm

/-- The abelian-group analogue of `upRingObjIso`. -/
noncomputable def upAbObjIso (O : Dᵒᵖ ⥤ RingCat.{w}) (G : PresheafOfModules.{w} O) (U : Cᵒᵖ) :
    colimit (CostructuredArrow.proj u.op U ⋙ G.presheaf) ≅
      (upAb u (underlyingAb O G)).obj U :=
  (u.op.leftKanExtensionObjIsoColimit G.presheaf U).symm

/-- `Stacks.PresheafOfModules.Pullback.leftKanExtensionObjIsoColimit_naturality`, restated once and
  for all at the
pinned spellings: conjugating a restriction map of `u_p O` by `upRingObjIso` gives the colimit
reindexing `pbRingPre`.  Everything downstream rewrites with this instead of crossing the
`lan`/`leftKanExtension` boundary in a statement. -/
lemma upRingObjIso_hom_map_inv (O : Dᵒᵖ ⥤ RingCat.{w}) {U V : Cᵒᵖ} (i : U ⟶ V) :
    (upRingObjIso u O U).hom ≫ (upRing u O).map i ≫ (upRingObjIso u O V).inv
      = pbRingPre u O i := by
  have key : (upRing u O).map i ≫ (upRingObjIso u O V).inv
      = (upRingObjIso u O U).inv ≫ pbRingPre u O i :=
    Stacks.PresheafOfModules.Pullback.leftKanExtensionObjIsoColimit_naturality u.op O i
  rw [key, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

omit [RepresentablyFlat u] in
/-- The abelian-group analogue of `upRingObjIso_hom_map_inv`. -/
lemma upAbObjIso_hom_map_inv (O : Dᵒᵖ ⥤ RingCat.{w}) (G : PresheafOfModules.{w} O)
    {U V : Cᵒᵖ} (i : U ⟶ V) :
    (upAbObjIso u O G U).hom ≫ (upAb u (underlyingAb O G)).map i ≫ (upAbObjIso u O G V).inv
      = pbAbPre u O G i := by
  have key : (upAb u (underlyingAb O G)).map i ≫ (upAbObjIso u O G V).inv
      = (upAbObjIso u O G U).inv ≫ pbAbPre u O G i :=
    Stacks.PresheafOfModules.Pullback.leftKanExtensionObjIsoColimit_naturality u.op G.presheaf i
  rw [key, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- `u_p` of a morphism of `O`-modules, as a morphism `u_p G ⟶ u_p G'` of presheaves of
abelian groups, **with its result type ascribed at the `upAb` spelling**. -/
noncomputable def upAbMap (O : Dᵒᵖ ⥤ RingCat.{w}) {G G' : PresheafOfModules.{w} O}
    (φ : G ⟶ G') : upAb u (underlyingAb O G) ⟶ upAb u (underlyingAb O G') :=
  u.op.lan.map ((PresheafOfModules.toPresheaf O).map φ)

omit [RepresentablyFlat u] in
/-- `Stacks.PresheafOfModules.Pullback.lke_morphism_naturality` at the pinned spellings:
  conjugating `upAbMap` by
`upAbObjIso` gives the levelwise colimit map `pbAbWhisker`. -/
lemma upAbObjIso_hom_app_inv (O : Dᵒᵖ ⥤ RingCat.{w}) {G G' : PresheafOfModules.{w} O}
    (φ : G ⟶ G') (U : Cᵒᵖ) :
    (upAbObjIso u O G U).hom ≫ (upAbMap u O φ).app U ≫ (upAbObjIso u O G' U).inv
      = pbAbWhisker u O φ U := by
  have key : (upAbMap u O φ).app U ≫ (upAbObjIso u O G' U).inv
      = (upAbObjIso u O G U).inv ≫ pbAbWhisker u O φ U :=
    Stacks.PresheafOfModules.Pullback.lke_morphism_naturality u.op ((PresheafOfModules.toPresheaf
      O).map φ) U
  rw [key, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- The comparison isomorphism between `colimit pbRdiag` and the section `(u_p O)(U)`. -/
noncomputable def pbRingIso (O : Dᵒᵖ ⥤ RingCat.{w})
    (U : Cᵒᵖ) : colimit (pbRdiag u O U) ≅ (upRing u O).obj U :=
  pbRingColimIso u O U ≪≫ upRingObjIso u O U

/-- The comparison isomorphism between `colimit (pbMmod).presheaf` and the section `(u_p G)(U)`. -/
noncomputable def pbAbIso (O : Dᵒᵖ ⥤ RingCat.{w}) (G : PresheafOfModules.{w} O)
    (U : Cᵒᵖ) :
    colimit (pbMmod u O G U).presheaf ≅ (upAb u (underlyingAb O G)).obj U :=
  pbAbColimIso u O G U ≪≫ upAbObjIso u O G U

/- The construction below rests on the single nontrivial input Stacks 002W cited above: in
`Type`, filtered colimits commute with finite products. Mathlib packages the resulting
module structure in `PresheafOfModules.ModuleColimit`: given a colimit ring `cR.pt` and a
colimit abelian group `cM.pt` over the SAME filtered index, it puts a `Module cR.pt cM.pt`
structure on the colimit abelian group, with the germ formula `[V, a] • [V, s] = [V, a • s]`.
Everything below specialises that machinery to the index category `I^u_U` of Stacks 00VC,
which is the costructured-arrow category
`CostructuredArrow (u.op) U` underlying
`u.op.lan`.

The assembly uses `PresheafOfModules.ofPresheaf`, which builds a `PresheafOfModules R` from a
*prescribed* presheaf of abelian groups `M : Cᵒᵖ ⥤ Ab` with sectionwise
`Module (R.obj X) (M.obj X)` instances and a semilinearity hypothesis. Crucially
`(ofPresheaf M h).presheaf = M` holds by `rfl`, so the equality
`(toPresheaf _).obj M = upAb u (underlyingAb O G)` demanded by the tag is closed by
`rfl`. -/

/-- **The scalar multiplication and the module axioms, sectionwise.**

For each object `U` of `C`, the abelian group `(u_p G)(U) = colim_{(V, φ) ∈ I^u_U} G(V)` carries a
module structure over the ring `(u_p O)(U) = colim_{(V, φ) ∈ I^u_U} O(V)`.

Both colimits are taken over the same filtered index category
`I^u_U = CostructuredArrow (u.op) U` of Stacks 00VC. By Stacks 002W the forgetful functors
to `Type` preserve these filtered
colimits and filtered colimits commute with the finite product, so there is a canonical
bijection `colim (O(V) × G(V)) ≅ (colim O(V)) × (colim G(V))`; the scalar action is the
composite of its inverse with `colim` of the levelwise actions `O(V) × G(V) → G(V)`. On
representatives it is `[V, a] • [V, s] = [V, a • s]`, well defined because `I^u_U` is filtered,
so any two germs share a representative `V`, and the module axioms reduce to those of the
`O(V)`-module `G(V)` at a common representative.

Formally this is `PresheafOfModules.ModuleColimit` for
`R := CostructuredArrow.proj _ U ⋙ O` and `M := CostructuredArrow.proj _ U ⋙ G.presheaf`,
transported along `pbRingIso` and `pbAbIso`, the comparison isomorphisms of the colimits with
the Kan-extension sections `(u_p O)(U)` and `(u_p G)(U)`. -/
@[reducible] noncomputable def upModule (O : Dᵒᵖ ⥤ RingCat.{w})
    (G : PresheafOfModules.{w} O) (U : Cᵒᵖ) :
    Module ((upRing u O).obj U) ((upAb u (underlyingAb O G)).obj U) :=
  letI := pbInstCM u O G U
  letI : Module ((upRing u O).obj U) ↑(colimit (pbMmod u O G U).presheaf) :=
    Module.compHom (↑(colimit (pbMmod u O G U).presheaf))
      (pbRingIso u O U).ringCatIsoToRingEquiv.symm.toRingHom
  Stacks.PresheafOfModules.Pullback.moduleOfAddEquiv (addEquivIsoAddCommGroupIso.inv (pbAbIso u O G
    U))

/-- **Characterization of the transported scalar action.**
Unfolds the `•` of `upModule` in terms of the named comparison isos and the
`ModuleColimit` action `pbInstCM`. -/
theorem upModule_smul_eq (O : Dᵒᵖ ⥤ RingCat.{w}) (G : PresheafOfModules.{w} O)
    (U : Cᵒᵖ) (r : (upRing u O).obj U)
    (m : (upAb u (underlyingAb O G)).obj U) :
    letI := upModule u O G U
    letI := pbInstCM u O G U
    r • m = (pbAbIso u O G U).hom
      ((pbRingIso u O U).ringCatIsoToRingEquiv.symm r •
        (pbAbIso u O G U).symm.hom m) := by
  rfl

/-- The germ reindexing `colim_{I^u_U} O → colim_{I^u_V} O` along `i : U ⟶ V`, i.e.
`colimit.pre` along `CostructuredArrow.map i` read through the `opOpEquivalence` comparison
isomorphisms. -/
@[reducible] noncomputable def pbRingReindex (O : Dᵒᵖ ⥤ RingCat.{w})
    {U V : Cᵒᵖ} (i : U ⟶ V) (x : ↑(colimit (pbRdiag u O U))) :
    ↑(colimit (pbRdiag u O V)) :=
  (pbRingColimIso u O V).inv (pbRingPre u O i ((pbRingColimIso u O U).hom x))

/-- The germ reindexing `colim_{I^u_U} G → colim_{I^u_V} G` along `i : U ⟶ V`, the
abelian-group analogue of `pbRingReindex`. -/
@[reducible] noncomputable def pbAbReindex (O : Dᵒᵖ ⥤ RingCat.{w})
    (G : PresheafOfModules.{w} O) {U V : Cᵒᵖ} (i : U ⟶ V)
    (x : ↑(colimit (pbMmod u O G U).presheaf)) :
    ↑(colimit (pbMmod u O G V).presheaf) :=
  (pbAbColimIso u O G V).inv (pbAbPre u O G i ((pbAbColimIso u O G U).hom x))

/-- The map `colim_{I^u_U} G → colim_{I^u_U} G'` induced by a morphism `φ : G ⟶ G'` of
`O`-modules: the levelwise colimit map of `φ̲`, read through the `opOpEquivalence`
comparison isomorphisms. -/
@[reducible] noncomputable def pbAbColimMap (O : Dᵒᵖ ⥤ RingCat.{w})
    {G G' : PresheafOfModules.{w} O} (φ : G ⟶ G') (U : Cᵒᵖ)
    (x : ↑(colimit (pbMmod u O G U).presheaf)) :
    ↑(colimit (pbMmod u O G' U).presheaf) :=
  (pbAbColimIso u O G' U).inv (pbAbWhisker u O φ U ((pbAbColimIso u O G U).hom x))

/-- `pbRingReindex` sends the germ of `a` at `c` to the germ of `a` at the reindexed
object `(CostructuredArrow.map i).obj c`. -/
theorem pbRingReindex_ι (O : Dᵒᵖ ⥤ RingCat.{w}) {U V : Cᵒᵖ} (i : U ⟶ V)
    (c : ((CostructuredArrow u.op U)ᵒᵖ)ᵒᵖ) (a : ↑((pbRdiag u O U).obj c)) :
    pbRingReindex u O i (colimit.ι (pbRdiag u O U) c a)
      = colimit.ι (pbRdiag u O V)
          (Opposite.op (Opposite.op ((CostructuredArrow.map i).obj c.unop.unop))) a := by
  have := ConcreteCategory.congr_hom
    (Stacks.PresheafOfModules.Pullback.ι_colimitIso_pre_colimitIso_inv u.op O i c) a
  simp only [ConcreteCategory.comp_apply] at this
  exact this

omit [RepresentablyFlat u] in
/-- `pbAbReindex` sends the germ of `x` at `c` to the germ of `x` at the reindexed object
`(CostructuredArrow.map i).obj c`. -/
theorem pbAbReindex_ι (O : Dᵒᵖ ⥤ RingCat.{w}) (G : PresheafOfModules.{w} O)
    {U V : Cᵒᵖ} (i : U ⟶ V) (c : ((CostructuredArrow u.op U)ᵒᵖ)ᵒᵖ)
    (x : ↑((pbMmod u O G U).presheaf.obj c)) :
    pbAbReindex u O G i (colimit.ι (pbMmod u O G U).presheaf c x)
      = colimit.ι (pbMmod u O G V).presheaf
          (Opposite.op (Opposite.op ((CostructuredArrow.map i).obj c.unop.unop))) x := by
  have := ConcreteCategory.congr_hom
    (Stacks.PresheafOfModules.Pullback.ι_colimitIso_pre_colimitIso_inv u.op G.presheaf i c) x
  exact this

/-- The component of `φ` at an index of the colimit diagram, **with its source and target
types ascribed at the `pbMmod` spelling**.  Written as `((toPresheaf O).map φ).app _` its
target is `((toPresheaf O).obj G').obj _`, at which the levelwise `Module` instance
`pbInstMod` is not found by synthesis; this `def` is what makes `a • pbMmodApp … x`
elaborate. -/
noncomputable def pbMmodApp (O : Dᵒᵖ ⥤ RingCat.{w}) {G G' : PresheafOfModules.{w} O}
    (φ : G ⟶ G') (U : Cᵒᵖ) (c : ((CostructuredArrow u.op U)ᵒᵖ)ᵒᵖ) :
    (pbMmod u O G U).presheaf.obj c ⟶ (pbMmod u O G' U).presheaf.obj c :=
  ((PresheafOfModules.toPresheaf O).map φ).app ((pbIdx u U).obj c)

omit [RepresentablyFlat u] in
/-- `pbAbColimMap` keeps the germ index and applies `φ` to the section levelwise. -/
theorem pbAbColimMap_ι (O : Dᵒᵖ ⥤ RingCat.{w}) {G G' : PresheafOfModules.{w} O}
    (φ : G ⟶ G') (U : Cᵒᵖ) (c : ((CostructuredArrow u.op U)ᵒᵖ)ᵒᵖ)
    (x : ↑((pbMmod u O G U).presheaf.obj c)) :
    pbAbColimMap u O φ U (colimit.ι (pbMmod u O G U).presheaf c x)
      = colimit.ι (pbMmod u O G' U).presheaf c (pbMmodApp u O φ U c x) := by
  have := ConcreteCategory.congr_hom
    (Stacks.PresheafOfModules.Pullback.ι_colimitIso_colimMap_colimitIso_inv u.op
      ((PresheafOfModules.toPresheaf O).map φ) U c) x
  exact this

/-- **Semilinearity of the germ reindexing along a restriction.** The `ModuleColimit` scalar
actions at `U` and at `V` are computed by the same levelwise action, so `pbAbReindex` is
semilinear over `pbRingReindex`. -/
theorem pbReindex_smul (O : Dᵒᵖ ⥤ RingCat.{w}) (G : PresheafOfModules.{w} O)
    {U V : Cᵒᵖ} (i : U ⟶ V) (a : ↑(colimit (pbRdiag u O U)))
    (s : ↑(colimit (pbMmod u O G U).presheaf)) :
    letI := pbInstCM u O G U
    letI := pbInstCM u O G V
    pbAbReindex u O G i (a • s) = pbRingReindex u O i a • pbAbReindex u O G i s := by
  let := pbInstCM u O G U
  let := pbInstCM u O G V
  obtain ⟨c, a₀, s₀, ha, hs⟩ :=
    PresheafOfModules.ModuleColimit.jointly_surjective₂
      (hcR := colimit.isColimit (pbRdiag u O U))
      (hcM := colimit.isColimit (pbMmod u O G U).presheaf) a s
  -- `jointly_surjective₂` states its conclusion with `ModuleColimit.ιR`/`ιM`; retype both to
  -- the `colimit.ι` spelling that every lemma below is stated at (`:=` is defeq-tolerant,
  -- a type ascription would not be).
  have ha' : colimit.ι (pbRdiag u O U) c a₀ = a := ha
  have hs' : colimit.ι (pbMmod u O G U).presheaf c s₀ = s := hs
  have key : colimit.ι (pbRdiag u O U) c a₀ • colimit.ι (pbMmod u O G U).presheaf c s₀
      = colimit.ι (pbMmod u O G U).presheaf c (a₀ • s₀) :=
    PresheafOfModules.ModuleColimit.smul_eq
      (colimit.isColimit (pbRdiag u O U)) (colimit.isColimit (pbMmod u O G U).presheaf)
      (U := c) a₀ s₀
  have key' : colimit.ι (pbRdiag u O V)
          (Opposite.op (Opposite.op ((CostructuredArrow.map i).obj c.unop.unop))) a₀ •
        colimit.ι (pbMmod u O G V).presheaf
          (Opposite.op (Opposite.op ((CostructuredArrow.map i).obj c.unop.unop))) s₀
      = colimit.ι (pbMmod u O G V).presheaf
          (Opposite.op (Opposite.op ((CostructuredArrow.map i).obj c.unop.unop))) (a₀ • s₀) :=
    PresheafOfModules.ModuleColimit.smul_eq
      (colimit.isColimit (pbRdiag u O V)) (colimit.isColimit (pbMmod u O G V).presheaf)
      (U := Opposite.op (Opposite.op ((CostructuredArrow.map i).obj c.unop.unop))) a₀ s₀
  rw [← ha', ← hs', key, pbAbReindex_ι u O G i c (a₀ • s₀), pbRingReindex_ι u O i c a₀,
    pbAbReindex_ι u O G i c s₀, key']

/-- **Linearity of the germ map induced by a morphism of modules.** `pbAbColimMap` is
`colim O`-linear, because `φ` is `O(V)`-linear levelwise. -/
theorem pbAbColimMap_smul (O : Dᵒᵖ ⥤ RingCat.{w}) {G G' : PresheafOfModules.{w} O}
    (φ : G ⟶ G') (U : Cᵒᵖ) (a : ↑(colimit (pbRdiag u O U)))
    (t : ↑(colimit (pbMmod u O G U).presheaf)) :
    letI := pbInstCM u O G U
    letI := pbInstCM u O G' U
    pbAbColimMap u O φ U (a • t) = a • pbAbColimMap u O φ U t := by
  let := pbInstCM u O G U
  let := pbInstCM u O G' U
  obtain ⟨c, a₀, t₀, ha, ht⟩ :=
    PresheafOfModules.ModuleColimit.jointly_surjective₂
      (hcR := colimit.isColimit (pbRdiag u O U))
      (hcM := colimit.isColimit (pbMmod u O G U).presheaf) a t
  have ha' : colimit.ι (pbRdiag u O U) c a₀ = a := ha
  have ht' : colimit.ι (pbMmod u O G U).presheaf c t₀ = t := ht
  have key : colimit.ι (pbRdiag u O U) c a₀ • colimit.ι (pbMmod u O G U).presheaf c t₀
      = colimit.ι (pbMmod u O G U).presheaf c (a₀ • t₀) :=
    PresheafOfModules.ModuleColimit.smul_eq
      (colimit.isColimit (pbRdiag u O U)) (colimit.isColimit (pbMmod u O G U).presheaf)
      (U := c) a₀ t₀
  have key' : colimit.ι (pbRdiag u O U) c a₀ •
        colimit.ι (pbMmod u O G' U).presheaf c (pbMmodApp u O φ U c t₀)
      = colimit.ι (pbMmod u O G' U).presheaf c (a₀ • pbMmodApp u O φ U c t₀) :=
    PresheafOfModules.ModuleColimit.smul_eq
      (colimit.isColimit (pbRdiag u O U)) (colimit.isColimit (pbMmod u O G' U).presheaf)
      (U := c) a₀ (pbMmodApp u O φ U c t₀)
  rw [← ha', ← ht', key, pbAbColimMap_ι u O φ U c (a₀ • t₀), pbAbColimMap_ι u O φ U c t₀, key']
  congr 1
  exact (φ.app ((pbIdx u U).obj c)).hom.map_smul a₀ t₀

/-- Elementwise form of a commuting square of isomorphisms in a concrete category. -/
private theorem apply_hom_eq_of_comp_eq {C : Type*} [Category C] {FC : C → C → Type*}
    {CC : C → Type*} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    {X X' Y Y' Z Z' : C} (e : X ≅ X') (e' : Y ≅ Y') (f : X' ⟶ Y') (a : X ⟶ Z) (g : Z ⟶ Z')
    (b : Z' ⟶ Y) (h : e.hom ≫ f ≫ e'.inv = a ≫ g ≫ b) (x : CC X) :
    f (e.hom x) = e'.hom (b (g (a x))) := by
  rw [← Category.assoc, Iso.comp_inv_eq] at h
  simpa using ConcreteCategory.congr_hom h x

/-- Inverse form of a naturality square for a pair of isomorphisms. -/
private theorem symm_apply_eq_of_apply_eq {C : Type*} [Category C] {FC : C → C → Type*}
    {CC : C → Type*} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    {X X' Y Y' : C} (e : X ≅ X') (e' : Y ≅ Y') (f : X' ⟶ Y') (g : CC X → CC Y)
    (h : ∀ x, f (e.hom x) = e'.hom (g x)) (m : CC X') :
    e'.inv (f m) = g (e.inv m) := by
  have := h (e.inv m)
  rw [e.inv_hom_id_apply] at this
  rw [this]
  exact e'.hom_inv_id_apply _

omit [RepresentablyFlat u] in
/-- Element-level naturality of `pbAbIso` against the restriction map: pushing the germ
of `(pbMmod U).presheaf` at index `j` through `pbAbIso U` and then restricting equals
pushing the same section through `pbAbIso V` at the reindexed germ. -/
theorem pbAbIso_naturality (O : Dᵒᵖ ⥤ RingCat.{w}) (G : PresheafOfModules.{w} O)
    {U V : Cᵒᵖ} (i : U ⟶ V) (x : ↑(colimit (pbMmod u O G U).presheaf)) :
    (upAb u (underlyingAb O G)).map i ((pbAbIso u O G U).hom x)
      = (pbAbIso u O G V).hom (pbAbReindex u O G i x) := by
  refine apply_hom_eq_of_comp_eq _ _ _ _ _ _ ?_ x
  rw [pbAbIso, pbAbIso]
  simp only [Iso.trans_hom, Iso.trans_inv, Category.assoc]
  rw [reassoc_of% (upAbObjIso_hom_map_inv u O G i)]

/-- The ring analogue of `pbAbIso_naturality`. -/
theorem pbRingIso_naturality (O : Dᵒᵖ ⥤ RingCat.{w})
    {U V : Cᵒᵖ} (i : U ⟶ V) (x : ↑(colimit (pbRdiag u O U))) :
    (upRing u O).map i ((pbRingIso u O U).hom x)
      = (pbRingIso u O V).hom (pbRingReindex u O i x) := by
  refine apply_hom_eq_of_comp_eq _ _ _ _ _ _ ?_ x
  rw [pbRingIso, pbRingIso]
  simp only [Iso.trans_hom, Iso.trans_inv, Category.assoc]
  rw [reassoc_of% (upRingObjIso_hom_map_inv u O i)]

omit [RepresentablyFlat u] in
/-- **Morphism-level naturality of `pbAbIso`.** For a morphism `φ : G ⟶ G'` of
`O`-modules, the underlying Ab-presheaf morphism `u_p φ̲` at `U`, conjugated through the
`pbAbIso` comparison isos, equals the levelwise colimit map of `φ̲`. -/
theorem pbAbIso_morphism_naturality (O : Dᵒᵖ ⥤ RingCat.{w})
    {G G' : PresheafOfModules.{w} O} (φ : G ⟶ G') (U : Cᵒᵖ)
    (x : ↑(colimit (pbMmod u O G U).presheaf)) :
    (upAbMap u O φ).app U ((pbAbIso u O G U).hom x)
      = (pbAbIso u O G' U).hom (pbAbColimMap u O φ U x) := by
  refine apply_hom_eq_of_comp_eq _ _ _ _ _ _ ?_ x
  rw [pbAbIso, pbAbIso]
  simp only [Iso.trans_hom, Iso.trans_inv, Category.assoc]
  rw [reassoc_of% (upAbObjIso_hom_app_inv u O φ U)]

/-- `pbRingIso` carries the restriction map of `u_p O` to the germ reindexing
`pbRingReindex`; the inverse form of `pbRingIso_naturality`. -/
theorem pbRingIso_symm_naturality (O : Dᵒᵖ ⥤ RingCat.{w}) {U V : Cᵒᵖ}
    (i : U ⟶ V) (r : (upRing u O).obj U) :
    (pbRingIso u O V).ringCatIsoToRingEquiv.symm ((upRing u O).map i r)
      = pbRingReindex u O i ((pbRingIso u O U).ringCatIsoToRingEquiv.symm r) := by
  exact symm_apply_eq_of_apply_eq _ _ _ _ (pbRingIso_naturality u O i) r

omit [RepresentablyFlat u] in
/-- `pbAbIso` carries the restriction map of `u_p G` to the germ reindexing `pbAbReindex`;
the inverse form of `pbAbIso_naturality`. -/
theorem pbAbIso_symm_naturality (O : Dᵒᵖ ⥤ RingCat.{w}) (G : PresheafOfModules.{w} O)
    {U V : Cᵒᵖ} (i : U ⟶ V) (m : (upAb u (underlyingAb O G)).obj U) :
    (pbAbIso u O G V).symm.hom ((upAb u (underlyingAb O G)).map i m)
      = pbAbReindex u O G i ((pbAbIso u O G U).symm.hom m) := by
  exact symm_apply_eq_of_apply_eq _ _ _ _ (pbAbIso_naturality u O G i) m

omit [RepresentablyFlat u] in
/-- `pbAbIso` carries `u_p φ̲` to `pbAbColimMap`; the inverse form of
`pbAbIso_morphism_naturality`. -/
theorem pbAbIso_symm_morphism_naturality (O : Dᵒᵖ ⥤ RingCat.{w})
    {G G' : PresheafOfModules.{w} O} (φ : G ⟶ G') (U : Cᵒᵖ)
    (m : (upAb u (underlyingAb O G)).obj U) :
    (pbAbIso u O G' U).symm.hom
        ((upAbMap u O φ).app U m)
      = pbAbColimMap u O φ U ((pbAbIso u O G U).symm.hom m) := by
  exact symm_apply_eq_of_apply_eq _ _ _ _ (pbAbIso_morphism_naturality u O φ U) m

/-- **Semilinearity of the restriction maps of `u_p G`.**

For `i : U ⟶ V` in `Cᵒᵖ`, `r : (u_p O)(U)` and `m : (u_p G)(U)`, one has
`(r • m)|_V = r|_V • m|_V` for the `upModule` actions at `U` and at `V`. Together with
`upModule` this is the module-presheaf structure asserted by the tag.

The proof reduces `r` and `m` to a common germ over some `V₀ ∈ I^u_U` (joint surjectivity for
`ModuleColimit`), pushes the restriction maps through the comparison isomorphisms — where
`Stacks.PresheafOfModules.Pullback.leftKanExtensionObjIsoColimit_naturality` re-indexes the germ
  from `I^u_U` to
`I^u_V` — and
concludes because the *same* levelwise `O(V₀)`-action computes both sides, by the germ formula
`ModuleColimit.smul_eq` at `U` and at `V`. -/
theorem upModule_map_smul (O : Dᵒᵖ ⥤ RingCat.{w}) (G : PresheafOfModules.{w} O)
    ⦃U V : Cᵒᵖ⦄ (i : U ⟶ V) (r : (upRing u O).obj U)
    (m : (upAb u (underlyingAb O G)).obj U) :
    letI : ∀ W, Module ((upRing u O).obj W) ((upAb u (underlyingAb O G)).obj W) :=
      upModule u O G
    (upAb u (underlyingAb O G)).map i (r • m)
      = (upRing u O).map i r • (upAb u (underlyingAb O G)).map i m := by
  rw [upModule_smul_eq u O G U r m,
    upModule_smul_eq u O G V ((upRing u O).map i r)
      ((upAb u (underlyingAb O G)).map i m),
    pbRingIso_symm_naturality u O i r, pbAbIso_symm_naturality u O G i m,
    ← pbReindex_smul u O G i]
  exact pbAbIso_naturality u O G i _

/-- **Linearity of the underlying Ab map of `Φ.map φ` (functoriality semilinearity).**
For a morphism `φ : G ⟶ G'` of `O`-modules, the Ab-presheaf morphism `u_p φ̲` at `U` is
`(u_p O)(U)`-linear with respect to the `upModule` scalar actions on source and
target. This is the linearity obligation needed to package `Φ.map φ` via `homMk`. -/
theorem upModule_morphism_smul (O : Dᵒᵖ ⥤ RingCat.{w})
    {G G' : PresheafOfModules.{w} O} (φ : G ⟶ G') (U : Cᵒᵖ) (r : (upRing u O).obj U)
    (m : (upAb u (underlyingAb O G)).obj U) :
    letI := upModule u O G U
    letI := upModule u O G' U
    (upAbMap u O φ).app U (r • m)
      = r • (show (upAb u (underlyingAb O G')).obj U from (upAbMap u O φ).app U m) := by
  let := pbInstCM u O G U
  let := pbInstCM u O G' U
  rw [upModule_smul_eq u O G U r m,
    upModule_smul_eq u O G' U r
      ((upAbMap u O φ).app U m),
    pbAbIso_morphism_naturality u O φ U
      ((pbRingIso u O U).ringCatIsoToRingEquiv.symm r • (pbAbIso u O G U).symm.hom m)]
  congr 1
  rw [pbAbColimMap_smul]
  congr 1
  exact (pbAbIso_symm_morphism_naturality u O φ U m).symm


/-- **The module-level `u_p` (statement form).**

Let `O` be a presheaf of rings on `D` and `G` a presheaf of `O`-modules. Then the
pullback presheaf of abelian groups `u_p G` carries the structure of a presheaf of
`u_p O`-modules: there is a presheaf of `u_p O`-modules `M` whose underlying presheaf of
abelian groups is exactly `u_p G`.

The data of `M : PresheafOfModules (u_p O)` packages, for each open `U ⊆ X`, the scalar
multiplication `(u_p O)(U) × (u_p G)(U) → (u_p G)(U)` together with the module axioms and
the compatibility with the restriction maps. That `toPresheaf.obj M` is literally the
pullback presheaf `u_p G` expresses that this module structure lives on `u_p G` itself. -/
theorem up_presheaf_module (O : Dᵒᵖ ⥤ RingCat.{w}) (G : PresheafOfModules.{w} O) :
    ∃ M : PresheafOfModules.{w} (upRing u O),
      (PresheafOfModules.toPresheaf (upRing u O)).obj M =
        upAb u (underlyingAb O G) := by
  -- Equip each section `(u_p G)(U)` with the `(u_p O)(U)`-module structure of
  -- `upModule`, assemble via `PresheafOfModules.ofPresheaf`
  -- (semilinearity = `upModule_map_smul`), and read off the equality:
  -- `(ofPresheaf P h).presheaf = P` holds by `rfl`, hence `(toPresheaf _).obj M = P` by `rfl`.
  let : ∀ W, Module ((upRing u O).obj W) ((upAb u (underlyingAb O G)).obj W) :=
    upModule u O G
  refine ⟨PresheafOfModules.ofPresheaf (upAb u (underlyingAb O G))
    (fun U V i r m => upModule_map_smul u O G i r m), ?_⟩
  rfl

/-- **The functor lifting `u_p` to presheaves of modules.**

The construction of the module structure is functorial in `G`: `u_p` lifts to a functor
`Φ : PresheafOfModules O ⥤ PresheafOfModules (u_p O)` from the category of presheaves of
`O`-modules on `Y` to the category of presheaves of `u_p O`-modules on `X`.  That it lies
over the abelian-group-level functor `u_p` is `upModuleFunctorCompToPresheaf`.

On objects it sends `G` to the presheaf of `u_p O`-modules with carrier `u_p G` and the
scalar action of `upModule`. On a morphism `φ : G ⟶ G'` of `O`-modules with underlying
Ab-presheaf morphism `φ̲`, it takes `u.op.lan.map φ̲ : u_p G ⟶ u_p G'`,
which is `(u_p O)(U)`-linear for each `U` by `upModule_morphism_smul`: it is `colim` of
the levelwise `O(V)`-linear maps `φ_V`, and the action is built from the levelwise
`O(V)`-actions. Functoriality is inherited from that of `u.op.lan`, since
`PresheafOfModules.homMk` is built on top of it and `toPresheaf` is faithful. -/
noncomputable def upModuleFunctor (O : Dᵒᵖ ⥤ RingCat.{w}) :
    PresheafOfModules.{w} O ⥤ PresheafOfModules.{w} (upRing u O) where
  obj G :=
    letI : ∀ W, Module ((upRing u O).obj W) ((upAb u (underlyingAb O G)).obj W) :=
      upModule u O G
    PresheafOfModules.ofPresheaf (upAb u (underlyingAb O G))
      (fun U V i r m => upModule_map_smul u O G i r m)
  map {G G'} φ :=
    letI : ∀ W, Module ((upRing u O).obj W) ((upAb u (underlyingAb O G)).obj W) :=
      upModule u O G
    letI : ∀ W, Module ((upRing u O).obj W) ((upAb u (underlyingAb O G')).obj W) :=
      upModule u O G'
    PresheafOfModules.homMk (upAbMap u O φ)
      (fun U r m => upModule_morphism_smul u O φ U r m)
  map_id G := by
    apply (PresheafOfModules.toPresheaf (upRing u O)).map_injective
    change (u.op.lan).map ((PresheafOfModules.toPresheaf O).map (𝟙 G))
      = 𝟙 _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  map_comp {G G' G''} φ ψ := by
    apply (PresheafOfModules.toPresheaf (upRing u O)).map_injective
    change (u.op.lan).map ((PresheafOfModules.toPresheaf O).map (φ ≫ ψ))
      = (u.op.lan).map ((PresheafOfModules.toPresheaf O).map φ) ≫
        (u.op.lan).map ((PresheafOfModules.toPresheaf O).map ψ)
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]

/-- **The comparison isomorphism expressing that `upModuleFunctor` lies over `u_p`:**
`Φ ⋙ toPresheaf (u_p O) ≅ toPresheaf O ⋙ u.op.lan`.

Lying over `u_p` means that forgetting the module structure of `Φ.obj G` recovers `u_p`
applied to the abelian-group presheaf underlying `G`, naturally in `G`.  In particular, for
a morphism `φ : G → G'` of presheaves of `O`-modules, `Φ.map φ` is a morphism of presheaves
of `u_p O`-modules whose underlying morphism of presheaves of abelian groups is `u_p φ`.

It is the identity natural isomorphism: `Φ.obj G` is `ofPresheaf (u_p (underlying G)) …`,
whose underlying Ab presheaf is `u_p (underlying G)` on the nose, and `Φ.map φ` is
`homMk (u_p φ̲) …`, whose underlying Ab map is `u_p φ̲` on the nose, so both composites agree
definitionally (compare `pushforward₀CompToPresheaf` and `restrictScalarsCompToPresheaf` in
Mathlib, both also `Iso.refl _`). -/
noncomputable def upModuleFunctorCompToPresheaf (O : Dᵒᵖ ⥤ RingCat.{w}) :
    upModuleFunctor u O ⋙ PresheafOfModules.toPresheaf (upRing u O) ≅
      PresheafOfModules.toPresheaf O ⋙ u.op.lan :=
  Iso.refl _


/- The unit (germ) formula for the scalar action.

The action of `upModule` is a *transport* of `ModuleColimit`'s action along
`pbRingIso`/`pbAbIso`, so on its own it says nothing about concrete elements. The lemmas
below turn it into the germ formula that consumers need: the Kan-extension units
`O(V) → (u_p O)(u V)` and `G(V) → (u_p G)(u V)` are semilinear,

  unit (a • m) = unit a • unit m.

Equivalently: `(u_p O)(u V)` and `(u_p G)(u V)` are the colimits over `I^u_{u V}`, and the
unit is the injection at the object `(V, 𝟙 (u V))` of `I^u_{u V}`, so the formula is
`ModuleColimit.smul_eq` at that one index, read through the two comparison isomorphisms and
the `opOpEquivalence` reindexing. -/

/-- The index of the germ computed by the unit at `V`: the object `(V, 𝟙 (u V))` of the
neighbourhood category `I^u_{u V} = CostructuredArrow u.op (u V)`, written in
the double opposite used by `pbIdx`. -/
@[reducible] noncomputable def pbUnitIdx (V : Dᵒᵖ) :
    ((CostructuredArrow u.op (u.op.obj V))ᵒᵖ)ᵒᵖ :=
  Opposite.op (Opposite.op (CostructuredArrow.mk (Y := V) (𝟙 (u.op.obj V))))

/-- The unit `O(V) → (u_p O)(u V)` of the presheaf of rings `u_p O`, i.e. the map
sending a section over `V` to its germ over `u V`. -/
noncomputable def upRingUnit (O : Dᵒᵖ ⥤ RingCat.{w}) (V : Dᵒᵖ) :
    O.obj V ⟶ (upRing u O).obj (u.op.obj V) :=
  (u.op.leftKanExtensionUnit O).app V

/-- The unit `G(V) → (u_p G)(u V)` of the presheaf of abelian groups `u_p G`. -/
noncomputable def upAbUnit (G : Dᵒᵖ ⥤ AddCommGrpCat.{w}) (V : Dᵒᵖ) :
    G.obj V ⟶ (upAb u G).obj (u.op.obj V) :=
  (u.op.leftKanExtensionUnit G).app V

omit [RepresentablyFlat u] in
/-- The unit `G(V) → (u_p G)(u V)` is the germ at the index `pbUnitIdx`, i.e. the
colimit injection there followed by the comparison isomorphism `pbAbIso`. -/
theorem pbAbIso_unit (O : Dᵒᵖ ⥤ RingCat.{w}) (G : PresheafOfModules.{w} O)
    (V : Dᵒᵖ) (m : G.obj V) :
    (pbAbIso u O G (u.op.obj V)).hom
        (colimit.ι (pbMmod u O G (u.op.obj V)).presheaf (pbUnitIdx u V) m)
      = upAbUnit u (underlyingAb O G) V m := by
  have hmor :
      colimit.ι ((opOpEquivalence
            (CostructuredArrow u.op (u.op.obj V))).functor ⋙
          (CostructuredArrow.proj u.op (u.op.obj V) ⋙ G.presheaf))
          (pbUnitIdx u V) ≫
        ((Functor.Final.colimitIso
            (opOpEquivalence
              (CostructuredArrow u.op (u.op.obj V))).functor
            (CostructuredArrow.proj u.op (u.op.obj V) ⋙
              G.presheaf)).hom ≫
          (u.op.leftKanExtensionObjIsoColimit G.presheaf
            (u.op.obj V)).inv)
      = (u.op.leftKanExtensionUnit G.presheaf).app V := by
    rw [← Category.assoc, Functor.Final.ι_colimitIso_hom]
    exact Stacks.PresheafOfModules.Pullback.leftKanExtensionUnit_eq_ι_leftKanExtensionObjIsoColimit
      u.op G.presheaf V
  have h2 := ConcreteCategory.congr_hom hmor m
  rw [pbAbIso, upAbUnit]
  exact h2

/-- The ring analogue of `pbAbIso_unit`. -/
theorem pbRingIso_unit (O : Dᵒᵖ ⥤ RingCat.{w})
    (V : Dᵒᵖ) (a : O.obj V) :
    (pbRingIso u O (u.op.obj V)).hom
        (colimit.ι (pbRdiag u O (u.op.obj V)) (pbUnitIdx u V) a)
      = upRingUnit u O V a := by
  have hmor :
      colimit.ι ((opOpEquivalence
            (CostructuredArrow u.op (u.op.obj V))).functor ⋙
          (CostructuredArrow.proj u.op (u.op.obj V) ⋙ O))
          (pbUnitIdx u V) ≫
        ((Functor.Final.colimitIso
            (opOpEquivalence
              (CostructuredArrow u.op (u.op.obj V))).functor
            (CostructuredArrow.proj u.op (u.op.obj V) ⋙ O)).hom ≫
          (u.op.leftKanExtensionObjIsoColimit O
            (u.op.obj V)).inv)
      = (u.op.leftKanExtensionUnit O).app V := by
    rw [← Category.assoc, Functor.Final.ι_colimitIso_hom]
    exact Stacks.PresheafOfModules.Pullback.leftKanExtensionUnit_eq_ι_leftKanExtensionObjIsoColimit
      u.op O V
  have h2 := congrArg (fun φ => (ConcreteCategory.hom φ) a) hmor
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h2
  rw [pbRingIso, upRingUnit]
  exact h2

/-- **Semilinearity of the Kan-extension unit (the germ formula for the scalar action).**

For `a : O(V)` and `m : G(V)`, the unit maps into the presheaves `u_p O`, `u_p G` at `u V`
satisfy `unit (a • m) = unit a • unit m`, where the action on the right is the
`upModule` action of `(u_p O)(u V)` on `(u_p G)(u V)`.

This is the elementwise content of Stacks 008T that the transported definition of the
action does not expose: `upModule_smul_eq` describes `•` only through the
comparison isomorphisms `pbRingIso`/`pbAbIso`. Here both germs are pushed back to the
single index `pbUnitIdx` (the object `(V, 𝟙 (u V))` of `I^u_{u V}`), where the action is
`ModuleColimit.smul_eq` and the levelwise module is `G(V)` itself. -/
theorem upModule_unit_smul (O : Dᵒᵖ ⥤ RingCat.{w}) (G : PresheafOfModules.{w} O)
    (V : Dᵒᵖ) (a : O.obj V) (m : G.obj V) :
    letI := upModule u O G (u.op.obj V)
    upAbUnit u (underlyingAb O G) V (a • m)
      = upRingUnit u O V a • upAbUnit u (underlyingAb O G) V m := by
  let := pbInstCM u O G (u.op.obj V)
  -- Expose the transported action through the comparison isos.
  rw [upModule_smul_eq u O G (u.op.obj V)
    (upRingUnit u O V a) (upAbUnit u (underlyingAb O G) V m)]
  -- Both unit images are germs at `pbUnitIdx`, so the isos undo to colimit injections.
  have hR : (pbRingIso u O (u.op.obj V)).ringCatIsoToRingEquiv.symm
      (upRingUnit u O V a)
      = colimit.ι (pbRdiag u O (u.op.obj V)) (pbUnitIdx u V) a := by
    rw [← pbRingIso_unit u O V a]
    exact (pbRingIso u O (u.op.obj V)).ringCatIsoToRingEquiv.symm_apply_apply _
  have hM : (pbAbIso u O G (u.op.obj V)).symm.hom
      (upAbUnit u (underlyingAb O G) V m)
      = colimit.ι (pbMmod u O G (u.op.obj V)).presheaf (pbUnitIdx u V) m := by
    rw [← pbAbIso_unit u O G V m]
    exact (pbAbIso u O G (u.op.obj V)).hom_inv_id_apply _
  -- `ModuleColimit`'s germ formula at the single index `pbUnitIdx`, whose levelwise
  -- module is `G(V)` with its own `O(V)`-action.
  have key : colimit.ι (pbRdiag u O (u.op.obj V)) (pbUnitIdx u V) a •
        colimit.ι (pbMmod u O G (u.op.obj V)).presheaf (pbUnitIdx u V) m
      = colimit.ι (pbMmod u O G (u.op.obj V)).presheaf (pbUnitIdx u V) (a • m) :=
    PresheafOfModules.ModuleColimit.smul_eq
      (colimit.isColimit (pbRdiag u O (u.op.obj V)))
      (colimit.isColimit (pbMmod u O G (u.op.obj V)).presheaf)
      (U := pbUnitIdx u V) a m
  rw [hR, hM, key]
  exact (pbAbIso_unit u O G V (a • m)).symm

/-- The Kan-extension unit as a morphism of presheaves of rings `O ⟶ u.op ⋙ u_p O`.

This is the morphism of presheaves of rings along which the module-level pushforward and
pullback of Mathlib are taken: `PresheafOfModules.pushforward (ringUnit u O)` is the functor
`PresheafOfModules (u_p O) ⥤ PresheafOfModules O` sending `M` to `V ↦ M(u V)` with scalars
restricted along `ringUnit`, and `upModuleFunctor u O` is the candidate left adjoint. -/
noncomputable def ringUnit (O : Dᵒᵖ ⥤ RingCat.{w}) : O ⟶ u.op ⋙ upRing u O :=
  u.op.lanUnit.app O

/-- **Reduction of `f^{-1}F = (u_p F)^#` to a single adjunction.**

Mathlib's `PresheafOfModules.pullback` is defined as the left adjoint of
`PresheafOfModules.pushforward` and carries no colimit description; the source's `u_p` is the
colimit formula of this file.  The two agree as soon as the colimit formula *is* that left
adjoint, and then the source's `f^{-1}F = (u_p F)^#` is Mathlib's
`SheafOfModules.pullbackIso`.

This is a *conditional* statement: the adjunction `adj` is a hypothesis, not a result of this
file.  See the implementation notes for what proving it requires. -/
noncomputable def pullbackIsoUpModuleFunctor (O : Dᵒᵖ ⥤ RingCat.{w})
    (adj : upModuleFunctor u O ⊣ PresheafOfModules.pushforward.{w} (ringUnit u O)) :
    PresheafOfModules.pullback.{w} (ringUnit u O) ≅ upModuleFunctor u O :=
  Adjunction.leftAdjointUniq (PresheafOfModules.pullbackPushforwardAdjunction _) adj

/-! ### The germ calculus

The three facts the proof of Stacks 05VD consumes about the colimit formula, stated for an
arbitrary index `(V, φ) ∈ I^u_U` rather than only for the unit index `(V, 𝟙 (u V))`.
-/

attribute [local instance] FinallySmall.preservesColimitsOfShape_of_isFiltered

section Germ

variable (O : Dᵒᵖ ⥤ RingCat.{w}) (G : PresheafOfModules.{w} O)

/-- An object `(V, φ : U ⟶ u V)` of the index category `I^u_U`, written in the double
opposite `((CostructuredArrow u.op U)ᵒᵖ)ᵒᵖ` in which the colimit diagrams are indexed. -/
abbrev idx {U : Cᵒᵖ} (c : CostructuredArrow u.op U) :
    ((CostructuredArrow u.op U)ᵒᵖ)ᵒᵖ := op (op c)

omit [RepresentablyFlat u] in
/-- The double opposite of the index category is filtered.  Local for the same reason as
`finallySmallCostructuredArrowOp`: it is plumbing for the diagram shape `ModuleColimit`
demands, not something a consumer states anything about. -/
local instance isFilteredIdx (U : Cᵒᵖ) [IsFiltered (CostructuredArrow u.op U)] :
    IsFiltered (((CostructuredArrow u.op U)ᵒᵖ)ᵒᵖ) :=
  IsFiltered.of_equivalence (opOpEquivalence (CostructuredArrow u.op U)).symm

/-- The germ map `O(V) ⟶ (u_p O)(U)` at an index `(V, φ) ∈ I^u_U`: the colimit injection,
read through the colimit formula `pbRingIso`. -/
noncomputable def ringGerm {U : Cᵒᵖ} (c : CostructuredArrow u.op U) :
    O.obj c.left ⟶ (upRing u O).obj U :=
  colimit.ι (pbRdiag u O U) (idx u c) ≫ (pbRingIso u O U).hom

/-- The germ map `G(V) ⟶ (u_p G)(U)` at an index `(V, φ) ∈ I^u_U`: the colimit injection,
read through the colimit formula `pbAbIso`. -/
noncomputable def abGerm {U : Cᵒᵖ} (c : CostructuredArrow u.op U) :
    (underlyingAb O G).obj c.left ⟶ (upAb u (underlyingAb O G)).obj U :=
  colimit.ι (pbMmod u O G U).presheaf (idx u c) ≫ (pbAbIso u O G U).hom

/-- The inverse of the colimit formula `pbRingIso` sends the germ `ringGerm u O c a` of
`a : O.obj c.left` to the colimit injection of `a` at the index `c`. -/
lemma ringCatIsoToRingEquiv_symm_ringGerm {U : Cᵒᵖ} (c : CostructuredArrow u.op U)
    (a : O.obj c.left) :
    (pbRingIso u O U).ringCatIsoToRingEquiv.symm (ringGerm u O c a)
      = colimit.ι (pbRdiag u O U) (idx u c) a := by
  refine (pbRingIso u O U).ringCatIsoToRingEquiv.symm_apply_eq.2 ?_
  exact (ConcreteCategory.congr_hom (f := colimit.ι (pbRdiag u O U) (idx u c) ≫
    (pbRingIso u O U).hom) rfl a)

omit [RepresentablyFlat u] in
/-- The inverse of the colimit formula `pbAbIso` sends the germ `abGerm u O G c m` of
`m` to the colimit injection of `m` at the index `c`. -/
lemma pbAbIso_symm_abGerm {U : Cᵒᵖ} (c : CostructuredArrow u.op U)
    (m : (underlyingAb O G).obj c.left) :
    (pbAbIso u O G U).symm.hom (abGerm u O G c m)
      = colimit.ι (pbMmod u O G U).presheaf (idx u c) m := by
  rw [show abGerm u O G c m = (pbAbIso u O G U).hom
      (colimit.ι (pbMmod u O G U).presheaf (idx u c) m) from rfl]
  exact (pbAbIso u O G U).hom_inv_id_apply _

/-- **The germ formula for the scalar action.**  For `a : O(V)` and `m : G(V)` at an index
`(V, φ) ∈ I^u_U`, the germ of `a • m` is the product of the germs:
`[V, a] • [V, m] = [V, a • m]`.  This generalises `upModule_unit_smul` from the unit index
`(V, 𝟙 (u V))` to an arbitrary index, which is the form the proof of Stacks 05VD uses. -/
theorem germ_smul {U : Cᵒᵖ} (c : CostructuredArrow u.op U) (a : O.obj c.left)
    (m : G.obj c.left) :
    letI := upModule u O G U
    abGerm u O G c (a • m) = ringGerm u O c a • abGerm u O G c m := by
  let := pbInstCM u O G U
  have hR := ringCatIsoToRingEquiv_symm_ringGerm u O c a
  have hM := pbAbIso_symm_abGerm u O G c m
  have key : colimit.ι (pbRdiag u O U) (idx u c) a •
        colimit.ι (pbMmod u O G U).presheaf (idx u c) m
      = colimit.ι (pbMmod u O G U).presheaf (idx u c) (a • m) :=
    PresheafOfModules.ModuleColimit.smul_eq
      (colimit.isColimit (pbRdiag u O U)) (colimit.isColimit (pbMmod u O G U).presheaf)
      (U := idx u c) a m
  rw [upModule_smul_eq u O G U (ringGerm u O c a) (abGerm u O G c m), hR, hM, key]
  rfl

/-- **Joint surjectivity of the germ maps.**  A section of `u_p O` and a section of `u_p G`
over the same object `U` are germs at a *common* index `(V, φ) ∈ I^u_U`.  This is where the
directedness of `(I^u_U)ᵒᵖ` is used, and it is the step by which the proof of Stacks 05VD
replaces finitely many sections of `f^{-1}O` and `f^{-1}F` by sections over a single `V`. -/
theorem germ_jointly_surjective₂ {U : Cᵒᵖ} (r : (upRing u O).obj U)
    (m : (upAb u (underlyingAb O G)).obj U) :
    ∃ (c : CostructuredArrow u.op U) (a : O.obj c.left)
      (s : (underlyingAb O G).obj c.left), ringGerm u O c a = r ∧ abGerm u O G c s = m := by
  let := pbInstCM u O G U
  obtain ⟨c, a, s, ha, hs⟩ :=
    PresheafOfModules.ModuleColimit.jointly_surjective₂
      (hcR := colimit.isColimit (pbRdiag u O U))
      (hcM := colimit.isColimit (pbMmod u O G U).presheaf)
      ((pbRingIso u O U).ringCatIsoToRingEquiv.symm r) ((pbAbIso u O G U).symm.hom m)
  refine ⟨c.unop.unop, a, s, ?_, ?_⟩
  · refine (pbRingIso u O U).ringCatIsoToRingEquiv.symm.injective ?_
    rw [ringCatIsoToRingEquiv_symm_ringGerm]
    exact ha
  · have h₂ : (pbAbIso u O G U).symm.hom (abGerm u O G c.unop.unop s)
        = (pbAbIso u O G U).symm.hom m := (pbAbIso_symm_abGerm u O G c.unop.unop s).trans hs
    calc abGerm u O G c.unop.unop s
        = (pbAbIso u O G U).hom ((pbAbIso u O G U).symm.hom (abGerm u O G c.unop.unop s)) :=
          ((pbAbIso u O G U).inv_hom_id_apply _).symm
      _ = (pbAbIso u O G U).hom ((pbAbIso u O G U).symm.hom m) :=
          congrArg (fun x => (pbAbIso u O G U).hom x) h₂
      _ = m := (pbAbIso u O G U).inv_hom_id_apply m

/-- **A germ vanishes only for a reason visible at a later index.**  If the germ of
`m : G(V)` at `(V, φ) ∈ I^u_U` is zero in `(u_p G)(U)`, then `m` is already killed by the
restriction along some morphism `(V, φ) ⟶ (V', φ')` of `I^u_U`.  This is the second use of
directedness, and it is how the proof of Stacks 05VD arranges that `∑ f_a s_a` vanishes in
`F(V)` and not merely in `u_p F(U)`. -/
theorem abGerm_eq_zero_iff {U : Cᵒᵖ} (c : CostructuredArrow u.op U)
    (m : (underlyingAb O G).obj c.left) :
    abGerm u O G c m = 0 ↔
      ∃ (c' : CostructuredArrow u.op U) (h : c ⟶ c'),
        (underlyingAb O G).map h.left m = 0 := by
  have hzero : abGerm u O G c m = 0 ↔
      colimit.ι (pbMmod u O G U).presheaf (idx u c) m
        = colimit.ι (pbMmod u O G U).presheaf (idx u c) 0 := by
    rw [map_zero]
    exact ⟨fun h => by rw [← pbAbIso_symm_abGerm u O G c m, h, map_zero], fun h => by
      rw [show abGerm u O G c m = (pbAbIso u O G U).hom
        (colimit.ι (pbMmod u O G U).presheaf (idx u c) m) from rfl, h, map_zero]⟩
  have hcolim := Types.FilteredColimit.isColimit_eq_iff'
    (F := (pbMmod u O G U).presheaf ⋙ forget AddCommGrpCat)
    (isColimitOfPreserves (forget AddCommGrpCat)
      (colimit.isColimit (pbMmod u O G U).presheaf))
    (i := idx u c) m (0 : (underlyingAb O G).obj c.left)
  refine hzero.trans (hcolim.trans ⟨?_, ?_⟩)
  · rintro ⟨j, f, hf⟩
    exact ⟨j.unop.unop, f.unop.unop, hf.trans (map_zero ((pbMmod u O G U).presheaf.map f).hom)⟩
  · rintro ⟨c', h, hh⟩
    exact ⟨idx u c', h.op.op,
      hh.trans (map_zero ((pbMmod u O G U).presheaf.map h.op.op).hom).symm⟩

end Germ

end Stacks.ModuleUp
