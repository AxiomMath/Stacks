module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechVanishingCriteria.OnABasisForAbelianSheaves
public import StacksFrontier.Topology.Sheaves.Cohomology.FilteredColimits.SectionsOverAQuasiCompactOpen
public import StacksFrontier.Topology.Sheaves.Limits.DescendOpens
public import StacksFrontier.Topology.Sheaves.Limits.GermPullbackAbelian

/-!
# Abelian coefficients on a cofiltered limit of spectral spaces

`StacksFrontier.Topology.Sheaves.Limits.PullbackSections` and
`StacksFrontier.Topology.Sheaves.Limits.DescendOpens` prove Stacks 0A32 and Stacks 0A33 for sheaves
of **sets** on a cofiltered limit of spectral spaces.  The two colimit-comparison clauses of
Stacks 0A37 need the same comparison for sheaves of **abelian groups**.  This file supplies:

* the general transport principle along `forget AddCommGrpCat`, which is what converts a
  set-level bijectivity statement into an abelian colimit statement;
* the abelian analogue of the *first* step of Stacks 0A33 — Stacks 009F part (4) — on the limit
  space, unconditionally, together with its all-degrees strengthening, abelian Stacks 01FF;
* **abelian Stacks 0A32**, the second step, on top of the abelian germ model of
  `StacksFrontier.Topology.Sheaves.Limits.GermPullbackAbelian`; and
* **abelian Stacks 0A33** itself, for an abelian spectral sheaf system — the degree-zero input
  that the colimit-comparison clauses of Stacks 0A37 feed on.

## Main results

### Transport along the forgetful functor

* `isIso_of_bijective`: a morphism of `AddCommGrpCat` whose underlying function is bijective is
  an isomorphism.
* `isColimit_of_bijective_desc` and `bijective_desc_of_isColimit`, packaged as
  `isColimit_iff_bijective_desc`: for a **filtered** index category, a cocone of abelian groups
  is a colimit cocone *exactly* when the map induced out of the colimit of the underlying
  diagram of sets is bijective.  Filteredness is essential — it is what makes
  `forget AddCommGrpCat` preserve the colimit — and it is available in every application here,
  the index categories of Stacks 0A32 and 0A33 being `(Over i)ᵒᵖ` and `Jᵒᵖ` for cofiltered `J`.

  This is the reusable half of the passage from sheaves of sets to sheaves of abelian groups:
  any result in `StacksDraft.Topology.Sheaves.Limits` of the form "the canonical map is
  bijective" becomes an abelian `IsColimit` as soon as the abelian structures on the two sides
  are supplied.

### The hypotheses (H1) and (H2) of Stacks 0069 on a spectral space

The hypotheses (H1) and (H2) are Mathlib's `PrespectralSpace` and `QuasiSeparatedSpace`, and
they occur as hypotheses at every call site of abelian Stacks 009F, 01EW and 01FF.  A spectral
space satisfies both, so those results become unconditional there — and the vertex of a
cofiltered limit of spectral spaces is spectral by Stacks 0A2Z.

### Abelian Stacks 009F (4) and abelian Stacks 01FF on a spectral space

* `preservesColimitsOfShape_sheafSections_of_isCompact`: on a prespectral, quasi-separated space,
  sections over a quasi-compact open commute with filtered colimits of abelian sheaves, with no
  further hypothesis.  Equivalently `isIso_colimit_post_sheafSections_of_isCompact`:
  `colimᵢ 𝒜ᵢ(U) ⟶ (colimᵢ 𝒜ᵢ)(U)` is an isomorphism of abelian groups.
* `isIso_colimit_post_H'functor_of_isCompact`: the same in every degree,
  `colimᵢ Hᑫ(U, 𝒜ᵢ) ⟶ Hᑫ(U, colimᵢ 𝒜ᵢ)`.
* `SpectralDiagram.isIso_colimit_post_sheafSections_comapProj` and
  `SpectralDiagram.isIso_colimit_post_H'functor_comapProj`: the two statements at `U = pᵢ⁻¹V`
  for `V` a quasi-compact open of a stage, which is the open that Stacks 0A33 is about.

### Abelian Stacks 0A32

* `SpectralDiagram.abelianSliceFunctor` and `SpectralDiagram.abelianSliceCocone`: the slice
  diagram `a ↦ (f_a⁻¹ℱ)(f_a⁻¹U)` and the comparison cocone of Stacks 0A32, now valued in
  `AddCommGrpCat`, using the abelian germ model of
  `StacksFrontier.Topology.Sheaves.Limits.GermPullbackAbelian`.
* `SpectralDiagram.isColimitAbelianSliceCocone`: **Stacks 0A32 with abelian coefficients** — that
  cocone is a colimit cocone of abelian groups.  This is the second step of Stacks 0A33 in
  abelian form, and it is `SpectralDiagram.bijective_canonicalMap` fed to
  `isColimit_of_bijective_desc`.

### Abelian Stacks 0A33

For `S : SpectralAbelianSheafSystem.{u, u, u} J` — the system of
`StacksDraft.Ch20.Sec16.Tag0A37`, at the universes to which the two colimit-comparison clauses of
Stacks 0A37 have to be restated — all in the namespace
`Stacks.Cohomology.SpectralLimit.SpectralAbelianSheafSystem`:

* `typeSystem`: the underlying `SpectralSheafSystem` of sheaves of **sets**, obtained by composing
  with `CategoryTheory.Functor.mapPresheaf` of `forget AddCommGrpCat`.  Every identification with
  it is definitional, which is what lets the set-level Stacks 0A33 be used with no bridge.
* `pushStalk_add`: **the stalk map of an `f_a`-map is additive**, proved by a germ chase
  (`GermPullback.add_of_germ_spec`) rather than by `GermPullback.comap_add`.
* `abelianPullbackSystem`: **`SpectralSheafSystem.pullbackSystem` lifted to
  `Jᵒᵖ ⥤ Sheaf … AddCommGrpCat`**, the first input of abelian Stacks 0A33.
* `colimitSectionsIso` and `colimitSheafSectionsIso`: **the set-level vertex `F(pᵢ⁻¹U)` of Stacks
  0A33 is the underlying set of `colimⱼ 𝒜ⱼ(pᵢ⁻¹U)`, hence of the sections of the abelian colimit
  sheaf over `pᵢ⁻¹U`** — the second input.
* `abelianStageFunctor`, `abelianStageCocone` and `isColimitAbelianStageCocone`: **Stacks 0A33
  with abelian coefficients** — the cocone
  `colim_{a : j → i} 𝒜ⱼ(f_a⁻¹U) ⟶ (colimⱼ pⱼ⁻¹𝒜ⱼ)(pᵢ⁻¹U)`
  is a colimit cocone of abelian groups for every quasi-compact open `U` of a stage.
  `isColimitAbelianStageSectionsCocone` is the same statement with the vertex
  `colimⱼ 𝒜ⱼ(pᵢ⁻¹U)`, before the passage to the colimit sheaf.

## Implementation notes

### The two steps of Stacks 0A33, in abelian form

Stacks 0A33 factors into two steps, and the file supplies the abelian form of both:

1. `colimⱼ (pⱼ⁻¹Fⱼ)(pᵢ⁻¹U) ⟶ (colimⱼ pⱼ⁻¹Fⱼ)(pᵢ⁻¹U)` is invertible.  For sheaves of sets this is
   `SpectralSheafSystem.bijective_colimitCanonicalMap`, Stacks 009F (4) with its hypothesis
   supplied by `SpectralDiagram.hasFiniteCompactCofinalCovers_comapProj`.  For abelian sheaves it
   is `SpectralDiagram.isIso_colimit_post_sheafSections_comapProj` below, and
   `SpectralDiagram.isIso_colimit_post_H'functor_comapProj` upgrades it to all degrees.
2. `colim_{a : j → i} Fⱼ(f_a⁻¹U) ⟶ colimⱼ (pⱼ⁻¹Fⱼ)(pᵢ⁻¹U)` is invertible, which is the
   reindexing along `SpectralSheafSystem.comapProj_stageOpen` together with Stacks 0A32.

Step 2 now has an abelian form too: `SpectralDiagram.isColimitAbelianSliceCocone` below, which is
abelian Stacks 0A32.  The difficulty is that both sides of Stacks 0A32 are objects of the
germ model `GermPullback.sheaf`, whose sections over `W` are functions `W → Σ y, 𝒢.stalk y` — a
`Σ`-type carries no addition, and the model is `TopCat.subsheafToTypes` of a `PrelocalPredicate`,
of which there is no abelian version.  `StacksFrontier.Topology.Sheaves.Limits.GermPullbackAbelian`
removes that obstruction: the germ of a section at `z` is forced to be based at `g z`, so a
section is the same thing as a fibrewise family `f z ∈ (𝒢 ⋙ forget).stalk (g z)`, the local
condition **is** closed under pointwise addition (`GermPullback.fibrePred_add`), and the germ
model therefore lifts to a sheaf of abelian groups, `GermPullback.abelianSheaf`, whose composite
with `forget AddCommGrpCat` is the `Type`-valued model on the nose.  Feeding
`SpectralDiagram.bijective_canonicalMap` to `isColimit_of_bijective_desc` then costs nothing.

### The two inputs of abelian Stacks 0A33, and why it is not bookkeeping

Abelian Stacks 0A33 does **not** follow from steps 1 and 2 by bookkeeping, and the reason is the
vertex.  The cocone of Stacks 0A33, `SpectralSheafSystem.stageCocone`, has vertex
`(colimⱼ pⱼ⁻¹Fⱼ)(pᵢ⁻¹U)` computed as `DirectedColimitOfSheaves.colimitSheaf` of the `Type`-valued
pullback system — the sheafification of a presheaf colimit of `Type`-valued sheaves.  Two things
make that vertex an abelian group compatibly with the set-level map, and both are supplied below.

* `SpectralSheafSystem.pullbackSystem` lifted to `Jᵒᵖ ⥤ Sheaf … AddCommGrpCat`, which is
  `SpectralAbelianSheafSystem.abelianPullbackSystem`.  The objects are the abelian germ models
  `GermPullback.abelianSheaf`, but the transition maps are `pullbackMap`, built from `pushGerm` —
  the stalk map of `φ_a` — and not from `GermPullback.comap`, so their additivity is **not** the
  shape of `GermPullback.comap_add`: that one holds because pullback along a further map is
  precomposition, whereas a stalk map is not a precomposition.  The replacement is a germ chase,
  `GermPullback.add_of_germ_spec`: two germs at a point are germs of two sections over one common
  open, the germ maps of a presheaf of abelian groups are additive, and the `f_a`-map on sections
  is additive because it is a component of a morphism of presheaves of abelian groups.  It is
  cheap, but it is a different argument.
* the identification of the sections of the *abelian* colimit sheaf over `pᵢ⁻¹U` with the
  `Type`-level vertex, which is `SpectralAbelianSheafSystem.colimitSheafSectionsIso`.  Both sides
  are colimits of their respective section groups, so this is matching two colimit presentations,
  not transporting one statement: the `Type`-level vertex is a colimit of the section sets because
  `SpectralSheafSystem.bijective_colimitCanonicalMap` says the canonical map of Stacks 009F is
  bijective and evaluation at an open preserves the colimit of the colimit *presheaf*; the abelian
  colimit of section groups has the same underlying set because `forget AddCommGrpCat` preserves
  this filtered colimit; and the passage from `colimⱼ 𝒜ⱼ(pᵢ⁻¹U)` to the sections of the colimit
  *sheaf* is `SpectralDiagram.isIso_colimit_post_sheafSections_comapProj`, abelian Stacks 009F
  (4).  The two presentations are then identified by the unique isomorphism of colimit vertices,
  and it carries one comparison cocone to the other because both send a stage section to the image
  of its germ-model section under a colimit injection.

Neither is a universe issue; both are mathematics, and both are now proved.

### What abelian Stacks 0A33 does and does not give Stacks 0A37

Of the three gaps that `StacksDraft.Ch20.Sec16.Tag0A37ColimitComparison` records, abelian Stacks
0A33 closes **part of one**: the degree-zero half of the factorisation of `CohomologyCocone`'s
comparison through base change to the limit space — precisely the half named there as "absent: its
abelian analogue".  What stays open is the passage from degree zero to all degrees *across the
base change*; the all-degrees passage for a system of sheaves already living on one space is
proved, as `isIso_colimit_post_H'functor_of_isCompact` and
`SpectralDiagram.isIso_colimit_post_H'functor_comapProj` below.  The other gap — that
`Tag0A37Limit.existsUnique_pull_eq` characterises the cone point's sheaf only in corepresented
form, whereas `colimit.post` wants an honest colimit in the sheaf category — is independent of
this file and untouched by it.

### Universes

Everything is stated at a single universe `u`: `X : Type u`, coefficients `AddCommGrpCat.{u}`,
index `{I : Type u} [SmallCategory I]`.  This is forced, and is the verdict recorded in
`StacksDraft.Ch20.Sec16.Tag0A37ColimitComparison`: colimits of shape `I` in `AddCommGrpCat.{u}`
exist only for a `u`-small shape, and their exactness comes from `AB5 = AB5OfSize.{u, u}`.

The corollaries below take `J : Type u`, where `SpectralDiagram.invLimit` lands in `TopCat.{u}`.
Their `[SmallCategory …]` binders are now the *only* thing tying the index morphisms of the
system to the universe of the space: the library's Stacks 0A32 and 0A33 are stated at
`{J : Type v} [Category.{v'} J]` with `UnivLE.{max v v', max v u}`, so the index morphisms have
their own universe there.  `typeSystem` and the two `{I : Type u} [SmallCategory I]` corollaries
of this file, together with the 009F input
`Stacks.Cohomology.Sections.preservesColimitsOfShape_sheafSections_type_of_isCompact`, are what
a free-index restatement of the colimit-comparison clauses of Stacks 0A37 still waits on.

## References

* [Stacks Project, Tag 0069](https://stacks.math.columbia.edu/tag/0069)
* [Stacks Project, Tag 009F](https://stacks.math.columbia.edu/tag/009F)
* [Stacks Project, Tag 01FF](https://stacks.math.columbia.edu/tag/01FF)
* [Stacks Project, Tag 0A32](https://stacks.math.columbia.edu/tag/0A32)
* [Stacks Project, Tag 0A33](https://stacks.math.columbia.edu/tag/0A33)
* [Stacks Project, Tag 0A37](https://stacks.math.columbia.edu/tag/0A37)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

noncomputable section

namespace Stacks.Cohomology.AbelianSpectral

/-! ### Transport along the forgetful functor to sets -/

/-- A morphism of abelian groups whose underlying function is bijective is an isomorphism:
`forget AddCommGrpCat` reflects isomorphisms, and a bijection of types is an isomorphism. -/
theorem isIso_of_bijective {A B : AddCommGrpCat.{u}} (f : A ⟶ B) (hf : Function.Bijective f) :
    IsIso f :=
  have : IsIso ((forget AddCommGrpCat.{u}).map f) := (isIso_iff_bijective _).2 hf
  isIso_of_reflects_iso f (forget AddCommGrpCat.{u})

/-- **A filtered cocone of abelian groups is a colimit cocone as soon as it is one on underlying
sets.**  Let `d` be any presentation of the colimit of the underlying diagram of sets.  If the
map `d.pt ⟶ c.pt` induced by `c` is bijective, then `c` is a colimit cocone.

`forget AddCommGrpCat` preserves filtered colimits and reflects isomorphisms, hence reflects the
filtered colimits it preserves; bijectivity of the induced map says exactly that the image of `c`
under it is a colimit cocone. -/
def isColimit_of_bijective_desc {I : Type u} [SmallCategory I] [IsFiltered I]
    {A : I ⥤ AddCommGrpCat.{u}} (c : Cocone A)
    {d : Cocone (A ⋙ forget AddCommGrpCat.{u})} (hd : IsColimit d)
    (h : Function.Bijective (hd.desc ((forget AddCommGrpCat.{u}).mapCocone c))) :
    IsColimit c := by
  have hiso : IsIso (hd.desc ((forget AddCommGrpCat.{u}).mapCocone c)) :=
    (isIso_iff_bijective _).2 h
  have hset : IsColimit ((forget AddCommGrpCat.{u}).mapCocone c) := IsColimit.ofPointIso hd
  have : ReflectsColimit A (forget AddCommGrpCat.{u}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  exact isColimitOfReflects (forget AddCommGrpCat.{u}) hset

/-- The converse of `isColimit_of_bijective_desc`: a filtered colimit cocone of abelian groups
induces a bijection out of the colimit of the underlying diagram of sets, because
`forget AddCommGrpCat` preserves filtered colimits. -/
theorem bijective_desc_of_isColimit {I : Type u} [SmallCategory I] [IsFiltered I]
    {A : I ⥤ AddCommGrpCat.{u}} {c : Cocone A} (hc : IsColimit c)
    {d : Cocone (A ⋙ forget AddCommGrpCat.{u})} (hd : IsColimit d) :
    Function.Bijective (hd.desc ((forget AddCommGrpCat.{u}).mapCocone c)) := by
  have hset : IsColimit ((forget AddCommGrpCat.{u}).mapCocone c) :=
    isColimitOfPreserves (forget AddCommGrpCat.{u}) hc
  have : IsIso (hd.desc ((forget AddCommGrpCat.{u}).mapCocone c)) :=
    ⟨hset.desc d,
      hd.hom_ext fun j => by rw [← Category.assoc, hd.fac, hset.fac, Category.comp_id],
      hset.hom_ext fun j => by rw [← Category.assoc, hset.fac, hd.fac, Category.comp_id]⟩
  exact (isIso_iff_bijective _).1 this

/-- **The transport principle of route 1, as an equivalence.**  A cocone on a filtered diagram of
abelian groups is a colimit cocone if and only if the map it induces out of the colimit of the
underlying diagram of sets is bijective.

Being an equivalence, neither direction is vacuous: this is the precise sense in which a
set-level bijectivity statement — such as `SpectralDiagram.bijective_canonicalMap` (Stacks 0A32)
or `SpectralSheafSystem.bijective_stageColimitMap` (Stacks 0A33) — is the whole content of the
corresponding abelian colimit statement. -/
theorem isColimit_iff_bijective_desc {I : Type u} [SmallCategory I] [IsFiltered I]
    {A : I ⥤ AddCommGrpCat.{u}} (c : Cocone A)
    {d : Cocone (A ⋙ forget AddCommGrpCat.{u})} (hd : IsColimit d) :
    Nonempty (IsColimit c) ↔
      Function.Bijective (hd.desc ((forget AddCommGrpCat.{u}).mapCocone c)) :=
  ⟨fun ⟨hc⟩ => bijective_desc_of_isColimit hc hd, fun h => ⟨isColimit_of_bijective_desc c hd h⟩⟩

/-- **The transport principle in reflection form.**  A cocone on a filtered diagram of abelian
groups whose image under `forget AddCommGrpCat` is a colimit cocone is itself a colimit cocone.

This is the form to use when the set-level colimit cocone is not the image of the abelian one but
only isomorphic to it, so that no bijectivity statement about a chosen `desc` is available; it is
how abelian Stacks 0A33 is obtained from the set-level one below.  `IsColimit` is data, hence a
`def`. -/
def isColimit_of_isColimit_mapCocone {I : Type u} [SmallCategory I] [IsFiltered I]
    {A : I ⥤ AddCommGrpCat.{u}} (c : Cocone A)
    (h : IsColimit ((forget AddCommGrpCat.{u}).mapCocone c)) : IsColimit c :=
  have : ReflectsColimit A (forget AddCommGrpCat.{u}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  isColimitOfReflects (forget AddCommGrpCat.{u}) h

/-! ### Abelian Stacks 009F (4) and Stacks 01FF on a spectral space -/

variable {X : Type u} [TopologicalSpace X]

/-- **Stacks 009F (4) for abelian sheaves on a spectral space, unconditionally.**  On a
prespectral, quasi-separated space — in particular on any spectral space — sections over a
quasi-compact open commute with filtered colimits of abelian sheaves.

This is `Stacks.Cohomology.Sections.preservesColimitsOfShape_sheafSections_of_isCompact` with
both of its hypotheses discharged by the ambient `PrespectralSpace` and `QuasiSeparatedSpace`
instances. -/
theorem preservesColimitsOfShape_sheafSections_of_isCompact [PrespectralSpace X]
    [QuasiSeparatedSpace X] {I : Type u} [SmallCategory I] [IsFiltered I] (U : Opens X)
    (hU : IsCompact (U : Set X)) :
    PreservesColimitsOfShape I
      ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op U)) :=
  Stacks.Cohomology.Sections.preservesColimitsOfShape_sheafSections_of_isCompact
    inferInstance inferInstance U hU

/-- **The canonical map `colimᵢ 𝒜ᵢ(U) ⟶ (colimᵢ 𝒜ᵢ)(U)` is an isomorphism of abelian groups**,
for `U` a quasi-compact open of a prespectral, quasi-separated space and `𝒜` a filtered system of
abelian sheaves.  This is the explicit-map form of
`preservesColimitsOfShape_sheafSections_of_isCompact`, and the abelian analogue of the first step
of Stacks 0A33, `SpectralSheafSystem.bijective_colimitCanonicalMap`. -/
theorem isIso_colimit_post_sheafSections_of_isCompact [PrespectralSpace X]
    [QuasiSeparatedSpace X] {I : Type u} [SmallCategory I] [IsFiltered I] (U : Opens X)
    (hU : IsCompact (U : Set X))
    (𝒜 : I ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    IsIso (colimit.post 𝒜
      ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op U))) :=
  have := preservesColimitsOfShape_sheafSections_of_isCompact (X := X) (I := I) U hU
  inferInstance

section Index

universe t s

/-- **Stacks 01FF for abelian sheaves on a spectral space, unconditionally.**  Let `X` be
prespectral and quasi-separated, `U` a quasi-compact open and `𝒜` a filtered system of abelian
sheaves.  Then `colimᵢ Hᑫ(U, 𝒜ᵢ) ⟶ Hᑫ(U, colimᵢ 𝒜ᵢ)` is an isomorphism in every degree `q`.

This is `Stacks.Cohomology.AbelianBasis.isIso_colimit_post_H'functor_of_isCompact'` with both of
its hypotheses discharged.  It is the passage from degree zero to all degrees **for a system of
sheaves already living on the one space**; the remaining degree-zero input of the
colimit-comparison clauses of Stacks 0A37 is the base change to the limit space, i.e. the abelian
form of Stacks 0A32, which is discussed in the implementation notes above.

As there, the index category is free in two universes and is asked only to be `u`-small. -/
theorem isIso_colimit_post_H'functor_of_isCompact [PrespectralSpace X] [QuasiSeparatedSpace X]
    {I : Type t} [Category.{s} I] [IsFiltered I] [UnivLE.{t, u}] [UnivLE.{s, u}]
    (U : Opens X) (hU : IsCompact (U : Set X))
    (𝒜 : I ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (q : ℕ) :
    IsIso (colimit.post 𝒜 (Stacks.Cohomology.AbelianColimit.H'functor U q)) :=
  Stacks.Cohomology.AbelianBasis.isIso_colimit_post_H'functor_of_isCompact'
    inferInstance inferInstance U hU 𝒜 q

end Index

end Stacks.Cohomology.AbelianSpectral

namespace SpectralDiagram

open Stacks.Cohomology.AbelianSpectral

variable {J : Type u} [SmallCategory J] [IsCofiltered J] (D : SpectralDiagram.{u, u} J)

/-- **The abelian analogue of the first step of Stacks 0A33.**  For `V` a quasi-compact open of
the stage `X_i` and `𝒜` a filtered system of abelian sheaves on the limit `X = limⱼ Xⱼ`, the
canonical map `colimᵢ 𝒜ᵢ(pᵢ⁻¹V) ⟶ (colimᵢ 𝒜ᵢ)(pᵢ⁻¹V)` is an isomorphism of abelian groups.

The open `pᵢ⁻¹V` is quasi-compact because the projections are spectral maps (Stacks 0A2Z), and
the limit is a spectral space, so `isIso_colimit_post_sheafSections_of_isCompact` applies with no
hypothesis left over.  For sheaves of sets the corresponding statement is
`SpectralSheafSystem.bijective_colimitCanonicalMap`. -/
theorem isIso_colimit_post_sheafSections_comapProj {I : Type u} [SmallCategory I] [IsFiltered I]
    (i : J) (V : Opens (D.F.obj i)) (hV : IsCompact (V : Set (D.F.obj i)))
    (𝒜 : I ⥤ Sheaf (Opens.grothendieckTopology (D.invLimit : Type u)) AddCommGrpCat.{u}) :
    IsIso (colimit.post 𝒜
      ((sheafSections (Opens.grothendieckTopology (D.invLimit : Type u))
        AddCommGrpCat.{u}).obj (op (D.comapProj i V)))) :=
  isIso_colimit_post_sheafSections_of_isCompact _ (D.isCompact_comapProj i V hV) 𝒜

/-- **Abelian Stacks 01FF on the limit of a cofiltered diagram of spectral spaces,
unconditionally.**  For `V` a quasi-compact open of the stage `X_i`, `𝒜` a filtered system of
abelian sheaves on the limit and every degree `q`, the canonical map
`colimᵢ Hᑫ(pᵢ⁻¹V, 𝒜ᵢ) ⟶ Hᑫ(pᵢ⁻¹V, colimᵢ 𝒜ᵢ)` is an isomorphism.

This is the all-degrees form of `isIso_colimit_post_sheafSections_comapProj`, and the shape the
two colimit-comparison clauses of Stacks 0A37 need on the limit space once the comparison has
been based-changed there. -/
theorem isIso_colimit_post_H'functor_comapProj {I : Type u} [SmallCategory I] [IsFiltered I]
    (i : J) (V : Opens (D.F.obj i)) (hV : IsCompact (V : Set (D.F.obj i)))
    (𝒜 : I ⥤ Sheaf (Opens.grothendieckTopology (D.invLimit : Type u)) AddCommGrpCat.{u})
    (q : ℕ) :
    IsIso (colimit.post 𝒜
      (Stacks.Cohomology.AbelianColimit.H'functor (D.comapProj i V) q)) :=
  isIso_colimit_post_H'functor_of_isCompact _ (D.isCompact_comapProj i V hV) 𝒜 q

end SpectralDiagram

namespace SpectralDiagram

open GermPullback

variable {J : Type u} [SmallCategory J] [IsCofiltered J] (D : SpectralDiagram.{u, u} J) {i : J}
  (U : Opens (D.F.obj i)) (ℱ : (D.F.obj i).Sheaf AddCommGrpCat.{u})

/-- **The slice diagram of Stacks 0A32 with abelian coefficients**: the object `a : j ⟶ i` is sent
to the abelian group of sections of `f_a⁻¹ℱ` over `f_a⁻¹(U)` in the germ model, and a morphism of
the slice to pullback of sections along the corresponding transition map, which is additive by
`GermPullback.comap_add`.

Its image under `forget AddCommGrpCat` is `SpectralDiagram.sliceFunctor` for the underlying sheaf
of types: the underlying function of each transition map is `GermPullback.comap`, exactly as
there. -/
def abelianSliceFunctor : (Over i)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj A := AddCommGrpCat.of
    ((GermPullback.sheaf (D.mapFun A.unop.hom)
      (typePresheaf ℱ.presheaf)).presheaf.obj (op (D.slicePre U A.unop)))
  map {_ _} f := AddCommGrpCat.ofHom (GermPullback.comapAddHom ℱ.presheaf
    (D.mapFun_continuous f.unop.left) (fun z ↦ D.slice_comp f.unop z)
    (fun z ↦ D.slice_mem U f.unop z))
  map_id A := by
    refine ConcreteCategory.hom_ext _ _ fun σ ↦ ?_
    refine GermPullback.ext fun z ↦ ?_
    exact congrArg σ.1 (Subtype.ext (D.mapFun_id z.1))
  map_comp {_ _ _} f g := by
    refine ConcreteCategory.hom_ext _ _ fun σ ↦ ?_
    refine GermPullback.ext fun z ↦ ?_
    exact congrArg σ.1 (Subtype.ext (D.mapFun_comp g.unop.left f.unop.left z.1))

/-- The value of the abelian slice diagram at `a : j ⟶ i` is the group of sections of the abelian
germ model `GermPullback.abelianSheaf` of `ℱ` along `f_a`, over `f_a⁻¹(U)`. -/
lemma abelianSliceFunctor_obj (A : (Over i)ᵒᵖ) :
    (D.abelianSliceFunctor U ℱ).obj A =
      (GermPullback.abelianSheaf (D.mapFun A.unop.hom) ℱ.presheaf).presheaf.obj
        (op (D.slicePre U A.unop)) := rfl

/-- Pullback of sections along a morphism of the slice is computed pointwise, as in the
set-level `SpectralDiagram.sliceFunctor_map_val`. -/
@[simp]
lemma abelianSliceFunctor_map_val {A A' : (Over i)ᵒᵖ} (f : A ⟶ A')
    (σ : (D.abelianSliceFunctor U ℱ).obj A) (z : D.slicePre U A'.unop) :
    (((D.abelianSliceFunctor U ℱ).map f) σ).1 z =
      σ.1 ⟨D.mapFun f.unop.left z.1, D.slice_mem U f.unop z⟩ := rfl

/-- **The comparison cocone of Stacks 0A32 with abelian coefficients**: pulling sections back to
the limit `X` along the projections, which is additive by `GermPullback.comap_add`. -/
def abelianSliceCocone : Cocone (D.abelianSliceFunctor U ℱ) where
  pt := AddCommGrpCat.of
    ((GermPullback.sheaf (D.projFun i) (typePresheaf ℱ.presheaf)).presheaf.obj (op (D.limPre U)))
  ι :=
    { app A := AddCommGrpCat.ofHom (GermPullback.comapAddHom ℱ.presheaf
        (D.projFun_continuous A.unop.left) (fun x ↦ D.projFun_eq_mapFun A.unop.hom x)
        (fun x ↦ D.proj_mem U x))
      naturality := by
        intro A A' f
        refine ConcreteCategory.hom_ext _ _ fun σ ↦ ?_
        refine GermPullback.ext fun x ↦ ?_
        exact congrArg σ.1 (Subtype.ext (D.projFun_eq_mapFun f.unop.left x.1).symm) }

/-- The vertex of the abelian comparison cocone is the group of sections of the abelian germ model
of `ℱ` along `p_i`, over `p_i⁻¹(U)`. -/
lemma abelianSliceCocone_pt :
    (D.abelianSliceCocone U ℱ).pt =
      (GermPullback.abelianSheaf (D.projFun i) ℱ.presheaf).presheaf.obj (op (D.limPre U)) := rfl

/-- **Stacks 0A32 with abelian coefficients.**  For `J` a cofiltered index category, `D` a
cofiltered diagram of spectral spaces with spectral transition maps, `U` a quasi-compact open of
the stage `X_i` and `ℱ` a sheaf of abelian groups on `X_i`, the cocone
`colim_{a : j → i} (f_a⁻¹ℱ)(f_a⁻¹U) ⟶ (p_i⁻¹ℱ)(p_i⁻¹U)`
is a colimit cocone **of abelian groups**.

The proof is `SpectralDiagram.bijective_canonicalMap` (Stacks 0A32 for sheaves of sets) fed to
`Stacks.Cohomology.AbelianSpectral.isColimit_of_bijective_desc`: the index category `(Over i)ᵒᵖ`
is filtered, `forget AddCommGrpCat` therefore preserves and reflects its colimits, and the image
of `abelianSliceCocone` under the forgetful functor is the set-level `sliceCocone`.  This is an
`IsColimit`, which is data, hence a `def`. -/
def isColimitAbelianSliceCocone (hU : IsCompact (U : Set (D.F.obj i))) :
    IsColimit (D.abelianSliceCocone U ℱ) :=
  Stacks.Cohomology.AbelianSpectral.isColimit_of_bijective_desc _
    (colimit.isColimit (D.sliceFunctor U (GermPullback.typeSheaf ℱ)))
    (D.bijective_canonicalMap U (GermPullback.typeSheaf ℱ) hU)

end SpectralDiagram

namespace Stacks.Cohomology.SpectralLimit.SpectralAbelianSheafSystem

open AlgebraicGeometry GermPullback Stacks.Cohomology.AbelianSpectral

variable {J : Type u} [SmallCategory J] [IsCofiltered J]
  (S : SpectralAbelianSheafSystem.{u, u, u} J)

/-! ### The underlying system of sheaves of sets -/

/-- **The system of sheaves of sets underlying an abelian spectral sheaf system.**  Composing with
`CategoryTheory.Functor.mapPresheaf` of `forget AddCommGrpCat` replaces each sheaf of abelian
groups by its underlying sheaf of types and each `f_a`-map by its underlying map, leaving the
spaces and the continuous maps untouched; the sheaf condition transfers because
`forget AddCommGrpCat` preserves limits and reflects isomorphisms.

This is the `SpectralSheafSystem` to which Stacks 0A33 for sheaves of sets applies, and the
identifications are definitional: the presheaf at `j` is `typePresheaf` of the abelian one and the
`f_a`-map on sections is the underlying map of `φ_a`. -/
def typeSystem : SpectralSheafSystem.{u, u} J where
  E := S.E ⋙ SheafedSpace.forgetToPresheafedSpace ⋙ (forget AddCommGrpCat.{u}).mapPresheaf
  isSheaf j := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat.{u})
    (S.E.obj j).presheaf).1 (S.E.obj j).2
  isSpectralSpace j := S.spectralSpace j
  isSpectralMap a := S.spectralMap a

/-- The diagram of spaces underlying `typeSystem` is the one underlying `S` itself. -/
lemma typeSystem_diagram_F : S.typeSystem.diagram.F = S.baseDiagram := rfl

/-! ### Spellings in which the abelian structures of the germ model are found

The declarations of this section are `abbrev`s with hand-written types: each is definitionally the
corresponding component of `typeSystem`, but written so that the instances of
`StacksFrontier.Topology.Sheaves.Limits.GermPullbackAbelian` — `GermPullback.stalkAddCommGroup` and
`GermPullback.instAddCommGroupSections` — are found by instance search, which does not unfold
`typeSystem`. -/

/-- The presheaf of abelian groups at the stage `j`. -/
abbrev stagePresheaf (j : J) : ((S.E.obj j) : TopCat.{u}).Presheaf AddCommGrpCat.{u} :=
  (S.E.obj j).presheaf

/-- The transition map `f_a : X_j → X_i` of the underlying diagram of spaces, as a function. -/
abbrev stageMapFun {j i : J} (a : j ⟶ i) : (S.E.obj j) → (S.E.obj i) :=
  ConcreteCategory.hom (S.E.map a).hom.base

/-- The limit `X = limⱼ Xⱼ` of the underlying diagram of spaces. -/
abbrev invLim : TopCat.{u} := S.typeSystem.diagram.invLimit

/-- The projection `p_j : X → X_j`, as a function. -/
abbrev proj (j : J) : (S.invLim) → (S.E.obj j) := S.typeSystem.diagram.projFun j

/-- The germ model `p_j⁻¹𝒜_j` of the pullback to the limit, as a sheaf of types. -/
abbrev typePullback (j : J) : (S.invLim).Sheaf (Type u) :=
  GermPullback.sheaf (S.proj j) (typePresheaf (S.stagePresheaf j))

/-- The germ model `p_j⁻¹𝒜_j` of the pullback to the limit, as a sheaf of **abelian groups**. -/
abbrev abelianPullback (j : J) : (S.invLim).Sheaf AddCommGrpCat.{u} :=
  GermPullback.abelianSheaf (S.proj j) (S.stagePresheaf j)

/-- The germ-model pullback of the underlying system is the germ model of `typePullback`. -/
lemma typePullback_eq (j : J) : S.typePullback j = S.typeSystem.pullback j := rfl

/-- The abelian germ model forgets to the `Type`-valued one on the nose. -/
lemma abelianPullback_comp_forget (j : J) :
    typePresheaf (S.abelianPullback j).presheaf = (S.typePullback j).presheaf := rfl

/-! ### The `f_a`-map on sections and on stalks is additive -/

/-- The `f_a`-map on sections, `𝒜_i(V) → 𝒜_j(f_a⁻¹V)`. -/
abbrev pushSection {j i : J} (a : j ⟶ i) {V : Opens (S.E.obj i)}
    (t : (S.stagePresheaf i).obj (op V)) :
    (S.stagePresheaf j).obj (op ((Opens.map (S.E.map a).hom.base).obj V)) :=
  ConcreteCategory.hom ((S.E.map a).hom.c.app (op V)) t

/-- `pushSection` is the `f_a`-map on sections of the underlying system. -/
lemma pushSection_eq {j i : J} (a : j ⟶ i) {V : Opens (S.E.obj i)}
    (t : (S.stagePresheaf i).obj (op V)) : S.typeSystem.push a t = S.pushSection a t := rfl

/-- **The `f_a`-map on sections is additive**: it is a component of the morphism of presheaves of
abelian groups `φ_a : 𝒜_i ⟶ (f_a)_*𝒜_j`. -/
lemma pushSection_add {j i : J} (a : j ⟶ i) {V : Opens (S.E.obj i)}
    (s t : (S.stagePresheaf i).obj (op V)) :
    S.pushSection a (s + t) = S.pushSection a s + S.pushSection a t :=
  map_add (ConcreteCategory.hom ((S.E.map a).hom.c.app (op V))) s t

/-- The stalk map of the `f_a`-map on the underlying presheaves of types, with its source and
target spelled as stalks of `typePresheaf`.  This is the map out of which the transition maps of
the pullback system of Stacks 0A33 are built, through `SpectralSheafSystem.pushGerm`. -/
def pushStalk {j i : J} (a : j ⟶ i) (y : S.E.obj j) :
    (typePresheaf (S.stagePresheaf i)).stalkOfSize (S.stageMapFun a y) →
      (typePresheaf (S.stagePresheaf j)).stalkOfSize y :=
  ConcreteCategory.hom ((S.typeSystem.E.map a).stalkMap y)

/-- The stalk map of `φ_a` carries the germ at `f_a(y)` of `s ∈ 𝒜_i(V)` to the germ at `y` of
`φ_a s`.  This is `AlgebraicGeometry.PresheafedSpace.stalkMap_germ_apply`. -/
lemma pushStalk_germ {j i : J} (a : j ⟶ i) (y : S.E.obj j) (V : Opens (S.E.obj i))
    (hy : S.stageMapFun a y ∈ V) (s : (S.stagePresheaf i).obj (op V)) :
    S.pushStalk a y ((typePresheaf (S.stagePresheaf i)).germOfSize V _ hy s) =
      (typePresheaf (S.stagePresheaf j)).germOfSize
        ((Opens.map (S.E.map a).hom.base).obj V) y hy (S.pushSection a s) :=
  PresheafedSpace.stalkMap_germ_apply (S.typeSystem.E.map a) V y hy s

/-- **The stalk map of the `f_a`-map is additive.**  This is *not* the shape of
`GermPullback.comap_add`, which is additive because pullback of sections along a further map is
precomposition: the stalk map is not a precomposition, and the proof is instead a germ chase.
Every element of the stalk is the germ of a section (`TopCat.Presheaf.exists_germ_eq`), two germs
at a point are germs of sections over one common open, the germ maps are additive
(`GermPullback.germ_add`) and `pushSection` is additive — which is
`GermPullback.add_of_germ_spec`. -/
lemma pushStalk_add {j i : J} (a : j ⟶ i) (y : S.E.obj j)
    (ξ ζ : (typePresheaf (S.stagePresheaf i)).stalkOfSize (S.stageMapFun a y)) :
    S.pushStalk a y (ξ + ζ) = S.pushStalk a y ξ + S.pushStalk a y ζ :=
  GermPullback.add_of_germ_spec (S.stagePresheaf i) (Opens.map (S.E.map a).hom.base).obj
    (fun _ s ↦ S.pushSection a s) (S.pushStalk a y) (fun _ hV ↦ hV)
    (fun V hV s ↦ S.pushStalk_germ a y V hV s) (fun _ s t ↦ S.pushSection_add a s t) ξ ζ

/-- The stalk map of the `f_a`-map, as a morphism of abelian groups. -/
def pushStalkAddHom {j i : J} (a : j ⟶ i) (y : S.E.obj j) :
    (typePresheaf (S.stagePresheaf i)).stalkOfSize (S.stageMapFun a y) →+
      (typePresheaf (S.stagePresheaf j)).stalkOfSize y :=
  AddMonoidHom.mk' (S.pushStalk a y) (S.pushStalk_add a y)

/-- The stalk map of the `f_a`-map sends zero to zero. -/
lemma pushStalk_zero {j i : J} (a : j ⟶ i) (y : S.E.obj j) : S.pushStalk a y 0 = 0 :=
  map_zero (S.pushStalkAddHom a y)

/-- `SpectralSheafSystem.pushGerm` is the stalk map read on the value of a germ in the stalk at
the base point prescribed by `f_a`.  This is the form free of dependent casts. -/
lemma pushGerm_eq {j i : J} (a : j ⟶ i) (y : S.E.obj j)
    (γ : Germs (typePresheaf (S.stagePresheaf i))) (h : γ.1 = S.stageMapFun a y) :
    S.typeSystem.pushGerm a y γ h =
      (⟨y, S.pushStalk a y (germValue (S.stagePresheaf i) γ (S.stageMapFun a y))⟩ :
        Germs (typePresheaf (S.stagePresheaf j))) :=
  (S.typeSystem.pushGerm_congr a y (mk_germValue (S.stagePresheaf i) h).symm h rfl).trans
    (S.typeSystem.pushGerm_mk a y _ rfl)

/-! ### The transition maps of the pullback system are additive -/

/-- The transition map `p_i⁻¹𝒜_i → p_j⁻¹𝒜_j` of the pullback system on sections over `W`, with
its source and target spelled so that the abelian structures are found. -/
abbrev pullbackMap {j i : J} (a : j ⟶ i) {W : Opens (S.invLim)}
    (σ : (S.typePullback i).presheaf.obj (op W)) : (S.typePullback j).presheaf.obj (op W) :=
  S.typeSystem.pullbackMap a σ

/-- The transition map of the pullback system takes at `z` the germ based at `p_j(z)` whose stalk
value is the image under the stalk map of `φ_a` of the stalk value of `σ`. -/
lemma pullbackMap_val_pushStalk {j i : J} (a : j ⟶ i) {W : Opens (S.invLim)}
    (σ : (S.typePullback i).presheaf.obj (op W)) (z : W) :
    (S.pullbackMap a σ).1 z = (⟨S.proj j z.1, S.pushStalk a (S.proj j z.1)
      (germValue (S.stagePresheaf i) (σ.1 z) (S.stageMapFun a (S.proj j z.1)))⟩ :
        Germs (typePresheaf (S.stagePresheaf j))) :=
  S.pushGerm_eq a (S.proj j z.1) (σ.1 z) _

/-- The stalk value of a transported section. -/
lemma stalkVal_pullbackMap {j i : J} (a : j ⟶ i) {W : Opens (S.invLim)}
    (σ : (S.typePullback i).presheaf.obj (op W)) (z : W) :
    stalkVal (S.stagePresheaf j) (S.pullbackMap a σ) z = S.pushStalk a (S.proj j z.1)
      (germValue (S.stagePresheaf i) (σ.1 z) (S.stageMapFun a (S.proj j z.1))) := by
  rw [stalkVal, S.pullbackMap_val_pushStalk a σ z, germValue_mk]

/-- **The transition maps of the pullback system are additive.**  Addition of germ-model sections
is addition of stalk values (`GermPullback.add_val`), the stalk value of a transported section is
the image of the stalk value (`stalkVal_pullbackMap`), reading a sum of germs in a prescribed
stalk is additive (`GermPullback.germValue_add_mk`), and the stalk map of `φ_a` is additive
(`pushStalk_add`). -/
lemma pullbackMap_add {j i : J} (a : j ⟶ i) {W : Opens (S.invLim)}
    (σ τ : (S.typePullback i).presheaf.obj (op W)) :
    S.pullbackMap a (σ + τ) = S.pullbackMap a σ + S.pullbackMap a τ := by
  refine GermPullback.ext fun z ↦ ?_
  have hR : (S.pullbackMap a σ + S.pullbackMap a τ).1 z =
      (⟨S.proj j z.1, S.pushStalk a (S.proj j z.1)
          (germValue (S.stagePresheaf i) (σ.1 z) (S.stageMapFun a (S.proj j z.1))) +
        S.pushStalk a (S.proj j z.1)
          (germValue (S.stagePresheaf i) (τ.1 z) (S.stageMapFun a (S.proj j z.1)))⟩ :
            Germs (typePresheaf (S.stagePresheaf j))) := by
    rw [add_val, S.stalkVal_pullbackMap, S.stalkVal_pullbackMap]
  rw [hR, S.pullbackMap_val_pushStalk a (σ + τ) z, ← S.pushStalk_add,
    ← val_eq_mk (S.stagePresheaf i) σ z, ← val_eq_mk (S.stagePresheaf i) τ z,
    ← germValue_add_mk, add_val]

/-- The transition maps of the pullback system send zero to zero. -/
lemma pullbackMap_zero {j i : J} (a : j ⟶ i) {W : Opens (S.invLim)} :
    S.pullbackMap a (0 : (S.typePullback i).presheaf.obj (op W)) = 0 := by
  refine GermPullback.ext fun z ↦ ?_
  rw [S.pullbackMap_val_pushStalk a 0 z, zero_val, zero_val, germValue_zero_mk, S.pushStalk_zero]

/-- The transition map of the pullback system, as a morphism of abelian groups. -/
def pullbackMapAddHom {j i : J} (a : j ⟶ i) (W : Opens (S.invLim)) :
    (S.typePullback i).presheaf.obj (op W) →+ (S.typePullback j).presheaf.obj (op W) :=
  AddMonoidHom.mk' (S.pullbackMap a) (S.pullbackMap_add a)

/-- The transition maps of the pullback system compose with the identity as the identity. -/
lemma pullbackMap_id {j : J} {W : Opens (S.invLim)}
    (σ : (S.typePullback j).presheaf.obj (op W)) : S.pullbackMap (𝟙 j) σ = σ :=
  ConcreteCategory.congr_hom (NatTrans.congr_app
    (congrArg (fun f ↦ f.hom) (S.typeSystem.pullbackSystem.map_id (op j))) (op W)) σ

/-- The transition maps of the pullback system compose. -/
lemma pullbackMap_comp {k j i : J} (b : k ⟶ j) (a : j ⟶ i) {W : Opens (S.invLim)}
    (σ : (S.typePullback i).presheaf.obj (op W)) :
    S.pullbackMap (b ≫ a) σ = S.pullbackMap b (S.pullbackMap a σ) :=
  ConcreteCategory.congr_hom (NatTrans.congr_app
    (congrArg (fun f ↦ f.hom) (S.typeSystem.pullbackSystem.map_comp a.op b.op)) (op W)) σ

/-- **The abelian pullback system `j ↦ p_j⁻¹𝒜_j`, the first of the two inputs of abelian Stacks
0A33.**  This is `SpectralSheafSystem.pullbackSystem` lifted to sheaves of abelian groups: the
objects are the abelian germ models `GermPullback.abelianSheaf`, and the transition maps are the
same germwise action of the `f_a`-maps, now additive by `pullbackMap_add`.  Functoriality is
inherited from the underlying system, so the lift is again strict. -/
def abelianPullbackSystem : Jᵒᵖ ⥤ (S.invLim).Sheaf AddCommGrpCat.{u} where
  obj A := S.abelianPullback A.unop
  map {_ _} α :=
    ⟨{ app := fun W ↦ AddCommGrpCat.ofHom (S.pullbackMapAddHom α.unop W.unop)
       naturality := by
         intro _ _ _
         refine ConcreteCategory.hom_ext _ _ fun σ ↦ ?_
         exact GermPullback.ext fun _ ↦ rfl }⟩
  map_id A := by
    refine InducedCategory.hom_ext (NatTrans.ext (funext fun _ ↦ ?_))
    refine ConcreteCategory.hom_ext _ _ fun σ ↦ ?_
    exact S.pullbackMap_id σ
  map_comp {_ _ _} α β := by
    refine InducedCategory.hom_ext (NatTrans.ext (funext fun _ ↦ ?_))
    refine ConcreteCategory.hom_ext _ _ fun σ ↦ ?_
    exact S.pullbackMap_comp β.unop α.unop σ

/-- **The abelian pullback system forgets to the system of sheaves of sets on the nose**, section
groups included: for every open `W` of the limit, the diagram of section groups of the abelian
system composed with `forget AddCommGrpCat` is the diagram of section sets of the underlying
system.  This is what lets Stacks 0A33 for sheaves of sets be read as a statement about
the abelian system with no bridge. -/
lemma abelianPullbackSystem_comp_sections_forget (W : Opens (S.invLim)) :
    S.abelianPullbackSystem ⋙ ((sheafSections (Opens.grothendieckTopology (S.invLim : Type u))
        AddCommGrpCat.{u}).obj (op W)) ⋙ forget AddCommGrpCat.{u} =
      S.typeSystem.pullbackSystem ⋙ ((sheafSections
        (Opens.grothendieckTopology (S.invLim : Type u)) (Type u)).obj (op W)) := rfl

/-! ### The abelian stage diagram -/

section Stage

variable {i : J} (U : Opens (S.E.obj i))

/-- The `f_a`-map followed by a restriction, the transition map of the stage diagram. -/
abbrev pushResSection {j k : J} (a : j ⟶ k) {V : Opens (S.E.obj k)} {V' : Opens (S.E.obj j)}
    (hV' : V' ≤ (Opens.map (S.E.map a).hom.base).obj V)
    (t : (S.stagePresheaf k).obj (op V)) : (S.stagePresheaf j).obj (op V') :=
  S.typeSystem.pushRes a hV' t

/-- `pushResSection` is the `f_a`-map followed by restriction. -/
lemma pushResSection_eq {j k : J} (a : j ⟶ k) {V : Opens (S.E.obj k)} {V' : Opens (S.E.obj j)}
    (hV' : V' ≤ (Opens.map (S.E.map a).hom.base).obj V)
    (t : (S.stagePresheaf k).obj (op V)) :
    S.pushResSection a hV' t =
      ConcreteCategory.hom ((S.stagePresheaf j).map (homOfLE hV').op) (S.pushSection a t) := rfl

/-- The `f_a`-map followed by a restriction is additive: both factors are. -/
lemma pushResSection_add {j k : J} (a : j ⟶ k) {V : Opens (S.E.obj k)} {V' : Opens (S.E.obj j)}
    (hV' : V' ≤ (Opens.map (S.E.map a).hom.base).obj V)
    (s t : (S.stagePresheaf k).obj (op V)) :
    S.pushResSection a hV' (s + t) = S.pushResSection a hV' s + S.pushResSection a hV' t := by
  rw [pushResSection_eq, pushResSection_eq, pushResSection_eq, S.pushSection_add, map_add]

/-- **The stage diagram of Stacks 0A33 with abelian coefficients**: the stage `a : j ⟶ i` is sent
to the abelian group `𝒜_j(f_a⁻¹U)` and a morphism of stages acts by the `f_g`-map followed by a
restriction, which is additive by `pushResSection_add`.  Its image under `forget AddCommGrpCat` is
the set-level `SpectralSheafSystem.stageFunctor`, on the nose. -/
def abelianStageFunctor : (Over i)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj A := (S.stagePresheaf A.unop.left).obj (op (S.typeSystem.diagram.slicePre U A.unop))
  map {_ _} g := AddCommGrpCat.ofHom (AddMonoidHom.mk'
    (S.pushResSection g.unop.left (S.typeSystem.stageOpen_le U g.unop))
    (S.pushResSection_add g.unop.left _))
  map_id A := by
    refine ConcreteCategory.hom_ext _ _ fun t ↦ ?_
    exact ConcreteCategory.congr_hom ((S.typeSystem.stageFunctor U).map_id A) t
  map_comp {_ _ _} g g' := by
    refine ConcreteCategory.hom_ext _ _ fun t ↦ ?_
    exact ConcreteCategory.congr_hom ((S.typeSystem.stageFunctor U).map_comp g g') t

/-- The abelian stage diagram forgets to the set-level stage diagram. -/
lemma abelianStageFunctor_comp_forget :
    S.abelianStageFunctor U ⋙ forget AddCommGrpCat.{u} = S.typeSystem.stageFunctor U := rfl

/-- The open `p_i⁻¹U` of the limit. -/
abbrev limOpen : Opens (S.invLim) := S.typeSystem.diagram.comapProj i U

/-- Sections over `p_i⁻¹U`, as a functor on sheaves of abelian groups on the limit. -/
abbrev sectionsFunctor : (S.invLim).Sheaf AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  (sheafSections (Opens.grothendieckTopology (S.invLim : Type u))
    AddCommGrpCat.{u}).obj (op (S.limOpen U))

/-- The germ-model image over `p_i⁻¹U` of a stage section, as a morphism of abelian groups.  Its
underlying function is the set-level `SpectralSheafSystem.stageToPullback`. -/
def abelianStageToPullback (A : Over i) :
    (S.abelianStageFunctor U).obj (op A) ⟶ (S.sectionsFunctor U).obj (S.abelianPullback A.left) :=
  AddCommGrpCat.ofHom (GermPullback.ofSectionAddHom (S.stagePresheaf A.left)
    (fun z ↦ S.typeSystem.projFun_mem_stageOpen U A z))

/-- `abelianStageToPullback` is the germwise image of a stage section. -/
lemma abelianStageToPullback_apply (A : Over i) (t : (S.abelianStageFunctor U).obj (op A)) :
    ConcreteCategory.hom (S.abelianStageToPullback U A) t =
      S.typeSystem.stageToPullback U A t := rfl

/-! ### Matching the two colimit presentations of the sections over `p_i⁻¹U` -/

/-- **The abelian comparison cocone of Stacks 0A33, with vertex `colimⱼ 𝒜ⱼ(p_i⁻¹U)`**: a stage
section is sent to its germ-model image, injected into the colimit of the section groups. -/
def abelianStageSectionsCocone : Cocone (S.abelianStageFunctor U) where
  pt := colimit (S.abelianPullbackSystem ⋙ S.sectionsFunctor U)
  ι :=
    { app := fun A ↦ S.abelianStageToPullback U A.unop ≫
        colimit.ι (S.abelianPullbackSystem ⋙ S.sectionsFunctor U) (op A.unop.left)
      naturality := by
        intro A B g
        refine ConcreteCategory.hom_ext _ _ fun t ↦ ?_
        have hw := ConcreteCategory.congr_hom
          (colimit.w (S.abelianPullbackSystem ⋙ S.sectionsFunctor U) (g.unop.left).op)
          (S.typeSystem.stageToPullback U A.unop t)
        refine Eq.trans ?_ hw
        exact congrArg (fun x ↦ ConcreteCategory.hom (colimit.ι
          (S.abelianPullbackSystem ⋙ S.sectionsFunctor U) (op B.unop.left)) x)
          (S.typeSystem.pullbackMap_stageToPullback U g.unop t).symm }

/-- The colimit cocone of the colimit *presheaf* of the underlying pullback system, evaluated at
`p_i⁻¹U`.  Colimits of presheaves are pointwise, so evaluation preserves them. -/
def presheafEvalCocone :
    Cocone ((S.abelianPullbackSystem ⋙ S.sectionsFunctor U) ⋙ forget AddCommGrpCat.{u}) :=
  ((evaluation (Opens (S.invLim))ᵒᵖ (Type u)).obj (op (S.limOpen U))).mapCocone
    (colimit.cocone (DirectedColimitOfSheaves.presheafSystem S.typeSystem.pullbackSystem))

/-- Evaluation at an open preserves the colimit of the presheaf system. -/
def isColimitPresheafEvalCocone : IsColimit (S.presheafEvalCocone U) :=
  isColimitOfPreserves ((evaluation (Opens (S.invLim))ᵒᵖ (Type u)).obj (op (S.limOpen U)))
    (colimit.isColimit _)

/-- **The set-level cocone with vertex `F(p_i⁻¹U)`**, `F = colimⱼ p_j⁻¹F_j` being the colimit
*sheaf*: the colimit cocone of the colimit presheaf at `p_i⁻¹U`, pushed along the canonical map of
Stacks 009F.  It is a cocone on the diagram underlying the abelian one. -/
def typeColimitCocone :
    Cocone ((S.abelianPullbackSystem ⋙ S.sectionsFunctor U) ⋙ forget AddCommGrpCat.{u}) :=
  (S.presheafEvalCocone U).extend
    (DirectedColimitOfSheaves.canonicalMap S.typeSystem.pullbackSystem (S.limOpen U))

/-- **The set-level vertex is a colimit of the section sets**, which is Stacks 009F (4) for the
pullback system: the canonical map `colimⱼ (p_j⁻¹F_j)(p_i⁻¹U) ⟶ F(p_i⁻¹U)` is bijective by
`SpectralSheafSystem.bijective_colimitCanonicalMap`, so pushing the colimit cocone along it
again gives a colimit cocone. -/
def isColimitTypeColimitCocone (hU : IsCompact (U : Set (S.E.obj i))) :
    IsColimit (S.typeColimitCocone U) := by
  have hiso : IsIso (DirectedColimitOfSheaves.canonicalMap
      S.typeSystem.pullbackSystem (S.limOpen U)) :=
    (isIso_iff_bijective _).2 (S.typeSystem.bijective_colimitCanonicalMap U hU)
  exact IsColimit.ofIsoColimit (S.isColimitPresheafEvalCocone U)
    (Cocone.ext (@asIso _ _ _ _ _ hiso) fun _ ↦ rfl)

/-- The set-level vertex receives the germ-model image of a stage section exactly as
`SpectralSheafSystem.stageCocone` does. -/
lemma typeColimitCocone_ι_app (A : Over i) (t : (S.abelianStageFunctor U).obj (op A)) :
    ConcreteCategory.hom ((S.typeColimitCocone U).ι.app (op A.left))
        (S.typeSystem.stageToPullback U A t) =
      S.typeSystem.stageToColimit U A t := rfl

/-- The colimit of the abelian section groups, forgotten: `forget AddCommGrpCat` preserves the
filtered colimit over `Jᵒᵖ`. -/
def isColimitForgetColimitSections :
    IsColimit ((forget AddCommGrpCat.{u}).mapCocone
      (colimit.cocone (S.abelianPullbackSystem ⋙ S.sectionsFunctor U))) :=
  isColimitOfPreserves (forget AddCommGrpCat.{u}) (colimit.isColimit _)

/-- **The second of the two inputs of abelian Stacks 0A33: the set-level vertex `F(p_i⁻¹U)` is the
underlying set of `colimⱼ 𝒜ⱼ(p_i⁻¹U)`.**  Both are colimits of one and the same diagram of sets —
the left-hand side by Stacks 009F (4) for the pullback system
(`isColimitTypeColimitCocone`), the right-hand side because `forget AddCommGrpCat` preserves
filtered colimits (`isColimitForgetColimitSections`) — so the two presentations are identified by
the unique isomorphism of their vertices. -/
def colimitSectionsIso (hU : IsCompact (U : Set (S.E.obj i))) :
    (S.typeColimitCocone U).pt ≅
      ((forget AddCommGrpCat.{u}).mapCocone
        (colimit.cocone (S.abelianPullbackSystem ⋙ S.sectionsFunctor U))).pt :=
  (S.isColimitTypeColimitCocone U hU).coconePointUniqueUpToIso
    (S.isColimitForgetColimitSections U)

/-- The set-level comparison cocone of Stacks 0A33 is a colimit cocone: this is Stacks
0A33, `SpectralSheafSystem.bijective_stageColimitMap`, read through
`CategoryTheory.Limits.IsColimit.ofPointIso`. -/
def isColimitStageCocone (hU : IsCompact (U : Set (S.E.obj i))) :
    IsColimit (S.typeSystem.stageCocone U) := by
  have hiso : IsIso (S.typeSystem.stageColimitMap U) :=
    (isIso_iff_bijective _).2 (S.typeSystem.bijective_stageColimitMap U hU)
  exact @IsColimit.ofPointIso _ _ _ _ _ _ _ (colimit.isColimit _) hiso

/-- **The two comparison cocones agree**: `colimitSectionsIso` carries the set-level comparison
cocone of Stacks 0A33 to the forgotten abelian one, because both send a stage section to the
image of its germ-model section under a colimit injection. -/
def stageCoconeIso (hU : IsCompact (U : Set (S.E.obj i))) :
    S.typeSystem.stageCocone U ≅
      (forget AddCommGrpCat.{u}).mapCocone (S.abelianStageSectionsCocone U) :=
  Cocone.ext (S.colimitSectionsIso U hU) fun A ↦ by
    refine ConcreteCategory.hom_ext _ _ fun t ↦ ?_
    exact ConcreteCategory.congr_hom (IsColimit.comp_coconePointUniqueUpToIso_hom
      (S.isColimitTypeColimitCocone U hU) (S.isColimitForgetColimitSections U)
      (op A.unop.left)) (S.typeSystem.stageToPullback U A.unop t)

/-- **Abelian Stacks 0A33 in the colimit-of-sections form**: the cocone
`colim_{a : j → i} 𝒜ⱼ(f_a⁻¹U) ⟶ colimⱼ 𝒜ⱼ(p_i⁻¹U)` is a colimit cocone of abelian groups.
This is the set-level Stacks 0A33 plus the identification `stageCoconeIso`, reflected
through `forget AddCommGrpCat`. -/
def isColimitAbelianStageSectionsCocone (hU : IsCompact (U : Set (S.E.obj i))) :
    IsColimit (S.abelianStageSectionsCocone U) :=
  isColimit_of_isColimit_mapCocone _
    (IsColimit.ofIsoColimit (S.isColimitStageCocone U hU) (S.stageCoconeIso U hU))

/-! ### Abelian Stacks 0A33 -/

/-- **The comparison cocone of Stacks 0A33 with abelian coefficients**:
`colim_{a : j → i} 𝒜ⱼ(f_a⁻¹U) ⟶ (colimⱼ p_j⁻¹𝒜ⱼ)(p_i⁻¹U)`, the vertex being the sections over
`p_i⁻¹U` of the colimit taken in sheaves of abelian groups.  A stage section is sent to its
germ-model image pushed into the colimit sheaf (`abelianStageCocone_ι_app`). -/
def abelianStageCocone : Cocone (S.abelianStageFunctor U) :=
  (S.abelianStageSectionsCocone U).extend
    (colimit.post S.abelianPullbackSystem (S.sectionsFunctor U))

/-- The vertex of the abelian comparison cocone is `(colimⱼ p_j⁻¹𝒜ⱼ)(p_i⁻¹U)`. -/
lemma abelianStageCocone_pt :
    (S.abelianStageCocone U).pt =
      (colimit S.abelianPullbackSystem).presheaf.obj (op (S.limOpen U)) := rfl

/-- The abelian comparison cocone sends a stage section to the image over `p_i⁻¹U` of its
germ-model section under the colimit injection `p_j⁻¹𝒜ⱼ ⟶ colimⱼ p_j⁻¹𝒜ⱼ`. -/
lemma abelianStageCocone_ι_app (A : Over i) (t : (S.abelianStageFunctor U).obj (op A)) :
    ConcreteCategory.hom ((S.abelianStageCocone U).ι.app (op A)) t =
      ConcreteCategory.hom ((S.sectionsFunctor U).map
        (colimit.ι S.abelianPullbackSystem (op A.left)))
        (S.typeSystem.stageToPullback U A t) :=
  ConcreteCategory.congr_hom
    (colimit.ι_post S.abelianPullbackSystem (S.sectionsFunctor U) (op A.left))
    (S.typeSystem.stageToPullback U A t)

/-- **Stacks 0A33 with abelian coefficients.**  Let `J` be a cofiltered index category, `S` a
cofiltered diagram of spectral spaces with spectral transition maps carrying a sheaf of abelian
groups `𝒜ⱼ` on each stage and a compatible system of `f_a`-maps, `X = limⱼ Xⱼ` the limit and
`𝒜 = colimⱼ p_j⁻¹𝒜ⱼ` on `X`.  Then for every `i` and every quasi-compact open `U ⊆ X_i` the
cocone
`colim_{a : j → i} 𝒜ⱼ(f_a⁻¹U) ⟶ 𝒜(p_i⁻¹U)`
is a colimit cocone **of abelian groups**.

The proof is the set-level Stacks 0A33, `SpectralSheafSystem.bijective_stageColimitMap`,
together with the two inputs this file supplies: the abelian pullback system
(`abelianPullbackSystem`, whose transition maps are additive by `pullbackMap_add`) and the
identification of the set-level vertex with the sections of the abelian colimit sheaf
(`colimitSectionsIso` for the colimit of section groups, then `colimit.post` — abelian Stacks
009F (4), `SpectralDiagram.isIso_colimit_post_sheafSections_comapProj` — for the passage to the
colimit sheaf). -/
def isColimitAbelianStageCocone (hU : IsCompact (U : Set (S.E.obj i))) :
    IsColimit (S.abelianStageCocone U) := by
  have hiso : IsIso (colimit.post S.abelianPullbackSystem (S.sectionsFunctor U)) :=
    S.typeSystem.diagram.isIso_colimit_post_sheafSections_comapProj i U hU
      S.abelianPullbackSystem
  exact IsColimit.ofIsoColimit (S.isColimitAbelianStageSectionsCocone U hU)
    (Cocone.ext (@asIso _ _ _ _ _ hiso) fun _ ↦ rfl)

/-- **The sections of the abelian colimit sheaf over `p_i⁻¹U` are the set-level vertex of Stacks
0A33.**  The composite of `colimitSectionsIso` with abelian Stacks 009F (4) for the pullback
system, stated as the explicit second input of abelian Stacks 0A33. -/
def colimitSheafSectionsIso (hU : IsCompact (U : Set (S.E.obj i))) :
    (S.typeColimitCocone U).pt ≅ (forget AddCommGrpCat.{u}).obj
      ((colimit S.abelianPullbackSystem).presheaf.obj (op (S.limOpen U))) :=
  have hiso : IsIso (colimit.post S.abelianPullbackSystem (S.sectionsFunctor U)) :=
    S.typeSystem.diagram.isIso_colimit_post_sheafSections_comapProj i U hU
      S.abelianPullbackSystem
  (S.colimitSectionsIso U hU).trans
    ((forget AddCommGrpCat.{u}).mapIso (@asIso _ _ _ _ _ hiso))

end Stage

end Stacks.Cohomology.SpectralLimit.SpectralAbelianSheafSystem

end

end
