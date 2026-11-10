module

public import StacksFrontier.CategoryTheory.Sites.Hypercovering.GlobalDegeneration
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The abutment filtration of a hypercovering of the final presheaf, under a refinement

Part (1) of [Stacks, Tag 09VZ] asks that every cohomology class of an abelian sheaf be the image,
under the canonical comparison `Ȟ^i(K, 𝓕) ⟶ H^i(𝓕)` of [Stacks, Tag 09VY], of a Čech class on
some hypercovering `K` of the final presheaf.  Part (2) --
`Stacks.CategoryTheory.Hypercovering.exists_hom_cechCohomologyEdge_eq` of
`StacksFrontier/CategoryTheory/Sites/Hypercovering/GlobalDegeneration.lean` -- is available in every
degree; part (1) needs on top of it the **descent of the abutment filtration along a refinement**,
and that descent is what this file carries out.  **Part (1) in every degree is
`exists_hypercoveringOfTerminal_cechCohomologyEdge_eq`.**

## Main definitions

* `Stacks.CategoryTheory.Hypercovering.globalFiltered`: the abutment `H^n(𝓕)` with the filtration
  a hypercovering of the final presheaf puts on it.  The group does not move with the
  hypercovering -- the sections over the final presheaf mention no hypercovering -- but the
  filtration does.
* `Stacks.CategoryTheory.Hypercovering.globalFilteredMap`: the morphism of filtered abutments a
  refinement induces, which is the morphism `θ` of
  `Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo.bottomRowEdge_comp_of_cocone`.
* `Stacks.CategoryTheory.Hypercovering.globalStepToAbutment`: the inclusion
  `F^jH^n(𝓕) ⟶ H^n(𝓕)` of a step of that filtration into global cohomology, with its target
  written as a value of `globalCohomologyFunctor`, which mentions no hypercovering.
* `Stacks.CategoryTheory.Hypercovering.globalGradedToPageInfinity`: the projection of a
  filtration step onto its graded piece followed by the identification
  `E_∞^{p,q} ≅ gr^pH^{p+q}` of [Stacks, Tag 09VY] inverted.  It is the one place a graded piece
  occurs in the descent, and it is a definition for that reason.

## Main results

* `Stacks.CategoryTheory.Hypercovering.exists_hypercoveringOfTerminal_cechCohomologyEdge_eq`:
  **part (1) of [Stacks, Tag 09VZ] in every degree.**
* `Stacks.CategoryTheory.Hypercovering.exists_hom_gradedPiece_apply_eq_zero`,
  `exists_hom_globalStepToAbutment_succ`, `exists_hom_globalStepToAbutment_succInt` and
  `exists_hom_globalStepToAbutment_eq`: **the abutment filtration descends along a refinement**,
  one step at a time and then all the way to the bottom step.
* `exists_cechCohomologyEdge_apply_eq_globalStepToAbutment_apply`: **the bottom step
  `F^iH^i(𝓕)` is the image of the canonical comparison of [Stacks, Tag 09VY]** on the same
  hypercovering.
* `Stacks.Cohomology.Leray.exists_apply_eq_step_of_exact`,
  `exists_apply_eq_inc_of_exact` and `exists_apply_eq_of_epi_comp`: the three element-level steps
  of the descent, over **bare objects of `AddCommGrpCat`**.  That is what makes them usable: see
  the implementation notes.

* `Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo.stepToAbutment_comp_of_abutmentIso_comp`:
  **a cocone criterion for the inclusion of a filtration step into the abutment.**  Two functorial
  first-quadrant abutments with the same asserted abutment and a morphism of the filtered
  abutments compatible with the two abutment identifications give a cocone identity for the
  inclusions.  Unlike `stepToAbutment_naturality` the morphism need not come from a morphism of
  the parameter category, which is what makes the criterion applicable to a refinement of
  hypercoverings; it is the analogue for a filtration step of `bottomRowEdge_comp_of_cocone`.
* `Stacks.CategoryTheory.Hypercovering.globalGradedIso_naturality`: **the identification
  `E_∞^{p,q} ≅ gr^pH^{p+q}` of [Stacks, Tag 09VY] is compatible with a refinement of the
  hypercovering**, at every bidegree.  This is where the degeneration of
  `GlobalDegeneration.lean` meets the filtration.
* `Stacks.CategoryTheory.Hypercovering.globalFilteredMap_hom_comp_abutmentIso`: **the
  identification of the abutment of [Stacks, Tag 09VX] with the sections over the final presheaf
  is compatible with a refinement of the hypercovering**, at an arbitrary total degree.
* `Stacks.CategoryTheory.Hypercovering.globalCohomologyAbutmentIso_hom_app_eq`: the passage from
  the sections over the final presheaf to global cohomology does not move with the hypercovering.
* `Stacks.CategoryTheory.Hypercovering.globalFilteredMap_natTrans_comp_globalStepToAbutment`:
  **the inclusion `F^jH^n(𝓕) ⟶ H^n(𝓕)` is compatible with a refinement of the hypercovering**, at
  every step and in every total degree.  There is no map on the target: global cohomology mentions
  no hypercovering, so the two sides are plain equalities of cohomology classes.
* `Stacks.CategoryTheory.Hypercovering.globalStep_comp_globalStepToAbutment` and
  `isIso_globalStepToAbutment_zero`: **consecutive steps have the same inclusion into
  `H^n(𝓕)`, and the zeroth step is the whole of it.**  These three are the descent's hypotheses on
  the filtration.
* `Stacks.CategoryTheory.Hypercovering.cechCohomologyToPageTwoZero_comp_bottomRowEdge_comp` and
  `cechCohomologyToPageTwoZero_comp_globalBottomRowEdge`: the canonical comparison of
  [Stacks, Tag 09VY] is `cechCohomologyToPageTwoZero` followed by the bottom-row edge map of the
  abutment.  With `epi_cechCohomologyToPageTwoZero` this is the factorisation through which the
  bottom step `F^iH^i(𝓕)` is the image of the comparison.

## Implementation notes

Every statement in this file is governed by a single cost, the definitional identification of two
spellings of the filtered abutment, and the file is arranged around **where** such an
identification is affordable.  The whole descent fits in the elaborator only because each
element-level step is taken over bare objects of `AddCommGrpCat`, with the identifications paid
in identities of *morphisms* beforehand.

The filtered abutment `F^•H^n(𝓕)` of a hypercovering of the final presheaf has three
definitionally equal spellings: `((globalAbutment J K).filtration n).obj F`, which is the one the
generic abutment API presents it in; `(hypercoverPresheafFiltrationFunctor J ⊤ K n).obj F`, which
is the one `hypercoverPresheafGradedIso` presents the graded pieces in and which `globalFiltered`
is written as; and the induced filtered object of the filtered total complex, which is the one
`CochainComplex.Filtered.inducedFilteredObjectMap` gives the refinement map in.

Such an identification is affordable at a *filtered object* and at
a *step* of its filtration: `((globalAbutment J K).filtration n).obj F` against
`globalFiltered J F K n`, and `.filtration.obj (op j)` of either, are compared argumentwise and
cost nothing, which is why `globalStepToAbutment` can be a definition with its source written in
the `globalFiltered` spelling and its body in the `globalAbutment` one.  It is **not** affordable
underneath a projection that reduces:

* at the *underlying object* of the filtered abutment, which is what
  `CategoryTheory.FilteredObject.forget` and the underlying morphism `FilteredObject.Hom.hom`
  present.  Both spellings reduce there to a homology group of the filtered total complex, and the
  comparison becomes one of two homology constructions with their colimit data.  That is why the
  abutment identification of [Stacks, Tag 09VY] is split off *before* its component at the
  coefficient sheaf is taken: `globalAbutment_abutmentIso_hom` is an identity of natural
  transformations and is `rfl`, while the same identity at `F` does not finish inside the
  heartbeats, and rewriting with the former inside the natural transformation is what carries
  `globalFilteredMap_natTrans_comp_globalStepToAbutment` through;
* at a *graded piece*: `CategoryTheory.FilteredObject.gr p` is a cokernel, so writing an element
  of `gr^pH^{p+q}(𝓕)`, or the zero of that group, forces the cokernel and its colimit data.  That
  is why the one-step descent is **not** the obvious composite of
  `exists_hom_pageInfinity_apply_eq_zero` with
  `Stacks.Cohomology.Leray.exists_step_apply_eq_natTrans_app_apply`: that arrangement must write
  the class in the graded piece, either as the transported element, as the argument of
  `FilteredObject.grMapπ`, or as the hypothesis of a lemma split off for it, and each of those
  exhausts the budget.  Here the class is never written.  The vanishing is carried at the
  *infinity page* -- `exists_hom_gradedPiece_apply_eq_zero` -- the comparison of the two sides is
  an identity of morphisms -- `globalFilteredMap_natTrans_comp_grMapπ` -- and the two are joined
  by `Stacks.Cohomology.Leray.exists_apply_eq_inc_of_exact`, whose objects are all variables, so
  nothing in its proof mentions a cokernel.  The only place the zero of a graded piece is named is
  `exists_step_apply_eq_of_grMapπ_apply_eq_zero`, which is a declaration of its own for that
  reason and is consumed without being applied.

Two further measurements of the same kind decide the shape of the rest.

*A composite that two declarations must agree on has to be a named constant.*
`globalGradedToPageInfinity` is a definition, not an inline composite: when the composite is
written out in two statements, the instance paths through `HasCokernels AddCommGrpCat` are
resolved afresh in each, and comparing the two resolutions unfolds the cokernel -- more than a
heartbeat budget by itself, which is what defeats the otherwise obvious one-declaration proof.
For the same reason it is opened with `unfold` and not with a `rfl` lemma restating its body: the
equation `unfold` uses carries the definition's stored body, so nothing is elaborated twice.

*The last rung has to avoid `exists_apply_eq_stepToAbutment_apply` of
`StacksFrontier/CategoryTheory/Sites/Hypercovering/CohomologyAsColimit.lean`.*  Applied to
`globalAbutment` with `cechCohomologyToPageTwoZero` as the epimorphism onto the bottom row that
lemma *elaborates* and the **kernel** then cannot recheck it, because the Čech cohomology group
and the filtration step both appear in it as values of a functor.  What replaces it is
`Stacks.Cohomology.Leray.exists_apply_eq_of_epi_comp`, the same statement over bare objects with
the factorisation carried as a hypothesis, fed
`cechCohomologyToPageTwoZero_comp_globalStepToAbutment`.  That factorisation is proved in term
mode and not by `rw`: rewriting with
`Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo.bottomRowEdge_app_eq` abstracts a
subterm whose elaborated source is the `globalFiltered` spelling of the step while the lemma
presents it in the `globalAbutment` one, and the motive `rw` builds from that is not type-correct.

Above that the descent is routine: the integer-indexed form of the one-step statement, the
descending induction on `k` with the propositional hypothesis `j + k = n` (the one-step statement
is indexed by `(p, q)` with `p + q = n`, which no induction incrementing the index keeps
`rfl`-compatible), and part (1) itself -- quantified over all of `H^i(𝓕)`, which the zeroth step
being the whole abutment (`isIso_globalStepToAbutment_zero`) is what reduces to the bottom step.
No refinement appears in the conclusion of the induction: global cohomology mentions no
hypercovering, so the composite of the refinements is never needed.

`Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo.ofIsoAbutment` is an `abbrev`, which is
what makes the affordable identifications above affordable; making
`hypercoverPresheafAbutment` or `hypercoverPresheafFunctorialAbutment` reducible as well was tried
and is actively harmful, a reducible structure instance being unfolded eagerly wherever one of its
fields is projected.

The size hypotheses carried are those of `GlobalDegeneration.lean`: sheafification, enough
injectives and `HasExt` at the coefficient universe.  Everything up to and including the
factorisation of the canonical comparison is at a free hypercovering universe `w`, [Stacks, Tag
01GJ] playing no part in it; the descent of section `Descent` carries
`WEqualsLocallyBijective` and `Precoverage.IsStableUnderComposition` and lives at `max u v w`,
which is what Tag 01GJ forces on the degeneration it rests on.

## References

* [Stacks Project, Tag 09VZ](https://stacks.math.columbia.edu/tag/09VZ)
* [Stacks Project, Tag 09VY](https://stacks.math.columbia.edu/tag/09VY)
* [Stacks Project, Tag 09VX](https://stacks.math.columbia.edu/tag/09VX)
* [Stacks Project, Tag 01H0](https://stacks.math.columbia.edu/tag/01H0)
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

/-! ### Transporting a functorial abutment along an isomorphism of the abutment -/

namespace Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo

variable {D A : Type*} [Category* D] [Category* A] [Abelian A]
  {E₁ E₂ : D ⥤ E₂CohomologicalSpectralSequenceNat A} {H : ℕ → D ⥤ A}

/-- **The inclusion of a filtration step into the abutment is compatible with a morphism of the
filtered abutments of two spectral sequences with the same asserted abutment.**  Unlike
`stepToAbutment_naturality` the morphism need not come from a morphism of the parameter category,
which is what makes the statement applicable to a refinement of hypercoverings; what replaces
naturality is the hypothesis `hab`, that the morphism is compatible with the two abutment
identifications.  It is the analogue, for a filtration step, of `bottomRowEdge_comp_of_cocone`. -/
lemma stepToAbutment_comp_of_abutmentIso_comp
    (h₁ : FunctorialFirstQuadrantAbutsTo E₁ H) (h₂ : FunctorialFirstQuadrantAbutsTo E₂ H)
    (n : ℕ) (j : ℤ) (X : D) (θ : (h₁.filtration n).obj X ⟶ (h₂.filtration n).obj X)
    (hab : θ.hom ≫ (h₂.abutmentIso n).hom.app X = (h₁.abutmentIso n).hom.app X) :
    θ.natTrans.app (op j) ≫ (h₂.stepToAbutment n j).app X =
      (h₁.stepToAbutment n j).app X := by
  rw [h₂.stepToAbutment_app, h₁.stepToAbutment_app, ← Category.assoc,
    FilteredObject.Hom.comm θ (op j), Category.assoc, hab]

end Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo

/-! ### The two descent steps over bare objects of `AddCommGrpCat` -/

universe t

namespace Stacks.Cohomology.Leray

/-- **An element of a filtration step whose class in the graded piece is killed by a morphism
comes, after that morphism, from the next step** -- stated over bare objects of
`AddCommGrpCat`, with the short exactness of `0 → B' → B → G → 0` carried as the hypothesis
`hex` and the vanishing carried at the source of the last factor `u` of the comparison.

Every object here is a variable, which is the point: at the place this is used `G` is a graded
piece `gr^pH^n(𝓕)` of the abutment filtration of a hypercovering -- a cokernel -- and *no*
element of it is written anywhere, neither as the transported class nor as the argument of
`CategoryTheory.FilteredObject.grMapπ`.  The hypothesis `hcomm` is an identity of morphisms, and
`hη` is a vanishing at the source `Q` of `u`, which at the point of use is a term of the infinity
page of the spectral sequence and not a cokernel.  Compare
`exists_step_apply_eq_natTrans_app_apply`, which is the same statement with the class in the
graded piece written out; that spelling does not elaborate at the abutment filtration of a
hypercovering of the final presheaf. -/
lemma exists_apply_eq_step_of_exact {A B B' P Q G : AddCommGrpCat.{t}}
    {s : B' ⟶ B} {π : B ⟶ G} {m : A ⟶ B} {c : A ⟶ P} {e : P ⟶ Q} {u : Q ⟶ G}
    (hex : ∀ (y : ToType B) (_ : ConcreteCategory.hom π y = 0),
      ∃ y' : ToType B', ConcreteCategory.hom s y' = y)
    (hcomm : m ≫ π = (c ≫ e) ≫ u) {η : ToType A}
    (hη : ConcreteCategory.hom (c ≫ e) η = 0) :
    ∃ η' : ToType B', ConcreteCategory.hom s η' = ConcreteCategory.hom m η := by
  refine hex _ ?_
  rw [← ConcreteCategory.comp_apply, hcomm, ConcreteCategory.comp_apply, hη, map_zero]

/-- `exists_apply_eq_step_of_exact` followed by the two triangles that send a filtration step into
a common target: the step `B' ⟶ B` and the morphism `m : A ⟶ B` both commute with maps `incB'`,
`incB`, `incA` into `T`, so the element of `B'` produced there has the same image in `T` as `η`.

Stated over bare objects of `AddCommGrpCat` for the reason given at
`exists_apply_eq_step_of_exact`, and merged with it so that at the point of use neither a
filtration step nor the morphism a refinement induces on one occurs in the *statement* of the
one-step descent -- only `incA`, `incB'` and the element they are read on.  At the abutment
filtration of a hypercovering of the final presheaf, `T` is global cohomology and the three maps
into it are the inclusions of filtration steps, which mention no hypercovering. -/
lemma exists_apply_eq_inc_of_exact {A B B' P Q G T : AddCommGrpCat.{t}}
    {s : B' ⟶ B} {π : B ⟶ G} {m : A ⟶ B} {c : A ⟶ P} {e : P ⟶ Q} {u : Q ⟶ G}
    {incB : B ⟶ T} {incB' : B' ⟶ T} {incA : A ⟶ T}
    (hex : ∀ (y : ToType B) (_ : ConcreteCategory.hom π y = 0),
      ∃ y' : ToType B', ConcreteCategory.hom s y' = y)
    (hcomm : m ≫ π = (c ≫ e) ≫ u) (hstep : s ≫ incB = incB') (hmap : m ≫ incB = incA)
    {η : ToType A} (hη : ConcreteCategory.hom (c ≫ e) η = 0) :
    ∃ η' : ToType B', ConcreteCategory.hom incB' η' = ConcreteCategory.hom incA η := by
  obtain ⟨η', hη'⟩ := exists_apply_eq_step_of_exact hex hcomm hη
  refine ⟨η', ?_⟩
  rw [← hstep, ← hmap, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hη']

/-- **An epimorphism followed by an epimorphism followed by anything hits every element of the
image of that last factor** -- stated over bare objects of `AddCommGrpCat`, with the composite
`k` carried so that no factorisation has to be rewritten on an element.

This is `exists_apply_eq_stepToAbutment_apply` with the spectral sequence removed from the
statement: there the source of `e` is a Čech cohomology group, `S` is a filtration step of the
abutment and `T` the abutment, each a value of a functor, and the application at the abutment of
[Stacks, Tag 09VY] elaborates but cannot be rechecked by the kernel.  Here all four objects are
variables, and the two epimorphisms and the factorisation are supplied as hypotheses proved at
the level of morphisms. -/
lemma exists_apply_eq_of_epi_comp {A B S T : AddCommGrpCat.{t}} {e : A ⟶ B} {g : B ⟶ S}
    {inc : S ⟶ T} {k : A ⟶ T} (he : Epi e) (hg : Epi g) (hk : e ≫ g ≫ inc = k)
    (η : ToType S) :
    ∃ c : ToType A, ConcreteCategory.hom k c = ConcreteCategory.hom inc η := by
  obtain ⟨c, hc⟩ := (AddCommGrpCat.epi_iff_surjective (e ≫ g)).1 (epi_comp' he hg) η
  refine ⟨c, ?_⟩
  rw [← hk, ← Category.assoc, ConcreteCategory.comp_apply, hc]

end Stacks.Cohomology.Leray

namespace Stacks.CategoryTheory.Hypercovering

open Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
  [HasEqualizers C] [HasBinaryProducts C] (J : Pretopology C)
  [HasSheafify J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)}]
  [EnoughInjectives (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)})]
  [HasExt.{max (max u v) (max v w)}
    (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)})]
  (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)})

/-! ### The abutment filtration as a `Rel`-shaped family -/

/-- **The abutment of [Stacks, Tag 09VY] with the filtration a hypercovering of the final presheaf
puts on it**: the cohomology of the filtered total complex of [Stacks, Tag 09VX], with its induced
filtration.  Its underlying group does not move with the hypercovering; the filtration does.

The spelling is the one `hypercoverPresheafGradedIso` presents the graded pieces in, which is what
makes `FilteredObject.gr` -- a cokernel, hence data computed from the object -- agree on the nose
below. -/
abbrev globalFiltered (K : HypercoveringOfTerminal.{w} J) (n : ℕ) :=
  (hypercoverPresheafFiltrationFunctor J (⊤_ (Cᵒᵖ ⥤ Type v)) K (n : ℤ)).obj F

/-- **The morphism of filtered abutments a refinement of hypercoverings of the final presheaf
induces**: `CochainComplex.Filtered.inducedFilteredObjectMap` of the Čech pullback on the filtered
total complexes, `HypercoveringOf.Hom.filteredMap`.  It is the morphism `θ` of
`Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo.bottomRowEdge_comp_of_cocone`.

Its source and target are written through `globalFiltered`, which is the single place the two
spellings of the filtered abutment are identified. -/
abbrev globalFilteredMap {K L : HypercoveringOfTerminal.{w} J} (ψ : L.Hom K) (n : ℕ) :
    globalFiltered.{w} J F K n ⟶ globalFiltered.{w} J F L n :=
  CochainComplex.Filtered.inducedFilteredObjectMap
    (ψ.filteredMap J (⊤_ (Cᵒᵖ ⥤ Type v)) F) (n : ℤ)

omit [HasBinaryProducts C] [HasExt.{max (max u v) (max v w)}
    (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)})] in
/-- **The identification `E_∞^{p,q} ≅ gr^pH^{p+q}` of [Stacks, Tag 09VY] is compatible with a
refinement of the hypercovering**, at every bidegree:
`HypercoveringOf.Hom.hypercoverPresheafGradedIso_naturality` read at the final presheaf and the
coefficient sheaf.  This is the hypothesis `hgr` of
`Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo.bottomRowEdge_comp_of_cocone` off the
bottom row, which is where the degeneration meets the filtration. -/
lemma globalGradedIso_naturality {K L : HypercoveringOfTerminal.{w} J} (ψ : L.Hom K) (p q : ℕ) :
    CategoryTheory.SpectralSequence.Hom.mapPageInfinity
          (globalSpectralSequenceAtMap.{w} J F ψ) (p, q) ≫
        (hypercoverPresheafGradedIso J (⊤_ (Cᵒᵖ ⥤ Type v)) L F p q).hom =
      (hypercoverPresheafGradedIso J (⊤_ (Cᵒᵖ ⥤ Type v)) K F p q).hom ≫
        (FilteredObject.gr (p : ℤ)).map (globalFilteredMap.{w} J F ψ (p + q)) :=
  ψ.hypercoverPresheafGradedIso_naturality J (⊤_ (Cᵒᵖ ⥤ Type v)) F p q

omit [HasBinaryProducts C] [HasExt.{max (max u v) (max v w)}
    (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)})] in
/-- **The identification of the abutment of [Stacks, Tag 09VX] with the sections over the final
presheaf is compatible with a refinement of the hypercovering**: this is the hypothesis `hab` of
`Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo.bottomRowEdge_comp_of_cocone`, at an
arbitrary total degree, and it is
`HypercoveringOf.Hom.homologyMap_filteredMap_comp_abutmentIso`. -/
lemma globalFilteredMap_hom_comp_abutmentIso {K L : HypercoveringOfTerminal.{w} J}
    (ψ : L.Hom K) (n : ℕ) :
    (globalFilteredMap.{w} J F ψ n).hom ≫
        ((hypercoverPresheafAbutment J (⊤_ (Cᵒᵖ ⥤ Type v)) L).abutmentIso n).hom.app F =
      ((hypercoverPresheafAbutment J (⊤_ (Cᵒᵖ ⥤ Type v)) K).abutmentIso n).hom.app F := by
  rw [hypercoverPresheafAbutment_abutmentIso_hom_app,
    hypercoverPresheafAbutment_abutmentIso_hom_app, Category.id_comp, Category.id_comp]
  exact ψ.homologyMap_filteredMap_comp_abutmentIso J (⊤_ (Cᵒᵖ ⥤ Type v)) n F

omit [HasBinaryProducts C] in
/-- **The passage from the sections over the final presheaf to global cohomology does not move
with the hypercovering**, read at the coefficient sheaf: `globalCohomologyAbutmentIso_eq`. -/
lemma globalCohomologyAbutmentIso_hom_app_eq (K L : HypercoveringOfTerminal.{w} J) (n : ℕ) :
    (globalCohomologyAbutmentIso J L n).hom.app F =
      (globalCohomologyAbutmentIso J K n).hom.app F :=
  congrArg (fun t ↦ NatTrans.app t F)
    (congrArg Iso.hom (globalCohomologyAbutmentIso_eq J K L n))

/-- **The inclusion `F^jH^n(𝓕) ⟶ H^n(𝓕)` of a step of the abutment filtration carried by a
hypercovering of the final presheaf into global cohomology**: the inclusion of that step into the
abutment of [Stacks, Tag 09VY], whose asserted abutment is global cohomology.

Its target is `(globalCohomologyFunctor J n).obj F`, which mentions no hypercovering; that is what
makes a descent through the filtration produce plain equalities of cohomology classes, with no
comparison of two spellings of the abutment at each step.  Its source is written in the
`globalFiltered` spelling, the one the refinement map and the graded identification of
[Stacks, Tag 09VY] live in, so the identification of that spelling with the one the generic
abutment API presents the filtration in is paid here once -- the device
`cechCohomologyToPageTwoZero` of `GlobalDegeneration.lean` uses for the two spellings of a Čech
cohomology group. -/
def globalStepToAbutment (K : HypercoveringOfTerminal.{w} J) (n : ℕ) (j : ℤ) :
    (globalFiltered.{w} J F K n).filtration.obj (op j) ⟶
      (globalCohomologyFunctor.{w} J n).obj F :=
  ((globalAbutment J K).stepToAbutment n j).app F

omit [HasBinaryProducts C] in
/-- `globalStepToAbutment` is the inclusion of the filtration step into the abutment of
[Stacks, Tag 09VY], the two spellings of the step being definitionally equal. -/
lemma globalStepToAbutment_eq (K : HypercoveringOfTerminal.{w} J) (n : ℕ) (j : ℤ) :
    globalStepToAbutment.{w} J F K n j = ((globalAbutment J K).stepToAbutment n j).app F :=
  rfl

omit [HasBinaryProducts C] in
/-- **The abutment identification of [Stacks, Tag 09VY] is the identification of
[Stacks, Tag 09VX] followed by the passage to global cohomology**, as an identity of natural
transformations: the abutment of the former is the abutment of the latter with global cohomology
substituted for the sections over the final presheaf.

It is stated between natural transformations and not at the coefficient sheaf on purpose.  Taking
the component at `F` first forces the value of the filtration functor at `F`, hence the underlying
object of the filtered abutment -- a homology group of the filtered total complex -- and a
definitional comparison of the two spellings there reduces both projections and compares the two
homology constructions, which does not finish inside the heartbeats.  Between natural
transformations the two filtrations are compared as functors, argumentwise, and the comparison is
immediate. -/
lemma globalAbutment_abutmentIso_hom (K : HypercoveringOfTerminal.{w} J) (n : ℕ) :
    ((globalAbutment J K).abutmentIso n).hom =
      ((hypercoverPresheafAbutment J (⊤_ (Cᵒᵖ ⥤ Type v)) K).abutmentIso n).hom ≫
        (globalCohomologyAbutmentIso J K n).hom :=
  rfl

omit [HasBinaryProducts C] in
/-- **The inclusion of a step of the abutment filtration into global cohomology is compatible with
a refinement of the hypercovering**: the map a refinement induces on the step followed by the
inclusion carried by the refinement is the inclusion carried by the original hypercovering.  There
is no map on the target, global cohomology mentioning no hypercovering.

This is `stepToAbutment_comp_of_abutmentIso_comp` for the two abutments of [Stacks, Tag 09VY].
Its hypothesis `hab` is reached by splitting the abutment identification with
`globalAbutment_abutmentIso_hom`, which is done by rewriting *inside* the natural transformation,
before its component at the coefficient sheaf is taken; the two ingredients are then
`globalFilteredMap_hom_comp_abutmentIso` -- the identification of [Stacks, Tag 09VX] moves with
the hypercovering -- and `globalCohomologyAbutmentIso_hom_app_eq` -- the passage to global
cohomology does not. -/
lemma globalFilteredMap_natTrans_comp_globalStepToAbutment
    {K L : HypercoveringOfTerminal.{w} J} (ψ : L.Hom K) (n : ℕ) (j : ℤ) :
    (globalFilteredMap.{w} J F ψ n).natTrans.app (op j) ≫
        globalStepToAbutment.{w} J F L n j =
      globalStepToAbutment.{w} J F K n j := by
  refine stepToAbutment_comp_of_abutmentIso_comp (globalAbutment J K) (globalAbutment J L)
    n j F (globalFilteredMap.{w} J F ψ n) ?_
  rw [globalAbutment_abutmentIso_hom J L n, globalAbutment_abutmentIso_hom J K n,
    NatTrans.comp_app, NatTrans.comp_app]
  exact (Category.assoc _ _ _).symm.trans
    ((globalFilteredMap_hom_comp_abutmentIso.{w} J F ψ n =≫
        (globalCohomologyAbutmentIso J L n).hom.app F).trans
      (((hypercoverPresheafAbutment J (⊤_ (Cᵒᵖ ⥤ Type v)) K).abutmentIso n).hom.app F ≫=
        globalCohomologyAbutmentIso_hom_app_eq.{w} J F K L n))

omit [HasBinaryProducts C] in
/-- **Passing from the `(j+1)`-st step of the abutment filtration of a hypercovering of the final
presheaf to the `j`-th does not change the inclusion into global cohomology.** -/
lemma globalStep_comp_globalStepToAbutment (K : HypercoveringOfTerminal.{w} J) (n : ℕ) (j : ℤ) :
    (globalFiltered.{w} J F K n).filtration.step (FilteredObject.succHom j) ≫
        globalStepToAbutment.{w} J F K n j = globalStepToAbutment.{w} J F K n (j + 1) :=
  (globalAbutment J K).step_comp_stepToAbutment n j F

omit [HasBinaryProducts C] in
/-- **The zeroth step of the abutment filtration is the whole of global cohomology**: its
inclusion is an isomorphism, the zeroth step being the top one. -/
lemma isIso_globalStepToAbutment_zero (K : HypercoveringOfTerminal.{w} J) (n : ℕ) :
    IsIso (globalStepToAbutment.{w} J F K n 0) :=
  (globalAbutment J K).isIso_stepToAbutment_zero n F

/-! ### The canonical comparison factored through the abutment of [Stacks, Tag 09VX] -/

omit [HasBinaryProducts C] in
/-- **The canonical comparison of [Stacks, Tag 09VY], factored through the abutment of
[Stacks, Tag 09VX]**: `cechCohomologyToPageTwoZero` followed by the bottom-row edge map of the
abutment of [Stacks, Tag 09VX] and then by the passage to global cohomology.  This is
`cechToPageTwoZero_comp_bottomRowEdge` with the source written as the Čech cohomology group and
the target of the edge map unfolded by `globalBottomRowEdge_app`. -/
lemma cechCohomologyToPageTwoZero_comp_bottomRowEdge_comp (K : HypercoveringOfTerminal.{w} J)
    (i : ℕ) :
    (cechCohomologyToPageTwoZero.{w} J F K i ≫
        ((hypercoverPresheafAbutment J (⊤_ (Cᵒᵖ ⥤ Type v)) K).bottomRowEdge i).app F) ≫
      (globalCohomologyAbutmentIso J K i).hom.app F = cechCohomologyEdge.{w} J K i F :=
  (Category.assoc _ _ _).trans
    ((_ ≫= (globalBottomRowEdge_app J K i F).symm).trans
      (cechToPageTwoZero_comp_bottomRowEdge.{w} J F K i))

/-! ### The bottom step of the filtration is the image of the canonical comparison -/

omit [HasBinaryProducts C] in
/-- **The canonical comparison of [Stacks, Tag 09VY] is `cechCohomologyToPageTwoZero` followed by
the bottom-row edge map of the abutment of [Stacks, Tag 09VY]**: that edge map is the one of
[Stacks, Tag 09VX] followed by the passage to global cohomology
(`globalBottomRowEdge_app`), and reassociating gives
`cechCohomologyToPageTwoZero_comp_bottomRowEdge_comp`. -/
lemma cechCohomologyToPageTwoZero_comp_globalBottomRowEdge (K : HypercoveringOfTerminal.{w} J)
    (i : ℕ) :
    cechCohomologyToPageTwoZero.{w} J F K i ≫ ((globalAbutment J K).bottomRowEdge i).app F =
      cechCohomologyEdge.{w} J K i F :=
  ((cechCohomologyToPageTwoZero.{w} J F K i ≫= globalBottomRowEdge_app J K i F).trans
      (Category.assoc _ _ _).symm).trans
    (cechCohomologyToPageTwoZero_comp_bottomRowEdge_comp.{w} J F K i)

omit [HasBinaryProducts C] [HasExt (Sheaf J.toGrothendieck AddCommGrpCat)] in
/-- `cechCohomologyToPageTwoZero` is an isomorphism, being `cechToPageTwoZero`.  The two spellings
of its source are identified here, once, exactly as `mono_cechCohomologyToPageTwoZero` does. -/
lemma isIso_cechCohomologyToPageTwoZero (K : HypercoveringOfTerminal.{w} J) (i : ℕ) :
    IsIso (cechCohomologyToPageTwoZero.{w} J F K i) :=
  isIso_cechToPageTwoZero.{w} J F K i

omit [HasBinaryProducts C] [HasExt (Sheaf J.toGrothendieck AddCommGrpCat)] in
/-- `cechCohomologyToPageTwoZero` is an epimorphism, being an isomorphism. -/
lemma epi_cechCohomologyToPageTwoZero (K : HypercoveringOfTerminal.{w} J) (i : ℕ) :
    Epi (cechCohomologyToPageTwoZero.{w} J F K i) :=
  have := isIso_cechCohomologyToPageTwoZero.{w} J F K i
  IsIso.epi_of_iso _

omit [HasBinaryProducts C] in
/-- **The canonical comparison of [Stacks, Tag 09VY] is `cechCohomologyToPageTwoZero`, followed
by an epimorphism onto the bottom step `F^iH^i(𝓕)` of the abutment filtration, followed by the
inclusion of that step into global cohomology**: this is
`cechCohomologyToPageTwoZero_comp_globalBottomRowEdge` with the bottom-row edge map split by
`Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo.bottomRowEdge_app_eq`, and with the
inclusion written as `globalStepToAbutment`. -/
lemma cechCohomologyToPageTwoZero_comp_globalStepToAbutment
    (K : HypercoveringOfTerminal.{w} J) (i : ℕ) :
    cechCohomologyToPageTwoZero.{w} J F K i ≫
        (((globalAbutment J K).bottomRowGrHom i).app F ≫
            ((globalAbutment J K).grIsoEval i).hom.app F) ≫
          globalStepToAbutment.{w} J F K i (i : ℤ) =
      cechCohomologyEdge.{w} J K i F :=
  (cechCohomologyToPageTwoZero.{w} J F K i ≫=
      ((globalAbutment J K).bottomRowEdge_app_eq i F).symm).trans
    (cechCohomologyToPageTwoZero_comp_globalBottomRowEdge.{w} J F K i)

omit [HasBinaryProducts C] in
/-- **Every cohomology class in the bottom step `F^iH^i(𝓕)` of the abutment filtration carried by
a hypercovering of the final presheaf is the image of a Čech class under the canonical comparison
of [Stacks, Tag 09VY]**, in the same degree and on the same hypercovering.

This is the last rung of part (1): the comparison is `cechCohomologyToPageTwoZero` -- an
isomorphism, hence an epimorphism -- followed by the epimorphism `E₂^{i,0} ⟶ F^iH^i(𝓕)` of
`epi_bottomRowGrHom_comp_grIsoEval_hom_app` and then by the inclusion of the step, which is
`cechCohomologyToPageTwoZero_comp_globalStepToAbutment`.  The element-level step is taken by
`Stacks.Cohomology.Leray.exists_apply_eq_of_epi_comp`, over bare objects of `AddCommGrpCat`, so
that neither the Čech cohomology group nor the filtration step appears in it as a value of a
functor. -/
theorem exists_cechCohomologyEdge_apply_eq_globalStepToAbutment_apply
    (K : HypercoveringOfTerminal.{w} J) (i : ℕ)
    (η : ToType ((globalFiltered.{w} J F K i).filtration.obj (op (i : ℤ)))) :
    ∃ ξK : cechCohomology J (⊤_ (Cᵒᵖ ⥤ Type v)) K F i,
      ConcreteCategory.hom (cechCohomologyEdge.{w} J K i F) ξK =
        ConcreteCategory.hom (globalStepToAbutment.{w} J F K i (i : ℤ)) η :=
  _root_.Stacks.Cohomology.Leray.exists_apply_eq_of_epi_comp
    (epi_cechCohomologyToPageTwoZero.{w} J F K i)
    ((globalAbutment J K).epi_bottomRowGrHom_comp_grIsoEval_hom_app i F)
    (cechCohomologyToPageTwoZero_comp_globalStepToAbutment.{w} J F K i) η

/-! ### The abutment filtration descends one step along a refinement -/

/-- **The passage from a step of the abutment filtration to the infinity page of the spectral
sequence of [Stacks, Tag 09VY]**: the projection `F^pH^{p+q}(𝓕) ⟶ gr^pH^{p+q}(𝓕)` onto the graded
piece followed by the graded identification `E_∞^{p,q} ≅ gr^pH^{p+q}` inverted.

It is a definition and not an inline composite because it is the one place a graded piece --
a cokernel -- occurs in the descent: every statement below mentions this constant and never the
composite, so the two sides of each application are the *same* term, instances and all.  Written
out inline instead, the instance paths through `HasCokernels AddCommGrpCat` are resolved afresh in
each declaration and comparing two of them unfolds the cokernel's colimit data; that is what
exhausts the elaborator. -/
def globalGradedToPageInfinity (K : HypercoveringOfTerminal.{w} J) (p q : ℕ) :
    (globalFiltered.{w} J F K (p + q)).filtration.obj (op (p : ℤ)) ⟶
      (globalSpectralSequenceAt.{w} J F K).pageInfinity (p, q) :=
  FilteredObject.grMapπ (FilteredObject.succHom (p : ℤ))
      (globalFiltered.{w} J F K (p + q)) ≫
    (hypercoverPresheafGradedIso J (⊤_ (Cᵒᵖ ⥤ Type v)) K F p q).inv

omit [HasBinaryProducts C] [HasExt.{max (max u v) (max v w)}
    (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)})] in
/-- **The projection onto a graded piece of the abutment filtration, followed by the map a
refinement induces on that graded piece, factors through the infinity page of the spectral
sequence**: `globalGradedToPageInfinity`, then the map the refinement induces on the infinity
page, then the graded identification of the refinement.

This is `globalGradedIso_naturality` and the naturality `CategoryTheory.FilteredObject.grMapπ_map`
of the projections, pasted.  It is an identity of *morphisms* -- the whole point: a graded piece
is a cokernel, so an element of one cannot be written at the abutment filtration of a
hypercovering of the final presheaf, and the vanishing that the descent needs is carried instead
at the source of the last factor, which is a term of the infinity page.  It is the hypothesis
`hcomm` of `Stacks.Cohomology.Leray.exists_apply_eq_step_of_exact`.

The proof opens `globalGradedToPageInfinity` with `unfold` and not with a `rfl` lemma restating
its body: the equation `unfold` uses carries the definition's *stored* body, whereas a restatement
is elaborated afresh and comparing the two resolutions of the cokernel instances is by itself more
than a heartbeat budget. -/
lemma globalFilteredMap_natTrans_comp_grMapπ {K L : HypercoveringOfTerminal.{w} J}
    (ψ : L.Hom K) (p q : ℕ) :
    (globalFilteredMap.{w} J F ψ (p + q)).natTrans.app (op (p : ℤ)) ≫
        FilteredObject.grMapπ (FilteredObject.succHom (p : ℤ))
          (globalFiltered.{w} J F L (p + q)) =
      (globalGradedToPageInfinity.{w} J F K p q ≫
          CategoryTheory.SpectralSequence.Hom.mapPageInfinity
            (globalSpectralSequenceAtMap.{w} J F ψ) (p, q)) ≫
        (hypercoverPresheafGradedIso J (⊤_ (Cᵒᵖ ⥤ Type v)) L F p q).hom := by
  unfold globalGradedToPageInfinity
  rw [Category.assoc, Category.assoc, globalGradedIso_naturality, Iso.inv_hom_id_assoc]
  exact (FilteredObject.grMapπ_map (FilteredObject.succHom (p : ℤ))
    (globalFilteredMap.{w} J F ψ (p + q))).symm

omit [HasBinaryProducts C] [HasExt.{max (max u v) (max v w)}
    (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)})] in
/-- **An element of a step of the abutment filtration whose class in the graded piece vanishes
comes from the next step**: the short exactness of `0 → F^{j+1} → F^j → gr^j → 0`
(`CategoryTheory.FilteredObject.stepShortComplex_shortExact`) read on elements, at the abutment
filtration of a hypercovering of the final presheaf.

It is split off as its own declaration because it is the one place where the zero of a graded
piece has to be named, and it is the hypothesis `hex` of
`Stacks.Cohomology.Leray.exists_apply_eq_step_of_exact`, which consumes it without ever applying
it. -/
lemma exists_step_apply_eq_of_grMapπ_apply_eq_zero (L : HypercoveringOfTerminal.{w} J) (n : ℕ)
    (j : ℤ) (y : ToType ((globalFiltered.{w} J F L n).filtration.obj (op j)))
    (hy : ConcreteCategory.hom (FilteredObject.grMapπ (FilteredObject.succHom j)
      (globalFiltered.{w} J F L n)) y = 0) :
    ∃ y' : ToType ((globalFiltered.{w} J F L n).filtration.obj (op (j + 1))),
      ConcreteCategory.hom ((globalFiltered.{w} J F L n).filtration.step
        (FilteredObject.succHom j)) y' = y :=
  (ShortComplex.ab_exact_iff _).1
    (FilteredObject.stepShortComplex_shortExact (FilteredObject.succHom j)
      (globalFiltered.{w} J F L n)).exact y hy

omit [HasBinaryProducts C] in
/-- **The one-step descent of the abutment filtration, with the refinement and the vanishing of
the graded class carried as hypotheses.**  Given a refinement `ψ` and a class `η` in the `p`-th
step `F^pH^{p+q}(𝓕)` whose image in the infinity page of the refinement vanishes, `η` is -- as a
class in global cohomology -- a class in the `(p+1)`-st step of the filtration `ψ` carries.

This is `Stacks.Cohomology.Leray.exists_apply_eq_inc_of_exact` at the abutment filtration, and it
is split off from the choice of refinement (`exists_hom_globalStepToAbutment_succ`) so that
neither declaration exhausts the elaborator's heartbeats: the five hypotheses this one supplies
are all identities of morphisms between values of the filtration functor, and matching them
against the bare-object lemma is by itself most of a heartbeat budget. -/
lemma exists_globalStepToAbutment_succ_apply_eq {K L : HypercoveringOfTerminal.{w} J}
    (ψ : L.Hom K) (p q : ℕ)
    {η : ToType ((globalFiltered.{w} J F K (p + q)).filtration.obj (op (p : ℤ)))}
    (hψ : ConcreteCategory.hom
      (globalGradedToPageInfinity.{w} J F K p q ≫
        CategoryTheory.SpectralSequence.Hom.mapPageInfinity
          (globalSpectralSequenceAtMap.{w} J F ψ) (p, q)) η = 0) :
    ∃ η' : ToType ((globalFiltered.{w} J F L (p + q)).filtration.obj (op ((p : ℤ) + 1))),
      ConcreteCategory.hom (globalStepToAbutment.{w} J F L (p + q) ((p : ℤ) + 1)) η' =
        ConcreteCategory.hom (globalStepToAbutment.{w} J F K (p + q) (p : ℤ)) η :=
  _root_.Stacks.Cohomology.Leray.exists_apply_eq_inc_of_exact
    (exists_step_apply_eq_of_grMapπ_apply_eq_zero.{w} J F L (p + q) (p : ℤ))
    (globalFilteredMap_natTrans_comp_grMapπ.{w} J F ψ p q)
    (globalStep_comp_globalStepToAbutment.{w} J F L (p + q) (p : ℤ))
    (globalFilteredMap_natTrans_comp_globalStepToAbutment.{w} J F ψ (p + q) (p : ℤ))
    hψ

section Descent

variable [J.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{max (max u v) (max v w)}]
  [Precoverage.IsStableUnderComposition J.toPrecoverage]

omit [HasExt.{max (max u v) (max v w)}
    (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)})] in
/-- **For `q > 0` the class of an element of the `p`-th step `F^pH^{p+q}(𝓕)` in the graded piece
`gr^pH^{p+q}(𝓕)` dies after a refinement of the hypercovering.**

The vanishing is stated at the *infinity page* and not at the graded piece: the class is read as
the image of `η` under `globalGradedToPageInfinity`, so that no element and no zero of a graded
piece -- a cokernel, whose colimit data is what exhausts the elaborator here -- occurs in the
statement.  It is `exists_hom_pageInfinity_apply_eq_zero`, the degeneration of
`StacksFrontier/CategoryTheory/Sites/Hypercovering/GlobalDegeneration.lean`, read on that image. -/
theorem exists_hom_gradedPiece_apply_eq_zero (q : ℕ) (hq : 0 < q) (p : ℕ)
    (K : HypercoveringOfTerminal.{max u v w} J)
    (η : ToType ((globalFiltered.{max u v w} J F K (p + q)).filtration.obj (op (p : ℤ)))) :
    ∃ (L : HypercoveringOfTerminal.{max u v w} J) (ψ : L.Hom K),
      ConcreteCategory.hom
        (globalGradedToPageInfinity.{max u v w} J F K p q ≫
          CategoryTheory.SpectralSequence.Hom.mapPageInfinity
            (globalSpectralSequenceAtMap.{max u v w} J F ψ) (p, q)) η = 0 := by
  obtain ⟨L, ψ, hψ⟩ := exists_hom_pageInfinity_apply_eq_zero.{w} J F q hq p K
    (ConcreteCategory.hom (globalGradedToPageInfinity.{max u v w} J F K p q) η)
  exact ⟨L, ψ, (ConcreteCategory.comp_apply _ _ η).trans hψ⟩

/-- **The abutment filtration of a hypercovering of the final presheaf descends one step along a
refinement**, for `q > 0`: a class in the `p`-th step `F^pH^{p+q}(𝓕)` is, after a refinement of
the hypercovering, a class in the `(p+1)`-st step with the same image in global cohomology.

There is no map on the target: global cohomology mentions no hypercovering, so the two sides are
plain equalities of cohomology classes, and neither the filtration step nor the morphism the
refinement induces on it occurs in the statement.

Its two halves are `exists_hom_gradedPiece_apply_eq_zero` -- the class in the graded piece dies
after a refinement, stated at the infinity page -- and
`exists_globalStepToAbutment_succ_apply_eq`, which is where the five identities of morphisms that
the descent rests on are matched against the bare-object lemma. -/
theorem exists_hom_globalStepToAbutment_succ (q : ℕ) (hq : 0 < q) (p : ℕ)
    (K : HypercoveringOfTerminal.{max u v w} J)
    (η : ToType ((globalFiltered.{max u v w} J F K (p + q)).filtration.obj (op (p : ℤ)))) :
    ∃ (L : HypercoveringOfTerminal.{max u v w} J)
      (η' : ToType ((globalFiltered.{max u v w} J F L (p + q)).filtration.obj
        (op ((p : ℤ) + 1)))),
      ConcreteCategory.hom
          (globalStepToAbutment.{max u v w} J F L (p + q) ((p : ℤ) + 1)) η' =
        ConcreteCategory.hom (globalStepToAbutment.{max u v w} J F K (p + q) (p : ℤ)) η := by
  obtain ⟨L, ψ, hψ⟩ := exists_hom_gradedPiece_apply_eq_zero.{w} J F q hq p K η
  exact ⟨L, exists_globalStepToAbutment_succ_apply_eq.{max u v w} J F ψ p q hψ⟩

/-- `exists_hom_globalStepToAbutment_succ` with the filtration step carried by an integer index
strictly below the total degree.  This is the shape the descending induction consumes: the
`p + q` indexing of the one-step statement is not `rfl`-compatible with an induction that
increments `p`, and the integer index keeps the successor step `j + 1` free of casts. -/
theorem exists_hom_globalStepToAbutment_succInt (n : ℕ) (j : ℤ) (hj : 0 ≤ j) (hjn : j < n)
    (K : HypercoveringOfTerminal.{max u v w} J)
    (η : ToType ((globalFiltered.{max u v w} J F K n).filtration.obj (op j))) :
    ∃ (L : HypercoveringOfTerminal.{max u v w} J)
      (η' : ToType ((globalFiltered.{max u v w} J F L n).filtration.obj (op (j + 1)))),
      ConcreteCategory.hom (globalStepToAbutment.{max u v w} J F L n (j + 1)) η' =
        ConcreteCategory.hom (globalStepToAbutment.{max u v w} J F K n j) η := by
  obtain ⟨p, rfl⟩ : ∃ p : ℕ, j = (p : ℤ) := ⟨j.toNat, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, n = p + q := ⟨n - p, by omega⟩
  exact exists_hom_globalStepToAbutment_succ.{w} J F q (by omega) p K η

/-- **Every cohomology class in a step `F^jH^n(𝓕)` of the abutment filtration of a hypercovering
of the final presheaf is, after a refinement of the hypercovering, a class in the bottom step
`F^nH^n(𝓕)`**: the filtration is descended one step at a time by
`exists_hom_globalStepToAbutment_succInt`, `k` times from the step `j` with `j + k = n`.

The induction is on `k` with the *propositional* hypothesis `j + k = n`, not on the index `j`:
the one-step statement is indexed by the pair `(p, q)` with `p + q = n`, which no induction
incrementing the index can keep `rfl`-compatible.  There is no map on the target and no
refinement in the conclusion: global cohomology mentions no hypercovering, so the composite of
the refinements is not needed and the two sides are plain equalities of cohomology classes. -/
theorem exists_hom_globalStepToAbutment_eq (n k : ℕ) :
    ∀ (j : ℤ) (_ : 0 ≤ j) (_ : j + k = n) (K : HypercoveringOfTerminal.{max u v w} J)
      (η : ToType ((globalFiltered.{max u v w} J F K n).filtration.obj (op j))),
      ∃ (L : HypercoveringOfTerminal.{max u v w} J)
        (η' : ToType ((globalFiltered.{max u v w} J F L n).filtration.obj (op (n : ℤ)))),
        ConcreteCategory.hom (globalStepToAbutment.{max u v w} J F L n (n : ℤ)) η' =
          ConcreteCategory.hom (globalStepToAbutment.{max u v w} J F K n j) η := by
  induction k with
  | zero =>
    intro j _ hjn K η
    obtain rfl : j = (n : ℤ) := by omega
    exact ⟨K, η, rfl⟩
  | succ k ih =>
    intro j hj hjn K η
    obtain ⟨L₁, η₁, hη₁⟩ :=
      exists_hom_globalStepToAbutment_succInt.{w} J F n j hj (by omega) K η
    obtain ⟨L₂, η', hη'⟩ := ih (j + 1) (by omega) (by omega) L₁ η₁
    exact ⟨L₂, η', hη'.trans hη₁⟩

/-- **Stacks Project, Tag 09VZ, part (1), in every degree.**  Every cohomology class of an abelian
sheaf is the image, under the canonical comparison `Ȟ^i(K, 𝓕) ⟶ H^i(𝓕)` of [Stacks, Tag 09VY], of
a Čech class on some hypercovering `K` of the final presheaf.

The coefficients are the sheaf `𝓕` itself, not its degree-zero cohomology presheaf.  A
hypercovering exists by [Stacks, Tag 0DAX] applied to the identity coverings; the zeroth step of
the abutment filtration is the whole of `H^i(𝓕)` (`isIso_globalStepToAbutment_zero`), the class
descends from there to the bottom step `F^iH^i(𝓕)` after a refinement
(`exists_hom_globalStepToAbutment_eq`, whose engine is the degeneration of
`StacksFrontier/CategoryTheory/Sites/Hypercovering/GlobalDegeneration.lean`), and the bottom step is
the image of `Ȟ^i(L, 𝓕)` under the comparison
(`exists_cechCohomologyEdge_apply_eq_globalStepToAbutment_apply`). -/
@[stacks 09VZ "part (1) in every degree, at the hypercovering universe `max u v w`, which is \
what Tag 01GJ forces; the canonical map is the bottom-row edge map of the spectral sequence of \
Tag 09VY, i.e. the comparison of Tag 01GY.  The size binders are those the chapter's \
presheaf-side tags carry -- sheafification, enough injectives and `HasExt` at the coefficient \
universe -- together with `WEqualsLocallyBijective`, a theorem for every essentially small \
site, which is carried here because the degeneration of the spectral sequence rests on Tag \
01GJ.  See `exists_hypercoveringOfTerminal_cechCohomologyEdge_zero_eq` for degree zero at a \
free universe `w`", sga "4 V 7.4.1" "Clause 2)"]
theorem exists_hypercoveringOfTerminal_cechCohomologyEdge_eq (i : ℕ)
    (ξ : (globalCohomologyFunctor.{max u v w} J i).obj F) :
    ∃ (K : HypercoveringOfTerminal.{max u v w} J)
      (ξK : cechCohomology J (⊤_ (Cᵒᵖ ⥤ Type v)) K F i),
      ConcreteCategory.hom (cechCohomologyEdge.{max u v w} J K i F) ξK = ξ := by
  obtain ⟨K, -⟩ :=
    exists_hypercoveringOfTerminal_with_objects_in.{max u v w} J Set.univ fun U ↦
      ⟨PUnit.{max u v w + 1}, fun _ ↦ U, fun _ ↦ 𝟙 U, fun _ ↦ Set.mem_univ _,
        mem_coverings_ofArrows_id J U⟩
  have hiso := isIso_globalStepToAbutment_zero.{max u v w} J F K i
  have hx : ConcreteCategory.hom (globalStepToAbutment.{max u v w} J F K i 0)
      (ConcreteCategory.hom (inv (globalStepToAbutment.{max u v w} J F K i 0)) ξ) = ξ :=
    (_root_.Stacks.Cohomology.Leray.apply_apply_eq_of_comp_eq (IsIso.inv_hom_id _) ξ).trans
      (ConcreteCategory.id_apply ξ)
  obtain ⟨L, η', hη'⟩ := exists_hom_globalStepToAbutment_eq.{w} J F i i 0 le_rfl (by omega) K
    (ConcreteCategory.hom (inv (globalStepToAbutment.{max u v w} J F K i 0)) ξ)
  rw [hx] at hη'
  obtain ⟨ξK, hξK⟩ := exists_cechCohomologyEdge_apply_eq_globalStepToAbutment_apply.{max u v w}
    J F L i η'
  exact ⟨L, ξK, hξK.trans hη'⟩

end Descent

end Stacks.CategoryTheory.Hypercovering

end
