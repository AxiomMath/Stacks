module

public import StacksFrontier.CategoryTheory.Sites.Hypercovering.CohomologyZeroRepresentatives
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.EdgeMap

/-!
# The abutment of the spectral sequence of a hypercovering of a presheaf, in the hypercovering

Let `C` be a site with equalizers and fibre products, let `G` be a presheaf of sets on `C` and let
`K` be a hypercovering of `G` ([Stacks, Tag 09VU]).  [Stacks, Tag 09VX] gives a first-quadrant
spectral sequence `E₂^{p,q} = Ȟ^p(K, H̲^q(F))` converging to `H^{p+q}(G, F)`, functorial in the
abelian sheaf `F`, and `presheafHypercoveringSpectralSequenceFunctoriality` makes the *spectral
sequence* functorial in `K`.  What that functoriality leaves open, and what is supplied here, is
the compatibility of the identification of the **abutment** with a morphism of hypercoverings: it
is what the comparison of [Stacks, Tag 09VZ] in degrees above zero needs, and what the
implementation notes of `StacksFrontier/CategoryTheory/Sites/Hypercovering/EdgeMap.lean` record as
missing.

## Why the abutment does not move

Cohomology over `G` is the right derived functor of `Γ(G, -) = Hom(**Z**_G^♯, -)`, and
`presheafSectionsFunctor J G K` is that functor: the augmented simplicial presheaf
`HypercoveringOf.toAugmentedULift` of a hypercovering of `G` has `liftedPresheaf G` at the
augmentation points, which mentions no hypercovering.  Consequently
`presheafSectionsFunctor J G K = presheafSectionsFunctor J G L` and
`presheafSectionsRightDerivedNatIso J G K n = presheafSectionsRightDerivedNatIso J G L n`
*definitionally*, and the only factor of `hypercoverPresheafAbutmentIso` that moves with the
hypercovering is the comparison of [Stacks, Tag 0133].  That comparison is **data**
(`comparisonMapP`), not a chosen witness, so it has a naturality statement, and its hypothesis is
the compatibility of the augmentation of the double complex with the Čech pullback.  That
compatibility is `HypercoveringOf.Hom.presheafSectionsAug_comp_rowZeroMap`, the general-degree
analogue of `freeAbelianSheafEpsZero_comp_homCxPrecomp`; its two ingredients -- the degree-zero
augmentation square and the naturality of [Stacks, Tag 01GX] in the hypercovering -- live upstream
in `HomComplexAugmentation.lean` and `CohomologyZeroRepresentatives.lean`.

## Main definitions

* `Stacks.CategoryTheory.Hypercovering.HypercoveringOf.Hom.doubleMap` and
  `filteredMap`: the Čech pullback along a morphism of hypercoverings on the double complex of a
  sheaf and on its total complex filtered by the hypercovering degree.
* `Stacks.CategoryTheory.Hypercovering.presheafCechCohomologyFunctorMap`: the Čech pullback on
  `Ȟ^p(-, -)`, as a morphism of functors of the coefficient presheaf.
* `Stacks.CategoryTheory.Hypercovering.globalAbutment`: the functorial filtered abutment of
  [Stacks, Tag 09VY], named.

## Main results

* `Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo.bottomRowEdge_comp_of_cocone`: **a
  cocone criterion for the bottom-row edge map.**  Two functorial first-quadrant abutments with
  the same asserted abutment, a morphism of the spectral sequences at an object and a morphism of
  the filtered abutments compatible with it give a cocone identity for the edge maps.  Unlike
  `bottomRowEdge_naturality` the two morphisms need not come from a morphism of the parameter
  category, which is what makes the criterion applicable to a morphism of hypercoverings.
* `HypercoveringOf.Hom.hypercoverPresheafAugmentation_comp_sectionsComplexIntFunctorMap`: the
  augmentation of the Čech complex is natural in the hypercovering.
* `Stacks.CategoryTheory.Hypercovering.HypercoveringOf.Hom.presheafSectionsAug_comp_rowZeroMap`:
  the augmentation of the double complex of [Stacks, Tag 0133] is natural in the hypercovering.
* `HypercoveringOf.Hom.totalComparison_comp_homologyMap_filteredMap`: **the comparison of
  [Stacks, Tag 0133] forms a cocone on the hypercoverings of `G`.**
* `HypercoveringOf.Hom.homologyMap_filteredMap_comp_abutmentIso`:
  **the abutment identification of [Stacks, Tag 09VX] forms a cocone on the hypercoverings of
  `G`**: the Čech pullback followed by the identification of `K` is the identification of `L`.
  Nothing is assumed.
* `HypercoveringOf.Hom.hypercoverPresheafGradedIso_naturality`: **the identification
  `E_∞^{p,q} ≅ gr^pH^{p+q}` of [Stacks, Tag 09VX] is natural in the hypercovering**, which is the
  hypothesis `hgr` of `bottomRowEdge_comp_of_cocone`.  Its three factors --
  `hypercoverPresheafPageInfinityIso`, `hypercoverPresheafPageInfinityTransportIso` and
  `hypercoverPresheafCanonicalGradedIso` -- each rest on a generic lemma accepting an arbitrary
  morphism of spectral sequences.
* `HypercoveringOf.Hom.spectralSequenceFunctorMap_comp_bottomRowEdge`: **the bottom-row edge map
  of [Stacks, Tag 09VX] forms a cocone on the hypercoverings of `G`.**
* `CategoryTheory.Functor.mapHomologicalComplexHomologyIso_hom_app_naturality`: the homology
  comparison of an exact functor is natural **in the functor**.  This is the one new generic
  ingredient of the second-page naturality.
* `HypercoveringOf.Hom.hypercoverPresheafPageTwoIso_naturality`: **the second page of
  [Stacks, Tag 09VX] is `Ȟ^p(K, H̲^{q'}(F))` naturally in the hypercovering**, for every `(p, q')`.
* `HypercoveringOf.Hom.globalCechEdge_comp_cechCohomologyMap`: **the global edge map
  `Ȟ^i(K, 𝓕) ⟶ H^i(𝓕)` of [Stacks, Tag 09VY] forms a cocone on the hypercoverings of the final
  presheaf, in every degree**, with coefficients in the sheaf itself.  This is the cocone identity
  the comparison of [Stacks, Tag 09VZ] needs in general degree, and nothing about it is assumed.
* `Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo.isIso_bottomRowEdge_zero_app`: **in
  degree zero the bottom-row edge map of a first-quadrant spectral sequence is an isomorphism**,
  the corner `E₂^{0,0}` being the whole abutment; hence
  `Stacks.CategoryTheory.Hypercovering.isIso_globalCechEdge_zero_app` for the global edge map.
* `Stacks.CategoryTheory.Hypercovering.cechCohomologyEdge`: the canonical comparison
  `Ȟ^i(K, 𝓕) ⟶ H^i(𝓕)` of [Stacks, Tag 09VY] with its source written as the Čech cohomology
  group, which is the spelling the Čech pullback lives in, together with its cocone identity
  `cechCohomologyMap_comp_cechCohomologyEdge` and, in degree zero,
  `isIso_cechCohomologyEdge_zero`.
* `Stacks.CategoryTheory.Hypercovering.exists_hypercoveringOfTerminal_cechCohomologyEdge_zero_eq`
  and `Stacks.CategoryTheory.Hypercovering.exists_hom_cechCohomologyEdge_zero_eq`: **both parts
  of [Stacks, Tag 09VZ] in degree zero**, for that comparison, with nothing assumed beyond the
  source's hypotheses.

## Implementation notes

Every square here is assembled in term mode or through a `show` that pins all four corners.  This
is forced rather than stylistic: the two sides of each square are typed through different --
definitionally equal -- spellings of one object (`presheafSectionsResZ J G K F` versus
`... J G L F`, `(hypercoverPresheafFiltrationFunctor J G K n ⋙ forget).obj F` versus
`HomologicalComplex.homology (hypercoverPresheafFiltered J G K F).X n`), and a rewrite, whose
motive is type-checked at the `instances` transparency, cannot see through them; when it fails it
fails silently for every subsequent rewrite in the same `rw` list.

Several steps are forced into a shape that looks roundabout.  `globalAbutment` is an `abbrev`
rather than the `abutment` field of `hypercoveringGlobalSpectralSequence` read in place, and
`globalCechEdge_app` is assembled out of `globalCechEdge_app_aux`, `globalPageTwoIso_inv_app` and
`globalAbutmentEdge_app` rather than proved by a single `rfl`: each of those identities is true by
definition, but the single `rfl` for their composite exhausts the elaborator's heartbeats, while
the three separately do not.  For the same reason the three squares of
`globalCechEdge_comp_cechCohomologyMap` are pasted in `globalCechEdge_square`, whose statement is
written in the spelling the squares themselves use, so that the passage to the spelling of
`globalCechEdge` happens in one step and in a declaration of its own.

The degree-zero statements of [Stacks, Tag 09VZ] at the end of the file are split the same way and
for the same reason.  `globalCechEdge` is a morphism out of a value of
`presheafCechCohomologyFunctor`, while the Čech pullback `HypercoveringOf.Hom.cechCohomologyMap`
is a morphism between values of `cechCohomology`; the two spellings are definitionally equal, but
each identification costs an unfolding of `presheafCechCohomologyFunctor`, `Functor.comp` and
`HomologicalComplex.homologyFunctor`, and three or four of them in one declaration -- which is
what writing the element-level steps out with their types does -- exhausts the heartbeats.
`cechCohomologyEdge` and the two lemmas after it pay for the identification once each, and
everything after them is in the `cechCohomology` spelling alone.  The element-level steps are
then taken by `hom_apply_eq_of_comp_eq_of_isIso`, which chains them between bare objects of
`AddCommGrpCat`: chaining two equations between elements of a functor value instead makes the
elaborator compare the `ConcreteCategory` instance paths that produced them, and that is the one
step that did not finish inside the heartbeats even with the spellings unified.

The naturality in the hypercovering of the **coefficient** half of the second page rests on one
new generic ingredient,
`CategoryTheory.Functor.mapHomologicalComplexHomologyIso_hom_app_naturality`: the comparison
`H^i(E(K^•)) ≅ E(H^i(K^•))` of an exact functor is natural in `E`, which is
`CategoryTheory.NatTrans.app_homology` read on a homological complex.  It is needed because the
coefficient comparison `hypercoverPresheafDoubleHomologyNatIso` is the homology comparison of the
sections complex functor of the hypercovering, and a morphism of hypercoverings moves that
functor.

What is **not** proved here, and what [Stacks, Tag 09VZ] needs on top of the cocone identity, is
the **degeneration** of the spectral sequence of a hypercovering of the final presheaf in the
colimit over hypercoverings.  The degeneration available in
`StacksFrontier/CategoryTheory/Sites/Hypercovering/PageDegeneration.lean` -- for `q > 0` and every
`r ≥ 2`, every element of `E_r^{p,q}` dies after a refinement -- is for a hypercovering of an
*object* of a small site, where Čech cohomology is taken in `FormalCoproduct (Over X)`.  The
analogue for hypercoverings of the final presheaf is not available: it would need the analogue of
[Stacks, Tag 01GJ] (`exists_hypercovering_map_factoring_through_covering`) for hypercoverings of
the final presheaf, on which `exists_hypercovering_map_cechCohomology_eq_zero` rests.  Without it
neither part (1) nor part (2) of [Stacks, Tag 09VZ] can be had in degrees above zero, so both are
stated only in degree zero, where the edge map is an isomorphism and no degeneration is needed;
that is what the two tags on this file say.

## References

* [Stacks Project, Tag 09VX](https://stacks.math.columbia.edu/tag/09VX)
* [Stacks Project, Tag 09VY](https://stacks.math.columbia.edu/tag/09VY)
* [Stacks Project, Tag 09VZ](https://stacks.math.columbia.edu/tag/09VZ)
* [Stacks Project, Tag 01GY](https://stacks.math.columbia.edu/tag/01GY)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
* [Stacks Project, Tag 01GX](https://stacks.math.columbia.edu/tag/01GX)
* [Stacks Project, Tag 09VU](https://stacks.math.columbia.edu/tag/09VU)
* [Stacks Project, Tag 0DAX](https://stacks.math.columbia.edu/tag/0DAX)
-/

@[expose] public noncomputable section

universe q w v u

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

/-! ### A cocone criterion for the bottom-row edge map -/

namespace Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo

variable {D A : Type*} [Category* D] [Category* A] [Abelian A]
  {E₁ E₂ : D ⥤ E₂CohomologicalSpectralSequenceNat A} {H : ℕ → D ⥤ A}

/-- **A cocone criterion for the bottom-row edge map.**  Let two functorial first-quadrant
abutments of two spectral sequences have the *same* asserted abutment `H`, let `φ` be a morphism
of the spectral sequences at an object `X` and let `θ` be a morphism of the filtered abutments at
`X`.  If `φ` and `θ` agree through the graded identifications, and if `θ` is compatible with the
two abutment identifications, then `φ` on the second page at `(i, 0)` followed by the edge map of
the first abutment is the edge map of the second.

This is `bottomRowEdge_app` with the five factors moved past `φ` in turn: the edge epimorphism by
`CategoryTheory.SpectralSequence.Hom.edgeEpi_naturality`, the graded identification by `hgr`, the
identification of `gr^i` with `F^i` by `CategoryTheory.FilteredObject.grMapπ_map`, the filtration
inclusion by `CategoryTheory.FilteredObject.Hom.comm` and the abutment identification by `hab`.

Unlike `bottomRowEdge_naturality`, `φ` and `θ` are *not* required to come from a morphism of the
parameter category `D`; that is what makes the criterion applicable to a morphism of
hypercoverings, which the parameter category of the spectral sequence of [Stacks, Tag 09VX] does
not contain. -/
theorem bottomRowEdge_comp_of_cocone
    (h₁ : FunctorialFirstQuadrantAbutsTo E₁ H) (h₂ : FunctorialFirstQuadrantAbutsTo E₂ H)
    (i : ℕ) (X : D) (φ : E₂.obj X ⟶ E₁.obj X)
    (θ : (h₂.filtration i).obj X ⟶ (h₁.filtration i).obj X)
    (hgr : CategoryTheory.SpectralSequence.Hom.mapPageInfinity φ (i, 0) ≫
        (h₁.bottomGradedIso i X).hom =
      (h₂.bottomGradedIso i X).hom ≫ (FilteredObject.gr (i : ℤ)).map θ)
    (hab : θ.hom ≫ (h₁.abutmentIso i).hom.app X = (h₂.abutmentIso i).hom.app X) :
    (φ.hom 2).f (i, 0) ≫ (h₁.bottomRowEdge i).app X = (h₂.bottomRowEdge i).app X := by
  have := h₁.isIso_grMapπ i X
  have := h₂.isIso_grMapπ i X
  have hπ : (FilteredObject.gr (i : ℤ)).map θ ≫
        inv (FilteredObject.grMapπ (FilteredObject.succHom (i : ℤ))
          ((h₁.filtration i).obj X)) =
      inv (FilteredObject.grMapπ (FilteredObject.succHom (i : ℤ))
          ((h₂.filtration i).obj X)) ≫ θ.natTrans.app (op (i : ℤ)) := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, IsIso.comp_inv_eq]
    exact FilteredObject.grMapπ_map _ θ
  rw [h₁.bottomRowEdge_app i X, h₂.bottomRowEdge_app i X,
    reassoc_of% (CategoryTheory.SpectralSequence.Hom.edgeEpi_naturality φ (i, 0) 2),
    reassoc_of% hgr, reassoc_of% hπ,
    reassoc_of% (FilteredObject.Hom.comm θ (op (i : ℤ))), hab]

/-- **Transporting the abutment along an isomorphism postcomposes the bottom-row edge map with
it.**  `FunctorialFirstQuadrantAbutsTo.ofIsoAbutment` changes the single field `abutmentIso`, and
that field is the last factor of `bottomRowEdge`; the other three factors are independent of the
asserted abutment. -/
lemma bottomRowEdge_ofIsoAbutment (h : FunctorialFirstQuadrantAbutsTo E₁ H)
    {H' : ℕ → D ⥤ A} (e : ∀ n, H n ≅ H' n) (i : ℕ) :
    (h.ofIsoAbutment e).bottomRowEdge i = h.bottomRowEdge i ≫ (e i).hom := by
  change h.bottomRowGrHom i ≫ (h.grIsoEval i).hom ≫ h.evalHomForget i ≫
      ((h.abutmentIso i).hom ≫ (e i).hom) =
    (h.bottomRowGrHom i ≫ (h.grIsoEval i).hom ≫ h.evalHomForget i ≫
      (h.abutmentIso i).hom) ≫ (e i).hom
  simp only [Category.assoc]

/-- **In degree zero the bottom-row edge map is an isomorphism**: for a first-quadrant spectral
sequence the corner `E₂^{0,0}` is already the whole abutment `H^0`.

Each of the four factors of `bottomRowEdge` is invertible at `i = 0`: the edge epimorphism
`E₂^{0,0} ⟶ E_∞^{0,0}` because there is no differential into or out of the corner, so both edge
classes hold there and `edgeEpi` is `pageInfinityIso` inverted; the graded identification because
it is an isomorphism; the projection `F^0H^0 ⟶ gr^0H^0` because the first filtration step vanishes
in degree zero (`isIso_grMapπ`); and the inclusion `F^0H^0 ⟶ H^0` because the zeroth step is the
top one (`isTop`). -/
lemma isIso_bottomRowEdge_zero_app (h : FunctorialFirstQuadrantAbutsTo E₁ H) (K : D) :
    IsIso ((h.bottomRowEdge 0).app K) := by
  have he : IsIso ((E₁.obj K).edgeEpi ((0 : ℕ), (0 : ℕ)) 2) := by
    rw [(E₁.obj K).edgeEpi_eq_pageInfinityIso_inv ((0 : ℕ), (0 : ℕ)) 2]
    infer_instance
  have := h.isIso_grMapπ 0 K
  have hι : IsIso (((h.filtration 0).obj K).filtration.ι.app (op (((0 : ℕ) : ℤ)))) :=
    (Filtration.subobject_eq_top_iff _ _).1 (by simpa using h.isTop K 0)
  have hb : IsIso ((h.bottomGradedIso 0 K).hom) := inferInstance
  have ha : IsIso ((h.abutmentIso 0).hom.app K) := inferInstance
  have hinv : IsIso (inv (FilteredObject.grMapπ (FilteredObject.succHom (((0 : ℕ) : ℤ)))
    ((h.filtration 0).obj K))) := inferInstance
  rw [h.bottomRowEdge_app 0 K]
  exact IsIso.comp_isIso' he (IsIso.comp_isIso' hb (IsIso.comp_isIso' hinv
    (IsIso.comp_isIso' hι ha)))

end Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo



/-! ### The degree-zero part of an augmentation, composed with a map of complexes -/

namespace StacksDraft.DerivedSectionsComparison

/-- **Composing the degree-zero part of an augmentation out of a single complex with a morphism of
complexes is the degree-zero part of the composite augmentation.**  Both sides are the
single-complex identification followed by the degree-zero components, so this is
`CategoryTheory.Category.assoc`. -/
theorem augZero_comp {B : Type u} [Category.{v} B] [Abelian B] (Z : B)
    {L L' : CochainComplex B ℤ}
    (g : (HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj Z ⟶ L) (φ : L ⟶ L') :
    augZero Z L g ≫ φ.f 0 = augZero Z L' (g ≫ φ) :=
  Category.assoc _ _ _

/-- **Two isomorphisms out of one object and a morphism between their targets**: if the triangle
commutes then the morphism is the composite of the inverses. -/
theorem comp_inv_eq_inv {𝒜 : Type*} [Category* 𝒜] {X Y Z : 𝒜} (a : X ≅ Y) (b : X ≅ Z)
    (m : Y ⟶ Z) (h : a.hom ≫ m = b.hom) : m ≫ b.inv = a.inv := by
  rw [Iso.comp_inv_eq, ← h, ← Category.assoc, a.inv_hom_id, Category.id_comp]

/-- **A triangle of isomorphisms read in the inverse direction.** -/
theorem inv_comp_eq_comp_inv {𝒜 : Type*} [Category* 𝒜] {X Y X' Y' : 𝒜}
    (e : X ≅ X') (e' : Y ≅ Y') (f : X ⟶ Y) (g : X' ⟶ Y')
    (h : f ≫ e'.hom = e.hom ≫ g) : e.inv ≫ f = g ≫ e'.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← h, Category.assoc, e'.hom_inv_id, Category.comp_id]

end StacksDraft.DerivedSectionsComparison

/-! ### The homology comparison of an exact functor is natural in the functor -/

namespace CategoryTheory.Functor

/-- **`CategoryTheory.Functor.mapHomologicalComplexHomologyIso` is natural in the functor.**  A
natural transformation `α : E ⟶ E'` of exact functors acts on the homology of a complex either
through the complexes or through the homology, and the two agree.

This is `CategoryTheory.NatTrans.app_homology` -- the component of `α` at the homology of the
short complex in degree `i`, computed through the two homology comparisons -- read on the
homology of a homological complex, which is by definition the homology of that short complex.
It is what makes the coefficient comparison of a second page natural in the functor whose
homology is being compared, and so in the hypercovering. -/
theorem mapHomologicalComplexHomologyIso_hom_app_naturality {B : Type*} [Category* B]
    [Abelian B] {B' : Type*} [Category* B'] [Abelian B'] {E E' : B ⥤ B'} [E.Additive]
    [E.PreservesHomology] [E'.Additive] [E'.PreservesHomology] (α : E ⟶ E') {ι : Type*}
    (c : ComplexShape ι) (i : ι) (Z : HomologicalComplex B c) :
    HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex α c).app Z) i ≫
        (E'.mapHomologicalComplexHomologyIso c i).hom.app Z =
      (E.mapHomologicalComplexHomologyIso c i).hom.app Z ≫ α.app (Z.homology i) := by
  refine Eq.trans ?_ (congrArg (fun t ↦ ((Z.sc i).mapHomologyIso E).hom ≫ t)
    (_root_.CategoryTheory.NatTrans.app_homology (F := E) (G := E') α (Z.sc i)).symm)
  exact (Iso.hom_inv_id_assoc ((Z.sc i).mapHomologyIso E)
    (ShortComplex.homologyMap ((Z.sc i).mapNatTrans α) ≫
      ((Z.sc i).mapHomologyIso E').hom)).symm

end CategoryTheory.Functor

/-! ### An isomorphism of abelian groups, read on elements -/

namespace Stacks.CategoryTheory.Hypercovering

/-- **An isomorphism of abelian groups hits every element**: the element is the image of its
value under the inverse. -/
lemma exists_hom_apply_eq_of_isIso {A B : AddCommGrpCat.{q}} (φ : A ⟶ B) [IsIso φ]
    (z : ToType B) : ∃ x, ConcreteCategory.hom φ x = z :=
  (ConcreteCategory.bijective_of_isIso φ).2 z

/-- **A commuting triangle of morphisms of abelian groups, read on an element.**  Stated so that
the element-level steps below can be taken without writing down the type of either side: the
objects involved are values of functors built out of a hypercovering, and a written-down type
there has to be unified with the one the term produces, which is expensive. -/
lemma hom_apply_apply_eq_of_comp_eq {A₁ A₂ A₃ : AddCommGrpCat.{q}} {f : A₁ ⟶ A₂} {g : A₂ ⟶ A₃}
    {k : A₁ ⟶ A₃} (e : f ≫ g = k) (x : ToType A₁) :
    ConcreteCategory.hom g (ConcreteCategory.hom f x) = ConcreteCategory.hom k x :=
  (ConcreteCategory.comp_apply f g x).symm.trans (ConcreteCategory.congr_hom e x)

/-- **An isomorphism of abelian groups is injective on elements**: applying the inverse cancels
it. -/
lemma hom_apply_injective_of_isIso {A B : AddCommGrpCat.{q}} (φ : A ⟶ B) [IsIso φ]
    {x y : ToType A} (hxy : ConcreteCategory.hom φ x = ConcreteCategory.hom φ y) : x = y :=
  (ConcreteCategory.bijective_of_isIso φ).1 hxy

/-- **Two elements of two groups mapping into one group agree already there, as soon as their
images under an isomorphism out of it agree**, the two composites with that isomorphism being
given.  This is `hom_apply_apply_eq_of_comp_eq` on each side and
`hom_apply_injective_of_isIso` in the middle.

The three steps are chained here, between bare objects of `AddCommGrpCat`, rather than at the
point of use: there the objects are values of functors built out of a hypercovering, and chaining
two equations between elements of such an object makes the elaborator compare the two
`ConcreteCategory` instance paths that produced them, which it does not finish inside its
heartbeats. -/
lemma hom_apply_eq_of_comp_eq_of_isIso {A₁ A₂ A₃ B : AddCommGrpCat.{q}} {f : A₁ ⟶ A₃}
    {g : A₂ ⟶ A₃} (φ : A₃ ⟶ B) [IsIso φ] {kf : A₁ ⟶ B} {kg : A₂ ⟶ B} (ef : f ≫ φ = kf)
    (eg : g ≫ φ = kg) {x : ToType A₁} {y : ToType A₂}
    (h : ConcreteCategory.hom kf x = ConcreteCategory.hom kg y) :
    ConcreteCategory.hom f x = ConcreteCategory.hom g y :=
  hom_apply_injective_of_isIso φ
    ((hom_apply_apply_eq_of_comp_eq ef x).trans
      (h.trans (hom_apply_apply_eq_of_comp_eq eg y).symm))

/-! ### The augmentation of the Čech complex is natural in the hypercovering -/

variable {C : Type u} [Category.{v} C] [HasEqualizers C] [HasPullbacks C]
variable (J : Pretopology C) (G : Cᵒᵖ ⥤ Type q)
  [HasSheafify J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}]

/-- **[Stacks, Tag 01GX] is natural in the hypercovering**, on the `ℤ`-indexed complexes: the
`ℕ`-indexed square whiskered by the extension functor. -/
theorem HypercoveringOf.Hom.sectionsComplexIntFunctorMap_comp_sectionsComplexIntIso
    {K L : HypercoveringOf.{q, w} J G} (ψ : HypercoveringOf.Hom K L) :
    SemiRepresentable.sectionsComplexIntFunctorMap.{q, w, v, u}
          J.toGrothendieck ψ.simplicialHom ≫
        (sectionsComplexIntIsoFreeAbelianSheafHomCxZ.{q, w, v, u} J G K).hom =
      (sectionsComplexIntIsoFreeAbelianSheafHomCxZ.{q, w, v, u} J G L).hom ≫
        SimplicialObject.Augmented.freeAbelianSheafHomCxZPrecomp J.toGrothendieck
          (ψ.toAugmentedULiftHom J G) :=
  (Functor.whiskerRight_comp _ _
        (ComplexShape.embeddingUpNat.extendFunctor
          AddCommGrpCat.{max (max u v) (max q w)})).symm.trans
    ((congrArg (fun t ↦ Functor.whiskerRight t
          (ComplexShape.embeddingUpNat.extendFunctor
            AddCommGrpCat.{max (max u v) (max q w)}))
        (ψ.sectionsComplexFunctorMap_comp_sectionsComplexIso J G)).trans
      (Functor.whiskerRight_comp _ _
        (ComplexShape.embeddingUpNat.extendFunctor
          AddCommGrpCat.{max (max u v) (max q w)})))

/-- **The augmentation of the Čech complex of a hypercovering of `G` is natural in the
hypercovering**: the augmentation of `L` followed by the Čech pullback along `ψ : K ⟶ L` is the
augmentation of `K`.

Both augmentations are the augmentation of the Hom complex of the augmented simplicial presheaf
read through the comparison of [Stacks, Tag 01GX]; the first factor moves by
`CategoryTheory.SimplicialObject.Augmented.freeAbelianSheafEpsNatTrans_comp_homCxZPrecomp`, whose
component at the augmentation points is an identity, and the second by
`HypercoveringOf.Hom.sectionsComplexIntFunctorMap_comp_sectionsComplexIntIso`.

The sources of the two sides agree because `presheafSectionsFunctor J G K` does not mention `K`:
the augmented simplicial presheaf of a hypercovering of `G` has `liftedPresheaf G` at the
augmentation points. -/
theorem HypercoveringOf.Hom.hypercoverPresheafAugmentation_comp_sectionsComplexIntFunctorMap
    {K L : HypercoveringOf.{q, w} J G} (ψ : HypercoveringOf.Hom K L) :
    hypercoverPresheafAugmentation.{q, w, v, u} J G L ≫
        SemiRepresentable.sectionsComplexIntFunctorMap.{q, w, v, u}
          J.toGrothendieck ψ.simplicialHom =
      hypercoverPresheafAugmentation.{q, w, v, u} J G K := by
  have hinv := StacksDraft.DerivedSectionsComparison.inv_comp_eq_comp_inv
    (sectionsComplexIntIsoFreeAbelianSheafHomCxZ.{q, w, v, u} J G L)
    (sectionsComplexIntIsoFreeAbelianSheafHomCxZ.{q, w, v, u} J G K)
    (SemiRepresentable.sectionsComplexIntFunctorMap.{q, w, v, u}
      J.toGrothendieck ψ.simplicialHom)
    (SimplicialObject.Augmented.freeAbelianSheafHomCxZPrecomp J.toGrothendieck
      (ψ.toAugmentedULiftHom J G))
    (ψ.sectionsComplexIntFunctorMap_comp_sectionsComplexIntIso J G)
  have heps : SimplicialObject.Augmented.freeAbelianSheafEpsNatTrans J.toGrothendieck
          (L.toAugmentedULift.{q, w, v, u} J G) ≫
        SimplicialObject.Augmented.freeAbelianSheafHomCxZPrecomp J.toGrothendieck
          (ψ.toAugmentedULiftHom J G) =
      SimplicialObject.Augmented.freeAbelianSheafEpsNatTrans J.toGrothendieck
        (K.toAugmentedULift.{q, w, v, u} J G) := by
    rw [SimplicialObject.Augmented.freeAbelianSheafEpsNatTrans_comp_homCxZPrecomp
        J.toGrothendieck (ψ.toAugmentedULiftHom J G),
      ψ.freeAbelianSheafSectionsPrecomp_toAugmentedULiftHom J G]
    exact (congrArg (fun t ↦ t ≫ SimplicialObject.Augmented.freeAbelianSheafEpsNatTrans
          J.toGrothendieck (K.toAugmentedULift.{q, w, v, u} J G))
        (Functor.whiskerRight_id'
          (HomologicalComplex.single AddCommGrpCat.{max (max u v) (max q w)}
            (ComplexShape.up ℤ) 0))).trans (Category.id_comp _)
  change (SimplicialObject.Augmented.freeAbelianSheafEpsNatTrans J.toGrothendieck
          (L.toAugmentedULift.{q, w, v, u} J G) ≫
        (sectionsComplexIntIsoFreeAbelianSheafHomCxZ.{q, w, v, u} J G L).inv) ≫
      SemiRepresentable.sectionsComplexIntFunctorMap.{q, w, v, u}
        J.toGrothendieck ψ.simplicialHom =
    SimplicialObject.Augmented.freeAbelianSheafEpsNatTrans J.toGrothendieck
        (K.toAugmentedULift.{q, w, v, u} J G) ≫
      (sectionsComplexIntIsoFreeAbelianSheafHomCxZ.{q, w, v, u} J G K).inv
  rw [Category.assoc, hinv, ← Category.assoc, heps]
  rfl

/-- **The augmentation of the double complex of a hypercovering of `G` is natural in the
hypercovering**, which is the presheaf analogue of
`Stacks.CategoryTheory.Hypercovering.Functorial.hypercoverAugCochain_app_comp_cechPullback`: the
augmentation of `L` followed by the Čech pullback along `ψ : K ⟶ L` on the zeroth rows is the
augmentation of `K`.

The augmentation is `StacksDraft.DerivedSectionsComparison.augZero` of
`hypercoverPresheafAugmentation` in each outer degree, so this is
`HypercoveringOf.Hom.hypercoverPresheafAugmentation_comp_sectionsComplexIntFunctorMap` read
degreewise. -/
theorem HypercoveringOf.Hom.presheafSectionsAug_comp_rowZeroMap
    [EnoughInjectives (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)})]
    {K L : HypercoveringOf.{q, w} J G} (ψ : HypercoveringOf.Hom K L)
    (Z : CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) ℤ) :
    presheafSectionsAug J G L Z ≫
        rowZeroMap ((hypercoverPresheafDoubleFunctorMap.{q, w, v, u}
          J G ψ.simplicialHom).app Z) =
      presheafSectionsAug J G K Z := by
  refine HomologicalComplex.hom_ext _ _ fun r ↦ ?_
  have h : (hypercoverPresheafAugmentation.{q, w, v, u} J G L).app (Z.X r) ≫
      (SemiRepresentable.sectionsComplexIntFunctorMap.{q, w, v, u}
        J.toGrothendieck ψ.simplicialHom).app (Z.X r) =
      (hypercoverPresheafAugmentation.{q, w, v, u} J G K).app (Z.X r) :=
    congrArg (fun t ↦ NatTrans.app t (Z.X r))
      (ψ.hypercoverPresheafAugmentation_comp_sectionsComplexIntFunctorMap J G)
  exact (StacksDraft.DerivedSectionsComparison.augZero_comp _ _ _).trans
    (congrArg (StacksDraft.DerivedSectionsComparison.augZero
      ((presheafSectionsFunctor.{q, w, v, u} J G K).obj (Z.X r))
      ((SemiRepresentable.sectionsComplexIntFunctor.{q, w, v, u} J.toGrothendieck
        K.toSimplicialObject).obj (Z.X r))) h)

/-! ### The filtered total complex is contravariant in the hypercovering -/

section Filtered

variable [EnoughInjectives (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)})]

/-- **The morphism of double complexes of a sheaf attached to a morphism of hypercoverings**: the
Čech pullback degreewise in the chosen injective resolution.  Unlike the morphism attached to a
morphism of sheaves it is functorial on the nose, the chosen resolution being untouched. -/
def HypercoveringOf.Hom.doubleMap {K L : HypercoveringOf.{q, w} J G}
    (ψ : HypercoveringOf.Hom K L)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) :
    hypercoverPresheafDouble J G L F ⟶ hypercoverPresheafDouble J G K F :=
  (hypercoverPresheafDoubleOfNatFunctorMap.{q, w, v, u} J G ψ.simplicialHom).app
    (injectiveResolution F).cocomplex

/-- **The morphism of filtered total complexes attached to a morphism of hypercoverings.**  A
morphism of hypercoverings acts degreewise in both indices of the double complex, so it respects
the filtration by the hypercovering degree; this is `HypercoveringOf.Hom.doubleMap` with that
filtration. -/
def HypercoveringOf.Hom.filteredMap {K L : HypercoveringOf.{q, w} J G}
    (ψ : HypercoveringOf.Hom K L)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) :
    hypercoverPresheafFiltered J G L F ⟶ hypercoverPresheafFiltered J G K F :=
  Stacks.Cohomology.CechSpectral.totalFiltrationMap (fun (_ : ℤ) j => j) (fun _ _ => le_rfl)
    (fun _ _ => by omega) (ψ.doubleMap J G F)

/-- The underlying morphism of complexes of `HypercoveringOf.Hom.filteredMap` is the total complex
of the Čech pullback. -/
@[simp]
lemma HypercoveringOf.Hom.filteredMap_hom {K L : HypercoveringOf.{q, w} J G}
    (ψ : HypercoveringOf.Hom K L)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) :
    (ψ.filteredMap J G F).hom =
      HomologicalComplex₂.total.map (ψ.doubleMap J G F) (ComplexShape.up ℤ) :=
  rfl

/-- The value of the comparison isomorphism of [Stacks, Tag 0133] at a sheaf, unfolded to the map
`comparisonMapP` induces on cohomology.  Stated on its own: the two spellings are definitionally
equal, but discovering that inside a larger goal is not affordable. -/
lemma hypercoverPresheafTotalComparisonNatIso_hom_app
    (K : HypercoveringOf.{q, w} J G) (n : ℕ)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) :
    (hypercoverPresheafTotalComparisonNatIso J G K n).hom.app F =
      HomologicalComplex.homologyMap
        (comparisonMapP (presheafSectionsResZ J G K F) (hypercoverPresheafDouble J G K F)
          (presheafSectionsAug J G K ((ComplexShape.embeddingUpNat.extendFunctor
            (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)})).obj
              (injectiveResolution F).cocomplex))
          (hypotheses_presheafSectionsAug_resolution J G K F)) (n : ℤ) := by
  dsimp only [hypercoverPresheafTotalComparisonNatIso, NatIso.ofComponents_hom_app,
    hypercoverPresheafTotalComparisonIso, comparisonHomologyIso, asIso_hom]
  rfl

/-- The value of the abutment identification of [Stacks, Tag 09VX] at a sheaf, as the composite of
its two factors. -/
lemma hypercoverPresheafAbutmentIso_hom_app
    (K : HypercoveringOf.{q, w} J G) (n : ℕ)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) :
    (hypercoverPresheafAbutmentIso J G K n).hom.app F =
      (hypercoverPresheafTotalComparisonNatIso J G K n).inv.app F ≫
        (presheafSectionsRightDerivedNatIso J G K n).hom.app F :=
  rfl

set_option maxHeartbeats 1600000 in
/-- **The comparison of [Stacks, Tag 0133] forms a cocone on the hypercoverings of `G`**: the
comparison isomorphism of `L` followed by the Čech pullback along `ψ : K ⟶ L` is the comparison
isomorphism of `K`.

Its source, `H^n(Γ(G, I^•(F)))`, does not move with the hypercovering: `presheafSectionsFunctor`
is the sections over `G` and mentions no hypercovering.  So this is `comparisonMapP_naturality`
with the identity in the complex direction, and its hypothesis is
`HypercoveringOf.Hom.presheafSectionsAug_comp_rowZeroMap`. -/
theorem HypercoveringOf.Hom.totalComparison_comp_homologyMap_filteredMap
    {K L : HypercoveringOf.{q, w} J G} (ψ : HypercoveringOf.Hom K L) (n : ℕ)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) :
    (hypercoverPresheafTotalComparisonNatIso J G L n).hom.app F ≫
        HomologicalComplex.homologyMap (ψ.filteredMap J G F).hom (n : ℤ) =
      (hypercoverPresheafTotalComparisonNatIso J G K n).hom.app F := by
  have hcomm : presheafSectionsAug J G L ((ComplexShape.embeddingUpNat.extendFunctor
          (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)})).obj
            (injectiveResolution F).cocomplex) ≫
        rowZeroMap (ψ.doubleMap J G F) =
      𝟙 (presheafSectionsResZ J G K F) ≫
        presheafSectionsAug J G K ((ComplexShape.embeddingUpNat.extendFunctor
          (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)})).obj
            (injectiveResolution F).cocomplex) :=
    (ψ.presheafSectionsAug_comp_rowZeroMap J G _).trans (Category.id_comp _).symm
  have hnat := comparisonMapP_naturality (presheafSectionsResZ J G K F)
    (hypercoverPresheafDouble J G L F)
    (presheafSectionsAug J G L ((ComplexShape.embeddingUpNat.extendFunctor
      (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)})).obj
        (injectiveResolution F).cocomplex))
    (hypotheses_presheafSectionsAug_resolution J G L F)
    (hypotheses_presheafSectionsAug_resolution J G K F)
    (𝟙 (presheafSectionsResZ J G K F)) (ψ.doubleMap J G F) hcomm
  rw [Category.id_comp] at hnat
  have h := congrArg (fun z ↦ HomologicalComplex.homologyMap z (n : ℤ)) hnat
  simp only [HomologicalComplex.homologyMap_comp] at h
  rw [hypercoverPresheafTotalComparisonNatIso_hom_app,
    hypercoverPresheafTotalComparisonNatIso_hom_app,
    HypercoveringOf.Hom.filteredMap_hom]
  exact h

set_option maxHeartbeats 1600000 in
/-- **The abutment identification of [Stacks, Tag 09VX] forms a cocone on the hypercoverings of
`G`**: the Čech pullback along `ψ : K ⟶ L` followed by the identification of `K` is the
identification of `L`.

The target `R^nΓ(G, -)` does not move with the hypercovering, and neither does the second factor
`presheafSectionsRightDerivedNatIso` of `hypercoverPresheafAbutmentIso` -- both mention only the
sections over `G`.  What moves is the first factor, and that is
`HypercoveringOf.Hom.totalComparison_comp_homologyMap_filteredMap` read in the inverse
direction. -/
theorem HypercoveringOf.Hom.homologyMap_filteredMap_comp_abutmentIso
    {K L : HypercoveringOf.{q, w} J G} (ψ : HypercoveringOf.Hom K L) (n : ℕ)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) :
    HomologicalComplex.homologyMap (ψ.filteredMap J G F).hom (n : ℤ) ≫
        (hypercoverPresheafAbutmentIso J G K n).hom.app F =
      (hypercoverPresheafAbutmentIso J G L n).hom.app F := by
  have hinv := StacksDraft.DerivedSectionsComparison.comp_inv_eq_inv
    ((hypercoverPresheafTotalComparisonNatIso J G L n).app F)
    ((hypercoverPresheafTotalComparisonNatIso J G K n).app F)
    (HomologicalComplex.homologyMap (ψ.filteredMap J G F).hom (n : ℤ))
    (ψ.totalComparison_comp_homologyMap_filteredMap J G n F)
  have hRD : presheafSectionsRightDerivedNatIso J G L n =
      presheafSectionsRightDerivedNatIso J G K n := rfl
  rw [hypercoverPresheafAbutmentIso_hom_app, hypercoverPresheafAbutmentIso_hom_app, hRD]
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun t ↦ t ≫ (presheafSectionsRightDerivedNatIso J G K n).hom.app F) hinv)

/-! ### The graded identification of the abutment is natural in the hypercovering -/

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **`hypercoverPresheafPageInfinityIso` is natural in the hypercovering.**  The mirror in the
hypercovering direction of `hypercoverPresheafPageInfinityIso_naturality`: both transports -- the
start-page shift and the first-quadrant reindexing -- are read at the page
`CochainComplex.Filtered.stablePage p q'`, which is admissible for every hypercovering at once,
and `CategoryTheory.SpectralSequence.shiftNatRestrict_pageInfinityIsoAt_naturality` accepts an
arbitrary morphism of the underlying spectral sequences, so the Čech pullback
`HomologicalComplex₂.spectralSequenceMap₂ (ψ.doubleMap J G F)` serves as well as the one induced
by a morphism of sheaves. -/
theorem HypercoveringOf.Hom.hypercoverPresheafPageInfinityIso_naturality
    {K L : HypercoveringOf.{q, w} J G} (ψ : HypercoveringOf.Hom K L)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) (p q' : ℕ) :
    Hom.mapPageInfinity
          ((hypercoverPresheafSpectralSequenceFunctorMap.{q, w, v, u} J G
            ψ.simplicialHom).app F) (p, q') ≫
        (hypercoverPresheafPageInfinityIso J G K F p q').hom =
      (hypercoverPresheafPageInfinityIso J G L F p q').hom ≫
        Hom.mapPageInfinity
          (HomologicalComplex₂.spectralSequenceMap₂ (ψ.doubleMap J G F))
          (ComplexShape.natEmb (p, q')) := by
  have := hasPageInfinityAt_hypercoverPresheafSpectralSequence₂ J G L F
    (ComplexShape.natEmb (p, q'))
  have := hasPageInfinityAt_hypercoverPresheafSpectralSequence₂ J G K F
    (ComplexShape.natEmb (p, q'))
  have := hasEdgeMonoAtFrom_hypercoverPresheafSpectralSequence₂ J G L F p q'
  have := hasEdgeEpiAtFrom_hypercoverPresheafSpectralSequence₂ J G L F p q'
  have := hasEdgeMonoAtFrom_hypercoverPresheafSpectralSequence₂ J G K F p q'
  have := hasEdgeEpiAtFrom_hypercoverPresheafSpectralSequence₂ J G K F p q'
  have := hasEdgeMonoAtFrom_hypercoverPresheafShiftStart J G L F p q'
  have := hasEdgeEpiAtFrom_hypercoverPresheafShiftStart J G L F p q'
  have := hasEdgeMonoAtFrom_hypercoverPresheafShiftStart J G K F p q'
  have := hasEdgeEpiAtFrom_hypercoverPresheafShiftStart J G K F p q'
  have := hasEdgeMonoAtFrom_hypercoverPresheafNatRestrict J G L F p q'
  have := hasEdgeEpiAtFrom_hypercoverPresheafNatRestrict J G L F p q'
  have := hasEdgeMonoAtFrom_hypercoverPresheafNatRestrict J G K F p q'
  have := hasEdgeEpiAtFrom_hypercoverPresheafNatRestrict J G K F p q'
  exact shiftNatRestrict_pageInfinityIsoAt_naturality (show (0 : ℤ) ≤ 2 by omega)
    (shiftStart_isFirstQuadrant _ (by omega)
      (isFirstQuadrant_hypercoverPresheafSpectralSequence₂ J G L F))
    (shiftStart_isFirstQuadrant _ (by omega)
      (isFirstQuadrant_hypercoverPresheafSpectralSequence₂ J G K F))
    (HomologicalComplex₂.spectralSequenceMap₂ (ψ.doubleMap J G F)) (p, q')
    (stablePage p q') (two_le_stablePage p q')

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The transport of the infinity page across the two presentations of the filtration is
natural in the hypercovering.**  The mirror in the hypercovering direction of
`hypercoverPresheafPageInfinityTransportIso_naturality`: it is
`CategoryTheory.SpectralSequence.mapPageInfinity_pageInfinityEqToIso` at the conjugation square
`HomologicalComplex₂.spectralSequenceMap₂_eqToHom` of the Čech pullback. -/
theorem HypercoveringOf.Hom.hypercoverPresheafPageInfinityTransportIso_naturality
    {K L : HypercoveringOf.{q, w} J G} (ψ : HypercoveringOf.Hom K L)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) (p q' : ℕ) :
    Hom.mapPageInfinity
          (HomologicalComplex₂.spectralSequenceMap₂ (ψ.doubleMap J G F))
          (ComplexShape.natEmb (p, q')) ≫
        (hypercoverPresheafPageInfinityTransportIso J G K F p q').hom =
      (hypercoverPresheafPageInfinityTransportIso J G L F p q').hom ≫
        Hom.mapPageInfinity (CochainComplex.filteredSpectralSequenceMap
          (ψ.filteredMap J G F)) (ComplexShape.natEmb (p, q')) := by
  have := hasPageInfinityAt_hypercoverPresheafSpectralSequence₂ J G L F
    (ComplexShape.natEmb (p, q'))
  have := hasPageInfinityAt_hypercoverPresheafSpectralSequence₂ J G K F
    (ComplexShape.natEmb (p, q'))
  have := hasPageInfinityAt_hypercoverPresheafFiltered J G L F (ComplexShape.natEmb (p, q'))
  have := hasPageInfinityAt_hypercoverPresheafFiltered J G K F (ComplexShape.natEmb (p, q'))
  exact mapPageInfinity_pageInfinityEqToIso _ _ _ _
    (HomologicalComplex₂.spectralSequenceMap₂_eqToHom (ψ.doubleMap J G F))
    (ComplexShape.natEmb (p, q'))

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **`hypercoverPresheafCanonicalGradedIso` is natural in the hypercovering.**  The mirror in the
hypercovering direction of `hypercoverPresheafCanonicalGradedIso_naturality`: it is
`CochainComplex.Filtered.canonicalPageInfinityIsoGr_naturality` at the page
`CochainComplex.Filtered.stablePage p q'`, which `isStableFrom_hypercoverPresheafFiltered` makes
stable for every hypercovering at once, applied to the Čech pullback
`HypercoveringOf.Hom.filteredMap`. -/
theorem HypercoveringOf.Hom.hypercoverPresheafCanonicalGradedIso_naturality
    {K L : HypercoveringOf.{q, w} J G} (ψ : HypercoveringOf.Hom K L)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) (p q' : ℕ) :
    Hom.mapPageInfinity (CochainComplex.filteredSpectralSequenceMap
          (ψ.filteredMap J G F)) (ComplexShape.natEmb (p, q')) ≫
        (hypercoverPresheafCanonicalGradedIso J G K F p q').hom =
      (hypercoverPresheafCanonicalGradedIso J G L F p q').hom ≫
        (FilteredObject.gr (p : ℤ)).map
          (inducedFilteredObjectMap (ψ.filteredMap J G F) ((p + q' : ℕ) : ℤ)) := by
  have := hasPageInfinityAt_hypercoverPresheafFiltered J G L F ((p : ℤ), (q' : ℤ))
  have := hasPageInfinityAt_hypercoverPresheafFiltered J G K F ((p : ℤ), (q' : ℤ))
  have := hasEdgeMonoAtFrom_hypercoverPresheafFiltered J G L F p q'
  have := hasEdgeEpiAtFrom_hypercoverPresheafFiltered J G L F p q'
  have := hasEdgeMonoAtFrom_hypercoverPresheafFiltered J G K F p q'
  have := hasEdgeEpiAtFrom_hypercoverPresheafFiltered J G K F p q'
  exact canonicalPageInfinityIsoGr_naturality (ψ.filteredMap J G F)
    (isDegreewiseFinite_hypercoverPresheafFiltered J G L F)
    (isDegreewiseFinite_hypercoverPresheafFiltered J G K F) (p : ℤ) (q' : ℤ)
    (stablePage p q')
    (isStableFrom_hypercoverPresheafFiltered J G L F p q')
    (isStableFrom_hypercoverPresheafFiltered J G K F p q')
    (inducedFilteredObjectMap (ψ.filteredMap J G F) ((p + q' : ℕ) : ℤ)) rfl

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The identification `E_∞^{p,q'} ≅ gr^pH^{p+q'}` of [Stacks, Tag 09VX] is natural in the
hypercovering**: the three squares above, pasted.  This is the hypothesis `hgr` of
`Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo.bottomRowEdge_comp_of_cocone`. -/
theorem HypercoveringOf.Hom.hypercoverPresheafGradedIso_naturality
    {K L : HypercoveringOf.{q, w} J G} (ψ : HypercoveringOf.Hom K L)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) (p q' : ℕ) :
    Hom.mapPageInfinity
          ((hypercoverPresheafSpectralSequenceFunctorMap.{q, w, v, u} J G
            ψ.simplicialHom).app F) (p, q') ≫
        (hypercoverPresheafGradedIso J G K F p q').hom =
      (hypercoverPresheafGradedIso J G L F p q').hom ≫
        (FilteredObject.gr (p : ℤ)).map
          (inducedFilteredObjectMap (ψ.filteredMap J G F) ((p + q' : ℕ) : ℤ)) := by
  rw [hypercoverPresheafGradedIso, hypercoverPresheafGradedIso]
  simp only [Iso.trans_hom, Category.assoc]
  rw [reassoc_of% ψ.hypercoverPresheafPageInfinityIso_naturality J G F p q',
    reassoc_of% ψ.hypercoverPresheafPageInfinityTransportIso_naturality J G F p q',
    ψ.hypercoverPresheafCanonicalGradedIso_naturality J G F p q']
  rfl

/-! ### The bottom-row edge map forms a cocone on the hypercoverings -/

/-- The value at a sheaf of the abutment identification carried by
`hypercoverPresheafAbutment`: the transported abutment mentions the identification of
[Stacks, Tag 09VX] alone, the filtered abutment it is transported from asserting its own
cohomology. -/
lemma hypercoverPresheafAbutment_abutmentIso_hom_app (K : HypercoveringOf.{q, w} J G) (n : ℕ)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) :
    ((hypercoverPresheafAbutment J G K).abutmentIso n).hom.app F =
      𝟙 _ ≫ (hypercoverPresheafAbutmentIso J G K n).hom.app F :=
  rfl

open Stacks.Cohomology.Leray CochainComplex.Filtered in
/-- **The bottom-row edge map of [Stacks, Tag 09VX] forms a cocone on the hypercoverings of
`G`**: the Čech pullback along `ψ : K ⟶ L` on the second page at `(i, 0)` followed by the edge
map of `K` is the edge map of `L`.

This is `Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo.bottomRowEdge_comp_of_cocone`
applied to the two abutments, with `hgr` supplied by
`HypercoveringOf.Hom.hypercoverPresheafGradedIso_naturality` and `hab` by
`HypercoveringOf.Hom.homologyMap_filteredMap_comp_abutmentIso`.  The two abutments assert the
same `H`: `presheafSectionsFunctor J G K` is the sections over `G` and does not mention `K`. -/
theorem HypercoveringOf.Hom.spectralSequenceFunctorMap_comp_bottomRowEdge
    {K L : HypercoveringOf.{q, w} J G} (ψ : HypercoveringOf.Hom K L) (i : ℕ)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) :
    (((hypercoverPresheafSpectralSequenceFunctorMap.{q, w, v, u} J G
            ψ.simplicialHom).app F).hom 2).f (i, 0) ≫
        ((hypercoverPresheafAbutment J G K).bottomRowEdge i).app F =
      ((hypercoverPresheafAbutment J G L).bottomRowEdge i).app F := by
  refine FunctorialFirstQuadrantAbutsTo.bottomRowEdge_comp_of_cocone
    (hypercoverPresheafAbutment J G K) (hypercoverPresheafAbutment J G L) i F _
    (inducedFilteredObjectMap (ψ.filteredMap J G F) (i : ℤ)) ?_ ?_
  · exact ψ.hypercoverPresheafGradedIso_naturality J G F i 0
  · rw [hypercoverPresheafAbutment_abutmentIso_hom_app J G K i F,
      hypercoverPresheafAbutment_abutmentIso_hom_app J G L i F, Category.id_comp,
      Category.id_comp]
    exact ψ.homologyMap_filteredMap_comp_abutmentIso J G i F

end Filtered

/-! ### The coefficient comparison is natural in the hypercovering -/

section PageTwo

/-- **The hypercovering-free factor of the coefficient comparison**: extending the inner index of
a double complex by zero from `ℕ` commutes with taking homology in the inner and then the outer
direction.  This is the factor of `hypercoverPresheafDoubleHomologyNatIso` that does not mention
the hypercovering, named so that the Čech pullback can be moved past it by naturality in the
double complex. -/
def extendInnerHomologyNatIso {A : Type*} [Category* A] [Abelian A] (p : ℕ) (r : ℤ) :
    (ComplexShape.embeddingUpNat.extendFunctor A).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex₂.homologyIIHomologyIFunctor A (p : ℤ) r ≅
      HomologicalComplex.homologyFunctor (CochainComplex A ℕ) (ComplexShape.up ℤ) r ⋙
        HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) p :=
  Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexHomologyIso
        (ComplexShape.embeddingUpNat.extendFunctor A) (ComplexShape.up ℤ) r)
      (HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) (p : ℤ)) ≪≫
    Functor.isoWhiskerLeft
      (HomologicalComplex.homologyFunctor (CochainComplex A ℕ) (ComplexShape.up ℤ) r)
      (ComplexShape.embeddingUpNat.extendFunctorHomologyIso A p (p : ℤ) rfl)

omit [HasSheafify J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}] in
/-- **The Čech pullback on `Ȟ^p(-, -)` as a morphism of functors of the coefficient presheaf**:
`cochainComplexFunctorMap` followed by homology.  `HypercoveringOf.Hom.cechCohomologyMap` is its
component at the presheaf underlying a sheaf. -/
def presheafCechCohomologyFunctorMap {K L : HypercoveringOf.{q, w} J G}
    (ψ : HypercoveringOf.Hom K L) (p : ℕ) :
    presheafCechCohomologyFunctor J G L p ⟶ presheafCechCohomologyFunctor J G K p :=
  Functor.whiskerRight (cochainComplexFunctorMap.{w} ψ.simplicialHom)
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{max (max u v) (max q w)}
      (ComplexShape.up ℕ) p)

omit [HasSheafify J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}] in
/-- The restriction map on Čech cohomology is the component of
`presheafCechCohomologyFunctorMap` at the presheaf underlying the sheaf. -/
lemma HypercoveringOf.Hom.cechCohomologyMap_eq {K L : HypercoveringOf.{q, w} J G}
    (ψ : HypercoveringOf.Hom K L)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) (p : ℕ) :
    ψ.cechCohomologyMap F p = (presheafCechCohomologyFunctorMap J G ψ p).app F.obj :=
  rfl

omit [HasSheafify J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}] in
/-- **The double complex with inner index in `ℕ` is contravariantly functorial in the
hypercovering**, the complex of sections being so degreewise.  This is
`hypercoverPresheafDoubleFunctorMap` before the inner index is extended by zero. -/
def hypercoverPresheafDoubleNatFunctorMap {K K' : HypercoveringOf.{q, w} J G}
    (ψ : K.toSimplicialObject ⟶ K'.toSimplicialObject) :
    hypercoverPresheafDoubleNatFunctor J G K' ⟶ hypercoverPresheafDoubleNatFunctor J G K :=
  NatTrans.mapHomologicalComplex
    (SemiRepresentable.sectionsComplexFunctorMap.{q, w, v, u} J.toGrothendieck ψ)
    (ComplexShape.up ℤ)

omit [HasSheafify J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}] in
/-- **The coefficient half of the second-page identification is natural in the hypercovering**,
at a complex of abelian sheaves: the Čech pullback on the double complex, read through the
comparison, is the Čech pullback on Čech cohomology.

The comparison has two factors.  The first, `extendInnerHomologyNatIso`, does not mention the
hypercovering, so the Čech pullback moves past it by naturality in the double complex.  The
second is the homology comparison of the sections complex functor of the hypercovering, and the
Čech pullback moves past that by
`CategoryTheory.Functor.mapHomologicalComplexHomologyIso_hom_app_naturality`, that comparison
being natural in the functor whose homology is compared.

The two `have`s are the exactness of the sections complex functor on presheaves, which is what
`hypercoverPresheafDoubleHomologyNatIso` is built on; `CategoryTheory.Functor.PreservesHomology`
is a proposition, so they are the instances that definition supplies for itself. -/
theorem HypercoveringOf.Hom.hypercoverPresheafDoubleHomologyNatIso_naturality
    {K L : HypercoveringOf.{q, w} J G} (ψ : HypercoveringOf.Hom K L) (p : ℕ) (r : ℤ)
    (Z : CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) ℤ) :
    (HomologicalComplex₂.homologyIIHomologyIFunctor
          AddCommGrpCat.{max (max u v) (max q w)} (p : ℤ) r).map
        ((hypercoverPresheafDoubleFunctorMap.{q, w, v, u} J G ψ.simplicialHom).app Z) ≫
        (hypercoverPresheafDoubleHomologyNatIso J G K p r).hom.app Z =
      (hypercoverPresheafDoubleHomologyNatIso J G L p r).hom.app Z ≫
        (presheafCechCohomologyFunctorMap J G ψ p).app
          ((HomologicalComplex.homologyFunctor
            (Cᵒᵖ ⥤ AddCommGrpCat.{max (max u v) (max q w)}) (ComplexShape.up ℤ) r).obj
              (((sheafToPresheaf J.toGrothendieck
                AddCommGrpCat.{max (max u v) (max q w)}).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj Z)) := by
  have := cochainComplexFunctor_preservesHomology.{w}
    (A := AddCommGrpCat.{max (max u v) (max q w)})
    (fun I => hasExactLimitsOfShape_discrete_addCommGrpCat.{max (max u v) q, w} I)
    K.toSimplicialObject
  have := cochainComplexFunctor_preservesHomology.{w}
    (A := AddCommGrpCat.{max (max u v) (max q w)})
    (fun I => hasExactLimitsOfShape_discrete_addCommGrpCat.{max (max u v) q, w} I)
    L.toSimplicialObject
  change (HomologicalComplex₂.homologyIIHomologyIFunctor
          AddCommGrpCat.{max (max u v) (max q w)} (p : ℤ) r).map
        ((hypercoverPresheafDoubleFunctorMap.{q, w, v, u} J G ψ.simplicialHom).app Z) ≫
      ((extendInnerHomologyNatIso (A := AddCommGrpCat.{max (max u v) (max q w)}) p r).hom.app
          ((hypercoverPresheafDoubleNatFunctor J G K).obj Z) ≫
        (HomologicalComplex.homologyFunctor AddCommGrpCat.{max (max u v) (max q w)}
          (ComplexShape.up ℕ) p).map
            ((Functor.mapHomologicalComplexHomologyIso
              (FormalCoproduct.cochainComplexFunctor
                (A := AddCommGrpCat.{max (max u v) (max q w)}) K.toSimplicialObject)
              (ComplexShape.up ℤ) r).hom.app
                (((sheafToPresheaf J.toGrothendieck
                  AddCommGrpCat.{max (max u v) (max q w)}).mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj Z))) =
    ((extendInnerHomologyNatIso (A := AddCommGrpCat.{max (max u v) (max q w)}) p r).hom.app
          ((hypercoverPresheafDoubleNatFunctor J G L).obj Z) ≫
        (HomologicalComplex.homologyFunctor AddCommGrpCat.{max (max u v) (max q w)}
          (ComplexShape.up ℕ) p).map
            ((Functor.mapHomologicalComplexHomologyIso
              (FormalCoproduct.cochainComplexFunctor
                (A := AddCommGrpCat.{max (max u v) (max q w)}) L.toSimplicialObject)
              (ComplexShape.up ℤ) r).hom.app
                (((sheafToPresheaf J.toGrothendieck
                  AddCommGrpCat.{max (max u v) (max q w)}).mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj Z))) ≫
      (presheafCechCohomologyFunctorMap J G ψ p).app
        ((HomologicalComplex.homologyFunctor
          (Cᵒᵖ ⥤ AddCommGrpCat.{max (max u v) (max q w)}) (ComplexShape.up ℤ) r).obj
            (((sheafToPresheaf J.toGrothendieck
              AddCommGrpCat.{max (max u v) (max q w)}).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj Z))
  have sq1 : (HomologicalComplex₂.homologyIIHomologyIFunctor
            AddCommGrpCat.{max (max u v) (max q w)} (p : ℤ) r).map
          ((hypercoverPresheafDoubleFunctorMap.{q, w, v, u} J G ψ.simplicialHom).app Z) ≫
        (extendInnerHomologyNatIso (A := AddCommGrpCat.{max (max u v) (max q w)}) p r).hom.app
          ((hypercoverPresheafDoubleNatFunctor J G K).obj Z) =
      (extendInnerHomologyNatIso (A := AddCommGrpCat.{max (max u v) (max q w)}) p r).hom.app
          ((hypercoverPresheafDoubleNatFunctor J G L).obj Z) ≫
        (HomologicalComplex.homologyFunctor AddCommGrpCat.{max (max u v) (max q w)}
          (ComplexShape.up ℕ) p).map
            (HomologicalComplex.homologyMap
              ((hypercoverPresheafDoubleNatFunctorMap.{q, w, v, u} J G
                ψ.simplicialHom).app Z) r) :=
    (extendInnerHomologyNatIso (A := AddCommGrpCat.{max (max u v) (max q w)}) p r).hom.naturality
      ((hypercoverPresheafDoubleNatFunctorMap.{q, w, v, u} J G ψ.simplicialHom).app Z)
  have sq2 : (HomologicalComplex.homologyFunctor AddCommGrpCat.{max (max u v) (max q w)}
            (ComplexShape.up ℕ) p).map
          (HomologicalComplex.homologyMap
            ((hypercoverPresheafDoubleNatFunctorMap.{q, w, v, u} J G
              ψ.simplicialHom).app Z) r) ≫
        (HomologicalComplex.homologyFunctor AddCommGrpCat.{max (max u v) (max q w)}
          (ComplexShape.up ℕ) p).map
            ((Functor.mapHomologicalComplexHomologyIso
              (FormalCoproduct.cochainComplexFunctor
                (A := AddCommGrpCat.{max (max u v) (max q w)}) K.toSimplicialObject)
              (ComplexShape.up ℤ) r).hom.app
                (((sheafToPresheaf J.toGrothendieck
                  AddCommGrpCat.{max (max u v) (max q w)}).mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj Z)) =
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{max (max u v) (max q w)}
          (ComplexShape.up ℕ) p).map
            ((Functor.mapHomologicalComplexHomologyIso
              (FormalCoproduct.cochainComplexFunctor
                (A := AddCommGrpCat.{max (max u v) (max q w)}) L.toSimplicialObject)
              (ComplexShape.up ℤ) r).hom.app
                (((sheafToPresheaf J.toGrothendieck
                  AddCommGrpCat.{max (max u v) (max q w)}).mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj Z)) ≫
        (presheafCechCohomologyFunctorMap J G ψ p).app
          ((HomologicalComplex.homologyFunctor
            (Cᵒᵖ ⥤ AddCommGrpCat.{max (max u v) (max q w)}) (ComplexShape.up ℤ) r).obj
              (((sheafToPresheaf J.toGrothendieck
                AddCommGrpCat.{max (max u v) (max q w)}).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj Z)) :=
    (((HomologicalComplex.homologyFunctor AddCommGrpCat.{max (max u v) (max q w)}
          (ComplexShape.up ℕ) p).map_comp _ _).symm.trans
      (congrArg (HomologicalComplex.homologyFunctor AddCommGrpCat.{max (max u v) (max q w)}
          (ComplexShape.up ℕ) p).map
        (CategoryTheory.Functor.mapHomologicalComplexHomologyIso_hom_app_naturality
          (cochainComplexFunctorMap.{w} ψ.simplicialHom) (ComplexShape.up ℤ) r
          (((sheafToPresheaf J.toGrothendieck
            AddCommGrpCat.{max (max u v) (max q w)}).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj Z)))).trans
      ((HomologicalComplex.homologyFunctor AddCommGrpCat.{max (max u v) (max q w)}
        (ComplexShape.up ℕ) p).map_comp _ _)
  exact (CommSq.vert_comp ⟨sq1⟩ ⟨sq2⟩).w

variable [EnoughInjectives (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)})]

omit [EnoughInjectives (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)})] in
/-- **The coefficient comparison at an `ℕ`-indexed complex is natural in the hypercovering.**
`HypercoveringOf.Hom.hypercoverPresheafDoubleHomologyNatIso_naturality` at the extension of the
complex, followed by the naturality of the Čech pullback in the coefficient presheaf, which moves
it past the degree comparison `extendUpNatMapHomologyNatIso`. -/
theorem HypercoveringOf.Hom.hypercoverPresheafResolutionCoefficientNatIso_naturality
    {K L : HypercoveringOf.{q, w} J G} (ψ : HypercoveringOf.Hom K L) (p q' : ℕ)
    (Y : CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) ℕ) :
    (HomologicalComplex₂.homologyIIHomologyIFunctor
          AddCommGrpCat.{max (max u v) (max q w)} (p : ℤ) (q' : ℤ)).map
        ((hypercoverPresheafDoubleFunctorMap.{q, w, v, u} J G ψ.simplicialHom).app
          ((ComplexShape.embeddingUpNat.extendFunctor
            (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)})).obj Y)) ≫
        (hypercoverPresheafResolutionCoefficientNatIso J G K p q').hom.app Y =
      (hypercoverPresheafResolutionCoefficientNatIso J G L p q').hom.app Y ≫
        (presheafCechCohomologyFunctorMap J G ψ p).app
          ((HomologicalComplex.homologyFunctor
            (Cᵒᵖ ⥤ AddCommGrpCat.{max (max u v) (max q w)}) (ComplexShape.up ℕ) q').obj
              (((sheafToPresheaf J.toGrothendieck
                AddCommGrpCat.{max (max u v) (max q w)}).mapHomologicalComplex
                  (ComplexShape.up ℕ)).obj Y)) := by
  change (HomologicalComplex₂.homologyIIHomologyIFunctor
          AddCommGrpCat.{max (max u v) (max q w)} (p : ℤ) (q' : ℤ)).map
        ((hypercoverPresheafDoubleFunctorMap.{q, w, v, u} J G ψ.simplicialHom).app
          ((ComplexShape.embeddingUpNat.extendFunctor
            (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)})).obj Y)) ≫
      ((hypercoverPresheafDoubleHomologyNatIso J G K p (q' : ℤ)).hom.app
          ((ComplexShape.embeddingUpNat.extendFunctor
            (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)})).obj Y) ≫
        (presheafCechCohomologyFunctor J G K p).map
          ((extendUpNatMapHomologyNatIso (sheafToPresheaf J.toGrothendieck
            AddCommGrpCat.{max (max u v) (max q w)}) q').hom.app Y)) =
    ((hypercoverPresheafDoubleHomologyNatIso J G L p (q' : ℤ)).hom.app
          ((ComplexShape.embeddingUpNat.extendFunctor
            (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)})).obj Y) ≫
        (presheafCechCohomologyFunctor J G L p).map
          ((extendUpNatMapHomologyNatIso (sheafToPresheaf J.toGrothendieck
            AddCommGrpCat.{max (max u v) (max q w)}) q').hom.app Y)) ≫
      (presheafCechCohomologyFunctorMap J G ψ p).app
        ((HomologicalComplex.homologyFunctor
          (Cᵒᵖ ⥤ AddCommGrpCat.{max (max u v) (max q w)}) (ComplexShape.up ℕ) q').obj
            (((sheafToPresheaf J.toGrothendieck
              AddCommGrpCat.{max (max u v) (max q w)}).mapHomologicalComplex
                (ComplexShape.up ℕ)).obj Y))
  exact (CommSq.vert_comp
    ⟨ψ.hypercoverPresheafDoubleHomologyNatIso_naturality J G p (q' : ℤ)
      ((ComplexShape.embeddingUpNat.extendFunctor
        (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)})).obj Y)⟩
    ⟨((presheafCechCohomologyFunctorMap J G ψ p).naturality
      ((extendUpNatMapHomologyNatIso (sheafToPresheaf J.toGrothendieck
        AddCommGrpCat.{max (max u v) (max q w)}) q').hom.app Y)).symm⟩).w

/-- **The coefficient comparison `H^p_{II}(H^{q'}_I(A^{•,•}(F))) ≅ Ȟ^p(K, H̲^{q'}(F))` is natural
in the hypercovering.**
`HypercoveringOf.Hom.hypercoverPresheafResolutionCoefficientNatIso_naturality` at the chosen
injective resolution of `F`, followed by the naturality of the Čech pullback at the comparison of
that resolution with the right derived functor. -/
theorem HypercoveringOf.Hom.hypercoverPresheafCoefficientIso_naturality
    {K L : HypercoveringOf.{q, w} J G} (ψ : HypercoveringOf.Hom K L) (p q' : ℕ)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) :
    (HomologicalComplex₂.homologyIIHomologyIFunctor
          AddCommGrpCat.{max (max u v) (max q w)} (p : ℤ) (q' : ℤ)).map
        (ψ.doubleMap J G F) ≫
        (hypercoverPresheafCoefficientIso J G K p q' F).hom =
      (hypercoverPresheafCoefficientIso J G L p q' F).hom ≫
        (presheafCechCohomologyFunctorMap J G ψ p).app
          (((sheafToPresheaf J.toGrothendieck
            AddCommGrpCat.{max (max u v) (max q w)}).rightDerived q').obj F) := by
  change (HomologicalComplex₂.homologyIIHomologyIFunctor
          AddCommGrpCat.{max (max u v) (max q w)} (p : ℤ) (q' : ℤ)).map
        ((hypercoverPresheafDoubleFunctorMap.{q, w, v, u} J G ψ.simplicialHom).app
          ((ComplexShape.embeddingUpNat.extendFunctor
            (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)})).obj
              (injectiveResolution F).cocomplex)) ≫
      ((hypercoverPresheafResolutionCoefficientNatIso J G K p q').hom.app
          (injectiveResolution F).cocomplex ≫
        (presheafCechCohomologyFunctor J G K p).map
          ((injectiveResolution F).isoRightDerivedObj (sheafToPresheaf J.toGrothendieck
            AddCommGrpCat.{max (max u v) (max q w)}) q').inv) =
    ((hypercoverPresheafResolutionCoefficientNatIso J G L p q').hom.app
          (injectiveResolution F).cocomplex ≫
        (presheafCechCohomologyFunctor J G L p).map
          ((injectiveResolution F).isoRightDerivedObj (sheafToPresheaf J.toGrothendieck
            AddCommGrpCat.{max (max u v) (max q w)}) q').inv) ≫
      (presheafCechCohomologyFunctorMap J G ψ p).app
        (((sheafToPresheaf J.toGrothendieck
          AddCommGrpCat.{max (max u v) (max q w)}).rightDerived q').obj F)
  exact (CommSq.vert_comp
    ⟨ψ.hypercoverPresheafResolutionCoefficientNatIso_naturality J G p q'
      (injectiveResolution F).cocomplex⟩
    ⟨((presheafCechCohomologyFunctorMap J G ψ p).naturality
      ((injectiveResolution F).isoRightDerivedObj (sheafToPresheaf J.toGrothendieck
        AddCommGrpCat.{max (max u v) (max q w)}) q').inv).symm⟩).w

/-- **[Stacks, Tag 0130] (6) is natural in the hypercovering**: the Čech pullback on the second
page at `((p : ℤ), (q' : ℤ))` is the Čech pullback on `H^p_{II}(H^{q'}_I(A^{•,•}(F)))`.  This is
`HomologicalComplex₂.isoTwoPageTotalFiltration₂_naturality_functor`, which already accepts an
arbitrary morphism of double complexes, at `HypercoveringOf.Hom.doubleMap`. -/
theorem HypercoveringOf.Hom.hypercoverPresheafPageTwoAppIso_naturality
    {K L : HypercoveringOf.{q, w} J G} (ψ : HypercoveringOf.Hom K L) (p q' : ℕ)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) :
    (((hypercoverPresheafSpectralSequenceFunctorMap.{q, w, v, u} J G
            ψ.simplicialHom).app F).hom 2).f (p, q') ≫
        (hypercoverPresheafPageTwoAppIso J G K p q' F).hom =
      (hypercoverPresheafPageTwoAppIso J G L p q' F).hom ≫
        (HomologicalComplex₂.homologyIIHomologyIFunctor
          AddCommGrpCat.{max (max u v) (max q w)} (p : ℤ) (q' : ℤ)).map (ψ.doubleMap J G F) :=
  HomologicalComplex₂.isoTwoPageTotalFiltration₂_naturality_functor (ψ.doubleMap J G F)
    (p : ℤ) (q' : ℤ)

/-- **The second page of [Stacks, Tag 09VX] is `Ȟ^p(K, H̲^{q'}(F))` naturally in the
hypercovering**: the Čech pullback on the second page at `(p, q')` is the Čech pullback on Čech
cohomology.  The two squares above, pasted; the passage from `ℤ × ℤ` to `ℕ × ℕ` contributes an
identity. -/
theorem HypercoveringOf.Hom.hypercoverPresheafPageTwoIso_naturality
    {K L : HypercoveringOf.{q, w} J G} (ψ : HypercoveringOf.Hom K L) (p q' : ℕ)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) :
    (((hypercoverPresheafSpectralSequenceFunctorMap.{q, w, v, u} J G
            ψ.simplicialHom).app F).hom 2).f (p, q') ≫
        (hypercoverPresheafPageTwoIso J G K p q').hom.app F =
      (hypercoverPresheafPageTwoIso J G L p q').hom.app F ≫
        (presheafCechCohomologyFunctorMap J G ψ p).app
          (((sheafToPresheaf J.toGrothendieck
            AddCommGrpCat.{max (max u v) (max q w)}).rightDerived q').obj F) := by
  change (((hypercoverPresheafSpectralSequenceFunctorMap.{q, w, v, u} J G
            ψ.simplicialHom).app F).hom 2).f (p, q') ≫
      (𝟙 _ ≫ ((hypercoverPresheafPageTwoAppIso J G K p q' F).hom ≫
        (hypercoverPresheafCoefficientIso J G K p q' F).hom)) =
    (𝟙 _ ≫ ((hypercoverPresheafPageTwoAppIso J G L p q' F).hom ≫
        (hypercoverPresheafCoefficientIso J G L p q' F).hom)) ≫
      (presheafCechCohomologyFunctorMap J G ψ p).app
        (((sheafToPresheaf J.toGrothendieck
          AddCommGrpCat.{max (max u v) (max q w)}).rightDerived q').obj F)
  refine (congrArg (fun t ↦ _ ≫ t) (Category.id_comp _)).trans
    (Eq.trans ?_ (congrArg (fun t ↦ t ≫ _) (Category.id_comp _).symm))
  exact (CommSq.vert_comp ⟨ψ.hypercoverPresheafPageTwoAppIso_naturality J G p q' F⟩
    ⟨ψ.hypercoverPresheafCoefficientIso_naturality J G p q' F⟩).w

end PageTwo

/-! ### The global edge map forms a cocone on the hypercoverings of the final presheaf -/

section Global

variable {C : Type u} [Category.{v} C] [HasEqualizers C] [HasPullbacks C]
variable (J : Pretopology C)
  [HasSheafify J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)}]
  [EnoughInjectives (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)})]
  [HasExt.{max (max u v) (max v w)}
    (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)})]

/-- **The identification of the abutment of [Stacks, Tag 09VY] with global cohomology does not
move with the hypercovering.**  It is built out of the sections over the final presheaf, which
mention no hypercovering: the augmented simplicial presheaf of a hypercovering of `G` has
`liftedPresheaf G` at the augmentation points. -/
lemma globalCohomologyAbutmentIso_eq (K L : HypercoveringOfTerminal.{w} J) (n : ℕ) :
    globalCohomologyAbutmentIso J L n = globalCohomologyAbutmentIso J K n :=
  rfl

/-- **The functorial filtered abutment of [Stacks, Tag 09VY]**, named: the abutment of
[Stacks, Tag 09VX] at the final presheaf, transported along `globalCohomologyAbutmentIso`.  It is
the `abutment` field of `hypercoveringGlobalSpectralSequence`, spelled so that
`Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo.bottomRowEdge_ofIsoAbutment` applies to it
without the spectral sequence data having to be unfolded. -/
abbrev globalAbutment (K : HypercoveringOfTerminal.{w} J) :
    Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo
      (hypercoverPresheafSpectralSequenceFunctor J (⊤_ (Cᵒᵖ ⥤ Type v)) K)
      (fun n ↦ globalCohomologyFunctor.{w} J n) :=
  (hypercoverPresheafAbutment J (⊤_ (Cᵒᵖ ⥤ Type v)) K).ofIsoAbutment
    (globalCohomologyAbutmentIso J K)

/-- `globalAbutment` is the `abutment` field of `hypercoveringGlobalSpectralSequence`. -/
lemma hypercoveringGlobalSpectralSequence_abutment (K : HypercoveringOfTerminal.{w} J) :
    (hypercoveringGlobalSpectralSequence J K).abutment = globalAbutment J K :=
  rfl

/-- **The bottom-row edge map of [Stacks, Tag 09VY] is the bottom-row edge map of
[Stacks, Tag 09VX] followed by the identification of the sections over the final presheaf with
global cohomology**, the abutment of the former being the abutment of the latter transported along
that identification. -/
lemma globalBottomRowEdge_eq (K : HypercoveringOfTerminal.{w} J) (i : ℕ) :
    (globalAbutment J K).bottomRowEdge i =
      (hypercoverPresheafAbutment J (⊤_ (Cᵒᵖ ⥤ Type v)) K).bottomRowEdge i ≫
        (globalCohomologyAbutmentIso J K i).hom :=
  Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo.bottomRowEdge_ofIsoAbutment
    (hypercoverPresheafAbutment J (⊤_ (Cᵒᵖ ⥤ Type v)) K) (globalCohomologyAbutmentIso J K) i

/-- `globalBottomRowEdge_eq` at a sheaf. -/
lemma globalBottomRowEdge_app (K : HypercoveringOfTerminal.{w} J) (i : ℕ)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)}) :
    ((globalAbutment J K).bottomRowEdge i).app F =
      ((hypercoverPresheafAbutment J (⊤_ (Cᵒᵖ ⥤ Type v)) K).bottomRowEdge i).app F ≫
        (globalCohomologyAbutmentIso J K i).hom.app F :=
  (congrArg (fun t ↦ NatTrans.app t F) (globalBottomRowEdge_eq J K i)).trans
    (NatTrans.comp_app _ _ F)

/-- **The bottom-row edge map of [Stacks, Tag 09VY] forms a cocone on the hypercoverings of the
final presheaf**: the Čech pullback along `ψ : K ⟶ L` on the second page at `(i, 0)` followed by
the edge map of `K` is the edge map of `L`.

`HypercoveringOf.Hom.spectralSequenceFunctorMap_comp_bottomRowEdge` for the spectral sequence of
[Stacks, Tag 09VX] at the final presheaf, followed by `globalCohomologyAbutmentIso_eq`: the
identification of the abutment with global cohomology does not move with the hypercovering. -/
theorem HypercoveringOf.Hom.globalBottomRowEdge_comp
    {K L : HypercoveringOfTerminal.{w} J} (ψ : HypercoveringOf.Hom K L) (i : ℕ)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)}) :
    (((hypercoverPresheafSpectralSequenceFunctorMap.{v, w, v, u} J (⊤_ (Cᵒᵖ ⥤ Type v))
            ψ.simplicialHom).app F).hom 2).f (i, 0) ≫
        ((globalAbutment J K).bottomRowEdge i).app F =
      ((globalAbutment J L).bottomRowEdge i).app F := by
  have hG : (globalCohomologyAbutmentIso J K i).hom.app F =
      (globalCohomologyAbutmentIso J L i).hom.app F :=
    congrArg (fun t ↦ NatTrans.app t F)
      (congrArg Iso.hom (globalCohomologyAbutmentIso_eq J L K i))
  exact (_ ≫= globalBottomRowEdge_app J K i F).trans
    ((Category.assoc _ _ _).symm.trans
      ((ψ.spectralSequenceFunctorMap_comp_bottomRowEdge J (⊤_ (Cᵒᵖ ⥤ Type v)) i F =≫ _).trans
        ((_ ≫= hG).trans (globalBottomRowEdge_app J L i F).symm)))

/-- The value of the global edge map of [Stacks, Tag 09VY] at a sheaf, as the composite of its
three factors: the degree-zero coefficient identification, the second-page identification and the
bottom-row edge map of the abutment. -/
lemma globalCechEdge_app_aux (K : HypercoveringOfTerminal.{w} J) (i : ℕ)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)}) :
    (globalCechEdge.{w} J K i).app F =
      ((presheafCechCohomologyFunctor J (⊤_ (Cᵒᵖ ⥤ Type v)) K i).map
        ((sheafToPresheaf J.toGrothendieck
          AddCommGrpCat.{max (max u v) (max v w)}).rightDerivedZeroIsoSelf.inv.app F)) ≫
        (((hypercoveringGlobalSpectralSequence J K).pageTwoIso i 0).inv.app F ≫
          ((hypercoveringGlobalSpectralSequence J K).abutment.bottomRowEdge i).app F) :=
  rfl

/-- The second-page identification of [Stacks, Tag 09VY] is the one of [Stacks, Tag 09VX] at the
final presheaf, read at a sheaf. -/
lemma globalPageTwoIso_inv_app (K : HypercoveringOfTerminal.{w} J) (p q' : ℕ)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)}) :
    ((hypercoveringGlobalSpectralSequence J K).pageTwoIso p q').inv.app F =
      ((hypercoverPresheafPageTwoIso J (⊤_ (Cᵒᵖ ⥤ Type v)) K p q').app F).inv :=
  rfl

/-- The bottom-row edge map of the abutment of [Stacks, Tag 09VY] is the one of
`globalAbutment`, read at a sheaf. -/
lemma globalAbutmentEdge_app (K : HypercoveringOfTerminal.{w} J) (i : ℕ)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)}) :
    ((hypercoveringGlobalSpectralSequence J K).abutment.bottomRowEdge i).app F =
      ((globalAbutment J K).bottomRowEdge i).app F :=
  congrArg (fun h' ↦ NatTrans.app
      (Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo.bottomRowEdge h' i) F)
    (hypercoveringGlobalSpectralSequence_abutment J K)

/-- `globalCechEdge_app_aux` with the two identifications rewritten into the spelling the squares
of `globalCechEdge_square` use. -/
lemma globalCechEdge_app (K : HypercoveringOfTerminal.{w} J) (i : ℕ)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)}) :
    (globalCechEdge.{w} J K i).app F =
      ((presheafCechCohomologyFunctor J (⊤_ (Cᵒᵖ ⥤ Type v)) K i).map
        ((sheafToPresheaf J.toGrothendieck
          AddCommGrpCat.{max (max u v) (max v w)}).rightDerivedZeroIsoSelf.inv.app F)) ≫
        ((((hypercoverPresheafPageTwoIso J (⊤_ (Cᵒᵖ ⥤ Type v)) K i 0).app F).inv) ≫
          (((globalAbutment J K).bottomRowEdge i).app F)) :=
  (globalCechEdge_app_aux J K i F).trans
    (_ ≫= ((globalPageTwoIso_inv_app J K i 0 F) =≫ _).trans
      (_ ≫= globalAbutmentEdge_app J K i F))

/-- **The three squares that make the global edge map a cocone, pasted.**  Stated in the spelling
the squares themselves use, so that `HypercoveringOf.Hom.globalCechEdge_comp_cechCohomologyMap`
only has to recognise the global edge map in it. -/
lemma globalCechEdge_square {K L : HypercoveringOfTerminal.{w} J}
    (ψ : HypercoveringOf.Hom K L) (i : ℕ)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)}) :
    ((presheafCechCohomologyFunctorMap J (⊤_ (Cᵒᵖ ⥤ Type v)) ψ i).app F.obj) ≫
        (((presheafCechCohomologyFunctor J (⊤_ (Cᵒᵖ ⥤ Type v)) K i).map
        ((sheafToPresheaf J.toGrothendieck
          AddCommGrpCat.{max (max u v) (max v w)}).rightDerivedZeroIsoSelf.inv.app F)) ≫
          ((((hypercoverPresheafPageTwoIso J (⊤_ (Cᵒᵖ ⥤ Type v)) K i 0).app F).inv) ≫
            (((globalAbutment J K).bottomRowEdge i).app F))) =
      ((presheafCechCohomologyFunctor J (⊤_ (Cᵒᵖ ⥤ Type v)) L i).map
        ((sheafToPresheaf J.toGrothendieck
          AddCommGrpCat.{max (max u v) (max v w)}).rightDerivedZeroIsoSelf.inv.app F)) ≫
        ((((hypercoverPresheafPageTwoIso J (⊤_ (Cᵒᵖ ⥤ Type v)) L i 0).app F).inv) ≫
          (((globalAbutment J L).bottomRowEdge i).app F)) := by
  have hA : (presheafCechCohomologyFunctorMap J (⊤_ (Cᵒᵖ ⥤ Type v)) ψ i).app F.obj ≫ _ = _ :=
    ((presheafCechCohomologyFunctorMap J (⊤_ (Cᵒᵖ ⥤ Type v)) ψ i).naturality
      ((sheafToPresheaf J.toGrothendieck
        AddCommGrpCat.{max (max u v) (max v w)}).rightDerivedZeroIsoSelf.inv.app F)).symm
  have hB := (StacksDraft.DerivedSectionsComparison.inv_comp_eq_comp_inv
    ((hypercoverPresheafPageTwoIso J (⊤_ (Cᵒᵖ ⥤ Type v)) L i 0).app F)
    ((hypercoverPresheafPageTwoIso J (⊤_ (Cᵒᵖ ⥤ Type v)) K i 0).app F)
    ((((hypercoverPresheafSpectralSequenceFunctorMap.{v, w, v, u} J (⊤_ (Cᵒᵖ ⥤ Type v))
        ψ.simplicialHom).app F).hom 2).f (i, 0))
    ((presheafCechCohomologyFunctorMap J (⊤_ (Cᵒᵖ ⥤ Type v)) ψ i).app
        (((sheafToPresheaf J.toGrothendieck
          AddCommGrpCat.{max (max u v) (max v w)}).rightDerived 0).obj F))
    (ψ.hypercoverPresheafPageTwoIso_naturality J (⊤_ (Cᵒᵖ ⥤ Type v)) i 0 F)).symm
  rw [← Category.assoc, hA, Category.assoc, reassoc_of% hB,
    ← ψ.globalBottomRowEdge_comp J i F]
  exact _ ≫= Category.assoc _ _ _

/-- **The global edge map `Ȟ^i(K, 𝓕) ⟶ H^i(𝓕)` of [Stacks, Tag 09VY] forms a cocone on the
hypercoverings of the final presheaf, in every degree**: a morphism of hypercoverings
`ψ : K ⟶ L` induces the restriction map `Ȟ^i(L, 𝓕) ⟶ Ȟ^i(K, 𝓕)`, and following it by the edge map
of `K` gives back the edge map of `L`.

This is the cocone identity that the comparison of [Stacks, Tag 09VZ] needs in general degree,
with coefficients in the sheaf itself, and nothing about it is assumed.  Its three factors move
past the Čech pullback in turn: the degree-zero coefficient identification by the naturality of
the Čech pullback in the coefficient presheaf, the second-page identification by
`HypercoveringOf.Hom.hypercoverPresheafPageTwoIso_naturality`, and the edge map by
`HypercoveringOf.Hom.globalBottomRowEdge_comp`. -/
theorem HypercoveringOf.Hom.globalCechEdge_comp_cechCohomologyMap
    {K L : HypercoveringOfTerminal.{w} J} (ψ : HypercoveringOf.Hom K L) (i : ℕ)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)}) :
    ψ.cechCohomologyMap F i ≫ (globalCechEdge.{w} J K i).app F =
      (globalCechEdge.{w} J L i).app F := by
  rw [globalCechEdge_app J K i F, globalCechEdge_app J L i F]
  exact globalCechEdge_square J ψ i F

/-! ### [Stacks, Tag 09VZ] in degree zero, for the canonical edge map -/

/-- **In degree zero the global edge map `Ȟ⁰(K, 𝓕) ⟶ H⁰(𝓕)` of [Stacks, Tag 09VY] is an
isomorphism.**  Its three factors are: the identification of the degree-zero coefficients, an
isomorphism because `rightDerivedZeroIsoSelf` is one; the second-page identification; and the
bottom-row edge map of the spectral sequence, which in degree zero is an isomorphism because the
corner of a first-quadrant spectral sequence is already the whole abutment
(`Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo.isIso_bottomRowEdge_zero_app`). -/
lemma isIso_globalCechEdge_zero_app (K : HypercoveringOfTerminal.{w} J)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)}) :
    IsIso ((globalCechEdge.{w} J K 0).app F) := by
  have h₁ : IsIso ((presheafCechCohomologyFunctor J (⊤_ (Cᵒᵖ ⥤ Type v)) K 0).map
      ((sheafToPresheaf J.toGrothendieck
        AddCommGrpCat.{max (max u v) (max v w)}).rightDerivedZeroIsoSelf.inv.app F)) :=
    inferInstance
  have h₂ : IsIso (((hypercoverPresheafPageTwoIso J (⊤_ (Cᵒᵖ ⥤ Type v)) K 0 0).app F).inv) :=
    inferInstance
  have h₃ := Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo.isIso_bottomRowEdge_zero_app
    (globalAbutment J K) F
  rw [globalCechEdge_app J K 0 F]
  exact IsIso.comp_isIso' h₁ (IsIso.comp_isIso' h₂ h₃)

/-- **The canonical comparison `Ȟ^i(K, 𝓕) ⟶ H^i(𝓕)` of [Stacks, Tag 09VY]**, with its source
written as the Čech cohomology group `cechCohomology` rather than as a value of the functor
`presheafCechCohomologyFunctor` that `globalCechEdge` is a morphism out of.  It is
`globalCechEdge` at `𝓕`, and nothing more.

The two spellings of the source are definitionally equal -- that is
`presheafCechCohomologyFunctor_obj` -- but only after `presheafCechCohomologyFunctor`,
`Functor.comp` and `HomologicalComplex.homologyFunctor` have been unfolded, and that unfolding is
expensive enough that a handful of element-level statements mixing the two exhausts the
elaborator's heartbeats.  This definition, and the two lemmas after it, pay for the
identification once each; everything downstream is then written in the `cechCohomology` spelling
alone, where the Čech pullback `HypercoveringOf.Hom.cechCohomologyMap` also lives, and costs
nothing. -/
def cechCohomologyEdge (K : HypercoveringOfTerminal.{w} J) (i : ℕ)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)}) :
    cechCohomology J (⊤_ (Cᵒᵖ ⥤ Type v)) K F i ⟶ (globalCohomologyFunctor.{w} J i).obj F :=
  (globalCechEdge.{w} J K i).app F

/-- **The canonical comparison of [Stacks, Tag 09VY] forms a cocone on the hypercoverings of the
final presheaf, in every degree**, in the `cechCohomology` spelling:
`HypercoveringOf.Hom.globalCechEdge_comp_cechCohomologyMap` read through
`cechCohomologyEdge`. -/
lemma cechCohomologyMap_comp_cechCohomologyEdge {K L : HypercoveringOfTerminal.{w} J}
    (ψ : HypercoveringOf.Hom K L) (i : ℕ)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)}) :
    ψ.cechCohomologyMap F i ≫ cechCohomologyEdge.{w} J K i F =
      cechCohomologyEdge.{w} J L i F :=
  HypercoveringOf.Hom.globalCechEdge_comp_cechCohomologyMap J ψ i F

/-- **In degree zero the canonical comparison of [Stacks, Tag 09VY] is an isomorphism**, in the
`cechCohomology` spelling: `isIso_globalCechEdge_zero_app` read through `cechCohomologyEdge`. -/
lemma isIso_cechCohomologyEdge_zero (K : HypercoveringOfTerminal.{w} J)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)}) :
    IsIso (cechCohomologyEdge.{w} J K 0 F) :=
  isIso_globalCechEdge_zero_app J K F

/-- **Stacks Project, Tag 09VZ, part (1), in degree zero.**  Every degree-zero cohomology class of
an abelian sheaf is the image, under the canonical comparison `Ȟ⁰(K, 𝓕) ⟶ H⁰(𝓕)` of
[Stacks, Tag 09VY], of a degree-zero Čech class on some hypercovering `K` of the final presheaf.

A hypercovering exists by [Stacks, Tag 0DAX] applied to the identity coverings, and in degree
zero the comparison is an isomorphism, `isIso_cechCohomologyEdge_zero`. -/
@[stacks 09VZ "part (1) in degree i = 0, universe-general: the hypercoverings are at a free \
universe `w`, which is what keeps this statement from being subsumed by \
`exists_hypercoveringOfTerminal_cechCohomologyEdge_eq`, which has every degree but is at \
`max u v w` because Tag 01GJ forces it; the canonical map is the bottom-row edge map of the \
spectral sequence of Tag 09VY, i.e. the comparison of Tag 01GY"]
theorem exists_hypercoveringOfTerminal_cechCohomologyEdge_zero_eq
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)})
    (ξ : (globalCohomologyFunctor.{max u v w} J 0).obj F) :
    ∃ (K : HypercoveringOfTerminal.{max u v w} J)
      (ξK : cechCohomology J (⊤_ (Cᵒᵖ ⥤ Type v)) K F 0),
      ConcreteCategory.hom (cechCohomologyEdge.{max u v w} J K 0 F) ξK = ξ := by
  obtain ⟨K, -⟩ :=
    exists_hypercoveringOfTerminal_with_objects_in.{max u v w} J Set.univ fun U ↦
      ⟨PUnit.{max u v w + 1}, fun _ ↦ U, fun _ ↦ 𝟙 U, fun _ ↦ Set.mem_univ _,
        mem_coverings_ofArrows_id J U⟩
  have := isIso_cechCohomologyEdge_zero.{max u v w} J K F
  obtain ⟨ξK, hξK⟩ :=
    exists_hom_apply_eq_of_isIso (cechCohomologyEdge.{max u v w} J K 0 F) ξ
  exact ⟨K, ξK, hξK⟩

/-- **Two degree-zero Čech classes with the same image under the comparison of [Stacks, Tag 09VY]
agree on any common refinement.**  Both restrictions have the same image on the refinement `M`,
because the comparison is natural in the hypercovering
(`cechCohomologyMap_comp_cechCohomologyEdge`), and in degree zero the comparison on `M` is
injective (`isIso_cechCohomologyEdge_zero`).

This is the element-level half of part (2) of [Stacks, Tag 09VZ], split off from the choice of
refinement so that neither declaration exhausts the elaborator's heartbeats, as the
implementation notes of this file describe. -/
lemma cechCohomologyMap_apply_eq_of_cechCohomologyEdge_apply_eq
    {K L M : HypercoveringOfTerminal.{w} J} (f : M.Hom K) (g : M.Hom L)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)})
    (ξK : cechCohomology J (⊤_ (Cᵒᵖ ⥤ Type v)) K F 0)
    (ξL : cechCohomology J (⊤_ (Cᵒᵖ ⥤ Type v)) L F 0)
    (h : ConcreteCategory.hom (cechCohomologyEdge.{w} J K 0 F) ξK =
      ConcreteCategory.hom (cechCohomologyEdge.{w} J L 0 F) ξL) :
    ConcreteCategory.hom (f.cechCohomologyMap F 0) ξK =
      ConcreteCategory.hom (g.cechCohomologyMap F 0) ξL := by
  have := isIso_cechCohomologyEdge_zero.{w} J M F
  exact hom_apply_eq_of_comp_eq_of_isIso (cechCohomologyEdge.{w} J M 0 F)
    (cechCohomologyMap_comp_cechCohomologyEdge J f 0 F)
    (cechCohomologyMap_comp_cechCohomologyEdge J g 0 F) h

/-- **Stacks Project, Tag 09VZ, part (2), in degree zero.**  Two degree-zero Čech classes on
hypercoverings `K` and `L` of the final presheaf whose images under the canonical comparison
`Ȟ⁰(-, 𝓕) ⟶ H⁰(𝓕)` of [Stacks, Tag 09VY] agree restrict to the same class on a common
refinement.

Nothing is assumed beyond the source's hypotheses.  The common refinement is the degreewise
product, `exists_hom_of_prod`, which is what products of pairs in `C` are assumed for; that the
two restrictions then agree is
`cechCohomologyMap_apply_eq_of_cechCohomologyEdge_apply_eq`, which rests on the naturality of the
comparison in the hypercovering, `HypercoveringOf.Hom.globalCechEdge_comp_cechCohomologyMap`. -/
@[stacks 09VZ "part (2) in degree i = 0, universe-general: the hypercoverings are at a free \
universe `w`, which is what keeps this statement from being subsumed by \
`exists_hom_cechCohomologyEdge_eq`, the same part (2) in every degree but with the \
hypercoverings at `max u v w`, the universe Tag 01GJ forces.  The canonical map is the \
bottom-row edge map of the spectral sequence of Tag 09VY, i.e. the comparison of Tag 01GY, and \
its naturality in the hypercovering is proved, not assumed"]
theorem exists_hom_cechCohomologyEdge_zero_eq [HasBinaryProducts C]
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)})
    (K L : HypercoveringOfTerminal.{w} J)
    (ξK : cechCohomology J (⊤_ (Cᵒᵖ ⥤ Type v)) K F 0)
    (ξL : cechCohomology J (⊤_ (Cᵒᵖ ⥤ Type v)) L F 0)
    (h : ConcreteCategory.hom (cechCohomologyEdge.{w} J K 0 F) ξK =
      ConcreteCategory.hom (cechCohomologyEdge.{w} J L 0 F) ξL) :
    ∃ (M : HypercoveringOfTerminal.{w} J) (f : M.Hom K) (g : M.Hom L),
      ConcreteCategory.hom (f.cechCohomologyMap F 0) ξK =
        ConcreteCategory.hom (g.cechCohomologyMap F 0) ξL := by
  obtain ⟨M, ⟨f⟩, ⟨g⟩⟩ := exists_hom_of_prod J K L
  exact ⟨M, f, g,
    cechCohomologyMap_apply_eq_of_cechCohomologyEdge_apply_eq J f g F ξK ξL h⟩

end Global

end Stacks.CategoryTheory.Hypercovering

end
