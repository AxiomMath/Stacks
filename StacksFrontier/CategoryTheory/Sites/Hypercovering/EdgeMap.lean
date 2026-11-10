module

public import StacksFrontier.Algebra.Homology.SpectralSequence.EdgeEpiNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaSections
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.GlobalCohomologySpectralSequence
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.SpectralSequenceAbutmentIsCohomology
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.SpectralSequenceSecondPage

/-!
# The edge map `Ȟ^i(K, 𝓕) ⟶ H^i(X, 𝓕)` of the hypercovering spectral sequence

Clause (3) of [Stacks, Tag 01GY] gives, for a hypercovering `K` of an object `X` of a site with
fibre products, a first-quadrant spectral sequence `E₂^{p,q} = Ȟ^p(K, H^q(𝓕)) ⇒ H^{p+q}(X, 𝓕)`.
Its bottom row carries, in **every** degree `i`, a canonical map

```
Ȟ^i(K, 𝓕) = E₂^{i,0} ⟶ E_∞^{i,0} ≅ gr^i H^i(X, 𝓕) = F^i H^i(X, 𝓕) ⊆ H^i(X, 𝓕),
```

the *edge map*: the edge epimorphism onto the infinity page, the abutment's graded
identification, the identification of `gr^i H^i` with `F^i H^i` (the `(i+1)`-st filtration step
of `H^i` being zero in a first-quadrant spectral sequence) and the inclusion of that filtration
step. It is the comparison whose colimit over all hypercoverings [Stacks, Tag 01H0] asserts to
be an isomorphism, and its global analogue is the comparison of [Stacks, Tag 09VZ].

In degree zero all three middle maps are isomorphisms -- there is no differential into or out of
`(0, 0)`, and `F^0 H^0 = H^0`. In general degree the first map is only an epimorphism and the
last only a monomorphism, so the edge map is a morphism and not an isomorphism; that it becomes an
isomorphism in the colimit over hypercoverings is the content of [Stacks, Tag 01H0] and is not
proved here.

## The coefficients

The second page of the spectral sequence is `Ȟ^p(K, H^q(𝓕))`, with coefficients in the
degree-`q` *cohomology presheaf* of `𝓕`. On the bottom row `q = 0` that presheaf is the presheaf
of sections of `𝓕` itself (`Stacks.Cohomology.FreeYoneda.cohomologyPresheafIsoSections`), so the
source of the edge map is the Čech cohomology of `K` with coefficients in `𝓕`, which is what
[Stacks, Tag 01H0] and [Stacks, Tag 09VZ] are about. `cohomologyPresheafFunctorZeroIso` makes
that objectwise isomorphism natural in the sheaf, and `pageTwoSmallSiteZeroIso` transports it
through Čech cohomology, so that the source of the edge map reads `Ȟ^i(K, 𝓕)` and not
`Ȟ^i(K, H⁰(𝓕))`.

## Main definitions

* `Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo.bottomRowEdge`: for a functorial
  filtered abutment of a first-quadrant spectral sequence, the edge map `E₂^{i,0} ⟶ H^i`,
  natural in the parameter.
* `Stacks.Cohomology.FreeYoneda.cohomologyPresheafFunctorZeroIso`: the degree-zero sheaf
  cohomology presheaf is the presheaf of sections, naturally in the sheaf.
* `Stacks.CategoryTheory.Hypercovering.cechSmallSite` and
  `Stacks.CategoryTheory.Hypercovering.Functorial.cechHypercovering`: `(K, 𝓕) ↦ Ȟ^p(K, 𝓕)`, the
  Čech cohomology of a hypercovering with coefficients in the sheaf itself.
* `Stacks.CategoryTheory.Hypercovering.Functorial.hypercoveringCechEdge`: the edge map
  `Ȟ^i(K, 𝓕) ⟶ H^i(X, 𝓕)` of clause (3) of [Stacks, Tag 01GY], natural in the hypercovering and
  in the coefficient sheaf simultaneously.
* `Stacks.CategoryTheory.Hypercovering.globalCechEdge`: the global analogue
  `Ȟ^i(K, 𝓕) ⟶ H^i(𝓕)` for a hypercovering of the final presheaf, from [Stacks, Tag 09VY].

## Main results

* `Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo.bottomRowEdge_naturality` and
  `bottomRowEdge_app`: the naturality square of the edge map and its value at an object.
* `cechHypercovering_map_comp_hypercoveringCechEdge`, in
  `Stacks.CategoryTheory.Hypercovering.Functorial`: the edge maps form a cocone: a morphism of
  hypercoverings `L ⟶ K` gives `Ȟ^i(K, 𝓕) ⟶ Ȟ^i(L, 𝓕)`, and following it by the edge map of `L` is
  the edge map of `K`.

## Implementation notes

The naturality of the edge map in the parameter rests on the naturality of the edge epimorphism,
`CategoryTheory.SpectralSequence.Hom.edgeEpi_naturality`: at `(i, 0)` with `i ≥ 2` the
differentials into the position do not vanish on the second page, so the second page is not the
infinity page there and only the edge epimorphism is available.

`bottomGradedIso` is `FunctorialFirstQuadrantAbutsTo.gradedIso` at `q = 0` restated with
`filtration i` in place of `filtration (i + 0)`. The two are definitionally equal but not
syntactically so, and without the restatement `Category.assoc` cannot re-associate a composite
through the graded identification.

For the global spectral sequence of [Stacks, Tag 09VY] the parameter category is the category of
sheaves alone, the hypercovering being a fixed parameter, so `globalCechEdge` is natural in the
sheaf only: `presheafHypercoveringSpectralSequenceFunctoriality` makes the *spectral sequence*
functorial in the hypercovering, but no compatibility of the abutments
`hypercoverPresheafAbutment J G K` for different `K` is available. For a hypercovering of an
*object* the abutment is functorial in the hypercovering (`hypercoveringCohomologyAbutment`), which
is why `hypercoveringCechEdge` is natural in `K` and `globalCechEdge` is not.

## References

* [Stacks Project, Tag 01GY](https://stacks.math.columbia.edu/tag/01GY)
* [Stacks Project, Tag 01H0](https://stacks.math.columbia.edu/tag/01H0)
* [Stacks Project, Tag 09VY](https://stacks.math.columbia.edu/tag/09VY)
* [Stacks Project, Tag 09VZ](https://stacks.math.columbia.edu/tag/09VZ)
* [Stacks Project, Tag 03AY](https://stacks.math.columbia.edu/tag/03AY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Prod

universe w v u

/-! ### The bottom-row edge map of a functorial first-quadrant abutment -/

namespace Stacks.Cohomology.Leray

variable {D A : Type*} [Category* D] [Category* A] [Abelian A]
  {E : D ⥤ E₂CohomologicalSpectralSequenceNat A} {H : ℕ → D ⥤ A}

namespace FunctorialFirstQuadrantAbutsTo

variable (h : FunctorialFirstQuadrantAbutsTo E H)

/-- The projection of the `i`-th filtration step of the abutment in degree `i` onto the `i`-th
graded piece is invertible, the `(i + 1)`-st step being zero. -/
lemma isIso_grMapπ (i : ℕ) (K : D) :
    IsIso (FilteredObject.grMapπ (FilteredObject.succHom (i : ℤ))
      ((h.filtration i).obj K)) :=
  cokernel.π_of_zero
    (((Filtration.subobject_eq_bot_iff ((h.filtration i).obj K).filtration
      (op ((i : ℤ) + 1))).1 (h.isBot K i)).some.isZero.eq_zero_of_src _)

attribute [local instance] isIso_grMapπ

/-- The infinity page at `(i, 0)` is the `i`-th graded piece of the abutment in degree `i`:
the field `gradedIso` at `q = 0`, with the total degree written `i` rather than `i + 0`. -/
def bottomGradedIso (i : ℕ) (K : D) :
    (E.obj K).pageInfinity (i, 0) ≅
      (FilteredObject.gr (i : ℤ)).obj ((h.filtration i).obj K) :=
  h.gradedIso K i 0

/-- `bottomGradedIso` is natural in the parameter: the field `gradedIso_naturality` at `q = 0`. -/
lemma bottomGradedIso_naturality (i : ℕ) {K L : D} (φ : K ⟶ L) :
    SpectralSequence.Hom.mapPageInfinity (E.map φ) (i, 0) ≫ (h.bottomGradedIso i L).hom =
      (h.bottomGradedIso i K).hom ≫
        (FilteredObject.gr (i : ℤ)).map ((h.filtration i).map φ) :=
  h.gradedIso_naturality φ i 0

/-- The naturality square of the composite of the edge epimorphism at `(i, 0)` with the graded
identification. -/
lemma bottomRowSquare (i : ℕ) {K L : D} (φ : K ⟶ L) :
    ((E.map φ).hom 2).f (i, 0) ≫ ((E.obj L).edgeEpi (i, 0) 2 ≫ (h.bottomGradedIso i L).hom) =
      ((E.obj K).edgeEpi (i, 0) 2 ≫ (h.bottomGradedIso i K).hom) ≫
        (FilteredObject.gr (i : ℤ)).map ((h.filtration i).map φ) := by
  rw [← Category.assoc, SpectralSequence.Hom.edgeEpi_naturality (E.map φ) (i, 0) 2,
    Category.assoc, h.bottomGradedIso_naturality i φ, Category.assoc]

/-- The edge epimorphism of the bottom row onto the graded piece of the abutment,
`E₂^{i,0} ⟶ gr^i H^i`, natural in the parameter. -/
def bottomRowGrHom (i : ℕ) :
    E ⋙ CategoryTheory.SpectralSequence.pageFunctor _ _ 2 2 ⋙
        HomologicalComplex.eval _ _ ((i : ℕ), (0 : ℕ)) ⟶
      h.filtration i ⋙ FilteredObject.gr (i : ℤ) where
  app K := (E.obj K).edgeEpi (i, 0) 2 ≫ (h.bottomGradedIso i K).hom
  naturality _ _ φ := h.bottomRowSquare i φ

/-- The `i`-th graded piece of the abutment in degree `i` is its `i`-th filtration step,
naturally, the `(i + 1)`-st step being zero. -/
def grIsoEval (i : ℕ) :
    h.filtration i ⋙ FilteredObject.gr (i : ℤ) ≅
      h.filtration i ⋙ FilteredObject.eval (op (i : ℤ)) :=
  NatIso.ofComponents
    (fun K ↦ (asIso (FilteredObject.grMapπ (FilteredObject.succHom (i : ℤ))
      ((h.filtration i).obj K))).symm)
    (fun {_ _} φ ↦ by
      dsimp only [Functor.comp_map, Iso.symm_hom, asIso_inv, FilteredObject.eval_map]
      rw [IsIso.eq_inv_comp, ← Category.assoc, IsIso.comp_inv_eq]
      exact FilteredObject.grMapπ_map _ ((h.filtration i).map φ))

/-- The inclusion of the `i`-th filtration step of the abutment in degree `i`, `F^i H^i ⟶ H^i`,
naturally. -/
def evalHomForget (i : ℕ) :
    h.filtration i ⋙ FilteredObject.eval (op (i : ℤ)) ⟶
      h.filtration i ⋙ FilteredObject.forget where
  app K := ((h.filtration i).obj K).filtration.ι.app (op (i : ℤ))
  naturality _ _ φ := FilteredObject.Hom.comm ((h.filtration i).map φ) (op (i : ℤ))

/-- Each component of `evalHomForget` is a monomorphism. -/
instance mono_evalHomForget_app (i : ℕ) (K : D) : Mono ((h.evalHomForget i).app K) :=
  inferInstanceAs (Mono (((h.filtration i).obj K).filtration.ι.app (op (i : ℤ))))

/-- The edge map of the bottom row of a first-quadrant spectral sequence, `E₂^{i,0} ⟶ H^i`,
natural in the parameter: the edge epimorphism onto the infinity page, the graded identification
of the abutment, the identification of `gr^i H^i` with `F^i H^i` and the inclusion of `F^i H^i`
in `H^i`. -/
def bottomRowEdge (i : ℕ) :
    E ⋙ CategoryTheory.SpectralSequence.pageFunctor _ _ 2 2 ⋙
        HomologicalComplex.eval _ _ ((i : ℕ), (0 : ℕ)) ⟶ H i :=
  h.bottomRowGrHom i ≫ (h.grIsoEval i).hom ≫ h.evalHomForget i ≫ (h.abutmentIso i).hom

/-- The value of the bottom-row edge map at an object of the parameter category. -/
lemma bottomRowEdge_app (i : ℕ) (K : D) :
    (h.bottomRowEdge i).app K =
      (E.obj K).edgeEpi (i, 0) 2 ≫ (h.bottomGradedIso i K).hom ≫
        inv (FilteredObject.grMapπ (FilteredObject.succHom (i : ℤ))
          ((h.filtration i).obj K)) ≫
        ((h.filtration i).obj K).filtration.ι.app (op (i : ℤ)) ≫
        (h.abutmentIso i).hom.app K := by
  dsimp only [bottomRowEdge, NatTrans.comp_app, bottomRowGrHom, grIsoEval, evalHomForget,
    NatIso.ofComponents_hom_app, Iso.symm_hom, asIso_inv]
  exact Category.assoc _ _ _

/-- The bottom-row edge map is natural in the parameter, spelled out as a square: the map a
morphism of the parameter category induces on the second page at `(i, 0)` followed by the edge
map is the edge map followed by the map it induces on the abutment. -/
lemma bottomRowEdge_naturality (i : ℕ) {K L : D} (φ : K ⟶ L) :
    ((E.map φ).hom 2).f (i, 0) ≫ (h.bottomRowEdge i).app L =
      (h.bottomRowEdge i).app K ≫ (H i).map φ :=
  (h.bottomRowEdge i).naturality φ

end FunctorialFirstQuadrantAbutsTo

end Stacks.Cohomology.Leray

/-! ### Degree-zero sheaf cohomology is the presheaf of sections, naturally in the sheaf -/

namespace Stacks.Cohomology.FreeYoneda

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}] [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]

/-- The degree-zero sheaf cohomology presheaf is the presheaf of sections, naturally in the
sheaf. -/
def cohomologyPresheafFunctorZeroIso :
    Sheaf.cohomologyPresheafFunctor J 0 ≅ sheafToPresheaf J AddCommGrpCat.{v} :=
  NatIso.ofComponents cohomologyPresheafIsoSections (fun {_ _} β ↦ by
    refine NatTrans.ext (funext fun U ↦ ConcreteCategory.hom_ext _ _ fun x ↦ ?_)
    exact ((ConcreteCategory.comp_apply _ _ x).trans
      (extSectionsAddEquiv_naturality U.unop x β)).trans
      (ConcreteCategory.comp_apply _ _ x).symm)

end Stacks.Cohomology.FreeYoneda

/-! ### Čech cohomology with coefficients in the sheaf -/

namespace Stacks.CategoryTheory.Hypercovering

section SmallSite

variable {C : Type v} [SmallCategory C]

/-- `CategoryTheory.Sheaf.hasExt_of_smallSite` as a local instance. -/
local instance hasExtSmallSiteEdge (J : GrothendieckTopology C) :
    HasExt.{v} (Sheaf J AddCommGrpCat.{v}) :=
  Sheaf.hasExt_of_smallSite J

variable (J : GrothendieckTopology C) (X : C)

/-- `(K, 𝓕) ↦ Ȟ^p(K, 𝓕)` on a site in the Stacks sense: the Čech cohomology of a simplicial
semi-representable object over `X` with coefficients in the sheaf `𝓕` itself, contravariantly in
`K` and covariantly in `𝓕`. -/
def cechSmallSite (p : ℕ) :
    (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ × Sheaf J AddCommGrpCat.{v} ⥤
      AddCommGrpCat.{v} :=
  Functor.uncurry.obj (cechCohomologyOverBifunctor.{v} X p ⋙
    (Functor.whiskeringLeft (Sheaf J AddCommGrpCat.{v}) (Cᵒᵖ ⥤ AddCommGrpCat.{v})
      AddCommGrpCat.{v}).obj (sheafToPresheaf J AddCommGrpCat.{v}))

/-- The value of `cechSmallSite` is `Ȟ^p(K, 𝓕)`, on the nose: the degree-`p` Čech cohomology
of `K` with coefficients in the presheaf underlying `𝓕`. -/
lemma cechSmallSite_obj (K : SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))
    (F : Sheaf J AddCommGrpCat.{v}) (p : ℕ) :
    (cechSmallSite J X p).obj (op K, F) =
      ((cechCohomologyOverBifunctor.{v} X p).obj (op K)).obj
        ((sheafToPresheaf J AddCommGrpCat.{v}).obj F) :=
  rfl

/-- On a morphism of simplicial semi-representable objects `cechSmallSite` is the canonical
pullback map on Čech cohomology, with the coefficient sheaf fixed. -/
lemma cechSmallSite_map_hypercovering
    {K L : SimplicialObject (Limits.FormalCoproduct.{v} (Over X))} (f : K ⟶ L)
    (F : Sheaf J AddCommGrpCat.{v}) (p : ℕ) :
    (cechSmallSite J X p).map (f.op ×ₘ 𝟙 F) =
      ((cechCohomologyOverBifunctor.{v} X p).map f.op).app
        ((sheafToPresheaf J AddCommGrpCat.{v}).obj F) := by
  simp [cechSmallSite, Functor.uncurry]

/-- The bottom row of the second page of [Stacks, Tag 01GY] has coefficients in the sheaf
itself: `Ȟ^p(K, H⁰(𝓕)) ≅ Ȟ^p(K, 𝓕)`, naturally in `K` and `𝓕` simultaneously. -/
def pageTwoSmallSiteZeroIso (p : ℕ) :
    pageTwoSmallSite J X p 0 ≅ cechSmallSite J X p :=
  Functor.uncurry.mapIso (Functor.isoWhiskerLeft (cechCohomologyOverBifunctor.{v} X p)
    ((Functor.whiskeringLeft (Sheaf J AddCommGrpCat.{v}) (Cᵒᵖ ⥤ AddCommGrpCat.{v})
      AddCommGrpCat.{v}).mapIso
      (Stacks.Cohomology.FreeYoneda.cohomologyPresheafFunctorZeroIso J)))

end SmallSite

/-! ### The edge map of the hypercovering spectral sequence -/

namespace Functorial

variable {C : Type v} [SmallCategory C] [HasPullbacks C] (X : C) (J : Pretopology C)

/-- `Ȟ^p(-, -)` on the hypercoverings of `X`, with coefficients in the sheaf: the restriction of
`cechSmallSite` to the full subcategory of hypercoverings of `X`. -/
abbrev cechHypercovering (p : ℕ) :
    (HypercoveringCat X J)ᵒᵖ × Sheaf J.toGrothendieck AddCommGrpCat.{v} ⥤ AddCommGrpCat.{v} :=
  (ObjectProperty.ι _).op.prod (𝟭 (Sheaf J.toGrothendieck AddCommGrpCat.{v})) ⋙
    cechSmallSite J.toGrothendieck X p

/-- The bottom row of the second page of clause (3) of [Stacks, Tag 01GY] is `Ȟ^p(K, 𝓕)`,
naturally in the hypercovering and in the coefficient sheaf simultaneously. -/
def hypercoveringPageTwoZeroIso (p : ℕ) :
    pageTwoHypercovering.{v} X J p 0 ≅ cechHypercovering.{v} X J p :=
  Functor.isoWhiskerLeft _ (pageTwoSmallSiteZeroIso J.toGrothendieck X p)

/-- The asserted abutment of clause (3) of [Stacks, Tag 01GY] does not move with the
hypercovering: a morphism of hypercoverings acts on `H^n(X, -)` by the identity. -/
lemma hypercoveringCohomologyFunctor_map_eq_id (n : ℕ)
    {K L : (HypercoveringCat X J)ᵒᵖ} (φ : K ⟶ L)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{v}) :
    (hypercoveringCohomologyFunctor X J n).map (φ ×ₘ 𝟙 F) = 𝟙 _ := by
  change ((Sheaf.cohomologyPresheafFunctor J.toGrothendieck n).map (𝟙 F)).app (op X) = _
  rw [CategoryTheory.Functor.map_id, NatTrans.id_app]
  rfl

/-- The edge map of clause (3) of [Stacks, Tag 01GY] in general degree, `Ȟ^i(K, 𝓕) ⟶ H^i(X, 𝓕)`,
natural in the hypercovering `K` and in the abelian sheaf `𝓕` simultaneously: the bottom-row edge
map of the hypercovering spectral sequence, read through the second-page identification
`hypercoveringPageTwoIso` and the identification `hypercoveringPageTwoZeroIso` of the bottom row's
coefficients with the sheaf itself. -/
def hypercoveringCechEdge (i : ℕ) :
    cechHypercovering.{v} X J i ⟶ hypercoveringCohomologyFunctor X J i :=
  (hypercoveringPageTwoZeroIso.{v} X J i).inv ≫ (hypercoveringPageTwoIso.{v} X J i 0).inv ≫
    (hypercoveringCohomologyAbutment X J).bottomRowEdge i

/-- The edge maps of [Stacks, Tag 01GY] form a cocone on the diagram of Čech cohomology: a
morphism of hypercoverings `φ : L ⟶ K` induces `Ȟ^i(K, 𝓕) ⟶ Ȟ^i(L, 𝓕)`, and following it by the
edge map of `L` gives back the edge map of `K`. -/
lemma cechHypercovering_map_comp_hypercoveringCechEdge (i : ℕ) {K L : HypercoveringCat X J}
    (φ : L ⟶ K) (F : Sheaf J.toGrothendieck AddCommGrpCat.{v}) :
    (cechHypercovering.{v} X J i).map (φ.op ×ₘ 𝟙 F) ≫
        (hypercoveringCechEdge.{v} X J i).app (op L, F) =
      (hypercoveringCechEdge.{v} X J i).app (op K, F) := by
  rw [(hypercoveringCechEdge.{v} X J i).naturality (φ.op ×ₘ 𝟙 F),
    hypercoveringCohomologyFunctor_map_eq_id X J i φ.op F]
  exact Category.comp_id _

end Functorial

/-! ### The global edge map of a hypercovering of the final presheaf -/

section Global

variable {C : Type u} [Category.{v} C] [HasEqualizers C] [HasPullbacks C]
variable (J : Pretopology C) (K : HypercoveringOfTerminal.{w} J)
  [HasSheafify J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)}]
  [EnoughInjectives (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)})]
  [HasExt.{max (max u v) (max v w)}
    (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)})]

/-- The global edge map `Ȟ^i(K, 𝓕) ⟶ H^i(𝓕)`, natural in the abelian sheaf `𝓕`: the
bottom-row edge map of the spectral sequence of [Stacks, Tag 09VY] of a hypercovering `K` of the
final presheaf, with the degree-zero coefficient presheaf `R^0(\mathrm{sheafToPresheaf})` of its
second page identified with the presheaf underlying `𝓕`. -/
def globalCechEdge (i : ℕ) :
    sheafToPresheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)} ⋙
        presheafCechCohomologyFunctor J (⊤_ (Cᵒᵖ ⥤ Type v)) K i ⟶
      globalCohomologyFunctor.{w} J i :=
  Functor.whiskerRight
      (sheafToPresheaf J.toGrothendieck
        AddCommGrpCat.{max (max u v) (max v w)}).rightDerivedZeroIsoSelf.inv
      (presheafCechCohomologyFunctor J (⊤_ (Cᵒᵖ ⥤ Type v)) K i) ≫
    ((hypercoveringGlobalSpectralSequence J K).pageTwoIso i 0).inv ≫
    (hypercoveringGlobalSpectralSequence J K).abutment.bottomRowEdge i

end Global

end Stacks.CategoryTheory.Hypercovering

end
