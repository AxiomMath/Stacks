module

public import Mathlib.CategoryTheory.Limits.IsConnected
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.EdgeMap
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.HomotopyCategory
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.PageDegeneration
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.SpectralSequenceAbutmentIsCohomology
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.SpectralSequenceSecondPage
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cohomology as a colimit over hypercoverings

Let `C` be a site with fibre products and `X` an object of `C`. For an abelian sheaf `𝓕` the
Čech-to-cohomology edge maps `Ȟ^n(K, 𝓕) ⟶ H^n(X, 𝓕)` exhibit `H^n(X, 𝓕)` as the colimit of the
Čech cohomology groups `Ȟ^n(K, 𝓕)` over the hypercoverings `K` of `X`, and the functor
`𝓕 ↦ H^n(X, 𝓕)` as the colimit of the functors `𝓕 ↦ Ȟ^n(K, 𝓕)` in `Ab(C) ⥤ Ab`. In degree zero
the corner `E₂^{0,0}` of the hypercovering spectral sequence is already the whole abutment, so
every leg of the cocone is an isomorphism.

## Main results

* `CategoryTheory.Limits.isColimit_of_isIso_cocone_ι`: a cocone over a connected index category
  all of whose legs are isomorphisms is a colimit cocone.
* `Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo.pageTwoCornerIso`: for a functorial
  filtered abutment of a first-quadrant spectral sequence, `E₂^{0,0}` is the abutment in degree
  zero, naturally in the parameter.
* `Stacks.CategoryTheory.Hypercovering.isConnected_hypercoverings`: the hypercoverings of `X`
  form a connected category.
* `Stacks.CategoryTheory.Hypercovering.Functorial.isColimit_cechCohomologyZeroCocone`: the
  degree-zero case of the identification of sheaf cohomology with hypercovering Čech cohomology.
* `Stacks.CategoryTheory.Hypercovering.Functorial.exists_hypercovering_map_pageInfinity_eq_zero`:
  for `q > 0`, every element of the infinity page `E_∞^{p,q}` of the spectral sequence of a
  hypercovering dies after a refinement of the hypercovering.
* `Stacks.CategoryTheory.Hypercovering.Functorial.exists_hypercovering_map_gradedPiece_eq_zero`:
  for `q > 0`, every element of the graded piece `gr^p H^{p+q}(X, 𝓕)` of the abutment filtration
  dies after a refinement.
* `Stacks.CategoryTheory.Hypercovering.Functorial.exists_hypercovering_map_filtration_step`:
  for `q > 0`, an element of the step `F^p H^{p+q}(X, 𝓕)` of the filtration carried by a
  hypercovering becomes, after a refinement, the image of an element of the next step
  `F^{p+1} H^{p+q}(X, 𝓕)`.
* `Stacks.CategoryTheory.Hypercovering.Functorial.exists_hypercovering_map_stepToAbutment_eq`:
  every cohomology class in a step `F^j H^n(X, 𝓕)` of the filtration becomes, after a
  refinement, a class in the bottom step `F^n H^n(X, 𝓕)`.
* `Stacks.CategoryTheory.Hypercovering.Functorial`'s
  `exists_hypercovering_map_hypercoveringCechEdge_apply_eq`: every cohomology class in
  `H^n(X, 𝓕)` is, after a refinement of the hypercovering, the image of a Čech class `Ȟ^n(L, 𝓕)`
  under the edge map `hypercoveringCechEdge`.
* `CategoryTheory.CohomologicalSpectralSequenceNat.exists_map_pageTwo_eq_zero`: for a functorial
  first-quadrant spectral sequence of abelian groups whose terms off the bottom row all die after
  a morphism of the parameter category, the kernel of `E₂^{n,0} ⟶ E_r^{n,0}` dies after such a
  morphism.
* `CategoryTheory.CohomologicalSpectralSequenceNat.exists_map_eq_zero_of_edgeEpi_apply_eq_zero`:
  the same at the edge epimorphism `E₂^{n,0} ⟶ E_∞^{n,0}` itself.
* `Stacks.Cohomology.Leray.edgeEpi_apply_eq_zero_of_bottomRowEdge_apply_eq_zero`: the kernel of
  the bottom-row edge map `E₂^{i,0} ⟶ H^i` of a functorial abutment is contained in the kernel of
  that edge epimorphism.
* `Stacks.CategoryTheory.Hypercovering.Functorial`'s
  `exists_hypercovering_map_cechHypercovering_apply_eq_zero`: a Čech class in `Ȟ^n(K, 𝓕)` that
  the edge map `hypercoveringCechEdge` kills dies after a refinement of the hypercovering.
* `Stacks.CategoryTheory.Hypercovering.Functorial.isColimit_cechCoconeAtSheaf`: `H^n(X, 𝓕)` is
  the colimit over the hypercoverings of `X` of the Čech cohomology groups `Ȟ^n(K, 𝓕)`, the
  cocone being the edge maps.
* `Stacks.CategoryTheory.Hypercovering.Functorial.isColimit_cechFunctorCocone`: the same as an
  identification of functors on the abelian sheaves: the edge maps exhibit `𝓕 ↦ H^i(X, 𝓕)` as the
  colimit over the hypercoverings of `X` of the functors `𝓕 ↦ Ȟ^i(K, 𝓕)`, the colimit being
  taken in `Ab(C) ⥤ Ab`.

## Implementation notes

The cocone is built from the hypercovering spectral sequence together with its second page and its
abutment, at an arbitrary hypercovering, and not from the comparison map
`Stacks.CategoryTheory.Hypercovering.hypercoverCohomologyComparison`.

The index category is the category of hypercoverings with *all* maps, not with maps up to
homotopy. It is connected (`isConnected_hypercoverings`), any two hypercoverings being refined
by their product (`exists_hom_pair`), but not known to be cofiltered.

## References

* [Stacks Project, Tag 01GI](https://stacks.math.columbia.edu/tag/01GI)
* [Stacks Project, Tag 01GV](https://stacks.math.columbia.edu/tag/01GV)
* [Stacks Project, Tag 01GY](https://stacks.math.columbia.edu/tag/01GY)
* [Stacks Project, Tag 01H0](https://stacks.math.columbia.edu/tag/01H0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Prod

universe w v₁ u₁ v u

/-! ### Colimits over a connected index category -/

namespace CategoryTheory.Limits

/-- **A cocone whose legs are all isomorphisms is a colimit cocone**, provided the index
category is connected. -/
def isColimit_of_isIso_cocone_ι {I : Type u₁} [Category.{v₁} I] [IsConnected I]
    {A : Type u} [Category.{v} A] {D : I ⥤ A} (c : Cocone D)
    (hc : ∀ i, IsIso (c.ι.app i)) : IsColimit c :=
  haveI := hc
  { desc := fun s ↦ inv (c.ι.app (Classical.arbitrary I)) ≫ s.ι.app (Classical.arbitrary I)
    fac := fun s i ↦ by
      have key : ∀ j j' : I, inv (c.ι.app j) ≫ s.ι.app j = inv (c.ι.app j') ≫ s.ι.app j' := by
        refine constant_of_preserves_morphisms (fun j ↦ inv (c.ι.app j) ≫ s.ι.app j) ?_
        intro j₁ j₂ f
        have hcw : D.map f ≫ c.ι.app j₂ = c.ι.app j₁ := c.w f
        have hsw : D.map f ≫ s.ι.app j₂ = s.ι.app j₁ := s.w f
        rw [IsIso.inv_comp_eq, ← hsw, ← hcw, Category.assoc, IsIso.hom_inv_id_assoc]
      rw [← key i (Classical.arbitrary I), IsIso.hom_inv_id_assoc]
    uniq := fun s m hm ↦ by
      rw [← hm (Classical.arbitrary I), IsIso.inv_hom_id_assoc] }

end CategoryTheory.Limits

/-- A monomorphism of abelian groups reflects zero: an element with zero image is zero. -/
private theorem eq_zero_of_mono_hom_apply_eq_zero {A B : AddCommGrpCat.{v}} (f : A ⟶ B) [Mono f]
    (x : ToType A) (hx : ConcreteCategory.hom f x = 0) : x = 0 :=
  (AddCommGrpCat.mono_iff_injective f).1 inferInstance (hx.trans (map_zero _).symm)

/-! ### The corner of the second page of a first-quadrant spectral sequence -/

namespace Stacks.Cohomology.Leray

variable {D A : Type*} [Category* D] [Category* A] [Abelian A]
  {E : D ⥤ E₂CohomologicalSpectralSequenceNat A} {H : ℕ → D ⥤ A}

/-- **A morphism of spectral sequences commutes with the identification of a page with the
infinity page**, at a bidegree and a page where the differentials into and out of it vanish. -/
lemma pageInfinityIso_inv_naturality
    {E E' : E₂CohomologicalSpectralSequenceNat A} (f : E ⟶ E') (p q : ℕ) (r : ℤ)
    [E.HasEdgeMonoAtFrom (p, q) r] [E.HasEdgeEpiAtFrom (p, q) r]
    [E'.HasEdgeMonoAtFrom (p, q) r] [E'.HasEdgeEpiAtFrom (p, q) r] (hr : 2 ≤ r := by lia) :
    (f.hom r).f (p, q) ≫ (E'.pageInfinityIso (p, q) r).inv =
      (E.pageInfinityIso (p, q) r).inv ≫ SpectralSequence.Hom.mapPageInfinity f (p, q) := by
  rw [SpectralSequence.Hom.mapPageInfinity_eq f (p, q) r]
  simp

/-- **A morphism of spectral sequences commutes with the identification of the infinity page with
a page** on which the differentials into and out of the bidegree have vanished, in the direction
that reads the infinity page off on that page. -/
lemma mapPageInfinity_comp_pageInfinityIso_hom
    {E E' : E₂CohomologicalSpectralSequenceNat A} (f : E ⟶ E') (p q : ℕ) (r : ℤ)
    [E.HasEdgeMonoAtFrom (p, q) r] [E.HasEdgeEpiAtFrom (p, q) r]
    [E'.HasEdgeMonoAtFrom (p, q) r] [E'.HasEdgeEpiAtFrom (p, q) r] (hr : 2 ≤ r := by lia) :
    SpectralSequence.Hom.mapPageInfinity f (p, q) ≫ (E'.pageInfinityIso (p, q) r).hom =
      (E.pageInfinityIso (p, q) r).hom ≫ (f.hom r).f (p, q) := by
  rw [SpectralSequence.Hom.mapPageInfinity_eq f (p, q) r]
  simp

/-- **A morphism of spectral sequences of abelian groups kills an element of the infinity page at
`(p, q)` as soon as it kills the element's image on a page where the infinity page is already
reached.** -/
lemma mapPageInfinity_apply_eq_zero
    {E E' : E₂CohomologicalSpectralSequenceNat AddCommGrpCat.{v}} (f : E ⟶ E') (p q : ℕ) (r : ℤ)
    [E.HasEdgeMonoAtFrom (p, q) r] [E.HasEdgeEpiAtFrom (p, q) r]
    [E'.HasEdgeMonoAtFrom (p, q) r] [E'.HasEdgeEpiAtFrom (p, q) r] (hr : 2 ≤ r)
    (x : ToType (E.pageInfinity (p, q)))
    (hx : ConcreteCategory.hom ((f.hom r hr).f (p, q))
      (ConcreteCategory.hom (E.pageInfinityIso (p, q) r).hom x) = 0) :
    ConcreteCategory.hom (SpectralSequence.Hom.mapPageInfinity f (p, q)) x = 0 := by
  refine eq_zero_of_mono_hom_apply_eq_zero (E'.pageInfinityIso (p, q) r).hom _ ?_
  rw [← ConcreteCategory.comp_apply, mapPageInfinity_comp_pageInfinityIso_hom f p q r hr,
    ConcreteCategory.comp_apply]
  exact hx

namespace FunctorialFirstQuadrantAbutsTo

variable (h : FunctorialFirstQuadrantAbutsTo E H)

/-- The projection of the zeroth filtration step of the abutment in degree zero onto the zeroth
graded piece is invertible, the first step being zero. -/
lemma isIso_grMapπ_zero (K : D) :
    IsIso (FilteredObject.grMapπ (FilteredObject.succHom (0 : ℤ))
      ((h.filtration 0).obj K)) :=
  cokernel.π_of_zero
    (((Filtration.subobject_eq_bot_iff ((h.filtration 0).obj K).filtration
      (op ((0 : ℤ) + 1))).1 (h.isBot K 0)).some.isZero.eq_zero_of_src _)

/-- The zeroth filtration step of the abutment is the whole abutment, in every degree. -/
lemma isIso_ι_app_zero (n : ℕ) (K : D) :
    IsIso (((h.filtration n).obj K).filtration.ι.app (op (0 : ℤ))) :=
  (Filtration.subobject_eq_top_iff _ _).1 (h.isTop K n)

attribute [local instance] isIso_grMapπ_zero isIso_ι_app_zero

/-- The naturality square identifying the corner of the second page with the zeroth graded
piece of the abutment in degree zero. -/
lemma pageTwoCornerSquare {K L : D} (φ : K ⟶ L) :
    ((E.map φ).hom 2).f (0, 0) ≫
        (((E.obj L).pageInfinityIso (0, 0) 2).symm ≪≫ h.gradedIso L 0 0).hom =
      (((E.obj K).pageInfinityIso (0, 0) 2).symm ≪≫ h.gradedIso K 0 0).hom ≫
        (FilteredObject.gr (0 : ℤ)).map ((h.filtration 0).map φ) := by
  simp only [Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, pageInfinityIso_inv_naturality (E.map φ) 0 0 2, Category.assoc,
    h.gradedIso_naturality φ 0 0, Category.assoc]

/-- **The corner of the second page is the zeroth graded piece of the abutment in degree
zero**, naturally. -/
def pageTwoCornerGrIso :
    E ⋙ CategoryTheory.SpectralSequence.pageFunctor _ _ 2 2 ⋙
        HomologicalComplex.eval _ _ ((0 : ℕ), (0 : ℕ)) ≅
      h.filtration 0 ⋙ FilteredObject.gr (0 : ℤ) :=
  NatIso.ofComponents
    (fun K ↦ ((E.obj K).pageInfinityIso (0, 0) 2).symm ≪≫ h.gradedIso K 0 0)
    (fun {_ _} φ ↦ h.pageTwoCornerSquare φ)

/-- **The zeroth graded piece of the abutment in degree zero is the zeroth filtration step**,
naturally, the first step being zero. -/
def grZeroIsoEval :
    h.filtration 0 ⋙ FilteredObject.gr (0 : ℤ) ≅
      h.filtration 0 ⋙ FilteredObject.eval (op (0 : ℤ)) :=
  NatIso.ofComponents
    (fun K ↦ (asIso (FilteredObject.grMapπ (FilteredObject.succHom (0 : ℤ))
      ((h.filtration 0).obj K))).symm)
    (fun {_ _} φ ↦ by
      dsimp only [Functor.comp_map, Iso.symm_hom, asIso_inv, FilteredObject.eval_map]
      rw [IsIso.eq_inv_comp, ← Category.assoc, IsIso.comp_inv_eq]
      exact FilteredObject.grMapπ_map _ ((h.filtration 0).map φ))

/-- **The zeroth filtration step of the abutment in degree zero is the whole abutment**,
naturally. -/
def evalZeroIsoForget :
    h.filtration 0 ⋙ FilteredObject.eval (op (0 : ℤ)) ≅
      h.filtration 0 ⋙ FilteredObject.forget :=
  NatIso.ofComponents
    (fun K ↦ asIso (((h.filtration 0).obj K).filtration.ι.app (op (0 : ℤ))))
    (fun {_ _} φ ↦ FilteredObject.Hom.comm ((h.filtration 0).map φ) (op (0 : ℤ)))

/-- **The corner of the second page of a first-quadrant spectral sequence is the abutment in
degree zero**, naturally in the parameter. -/
def pageTwoCornerIso :
    E ⋙ CategoryTheory.SpectralSequence.pageFunctor _ _ 2 2 ⋙
        HomologicalComplex.eval _ _ ((0 : ℕ), (0 : ℕ)) ≅ H 0 :=
  h.pageTwoCornerGrIso ≪≫ h.grZeroIsoEval ≪≫ h.evalZeroIsoForget ≪≫ h.abutmentIso 0

/-! #### The steps of the abutment filtration as subobjects of the abutment -/

/-- **The inclusion `F^j H^n ⟶ H^n` of a step of the abutment filtration into the abutment**,
natural in the parameter: the inclusion carried by the filtered object, followed by the
identification of the filtered object with the asserted abutment. -/
def stepToAbutment (n : ℕ) (j : ℤ) : h.filtration n ⋙ FilteredObject.eval (op j) ⟶ H n where
  app K := ((h.filtration n).obj K).filtration.ι.app (op j) ≫ (h.abutmentIso n).hom.app K
  naturality K L φ := by
    have hcomm := FilteredObject.Hom.comm ((h.filtration n).map φ) (op j)
    have hnat : ((h.filtration n).map φ).hom ≫ (h.abutmentIso n).hom.app L =
        (h.abutmentIso n).hom.app K ≫ (H n).map φ := (h.abutmentIso n).hom.naturality φ
    dsimp only [Functor.comp_map, FilteredObject.eval_map]
    rw [← Category.assoc, hcomm, Category.assoc, hnat, ← Category.assoc]

/-- The value of the inclusion of a filtration step at an object of the parameter category. -/
@[simp]
lemma stepToAbutment_app (n : ℕ) (j : ℤ) (K : D) :
    (h.stepToAbutment n j).app K =
      ((h.filtration n).obj K).filtration.ι.app (op j) ≫ (h.abutmentIso n).hom.app K :=
  rfl

/-- **The inclusion of a filtration step into the abutment is natural in the parameter**, spelled
out as a square: the map a morphism of the parameter category induces on the step followed by the
inclusion is the inclusion followed by the map it induces on the abutment. -/
lemma stepToAbutment_naturality (n : ℕ) (j : ℤ) {K L : D} (φ : K ⟶ L) :
    ((h.filtration n).map φ).natTrans.app (op j) ≫ (h.stepToAbutment n j).app L =
      (h.stepToAbutment n j).app K ≫ (H n).map φ :=
  (h.stepToAbutment n j).naturality φ

/-- **Passing from the `(j+1)`-st step of the abutment filtration to the `j`-th does not change
the inclusion into the abutment.** -/
lemma step_comp_stepToAbutment (n : ℕ) (j : ℤ) (K : D) :
    ((h.filtration n).obj K).filtration.step (FilteredObject.succHom j) ≫
        (h.stepToAbutment n j).app K = (h.stepToAbutment n (j + 1)).app K := by
  rw [h.stepToAbutment_app, h.stepToAbutment_app, ← Category.assoc,
    Filtration.step_comp_ι_app]

/-- **The zeroth step of the abutment filtration is the whole abutment**: its inclusion is an
isomorphism, the zeroth step being the top one (`isTop`). -/
lemma isIso_stepToAbutment_zero (n : ℕ) (K : D) : IsIso ((h.stepToAbutment n 0).app K) :=
  have := h.isIso_ι_app_zero n K
  inferInstanceAs (IsIso (((h.filtration n).obj K).filtration.ι.app (op (0 : ℤ)) ≫
    (h.abutmentIso n).hom.app K))

/-- **The bottom-row edge map is an epimorphism onto the `i`-th filtration step of the abutment
followed by the inclusion of that step.**  The epimorphism is the edge epimorphism
`E₂^{i,0} ⟶ E_∞^{i,0}` followed by the identifications of `E_∞^{i,0}` with `gr^i H^i` and of
`gr^i H^i` with `F^i H^i`, which is `bottomRowGrHom` followed by `grIsoEval`. -/
lemma bottomRowEdge_app_eq (i : ℕ) (K : D) :
    (h.bottomRowEdge i).app K =
      ((h.bottomRowGrHom i).app K ≫ (h.grIsoEval i).hom.app K) ≫
        (h.stepToAbutment i (i : ℤ)).app K := by
  dsimp only [bottomRowEdge, NatTrans.comp_app, evalHomForget, stepToAbutment_app]
  rw [Category.assoc]

/-- The map `E₂^{i,0} ⟶ F^i H^i` out of the bottom row of the second page onto the `i`-th step
of the abutment filtration is an epimorphism. -/
lemma epi_bottomRowGrHom_comp_grIsoEval_hom_app (i : ℕ) (K : D) :
    Epi ((h.bottomRowGrHom i).app K ≫ (h.grIsoEval i).hom.app K) :=
  have h₁ : Epi ((h.bottomRowGrHom i).app K) :=
    epi_comp' (inferInstanceAs (Epi ((E.obj K).edgeEpi (i, 0) 2)))
      (inferInstanceAs (Epi (h.bottomGradedIso i K).hom))
  epi_comp' h₁ (inferInstanceAs (Epi ((h.grIsoEval i).hom.app K)))

/-- **The value of the bottom-row edge map at an object, as the composite of the values of its
four factors**: the edge epimorphism onto the graded piece, the identification of `gr^i H^i` with
`F^i H^i`, the inclusion of that step and the identification of the filtered object with the
asserted abutment. -/
lemma bottomRowEdge_app_eq' (i : ℕ) (K : D) :
    (h.bottomRowEdge i).app K =
      (h.bottomRowGrHom i).app K ≫ (h.grIsoEval i).hom.app K ≫
        (h.evalHomForget i).app K ≫ (h.abutmentIso i).hom.app K :=
  rfl

end FunctorialFirstQuadrantAbutsTo

/-! ### Graded pieces of a functorial abutment, on elements -/

/-- **A commuting triangle of morphisms of abelian groups, read on an element.** -/
lemma apply_apply_eq_of_comp_eq {A₁ A₂ A₃ : AddCommGrpCat.{v}} {f : A₁ ⟶ A₂} {g : A₂ ⟶ A₃}
    {k : A₁ ⟶ A₃} (e : f ≫ g = k) (x : ToType A₁) :
    ConcreteCategory.hom g (ConcreteCategory.hom f x) = ConcreteCategory.hom k x :=
  (ConcreteCategory.comp_apply f g x).symm.trans (ConcreteCategory.congr_hom e x)

/-- **A morphism of the parameter category kills a graded piece of the abutment as soon as it
kills the corresponding term of the infinity page.** -/
lemma gradedPiece_map_apply_eq_zero
    {E : D ⥤ E₂CohomologicalSpectralSequenceNat AddCommGrpCat.{v}}
    {H : ℕ → D ⥤ AddCommGrpCat.{v}} (h : FunctorialFirstQuadrantAbutsTo E H)
    {K L : D} (φ : K ⟶ L) (p q : ℕ)
    (y : ToType ((FilteredObject.gr (p : ℤ)).obj ((h.filtration (p + q)).obj K)))
    (hy : ConcreteCategory.hom (SpectralSequence.Hom.mapPageInfinity (E.map φ) (p, q))
      (ConcreteCategory.hom (h.gradedIso K p q).inv y) = 0) :
    ConcreteCategory.hom ((FilteredObject.gr (p : ℤ)).map ((h.filtration (p + q)).map φ)) y
      = 0 := by
  have hinv : ConcreteCategory.hom (h.gradedIso K p q).hom
      (ConcreteCategory.hom (h.gradedIso K p q).inv y) = y := by
    rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id, ConcreteCategory.id_apply]
  have key := ConcreteCategory.congr_hom (h.gradedIso_naturality φ p q)
    (ConcreteCategory.hom (h.gradedIso K p q).inv y)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hy, map_zero, hinv] at key
  exact key.symm

/-- **A map onto the bottom row of the second page, followed by the bottom-row edge map, hits
every element of the `i`-th filtration step of the abutment in degree `i`.** -/
lemma exists_apply_eq_stepToAbutment_apply
    {E : D ⥤ E₂CohomologicalSpectralSequenceNat AddCommGrpCat.{v}}
    {H : ℕ → D ⥤ AddCommGrpCat.{v}} (h : FunctorialFirstQuadrantAbutsTo E H) (i : ℕ) (K : D)
    {G : AddCommGrpCat.{v}}
    (w : G ⟶ ((E.obj K).page 2 le_rfl).X (i, 0)) (hw : Epi w)
    (η : ToType (((h.filtration i).obj K).filtration.obj (op (i : ℤ)))) :
    ∃ c, ConcreteCategory.hom (w ≫ (h.bottomRowEdge i).app K) c =
      ConcreteCategory.hom ((h.stepToAbutment i (i : ℤ)).app K) η := by
  have hfac : (w ≫ (h.bottomRowGrHom i).app K ≫ (h.grIsoEval i).hom.app K) ≫
      (h.stepToAbutment i (i : ℤ)).app K = w ≫ (h.bottomRowEdge i).app K := by
    rw [h.bottomRowEdge_app_eq i K]
    exact Category.assoc _ _ _
  have := epi_comp' hw (h.epi_bottomRowGrHom_comp_grIsoEval_hom_app i K)
  obtain ⟨c, hc⟩ : ∃ c, ConcreteCategory.hom (w ≫ (h.bottomRowGrHom i).app K ≫
      (h.grIsoEval i).hom.app K) c = η :=
    (AddCommGrpCat.epi_iff_surjective _).1 inferInstance η
  refine ⟨c, ?_⟩
  have key := apply_apply_eq_of_comp_eq hfac c
  rw [hc] at key
  exact key.symm

/-- **A class on the bottom row of the second page that the bottom-row edge map kills is killed
already by the edge epimorphism onto the infinity page.** -/
lemma edgeEpi_apply_eq_zero_of_bottomRowEdge_apply_eq_zero
    {E : D ⥤ E₂CohomologicalSpectralSequenceNat AddCommGrpCat.{v}}
    {H : ℕ → D ⥤ AddCommGrpCat.{v}} (h : FunctorialFirstQuadrantAbutsTo E H) (i : ℕ) (K : D)
    (z : ToType (((E.obj K).page 2 le_rfl).X (i, 0)))
    (hz : ConcreteCategory.hom ((h.bottomRowEdge i).app K) z = 0) :
    ConcreteCategory.hom ((E.obj K).edgeEpi (i, 0) 2) z = 0 := by
  have h1 : ConcreteCategory.hom ((h.bottomRowGrHom i).app K) z = 0 := by
    refine eq_zero_of_mono_hom_apply_eq_zero ((h.grIsoEval i).hom.app K ≫
      (h.evalHomForget i).app K ≫ (h.abutmentIso i).hom.app K) _ ?_
    exact (apply_apply_eq_of_comp_eq (h.bottomRowEdge_app_eq' i K).symm z).trans hz
  exact eq_zero_of_mono_hom_apply_eq_zero (h.bottomGradedIso i K).hom _
    ((ConcreteCategory.comp_apply ((E.obj K).edgeEpi (i, 0) 2)
      (h.bottomGradedIso i K).hom z).symm.trans h1)

/-- **An element of the `j`-th step of a filtration of abelian groups whose class in `gr^j`
is killed by a morphism comes, after that morphism, from the `(j+1)`-st step.** -/
lemma exists_step_apply_eq_natTrans_app_apply
    {A B : FilteredObject AddCommGrpCat.{v} ℤᵒᵖ} (φ : A ⟶ B) (j : ℤ)
    (η : ToType (A.filtration.obj (op j)))
    (hη : ConcreteCategory.hom ((FilteredObject.gr j).map φ)
      (ConcreteCategory.hom (FilteredObject.grMapπ (FilteredObject.succHom j) A) η) = 0) :
    ∃ η' : ToType (B.filtration.obj (op (j + 1))),
      ConcreteCategory.hom (B.filtration.step (FilteredObject.succHom j)) η' =
        ConcreteCategory.hom (φ.natTrans.app (op j)) η := by
  have e1 : ConcreteCategory.hom (FilteredObject.grMapπ (FilteredObject.succHom j) A ≫
      (FilteredObject.gr j).map φ) η =
      ConcreteCategory.hom ((FilteredObject.gr j).map φ)
        (ConcreteCategory.hom (FilteredObject.grMapπ (FilteredObject.succHom j) A) η) :=
    ConcreteCategory.comp_apply _ _ η
  have e2 := ConcreteCategory.congr_hom
    (FilteredObject.grMapπ_map (FilteredObject.succHom j) φ) η
  have e3 : ConcreteCategory.hom (φ.natTrans.app (op j) ≫
      FilteredObject.grMapπ (FilteredObject.succHom j) B) η =
      ConcreteCategory.hom (FilteredObject.grMapπ (FilteredObject.succHom j) B)
        (ConcreteCategory.hom (φ.natTrans.app (op j)) η) :=
    ConcreteCategory.comp_apply _ _ η
  exact (ShortComplex.ab_exact_iff _).1
    (FilteredObject.stepShortComplex_shortExact (FilteredObject.succHom j) B).exact _
    (e3.symm.trans (e2.symm.trans (e1.trans hη)))

end Stacks.Cohomology.Leray

/-! ### The kernel of the edge epimorphism of a spectral sequence of abelian groups -/

namespace CategoryTheory.SpectralSequence

variable {ι : Type*} {c : ℤ → ComplexShape ι} {r₀ : ℤ}

/-- **The kernel of the one-step edge epimorphism out of `pq` on the page `r` is the image of the
differential into `pq` on that page**: the page `r + 1` at `pq` is the cokernel of that
differential. -/
lemma exists_d_apply_eq_of_edgeEpiStep_apply_eq_zero
    {E : SpectralSequence AddCommGrpCat.{v} c r₀} (pq : ι) (r r' : ℤ) [E.HasEdgeEpiAt pq r]
    (hrr' : r + 1 = r')
    (y : ToType ((E.page r (E.le₀_of_hasEdgeEpiAt pq r)).X pq))
    (hy : ConcreteCategory.hom (E.edgeEpiStep pq r r' hrr') y = 0) :
    ∃ z : ToType ((E.page r (E.le₀_of_hasEdgeEpiAt pq r)).X ((c r).prev pq)),
      ConcreteCategory.hom
        ((E.page r (E.le₀_of_hasEdgeEpiAt pq r)).d ((c r).prev pq) pq) z = y :=
  (ShortComplex.ab_exact_iff _).1
    (E.edgeEpiStepShortComplex_exact ((c r).prev pq) pq r r' rfl hrr') y hy

/-- **A morphism of spectral sequences of abelian groups commutes with the differentials of a
page**, read on elements. -/
lemma d_apply_naturality {E E' : SpectralSequence AddCommGrpCat.{v} c r₀} (f : E ⟶ E')
    (r : ℤ) (hr : r₀ ≤ r) (pq pq' : ι) (z : ToType ((E.page r hr).X pq)) :
    ConcreteCategory.hom ((f.hom r hr).f pq')
        (ConcreteCategory.hom ((E.page r hr).d pq pq') z) =
      ConcreteCategory.hom ((E'.page r hr).d pq pq')
        (ConcreteCategory.hom ((f.hom r hr).f pq) z) :=
  (_root_.Stacks.Cohomology.Leray.apply_apply_eq_of_comp_eq
      (HomologicalComplex.Hom.comm (f.hom r hr) pq pq').symm z).trans
    (ConcreteCategory.comp_apply _ _ z)

/-- **A morphism of spectral sequences of abelian groups commutes with the composite edge
epimorphism**, read on elements. -/
lemma edgeEpiSteps_apply_naturality {E E' : SpectralSequence AddCommGrpCat.{v} c r₀} (f : E ⟶ E')
    (pq : ι) (r r' : ℤ) [E.HasPageInfinityAt pq] [E'.HasPageInfinityAt pq]
    [E.HasEdgeEpiAtFrom pq r] [E'.HasEdgeEpiAtFrom pq r] (hrr' : r ≤ r') (hr₀ : r₀ ≤ r)
    (hr₀' : r₀ ≤ r') (z : ToType ((E.page r hr₀).X pq)) :
    ConcreteCategory.hom ((f.hom r' hr₀').f pq)
        (ConcreteCategory.hom (E.edgeEpiSteps pq r r' hrr') z) =
      ConcreteCategory.hom (E'.edgeEpiSteps pq r r' hrr')
        (ConcreteCategory.hom ((f.hom r hr₀).f pq) z) :=
  (_root_.Stacks.Cohomology.Leray.apply_apply_eq_of_comp_eq
      (Hom.edgeEpiSteps_naturality f pq r r' hrr' hr₀) z).trans
    (ConcreteCategory.comp_apply _ _ z)

/-- **The composite edge epimorphism splits off its last one-step edge epimorphism**, read on
elements. -/
lemma edgeEpiSteps_apply_succ {E : SpectralSequence AddCommGrpCat.{v} c r₀} (pq : ι)
    (r r' r'' : ℤ) [E.HasPageInfinityAt pq] [E.HasEdgeEpiAtFrom pq r] [E.HasEdgeEpiAt pq r']
    (h₁ : r ≤ r') (h₂ : r' + 1 = r'')
    (z : ToType ((E.page r (E.le₀_of_hasEdgeEpiAtFrom pq r)).X pq)) :
    ConcreteCategory.hom (E.edgeEpiSteps pq r r'' (by omega)) z =
      ConcreteCategory.hom (E.edgeEpiStep pq r' r'' h₂)
        (ConcreteCategory.hom (E.edgeEpiSteps pq r r' h₁) z) :=
  (ConcreteCategory.congr_hom
      (E.edgeEpiSteps_eq_edgeEpiSteps_comp_edgeEpiStep pq r r' r'' h₁ h₂) z).trans
    (ConcreteCategory.comp_apply _ _ z)

/-- **A class whose image under the composite edge epimorphism `E_r^{pq'} ⟶ E_{r'}^{pq'}` is the
image of a differential that a morphism of spectral sequences kills is itself killed by that
morphism followed by the composite edge epimorphism.** -/
lemma edgeEpiSteps_map_apply_eq_zero {E E' : SpectralSequence AddCommGrpCat.{v} c r₀}
    (f : E ⟶ E') (pq pq' : ι) (r r' : ℤ)
    [E.HasPageInfinityAt pq'] [E'.HasPageInfinityAt pq']
    [E.HasEdgeEpiAtFrom pq' r] [E'.HasEdgeEpiAtFrom pq' r]
    (hrr' : r ≤ r') (hr₀ : r₀ ≤ r) (hr₀' : r₀ ≤ r')
    (z : ToType ((E.page r hr₀).X pq')) (zz : ToType ((E.page r' hr₀').X pq))
    (hzz : ConcreteCategory.hom ((E.page r' hr₀').d pq pq') zz =
      ConcreteCategory.hom (E.edgeEpiSteps pq' r r' hrr') z)
    (hg : ConcreteCategory.hom ((f.hom r' hr₀').f pq) zz = 0) :
    ConcreteCategory.hom (E'.edgeEpiSteps pq' r r' hrr')
      (ConcreteCategory.hom ((f.hom r hr₀).f pq') z) = 0 := by
  rw [← edgeEpiSteps_apply_naturality f pq' r r' hrr' hr₀ hr₀' z, ← hzz,
    d_apply_naturality f r' hr₀' pq pq' zz, hg, map_zero]

/-- **The composite edge epimorphism from a page to that same page is injective**: it is the
identification of the page with itself. -/
lemma eq_zero_of_edgeEpiSteps_apply_eq_zero {E : SpectralSequence AddCommGrpCat.{v} c r₀}
    (pq : ι) (r r' : ℤ) [E.HasPageInfinityAt pq] [E.HasEdgeEpiAtFrom pq r] (h : r = r')
    (z : ToType ((E.page r (E.le₀_of_hasEdgeEpiAtFrom pq r)).X pq))
    (hz : ConcreteCategory.hom (E.edgeEpiSteps pq r r' h.le) z = 0) : z = 0 := by
  rw [E.edgeEpiSteps_eq_of_eq pq r r' h] at hz
  exact eq_zero_of_mono_hom_apply_eq_zero
    (E.pageXIsoOfEq pq r r' h (E.le₀_of_hasEdgeEpiAtFrom pq r)).hom z hz

/-- **A class on the bottom row killed by the edge epimorphism onto the infinity page is killed by
the composite edge epimorphism to any page from which the position is stable.** -/
lemma edgeEpiSteps_apply_eq_zero_of_edgeEpi_apply_eq_zero
    {E : SpectralSequence AddCommGrpCat.{v} c r₀} (pq : ι) (r r' : ℤ) (hrr' : r ≤ r')
    [E.HasPageInfinityAt pq] [E.HasEdgeEpiAtFrom pq r]
    [E.HasEdgeMonoAtFrom pq r'] [E.HasEdgeEpiAtFrom pq r']
    (z : ToType ((E.page r (E.le₀_of_hasEdgeEpiAtFrom pq r)).X pq))
    (hz : ConcreteCategory.hom (E.edgeEpi pq r) z = 0) :
    ConcreteCategory.hom (E.edgeEpiSteps pq r r' hrr') z = 0 := by
  exact eq_zero_of_mono_hom_apply_eq_zero (E.pageInfinityIso pq r').inv _
    ((_root_.Stacks.Cohomology.Leray.apply_apply_eq_of_comp_eq
      (E.edgeEpiSteps_pageInfinityIso_inv' pq r r' hrr') z).trans hz)

end CategoryTheory.SpectralSequence

namespace CategoryTheory.CohomologicalSpectralSequenceNat

/-- **A class on the bottom row of the second page of a first-quadrant spectral sequence of
abelian groups that the composite edge epimorphism to the page `r + 1` kills is either killed
already by the composite to the page `r`, or its image there is the image of the differential from
a position off the bottom row.** -/
lemma eq_zero_or_exists_d_apply_eq
    (E : CohomologicalSpectralSequenceNat AddCommGrpCat.{v} 2) (n : ℕ) (r r' : ℤ) (hr : 2 ≤ r)
    [E.HasEdgeEpiAt (n, 0) r] (hrr' : r + 1 = r') (hr' : 2 ≤ r')
    (z : ToType ((E.page 2 le_rfl).X (n, 0)))
    (hz : ConcreteCategory.hom (E.edgeEpiSteps (n, 0) 2 r' hr') z = 0) :
    ConcreteCategory.hom (E.edgeEpiSteps (n, 0) 2 r hr) z = 0 ∨
      ∃ (p q : ℕ) (_ : 0 < q) (zz : ToType ((E.page r hr).X (p, q))),
        ConcreteCategory.hom ((E.page r hr).d (p, q) (n, 0)) zz =
          ConcreteCategory.hom (E.edgeEpiSteps (n, 0) 2 r hr) z := by
  have hy := (SpectralSequence.edgeEpiSteps_apply_succ (n, 0) 2 r r' hr hrr' z).symm.trans hz
  obtain ⟨zz, hzz⟩ := SpectralSequence.exists_d_apply_eq_of_edgeEpiStep_apply_eq_zero
    (n, 0) r r' hrr' _ hy
  rcases Nat.eq_zero_or_pos
      ((ComplexShape.spectralSequenceNat (r, 1 - r)).prev (n, 0)).2 with hq | hq
  · refine Or.inl ?_
    have hd : (E.page r hr).d ((ComplexShape.spectralSequenceNat (r, 1 - r)).prev (n, 0))
        (n, 0) = 0 := by
      refine (E.page r hr).shape _ _ (fun hrel ↦ ?_)
      simp only [ComplexShape.spectralSequenceNat_rel_iff] at hrel
      omega
    rw [← hzz, hd]
    simp
  · exact Or.inr ⟨_, _, hq, zz, hzz⟩

variable {D : Type*} [Category* D]

/-- **A composite of two morphisms of the parameter category acts on a page as the composite of
what each does**, read on an element. -/
lemma map_comp_apply (E : D ⥤ CohomologicalSpectralSequenceNat AddCommGrpCat.{v} 2) (r : ℤ)
    (hr : 2 ≤ r) {K L M : D} (g₁ : K ⟶ L) (g₂ : L ⟶ M) (pq : ℕ × ℕ)
    (z : ToType (((E.obj K).page r hr).X pq)) :
    ConcreteCategory.hom (((E.map (g₁ ≫ g₂)).hom r hr).f pq) z =
      ConcreteCategory.hom (((E.map g₂).hom r hr).f pq)
        (ConcreteCategory.hom (((E.map g₁).hom r hr).f pq) z) := by
  rw [CategoryTheory.Functor.map_comp]
  exact ConcreteCategory.comp_apply _ _ z

/-- **For a functorial first-quadrant spectral sequence of abelian groups whose terms off the
bottom row all die after a morphism of the parameter category, the kernel of the composite edge
epimorphism `E₂^{n,0} ⟶ E_r^{n,0}` dies after such a morphism.** The hypothesis `hdeg` is the
degeneration off the bottom row. -/
theorem exists_map_pageTwo_eq_zero
    (E : D ⥤ CohomologicalSpectralSequenceNat AddCommGrpCat.{v} 2) (n : ℕ)
    (hdeg : ∀ (q : ℕ), 0 < q → ∀ (r : ℤ) (hr : 2 ≤ r) (p : ℕ) (K : D)
      (x : ToType (((E.obj K).page r hr).X (p, q))),
      ∃ (L : D) (g : K ⟶ L), ConcreteCategory.hom (((E.map g).hom r hr).f (p, q)) x = 0)
    (k : ℕ) :
    ∀ (r : ℤ) (hr : 2 ≤ r) (_ : 2 + (k : ℤ) = r) (K : D)
      (z : ToType (((E.obj K).page 2 le_rfl).X (n, 0)))
      (_ : ConcreteCategory.hom ((E.obj K).edgeEpiSteps (n, 0) 2 r hr) z = 0),
      ∃ (L : D) (g : K ⟶ L),
        ConcreteCategory.hom (((E.map g).hom 2 le_rfl).f (n, 0)) z = 0 := by
  induction k with
  | zero =>
    intro r hr hk K z hz
    refine ⟨K, 𝟙 K, ?_⟩
    rw [SpectralSequence.eq_zero_of_edgeEpiSteps_apply_eq_zero (n, 0) 2 r (by omega) z hz,
      map_zero]
  | succ k ih =>
    intro r hr hk K z hz
    have hr' : (2 : ℤ) ≤ r - 1 := by omega
    have := hasEdgeEpiAt (E.obj K) (n, 0) (r - 1) (by omega) hr'
    rcases eq_zero_or_exists_d_apply_eq (E.obj K) n (r - 1) r hr' (by omega) hr z hz with
      h0 | ⟨p, q, hq, zz, hzz⟩
    · exact ih (r - 1) hr' (by omega) K z h0
    · obtain ⟨L, g, hg⟩ := hdeg q hq (r - 1) hr' p K zz
      obtain ⟨M, g', hg'⟩ := ih (r - 1) hr' (by omega) L
        (ConcreteCategory.hom (((E.map g).hom 2 le_rfl).f (n, 0)) z)
        (SpectralSequence.edgeEpiSteps_map_apply_eq_zero (E.map g) (p, q) (n, 0) 2
          (r - 1) hr' le_rfl hr' z zz hzz hg)
      exact ⟨M, g ≫ g', (map_comp_apply E 2 le_rfl g g' (n, 0) z).trans hg'⟩

/-- **For a functorial first-quadrant spectral sequence of abelian groups whose terms off the
bottom row all die after a morphism of the parameter category, the kernel of the edge epimorphism
`E₂^{n,0} ⟶ E_∞^{n,0}` dies after such a morphism.** -/
theorem exists_map_eq_zero_of_edgeEpi_apply_eq_zero
    (E : D ⥤ CohomologicalSpectralSequenceNat AddCommGrpCat.{v} 2) (n : ℕ)
    (hdeg : ∀ (q : ℕ), 0 < q → ∀ (r : ℤ) (hr : 2 ≤ r) (p : ℕ) (K : D)
      (x : ToType (((E.obj K).page r hr).X (p, q))),
      ∃ (L : D) (g : K ⟶ L), ConcreteCategory.hom (((E.map g).hom r hr).f (p, q)) x = 0)
    (K : D) (z : ToType (((E.obj K).page 2 le_rfl).X (n, 0)))
    (hz : ConcreteCategory.hom ((E.obj K).edgeEpi (n, 0) 2) z = 0) :
    ∃ (L : D) (g : K ⟶ L),
      ConcreteCategory.hom (((E.map g).hom 2 le_rfl).f (n, 0)) z = 0 := by
  have : (E.obj K).HasEdgeMonoAtFrom (n, 0) ((n : ℤ) + 2) :=
    hasEdgeMonoAtFrom (E.obj K) (n, 0) ((n : ℤ) + 2)
  have : (E.obj K).HasEdgeEpiAtFrom (n, 0) ((n : ℤ) + 2) :=
    hasEdgeEpiAtFrom (E.obj K) (n, 0) ((n : ℤ) + 2)
  exact exists_map_pageTwo_eq_zero E n hdeg n ((n : ℤ) + 2) (by omega) (by omega) K z
    (SpectralSequence.edgeEpiSteps_apply_eq_zero_of_edgeEpi_apply_eq_zero (n, 0) 2 ((n : ℤ) + 2)
      (by omega) z hz)

end CategoryTheory.CohomologicalSpectralSequenceNat

/-! ### The hypercoverings of an object form a connected category -/

namespace Stacks.CategoryTheory.Hypercovering

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

/-- **The hypercoverings of `X` form a connected category.** -/
instance isConnected_hypercoverings (J : Pretopology C)
    [Precoverage.IsStableUnderComposition J.toPrecoverage] (X : C) :
    IsConnected (Hypercoverings.{w} J X) := by
  have : Nonempty (Hypercoverings.{w} J X) := nonempty_hypercoverings.{w} J X
  refine IsConnected.of_constant_of_preserves_morphisms (fun {α} F hF K L ↦ ?_)
  have hKL : IsHypercovering J (K.obj ⨯ L.obj) :=
    IsHypercovering.prod J K.property L.property
  have hfst := hF (j₁ := ⟨K.obj ⨯ L.obj, hKL⟩) (j₂ := K) (ObjectProperty.homMk Limits.prod.fst)
  have hsnd := hF (j₁ := ⟨K.obj ⨯ L.obj, hKL⟩) (j₂ := L) (ObjectProperty.homMk Limits.prod.snd)
  exact hfst.symm.trans hsnd

end Stacks.CategoryTheory.Hypercovering

/-! ### Degree-zero cohomology is the colimit of hypercovering Čech cohomology -/

namespace Stacks.CategoryTheory.Hypercovering.Functorial

variable {C : Type v} [SmallCategory C] [HasPullbacks C] (X : C) (J : Pretopology C)

/-- Abelian sheaves of the right size on a small site have `Ext` groups in that size. -/
local instance hasExtSmallSiteColimit :
    HasExt.{v} (Sheaf J.toGrothendieck AddCommGrpCat.{v}) :=
  hasExtSmallSitePage J

/-- **Cohomology `H^n(X, -)` as a functor of the abelian sheaf**: the value at `X` of the
degree-`n` cohomology presheaf. -/
def sheafCohomologyAtObject (n : ℕ) :
    Sheaf J.toGrothendieck AddCommGrpCat.{v} ⥤ AddCommGrpCat.{v} :=
  Sheaf.cohomologyPresheafFunctor J.toGrothendieck n ⋙
    (evaluation Cᵒᵖ AddCommGrpCat.{v}).obj (op X)

/-- **For a hypercovering `K` of `X` the corner `E₂^{0,0}` of its spectral sequence is
`H⁰(X, 𝓕)`**, naturally in `K` and in `𝓕` at once. -/
def cechCohomologyZeroIsoCohomology :
    pageTwoHypercovering.{v} X J 0 0 ≅ hypercoveringCohomologyFunctor X J 0 :=
  (hypercoveringPageTwoIso.{v} X J 0 0).symm ≪≫
    (hypercoveringCohomologyAbutment X J).pageTwoCornerIso

/-- **The diagram `K ↦ Ȟ⁰(K, H⁰(-))` of degree-zero hypercovering Čech cohomology**, indexed by
the opposite of the category of hypercoverings of `X`. -/
def cechCohomologyZeroDiagram :
    (HypercoveringCat X J)ᵒᵖ ⥤
      (Sheaf J.toGrothendieck AddCommGrpCat.{v} ⥤ AddCommGrpCat.{v}) :=
  Functor.curryObj (pageTwoHypercovering.{v} X J 0 0)

/-- **The abutment of the hypercovering spectral sequence does not move with the
hypercovering**: a morphism of hypercoverings acts on `H^n(X, -)` by the identity. -/
lemma curryObj_hypercoveringCohomologyFunctor_map (n : ℕ)
    {K L : (HypercoveringCat X J)ᵒᵖ} (φ : K ⟶ L) :
    (Functor.curryObj (hypercoveringCohomologyFunctor X J n)).map φ =
      𝟙 ((Functor.curryObj (hypercoveringCohomologyFunctor X J n)).obj K) := by
  refine NatTrans.ext (funext fun F ↦ ?_)
  change (hypercoveringCohomologyFunctor X J n).map (φ ×ₘ 𝟙 F) = _
  change ((Sheaf.cohomologyPresheafFunctor J.toGrothendieck n).map (𝟙 F)).app (op X) = _
  rw [CategoryTheory.Functor.map_id, NatTrans.id_app]
  rfl

/-- The abutment `H⁰(X, -)` of the hypercovering spectral sequence does not depend on the
hypercovering, so as a diagram on the hypercoverings it is constant. -/
def hypercoveringCohomologyZeroIsoConst :
    Functor.curryObj (hypercoveringCohomologyFunctor X J 0) ≅
      (Functor.const (HypercoveringCat X J)ᵒᵖ).obj (sheafCohomologyAtObject X J 0) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun {_ _} φ ↦
    (Category.comp_id _).trans
      ((curryObj_hypercoveringCohomologyFunctor_map X J 0 φ).trans
        (Category.id_comp _).symm))

/-- **The canonical cocone exhibiting `H⁰(X, -)` on the diagram of degree-zero hypercovering
Čech cohomology**: its leg at a hypercovering `K` is the identification of `Ȟ⁰(K, H⁰(-))` with
`H⁰(X, -)`. -/
def cechCohomologyZeroCocone : Cocone (cechCohomologyZeroDiagram X J) :=
  Cocone.mk (sheafCohomologyAtObject X J 0)
    (Functor.curry.mapIso (cechCohomologyZeroIsoCohomology X J) ≪≫
      hypercoveringCohomologyZeroIsoConst X J).hom

/-- For a site with fibre products and an object `X`, the functor `𝓕 ↦ H⁰(X, 𝓕)` on abelian
sheaves is the colimit over all hypercoverings `K` of `X` of the functors `𝓕 ↦ Ȟ⁰(K, H⁰(𝓕))`,
the cocone being the canonical identification of each `Ȟ⁰(K, H⁰(-))` with `H⁰(X, -)`. -/
@[stacks 01H0 "the case i = 0: colim over hypercoverings of Ȟ⁰(K, H⁰(-)) is H⁰(X, -), as \
functors on Ab(C); the hypotheses carried are fibre products in C and stability of the \
pretopology under composition"]
def isColimit_cechCohomologyZeroCocone
    [Precoverage.IsStableUnderComposition J.toPrecoverage] :
    IsColimit (cechCohomologyZeroCocone X J) :=
  isColimit_of_isIso_cocone_ι _ (fun K ↦
    inferInstanceAs (IsIso ((Functor.curry.mapIso (cechCohomologyZeroIsoCohomology X J) ≪≫
      hypercoveringCohomologyZeroIsoConst X J).hom.app K)))

/-! ### The infinity page off the bottom row dies after a refinement -/

/-- The differentials into `(p, q)` have all vanished on the page `r` as soon as `p + 1 ≤ r`, so
the infinity page of the hypercovering spectral sequence at `(p, q)` can be read off on that
page. -/
lemma hasEdgeMonoAtFrom_hypercoveringSpectralSequence (pq : ℕ × ℕ) (r : ℤ)
    (hp : (pq.1 : ℤ) + 1 ≤ r) (hr : 2 ≤ r)
    (KF : (HypercoveringCat X J)ᵒᵖ × Sheaf J.toGrothendieck AddCommGrpCat.{v}) :
    ((hypercoveringSpectralSequence X J).obj KF).HasEdgeMonoAtFrom pq r :=
  _root_.CategoryTheory.CohomologicalSpectralSequenceNat.hasEdgeMonoAtFrom
    _ pq r hp hr

/-- The differentials out of `(p, q)` have all vanished on the page `r` as soon as `q + 2 ≤ r`. -/
lemma hasEdgeEpiAtFrom_hypercoveringSpectralSequence (pq : ℕ × ℕ) (r : ℤ)
    (hq : (pq.2 : ℤ) + 2 ≤ r) (hr : 2 ≤ r)
    (KF : (HypercoveringCat X J)ᵒᵖ × Sheaf J.toGrothendieck AddCommGrpCat.{v}) :
    ((hypercoveringSpectralSequence X J).obj KF).HasEdgeEpiAtFrom pq r :=
  _root_.CategoryTheory.CohomologicalSpectralSequenceNat.hasEdgeEpiAtFrom
    _ pq r hq hr

/-- **Every element of the infinity page `E_∞^{p,q}` of the hypercovering spectral sequence dies
after a refinement of the hypercovering**, for `q > 0`. -/
theorem exists_hypercovering_map_pageInfinity_eq_zero
    [Precoverage.IsStableUnderComposition J.toPrecoverage]
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{v}) (q : ℕ) (hq : 0 < q) (p : ℕ)
    (K : (HypercoveringCat X J)ᵒᵖ)
    (x : ToType (((hypercoveringSpectralSequence X J).obj (K, F)).pageInfinity (p, q))) :
    ∃ (L : (HypercoveringCat X J)ᵒᵖ) (g : K ⟶ L),
      ConcreteCategory.hom (_root_.CategoryTheory.SpectralSequence.Hom.mapPageInfinity
        ((hypercoveringSpectralSequence X J).map (g ×ₘ 𝟙 F)) (p, q)) x = 0 := by
  have hr : (2 : ℤ) ≤ (p : ℤ) + (q : ℤ) + 2 := by omega
  have := hasEdgeMonoAtFrom_hypercoveringSpectralSequence X J (p, q)
    ((p : ℤ) + (q : ℤ) + 2) (by omega) hr (K, F)
  have := hasEdgeEpiAtFrom_hypercoveringSpectralSequence X J (p, q)
    ((p : ℤ) + (q : ℤ) + 2) (by omega) hr (K, F)
  obtain ⟨L, g, hg⟩ := exists_hypercovering_map_page_eq_zero X J F q hq
    ((p : ℤ) + (q : ℤ) + 2) hr p K
    (ConcreteCategory.hom (((hypercoveringSpectralSequence X J).obj (K, F)).pageInfinityIso
      (p, q) ((p : ℤ) + (q : ℤ) + 2)).hom x)
  have := hasEdgeMonoAtFrom_hypercoveringSpectralSequence X J (p, q)
    ((p : ℤ) + (q : ℤ) + 2) (by omega) hr (L, F)
  have := hasEdgeEpiAtFrom_hypercoveringSpectralSequence X J (p, q)
    ((p : ℤ) + (q : ℤ) + 2) (by omega) hr (L, F)
  exact ⟨L, g, _root_.Stacks.Cohomology.Leray.mapPageInfinity_apply_eq_zero
    ((hypercoveringSpectralSequence X J).map (g ×ₘ 𝟙 F)) p q ((p : ℤ) + (q : ℤ) + 2) hr x hg⟩

/-! ### The filtration of the abutment collapses onto its bottom step in the colimit -/

/-- **Every element of the graded piece `gr^p H^{p+q}(X, 𝓕)` of the abutment filtration of a
hypercovering dies after a refinement of the hypercovering**, for `q > 0`. -/
theorem exists_hypercovering_map_gradedPiece_eq_zero
    [Precoverage.IsStableUnderComposition J.toPrecoverage]
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{v}) (q : ℕ) (hq : 0 < q) (p : ℕ)
    (K : (HypercoveringCat X J)ᵒᵖ)
    (y : ToType ((FilteredObject.gr (p : ℤ)).obj
      (((hypercoveringCohomologyAbutment X J).filtration (p + q)).obj (K, F)))) :
    ∃ (L : (HypercoveringCat X J)ᵒᵖ) (g : K ⟶ L),
      ConcreteCategory.hom ((FilteredObject.gr (p : ℤ)).map
        (((hypercoveringCohomologyAbutment X J).filtration (p + q)).map (g ×ₘ 𝟙 F))) y = 0 := by
  obtain ⟨L, g, hg⟩ := exists_hypercovering_map_pageInfinity_eq_zero X J F q hq p K
    (ConcreteCategory.hom ((hypercoveringCohomologyAbutment X J).gradedIso (K, F) p q).inv y)
  exact ⟨L, g, _root_.Stacks.Cohomology.Leray.gradedPiece_map_apply_eq_zero
    (hypercoveringCohomologyAbutment X J) (g ×ₘ 𝟙 F) p q y hg⟩

/-- **The filtration of `H^{p+q}(X, 𝓕)` carried by a hypercovering descends one step after a
refinement**, for `q > 0`: an element of the `p`-th step `F^p H^{p+q}(X, 𝓕)` becomes, after a
refinement `g : K ⟶ L` of the hypercovering, the image of an element of the `(p+1)`-st step
`F^{p+1} H^{p+q}(X, 𝓕)` of the filtration carried by `L`. -/
theorem exists_hypercovering_map_filtration_step
    [Precoverage.IsStableUnderComposition J.toPrecoverage]
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{v}) (q : ℕ) (hq : 0 < q) (p : ℕ)
    (K : (HypercoveringCat X J)ᵒᵖ)
    (η : ToType ((((hypercoveringCohomologyAbutment X J).filtration (p + q)).obj
      (K, F)).filtration.obj (op (p : ℤ)))) :
    ∃ (L : (HypercoveringCat X J)ᵒᵖ) (g : K ⟶ L)
      (η' : ToType ((((hypercoveringCohomologyAbutment X J).filtration (p + q)).obj
        (L, F)).filtration.obj (op ((p : ℤ) + 1)))),
      ConcreteCategory.hom ((((hypercoveringCohomologyAbutment X J).filtration (p + q)).obj
          (L, F)).filtration.step (FilteredObject.succHom (p : ℤ))) η' =
        ConcreteCategory.hom ((((hypercoveringCohomologyAbutment X J).filtration (p + q)).map
          (g ×ₘ 𝟙 F)).natTrans.app (op (p : ℤ))) η := by
  obtain ⟨L, g, hg⟩ := exists_hypercovering_map_gradedPiece_eq_zero X J F q hq p K
    (ConcreteCategory.hom (FilteredObject.grMapπ (FilteredObject.succHom (p : ℤ))
      (((hypercoveringCohomologyAbutment X J).filtration (p + q)).obj (K, F))) η)
  obtain ⟨η', hη'⟩ := _root_.Stacks.Cohomology.Leray.exists_step_apply_eq_natTrans_app_apply
    (((hypercoveringCohomologyAbutment X J).filtration (p + q)).map (g ×ₘ 𝟙 F)) (p : ℤ) η hg
  exact ⟨L, g, η', hη'⟩

/-! ### The Čech edge map is surjective in the colimit over the hypercoverings -/

/-- **A refinement of the hypercovering acts on a cohomology class by the identity.** -/
lemma hypercoveringCohomologyFunctor_map_apply (n : ℕ)
    {K L : (HypercoveringCat X J)ᵒᵖ} (φ : K ⟶ L)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{v})
    (w : ToType ((hypercoveringCohomologyFunctor X J n).obj (K, F))) :
    ConcreteCategory.hom ((hypercoveringCohomologyFunctor X J n).map (φ ×ₘ 𝟙 F)) w = w :=
  (ConcreteCategory.congr_hom (hypercoveringCohomologyFunctor_map_eq_id X J n φ F) w).trans
    (ConcreteCategory.id_apply w)

/-- **Composing two refinements of the hypercovering acts on `H^n(X, -)` as either one
does.** -/
lemma hypercoveringCohomologyFunctor_map_comp (n : ℕ)
    {K L M : (HypercoveringCat X J)ᵒᵖ} (g₁ : K ⟶ L) (g₂ : L ⟶ M)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{v}) :
    (hypercoveringCohomologyFunctor X J n).map (g₁ ×ₘ 𝟙 F) ≫
        (hypercoveringCohomologyFunctor X J n).map (g₂ ×ₘ 𝟙 F) =
      (hypercoveringCohomologyFunctor X J n).map ((g₁ ≫ g₂) ×ₘ 𝟙 F) :=
  ConcreteCategory.hom_ext _ _ fun w ↦
    (ConcreteCategory.comp_apply _ _ w).trans
      ((hypercoveringCohomologyFunctor_map_apply X J n g₂ F
          (ConcreteCategory.hom
            ((hypercoveringCohomologyFunctor X J n).map (g₁ ×ₘ 𝟙 F)) w)).trans
        ((hypercoveringCohomologyFunctor_map_apply X J n g₁ F w).trans
          (hypercoveringCohomologyFunctor_map_apply X J n (g₁ ≫ g₂) F w).symm))

/-- `exists_hypercovering_map_filtration_step` with the filtration step carried by an integer
index strictly below the total degree. -/
theorem exists_hypercovering_map_filtration_stepInt
    [Precoverage.IsStableUnderComposition J.toPrecoverage]
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{v}) (n : ℕ) (j : ℤ) (hj : 0 ≤ j) (hjn : j < n)
    (K : (HypercoveringCat X J)ᵒᵖ)
    (η : ToType ((((hypercoveringCohomologyAbutment X J).filtration n).obj
      (K, F)).filtration.obj (op j))) :
    ∃ (L : (HypercoveringCat X J)ᵒᵖ) (g : K ⟶ L)
      (η' : ToType ((((hypercoveringCohomologyAbutment X J).filtration n).obj
        (L, F)).filtration.obj (op (j + 1)))),
      ConcreteCategory.hom ((((hypercoveringCohomologyAbutment X J).filtration n).obj
          (L, F)).filtration.step (FilteredObject.succHom j)) η' =
        ConcreteCategory.hom ((((hypercoveringCohomologyAbutment X J).filtration n).map
          (g ×ₘ 𝟙 F)).natTrans.app (op j)) η := by
  obtain ⟨p, rfl⟩ : ∃ p : ℕ, j = (p : ℤ) := ⟨j.toNat, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, n = p + q := ⟨n - p, by omega⟩
  exact exists_hypercovering_map_filtration_step X J F q (by omega) p K η

/-- **Every cohomology class in a step `F^j H^n(X, 𝓕)` of the abutment filtration of a
hypercovering becomes, after a refinement of the hypercovering, a class in the bottom step
`F^n H^n(X, 𝓕)`**, for `0 ≤ j` and `j + k = n`. -/
theorem exists_hypercovering_map_stepToAbutment_eq
    [Precoverage.IsStableUnderComposition J.toPrecoverage]
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{v}) (n k : ℕ) :
    ∀ (j : ℤ) (_ : 0 ≤ j) (_ : j + k = n) (K : (HypercoveringCat X J)ᵒᵖ)
      (η : ToType ((((hypercoveringCohomologyAbutment X J).filtration n).obj
        (K, F)).filtration.obj (op j))),
      ∃ (L : (HypercoveringCat X J)ᵒᵖ) (g : K ⟶ L)
        (η' : ToType ((((hypercoveringCohomologyAbutment X J).filtration n).obj
          (L, F)).filtration.obj (op (n : ℤ)))),
        ConcreteCategory.hom
            (((hypercoveringCohomologyAbutment X J).stepToAbutment n (n : ℤ)).app (L, F)) η' =
          ConcreteCategory.hom ((hypercoveringCohomologyFunctor X J n).map (g ×ₘ 𝟙 F))
            (ConcreteCategory.hom
              (((hypercoveringCohomologyAbutment X J).stepToAbutment n j).app (K, F)) η) := by
  induction k with
  | zero =>
    intro j _ hjn K η
    obtain rfl : j = (n : ℤ) := by omega
    exact ⟨K, 𝟙 K, η, (hypercoveringCohomologyFunctor_map_apply X J n (𝟙 K) F _).symm⟩
  | succ k ih =>
    intro j hj hjn K η
    obtain ⟨L₁, g₁, η₁, hη₁⟩ :=
      exists_hypercovering_map_filtration_stepInt X J F n j hj (by omega) K η
    obtain ⟨L₂, g₂, η', hη'⟩ := ih (j + 1) (by omega) (by omega) L₁ η₁
    refine ⟨L₂, g₁ ≫ g₂, η', hη'.trans ?_⟩
    have e₁ := _root_.Stacks.Cohomology.Leray.apply_apply_eq_of_comp_eq
      ((hypercoveringCohomologyAbutment X J).step_comp_stepToAbutment n j (L₁, F)) η₁
    rw [hη₁] at e₁
    have e₂ := _root_.Stacks.Cohomology.Leray.apply_apply_eq_of_comp_eq
      ((hypercoveringCohomologyAbutment X J).stepToAbutment_naturality n j (g₁ ×ₘ 𝟙 F)) η
    have e₃ := ConcreteCategory.comp_apply
      (((hypercoveringCohomologyAbutment X J).stepToAbutment n j).app (K, F))
      ((hypercoveringCohomologyFunctor X J n).map (g₁ ×ₘ 𝟙 F))
      η
    rw [← e₁, e₂, e₃]
    exact _root_.Stacks.Cohomology.Leray.apply_apply_eq_of_comp_eq
      (hypercoveringCohomologyFunctor_map_comp X J n g₁ g₂ F) _

/-- **The Čech-to-cohomology edge map at a hypercovering and a coefficient sheaf is the two
second-page identifications followed by the bottom-row edge map of the abutment**, with the two
identifications grouped together. -/
lemma hypercoveringCechEdge_app_eq (n : ℕ)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{v}) (L : (HypercoveringCat X J)ᵒᵖ) :
    (hypercoveringCechEdge.{v} X J n).app (L, F) =
      ((hypercoveringPageTwoZeroIso.{v} X J n).inv.app (L, F) ≫
          (pageTwoIsoHypercovering X J n 0 F L).inv) ≫
        ((hypercoveringCohomologyAbutment X J).bottomRowEdge n).app (L, F) :=
  (Category.assoc _ _ _).symm

/-- **The Čech-to-cohomology edge map hits every element of the bottom step `F^n H^n(X, 𝓕)` of
the abutment filtration.** -/
lemma exists_hypercoveringCechEdge_app_apply_eq (n : ℕ)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{v}) (L : (HypercoveringCat X J)ᵒᵖ)
    (η : ToType ((((hypercoveringCohomologyAbutment X J).filtration n).obj
      (L, F)).filtration.obj (op (n : ℤ)))) :
    ∃ c : ToType ((cechHypercovering.{v} X J n).obj (L, F)),
      ConcreteCategory.hom ((hypercoveringCechEdge.{v} X J n).app (L, F)) c =
        ConcreteCategory.hom
          (((hypercoveringCohomologyAbutment X J).stepToAbutment n (n : ℤ)).app (L, F)) η := by
  obtain ⟨c, hc⟩ := _root_.Stacks.Cohomology.Leray.exists_apply_eq_stepToAbutment_apply
    (hypercoveringCohomologyAbutment X J) n (L, F)
    ((hypercoveringPageTwoZeroIso.{v} X J n).inv.app (L, F) ≫
      (pageTwoIsoHypercovering X J n 0 F L).inv)
    (epi_comp' (inferInstanceAs (Epi ((hypercoveringPageTwoZeroIso.{v} X J n).app (L, F)).inv))
      (inferInstanceAs (Epi (pageTwoIsoHypercovering X J n 0 F L).inv))) η
  refine ⟨c, ?_⟩
  rw [hypercoveringCechEdge_app_eq X J n F L]
  exact hc

/-- Every cohomology class in `H^n(X, 𝓕)` is, after a refinement of the hypercovering, the image
under the Čech-to-cohomology edge map `hypercoveringCechEdge` of a Čech class `Ȟ^n(L, 𝓕)`. -/
theorem exists_hypercovering_map_hypercoveringCechEdge_apply_eq
    [Precoverage.IsStableUnderComposition J.toPrecoverage]
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{v}) (n : ℕ) (K : (HypercoveringCat X J)ᵒᵖ)
    (x : ToType ((hypercoveringCohomologyFunctor X J n).obj (K, F))) :
    ∃ (L : (HypercoveringCat X J)ᵒᵖ) (g : K ⟶ L)
      (c : ToType ((cechHypercovering.{v} X J n).obj (L, F))),
      ConcreteCategory.hom ((hypercoveringCechEdge.{v} X J n).app (L, F)) c =
        ConcreteCategory.hom ((hypercoveringCohomologyFunctor X J n).map (g ×ₘ 𝟙 F)) x := by
  have := (hypercoveringCohomologyAbutment X J).isIso_stepToAbutment_zero n (K, F)
  have hx : ConcreteCategory.hom
      (((hypercoveringCohomologyAbutment X J).stepToAbutment n 0).app (K, F))
      (ConcreteCategory.hom
        (inv (((hypercoveringCohomologyAbutment X J).stepToAbutment n 0).app (K, F))) x) = x :=
    (_root_.Stacks.Cohomology.Leray.apply_apply_eq_of_comp_eq (IsIso.inv_hom_id _) x).trans
      (ConcreteCategory.id_apply _)
  obtain ⟨L, g, η', hη'⟩ := exists_hypercovering_map_stepToAbutment_eq X J F n n 0 le_rfl
    (by omega) K (ConcreteCategory.hom
      (inv (((hypercoveringCohomologyAbutment X J).stepToAbutment n 0).app (K, F))) x)
  rw [hx] at hη'
  obtain ⟨c, hc⟩ := exists_hypercoveringCechEdge_app_apply_eq X J n F L η'
  exact ⟨L, g, c, hc.trans hη'⟩

/-! ### The Čech edge map is injective in the colimit over the hypercoverings -/

/-- **Two refinements of the hypercovering with the coefficient sheaf fixed compose to one.** -/
lemma prod_mkHom_comp {K L M : (HypercoveringCat X J)ᵒᵖ} (g₁ : K ⟶ L) (g₂ : L ⟶ M)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{v}) :
    (g₁ ×ₘ 𝟙 F) ≫ (g₂ ×ₘ 𝟙 F) = (g₁ ≫ g₂) ×ₘ 𝟙 F :=
  _root_.CategoryTheory.Prod.hom_ext rfl (Category.comp_id _)

/-- **The hypercoverings of `X` sitting over a fixed abelian sheaf `𝓕`**, as the functor
`K ↦ (K, 𝓕)` into the parameter category of the hypercovering spectral sequence. -/
@[simps]
def atSheaf (F : Sheaf J.toGrothendieck AddCommGrpCat.{v}) :
    (HypercoveringCat X J)ᵒᵖ ⥤
      (HypercoveringCat X J)ᵒᵖ × Sheaf J.toGrothendieck AddCommGrpCat.{v} where
  obj K := (K, F)
  map g := g ×ₘ 𝟙 F
  map_id _ := rfl
  map_comp g₁ g₂ := (prod_mkHom_comp X J g₁ g₂ F).symm

/-- **The hypercovering spectral sequence at a fixed coefficient sheaf**, as a functor of the
hypercovering alone: `atSheaf` followed by the spectral sequence. -/
def hypercoveringSpectralSequenceAt (F : Sheaf J.toGrothendieck AddCommGrpCat.{v}) :
    (HypercoveringCat X J)ᵒᵖ ⥤ E₂CohomologicalSpectralSequenceNat AddCommGrpCat.{v} :=
  atSheaf X J F ⋙ hypercoveringSpectralSequence X J

/-- The spectral sequence at a fixed coefficient sheaf is the spectral sequence of the pair. -/
lemma hypercoveringSpectralSequenceAt_obj (F : Sheaf J.toGrothendieck AddCommGrpCat.{v})
    (K : (HypercoveringCat X J)ᵒᵖ) :
    (hypercoveringSpectralSequenceAt X J F).obj K =
      (hypercoveringSpectralSequence X J).obj (K, F) :=
  rfl

/-- A refinement acts on the spectral sequence at a fixed coefficient sheaf as the refinement
paired with the identity of the sheaf acts on the spectral sequence of the pair. -/
lemma hypercoveringSpectralSequenceAt_map (F : Sheaf J.toGrothendieck AddCommGrpCat.{v})
    {K L : (HypercoveringCat X J)ᵒᵖ} (g : K ⟶ L) :
    (hypercoveringSpectralSequenceAt X J F).map g =
      (hypercoveringSpectralSequence X J).map (g ×ₘ 𝟙 F) :=
  rfl

/-- **`exists_hypercovering_map_page_eq_zero` at the spectral sequence of a fixed coefficient
sheaf**: for `q > 0` and every page `r ≥ 2`, every element of `E_r^{p,q}` dies after a refinement
of the hypercovering. -/
theorem exists_hypercoveringSpectralSequenceAt_map_page_eq_zero
    [Precoverage.IsStableUnderComposition J.toPrecoverage]
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{v}) (q : ℕ) (hq : 0 < q) (r : ℤ) (hr : 2 ≤ r)
    (p : ℕ) (K : (HypercoveringCat X J)ᵒᵖ)
    (x : ToType ((((hypercoveringSpectralSequenceAt X J F).obj K).page r hr).X (p, q))) :
    ∃ (L : (HypercoveringCat X J)ᵒᵖ) (g : K ⟶ L),
      ConcreteCategory.hom
        ((((hypercoveringSpectralSequenceAt X J F).map g).hom r hr).f (p, q)) x = 0 :=
  exists_hypercovering_map_page_eq_zero X J F q hq r hr p K x

/-- **The Čech cohomology of a hypercovering is the bottom row of the second page of its spectral
sequence**, as a single isomorphism whose target is spelled the way the spectral sequence presents
the page: the second-page identification `pageTwoIsoHypercovering` and the identification
`hypercoveringPageTwoZeroIso` of the bottom row's coefficients with the sheaf itself, both
inverted. -/
def cechIsoPageTwoZero (n : ℕ) (F : Sheaf J.toGrothendieck AddCommGrpCat.{v})
    (K : (HypercoveringCat X J)ᵒᵖ) :
    (cechHypercovering.{v} X J n).obj (K, F) ≅
      (((hypercoveringSpectralSequence X J).obj (K, F)).page 2 le_rfl).X (n, 0) :=
  ((hypercoveringPageTwoZeroIso.{v} X J n).app (K, F)).symm ≪≫
    (pageTwoIsoHypercovering X J n 0 F K).symm

/-- **The Čech-to-cohomology edge map is `cechIsoPageTwoZero` followed by the bottom-row edge map
of the abutment.** -/
lemma cechIsoPageTwoZero_hom_comp_bottomRowEdge (n : ℕ)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{v}) (K : (HypercoveringCat X J)ᵒᵖ) :
    (cechIsoPageTwoZero X J n F K).hom ≫
        ((hypercoveringCohomologyAbutment X J).bottomRowEdge n).app (K, F) =
      (hypercoveringCechEdge.{v} X J n).app (K, F) :=
  (hypercoveringCechEdge_app_eq X J n F K).symm

/-- **`cechIsoPageTwoZero` is natural in the hypercovering**: the canonical pullback map on Čech
cohomology corresponds to the map a refinement induces on the second page at `(n, 0)`. -/
lemma cechHypercovering_map_comp_cechIsoPageTwoZero_hom (n : ℕ)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{v}) {K L : (HypercoveringCat X J)ᵒᵖ} (g : K ⟶ L) :
    (cechHypercovering.{v} X J n).map (g ×ₘ 𝟙 F) ≫ (cechIsoPageTwoZero X J n F L).hom =
      (cechIsoPageTwoZero X J n F K).hom ≫
        (((hypercoveringSpectralSequence X J).map (g ×ₘ 𝟙 F)).hom 2 le_rfl).f (n, 0) := by
  have h₁ := (hypercoveringPageTwoZeroIso.{v} X J n).inv.naturality (g ×ₘ 𝟙 F)
  have h₂ : (pageTwoHypercovering.{v} X J n 0).map (g ×ₘ 𝟙 F) ≫
      (pageTwoIsoHypercovering X J n 0 F L).inv =
      (pageTwoIsoHypercovering X J n 0 F K).inv ≫
        (((hypercoveringSpectralSequence X J).map (g ×ₘ 𝟙 F)).hom 2 le_rfl).f (n, 0) := by
    rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
    exact (pageTwoIsoHypercovering_naturality X J n 0 F g).symm
  change (cechHypercovering.{v} X J n).map (g ×ₘ 𝟙 F) ≫
      ((hypercoveringPageTwoZeroIso.{v} X J n).inv.app (L, F) ≫
        (pageTwoIsoHypercovering X J n 0 F L).inv) =
      ((hypercoveringPageTwoZeroIso.{v} X J n).inv.app (K, F) ≫
        (pageTwoIsoHypercovering X J n 0 F K).inv) ≫
        (((hypercoveringSpectralSequence X J).map (g ×ₘ 𝟙 F)).hom 2 le_rfl).f (n, 0)
  rw [Category.assoc, ← Category.assoc, h₁, Category.assoc, h₂]

open _root_.CategoryTheory.CohomologicalSpectralSequenceNat in
/-- A Čech class in `Ȟ^n(K, 𝓕)` that the Čech-to-cohomology edge map `hypercoveringCechEdge`
kills dies after a refinement of the hypercovering. -/
theorem exists_hypercovering_map_cechHypercovering_apply_eq_zero
    [Precoverage.IsStableUnderComposition J.toPrecoverage]
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{v}) (n : ℕ) (K : (HypercoveringCat X J)ᵒᵖ)
    (c : ToType ((cechHypercovering.{v} X J n).obj (K, F)))
    (hc : ConcreteCategory.hom ((hypercoveringCechEdge.{v} X J n).app (K, F)) c = 0) :
    ∃ (L : (HypercoveringCat X J)ᵒᵖ) (g : K ⟶ L),
      ConcreteCategory.hom ((cechHypercovering.{v} X J n).map (g ×ₘ 𝟙 F)) c = 0 := by
  have hz : ConcreteCategory.hom
      (((hypercoveringCohomologyAbutment X J).bottomRowEdge n).app (K, F))
      (ConcreteCategory.hom (cechIsoPageTwoZero X J n F K).hom c) = 0 :=
    (_root_.Stacks.Cohomology.Leray.apply_apply_eq_of_comp_eq
      (cechIsoPageTwoZero_hom_comp_bottomRowEdge X J n F K) c).trans hc
  have hz' := _root_.Stacks.Cohomology.Leray.edgeEpi_apply_eq_zero_of_bottomRowEdge_apply_eq_zero
    (hypercoveringCohomologyAbutment X J) n (K, F)
    (ConcreteCategory.hom (cechIsoPageTwoZero X J n F K).hom c) hz
  obtain ⟨L, g, hg⟩ :=
    exists_map_eq_zero_of_edgeEpi_apply_eq_zero
      (hypercoveringSpectralSequenceAt X J F) n
      (exists_hypercoveringSpectralSequenceAt_map_page_eq_zero X J F) K
      (ConcreteCategory.hom (cechIsoPageTwoZero X J n F K).hom c) hz'
  have hg' : ConcreteCategory.hom
      ((((hypercoveringSpectralSequence X J).map (g ×ₘ 𝟙 F)).hom 2 le_rfl).f (n, 0))
      (ConcreteCategory.hom (cechIsoPageTwoZero X J n F K).hom c) = 0 := hg
  refine ⟨L, g, eq_zero_of_mono_hom_apply_eq_zero (cechIsoPageTwoZero X J n F L).hom _ ?_⟩
  exact (_root_.Stacks.Cohomology.Leray.apply_apply_eq_of_comp_eq
    (cechHypercovering_map_comp_cechIsoPageTwoZero_hom X J n F g) c).trans
    ((ConcreteCategory.comp_apply _ _ c).trans hg')

/-! ### Sheaf cohomology in every degree is the colimit of hypercovering Čech cohomology -/

/-- **The diagram `K ↦ Ȟ^n(K, 𝓕)` of hypercovering Čech cohomology at a fixed abelian sheaf
`𝓕`**, indexed by the opposite of the category of hypercoverings of `X`. -/
abbrev cechDiagramAtSheaf (n : ℕ) (F : Sheaf J.toGrothendieck AddCommGrpCat.{v}) :
    (HypercoveringCat X J)ᵒᵖ ⥤ AddCommGrpCat.{v} :=
  atSheaf X J F ⋙ cechHypercovering.{v} X J n

/-- **The cocone of Čech-to-cohomology edge maps on the diagram of Čech cohomology**, with vertex
`H^n(X, 𝓕)`. -/
def cechCoconeAtSheaf (n : ℕ) (F : Sheaf J.toGrothendieck AddCommGrpCat.{v}) :
    Cocone (cechDiagramAtSheaf X J n F) where
  pt := (sheafCohomologyAtObject X J n).obj F
  ι :=
    { app := fun K ↦ (hypercoveringCechEdge.{v} X J n).app (K, F)
      naturality := fun K _ g ↦
        (((hypercoveringCechEdge.{v} X J n).naturality (g ×ₘ 𝟙 F)).trans
          ((congrArg (fun u ↦ (hypercoveringCechEdge.{v} X J n).app (K, F) ≫ u)
              (hypercoveringCohomologyFunctor_map_eq_id X J n g F)).trans
            (Category.comp_id _))).trans (Category.comp_id _).symm }

/-- The leg of `cechCoconeAtSheaf` at a hypercovering is the Čech-to-cohomology edge map there. -/
@[simp]
lemma cechCoconeAtSheaf_ι_app (n : ℕ) (F : Sheaf J.toGrothendieck AddCommGrpCat.{v})
    (K : (HypercoveringCat X J)ᵒᵖ) :
    (cechCoconeAtSheaf X J n F).ι.app K = (hypercoveringCechEdge.{v} X J n).app (K, F) :=
  rfl

/-- **Two hypercoverings of `X` admit maps to a common hypercovering in the opposite category**:
they are both refined by their product. -/
lemma exists_hom_pair (K L : (HypercoveringCat X J)ᵒᵖ)
    [Precoverage.IsStableUnderComposition J.toPrecoverage] :
    ∃ M : (HypercoveringCat X J)ᵒᵖ, Nonempty (K ⟶ M) ∧ Nonempty (L ⟶ M) :=
  ⟨op ⟨K.unop.obj ⨯ L.unop.obj,
      IsHypercovering.prod J K.unop.property L.unop.property⟩,
    ⟨(ObjectProperty.homMk Limits.prod.fst).op⟩, ⟨(ObjectProperty.homMk Limits.prod.snd).op⟩⟩

/-- **A leg of a cocone on the diagram of Čech cohomology, read on an element pushed along a
refinement**, is the leg at the hypercovering one started from: the cocone condition on
elements. -/
lemma cocone_ι_app_map_apply (n : ℕ) (F : Sheaf J.toGrothendieck AddCommGrpCat.{v})
    (t : Cocone (cechDiagramAtSheaf X J n F)) {K M : (HypercoveringCat X J)ᵒᵖ} (g : K ⟶ M)
    (c : ToType ((cechDiagramAtSheaf X J n F).obj K)) :
    ConcreteCategory.hom (t.ι.app M)
        (ConcreteCategory.hom ((cechDiagramAtSheaf X J n F).map g) c) =
      ConcreteCategory.hom (t.ι.app K) c :=
  _root_.Stacks.Cohomology.Leray.apply_apply_eq_of_comp_eq (t.w g) c

/-- **A Čech class that the leg of `cechCoconeAtSheaf` kills dies after a refinement of the
hypercovering.** -/
lemma exists_map_apply_eq_zero_of_cechCoconeAtSheaf_ι_app_apply_eq_zero
    [Precoverage.IsStableUnderComposition J.toPrecoverage]
    (n : ℕ) (F : Sheaf J.toGrothendieck AddCommGrpCat.{v}) (K : (HypercoveringCat X J)ᵒᵖ)
    (c : ToType ((cechDiagramAtSheaf X J n F).obj K))
    (hc : ConcreteCategory.hom ((cechCoconeAtSheaf X J n F).ι.app K) c = 0) :
    ∃ (L : (HypercoveringCat X J)ᵒᵖ) (g : K ⟶ L),
      ConcreteCategory.hom ((cechDiagramAtSheaf X J n F).map g) c = 0 :=
  exists_hypercovering_map_cechHypercovering_apply_eq_zero X J F n K c hc

/-- **Every cohomology class in `H^n(X, 𝓕)` is the image of a Čech class of some
hypercovering.** -/
lemma exists_cechCoconeAtSheaf_ι_app_apply_eq
    [Precoverage.IsStableUnderComposition J.toPrecoverage]
    (n : ℕ) (F : Sheaf J.toGrothendieck AddCommGrpCat.{v})
    (x : ToType (cechCoconeAtSheaf X J n F).pt) :
    ∃ (L : (HypercoveringCat X J)ᵒᵖ) (c : ToType ((cechDiagramAtSheaf X J n F).obj L)),
      ConcreteCategory.hom ((cechCoconeAtSheaf X J n F).ι.app L) c = x :=
  (_root_.Stacks.CategoryTheory.Hypercovering.nonempty_hypercoverings.{v} J X).elim fun K ↦ by
    obtain ⟨L, g, c, hc⟩ :=
      exists_hypercovering_map_hypercoveringCechEdge_apply_eq X J F n (op K) x
    exact ⟨L, c, hc.trans (hypercoveringCohomologyFunctor_map_apply X J n g F x)⟩

/-- **Two Čech classes with the same image in `H^n(X, 𝓕)` have the same image under every cocone
on the diagram of Čech cohomology.** -/
lemma cocone_ι_app_apply_eq_of_cechCoconeAtSheaf_ι_app_apply_eq
    [Precoverage.IsStableUnderComposition J.toPrecoverage]
    (n : ℕ) (F : Sheaf J.toGrothendieck AddCommGrpCat.{v})
    (s : Cocone (cechDiagramAtSheaf X J n F)) {K L : (HypercoveringCat X J)ᵒᵖ}
    (c : ToType ((cechDiagramAtSheaf X J n F).obj K))
    (c' : ToType ((cechDiagramAtSheaf X J n F).obj L))
    (hcc' : ConcreteCategory.hom ((cechCoconeAtSheaf X J n F).ι.app K) c =
      ConcreteCategory.hom ((cechCoconeAtSheaf X J n F).ι.app L) c') :
    ConcreteCategory.hom (s.ι.app K) c = ConcreteCategory.hom (s.ι.app L) c' := by
  obtain ⟨M, ⟨g⟩, ⟨g'⟩⟩ := exists_hom_pair X J K L
  have hd : ConcreteCategory.hom ((cechCoconeAtSheaf X J n F).ι.app M)
      (ConcreteCategory.hom ((cechDiagramAtSheaf X J n F).map g) c -
        ConcreteCategory.hom ((cechDiagramAtSheaf X J n F).map g') c') = 0 := by
    rw [map_sub, cocone_ι_app_map_apply, cocone_ι_app_map_apply, hcc', sub_self]
  obtain ⟨N, k, hk⟩ :=
    exists_map_apply_eq_zero_of_cechCoconeAtSheaf_ι_app_apply_eq_zero X J n F M _ hd
  rw [map_sub, sub_eq_zero] at hk
  exact ((cocone_ι_app_map_apply X J n F s k _).trans
      (cocone_ι_app_map_apply X J n F s g c)).symm.trans
    ((congrArg (fun z ↦ ConcreteCategory.hom (s.ι.app N) z) hk).trans
      ((cocone_ι_app_map_apply X J n F s k _).trans
        (cocone_ι_app_map_apply X J n F s g' c')))

variable [Precoverage.IsStableUnderComposition J.toPrecoverage]

/-- **The value a cocone on the diagram of Čech cohomology must take on a cohomology class**:
the class is the image of a Čech class of some hypercovering, the leg of the cocone there is
applied to it, and *every* Čech class representing the class gives the same value. -/
lemma exists_descValueAtSheaf (n : ℕ) (F : Sheaf J.toGrothendieck AddCommGrpCat.{v})
    (s : Cocone (cechDiagramAtSheaf X J n F))
    (x : ToType (cechCoconeAtSheaf X J n F).pt) :
    ∃ y : ToType s.pt, ∀ (K : (HypercoveringCat X J)ᵒᵖ)
      (c : ToType ((cechDiagramAtSheaf X J n F).obj K)),
      ConcreteCategory.hom ((cechCoconeAtSheaf X J n F).ι.app K) c = x →
        ConcreteCategory.hom (s.ι.app K) c = y := by
  obtain ⟨L, c, hc⟩ := exists_cechCoconeAtSheaf_ι_app_apply_eq X J n F x
  exact ⟨ConcreteCategory.hom (s.ι.app L) c, fun K c' hc' ↦
    cocone_ι_app_apply_eq_of_cechCoconeAtSheaf_ι_app_apply_eq X J n F s c' c
      (hc'.trans hc.symm)⟩

/-- The map out of `H^n(X, 𝓕)` into the vertex of a cocone on the diagram of Čech cohomology, as
a function: the value `exists_descValueAtSheaf` provides. -/
noncomputable def descFunAtSheaf (n : ℕ)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{v})
    (s : Cocone (cechDiagramAtSheaf X J n F))
    (x : ToType (cechCoconeAtSheaf X J n F).pt) : ToType s.pt :=
  (exists_descValueAtSheaf X J n F s x).choose

/-- `descFunAtSheaf` is the leg of the cocone at *any* hypercovering a class comes from. -/
lemma descFunAtSheaf_apply (n : ℕ) (F : Sheaf J.toGrothendieck AddCommGrpCat.{v})
    (s : Cocone (cechDiagramAtSheaf X J n F)) {K : (HypercoveringCat X J)ᵒᵖ}
    (c : ToType ((cechDiagramAtSheaf X J n F).obj K)) :
    descFunAtSheaf X J n F s
        (ConcreteCategory.hom ((cechCoconeAtSheaf X J n F).ι.app K) c) =
      ConcreteCategory.hom (s.ι.app K) c :=
  ((exists_descValueAtSheaf X J n F s
    (ConcreteCategory.hom ((cechCoconeAtSheaf X J n F).ι.app K) c)).choose_spec K c rfl).symm

/-- `descFunAtSheaf` is additive. -/
lemma descFunAtSheaf_add (n : ℕ) (F : Sheaf J.toGrothendieck AddCommGrpCat.{v})
    (s : Cocone (cechDiagramAtSheaf X J n F))
    (x y : ToType (cechCoconeAtSheaf X J n F).pt) :
    descFunAtSheaf X J n F s (x + y) =
      descFunAtSheaf X J n F s x + descFunAtSheaf X J n F s y := by
  obtain ⟨K, c, hc⟩ := exists_cechCoconeAtSheaf_ι_app_apply_eq X J n F x
  obtain ⟨L, c', hc'⟩ := exists_cechCoconeAtSheaf_ι_app_apply_eq X J n F y
  obtain ⟨M, ⟨g⟩, ⟨g'⟩⟩ := exists_hom_pair X J K L
  have hx : ConcreteCategory.hom ((cechCoconeAtSheaf X J n F).ι.app M)
      (ConcreteCategory.hom ((cechDiagramAtSheaf X J n F).map g) c) = x :=
    (cocone_ι_app_map_apply X J n F (cechCoconeAtSheaf X J n F) g c).trans hc
  have hy : ConcreteCategory.hom ((cechCoconeAtSheaf X J n F).ι.app M)
      (ConcreteCategory.hom ((cechDiagramAtSheaf X J n F).map g') c') = y :=
    (cocone_ι_app_map_apply X J n F (cechCoconeAtSheaf X J n F) g' c').trans hc'
  have hxy : ConcreteCategory.hom ((cechCoconeAtSheaf X J n F).ι.app M)
      (ConcreteCategory.hom ((cechDiagramAtSheaf X J n F).map g) c +
        ConcreteCategory.hom ((cechDiagramAtSheaf X J n F).map g') c') = x + y := by
    rw [map_add, hx, hy]
  rw [← hxy, descFunAtSheaf_apply, map_add, ← hx, ← hy, descFunAtSheaf_apply,
    descFunAtSheaf_apply]

/-- For a site with fibre products, an object `X` and an abelian sheaf `𝓕`, the cohomology
`H^n(X, 𝓕)` is the colimit over the hypercoverings of `X` of the Čech cohomology groups
`Ȟ^n(K, 𝓕)`, the cocone being the canonical edge maps `hypercoveringCechEdge`. The index category
is the category of hypercoverings itself, not the homotopy quotient `HC(C, X)`. -/
@[stacks 01H0 "the general case at a fixed abelian sheaf: colim over hypercoverings of Ȟ^i(K, 𝓕) \
is H^i(X, 𝓕); the index category is the hypercoverings of X themselves rather than the homotopy \
quotient HC(C, X), and the hypotheses carried are fibre products in C and stability of the \
pretopology under composition", sga "4 V 7.4.1" "Clause 2)"]
def isColimit_cechCoconeAtSheaf (n : ℕ) (F : Sheaf J.toGrothendieck AddCommGrpCat.{v}) :
    IsColimit (cechCoconeAtSheaf X J n F) where
  desc s := ConcreteCategory.ofHom
    (AddMonoidHom.mk' (descFunAtSheaf X J n F s) (descFunAtSheaf_add X J n F s))
  fac s K := ConcreteCategory.hom_ext _ _ fun c ↦ by
    rw [ConcreteCategory.comp_apply, ConcreteCategory.hom_ofHom]
    exact descFunAtSheaf_apply X J n F s c
  uniq s m hm := ConcreteCategory.hom_ext _ _ fun x ↦ by
    obtain ⟨K, c, hc⟩ := exists_cechCoconeAtSheaf_ι_app_apply_eq X J n F x
    rw [← hc, ConcreteCategory.hom_ofHom]
    exact ((ConcreteCategory.comp_apply _ _ c).symm.trans
      (ConcreteCategory.congr_hom (hm K) c)).trans
      (descFunAtSheaf_apply X J n F s c).symm

/-! ### Sheaf cohomology as a colimit of functors on the abelian sheaves -/

omit [Precoverage.IsStableUnderComposition J.toPrecoverage] in
/-- **The abutment of the hypercovering spectral sequence does not depend on the
hypercovering**, so as a diagram of functors on the abelian sheaves it is the constant diagram at
`H^n(X, -)`. -/
def hypercoveringCohomologyIsoConst (n : ℕ) :
    Functor.curryObj (hypercoveringCohomologyFunctor X J n) ≅
      (Functor.const (HypercoveringCat X J)ᵒᵖ).obj (sheafCohomologyAtObject X J n) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun {_ _} φ ↦
    (Category.comp_id _).trans
      ((curryObj_hypercoveringCohomologyFunctor_map X J n φ).trans
        (Category.id_comp _).symm))

omit [Precoverage.IsStableUnderComposition J.toPrecoverage] in
/-- **The diagram `K ↦ Ȟ^n(K, -)` of hypercovering Čech cohomology, with values in the functors
on the abelian sheaves**: the currying of `cechHypercovering`, which is a functor of the
hypercovering and of the coefficient sheaf at once. -/
def cechFunctorDiagram (n : ℕ) :
    (HypercoveringCat X J)ᵒᵖ ⥤
      (Sheaf J.toGrothendieck AddCommGrpCat.{v} ⥤ AddCommGrpCat.{v}) :=
  Functor.curryObj (cechHypercovering.{v} X J n)

omit [Precoverage.IsStableUnderComposition J.toPrecoverage] in
/-- **The cocone of Čech-to-cohomology edge maps on the diagram of Čech cohomology functors**,
with vertex the functor `H^n(X, -)`. Its leg at a hypercovering `K` is the edge map
`Ȟ^n(K, -) ⟶ H^n(X, -)`, a natural transformation of functors on the abelian sheaves. -/
def cechFunctorCocone (n : ℕ) : Cocone (cechFunctorDiagram X J n) where
  pt := sheafCohomologyAtObject X J n
  ι :=
    { app := fun K ↦
        { app := fun F ↦ (hypercoveringCechEdge.{v} X J n).app (K, F)
          naturality := fun _ _ f ↦
            (hypercoveringCechEdge.{v} X J n).naturality (𝟙 K ×ₘ f) }
      naturality := fun K _ g ↦ NatTrans.ext (funext fun F ↦
        (((hypercoveringCechEdge.{v} X J n).naturality (g ×ₘ 𝟙 F)).trans
          ((congrArg (fun u ↦ (hypercoveringCechEdge.{v} X J n).app (K, F) ≫ u)
              (hypercoveringCohomologyFunctor_map_eq_id X J n g F)).trans
            (Category.comp_id _))).trans (Category.comp_id _).symm) }

omit [Precoverage.IsStableUnderComposition J.toPrecoverage] in
/-- The leg of `cechFunctorCocone` at a hypercovering, read at a sheaf, is the
Čech-to-cohomology edge map there. -/
@[simp]
lemma cechFunctorCocone_ι_app_app (n : ℕ) (K : (HypercoveringCat X J)ᵒᵖ)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{v}) :
    ((cechFunctorCocone X J n).ι.app K).app F = (hypercoveringCechEdge.{v} X J n).app (K, F) :=
  rfl

omit [Precoverage.IsStableUnderComposition J.toPrecoverage] in
/-- **Evaluating the cocone of Čech cohomology functors at an abelian sheaf gives the cocone of
Čech cohomology groups of that sheaf**: currying and then evaluating is pairing with the sheaf,
and the legs are the same edge maps. -/
def evaluationMapCoconeIso (n : ℕ) (F : Sheaf J.toGrothendieck AddCommGrpCat.{v}) :
    ((evaluation (Sheaf J.toGrothendieck AddCommGrpCat.{v}) AddCommGrpCat.{v}).obj F).mapCocone
        (cechFunctorCocone X J n) ≅
      cechCoconeAtSheaf X J n F :=
  Cocone.ext (Iso.refl _) (fun _ ↦ Category.comp_id _)

/-- Let `C` be a site with fibre products and `X` an object of `C`. For every `i`, the two
functors `Ab(C) ⥤ Ab` given by `𝓕 ↦ H^i(X, 𝓕)` and by `𝓕 ↦ colim_K Ȟ^i(K, 𝓕)`, the colimit
being over the hypercoverings `K` of `X`, are canonically isomorphic: the edge maps
`hypercoveringCechEdge` exhibit the functor `H^i(X, -)` as the colimit of the functors
`Ȟ^i(K, -)` in the category of functors `Ab(C) ⥤ Ab`. The index category is the category of
hypercoverings itself, not the homotopy quotient `HC(C, X)`. -/
@[stacks 01H0 "the functor-level statement in every degree, which is the claim of the tag: the \
edge maps exhibit the functor 𝓕 ↦ H^i(X, 𝓕) on Ab(C) as the colimit over the hypercoverings K of \
X of the functors 𝓕 ↦ Ȟ^i(K, 𝓕), the colimit being taken in the category of functors Ab(C) ⥤ Ab; \
the index category is the hypercoverings of X themselves rather than the homotopy quotient \
HC(C, X), and the hypotheses carried are fibre products in C and stability of the pretopology \
under composition"]
def isColimit_cechFunctorCocone (n : ℕ) : IsColimit (cechFunctorCocone X J n) :=
  evaluationJointlyReflectsColimits _ (fun F ↦
    (isColimit_cechCoconeAtSheaf X J n F).ofIsoColimit
      (evaluationMapCoconeIso X J n F).symm)

end Stacks.CategoryTheory.Hypercovering.Functorial

end
