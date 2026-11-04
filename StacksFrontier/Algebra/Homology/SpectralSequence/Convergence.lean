module

public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Basic
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Canonical
public import StacksFrontier.CategoryTheory.Subobject.Butterfly
public import StacksCore.Algebra.Homology.SpectralSequence.PageInfinity
public import StacksCore.CategoryTheory.Filtration.GradedPieces
import StacksCore.Tactic.StacksAttribute

/-!
# The convergence identification `E_∞^{p,q} ≅ gr^p H^{p+q}`

For a filtered complex `(K^•, F)` of an abelian category whose filtration is finite in each
degree, the infinity page of its spectral sequence is the associated graded object of the
filtration induced on cohomology:
`E_∞^{p,q} ≅ gr^p H^{p+q}(K^•)`.

This is the datum a spectral sequence needs in order to *abut* to its cohomology, in the sense of
`Stacks.Cohomology.Leray.FirstQuadrantAbutment.gradedIso` and of
`Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo.gradedIso`; it is the one field of those
structures that is not a formal consequence of the others.

## Main results

* `CochainComplex.Filtered.inducedFilteredObject`: the cohomology `H^n(K^•)` together with the
  induced filtration `F^pH^n(K^•) = Im(H^n(F^pK^•) ⟶ H^n(K^•))` of [Stacks, Tag 012P], as a
  `CategoryTheory.FilteredObject C ℤᵒᵖ`, so that `FilteredObject.gr p` applies to it.
* `CochainComplex.Filtered.hasPageInfinityAt_of_isDegreewiseFinite`: a filtration finite in each
  degree makes the spectral sequence stabilise at every bidegree, so that `E_∞^{p,q}` is the
  stable page and not the fallback zero object.
* `CochainComplex.Filtered.nonempty_pageInfinityIso_gr` and
  `CochainComplex.Filtered.pageInfinityIsoGr`: **the convergence identification**
  `E_∞^{p,q} ≅ gr^p H^{p+q}(K^•)`, under no hypothesis beyond degreewise finiteness of the
  filtration.
* `CochainComplex.Filtered.pageIsoGrAt` and `CochainComplex.Filtered.pageInfinityIsoGrAt`: the
  same identification with the stable page `R` supplied rather than chosen, together with the
  equation `CochainComplex.Filtered.π_pageIsoGrAt` characterising it.
* `CochainComplex.Filtered.canonicalPageIsoGr_naturality` and
  `CochainComplex.Filtered.canonicalPageInfinityIsoGr_naturality`: **the identification is natural
  in the filtered complex**, for the canonical spectral sequence and at a page stable for both
  filtered complexes.  `CochainComplex.Filtered.isStableFrom_of_firstQuadrant` provides such a
  page uniformly in the filtered complex when the filtration is first quadrant.

## Implementation notes

The two halves of the proof, and why they are the two halves:

* *The stable page is a subquotient of the filtration of `H^n`.* [Stacks, Tag 012Q]
  (`CochainComplex.exists_epi_gradedPiece_homology_of_isGLB_isLUB`) exhibits `gr^pH^n(K^•)` only
  as a quotient of a subobject of `Z_∞^{p,q}/B_∞^{p,q}`, and [Stacks, Tag 012V]
  (`CochainComplex.exists_iso_stablePage_iff_and_isGLB_isLUB_inducedFiltration_iff`) says that
  the comparison is an isomorphism *exactly* when the inclusions (012S) and (012T) are
  equalities.  Those equalities are what degreewise finiteness buys: they are the fourth
  conclusion of [Stacks, Tag 012W]
  (`CochainComplex.isBounded_and_converges_of_isDegreewiseFinite`).  So the identification with
  the graded piece is obtained by discharging (012S) and (012T), not by building a map out of
  the subquotient by hand.
* *The infinity page is the stable page.*  `E_∞^{p,q}` is Riou's `pageInfinity`, the page
  `E_{rMin}^{p,q}` once all differentials into and out of `(p, q)` have vanished; degreewise
  finiteness makes the relevant page objects *themselves* vanish for `r ≫ 0`, because
  `Z_r^{p+r,q-r+1} = 0` once `F^{p+r}K^{n+1} = 0`, and `Z_r^{p-r,q+r-1} = D_r^{p-r,q+r-1}` once
  `F^{p-r}K^{n-1} = F^{p-r+1}K^{n-1} = K^{n-1}`.  That is
  `hasPageInfinityAt_of_isDegreewiseFinite`, and `SpectralSequence.pageInfinityIso` then moves
  `E_∞^{p,q}` onto the stable page.

The page `E_r^{p,q}` of `CochainComplex.Filtered.spectralSequenceFunctor` is the subquotient
`Z_r^{p,q}/(D_r^{p,q} ⊓ Z_r^{p,q})` *definitionally* (`CochainComplex.Filtered.pageIso` is the
identity), and `(FilteredObject.gr p).obj A` is `cokernel (A.filtration.step (succHom p))`
definitionally; so both ends of the chain of isomorphisms need no transport.  The one piece of
genuine subobject bookkeeping in between is `exists_cokernelIso_sup`: the stable page is
`(Ker d^n ⊓ F^pK^n)/(Ker d^n ⊓ F^{p+1}K^n ⊔ Im d^{n-1} ⊓ F^pK^n)`, whereas (012S) and (012T) are
stated for the numerator and denominator with `F^{p+1}K^n` adjoined to both, and adjoining a
subobject of the denominator to both does not change the quotient.  This is the degenerate case
`B = ⊤` of the butterfly lemma `CategoryTheory.Subobject.exists_iso_butterfly`, proved here
directly because the rewriting of the butterfly's four joins into this shape is longer than the
proof.

`exists_cokernelIso_sup` and `exists_cokernel_preComp_iso` each return their isomorphism
together with the equation characterising it, rather than only its existence, so that the links
of the chain are data; the same is done for [Stacks, Tag 012Q] and [Stacks, Tag 012V] in
`StacksFrontier/Algebra/Homology/SpectralSequence/FilteredComplex/Basic.lean`
(`CochainComplex.stablePageIsoGradedPiece` and its uniqueness).  What is still missing before the
chain can be made *natural* in the filtered complex is listed at the end of these notes.

`exists_cokernelIso_sup`, `cokernelOfLEIso` and `exists_cokernel_preComp_iso` also occur, private,
in `StacksFrontier/Homology/DerivedComplete/FilteredCompletionTruncation.lean` and
`StacksFrontier/Homology/DerivedComplete/FilteredCompletionModel.lean`, whose
`converges_of_filtrationSubobject_finite` is the same (012Q, 012V, 012W) assembly stopping one
step short of `pageInfinity`.  They are repeated rather than imported because those files belong
to the adic derived-completion development and carry `ModuleCat` and `DerivedCategory` with them,
which the spectral-sequence foundations -- and hence every consumer of the abutment datum --
must not depend on.  The right cleanup is for those files to import this file.

*What naturality needs, and what it does not.*  `pageInfinityIsoGr` is a composite of seven
isomorphisms, and three things stood between it and a naturality statement.  Two were real and are
settled here.  The page identification `hE` is an unconstrained family of isomorphisms at this
generality, so no square through it commutes for a reason; the natural statement therefore belongs
at `CochainComplex.filteredSpectralSequence` -- that is, at
`CochainComplex.Filtered.spectralSequenceFunctor` -- where `hE` is
`FilteredComplexSpectralSequence.eIso` and every component of it is an identity.  And the stable
page has to be *common* to the two filtered complexes, since
`CategoryTheory.SpectralSequence.Hom.mapPageInfinity_eq` compares them on a single page, whereas
`exists_stable_page` chooses one at each; `IsStableFrom` names the property so that the page can be
supplied, and `IsStableFrom.mono` makes a common page out of a maximum.

The third was the functoriality of the subobject bookkeeping: for `φ : K^• ⟶ L^•` there is no map
`Z_∞^{p, q}(K) ⟶ Z_∞^{p, q}(L)`, and none of the commuting squares of quotients of
`Subobject.ofLE` that carrying the chain link by link would need.  It turns out not to be needed.
`π_pageIsoGrAt` pins the whole composite by one equation, and both sides of that equation live on
`Z_R^{p, q}`, on `Z^n(K^•)` and on `H^n(K^•)` -- objects a morphism of filtered complexes acts on.
Cancelling the epimorphism `cokernel.π` on the source and the monomorphism
`F^pH^n(L^•) ⟶ H^n(L^•)` on the target turns the naturality square into the commuting square of
`φ` over `K^n ⟶ L^n`.  That is `canonicalPageIsoGr_naturality`; the stable cycles never appear.

## References

* [Stacks Project, Tag 012P](https://stacks.math.columbia.edu/tag/012P)
* [Stacks Project, Tag 012Q](https://stacks.math.columbia.edu/tag/012Q)
* [Stacks Project, Tag 012V](https://stacks.math.columbia.edu/tag/012V)
* [Stacks Project, Tag 012W](https://stacks.math.columbia.edu/tag/012W)
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite
open CochainComplex FilteredComplexSpectralSequence

namespace CochainComplex.Filtered

variable {C : Type u} [Category.{v} C] [Abelian C]

/-! ### Degreewise finiteness, in terms of the degreewise filtration subobjects -/

section Filtration

variable (K : Filtered C) (F : ∀ (_p n : ℤ), Subobject (K.X.X n))
  (hF : ∀ p n : ℤ, F p n = Subobject.mk ((K.filtration.ι.app (op p)).f n))

include hF

/-- A degreewise filtration by subcomplexes is decreasing. -/
private lemma F_antitone (p p' n : ℤ) (h : p ≤ p') : F p' n ≤ F p n := by
  rw [hF p' n, hF p n]
  exact filtrationSubobject_antitone K p p' n h

end Filtration

/-! ### Quotients of nested subobjects -/

/-- Equal pairs of nested subobjects have the same quotient. -/
noncomputable def cokernelOfLEIso {X : C} {U V U' V' : Subobject X}
    (h : U ≤ V) (h' : U' ≤ V') (hU : U = U') (hV : V = V') :
    cokernel (Subobject.ofLE U V h) ≅ cokernel (Subobject.ofLE U' V' h') := by
  subst hU; subst hV; exact Iso.refl _

/-- **A class is unchanged by `cokernelOfLEIso`.** The transport along `U = U'`, `V = V'` carries
the class of a generator `k` of the numerator to the class of any generator `k'` agreeing with it
over the ambient object.  This is the form in which the three equality transports of the
convergence chain are crossed by the characterising equations of the links on either side of
them. -/
@[reassoc]
lemma comp_π_cokernelOfLEIso {X : C} {U V U' V' : Subobject X}
    (h : U ≤ V) (h' : U' ≤ V') (hU : U = U') (hV : V = V') {T : C}
    (k : T ⟶ (V : C)) (k' : T ⟶ (V' : C)) (hk : k ≫ V.arrow = k' ≫ V'.arrow) :
    k ≫ cokernel.π (Subobject.ofLE U V h) ≫ (cokernelOfLEIso h h' hU hV).hom =
      k' ≫ cokernel.π (Subobject.ofLE U' V' h') := by
  subst hU
  subst hV
  obtain rfl : k = k' := (cancel_mono V.arrow).1 hk
  simp [cokernelOfLEIso]

/-- **`cokernelOfLEIso` with the numerator unchanged does not move the projection.**  The special
case of `comp_π_cokernelOfLEIso` in which only the denominator is transported, which is the shape
of the first and the last transport of the convergence chain. -/
@[reassoc]
lemma π_cokernelOfLEIso {X : C} {U V U' : Subobject X} (h : U ≤ V) (h' : U' ≤ V) (hU : U = U') :
    cokernel.π (Subobject.ofLE U V h) ≫ (cokernelOfLEIso h h' hU rfl).hom =
      cokernel.π (Subobject.ofLE U' V h') := by
  simpa using comp_π_cokernelOfLEIso h h' hU rfl (𝟙 _) (𝟙 _) rfl

/-- **Adjoining a subobject of the denominator to both terms does not change the quotient.** If
`U/W` is a subquotient of `X` and `W' ⊓ U ≤ W`, then `U/W ≅ (U ⊔ W')/(W ⊔ W')`.  This is the
degenerate case `B = ⊤` of the butterfly lemma.

The isomorphism is returned together with the equation characterising it -- it is the descent of
the inclusion `U ⟶ U ⊔ W'` -- so that it is *data* and not merely available: the two numerators
have a common generator, and the isomorphism is the unique one compatible with it. -/
lemma exists_cokernelIso_sup {X : C} (W U W' : Subobject X)
    (hW : W ≤ U) (hW' : W' ⊓ U ≤ W) :
    ∃ e : cokernel (Subobject.ofLE W U hW) ≅
        cokernel (Subobject.ofLE (W ⊔ W') (U ⊔ W') (sup_le_sup_right hW W')),
      cokernel.π (Subobject.ofLE W U hW) ≫ e.hom =
        Subobject.ofLE U (U ⊔ W') le_sup_left ≫
          cokernel.π (Subobject.ofLE (W ⊔ W') (U ⊔ W') (sup_le_sup_right hW W')) := by
  let j := Subobject.ofLE W U hW
  let j' := Subobject.ofLE (W ⊔ W') (U ⊔ W') (sup_le_sup_right hW W')
  let v := Subobject.ofLE U (U ⊔ W') le_sup_left
  have hv : v ≫ (U ⊔ W').arrow = U.arrow := Subobject.ofLE_arrow _
  have : Mono (v ≫ (U ⊔ W').arrow) := by rw [hv]; infer_instance
  have : Epi (v ≫ cokernel.π j') :=
    Subobject.epi_comp_cokernel_π (Y := W') j' (Subobject.ofLE_arrow _) v
      (by simp only [hv, Subobject.mk_arrow]; exact le_rfl) le_sup_right
  have hi : (W ⊔ W') ⊓ U = W := by
    rwa [sup_inf_assoc_of_le _ hW, sup_eq_left]
  obtain ⟨e, he⟩ := Subobject.exists_iso_cokernel_of_factors_iff j
    (Subobject.ofLE_arrow _) j' (Subobject.ofLE_arrow _) (𝟙 _) v
    (fun {T} g => by
      simp only [Category.id_comp, hv]
      refine ⟨Subobject.factors_of_le _ le_sup_left, fun h => ?_⟩
      have hh := (Subobject.inf_factors (g ≫ U.arrow)).2 ⟨h, Subobject.factors_comp_arrow _⟩
      rwa [hi] at hh)
  exact ⟨e, by simpa only [Category.id_comp] using he⟩

/-- **The isomorphism of `exists_cokernelIso_sup`, as data.**  The convergence chain is assembled
below out of named isomorphisms rather than chosen ones, so that the equation characterising each
link is attached to the link itself; this is the first of them. -/
noncomputable def cokernelIsoSup {X : C} (W U W' : Subobject X)
    (hW : W ≤ U) (hW' : W' ⊓ U ≤ W) :
    cokernel (Subobject.ofLE W U hW) ≅
      cokernel (Subobject.ofLE (W ⊔ W') (U ⊔ W') (sup_le_sup_right hW W')) :=
  (exists_cokernelIso_sup W U W' hW hW').choose

/-- The equation characterising `cokernelIsoSup`: it is the descent of `U ⟶ U ⊔ W'`. -/
@[reassoc]
lemma π_cokernelIsoSup {X : C} (W U W' : Subobject X) (hW : W ≤ U) (hW' : W' ⊓ U ≤ W) :
    cokernel.π (Subobject.ofLE W U hW) ≫ (cokernelIsoSup W U W' hW hW').hom =
      Subobject.ofLE U (U ⊔ W') le_sup_left ≫
        cokernel.π (Subobject.ofLE (W ⊔ W') (U ⊔ W') (sup_le_sup_right hW W')) :=
  (exists_cokernelIso_sup W U W' hW hW').choose_spec

/-- **The graded piece `Im h/Im(g ≫ f)` computed by `image.preComp`, as a quotient of image
subobjects.**  The last link of the convergence chain: `gr^pH^n(K^•)` is presented by
`image.preComp` on the (012V) side and by a quotient of two steps of the induced filtration on the
`FilteredObject.gr` side, and the two presentations differ only by `imageSubobjectIso`. -/
noncomputable def cokernelPreCompIso {X Y Z : C} (g : X ⟶ Y) (f : Y ⟶ Z) :
    cokernel (image.preComp g f) ≅
      cokernel (Subobject.ofLE _ _ (imageSubobject_comp_le g f)) :=
  cokernel.mapIso _ _ (imageSubobjectIso (g ≫ f)).symm (imageSubobjectIso f).symm (by
    rw [← cancel_mono (imageSubobject f).arrow]; simp)

/-- The equation characterising `cokernelPreCompIso`: it is compatible with the two projections
from `Im f`. -/
@[reassoc]
lemma π_cokernelPreCompIso {X Y Z : C} (g : X ⟶ Y) (f : Y ⟶ Z) :
    cokernel.π (image.preComp g f) ≫ (cokernelPreCompIso g f).hom =
      (imageSubobjectIso f).inv ≫
        cokernel.π (Subobject.ofLE _ _ (imageSubobject_comp_le g f)) := by
  simp [cokernelPreCompIso, cokernel.mapIso]

/-- The graded piece `Im h/Im(g ≫ f)` computed by `image.preComp` is the quotient of the
corresponding image subobjects, compatibly with the two projections from `Im f`.  As for
`exists_cokernelIso_sup`, the equation is carried so that the isomorphism is data. -/
private lemma exists_cokernel_preComp_iso {X Y Z : C} (g : X ⟶ Y) (f : Y ⟶ Z) :
    ∃ (hle : imageSubobject (g ≫ f) ≤ imageSubobject f)
      (e : cokernel (image.preComp g f) ≅ cokernel (Subobject.ofLE _ _ hle)),
      cokernel.π (image.preComp g f) ≫ e.hom =
        (imageSubobjectIso f).inv ≫ cokernel.π (Subobject.ofLE _ _ hle) :=
  ⟨imageSubobject_comp_le g f, cokernelPreCompIso g f, π_cokernelPreCompIso g f⟩

/-! ### The filtration induced on cohomology, as a filtered object -/

/-- **The cohomology of a filtered complex, filtered.** `H^n(K^•)` together with the filtration
`F^pH^n(K^•) = Im(H^n(F^pK^•) ⟶ H^n(K^•))` induced on it by `(K^•, F)` ([Stacks, Tag 012P]), as
an object of `Fil(C) = CategoryTheory.FilteredObject C ℤᵒᵖ`.  Packaging the induced filtration
this way is what lets `CategoryTheory.FilteredObject.gr p` be applied to it, so that the graded
pieces `gr^pH^n(K^•)` are the values of a functor. -/
@[stacks 012P "the induced filtration of `H^n(K^•)`, bundled as an object of `Fil(𝒜)`",
  ega "0 11.2.2"]
noncomputable def inducedFilteredObject (K : Filtered C) (n : ℤ) : FilteredObject C ℤᵒᵖ where
  X := K.X.homology n
  filtration := K.inducedFiltration n

/-- The underlying object of `inducedFilteredObject` is the cohomology. -/
@[simp]
lemma inducedFilteredObject_X (K : Filtered C) (n : ℤ) :
    (K.inducedFilteredObject n).X = K.X.homology n :=
  rfl

/-- The steps of `inducedFilteredObject`, as subobjects, are the induced filtration. -/
@[simp]
lemma inducedFilteredObject_subobject (K : Filtered C) (n p : ℤ) :
    (K.inducedFilteredObject n).filtration.subobject (op p) = K.inducedFiltrationStep n p :=
  Filtration.subobject_ofAntitone _ (K.inducedFiltrationStep_antitone n) p

/-- The graded piece of the induced filtration is the quotient of two of its steps. -/
lemma gr_inducedFilteredObject (K : Filtered C) (n p : ℤ) :
    (FilteredObject.gr p).obj (K.inducedFilteredObject n) =
      cokernel (Subobject.ofLE (K.inducedFiltrationStep n (p + 1)) (K.inducedFiltrationStep n p)
        (K.inducedFiltrationStep_antitone n (by omega : p ≤ p + 1))) :=
  rfl

/-! ### Stabilisation and convergence

Throughout this section the spectral sequence is presented as in [Stacks, Tag 012W]: by an
isomorphism `hE` of each page with the subquotient `Z_r^{p,q}/(D_r^{p,q} ⊓ Z_r^{p,q})` of `K^n`.
This is the presentation in which [Stacks, Tag 012M]
(`CochainComplex.exists_cohomologicalSpectralSequence`), [Stacks, Tag 012W] and [Stacks, Tag 0132]
(`HomologicalComplex₂.isBounded_and_converges_totalFiltration₁`,
`HomologicalComplex₂.isBounded_and_converges_totalFiltration₂`) all state their conclusions, so a
consumer which has already invoked one of those has the data to hand; the specialisations at the
end of the file discharge it for `CochainComplex.Filtered.spectralSequenceFunctor`. -/

/-- **`R` is a stable page for the bidegree `(p, q)`**: the filtration of `K^{n + 1}` has reached
zero at `p + r` and that of `K^{n - 1}` is still everything at `p - r + 1`, for every `r ≥ R`.
These are the two conditions under which the page `E_r^{p,q}` is the subquotient of `K^n` cut out
by the right-hand sides of (012S) and (012T), and under which all the differentials into and out
of `(p, q)` vanish.

Naming the property, rather than only asserting that some `R` has it (`exists_stable_page`), is
what makes the convergence chain usable *between* two filtered complexes:
`CategoryTheory.SpectralSequence.Hom.mapPageInfinity_eq` compares two spectral sequences on a
single page, and a page chosen separately at each of them is no such page.  The property is
inherited by every larger index (`IsStableFrom.mono`), so a common stable page for two filtered
complexes is a maximum. -/
def IsStableFrom (K : Filtered C) (F : ∀ (_p n : ℤ), Subobject (K.X.X n)) (p q R : ℤ) : Prop :=
  1 ≤ R ∧ (∀ r : ℤ, R ≤ r → F (p + r) (p + q + 1) = ⊥) ∧
    (∀ r : ℤ, R ≤ r → F (p - r + 1) (p + q - 1) = ⊤)

namespace IsStableFrom

variable {K : Filtered C} {F : ∀ (_p n : ℤ), Subobject (K.X.X n)} {p q R R' : ℤ}

/-- A stable page is at least the first page. -/
lemma one_le (h : IsStableFrom K F p q R) : 1 ≤ R := h.1

/-- A stable page is in particular a non-negative page index. -/
lemma zero_le (h : IsStableFrom K F p q R) : 0 ≤ R := zero_le_one.trans h.1

/-- At a stable page the filtration of `K^{n + 1}` has reached zero: this is the right-hand side
of (012S). -/
lemma eq_bot (h : IsStableFrom K F p q R) : F (p + R) (p + q + 1) = ⊥ := h.2.1 R le_rfl

/-- At a stable page the filtration of `K^{n - 1}` is still everything: this is the right-hand
side of (012T). -/
lemma eq_top (h : IsStableFrom K F p q R) : F (p - R + 1) (p + q - 1) = ⊤ := h.2.2 R le_rfl

/-- **Stability is inherited by every later page.**  Hence `max R R'` is a stable page for two
filtered complexes whose stable pages are `R` and `R'` separately, which is what a naturality
statement about the infinity page needs. -/
lemma mono (h : IsStableFrom K F p q R) (hRR' : R ≤ R') : IsStableFrom K F p q R' :=
  ⟨h.1.trans hRR', fun r hr => h.2.1 r (hRR'.trans hr), fun r hr => h.2.2 r (hRR'.trans hr)⟩

end IsStableFrom

/-- **A first-quadrant filtration makes every page beyond `max (q + 2) (p + 1)` stable at
`(p, q)`.**  The bound depends on the bidegree alone and not on the filtered complex, so this is
the form in which a *functorial* first-quadrant filtered complex has a stable page common to all
its values -- which is what `canonicalPageInfinityIsoGr_naturality` asks for.

The two conditions are read off the two halves of the first-quadrant hypothesis directly:
`F^{p+r}K^{p+q+1} = 0` because `p + q + 1 < p + r`, and `F^{p-r+1}K^{p+q-1} = K^{p+q-1}` because
`p - r + 1 ≤ 0` and the filtration is already everything at `0`. -/
lemma isStableFrom_of_firstQuadrant (K : Filtered C)
    (htop : ∀ n : ℤ, IsIso ((K.filtration.ι.app (op (0 : ℤ))).f n))
    (hbot : ∀ p n : ℤ, n < p → IsZero ((K.filtration.obj (op p)).X n))
    (p q R : ℤ) (h1 : 1 ≤ R) (hq : q + 2 ≤ R) (hp : p + 1 ≤ R) :
    IsStableFrom K (filtrationSubobject K) p q R := by
  refine ⟨h1, fun r hr => Subobject.mk_eq_bot_iff_zero.mpr
    ((hbot (p + r) (p + q + 1) (by omega)).eq_of_src _ _), fun r hr => top_le_iff.mp ?_⟩
  refine le_trans ?_ (filtrationSubobject_antitone K (p - r + 1) 0 (p + q - 1) (by omega))
  exact ((Subobject.isIso_iff_mk_eq_top
    ((K.filtration.ι.app (op (0 : ℤ))).f (p + q - 1))).mp (htop _)).ge

/-- **Degreewise finiteness supplies a stable page at every bidegree.**  The `∀ r ≥ R` form of
`exists_stable_page`, which the latter is now read off: degreewise finiteness bounds the
filtration of `K^{n + 1}` and of `K^{n - 1}` once and for all, so the two conditions hold not
just at one index but from it on. -/
private lemma exists_isStableFrom (K : Filtered C) (F : ∀ (_p n : ℤ), Subobject (K.X.X n))
    (hF : ∀ p n : ℤ, F p n = Subobject.mk ((K.filtration.ι.app (op p)).f n))
    (hK : K.filtration.IsDegreewiseFinite) (p q : ℤ) :
    ∃ R : ℤ, IsStableFrom K F p q R := by
  obtain ⟨b, hb⟩ := exists_F_eq_bot K F hF hK (p + q + 1)
  obtain ⟨a, ha⟩ := exists_F_eq_top K F hF hK (p + q - 1)
  exact ⟨max 1 (max (b - p) (p + 1 - a)),
    le_max_left _ _, fun r hr => hb _ (by omega), fun r hr => ha _ (by omega)⟩

section StablePage

variable {K : Filtered C} {F : ∀ (_p n : ℤ), Subobject (K.X.X n)}
  (hF : ∀ p n : ℤ, F p n = Subobject.mk ((K.filtration.ι.app (op p)).f n))
  {Z : ∀ (_r _p n : ℤ), Subobject (K.X.X n)}
  (hZ : ∀ r p n : ℤ, Z r p n =
    F p n ⊓ (Subobject.pullback (K.X.d n (n + 1))).obj (F (p + r) (n + 1)))
  {D : ∀ (_r _p n : ℤ), Subobject (K.X.X n)}
  (hD : ∀ r p n : ℤ, D r p n = Z (r - 1) (p + 1) n ⊔
    (Subobject.«exists» (K.X.d (n - 1) n)).obj (Z (r - 1) (p - r + 1) (n - 1)))
  {p q R : ℤ} (hR : IsStableFrom K F p q R)

include hZ hR

/-- **At a stable page the cycles are the cycles of `K^•` lying in `F^pK^n`**: the right-hand side
of (012S).  The vanishing `F^{p + R}K^{n + 1} = 0` turns the preimage condition cutting out
`Z_R^{p,q}` into the condition that the differential vanish. -/
lemma cycles_eq_inf_of_isStableFrom :
    Z R p (p + q) = kernelSubobject (K.X.d (p + q) (p + q + 1)) ⊓ F p (p + q) := by
  rw [hZ R p (p + q), hR.eq_bot, Subobject.pullback_bot, inf_comm]

include hD in
/-- **At a stable page the boundaries are the right-hand side of (012T)**,
`Ker(d^n) ∩ F^{p+1}K^n + Im(d^{n-1}) ∩ F^pK^n`: the vanishing `F^{p+R}K^{n+1} = 0` cuts the first
summand `Z_{R-1}^{p+1,q}` down to it, and the exhaustion `F^{p-R+1}K^{n-1} = K^{n-1}` makes the
second the whole image of `d^{n-1}` met with `F^pK^n`. -/
lemma boundaries_eq_sup_of_isStableFrom :
    D R p (p + q) =
      kernelSubobject (K.X.d (p + q) (p + q + 1)) ⊓ F (p + 1) (p + q) ⊔
        imageSubobject (K.X.d (p + q - 1) (p + q)) ⊓ F p (p + q) := by
  rw [hD R p (p + q), hZ (R - 1) (p + 1) (p + q), hZ (R - 1) (p - R + 1) (p + q - 1),
    show p + 1 + (R - 1) = p + R by omega, show p + q - 1 + 1 = p + q by omega,
    show p - R + 1 + (R - 1) = p by omega, hR.eq_bot, hR.eq_top, Subobject.pullback_bot,
    top_inf_eq, Abelian.Subobject.exists_pullback_eq_inf, inf_comm (F (p + 1) (p + q)),
    inf_comm (F p (p + q))]

include hF hD in
/-- The boundaries at a stable page lie in the cycles: both summands of (012T) do. -/
lemma boundaries_le_cycles_of_isStableFrom : D R p (p + q) ≤ Z R p (p + q) := by
  rw [cycles_eq_inf_of_isStableFrom hZ hR, boundaries_eq_sup_of_isStableFrom hZ hD hR]
  exact sup_le (inf_le_inf_left _ (F_antitone K F hF p (p + 1) (p + q) (by omega)))
    (inf_le_inf_right _ (image_le_kernel _ _ (by simp)))

include hF hD in
/-- **`F^{p+1}K^n` meets the cycles inside the boundaries.**  This is the side condition of
`cokernelIsoSup`: it is what lets `F^{p+1}K^n` be adjoined to numerator and denominator of the
stable page without changing the quotient. -/
lemma inf_cycles_le_boundaries_of_isStableFrom :
    F (p + 1) (p + q) ⊓ Z R p (p + q) ≤ D R p (p + q) := by
  rw [cycles_eq_inf_of_isStableFrom hZ hR, boundaries_eq_sup_of_isStableFrom hZ hD hR,
    inf_left_comm, inf_eq_left.mpr (F_antitone K F hF p (p + 1) (p + q) (by omega))]
  exact le_sup_left

/-- **At a stable page the cycles of `Z_R^{p,q}` are cycles of `K^•`**: they are killed by
`d^n`, which is what lets them be lifted to `Z^n(K^•)` and given a cohomology class. -/
lemma arrow_comp_d_eq_zero_of_isStableFrom :
    (Z R p (p + q)).arrow ≫ K.X.d (p + q) (p + q + 1) = 0 :=
  Subobject.arrow_comp_eq_zero_of_le_kernelSubobject
    (le_trans (le_of_eq (cycles_eq_inf_of_isStableFrom hZ hR)) inf_le_left)

/-- The cycles at a stable page lie in the stable cycles of (012S). -/
lemma cycles_le_stableCycles_of_isStableFrom :
    Z R p (p + q) ≤
      kernelSubobject (K.X.d (p + q) (p + q + 1)) ⊓ F p (p + q) ⊔ F (p + 1) (p + q) :=
  le_trans (le_of_eq (cycles_eq_inf_of_isStableFrom hZ hR)) le_sup_left

/-- The numerator of the stable page with `F^{p+1}K^n` adjoined is the stable cycles, the
left-hand side of (012S). -/
lemma sup_cycles_eq_of_isStableFrom :
    Z R p (p + q) ⊔ F (p + 1) (p + q) =
      kernelSubobject (K.X.d (p + q) (p + q + 1)) ⊓ F p (p + q) ⊔ F (p + 1) (p + q) := by
  rw [cycles_eq_inf_of_isStableFrom hZ hR]

include hD in
/-- The denominator of the stable page with `F^{p+1}K^n` adjoined is the stable boundaries, the
left-hand side of (012T), met with the stable cycles. -/
lemma sup_boundaries_eq_of_isStableFrom :
    D R p (p + q) ⊔ F (p + 1) (p + q) =
      (imageSubobject (K.X.d (p + q - 1) (p + q)) ⊓ F p (p + q) ⊔ F (p + 1) (p + q)) ⊓
        (kernelSubobject (K.X.d (p + q) (p + q + 1)) ⊓ F p (p + q) ⊔ F (p + 1) (p + q)) := by
  rw [inf_eq_left.mpr (sup_le_sup_right
      (inf_le_inf_right _ (image_le_kernel _ _ (by simp))) (F (p + 1) (p + q))),
    boundaries_eq_sup_of_isStableFrom hZ hD hR, sup_assoc,
    sup_eq_right.mpr (inf_le_right.trans le_sup_right)]

end StablePage

/-- **`Im(H^n(F^{p+1}K^•) ⟶ H^n(K^•))` is the step `F^{p+1}H^n(K^•)` of the induced
filtration.**  The last link of the convergence chain needs this: the composite
`F^{p+1}K^• ⟶ F^pK^• ⟶ K^•` is the inclusion of `F^{p+1}K^•`. -/
lemma imageSubobject_homologyMap_comp_eq (K : Filtered C) (n p : ℤ) :
    imageSubobject (HomologicalComplex.homologyMap (K.filtration.diagram.map
          (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n ≫
        HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n) =
      K.inducedFiltrationStep n (p + 1) := by
  rw [← HomologicalComplex.homologyMap_comp, Filtration.diagram_map_comp_ι_app]

/-- **The step `F^{p+1}H^n(K^•)` of the induced filtration lies in the step `F^pH^n(K^•)`.**
`inducedFiltrationStep_antitone` at the single step the graded piece `gr^p` is the quotient over,
named so that the inequality is a declaration rather than an application of `Antitone`: that is
what lets the quotient `gr^pH^n(K^•)` be rewritten in. -/
lemma inducedFiltrationStep_succ_le (K : Filtered C) (n p : ℤ) :
    K.inducedFiltrationStep n (p + 1) ≤ K.inducedFiltrationStep n p :=
  K.inducedFiltrationStep_antitone n (Int.le_add_one le_rfl)

/-- **`gr^pH^n(K^•)` presented by `image.preComp` is the quotient of two steps of the induced
filtration.**  The last link of the convergence chain: `cokernelPreCompIso` presents the graded
piece as a quotient of two image subobjects, and those images *are* the steps `F^{p+1}H^n(K^•)`
and `F^pH^n(K^•)` of [Stacks, Tag 012P]. -/
noncomputable def preCompIsoGrInducedFiltration (K : Filtered C) (n p : ℤ) :
    cokernel (image.preComp
        (HomologicalComplex.homologyMap (K.filtration.diagram.map
          (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n)
        (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n)) ≅
      cokernel (Subobject.ofLE (K.inducedFiltrationStep n (p + 1))
        (K.inducedFiltrationStep n p) (K.inducedFiltrationStep_succ_le n p)) :=
  cokernelPreCompIso _ _ ≪≫
    cokernelOfLEIso (imageSubobject_comp_le _ _) (K.inducedFiltrationStep_succ_le n p)
      (imageSubobject_homologyMap_comp_eq K n p) rfl

/-- The equation characterising `preCompIsoGrInducedFiltration`. -/
@[reassoc]
lemma π_preCompIsoGrInducedFiltration (K : Filtered C) (n p : ℤ) :
    cokernel.π (image.preComp
          (HomologicalComplex.homologyMap (K.filtration.diagram.map
            (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n)
          (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n)) ≫
        (preCompIsoGrInducedFiltration K n p).hom =
      (imageSubobjectIso (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n)).inv ≫
        cokernel.π (Subobject.ofLE (K.inducedFiltrationStep n (p + 1))
          (K.inducedFiltrationStep n p) (K.inducedFiltrationStep_succ_le n p)) := by
  rw [preCompIsoGrInducedFiltration, Iso.trans_hom, ← Category.assoc, π_cokernelPreCompIso,
    Category.assoc, π_cokernelOfLEIso]

/-- The inverse of `imageSubobjectIso` followed by the arrow of the step `F^pH^n(K^•)` is the
image inclusion. -/
private lemma imageSubobjectIso_inv_comp_arrow (K : Filtered C) (n p : ℤ) :
    (imageSubobjectIso (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n)).inv ≫
      (K.inducedFiltrationStep n p).arrow =
      image.ι (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n) := by
  simp

/-- **A subobject of `F^pK^n` killed by `d^n` factors through `A = Ker(d^n) ∩ F^pK^n`**, the
source of the two maps of [Stacks, Tag 012Q].  The factorisation is unique, `A` being a
subobject. -/
private lemma exists_factorThru_pullback_iCycles (K : Filtered C) (n p : ℤ)
    (F : ∀ (_p n : ℤ), Subobject (K.X.X n)) (P : Subobject (K.X.X n)) (hPF : P ≤ F p n)
    (t : (P : C) ⟶ K.X.cycles n) (ht : t ≫ K.X.iCycles n = P.arrow) :
    ∃ w : (P : C) ⟶ ((Subobject.pullback (K.X.iCycles n)).obj (F p n) : C),
      w ≫ ((Subobject.pullback (K.X.iCycles n)).obj (F p n)).arrow = t :=
  ⟨Subobject.factorThru _ t ((pullback_factors_iff _ _ _).2
      (by rw [ht]; exact Subobject.factors_of_le _ hPF (Subobject.factors_self P))),
    Subobject.factorThru_arrow _ _ _⟩

/-- **A subobject of `F^pK^n` killed by `d^n` has a cohomology class lying in `F^pH^n(K^•)`.**
The factorisation `t` through the cycles of `K^•` and the resulting map `β` to the step
`F^pH^n(K^•) = Im(H^n(F^pK^•) ⟶ H^n(K^•))` of the induced filtration; both are unique, being
pinned by the monomorphisms `Z^n(K^•) ⟶ K^n` and `F^pH^n(K^•) ⟶ H^n(K^•)`.

This is the pair of maps in terms of which `π_pageIsoGrAt` characterises the convergence
identification, and the reason that characterisation is natural: `t` and `β` are built from
`P.arrow` and `H^n`, both of which a morphism of filtered complexes acts on. -/
lemma exists_liftCycles_toInducedFiltrationStep (K : Filtered C) (n p : ℤ)
    (F : ∀ (_p n : ℤ), Subobject (K.X.X n))
    (hF : ∀ p n : ℤ, F p n = Subobject.mk ((K.filtration.ι.app (op p)).f n))
    (P : Subobject (K.X.X n)) (hPF : P ≤ F p n) (hPd : P.arrow ≫ K.X.d n (n + 1) = 0) :
    ∃ (t : (P : C) ⟶ K.X.cycles n) (β : (P : C) ⟶ (K.inducedFiltrationStep n p : C)),
      t ≫ K.X.iCycles n = P.arrow ∧
        β ≫ (K.inducedFiltrationStep n p).arrow = t ≫ K.X.homologyπ n := by
  obtain ⟨w, hw⟩ :=
    exists_factorThru_pullback_iCycles K n p F P hPF
      (K.X.liftCycles P.arrow (n + 1) (by simp) hPd) (by simp)
  obtain ⟨b, -, hb⟩ := exists_epi_comp_image_ι_homologyMap_filtration K p n F _ hF rfl
  refine ⟨K.X.liftCycles P.arrow (n + 1) (by simp) hPd,
    w ≫ b ≫ (imageSubobjectIso _).inv, by simp, ?_⟩
  rw [Category.assoc, Category.assoc, imageSubobjectIso_inv_comp_arrow, hb, ← Category.assoc, hw]

section Convergence

variable (K : Filtered C) (F : ∀ (_p n : ℤ), Subobject (K.X.X n))
  (hF : ∀ p n : ℤ, F p n = Subobject.mk ((K.filtration.ι.app (op p)).f n))
  (Z : ∀ (_r _p n : ℤ), Subobject (K.X.X n))
  (hZ : ∀ r p n : ℤ, Z r p n =
    F p n ⊓ (Subobject.pullback (K.X.d n (n + 1))).obj (F (p + r) (n + 1)))
  (D : ∀ (_r _p n : ℤ), Subobject (K.X.X n))
  (hD : ∀ r p n : ℤ, D r p n = Z (r - 1) (p + 1) n ⊔
    (Subobject.«exists» (K.X.d (n - 1) n)).obj (Z (r - 1) (p - r + 1) (n - 1)))
  (E : CohomologicalSpectralSequence C 0)
  (hE : ∀ (r p q n : ℤ) (hr : 0 ≤ r) (_ : n = p + q), (E.page r hr).X (p, q) ≅
    cokernel (Subobject.ofLE _ _ (inf_le_right : D r p n ⊓ Z r p n ≤ Z r p n)))

include hE

include hZ

/-- Where the filtration of `K^{n+1}` has vanished, the target of the differential out of
`(p, q)` on the page `r` is zero. -/
private lemma isZero_page_target (r p q : ℤ) (hr : 0 ≤ r)
    (h : F (p + r) (p + q + 1) = ⊥) :
    IsZero ((E.page r hr).X (p + r, q + (1 - r))) := by
  refine isZero_page K Z D E hE r (p + r) (q + (1 - r)) (p + q + 1) hr (by omega)
    (le_of_eq_of_le ?_ bot_le)
  rw [hZ _ _ _, h, bot_inf_eq]

include hD hF

/-- Where the filtration of `K^{n-1}` is everything, the source of the differential into `(p, q)`
on the page `r` is zero. -/
private lemma isZero_page_source (r p q : ℤ) (hr : 0 ≤ r)
    (h : F (p - r + 1) (p + q - 1) = ⊤) :
    IsZero ((E.page r hr).X (p - r, q + r - 1)) := by
  refine isZero_page K Z D E hE r (p - r) (q + r - 1) (p + q - 1) hr (by omega) ?_
  rw [hD _ _ _]
  refine le_trans (le_of_eq ?_) le_sup_left
  rw [hZ _ _ _, hZ _ _ _, h, show p - r + 1 + (r - 1) = p by omega,
    show p + q - 1 + 1 = p + q by omega, top_inf_eq,
    top_le_iff.mp ((h).ge.trans (F_antitone K F hF (p - r) (p - r + 1) (p + q - 1) (by omega))),
    top_inf_eq, show p - r + r = p by omega]

/-- A page from which all the differentials into and out of `(p, q)` vanish, given that the
filtration of `K^{n+1}` has vanished and that of `K^{n-1}` is everything from that page on. -/
private lemma mem_hasEdgeMonoSet_and_hasEdgeEpiSet (R p q : ℤ) (hR : 0 ≤ R)
    (hb : ∀ r : ℤ, R ≤ r → F (p + r) (p + q + 1) = ⊥)
    (ha : ∀ r : ℤ, R ≤ r → F (p - r + 1) (p + q - 1) = ⊤) :
    R ∈ E.hasEdgeMonoSet (p, q) ∧ R ∈ E.hasEdgeEpiSet (p, q) := by
  refine ⟨⟨hR, fun r hr => ?_⟩, ⟨hR, fun r hr => ?_⟩⟩
  · -- the differentials into `(p, q)` all vanish: the source page object is zero
    have hz := isZero_page_source K F hF Z hZ D hD E hE r p q (by omega) (ha r hr)
    refine ⟨by omega, fun pq' => ?_⟩
    rcases eq_or_ne pq' (p - r, q + r - 1) with rfl | hne
    · exact hz.eq_of_src _ _
    · refine (E.page r (by omega)).shape _ _ fun hrel => hne ?_
      obtain ⟨h₁, h₂⟩ := Prod.ext_iff.mp hrel
      exact Prod.ext (by simp only [Prod.fst_add] at h₁; omega)
        (by simp only [Prod.snd_add] at h₂; omega)
  · -- the differentials out of `(p, q)` all vanish: the target page object is zero
    have hz := isZero_page_target K F Z hZ D E hE r p q (by omega) (hb r hr)
    refine ⟨by omega, fun pq' => ?_⟩
    rcases eq_or_ne pq' (p + r, q + (1 - r)) with rfl | hne
    · exact hz.eq_of_tgt _ _
    · exact (E.page r (by omega)).shape _ _ fun hrel => hne (by rw [← hrel]; rfl)

/-- **A stable page is a page from which all the differentials into and out of `(p, q)` vanish.**
`mem_hasEdgeMonoSet_and_hasEdgeEpiSet` read through `IsStableFrom`. -/
private lemma mem_hasEdgeSets_of_isStableFrom (p q R : ℤ) (hR : IsStableFrom K F p q R) :
    R ∈ E.hasEdgeMonoSet (p, q) ∧ R ∈ E.hasEdgeEpiSet (p, q) :=
  mem_hasEdgeMonoSet_and_hasEdgeEpiSet K F hF Z hZ D hD E hE R p q hR.zero_le hR.2.1 hR.2.2

/-- **A stable page makes the infinity page at `(p, q)` a genuine page of the sequence** and not
the fallback zero object.  This is `hasPageInfinityAt_of_isDegreewiseFinite'` with the stable page
supplied rather than chosen. -/
lemma hasPageInfinityAt_of_isStableFrom (p q R : ℤ) (hR : IsStableFrom K F p q R) :
    E.HasPageInfinityAt (p, q) :=
  ⟨⟨R, (mem_hasEdgeSets_of_isStableFrom K F hF Z hZ D hD E hE p q R hR).1⟩,
    ⟨R, (mem_hasEdgeSets_of_isStableFrom K F hF Z hZ D hD E hE p q R hR).2⟩⟩

/-- At a stable page the differentials into `(p, q)` have vanished for good. -/
lemma hasEdgeMonoAtFrom_of_isStableFrom (p q R : ℤ) (hR : IsStableFrom K F p q R)
    [E.HasPageInfinityAt (p, q)] :
    E.HasEdgeMonoAtFrom (p, q) R :=
  ⟨E.rToMin_LE (p, q) R (mem_hasEdgeSets_of_isStableFrom K F hF Z hZ D hD E hE p q R hR).1⟩

/-- At a stable page the differentials out of `(p, q)` have vanished for good. -/
lemma hasEdgeEpiAtFrom_of_isStableFrom (p q R : ℤ) (hR : IsStableFrom K F p q R)
    [E.HasPageInfinityAt (p, q)] :
    E.HasEdgeEpiAtFrom (p, q) R :=
  ⟨E.rFromMin_LE (p, q) R (mem_hasEdgeSets_of_isStableFrom K F hF Z hZ D hD E hE p q R hR).2⟩

/-- **Degreewise finiteness makes the inclusions (012S) and (012T) equalities.**  The fourth
conclusion of [Stacks, Tag 012W]: the stable cycles are `Ker(d^n) ∩ F^pK^n + F^{p+1}K^n` and the
stable boundaries are `Im(d^{n-1}) ∩ F^pK^n + F^{p+1}K^n`, each presented as the bound of the
family it is the limit of. -/
lemma isGLB_isLUB_stable (hK : K.filtration.IsDegreewiseFinite) (p n : ℤ) :
    IsGLB (Set.range fun r : ℕ =>
        F p n ⊓ (Subobject.pullback (K.X.d n (n + 1))).obj (F (p + r) (n + 1)) ⊔ F (p + 1) n)
      (kernelSubobject (K.X.d n (n + 1)) ⊓ F p n ⊔ F (p + 1) n) ∧
    IsLUB (Set.range fun r : ℕ =>
        F p n ⊓ (Subobject.«exists» (K.X.d (n - 1) n)).obj (F (p - r) (n - 1)) ⊔ F (p + 1) n)
      (imageSubobject (K.X.d (n - 1) n) ⊓ F p n ⊔ F (p + 1) n) :=
  (isBounded_and_converges_of_isDegreewiseFinite K hK F hF Z hZ D hD
    (fun m p' => K.inducedFiltrationStep m p') (fun _ _ => rfl) E hE).2.2.2.1 p n

/-- **`E_R^{p,q} ≅ gr^pH^{p+q}(K^•)` at a supplied stable page `R`.**  The seven-link chain of
`nonempty_pageInfinityIso_gr'`, as data and with the page `R` an argument instead of a choice:
the page identification `hE`, the two equality transports putting the page in the shape of (012S)
and (012T), the adjunction of `F^{p+1}K^n` to numerator and denominator (`cokernelIsoSup`), the
comparison of [Stacks, Tag 012V] (`CochainComplex.stablePageIsoGradedPiece`), and the two links
turning `Limits.image.preComp` into the quotient of two steps of the induced filtration.

Supplying `R` is what makes the identification comparable at two filtered complexes: a stable page
chosen separately at each of them is no common page, and
`CategoryTheory.SpectralSequence.Hom.mapPageInfinity_eq` needs one.  By `IsStableFrom.mono` a
common stable page always exists, so nothing is lost. -/
noncomputable def pageIsoGrAt (hK : K.filtration.IsDegreewiseFinite) (p q R : ℤ)
    (hR : IsStableFrom K F p q R) :
    (E.page R hR.zero_le).X (p, q) ≅
      cokernel (Subobject.ofLE (K.inducedFiltrationStep (p + q) (p + 1))
        (K.inducedFiltrationStep (p + q) p)
        (K.inducedFiltrationStep_succ_le (p + q) p)) :=
  hE R p q (p + q) hR.zero_le rfl ≪≫
    cokernelOfLEIso inf_le_right (boundaries_le_cycles_of_isStableFrom hF hZ hD hR)
      (inf_eq_left.mpr (boundaries_le_cycles_of_isStableFrom hF hZ hD hR)) rfl ≪≫
    cokernelIsoSup (D R p (p + q)) (Z R p (p + q)) (F (p + 1) (p + q))
      (boundaries_le_cycles_of_isStableFrom hF hZ hD hR)
      (inf_cycles_le_boundaries_of_isStableFrom hF hZ hD hR) ≪≫
    cokernelOfLEIso (sup_le_sup_right (boundaries_le_cycles_of_isStableFrom hF hZ hD hR) _)
      inf_le_right (sup_boundaries_eq_of_isStableFrom hZ hD hR)
      (sup_cycles_eq_of_isStableFrom hZ hR) ≪≫
    stablePageIsoGradedPiece K p (p + q) F _ _ _ hF rfl
      (isGLB_isLUB_stable K F hF Z hZ D hD E hE hK p (p + q)).1
      (isGLB_isLUB_stable K F hF Z hZ D hD E hE hK p (p + q)).2 rfl rfl _
      (stableCyclesLift_comp_arrow K p (p + q) F _ _ rfl
        (isGLB_isLUB_stable K F hF Z hZ D hD E hE hK p (p + q)).1)
      _ (toImageHomologyMap_comp_image_ι K p (p + q) F _ hF rfl) ≪≫
    preCompIsoGrInducedFiltration K (p + q) p

/-- **The equation characterising `pageIsoGrAt`.**  The class in `E_R^{p,q}` of a cycle of `K^•`
lying in `F^pK^n` -- that is, of an element of `Z_R^{p,q} = Ker(d^n) ∩ F^pK^n` -- goes to the class
in `gr^pH^n(K^•)` of its cohomology class.

`t` is the factorisation through the cycles of `K^•` and `β` the resulting map to `F^pH^n(K^•)`,
both supplied by `exists_liftCycles_toInducedFiltrationStep` and both unique, being pinned by
monomorphisms; so this equation determines `pageIsoGrAt` completely, the projection out of
`Z_R^{p,q}` being an epimorphism.

This is the whole content of the seven-link chain as far as naturality is concerned.  Both sides
are written in terms of `K^n`, `Z^n(K^•)` and `H^n(K^•)` only -- no stable cycles `Z_∞^{p,q}`, no
quotient of a `Subobject.ofLE` -- and a morphism of filtered complexes acts on each of those. -/
lemma π_pageIsoGrAt (hK : K.filtration.IsDegreewiseFinite) (p q R : ℤ)
    (hR : IsStableFrom K F p q R)
    (t : ((Z R p (p + q) : Subobject (K.X.X (p + q))) : C) ⟶ K.X.cycles (p + q))
    (ht : t ≫ K.X.iCycles (p + q) = (Z R p (p + q)).arrow)
    (β : ((Z R p (p + q) : Subobject (K.X.X (p + q))) : C) ⟶
      (K.inducedFiltrationStep (p + q) p : C))
    (hβ : β ≫ (K.inducedFiltrationStep (p + q) p).arrow = t ≫ K.X.homologyπ (p + q)) :
    cokernel.π (Subobject.ofLE _ _
          (inf_le_right : D R p (p + q) ⊓ Z R p (p + q) ≤ Z R p (p + q))) ≫
        (hE R p q (p + q) hR.zero_le rfl).inv ≫
          (pageIsoGrAt K F hF Z hZ D hD E hE hK p q R hR).hom =
      β ≫ cokernel.π (Subobject.ofLE (K.inducedFiltrationStep (p + q) (p + 1))
        (K.inducedFiltrationStep (p + q) p)
        (K.inducedFiltrationStep_succ_le (p + q) p)) := by
  obtain ⟨w, hw⟩ := exists_factorThru_pullback_iCycles K (p + q) p F (Z R p (p + q))
    (by rw [cycles_eq_inf_of_isStableFrom hZ hR]; exact inf_le_right) t ht
  have hGLB := (isGLB_isLUB_stable K F hF Z hZ D hD E hE hK p (p + q)).1
  have hLUB := (isGLB_isLUB_stable K F hF Z hZ D hD E hE hK p (p + q)).2
  -- the generator of the stable page comes from `A = Ker(d^n) ∩ F^pK^n`
  have hgen : Subobject.ofLE (Z R p (p + q))
        (kernelSubobject (K.X.d (p + q) (p + q + 1)) ⊓ F p (p + q) ⊔ F (p + 1) (p + q))
        (cycles_le_stableCycles_of_isStableFrom hZ hR) =
      w ≫ stableCyclesLift K p (p + q) F _ _ rfl hGLB :=
    (cancel_mono _).1 (by
      rw [Subobject.ofLE_arrow, Category.assoc, stableCyclesLift_comp_arrow, ← Category.assoc,
        hw, ht])
  -- and `β` is the cohomology class of that generator
  have hcls : w ≫ toImageHomologyMap K p (p + q) F _ hF rfl ≫
        (imageSubobjectIso (HomologicalComplex.homologyMap
          (K.filtration.ι.app (op p)) (p + q))).inv = β :=
    (cancel_mono (K.inducedFiltrationStep (p + q) p).arrow).1 (by
      rw [hβ, Category.assoc, Category.assoc, imageSubobjectIso_inv_comp_arrow,
        toImageHomologyMap_comp_image_ι, ← Category.assoc, hw])
  -- the middle transport, crossed by the generator on either side
  have hmid := comp_π_cokernelOfLEIso
      (sup_le_sup_right (boundaries_le_cycles_of_isStableFrom hF hZ hD hR) (F (p + 1) (p + q)))
      (inf_le_right :
        (imageSubobject (K.X.d (p + q - 1) (p + q)) ⊓ F p (p + q) ⊔ F (p + 1) (p + q)) ⊓
            (kernelSubobject (K.X.d (p + q) (p + q + 1)) ⊓ F p (p + q) ⊔ F (p + 1) (p + q)) ≤
          kernelSubobject (K.X.d (p + q) (p + q + 1)) ⊓ F p (p + q) ⊔ F (p + 1) (p + q))
      (sup_boundaries_eq_of_isStableFrom hZ hD hR) (sup_cycles_eq_of_isStableFrom hZ hR)
      (Subobject.ofLE (Z R p (p + q)) (Z R p (p + q) ⊔ F (p + 1) (p + q)) le_sup_left)
      (Subobject.ofLE (Z R p (p + q))
        (kernelSubobject (K.X.d (p + q) (p + q + 1)) ⊓ F p (p + q) ⊔ F (p + 1) (p + q))
        (cycles_le_stableCycles_of_isStableFrom hZ hR))
      (by rw [Subobject.ofLE_arrow, Subobject.ofLE_arrow])
  simp only [pageIsoGrAt, Iso.trans_hom, Iso.inv_hom_id_assoc]
  rw [π_cokernelOfLEIso_assoc, π_cokernelIsoSup_assoc, reassoc_of% hmid, hgen, Category.assoc,
    reassoc_of% (stablePageIsoGradedPiece_spec K p (p + q) F _ _ _ hF rfl hGLB hLUB rfl rfl _
      (stableCyclesLift_comp_arrow K p (p + q) F _ _ rfl hGLB) _
      (toImageHomologyMap_comp_image_ι K p (p + q) F _ hF rfl)),
    ← hcls, Category.assoc, Category.assoc]
  exact congrArg (fun u => w ≫ toImageHomologyMap K p (p + q) F
      ((Subobject.pullback (K.X.iCycles (p + q))).obj (F p (p + q))) hF rfl ≫ u)
    (π_preCompIsoGrInducedFiltration K (p + q) p)

/-- **Degreewise finiteness makes the spectral sequence stabilise at every bidegree.** All the
differentials into and out of `(p, q)` vanish from some page on, so the infinity page `E_∞^{p,q}`
is the stable page `E_{rMin}^{p,q}` and not the fallback zero object. -/
theorem hasPageInfinityAt_of_isDegreewiseFinite' (hK : K.filtration.IsDegreewiseFinite)
    (p q : ℤ) :
    E.HasPageInfinityAt (p, q) := by
  obtain ⟨R, hR⟩ := exists_isStableFrom K F hF hK p q
  exact hasPageInfinityAt_of_isStableFrom K F hF Z hZ D hD E hE p q R hR

/-- **`E_∞^{p,q} ≅ gr^pH^{p+q}(K^•)` at a supplied stable page `R`.**  `pageIsoGrAt` read on the
infinity page: `CategoryTheory.SpectralSequence.pageInfinityIso` identifies `E_∞^{p,q}` with
`E_R^{p,q}` at any page from which the differentials into and out of `(p, q)` have vanished, and a
stable page is such a page.

The three instance arguments are consequences of `hR` -- see
`hasPageInfinityAt_of_isStableFrom`, `hasEdgeMonoAtFrom_of_isStableFrom` and
`hasEdgeEpiAtFrom_of_isStableFrom` -- and are taken as arguments only so that this definition and
a statement about it can both name the same instances. -/
noncomputable def pageInfinityIsoGrAt (hK : K.filtration.IsDegreewiseFinite) (p q R : ℤ)
    (hR : IsStableFrom K F p q R) [E.HasPageInfinityAt (p, q)]
    [E.HasEdgeMonoAtFrom (p, q) R] [E.HasEdgeEpiAtFrom (p, q) R] :
    E.pageInfinity (p, q) ≅
      cokernel (Subobject.ofLE (K.inducedFiltrationStep (p + q) (p + 1))
        (K.inducedFiltrationStep (p + q) p) (K.inducedFiltrationStep_succ_le (p + q) p)) :=
  E.pageInfinityIso (p, q) R ≪≫ pageIsoGrAt K F hF Z hZ D hD E hE hK p q R hR

/-- **`E_∞^{p,q} ≅ gr^p H^{p+q}(K^•)`.**  For a filtered complex `(K^•, F)` of an abelian
category whose filtration is finite in each degree, the infinity page of its spectral sequence at
the bidegree `(p, q)` is the `p`-th graded piece of the filtration induced on `H^{p+q}(K^•)`.

This is the convergence datum of [Stacks, Tag 012W](3): the spectral sequence converges to
`H^*(K^•)`.  Degreewise finiteness of the filtration is the only hypothesis; the boundedness, the
finiteness of the induced filtration, the regularity and the two equalities (012S), (012T) that
the statement of 012W lists separately are all consequences of it, and are discharged here.

The isomorphism is `pageInfinityIsoGrAt` at a stable page chosen by `exists_isStableFrom`; only
its existence is asserted, because a page chosen here is not a page chosen anywhere else. -/
@[stacks 012W "(3), the comparison `E_∞^{p,q} ≅ gr^pH^n(K^•)` of (012V) is an isomorphism"]
theorem nonempty_pageInfinityIso_gr' (hK : K.filtration.IsDegreewiseFinite) (p q : ℤ) :
    Nonempty (E.pageInfinity (p, q) ≅
      (FilteredObject.gr p).obj (K.inducedFilteredObject (p + q))) := by
  rw [gr_inducedFilteredObject K (p + q) p]
  obtain ⟨R, hR⟩ := exists_isStableFrom K F hF hK p q
  have := hasPageInfinityAt_of_isStableFrom K F hF Z hZ D hD E hE p q R hR
  have := hasEdgeMonoAtFrom_of_isStableFrom K F hF Z hZ D hD E hE p q R hR
  have := hasEdgeEpiAtFrom_of_isStableFrom K F hF Z hZ D hD E hE p q R hR
  exact ⟨pageInfinityIsoGrAt K F hF Z hZ D hD E hE hK p q R hR⟩

end Convergence

/-! ### The convergence identification for the canonical spectral sequence -/

/-- **Degreewise finiteness makes the canonical spectral sequence stabilise at every bidegree.**
`hasPageInfinityAt_of_isDegreewiseFinite'` for
`CochainComplex.Filtered.spectralSequenceFunctor`. -/
theorem hasPageInfinityAt_of_isDegreewiseFinite (K : Filtered C)
    (hK : K.filtration.IsDegreewiseFinite) (p q : ℤ) :
    (spectralSequenceFunctor.obj K).HasPageInfinityAt (p, q) :=
  hasPageInfinityAt_of_isDegreewiseFinite' K (filtrationSubobject K) (fun _ _ => rfl)
    (cycles K.X (filtrationSubobject K)) (fun _ _ _ => rfl)
    (boundaries K.X (filtrationSubobject K)) (fun _ _ _ => rfl) _
    (fun r p' q' n' hr hn' => by subst hn'; exact pageIso K r p' q' hr) hK p q

/-- **`E_∞^{p,q} ≅ gr^p H^{p+q}(K^•)` for the canonical spectral sequence of a filtered
complex.**  `nonempty_pageInfinityIso_gr'` for
`CochainComplex.Filtered.spectralSequenceFunctor`, whose pages are the subquotients
`Z_r^{p,q}/(D_r^{p,q} ⊓ Z_r^{p,q})` on the nose. -/
@[stacks 012W "(3), for the canonical spectral sequence of a filtered complex",
  sga "4 Vbis 2.5.2" "partial"]
theorem nonempty_pageInfinityIso_gr (K : Filtered C)
    (hK : K.filtration.IsDegreewiseFinite) (p q : ℤ) :
    Nonempty ((spectralSequenceFunctor.obj K).pageInfinity (p, q) ≅
      (FilteredObject.gr p).obj (K.inducedFilteredObject (p + q))) :=
  nonempty_pageInfinityIso_gr' K (filtrationSubobject K) (fun _ _ => rfl)
    (cycles K.X (filtrationSubobject K)) (fun _ _ _ => rfl)
    (boundaries K.X (filtrationSubobject K)) (fun _ _ _ => rfl) _
    (fun r p' q' n' hr hn' => by subst hn'; exact pageIso K r p' q' hr) hK p q

/-- **`E_∞^{p,q} ≅ gr^p H^{p+q}(K^•)`**, as data: the convergence identification of
`nonempty_pageInfinityIso_gr'`, chosen.  This is the isomorphism a filtered abutment datum such as
`Stacks.Cohomology.Leray.FirstQuadrantAbutment.gradedIso` asks for.  It is only a choice: the
comparison of [Stacks, Tag 012V] is itself produced by an existence statement, so no canonical
isomorphism is available at this generality. -/
noncomputable def pageInfinityIsoGr (K : Filtered C) (F : ∀ (_p n : ℤ), Subobject (K.X.X n))
    (hF : ∀ p n : ℤ, F p n = Subobject.mk ((K.filtration.ι.app (op p)).f n))
    (Z : ∀ (_r _p n : ℤ), Subobject (K.X.X n))
    (hZ : ∀ r p n : ℤ, Z r p n =
      F p n ⊓ (Subobject.pullback (K.X.d n (n + 1))).obj (F (p + r) (n + 1)))
    (D : ∀ (_r _p n : ℤ), Subobject (K.X.X n))
    (hD : ∀ r p n : ℤ, D r p n = Z (r - 1) (p + 1) n ⊔
      (Subobject.«exists» (K.X.d (n - 1) n)).obj (Z (r - 1) (p - r + 1) (n - 1)))
    (E : CohomologicalSpectralSequence C 0)
    (hE : ∀ (r p q n : ℤ) (hr : 0 ≤ r) (_ : n = p + q), (E.page r hr).X (p, q) ≅
      cokernel (Subobject.ofLE _ _ (inf_le_right : D r p n ⊓ Z r p n ≤ Z r p n)))
    (hK : K.filtration.IsDegreewiseFinite) (p q : ℤ) :
    E.pageInfinity (p, q) ≅ (FilteredObject.gr p).obj (K.inducedFilteredObject (p + q)) :=
  (nonempty_pageInfinityIso_gr' K F hF Z hZ D hD E hE hK p q).some

/-! ### Naturality of the convergence identification

The two obstructions to naturality that the implementation notes above record are both removed at
this specialisation.  The page identification `hE`, an unconstrained family of isomorphisms at the
generality of `nonempty_pageInfinityIso_gr'`, is here `FilteredComplexSpectralSequence.eIso`, whose
components are identities, so every square through it commutes; and the stable page is supplied
rather than chosen, so one page can serve two filtered complexes at once (`IsStableFrom.mono`
produces it as a maximum).

Naturality does *not* need the functoriality of the subobject bookkeeping those notes also ask for
-- no morphism `Z_∞^{p,q}(K) ⟶ Z_∞^{p,q}(L)`, and none of the commuting squares of quotients of
`Subobject.ofLE`.  The reason is `π_pageIsoGrAt`: the chain is pinned by an equation both of whose
sides live on `Z_R^{p,q}`, `Z^n(K^•)` and `H^n(K^•)` only.  Cancelling the epimorphism
`cokernel.π` on the source and the monomorphism `F^pH^n(L^•) ⟶ H^n(L^•)` on the target reduces the
naturality square to the commuting square of `φ` over `K^n ⟶ L^n`, where the identity holds for the
reason it always does.

The spectral sequence is named here as `CochainComplex.filteredSpectralSequence K` and the induced
morphism as `CochainComplex.filteredSpectralSequenceMap φ`, which are
`CochainComplex.Filtered.spectralSequenceFunctor.obj K` and `.map φ` -- by
`CochainComplex.Filtered.spectralSequenceFunctor_obj` and
`CochainComplex.Filtered.spectralSequenceFunctor_map`, both `rfl`.  The point of the choice is
transparency: through `filteredSpectralSequence` the page object `E_R^{p,q}` unfolds to the
subquotient `Z_R^{p,q}/(D_R^{p,q} ⊓ Z_R^{p,q})` by reducible definitions only, which is what lets
the subquotient-level facts (`FilteredComplexSpectralSequence.π_pageObjMap`) be rewritten into a
statement about the page. -/

/-- **The graded piece of the induced filtration is computed on the steps.**  A morphism `ψ` of
the filtered cohomologies restricts to a map `σ` of the `p`-th steps lying over its underlying
morphism `f`, and `gr^p(ψ)` is the morphism `σ` descends to.

Stated existentially, and with the underlying morphism supplied separately, so that `σ` and `f`
carry the types `F^pH^n(K^•) ⟶ F^pH^n(L^•)` and `H^n(K^•) ⟶ H^n(L^•)` rather than the
`CategoryTheory.FilteredObject` spellings of them. -/
lemma exists_inducedFiltrationStep_map {K L : Filtered C} (n p : ℤ)
    (ψ : K.inducedFilteredObject n ⟶ L.inducedFilteredObject n)
    (f : K.X.homology n ⟶ L.X.homology n) (hf : ψ.hom = f) :
    ∃ σ : (K.inducedFiltrationStep n p : C) ⟶ (L.inducedFiltrationStep n p : C),
      σ ≫ (L.inducedFiltrationStep n p).arrow =
          (K.inducedFiltrationStep n p).arrow ≫ f ∧
        cokernel.π (Subobject.ofLE (K.inducedFiltrationStep n (p + 1))
            (K.inducedFiltrationStep n p) (K.inducedFiltrationStep_succ_le n p)) ≫
            (FilteredObject.gr p).map ψ =
          σ ≫ cokernel.π (Subobject.ofLE (L.inducedFiltrationStep n (p + 1))
            (L.inducedFiltrationStep n p) (L.inducedFiltrationStep_succ_le n p)) :=
  ⟨ψ.natTrans.app (op p), hf ▸ ψ.comm (op p),
    FilteredObject.grMapπ_map (FilteredObject.succHom p) ψ⟩

/-- **The map a morphism of filtered complexes induces on the pages of the canonical spectral
sequence** is `FilteredComplexSpectralSequence.pageObjMap`, the map on the subquotients
`Z_r^{p,q}/(D_r^{p,q} ⊓ Z_r^{p,q})` of [Stacks, Tag 012O]. -/
lemma filteredSpectralSequenceMap_hom_f {K L : Filtered C} (φ : K ⟶ L) (r : ℤ) (hr : 0 ≤ r)
    (p q : ℤ) :
    ((filteredSpectralSequenceMap φ).hom r hr).f (p, q) =
      pageObjMap φ.hom (exists_filtrationSubobject_le φ) r p (p + q) :=
  rfl

/-- **`E_R^{p,q} ≅ gr^pH^{p+q}(K^•)` for the canonical spectral sequence, at a supplied stable
page.**  `pageIsoGrAt` for `CochainComplex.filteredSpectralSequence`, whose page identification
`FilteredComplexSpectralSequence.eIso` is an identity. -/
noncomputable def canonicalPageIsoGr (K : Filtered C)
    (hK : K.filtration.IsDegreewiseFinite) (p q R : ℤ)
    (hR : IsStableFrom K (filtrationSubobject K) p q R) :
    ((filteredSpectralSequence K).page R hR.zero_le).X (p, q) ≅
      cokernel (Subobject.ofLE (K.inducedFiltrationStep (p + q) (p + 1))
        (K.inducedFiltrationStep (p + q) p) (K.inducedFiltrationStep_succ_le (p + q) p)) :=
  pageIsoGrAt K (filtrationSubobject K) (fun _ _ => rfl)
    (cycles K.X (filtrationSubobject K)) (fun _ _ _ => rfl)
    (boundaries K.X (filtrationSubobject K)) (fun _ _ _ => rfl) _
    (eIso K.X (filtrationSubobject K) (filtrationSubobject_antitone K)) hK p q R hR

/-- **The equation characterising `canonicalPageIsoGr`.**  `π_pageIsoGrAt` with the page
identification cancelled: the class of a cycle of `K^•` lying in `F^pK^n` goes to the class in
`gr^pH^n(K^•)` of its cohomology class. -/
@[reassoc]
lemma π_canonicalPageIsoGr (K : Filtered C)
    (hK : K.filtration.IsDegreewiseFinite) (p q R : ℤ)
    (hR : IsStableFrom K (filtrationSubobject K) p q R)
    (t : ((cycles K.X (filtrationSubobject K) R p (p + q) : Subobject (K.X.X (p + q))) : C) ⟶
      K.X.cycles (p + q))
    (ht : t ≫ K.X.iCycles (p + q) = (cycles K.X (filtrationSubobject K) R p (p + q)).arrow)
    (β : ((cycles K.X (filtrationSubobject K) R p (p + q) : Subobject (K.X.X (p + q))) : C) ⟶
      (K.inducedFiltrationStep (p + q) p : C))
    (hβ : β ≫ (K.inducedFiltrationStep (p + q) p).arrow = t ≫ K.X.homologyπ (p + q)) :
    cokernel.π (den K.X (filtrationSubobject K) R p (p + q)) ≫
        (canonicalPageIsoGr K hK p q R hR).hom =
      β ≫ cokernel.π (Subobject.ofLE (K.inducedFiltrationStep (p + q) (p + 1))
        (K.inducedFiltrationStep (p + q) p) (K.inducedFiltrationStep_succ_le (p + q) p)) := by
  simpa [canonicalPageIsoGr] using
    π_pageIsoGrAt K (filtrationSubobject K) (fun _ _ => rfl)
      (cycles K.X (filtrationSubobject K)) (fun _ _ _ => rfl)
      (boundaries K.X (filtrationSubobject K)) (fun _ _ _ => rfl) _
      (eIso K.X (filtrationSubobject K) (filtrationSubobject_antitone K)) hK p q R hR t ht β hβ

/-- **The convergence identification of the canonical spectral sequence is natural in the filtered
complex**, at a page stable for both. This is the natural variant of
`nonempty_pageInfinityIso_gr'` read on the page `R`; `canonicalPageInfinityIsoGr_naturality` is the
same statement on the infinity page.

`ψ` is any morphism of filtered objects whose underlying morphism is `H^n(φ)` -- for instance
`CochainComplex.Filtered.inducedFilteredObjectMap φ (p + q)`, whose underlying morphism is `H^n(φ)`
by definition.  Nothing more about `ψ` is used, and nothing more is available: a morphism of
filtered objects is determined by its underlying morphism. -/
theorem canonicalPageIsoGr_naturality {K L : Filtered C} (φ : K ⟶ L)
    (hK : K.filtration.IsDegreewiseFinite) (hL : L.filtration.IsDegreewiseFinite)
    (p q R : ℤ) (hRK : IsStableFrom K (filtrationSubobject K) p q R)
    (hRL : IsStableFrom L (filtrationSubobject L) p q R)
    (ψ : K.inducedFilteredObject (p + q) ⟶ L.inducedFilteredObject (p + q))
    (hψ : ψ.hom = HomologicalComplex.homologyMap φ.hom (p + q)) :
    ((filteredSpectralSequenceMap φ).hom R hRK.zero_le).f (p, q) ≫
        (canonicalPageIsoGr L hL p q R hRL).hom =
      (canonicalPageIsoGr K hK p q R hRK).hom ≫ (FilteredObject.gr p).map ψ := by
  -- the cycles of `Z_R^{p,q}`, lifted to `Z^n` and sent to `F^pH^n`, at both filtered complexes
  obtain ⟨tK, βK, htK, hβK⟩ := exists_liftCycles_toInducedFiltrationStep K (p + q) p
    (filtrationSubobject K) (fun _ _ => rfl) _
    (cycles_le_F K.X (filtrationSubobject K) R p (p + q))
    (arrow_comp_d_eq_zero_of_isStableFrom (fun _ _ _ => rfl) hRK)
  obtain ⟨tL, βL, htL, hβL⟩ := exists_liftCycles_toInducedFiltrationStep L (p + q) p
    (filtrationSubobject L) (fun _ _ => rfl) _
    (cycles_le_F L.X (filtrationSubobject L) R p (p + q))
    (arrow_comp_d_eq_zero_of_isStableFrom (fun _ _ _ => rfl) hRL)
  obtain ⟨σ, hσ, hσgr⟩ := exists_inducedFiltrationStep_map (p + q) p ψ _ hψ
  -- `φ` carries the lift to the lift, both lying over `K^n ⟶ L^n` with `Z^n(L^•)` a subobject
  have hlift : cyclesMap φ.hom (exists_filtrationSubobject_le φ) R p (p + q) ≫ tL =
      tK ≫ HomologicalComplex.cyclesMap φ.hom (p + q) :=
    (cancel_mono (L.X.iCycles (p + q))).1 (by
      rw [Category.assoc, htL, cyclesMap_arrow, Category.assoc,
        HomologicalComplex.cyclesMap_i, ← Category.assoc, htK])
  -- hence it carries the cohomology class to the cohomology class, `F^pH^n(L^•)` being a
  -- subobject of `H^n(L^•)`
  have hcls : cyclesMap φ.hom (exists_filtrationSubobject_le φ) R p (p + q) ≫ βL = βK ≫ σ :=
    (cancel_mono (L.inducedFiltrationStep (p + q) p).arrow).1 <|
      calc (cyclesMap φ.hom (exists_filtrationSubobject_le φ) R p (p + q) ≫ βL) ≫
              (L.inducedFiltrationStep (p + q) p).arrow
          = (cyclesMap φ.hom (exists_filtrationSubobject_le φ) R p (p + q) ≫ tL) ≫
              L.X.homologyπ (p + q) := by rw [Category.assoc, hβL, Category.assoc]
        _ = tK ≫ HomologicalComplex.cyclesMap φ.hom (p + q) ≫ L.X.homologyπ (p + q) := by
              rw [hlift, Category.assoc]
        _ = (tK ≫ K.X.homologyπ (p + q)) ≫ HomologicalComplex.homologyMap φ.hom (p + q) := by
              rw [← HomologicalComplex.homologyπ_naturality, Category.assoc]
        _ = (βK ≫ (K.inducedFiltrationStep (p + q) p).arrow) ≫
              HomologicalComplex.homologyMap φ.hom (p + q) := by rw [hβK]
        _ = (βK ≫ σ) ≫ (L.inducedFiltrationStep (p + q) p).arrow := by
              rw [Category.assoc, Category.assoc, hσ]
  -- the square, after cancelling the projection onto the page
  refine (cancel_epi (cokernel.π (den K.X (filtrationSubobject K) R p (p + q)))).1 ?_
  rw [filteredSpectralSequenceMap_hom_f, π_pageObjMap_assoc,
    π_canonicalPageIsoGr L hL p q R hRL tL htL βL hβL, ← Category.assoc, hcls, Category.assoc,
    ← hσgr]
  exact (π_canonicalPageIsoGr_assoc K hK p q R hRK tK htK βK hβK
    ((FilteredObject.gr p).map ψ)).symm

/-- **`E_∞^{p,q} ≅ gr^pH^{p+q}(K^•)` for the canonical spectral sequence, at a supplied stable
page.**  `canonicalPageIsoGr` read on the infinity page.

The three instance arguments are consequences of `hR` -- see `hasPageInfinityAt_of_isStableFrom`,
`hasEdgeMonoAtFrom_of_isStableFrom` and `hasEdgeEpiAtFrom_of_isStableFrom` -- and are taken as
arguments only so that this definition and `canonicalPageInfinityIsoGr_naturality` name the same
instances. -/
noncomputable def canonicalPageInfinityIsoGr (K : Filtered C)
    (hK : K.filtration.IsDegreewiseFinite) (p q R : ℤ)
    (hR : IsStableFrom K (filtrationSubobject K) p q R)
    [(filteredSpectralSequence K).HasPageInfinityAt (p, q)]
    [(filteredSpectralSequence K).HasEdgeMonoAtFrom (p, q) R]
    [(filteredSpectralSequence K).HasEdgeEpiAtFrom (p, q) R] :
    (filteredSpectralSequence K).pageInfinity (p, q) ≅
      cokernel (Subobject.ofLE (K.inducedFiltrationStep (p + q) (p + 1))
        (K.inducedFiltrationStep (p + q) p) (K.inducedFiltrationStep_succ_le (p + q) p)) :=
  (filteredSpectralSequence K).pageInfinityIso (p, q) R ≪≫ canonicalPageIsoGr K hK p q R hR

/-- **The convergence identification `E_∞^{p,q} ≅ gr^pH^{p+q}` of the canonical spectral sequence
is natural in the filtered complex**, at a page stable for both.

This is the natural variant of `nonempty_pageInfinityIso_gr'` and of `pageInfinityIsoGr`, stated
where it can be stated: at the canonical spectral sequence of a filtered complex, with a common
stable page.  `CategoryTheory.SpectralSequence.Hom.mapPageInfinity_eq` computes the map induced on
the infinity pages on that common page, where it is the map on the subquotients of
[Stacks, Tag 012O], and `canonicalPageIsoGr_naturality` is the square there. -/
theorem canonicalPageInfinityIsoGr_naturality {K L : Filtered C} (φ : K ⟶ L)
    (hK : K.filtration.IsDegreewiseFinite) (hL : L.filtration.IsDegreewiseFinite)
    (p q R : ℤ) (hRK : IsStableFrom K (filtrationSubobject K) p q R)
    (hRL : IsStableFrom L (filtrationSubobject L) p q R)
    (ψ : K.inducedFilteredObject (p + q) ⟶ L.inducedFilteredObject (p + q))
    (hψ : ψ.hom = HomologicalComplex.homologyMap φ.hom (p + q))
    [(filteredSpectralSequence K).HasPageInfinityAt (p, q)]
    [(filteredSpectralSequence L).HasPageInfinityAt (p, q)]
    [(filteredSpectralSequence K).HasEdgeMonoAtFrom (p, q) R]
    [(filteredSpectralSequence K).HasEdgeEpiAtFrom (p, q) R]
    [(filteredSpectralSequence L).HasEdgeMonoAtFrom (p, q) R]
    [(filteredSpectralSequence L).HasEdgeEpiAtFrom (p, q) R] :
    SpectralSequence.Hom.mapPageInfinity (filteredSpectralSequenceMap φ) (p, q) ≫
        (canonicalPageInfinityIsoGr L hL p q R hRL).hom =
      (canonicalPageInfinityIsoGr K hK p q R hRK).hom ≫ (FilteredObject.gr p).map ψ := by
  rw [SpectralSequence.Hom.mapPageInfinity_eq (filteredSpectralSequenceMap φ) (p, q) R
      hRK.zero_le, canonicalPageInfinityIsoGr, canonicalPageInfinityIsoGr]
  simp only [Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc]
  exact (congrArg (fun u => ((filteredSpectralSequence K).pageInfinityIso (p, q) R).hom ≫ u)
    (canonicalPageIsoGr_naturality φ hK hL p q R hRK hRL ψ hψ)).trans
    (Category.assoc _ _ _).symm

end CochainComplex.Filtered

end
