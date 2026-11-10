module

public import Mathlib.Algebra.Homology.SingleHomology
public import StacksFrontier.Algebra.Homology.SpectralSequence.DoubleComplexNaturality
public import StacksFrontier.Algebra.Homology.SpectralSequence.NatRestrict
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The second spectral sequence of a double complex as a first-quadrant `E₂` functor

[Stacks, Tag 01ES] needs a functor `D ⥤ E₂CohomologicalSpectralSequenceNat 𝒜` together with a
*natural* identification of its second page. The ingredients are all present in the library but
they do not meet: the Tag 01ES development has the functor
`Stacks.Cohomology.CechSpectral.totalSpectralSequence₂Functor` on `ℤ × ℤ`,
`StacksFrontier/Algebra/Homology/SpectralSequence/DoubleComplexNaturality.lean` has the naturality
of `''E_2^{p,q} = H^p_{II}(H^q_I(K^{•,•}))` -- but for `spectralSequence₂` and
`spectralSequenceMap₂`, which are not assembled into a functor -- and
`StacksFrontier/Algebra/Homology/SpectralSequence/NatRestrict.lean` has the index conversion
`ℤ × ℤ → ℕ × ℕ`. This file joins them.

Three things here are not restatements.

*The functor.* `spectralSequence₂Functor` is the second spectral sequence as a functor built from
`spectralSequenceMap₂`, which is the morphism the naturality theorem of
`DoubleComplexNaturality.lean` is about.
`Stacks.Cohomology.CechSpectral.totalSpectralSequence₂Functor` is *equal* to it objectwise
(`spectralSequence₂Functor_obj`) but presents the filtration steps
differently, so the naturality theorem cannot be read as a statement about its `map`.

*The second page, naturally.* `pageTwoNatIso` is the identification
`''E_2^{p,q} ≅ H^p_{II}(H^q_I(-))` as a natural isomorphism of functors. This is the `def`-form,
natural refinement of `HomologicalComplex₂.exists_iso_pages_totalFiltration₂` that
[Stacks, Tag 01ES] needs and the library did not have; the data
is `isoTwoPageTotalFiltration₂` and the square is
`isoTwoPageTotalFiltration₂_naturality_functor`.

*Functoriality from homotopy classes.* `e₂FunctorOfHomotopyClasses` builds the `E₂` functor from a
double complex depending functorially on an object of `D` only *up to filtered homotopy*: the
assignment `X ↦ K(X)` on objects and a choice of `K(X) ⟶ K(Y)` for each morphism, with the functor
laws required only up to `FilteredHomotopy₂`. This is the shape in which a Čech double complex
built from injective resolutions is functorial -- an injective resolution is functorial into the
homotopy category and no further -- and it works because
`CochainComplex.filteredSpectralSequenceMap_hom_eq_of_filteredHomotopic` makes the induced map on
the pages `E_r`, `r ≥ 1`, independent of the choice. The target is `E₂`-presented for exactly that
reason: homotopy invariance fails on the zeroth page.

## Main definitions

* `HomologicalComplex₂.homologyIIHomologyIFunctor`: the functor `H^p_{II}(H^q_I(-))`.
* `HomologicalComplex₂.spectralSequence₂Functor`: the second spectral sequence of a double
  complex, as a functor, with `spectralSequenceMap₂` as its action on morphisms.
* `HomologicalComplex₂.e₂SpectralSequence₂Functor`: the same, presented from its second page.
* `HomologicalComplex₂.FilteredHomotopy₂`: two morphisms of double complexes are filtered
  homotopic when their total complexes are homotopic through a homotopy preserving the filtration
  by the second coordinate.
* `HomologicalComplex₂.e₂FunctorOfHomotopyClasses`: the `E₂` functor attached to a double complex
  which is functorial only up to filtered homotopy.

## Main results

* `HomologicalComplex₂.pageTwoNatIso`: `''E_2^{p,q} ≅ H^p_{II}(H^q_I(-))`, naturally in the double
  complex.
* `HomologicalComplex₂.isFirstQuadrant_e₂SpectralSequence₂Functor`: a double complex whose
  `H^p_{II}(H^q_I(-))` vanishes outside the first quadrant has a first-quadrant second spectral
  sequence, so `CategoryTheory.SpectralSequence.natRestrictE₂Comp` applies to it.
* `HomologicalComplex₂.spectralSequenceMap₂_hom_eq_of_filteredHomotopy₂`: filtered homotopic
  morphisms of double complexes induce the same map on the pages `E_r`, `r ≥ 1`.
* `HomologicalComplex₂.pageTwoIso_naturality_of_homotopyClasses`: the second-page identification
  is natural for `e₂FunctorOfHomotopyClasses` as well.
* `HomologicalComplex₂.not_forall_isFirstQuadrant`: over a category with a nonzero object, no
  double complex-indexed family of first-quadrant hypotheses holds for *every* double complex, so
  the first-quadrant restriction has to be made functor by functor.
* `CategoryTheory.SpectralSequence.natRestrictE₂Comp_pageTwoIso`: the second page of a
  first-quadrant restriction at `(p, q) : ℕ × ℕ` is the second page of the original at
  `((p : ℤ), (q : ℤ))`.

## Implementation notes

**Nothing here carries the tag `01ES`, and this file does not prove it.** What it does not supply
is the Čech double complex of an injective resolution -- for which the two engines above are the
intended input -- and the filtered abutment, which needs the identification
`E_∞^{p,q} ≅ gr^p H^{p+q}`; the latter exists in the library only as the existence statement
`CochainComplex.exists_epi_gradedPiece_homology_of_isGLB_isLUB` of
`StacksFrontier/Algebra/Homology/SpectralSequence/FilteredComplex/Basic.lean`, which gives
`gr^p H^n` as a subquotient of `E_∞^{p, n - p}` rather than as a quotient of it.

`Stacks.Cohomology.CechSpectral.totalE₂SpectralSequenceNat₂Functor` is *not* usable for this
purpose: its hypothesis is
first-quadrant vanishing for **every** double complex over the ambient category, which is false as
soon as that category has a nonzero object (a double complex concentrated in bidegree `(0, -1)`
has `''E_2^{-1,0} ≠ 0`). The first-quadrant hypothesis has to be imposed only on the double
complexes actually arising, which is what
`CategoryTheory.SpectralSequence.natRestrictE₂Comp` -- quantified over the objects of the source
category -- does, and which is why `isFirstQuadrant_e₂SpectralSequence₂Functor` below is stated
for a single double complex.

## References

* [Stacks Project, Tag 0130](https://stacks.math.columbia.edu/tag/0130)
* [Stacks Project, Tag 012O](https://stacks.math.columbia.edu/tag/012O)
* [Stacks Project, Tag 01ES](https://stacks.math.columbia.edu/tag/01ES)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace FilteredComplexSpectralSequence

variable {A : Type u} [Category.{v} A] [Abelian A] {K L : CochainComplex A ℤ}
  {FK : ℤ → ∀ n : ℤ, Subobject (K.X n)} {FL : ℤ → ∀ n : ℤ, Subobject (L.X n)}

/-- **The morphism of spectral sequences depends only on the morphism of complexes.** Its second
argument, the compatibility of that morphism with the two filtrations, is a proposition, so equal
morphisms of complexes give equal morphisms of spectral sequences however that compatibility is
proved. This is what lets a morphism of spectral sequences be rewritten along an identity such as
`HomologicalComplex₂.total.map_comp`, which cannot be rewritten under the binder. -/
lemma spectralSequenceMap_congr {φ ψ : K ⟶ L} (h : φ = ψ)
    (hφ : ∀ p n : ℤ, (Subobject.«exists» (φ.f n)).obj (FK p n) ≤ FL p n)
    (hψ : ∀ p n : ℤ, (Subobject.«exists» (ψ.f n)).obj (FK p n) ≤ FL p n)
    (hantiK : ∀ p p' n : ℤ, p ≤ p' → FK p' n ≤ FK p n)
    (hantiL : ∀ p p' n : ℤ, p ≤ p' → FL p' n ≤ FL p n) :
    spectralSequenceMap φ hφ hantiK hantiL = spectralSequenceMap ψ hψ hantiK hantiL := by
  subst h
  rfl

end FilteredComplexSpectralSequence

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

section HomologyII

variable (C)

/-- **The functor `H^p_{II}(H^q_I(-))`** on double complexes: homology in the first direction at
`q`, which leaves a cochain complex in the second direction, followed by homology of that complex
at `p`. This is the object [Stacks, Tag 0130] (6) identifies the second page of the second
spectral sequence with. -/
def homologyIIHomologyIFunctor (p q : ℤ) :
    HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⥤ C :=
  HomologicalComplex.homologyFunctor (HomologicalComplex C (ComplexShape.up ℤ))
      (ComplexShape.up ℤ) q ⋙
    HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) p

/-- `homologyIIHomologyIFunctor` at a double complex is `H^p(H^q_I(K^{•,•}))`. -/
lemma homologyIIHomologyIFunctor_obj (p q : ℤ)
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)) :
    (homologyIIHomologyIFunctor C p q).obj K = (K.homology q).homology p :=
  rfl

end HomologyII

section Functoriality

/-- **The second spectral sequence of a double complex is functorial: identities.** -/
lemma spectralSequenceMap₂_id
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] :
    spectralSequenceMap₂ (𝟙 K) = 𝟙 K.spectralSequence₂ :=
  (FilteredComplexSpectralSequence.spectralSequenceMap_congr
    (HomologicalComplex₂.total.map_id K (ComplexShape.up ℤ)) _
    FilteredComplexSpectralSequence.exists_id_f_le _ _).trans
    (FilteredComplexSpectralSequence.spectralSequenceMap_id _)

/-- **The second spectral sequence of a double complex is functorial: composition.** -/
lemma spectralSequenceMap₂_comp
    {K L M : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)}
    [K.HasTotal (ComplexShape.up ℤ)] [L.HasTotal (ComplexShape.up ℤ)]
    [M.HasTotal (ComplexShape.up ℤ)] (φ : K ⟶ L) (ψ : L ⟶ M) :
    spectralSequenceMap₂ (φ ≫ ψ) = spectralSequenceMap₂ φ ≫ spectralSequenceMap₂ ψ := by
  refine Eq.trans (FilteredComplexSpectralSequence.spectralSequenceMap_congr
    (HomologicalComplex₂.total.map_comp φ ψ (ComplexShape.up ℤ)) _ ?_ _ _)
    (FilteredComplexSpectralSequence.spectralSequenceMap_comp _ _ _ _ _ _ _ _)
  rw [← HomologicalComplex₂.total.map_comp]
  exact exists_stepSubobject₂_le (φ ≫ ψ)

variable (C)
variable [∀ (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)),
  K.HasTotal (ComplexShape.up ℤ)]

/-- **The second spectral sequence of a double complex, as a functor**, with `spectralSequenceMap₂`
as its action on morphisms. Unlike
`Stacks.Cohomology.CechSpectral.totalSpectralSequence₂Functor`, whose filtration steps are the
images of the total projectors, this one presents them as `K.stepSubobject`, which is the
presentation the naturality of the page identifications is stated for. -/
def spectralSequence₂Functor :
    HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⥤
      CohomologicalSpectralSequence C 0 where
  obj K := K.spectralSequence₂
  map φ := spectralSequenceMap₂ φ
  map_id K := spectralSequenceMap₂_id K
  map_comp φ ψ := spectralSequenceMap₂_comp φ ψ

/-- The two presentations of the second spectral sequence of a double complex agree. -/
lemma spectralSequence₂Functor_obj
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)) :
    (spectralSequence₂Functor C).obj K =
      (Stacks.Cohomology.CechSpectral.totalSpectralSequence₂Functor C).obj K :=
  spectralSequence₂_eq K

/-- **The second spectral sequence of a double complex, presented from its second page, as a
functor.** This is the form [Stacks, Tag 01ES] needs: the first page of the second spectral
sequence is not first-quadrant even when the second page is, and homotopy invariance of the
induced maps only holds from the first page on. -/
def e₂SpectralSequence₂Functor :
    HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⥤
      E₂CohomologicalSpectralSequence C :=
  spectralSequence₂Functor C ⋙ Stacks.Cohomology.CechSpectral.restrictR₀ (by omega)

/-- **[Stacks, Tag 0130] (6), naturally.** The identification
`''E_2^{p,q} ≅ H^p_{II}(H^q_I(K^{•,•}))` of the second page of the second spectral sequence of a
double complex is a natural isomorphism of functors of the double complex. -/
def pageTwoNatIso (p q : ℤ) :
    e₂SpectralSequence₂Functor C ⋙ CategoryTheory.SpectralSequence.pageFunctor C _ 2 2 ⋙
        HomologicalComplex.eval C _ (p, q) ≅
      homologyIIHomologyIFunctor C p q :=
  NatIso.ofComponents
    (fun K => isoTwoPageTotalFiltration₂ K _ (pageIso₂ K) (exists_delta₂ K) p q)
    (fun φ => isoTwoPageTotalFiltration₂_naturality_functor φ p q)

/-- **First-quadrant vanishing need only be checked on `H^p_{II}(H^q_I(-))`.** If
`H^p_{II}(H^q_I(K^{•,•}))` vanishes whenever `p < 0` or `q < 0`, then every page of the second
spectral sequence of `K^{•,•}` from the second on vanishes outside the first quadrant, so
`CategoryTheory.SpectralSequence.natRestrictE₂Comp` applies to any functor whose values are such
double complexes. -/
lemma isFirstQuadrant_e₂SpectralSequence₂Functor
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (h : ∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((homologyIIHomologyIFunctor C p q).obj K)) :
    CategoryTheory.SpectralSequence.IsFirstQuadrant (u := fun r => (r, 1 - r))
      ((e₂SpectralSequence₂Functor C).obj K) :=
  CategoryTheory.SpectralSequence.isFirstQuadrant_of_isZero_page _ fun x hx =>
    (Iso.isZero_iff ((pageTwoNatIso C x.1 x.2).app K)).2 (h x.1 x.2 hx)

end Functoriality

section Unsatisfiable

variable [∀ (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)),
  K.HasTotal (ComplexShape.up ℤ)]

/-- **First-quadrant vanishing for *every* double complex is unsatisfiable.** As soon as the
ambient category has a nonzero object `A`, the double complex concentrated in bidegree `(0, -1)`
with value `A` has `H^{-1}_{II}(H^0_I(-)) ≅ A`, hence a nonzero `''E_2^{-1,0}`.

Consequently the hypothesis `hF` of
`Stacks.Cohomology.CechSpectral.totalE₂SpectralSequenceNat₂Functor`, which asks for first-quadrant
vanishing of the second spectral sequence of every double complex over the ambient category, can
never be discharged; the
index conversion `ℤ × ℤ → ℕ × ℕ` for [Stacks, Tag 01ES] must be made through
`CategoryTheory.SpectralSequence.natRestrictE₂Comp`, whose hypothesis ranges only over the objects
of the source category of the functor being restricted. -/
lemma not_forall_isFirstQuadrant (A : C) (hA : ¬ IsZero A) :
    ¬ ∀ K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ),
      CategoryTheory.SpectralSequence.IsFirstQuadrant (u := fun r => (r, 1 - r))
        ((Stacks.Cohomology.CechSpectral.totalE₂SpectralSequence₂Functor C).obj K) := by
  intro h
  refine hA ?_
  let L : CochainComplex C ℤ := (HomologicalComplex.single C (ComplexShape.up ℤ) (-1)).obj A
  let K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
    (HomologicalComplex.single (HomologicalComplex C (ComplexShape.up ℤ))
      (ComplexShape.up ℤ) 0).obj L
  have hKeq : (Stacks.Cohomology.CechSpectral.totalE₂SpectralSequence₂Functor C).obj K =
      (e₂SpectralSequence₂Functor C).obj K :=
    congrArg (Stacks.Cohomology.CechSpectral.restrictR₀ (show (0 : ℤ) ≤ 2 by omega)).obj
      (spectralSequence₂_eq K).symm
  have h2 := hKeq ▸ h K 2 le_rfl (-1, 0) (Or.inl (by omega))
  have e1 : (homologyIIHomologyIFunctor C (-1) 0).obj K ≅ L.homology (-1) :=
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) (-1)).mapIso
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 L)
  exact (Iso.isZero_iff ((pageTwoNatIso C (-1) 0).app K ≪≫ e1 ≪≫
    HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) (-1) A)).1 h2

end Unsatisfiable

section Homotopy

/-- Two morphisms of double complexes are **filtered homotopic** when their total complexes are
homotopic through a homotopy each of whose components carries the step `⨁_{j ≥ p} K^{i,j}` of the
filtration by the second coordinate into the corresponding step for the target. -/
def FilteredHomotopy₂ {K L : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)}
    [K.HasTotal (ComplexShape.up ℤ)] [L.HasTotal (ComplexShape.up ℤ)] (φ ψ : K ⟶ L) : Prop :=
  ∃ h : Homotopy (total.map φ (ComplexShape.up ℤ)) (total.map ψ (ComplexShape.up ℤ)),
    ∀ p i j : ℤ, (Subobject.«exists» (h.hom i j)).obj (K.stepSubobject (fun _ j => j) p i) ≤
      L.stepSubobject (fun _ j => j) p j

/-- **Homotopy invariance for the second spectral sequence of a double complex.** Filtered
homotopic morphisms induce the same map on the pages `E_r` for `r ≥ 1`. -/
@[ega "0 11.2.3" "special case", ega "0 11.3.2" "partial"]
lemma spectralSequenceMap₂_hom_eq_of_filteredHomotopy₂
    {K L : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)}
    [K.HasTotal (ComplexShape.up ℤ)] [L.HasTotal (ComplexShape.up ℤ)] {φ ψ : K ⟶ L}
    (hφψ : FilteredHomotopy₂ φ ψ) {r : ℤ} (hr : 1 ≤ r) :
    (spectralSequenceMap₂ φ).hom r (by omega) = (spectralSequenceMap₂ ψ).hom r (by omega) := by
  obtain ⟨h, hh⟩ := hφψ
  exact FilteredComplexSpectralSequence.spectralSequenceMap_hom_eq_of_homotopy _ _ _ h hh _ hr

variable {D : Type*} [Category D]
  (obj : D → HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
  [∀ X : D, (obj X).HasTotal (ComplexShape.up ℤ)]
  (map : ∀ {X Y : D}, (X ⟶ Y) → (obj X ⟶ obj Y))

/-- **A double complex functorial only up to filtered homotopy still has a functorial `E₂`
spectral sequence.** The data is an assignment `X ↦ K(X)` of a double complex to each object of
`D`, together with a choice of morphism `K(X) ⟶ K(Y)` for each `X ⟶ Y`; the functor laws are
required to hold only up to `FilteredHomotopy₂`. This is how a Čech double complex built from
injective resolutions is functorial, an injective resolution being functorial into the homotopy
category and no further. The target is presented from the second page because homotopy invariance
of the induced maps fails on the zeroth one. -/
def e₂FunctorOfHomotopyClasses
    (hid : ∀ X : D, FilteredHomotopy₂ (map (𝟙 X)) (𝟙 (obj X)))
    (hcomp : ∀ {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z),
      FilteredHomotopy₂ (map (f ≫ g)) (map f ≫ map g)) :
    D ⥤ E₂CohomologicalSpectralSequence C where
  obj X := (Stacks.Cohomology.CechSpectral.restrictR₀ (show (0 : ℤ) ≤ 2 by omega)).obj
    (obj X).spectralSequence₂
  map f := (Stacks.Cohomology.CechSpectral.restrictR₀ (show (0 : ℤ) ≤ 2 by omega)).map
    (spectralSequenceMap₂ (map f))
  map_id X := by
    refine CategoryTheory.SpectralSequence.hom_ext fun r hr => ?_
    refine Eq.trans (spectralSequenceMap₂_hom_eq_of_filteredHomotopy₂ (hid X)
      (show (1 : ℤ) ≤ r by omega)) ?_
    rw [spectralSequenceMap₂_id]
    simp
  map_comp f g := by
    refine CategoryTheory.SpectralSequence.hom_ext fun r hr => ?_
    refine Eq.trans (spectralSequenceMap₂_hom_eq_of_filteredHomotopy₂ (hcomp f g)
      (show (1 : ℤ) ≤ r by omega)) ?_
    rw [spectralSequenceMap₂_comp]
    rfl

variable [∀ (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)),
  K.HasTotal (ComplexShape.up ℤ)]

omit [∀ X : D, (obj X).HasTotal (ComplexShape.up ℤ)] in
/-- The value of `e₂FunctorOfHomotopyClasses` at an object is the second spectral sequence of the
double complex there, so `isFirstQuadrant_e₂SpectralSequence₂Functor` applies to it. -/
lemma e₂FunctorOfHomotopyClasses_obj
    (hid : ∀ X : D, FilteredHomotopy₂ (map (𝟙 X)) (𝟙 (obj X)))
    (hcomp : ∀ {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z),
      FilteredHomotopy₂ (map (f ≫ g)) (map f ≫ map g)) (X : D) :
    (e₂FunctorOfHomotopyClasses obj map hid hcomp).obj X =
      (e₂SpectralSequence₂Functor C).obj (obj X) :=
  rfl

omit [∀ X : D, (obj X).HasTotal (ComplexShape.up ℤ)] in
/-- **The second-page identification is natural for `e₂FunctorOfHomotopyClasses` too.** The
isomorphisms are the same `isoTwoPageTotalFiltration₂` as in `pageTwoNatIso`, and the square they
make commute is the one for the chosen morphism of double complexes; this is the input
`CategoryTheory.NatIso.ofComponents` asks for when the target `H^p_{II}(H^q_I(K(-)))` is known to
be a functor by other means. -/
lemma pageTwoIso_naturality_of_homotopyClasses
    (hid : ∀ X : D, FilteredHomotopy₂ (map (𝟙 X)) (𝟙 (obj X)))
    (hcomp : ∀ {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z),
      FilteredHomotopy₂ (map (f ≫ g)) (map f ≫ map g)) {X Y : D} (f : X ⟶ Y) (p q : ℤ) :
    (((e₂FunctorOfHomotopyClasses obj map hid hcomp).map f).hom 2 le_rfl).f (p, q) ≫
        (isoTwoPageTotalFiltration₂ (obj Y) _ (pageIso₂ (obj Y)) (exists_delta₂ (obj Y))
          p q).hom =
      (isoTwoPageTotalFiltration₂ (obj X) _ (pageIso₂ (obj X)) (exists_delta₂ (obj X)) p q).hom ≫
        (homologyIIHomologyIFunctor C p q).map (map f) :=
  isoTwoPageTotalFiltration₂_naturality_functor (map f) p q

end Homotopy

end HomologicalComplex₂

namespace CategoryTheory.SpectralSequence

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type*} [Category D]

/-- **The second page of a first-quadrant restriction is the second page of the original.** At
`(p, q) : ℕ × ℕ` it is the original second page at `((p : ℤ), (q : ℤ))`, on the nose, because
`HomologicalComplex.natRestrict` is defined by reindexing along `natEmb`. This is the step that
turns a second-page identification carried on `ℤ × ℤ` into one carried on `ℕ × ℕ`. -/
def natRestrictE₂Comp_pageTwoIso (F : D ⥤ E₂CohomologicalSpectralSequence C)
    (hF : ∀ X : D, IsFirstQuadrant (u := fun r => (r, 1 - r)) (F.obj X)) (p q : ℕ) :
    natRestrictE₂Comp F hF ⋙ pageFunctor C _ 2 2 ⋙ HomologicalComplex.eval C _ (p, q) ≅
      F ⋙ pageFunctor C _ 2 2 ⋙ HomologicalComplex.eval C _ ((p : ℤ), (q : ℤ)) :=
  Iso.refl _

end CategoryTheory.SpectralSequence

end
