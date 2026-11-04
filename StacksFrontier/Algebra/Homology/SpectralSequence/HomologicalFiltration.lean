module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.CategoryTheory.Subobject.Lattice
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Basic
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Cycles
public import StacksCore.Tactic.StacksAttribute

@[expose] public section

/-!
# Filtered complexes in homological indexing and their spectral sequences

A cochain complex `X` of modules whose degree `-n` is thought of as chain degree `n`, together
with an increasing filtration of each term by submodules compatible with the differential, has a
spectral sequence in homological indexing. This file sets up that filtration, the data
identifying an abstract spectral sequence with the pages of such a filtration, the convergence
predicate, and the construction of that data from the subobject calculus of a decreasing
filtration by subobjects.

## Main definitions

* `CochainComplex.Tor.HomologicalFiltration` is an increasing degreewise filtration by
  submodules, compatible with the differential, indexed so that `step p n` sits in chain
  degree `n`.
* `CochainComplex.Tor.HomologicalFiltration.pageCycles` and `pageRelations` are the numerator
  and the denominator presenting the `r`-th page.
* `CochainComplex.Tor.TorFiltrationData` identifies the pages and the structure maps of a
  spectral sequence with those filtered-complex representatives.
* `CochainComplex.Tor.TorFiltrationData.Converges` requires the canonical comparison to the
  induced homology filtration to be an isomorphism.
* `CochainComplex.Tor.HomologicalSpectralSequenceAbutsTo` transports this convergence to an
  abstract graded module.
* `CochainComplex.Tor.homologicalFiltrationOfSubobjects` reverses the indices of a decreasing
  degreewise filtration by subobjects.
* `CochainComplex.Tor.homologicalSpectralSequence` is the spectral sequence of such a
  filtration, in homological indexing.

## Main results

* `CochainComplex.Tor.TorFiltrationData.comparison_unique`: the comparison isomorphism in the
  convergence assertion is determined by its effect on classes of actual filtered cycles.
* `CochainComplex.Tor.TorFiltrationData.abutsTo_homology`: a convergent filtered-complex
  spectral sequence abuts to the homology of that very complex.
* `CochainComplex.Tor.TorFiltrationData.converges_of_finite`: a filtration which is finite in
  each degree converges.
* `CochainComplex.Tor.nonempty_torFiltrationData`: the spectral sequence of a decreasing
  filtration by subobjects, read in homological indexing, is presented by that filtration.
* `CochainComplex.Tor.factors_filtration_arrow_comp_d`: each step of a filtration of a cochain
  complex by subcomplexes is carried into the next by the differential.

## Implementation notes

Two shapes of spectral sequence occur, with `r`-th differential of bidegree `(r - 1, -r)` and
`(-r, r - 1)`; a `Bool` selects which of the two coordinates of a double complex is used as the
filtration degree, and `filtrationBidegree` places the pair `(p, n)` of filtration and total
degree in the corresponding bidegree. Pages are presented by surjections from the cycle
representatives whose kernels are exactly the standard page relations, and both the
differentials and the page-turning isomorphisms are required to act on representatives as in the
filtered-complex construction; pagewise abstract isomorphisms do not suffice. Convergence uses
the filtration induced on homology and the unique comparison compatible with cycle classes.

Passing from a decreasing filtration by subobjects to an increasing filtration by submodules
negates both the filtration index and the degree, and turns the cohomological spectral sequence
of the subobject calculus into a homologically indexed one by reindexing along an embedding of
complex shapes.

## References

* [The Stacks Project, Tag 012M](https://stacks.math.columbia.edu/tag/012M)
* [The Stacks Project, Tag 012X](https://stacks.math.columbia.edu/tag/012X)
-/

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.Tor

universe u v w

/-- A spectral sequence whose `r`-th differential has bidegree `(r - 1, -r)`. -/
public abbrev FirstTorSpectralSequence (C : Type v) [Category.{w} C] [Abelian C] :=
  SpectralSequence C (fun r ↦ ComplexShape.up' (⟨r - 1, -r⟩ : ℤ × ℤ)) 2

/-- A spectral sequence whose `r`-th differential has bidegree `(-r, r - 1)`. -/
public abbrev SecondTorSpectralSequence (C : Type v) [Category.{w} C] [Abelian C] :=
  SpectralSequence C (fun r ↦ ComplexShape.up' (⟨-r, r - 1⟩ : ℤ × ℤ)) 1

/-- An increasing filtration by subcomplexes, in homological indexing:
`step p n` is a submodule of the term in chain degree `n`. -/
public structure HomologicalFiltration {R : Type u} [CommRing R]
    (X : CochainComplex (ModuleCat.{v} R) ℤ) where
  /-- The `p`-th step of the filtration of the term in chain degree `n`. -/
  step : ∀ (_p n : ℤ), Submodule R (X.X (-n))
  /-- The filtration is increasing in `p`. -/
  monotone : ∀ n, Monotone (fun p ↦ step p n)
  /-- The differential carries the `p`-th step in degree `n` into the `p`-th step in
  degree `n - 1`. -/
  differential : ∀ p n (x : X.X (-n)), x ∈ step p n →
    X.d (-n) (-(n - 1)) x ∈ step p (n - 1)

namespace HomologicalFiltration

variable {R : Type u} [CommRing R] {X : CochainComplex (ModuleCat.{v} R) ℤ}
    (F : HomologicalFiltration X)

/-- Representatives of the cycles on page `r`. -/
public def pageCycles (r p n : ℤ) : Submodule R (X.X (-n)) :=
  F.step p n ⊓ (F.step (p - r) (n - 1)).comap (X.d (-n) (-(n - 1))).hom

/-- The relations on page `r`: lower-filtration cycles and boundaries of
representatives in filtration `p + r - 1`. -/
public def pageRelations (r p n : ℤ) : Submodule R (X.X (-n)) :=
  F.pageCycles (r - 1) (p - 1) n ⊔
    (F.pageCycles (r - 1) (p + r - 1) (n + 1)).map
      (X.d (-(n + 1)) (-n)).hom

/-- Actual cycles lying in filtration `p`. -/
public noncomputable def filteredCycles (p n : ℤ) : Submodule R (X.cycles (-n)) :=
  (F.step p n).comap (X.iCycles (-n)).hom

/-- The induced filtration on homology, the image of the filtered cycles. -/
public noncomputable def homologyFiltration (p n : ℤ) : Submodule R (X.homology (-n)) :=
  (F.filteredCycles p n).map (X.homologyπ (-n)).hom

/-- The induced homology filtration is increasing. -/
public theorem homologyFiltration_monotone (n : ℤ) :
    Monotone (fun p ↦ F.homologyFiltration p n) := by
  intro p q hpq
  exact Submodule.map_mono (Submodule.comap_mono (F.monotone n hpq))

/-- The associated graded module of the induced homology filtration. -/
public noncomputable abbrev homologyGraded (p n : ℤ) : ModuleCat.{v} R :=
  ModuleCat.of R (F.homologyFiltration p n ⧸
    (F.homologyFiltration (p - 1) n).comap (F.homologyFiltration p n).subtype)

/-- The canonical map from filtered cycles to the associated graded homology. -/
public noncomputable def cycleClass (p n : ℤ) :
    ModuleCat.of R (F.filteredCycles p n) ⟶ F.homologyGraded p n :=
  ModuleCat.ofHom <|
    ((F.homologyFiltration (p - 1) n).comap
      (F.homologyFiltration p n).subtype).mkQ.comp
        (((X.homologyπ (-n)).hom.comp (F.filteredCycles p n).subtype).codRestrict
          (F.homologyFiltration p n) (fun x ↦ ⟨x, x.property, rfl⟩))

/-- Filtered cycles surject onto the associated graded homology. This makes
the comparison equation a characterization, rather than a choice of isomorphism. -/
public instance cycleClass_epi (p n : ℤ) : Epi (F.cycleClass p n) := by
  apply (ModuleCat.epi_iff_surjective _).2
  intro z
  obtain ⟨y, rfl⟩ := ((F.homologyFiltration (p - 1) n).comap
    (F.homologyFiltration p n).subtype).mkQ_surjective z
  obtain ⟨x, hx, hxy⟩ := y.property
  refine ⟨⟨x, hx⟩, ?_⟩
  change (Submodule.mkQ _ ⟨(X.homologyπ (-n)) x, _⟩) = Submodule.mkQ _ y
  congr 1
  exact Subtype.ext hxy

/-- An actual filtered cycle is a representative on every page. -/
public noncomputable def cyclesToPageCycles (r p n : ℤ) :
    ModuleCat.of R (F.filteredCycles p n) ⟶ ModuleCat.of R (F.pageCycles r p n) :=
  ModuleCat.ofHom <|
    (((X.iCycles (-n)).hom.comp (F.filteredCycles p n).subtype).codRestrict
      (F.pageCycles r p n) (fun x ↦ by
        refine ⟨x.property, ?_⟩
        change X.d (-n) (-(n - 1)) (X.iCycles (-n) x.val) ∈ F.step (p - r) (n - 1)
        have h := congrArg (fun f ↦ f.hom x.val) (X.iCycles_d (-n) (-(n - 1)))
        simpa using h ▸ (F.step (p - r) (n - 1)).zero_mem))

end HomologicalFiltration

/-- `false` filters by the resolution degree (the first Tor spectral sequence),
`true` by the degree of `K` (the second). The arguments are filtration and total degree. -/
public def filtrationBidegree (axis : Bool) (p n : ℤ) : ℤ × ℤ :=
  if axis then (p, n - p) else (n - p, p)

/-- Differential shape for the chosen coordinate filtration. -/
public def torSpectralSequenceShape (axis : Bool) (r : ℤ) : ComplexShape (ℤ × ℤ) :=
  if axis then ComplexShape.up' (⟨-r, r - 1⟩ : ℤ × ℤ)
  else ComplexShape.up' (⟨r - 1, -r⟩ : ℤ × ℤ)

/-- Data identifying a spectral sequence with that of a filtered complex.
The surjections have precisely the standard page relations as kernels. Both the
differentials and the homology-to-next-page isomorphisms act on representatives
as in the filtered-complex construction; pagewise abstract isomorphisms do not suffice. -/
public structure TorFiltrationData
    {R : Type u} [CommRing R] {X : CochainComplex (ModuleCat.{v} R) ℤ}
    {c : ℤ → ComplexShape (ℤ × ℤ)} {s : ℤ}
    (E : SpectralSequence (ModuleCat.{v} R) c s)
    (F : HomologicalFiltration X) (axis : Bool) where
  /-- The `r`-th page has the differential shape of the chosen coordinate filtration. -/
  shape : ∀ r, c r = torSpectralSequenceShape axis r
  /-- The map from the page cycles onto the term of the `r`-th page in bidegree `(p, n)`. -/
  projection : ∀ (r : ℤ) (hr : s ≤ r) (p n : ℤ),
    ModuleCat.of R (F.pageCycles r p n) ⟶ (E.page r hr).X (filtrationBidegree axis p n)
  /-- Each projection is surjective. -/
  surjective : ∀ r hr p n, Function.Surjective (projection r hr p n)
  /-- The kernel of each projection is the module of page relations. -/
  kernel : ∀ r hr p n, LinearMap.ker (projection r hr p n).hom =
    (F.pageRelations r p n).comap (F.pageCycles r p n).subtype
  /-- The page differential acts on representatives as the differential of `X`. -/
  differential : ∀ r hr p n (x : X.X (-n)) (hx : x ∈ F.pageCycles r p n)
    (hdx : X.d (-n) (-(n - 1)) x ∈ F.pageCycles r (p - r) (n - 1)),
    (E.page r hr).d (filtrationBidegree axis p n)
        (filtrationBidegree axis (p - r) (n - 1)) (projection r hr p n ⟨x, hx⟩) =
      projection r hr (p - r) (n - 1) ⟨X.d (-n) (-(n - 1)) x, hdx⟩
  /-- A representative lying in the page cycles of the next page projects to a cycle of the page
  differential. -/
  next_cycle : ∀ r hr p n (x : X.X (-n))
    (hx : x ∈ F.pageCycles r p n) (_ : x ∈ F.pageCycles (r + 1) p n),
    (E.page r hr).d (filtrationBidegree axis p n)
      ((c r).next (filtrationBidegree axis p n)) (projection r hr p n ⟨x, hx⟩) = 0
  /-- The identification of the homology of the `r`-th page with the next page sends the class
  of a representative to its projection on the next page. -/
  next_projection : ∀ r hr p n (x : X.X (-n))
    (hx : x ∈ F.pageCycles r p n) (hx' : x ∈ F.pageCycles (r + 1) p n),
    (E.iso r (r + 1) (filtrationBidegree axis p n) rfl hr).hom
      ((E.page r hr).homologyπ (filtrationBidegree axis p n)
        ((E.page r hr).cyclesMk (projection r hr p n ⟨x, hx⟩)
          ((c r).next (filtrationBidegree axis p n)) rfl (next_cycle r hr p n x hx hx'))) =
      projection (r + 1) (by omega) p n ⟨x, hx'⟩

/-- Convergence through the canonical comparison: on actual filtered cycles the
comparison is the usual homology class modulo the preceding filtration step.
Finiteness refers to the induced homology filtration, not a freely chosen one. -/
public def TorFiltrationData.Converges
    {R : Type u} [CommRing R] {X : CochainComplex (ModuleCat.{v} R) ℤ}
    {c : ℤ → ComplexShape (ℤ × ℤ)} {s : ℤ}
    {E : SpectralSequence (ModuleCat.{v} R) c s}
    {F : HomologicalFiltration X} {axis : Bool}
    (S : TorFiltrationData E F axis) : Prop :=
  (∀ n, ∃ a b : ℤ, a ≤ b ∧
    F.homologyFiltration a n = ⊥ ∧ F.homologyFiltration b n = ⊤) ∧
  ∀ p n, ∃ r₀ : ℤ, s ≤ r₀ ∧ ∀ r hr, r₀ ≤ r →
    (E.page r hr).d (filtrationBidegree axis p n)
      ((c r).next (filtrationBidegree axis p n)) = 0 ∧
    (E.page r hr).d ((c r).prev (filtrationBidegree axis p n))
      (filtrationBidegree axis p n) = 0 ∧
    ∃ comparison : (E.page r hr).X (filtrationBidegree axis p n) ⟶ F.homologyGraded p n,
      IsIso comparison ∧
      F.cyclesToPageCycles r p n ≫ S.projection r hr p n ≫ comparison = F.cycleClass p n

/-- The isomorphism in the convergence assertion is uniquely characterized
by its compatibility with the classes of actual filtered cycles. -/
public theorem TorFiltrationData.comparison_unique
    {R : Type u} [CommRing R] {X : CochainComplex (ModuleCat.{v} R) ℤ}
    {c : ℤ → ComplexShape (ℤ × ℤ)} {s : ℤ}
    {E : SpectralSequence (ModuleCat.{v} R) c s}
    {F : HomologicalFiltration X} {axis : Bool}
    (S : TorFiltrationData E F axis) (r : ℤ) (hr : s ≤ r) (p n : ℤ)
    (f g : (E.page r hr).X (filtrationBidegree axis p n) ⟶ F.homologyGraded p n)
    [IsIso f]
    (hf : F.cyclesToPageCycles r p n ≫ S.projection r hr p n ≫ f = F.cycleClass p n)
    (hg : F.cyclesToPageCycles r p n ≫ S.projection r hr p n ≫ g = F.cycleClass p n) :
    f = g := by
  let a := F.cyclesToPageCycles r p n ≫ S.projection r hr p n
  have haf : a ≫ f = F.cycleClass p n := by simpa [a] using hf
  have : Epi (a ≫ f) := by rw [haf]; infer_instance
  have : Epi a := (epi_comp_iff_of_isIso a f).mp inferInstance
  apply (cancel_epi a).1
  simpa [a] using hf.trans hg.symm

/-- Abutment to an abstract graded module, with a filtered-complex model of the
spectral sequence and a specified identification of its homology with that module.
The stable-page comparison in `S.Converges` is pinned by actual cycle classes.
For the tensor-product theorem below the model and its two filtrations are specified
explicitly, rather than existentially hidden in this transport predicate. -/
public def HomologicalSpectralSequenceAbutsTo
    {R : Type u} [CommRing R] {c : ℤ → ComplexShape (ℤ × ℤ)} {s : ℤ}
    (E : SpectralSequence (ModuleCat.{v} R) c s) (H : ℤ → ModuleCat.{v} R) : Prop :=
  ∃ (X : CochainComplex (ModuleCat.{v} R) ℤ) (F : HomologicalFiltration X) (axis : Bool)
    (S : TorFiltrationData E F axis),
    S.Converges ∧ Nonempty (∀ n, X.homology (-n) ≅ H n)

/-- A convergent filtered-complex spectral sequence abuts to the homology
of that very complex, with the identity identification. -/
public theorem TorFiltrationData.abutsTo_homology
    {R : Type u} [CommRing R] {X : CochainComplex (ModuleCat.{v} R) ℤ}
    {c : ℤ → ComplexShape (ℤ × ℤ)} {s : ℤ}
    {E : SpectralSequence (ModuleCat.{v} R) c s}
    {F : HomologicalFiltration X} {axis : Bool}
    (S : TorFiltrationData E F axis) (hS : S.Converges) :
    HomologicalSpectralSequenceAbutsTo E (fun n ↦ X.homology (-n)) :=
  ⟨X, F, axis, S, hS, ⟨fun _ ↦ Iso.refl _⟩⟩

/-- Transport an abutment along an identification of graded modules, retaining
its filtered-complex model and the canonical stable-page comparisons. -/
public theorem HomologicalSpectralSequenceAbutsTo.of_iso
    {R : Type u} [CommRing R] {c : ℤ → ComplexShape (ℤ × ℤ)} {s : ℤ}
    {E : SpectralSequence (ModuleCat.{v} R) c s} {H H' : ℤ → ModuleCat.{v} R}
    (h : HomologicalSpectralSequenceAbutsTo E H) (e : ∀ n, H n ≅ H' n) :
    HomologicalSpectralSequenceAbutsTo E H' := by
  obtain ⟨X, F, axis, S, hS, ⟨eX⟩⟩ := h
  exact ⟨X, F, axis, S, hS, ⟨fun n ↦ eX n ≪≫ e n⟩⟩

/-- The submodule of a monomorphism's subobject is the range of the monomorphism. -/
public theorem subobjectModule_mk
    {R : Type u} [Ring R] {X Y : ModuleCat.{v} R}
    (f : X ⟶ Y) [Mono f] :
    ModuleCat.subobjectModule Y (Subobject.mk f) = LinearMap.range f.hom := by
  show LinearMap.range (Subobject.mk f).arrow.hom = _
  conv_rhs => rw [← Subobject.underlyingIso_arrow f]
  rw [ModuleCat.hom_comp,
    LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr
        ((ModuleCat.epi_iff_surjective (Subobject.underlyingIso f).inv).mp inferInstance))]

/-- The submodule underlying the image subobject of a map of modules is its range. -/
theorem subobjectModule_imageSubobject
    {R : Type u} [Ring R] {X Y : ModuleCat.{v} R} (f : X ⟶ Y) :
    ModuleCat.subobjectModule Y (imageSubobject f) = LinearMap.range f.hom := by
  show LinearMap.range (imageSubobject f).arrow.hom = _
  conv_rhs => rw [← imageSubobject_arrow_comp f]
  rw [ModuleCat.hom_comp,
    LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr
        ((ModuleCat.epi_iff_surjective (factorThruImageSubobject f)).mp inferInstance))]

/-- Reverse the indices of a decreasing degreewise filtration by subobjects: the step at
filtration index `p` and chain degree `n` is the submodule underlying the subobject at
cochain index `-p` and cochain degree `-n`. -/
noncomputable def homologicalFiltrationOfSubobjects
    {R : Type u} [CommRing R] (X : CochainComplex (ModuleCat.{v} R) ℤ)
    (G : ℤ → ∀ n : ℤ, Subobject (X.X n))
    (hanti : ∀ p p' n : ℤ, p ≤ p' → G p' n ≤ G p n)
    (hd : ∀ p n m : ℤ, m = n + 1 → (G p m).Factors ((G p n).arrow ≫ X.d n m)) :
    HomologicalFiltration X where
  step p n := ModuleCat.subobjectModule (X.X (-n)) (G (-p) (-n))
  monotone n p q hpq :=
    (ModuleCat.subobjectModule (X.X (-n))).monotone (hanti (-q) (-p) (-n) (by omega))
  differential p n x hx := by
    change X.d (-n) (-(n - 1)) x ∈ LinearMap.range ((G (-p) (-(n - 1))).arrow).hom
    obtain ⟨y, rfl⟩ := (show x ∈ LinearMap.range ((G (-p) (-n)).arrow).hom from hx)
    refine ⟨Subobject.factorThru _ _ (hd (-p) (-n) (-(n - 1)) (by omega)) y, ?_⟩
    have h := congrArg (fun f ↦ f y)
      (Subobject.factorThru_arrow _ _ (hd (-p) (-n) (-(n - 1)) (by omega)))
    simpa only [ConcreteCategory.comp_apply] using h

/-- The steps of `homologicalFiltrationOfSubobjects` are the submodules underlying the given
subobjects, at negated indices. -/
theorem homologicalFiltrationOfSubobjects_step
    {R : Type u} [CommRing R] (X : CochainComplex (ModuleCat.{v} R) ℤ)
    (G : ℤ → ∀ n : ℤ, Subobject (X.X n))
    (hanti : ∀ p p' n : ℤ, p ≤ p' → G p' n ≤ G p n)
    (hd : ∀ p n m : ℤ, m = n + 1 → (G p m).Factors ((G p n).arrow ≫ X.d n m)) (p n : ℤ) :
    (homologicalFiltrationOfSubobjects X G hanti hd).step p n =
      ModuleCat.subobjectModule (X.X (-n)) (G (-p) (-n)) :=
  rfl
/-- Read a factorisation of a map of modules on elements. -/
theorem hom_apply_eq_of_comp {R : Type u} [Ring R] {A B C' : ModuleCat.{v} R}
    {f : A ⟶ B} {g : B ⟶ C'} {h : A ⟶ C'} (e : f ≫ g = h) (a : A) : g (f a) = h a := by
  rw [← e]; rfl
/-- The degree reversal for the two choices of filtration coordinate. -/
def reverseBidegree (axis : Bool) (pq : ℤ × ℤ) : ℤ × ℤ :=
  if axis then (-pq.1, -pq.2) else (-pq.2, -pq.1)

/-- Degree reversal for the filtration by the first coordinate. -/
theorem reverseBidegree_true (a b : ℤ) : reverseBidegree true (a, b) = (-a, -b) := rfl

/-- Degree reversal for the filtration by the second coordinate. -/
theorem reverseBidegree_false (a b : ℤ) : reverseBidegree false (a, b) = (-b, -a) := rfl

/-- Degree reversal is an involution. -/
theorem reverseBidegree_involutive (axis : Bool) :
    Function.Involutive (reverseBidegree axis) := by
  intro pq
  cases axis <;> simp [reverseBidegree]

/-- Degree reversal applied twice is the identity. -/
theorem reverseBidegree_reverseBidegree (axis : Bool) (pq : ℤ × ℤ) :
    reverseBidegree axis (reverseBidegree axis pq) = pq :=
  reverseBidegree_involutive axis pq

/-- The cohomological bidegree carrying filtration index `p` and total chain degree `n`. -/
theorem reverseBidegree_filtrationBidegree (axis : Bool) (p n : ℤ) :
    reverseBidegree axis (filtrationBidegree axis p n) = (-p, p - n) := by
  cases axis <;> simp [reverseBidegree, filtrationBidegree]

/-- Degree reversal as an embedding of the cohomological differential shape into the
homological one. -/
def torShapeEmbedding (axis : Bool) (r : ℤ) :
    (ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)).Embedding
      (torSpectralSequenceShape axis r) where
  f := reverseBidegree axis
  injective_f := (reverseBidegree_involutive axis).injective
  rel := by
    rintro ⟨p, q⟩ ⟨p', q'⟩ h
    change (p, q) + (r, 1 - r) = (p', q') at h
    have hp := congrArg Prod.fst h
    have hq := congrArg Prod.snd h
    cases axis
    · change (-q, -p) + (r - 1, -r) = (-q', -p')
      apply Prod.ext <;> dsimp at hp hq ⊢ <;> omega
    · change (-p, -q) + (-r, r - 1) = (-p', -q')
      apply Prod.ext <;> dsimp at hp hq ⊢ <;> omega

/-- Reindex a cohomological spectral sequence by homological bidegrees. -/
noncomputable def torIndexedSpectralSequence
    {C : Type v} [Category.{u} C] [Abelian C]
    (E : CohomologicalSpectralSequence C 0) (axis : Bool) (s : ℤ) (hs : 0 ≤ s) :
    SpectralSequence C (torSpectralSequenceShape axis) s where
  page r hr := (E.page r (hs.trans hr)).extend (torShapeEmbedding axis r)
  iso r r' pq h hr := by
    subst r'
    exact (E.page r (hs.trans hr)).extendHomologyIso (torShapeEmbedding axis r)
        (reverseBidegree_reverseBidegree axis pq) ≪≫
      E.iso r (r + 1) (reverseBidegree axis pq) rfl (hs.trans hr) ≪≫
      ((E.page (r + 1) (by omega)).extendXIso (torShapeEmbedding axis (r + 1))
        (reverseBidegree_reverseBidegree axis pq)).symm

/-- The pages of the reindexed spectral sequence are the pages of the original one, at the
reversed bidegree. -/
@[ega "0 11.3.5" "partial"]
noncomputable def torIndexedSpectralSequence_pageIso
    {C : Type v} [Category.{u} C] [Abelian C]
    (E : CohomologicalSpectralSequence C 0) (axis : Bool) (s : ℤ) (hs : 0 ≤ s)
    (r : ℤ) (hr : s ≤ r) (pq : ℤ × ℤ) :
    ((torIndexedSpectralSequence E axis s hs).page r hr).X pq ≅
      (E.page r (hs.trans hr)).X (reverseBidegree axis pq) :=
  (E.page r (hs.trans hr)).extendXIso (torShapeEmbedding axis r)
    (reverseBidegree_reverseBidegree axis pq)

/-- The differential of the reindexed spectral sequence is that of the original one, read
through the page identifications. -/
theorem torIndexedSpectralSequence_d
    {C : Type v} [Category.{u} C] [Abelian C]
    (E : CohomologicalSpectralSequence C 0) (axis : Bool) (s : ℤ) (hs : 0 ≤ s)
    (r : ℤ) (hr : s ≤ r) (pq pq' : ℤ × ℤ) :
    ((torIndexedSpectralSequence E axis s hs).page r hr).d pq pq' =
      (torIndexedSpectralSequence_pageIso E axis s hs r hr pq).hom ≫
        (E.page r (hs.trans hr)).d (reverseBidegree axis pq) (reverseBidegree axis pq') ≫
        (torIndexedSpectralSequence_pageIso E axis s hs r hr pq').inv :=
  (E.page r (hs.trans hr)).extend_d_eq (torShapeEmbedding axis r)
    (reverseBidegree_reverseBidegree axis pq) (reverseBidegree_reverseBidegree axis pq')

/-- The differential of the spectral sequence reindexed along the first coordinate, read
through the page identifications, with the reversed bidegrees written out. -/
theorem torIndexedSpectralSequence_d_true
    {C : Type v} [Category.{u} C] [Abelian C]
    (E : CohomologicalSpectralSequence C 0) (s : ℤ) (hs : 0 ≤ s)
    (r : ℤ) (hr : s ≤ r) (a b a' b' : ℤ) :
    ((torIndexedSpectralSequence E true s hs).page r hr).d (a, b) (a', b') =
      (torIndexedSpectralSequence_pageIso E true s hs r hr (a, b)).hom ≫
        (E.page r (hs.trans hr)).d (-a, -b) (-a', -b') ≫
        (torIndexedSpectralSequence_pageIso E true s hs r hr (a', b')).inv :=
  torIndexedSpectralSequence_d E true s hs r hr (a, b) (a', b')

/-- A morphism presented as a conjugate is recovered by conjugating back. -/
theorem conj_inv_hom {C : Type*} [Category C] {X₁ X₂ Y₁ Y₂ : C}
    (a₁ : X₁ ≅ Y₁) (a₂ : X₂ ≅ Y₂) (d : Y₁ ⟶ Y₂) (e : X₁ ⟶ X₂)
    (he : e = a₁.hom ≫ d ≫ a₂.inv) : a₁.inv ≫ e ≫ a₂.hom = d := by
  subst he
  simp

/-- Conjugating the differential of the spectral sequence reindexed along the first coordinate
by the page identifications recovers the differential of the original one. -/
theorem torIndexedSpectralSequence_d_true_conj
    {C : Type v} [Category.{u} C] [Abelian C]
    (E : CohomologicalSpectralSequence C 0) (s : ℤ) (hs : 0 ≤ s)
    (r : ℤ) (hr : s ≤ r) (a b a' b' : ℤ) :
    (torIndexedSpectralSequence_pageIso E true s hs r hr (a, b)).inv ≫
        ((torIndexedSpectralSequence E true s hs).page r hr).d (a, b) (a', b') ≫
        (torIndexedSpectralSequence_pageIso E true s hs r hr (a', b')).hom =
      (E.page r (hs.trans hr)).d (-a, -b) (-a', -b') :=
  conj_inv_hom _ _ _ _ (torIndexedSpectralSequence_d_true E s hs r hr a b a' b')

/-- The page-turning isomorphism of the reindexed spectral sequence, read through the page
identifications. -/
theorem torIndexedSpectralSequence_iso_hom
    {C : Type v} [Category.{u} C] [Abelian C]
    (E : CohomologicalSpectralSequence C 0) (axis : Bool) (s : ℤ) (hs : 0 ≤ s)
    (r : ℤ) (hr : s ≤ r) (pq : ℤ × ℤ) :
    ((torIndexedSpectralSequence E axis s hs).iso r (r + 1) pq rfl hr).hom =
      ((E.page r (hs.trans hr)).extendHomologyIso (torShapeEmbedding axis r)
        (reverseBidegree_reverseBidegree axis pq)).hom ≫
        (E.iso r (r + 1) (reverseBidegree axis pq) rfl (hs.trans hr)).hom ≫
        (torIndexedSpectralSequence_pageIso E axis s hs (r + 1) (by omega) pq).inv := rfl


private theorem torIndexedSpectralSequence_d_apply {R : Type u} [CommRing R]
    (E : CohomologicalSpectralSequence (ModuleCat.{v} R) 0) (axis : Bool) (s : ℤ) (hs : 0 ≤ s)
    (r : ℤ) (hr : s ≤ r) (pq pq' : ℤ × ℤ)
    (y : ((torIndexedSpectralSequence E axis s hs).page r hr).X pq) :
    (torIndexedSpectralSequence_pageIso E axis s hs r hr pq').hom
        (((torIndexedSpectralSequence E axis s hs).page r hr).d pq pq' y) =
      (E.page r (hs.trans hr)).d (reverseBidegree axis pq) (reverseBidegree axis pq')
        ((torIndexedSpectralSequence_pageIso E axis s hs r hr pq).hom y) := by
  have h : ((torIndexedSpectralSequence E axis s hs).page r hr).d pq pq' ≫
      (torIndexedSpectralSequence_pageIso E axis s hs r hr pq').hom =
      (torIndexedSpectralSequence_pageIso E axis s hs r hr pq).hom ≫
        (E.page r (hs.trans hr)).d (reverseBidegree axis pq) (reverseBidegree axis pq') := by
    rw [torIndexedSpectralSequence_d]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (hom_apply_eq_of_comp h y).trans rfl

private theorem torIndexedSpectralSequence_iso_hom_apply {R : Type u} [CommRing R]
    (E : CohomologicalSpectralSequence (ModuleCat.{v} R) 0) (axis : Bool) (s : ℤ) (hs : 0 ≤ s)
    (r : ℤ) (hr : s ≤ r) (pq : ℤ × ℤ)
    (y : ((torIndexedSpectralSequence E axis s hs).page r hr).homology pq) :
    (torIndexedSpectralSequence_pageIso E axis s hs (r + 1) (by omega) pq).hom
        (((torIndexedSpectralSequence E axis s hs).iso r (r + 1) pq rfl hr).hom y) =
      (E.iso r (r + 1) (reverseBidegree axis pq) rfl (hs.trans hr)).hom
        (((E.page r (hs.trans hr)).extendHomologyIso (torShapeEmbedding axis r)
          (reverseBidegree_reverseBidegree axis pq)).hom y) := by
  have h : ((torIndexedSpectralSequence E axis s hs).iso r (r + 1) pq rfl hr).hom ≫
      (torIndexedSpectralSequence_pageIso E axis s hs (r + 1) (by omega) pq).hom =
      ((E.page r (hs.trans hr)).extendHomologyIso (torShapeEmbedding axis r)
          (reverseBidegree_reverseBidegree axis pq)).hom ≫
        (E.iso r (r + 1) (reverseBidegree axis pq) rfl (hs.trans hr)).hom := by
    have key : ∀ {X Y Z W : ModuleCat.{v} R} (a : X ⟶ Y) (b : Y ⟶ Z) (c : W ≅ Z),
        (a ≫ b ≫ c.inv) ≫ c.hom = a ≫ b := by
      intros; simp
    rw [torIndexedSpectralSequence_iso_hom]
    exact key _ _ _
  exact (hom_apply_eq_of_comp h y).trans rfl

section Convergence

variable {R : Type u} [CommRing R]

private theorem exists_iCycles_eq (X : CochainComplex (ModuleCat.{v} R) ℤ) (m m' : ℤ)
    (hm : m + 1 = m') (x : X.X m) (hx : X.d m m' x = 0) :
    ∃ z : X.cycles m, X.iCycles m z = x := by
  have hex : (ShortComplex.mk (X.iCycles m) (X.d m m') (X.iCycles_d m m')).Exact :=
    ShortComplex.exact_of_f_is_kernel _ (X.cyclesIsKernel m m' (by simp; omega))
  have hx' : x ∈ LinearMap.ker (X.d m m').hom := hx
  rwa [← hex.moduleCat_range_eq_ker] at hx'

private theorem homologyπ_eq_zero_iff (X : CochainComplex (ModuleCat.{v} R) ℤ) (m' m : ℤ)
    (hm : m' + 1 = m) (z : X.cycles m) :
    X.homologyπ m z = 0 ↔ ∃ w : X.X m', X.d m' m w = X.iCycles m z := by
  have hex : (ShortComplex.mk (X.toCycles m' m) (X.homologyπ m)
      (X.toCycles_comp_homologyπ m' m)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (X.homologyIsCokernel m' m (by simp; omega))
  have h := hex.moduleCat_range_eq_ker
  have hinj := (ModuleCat.mono_iff_injective (X.iCycles m)).mp inferInstance
  constructor
  · intro hz
    have hz' : z ∈ LinearMap.ker (X.homologyπ m).hom := hz
    rw [← h] at hz'
    obtain ⟨w, hw⟩ := hz'
    refine ⟨w, ?_⟩
    rw [← hom_apply_eq_of_comp (X.toCycles_i m' m) w]
    exact congrArg _ hw
  · rintro ⟨w, hw⟩
    obtain rfl : z = X.toCycles m' m w :=
      hinj (by rw [hom_apply_eq_of_comp (X.toCycles_i m' m) w, hw])
    show X.toCycles m' m w ∈ LinearMap.ker (X.homologyπ m).hom
    rw [← h]
    exact ⟨w, rfl⟩

variable {X : CochainComplex (ModuleCat.{v} R) ℤ} (F : HomologicalFiltration X)

private theorem step_eq_bot_of_le {a p n : ℤ} (ha : F.step a n = ⊥) (h : p ≤ a) :
    F.step p n = ⊥ :=
  eq_bot_iff.mpr (ha ▸ F.monotone n h)

private theorem step_eq_top_of_le {b p n : ℤ} (hb : F.step b n = ⊤) (h : b ≤ p) :
    F.step p n = ⊤ :=
  eq_top_iff.mpr (hb ▸ F.monotone n h)

private theorem homologyFiltration_eq_bot {a n : ℤ} (ha : F.step a n = ⊥) :
    F.homologyFiltration a n = ⊥ := by
  have hinj := (ModuleCat.mono_iff_injective (X.iCycles (-n))).mp inferInstance
  simp only [HomologicalFiltration.homologyFiltration, HomologicalFiltration.filteredCycles, ha,
    Submodule.comap_bot, LinearMap.ker_eq_bot.mpr hinj, Submodule.map_bot]

private theorem homologyFiltration_eq_top {b n : ℤ} (hb : F.step b n = ⊤) :
    F.homologyFiltration b n = ⊤ := by
  have hsurj := (ModuleCat.epi_iff_surjective (X.homologyπ (-n))).mp inferInstance
  simp only [HomologicalFiltration.homologyFiltration, HomologicalFiltration.filteredCycles, hb,
    Submodule.comap_top, Submodule.map_top, LinearMap.range_eq_top.mpr hsurj]

private theorem cycleClass_eq_zero_iff (p n : ℤ) (z : F.filteredCycles p n) :
    F.cycleClass p n z = 0 ↔ X.homologyπ (-n) z.1 ∈ F.homologyFiltration (p - 1) n := by
  show Submodule.mkQ _ _ = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  rfl


private theorem torSpectralSequenceShape_rel (axis : Bool) (r p n : ℤ) :
    (torSpectralSequenceShape axis r).Rel (filtrationBidegree axis p n)
      (filtrationBidegree axis (p - r) (n - 1)) := by
  cases axis <;>
  · simp only [torSpectralSequenceShape, filtrationBidegree, Bool.false_eq_true, ↓reduceIte]
    show (_ : ℤ × ℤ) + _ = _
    apply Prod.ext <;> dsimp <;> omega

variable {c : ℤ → ComplexShape (ℤ × ℤ)} {s : ℤ} {E : SpectralSequence (ModuleCat.{v} R) c s}
  {axis : Bool}

private theorem TorFiltrationData.next_eq
    (S : TorFiltrationData E F axis) (r p n : ℤ) :
    (c r).next (filtrationBidegree axis p n) = filtrationBidegree axis (p - r) (n - 1) :=
  (c r).next_eq' (by rw [S.shape r]; exact torSpectralSequenceShape_rel axis r p n)

private theorem TorFiltrationData.prev_eq
    (S : TorFiltrationData E F axis) (r p n : ℤ) :
    (c r).prev (filtrationBidegree axis p n) = filtrationBidegree axis (p + r) (n + 1) :=
  (c r).prev_eq' (by
    rw [S.shape r]
    have h := torSpectralSequenceShape_rel axis r (p + r) (n + 1)
    rwa [show p + r - r = p by omega, show n + 1 - 1 = n by omega] at h)

private theorem TorFiltrationData.differential'
    (S : TorFiltrationData E F axis) (r : ℤ) (hr : s ≤ r) (p₀ n₀ p n : ℤ)
    (hp : p = p₀ - r) (hn : n = n₀ - 1) (x : X.X (-n₀)) (hx : x ∈ F.pageCycles r p₀ n₀)
    (hdx : X.d (-n₀) (-n) x ∈ F.pageCycles r p n) :
    (E.page r hr).d (filtrationBidegree axis p₀ n₀) (filtrationBidegree axis p n)
        (S.projection r hr p₀ n₀ ⟨x, hx⟩) =
      S.projection r hr p n ⟨X.d (-n₀) (-n) x, hdx⟩ := by
  subst hp hn
  exact S.differential r hr p₀ n₀ x hx hdx

private theorem TorFiltrationData.projection_eq_zero
    (S : TorFiltrationData E F axis) (r : ℤ) (hr : s ≤ r) (p n : ℤ)
    (x : F.pageCycles r p n) (hx : x.1 ∈ F.pageRelations r p n) :
    S.projection r hr p n x = 0 := by
  have : x ∈ LinearMap.ker (S.projection r hr p n).hom := by
    rw [S.kernel]
    exact hx
  exact this

private theorem pageCycles_eq_of_bot (r p n : ℤ) (h : F.step (p - r) (n - 1) = ⊥)
    (x : X.X (-n)) (hx : x ∈ F.pageCycles r p n) : X.d (-n) (-(n - 1)) x = 0 := by
  have h' : X.d (-n) (-(n - 1)) x ∈ F.step (p - r) (n - 1) := hx.2
  rwa [h] at h'

private theorem finite_step_bounds
    (hfin : ∀ n, ∃ a b : ℤ, a ≤ b ∧ F.step a n = ⊥ ∧ F.step b n = ⊤) (p n : ℤ) (s : ℤ) :
    ∃ r₀ : ℤ, s ≤ r₀ ∧ ∀ r, r₀ ≤ r →
      F.step (p - r) (n - 1) = ⊥ ∧ F.step (p + r - 1) (n + 1) = ⊤ := by
  obtain ⟨a, -, -, ha, -⟩ := hfin (n - 1)
  obtain ⟨-, b, -, -, hb⟩ := hfin (n + 1)
  exact ⟨max s (max (p - a) (b - p + 1)), le_max_left _ _, fun r hr ↦
    ⟨step_eq_bot_of_le F ha (by omega), step_eq_top_of_le F hb (by omega)⟩⟩

private theorem cyclesToPageCycles_bijective (r p n : ℤ) (h : F.step (p - r) (n - 1) = ⊥) :
    Function.Bijective (F.cyclesToPageCycles r p n) := by
  have hinj := (ModuleCat.mono_iff_injective (X.iCycles (-n))).mp inferInstance
  refine ⟨fun z z' hzz ↦ Subtype.ext (hinj (congrArg Subtype.val hzz)), ?_⟩
  rintro ⟨x, hx⟩
  obtain ⟨z, hz⟩ := exists_iCycles_eq X (-n) (-(n - 1)) (by omega) x
    (pageCycles_eq_of_bot F r p n h x hx)
  refine ⟨⟨z, ?_⟩, Subtype.ext hz⟩
  show X.iCycles (-n) z ∈ F.step p n
  rw [hz]
  exact hx.1

private theorem mem_pageRelations_iff_of_large (r p n : ℤ) (hbot : F.step (p - r) (n - 1) = ⊥)
    (htop : F.step (p + r - 1) (n + 1) = ⊤) (z : F.filteredCycles p n) :
    X.iCycles (-n) z.1 ∈ F.pageRelations r p n ↔
      X.homologyπ (-n) z.1 ∈ F.homologyFiltration (p - 1) n := by
  constructor
  · intro hx
    obtain ⟨y, hy, w', hw', hyw⟩ := Submodule.mem_sup.mp hx
    obtain ⟨w, -, rfl⟩ := hw'
    have hdy := pageCycles_eq_of_bot F (r - 1) (p - 1) n
      (by rwa [show p - 1 - (r - 1) = p - r by omega]) y hy
    obtain ⟨yc, hyc⟩ := exists_iCycles_eq X (-n) (-(n - 1)) (by omega) y hdy
    refine ⟨yc, by change X.iCycles (-n) yc ∈ F.step (p - 1) n; rw [hyc]; exact hy.1, ?_⟩
    show X.homologyπ (-n) yc = X.homologyπ (-n) z.1
    rw [← sub_eq_zero, ← map_sub, homologyπ_eq_zero_iff X (-(n + 1)) (-n) (by omega)]
    refine ⟨-w, ?_⟩
    rw [map_sub, hyc, ← hyw, map_neg]
    abel
  · rintro ⟨yc, hyc, hyz⟩
    have hyz' : X.homologyπ (-n) (z.1 - yc) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact hyz.symm
    obtain ⟨w, hw⟩ := (homologyπ_eq_zero_iff X (-(n + 1)) (-n) (by omega) _).mp hyz'
    rw [map_sub] at hw
    apply Submodule.mem_sup.mpr
    refine ⟨X.iCycles (-n) yc, ⟨hyc, ?_⟩, X.d (-(n + 1)) (-n) w,
      ⟨w, ⟨by rw [htop]; trivial, ?_⟩, rfl⟩, ?_⟩
    · show X.d (-n) (-(n - 1)) (X.iCycles (-n) yc) ∈ F.step (p - 1 - (r - 1)) (n - 1)
      rw [hom_apply_eq_of_comp (X.iCycles_d (-n) (-(n - 1)))]
      exact zero_mem _
    · show X.d (-(n + 1)) (-(n + 1 - 1)) w ∈ F.step (p + r - 1 - (r - 1)) (n + 1 - 1)
      rw [show n + 1 - 1 = n by omega, show p + r - 1 - (r - 1) = p by omega, hw]
      exact Submodule.sub_mem _ z.2 (F.monotone n (show p - 1 ≤ p by omega) hyc)
    · rw [hw]
      abel

private theorem exists_comparison
    (S : TorFiltrationData E F axis) (r : ℤ) (hr : s ≤ r) (p n : ℤ)
    (hbot : F.step (p - r) (n - 1) = ⊥) (htop : F.step (p + r - 1) (n + 1) = ⊤) :
    ∃ comparison : (E.page r hr).X (filtrationBidegree axis p n) ⟶ F.homologyGraded p n,
      IsIso comparison ∧
      F.cyclesToPageCycles r p n ≫ S.projection r hr p n ≫ comparison = F.cycleClass p n := by
  let e := LinearEquiv.ofBijective (F.cyclesToPageCycles r p n).hom
    (cyclesToPageCycles_bijective F r p n hbot)
  let f := (F.cycleClass p n).hom ∘ₗ e.symm.toLinearMap
  have hsurjc := (ModuleCat.epi_iff_surjective (F.cycleClass p n)).mp inferInstance
  have hf : Function.Surjective f := hsurjc.comp e.symm.surjective
  have hπ : Function.Surjective (S.projection r hr p n).hom := S.surjective r hr p n
  have hker : LinearMap.ker (S.projection r hr p n).hom = LinearMap.ker f := by
    ext y
    obtain ⟨z, rfl⟩ := e.surjective y
    rw [S.kernel, LinearMap.mem_ker, Submodule.mem_comap]
    show X.iCycles (-n) z.1 ∈ F.pageRelations r p n ↔ F.cycleClass p n (e.symm (e z)) = 0
    rw [LinearEquiv.symm_apply_apply, cycleClass_eq_zero_iff,
      mem_pageRelations_iff_of_large F r p n hbot htop]
  let comp := ((LinearMap.quotKerEquivOfSurjective _ hπ).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans
      (LinearMap.quotKerEquivOfSurjective f hf))).toModuleIso
  refine ⟨comp.hom, inferInstance, ?_⟩
  ext z
  show comp.hom (S.projection r hr p n (e z)) = F.cycleClass p n z
  show (LinearMap.quotKerEquivOfSurjective f hf) ((Submodule.quotEquivOfEq _ _ hker)
    ((LinearMap.quotKerEquivOfSurjective _ hπ).symm (S.projection r hr p n (e z)))) = _
  rw [show (LinearMap.quotKerEquivOfSurjective _ hπ).symm (S.projection r hr p n (e z)) =
      Submodule.Quotient.mk (e z) from
    (LinearEquiv.symm_apply_eq _).mpr (LinearMap.quotKerEquivOfSurjective_apply_mk _ _ _).symm,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]
  show F.cycleClass p n (e.symm (e z)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- A filtration which is finite in every chain degree converges. -/
theorem TorFiltrationData.converges_of_finite
    (S : TorFiltrationData E F axis)
    (hfin : ∀ n, ∃ a b : ℤ, a ≤ b ∧ F.step a n = ⊥ ∧ F.step b n = ⊤) : S.Converges := by
  refine ⟨fun n ↦ ?_, fun p n ↦ ?_⟩
  · obtain ⟨a, b, hab, ha, hb⟩ := hfin n
    exact ⟨a, b, hab, homologyFiltration_eq_bot F ha, homologyFiltration_eq_top F hb⟩
  obtain ⟨r₀, hs, hr₀⟩ := finite_step_bounds F hfin p n s
  refine ⟨r₀, hs, fun r hr hrr ↦ ?_⟩
  obtain ⟨hbot, htop⟩ := hr₀ r hrr
  refine ⟨?_, ?_, ?_⟩
  · rw [TorFiltrationData.next_eq F S r p n]
    ext y
    obtain ⟨⟨x, hx⟩, rfl⟩ := S.surjective r hr p n y
    have hdx0 := pageCycles_eq_of_bot F r p n hbot x hx
    have hdx : X.d (-n) (-(n - 1)) x ∈ F.pageCycles r (p - r) (n - 1) := hdx0 ▸ zero_mem _
    rw [S.differential r hr p n x hx hdx,
      show (⟨_, hdx⟩ : F.pageCycles r (p - r) (n - 1)) = 0 from Subtype.ext hdx0, map_zero]
    rfl
  · rw [TorFiltrationData.prev_eq F S r p n]
    ext y
    obtain ⟨⟨x, hx⟩, rfl⟩ := S.surjective r hr (p + r) (n + 1) y
    have hxs : X.d (-(n + 1)) (-n) x ∈ F.step p n := by
      have := hx.2
      change X.d (-(n + 1)) (-(n + 1 - 1)) x ∈ F.step (p + r - r) (n + 1 - 1) at this
      rwa [show n + 1 - 1 = n by omega, show p + r - r = p by omega] at this
    have hdx : X.d (-(n + 1)) (-n) x ∈ F.pageCycles r p n := by
      refine ⟨hxs, ?_⟩
      · show X.d (-n) (-(n - 1)) (X.d (-(n + 1)) (-n) x) ∈ F.step (p - r) (n - 1)
        rw [← ConcreteCategory.comp_apply, HomologicalComplex.d_comp_d]
        exact zero_mem _
    rw [TorFiltrationData.differential' F S r hr (p + r) (n + 1) p n (by omega) (by omega) x hx hdx,
      TorFiltrationData.projection_eq_zero F S r hr p n _ ?_]
    · rfl
    apply Submodule.mem_sup_right
    refine ⟨x, ⟨by rw [htop]; trivial, ?_⟩, rfl⟩
    show X.d (-(n + 1)) (-(n + 1 - 1)) x ∈ F.step (p + r - 1 - (r - 1)) (n + 1 - 1)
    rwa [show n + 1 - 1 = n by omega, show p + r - 1 - (r - 1) = p by omega]
  · exact exists_comparison F S r hr p n hbot htop
end Convergence

section Model

open FilteredComplexSpectralSequence

variable {R : Type u} [CommRing R]

/-- The submodule of the image of a subobject along `f` is the image under `f` of its
submodule. -/
public theorem subobjectModule_exists
    {M N : ModuleCat.{v} R} (f : M ⟶ N) (A : Subobject M) :
    ModuleCat.subobjectModule N ((Subobject.«exists» f).obj A) =
      (ModuleCat.subobjectModule M A).map f.hom := by
  have hA : (Subobject.«exists» f).obj A = imageSubobject (A.arrow ≫ f) :=
    le_antisymm
      (Subobject.exists_le_of_comm f (factorThruImageSubobject (A.arrow ≫ f))
        (imageSubobject_arrow_comp _))
      (imageSubobject_le _ (Subobject.imageFactorisation f A).F.e
        (Subobject.imageFactorisation f A).F.fac)
  rw [hA, subobjectModule_imageSubobject]
  show LinearMap.range (A.arrow ≫ f).hom =
    Submodule.map f.hom (LinearMap.range A.arrow.hom)
  rw [ModuleCat.hom_comp, LinearMap.range_comp]

/-- The submodule of the pullback of a subobject along `f` is the preimage under `f` of its
submodule. -/
public theorem subobjectModule_pullback
    {M N : ModuleCat.{v} R} (f : M ⟶ N) (A : Subobject N) :
    ModuleCat.subobjectModule M ((Subobject.pullback f).obj A) =
      (ModuleCat.subobjectModule N A).comap f.hom := by
  apply le_antisymm
  · rw [← Submodule.map_le_iff_le_comap, ← subobjectModule_exists]
    exact (ModuleCat.subobjectModule N).monotone
      ((Subobject.exists_le_iff_le_pullback _ _ _).2 le_rfl)
  · rw [← (ModuleCat.subobjectModule M).apply_symm_apply
      ((ModuleCat.subobjectModule N A).comap f.hom)]
    apply (ModuleCat.subobjectModule M).monotone
    rw [← Subobject.exists_le_iff_le_pullback]
    apply (ModuleCat.subobjectModule N).le_iff_le.mp
    rw [subobjectModule_exists, OrderIso.apply_symm_apply]
    exact Submodule.map_comap_le f.hom _

private noncomputable def subobjectIso {M : ModuleCat.{v} R} (P : Subobject M) :
    ModuleCat.of R (ModuleCat.subobjectModule M P) ≅ (P : ModuleCat.{v} R) :=
  (LinearEquiv.ofInjective P.arrow.hom
    ((ModuleCat.mono_iff_injective P.arrow).mp inferInstance)).toModuleIso.symm

private theorem subobjectIso_hom_arrow {M : ModuleCat.{v} R} (P : Subobject M)
    (x : ModuleCat.subobjectModule M P) :
    P.arrow ((subobjectIso P).hom x) = x.1 := by
  show P.arrow.hom ((LinearEquiv.ofInjective P.arrow.hom _).symm x) = x.1
  exact LinearEquiv.ofInjective_symm_apply _ x

private theorem ker_cokernel_π {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    LinearMap.ker (cokernel.π f).hom = LinearMap.range f.hom :=
  ((ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp (ShortComplex.exact_cokernel f)).symm

variable (X : CochainComplex (ModuleCat.{v} R) ℤ) (G : ℤ → ∀ n : ℤ, Subobject (X.X n))

private noncomputable abbrev cycSub (r a m : ℤ) : Submodule R (X.X m) :=
  ModuleCat.subobjectModule _ (cycles X G r a m)

private noncomputable abbrev bdySub (r a m : ℤ) : Submodule R (X.X m) :=
  ModuleCat.subobjectModule _ (boundaries X G r a m)

private theorem cycSub_eq (r a m : ℤ) :
    cycSub X G r a m = ModuleCat.subobjectModule _ (G a m) ⊓
      (ModuleCat.subobjectModule _ (G (a + r) (m + 1))).comap (X.d m (m + 1)).hom := by
  rw [cycSub, cycles, OrderIso.map_inf, subobjectModule_pullback]

private theorem bdySub_eq (r a m : ℤ) :
    bdySub X G r a m = cycSub X G (r - 1) (a + 1) m ⊔
      (cycSub X G (r - 1) (a - r + 1) (m - 1)).map (X.d (m - 1) m).hom := by
  rw [bdySub, boundaries, OrderIso.map_sup, subobjectModule_exists]

variable (hanti : ∀ p p' n : ℤ, p ≤ p' → G p' n ≤ G p n)

section Reversed

variable (hd : ∀ p n m : ℤ, m = n + 1 → (G p m).Factors ((G p n).arrow ≫ X.d n m))

private theorem modelFiltration_pageCycles (r p n a : ℤ) (ha : -p = a) :
    (homologicalFiltrationOfSubobjects X G hanti hd).pageCycles r p n = cycSub X G r a (-n) := by
  subst ha
  rw [cycSub_eq]
  simp only [HomologicalFiltration.pageCycles, homologicalFiltrationOfSubobjects]
  rw [show -(p - r) = -p + r by omega, show -(n - 1) = -n + 1 by omega]

private theorem modelFiltration_pageRelations (r p n a : ℤ) (ha : -p = a) :
    (homologicalFiltrationOfSubobjects X G hanti hd).pageRelations r p n =
      bdySub X G r a (-n) := by
  subst ha
  rw [bdySub_eq]
  simp only [HomologicalFiltration.pageRelations]
  rw [modelFiltration_pageCycles X G hanti hd (r - 1) (p - 1) n (-p + 1) (by omega),
    modelFiltration_pageCycles X G hanti hd (r - 1) (p + r - 1) (n + 1) (-p - r + 1) (by omega),
    show -(n + 1) = -n - 1 by omega]

end Reversed

private noncomputable def pageClass (r : ℤ) (hr : 0 ≤ r) (pq : ℤ × ℤ) (n : ℤ)
    (hn : n = pq.1 + pq.2) :
    ModuleCat.of R (cycSub X G r pq.1 n) ⟶
      ((spectralSequence X G hanti).page r hr).X pq :=
  (subobjectIso _).hom ≫ cokernel.π (den X G r pq.1 n) ≫
    (eIso X G hanti r pq.1 pq.2 n hr hn).inv

private theorem pageClass_eq (r : ℤ) (hr : 0 ≤ r) (p q : ℤ) :
    pageClass X G hanti r hr (p, q) (p + q) rfl =
      (subobjectIso _).hom ≫ cokernel.π (den X G r p (p + q)) := by
  rw [pageClass, eIso_inv_rfl, Category.comp_id]

private theorem pageClass_surjective (r : ℤ) (hr : 0 ≤ r) (pq : ℤ × ℤ) (n : ℤ)
    (hn : n = pq.1 + pq.2) : Function.Surjective (pageClass X G hanti r hr pq n hn) := by
  rw [pageClass]
  exact (ModuleCat.epi_iff_surjective _).mp inferInstance

private theorem pageClass_ker (r : ℤ) (hr : 0 ≤ r) (pq : ℤ × ℤ) (n : ℤ)
    (hn : n = pq.1 + pq.2) :
    LinearMap.ker (pageClass X G hanti r hr pq n hn).hom =
      (bdySub X G r pq.1 n).comap (cycSub X G r pq.1 n).subtype := by
  have hiso := (ModuleCat.mono_iff_injective
    (eIso X G hanti r pq.1 pq.2 n hr hn).inv).mp inferInstance
  ext x
  have hmem : x ∈ LinearMap.ker (pageClass X G hanti r hr pq n hn).hom ↔
      (subobjectIso _).hom x ∈ LinearMap.ker (cokernel.π (den X G r pq.1 n)).hom := by
    constructor
    · intro hx
      have hx' : (eIso X G hanti r pq.1 pq.2 n hr hn).inv
          (cokernel.π (den X G r pq.1 n) ((subobjectIso _).hom x)) = 0 := hx
      exact hiso (hx'.trans (map_zero _).symm)
    · intro hx
      have hx' : cokernel.π (den X G r pq.1 n) ((subobjectIso _).hom x) = 0 := hx
      show (eIso X G hanti r pq.1 pq.2 n hr hn).inv
        (cokernel.π (den X G r pq.1 n) ((subobjectIso _).hom x)) = 0
      rw [hx', map_zero]
  rw [hmem, ker_cokernel_π, Submodule.mem_comap]
  show _ ↔ x.1 ∈ bdySub X G r pq.1 n
  have hZinj := (ModuleCat.mono_iff_injective (cycles X G r pq.1 n).arrow).mp inferInstance
  constructor
  · rintro ⟨y, hy⟩
    have hval : (boundaries X G r pq.1 n ⊓ cycles X G r pq.1 n).arrow y = x.1 := by
      rw [← subobjectIso_hom_arrow (cycles X G r pq.1 n) x, ← hy,
        ← ConcreteCategory.comp_apply, Subobject.ofLE_arrow]
    rw [← hval]
    exact (ModuleCat.subobjectModule (X.X n)).monotone
      (inf_le_left : boundaries X G r pq.1 n ⊓ cycles X G r pq.1 n ≤ _) ⟨y, rfl⟩
  · intro hx
    have hmem2 : x.1 ∈ ModuleCat.subobjectModule (X.X n)
        (boundaries X G r pq.1 n ⊓ cycles X G r pq.1 n) := by
      rw [OrderIso.map_inf]
      exact ⟨hx, x.2⟩
    obtain ⟨y, hy⟩ := hmem2
    refine ⟨y, hZinj ?_⟩
    show (cycles X G r pq.1 n).arrow ((den X G r pq.1 n) y) = _
    rw [← ConcreteCategory.comp_apply, Subobject.ofLE_arrow, subobjectIso_hom_arrow]
    exact hy

/-- The differential of the spectral sequence of a filtered complex, read through the page
identifications, is induced on representatives by the differential of the complex. -/
theorem den_π_eIso_inv_comp_d (r : ℤ) (hr : 0 ≤ r) (p q n : ℤ) (hn : n = p + q) :
    cokernel.π (den X G r p n) ≫ (eIso X G hanti r p q n hr hn).inv ≫
        ((spectralSequence X G hanti).page r hr).d (p, q) (p + r, q - r + 1) =
      deltaCycles X G r p n ≫ cokernel.π (den X G r (p + r) (n + 1)) ≫
        (eIso X G hanti r (p + r) (q - r + 1) (n + 1) hr (by omega)).inv := by
  subst hn
  rw [spectralSequence_d, eIso_inv_rfl, Category.id_comp, ← Category.assoc, π_comp_pageMap,
    Category.assoc]

private theorem pageClass_d (r : ℤ) (hr : 0 ≤ r) (p q n : ℤ) (hn : n = p + q)
    (x : cycSub X G r p n) (hdx : X.d n (n + 1) x.1 ∈ cycSub X G r (p + r) (n + 1)) :
    ((spectralSequence X G hanti).page r hr).d (p, q) (p + r, q - r + 1)
        (pageClass X G hanti r hr (p, q) n hn x) =
      pageClass X G hanti r hr (p + r, q - r + 1) (n + 1) (by omega) ⟨_, hdx⟩ := by
  have hstep : deltaCycles X G r p n ((subobjectIso (cycles X G r p n)).hom x) =
      (subobjectIso (cycles X G r (p + r) (n + 1))).hom ⟨_, hdx⟩ := by
    apply (ModuleCat.mono_iff_injective (cycles X G r (p + r) (n + 1)).arrow).mp inferInstance
    rw [hom_apply_eq_of_comp (deltaCycles_arrow X G r p n), ConcreteCategory.comp_apply,
      subobjectIso_hom_arrow, subobjectIso_hom_arrow]
  have key := congrArg (fun f : ModuleCat.of R (cycSub X G r p n) ⟶
        ((spectralSequence X G hanti).page r hr).X (p + r, q - r + 1) ↦ f x)
    (congrArg ((subobjectIso (cycles X G r p n)).hom ≫ ·)
      (den_π_eIso_inv_comp_d X G hanti r hr p q n hn))
  simp only [pageClass, ConcreteCategory.comp_apply] at key ⊢
  rw [key, hstep]

private theorem cycles_succ_comp_pageMap (r p n : ℤ) :
    (Subobject.ofLE _ _ (cycles_succ_le X G hanti r p n) ≫ cokernel.π (den X G r p n)) ≫
      pageMap X G r p n = 0 := by
  have key : Subobject.ofLE _ _ (cycles_succ_le X G hanti r p n) ≫
      cokernel.π (den X G r p n) =
      (Subobject.ofLE _ _ (cyclesSucc_le_kernelNumerator X G hanti r p n) ≫
          cokernel.π (Subobject.ofLE _ _ (den_le_kernelNumerator X G hanti r p n))) ≫
        pageCyclesι X G hanti r p n := by
    rw [Category.assoc, π_comp_pageCyclesι, ← Category.assoc, Subobject.ofLE_comp_ofLE]
  rw [key, Category.assoc, pageCyclesι_comp_pageMap, comp_zero]

private theorem pageShape_rel (r p q : ℤ) :
    (p, q) + (r, 1 - r) = ((p + r, q - r + 1) : ℤ × ℤ) :=
  Prod.ext rfl (by simp only [Prod.snd_add]; ring)

private theorem cycles_succ_comp_pageComplex_d (r p q : ℤ) :
    (Subobject.ofLE _ _ (cycles_succ_le X G hanti r p (p + q)) ≫
        cokernel.π (den X G r p (p + q))) ≫
      (pageComplex X G r).d (p, q) (p + r, q - r + 1) = 0 := by
  rw [pageComplex_d X G r (pq := (p, q)) (pq' := (p + r, q - r + 1)) (pageShape_rel r p q),
    pageMap']
  simp only [← Category.assoc]
  rw [cycles_succ_comp_pageMap X G hanti, zero_comp]

private noncomputable def pageTurnLift (r p q : ℤ) :
    (cycles X G (r + 1) p (p + q) : ModuleCat.{v} R) ⟶ (pageComplex X G r).cycles (p, q) :=
  (pageComplex X G r).liftCycles
    (Subobject.ofLE _ _ (cycles_succ_le X G hanti r p (p + q)) ≫
      cokernel.π (den X G r p (p + q)))
    (p + r, q - r + 1)
    (ComplexShape.next_eq' _ (by rw [ComplexShape.up'_Rel]; exact pageShape_rel r p q))
    (cycles_succ_comp_pageComplex_d X G hanti r p q)

private theorem pageTurnLift_iCycles (r p q : ℤ) :
    pageTurnLift X G hanti r p q ≫ (pageComplex X G r).iCycles (p, q) =
      Subobject.ofLE _ _ (cycles_succ_le X G hanti r p (p + q)) ≫
        cokernel.π (den X G r p (p + q)) :=
  HomologicalComplex.liftCycles_i ..

private theorem pageTurnLift_homologyπ (r p q : ℤ) :
    pageTurnLift X G hanti r p q ≫ (pageComplex X G r).homologyπ (p, q) ≫
        (pageHomologyIso X G hanti r (p, q)).hom =
      cokernel.π (den X G (r + 1) p (p + q)) := by
  simpa only [Category.id_comp] using
    homologyπ_comp_pageHomologyIso_hom X G hanti r (p, q) (pageTurnLift X G hanti r p q) (𝟙 _)
      (Subobject.ofLE _ _ (cycles_succ_le X G hanti r p (p + q)))
      (by rw [Subobject.ofLE_arrow, Category.id_comp])
      (pageTurnLift_iCycles X G hanti r p q)

private theorem spectralSequence_iso_hom (r : ℤ) (hr : 0 ≤ r) (pq : ℤ × ℤ) :
    ((spectralSequence X G hanti).iso r (r + 1) pq rfl hr).hom =
      (pageHomologyIso X G hanti r pq).hom := rfl

private theorem pageClass_next (r : ℤ) (hr : 0 ≤ r) (p q : ℤ)
    (x : cycSub X G r p (p + q)) (hx : x.1 ∈ cycSub X G (r + 1) p (p + q))
    (z : ((spectralSequence X G hanti).page r hr).cycles (p, q))
    (hz : ((spectralSequence X G hanti).page r hr).iCycles (p, q) z =
      pageClass X G hanti r hr (p, q) (p + q) rfl x) :
    ((spectralSequence X G hanti).iso r (r + 1) (p, q) rfl hr).hom
        (((spectralSequence X G hanti).page r hr).homologyπ (p, q) z) =
      pageClass X G hanti (r + 1) (by omega) (p, q) (p + q) rfl ⟨x.1, hx⟩ := by
  set x' : (cycles X G (r + 1) p (p + q) : ModuleCat.{v} R) :=
    (subobjectIso (cycles X G (r + 1) p (p + q))).hom ⟨x.1, hx⟩ with hx'def
  have harrow : (Subobject.ofLE _ _ (cycles_succ_le X G hanti r p (p + q))) x' =
      (subobjectIso (cycles X G r p (p + q))).hom x := by
    apply (ModuleCat.mono_iff_injective (cycles X G r p (p + q)).arrow).mp inferInstance
    rw [hom_apply_eq_of_comp
      (Subobject.ofLE_arrow (cycles_succ_le X G hanti r p (p + q))), hx'def,
      subobjectIso_hom_arrow, subobjectIso_hom_arrow]
  have hzeq : z = pageTurnLift X G hanti r p q x' := by
    apply (ModuleCat.mono_iff_injective
      ((pageComplex X G r).iCycles (p, q))).mp inferInstance
    rw [hom_apply_eq_of_comp (pageTurnLift_iCycles X G hanti r p q)]
    rw [show ((pageComplex X G r).iCycles (p, q)) z =
      ((spectralSequence X G hanti).page r hr).iCycles (p, q) z from rfl, hz, pageClass_eq]
    simp only [ConcreteCategory.comp_apply]
    rw [harrow]
  rw [hzeq, spectralSequence_iso_hom, pageClass_eq]
  have key := hom_apply_eq_of_comp (pageTurnLift_homologyπ X G hanti r p q) x'
  simp only [ConcreteCategory.comp_apply] at key ⊢
  exact key

private theorem pageClass_d' (r : ℤ) (hr : 0 ≤ r) (pq pq' : ℤ × ℤ) (m m' : ℤ)
    (hm : m = pq.1 + pq.2) (hm' : m' = pq'.1 + pq'.2)
    (h1 : pq.1 + r = pq'.1) (h2 : pq.2 - r + 1 = pq'.2)
    (x : cycSub X G r pq.1 m) (hdx : X.d m m' x.1 ∈ cycSub X G r pq'.1 m') :
    ((spectralSequence X G hanti).page r hr).d pq pq'
        (pageClass X G hanti r hr pq m hm x) =
      pageClass X G hanti r hr pq' m' hm' ⟨_, hdx⟩ := by
  obtain ⟨a, b⟩ := pq
  obtain ⟨a', b'⟩ := pq'
  dsimp only at h1 h2 hm hm' x hdx ⊢
  subst h1 h2 hm
  obtain rfl : m' = a + b + 1 := by omega
  exact pageClass_d X G hanti r hr a b (a + b) rfl x hdx

private theorem pageClass_next' (r : ℤ) (hr : 0 ≤ r) (pq : ℤ × ℤ) (m : ℤ)
    (hm : m = pq.1 + pq.2) (x : cycSub X G r pq.1 m) (hx : x.1 ∈ cycSub X G (r + 1) pq.1 m)
    (z : ((spectralSequence X G hanti).page r hr).cycles pq)
    (hz : ((spectralSequence X G hanti).page r hr).iCycles pq z =
      pageClass X G hanti r hr pq m hm x) :
    ((spectralSequence X G hanti).iso r (r + 1) pq rfl hr).hom
        (((spectralSequence X G hanti).page r hr).homologyπ pq z) =
      pageClass X G hanti (r + 1) (by omega) pq m hm ⟨x.1, hx⟩ := by
  obtain ⟨a, b⟩ := pq
  dsimp only at hm x hx z hz ⊢
  subst hm
  exact pageClass_next X G hanti r hr a b x hx z hz

/-- The spectral sequence of a decreasing degreewise filtration by subobjects, read in
homological indexing: the cohomological spectral sequence of the filtration, reindexed along the
chosen coordinate. -/
noncomputable abbrev homologicalSpectralSequence (axis : Bool) (s : ℤ) (hs : 0 ≤ s) :
    SpectralSequence (ModuleCat.{v} R) (torSpectralSequenceShape axis) s :=
  torIndexedSpectralSequence (spectralSequence X G hanti) axis s hs

variable (hd : ∀ p n m : ℤ, m = n + 1 → (G p m).Factors ((G p n).arrow ≫ X.d n m))

private theorem reverseBidegree_filtrationBidegree_fst (axis : Bool) (p n : ℤ) :
    -p = (reverseBidegree axis (filtrationBidegree axis p n)).1 := by
  rw [reverseBidegree_filtrationBidegree]

/-- The page cycles of the model filtration are the cycles of the reversed bidegree. -/
private theorem modelFiltration_pageCycles_rev (axis : Bool) (r p n : ℤ) :
    (homologicalFiltrationOfSubobjects X G hanti hd).pageCycles r p n =
      cycSub X G r (reverseBidegree axis (filtrationBidegree axis p n)).1 (-n) :=
  modelFiltration_pageCycles X G hanti hd r p n _
    (reverseBidegree_filtrationBidegree_fst axis p n)

private theorem reverseBidegree_filtrationBidegree_sum (axis : Bool) (p n : ℤ) :
    -n = (reverseBidegree axis (filtrationBidegree axis p n)).1 +
      (reverseBidegree axis (filtrationBidegree axis p n)).2 := by
  rw [reverseBidegree_filtrationBidegree]; ring

private noncomputable def modelProjection (axis : Bool) (s : ℤ) (hs : 0 ≤ s) (r : ℤ)
    (hr : s ≤ r) (p n : ℤ) :
    ModuleCat.of R ((homologicalFiltrationOfSubobjects X G hanti hd).pageCycles r p n) ⟶
      ((homologicalSpectralSequence X G hanti axis s hs).page r hr).X
        (filtrationBidegree axis p n) :=
  ModuleCat.ofHom (LinearEquiv.ofEq _ _
      (modelFiltration_pageCycles_rev X G hanti hd axis r p n)).toLinearMap ≫
    pageClass X G hanti r (hs.trans hr)
      (reverseBidegree axis (filtrationBidegree axis p n)) (-n)
      (reverseBidegree_filtrationBidegree_sum axis p n) ≫
    (torIndexedSpectralSequence_pageIso (spectralSequence X G hanti) axis s hs r hr
      (filtrationBidegree axis p n)).inv

private theorem modelProjection_apply (axis : Bool) (s : ℤ) (hs : 0 ≤ s) (r : ℤ)
    (hr : s ≤ r) (p n : ℤ)
    (x : (homologicalFiltrationOfSubobjects X G hanti hd).pageCycles r p n) :
    (torIndexedSpectralSequence_pageIso (spectralSequence X G hanti) axis s hs r hr
        (filtrationBidegree axis p n)).hom
        (modelProjection X G hanti hd axis s hs r hr p n x) =
      pageClass X G hanti r (hs.trans hr)
        (reverseBidegree axis (filtrationBidegree axis p n)) (-n)
        (reverseBidegree_filtrationBidegree_sum axis p n)
        ⟨x.1, (modelFiltration_pageCycles_rev X G hanti hd axis r p n).le x.2⟩ := by
  show (torIndexedSpectralSequence_pageIso (spectralSequence X G hanti) axis s hs r hr
    (filtrationBidegree axis p n)).hom
      ((torIndexedSpectralSequence_pageIso (spectralSequence X G hanti) axis s hs r hr
        (filtrationBidegree axis p n)).inv _) = _
  rw [Iso.inv_hom_id_apply]
  rfl

private theorem modelProjection_surjective (axis : Bool) (s : ℤ) (hs : 0 ≤ s) (r : ℤ)
    (hr : s ≤ r) (p n : ℤ) :
    Function.Surjective (modelProjection X G hanti hd axis s hs r hr p n) := by
  have h1 := (LinearEquiv.ofEq _ _
    (modelFiltration_pageCycles_rev X G hanti hd axis r p n)).surjective
  have h2 := pageClass_surjective X G hanti r (hs.trans hr)
    (reverseBidegree axis (filtrationBidegree axis p n)) (-n)
    (reverseBidegree_filtrationBidegree_sum axis p n)
  have h3 := (ConcreteCategory.bijective_of_isIso
    (torIndexedSpectralSequence_pageIso (spectralSequence X G hanti) axis s hs r hr
      (filtrationBidegree axis p n)).inv).2
  exact h3.comp (h2.comp h1)

private theorem modelProjection_kernel (axis : Bool) (s : ℤ) (hs : 0 ≤ s) (r : ℤ)
    (hr : s ≤ r) (p n : ℤ) :
    LinearMap.ker (modelProjection X G hanti hd axis s hs r hr p n).hom =
      ((homologicalFiltrationOfSubobjects X G hanti hd).pageRelations r p n).comap
        ((homologicalFiltrationOfSubobjects X G hanti hd).pageCycles r p n).subtype := by
  ext x
  rw [LinearMap.mem_ker, Submodule.mem_comap,
    modelFiltration_pageRelations X G hanti hd r p n _
      (reverseBidegree_filtrationBidegree_fst axis p n)]
  have hinj := (ConcreteCategory.bijective_of_isIso
    (torIndexedSpectralSequence_pageIso (spectralSequence X G hanti) axis s hs r hr
      (filtrationBidegree axis p n)).hom).1
  rw [← hinj.eq_iff, map_zero, modelProjection_apply, ← LinearMap.mem_ker, pageClass_ker]
  exact Iff.rfl

private theorem modelProjection_differential (axis : Bool) (s : ℤ) (hs : 0 ≤ s) (r : ℤ)
    (hr : s ≤ r) (p n : ℤ) (x : X.X (-n))
    (hx : x ∈ (homologicalFiltrationOfSubobjects X G hanti hd).pageCycles r p n)
    (hdx : X.d (-n) (-(n - 1)) x ∈
      (homologicalFiltrationOfSubobjects X G hanti hd).pageCycles r (p - r) (n - 1)) :
    ((homologicalSpectralSequence X G hanti axis s hs).page r hr).d
        (filtrationBidegree axis p n) (filtrationBidegree axis (p - r) (n - 1))
        (modelProjection X G hanti hd axis s hs r hr p n ⟨x, hx⟩) =
      modelProjection X G hanti hd axis s hs r hr (p - r) (n - 1) ⟨_, hdx⟩ := by
  have hinj := (ConcreteCategory.bijective_of_isIso
    (torIndexedSpectralSequence_pageIso (spectralSequence X G hanti) axis s hs r hr
      (filtrationBidegree axis (p - r) (n - 1))).hom).1
  apply hinj
  rw [modelProjection_apply, torIndexedSpectralSequence_d_apply, modelProjection_apply]
  apply pageClass_d'
  · rw [reverseBidegree_filtrationBidegree, reverseBidegree_filtrationBidegree]
    dsimp only
    ring
  · rw [reverseBidegree_filtrationBidegree, reverseBidegree_filtrationBidegree]
    dsimp only
    ring

private theorem pageCycles_succ_d_mem {Y : CochainComplex (ModuleCat.{v} R) ℤ}
    (F : HomologicalFiltration Y) (r p n : ℤ) (x : Y.X (-n))
    (hx : x ∈ F.pageCycles (r + 1) p n) :
    Y.d (-n) (-(n - 1)) x ∈ F.pageCycles r (p - r) (n - 1) ∧
      Y.d (-n) (-(n - 1)) x ∈ F.pageRelations r (p - r) (n - 1) := by
  have hdd : Y.d (-(n - 1)) (-(n - 1 - 1)) (Y.d (-n) (-(n - 1)) x) = 0 := by
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.d_comp_d]; rfl
  have h2 := hx.2
  change Y.d (-n) (-(n - 1)) x ∈ F.step (p - (r + 1)) (n - 1) at h2
  refine ⟨⟨F.monotone (n - 1) (by omega) h2, ?_⟩, Submodule.mem_sup_left ⟨?_, ?_⟩⟩
  · show _ ∈ F.step (p - r - r) (n - 1 - 1); rw [hdd]; exact zero_mem _
  · show _ ∈ F.step (p - r - 1) (n - 1); rwa [show p - r - 1 = p - (r + 1) by omega]
  · show _ ∈ F.step (p - r - 1 - (r - 1)) (n - 1 - 1); rw [hdd]; exact zero_mem _

private theorem modelProjection_next_cycle (axis : Bool) (s : ℤ) (hs : 0 ≤ s) (r : ℤ)
    (hr : s ≤ r) (p n : ℤ) (x : X.X (-n))
    (hx : x ∈ (homologicalFiltrationOfSubobjects X G hanti hd).pageCycles r p n)
    (hx' : x ∈ (homologicalFiltrationOfSubobjects X G hanti hd).pageCycles (r + 1) p n) :
    ((homologicalSpectralSequence X G hanti axis s hs).page r hr).d
        (filtrationBidegree axis p n)
        ((torSpectralSequenceShape axis r).next (filtrationBidegree axis p n))
        (modelProjection X G hanti hd axis s hs r hr p n ⟨x, hx⟩) = 0 := by
  obtain ⟨h1, h2⟩ := pageCycles_succ_d_mem (homologicalFiltrationOfSubobjects X G hanti hd)
    r p n x hx'
  rw [(torSpectralSequenceShape axis r).next_eq' (torSpectralSequenceShape_rel axis r p n),
    modelProjection_differential X G hanti hd axis s hs r hr p n x hx h1]
  have hmem : (⟨_, h1⟩ : (homologicalFiltrationOfSubobjects X G hanti hd).pageCycles
      r (p - r) (n - 1)) ∈
      LinearMap.ker (modelProjection X G hanti hd axis s hs r hr (p - r) (n - 1)).hom := by
    rw [modelProjection_kernel]; exact h2
  exact hmem

private theorem modelProjection_next_projection (axis : Bool) (s : ℤ) (hs : 0 ≤ s) (r : ℤ)
    (hr : s ≤ r) (p n : ℤ) (x : X.X (-n))
    (hx : x ∈ (homologicalFiltrationOfSubobjects X G hanti hd).pageCycles r p n)
    (hx' : x ∈ (homologicalFiltrationOfSubobjects X G hanti hd).pageCycles (r + 1) p n) :
    ((homologicalSpectralSequence X G hanti axis s hs).iso r (r + 1)
        (filtrationBidegree axis p n) rfl hr).hom
      (((homologicalSpectralSequence X G hanti axis s hs).page r hr).homologyπ
        (filtrationBidegree axis p n)
        (((homologicalSpectralSequence X G hanti axis s hs).page r hr).cyclesMk
          (modelProjection X G hanti hd axis s hs r hr p n ⟨x, hx⟩)
          ((torSpectralSequenceShape axis r).next (filtrationBidegree axis p n)) rfl
          (modelProjection_next_cycle X G hanti hd axis s hs r hr p n x hx hx'))) =
      modelProjection X G hanti hd axis s hs (r + 1) (by omega) p n ⟨x, hx'⟩ := by
  set E := spectralSequence X G hanti with hE
  set pq := filtrationBidegree axis p n with hpq
  have hj := reverseBidegree_reverseBidegree axis pq
  have hinj := (ConcreteCategory.bijective_of_isIso
    (torIndexedSpectralSequence_pageIso E axis s hs (r + 1) (by omega) pq).hom).1
  apply hinj
  rw [modelProjection_apply, torIndexedSpectralSequence_iso_hom_apply]
  erw [hom_apply_eq_of_comp (HomologicalComplex.homologyπ_extendHomologyIso_hom
    (E.page r (hs.trans hr)) (torShapeEmbedding axis r) hj)]
  erw [ConcreteCategory.comp_apply]
  refine pageClass_next' X G hanti r (hs.trans hr) (reverseBidegree axis pq) (-n)
    (reverseBidegree_filtrationBidegree_sum axis p n)
    ⟨x, (modelFiltration_pageCycles_rev X G hanti hd axis r p n).le hx⟩
    ((modelFiltration_pageCycles_rev X G hanti hd axis (r + 1) p n).le hx') _ ?_
  erw [hom_apply_eq_of_comp (HomologicalComplex.extendCyclesIso_hom_iCycles _ _ _),
    ConcreteCategory.comp_apply]
  refine (congrArg _ ?_).trans
    (modelProjection_apply X G hanti hd axis s hs r hr p n ⟨x, hx⟩)
  exact HomologicalComplex.i_cyclesMk (C := ModuleCat.{v} R)
    ((torIndexedSpectralSequence E axis s hs).page r hr) _ _ _ _

/-- **The spectral sequence of a filtered complex, in homological indexing.** The pages of
`homologicalSpectralSequence` are the standard quotients of the `r`-cycles of the reversed
filtration by the `r`-relations, and its differentials and page-turning isomorphisms act on
representatives as the differential of the complex does. -/
theorem nonempty_torFiltrationData (axis : Bool) (s : ℤ) (hs : 0 ≤ s) :
    Nonempty (TorFiltrationData (homologicalSpectralSequence X G hanti axis s hs)
      (homologicalFiltrationOfSubobjects X G hanti hd) axis) :=
  ⟨{ shape := fun _ ↦ rfl
     projection := fun r hr p n ↦ modelProjection X G hanti hd axis s hs r hr p n
     surjective := fun r hr p n ↦ modelProjection_surjective X G hanti hd axis s hs r hr p n
     kernel := fun r hr p n ↦ modelProjection_kernel X G hanti hd axis s hs r hr p n
     differential := fun r hr p n x hx hdx ↦
       modelProjection_differential X G hanti hd axis s hs r hr p n x hx hdx
     next_cycle := fun r hr p n x hx hx' ↦
       modelProjection_next_cycle X G hanti hd axis s hs r hr p n x hx hx'
     next_projection := fun r hr p n x hx hx' ↦
       modelProjection_next_projection X G hanti hd axis s hs r hr p n x hx hx' }⟩

/-- Each step of a filtration of a cochain complex by subcomplexes is carried into the next by
the differential. -/
theorem factors_filtration_arrow_comp_d {A : Type u} [Category.{v} A] [Abelian A]
    (K : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ)
    (F : ∀ (_p n : ℤ), Subobject (K.X.X n))
    (hF : ∀ p n : ℤ, F p n = Subobject.mk ((K.filtration.ι.app (Opposite.op p)).f n))
    (p n m : ℤ) (hm : m = n + 1) : (F p m).Factors ((F p n).arrow ≫ K.X.d n m) := by
  subst hm
  rw [← Subobject.le_pullback_iff]
  have h := FilteredComplexSpectralSequence.cycles_zero_eq K F hF p n
  rw [FilteredComplexSpectralSequence.cycles, add_zero] at h
  exact h.ge.trans inf_le_right

end Model

end CochainComplex.Tor

end
