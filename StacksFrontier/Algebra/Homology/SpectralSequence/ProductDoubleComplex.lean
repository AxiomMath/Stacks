module

public import StacksFrontier.Algebra.Homology.SpectralSequence.DoubleComplex
public import StacksFrontier.Algebra.Homology.AbelianGroupComplexResolutions

/-!
# The spectral sequence of the product totalization of a double complex

Let `K^{•, •}` be a double complex of abelian groups whose first index runs over `ℕ` and whose
second runs over `ℤ`, and let `Tot_π(K)` be its product totalization, with
`Tot_π^n(K) = ∏_{p + q = n} K^{p, q}`. Filtering `Tot_π(K)` by the first coordinate,
`F^i Tot_π^n(K) = ∏_{p + q = n, p ≥ i} K^{p, q}`, gives a filtered complex, hence a spectral
sequence whose zeroth page is the column `E_0^{p, q} = K^{p, q}`.

The filtration is exhaustive, `F^i Tot_π(K) = Tot_π(K)` for `i ≤ 0`, but it is not degreewise
finite: a single total degree meets infinitely many columns, so no convergence is asserted.

## Main definitions

* `HomologicalComplex₂.productTotalColumnSubobject`: the step `F^i Tot_π^n(K)`, as a subobject.
* `HomologicalComplex₂.productTotalColumnFiltration`: `Tot_π(K)` filtered by its first
  coordinate.
* `HomologicalComplex₂.productTotalColumnSpectralSequence`: the spectral sequence of that
  filtered complex.

## Main results

* `HomologicalComplex₂.productTotalColumnCokernelIso`: the graded piece
  `F^p Tot_π^{p + q}(K)/F^{p + 1} Tot_π^{p + q}(K)` is the column `K^{p, q}`.
* `HomologicalComplex₂.exists_iso_zeroPage_productTotalColumn`: `E_0^{p, q} = K^{p, q}`, by an
  isomorphism sending the class of an element of `F^p Tot_π^{p + q}(K)` to its component in the
  first coordinate `p`.

## Implementation notes

`Tot_π^n(K)` is the group of dependent functions on the pairs `(p, q) ∈ ℕ × ℤ` with `p + q = n`
of `StacksFrontier.Algebra.Homology.AbelianGroupComplexResolutions`, so the steps of the filtration are the
subgroups cut out by vanishing in the columns `p < i`, and the graded piece is computed by the
short exact sequence whose surjection evaluates at the single remaining column.

## References

* [Stacks Project, Tag 012M](https://stacks.math.columbia.edu/tag/012M)
* [Stacks Project, Tag 0130](https://stacks.math.columbia.edu/tag/0130)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace HomologicalComplex₂

variable (K : HomologicalComplex₂ AddCommGrpCat.{u} (ComplexShape.up ℕ) (ComplexShape.up ℤ))

/-! ### The filtration of `Tot_π(K)` by the simplicial coordinate -/

/-- The subgroup of `Tot_π^n(K) = ∏_{p + q = n} K^{p, q}` of families vanishing in every
simplicial degree `p < i`. -/
def productTotalColumnSupport (i n : ℤ) : AddSubgroup (K.productTotalX n) where
  carrier := {x | ∀ j : {pq : ℕ × ℤ // (pq.1 : ℤ) + pq.2 = n}, (j.1.1 : ℤ) < i → x j = 0}
  zero_mem' _ _ := rfl
  add_mem' {x y} hx hy j hj := show x j + y j = 0 by rw [hx j hj, hy j hj, add_zero]
  neg_mem' {x} hx j hj := show -(x j) = 0 by rw [hx j hj, neg_zero]

/-- Families supported in simplicial degrees `≥ i'` are supported in simplicial degrees `≥ i`
when `i ≤ i'`. -/
lemma productTotalColumnSupport_le (i i' n : ℤ) (h : i ≤ i') :
    K.productTotalColumnSupport i' n ≤ K.productTotalColumnSupport i n :=
  fun _ hx j hj => hx j (lt_of_lt_of_le hj h)

/-- The differential of `Tot_π(K)` preserves the subgroup of families supported in simplicial
degrees `≥ i`: its component in `K^{p, q}` only involves the components in `K^{p, q - 1}` and
`K^{p - 1, q}`. -/
lemma productTotalD_mem_columnSupport (i n : ℤ) (x : K.productTotalX n)
    (hx : x ∈ K.productTotalColumnSupport i n) :
    K.productTotalD n x ∈ K.productTotalColumnSupport i (n + 1) := by
  rintro ⟨⟨p, q⟩, h⟩ hp
  rcases p with _ | p
  · rw [productTotalD_apply, productTotalDComp_zero_left, hx _ (by exact_mod_cast hp)]
    exact map_zero _
  · rw [productTotalD_apply, productTotalDComp_succ, hx _ (by push_cast at hp ⊢; omega),
      hx _ (by push_cast at hp ⊢; omega)]
    simp

/-- The restriction of the differential of `Tot_π(K)` to the families supported in simplicial
degrees `≥ i`. -/
def productTotalColumnD (i n : ℤ) :
    AddCommGrpCat.of (K.productTotalColumnSupport i n) ⟶
      AddCommGrpCat.of (K.productTotalColumnSupport i (n + 1)) :=
  AddCommGrpCat.ofHom
    (((K.productTotalD n).hom.comp (K.productTotalColumnSupport i n).subtype).codRestrict _
      fun x => K.productTotalD_mem_columnSupport i n x.1 x.2)

/-- The inclusion of the subgroup `F^i Tot_π^n(K)` into `Tot_π^n(K)`. -/
def productTotalColumnSubtype (i n : ℤ) :
    AddCommGrpCat.of (K.productTotalColumnSupport i n) ⟶ K.productTotal.X n :=
  AddCommGrpCat.ofHom (K.productTotalColumnSupport i n).subtype

/-- The inclusion of `F^i Tot_π^n(K)` into `Tot_π^n(K)` is a monomorphism. -/
instance mono_productTotalColumnSubtype (i n : ℤ) : Mono (K.productTotalColumnSubtype i n) :=
  ConcreteCategory.mono_of_injective _ fun _ _ h => Subtype.ext h

/-- The inclusion of `F^i Tot_π^n(K)` into `Tot_π^n(K)` sends an element to its underlying
family. -/
@[simp]
lemma productTotalColumnSubtype_apply (i n : ℤ)
    (x : AddCommGrpCat.of (K.productTotalColumnSupport i n)) :
    K.productTotalColumnSubtype i n x = x.1 := rfl

/-- The restricted differential `F^i Tot_π^n(K) ⟶ F^i Tot_π^{n + 1}(K)` followed by the inclusion
into `Tot_π^{n + 1}(K)` is the inclusion followed by the differential of `Tot_π(K)`. -/
@[reassoc]
lemma productTotalColumnD_comp_subtype (i n : ℤ) :
    K.productTotalColumnD i n ≫ K.productTotalColumnSubtype i (n + 1) =
      K.productTotalColumnSubtype i n ≫ K.productTotal.d n (n + 1) := by
  rw [productTotal_d]
  ext x
  exact rfl

/-- The inclusion of the subgroup `F^{i'} Tot_π^n(K)` into `F^i Tot_π^n(K)`, for `i ≤ i'`. -/
def productTotalColumnInclusion (i i' n : ℤ) (h : i ≤ i') :
    AddCommGrpCat.of (K.productTotalColumnSupport i' n) ⟶
      AddCommGrpCat.of (K.productTotalColumnSupport i n) :=
  AddCommGrpCat.ofHom (AddSubgroup.inclusion (K.productTotalColumnSupport_le i i' n h))

/-- The inclusion `F^{i'} Tot_π^n(K) ⟶ F^i Tot_π^n(K)` followed by the inclusion into
`Tot_π^n(K)` is the inclusion of `F^{i'} Tot_π^n(K)` into `Tot_π^n(K)`. -/
@[reassoc]
lemma productTotalColumnInclusion_comp_subtype (i i' n : ℤ) (h : i ≤ i') :
    K.productTotalColumnInclusion i i' n h ≫ K.productTotalColumnSubtype i n =
      K.productTotalColumnSubtype i' n := rfl

/-- **The step `F^i Tot_π^n(K) = ∏_{p + q = n, p ≥ i} K^{p, q}`**, as a subobject of the
degree-`n` term of the product total complex. -/
def productTotalColumnSubobject (i n : ℤ) : Subobject (K.productTotal.X n) :=
  Subobject.mk (K.productTotalColumnSubtype i n)

/-- The underlying object of `productTotalColumnSubobject` is the subgroup it is made from. -/
def productTotalColumnSubobjectIso (i n : ℤ) :
    (K.productTotalColumnSubobject i n : AddCommGrpCat.{u}) ≅
      AddCommGrpCat.of (K.productTotalColumnSupport i n) :=
  Subobject.underlyingIso (K.productTotalColumnSubtype i n)

/-- `productTotalColumnSubobjectIso` followed by the inclusion of the subgroup is the arrow of
the subobject `productTotalColumnSubobject`. -/
@[reassoc (attr := simp)]
lemma productTotalColumnSubobjectIso_hom_subtype (i n : ℤ) :
    (K.productTotalColumnSubobjectIso i n).hom ≫ K.productTotalColumnSubtype i n =
      (K.productTotalColumnSubobject i n).arrow :=
  Subobject.underlyingIso_hom_comp_eq_mk _

/-- The inverse of `productTotalColumnSubobjectIso` followed by the arrow of the subobject
`productTotalColumnSubobject` is the inclusion of the subgroup. -/
@[reassoc (attr := simp)]
lemma productTotalColumnSubobjectIso_inv_arrow (i n : ℤ) :
    (K.productTotalColumnSubobjectIso i n).inv ≫ (K.productTotalColumnSubobject i n).arrow =
      K.productTotalColumnSubtype i n :=
  Subobject.underlyingIso_arrow _

/-- The steps of the filtration decrease: `F^{i'} Tot_π^n(K) ≤ F^i Tot_π^n(K)` for `i ≤ i'`. -/
lemma productTotalColumnSubobject_antitone (i i' n : ℤ) (h : i ≤ i') :
    K.productTotalColumnSubobject i' n ≤ K.productTotalColumnSubobject i n := by
  refine Subobject.mk_le_mk_of_comm (K.productTotalColumnInclusion i i' n h) ?_
  exact K.productTotalColumnInclusion_comp_subtype i i' n h

/-- The differential `Tot_π^m(K) ⟶ Tot_π^{m'}(K)` maps `F^i Tot_π^m(K)` into
`F^i Tot_π^{m'}(K)`. -/
lemma productTotalColumnSubobject_factors (i m m' : ℤ) :
    (K.productTotalColumnSubobject i m').Factors
      ((K.productTotalColumnSubobject i m).arrow ≫ K.productTotal.d m m') := by
  by_cases h : m + 1 = m'
  · subst h
    have key : ((K.productTotalColumnSubobjectIso i m).hom ≫ K.productTotalColumnD i m ≫
          (K.productTotalColumnSubobjectIso i (m + 1)).inv) ≫
            (K.productTotalColumnSubobject i (m + 1)).arrow =
        (K.productTotalColumnSubobject i m).arrow ≫ K.productTotal.d m (m + 1) := by
      rw [Category.assoc, Category.assoc, K.productTotalColumnSubobjectIso_inv_arrow i (m + 1),
        K.productTotalColumnD_comp_subtype i m, ← Category.assoc,
        K.productTotalColumnSubobjectIso_hom_subtype i m]
    rw [← key]
    exact Subobject.factors_comp_arrow _
  · rw [K.productTotal.shape m m' (by simpa using h), comp_zero]
    exact Subobject.factors_zero

/-- **The subcomplex `F^i Tot_π(K)`** of the product total complex: in degree `n` the families
`∏_{p + q = n} K^{p, q}` supported in simplicial degrees `p ≥ i`. -/
abbrev productTotalColumnSubcomplex (i : ℤ) : CochainComplex AddCommGrpCat.{u} ℤ :=
  HomologicalComplex.subcomplexOfSubobjects K.productTotal (K.productTotalColumnSubobject i)
    (K.productTotalColumnSubobject_factors i)

/-- The diagram `i ↦ F^i Tot_π(K)` of the steps of the filtration by the simplicial
coordinate. -/
def productTotalColumnDiagram : ℤᵒᵖ ⥤ CochainComplex AddCommGrpCat.{u} ℤ where
  obj i := K.productTotalColumnSubcomplex i.unop
  map f := HomologicalComplex.subcomplexOfSubobjectsMap _ _ _
    fun n => K.productTotalColumnSubobject_antitone _ _ n (leOfHom f.unop)
  map_id _ := HomologicalComplex.hom_ext _ _ fun _ => Subobject.ofLE_refl _
  map_comp _ _ := HomologicalComplex.hom_ext _ _ fun _ => by
    simp only [HomologicalComplex.comp_f, HomologicalComplex.subcomplexOfSubobjectsMap_f]
    rw [Subobject.ofLE_comp_ofLE]

/-- The inclusions `F^i Tot_π(K) ⟶ Tot_π(K)` of the steps of the filtration. -/
def productTotalColumnDiagramι :
    K.productTotalColumnDiagram ⟶ (Functor.const ℤᵒᵖ).obj K.productTotal where
  app _ := HomologicalComplex.subcomplexOfSubobjectsι _ _ _
  naturality _ _ _ := HomologicalComplex.hom_ext _ _ fun _ => by
    simp [productTotalColumnDiagram]

/-- Each inclusion `F^i Tot_π(K) ⟶ Tot_π(K)` is a monomorphism. -/
instance mono_productTotalColumnDiagramι_app (i : ℤᵒᵖ) :
    Mono (K.productTotalColumnDiagramι.app i) :=
  inferInstanceAs (Mono (HomologicalComplex.subcomplexOfSubobjectsι K.productTotal
    (K.productTotalColumnSubobject i.unop) (K.productTotalColumnSubobject_factors i.unop)))

/-- **The filtration of `Tot_π(K)` by the simplicial coordinate**, with
`F^i Tot_π^n(K) = ∏_{p + q = n, p ≥ i} K^{p, q}`. -/
def productTotalColumnFiltration :
    FilteredObject (CochainComplex AddCommGrpCat.{u} ℤ) ℤᵒᵖ where
  X := K.productTotal
  filtration := Filtration.ofDiagram _ K.productTotalColumnDiagramι

/-- `productTotalColumnSubobject i n` is the subobject of `Tot_π^n(K)` given by the degree-`n`
component of the `i`-th step of `productTotalColumnFiltration`. -/
lemma productTotalColumnSubobject_eq (i n : ℤ) :
    K.productTotalColumnSubobject i n =
      Subobject.mk ((K.productTotalColumnFiltration.filtration.ι.app (op i)).f n) :=
  (Subobject.mk_arrow _).symm

/-! ### The graded pieces of the filtration -/

/-- The projection of `F^p Tot_π^n(K)` onto its component in the lowest surviving column
`K^{p, q}`, where `p + q = n`. -/
def productTotalColumnProjection (p : ℕ) (n q : ℤ) (h : (p : ℤ) + q = n) :
    AddCommGrpCat.of (K.productTotalColumnSupport (p : ℤ) n) ⟶ (K.X p).X q :=
  AddCommGrpCat.ofHom
    { toFun x := x.1 ⟨(p, q), h⟩
      map_zero' := rfl
      map_add' _ _ := rfl }

/-- `productTotalColumnProjection` sends a family to its component in `K^{p, q}`. -/
@[simp]
lemma productTotalColumnProjection_apply (p : ℕ) (n q : ℤ) (h : (p : ℤ) + q = n)
    (x : AddCommGrpCat.of (K.productTotalColumnSupport (p : ℤ) n)) :
    K.productTotalColumnProjection p n q h x = x.1 ⟨(p, q), h⟩ := rfl

/-- The family in `Tot_π^n(K)` whose component in `K^{p, q}` is `y` and whose other components
vanish. -/
def productTotalColumnSingle (p : ℕ) (n q : ℤ) (h : (p : ℤ) + q = n) (y : (K.X p).X q) :
    K.productTotalX n := fun j =>
  if hj : j = ⟨(p, q), h⟩ then
    (eqToHom (congrArg (fun k : {pq : ℕ × ℤ // (pq.1 : ℤ) + pq.2 = n} =>
      (K.X k.1.1).X k.1.2) hj.symm) : (K.X p).X q ⟶ (K.X j.1.1).X j.1.2) y
  else 0

/-- The component of `productTotalColumnSingle p n q h y` in `K^{p, q}` is `y`. -/
@[simp]
lemma productTotalColumnSingle_self (p : ℕ) (n q : ℤ) (h : (p : ℤ) + q = n) (y : (K.X p).X q) :
    K.productTotalColumnSingle p n q h y ⟨(p, q), h⟩ = y := by
  rw [productTotalColumnSingle, dite_eq_left rfl]
  rfl

/-- The components of `productTotalColumnSingle p n q h y` away from `K^{p, q}` vanish. -/
lemma productTotalColumnSingle_of_ne (p : ℕ) (n q : ℤ) (h : (p : ℤ) + q = n) (y : (K.X p).X q)
    (j : {pq : ℕ × ℤ // (pq.1 : ℤ) + pq.2 = n}) (hj : j ≠ ⟨(p, q), h⟩) :
    K.productTotalColumnSingle p n q h y j = 0 := dite_eq_right hj

/-- The projection of `F^p Tot_π^n(K)` onto `K^{p, q}` is surjective. -/
lemma productTotalColumnProjection_surjective (p : ℕ) (n q : ℤ) (h : (p : ℤ) + q = n) :
    Function.Surjective (K.productTotalColumnProjection p n q h) := by
  intro y
  refine ⟨⟨K.productTotalColumnSingle p n q h y, fun j hj => ?_⟩,
    K.productTotalColumnSingle_self p n q h y⟩
  refine K.productTotalColumnSingle_of_ne p n q h y j fun hjj => ?_
  rw [hjj] at hj
  exact absurd hj (lt_irrefl _)

/-- The composite `F^{p + 1} Tot_π^n(K) ⟶ F^p Tot_π^n(K) ⟶ K^{p, q}` is zero. -/
lemma productTotalColumnInclusion_comp_projection (p : ℕ) (n q : ℤ) (h : (p : ℤ) + q = n) :
    K.productTotalColumnInclusion (p : ℤ) ((p : ℤ) + 1) n (by omega) ≫
        K.productTotalColumnProjection p n q h = 0 := by
  ext x
  exact x.2 ⟨(p, q), h⟩ (by dsimp; omega)

/-- The short complex `F^{p + 1} Tot_π^n(K) ⟶ F^p Tot_π^n(K) ⟶ K^{p, q}`, for `p + q = n`. -/
def productTotalColumnShortComplex (p : ℕ) (n q : ℤ) (h : (p : ℤ) + q = n) :
    ShortComplex AddCommGrpCat.{u} :=
  ShortComplex.mk _ _ (K.productTotalColumnInclusion_comp_projection p n q h)

/-- The sequence `0 ⟶ F^{p + 1} Tot_π^n(K) ⟶ F^p Tot_π^n(K) ⟶ K^{p, q} ⟶ 0` is short exact,
for `p + q = n`. -/
lemma productTotalColumnShortComplex_shortExact (p : ℕ) (n q : ℤ) (h : (p : ℤ) + q = n) :
    (K.productTotalColumnShortComplex p n q h).ShortExact where
  exact := (ShortComplex.ab_exact_iff _).2 fun x hx =>
    ⟨⟨x.1, fun j hj => by
      rcases lt_or_eq_of_le (by omega : (j.1.1 : ℤ) ≤ (p : ℤ)) with hlt | heq
      · exact x.2 j hlt
      · obtain rfl : j = ⟨(p, q), h⟩ :=
          Subtype.ext (Prod.ext (by exact_mod_cast heq)
            (by have := j.2; show j.1.2 = q; omega))
        exact hx⟩, rfl⟩
  mono_f := by
    show Mono (K.productTotalColumnInclusion (p : ℤ) ((p : ℤ) + 1) n (by omega))
    exact mono_of_mono_fac
      (K.productTotalColumnInclusion_comp_subtype (p : ℤ) ((p : ℤ) + 1) n (by omega))
  epi_g := ConcreteCategory.epi_of_surjective _ (K.productTotalColumnProjection_surjective p n q h)

/-- **The graded piece of the filtration by the first coordinate is a column.** For `p + q = n`
the quotient of `F^p Tot_π^n(K)` by `F^{p + 1} Tot_π^n(K)` is `K^{p, q}`, by the projection onto
the component in the first coordinate `p`. -/
def productTotalColumnCokernelIso (p : ℕ) (n q : ℤ) (h : (p : ℤ) + q = n) :
    cokernel (K.productTotalColumnInclusion (p : ℤ) ((p : ℤ) + 1) n (by omega)) ≅
      (K.X p).X q :=
  haveI := (K.productTotalColumnShortComplex_shortExact p n q h).epi_g
  colimit.isoColimitCocone ⟨_,
    (K.productTotalColumnShortComplex_shortExact p n q h).exact.gIsCokernel⟩

/-- The projection onto the cokernel followed by `productTotalColumnCokernelIso` is the
projection `productTotalColumnProjection` of `F^p Tot_π^n(K)` onto `K^{p, q}`. -/
@[reassoc (attr := simp)]
lemma π_productTotalColumnCokernelIso_hom (p : ℕ) (n q : ℤ) (h : (p : ℤ) + q = n) :
    cokernel.π (K.productTotalColumnInclusion (p : ℤ) ((p : ℤ) + 1) n (by omega)) ≫
        (K.productTotalColumnCokernelIso p n q h).hom =
      K.productTotalColumnProjection p n q h :=
  colimit.isoColimitCocone_ι_hom _ WalkingParallelPair.one

/-! ### The zeroth and first pages -/

/-- **The spectral sequence of the filtration of `Tot_π(K)` by the first coordinate.**
Its pages are the quotients `Z_r^{p, q}/(D_r^{p, q} ⊓ Z_r^{p, q})` of the cycles and boundaries
of the filtration `F^i Tot_π^n(K) = ∏_{p + q = n, p ≥ i} K^{p, q}`, and its differentials are
induced by the differential of `Tot_π(K)`. -/
abbrev productTotalColumnSpectralSequence :
    CohomologicalSpectralSequence AddCommGrpCat.{u} 0 :=
  FilteredComplexSpectralSequence.spectralSequence K.productTotal
    K.productTotalColumnSubobject
    fun _ _ n h => K.productTotalColumnSubobject_antitone _ _ n h

open FilteredComplexSpectralSequence in
/-- `Z_0^{i, n} = F^i Tot_π^n(K)`, so the zeroth cycles lift canonically to the subgroup of
families supported in the columns `≥ i`. -/
def productTotalColumnCyclesLift (i n : ℤ) :
    (cycles K.productTotal K.productTotalColumnSubobject 0 i n : AddCommGrpCat.{u}) ⟶
      AddCommGrpCat.of (K.productTotalColumnSupport i n) :=
  Subobject.ofLE _ _ (le_of_eq (cycles_zero_eq K.productTotalColumnFiltration
      K.productTotalColumnSubobject K.productTotalColumnSubobject_eq i n)) ≫
    (K.productTotalColumnSubobjectIso i n).hom

open FilteredComplexSpectralSequence in
/-- `productTotalColumnCyclesLift` followed by the inclusion of `F^i Tot_π^n(K)` into
`Tot_π^n(K)` is the arrow of the zeroth cycles `Z_0^{i, n}`. -/
@[reassoc]
lemma productTotalColumnCyclesLift_comp_subtype (i n : ℤ) :
    K.productTotalColumnCyclesLift i n ≫ K.productTotalColumnSubtype i n =
      (cycles K.productTotal K.productTotalColumnSubobject 0 i n).arrow := by
  rw [productTotalColumnCyclesLift, Category.assoc,
    K.productTotalColumnSubobjectIso_hom_subtype i n, Subobject.ofLE_arrow]

open FilteredComplexSpectralSequence in
/-- **The zeroth page of the spectral sequence is the column `K^{p, q}`**: the subquotient
`Z_0^{p, q}/(D_0^{p, q} ⊓ Z_0^{p, q})` is `F^p Tot_π^n(K)/F^{p + 1} Tot_π^n(K)`, which is
`K^{p, q}`. The second clause pins the isomorphism: the class of an element of `F^p Tot_π^n(K)`
goes to its component in `K^{p, q}`. -/
theorem exists_iso_zeroPage_productTotalColumn (p : ℕ) (n q : ℤ) (h : (p : ℤ) + q = n) :
    ∃ e : cokernel (den K.productTotal K.productTotalColumnSubobject 0 (p : ℤ) n) ≅
        (K.X p).X q,
      cokernel.π (den K.productTotal K.productTotalColumnSubobject 0 (p : ℤ) n) ≫ e.hom =
        K.productTotalColumnCyclesLift (p : ℤ) n ≫
          K.productTotalColumnProjection p n q h := by
  obtain ⟨e, he⟩ := exists_iso_cokernel_ofLE_of_eq
    (inf_le_right :
      boundaries K.productTotal K.productTotalColumnSubobject 0 (p : ℤ) n ⊓
        cycles K.productTotal K.productTotalColumnSubobject 0 (p : ℤ) n ≤ _)
    (K.productTotalColumnSubtype ((p : ℤ) + 1) n)
    (K.productTotalColumnSubtype (p : ℤ) n)
    (K.productTotalColumnInclusion (p : ℤ) ((p : ℤ) + 1) n (by omega))
    (K.productTotalColumnInclusion_comp_subtype _ _ _ _)
    (boundaries_zero_inf_cycles_zero K.productTotalColumnFiltration
      K.productTotalColumnSubobject K.productTotalColumnSubobject_eq (p : ℤ) n)
    (cycles_zero_eq K.productTotalColumnFiltration
      K.productTotalColumnSubobject K.productTotalColumnSubobject_eq (p : ℤ) n)
  refine ⟨e ≪≫ K.productTotalColumnCokernelIso p n q h, ?_⟩
  refine (Category.assoc _ _ _).symm.trans ?_
  refine ((congrArg (· ≫ (K.productTotalColumnCokernelIso p n q h).hom)
    (he (K.productTotalColumnCyclesLift (p : ℤ) n)
      (K.productTotalColumnCyclesLift_comp_subtype (p : ℤ) n))).trans ?_)
  exact (Category.assoc _ _ _).trans
    (congrArg (K.productTotalColumnCyclesLift (p : ℤ) n ≫ ·)
      (K.π_productTotalColumnCokernelIso_hom p n q h))

/-- **The component of the differential of `Tot_π(K)` in the lowest surviving column.** On a
family supported in the columns `≥ p`, the component of `d` in `K^{p, q + 1}` is `(-1)^p` times
the differential of the column `K^{p, •}`. -/
lemma productTotalD_apply_column (p : ℕ) (n q q' : ℤ) (hq : (p : ℤ) + q = n) (hq' : q + 1 = q')
    (x : K.productTotalX n) (hx : x ∈ K.productTotalColumnSupport (p : ℤ) n) :
    K.productTotalD n x ⟨(p, q'), by omega⟩ =
      (-1 : ℤ) ^ p • (K.X p).d q q' (x ⟨(p, q), hq⟩) := by
  cases p with
  | zero =>
    rw [K.productTotalD_apply_zero_left n x q' q hq' (by omega) (by omega)]
    simp
  | succ p =>
    rw [K.productTotalD_apply_succ n x p q' q hq' (by push_cast; omega) (by push_cast; omega),
      hx ⟨(p, q'), by push_cast at hq ⊢; omega⟩ (by push_cast; omega), map_zero, zero_add]

open FilteredComplexSpectralSequence in
/-- **The zeroth differential is the differential of the column, up to sign.** On the zeroth
cycles `Z_0^{p,q} = F^p Tot_π^n(K)` the differential of `Tot_π(K)`, read in the column `p`, is
`(-1)^p` times the differential of `K^{p,•}`. -/
lemma deltaCycles'_comp_productTotalColumnProjection (p : ℕ) (n n' q q' : ℤ)
    (hq : (p : ℤ) + q = n) (hq' : (p : ℤ) + q' = n') (hqq' : q + 1 = q')
    (hp : (p : ℤ) = (p : ℤ) + 0) (hn : n' = n + 1) :
    deltaCycles' K.productTotal K.productTotalColumnSubobject 0 (p : ℤ) n (p : ℤ) n' hp hn ≫
        K.productTotalColumnCyclesLift (p : ℤ) n' ≫
          K.productTotalColumnProjection p n' q' hq' =
      K.productTotalColumnCyclesLift (p : ℤ) n ≫
        K.productTotalColumnProjection p n q hq ≫ ((-1 : ℤ) ^ p • (K.X p).d q q') := by
  subst hn
  ext x
  have hlift : ∀ (m : ℤ)
      (y : (cycles K.productTotal K.productTotalColumnSubobject 0 (p : ℤ) m : AddCommGrpCat.{u})),
      ((K.productTotalColumnCyclesLift (p : ℤ) m y : K.productTotalColumnSupport (p : ℤ) m) :
        K.productTotalX m) =
      (cycles K.productTotal K.productTotalColumnSubobject 0 (p : ℤ) m).arrow y := fun m y =>
    ConcreteCategory.congr_hom (K.productTotalColumnCyclesLift_comp_subtype (p : ℤ) m) y
  have h2 := ConcreteCategory.congr_hom
    (deltaCycles'_arrow K.productTotal K.productTotalColumnSubobject 0 (p : ℤ) n (p : ℤ)
      (n + 1) hp rfl) x
  simp only [CategoryTheory.comp_apply] at h2
  rw [productTotal_d] at h2
  have key := (hlift _ _).trans (h2.trans (congrArg (K.productTotalD n) (hlift n x).symm))
  have hmem := (K.productTotalColumnCyclesLift (p : ℤ) n x).2
  simp only [CategoryTheory.comp_apply, K.productTotalColumnProjection_apply]
  rw [key, K.productTotalD_apply_column p n q q' hq hqq' _ hmem]
  simp
  rfl

open FilteredComplexSpectralSequence in
/-- **`E_0^{p,q} = K^{p,q}`**, as data: the isomorphism from the zeroth page of
`productTotalColumnSpectralSequence` to the column `K^{p,q}` given by
`exists_iso_zeroPage_productTotalColumn`, pinned by `π_productTotalColumnZeroPageIso_hom`. -/
def productTotalColumnZeroPageIso (p : ℕ) (q : ℤ) :
    (K.productTotalColumnSpectralSequence.page 0 le_rfl).X ((p : ℤ), q) ≅ (K.X p).X q :=
  (K.exists_iso_zeroPage_productTotalColumn p ((p : ℤ) + q) q rfl).choose

open FilteredComplexSpectralSequence in
/-- `productTotalColumnZeroPageIso` sends the class of an element of `F^p Tot_π^{p+q}(K)` to its
component in `K^{p,q}`. -/
lemma π_productTotalColumnZeroPageIso_hom (p : ℕ) (q : ℤ) :
    cokernel.π (den K.productTotal K.productTotalColumnSubobject 0 (p : ℤ) ((p : ℤ) + q)) ≫
        (K.productTotalColumnZeroPageIso p q).hom =
      K.productTotalColumnCyclesLift (p : ℤ) ((p : ℤ) + q) ≫
        K.productTotalColumnProjection p ((p : ℤ) + q) q rfl :=
  (K.exists_iso_zeroPage_productTotalColumn p ((p : ℤ) + q) q rfl).choose_spec

open FilteredComplexSpectralSequence in
/-- Under `productTotalColumnZeroPageIso` the zeroth differential is `(-1)^p` times the
differential of the column `K^{p,•}`. -/
lemma productTotalColumnZeroPageIso_d (p : ℕ) (k k' : ℤ) (hk : k' = k + 1) :
    (K.productTotalColumnSpectralSequence.page 0 le_rfl).d ((p : ℤ), k) ((p : ℤ), k') ≫
        (K.productTotalColumnZeroPageIso p k').hom =
      (K.productTotalColumnZeroPageIso p k).hom ≫ (((-1 : ℤˣ) ^ p) • (K.X p).d k k') := by
  subst hk
  have hd : (K.productTotalColumnSpectralSequence.page 0 le_rfl).d ((p : ℤ), k)
        ((p : ℤ), k + 1) =
      pageMap' K.productTotal K.productTotalColumnSubobject 0 (p : ℤ) ((p : ℤ) + k) (p : ℤ)
        ((p : ℤ) + (k + 1)) (by omega) (by omega) :=
    pageComplex_d K.productTotal K.productTotalColumnSubobject 0
      (pq := ((p : ℤ), k)) (pq' := ((p : ℤ), k + 1)) (Prod.ext (by simp) (by simp))
  rw [hd]
  refine (cancel_epi (cokernel.π (den K.productTotal K.productTotalColumnSubobject 0 (p : ℤ)
    ((p : ℤ) + k)))).1 ?_
  rw [reassoc_of% (π_comp_pageMap' K.productTotal K.productTotalColumnSubobject 0 (p : ℤ)
      ((p : ℤ) + k) (p : ℤ) ((p : ℤ) + (k + 1)) (by omega) (by omega)),
    K.π_productTotalColumnZeroPageIso_hom p (k + 1),
    reassoc_of% (K.π_productTotalColumnZeroPageIso_hom p k), Units.smul_def,
    Units.val_pow_eq_pow_val]
  exact K.deltaCycles'_comp_productTotalColumnProjection p ((p : ℤ) + k) ((p : ℤ) + (k + 1)) k
    (k + 1) rfl rfl rfl (by omega) (by omega)

/-- **`E_1^{p,q} = H^q(K^{p,•})`**: the first page of the spectral sequence of the filtration of
`Tot_π(K)` by the first coordinate is the cohomology of the column `K^{p,•}`. -/
def productTotalColumnOnePageIso (p : ℕ) (q : ℤ) :
    (K.productTotalColumnSpectralSequence.page 1 zero_le_one).X ((p : ℤ), q) ≅
      (K.X p).homology q :=
  (K.productTotalColumnSpectralSequence.iso 0 1 ((p : ℤ), q)).symm ≪≫
    ShortComplex.homologyMapIso
      (lineScIso (K.productTotalColumnSpectralSequence.page 0 le_rfl) (fun k => ((p : ℤ), k))
        (fun k => Prod.ext (by simp) (by simp)) (K.X p) ((-1 : ℤˣ) ^ p)
        (K.productTotalColumnZeroPageIso p)
        (fun k k' hk => K.productTotalColumnZeroPageIso_d p k k' hk) q)

end HomologicalComplex₂

end
