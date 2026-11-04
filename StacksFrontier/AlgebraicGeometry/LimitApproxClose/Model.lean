module

public import StacksFrontier.AlgebraicGeometry.LimitApproxClose.Chart

/-!
# A charted subalgebra is an open model, and its image is the union of the charted standard opens

Let `f : W ⟶ Spec R` be an open immersion and let `r : Fin n → R` be a finite family whose
standard opens lie inside the image of `f` and cover it.  A subalgebra `A ⊆ R` which is of
finite type, contains the family, and at every member of the family has the chart data of
`AlgebraicGeometry.HasAwayNumerators` is then an *open model* of `f` — the canonical factorization
`W ⟶ Spec A` is an open immersion — **and** its image is exactly the union of the standard opens
of the family read inside `Spec A`.

The second half is the statement the gluing step of the one-affine-open step of Tag 07RN needs
and which `Stacks.FiniteTypeOpenModel.IsOpenModel` does not provide: that predicate is
existential in the factorizing morphism and records nothing about its image.  The image is also
not a consequence of it, as the counterexample recorded with
`AlgebraicGeometry.HasAwayNumerators` shows.  What makes the image computable is precisely the
chart data.

## What is proved, and the route

* `AlgebraicGeometry.IsChartedSubalgebra` bundles the three conditions, and
  `AlgebraicGeometry.IsChartedSubalgebra.mono` enlarges the subalgebra, which is what makes
  charted subalgebras cofinal among the finitely generated ones.

* `AlgebraicGeometry.chartLift` lifts the inclusion of a charted standard open through `f`,
  which is possible because that standard open lies inside the image of `f`.  Composing the lift
  with the canonical factorization gives back the composite `D(r l) ⟶ Spec R ⟶ Spec A` of
  `AlgebraicGeometry.basicOpen_ι_comp_SpecMap_eq`, so each lift is an open immersion onto the
  standard open of the same element in `Spec A`.

* `AlgebraicGeometry.IsChartedSubalgebra.injective_comp_SpecMap_val` is the one step which is
  not local: two points of `W` with the same image in `Spec A` have their images under `f` in
  *one* charted standard open — the second lands there because the standard open of `Spec A` has
  the standard open of `Spec R` as its inverse image — and the chart is injective there.

* `AlgebraicGeometry.IsChartedSubalgebra.isOpenImmersion_comp_SpecMap_val` is then Mathlib's
  `AlgebraicGeometry.IsOpenImmersion.of_forall_source_exists` on the cover of `W` by the lifted
  charts, and `AlgebraicGeometry.IsChartedSubalgebra.isFiniteTypeOpenModel` reads the
  open-model predicate off it.

* `AlgebraicGeometry.IsChartedSubalgebra.opensRange_comp_SpecMap_val` is the image equality.
  One inclusion is the inverse-image computation applied to a point, the other is the image of
  one chart, which is an identified standard open of `Spec A`.

## Universe situation

The ring and the schemes are in the single universe `u` of the file this builds on.  No
limit or colimit is formed here and no index universe enters.

## Transparency gotchas

* The inclusion of the subalgebra is written `(A.val : A →+* R)` throughout, which is the
  spelling of the chart machinery; `A.subtype` is the same morphism but only up to
  unfolding, so `Stacks.FiniteTypeOpenModel.IsOpenModel` — which is stated with
  `A.subtype` — is reached by reflexivity rather than by a rewrite, exactly as in the proof of
  the chart machinery.

* The image equality is stated under a `haveI` introducing the open-immersion instance proved
  just above it.  Two `AlgebraicGeometry.Scheme.Hom.opensRange` terms built from different
  instances are equal, the open being a structure with a propositional second field, so a
  consumer carrying its own instance can use the statement unchanged.

* A standard open ascribed to the opens of `Spec R` is *not* a coercion: the members are opens of
  `PrimeSpectrum R`, and the ascription goes through only because the two carriers are
  definitionally equal.  A coercion of such an ascribed open to a `Set` of the carrier of
  `Spec R` is **not** found at all, which is why every statement here is about opens and the
  pointwise arguments go through `TopologicalSpace.Opens.mem_iSup`.

## What is NOT done here

The chart data is a hypothesis in this file.  Producing it — that is, finding a charted
subalgebra above a prescribed finitely generated one — is the sibling
`AlgebraicGeometry.exists_isChartedSubalgebra_ge`.  Nothing here mentions a diagram of schemes,
an inverse
limit, or `AlgebraicGeometry.Scheme.FiniteTypeApproximation`.  Tag 07RN is not proved and no tag
attribute is attached to anything in this file.

## References

* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
* [Stacks Project, Tag 01Z7](https://stacks.math.columbia.edu/tag/01Z7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R]

/-- **A subalgebra charted by a finite family of elements.**  It is of finite type over the
integers, contains the family, and at every member of the family carries the chart data which
makes the two localizations agree. -/
structure IsChartedSubalgebra (A : Subalgebra ℤ R) {n : ℕ} (r : Fin n → R) : Prop where
  /-- The subalgebra is of finite type over the integers. -/
  fg : A.FG
  /-- Every member of the family lies in the subalgebra. -/
  mem : ∀ l, r l ∈ A
  /-- At every member of the family the two localizations agree. -/
  numerators : ∀ l, HasAwayNumerators A (r l)

/-- A finite-type subalgebra containing a charted one is charted by the same family. -/
lemma IsChartedSubalgebra.mono {A B : Subalgebra ℤ R} (hAB : A ≤ B) (hB : B.FG) {n : ℕ}
    {r : Fin n → R} (h : IsChartedSubalgebra A r) : IsChartedSubalgebra B r :=
  ⟨hB, fun l ↦ hAB (h.mem l), fun l ↦ (h.numerators l).mono hAB⟩

variable {W : Scheme.{u}} {f : W ⟶ Spec (.of R)} [IsOpenImmersion f] {n : ℕ} {r : Fin n → R}
  {A : Subalgebra ℤ R}

/-- The standard open of a member of the family inside `Spec A` has the standard open of the
same element inside `Spec R` as its inverse image. -/
lemma IsChartedSubalgebra.preimage_basicOpen (h : IsChartedSubalgebra A r) (l : Fin n) :
    Spec.map (CommRingCat.ofHom (A.val : A →+* R)) ⁻¹ᵁ
        (PrimeSpectrum.basicOpen (⟨r l, h.mem l⟩ : A) : (Spec (.of A)).Opens) =
      (PrimeSpectrum.basicOpen (r l) : (Spec (.of R)).Opens) :=
  SpecMap_preimage_basicOpen _ _

/-- A point lies in the standard open of a member of the family in `Spec R` iff its image lies in
the standard open of the same element in `Spec A`. -/
private lemma IsChartedSubalgebra.mem_basicOpen_iff (h : IsChartedSubalgebra A r) (l : Fin n)
    {z : Spec (.of R)} :
    z ∈ (PrimeSpectrum.basicOpen (r l) : (Spec (.of R)).Opens) ↔
      Spec.map (CommRingCat.ofHom (A.val : A →+* R)) z ∈
        (PrimeSpectrum.basicOpen (⟨r l, h.mem l⟩ : A) : (Spec (.of A)).Opens) :=
  (SetLike.ext_iff.mp (h.preimage_basicOpen l) z).symm

/-- The inclusion of a standard open lying inside the image of `f`, lifted through `f`. -/
noncomputable def chartLift (f : W ⟶ Spec (.of R)) [IsOpenImmersion f] {n : ℕ} {r : Fin n → R}
    (hrU : ∀ l, (PrimeSpectrum.basicOpen (r l) : (Spec (.of R)).Opens) ≤ f.opensRange)
    (l : Fin n) :
    Scheme.Opens.toScheme (X := Spec (.of R)) (PrimeSpectrum.basicOpen (r l)) ⟶ W :=
  IsOpenImmersion.lift f (Scheme.Opens.ι _) (by
    rintro y ⟨z, rfl⟩
    exact hrU l z.2)

/-- A lifted chart followed by `f` is the inclusion of the standard open `D(r l)` into `Spec R`. -/
lemma chartLift_comp (f : W ⟶ Spec (.of R)) [IsOpenImmersion f] {n : ℕ} {r : Fin n → R}
    (hrU : ∀ l, (PrimeSpectrum.basicOpen (r l) : (Spec (.of R)).Opens) ≤ f.opensRange)
    (l : Fin n) :
    chartLift f hrU l ≫ f =
      Scheme.Opens.ι (X := Spec (.of R)) (PrimeSpectrum.basicOpen (r l)) :=
  IsOpenImmersion.lift_fac _ _ _

/-- A lifted chart is an open immersion. -/
instance isOpenImmersion_chartLift (f : W ⟶ Spec (.of R)) [IsOpenImmersion f] {n : ℕ}
    {r : Fin n → R}
    (hrU : ∀ l, (PrimeSpectrum.basicOpen (r l) : (Spec (.of R)).Opens) ≤ f.opensRange)
    (l : Fin n) : IsOpenImmersion (chartLift f hrU l) := by
  have hι : IsOpenImmersion (Scheme.Opens.ι (X := Spec (.of R))
      (PrimeSpectrum.basicOpen (r l))) := by
    rw [← basicOpenIsoSpecAway_hom_SpecMap (R := CommRingCat.of R)]
    infer_instance
  have h : IsOpenImmersion (chartLift f hrU l ≫ f) := by
    rw [chartLift_comp]
    exact hι
  exact IsOpenImmersion.of_comp _ f

/-- A lifted chart composed with the canonical factorization is the composite
`D(r l) ⟶ Spec R ⟶ Spec A` of `AlgebraicGeometry.basicOpen_ι_comp_SpecMap_eq`. -/
lemma chartLift_comp_SpecMap_val (A : Subalgebra ℤ R) (f : W ⟶ Spec (.of R)) [IsOpenImmersion f]
    {n : ℕ} {r : Fin n → R}
    (hrU : ∀ l, (PrimeSpectrum.basicOpen (r l) : (Spec (.of R)).Opens) ≤ f.opensRange)
    (l : Fin n) :
    chartLift f hrU l ≫ f ≫ Spec.map (CommRingCat.ofHom (A.val : A →+* R)) =
      Scheme.Opens.ι (X := Spec (.of R)) (PrimeSpectrum.basicOpen (r l)) ≫
        Spec.map (CommRingCat.ofHom (A.val : A →+* R)) := by
  rw [← Category.assoc, chartLift_comp]

/-- For a charted subalgebra `A`, a lifted chart followed by `f` and the canonical map
`Spec R ⟶ Spec A` is an open immersion. -/
lemma IsChartedSubalgebra.isOpenImmersion_chartLift_comp (h : IsChartedSubalgebra A r)
    (hrU : ∀ l, (PrimeSpectrum.basicOpen (r l) : (Spec (.of R)).Opens) ≤ f.opensRange)
    (l : Fin n) :
    IsOpenImmersion (chartLift f hrU l ≫ f ≫
      Spec.map (CommRingCat.ofHom (A.val : A →+* R))) := by
  rw [chartLift_comp_SpecMap_val]
  exact (h.numerators l).isOpenImmersion_basicOpen_ι_comp_SpecMap_val (h.mem l)

/-- Each point of `W` is carried by `f` into one of the charted standard opens. -/
lemma exists_mem_basicOpen (f : W ⟶ Spec (.of R)) [IsOpenImmersion f] {n : ℕ} {r : Fin n → R}
    (hcover : f.opensRange ≤ ⨆ l, (PrimeSpectrum.basicOpen (r l) : (Spec (.of R)).Opens))
    (x : W) :
    ∃ l, f x ∈ (PrimeSpectrum.basicOpen (r l) : (Spec (.of R)).Opens) :=
  Opens.mem_iSup.mp (hcover (Scheme.Hom.mem_opensRange.mpr ⟨x, rfl⟩))

/-- **The canonical factorization through a charted subalgebra is injective.**  Two points with
the same image have their `f`-images in one charted standard open, where the chart is
injective. -/
lemma IsChartedSubalgebra.injective_comp_SpecMap_val (h : IsChartedSubalgebra A r)
    (hcover : f.opensRange ≤ ⨆ l, (PrimeSpectrum.basicOpen (r l) : (Spec (.of R)).Opens)) :
    Function.Injective (f ≫ Spec.map (CommRingCat.ofHom (A.val : A →+* R))) := by
  intro x y hxy
  obtain ⟨l, hxl⟩ := exists_mem_basicOpen f hcover x
  have hgxy : Spec.map (CommRingCat.ofHom (A.val : A →+* R)) (f x) =
      Spec.map (CommRingCat.ofHom (A.val : A →+* R)) (f y) := hxy
  have hyl : f y ∈ (PrimeSpectrum.basicOpen (r l) : (Spec (.of R)).Opens) := by
    refine (h.mem_basicOpen_iff l).mpr ?_
    rw [← hgxy]
    exact (h.mem_basicOpen_iff l).mp hxl
  have hoi := (h.numerators l).isOpenImmersion_basicOpen_ι_comp_SpecMap_val (h.mem l)
  have hpq : (⟨f x, hxl⟩ : Scheme.Opens.toScheme (X := Spec (.of R))
      (PrimeSpectrum.basicOpen (r l))) = ⟨f y, hyl⟩ :=
    (Scheme.Hom.isOpenEmbedding (Scheme.Opens.ι (X := Spec (.of R))
      (PrimeSpectrum.basicOpen (r l)) ≫
      Spec.map (CommRingCat.ofHom (A.val : A →+* R)))).injective hgxy
  exact f.isOpenEmbedding.injective (congrArg Subtype.val hpq)

/-- **A charted subalgebra is an open model.**  The canonical factorization `W ⟶ Spec A` is an
open immersion: it is injective, and on each lifted chart it is the chart itself. -/
lemma IsChartedSubalgebra.isOpenImmersion_comp_SpecMap_val (h : IsChartedSubalgebra A r)
    (hrU : ∀ l, (PrimeSpectrum.basicOpen (r l) : (Spec (.of R)).Opens) ≤ f.opensRange)
    (hcover : f.opensRange ≤ ⨆ l, (PrimeSpectrum.basicOpen (r l) : (Spec (.of R)).Opens)) :
    IsOpenImmersion (f ≫ Spec.map (CommRingCat.ofHom (A.val : A →+* R))) := by
  refine IsOpenImmersion.of_forall_source_exists _
    (h.injective_comp_SpecMap_val hcover) fun x ↦ ?_
  obtain ⟨l, hxl⟩ := exists_mem_basicOpen f hcover x
  refine ⟨_, chartLift f hrU l, inferInstance, ?_, h.isOpenImmersion_chartLift_comp hrU l⟩
  refine Scheme.Hom.mem_opensRange.mpr ⟨⟨f x, hxl⟩, ?_⟩
  refine f.isOpenEmbedding.injective ?_
  exact congrArg (fun k : Scheme.Opens.toScheme (X := Spec (.of R))
    (PrimeSpectrum.basicOpen (r l)) ⟶ Spec (.of R) ↦ k ⟨f x, hxl⟩) (chartLift_comp f hrU l)

/-- A charted subalgebra is a finite-type open model in the sense of
`Stacks.FiniteTypeOpenModel.IsOpenModel`. -/
lemma IsChartedSubalgebra.isFiniteTypeOpenModel (h : IsChartedSubalgebra A r)
    (hrU : ∀ l, (PrimeSpectrum.basicOpen (r l) : (Spec (.of R)).Opens) ≤ f.opensRange)
    (hcover : f.opensRange ≤ ⨆ l, (PrimeSpectrum.basicOpen (r l) : (Spec (.of R)).Opens)) :
    Stacks.FiniteTypeOpenModel.IsOpenModel f A :=
  ⟨h.fg, _, h.isOpenImmersion_comp_SpecMap_val hrU hcover, rfl⟩

/-- **The image of the canonical factorization through a charted subalgebra.**  It is the union
of the standard opens of the charting family, read inside the spectrum of the subalgebra.

This is the image computation that the gluing of the one-affine-open step of Tag 07RN needs:
with a *compatible* choice of charting family along an inverse system, the images of the
factorizations are inverse images of one another, which is the cartesianness the glued system
requires. -/
theorem IsChartedSubalgebra.opensRange_comp_SpecMap_val (h : IsChartedSubalgebra A r)
    (hrU : ∀ l, (PrimeSpectrum.basicOpen (r l) : (Spec (.of R)).Opens) ≤ f.opensRange)
    (hcover : f.opensRange ≤ ⨆ l, (PrimeSpectrum.basicOpen (r l) : (Spec (.of R)).Opens)) :
    haveI := h.isOpenImmersion_comp_SpecMap_val hrU hcover
    (f ≫ Spec.map (CommRingCat.ofHom (A.val : A →+* R))).opensRange =
      (⨆ l, PrimeSpectrum.basicOpen (⟨r l, h.mem l⟩ : A) : (Spec (.of A)).Opens) := by
  have hg := h.isOpenImmersion_comp_SpecMap_val hrU hcover
  refine le_antisymm (fun y hy ↦ ?_) (iSup_le fun l y hy ↦ ?_)
  · obtain ⟨x, rfl⟩ := Scheme.Hom.mem_opensRange.mp hy
    obtain ⟨l, hxl⟩ := exists_mem_basicOpen f hcover x
    exact Opens.mem_iSup.mpr ⟨l, (h.mem_basicOpen_iff l).mp hxl⟩
  · have himg := (h.numerators l).opensRange_basicOpen_ι_comp_SpecMap_val (h.mem l)
    have hoi := (h.numerators l).isOpenImmersion_basicOpen_ι_comp_SpecMap_val (h.mem l)
    rw [← himg] at hy
    obtain ⟨z, rfl⟩ := Scheme.Hom.mem_opensRange.mp hy
    refine Scheme.Hom.mem_opensRange.mpr ⟨chartLift f hrU l z, ?_⟩
    exact congrArg (fun k : Scheme.Opens.toScheme (X := Spec (.of R))
      (PrimeSpectrum.basicOpen (r l)) ⟶ Spec (.of A) ↦ k z)
      (chartLift_comp_SpecMap_val A f hrU l)

end AlgebraicGeometry
