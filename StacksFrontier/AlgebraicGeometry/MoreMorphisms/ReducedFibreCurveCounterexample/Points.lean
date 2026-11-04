module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreCurveCounterexample.Total

/-!
# Coordinates and the special point of the counterexample

On the `n`-th chart of the line with infinitely many origins the coordinate `t` is a section
`τ` generating a maximal ideal, and on the `n`-th chart of the total space the coordinates
`x` and `y` are sections with `τ = x ^ (n + 1) y`. The point `(0, 1)` of that chart lies over the
`n`-th origin, where `τ` vanishes, on the line `x = 0` and off the line `y = 0`.

## Main results

* `totalMap_appLE_baseCoord`: on the `n`-th chart, `τ = x ^ (n + 1) y`.
* `totalMap_specialPoint`: the special point of the `n`-th chart maps to the `n`-th origin.
* `eq_specialPoint_of_specializes`: the special point is a generic point of its fibre.
* `exists_germ_totalMap_baseCoord`: at the special point, the pullback of `τ` is the product of the
  `(n + 1)`-st power of an element of the maximal ideal and a unit.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Polynomial

universe u

namespace AlgebraicGeometry.ReducedFibreCurveCounterexample

section Charts

variable {R R' : CommRingCat.{u}} {Z Z' : Scheme.{u}} (ι : Spec R ⟶ Z) [IsOpenImmersion ι]

/-- The section of `Z` over the image of an open immersion `Spec R ⟶ Z` given by an element of
`R`. -/
def chartSection (r : R) : Γ(Z, ι ''ᵁ ⊤) :=
  (ι.appIso ⊤).inv ((Scheme.ΓSpecIso R).inv r)

/-- A point of the image of an open immersion `Spec R ⟶ Z` lies in the nonvanishing locus of the
section given by `r` exactly when `r` is not in its prime. -/
theorem mem_basicOpen_chartSection (r : R) (y : Spec R) :
    ι y ∈ Z.basicOpen (chartSection ι r) ↔ r ∉ y.asIdeal := by
  have h1 : y ∈ ι ⁻¹ᵁ Z.basicOpen (chartSection ι r) ↔ ι y ∈ Z.basicOpen (chartSection ι r) :=
    Iff.rfl
  rw [← h1, Scheme.preimage_basicOpen]
  have h2 : (Spec R).basicOpen ((ι.appIso ⊤).hom (chartSection ι r)) =
      ⊤ ⊓ (Spec R).basicOpen (ι.app (ι ''ᵁ ⊤) (chartSection ι r)) := by
    rw [Scheme.Hom.appIso_hom, ConcreteCategory.comp_apply, Scheme.basicOpen_res]
  rw [chartSection, Iso.inv_hom_id_apply, basicOpen_eq_of_affine, top_inf_eq] at h2
  show y ∈ (Spec R).basicOpen (ι.app (ι ''ᵁ ⊤) ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso R).inv r))) ↔ _
  rw [← h2]
  exact PrimeSpectrum.mem_basicOpen _ _

variable (ι' : Spec R' ⟶ Z') [IsOpenImmersion ι']

/-- The pullback of the section given by `r` along a morphism which is `Spec φ` on charts is the
section given by `φ r`. -/
theorem appLE_chartSection (F : Z' ⟶ Z) (φ : R ⟶ R') (h : ι' ≫ F = Spec.map φ ≫ ι)
    (hle : ι' ''ᵁ ⊤ ≤ F ⁻¹ᵁ (ι ''ᵁ ⊤)) (r : R) :
    F.appLE (ι ''ᵁ ⊤) (ι' ''ᵁ ⊤) hle (chartSection ι r) = chartSection ι' (φ r) := by
  apply (ι'.appIso ⊤).commRingCatIsoToRingEquiv.injective
  show (ι'.appIso ⊤).hom (F.appLE (ι ''ᵁ ⊤) (ι' ''ᵁ ⊤) hle (chartSection ι r)) =
    (ι'.appIso ⊤).hom (chartSection ι' (φ r))
  rw [show chartSection ι' (φ r) = (ι'.appIso ⊤).inv ((Scheme.ΓSpecIso R').inv (φ r)) from rfl,
    Iso.inv_hom_id_apply, ← ConcreteCategory.comp_apply,
    Scheme.Hom.appIso_hom', Scheme.Hom.appLE_comp_appLE]
  have key : ∀ (G : Spec R' ⟶ Z) (_ : G = Spec.map φ ≫ ι) (e : ⊤ ≤ G ⁻¹ᵁ (ι ''ᵁ ⊤)),
      G.appLE (ι ''ᵁ ⊤) ⊤ e (chartSection ι r) = (Scheme.ΓSpecIso R').inv (φ r) := by
    rintro G rfl e
    have e' : ⊤ ≤ Spec.map φ ⁻¹ᵁ ι ⁻¹ᵁ ι ''ᵁ ⊤ := e
    show ((Spec.map φ).appLE (ι ⁻¹ᵁ ι ''ᵁ ⊤) ⊤ e') (ι.app (ι ''ᵁ ⊤) (chartSection ι r)) = _
    rw [chartSection, ← ConcreteCategory.comp_apply _ (ι.app _), Scheme.Hom.appIso_inv_app,
      ← ConcreteCategory.comp_apply, Scheme.Hom.map_appLE,
      show ∀ h, (Spec.map φ).appLE ⊤ ⊤ h = (Spec.map φ).appTop from
        fun _ ↦ (Spec.map φ).appLE_eq_app,
      ← ConcreteCategory.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, ConcreteCategory.comp_apply]
  exact key _ h _

/-- The map `r ↦ chartSection ι r` is injective. -/
theorem chartSection_injective : Function.Injective (chartSection ι) := by
  intro a b h
  simpa [chartSection] using congrArg (fun s ↦ (Scheme.ΓSpecIso R).hom ((ι.appIso ⊤).hom s)) h

/-- `chartSection` as a ring isomorphism. -/
def chartSectionEquiv : R ≃+* Γ(Z, ι ''ᵁ ⊤) :=
  ((Scheme.ΓSpecIso R).symm ≪≫ (ι.appIso ⊤).symm).commRingCatIsoToRingEquiv

/-- The ring isomorphism `chartSectionEquiv ι` sends `r` to `chartSection ι r`. -/
theorem chartSectionEquiv_apply (r : R) : chartSectionEquiv ι r = chartSection ι r := rfl

end Charts

variable (k : Type u) [Field k]

/-- The origin of the affine line. -/
def origin : line k := ⟨Ideal.span {X}, (Ideal.span_singleton_prime X_ne_zero).mpr prime_X⟩

/-- The coordinate `t` on the `n`-th chart of the line with infinitely many origins. -/
def baseCoord (n : ℕ) : Γ(base k, baseChart k n) := chartSection (baseι k n) (X : k[X])

/-- The coordinate `t` on the `n`-th chart is nonzero. -/
theorem baseCoord_ne_zero (n : ℕ) : baseCoord k n ≠ 0 := by
  intro h
  rw [baseCoord, ← chartSectionEquiv_apply] at h
  exact X_ne_zero ((map_eq_zero_iff _ (chartSectionEquiv (baseι k n)).injective).mp h)

/-- The ideal generated by `X` in `k[X]` is maximal. -/
private theorem isMaximal_span_X : (Ideal.span {(X : k[X])}).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible irreducible_X

/-- The coordinate `t` on the `n`-th chart generates a maximal ideal of its ring of sections. -/
theorem isMaximal_span_baseCoord (n : ℕ) : (Ideal.span {baseCoord k n}).IsMaximal := by
  have h : Ideal.span {baseCoord k n} =
      (Ideal.span {(X : k[X])}).map (chartSectionEquiv (baseι k n)) := by
    rw [Ideal.map_span, Set.image_singleton, chartSectionEquiv_apply, baseCoord]
  rw [h]
  have := isMaximal_span_X k
  exact Ideal.map_isMaximal_of_equiv _

/-- The coordinate `t` on the `n`-th chart vanishes at the `n`-th origin. -/
theorem origin_notMem_basicOpen_baseCoord (n : ℕ) :
    baseι k n (origin k) ∉ (base k).basicOpen (baseCoord k n) := by
  rw [baseCoord, mem_basicOpen_chartSection]
  exact fun h ↦ h (Ideal.subset_span rfl)

/-- The point `(0, 1)` of the plane, the generic point of the line `x = 0`. -/
def specialPoint0 : plane k :=
  ⟨Ideal.span {MvPolynomial.X 0}, (Ideal.span_singleton_prime (MvPolynomial.X_ne_zero 0)).mpr
    MvPolynomial.X_prime⟩

/-- The variable `y` does not lie in the ideal generated by the variable `x`. -/
private theorem X_one_notMem_span_X_zero :
    (MvPolynomial.X 1 : planeRing k) ∉ Ideal.span {MvPolynomial.X 0} := by
  rw [Ideal.mem_span_singleton, MvPolynomial.X_dvd_X]
  decide

/-- The coordinate `x` on the `n`-th chart of the total space. -/
def totalCoordX (n : ℕ) : Γ(total k, totalChart k n) :=
  chartSection (totalι k n) (MvPolynomial.X 0 : planeRing k)

/-- The coordinate `y` on the `n`-th chart of the total space. -/
def totalCoordY (n : ℕ) : Γ(total k, totalChart k n) :=
  chartSection (totalι k n) (MvPolynomial.X 1 : planeRing k)

/-- The `n`-th chart of the total space lies over the `n`-th chart of the base. -/
theorem totalChart_le (n : ℕ) : totalChart k n ≤ totalMap k ⁻¹ᵁ baseChart k n :=
  (preimage_baseChart k n).ge

/-- **On the `n`-th chart, `t = x ^ (n + 1) y`.** -/
theorem totalMap_appLE_baseCoord (n : ℕ) :
    (totalMap k).appLE (baseChart k n) (totalChart k n) (totalChart_le k n) (baseCoord k n) =
      totalCoordX k n ^ (n + 1) * totalCoordY k n := by
  rw [baseCoord, appLE_chartSection (baseι k n) (totalι k n) (totalMap k)
    (CommRingCat.ofHom (planeMap k (n + 1)).toRingHom) (by rw [totalι_totalMap, chartMap]),
    totalCoordX, totalCoordY, ← chartSectionEquiv_apply, ← chartSectionEquiv_apply,
    ← chartSectionEquiv_apply, ← map_pow, ← map_mul]
  congr 1
  simp [planeMap]

/-- The coordinate `x` vanishes at the special point of the `n`-th chart. -/
theorem specialPoint_notMem_basicOpen_totalCoordX (n : ℕ) :
    totalι k n (specialPoint0 k) ∉ (total k).basicOpen (totalCoordX k n) := by
  rw [totalCoordX, mem_basicOpen_chartSection]
  exact fun h ↦ h (Ideal.subset_span rfl)

/-- The coordinate `y` does not vanish at the special point of the `n`-th chart. -/
theorem specialPoint_mem_basicOpen_totalCoordY (n : ℕ) :
    totalι k n (specialPoint0 k) ∈ (total k).basicOpen (totalCoordY k n) := by
  rw [totalCoordY, mem_basicOpen_chartSection]
  exact X_one_notMem_span_X_zero k

/-- The map of spectra induced by `t ↦ x ^ (n + 1) y` sends the point `(0, 1)` of the plane to the
origin of the line. -/
theorem specMap_planeMap_specialPoint0 (n : ℕ) :
    Spec.map (CommRingCat.ofHom (planeMap k (n + 1)).toRingHom) (specialPoint0 k) = origin k := by
  apply PrimeSpectrum.ext
  show Ideal.comap (planeMap k (n + 1)).toRingHom (Ideal.span {MvPolynomial.X 0}) =
    Ideal.span {X}
  have := isMaximal_span_X k
  have : (Ideal.span {(MvPolynomial.X 0 : planeRing k)}).IsPrime := (specialPoint0 k).isPrime
  refine (Ideal.IsMaximal.eq_of_le inferInstance (Ideal.IsPrime.ne_top ?_) ?_).symm
  · exact Ideal.comap_isPrime _ _
  · rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    show planeMap k (n + 1) X ∈ _
    rw [planeMap, Polynomial.aeval_X, Ideal.mem_span_singleton, pow_succ,
      mul_comm _ (MvPolynomial.X 0), mul_assoc]
    exact dvd_mul_right _ _

/-- The special point of the `n`-th chart of the total space maps to the `n`-th origin. -/
theorem totalMap_specialPoint (n : ℕ) :
    totalMap k (totalι k n (specialPoint0 k)) = baseι k n (origin k) := by
  rw [← Scheme.Hom.comp_apply, totalι_totalMap, chartMap, Scheme.Hom.comp_apply,
    specMap_planeMap_specialPoint0]

/-- **The special point is a generic point of its fibre.** -/
theorem eq_specialPoint_of_specializes (n : ℕ) (a : total k)
    (ha : a ⤳ totalι k n (specialPoint0 k))
    (hfa : totalMap k a = totalMap k (totalι k n (specialPoint0 k))) :
    a = totalι k n (specialPoint0 k) := by
  obtain ⟨a₀, rfl⟩ : a ∈ Set.range (totalι k n) :=
    ha.mem_open (totalι k n).isOpenEmbedding.isOpen_range ⟨_, rfl⟩
  have hle : a₀.asIdeal ≤ Ideal.span {MvPolynomial.X 0} :=
    (PrimeSpectrum.le_iff_specializes a₀ (specialPoint0 k)).mpr
      ((totalι k n).isOpenEmbedding.isInducing.specializes_iff.mp ha)
  rw [totalMap_specialPoint, ← Scheme.Hom.comp_apply, totalι_totalMap, chartMap,
    Scheme.Hom.comp_apply] at hfa
  have h₀ := congrArg PrimeSpectrum.asIdeal ((baseι k n).isOpenEmbedding.injective hfa)
  change Ideal.comap (planeMap k (n + 1)).toRingHom a₀.asIdeal = Ideal.span {X} at h₀
  have hX : planeMap k (n + 1) X ∈ a₀.asIdeal := by
    show X ∈ Ideal.comap (planeMap k (n + 1)).toRingHom a₀.asIdeal
    rw [h₀]
    exact Ideal.subset_span rfl
  rw [planeMap, Polynomial.aeval_X] at hX
  have hX0 : MvPolynomial.X 0 ∈ a₀.asIdeal := by
    rcases a₀.isPrime.mem_or_mem hX with h | h
    · exact a₀.isPrime.mem_of_pow_mem _ h
    · exact (X_one_notMem_span_X_zero k (hle h)).elim
  congr 1
  exact PrimeSpectrum.ext (le_antisymm hle ((Ideal.span_singleton_le_iff_mem _).mpr hX0))

/-- **At the special point, `t` vanishes to order `n + 1` along `x`.** In the local ring at the
special point of the `n`-th chart, the pullback of `t` is `a ^ (n + 1) * c` with `a` in the
maximal ideal and `c` a unit (namely `a = x` and `c = y`). Stated at any point `x'` equal to the
special point, so that it can be transported. -/
theorem exists_germ_totalMap_baseCoord (n : ℕ) (x' : total k)
    (hx' : x' = totalι k n (specialPoint0 k)) (hxU : x' ∈ totalMap k ⁻¹ᵁ baseChart k n) :
    ∃ a c : (total k).presheaf.stalk x', a ∈ IsLocalRing.maximalIdeal _ ∧ IsUnit c ∧
      (total k).presheaf.germ _ x' hxU ((totalMap k).app (baseChart k n) (baseCoord k n)) =
        a ^ (n + 1) * c := by
  subst hx'
  have hmem := mem_totalChart k n (specialPoint0 k)
  refine ⟨(total k).presheaf.germ _ _ hmem (totalCoordX k n),
    (total k).presheaf.germ _ _ hmem (totalCoordY k n), ?_, ?_, ?_⟩
  · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← Scheme.mem_basicOpen _ _ _ hmem]
    exact specialPoint_notMem_basicOpen_totalCoordX k n
  · rw [← Scheme.mem_basicOpen _ _ _ hmem]
    exact specialPoint_mem_basicOpen_totalCoordY k n
  · rw [← map_pow, ← map_mul, ← totalMap_appLE_baseCoord, Scheme.Hom.appLE,
      ConcreteCategory.comp_apply, TopCat.Presheaf.germ_res_apply]

end AlgebraicGeometry.ReducedFibreCurveCounterexample
