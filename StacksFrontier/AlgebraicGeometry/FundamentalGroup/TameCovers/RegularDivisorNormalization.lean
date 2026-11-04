module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.Abhyankar.RegularDivisor
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameCovers.AffineNormalization
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameCovers.StandardIntegralClosure
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Properties
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcPlumbing
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.Regular
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.RegularGerm
public import StacksFrontier.AlgebraicGeometry.Curves.InseparableGenusChangeFunctionField

/-!
# The normalization of a tame cover along a regular divisor

Let `X` be a locally Noetherian scheme, `D ⊆ X` an effective Cartier divisor which is a regular
scheme and `Y ⟶ X ∖ D` finite étale, tamely ramified over `X` in codimension one. Granted
Abhyankar's lemma ([Stacks, Tag 0EYG]), the normalization `π : Y' ⟶ X` of `X` in `Y` is finite
locally free, restricts to `Y` over `X ∖ D`, `D' = π⁻¹(D)_red` is a regular effective Cartier
divisor, and étale locally `Y' ⟶ X` is a disjoint union of standard morphisms
`Spec(A[x]/(x^e - φ)) ⟶ Spec(A)` ([Stacks, Tag 0EYH]).

## Main results

* `AlgebraicGeometry.TameCovers.normalization_of_isTamelyRamifiedInCodimensionOne`: Tag 0EYH.
* `AlgebraicGeometry.TameCovers.exists_etale_chart_normalization`: the étale local structure.
* `AlgebraicGeometry.TameCovers.isFiniteLocallyFree_fromNormalization`,
  `AlgebraicGeometry.TameCovers.exists_iso_pullback_fromNormalization_ι`,
  `AlgebraicGeometry.TameCovers.isEffectiveCartierDivisor_radical_comap_fromNormalization`,
  `AlgebraicGeometry.TameCovers.isRegularLocalRing_stalk_radical_comap_fromNormalization`: the
  parts of Tag 0EYH separately.

## Implementation notes

The normalization of `X` in `Y` is Mathlib's relative normalization of `Y ⟶ X ∖ D ⟶ X`. As in the
source, the local structure is read off from the chart of Tag 0EYG: normalization commutes with
étale base change (Tag 03GV), and the integral closure of `A` in `A_φ[x]/(x^e - φ)` is
`A[x]/(x^e - φ)` (`AlgebraicGeometry.TameCovers.isIntegrallyClosedIn_localizationAway`). The
global properties then descend along the étale charts. "`D'` is a regular scheme" is spelled as
regularity of every local ring of the closed subscheme cut out by the radical of `π⁻¹(D)`.

Abhyankar's lemma itself is
`AlgebraicGeometry.exists_etale_standardTamelyRamified_of_isTamelyRamifiedInCodimensionOne`
([Stacks, Tag 0EYG]), which takes the named arguments `h0BMA` (purity for regular local rings,
[Stacks, Tag 0BMA] (1)) and `h0EYD` (tameness pulls back, [Stacks, Tag 0EYD]). These are
threaded through as hypotheses.

## References

* [Stacks Project, Tag 0EYH](https://stacks.math.columbia.edu/tag/0EYH)
* [Stacks Project, Tag 0EYG](https://stacks.math.columbia.edu/tag/0EYG)
* [Stacks Project, Tag 03GV](https://stacks.math.columbia.edu/tag/03GV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.TameCovers

/-- Componentwise integral closure: if each `χ i` has image containing every element of `B i`
integral over `A`, the same holds for the product map. -/
theorem exists_piMap_eq_of_isIntegralElem {ι : Type u} {A : CommRingCat.{u}}
    {C B : ι → CommRingCat.{u}} (ψ : ∀ i, A ⟶ C i) (χ : ∀ i, C i ⟶ B i)
    (hcl : ∀ i (b : B i), (ψ i ≫ χ i).hom.IsIntegralElem b → ∃ c, χ i c = b)
    (b : Π i, B i)
    (hb : (RingHom.pi fun i ↦ (ψ i ≫ χ i).hom).IsIntegralElem b) :
    ∃ c : Π i, C i, (RingHom.pi fun i ↦ (χ i).hom.comp (Pi.evalRingHom _ i)) c = b := by
  have hcomp : ∀ i, (b i : B i) ∈ Set.range (χ i) := by
    intro i
    obtain ⟨P, hP, hPb⟩ := hb
    refine hcl i (b i) ⟨P, hP, ?_⟩
    have := congrArg (Pi.evalRingHom _ i) hPb
    rw [Polynomial.hom_eval₂, map_zero] at this
    exact this
  choose c hc using hcomp
  exact ⟨c, funext fun i ↦ hc i⟩

/-- The standard tamely ramified morphism `Spec(A[x]/(x^e - φ)) ⟶ Spec(A)` is flat. -/
theorem flat_standardTamelyRamifiedMorphism (A : Type u) [CommRing A] (φ : A) (e : ℕ)
    [NeZero e] : Flat (standardTamelyRamifiedMorphism A φ e) := by
  show Flat (Spec.map (CommRingCat.ofHom (algebraMap A (standardTamelyRamifiedAlgebra A φ e))))
  rw [Flat.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]
  infer_instance

/-- The standard tamely ramified morphism is locally of finite presentation. -/
theorem locallyOfFinitePresentation_standardTamelyRamifiedMorphism (A : Type u) [CommRing A]
    (φ : A) (e : ℕ) : LocallyOfFinitePresentation (standardTamelyRamifiedMorphism A φ e) := by
  show LocallyOfFinitePresentation
    (Spec.map (CommRingCat.ofHom (algebraMap A (standardTamelyRamifiedAlgebra A φ e))))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation), CommRingCat.hom_ofHom,
    RingHom.finitePresentation_algebraMap]
  exact Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton _)

/-- In a cartesian square `Spec A_φ = g⁻¹(X ∖ D)`, the preimage of the support of `D` under
`g : Spec A ⟶ X` is `V(φ)`. -/
theorem preimage_support_eq_zeroLocus {X : Scheme.{u}} (D : X.IdealSheafData)
    {A : CommRingCat.{u}} (g : Spec A ⟶ X) (φ : A)
    {gU : Spec (.of (Localization.Away φ)) ⟶ (D.support.compl : X.Opens)}
    (hpb : IsPullback gU (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away φ))))
      (Scheme.Opens.ι (D.support.compl : X.Opens)) g) :
    g ⁻¹' (D.support : Set X) = PrimeSpectrum.zeroLocus {φ} := by
  have hr : Set.range (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away φ)))) =
      g ⁻¹' Set.range (Scheme.Opens.ι (D.support.compl : X.Opens)) := by
    rw [← Scheme.Pullback.range_snd]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨hpb.isoPullback.hom y, by rw [← Scheme.Hom.comp_apply, hpb.isoPullback_hom_snd]⟩
    · rintro ⟨y, rfl⟩
      exact ⟨hpb.isoPullback.inv y, by rw [← Scheme.Hom.comp_apply, hpb.isoPullback_inv_snd]⟩
  rw [Scheme.Opens.range_ι] at hr
  have hb : Set.range (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away φ)))) =
      (PrimeSpectrum.basicOpen φ : Set (PrimeSpectrum A)) :=
    PrimeSpectrum.localization_away_comap_range (Localization.Away φ) φ
  rw [hb] at hr
  have hc : (g ⁻¹' (D.support : Set X))ᶜ = (PrimeSpectrum.basicOpen φ : Set (PrimeSpectrum A)) := by
    rw [hr]; rfl
  rw [← compl_compl (g ⁻¹' (D.support : Set X)), hc, PrimeSpectrum.basicOpen_eq_zeroLocus_compl]
  exact compl_compl _

/-- The preimage of `V(φ)` under the standard morphism `Spec(A[x]/(x^e - φ)) ⟶ Spec(A)` is the
zero locus of the root. -/
theorem preimage_zeroLocus_standardTamelyRamifiedMorphism (A : Type u) [CommRing A] (φ : A)
    (e : ℕ) [NeZero e] :
    standardTamelyRamifiedMorphism A φ e ⁻¹' PrimeSpectrum.zeroLocus {φ} =
      PrimeSpectrum.zeroLocus {Abhyankar.root A φ e} := by
  show PrimeSpectrum.comap (algebraMap A (standardTamelyRamifiedAlgebra A φ e)) ⁻¹'
    PrimeSpectrum.zeroLocus {φ} = _
  rw [PrimeSpectrum.preimage_comap_zeroLocus, Set.image_singleton, algebraMap_eq_root_pow,
    PrimeSpectrum.zeroLocus_singleton_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne e))]

/-- The ideal of global sections cut out by `Spec(R/r) ⟶ Spec(R)` is generated by `r`. -/
theorem ker_appTop_specMap_quotient (R : CommRingCat.{u}) (r : R) :
    RingHom.ker (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {r})))).appTop.hom =
      Ideal.span {(Scheme.ΓSpecIso R).inv r} := by
  set κ := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {r})))
  have h : κ.appTop = (Scheme.ΓSpecIso R).hom ≫ CommRingCat.ofHom
      (Ideal.Quotient.mk (Ideal.span {r})) ≫ (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.ΓSpecIso_inv_naturality, Iso.hom_inv_id_assoc]
  let σ := (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
  have hσ : ∀ a, σ a = (Scheme.ΓSpecIso R).hom a := fun _ ↦ rfl
  show RingHom.ker κ.appTop.hom = Ideal.span {σ.symm r}
  ext a
  rw [RingHom.mem_ker, h, Ideal.mem_span_singleton]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
  have key : σ.symm r ∣ a ↔ r ∣ σ a :=
    ⟨fun hd ↦ by simpa using map_dvd σ hd, fun hd ↦ by simpa using map_dvd σ.symm hd⟩
  rw [key, hσ, ← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
  exact ⟨fun ha ↦ by
    simpa using congrArg (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ Ideal.span {r}))).hom.hom ha,
    fun ha ↦ by rw [ha, map_zero]⟩

/-- The kernel of `Spec(R/r) ⟶ Spec(R)` is an effective Cartier divisor when `r` is a
nonzerodivisor. -/
theorem isEffectiveCartierDivisor_ker_specMap_quotient (R : CommRingCat.{u}) (r : R)
    (hr : r ∈ nonZeroDivisors R) :
    Stacks.Divisors.IsEffectiveCartierDivisor
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {r})))).ker := by
  let σ := (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
  rw [Scheme.ker_of_isAffine, ker_appTop_specMap_quotient]
  refine Stacks.Divisors.isEffectiveCartierDivisor_ofIdealTop_span _ ?_
  refine isRegular_iff_mem_nonZeroDivisors.mpr (mem_nonZeroDivisors_iff_right.mpr fun x hx ↦ ?_)
  change x * σ.symm r = 0 at hx
  have h1 : σ x * r = 0 := by simpa using congrArg σ hx
  have h2 := (mem_nonZeroDivisors_iff_right.mp hr) _ h1
  simpa using congrArg σ.symm h2

/-- `Spec(R/r) ⟶ Spec(R)` is a closed immersion. -/
private theorem isClosedImmersion_specMap_quotient (R : CommRingCat.{u}) (r : R) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {r})))) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- The support of the kernel of `Spec(R/r) ⟶ Spec(R)` is `V(r)`. -/
theorem coe_support_ker_specMap_quotient (R : CommRingCat.{u}) (r : R) :
    ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {r})))).ker.support :
      Set (Spec R)) = PrimeSpectrum.zeroLocus {r} := by
  have := isClosedImmersion_specMap_quotient R r
  rw [Scheme.Hom.support_ker, (Spec.map _).isClosedEmbedding.isClosed_range.closure_eq]
  show Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {r}))) = _
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
    PrimeSpectrum.zeroLocus_span]

/-- The closed subscheme `Spec(R/r)` of `Spec(R)` is reduced when `R/r` is regular. -/
theorem isReduced_subscheme_ker_specMap_quotient (R : CommRingCat.{u}) (r : R)
    (hreg : IsRegularRing (R ⧸ Ideal.span {r})) :
    IsReduced
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {r})))).ker.subscheme := by
  have := isClosedImmersion_specMap_quotient R r
  have : IsReduced (Spec (CommRingCat.of (R ⧸ Ideal.span {r}))) :=
    isReduced_of_isRegular ((isRegular_spec_iff _).mpr hreg)
  exact isReduced_of_isOpenImmersion (Stacks.Divisors.closedImmersionKerIso _).inv

/-- **Effective Cartier divisors from étale charts.** If every point of `Y` lies in the image of
an étale chart `Spec R ⟶ Y` along which `I` pulls back to the divisor of a nonzerodivisor, then
`I` is an effective Cartier divisor. -/
theorem isEffectiveCartierDivisor_of_etale_charts {Y : Scheme.{u}} (I : Y.IdealSheafData)
    (h : ∀ y : Y, ∃ (R : CommRingCat.{u}) (q : Spec R ⟶ Y) (_ : Etale q) (w : Spec R)
      (_ : q w = y) (r : R) (_ : r ∈ nonZeroDivisors R),
      I.comap q = (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {r})))).ker) :
    Stacks.Divisors.IsEffectiveCartierDivisor I := by
  refine Stacks.Divisors.isEffectiveCartierDivisor_of_flat_universallyOpen_pointwise I fun y ↦ ?_
  obtain ⟨R, q, hq, w, hw, r, hr, hI⟩ := h y
  refine ⟨Spec R, q, inferInstance, inferInstance, ⟨w, hw⟩, ?_⟩
  rw [hI]
  exact isEffectiveCartierDivisor_ker_specMap_quotient R r hr

/-- **Regular closed subschemes from étale charts.** If every point of `Y` lies in the image of
an étale chart `Spec R ⟶ Y` along which `I` pulls back to `Spec(R/r)` with `R/r` regular, then
every local ring of the closed subscheme cut out by `I` is regular. -/
theorem isRegularLocalRing_stalk_of_etale_charts {Y : Scheme.{u}} (I : Y.IdealSheafData)
    (h : ∀ y : Y, ∃ (R : CommRingCat.{u}) (q : Spec R ⟶ Y) (_ : Etale q) (w : Spec R)
      (_ : q w = y) (r : R) (_ : IsRegularRing (R ⧸ Ideal.span {r})),
      I.comap q = (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {r})))).ker)
    (z : I.subscheme) : IsRegularLocalRing (I.subscheme.presheaf.stalk z) := by
  obtain ⟨R, q, hq, w, hw, r, hreg, hI⟩ := h (I.subschemeι z)
  obtain ⟨p, hp₁, hp₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := q) (g := I.subschemeι)
    w z hw
  let κ := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {r})))
  have := isClosedImmersion_specMap_quotient R r
  have hregC : IsRegular (I.comap q).subscheme := hI ▸
    ObjectProperty.prop_of_iso (P := fun Z : Scheme.{u} ↦ IsRegular Z)
      (Stacks.Divisors.closedImmersionKerIso κ) ((isRegular_spec_iff _).mpr hreg)
  have hregP : IsRegular (pullback q I.subschemeι) :=
    ObjectProperty.prop_of_iso (P := fun Z : Scheme.{u} ↦ IsRegular Z) (I.comapIso q) hregC
  have hstalk := ((isRegular_iff_regular_stalks _).mp hregP).2 p
  rwa [isRegularLocalRing_stalk_iff_of_etale (pullback.snd q I.subschemeι) p, hp₂] at hstalk

/-- Over `X ∖ D` the normalization is `Y`: the square formed by `Y ⟶ Y'`, `f`, the
normalization `π` and the inclusion of `X ∖ D` is cartesian. -/
theorem isPullback_toNormalization_ι {X : Scheme.{u}} [IsLocallyNoetherian X]
    (D : X.IdealSheafData) {Y : Scheme.{u}} (f : Y ⟶ (D.support.compl : X.Opens))
    [IsFinite f] :
    IsPullback (f ≫ Scheme.Opens.ι (D.support.compl : X.Opens)).toNormalization f
      (f ≫ Scheme.Opens.ι (D.support.compl : X.Opens)).fromNormalization
      (Scheme.Opens.ι (D.support.compl : X.Opens)) := by
  let j := Scheme.Opens.ι (D.support.compl : X.Opens)
  have sq : IsPullback (𝟙 Y) f (f ≫ j) j := by
    simpa using (IsPullback.of_id_fst (f := f)).paste_vert (IsKernelPair.id_of_mono j)
  have sq' := isPullback_normalizationMap_of_smooth (f ≫ j) j sq
  have s1 : IsPullback f.toNormalization f f.fromNormalization (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have := s1.paste_horiz sq'
  rwa [Scheme.Hom.toNormalization_normalizationMap, Category.id_comp, Category.id_comp] at this

/-- **[Stacks, Tag 0EYH] (1).** The restriction of the normalization of `X` in `Y` to `X ∖ D` is
`Y`: normalization commutes with the (smooth) base change along the open immersion, and `Y` is
integral, hence normal, over `X ∖ D`. -/
theorem exists_iso_pullback_fromNormalization_ι {X : Scheme.{u}} [IsLocallyNoetherian X]
    (D : X.IdealSheafData) {Y : Scheme.{u}} (f : Y ⟶ (D.support.compl : X.Opens))
    [IsFinite f] :
    ∃ e : pullback (f ≫ Scheme.Opens.ι (D.support.compl : X.Opens)).fromNormalization
        (Scheme.Opens.ι (D.support.compl : X.Opens)) ≅ Y,
      e.hom ≫ f = pullback.snd _ _ :=
  ⟨(isPullback_toNormalization_ι D f).isoPullback.symm,
    (isPullback_toNormalization_ι D f).isoPullback_inv_snd⟩

section Chart

variable (h0BMA : PurityAtRegularLocalRings.{u})
    (h0EYD : ∀ S : Stacks.FundamentalGroup.CodimensionOnePullbackSetup.{u},
      Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne S.U.ι S.f →
      Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne (pullback.fst S.g S.U.ι)
        S.pulledBackCover)

include h0BMA h0EYD in
/-- **The étale local structure of the normalization.** In the situation of [Stacks, Tag 0EYG],
étale locally on `X` the normalization of `X` in `Y` is a finite disjoint union of standard
morphisms `Spec(A[x]/(x^e - φ)) ⟶ Spec(A)`. The chart is the one supplied by Tag 0EYG; the
normalization is computed by smooth base change (Tag 03GV) and the integral closure of
`A` in `A_φ[x]/(x^e - φ)`. -/
theorem exists_etale_chart_normalization {X : Scheme.{u}} [IsLocallyNoetherian X]
    (D : X.IdealSheafData) (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    (hDreg : ∀ z : D.subscheme, IsRegularLocalRing (D.subscheme.presheaf.stalk z))
    {Y : Scheme.{u}} (f : Y ⟶ (D.support.compl : X.Opens)) [IsFinite f] [Etale f]
    (hf : Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne
      (Scheme.Opens.ι (D.support.compl : X.Opens)) f) (x : X) :
    ∃ (A : CommRingCat.{u}) (g : Spec A ⟶ X) (_ : Etale g) (a : Spec A) (_ : g a = x)
      (φ : A) (_ : IsNoetherianRing A) (_ : φ ∈ nonZeroDivisors A)
      (_ : IsRegularRing (A ⧸ Ideal.span {φ}))
      (gU : Spec (.of (Localization.Away φ)) ⟶ (D.support.compl : X.Opens))
      (_ : IsPullback gU (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away φ))))
        (Scheme.Opens.ι (D.support.compl : X.Opens)) g)
      (n : ℕ) (e : Fin n → ℕ) (_ : ∀ i, 0 < e i ∧ IsUnit (e i : A)),
      ∃ ι : pullback (f ≫ Scheme.Opens.ι (D.support.compl : X.Opens)).fromNormalization g ≅
          ∐ fun i ↦ Spec (.of (standardTamelyRamifiedAlgebra A φ (e i))),
        ι.hom ≫ Sigma.desc (fun i ↦ standardTamelyRamifiedMorphism A φ (e i)) =
          pullback.snd _ g := by
  obtain ⟨A, g, hg, a, hga, φ, hA, hφ, hreg, gU, -, hpb, n, e, he, ι, hι⟩ :=
    exists_etale_standardTamelyRamified_of_isTamelyRamifiedInCodimensionOne h0BMA h0EYD
      D hD hDreg f hf x
  have hne : ∀ i, NeZero (e i) := fun i ↦ ⟨(he i).1.ne'⟩
  let F := f ≫ Scheme.Opens.ι (D.support.compl : X.Opens)
  let loc := Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away φ)))
  let p : pullback f gU ⟶ Spec A := pullback.snd f gU ≫ loc
  have sq : IsPullback (pullback.fst f gU) p F g :=
    (IsPullback.of_hasPullback f gU).paste_vert hpb
  have : IsAffine (pullback f gU) := IsAffine.of_isIso ι.hom
  have sq' := isPullback_normalizationMap_of_smooth F g sq
  let Ci : Fin n → CommRingCat.{u} := fun i ↦ .of (standardTamelyRamifiedAlgebra A φ (e i))
  let Bi : Fin n → CommRingCat.{u} := fun i ↦
    .of (Localization.Away (algebraMap A (standardTamelyRamifiedAlgebra A φ (e i)) φ))
  let ψi : ∀ i, A ⟶ Ci i := fun i ↦ CommRingCat.ofHom (algebraMap _ _)
  let χi : ∀ i, Ci i ⟶ Bi i := fun i ↦ CommRingCat.ofHom (algebraMap _ _)
  let ε : ULift.{u} (Fin n) ≃ Fin n := Equiv.ulift
  let Ci' : ULift.{u} (Fin n) → CommRingCat.{u} := fun j ↦ Ci (ε j)
  let Bi' : ULift.{u} (Fin n) → CommRingCat.{u} := fun j ↦ Bi (ε j)
  let Ψ : A ⟶ CommRingCat.of (Π j, Ci' j) := CommRingCat.ofHom (RingHom.pi fun j ↦ (ψi (ε j)).hom)
  let Χ : CommRingCat.of (Π j, Ci' j) ⟶ CommRingCat.of (Π j, Bi' j) :=
    CommRingCat.ofHom (RingHom.pi fun j ↦ (χi (ε j)).hom.comp (Pi.evalRingHom _ j))
  let vC : (∐ fun i ↦ Spec (Ci i)) ≅ Spec (CommRingCat.of (Π j, Ci' j)) :=
    (Sigma.reindex ε fun i ↦ Spec (Ci i)).symm ≪≫ asIso (sigmaSpec Ci')
  let vB : (∐ fun i ↦ Spec (Bi i)) ≅ Spec (CommRingCat.of (Π j, Bi' j)) :=
    (Sigma.reindex ε fun i ↦ Spec (Bi i)).symm ≪≫ asIso (sigmaSpec Bi')
  let h : pullback f gU ⟶ ∐ fun i ↦ Spec (Ci i) := ι.hom ≫ Limits.Sigma.map fun i ↦ Spec.map (χi i)
  let q : (∐ fun i ↦ Spec (Ci i)) ⟶ Spec A := Sigma.desc fun i ↦ Spec.map (ψi i)
  have hq : vC.hom ≫ Spec.map Ψ = q := by
    refine Sigma.hom_ext _ _ fun i ↦ ?_
    obtain ⟨j, rfl⟩ := ε.surjective i
    simp only [vC, Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc,
      Sigma.ι_reindex_inv_assoc]
    show Sigma.ι (fun j ↦ Spec (Ci' j)) j ≫ sigmaSpec Ci' ≫ Spec.map Ψ = _
    rw [ι_sigmaSpec_assoc, ← Spec.map_comp, Sigma.ι_desc]
    rfl
  have hh : h ≫ vC.hom = (ι ≪≫ vB).hom ≫ Spec.map Χ := by
    simp only [h, vC, vB, Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc]
    congr 1
    refine Sigma.hom_ext _ _ fun i ↦ ?_
    obtain ⟨j, rfl⟩ := ε.surjective i
    rw [Limits.Sigma.ι_map_assoc, Sigma.ι_reindex_inv_assoc, Sigma.ι_reindex_inv_assoc]
    show Spec.map (χi (ε j)) ≫ Sigma.ι (fun j ↦ Spec (Ci' j)) j ≫ sigmaSpec Ci' =
      (Sigma.ι (fun j ↦ Spec (Bi' j)) j ≫ sigmaSpec Bi') ≫ Spec.map Χ
    rw [ι_sigmaSpec, ι_sigmaSpec, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  have hH : p = h ≫ q := by
    simp only [p, h, q, Category.assoc, ← hι]
    congr 1
    refine Sigma.hom_ext _ _ fun i ↦ ?_
    rw [Sigma.ι_desc_assoc, Limits.Sigma.ι_map_assoc, Sigma.ι_desc]
    simp only [loc, standardTamelyRamifiedCover, Scheme.Spec_map, Quiver.Hom.unop_op,
      ← Spec.map_comp]
    congr 1
    ext y
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
    exact IsLocalization.map_eq _ _
  have hclosed : ∀ i, IsIntegrallyClosedIn (standardTamelyRamifiedAlgebra A φ (e i))
      (Localization.Away (algebraMap A (standardTamelyRamifiedAlgebra A φ (e i)) φ)) := fun i ↦ by
    have := hne i
    exact isIntegrallyClosedIn_localizationAway hφ
  have hfin : ∀ j, Module.Finite A (Ci' j) := fun j ↦ by
    have := hne (ε j)
    show Module.Finite A (standardTamelyRamifiedAlgebra A φ (e (ε j)))
    infer_instance
  have hΨ : Ψ.hom.IsIntegral := by
    show (algebraMap A (Π j, Ci' j)).IsIntegral
    exact (RingHom.finite_algebraMap.mpr inferInstance).to_isIntegral
  have : IsIntegralHom (Spec.map Ψ) := IsIntegralHom.SpecMap_iff.mpr hΨ
  have : IsIntegralHom q := by rw [← hq]; infer_instance
  have hinj : Function.Injective Χ := fun c c' hcc ↦ funext fun j ↦
    (isIntegrallyClosedIn_iff.mp (hclosed (ε j))).1 (congrFun hcc j)
  have hcl : ∀ b : CommRingCat.of (Π j, Bi' j), (Ψ ≫ Χ).hom.IsIntegralElem b →
      ∃ c, Χ c = b := by
    intro b hb
    have hcomp : (Ψ ≫ Χ).hom = RingHom.pi fun j ↦ (ψi (ε j) ≫ χi (ε j)).hom :=
      RingHom.ext fun _ ↦ rfl
    rw [hcomp] at hb
    exact exists_piMap_eq_of_isIntegralElem (fun j ↦ ψi (ε j)) (fun j ↦ χi (ε j))
      (fun j b' hb' ↦ (isIntegrallyClosedIn_iff.mp (hclosed (ε j))).2
        (RingHom.IsIntegralElem.of_comp (f := (ψi (ε j)).hom) hb')) b hb
  let N := p.normalizationDesc h q hH
  have hN : IsIso N :=
    isIso_normalizationDesc_of_iso_specMap Ψ Χ hinj hcl (ι ≪≫ vB) vC h q p hh hq hH
  refine ⟨A, g, hg, a, hga, φ, hA, hφ, hreg, gU, hpb, n, e, he,
    sq'.isoPullback.symm ≪≫ asIso N, ?_⟩
  show (sq'.isoPullback.inv ≫ N) ≫ q = _
  rw [Category.assoc, Scheme.Hom.normalizationDesc_comp, IsPullback.isoPullback_inv_snd]

/-- A morphism whose base change to each member of an étale cover is a disjoint union of
morphisms with property `P` has property `P`. -/
private theorem of_etale_chart_sigmaDesc {X Y : Scheme.{u}} (π : Y ⟶ X)
    (P : MorphismProperty Scheme.{u}) [P.IsLocalAtTarget Scheme.etalePrecoverage]
    [IsZariskiLocalAtSource P] (𝒰 : X.Cover Scheme.etalePrecoverage) {n : 𝒰.I₀ → ℕ}
    {S : ∀ x, Fin (n x) → Scheme.{u}} {F : ∀ x i, S x i ⟶ 𝒰.X x}
    (ι : ∀ x, pullback π (𝒰.f x) ≅ ∐ S x)
    (hι : ∀ x, (ι x).hom ≫ Sigma.desc (F x) = pullback.snd π (𝒰.f x))
    (hF : ∀ x i, P (F x i)) : P π := by
  refine MorphismProperty.IsLocalAtTarget.of_zeroHypercover (P := P) 𝒰 fun x ↦ ?_
  rw [← hι x, P.cancel_left_of_respectsIso]
  exact IsZariskiLocalAtSource.sigmaDesc (hF x)

include h0BMA h0EYD in
/-- **[Stacks, Tag 0EYH], first assertion.** The normalization of `X` in `Y` is finite locally
free: étale locally on `X` it is a finite disjoint union of the standard finite free morphisms,
and flatness and local finite presentation are étale local on the target, while integrality
holds by construction. -/
theorem isFiniteLocallyFree_fromNormalization {X : Scheme.{u}} [IsLocallyNoetherian X]
    (D : X.IdealSheafData) (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    (hDreg : ∀ z : D.subscheme, IsRegularLocalRing (D.subscheme.presheaf.stalk z))
    {Y : Scheme.{u}} (f : Y ⟶ (D.support.compl : X.Opens)) [IsFinite f] [Etale f]
    (hf : Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne
      (Scheme.Opens.ι (D.support.compl : X.Opens)) f) :
    Stacks.Morphisms.IsFiniteLocallyFree
      (f ≫ Scheme.Opens.ι (D.support.compl : X.Opens)).fromNormalization := by
  set π := (f ≫ Scheme.Opens.ι (D.support.compl : X.Opens)).fromNormalization
  choose A g hg a hga φ hA hφ hreg gU hpb n e he ι hι using
    fun x ↦ exists_etale_chart_normalization h0BMA h0EYD
      D hD hDreg f hf x
  let 𝒰 : X.Cover Scheme.etalePrecoverage :=
    Scheme.Cover.mkOfCovers X (fun x ↦ Spec (A x)) g (fun x ↦ ⟨x, a x, hga x⟩) hg
  have : IsZariskiLocalAtSource (@Flat.{u}) := Stacks.Descent.flat_isZariskiLocalAtSource
  have : IsZariskiLocalAtSource (@LocallyOfFinitePresentation.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation.{u})
  have hflat : Flat π :=
    of_etale_chart_sigmaDesc π (@Flat) 𝒰 ι hι fun x i ↦
      have : NeZero (e x i) := ⟨(he x i).1.ne'⟩
      flat_standardTamelyRamifiedMorphism _ _ _
  have hlfp : LocallyOfFinitePresentation π :=
    of_etale_chart_sigmaDesc π (@LocallyOfFinitePresentation) 𝒰 ι hι fun x i ↦
      locallyOfFinitePresentation_standardTamelyRamifiedMorphism _ _ _
  exact (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
    π).mpr ⟨(IsFinite.iff_isIntegralHom_and_locallyOfFiniteType π).mpr
      ⟨inferInstance, inferInstance⟩, hflat, hlfp⟩

include h0BMA h0EYD in
/-- **Étale charts for the reduced preimage of `D`.** Every point of the normalization `Y'` of
`X` in `Y` has an étale neighbourhood `Spec(A[x]/(x^e - φ)) ⟶ Y'` along which
`D' = π⁻¹(D)_red` pulls back to the zero scheme of the root `x`, a nonzerodivisor with regular
quotient `A/φA`. -/
theorem exists_etale_chart_radical_comap {X : Scheme.{u}} [IsLocallyNoetherian X]
    (D : X.IdealSheafData) (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    (hDreg : ∀ z : D.subscheme, IsRegularLocalRing (D.subscheme.presheaf.stalk z))
    {Y : Scheme.{u}} (f : Y ⟶ (D.support.compl : X.Opens)) [IsFinite f] [Etale f]
    (hf : Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne
      (Scheme.Opens.ι (D.support.compl : X.Opens)) f)
    (y : (f ≫ Scheme.Opens.ι (D.support.compl : X.Opens)).normalization) :
    ∃ (R : CommRingCat.{u})
      (q : Spec R ⟶ (f ≫ Scheme.Opens.ι (D.support.compl : X.Opens)).normalization)
      (_ : Etale q) (w : Spec R) (_ : q w = y) (r : R) (_ : r ∈ nonZeroDivisors R)
      (_ : IsRegularRing (R ⧸ Ideal.span {r})),
      (D.comap (f ≫ Scheme.Opens.ι (D.support.compl : X.Opens)).fromNormalization).radical.comap q =
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {r})))).ker := by
  set π := (f ≫ Scheme.Opens.ι (D.support.compl : X.Opens)).fromNormalization
  obtain ⟨A, g, hg, a, hga, φ, hA, hφ, hreg, gU, hpb, n, e, he, ι, hι⟩ :=
    exists_etale_chart_normalization h0BMA h0EYD D hD hDreg f hf (π y)
  obtain ⟨z, hz⟩ : y ∈ Set.range (pullback.fst π g) := by
    rw [Scheme.Pullback.range_fst]; exact ⟨a, hga⟩
  obtain ⟨i, w, hw⟩ := (sigmaOpenCover
    (fun i ↦ Spec (.of (standardTamelyRamifiedAlgebra A φ (e i))))).exists_eq (ι.hom z)
  change Sigma.ι (fun i ↦ Spec (.of (standardTamelyRamifiedAlgebra A φ (e i)))) i w = _ at hw
  have : NeZero (e i) := ⟨(he i).1.ne'⟩
  let q := Sigma.ι (fun i ↦ Spec (.of (standardTamelyRamifiedAlgebra A φ (e i)))) i ≫ ι.inv ≫
    pullback.fst π g
  have hqw : q w = y := by
    show pullback.fst π g (ι.inv (Sigma.ι
      (fun i ↦ Spec (.of (standardTamelyRamifiedAlgebra A φ (e i)))) i w)) = y
    have hinv : ι.inv (ι.hom z) = z := by
      rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]; rfl
    rw [hw, hinv, hz]
  let std' : ∀ i, Spec (.of (standardTamelyRamifiedAlgebra A φ (e i))) ⟶ Spec A := fun i ↦
    Spec.map (CommRingCat.ofHom (algebraMap A (standardTamelyRamifiedAlgebra A φ (e i))) :
      A ⟶ CommRingCat.of (standardTamelyRamifiedAlgebra A φ (e i)))
  have hι' : ι.hom ≫ Sigma.desc std' = pullback.snd π g := hι
  have hqπ : ∀ t, π (q t) = g (std' i t) := by
    intro t
    have h1 : ∀ p, π (pullback.fst π g p) = g (pullback.snd π g p) := fun p ↦ by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    have h2 : ∀ u, pullback.snd π g (ι.inv u) = Sigma.desc std' u := fun u ↦ by
      rw [← hι', Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply ι.inv ι.hom, Iso.inv_hom_id]; rfl
    have h3 : Sigma.desc std' (Sigma.ι
        (fun i ↦ Spec (.of (standardTamelyRamifiedAlgebra A φ (e i)))) i t) = std' i t :=
      (Scheme.Hom.comp_apply _ _ t).symm.trans (congrArg (fun k ↦ k t) (Sigma.ι_desc std' i))
    show π (pullback.fst π g (ι.inv (Sigma.ι
      (fun i ↦ Spec (.of (standardTamelyRamifiedAlgebra A φ (e i)))) i t))) = _
    rw [h1, h2, h3]
  let r := Abhyankar.root A φ (e i)
  have hregQ : IsRegularRing (standardTamelyRamifiedAlgebra A φ (e i) ⧸ Ideal.span {r}) :=
    IsRegularRing.of_ringEquiv (Abhyankar.quotRootEquiv A φ (e i)).symm
  refine ⟨.of (standardTamelyRamifiedAlgebra A φ (e i)), q, inferInstance, w, hqw, r,
    root_mem_nonZeroDivisors_of_mem_nonZeroDivisors hφ, hregQ, ?_⟩
  refine Scheme.IdealSheafData.eq_of_isReduced_subscheme_of_support_eq _ _
    (Scheme.IdealSheafData.isReduced_subscheme_comap _ q inferInstance)
    (isReduced_subscheme_ker_specMap_quotient
      (CommRingCat.of (standardTamelyRamifiedAlgebra A φ (e i))) r hregQ)
    (TopologicalSpace.Closeds.ext ?_)
  rw [coe_support_ker_specMap_quotient (CommRingCat.of (standardTamelyRamifiedAlgebra A φ (e i))) r]
  rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
    Scheme.IdealSheafData.support_radical, Scheme.IdealSheafData.support_comap,
    TopologicalSpace.Closeds.coe_preimage]
  have hcomp : q ⁻¹' (π ⁻¹' (D.support : Set X)) =
      std' i ⁻¹' (g ⁻¹' (D.support : Set X)) := by
    ext t
    simp only [Set.mem_preimage, hqπ]
  rw [hcomp, preimage_support_eq_zeroLocus D g φ hpb]
  have hstd := preimage_zeroLocus_standardTamelyRamifiedMorphism (↑A) φ (e i)
  change std' i ⁻¹' PrimeSpectrum.zeroLocus {φ} = _ at hstd
  rw [hstd]

include h0BMA h0EYD in
/-- **[Stacks, Tag 0EYH] (2).** `D' = π⁻¹(D)_red` is an effective Cartier divisor on the
normalization `Y'` of `X` in `Y`. -/
theorem isEffectiveCartierDivisor_radical_comap_fromNormalization {X : Scheme.{u}}
    [IsLocallyNoetherian X] (D : X.IdealSheafData)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    (hDreg : ∀ z : D.subscheme, IsRegularLocalRing (D.subscheme.presheaf.stalk z))
    {Y : Scheme.{u}} (f : Y ⟶ (D.support.compl : X.Opens)) [IsFinite f] [Etale f]
    (hf : Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne
      (Scheme.Opens.ι (D.support.compl : X.Opens)) f) :
    Stacks.Divisors.IsEffectiveCartierDivisor
      (D.comap (f ≫ Scheme.Opens.ι (D.support.compl : X.Opens)).fromNormalization).radical :=
  isEffectiveCartierDivisor_of_etale_charts _ fun y ↦ by
    obtain ⟨R, q, hq, w, hw, r, hr, -, hI⟩ :=
      exists_etale_chart_radical_comap h0BMA h0EYD D hD hDreg f hf y
    exact ⟨R, q, hq, w, hw, r, hr, hI⟩

include h0BMA h0EYD in
/-- **[Stacks, Tag 0EYH] (3).** `D' = π⁻¹(D)_red` is a regular scheme: every local ring of the
closed subscheme `D'` of the normalization `Y'` is regular. -/
theorem isRegularLocalRing_stalk_radical_comap_fromNormalization {X : Scheme.{u}}
    [IsLocallyNoetherian X] (D : X.IdealSheafData)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    (hDreg : ∀ z : D.subscheme, IsRegularLocalRing (D.subscheme.presheaf.stalk z))
    {Y : Scheme.{u}} (f : Y ⟶ (D.support.compl : X.Opens)) [IsFinite f] [Etale f]
    (hf : Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne
      (Scheme.Opens.ι (D.support.compl : X.Opens)) f)
    (z : (D.comap (f ≫ Scheme.Opens.ι
      (D.support.compl : X.Opens)).fromNormalization).radical.subscheme) :
    IsRegularLocalRing
      ((D.comap (f ≫ Scheme.Opens.ι
        (D.support.compl : X.Opens)).fromNormalization).radical.subscheme.presheaf.stalk z) :=
  isRegularLocalRing_stalk_of_etale_charts _ (fun y ↦ by
    obtain ⟨R, q, hq, w, hw, r, -, hreg, hI⟩ :=
      exists_etale_chart_radical_comap h0BMA h0EYD D hD hDreg f hf y
    exact ⟨R, q, hq, w, hw, r, hreg, hI⟩) z

include h0BMA h0EYD in
/-- **Stacks Project, Tag 0EYH.** In the situation of Abhyankar's lemma for a regular divisor
([Stacks, Tag 0EYG]: `X` locally Noetherian, `D ⊆ X` an effective Cartier divisor which is a
regular scheme, `Y ⟶ X ∖ D` finite étale and tamely ramified over `X` in codimension one), the
normalization `π : Y' ⟶ X` of `X` in `Y` is finite locally free and
1. the restriction of `Y'` to `X ∖ D` is isomorphic to `Y`,
2. `D' = π⁻¹(D)_red` is an effective Cartier divisor on `Y'`, and
3. `D'` is a regular scheme.
Moreover, étale locally on `X` the morphism `Y' ⟶ X` is a finite disjoint union of morphisms
`Spec(A[x]/(x^e - φ)) ⟶ Spec(A)` with `A` Noetherian, `φ ∈ A` a nonzerodivisor with `A/φA`
regular and `e ≥ 1` invertible in `A`.

The arguments `h0BMA` ([Stacks, Tag 0BMA] (1)) and `h0EYD` ([Stacks, Tag 0EYD]) are those of
Abhyankar's lemma, [Stacks, Tag 0EYG]. -/
theorem normalization_of_isTamelyRamifiedInCodimensionOne {X : Scheme.{u}}
    [IsLocallyNoetherian X] (D : X.IdealSheafData)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    (hDreg : ∀ z : D.subscheme, IsRegularLocalRing (D.subscheme.presheaf.stalk z))
    {Y : Scheme.{u}} (f : Y ⟶ (D.support.compl : X.Opens)) [IsFinite f] [Etale f]
    (hf : Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne
      (Scheme.Opens.ι (D.support.compl : X.Opens)) f) :
    Stacks.Morphisms.IsFiniteLocallyFree
        (f ≫ Scheme.Opens.ι (D.support.compl : X.Opens)).fromNormalization ∧
      (∃ e : pullback (f ≫ Scheme.Opens.ι (D.support.compl : X.Opens)).fromNormalization
          (Scheme.Opens.ι (D.support.compl : X.Opens)) ≅ Y,
        e.hom ≫ f = pullback.snd _ _) ∧
      Stacks.Divisors.IsEffectiveCartierDivisor
        (D.comap (f ≫ Scheme.Opens.ι (D.support.compl : X.Opens)).fromNormalization).radical ∧
      (∀ z : (D.comap (f ≫ Scheme.Opens.ι
          (D.support.compl : X.Opens)).fromNormalization).radical.subscheme,
        IsRegularLocalRing ((D.comap (f ≫ Scheme.Opens.ι
          (D.support.compl : X.Opens)).fromNormalization).radical.subscheme.presheaf.stalk z)) ∧
      ∀ x : X, ∃ (A : CommRingCat.{u}) (g : Spec A ⟶ X) (_ : Etale g) (a : Spec A)
        (_ : g a = x) (φ : A) (_ : IsNoetherianRing A) (_ : φ ∈ nonZeroDivisors A)
        (_ : IsRegularRing (A ⧸ Ideal.span {φ})) (n : ℕ) (e : Fin n → ℕ)
        (_ : ∀ i, 0 < e i ∧ IsUnit (e i : A)),
        ∃ ι : pullback (f ≫ Scheme.Opens.ι (D.support.compl : X.Opens)).fromNormalization g ≅
            ∐ fun i ↦ Spec (.of (standardTamelyRamifiedAlgebra A φ (e i))),
          ι.hom ≫ Sigma.desc (fun i ↦ standardTamelyRamifiedMorphism A φ (e i)) =
            pullback.snd _ g :=
  ⟨isFiniteLocallyFree_fromNormalization h0BMA h0EYD D hD hDreg f hf,
    exists_iso_pullback_fromNormalization_ι D f,
    isEffectiveCartierDivisor_radical_comap_fromNormalization h0BMA h0EYD D hD hDreg f hf,
    isRegularLocalRing_stalk_radical_comap_fromNormalization h0BMA h0EYD D hD hDreg f hf,
    fun x ↦ by
      obtain ⟨A, g, hg, a, hga, φ, hA, hφ, hreg, -, -, n, e, he, ι, hι⟩ :=
        exists_etale_chart_normalization h0BMA h0EYD D hD hDreg f hf x
      exact ⟨A, g, hg, a, hga, φ, hA, hφ, hreg, n, e, he, ι, hι⟩⟩

end Chart

end AlgebraicGeometry.TameCovers
