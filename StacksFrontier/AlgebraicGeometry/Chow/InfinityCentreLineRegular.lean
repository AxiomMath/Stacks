module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.CriteriaLocalizedSituation
public import StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreLineAtInfinity
public import StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreLineRegularAlgebra
public import StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreModification
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.RegularImmersionFpqc
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.RegularImmersion
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectClosedImmersion
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.CodimLocal

/-!
# The projective line of a regularly immersed centre inside the blowup at infinity

Let `i : Z ⟶ X` be a closed immersion which is regular of codimension `r`, let `b : W ⟶ 𝐏¹_X` be
the blowup of `𝐏¹_X` in the centre `∞(Z)` (Stacks 0FBG) and `i' : 𝐏¹_Z ⟶ W` the closed immersion
of Stacks 0FE9 (`Stacks.Chow.lineToBlowupAtInfinity`). Then `i'` is again a regular immersion of
codimension `r`, so that `Q = i'_*𝒪_{𝐏¹_Z}` is a perfect object of `D(𝒪_W)` and its Chern classes
are defined (the claim in the proof of Stacks 0FEG).

The question is local on `W`. Over the open `𝐀¹_X ∪ 𝐏¹_{X ∖ Z}` of `𝐏¹_X` the blowup `b` is an
isomorphism, and there `i'` is the base change `𝐏¹_Z ⟶ 𝐏¹_X` of `i` along the flat morphism
`𝐏¹_X ⟶ X`. The remaining points of `𝐏¹_Z` lie on the divisor at infinity; over an affine open
`Spec A ⊆ X` on which `Z` is cut out by a regular sequence `f₁, …, f_r` they map into the chart
`D₊(S) = Spec A[s][J/s]`, `J = (f, s)`, of `W` (they avoid the strict transform `X'`). On that
chart `i'` is cut out by the ratios `yᵢ = fᵢ/s`: the composite `A[s] ⟶ A[s][J/s] ⟶ 𝒪(𝐏¹_Z)` is the
surjection onto `(A/I)[s]`, and the ratios generate the kernel of every such map
(`Stacks.Chow.ker_eq_span_infinityChartRatio`). They form a regular sequence
(`Stacks.Chow.isWeaklyRegular_infinityChartRatio`).

## Main results

* `Stacks.Chow.isRegularClosedImmersionOfCodim_lineToBlowupAtInfinity`: `i'` is a regular closed
  immersion of codimension `r`.
* `Stacks.Chow.perfect_lineToBlowupAtInfinity` and
  `Stacks.Chow.isPerfect_pushforward_lineToBlowupAtInfinity`: `i'` is a perfect morphism and
  `i'_*𝒪_{𝐏¹_Z}` is a perfect object of `D(𝒪_W)`.
* `Stacks.Chow.hasDefinedChernClasses_pushforward_lineToBlowupAtInfinity`: for `X` locally of
  finite type over the base of chapter 42 and quasi-compact, or with quasi-compact irreducible
  components, the Chern classes of `i'_*𝒪_{𝐏¹_Z}` are defined.

## Implementation notes

As for `Stacks.Chow.lineToBlowupAtInfinity`, the source of `i'` is the projective line of the
closed subscheme `V(ker i)`, which `Z` is isomorphic to through `i`. Regularity is read in the
affine-open form of Stacks 063G
(`Stacks.AlgebraicGeometry.RegularIdealSheaf.isRegularClosedImmersionOfCodim_iff_kerGeneratedBy`).
On the chart `D₊(S)` the source computes the chart ring as `A[s, y]/(sy - f)` (Stacks 0BIQ) and
notes that `y, sy - f` is a regular sequence there; here the chart ring is the subring
`A[s][J/s]` of `A[s, 1/s]` and the regularity of `y` is checked inside `A[s, 1/s]`, which needs of
`f` only that it is quasi-regular (Stacks 061M) and that each `fₖ₊₁` is a nonzerodivisor modulo
`(f₁, …, fₖ)`.

## References

* [Stacks Project, Tag 0FEG](https://stacks.math.columbia.edu/tag/0FEG)
* [Stacks Project, Tag 0FE9](https://stacks.math.columbia.edu/tag/0FE9)
* [Stacks Project, Tag 0FBG](https://stacks.math.columbia.edu/tag/0FBG)
* [Stacks Project, Tag 063G](https://stacks.math.columbia.edu/tag/063G)
* [Stacks Project, Tag 068C](https://stacks.math.columbia.edu/tag/068C)
* [Stacks Project, Tag 0GUE](https://stacks.math.columbia.edu/tag/0GUE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The affine-open condition, read on an open subscheme -/

/-- The condition "a regular sequence of length `c`" on finite families is stable under flat ring
maps. -/
theorem regularSequenceOfLength_map_of_flat (c : ℕ) {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (hφ : φ.Flat) {r : ℕ} (f : Fin r → A)
    (hf : r = c ∧ RingTheory.Sequence.IsWeaklyRegular A (List.ofFn f)) :
    r = c ∧ RingTheory.Sequence.IsWeaklyRegular B (List.ofFn fun i => φ (f i)) :=
  ⟨hf.1, Stacks.AlgebraicGeometry.isWeaklyRegular_ofFn_map_of_flat φ hφ f hf.2⟩

/-- **The affine-open condition at a point, from an open neighbourhood.** Let `j : Z ⟶ X` be a
closed immersion and `O ⊆ X` an open such that the restriction of `j` over `O` satisfies the
affine-open condition `KerGeneratedBy Seq`. Then around every point of `O` in the image of `j`
some affine open of `X` carries a `Seq`-family generating the kernel of `j` on sections there. -/
theorem exists_affineOpen_ker_eq_span_of_kerGeneratedBy_pullback
    {Seq : ∀ {A : Type u} [CommRing A] {r : ℕ}, (Fin r → A) → Prop}
    (hSeq : ∀ {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B), φ.Flat →
      ∀ {r : ℕ} (f : Fin r → A), Seq f → Seq fun i => φ (f i))
    {Z X : Scheme.{u}} (j : Z ⟶ X) [IsClosedImmersion j] (O : X.Opens)
    (hO : KerGeneratedBy Seq (pullback.snd j O.ι)) {x : X} (hxO : x ∈ O)
    (hx : x ∈ Set.range j.base) :
    ∃ (U : X.affineOpens) (_ : x ∈ (U : Set X)) (r : ℕ) (f : Fin r → Γ(X, U.1)),
      RingHom.ker (j.app U.1).hom = Ideal.span (Set.range f) ∧ Seq f := by
  have hx' : (⟨x, hxO⟩ : O) ∈ closure (Set.range (pullback.snd j O.ι).base) :=
    subset_closure (by rw [Scheme.Pullback.range_snd]; exact hx)
  obtain ⟨V, hxV, r, f, hker, hseq⟩ := hO ⟨x, hxO⟩ hx'
  let e := (O.ι.appIso V.1).symm.commRingCatIsoToRingEquiv
  refine ⟨⟨O.ι ''ᵁ V.1, V.2.image_of_isOpenImmersion O.ι⟩, ⟨⟨x, hxO⟩, hxV, rfl⟩, r,
    fun a => e (f a), ?_, seq_of_ringEquiv hSeq e f hseq⟩
  have hk := Scheme.ker_ideal_of_isPullback_of_isOpenImmersion j (pullback.snd j O.ι)
    (pullback.fst j O.ι) O.ι (IsPullback.of_hasPullback j O.ι).flip V
  rw [Scheme.Hom.ker_apply, Scheme.Hom.ker_apply, hker,
    show ((O.ι.appIso V.1).inv).hom = e.toRingHom from rfl] at hk
  have hh := congrArg (Ideal.map e.toRingHom) hk.symm
  rwa [Ideal.map_span, ← Set.range_comp,
    Ideal.map_comap_of_surjective e.toRingHom e.surjective] at hh

variable {X : Scheme.{u}} (ℐ : X.IdealSheafData)

/-! ### Away from the divisor at infinity -/

/-- **Over `𝐀¹_X ∪ 𝐏¹_{X ∖ Z}`, `𝐏¹_Z ⟶ W` is regular of codimension `c` when `Z ⟶ X` is.** The
restriction of `𝐏¹_Z ⟶ W` over the preimage of that open in `W` satisfies the affine-open condition
for regular sequences of length `c`. -/
theorem kerGeneratedBy_pullback_isomorphismLocusAtInfinity {c : ℕ}
    (h : IsRegularClosedImmersionOfCodim ℐ.subschemeι c) :
    KerGeneratedBy
      (fun {A} _ {r} f => r = c ∧ RingTheory.Sequence.IsWeaklyRegular A (List.ofFn f))
      (pullback.snd (lineToBlowupAtInfinity ℐ)
        (blowupAtInfinityToLine ℐ ⁻¹ᵁ isomorphismLocusAtInfinity ℐ).ι) := by
  have hj : IsRegularClosedImmersionOfCodim (projectiveLineBaseChange ℐ.subschemeι) c :=
    IsRegularClosedImmersionOfCodim.of_isPullback
      (isPullback_projectiveLineBaseChange ℐ.subschemeι) h
  have : IsIso (blowupAtInfinityToLine ℐ ∣_ isomorphismLocusAtInfinity ℐ) :=
    isIso_blowupAtInfinityToLine_restrict ℐ
  have hsq := (IsPullback.of_hasPullback (lineToBlowupAtInfinity ℐ)
    (blowupAtInfinityToLine ℐ ⁻¹ᵁ isomorphismLocusAtInfinity ℐ).ι).paste_vert
    (isPullback_morphismRestrict (blowupAtInfinityToLine ℐ) (isomorphismLocusAtInfinity ℐ)).flip
  rw [lineToBlowupAtInfinity_comp] at hsq
  have hP := IsRegularClosedImmersionOfCodim.of_isPullback hsq hj
  have : IsClosedImmersion (pullback.snd (lineToBlowupAtInfinity ℐ)
      (blowupAtInfinityToLine ℐ ⁻¹ᵁ isomorphismLocusAtInfinity ℐ).ι ≫
        (blowupAtInfinityToLine ℐ ∣_ isomorphismLocusAtInfinity ℐ)) :=
    MorphismProperty.of_isPullback hsq inferInstance
  rw [isRegularClosedImmersionOfCodim_iff_kerGeneratedBy] at hP
  exact (kerGeneratedBy_comp_iso_iff (regularSequenceOfLength_map_of_flat c)
    _ (asIso (blowupAtInfinityToLine ℐ ∣_ isomorphismLocusAtInfinity ℐ))).mp hP

/-! ### On the chart `D₊(S)` -/

/-- The blowup map sends `𝐏¹_Z ⟶ W` to the base change `𝐏¹_Z ⟶ 𝐏¹_X`, pointwise. -/
private theorem blowupAtInfinityToLine_lineToBlowupAtInfinity_apply (p : relativeProjectiveLine
    ℐ.subscheme) : blowupAtInfinityToLine ℐ (lineToBlowupAtInfinity ℐ p) =
      projectiveLineBaseChange ℐ.subschemeι p := by
  rw [← Scheme.Hom.comp_apply, lineToBlowupAtInfinity_comp]

/-- A point of `𝐏¹_Z` lies over the chart `D₊(S)` of `W` iff its image in `𝐏¹_X` lies in the chart
at infinity over `U`. -/
private theorem lineToBlowupAtInfinity_mem_range_chartS_iff (U : X.affineOpens)
    (p : relativeProjectiveLine ℐ.subscheme) :
    lineToBlowupAtInfinity ℐ p ∈ Set.range (blowupAtInfinityChartS ℐ U) ↔
      projectiveLineBaseChange ℐ.subschemeι p ∈ (infinityChartAffineOpen U).1 := by
  have hbp := blowupAtInfinityToLine_lineToBlowupAtInfinity_apply ℐ p
  exact ⟨fun hw => hbp ▸ blowupAtInfinityToLine_mem_of_mem_range_chartS ℐ U hw,
    fun hq => (mem_range_blowupAtInfinityChartS_iff_notMem ℐ U _ (hbp ▸ hq)).mpr
      (lineToBlowupAtInfinity_notMem_support_strictTransformIdealAtInfinity ℐ p)⟩

/-- `𝐏¹_Z` meets the chart at infinity over `U` exactly where its image in `W` meets `D₊(S)`. -/
theorem preimage_opensRange_infinityChartOver_eq (U : X.affineOpens) :
    projectiveLineBaseChange ℐ.subschemeι ⁻¹ᵁ (infinityChartOver U).opensRange =
      lineToBlowupAtInfinity ℐ ⁻¹ᵁ (blowupAtInfinityChartS ℐ U).opensRange := by
  ext p
  have hmem : ∀ q, q ∈ (infinityChartOver U).opensRange ↔ q ∈ (infinityChartAffineOpen U).1 :=
    fun q => ⟨fun ⟨a, ha⟩ => ⟨a, trivial, ha⟩, fun ⟨a, _, ha⟩ => ⟨a, ha⟩⟩
  change projectiveLineBaseChange ℐ.subschemeι p ∈ (infinityChartOver U).opensRange ↔
    lineToBlowupAtInfinity ℐ p ∈ Set.range (blowupAtInfinityChartS ℐ U)
  rw [hmem, lineToBlowupAtInfinity_mem_range_chartS_iff]

/-- **`𝐏¹_Z ∩ D₊(S)` is `𝐏¹_Z` over the chart at infinity.** The part of `𝐏¹_Z` over the chart
`D₊(S) = Spec A[s][J/s]` of `W`, mapped to `Spec A[s]`, is the base change of `𝐏¹_Z ⟶ 𝐏¹_X` along
the chart at infinity over `U`. -/
theorem isPullback_lineToBlowupAtInfinity_chartS (U : X.affineOpens) :
    IsPullback
      (pullback.snd (lineToBlowupAtInfinity ℐ) (blowupAtInfinityChartS ℐ U) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap (Polynomial Γ(X, U.1)) (infinityChartAlgebra (ℐ.ideal U)))))
      (pullback.fst (lineToBlowupAtInfinity ℐ) (blowupAtInfinityChartS ℐ U))
      (infinityChartOver U) (projectiveLineBaseChange ℐ.subschemeι) := by
  refine IsOpenImmersion.isPullback _ _ _ _ ?_ ?_
  · rw [Category.assoc, ← blowupAtInfinityPolyChart_comp ℐ U Polynomial.X
      (X_mem_infinityChartIdeal _), ← pullback.condition_assoc, lineToBlowupAtInfinity_comp]
  · rw [preimage_opensRange_infinityChartOver_eq]
    ext p
    change _ ↔ p ∈ Set.range (pullback.fst (lineToBlowupAtInfinity ℐ)
      (blowupAtInfinityChartS ℐ U)).base
    rw [Scheme.Pullback.range_fst]
    rfl

/-- `𝐏¹_Z ∩ D₊(S) ⟶ Spec A[s]` is a closed immersion. -/
instance (U : X.affineOpens) :
    IsClosedImmersion
      (pullback.snd (lineToBlowupAtInfinity ℐ) (blowupAtInfinityChartS ℐ U) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap (Polynomial Γ(X, U.1)) (infinityChartAlgebra (ℐ.ideal U))))) :=
  MorphismProperty.of_isPullback (isPullback_lineToBlowupAtInfinity_chartS ℐ U).flip
    inferInstance

/-- On global sections, `𝐏¹_Z ∩ D₊(S) ⟶ Spec A[s]` has kernel `I · A[s]`, `I = ℐ(U)`. -/
theorem ker_appTop_lineToBlowupAtInfinity_chartS (U : X.affineOpens) :
    RingHom.ker (pullback.snd (lineToBlowupAtInfinity ℐ) (blowupAtInfinityChartS ℐ U) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap (Polynomial Γ(X, U.1)) (infinityChartAlgebra (ℐ.ideal U))))).appTop.hom =
      ((ℐ.ideal U).map (Polynomial.C : Γ(X, U.1) →+* Polynomial Γ(X, U.1))).map
        (Scheme.ΓSpecIso (CommRingCat.of (Polynomial Γ(X, U.1)))).inv.hom := by
  have hker : (pullback.snd (lineToBlowupAtInfinity ℐ) (blowupAtInfinityChartS ℐ U) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap (Polynomial Γ(X, U.1)) (infinityChartAlgebra (ℐ.ideal U))))).ker =
      ℐ.comap (Spec.map (CommRingCat.ofHom
        (Polynomial.C : Γ(X, U.1) →+* Polynomial Γ(X, U.1))) ≫ U.2.fromSpec) := by
    rw [ker_eq_comap_ker_of_isPullback (isPullback_lineToBlowupAtInfinity_chartS ℐ U),
      ker_eq_comap_ker_of_isPullback (isPullback_projectiveLineBaseChange ℐ.subschemeι).flip,
      Scheme.IdealSheafData.ker_subschemeι, ← Scheme.IdealSheafData.comap_comp,
      infinityChartOver_comp]
  have h := ideal_comap_SpecMap_fromSpec_top ℐ U
    (CommRingCat.ofHom (Polynomial.C : Γ(X, U.1) →+* Polynomial Γ(X, U.1)))
  rwa [← hker, Scheme.Hom.ker_apply] at h

/-- Global sections of `a ≫ Spec.map φ`, read through `Γ(Spec R) ≅ R`, are those of `a` after
`φ`. -/
theorem appTop_comp_ΓSpecIso_inv_comp {T : Scheme.{u}} {R S : Type u} [CommRing R] [CommRing S]
    (a : T ⟶ Spec (.of S)) (φ : R →+* S) :
    (a.appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).comp φ =
      (a ≫ Spec.map (CommRingCat.ofHom φ)).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom := by
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)
  rw [Scheme.Hom.comp_appTop]
  ext x
  have hx := congrArg (fun g => g.hom x) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hx
  simp only [RingHom.comp_apply, CommRingCat.hom_comp, hx]

/-- **The ratios on a closed subscheme of the chart.** Let `a : T ⟶ Spec A[s][J/s]` be a morphism
such that `T ⟶ Spec A[s][J/s] ⟶ Spec A[s]` is a closed immersion whose kernel on global sections
is `I · A[s]`, `I = (f₁, …, f_r)`. Then the kernel of `a` on global sections is generated by the
ratios `fᵢ/s`. -/
theorem ker_appTop_eq_span_infinityChartRatio {T : Scheme.{u}} {A : Type u} [CommRing A] {r : ℕ}
    (f : Fin r → A) {I : Ideal A} (hfI : ∀ i, f i ∈ I) (hf : I = Ideal.span (Set.range f))
    (a : T ⟶ Spec (.of (infinityChartAlgebra I)))
    [IsClosedImmersion (a ≫ Spec.map (CommRingCat.ofHom
      (algebraMap (Polynomial A) (infinityChartAlgebra I))))]
    (hker : RingHom.ker (a ≫ Spec.map (CommRingCat.ofHom
        (algebraMap (Polynomial A) (infinityChartAlgebra I)))).appTop.hom =
      (I.map (Polynomial.C : A →+* Polynomial A)).map
        (Scheme.ΓSpecIso (.of (Polynomial A))).inv.hom) :
    RingHom.ker (a.appTop.hom.comp (Scheme.ΓSpecIso (.of (infinityChartAlgebra I))).inv.hom) =
      Ideal.span (Set.range (infinityChartRatio f hfI)) := by
  have heq := appTop_comp_ΓSpecIso_inv_comp a (algebraMap (Polynomial A) (infinityChartAlgebra I))
  refine ker_eq_span_infinityChartRatio f hfI hf _ ?_ ?_
  · rw [heq]
    exact (Scheme.Hom.app_surjective (a ≫ Spec.map (CommRingCat.ofHom
      (algebraMap (Polynomial A) (infinityChartAlgebra I)))) ⊤ (isAffineOpen_top _)).comp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (Polynomial A))).inv).2
  · rw [heq, ← RingHom.comap_ker, hker]
    exact Ideal.comap_map_of_bijective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (Polynomial A))).inv)

/-- **The kernel of a closed immersion on the image of an affine chart.** For a closed immersion
`i : T ⟶ W` and an open immersion `χ : Spec R ⟶ W`, the kernel of `i` on the sections over the
image of `χ` is, through `Γ(W, χ(Spec R)) ≅ R`, the kernel of the base change of `i` along `χ` on
global sections. -/
theorem ker_app_image_top_eq_map {T W : Scheme.{u}} (i : T ⟶ W) [IsClosedImmersion i]
    {R : CommRingCat.{u}} (χ : Spec R ⟶ W) [IsOpenImmersion χ] :
    RingHom.ker (i.app (χ ''ᵁ ⊤)).hom =
      (RingHom.ker ((pullback.snd i χ).appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom)).map
        ((Scheme.ΓSpecIso R).symm ≪≫ (χ.appIso ⊤).symm).commRingCatIsoToRingEquiv.toRingHom := by
  obtain ⟨e, he⟩ : ∃ e : R ≃+* Γ(W, χ ''ᵁ ⊤),
      e = ((Scheme.ΓSpecIso R).symm ≪≫ (χ.appIso ⊤).symm).commRingCatIsoToRingEquiv := ⟨_, rfl⟩
  rw [← he]
  have hk1 := Scheme.ker_ideal_of_isPullback_of_isOpenImmersion i (pullback.snd i χ)
    (pullback.fst i χ) χ (IsPullback.of_hasPullback i χ).flip ⟨⊤, isAffineOpen_top _⟩
  rw [Scheme.Hom.ker_apply, Scheme.Hom.ker_apply] at hk1
  have hk2 : RingHom.ker ((pullback.snd i χ).appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom) =
      (RingHom.ker (i.app (χ ''ᵁ ⊤)).hom).comap e.toRingHom := by
    rw [← RingHom.comap_ker]
    change Ideal.comap _ (RingHom.ker ((pullback.snd i χ).app ⊤).hom) = _
    rw [hk1, Ideal.comap_comap, he]
    rfl
  rw [hk2, Ideal.map_comap_of_surjective e.toRingHom e.surjective]

/-- **A regular sequence cutting out the base change to an affine chart.** For a closed
immersion `i : T ⟶ W` and an open immersion `χ : Spec R ⟶ W`, if the kernel of the base change of
`i` along `χ` on global sections is generated by a regular sequence `y` of `R`, then the kernel of
`i` on the sections over the image of `χ` is generated by a regular sequence of the same length. -/
theorem exists_ker_app_image_top_eq_span_of_ker_pullbackSnd {T W : Scheme.{u}} (i : T ⟶ W)
    [IsClosedImmersion i] {R : CommRingCat.{u}} (χ : Spec R ⟶ W) [IsOpenImmersion χ] {r : ℕ}
    (y : Fin r → R)
    (hker : RingHom.ker ((pullback.snd i χ).appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom) =
      Ideal.span (Set.range y))
    (hy : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn y)) :
    ∃ g : Fin r → Γ(W, χ ''ᵁ ⊤),
      RingHom.ker (i.app (χ ''ᵁ ⊤)).hom = Ideal.span (Set.range g) ∧
        RingTheory.Sequence.IsWeaklyRegular Γ(W, χ ''ᵁ ⊤) (List.ofFn g) := by
  obtain ⟨e, he⟩ : ∃ e : R ≃+* Γ(W, χ ''ᵁ ⊤),
      e = ((Scheme.ΓSpecIso R).symm ≪≫ (χ.appIso ⊤).symm).commRingCatIsoToRingEquiv := ⟨_, rfl⟩
  refine ⟨fun a => e (y a), ?_, Stacks.AlgebraicGeometry.isWeaklyRegular_ofFn_map_of_flat
    e.toRingHom (RingHom.Flat.of_bijective e.bijective) _ hy⟩
  rw [ker_app_image_top_eq_map, hker, ← he, Ideal.map_span, ← Set.range_comp]
  rfl

/-- **On the chart `D₊(S)` over `U`, `𝐏¹_Z` is cut out by a regular sequence of length `r`.**
If `ℐ(U)` is generated by a regular sequence `f₁, …, f_r`, the kernel of `𝐏¹_Z ⟶ W` on the
sections over `D₊(S)` is generated by the images of the ratios `fᵢ/s`, which form a regular
sequence. -/
theorem exists_ker_lineToBlowupAtInfinity_app_chartS (U : X.affineOpens) {r : ℕ}
    (f : Fin r → Γ(X, U.1)) (hf : ℐ.ideal U = Ideal.span (Set.range f))
    (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(X, U.1) (List.ofFn f)) :
    ∃ g : Fin r → Γ(blowupAtInfinity ℐ, blowupAtInfinityChartS ℐ U ''ᵁ ⊤),
      RingHom.ker ((lineToBlowupAtInfinity ℐ).app (blowupAtInfinityChartS ℐ U ''ᵁ ⊤)).hom =
        Ideal.span (Set.range g) ∧
      RingTheory.Sequence.IsWeaklyRegular Γ(blowupAtInfinity ℐ, blowupAtInfinityChartS ℐ U ''ᵁ ⊤)
        (List.ofFn g) := by
  have hfI : ∀ i, f i ∈ ℐ.ideal U := fun i => by rw [hf]; exact Ideal.subset_span ⟨i, rfl⟩
  exact exists_ker_app_image_top_eq_span_of_ker_pullbackSnd _ _ (infinityChartRatio f hfI)
    (ker_appTop_eq_span_infinityChartRatio f hfI hf _
      (ker_appTop_lineToBlowupAtInfinity_chartS ℐ U))
    (isWeaklyRegular_infinityChartRatio f hfI hf hreg)

/-! ### The main result -/

/-- **`𝐏¹_Z ⟶ W` is regular of codimension `c` when `Z ⟶ X` is**, for the closed subscheme
`Z = V(ℐ)` of an ideal sheaf `ℐ`. -/
theorem isRegularClosedImmersionOfCodim_lineToBlowupAtInfinity_of_subschemeι {c : ℕ}
    (h : IsRegularClosedImmersionOfCodim ℐ.subschemeι c) :
    IsRegularClosedImmersionOfCodim (lineToBlowupAtInfinity ℐ) c := by
  have hK := (isRegularClosedImmersionOfCodim_iff_kerGeneratedBy _ c).mp h
  rw [isRegularClosedImmersionOfCodim_iff_kerGeneratedBy]
  intro w hw
  rw [(lineToBlowupAtInfinity ℐ).isClosedEmbedding.isClosed_range.closure_eq] at hw
  obtain ⟨p, rfl⟩ := hw
  have hbp := blowupAtInfinityToLine_lineToBlowupAtInfinity_apply ℐ p
  have hqz : (relativeProjectiveLine X ↘ X) (projectiveLineBaseChange ℐ.subschemeι p) =
      ℐ.subschemeι ((relativeProjectiveLine ℐ.subscheme ↘ ℐ.subscheme) p) := by
    rw [← Scheme.Hom.comp_apply, projectiveLineBaseChange_over, Scheme.Hom.comp_apply]
  obtain ⟨U, hzU, r, f, hker, hc, hreg⟩ :=
    hK _ (subset_closure ⟨(relativeProjectiveLine ℐ.subscheme ↘ ℐ.subscheme) p, rfl⟩)
  subst hc
  by_cases hq : projectiveLineBaseChange ℐ.subschemeι p ∈ Set.range (affineChart X)
  · have hL : projectiveLineBaseChange ℐ.subschemeι p ∈ isomorphismLocusAtInfinity ℐ :=
      (le_sup_left : (affineChart X).opensRange ≤ isomorphismLocusAtInfinity ℐ) hq
    exact exists_affineOpen_ker_eq_span_of_kerGeneratedBy_pullback
      (regularSequenceOfLength_map_of_flat r) _ _
      (kerGeneratedBy_pullback_isomorphismLocusAtInfinity ℐ h)
      (show blowupAtInfinityToLine ℐ (lineToBlowupAtInfinity ℐ p) ∈ _ by rw [hbp]; exact hL)
      ⟨p, rfl⟩
  · have hinf : projectiveLineBaseChange ℐ.subschemeι p ∈ Set.range (lineInfinitySection X) := by
      rw [← compl_range_affineChart]; exact hq
    obtain ⟨x₀, hx₀⟩ := hinf
    have hx₀U : x₀ ∈ U.1 := by
      have : (relativeProjectiveLine X ↘ X) (lineInfinitySection X x₀) = x₀ := by
        rw [← Scheme.Hom.comp_apply, lineInfinitySection_comp]; rfl
      rwa [← this, hx₀, hqz]
    obtain ⟨y, hy⟩ := (IsAffineOpen.range_fromSpec (U.2 : IsAffineOpen U.1)).ge hx₀U
    have hqU : projectiveLineBaseChange ℐ.subschemeι p ∈ (infinityChartAffineOpen U).1 := by
      refine ⟨Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : Γ(X, U.1)))) y,
        trivial, ?_⟩
      have := congrArg (fun φ => φ y) (congrArg (fun g => (g.base : _ → _))
        (specMap_evalZero_infinityChartOver U))
      simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] at this
      change (infinityChartOver U) _ = _
      rw [this, hy, hx₀]
    have hw := (lineToBlowupAtInfinity_mem_range_chartS_iff ℐ U p).mpr hqU
    have hI : ℐ.ideal U = Ideal.span (Set.range f) := by
      rw [← hker, ← Scheme.Hom.ker_apply, Scheme.IdealSheafData.ker_subschemeι]
    obtain ⟨g, hg, hgr⟩ := exists_ker_lineToBlowupAtInfinity_app_chartS ℐ U f hI hreg
    obtain ⟨a, ha⟩ := hw
    exact ⟨⟨blowupAtInfinityChartS ℐ U ''ᵁ ⊤,
      (isAffineOpen_top _).image_of_isOpenImmersion _⟩, ⟨a, trivial, ha⟩, r, g, hg, rfl, hgr⟩

/-- **The closed immersion `𝐏¹_Z ⟶ W` of Stacks 0FE9 is regular of codimension `r` when `Z ⟶ X`
is.** Here `W` is the blowup of `𝐏¹_X` in `∞(Z)` and the source of `𝐏¹_Z ⟶ W` is the projective
line of `V(ker i) ≅ Z`. -/
theorem isRegularClosedImmersionOfCodim_lineToBlowupAtInfinity {Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] {r : ℕ} (hreg : IsRegularClosedImmersionOfCodim i r) :
    IsRegularClosedImmersionOfCodim (lineToBlowupAtInfinity i.ker) r := by
  refine isRegularClosedImmersionOfCodim_lineToBlowupAtInfinity_of_subschemeι i.ker ?_
  rw [← i.toImage_imageι] at hreg
  exact (isRegularClosedImmersionOfCodim_iso_comp_iff (asIso i.toImage) _ r).mp hreg

/-- **`𝐏¹_Z ⟶ W` is a perfect morphism** (Stacks 068C) when `Z ⟶ X` is a regular immersion. -/
theorem perfect_lineToBlowupAtInfinity {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {r : ℕ} (hreg : IsRegularClosedImmersionOfCodim i r) :
    Perfect (lineToBlowupAtInfinity i.ker) :=
  perfect_of_isRegularImmersion _
    (isRegularClosedImmersionOfCodim_lineToBlowupAtInfinity i hreg).isRegularImmersion

/-- **`Q = i'_*𝒪_{𝐏¹_Z}` is a perfect object of `D(𝒪_W)`** (Stacks 0G2E), for
`i' : 𝐏¹_Z ⟶ W` the closed immersion of Stacks 0FE9 and `Z ⟶ X` regular. -/
theorem isPerfect_pushforward_lineToBlowupAtInfinity {Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] {r : ℕ} (hreg : IsRegularClosedImmersionOfCodim i r) :
    RingedSpace.IsPerfect
      ((DerivedCategory.singleFunctor (blowupAtInfinity i.ker).Modules 0).obj
        ((Scheme.Modules.pushforward (lineToBlowupAtInfinity i.ker)).obj
          (SheafOfModules.unit _))) :=
  have := perfect_lineToBlowupAtInfinity i hreg
  isPerfect_pushforward_structureSheaf _

/-- **The Chern classes of `Q = i'_*𝒪_{𝐏¹_Z}` are defined** (Stacks 0GUE), for `X` locally of
finite type over the base of chapter 42 which is quasi-compact or has quasi-compact irreducible
components, and `Z ⟶ X` regular. -/
theorem hasDefinedChernClasses_pushforward_lineToBlowupAtInfinity (C : ChowSituation.{u})
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {r : ℕ} (hreg : IsRegularClosedImmersionOfCodim i r)
    (hX : CompactSpace X ∨ ∀ T ∈ irreducibleComponents X, IsCompact T) :
    HasDefinedChernClasses
      ((DerivedCategory.singleFunctor (blowupAtInfinity i.ker).Modules 0).obj
        ((Scheme.Modules.pushforward (lineToBlowupAtInfinity i.ker)).obj
          (SheafOfModules.unit _))) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have hX' : ∀ T ∈ irreducibleComponents X, IsCompact T := hX.elim
    (fun _ T hT => (isClosed_of_mem_irreducibleComponents T hT).isCompact) id
  exact hasDefinedChernClasses_of_isCompact_irreducibleComponents C
    (blowupAtInfinityToBase i.ker ≫ sX)
    (isCompact_of_mem_irreducibleComponents_of_isProperMap
      (blowupAtInfinityToBase i.ker).isProperMap hX') _
    (isPerfect_pushforward_lineToBlowupAtInfinity i hreg)

end Stacks.Chow

end
