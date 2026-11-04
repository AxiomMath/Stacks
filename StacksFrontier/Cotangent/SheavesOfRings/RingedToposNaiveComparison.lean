module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.SheavesOfRings.NaiveComparisonArrow
public import StacksFrontier.Cotangent.SheavesOfRings.RingedToposCotangentComplex
public import StacksFrontier.Homology.DoubleExtend

/-!
# The canonical map from the cotangent complex to the naive cotangent complex

Let `(f, f♯) : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)` be a morphism of ringed topoi, let `P_•` be the
standard resolution of `𝒪_C` over `f⁻¹𝒪_D` and let `I` be the kernel of the augmentation
`P₀ ⟶ 𝒪_C`.  The cotangent complex `L_f` is the alternating-face complex of
`Ω_{P_•/f⁻¹𝒪_D} ⊗_{P_•} 𝒪_C`, and the naive cotangent complex `NL_f` is the two-term complex

`I/I² ⟶ 𝒪_C ⊗_{P₀} Ω_{P₀/f⁻¹𝒪_D}`

in cohomological degrees `-1` and `0`.  The degreewise comparison maps assemble into a map of
complexes `L_f ⟶ NL_f`, first for a homomorphism of sheaves of commutative rings on a site and then
for a morphism of ringed topoi.  That map identifies `NL_f` with the truncation `τ_{≥ -1} L_f`
exactly when it is an isomorphism on the cohomology sheaves of every degree `≥ -1`.

## Main definitions

* `HomologicalComplex.mkHomToDouble`: a morphism into a complex `HomologicalComplex.double g h`
  concentrated in two adjacent degrees, from its two components and the one commuting square
  they must satisfy.  This is dual to `HomologicalComplex.mkHomFromDouble`.
* `CategoryTheory.Sheaf.naiveCotangentComplex`: the naive cotangent complex `NL_{B/A}` of a
  homomorphism `f : A ⟶ B` of sheaves of commutative rings, as a cochain complex concentrated in
  degrees `-1` and `0`.
* `CategoryTheory.Sheaf.naiveComparison`: the canonical map of complexes `L_{B/A} ⟶ NL_{B/A}`.
* `AlgebraicGeometry.RingedToposHom.naiveCotangentComplex` is `NL_f` and
  `AlgebraicGeometry.RingedToposHom.naiveComparison` is the canonical map `L_f ⟶ NL_f` of a
  morphism of ringed topoi.

## Main results

* `CategoryTheory.Sheaf.objD_one` and
  `CategoryTheory.Sheaf.cotangentComplex_d_negTwo_negOne`: the differential of the cotangent
  complex from degree `-2` to degree `-1` is the alternating sum `δ₀ - δ₁ + δ₂` of the three
  faces `P₂ ⇶ P₁`, transported through the canonical degree isomorphisms.
* `CategoryTheory.Sheaf.naiveComparison_f_negOne` and
  `CategoryTheory.Sheaf.naiveComparison_f_zero`: the two components of the comparison are the
  arrows `d x ⊗ b ↦ b · [d₀ x - d₁ x]` and `d p ⊗ b ↦ b ⊗ d p`.
* `AlgebraicGeometry.RingedToposHom.naiveCotangentComplex_isZero_homology`: `NL_f` has no
  cohomology outside degrees `-1` and `0`.
* `AlgebraicGeometry.RingedToposHom.naiveComparison_isIso_homologyMap`: under the hypotheses that
  the comparison is an isomorphism on `H⁰` and on `H^{-1}`, it is an isomorphism on `Hⁱ` for every
  `i ≥ -1`; together with the previous result this is the identification of `NL_f` with
  `τ_{≥ -1} L_f`.

## Implementation notes

The naive cotangent complex is built here from the presentation `P₀ ⟶ 𝒪_C` of `𝒪_C` by the
degree-zero term of the standard resolution, rather than from
`Stacks.Sites.FreeAlgebra.canonicalPresentation`; the canonical isomorphism between those two
presentations of `𝒪_C` is not constructed, so the comparison is not transported to
`Stacks.SheafOfModules.naiveCotangentComplex`.

The identification of `NL_f` with `τ_{≥ -1} L_f` is phrased as a statement about cohomology
sheaves rather than about a truncation functor on a derived category: `NL_f` is concentrated in
degrees `-1` and `0`, so a map `L_f ⟶ NL_f` identifies `NL_f` with `τ_{≥ -1} L_f` exactly when it
is an isomorphism on `Hⁱ` for every `i ≥ -1`.  The two isomorphisms in degrees `0` and `-1` are
hypotheses of `CategoryTheory.Sheaf.naiveComparison_isIso_homologyMap` and
`AlgebraicGeometry.RingedToposHom.naiveComparison_isIso_homologyMap`; they are the comparison with
the chaotic topology in the proof of Tag 08US, which is not formalized here.

## References

* [Stacks Project, Tag 08V2](https://stacks.math.columbia.edu/tag/08V2)
* [Stacks Project, Tag 08US](https://stacks.math.columbia.edu/tag/08US), the same statement for a
  homomorphism of sheaves of rings, of which Tag 08V2 is the special case at `f⁻¹𝒪_D ⟶ 𝒪_C`.
* [Stacks Project, Tag 08UP](https://stacks.math.columbia.edu/tag/08UP), the same comparison for
  a homomorphism of commutative rings.
* [Stacks Project, Tag 08SU](https://stacks.math.columbia.edu/tag/08SU), the cotangent complex of
  a morphism of ringed topoi.
* [Stacks Project, Tag 08U0](https://stacks.math.columbia.edu/tag/08U0), the naive cotangent
  complex of a morphism of ringed topoi.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u v w v' u' w'

/-! ### Morphisms into a complex concentrated in two degrees -/

namespace HomologicalComplex

section

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
  {X₀ X₁ : C} {f : X₀ ⟶ X₁} {ι : Type*} {c : ComplexShape ι} {i₀ i₁ : ι}
  (hi₀₁ : c.Rel i₀ i₁) (h : i₀ ≠ i₁) {K : HomologicalComplex C c}
  (φ₀ : K.X i₀ ⟶ X₀) (φ₁ : K.X i₁ ⟶ X₁)

open scoped Classical in
/-- The degreewise family underlying `HomologicalComplex.mkHomToDouble`: the two given morphisms
in degrees `i₀` and `i₁`, and zero in every other degree. -/
noncomputable def toDoubleF (k : ι) : K.X k ⟶ (double f hi₀₁).X k :=
  if hk₀ : k = i₀ then
    eqToHom (by rw [hk₀]) ≫ φ₀ ≫ (doubleXIso₀ f hi₀₁).inv ≫ eqToHom (by rw [hk₀])
  else if hk₁ : k = i₁ then
    eqToHom (by rw [hk₁]) ≫ φ₁ ≫ (doubleXIso₁ f hi₀₁ h).inv ≫ eqToHom (by rw [hk₁])
  else 0

/-- In degree `i₀`, `HomologicalComplex.toDoubleF` is `φ₀` followed by the identification of that
degree of `double f hi₀₁` with `X₀`. -/
@[simp]
lemma toDoubleF_i₀ : toDoubleF hi₀₁ h φ₀ φ₁ i₀ = φ₀ ≫ (doubleXIso₀ f hi₀₁).inv := by
  classical
  rw [toDoubleF, dite_eq_left rfl]
  simp

/-- In degree `i₁`, `HomologicalComplex.toDoubleF` is `φ₁` followed by the identification of that
degree of `double f hi₀₁` with `X₁`. -/
@[simp]
lemma toDoubleF_i₁ : toDoubleF hi₀₁ h φ₀ φ₁ i₁ = φ₁ ≫ (doubleXIso₁ f hi₀₁ h).inv := by
  classical
  rw [toDoubleF, dite_eq_right h.symm, dite_eq_left rfl]
  simp

/-- In a degree other than `i₀` and `i₁`, `HomologicalComplex.toDoubleF` is zero. -/
lemma toDoubleF_eq_zero (k : ι) (h₀ : k ≠ i₀) (h₁ : k ≠ i₁) :
    toDoubleF (f := f) hi₀₁ h φ₀ φ₁ k = 0 := by
  classical
  rw [toDoubleF, dite_eq_right h₀, dite_eq_right h₁]

variable (comm : K.d i₀ i₁ ≫ φ₁ = φ₀ ≫ f)
  (hφ : ∀ k : ι, c.Rel k i₀ → K.d k i₀ ≫ φ₀ = 0)
  (hsucc : ∀ k : ι, c.Rel i₁ k → k ≠ i₀ ∧ k ≠ i₁)

/-- Constructor for morphisms into a homological complex `double f hi₀₁`, dual to
`HomologicalComplex.mkHomFromDouble`: such a morphism is given by its components in degrees `i₀`
and `i₁`, the square `comm` relating them, and the vanishing `hφ` of the composite of the
component in degree `i₀` with every differential into that degree. -/
noncomputable def mkHomToDouble : K ⟶ double f hi₀₁ where
  f := toDoubleF hi₀₁ h φ₀ φ₁
  comm' k₀ k₁ hk := by
    by_cases h₀ : k₀ = i₀
    · subst h₀
      obtain rfl := c.next_eq hk hi₀₁
      rw [toDoubleF_i₀, toDoubleF_i₁, double_d f hi₀₁ h]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [reassoc_of% comm]
    · by_cases h₁ : k₀ = i₁
      · subst h₁
        obtain ⟨hA, hB⟩ := hsucc k₁ hk
        rw [toDoubleF_i₁, toDoubleF_eq_zero hi₀₁ h φ₀ φ₁ k₁ hA hB,
          double_d_eq_zero₀ f hi₀₁ _ _ h.symm, comp_zero, comp_zero]
      · rw [toDoubleF_eq_zero hi₀₁ h φ₀ φ₁ k₀ h₀ h₁, zero_comp]
        by_cases hk₁₀ : k₁ = i₀
        · subst hk₁₀
          rw [toDoubleF_i₀, ← Category.assoc, hφ k₀ hk, zero_comp]
        · by_cases hk₁₁ : k₁ = i₁
          · exact absurd (c.prev_eq hk (by rw [hk₁₁]; exact hi₀₁)) h₀
          · rw [toDoubleF_eq_zero hi₀₁ h φ₀ φ₁ k₁ hk₁₀ hk₁₁, comp_zero]

/-- The components of `HomologicalComplex.mkHomToDouble` are given by
`HomologicalComplex.toDoubleF`. -/
@[simp]
lemma mkHomToDouble_f (k : ι) :
    (mkHomToDouble hi₀₁ h φ₀ φ₁ comm hφ hsucc).f k = toDoubleF hi₀₁ h φ₀ φ₁ k := rfl

end

end HomologicalComplex

/-! ### The comparison for a homomorphism of sheaves of rings -/

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A B : Sheaf J CommRingCat.{max u v w}} (f : A ⟶ B)

/-- The naive cotangent complex `NL_{B/A}`, with the conormal sheaf `I/I²` of the presentation
`P₀ ⟶ B` in cohomological degree `-1` and `B ⊗_{P₀} Ω_{P₀/A}` in degree `0`. -/
noncomputable def naiveCotangentComplex : CochainComplex (targetModules.{u, v, w} J B) ℤ :=
  HomologicalComplex.double (naiveSequence.{u, v, w} J f).f
    ComplexShape.upIntRelNegOneZero

/-- The conormal sheaf `I/I²` is the degree `-1` term of the naive cotangent complex. -/
noncomputable def naiveCotangentComplexXNegOneIso :
    (naiveCotangentComplex.{u, v, w} J f).X (-1) ≅ (naiveSequence.{u, v, w} J f).X₁ :=
  HomologicalComplex.doubleXIso₀ _ ComplexShape.upIntRelNegOneZero

/-- The sheaf `B ⊗_{P₀} Ω_{P₀/A}` is the degree `0` term of the naive cotangent complex. -/
noncomputable def naiveCotangentComplexXZeroIso :
    (naiveCotangentComplex.{u, v, w} J f).X 0 ≅ (naiveSequence.{u, v, w} J f).X₂ :=
  HomologicalComplex.doubleXIso₁ _ ComplexShape.upIntRelNegOneZero (by decide)

/-- The naive cotangent complex has no terms outside degrees `-1` and `0`. -/
theorem naiveCotangentComplex_isZero_X (i : ℤ) (hneg : i ≠ -1) (hzero : i ≠ 0) :
    IsZero ((naiveCotangentComplex.{u, v, w} J f).X i) :=
  HomologicalComplex.isZero_double_X _ _ i hneg hzero

/-- The alternating sum of the face maps in simplicial degree one is `δ₀ - δ₁ + δ₂`. -/
theorem objD_one :
    AlgebraicTopology.AlternatingFaceMapComplex.objD
        (cotangentSimplicialModule.{u, v, w} J f).object 1 =
      (cotangentSimplicialModule.{u, v, w} J f).object.δ 0 -
        (cotangentSimplicialModule.{u, v, w} J f).object.δ 1 +
        (cotangentSimplicialModule.{u, v, w} J f).object.δ 2 := by
  rw [AlgebraicTopology.AlternatingFaceMapComplex.objD, Fin.sum_univ_three]
  simp [sub_eq_add_neg]

/-- The differential from degree `-2` to degree `-1`, transported through the canonical degree
isomorphisms. -/
theorem cotangentComplex_d_negTwo_negOne :
    (cotangentComplex.{u, v, w} J f).d (-2) (-1) =
      (cotangentComplex_degreeIso.{u, v, w} J f 2).hom ≫
        AlgebraicTopology.AlternatingFaceMapComplex.objD
          (cotangentSimplicialModule.{u, v, w} J f).object 1 ≫
        (cotangentComplex_degreeIso.{u, v, w} J f 1).inv :=
  cotangentComplex_d.{u, v, w} J f 1

/-- The canonical map of complexes `L_{B/A} ⟶ NL_{B/A}`: it is `d x ⊗ b ↦ b · [d₀ x - d₁ x]` in
degree `-1`, it is `d p ⊗ b ↦ b ⊗ d p` in degree `0`, and it is zero in every other degree, the
naive cotangent complex having no other terms. -/
@[stacks 08US "the canonical map `L_{B/A} → NL_{B/A}` as a map of complexes, assembled from the
degreewise comparison and its two squares. Hypotheses beyond the source: the naive cotangent
complex is realized as the conormal sequence of the presentation `P₀ ⟶ B` by the degree-zero term
of the standard resolution, and the identification of that presentation with
`Stacks.Sites.FreeAlgebra.canonicalPresentation` is not carried"]
noncomputable def naiveComparison :
    cotangentComplex.{u, v, w} J f ⟶ naiveCotangentComplex.{u, v, w} J f :=
  HomologicalComplex.mkHomToDouble ComplexShape.upIntRelNegOneZero (by decide)
    ((cotangentComplex_degreeIso.{u, v, w} J f 1).hom ≫ naiveComparisonNegOne.{u, v, w} J f)
    ((cotangentComplex_degreeIso.{u, v, w} J f 0).hom ≫ naiveComparisonZero.{u, v, w} J f)
    (by
      rw [cotangentComplex_d_negOne_zero, objD_zero]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, Preadditive.sub_comp,
        naiveComparisonNegOne_comp_conormal J f])
    (fun k hk => by
      obtain rfl : k = -2 := by change k + 1 = -1 at hk; omega
      rw [cotangentComplex_d_negTwo_negOne, objD_one]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [naiveComparisonNegOne_faceSum, comp_zero])
    (fun k hk => by
      obtain rfl : k = 1 := by change (0 : ℤ) + 1 = k at hk; omega
      exact ⟨by decide, by decide⟩)

/-- In degree `-1` the comparison is the arrow `d x ⊗ b ↦ b · [d₀ x - d₁ x]`. -/
theorem naiveComparison_f_negOne :
    (naiveComparison.{u, v, w} J f).f (-1) =
      ((cotangentComplex_degreeIso.{u, v, w} J f 1).hom ≫
          naiveComparisonNegOne.{u, v, w} J f) ≫
        (naiveCotangentComplexXNegOneIso.{u, v, w} J f).inv :=
  HomologicalComplex.toDoubleF_i₀ _ _ _ _

/-- In degree `0` the comparison is the arrow `d p ⊗ b ↦ b ⊗ d p`. -/
theorem naiveComparison_f_zero :
    (naiveComparison.{u, v, w} J f).f 0 =
      ((cotangentComplex_degreeIso.{u, v, w} J f 0).hom ≫
          naiveComparisonZero.{u, v, w} J f) ≫
        (naiveCotangentComplexXZeroIso.{u, v, w} J f).inv :=
  HomologicalComplex.toDoubleF_i₁ _ _ _ _

/-- The naive cotangent complex has no cohomology outside degrees `-1` and `0`. -/
theorem naiveCotangentComplex_isZero_homology (i : ℤ) (hneg : i ≠ -1) (hzero : i ≠ 0) :
    IsZero ((naiveCotangentComplex.{u, v, w} J f).homology i) :=
  (HomologicalComplex.ExactAt.of_isZero
    (naiveCotangentComplex_isZero_X.{u, v, w} J f i hneg hzero)).isZero_homology

/-- If the canonical map `L_{B/A} ⟶ NL_{B/A}` is an isomorphism on the cohomology sheaves of
degrees `0` and `-1` (the hypotheses `homologyZeroIsIso` and `homologyNegOneIsIso`), then it is an
isomorphism on the cohomology sheaf of every degree `≥ -1`. Since the naive cotangent complex has
no cohomology below degree `-1`, this says that the canonical map identifies `NL_{B/A}` with the
truncation `τ_{≥ -1} L_{B/A}`. -/
@[stacks 08US "the identification of the naive cotangent complex with the truncation
`τ_{≥ -1} L_{B/A}`, stated as: the canonical map is an isomorphism on the cohomology sheaf of
every degree `≥ -1`, the naive complex having no cohomology below degree `-1` by
`CategoryTheory.Sheaf.naiveCotangentComplex_isZero_homology`. Hypotheses carried:
`homologyZeroIsIso` and `homologyNegOneIsIso`, the isomorphisms on `H⁰` and on `H^{-1}`, which
are the final step of the source's proof — the comparison with the chaotic topology, reducing
them to the ring-level map of Tag 08UP and transporting along the inverse-image isomorphism of
Tag 08TZ. That tag IS carried as an isomorphism of complexes,
`Stacks.SheafOfModules.inverseImageNaiveCotangentComplexIso`; what is not carried is the
comparison with the chaotic topology"]
theorem naiveComparison_isIso_homologyMap
    (homologyZeroIsIso :
      IsIso (HomologicalComplex.homologyMap (naiveComparison.{u, v, w} J f) 0))
    (homologyNegOneIsIso :
      IsIso (HomologicalComplex.homologyMap (naiveComparison.{u, v, w} J f) (-1)))
    (i : ℤ) (hi : -1 ≤ i) :
    IsIso (HomologicalComplex.homologyMap (naiveComparison.{u, v, w} J f) i) := by
  by_cases hneg : i = -1
  · exact hneg ▸ homologyNegOneIsIso
  by_cases hzero : i = 0
  · exact hzero ▸ homologyZeroIsIso
  have hL : IsZero ((cotangentComplex.{u, v, w} J f).homology i) :=
    (HomologicalComplex.ExactAt.of_isZero
      (cotangentComplex_isZero_pos.{u, v, w} J f i (by omega))).isZero_homology
  have hN : IsZero ((naiveCotangentComplex.{u, v, w} J f).homology i) :=
    naiveCotangentComplex_isZero_homology.{u, v, w} J f i hneg hzero
  exact ⟨0, hL.eq_of_src _ _, hN.eq_of_src _ _⟩

end CategoryTheory.Sheaf

/-! ### The comparison for a morphism of ringed topoi -/

namespace AlgebraicGeometry.RingedToposHom

variable {X : RingedTopos.{v, u, max u v w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{max u v w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  (f : RingedToposHom X Y)

/-- The conormal sequence `I/I² ⟶ 𝒪_C ⊗_{P₀} Ω_{P₀/f⁻¹𝒪_D} ⟶ Ω_f ⟶ 0` of the presentation of
`𝒪_C` by the degree-zero term of the standard resolution of `f⁻¹𝒪_D ⟶ 𝒪_C`.  Its first two
terms, with the left-hand map as differential, are the naive cotangent complex of `f`. -/
noncomputable abbrev naiveSequence : ShortComplex (Sheaf.targetModules.{u, v, w} X.J X.O) :=
  Sheaf.naiveSequence.{u, v, w} X.J f.fSharpInverseImage

/-- The naive cotangent complex `NL_f = NL_{𝒪_C/f⁻¹𝒪_D}` of a morphism of ringed topoi
`(f, f♯) : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)`: the two-term complex `I/I² ⟶ 𝒪_C ⊗_{P₀} Ω_{P₀/f⁻¹𝒪_D}` in
cohomological degrees `-1` and `0`, formed from the inverse-image form `f⁻¹𝒪_D ⟶ 𝒪_C` of its
structure map. -/
@[stacks 08U0 "the complex `NL_f`, with the free algebra sheaf of the source's presentation
spelled by the degree-zero term `P₀` of the standard resolution of `f⁻¹𝒪_D ⟶ 𝒪_C`; the
identification of that presentation with `Stacks.Sites.FreeAlgebra.canonicalPresentation` is not
carried"]
noncomputable def naiveCotangentComplex :
    CochainComplex (Sheaf.targetModules.{u, v, w} X.J X.O) ℤ :=
  Sheaf.naiveCotangentComplex.{u, v, w} X.J f.fSharpInverseImage

/-- `NL_f` has no terms outside degrees `-1` and `0`. -/
theorem naiveCotangentComplex_isZero_X (i : ℤ) (hneg : i ≠ -1) (hzero : i ≠ 0) :
    IsZero ((f.naiveCotangentComplex).X i) :=
  Sheaf.naiveCotangentComplex_isZero_X.{u, v, w} X.J f.fSharpInverseImage i hneg hzero

/-- `NL_f` has no cohomology outside degrees `-1` and `0`. -/
theorem naiveCotangentComplex_isZero_homology (i : ℤ) (hneg : i ≠ -1) (hzero : i ≠ 0) :
    IsZero ((f.naiveCotangentComplex).homology i) :=
  Sheaf.naiveCotangentComplex_isZero_homology.{u, v, w} X.J f.fSharpInverseImage i hneg hzero

/-- The canonical map `L_f ⟶ NL_f` from the cotangent complex of a morphism of ringed topoi to its
naive cotangent complex: `CategoryTheory.Sheaf.naiveComparison` at the inverse-image form
`f⁻¹𝒪_D ⟶ 𝒪_C` of the structure map. It is `d x ⊗ b ↦ b · [d₀ x - d₁ x]` in degree `-1`, it is
`d p ⊗ b ↦ b ⊗ d p` in degree `0`, and it is zero in every other degree. -/
@[stacks 08V2 "the canonical map `L_f → NL_f` of a morphism of ringed topoi, as a map of complexes
of sheaves of `𝒪_C`-modules. Hypotheses beyond the source: `NL_f` is realized as the conormal
sequence of the presentation `P₀ ⟶ 𝒪_C` by the degree-zero term of the standard resolution of
`f⁻¹𝒪_D ⟶ 𝒪_C`, and the identification of that presentation with
`Stacks.Sites.FreeAlgebra.canonicalPresentation` is not carried, so the map is not transported to
`Stacks.SheafOfModules.naiveCotangentComplex`. The second assertion of the tag, that this map
identifies `NL_f` with the truncation `τ_{≥ -1} L_f`, is the separate carrier
`AlgebraicGeometry.RingedToposHom.naiveComparison_isIso_homologyMap`"]
noncomputable def naiveComparison : f.cotangentComplex ⟶ f.naiveCotangentComplex :=
  Sheaf.naiveComparison.{u, v, w} X.J f.fSharpInverseImage

/-- If the canonical map `L_f ⟶ NL_f` is an isomorphism on the cohomology sheaves of degrees `0`
and `-1` (the hypotheses `homologyZeroIsIso` and `homologyNegOneIsIso`), then it is an isomorphism
on the cohomology sheaf of every degree `≥ -1`. Since `NL_f` has no cohomology below degree `-1`,
by `AlgebraicGeometry.RingedToposHom.naiveCotangentComplex_isZero_homology`, this says that the
canonical map identifies the naive cotangent complex with the truncation `τ_{≥ -1} L_f`. -/
@[stacks 08V2 "the second assertion of the tag: the canonical map identifies `NL_f` with the
truncation `τ_{≥ -1} L_f`, stated as: it is an isomorphism on the cohomology sheaf of every
degree `≥ -1`, the naive complex having no cohomology below degree `-1` by
`AlgebraicGeometry.RingedToposHom.naiveCotangentComplex_isZero_homology`. Hypotheses carried:
`homologyZeroIsIso` and `homologyNegOneIsIso`, the isomorphisms on `H⁰` and on `H^{-1}`, which
are the final step of the proof of Tag 08US that this tag is the special case of — the comparison
with the chaotic topology, reducing them to the ring-level map of Tag 08UP and transporting along
the inverse-image isomorphism of Tag 08TZ. That tag IS carried as an isomorphism of complexes,
`Stacks.SheafOfModules.inverseImageNaiveCotangentComplexIso`; what is not carried is the
comparison with the chaotic topology"]
theorem naiveComparison_isIso_homologyMap
    (homologyZeroIsIso : IsIso (HomologicalComplex.homologyMap f.naiveComparison 0))
    (homologyNegOneIsIso : IsIso (HomologicalComplex.homologyMap f.naiveComparison (-1)))
    (i : ℤ) (hi : -1 ≤ i) :
    IsIso (HomologicalComplex.homologyMap f.naiveComparison i) :=
  Sheaf.naiveComparison_isIso_homologyMap.{u, v, w} X.J f.fSharpInverseImage
    homologyZeroIsIso homologyNegOneIsIso i hi

end AlgebraicGeometry.RingedToposHom

end
