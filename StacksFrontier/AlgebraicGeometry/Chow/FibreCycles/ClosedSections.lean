module

public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles

/-!
# The two integral points of the projective line are closed subschemes

The projective line over a commutative ring is glued from two copies of the affine line along
their common punctured affine line. The origin of either chart therefore misses the other
chart entirely, because the overlap is the locus where the coordinate is invertible. Hence the
closed subscheme `V(X)` of a chart stays closed in the glued scheme, and in particular the
distinguished points `0` and `∞` of `ℙ¹_ℤ` — which are the images of the whole of `Spec ℤ`
under the two chart immersions, the zero section and the infinity section of `ℙ¹_ℤ ⟶ Spec ℤ` —
have closed range.

## Main results

* `Stacks.Chow.notMem_range_ι_of_X_mem`: a point of one chart at which the coordinate vanishes
  does not lie in the image of any other chart.
* `Stacks.Chow.mem_range_ι_of_X_notMem`: a point of one chart at which the coordinate does not
  vanish lies in the image of every other chart.
* `Stacks.Chow.isClosed_image_ι`: the image under a chart immersion of a closed set on which
  the coordinate vanishes is closed in the projective line.
* `Stacks.Chow.isClosed_range_integralZeroSection` and
  `Stacks.Chow.isClosed_range_integralInfinitySection`: the two distinguished integral points
  of `ℙ¹_ℤ` have closed range.
* `Stacks.Chow.range_comp_scheme` and `Stacks.Chow.surjective_of_isIso`: two general facts
  about ranges of morphisms of schemes that the above needs.

## Implementation notes

The overlap inclusion `D.f i j` of the glue datum of Tag 01JE is, for `i ≠ j`, the punctured
chart `Spec k[T, T⁻¹] ⟶ Spec k[X]` precomposed with an `eqToHom` coming from the `dite` that
`CategoryTheory.GlueData.ofGlueData'` inserts; it is extracted here only up to that
precomposition, which is all the range argument needs. The range of the punctured chart is the
basic open set `D(X)`, by the localization description of the range of `Spec` of a localization
map.

Closedness in the glued scheme is checked chart by chart with
`AlgebraicGeometry.Scheme.GlueData.isOpen_iff`, and the two cases are "the chart itself", where
the preimage of the image is the original set because a chart immersion is injective, and "any
other chart", where the preimage is empty by the first result above. The argument never needs
the index type to be `ULift Bool`, so it is stated for an arbitrary pair of distinct indices.

## References

* [Stacks Project, Tag 01JE](https://stacks.math.columbia.edu/tag/01JE)
* [Stacks Project, Tag 02S4](https://stacks.math.columbia.edu/tag/02S4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

section ProjectiveLine

variable (k : Type u) [CommRing k]

/-- A point lies in the range of the punctured chart exactly when the coordinate does not
belong to it. -/
private theorem mem_range_puncturedChart_iff {x : Spec (CommRingCat.of (Polynomial k))} :
    x ∈ Set.range (projectiveLinePuncturedChart k).base ↔
      (Polynomial.X : Polynomial k) ∉ (x : PrimeSpectrum (Polynomial k)).asIdeal := by
  change (x : PrimeSpectrum (Polynomial k)) ∈
      Set.range (PrimeSpectrum.comap (Polynomial.toLaurent (R := k))) ↔ _
  rw [show (Polynomial.toLaurent (R := k)) =
      algebraMap (Polynomial k) (LaurentPolynomial k) from rfl,
    PrimeSpectrum.localization_away_comap_range (LaurentPolynomial k) Polynomial.X]
  exact PrimeSpectrum.mem_basicOpen _ _

/-- The overlap of two distinct charts is the punctured chart, up to an isomorphism. -/
private theorem gluingData_f_eq_iso_comp (i j : (projectiveLineGluingData k).J) (h : i ≠ j) :
    ∃ u : (projectiveLineGluingData k).V (i, j) ≅ Spec (CommRingCat.of (LaurentPolynomial k)),
      (projectiveLineGluingData k).f i j = u.hom ≫ projectiveLinePuncturedChart k := by
  refine ⟨eqToIso (dite_eq_right h), ?_⟩
  change (projectiveLineGluingData' k).f' i j = _
  dsimp only [CategoryTheory.GlueData'.f']
  split_ifs with h'
  · exact absurd h' h
  · rfl

/-- A point in the range of the punctured chart is one at which the coordinate is invertible,
so the coordinate does not belong to it. -/
theorem notMem_of_mem_range_puncturedChart {x : Spec (CommRingCat.of (Polynomial k))}
    (h : x ∈ Set.range (projectiveLinePuncturedChart k).base) :
    (Polynomial.X : Polynomial k) ∉ (x : PrimeSpectrum (Polynomial k)).asIdeal :=
  (mem_range_puncturedChart_iff k).mp h

/-- Every overlap of two distinct charts of the projective line lands in the punctured
chart. -/
theorem range_gluingData_f_subset (i j : (projectiveLineGluingData k).J) (h : i ≠ j) :
    Set.range ((projectiveLineGluingData k).f i j).base ⊆
      Set.range (projectiveLinePuncturedChart k).base := by
  obtain ⟨u, hu⟩ := gluingData_f_eq_iso_comp k i j h
  rintro x ⟨z, rfl⟩
  exact ⟨u.hom z, by rw [← Scheme.Hom.comp_apply, ← hu]; rfl⟩

/-- A point of one chart at which the coordinate vanishes does not lie in the image of any
other chart: the two charts overlap exactly where the coordinate is invertible. -/
theorem notMem_range_ι_of_X_mem (i₀ i : (projectiveLineGluingData k).J) (hne : i₀ ≠ i)
    (x : Spec (CommRingCat.of (Polynomial k)))
    (hx : (Polynomial.X : Polynomial k) ∈ (x : PrimeSpectrum (Polynomial k)).asIdeal) :
    ((projectiveLineGluingData k).ι i₀) x ∉
      Set.range ((projectiveLineGluingData k).ι i).base := by
  rintro ⟨y, hy⟩
  obtain ⟨z, hz, -⟩ := ((projectiveLineGluingData k).ι_eq_iff i₀ i x y).mp hy.symm
  dsimp only at hz
  exact notMem_of_mem_range_puncturedChart k
    (range_gluingData_f_subset k _ _ hne ⟨z, hz⟩) hx

/-- A point of one chart at which the coordinate does not vanish lies in the image of every
other chart: the two charts overlap exactly where the coordinate is invertible. -/
theorem mem_range_ι_of_X_notMem (i₀ i : (projectiveLineGluingData k).J) (hne : i₀ ≠ i)
    (x : Spec (CommRingCat.of (Polynomial k)))
    (hx : (Polynomial.X : Polynomial k) ∉ (x : PrimeSpectrum (Polynomial k)).asIdeal) :
    ((projectiveLineGluingData k).ι i₀) x ∈
      Set.range ((projectiveLineGluingData k).ι i).base := by
  obtain ⟨u, hu⟩ := gluingData_f_eq_iso_comp k i₀ i hne
  have hx' := (mem_range_puncturedChart_iff k).mpr hx
  obtain ⟨z, hz'⟩ : ∃ z : Spec (CommRingCat.of (LaurentPolynomial k)),
      projectiveLinePuncturedChart k z = x := hx'
  refine ⟨((projectiveLineGluingData k).t i₀ i ≫ (projectiveLineGluingData k).f i i₀) (u.inv z),
    (((projectiveLineGluingData k).ι_eq_iff i₀ i x _).mpr ⟨u.inv z, ?_, rfl⟩).symm⟩
  show ((projectiveLineGluingData k).f i₀ i) (u.inv z) = x
  have h₂ : (u.hom ≫ projectiveLinePuncturedChart k) (u.inv z) = x := by
    rw [Scheme.Hom.comp_apply, Scheme.inv_hom_apply]
    exact hz'
  exact (congrArg (fun g => g (u.inv z)) hu).trans h₂

/-- The image under a chart immersion of a closed set contained in the vanishing locus of the
coordinate is closed in the projective line. -/
theorem isClosed_image_ι (i₀ : (projectiveLineGluingData k).J)
    {Z : Set ((projectiveLineGluingData k).U i₀)} (hZ : IsClosed Z)
    (hZX : ∀ x ∈ Z, (Polynomial.X : Polynomial k) ∈ (x : PrimeSpectrum (Polynomial k)).asIdeal) :
    IsClosed (((projectiveLineGluingData k).ι i₀) '' Z) := by
  rw [← isOpen_compl_iff, (projectiveLineGluingData k).isOpen_iff]
  intro i
  rw [Set.preimage_compl, isOpen_compl_iff]
  obtain rfl | hne := eq_or_ne i₀ i
  · rwa [Set.preimage_image_eq _
      ((projectiveLineGluingData k).ι i₀).isOpenEmbedding.injective]
  · convert isClosed_empty
    ext y
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_empty_iff_false, iff_false, not_exists,
      not_and]
    intro x hxZ hx
    exact notMem_range_ι_of_X_mem k i₀ i hne x (hZX x hxZ) ⟨y, hx.symm⟩

end ProjectiveLine

section IntegralSections

/-- The range of a composition of morphisms of schemes is the image of the range. -/
theorem range_comp_scheme {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) :
    Set.range (a ≫ b) = b '' Set.range a := by
  have h : (⇑(a ≫ b) : X → Z) = ⇑b ∘ ⇑a := funext fun x => Scheme.Hom.comp_apply a b x
  rw [h, Set.range_comp]

/-- An isomorphism of schemes is surjective on points. -/
theorem surjective_of_isIso {A B : Scheme.{u}} (g : A ⟶ B) [IsIso g] :
    Function.Surjective ⇑g := by
  have : IsIso g.base := inferInstance
  exact (TopCat.homeoOfIso (asIso g.base)).surjective

/-- The comparison between the two terminal schemes is surjective on points. -/
theorem surjective_specULiftZIsTerminal_from : Function.Surjective
    ⇑(AlgebraicGeometry.specULiftZIsTerminal.from (⊤_ Scheme.{u})) :=
  have : IsIso (AlgebraicGeometry.specULiftZIsTerminal.from (⊤_ Scheme.{u})) :=
    isIso_of_isTerminal terminalIsTerminal AlgebraicGeometry.specULiftZIsTerminal _
  surjective_of_isIso _

/-- The origin of an affine-line chart is the vanishing locus of the kernel of evaluation at
zero. -/
theorem range_specMap_evalRingHom_zero :
    Set.range (Spec.map (CommRingCat.ofHom
        (Polynomial.evalRingHom (0 : ULift.{u} ℤ)))) =
      PrimeSpectrum.zeroLocus
        (RingHom.ker (Polynomial.evalRingHom (0 : ULift.{u} ℤ))) := by
  show Set.range (PrimeSpectrum.comap (Polynomial.evalRingHom (0 : ULift.{u} ℤ))) = _
  exact range_comap_of_surjective _ _ fun a => ⟨Polynomial.C a, by simp⟩

/-- The coordinate vanishes at every point of the origin of an affine-line chart. -/
theorem X_mem_of_mem_range_specMap_evalRingHom_zero
    {x : Spec (CommRingCat.of (Polynomial (ULift.{u} ℤ)))}
    (hx : x ∈ Set.range (Spec.map (CommRingCat.ofHom
      (Polynomial.evalRingHom (0 : ULift.{u} ℤ))))) :
    (Polynomial.X : Polynomial (ULift.{u} ℤ)) ∈
      (x : PrimeSpectrum (Polynomial (ULift.{u} ℤ))).asIdeal := by
  rw [range_specMap_evalRingHom_zero] at hx
  exact hx (by simp [RingHom.mem_ker])

/-- The range of an integral point obtained as the origin of a chart is the image of the
origin. -/
private theorem range_terminalFrom_comp_origin_comp
    (c : Spec (CommRingCat.of (Polynomial (ULift.{u} ℤ))) ⟶ projectiveLine (ULift.{u} ℤ)) :
    Set.range (AlgebraicGeometry.specULiftZIsTerminal.from (⊤_ Scheme.{u}) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : ULift.{u} ℤ))) ≫ c) =
      c '' Set.range (Spec.map (CommRingCat.ofHom
        (Polynomial.evalRingHom (0 : ULift.{u} ℤ)))) := by
  simp only [← Category.assoc]
  rw [range_comp_scheme, range_comp_scheme, surjective_specULiftZIsTerminal_from.range_eq,
    Set.image_univ]

/-- The image of the origin under a chart immersion is closed in the projective line. -/
private theorem isClosed_image_ι_origin (i₀ : (projectiveLineGluingData (ULift.{u} ℤ)).J) :
    IsClosed (((projectiveLineGluingData (ULift.{u} ℤ)).ι i₀) ''
      Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : ULift.{u} ℤ))))) :=
  isClosed_image_ι (ULift.{u} ℤ) i₀
    (range_specMap_evalRingHom_zero.symm ▸
      PrimeSpectrum.isClosed_zeroLocus (R := Polynomial (ULift.{u} ℤ)) _)
    fun _ hx => X_mem_of_mem_range_specMap_evalRingHom_zero hx

/-- The zero point of `ℙ¹_ℤ` is the image of the origin of the first chart. -/
theorem range_integralZeroSection :
    Set.range (integralZeroSection.{u}) =
      (projectiveLineXChart (ULift.{u} ℤ)) ''
        Set.range (Spec.map (CommRingCat.ofHom
          (Polynomial.evalRingHom (0 : ULift.{u} ℤ)))) :=
  range_terminalFrom_comp_origin_comp _

/-- The infinity point of `ℙ¹_ℤ` is the image of the origin of the second chart. -/
theorem range_integralInfinitySection :
    Set.range (integralInfinitySection.{u}) =
      (projectiveLineYChart (ULift.{u} ℤ)) ''
        Set.range (Spec.map (CommRingCat.ofHom
          (Polynomial.evalRingHom (0 : ULift.{u} ℤ)))) :=
  range_terminalFrom_comp_origin_comp _

/-- The zero point of `ℙ¹_ℤ` is a closed subset. -/
theorem isClosed_range_integralZeroSection :
    IsClosed (Set.range (integralZeroSection.{u})) := by
  rw [range_integralZeroSection]
  exact isClosed_image_ι_origin (projectiveLineXIndex (ULift.{u} ℤ))

/-- The infinity point of `ℙ¹_ℤ` is a closed subset. -/
theorem isClosed_range_integralInfinitySection :
    IsClosed (Set.range (integralInfinitySection.{u})) := by
  rw [range_integralInfinitySection]
  exact isClosed_image_ι_origin (projectiveLineYIndex (ULift.{u} ℤ))

end IntegralSections

end Stacks.Chow

end
