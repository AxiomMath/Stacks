module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.UniversalFlattening
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.FibreHilbert
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.Valuative
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.HilbertPolynomialFiniteDetermination
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFibreEulerCharacteristicUnconditional

/-!
# The Hilbert-polynomial locus `Z_P` of the flat locus

Over the flat locus `Z ⟶ G` of the universal family `ℱ_G`
(`AlgebraicGeometry.ProjectiveQuot.flatLocus`) the pulled-back family `ℱ_Z` is flat and of finite
presentation over `Z`. Its fibrewise Hilbert functions `y ↦ (d ↦ χ(ℱ_y(d)))` are locally constant
in each `d` (Stacks 0B9T), and each is determined by its values at `d = 0, …, n` (Stacks 08AC, the
backward differences of order `n + 1` vanish). Hence the locus
`Z_P = {y ∈ Z : χ(ℱ_y(d)) = P(d + m) for all d}` is open and closed. A morphism `t : T ⟶ G` factors
through `Z_P` exactly when `(ℙⁿ_t)^* ℱ_G` is flat over `T` with fibrewise Hilbert functions
`d ↦ P(d + m)`. This is the open and closed subscheme of the proof of Stacks 0DPA.

## Main definitions

* `AlgebraicGeometry.ProjectiveQuot.flatFamily`: `ℱ_Z` on `ℙⁿ_Z`.
* `AlgebraicGeometry.ProjectiveQuot.hilbertLocus`: `Z_P`, an open of `Z`.
* `AlgebraicGeometry.ProjectiveQuot.hilbertLocusHom`: `Z_P ⟶ G`.

## Main results

* `AlgebraicGeometry.ProjectiveQuot.isClopen_hilbertLocusSet`: `Z_P` is open and closed in `Z`.
* `AlgebraicGeometry.ProjectiveQuot.exists_lift_hilbertLocusHom_iff`: `t : T ⟶ G` factors through
  `Z_P` iff `(ℙⁿ_t)^* ℱ_G` is flat over `T` with fibrewise Hilbert functions `d ↦ P(d + m)`.

## References

* [Stacks Project, Tag 0DPA](https://stacks.math.columbia.edu/tag/0DPA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

universe u

namespace AlgebraicGeometry.ProjectiveQuot

variable (n r : ℕ) (hr : 1 ≤ r) (P : Polynomial ℚ)

/-- **The family `ℱ_Z`** on `ℙⁿ_Z` over the flat locus `Z` of `ℱ_G`. -/
abbrev flatFamily : (projectiveSpaceOver n (flatLocus.{u} n r hr P).left).Modules :=
  (Scheme.Modules.pullback (projectiveSpaceOverMap n (flatLocus.{u} n r hr P).hom)).obj
    (universalFamily.{u} n r hr P)

/-- The family `ℱ_Z` is flat and of finite presentation over the flat locus `Z`. -/
theorem isFlatFamily_flatFamily : IsFlatFamily (flatFamily.{u} n r hr P) :=
  ⟨inferInstance, (exists_lift_flatLocus_iff _).1 ⟨𝟙 _, Category.id_comp _⟩⟩

/-- The fibrewise Hilbert functions of `ℱ_Z` are locally constant in each degree (Stacks 0B9T). -/
theorem isLocallyConstant_fibreHilbert_flatFamily (d : ℤ) :
    IsLocallyConstant fun y => fibreHilbert (flatFamily.{u} n r hr P) y d := by
  have hF := isFlatFamily_flatFamily.{u} n r hr P
  have := isProper_projectiveSpaceOver n (flatLocus.{u} n r hr P).left
  have h := isLocallyConstant_fibreEulerCharacteristic _
    (finitePresentation_projectiveSpaceOver n _) (twist d (flatFamily.{u} n r hr P))
    inferInstance (isFlatOver_twist _ d _ hF.2)
  have he : (fun y => fibreHilbert (flatFamily.{u} n r hr P) y d) =
      fibreEulerCharacteristic (projectiveSpaceOver n (flatLocus.{u} n r hr P).left ↘
        (flatLocus.{u} n r hr P).left) (twist d (flatFamily.{u} n r hr P)) := by
    funext y
    have := isCoherent_fibre y (flatFamily.{u} n r hr P)
    exact hilbertPolynomial_fibre_eq_fibreEulerCharacteristic hF y d
  rwa [he]

/-- **The Hilbert-polynomial locus** `Z_P = {y ∈ Z : χ(ℱ_y(d)) = P(d + m) for all d}` as a set. -/
def hilbertLocusSet : Set (flatLocus.{u} n r hr P).left :=
  {y | ∀ d : ℤ, (fibreHilbert (flatFamily.{u} n r hr P) y d : ℚ) =
    P.eval ((d : ℚ) + (regularityIndex.{u} n r hr P : ℚ))}

/-- **`Z_P` is open and closed.** -/
theorem isClopen_hilbertLocusSet : IsClopen (hilbertLocusSet.{u} n r hr P) := by
  have hloc := isLocallyConstant_fibreHilbert_flatFamily.{u} n r hr P
  refine ⟨?_, ?_⟩
  · have : hilbertLocusSet.{u} n r hr P = ⋂ d : ℤ, {y | ((fun z : ℤ => (z : ℚ)) ∘
        (fun y => fibreHilbert (flatFamily.{u} n r hr P) y d)) y =
          P.eval ((d : ℚ) + (regularityIndex.{u} n r hr P : ℚ))} := by
      ext y
      simp only [hilbertLocusSet, Set.mem_setOf_eq, Set.mem_iInter, Function.comp_apply]
    rw [this]
    exact isClosed_iInter fun d => ((hloc d).comp _).isClosed_fiber _
  · refine isOpen_iff_forall_mem_open.2 fun y hy => ⟨⋂ i ∈ Finset.range (n + 1),
      {y' | fibreHilbert (flatFamily.{u} n r hr P) y' i =
        fibreHilbert (flatFamily.{u} n r hr P) y i}, ?_, ?_, ?_⟩
    · intro y' hy' d
      have hfun : fibreHilbert (flatFamily.{u} n r hr P) y' =
          fibreHilbert (flatFamily.{u} n r hr P) y := by
        have := isCoherent_fibre y (flatFamily.{u} n r hr P)
        have := isCoherent_fibre y' (flatFamily.{u} n r hr P)
        exact hilbertPolynomial_eq_of_forall_le _ _ n _ _ fun i hi =>
          Set.mem_iInter₂.1 hy' i (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
      rw [hfun]
      exact hy d
    · exact isOpen_biInter_finset fun i _ => (hloc i).isOpen_fiber _
    · exact Set.mem_iInter₂.2 fun i _ => rfl

/-- **`Z_P`** as an open of the flat locus `Z`. -/
def hilbertLocus : (flatLocus.{u} n r hr P).left.Opens :=
  ⟨hilbertLocusSet.{u} n r hr P, (isClopen_hilbertLocusSet.{u} n r hr P).isOpen⟩

/-- **The monomorphism `Z_P ⟶ G`.** -/
def hilbertLocusHom : (hilbertLocus.{u} n r hr P).toScheme ⟶ quotGrassmannian.{u} n r hr P :=
  (hilbertLocus.{u} n r hr P).ι ≫ (flatLocus.{u} n r hr P).hom

/-- The morphism `Z_P ⟶ G` is a monomorphism. -/
instance : Mono (hilbertLocusHom.{u} n r hr P) := by
  unfold hilbertLocusHom
  infer_instance

variable {n r hr P}

/-- The pullback of `ℱ_G` along `s ≫ (Z ⟶ G)` has the fibrewise Hilbert functions of `ℱ_Z` at
the images of the points. -/
theorem fibreHilbert_pullback_comp_flatLocus {T : Scheme.{u}}
    (s : T ⟶ (flatLocus.{u} n r hr P).left) (t : T) :
    fibreHilbert ((Scheme.Modules.pullback
      (projectiveSpaceOverMap n (s ≫ (flatLocus.{u} n r hr P).hom))).obj
        (universalFamily.{u} n r hr P)) t =
      fibreHilbert (flatFamily.{u} n r hr P) (s t) := by
  rw [← fibreHilbert_pullback s (flatFamily.{u} n r hr P) t]
  exact fibreHilbert_eq_of_iso
    ((Scheme.Modules.pullbackCongr (projectiveSpaceOverMap_comp n s _)).symm.app
        (universalFamily.{u} n r hr P) ≪≫
      ((Scheme.Modules.pullbackComp (projectiveSpaceOverMap n s)
        (projectiveSpaceOverMap n (flatLocus.{u} n r hr P).hom)).app
          (universalFamily.{u} n r hr P)).symm :
      (Scheme.Modules.pullback (projectiveSpaceOverMap n (s ≫ (flatLocus.{u} n r hr P).hom))).obj
        (universalFamily.{u} n r hr P) ≅
      (Scheme.Modules.pullback (projectiveSpaceOverMap n s)).obj
        (flatFamily.{u} n r hr P)) t

/-- **The `T`-points of `Z_P`**: `t : T ⟶ G` factors through `Z_P` iff `(ℙⁿ_t)^* ℱ_G` is flat
over `T` with fibrewise Hilbert functions `d ↦ P(d + m)`. -/
theorem exists_lift_hilbertLocusHom_iff {T : Scheme.{u}} (t : T ⟶ quotGrassmannian.{u} n r hr P) :
    (∃ w : T ⟶ (hilbertLocus.{u} n r hr P).toScheme, w ≫ hilbertLocusHom.{u} n r hr P = t) ↔
      IsFlatOver (projectiveSpaceOver n T ↘ T).toLRSHom.toShHom
          ((Scheme.Modules.pullback (projectiveSpaceOverMap n t)).obj
            (universalFamily.{u} n r hr P)) ∧
        ∀ (t' : T) (d : ℤ),
          (fibreHilbert ((Scheme.Modules.pullback (projectiveSpaceOverMap n t)).obj
              (universalFamily.{u} n r hr P)) t' d : ℚ) =
            P.eval ((d : ℚ) + (regularityIndex.{u} n r hr P : ℚ)) := by
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨(exists_lift_flatLocus_iff _).1 ⟨w ≫ (hilbertLocus.{u} n r hr P).ι, by
      rw [hilbertLocusHom, Category.assoc]⟩, fun t' d => ?_⟩
    rw [hilbertLocusHom, ← Category.assoc, fibreHilbert_pullback_comp_flatLocus]
    exact (w t').2 d
  · rintro ⟨hflat, hhil⟩
    obtain ⟨s, rfl⟩ := (exists_lift_flatLocus_iff t).2 hflat
    have hrange : Set.range s ⊆ Set.range (hilbertLocus.{u} n r hr P).ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨t', rfl⟩ d
      rw [← fibreHilbert_pullback_comp_flatLocus]
      exact hhil t' d
    refine ⟨IsOpenImmersion.lift (hilbertLocus.{u} n r hr P).ι s hrange, ?_⟩
    rw [hilbertLocusHom, ← Category.assoc, IsOpenImmersion.lift_fac]

end AlgebraicGeometry.ProjectiveQuot

end
