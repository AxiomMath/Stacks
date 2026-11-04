module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.RationalDoublePointResolution
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.ChartStalkBridge
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.CaseOneChart
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.CaseTransfer
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.CaseTwoStep
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.EmbeddingDimensionThree

/-!
# The levels of the termination argument for rational double points

The singular points met while blowing up a rational double point are sorted into four levels,
following Section 54.12 of the source with the exact invariants of the case II analysis:

* level 0: an element is a good coordinate (case I);
* level 1: an element is the first of three generators with `w₃² = w₁F`, `F ≡ f w₂²` modulo
  `(w₁, w₃)𝔪`, `f` a unit (`AlgebraicGeometry.HasDoubleLineRelationUnit`);
* level 2: an element is the second of three generators with `w₃² = w₁F`, `F ∈ 𝔪²`
  (`AlgebraicGeometry.HasDoubleLineRelation`);
* level 3: the ring is in case II (`AlgebraicGeometry.IsCaseTwo`).

At a singular point of the blowup of a ring at level `n` with element `x`, the chart computations
(`CaseOneChart`, `CaseTwoStep`) show that the local ring is either at a lower level, or has residue
field `κ`, has its exceptional divisor cut out by `x` and is again at level `n` with the image of
`x`. They are statements about the localization of a chart ring, which
`AlgebraicGeometry.exists_isMaximal_ringEquiv_stalk_compat_of_memChart` identifies with the local
ring of the blowup compatibly with the maps from the base. This is the input of
`AlgebraicGeometry.exists_singularPointBlowupChain_isRegular_of_levels`.

## Main definitions

* `AlgebraicGeometry.rationalDoublePointLevel`: the four levels.

## Main results

* `AlgebraicGeometry.RationalDoublePointSituation.step_rationalDoublePointLevel`: the descent.
* `AlgebraicGeometry.RationalDoublePointSituation.exists_rationalDoublePointLevel`: every
  Situation 0BGC has a regular blowup or an element at some level.

## References

* [Stacks Project, Tag 0BGE](https://stacks.math.columbia.edu/tag/0BGE)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry

/-- **The levels of the termination argument.** -/
def rationalDoublePointLevel : ℕ → ∀ (R : Type u) [CommRing R] [IsLocalRing R], R → Prop
  | 0 => fun R _ _ x => IsGoodCoordinate R x
  | 1 => fun R _ _ x => ∃ w : Fin 3 → R, w 0 = x ∧ HasDoubleLineRelationUnit R w
  | 2 => fun R _ _ x => ∃ w : Fin 3 → R, w 1 = x ∧ HasDoubleLineRelation R w
  | 3 => fun R _ _ x => IsCaseTwo R ∧ x ∈ maximalIdeal R
  | _ + 4 => fun _ _ _ _ => False

/-- The levels are carried along a local homomorphism which is surjective on residue fields and
maps the maximal ideal onto the maximal ideal. -/
theorem rationalDoublePointLevel_map (n : ℕ) {R R' : Type u} [CommRing R] [IsLocalRing R]
    [CommRing R'] [IsLocalRing R'] (φ : R →+* R') [IsLocalHom φ]
    (hsurj : Function.Surjective ((Ideal.Quotient.mk (maximalIdeal R')).comp φ))
    (hmap : Ideal.map φ (maximalIdeal R) = maximalIdeal R') (x : R)
    (h : rationalDoublePointLevel n R x) : rationalDoublePointLevel n R' (φ x) := by
  match n, h with
  | 0, h => exact IsGoodCoordinate.map φ hsurj hmap h
  | 1, ⟨w, hw, hD⟩ => exact ⟨φ ∘ w, by simp [hw], HasDoubleLineRelationUnit.map φ hmap hD⟩
  | 2, ⟨w, hw, hD⟩ => exact ⟨φ ∘ w, by simp [hw], HasDoubleLineRelation.map φ hmap hD⟩
  | 3, ⟨hII, hx⟩ => exact ⟨IsCaseTwo.map φ hmap hII, hmap ▸ Ideal.mem_map_of_mem φ hx⟩

/-- The levels are carried along ring isomorphisms. -/
theorem rationalDoublePointLevel_ringEquiv (n : ℕ) {R R' : Type u} [CommRing R] [IsLocalRing R]
    [CommRing R'] [IsLocalRing R'] (e : R ≃+* R') (x : R)
    (h : rationalDoublePointLevel n R x) : rationalDoublePointLevel n R' (e x) := by
  have : IsLocalHom (e : R →+* R') := IsLocalHom.of_surjective _ e.surjective
  exact rationalDoublePointLevel_map n (e : R →+* R')
    (Ideal.Quotient.mk_surjective.comp e.surjective) (map_ringEquiv_maximalIdeal e) x h

/-- The levels are carried to the completion. -/
theorem rationalDoublePointLevel_adicCompletion (n : ℕ) (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (x : R) (h : rationalDoublePointLevel n R x) :
    rationalDoublePointLevel n (AdicCompletion (maximalIdeal R) R) (algebraMap _ _ x) := by
  refine rationalDoublePointLevel_map n _ (fun t => ?_) AdicCompletion.maximalIdeal_eq_map.symm x h
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective t
  obtain ⟨r, hr⟩ := (AdicCompletion.residueField_map_bijective R).2 (residue _ y)
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  exact ⟨r, hr⟩

/-- An element at some level lies in the maximal ideal. -/
theorem mem_maximalIdeal_of_rationalDoublePointLevel (n : ℕ) {R : Type u} [CommRing R]
    [IsLocalRing R] (x : R) (h : rationalDoublePointLevel n R x) : x ∈ maximalIdeal R := by
  match n, h with
  | 0, ⟨w, a, hw0, hspan, _⟩ => exact hw0 ▸ hspan ▸ Ideal.subset_span ⟨0, rfl⟩
  | 1, ⟨w, hw, hspan, _⟩ => exact hw ▸ hspan ▸ Ideal.subset_span ⟨0, rfl⟩
  | 2, ⟨w, hw, hspan, _⟩ => exact hw ▸ hspan ▸ Ideal.subset_span ⟨1, rfl⟩
  | 3, ⟨_, hx⟩ => exact hx

namespace RationalDoublePointSituation

/-- **The chart data at a singular point of the blowup.** At a singular point `z` of the blowup
of a Situation 0BGC lying in the chart attached to `b`, the local ring is the localization of
`A[𝔪/b]` at a maximal ideal containing `𝔪A[𝔪/b]`, compatibly with the maps from `A`; that
localization is a Noetherian normal domain of dimension two which is not regular. -/
theorem exists_chartData (S : RationalDoublePointSituation.{u}) {b : S.A}
    (hb : b ∈ IsLocalRing.maximalIdeal S.A) (z : blowUp (maximalIdealSheaf S.A))
    (hz : z ∈ singularLocus (blowUp (maximalIdealSheaf S.A))) (hc : MemChart hb z) :
    ∃ M : Ideal (affineBlowupAlgebra (IsLocalRing.maximalIdeal S.A) b (Localization.Away b)),
      M.IsMaximal ∧
      Ideal.map (algebraMap S.A (affineBlowupAlgebra (IsLocalRing.maximalIdeal S.A) b
        (Localization.Away b))) (IsLocalRing.maximalIdeal S.A) ≤ M ∧
      ∃ (_ : M.IsPrime)
        (ε : (blowUp (maximalIdealSheaf S.A)).presheaf.stalk z ≃+* Localization.AtPrime M),
        (∀ a : S.A, ε (maximalIdealBlowUpStalkHom S.A z a) =
          algebraMap _ (Localization.AtPrime M)
            (algebraMap S.A (affineBlowupAlgebra (IsLocalRing.maximalIdeal S.A) b
              (Localization.Away b)) a)) ∧
        IsNoetherianRing (Localization.AtPrime M) ∧ IsDomain (Localization.AtPrime M) ∧
        IsIntegrallyClosed (Localization.AtPrime M) ∧
        ringKrullDim (Localization.AtPrime M) = 2 ∧
        ¬ IsRegularLocalRing (Localization.AtPrime M) := by
  have hzc := S.isClosed_of_mem_singularLocus_blowUp z hz
  obtain ⟨M, hM, hle, hprime, ε, hε⟩ :=
    exists_isMaximal_ringEquiv_stalk_compat_of_memChart S.A hb z hzc hc
  have := S.isLocallyNoetherian_blowUp
  have : IsNormalDomain ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk z) :=
    S.isNormalDomain_stalk_blowUp z
  refine ⟨M, hM, hle, hprime, ε, hε, isNoetherianRing_of_ringEquiv _ ε,
    ε.symm.injective.isDomain ε.symm.toRingHom, IsIntegrallyClosed.of_equiv ε, ?_, ?_⟩
  · rw [← ringKrullDim_eq_of_ringEquiv ε]
    exact S.ringKrullDim_stalk_blowUp_eq_two z hzc
  · exact fun hreg => hz (IsRegularLocalRing.of_ringEquiv ε.symm)


section Transport

variable (S : RationalDoublePointSituation.{u}) {b : S.A} {z : blowUp (maximalIdealSheaf S.A)}
  {M : Ideal (affineBlowupAlgebra (IsLocalRing.maximalIdeal S.A) b (Localization.Away b))}
  [M.IsMaximal]
  (ε : (blowUp (maximalIdealSheaf S.A)).presheaf.stalk z ≃+* Localization.AtPrime M)
  (hε : ∀ a : S.A, ε (maximalIdealBlowUpStalkHom S.A z a) =
    algebraMap _ (Localization.AtPrime M)
      (algebraMap S.A (affineBlowupAlgebra (IsLocalRing.maximalIdeal S.A) b
        (Localization.Away b)) a))

include hε in
/-- The exceptional condition on a chart gives the exceptional condition on the blowup. -/
theorem map_maximalIdeal_eq_span_of_chart (x : S.A)
    (h : Ideal.map ((algebraMap (affineBlowupAlgebra (IsLocalRing.maximalIdeal S.A) b
        (Localization.Away b)) (Localization.AtPrime M)).comp
        (algebraMap S.A (affineBlowupAlgebra (IsLocalRing.maximalIdeal S.A) b
          (Localization.Away b)))) (IsLocalRing.maximalIdeal S.A) =
      Ideal.span {((algebraMap (affineBlowupAlgebra (IsLocalRing.maximalIdeal S.A) b
        (Localization.Away b)) (Localization.AtPrime M)).comp
        (algebraMap S.A (affineBlowupAlgebra (IsLocalRing.maximalIdeal S.A) b
          (Localization.Away b)))) x}) :
    Ideal.map (maximalIdealBlowUpStalkHom S.A z) (IsLocalRing.maximalIdeal S.A) =
      Ideal.span {maximalIdealBlowUpStalkHom S.A z x} :=
  map_maximalIdeal_eq_span_of_ringEquiv _ ε ((algebraMap _ (Localization.AtPrime M)).comp
    (algebraMap S.A (affineBlowupAlgebra (IsLocalRing.maximalIdeal S.A) b
      (Localization.Away b)))) hε x h

include hε in
/-- Surjectivity on the residue field of a chart point gives it on the blowup. -/
theorem surjective_residue_of_chart
    (hle : Ideal.map (algebraMap S.A (affineBlowupAlgebra (IsLocalRing.maximalIdeal S.A) b
      (Localization.Away b))) (IsLocalRing.maximalIdeal S.A) ≤ M)
    (h : Function.Surjective ((Ideal.Quotient.mk M).comp
      (algebraMap S.A (affineBlowupAlgebra (IsLocalRing.maximalIdeal S.A) b
        (Localization.Away b))))) :
    Function.Surjective ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk z))).comp
        (maximalIdealBlowUpStalkHom S.A z)) := by
  obtain ⟨ι, hι⟩ := exists_residueField_ringEquiv_of_surjective M hle h
  refine surjective_residue_of_ringEquiv _ ε ((algebraMap _ (Localization.AtPrime M)).comp
    (algebraMap S.A (affineBlowupAlgebra (IsLocalRing.maximalIdeal S.A) b
      (Localization.Away b)))) hε fun t => ?_
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective t
  obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective (ι.symm (residue _ y))
  refine ⟨r, ?_⟩
  have key : ι (residue S.A r) = residue _ y := by rw [hr, ι.apply_symm_apply]
  rw [hι r] at key
  exact key

end Transport

/-- A level at a local ring of the blowup is a level at a Situation 0BGC with that ring. -/
theorem exists_situation_level (S : RationalDoublePointSituation.{u})
    (z : blowUp (maximalIdealSheaf S.A))
    (hz : z ∈ singularLocus (blowUp (maximalIdealSheaf S.A))) (n : ℕ)
    {B : Type u} [CommRing B] [IsLocalRing B]
    (ε : (blowUp (maximalIdealSheaf S.A)).presheaf.stalk z ≃+* B) (y : B)
    (h : rationalDoublePointLevel n B y) :
    ∃ S' : RationalDoublePointSituation.{u},
      Nonempty (S'.A ≃+* (blowUp (maximalIdealSheaf S.A)).presheaf.stalk z) ∧
      ∃ y' : S'.A, rationalDoublePointLevel n S'.A y' := by
  obtain ⟨S', ⟨e⟩⟩ := S.exists_situation_of_mem_singularLocus_blowUp z hz
  exact ⟨S', ⟨e⟩, _, rationalDoublePointLevel_ringEquiv n (e.trans ε).symm y h⟩

/-- **Case I gives level `0` or a regular blowup**: in case I, a singular point of the blowup
produces a good coordinate (`AlgebraicGeometry.exists_isGoodCoordinate_of_chart`). -/
theorem singularLocus_eq_empty_or_level_zero (S : RationalDoublePointSituation.{u})
    (h : IsCaseOne S.A) :
    singularLocus (blowUp (maximalIdealSheaf S.A)) = ∅ ∨
      ∃ g : S.A, rationalDoublePointLevel 0 S.A g := by
  rcases (singularLocus (blowUp (maximalIdealSheaf S.A))).eq_empty_or_nonempty with he | ⟨z, hz⟩
  · exact Or.inl he
  right
  obtain ⟨w, a, hspan, hupper, -, hrel, hcase⟩ := h
  obtain ⟨j, hj⟩ := exists_memChart S.A w hspan z
  obtain ⟨M, hM, hle, hprime, ε, hε, hnoeth, hdom, hic, hdim, hsing⟩ :=
    S.exists_chartData _ z hz hj
  have := hM
  have := hnoeth
  exact exists_isGoodCoordinate_of_chart w hspan a hupper hrel hcase j _ M hle hdim hsing

/-- A singular point in case I has a lower level, or its Situation has a regular blowup. -/
theorem descent_of_isCaseOne (S : RationalDoublePointSituation.{u})
    (z : blowUp (maximalIdealSheaf S.A))
    (hz : z ∈ singularLocus (blowUp (maximalIdealSheaf S.A)))
    (h : IsCaseOne ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk z)) (n : ℕ) (hn : 0 < n) :
    ∃ S' : RationalDoublePointSituation.{u},
      Nonempty (S'.A ≃+* (blowUp (maximalIdealSheaf S.A)).presheaf.stalk z) ∧
      (singularLocus (blowUp (maximalIdealSheaf S'.A)) = ∅ ∨
        ∃ i < n, ∃ y : S'.A, rationalDoublePointLevel i S'.A y) := by
  obtain ⟨S', ⟨e⟩⟩ := S.exists_situation_of_mem_singularLocus_blowUp z hz
  have : IsLocalHom e.symm.toRingHom := IsLocalHom.of_surjective _ e.symm.surjective
  have h' : IsCaseOne S'.A := IsCaseOne.map e.symm.toRingHom
    (Ideal.Quotient.mk_surjective.comp e.symm.surjective) (map_ringEquiv_maximalIdeal e.symm) h
  refine ⟨S', ⟨e⟩, ?_⟩
  rcases S'.singularLocus_eq_empty_or_level_zero h' with he | ⟨g, hg⟩
  · exact Or.inl he
  · exact Or.inr ⟨0, hn, g, hg⟩

/-- **The descent at level `0`** (Section 54.12, "Resolution in case I"). If `x` is a good
coordinate of the ring of a Situation 0BGC, every singular point of the blowup has residue field
`κ`, has its exceptional divisor cut out by `x`, and has the image of `x` as a good coordinate.
The point lies on some chart, where the good coordinate generates `𝔪B`
(`AlgebraicGeometry.map_maximalIdeal_eq_span_of_isGoodCoordinate_chart`); hence it lies on the
chart of `x`, where `AlgebraicGeometry.isGoodCoordinate_localization_of_chart` applies. -/
theorem step_level_zero (S : RationalDoublePointSituation.{u}) (x : S.A)
    (hx : rationalDoublePointLevel 0 S.A x) (z : blowUp (maximalIdealSheaf S.A))
    (hz : z ∈ singularLocus (blowUp (maximalIdealSheaf S.A))) :
    Function.Surjective ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal
        ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk z))).comp
          (maximalIdealBlowUpStalkHom S.A z)) ∧
      Ideal.map (maximalIdealBlowUpStalkHom S.A z) (IsLocalRing.maximalIdeal S.A) =
        Ideal.span {maximalIdealBlowUpStalkHom S.A z x} ∧
      rationalDoublePointLevel 0 ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk z)
        (maximalIdealBlowUpStalkHom S.A z x) := by
  obtain ⟨w, a, rfl, hspan, hupper, -, hrel, hgood⟩ := hx
  have hw : ∀ i, w i ∈ IsLocalRing.maximalIdeal S.A := fun i => hspan ▸ Ideal.subset_span ⟨i, rfl⟩
  obtain ⟨j, hj⟩ := exists_memChart S.A w hspan z
  obtain ⟨M, hM, hle, hp, ε, hε, hN, -, -, hdim, hsing⟩ := S.exists_chartData _ z hz hj
  have := hM
  have := hN
  have hexc := S.map_maximalIdeal_eq_span_of_chart ε hε (w 0)
    (map_maximalIdeal_eq_span_of_isGoodCoordinate_chart w hspan a hupper hrel hgood j _ M hle
      hdim hsing)
  obtain ⟨M₀, hM₀, hle₀, hp₀, ε₀, hε₀, hN₀, -, -, hdim₀, hsing₀⟩ :=
    S.exists_chartData (hw 0) z hz (memChart_of_map_maximalIdeal_eq_span S.A (hw 0) z hexc)
  have := hM₀
  have := hN₀
  obtain ⟨hsurj, hgc⟩ := isGoodCoordinate_localization_of_chart (Localization.Away (w 0)) hw
    hspan a hupper hrel hgood M₀ hle₀ hdim₀ hsing₀
  refine ⟨S.surjective_residue_of_chart ε₀ hε₀ hle₀ hsurj, hexc, ?_⟩
  have h := rationalDoublePointLevel_ringEquiv 0 ε₀.symm _ hgc
  rwa [← hε₀, RingEquiv.symm_apply_apply] at h

/-- **Every Situation 0BGC has a regular blowup or an element at some level**: it is in case I,
which gives level `0` or a regular blowup, or in case II, which is level `3`. -/
theorem exists_rationalDoublePointLevel (S : RationalDoublePointSituation.{u}) :
    singularLocus (blowUp (maximalIdealSheaf S.A)) = ∅ ∨
      ∃ (n : ℕ) (x : S.A), rationalDoublePointLevel n S.A x := by
  rcases S.isCaseOne_or_isCaseTwo with h | h
  · rcases S.singularLocus_eq_empty_or_level_zero h with he | ⟨g, hg⟩
    · exact Or.inl he
    · exact Or.inr ⟨0, g, hg⟩
  · exact Or.inr ⟨3, 0, h, zero_mem _⟩

end RationalDoublePointSituation

end AlgebraicGeometry

end
