module

public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.Stratification
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.RingTheory.Localization.Away.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Transition maps for finite vanishing stratifications

If `E₁ ⊆ E₂` are finite subsets of a ring, restriction of a vanishing pattern on `E₂` to `E₁`
gives a canonical map between the corresponding localization rings. Taken over all patterns,
these maps give the transition morphism `X_{E₂} → X_{E₁}`, and it carries the closed subscheme
`Z_{E₂}` into `Z_{E₁}`.

## Main definitions

* `AlgebraicGeometry.ProEtale.restrictStratum`: restriction of a vanishing pattern to a smaller
  finite set.
* `AlgebraicGeometry.ProEtale.stratificationAlgebraMap`: the diagonal structure map from `A` to
  the stratification ring `A_E`.
* `AlgebraicGeometry.ProEtale.stratificationRingMap`: the canonical transition ring map.
* `AlgebraicGeometry.ProEtale.stratificationSchemeMap`: the corresponding affine scheme map.
* `AlgebraicGeometry.ProEtale.closedStratumCoordinateMap`: the transition map between the
  coordinate rings of corresponding closed strata.

## Main results

* `AlgebraicGeometry.ProEtale.locallyClosedPoints_restrictStratum` gives the inclusion of strata.
* `AlgebraicGeometry.ProEtale.stratificationRingMap_comp` and
  `AlgebraicGeometry.ProEtale.stratificationRingMap_id` give the directed system of rings.
* `AlgebraicGeometry.ProEtale.closedStrataTransition` gives the induced map on closed strata and
  its compatibility with the ambient transition map.

## Implementation notes

A decomposition of `E` is indexed by its subset of nonvanishing elements. The transition map on
each factor is the canonical localization map of a locally closed stratum. The displayed scheme
arrow is the spectrum of their product map. Its restriction to the closed subschemes is recorded
as a morphism commuting with their closed immersions, rather than merely as an inclusion of
underlying sets.

## References

* [Stacks Project, Tag 0972](https://stacks.math.columbia.edu/tag/0972)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProEtale

variable {A : Type u} [CommRing A]

/-- Restrict the nonvanishing elements of a stratum of `E₂` to `E₁`. -/
def restrictStratum (E₁ E₂ : Finset A) (_h : E₁ ⊆ E₂)
    (i : {E' : Finset A // E' ⊆ E₂}) : {E' : Finset A // E' ⊆ E₁} :=
  by
    classical
    exact ⟨E₁ ∩ i.val, Finset.inter_subset_left⟩

/-- The stratum ideal of the restriction to `E₁` of a vanishing pattern on `E₂` is contained in
the stratum ideal of the original pattern. -/
theorem stratumIdeal_le (E₁ E₂ : Finset A) (h : E₁ ⊆ E₂)
    (i : {E' : Finset A // E' ⊆ E₂}) :
    stratumIdeal E₁ (restrictStratum E₁ E₂ h i) ≤ stratumIdeal E₂ i := by
  classical
  apply Ideal.span_mono
  intro x hx
  change x ∈ E₁ \ (E₁ ∩ i.val) at hx
  change x ∈ E₂ \ i.val
  simp only [Finset.mem_sdiff, Finset.mem_inter] at hx ⊢
  exact ⟨h hx.1, fun hxi => hx.2 ⟨hx.1, hxi⟩⟩

/-- Restriction of a vanishing pattern carries its locally closed stratum
into the corresponding stratum for the smaller finite set. -/
@[stacks 0972 "inclusion of strata"]
theorem locallyClosedPoints_restrictStratum (E₁ E₂ : Finset A)
    (h : E₁ ⊆ E₂) (i : {E' : Finset A // E' ⊆ E₂})
    (q : PrimeSpectrum A)
    (hq : q ∈ locallyClosedPoints
      (stratumIdeal E₂ i) (stratumOpenElement i.val)) :
    q ∈ locallyClosedPoints
      (stratumIdeal E₁ (restrictStratum E₁ E₂ h i))
      (stratumOpenElement (restrictStratum E₁ E₂ h i).val) := by
  classical
  change stratumIdeal E₁ (restrictStratum E₁ E₂ h i) ≤ q.asIdeal ∧
    stratumOpenElement (restrictStratum E₁ E₂ h i).val ∉ q.asIdeal
  change stratumIdeal E₂ i ≤ q.asIdeal ∧
    stratumOpenElement i.val ∉ q.asIdeal at hq
  refine ⟨(stratumIdeal_le E₁ E₂ h i).trans hq.1, ?_⟩
  · change (E₁ ∩ i.val).prod id ∉ q.asIdeal
    intro hprod
    obtain ⟨x, hx, hxq⟩ := q.isPrime.prod_mem_iff.mp hprod
    simp only [Finset.mem_inter] at hx
    apply hq.2
    change i.val.prod id ∈ q.asIdeal
    exact q.isPrime.prod_mem_iff.mpr ⟨x, hx.2, hxq⟩

/-- The diagonal structure map from `A` to the product of its stratum localizations. -/
def stratificationAlgebraMap (E : Finset A) : A →+* stratificationRing E :=
  RingHom.pi (fun i => algebraMap A
    (localizationRing (stratumIdeal E i) (stratumOpenElement i.val)))

/-- The canonical transition map `A_{E₁} → A_{E₂}` for `E₁ ⊆ E₂`. -/
@[stacks 0972 "the transition ring map"]
def stratificationRingMap (E₁ E₂ : Finset A) (h : E₁ ⊆ E₂) :
    stratificationRing E₁ →+* stratificationRing E₂ :=
  RingHom.pi (fun i =>
    (localizationMap (RingHom.id A)
      (stratumIdeal E₁ (restrictStratum E₁ E₂ h i))
      (stratumOpenElement (restrictStratum E₁ E₂ h i).val)
      (stratumIdeal E₂ i)
      (stratumOpenElement i.val)
      (by
        intro q hq
        simpa only [PrimeSpectrum.comap_id] using
          locallyClosedPoints_restrictStratum E₁ E₂ h i q hq)).comp
      (Pi.evalRingHom (fun j : {E' : Finset A // E' ⊆ E₁} =>
        localizationRing (stratumIdeal E₁ j) (stratumOpenElement j.val))
        (restrictStratum E₁ E₂ h i)))

omit [CommRing A] in
private theorem restrictStratum_refl (E : Finset A)
    (i : {E' : Finset A // E' ⊆ E}) :
    restrictStratum E E (Finset.Subset.refl E) i = i := by
  classical
  apply Subtype.ext
  simp [restrictStratum, Finset.inter_eq_right.mpr i.property]

omit [CommRing A] in
private theorem restrictStratum_comp (E₁ E₂ E₃ : Finset A)
    (h₁₂ : E₁ ⊆ E₂) (h₂₃ : E₂ ⊆ E₃)
    (i : {E' : Finset A // E' ⊆ E₃}) :
    restrictStratum E₁ E₂ h₁₂ (restrictStratum E₂ E₃ h₂₃ i) =
      restrictStratum E₁ E₃ (h₁₂.trans h₂₃) i := by
  classical
  apply Subtype.ext
  simp only [restrictStratum]
  ext x
  simp only [Finset.mem_inter]
  constructor
  · rintro ⟨hx₁, -, hxi⟩
    exact ⟨hx₁, hxi⟩
  · rintro ⟨hx₁, hxi⟩
    exact ⟨hx₁, h₁₂ hx₁, hxi⟩

private theorem localizationMap_id_cast {R : Type u} [CommRing R]
    (M N : Submonoid R) (h : M = N) (hm : M ≤ N.comap (RingHom.id R))
    (x : Localization M) :
    IsLocalization.map (Localization N) (RingHom.id R) hm x =
      cast (congrArg (fun S : Submonoid R => Localization S) h) x := by
  subst N
  simp

private theorem localizationMap_id_source_cast {R : Type u} [CommRing R]
    (M N T : Submonoid R) (h : M = N)
    (hM : M ≤ T.comap (RingHom.id R)) (hN : N ≤ T.comap (RingHom.id R))
    (x : Localization M) :
    IsLocalization.map (Localization T) (RingHom.id R) hN
        (cast (congrArg (fun S : Submonoid R => Localization S) h) x) =
      IsLocalization.map (Localization T) (RingHom.id R) hM x := by
  subst N
  rfl

universe v w

/-- Casting the value `x i` of a dependent function along `i = j` gives `x j`. -/
theorem dependentSection_cast {ι : Sort v} {β : ι → Sort w}
    (x : ∀ i, β i) {i j : ι} (h : i = j) :
    cast (congrArg β h) (x i) = x j := by
  cases h
  rfl

/-- The transition map between the coordinate rings of the closed strata attached to
corresponding vanishing patterns. -/
noncomputable def closedStratumCoordinateMap (E₁ E₂ : Finset A)
    (h : E₁ ⊆ E₂) (i : {E' : Finset A // E' ⊆ E₂}) :
    stratumCoordinateRing E₁ (restrictStratum E₁ E₂ h i) →+*
      stratumCoordinateRing E₂ i := by
  classical
  let j := restrictStratum E₁ E₂ h i
  let I₁ := stratumIdeal E₁ j
  let I₂ := stratumIdeal E₂ i
  let f₁ := stratumOpenElement j.val
  let f₂ := stratumOpenElement i.val
  let q : A ⧸ I₁ →+* A ⧸ I₂ := Ideal.Quotient.factor (stratumIdeal_le E₁ E₂ h i)
  let f : A ⧸ I₁ →+* stratumCoordinateRing E₂ i :=
    (algebraMap (A ⧸ I₂) (stratumCoordinateRing E₂ i)).comp q
  have hsubset : j.val ⊆ i.val := by
    intro x hx
    change x ∈ E₁ ∩ i.val at hx
    simp only [Finset.mem_inter] at hx
    exact hx.2
  have hdiv : (Ideal.Quotient.mk I₂ f₁) ∣ (Ideal.Quotient.mk I₂ f₂) := by
    refine ⟨∏ x ∈ i.val \ j.val, Ideal.Quotient.mk I₂ x, ?_⟩
    have hp := Finset.prod_sdiff hsubset (f := fun x => Ideal.Quotient.mk I₂ x)
    simpa [f₁, f₂, stratumOpenElement, mul_comm] using hp.symm
  have hunit : IsUnit (f (Ideal.Quotient.mk I₁ f₁)) := by
    dsimp [f, q]
    exact IsLocalization.Away.isUnit_of_dvd (x := Ideal.Quotient.mk I₂ f₂)
      (r := Ideal.Quotient.mk I₂ f₁) hdiv
  exact Localization.awayLift f (Ideal.Quotient.mk I₁ f₁) hunit

private theorem closedStratumCoordinateMap_comp_algebraMap (E₁ E₂ : Finset A)
    (h : E₁ ⊆ E₂) (i : {E' : Finset A // E' ⊆ E₂}) :
    (closedStratumCoordinateMap E₁ E₂ h i).comp
        (algebraMap (A ⧸ stratumIdeal E₁ (restrictStratum E₁ E₂ h i))
          (stratumCoordinateRing E₁ (restrictStratum E₁ E₂ h i))) =
      (algebraMap (A ⧸ stratumIdeal E₂ i) (stratumCoordinateRing E₂ i)).comp
      (Ideal.Quotient.factor (stratumIdeal_le E₁ E₂ h i)) := by
  simp [closedStratumCoordinateMap, Localization.awayLift, IsLocalization.Away.lift_comp]

/-- The transition map between closed-stratum coordinate rings commutes with the maps from the
stratum localizations and the transition map between those localizations. -/
theorem closedStratumCoordinateMap_comp_localizationToCoordinateRing
    (E₁ E₂ : Finset A) (h : E₁ ⊆ E₂)
    (i : {E' : Finset A // E' ⊆ E₂}) :
    (closedStratumCoordinateMap E₁ E₂ h i).comp
        (localizationToCoordinateRing
          (stratumIdeal E₁ (restrictStratum E₁ E₂ h i))
          (stratumOpenElement (restrictStratum E₁ E₂ h i).val)) =
      (localizationToCoordinateRing (stratumIdeal E₂ i)
        (stratumOpenElement i.val)).comp
        (localizationMap (RingHom.id A)
          (stratumIdeal E₁ (restrictStratum E₁ E₂ h i))
          (stratumOpenElement (restrictStratum E₁ E₂ h i).val)
          (stratumIdeal E₂ i) (stratumOpenElement i.val)
          (by
            intro q hq
            simpa only [PrimeSpectrum.comap_id] using
              locallyClosedPoints_restrictStratum E₁ E₂ h i q hq)) := by
  classical
  let I₁ := stratumIdeal E₁ (restrictStratum E₁ E₂ h i)
  let I₂ := stratumIdeal E₂ i
  let f₁ := stratumOpenElement (restrictStratum E₁ E₂ h i).val
  let f₂ := stratumOpenElement i.val
  let L₁ := localizationRing I₁ f₁
  let L₂ := localizationRing I₂ f₂
  let C₁ := stratumCoordinateRing E₁ (restrictStratum E₁ E₂ h i)
  let C₂ := stratumCoordinateRing E₂ i
  let loc₁ := localizationToCoordinateRing I₁ f₁
  let loc₂ := localizationToCoordinateRing I₂ f₂
  let map₁₂ := localizationMap (RingHom.id A) I₁ f₁ I₂ f₂ (by
    intro q hq
    simpa only [PrimeSpectrum.comap_id] using
      locallyClosedPoints_restrictStratum E₁ E₂ h i q hq)
  let q₁₂ := Ideal.Quotient.factor (stratumIdeal_le E₁ E₂ h i)
  have hloc₁ : loc₁.comp (algebraMap A L₁) =
      (algebraMap (A ⧸ I₁) C₁).comp (Ideal.Quotient.mk I₁) := by
    change (localizationToCoordinateRing I₁ f₁).comp (algebraMap A L₁) = _
    calc
      _ = locallyClosedCoordinateMap I₁ f₁ := by
        unfold localizationToCoordinateRing
        exact IsLocalization.lift_comp (fun s => s.property)
      _ = _ := rfl
  have hloc₂ : loc₂.comp (algebraMap A L₂) =
      (algebraMap (A ⧸ I₂) C₂).comp (Ideal.Quotient.mk I₂) := by
    change (localizationToCoordinateRing I₂ f₂).comp (algebraMap A L₂) = _
    calc
      _ = locallyClosedCoordinateMap I₂ f₂ := by
        unfold localizationToCoordinateRing
        exact IsLocalization.lift_comp (fun s => s.property)
      _ = _ := rfl
  have hmap : map₁₂.comp (algebraMap A L₁) = algebraMap A L₂ := by
    have hsel := localizationSubmonoid_le_comap (RingHom.id A) I₁ f₁ I₂ f₂ (by
        intro q hq
        simpa only [PrimeSpectrum.comap_id] using
          locallyClosedPoints_restrictStratum E₁ E₂ h i q hq)
    ext a
    change IsLocalization.map L₂ (RingHom.id A) hsel (algebraMap A L₁ a) = _
    simp
  apply IsLocalization.ringHom_ext (localizationSubmonoid I₁ f₁)
  calc
    ((closedStratumCoordinateMap E₁ E₂ h i).comp loc₁).comp (algebraMap A L₁) =
        ((algebraMap (A ⧸ I₂) C₂).comp q₁₂).comp (Ideal.Quotient.mk I₁) := by
      rw [RingHom.comp_assoc, hloc₁, ← RingHom.comp_assoc,
        closedStratumCoordinateMap_comp_algebraMap]
    _ = (algebraMap (A ⧸ I₂) C₂).comp (Ideal.Quotient.mk I₂) := by
      rw [RingHom.comp_assoc]
      ext a
      apply congrArg (algebraMap (A ⧸ I₂) C₂)
      exact Ideal.Quotient.factor_mk (stratumIdeal_le E₁ E₂ h i) a
    _ = (loc₂.comp map₁₂).comp (algebraMap A L₁) := by
      rw [RingHom.comp_assoc, hmap, hloc₂]

/-- The transition maps respect the structure maps from `A`. -/
@[stacks 0972 "A-algebra compatibility"]
theorem stratificationRingMap_comp_algebraMap (E₁ E₂ : Finset A) (h : E₁ ⊆ E₂) :
    (stratificationRingMap E₁ E₂ h).comp (stratificationAlgebraMap E₁) =
      stratificationAlgebraMap E₂ := by
  classical
  ext x i
  simp only [RingHom.comp_apply, stratificationRingMap, stratificationAlgebraMap,
    RingHom.pi_apply]
  simp [localizationMap]

/-- The transition map for an identity inclusion is the identity. -/
@[stacks 0972 "identity transition"]
theorem stratificationRingMap_id (E : Finset A) :
    stratificationRingMap E E (Finset.Subset.refl E) = RingHom.id _ := by
  classical
  ext x i
  let j := restrictStratum E E (Finset.Subset.refl E) i
  have hji : j = i := restrictStratum_refl E i
  let M : {E' : Finset A // E' ⊆ E} → Submonoid A := fun k =>
    localizationSubmonoid (stratumIdeal E k) (stratumOpenElement k.val)
  have hM : M j = M i := congrArg M hji
  simp only [stratificationRingMap, RingHom.pi_apply, RingHom.comp_apply]
  change IsLocalization.map (Localization (M i)) (RingHom.id A) _ (x j) = x i
  rw [localizationMap_id_cast (M j) (M i) hM]
  exact dependentSection_cast (fun k => x k) hji

/-- The transition maps compose for a chain of finite subsets. -/
@[stacks 0972 "composition of transitions"]
theorem stratificationRingMap_comp (E₁ E₂ E₃ : Finset A)
    (h₁₂ : E₁ ⊆ E₂) (h₂₃ : E₂ ⊆ E₃) :
    (stratificationRingMap E₂ E₃ h₂₃).comp (stratificationRingMap E₁ E₂ h₁₂) =
      stratificationRingMap E₁ E₃ (h₁₂.trans h₂₃) := by
  classical
  ext x i
  let j₂ := restrictStratum E₂ E₃ h₂₃ i
  let j₁ := restrictStratum E₁ E₂ h₁₂ j₂
  let j₁₃ := restrictStratum E₁ E₃ (h₁₂.trans h₂₃) i
  have hj : j₁ = j₁₃ := restrictStratum_comp E₁ E₂ E₃ h₁₂ h₂₃ i
  simp only [stratificationRingMap, localizationMap, RingHom.comp_apply, RingHom.pi_apply,
    Pi.evalRingHom_apply]
  rw [IsLocalization.map_map]
  simp only [RingHom.id_comp]
  let M₁ : {E' : Finset A // E' ⊆ E₁} → Submonoid A := fun k =>
    localizationSubmonoid (stratumIdeal E₁ k) (stratumOpenElement k.val)
  let M₃ : {E' : Finset A // E' ⊆ E₃} → Submonoid A := fun k =>
    localizationSubmonoid (stratumIdeal E₃ k) (stratumOpenElement k.val)
  have hM : M₁ j₁ = M₁ j₁₃ := congrArg M₁ hj
  have hx : cast (congrArg (fun k => Localization (M₁ k)) hj) (x j₁) = x j₁₃ :=
    dependentSection_cast (fun k => x k) hj
  rw [← hx]
  change IsLocalization.map (Localization (M₃ i)) (RingHom.id A) _ (x j₁) =
    IsLocalization.map (Localization (M₃ i)) (RingHom.id A) _
      (cast (congrArg (fun S : Submonoid A => Localization S) hM) (x j₁))
  exact (localizationMap_id_source_cast (M₁ j₁) (M₁ j₁₃) (M₃ i) hM _ _ (x j₁)).symm

/-- The corresponding transition arrow `X_{E₂} → X_{E₁}`. -/
@[stacks 0972 "the scheme morphism"]
def stratificationSchemeMap (E₁ E₂ : Finset A) (h : E₁ ⊆ E₂) :
    Spec (.of (stratificationRing E₂)) ⟶ Spec (.of (stratificationRing E₁)) :=
  Spec.map (CommRingCat.ofHom (stratificationRingMap E₁ E₂ h))

/-- The transition arrow restricts to a morphism `Z_{E₂} → Z_{E₁}` of
closed subschemes, commuting with their inclusions into the affine schemes. -/
@[stacks 0972 "transition on closed strata"]
def closedStrataTransition (E₁ E₂ : Finset A) (h : E₁ ⊆ E₂) :
    {g : closedStrata E₂ ⟶ closedStrata E₁ //
      g ≫ closedStrataMap E₁ = closedStrataMap E₂ ≫ stratificationSchemeMap E₁ E₂ h} := by
  classical
  let F₁ : {E' : Finset A // E' ⊆ E₁} → Scheme.{u} := fun j =>
    Spec (.of (stratumCoordinateRing E₁ j))
  let F₂ : {E' : Finset A // E' ⊆ E₂} → Scheme.{u} := fun i =>
    Spec (.of (stratumCoordinateRing E₂ i))
  have h₁ : (∐ F₁) = closedStrata E₁ := by rfl
  have h₂ : (∐ F₂) = closedStrata E₂ := by rfl
  let g : closedStrata E₂ ⟶ closedStrata E₁ :=
    eqToHom h₂.symm ≫
      Sigma.desc (fun i =>
        Spec.map (CommRingCat.ofHom (closedStratumCoordinateMap E₁ E₂ h i)) ≫
          Sigma.ι F₁ (restrictStratum E₁ E₂ h i)) ≫
      eqToHom h₁
  refine ⟨g, ?_⟩
  apply (cancel_epi (eqToHom h₂)).mp
  apply Sigma.hom_ext
  intro i
  simp only [closedStrata, eqToHom_naturality, eqToHom_refl, Category.id_comp,
    closedStrataMap, Category.assoc, eqToHom_naturality_assoc, colimit.ι_desc_assoc,
    Discrete.functor_obj_eq_as, Cofan.mk_pt, Cofan.mk_ι_app, Sigma.ι_comp_desc, F₂, g]
  rw [stratificationSchemeMap]
  simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  apply CommRingCat.hom_ext
  change (closedStratumCoordinateMap E₁ E₂ h i).comp
      ((localizationToCoordinateRing
          (stratumIdeal E₁ (restrictStratum E₁ E₂ h i))
          (stratumOpenElement (restrictStratum E₁ E₂ h i).val)).comp
        (Pi.evalRingHom (fun E' : {E' : Finset A // E' ⊆ E₁} =>
          localizationRing (stratumIdeal E₁ E') (stratumOpenElement E'.val))
          (restrictStratum E₁ E₂ h i))) =
    (localizationToCoordinateRing
        (stratumIdeal E₂ i) (stratumOpenElement i.val)).comp
      ((Pi.evalRingHom (fun E' : {E' : Finset A // E' ⊆ E₂} =>
          localizationRing (stratumIdeal E₂ E') (stratumOpenElement E'.val)) i).comp
        (stratificationRingMap E₁ E₂ h))
  rw [← RingHom.comp_assoc,
    closedStratumCoordinateMap_comp_localizationToCoordinateRing,
    RingHom.comp_assoc]
  congr 1

end AlgebraicGeometry.ProEtale

end
