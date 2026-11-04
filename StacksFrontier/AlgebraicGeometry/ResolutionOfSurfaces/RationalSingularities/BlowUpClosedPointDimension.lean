module

public import StacksFrontier.AlgebraicGeometry.Blowup.FiniteOverLocalDimensionOne
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Birational
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.DimensionFormula
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.ModificationIsolatedFibrePoint
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalCurve
public import StacksFrontier.AlgebraicGeometry.Surfaces.BlowUpNormality
public import StacksFrontier.Topology.Irreducible.SingletonComponent
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalIdealPowersExtra

/-!
# The local ring at a closed point of the blowup of a surface singularity

Let `(A, 𝔪)` be a two-dimensional Noetherian local normal domain, let `X` be the blowup of
`Spec(A)` in `𝔪` and let `x` be a **closed** point of `X`. Then `dim 𝒪_{X, x} = 2`.

## Main results

* `AlgebraicGeometry.ringKrullDim_stalk_blowUp_maximalIdeal_eq_two_of_isClosed`.

## Implementation notes

No `@[stacks]` attribute is attached: this is the local dimension at an arbitrary closed point of
the exceptional fibre, and no tag of the source states it. Section 54.7 records the dimension of
the components of the special fibre, [Stacks, Tag 0B63] the dimension of the exceptional curve,
and [Stacks, Tag 0BAE] the dimension formula from which the upper bound comes; the statement
below is the one its consumers need — the two-dimensionality of the local ring at the point at
which the next blowup of a sequence of blowups at closed points is performed — and it is none of
those.

The upper bound is `AlgebraicGeometry.ringKrullDim_stalk_blowUp_residuePoint_le_two`, the
dimension formula on the blowup; it holds at every point. The lower bound is a chain of two
specializations into `x`, which
`AlgebraicGeometry.ringKrullDim_stalk_ge_two_of_specialization_chain` converts into the bound.
Building the chain is where closedness of `x` enters, and it is built in the special fibre:
the blowup morphism is proper, so `x` lies over the closed point `s` of `Spec(A)` and is a closed
point of the fibre `X_s`; the generic point `η` of the irreducible component of `X_s` through `x`
and the generic point of `X` are then the other two members of the chain — the latter does not
lie over `s`, the blowup being birational and `Spec(A)` of dimension two.

That leaves the case `η = x`, in which the component is the single point `x`. It is the case the
source discards, and it is not vacuous here: it says exactly that `x` is isolated in `X_s`, which
by Zariski's main theorem over a local base
(`AlgebraicGeometry.IsModification.isIso_of_isOpen_singleton_fiber`) makes the blowup morphism an
isomorphism. The conclusion then holds for a different reason — the stalk is `A` itself, of
dimension two — so the case needs no exclusion, and the statement carries no hypothesis on the
fibre. This is why the special fibre is used in place of the exceptional divisor: the Zariski
step is stated for the fibre. The two *are* identified in this library — as a pullback square by
`AlgebraicGeometry.isPullback_exceptionalToCentre` of `Blowup/ExceptionalDifferentials.lean`, at
the level of ideal sheaves by
`AlgebraicGeometry.RationalSingularitySituation.exceptionalIdeal_eq_comap` of
`…/RationalSingularities/ExceptionalIdealPowers.lean`, and topologically by
`AlgebraicGeometry.BlowUpDualizing.range_exceptionalImmersion` of
`…/RationalSingularities/BlowUpDualizingGeneration.lean` — but each at the `ker`/`fiberι`
spelling of the centre, whereas the statements below spell it as
`AlgebraicGeometry.maximalIdealSheaf`, so crossing to them would go through
`vanishingIdeal_closedPoint_eq_maximalIdealSheaf`.

The centre of the blowup is spelled as the ideal sheaf generated over the whole space by the
image of `𝔪`, which is `AlgebraicGeometry.maximalIdealSheaf` and the spelling of the normality
results about this blowup. A consumer holding the other spelling — the vanishing ideal of the
closed point, which is the centre of a stage of a sequence of blowups at closed points — crosses
over by `AlgebraicGeometry.vanishingIdeal_closedPoint_eq_maximalIdealSheaf`, which must be
rewritten into the goal rather than into the statement below: the point of the blowup and the
proof that it is closed both depend on the centre, so rewriting the hypothesis produces an
ill-typed motive, while `revert x hx` followed by the rewrite does not.

## References

* [Stacks Project, Tag 0B63](https://stacks.math.columbia.edu/tag/0B63)
* [Stacks Project, Tag 0BAE](https://stacks.math.columbia.edu/tag/0BAE)
* [Stacks Project, Tag 0AX8](https://stacks.math.columbia.edu/tag/0AX8)
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A chain of two proper specializations into `x₂` forces the local ring at `x₂` to have
dimension at least two: its dimension is the coheight of `x₂` in the specialization order. -/
private theorem two_le_ringKrullDim_stalk_of_specializes_of_specializes {X : Scheme.{u}}
    {x₀ x₁ x₂ : X} (h₀₁ : x₀ ⤳ x₁) (h₁₂ : x₁ ⤳ x₂) (hne₀₁ : x₀ ≠ x₁) (hne₁₂ : x₁ ≠ x₂) :
    2 ≤ ringKrullDim (X.presheaf.stalk x₂) := by
  have hlt : ∀ {a b : X}, a ⤳ b → a ≠ b → b < a := fun h hne =>
    lt_of_le_not_ge (Scheme.le_iff_specializes.mpr h)
      fun h' => hne (h.antisymm (Scheme.le_iff_specializes.mp h')).eq
  have hco : (2 : ℕ∞) ≤ Order.coheight x₂ :=
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ Order.coheight x₀ + 1 + 1 := by gcongr; exact bot_le
      _ ≤ Order.coheight x₁ + 1 := by gcongr; exact Order.coheight_add_one_le (hlt h₀₁ hne₀₁)
      _ ≤ Order.coheight x₂ := Order.coheight_add_one_le (hlt h₁₂ hne₁₂)
  rw [ringKrullDim_stalk_eq_coheight]
  simpa using WithBot.coe_le_coe.mpr hco

/-- An isomorphism of schemes preserves the dimension of the local rings. -/
theorem ringKrullDim_stalk_eq_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (x : X) :
    ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (f x)) := by
  have : IsIso (f.stalkMap x) := ((isIso_iff_isIso_stalkMap f).mp ‹_›).2 x
  exact (ringKrullDim_eq_of_ringEquiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv).symm

/-- The generic point of the spectrum of a two-dimensional local domain is not its closed
point. -/
theorem genericPoint_ne_closedPoint_of_ringKrullDim_eq_two (A : Type u) [CommRing A]
    [IsLocalRing A] [IsDomain A] (hdim : ringKrullDim A = 2) :
    genericPoint (Spec (.of A)) ≠ IsLocalRing.closedPoint A := by
  intro h
  refine maximalIdeal_ne_bot_of_dimension_two A hdim ?_
  have hbot : (IsLocalRing.closedPoint A : PrimeSpectrum A) = (⊥ : PrimeSpectrum A) := by
    rw [← h]
    exact genericPoint_eq_bot_of_affine (.of A)
  simpa [IsLocalRing.closedPoint] using congrArg PrimeSpectrum.asIdeal hbot

/-- A point of the spectrum of a local ring which is closed is the closed point. -/
theorem eq_closedPoint_of_isClosed_singleton {A : Type u} [CommRing A] [IsLocalRing A]
    {y : Spec (.of A)} (hy : IsClosed {y}) : y = IsLocalRing.closedPoint A :=
  (Set.mem_singleton_iff.mp ((IsLocalRing.specializes_closedPoint y).mem_closed hy rfl)).symm

/-- A modification of the spectrum of a Noetherian normal local domain whose fibre over the
closed point has a one-point irreducible component is an isomorphism. -/
theorem IsModification.isIso_of_singleton_mem_irreducibleComponents_fiber {A : Type u}
    [CommRing A] [IsLocalRing A] [IsNormalDomain A] [IsNoetherianRing A] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of A)} (hf : IsModification f) (p : f.fiber (IsLocalRing.closedPoint A))
    (hp : ({p} : Set (f.fiber (IsLocalRing.closedPoint A))) ∈
      irreducibleComponents (f.fiber (IsLocalRing.closedPoint A))) :
    IsIso f := by
  have : IsProper f := hf.isProper
  have := finite_irreducibleComponents_fiber_closedPoint A f
  exact hf.isIso_of_isOpen_singleton_fiber p
    (Stacks.Topology.Irreducible.isOpen_singleton_of_mem_irreducibleComponents
      (Set.toFinite _) p hp)

open Stacks.Blowup in
/-- **The local rings of the blowup of the spectrum of a two-dimensional Noetherian local domain
in its maximal ideal have dimension at most two.**

The general dimension formula [Stacks, Tag 0BAE] bounds `dim 𝒪_{X, x} + trdeg_{κ(f x)} κ(x)` by
`dim 𝒪_{S, f x}` plus a correction term which vanishes because the blowup morphism is birational
— the blowup of an integral scheme in a nonzero ideal, the maximal ideal being nonzero in
dimension two — and `dim 𝒪_{S, f x}` is the height of the prime of `f x`, at most the dimension
`2` of `A`. -/
theorem ringKrullDim_stalk_blowUp_residuePoint_le_two (A : Type u) [CommRing A] [IsLocalRing A]
    [IsDomain A] [IsNoetherianRing A] (hdim : ringKrullDim A = 2)
    (x : blowUp (residuePoint A).ker) :
    ringKrullDim ((blowUp (residuePoint A).ker).presheaf.stalk x) ≤ 2 := by
  let I : (Spec (.of A)).IdealSheafData := (residuePoint A).ker
  let f : blowUp I ⟶ Spec (.of A) := blowUpToBase I
  have hIne : I ≠ ⊥ := ker_residuePoint_ne_bot A hdim
  have : IsIntegral (blowUp I) := isIntegral_blowUp I hIne
  have : LocallyOfFiniteType f := (isProper_blowUpToBase I).toLocallyOfFiniteType
  have hformula := ringKrullDim_stalk_add_residueFieldTranscendenceDegree_le f x
  rw [genericResidueFieldTranscendenceDegreeAt_eq_zero f
    (isBirational_blowUpToBase I hIne) x] at hformula
  have hbase : ringKrullDim ((Spec (.of A)).presheaf.stalk (f x)) ≤ 2 := by
    let q : PrimeSpectrum A := f x
    have hdimSpec : ringKrullDim ((Spec (.of A)).presheaf.stalk (f x)) =
        (q.asIdeal.height : WithBot ℕ∞) := by
      rw [ringKrullDim_eq_of_ringEquiv
          (Spec.stalkIso (.of A) (f x)).commRingCatIsoToRingEquiv,
        IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal]
    rw [hdimSpec]
    calc ((q.asIdeal.height : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim A := by
          simpa only [ringKrullDim] using
            Ideal.height_le_ringKrullDim_of_ne_top q.isPrime.ne_top
      _ = 2 := hdim
  calc ringKrullDim ((blowUp I).presheaf.stalk x)
      ≤ ringKrullDim ((blowUp I).presheaf.stalk x) +
          (residueFieldTranscendenceDegree f x : WithBot ℕ∞) :=
        le_add_of_nonneg_right (WithBot.coe_le_coe.mpr zero_le)
    _ ≤ ringKrullDim ((Spec (.of A)).presheaf.stalk (f x)) := by simpa using hformula
    _ ≤ 2 := hbase

/-- **The local ring at a closed point of the blowup of the spectrum of a two-dimensional
Noetherian local normal domain in its maximal ideal has dimension two.**

The upper bound is the dimension formula [Stacks, Tag 0BAE] and holds at every point. For the
lower bound, properness puts `x` in the fibre over the closed point and makes it a closed point
of that fibre; the generic point of the irreducible component of the fibre through `x`, and the
generic point of the blowup, complete a chain of two proper specializations into `x`. If instead
that component is the single point `x`, then `x` is isolated in the fibre and Zariski's main
theorem makes the blowup morphism an isomorphism, so that the stalk at `x` is `A`. -/
theorem ringKrullDim_stalk_blowUp_maximalIdeal_eq_two_of_isClosed (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNormalDomain A] [IsNoetherianRing A] (hdim : ringKrullDim A = 2)
    (x : blowUp (Scheme.IdealSheafData.ofIdealTop
      (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (IsLocalRing.maximalIdeal A))))
    (hx : IsClosed ({x} : Set (blowUp (Scheme.IdealSheafData.ofIdealTop
      (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (IsLocalRing.maximalIdeal A)))))) :
    ringKrullDim ((blowUp (Scheme.IdealSheafData.ofIdealTop
      (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom
        (IsLocalRing.maximalIdeal A)))).presheaf.stalk x) = 2 := by
  classical
  let I : (Spec (.of A)).IdealSheafData := Scheme.IdealSheafData.ofIdealTop
    (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (IsLocalRing.maximalIdeal A))
  let f : blowUp I ⟶ Spec (.of A) := blowUpToBase I
  have hmod : IsModification f := isModification_blowUpToBase_maximalIdeal A hdim
  have : IsIntegral (blowUp I) := isIntegral_blowUp_maximalIdeal A hdim
  have : IsProper f := hmod.isProper
  have : LocallyOfFiniteType f := ‹IsProper f›.toLocallyOfFiniteType
  have : IsLocallyNoetherian (blowUp I) := LocallyOfFiniteType.isLocallyNoetherian f
  have hle := ringKrullDim_stalk_blowUp_residuePoint_le_two A hdim
  rw [ker_residuePoint_eq_ofIdealTop_map A] at hle
  refine le_antisymm (hle x) ?_
  have hfx : f x = IsLocalRing.closedPoint A :=
    eq_closedPoint_of_isClosed_singleton (by simpa using f.isClosedMap _ hx)
  let ι := f.fiberι (IsLocalRing.closedPoint A)
  have hinj : Function.Injective ι :=
    (f.fiberι _).isEmbedding.injective
  obtain ⟨p, hp⟩ : ∃ p : f.fiber (IsLocalRing.closedPoint A),
      ι p = x :=
    (f.range_fiberι (IsLocalRing.closedPoint A)).ge (Set.mem_singleton_iff.mpr hfx)
  have hpclosed : IsClosed ({p} : Set (f.fiber (IsLocalRing.closedPoint A))) := by
    rw [← hinj.preimage_image {p}, Set.image_singleton, hp]
    exact hx.preimage ι.continuous
  have hCmem : irreducibleComponent p ∈
      irreducibleComponents (f.fiber (IsLocalRing.closedPoint A)) :=
    irreducibleComponent_mem_irreducibleComponents p
  have hgen : IsGenericPoint hCmem.1.genericPoint (irreducibleComponent p) :=
    hCmem.1.isGenericPoint_genericPoint isClosed_irreducibleComponent
  by_cases hη : hCmem.1.genericPoint = p
  · have hCsingle : irreducibleComponent p = {p} := by
      rw [← hgen, hη]
      exact hpclosed.closure_eq
    have : IsIso f := hmod.isIso_of_singleton_mem_irreducibleComponents_fiber p
      (hCsingle ▸ hCmem)
    have heq := ringKrullDim_stalk_eq_of_isIso f x
    rw [hfx, ringKrullDim_stalk_closedPoint, hdim] at heq
    exact heq.ge
  · have hmid : ι hCmem.1.genericPoint ⤳ x :=
      hp ▸ (hgen.specializes mem_irreducibleComponent).map
        ι.continuous
    have hmidne : ι hCmem.1.genericPoint ≠ x := fun he =>
      hη (hinj (he.trans hp.symm))
    have htopne : genericPoint (blowUp I) ≠
        ι hCmem.1.genericPoint := fun he =>
      genericPoint_ne_closedPoint_of_ringKrullDim_eq_two A hdim <| by
        rw [← IsBirational.genericPoint_eq f hmod.isBirational, he]
        exact f.apply_fiberι (IsLocalRing.closedPoint A) hCmem.1.genericPoint
    exact two_le_ringKrullDim_stalk_of_specializes_of_specializes (genericPoint_specializes _)
      hmid htopne hmidne

end AlgebraicGeometry

end

end
