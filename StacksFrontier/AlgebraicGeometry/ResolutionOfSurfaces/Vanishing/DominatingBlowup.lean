module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Blowup.DominatedByBlowup
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Stability
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.HigherCodimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.GeneralDimensionFormula
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.BirationalIsIso
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.Basic

/-!
# A blowup of the punctured spectrum dominating the modification

In the vanishing situation of [Stacks, Tag 0AX8] — a two-dimensional Noetherian normal local
domain `A` and a modification `f : X ⟶ S = Spec(A)` — the morphism `f` is an isomorphism over
the punctured spectrum `U = S ∖ {s}`, and therefore some `U`-admissible blowup of `S` factors
through `X`.

## Main results

* `AlgebraicGeometry.VanishingSituation.isIso_morphismRestrict_puncturedSpectrumOpen`: the
  modification is an isomorphism over the punctured spectrum.
* `AlgebraicGeometry.VanishingSituation.exists_isAdmissibleBlowup_dominating`: a `U`-admissible
  blowup dominating `X`, from the two inputs of the general domination lemma. With those inputs
  supplied, [Stacks, Tag 0B4M] is
  `AlgebraicGeometry.VanishingSituation.exists_isAdmissibleBlowup_dominating_of_noetherian`
  (`StacksFrontier/AlgebraicGeometry/Flatness/Flattening/StrictTransformOpenImmersion.lean`).

## The isomorphism over the punctured spectrum

The source asserts this in the discussion following Situation [Stacks, Tag 0AX8], by the
codimension-one clause of [Stacks, Tag 0BFP]. That clause is not available here — only the
finite-fibre and quasi-finite-point clauses of 0BFP are, and both *consume* the finiteness that
the codimension-one clause supplies — so the argument is run directly instead.

A point `u ≠ s` of `S` is a prime strictly below the maximal ideal, so its height is at most
`dim(A) - 1 = 1`; the dimension formula of [Stacks, Tag 0BAE] then forces the generic fibre of
`f` to be a single point, and [Stacks, Tag 0B2I] propagates the resulting generic fibre
dimension `0` to every fibre over a point whose local ring has dimension at most one. So all
fibres of `f ∣_ U` are zero-dimensional. Zariski's main theorem [Stacks, Tag 02OH] makes
`f ∣_ U` finite, and a finite birational morphism onto a normal integral scheme is an
isomorphism ([Stacks, Tag 0AB1]).

## Implementation notes

The two hypotheses of `exists_isAdmissibleBlowup_dominating` are the two inputs of
`AlgebraicGeometry.exists_isAdmissibleBlowup_dominating` in
`StacksFrontier/AlgebraicGeometry/Blowup/DominatedByBlowup.lean`, namely
`AlgebraicGeometry.CartierBoundaryReduction` ([Stacks, Tag 080Y]) and
`AlgebraicGeometry.StrictTransformOpenImmersion` ([Stacks, Tag 081S]). Both are proved in this
library for Situation 0AX8, by `AlgebraicGeometry.cartierBoundaryReduction` and
`AlgebraicGeometry.VanishingSituation.strictTransformOpenImmersion`; the unconditional
statement is
`AlgebraicGeometry.VanishingSituation.exists_isAdmissibleBlowup_dominating_of_noetherian`.

The facts about the generic point of a birational morphism used below are
`StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericPoint`.

## References

* [Stacks Project, Tag 0B4M](https://stacks.math.columbia.edu/tag/0B4M)
* [Stacks Project, Tag 0AX8](https://stacks.math.columbia.edu/tag/0AX8)
* [Stacks Project, Tag 081T](https://stacks.math.columbia.edu/tag/081T)
* [Stacks Project, Tag 0BFP](https://stacks.math.columbia.edu/tag/0BFP)
* [Stacks Project, Tag 0B2I](https://stacks.math.columbia.edu/tag/0B2I)
* [Stacks Project, Tag 0BAE](https://stacks.math.columbia.edu/tag/0BAE)
* [Stacks Project, Tag 02OH](https://stacks.math.columbia.edu/tag/02OH)
* [Stacks Project, Tag 0AB1](https://stacks.math.columbia.edu/tag/0AB1)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### The generic point of a birational morphism -/

/-- **The generic point of the target of a birational morphism has a one-point preimage.** At a
point above the generic point the dimension formula of [Stacks, Tag 0BAE] forces the local ring
to have dimension zero, and on an integral scheme only the generic point has that property. -/
public theorem preimage_genericPoint {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsLocallyNoetherian Y] (f : X ⟶ Y) [LocallyOfFiniteType f]
    (hf : IsBirational f) :
    f ⁻¹' {genericPoint Y} = {genericPoint X} := by
  have hmap : f (genericPoint X) = genericPoint Y := IsBirational.genericPoint_eq f hf
  apply Set.Subset.antisymm
  · intro x hx
    have hfx : f x = genericPoint Y := hx
    by_contra hne
    have hone : (1 : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x) :=
      Stacks.LocalCohomology.one_le_ringKrullDim_stalk_of_ne_genericPoint x hne
    have hformula := ringKrullDim_stalk_add_residueFieldTranscendenceDegree_le f x
    rw [genericResidueFieldTranscendenceDegreeAt_eq_zero f hf x, hfx,
      ringKrullDim_stalk_genericPoint_eq_zero Y] at hformula
    have hle : ringKrullDim (X.presheaf.stalk x) ≤ 0 := by
      refine le_trans (le_add_of_nonneg_right ?_) (hformula.trans (by simp))
      exact WithBot.coe_le_coe.mpr zero_le
    exact absurd (hone.trans hle) (by simp)
  · rw [Set.singleton_subset_iff]
    exact hmap

/-! ### Fibre dimensions of a birational morphism -/

/-- The fibre of a birational morphism over the generic point of the target is a single point. -/
public theorem subsingleton_fiber_genericPoint {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y] (f : X ⟶ Y) [LocallyOfFiniteType f]
    (hf : IsBirational f) :
    Subsingleton (f.fiber (genericPoint Y)) := by
  have hpre : f ⁻¹' {genericPoint Y} = {genericPoint X} :=
    preimage_genericPoint f hf
  have key : ∀ w : f.fiber (genericPoint Y), f.fiberι (genericPoint Y) w = genericPoint X := by
    intro w
    have h : f.fiberι (genericPoint Y) w ∈ f ⁻¹' {genericPoint Y} := (f.fiberHomeo _ w).2
    rw [hpre] at h
    simpa using h
  refine ⟨fun z z' => ?_⟩
  refine (f.fiberι (genericPoint Y)).isEmbedding.injective ?_
  rw [key z, key z']

/-- The generic fibre of a birational morphism has dimension zero at the generic point of the
source: that fibre is a one-point space, so the point is isolated. -/
public theorem topologicalKrullDimAt_fiber_genericPoint_eq_zero {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y] (f : X ⟶ Y) [LocallyOfFiniteType f]
    (hf : IsBirational f) :
    topologicalKrullDimAt (f.fiber (f (genericPoint X))) (f.asFiber (genericPoint X)) = 0 := by
  have hmap : f (genericPoint X) = genericPoint Y := IsBirational.genericPoint_eq f hf
  have _ : Subsingleton (f.fiber (f (genericPoint X))) := by
    rw [hmap]; exact subsingleton_fiber_genericPoint f hf
  have _ : Nonempty (f.fiber (f (genericPoint X))) := ⟨f.asFiber (genericPoint X)⟩
  have _ : LocallyOfFiniteType (f.fiberToSpecResidueField (f (genericPoint X))) := by
    change LocallyOfFiniteType (Limits.pullback.snd f
      (Y.fromSpecResidueField (f (genericPoint X))))
    infer_instance
  have _ : IsLocallyNoetherian (f.fiber (f (genericPoint X))) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (f.fiberToSpecResidueField (f (genericPoint X)))
  refine (AlgebraicGeometry.topologicalKrullDimAt_eq_zero_iff_isIsolatedPoint _ _).2 ?_
  rw [isIsolatedPoint_iff]
  have hs : ({f.asFiber (genericPoint X)} :
      Set (f.fiber (f (genericPoint X)))) = Set.univ := by
    ext z
    simp only [Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  simp [hs]

/-- Transport of a fibre along an equality of base points. -/
public noncomputable def fiberHomeomorphOfEq {X Y : Scheme.{u}} (f : X ⟶ Y) {y y' : Y}
    (h : y = y') : f.fiber y ≃ₜ f.fiber y' := by
  cases h
  exact Homeomorph.refl _

public theorem fiberι_fiberHomeomorphOfEq {X Y : Scheme.{u}} (f : X ⟶ Y) {y y' : Y}
    (h : y = y') (z : f.fiber y) :
    f.fiberι y' (fiberHomeomorphOfEq f h z) = f.fiberι y z := by
  cases h
  rfl

/-- **Over a point whose local ring has dimension at most one, a birational morphism has a
zero-dimensional fibre.** The generic fibre is a single point, so [Stacks, Tag 0B2I] applies
with generic fibre dimension zero at every point of the fibre. -/
private theorem topologicalKrullDim_fiber_le_zero_of_ringKrullDim_stalk_le_one
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] (hf : IsBirational f) (y : Y)
    (hy : ringKrullDim (Y.presheaf.stalk y) ≤ 1) :
    topologicalKrullDim (f.fiber y) ≤ ((0 : ℕ) : WithBot ℕ∞) := by
  have hgeneric : ∀ η : X, closure {η} ∈ irreducibleComponents X → ∀ _ : X,
      topologicalKrullDimAt (f.fiber (f η)) (f.asFiber η) = ((0 : ℕ) : WithBot ℕ∞) := by
    intro η hη _
    have hηeq : η = genericPoint X := by
      rw [irreducibleComponents_eq_singleton] at hη
      exact IsGenericPoint.eq (by simpa [IsGenericPoint] using hη) (genericPoint_spec X)
    subst hηeq
    simpa using topologicalKrullDimAt_fiber_genericPoint_eq_zero f hf
  have hlocAt : ∀ x : X, f x = y →
      topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) ≤ ((0 : ℕ) : WithBot ℕ∞) := by
    intro x hx
    have hnoeth : IsNoetherianRing (Y.presheaf.stalk (f x)) := by
      rw [hx]; infer_instance
    have hdim : ringKrullDim (Y.presheaf.stalk (f x)) ≤ 1 := by rw [hx]; exact hy
    exact le_of_eq (topologicalKrullDimAt_fiber_eq_of_target_dim_le_one f x hnoeth hdim 0
      fun η hη _ => hgeneric η hη x)
  rw [topologicalKrullDim_eq_iSup_localKrullDim]
  refine iSup_le fun z => ?_
  have hx : f (f.fiberι y z) = y :=
    Set.mem_singleton_iff.mp (Set.mem_preimage.mp (f.fiberHomeo y z).2)
  have hpoint : fiberHomeomorphOfEq f hx (f.asFiber (f.fiberι y z)) = z := by
    refine (f.fiberι y).isEmbedding.injective ?_
    rw [fiberι_fiberHomeomorphOfEq]
    simp [Scheme.Hom.fiberι_asFiber]
  rw [← topologicalKrullDimAt_eq_localKrullDim, ← hpoint,
    ← topologicalKrullDimAt_eq_of_homeomorph (fiberHomeomorphOfEq f hx)]
  exact hlocAt (f.fiberι y z) hx

namespace VanishingSituation

/-! ### The modification is an isomorphism over the punctured spectrum -/

/-- The spectrum of a normal domain is a normal scheme: its local rings are the localizations of
the domain at its primes, which are integrally closed domains. -/
private theorem isNormal_base (V : VanishingSituation.{u}) : IsNormal V.base := by
  refine (isNormal_iff_stalk_normal _).2 fun x => ?_
  set p : Ideal V.A := x.asIdeal with hpdef
  have : p.IsPrime := x.isPrime
  have hle : p.primeCompl ≤ nonZeroDivisors V.A := Ideal.primeCompl_le_nonZeroDivisors p
  have : IsDomain (Localization.AtPrime p) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.AtPrime p) hle
  have : IsIntegrallyClosed (Localization.AtPrime p) :=
    isIntegrallyClosed_of_isLocalization (Localization.AtPrime p) p.primeCompl hle
  let e : Localization.AtPrime p ≃+* V.base.presheaf.stalk x :=
    (Spec.stalkIso (CommRingCat.of V.A) x).commRingCatIsoToRingEquiv.symm
  exact ⟨Function.Injective.isDomain e.symm.toRingHom (by exact e.symm.injective),
    IsIntegrallyClosed.of_equiv e⟩

/-- The maximal ideal of the base has height two. -/
private theorem height_maximalIdeal (V : VanishingSituation.{u}) :
    ((IsLocalRing.maximalIdeal V.A).height : WithBot ℕ∞) = 2 := by
  rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim, V.dimension_two]

/-- The base has dimension two, so its generic point is not its closed point. -/
private theorem genericPoint_ne_closedPoint (V : VanishingSituation.{u}) :
    genericPoint V.base ≠ V.closedPoint := by
  intro h
  have hmax : IsMax (V.closedPoint : V.base) := h ▸ isMax_genericPoint V.base
  have h0 : Order.coheight (V.closedPoint : V.base) = 0 := Order.coheight_eq_zero.2 hmax
  have hh : (IsLocalRing.maximalIdeal V.A).height = 0 := by
    rw [show IsLocalRing.maximalIdeal V.A = (V.closedPoint : V.base).asIdeal from rfl,
      idealHeight_eq_coheight, h0]
  have h2 : ((0 : ℕ∞) : WithBot ℕ∞) = 2 := by rw [← hh]; exact V.height_maximalIdeal
  simp at h2

private theorem mem_puncturedSpectrumOpen_iff (V : VanishingSituation.{u}) (p : V.base) :
    p ∈ V.puncturedSpectrumOpen ↔ p ≠ V.closedPoint :=
  Iff.rfl

/-- A point of the punctured spectrum is a prime strictly below the maximal ideal, so its local
ring has dimension at most `dim(A) - 1 = 1`. -/
private theorem ringKrullDim_stalk_le_one (V : VanishingSituation.{u}) (p : V.base)
    (hp : p ≠ V.closedPoint) : ringKrullDim (V.base.presheaf.stalk p) ≤ 1 := by
  rw [ringKrullDim_stalk_eq_coheight, ← idealHeight_eq_coheight]
  have hprime : p.asIdeal.IsPrime := p.isPrime
  have hle : p.asIdeal ≤ IsLocalRing.maximalIdeal V.A :=
    IsLocalRing.le_maximalIdeal_of_isPrime p.asIdeal
  have hne : p.asIdeal ≠ IsLocalRing.maximalIdeal V.A := fun h => hp (PrimeSpectrum.ext h)
  have hstep := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hle hne)
  rw [show (IsLocalRing.maximalIdeal V.A).height = 2 from
    WithBot.coe_inj.mp V.height_maximalIdeal] at hstep
  have hne_top : p.asIdeal.height ≠ ⊤ := by
    intro h
    rw [h] at hstep
    simp at hstep
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne_top
  rw [← hn] at hstep ⊢
  have hn2 : n + 1 ≤ 2 := by exact_mod_cast hstep
  have hle1 : n ≤ 1 := by omega
  exact_mod_cast hle1

/-- The local rings of an open subscheme are the local rings of the ambient scheme. -/
private theorem ringKrullDim_stalk_toScheme {X : Scheme.{u}} (U : X.Opens) (y : U) :
    ringKrullDim (U.toScheme.presheaf.stalk y) = ringKrullDim (X.presheaf.stalk y.1) :=
  ringKrullDim_eq_of_ringEquiv (U.stalkIso y).commRingCatIsoToRingEquiv

/-- **The modification of Situation [Stacks, Tag 0AX8] is an isomorphism over the punctured
spectrum.** Every point of `U = S ∖ {s}` has a local ring of dimension at most one, so every
fibre of `f ∣_ U` is zero-dimensional; a proper morphism with zero-dimensional fibres is finite
([Stacks, Tag 02OH]), and a finite birational morphism onto a normal integral scheme is an
isomorphism ([Stacks, Tag 0AB1]).

The source records this in the discussion following Situation [Stacks, Tag 0AX8], citing the
codimension-one clause of [Stacks, Tag 0BFP]. -/
public theorem isIso_morphismRestrict_puncturedSpectrumOpen (V : VanishingSituation.{u}) :
    IsIso (V.f ∣_ V.puncturedSpectrumOpen) := by
  have hgen : genericPoint V.base ∈ V.puncturedSpectrumOpen :=
    (V.mem_puncturedSpectrumOpen_iff _).2 V.genericPoint_ne_closedPoint
  have hUne : Nonempty V.puncturedSpectrumOpen := ⟨⟨genericPoint V.base, hgen⟩⟩
  have hmapgen : V.f (genericPoint V.X) = genericPoint V.base :=
    IsBirational.genericPoint_eq V.f V.modification.isBirational
  have hfne : Nonempty (V.f ⁻¹ᵁ V.puncturedSpectrumOpen) :=
    ⟨⟨genericPoint V.X, by
      change V.f (genericPoint V.X) ∈ V.puncturedSpectrumOpen
      rw [hmapgen]
      exact hgen⟩⟩
  have hbir : IsBirational (V.f ∣_ V.puncturedSpectrumOpen) :=
    V.modification.isBirational.morphismRestrict V.puncturedSpectrumOpen
  have hnormalbase : IsNormal V.base := V.isNormal_base
  have hdim : ∀ y : V.puncturedSpectrumOpen.toScheme,
      topologicalKrullDim ((V.f ∣_ V.puncturedSpectrumOpen).fiber y) ≤
        ((0 : ℕ) : WithBot ℕ∞) := by
    intro y
    refine topologicalKrullDim_fiber_le_zero_of_ringKrullDim_stalk_le_one _ hbir y
      (le_of_eq_of_le (ringKrullDim_stalk_toScheme V.puncturedSpectrumOpen y) ?_)
    exact V.ringKrullDim_stalk_le_one y.1 ((V.mem_puncturedSpectrumOpen_iff _).1 y.2)
  have : IsFinite (V.f ∣_ V.puncturedSpectrumOpen) :=
    isFinite_of_isProper_of_forall_topologicalKrullDim_fiber_le_zero _ hdim
  exact isIso_of_isIntegralHom_of_isBirational_of_isNormal _ hbir

/-! ### Tag 0B4M -/

/-- In Situation [Stacks, Tag 0AX8], given the inputs `h080Y` and `h081S` of
`AlgebraicGeometry.exists_isAdmissibleBlowup_dominating`, there is a `U`-admissible blowup
`b : S' ⟶ S` of the punctured spectrum `U = S ∖ {s}` which dominates `X`: it factors as
`S' ⟶ X ⟶ S`.

This applies that lemma at the modification `f`, which is an isomorphism over `U` by
`isIso_morphismRestrict_puncturedSpectrumOpen`. Both inputs are proved in this library
(`AlgebraicGeometry.cartierBoundaryReduction` and
`AlgebraicGeometry.VanishingSituation.strictTransformOpenImmersion`), and
`AlgebraicGeometry.VanishingSituation.exists_isAdmissibleBlowup_dominating_of_noetherian`
supplies them, giving [Stacks, Tag 0B4M] with no hypothesis. -/
public theorem exists_isAdmissibleBlowup_dominating (V : VanishingSituation.{u})
    (h080Y : CartierBoundaryReduction V.base V.puncturedSpectrumOpen)
    (h081S : StrictTransformOpenImmersion V.f V.puncturedSpectrumOpen) :
    ∃ (S' : Scheme.{u}) (b : S' ⟶ V.base),
      Stacks.Blowup.IsAdmissibleBlowup V.puncturedSpectrumOpen b ∧
        ∃ g : S' ⟶ V.X, g ≫ V.f = b :=
  have : IsIso (V.f ∣_ V.puncturedSpectrumOpen) :=
    V.isIso_morphismRestrict_puncturedSpectrumOpen
  AlgebraicGeometry.exists_isAdmissibleBlowup_dominating V.f V.puncturedSpectrumOpen h080Y h081S

end VanishingSituation

end AlgebraicGeometry

end
