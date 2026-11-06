module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.IsomorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.LocalizationSequence
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.OpenImmersionRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.FibreDimension

/-!
# Chow groups of an affine-space bundle

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `f : X ⟶ Y` be a
morphism of schemes locally of finite type over `S` which is Zariski-locally on `Y` the
projection `U × 𝔸^r ⟶ U`. Stacks 02TT asserts that the flat pullback
`f^* : A_k(Y) ⟶ A_{k+r}(X)` is surjective for every `k`. This file introduces the local
triviality hypothesis, derives from it the three properties of `f` that the flat pullback needs —
locally of finite type, flat, of relative dimension `r` — and proves Stacks 02TT in relative
dimension zero, where an affine-space bundle is an isomorphism and the pullback is the
restriction map of Stacks 02RC.

## Main definitions

* `Stacks.Chow.IsAffineSpaceBundle` — the local triviality hypothesis of Stacks 02TT: every
  point of the target has an open neighbourhood `U` over which `f` restricts to the projection
  `𝔸^r_U ⟶ U`.

## Main results

* `Stacks.Chow.flat_affineSpaceOver`, `Stacks.Chow.relativeDimension_affineSpaceOver` — the
  projection of affine `r`-space over a scheme is flat of relative dimension `r`.
* `Stacks.Chow.locallyOfFiniteType_of_isAffineSpaceBundle`,
  `Stacks.Chow.flat_of_isAffineSpaceBundle`,
  `Stacks.Chow.relativeDimension_of_isAffineSpaceBundle` — an affine-space bundle of rank `r` is
  locally of finite type, flat, and of relative dimension `r`.
* `Stacks.Chow.isIso_of_isAffineSpaceBundle_zero` — an affine-space bundle of rank zero is an
  isomorphism.
* `Stacks.Chow.flatPullback_surjective_of_isOpenImmersion`,
  `Stacks.Chow.flatPullbackChow_surjective_of_isOpenImmersion` — flat pullback along an open
  immersion is surjective, on cycles and on Chow groups.
* `Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_of_isIso` — flat pullback along an
  isomorphism preserves rational equivalence.
* `Stacks.Chow.flatPullbackChow_surjective_of_isAffineSpaceBundle_zero` — **Stacks 02TT** in
  relative dimension zero.

## Implementation notes

Local triviality is phrased with the restriction `f ∣_ U : f ⁻¹ᵁ U ⟶ U` of `f` to an open
subscheme `U` of the target, matching the source, and affine space is indexed by
`ULift (Fin r)` so that the index type lies in the universe of the schemes. The compatibility
with the two projections to `U` is part of the hypothesis: an abstract isomorphism of schemes
would not say that `f` itself is the projection.

Relative dimension `r` is recorded through
`AlgebraicGeometry.locallyOfFiniteTypeRelativeDimension`, which bundles the local finite-type
instance that `AlgebraicGeometry.RelativeDimension` takes as an argument and is local on the
target.

## References

* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT)
* [Stacks Project, Tag 02RC](https://stacks.math.columbia.edu/tag/02RC)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 02VJ](https://stacks.math.columbia.edu/tag/02VJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Affine-space bundles -/

/-- A morphism `f : X ⟶ Y` is an affine-space bundle of rank `r` if every point of `Y` has an
open neighbourhood `U` over which `f` restricts to the projection `𝔸^r_U ⟶ U`. This is the local
triviality hypothesis of Stacks 02TT. -/
def IsAffineSpaceBundle {X Y : Scheme.{u}} (f : X ⟶ Y) (r : ℕ) : Prop :=
  ∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧
    ∃ e : (f ⁻¹ᵁ U).toScheme ≅ 𝔸(ULift.{u} (Fin r); U.toScheme),
      e.hom ≫ (𝔸(ULift.{u} (Fin r); U.toScheme) ↘ U.toScheme) = f ∣_ U

/-- A property of morphisms that is Zariski-local on the target and holds for the projection of
affine `r`-space over every base holds for every affine-space bundle of rank `r`. -/
theorem morphismProperty_of_isAffineSpaceBundle (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtTarget P] {X Y : Scheme.{u}} (f : X ⟶ Y) (r : ℕ)
    (hP : ∀ T : Scheme.{u}, P (𝔸(ULift.{u} (Fin r); T) ↘ T)) (h : IsAffineSpaceBundle f r) :
    P f := by
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict fun y ↦ ?_
  obtain ⟨U, hyU, e, he⟩ := h y
  refine ⟨U, hyU, ?_⟩
  rw [← he, P.cancel_left_of_respectsIso]
  exact hP U.toScheme

/-! ### The projection of affine space -/

/-- The projection of affine `r`-space over a scheme is flat: the polynomial ring is a free, hence
flat, module over the integers, and flatness is stable under base change. -/
theorem flat_affineSpaceOver (T : Scheme.{u}) (r : ℕ) :
    AlgebraicGeometry.Flat (𝔸(ULift.{u} (Fin r); T) ↘ T) := by
  have hC : AlgebraicGeometry.Flat
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ := ULift.{u} (Fin r))
        (R := ULift.{u} ℤ)))) := by
    refine AlgebraicGeometry.Flat.SpecMap_iff.mpr ?_
    have hf : (algebraMap (ULift.{u} ℤ) (MvPolynomial (ULift.{u} (Fin r)) (ULift.{u} ℤ))).Flat :=
      RingHom.flat_algebraMap_iff.mpr inferInstance
    simpa only [CommRingCat.hom_ofHom, MvPolynomial.algebraMap_eq] using hf
  have hterm : AlgebraicGeometry.Flat
      (terminal.from (Spec (CommRingCat.of (MvPolynomial (ULift.{u} (Fin r)) (ULift.{u} ℤ))))) := by
    have _ := isIso_of_isTerminal specULiftZIsTerminal.{u} terminalIsTerminal
      (terminal.from (Spec (CommRingCat.of (ULift.{u} ℤ))))
    have _ : AlgebraicGeometry.Flat
        (terminal.from (Spec (CommRingCat.of (ULift.{u} ℤ)))) := inferInstance
    rw [← terminal.comp_from (Spec.map (CommRingCat.ofHom (MvPolynomial.C
      (σ := ULift.{u} (Fin r)) (R := ULift.{u} ℤ))))]
    exact AlgebraicGeometry.Flat.comp _ _
  have _ : MorphismProperty.IsStableUnderBaseChangeAlong
      (@AlgebraicGeometry.Flat : MorphismProperty Scheme.{u}) (terminal.from T) :=
    ⟨fun pb hpb ↦ AlgebraicGeometry.Flat.isStableUnderBaseChange.of_isPullback pb hpb⟩
  exact MorphismProperty.pullback_fst
    (P := (@AlgebraicGeometry.Flat : MorphismProperty Scheme.{u})) _ _ hterm

/-- The projection of affine `r`-space over a scheme has relative dimension `r`: each fibre is
affine `r`-space over a residue field, which is irreducible of Krull dimension `r`. -/
theorem relativeDimension_affineSpaceOver (T : Scheme.{u}) (r : ℕ) :
    AlgebraicGeometry.RelativeDimension (𝔸(ULift.{u} (Fin r); T) ↘ T) r := by
  intro t ht
  let n := ULift.{u} (Fin r)
  let K := T.residueField t
  let e : 𝔸(n; Spec (CommRingCat.of K)) ≅ (𝔸(n; T) ↘ T).fiber t :=
    (AffineSpace.isPullback_map (n := n) (T.fromSpecResidueField t)).isoPullback
  let h := TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e)
  have _ : IrreducibleSpace 𝔸(n; Spec (CommRingCat.of K)) := inferInstance
  have _ : IrreducibleSpace ((𝔸(n; T) ↘ T).fiber t) := h.irreducibleSpace_iff.mp inferInstance
  refine ⟨TopologicalSpace.Equidimensional.of_preirreducibleSpace _, ?_⟩
  have hd : topologicalKrullDim 𝔸(n; Spec (CommRingCat.of K)) = (r : WithBot ℕ∞) := by
    calc
      topologicalKrullDim 𝔸(n; Spec (CommRingCat.of K))
          = topologicalKrullDim (PrimeSpectrum (MvPolynomial n K)) :=
        IsHomeomorph.topologicalKrullDim_eq _
          (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso
            (AffineSpace.SpecIso n (CommRingCat.of K)))).isHomeomorph
      _ = ringKrullDim (MvPolynomial n K) :=
        PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
      _ = ringKrullDim K + Nat.card n := MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite
      _ = (r : WithBot ℕ∞) := by simp [n]
  exact (IsHomeomorph.topologicalKrullDim_eq _ h.isHomeomorph).symm.trans hd

/-! ### Structural properties of an affine-space bundle -/

/-- An affine-space bundle is locally of finite type: affine `r`-space over a base is of finite
presentation over it, and being locally of finite type is Zariski-local on the target. -/
theorem locallyOfFiniteType_of_isAffineSpaceBundle {X Y : Scheme.{u}} (f : X ⟶ Y) (r : ℕ)
    (h : IsAffineSpaceBundle f r) : LocallyOfFiniteType f := by
  have _ : IsZariskiLocalAtTarget (@LocallyOfFiniteType.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (@LocallyOfFiniteType.{u})
  exact morphismProperty_of_isAffineSpaceBundle (@LocallyOfFiniteType) f r
    (fun T ↦ inferInstanceAs (LocallyOfFiniteType (𝔸(ULift.{u} (Fin r); T) ↘ T))) h

/-- An affine-space bundle is flat, flatness being Zariski-local on the target. -/
theorem flat_of_isAffineSpaceBundle {X Y : Scheme.{u}} (f : X ⟶ Y) (r : ℕ)
    (h : IsAffineSpaceBundle f r) : AlgebraicGeometry.Flat f := by
  have _ : IsZariskiLocalAtTarget (@AlgebraicGeometry.Flat.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget
      (P := @AlgebraicGeometry.Flat) (Q := RingHom.Flat)
  exact morphismProperty_of_isAffineSpaceBundle (@AlgebraicGeometry.Flat) f r
    (fun T ↦ flat_affineSpaceOver T r) h

/-- An affine-space bundle of rank `r` has relative dimension `r`: being locally of finite type of
relative dimension `r` is Zariski-local on the target by Stacks 02VJ. -/
theorem relativeDimension_of_isAffineSpaceBundle {X Y : Scheme.{u}} (f : X ⟶ Y) (r : ℕ)
    (h : IsAffineSpaceBundle f r) [LocallyOfFiniteType f] :
    AlgebraicGeometry.RelativeDimension f r := by
  have _ : IsZariskiLocalAtTarget (locallyOfFiniteTypeRelativeDimension.{u} r) :=
    MorphismProperty.IsLocalAtTarget.of_le Scheme.zariskiPrecoverage_le_fpqcPrecoverage
  have hP : locallyOfFiniteTypeRelativeDimension.{u} r f :=
    morphismProperty_of_isAffineSpaceBundle (locallyOfFiniteTypeRelativeDimension.{u} r) f r
      (fun T ↦ ⟨inferInstanceAs (LocallyOfFiniteType (𝔸(ULift.{u} (Fin r); T) ↘ T)),
        relativeDimension_affineSpaceOver T r⟩) h
  exact hP.choose_spec

/-- An affine-space bundle of rank zero is an isomorphism: the projection of affine space on an
empty index set is an isomorphism, and being an isomorphism is Zariski-local on the target. -/
theorem isIso_of_isAffineSpaceBundle_zero {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : IsAffineSpaceBundle f 0) : IsIso f :=
  morphismProperty_of_isAffineSpaceBundle (MorphismProperty.isomorphisms Scheme.{u}) f 0
    (fun T ↦ inferInstanceAs (IsIso (𝔸(ULift.{u} (Fin 0); T) ↘ T))) h

/-! ### Surjectivity of flat pullback along an open immersion -/

/-- Flat pullback of cycles along an open immersion is surjective: in relative dimension zero it
is the restriction map, which is surjective by Stacks 02RC. -/
theorem flatPullback_surjective_of_isOpenImmersion (C : ChowSituation.{u}) {X U : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sU : U ⟶ C.S) [LocallyOfFiniteType sU]
    (j : U ⟶ X) [IsOpenImmersion j] (hj : j ≫ sX = sU)
    (hr : AlgebraicGeometry.RelativeDimension j 0) (k : ℤ) :
    Function.Surjective (flatPullback C sU sX j hj 0 hr k) := by
  intro d
  have hd : (d : AlgebraicCycle U ℤ) ∈ cyclesOfDimension C sU k := by
    simpa using d.2
  obtain ⟨c, hc⟩ := cycleGroupRestrict_surjective C sX sU j hj k ⟨(d : AlgebraicCycle U ℤ), hd⟩
  refine ⟨c, Subtype.ext ?_⟩
  rw [← cycleGroupRestrict_eq_flatPullback C sX sU j hj hr k c]
  exact congrArg Subtype.val hc

/-- Flat pullback on Chow groups along an open immersion is surjective: a class on the open
subscheme is the class of a cycle, and that cycle is a flat pullback. -/
theorem flatPullbackChow_surjective_of_isOpenImmersion (C : ChowSituation.{u})
    {X U : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sU : U ⟶ C.S)
    [LocallyOfFiniteType sU] (j : U ⟶ X) [IsOpenImmersion j] (hj : j ≫ sX = sU)
    (hr : AlgebraicGeometry.RelativeDimension j 0) (k : ℤ)
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C sU sX j hj 0 hr k) :
    Function.Surjective (flatPullbackChow C sU sX j hj 0 hr k hfac) := by
  intro q
  obtain ⟨d, rfl⟩ := QuotientAddGroup.mk'_surjective _ q
  obtain ⟨c, hc⟩ := flatPullback_surjective_of_isOpenImmersion C sX sU j hj hr k d
  exact ⟨QuotientAddGroup.mk' _ c, by rw [flatPullbackChow_mk, hc]⟩

/-- Flat pullback of `k`-cycles along an isomorphism over the base carries cycles rationally
equivalent to zero to cycles rationally equivalent to zero. An isomorphism `f : X ⟶ Y` sits in a
square over the inclusion of `Y` as its own largest open subscheme, along which the assertion is
Stacks 02S1 for an open immersion, and the assertion transports across a square whose two
remaining legs are isomorphisms. -/
theorem flatPullbackFactorsThroughRationalEquivalence_of_isIso (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (f : X ⟶ Y) [IsIso f] (hbase : f ≫ sY = sX)
    (hf : AlgebraicGeometry.RelativeDimension f 0) (k : ℤ) :
    FlatPullbackFactorsThroughRationalEquivalence C sX sY f hbase 0 hf k := by
  have _ : IsIso ((⊤ : Y.Opens).ι) := by
    rw [← Scheme.topIso_hom Y]
    infer_instance
  refine flatPullbackFactorsThroughRationalEquivalence_of_isIso_square C sY sX sY
    ((⊤ : Y.Opens).ι ≫ sY) (𝟙 Y) (Category.id_comp sY) (f ≫ Y.topIso.inv) (by simp [hbase]) f
    hbase ((⊤ : Y.Opens).ι) rfl (by simp) 0 hf (relativeDimension_opensι (⊤ : Y.Opens)) k ?_
  exact flatPullbackFactorsThroughRationalEquivalence_of_opensι C sY (⊤ : Y.Opens) k

/-! ### Stacks 02TT in relative dimension zero -/

/-- **Stacks 02TT in relative dimension zero.** Let `X` and `Y` be locally of finite type over the
base of chapter 42 and let `f : X ⟶ Y` be flat of relative dimension zero which is
Zariski-locally on `Y` the projection `U × 𝔸^0 ⟶ U`. Then `f^* : A_k(Y) ⟶ A_k(X)` is surjective
for every `k`.

Such an `f` is an isomorphism, so its flat pullback is the restriction map of Stacks 02RC. The
instance of Stacks 02S1 needed to write the map down is not an extra assumption here: it is
supplied by `Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_of_isIso`.

Stacks 02TT in every relative dimension is
`Stacks.Chow.flatPullbackChow_surjective_of_isAffineSpaceBundle_unconditional`. -/
theorem flatPullbackChow_surjective_of_isAffineSpaceBundle_zero (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f] [AlgebraicGeometry.Flat f]
    (hbase : f ≫ sY = sX) (hf : AlgebraicGeometry.RelativeDimension f 0)
    (hbundle : IsAffineSpaceBundle f 0) (k : ℤ)
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C sX sY f hbase 0 hf k) :
    Function.Surjective (flatPullbackChow C sX sY f hbase 0 hf k hfac) := by
  have _ : IsIso f := isIso_of_isAffineSpaceBundle_zero f hbundle
  have _ : IsOpenImmersion f := IsOpenImmersion.of_isIso f
  exact flatPullbackChow_surjective_of_isOpenImmersion C sY sX f hbase hf k hfac

end Stacks.Chow

end
