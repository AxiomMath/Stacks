module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.ResidueField
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuliEllipticCurvesAlgebraic
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuliEllipticCurvesGluing
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassCoordinateChangeTorsor
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassEquationNoetherian
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassEquationField
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassFamilyElliptic
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassFamily

/-!
# The Weierstrass family is a smooth surjective cover of the moduli stack

Let `W = Spec(ℤ[a₁, a₂, a₃, a₄, a₆, 1/Δ])` and let `(E_W, f_W, 0_W)` be the Weierstrass family
over `W` constructed in Section 072S. This file proves that the morphism `W ⟶ 𝓜₁,₁` it
classifies is smooth and surjective (Tag 072T), and hence that `𝓜₁,₁` has a smooth surjective
cover by a scheme (condition (3) of Tag 072R).

## Main definitions

* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.identityComparison` is the identity triple
  `(1, 1, 1)` of a pointed family with itself.

## Main results

* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.smooth_snd_of_locally_comparison`: if
  `H × W` is the fibre product `W ×_{𝓜₁,₁} W` and an elliptic curve `E'` over `S'` has a
  Weierstrass equation Zariski locally on `S'`, then every fibre product `W ×_{𝓜₁,₁} S'` is
  smooth over `S'`.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.surjective_snd_of_comparison_residueField`:
  if every fibre of `E'` has a Weierstrass equation, every fibre product `W ×_{𝓜₁,₁} S'` is
  surjective over `S'`.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.isSmooth_family` and
  `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.isSurjective_family` are the two assertions
  of Tag 072T.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.hasSmoothSurjectiveCover`: consequently
  condition (3) of Tag 072R holds, that is, `𝓜₁,₁` has a smooth surjective cover by a scheme.

## Implementation notes

The moduli stack is not an object: as in Sections 072J, 072L, 072P and 072R, the morphism
`W ⟶ 𝓜₁,₁` of the source *is* the Weierstrass family
`AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.family` over `W`, smoothness of that
morphism is `AlgebraicGeometry.ModuliEllipticCurves.PointedFamily.IsSmooth` and surjectivity is
`AlgebraicGeometry.ModuliEllipticCurves.PointedFamily.IsSurjective`. Both of those take as an
argument the proof that the family is an elliptic curve, which is
`AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.isElliptic_family` (Section 072S).

Surjectivity is the source's one-line argument: every elliptic curve over a field has a
Weierstrass equation
(`AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.exists_comparison_fromSpecResidueField`, for
the fibre of a family at a point), and a Weierstrass equation for the fibre at `s'` is a point of
`S' ×_{𝓜₁,₁} W` over `s'`.

Smoothness follows the source's sketch. The group `H` of coordinate changes acts on `W`, and the
two assertions of the source's proof are proved elsewhere: an elliptic curve has a Weierstrass
equation Zariski locally on its base
(`AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.localWeierstrassAt_of_noetherian` with
`AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.localWeierstrassNoetherian`), and two
Weierstrass equations of the same curve differ by a unique element of `H`
(`AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.exists_unique_variableChange`), which makes
`H × W` the fibre product `W ×_{𝓜₁,₁} W`
(`AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.representsComparisons_coordinateChange`).
This is the torsor property: over an open `U` of `S'` where `E'` is the restriction of the
Weierstrass family along `a : U ⟶ W`, any fibre product `W ×_{𝓜₁,₁} S'` restricted to `U` is
isomorphic to `(H × W) ×_W U`, the base change along `a` of the projection `H × W ⟶ W`, which
is smooth because `H` is smooth over `Spec(ℤ)`.

## References

* [Stacks Project, Tag 072S](https://stacks.math.columbia.edu/tag/072S)
* [Stacks Project, Tag 072T](https://stacks.math.columbia.edu/tag/072T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ModuliEllipticCurves.Weierstrass

/-! ### The second projection of a fibre product presented by a restriction -/

/-- In the fibre product `P ×_{W₁ × W₂} (W₁ × U)` of `(f₁, f₂) : P ⟶ W₁ × W₂` and
`1 × c' : W₁ × U ⟶ W₁ × W₂`, the projection to `U` is the base change of `f₂` along `c'`: the
coordinate in `W₁` is determined by the point of `P`. -/
theorem isPullback_pullback_prodLift_prodMap {P W₁ W₂ U : Scheme.{u}} (f₁ : P ⟶ W₁)
    (f₂ : P ⟶ W₂) (c' : U ⟶ W₂) :
    IsPullback (Limits.pullback.fst (prod.lift f₁ f₂) (prod.map (𝟙 W₁) c'))
      (Limits.pullback.snd (prod.lift f₁ f₂) (prod.map (𝟙 W₁) c') ≫ prod.snd) f₂ c' := by
  have hc {T : Scheme.{u}} (k : W₁ ⨯ W₂ ⟶ T) :=
    Limits.pullback.condition_assoc (f := prod.lift f₁ f₂) (g := prod.map (𝟙 W₁) c') k
  have hw : Limits.pullback.fst (prod.lift f₁ f₂) (prod.map (𝟙 W₁) c') ≫ f₂ =
      (Limits.pullback.snd (prod.lift f₁ f₂) (prod.map (𝟙 W₁) c') ≫ prod.snd) ≫ c' := by
    simpa using hc prod.snd
  refine ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk hw
    (fun s => Limits.pullback.lift s.fst (prod.lift (s.fst ≫ f₁) s.snd) ?_) ?_ ?_ ?_⟩⟩
  · refine prod.hom_ext ?_ ?_
    · simp
    · simp [s.condition]
  · exact fun s => Limits.pullback.lift_fst _ _ _
  · intro s
    rw [← Category.assoc, Limits.pullback.lift_snd, prod.lift_snd]
  · intro s m h₁ h₂
    refine Limits.pullback.hom_ext ?_ ?_
    · rw [Limits.pullback.lift_fst]
      exact h₁
    · rw [Limits.pullback.lift_snd]
      refine prod.hom_ext ?_ ?_
      · rw [prod.lift_fst, ← h₁, Category.assoc, Category.assoc]
        exact congrArg (m ≫ ·) (by simpa using (hc prod.fst).symm)
      · rw [prod.lift_snd, ← h₂, Category.assoc]

/-- The projection `H × W ⟶ W` is smooth, as a base change of `H ⟶ Spec(ℤ)`. -/
theorem smooth_productToBase : Smooth productToBase.{u} :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _)
    smooth_coordinateChangeGroupToSpecZ.{u}

/-! ### Smoothness from local Weierstrass equations and the coordinate-change torsor -/

/-- The identity triple `(1, 1, 1)` of a family with itself. -/
def identityComparison {S : Scheme.{u}} (E : PointedFamily S) : Comparison E E S where
  fst := 𝟙 S
  snd := 𝟙 S
  iso := Iso.refl _
  iso_map := Category.id_comp _
  zero_iso := Category.comp_id _

/-- **The smoothness half of the source's argument.** Suppose that `H × W` is a fibre product
`W ×_{𝓜₁,₁} W`, with second projection the projection `H × W ⟶ W`, and that the elliptic curve
`E'` over `S'` has a Weierstrass equation Zariski locally on `S'`. Then for every fibre product
`P = W ×_{𝓜₁,₁} S'` the projection `P ⟶ S'` is smooth: over an open `U` on which `E'` is the
restriction of the Weierstrass family along `a : U ⟶ W`, the scheme `P ×_{S'} U` is the base
change of `H × W ⟶ W` along `a`. -/
theorem smooth_snd_of_locally_comparison
    (rW : RepresentsComparisons family.{u} family.{u} coordinateChangeProduct.{u})
    (hW : (rW.homEquiv _ (𝟙 _)).snd = productToBase.{u}) {S' : Scheme.{u}}
    (E' : PointedFamily S') (hloc : ∀ s : S', ∃ U : S'.Opens, s ∈ U ∧
      ∃ x : Comparison family.{u} E' U.toScheme, x.snd = U.ι)
    (P : Scheme.{u}) (r : RepresentsComparisons family.{u} E' P) :
    Smooth (r.homEquiv P (𝟙 P)).snd := by
  have : IsZariskiLocalAtTarget @Smooth.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _
  choose U hU x hx using hloc
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @Smooth) U
    (eq_top_iff.mpr fun s _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨s, hU s⟩) fun s => ?_
  let r₁ := r.restrictSnd (U s)
  let r₂ := (rW.ofComparisons (identityComparison family.{u}) (x s) rfl (hx s)).ofFamilyIso
    (PointedFamily.pullbackIdIso family.{u}) (FamilyIso.refl _)
  have h₂ : Smooth (r₂.homEquiv _ (𝟙 _)).snd := by
    have e : (r₂.homEquiv _ (𝟙 _)).snd = Limits.pullback.snd
        (prod.lift (rW.homEquiv _ (𝟙 _)).fst (rW.homEquiv _ (𝟙 _)).snd)
        (prod.map (𝟙 base.{u}) (x s).fst) ≫ prod.snd := Category.id_comp _
    rw [e]
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (isPullback_pullback_prodLift_prodMap (rW.homEquiv _ (𝟙 _)).fst
        (rW.homEquiv _ (𝟙 _)).snd (x s).fst) (hW ▸ smooth_productToBase)
  have h₁ := RepresentsComparisons.uniqueIso_hom_snd r₁ r₂
  rw [RepresentsComparisons.restrictSnd_snd] at h₁
  rw [← h₁]
  have : Smooth (RepresentsComparisons.uniqueIso r₁ r₂).hom := inferInstance
  exact MorphismProperty.comp_mem _ _ _ this h₂

/-! ### Surjectivity from Weierstrass equations of the fibres -/

/-- **The surjectivity half of the source's argument.** If the fibre of `E'` at every point
`s'` of `S'` has a Weierstrass equation, that is, it is the restriction of the Weierstrass family
along a point of `W` with values in `κ(s')`, then for every fibre product
`P = W ×_{𝓜₁,₁} S'` the projection `P ⟶ S'` is surjective: the Weierstrass equation at `s'` is a
point of `P` over `s'`. -/
theorem surjective_snd_of_comparison_residueField {S' : Scheme.{u}} (E' : PointedFamily S')
    (hW : ∀ s' : S', ∃ x : Comparison family.{u} E' (Spec (S'.residueField s')),
      x.snd = S'.fromSpecResidueField s')
    (P : Scheme.{u}) (r : RepresentsComparisons family.{u} E' P) :
    AlgebraicGeometry.Surjective (r.homEquiv P (𝟙 P)).snd := by
  refine ⟨fun s' => ?_⟩
  obtain ⟨x, hx⟩ := hW s'
  have hsnd : x.snd = (r.homEquiv (Spec (S'.residueField s'))).symm x ≫
      (r.homEquiv P (𝟙 P)).snd := by
    simpa using r.snd_homEquiv ((r.homEquiv (Spec (S'.residueField s'))).symm x)
  obtain ⟨p, hp⟩ : s' ∈ Set.range (S'.fromSpecResidueField s').base := by
    rw [Scheme.range_fromSpecResidueField]
    exact Set.mem_singleton _
  refine ⟨((r.homEquiv (Spec (S'.residueField s'))).symm x).base p, ?_⟩
  rw [← hx, hsnd] at hp
  simpa using hp

/-- A Weierstrass equation for `E'` over an open `U ∋ s'` restricts to one for the fibre of `E'`
at `s'`. -/
theorem exists_comparison_residueField_of_restrict {S' : Scheme.{u}} {E' : PointedFamily S'}
    {s' : S'} {U : S'.Opens} (hs : s' ∈ U) (x : Comparison family.{u} E' U.toScheme)
    (hx : x.snd = U.ι) :
    ∃ y : Comparison family.{u} E' (Spec (S'.residueField s')),
      y.snd = S'.fromSpecResidueField s' := by
  have hrange : Set.range (S'.fromSpecResidueField s').base ⊆ Set.range U.ι.base := by
    rw [Scheme.range_fromSpecResidueField, U.range_ι]
    rintro _ rfl
    exact hs
  refine ⟨x.baseChange (IsOpenImmersion.lift U.ι _ hrange), ?_⟩
  rw [Comparison.baseChange_snd, hx, IsOpenImmersion.lift_fac]

/-! ### The smooth cover -/

/-- **Stacks Project, Tag 072T.** The morphism `W ⟶ 𝓜₁,₁` given by the Weierstrass family
`(E_W, f_W, 0_W)` is smooth: for every elliptic curve `E'` over a scheme `S'` and every fibre
product `P = W ×_{𝓜₁,₁} S'`, the projection `P ⟶ S'` is smooth. Over an open of `S'` on which
`E'` has a Weierstrass equation, `P` is the base change of the smooth projection `H × W ⟶ W`,
because `H × W` is the fibre product `W ×_{𝓜₁,₁} W`. -/
@[stacks 072T "the morphism W → M_{1,1} is smooth"]
theorem isSmooth_family : family.{u}.IsSmooth isElliptic_family.{u} := by
  intro S' E' hE' P r
  exact smooth_snd_of_locally_comparison representsComparisons_coordinateChange
    representsComparisons_coordinateChange_homEquiv_id_snd E'
    (localWeierstrassAt_of_noetherian localWeierstrassNoetherian E' hE') P r

/-- **Stacks Project, Tag 072T.** The morphism `W ⟶ 𝓜₁,₁` given by the Weierstrass family
`(E_W, f_W, 0_W)` is surjective: for every elliptic curve `E'` over a scheme `S'` and every fibre
product `P = W ×_{𝓜₁,₁} S'`, the projection `P ⟶ S'` is surjective, because the fibre of `E'` at
each point has a Weierstrass equation. -/
@[stacks 072T "the morphism W → M_{1,1} is surjective"]
theorem isSurjective_family : family.{u}.IsSurjective isElliptic_family.{u} := by
  intro S' E' hE' P r
  exact surjective_snd_of_comparison_residueField E'
    (exists_comparison_fromSpecResidueField E' hE') P r

/-- **Stacks Project, Tag 072R**, condition (3): the moduli stack `𝓜₁,₁` of elliptic curves
has a smooth surjective cover by a scheme, namely the Weierstrass family over
`W = Spec(ℤ[a₁, a₂, a₃, a₄, a₆, 1/Δ])`. -/
theorem hasSmoothSurjectiveCover : HasSmoothSurjectiveCover.{u} :=
  ⟨base.{u}, family.{u}, isElliptic_family.{u}, isSmooth_family, isSurjective_family⟩

end AlgebraicGeometry.ModuliEllipticCurves.Weierstrass

end
