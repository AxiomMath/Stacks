module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.IntegralBaseFiniteDimension
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.PositiveRankSurjectivity
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.IntegralComponentSurjectivity
public import StacksFrontier.AlgebraicGeometry.Chow.BoundedDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.MaximalDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.FlatPullbackPrincipalDivisor

/-!
# The devissage of Stacks 02TT

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project. Granted that flat pullback
along the projection of affine space is surjective over every base, this file proves that flat
pullback is surjective along **every** affine-space bundle. That is the devissage of the first two
paragraphs of the proof of Stacks 02TT, assembled from its two steps:

* the reduction of an arbitrary base to the integral closed subschemes carrying the images of the
  components of a class, `Stacks.Chow.flatPullbackChow_surjective_of_forall_integralComponent`;
* the induction over an integral base,
  `Stacks.Chow.flatPullbackChow_surjective_isIntegral_of_forall_schemeDeltaDimension_lt`, which
  descends on the delta-dimension of the base by passing to the reduced complement of a
  trivializing open subscheme.

## Why the two steps have to be interleaved this way

The induction on the delta-dimension is only available above a floor and only for a base of
*finite* delta-dimension (`Stacks.Chow.schemeDeltaDimension_induction`), and a scheme merely
locally of finite type over `S` can have delta-dimension `⊤`. So the induction cannot be run at an
arbitrary base at all. The first step repairs this: it replaces an arbitrary base `Y` by the
integral closed subschemes `closure {y}`, each of which is irreducible and therefore of finite
delta-dimension (`Stacks.Chow.schemeDeltaDimension_lt_top_integralComponentAt`).

Inside the induction the first step is used again, and for a different reason: the induction
hypothesis is available for every base of smaller delta-dimension, but the base reached at a given
stage need not be integral, whereas the induction *step* needs an integral base. The first step
supplies that too, and does not raise the delta-dimension — a closed subscheme has
delta-dimension at most that of the ambient scheme.

Below the floor `k` there is nothing to prove: a base of delta-dimension `< k` has
`A_k = 0`, and the total space of a bundle of rank `r` over it has `A_{k+r} = 0`, because the
relative dimension of a point of the total space exceeds that of its image by at most `r`
(`Stacks.Chow.toNat_residueTrdeg_le_of_relativeDimension`). A homomorphism into the zero group is
surjective.

## Main results

* `Stacks.Chow.flatPullbackChow_surjective_of_isAffineSpaceBundle_of_forall_trivial` — the
  devissage: surjectivity of flat pullback along an affine-space bundle of rank `r`, from
  surjectivity along the trivial bundle over every base.

## Implementation notes

No `@[stacks 02TT]` attribute is placed here. The statement of that tag is the surjectivity for a
bundle whose rank is arbitrary and whose trivial-bundle input is *discharged*; that is
`Stacks.Chow.flatPullbackChow_surjective_of_isAffineSpaceBundle` in
`StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.PositiveRankSurjectivity`, where the attribute
sits. What is proved here still takes the trivial-bundle case as a hypothesis.

## References

* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT)
* [Stacks Project, Tag 02QP](https://stacks.math.columbia.edu/tag/02QP)
* [Stacks Project, Tag 02QR](https://stacks.math.columbia.edu/tag/02QR)
* [Stacks Project, Tag 02JW](https://stacks.math.columbia.edu/tag/02JW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

attribute [local instance] flat_affineSpaceOver locallyOfFiniteType_comapRestrict
  flat_comapRestrict

/-- An element of `EInt` strictly below an integer `k` is at most `k - 1`. -/
theorem le_sub_one_of_lt_coe {x : EInt} {k : ℤ} (h : x < (k : EInt)) :
    x ≤ ((k - 1 : ℤ) : EInt) := by
  induction x using WithBotTop.rec with
  | bot => exact bot_le
  | coe d =>
    rw [WithBotTop.coe_lt_coe] at h
    exact WithBotTop.coe_le_coe.mpr (by omega)
  | top => exact absurd h (not_lt.mpr le_top)

/-- **Below the floor there is nothing to prove.** If the base of an affine-space bundle of rank
`r` has delta-dimension `< k`, then the total space has no point of relative dimension `k + r`,
so `A_{k+r}` of the total space vanishes and every homomorphism into it is surjective.

The relative dimension of a point of the total space is that of its image plus the transcendence
degree of the residue-field extension, and that degree is at most `r` for a morphism of relative
dimension `r`. -/
theorem flatPullbackChow_surjective_of_schemeDeltaDimension_lt (C : ChowSituation.{u})
    {A B : Scheme.{u}} (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (v : A ⟶ B)
    [LocallyOfFiniteType v] [AlgebraicGeometry.Flat v] (r : ℕ)
    (hv : AlgebraicGeometry.RelativeDimension v r) (k : ℤ)
    (hlt : schemeDeltaDimension C sB < (k : EInt)) :
    Function.Surjective (flatPullbackChowOfRelativeDimension C (v ≫ sB) sB v rfl r hv k) := by
  have hk : ∀ x : A,
      relativeDimension C.dimensionFunction (v ≫ sB) x ≠ k + (r : ℤ) := by
    intro x
    have hadd := relativeDimension_comp_eq_add_trdeg C.dimensionFunction sB v x
    have hbase := relativeDimension_le_of_schemeDeltaDimension_le' C sB
      (le_sub_one_of_lt_coe hlt) (v.base x)
    have htr := toNat_residueTrdeg_le_of_relativeDimension v r hv x
    omega
  intro β
  exact ⟨0, (map_zero _).trans (chowGroup_eq_zero C (v ≫ sB) hk β).symm⟩

/-- **The devissage of Stacks 02TT.** Let `(S, δ)` be the base situation of chapter 42 and assume
that flat pullback along the projection `𝔸^s_B ⟶ B` is surjective in every degree over every base
`B` locally of finite type over `S`. Then for every affine-space bundle `f : X ⟶ Y` of rank `r`
over a base locally of finite type over `S`, flat pullback `f^* : A_k(Y) ⟶ A_{k+r}(X)` is
surjective.

The statement is proved for a base of finite delta-dimension by strong induction on it: below the
floor `k` both Chow groups vanish, and at a given delta-dimension the base is replaced by the
integral closed subschemes carrying the images of the components of a class
(`Stacks.Chow.flatPullbackChow_surjective_of_forall_integralComponent`), over which the induction
step
`Stacks.Chow.flatPullbackChow_surjective_isIntegral_of_forall_schemeDeltaDimension_lt` applies.
An arbitrary base is then reduced to those same integral closed subschemes, which have finite
delta-dimension because they are irreducible. -/
theorem flatPullbackChow_surjective_of_isAffineSpaceBundle_of_forall_trivial
    (C : ChowSituation.{u})
    (htriv : ∀ (B : Scheme.{u}) (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (s : ℕ) (j : ℤ),
      Function.Surjective (flatPullbackChowOfRelativeDimension C
        ((𝔸(ULift.{u} (Fin s); B) ↘ B) ≫ sB) sB (𝔸(ULift.{u} (Fin s); B) ↘ B) rfl s
        (relativeDimension_affineSpaceOver B s) j))
    {X Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [AlgebraicGeometry.Flat f] (r : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f r) (hbundle : IsAffineSpaceBundle f r) (k : ℤ) :
    Function.Surjective (flatPullbackChowOfRelativeDimension C (f ≫ sY) sY f rfl r hf k) := by
  -- the statement over a base of finite delta-dimension, by induction on it
  have key : ∀ (B : Scheme.{u}) (sB : B ⟶ C.S) [LocallyOfFiniteType sB],
      schemeDeltaDimension C sB < ⊤ →
      ∀ (A : Scheme.{u}) (v : A ⟶ B) [LocallyOfFiniteType v] [AlgebraicGeometry.Flat v]
        (hv : AlgebraicGeometry.RelativeDimension v r), IsAffineSpaceBundle v r →
        Function.Surjective (flatPullbackChowOfRelativeDimension C (v ≫ sB) sB v rfl r hv k) := by
    intro B sB _ hfin
    refine schemeDeltaDimension_induction C k
      (P := fun B sB _ ↦ ∀ (A : Scheme.{u}) (v : A ⟶ B) [LocallyOfFiniteType v]
        [AlgebraicGeometry.Flat v] (hv : AlgebraicGeometry.RelativeDimension v r),
        IsAffineSpaceBundle v r →
        Function.Surjective (flatPullbackChowOfRelativeDimension C (v ≫ sB) sB v rfl r hv k))
      (fun B' sB' _ hlt A v _ _ hv _ ↦
        flatPullbackChow_surjective_of_schemeDeltaDimension_lt C sB' v r hv k hlt) ?_ sB hfin
    -- the induction step
    intro n hkn ih B' sB' _ hdim A v _ _ hv hbv
    let := quasiCompact_of_isAffineSpaceBundle v r hbv
    refine flatPullbackChow_surjective_of_forall_integralComponent C sB' v r hv k ?_
    intro y sW _ hgb hg
    subst hgb
    let := isIntegral_integralComponentAt y
    -- the delta-dimension of a closed subscheme does not exceed that of the ambient scheme
    have hle : schemeDeltaDimension C ((integralComponentAt y).subschemeι ≫ sB') ≤ (n : EInt) :=
      schemeDeltaDimension_le_of_forall_relativeDimension_le C sB'
        (integralComponentAt y).subschemeι fun w ↦
          relativeDimension_le_of_schemeDeltaDimension_le' C sB' hdim.le _
    refine flatPullbackChow_surjective_isIntegral_of_forall_schemeDeltaDimension_lt C htriv
      ((integralComponentAt y).subschemeι ≫ sB') (comapRestrict (integralComponentAt y) v) r hg
      (isAffineSpaceBundle_comapRestrict v hbv (integralComponentAt y)) k ?_
    intro Z' W sZ' _ sW _ g _ _ hgb' hg' hbg hltZ'
    subst hgb'
    exact ih Z' sZ' (lt_of_lt_of_le hltZ' hle) W g hg' hbg
  -- an arbitrary base: reduce to the integral closed subschemes, which are irreducible
  let := quasiCompact_of_isAffineSpaceBundle f r hbundle
  refine flatPullbackChow_surjective_of_forall_integralComponent C sY f r hf k ?_
  intro y sW _ hgb hg
  subst hgb
  exact key ((integralComponentAt y).subscheme) ((integralComponentAt y).subschemeι ≫ sY)
    (schemeDeltaDimension_lt_top_integralComponentAt C sY y) _
    (comapRestrict (integralComponentAt y) f) hg
    (isAffineSpaceBundle_comapRestrict f hbundle (integralComponentAt y))

/-- Surjectivity of flat pullback along the projection of affine `r`-space, from the
relative-dimension-one case alone: `Stacks.Chow.flatPullbackChow_surjective_affineSpaceOver` with
its Stacks 02S1 hypothesis discharged by
`Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_general`. -/
theorem flatPullbackChow_surjective_affineSpaceOver_of_rankOne (C : ChowSituation.{u})
    (hone : ∀ (B : Scheme.{u}) (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (j : ℤ),
      Function.Surjective (flatPullbackChowOfRelativeDimension C
        ((𝔸(ULift.{u} (Fin 1); B) ↘ B) ≫ sB) sB
        (𝔸(ULift.{u} (Fin 1); B) ↘ B) rfl 1 (relativeDimension_affineSpaceOver B 1) j))
    (r : ℕ) (T : Scheme.{u}) (sT : T ⟶ C.S) [LocallyOfFiniteType sT] (k : ℤ) :
    Function.Surjective (flatPullbackChowOfRelativeDimension C
      ((𝔸(ULift.{u} (Fin r); T) ↘ T) ≫ sT) sT
      (𝔸(ULift.{u} (Fin r); T) ↘ T) rfl r (relativeDimension_affineSpaceOver T r) k) :=
  flatPullbackChow_surjective_affineSpaceOver C
    (@flatPullbackFactorsThroughRationalEquivalence_general C) hone r T sT k

/-- Surjectivity of flat pullback along an affine-space bundle of rank `r`, from the
relative-dimension-one case alone: the rank induction is
`Stacks.Chow.flatPullbackChow_surjective_affineSpaceOver_of_rankOne` and the devissage is
`Stacks.Chow.flatPullbackChow_surjective_of_isAffineSpaceBundle_of_forall_trivial`. -/
theorem flatPullbackChow_surjective_of_isAffineSpaceBundle_of_rankOne (C : ChowSituation.{u})
    (hone : ∀ (B : Scheme.{u}) (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (j : ℤ),
      Function.Surjective (flatPullbackChowOfRelativeDimension C
        ((𝔸(ULift.{u} (Fin 1); B) ↘ B) ≫ sB) sB
        (𝔸(ULift.{u} (Fin 1); B) ↘ B) rfl 1 (relativeDimension_affineSpaceOver B 1) j))
    {X Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [AlgebraicGeometry.Flat f] (r : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f r) (hbundle : IsAffineSpaceBundle f r) (k : ℤ) :
    Function.Surjective (flatPullbackChowOfRelativeDimension C (f ≫ sY) sY f rfl r hf k) :=
  flatPullbackChow_surjective_of_isAffineSpaceBundle_of_forall_trivial C
    (fun B sB _ s j ↦ flatPullbackChow_surjective_affineSpaceOver_of_rankOne C hone s B sB j)
    sY f r hf hbundle k

end Stacks.Chow

end
