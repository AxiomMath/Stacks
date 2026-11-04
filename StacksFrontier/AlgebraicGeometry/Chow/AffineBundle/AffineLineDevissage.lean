module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.BaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.IntegralImageAssembly
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.PrimeCycleDevissage
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.PrimeCycleTransport
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.QuasiCompactBundle
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.RankOneUtilities
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.TrivialBundle
public import StacksFrontier.AlgebraicGeometry.Chow.DeltaDimensionInduction

/-!
# The affine line: surjectivity of flat pullback over an arbitrary base

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project. This file proves that
flat pullback along the projection `𝔸^1_B ⟶ B` of the affine line is surjective in every degree
and over every base `B` locally of finite type over `S`. That is the rank-one case of Stacks
02TT, from which the general case follows by the devissage of
`StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.Devissage`.

## The argument

Everything is reduced to one special configuration. By
`Stacks.Chow.flatPullbackChow_surjective_of_forall_primeCycle` it suffices to lift, for each
point `x` of `𝔸^1_B`, the class of a single prime cycle: the prime cycle of the closure of `x`,
transported to the inverse image of the integral closed subscheme `Z = closure {f x}` of the base
attached to the image of `x`. Over that inverse image two simplifications happen at once. First,
pullback along a closed immersion carries a prime cycle to a prime cycle — that is the lemma
`cyclePullbackAlongClosedImmersion_cycleAssociatedToClosedSubscheme_integralComponentAt` of the
`Stacks.Chow` namespace — so the class to be lifted is again the class of a prime cycle. Second,
the restricted bundle is a
base change of `𝔸^1_B ⟶ B`, hence *globally* trivial over `Z`
(`Stacks.Chow.isTrivialAffineSpaceBundle_of_isPullback`); relabelling the inverse image by that
trivialization moves the problem to `𝔸^1_Z ⟶ Z` with `Z` integral
(`Stacks.Chow.mem_range_flatPullbackChow_primeCycle_of_isIso_comp`). Finally the point of `𝔸^1_Z`
one has to treat dominates `Z`, because `x` is the generic point of `Z`'s inverse image of its
own closure; so the configuration reached is exactly the one the carried hypothesis speaks
about.

That reduction is run twice, exactly as in the devissage of Stacks 02TT. First over a base of
*finite* delta-dimension, where `Stacks.Chow.schemeDeltaDimension_induction` supplies the
hypothesis of the carried statement about bases of smaller delta-dimension — the base case being
the vanishing of the target Chow group below the floor,
`Stacks.Chow.flatPullbackChow_surjective_of_schemeDeltaDimension_lt`. Then over an arbitrary
base, whose delta-dimension may be `⊤`: there the reduction replaces the base by the integral
closed subschemes `Z`, which are irreducible and therefore of finite delta-dimension
(`Stacks.Chow.schemeDeltaDimension_lt_top_integralComponentAt`), so the first statement applies
to every base below them.

## Main results

* `Stacks.Chow.flatPullbackChow_surjective_affineLineOver_of_dominant` — flat pullback along
  `𝔸^1_B ⟶ B` is surjective in every degree and over every base, granted the dominant
  prime-cycle step.

## Implementation notes

The one hypothesis carried through this file, `hdom`, is the fourth step of the proof of Stacks
02TT: over an *integral* base `Y` of delta-dimension `n`, and granted surjectivity of flat
pullback along the affine line over every base of delta-dimension smaller than `n`, the class of
the prime cycle of a point of `𝔸^1_Y` *dominating* `Y` is a flat pullback. It is not proved here;
it is discharged in a separate file, and this file is everything around it.

No `@[stacks 02TT]` attribute is placed here: the statement of that tag is surjectivity for a
bundle of arbitrary rank with no hypothesis carried, and the attribute sits on
`Stacks.Chow.flatPullbackChow_surjective_of_isAffineSpaceBundle` in
`StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.PositiveRankSurjectivity`.

## References

* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT)
* [Stacks Project, Tag 02QP](https://stacks.math.columbia.edu/tag/02QP)
* [Stacks Project, Tag 02RD](https://stacks.math.columbia.edu/tag/02RD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

attribute [local instance] flat_affineSpaceOver locallyOfFiniteType_comapRestrict
  flat_comapRestrict

/-- **The shared inner step.** Let `f : 𝔸^1_B ⟶ B` be the projection of the affine line, let `x`
be a point of `𝔸^1_B`, and let `Z = closure {f x}` be the integral closed subscheme of `B`
attached to its image. Granted the dominant prime-cycle step `hdom` and surjectivity of flat
pullback along the affine line over every base of delta-dimension smaller than that of `Z`, the
class on `f^{-1}(Z)` of the prime cycle of `closure {x}` is in the range of flat pullback along
the restriction `f^{-1}(Z) ⟶ Z`.

This is precisely the hypothesis
`Stacks.Chow.flatPullbackChow_surjective_of_forall_primeCycle` consumes, at the point `x`.

The point `x` lies in `f^{-1}(Z)`, since `f x` lies in `Z`; so the class to be lifted is the
class of a prime cycle of `f^{-1}(Z)` itself. The restriction `f^{-1}(Z) ⟶ Z` is a base change of
`f`, hence a globally trivial bundle of rank one, and relabelling its source by a trivialization
`e` reduces the goal to the corresponding statement for `𝔸^1_Z ⟶ Z`. The point of `𝔸^1_Z` thus
reached lies over the generic point of `Z`, because a closed immersion is injective on points and
both that image and the generic point of `Z` are carried to `f x`. -/
private theorem mem_range_primeCycle_comapRestrict (C : ChowSituation.{u}) (j : ℤ)
    (hdom : ∀ (Y : Scheme.{u}) [IsIntegral Y] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (n : ℤ),
      schemeDeltaDimension C sY = (n : EInt) →
      (∀ (B : Scheme.{u}) (sB : B ⟶ C.S) [LocallyOfFiniteType sB],
        schemeDeltaDimension C sB < (n : EInt) →
        Function.Surjective (flatPullbackChowOfRelativeDimension C
          ((𝔸(ULift.{u} (Fin 1); B) ↘ B) ≫ sB) sB (𝔸(ULift.{u} (Fin 1); B) ↘ B) rfl 1
          (relativeDimension_affineSpaceOver B 1) j)) →
      ∀ w : ↥𝔸(ULift.{u} (Fin 1); Y),
        (𝔸(ULift.{u} (Fin 1); Y) ↘ Y).base w = genericPoint ↥Y →
        (QuotientAddGroup.mk' (rationalEquivalences C
            ((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ≫ sY) (j + ((1 : ℕ) : ℤ)))
          (cycleAssociatedToClosedSubscheme C ((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ≫ sY)
            (integralComponentAt w).subschemeι (j + ((1 : ℕ) : ℤ)))) ∈
        (flatPullbackChowOfRelativeDimension C ((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ≫ sY) sY
          (𝔸(ULift.{u} (Fin 1); Y) ↘ Y) rfl 1 (relativeDimension_affineSpaceOver Y 1) j).range)
    {B : Scheme.{u}} (sB : B ⟶ C.S) [LocallyOfFiniteType sB]
    (x : ↥𝔸(ULift.{u} (Fin 1); B))
    (hsm : ∀ (B'' : Scheme.{u}) (sB'' : B'' ⟶ C.S) [LocallyOfFiniteType sB''],
      schemeDeltaDimension C sB'' <
        schemeDeltaDimension C
          ((integralComponentAt ((𝔸(ULift.{u} (Fin 1); B) ↘ B).base x)).subschemeι ≫ sB) →
      Function.Surjective (flatPullbackChowOfRelativeDimension C
        ((𝔸(ULift.{u} (Fin 1); B'') ↘ B'') ≫ sB'') sB'' (𝔸(ULift.{u} (Fin 1); B'') ↘ B'') rfl 1
        (relativeDimension_affineSpaceOver B'' 1) j)) :
    (QuotientAddGroup.mk' (rationalEquivalences C
        (((integralComponentAt ((𝔸(ULift.{u} (Fin 1); B) ↘ B).base x)).comap
            (𝔸(ULift.{u} (Fin 1); B) ↘ B)).subschemeι ≫
          (𝔸(ULift.{u} (Fin 1); B) ↘ B) ≫ sB) (j + ((1 : ℕ) : ℤ)))
      (cyclePullbackAlongClosedImmersion C
        (((integralComponentAt ((𝔸(ULift.{u} (Fin 1); B) ↘ B).base x)).comap
            (𝔸(ULift.{u} (Fin 1); B) ↘ B)).subschemeι ≫
          (𝔸(ULift.{u} (Fin 1); B) ↘ B) ≫ sB) ((𝔸(ULift.{u} (Fin 1); B) ↘ B) ≫ sB)
        ((integralComponentAt ((𝔸(ULift.{u} (Fin 1); B) ↘ B).base x)).comap
          (𝔸(ULift.{u} (Fin 1); B) ↘ B)).subschemeι rfl (j + ((1 : ℕ) : ℤ))
        (cycleAssociatedToClosedSubscheme C ((𝔸(ULift.{u} (Fin 1); B) ↘ B) ≫ sB)
          (integralComponentAt x).subschemeι (j + ((1 : ℕ) : ℤ))))) ∈
      (flatPullbackChowOfRelativeDimension C
        (((integralComponentAt ((𝔸(ULift.{u} (Fin 1); B) ↘ B).base x)).comap
            (𝔸(ULift.{u} (Fin 1); B) ↘ B)).subschemeι ≫
          (𝔸(ULift.{u} (Fin 1); B) ↘ B) ≫ sB)
        ((integralComponentAt ((𝔸(ULift.{u} (Fin 1); B) ↘ B).base x)).subschemeι ≫ sB)
        (comapRestrict (integralComponentAt ((𝔸(ULift.{u} (Fin 1); B) ↘ B).base x))
          (𝔸(ULift.{u} (Fin 1); B) ↘ B))
        (comapRestrict_comp_base C ((𝔸(ULift.{u} (Fin 1); B) ↘ B) ≫ sB) sB
          (𝔸(ULift.{u} (Fin 1); B) ↘ B) rfl
          (integralComponentAt ((𝔸(ULift.{u} (Fin 1); B) ↘ B).base x))) 1
        (relativeDimension_comapRestrict
          (integralComponentAt ((𝔸(ULift.{u} (Fin 1); B) ↘ B).base x))
          (𝔸(ULift.{u} (Fin 1); B) ↘ B) (relativeDimension_affineSpaceOver B 1)) j).range := by
  let _ : IsIntegral
      (integralComponentAt ((𝔸(ULift.{u} (Fin 1); B) ↘ B).base x)).subscheme :=
    isIntegral_integralComponentAt _
  -- the point `x` lies in the inverse image of the closure of its image
  obtain ⟨x', hx'⟩ : x ∈ Set.range
      ((integralComponentAt ((𝔸(ULift.{u} (Fin 1); B) ↘ B).base x)).comap
        (𝔸(ULift.{u} (Fin 1); B) ↘ B)).subschemeι.base := by
    rw [Scheme.IdealSheafData.range_subschemeι, coe_support_comap]
    simpa only [Set.mem_preimage, coe_support_integralComponentAt] using
      subset_closure (Set.mem_singleton ((𝔸(ULift.{u} (Fin 1); B) ↘ B).base x))
  -- so the class to be lifted is the class of a prime cycle of the inverse image
  have hcyc :=
    cyclePullbackAlongClosedImmersion_cycleAssociatedToClosedSubscheme_integralComponentAt C
      (((integralComponentAt ((𝔸(ULift.{u} (Fin 1); B) ↘ B).base x)).comap
          (𝔸(ULift.{u} (Fin 1); B) ↘ B)).subschemeι ≫ (𝔸(ULift.{u} (Fin 1); B) ↘ B) ≫ sB)
      ((𝔸(ULift.{u} (Fin 1); B) ↘ B) ≫ sB)
      ((integralComponentAt ((𝔸(ULift.{u} (Fin 1); B) ↘ B).base x)).comap
        (𝔸(ULift.{u} (Fin 1); B) ↘ B)).subschemeι rfl (j + ((1 : ℕ) : ℤ)) x'
  rw [hx'] at hcyc
  rw [hcyc]
  -- the restricted bundle is globally trivial, being a base change of the affine line
  obtain ⟨e, he⟩ : IsTrivialAffineSpaceBundle
      (comapRestrict (integralComponentAt ((𝔸(ULift.{u} (Fin 1); B) ↘ B).base x))
        (𝔸(ULift.{u} (Fin 1); B) ↘ B)) 1 :=
    isTrivialAffineSpaceBundle_of_isPullback
      (isPullback_comapRestrict (integralComponentAt ((𝔸(ULift.{u} (Fin 1); B) ↘ B).base x))
        (𝔸(ULift.{u} (Fin 1); B) ↘ B)) 1 (isTrivialAffineSpaceBundle_affineSpaceOver B 1)
  -- the delta-dimension of the integral closed subscheme is an integer
  obtain ⟨n, hn⟩ := exists_schemeDeltaDimension_eq_integralComponentAt C sB
    ((𝔸(ULift.{u} (Fin 1); B) ↘ B).base x)
  -- the point of `𝔸^1_Z` reached dominates `Z`
  have hdomination :
      (𝔸(ULift.{u} (Fin 1);
            (integralComponentAt ((𝔸(ULift.{u} (Fin 1); B) ↘ B).base x)).subscheme) ↘
          (integralComponentAt ((𝔸(ULift.{u} (Fin 1); B) ↘ B).base x)).subscheme).base
          (e.hom.base x') =
        genericPoint ↥(integralComponentAt ((𝔸(ULift.{u} (Fin 1); B) ↘ B).base x)).subscheme := by
    have h1 : (𝔸(ULift.{u} (Fin 1);
          (integralComponentAt ((𝔸(ULift.{u} (Fin 1); B) ↘ B).base x)).subscheme) ↘
        (integralComponentAt ((𝔸(ULift.{u} (Fin 1); B) ↘ B).base x)).subscheme).base
          (e.hom.base x') =
        (comapRestrict (integralComponentAt ((𝔸(ULift.{u} (Fin 1); B) ↘ B).base x))
          (𝔸(ULift.{u} (Fin 1); B) ↘ B)).base x' := by
      rw [← he]
      rfl
    have h2 : (integralComponentAt ((𝔸(ULift.{u} (Fin 1); B) ↘ B).base x)).subschemeι.base
        ((comapRestrict (integralComponentAt ((𝔸(ULift.{u} (Fin 1); B) ↘ B).base x))
          (𝔸(ULift.{u} (Fin 1); B) ↘ B)).base x') =
        (𝔸(ULift.{u} (Fin 1); B) ↘ B).base x := by
      have h : (comapRestrict (integralComponentAt ((𝔸(ULift.{u} (Fin 1); B) ↘ B).base x))
            (𝔸(ULift.{u} (Fin 1); B) ↘ B) ≫
          (integralComponentAt ((𝔸(ULift.{u} (Fin 1); B) ↘ B).base x)).subschemeι).base x' =
          (((integralComponentAt ((𝔸(ULift.{u} (Fin 1); B) ↘ B).base x)).comap
            (𝔸(ULift.{u} (Fin 1); B) ↘ B)).subschemeι ≫
              (𝔸(ULift.{u} (Fin 1); B) ↘ B)).base x' := by
        rw [comapRestrict_subschemeι]
      exact h.trans (congrArg (𝔸(ULift.{u} (Fin 1); B) ↘ B).base hx')
    have h3 : (integralComponentAt ((𝔸(ULift.{u} (Fin 1); B) ↘ B).base x)).subschemeι.base
        (genericPoint
          ↥(integralComponentAt ((𝔸(ULift.{u} (Fin 1); B) ↘ B).base x)).subscheme) =
        (𝔸(ULift.{u} (Fin 1); B) ↘ B).base x := by
      simpa [genericPointOf] using
        genericPointOf_integralComponentAt ((𝔸(ULift.{u} (Fin 1); B) ↘ B).base x)
    exact (integralComponentAt
      ((𝔸(ULift.{u} (Fin 1); B) ↘ B).base x)).subschemeι.isClosedEmbedding.injective
        (by rw [h1, h2, h3])
  -- transport the goal along the trivialization and apply the carried hypothesis
  refine mem_range_flatPullbackChow_primeCycle_of_isIso_comp C _ _ _ e.hom _ _ he ?_ rfl _ 1 _ _
    j x'
    (hdom (integralComponentAt ((𝔸(ULift.{u} (Fin 1); B) ↘ B).base x)).subscheme
      ((integralComponentAt ((𝔸(ULift.{u} (Fin 1); B) ↘ B).base x)).subschemeι ≫ sB) n hn
      (fun B'' sB'' _ h ↦ hsm B'' sB'' (by rw [hn]; exact h)) (e.hom.base x') hdomination)
  rw [← Category.assoc, he]
  exact comapRestrict_comp_base C ((𝔸(ULift.{u} (Fin 1); B) ↘ B) ≫ sB) sB
    (𝔸(ULift.{u} (Fin 1); B) ↘ B) rfl
    (integralComponentAt ((𝔸(ULift.{u} (Fin 1); B) ↘ B).base x))

/-- **The rank-one case of Stacks 02TT over a base of finite delta-dimension.** Granted the
dominant prime-cycle step `hdom`, flat pullback along the projection `𝔸^1_B ⟶ B` is surjective in
degree `j` for every base `B` locally of finite type over `S` whose delta-dimension is finite.

The proof is strong induction on the delta-dimension of the base
(`Stacks.Chow.schemeDeltaDimension_induction`), with floor `j`. Below the floor the target Chow
group vanishes (`Stacks.Chow.flatPullbackChow_surjective_of_schemeDeltaDimension_lt`). At
delta-dimension `d` the problem is reduced to prime cycles
(`Stacks.Chow.flatPullbackChow_surjective_of_forall_primeCycle`) and each of them is handled by
`Stacks.Chow.mem_range_primeCycle_comapRestrict`, whose hypothesis about smaller bases is the
induction hypothesis: the integral closed subscheme attached to a point of the base is a closed
subscheme of it and so has delta-dimension at most `d`. -/
private theorem key (C : ChowSituation.{u}) (j : ℤ)
    (hdom : ∀ (Y : Scheme.{u}) [IsIntegral Y] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (n : ℤ),
      schemeDeltaDimension C sY = (n : EInt) →
      (∀ (B : Scheme.{u}) (sB : B ⟶ C.S) [LocallyOfFiniteType sB],
        schemeDeltaDimension C sB < (n : EInt) →
        Function.Surjective (flatPullbackChowOfRelativeDimension C
          ((𝔸(ULift.{u} (Fin 1); B) ↘ B) ≫ sB) sB (𝔸(ULift.{u} (Fin 1); B) ↘ B) rfl 1
          (relativeDimension_affineSpaceOver B 1) j)) →
      ∀ w : ↥𝔸(ULift.{u} (Fin 1); Y),
        (𝔸(ULift.{u} (Fin 1); Y) ↘ Y).base w = genericPoint ↥Y →
        (QuotientAddGroup.mk' (rationalEquivalences C
            ((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ≫ sY) (j + ((1 : ℕ) : ℤ)))
          (cycleAssociatedToClosedSubscheme C ((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ≫ sY)
            (integralComponentAt w).subschemeι (j + ((1 : ℕ) : ℤ)))) ∈
        (flatPullbackChowOfRelativeDimension C ((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ≫ sY) sY
          (𝔸(ULift.{u} (Fin 1); Y) ↘ Y) rfl 1 (relativeDimension_affineSpaceOver Y 1) j).range)
    (B : Scheme.{u}) (sB : B ⟶ C.S) [LocallyOfFiniteType sB]
    (hfin : schemeDeltaDimension C sB < ⊤) :
    Function.Surjective (flatPullbackChowOfRelativeDimension C
      ((𝔸(ULift.{u} (Fin 1); B) ↘ B) ≫ sB) sB (𝔸(ULift.{u} (Fin 1); B) ↘ B) rfl 1
      (relativeDimension_affineSpaceOver B 1) j) := by
  refine schemeDeltaDimension_induction C j
    (P := fun B sB _ ↦ Function.Surjective (flatPullbackChowOfRelativeDimension C
      ((𝔸(ULift.{u} (Fin 1); B) ↘ B) ≫ sB) sB (𝔸(ULift.{u} (Fin 1); B) ↘ B) rfl 1
      (relativeDimension_affineSpaceOver B 1) j))
    (fun B' sB' _ hlt ↦ flatPullbackChow_surjective_of_schemeDeltaDimension_lt C sB'
      (𝔸(ULift.{u} (Fin 1); B') ↘ B') 1 (relativeDimension_affineSpaceOver B' 1) j hlt) ?_ sB hfin
  -- the induction step
  intro d _hjd ih B' sB' _ hdim
  refine flatPullbackChow_surjective_of_forall_primeCycle C sB'
    (𝔸(ULift.{u} (Fin 1); B') ↘ B') 1 (relativeDimension_affineSpaceOver B' 1) j fun x ↦ ?_
  refine mem_range_primeCycle_comapRestrict C j hdom sB' x fun B'' sB'' _ hlt ↦ ?_
  -- a closed subscheme has delta-dimension at most that of the ambient scheme
  have hle : schemeDeltaDimension C
      ((integralComponentAt ((𝔸(ULift.{u} (Fin 1); B') ↘ B').base x)).subschemeι ≫ sB') ≤
        (d : EInt) :=
    schemeDeltaDimension_le_of_forall_relativeDimension_le C sB'
      (integralComponentAt ((𝔸(ULift.{u} (Fin 1); B') ↘ B').base x)).subschemeι fun w ↦
        relativeDimension_le_of_schemeDeltaDimension_le' C sB' hdim.le _
  exact ih B'' sB'' (lt_of_lt_of_le hlt hle)

/-- **The rank-one case of Stacks 02TT.** Let `(S, δ)` be the base situation of chapter 42 of the
Stacks Project. Granted the dominant prime-cycle step `hdom` — the fourth step of the proof of
Stacks 02TT, discharged elsewhere — flat pullback along the projection `𝔸^1_B ⟶ B` of the affine
line, `A_j(B) ⟶ A_{j+1}(𝔸^1_B)`, is surjective in every degree `j` and over every base `B`
locally of finite type over `S`.

A base merely locally of finite type over `S` can have delta-dimension `⊤`, so
`Stacks.Chow.key` does not apply to it directly. The reduction to prime cycles
(`Stacks.Chow.flatPullbackChow_surjective_of_forall_primeCycle`) repairs this: each prime cycle
is handled over the integral closed subscheme of the base attached to the image of its point, and
such a subscheme is irreducible, hence of finite delta-dimension
(`Stacks.Chow.schemeDeltaDimension_lt_top_integralComponentAt`). So every base of strictly smaller
delta-dimension has finite delta-dimension too, and `Stacks.Chow.key` supplies the surjectivity
over it that `Stacks.Chow.mem_range_primeCycle_comapRestrict` asks for. -/
theorem flatPullbackChow_surjective_affineLineOver_of_dominant (C : ChowSituation.{u}) (j : ℤ)
    (hdom : ∀ (Y : Scheme.{u}) [IsIntegral Y] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (n : ℤ),
      schemeDeltaDimension C sY = (n : EInt) →
      (∀ (B : Scheme.{u}) (sB : B ⟶ C.S) [LocallyOfFiniteType sB],
        schemeDeltaDimension C sB < (n : EInt) →
        Function.Surjective (flatPullbackChowOfRelativeDimension C
          ((𝔸(ULift.{u} (Fin 1); B) ↘ B) ≫ sB) sB (𝔸(ULift.{u} (Fin 1); B) ↘ B) rfl 1
          (relativeDimension_affineSpaceOver B 1) j)) →
      ∀ w : ↥𝔸(ULift.{u} (Fin 1); Y),
        (𝔸(ULift.{u} (Fin 1); Y) ↘ Y).base w = genericPoint ↥Y →
        (QuotientAddGroup.mk' (rationalEquivalences C
            ((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ≫ sY) (j + ((1 : ℕ) : ℤ)))
          (cycleAssociatedToClosedSubscheme C ((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ≫ sY)
            (integralComponentAt w).subschemeι (j + ((1 : ℕ) : ℤ)))) ∈
        (flatPullbackChowOfRelativeDimension C ((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ≫ sY) sY
          (𝔸(ULift.{u} (Fin 1); Y) ↘ Y) rfl 1 (relativeDimension_affineSpaceOver Y 1) j).range)
    (B : Scheme.{u}) (sB : B ⟶ C.S) [LocallyOfFiniteType sB] :
    Function.Surjective (flatPullbackChowOfRelativeDimension C
      ((𝔸(ULift.{u} (Fin 1); B) ↘ B) ≫ sB) sB (𝔸(ULift.{u} (Fin 1); B) ↘ B) rfl 1
      (relativeDimension_affineSpaceOver B 1) j) := by
  refine flatPullbackChow_surjective_of_forall_primeCycle C sB
    (𝔸(ULift.{u} (Fin 1); B) ↘ B) 1 (relativeDimension_affineSpaceOver B 1) j fun x ↦ ?_
  refine mem_range_primeCycle_comapRestrict C j hdom sB x fun B'' sB'' _ hlt ↦ ?_
  exact key C j hdom B'' sB''
    (lt_trans hlt (schemeDeltaDimension_lt_top_integralComponentAt C sB _))

end Stacks.Chow

end
