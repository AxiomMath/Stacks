module

public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningAffineOverAffineBase.FiniteOrderStep
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceRange
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersionFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.FiniteTypeIdealSheaf

/-!
# The closed subspace of a scheme cut out by a sheaf of ideals

Let `T` be an object of the big fppf site over `S` and let `K` be a quasi-coherent sheaf of
ideals on the underlying scheme of `T`. The closed subscheme `V(K)` is an object of the site, and
the range of its inclusion is a closed subspace `Z_K` of the algebraic space represented by `T`.
This file records the three facts about `Z_K` that the comparison of a blowup of the scheme with
the blowup of the algebraic space uses: on the identity chart `Z_K` is cut out by `K`, so its
inclusion is of finite presentation when `V(K) ⟶ T` is, and its points are those over the
support of `K`.

## Main definitions

* `AlgebraicGeometry.Space.closedSubspaceOfIdeal`: the closed subspace `Z_K`.

## Main results

* `AlgebraicGeometry.Space.ker_rep_snd_closedSubspaceOfIdeal`: on the identity chart `Z_K` is
  cut out by `K`.
* `AlgebraicGeometry.Space.isFinitePresentation_closedSubspaceOfIdeal`: finite presentation.
* `AlgebraicGeometry.Space.subspacePointSet_closedSubspaceOfIdeal`: the points of `Z_K` are the
  points of the space over the support of `K`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The closed subspace of the algebraic space represented by `T` cut out by a quasi-coherent
sheaf of ideals `K` on its underlying scheme: the range of the inclusion `V(K) ⟶ T`. -/
def closedSubspaceOfIdeal (T : BigFppfOver B S hS)
    (K : ((BigFppfOver.toScheme B S hS).obj T).IdealSheafData) :
    ClosedSubspaces B S hS (schemeSpace T).1 :=
  ⟨Subfunctor.range (yoneda.map (closedSubschemeOverι B S hS T K)),
    isClosedSubspace_range_yoneda_map B S hS _
      (inferInstanceAs (AlgebraicGeometry.IsClosedImmersion K.subschemeι))⟩

/-- **On the identity chart the closed subspace `Z_K` is cut out by `K`.** -/
theorem ker_rep_snd_closedSubspaceOfIdeal (T : BigFppfOver B S hS)
    (K : ((BigFppfOver.toScheme B S hS).obj T).IdealSheafData) :
    ((BigFppfOver.toScheme B S hS).map
      ((closedSubspaceOfIdeal T K).2.2.rep.snd (𝟙 (yoneda.obj T)))).ker = K := by
  have : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map
      (closedSubschemeOverι B S hS T K)) :=
    inferInstanceAs (AlgebraicGeometry.IsClosedImmersion K.subschemeι)
  rw [ker_rep_snd_eq_ker_of_range_eq B S hS (schemeSpace T) (closedSubspaceOfIdeal T K) T
    (closedSubschemeOverObj B S hS T K) (𝟙 _) (closedSubschemeOverι B S hS T K)
    (Subfunctor.preimage_id _)]
  exact K.ker_subschemeι

/-- The identity of a represented presheaf satisfies the relatively representable form of any
base-change stable property of scheme morphisms that identities have. -/
theorem presheaf_inverseImage_id (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (T : BigFppfOver B S hS) (hP : P (𝟙 ((BigFppfOver.toScheme B S hS).obj T))) :
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf
      (𝟙 (yoneda.obj T)) := by
  rw [← yoneda.map_id]
  exact (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS P (𝟙 T)).2
    (by simpa using hP)

/-- **The inclusion of `Z_K` is of finite presentation when `V(K) ⟶ T` is.** -/
theorem isFinitePresentation_closedSubspaceOfIdeal (T : BigFppfOver B S hS)
    (K : ((BigFppfOver.toScheme B S hS).obj T).IdealSheafData)
    (hK : FinitePresentation K.subschemeι) :
    IsFinitePresentation B S hS (closedSubspaceOfIdeal T K).1.ι := by
  have hft := (finitePresentation_subschemeι_iff_isFiniteType K).1 hK
  refine (isFinitePresentation_iff_fg_ker_of_surjectiveEtaleChart B S hS
    (Z := ⟨(closedSubspaceOfIdeal T K).1.toFunctor, (closedSubspaceOfIdeal T K).2.1⟩)
    (X := schemeSpace T) (ObjectProperty.homMk (closedSubspaceOfIdeal T K).1.ι)
    (closedSubspaceOfIdeal T K).2.2 (b := 𝟙 _)
    (presheaf_inverseImage_id _ T inferInstance)
    (presheaf_inverseImage_id _ T inferInstance)).2 fun A => ?_
  rw [ker_rep_snd_closedSubspaceOfIdeal]
  exact hft A

end AlgebraicGeometry.Space

end
