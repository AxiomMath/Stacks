module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RepresentedAffineSystemUnitColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RepresentedAffinePerfectEnvelope

/-!
# Morphisms between perfect objects along a directed system of affine representables

Let `V₀` be an affine object of the big fppf site over `S`, and let `j ↦ V_j` be a directed system
of affine objects over `V₀` with a cone `V ⟶ V_j` over `V₀` whose rings of global functions are
the filtered colimit of those of the `V_j`.  For perfect objects `E` and `K` of `D(𝒪_{h_{V₀}})`
this file proves

`Hom_{D(𝒪_{h_V})}(Lk^*E, Lk^*K) = colim_j Hom_{D(𝒪_{h_{V_j}})}(Lk_j^*E, Lk_j^*K)`,

the derived pullbacks being taken with their canonical pseudofunctoriality.  This is the affine
case of Stacks 09RI for a perfect second argument.  It is deduced from the case of the structure
sheaf in two degrees,
`AlgebraicGeometry.Space.RepresentedAffineSystem.isColim_unitObj`: the statement with both
arguments shifted cuts out a thick subcategory in each argument
(`CategoryTheory.PullbackData.LimitSystem.isShiftedColim_of_triangEnvelope`), and the perfect
objects lie in the triangulated envelope of the structure sheaf
(`AlgebraicGeometry.Space.triangEnvelope_representedAffineUnitObj_of_isPerfect`).

## Main results

* `AlgebraicGeometry.Space.RepresentedAffineSystem.isColim_of_isPerfect`.

## References

* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian


variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The shift of the structure sheaf in degree `0`** by `n` is the structure sheaf in degree
`-n`. -/
def representedAffineUnitObjShiftIso (V : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] (n : ℤ) :
    (representedAffineUnitObj B S hS V 0)⟦n⟧ ≅ representedAffineUnitObj B S hS V (-n) :=
  letI := HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
  ((representedAffineDerivedAssociated B S hS V).commShiftIso n).symm.app _ ≪≫
    (representedAffineDerivedAssociated B S hS V).mapIso
      (((DerivedCategory.singleFunctors
        (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))).shiftIso n (-n) 0
          (by omega)).app _)

namespace RepresentedAffineSystem

variable {V₀ : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V₀)]
  {J : Type w} [Preorder J] [IsDirected J (· ≤ ·)] [Nonempty J]
  (Sys : RepresentedAffineSystem V₀ J)

/-- The colimit statement for the structure sheaf in degree `0` with both arguments shifted. -/
theorem isShiftedColim_unitObj (hring : Sys.IsRingColimit) :
    Sys.toLimitSystem.IsShiftedColim (DerivedPullbackComposition.canonical B S hS).toPullbackData
      (representedAffineUnitObj B S hS V₀ 0) (representedAffineUnitObj B S hS V₀ 0) :=
  fun n m =>
    ((Sys.isColim_unitObj hring (-n) (-m)).of_iso_fst
      (DerivedPullbackComposition.canonical B S hS).isCoherent_toPullbackData
      (representedAffineUnitObjShiftIso V₀ n).symm).of_iso_snd
      (DerivedPullbackComposition.canonical B S hS).isCoherent_toPullbackData _
      (representedAffineUnitObjShiftIso V₀ m).symm

/-- **The affine case of Stacks 09RI for perfect objects.**  Along a directed system of affine
representables over `V₀` with a cone whose rings of global functions form a filtered colimit,
`Hom(Lk^*E, Lk^*K)` is the filtered colimit of the `Hom(Lk_j^*E, Lk_j^*K)` for perfect objects
`E` and `K` of `D(𝒪_{h_{V₀}})`. -/
theorem isColim_of_isPerfect (hring : Sys.IsRingColimit)
    (E K : @DerivedCategory (Modules.{u, u} B S hS (yoneda.obj V₀)
      (isAlgebraicSpace_yoneda B S hS V₀)) _ _ (HasDerivedCategory.standard _))
    (hE : letI := HasDerivedCategory.standard (Modules.{u, u} B S hS (yoneda.obj V₀)
      (isAlgebraicSpace_yoneda B S hS V₀))
      (smallEtaleRingedSite B S hS (yoneda.obj V₀)
      (isAlgebraicSpace_yoneda B S hS V₀)).IsPerfect E)
    (hK : letI := HasDerivedCategory.standard (Modules.{u, u} B S hS (yoneda.obj V₀)
      (isAlgebraicSpace_yoneda B S hS V₀))
      (smallEtaleRingedSite B S hS (yoneda.obj V₀)
      (isAlgebraicSpace_yoneda B S hS V₀)).IsPerfect K) :
    Sys.toLimitSystem.IsColim (DerivedPullbackComposition.canonical B S hS).toPullbackData E K := by
  have hP := (DerivedPullbackComposition.canonical B S hS).isCoherent_toPullbackData
  have h := PullbackData.LimitSystem.isShiftedColim_of_triangEnvelope hP
    (Sys.isShiftedColim_unitObj hring)
    (triangEnvelope_representedAffineUnitObj_of_isPerfect B S hS V₀ E hE)
    (triangEnvelope_representedAffineUnitObj_of_isPerfect B S hS V₀ K hK) 0 0
  exact (h.of_iso_fst hP ((shiftFunctorZero _ ℤ).app _)).of_iso_snd hP _
    ((shiftFunctorZero _ ℤ).app _)

end RepresentedAffineSystem

end AlgebraicGeometry.Space

end
