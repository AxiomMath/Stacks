module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHomAffineLeafBaseChangeModel
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHomAffineLeafRepresentedCrossing

/-!
# The leaf of Stacks 09RI over an affine point is computed on the affine models

In Situation 09RH let `g : V ⟶ X₀` be a morphism onto the chosen stage from an algebraic space
`V ≅ h_T` with `T` affine.  The colimit statement of Stacks 09RI on the base-changed system
`AlgebraicGeometry.Space.DescentSituation.baseChangeSystem` of `g`, at objects `X` and `Y` of
`D(𝒪_V)`, follows from the same statement on the directed system of affine representables
`AlgebraicGeometry.Space.DescentSituation.affineModelSystem` at the pullbacks of `X` and `Y` to
`h_T`.  This is the transport along the morphism of systems
`AlgebraicGeometry.Space.DescentSituation.affineModelBaseChangeHom`, which is an isomorphism at
every stage and at the limit, so that derived pullback along it is fully faithful there; it is
followed by the change of base along `V ≅ h_T`.

## Main results

* `AlgebraicGeometry.Space.DescentSituation.isColim_baseChangeSystem_of_affineModelSystem`: the
  transport for `AlgebraicGeometry.Space.canonicalPullbackData`.
* `AlgebraicGeometry.Space.DescentSituation.shiftedIsColim_baseChangeSystem_of_affineModelSystem`:
  the same at every shift of the first argument, for
  `AlgebraicGeometry.Space.smallEtaleDerivedPullbackData`, the datum the leaf of Stacks 09RI is
  stated at.

## References

* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

namespace DescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  {D : DescentSituation B S hS hZ I} {V : AlgebraicSpaces B S hS} (g : V ⟶ D.stage D.base)
  {T : BigFppfOver B S hS} (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
  (e : V.1 ≅ yoneda.obj T) (u : yoneda.obj T ⟶ (stagesSystem D).obj (op (baseStage D)))
  (hu : e.inv ≫ g.hom = u) (hconv : SiteContainsBaseChangeLimits B S hS D.system)

include hu in
/-- **The colimit statement of Stacks 09RI on the base-changed system along an affine point
follows from the one on its affine models**, at the pullbacks of the two objects to `h_T`. -/
theorem isColim_baseChangeSystem_of_affineModelSystem (X Y : derivedModules B S hS V)
    (h : (affineModelSystem hT u hconv).toLimitSystem.IsColim (canonicalPullbackData B S hS)
      ((smallEtaleDerivedModulePullback B S hS (baseChangeAffinePointIso e).inv).obj X)
      ((smallEtaleDerivedModulePullback B S hS (baseChangeAffinePointIso e).inv).obj Y)) :
    (baseChangeSystem g).IsColim (canonicalPullbackData B S hS) X Y := by
  have hP : (canonicalPullbackData B S hS).IsCoherent :=
    (DerivedPullbackComposition.canonical B S hS).isCoherent_toPullbackData
  set eS := baseChangeAffinePointIso (B := B) (S := S) (hS := hS) e
  set α := affineModelBaseChangeHom g hT e u hu hconv
  have hst : ∀ j, Function.Bijective (α.stageMap
      ((smallEtaleDerivedModulePullback B S hS eS.inv).obj X)
      ((smallEtaleDerivedModulePullback B S hS eS.inv).obj Y)
      (canonicalPullbackData B S hS) j) := fun j =>
    PullbackData.bijective_factorHom_of_fullyFaithful _ _
      (smallEtaleDerivedModulePullbackEquivalence B S hS
        (affineModelBaseChangeIso g hT e u hu j)).fullyFaithfulFunctor _ _
  have hlim : Function.Bijective (α.limitMap
      ((smallEtaleDerivedModulePullback B S hS eS.inv).obj X)
      ((smallEtaleDerivedModulePullback B S hS eS.inv).obj Y)
      (canonicalPullbackData B S hS)) :=
    PullbackData.bijective_factorHom_of_fullyFaithful _ _
      (smallEtaleDerivedModulePullbackEquivalence B S hS
        (affineModelBaseChangeLimitIso g hT e u hu hconv)).fullyFaithfulFunctor _ _
  exact (((PullbackData.LimitSystem.isColim_comp_iff (S := baseChangeSystem g) hP eS.hom _ _).1
    ((PullbackData.LimitSystem.Hom.isColim_iff α _ _ hP hst hlim).2 h)).of_iso_fst hP
      ((smallEtaleDerivedModulePullbackHomInvIso B S hS eS).app X)).of_iso_snd
    hP _ ((smallEtaleDerivedModulePullbackHomInvIso B S hS eS).app Y)

include hu in
/-- **The leaf statement of Stacks 09RI on the base-changed system along an affine point follows
from the colimit statement on its affine models**, at every shift of the first argument and for
the pullback datum `AlgebraicGeometry.Space.smallEtaleDerivedPullbackData` the leaf is stated
at. -/
theorem shiftedIsColim_baseChangeSystem_of_affineModelSystem (X Y : derivedModules B S hS V)
    (h : ∀ n : ℤ, (affineModelSystem hT u hconv).toLimitSystem.IsColim
      (canonicalPullbackData B S hS)
      ((smallEtaleDerivedModulePullback B S hS (baseChangeAffinePointIso e).inv).obj (X⟦n⟧))
      ((smallEtaleDerivedModulePullback B S hS (baseChangeAffinePointIso e).inv).obj Y)) :
    PullbackData.LimitSystem.ShiftedIsColim (baseChangeSystem g)
      (smallEtaleDerivedPullbackData B S hS) X Y :=
  (shiftedIsColim_canonicalPullbackData_iff (baseChangeSystem g) X Y).1 fun n =>
    isColim_baseChangeSystem_of_affineModelSystem g hT e u hu hconv _ _ (h n)

end DescentSituation

end AlgebraicGeometry.Space

end
