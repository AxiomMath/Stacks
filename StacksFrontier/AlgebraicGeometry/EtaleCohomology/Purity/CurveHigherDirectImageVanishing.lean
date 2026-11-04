module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.AffineLineGeometricFibre
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.CitedInputs

/-!
# Higher direct images along an affine morphism out of a curve vanish above degree one

Let `k` be an algebraically closed field and `h : Y ⟶ X` an affine morphism from a scheme `Y`
locally of finite type over `k` and of dimension at most one. For every torsion abelian sheaf `G`
on `Y_étale`, `R^r h_* G = 0` for `r ≥ 2`. The higher direct image is the sheafification of
`V ↦ H^r(V ×_X Y, G)`, and over an affine `V` étale over `X` the base change `V ×_X Y` is an
affine curve over `k`, whose étale cohomology with torsion coefficients vanishes above degree one
(Stacks 03SC, part (2), `Stacks.EtaleCohomology.SmoothBaseChange.affineCurveCohomologyVanishing`).

This is the vanishing in degrees `≥ 2` of the local computation behind cohomological purity:
for the inclusion `j : 𝐆_m ⟶ 𝐀¹` of the complement of the origin, `R^q j_* Λ = 0` for `q ≥ 2`.

## Main results

* `Stacks.EtaleCohomology.isZero_rightDerived_pushforward_of_isAffineHom_of_dim_le_one`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] AlgebraicGeometry.Etale.isStableUnderComposition
  Stacks.EtaleCohomology.etaleContainsIdentities
  Stacks.Cohomology.ColimitsOfCohomology.additive_sheafΓ

/-- **`R^r h_* G = 0` for `r ≥ 2`** for an affine morphism `h : Y ⟶ X` out of a scheme `Y` locally
of finite type and of dimension at most one over an algebraically closed field, and `G` a torsion
abelian sheaf on `Y_étale`. -/
theorem isZero_rightDerived_pushforward_of_isAffineHom_of_dim_le_one (k : Type u) [Field k]
    [IsAlgClosed k] {X Y : Scheme.{u}} (h : Y ⟶ X) [IsAffineHom h] (e : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType e] (hdim : topologicalKrullDim Y ≤ 1)
    (G : Sheaf Y.smallEtaleTopology Ab.{u + 1})
    (hG : Stacks.Torsion.torsionSheafProperty Y.smallEtaleTopology G) (r : ℕ) (hr : 2 ≤ r) :
    IsZero (((smallEtalePushforwardAb h).rightDerived r).obj G) := by
  refine SmoothBaseChange.isZero_rightDerived_pushforward_of_affineEtale h r G fun Z => ?_
  let W := (smallEtaleBaseChange h).obj ((AffineEtale.Spec X).obj Z)
  have : IsAffine ((AffineEtale.Spec X).obj Z).left :=
    (inferInstance : IsAffine (Spec Z.left.unop))
  have : IsAffine W.left := by
    show IsAffine (pullback ((AffineEtale.Spec X).obj Z).hom h)
    have : IsAffineHom (pullback.fst ((AffineEtale.Spec X).obj Z).hom h) :=
      MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ h).flip ‹IsAffineHom h›
    have : IsAffine ((𝟭 Scheme).obj ((AffineEtale.Spec X).obj Z).left) :=
      ‹IsAffine ((AffineEtale.Spec X).obj Z).left›
    exact isAffine_of_isAffineHom (pullback.fst _ h)
  have : HasExt.{u + 1} (Sheaf W.left.smallEtaleTopology Ab.{u + 1}) :=
    have := isGrothendieckAbelian_sheaf_smallEtale_objectUniverse W.left
    inferInstance
  refine SmoothBaseChange.isZero_rightDerived_sectionsOverObject_of_subsingleton W r G ?_
  have hW : topologicalKrullDim W.left ≤ 1 :=
    (SmoothBaseChange.topologicalKrullDim_le_of_etale (W.left ↘ Y)).trans hdim
  have : IsAffineHom ((W.left ↘ Y) ≫ e) := isAffineHom_of_isAffine _
  have : LocallyOfFiniteType ((W.left ↘ Y) ≫ e) :=
    MorphismProperty.comp_mem _ _ _ (by infer_instance) ‹_›
  have : IsSeparated ((W.left ↘ Y) ≫ e) := IsSeparated.of_isAffineHom _
  have : QuasiCompact ((W.left ↘ Y) ≫ e) := AlgebraicGeometry.instQuasiCompactOfIsAffineHom _
  exact SmoothBaseChange.affineCurveCohomologyVanishing k ((W.left ↘ Y) ≫ e) hW inferInstance _
    (Stacks.Torsion.torsionSheafProperty_sheafPushforwardContinuous _ G hG) r (by omega)

end Stacks.EtaleCohomology

end
