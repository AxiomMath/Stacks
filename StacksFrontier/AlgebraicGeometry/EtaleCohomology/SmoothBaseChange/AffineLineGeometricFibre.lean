module

public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleLocalDimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.CitedStatements
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.HigherDirectImageAffineVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.TorsionSheavesAndRestriction
public import StacksFrontier.Topology.Dimension.LocalKrullDim
public import StacksFrontier.Topology.Dimension.Krull
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial

/-!
# The affine line over a geometric generic point

Consider a diagram of two cartesian squares
```
𝔸¹_T  ←--  X'  ←-h-  Y
  |        |f'       |e
  T   ←s-  S'  ←-g-  Spec K
```
with `S'` affine and `K` algebraically closed. Then `Y`, the affine line over `K`, has dimension
at most one, and, given the vanishing of the étale cohomology of affine curves above degree one
(Stacks 03SC, part (2)), `R^r h_* G = 0` for every torsion abelian sheaf `G` on `Y_étale` and
every `r ≥ 2`.

## Main results

* `Stacks.EtaleCohomology.SmoothBaseChange.topologicalKrullDim_le_of_etale` — an étale morphism
  does not raise the dimension.
* `Stacks.EtaleCohomology.SmoothBaseChange.isZero_rightDerived_affineLine_of_two_le` — the
  vanishing in degrees at least two.

## References

* [Stacks Project, Tag 0EYU](https://stacks.math.columbia.edu/tag/0EYU)
* [Stacks Project, Tag 0F08](https://stacks.math.columbia.edu/tag/0F08)
* [Stacks Project, Tag 03SC](https://stacks.math.columbia.edu/tag/03SC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale

universe u

namespace Stacks.EtaleCohomology.SmoothBaseChange

attribute [local instance] AlgebraicGeometry.Etale.isStableUnderComposition
  Stacks.EtaleCohomology.etaleContainsIdentities
  Stacks.Cohomology.ColimitsOfCohomology.additive_sheafΓ

/-- **An étale morphism does not raise the dimension**: `dim U ≤ dim V` for an étale morphism
`f : U ⟶ V`. -/
theorem topologicalKrullDim_le_of_etale {U V : Scheme.{u}} (f : U ⟶ V) [Etale f] :
    topologicalKrullDim U ≤ topologicalKrullDim V := by
  rw [TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
  refine iSup_le fun x => ?_
  rw [← TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim,
    topologicalKrullDimAt_eq_of_etale f x]
  exact topologicalKrullDimAt_le_topologicalKrullDim _

/-- The affine line over a field has dimension at most one. -/
theorem topologicalKrullDim_affineLine_spec (K : Type u) [Field K] :
    topologicalKrullDim (𝔸(ULift.{u} (Fin 1); Spec (.of K))) ≤ 1 := by
  rw [IsHomeomorph.topologicalKrullDim_eq _
    (Scheme.homeoOfIso (AffineSpace.SpecIso (ULift.{u} (Fin 1)) (.of K))).isHomeomorph]
  show topologicalKrullDim (PrimeSpectrum (MvPolynomial (ULift.{u} (Fin 1)) K)) ≤ 1
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

section NormalizedDiagram

variable {T S' X' Y : Scheme.{u}} {s : S' ⟶ T} {p : X' ⟶ 𝔸(ULift.{u} (Fin 1); T)}
  {f' : X' ⟶ S'} (hp : IsPullback p f' (𝔸(ULift.{u} (Fin 1); T) ↘ T) s)
  {K : Type u} [Field K] {g : Spec (.of K) ⟶ S'} {h : Y ⟶ X'} {e : Y ⟶ Spec (.of K)}
  (sq : IsPullback h e f' g)

include hp sq in
/-- `Y`, the affine line over `K`, has dimension at most one. -/
theorem topologicalKrullDim_le_one_of_affineLine : topologicalKrullDim Y ≤ 1 := by
  have h₁ : IsPullback (h ≫ p) e (𝔸(ULift.{u} (Fin 1); T) ↘ T) (g ≫ s) := sq.paste_horiz hp
  have h₂ := AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) (g ≫ s)
  rw [IsHomeomorph.topologicalKrullDim_eq _
    (Scheme.homeoOfIso (h₁.isoIsPullback _ _ h₂)).isHomeomorph]
  exact topologicalKrullDim_affineLine_spec K

include hp sq in
/-- The structure morphism of `Y` over `Spec K` is locally of finite type. -/
theorem locallyOfFiniteType_affineLine_e : LocallyOfFiniteType e := by
  have : LocallyOfFiniteType f' := MorphismProperty.of_isPullback hp inferInstance
  exact MorphismProperty.of_isPullback sq inferInstance

variable [IsAffine S']

include sq in
/-- `h : Y ⟶ X'` is an affine morphism. -/
theorem isAffineHom_affineLine_h : IsAffineHom h :=
  MorphismProperty.of_isPullback sq.flip inferInstance

include hp sq in
/-- **The vanishing in degrees at least two.** Given the vanishing of the étale cohomology of
affine curves above degree one (`AffineCurveCohomologyVanishing`, part (2) of Stacks 03SC), for
`K` algebraically closed and every abelian sheaf `G` on `Y_étale` which is torsion,
`R^r h_* G = 0` for `r ≥ 2`. -/
theorem isZero_rightDerived_affineLine_of_two_le (h03SC2 : AffineCurveCohomologyVanishing.{u})
    [IsAlgClosed K] (G : Sheaf Y.smallEtaleTopology Ab.{u + 1})
    (hG : Stacks.Torsion.torsionSheafProperty Y.smallEtaleTopology G) (r : ℕ) (hr : 2 ≤ r) :
    IsZero (((smallEtalePushforwardAb h).rightDerived r).obj G) := by
  have : IsAffineHom h := isAffineHom_affineLine_h sq
  have : LocallyOfFiniteType e := locallyOfFiniteType_affineLine_e hp sq
  refine isZero_rightDerived_pushforward_of_affineEtale h r G fun Z => ?_
  let W := (smallEtaleBaseChange h).obj ((AffineEtale.Spec X').obj Z)
  have : IsAffine ((AffineEtale.Spec X').obj Z).left :=
    (inferInstance : IsAffine (Spec Z.left.unop))
  have : IsAffine W.left := by
    show IsAffine (pullback ((AffineEtale.Spec X').obj Z).hom h)
    have : IsAffineHom (pullback.fst ((AffineEtale.Spec X').obj Z).hom h) :=
      MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ h).flip ‹IsAffineHom h›
    have : IsAffine ((𝟭 Scheme).obj ((AffineEtale.Spec X').obj Z).left) :=
      ‹IsAffine ((AffineEtale.Spec X').obj Z).left›
    exact isAffine_of_isAffineHom (pullback.fst _ h)
  have : HasExt.{u + 1} (Sheaf W.left.smallEtaleTopology Ab.{u + 1}) :=
    have := isGrothendieckAbelian_sheaf_smallEtale_objectUniverse W.left
    inferInstance
  refine isZero_rightDerived_sectionsOverObject_of_subsingleton W r G ?_
  have hdim : topologicalKrullDim W.left ≤ 1 :=
    (topologicalKrullDim_le_of_etale (W.left ↘ Y)).trans
      (topologicalKrullDim_le_one_of_affineLine hp sq)
  exact h03SC2 K ((W.left ↘ Y) ≫ e) hdim inferInstance _
    (Stacks.Torsion.torsionSheafProperty_sheafPushforwardContinuous _ G hG) r (by omega)

end NormalizedDiagram

end Stacks.EtaleCohomology.SmoothBaseChange

end
