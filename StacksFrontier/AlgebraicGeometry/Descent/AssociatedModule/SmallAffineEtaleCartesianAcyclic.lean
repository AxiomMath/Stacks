module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCartesian
public import StacksFrontier.AlgebraicGeometry.Topologies.AffineSiteLiftedCartesian
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineSiteFlatCovers

/-!
# Cartesian modules on the small affine étale site are acyclic, at every section universe

Let `S` be a scheme contained in a big étale site `B`, and let `S_{affine, étale}` be the small
affine étale site of Stacks 021B, with the structure sheaf of global functions.  This file
proves that a sheaf of modules on `S_{affine, étale}` whose underlying presheaf is *cartesian*
— every restriction map is a base change — has vanishing higher cohomology over every object,
with the module sections in `Type (u + 1)`.  This is Descent, Proposition 03DW (with Cohomology
of Schemes, Lemma 01XB) read for the étale topology at the section universe of the higher direct
images of Stacks 0765: at section universe `u` it is
`AlgebraicGeometry.SmallEtale.isZero_rightDerived_evaluation_of_isQuasicoherentOnSite`, whose
route goes through Mathlib's quasi-coherent modules on a scheme.

## The route

Nothing here is new: the general theorem
`Stacks.ModulesOnACategory.ChaoticComparison.isZero_rightDerived_evaluation_of_isCartesianPresheaf`
reduces the claim to two statements about the base changes `N ⊗_{O(x)} O_x` on the slices
`S_{affine, étale}/x` — that they are sheaves, and that they are acyclic — and those are
`Stacks.AffineSiteBaseChange.isSheaf_baseChangePresheaf` and
`Stacks.AffineSiteBaseChange.isZero_rightDerived_evaluation_baseChange`, for any category of
affine schemes whose topology is *flatly cofinal*.  All three are stated with the universe of the
module sections free.  What is proved here is the flat cofinality of the small affine étale
topology, `AlgebraicGeometry.SmallAffineEtale.isFlatCofinal`.

## Main results

* `AlgebraicGeometry.SmallAffineEtale.isFlatCofinal`: every covering sieve of
  `S_{affine, étale}` contains a finite covering family which is a flat covering of the
  underlying affine schemes.
* `AlgebraicGeometry.SmallAffineEtale.isZero_rightDerived_evaluation_of_isCartesian`:
  **a cartesian sheaf of modules on `S_{affine, étale}`, with sections in `Type (u + 1)`, has
  vanishing higher cohomology over every object.**

## References

* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
-/

@[expose] public section

-- The ambient-universe instances on sheaves of modules state their module universe as a `max`
-- pattern which the module universe below does not match syntactically; the same instances are
-- supplied at explicit universes.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AffineSiteBaseChange Stacks.TerminalBaseChange Stacks.Sites.OverModules
  Stacks.ModulesOnACategory.ChaoticComparison

universe u

namespace AlgebraicGeometry.SmallAffineEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The small affine étale topology is flatly cofinal**: every covering sieve contains a finite
covering family which is a flat covering of the underlying affine schemes. -/
theorem isFlatCofinal : IsFlatCofinal (toScheme B S hS) (topology B S hS) := by
  intro x T hT
  obtain ⟨E, hfin, hE, hEJ, hle⟩ := Stacks.Sites.exists_finite_flat_covering_refinement
    (toScheme B S hS) (precoverage B S hS)
    (SmallEtale.smallAffineEtale_covering_finite_flat B S hS) T hT
  let e : Fin (Nat.card E.I₀) ≃ E.I₀ := (Finite.equivFin E.I₀).symm
  have hs : (E.reindex e).sieve₀ = E.sieve₀ :=
    congrArg Sieve.generate (E.presieve₀_reindex e)
  refine ⟨E.reindex e, inferInstanceAs (Finite (Fin _)), ?_, hs ▸ hle, hs ▸ hEJ⟩
  have hpr : ((E.reindex e).map (toScheme B S hS)).presieve₀ =
      (E.map (toScheme B S hS)).presieve₀ := by
    rw [PreZeroHypercover.presieve₀_map, PreZeroHypercover.presieve₀_map,
      E.presieve₀_reindex e]
  exact hpr ▸ hE

attribute [local instance] Stacks.SheafOfModulesEvaluation.evaluation_additive

/-- **A cartesian sheaf of modules on the small affine étale site has no higher cohomology**,
with its sections in `Type (u + 1)`: for every object `U` and every `p > 0`, the `p`-th
module-valued cohomology over `U` vanishes. -/
theorem isZero_rightDerived_evaluation_of_isCartesian
    (F : SheafOfModules.{u + 1} (ringsSheaf (isFlatCofinal B S hS)))
    (hF : IsCartesianPresheaf F.val) (U : SmallAffineEtale B S hS) (p : ℕ) (hp : 0 < p) :
    letI := GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1} (topology B S hS)
    letI := AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u + 1,
      u} (topology B S hS)
    letI := Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives.{u + 1, u, u, 0}
      (ringsSheaf (isFlatCofinal B S hS))
    letI := Stacks.SheafOfModulesEvaluation.evaluation_additive.{u + 1, u, u + 1, u}
      (ringsSheaf (isFlatCofinal B S hS)) (op U)
    IsZero (((SheafOfModules.evaluation.{u + 1} (ringsSheaf (isFlatCofinal B S hS))
      (op U)).rightDerived p).obj F) := by
  let hJ := isFlatCofinal B S hS
  have (y : SmallAffineEtale B S hS) :=
    Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives.{u + 1, u, u, 0}
      (overRingSheaf (ringsSheaf hJ) y)
  have := Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives.{u + 1, u, u, 0}
    (ringsSheaf hJ)
  have := GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1} (topology B S hS)
  have := AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u + 1,
    u} (topology B S hS)
  have : ∀ X : SmallAffineEtale B S hS,
      HasSheafify ((topology B S hS).over X) AddCommGrpCat.{u + 1} := fun X =>
    GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1} _
  have : ∀ X : SmallAffineEtale B S hS,
      ((topology B S hS).over X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} := fun X =>
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u + 1, u} _
  have hO : ∀ (V : (SmallAffineEtale B S hS)ᵒᵖ) (x y : (ringsSheaf hJ).obj.obj V),
      x * y = y * x := fun V x y => by
    let _ : CommRing ((ringsSheaf hJ).obj.obj V) :=
      inferInstanceAs (CommRing ((rings (toScheme B S hS)).obj V))
    exact mul_comm x y
  open Stacks.ModulesOnACategory.ChaoticComparison in
  exact isZero_rightDerived_evaluation_of_isCartesianPresheaf.{0}
    (ringsSheaf hJ) hO
    (fun x N => isSheaf_baseChangePresheaf hJ x N)
    (fun x N V q hq => isZero_rightDerived_evaluation_baseChange.{0} hJ x N
      (isSheaf_baseChangePresheaf hJ x N) V q hq) F hF U p hp

end AlgebraicGeometry.SmallAffineEtale

end
