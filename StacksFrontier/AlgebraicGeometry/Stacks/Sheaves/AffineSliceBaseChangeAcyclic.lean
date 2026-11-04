module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineSiteCartesianModules
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.QuasiCoherentModulesAndAffines
public import StacksFrontier.AlgebraicGeometry.Topologies.AffineSiteBaseChangeAcyclic

/-!
# Base changes on the localized associated affine sites of a category fibred in groupoids

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and `𝒳_{affine, τ}` its associated
affine site for a topology `τ` on the affine schemes over `S` (Stacks 0H0A).  For the étale and
fppf topologies, and more generally for any flatly cofinal `τ`, the structure presheaf `O` is a
sheaf of rings on `𝒳_{affine, τ}`, and for every object `x` and every `O(x)`-module `N` the base
change `N ⊗_{O(x)} O_x` is a sheaf on the localized site `𝒳_{affine, τ}/x` with vanishing higher
cohomology over every object.  These are the inputs on single modules from which hypothesis (2)
of Stacks 0GZS follows for the comparison morphisms of Stacks 0H0J and 0H0X.

## Main results

* `AlgebraicGeometry.Stack.AffineCategory.isFlatCofinal_siteKind`: each of the five associated
  affine sites is flatly cofinal for the underlying scheme functor.
* `AlgebraicGeometry.Stack.AffineCategory.isSheaf_baseChange_affineSlice` and
  `AlgebraicGeometry.Stack.AffineCategory.isZero_rightDerived_evaluation_baseChange_affineSlice`:
  the base changes `N ⊗_{O(x)} O_x`, for the structure sheaf `O` of
  `AlgebraicGeometry.Stack.AffineCategory.siteKindRingedSite`, are sheaves with vanishing higher
  cohomology over every object of the localized site.

## References

* [Stacks Project, Tag 0H0A](https://stacks.math.columbia.edu/tag/0H0A)
* [Stacks Project, Tag 0H0J](https://stacks.math.columbia.edu/tag/0H0J)
* [Stacks Project, Tag 0H0U](https://stacks.math.columbia.edu/tag/0H0U)
* [Stacks Project, Tag 0H0X](https://stacks.math.columbia.edu/tag/0H0X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AffineSiteBaseChange Stacks.Sites.OverModules Stacks.TerminalBaseChange
open Stacks.ModulesOnACategory.ChaoticComparison (overRingSheaf)

namespace AlgebraicGeometry.Stack.AffineCategory

universe u v w t

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] {p : 𝒳 ⥤ BigFppfOver B S hS}

/-- **Each of the five associated affine sites is flatly cofinal**: every covering sieve of
`𝒳_{affine, τ}` contains a finite covering family which is a flat covering of the underlying
affine schemes (`exists_finite_flat_covering`). -/
theorem isFlatCofinal_siteKind (hp : p.IsFiberedInGroupoids) (τ : SiteKind) :
    IsFlatCofinal (toScheme B S hS p)
      (associatedAffineTopology B S hS p (BigAffineFppf.siteKindTopology B S hS τ)) := by
  intro x T hT
  obtain ⟨E, hfin, hE, hEJ, hle⟩ := exists_finite_flat_covering B S hS p hp τ T hT
  let e : Fin (Nat.card E.I₀) ≃ E.I₀ := (Finite.equivFin E.I₀).symm
  have hs : (E.reindex e).sieve₀ = E.sieve₀ :=
    congrArg Sieve.generate (E.presieve₀_reindex e)
  refine ⟨E.reindex e, inferInstanceAs (Finite (Fin _)), ?_, hs ▸ hle, hs ▸ hEJ⟩
  have hpr : ((E.reindex e).map (toScheme B S hS p)).presieve₀ =
      (E.map (toScheme B S hS p)).presieve₀ := by
    rw [PreZeroHypercover.presieve₀_map, PreZeroHypercover.presieve₀_map,
      E.presieve₀_reindex e]
  exact hpr ▸ hE

variable (hp : p.IsFiberedInGroupoids) (τ : SiteKind)

/-- The section rings of the structure sheaf of `siteKindRingedSite`, restricted to a slice, are
commutative. -/
instance commSections_overRingPresheaf_siteKindRingedSite (x : AffineCategory B S hS p) :
    CommSections (overRingPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf
        (siteKindRingedSite B S hS p hp τ).O).obj x) :=
  commSections_overRingPresheaf_rings (toScheme B S hS p) x

/-- The sheaf of rings `O` of `siteKindRingedSite` is the sheaf of global functions of the
underlying scheme functor. -/
theorem siteKindRingedSite_ringSheaf_eq :
    (Stacks.SheafOfModules.Tensor.ringSheaf (siteKindRingedSite B S hS p hp τ).O) =
      haveI := hasPullbacks B S hS p hp
      haveI := preservesPullbacks_toScheme B S hS p hp
      ringsSheaf (isFlatCofinal_siteKind B S hS hp τ) :=
  rfl

/-- **The base change `N ⊗_{O(x)} O_x` is a sheaf on the localized associated affine site
`𝒳_{affine, τ}/x`**, for every `O(x)`-module `N`: it is cartesian, and a cartesian presheaf of
modules is a sheaf (`isSheaf_over_of_cartesian`). -/
theorem isSheaf_baseChange_affineSlice (x : AffineCategory B S hS p)
    (N : ModuleCat.{max (max v w) w u t}
      ((overRingPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf
          (siteKindRingedSite B S hS p hp τ).O).obj x).obj
        (op (Over.mk (𝟙 x))))) :
    Presheaf.IsSheaf
      ((associatedAffineTopology B S hS p (BigAffineFppf.siteKindTopology B S hS τ)).over x)
      ((baseChangePresheaf.{max (max v w) t}
        (overRingPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf
            (siteKindRingedSite B S hS p hp τ).O).obj x)
          (Over.mkIdTerminal (X := x))).obj N).presheaf :=
  isSheaf_over_of_cartesian.{u, v, w, max (max v w) t} B S hS p ((toScheme B S hS p).op ⋙ Scheme.Γ)
    rfl hp τ x _ (fun f => isIso_restrictionBaseChange_baseChangePresheaf.{max (max v w) t} _ _ N f)

-- The ambient-universe instances on sheaves of modules state their universe as a `max` pattern
-- that the module universe `max t u v w` below does not match syntactically, which leaves the
-- universe of the statement unsolved; the same instances are supplied below at this universe.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives
  Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_isGrothendieckAbelian
  Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory

attribute [local instance] Stacks.SheafOfModulesEvaluation.evaluation_additive

/-- **The higher cohomology of the base change `N ⊗_{O(x)} O_x` vanishes over every object of
the localized associated affine site**, as module-valued right derived functors of sections
over that object. -/
theorem isZero_rightDerived_evaluation_baseChange_affineSlice (x : AffineCategory B S hS p)
    (N : ModuleCat.{max t u v w}
      ((overRingPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf
          (siteKindRingedSite B S hS p hp τ).O).obj x).obj
        (op (Over.mk (𝟙 x)))))
    (V : Over x) (n : ℕ) (hn : 0 < n) :
    haveI := Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{max v w, w, max u t}
      (J := (siteKindRingedSite B S hS p hp τ).J.over x)
    haveI := Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{max v w, w,
      max u t} (J := (siteKindRingedSite B S hS p hp τ).J.over x)
    haveI := Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives.{max v w, w, u, t}
      (overRingSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
          (siteKindRingedSite B S hS p hp τ).O) x)
    IsZero (((SheafOfModules.evaluation.{max t u v w}
      (overRingSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
          (siteKindRingedSite B S hS p hp τ).O) x) (op V)).rightDerived n).obj
        (⟨(baseChangePresheaf.{max (max v w) t}
          (overRingPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf
              (siteKindRingedSite B S hS p hp τ).O).obj x)
            (Over.mkIdTerminal (X := x))).obj N,
          isSheaf_baseChange_affineSlice.{u, v, w, t} B S hS hp τ x N⟩ :
          SheafOfModules.{max t u v w}
            (overRingSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
                (siteKindRingedSite B S hS p hp τ).O) x))) := by
  have := hasPullbacks B S hS p hp
  have := preservesPullbacks_toScheme B S hS p hp
  have := Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{max v w, w, max u t}
    (J := (siteKindRingedSite B S hS p hp τ).J.over x)
  have := Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{max v w, w,
    max u t} (J := (siteKindRingedSite B S hS p hp τ).J.over x)
  have : EnoughInjectives (SheafOfModules.{max t u v w}
      (overRingSheaf (ringsSheaf (isFlatCofinal_siteKind B S hS hp τ)) x)) :=
    Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives.{max v w, w, u, t} _
  exact isZero_rightDerived_evaluation_baseChange.{t, u, v, w}
    (isFlatCofinal_siteKind B S hS hp τ) x N _ V n hn

end AlgebraicGeometry.Stack.AffineCategory
