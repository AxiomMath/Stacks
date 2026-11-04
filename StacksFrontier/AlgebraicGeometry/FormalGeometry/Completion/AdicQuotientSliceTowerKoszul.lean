module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AdicQuotientSliceTowerDescent
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulAdicQuotientTowerOffset
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulAdicAffineSliceDerivedLimit
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.GlobalSectionsCompletionGenerated
public import StacksCore.Tactic.StacksAttribute

/-!
# Part (3) of Tag 0A0K at the source's hypotheses: `ℱ^∧ = lim ℱ/𝓘ⁿℱ`

Let `X` be a locally Noetherian scheme — **not** assumed quasi-compact — let `𝓘 ⊂ 𝒪_X` be an
arbitrary quasi-coherent sheaf of ideals and let `ℱ` be a coherent `𝒪_X`-module. This file proves
that the canonical comparison

`c : ℱ^∧ ⟶ (lim ℱ/𝓘ⁿℱ)[0]`

is an isomorphism, so that `ℱ^∧ = lim ℱ/𝓘ⁿℱ` with an *ordinary* inverse limit. That is part (3)
of [Stacks, Tag 0A0K], read through its canonical comparison map, at the source's own hypotheses.

`Completion/AdicQuotientSliceTowerDescent.lean` reduces it to a derived-limit presentation of
`(ℱ|_V)^∧` over the slice's own adic quotient tower `n ↦ (ℱ|_V)/(𝓘|_V)ⁿ(ℱ|_V)`, through the
slice's own canonical maps, for `V` ranging over the affine opens. This file supplies that
presentation, which is what the Koszul chain of `DerivedCompletionRinged/` produces once three
things are in place.

## Main results

* `Stacks.Algebraization.exists_isDerivedLimitWithProjections_completionToAdicQuotientSliceTower`
  — **the per-affine-slice presentation**, through the slice's own canonical maps: the hypothesis
  of `Stacks.Algebraization.isIso_comparison_of_affineOpens_sliceTower`, proved.
* `Stacks.Algebraization.isIso_comparisonDerivedCompletionLimitAdicQuotient` — **part (3) of
  [Stacks, Tag 0A0K]**, registered.

## The three things the Koszul chain needed

The chain ends at `AlgebraicGeometry.RingedSite`
`.isDerivedLimitWithProjections_koszulTopSingle_completion`, which presents the **Čech**
completion of `ℱ|_V` over the Koszul top-cohomology tower
`n ↦ (ℱ|_V)/(f_1^{n+1}, …, f_r^{n+1})(ℱ|_V)` through projections pinned against the Čech
completion map, with the pro-vanishing below the top degree as its only hypothesis and that
discharged on an affine slice by
`Stacks.KoszulProZero.exists_koszulDualSystemOn_over_homologyMap_eq_zero_of_section`, with no
compactness.

1. *The offset of the two site-level adic quotient towers.*
   `Stacks.Sites.adicQuotientTowerOnOffset` of
   `DerivedCompletionRinged/KoszulAdicQuotientTowerOffset.lean` is the interleaving
   `ℱ/ℐⁿ⁺¹ℱ ⟶ ℱ/ℐⁿℱ` relating `Stacks.Sites.adicQuotientTowerOn`, which the Koszul pigeonhole
   lands in, with `Stacks.Sites.idealSmulQuotientTower`, which part (3) is about. It carries the
   quotient projections to each other and has eventual inverses one level up.
2. *The Čech completion against the reflector, with its unit equation.* The presentation asked for
   here is at `AlgebraicGeometry.RingedSite.derivedCompletion`, the reflector of
   [Stacks, Tag 099F], and the chain ends at
   `AlgebraicGeometry.RingedSite.completionFunctor`, the Čech model of [Stacks, Tag 099B]. They
   are identified by
   `AlgebraicGeometry.RingedSite.exists_iso_derivedCompletion_completionFunctor_obj`, which now
   carries `derivedCompletionUnit ≫ θ.hom = completionUnit`. That equation is what moves the
   *pinning* from one model to the other; an isomorphism alone transports properties and
   identifies no map.
3. *The transport of the pinning.* `AlgebraicGeometry.RingedSite`
   `.completionUnit_app_comp_koszulTopSingleProjection_comp_map_eq` computes the Čech completion
   map followed by the transported Koszul projection: it is the quotient projection
   `ℱ|_V ⟶ (ℱ|_V)/(𝓘|_V)ⁿ(ℱ|_V)` in degree zero, with no sign surviving. The slice's own
   canonical maps have the same composite with the reflector's completion map
   (`Stacks.Algebraization.derivedCompletionUnit_comp_completionToAdicQuotientSliceTower`), and a
   map out of a derived completion into a derived-complete object is determined by that
   composite, so the two families of projections coincide.

## Why the restricted tower carries the uniqueness

The identification in (3) is made against the **restriction of the scheme's** adic quotient
tower rather than against the slice's own: the terms of the restricted tower are derived complete
because the scheme-level terms are
(`Stacks.Algebraization.isDerivedComplete_single_adicQuotientSystem_obj`) and restriction
preserves derived completeness, which is the first step of [Stacks, Tag 0A0F]. Derived
completeness is a nested statement about sections and is not known in this library to transport
along an arbitrary isomorphism, so the uniqueness is applied where it is available and the
identification of the two towers — an isomorphism in the derived category of the slice,
`Stacks.Algebraization.adicQuotientSliceDerivedTowerIso` — is cancelled afterwards.

## Where the generality comes from

Nothing below buys quasi-compactness of `X` or a global generating family for `𝓘`. On an affine
open `V` the restriction `𝓘|_V` *is* generated by finitely many sections of `Γ(X, V)`
(`Stacks.KoszulProZero.exists_eq_generatedIdealSheaf_overIdeal_affine`), which on the slice are
global; and the Artin–Rees level behind the pro-vanishing is computed once over the single model
`A = Γ(X, V)`, `M = Γ(ℱ, V)`, so no maximum over a cover is taken. Reading the source's equality
through the canonical comparison map is what lets the per-slice statements be glued at all:
invertibility of a *named* map is local on the site
(`Stacks.SheafOfModules.isIso_of_coversTop_mapDerivedCategory`), while the non-canonical
isomorphism a derived limit supplies is not.

`Stacks.Algebraization.nonempty_iso_completion_limit_adicQuotientSystem` of
`Completion/KoszulAdicCompletionLimit.lean` is the other registration of part (3): it is proved
by running the Koszul chain on `X` itself, which costs `[CompactSpace X]` and a global generating
family and yields a non-canonical isomorphism rather than the invertibility of the canonical map.

## References

* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
* [Stacks Project, Tag 099B](https://stacks.math.columbia.edu/tag/099B)
* [Stacks Project, Tag 099F](https://stacks.math.columbia.edu/tag/099F)
* [Stacks Project, Tag 0A0E](https://stacks.math.columbia.edu/tag/0A0E)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite
open Stacks.SheafOfModules (opensRingedSite)
open AlgebraicGeometry.RingedSite (restrictModulesToSlice overIdeal derivedCompletion
  derivedCompletionUnit generatedIdealSheaf globalSectionOfSection koszulTopDeg_eq)
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

attribute [local instance] monoSubmoduleι
attribute [local instance] modulesEnoughInjectives
attribute [local instance 100000] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance] Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp
attribute [local instance] Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData) (ℱ : X.Modules)
  [ℱ.IsCoherent]

attribute [local instance]
  isRightAdjoint_ι_isDerivedComplete_overIdeal_idealSheafSiteSubmodule

/-! ### The uniqueness carried by the restricted tower -/

omit [IsLocallyNoetherian X] [_root_.SheafOfModules.IsCoherent ℱ] in
/-- **The restriction of a term `(ℱ/𝓘ⁿℱ)[0]` of the adic quotient tower is derived complete along
`𝓘|_V`.** The term itself is derived complete along `𝓘` — a local section of `𝓘` acts on it
through its `n`-th power, which is zero
(`Stacks.Algebraization.isDerivedComplete_single_adicQuotientSystem_obj`) — and restriction to a
slice preserves derived completeness, which is the first step of [Stacks, Tag 0A0F].

This is the companion of `Stacks.Algebraization`
`.isDerivedComplete_restrict_single_limit_adicQuotientSystem` at a term of the tower rather than
at its limit, and it is what gives the slice's canonical maps onto the *restricted* tower their
uniqueness. -/
theorem isDerivedComplete_restrict_single_adicQuotientSystem_obj (V : X.Opens) (n : ℕ) :
    AlgebraicGeometry.RingedSite.IsDerivedComplete.{u, u, u, u}
      ((opensRingedSite X.sheaf).over V)
      (overIdeal (idealSheafSiteSubmodule I) V)
      ((SheafOfModules.overFunctor.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O))
        V).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O)))
          0).obj
          ((adicQuotientSystem I ℱ).obj ⟨n⟩ : SheafOfModules.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O))))) := by
  obtain ⟨_, _, _, h⟩ := AlgebraicGeometry.RingedSite.restrict_isDerivedComplete_overIdeal
    (opensRingedSite X.sheaf) (idealSheafSiteSubmodule I) V _
    (isDerivedComplete_single_adicQuotientSystem_obj I ℱ n)
  exact h

/-- **`Stacks.Algebraization.restrictCompletionToAdicQuotient` is the only map out of `(ℱ|_V)^∧`
restricting along the completion unit of the slice to the restriction of the quotient projection
`ℱ ⟶ ℱ/𝓘ⁿℱ`.** The restricted term is derived complete along `𝓘|_V`
(`Stacks.Algebraization.isDerivedComplete_restrict_single_adicQuotientSystem_obj`), so a map out
of `(ℱ|_V)^∧` into it is determined by its restriction along the unit.

This is the companion of `Stacks.Algebraization.eq_restrictComparisonLimitAdicQuotient` at a term
of the tower rather than at its limit. -/
theorem eq_restrictCompletionToAdicQuotient (V : X.Opens) (n : ℕ)
    {g : (derivedCompletion ((opensRingedSite X.sheaf).over V)
        (overIdeal (idealSheafSiteSubmodule I) V)).obj
        ((SheafOfModules.overFunctor.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O))
          V).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor (SheafOfModules.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O)))
            0).obj (ℱ : SheafOfModules.{u}
              ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O))))) ⟶
      (SheafOfModules.overFunctor.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O))
        V).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O)))
          0).obj
          ((adicQuotientSystem I ℱ).obj ⟨n⟩ : SheafOfModules.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O))))}
    (hg : (derivedCompletionUnit ((opensRingedSite X.sheaf).over V)
          (overIdeal (idealSheafSiteSubmodule I) V)).app _ ≫ g =
      (SheafOfModules.overFunctor.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O))
        V).mapDerivedCategory.map
        ((DerivedCategory.singleFunctor (SheafOfModules.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O)))
          0).map ((adicQuotientCone I ℱ).π.app ⟨n⟩))) :
    g = restrictCompletionToAdicQuotient I ℱ V n :=
  AlgebraicGeometry.RingedSite.hom_ext_derivedCompletionUnit _ _
    (isDerivedComplete_restrict_single_adicQuotientSystem_obj I ℱ V n)
    (hg.trans (derivedCompletionUnit_comp_restrictCompletionToAdicQuotient I ℱ V n).symm)

/-! ### The slice's own canonical maps, pinned -/

/-- **The slice's canonical map `(ℱ|_V)^∧ ⟶ ((ℱ|_V)/(𝓘|_V)ⁿ(ℱ|_V))[0]`, pinned.** Composing it
with the completion unit of the slice gives the comparison
`((ℱ|_V)[0]) ≅ (ℱ[0])|_V` of [Stacks, Tag 0942] followed by the quotient projection
`ℱ|_V ⟶ (ℱ|_V)/(𝓘|_V)ⁿ(ℱ|_V)` in degree zero.

Three identities compose: `Stacks.Algebraization`
`.derivedCompletionUnit_comp_restrictCompletionToAdicQuotient`, which is the same statement for
the restricted tower; the naturality of
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor`, which moves the restriction past the
single functor; and `Stacks.Algebraization.π_comp_adicQuotientSliceTowerIso_hom_app`, which says
that identifying the two towers respects the quotient projections. -/
theorem derivedCompletionUnit_comp_completionToAdicQuotientSliceTower (V : X.Opens) (n : ℕ) :
    (derivedCompletionUnit ((opensRingedSite X.sheaf).over V)
          (overIdeal (idealSheafSiteSubmodule I) V)).app
        ((SheafOfModules.overFunctor.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O))
          V).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor (SheafOfModules.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O)))
            0).obj (ℱ : SheafOfModules.{u}
              ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O))))) ≫
        completionToAdicQuotientSliceTower I ℱ V n =
      ((SheafOfModules.overFunctor.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O))
            V).mapDerivedCategorySingleFunctor 0).hom.app
          (ℱ : SheafOfModules.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O))) ≫
        (DerivedCategory.singleFunctor
          (AlgebraicGeometry.RingedSite.Modules.{u, u, u}
            ((opensRingedSite X.sheaf).over V)) 0).map
          (Stacks.Sites.idealSmulQuotientπ
            ((restrictModulesToSlice (opensRingedSite X.sheaf) V).obj ℱ)
            (Stacks.Sites.idealPow (O := ((opensRingedSite X.sheaf).over V).O)
              (overIdeal (idealSheafSiteSubmodule I) V) n)) := by
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker
    (derivedCompletionUnit_comp_restrictCompletionToAdicQuotient I ℱ V n) _) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker
    (((SheafOfModules.overFunctor.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O))
        V).mapDerivedCategorySingleFunctor 0).hom.naturality
      ((adicQuotientCone I ℱ).π.app ⟨n⟩)) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine whisker_eq _ ?_
  refine Eq.trans
    (((DerivedCategory.singleFunctor
      (AlgebraicGeometry.RingedSite.Modules.{u, u, u}
        ((opensRingedSite X.sheaf).over V)) 0).map_comp _ _).symm) ?_
  exact congrArg
    (DerivedCategory.singleFunctor
      (AlgebraicGeometry.RingedSite.Modules.{u, u, u}
        ((opensRingedSite X.sheaf).over V)) 0).map
    (π_comp_adicQuotientSliceTowerIso_hom_app I ℱ V n)

/-! ### The Koszul presentation on an affine slice -/

/-- **The Koszul chain's presentation of `(ℱ|_V)^∧` over the slice's own adic quotient tower,
with its projections pinned**, at a sheaf of ideals *equal* to one generated by finitely many
sections of `Γ(X, V)`.

The equality `J = (f_1, …, f_r)` is a hypothesis rather than a definition so that the statement
can be read at `J = 𝓘|_V`, which is what part (3) asks for: on an affine open the restriction of
an arbitrary quasi-coherent ideal sheaf *is* such a `J`
(`Stacks.KoszulProZero.exists_eq_generatedIdealSheaf_overIdeal_affine`), but it is not spelled
that way, and the generators depend on the open.

The projections are returned existentially and *pinned* by the equation on the completion unit,
which determines them; `Stacks.Algebraization`
`.exists_isDerivedLimitWithProjections_completionToAdicQuotientSliceTower` below is where they
are identified with the slice's own canonical maps. Four steps compose: the Koszul presentation
over the top-cohomology tower, the transport along
`AlgebraicGeometry.RingedSite.koszulTopHomologyToIdealSmulQuotientTower` by
`NoetherianAdicCompletion.IsDerivedLimitWithProjections.comp_of_hasEventualInverses`, the passage
from the Čech model of the completion to the reflector by
`NoetherianAdicCompletion.IsDerivedLimitWithProjections.of_iso` at
`AlgebraicGeometry.RingedSite.exists_iso_derivedCompletion_completionFunctor_obj`, and the
comparison `((ℱ|_V)[0]) ≅ (ℱ[0])|_V` of [Stacks, Tag 0942]. -/
theorem exists_isDerivedLimitWithProjections_idealSmulQuotientTower_of_eq
    (U : X.affineOpens) {r : ℕ} (g : Fin r → Γ(X, U.1))
    (J : SheafOfModules.Submodule (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf ((opensRingedSite X.sheaf).over U.1).O))))
    [(ObjectProperty.ι (AlgebraicGeometry.RingedSite.IsDerivedComplete.{u, u, u, u}
      ((opensRingedSite X.sheaf).over U.1) J)).IsRightAdjoint]
    (hJ : J = generatedIdealSheaf
      (fun i => globalSectionOfSection (opensRingedSite X.sheaf) U.1 (g i))) :
    ∃ (hp : HasProduct (fun n : ℕ =>
        (Stacks.Sites.idealSmulQuotientTower
              ((restrictModulesToSlice (opensRingedSite X.sheaf) U.1).obj ℱ) J ⋙
            DerivedCategory.singleFunctor
              (AlgebraicGeometry.RingedSite.Modules.{u, u, u}
                ((opensRingedSite X.sheaf).over U.1)) 0).obj ⟨n⟩))
      (π : ∀ n : ℕ, (derivedCompletion ((opensRingedSite X.sheaf).over U.1) J).obj
          ((SheafOfModules.overFunctor.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O))
            U.1).mapDerivedCategory.obj
            ((DerivedCategory.singleFunctor (SheafOfModules.{u}
              ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O))) 0).obj
              (ℱ : SheafOfModules.{u}
                ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O))))) ⟶
        (Stacks.Sites.idealSmulQuotientTower
              ((restrictModulesToSlice (opensRingedSite X.sheaf) U.1).obj ℱ) J ⋙
            DerivedCategory.singleFunctor
              (AlgebraicGeometry.RingedSite.Modules.{u, u, u}
                ((opensRingedSite X.sheaf).over U.1)) 0).obj ⟨n⟩),
      (∀ n : ℕ, (derivedCompletionUnit ((opensRingedSite X.sheaf).over U.1) J).app _ ≫ π n =
          ((SheafOfModules.overFunctor.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O))
                U.1).mapDerivedCategorySingleFunctor 0).hom.app
              (ℱ : SheafOfModules.{u}
                ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O))) ≫
            (DerivedCategory.singleFunctor
              (AlgebraicGeometry.RingedSite.Modules.{u, u, u}
                ((opensRingedSite X.sheaf).over U.1)) 0).map
              (Stacks.Sites.idealSmulQuotientπ
                ((restrictModulesToSlice (opensRingedSite X.sheaf) U.1).obj ℱ)
                (Stacks.Sites.idealPow (O := ((opensRingedSite X.sheaf).over U.1).O) J n))) ∧
        @NoetherianAdicCompletion.IsDerivedLimitWithProjections _ _ _ _ _ _ _
          (Stacks.Sites.idealSmulQuotientTower
              ((restrictModulesToSlice (opensRingedSite X.sheaf) U.1).obj ℱ) J ⋙
            DerivedCategory.singleFunctor
              (AlgebraicGeometry.RingedSite.Modules.{u, u, u}
                ((opensRingedSite X.sheaf).over U.1)) 0) hp
          ((derivedCompletion ((opensRingedSite X.sheaf).over U.1) J).obj
            ((SheafOfModules.overFunctor.{u}
              ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O))
              U.1).mapDerivedCategory.obj
              ((DerivedCategory.singleFunctor (SheafOfModules.{u}
                ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O))) 0).obj
                (ℱ : SheafOfModules.{u}
                  ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O)))))) π := by
  subst hJ
  have hK := AlgebraicGeometry.RingedSite.isDerivedLimitWithProjections_koszulTopSingle_completion
    ((opensRingedSite X.sheaf).over U.1)
    (fun i => globalSectionOfSection (opensRingedSite X.sheaf) U.1 (g i))
    ((restrictModulesToSlice (opensRingedSite X.sheaf) U.1).obj ℱ)
    (fun n p hp =>
      Stacks.KoszulProZero.exists_koszulDualSystemOn_over_homologyMap_eq_zero_of_section
        X ℱ U g n p hp)
  have hK2 := hK.comp_of_hasEventualInverses
    (Functor.whiskerRight
      (AlgebraicGeometry.RingedSite.koszulTopHomologyToIdealSmulQuotientTower
        ((opensRingedSite X.sheaf).over U.1)
        (fun i => globalSectionOfSection (opensRingedSite X.sheaf) U.1 (g i))
        ((restrictModulesToSlice (opensRingedSite X.sheaf) U.1).obj ℱ) (r : ℤ) koszulTopDeg_eq)
      (DerivedCategory.singleFunctor
        (AlgebraicGeometry.RingedSite.Modules.{u, u, u}
          ((opensRingedSite X.sheaf).over U.1)) 0))
    ((AlgebraicGeometry.RingedSite.hasEventualInverses_koszulTopHomologyToIdealSmulQuotientTower
      ((opensRingedSite X.sheaf).over U.1)
      (fun i => globalSectionOfSection (opensRingedSite X.sheaf) U.1 (g i))
      ((restrictModulesToSlice (opensRingedSite X.sheaf) U.1).obj ℱ) (r : ℤ)
      koszulTopDeg_eq).whiskerRight _)
  obtain ⟨θ, hθ⟩ :=
    AlgebraicGeometry.RingedSite.exists_iso_derivedCompletion_completionFunctor_obj
    ((opensRingedSite X.sheaf).over U.1)
    (fun i => globalSectionOfSection (opensRingedSite X.sheaf) U.1 (g i))
    ((SheafOfModules.overFunctor.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O))
      U.1).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor (SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O))) 0).obj
        (ℱ : SheafOfModules.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O)))))
  refine ⟨inferInstance, _, ?_, hK2.of_iso (θ ≪≫
    (AlgebraicGeometry.RingedSite.completionFunctor ((opensRingedSite X.sheaf).over U.1)
      (fun i => globalSectionOfSection (opensRingedSite X.sheaf) U.1 (g i))).mapIso
      (((SheafOfModules.overFunctor.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O))
        U.1).mapDerivedCategorySingleFunctor 0).app
        (ℱ : SheafOfModules.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O)))))⟩
  intro n
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker
    ((Category.assoc _ _ _).symm.trans
      ((eq_whisker hθ _).trans
        (((AlgebraicGeometry.RingedSite.completionUnit ((opensRingedSite X.sheaf).over U.1)
          (fun i => globalSectionOfSection (opensRingedSite X.sheaf) U.1 (g i))).naturality
          (((SheafOfModules.overFunctor.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O))
            U.1).mapDerivedCategorySingleFunctor 0).hom.app
            (ℱ : SheafOfModules.{u}
              ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O))))).symm)))
    _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact whisker_eq _
    (AlgebraicGeometry.RingedSite.completionUnit_app_comp_koszulTopSingleProjection_comp_map_eq
      ((opensRingedSite X.sheaf).over U.1)
      (fun i => globalSectionOfSection (opensRingedSite X.sheaf) U.1 (g i))
      ((restrictModulesToSlice (opensRingedSite X.sheaf) U.1).obj ℱ) n)

/-! ### The per-affine-slice presentation through the slice's own canonical maps -/

/-- **The per-affine-slice derived-limit presentation of `(ℱ|_V)^∧` over the slice's own adic
quotient tower, through the slice's own canonical maps.** This is the hypothesis of
`Stacks.Algebraization.isIso_comparison_of_affineOpens_sliceTower`, proved: no quasi-compactness
of `X` and no global generating family for `𝓘`.

On an affine open the restriction of `𝓘` is generated by finitely many sections of `Γ(X, V)`
(`Stacks.KoszulProZero.exists_eq_generatedIdealSheaf_overIdeal_affine`), which the Koszul chain
produces a pinned presentation at
(`Stacks.Algebraization.exists_isDerivedLimitWithProjections_idealSmulQuotientTower_of_eq`); its
projections and the slice's own canonical maps have the same composite with the completion unit of
the slice, so they are equal. The comparison is made after cancelling the identification of the
two towers, because it is the *restricted* tower whose terms are known to be derived complete. -/
theorem exists_isDerivedLimitWithProjections_completionToAdicQuotientSliceTower
    (U : X.affineOpens) :
    ∃ h : HasProduct (fun n : ℕ =>
        (Stacks.Sites.idealSmulQuotientTower
              ((restrictModulesToSlice (opensRingedSite X.sheaf) U.1).obj ℱ)
              (overIdeal (idealSheafSiteSubmodule I) U.1) ⋙
            DerivedCategory.singleFunctor
              (AlgebraicGeometry.RingedSite.Modules.{u, u, u}
                ((opensRingedSite X.sheaf).over U.1)) 0).obj ⟨n⟩),
      @NoetherianAdicCompletion.IsDerivedLimitWithProjections _ _ _ _ _ _ _
        (Stacks.Sites.idealSmulQuotientTower
            ((restrictModulesToSlice (opensRingedSite X.sheaf) U.1).obj ℱ)
            (overIdeal (idealSheafSiteSubmodule I) U.1) ⋙
          DerivedCategory.singleFunctor
            (AlgebraicGeometry.RingedSite.Modules.{u, u, u}
              ((opensRingedSite X.sheaf).over U.1)) 0) h
        ((derivedCompletion ((opensRingedSite X.sheaf).over U.1)
          (overIdeal (idealSheafSiteSubmodule I) U.1)).obj
          ((SheafOfModules.overFunctor.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O))
            U.1).mapDerivedCategory.obj
            ((DerivedCategory.singleFunctor (SheafOfModules.{u}
              ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O))) 0).obj
              (ℱ : SheafOfModules.{u}
                ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O))))))
        (completionToAdicQuotientSliceTower I ℱ U.1) := by
  obtain ⟨r, g, hgen⟩ :=
    Stacks.KoszulProZero.exists_eq_generatedIdealSheaf_overIdeal_affine X I U
  obtain ⟨hp, π, hπ, hlim⟩ :=
    exists_isDerivedLimitWithProjections_idealSmulQuotientTower_of_eq ℱ U g
      (overIdeal (idealSheafSiteSubmodule I) U.1) hgen
  refine ⟨hp, ?_⟩
  have hπeq : π = completionToAdicQuotientSliceTower I ℱ U.1 := by
    funext n
    have hc := congrFun (completionToAdicQuotientSliceTower_comp_inv_app I ℱ U.1) n
    refine (Iso.cancel_iso_inv_right _ _
      ((adicQuotientSliceDerivedTowerIso I ℱ U.1).app ⟨n⟩)).1 ?_
    refine (eq_restrictCompletionToAdicQuotient I ℱ U.1 n ?_).trans hc.symm
    erw [← Category.assoc, hπ n,
      ← derivedCompletionUnit_comp_completionToAdicQuotientSliceTower I ℱ U.1 n, Category.assoc,
      hc, derivedCompletionUnit_comp_restrictCompletionToAdicQuotient]
  exact hπeq ▸ hlim

/-! ### Part (3) -/

/-- **Part (3) of [Stacks, Tag 0A0K]: `ℱ^∧ = lim ℱ/𝓘ⁿℱ` with an ordinary inverse limit.** Let `X`
be a locally Noetherian scheme — **not** assumed quasi-compact — let `𝓘 ⊂ 𝒪_X` be an arbitrary
quasi-coherent sheaf of ideals and let `ℱ` be a coherent `𝒪_X`-module. Then the canonical
comparison

`c : ℱ^∧ ⟶ (lim ℱ/𝓘ⁿℱ)[0]`

from the derived completion of `ℱ` along `𝓘` to the ordinary inverse limit of the adic quotients,
placed in degree zero, is an isomorphism.

The comparison is the unique map compatible with the completion unit of `ℱ` and the limit lift
`ℱ ⟶ lim ℱ/𝓘ⁿℱ` (`Stacks.Algebraization`
`.existsUnique_comparison_derivedCompletion_limit_adicQuotientSystem`), so the statement is about
a named map and not merely the existence of an isomorphism — which is what makes it provable at
these hypotheses at all, invertibility of a named map being local on the site
(`Stacks.SheafOfModules.isIso_of_coversTop_mapDerivedCategory`).

`Stacks.Algebraization.isIso_comparison_of_affineOpens_sliceTower` reduces it to the per-affine-
slice presentation `Stacks.Algebraization`
`.exists_isDerivedLimitWithProjections_completionToAdicQuotientSliceTower`, which is the Koszul
chain of `DerivedCompletionRinged/` run on the slice over an affine open, where the restricted
ideal sheaf is generated by finitely many sections and the Artin–Rees level is computed once over
a single Noetherian model.

`Stacks.Algebraization.nonempty_iso_completion_limit_adicQuotientSystem` of
`Completion/KoszulAdicCompletionLimit.lean` is the other registration of this part: it runs the
same chain on `X` itself, which costs `[CompactSpace X]` and a global generating family for `𝓘`
and delivers the non-canonical isomorphism of [Stacks, Tag 0H9L] in place of the invertibility of
`c`. -/
@[stacks 0A0K "part (3), `ℱ^∧ = lim ℱ/𝓘ⁿℱ` with an ordinary limit, at the source's own \
hypotheses: for a coherent module `ℱ` on a locally Noetherian scheme `X`, which is **not** \
assumed quasi-compact, and an **arbitrary** quasi-coherent sheaf of ideals `𝓘` — with no global \
generating family — the canonical comparison `c : ℱ^∧ ⟶ (lim ℱ/𝓘ⁿℱ)[0]` from the derived \
completion of `ℱ` along `𝓘` to the ordinary inverse limit of the adic quotients `ℱ/𝓘ⁿℱ`, placed \
in degree zero, is an isomorphism. The comparison is the unique map compatible with the \
completion unit and the limit lift, so the statement identifies a named map rather than \
asserting an abstract isomorphism. The source's `=` is also read as such an abstract \
isomorphism by `nonempty_iso_completion_limit_adicQuotientSystem`, which buys quasi-compactness \
of the scheme and a global generating family for the ideal sheaf"]
theorem isIso_comparisonDerivedCompletionLimitAdicQuotient :
    IsIso (comparisonDerivedCompletionLimitAdicQuotient I ℱ) :=
  isIso_comparison_of_affineOpens_sliceTower I ℱ
    fun U => exists_isDerivedLimitWithProjections_completionToAdicQuotientSliceTower I ℱ U

end Stacks.Algebraization

end
