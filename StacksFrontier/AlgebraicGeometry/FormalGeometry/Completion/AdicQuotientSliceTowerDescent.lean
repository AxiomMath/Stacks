module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AdicQuotientSliceDescent
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AdicQuotientSliceTower

/-!
# The descent of `ℱ^∧ ⟶ (lim ℱ/𝓘ⁿℱ)[0]` at the slice's own adic quotient tower

Let `X` be a locally Noetherian scheme — **not** assumed quasi-compact — let `𝓘 ⊂ 𝒪_X` be an
arbitrary quasi-coherent sheaf of ideals and let `ℱ` be a coherent `𝒪_X`-module.
`Completion/AdicQuotientSliceDescent.lean` reduces the invertibility of the canonical comparison

`c : ℱ^∧ ⟶ (lim ℱ/𝓘ⁿℱ)[0]`

to a derived-limit presentation of `(ℱ|_V)^∧` over the **restriction** of the scheme's adic
quotient tower, for `V` ranging over the affine opens. The Koszul chain of
`DerivedCompletionRinged/` presents `(ℱ|_V)^∧` over the slice's **own** adic quotient tower
`n ↦ (ℱ|_V)/(𝓘|_V)ⁿ(ℱ|_V)` instead, that being the only one a slice of an opens site — which is
a `AlgebraicGeometry.RingedSite` and not a scheme — carries. This file restates the descent over
the latter. It is a step towards part (3) of [Stacks, Tag 0A0K] read through its canonical
comparison map, and **not** a proof of it: the per-slice presentation stays a hypothesis, so no
`@[stacks]` attribute is attached anywhere here. See "No `@[stacks]` attribute, and what would
earn one" below.

`Completion/AdicQuotientSliceTower.lean` supplies the identification of the two towers, and
nothing else is needed for the restatement: the identification is carried into the derived
category by
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor` — restriction is exact, so it commutes
with the single functor — and the presentation is transported along it by
`NoetherianAdicCompletion.IsDerivedLimitWithProjections.ofNatIso`, which carries the projections.

## Main definitions and results

* `Stacks.Algebraization.adicQuotientSliceDerivedTowerIso` — **the identification of the two
  towers in the derived category of the slice**.
* `Stacks.Algebraization.completionToAdicQuotientSliceTower` — the slice's own canonical maps
  `(ℱ|_V)^∧ ⟶ ((ℱ|_V)/(𝓘|_V)ⁿ(ℱ|_V))[0]`, read through that identification.
* `Stacks.Algebraization.isIso_comparison_of_affineOpens_sliceTower` — **the descent at the
  slice's own tower**: invertibility of `c` from a derived-limit presentation of `(ℱ|_V)^∧` over
  the slice's own tower, for `V` affine.

## No `@[stacks]` attribute here, and where part (3) is registered

Nothing in this file carries a `@[stacks 0A0K]` attribute, and the theorem below is **not** a
registration of part (3): its ambient hypotheses are the tag's own — `X` locally Noetherian, `𝓘`
an arbitrary quasi-coherent `AlgebraicGeometry.Scheme.IdealSheafData`, `ℱ` coherent, with neither
quasi-compactness of `X` nor a global generating family for `𝓘` — but it takes the
per-affine-slice derived-limit presentation as an explicit hypothesis, and that hypothesis is
part-(1)-shaped content of the same tag. A statement with such a hypothesis proves no assertion
of the tag, whoever supplies it.

**That hypothesis is now supplied, and part (3) is registered.**
`Stacks.Algebraization.exists_isDerivedLimitWithProjections_completionToAdicQuotientSliceTower`
of `Completion/AdicQuotientSliceTowerKoszul.lean` proves it from the Koszul chain of
`DerivedCompletionRinged/`, and
`Stacks.Algebraization.isIso_comparisonDerivedCompletionLimitAdicQuotient` of that file is the
registration. What this file contributes is the restatement: reading the source's equality
through the canonical comparison map is what makes the *ambient* hypotheses general, since
invertibility of a *named* map is local on the site
(`Stacks.SheafOfModules.isIso_of_coversTop_mapDerivedCategory`) while the non-canonical
isomorphism a derived limit supplies is not, and the Koszul presentation of `ℱ^∧` is genuinely
unavailable on a scheme that is not quasi-compact.

The chain's own end is
`AlgebraicGeometry.RingedSite.isDerivedLimitWithProjections_koszulTopSingle_completion`, which
presents the **Čech** completion of `ℱ|_V` over the Koszul top-cohomology tower
`n ↦ (ℱ|_V)/(f_1^{n+1}, …, f_r^{n+1})(ℱ|_V)` through projections pinned against the Čech unit by
`AlgebraicGeometry.RingedSite.completionUnit_app_comp_koszulTopSingleProjection_eq`, with the
pro-vanishing below the top degree as its only hypothesis and that discharged on an affine slice
by `Stacks.KoszulProZero.exists_koszulDualSystemOn_over_homologyMap_eq_zero_of_section`, with no
compactness. Three things stood between it and the hypothesis below, and all three are built:

* **The offset of the two site-level adic quotient towers.** `AlgebraicGeometry.RingedSite`
  `.exists_hasEventualInverses_koszulTopHomologySystem_adicQuotientTowerOn` lands the site-level
  pigeonhole at an arbitrary coefficient, but over `Stacks.Sites.adicQuotientTowerOn`, whose
  `n`-th term is `ℱ/𝓘ⁿ⁺¹ℱ`, while `Stacks.Sites.idealSmulQuotientTower` — the tower the
  hypothesis below is stated over, and the one `Completion/AdicQuotientSliceTower.lean`
  identifies the restriction with — has `ℱ/𝓘ⁿℱ`. The terms agree on the nose one index apart
  (`Stacks.Sites.idealSmulQuotient F (idealPow 𝓘 n)` and `cokernel (idealPowSmul 𝓘 n ⊤).ι` are
  the same term, `Stacks.Sites.idealPowSmul` being defined as `idealSmul (idealPow …)`), but the
  two towers are **not** isomorphic as `ℕᵒᵖ`-functors: at `n = 0` one is `ℱ/𝓘ℱ` and the other
  `ℱ/ℱ`, `Stacks.Sites.idealPow_zero` giving `𝓘⁰ = ⊤`. What relates them is
  `Stacks.Sites.adicQuotientTowerOnOffset` of
  `DerivedCompletionRinged/KoszulAdicQuotientTowerOffset.lean`, the natural transformation
  induced by `𝓘ⁿ⁺¹ ⊆ 𝓘ⁿ`, with eventual inverses at the level above.
* **The Čech completion against the reflector.** The hypothesis below is stated at
  `AlgebraicGeometry.RingedSite.derivedCompletion`, the reflector of [Stacks, Tag 099F], and the
  Koszul chain ends at `AlgebraicGeometry.RingedSite.completionFunctor`, the Čech model of
  [Stacks, Tag 099B]. The two are identified by
  `AlgebraicGeometry.RingedSite.exists_iso_derivedCompletion_completionFunctor_obj`, whose
  statement now carries the unit compatibility `derivedCompletionUnit ≫ θ.hom = completionUnit`
  that makes the comparison canonical; it used to be a bare `Nonempty`, which transports
  properties and pins no map.
* **The transport of the pinning.** The composite projections are identified with
  `Stacks.Algebraization.completionToAdicQuotientSliceTower` in
  `Completion/AdicQuotientSliceTowerKoszul.lean`. Both are maps out of a derived completion into
  a derived-complete object, so each is determined by its restriction along the unit
  (`AlgebraicGeometry.RingedSite.hom_ext_derivedCompletionUnit`), and the identification is the
  comparison of two such restrictions — the same shape of argument as
  `Stacks.Algebraization.eq_restrictComparisonLimitAdicQuotient`, carried out against the
  *restricted* tower, whose terms are the ones whose derived completeness is available.

`Stacks.Algebraization.nonempty_iso_completion_limit_adicQuotientSystem` of
`Completion/KoszulAdicCompletionLimit.lean` is the other registration of part (3): it runs the
Koszul chain on the scheme itself, which buys `[CompactSpace Y]` and a global generating family
for the ideal sheaf and produces a non-canonical isomorphism rather than inverting the canonical
map.

## Implementation notes

The two spellings of the category of modules on the slice meet here —
`AlgebraicGeometry.RingedSite.Modules ((opensRingedSite X.sheaf).over V)`, which
`Stacks.Sites.idealSmulQuotientTower` is valued in, and
`SheafOfModules ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O).over V)`,
which `SheafOfModules.overFunctor` is valued in — and **no bridge between them is needed**. The
first is a reducible abbreviation, so instance search crosses to the second on its own: all of
`CategoryTheory.Abelian`, `CategoryTheory.HasDerivedCategory`,
`CategoryTheory.Limits.HasZeroObject`, `CategoryTheory.HasShift`, `CategoryTheory.Preadditive`, the
additivity of the shifts and `CategoryTheory.Pretriangulated` resolve at the first spelling, and
the `≪≫` below crosses the two in the unifier.

What is **not** crossed by a tactic is the equality of the two families of projections: `rw`
builds its motive at a transparency where `AlgebraicGeometry.RingedSite.over`'s structure sheaf
and its restriction are not simultaneously type-correct, exactly as the implementation notes of
`Completion/AdicQuotientSliceTower.lean` and
`DerivedCompletionRinged/StrictAdicRestrictionToAnOpen.lean` record, so
`Stacks.Algebraization.completionToAdicQuotientSliceTower_comp_inv_app` is an `Eq.trans` chain
with `congrArg` and not a rewrite.

The product the derived-limit predicate asks for is transported between the two towers by
`CategoryTheory.Limits.hasLimit_of_iso` at `CategoryTheory.Discrete.natIso` of the components;
the index family has to be pinned with `(F := …)`, the two spellings of the product of a family
over `ℕ` not being found by unification from the components alone.

## References

* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
* [Stacks Project, Tag 0A0E](https://stacks.math.columbia.edu/tag/0A0E)
* [Stacks Project, Tag 0942](https://stacks.math.columbia.edu/tag/0942)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite
open Stacks.SheafOfModules (opensRingedSite)
open AlgebraicGeometry.RingedSite (restrictModulesToSlice overIdeal derivedCompletion)
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

variable {X : Scheme.{u}} (I : X.IdealSheafData) (ℱ : X.Modules) (V : X.Opens)

/-! ### The identification of the two towers in the derived category -/

/-- **The restriction of the scheme's adic quotient tower in degree zero is the slice's own adic
quotient tower in degree zero**, as inverse systems in `D(𝒪_V)`.

Two steps compose. Restriction to a slice is exact, so it commutes with the single functor and
the restriction of the tower in degree zero is the tower of restrictions in degree zero
(`CategoryTheory.Functor.mapDerivedCategorySingleFunctor`); and the tower of restrictions is the
slice's own tower, which is `Stacks.Algebraization.adicQuotientSliceTowerIso`.

The two names for the category of modules on the slice meet at the join: the first step is stated
at `SheafOfModules ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O).over V)`
and the second at `AlgebraicGeometry.RingedSite.Modules ((opensRingedSite X.sheaf).over V)`. No
bridge is needed — the latter is a reducible abbreviation of the former, and `≪≫` crosses them in
the unifier. -/
def adicQuotientSliceDerivedTowerIso :
    (adicQuotientSystem I ℱ ⋙ DerivedCategory.singleFunctor
          (SheafOfModules.{u}
              ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O))) 0) ⋙
        (SheafOfModules.overFunctor.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O))
          V).mapDerivedCategory ≅
      Stacks.Sites.idealSmulQuotientTower
          ((restrictModulesToSlice (opensRingedSite X.sheaf) V).obj ℱ)
          (overIdeal (idealSheafSiteSubmodule I) V) ⋙
        DerivedCategory.singleFunctor
          (AlgebraicGeometry.RingedSite.Modules.{u, u, u} ((opensRingedSite X.sheaf).over V)) 0 :=
  Functor.isoWhiskerLeft (adicQuotientSystem I ℱ)
      ((SheafOfModules.overFunctor.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O))
        V).mapDerivedCategorySingleFunctor 0) ≪≫
    Functor.isoWhiskerRight (adicQuotientSliceTowerIso I ℱ V)
      (DerivedCategory.singleFunctor
        (AlgebraicGeometry.RingedSite.Modules.{u, u, u} ((opensRingedSite X.sheaf).over V)) 0)

/-! ### The slice's own canonical maps onto its own tower -/

variable [IsLocallyNoetherian X] [ℱ.IsCoherent]

attribute [local instance]
  isRightAdjoint_ι_isDerivedComplete_overIdeal_idealSheafSiteSubmodule

/-- **The slice's canonical map `(ℱ|_V)^∧ ⟶ ((ℱ|_V)/(𝓘|_V)ⁿ(ℱ|_V))[0]`**: the slice's canonical
map onto the `n`-th term of the *restricted* tower,
`Stacks.Algebraization.restrictCompletionToAdicQuotient`, read through the identification of that
term with the `n`-th term of the slice's own tower.

Both factors are pinned, so the composite is: the first is the unique map restricting along the
completion unit of the slice to the restriction of the quotient projection `ℱ ⟶ ℱ/𝓘ⁿℱ`
(`Stacks.Algebraization.derivedCompletionUnit_comp_restrictCompletionToAdicQuotient`), and the
second is pinned by the quotient projections out of `ℱ|_V`
(`Stacks.Algebraization.π_comp_adicQuotientSliceTowerIso_hom_app`). -/
def completionToAdicQuotientSliceTower (n : ℕ) :
    (derivedCompletion ((opensRingedSite X.sheaf).over V)
        (overIdeal (idealSheafSiteSubmodule I) V)).obj
        ((SheafOfModules.overFunctor.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O))
          V).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor (SheafOfModules.{u}
              ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O)))
            0).obj (ℱ : SheafOfModules.{u}
                ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O))))) ⟶
      (Stacks.Sites.idealSmulQuotientTower
          ((restrictModulesToSlice (opensRingedSite X.sheaf) V).obj ℱ)
          (overIdeal (idealSheafSiteSubmodule I) V) ⋙
        DerivedCategory.singleFunctor
          (AlgebraicGeometry.RingedSite.Modules.{u, u, u}
            ((opensRingedSite X.sheaf).over V)) 0).obj ⟨n⟩ :=
  restrictCompletionToAdicQuotient I ℱ V n ≫
    (adicQuotientSliceDerivedTowerIso I ℱ V).hom.app ⟨n⟩

omit [ℱ.IsCoherent] in
/-- Undoing the identification of the towers returns the slice's canonical maps onto the
restricted tower. This is the one equation the transport below needs, and it is an `Eq.trans`
chain rather than a rewrite: `rw` builds its motive at a transparency at which the structure
sheaf of the slice site and the restriction of the structure sheaf are not simultaneously
type-correct. -/
theorem completionToAdicQuotientSliceTower_comp_inv_app :
    (fun n : ℕ => completionToAdicQuotientSliceTower I ℱ V n ≫
        (adicQuotientSliceDerivedTowerIso I ℱ V).symm.hom.app ⟨n⟩) =
      restrictCompletionToAdicQuotient I ℱ V := by
  funext n
  exact (Category.assoc (restrictCompletionToAdicQuotient I ℱ V n)
      ((adicQuotientSliceDerivedTowerIso I ℱ V).hom.app ⟨n⟩)
      ((adicQuotientSliceDerivedTowerIso I ℱ V).inv.app ⟨n⟩)).trans
    ((congrArg (fun g => restrictCompletionToAdicQuotient I ℱ V n ≫ g)
        ((adicQuotientSliceDerivedTowerIso I ℱ V).hom_inv_id_app ⟨n⟩)).trans
      (Category.comp_id _))

/-! ### The descent -/

/-- **The descent of the canonical comparison at the slice's own adic quotient tower.** Let `X`
be a locally Noetherian scheme, `𝓘 ⊂ 𝒪_X` an arbitrary
quasi-coherent sheaf of ideals and `ℱ` a coherent `𝒪_X`-module. If over every affine open `V`
the derived completion `(ℱ|_V)^∧` is a derived inverse limit of the slice's **own** adic quotient
tower `n ↦ (ℱ|_V)/(𝓘|_V)ⁿ(ℱ|_V)` through the slice's own canonical maps
`Stacks.Algebraization.completionToAdicQuotientSliceTower`, then the canonical comparison
`c : ℱ^∧ ⟶ (lim ℱ/𝓘ⁿℱ)[0]` is an isomorphism, so that `ℱ^∧ = lim ℱ/𝓘ⁿℱ` with an ordinary limit.

This is `Stacks.Algebraization.isIso_comparison_of_affineOpens` with its hypothesis moved off the
restriction of the scheme's tower and onto the slice's own, which is the tower the Koszul chain of
`DerivedCompletionRinged/` presents `(ℱ|_V)^∧` over, a slice of an opens site being a ringed site
and not a scheme. The move is the identification
`Stacks.Algebraization.adicQuotientSliceDerivedTowerIso` and
`NoetherianAdicCompletion.IsDerivedLimitWithProjections.ofNatIso`, which carries the projections
across; `Stacks.Algebraization.completionToAdicQuotientSliceTower_comp_inv_app` identifies the
transported projections with the ones the restricted statement asks for.

No quasi-compactness of `X` and no global generating family for `𝓘` appear in the ambient
hypotheses. Both are genuinely needed by the other route to part (3),
`Stacks.Algebraization.nonempty_iso_completion_limit_adicQuotientSystem`, which pays for them an
unconditional statement and a non-canonical isomorphism; reading the source's equality through
the canonical map is what buys the general hypotheses, invertibility of a named map being local
on the site while a derived limit's isomorphism is not.

This carries **no** `@[stacks]` attribute and is not a registration of part (3): `hq` is a
derived-limit presentation of `(ℱ|_V)^∧`, which is part-(1)-shaped content of the same tag, so
the statement proves no assertion of the tag by itself. `hq` is supplied by
`Stacks.Algebraization.exists_isDerivedLimitWithProjections_completionToAdicQuotientSliceTower`
and part (3) registered by
`Stacks.Algebraization.isIso_comparisonDerivedCompletionLimitAdicQuotient`, both of
`Completion/AdicQuotientSliceTowerKoszul.lean`. -/
theorem isIso_comparison_of_affineOpens_sliceTower
    (hq : ∀ U : X.affineOpens, ∃ h : HasProduct (fun n : ℕ =>
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
        (completionToAdicQuotientSliceTower I ℱ U.1)) :
    IsIso (comparisonDerivedCompletionLimitAdicQuotient I ℱ) := by
  refine isIso_comparison_of_affineOpens I ℱ fun U => ?_
  obtain ⟨hp, hlim⟩ := hq U
  have := hp
  have hp' : HasProduct (fun n : ℕ =>
      ((adicQuotientSystem I ℱ ⋙ DerivedCategory.singleFunctor
            (SheafOfModules.{u}
                ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O))) 0) ⋙
          (SheafOfModules.overFunctor.{u}
              ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O))
            U.1).mapDerivedCategory).obj ⟨n⟩) :=
    hasLimit_of_iso (F := Discrete.functor fun n : ℕ =>
        (Stacks.Sites.idealSmulQuotientTower
              ((restrictModulesToSlice (opensRingedSite X.sheaf) U.1).obj ℱ)
              (overIdeal (idealSheafSiteSubmodule I) U.1) ⋙
            DerivedCategory.singleFunctor
              (AlgebraicGeometry.RingedSite.Modules.{u, u, u}
                ((opensRingedSite X.sheaf).over U.1)) 0).obj ⟨n⟩)
      (Discrete.natIso fun j =>
        ((adicQuotientSliceDerivedTowerIso I ℱ U.1).app ⟨j.as⟩).symm)
  exact ⟨hp', completionToAdicQuotientSliceTower_comp_inv_app I ℱ U.1 ▸
    NoetherianAdicCompletion.IsDerivedLimitWithProjections.ofNatIso
      (adicQuotientSliceDerivedTowerIso I ℱ U.1).symm hlim⟩

end Stacks.Algebraization

end
