module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.IdealSheafSiteSubmodule
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerModule
public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.IdealPowerSections

/-!
# `𝓘ⁿℱ` on a scheme is `𝓘ⁿℱ` on its small Zariski site

Let `X` be a scheme, `𝓘` a quasi-coherent sheaf of ideals and `ℱ` a sheaf of `𝒪_X`-modules.
Two constructions in this library produce the subsheaf `𝓘ⁿℱ`, and nothing related them.

* `Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple 𝓘 n ℱ` is the **infimum** of the
  subsheaves of `ℱ` whose sections over every *affine* open `U` contain `𝓘(U)ⁿ Γ(ℱ, U)`. It is
  what the adic quotient tower `Stacks.Algebraization.adicQuotientSystem` of
  `Completion/AdicQuotientSystem.lean` is built from, and what the Artin–Rees statements for
  schemes are written at.
* `Stacks.Sites.idealPowSmul ℐ n ⊤` is the **local-membership closure** of the objectwise product
  `W ↦ ℐ(W)ⁿ ℱ(W)`, for `ℐ` a sheaf of ideals of the structure sheaf of an arbitrary ringed
  site. It is what the site-level adic quotients of `CategoryTheory/Sites/Modules/` are built
  from, and what the Koszul chain of `DerivedCompletionRinged/` meets after restriction to a
  slice — the slice of a scheme's opens site is not an opens site of a scheme, so the
  scheme-level construction is unavailable there.

This file identifies them, at `ℐ` the reading `Stacks.Algebraization.idealSheafSiteSubmodule 𝓘`
of `𝓘` as a sheaf of ideals of the structure sheaf of the opens ringed site. Nothing is assumed:
neither quasi-coherence of `ℱ` nor that `X` be locally Noetherian.

## Main results

* `Stacks.Algebraization.idealPowSmul_le_idealPowerMultiple` and
  `Stacks.Algebraization.idealPowerMultiple_le_idealPowSmul` — the two inclusions.
* `Stacks.Algebraization.idealPowerMultiple_eq_idealPowSmul` — **`𝓘ⁿℱ` computed on the scheme is
  `𝓘ⁿℱ` computed on the site.**

## What this unblocks

The adic quotient tower of a scheme and its site-level counterpart are the cokernels of the
inclusions of these two subsheaves, so the identification is what lets the restriction of the
scheme's tower to a slice be compared with the slice's own tower — the one remaining input of
the descent of `Completion/AdicQuotientSliceDescent.lean`. Two module docstrings in this subtree
recorded that no such comparison existed and that none was wanted where they stood
(`Completion/AdicQuotientModuleSiteQuasicoherent.lean`,
`Completion/AffineAdicTowerR1LimVanishing.lean`); both remain correct about their own
statements, which are at `ℱ = 𝒪` and need no comparison.

## Implementation notes

The two constructions are characterized by universal properties with *different* index sets —
`Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple_le_iff` tests against the affine opens
only, while `Stacks.Sites.idealPowSmul_le_iff` tests against every object of the site — and that
asymmetry is the whole content.

One inclusion is immediate: over an affine open `U` the ideal of sections of `ℐ` is `𝓘(U)` on the
nose (`Stacks.Algebraization.idealSheafSiteSubmodule_obj_affine`), so the affine-local lower
bound defining `idealPowerMultiple` is one of the objectwise lower bounds `idealPowSmul`
satisfies.

The other needs the passage from the affine opens to all of them, and that is the locality of
membership in a `SheafOfModules.Submodule`
(`Stacks.AlgebraicGeometry.IdealPower.mem_of_forall_affineOpens`): a product `a·s` of a section
`a` of `ℐ(W)ⁿ` with a section `s` of `ℱ` over an arbitrary open `W` restricts, over an affine
`U ⊆ W`, to `a|_U · s|_U` with `a|_U ∈ 𝓘(U)ⁿ`, because restriction is a ring map and carries the
`n`-th power of an ideal into the `n`-th power of the image. The restricted product then lies in
the affine-local lower bound.

`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules X.ringCatSheaf` while
`Stacks.Sites.idealPowSmul` is stated for sheaves of modules over
`Stacks.SheafOfModules.Tensor.ringSheaf 𝒪` of a site; the two sheaves of rings are
definitionally but not syntactically equal, so each statement below ascribes its objects into
one spelling, the sheaf of commutative rings is passed as `(O := …)` rather than inferred, and
the crossings are confined to the statement boundary — as elsewhere in this directory.

## References

* [Stacks Project, Tag 0942](https://stacks.math.columbia.edu/tag/0942)
* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.IdealPower
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable {X : Scheme.{u}} (I : X.IdealSheafData) (ℱ : X.Modules)

/-- Over an affine open `U`, the `n`-th power of the ideal of sections of `ℐ` is `𝓘(U)ⁿ`. -/
private theorem sectionIdeal_pow_affine (U : X.affineOpens) (n : ℕ) :
    Stacks.Sites.sectionIdeal (O := (Stacks.SheafOfModules.opensRingedSite X.sheaf).O)
      (idealSheafSiteSubmodule I) (op U.1) ^ n = I.ideal U ^ n :=
  congrArg (· ^ n) (idealSheafSiteSubmodule_obj_affine I U)

/-- **`𝓘ⁿℱ` computed on the site is contained in `𝓘ⁿℱ` computed on the scheme.** The site-level
product is the smallest subsheaf whose sections over every open contain the objectwise product
`𝓘(W)ⁿ Γ(ℱ, W)`, so it is enough that a product `a·s` of a section of `𝓘(W)ⁿ` with a section of
`ℱ` lie in the scheme-level subsheaf.

Membership there is local on the affine opens, so it is enough over an affine `U ⊆ W`, where the
restriction of `a` lies in `𝓘(U)ⁿ` — restriction is a ring map carrying `𝓘(W)` into `𝓘(U)`,
hence `𝓘(W)ⁿ` into `𝓘(U)ⁿ` — and `𝓘(U)ⁿ Γ(ℱ, U)` is the affine-local lower bound defining the
scheme-level subsheaf. -/
theorem idealPowSmul_le_idealPowerMultiple (n : ℕ) :
    Stacks.Sites.idealPowSmul (O := (Stacks.SheafOfModules.opensRingedSite X.sheaf).O)
        (idealSheafSiteSubmodule I) n
        (⊤ : (show SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
            (Stacks.SheafOfModules.opensRingedSite X.sheaf).O)) from ℱ).Submodule) ≤
      (show (show SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
          (Stacks.SheafOfModules.opensRingedSite X.sheaf).O)) from ℱ).Submodule from
        idealPowerMultiple I n ℱ) := by
  refine (Stacks.Sites.idealPowSmul_le_iff
    (O := (Stacks.SheafOfModules.opensRingedSite X.sheaf).O)
    (idealSheafSiteSubmodule I) n _ _).2 fun W => ?_
  refine Submodule.smul_le.2 ?_
  intro a ha s _
  refine mem_of_forall_affineOpens (idealPowerMultiple I n ℱ) (a • s) fun U hU => ?_
  have hsmul : ℱ.presheaf.map (homOfLE hU).op (a • s) =
      X.presheaf.map (homOfLE hU).op a • ℱ.presheaf.map (homOfLE hU).op s :=
    PresheafOfModules.map_smul ℱ.val (homOfLE hU).op a s
  rw [hsmul]
  refine le_idealPowerMultiple_obj I n ℱ U (Submodule.smul_mem_smul ?_ Submodule.mem_top)
  have ha' : a ∈ Stacks.Sites.sectionIdeal
      (O := (Stacks.SheafOfModules.opensRingedSite X.sheaf).O)
      (idealSheafSiteSubmodule I) W ^ n := ha
  have hi : Ideal.map
      ((Stacks.SheafOfModules.opensRingedSite X.sheaf).O.obj.map (homOfLE hU).op).hom
      (Stacks.Sites.sectionIdeal (O := (Stacks.SheafOfModules.opensRingedSite X.sheaf).O)
        (idealSheafSiteSubmodule I) W) ≤
      Stacks.Sites.sectionIdeal (O := (Stacks.SheafOfModules.opensRingedSite X.sheaf).O)
        (idealSheafSiteSubmodule I) (op U.1) :=
    Ideal.map_le_iff_le_comap.mpr fun z hz =>
      (idealSheafSiteSubmodule I).toSubmodule.map (homOfLE hU).op hz
  have hpow := pow_le_pow_left' hi n
  rw [← Ideal.map_pow] at hpow
  exact (sectionIdeal_pow_affine I U n).le (hpow (Ideal.mem_map_of_mem _ ha'))

/-- **`𝓘ⁿℱ` computed on the scheme is contained in `𝓘ⁿℱ` computed on the site.** The scheme-level
product is the infimum of the subsheaves bounded below on the affine opens, and over an affine
open the ideal of sections of `𝓘` is `𝓘(U)`, so that bound is one of the objectwise bounds the
site-level product satisfies. -/
theorem idealPowerMultiple_le_idealPowSmul (n : ℕ) :
    (show (show SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Stacks.SheafOfModules.opensRingedSite X.sheaf).O)) from ℱ).Submodule from
        idealPowerMultiple I n ℱ) ≤
      Stacks.Sites.idealPowSmul (O := (Stacks.SheafOfModules.opensRingedSite X.sheaf).O)
        (idealSheafSiteSubmodule I) n
        (⊤ : (show SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
            (Stacks.SheafOfModules.opensRingedSite X.sheaf).O)) from ℱ).Submodule) := by
  refine (idealPowerMultiple_le_iff I n ℱ _).2 fun U => ?_
  refine Submodule.smul_le.2 ?_
  intro a ha z _
  exact Stacks.Sites.smul_mem_idealPowSmul_of_mem_pow (idealSheafSiteSubmodule I) n
    ((sectionIdeal_pow_affine I U n).ge ha)
    (Stacks.SheafOfModules.mem_top_obj z)

/-- **`𝓘ⁿℱ` computed on the scheme is `𝓘ⁿℱ` computed on its small Zariski site.** The infimum of
the subsheaves of `ℱ` bounded below by `𝓘(U)ⁿ Γ(ℱ, U)` on every affine open agrees with the
local-membership closure of the objectwise product `W ↦ 𝓘(W)ⁿ Γ(ℱ, W)`.

Nothing is assumed of `ℱ` or of `X`. The content is the asymmetry of the two universal
properties: one tests against the affine opens, the other against every open, and the two meet
because membership in a subsheaf is local on the affine opens. -/
theorem idealPowerMultiple_eq_idealPowSmul (n : ℕ) :
    (show (show SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Stacks.SheafOfModules.opensRingedSite X.sheaf).O)) from ℱ).Submodule from
        idealPowerMultiple I n ℱ) =
      Stacks.Sites.idealPowSmul (O := (Stacks.SheafOfModules.opensRingedSite X.sheaf).O)
        (idealSheafSiteSubmodule I) n
        (⊤ : (show SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
            (Stacks.SheafOfModules.opensRingedSite X.sheaf).O)) from ℱ).Submodule) :=
  le_antisymm (idealPowerMultiple_le_idealPowSmul I ℱ n)
    (idealPowSmul_le_idealPowerMultiple I ℱ n)

end Stacks.Algebraization

end
