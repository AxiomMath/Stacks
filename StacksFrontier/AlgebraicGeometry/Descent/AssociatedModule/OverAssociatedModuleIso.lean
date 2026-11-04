module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentTopologiesTwo.TopologyIndependence
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSiteAssociatedModule

/-!
# The sections-defined `𝓕^a` of 03DU (3) is the pullback, on the big fppf site

[Stacks, Tag 03DU] (3) defines the associated module `𝓕^a` on a big `τ`-site of `S` by its
sections, `(f : T → S) ↦ Γ(T, f^*𝓕)`; that definition is
`AlgebraicGeometry.overAssociatedModule`, which carries the tag.
`AlgebraicGeometry.BigFppfOver.associatedModule` is instead the pullback of sheaves of modules
along the morphism of ringed sites `id_{fppf, Zar} : ((Sch/S)_fppf, 𝒪) → (S_Zar, 𝒪_S)`.
[Stacks, Remark 03FH] (1) says the two agree.  This file records that, at `τ = fppf`, they
agree **on the nose**.

`AlgebraicGeometry.BigFppfOver.sectionsSheafOfModules` is the pullback-sections presheaf of
modules packaged with its sheaf condition, and
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleIsoSectionsSheaf` identifies the pullback
with it at every `τ : AlgebraicGeometry.SiteKind`, from [Stacks, Tag 070S] (1) and [Stacks,
Tag 03DT].  What is observed here is that at `τ = fppf` that packaging is *definitionally*
`AlgebraicGeometry.overAssociatedModule`: both are the restriction of [Stacks, Tag 03DS] along
the same functor to the schemes over `S`, with the same module structures, over the same
structure sheaf (`AlgebraicGeometry.overStructureSheaf_fppf`).

## Main results

* `AlgebraicGeometry.BigFppfOver.overAssociatedModule_fppf`: the two packagings of the
  pullback-sections sheaf on `(Sch/S)_fppf` are equal.
* `AlgebraicGeometry.BigFppfOver.associatedModuleIsoOverAssociatedModule`: **[Stacks,
  Remark 03FH] (1) at `τ = fppf`** — the pullback of `𝓕` along `id_{fppf, Zar}` is the
  sections-defined `𝓕^a` of [Stacks, Tag 03DU] (3).

## Implementation notes

Only `τ = fppf` is covered, and the obstruction is a parametrization mismatch rather than
mathematics.  `AlgebraicGeometry.overAssociatedModule` is indexed by
`AlgebraicGeometry.CoveringTopology` together with a site `AlgebraicGeometry.BigSite τ` of that
very topology, so for `τ ≠ fppf` its underlying category is that of a Zariski, étale, smooth or
syntomic big site; `AlgebraicGeometry.BigFppfOver.baseAssociatedModule` is indexed by
`AlgebraicGeometry.SiteKind` and keeps the big *fppf* category throughout, varying only the
topology on it.  The two families meet exactly where the categories do, at
`AlgebraicGeometry.CoveringTopology.fppf`, and there `AlgebraicGeometry.BigSite` reduces to
`AlgebraicGeometry.BigFppfSite` and `AlgebraicGeometry.overTopology` to
`AlgebraicGeometry.BigFppfOver.topology`, both by `rfl`.  Relating them at the other three
topologies is a comparison of two big sites, not an instance of this statement.

The small étale half of [Stacks, Remark 03FH] (1) is
`AlgebraicGeometry.SmallEtale.associatedModuleIsoOfSections`.

No `stacks` attribute is placed here: [Stacks, Remark 03FH] (1) quantifies over the five
topologies and over both the big and the small sites, so this is a proper part of its clause.

## References

* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03FH](https://stacks.math.columbia.edu/tag/03FH)
* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : S.Modules) [F.IsQuasicoherent]

/-- The pullback-sections sheaf of modules on `(Sch/S)_fppf` is the associated module `𝓕^a` of
[Stacks, Tag 03DU] (3) at `τ = fppf`.

Both are the restriction of the presheaf of [Stacks, Tag 03DS] along the inclusion of the big
fppf category of `S`-schemes into the schemes over `S`, with the module structure of
[Stacks, Tag 03DU], together with a sheaf condition; the sheaf conditions are propositions, and
the structure sheaves agree by `AlgebraicGeometry.overStructureSheaf_fppf`. -/
public theorem overAssociatedModule_fppf :
    overAssociatedModule .fppf B S hS F = sectionsSheafOfModules B S hS .fppf F :=
  rfl

/-- **[Stacks, Remark 03FH] (1) on the big fppf site of `S`.**  The pullback of a quasi-coherent
`𝒪_S`-module `𝓕` along the morphism of ringed sites
`id_{fppf, Zar} : ((Sch/S)_fppf, 𝒪) → (S_Zar, 𝒪_S)` is the sections-defined associated module
`𝓕^a` of [Stacks, Tag 03DU] (3), whose value at `f : T → S` is `Γ(T, f^*𝓕)`.

This is `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleIsoSectionsSheaf` at `τ = fppf`,
read through `AlgebraicGeometry.BigFppfOver.overAssociatedModule_fppf`; its two inputs are
[Stacks, Tag 070S] (1), `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleIsoSections`, and
[Stacks, Tag 03DT] on the big `τ`-sites,
`AlgebraicGeometry.BigFppfOver.isSheaf_sectionsPresheafOfModules_baseOverTopology`. -/
public noncomputable def associatedModuleIsoOverAssociatedModule :
    (associatedModule B S hS).obj F ≅ overAssociatedModule .fppf B S hS F :=
  baseAssociatedModuleIsoSectionsSheaf B S hS .fppf F

end AlgebraicGeometry.BigFppfOver

end
