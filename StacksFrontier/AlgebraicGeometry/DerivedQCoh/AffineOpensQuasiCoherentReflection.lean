module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineOpensSite
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentDenseSubsiteReflection

/-!
# Quasi-coherence of `𝒪_X`-modules is detected on the affine opens

Let `X` be a scheme. `AlgebraicGeometry.Scheme.affineOpensToOpens` exhibits the affine opens of
`X`, with all inclusions as arrows, as a **dense subsite** of the site `X.Opens` of all opens —
the site carrying `𝒪_X` itself. This file reads off, at those universes, the two consequences of
density for sheaves of modules:

* restriction of sheaves of `𝒪_X`-modules to the affine opens is an **equivalence of
  categories**; and
* a sheaf of `𝒪_X`-modules is quasi-coherent if and only if its restriction to the affine opens
  is quasi-coherent over the restricted structure sheaf.

The second is the **reflection** of quasi-coherence across the affine opens. Only the
preservation direction was available before, as
`Stacks.SheafOfModules.isQuasicoherentOnSite_restriction`; reflection is
`Stacks.SheafOfModules.isQuasicoherentOnSite_of_subsiteRestriction`, and what this file adds is
that its hypotheses hold for `AlgebraicGeometry.Scheme.affineOpensToOpens`, where every universe
is `u`.

## Main definitions

* `AlgebraicGeometry.Scheme.affineOpensModuleRestriction`: restriction of sheaves of
  `𝒪_X`-modules along `Scheme.affineOpensToOpens`, over the structure sheaf of
  `AlgebraicGeometry.Scheme.affineZariskiRingedSite`.
* `AlgebraicGeometry.Scheme.affineOpensModuleRestrictionEquivalence`: **restriction of sheaves of
  modules to the affine opens is an equivalence of categories.**

## Main results

* `AlgebraicGeometry.Scheme.affineZariskiRingedSite_ringSheaf_eq`: the structure sheaf of
  `Scheme.affineZariskiRingedSite`, read as a sheaf of rings, is the restriction of `𝒪_X` along
  `Scheme.affineOpensToOpens` on the nose.
* `AlgebraicGeometry.Scheme.isQuasicoherentOnSite_of_affineOpensModuleRestriction`:
  **reflection of quasi-coherence across the affine opens of a scheme** — a sheaf of
  `𝒪_X`-modules whose restriction to the affine opens is quasi-coherent on the affine site is
  quasi-coherent on `X.Opens`.
* `AlgebraicGeometry.Scheme.isQuasicoherentOnSite_affineOpensModuleRestriction`: the
  preservation direction, from
  `Stacks.SheafOfModules.isQuasicoherentOnSite_restriction`.
* `AlgebraicGeometry.Scheme.isQuasicoherentOnSite_affineOpensModuleRestriction_iff`: the two
  together, as an `iff`.

## No `@[stacks]` attribute

Nothing here is tagged. Reflection and preservation together are the comparison of the
quasi-coherent *modules* on the two sites of [Stacks, Tag 0GZZ] (1) and (3), whereas the tag
asserts an equivalence of **derived** categories. That derived comparison is proved, from the
results of this file, in
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineOpensDerivedComparison.lean`, which proves
(1) ≃ (3) without registering the tag: the tag is the whole chain (1) ≃ ... ≃ (5). The underlying
general statement here is the dense-subsite form of [Stacks, Tag 03DM] for clause (6) of
[Stacks, Tag 03DL] and its converse, and the existing tags for 03DM in this development sit on
the general statements rather than on this instance.

## Implementation notes

The module universe is `u`: all four universes of the general statement — the objects and the
morphisms of each of the two sites, and the sections of the structure sheaf — are `u` here,
because `Scheme.affineZariskiRingedSite` is a `RingedSite.{u, u, u}` and `X.Opens` is a `Type u`
whose order category has morphisms in `Type u`. So the general reflection, whose module universe
is `max u v m` for sites with objects in `Type u` and morphisms in `Type v`, is instantiated at
`max u u u = u`, and no universe lift of the sections appears in any statement.

`Scheme.affineZariskiRingedSite` is built from `X.sheaf`, a sheaf of *commutative* rings, and its
`(Stacks.SheafOfModules.Tensor.ringSheaf AlgebraicGeometry.RingedSite.O)` forgets commutativity;
`X.ringCatSheaf` forgets it on `X.Opens`. The two forgetful functors are both `sheafCompose` with
`forget₂ CommRingCat RingCat`, and restriction along `Scheme.affineOpensToOpens` commutes with it
on the nose, which is `Scheme.affineZariskiRingedSite_ringSheaf_eq`.

## References

* [Stacks Project, Tag 0GZZ](https://stacks.math.columbia.edu/tag/0GZZ)
* [Stacks Project, Tag 0GZX](https://stacks.math.columbia.edu/tag/0GZX)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (X : Scheme.{u})

/-- **The structure sheaf of the affine site is the restriction of `𝒪_X`**, as a sheaf of rings:
both forget commutativity by composing with `forget₂ CommRingCat RingCat`, and restriction along
`Scheme.affineOpensToOpens` commutes with that. -/
theorem Scheme.affineZariskiRingedSite_ringSheaf_eq :
    (Stacks.SheafOfModules.Tensor.ringSheaf X.affineZariskiRingedSite.O) =
      (X.affineOpensToOpens.sheafPushforwardContinuous RingCat.{u}
        X.affineOpensTopology (Opens.grothendieckTopology X)).obj X.ringCatSheaf :=
  rfl

/-- **Restriction of sheaves of `𝒪_X`-modules to the affine opens of `X`**, over the structure
sheaf of `AlgebraicGeometry.Scheme.affineZariskiRingedSite`. -/
abbrev Scheme.affineOpensModuleRestriction :
    SheafOfModules.{u} X.ringCatSheaf ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.affineZariskiRingedSite.O) :=
  Stacks.DenseSubsiteModules.moduleRestrictionOfUniv.{u, u} X.affineOpensTopology
    X.affineOpensToOpens X.ringCatSheaf

/-- **Restriction of sheaves of modules to the affine opens of a scheme is an equivalence of
categories.** The affine opens are a dense subsite of `X.Opens`, so
`Stacks.DenseSubsiteModules.moduleRestrictionEquivalenceOfUniv` applies; both of its module
universes are `u`. -/
def Scheme.affineOpensModuleRestrictionEquivalence :
    SheafOfModules.{u} X.ringCatSheaf ≌
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.affineZariskiRingedSite.O) :=
  Stacks.DenseSubsiteModules.moduleRestrictionEquivalenceOfUniv.{u, u} X.affineOpensTopology
    X.affineOpensToOpens X.ringCatSheaf

/-- **Reflection of quasi-coherence across the affine opens of a scheme.** A sheaf of
`𝒪_X`-modules on the site `X.Opens` of all opens of `X` whose restriction to the affine opens is
quasi-coherent on the ringed site `(X_{affine, Zar}, 𝒪)` is quasi-coherent on `X.Opens`.

This is the converse of
`AlgebraicGeometry.Scheme.isQuasicoherentOnSite_affineOpensModuleRestriction`, and the content
is that `AlgebraicGeometry.Scheme.affineOpensToOpens` is a dense subsite: see
`Stacks.SheafOfModules.isQuasicoherentOnSite_of_subsiteRestriction`. -/
theorem Scheme.isQuasicoherentOnSite_of_affineOpensModuleRestriction
    (M : SheafOfModules.{u} X.ringCatSheaf)
    (h : ((X.affineOpensModuleRestriction).obj M).IsQuasicoherentOnSite) :
    M.IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_of_subsiteRestriction.{u, u, u, u}
    X.affineOpensTopology X.affineOpensToOpens X.ringCatSheaf M h

/-- **Preservation of quasi-coherence by restriction to the affine opens of a scheme.** The
restriction to the affine opens of a quasi-coherent sheaf of `𝒪_X`-modules is quasi-coherent on
the ringed site `(X_{affine, Zar}, 𝒪)`.

This is `Stacks.SheafOfModules.isQuasicoherentOnSite_restriction`, the dense-subsite
form of [Stacks, Tag 03DM] for clause (6) of [Stacks, Tag 03DL]. -/
theorem Scheme.isQuasicoherentOnSite_affineOpensModuleRestriction
    (M : SheafOfModules.{u} X.ringCatSheaf) (hM : M.IsQuasicoherentOnSite) :
    ((X.affineOpensModuleRestriction).obj M).IsQuasicoherentOnSite :=
  ((Stacks.SheafOfModules.isQuasicoherentOnSite_subsiteRestriction_iff.{u, u, u, u}
    X.affineOpensTopology X.affineOpensToOpens X.ringCatSheaf M).mpr hM)

/-- **Quasi-coherence of a sheaf of `𝒪_X`-modules is detected on the affine opens of `X`.** The
restriction of a sheaf of `𝒪_X`-modules to the affine opens, over the restricted structure
sheaf, is quasi-coherent on the ringed site `(X_{affine, Zar}, 𝒪)` if and only if the module
itself is quasi-coherent on `X.Opens`.

This is the comparison of the quasi-coherent modules on the sites (1) and (3) of
[Stacks, Tag 0GZZ]; the step from (3) to (4), the change of topology, is not involved. -/
theorem Scheme.isQuasicoherentOnSite_affineOpensModuleRestriction_iff
    (M : SheafOfModules.{u} X.ringCatSheaf) :
    ((X.affineOpensModuleRestriction).obj M).IsQuasicoherentOnSite ↔
      M.IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_subsiteRestriction_iff.{u, u, u, u}
    X.affineOpensTopology X.affineOpensToOpens X.ringCatSheaf M

end AlgebraicGeometry

end
