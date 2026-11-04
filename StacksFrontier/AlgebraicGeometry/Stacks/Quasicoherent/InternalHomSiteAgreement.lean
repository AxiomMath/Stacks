module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.InternalHom

/-!
# The internal Hom of modules on a stack is the same on `𝒳_étale` and on `𝒳_fppf`

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids.  Its five associated sites
all carry the structure sheaf of Stacks 06TV, so each of them is a ringed site and the internal
Hom of Stacks 03EM is available on each.  The first assertion of **Stacks 0GQN** is that for
`𝒳` an algebraic stack, `𝒡` of finite presentation and `𝒢` quasi-coherent, the internal Hom
`Hom_{𝒪_𝒳}(𝒡, 𝒢)` computed in `Mod(𝒳_étale, 𝒪_𝒳)` and the one computed in `Mod(𝒪_𝒳)`, that is
on the associated fppf site, agree.

That assertion is proved here, and the source's own argument for it shows more than the source
states: the internal Hom is built from the presheaves of modules underlying its two arguments
and from the presheaf of rings underlying the structure sheaf, and none of those three changes
with the topology.  So the two internal Homs have *equal* underlying presheaves of modules, for
arbitrary sheaves of modules on the associated fppf site and for all five associated topologies
at once.  The remaining half of the agreement is that the common presheaf is a sheaf for the
fppf topology — only then is the module computed on `𝒳_étale` an object of `Mod(𝒪_𝒳)` — and that
holds because the internal Hom of Stacks 03EM is a sheaf as soon as its target is.

## Main definitions

* `AlgebraicGeometry.FibredSite.restrictSiteModules`: a sheaf of modules on the associated fppf
  site, read as a sheaf of modules on one of the five associated sites, with its underlying
  presheaf of modules unchanged.

## Main results

* `AlgebraicGeometry.FibredSite.internalHomSheaf_restrictSiteModules_val`: **Stacks 0GQN**, the
  equality of the two underlying presheaves of modules.
* `AlgebraicGeometry.FibredSite.isSheaf_internalHomSheaf_restrictSiteModules`:
  **Stacks 0GQN**, the internal Hom computed on a coarser associated site is a sheaf for the
  fppf associated topology.
* `AlgebraicGeometry.FibredSite.internalHomSheaf_restrictSiteModules_eq`: **Stacks 0GQN**, the
  two internal Homs agree as objects of `Mod(𝒪_𝒳)`.

## Implementation notes

The hypotheses of the source — that `𝒳` be an algebraic stack, that `𝒡` be of finite
presentation and that `𝒢` be quasi-coherent — are not used, and the source does not use them
for this assertion either; they enter its later assertions, about local quasi-coherence, the
flat base change property and the quasi-coherator.  Only the fppf sheaf condition on the two
arguments is used, and it is used exactly once, for the target: `𝒢` being a sheaf for the fppf
topology is what makes the internal Hom one.  So the statements below are strictly more general
than the assertion they realize, in the same way as `Stacks 06WN`'s comparison in
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.InternalHom`, which they generalize from
quasi-coherent arguments to arbitrary ones.

The sections of the modules live in a universe `m` independent of the universes of the fibred
category.  That independence is not optional here: the internal Hom of two modules with
sections in `m` on a site whose objects lie in `Type v` and whose morphisms lie in `Type w` has
its sections in `max v w m`, so a statement binding `m` to the universe of the schemes could
not be applied to its own output.

Both sides are spelled through `AlgebraicGeometry.FibredSite.ringedSite` and
`AlgebraicGeometry.RingedSite.internalHomSheaf`, the ringed-site spelling, rather than through
`AlgebraicGeometry.Stack.ringStructureSheafCore`, which takes a Grothendieck topology on the
schemes together with a proof that it is coarser than the fppf one.  The two spellings of the
structure sheaf are not interchangeable in a statement, and this file uses the `SiteKind`
one throughout.

## References

* [Stacks Project, Tag 0GQN](https://stacks.math.columbia.edu/tag/0GQN)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 06TV](https://stacks.math.columbia.edu/tag/06TV)
* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
-/

@[expose] public section

open CategoryTheory

universe u v w m

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)

/-- A sheaf of modules on the associated fppf site of a category fibred in groupoids, read as a
sheaf of modules on one of the five associated sites.  Neither the underlying presheaf of
modules nor the underlying presheaf of rings changes: a sheaf for the inherited fppf topology
is a sheaf for each coarser inherited topology.

This is `AlgebraicGeometry.FibredSite.toSiteModules` with the quasi-coherence hypothesis on the
module dropped. -/
public def restrictSiteModules (τ : SiteKind)
    (F : SheafOfModules.{m} (ringStructureSheafCore B S hS p hp .fppf)) :
    SheafOfModules.{m} (ringStructureSheafCore B S hS p hp τ) :=
  ⟨F.val, F.isSheaf.of_le (BigFppfOver.associatedTopology_le_fppf B S hS p τ)⟩

/-- **Stacks 0GQN**, the first assertion, on underlying presheaves of modules.  The internal
Hom of two sheaves of modules on the associated fppf site of a category fibred in groupoids has
the same underlying presheaf of modules whether it is computed on the associated fppf site or
on any of the five associated sites; the source's case is the étale one.

The internal Hom of Stacks 03EM is built from the presheaves of modules underlying its two
arguments and from the presheaf of rings underlying the structure sheaf, and none of the three
depends on the topology, so the two presheaves of modules are equal on the nose. -/
@[stacks 0GQN "the two internal Homs have the same presheaf of modules"]
public theorem internalHomSheaf_restrictSiteModules_val (τ : SiteKind)
    (F G : SheafOfModules.{m} (ringStructureSheafCore B S hS p hp .fppf)) :
    ((ringedSite B S hS p hp τ).internalHomSheaf
        (restrictSiteModules.{u, v, w, m} B S hS p hp τ F)
        (restrictSiteModules.{u, v, w, m} B S hS p hp τ G)).val =
      ((ringedSite B S hS p hp .fppf).internalHomSheaf F G).val :=
  rfl

/-- **Stacks 0GQN**, the first assertion, on the sheaf condition.  The internal Hom computed on
one of the five associated sites of a category fibred in groupoids is a sheaf for the
associated *fppf* topology, so it is an object of `Mod(𝒪_𝒳)` and not merely of
`Mod(𝒳_étale, 𝒪_𝒳)`.

By Stacks 03EM the internal Hom is a sheaf for any topology for which its target is one, and
the target here is a sheaf for the associated fppf topology. -/
@[stacks 0GQN "the common value is a sheaf for the fppf topology"]
public theorem isSheaf_internalHomSheaf_restrictSiteModules (τ : SiteKind)
    (F G : SheafOfModules.{m} (ringStructureSheafCore B S hS p hp .fppf)) :
    Presheaf.IsSheaf (BigFppfOver.associatedTopology B S hS p .fppf)
      ((ringedSite B S hS p hp τ).internalHomSheaf
        (restrictSiteModules.{u, v, w, m} B S hS p hp τ F)
        (restrictSiteModules.{u, v, w, m} B S hS p hp τ G)).val.presheaf :=
  ((ringedSite B S hS p hp .fppf).internalHomSheaf F G).isSheaf

/-- **Stacks 0GQN**, the first assertion.  The internal Hom of two sheaves of modules on the
associated fppf site of a category fibred in groupoids, computed on one of the five associated
sites, agrees as an object of `Mod(𝒪_𝒳)` with the one computed on the associated fppf site; the
source's case is the étale one.

This is the conjunction of the two statements above: the underlying presheaves of modules are
equal, and the common presheaf is a sheaf for the associated fppf topology. -/
@[stacks 0GQN "the two internal Homs agree as objects of Mod(𝒪_𝒳)"]
public theorem internalHomSheaf_restrictSiteModules_eq (τ : SiteKind)
    (F G : SheafOfModules.{m} (ringStructureSheafCore B S hS p hp .fppf)) :
    (⟨((ringedSite B S hS p hp τ).internalHomSheaf
          (restrictSiteModules.{u, v, w, m} B S hS p hp τ F)
          (restrictSiteModules.{u, v, w, m} B S hS p hp τ G)).val,
        isSheaf_internalHomSheaf_restrictSiteModules.{u, v, w, m} B S hS p hp τ F G⟩ :
        SheafOfModules.{max v w m} (ringStructureSheafCore B S hS p hp .fppf)) =
      (ringedSite B S hS p hp .fppf).internalHomSheaf F G :=
  rfl

end AlgebraicGeometry.FibredSite

end
