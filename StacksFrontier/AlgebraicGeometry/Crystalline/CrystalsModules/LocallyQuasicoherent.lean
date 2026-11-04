module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSite

/-!
# Locally quasi-coherent modules on the crystalline sites

A sheaf of `𝒪_{X/S}`-modules `F` on the big or the small crystalline site of a global crystalline
situation restricts, over every object `(U, T, δ)`, to a module `F_T` on the ambient scheme `T`:
its sections over an open `W` of `T` are the sections of `F` over the restriction
`(U ∩ W, W, δ|_W)`.  The module `F` is *locally quasi-coherent* when every one of these
restrictions is a quasi-coherent `𝒪_T`-module.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.Thickening.ringRestrictionSheaf` — the restriction of
  the structure sheaf of the big crystalline site to the ambient scheme of an object, as a sheaf
  of rings on that scheme.
* `Crystalline.GlobalCrystallineSituation.IsLocallyQuasiCoherent` — local quasi-coherence of a
  sheaf of `𝒪_{X/S}`-modules on the big crystalline site.
* `Crystalline.GlobalCrystallineSituation.SmallSite.IsLocallyQuasiCoherent` — local
  quasi-coherence of a sheaf of `𝒪_{X/S}`-modules on the small crystalline site.

## Implementation notes

Quasi-coherence of the restriction is `SheafOfModules.IsQuasicoherentOnSite`, the ringed-site
form of the condition which the crystalline notion of quasi-coherence also uses; on the Zariski
site of a scheme it is the usual notion, every open having a cover on whose members the module
is a cokernel of a map between free modules.

The restriction `F_T` is built as a presheaf of modules, and its sheaf condition is carried in
the definition as an existential rather than as a separate hypothesis: restriction along the
opens of the ambient scheme turns a sheaf on a crystalline site into a sheaf on `T`, so the
existential is no restriction, and quantifying over it keeps the definition free of a
sheafification interface for the restriction functor.

The small crystalline site is the full subcategory of the big one cut out by the objects whose
map to `X` is an open immersion, and a restriction to an open of the ambient scheme stays inside
it, so the restrictions of an object `A` of `Cris(X/S)` to the opens of its ambient scheme are
the lift through that full subcategory of the restrictions of the underlying object `A.obj` of
`CRIS(X/S)`.  Since the inclusion of the small site is the identity on objects up to the
subcategory packaging, the restricted structure sheaf of the small site *is* the restricted
structure sheaf `Crystalline.GlobalCrystallineSituation.Thickening.ringRestrictionSheaf` of the
big site at `A.obj`, and the restricted module is the pushforward of `F` along that lift; the
small-site definition is therefore stated with the big-site restricted structure sheaf and with
the lift used inline, no small-site copy of either being introduced.  The quantifier of the
small-site definition still ranges over the objects of `Cris(X/S)` alone, of which there are
fewer than of `CRIS(X/S)`.

## References

* [Stacks Project, Tag 07IS](https://stacks.math.columbia.edu/tag/07IS)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}

namespace Thickening

/-- The restriction of the structure sheaf of the big crystalline site to the ambient scheme of
an object, as a sheaf of rings on that scheme: over an open `W` it is the ring of global
sections of the open subscheme `W`. -/
noncomputable def ringRestrictionSheaf (A : Thickening S) :
    Sheaf (Opens.grothendieckTopology ↥A.thickening.target.scheme) RingCat.{u} :=
  ⟨ringRestriction A, isSheaf_ringRestriction A⟩

/-- The underlying presheaf of rings of `ringRestrictionSheaf A` is `ringRestriction A`. -/
@[simp]
theorem ringRestrictionSheaf_obj (A : Thickening S) :
    (ringRestrictionSheaf A).obj = ringRestriction A := rfl

end Thickening

/-- A sheaf of `𝒪_{X/S}`-modules on the big crystalline site is *locally quasi-coherent* when
for every object `(U, T, δ)` the restriction `F_T` is a quasi-coherent `𝒪_T`-module. -/
@[stacks 07IS "part (1): locally quasi-coherent, on the big site CRIS(X/S)"]
def IsLocallyQuasiCoherent (M : SheafOfModules.{u} (crystallineStructureSheaf S)) : Prop :=
  ∀ A : Thickening S,
    ∃ h : Presheaf.IsSheaf (Opens.grothendieckTopology ↥A.thickening.target.scheme)
      (Thickening.moduleRestriction (M.val : PresheafOfModules.{u} (crisRing S)) A).presheaf,
      SheafOfModules.IsQuasicoherentOnSite
        (⟨Thickening.moduleRestriction (M.val : PresheafOfModules.{u} (crisRing S)) A, h⟩ :
          SheafOfModules.{u} A.ringRestrictionSheaf)

namespace SmallSite

/-- A sheaf of `𝒪_{X/S}`-modules on the small crystalline site is *locally quasi-coherent* when
for every object `(U, T, δ)` of `Cris(X/S)` the restriction `F_T` is a quasi-coherent
`𝒪_T`-module. The restriction is the pushforward of `F` along the restrictions of the object to
the opens of its ambient scheme, lifted to `Cris(X/S)`; it is a module over the restriction of the
structure sheaf of the big crystalline site to the ambient scheme of the underlying object. -/
@[stacks 07IS "part (1): locally quasi-coherent, on the small site Cris(X/S)"]
def IsLocallyQuasiCoherent (M : SheafOfModules.{u} (structureSheaf S)) : Prop :=
  ∀ A : CrystallineThickening S,
    ∃ h : Presheaf.IsSheaf (Opens.grothendieckTopology ↥A.obj.thickening.target.scheme)
      ((PresheafOfModules.pushforward₀
          (ObjectProperty.lift (Thickening.IsCrystalline (S := S)) A.obj.restrictOpenFunctor
            fun W ↦ Thickening.isCrystalline_restrictOpen A.property W)
          (crisRing S)).obj (M.val : PresheafOfModules.{u} (crisRing S))).presheaf,
      SheafOfModules.IsQuasicoherentOnSite
        (⟨(PresheafOfModules.pushforward₀
              (ObjectProperty.lift (Thickening.IsCrystalline (S := S)) A.obj.restrictOpenFunctor
                fun W ↦ Thickening.isCrystalline_restrictOpen A.property W)
              (crisRing S)).obj (M.val : PresheafOfModules.{u} (crisRing S)), h⟩ :
          SheafOfModules.{u} (Thickening.ringRestrictionSheaf A.obj))

end SmallSite

end Crystalline.GlobalCrystallineSituation

end
