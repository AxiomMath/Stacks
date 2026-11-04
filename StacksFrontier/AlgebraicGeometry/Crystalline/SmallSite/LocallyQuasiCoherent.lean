module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyGlue.AffineOpenVanishing
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.AffineRestrictionPresentation
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.StructureSheaf

/-!
# The restriction of a locally quasi-coherent module to the ambient scheme of an object

Fix a global crystalline situation `(p, (S, I, γ), X)`.  An object `(U, T, δ)` of the small
crystalline site `Cris(X/S)` restricts to `(U ∩ W, W, δ|_W)` over every open `W` of its ambient
scheme `T`, and these restrictions form a functor from the opens of `T` to `Cris(X/S)`
(`SmallSite.CrystallineThickening.restrictOpenFunctor`).  A sheaf of `𝒪_{X/S}`-modules `F`
therefore has, for every object `(U, T, δ)`, a restriction `F_T` on `T` with
`F_T(W) = F(U ∩ W, W, δ|_W)`, a module over the restriction of `𝒪_{X/S}`, which is the structure
sheaf of `T`.  Local quasi-coherence of `F`,
`Crystalline.GlobalCrystallineSituation.SmallSite.IsLocallyQuasiCoherent`, says that every one of
these restrictions is a quasi-coherent module.

This file reads that condition on the restriction taken as a *sheaf* of `𝒪_T`-modules, and uses it
for the vanishing of the higher cohomology of `F_T` on an affine ambient scheme, which is the step
of [Stacks, Tag 07JJ] at which local quasi-coherence is used.

## Main definitions

* `SmallSite.CrystallineThickening.ringRestrictionIso` — the restriction of the structure sheaf
  `𝒪_{X/S}` to the ambient scheme of an object, identified with the structure sheaf of rings of
  that scheme.
* `SmallSite.CrystallineThickening.modulePresheafRestriction` — the restriction `F_T` of a sheaf
  of `𝒪_{X/S}`-modules to the ambient scheme of an object, as a presheaf of `𝒪_T`-modules.
* `SmallSite.CrystallineThickening.moduleRestriction` — the same restriction read as a sheaf of
  `𝒪_T`-modules.

## Main results

* `SmallSite.isQuasicoherentOnSite_moduleRestriction` — local quasi-coherence read on the
  sheaf-of-modules restriction and over the structure sheaf of the ambient scheme.
* `SmallSite.isQuasicoherent_moduleRestriction` — the same with Mathlib's quasi-coherence.
* `SmallSite.isZero_cohomology_restriction_of_isAffine` — the higher cohomology of the restriction
  `F_T` of a locally quasi-coherent module vanishes when `T` is affine.

## Implementation notes

Local quasi-coherence is not defined here: the predicate on the small crystalline site is
`Crystalline.GlobalCrystallineSituation.SmallSite.IsLocallyQuasiCoherent`, which is what carries
[Stacks, Tag 07IS] part (1), and this file consumes it.

Its definition states the restriction at the level of presheaves of modules and quantifies over
the Zariski sheaf condition on the ambient scheme as an existential.  That condition is no
restriction, and
`Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening.isSheaf_restriction`
proves it outright: the coverings of `Cris(X/S)` are the Zariski coverings of the ambient schemes,
so the restrictions of an object to the opens of its ambient scheme form a continuous functor to
`Cris(X/S)` and restriction along it carries sheaves to sheaves.  So the restriction is available
as a sheaf of modules with no hypothesis, which is `moduleRestriction`, and
`isQuasicoherentOnSite_moduleRestriction` discharges the existential of the definition against it;
that is the lemma a consumer of local quasi-coherence on the small site wants, in place of the
`∃ h` of the definition.

The restriction of a presheaf to the ambient scheme of an object, its module version and the
identification of the restricted structure sheaf all exist for the big crystalline site
(`Thickening.restriction`, `Thickening.moduleRestriction`, `Thickening.restrictionStructureIso`).
They are redone here for the small site rather than transported along the inclusion
`Cris(X/S) ⥤ CRIS(X/S)`, because the restrictions of an object of `Cris(X/S)` are again objects of
`Cris(X/S)` while a sheaf on the small site is not the restriction of one on the big site.  The
ring identification is assembled from `CrystallineThickening.sectionsIso`, which the structure
sheaf file already provides together with its naturality; it is the presheaf underlying
`Thickening.ringRestrictionSheafStructureIso` at the underlying object, which is the sheaf-level
isomorphism along which quasi-coherence is transported.

Two notions of quasi-coherence appear.  The definition of local quasi-coherence uses
`SheafOfModules.IsQuasicoherentOnSite`, the ringed-site form of [Stacks, Tag 03DL](6); Mathlib's
`SheafOfModules.IsQuasicoherent`, which the cohomology vanishing needs, is the one stated through
a global presentation on a family covering the final object.  On the Zariski site of a scheme the
two agree, the site being small relative to the universe of the sections, by
`SheafOfModules.isQuasicoherent_iff_isQuasicoherentOnSite`.

The cohomology of `F_T` is `Hgroup`, the right derived functor of the sections of an
`𝒪_T`-module over an open, and the vanishing is [Stacks, Tag 01XB].

## References

* [Stacks Project, Tag 07IS](https://stacks.math.columbia.edu/tag/07IS)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 07JJ](https://stacks.math.columbia.edu/tag/07JJ)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}}

namespace CrystallineThickening

/-- **The restriction of the structure sheaf of the small crystalline site to the ambient scheme
of an object is the structure sheaf of rings of that scheme.**  Over an open `W` the former is the
ring of global sections of the open subscheme `W`. -/
def ringRestrictionIso (A : CrystallineThickening S) :
    (restrictOpenFunctor A).op ⋙ crisRing S ≅
      A.obj.thickening.target.scheme.ringCatSheaf.obj :=
  NatIso.ofComponents (fun W ↦ sectionsIso A W.unop)
    (fun i ↦ sectionsIso_restrictOpenLE A (leOfHom i.unop))

/-- The restriction `F_T` of a sheaf of `𝒪_{X/S}`-modules to the ambient scheme of an object, as a
presheaf of `𝒪_T`-modules: its sections over an open `W` are the sections of `F` over the
restriction of the object to `W`. -/
def modulePresheafRestriction (A : CrystallineThickening S)
    (F : SheafOfModules.{u} (structureSheaf S)) :
    PresheafOfModules.{u} A.obj.thickening.target.scheme.ringCatSheaf.obj :=
  (PresheafOfModules.restrictScalars (ringRestrictionIso A).inv).obj
    ((PresheafOfModules.pushforward₀ (restrictOpenFunctor A) (crisRing S)).obj F.val)

/-- The underlying presheaf of abelian groups of `modulePresheafRestriction A F` is the
composite of `F` with the restriction of the object `A` to the opens of its ambient scheme. -/
@[simp]
theorem modulePresheafRestriction_presheaf (A : CrystallineThickening S)
    (F : SheafOfModules.{u} (structureSheaf S)) :
    (modulePresheafRestriction A F).presheaf =
      (restrictOpenFunctor A).op ⋙ F.val.presheaf := rfl

/-- **The restriction `F_T` of a sheaf of `𝒪_{X/S}`-modules to the ambient scheme of an object**,
read as a sheaf of `𝒪_T`-modules.  The Zariski sheaf condition on the ambient scheme is
`isSheaf_restriction`, the continuity of the restrictions of the object to the opens of its
ambient scheme. -/
def moduleRestriction (A : CrystallineThickening S)
    (F : SheafOfModules.{u} (structureSheaf S)) :
    A.obj.thickening.target.scheme.Modules :=
  ⟨modulePresheafRestriction A F, isSheaf_restriction A F.val.presheaf F.isSheaf⟩

end CrystallineThickening

/-- **Local quasi-coherence on the small crystalline site, read on the sheaf-of-modules
restriction.**  The definition of
`Crystalline.GlobalCrystallineSituation.SmallSite.IsLocallyQuasiCoherent` states the restriction
`F_T` at the level of presheaves of modules and quantifies over its Zariski sheaf condition; that
condition always holds, by
`Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening.isSheaf_restriction`, and
the sheaf of modules it produces is
`Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening.moduleRestriction` once
its scalars are read in the structure sheaf of the ambient scheme rather than in the restriction
of `𝒪_{X/S}`. -/
theorem isQuasicoherentOnSite_moduleRestriction
    {F : SheafOfModules.{u} (structureSheaf S)} (hF : IsLocallyQuasiCoherent F)
    (A : CrystallineThickening S) :
    (CrystallineThickening.moduleRestriction A F).IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_restrictScalars_of_isIso
    (Thickening.ringRestrictionSheafStructureIso A.obj).inv _ (hF A).choose_spec

/-- **The restriction `F_T` of a locally quasi-coherent sheaf of `𝒪_{X/S}`-modules to the ambient
scheme of an object is a quasi-coherent `𝒪_T`-module** in Mathlib's sense, the two notions of
quasi-coherence agreeing on the Zariski site of a scheme. -/
theorem isQuasicoherent_moduleRestriction
    {F : SheafOfModules.{u} (structureSheaf S)} (hF : IsLocallyQuasiCoherent F)
    (A : CrystallineThickening S) :
    (CrystallineThickening.moduleRestriction A F).IsQuasicoherent :=
  (isQuasicoherentOnSite_moduleRestriction hF A).isQuasicoherent

/-- **The higher cohomology of the restriction on an affine ambient scheme vanishes.**  For a
locally quasi-coherent `𝒪_{X/S}`-module `F` and an object `(U, T, δ)` of `Cris(X/S)` whose ambient
scheme `T` is affine, `H^p(T, F_T) = 0` for `p > 0`. -/
theorem isZero_cohomology_restriction_of_isAffine
    (F : SheafOfModules.{u} (structureSheaf S)) (hF : IsLocallyQuasiCoherent F)
    (A : CrystallineThickening S) [IsAffine A.obj.thickening.target.scheme]
    (p : ℕ) (hp : 0 < p) :
    IsZero (Hgroup A.obj.thickening.target.scheme.ringCatSheaf ⊤ p
      (CrystallineThickening.moduleRestriction A F)) :=
  have := isQuasicoherent_moduleRestriction hF A
  Stacks.Cohomology.AffineOpen.isZero_hgroup_of_isAffine _ _ p hp

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
