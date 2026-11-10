module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.Functor
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits

/-!
# Direct sums and colimits of associated modules

Stacks Lemma 06VE lists ten properties of the functor `𝓕 ↦ 𝓕^a` from the quasi-coherent
modules of a scheme `S` to the modules of its big `τ`-site.  Clauses (2) and (3) — that it
commutes with direct sums and with colimits — rest on two inputs, and this file supplies both
for `τ = fppf`.

The first input is that `𝓕 ↦ 𝓕^a` is a left adjoint: it is the pullback along the morphism of
ringed sites `((Sch/S)_fppf, 𝒪) → (S_Zar, 𝒪_S)`, whose right adjoint is restriction along the
inclusion of the small Zariski site, so it preserves every colimit.  That is Stacks 03DC,
already recorded as
`AlgebraicGeometry.BigFppfOver.preservesColimitsOfSize_associatedModule`.

The second input is that the colimits of the *source* category are the colimits of all
`𝒪_S`-modules.  Quasi-coherence on a scheme is closed under colimits — Schemes, Section 01LA,
in this library `Stacks.AlgebraicGeometry.QuasicoherentColimits.isClosedUnderColimitsOfShape`
— so the inclusion `QCoh(𝒪_S) ⥤ Mod(𝒪_S)` creates, and hence preserves, them.  Composing the
two functors gives the clause.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.associatedModuleQcoh`: the functor
  `QCoh(𝒪_S) ⥤ Mod((Sch/S)_fppf, 𝒪)` of Stacks 06VE, the associated-module functor restricted
  to the quasi-coherent modules of `S`.
* `AlgebraicGeometry.BigFppfOver.associatedModuleOfSheaf`: the associated-module functor with
  its source retyped, which is what the previous definition composes with.

## Main results

* `AlgebraicGeometry.BigFppfOver.preservesColimitsOfShape_isQuasicoherent_ι` and
  `AlgebraicGeometry.BigFppfOver.hasColimitsOfShape_isQuasicoherent`: the quasi-coherent
  modules of `S` have colimits and the inclusion into all `𝒪_S`-modules preserves them, which
  is the half of the clause that concerns the source category.
* `AlgebraicGeometry.BigFppfOver.preservesColimitsOfShape_associatedModuleQcoh` and
  `AlgebraicGeometry.BigFppfOver.preservesColimitsOfSize_associatedModuleQcoh`:
  **Stacks 06VE (3)** — `𝓕 ↦ 𝓕^a` commutes with colimits.
* `AlgebraicGeometry.BigFppfOver.preservesColimitsOfShape_discrete_associatedModuleQcoh`:
  **Stacks 06VE (2)** — it commutes with direct sums, the discrete case of clause (3).
* `AlgebraicGeometry.BigFppfOver.preservesColimitsOfSize_of_isoAssociatedModule`: the same
  conclusion for any functor isomorphic to the associated-module functor.  This is the shape
  in which Remark 03FH transfers clauses (2) and (3) to the sections description of
  Definition 03DU (3).

## Implementation notes

The per-shape statements leave the index category `K` in arbitrary universes and carry, as
hypotheses, the two colimit existence facts the argument consumes: colimits of shape `K` in the
modules over a commutative ring, which is what the closure of quasi-coherence on an affine is
proved from, and colimits of shape `K` in all `𝒪_S`-modules.  Both are automatic for
`K : Type u` with `Category.{u} K`, which is the instantiation made below.

`AlgebraicGeometry.BigFppfOver.associatedModule` is stated on
`AlgebraicGeometry.Scheme.Modules` while `CategoryTheory.ObjectProperty.ι` lands in
`SheafOfModules.{u} S.ringCatSheaf`.  The two carry definitionally equal but syntactically
different `CategoryTheory.Category` instances, and instance search, which matches only up to
reducible unfolding, does not identify them: the composite of the two functors elaborates, but
no colimit preservation of the second factor is then found for it.  Hence the retyping
`AlgebraicGeometry.BigFppfOver.associatedModuleOfSheaf`, across which the preservation is
transported once, by hand, in
`AlgebraicGeometry.BigFppfOver.preservesColimitsOfShape_associatedModuleOfSheaf`.

The size statement is `CategoryTheory.Limits.PreservesColimitsOfSize.{u, u}`, at the universe
of the site.  A bare `CategoryTheory.Limits.PreservesColimits` would bind the index universe to
the hom universe of the source category, which is unrelated to the universe of `S`; the
source's "commutes with colimits" means small colimits indexed at the size of the site, and
that is what the equal-universe spelling says.  This follows the convention already written
into this library for the analogous clause of Stacks 09JJ and used in
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.QuasicoherentTransfer`.

The declarations below are stated for `τ = fppf`, and that is a property of *these*
declarations, not of the clauses.  `AlgebraicGeometry.FibredSite.baseStructureSheaf`
(`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/StructureSheaf.lean:59`) supplies a
`CommRingCat`-valued structure sheaf on `AlgebraicGeometry.BigFppfOver.baseOverTopology B S hS τ`
for **every** `τ : SiteKind`, by restricting the fppf structure sheaf along
`AlgebraicGeometry.BigFppfOver.baseOverTopology_le_fppf`, so the category `Mod((Sch/S)_τ, 𝒪)`
*is* available for all five topologies and each clause can be stated.  **The functor is not
missing either**: `AlgebraicGeometry.BigFppfOver.structureMap` has the analogue
`AlgebraicGeometry.BigFppfOver.baseStructureMap`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/BaseRingedSite.lean:206`) at every `τ`,
and the pullback along it is `AlgebraicGeometry.BigFppfOver.baseAssociatedModule`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/BaseRingedSite.lean:232`), with
`baseAssociatedModule .fppf = associatedModule` by `rfl`.

**The inputs are not fppf-specific either, and clauses (2), (3), (4) are proved at every
`τ`** in
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.BaseAssociatedModuleColimits`,
as `AlgebraicGeometry.BigFppfOver.preservesColimitsOfShape_discrete_baseAssociatedModuleQcoh`,
`…preservesColimitsOfSize_baseAssociatedModuleQcoh` and
`…preservesFiniteColimits_baseAssociatedModuleQcoh`.  The adjunction, and with it cocontinuity
of `𝓕 ↦ 𝓕^a`, is `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleAdjunction` and
`AlgebraicGeometry.BigFppfOver.preservesColimitsOfSize_baseAssociatedModule`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/BaseRingedSite.lean:306` and `:317`),
both for every `τ : SiteKind`; the other input,
`AlgebraicGeometry.BigFppfOver.preservesColimitsOfShape_isQuasicoherent_ι` below, is about
`QCoh(𝒪_S)` alone.  (The coarser sites do carry a structure sheaf in this library, the
analogue of the functor is constructed there, and the two inputs just named are available at
every `τ`.)

The fppf statements are kept as they stand: they are what the rest of the development cites, and
at `τ = .fppf` they are the `τ`-general ones, `baseAssociatedModule` and `associatedModule`
agreeing by `rfl`.

The source's second functor, `QCoh(𝒪_S) ⥤ Mod(S_τ, 𝒪)` into the modules of a *small* site of
`S`, is a different construction and is not built here — but it is **not absent from the
library**.  At `τ = étale` it is `AlgebraicGeometry.SmallEtale.associatedModule`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleRingedSite.lean:417`), which
is Definition 03DU (4) at that `τ`, and clauses (2) and (3) for it are proved in
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.SmallEtaleAssociatedModuleColimits`.
03DU (4) defines that functor for `τ ∈ {Zariski, étale}`, and the Zariski half is in the library
too: `AlgebraicGeometry.SmallZariski.associatedModule`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallZariskiRingedSite.lean:180`), over
`AlgebraicGeometry.SmallZariski.structureSheaf`, the sheaf `T/S ↦ Γ(T, 𝒪_T)` of 03DU (2) at that
`τ`.  Clauses (2) and (3) of 06VE are not stated for it here, though its colimit preservation is
(`ibid.:202`).

`𝓕^a` is taken in the form of Remark 03FH, the pullback along the morphism of ringed sites.
Stacks Definition 03DU (3) instead *defines* `𝓕^a` by its sections,
`(f : T → S) ↦ Γ(T, f^* 𝓕)`, and Remark 03FH is the identification of the two descriptions.
That identification is not proved in this library, and clauses (2) and (3) do not need it: they
assert that the functor is cocontinuous, which is a property of the functor however it is
presented, and the pullback is the presentation Remark 03FH names.  The last result below is
nevertheless stated so that the identification, once available, transfers the two clauses to any
other construction of `𝓕^a` with no further mathematics — in particular to the sections
description, whose presheaf-level half is
`AlgebraicGeometry.BigFppfOver.sectionsPresheafOfModules`.

Quasi-coherence of `𝒪_S`-modules is Mathlib's `SheafOfModules.IsQuasicoherent` rather than this
library's `SheafOfModules.IsQuasicoherentOnSite`, because the closure of quasi-coherence under
colimits on a scheme is proved for the former.

## References

* [Stacks Project, Tag 06VE](https://stacks.math.columbia.edu/tag/06VE)
* [Stacks Project, Tag 03DC](https://stacks.math.columbia.edu/tag/03DC)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03FH](https://stacks.math.columbia.edu/tag/03FH)
* [Stacks Project, Tag 01LA](https://stacks.math.columbia.edu/tag/01LA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe uK vK u

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The associated-module functor, retyped so that its source carries the category instance of
`SheafOfModules.{u} S.ringCatSheaf`.

`AlgebraicGeometry.BigFppfOver.associatedModule` is stated on
`AlgebraicGeometry.Scheme.Modules`, whose `CategoryTheory.Category` instance is definitionally
equal to, but not syntactically the same as, the one on `SheafOfModules.{u} S.ringCatSheaf`,
which is where `CategoryTheory.ObjectProperty.ι` lands.  Instance search matches up to reducible
unfolding and does not identify the two, so the two factors of
`AlgebraicGeometry.BigFppfOver.associatedModuleQcoh` are composed at this retyping. -/
public noncomputable abbrev associatedModuleOfSheaf :
    SheafOfModules.{u} S.ringCatSheaf ⥤ SheafOfModules.{u} (structureSheaf B S hS) :=
  associatedModule B S hS

/-- The associated-module functor preserves colimits of shape `K`, recorded at the retyping
`AlgebraicGeometry.BigFppfOver.associatedModuleOfSheaf`.  Its proof is the instance
`AlgebraicGeometry.BigFppfOver.preservesColimitsOfSize_associatedModule`, which is Stacks 03DC
applied to the adjunction, transported across the two category instances by hand. -/
public theorem preservesColimitsOfShape_associatedModuleOfSheaf (K : Type uK)
    [Category.{vK} K] : PreservesColimitsOfShape K (associatedModuleOfSheaf B S hS) := by
  have h : PreservesColimitsOfShape K (associatedModule B S hS) := inferInstance
  exact h

/-- **The functor of Stacks 06VE** for `τ = fppf`: the associated-module functor `𝓕 ↦ 𝓕^a`
restricted to the quasi-coherent modules of `S`, as a functor
`QCoh(𝒪_S) ⥤ Mod((Sch/S)_fppf, 𝒪)`.

Here `𝓕^a` is the pullback along the morphism of ringed sites
`((Sch/S)_fppf, 𝒪) → (S_Zar, 𝒪_S)`, which is the description of Remark 03FH. -/
public noncomputable abbrev associatedModuleQcoh :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ⥤
      SheafOfModules.{u} (structureSheaf B S hS) :=
  (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι ⋙ associatedModuleOfSheaf B S hS

section Shape

variable (K : Type uK) [Category.{vK} K]
  [∀ R : CommRingCat.{u}, HasColimitsOfShape K (ModuleCat.{u} R)]
  [HasColimitsOfShape K (SheafOfModules.{u} S.ringCatSheaf)]

/-- Quasi-coherent `𝒪_S`-modules are closed under colimits of shape `K`. -/
private instance isClosedUnderColimitsOfShape_isQuasicoherent :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).IsClosedUnderColimitsOfShape K :=
  Stacks.AlgebraicGeometry.QuasicoherentColimits.isClosedUnderColimitsOfShape S

/-- Colimits of shape `K` of quasi-coherent `𝒪_S`-modules exist: they are the colimits of the
same diagram of all `𝒪_S`-modules, which is quasi-coherent again. -/
public theorem hasColimitsOfShape_isQuasicoherent :
    HasColimitsOfShape K
      (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory := by
  exact Limits.hasColimitsOfShape_of_closedUnderColimits K _

/-- The inclusion of the quasi-coherent modules of a scheme into all its modules preserves
colimits of shape `K`: quasi-coherence is closed under those colimits, so the inclusion creates
them, and a functor creating colimits that its target has preserves them.

This is the half of Stacks 06VE (2), (3) that concerns the source category, and it is the
content of Schemes, Section 01LA that the source cites. -/
public theorem preservesColimitsOfShape_isQuasicoherent_ι :
    PreservesColimitsOfShape K (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι := by
  have : CreatesColimitsOfShape K (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι :=
    Limits.createsColimitsOfShapeFullSubcategoryInclusion K _
  infer_instance

/-- **Stacks 06VE (3)**, one shape at a time.  The functor `𝓕 ↦ 𝓕^a` commutes with colimits of
shape `K`: it is the inclusion of the quasi-coherent modules, which preserves them, followed by
the associated-module functor, which is a left adjoint. -/
public theorem preservesColimitsOfShape_associatedModuleQcoh :
    PreservesColimitsOfShape K (associatedModuleQcoh B S hS) := by
  have := preservesColimitsOfShape_isQuasicoherent_ι S K
  have := preservesColimitsOfShape_associatedModuleOfSheaf B S hS K
  exact Limits.comp_preservesColimitsOfShape
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι (associatedModuleOfSheaf B S hS)

end Shape

/-- **Stacks 06VE (2).**  The functor `𝓕 ↦ 𝓕^a` commutes with direct sums: a direct sum is a
colimit over a discrete index category, so this is the discrete case of clause (3).

Stated for the **big fppf** site, which is what this declaration's functor is.  The base's
clause string "fppf only" is kept byte-identical (a base registration line is never rewritten);
read it as the scope of *this* declaration, not of the library, since the reason the previous
version gave for the restriction — that the clause's inputs were proved at fppf only — was
false: `AlgebraicGeometry.BigFppfOver.preservesColimitsOfSize_baseAssociatedModule`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/BaseRingedSite.lean:317`) is an
instance at every `τ : SiteKind`.  **The clause at every `τ` is
`AlgebraicGeometry.BigFppfOver.preservesColimitsOfShape_discrete_baseAssociatedModuleQcoh`**, in
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.BaseAssociatedModuleColimits`, of
which this is the `τ = .fppf` case.

The source's second functor, `QCoh(𝒪_S) ⥤ Mod(S_τ, 𝒪)` into a **small** site of `S`, is a
different construction, and **this clause holds for it too**, at `τ = étale`:
`AlgebraicGeometry.SmallEtale.preservesColimitsOfShape_discrete_associatedModuleQcoh`, over
`AlgebraicGeometry.SmallEtale.associatedModule`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleRingedSite.lean:417`).  An
earlier note here said "small site untreated"; that was true when written and is now false. -/
@[stacks 06VE "direct_sums, big site at τ = fppf only"]
public theorem preservesColimitsOfShape_discrete_associatedModuleQcoh (I : Type u) :
    PreservesColimitsOfShape (Discrete I) (associatedModuleQcoh B S hS) :=
  preservesColimitsOfShape_associatedModuleQcoh B S hS (Discrete I)

/-- **Stacks 06VE (3).**  The functor `𝓕 ↦ 𝓕^a` commutes with all colimits indexed at the size
of the site.

Stated for the big fppf site, as on
`AlgebraicGeometry.BigFppfOver.preservesColimitsOfShape_discrete_associatedModuleQcoh`, and for
the same reason: that is this declaration's functor.  The clause at every `τ` is
`AlgebraicGeometry.BigFppfOver.preservesColimitsOfSize_baseAssociatedModuleQcoh`, of which this
is the `τ = .fppf` case; the clause's inputs are not specific to fppf.

The small-site functor of the source statement is treated at `τ = étale`, where this clause is
`AlgebraicGeometry.SmallEtale.preservesColimitsOfSize_associatedModuleQcoh`.  The clause string
"fppf only" is kept byte-identical and reads as the scope of this declaration. -/
@[stacks 06VE "colimits, big site at τ = fppf only"]
public theorem preservesColimitsOfSize_associatedModuleQcoh :
    PreservesColimitsOfSize.{u, u} (associatedModuleQcoh B S hS) := by
  constructor
  intro K _
  exact preservesColimitsOfShape_associatedModuleQcoh B S hS K

/-- **Stacks 06VE (2), (3) for the sections description.**  Any functor out of the
quasi-coherent modules of `S` isomorphic to the associated-module functor commutes with direct
sums and with colimits.

Stacks Definition 03DU (3) describes `𝓕^a` by its sections and Remark 03FH identifies that
description with the pullback along the morphism of ringed sites; this is the form in which
that identification discharges clauses (2) and (3) for the sections description, the
isomorphism being its only input. -/
public theorem preservesColimitsOfSize_of_isoAssociatedModule
    (G : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ⥤
      SheafOfModules.{u} (structureSheaf B S hS))
    (e : G ≅ associatedModuleQcoh B S hS) :
    PreservesColimitsOfSize.{u, u} G := by
  have := preservesColimitsOfSize_associatedModuleQcoh B S hS
  exact preservesColimits_of_natIso e.symm

end AlgebraicGeometry.BigFppfOver

end
