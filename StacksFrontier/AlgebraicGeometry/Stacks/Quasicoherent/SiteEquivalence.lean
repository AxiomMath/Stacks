module

public import Mathlib.Tactic.TFAE
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SiteComparison

/-!
# The three conditions of Stacks 0EM8, and the implications between them

Stacks 0EM8 says, for a category `𝒳` fibred in groupoids over the big fppf category of schemes
over `S` and a presheaf of modules `𝓕` on `𝒳`, that the three conditions

1. `𝓕` is an object of `Mod(𝒳_Zar, 𝒪_𝒳)` and is quasi-coherent on `(𝒳_Zar, 𝒪_𝒳)` in the sense
   of Modules on Sites, Definition 03DL,
2. `𝓕` is an object of `Mod(𝒳_ét, 𝒪_𝒳)` and is quasi-coherent on `(𝒳_ét, 𝒪_𝒳)` in the sense of
   Modules on Sites, Definition 03DL,
3. `𝓕` is a quasi-coherent module on `𝒳` in the sense of Definition 06WG, that is, on
   `(𝒳_fppf, 𝒪_𝒳)`,

are equivalent.  Each of the three carries **its own sheaf assertion**: clauses (1) and (2) ask
only that `𝓕` be a Zariski, respectively étale, sheaf.  This file states the three conditions as
one predicate `AlgebraicGeometry.FibredSite.IsQuasicoherentClause` indexed by the topology, and
proves every implication between them.

## Main definitions

* `AlgebraicGeometry.FibredSite.structureRingPresheaf`: the presheaf of rings underlying the
  coefficient sheaf of all five associated sites, which is one and the same presheaf.
* `AlgebraicGeometry.FibredSite.IsQuasicoherentClause`: the clause of Stacks 0EM8 at a
  `AlgebraicGeometry.SiteKind` — the sheaf condition for the inherited topology together with
  quasi-coherence of the resulting sheaf of modules in the sense of Stacks 03DL(6).
* `AlgebraicGeometry.FibredSite.IsSheafFppfOfQuasicoherentOnSite` and
  `AlgebraicGeometry.FibredSite.QuasicoherentOnSiteOfLeFppf`: the two inputs of Stacks 0EM8 that
  the library does not have, stated at the level of sheaves of modules.

## Main results

* `AlgebraicGeometry.FibredSite.isSheaf_of_isQuasicoherentClause_fppf`: clause (3) gives the
  sheaf condition of clauses (1) and (2), unconditionally.
* `AlgebraicGeometry.FibredSite.isQuasicoherentClause_fppf_of_isQuasicoherentClause`: clause (1),
  respectively (2), implies clause (3), over
  `AlgebraicGeometry.FibredSite.IsSheafFppfOfQuasicoherentOnSite`.
* `AlgebraicGeometry.FibredSite.isQuasicoherentClause_of_isQuasicoherentClause_fppf`: clause (3)
  implies clause (1), respectively (2), over
  `AlgebraicGeometry.FibredSite.QuasicoherentOnSiteOfLeFppf`.
* `AlgebraicGeometry.FibredSite.isQuasicoherentClause_of_isQuasicoherentClause`: clauses (1) and
  (2) imply one another, as the composites through clause (3).
* `AlgebraicGeometry.FibredSite.tfae_isQuasicoherentClause`: **the three-way equivalence of
  Stacks 0EM8** over the two inputs.
* `AlgebraicGeometry.FibredSite.isSheafFppfOfQuasicoherentOnSite_of_imp` and
  `AlgebraicGeometry.FibredSite.quasicoherentOnSiteOfLeFppf_of_imp`: each of the two inputs is
  *implied by* the implication of Stacks 0EM8 it buys, so neither is stronger than what the
  source statement asserts.

## The form in which Stacks 0EM8 is carried

`AlgebraicGeometry.FibredSite.tfae_isQuasicoherentClause` carries Stacks 0EM8 with the two
inputs above as explicit named hypotheses, one of each at the Zariski and at the étale topology:
`h₁z`/`h₁e` and `h₂z`/`h₂e`.  The `stacks` attribute on it records exactly that.  At `τ = .fppf`
both inputs are theorems here, `AlgebraicGeometry.FibredSite.isSheafFppfOfQuasicoherentOnSite_fppf`
and `AlgebraicGeometry.FibredSite.quasicoherentOnSiteOfLeFppf_fppf`, so what the equivalence
carries is precisely the Zariski and the étale instance of each and nothing more.  The two
inputs are stated as `abbrev`s, in the shapes the proofs below consume, so that each can be
struck from the signature with no change to any proof here as soon as it is discharged.

Both come from one place in the source, and neither is a weakness of the formalization.

`AlgebraicGeometry.FibredSite.IsSheafFppfOfQuasicoherentOnSite` is the passage from the sheaf
assertion of clause (1) or (2) to the one of clause (3).  The source gets it by restricting `𝓕`
to an object `x` of `𝒳` over a scheme `U`, where `𝒳_τ/x = (Sch/U)_τ`, identifying the
restriction with `𝓗^a` for a quasi-coherent `𝒪_U`-module `𝓗` — the essential-surjectivity half
of Descent, Proposition 03DX — and then invoking Descent, Lemma 03DT, which says `𝓗^a` is a
sheaf for the fppf topology as well.

`AlgebraicGeometry.FibredSite.QuasicoherentOnSiteOfLeFppf` is the converse of
`Stacks.SheafOfModules.isQuasicoherentOnSite_of_le`: quasi-coherence passing from the inherited
fppf topology to a coarser one.  A global presentation is a cokernel of a map between coproducts
of copies of the structure sheaf taken in the category of *sheaves* of modules, so it depends on
the topology; what carries a presentation from a coarser topology to a finer one is
sheafification, a left adjoint, and the inclusion in the other direction is a right adjoint and
carries no colimit.  The source again supplies this direction through Descent,
Proposition 03DX and Descent, Lemma 03DV.

So both inputs funnel into the essential-surjectivity half of Descent, Proposition 03DX, which
in turn rests on the effectivity half of Descent, Proposition 023T; the implementation notes of
`StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.Effective` and of
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.GlobalPresentationObstruction` record
that gap, the latter with the reason a global presentation cannot be produced over the base
itself.

That half is not available in this library, and the two `stacks` attributes for 03DX do
not supply it: they sit on
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite` and
`AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_isCartesianOnAffineCharts`, which state the
different criterion that quasi-coherence on the small étale site of an algebraic space is
equivalent to being cartesian on affine charts.  Essential surjectivity is carried instead as
`AlgebraicGeometry.BigFppfOver.QuasicoherentIsEssImageAssociatedModule`, at the big fppf site,
and as `AlgebraicGeometry.SmallEtale.QuasicoherentIsEssImageAssociatedModule`; every reduction
of it in this library terminates at
`AlgebraicGeometry.BigFppfOver.AssociatedModuleGlueDescentDatum`, which is the one open
assumption left.  What is unconditional is only the local step, that a module with a
presentation by free modules is an `𝓗^a`, together with full faithfulness.

Discharging the two inputs therefore needs more than that one assumption.  The source checks
quasi-coherence on `𝒳` after restricting to `𝒳/x` and reads `𝒳/x ≌ (Sch/U)_fppf`; the
implementation notes of
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.QuasicoherentAssembly` record that
the localization of Stacks 06WI and the invariance of quasi-coherence under an equivalence of
ringed sites are both present, while the identification of the *restricted structure sheaf* —
what turns them into a statement about `QCoh((Sch/U)_fppf, 𝒪)` — is not.  So each input is two
steps from unconditional, not one.

The two inputs are not over-assumptions:
`AlgebraicGeometry.FibredSite.isSheafFppfOfQuasicoherentOnSite_of_imp` and
`AlgebraicGeometry.FibredSite.quasicoherentOnSiteOfLeFppf_of_imp` recover each of them from the
implication of Stacks 0EM8 it is used for, so each is *equivalent* to that implication rather
than merely sufficient for it.

Clause (1) or (2) implies clause (3) *as soon as the fppf sheaf condition is known*, with no
further input: that is `AlgebraicGeometry.FibredSite.isQuasicoherentOnSite_of_siteRestriction`,
and it is what makes `AlgebraicGeometry.FibredSite.IsSheafFppfOfQuasicoherentOnSite` the whole
of the first input.  In the other direction the sheaf condition is free, the inherited
`τ`-topology being coarser than the inherited fppf one, which is
`AlgebraicGeometry.FibredSite.isSheaf_of_isQuasicoherentClause_fppf`.

The clauses are stated for a presheaf of modules over
`AlgebraicGeometry.FibredSite.structureRingPresheaf`, the presheaf of rings underlying
`AlgebraicGeometry.FibredSite.ringStructureSheafCore` at every one of the five topologies —
`AlgebraicGeometry.FibredSite.ringStructureSheafCore_obj` is an equality by `rfl` and does not
mention the `AlgebraicGeometry.SiteKind`.  So a single presheaf of modules is the subject of all
three clauses, and the clauses differ only in the sheaf condition asserted of it and in the
topology quasi-coherence is read for.

## References

* [Stacks Project, Tag 0EM8](https://stacks.math.columbia.edu/tag/0EM8)
* [Stacks Project, Tag 06WG](https://stacks.math.columbia.edu/tag/06WG)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)

/-- The presheaf of rings underlying the coefficient sheaf of rings of the associated sites of a
category fibred in groupoids.  All five associated topologies have the same underlying category
and the same structure presheaf, so this presheaf does not depend on the
`AlgebraicGeometry.SiteKind`; it is recorded at the inherited fppf topology. -/
public noncomputable abbrev structureRingPresheaf : 𝒳ᵒᵖ ⥤ RingCat.{u} :=
  (ringStructureSheafCore B S hS p hp .fppf).obj

/-- **A clause of Stacks 0EM8.**  A presheaf of modules `𝓕` on a category fibred in groupoids
satisfies the clause of Stacks 0EM8 at the topology `τ` when `𝓕` is a sheaf for the inherited
`τ`-topology — so that it is an object of `Mod(𝒳_τ, 𝒪_𝒳)` — and the resulting sheaf of modules
is quasi-coherent on `(𝒳_τ, 𝒪_𝒳)` in the sense of Stacks 03DL(6).

At `τ = .zariski` and `τ = .etale` this is clause (1), respectively (2), of Stacks 0EM8, and at
`τ = .fppf` it is clause (3), quasi-coherence of `𝓕` as a module on `𝒳` in the sense of
Stacks 06WG. -/
public def IsQuasicoherentClause (τ : SiteKind)
    (𝓕 : PresheafOfModules.{u} (structureRingPresheaf B S hS p hp)) : Prop :=
  ∃ h : Presheaf.IsSheaf (BigFppfOver.associatedTopology B S hS p τ) 𝓕.presheaf,
    SheafOfModules.IsQuasicoherentOnSite
      (⟨𝓕, h⟩ : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ))

/-- A presheaf of modules satisfying the clause of Stacks 0EM8 at `τ` is a sheaf for the
inherited `τ`-topology. -/
public theorem isSheaf_of_isQuasicoherentClause (τ : SiteKind)
    {𝓕 : PresheafOfModules.{u} (structureRingPresheaf B S hS p hp)}
    (h : IsQuasicoherentClause B S hS p hp τ 𝓕) :
    Presheaf.IsSheaf (BigFppfOver.associatedTopology B S hS p τ) 𝓕.presheaf :=
  h.elim fun h' _ => h'

/-- The sheaf assertion of clauses (1) and (2) of Stacks 0EM8 follows from clause (3) with no
further input: the inherited `τ`-topology is coarser than the inherited fppf topology, so a
sheaf for the latter is a sheaf for the former. -/
public theorem isSheaf_of_isQuasicoherentClause_fppf (τ : SiteKind)
    {𝓕 : PresheafOfModules.{u} (structureRingPresheaf B S hS p hp)}
    (h : IsQuasicoherentClause B S hS p hp .fppf 𝓕) :
    Presheaf.IsSheaf (BigFppfOver.associatedTopology B S hS p τ) 𝓕.presheaf :=
  (isSheaf_of_isQuasicoherentClause B S hS p hp .fppf h).of_le
    (BigFppfOver.associatedTopology_le_fppf B S hS p τ)

/-- **The first input of Stacks 0EM8 the library does not have.**  A sheaf of modules on the
associated `τ`-site of a category fibred in groupoids which is quasi-coherent on
`(𝒳_τ, 𝒪_𝒳)` in the sense of Stacks 03DL(6) is a sheaf for the inherited fppf topology.

This is the passage from the sheaf assertion of clause (1) or (2) of Stacks 0EM8 to the one of
clause (3); in the source it is the essential-surjectivity half of Descent,
Proposition 03DX followed by Descent, Lemma 03DT. -/
public abbrev IsSheafFppfOfQuasicoherentOnSite (τ : SiteKind) : Prop :=
  ∀ M : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ),
    M.IsQuasicoherentOnSite →
      Presheaf.IsSheaf (BigFppfOver.associatedTopology B S hS p .fppf) M.val.presheaf

/-- **The second input of Stacks 0EM8 the library does not have.**  A sheaf of modules on the
inherited fppf site of a category fibred in groupoids which is quasi-coherent there in the sense
of Stacks 03DL(6) stays quasi-coherent when read for a coarser associated topology.

This is the converse of `Stacks.SheafOfModules.isQuasicoherentOnSite_of_le`, and the direction
the comparison of topoi does not supply: a global presentation is carried from a coarser
topology to a finer one by sheafification, a left adjoint, while the inclusion in the other
direction is a right adjoint. -/
public abbrev QuasicoherentOnSiteOfLeFppf (τ : SiteKind) : Prop :=
  ∀ M : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf),
    M.IsQuasicoherentOnSite →
      ((Stacks.SheafOfModules.comparisonPushforward
        (BigFppfOver.associatedTopology_le_fppf B S hS p τ)
        (ringStructureSheafCore B S hS p hp .fppf)).obj M).IsQuasicoherentOnSite

/-- Both inputs are satisfied at `τ = .fppf`, where the two topologies coincide: the first is
the sheaf condition the module already carries. -/
public theorem isSheafFppfOfQuasicoherentOnSite_fppf :
    IsSheafFppfOfQuasicoherentOnSite B S hS p hp .fppf := fun M _ => M.isSheaf

/-- Both inputs are satisfied at `τ = .fppf`, where the two topologies coincide: the second is
quasi-coherence of the module itself, reading a module sheaf for its own topology changing
neither the module nor the coefficient sheaf of rings. -/
public theorem quasicoherentOnSiteOfLeFppf_fppf :
    QuasicoherentOnSiteOfLeFppf B S hS p hp .fppf := fun _ hM => hM

/-- **Clause (1) implies clause (3), and clause (2) implies clause (3), of Stacks 0EM8**, over
the first input.  The hypothesis supplies the fppf sheaf condition, and
`AlgebraicGeometry.FibredSite.isQuasicoherentOnSite_of_siteRestriction` then upgrades
quasi-coherence for the coarser topology to quasi-coherence on the inherited fppf site. -/
public theorem isQuasicoherentClause_fppf_of_isQuasicoherentClause (τ : SiteKind)
    (h₁ : IsSheafFppfOfQuasicoherentOnSite B S hS p hp τ)
    {𝓕 : PresheafOfModules.{u} (structureRingPresheaf B S hS p hp)}
    (h : IsQuasicoherentClause B S hS p hp τ 𝓕) :
    IsQuasicoherentClause B S hS p hp .fppf 𝓕 := by
  obtain ⟨hsh, hqc⟩ := h
  exact ⟨_, isQuasicoherentOnSite_of_siteRestriction B S hS p hp τ ⟨𝓕, h₁ ⟨𝓕, hsh⟩ hqc⟩ hqc⟩

/-- **Clause (3) implies clause (1), and clause (3) implies clause (2), of Stacks 0EM8**, over
the second input.  The sheaf condition is free, the inherited `τ`-topology being coarser than
the inherited fppf one; the hypothesis supplies quasi-coherence for the coarser topology. -/
public theorem isQuasicoherentClause_of_isQuasicoherentClause_fppf (τ : SiteKind)
    (h₂ : QuasicoherentOnSiteOfLeFppf B S hS p hp τ)
    {𝓕 : PresheafOfModules.{u} (structureRingPresheaf B S hS p hp)}
    (h : IsQuasicoherentClause B S hS p hp .fppf 𝓕) :
    IsQuasicoherentClause B S hS p hp τ 𝓕 := by
  obtain ⟨hsh, hqc⟩ := h
  exact ⟨isSheaf_of_isQuasicoherentClause_fppf B S hS p hp τ ⟨hsh, hqc⟩, h₂ ⟨𝓕, hsh⟩ hqc⟩

/-- **Clause (1) implies clause (2), and clause (2) implies clause (1), of Stacks 0EM8**: the
two composites through clause (3). -/
public theorem isQuasicoherentClause_of_isQuasicoherentClause (τ σ : SiteKind)
    (h₁ : IsSheafFppfOfQuasicoherentOnSite B S hS p hp τ)
    (h₂ : QuasicoherentOnSiteOfLeFppf B S hS p hp σ)
    {𝓕 : PresheafOfModules.{u} (structureRingPresheaf B S hS p hp)}
    (h : IsQuasicoherentClause B S hS p hp τ 𝓕) :
    IsQuasicoherentClause B S hS p hp σ 𝓕 :=
  isQuasicoherentClause_of_isQuasicoherentClause_fppf B S hS p hp σ h₂
    (isQuasicoherentClause_fppf_of_isQuasicoherentClause B S hS p hp τ h₁ h)

/-- **The three-way equivalence of Stacks 0EM8**, over its two inputs at the Zariski and the
étale topology: for a presheaf of modules on a category fibred in groupoids over the big fppf
category of schemes over `S`, being a quasi-coherent Zariski module, being a quasi-coherent
étale module, and being a quasi-coherent module on `𝒳` in the sense of Stacks 06WG are
equivalent. -/
@[stacks 0EM8 "the three-way equivalence, with the two inputs at each of the Zariski and the \
étale topology carried as explicit hypotheses: `h₁z`/`h₁e`, a `τ`-sheaf of modules that is \
quasi-coherent on `(𝒳_τ, 𝒪_𝒳)` is a sheaf for the inherited fppf topology, and `h₂z`/`h₂e`, \
quasi-coherence passes from the inherited fppf topology to a coarser one. At `τ = .fppf` both \
are discharged here. Neither is discharged at `τ = .zariski` or `τ = .etale`: both funnel into \
the essential-surjectivity half of Descent, Proposition 03DX, which this repository does not \
prove and carries as the hypothesis \
`AlgebraicGeometry.BigFppfOver.QuasicoherentIsEssImageAssociatedModule`, its only open \
reduction being `AlgebraicGeometry.BigFppfOver.AssociatedModuleGlueDescentDatum`; the two \
existing 03DX declarations state the different criterion that quasi-coherence on the small étale \
site of an algebraic space is equivalent to being cartesian on affine charts"]
public theorem tfae_isQuasicoherentClause
    (h₁z : IsSheafFppfOfQuasicoherentOnSite B S hS p hp .zariski)
    (h₁e : IsSheafFppfOfQuasicoherentOnSite B S hS p hp .etale)
    (h₂z : QuasicoherentOnSiteOfLeFppf B S hS p hp .zariski)
    (h₂e : QuasicoherentOnSiteOfLeFppf B S hS p hp .etale)
    (𝓕 : PresheafOfModules.{u} (structureRingPresheaf B S hS p hp)) :
    [IsQuasicoherentClause B S hS p hp .zariski 𝓕,
      IsQuasicoherentClause B S hS p hp .etale 𝓕,
      IsQuasicoherentClause B S hS p hp .fppf 𝓕].TFAE := by
  tfae_have 1 → 3 := isQuasicoherentClause_fppf_of_isQuasicoherentClause B S hS p hp _ h₁z
  tfae_have 2 → 3 := isQuasicoherentClause_fppf_of_isQuasicoherentClause B S hS p hp _ h₁e
  tfae_have 3 → 1 := isQuasicoherentClause_of_isQuasicoherentClause_fppf B S hS p hp _ h₂z
  tfae_have 3 → 2 := isQuasicoherentClause_of_isQuasicoherentClause_fppf B S hS p hp _ h₂e
  tfae_finish

/-- The first input of Stacks 0EM8 is *equivalent* to the implication it buys: if the clause of
Stacks 0EM8 at `τ` implies clause (3) for every presheaf of modules, then every `τ`-sheaf of
modules which is quasi-coherent on `(𝒳_τ, 𝒪_𝒳)` is a sheaf for the inherited fppf topology. -/
public theorem isSheafFppfOfQuasicoherentOnSite_of_imp (τ : SiteKind)
    (h : ∀ 𝓕 : PresheafOfModules.{u} (structureRingPresheaf B S hS p hp),
      IsQuasicoherentClause B S hS p hp τ 𝓕 → IsQuasicoherentClause B S hS p hp .fppf 𝓕) :
    IsSheafFppfOfQuasicoherentOnSite B S hS p hp τ := fun M hM =>
  isSheaf_of_isQuasicoherentClause B S hS p hp .fppf (h M.val ⟨M.isSheaf, hM⟩)

/-- The second input of Stacks 0EM8 is *equivalent* to the implication it buys: if clause (3) of
Stacks 0EM8 implies the clause at `τ` for every presheaf of modules, then quasi-coherence on the
inherited fppf site survives being read for the coarser topology `τ`. -/
public theorem quasicoherentOnSiteOfLeFppf_of_imp (τ : SiteKind)
    (h : ∀ 𝓕 : PresheafOfModules.{u} (structureRingPresheaf B S hS p hp),
      IsQuasicoherentClause B S hS p hp .fppf 𝓕 → IsQuasicoherentClause B S hS p hp τ 𝓕) :
    QuasicoherentOnSiteOfLeFppf B S hS p hp τ := fun M hM =>
  (h M.val ⟨M.isSheaf, hM⟩).elim fun _ hqc => hqc

end AlgebraicGeometry.FibredSite

end
