module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRingedSite
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.AssociatedModuleColimits

/-!
# Direct sums and colimits of associated modules on the small étale site

Stacks Lemma 06VE lists ten properties of **two** functors,
`QCoh(𝒪_S) ⥤ Mod((Sch/S)_τ, 𝒪)` and `QCoh(𝒪_S) ⥤ Mod(S_τ, 𝒪)`, both written `𝓕 ↦ 𝓕^a`.
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.AssociatedModuleColimits` proves
clauses (2) and (3) — commutation with direct sums and with colimits — for the first functor at
`τ = fppf`.  **This file proves the same two clauses for the second functor at `τ = étale`.**

The argument is the one the big site uses, with its two inputs supplied on the small site.

The first input is that `𝓕 ↦ 𝓕^a` is a left adjoint: on the small étale site it is the pullback
along the morphism of ringed sites `(S_étale, 𝒪) → (S_Zar, 𝒪_S)`, whose right adjoint is
restriction along the inclusion of the small Zariski site, so it preserves every colimit.  That
is Stacks 03DC, recorded as
`AlgebraicGeometry.SmallEtale.preservesColimitsOfSize_associatedModule`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleRingedSite.lean:440`).

The second input is about the *source* category, which is the same category for both functors of
the source statement, so it is reused verbatim:
`AlgebraicGeometry.BigFppfOver.preservesColimitsOfShape_isQuasicoherent_ι` depends on `S` alone
and not on any site, and is imported rather than restated.

## Main definitions

* `AlgebraicGeometry.SmallEtale.associatedModuleQcoh`: the **second functor of Stacks 06VE** at
  `τ = étale`, `QCoh(𝒪_S) ⥤ Mod(S_étale, 𝒪)`, the associated-module functor of the small étale
  site restricted to the quasi-coherent modules of `S`.
* `AlgebraicGeometry.SmallEtale.associatedModuleOfSheaf`: that functor's second factor with its
  source retyped, for the reason given in the implementation notes.

## Main results

* `AlgebraicGeometry.SmallEtale.preservesColimitsOfShape_associatedModuleQcoh` and
  `AlgebraicGeometry.SmallEtale.preservesColimitsOfSize_associatedModuleQcoh`:
  **Stacks 06VE (3) for the small site at `τ = étale`.**
* `AlgebraicGeometry.SmallEtale.preservesColimitsOfShape_discrete_associatedModuleQcoh`:
  **Stacks 06VE (2) for the small site at `τ = étale`** — commutation with direct sums, the
  discrete case of clause (3).
* `AlgebraicGeometry.SmallEtale.preservesColimitsOfSize_of_isoAssociatedModule`: the same
  conclusion for any functor isomorphic to the small étale associated-module functor, which is
  the shape in which the sections description of Definition 03DU (4) would inherit the two
  clauses.

## Implementation notes

`τ = étale` is the whole of the small-site content of 06VE proved here.  The second functor of
06VE is the one of Definition 03DU (4), which 03DU (4) itself defines for
`τ ∈ {Zariski, étale}` — 03DV (2) and 03DX (2) quantify the same way.  The Zariski half of each
is a separate statement about a functor that **is** in the library:
`AlgebraicGeometry.SmallZariski.associatedModule`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallZariskiRingedSite.lean:180`), over
`AlgebraicGeometry.SmallZariski.structureSheaf`, the sheaf `T/S ↦ Γ(T, 𝒪_T)` of 03DU (2) at that
`τ`.  So the cheap substitute — reading `S_Zar` as `S.Opens` with `S.ringCatSheaf` and offering
`𝟭 S.Modules`, which would state a different theorem, `T/S ↦ Γ(T, 𝒪_T)` being *isomorphic* to
`𝒪_S` and not equal to it — is not the only route open.  The clause of 06VE at
`τ = Zariski` is not proved here, but the colimit preservation it rests on is:
`AlgebraicGeometry.SmallZariski.preservesColimitsOfSize_associatedModule` (`ibid.:202`).  See the implementation notes of
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRingedSite`.

`AlgebraicGeometry.SmallEtale.associatedModule` is stated on
`AlgebraicGeometry.Scheme.Modules` while `CategoryTheory.ObjectProperty.ι` lands in
`SheafOfModules.{u} S.ringCatSheaf`.  The two carry definitionally equal but syntactically
different `CategoryTheory.Category` instances, and instance search, which matches only up to
reducible unfolding, does not identify them, so the composite elaborates but no colimit
preservation of its second factor is found for it.  Hence the retyping
`AlgebraicGeometry.SmallEtale.associatedModuleOfSheaf`, across which the preservation is
transported once, by hand, in
`AlgebraicGeometry.SmallEtale.preservesColimitsOfShape_associatedModuleOfSheaf`.  This is the
same friction, and the same remedy, as on the big site.

The size statement is `CategoryTheory.Limits.PreservesColimitsOfSize.{u, u}`, at the universe of
the scheme.  A bare `CategoryTheory.Limits.PreservesColimits` would bind the index universe to
the hom universe of the source category, which is unrelated to the universe of `S`; the source's
"commutes with colimits" means small colimits indexed at the size of the site, and that is what
the equal-universe spelling says.

Quasi-coherence of `𝒪_S`-modules is Mathlib's `SheafOfModules.IsQuasicoherent` rather than this
library's `SheafOfModules.IsQuasicoherentOnSite`, because the closure of quasi-coherence under
colimits on a scheme is proved for the former.

`𝓕^a` is taken in the form of Remark 03FH, the pullback along the morphism of ringed sites, and
not in the form of the sections formula `(f : T → S) ↦ Γ(T, f^*𝓕)` by which Definition 03DU (4)
names it.  Clauses (2) and (3) do not need the identification of the two: they assert that the
functor is cocontinuous, which is a property of the functor however it is presented.  The last
result below is stated so that the identification, once available for `S_étale` — its big-site
half is `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleIsoSections` — transfers the two
clauses to the sections description with no further mathematics.

## References

* [Stacks Project, Tag 06VE](https://stacks.math.columbia.edu/tag/06VE)
* [Stacks Project, Tag 03DC](https://stacks.math.columbia.edu/tag/03DC)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03FH](https://stacks.math.columbia.edu/tag/03FH)
* [Stacks Project, Tag 01LA](https://stacks.math.columbia.edu/tag/01LA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe uK vK u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The associated-module functor of the small étale site of `S`, retyped so that its source
carries the category instance of `SheafOfModules.{u} S.ringCatSheaf`.

`AlgebraicGeometry.SmallEtale.associatedModule` is stated on
`AlgebraicGeometry.Scheme.Modules`, whose `CategoryTheory.Category` instance is definitionally
equal to, but not syntactically the same as, the one on `SheafOfModules.{u} S.ringCatSheaf`,
which is where `CategoryTheory.ObjectProperty.ι` lands.  Instance search matches up to reducible
unfolding and does not identify the two, so the two factors of
`AlgebraicGeometry.SmallEtale.associatedModuleQcoh` are composed at this retyping. -/
public noncomputable abbrev associatedModuleOfSheaf :
    SheafOfModules.{u} S.ringCatSheaf ⥤ SheafOfModules.{u} (structureSheaf B S hS) :=
  associatedModule B S hS

/-- The associated-module functor of the small étale site preserves colimits of shape `K`,
recorded at the retyping `AlgebraicGeometry.SmallEtale.associatedModuleOfSheaf`.  Its proof is
the instance `AlgebraicGeometry.SmallEtale.preservesColimitsOfSize_associatedModule`, which is
Stacks 03DC applied to the adjunction, transported across the two category instances by hand. -/
public theorem preservesColimitsOfShape_associatedModuleOfSheaf (K : Type uK)
    [Category.{vK} K] : PreservesColimitsOfShape K (associatedModuleOfSheaf B S hS) := by
  have h : PreservesColimitsOfShape K (associatedModule B S hS) := inferInstance
  exact h

/-- **The second functor of Stacks 06VE**, at `τ = étale`: the associated-module functor
`𝓕 ↦ 𝓕^a` of the small étale site of `S` restricted to the quasi-coherent modules of `S`, as a
functor `QCoh(𝒪_S) ⥤ Mod(S_étale, 𝒪)`.

Here `𝓕^a` is the pullback along the morphism of ringed sites `(S_étale, 𝒪) → (S_Zar, 𝒪_S)`,
which is the description of Remark 03FH; the functor itself is Definition 03DU (4) at
`τ = étale`, `AlgebraicGeometry.SmallEtale.associatedModule`. -/
public noncomputable abbrev associatedModuleQcoh :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ⥤
      SheafOfModules.{u} (structureSheaf B S hS) :=
  (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι ⋙ associatedModuleOfSheaf B S hS

section Shape

variable (K : Type uK) [Category.{vK} K]
  [∀ R : CommRingCat.{u}, HasColimitsOfShape K (ModuleCat.{u} R)]
  [HasColimitsOfShape K (SheafOfModules.{u} S.ringCatSheaf)]

/-- **Stacks 06VE (3) for the small site at `τ = étale`**, one shape at a time.  The functor
`𝓕 ↦ 𝓕^a` into `Mod(S_étale, 𝒪)` commutes with colimits of shape `K`: it is the inclusion of the
quasi-coherent modules, which preserves them, followed by the associated-module functor of the
small étale site, which is a left adjoint.

The first factor is site-independent, so it is
`AlgebraicGeometry.BigFppfOver.preservesColimitsOfShape_isQuasicoherent_ι` unchanged — it is the
content of Schemes, Section 01LA that the source cites about `QCoh(𝒪_S)`, and `QCoh(𝒪_S)` is the
common source of both functors of 06VE. -/
public theorem preservesColimitsOfShape_associatedModuleQcoh :
    PreservesColimitsOfShape K (associatedModuleQcoh B S hS) := by
  have := BigFppfOver.preservesColimitsOfShape_isQuasicoherent_ι S K
  have := preservesColimitsOfShape_associatedModuleOfSheaf B S hS K
  exact Limits.comp_preservesColimitsOfShape
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι (associatedModuleOfSheaf B S hS)

end Shape

/-- **Stacks 06VE (2) for the small site at `τ = étale`.**  The functor
`QCoh(𝒪_S) ⥤ Mod(S_étale, 𝒪)`, `𝓕 ↦ 𝓕^a`, commutes with direct sums: a direct sum is a colimit
over a discrete index category, so this is the discrete case of clause (3).

The clause string records exactly the scope proved: the second functor of 06VE,
on the small site, at `τ = étale`.  The functor is the one of Definition 03DU (4), which is
defined for `τ ∈ {Zariski, étale}`; the Zariski half of this clause is a separate statement about
`AlgebraicGeometry.SmallZariski.associatedModule`, which exists — see the implementation notes
above.  The big-site half of the same clause is
`AlgebraicGeometry.BigFppfOver.preservesColimitsOfShape_discrete_associatedModuleQcoh`. -/
@[stacks 06VE "direct_sums, small site at τ = étale"]
public theorem preservesColimitsOfShape_discrete_associatedModuleQcoh (I : Type u) :
    PreservesColimitsOfShape (Discrete I) (associatedModuleQcoh B S hS) :=
  preservesColimitsOfShape_associatedModuleQcoh B S hS (Discrete I)

/-- **Stacks 06VE (3) for the small site at `τ = étale`.**  The functor
`QCoh(𝒪_S) ⥤ Mod(S_étale, 𝒪)`, `𝓕 ↦ 𝓕^a`, commutes with all colimits indexed at the size of the
scheme.

Scope as on
`AlgebraicGeometry.SmallEtale.preservesColimitsOfShape_discrete_associatedModuleQcoh`; the
big-site half is
`AlgebraicGeometry.BigFppfOver.preservesColimitsOfSize_associatedModuleQcoh`. -/
@[stacks 06VE "colimits, small site at τ = étale"]
public theorem preservesColimitsOfSize_associatedModuleQcoh :
    PreservesColimitsOfSize.{u, u} (associatedModuleQcoh B S hS) := by
  constructor
  intro K _
  exact preservesColimitsOfShape_associatedModuleQcoh B S hS K

/-- **Stacks 06VE (2), (3) on the small étale site for the sections description.**  Any functor
out of the quasi-coherent modules of `S` isomorphic to the small étale associated-module functor
commutes with direct sums and with colimits.

Stacks Definition 03DU (4) describes `𝓕^a` by its sections and Remark 03FH identifies that
description with the pullback along the morphism of ringed sites; this is the form in which that
identification, once available for `S_étale`, discharges clauses (2) and (3) for the sections
description, the isomorphism being its only input. -/
public theorem preservesColimitsOfSize_of_isoAssociatedModule
    (G : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ⥤
      SheafOfModules.{u} (structureSheaf B S hS))
    (e : G ≅ associatedModuleQcoh B S hS) :
    PreservesColimitsOfSize.{u, u} G := by
  have := preservesColimitsOfSize_associatedModuleQcoh B S hS
  exact preservesColimits_of_natIso e.symm

end AlgebraicGeometry.SmallEtale

end
