module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiRealFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.BaseAssociatedModuleColimits
import StacksCore.Tactic.StacksAttribute

/-!
# Direct sums, colimits, right exactness and extensions for `𝓕 ↦ 𝓕^a` on the small Zariski site

Stacks 06VE states its ten clauses of the two functors `QCoh(𝒪_S) ⥤ Mod((Sch/S)_τ, 𝒪)` and
`QCoh(𝒪_S) ⥤ Mod(S_τ, 𝒪)`, `𝓕 ↦ 𝓕^a`, the second of which exists for `τ ∈ {Zariski, étale}`.
**This file proves clauses (2), (3), (4) and (10) for the second functor at `τ = Zariski`, over
the functor of Definition 03DU (4)** — `AlgebraicGeometry.SmallZariski.associatedModuleQcoh`, the
pullback of sheaves of modules along the morphism of ringed sites `(S_Zar, 𝒪) → (S_Zar, 𝒪_S)` of
Remark 03FH, whose coefficient sheaf is the sheaf `T/S ↦ Γ(T, 𝒪_T)` of Definition 03DU (2).

**Why this file exists.**
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiClosureProperties` already
carries these four clause strings at `τ = Zariski`, but over the *identity reading*
`AlgebraicGeometry.SmallZariski.associatedModuleQcohOfIdentity`: the pullback along the
**identity** morphism of ringed sites, which
`AlgebraicGeometry.SmallZariski.associatedModuleIsoOfIdentity` identifies with `𝟭`.  As the
module documentation of
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiFullyFaithful` records, that
reading presupposes the identification of the two structure sheaves which the source proves
(Tag 020X with Tag 03FG), so a clause proved of it is a statement about the identity functor and
not about `𝓕 ↦ 𝓕^a`.  That is the defect already retired for Stacks 0GN7, for clause (1) of
06VE, and for 03DU (4) and 03DX (2) at `τ = Zariski`, where the fix was to restate over the real
functor in
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiRealFullyFaithful`; this file
is the same fix for clauses (2), (3), (4) and (10), and the `06VE` attributes for them now sit
here.  The identity-reading statements are kept — other files transport iso-invariant properties
along them — but carry no tag.

**The proofs, and why they are not formal.**  At `τ = Zariski` the morphism of ringed sites of
Remark 03FH is an equivalence of ringed sites: its site half is the inverse of the open-image
comparison of Stacks 020X and its ring half
`AlgebraicGeometry.SmallZariski.structureMap` is an isomorphism
(`AlgebraicGeometry.SmallZariski.isIso_structureMap`), so `𝓕 ↦ 𝓕^a` is an equivalence
(`AlgebraicGeometry.SmallZariski.isEquivalence_associatedModule`) — a theorem about it, resting
on Stacks 03FG, and not its definition.  Each clause below is that theorem combined with the
corresponding fact about `QCoh(𝒪_S)`:

* clauses (2), (3): `𝓕 ↦ 𝓕^a` is a left adjoint, so it commutes with colimits (Stacks 03DC),
  and colimits of quasi-coherent modules on a scheme are their colimits as `𝒪_S`-modules
  (Schemes, Section 01LA), which is
  `AlgebraicGeometry.BigFppfOver.preservesColimitsOfShape_isQuasicoherent_ι`;
* clause (4): the same for finite colimits, the inclusion of `QCoh(𝒪_S)` being right exact
  because quasi-coherent modules are a weak Serre subcategory;
* clause (10): restriction along the morphism of ringed sites is an equivalence, hence exact, so
  it carries the given short exact sequence to a short exact sequence of `𝒪_S`-modules whose
  outer terms are quasi-coherent; the middle term is then quasi-coherent because quasi-coherence
  is closed under extensions (Schemes, Section 01LA again,
  `Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isClosedUnderExtensions`),
  and the counit of the adjunction exhibits it as an `𝓕^a`.

The source's proof of (10) takes two steps that are *not* needed at `τ = Zariski`: the vanishing
`H^1(U, 𝓕₁^a) = 0` on an affine `U` of Proposition 03DW and the universal injectivity of
`𝓕₁(U) → 𝓔(U)` tested against the `A`-algebras `A ⊕ M`.  Both are there to compare the
restriction `𝓔|_{S_Zar}` with `𝓔` itself, and at `τ = Zariski` that restriction is an equivalence
— which here is a theorem (Stacks 03FG), not a reading of the definitions.

## Main results

* `SmallZariski.preservesColimitsOfShape_discrete_associatedModuleQcohOfComparison`:
  **Stacks 06VE (2), small site at `τ = Zariski`** — `𝓕 ↦ 𝓕^a` commutes with direct sums.
* `AlgebraicGeometry.SmallZariski.preservesColimitsOfSize_associatedModuleQcohOfComparison`:
  **Stacks 06VE (3), small site at `τ = Zariski`** — it commutes with colimits.
* `AlgebraicGeometry.SmallZariski.preservesFiniteColimits_associatedModuleQcohOfComparison`:
  **Stacks 06VE (4), small site at `τ = Zariski`** — it is right exact.
* `AlgebraicGeometry.SmallZariski.essImage_associatedModuleQcohOfComparison_iff`: a module on
  `S_Zar` is in the essential image of `𝓕 ↦ 𝓕^a` exactly when its restriction is quasi-coherent.
* `AlgebraicGeometry.SmallZariski.essImage_X₂_of_shortExactOfComparison`:
  **Stacks 06VE (10), small site at `τ = Zariski`** — given a short exact sequence
  `0 → 𝓕₁^a → 𝓔 → 𝓕₂^a → 0` of `𝒪`-modules on `S_Zar`, the module `𝓔` is in the essential image
  of `𝓕 ↦ 𝓕^a`.

## Implementation notes

The names carry the suffix `OfComparison` — the functor being the pullback along the comparison
of Remark 03FH — because the plain names
`AlgebraicGeometry.SmallZariski.preservesColimitsOfShape_discrete_associatedModuleQcoh` and its
siblings are already taken, in
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiClosureProperties`, by the
identity-reading statements of the same clauses.  The functor itself is
`AlgebraicGeometry.SmallZariski.associatedModuleQcoh`, with no suffix.

Right exactness is not read off the size-indexed clause (3), for the reason recorded on
`AlgebraicGeometry.BigFppfOver.preservesFiniteColimits_baseAssociatedModuleQcoh`:
`CategoryTheory.Limits.PreservesFiniteColimits` quantifies over finite categories in `Type 0`
while clause (3) is stated at the universe of the scheme, and neither contains the other.

Clause (10) is stated with the short exact sequence as a
`CategoryTheory.ShortComplex.ShortExact` and with the two outer terms only *assumed* to be in the
essential image rather than presented as `𝓕₁^a` and `𝓕₂^a` for named `𝓕₁`, `𝓕₂`: that is the
same hypothesis, the essential image being by definition the objects isomorphic to some `𝓕^a`,
and it is the form the clause is consumed in — Stacks 0GNB (4) and 0GNC (4) know their outer
terms are quasi-coherent, not which quasi-coherent module they come from.

**What is not proved here.**  Clause (7) at `τ = Zariski` over this functor is *not* here: the
tensor product on `Mod(S_Zar, 𝒪)` is taken over `AlgebraicGeometry.SmallZariski.structureSheaf`
on the small Zariski site, and comparing it with the tensor product of `𝒪_S`-modules is
Stacks 03EL for the morphism of ringed topoi attached to Remark 03FH, which at `τ = Zariski` the
library does not yet have — the étale route is
`AlgebraicGeometry.SmallEtale.toZariskiRingedToposModulesHom`, built from
`AlgebraicGeometry.SmallEtale.toZariskiRingedSiteHom`, and the small Zariski site carries no
`AlgebraicGeometry.RingedSite.HomGeneral`.  Clause (8) at `τ = Zariski` is in the same position:
`AlgebraicGeometry.SmallZariski.associatedModuleSheafHomIso` proves it for the identity reading
only.  Clause (10) at `τ = étale` and on the big sites is *not* a consequence of this file:
there `𝓕 ↦ 𝓕^a` is not an equivalence and the restriction genuinely has to be compared with the
module itself, which is what the source's two steps do.

## References

* [Stacks Project, Tag 06VE](https://stacks.math.columbia.edu/tag/06VE)
* [Stacks Project, Tag 01LA](https://stacks.math.columbia.edu/tag/01LA)
* [Stacks Project, Tag 03DC](https://stacks.math.columbia.edu/tag/03DC)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03FG](https://stacks.math.columbia.edu/tag/03FG)
* [Stacks Project, Tag 03FH](https://stacks.math.columbia.edu/tag/03FH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe uK vK u

namespace AlgebraicGeometry.SmallZariski

variable (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Clauses (2), (3) and (4): direct sums, colimits, right exactness -/

/-- The associated-module functor of the small Zariski site preserves colimits of shape `K`,
recorded at the retyping `AlgebraicGeometry.SmallZariski.associatedModuleOfSheaf`.  Its proof is
the instance `AlgebraicGeometry.SmallZariski.preservesColimitsOfSize_associatedModule`, which is
Stacks 03DC applied to the adjunction of Remark 03FH, transported across the two category
instances by hand. -/
public theorem preservesColimitsOfShape_associatedModuleOfSheaf (K : Type uK)
    [Category.{vK} K] : PreservesColimitsOfShape K
      (AlgebraicGeometry.SmallZariski.associatedModuleOfSheaf B S hS) :=
  inferInstanceAs (PreservesColimitsOfShape K (associatedModule B S hS))

/-- The associated-module functor of the small Zariski site is right exact, at the retyping
`AlgebraicGeometry.SmallZariski.associatedModuleOfSheaf`: it is a left adjoint. -/
public theorem preservesFiniteColimits_associatedModuleOfSheaf :
    PreservesFiniteColimits (associatedModuleOfSheaf B S hS) :=
  inferInstanceAs (PreservesFiniteColimits (associatedModule B S hS))

section Shape

variable (K : Type uK) [Category.{vK} K]
  [∀ R : CommRingCat.{u}, HasColimitsOfShape K (ModuleCat.{u} R)]
  [HasColimitsOfShape K (SheafOfModules.{u} S.ringCatSheaf)]

/-- **Stacks 06VE (3) for the small site at `τ = Zariski`**, one shape at a time.  The functor
`QCoh(𝒪_S) ⥤ Mod(S_Zar, 𝒪)`, `𝓕 ↦ 𝓕^a` of Definition 03DU (4), commutes with colimits of shape
`K`: it is the inclusion of the quasi-coherent modules, which preserves them, followed by the
pullback along the morphism of ringed sites of Remark 03FH, which is a left adjoint.

The first factor is site-independent, so it is
`AlgebraicGeometry.BigFppfOver.preservesColimitsOfShape_isQuasicoherent_ι` unchanged — it is the
content of Schemes, Section 01LA that the source cites about `QCoh(𝒪_S)`, the common source of
both functors of 06VE. -/
public theorem preservesColimitsOfShape_associatedModuleQcohOfComparison :
    PreservesColimitsOfShape K
      (AlgebraicGeometry.SmallZariski.associatedModuleQcoh B S hS) := by
  have := BigFppfOver.preservesColimitsOfShape_isQuasicoherent_ι S K
  have := preservesColimitsOfShape_associatedModuleOfSheaf B S hS K
  exact Limits.comp_preservesColimitsOfShape
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι (associatedModuleOfSheaf B S hS)

end Shape

/-- **Stacks 06VE (2) for the small site at `τ = Zariski`.**  The functor
`QCoh(𝒪_S) ⥤ Mod(S_Zar, 𝒪)`, `𝓕 ↦ 𝓕^a` of Definition 03DU (4), commutes with direct sums: a
direct sum is a colimit over a discrete index category, so this is the discrete case of
clause (3).

Definition 03DU gives a small site only for `τ ∈ {Zariski, étale}`, so with
`AlgebraicGeometry.SmallEtale.preservesColimitsOfShape_discrete_associatedModuleQcoh` (the small
site at `τ = étale`) and
`AlgebraicGeometry.BigFppfOver.preservesColimitsOfShape_discrete_baseAssociatedModuleQcoh` (the
big site, every `τ`) this completes the covering set of the clause. -/
@[stacks 06VE "part (2), small site at τ = Zariski"]
public theorem preservesColimitsOfShape_discrete_associatedModuleQcohOfComparison (I : Type u) :
    PreservesColimitsOfShape (Discrete I)
      (AlgebraicGeometry.SmallZariski.associatedModuleQcoh B S hS) :=
  preservesColimitsOfShape_associatedModuleQcohOfComparison B S hS (Discrete I)

/-- **Stacks 06VE (3) for the small site at `τ = Zariski`.**  The functor
`QCoh(𝒪_S) ⥤ Mod(S_Zar, 𝒪)`, `𝓕 ↦ 𝓕^a` of Definition 03DU (4), commutes with all colimits
indexed at the size of the scheme.

Scope as on `preservesColimitsOfShape_discrete_associatedModuleQcohOfComparison`. -/
@[stacks 06VE "part (3), small site at τ = Zariski"]
public theorem preservesColimitsOfSize_associatedModuleQcohOfComparison :
    PreservesColimitsOfSize.{u, u}
      (AlgebraicGeometry.SmallZariski.associatedModuleQcoh B S hS) :=
  ⟨fun {K} _ => preservesColimitsOfShape_associatedModuleQcohOfComparison B S hS K⟩

/-- **Stacks 06VE (4) for the small site at `τ = Zariski`.**  The functor
`QCoh(𝒪_S) ⥤ Mod(S_Zar, 𝒪)`, `𝓕 ↦ 𝓕^a` of Definition 03DU (4), is right exact, i.e. commutes
with finite colimits.

As on the big site this is not read off clause (3) but assembled from the two factors, the
inclusion of the quasi-coherent modules being right exact because they are a weak Serre
subcategory. -/
@[stacks 06VE "part (4), small site at τ = Zariski"]
public theorem preservesFiniteColimits_associatedModuleQcohOfComparison :
    PreservesFiniteColimits
      (AlgebraicGeometry.SmallZariski.associatedModuleQcoh B S hS) := by
  have : PreservesFiniteColimits (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι :=
    ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass _
  have := preservesFiniteColimits_associatedModuleOfSheaf B S hS
  exact Limits.comp_preservesFiniteColimits
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι (associatedModuleOfSheaf B S hS)

/-! ### Clause (10): an extension of two associated modules is an associated module -/

/-- The adjunction of Remark 03FH at the retyping of
`AlgebraicGeometry.SmallZariski.associatedModuleOfSheaf` and
`AlgebraicGeometry.SmallZariski.restrictModuleOfSheaf`. -/
public noncomputable def associatedModuleAdjunctionOfSheaf :
    AlgebraicGeometry.SmallZariski.associatedModuleOfSheaf B S hS ⊣
      AlgebraicGeometry.SmallZariski.restrictModuleOfSheaf B S hS :=
  associatedModuleAdjunction B S hS

/-- Restriction along the morphism of ringed sites of Remark 03FH is exact at `τ = Zariski`,
being an equivalence: it preserves finite limits. -/
public theorem preservesFiniteLimits_restrictModuleOfSheaf :
    PreservesFiniteLimits (restrictModuleOfSheaf B S hS) :=
  have := Adjunction.isEquivalencePreservesLimits (restrictModuleOfSheaf B S hS)
  inferInstance

/-- Restriction along the morphism of ringed sites of Remark 03FH is exact at `τ = Zariski`,
being an equivalence: it preserves finite colimits. -/
public theorem preservesFiniteColimits_restrictModuleOfSheaf :
    PreservesFiniteColimits (restrictModuleOfSheaf B S hS) :=
  have := Adjunction.isEquivalence_preservesColimits (restrictModuleOfSheaf B S hS)
  inferInstance

/-- A module whose restriction along the morphism of ringed sites of Remark 03FH is
quasi-coherent is in the essential image of `𝓕 ↦ 𝓕^a`, by the counit of the adjunction. -/
private theorem essImage_associatedModuleQcohOfComparison_of_restrict
    (E : SheafOfModules.{u} (structureSheaf B S hS))
    (hE : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf)
      ((restrictModuleOfSheaf B S hS).obj E)) :
    (associatedModuleQcoh B S hS).essImage E :=
  ⟨⟨(restrictModuleOfSheaf B S hS).obj E, hE⟩,
    ⟨asIso ((associatedModuleAdjunctionOfSheaf B S hS).counit.app E)⟩⟩

/-- **The essential image of `𝓕 ↦ 𝓕^a` on the small Zariski site**: an `𝒪`-module on `S_Zar` is
`𝓕^a` for a quasi-coherent `𝒪_S`-module `𝓕` exactly when its restriction along the morphism of
ringed sites of Remark 03FH is quasi-coherent.

Both directions use that `𝓕 ↦ 𝓕^a` is an equivalence at `τ = Zariski`, Stacks 03FG: forwards,
the unit identifies the restriction of `𝓕^a` with `𝓕`; backwards, the counit exhibits a module as
the associated module of its own restriction.  This is the object-level form of Stacks 03DX (2)
at `τ = Zariski`, of which `AlgebraicGeometry.SmallZariski.essSurj_associatedModuleQcohOnSite` is
the version cut out by quasi-coherence on the site. -/
public theorem essImage_associatedModuleQcohOfComparison_iff
    (E : SheafOfModules.{u} (structureSheaf B S hS)) :
    (associatedModuleQcoh B S hS).essImage E ↔
      SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf)
        ((restrictModuleOfSheaf B S hS).obj E) := by
  constructor
  · rintro ⟨F, ⟨e⟩⟩
    exact (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
      (asIso ((associatedModuleAdjunctionOfSheaf B S hS).unit.app F.obj) ≪≫
        (restrictModuleOfSheaf B S hS).mapIso e) F.property
  · exact essImage_associatedModuleQcohOfComparison_of_restrict B S hS E

/-- **Stacks 06VE (10) for the small site at `τ = Zariski`.**  Given a short exact sequence
`0 → 𝓕₁^a → 𝓔 → 𝓕₂^a → 0` of `𝒪`-modules on the small Zariski site of `S`, with `𝓕₁` and `𝓕₂`
quasi-coherent on `S`, the module `𝓔` is itself in the essential image of `𝓕 ↦ 𝓕^a`.

Restriction along the morphism of ringed sites of Remark 03FH is an equivalence at `τ = Zariski`
(Stacks 03FG), hence exact, so it carries the sequence to a short exact sequence of
`𝒪_S`-modules; by `AlgebraicGeometry.SmallZariski.essImage_associatedModuleQcohOfComparison_iff`
its outer terms are quasi-coherent, so its middle term is too, quasi-coherent modules on a scheme
being closed under extensions (Schemes, Section 01LA).  The same lemma turns that back into
membership of the essential image.

The clause at `τ = étale` and on the big sites is a different statement and is not implied by
this one; see the implementation notes of this module. -/
@[stacks 06VE "part (10), small site at τ = Zariski"]
public theorem essImage_X₂_of_shortExactOfComparison
    {C : ShortComplex (SheafOfModules.{u} (structureSheaf B S hS))} (hC : C.ShortExact)
    (h₁ : (associatedModuleQcoh B S hS).essImage C.X₁)
    (h₃ : (associatedModuleQcoh B S hS).essImage C.X₃) :
    (associatedModuleQcoh B S hS).essImage C.X₂ := by
  have := preservesFiniteLimits_restrictModuleOfSheaf B S hS
  have := preservesFiniteColimits_restrictModuleOfSheaf B S hS
  have hC' : (C.map (restrictModuleOfSheaf B S hS)).ShortExact := hC.map_of_exact _
  rw [essImage_associatedModuleQcohOfComparison_iff] at h₁ h₃ ⊢
  exact ObjectProperty.prop_X₂_of_shortExact (SheafOfModules.isQuasicoherent S.ringCatSheaf) hC'
    h₁ h₃

/-- **The essential image of `𝓕 ↦ 𝓕^a` on the small Zariski site is the modules quasi-coherent
on the site**, which is Stacks 03DX (2) at `τ = Zariski` read as a statement about objects: the
two directions are Stacks 03DV (2),
`AlgebraicGeometry.SmallZariski.isQuasicoherentOnSite_associatedModule_of_isQuasicoherent`, and
`AlgebraicGeometry.SmallZariski.essSurj_associatedModuleQcohOnSite` — here spelled out from
`AlgebraicGeometry.SmallZariski.isQuasicoherent_restrictModule` and the counit, to stay in
`Mod(S_Zar, 𝒪)` rather than in the quasi-coherent subcategory. -/
public theorem essImage_associatedModuleQcohOfComparison_iff_isQuasicoherentOnSite
    (E : SheafOfModules.{u} (structureSheaf B S hS)) :
    (associatedModuleQcoh B S hS).essImage E ↔ E.IsQuasicoherentOnSite := by
  constructor
  · rintro ⟨F, ⟨e⟩⟩
    exact (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureSheaf B S hS)).prop_of_iso e
        (isQuasicoherentOnSite_associatedModule_of_isQuasicoherent B S hS F.obj F.property)
  · exact fun hE => essImage_associatedModuleQcohOfComparison_of_restrict B S hS E
      (isQuasicoherent_restrictModule B S hS E hE)

/-- **Stacks 06VE (10) for the small site at `τ = Zariski`, in the form the source states it**:
given a short exact sequence `0 → 𝓕₁ → 𝓕₂ → 𝓕₃ → 0` of `𝒪`-modules on the small Zariski site of
`S` whose outer terms are quasi-coherent, the middle term is quasi-coherent.

The source states clause (10) as "`𝓔` is quasi-coherent, i.e. `𝓔` is in the essential image of
the functor"; this is the first reading and
`AlgebraicGeometry.SmallZariski.essImage_X₂_of_shortExactOfComparison` is the second.  The two
agree by Stacks 03DX (2) at `τ = Zariski`,
`essImage_associatedModuleQcohOfComparison_iff_isQuasicoherentOnSite`. It is also the third case
of Stacks 0GNB (4) and 0GNC (4) at this site. -/
@[stacks 06VE "part (10), small site at τ = Zariski, as quasi-coherence on the site"]
public theorem isQuasicoherentOnSite_X₂_of_shortExactOfComparison
    {C : ShortComplex (SheafOfModules.{u} (structureSheaf B S hS))} (hC : C.ShortExact)
    (h₁ : C.X₁.IsQuasicoherentOnSite) (h₃ : C.X₃.IsQuasicoherentOnSite) :
    C.X₂.IsQuasicoherentOnSite :=
  (essImage_associatedModuleQcohOfComparison_iff_isQuasicoherentOnSite B S hS _).1
    (essImage_X₂_of_shortExactOfComparison B S hS hC
      ((essImage_associatedModuleQcohOfComparison_iff_isQuasicoherentOnSite B S hS _).2 h₁)
      ((essImage_associatedModuleQcohOfComparison_iff_isQuasicoherentOnSite B S hS _).2 h₃))

end AlgebraicGeometry.SmallZariski

end
