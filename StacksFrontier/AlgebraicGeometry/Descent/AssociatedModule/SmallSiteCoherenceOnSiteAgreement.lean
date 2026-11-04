module

public import StacksFrontier.AlgebraicGeometry.AffineOpensRestrictionFlat
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseRingedSite
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallSiteCoherenceAgreement
import StacksCore.Tactic.StacksAttribute

/-!
# Coherence in the sense of Modules on Sites across `𝓕 ↦ 𝓕^a` on `S_Zar` and `S_étale`

Descent, Lemma 05VG says that for a property `𝒫` of Modules on Sites, Definitions 03DE, 03DL
and 03ER, a quasi-coherent `𝒪_S`-module `𝓕` has `𝒫` if and only if `𝓕^a` has `𝒫` as an
`𝒪`-module.  For `𝒫` = "coherent", Definition 03DL (8), the source asserts this only for the
small sites `S_Zar` and `S_étale` of a locally Noetherian scheme `S`.  This file states that
clause with the **same** predicate on both sides: `𝓕` is coherent as a sheaf of modules on the
ringed site `(Opens(S), 𝒪_S)` in the sense of 03DL (8) if and only if `𝓕^a` is coherent in the
sense of 03DL (8) on `S_Zar`, respectively on `S_étale`.

## The route

Over a locally Noetherian scheme, 03DL (8) coherence of a quasi-coherent `𝒪_S`-module on the
ringed site of opens of `S` agrees with coherence of `𝓕` as an `𝒪_S`-module (Stacks 01BV), which
is `AlgebraicGeometry.Scheme.Modules.isCoherentOnSite_iff_isCoherent`.  Both directions go through
Stacks 01XZ, as in the source's proof of 05VG:

* coherence on the site contains finite type, and a quasi-coherent module of finite type over a
  locally Noetherian scheme is coherent (01XZ (2) ⟹ (1));
* a coherent `𝒪_S`-module is of finite presentation (01XZ (1) ⟹ (3)), and a module of finite
  presentation on a ringed site whose structure sheaf is 03DL (8)-coherent is 03DL (8)-coherent;
  the structure sheaf of `(Opens(S), 𝒪_S)` is 03DL (8)-coherent because the affine opens cover,
  their rings of sections are Noetherian and restriction between them is flat
  (`AlgebraicGeometry.Scheme.isCoherentOnSite_unit`).

Composing with the clause between 01BV coherence of `𝓕` and 03DL (8) coherence of `𝓕^a`
(`AlgebraicGeometry.SmallZariski.isCoherentOnSite_associatedModule_iff` and
`AlgebraicGeometry.SmallEtale.isCoherentOnSite_associatedModule_iff`) gives the statement.

## Main results

* `AlgebraicGeometry.Scheme.isCoherentOnSite_unit`: the structure sheaf of a locally Noetherian
  scheme is coherent in the sense of Modules on Sites, Definition 03DL (8).
* `AlgebraicGeometry.Scheme.Modules.isCoherentOnSite_iff_isCoherent`: for a quasi-coherent module
  on a locally Noetherian scheme, coherence in the sense of 03DL (8) is coherence in the sense of
  01BV.
* `AlgebraicGeometry.Scheme.Modules.isCoherentOnSite_iff_isCoherentOnSite_associatedModule`:
  **Descent, Lemma 05VG for `𝒫` = "coherent"**, at the comparison functors
  `AlgebraicGeometry.SmallZariski.associatedModule` and
  `AlgebraicGeometry.SmallEtale.associatedModule` of Descent, Proposition 03DX (2).

## References

* [Stacks Project, Tag 05VG](https://stacks.math.columbia.edu/tag/05VG)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 01BV](https://stacks.math.columbia.edu/tag/01BV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u})

/-- The affine opens contained in an open `W` of a scheme generate a covering sieve of `W` for the
Grothendieck topology of open covers: the affine opens form a basis of the topology. -/
theorem sieve_generate_isAffineOpen_mem_grothendieckTopology (W : S.Opens) :
    Sieve.generate (fun {V : S.Opens} (_ : V ⟶ W) ↦ IsAffineOpen V) ∈
      Opens.grothendieckTopology S W := by
  intro x hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open hx W.2
  exact ⟨V, homOfLE hVW, ⟨V, 𝟙 V, homOfLE hVW, hV, Category.id_comp _⟩, hxV⟩

/-- **The structure sheaf of a locally Noetherian scheme is coherent in the sense of Modules on
Sites, Definition 03DL (8)**, on the ringed site of opens of the scheme.

The finite-type clause is `PresheafOfModules.isFiniteType_unit`.  The relations clause is
`AlgebraicGeometry.RingedSite.isFiniteType_relations_unit` at the covering by affine opens: the
ring of sections over an affine open of a locally Noetherian scheme is Noetherian, and restriction
between affine opens is flat (`AlgebraicGeometry.IsAffineOpen.flat_presheaf_map`). -/
@[sga "6 I 3.6"]
theorem isCoherentOnSite_unit [IsLocallyNoetherian S] :
    SheafOfModules.IsCoherentOnSite (SheafOfModules.unit S.ringCatSheaf) where
  isFiniteType := PresheafOfModules.isFiniteType_unit _
  kernel_isFiniteType U n s :=
    RingedSite.isFiniteType_relations_unit S.zariskiRingedSite (fun V ↦ IsAffineOpen V)
      (GrothendieckTopology.exists_covering_factorThrough_of_generate _ _
        (sieve_generate_isAffineOpen_mem_grothendieckTopology S))
      (fun A hA ↦ IsLocallyNoetherian.component_noetherian ⟨A, hA⟩)
      (fun h hA hA' ↦ hA'.flat_presheaf_map hA (leOfHom h)) U n s

namespace Modules

variable {S}

/-- **On a locally Noetherian scheme, coherence of a quasi-coherent module in the sense of Modules
on Sites, Definition 03DL (8), is coherence in the sense of Stacks 01BV.**

Forward: a 03DL (8)-coherent module is of finite type, and a quasi-coherent module of finite type
over a locally Noetherian scheme is coherent (Stacks 01XZ).  Backward: a coherent module is of
finite presentation (Stacks 01XZ), and a module of finite presentation on a ringed site whose
structure sheaf is 03DL (8)-coherent is 03DL (8)-coherent; the structure sheaf is
`AlgebraicGeometry.Scheme.isCoherentOnSite_unit`. -/
theorem isCoherentOnSite_iff_isCoherent [IsLocallyNoetherian S] (𝓕 : S.Modules)
    [𝓕.IsQuasicoherent] :
    SheafOfModules.IsCoherentOnSite 𝓕 ↔ 𝓕.IsCoherent := by
  constructor
  · intro hm
    have : SheafOfModules.IsFiniteType 𝓕 :=
      SheafOfModules.isFiniteType_of_presheaf_isFiniteType _ hm.isFiniteType
    exact Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType
      𝓕
  · intro hc
    have : SheafOfModules.IsFinitePresentation
        (R := Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O) 𝓕 :=
      Stacks.AlgebraicGeometry.CoherentTFAE.isFinitePresentation_of_isCoherent' 𝓕
    exact Stacks.SheafOfModules.isCoherentOnSite_of_isFinitePresentation_of_unit
      S.zariskiRingedSite 𝓕 (isCoherentOnSite_unit S)

variable (Be : BigEtaleSite.{u}) (he : Be.Contains S) (Bz : BigZariskiSite.{u})
  (hz : Bz.Contains S)

/-- **Descent, Lemma 05VG, for the property "coherent" (Modules on Sites, Definition 03DL (8)).**
Let `S` be a locally Noetherian scheme and `𝓕` a quasi-coherent `𝒪_S`-module.  Then `𝓕` is
coherent if and only if `𝓕^a` is coherent as an `𝒪`-module, at the comparison functor
`𝓕 ↦ 𝓕^a` of Descent, Proposition 03DX (2) for `τ = Zariski`
(`AlgebraicGeometry.SmallZariski.associatedModule`, to `S_Zar`) and for `τ = étale`
(`AlgebraicGeometry.SmallEtale.associatedModule`, to `S_étale`).

"Coherent" is the one predicate `SheafOfModules.IsCoherentOnSite` of Definition 03DL (8) on both
sides: for `𝓕` on the ringed site `(Opens(S), 𝒪_S)`, for `𝓕^a` on `(S_Zar, 𝒪)` and on
`(S_étale, 𝒪)`.  On `𝓕` it agrees with coherence of `𝒪_S`-modules in the sense of Stacks 01BV by
`AlgebraicGeometry.Scheme.Modules.isCoherentOnSite_iff_isCoherent`.  These are exactly the sites,
and locally Noetherian is exactly the hypothesis, under which the source asserts the coherent
case. -/
@[stacks 05VG "coherent (03DL (8)) on both sides, S locally Noetherian: 𝓕 has 𝒫 on (Opens(S), 𝒪_S) \
⇔ 𝓕ᵃ has 𝒫 on S_Zar, and ⇔ 𝓕ᵃ has 𝒫 on S_étale, at the comparison functors of 03DX (2)"]
theorem isCoherentOnSite_iff_isCoherentOnSite_associatedModule [IsLocallyNoetherian S]
    (𝓕 : S.Modules) [𝓕.IsQuasicoherent] :
    (SheafOfModules.IsCoherentOnSite 𝓕 ↔
        SheafOfModules.IsCoherentOnSite ((SmallZariski.associatedModule Bz S hz).obj 𝓕)) ∧
      (SheafOfModules.IsCoherentOnSite 𝓕 ↔
        SheafOfModules.IsCoherentOnSite ((SmallEtale.associatedModule Be S he).obj 𝓕)) :=
  ⟨(isCoherentOnSite_iff_isCoherent 𝓕).trans
      (SmallZariski.isCoherentOnSite_associatedModule_iff Bz S hz 𝓕),
    (isCoherentOnSite_iff_isCoherent 𝓕).trans
      (SmallEtale.isCoherentOnSite_associatedModule_iff Be S he 𝓕)⟩

end Modules

end AlgebraicGeometry.Scheme

end
