module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.UnitQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcHomSheafRefinement

/-!
# Full faithfulness of `𝓕 ↦ 𝓕^a` on each of the five big sites

Stacks 0GN7 says that for every `τ ∈ {Zariski, étale, smooth, syntomic, fppf}` the functor
`𝓕 ↦ 𝓕^a` of Definition 03DU is fully faithful, both as a functor
`QCoh(𝒪_S) → QCoh((Sch/S)_τ, 𝒪)` into the big site and as a functor
`QCoh(𝒪_S) → QCoh(S_τ, 𝒪)` into the small site.  This file proves the big-site half, for all
five `τ` at once and with no hypothesis.

Nothing in the argument is topology-specific.  The categorical half,
`CategoryTheory.Adjunction.full_comp_L_of_isIso_unit_app` and
`CategoryTheory.Adjunction.faithful_comp_L_of_mono_unit_app`, mentions no site; what has to be
re-derived at a general `τ` is that the unit of the associated-module adjunction of `(Sch/S)_τ`
is an isomorphism at a quasi-coherent module, and
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.UnitQuasicoherent` does that at
`τ = fppf` out of three inputs, each of which is now available at every `τ`:

* the `τ`-sheafification presentation of `𝓕^a`,
  `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleSheafificationIso`, and the
  `τ`-sheafification of the comparison being an isomorphism,
  `AlgebraicGeometry.BigFppfOver.isIso_baseSheafification_map_sectionsComparison` — Stacks 070S (1)
  at every `τ`;
* the map which pulls sections back, `AlgebraicGeometry.BigFppfOver.sectionsUnit`, which does not
  see the topology at all;
* the sheaf condition for the pullback-sections presheaf, Stacks 03DT.  This is the only place
  the topology is used and it goes the easy way: each of the five topologies is **coarser** than
  the fppf one (`AlgebraicGeometry.BigFppfOver.baseOverTopology_le_fppf`), so an fppf sheaf is a
  `τ`-sheaf, and the fppf sheaf condition is unconditional through
  `AlgebraicGeometry.fpqcDescentOfQuasicoherentHoms`.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleQcoh`: the functor of Stacks 0GN7 for the
  indicated big site, `QCoh(𝒪_S) ⥤ Mod((Sch/S)_τ, 𝒪)`.

## Main results

* `AlgebraicGeometry.BigFppfOver.isSheaf_sectionsPresheafOfModules_baseOverTopology`:
  **Stacks 03DT on each of the five big sites of `S`**, unconditionally.
* `AlgebraicGeometry.BigFppfOver.isIso_baseUnit_app`: **the unit of the associated-module
  adjunction of `(Sch/S)_τ` is an isomorphism at every quasi-coherent `𝒪_S`-module** — the
  hypothesis of `AlgebraicGeometry.BigFppfOver.isIso_baseUnit_app_of_isSheaf` discharged.
* `AlgebraicGeometry.BigFppfOver.baseUnitIsoOnQuasicoherent`: the same statement in the shape in
  which `AlgebraicGeometry.BigFppfOver.UnitIsoOnQuasicoherent` records the fppf case.
* `AlgebraicGeometry.BigFppfOver.fullyFaithfulBaseAssociatedModuleQcoh`, with its two halves
  `AlgebraicGeometry.BigFppfOver.full_baseAssociatedModuleQcoh` and
  `AlgebraicGeometry.BigFppfOver.faithful_baseAssociatedModuleQcoh`: **Stacks 0GN7 for the big
  site, at every `τ`** — which is also **clause (1) of Stacks 06VE** for the first of that
  lemma's two functors, whose target `Mod((Sch/S)_τ, 𝒪)` is the target here on the nose.

## Implementation notes

The `τ`-parametric unit argument is **not** here.  It lives next to the fppf one it replaced, in
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.UnitQuasicoherent`, as
`AlgebraicGeometry.BigFppfOver.isIso_baseUnit_app_of_isSheaf`, with
`AlgebraicGeometry.BigFppfOver.isIso_unit_app_of_isSheaf` now its `τ = fppf` instance — so the
repository holds one copy of that argument, not two.  Only the sheaf condition, which is what
needs `AlgebraicGeometry.fpqcDescentOfQuasicoherentHoms` and hence an import that
`UnitQuasicoherent` does not have, is discharged here.

The source category of the functor is spelled `SheafOfModules.{u} S.ringCatSheaf` rather than
`AlgebraicGeometry.Scheme.Modules`, through
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleOfSheaf`, for the reason recorded on
`AlgebraicGeometry.BigFppfOver.associatedModuleOfSheaf`: the two carry definitionally equal but
syntactically different `CategoryTheory.Category` instances and instance search does not identify
them, while `CategoryTheory.ObjectProperty.ι` lands in the former.

## References

* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
* [Stacks Project, Tag 06VE](https://stacks.math.columbia.edu/tag/06VE)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 03DT on each of the five big sites of `S`.**  The pullback-sections presheaf of
modules of a quasi-coherent module `F` on `S` is a sheaf for each of the five localized
topologies, with no hypothesis.

Each of the five topologies is coarser than the fppf one, so this is the fppf statement
`AlgebraicGeometry.BigFppfOver.isSheaf_sectionsPresheafOfModules` — whose hypothesis is
discharged by `AlgebraicGeometry.fpqcDescentOfQuasicoherentHoms` — read through
`CategoryTheory.Presheaf.IsSheaf.of_le`. -/
@[stacks 0DEW "clause (1) only: 𝓕ᵃ satisfies the sheaf condition for fppf and a fortiori \
étale coverings; 𝓕 on S_étale is the associated module of a quasi-coherent module on the \
scheme S, the source's first reduction"]
public theorem isSheaf_sectionsPresheafOfModules_baseOverTopology (τ : SiteKind)
    (F : S.Modules) [F.IsQuasicoherent] :
    Presheaf.IsSheaf (baseOverTopology B S hS τ)
      (sectionsPresheafOfModules B S hS F).presheaf :=
  (isSheaf_sectionsPresheafOfModules B S hS fpqcDescentOfQuasicoherentHoms F).of_le
    (baseOverTopology_le_fppf B S hS τ)

/-- **The unit of the associated-module adjunction of `(Sch/S)_τ` is an isomorphism at every
quasi-coherent `𝒪_S`-module**, with no hypothesis: the sheaf condition the previous statement
asks for is `AlgebraicGeometry.BigFppfOver.isSheaf_sectionsPresheafOfModules_baseOverTopology`. -/
public theorem isIso_baseUnit_app (τ : SiteKind) (F : S.Modules) [F.IsQuasicoherent] :
    IsIso ((baseAssociatedModuleAdjunction B S hS τ).unit.app F) :=
  isIso_baseUnit_app_of_isSheaf B S hS τ F
    (isSheaf_sectionsPresheafOfModules_baseOverTopology B S hS τ F)

/-- `AlgebraicGeometry.BigFppfOver.UnitIsoOnQuasicoherent` for the indicated big site, proved:
the unit `𝓕 ⟶ (𝓕^a)|_{S_Zar}` of the associated-module adjunction of `(Sch/S)_τ` is an
isomorphism at every quasi-coherent `𝒪_S`-module.  This is the shape the full-faithfulness
statements below consume. -/
public theorem baseUnitIsoOnQuasicoherent (τ : SiteKind) :
    ∀ M : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory,
      IsIso ((baseAssociatedModuleAdjunction B S hS τ).unit.app M.obj) := fun M => by
  have : M.obj.IsQuasicoherent := M.property
  exact isIso_baseUnit_app B S hS τ M.obj

/-- The associated-module functor of the indicated big site, retyped so that its source carries
the category instance of `SheafOfModules.{u} S.ringCatSheaf`, for the reason recorded on
`AlgebraicGeometry.BigFppfOver.associatedModuleOfSheaf`. -/
public noncomputable abbrev baseAssociatedModuleOfSheaf (τ : SiteKind) :
    SheafOfModules.{u} S.ringCatSheaf ⥤
      SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS τ) :=
  baseAssociatedModule B S hS τ

/-- **The functor of Stacks 0GN7 for the indicated big site**: the associated-module functor
`𝓕 ↦ 𝓕^a` restricted to the quasi-coherent modules of `S`, as a functor
`QCoh(𝒪_S) ⥤ Mod((Sch/S)_τ, 𝒪)`.

Here `𝓕^a` is the pullback along the morphism of ringed sites
`id_{τ,Zar} : ((Sch/S)_τ, 𝒪) → (S_Zar, 𝒪_S)`, which is the description of Remark 03FH; the fppf
case is `AlgebraicGeometry.BigFppfOver.associatedModuleQcoh`. -/
public noncomputable abbrev baseAssociatedModuleQcoh (τ : SiteKind) :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ⥤
      SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS τ) :=
  (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι ⋙ baseAssociatedModuleOfSheaf B S hS τ

/-- **Stacks 0GN7 for the big site, the fullness half**, at every `τ`. -/
public theorem full_baseAssociatedModuleQcoh (τ : SiteKind) :
    (baseAssociatedModuleQcoh B S hS τ).Full :=
  (baseAssociatedModuleAdjunction B S hS τ).full_comp_L_of_isIso_unit_app
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι (ObjectProperty.full_ι _)
    (baseUnitIsoOnQuasicoherent B S hS τ)

/-- **Stacks 0GN7 for the big site, the faithfulness half**, at every `τ` — of which only the
weaker statement that the unit is a monomorphism at the quasi-coherent modules is used. -/
public theorem faithful_baseAssociatedModuleQcoh (τ : SiteKind) :
    (baseAssociatedModuleQcoh B S hS τ).Faithful :=
  (baseAssociatedModuleAdjunction B S hS τ).faithful_comp_L_of_mono_unit_app
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι (ObjectProperty.faithful_ι _) fun M => by
      have := baseUnitIsoOnQuasicoherent B S hS τ M
      exact inferInstanceAs
        (Mono ((baseAssociatedModuleAdjunction B S hS τ).unit.app M.obj))

/-- **Stacks 0GN7 for the big site, and clause (1) of Stacks 06VE for it.**  For every
`τ ∈ {Zariski, étale, smooth, syntomic, fppf}` the functor `𝓕 ↦ 𝓕^a` of Definition 03DU, from
the quasi-coherent `𝒪_S`-modules to the `𝒪`-modules on the big site `(Sch/S)_τ`, is fully
faithful.

The two tags assert one thing of one functor, and the clause strings record the scope this
declaration proves — on **one source line**, because a tag registry that reads the attributes
matches a second `stacks` clause only when it is on the same line as the first, and two clause
strings plus the attribute syntax do not fit in a hundred characters unless both are short.  The
0GN7 string therefore no longer ends `; small site S_τ untreated`: that is information about
*where else the tag is registered*, not about the scope proved, and
`big site (Sch/S)_τ, every τ` already states the scope exactly.  The other registrations are
named in the last paragraph below.

06VE's first functor is `QCoh(𝒪_S) → Mod((Sch/S)_τ, 𝒪)`, whose target is
`Mod` — which is the target below on the nose, `SheafOfModules` over the structure sheaf of
`(Sch/S)_τ` — so clause (1) of 06VE needs no reading through a subcategory.  0GN7 spells the
same functor with target `QCoh((Sch/S)_τ, 𝒪)`, and that too is the same statement: full
faithfulness of a functor into a category is full faithfulness into any full subcategory
containing its image, and the image does land in `QCoh` by Stacks 03DV (1),
`AlgebraicGeometry.BigFppfOver.isQuasicoherentOnSite_baseAssociatedModule_of_isQuasicoherent`.

What is **not** claimed by either tag here is the source's second functor,
`QCoh(𝒪_S) → Mod(S_τ, 𝒪)` into the *small* site of `S` for `τ ∈ {Zariski, étale}` — a different
construction, Definition 03DU (4).  It is claimed elsewhere, and 0GN7 quantifies over nothing
beyond these: Definition 03DU gives a small site only at `τ ∈ {Zariski, étale}`, so this
declaration together with
`AlgebraicGeometry.SmallZariski.fullyFaithfulAssociatedModuleQcoh`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallZariskiRealFullyFaithful.lean`)
and `AlgebraicGeometry.SmallEtale.fullyFaithfulAssociatedModuleQcoh'`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleLocalBijectivity.lean`) is
every functor the lemma speaks of.  At `τ = Zariski` the *sections*-defined form of the functor
carries the tag too, as
`AlgebraicGeometry.SmallZariski.fullyFaithfulAssociatedSheafFunctor`.

(The small étale functor is `AlgebraicGeometry.SmallEtale.associatedModule`, in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleRingedSite.lean`, and its full
faithfulness rests on `AlgebraicGeometry.SmallEtale.unitIsoOnQuasicoherent` of
`SmallEtaleLocalBijectivity.lean`, which proves
`AlgebraicGeometry.SmallEtale.UnitIsoOnQuasicoherent` with no hypothesis.) -/
@[stacks 0GN7 "big site (Sch/S)_τ, every τ", stacks 06VE "part (1), big site, every τ"]
public noncomputable def fullyFaithfulBaseAssociatedModuleQcoh (τ : SiteKind) :
    (baseAssociatedModuleQcoh B S hS τ).FullyFaithful :=
  have := full_baseAssociatedModuleQcoh B S hS τ
  have := faithful_baseAssociatedModuleQcoh B S hS τ
  .ofFullyFaithful _

end BigFppfOver

end AlgebraicGeometry

end
