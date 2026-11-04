module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksCore.Tactic.StacksAttribute

/-!
# The identity reading of `𝓕 ↦ 𝓕^a` on the small Zariski site

**Nothing here is registered against a Stacks tag, and that is deliberate.**  This file reads
the small Zariski site of `S` as the category of opens of the underlying space of `S` — the site
over which `AlgebraicGeometry.Scheme.ringCatSheaf` and hence `AlgebraicGeometry.Scheme.Modules`
are already taken — and offers for `𝓕 ↦ 𝓕^a` the pullback of sheaves of modules along the
*identity* morphism of ringed sites `(S_Zar, 𝒪_S) → (S_Zar, 𝒪_S)`.  Under that reading
`𝓕^a = 𝓕` (`AlgebraicGeometry.SmallZariski.associatedModuleIsoOfIdentity`,
`SheafOfModules.pullbackId`) and every statement below is the corresponding statement about the
identity functor: full faithfulness, in particular, is
`CategoryTheory.Functor.FullyFaithful.id` transported along that isomorphism.

**That is not Stacks 0GN7 at `τ = Zariski`, and it is not Definition 03DU (4) either.**  The
coefficient sheaf of Definition 03DU (2) at `τ = Zariski` is `T/S ↦ Γ(T, 𝒪_T)`, which is
`AlgebraicGeometry.SmallZariski.structureSheaf`; it is *isomorphic* to `𝒪_S` and not equal to
it, and the identification of the two sites is Tag 020X with Tag 03FG rather than a definition.
Reading the comparison as the strict identity therefore presupposes what the source proves, and
the resulting full-faithfulness statement is a tautology about `𝟭`.  The clause is stated and
proved over the functor the source names —
`AlgebraicGeometry.SmallZariski.associatedModule`, the pullback along the genuine comparison
`AlgebraicGeometry.SmallZariski.structureMap` — in
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiRealFullyFaithful`, and the
`0GN7`, `06VE (1)`, `03DU (4)` and `03DX (2)` attributes for `τ = Zariski` sit there.

What survives here is a correct and sometimes convenient *reading*: the identity-reading functor
and the isomorphisms identifying it with `𝟭`, which other files use to transport iso-invariant
properties.  Everything is named `*OfIdentity` so that the reading is visible at each use.

## Main definitions

* `AlgebraicGeometry.SmallZariski.associatedModuleOfIdentity`: the pullback of sheaves of modules
  along the identity morphism of ringed sites `(S_Zar, 𝒪_S) → (S_Zar, 𝒪_S)`.
* `AlgebraicGeometry.SmallZariski.restrictModuleOfIdentity`: its right adjoint, restriction along
  that morphism.
* `AlgebraicGeometry.SmallZariski.associatedModuleQcohOfIdentity`: it restricted to the
  quasi-coherent modules, `QCoh(𝒪_S) ⥤ Mod(S_Zar, 𝒪_S)`.

## Main results

* `AlgebraicGeometry.SmallZariski.associatedModuleIsoOfIdentity`: the identity-reading functor is
  the identity functor.
* `AlgebraicGeometry.SmallZariski.restrictAssociatedModuleIsoOfIdentity`: so is
  `f_*f^*`, at every `𝒪_S`-module.
* `AlgebraicGeometry.SmallZariski.fullyFaithfulAssociatedModuleQcohOfIdentity`, with its two
  halves `AlgebraicGeometry.SmallZariski.full_associatedModuleQcohOfIdentity` and
  `AlgebraicGeometry.SmallZariski.faithful_associatedModuleQcohOfIdentity`: the identity-reading
  functor is fully faithful on `QCoh(𝒪_S)`.  Untagged: see the second paragraph above.

## Implementation notes

The source category is spelled `SheafOfModules.{u} S.ringCatSheaf` rather than
`AlgebraicGeometry.Scheme.Modules` throughout, for the reason recorded on
`AlgebraicGeometry.BigFppfOver.associatedModuleOfSheaf`: the two carry definitionally equal but
syntactically different `CategoryTheory.Category` instances and instance search does not identify
them, while `CategoryTheory.ObjectProperty.ι` lands in the former.

## References

* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03FG](https://stacks.math.columbia.edu/tag/03FG)
* [Stacks Project, Tag 03FH](https://stacks.math.columbia.edu/tag/03FH)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.SmallZariski

variable (S : Scheme.{u})

/-- The structure sheaf `𝒪_S` of the ringed site `(S_Zar, 𝒪_S)`, which is
`AlgebraicGeometry.Scheme.ringCatSheaf` read at the site of opens of `S` rather than at
`TopCat.Sheaf`.

The two differ only in that `TopCat.Sheaf` is a `def` wrapping `CategoryTheory.Sheaf` with a
`deriving Category` instance of its own: instance search, which unfolds neither, then fails to
see `𝟙 𝒪_S` as a morphism of sheaves of rings on a site, and with it every instance the
pullback below needs. -/
public abbrev opensStructureSheaf : Sheaf (Opens.grothendieckTopology ↥S) RingCat.{u} :=
  S.ringCatSheaf

/-- The identity reading of `𝓕 ↦ 𝓕^a` on the small Zariski site of `S`: the pullback of sheaves
of modules along the *identity* morphism of ringed sites `(S_Zar, 𝒪_S) → (S_Zar, 𝒪_S)`.

**This is not Definition 03DU (4) and carries no `03DU` attribute.**  Clause (4) takes the
pullback along the comparison of Remark 03FH, whose coefficient sheaf is `T/S ↦ Γ(T, 𝒪_T)` —
isomorphic to `𝒪_S` but not equal to it — and that functor is
`AlgebraicGeometry.SmallZariski.associatedModule`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallZariskiRingedSite.lean:180`),
where the `03DU` attribute for `τ = Zariski` sits. -/
public noncomputable abbrev associatedModuleOfIdentity :
    SheafOfModules.{u} S.ringCatSheaf ⥤ SheafOfModules.{u} S.ringCatSheaf :=
  SheafOfModules.pullback.{u} (F := 𝟭 (Opens ↥S)) (𝟙 (opensStructureSheaf S))

/-- Restriction of a sheaf of modules along the identity morphism of ringed sites
`(S_Zar, 𝒪_S) → (S_Zar, 𝒪_S)`, the right adjoint of
`AlgebraicGeometry.SmallZariski.associatedModuleOfIdentity`. -/
public noncomputable abbrev restrictModuleOfIdentity :
    SheafOfModules.{u} S.ringCatSheaf ⥤ SheafOfModules.{u} S.ringCatSheaf :=
  SheafOfModules.pushforward.{u} (F := 𝟭 (Opens ↥S)) (𝟙 (opensStructureSheaf S))

/-- Restriction along the identity morphism of ringed sites is the identity functor of
`Mod(S_Zar, 𝒪_S)`. -/
public noncomputable def restrictModuleIsoOfIdentity : restrictModuleOfIdentity S ≅ 𝟭 _ :=
  SheafOfModules.pushforwardId.{u} (opensStructureSheaf S)

/-- The identity-reading functor is the identity functor of `Mod(S_Zar, 𝒪_S)`, the morphism of
ringed sites it is the pullback along being the identity.  This is the isomorphism along which
every statement below is transported, and the reason none of them is tagged. -/
public noncomputable def associatedModuleIsoOfIdentity : associatedModuleOfIdentity S ≅ 𝟭 _ :=
  SheafOfModules.pullbackId.{u} (opensStructureSheaf S)

/-- The identity-reading functor is fully faithful, on all of `Mod(S_Zar, 𝒪_S)`: it is
`CategoryTheory.Functor.FullyFaithful.id` read through
`AlgebraicGeometry.SmallZariski.associatedModuleIsoOfIdentity`. -/
public noncomputable def fullyFaithfulAssociatedModuleOfIdentity :
    (associatedModuleOfIdentity S).FullyFaithful :=
  (Functor.FullyFaithful.id _).ofIso (associatedModuleIsoOfIdentity S).symm

/-- The identity-reading functor is full. -/
public instance full_associatedModuleOfIdentity : (associatedModuleOfIdentity S).Full :=
  (fullyFaithfulAssociatedModuleOfIdentity S).full

/-- The identity-reading functor is faithful. -/
public instance faithful_associatedModuleOfIdentity : (associatedModuleOfIdentity S).Faithful :=
  (fullyFaithfulAssociatedModuleOfIdentity S).faithful

/-- `f_*f^*` is the identity functor for the identity reading, at every `𝒪_S`-module.  The
corresponding statement for the functor of Remark 03FH — where it is the unit of a genuine
adjunction being an isomorphism — is
`AlgebraicGeometry.SmallZariski.restrictAssociatedModuleIso`. -/
public noncomputable def restrictAssociatedModuleIsoOfIdentity :
    associatedModuleOfIdentity S ⋙ restrictModuleOfIdentity S ≅ 𝟭 _ :=
  Functor.isoWhiskerRight (associatedModuleIsoOfIdentity S) (restrictModuleOfIdentity S) ≪≫
    (restrictModuleOfIdentity S).leftUnitor ≪≫ restrictModuleIsoOfIdentity S

/-- The identity-reading functor restricted to the quasi-coherent modules of `S`, as a functor
`QCoh(𝒪_S) ⥤ Mod(S_Zar, 𝒪_S)`. -/
public noncomputable abbrev associatedModuleQcohOfIdentity :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ⥤
      SheafOfModules.{u} S.ringCatSheaf :=
  (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι ⋙ associatedModuleOfIdentity S

/-- The identity-reading functor is full on `QCoh(𝒪_S)`. -/
public instance full_associatedModuleQcohOfIdentity : (associatedModuleQcohOfIdentity S).Full :=
  inferInstance

/-- The identity-reading functor is faithful on `QCoh(𝒪_S)`. -/
public instance faithful_associatedModuleQcohOfIdentity :
    (associatedModuleQcohOfIdentity S).Faithful :=
  inferInstance

/-- The identity-reading functor `QCoh(𝒪_S) ⥤ Mod(S_Zar, 𝒪_S)` is fully faithful.

**No attribute sits here.**  This is `CategoryTheory.Functor.FullyFaithful.id` transported along
`AlgebraicGeometry.SmallZariski.associatedModuleIsoOfIdentity`, so as a statement about the
functor of Definition 03DU (4) it would be a tautology obtained by reading the comparison of
Remark 03FH as a strict identity; see the module documentation.  Stacks 0GN7 and clause (1) of
Stacks 06VE at `τ = Zariski` are registered on
`AlgebraicGeometry.SmallZariski.fullyFaithfulAssociatedModuleQcoh` in
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiRealFullyFaithful`, which
proves them for the pullback along the genuine comparison; together with
`AlgebraicGeometry.BigFppfOver.fullyFaithfulBaseAssociatedModuleQcoh` (the big site, every `τ`)
and `AlgebraicGeometry.SmallEtale.fullyFaithfulAssociatedModuleQcoh'` (the small site at
`τ = étale`) those are the covering set of 0GN7. -/
public noncomputable def fullyFaithfulAssociatedModuleQcohOfIdentity :
    (associatedModuleQcohOfIdentity S).FullyFaithful :=
  (SheafOfModules.isQuasicoherent S.ringCatSheaf).fullyFaithfulι.comp
    (fullyFaithfulAssociatedModuleOfIdentity S)

end AlgebraicGeometry.SmallZariski

end
