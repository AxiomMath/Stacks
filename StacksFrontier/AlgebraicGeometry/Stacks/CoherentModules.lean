module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherenceConditions
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentLocallyNoetherian

/-!
# Coherent modules on a locally Noetherian algebraic stack (Stacks 0GR6)

Let `𝒳` be a locally Noetherian algebraic stack.  Stacks 0GR6 calls an `𝒪_𝒳`-module *coherent*
when it satisfies one, and hence all, of the four equivalent conditions of Stacks 0GR5, and
writes `Coh(𝒪_𝒳)` for the category of coherent `𝒪_𝒳`-modules.  Coherence is defined here as the
conjunction of the two conditions of Stacks 0GR5 this library states, namely (1) that the module
be quasi-coherent of finite type and (2) that it be of finite presentation.

## Main definitions

* `AlgebraicGeometry.Stack.IsCoherent`: **Stacks 0GR6**, coherence of a module on the big fppf
  site of an algebraic stack.
* `AlgebraicGeometry.Stack.coherentModules` and `AlgebraicGeometry.Stack.Coh`: **Stacks 0GR6**,
  the category `Coh(𝒪_𝒳)` of coherent `𝒪_𝒳`-modules.

## Main results

* `AlgebraicGeometry.Stack.isCoherent_iff_isCoherentModule`: on a locally Noetherian algebraic
  stack coherence is exactly condition (2) of Stacks 0GR5, so the definition above agrees with
  `AlgebraicGeometry.Stack.IsCoherentModule`.
* `AlgebraicGeometry.Stack.IsCoherent.isQuasicoherentFiniteTypeModule` and
  `AlgebraicGeometry.Stack.IsCoherent.isFinitePresentationOnSite`: a coherent module satisfies
  each of the two conditions separately.
* `AlgebraicGeometry.Stack.isCoherent_unit` and
  `AlgebraicGeometry.Stack.isCoherent_of_isFiniteLocallyFreeOnSite`: the structure sheaf is
  coherent, as is every finite locally free module.

## Implementation notes

Conditions (3) and (4) of Stacks 0GR5 are not stated in this library, and of the source's
equivalence only the implication (2) ⟹ (1) is proved, at
`AlgebraicGeometry.Stack.isQuasicoherentFiniteTypeModule_of_isFinitePresentationOnSite`.  Taking
the conjunction of the two available conditions, rather than either one alone, makes the
definition independent of that choice; by the proved implication it is equivalent to condition
(2) alone, so it demands no more than the source does of a coherent module.  The converse
implication (1) ⟹ (2) is not available: the source obtains it only through conditions (3) and
(4), where local Noetherianity of `𝒳` is used.

Local Noetherianity is not a hypothesis of `IsCoherent` itself, which is a condition on a module
over the structure sheaf of an arbitrary algebraic stack, but an ambient hypothesis carried by
the results about it, as it is by Stacks 0GR5, 0GR7 and 0GR8 in this library.  It is
`AlgebraicGeometry.Stack.HasPropertyOnSomeSchemeAtlas` of Stacks 04YG taken at
`AlgebraicGeometry.IsLocallyNoetherian`.  The universe `m` of the module sections is free, as it
is for the two conditions.

No module on the site of an algebraic stack is shown here, or anywhere in this development, to
be *non*-coherent, so `IsCoherent` has no negative witness at the stack level.  What rules out
its being true of every module for want of content is one conjunct's worth of non-vacuity:
condition (2), `SheafOfModules.IsFinitePresentationOnSite`, fails for a concrete module on a
concrete ringed site, by
`Stacks.CoherentModulesWitness.not_isFinitePresentationOnSite_nodalPushforward` of
`StacksFrontier.AlgebraicGeometry.Stacks.CoherentModulesWitness`.  Carrying that witness onto a
stack is blocked by the comparison this library does not have, between modules on the big fppf
site of a scheme and modules on its small Zariski site: `AlgebraicGeometry.Stack.schemeStack` of
`StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack` is connected to nothing built out of
`AlgebraicGeometry.Stack.ringStructureSheafCore`, and every negative result in the tree —
`Stacks.NodalCurve.not_isFiniteType_pushforward_unit` of
`StacksFrontier.AlgebraicGeometry.PseudoCoherent.NodalPushforward`, and the `¬ ….IsCoherent` family
under `StacksDraft.AlgebraicGeometry.LocalCohomology.CodimensionOneObstruction` — is about
`AlgebraicGeometry.Scheme.Modules` on the Zariski site of a scheme.
`AlgebraicGeometry.Stack.not_isCoherent_of_not_isFiniteTypeOnSite` is the statement such a
comparison would be fed into.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 04YG](https://stacks.math.columbia.edu/tag/04YG)
* [Stacks Project, Tag 0GR5](https://stacks.math.columbia.edu/tag/0GR5)
* [Stacks Project, Tag 0GR6](https://stacks.math.columbia.edu/tag/0GR6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u m t

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0GR6.**  A module on the big fppf site of an algebraic stack `𝒳` is *coherent* when
it satisfies the conditions of Stacks 0GR5: it is quasi-coherent of finite type, condition (1),
and of finite presentation, condition (2). -/
@[stacks 0GR6 "coherence, as conditions (1) and (2) of Stacks 0GR5 jointly"]
def IsCoherent (𝒳 : AlgebraicStacks.{u, t} B S hS)
    (M : SheafOfModules.{m} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl)) : Prop :=
  IsQuasicoherentFiniteTypeModule B S hS 𝒳 M ∧ M.IsFinitePresentationOnSite

variable {B S hS}

/-- A coherent module is quasi-coherent of finite type, condition (1) of Stacks 0GR5. -/
theorem IsCoherent.isQuasicoherentFiniteTypeModule {𝒳 : AlgebraicStacks.{u, t} B S hS}
    {M : SheafOfModules.{m} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl)} (hM : IsCoherent B S hS 𝒳 M) :
    IsQuasicoherentFiniteTypeModule B S hS 𝒳 M :=
  hM.1

/-- A coherent module is of finite presentation, condition (2) of Stacks 0GR5. -/
theorem IsCoherent.isFinitePresentationOnSite {𝒳 : AlgebraicStacks.{u, t} B S hS}
    {M : SheafOfModules.{m} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl)} (hM : IsCoherent B S hS 𝒳 M) :
    M.IsFinitePresentationOnSite :=
  hM.2

variable (B S hS)

/-- On a locally Noetherian algebraic stack coherence is condition (2) of Stacks 0GR5 alone:
condition (2) implies condition (1) by
`AlgebraicGeometry.Stack.isQuasicoherentFiniteTypeModule_of_isFinitePresentationOnSite`, so
adjoining condition (1) to it is no restriction. -/
theorem isCoherent_iff_isCoherentModule (𝒳 : AlgebraicStacks.{u, t} B S hS)
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    (M : SheafOfModules.{m} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl)) :
    IsCoherent B S hS 𝒳 M ↔ IsCoherentModule B S hS 𝒳 M :=
  ⟨fun hM ↦ hM.2, fun hM ↦
    ⟨isQuasicoherentFiniteTypeModule_of_isFinitePresentationOnSite B S hS 𝒳 h𝒳 M hM, hM⟩⟩

/-- **Stacks 0GR6.**  The category `Coh(𝒪_𝒳)` of coherent modules on an algebraic stack `𝒳`: the
full subcategory of the `𝒪_𝒳`-modules on the big fppf site of `𝒳` cut out by
`AlgebraicGeometry.Stack.IsCoherent`. -/
@[stacks 0GR6 "the category Coh(O_X) of coherent modules"]
def coherentModules (𝒳 : AlgebraicStacks.{u, t} B S hS) :
    ObjectProperty (SheafOfModules.{m} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl)) :=
  fun M ↦ IsCoherent B S hS 𝒳 M

/-- The category `Coh(𝒪_𝒳)` of coherent `𝒪_𝒳`-modules. -/
abbrev Coh (𝒳 : AlgebraicStacks.{u, t} B S hS) :=
  (coherentModules.{u, m, t} B S hS 𝒳).FullSubcategory

/-- An object of `Coh(𝒪_𝒳)` is coherent. -/
theorem IsCoherent.of_mem_coh {𝒳 : AlgebraicStacks.{u, t} B S hS}
    (M : Coh.{u, m, t} B S hS 𝒳) : IsCoherent B S hS 𝒳 M.obj :=
  M.property

/-- **The structure sheaf of a locally Noetherian algebraic stack is coherent.**  It is of finite
presentation, being the coproduct of a single copy of itself, and condition (2) of Stacks 0GR5
implies condition (1). -/
theorem isCoherent_unit (𝒳 : AlgebraicStacks.{u, t} B S hS)
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳) :
    IsCoherent B S hS 𝒳 (SheafOfModules.unit _) :=
  (isCoherent_iff_isCoherentModule B S hS 𝒳 h𝒳 _).mpr (isCoherentModule_unit B S hS 𝒳 h𝒳)

/-- **Every finite locally free module on a locally Noetherian algebraic stack is coherent.**  The
covering witnessing finite local freeness carries a finite global presentation on each member,
and condition (2) of Stacks 0GR5 implies condition (1). -/
theorem isCoherent_of_isFiniteLocallyFreeOnSite (𝒳 : AlgebraicStacks.{u, t} B S hS)
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    (M : SheafOfModules.{m} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl))
    (hM : M.IsFiniteLocallyFreeOnSite) :
    IsCoherent B S hS 𝒳 M :=
  (isCoherent_iff_isCoherentModule B S hS 𝒳 h𝒳 M).mpr
    (isCoherentModule_of_isFiniteLocallyFreeOnSite B S hS 𝒳 h𝒳 M hM)

end AlgebraicGeometry.Stack

end
