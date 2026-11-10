module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiRealClosureProperties
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiSectionsIso

/-!
# Tags 03DV (2), 03DX (2) and 06VE at `τ = Zariski`, for the sections-defined `𝓕ᵃ`

[Stacks, Tag 03DU] (4) defines `𝓕ᵃ` **by its sections**: over an object `f : T → S` of the small
site its sections are `Γ(T, f^*𝓕)`.  On the small Zariski site of `S` that sheaf is
`AlgebraicGeometry.SmallZariski.associatedModuleOfSections` and that functor is
`AlgebraicGeometry.SmallZariski.associatedSheafFunctor`.  What the development calls
`AlgebraicGeometry.SmallZariski.associatedModule` is a different construction — the pullback of
sheaves of modules along the morphism of ringed sites `(S_Zar, 𝒪) → (S_Zar, 𝒪_S)` of
[Stacks, Remark 03FH] — and as the faithfulness note of
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.Functor` records, **every statement of
Tags 03DV, 0GN7, 03DX and 06VE is about the sections description**, so each of them reads through
the identification of the two.  At `τ = Zariski` that identification is
`AlgebraicGeometry.SmallZariski.associatedModuleIsoOfSections`, with the functor-level form
`AlgebraicGeometry.SmallZariski.associatedModuleQcohIsoAssociatedSheafFunctor`; **this file
carries the clauses across it**, so that each is registered on a statement about the object the
source names.

The pullback-form statements stay where they are and keep their own content — at `τ = Zariski`
the comparison is an equivalence of ringed sites, which is what makes them provable at all — and
nothing here replaces them; `associatedModuleQcohIsoAssociatedSheafFunctor` is what turns each
into the clause.

## What is transported, and what needed no transport

Transported here: 03DV (2); 03DX (2), in both the "the functor is an equivalence" and the
"there is an equivalence of categories" forms the source offers; and 06VE (2), (3), (4), (10).
Each is a property of the functor, or of its value at a module, that an isomorphism of functors
carries across, so each proof is one application of the isomorphism to the pullback-form
statement.

Clause (1) of 06VE — full faithfulness — needed no file of its own: it is the same assertion as
[Stacks, Tag 0GN7], already proved for the sections-defined functor by
`AlgebraicGeometry.SmallZariski.fullyFaithfulAssociatedSheafFunctor`, which now carries both
attributes, exactly as `AlgebraicGeometry.SmallZariski.fullyFaithfulAssociatedModuleQcoh` carries
both for the pullback-defined one.

`AlgebraicGeometry.SmallZariski.isQuasicoherentOnSite_X₂_of_shortExactOfComparison` — clause (10)
in the form the source states it, "`𝓔` is quasi-coherent" — needed no transport either, and that
is not an accident of its proof: its *statement* names no functor at all, being about short exact
sequences of `𝒪`-modules on `S_Zar` and the quasi-coherence of [Stacks, Tag 03DL] (6).  A
statement that does not mention `𝓕ᵃ` cannot be about the wrong `𝓕ᵃ`.

## The `*OfIdentity` reading is not involved

A third reading of `𝓕 ↦ 𝓕ᵃ` on the small Zariski site — the pullback along the *identity*
morphism of ringed sites, which
`AlgebraicGeometry.SmallZariski.associatedModuleIsoOfIdentity` identifies with `𝟭` — lives in
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiFullyFaithful` and
`StacksDraft.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiEquivalence` under names
suffixed `OfIdentity`.  Every tag resting on it has already been retired; nothing in this cluster
is registered on it, and nothing here uses it.

## Main definitions

* `AlgebraicGeometry.SmallZariski.associatedSheafFunctorOnSite`: the sections-defined
  `𝓕 ↦ 𝓕ᵃ` corestricted to `QCoh(S_Zar, 𝒪)`, which is the functor [Stacks, Tag 03DX] (2) asserts
  to be an equivalence.
* `AlgebraicGeometry.SmallZariski.associatedModuleQcohOnSiteIsoAssociatedSheafFunctorOnSite`: the
  identification of the two readings, corestricted.
* `AlgebraicGeometry.SmallZariski.associatedSheafFunctorEquivalence`: **[Stacks, Tag 03DX] (2) at
  `τ = Zariski` for the sections-defined functor**, as an equivalence of categories.

## Main results

* `AlgebraicGeometry.SmallZariski.isQuasicoherentOnSite_associatedModuleOfSections`:
  **[Stacks, Tag 03DV] (2) at `τ = Zariski` for the sections-defined `𝓕ᵃ`.**
* `AlgebraicGeometry.SmallZariski.isEquivalence_associatedSheafFunctorOnSite`:
  **[Stacks, Tag 03DX] (2) at `τ = Zariski` for the sections-defined functor.**
* `AlgebraicGeometry.SmallZariski.preservesColimitsOfShape_discrete_associatedSheafFunctor`,
  `AlgebraicGeometry.SmallZariski.preservesColimitsOfSize_associatedSheafFunctor` and
  `AlgebraicGeometry.SmallZariski.preservesFiniteColimits_associatedSheafFunctor`:
  **[Stacks, Tag 06VE] (2), (3) and (4) at `τ = Zariski` for the sections-defined functor.**
* `AlgebraicGeometry.SmallZariski.essImage_X₂_of_shortExact_associatedSheafFunctor`:
  **[Stacks, Tag 06VE] (10) at `τ = Zariski` for the sections-defined functor.**

## Implementation notes

`AlgebraicGeometry.SmallZariski.essImage_associatedSheafFunctor_iff` is proved by hand from the
components of the isomorphism of functors rather than from a transport lemma for
`CategoryTheory.Functor.essImage`: membership of the essential image is `∃ 𝓕, Nonempty (…)`, and
composing the given isomorphism with the component at the witness is the whole argument in both
directions.

Clause (3) is stated at `PreservesColimitsOfSize.{u, u}` and clause (4) at
`CategoryTheory.Limits.PreservesFiniteColimits` separately, rather than the second being read off
the first, for the reason recorded on
`AlgebraicGeometry.SmallZariski.preservesFiniteColimits_associatedModuleQcohOfComparison`:
`PreservesFiniteColimits` quantifies over finite categories in `Type 0` while clause (3) is
stated at the universe of the scheme, and neither contains the other.

Clause (2) of 03DX is proved by transporting `CategoryTheory.Functor.IsEquivalence` along the
*corestricted* identification
`AlgebraicGeometry.SmallZariski.associatedModuleQcohOnSiteIsoAssociatedSheafFunctorOnSite`,
rather than by re-running the source's decomposition into full faithfulness and essential
surjectivity over the sections-defined functor.  Both routes are available, and this one is taken
because the decomposition's three inputs — [Stacks, Tag 03DV] (2), [Stacks, Tag 0GN7] and
`AlgebraicGeometry.SmallZariski.isQuasicoherent_restrictModule` — are exactly what
`AlgebraicGeometry.SmallZariski.isEquivalence_associatedModuleQcohOnSite` already assembles, so
re-running it would duplicate that assembly and not weaken the dependence on the
identification.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03FH](https://stacks.math.columbia.edu/tag/03FH)
* [Stacks Project, Tag 06VE](https://stacks.math.columbia.edu/tag/06VE)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallZariski

variable (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### [Stacks, Tag 03DV] (2) for the sections-defined `𝓕ᵃ` -/

/-- **[Stacks, Tag 03DV] (2) at `τ = Zariski`, for the sheaf the source constructs.**  The
associated module `𝓕ᵃ` of [Stacks, Tag 03DU] (4) — the sheaf on `S_Zar` whose sections over an
object `f : T → S` are `Γ(T, f^*𝓕)`,
`AlgebraicGeometry.SmallZariski.associatedModuleOfSections` — is a quasi-coherent `𝒪`-module in
the sense of [Stacks, Tag 03DL] (6).

`AlgebraicGeometry.SmallZariski.isQuasicoherentOnSite_associatedModule_of_isQuasicoherent` is the
same clause for the *pullback*-defined `𝓕ᵃ` of [Stacks, Remark 03FH]; this is it read through
`AlgebraicGeometry.SmallZariski.associatedModuleIsoOfSections`, which identifies the two, and
quasi-coherence on a site is invariant under isomorphism. -/
@[stacks 03DV "part (2) at τ = Zariski, for the SECTIONS-defined 𝓕ᵃ of Definition 03DU (4) — \
SmallZariski.associatedModuleOfSections, whose sections over f : T → S are Γ(T, f^*𝓕).  The same \
clause for the pullback-defined 𝓕ᵃ of Remark 03FH is \
isQuasicoherentOnSite_associatedModule_of_isQuasicoherent; the two sheaves are identified by \
associatedModuleIsoOfSections"]
public theorem isQuasicoherentOnSite_associatedModuleOfSections (F : S.Modules)
    [F.IsQuasicoherent] : (associatedModuleOfSections B S hS F).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso (associatedModuleIsoOfSections B S hS F)
    (isQuasicoherentOnSite_associatedModule_of_isQuasicoherent B S hS F inferInstance)

/-! ### [Stacks, Tag 03DX] (2) for the sections-defined functor -/

/-- **The functor of [Stacks, Tag 03DX] (2) at `τ = Zariski`, as the source defines it**:
`𝓕 ↦ 𝓕ᵃ` of [Stacks, Tag 03DU] (4) as a functor `QCoh(𝒪_S) ⥤ QCoh(S_Zar, 𝒪)`.

This is `AlgebraicGeometry.SmallZariski.associatedSheafFunctor`, whose target is *all* modules on
`S_Zar`, corestricted along [Stacks, Tag 03DV] (2),
`AlgebraicGeometry.SmallZariski.isQuasicoherentOnSite_associatedModuleOfSections`.  Its
pullback-defined counterpart is
`AlgebraicGeometry.SmallZariski.associatedModuleQcohOnSite`. -/
public noncomputable abbrev associatedSheafFunctorOnSite :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (structureSheaf B S hS)).FullSubcategory :=
  ObjectProperty.lift _ (associatedSheafFunctor B S hS) fun M =>
    @isQuasicoherentOnSite_associatedModuleOfSections B S hS M.obj M.property

/-- **The two corestricted readings of `𝓕 ↦ 𝓕ᵃ` on the small Zariski site agree.**
`AlgebraicGeometry.SmallZariski.associatedModuleQcohIsoAssociatedSheafFunctor` corestricted to
`QCoh(S_Zar, 𝒪)`, each side along its own form of [Stacks, Tag 03DV] (2): a morphism of the full
subcategory is a morphism of the ambient category, so naturality is the naturality of that
isomorphism unchanged. -/
public noncomputable def associatedModuleQcohOnSiteIsoAssociatedSheafFunctorOnSite :
    associatedModuleQcohOnSite B S hS ≅ associatedSheafFunctorOnSite B S hS :=
  NatIso.ofComponents
    (fun M => ObjectProperty.isoMk _
      ((associatedModuleQcohIsoAssociatedSheafFunctor B S hS).app M))
    (fun f => ObjectProperty.hom_ext _
      ((associatedModuleQcohIsoAssociatedSheafFunctor B S hS).hom.naturality f))

/-- **[Stacks, Tag 03DX] clause (2) at `τ = Zariski`, for the functor the source defines**: the
sections-defined `𝓕 ↦ 𝓕ᵃ` of [Stacks, Tag 03DU] (4) is an equivalence
`QCoh(𝒪_S) ⥤ QCoh(S_Zar, 𝒪)`.

`AlgebraicGeometry.SmallZariski.isEquivalence_associatedModuleQcohOnSite` is the same clause for
the pullback-defined functor of [Stacks, Remark 03FH]; this is it read through
`AlgebraicGeometry.SmallZariski.associatedModuleQcohIsoAssociatedSheafFunctor`.  The
decomposition is the source's own: [Stacks, Tag 03DV] (2) for the functor,
[Stacks, Tag 0GN7] for full faithfulness, and
`AlgebraicGeometry.SmallZariski.isQuasicoherent_restrictModule` for essential surjectivity. -/
@[stacks 03DX "clause (2) at τ = Zariski, for the SECTIONS-defined functor 𝓕 ↦ 𝓕ᵃ of \
Definition 03DU (4) — SmallZariski.associatedSheafFunctor corestricted to QCoh(S_Zar, 𝒪) — is an \
equivalence QCoh(𝒪_S) ⥤ QCoh(S_Zar, 𝒪).  The same clause for the pullback-defined functor of \
Remark 03FH is isEquivalence_associatedModuleQcohOnSite; the two functors are identified by \
associatedModuleQcohIsoAssociatedSheafFunctor"]
public theorem isEquivalence_associatedSheafFunctorOnSite :
    (associatedSheafFunctorOnSite B S hS).IsEquivalence :=
  have := isEquivalence_associatedModuleQcohOnSite B S hS
  Functor.isEquivalence_of_iso
    (associatedModuleQcohOnSiteIsoAssociatedSheafFunctorOnSite B S hS)

/-- **The equivalence of categories of [Stacks, Tag 03DX] (2) at `τ = Zariski`, for the functor
the source defines**: `QCoh(𝒪_S) ≌ QCoh(S_Zar, 𝒪)`, with the sections-defined `𝓕 ↦ 𝓕ᵃ` as its
functor.

The source states the clause as an equivalence rather than as the three properties of the
functor, and this is that statement; its `CategoryTheory.Equivalence.functor` is
`AlgebraicGeometry.SmallZariski.associatedSheafFunctorOnSite` by definition.  Its
pullback-defined counterpart is
`AlgebraicGeometry.SmallZariski.associatedModuleEquivalence`. -/
@[stacks 03DX "clause (2) at τ = Zariski, the equivalence of categories \
QCoh(𝒪_S) ≌ QCoh(S_Zar, 𝒪) whose functor is the SECTIONS-defined 𝓕 ↦ 𝓕ᵃ of Definition 03DU (4), \
SmallZariski.associatedSheafFunctor corestricted to QCoh(S_Zar, 𝒪).  The same clause for the \
pullback-defined functor of Remark 03FH is associatedModuleEquivalence"]
public noncomputable def associatedSheafFunctorEquivalence :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ≌
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (structureSheaf B S hS)).FullSubcategory :=
  have := isEquivalence_associatedSheafFunctorOnSite B S hS
  (associatedSheafFunctorOnSite B S hS).asEquivalence

/-! ### [Stacks, Tag 06VE] (2), (3) and (4) for the sections-defined functor -/

/-- **[Stacks, Tag 06VE] (2) for the small site at `τ = Zariski`, for the functor the source
defines.**  The sections-defined `𝓕 ↦ 𝓕ᵃ` of [Stacks, Tag 03DU] (4), as a functor
`QCoh(𝒪_S) ⥤ Mod(S_Zar, 𝒪)`, commutes with direct sums.

`AlgebraicGeometry.SmallZariski.preservesColimitsOfShape_discrete_associatedModuleQcohOfComparison`
is the same clause for the pullback-defined functor of [Stacks, Remark 03FH]; this is it read
through `AlgebraicGeometry.SmallZariski.associatedModuleQcohIsoAssociatedSheafFunctor`.  06VE's
second functor has target `Mod(S_τ, 𝒪)`, which is the target here on the nose. -/
@[stacks 06VE "part (2), small site at τ = Zariski, for the SECTIONS-defined functor 𝓕 ↦ 𝓕ᵃ of \
Definition 03DU (4) — SmallZariski.associatedSheafFunctor.  The same clause for the \
pullback-defined functor of Remark 03FH is \
preservesColimitsOfShape_discrete_associatedModuleQcohOfComparison; the two functors are \
identified by associatedModuleQcohIsoAssociatedSheafFunctor"]
public theorem preservesColimitsOfShape_discrete_associatedSheafFunctor (I : Type u) :
    PreservesColimitsOfShape (Discrete I) (associatedSheafFunctor B S hS) :=
  have := preservesColimitsOfShape_discrete_associatedModuleQcohOfComparison B S hS I
  preservesColimitsOfShape_of_natIso (associatedModuleQcohIsoAssociatedSheafFunctor B S hS)

/-- **[Stacks, Tag 06VE] (3) for the small site at `τ = Zariski`, for the functor the source
defines.**  The sections-defined `𝓕 ↦ 𝓕ᵃ` commutes with all colimits indexed at the size of the
scheme.

Scope and route as on
`AlgebraicGeometry.SmallZariski.preservesColimitsOfShape_discrete_associatedSheafFunctor`. -/
@[stacks 06VE "part (3), small site at τ = Zariski, for the SECTIONS-defined functor 𝓕 ↦ 𝓕ᵃ of \
Definition 03DU (4) — SmallZariski.associatedSheafFunctor.  The same clause for the \
pullback-defined functor of Remark 03FH is \
preservesColimitsOfSize_associatedModuleQcohOfComparison; \
the two functors are identified by associatedModuleQcohIsoAssociatedSheafFunctor"]
public theorem preservesColimitsOfSize_associatedSheafFunctor :
    PreservesColimitsOfSize.{u, u} (associatedSheafFunctor B S hS) := by
  constructor
  intro K _
  have := preservesColimitsOfSize_associatedModuleQcohOfComparison B S hS
  have : PreservesColimitsOfShape K (associatedModuleQcoh B S hS) := inferInstance
  exact preservesColimitsOfShape_of_natIso (associatedModuleQcohIsoAssociatedSheafFunctor B S hS)

/-- **[Stacks, Tag 06VE] (4) for the small site at `τ = Zariski`, for the functor the source
defines.**  The sections-defined `𝓕 ↦ 𝓕ᵃ` is right exact, i.e. commutes with finite colimits.

Scope and route as on
`AlgebraicGeometry.SmallZariski.preservesColimitsOfShape_discrete_associatedSheafFunctor`; see the
implementation notes of this module for why this is not read off clause (3). -/
@[stacks 06VE "part (4), small site at τ = Zariski, for the SECTIONS-defined functor 𝓕 ↦ 𝓕ᵃ of \
Definition 03DU (4) — SmallZariski.associatedSheafFunctor.  The same clause for the \
pullback-defined functor of Remark 03FH is \
preservesFiniteColimits_associatedModuleQcohOfComparison; the two functors are identified by \
associatedModuleQcohIsoAssociatedSheafFunctor"]
public theorem preservesFiniteColimits_associatedSheafFunctor :
    PreservesFiniteColimits (associatedSheafFunctor B S hS) :=
  have := preservesFiniteColimits_associatedModuleQcohOfComparison B S hS
  preservesFiniteColimits_of_natIso (associatedModuleQcohIsoAssociatedSheafFunctor B S hS)

/-! ### [Stacks, Tag 06VE] (10) for the sections-defined functor -/

/-- **The two readings of `𝓕 ↦ 𝓕ᵃ` on the small Zariski site have the same essential image.**
An `𝒪`-module on `S_Zar` is `𝓕ᵃ` for the sections-defined functor of [Stacks, Tag 03DU] (4)
exactly when it is `𝓕ᵃ` for the pullback-defined functor of [Stacks, Remark 03FH]: compose the
given isomorphism with the component of
`AlgebraicGeometry.SmallZariski.associatedModuleQcohIsoAssociatedSheafFunctor` at the witnessing
module. -/
public theorem essImage_associatedSheafFunctor_iff
    (E : SheafOfModules.{u} (structureSheaf B S hS)) :
    (associatedSheafFunctor B S hS).essImage E ↔ (associatedModuleQcoh B S hS).essImage E := by
  constructor
  · rintro ⟨F, ⟨e⟩⟩
    exact ⟨F, ⟨(associatedModuleQcohIsoAssociatedSheafFunctor B S hS).app F ≪≫ e⟩⟩
  · rintro ⟨F, ⟨e⟩⟩
    exact ⟨F, ⟨((associatedModuleQcohIsoAssociatedSheafFunctor B S hS).app F).symm ≪≫ e⟩⟩

/-- **[Stacks, Tag 06VE] (10) for the small site at `τ = Zariski`, for the functor the source
defines.**  Given a short exact sequence `0 → 𝓕₁ᵃ → 𝓔 → 𝓕₂ᵃ → 0` of `𝒪`-modules on the small
Zariski site of `S`, with `𝓕₁` and `𝓕₂` quasi-coherent on `S` and `𝓕 ↦ 𝓕ᵃ` the sections-defined
functor of [Stacks, Tag 03DU] (4), the module `𝓔` is itself in the essential image of that
functor.

`AlgebraicGeometry.SmallZariski.essImage_X₂_of_shortExactOfComparison` is the same clause for the
pullback-defined functor of [Stacks, Remark 03FH]; the two functors have the same essential image
by `AlgebraicGeometry.SmallZariski.essImage_associatedSheafFunctor_iff`, and all three hypotheses
and the conclusion read across it.

The clause in the form the source states it — "`𝓔` is quasi-coherent" — is
`AlgebraicGeometry.SmallZariski.isQuasicoherentOnSite_X₂_of_shortExactOfComparison`, whose
statement names no functor and so needs no sections-defined counterpart. -/
@[stacks 06VE "part (10), small site at τ = Zariski, for the SECTIONS-defined functor 𝓕 ↦ 𝓕ᵃ of \
Definition 03DU (4) — SmallZariski.associatedSheafFunctor.  The same clause for the \
pullback-defined functor of Remark 03FH is essImage_X₂_of_shortExactOfComparison; the two \
functors have the same essential image by essImage_associatedSheafFunctor_iff"]
public theorem essImage_X₂_of_shortExact_associatedSheafFunctor
    {C : ShortComplex (SheafOfModules.{u} (structureSheaf B S hS))} (hC : C.ShortExact)
    (h₁ : (associatedSheafFunctor B S hS).essImage C.X₁)
    (h₃ : (associatedSheafFunctor B S hS).essImage C.X₃) :
    (associatedSheafFunctor B S hS).essImage C.X₂ :=
  (essImage_associatedSheafFunctor_iff B S hS _).2
    (essImage_X₂_of_shortExactOfComparison B S hS hC
      ((essImage_associatedSheafFunctor_iff B S hS _).1 h₁)
      ((essImage_associatedSheafFunctor_iff B S hS _).1 h₃))

end AlgebraicGeometry.SmallZariski

end
