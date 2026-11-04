module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.UniquenessOfASolutionUnconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.GlueingForHomsRelativizedCoherence
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.GlueingForHomsFromTheCoverUnconditional

/-!
# The glueing of morphisms at an arbitrary open, from the covering hypotheses

Let `(X, 𝒪_X)` be a ringed space and let `(ℬ, K_U, ρ^U_V)` be a system of locally given derived
objects on it, as in Situation [Stacks, Tag 0D67].  The sheaf condition of [Stacks, Tag 0D66]
part (2), in the form `Stacks.DerivedGlueing.HasGluingForHomsAt S O`, is what the comparison
isomorphism and the cocycle condition of [Stacks, Tag 0D69] consume, and they consume it at the
overlap `U ∩ V` and at the triple intersection `U ∩ V ∩ W` — not at the whole space.

`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.GlueingForHomsAtTopFromTheCover`
discharges it at `O = ⊤`.  This file discharges it at an arbitrary open `O` which is the union of
the members of `ℬ` contained in it, from hypotheses (1) and (2) of [Stacks, Tag 0D68] and **one**
further statement, isolated here as `Stacks.DerivedGlueing.HasGlobalNegativeExtVanishing`.

## What the passage from `⊤` to a general open costs

Two things are needed for the general open, and the module documentation of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.GlueingForHomsOverAMember` names both:
the generalisation from `⊤` to `O` of `Stacks.DerivedGlueing.openModuleRestriction_top_eq`, and
the identification of `Stacks.DerivedGlueing.restrictHomBelow` with
`AlgebraicGeometry.RingedSite.restrictDerivedHom` through it.  **Both are proved.**  The first is
`Stacks.DerivedGlueing.openModuleRestriction_eq`, which holds by `rfl` for an arbitrary open; the
second is `Stacks.DerivedGlueing.restrictHomBelow_eq_restrictDerivedHom`, unconditional at an
arbitrary open since the reduction of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.CompareIsoCounitReduction`.  So the
morphism dictionary — the whole content of the discharge at `⊤` — needs nothing new at a general
open, and `Stacks.DerivedGlueing.gluesHomsAt_of_sSup_covered` below is its general-open form.

What is **not** carried is the negative-`Ext` hypothesis of the sheaf condition at the members of
`ℬ` that are *not* contained in `O`.  The sheaf condition is read off a coarsening of a collection
covering the whole space ([Stacks, Tag 0D5Q],
`Stacks.DerivedGlueing.exists_coarsening`), so it asks for the vanishing at every member; the
objects here are given only over `O`, and the hypothesis available is the vanishing at the members
contained in `O`.  A member straddling the boundary of `O` is not reached by either.

The collection `Stacks.DerivedGlueing.opensBelowTop` — the members contained in `O`, together with
`⊤` — covers the whole space and has the covering property on intersections, so the discharge can
be run with it instead of with `ℬ`, and then exactly **one** instance of the missing hypothesis
remains, the one at `⊤`.  That instance is the vanishing of `Ext^i(j_!K, j_!L)` for `i < 0`, which
by the adjunction `j_! ⊣ j^*` is the vanishing clause of [Stacks, Tag 0D68] for the system induced
on the ringed space `O`, i.e. the clause the source obtains by applying Tag 0D68 there.  That is
`Stacks.DerivedGlueing.HasGlobalNegativeExtVanishing`, which is isolated here and discharged at
every open the collection covers by
`Stacks.DerivedGlueing.hasGlobalNegativeExtVanishing_of_sSup_covered`, in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.HomVanishingOverASubcollection` — by
running the whole-space statement on the ringed space `X|O`, which the members below `O` cover.

## Main definitions

* `Stacks.DerivedGlueing.globalObjOver`, `Stacks.DerivedGlueing.siteRestrictOver`: the extension
  by zero along `O` of an object given over `O`, and its restriction to the slice over an open.
* `Stacks.DerivedGlueing.selfHomEquivOver`: the morphism dictionary at `W = O`.
* `Stacks.DerivedGlueing.opensBelowTop`: the members contained in `O`, together with `⊤`.
* `Stacks.DerivedGlueing.HasGlobalNegativeExtVanishing`: the vanishing clause of
  [Stacks, Tag 0D68] read at `O`.

## Main results

* `Stacks.DerivedGlueing.restrictDerivedHom_selfHomEquivOver`: the restriction of the morphism
  attached to `ψ : K ⟶ L` is the morphism attached to the displayed restriction of `ψ`.
* `Stacks.DerivedGlueing.gluesHomsAt_of_sSup_covered`: the glueing of morphisms at an arbitrary
  open the collection covers, for a pair of objects over it whose negative `Ext` vanishes at every
  member.
* `Stacks.DerivedGlueing.gluesHomsAt_of_sSup_covered_of_vanishing`: the same from the vanishing at
  `⊤` alone, by running the discharge over `Stacks.DerivedGlueing.opensBelowTop`.
* `Stacks.DerivedGlueing.subsingleton_shiftedHom_overFunctorTop`: the converse of
  `Stacks.DerivedGlueing.subsingleton_shiftedHom_of_overTop`, so that the vanishing on the slice
  over `⊤` and the vanishing of the global group are the same statement.
* `Stacks.DerivedGlueing.hasGluingForHomsAt_of_sSup_covered` and
  `Stacks.DerivedGlueing.hasUniqueSolutionOverIso_of_covers_of_vanishing`: the sheaf condition and
  the relativized uniqueness clause of Tag 0D68.
* `Stacks.DerivedGlueing.exists_unique_overlapIso_of_covers_of_vanishing` and
  `Stacks.DerivedGlueing.restrictOverlapHom_cocycle_of_covers_of_vanishing`: the two clauses of
  Tag 0D69 at hypotheses (1) and (2) of Tag 0D68 and nothing else but that one vanishing
  statement, read at the single open the argument reads it at.

## The global covering hypothesis is redundant

None of the statements below asks that the collection cover `X`: the hypothesis is implied by
the hypotheses that remain.  Each statement is read at an
open `O` which is the union of the members of the collection contained in it, and the proof
splits on whether `O` is `⊤`: away from `⊤` the argument runs over
`Stacks.DerivedGlueing.opensBelowTop`, a collection which contains `⊤` and so covers `X` whatever
the original collection does; and at `O = ⊤` the hypothesis on `O` *is* the statement that the
collection covers `X`, because every open is contained in `⊤`.

This matters beyond economy.  It is what makes the relativized uniqueness clause of
[Stacks, Tag 0D68] available for a collection that covers only part of the space — the shape the
limit stages of the recursion of [Stacks, Tag 0D6B] consume, where the collection is the set of
stages strictly below a limit stage.

## Tags covered

None.  Every statement below either is a step of a proof or still carries
`Stacks.DerivedGlueing.HasGlobalNegativeExtVanishing` as a hypothesis; no `@[stacks]` attribute
is attached.  That hypothesis is discharged downstream, by
`Stacks.DerivedGlueing.hasGlobalNegativeExtVanishing_of_sSup_covered`, and the two clauses of
Tag 0D69 below are registered there in their discharged form,
`Stacks.DerivedGlueing.exists_unique_overlapIso_of_covers` and
`Stacks.DerivedGlueing.restrictOverlapHom_cocycle_of_covers`.

## References

* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
* [Stacks Project, Tag 0D69](https://stacks.math.columbia.edu/tag/0D69)
* [Stacks Project, Tag 0D5Q](https://stacks.math.columbia.edu/tag/0D5Q)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open ExtensionByZeroModules
open Stacks.SheafOfModules (ringedSite)

namespace Stacks.DerivedGlueing

universe u

variable {X : RingedSpace.{u, u}}

attribute [local instance 10000] HasDerivedCategory.standard

/-- Extension by zero along `O` of an object given over `O`. -/
abbrev globalObjOver (O : Opens X.carrier) (K : OpenDerivedCategory X O) :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) :=
  (jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj K

/-- The restriction of that extension to the slice over an open. -/
abbrev siteRestrictOver (O W : Opens X.carrier) (K : OpenDerivedCategory X O) :=
  (SheafOfModules.overFunctor.{u} (structureSheafRing X) W).mapDerivedCategory.obj
    (globalObjOver O K)

/-- The morphism dictionary at `W = O`. -/
def selfHomEquivOver (S : LocallyGiven X) {O : Opens X.carrier}
    (K L : OpenDerivedCategory X O) :
    (K ⟶ L) ≃ (siteRestrictOver O O K ⟶ siteRestrictOver O O L) :=
  (Iso.homCongr ((restrictionSelfIso S O le_rfl).app K)
      ((restrictionSelfIso S O le_rfl).app L)).symm.trans
    (homEquivSlice S K L (le_refl O))

/-- The dictionary at `W = O`, written out: it is the dictionary at the open `O` applied to the
conjugate of the morphism by the identification of restriction from `O` to `O` with the
identity. -/
theorem selfHomEquivOver_apply (S : LocallyGiven X) {O : Opens X.carrier}
    (K L : OpenDerivedCategory X O) (psi : K ⟶ L) :
    selfHomEquivOver S K L psi =
      homEquivSlice S K L (le_refl O)
        (((restrictionSelfIso S O le_rfl).app K).hom ≫ psi ≫
          ((restrictionSelfIso S O le_rfl).app L).inv) :=
  rfl

/-- **The site-side restriction to `W` of the morphism attached to `ψ : K ⟶ L` is the morphism
attached to the displayed restriction of `ψ` to `W`.** This is the dictionary
`Stacks.DerivedGlueing.restrictHomBelow_eq_restrictDerivedHom` read at the pair `W ≤ O ≤ O`,
followed by `Stacks.DerivedGlueing.restrictionSelf_conj_eq_map` and
`Stacks.DerivedGlueing.restrictHomBelow_map`. -/
theorem restrictDerivedHom_selfHomEquivOver (S : LocallyGiven X) {O : Opens X.carrier}
    (K L : OpenDerivedCategory X O) (W : Opens X.carrier) (hWO : W ≤ O) (psi : K ⟶ L) :
    RingedSite.restrictDerivedHom (ringedSite X.sheaf) hWO.hom
        (globalObjOver O K) (globalObjOver O L) (selfHomEquivOver S K L psi) =
      homEquivSlice S K L hWO ((S.restriction W O hWO).map psi) :=
  have hchi : ((restrictionSelfIso S O le_rfl).app K).hom ≫ psi ≫
      ((restrictionSelfIso S O le_rfl).app L).inv = (S.restriction O O le_rfl).map psi :=
    restrictionSelf_conj_eq_map S O le_rfl psi
  have e1 : selfHomEquivOver S K L psi =
      homEquivSlice S K L (le_refl O) ((S.restriction O O le_rfl).map psi) :=
    (selfHomEquivOver_apply S K L psi).trans (congrArg (homEquivSlice S K L (le_refl O)) hchi)
  have hd := restrictHomBelow_eq_restrictDerivedHom S K L hWO (le_refl O)
    ((S.restriction O O le_rfl).map psi)
  have h2 : restrictHomBelow S hWO (le_refl O) ((S.restriction O O le_rfl).map psi) =
      (S.restriction W O hWO).map psi :=
    restrictHomBelow_map S hWO (le_refl O) psi
  (congrArg
      (RingedSite.restrictDerivedHom (ringedSite X.sheaf) hWO.hom
        (globalObjOver O K) (globalObjOver O L)) e1).trans
    (hd.symm.trans (congrArg (homEquivSlice S K L hWO) h2))

/-! ### The members below an open, together with the whole space -/

/-- **The members of the collection contained in `O`, together with `⊤`.** -/
def opensBelowTop (S : LocallyGiven X) (O : Opens X.carrier) : Set (Opens X.carrier) :=
  {W | W ∈ S.opens ∧ W ≤ O} ∪ {⊤}

/-- A member of the collection contained in `O` belongs to the enlarged collection. -/
theorem mem_opensBelowTop_of_mem {S : LocallyGiven X} {O W : Opens X.carrier}
    (hW : W ∈ S.opens) (hWO : W ≤ O) : W ∈ opensBelowTop S O :=
  Or.inl ⟨hW, hWO⟩

/-- The whole space belongs to the enlarged collection. -/
theorem top_mem_opensBelowTop (S : LocallyGiven X) (O : Opens X.carrier) :
    (⊤ : Opens X.carrier) ∈ opensBelowTop S O :=
  Or.inr rfl

/-- The collection covers the space, `⊤` being a member. -/
theorem sSup_opensBelowTop (S : LocallyGiven X) (O : Opens X.carrier) :
    sSup (opensBelowTop S O) = ⊤ :=
  top_le_iff.mp (le_sSup (top_mem_opensBelowTop S O))

/-- An element of the collection other than `⊤` is a member of `S.opens` below `O`. -/
theorem mem_of_mem_opensBelowTop {S : LocallyGiven X} {O W : Opens X.carrier}
    (hW : W ∈ opensBelowTop S O) (hne : W ≠ ⊤) : W ∈ S.opens ∧ W ≤ O :=
  hW.elim id fun h => absurd h hne

/-- **The intersection of two elements of the collection is the union of the elements contained
in it.** -/
theorem inf_eq_sSup_opensBelowTop (S : LocallyGiven X)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (O : Opens X.carrier) :
    ∀ A ∈ opensBelowTop S O, ∀ B ∈ opensBelowTop S O,
      A ⊓ B = sSup {W | W ∈ opensBelowTop S O ∧ W ≤ A ⊓ B} := by
  have key : ∀ A ∈ opensBelowTop S O, A = sSup {W | W ∈ opensBelowTop S O ∧ W ≤ A} :=
    fun A hA => le_antisymm (le_sSup ⟨hA, le_rfl⟩) (sSup_le fun _ hW => hW.2)
  intro A hA B hB
  rcases eq_or_ne A ⊤ with rfl | hAne
  · simpa using key B hB
  rcases eq_or_ne B ⊤ with rfl | hBne
  · simpa using key A hA
  obtain ⟨hAmem, hAO⟩ := mem_of_mem_opensBelowTop hA hAne
  obtain ⟨hBmem, -⟩ := mem_of_mem_opensBelowTop hB hBne
  refine le_antisymm ?_ (sSup_le fun _ hW => hW.2)
  refine (hinter A hAmem B hBmem).le.trans (sSup_le fun W hW => ?_)
  exact le_sSup ⟨mem_opensBelowTop_of_mem hW.1 (hW.2.trans (inf_le_left.trans hAO)), hW.2⟩

/-- **The open `O` is the union of the elements of the collection contained in it.** -/
theorem sSup_covered_opensBelowTop (S : LocallyGiven X) {O : Opens X.carrier}
    (hO : O = sSup {W | W ∈ S.opens ∧ W ≤ O}) :
    O = sSup {W | W ∈ opensBelowTop S O ∧ W ≤ O} := by
  refine le_antisymm ?_ (sSup_le fun _ hW => hW.2)
  exact hO.le.trans (sSup_le fun W hW => le_sSup ⟨mem_opensBelowTop_of_mem hW.1 hW.2, hW.2⟩)

/-- A family of morphisms over the members below `O` is glued by a unique morphism over `O` as soon
as the corresponding family of displayed morphisms is glued by a unique morphism of the sites. -/
private theorem exists_unique_map_of_exists_unique_restrictDerivedHom (S : LocallyGiven X)
    {O : Opens X.carrier} (K L : OpenDerivedCategory X O) (ℬ : Set (Opens X.carrier))
    (hℬ : ∀ W ∈ S.opens, W ≤ O → W ∈ ℬ) (hmem : ∀ U ∈ ℬ, U ≤ O → U ∈ S.opens)
    (phi : ∀ W, W ∈ S.opens → ∀ hWO : W ≤ O,
      (S.restriction W O hWO).obj K ⟶ (S.restriction W O hWO).obj L)
    (h : ∃! Psi : siteRestrictOver O O K ⟶ siteRestrictOver O O L,
      ∀ (U : Opens X.carrier) (hU : U ∈ ℬ) (hUO : U ≤ O),
        RingedSite.restrictDerivedHom (ringedSite X.sheaf) hUO.hom
          (globalObjOver O K) (globalObjOver O L) Psi =
          homEquivSlice S K L hUO (phi U (hmem U hU hUO) hUO)) :
    ∃! ψ : K ⟶ L, ∀ (W : Opens X.carrier) (hW : W ∈ S.opens) (hWO : W ≤ O),
      (S.restriction W O hWO).map ψ = phi W hW hWO := by
  obtain ⟨Psi, hPsi, huniq⟩ := h
  refine ⟨(selfHomEquivOver S K L).symm Psi, fun W hW hWO => ?_, fun chi hchi => ?_⟩
  · refine (homEquivSlice S K L hWO).injective ?_
    exact ((restrictDerivedHom_selfHomEquivOver S K L W hWO
      ((selfHomEquivOver S K L).symm Psi)).symm.trans
        (congrArg
          (RingedSite.restrictDerivedHom (ringedSite X.sheaf) hWO.hom
            (globalObjOver O K) (globalObjOver O L))
          ((selfHomEquivOver S K L).apply_symm_apply Psi))).trans
      (hPsi W (hℬ W hW hWO) hWO)
  · refine (selfHomEquivOver S K L).injective ?_
    refine ((huniq (selfHomEquivOver S K L chi)
      (fun U hU hUO =>
        (restrictDerivedHom_selfHomEquivOver S K L U hUO chi).trans
          (congrArg (homEquivSlice S K L hUO) (hchi U (hmem U hU hUO) hUO)))).trans ?_)
    exact ((selfHomEquivOver S K L).apply_symm_apply Psi).symm

/-- **The glueing of morphisms at an arbitrary open `O` that the collection covers, for one pair
of objects given over `O`, from the vanishing at `⊤` alone.** -/
theorem gluesHomsAt_of_sSup_covered_of_vanishing (S : LocallyGiven X)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    {O : Opens X.carrier} (hO : O = sSup {W | W ∈ S.opens ∧ W ≤ O})
    (K L : OpenDerivedCategory X O)
    (hres : ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (siteRestrictOver O ⊤ K) (siteRestrictOver O ⊤ L) i)) :
    GluesHomsAt S O K L := by
  intro hExt phi hphi
  by_cases htop : O = ⊤
  · subst htop
    have hset : {W : Opens X.carrier | W ∈ S.opens ∧ W ≤ ⊤} = S.opens :=
      Set.ext fun W => ⟨fun h => h.1, fun h => ⟨h, le_top⟩⟩
    have hcover : sSup S.opens = ⊤ := by rw [← hset]; exact hO.symm
    exact hasGluingForHomsAt_top_unconditional S hcover hinter K L hExt phi hphi
  have hmem : ∀ U ∈ opensBelowTop S O, U ≤ O → U ∈ S.opens := by
    intro U hU hUO
    exact (mem_of_mem_opensBelowTop hU fun h => htop (top_le_iff.mp (h ▸ hUO))).1
  obtain ⟨Psi, hPsi, huniq⟩ := exists_unique_restrictDerivedHom_on_sSup_covered
    (globalObjOver O K) (globalObjOver O L) (opensBelowTop S O)
    (sSup_opensBelowTop S O) (inf_eq_sSup_opensBelowTop S hinter O)
    (by
      intro U hU i hi
      rcases eq_or_ne U ⊤ with rfl | hUne
      · exact hres i hi
      · obtain ⟨hUmem, hUO⟩ := mem_of_mem_opensBelowTop hU hUne
        exact subsingleton_shiftedHom_overFunctor_jShriek S K L hUO i (hExt U hUmem hUO i hi))
    O (sSup_covered_opensBelowTop S hO)
    (fun U hU hUO => homEquivSlice S K L hUO (phi U (hmem U hU hUO) hUO))
    (fun U U' hU hU' hle hUO =>
      ((restrictHomBelow_eq_restrictDerivedHom S K L hle hUO
            (phi U (hmem U hU hUO) hUO)).symm).trans
        (congrArg (homEquivSlice S K L (hle.trans hUO))
          (hphi U U' (hmem U hU hUO) (hmem U' hU' (hle.trans hUO)) hle hUO)))
  exact exists_unique_map_of_exists_unique_restrictDerivedHom S K L (opensBelowTop S O)
    (fun W hW hWO => mem_opensBelowTop_of_mem hW hWO) hmem phi
    ⟨Psi, hPsi, huniq⟩

/-- **The glueing of morphisms at an arbitrary open `O` that the collection covers, for one
pair of objects given over `O`.** -/
theorem gluesHomsAt_of_sSup_covered (S : LocallyGiven X)
    (hcover : sSup S.opens = ⊤)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    {O : Opens X.carrier} (hO : O = sSup {W | W ∈ S.opens ∧ W ≤ O})
    (K L : OpenDerivedCategory X O)
    (hExtAll : ∀ W ∈ S.opens, ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (siteRestrictOver O W K) (siteRestrictOver O W L) i)) :
    GluesHomsAt S O K L := by
  intro _hExt phi hphi
  obtain ⟨Psi, hPsi, huniq⟩ := exists_unique_restrictDerivedHom_on_sSup_covered
    (globalObjOver O K) (globalObjOver O L) S.opens hcover hinter hExtAll O hO
    (fun W hW hWO => homEquivSlice S K L hWO (phi W hW hWO))
    (fun W W' hW hW' hle hWO =>
      ((restrictHomBelow_eq_restrictDerivedHom S K L hle hWO (phi W hW hWO)).symm).trans
        (congrArg (homEquivSlice S K L (hle.trans hWO)) (hphi W W' hW hW' hle hWO)))
  exact exists_unique_map_of_exists_unique_restrictDerivedHom S K L S.opens
    (fun _ hW _ => hW) (fun _ hW _ => hW) phi ⟨Psi, hPsi, huniq⟩

/-! ### From the vanishing of a global `Ext` group to the vanishing on the slice over `⊤` -/

section Top

variable {T : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology T) RingCat.{u})

/-- **The retraction of restriction to the slice over `⊤`, on derived categories.** -/
def retractionTopIso (K : DerivedCategory (SheafOfModules.{u} R)) :
    (overFunctorTopRetraction R).mapDerivedCategory.obj
        ((SheafOfModules.overFunctor.{u} R (⊤ : Opens T)).mapDerivedCategory.obj K) ≅ K :=
  (Stacks.Homology.mapDerivedCategoryCompIso (SheafOfModules.overFunctor.{u} R (⊤ : Opens T))
      (overFunctorTopRetraction R) (𝟭 (SheafOfModules.{u} R))
      (overFunctorTopCompRetractionIso R)).app K ≪≫
    Stacks.Homology.mapDerivedCategoryIdIso.app K

/-- **Restriction to the slice over `⊤` preserves the vanishing of a shifted `Hom` group.** The
converse of `Stacks.DerivedGlueing.subsingleton_shiftedHom_of_overTop`: the retraction
`Stacks.DerivedGlueing.overFunctorTopRetraction` is itself faithful on derived categories, by
`Stacks.DerivedGlueing.sliceExtendOverIso` at `⊤`, and it undoes the restriction. -/
theorem subsingleton_shiftedHom_overFunctorTop
    (K L : DerivedCategory (SheafOfModules.{u} R)) (i : ℤ)
    (h : Subsingleton (ShiftedHom K L i)) :
    Subsingleton (ShiftedHom
      ((SheafOfModules.overFunctor.{u} R (⊤ : Opens T)).mapDerivedCategory.obj K)
      ((SheafOfModules.overFunctor.{u} R (⊤ : Opens T)).mapDerivedCategory.obj L) i) :=
  have _hf := faithful_mapDerivedCategory_of_comp (overFunctorTopRetraction R)
    (SheafOfModules.overFunctor.{u} R (⊤ : Opens T)) (sliceExtendOverIso R ⊤)
  subsingleton_shiftedHom_of_faithful (overFunctorTopRetraction R).mapDerivedCategory _ _ i
    (subsingleton_shiftedHom_of_iso (retractionTopIso R K) (retractionTopIso R L) i h)

end Top

/-! ### The residual: the vanishing clause of Tag 0D68 at an open -/

/-- **The vanishing clause of [Stacks, Tag 0D68], read at the open `O`.** For two objects given
over `O` whose displayed restrictions to the members of the collection contained in `O` admit no
negative shifted morphisms, the extensions by zero along `O` admit none either.

By the adjunction `j_! ⊣ j^*` of
`ExtensionByZeroModules.jShriekAdjunction`, whose unit is invertible
(`ExtensionByZeroModules.isIso_jShriekAdjunction_unit`), the group
`Ext^i(j_!K, j_!L)` is `Ext^i_{\mathcal{O}_O}(K, L)`, so this is exactly the vanishing clause of
Tag 0D68 for the system induced on the ringed space `O` — the clause the source obtains by
applying Tag 0D68 there.  At `O = ⊤` it is
`Stacks.DerivedGlueing.subsingleton_shiftedHom_restrict_of_sSup_covered`; at every open the
collection covers it is
`Stacks.DerivedGlueing.hasGlobalNegativeExtVanishing_of_sSup_covered`, which runs that same
statement on the ringed space `X|O`.  `Stacks.DerivedGlueing.hasGluingForHomsAt_of_sSup_covered`
is where it is consumed. -/
def HasGlobalNegativeExtVanishing (S : LocallyGiven X) (O : Opens X.carrier) : Prop :=
  ∀ K L : OpenDerivedCategory X O,
    (∀ (W : Opens X.carrier), W ∈ S.opens → ∀ hWO : W ≤ O, ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom ((S.restriction W O hWO).obj K)
        ((S.restriction W O hWO).obj L) i)) →
    ∀ i : ℤ, i < 0 → Subsingleton (ShiftedHom (globalObjOver O K) (globalObjOver O L) i)

/-- **The glueing of morphisms at an arbitrary open the collection covers.** -/
theorem hasGluingForHomsAt_of_sSup_covered (S : LocallyGiven X)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    {O : Opens X.carrier} (hO : O = sSup {W | W ∈ S.opens ∧ W ≤ O})
    (hres : HasGlobalNegativeExtVanishing S O) :
    HasGluingForHomsAt S O := by
  intro K L hExt phi hphi
  refine gluesHomsAt_of_sSup_covered_of_vanishing S hinter hO K L
    (fun i hi => subsingleton_shiftedHom_overFunctorTop (structureSheafRing X) _ _ i
      (hres K L hExt i hi)) hExt phi hphi

/-- **The uniqueness clause of [Stacks, Tag 0D68], relativized to every open the collection
covers.** -/
theorem hasUniqueSolutionOverIso_of_covers_of_vanishing (S : LocallyGiven X)
    (hres : ∀ O : Opens X.carrier, O = sSup {W | W ∈ S.opens ∧ W ≤ O} →
      HasGlobalNegativeExtVanishing S O) :
    HasUniqueSolutionOverIso S :=
  hasUniqueSolutionOverIso_of_hasGluingForHomsAt S
    fun O hO hinter => hasGluingForHomsAt_of_sSup_covered S hinter hO (hres O hO)

/-! ### The two clauses of Tag 0D69, at the source's own hypotheses -/

/-- **The comparison isomorphism over an overlap, at the source's hypotheses (1) and (2),
with only the vanishing clause of Tag 0D68 at the overlap left over.** -/
theorem exists_unique_overlapIso_of_covers_of_vanishing (S : LocallyGiven X)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i))
    (U V : Opens X.carrier) (hU : U ∈ S.opens) (hV : V ∈ S.opens)
    (hres : HasGlobalNegativeExtVanishing S (U ⊓ V)) :
    ∃! φ : (S.restriction (U ⊓ V) U inf_le_left).obj (S.obj U hU) ≅
        (S.restriction (U ⊓ V) V inf_le_right).obj (S.obj V hV),
      IsOverlapHom S hU hV inf_le_left inf_le_right φ.hom :=
  exists_unique_overlapIso_of_hasGluingForHomsAt S hExt U V hU hV
    (hasGluingForHomsAt_of_sSup_covered S hinter (hinter U hU V hV) hres)

/-- **The cocycle condition over a triple intersection, at the source's hypotheses (1) and (2),
with only the vanishing clause of Tag 0D68 at the triple intersection left over.** -/
theorem restrictOverlapHom_cocycle_of_covers_of_vanishing (S : LocallyGiven X)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i))
    (U V W : Opens X.carrier) (hU : U ∈ S.opens) (hV : V ∈ S.opens) (hW : W ∈ S.opens)
    (hres : HasGlobalNegativeExtVanishing S (U ⊓ V ⊓ W))
    (φUV : (S.restriction (U ⊓ V) U inf_le_left).obj (S.obj U hU) ≅
      (S.restriction (U ⊓ V) V inf_le_right).obj (S.obj V hV))
    (hφUV : IsOverlapHom S hU hV inf_le_left inf_le_right φUV.hom)
    (φVW : (S.restriction (V ⊓ W) V inf_le_left).obj (S.obj V hV) ≅
      (S.restriction (V ⊓ W) W inf_le_right).obj (S.obj W hW))
    (hφVW : IsOverlapHom S hV hW inf_le_left inf_le_right φVW.hom)
    (φUW : (S.restriction (U ⊓ W) U inf_le_left).obj (S.obj U hU) ≅
      (S.restriction (U ⊓ W) W inf_le_right).obj (S.obj W hW))
    (hφUW : IsOverlapHom S hU hW inf_le_left inf_le_right φUW.hom) :
    restrictOverlapHom S hU hW inf_le_left inf_le_right
        (le_inf (inf_le_left.trans inf_le_left) inf_le_right : U ⊓ V ⊓ W ≤ U ⊓ W) φUW.hom =
      restrictOverlapHom S hU hV inf_le_left inf_le_right
          (inf_le_left : U ⊓ V ⊓ W ≤ U ⊓ V) φUV.hom ≫
        restrictOverlapHom S hV hW inf_le_left inf_le_right
          (le_inf (inf_le_left.trans inf_le_right) inf_le_right : U ⊓ V ⊓ W ≤ V ⊓ W) φVW.hom :=
  restrictOverlapHom_cocycle_of_hasGluingForHomsAt S hExt U V W hU hV hW
    (hasGluingForHomsAt_of_sSup_covered S hinter
      (inf_inf_eq_sSup S hinter U V W hU hV hW) hres)
    φUV hφUV φVW hφVW φUW hφUW

end Stacks.DerivedGlueing

end
