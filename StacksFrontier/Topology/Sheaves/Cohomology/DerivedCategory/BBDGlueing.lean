module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.GlueingForHomsWithoutCovering
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.WellOrderedCoverRecursion

/-!
# The BBD gluing lemma

Let `(X, 𝒪_X)` be a ringed space and let `(ℬ, K_U, ρ^U_V)` be a system of locally given derived
objects on it, as in Situation [Stacks, Tag 0D67].  Assume that `X = ⋃_{U ∈ ℬ} U`, that for
`U, V ∈ ℬ` the intersection `U ∩ V` is the union of the members of `ℬ` contained in it, and that
`Ext^i(K_U, K_U) = 0` for `i < 0` and `U ∈ ℬ`.  Then there are an object `K` of `D(𝒪_X)` and
isomorphisms `ρ_U : K|_U ≅ K_U` in `D(𝒪_U)` for `U ∈ ℬ` with `ρ^U_V ∘ ρ_U|_V = ρ_V` for `V ⊆ U`
in `ℬ`, and the pair `(K, ρ_U)` is unique up to unique isomorphism.  This is
[Stacks, Tag 0D6C], the unbounded case of Theorem 3.2.4 of [BBD].

The proof is the source's.  Well order `ℬ` and put `T_α = ⋃_{β ≤ α} U_β`.  By transfinite
induction every `T_α` carries a solution: the union `⋃_{β < α} T_β` of the earlier stages
carries one by the glueing along a well ordered chain of solutions, and adjoining the member
`U_α` is the two-open case of [Stacks, Tag 0D6A].  A last glueing along the chain of all the
`T_α` gives a solution over `X`.

The glueing along a well ordered chain of solutions is [Stacks, Tag 0D6B] read over an open.
The solutions over the stages are identified on their overlaps by the uniqueness clause of
[Stacks, Tag 0D68], the system of complexes of the transfinite recursion of Tag 0D6B is
assembled over the union of the chain, and the identifications of the glued object with the
prescribed objects on the members of `ℬ` contained in no single stage come from the uniqueness
clause once more, for the subsystem of the members contained in some stage.

## Main results

* `Stacks.DerivedGlueing.nonempty_solutionOver_of_subcollectionSolution`: a solution over an
  open for a subsystem covering every member of the collection below it is a solution for the
  system.
* `Stacks.DerivedGlueing.nonempty_solutionOver_iSup_of_wellOrdered`: solutions over the stages
  of a well ordered chain of opens glue to a solution over its union.
* `Stacks.DerivedGlueing.nonempty_solutionOver_of_eq_sSup_covered`: every open that is the
  union of the members of the collection it contains carries a solution.
* `Stacks.DerivedGlueing.exists_solution_of_covers_unconditional`: the existence clause of
  [Stacks, Tag 0D6C].
* `Stacks.DerivedGlueing.gluesAlongChain_unconditional`,
  `Stacks.DerivedGlueing.gluesAlongProperChain_unconditional`: glueing along a chain of opens
  holds for every system.
* `Stacks.DerivedGlueing.exists_solution_and_unique_solutionIso_of_covers_unconditional`:
  **[Stacks, Tag 0D6C]**, existence and uniqueness up to unique isomorphism.

## References

* [Stacks Project, Tag 0D6C](https://stacks.math.columbia.edu/tag/0D6C)
* [Stacks Project, Tag 0D6B](https://stacks.math.columbia.edu/tag/0D6B)
* [Stacks Project, Tag 0D6A](https://stacks.math.columbia.edu/tag/0D6A)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Stacks.DerivedGlueing

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}}

/-! ### From a solution for a subsystem to a solution for the system -/

/-- A solution `A` over `P` and compatible identifications of its restrictions to `V` and to
`W ≤ V ≤ P` with solutions `BV` and `BW`, the second unique, are related by a given compatible
identification of the restriction to `W` of `BV` with `BW`. -/
private theorem comp_hom_eq_of_unique {S : LocallyGiven X} {P V W : Opens X.carrier}
    (hVP : V ≤ P) (hWV : W ≤ V) (A : SolutionOver S P) {BV : SolutionOver S V}
    {BW : SolutionOver S W} (rhoV : (A.restrictOpen V hVP).obj ≅ BV.obj)
    (hrhoV : (A.restrictOpen V hVP).IsCompatibleHom BV rhoV.hom)
    (rhoW : (A.restrictOpen W (hWV.trans hVP)).obj ≅ BW.obj)
    (hunique : ∀ φ : (A.restrictOpen W (hWV.trans hVP)).obj ≅ BW.obj,
      (A.restrictOpen W (hWV.trans hVP)).IsCompatibleHom BW φ.hom → φ = rhoW)
    (psi : (S.restriction W V hWV).obj BV.obj ≅ BW.obj)
    (hpsi : (BV.restrictOpen W hWV).IsCompatibleHom BW psi.hom) :
    (S.restrictionComp W V P hWV hVP).hom.app A.obj ≫
      (S.restriction W V hWV).map rhoV.hom ≫ psi.hom = rhoW.hom :=
  congrArg Iso.hom (hunique
    ((S.restrictionComp W V P hWV hVP).app A.obj ≪≫ (S.restriction W V hWV).mapIso rhoV ≪≫ psi)
    ((restrictOpen_comparison_isCompatibleHom A hVP hWV).comp
      ((hrhoV.restrictOpen hWV).comp hpsi)))

/-- **A solution for a subsystem is a solution for the system**, over an open `P` such that every
member of the collection contained in `P` is the union of the members of the subcollection it
contains.  Over such a member the restriction of the given solution and the prescribed object are
two solutions for the subsystem, which the uniqueness clause of [Stacks, Tag 0D68] identifies
uniquely; the same uniqueness gives the compatibility of these identifications. -/
theorem nonempty_solutionOver_of_subcollectionSolution (S : LocallyGiven X)
    (𝒟 : Set (Opens X.carrier)) (h𝒟 : 𝒟 ⊆ S.opens) {P : Opens X.carrier}
    (hmem : ∀ W ∈ S.opens, W ≤ P → W = sSup {T | T ∈ 𝒟 ∧ T ≤ W})
    (hinter : ∀ U ∈ 𝒟, ∀ V ∈ 𝒟, U ⊓ V = sSup {W | W ∈ 𝒟 ∧ W ≤ U ⊓ V})
    (hExt : ∀ (W : Opens X.carrier) (hW : W ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj W hW) (S.obj W hW) i))
    (FS : SolutionOver (S.subcollection 𝒟 h𝒟) P) :
    Nonempty (SolutionOver S P) := by
  have huniq : HasUniqueSolutionOverIso (S.subcollection 𝒟 h𝒟) :=
    hasUniqueSolutionOverIso_of_covers _ hinter
  have key : ∀ (W : Opens X.carrier) (hW : W ∈ S.opens) (hWP : W ≤ P),
      ∃! φ : (FS.restrictOpen W hWP).obj ≅ (selfSolutionOverSubcollection S 𝒟 h𝒟 W hW).obj,
        (FS.restrictOpen W hWP).IsCompatibleHom (selfSolutionOverSubcollection S 𝒟 h𝒟 W hW)
          φ.hom :=
    fun W hW hWP => huniq W (hmem W hW hWP) hinter
      (fun U' hU' i hi => hExt U' (h𝒟 hU') i hi) (FS.restrictOpen W hWP)
      (selfSolutionOverSubcollection S 𝒟 h𝒟 W hW)
  choose rho hrho hrhouniq using key
  refine ⟨{ obj := FS.obj, rho := rho, compatibility := ?_ }⟩
  intro V₀ W₀ hW₀V₀ hV₀ hW₀ hV₀P
  exact comp_hom_eq_of_unique hV₀P hW₀V₀ FS (rho V₀ hV₀ hV₀P) (hrho V₀ hV₀ hV₀P)
    (rho W₀ hW₀ (hW₀V₀.trans hV₀P)) (hrhouniq W₀ hW₀ (hW₀V₀.trans hV₀P)) _
    (selfSolutionOverSubcollection_rho_isCompatibleHom S 𝒟 h𝒟 V₀ W₀ hW₀V₀ hV₀ hW₀)

/-! ### An object over the union of a chain of solutions -/

section Chain

variable (S : LocallyGiven X) {E : Type*} [LinearOrder E] (T : E → Opens X.carrier)
  (hmono : Monotone T) {V : Opens X.carrier} (hTV : ∀ α : E, T α ≤ V)
  (A : ∀ α : E, SolutionOver S (T α)) (G : OpenDerivedCategory X V)
  (sigma : ∀ α : E, (S.restriction (T α) V (hTV α)).obj G ≅ (A α).obj)

/-- The identifications of the restrictions of `G` to the stages `T β ≤ T α` with the objects of
the solutions there are compatible with a morphism of solutions from the restriction of `A α` to
`T β` to `A β`. -/
def IsCompatibleAlongChain : Prop :=
  ∀ β α : E, (h : β < α) →
    ∃ φ : (S.restriction (T β) (T α) (hmono h.le)).obj (A α).obj ⟶ (A β).obj,
    ((A α).restrictOpen (T β) (hmono h.le)).IsCompatibleHom (A β) φ ∧
      (S.restrictionComp (T β) (T α) V (hmono h.le) (hTV α)).hom.app G ≫
          (S.restriction (T β) (T α) (hmono h.le)).map (sigma α).hom ≫ φ =
        (sigma β).hom

variable {S T hmono hTV A G sigma}

/-- **The identification of the restriction of `G` to a member of the collection does not depend
on the stage it is read off.** -/
theorem transportedRho_eq_of_le (hc : IsCompatibleAlongChain S T hmono hTV A G sigma)
    {β α : E} (h : β ≤ α) (W : Opens X.carrier) (hW : W ∈ S.opens) (hWβ : W ≤ T β) :
    transportedRho S (hTV α) G (A α) (sigma α) W hW (hWβ.trans (hmono h)) =
      transportedRho S (hTV β) G (A β) (sigma β) W hW hWβ := by
  rcases h.eq_or_lt with rfl | hlt
  · rfl
  obtain ⟨φ, hφ, hφσ⟩ := hc β α hlt
  have hrho : (S.restrictionComp W (T β) (T α) hWβ (hmono h)).inv.app (A α).obj ≫
      ((A α).rho W hW (hWβ.trans (hmono h))).hom =
        (S.restriction W (T β) hWβ).map φ ≫ ((A β).rho W hW hWβ).hom :=
    ((restrictOpen_rho_hom S (A α) (T β) (hmono h) W hW hWβ).symm.trans
      (hφ W hW hWβ).symm)
  apply Iso.ext
  rw [transportedRho_hom_factor S (hTV α) G (A α) (sigma α) (T β) W (hmono h) hWβ hW, hrho,
    transportedRho_hom, ← hφσ]
  simp only [Functor.map_comp, Category.assoc]

/-- The identification of the restriction of `G` to a member of the collection contained in some
stage, read off the solution at two stages containing it, is the same. -/
theorem transportedRho_eq (hc : IsCompatibleAlongChain S T hmono hTV A G sigma) {β α : E}
    (W : Opens X.carrier) (hW : W ∈ S.opens) (hWα : W ≤ T α) (hWβ : W ≤ T β) :
    transportedRho S (hTV α) G (A α) (sigma α) W hW hWα =
      transportedRho S (hTV β) G (A β) (sigma β) W hW hWβ := by
  rcases le_total β α with h | h
  · exact transportedRho_eq_of_le hc h W hW hWβ
  · exact (transportedRho_eq_of_le hc h W hW hWα).symm

/-- The members of the collection contained in some stage of the chain. -/
def opensBelowChain (S : LocallyGiven X) (T : E → Opens X.carrier) : Set (Opens X.carrier) :=
  {W | W ∈ S.opens ∧ ∃ α : E, W ≤ T α}

omit [LinearOrder E] in
/-- The members of the collection contained in some stage of the chain belong to the collection. -/
theorem opensBelowChain_subset (S : LocallyGiven X) (T : E → Opens X.carrier) :
    opensBelowChain S T ⊆ S.opens :=
  fun _ hW => hW.1

variable (hmono hTV A G sigma) in
/-- **`G` as a solution over the union of the chain for the subsystem of the members contained in
some stage.** The identification over such a member is read off any stage containing it. -/
def chainSolutionOverSubcollection (hc : IsCompatibleAlongChain S T hmono hTV A G sigma) :
    SolutionOver (S.subcollection (opensBelowChain S T) (opensBelowChain_subset S T)) V where
  obj := G
  rho W hW _ := transportedRho S (hTV hW.2.choose) G (A hW.2.choose) (sigma hW.2.choose) W hW.1
    hW.2.choose_spec
  compatibility := by
    intro V₀ W₀ hW₀V₀ hV₀ hW₀ _
    refine (transportedRho_compatibility S (hTV hV₀.2.choose) G (A hV₀.2.choose)
      (sigma hV₀.2.choose) V₀ W₀ hW₀V₀ hV₀.1 hW₀.1 hV₀.2.choose_spec).trans ?_
    exact congrArg Iso.hom (transportedRho_eq hc W₀ hW₀.1 _ hW₀.2.choose_spec)

end Chain

/-! ### Glueing along a well ordered chain of solutions -/

/-- **A union of opens, each the union of the members of the collection it contains, is again
one.** -/
theorem iSup_eq_sSup_covered (S : LocallyGiven X) {E : Type*} (T : E → Opens X.carrier)
    (hT : ∀ α : E, T α = sSup {W | W ∈ S.opens ∧ W ≤ T α}) :
    (⨆ α : E, T α) = sSup {W | W ∈ S.opens ∧ W ≤ ⨆ α : E, T α} := by
  rw [← sSup_range]
  exact sSup_eq_sSup_covered S _ (by rintro _ ⟨α, rfl⟩; exact hT α)

/-- **The members contained in a union of a chain are covered by the members contained in a
single stage.** -/
theorem eq_sSup_opensBelowChain (S : LocallyGiven X) {E : Type*} (T : E → Opens X.carrier)
    (hT : ∀ α : E, T α = sSup {W | W ∈ S.opens ∧ W ≤ T α})
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (W : Opens X.carrier) (hW : W ∈ S.opens) (hWT : W ≤ ⨆ α : E, T α) :
    W = sSup {W' | W' ∈ opensBelowChain S T ∧ W' ≤ W} := by
  refine le_antisymm (fun x hx => ?_) (sSup_le fun _ hW' => hW'.2)
  obtain ⟨α, hxα⟩ := Opens.mem_iSup.mp (hWT hx)
  have hxWα : x ∈ W ⊓ T α := ⟨hx, hxα⟩
  rw [inf_eq_sSup_covered S hinter hW (hT α)] at hxWα
  obtain ⟨W', hW', hxW'⟩ := Opens.mem_sSup.mp hxWα
  exact Opens.mem_sSup.mpr
    ⟨W', ⟨⟨hW'.1, α, hW'.2.trans inf_le_right⟩, hW'.2.trans inf_le_left⟩, hxW'⟩

/-- The intersection of two members contained in stages of a chain is the union of the members
contained in a stage that it contains. -/
theorem inf_eq_sSup_opensBelowChain (S : LocallyGiven X) {E : Type*} (T : E → Opens X.carrier)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (U : Opens X.carrier) (hU : U ∈ opensBelowChain S T) (V : Opens X.carrier)
    (hV : V ∈ opensBelowChain S T) :
    U ⊓ V = sSup {W | W ∈ opensBelowChain S T ∧ W ≤ U ⊓ V} := by
  obtain ⟨α, hα⟩ := hU.2
  exact le_antisymm ((hinter U hU.1 V hV.1).le.trans (sSup_le_sSup fun W hW =>
    ⟨⟨hW.1, α, hW.2.trans (inf_le_left.trans hα)⟩, hW.2⟩)) (sSup_le fun _ hW => hW.2)

/-- **The object of a solution over an open covered by the collection has no negative
self-Ext.** -/
theorem SolutionOver.subsingleton_shiftedHom_self {S : LocallyGiven X} {O : Opens X.carrier}
    (A : SolutionOver S O) (hO : O = sSup {W | W ∈ S.opens ∧ W ≤ O})
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i))
    (i : ℤ) (hi : i < 0) :
    Subsingleton (ShiftedHom A.obj A.obj i) :=
  subsingleton_shiftedHom_of_subcollection S S.opens subset_rfl O hO hinter A.obj A.obj
    (fun W hW hWO j hj => subsingleton_shiftedHom_of_iso (A.rho W hW hWO) (A.rho W hW hWO) j
      (hExt W hW j hj)) i hi

/-- **Solutions over the stages of a well ordered chain of opens glue to a solution over its
union.** Let `T` be an increasing family of opens indexed by a well ordered set, each stage the
union of the members of the collection it contains, and let `A α` be a solution over `T α`.
Then there is a solution over `⋃_α T α`.

This is [Stacks, Tag 0D6B] read over an open, applied as in the source's proof of
[Stacks, Tag 0D6C]: the uniqueness clause of [Stacks, Tag 0D68] gives the transitions between
the solutions, the system of complexes of the transfinite recursion of Tag 0D6B is assembled
over the union, and the identifications of the glued object over the members contained in no
single stage come from
`Stacks.DerivedGlueing.nonempty_solutionOver_of_subcollectionSolution`. -/
theorem nonempty_solutionOver_iSup_of_wellOrdered (S : LocallyGiven X)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i))
    {E : Type u} [LinearOrder E] [WellFoundedLT E] (T : E → Opens X.carrier)
    (hmono : Monotone T) (hT : ∀ α : E, T α = sSup {W | W ∈ S.opens ∧ W ≤ T α})
    (A : ∀ α : E, SolutionOver S (T α)) :
    Nonempty (SolutionOver S (⨆ α : E, T α)) := by
  rcases isEmpty_or_nonempty E with hE | hE
  · rw [iSup_of_empty]
    exact ⟨solutionOverBot S⟩
  have hTV : ∀ α : E, T α ≤ ⨆ α : E, T α := le_iSup T
  have huniq := hasUniqueSolutionOverIso_of_covers S hinter
  have key : ∀ (β α : E) (h : β ≤ α),
      ∃! φ : ((A α).restrictOpen (T β) (hmono h)).obj ≅ (A β).obj,
        ((A α).restrictOpen (T β) (hmono h)).IsCompatibleHom (A β) φ.hom :=
    fun β α h => huniq (T β) (hT β) hinter hExt _ _
  choose rho hrho hrhouniq using key
  have hcocycle : ∀ (γ β α : E) (hγβ : γ < β) (hβα : β < α),
      (rho γ α (hγβ.trans hβα).le).hom =
        (S.restrictionComp (T γ) (T β) (T α) (hmono hγβ.le) (hmono hβα.le)).hom.app (A α).obj ≫
          (S.restriction (T γ) (T β) (hmono hγβ.le)).map (rho β α hβα.le).hom ≫
            (rho γ β hγβ.le).hom := by
    intro γ β α hγβ hβα
    exact (comp_hom_eq_of_unique (hmono hβα.le) (hmono hγβ.le) (A α) (rho β α hβα.le)
      (hrho β α hβα.le) (rho γ α (hγβ.trans hβα).le) (hrhouniq γ α (hγβ.trans hβα).le)
      (rho γ β hγβ.le) (hrho γ β hγβ.le)).symm
  obtain ⟨F, I, hsupp, hqi, hK, hrhoF⟩ := producesComplexSystem S E T (fun β α h => hmono h)
    (fun α => (A α).obj)
    (fun α i hi => (A α).subsingleton_shiftedHom_self (hT α) hinter hExt i hi)
    (fun β α h => rho β α h.le) hcocycle
  let sigma : ∀ α : E, (S.restriction (T α) (⨆ α : E, T α) (hTV α)).obj
      (glueingObjectOver (⨆ α : E, T α) F) ≅ (A α).obj := fun α =>
    glueingRestrictionIsoOver (⨆ α : E, T α) T F I hsupp
      (glueingComplexSupportIso (⨆ α : E, T α) T F I hsupp hTV) hqi hTV S α ≪≫ hK α
  have hc : IsCompatibleAlongChain S T hmono hTV A (glueingObjectOver (⨆ α : E, T α) F) sigma :=
    fun β α h => ⟨(rho β α h.le).hom, hrho β α h.le, by
      rw [← hrhoF β α h]
      exact glueing_compatibility_of_iso_over (⨆ α : E, T α) T F I hsupp
        (glueingComplexSupportIso (⨆ α : E, T α) T F I hsupp hTV) hqi hTV S
        (fun α => (A α).obj) hK (hmono h.le) h.le⟩
  exact nonempty_solutionOver_of_subcollectionSolution S (opensBelowChain S T)
    (opensBelowChain_subset S T) (fun W hW hWT => eq_sSup_opensBelowChain S T hT hinter W hW hWT)
    (inf_eq_sSup_opensBelowChain S T hinter) hExt
    (chainSolutionOverSubcollection hmono hTV A _ sigma hc)

/-! ### Tag 0D6C -/

section Stages

variable {ι : Type*} [LinearOrder ι] (U : ι → Opens X.carrier)

/-- The union of the members of a well ordered family up to a given index. -/
def stageUpTo (α : ι) : Opens X.carrier :=
  ⨆ (β : ι) (_ : β ≤ α), U β

variable {U}

/-- Each member of the family up to a given index is contained in the stage at that index. -/
theorem le_stageUpTo {β α : ι} (h : β ≤ α) : U β ≤ stageUpTo U α :=
  le_iSup₂_of_le (f := fun (β : ι) (_ : β ≤ α) => U β) β h le_rfl

/-- The stages of the family increase with the index. -/
theorem stageUpTo_monotone : Monotone (stageUpTo U) :=
  fun _ _ h => iSup₂_le fun _ hβ => le_stageUpTo (hβ.trans h)

/-- If every member of the family belongs to the collection, then each stage is the union of the
members of the collection it contains. -/
theorem stageUpTo_eq_sSup_covered (S : LocallyGiven X) (hU : ∀ i : ι, U i ∈ S.opens) (α : ι) :
    stageUpTo U α = sSup {W | W ∈ S.opens ∧ W ≤ stageUpTo U α} :=
  le_antisymm (iSup₂_le fun β hβ => le_sSup ⟨hU β, le_stageUpTo hβ⟩) (sSup_le fun _ hW => hW.2)

/-- **A stage is the union of the earlier stages and its own member.** -/
theorem stageUpTo_eq_sup (α : ι) :
    stageUpTo U α = U α ⊔ ⨆ β : Set.Iio α, stageUpTo U β.1 := by
  refine le_antisymm (iSup₂_le fun β hβ => ?_)
    (sup_le (le_stageUpTo le_rfl) (iSup_le fun β => stageUpTo_monotone β.2.le))
  rcases hβ.eq_or_lt with rfl | hlt
  · exact le_sup_left
  · exact le_sup_of_le_right ((le_stageUpTo le_rfl).trans (le_iSup_of_le ⟨β, hlt⟩ le_rfl))

end Stages

/-- **Existence of a solution, for a collection enumerated by a well ordered set.** Every stage
`⋃_{β ≤ α} U_β` carries a solution by transfinite induction: the earlier stages glue along the
well ordered chain they form, by `Stacks.DerivedGlueing.nonempty_solutionOver_iSup_of_wellOrdered`,
and the member `U_α` is adjoined by the two-open case of [Stacks, Tag 0D6A].  A last glueing
along all the stages gives a solution over the union of the family. -/
theorem nonempty_solutionOver_iSup_of_wellOrdered_family (S : LocallyGiven X)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i))
    {ι : Type u} [LinearOrder ι] [WellFoundedLT ι] (U : ι → Opens X.carrier)
    (hU : ∀ i : ι, U i ∈ S.opens) :
    Nonempty (SolutionOver S (⨆ i : ι, U i)) := by
  have hstage : ∀ α : ι, Nonempty (SolutionOver S (stageUpTo U α)) := by
    intro α
    induction α using WellFoundedLT.induction with
    | ind α ih =>
      obtain ⟨B⟩ := nonempty_solutionOver_iSup_of_wellOrdered S hinter hExt
        (fun β : Set.Iio α => stageUpTo U β.1) (fun _ _ h => stageUpTo_monotone h)
        (fun β => stageUpTo_eq_sSup_covered S hU β.1) (fun β => (ih β.1 β.2).some)
      have hM := iSup_eq_sSup_covered S (fun β : Set.Iio α => stageUpTo U β.1)
        (fun β => stageUpTo_eq_sSup_covered S hU β.1)
      rw [stageUpTo_eq_sup]
      exact gluesAlongTwoOpens_unconditional S (U α) (hU α) _ hM
        (inf_eq_sSup_covered S hinter (hU α) hM) hinter hExt (selfSolutionOver S (U α) (hU α)) B
  obtain ⟨B⟩ := nonempty_solutionOver_iSup_of_wellOrdered S hinter hExt (stageUpTo U)
    stageUpTo_monotone (stageUpTo_eq_sSup_covered S hU) fun α => (hstage α).some
  have heq : (⨆ α : ι, stageUpTo U α) = ⨆ i : ι, U i :=
    le_antisymm (iSup_le fun _ => iSup₂_le fun β _ => le_iSup U β)
      (iSup_le fun i => (le_stageUpTo le_rfl).trans (le_iSup (stageUpTo U) i))
  rw [heq] at B
  exact ⟨B⟩

/-- The members of a collection of opens, as a type carrying no order of its own. -/
def CollectionIndex (ℬ : Set (Opens X.carrier)) : Type u := ℬ

/-- **Every open that is the union of the members of the collection it contains carries a
solution**, when the intersection of two members is the union of the members contained in it and
the prescribed objects have no negative self-Ext.  The members contained in the open are well
ordered by Zermelo's theorem and
`Stacks.DerivedGlueing.nonempty_solutionOver_iSup_of_wellOrdered_family` applies. -/
theorem nonempty_solutionOver_of_eq_sSup_covered (S : LocallyGiven X)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i))
    {O : Opens X.carrier} (hO : O = sSup {W | W ∈ S.opens ∧ W ≤ O}) :
    Nonempty (SolutionOver S O) := by
  obtain ⟨hlin, hwf⟩ := exists_wellFoundedLT (CollectionIndex {W | W ∈ S.opens ∧ W ≤ O})
  let := hlin
  have := hwf
  obtain ⟨B⟩ := nonempty_solutionOver_iSup_of_wellOrdered_family S hinter hExt
    (fun i : CollectionIndex {W | W ∈ S.opens ∧ W ≤ O} =>
      (show ↥{W | W ∈ S.opens ∧ W ≤ O} from i).1)
    fun i => (show ↥{W | W ∈ S.opens ∧ W ≤ O} from i).2.1
  have h : (⨆ i : CollectionIndex {W | W ∈ S.opens ∧ W ≤ O},
      (show ↥{W | W ∈ S.opens ∧ W ≤ O} from i).1) = O :=
    (sSup_eq_iSup' {W | W ∈ S.opens ∧ W ≤ O}).symm.trans hO.symm
  rw [h] at B
  exact ⟨B⟩

/-- **[Stacks, Tag 0D6C], existence.** In Situation 0D67, if the members of the collection cover
`X`, the intersection of two members is the union of the members contained in it, and the
prescribed objects have no negative self-Ext, then the system has a solution. -/
theorem exists_solution_of_covers_unconditional (S : LocallyGiven X) (hcover : sSup S.opens = ⊤)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i)) :
    Nonempty (Solution S) :=
  ⟨(nonempty_solutionOver_of_eq_sSup_covered S hinter hExt
    (top_eq_sSup_covered_of_sSup_eq_top S hcover)).some.toSolution⟩

/-- **Glueing along a chain holds for every system.** The union of a chain of opens, each the
union of the members of the collection it contains, is again one, and so carries a solution by
`Stacks.DerivedGlueing.nonempty_solutionOver_of_eq_sSup_covered`. -/
theorem gluesAlongChain_unconditional (S : LocallyGiven X) : GluesAlongChain S :=
  fun 𝒞 _ _ hcov hinter hExt _ =>
    nonempty_solutionOver_of_eq_sSup_covered S hinter hExt (sSup_eq_sSup_covered S 𝒞 hcov)

/-- **Glueing along a chain with no greatest element holds for every system.** -/
theorem gluesAlongProperChain_unconditional (S : LocallyGiven X) : GluesAlongProperChain S :=
  fun 𝒞 _ _ _ hcov hinter hExt _ =>
    nonempty_solutionOver_of_eq_sSup_covered S hinter hExt (sSup_eq_sSup_covered S 𝒞 hcov)

/-- **[Stacks, Tag 0D6C] (BBD gluing lemma).** In Situation 0D67 suppose that the members of the
collection cover `X`, that for two members `U, V` the intersection `U ∩ V` is the union of the
members contained in it, and that `Ext^i(K_U, K_U) = 0` for `i < 0` and every member `U`.  Then
the system has a solution, and any two solutions are identified by exactly one isomorphism of
solutions.

A solution is a `Stacks.DerivedGlueing.Solution`: an object `K` of `D(𝒪_X)` with isomorphisms
`ρ_U : K|_U ≅ K_U` satisfying `ρ^U_V ∘ ρ_U|_V = ρ_V`.  The conclusion
`Stacks.DerivedGlueing.Solution.IsCompatibleHom A B ψ.hom` says that `ψ` is compatible with the
`ρ_U` of the two solutions. -/
@[stacks 0D6C "existence of a solution `(K, ρ_U)` and its uniqueness up to unique isomorphism,
  for a collection satisfying (1) `hcover`, (2) `hinter` and (3) `hExt`"]
theorem exists_solution_and_unique_solutionIso_of_covers_unconditional (S : LocallyGiven X)
    (hcover : sSup S.opens = ⊤)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i)) :
    Nonempty (Solution S) ∧
      ∀ A B : Solution S, ∃! ψ : A.obj ≅ B.obj, A.IsCompatibleHom B ψ.hom :=
  ⟨exists_solution_of_covers_unconditional S hcover hinter hExt,
    fun A B => exists_unique_solutionIso_of_covers_unconditional S hcover hinter hExt A B⟩

end Stacks.DerivedGlueing

end
