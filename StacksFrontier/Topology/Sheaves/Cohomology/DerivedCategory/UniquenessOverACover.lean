module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.UniquenessOfASolution

/-!
# Uniqueness of a solution up to unique isomorphism, over a cover

Let `(X, 𝒪_X)` be a ringed space and let `(ℬ, K_U, ρ^U_V)` be a system of locally given derived
objects on it, as in Situation 0D67.  Both [Stacks, Tag 0D6A] and [Stacks, Tag 0D6C] assert that
a solution *exists* and is *unique up to unique isomorphism*.  This file derives the uniqueness
from the glueing of morphisms, `Stacks.DerivedGlueing.HasGluingForHomsOver`.

A morphism of solutions is a morphism of their global objects commuting with their
identifications on every member of `ℬ`, which is
`Stacks.DerivedGlueing.Solution.IsCompatibleHom`; "unique up to unique isomorphism" is that
there is exactly one isomorphism of solutions between any two solutions.

## Main definitions

* `Stacks.DerivedGlueing.Solution.IsCompatibleHom`: a morphism of solutions.
* `Stacks.DerivedGlueing.restrictionSelfIso`: restriction from an open to itself is the identity.

## Main results

* `Stacks.DerivedGlueing.exists_unique_solutionIso_of_top_mem`: **[Stacks, Tag 0D6A]**,
  uniqueness up to unique isomorphism when a single member of the collection is all of `X`.  This
  is the case `n = 1` of the tag and needs **no** granted hypothesis; together with
  `Stacks.DerivedGlueing.exists_solution_of_top_mem` it is the whole of Tag 0D6A for `n = 1`.
* `Stacks.DerivedGlueing.exists_unique_solutionIso_of_finite_cover`: **[Stacks, Tag 0D6A]**,
  uniqueness up to unique isomorphism, granted `HasGluingForHomsOver`.
* `Stacks.DerivedGlueing.exists_unique_solutionIso_of_covers`: uniqueness up to unique
  isomorphism over a covering collection, from `HasGluingForHomsOver`.

## The route

The source deduces uniqueness in both tags from the *uniqueness clause of*
[Stacks, Tag 0D68], the predicate `Stacks.DerivedGlueing.HasUniqueSolutionOverIso`, which
`Stacks.DerivedGlueing.hasUniqueSolutionOverIso_of_hasGluingForHomsOver` derives from
`Stacks.DerivedGlueing.HasGluingForHomsOver` — the sheaf condition of [Stacks, Tag 0D66]
part (2) for the rule `W ↦ Hom(K|_W, L|_W)`.  That sheaf condition holds for every system, by
`Stacks.DerivedGlueing.hasGluingForHomsOver_of_covers`.

The case `⊤ ∈ ℬ` needs no sheaf condition.  There the whole of the compatibility is forced by
its instance at `⊤`, by `Stacks.DerivedGlueing.Solution.isCompatibleHom_of_top`, and the
isomorphism is read off the identification `Stacks.DerivedGlueing.restrictionSelfIso` of
restriction from `⊤` to `⊤` with the identity functor; that identification is the unit of
`j_! ⊣ j^*`, which is invertible by [Stacks, Tag 00AB].

## Implementation notes

The cover hypotheses of the two tags are used only through the single consequence that `⊤` is
the union of the members of `ℬ` contained in it, which is what
`Stacks.DerivedGlueing.HasUniqueSolutionOverIso` asks of the open it is applied to.  So neither
theorem below needs the cover to be nonempty, and the version for 0D6A does not
assume `Finset.Nonempty`, unlike
`Stacks.DerivedGlueing.exists_solution_of_finite_cover`: an empty cover of `X` forces `X = ∅`,
where the statement still holds.

## References

* [Stacks Project, Tag 0D6A](https://stacks.math.columbia.edu/tag/0D6A)
* [Stacks Project, Tag 0D6C](https://stacks.math.columbia.edu/tag/0D6C)
* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
* [Stacks Project, Tag 00AB](https://stacks.math.columbia.edu/tag/00AB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open ExtensionByZeroModules

namespace Stacks.DerivedGlueing

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}}

/-! ### Restriction from an open to itself -/

/-- **Restriction of sheaves of modules from `U` to `U` is the identity.** Restriction is
extension by zero to `X` followed by restriction to the target open, so restriction from `U` to
`U` is `j^* j_!`, and the unit of `j_! ⊣ j^*` is invertible ([Stacks, Tag 00AB]). -/
def openModuleRestrictionSelfIso (X : RingedSpace.{u, u}) (U : Opens X.carrier) (hUU : U ≤ U) :
    openModuleRestriction X U U hUU ≅
      𝟭 (SheafOfModules.{u} (restrictedRingSheaf X U)) :=
  (@asIso _ _ _ _ (jShriekAdjunction U (underlyingRingSheaf X)).unit
    (isIso_jShriekAdjunction_unit U (underlyingRingSheaf X))).symm

/-- **The displayed restriction from `U` to `U` is the identity functor.** The displayed
restriction is the functor induced on derived categories by restriction of complexes of sheaves,
by `Stacks.DerivedGlueing.restrictionIsoMapDerivedCategory`, and that restriction is the
identity, by `Stacks.DerivedGlueing.openModuleRestrictionSelfIso`. -/
def restrictionSelfIso (S : LocallyGiven X) (U : Opens X.carrier) (hUU : U ≤ U) :
    S.restriction U U hUU ≅ 𝟭 (OpenDerivedCategory X U) :=
  restrictionIsoMapDerivedCategory S U U hUU ≪≫
    mapDerivedCategoryCongr (openModuleRestrictionSelfIso X U hUU) ≪≫
    Stacks.Homology.mapDerivedCategoryIdIso

/-- Restriction from `U` to `U` carries a morphism to its conjugate by
`Stacks.DerivedGlueing.restrictionSelfIso`. -/
theorem restrictionSelfIso_naturality (S : LocallyGiven X) (U : Opens X.carrier) (hUU : U ≤ U)
    {K L : OpenDerivedCategory X U} (f : K ⟶ L) :
    (S.restriction U U hUU).map f ≫ ((restrictionSelfIso S U hUU).app L).hom =
      ((restrictionSelfIso S U hUU).app K).hom ≫ f :=
  (restrictionSelfIso S U hUU).hom.naturality f

/-- **Restriction from `U` to `U` is faithful**, being the identity functor. -/
theorem restrictionSelf_map_injective (S : LocallyGiven X) (U : Opens X.carrier) (hUU : U ≤ U)
    {K L : OpenDerivedCategory X U} {f g : K ⟶ L}
    (h : (S.restriction U U hUU).map f = (S.restriction U U hUU).map g) : f = g := by
  have h1 := restrictionSelfIso_naturality S U hUU f
  rw [h, restrictionSelfIso_naturality S U hUU g] at h1
  exact ((cancel_epi ((restrictionSelfIso S U hUU).app K).hom).mp h1).symm

/-! ### Morphisms of solutions -/

/-- **A morphism of solutions** (Situation 0D67): a morphism between the global objects of two
solutions commuting with their identifications on every member of the collection.  This is
`Stacks.DerivedGlueing.SolutionOver.IsCompatibleHom` read at the open `⊤`. -/
def Solution.IsCompatibleHom {S : LocallyGiven X} (A B : Solution S) (ψ : A.obj ⟶ B.obj) :
    Prop :=
  ∀ (U : Opens X.carrier) (hU : U ∈ S.opens),
    (S.restriction U ⊤ le_top).map ψ ≫ (B.rho U hU).hom = (A.rho U hU).hom

/-- A morphism of solutions is a morphism of the solutions they define over `⊤`. -/
theorem Solution.isCompatibleHom_toSolutionOver {S : LocallyGiven X} {A B : Solution S}
    {ψ : A.obj ⟶ B.obj} (hψ : A.IsCompatibleHom B ψ) :
    A.toSolutionOver.IsCompatibleHom B.toSolutionOver ψ :=
  fun U hU _ => hψ U hU

/-- A morphism of the solutions over `⊤` defined by two solutions is a morphism of
solutions. -/
theorem Solution.isCompatibleHom_of_toSolutionOver {S : LocallyGiven X} {A B : Solution S}
    {ψ : A.obj ⟶ B.obj} (hψ : A.toSolutionOver.IsCompatibleHom B.toSolutionOver ψ) :
    A.IsCompatibleHom B ψ :=
  fun U hU => hψ U hU le_top

/-! ### The case of a single member: Tag 0D6A for `n = 1` -/

/-- **Compatibility at `⊤` forces compatibility everywhere, when `⊤` is a member of the
collection.** The identification of a solution over a member `W` is determined by its
identification over `⊤` and the prescribed transition `ρ^⊤_W`, by the compatibility of the
solution; so a morphism commuting with the identifications over `⊤` commutes with all of them,
by the naturality of the comparison of restriction in one and in two steps. -/
theorem Solution.isCompatibleHom_of_top {S : LocallyGiven X} (htop : ⊤ ∈ S.opens)
    (A B : Solution S) (ψ : A.obj ⟶ B.obj)
    (h : (S.restriction ⊤ ⊤ le_top).map ψ ≫ (B.rho ⊤ htop).hom = (A.rho ⊤ htop).hom) :
    A.IsCompatibleHom B ψ := by
  intro W hW
  rw [← A.compatibility W ⊤ le_top htop hW, ← B.compatibility W ⊤ le_top htop hW,
    ← Category.assoc, (S.restrictionComp W ⊤ ⊤ le_top le_top).hom.naturality ψ,
    Functor.comp_map, Category.assoc, ← Functor.map_comp_assoc, h]

/-- **[Stacks, Tag 0D6A] when the cover has a single member: uniqueness up to unique
isomorphism.** If the whole of `X` belongs to the collection, then any two solutions are
identified by exactly one isomorphism of solutions.

This is the case `n = 1` of the tag: restriction from `⊤` to `⊤` is the identity functor, by
`Stacks.DerivedGlueing.restrictionSelfIso`, so the identifications over `⊤` of the two solutions
compose to the required isomorphism and determine it; and compatibility over `⊤` forces
compatibility over every member, by `Stacks.DerivedGlueing.Solution.isCompatibleHom_of_top`.

Together with `Stacks.DerivedGlueing.exists_solution_of_top_mem` this is the whole of Tag 0D6A
for `n = 1`. -/
@[stacks 0D6A "uniqueness up to unique isomorphism when a single member of the collection is all
  of X, the case n = 1"]
theorem exists_unique_solutionIso_of_top_mem (S : LocallyGiven X) (htop : ⊤ ∈ S.opens)
    (A B : Solution S) :
    ∃! φ : A.obj ≅ B.obj, A.IsCompatibleHom B φ.hom := by
  set φ : A.obj ≅ B.obj := ((restrictionSelfIso S ⊤ le_top).app A.obj).symm ≪≫ A.rho ⊤ htop ≪≫
    (B.rho ⊤ htop).symm ≪≫ (restrictionSelfIso S ⊤ le_top).app B.obj with hφdef
  have key : (S.restriction ⊤ ⊤ le_top).map φ.hom =
      (A.rho ⊤ htop).hom ≫ (B.rho ⊤ htop).inv := by
    rw [← cancel_mono ((restrictionSelfIso S ⊤ le_top).app B.obj).hom,
      restrictionSelfIso_naturality, hφdef]
    simp
  refine ⟨φ, Solution.isCompatibleHom_of_top htop A B _ ?_, fun ψ hψ => Iso.ext ?_⟩
  · rw [key, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · refine restrictionSelf_map_injective S ⊤ le_top ?_
    rw [key, ← hψ ⊤ htop, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-! ### `⊤` as a union of members of the collection -/

/-- **The whole space is the union of the members of the collection contained in it**, when the
collection covers it. -/
theorem top_eq_sSup_covered_of_sSup_eq_top (S : LocallyGiven X) (hcover : sSup S.opens = ⊤) :
    (⊤ : Opens X.carrier) = sSup {W | W ∈ S.opens ∧ W ≤ ⊤} :=
  le_antisymm
    ((le_of_eq hcover.symm).trans (sSup_le fun _ hW => le_sSup ⟨hW, le_top⟩))
    (sSup_le fun _ hW => hW.2)

/-- **The whole space is the union of the members of the collection contained in it**, when
finitely many members cover it. -/
theorem top_eq_sSup_covered_of_finsetSup_eq_top (S : LocallyGiven X)
    (s : Finset (Opens X.carrier)) (hmem : ∀ U ∈ s, U ∈ S.opens) (hcover : s.sup id = ⊤) :
    (⊤ : Opens X.carrier) = sSup {W | W ∈ S.opens ∧ W ≤ ⊤} :=
  by simpa only [hcover] using finsetSup_eq_sSup_covered S s hmem

/-! ### Uniqueness over a cover, from the uniqueness clause of Tag 0D68 -/

/-- **Uniqueness of a solution up to unique isomorphism, granted the uniqueness clause of
[Stacks, Tag 0D68].** A solution is a solution over `⊤`, and when the collection covers `X` the
open `⊤` is the union of the members contained in it, so the granted clause applies there.

This carries the granted hypothesis and is therefore kept private and untagged; the tagged
statements below discharge it from `Stacks.DerivedGlueing.HasGluingForHomsOver`. -/
private theorem exists_unique_solutionIso_of_hasUniqueSolutionOverIso (S : LocallyGiven X)
    (huniq : HasUniqueSolutionOverIso S)
    (hcover : (⊤ : Opens X.carrier) = sSup {W | W ∈ S.opens ∧ W ≤ ⊤})
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i))
    (A B : Solution S) :
    ∃! φ : A.obj ≅ B.obj, A.IsCompatibleHom B φ.hom := by
  obtain ⟨φ, hφ, hφuniq⟩ := huniq ⊤ hcover hinter hExt A.toSolutionOver B.toSolutionOver
  exact ⟨φ, Solution.isCompatibleHom_of_toSolutionOver hφ,
    fun ψ hψ => hφuniq ψ (Solution.isCompatibleHom_toSolutionOver hψ)⟩

/-- **Uniqueness of a solution over a finite cover, from the glueing of morphisms.** In
Situation 0D67, assume that `X = U_1 ∪ … ∪ U_n` with `U_i` in the collection, that the
intersection of two members of the collection is the union of the members contained in it, that
the prescribed objects have no negative self-Ext, and that `S` satisfies
`Stacks.DerivedGlueing.HasGluingForHomsOver`, the sheaf condition of [Stacks, Tag 0D66] part (2).
Then any two solutions are identified by exactly one isomorphism of solutions.

The sheaf condition yields the uniqueness clause of [Stacks, Tag 0D68] by
`Stacks.DerivedGlueing.hasUniqueSolutionOverIso_of_hasGluingForHomsOver`.  The cover may be
empty: it enters only through `Stacks.DerivedGlueing.top_eq_sSup_covered_of_finsetSup_eq_top`. -/
theorem exists_unique_solutionIso_of_finite_cover (S : LocallyGiven X)
    (hglueHom : HasGluingForHomsOver S)
    (s : Finset (Opens X.carrier)) (hmem : ∀ U ∈ s, U ∈ S.opens) (hcover : s.sup id = ⊤)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i))
    (A B : Solution S) :
    ∃! φ : A.obj ≅ B.obj, A.IsCompatibleHom B φ.hom :=
  exists_unique_solutionIso_of_hasUniqueSolutionOverIso S
    (hasUniqueSolutionOverIso_of_hasGluingForHomsOver S hglueHom)
    (top_eq_sSup_covered_of_finsetSup_eq_top S s hmem hcover) hinter hExt A B

/-- **Uniqueness of a solution up to unique isomorphism, from the glueing of morphisms.** In
Situation 0D67, assume the sheaf condition `Stacks.DerivedGlueing.HasGluingForHomsOver`, that the
members of the collection cover `X`, that the intersection of two members is the union of the
members contained in it, and that the prescribed objects have no negative self-Ext.  Then any two
solutions are identified by exactly one isomorphism of solutions. -/
theorem exists_unique_solutionIso_of_covers (S : LocallyGiven X)
    (hglueHom : HasGluingForHomsOver S) (hcover : sSup S.opens = ⊤)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i))
    (A B : Solution S) :
    ∃! φ : A.obj ≅ B.obj, A.IsCompatibleHom B φ.hom :=
  exists_unique_solutionIso_of_hasUniqueSolutionOverIso S
    (hasUniqueSolutionOverIso_of_hasGluingForHomsOver S hglueHom)
    (top_eq_sSup_covered_of_sSup_eq_top S hcover) hinter hExt A B

end Stacks.DerivedGlueing

end
