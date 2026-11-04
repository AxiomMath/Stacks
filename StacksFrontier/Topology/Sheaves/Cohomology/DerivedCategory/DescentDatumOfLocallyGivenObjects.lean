module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.GlueingOverAFiniteCover
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.RestrictionComparisonCoherence

/-!
# The descent datum attached to a system of locally given derived objects

Let `(X, 𝒪_X)` be a ringed space and let `(ℬ, K_U, ρ^U_V)` be a system of locally given derived
objects on it, as in Situation 0D67.  Assume that the intersection of two members of `ℬ` is the
union of the members contained in it and that `Ext^i(K_U, K_U) = 0` for `i < 0` and `U ∈ ℬ`.
For `U, V ∈ ℬ` the two restrictions `K_U|_{U ∩ V}` and `K_V|_{U ∩ V}` are both solutions of the
system induced on `U ∩ V`, so there is a unique isomorphism

`ρ_{U,V} : K_U|_{U ∩ V} ⟶ K_V|_{U ∩ V}`

compatible with the prescribed transitions on the members of `ℬ` contained in `U ∩ V`, and these
isomorphisms satisfy the cocycle condition over a triple intersection.  The family
`(K_U, ρ_{U,V})` is the descent datum of the covering `X = ⋃_{U ∈ ℬ} U` described in
[Stacks, Tag 0D69]; the existence of a solution is the effectivity of that datum.

This file carries out that argument.  The system induced on `U ∩ V` is not formed on the ringed
space `U ∩ V`; everything is read inside `X`, through `Stacks.DerivedGlueing.SolutionOver`, a
solution of the system over an open subset of `X`.

## Main definitions

* `Stacks.DerivedGlueing.SolutionOver.IsCompatibleHom`: a morphism of solutions over an open
  subset, i.e. one commuting with their identifications.
* `Stacks.DerivedGlueing.HasUniqueSolutionOverIso`: the uniqueness clause of
  [Stacks, Tag 0D68], relativized to an open subset of `X`.
* `Stacks.DerivedGlueing.SolutionOver.restrictOpen`: the restriction of a solution over an open
  subset to a smaller open subset.
* `Stacks.DerivedGlueing.IsOverlapHom`: compatibility of a morphism between the restrictions of
  two prescribed objects with the prescribed transitions below the overlap.
* `Stacks.DerivedGlueing.restrictOverlapHom`, `Stacks.DerivedGlueing.restrictOverlapIso`: such a
  morphism, transported to a smaller open subset.

## Main results

* `Stacks.DerivedGlueing.exists_unique_overlapIso`: **[Stacks, Tag 0D69]**, the unique
  compatible isomorphism `ρ_{U,V}` between the two restrictions to an overlap.
* `Stacks.DerivedGlueing.restrictOverlapHom_cocycle`: **[Stacks, Tag 0D69]**, the cocycle
  condition `ρ_{U,W} = ρ_{V,W} ∘ ρ_{U,V}` over a triple intersection.
* `Stacks.DerivedGlueing.inf_inf_eq_sSup`: a triple intersection of members of the collection is
  the union of the members contained in it.

## The hypothesis the two theorems take, and why it is no longer owed

Tag 0D69 is a consequence of the *uniqueness* clause of [Stacks, Tag 0D68], and the two theorems
below take that clause as an explicit hypothesis, in the relativized form
`Stacks.DerivedGlueing.HasUniqueSolutionOverIso` — the uniqueness clause of 0D68 read over an
open subset of `X`, exactly as the source reads it, on the ringed space `U ∩ V`.

That hypothesis is **a theorem of this development**, at the source's hypothesis (1) and nothing
else: `Stacks.DerivedGlueing.hasUniqueSolutionOverIso_of_covers` proves it for every system whose
collection covers the space and whose pairwise intersections are unions of members.  So the two
theorems below are a conditional form kept for a consumer that has the clause by some other
route, and the two clauses of Tag 0D69 **at the source's own hypotheses and nothing else** are
`Stacks.DerivedGlueing.exists_unique_overlapIso_of_covers` and
`Stacks.DerivedGlueing.restrictOverlapHom_cocycle_of_covers`, in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.HomVanishingOverASubcollection`.

The route to that discharge is the source's own.  The clause follows from
`Stacks.DerivedGlueing.HasGluingForHomsOver` by
`Stacks.DerivedGlueing.hasUniqueSolutionOverIso_of_hasGluingForHomsOver` — the statement that a
compatible family of morphisms between the restrictions of two objects over an open subset to the
members of the collection contained in it comes from a unique morphism, which is the sheaf
condition of [Stacks, Tag 0D66] part (2); and that condition is proved at every open the
collection covers by `Stacks.DerivedGlueing.hasGluingForHomsAt_of_covers`, by running the
whole-space statement on the ringed space `X|O`.  See the module documentation of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.UniquenessOfASolution` and of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.HomVanishingOverASubcollection`.

Neither theorem below is vacuous, and the witnesses are not only the degenerate ones:
`Stacks.DerivedGlueing.hasUniqueSolutionOverIso_of_sSup_covered_mem` proves the hypothesis
outright for every system whose collection contains each open it covers — the saturated case, at
which
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.UniquenessOverASaturatedCollection`
also states both theorems with every binder but the source's negative self-Ext hypothesis
discharged — while `Stacks.DerivedGlueing.hasUniqueSolutionOverIso_of_covers` covers collections
that are **not** saturated, which is the case Tags 0D6A to 0D6C need.

The theorems take nothing else.  The associativity of the comparisons `restrictionComp` of
Situation 0D67 along a chain `W ⊆ T ⊆ O ⊆ U` of opens, which this argument needs at exactly one
point,
`Stacks.DerivedGlueing.restrictOpen_comparison_isCompatibleHom`, holds for every system and is
`Stacks.DerivedGlueing.LocallyGiven.restrictionComp_pentagon`.

## References

* [Stacks Project, Tag 0D69](https://stacks.math.columbia.edu/tag/0D69)
* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Stacks.DerivedGlueing

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}}

/-! ### Morphisms of solutions over an open subset -/

/-- **A morphism of solutions over an open subset.** A morphism between the objects of two
solutions over `O` commuting with their identifications on every member of the collection
contained in `O`. -/
def SolutionOver.IsCompatibleHom {S : LocallyGiven X} {O : Opens X.carrier}
    (A B : SolutionOver S O) (ψ : A.obj ⟶ B.obj) : Prop :=
  ∀ (W : Opens X.carrier) (hW : W ∈ S.opens) (hWO : W ≤ O),
    (S.restriction W O hWO).map ψ ≫ (B.rho W hW hWO).hom = (A.rho W hW hWO).hom

/-- The composition of two morphisms of solutions is a morphism of solutions. -/
theorem SolutionOver.IsCompatibleHom.comp {S : LocallyGiven X} {O : Opens X.carrier}
    {A B C : SolutionOver S O} {ψ : A.obj ⟶ B.obj} {χ : B.obj ⟶ C.obj}
    (hψ : A.IsCompatibleHom B ψ) (hχ : B.IsCompatibleHom C χ) :
    A.IsCompatibleHom C (ψ ≫ χ) := by
  intro W hW hWO
  rw [Functor.map_comp, Category.assoc, hχ W hW hWO, hψ W hW hWO]

/-- The inverse of an isomorphism of solutions is a morphism of solutions. -/
theorem SolutionOver.IsCompatibleHom.inv {S : LocallyGiven X} {O : Opens X.carrier}
    {A B : SolutionOver S O} {ψ : A.obj ≅ B.obj} (hψ : A.IsCompatibleHom B ψ.hom) :
    B.IsCompatibleHom A ψ.inv := by
  intro W hW hWO
  rw [← hψ W hW hWO, ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-! ### The uniqueness clause of Tag 0D68, over an open subset -/

/-- **The uniqueness clause of [Stacks, Tag 0D68], relativized to an open subset.** Let `O` be
an open subset of `X` which is the union of the members of the collection contained in it.  If
the intersection of two members of the collection is the union of the members contained in it,
and if the prescribed objects have no negative self-Ext, then two solutions over `O` are
identified by a unique isomorphism of solutions.

The source proves this by forming the induced system on the ringed space `O` and applying
[Stacks, Tag 0D68] there.  That is also how this development proves it, in
`Stacks.DerivedGlueing.hasUniqueSolutionOverIso_of_covers`; the two theorems of Tag 0D69 below
take it as an explicit hypothesis, for which see the section *The hypothesis the two theorems
take, and why it is no longer owed* of the module documentation. -/
def HasUniqueSolutionOverIso (S : LocallyGiven X) : Prop :=
  ∀ (O : Opens X.carrier), O = sSup {W | W ∈ S.opens ∧ W ≤ O} →
    (∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V}) →
    (∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i)) →
    ∀ A B : SolutionOver S O, ∃! φ : A.obj ≅ B.obj, A.IsCompatibleHom B φ.hom

/-! ### Restricting a solution to a smaller open subset -/

/-- **The restriction of a solution over `U` to a smaller open subset `O`.** Its object is the
restriction of the object of the given solution, and its identification over a member `W` of the
collection contained in `O` is the identification of the given solution over `W`, read through
the comparison of restriction from `U` to `W` with restriction through `O`. -/
def SolutionOver.restrictOpen {S : LocallyGiven X}
    {U : Opens X.carrier} (A : SolutionOver S U) (O : Opens X.carrier) (hOU : O ≤ U) :
    SolutionOver S O where
  obj := (S.restriction O U hOU).obj A.obj
  rho W hW hWO :=
    ((S.restrictionComp W O U hWO hOU).app A.obj).symm ≪≫ A.rho W hW (hWO.trans hOU)
  compatibility V W hWV hV hW hVO := by
    have key : (S.restrictionComp W V O hWV hVO).hom.app ((S.restriction O U hOU).obj A.obj) ≫
        (S.restriction W V hWV).map ((S.restrictionComp V O U hVO hOU).inv.app A.obj) =
        (S.restrictionComp W O U (hWV.trans hVO) hOU).inv.app A.obj ≫
          (S.restrictionComp W V U hWV (hVO.trans hOU)).hom.app A.obj := by
      rw [← cancel_epi ((S.restrictionComp W O U (hWV.trans hVO) hOU).hom.app A.obj),
        ← Category.assoc, S.restrictionComp_pentagon W V O U hWV hVO hOU A.obj,
        Iso.hom_inv_id_app_assoc,
        Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
        CategoryTheory.Functor.map_id]
      exact Category.comp_id _
    have hA := A.compatibility V W hWV hV hW (hVO.trans hOU)
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.map_comp, Category.assoc]
    rw [← Category.assoc, key, Category.assoc, hA]

/-- The underlying object of the restriction of a solution to `O` is the restriction of its
underlying object. -/
@[simp]
theorem SolutionOver.restrictOpen_obj {S : LocallyGiven X}
    {U : Opens X.carrier} (A : SolutionOver S U) (O : Opens X.carrier) (hOU : O ≤ U) :
    (A.restrictOpen O hOU).obj = (S.restriction O U hOU).obj A.obj :=
  rfl

/-- The comparison isomorphism of the restriction of a solution to `O` at `W` is the comparison
isomorphism of the solution at `W`, precomposed with the inverse of the comparison of restriction
in one and in two steps. -/
@[simp]
theorem SolutionOver.restrictOpen_rho {S : LocallyGiven X}
    {U : Opens X.carrier} (A : SolutionOver S U) (O : Opens X.carrier) (hOU : O ≤ U)
    (W : Opens X.carrier) (hW : W ∈ S.opens) (hWO : W ≤ O) :
    (A.restrictOpen O hOU).rho W hW hWO =
      ((S.restrictionComp W O U hWO hOU).app A.obj).symm ≪≫ A.rho W hW (hWO.trans hOU) :=
  rfl

/-- The comparison isomorphisms of the solution given by the prescribed object on `U` are the
isomorphisms `S.rho`. -/
@[simp]
theorem selfSolutionOver_rho (S : LocallyGiven X) (U : Opens X.carrier) (hU : U ∈ S.opens)
    (V : Opens X.carrier) (hV : V ∈ S.opens) (hVU : V ≤ U) :
    (selfSolutionOver S U hU).rho V hV hVU = S.rho V U hVU hU hV :=
  rfl

/-- **The restriction of a morphism of solutions.** The morphism induced on the restrictions to
a smaller open subset is again a morphism of solutions; only the naturality of the comparisons
is involved. -/
theorem isCompatibleHom_restrictOpen_aux {S : LocallyGiven X} {O : Opens X.carrier}
    {A B : SolutionOver S O} {ψ : A.obj ⟶ B.obj} (hψ : A.IsCompatibleHom B ψ)
    {T : Opens X.carrier} (hTO : T ≤ O) (W : Opens X.carrier) (hW : W ∈ S.opens)
    (hWT : W ≤ T) :
    (S.restriction T O hTO ⋙ S.restriction W T hWT).map ψ ≫
        ((S.restrictionComp W T O hWT hTO).inv.app B.obj ≫
          (B.rho W hW (hWT.trans hTO)).hom) =
      (S.restrictionComp W T O hWT hTO).inv.app A.obj ≫ (A.rho W hW (hWT.trans hTO)).hom := by
  rw [← Category.assoc, (S.restrictionComp W T O hWT hTO).inv.naturality ψ, Category.assoc,
    hψ W hW (hWT.trans hTO)]

/-- The restriction to `T` of a morphism of solutions over `O` is a morphism between the
restricted solutions. -/
theorem SolutionOver.IsCompatibleHom.restrictOpen {S : LocallyGiven X}
    {O : Opens X.carrier} {A B : SolutionOver S O}
    {ψ : A.obj ⟶ B.obj} (hψ : A.IsCompatibleHom B ψ) {T : Opens X.carrier} (hTO : T ≤ O) :
    (A.restrictOpen T hTO).IsCompatibleHom (B.restrictOpen T hTO)
      ((S.restriction T O hTO).map ψ) := fun W hW hWT =>
  isCompatibleHom_restrictOpen_aux hψ hTO W hW hWT

/-- **The comparison of restriction in one and in two steps is a morphism of solutions.** This
is the only point at which the coherence
`Stacks.DerivedGlueing.LocallyGiven.restrictionComp_pentagon` is used. -/
theorem restrictOpen_comparison_isCompatibleHom {S : LocallyGiven X}
    {U : Opens X.carrier} (A : SolutionOver S U)
    {O T : Opens X.carrier} (hOU : O ≤ U) (hTO : T ≤ O) :
    (A.restrictOpen T (hTO.trans hOU)).IsCompatibleHom
      ((A.restrictOpen O hOU).restrictOpen T hTO)
      ((S.restrictionComp T O U hTO hOU).hom.app A.obj) := by
  intro W hW hWT
  have key : (S.restriction W T hWT).map ((S.restrictionComp T O U hTO hOU).hom.app A.obj) =
      (S.restrictionComp W T U hWT (hTO.trans hOU)).inv.app A.obj ≫
        (S.restrictionComp W O U (hWT.trans hTO) hOU).hom.app A.obj ≫
          (S.restrictionComp W T O hWT hTO).hom.app ((S.restriction O U hOU).obj A.obj) := by
    rw [S.restrictionComp_pentagon W T O U hWT hTO hOU A.obj, Iso.inv_hom_id_app_assoc]
  simp only [SolutionOver.restrictOpen_rho, SolutionOver.restrictOpen_obj, Iso.trans_hom,
    Iso.symm_hom, Iso.app_inv, Category.assoc, key]
  simp only [Iso.hom_inv_id_app_assoc]

/-- The comparison of restriction in two and in one steps is a morphism of solutions. -/
theorem restrictOpen_comparison_inv_isCompatibleHom {S : LocallyGiven X}
    {U : Opens X.carrier} (A : SolutionOver S U)
    {O T : Opens X.carrier} (hOU : O ≤ U) (hTO : T ≤ O) :
    ((A.restrictOpen O hOU).restrictOpen T hTO).IsCompatibleHom
      (A.restrictOpen T (hTO.trans hOU))
      ((S.restrictionComp T O U hTO hOU).inv.app A.obj) :=
  SolutionOver.IsCompatibleHom.inv
    (A := A.restrictOpen T (hTO.trans hOU))
    (B := (A.restrictOpen O hOU).restrictOpen T hTO)
    (ψ := (S.restrictionComp T O U hTO hOU).app A.obj)
    (restrictOpen_comparison_isCompatibleHom A hOU hTO)

/-! ### Compatible morphisms between the restrictions to an overlap -/

/-- **Compatibility of a morphism between the restrictions of two prescribed objects.** Let `U`
and `V` be members of the collection and let `O` be an open subset of both.  A morphism
`K_U|_O ⟶ K_V|_O` is compatible when for every member `W` of the collection contained in `O` the
prescribed transition `ρ^U_W` is the composition of its restriction to `W` with `ρ^V_W`. -/
def IsOverlapHom (S : LocallyGiven X) {U V : Opens X.carrier} (hU : U ∈ S.opens)
    (hV : V ∈ S.opens) {O : Opens X.carrier} (hOU : O ≤ U) (hOV : O ≤ V)
    (φ : (S.restriction O U hOU).obj (S.obj U hU) ⟶
      (S.restriction O V hOV).obj (S.obj V hV)) : Prop :=
  ∀ (W : Opens X.carrier) (hW : W ∈ S.opens) (hWO : W ≤ O),
    (S.restriction W O hWO).map φ ≫ (S.restrictionComp W O V hWO hOV).inv.app (S.obj V hV) ≫
        (S.rho W V (hWO.trans hOV) hV hW).hom =
      (S.restrictionComp W O U hWO hOU).inv.app (S.obj U hU) ≫
        (S.rho W U (hWO.trans hOU) hU hW).hom

/-- A compatible morphism between the restrictions to `O` of the prescribed objects on `U` and
on `V` is exactly a morphism of the solutions they define over `O`. -/
theorem isOverlapHom_iff {S : LocallyGiven X}
    {U V : Opens X.carrier} (hU : U ∈ S.opens) (hV : V ∈ S.opens) {O : Opens X.carrier}
    (hOU : O ≤ U) (hOV : O ≤ V)
    (φ : (S.restriction O U hOU).obj (S.obj U hU) ⟶
      (S.restriction O V hOV).obj (S.obj V hV)) :
    IsOverlapHom S hU hV hOU hOV φ ↔
      ((selfSolutionOver S U hU).restrictOpen O hOU).IsCompatibleHom
        ((selfSolutionOver S V hV).restrictOpen O hOV) φ :=
  Iff.rfl

/-- The composition of two compatible morphisms is compatible. -/
theorem IsOverlapHom.comp {S : LocallyGiven X} {U V W : Opens X.carrier} {hU : U ∈ S.opens}
    {hV : V ∈ S.opens} {hW : W ∈ S.opens} {O : Opens X.carrier} {hOU : O ≤ U} {hOV : O ≤ V}
    {hOW : O ≤ W}
    {φ : (S.restriction O U hOU).obj (S.obj U hU) ⟶ (S.restriction O V hOV).obj (S.obj V hV)}
    {ψ : (S.restriction O V hOV).obj (S.obj V hV) ⟶ (S.restriction O W hOW).obj (S.obj W hW)}
    (hφ : IsOverlapHom S hU hV hOU hOV φ) (hψ : IsOverlapHom S hV hW hOV hOW ψ) :
    IsOverlapHom S hU hW hOU hOW (φ ≫ ψ) := by
  intro T hT hTO
  rw [Functor.map_comp, Category.assoc, hψ T hT hTO, hφ T hT hTO]

/-! ### Transporting a compatible morphism to a smaller open subset -/

/-- **A morphism between the restrictions of two prescribed objects to an open subset `O`,
transported to a smaller open subset `T`.** -/
def restrictOverlapHom (S : LocallyGiven X) {U V : Opens X.carrier} (hU : U ∈ S.opens)
    (hV : V ∈ S.opens) {O : Opens X.carrier} (hOU : O ≤ U) (hOV : O ≤ V)
    {T : Opens X.carrier} (hTO : T ≤ O)
    (φ : (S.restriction O U hOU).obj (S.obj U hU) ⟶
      (S.restriction O V hOV).obj (S.obj V hV)) :
    (S.restriction T U (hTO.trans hOU)).obj (S.obj U hU) ⟶
      (S.restriction T V (hTO.trans hOV)).obj (S.obj V hV) :=
  (S.restrictionComp T O U hTO hOU).hom.app (S.obj U hU) ≫ (S.restriction T O hTO).map φ ≫
    (S.restrictionComp T O V hTO hOV).inv.app (S.obj V hV)

/-- **An isomorphism between the restrictions of two prescribed objects to an open subset `O`,
transported to a smaller open subset `T`.** -/
def restrictOverlapIso (S : LocallyGiven X) {U V : Opens X.carrier} (hU : U ∈ S.opens)
    (hV : V ∈ S.opens) {O : Opens X.carrier} (hOU : O ≤ U) (hOV : O ≤ V)
    {T : Opens X.carrier} (hTO : T ≤ O)
    (φ : (S.restriction O U hOU).obj (S.obj U hU) ≅
      (S.restriction O V hOV).obj (S.obj V hV)) :
    (S.restriction T U (hTO.trans hOU)).obj (S.obj U hU) ≅
      (S.restriction T V (hTO.trans hOV)).obj (S.obj V hV) :=
  (S.restrictionComp T O U hTO hOU).app (S.obj U hU) ≪≫ (S.restriction T O hTO).mapIso φ ≪≫
    ((S.restrictionComp T O V hTO hOV).app (S.obj V hV)).symm

/-- The forward morphism of `restrictOverlapIso` is `restrictOverlapHom` applied to the forward
morphism of `φ`. -/
@[simp]
theorem restrictOverlapIso_hom (S : LocallyGiven X) {U V : Opens X.carrier} (hU : U ∈ S.opens)
    (hV : V ∈ S.opens) {O : Opens X.carrier} (hOU : O ≤ U) (hOV : O ≤ V)
    {T : Opens X.carrier} (hTO : T ≤ O)
    (φ : (S.restriction O U hOU).obj (S.obj U hU) ≅
      (S.restriction O V hOV).obj (S.obj V hV)) :
    (restrictOverlapIso S hU hV hOU hOV hTO φ).hom =
      restrictOverlapHom S hU hV hOU hOV hTO φ.hom :=
  rfl

/-- **Compatibility is inherited by the transported morphism.** -/
theorem IsOverlapHom.restrict {S : LocallyGiven X}
    {U V : Opens X.carrier} {hU : U ∈ S.opens} {hV : V ∈ S.opens} {O : Opens X.carrier}
    {hOU : O ≤ U} {hOV : O ≤ V} {T : Opens X.carrier} (hTO : T ≤ O)
    {φ : (S.restriction O U hOU).obj (S.obj U hU) ⟶ (S.restriction O V hOV).obj (S.obj V hV)}
    (hφ : IsOverlapHom S hU hV hOU hOV φ) :
    IsOverlapHom S hU hV (hTO.trans hOU) (hTO.trans hOV)
      (restrictOverlapHom S hU hV hOU hOV hTO φ) :=
  (isOverlapHom_iff hU hV (hTO.trans hOU) (hTO.trans hOV) _).mpr
    ((restrictOpen_comparison_isCompatibleHom (selfSolutionOver S U hU) hOU hTO).comp
      ((((isOverlapHom_iff hU hV hOU hOV φ).mp hφ).restrictOpen hTO).comp
        (restrictOpen_comparison_inv_isCompatibleHom (selfSolutionOver S V hV) hOV hTO)))

/-! ### Triple intersections are covered by members of the collection -/

/-- **The covering condition on intersections passes to a triple intersection.** If the
intersection of two members of the collection is the union of the members contained in it, then
so is the intersection of three members. -/
theorem inf_inf_eq_sSup (S : LocallyGiven X)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (U V W : Opens X.carrier) (hU : U ∈ S.opens) (hV : V ∈ S.opens) (hW : W ∈ S.opens) :
    U ⊓ V ⊓ W = sSup {O | O ∈ S.opens ∧ O ≤ U ⊓ V ⊓ W} := by
  refine le_antisymm (fun x hx => ?_) (sSup_le fun O hO => hO.2)
  obtain ⟨hxUV, hxW⟩ := hx
  rw [hinter U hU V hV] at hxUV
  obtain ⟨W', hW', hxW'⟩ := Opens.mem_sSup.mp hxUV
  have hx2 : x ∈ W' ⊓ W := ⟨hxW', hxW⟩
  rw [hinter W' hW'.1 W hW] at hx2
  obtain ⟨O, hO, hxO⟩ := Opens.mem_sSup.mp hx2
  exact Opens.mem_sSup.mpr ⟨O, ⟨hO.1, hO.2.trans (inf_le_inf_right W hW'.2)⟩, hxO⟩

/-! ### Tag 0D69 -/

/-- **The comparison isomorphism over an overlap, from the relativized uniqueness of
solutions.** In Situation 0D67, assume `Stacks.DerivedGlueing.HasUniqueSolutionOverIso S`, that
the intersection of two members of the collection is the union of the members contained in it,
and that the prescribed objects have no negative self-Ext.  Then for members `U` and `V` of the
collection there is a unique isomorphism `K_U|_{U ∩ V} ≅ K_V|_{U ∩ V}` compatible with the
prescribed transitions on the members of the collection contained in `U ∩ V`.

Both restrictions are solutions over `U ∩ V`, by
`Stacks.DerivedGlueing.SolutionOver.restrictOpen` applied to
`Stacks.DerivedGlueing.selfSolutionOver`, and `hinter` covers `U ∩ V` by members.  The statement
of [Stacks, Tag 0D69] is `Stacks.DerivedGlueing.exists_unique_overlapIso_of_covers`. -/
theorem exists_unique_overlapIso (S : LocallyGiven X)
    (huniq : HasUniqueSolutionOverIso S)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i))
    (U V : Opens X.carrier) (hU : U ∈ S.opens) (hV : V ∈ S.opens) :
    ∃! φ : (S.restriction (U ⊓ V) U inf_le_left).obj (S.obj U hU) ≅
        (S.restriction (U ⊓ V) V inf_le_right).obj (S.obj V hV),
      IsOverlapHom S hU hV inf_le_left inf_le_right φ.hom := by
  obtain ⟨φ, hφ, hφuniq⟩ := huniq (U ⊓ V) (hinter U hU V hV) hinter hExt
    ((selfSolutionOver S U hU).restrictOpen (U ⊓ V) inf_le_left)
    ((selfSolutionOver S V hV).restrictOpen (U ⊓ V) inf_le_right)
  refine ⟨φ, (isOverlapHom_iff hU hV inf_le_left inf_le_right φ.hom).mpr hφ, ?_⟩
  intro ψ hψ
  exact hφuniq ψ ((isOverlapHom_iff hU hV inf_le_left inf_le_right ψ.hom).mp hψ)

/-- **The cocycle condition, from the relativized uniqueness of solutions.** Let `U`, `V` and
`W` be members of the collection and let `ρ_{U,V}`, `ρ_{V,W}` and `ρ_{U,W}` be compatible
isomorphisms between the restrictions of the prescribed objects to the corresponding overlaps.
Then over the triple intersection `ρ_{U,W} = ρ_{V,W} ∘ ρ_{U,V}`.

Both sides are morphisms of the solutions over `U ∩ V ∩ W` defined by the prescribed objects on
`U` and on `W`; that open is covered by members of the collection by
`Stacks.DerivedGlueing.inf_inf_eq_sSup`, so `huniq` identifies them.  The statement of
[Stacks, Tag 0D69] is `Stacks.DerivedGlueing.restrictOverlapHom_cocycle_of_covers`. -/
theorem restrictOverlapHom_cocycle (S : LocallyGiven X)
    (huniq : HasUniqueSolutionOverIso S)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i))
    (U V W : Opens X.carrier) (hU : U ∈ S.opens) (hV : V ∈ S.opens) (hW : W ∈ S.opens)
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
          (le_inf (inf_le_left.trans inf_le_right) inf_le_right : U ⊓ V ⊓ W ≤ V ⊓ W) φVW.hom := by
  obtain ⟨φ, -, hφuniq⟩ := huniq (U ⊓ V ⊓ W) (inf_inf_eq_sSup S hinter U V W hU hV hW) hinter
    hExt ((selfSolutionOver S U hU).restrictOpen (U ⊓ V ⊓ W)
      (inf_le_left.trans inf_le_left))
    ((selfSolutionOver S W hW).restrictOpen (U ⊓ V ⊓ W) inf_le_right)
  have h₁ := hφuniq (restrictOverlapIso S hU hW inf_le_left inf_le_right
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right) φUW)
    ((isOverlapHom_iff hU hW _ _ _).mp (hφUW.restrict _))
  have h₂ := hφuniq (restrictOverlapIso S hU hV inf_le_left inf_le_right inf_le_left φUV ≪≫
      restrictOverlapIso S hV hW inf_le_left inf_le_right
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right) φVW)
    ((isOverlapHom_iff hU hW _ _ _).mp
      ((hφUV.restrict _).comp (hφVW.restrict _)))
  rw [← restrictOverlapIso_hom, ← restrictOverlapIso_hom, ← restrictOverlapIso_hom, h₁, ← h₂]
  rfl

end Stacks.DerivedGlueing

end
