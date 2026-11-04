module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.DescentDatumOfLocallyGivenObjects

/-!
# Uniqueness of a solution, from the glueing of morphisms

Let `(X, 𝒪_X)` be a ringed space and let `(ℬ, K_U, ρ^U_V)` be a system of locally given derived
objects on it, as in Situation 0D67. The uniqueness clause of [Stacks, Tag 0D68] says that two
solutions over an open subset `O` which is the union of the members of `ℬ` contained in it are
identified by a unique isomorphism of solutions; this is the predicate
`Stacks.DerivedGlueing.HasUniqueSolutionOverIso`.

Two solutions `A` and `B` over `O` have, on every member `W` of the collection contained in `O`, a
canonical comparison morphism

`A|_W ⟶ K_W ⟶ B|_W`,

and these comparisons are compatible with restriction to smaller members. If such compatible
families of morphisms glue uniquely, which is the sheaf condition of [Stacks, Tag 0D66] part (2)
for the rule `W ↦ Hom(A|_W, B|_W)`, then the glued morphism and the one glued from the
comparisons in the other direction are mutually inverse, and the resulting isomorphism is the
unique isomorphism of solutions.

## Main definitions

* `Stacks.DerivedGlueing.restrictHomBelow`: a morphism between the restrictions to `W` of two
  objects over `O`, restricted to a smaller open `T ⊆ W`, read through the comparison of
  restriction in one and in two steps.
* `Stacks.DerivedGlueing.SolutionOver.compHom`: the canonical comparison morphism between the
  restrictions of two solutions over `O` to a member of the collection.
* `Stacks.DerivedGlueing.HasGluingForHomsOver`: the sheaf condition of [Stacks, Tag 0D66]
  part (2) in the vocabulary of Situation 0D67 — a compatible family of morphisms between the
  restrictions of two objects over `O` to the members of the collection contained in `O` comes
  from a unique morphism over `O`.

## Main results

* `Stacks.DerivedGlueing.hasUniqueSolutionOverIso_of_hasGluingForHomsOver`: the glueing
  condition implies the uniqueness clause of [Stacks, Tag 0D68], relativized to an open subset.

## References

* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
* [Stacks Project, Tag 0D5Q](https://stacks.math.columbia.edu/tag/0D5Q)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Stacks.DerivedGlueing

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}}

/-! ### Restricting a morphism between restrictions to a smaller open -/

/-- Let `K` and `L` be objects over `O` and let `T ⊆ W ⊆ O`. A morphism `K|_W ⟶ L|_W` is
carried to a morphism `K|_T ⟶ L|_T` by restricting it from `W` to `T` and reading the result
through the comparison of restriction from `O` in one and in two steps.

This is the restriction map of the rule `W ↦ Hom(K|_W, L|_W)` of [Stacks, Tag 0D66] part (2). -/
def restrictHomBelow (S : LocallyGiven X) {O : Opens X.carrier}
    {K L : OpenDerivedCategory X O} {T W : Opens X.carrier} (hTW : T ≤ W) (hWO : W ≤ O)
    (φ : (S.restriction W O hWO).obj K ⟶ (S.restriction W O hWO).obj L) :
    (S.restriction T O (hTW.trans hWO)).obj K ⟶
      (S.restriction T O (hTW.trans hWO)).obj L :=
  (S.restrictionComp T W O hTW hWO).hom.app K ≫ (S.restriction T W hTW).map φ ≫
    (S.restrictionComp T W O hTW hWO).inv.app L

/-- Restricting the restriction of a morphism over `O` to a smaller open is its restriction. -/
theorem restrictHomBelow_map (S : LocallyGiven X) {O : Opens X.carrier}
    {K L : OpenDerivedCategory X O} {T W : Opens X.carrier} (hTW : T ≤ W) (hWO : W ≤ O)
    (ψ : K ⟶ L) :
    restrictHomBelow S hTW hWO ((S.restriction W O hWO).map ψ) =
      (S.restriction T O (hTW.trans hWO)).map ψ := by
  rw [restrictHomBelow, ← Category.assoc, ← Functor.comp_map,
    ← (S.restrictionComp T W O hTW hWO).hom.naturality ψ, Category.assoc, Iso.hom_inv_id_app,
    Category.comp_id]

/-- The identity restricts to the identity. -/
@[simp]
theorem restrictHomBelow_id (S : LocallyGiven X) {O : Opens X.carrier}
    {K : OpenDerivedCategory X O} {T W : Opens X.carrier} (hTW : T ≤ W) (hWO : W ≤ O) :
    restrictHomBelow S hTW hWO (𝟙 ((S.restriction W O hWO).obj K)) =
      𝟙 ((S.restriction T O (hTW.trans hWO)).obj K) := by
  rw [← CategoryTheory.Functor.map_id, restrictHomBelow_map, CategoryTheory.Functor.map_id]

/-- Restriction to a smaller open is compatible with composition. -/
theorem restrictHomBelow_comp (S : LocallyGiven X) {O : Opens X.carrier}
    {K L M : OpenDerivedCategory X O} {T W : Opens X.carrier} (hTW : T ≤ W) (hWO : W ≤ O)
    (φ : (S.restriction W O hWO).obj K ⟶ (S.restriction W O hWO).obj L)
    (χ : (S.restriction W O hWO).obj L ⟶ (S.restriction W O hWO).obj M) :
    restrictHomBelow S hTW hWO (φ ≫ χ) =
      restrictHomBelow S hTW hWO φ ≫ restrictHomBelow S hTW hWO χ := by
  simp only [restrictHomBelow, Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc]

/-- Restriction to a smaller open is transitive: restricting a morphism from `V` to `W` and then
to `T` is restricting it from `V` to `T`. Together with `Stacks.DerivedGlueing.restrictHomBelow_id`
this says that `W ↦ Hom(K|_W, L|_W)` is a presheaf on the opens contained in `O`. -/
theorem restrictHomBelow_trans (S : LocallyGiven X) {O : Opens X.carrier}
    {K L : OpenDerivedCategory X O} {T W V : Opens X.carrier} (hTW : T ≤ W) (hWV : W ≤ V)
    (hVO : V ≤ O)
    (φ : (S.restriction V O hVO).obj K ⟶ (S.restriction V O hVO).obj L) :
    restrictHomBelow S hTW (hWV.trans hVO) (restrictHomBelow S hWV hVO φ) =
      restrictHomBelow S (hTW.trans hWV) hVO φ := by
  have hpentK := S.restrictionComp_pentagon T W V O hTW hWV hVO K
  have hpentL := S.restrictionComp_pentagon T W V O hTW hWV hVO L
  have hnat := (S.restrictionComp T W V hTW hWV).hom.naturality φ
  have key : (S.restrictionComp T W V hTW hWV).hom.app ((S.restriction V O hVO).obj L) ≫
        (S.restriction T W hTW).map ((S.restrictionComp W V O hWV hVO).inv.app L) ≫
          (S.restrictionComp T W O hTW (hWV.trans hVO)).inv.app L =
      (S.restrictionComp T V O (hTW.trans hWV) hVO).inv.app L := by
    rw [← cancel_epi ((S.restrictionComp T V O (hTW.trans hWV) hVO).hom.app L),
      Iso.hom_inv_id_app, ← Category.assoc, hpentL, Category.assoc, ← Functor.map_comp_assoc,
      Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app]
  simp only [restrictHomBelow, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hpentK, ← reassoc_of% hnat, key]

/-! ### The comparison morphisms between two solutions -/

/-- The comparison morphism `A|_W ⟶ K_W ⟶ B|_W` between the restrictions of the objects of two
solutions over `O` to a member `W` of the collection contained in `O`, through their
identifications with the prescribed object on `W`. -/
def SolutionOver.compHom {S : LocallyGiven X} {O : Opens X.carrier} (A B : SolutionOver S O)
    (W : Opens X.carrier) (hW : W ∈ S.opens) (hWO : W ≤ O) :
    (S.restriction W O hWO).obj A.obj ⟶ (S.restriction W O hWO).obj B.obj :=
  (A.rho W hW hWO).hom ≫ (B.rho W hW hWO).inv

/-- The comparison morphism of a solution with itself is the identity. -/
@[simp]
theorem SolutionOver.compHom_self {S : LocallyGiven X} {O : Opens X.carrier}
    (A : SolutionOver S O) (W : Opens X.carrier) (hW : W ∈ S.opens) (hWO : W ≤ O) :
    A.compHom A W hW hWO = 𝟙 ((S.restriction W O hWO).obj A.obj) := by
  simp [SolutionOver.compHom]

/-- The two comparison morphisms between two solutions are mutually inverse. -/
@[simp]
theorem SolutionOver.compHom_comp_compHom {S : LocallyGiven X} {O : Opens X.carrier}
    (A B : SolutionOver S O) (W : Opens X.carrier) (hW : W ∈ S.opens) (hWO : W ≤ O) :
    A.compHom B W hW hWO ≫ B.compHom A W hW hWO =
      𝟙 ((S.restriction W O hWO).obj A.obj) := by
  simp [SolutionOver.compHom]

/-- The comparison morphisms form a compatible family: the comparison over a member `W` of the
collection, restricted to a smaller member `T`, is the comparison over `T`. -/
theorem SolutionOver.restrictHomBelow_compHom {S : LocallyGiven X} {O : Opens X.carrier}
    (A B : SolutionOver S O) {T W : Opens X.carrier} (hW : W ∈ S.opens) (hT : T ∈ S.opens)
    (hTW : T ≤ W) (hWO : W ≤ O) :
    restrictHomBelow S hTW hWO (A.compHom B W hW hWO) =
      A.compHom B T hT (hTW.trans hWO) := by
  have hA := A.compatibility W T hTW hW hT hWO
  have hB := B.compatibility W T hTW hW hT hWO
  rw [← cancel_mono (B.rho T hT (hTW.trans hWO)).hom]
  simp only [SolutionOver.compHom, restrictHomBelow, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rw [← hB]
  simp only [Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  exact hA

/-! ### The glueing condition on morphisms -/

/-- The sheaf condition of [Stacks, Tag 0D66] part (2), in the vocabulary of Situation 0D67: let
`O` be an open subset which is the union of the members of the collection contained in it, and
let `K` and `L` be objects over `O` with `Ext^i(K|_W, L|_W) = 0` for `i < 0` and every member `W`
of the collection contained in `O`. Then a family of morphisms `K|_W ⟶ L|_W`, compatible with
restriction between members, comes from a unique morphism `K ⟶ L`. That is, the rule
`W ↦ Hom(K|_W, L|_W)` is a sheaf on `O`, read on the members of the collection. -/
def HasGluingForHomsOver (S : LocallyGiven X) : Prop :=
  ∀ (O : Opens X.carrier), O = sSup {W | W ∈ S.opens ∧ W ≤ O} →
    (∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V}) →
    ∀ K L : OpenDerivedCategory X O,
      (∀ (W : Opens X.carrier), W ∈ S.opens → ∀ hWO : W ≤ O, ∀ i : ℤ, i < 0 →
        Subsingleton (ShiftedHom ((S.restriction W O hWO).obj K)
          ((S.restriction W O hWO).obj L) i)) →
      ∀ φ : ∀ (W : Opens X.carrier), W ∈ S.opens → ∀ hWO : W ≤ O,
          (S.restriction W O hWO).obj K ⟶ (S.restriction W O hWO).obj L,
        (∀ (W T : Opens X.carrier) (hW : W ∈ S.opens) (hT : T ∈ S.opens) (hTW : T ≤ W)
            (hWO : W ≤ O), restrictHomBelow S hTW hWO (φ W hW hWO) = φ T hT (hTW.trans hWO)) →
        ∃! ψ : K ⟶ L, ∀ (W : Opens X.carrier) (hW : W ∈ S.opens) (hWO : W ≤ O),
          (S.restriction W O hWO).map ψ = φ W hW hWO

/-! ### The uniqueness clause of Tag 0D68 -/

/-- The uniqueness clause of [Stacks, Tag 0D68] follows from the glueing of morphisms: if a
compatible family of morphisms between the restrictions of two objects over an open subset `O`
to the members of the collection contained in `O` comes from a unique morphism over `O`, then
two solutions over `O` are identified by a unique isomorphism of solutions. -/
theorem hasUniqueSolutionOverIso_of_hasGluingForHomsOver (S : LocallyGiven X)
    (hglue : HasGluingForHomsOver S) : HasUniqueSolutionOverIso S := by
  intro O hO hinter hExt A B
  have hExt' : ∀ (C D : SolutionOver S O) (W : Opens X.carrier) (hW : W ∈ S.opens)
      (hWO : W ≤ O), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom ((S.restriction W O hWO).obj C.obj)
        ((S.restriction W O hWO).obj D.obj) i) := fun C D W hW hWO i hi =>
    subsingleton_shiftedHom_of_iso (C.rho W hW hWO) (D.rho W hW hWO) i (hExt W hW i hi)
  have hcomp : ∀ C D : SolutionOver S O, ∃! ψ : C.obj ⟶ D.obj,
      ∀ (W : Opens X.carrier) (hW : W ∈ S.opens) (hWO : W ≤ O),
        (S.restriction W O hWO).map ψ = C.compHom D W hW hWO :=
    fun C D => hglue O hO hinter C.obj D.obj (hExt' C D) (C.compHom D)
      fun W T hW hT hTW hWO => C.restrictHomBelow_compHom D hW hT hTW hWO
  choose f hf using hcomp
  have hone : ∀ C D : SolutionOver S O, f C D ≫ f D C = 𝟙 C.obj := fun C D =>
    ((hf C C).2 _ fun W hW hWO => by
      rw [Functor.map_comp, (hf C D).1 W hW hWO, (hf D C).1 W hW hWO,
        SolutionOver.compHom_comp_compHom, SolutionOver.compHom_self]).trans
      ((hf C C).2 _ fun W hW hWO => by simp).symm
  refine ⟨⟨f A B, f B A, hone A B, hone B A⟩, fun W hW hWO => ?_, fun θ hθ => ?_⟩
  · rw [(hf A B).1 W hW hWO, SolutionOver.compHom, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  · exact Iso.ext ((hf A B).2 _ fun W hW hWO => by
      rw [SolutionOver.compHom, ← hθ W hW hWO, Category.assoc, Iso.hom_inv_id, Category.comp_id])

end Stacks.DerivedGlueing

end
