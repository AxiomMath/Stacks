module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.SmallSiteAbelianInstances
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.CoveringSetGlobalSections
import StacksCore.Tactic.StacksAttribute

/-!
# The base case of the filtered-colimit theorem for global cohomology

Stacks 0GN3 asserts that, for a site carrying a set `S` of quasi-compact sheaves of sets with
enough covers, products and equalizers, the canonical map
`colim_λ H^p(C, F_λ) ⟶ H^p(C, colim_λ F_λ)` is an isomorphism for every filtered diagram of
abelian sheaves and every `p ≥ 0`. Its proof is an induction on `p`. This file proves the **base
case** `p = 0`, for the zeroth right derived functor of `CategoryTheory.Sheaf.Γ` on abelian
sheaves.

It is deduced from the corresponding statement for sheaves of **sets**,
`CategoryTheory.Sheaf.bijective_colimit_post_globalSections_of_coveringSet`, in two steps.

First, global sections of an abelian sheaf, followed by the forgetful functor to types, is the
underlying sheaf of sets followed by global sections of sheaves of sets
(`globalSectionsForgetNatIso`); both sides are the limit over `Cᵒᵖ` of the underlying presheaf,
and the forgetful functor `AddCommGrpCat ⥤ Type` preserves limits. Since the sheafification
functor into abelian sheaves is compatible with the one into sheaves of sets, the underlying
sheaf of sets functor preserves filtered colimits (`preservesColimit_sheafForget`), so the
comparison map for abelian global sections becomes a composition of the comparison map for sets
with isomorphisms, and is therefore bijective. Faithfulness of the forgetful functor then
upgrades bijectivity to `IsIso` in sheaves of abelian groups.

Second, `Functor.toRightDerivedZero` is an isomorphism for a left exact functor, and global
sections is a right adjoint, hence left exact; so the comparison map for `Γ.rightDerived 0`
differs from the one for `Γ` by isomorphisms on both sides.

## Main results

* `isIso_colimit_post_globalSections_abelian`: the comparison map for global sections of abelian
  sheaves is an isomorphism.
* `isIso_colimit_post_rightDerived_globalSections_zero`: the same for the zeroth right derived
  functor, which is the base case of Stacks 0GN3.

## Implementation notes

The site, the coefficients and the diagram all live in one universe `u`. The sets-level input is
stated at `Type max u v` for a site `C : Type u` with `Category.{v} C`, which at `v = u` is the
`Type u` used here.

## References

* [Stacks Project, Tag 0GN3](https://stacks.math.columbia.edu/tag/0GN3)
* [Stacks Project, Tag 0GMR](https://stacks.math.columbia.edu/tag/0GMR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Cohomology.ColimitsOfCohomology

attribute [local instance] enoughInjectives_sheaf_ab additive_globalSections_ab

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-- Global sections of abelian sheaves, followed by the forgetful functor to types, agrees with
passing to the underlying sheaf of sets and then taking global sections. -/
def globalSectionsForgetNatIso :
    (Sheaf.Γ J (Ab.{u}) ⋙ forget AddCommGrpCat) ≅
      (sheafForget (J := J) (D := AddCommGrpCat) ⋙ Sheaf.Γ J (Type u)) :=
  Functor.isoWhiskerRight (Sheaf.ΓNatIsoLim J (Ab.{u})) (forget AddCommGrpCat) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf J (Ab.{u}))
      (preservesLimitNatIso (forget AddCommGrpCat)) ≪≫
    (Functor.isoWhiskerLeft (sheafForget (J := J) (D := AddCommGrpCat))
      (Sheaf.ΓNatIsoLim J (Type u))).symm

/-- The comparison map `colim (F ⋙ G) ⟶ G (colim F)` is natural in the functor `G`. -/
lemma colim_map_whiskerLeft_comp_colimit_post {I : Type*} [Category* I]
    {D : Type*} [Category* D] {A : Type*} [Category* A]
    (F : I ⥤ D) {G H : D ⥤ A} (α : G ⟶ H)
    [HasColimit F] [HasColimitsOfShape I A] :
    colim.map (Functor.whiskerLeft F α) ≫ colimit.post F H =
      colimit.post F G ≫ α.app (colimit F) := by
  refine colimit.hom_ext fun i => ?_
  simp

/-- The underlying sheaf of sets of an abelian sheaf preserves filtered colimits. -/
lemma preservesColimit_sheafForget {I : Type u} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf J AddCommGrpCat.{u}) :
    PreservesColimit F (sheafForget (D := AddCommGrpCat.{u}) J) := by
  let U := sheafForget (D := AddCommGrpCat.{u}) J
  let L := presheafToSheaf J AddCommGrpCat.{u}
  let P := F ⋙ sheafToPresheaf J AddCommGrpCat.{u}
  have : PreservesColimit P (L ⋙ U) :=
    preservesColimit_of_natIso P
      (sheafComposeNatIso J (forget AddCommGrpCat.{u})
        (sheafificationAdjunction J AddCommGrpCat.{u})
        (sheafificationAdjunction J (Type u)))
  have : PreservesColimit (P ⋙ L) U :=
    preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves L (colimit.isColimit P))
      (isColimitOfPreserves (L ⋙ U) (colimit.isColimit P))
  exact preservesColimit_of_iso_diagram U
    (Functor.associator F (sheafToPresheaf J AddCommGrpCat.{u}) L ≪≫
      (Functor.isoWhiskerLeft F (sheafificationNatIso J AddCommGrpCat.{u})).symm ≪≫
      Functor.rightUnitor F)

/-- **Stacks 0GN3 in degree zero, for abelian sheaves.** Let `S` be a set of sheaves of sets
satisfying hypotheses (1), (2), (3) and (5) of Stacks 0GN3: a member of `S` surjects onto the
final sheaf, surjections onto members of `S` are lifted by members of `S`, products of members of
`S` receive surjections from members of `S`, and every member of `S` is quasi-compact. Then for
every filtered diagram `F` of abelian sheaves the comparison map
`colim_i Γ(C, F i) ⟶ Γ(C, colim_i F i)` is an isomorphism.

Hypothesis (4) of Stacks 0GN3, on equalizers, is not needed in degree zero. -/
lemma isIso_colimit_post_globalSections_abelian (S : Set (Sheaf J (Type u)))
    (h_terminal : ∃ K ∈ S, Sheaf.IsLocallySurjective (terminal.from K))
    (h_lift : ∀ {G K : Sheaf J (Type u)} (f : G ⟶ K), K ∈ S →
      Sheaf.IsLocallySurjective f →
        ∃ K' ∈ S, ∃ g : K' ⟶ G, Sheaf.IsLocallySurjective (g ≫ f))
    (h_product : ∀ K ∈ S, ∀ K' ∈ S,
      ∃ K'' ∈ S, ∃ f : K'' ⟶ K ⨯ K', Sheaf.IsLocallySurjective f)
    (h_quasiCompact : ∀ K ∈ S, Sheaf.IsQuasiCompact K)
    {I : Type u} [SmallCategory I] [IsFiltered I] (F : I ⥤ Sheaf J (Ab.{u})) :
    IsIso (colimit.post F (Sheaf.Γ J (Ab.{u}))) := by
  have := preservesColimit_sheafForget J F
  let U : Sheaf J (Ab.{u}) ⥤ Sheaf J (Type u) := sheafForget (J := J) (D := AddCommGrpCat)
  let G := Sheaf.Γ J (Ab.{u})
  let GT := Sheaf.Γ J (Type u)
  let β := globalSectionsForgetNatIso J
  let eS := preservesColimitIso (forget AddCommGrpCat) (F ⋙ G)
  let m := colim.map (Functor.whiskerLeft F β.hom)
  have hm : IsIso m := by
    dsimp only [m]
    infer_instance
  have hsquare : eS.hom ≫ m ≫ colimit.post (F ⋙ U) GT ≫ GT.map (colimit.post F U) =
      (forget AddCommGrpCat).map (colimit.post F G) ≫ β.hom.app (colimit F) := by
    have hnat := colim_map_whiskerLeft_comp_colimit_post F β.hom
    have heS : eS.hom ≫ colimit.post F (G ⋙ forget AddCommGrpCat) =
        (forget AddCommGrpCat).map (colimit.post F G) := by
      rw [← colimit.post_post (F := F) (G := G) (H := forget AddCommGrpCat)]
      exact eS.hom_inv_id_assoc _
    calc
      eS.hom ≫ m ≫ colimit.post (F ⋙ U) GT ≫ GT.map (colimit.post F U) =
          eS.hom ≫ m ≫ colimit.post F (U ⋙ GT) := by
            rw [← colimit.post_post (F := F) (G := U) (H := GT)]
      _ = eS.hom ≫ colimit.post F (G ⋙ forget AddCommGrpCat) ≫ β.hom.app (colimit F) := by
            change eS.hom ≫
              (colim.map (Functor.whiskerLeft F β.hom) ≫ colimit.post F (U ⋙ GT)) = _
            rw [hnat]
      _ = (forget AddCommGrpCat).map (colimit.post F G) ≫ β.hom.app (colimit F) := by
            rw [← Category.assoc, heS]
  have : IsIso (colimit.post (F ⋙ U) GT) := (ConcreteCategory.isIso_iff_bijective _).2 (by
    simpa using Sheaf.bijective_colimit_post_globalSections_of_coveringSet (F ⋙ U)
      h_terminal h_lift h_product h_quasiCompact)
  have hright : IsIso
      ((forget AddCommGrpCat).map (colimit.post F G) ≫ β.hom.app (colimit F)) := by
    rw [← hsquare]
    infer_instance
  have : IsIso ((forget AddCommGrpCat).map (colimit.post F G)) :=
    (isIso_comp_right_iff _ _).mp hright
  exact isIso_of_reflects_iso (colimit.post F G) (forget AddCommGrpCat)

/-- **The base case of Stacks 0GN3.** Under hypotheses (1), (2), (3) and (5) of Stacks 0GN3,
degree-zero cohomology of the site commutes with filtered colimits of abelian sheaves: the
comparison map for the zeroth right derived functor of global sections is an isomorphism. -/
lemma isIso_colimit_post_rightDerived_globalSections_zero (S : Set (Sheaf J (Type u)))
    (h_terminal : ∃ K ∈ S, Sheaf.IsLocallySurjective (terminal.from K))
    (h_lift : ∀ {G K : Sheaf J (Type u)} (f : G ⟶ K), K ∈ S →
      Sheaf.IsLocallySurjective f →
        ∃ K' ∈ S, ∃ g : K' ⟶ G, Sheaf.IsLocallySurjective (g ≫ f))
    (h_product : ∀ K ∈ S, ∀ K' ∈ S,
      ∃ K'' ∈ S, ∃ f : K'' ⟶ K ⨯ K', Sheaf.IsLocallySurjective f)
    (h_quasiCompact : ∀ K ∈ S, Sheaf.IsQuasiCompact K)
    {I : Type u} [SmallCategory I] [IsFiltered I] (F : I ⥤ Sheaf J (Ab.{u})) :
    IsIso (colimit.post F ((Sheaf.Γ J (Ab.{u})).rightDerived 0)) := by
  let G := Sheaf.Γ J (Ab.{u})
  let α := G.toRightDerivedZero
  have hΓ : IsIso (colimit.post F G) :=
    isIso_colimit_post_globalSections_abelian J S h_terminal h_lift h_product h_quasiCompact F
  have hmap : IsIso (colim.map (Functor.whiskerLeft F α)) := by
    dsimp only [α]
    infer_instance
  have hcomp : IsIso
      (colim.map (Functor.whiskerLeft F α) ≫ colimit.post F (G.rightDerived 0)) := by
    rw [colim_map_whiskerLeft_comp_colimit_post F α]
    infer_instance
  exact (isIso_comp_left_iff (colim.map (Functor.whiskerLeft F α)) _).mp hcomp

end Stacks.Cohomology.ColimitsOfCohomology

end
