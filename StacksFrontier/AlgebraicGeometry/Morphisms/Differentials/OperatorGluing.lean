module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.OrderLocality

/-!
# Gluing differential operators along an open cover

A family of differential operators of order at most `k` defined on the members of an open
cover of a topological space and agreeing on the opens contained in two members of the cover
glues to a unique differential operator of order at most `k` on the whole space. For schemes
this is what assembles an affine-local construction into a global differential operator on
`X/Y`.

## Main definitions

* `DiffOp.coverGlueHom`: the morphism of presheaves of abelian groups obtained by gluing a
  family of operators on the members of an open cover.
* `DiffOp.coverGlue`: the glued operator, as a global operator on local sections.

## Main results

* `DiffOp.coverGlue_restrict`: the glued operator restricts on each member of the cover to
  the operator it was glued from.
* `DiffOp.globalOp_ext_of_cover`: two global operators compatible with restriction of
  sections which agree on the members of an open cover are equal.
* `DiffOp.existsUnique_globalOp_of_cover`: a family of differential operators of order at
  most `k` on the members of an open cover, agreeing on overlaps, glues to a unique
  differential operator of order at most `k`.
* `AlgebraicGeometry.existsUnique_globalDiffOp_of_cover`: the same statement for differential
  operators on `X/Y`, for an arbitrary open cover of the scheme `X`.

## Implementation notes

The opens contained in some member of the cover form a basis of the topology, and a family of
operators agreeing on overlaps is precisely a morphism between the restrictions of the two
presheaves of abelian groups to that basis; the glued operator is its image under
`TopCat.Sheaf.restrictHomEquivHom`. Indexing the basis by the pairs consisting of a member of
the cover and an open contained in it makes this assignment a function of the data, with no
choice of an index for an open lying in several members of the cover.

The order of the glued operator is obtained from the locality of the order on the base rather
than reproved, and uniqueness only uses compatibility with restriction of sections.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace DiffOp

variable {X : TopCat.{u}} {O O' : TopCat.Sheaf RingCat.{u} X} {F G : SheafOfModules.{u} O'}
  {ι : Type*}

/-- Two operators on members of a cover agree on the opens contained in both. -/
def AgreeOnCover (U : ι → Opens X) (D : ∀ i, RawOp F G (U i)) : Prop :=
  ∀ (i j : ι) (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j),
    D i (Over.mk (homOfLE hi)) = D j (Over.mk (homOfLE hj))

/-- A family of operators on the members of a cover whose restrictions to each pairwise
intersection agree does agree on the opens contained in two members of the cover. -/
theorem agreeOnCover_of_slice_eq (U : ι → Opens X) (D : ∀ i, RawOp F G (U i))
    (h : ∀ i j, (D i).slice (Over.mk (homOfLE (inf_le_left : U i ⊓ U j ≤ U i))) =
      (D j).slice (Over.mk (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)))) :
    AgreeOnCover U D :=
  fun i j _ hi hj ↦ congrFun (h i j) (Over.mk (homOfLE (le_inf hi hj)))

/-- The morphism of presheaves of abelian groups glued from a family of operators on the
members of an open cover which are compatible with restriction and agree on overlaps. -/
noncomputable def coverGlueHom (U : ι → Opens X) (hU : ∀ p : X, ∃ i, p ∈ U i)
    (D : ∀ i, RawOp F G (U i)) (hnat : ∀ i, (D i).IsNatural)
    (hagree : AgreeOnCover U D) : F.val.presheaf ⟶ G.val.presheaf :=
  TopCat.Sheaf.restrictHomEquivHom F.val.presheaf
    (⟨G.val.presheaf, G.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)
    (isBasis_coverSubsets U hU)
    { app q := AddCommGrpCat.ofHom (D q.unop.1 (Over.mk (homOfLE q.unop.2.2)))
      naturality q q' f := by
        ext x
        exact (congrArg (fun T : F.val.obj (op q'.unop.2.1) →+ G.val.obj (op q'.unop.2.1) ↦
            T (F.val.presheaf.map (homOfLE f.unop.hom.le).op x))
          (hagree q'.unop.1 q.unop.1 q'.unop.2.1 q'.unop.2.2
            (f.unop.hom.le.trans q.unop.2.2))).trans
          (hnat q.unop.1 (Over.mk (homOfLE (f.unop.hom.le.trans q.unop.2.2)))
            (Over.mk (homOfLE q.unop.2.2)) (Over.homMk (homOfLE f.unop.hom.le)
              (Subsingleton.elim _ _)) x) }

/-- On an open contained in a member of the cover, the glued morphism is the operator of that
member. -/
theorem coverGlueHom_app_apply (U : ι → Opens X) (hU : ∀ p : X, ∃ i, p ∈ U i)
    (D : ∀ i, RawOp F G (U i)) (hnat : ∀ i, (D i).IsNatural) (hagree : AgreeOnCover U D)
    (i : ι) {W : Opens X} (hW : W ≤ U i) (x : F.val.obj (op W)) :
    (coverGlueHom U hU D hnat hagree).app (op W) x = D i (Over.mk (homOfLE hW)) x :=
  congrArg (fun T : F.val.presheaf.obj (op W) ⟶ G.val.presheaf.obj (op W) ↦ T.hom x)
    (TopCat.Sheaf.extend_hom_app F.val.presheaf
      (⟨G.val.presheaf, G.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)
      (isBasis_coverSubsets U hU) _ (⟨i, ⟨W, hW⟩⟩ : (i : ι) × {W : Opens X // W ≤ U i}))

/-- The global operator on local sections glued from a family of operators on the members of
an open cover which are compatible with restriction and agree on overlaps. -/
noncomputable def coverGlue (U : ι → Opens X) (hU : ∀ p : X, ∃ i, p ∈ U i)
    (D : ∀ i, RawOp F G (U i)) (hnat : ∀ i, (D i).IsNatural)
    (hagree : AgreeOnCover U D) : GlobalOp F G :=
  fun V ↦ ((coverGlueHom U hU D hnat hagree).app V).hom

/-- The glued operator is compatible with restriction of sections. -/
theorem coverGlue_isNatural (U : ι → Opens X) (hU : ∀ p : X, ∃ i, p ∈ U i)
    (D : ∀ i, RawOp F G (U i)) (hnat : ∀ i, (D i).IsNatural) (hagree : AgreeOnCover U D)
    (V : Opens X) : ((coverGlue U hU D hnat hagree).restrict V).IsNatural :=
  AlgebraicGeometry.AffineDiffOp.natural_raw (coverGlueHom U hU D hnat hagree) V

/-- The glued operator restricts on each member of the cover to the operator it was glued
from. -/
theorem coverGlue_restrict (U : ι → Opens X) (hU : ∀ p : X, ∃ i, p ∈ U i)
    (D : ∀ i, RawOp F G (U i)) (hnat : ∀ i, (D i).IsNatural) (hagree : AgreeOnCover U D)
    (i : ι) : (coverGlue U hU D hnat hagree).restrict (U i) = D i := by
  funext Y
  exact AddMonoidHom.ext fun x ↦ coverGlueHom_app_apply U hU D hnat hagree i Y.hom.le x

/-- Two global operators compatible with restriction of sections which agree on every open
contained in a member of an open cover are equal. -/
theorem globalOp_ext_of_cover (B : ι → Opens X) (hB : ∀ p : X, ∃ i, p ∈ B i)
    (D E : GlobalOp F G) (hD : (D.restrict ⊤).IsNatural) (hE : (E.restrict ⊤).IsNatural)
    (h : ∀ i, D.restrict (B i) = E.restrict (B i)) : D = E := by
  funext V
  refine AddMonoidHom.ext fun s ↦ ?_
  apply TopCat.Presheaf.IsSheaf.section_ext (F := G.val.presheaf) G.isSheaf
  intro p hp
  obtain ⟨i, hi⟩ := hB p
  refine ⟨V.unop ⊓ B i, inf_le_left, ⟨hp, hi⟩, ?_⟩
  have hres : ∀ (T : GlobalOp F G), (T.restrict ⊤).IsNatural →
      G.val.presheaf.map (homOfLE (inf_le_left : V.unop ⊓ B i ≤ V.unop)).op (T V s) =
        T (op (V.unop ⊓ B i)) (F.val.presheaf.map
          (homOfLE (inf_le_left : V.unop ⊓ B i ≤ V.unop)).op s) :=
    fun T hT ↦ (hT (Over.mk (homOfLE (le_top : V.unop ⊓ B i ≤ ⊤)))
      (Over.mk (homOfLE (le_top : V.unop ≤ ⊤)))
      (Over.homMk (homOfLE (inf_le_left : V.unop ⊓ B i ≤ V.unop))
        (Subsingleton.elim _ _)) s).symm
  have key : D (op (V.unop ⊓ B i)) (F.val.presheaf.map
        (homOfLE (inf_le_left : V.unop ⊓ B i ≤ V.unop)).op s) =
      E (op (V.unop ⊓ B i)) (F.val.presheaf.map
        (homOfLE (inf_le_left : V.unop ⊓ B i ≤ V.unop)).op s) :=
    DFunLike.congr_fun
      (congrFun (h i) (Over.mk (homOfLE (inf_le_right : V.unop ⊓ B i ≤ B i)))) _
  exact (hres D hD).trans (key.trans (hres E hE).symm)

/-- **Gluing of differential operators.** A family of differential operators of order at most
`k` on the members of an arbitrary open cover, compatible with restriction of sections and
agreeing on the opens contained in two members of the cover, glues to a unique differential
operator of order at most `k`. -/
theorem existsUnique_globalOp_of_cover (φ : O ⟶ O')
    (hcomm : ∀ (V : (Opens X)ᵒᵖ) (r s : O'.obj.obj V), r * s = s * r) {k : ℕ}
    (U : ι → Opens X) (hU : ∀ p : X, ∃ i, p ∈ U i) (D : ∀ i, RawOp F G (U i))
    (hD : ∀ i, IsDiffOpOfOrder φ k (D i)) (hagree : AgreeOnCover U D) :
    ∃! E : GlobalOp F G,
      IsGlobalDiffOpOfOrder φ k E ∧ ∀ i, E.restrict (U i) = D i := by
  have hnat : ∀ i, (D i).IsNatural :=
    fun i ↦ RawOp.isNatural_of_isDiffOpOfOrder φ k (D i) (hD i)
  refine ⟨coverGlue U hU D hnat hagree, ⟨?_, coverGlue_restrict U hU D hnat hagree⟩, ?_⟩
  · refine isGlobalDiffOpOfOrder_of_cover φ hcomm U hU _
      (coverGlue_isNatural U hU D hnat hagree ⊤) fun i ↦ ?_
    exact (coverGlue_restrict U hU D hnat hagree i).symm ▸ hD i
  · intro E hE
    refine globalOp_ext_of_cover U hU E _
      (RawOp.isNatural_of_isDiffOpOfOrder φ k _ (hE.1 ⊤))
      (coverGlue_isNatural U hU D hnat hagree ⊤) fun i ↦ ?_
    exact (hE.2 i).trans (coverGlue_restrict U hU D hnat hagree i).symm

end DiffOp

namespace AlgebraicGeometry

/-- **Gluing of differential operators on a scheme.** A family of differential operators of
order at most `k` on `X/Y` defined on the members of an arbitrary open cover of `X`,
compatible with restriction of sections and agreeing on the opens contained in two members of
the cover, glues to a unique differential operator of order at most `k` on `X/Y`. -/
theorem existsUnique_globalDiffOp_of_cover {X Y : Scheme.{u}} (f : X ⟶ Y) (k : ℕ)
    {F G : X.Modules} {ι : Type*} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    (D : ∀ i, DiffOp.RawOp F G (U i))
    (hD : ∀ i, DiffOp.IsDiffOpOfOrder f.relativeStructureSheafMap k (D i))
    (hagree : DiffOp.AgreeOnCover U D) :
    ∃! E : DiffOp.GlobalOp F G,
      DiffOp.IsGlobalDiffOpOfOrder f.relativeStructureSheafMap k E ∧
        ∀ i, E.restrict (U i) = D i :=
  DiffOp.existsUnique_globalOp_of_cover _ (fun V r s ↦ mul_comm (G := Γ(X, V.unop)) r s) U
    (fun p ↦ Opens.mem_iSup.1 (hU ▸ Opens.mem_top p)) D hD hagree

end AlgebraicGeometry

end
