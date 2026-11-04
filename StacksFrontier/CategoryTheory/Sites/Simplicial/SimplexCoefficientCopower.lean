module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.FreeTensorCopower
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationResolution
public import StacksFrontier.CategoryTheory.Sites.Simplicial.IntegerResolution

/-!
# The simplex-coefficient presheaf is a copower by the presheaf of simplices

Let `S` be a simplicial-site situation. The degree-`n` term of the simplex-coefficient presheaf
of an abelian presheaf `G` on the total category has, over an object of simplicial degree `k`,
one summand of `G` for each simplex map `⦋n⦌ ⟶ ⦋k⦌`, and the restriction maps reindex the
summands by postcomposition. The presheaf of `n`-simplices of the integral resolution of
Stacks 09WI has exactly those simplex maps as its sections, and restricts by exactly that
postcomposition. So the degree-`n` term of the simplex-coefficient presheaf is the copower of `G`
by the presheaf of `n`-simplices.

This is the step of the projection formula of Stacks 0D9E that joins its two sides. The tensor
product `g_{n!}Z ⊗_Z F` is computed, through Stacks 0GMW and
`CategoryTheory.freeTensorCopowerIso`, as the sheafification of a copower of `F` by the presheaf
of `n`-simplices; the degree-`n` term `bar_n(F)` of the simplex-coefficient resolution is the
sheafification of the degree-`n` term of the simplex-coefficient presheaf. The isomorphism proved
here is what identifies the two before sheafifying.

The two sides index their summands by types in different universes: the simplex maps `⦋n⦌ ⟶ ⦋k⦌`
form a type in the lowest universe, while the sections of a presheaf of types live in the
universe of the site. The identification `SSet.stdSimplex.objEquiv` between them is a `ULift`, and
`CategoryTheory.finsuppCoproductIso` together with `CategoryTheory.Limits.Sigma.whiskerEquiv`
crosses it.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.stdSimplexPresheafObjEquiv`: the sections of the
  presheaf of `n`-simplices over an object are the simplex maps out of `⦋n⦌` into its simplicial
  degree.

## Main results

* `CategoryTheory.SimplicialSiteSituation.stdSimplexPresheafObjEquiv_map`: restriction in the
  presheaf of `n`-simplices is postcomposition with the degree map.
* `CategoryTheory.SimplicialSiteSituation.copowerStdSimplexIso`: **the copower of an abelian
  presheaf by the presheaf of `n`-simplices is the degree-`n` term of its simplex-coefficient
  presheaf.**
* `CategoryTheory.SimplicialSiteSituation.copowerStdSimplexIso_hom_app_single`: the value of that
  isomorphism on the summand labelled by a simplex, which pins it down.

## References

* [Stacks Project, Tag 09WI](https://stacks.math.columbia.edu/tag/09WI)
* [Stacks Project, Tag 0D9E](https://stacks.math.columbia.edu/tag/0D9E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (n : SimplexCategory)

/-- The sections of the presheaf of `n`-simplices over an object of the total category are the
simplex maps out of `⦋n⦌` into its simplicial degree. The two sides live in different universes
and the identification is a `ULift`. -/
def stdSimplexPresheafObjEquiv (U : S.totalCategoryᵒᵖ) :
    (stdSimplexPresheaf' S n).obj U ≃ (n ⟶ (totalSimplexDegree S).leftOp.obj U) :=
  SSet.stdSimplex.objEquiv

/-- Restriction in the presheaf of `n`-simplices is postcomposition with the degree map: that is
how the summands of the simplex-coefficient presheaf are reindexed too. -/
theorem stdSimplexPresheafObjEquiv_map {U V : S.totalCategoryᵒᵖ} (f : U ⟶ V)
    (x : (stdSimplexPresheaf' S n).obj U) :
    stdSimplexPresheafObjEquiv S n V ((stdSimplexPresheaf' S n).map f x) =
      stdSimplexPresheafObjEquiv S n U x ≫ (totalSimplexDegree S).leftOp.map f := by
  have hx : SSet.stdSimplex.objEquiv.symm
      (SSet.stdSimplex.objEquiv (n := (totalSimplexDegree S).leftOp.obj U)
        (m := Opposite.op n) x) = x :=
    Equiv.symm_apply_apply _ x
  have h := SSet.stdSimplex.objEquiv_symm_comp
    (n := (totalSimplexDegree S).leftOp.obj U) (m := Opposite.op n)
    (SSet.stdSimplex.objEquiv x) ((totalSimplexDegree S).leftOp.map f)
  rw [hx] at h
  exact (congrArg SSet.stdSimplex.objEquiv h).symm.trans (Equiv.apply_symm_apply _ _)

variable (G : S.totalCategoryᵒᵖ ⥤ AddCommGrpCat.{u})

/-- Over one object of the total category, the copower of `G` by the sections of the presheaf of
`n`-simplices is the copower of `G` by the simplex maps out of `⦋n⦌`. -/
def copowerStdSimplexIsoApp (U : S.totalCategoryᵒᵖ) :
    (copowerPresheafObj (stdSimplexPresheaf' S n) G).obj U ≅
      (((simplexCoefficientDiagram' (totalSimplexDegree S).leftOp).obj G).obj
        (Opposite.op n)).obj U :=
  (finsuppCoproductIso ((stdSimplexPresheaf' S n).obj U) (G.obj U)).symm ≪≫
    Sigma.whiskerEquiv (f := fun _ : (stdSimplexPresheaf' S n).obj U => G.obj U)
      (g := fun _ : n ⟶ (totalSimplexDegree S).leftOp.obj U => G.obj U)
      (stdSimplexPresheafObjEquiv S n U) (fun _ => Iso.refl _)

/-- The identification over one object carries the summand labelled by a section of the presheaf
of `n`-simplices to the summand labelled by the corresponding simplex map. -/
theorem copowerStdSimplexIsoApp_hom_single (U : S.totalCategoryᵒᵖ)
    (x : (stdSimplexPresheaf' S n).obj U) (m : (G.obj U : Type u)) :
    AddCommGrpCat.Hom.hom (copowerStdSimplexIsoApp S n G U).hom (Finsupp.single x m) =
      AddCommGrpCat.Hom.hom
        (Sigma.ι (fun _ : n ⟶ (totalSimplexDegree S).leftOp.obj U => G.obj U)
          (stdSimplexPresheafObjEquiv S n U x)) m := by
  show AddCommGrpCat.Hom.hom
      (Sigma.whiskerEquiv (f := fun _ : (stdSimplexPresheaf' S n).obj U => G.obj U)
        (g := fun _ : n ⟶ (totalSimplexDegree S).leftOp.obj U => G.obj U)
        (stdSimplexPresheafObjEquiv S n U) (fun _ => Iso.refl _)).hom
      (AddCommGrpCat.Hom.hom
        (finsuppCoproductIso ((stdSimplexPresheaf' S n).obj U) (G.obj U)).inv
          (Finsupp.single x m)) = _
  have hleg : AddCommGrpCat.Hom.hom
      (finsuppCoproductIso ((stdSimplexPresheaf' S n).obj U) (G.obj U)).inv
        (Finsupp.single x m) =
      AddCommGrpCat.Hom.hom
        (Sigma.ι (fun _ : (stdSimplexPresheaf' S n).obj U => G.obj U) x) m :=
    Finsupp.liftAddHom_apply_single _ x m
  rw [hleg]
  have hw : Sigma.ι (fun _ : (stdSimplexPresheaf' S n).obj U => G.obj U) x ≫
      (Sigma.whiskerEquiv (f := fun _ : (stdSimplexPresheaf' S n).obj U => G.obj U)
        (g := fun _ : n ⟶ (totalSimplexDegree S).leftOp.obj U => G.obj U)
        (stdSimplexPresheafObjEquiv S n U) (fun _ => Iso.refl _)).hom =
      Sigma.ι (fun _ : n ⟶ (totalSimplexDegree S).leftOp.obj U => G.obj U)
        (stdSimplexPresheafObjEquiv S n U x) := by
    simp [Sigma.whiskerEquiv]
  exact congrArg (fun k => AddCommGrpCat.Hom.hom k m) hw

/-- **The copower of an abelian presheaf by the presheaf of `n`-simplices is the degree-`n` term
of its simplex-coefficient presheaf.** Both have one summand of `G` for each simplex map out of
`⦋n⦌` into the simplicial degree, and both reindex the summands by postcomposition. -/
def copowerStdSimplexIso :
    copowerPresheafObj (stdSimplexPresheaf' S n) G ≅
      ((simplexCoefficientDiagram' (totalSimplexDegree S).leftOp).obj G).obj (Opposite.op n) :=
  NatIso.ofComponents (copowerStdSimplexIsoApp S n G) (by
    intro U V f
    apply AddCommGrpCat.hom_ext
    apply Finsupp.addHom_ext
    intro x m
    change AddCommGrpCat.Hom.hom (copowerStdSimplexIsoApp S n G V).hom
        (AddCommGrpCat.Hom.hom (copowerRestriction (stdSimplexPresheaf' S n) G f)
          (Finsupp.single x m)) =
      AddCommGrpCat.Hom.hom
        ((((simplexCoefficientDiagram' (totalSimplexDegree S).leftOp).obj G).obj
          (Opposite.op n)).map f)
        (AddCommGrpCat.Hom.hom (copowerStdSimplexIsoApp S n G U).hom (Finsupp.single x m))
    rw [copowerRestriction_single, copowerStdSimplexIsoApp_hom_single,
      copowerStdSimplexIsoApp_hom_single, stdSimplexPresheafObjEquiv_map]
    have hι := ι_copowerMap (C := AddCommGrpCat.{u})
      (fun φ : n ⟶ (totalSimplexDegree S).leftOp.obj U =>
        φ ≫ (totalSimplexDegree S).leftOp.map f)
      (G.map f) (stdSimplexPresheafObjEquiv S n U x)
    exact congrArg (fun k => AddCommGrpCat.Hom.hom k m) hι.symm)

/-- The value of the identification on the summand labelled by a section of the presheaf of
`n`-simplices. -/
theorem copowerStdSimplexIso_hom_app_single (U : S.totalCategoryᵒᵖ)
    (x : (stdSimplexPresheaf' S n).obj U) (m : (G.obj U : Type u)) :
    AddCommGrpCat.Hom.hom ((copowerStdSimplexIso S n G).hom.app U) (Finsupp.single x m) =
      AddCommGrpCat.Hom.hom
        (Sigma.ι (fun _ : n ⟶ (totalSimplexDegree S).leftOp.obj U => G.obj U)
          (stdSimplexPresheafObjEquiv S n U x)) m :=
  copowerStdSimplexIsoApp_hom_single S n G U x m

end CategoryTheory.SimplicialSiteSituation

end
