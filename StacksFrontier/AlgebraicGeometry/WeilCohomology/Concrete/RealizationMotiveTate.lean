module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationMotive
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilRealization
public import StacksFrontier.CategoryTheory.Graded.TwistedKaroubiTateRealization
public import StacksFrontier.CategoryTheory.GradedObject.MonoidalFunctorKunneth
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# The realization of Chow motives attached to Weil cohomology data

Let `G : M_k ⥤ graded F-vector spaces` be the functor of Stacks 0FHL attached to data (D0)–(D3)
satisfying (A), (B) and (C) (`Stacks.WeilCohomology.WeilData.motiveFunctor`). This file proves that
`G(𝟏(1))` is concentrated in degree `-2`, so that `G` is a realization in the sense of side (2) of
Stacks 0FHM (`Stacks.WeilCohomology.WeilRealization`).

## Proof

The Lefschetz motive `(P¹_k, c₂, 0)` is isomorphic to `𝟏(-1)` (Stacks 0FGD), and it is the image
of the projector `c₂` on `(P¹_k, 1, 0)`. Since `G` restricts on degree-zero correspondences to
`c ↦ pr₂,*(γ(c) ∪ pr₁^*-)`, `G(𝟏(-1))` is the image of `G(c₂)` on `H^*(P¹_k)`, a line in degree
`2` (`Stacks.WeilCohomology.WeilData.fibrePointImage_finrank_and_isZero`). As `G(𝟏(1))` is a
line in a single degree `a` (it is invertible) and `G(𝟏(1)) ⊗ G(𝟏(-1)) ≅ G(𝟏)` lives in degree
`0`, `a + 2 = 0`.

## Main results

* `Stacks.WeilCohomology.WeilData.motiveFunctor_tate_degree`: `G(𝟏(1))` is concentrated in degree
  `-2`.
* `Stacks.WeilCohomology.WeilDataAxioms.toWeilRealization`: the realization attached to data
  (D0)–(D3) satisfying (A), (B) and (C).

## References

* [Stacks Project, Tag 0FHL](https://stacks.math.columbia.edu/tag/0FHL)
* [Stacks Project, Tag 0FHM](https://stacks.math.columbia.edu/tag/0FHM)
* [Stacks Project, Tag 0FGD](https://stacks.math.columbia.edu/tag/0FGD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow MonoidalCategory
  CategoryTheory.GradedCategory Idempotents
open scoped TensorProduct

universe u w

namespace CategoryTheory.GradedCategory.TwistedKaroubi

variable {C : Type*} [Category C] [Preadditive C] [GradedCategory ℚ C] {𝒟 : Type*} [Category 𝒟]
  {G : TwistedKaroubi ℚ C ⥤ 𝒟} {F₀ : DegreeZero ℚ C ⥤ 𝒟}

/-- If `G` restricts along `X ↦ (X, 1, 0)` to `F₀`, then `G` of `(X, p, 0)` is the image of
`F₀(p)` on `F₀(X)`: it is isomorphic to any retract `U` of `F₀(X)` cutting out `F₀(p)`. -/
def untwistedObjIsoOfRetract (φ : toKaroubi (DegreeZero ℚ C) ⋙ untwisted ℚ C ⋙ G ≅ F₀)
    (P : Karoubi (DegreeZero ℚ C)) {U : 𝒟} (i : U ⟶ F₀.obj P.X) (e : F₀.obj P.X ⟶ U)
    (hie : i ≫ e = 𝟙 U) (hei : e ≫ i = F₀.map P.p) : (untwisted ℚ C ⋙ G).obj P ≅ U where
  hom := (untwisted ℚ C ⋙ G).map P.decompId_i ≫ φ.hom.app P.X ≫ e
  inv := i ≫ φ.inv.app P.X ≫ (untwisted ℚ C ⋙ G).map P.decompId_p
  hom_inv_id := by
    have h₁ : φ.hom.app P.X ≫ F₀.map P.p ≫ φ.inv.app P.X =
        (untwisted ℚ C ⋙ G).map ((toKaroubi _).map P.p) :=
      NatIso.naturality_2 φ P.p
    have h₂ : (untwisted ℚ C ⋙ G).map P.decompId_i ≫ (untwisted ℚ C ⋙ G).map P.decompId_p =
        𝟙 _ := by
      rw [← Functor.map_comp, ← P.decompId, Functor.map_id]
    calc _ = (untwisted ℚ C ⋙ G).map P.decompId_i ≫
          (φ.hom.app P.X ≫ (e ≫ i) ≫ φ.inv.app P.X) ≫ (untwisted ℚ C ⋙ G).map P.decompId_p := by
          simp only [Category.assoc]
      _ = 𝟙 _ := by
        rw [hei, h₁, Karoubi.decomp_p, Functor.map_comp, Category.assoc,
          ← Category.assoc ((untwisted ℚ C ⋙ G).map P.decompId_i), h₂, Category.id_comp]
  inv_hom_id := by
    have h₁ : φ.inv.app P.X ≫ (untwisted ℚ C ⋙ G).map ((toKaroubi _).map P.p) ≫ φ.hom.app P.X =
        F₀.map P.p :=
      NatIso.naturality_1 φ P.p
    calc _ = i ≫ (φ.inv.app P.X ≫ ((untwisted ℚ C ⋙ G).map P.decompId_p ≫
          (untwisted ℚ C ⋙ G).map P.decompId_i) ≫ φ.hom.app P.X) ≫ e := by
          simp only [Category.assoc]
      _ = 𝟙 U := by
        rw [← Functor.map_comp, ← Karoubi.decomp_p, h₁, ← hei, Category.assoc,
          ← Category.assoc i e, hie, Category.id_comp]

end CategoryTheory.GradedCategory.TwistedKaroubi

namespace Stacks.WeilCohomology.WeilData

open SmoothProjectiveScheme

variable {k : Type u} [Field k] {F : Type w} [Field F] [CharZero F] {W : WeilData k F}
  (hA : W.PoincareDuality) (hB : W.Kunneth) (hC : W.CycleClassAxiom hA.perfectPairing)

omit [CharZero F] in
/-- A degree of `V ⊗ W` receiving a summand `Vᵃ ⊗ Wᵇ` of two lines is nonzero. -/
private lemma not_isZero_tensorObj_apply (V W : GradedObject ℤ (ModuleCat.{w} F)) {a b : ℤ}
    (ha : Module.finrank F (V a) = 1) (hb : Module.finrank F (W b) = 1) :
    ¬ IsZero ((V ⊗ W) (a + b)) := by
  have := Module.finite_of_finrank_eq_succ ha
  have := Module.finite_of_finrank_eq_succ hb
  have h₁ : Module.finrank F (V a ⊗[F] W b) = 1 := by
    rw [Module.finrank_tensorProduct, ha, hb]
  have : Nontrivial (V a ⊗[F] W b) := Module.nontrivial_of_finrank_eq_succ h₁
  have := (GradedObject.Monoidal.ιTensorObj_injective V W a b (a + b) rfl).nontrivial
  rw [ModuleCat.isZero_iff_subsingleton, ← not_nontrivial_iff_subsingleton, not_not]
  assumption

section Braided

attribute [local instance 10000] GradedObject.koszulBraidedCategory
  GradedObject.koszulSymmetricCategory

attribute [local instance] motiveFunctorBraided

variable (x : (fieldChowSituation k).S ⟶ relativeProjectiveLine (Spec (CommRingCat.of k)))
  (hx : x ≫ (relativeProjectiveLine (Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) =
    𝟙 (fieldChowSituation k).S)

/-- `G` of the Lefschetz motive `(P¹_k, c₂, 0)` is the image of `G(c₂)` on `H^*(P¹_k)`. -/
def motiveFunctorLefschetzIso :
    (TwistedKaroubi.untwisted ℚ (CorrespondenceCategory k) ⋙ motiveFunctor hA hB hC).obj
      (ChowMotiveCat.lefschetzKaroubi x hx) ≅ fibrePointImage hA hB hC x hx :=
  TwistedKaroubi.untwistedObjIsoOfRetract (motiveFunctorIso hA hB hC) _
    (fun n ↦ ModuleCat.ofHom (LinearMap.ker (pointRestrict hA hB hC x hx n)).subtype)
    (fun n ↦ ModuleCat.ofHom (LinearMap.codRestrict (LinearMap.ker (pointRestrict hA hB hC x hx n))
      (fibrePointMap hA hB hC x hx n) (pointRestrict_fibrePoint hA hB hC x hx n)))
    (by
      funext n
      ext v
      exact congrArg Subtype.val (fibrePoint_apply_of_mem_ker hA hB hC x hx n v v.2))
    (by
      funext n
      ext v
      rfl)

/-- **`G(𝟏(1))` is concentrated in degree `-2`.** `G(𝟏(-1)) = G(P¹_k, c₂, 0)` is the line
`H^2(P¹_k)` in degree `2` (Stacks 0FGD, 0FHI), `G(𝟏(1))` is a line in some degree `a`, being
invertible, and `G(𝟏(1)) ⊗ G(𝟏(-1)) ≅ G(𝟏)` is concentrated in degree `0`, so `a + 2 = 0`. -/
theorem motiveFunctor_tate_degree :
    ∀ i : ℤ, i ≠ -2 → IsZero ((motiveFunctor hA hB hC).obj (ChowMotiveCat.tate k 1) i) := by
  let x := ChowMotiveCat.projectiveLineZero k
  have hx := ChowMotiveCat.projectiveLineZero_comp (k := k)
  have eL : (motiveFunctor hA hB hC).obj (ChowMotiveCat.tate k (-1)) ≅
      fibrePointImage hA hB hC x hx :=
    (motiveFunctor hA hB hC).mapIso (ChowMotiveCat.lefschetzKaroubiIso x hx).symm ≪≫
      motiveFunctorLefschetzIso hA hB hC x hx
  have h₂ : Module.finrank F ((motiveFunctor hA hB hC).obj (ChowMotiveCat.tate k (-1)) 2) = 1 :=
    ((GradedObject.eval 2).mapIso eL).toLinearEquiv.finrank_eq.trans
      (fibrePointImage_finrank_and_isZero hA hB hC x hx).1
  obtain ⟨a, ha, hz⟩ := TwistedKaroubi.exists_finrank_tateTriple_eq_one (motiveFunctor hA hB hC) 1
  have e : (motiveFunctor hA hB hC).obj (ChowMotiveCat.tate k 1) ⊗
      (motiveFunctor hA hB hC).obj (ChowMotiveCat.tate k (-1)) ≅
        (motiveFunctor hA hB hC).obj (𝟙_ (ChowMotiveCat k)) :=
    Functor.Monoidal.μIso (motiveFunctor hA hB hC) _ _ ≪≫
      (motiveFunctor hA hB hC).mapIso (ChowMotiveCat.tateHasInverse 1 (-1) (by norm_num)).isoLeft
  have ha₂ : a + 2 = 0 := by
    by_contra h
    exact not_isZero_tensorObj_apply _ _ ha h₂
      ((Functor.isZero_unit_apply h).of_iso ((GradedObject.eval _).mapIso e))
  exact fun i hi ↦ hz i (by omega)

end Braided

end Stacks.WeilCohomology.WeilData

namespace Stacks.WeilCohomology.WeilDataAxioms

variable {k : Type u} [Field k] {F : Type w} [Field F] [CharZero F]

/-- **The realization attached to data (D0)–(D3) satisfying (A), (B) and (C)** (side (2) of
Stacks 0FHM): the `ℚ`-linear functor `G : M_k ⥤ graded F-vector spaces` of symmetric monoidal
categories of Stacks 0FHL, with `G(𝟏(1))` concentrated in degree `-2`. -/
def toWeilRealization (T : WeilDataAxioms k F) : WeilRealization k F where
  functor := T.motiveFunctor
  braided := WeilData.motiveFunctorBraided _ _ _
  additive := WeilData.motiveFunctor_additive _ _ _
  linear := WeilData.motiveFunctor_linear _ _ _
  tate_degree := WeilData.motiveFunctor_tate_degree _ _ _

/-- The underlying functor of the realization of `T` is `T.motiveFunctor`. -/
theorem toWeilRealization_functor (T : WeilDataAxioms k F) :
    T.toWeilRealization.functor = T.motiveFunctor :=
  rfl

section Braided

attribute [local instance 10000] GradedObject.koszulBraidedCategory
  GradedObject.koszulSymmetricCategory

attribute [local instance] WeilData.corrFunctorBraided

/-- The realization of `T` restricts along `X ↦ (X, 1, 0)` to the realization
`c ↦ pr₂,*(γ(c) ∪ pr₁^*-)` of correspondences of degree zero. -/
def toWeilRealizationIso (T : WeilDataAxioms k F) :
    TwistedKaroubi.untwistedOfObj (CorrespondenceCategory k) ⋙ T.toWeilRealization.functor ≅
      WeilData.corrFunctor T.poincareDuality T.kunneth T.cycleClassAxiom :=
  WeilData.motiveFunctorIso _ _ _

/-- The isomorphism `toWeilRealizationIso` is a monoidal natural isomorphism. -/
instance toWeilRealizationIso_isMonoidal (T : WeilDataAxioms k F) :
    NatTrans.IsMonoidal T.toWeilRealizationIso.hom :=
  WeilData.motiveFunctorIso_isMonoidal _ _ _

end Braided

end Stacks.WeilCohomology.WeilDataAxioms

end
