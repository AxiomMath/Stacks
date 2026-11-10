module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.SimplicialSiteMooreSheaf
public import StacksFrontier.CategoryTheory.Sites.CopowerSheafification
public import StacksFrontier.Cotangent.Triangle.DerivedFirstVertex

/-!
# The complex `s(-)` of a copower by a presheaf pulled back from the site

Let `(C, J)` be a small site and write `π : Δ × C ⥤ C` for the second projection. The pullback
`π⁻¹G = (Prod.snd _ _).op ⋙ G` of a presheaf of sets `G` on `C` is a presheaf of sets on `Δ × C`
which is constant in the simplicial direction. The copower of an abelian presheaf `P` on `Δ × C`
by such a pullback is therefore, read through `Stacks.SimplicialModules.simplicialCurry` as a
simplicial abelian presheaf on `C`, the degreewise copower by `G`: in simplicial degree `m` it is
the abelian presheaf `V ↦ ∐_{s ∈ G(V)} P(⦋m⦌, V)`.

Consequently the complex `s(-)` of the copower of a morphism `b` by `π⁻¹G` is a
quasi-isomorphism as soon as `s(b)` is.

## Main definitions

* `Stacks.SimplicialModules.prodPullbackIndex`: the pullback `π⁻¹G` to `Δ × C` of a presheaf of
  sets on `C`.
* `Stacks.SimplicialModules.simplicialCurryCopowerIso`: the curried copower by `π⁻¹G` is the
  degreewise copower by `G`.
* `Stacks.SimplicialModules.mooreAbPresheafCochainCopowerIso`: the same identification on Moore
  complexes, where it reads as the degreewise application of `Stacks.copowerFunctor`.

## Main results

* `Stacks.SimplicialModules.simplicialCurryCopowerIso_hom_naturality` and
  `Stacks.SimplicialModules.mooreAbPresheafCochainCopowerIso_hom_naturality`: both
  identifications commute with a morphism of abelian presheaves on `Δ × C`.
* `Stacks.SimplicialModules.quasiIso_mooreAbSheafCochain_copowerMap_prodPullbackIndex`: the
  complex `s(-)` of the copower of a morphism by `π⁻¹G` is a quasi-isomorphism as soon as `s(-)`
  of the morphism is.

## References

* [Stacks Project, Tag 09D2](https://stacks.math.columbia.edu/tag/09D2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology

universe u

namespace Stacks.SimplicialModules

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-! ### The pullback of a presheaf of sets along the projection `Δ × C ⥤ C` -/

/-- The pullback `π⁻¹G` of a presheaf of sets `G` on `C` along the second projection
`π : Δ × C ⥤ C`: the presheaf `(⦋m⦌, V) ↦ G(V)` on `Δ × C`, constant in the simplicial
direction. -/
abbrev prodPullbackIndex (G : Cᵒᵖ ⥤ Type u) : (SimplexCategory × C)ᵒᵖ ⥤ Type u :=
  (CategoryTheory.Prod.snd SimplexCategory C).op ⋙ G

/-! ### The curried copower by a pullback is the degreewise copower -/

/-- The structure map of the curried copower by `π⁻¹G` is the copower by `G` of the structure
map. -/
lemma simplicialCurry_obj_copower_map (G : Cᵒᵖ ⥤ Type u)
    (P : (SimplexCategory × C)ᵒᵖ ⥤ AddCommGrpCat.{u}) {m m' : SimplexCategoryᵒᵖ} (φ : m ⟶ m') :
    ((simplicialCurry AddCommGrpCat.{u}).obj (P.copower (prodPullbackIndex G))).map φ =
      Functor.copowerMap (((simplicialCurry AddCommGrpCat.{u}).obj P).map φ) (𝟙 G) := by
  refine NatTrans.ext (funext fun V => ?_)
  refine Limits.Sigma.hom_ext _ _ fun s => ?_
  set e := (prodOpEquiv SimplexCategory (D := C)).inverse.map
    ((φ, 𝟙 V) : ((m, V) : SimplexCategoryᵒᵖ × Cᵒᵖ) ⟶ (m', V)) with he
  have hid : (prodPullbackIndex G).map e s = s := by simp [he]
  refine ((Sigma.ι_comp_map' (g := fun _ => P.obj _) ((prodPullbackIndex G).map e)
      (fun _ => P.map e) s).trans ?_).trans
    (Functor.ι_copowerMap_app
      (((simplicialCurry AddCommGrpCat.{u}).obj P).map φ) (𝟙 G) V s).symm
  rw [hid]
  rfl

/-- The copower of an abelian presheaf on `Δ × C` by the pullback `π⁻¹G`, curried, is the
degreewise copower by `G`; the isomorphism has identity components. -/
def simplicialCurryCopowerIso (G : Cᵒᵖ ⥤ Type u)
    (P : (SimplexCategory × C)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (simplicialCurry AddCommGrpCat.{u}).obj (P.copower (prodPullbackIndex G)) ≅
      (simplicialCurry AddCommGrpCat.{u}).obj P ⋙ Stacks.copowerFunctor G :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun {_ _} φ =>
    (Category.comp_id _).trans
      ((simplicialCurry_obj_copower_map G P φ).trans (Category.id_comp _).symm))

/-- Currying carries the copower of a morphism by `π⁻¹G` to its degreewise copower by `G`, on
the nose in each simplicial degree. -/
lemma simplicialCurry_map_copowerMap_app (G : Cᵒᵖ ⥤ Type u)
    {P Q : (SimplexCategory × C)ᵒᵖ ⥤ AddCommGrpCat.{u}} (b : P ⟶ Q) (m : SimplexCategoryᵒᵖ) :
    ((simplicialCurry AddCommGrpCat.{u}).map
        (Functor.copowerMap b (𝟙 (prodPullbackIndex G)))).app m =
      (Functor.whiskerRight ((simplicialCurry AddCommGrpCat.{u}).map b)
        (Stacks.copowerFunctor G)).app m :=
  rfl

/-- The identification `Stacks.SimplicialModules.simplicialCurryCopowerIso` of the curried
copower with the degreewise copower is natural in the abelian presheaf. -/
lemma simplicialCurryCopowerIso_hom_naturality (G : Cᵒᵖ ⥤ Type u)
    {P Q : (SimplexCategory × C)ᵒᵖ ⥤ AddCommGrpCat.{u}} (b : P ⟶ Q) :
    (simplicialCurry AddCommGrpCat.{u}).map (Functor.copowerMap b (𝟙 (prodPullbackIndex G))) ≫
        (simplicialCurryCopowerIso G Q).hom =
      (simplicialCurryCopowerIso G P).hom ≫
        Functor.whiskerRight ((simplicialCurry AddCommGrpCat.{u}).map b)
          (Stacks.copowerFunctor G) :=
  NatTrans.ext (funext fun m =>
    (Category.comp_id _).trans
      ((simplicialCurry_map_copowerMap_app G b m).trans (Category.id_comp _).symm))

/-! ### The Moore complex of a copower by a pullback -/

/-- The presheaf-level Moore complex of the copower by `π⁻¹G` is the degreewise copower by `G`
of the Moore complex. -/
def mooreAbPresheafCochainCopowerIso (G : Cᵒᵖ ⥤ Type u)
    (P : (SimplexCategory × C)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (mooreAbPresheafCochain (C := C)).obj (P.copower (prodPullbackIndex G)) ≅
      ((Stacks.copowerFunctor G).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((mooreAbPresheafCochain (C := C)).obj P) :=
  (alternatingFaceMapCochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u})).mapIso
      (simplicialCurryCopowerIso G P) ≪≫
    ((alternatingFaceMapCochainComplexCompMapHomologicalComplexIso
      (Stacks.copowerFunctor G)).app ((simplicialCurry AddCommGrpCat.{u}).obj P)).symm

/-- The identification `Stacks.SimplicialModules.mooreAbPresheafCochainCopowerIso` of the Moore
complex of a copower with the degreewise copower of the Moore complex is natural in the abelian
presheaf. -/
lemma mooreAbPresheafCochainCopowerIso_hom_naturality (G : Cᵒᵖ ⥤ Type u)
    {P Q : (SimplexCategory × C)ᵒᵖ ⥤ AddCommGrpCat.{u}} (b : P ⟶ Q) :
    (mooreAbPresheafCochain (C := C)).map
          (Functor.copowerMap b (𝟙 (prodPullbackIndex G))) ≫
        (mooreAbPresheafCochainCopowerIso G Q).hom =
      (mooreAbPresheafCochainCopowerIso G P).hom ≫
        ((Stacks.copowerFunctor G).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((mooreAbPresheafCochain (C := C)).map b) := by
  have hnat :
      (alternatingFaceMapCochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u})).map
            (Functor.whiskerRight ((simplicialCurry AddCommGrpCat.{u}).map b)
              (Stacks.copowerFunctor G)) ≫
          ((alternatingFaceMapCochainComplexCompMapHomologicalComplexIso
            (Stacks.copowerFunctor G)).app
              ((simplicialCurry AddCommGrpCat.{u}).obj Q)).inv =
        ((alternatingFaceMapCochainComplexCompMapHomologicalComplexIso
          (Stacks.copowerFunctor G)).app
            ((simplicialCurry AddCommGrpCat.{u}).obj P)).inv ≫
          ((Stacks.copowerFunctor G).mapHomologicalComplex (ComplexShape.up ℤ)).map
            ((alternatingFaceMapCochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u})).map
              ((simplicialCurry AddCommGrpCat.{u}).map b)) :=
    (alternatingFaceMapCochainComplexCompMapHomologicalComplexIso
      (Stacks.copowerFunctor G)).inv.naturality ((simplicialCurry AddCommGrpCat.{u}).map b)
  dsimp only [mooreAbPresheafCochainCopowerIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Functor.comp_map]
  rw [← Category.assoc, ← Functor.map_comp, simplicialCurryCopowerIso_hom_naturality,
    Functor.map_comp, Category.assoc, hnat, Category.assoc]

/-! ### The complex `s(-)` of a copower by a pullback -/

/-- The complex `s(-)` of the copower of a morphism `b` by a pulled-back presheaf of sets
`π⁻¹G` is a quasi-isomorphism as soon as the complex `s(-)` of `b` is. -/
theorem quasiIso_mooreAbSheafCochain_copowerMap_prodPullbackIndex (G : Cᵒᵖ ⥤ Type u)
    {P Q : (SimplexCategory × C)ᵒᵖ ⥤ AddCommGrpCat.{u}} (b : P ⟶ Q)
    (hb : QuasiIso ((mooreAbSheafCochain J).map b)) :
    QuasiIso ((mooreAbSheafCochain J).map
      (Functor.copowerMap b (𝟙 (prodPullbackIndex G)))) := by
  have hb' : QuasiIso (((presheafToSheaf J AddCommGrpCat.{u}).mapHomologicalComplex
      (ComplexShape.up ℤ)).map ((mooreAbPresheafCochain (C := C)).map b)) := hb
  change QuasiIso (((presheafToSheaf J AddCommGrpCat.{u}).mapHomologicalComplex
    (ComplexShape.up ℤ)).map ((mooreAbPresheafCochain (C := C)).map
      (Functor.copowerMap b (𝟙 (prodPullbackIndex G)))))
  have hcop := Stacks.quasiIso_mapHomologicalComplex_presheafToSheaf_copowerFunctor J G
    ((mooreAbPresheafCochain (C := C)).map b) hb'
  have hcomp : QuasiIso
      (((presheafToSheaf J AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((mooreAbPresheafCochain (C := C)).map
            (Functor.copowerMap b (𝟙 (prodPullbackIndex G)))) ≫
        ((presheafToSheaf J AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (mooreAbPresheafCochainCopowerIso G Q).hom) := by
    rw [← Functor.map_comp, mooreAbPresheafCochainCopowerIso_hom_naturality, Functor.map_comp]
    infer_instance
  exact quasiIso_of_comp_right _
    (((presheafToSheaf J AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (mooreAbPresheafCochainCopowerIso G Q).hom)

end Stacks.SimplicialModules

end
