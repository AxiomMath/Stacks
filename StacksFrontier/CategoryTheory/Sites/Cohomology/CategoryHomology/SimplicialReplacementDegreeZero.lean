module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.SimplicialReplacementChainMap

/-!
# Degree-zero homology of the simplicial replacement

Let `C` be a small category and `G` an abelian-group-valued presheaf on `C`. The simplicial
replacement complex `K_•(G)` of `Stacks.CategoryHomology.simplicialReplacementComplex` has
`K_0(G) = ⨁_U G(U)` and `K_1(G) = ⨁_{U₁ → U₀} G(U₀)`, with differential the difference of the
two faces: on the summand indexed by an arrow `a : U₁ ⟶ U₀` carrying a section `s` over `U₀`
it is the difference of `s` in the summand at `U₀` and `G(a)(s)` in the summand at `U₁`. Those
are exactly the relations defining `colim_{Cᵒᵖ} G`, so the canonical map
`⨁_U G(U) ⟶ colim G` is a cokernel of the differential and

  `H_0(K_•(G)) ≅ colim G`

canonically, compatibly with chain maps that are compatible with the augmentations in degree
zero. This is the degree-zero case of the identification of `H_n(K_•(G))` with the `n`th left
derived functor of `colim` in Stacks 08PG.

## Main definitions

* `Stacks.CategoryHomology.replacementObjInclusion`: the inclusion `G(U) ⟶ K_0(G)` of the
  summand indexed by an object.
* `Stacks.CategoryHomology.replacementAugmentation`: the canonical map `K_0(G) ⟶ colim G`.
* `Stacks.CategoryHomology.replacementAugmentationCocone`: the cocone on `G` attached to a map
  out of `K_0(G)` which kills the differential.
* `Stacks.CategoryHomology.replacementOpcyclesZeroIsoColimit` and
  `Stacks.CategoryHomology.replacementHomologyZeroIsoColimit`: the comparison of the degree-zero
  opcycles, respectively homology, of `K_•(G)` with `colim G`.

## Main results

* `Stacks.CategoryHomology.simplicialReplacementComplex_d_one_zero_summand`: the differential
  `K_1(G) ⟶ K_0(G)` on a summand.
* `Stacks.CategoryHomology.d_one_zero_comp_replacementAugmentation`: the augmentation kills the
  differential.
* `Stacks.CategoryHomology.replacementAugmentation_isColimit`: the augmentation is a cokernel of
  the differential.
* `Stacks.CategoryHomology.replacementHomologyZeroIsoColimit_naturality`: a chain map of
  simplicial replacements compatible with the augmentations in degree zero induces, on
  degree-zero homology, the map it is compatible with.

## Implementation notes

The index of the image of a summand under a face map is `x.whiskerLeft θ`, which is equal to
the `ComposableArrows.mk₀` of an object (`CategoryTheory.ComposableArrows.ext₀`) but not
definitionally so; `Stacks.CategoryHomology.replacementSummand_congr` transports along that
equality.

`Stacks.CategoryHomology.replacementObjInclusion` is indexed by an object of `Cᵒᵖ` and declared
with source `G.obj U`. Indexed by `ComposableArrows.mk₀ U.unop`, its source would be only
definitionally `G.obj U`, and `Category.comp_id` and `ConcreteCategory.comp_apply` would stop
rewriting in composites formed with it.

## References

* [Stacks Project, Tag 08PG](https://stacks.math.columbia.edu/tag/08PG)
* [Stacks Project, Tag 08RZ](https://stacks.math.columbia.edu/tag/08RZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum

universe u v

namespace Stacks.CategoryHomology

variable {C : Type u} [SmallCategory C]

/-- Two summands of a simplicial replacement group with equal indices and corresponding
coefficients agree. -/
lemma replacementSummand_congr (G : Cᵒᵖ ⥤ AddCommGrpCat.{v}) (n : ℕ)
    {x y : ComposableArrows C n} (h : x = y) (s : G.obj (op x.right))
    (t : G.obj (op y.right)) (hst : HEq s t) :
    replacementSummand G n x s = replacementSummand G n y t := by
  subst h
  rw [eq_of_heq hst]

variable (G : Cᵒᵖ ⥤ AddCommGrpCat.{max u v})

/-- The inclusion of the summand of `K_0(G)` indexed by an object `U` of `Cᵒᵖ`. -/
noncomputable def replacementObjInclusion (U : Cᵒᵖ) : G.obj U ⟶ replacementGroup G 0 := by
  classical
  exact AddCommGrpCat.ofHom
    (DirectSum.of (fun y : ComposableArrows C 0 => G.obj (op y.right))
      (ComposableArrows.mk₀ U.unop))

/-- `Stacks.CategoryHomology.replacementObjInclusion` is the inclusion of the summand indexed by
the constant string at `U`. -/
lemma replacementObjInclusion_apply (U : Cᵒᵖ) (s : G.obj U) :
    (replacementObjInclusion G U).hom s =
      replacementSummand G 0 (ComposableArrows.mk₀ U.unop) s :=
  rfl

/-- The canonical map from degree zero of the simplicial replacement to the colimit: on the
summand indexed by an object it is the colimit injection. -/
noncomputable def replacementAugmentation : replacementGroup G 0 ⟶ colimit G := by
  classical
  exact AddCommGrpCat.ofHom <| DirectSum.toAddMonoid fun x : ComposableArrows C 0 =>
    (colimit.ι G (op x.right)).hom

/-- The value of `Stacks.CategoryHomology.replacementAugmentation` on a summand. -/
lemma replacementAugmentation_summand (x : ComposableArrows C 0) (s : G.obj (op x.right)) :
    (replacementAugmentation G).hom (replacementSummand G 0 x s) =
      (colimit.ι G (op x.right)).hom s := by
  classical
  simp only [replacementAugmentation, replacementSummand, AddCommGrpCat.hom_ofHom,
    DirectSum.toAddMonoid_of]

/-- The augmentation restricted to the summand at `U` is the colimit injection at `U`. -/
lemma replacementObjInclusion_comp_replacementAugmentation (U : Cᵒᵖ) :
    replacementObjInclusion G U ≫ replacementAugmentation G = colimit.ι G U := by
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun s => ?_)
  exact (ConcreteCategory.comp_apply _ _ s).trans
    (replacementAugmentation_summand G (ComposableArrows.mk₀ U.unop) s)

/-- A face map `K_1(G) ⟶ K_0(G)` sends a summand to the summand at the endpoint it keeps, once
the coefficient has been identified. -/
private lemma replacementMap_delta_summand (i : Fin 2) (x : ComposableArrows C 1)
    (s : G.obj (op x.right)) (y : C)
    (hy : x.obj ((simplexIndexMap (SimplexCategory.δ i).op.unop).obj (Fin.last 0)) = y)
    (t : G.obj (op y))
    (hcoef : HEq ((G.map (op (x.map (homOfLE (Fin.le_last
      ((simplexIndexMap (SimplexCategory.δ i).op.unop).obj (Fin.last 0))))))).hom s) t) :
    (replacementMap G (SimplexCategory.δ i).op).hom (replacementSummand G 1 x s) =
      replacementSummand G 0 (ComposableArrows.mk₀ y) t :=
  (replacementMap_on_generator G (SimplexCategory.δ i).op x s).trans
    (replacementSummand_congr G 0 (ComposableArrows.ext₀ hy) _ _ hcoef)

/-- The zeroth face map `K_1(G) ⟶ K_0(G)` keeps the right endpoint of a string and its
coefficient. -/
lemma replacementMap_delta_zero_summand (x : ComposableArrows C 1) (s : G.obj (op x.right)) :
    (replacementMap G (SimplexCategory.δ (0 : Fin 2)).op).hom (replacementSummand G 1 x s) =
      replacementSummand G 0 (ComposableArrows.mk₀ x.right) s := by
  refine replacementMap_delta_summand G 0 x s _ rfl s ?_
  have hid : (op (x.map (homOfLE (Fin.le_last
      ((simplexIndexMap (SimplexCategory.δ (0 : Fin 2)).op.unop).obj (Fin.last 0))))) :
      op x.right ⟶ op x.right) = 𝟙 (op x.right) :=
    congrArg Quiver.Hom.op
      ((congrArg x.map (Subsingleton.elim _ (𝟙 _))).trans (x.map_id _))
  exact heq_of_eq ((congrArg (fun m => (G.map m).hom s) hid).trans (by simp))

/-- The first face map `K_1(G) ⟶ K_0(G)` keeps the left endpoint of a string and restricts its
coefficient along the string. -/
lemma replacementMap_delta_one_summand (x : ComposableArrows C 1) (s : G.obj (op x.right)) :
    (replacementMap G (SimplexCategory.δ (1 : Fin 2)).op).hom (replacementSummand G 1 x s) =
      replacementSummand G 0 (ComposableArrows.mk₀ x.left) ((G.map (op x.hom)).hom s) :=
  replacementMap_delta_summand G 1 x s _ rfl _
    (heq_of_eq (congrArg (fun m => (G.map (op (x.map m))).hom s) (Subsingleton.elim _ _)))

/-- The differential `K_1(G) ⟶ K_0(G)` of the simplicial replacement complex is the difference
of the two faces. -/
lemma simplicialReplacementComplex_d_one_zero :
    (simplicialReplacementComplex G).d 1 0 =
      replacementMap G (SimplexCategory.δ (0 : Fin 2)).op -
        replacementMap G (SimplexCategory.δ (1 : Fin 2)).op := by
  rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d _ 0,
    AlgebraicTopology.AlternatingFaceMapComplex.objD, Fin.sum_univ_two,
    Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_one_zsmul, ← sub_eq_add_neg]
  rfl

/-- The differential `K_1(G) ⟶ K_0(G)` on the summand indexed by a string `x` of one arrow: the
coefficient `s` over the right endpoint of `x`, minus its restriction along `x` placed in the
summand at the left endpoint. -/
lemma simplicialReplacementComplex_d_one_zero_summand (x : ComposableArrows C 1)
    (s : G.obj (op x.right)) :
    ((simplicialReplacementComplex G).d 1 0).hom (replacementSummand G 1 x s) =
      (replacementObjInclusion G (op x.right)).hom s -
        (replacementObjInclusion G (op x.left)).hom ((G.map (op x.hom)).hom s) := by
  rw [simplicialReplacementComplex_d_one_zero, AddCommGrpCat.hom_sub, AddMonoidHom.sub_apply,
    replacementMap_delta_zero_summand, replacementMap_delta_one_summand]
  rfl

/-- The canonical map `K_0(G) ⟶ colim G` kills the differential out of `K_1(G)`. -/
theorem d_one_zero_comp_replacementAugmentation :
    (simplicialReplacementComplex G).d 1 0 ≫ replacementAugmentation G = 0 := by
  refine replacementGroup_hom_ext 1 fun x s => ?_
  have hw := ConcreteCategory.congr_hom (colimit.w G (op x.hom)) s
  rw [ConcreteCategory.comp_apply] at hw
  rw [ConcreteCategory.comp_apply, simplicialReplacementComplex_d_one_zero_summand, map_sub,
    ← ConcreteCategory.comp_apply (replacementObjInclusion G _),
    ← ConcreteCategory.comp_apply (replacementObjInclusion G _),
    replacementObjInclusion_comp_replacementAugmentation,
    replacementObjInclusion_comp_replacementAugmentation, hw]
  exact sub_self _

/-- The restrictions to the summands of a map out of `K_0(G)` which kills the differential are
compatible with the restriction maps of `G`. -/
lemma replacementAugmentationCocone_aux {T : AddCommGrpCat.{max u v}}
    (h : replacementGroup G 0 ⟶ T)
    (hh : (simplicialReplacementComplex G).d 1 0 ≫ h = 0) {U V : Cᵒᵖ} (g : U ⟶ V)
    (s : G.obj U) :
    h.hom ((replacementObjInclusion G V).hom ((G.map g).hom s)) =
      h.hom ((replacementObjInclusion G U).hom s) := by
  have h₀ := ConcreteCategory.congr_hom hh
    (replacementSummand G 1 (ComposableArrows.mk₁ g.unop) s)
  rw [ConcreteCategory.comp_apply, simplicialReplacementComplex_d_one_zero_summand,
    map_sub] at h₀
  exact (sub_eq_zero.mp (h₀.trans (by simp))).symm

/-- The cocone on `G` determined by a map out of degree zero of the simplicial replacement which
kills the differential. -/
noncomputable def replacementAugmentationCocone {T : AddCommGrpCat.{max u v}}
    (h : replacementGroup G 0 ⟶ T)
    (hh : (simplicialReplacementComplex G).d 1 0 ≫ h = 0) : Cocone G where
  pt := T
  ι :=
    { app := fun U => replacementObjInclusion G U ≫ h
      naturality := fun U V g => by
        refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun s => ?_)
        simp only [Functor.const_obj_map, ConcreteCategory.comp_apply]
        exact replacementAugmentationCocone_aux G h hh g s }

/-- The canonical map `K_0(G) ⟶ colim G` is a cokernel of the differential
`K_1(G) ⟶ K_0(G)`. -/
noncomputable def replacementAugmentation_isColimit :
    IsColimit (CokernelCofork.ofπ (replacementAugmentation G)
      (d_one_zero_comp_replacementAugmentation G)) :=
  Cofork.IsColimit.mk _
    (fun S => colimit.desc G (replacementAugmentationCocone G S.π (CokernelCofork.condition S)))
    (fun S => by
      refine replacementGroup_hom_ext 0 fun x s => ?_
      have hmk : (ComposableArrows.mk₀ x.right : ComposableArrows C 0) = x :=
        ComposableArrows.ext₀ rfl
      have hfac : (colimit.ι G (op x.right) ≫
          colimit.desc G
            (replacementAugmentationCocone G S.π (CokernelCofork.condition S))).hom s
          = S.π.hom (replacementSummand G 0 (ComposableArrows.mk₀ x.right) s) :=
        ConcreteCategory.congr_hom
          (colimit.ι_desc
            (replacementAugmentationCocone G S.π (CokernelCofork.condition S))
            (op x.right)) s
      exact (ConcreteCategory.comp_apply _ _ _).trans
        ((congrArg
            (colimit.desc G
              (replacementAugmentationCocone G S.π (CokernelCofork.condition S))).hom
            (replacementAugmentation_summand G x s)).trans
          (((ConcreteCategory.comp_apply _ _ s).symm.trans hfac).trans
            (congrArg S.π.hom (replacementSummand_congr G 0 hmk _ _ HEq.rfl)))))
    (fun S m hm => colimit.hom_ext fun j =>
      (by
        rw [← replacementObjInclusion_comp_replacementAugmentation, Category.assoc]
        exact congrArg (replacementObjInclusion G j ≫ ·) hm :
        colimit.ι G j ≫ m = replacementObjInclusion G j ≫ S.π).trans
        (colimit.ι_desc (replacementAugmentationCocone G S.π (CokernelCofork.condition S)) j).symm)

/-- The degree-zero opcycles of the simplicial replacement complex of `G` are the colimit
of `G`. -/
noncomputable def replacementOpcyclesZeroIsoColimit :
    (simplicialReplacementComplex G).opcycles 0 ≅ colimit G :=
  IsColimit.coconePointUniqueUpToIso
    (HomologicalComplex.opcyclesIsCokernel (simplicialReplacementComplex G) 1 0 (by simp))
    (replacementAugmentation_isColimit G)

/-- `Stacks.CategoryHomology.replacementOpcyclesZeroIsoColimit` is compatible with the
augmentation. -/
@[reassoc]
lemma pOpcycles_comp_replacementOpcyclesZeroIsoColimit :
    (simplicialReplacementComplex G).pOpcycles 0 ≫ (replacementOpcyclesZeroIsoColimit G).hom =
      replacementAugmentation G :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (HomologicalComplex.opcyclesIsCokernel (simplicialReplacementComplex G) 1 0 (by simp))
    (replacementAugmentation_isColimit G) WalkingParallelPair.one

/-- The degree-zero homology of the simplicial replacement complex of `G` is the colimit
of `G`. -/
noncomputable def replacementHomologyZeroIsoColimit :
    (simplicialReplacementComplex G).homology 0 ≅ colimit G :=
  ChainComplex.isoHomologyι₀ (simplicialReplacementComplex G) ≪≫
    replacementOpcyclesZeroIsoColimit G

/-- A chain map of simplicial replacement complexes which is compatible in degree zero with the
augmentations induces, on degree-zero homology, the map it is compatible with. -/
theorem replacementHomologyZeroIsoColimit_naturality
    {G' : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}}
    (Φ : simplicialReplacementComplex G ⟶ simplicialReplacementComplex G')
    (ψ : colimit G ⟶ colimit G')
    (hΦ : Φ.f 0 ≫ replacementAugmentation G' = replacementAugmentation G ≫ ψ) :
    HomologicalComplex.homologyMap Φ 0 ≫ (replacementHomologyZeroIsoColimit G').hom =
      (replacementHomologyZeroIsoColimit G).hom ≫ ψ := by
  have hop : HomologicalComplex.opcyclesMap Φ 0 ≫ (replacementOpcyclesZeroIsoColimit G').hom =
      (replacementOpcyclesZeroIsoColimit G).hom ≫ ψ := by
    rw [← cancel_epi ((simplicialReplacementComplex G).pOpcycles 0),
      HomologicalComplex.p_opcyclesMap_assoc,
      pOpcycles_comp_replacementOpcyclesZeroIsoColimit,
      pOpcycles_comp_replacementOpcyclesZeroIsoColimit_assoc, hΦ]
  have hhom : HomologicalComplex.homologyMap Φ 0 ≫
      (ChainComplex.isoHomologyι₀ (simplicialReplacementComplex G')).hom =
      (ChainComplex.isoHomologyι₀ (simplicialReplacementComplex G)).hom ≫
        HomologicalComplex.opcyclesMap Φ 0 := by
    rw [← cancel_epi (ChainComplex.isoHomologyι₀ (simplicialReplacementComplex G)).inv,
      Iso.inv_hom_id_assoc, ChainComplex.isoHomologyι₀_inv_naturality_assoc, Iso.inv_hom_id,
      Category.comp_id]
  simp only [replacementHomologyZeroIsoColimit, Iso.trans_hom, Category.assoc,
    reassoc_of% hhom, hop]

end Stacks.CategoryHomology

end
