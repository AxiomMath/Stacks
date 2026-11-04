module

public import StacksFrontier.CategoryTheory.Adjunction.PullbackInternalHomPushforward
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormula

/-!
# The pullback map of internal Homs around a square

Consider a square of functors `L_f : S ⥤ T`, `L_g : S ⥤ S'`, `L_{f'} : S' ⥤ T'`, `L_{g'} : T ⥤ T'`
whose two composites are identified by `ε : L_{f'} L_g ≅ L_{g'} L_f`, with tensor bifunctors,
internal Homs and tensor comparisons on the four corners. If the four tensor comparisons are
compatible around the square (`Stacks.AffineProjectionFormula.TensorComparisonCompatible`) and
the tensor–Hom adjunction of `T'` is dinatural in its middle variable, then the maps
`φ : L H(M, K) ⟶ H(L M, L K)` of [Stacks, Tag 08JF] compose along the two sides of the square
to the same map, up to `ε`.

## Main results

* `CategoryTheory.PullbackInternalHom.pullbackHomMap_square`.
* `CategoryTheory.PullbackInternalHom.pullbackHomMap_chart_square` and
  `CategoryTheory.PullbackInternalHom.chart_square_of_homEquiv_symm`.
* `CategoryTheory.PullbackInternalHom.chart_iff_of_homEquiv_symm` and
  `CategoryTheory.PullbackInternalHom.chart_iff_of_homEquiv_symm_of_comp`: transport of an
  isomorphism-invariant property of maps around the square.

## References

* [Stacks Project, Tag 08JF](https://stacks.math.columbia.edu/tag/08JF)
-/

@[expose] public noncomputable section

namespace CategoryTheory.PullbackInternalHom

open Opposite
open scoped CategoryTheory.Prod

variable {S T S' T' : Type*} [Category S] [Category T] [Category S'] [Category T']
  {Lf : S ⥤ T} {Lf' : S' ⥤ T'} {Lg : S ⥤ S'} {Lg' : T ⥤ T'} {Lc : S ⥤ T'}
  (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)
  (TS : S ⥤ S ⥤ S) (TS' : S' ⥤ S' ⥤ S') (TT : T ⥤ T ⥤ T) (TT' : T' ⥤ T' ⥤ T')
  (μf : Functor.uncurry.obj TS ⋙ Lf ≅ Lf.prod Lf ⋙ Functor.uncurry.obj TT)
  (μf' : Functor.uncurry.obj TS' ⋙ Lf' ≅ Lf'.prod Lf' ⋙ Functor.uncurry.obj TT')
  (μg : Functor.uncurry.obj TS ⋙ Lg ≅ Lg.prod Lg ⋙ Functor.uncurry.obj TS')
  (μg' : Functor.uncurry.obj TT ⋙ Lg' ≅ Lg'.prod Lg' ⋙ Functor.uncurry.obj TT')
  (HS : Sᵒᵖ ⥤ S ⥤ S) (HS' : S'ᵒᵖ ⥤ S' ⥤ S') (HT : Tᵒᵖ ⥤ T ⥤ T) (HT' : T'ᵒᵖ ⥤ T' ⥤ T')
  (adjS : ∀ P : S, TS.flip.obj P ⊣ HS.obj (op P))
  (adjS' : ∀ P : S', TS'.flip.obj P ⊣ HS'.obj (op P))
  (adjT : ∀ P : T, TT.flip.obj P ⊣ HT.obj (op P))
  (adjT' : ∀ P : T', TT'.flip.obj P ⊣ HT'.obj (op P))

/-- The transpose of the pullback map of internal Homs is the inverse of the tensor comparison
followed by the image of the evaluation. -/
theorem homEquiv_symm_pullbackHomMap {C D : Type*} [Category C] [Category D] {F : C ⥤ D}
    (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D)
    (μ : Functor.uncurry.obj TC ⋙ F ≅ F.prod F ⋙ Functor.uncurry.obj TD)
    (HC : Cᵒᵖ ⥤ C ⥤ C) (HD : Dᵒᵖ ⥤ D ⥤ D)
    (adjC : ∀ P : C, TC.flip.obj P ⊣ HC.obj (op P))
    (adjD : ∀ P : D, TD.flip.obj P ⊣ HD.obj (op P)) (M K : C) :
    ((adjD (F.obj M)).homEquiv _ _).symm (pullbackHomMap TC TD μ HC HD adjC adjD M K) =
      μ.inv.app ((HC.obj (op M)).obj K, M) ≫ F.map ((adjC M).counit.app K) := by
  rw [pullbackHomMap, Equiv.symm_apply_apply]

/-- **The pullback map of internal Homs is natural in the target.** -/
theorem pullbackHomMap_naturality_right {C D : Type*} [Category C] [Category D] {F : C ⥤ D}
    (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D)
    (μ : Functor.uncurry.obj TC ⋙ F ≅ F.prod F ⋙ Functor.uncurry.obj TD)
    (HC : Cᵒᵖ ⥤ C ⥤ C) (HD : Dᵒᵖ ⥤ D ⥤ D)
    (adjC : ∀ P : C, TC.flip.obj P ⊣ HC.obj (op P))
    (adjD : ∀ P : D, TD.flip.obj P ⊣ HD.obj (op P)) (M : C) {K K' : C} (φ : K ⟶ K') :
    F.map ((HC.obj (op M)).map φ) ≫ pullbackHomMap TC TD μ HC HD adjC adjD M K' =
      pullbackHomMap TC TD μ HC HD adjC adjD M K ≫ (HD.obj (op (F.obj M))).map (F.map φ) := by
  apply ((adjD (F.obj M)).homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_right_symm,
    homEquiv_symm_pullbackHomMap, homEquiv_symm_pullbackHomMap]
  have hn := μ.inv.naturality (X := ((HC.obj (op M)).obj K, M))
    (Y := ((HC.obj (op M)).obj K', M)) (((HC.obj (op M)).map φ, 𝟙 M))
  simp only [Functor.comp_obj, Functor.prod_obj, Functor.uncurry_obj_obj, Functor.comp_map,
    Functor.prod_map, Functor.uncurry_obj_map, Functor.map_id, Category.comp_id] at hn
  simp only [Functor.flip_obj_map]
  rw [reassoc_of% hn]
  simp only [Category.assoc, ← F.map_comp]
  congr 2
  exact (adjC M).counit.naturality φ

/-- A map whose transpose is the inverse tensor comparison followed by the image of the
evaluation is the pullback map of internal Homs. -/
private theorem eq_pullbackHomMap_of_homEquiv_symm {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {TC : C ⥤ C ⥤ C} {TD : D ⥤ D ⥤ D}
    {μ : Functor.uncurry.obj TC ⋙ F ≅ F.prod F ⋙ Functor.uncurry.obj TD}
    {HC : Cᵒᵖ ⥤ C ⥤ C} {HD : Dᵒᵖ ⥤ D ⥤ D}
    {adjC : ∀ P : C, TC.flip.obj P ⊣ HC.obj (op P)}
    {adjD : ∀ P : D, TD.flip.obj P ⊣ HD.obj (op P)} {M K : C}
    {φ : F.obj ((HC.obj (op M)).obj K) ⟶ (HD.obj (op (F.obj M))).obj (F.obj K)}
    (h : ((adjD (F.obj M)).homEquiv _ _).symm φ =
      μ.inv.app ((HC.obj (op M)).obj K, M) ≫ F.map ((adjC M).counit.app K)) :
    φ = pullbackHomMap TC TD μ HC HD adjC adjD M K :=
  ((adjD (F.obj M)).homEquiv _ _).symm.injective
    (h.trans (homEquiv_symm_pullbackHomMap TC TD μ HC HD adjC adjD M K).symm)

/-- **The pullback maps of internal Homs around a square.** With `ε : L_{f'} L_g ≅ L_{g'} L_f`
the identification of the two composites, the map of [Stacks, Tag 08JF] along `L_g` followed by
the one along `L_{f'}` is `ε`, the map along `L_f` followed by the one along `L_{g'}`, and the
identifications `ε` in both variables of the internal Hom. -/
theorem pullbackHomMap_square (M K : S)
    (hsq : Stacks.AffineProjectionFormula.TensorComparisonCompatible eg ef
      (Functor.uncurry.obj TS) (Functor.uncurry.obj TS') (Functor.uncurry.obj TT)
      (Functor.uncurry.obj TT') μf.hom μf'.hom μg.hom μg'.hom ((HS.obj (op M)).obj K) M)
    (hD : ∀ {Q' Q : T'} (v : Q' ⟶ Q) {A Z : T'} (θ : A ⟶ (HT'.obj (op Q)).obj Z),
      ((adjT' Q').homEquiv A Z).symm (θ ≫ (HT'.map v.op).app Z) =
        (TT'.obj A).map v ≫ ((adjT' Q).homEquiv A Z).symm θ) :
    Lf'.map (pullbackHomMap TS TS' μg HS HS' adjS adjS' M K) ≫
        pullbackHomMap TS' TT' μf' HS' HT' adjS' adjT' (Lg.obj M) (Lg.obj K) =
      (Stacks.AffineProjectionFormula.squareCompositeIso eg ef).hom.app _ ≫
        Lg'.map (pullbackHomMap TS TT μf HS HT adjS adjT M K) ≫
        pullbackHomMap TT TT' μg' HT HT' adjT adjT' (Lf.obj M) (Lf.obj K) ≫
        (HT'.map ((Stacks.AffineProjectionFormula.squareCompositeIso eg ef).hom.app M).op).app _ ≫
        (HT'.obj (op (Lf'.obj (Lg.obj M)))).map
          ((Stacks.AffineProjectionFormula.squareCompositeIso eg ef).inv.app K) := by
  set ε := Stacks.AffineProjectionFormula.squareCompositeIso eg ef
  set H := (HS.obj (op M)).obj K
  apply ((adjT' (Lf'.obj (Lg.obj M))).homEquiv _ _).symm.injective
  conv_rhs => rw [← Category.assoc, ← Category.assoc, ← Category.assoc]
  rw [Adjunction.homEquiv_naturality_left_symm, homEquiv_symm_pullbackHomMap,
    Adjunction.homEquiv_naturality_right_symm, hD, Adjunction.homEquiv_naturality_left_symm,
    homEquiv_symm_pullbackHomMap]
  simp only [Functor.flip_obj_map]
  -- the left side
  have hL : (TT'.map (Lf'.map (pullbackHomMap TS TS' μg HS HS' adjS adjS' M K))).app
        (Lf'.obj (Lg.obj M)) ≫ μf'.inv.app ((HS'.obj (op (Lg.obj M))).obj (Lg.obj K), Lg.obj M) ≫
        Lf'.map ((adjS' (Lg.obj M)).counit.app (Lg.obj K)) =
      μf'.inv.app (Lg.obj H, Lg.obj M) ≫ Lf'.map (μg.inv.app (H, M)) ≫
        Lf'.map (Lg.map ((adjS M).counit.app K)) := by
    have hn := μf'.inv.naturality (X := (Lg.obj H, Lg.obj M))
      (Y := ((HS'.obj (op (Lg.obj M))).obj (Lg.obj K), Lg.obj M))
      ((pullbackHomMap TS TS' μg HS HS' adjS adjS' M K, 𝟙 _))
    simp only [Functor.comp_obj, Functor.prod_obj, Functor.uncurry_obj_obj, Functor.comp_map,
      Functor.prod_map, Functor.uncurry_obj_map, Functor.map_id, Category.comp_id] at hn
    rw [reassoc_of% hn, ← Lf'.map_comp, ← Lf'.map_comp]
    congr 2
    have h := homEquiv_symm_pullbackHomMap TS TS' μg HS HS' adjS adjS' M K
    rw [Adjunction.homEquiv_counit] at h
    simpa using h
  -- the right side
  have hR : (TT'.map (ε.hom.app H ≫ Lg'.map (pullbackHomMap TS TT μf HS HT adjS adjT M K))).app
        (Lg'.obj (Lf.obj M)) ≫ μg'.inv.app ((HT.obj (op (Lf.obj M))).obj (Lf.obj K), Lf.obj M) ≫
        Lg'.map ((adjT (Lf.obj M)).counit.app (Lf.obj K)) =
      (TT'.map (ε.hom.app H)).app (Lg'.obj (Lf.obj M)) ≫ μg'.inv.app (Lf.obj H, Lf.obj M) ≫
        Lg'.map (μf.inv.app (H, M)) ≫ Lg'.map (Lf.map ((adjS M).counit.app K)) := by
    have hn := μg'.inv.naturality (X := (Lf.obj H, Lf.obj M))
      (Y := ((HT.obj (op (Lf.obj M))).obj (Lf.obj K), Lf.obj M))
      ((pullbackHomMap TS TT μf HS HT adjS adjT M K, 𝟙 _))
    simp only [Functor.comp_obj, Functor.prod_obj, Functor.uncurry_obj_obj, Functor.comp_map,
      Functor.prod_map, Functor.uncurry_obj_map, Functor.map_id, Category.comp_id] at hn
    rw [Functor.map_comp, NatTrans.comp_app, Category.assoc, reassoc_of% hn, ← Lg'.map_comp,
      ← Lg'.map_comp]
    congr 3
    have h := homEquiv_symm_pullbackHomMap TS TT μf HS HT adjS adjT M K
    rw [Adjunction.homEquiv_counit] at h
    simpa using h
  have hinv : μf'.inv.app (Lg.obj H, Lg.obj M) ≫ Lf'.map (μg.inv.app (H, M)) =
      (Functor.uncurry.obj TT').map (ε.hom.app H ×ₘ ε.hom.app M) ≫
        μg'.inv.app (Lf.obj H, Lf.obj M) ≫ Lg'.map (μf.inv.app (H, M)) ≫
          ε.inv.app ((TS.obj H).obj M) := by
    rw [Stacks.AffineProjectionFormula.TensorComparisonCompatible] at hsq
    refine (cancel_epi (μf'.hom.app (Lg.obj H, Lg.obj M))).1 ?_
    refine (cancel_epi (Lf'.map (μg.hom.app (H, M)))).1 ?_
    rw [reassoc_of% hsq]
    simp only [Iso.hom_inv_id_app_assoc, ← Lf'.map_comp, Iso.hom_inv_id_app, Functor.map_id]
    rw [← Lg'.map_comp_assoc]
    simp [ε]
  have hε : Lg'.map (Lf.map ((adjS M).counit.app K)) ≫ ε.inv.app K =
      ε.inv.app ((TS.obj H).obj M) ≫ Lf'.map (Lg.map ((adjS M).counit.app K)) :=
    ε.inv.naturality ((adjS M).counit.app K)
  rw [hL]
  simp only [Category.assoc]
  rw [reassoc_of% hR, hε, reassoc_of% hinv]
  simp only [Functor.uncurry_obj_map, Category.assoc]
  rw [← reassoc_of% ((TT'.map (ε.hom.app H)).naturality (ε.hom.app M))]

/-- `pullbackHomMap_chart_square` with the identification `ε` of the two composites taken whole. -/
private theorem pullbackHomMap_chart_square_inv_aux (M K : S) {N' : S'} (φ : Lg.obj K ⟶ N')
    (hsq : Stacks.AffineProjectionFormula.TensorComparisonCompatible eg ef
      (Functor.uncurry.obj TS) (Functor.uncurry.obj TS') (Functor.uncurry.obj TT)
      (Functor.uncurry.obj TT') μf.hom μf'.hom μg.hom μg'.hom ((HS.obj (op M)).obj K) M)
    (hD : ∀ {Q' Q : T'} (v : Q' ⟶ Q) {A Z : T'} (θ : A ⟶ (HT'.obj (op Q)).obj Z),
      ((adjT' Q').homEquiv A Z).symm (θ ≫ (HT'.map v.op).app Z) =
        (TT'.obj A).map v ≫ ((adjT' Q).homEquiv A Z).symm θ) :
    Lg'.map (pullbackHomMap TS TT μf HS HT adjS adjT M K) ≫
        pullbackHomMap TT TT' μg' HT HT' adjT adjT' (Lf.obj M) (Lf.obj K) ≫
        (HT'.obj (op (Lg'.obj (Lf.obj M)))).map
          ((Stacks.AffineProjectionFormula.squareCompositeIso eg ef).inv.app K ≫ Lf'.map φ) =
      ((Stacks.AffineProjectionFormula.squareCompositeIso eg ef).inv.app ((HS.obj (op M)).obj K) ≫
          Lf'.map (pullbackHomMap TS TS' μg HS HS' adjS adjS' M K ≫
            (HS'.obj (op (Lg.obj M))).map φ)) ≫
        pullbackHomMap TS' TT' μf' HS' HT' adjS' adjT' (Lg.obj M) N' ≫
        (HT'.map ((Stacks.AffineProjectionFormula.squareCompositeIso eg ef).inv.app M).op).app
          (Lf'.obj N') := by
  have h := pullbackHomMap_square eg ef TS TS' TT TT' μf μf' μg μg' HS HS' HT HT'
    adjS adjS' adjT adjT' M K hsq hD
  have hn := pullbackHomMap_naturality_right TS' TT' μf' HS' HT' adjS' adjT' (Lg.obj M) φ
  generalize Stacks.AffineProjectionFormula.squareCompositeIso eg ef = ε at h ⊢
  rw [Lf'.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hn, reassoc_of% h, Iso.inv_hom_id_app_assoc]
  simp only [Functor.map_comp]
  have n1 : (HT'.obj (op (Lf'.obj (Lg.obj M)))).map (Lf'.map φ) ≫
      (HT'.map (ε.inv.app M).op).app (Lf'.obj N') =
      (HT'.map (ε.inv.app M).op).app _ ≫ (HT'.obj (op (Lg'.obj (Lf.obj M)))).map (Lf'.map φ) :=
    (HT'.map (ε.inv.app M).op).naturality (Lf'.map φ)
  have n2 : (HT'.obj (op (Lf'.obj (Lg.obj M)))).map (ε.inv.app K) ≫
      (HT'.map (ε.inv.app M).op).app _ =
      (HT'.map (ε.inv.app M).op).app _ ≫ (HT'.obj (op (Lg'.obj (Lf.obj M)))).map (ε.inv.app K) :=
    (HT'.map (ε.inv.app M).op).naturality (ε.inv.app K)
  have n3 : (HT'.map (ε.hom.app M).op).app (Lg'.obj (Lf.obj K)) ≫
      (HT'.map (ε.inv.app M).op).app (Lg'.obj (Lf.obj K)) = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← HT'.map_comp, ← op_comp]
    simp
  rw [n1, reassoc_of% n2, reassoc_of% n3]

/-- **The pullback maps of internal Homs around a square, followed by a map in the target.**
For `φ : L_g K ⟶ N'` and the inverse `ε⁻¹ = e₁ ≫ e₂ ≫ e_g⁻¹` of the identification of the two
composites, `L_{g'}` of the map along `L_f`, followed by the map along `L_{g'}` and
`ε⁻¹ ≫ L_{f'} φ` in the target, is `ε⁻¹`, `L_{f'}` of the map along `L_g` followed by `φ`, and the
map along `L_{f'}` followed by `ε⁻¹` in the source. -/
theorem pullbackHomMap_chart_square {Lc₀ : S ⥤ T'} (e₁ : Lf ⋙ Lg' ≅ Lc₀) (e₂ : Lc₀ ≅ Lc)
    (hef : ef = e₁ ≪≫ e₂) (M K : S) {N' : S'} (φ : Lg.obj K ⟶ N')
    (hsq : Stacks.AffineProjectionFormula.TensorComparisonCompatible eg ef
      (Functor.uncurry.obj TS) (Functor.uncurry.obj TS') (Functor.uncurry.obj TT)
      (Functor.uncurry.obj TT') μf.hom μf'.hom μg.hom μg'.hom ((HS.obj (op M)).obj K) M)
    (hD : ∀ {Q' Q : T'} (v : Q' ⟶ Q) {A Z : T'} (θ : A ⟶ (HT'.obj (op Q)).obj Z),
      ((adjT' Q').homEquiv A Z).symm (θ ≫ (HT'.map v.op).app Z) =
        (TT'.obj A).map v ≫ ((adjT' Q).homEquiv A Z).symm θ) :
    Lg'.map (pullbackHomMap TS TT μf HS HT adjS adjT M K) ≫
        pullbackHomMap TT TT' μg' HT HT' adjT adjT' (Lf.obj M) (Lf.obj K) ≫
        (HT'.obj (op (Lg'.obj (Lf.obj M)))).map
          (e₁.hom.app K ≫ e₂.hom.app K ≫ eg.inv.app K ≫ Lf'.map φ) =
      (e₁.hom.app ((HS.obj (op M)).obj K) ≫ e₂.hom.app ((HS.obj (op M)).obj K) ≫
          eg.inv.app ((HS.obj (op M)).obj K) ≫
          Lf'.map (pullbackHomMap TS TS' μg HS HS' adjS adjS' M K ≫
            (HS'.obj (op (Lg.obj M))).map φ)) ≫
        pullbackHomMap TS' TT' μf' HS' HT' adjS' adjT' (Lg.obj M) N' ≫
        (HT'.map (e₁.hom.app M ≫ e₂.hom.app M ≫ eg.inv.app M).op).app (Lf'.obj N') := by
  subst hef
  have hε : ∀ X : S, e₁.hom.app X ≫ e₂.hom.app X ≫ eg.inv.app X =
      (Stacks.AffineProjectionFormula.squareCompositeIso eg (e₁ ≪≫ e₂)).inv.app X := fun X => by
    simp [Stacks.AffineProjectionFormula.squareCompositeIso_inv_app]
  have hε' : ∀ (X : S) {Z : T'} (q : (Lg ⋙ Lf').obj X ⟶ Z),
      e₁.hom.app X ≫ e₂.hom.app X ≫ eg.inv.app X ≫ q =
        (Stacks.AffineProjectionFormula.squareCompositeIso eg (e₁ ≪≫ e₂)).inv.app X ≫ q :=
    fun X Z q => by rw [← hε]; simp only [Category.assoc]
  simp only [hε, hε']
  exact pullbackHomMap_chart_square_inv_aux eg (e₁ ≪≫ e₂) TS TS' TT TT' μf μf' μg μg' HS HS' HT
    HT' adjS adjS' adjT adjT' M K φ hsq hD

/-- `pullbackHomMap_chart_square` for maps `φ_f`, `φ_g`, `φ_{f'}`, `φ_{g'}` given through their
transposes: each is the map of [Stacks, Tag 08JF] as soon as its transpose is the inverse of the
tensor comparison followed by the image of the evaluation. -/
theorem chart_square_of_homEquiv_symm {Lc₀ : S ⥤ T'} (e₁ : Lf ⋙ Lg' ≅ Lc₀) (e₂ : Lc₀ ≅ Lc)
    (hef : ef = e₁ ≪≫ e₂) (M K : S) {N' : S'} (φ : Lg.obj K ⟶ N')
    (φf : Lf.obj ((HS.obj (op M)).obj K) ⟶ (HT.obj (op (Lf.obj M))).obj (Lf.obj K))
    (hφf : ((adjT (Lf.obj M)).homEquiv _ _).symm φf =
      μf.inv.app ((HS.obj (op M)).obj K, M) ≫ Lf.map ((adjS M).counit.app K))
    (φg : Lg.obj ((HS.obj (op M)).obj K) ⟶ (HS'.obj (op (Lg.obj M))).obj (Lg.obj K))
    (hφg : ((adjS' (Lg.obj M)).homEquiv _ _).symm φg =
      μg.inv.app ((HS.obj (op M)).obj K, M) ≫ Lg.map ((adjS M).counit.app K))
    (φf' : Lf'.obj ((HS'.obj (op (Lg.obj M))).obj N') ⟶
      (HT'.obj (op (Lf'.obj (Lg.obj M)))).obj (Lf'.obj N'))
    (hφf' : ((adjT' (Lf'.obj (Lg.obj M))).homEquiv _ _).symm φf' =
      μf'.inv.app ((HS'.obj (op (Lg.obj M))).obj N', Lg.obj M) ≫
        Lf'.map ((adjS' (Lg.obj M)).counit.app N'))
    (φg' : Lg'.obj ((HT.obj (op (Lf.obj M))).obj (Lf.obj K)) ⟶
      (HT'.obj (op (Lg'.obj (Lf.obj M)))).obj (Lg'.obj (Lf.obj K)))
    (hφg' : ((adjT' (Lg'.obj (Lf.obj M))).homEquiv _ _).symm φg' =
      μg'.inv.app ((HT.obj (op (Lf.obj M))).obj (Lf.obj K), Lf.obj M) ≫
        Lg'.map ((adjT (Lf.obj M)).counit.app (Lf.obj K)))
    (hsq : Stacks.AffineProjectionFormula.TensorComparisonCompatible eg ef
      (Functor.uncurry.obj TS) (Functor.uncurry.obj TS') (Functor.uncurry.obj TT)
      (Functor.uncurry.obj TT') μf.hom μf'.hom μg.hom μg'.hom ((HS.obj (op M)).obj K) M)
    (hD : ∀ {Q' Q : T'} (v : Q' ⟶ Q) {A Z : T'} (θ : A ⟶ (HT'.obj (op Q)).obj Z),
      ((adjT' Q').homEquiv A Z).symm (θ ≫ (HT'.map v.op).app Z) =
        (TT'.obj A).map v ≫ ((adjT' Q).homEquiv A Z).symm θ) :
    Lg'.map φf ≫ φg' ≫
        (HT'.obj (op (Lg'.obj (Lf.obj M)))).map
          (e₁.hom.app K ≫ e₂.hom.app K ≫ eg.inv.app K ≫ Lf'.map φ) =
      (e₁.hom.app ((HS.obj (op M)).obj K) ≫ e₂.hom.app ((HS.obj (op M)).obj K) ≫
          eg.inv.app ((HS.obj (op M)).obj K) ≫
          Lf'.map (φg ≫ (HS'.obj (op (Lg.obj M))).map φ)) ≫
        φf' ≫ (HT'.map (e₁.hom.app M ≫ e₂.hom.app M ≫ eg.inv.app M).op).app (Lf'.obj N') := by
  obtain rfl := eq_pullbackHomMap_of_homEquiv_symm hφf
  obtain rfl := eq_pullbackHomMap_of_homEquiv_symm hφg
  obtain rfl := eq_pullbackHomMap_of_homEquiv_symm hφf'
  obtain rfl := eq_pullbackHomMap_of_homEquiv_symm hφg'
  exact pullbackHomMap_chart_square eg ef TS TS' TT TT' μf μf' μg μg' HS HS' HT HT' adjS adjS'
    adjT adjT' e₁ e₂ hef M K φ hsq hD

/-- **Transport of a property of maps `L_{g'} K₁ ⟶ K₁'` around a square, along the maps of
[Stacks, Tag 08JF].** Let `P` be a property of maps `L_{g'} K₁ ⟶ K₁'` invariant under
isomorphisms of the pair `(K₁, K₁')`. If the maps `φ_f` (along `L_f`) and `φ_{f'}` (along
`L_{f'}`) are invertible, then `P` holds for `L_{f'}` of the map along `L_g` followed by `φ`,
read through `ε⁻¹`, exactly when it holds for the map along `L_{g'}` followed by
`ε⁻¹ ≫ L_{f'}φ`. -/
theorem chart_iff_of_homEquiv_symm {Lc₀ : S ⥤ T'} (e₁ : Lf ⋙ Lg' ≅ Lc₀) (e₂ : Lc₀ ≅ Lc)
    (hef : ef = e₁ ≪≫ e₂)
    (P : ∀ (K₁ : T) (K₁' : T'), (Lg'.obj K₁ ⟶ K₁') → Prop)
    (hP : ∀ {K₁ K₂ : T} {K₁' K₂' : T'} (e : K₁ ⟶ K₂) [IsIso e] (e' : K₁' ⟶ K₂') [IsIso e']
      (φ₁ : Lg'.obj K₁ ⟶ K₁') (φ₂ : Lg'.obj K₂ ⟶ K₂'), φ₁ ≫ e' = Lg'.map e ≫ φ₂ →
        (P K₁ K₁' φ₁ ↔ P K₂ K₂' φ₂))
    (M K : S) {N' : S'} (φ : Lg.obj K ⟶ N')
    (φf : Lf.obj ((HS.obj (op M)).obj K) ⟶ (HT.obj (op (Lf.obj M))).obj (Lf.obj K)) [IsIso φf]
    (hφf : ((adjT (Lf.obj M)).homEquiv _ _).symm φf =
      μf.inv.app ((HS.obj (op M)).obj K, M) ≫ Lf.map ((adjS M).counit.app K))
    (φg : Lg.obj ((HS.obj (op M)).obj K) ⟶ (HS'.obj (op (Lg.obj M))).obj (Lg.obj K))
    (hφg : ((adjS' (Lg.obj M)).homEquiv _ _).symm φg =
      μg.inv.app ((HS.obj (op M)).obj K, M) ≫ Lg.map ((adjS M).counit.app K))
    (φf' : Lf'.obj ((HS'.obj (op (Lg.obj M))).obj N') ⟶
      (HT'.obj (op (Lf'.obj (Lg.obj M)))).obj (Lf'.obj N')) [IsIso φf']
    (hφf' : ((adjT' (Lf'.obj (Lg.obj M))).homEquiv _ _).symm φf' =
      μf'.inv.app ((HS'.obj (op (Lg.obj M))).obj N', Lg.obj M) ≫
        Lf'.map ((adjS' (Lg.obj M)).counit.app N'))
    (φg' : Lg'.obj ((HT.obj (op (Lf.obj M))).obj (Lf.obj K)) ⟶
      (HT'.obj (op (Lg'.obj (Lf.obj M)))).obj (Lg'.obj (Lf.obj K)))
    (hφg' : ((adjT' (Lg'.obj (Lf.obj M))).homEquiv _ _).symm φg' =
      μg'.inv.app ((HT.obj (op (Lf.obj M))).obj (Lf.obj K), Lf.obj M) ≫
        Lg'.map ((adjT (Lf.obj M)).counit.app (Lf.obj K)))
    (hsq : Stacks.AffineProjectionFormula.TensorComparisonCompatible eg ef
      (Functor.uncurry.obj TS) (Functor.uncurry.obj TS') (Functor.uncurry.obj TT)
      (Functor.uncurry.obj TT') μf.hom μf'.hom μg.hom μg'.hom ((HS.obj (op M)).obj K) M)
    (hD : ∀ {Q' Q : T'} (v : Q' ⟶ Q) {A Z : T'} (θ : A ⟶ (HT'.obj (op Q)).obj Z),
      ((adjT' Q').homEquiv A Z).symm (θ ≫ (HT'.map v.op).app Z) =
        (TT'.obj A).map v ≫ ((adjT' Q).homEquiv A Z).symm θ) :
    P (Lf.obj ((HS.obj (op M)).obj K)) (Lf'.obj ((HS'.obj (op (Lg.obj M))).obj N'))
        (e₁.hom.app ((HS.obj (op M)).obj K) ≫ e₂.hom.app ((HS.obj (op M)).obj K) ≫
          eg.inv.app ((HS.obj (op M)).obj K) ≫
          Lf'.map (φg ≫ (HS'.obj (op (Lg.obj M))).map φ)) ↔
      P ((HT.obj (op (Lf.obj M))).obj (Lf.obj K))
        ((HT'.obj (op (Lg'.obj (Lf.obj M)))).obj (Lf'.obj N'))
        (φg' ≫ (HT'.obj (op (Lg'.obj (Lf.obj M)))).map
          (e₁.hom.app K ≫ e₂.hom.app K ≫ eg.inv.app K ≫ Lf'.map φ)) := by
  have hiso : IsIso (e₁.hom.app M ≫ e₂.hom.app M ≫ eg.inv.app M) := inferInstance
  have : IsIso ((HT'.map (e₁.hom.app M ≫ e₂.hom.app M ≫ eg.inv.app M).op).app (Lf'.obj N')) :=
    inferInstance
  refine hP φf (φf' ≫ (HT'.map (e₁.hom.app M ≫ e₂.hom.app M ≫ eg.inv.app M).op).app
    (Lf'.obj N')) _ _ ?_
  exact (chart_square_of_homEquiv_symm eg ef TS TS' TT TT' μf μf' μg μg' HS HS' HT HT' adjS adjS'
    adjT adjT' e₁ e₂ hef M K φ φf hφf φg hφg φf' hφf' φg' hφg' hsq hD).symm

/-- `pullbackHomMap_chart_square` with the identification `ε` of the two composites taken whole. -/
theorem pullbackHomMap_chart_square_inv (M K : S) {N' : S'} (φ : Lg.obj K ⟶ N')
    (hsq : Stacks.AffineProjectionFormula.TensorComparisonCompatible eg ef
      (Functor.uncurry.obj TS) (Functor.uncurry.obj TS') (Functor.uncurry.obj TT)
      (Functor.uncurry.obj TT') μf.hom μf'.hom μg.hom μg'.hom ((HS.obj (op M)).obj K) M)
    (hD : ∀ {Q' Q : T'} (v : Q' ⟶ Q) {A Z : T'} (θ : A ⟶ (HT'.obj (op Q)).obj Z),
      ((adjT' Q').homEquiv A Z).symm (θ ≫ (HT'.map v.op).app Z) =
        (TT'.obj A).map v ≫ ((adjT' Q).homEquiv A Z).symm θ) :
    Lg'.map (pullbackHomMap TS TT μf HS HT adjS adjT M K) ≫
        pullbackHomMap TT TT' μg' HT HT' adjT adjT' (Lf.obj M) (Lf.obj K) ≫
        (HT'.obj (op (Lg'.obj (Lf.obj M)))).map
          ((Stacks.AffineProjectionFormula.squareCompositeIso eg ef).inv.app K ≫ Lf'.map φ) =
      ((Stacks.AffineProjectionFormula.squareCompositeIso eg ef).inv.app ((HS.obj (op M)).obj K) ≫
          Lf'.map (pullbackHomMap TS TS' μg HS HS' adjS adjS' M K ≫
            (HS'.obj (op (Lg.obj M))).map φ)) ≫
        pullbackHomMap TS' TT' μf' HS' HT' adjS' adjT' (Lg.obj M) N' ≫
        (HT'.map ((Stacks.AffineProjectionFormula.squareCompositeIso eg ef).inv.app M).op).app
          (Lf'.obj N') := by
  exact pullbackHomMap_chart_square_inv_aux eg ef TS TS' TT TT' μf μf' μg μg' HS HS' HT HT'
    adjS adjS' adjT adjT' M K φ hsq hD

/-- `chart_iff_of_homEquiv_symm` with the inverse of the identification of the two composites
given as a composite `ι₁ ≫ ι₂ ≫ ι₃` of three families of maps through arbitrary objects. -/
theorem chart_iff_of_homEquiv_symm_of_comp (A₁ A₂ : S → T')
    (ι₁ : ∀ X, Lg'.obj (Lf.obj X) ⟶ A₁ X) (ι₂ : ∀ X, A₁ X ⟶ A₂ X)
    (ι₃ : ∀ X, A₂ X ⟶ Lf'.obj (Lg.obj X))
    (hι : ∀ X, ι₁ X ≫ ι₂ X ≫ ι₃ X =
      (Stacks.AffineProjectionFormula.squareCompositeIso eg ef).inv.app X)
    (P : ∀ (K₁ : T) (K₁' : T'), (Lg'.obj K₁ ⟶ K₁') → Prop)
    (hP : ∀ {K₁ K₂ : T} {K₁' K₂' : T'} (e : K₁ ⟶ K₂) [IsIso e] (e' : K₁' ⟶ K₂') [IsIso e']
      (φ₁ : Lg'.obj K₁ ⟶ K₁') (φ₂ : Lg'.obj K₂ ⟶ K₂'), φ₁ ≫ e' = Lg'.map e ≫ φ₂ →
        (P K₁ K₁' φ₁ ↔ P K₂ K₂' φ₂))
    (M K : S) {N' : S'} (φ : Lg.obj K ⟶ N')
    (φf : Lf.obj ((HS.obj (op M)).obj K) ⟶ (HT.obj (op (Lf.obj M))).obj (Lf.obj K)) [IsIso φf]
    (hφf : ((adjT (Lf.obj M)).homEquiv _ _).symm φf =
      μf.inv.app ((HS.obj (op M)).obj K, M) ≫ Lf.map ((adjS M).counit.app K))
    (φg : Lg.obj ((HS.obj (op M)).obj K) ⟶ (HS'.obj (op (Lg.obj M))).obj (Lg.obj K))
    (hφg : ((adjS' (Lg.obj M)).homEquiv _ _).symm φg =
      μg.inv.app ((HS.obj (op M)).obj K, M) ≫ Lg.map ((adjS M).counit.app K))
    (φf' : Lf'.obj ((HS'.obj (op (Lg.obj M))).obj N') ⟶
      (HT'.obj (op (Lf'.obj (Lg.obj M)))).obj (Lf'.obj N')) [IsIso φf']
    (hφf' : ((adjT' (Lf'.obj (Lg.obj M))).homEquiv _ _).symm φf' =
      μf'.inv.app ((HS'.obj (op (Lg.obj M))).obj N', Lg.obj M) ≫
        Lf'.map ((adjS' (Lg.obj M)).counit.app N'))
    (φg' : Lg'.obj ((HT.obj (op (Lf.obj M))).obj (Lf.obj K)) ⟶
      (HT'.obj (op (Lg'.obj (Lf.obj M)))).obj (Lg'.obj (Lf.obj K)))
    (hφg' : ((adjT' (Lg'.obj (Lf.obj M))).homEquiv _ _).symm φg' =
      μg'.inv.app ((HT.obj (op (Lf.obj M))).obj (Lf.obj K), Lf.obj M) ≫
        Lg'.map ((adjT (Lf.obj M)).counit.app (Lf.obj K)))
    (hsq : Stacks.AffineProjectionFormula.TensorComparisonCompatible eg ef
      (Functor.uncurry.obj TS) (Functor.uncurry.obj TS') (Functor.uncurry.obj TT)
      (Functor.uncurry.obj TT') μf.hom μf'.hom μg.hom μg'.hom ((HS.obj (op M)).obj K) M)
    (hD : ∀ {Q' Q : T'} (v : Q' ⟶ Q) {A Z : T'} (θ : A ⟶ (HT'.obj (op Q)).obj Z),
      ((adjT' Q').homEquiv A Z).symm (θ ≫ (HT'.map v.op).app Z) =
        (TT'.obj A).map v ≫ ((adjT' Q).homEquiv A Z).symm θ) :
    P (Lf.obj ((HS.obj (op M)).obj K)) (Lf'.obj ((HS'.obj (op (Lg.obj M))).obj N'))
        (ι₁ ((HS.obj (op M)).obj K) ≫ ι₂ ((HS.obj (op M)).obj K) ≫ ι₃ ((HS.obj (op M)).obj K) ≫
          Lf'.map (φg ≫ (HS'.obj (op (Lg.obj M))).map φ)) ↔
      P ((HT.obj (op (Lf.obj M))).obj (Lf.obj K))
        ((HT'.obj (op (Lg'.obj (Lf.obj M)))).obj (Lf'.obj N'))
        (φg' ≫ (HT'.obj (op (Lg'.obj (Lf.obj M)))).map (ι₁ K ≫ ι₂ K ≫ ι₃ K ≫ Lf'.map φ)) := by
  have e' : ∀ X {Z : T'} (q : Lf'.obj (Lg.obj X) ⟶ Z), ι₁ X ≫ ι₂ X ≫ ι₃ X ≫ q =
      (Stacks.AffineProjectionFormula.squareCompositeIso eg ef).inv.app X ≫ q := fun X Z q => by
    rw [← hι]; simp only [Category.assoc]
  simp only [e']
  have : IsIso ((HT'.map ((Stacks.AffineProjectionFormula.squareCompositeIso eg ef).inv.app
    M).op).app (Lf'.obj N')) := inferInstance
  refine hP φf (φf' ≫ (HT'.map ((Stacks.AffineProjectionFormula.squareCompositeIso eg ef).inv.app
    M).op).app (Lf'.obj N')) _ _ ?_
  obtain rfl := eq_pullbackHomMap_of_homEquiv_symm hφf
  obtain rfl := eq_pullbackHomMap_of_homEquiv_symm hφg
  obtain rfl := eq_pullbackHomMap_of_homEquiv_symm hφf'
  obtain rfl := eq_pullbackHomMap_of_homEquiv_symm hφg'
  exact (pullbackHomMap_chart_square_inv eg ef TS TS' TT TT' μf μf' μg μg' HS HS' HT HT' adjS
    adjS' adjT adjT' M K φ hsq hD).symm

end CategoryTheory.PullbackInternalHom

end
