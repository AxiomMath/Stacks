module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.MotiveNameIdentity
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationEquidimensionalBlock
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationNameAction
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# A realization and the action of Stacks 0FHL agree between equidimensional schemes

Let `G : M_k ⥤ graded F-vector spaces` be a realization (side (2) of Stacks 0FHM) and
`H^*(X) = G(h(X))` its data (Stacks 0FHK). For `X`, `Y` nonempty and equidimensional and a
correspondence `c ∈ Corr⁰(X, Y)`, `G(c)` is the action `a ↦ pr₂,*(γ(c) ∪ pr₁^*a)` of
Stacks 0FHL: the name of `c` under the duality of Stacks 0FGI is its cycle class, and a
realization acts on a morphism of motives whose name is a class `z` by the action of `z`
(`Stacks.WeilCohomology.WeilRealization.map_eq_blockAct`).

## References

* [Stacks Project, Tag 0FHM](https://stacks.math.columbia.edu/tag/0FHM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
  CategoryTheory.GradedCategory Stacks.Chow

universe u w

namespace Stacks.WeilCohomology.WeilData

open SmoothProjectiveScheme

variable {k : Type u} [Field k] {F : Type w} [Field F] {W : WeilData k F}

/-- A correspondence `c ∈ Corr⁰(X, Y)` as a morphism `X ⟶ Y` of correspondences of degree zero. -/
def corrDz (X Y : (SmoothProjectiveScheme k).FullSubcategory) :
    Corr k X.obj.hom Y.obj.hom 0 →+ (dz X ⟶ dz Y) where
  toFun c := DegreeZero.homMk (ChowMotiveCat.homOf 0 ((SmoothProjectiveCorr.toCorr X Y 0).symm c))
    (ChowMotiveCat.homOf_mem_grade _)
  map_zero' := DegreeZero.hom_ext (by rw [DegreeZero.homMk_val, LinearEquiv.map_zero,
    LinearMap.map_zero, DegreeZero.zero_val])
  map_add' c c' := DegreeZero.hom_ext (by rw [DegreeZero.homMk_val, LinearEquiv.map_add,
    LinearMap.map_add, DegreeZero.add_val, DegreeZero.homMk_val, DegreeZero.homMk_val])

/-- The underlying morphism of motives of `corrDz X Y c` is `c`, read in degree zero. -/
theorem corrDz_val {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (c : Corr k X.obj.hom Y.obj.hom 0) :
    DegreeZero.val (corrDz X Y c) =
      ChowMotiveCat.homOf 0 ((SmoothProjectiveCorr.toCorr X Y 0).symm c) :=
  DegreeZero.homMk_val _ _

/-- Every morphism of correspondences of degree zero is `corrDz` of its correspondence. -/
theorem eq_corrDz {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : dz X ⟶ dz Y) :
    f = corrDz X Y (SmoothProjectiveCorr.toCorr X Y 0
      (ChowMotiveCat.component 0 (DegreeZero.val f))) :=
  DegreeZero.hom_ext (by rw [corrDz_val, LinearEquiv.symm_apply_apply]; exact val_eq_homOf f)

/-- **Two actions of correspondences agree between equidimensional schemes as soon as they agree
on the integral classes**: for `X`, `Y` equidimensional of dimensions `d`, `e`,
`Corr⁰(X, Y) = CH_e(X × Y) ⊗ ℚ`, and the rational classes are recovered from the integral ones by
dividing by integers. -/
theorem CorrAction.ext_of_integral [CharZero F] (T T' : W.CorrAction)
    {X Y : (SmoothProjectiveScheme k).FullSubcategory} {d e : ℕ}
    (hX : RelativeDimension X.obj.hom d) (hY : RelativeDimension Y.obj.hom e) (n : ℤ)
    (h : ∀ α : chowGroup (fieldChowSituation k) (prodBase X.obj.hom Y.obj.hom) ((e : ℤ) - 0),
      T.act (corrDz X Y ((corrEquivCorrespondence k X.obj.hom Y.obj.hom hX hY 0).symm
        ((1 : ℚ) ⊗ₜ[ℤ] α))) n =
      T'.act (corrDz X Y ((corrEquivCorrespondence k X.obj.hom Y.obj.hom hX hY 0).symm
        ((1 : ℚ) ⊗ₜ[ℤ] α))) n)
    (f : dz X ⟶ dz Y) : T.act f n = T'.act f n := by
  let A : W.CorrAction → (dz X ⟶ dz Y) →+ (W.grade X n →ₗ[F] W.grade Y n) := fun S ↦
    { toFun := fun f ↦ S.act f n
      map_zero' := S.act_zero X Y n
      map_add' := fun f g ↦ S.act_add f g n }
  let Φ : W.CorrAction →
      Correspondence (fieldChowSituation k) X.obj.hom Y.obj.hom e 0 →+
        (W.grade X n →ₗ[F] W.grade Y n) := fun S ↦
    ((A S).comp (corrDz X Y)).comp
      (corrEquivCorrespondence k X.obj.hom Y.obj.hom hX hY 0).symm.toLinearMap.toAddMonoidHom
  have key : Φ T = Φ T' := by
    refine AddMonoidHom.ext fun t ↦ ?_
    induction t using TensorProduct.inductionOn with
    | add t t' ht ht' => rw [map_add, map_add, ht, ht']
    | tmul q α =>
      have hm : (q.den : ℤ) • (q ⊗ₜ[ℤ] α) = q.num • ((1 : ℚ) ⊗ₜ[ℤ] α) := by
        rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', zsmul_eq_mul, zsmul_eq_mul,
          mul_one, mul_comm, Int.cast_natCast, Rat.mul_den_eq_num]
      have h1 : (q.den : ℤ) • Φ T (q ⊗ₜ[ℤ] α) = (q.den : ℤ) • Φ T' (q ⊗ₜ[ℤ] α) := by
        rw [← map_zsmul, ← map_zsmul, hm, map_zsmul, map_zsmul]
        exact congrArg _ (h α)
      rw [← Int.cast_smul_eq_zsmul F, ← Int.cast_smul_eq_zsmul F] at h1
      exact smul_right_injective _ (Int.cast_ne_zero.2 (Int.natCast_ne_zero.2 q.den_nz)) h1
  rw [eq_corrDz f]
  obtain ⟨t, ht⟩ := (corrEquivCorrespondence k X.obj.hom Y.obj.hom hX hY 0).symm.surjective
    (SmoothProjectiveCorr.toCorr X Y 0 (ChowMotiveCat.component 0 (DegreeZero.val f)))
  rw [← ht]
  exact congrArg (fun φ ↦ φ t) key

section Axioms

variable [CharZero F] (hA : W.PoincareDuality) (hB : W.Kunneth)
  (hC : W.CycleClassAxiom hA.perfectPairing)

/-- The action of `corrDz X Y c` is the action `corrMap` of the correspondence `c`. -/
theorem corrHomMap_corrDz {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (c : Corr k X.obj.hom Y.obj.hom 0) (n : ℤ) :
    corrHomMap hA hB hC (corrDz X Y c) n = corrMap hA hB hC X Y 0 n c := by
  rw [corrHomMap, corrDz_val, ChowMotiveCat.component_homOf, LinearEquiv.apply_symm_apply]

/-- **The action of an integral correspondence between equidimensional schemes**: for the class
`1 ⊗ α ∈ CH_e(X × Y) ⊗ ℚ = Corr⁰(X, Y)`, the action `a ↦ pr₂,*(γ(c) ∪ pr₁^*a)` of Stacks 0FHL is
the action of `γ(α)`, `α` read in codimension `d`. -/
theorem corrMap_corrEquivCorrespondence_symm_tmul {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    {d e : ℕ} (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e) (n : ℤ)
    (α : chowGroup (fieldChowSituation k) (prodBase X.obj.hom Y.obj.hom) ((e : ℤ) - 0))
    (a : W.grade X n) :
    (corrMap hA hB hC X Y 0 n ((corrEquivCorrespondence k X.obj.hom Y.obj.hom
        hX.relativeDimension hY.relativeDimension 0).symm ((1 : ℚ) ⊗ₜ[ℤ] α)) a : W.H Y) =
      (W.blockAct hA.perfectPairing hX hY (W.cycleClassRing (prod X Y) d
        (chowGroupToCodimension (X ⊗ Y).obj.hom ((e : ℤ) - 0) d α)) n a : W.H Y) := by
  have := isIso_dimPart_self_ι X.obj.hom hX.relativeDimension
  have := isIso_dimPart_self_ι Y.obj.hom hY.relativeDimension
  have h2 := (chowGroupEquivOfIso (fieldChowSituation k)
    (prodBase (partBase X.obj.hom d) (partBase Y.obj.hom e)) (prodBase X.obj.hom Y.obj.hom)
    (prodHom X.obj.hom Y.obj.hom (partBase X.obj.hom d) (partBase Y.obj.hom e)
      (dimPart X.obj.hom d).ι (dimPart Y.obj.hom e).ι rfl rfl)
    (prodHom_comp_prodBase _ _ _ _ _ _ _ _) ((e : ℤ) - 0)).apply_symm_apply α
  rw [chowGroupEquivOfIso_apply] at h2
  have h1 : (correspondenceEquivOfIso (fieldChowSituation k) X.obj.hom Y.obj.hom
      (partBase X.obj.hom d) (partBase Y.obj.hom e) (dimPart X.obj.hom d).ι
      (dimPart Y.obj.hom e).ι rfl rfl e 0).symm ((1 : ℚ) ⊗ₜ[ℤ] α) =
      (1 : ℚ) ⊗ₜ[ℤ] (chowGroupEquivOfIso (fieldChowSituation k)
        (prodBase (partBase X.obj.hom d) (partBase Y.obj.hom e)) (prodBase X.obj.hom Y.obj.hom)
        (prodHom X.obj.hom Y.obj.hom (partBase X.obj.hom d) (partBase Y.obj.hom e)
          (dimPart X.obj.hom d).ι (dimPart Y.obj.hom e).ι rfl rfl)
        (prodHom_comp_prodBase _ _ _ _ _ _ _ _) ((e : ℤ) - 0)).symm α := by
    rw [LinearEquiv.symm_apply_eq, correspondenceEquivOfIso_tmul, h2]
  rw [corrEquivCorrespondence_symm_apply, h1, corrMap_lof_lof_tmul hA hB hC hX hY, h2,
    Rat.cast_one, one_smul]

end Axioms

end Stacks.WeilCohomology.WeilData

namespace Stacks.WeilCohomology.WeilRealization

open SmoothProjectiveScheme

variable {k : Type u} [Field k] {F : Type w} [Field F] [CharZero F] (G : WeilRealization k F)

section

attribute [-instance] ChowMotiveCat.monoidalCategory ChowMotiveCat.braidedCategory
  ChowMotiveCat.symmetricCategory TwistedKaroubi.monoidalCategoryStruct
  CorrespondenceCategory.monoidalCategoryStruct TwistedKaroubi.symmetricCategory

attribute [local instance] braidedTK monoidalTK

local notation "𝐎" => (GradedCompositionData.Obj.mk :
  CategoryTheory.ObjectProperty.FullSubcategory (SmoothProjectiveScheme _) →
    CorrespondenceCategory _)

/-- `G` of the inverse of an isomorphism undoes `G` of the isomorphism, elementwise. -/
private theorem map_inv_map_hom_apply
    {A B : TwistedKaroubi ℚ (canonicalCorrespondenceCompositionData k).Obj} (e : A ≅ B) (n : ℤ)
    (x : G.functorTK.obj A n) :
    (G.functorTK.map e.inv n).hom ((G.functorTK.map e.hom n).hom x) = x :=
  congrArg (fun φ ↦ (φ n).hom x) (G.functorTK.mapIso e).hom_inv_id

/-- **`G(𝟙 ≅ 𝟏(-d) ⊗ 𝟏(d))(1) = e_{-d} · e_d`.** -/
theorem map_unitTwistTensorIsoOfEq_inv_gradedOne (d : ℤ) :
    G.functorTK.map (TwistedKaroubi.unitTwistTensorIsoOfEq (R := ℚ)
        (C := (canonicalCorrespondenceCompositionData k).Obj) (-d) d 0 (neg_add_cancel d)).inv 0
        (Functor.gradedOne G.functorTK) =
      Functor.gradedMul G.functorTK (ChowMotiveCat.tate k (-d))
        (TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d) (2 * d)
        (-2 * d) 0 (by ring) (ChowMotiveCat.tateGenNeg G.functorTK G.tateGen d) (G.tateGen d) := by
  have h := TwistedKaroubi.eq_map_tateTensorHomOfEq_of_heq (G := G.functorTK) G.tate_degree
    G.tateBasis_ne_zero (-d) d 0 (neg_add_cancel d)
    (M := TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj (-d))
    (N := TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d)
    (P := TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj 0)
    rfl rfl rfl (show -2 * -d = 2 * d by ring) rfl (by ring) (by ring)
    (ChowMotiveCat.tateGenNeg G.functorTK G.tateGen d) (G.tateGen d)
    (Functor.gradedOne G.functorTK) (G.tateGenNeg_heq d) HEq.rfl G.tateGen_zero_heq.symm
  rw [TwistedKaroubi.tateTensorHomOfEq_rfl, TwistedKaroubi.tateTensorHom] at h
  refine (congrArg (G.functorTK.map (TwistedKaroubi.unitTwistTensorIsoOfEq (R := ℚ)
    (C := (canonicalCorrespondenceCompositionData k).Obj) (-d) d 0 (neg_add_cancel d)).inv 0)
      h).trans ?_
  exact G.map_inv_map_hom_apply _ _ _

/-- The Künneth morphism `h(X) ⊗ h(Y) ⟶ h(X × Y)` of motives is an isomorphism. -/
instance (X Y : (SmoothProjectiveScheme k).FullSubcategory) : IsIso (kunnethMot X Y) :=
  ChowMotiveCat.isIso_motMap_fst_snd_mul X Y

/-- The cycle class of `α` in the motive realization, placed in degree `2i` of the cohomology ring,
is the cycle class `γ(α)` of the Weil data of `G`. -/
theorem of_cycleClassMotive (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℤ)
    (α : codimensionChowGroup k X.obj.hom i) :
    DirectSum.of (G.cohAlg X).piece (2 * i)
        (ChowMotiveCat.cycleClassMotive G.functorTK G.tateGen X i α) =
      G.toWeilData.cycleClassRing X i α := by
  rw [WeilData.cycleClassRing, AddMonoidHom.coe_comp, Function.comp_apply,
    toWeilData_cycleClassCoord, cycleClassCoord]
  exact (ExternallyGradedAlgebra.gradeEquiv_symm_apply_coe _ _ _).symm

/-- **The realization of a correspondence from its name**: if the name
`η ≫ h(X) ◁ (c ▷ 𝟏(d))` of `c ▷ 𝟏(d)` factors as
`𝟙 ⟶ 𝟏(-d) ⊗ 𝟏(d) ⟶ h(X × Y)(d) ≅ h(X) ⊗ h(Y)(d)` through `P : 𝟏(-d) ⟶ h(X × Y)`, with the
first map sending `1` to `e_{-d} · e_d`, then `G(c)` is the action `a ↦ pr₂,*(z ∪ pr₁^*a)` of
`z = G(P)(e_{-d}) ∈ H^{2d}(X × Y)`. -/
theorem corrMapG_eq_blockAct_of_name (hP : G.toWeilData.PerfectPairing)
    (hK : G.toWeilData.KunnethTrace) {X Y : (SmoothProjectiveScheme k).FullSubcategory} {d e : ℕ}
    (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e)
    (f : WeilData.dz X ⟶ WeilData.dz Y)
    (u : 𝟙_ (TwistedKaroubi ℚ (canonicalCorrespondenceCompositionData k).Obj) ⟶
      TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj (-(d : ℤ)) ⊗
        TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d)
    (hu : G.functorTK.map u 0 (Functor.gradedOne G.functorTK) =
      Functor.gradedMul G.functorTK _ _ (2 * d) (-2 * d) 0 (by ring)
        (ChowMotiveCat.tateGenNeg G.functorTK G.tateGen d) (G.tateGen d))
    (P : TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj (-(d : ℤ)) ⟶
      TwistedKaroubi.ofObj (R := ℚ) (𝐎 (X ⊗ Y)))
    (K : TwistedKaroubi.ofObj (R := ℚ) (𝐎 X) ⊗ TwistedKaroubi.ofObj (R := ℚ) (𝐎 Y) ≅
      TwistedKaroubi.ofObj (R := ℚ) (𝐎 (X ⊗ Y))) (hK' : K.hom = kunnethMot X Y)
    (hname : letI := ChowMotiveCat.exactPairingMotive hX.relativeDimension
      η_ (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X))
          (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X) ⊗
            TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d) ≫
        TwistedKaroubi.ofObj (R := ℚ) (𝐎 X) ◁ (corrHom f ▷
          TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d) =
      u ≫ (P ▷ TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d) ≫
        (K.inv ▷ TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d) ≫
        (α_ (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X)) (TwistedKaroubi.ofObj (R := ℚ) (𝐎 Y))
          (TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d)).hom)
    (n : ℤ) (a : G.toWeilData.grade X n) :
    G.corrMapG f n a =
      G.toWeilData.blockAct hP hX hY (DirectSum.of (G.cohAlg (prod X Y)).piece (2 * d)
        (G.functorTK.map P (2 * d) (ChowMotiveCat.tateGenNeg G.functorTK G.tateGen d))) n a := by
  have e1 := Functor.map_whiskerRight_gradedMul (G := G.functorTK) P
    (TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d) (2 * d)
    (-2 * d) 0 (by ring) (ChowMotiveCat.tateGenNeg G.functorTK G.tateGen d) (G.tateGen d)
  have e2 := Functor.map_whiskerRight_gradedMul (G := G.functorTK) K.inv
    (TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d) (2 * d)
    (-2 * d) 0 (by ring)
    (G.functorTK.map P (2 * d) (ChowMotiveCat.tateGenNeg G.functorTK G.tateGen d)) (G.tateGen d)
  have hR : G.functorTK.map (u ≫ (P ▷
        TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d) ≫
      (K.inv ▷ TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d) ≫
      (α_ (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X)) (TwistedKaroubi.ofObj (R := ℚ) (𝐎 Y))
        (TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d)).hom) 0
        (Functor.gradedOne G.functorTK) =
      G.functorTK.map (α_ (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X))
        (TwistedKaroubi.ofObj (R := ℚ) (𝐎 Y))
        (TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d)).hom 0
        (Functor.gradedMul G.functorTK _
          (TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d)
          (2 * d) (-2 * d) 0 (by ring) (G.functorTK.map K.inv (2 * d)
            (G.functorTK.map P (2 * d) (ChowMotiveCat.tateGenNeg G.functorTK G.tateGen d)))
          (G.tateGen d)) := by
    simp only [Functor.map_comp, GradedObject.categoryOfGradedObjects_comp,
      ConcreteCategory.comp_apply]
    rw [hu]
    exact congrArg (G.functorTK.map (α_ (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X))
      (TwistedKaroubi.ofObj (R := ℚ) (𝐎 Y))
      (TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d)).hom 0)
      ((congrArg (G.functorTK.map (K.inv ▷
        TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d) 0) e1).trans
        e2)
  have hv := (congrArg (fun φ ↦ G.functorTK.map φ 0 (Functor.gradedOne G.functorTK)) hname).trans
    hR
  have hκ : G.functorTK.map (kunnethMot X Y) (2 * d) (G.functorTK.map K.inv (2 * d)
      (G.functorTK.map P (2 * d) (ChowMotiveCat.tateGenNeg G.functorTK G.tateGen d))) =
      G.functorTK.map P (2 * d) (ChowMotiveCat.tateGenNeg G.functorTK G.tateGen d) := by
    rw [← hK']
    exact G.map_inv_map_hom_apply K.symm _ _
  have h := map_eq_blockAct G hP hK hX hY (corrHom f) rfl _ hv n a
  rw [hκ] at h
  change ((G.cohAlg Y).gradeEquiv n).symm ((G.functorTK.map (corrHom f) n).hom
    ((G.cohAlg X).gradeEquiv n a)) = _
  rw [h]
  exact LinearEquiv.symm_apply_apply _ _

/-- The Tate triple of weight `d` is the Tate motive `𝟏(d)`. -/
theorem tateTriple_eq_tate (d : ℤ) :
    TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d =
      ChowMotiveCat.tate k d :=
  rfl

/-- Morphisms `f : A ⟶ B` and `g : A' ⟶ B` with `A = A'` and heterogeneously equal underlying
morphisms satisfy `f = eqToHom h ≫ g`. -/
theorem eq_eqToHom_comp_of_val_heq
    {A A' B : TwistedKaroubi ℚ (canonicalCorrespondenceCompositionData k).Obj}
    (h : A = A') (f : A ⟶ B) (g : A' ⟶ B) (hv : f.val ≍ g.val) : f = eqToHom h ≫ g := by
  subst h
  rw [eqToHom_refl, Category.id_comp]
  exact TwistedKaroubi.hom_ext (eq_of_heq hv)

/-- `namePointHom` is `ChowMotiveCat.pointMotiveHom`, read at the spelling `T(-d)` of `𝟏(-d)`. -/
theorem namePointHom_eq_pointMotiveHom {X Y : (SmoothProjectiveScheme k).FullSubcategory} {d e : ℕ}
    (α : chowGroup (fieldChowSituation k) (prodBase X.obj.hom Y.obj.hom) ((e : ℤ) - 0)) :
    namePointHom X Y d α = eqToHom (tateTriple_eq_tate (-(d : ℤ))) ≫
      ChowMotiveCat.pointMotiveHom (X ⊗ Y) d
        (chowGroupToCodimension (X ⊗ Y).obj.hom ((e : ℤ) - 0) d α) :=
  eq_eqToHom_comp_of_val_heq _ _ _
    (by rw [namePointHom_val, ChowMotiveCat.pointMotiveHom_val]; exact HEq.rfl)

/-- For `h : A = A'`, `G(eqToHom h ≫ g)` sends `x` to `G(g)(x')` whenever `x` and `x'` are
heterogeneously equal. -/
theorem map_eqToHom_comp_apply_of_heq
    {A A' B : TwistedKaroubi ℚ (canonicalCorrespondenceCompositionData k).Obj}
    (h : A = A') (g : A' ⟶ B) (n : ℤ) (x : G.functorTK.obj A n) (x' : G.functorTK.obj A' n)
    (hx : x ≍ x') : (G.functorTK.map (eqToHom h ≫ g) n).hom x = (G.functorTK.map g n).hom x' := by
  subst h
  cases hx
  simp

/-- **`G(a_α)(e_{-d})` is the cycle class of `α`.** -/
theorem map_namePointHom_tateGenNeg {X Y : (SmoothProjectiveScheme k).FullSubcategory} {d e : ℕ}
    (α : chowGroup (fieldChowSituation k) (prodBase X.obj.hom Y.obj.hom) ((e : ℤ) - 0)) :
    (G.functorTK.map (namePointHom X Y d α) (2 * d)).hom
        (ChowMotiveCat.tateGenNeg G.functorTK G.tateGen d) =
      ChowMotiveCat.cycleClassMotive G.functorTK G.tateGen (X ⊗ Y) d
        (chowGroupToCodimension (X ⊗ Y).obj.hom ((e : ℤ) - 0) d α) := by
  rw [namePointHom_eq_pointMotiveHom, ChowMotiveCat.cycleClassMotive_apply]
  exact G.map_eqToHom_comp_apply_of_heq _ _ _ _ _ HEq.rfl

section Axioms

variable (hA : G.toWeilData.PoincareDuality) (hB : G.toWeilData.Kunneth)
  (hC : G.toWeilData.CycleClassAxiom hA.perfectPairing)

/-- **Lieberman's lemma between equidimensional schemes** (proof of Stacks 0FHM): for `X`, `Y`
nonempty and equidimensional, the realization `G(c)` of a correspondence `c ∈ Corr⁰(X, Y)` is the
action `a ↦ pr₂,*(γ(c) ∪ pr₁^*a)` of Stacks 0FHL. -/
theorem corrMapG_eq_corrHomMap_of_equidimensional {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    {d e : ℕ} (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e)
    (f : WeilData.dz X ⟶ WeilData.dz Y) (n : ℤ) :
    G.corrMapG f n = WeilData.corrHomMap hA hB hC f n := by
  refine WeilData.CorrAction.ext_of_integral G.corrAction (WeilData.corrFunctorAction hA hB hC)
    hX.relativeDimension hY.relativeDimension n (fun α ↦ ?_) f
  refine LinearMap.ext fun a ↦ Subtype.ext ?_
  have h := corrMapG_eq_blockAct_of_name G hA.perfectPairing hB.kunnethTrace hX hY
    (WeilData.corrDz X Y ((corrEquivCorrespondence k X.obj.hom Y.obj.hom hX.relativeDimension
      hY.relativeDimension 0).symm ((1 : ℚ) ⊗ₜ[ℤ] α)))
    (unitTwistNegTensorHom ℚ (canonicalCorrespondenceCompositionData k).Obj d)
    (by rw [unitTwistNegTensorHom_eq_inv]; exact G.map_unitTwistTensorIsoOfEq_inv_gradedOne d)
    (namePointHom X Y d α) (tensorMotiveIso X Y) (tensorMotiveIso_hom X Y)
    (coevaluation_whiskerLeft_whiskerRight_eq hX.relativeDimension hY.relativeDimension α _
      (WeilData.corrDz_val _)) n a
  refine (congrArg Subtype.val h).trans ?_
  change _ = (WeilData.corrHomMap hA hB hC (WeilData.corrDz X Y _) n a : G.toWeilData.H Y)
  rw [WeilData.corrHomMap_corrDz, WeilData.corrMap_corrEquivCorrespondence_symm_tmul hA hB hC hX hY]
  exact congrArg (fun z ↦ (G.toWeilData.blockAct hA.perfectPairing hX hY z n a : G.toWeilData.H Y))
    ((congrArg (DirectSum.of (G.cohAlg (prod X Y)).piece (2 * d))
      (G.map_namePointHom_tateGenNeg α)).trans
      (of_cycleClassMotive G (prod X Y) d
        (chowGroupToCodimension (X ⊗ Y).obj.hom ((e : ℤ) - 0) d α)))

/-- **Lieberman's lemma** (proof of Stacks 0FHM): the realization `G(c)` of every correspondence
`c ∈ Corr⁰(X, Y)` is the action `a ↦ pr₂,*(γ(c) ∪ pr₁^*a)` of Stacks 0FHL attached to
`H^*(X) = G(h(X))`. -/
theorem corrMapG_eq_corrHomMap {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f : WeilData.dz X ⟶ WeilData.dz Y) (n : ℤ) :
    G.corrMapG f n = WeilData.corrHomMap hA hB hC f n :=
  WeilData.CorrAction.ext hA hB hC G.corrAction (WeilData.corrFunctorAction hA hB hC)
    (fun hX hY f n ↦ G.corrMapG_eq_corrHomMap_of_equidimensional hA hB hC hX hY f n) f n

end Axioms

end

end Stacks.WeilCohomology.WeilRealization

end
