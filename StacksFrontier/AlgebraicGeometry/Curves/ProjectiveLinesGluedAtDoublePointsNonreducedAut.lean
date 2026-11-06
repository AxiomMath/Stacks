module

public import StacksFrontier.AlgebraicGeometry.Curves.ProjectiveLinesGluedAtDoublePointsDualNumbers
public import StacksFrontier.AlgebraicGeometry.Scheme.AutomorphismFunctor
public import StacksFrontier.AlgebraicGeometry.Scheme.ReducedFinitelyManyPoints
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The automorphism group scheme of two projective lines glued at three double points is
non-reduced

Let `k` be an algebraically closed field of characteristic `2`, `a₀, a₁, a₂ ∈ k` pairwise
distinct, and `X = ℙ¹_k ⨿_T ℙ¹_k` the curve obtained by gluing two copies of `ℙ¹_k` along the
three double points `T = ∐ᵢ Spec(k[t]/(t - aᵢ)²)`. Let `Aut(X)` be the automorphism functor
`T ↦ Aut_T(X_T)` on schemes over `k` (`AlgebraicGeometry.Scheme.autFunctor`).

* `Aut(X)(k)` is the automorphism group of `X` over `k`, which is finite
  (`AlgebraicGeometry.finite_aut_gluedCurve`).
* `Aut(X)(k[ε])` contains the automorphism `t ↦ t + ε`
  (`AlgebraicGeometry.gluedCurveDualNumbersAut`),
  which is not the identity, and which restricts to the identity on the closed fibre: the
  translation by `ε` becomes the translation by `0` modulo `ε`.

So the restriction map `Aut(X)(k[ε]) ⟶ Aut(X)(k)` is not injective. A reduced scheme locally of
finite type over `k` with finitely many `k`-points has no nonzero tangent vectors
(`AlgebraicGeometry.eq_of_dualNumber_points`), so **`Aut(X)` is not represented by any reduced
scheme locally of finite type over `k`: the automorphism group scheme of `X` is non-reduced.**

## Main results

* `AlgebraicGeometry.finite_autFunctor_gluedCurve`: `Aut(X)(k)` is finite.
* `AlgebraicGeometry.autFunctor_map_gluedCurveDualNumbersAut`: the automorphism `t ↦ t + ε`
  restricts to the identity over the closed point of `Spec k[ε]`.
* `AlgebraicGeometry.not_exists_isReduced_represents_autFunctor_gluedCurve`: **`Aut(X)` is
  non-reduced.**

## Implementation notes

The automorphism group of `X` is an algebraic space of finite type over `k` by the boundedness of
the diagonal of the stack of curves (Stacks 0DSQ), hence a group scheme (Stacks 0B8F). The
non-reducedness proved here does not depend on this: it is the statement that no reduced scheme
locally of finite type over `k` represents the functor `Aut(X)` on schemes over `k`.

## References

* [Stacks Project, Tag 0DSU](https://stacks.math.columbia.edu/tag/0DSU)
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Polynomial Opposite

namespace AlgebraicGeometry

universe u

variable (k : Type u) [Field k] (pts : Fin 3 → k) (hpts : Function.Injective pts)

/-- The point `Spec k` as a scheme over `Spec k`. -/
abbrev pointOver : Over (Spec (.of k)) := Over.mk (𝟙 (Spec (.of k)))

/-- The dual numbers `Spec k[ε]` as a scheme over `Spec k`. -/
@[sga "3 II 2.1" "special case",
  sga "3 II 4.7.1" "I_S for S = Spec k",
  sga "3 III 2.10" "special case",
  sga "3 VIIA 1.2.0" "special case"]
abbrev dualNumbersOver : Over (Spec (.of k)) := Over.mk (dualNumbersToBase k)

/-- The reduction `k[ε] ⟶ k` modulo `ε`. -/
abbrev dualNumbersFst : DualNumber k →+* k := (TrivSqZeroExt.fstHom k k k).toRingHom

/-- Reduction modulo `ε` is a retraction of `k ⟶ k[ε]`. -/
theorem dualNumbersFst_comp_algebraMap :
    (dualNumbersFst k).comp (algebraMap k (DualNumber k)) = RingHom.id k := by
  ext r
  rfl

/-- The closed point `Spec k ⟶ Spec k[ε]`, as a morphism of schemes over `k`. -/
@[sga "3 II 2.1" "zero section ε_M of ρ", sga "3 VIIA 1.2.0" "zero section τ : Z → I_Z"]
def dualNumbersClosedPoint : pointOver k ⟶ dualNumbersOver k :=
  Over.homMk (Spec.map (CommRingCat.ofHom (dualNumbersFst k))) (by
    change Spec.map (CommRingCat.ofHom (dualNumbersFst k)) ≫ dualNumbersToBase k = 𝟙 _
    rw [Spec_map_ofHom_comp_Spec_map_ofHom, dualNumbersFst_comp_algebraMap, CommRingCat.ofHom_id,
      Spec.map_id])

/-! ### `Aut(X)(k)` is finite -/

/-- The curve `X` as a scheme over `k`. -/
abbrev gluedCurveOver : Over (Spec (.of k)) := Over.mk (gluedCurveToBase k pts hpts)

/-- The base change of `X` along `𝟙 : Spec k ⟶ Spec k` is `X`. -/
def baseChangeOverPointIso :
    (Over.pullback (pointOver k).hom).obj (gluedCurveOver k pts hpts) ≅ gluedCurveOver k pts hpts :=
  Over.isoMk (asIso (pullback.fst (gluedCurveToBase k pts hpts) (𝟙 _))) (by
    change pullback.fst _ _ ≫ gluedCurveToBase k pts hpts = pullback.snd _ _
    rw [pullback.condition, Category.comp_id])

variable [IsAlgClosed k]

/-- `Aut(X)(k)` is finite. -/
@[stacks 0DSU "the automorphism group of X over k, the k-points of Aut(X), is finite"]
theorem finite_autFunctor_gluedCurve :
    Finite ((Scheme.autFunctor (gluedCurveOver k pts hpts)).obj (op (pointOver k))) := by
  have := finite_aut_gluedCurve k pts hpts
  exact Finite.of_equiv _ (baseChangeOverPointIso k pts hpts).conjAut.toEquiv.symm

/-! ### `t ↦ t + ε` is the identity modulo `ε` -/

/-- The translation `t ↦ t + 0` of `ℙ¹_R` is the identity. -/
theorem projectiveLineTranslation_zero {R : Type u} [CommRing R] :
    projectiveLineTranslation (0 : R) (mul_zero 0) = 𝟙 _ := by
  rw [projectiveLineTranslation]
  convert projectiveLineHom_id (R := R) toLaurent_X_mul_overlapInverseCoordinate_X using 2 <;>
    simp

/-- The closed fibre `X ⟶ X_{k[ε]}`. -/
def gluedCurveClosedFibre : gluedCurve k pts hpts ⟶ gluedCurveDualNumbers k pts hpts :=
  pullback.lift (𝟙 _)
    (gluedCurveToBase k pts hpts ≫ Spec.map (CommRingCat.ofHom (dualNumbersFst k)))
    (by
      rw [Category.id_comp, Category.assoc, Spec_map_ofHom_comp_Spec_map_ofHom,
        dualNumbersFst_comp_algebraMap, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id])

omit [IsAlgClosed k] in
/-- The closed fibre followed by the projection to `X` is the identity. -/
@[reassoc (attr := simp)]
theorem gluedCurveClosedFibre_fst :
    gluedCurveClosedFibre k pts hpts ≫ pullback.fst _ _ = 𝟙 _ :=
  pullback.lift_fst _ _ _

omit [IsAlgClosed k] in
/-- The closed fibre lies over the closed point of `Spec k[ε]`. -/
@[reassoc (attr := simp)]
theorem gluedCurveClosedFibre_snd :
    gluedCurveClosedFibre k pts hpts ≫ pullback.snd _ _ =
      gluedCurveToBase k pts hpts ≫ Spec.map (CommRingCat.ofHom (dualNumbersFst k)) :=
  pullback.lift_snd _ _ _

omit [IsAlgClosed k] in
/-- On each copy of `ℙ¹_k`, the closed fibre is the reduction `ℙ¹_k ⟶ ℙ¹_{k[ε]}` modulo `ε`
followed by the copy of `ℙ¹_{k[ε]}`. -/
theorem gluedCurveComponent_comp_closedFibre (b : Bool) :
    gluedCurveComponent k pts hpts b ≫ gluedCurveClosedFibre k pts hpts =
      projectiveLineMap (dualNumbersFst k) ≫ gluedCurveDualNumbersComponent k pts hpts b := by
  apply pullback.hom_ext
  · rw [Category.assoc, gluedCurveClosedFibre, pullback.lift_fst, Category.comp_id,
      Category.assoc, gluedCurveDualNumbersComponent_fst, ← Category.assoc,
      projectiveLineDualNumbersMap, projectiveLineMap, projectiveLineMap,
      projectiveLineHom_comp _ _ _ _ _ _ _ _ X X toLaurent_X_mul_overlapInverseCoordinate_X,
      dualNumbersFst_comp_algebraMap, projectiveLineHom_id, Category.id_comp]
    all_goals exact Polynomial.ringHom_ext (fun r ↦ by simp) (by simp)
  · rw [Category.assoc, gluedCurveClosedFibre, pullback.lift_snd, Category.assoc,
      gluedCurveDualNumbersComponent_snd, ← Category.assoc, gluedCurveComponent_comp_toBase,
      projectiveLineMap_comp_structureMorphism]

variable [CharP k 2]

omit [IsAlgClosed k] in
/-- The automorphism `t ↦ t + ε` is the identity on the closed fibre. -/
theorem gluedCurveClosedFibre_comp_aut :
    gluedCurveClosedFibre k pts hpts ≫ (gluedCurveDualNumbersAut k pts hpts).asIso.hom.left =
      gluedCurveClosedFibre k pts hpts := by
  refine gluedCurve_hom_ext k pts hpts fun b ↦ ?_
  rw [← Category.assoc, gluedCurveComponent_comp_closedFibre, Category.assoc,
    gluedCurveDualNumbersComponent_comp_aut, ← Category.assoc,
    projectiveLineMap_comp_projectiveLineTranslation]
  have : projectiveLineTranslation (dualNumbersFst k DualNumber.eps)
      (by rw [← map_mul, DualNumber.eps_mul_eps, map_zero]) = 𝟙 _ := by
    simp only [show dualNumbersFst k DualNumber.eps = 0 from DualNumber.fst_eps]
    exact projectiveLineTranslation_zero
  rw [this, Category.id_comp]

omit [IsAlgClosed k] [CharP k 2] in
/-- The projection `X_k ⟶ X_{k[ε]}` over the closed point, read on `X`. -/
theorem inv_fst_comp_baseChangeMap :
    inv (pullback.fst (gluedCurveToBase k pts hpts) (𝟙 _)) ≫
        Scheme.baseChangeMap (gluedCurveOver k pts hpts) (dualNumbersClosedPoint k) =
      gluedCurveClosedFibre k pts hpts := by
  rw [IsIso.inv_comp_eq]
  have h₁ := Scheme.baseChangeMap_fst (gluedCurveOver k pts hpts) (dualNumbersClosedPoint k)
  have h₂ := Scheme.baseChangeMap_snd (gluedCurveOver k pts hpts) (dualNumbersClosedPoint k)
  dsimp only [pointOver, dualNumbersOver, gluedCurveOver, Over.mk_hom] at h₁ h₂
  apply pullback.hom_ext <;>
    dsimp only [pointOver, dualNumbersOver, gluedCurveOver, Over.mk_hom]
  · rw [h₁, Category.assoc, gluedCurveClosedFibre_fst, Category.comp_id]
  · rw [h₂, Category.assoc, gluedCurveClosedFibre_snd, ← Category.assoc, pullback.condition,
      Category.comp_id]
    rfl

omit [IsAlgClosed k] in
/-- The base change of `t ↦ t + ε` to the closed point is the identity. -/
theorem endBaseChange_gluedCurveDualNumbersAut :
    Scheme.endBaseChange (gluedCurveOver k pts hpts) (dualNumbersClosedPoint k)
      (gluedCurveDualNumbersAut k pts hpts).asIso.hom = 𝟙 _ := by
  have key : Scheme.baseChangeMap (gluedCurveOver k pts hpts) (dualNumbersClosedPoint k) ≫
      (gluedCurveDualNumbersAut k pts hpts).asIso.hom.left =
        Scheme.baseChangeMap (gluedCurveOver k pts hpts) (dualNumbersClosedPoint k) := by
    rw [← cancel_epi (inv (pullback.fst (gluedCurveToBase k pts hpts) (𝟙 _))), ← Category.assoc,
      inv_fst_comp_baseChangeMap, gluedCurveClosedFibre_comp_aut]
  refine Scheme.endo_ext _ ?_
  rw [Scheme.endBaseChange_left_fst, ← Category.assoc, key, Scheme.baseChangeMap_fst]
  exact (Category.id_comp _).symm

omit [IsAlgClosed k] in
/-- The automorphism `t ↦ t + ε` of `X_{k[ε]}` restricts to the identity over the closed point
of `Spec k[ε]`: its image under `Aut(X)(k[ε]) ⟶ Aut(X)(k)` is the identity. -/
@[stacks 0DSU "the automorphism t ↦ t + ε becomes the identity modulo ε"]
theorem autFunctor_map_gluedCurveDualNumbersAut :
    (Scheme.autFunctor (gluedCurveOver k pts hpts)).map (dualNumbersClosedPoint k).op
      (gluedCurveDualNumbersAut k pts hpts) =
        (1 : Aut ((Over.pullback (pointOver k).hom).obj (gluedCurveOver k pts hpts))) := by
  rw [Scheme.autFunctor_map_apply]
  exact Aut.ext (Iso.ext (endBaseChange_gluedCurveDualNumbersAut k pts hpts))

/-! ### Non-reducedness -/

/-- **The automorphism group scheme of `X` is non-reduced.** For `k` algebraically closed of
characteristic `2` and three distinct points, no reduced scheme locally of finite type over `k`
represents the automorphism functor `T ↦ Aut_T(X_T)` of the curve `X` obtained by gluing two
copies of `ℙ¹_k` along the double points at the three points. -/
@[stacks 0DSU "Aut(X) is non-reduced"]
theorem not_exists_isReduced_represents_autFunctor_gluedCurve :
    ¬ ∃ (G : Over (Spec (.of k))) (_ : IsReduced G.left) (_ : LocallyOfFiniteType G.hom),
      Nonempty (yoneda.obj G ≅ Scheme.autFunctor (gluedCurveOver k pts hpts)) := by
  rintro ⟨G, _, _, ⟨e⟩⟩
  set F := Scheme.autFunctor (gluedCurveOver k pts hpts)
  have hfin : Finite {p : Spec (.of k) ⟶ G.left // p ≫ G.hom = 𝟙 _} := by
    have := finite_autFunctor_gluedCurve k pts hpts
    have h1 : Finite (pointOver k ⟶ G) :=
      Finite.of_equiv _ (e.app (op (pointOver k))).toEquiv.symm
    exact Finite.of_injective (fun p ↦ (Over.homMk p.1 p.2 : pointOver k ⟶ G)) fun p q h ↦
      Subtype.ext (congrArg (fun φ : pointOver k ⟶ G ↦ φ.left) h)
  have hinj : ∀ φ₁ φ₂ : dualNumbersOver k ⟶ G,
      dualNumbersClosedPoint k ≫ φ₁ = dualNumbersClosedPoint k ≫ φ₂ → φ₁ = φ₂ := by
    intro φ₁ φ₂ h
    ext1
    exact eq_of_dualNumber_points G.hom hfin (Over.w φ₁) (Over.w φ₂)
      (congrArg (fun φ : pointOver k ⟶ G ↦ φ.left) h)
  let E₁ := (e.app (op (dualNumbersOver k))).toEquiv
  let E₀ := (e.app (op (pointOver k))).toEquiv
  let Φ : F.obj (op (dualNumbersOver k)) := gluedCurveDualNumbersAut k pts hpts
  let one : F.obj (op (dualNumbersOver k)) :=
    (1 : Aut ((Over.pullback (dualNumbersOver k).hom).obj (gluedCurveOver k pts hpts)))
  have hnat : ∀ a : dualNumbersOver k ⟶ G,
      E₀ (dualNumbersClosedPoint k ≫ a) = F.map (dualNumbersClosedPoint k).op (E₁ a) := fun a ↦
    NatTrans.naturality_apply e.hom (dualNumbersClosedPoint k).op a
  have hne : E₁.symm Φ ≠ E₁.symm one := fun h ↦
    gluedCurveDualNumbersAut_ne_one k pts hpts (E₁.symm.injective h)
  have hΦ : F.map (dualNumbersClosedPoint k).op Φ = F.map (dualNumbersClosedPoint k).op one := by
    show (Scheme.autFunctor (gluedCurveOver k pts hpts)).map (dualNumbersClosedPoint k).op
      (gluedCurveDualNumbersAut k pts hpts) =
        Scheme.autBaseChange _ (dualNumbersClosedPoint k) 1
    rw [autFunctor_map_gluedCurveDualNumbersAut, map_one]
  refine hne (hinj _ _ (E₀.injective ?_))
  rwa [hnat, hnat, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

end AlgebraicGeometry
