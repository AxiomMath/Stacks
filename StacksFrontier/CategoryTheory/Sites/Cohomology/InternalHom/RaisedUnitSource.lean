module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SectionUniverseLiftColimits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplexFunctoriality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.StrictlyPerfectInternalHomGeneral

/-!
# The internal Hom complex out of a trivialised single term, at unequal universes

Let `(C, O)` be a ringed site whose objects, morphisms and structure rings lie in three
independent universes `u`, `v` and `w`, and let `E` be a complex of `O`-modules with sections in
`w`, concentrated in a single degree `k`, with `E^k ≅ O`. The internal Hom complex
`SheafHom(E, F)` of Stacks 0A8Z has sections in `max u v w`, and in every degree `n` it is the
universe lift of `F^{k+n}`: a degree-`n` section over `U` is a morphism `E^k|_U ⟶ F^{k+n}|_U`,
which is determined by the image of the unit section. The identification is compatible with the
differentials, so on three-term truncations

`SheafHom(E, F)^{n-1} ⟶ SheafHom(E, F)^n ⟶ SheafHom(E, F)^{n+1}`

is the universe lift of `F^{k+n-1} ⟶ F^{k+n} ⟶ F^{k+n+1}`.

This is `AlgebraicGeometry.RingedSite.homUnitEvaluation` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.InternalHomUnitSource` with the
ringed site freed from `RingedSite.{u, u, u}`; there the universe lift is the identity. The
lift is `SheafOfModules.uliftForPresentation`.

The universe lift is not an artefact of the proof and the two evaluation maps cannot be merged:
`(sheafHomComplex X E F).obj.X n` has sections in `max u v w` and `F^{k+n}` has sections in `w`,
so away from the diagonal they are objects of different categories and no morphism between them
can be written. Only the bijection `AlgebraicGeometry.RingedSite.Raised.unitOverHomEquiv` on
which both rest is shared, and it is taken from
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.StrictlyPerfectInternalHomGeneral`.

## Main definitions

* `AlgebraicGeometry.RingedSite.Raised.homUnitEvaluationIso`: `SheafHom(E, F)^n` is the universe
  lift of `F^{k+n}`.
* `AlgebraicGeometry.RingedSite.Raised.homUnitShortComplexIso`: the same on three-term
  truncations.

## References

* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex

universe u v w

namespace AlgebraicGeometry.RingedSite.Raised

variable (X : RingedSite.{u, v, w})

variable {E F : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- Evaluation of the internal Hom complex at a trivialisation of a single term of the source,
landing in the universe lift of the target term. -/
def homUnitEvaluation (k n : ℤ)
    (e : E.X k ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (sheafHomComplex X E F).obj.X n ⟶
      SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w} (F.X (k + n)) where
  val :=
    { app := fun U => ModuleCat.ofHom
        { toFun := fun s => ULift.up
            ((((AddCommGrpCat.Hom.hom (((sheafHomComplex X E F).sectionsIso U.unop).hom.f n)
              s).v k (k + n) rfl).val.app (op (Over.mk (𝟙 U.unop))))
                (e.inv.val.app U (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)))
          map_add' := fun a b => congrArg ULift.up <|
            congrArg
              (fun c : Cochain (restrictComplex X E U.unop) (restrictComplex X F U.unop) n =>
                (c.v k (k + n) rfl).val.app (op (Over.mk (𝟙 U.unop)))
                  (e.inv.val.app U (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)))
              (map_add (AddCommGrpCat.Hom.hom
                (((sheafHomComplex X E F).sectionsIso U.unop).hom.f n)) a b)
          map_smul' := fun r s => by
            have h := (sheafHomComplex X E F).smul_natural U.unop r n k (k + n)
              rfl s (𝟙 U.unop)
                (e.inv.val.app U (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U))
            rw [op_id, (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map_id] at h
            exact congrArg ULift.up h }
      naturality := by
        intro U V f
        refine ModuleCat.hom_ext (LinearMap.ext fun s => ?_)
        let g : Over.mk f.unop ⟶ Over.mk (𝟙 U.unop) := Over.homMk f.unop (by simp)
        have he : (((restrictComplex X E U.unop).X k).val.map g.op)
              (e.inv.val.app U (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)) =
            e.inv.val.app V (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj V) := by
          have h := PresheafOfModules.naturality_apply e.inv.val f
            (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)
          change e.inv.val.app V ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f 1) = _
            at h
          rw [map_one] at h
          exact h.symm
        have hφ := PresheafOfModules.naturality_apply
          (((AddCommGrpCat.Hom.hom (((sheafHomComplex X E F).sectionsIso U.unop).hom.f n)
            s).v k (k + n) rfl).val) g.op
          (e.inv.val.app U (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U))
        have hr := (sheafHomComplex X E F).restrict_natural f.unop n k (k + n)
          rfl s (𝟙 V.unop)
            (e.inv.val.app V (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj V))
        rw [Category.id_comp] at hr
        rw [he] at hφ
        exact congrArg ULift.up (hr.symm.trans hφ) }

/-- If `E` is concentrated in degree `k` and `E^k ≅ O`, then `homUnitEvaluation` is an
isomorphism. -/
theorem homUnitEvaluation_isIso (k n : ℤ)
    (e : E.X k ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hE : ∀ p, p ≠ k → IsZero (E.X p)) :
    IsIso (homUnitEvaluation X k n e :
      (sheafHomComplex X E F).obj.X n ⟶
        SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w} (F.X (k + n))) := by
  let t := homUnitEvaluation X (F := F) k n e
  have ht (U : X.Cᵒᵖ) : IsIso (t.val.app U) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    let e₁ := (HomologicalComplex.Hom.isoApp
      ((sheafHomComplex X E F).sectionsIso U.unop) n).addCommGroupIsoToAddEquiv.toEquiv
    -- a degree-`n` cochain out of a source concentrated in degree `k` is a single morphism
    -- `E^k|_U ⟶ F^{k+n}|_U`
    let e₂ : Cochain (restrictComplex X E U.unop) (restrictComplex X F U.unop) n ≃
        ((restrictComplex X E U.unop).X k ⟶ (restrictComplex X F U.unop).X (k + n)) :=
      { toFun c := c.v k (k + n) rfl
        invFun f := Cochain.single f n
        left_inv c := by
          refine Cochain.ext _ _ fun p q hpq => ?_
          by_cases hp : p = k
          · subst p q
            simp
          · exact ((SheafOfModules.overFunctor
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U.unop).map_isZero
                (hE p hp)).eq_of_src _ _
        right_inv f := Cochain.single_v f n rfl }
    let e₃ := Iso.homCongr
      ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U.unop).mapIso e)
        (Iso.refl ((F.X (k + n)).over U.unop))
    exact (((e₁.trans e₂).trans (e₃.trans (unitOverHomEquiv X (F.X (k + n)) U.unop))).trans
      Equiv.ulift.symm).bijective
  have : IsIso ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map t) :=
    (inferInstance : IsIso (PresheafOfModules.isoMk (fun U => asIso (t.val.app U))
      (fun _ _ g => t.val.naturality g)).hom)
  have := (SheafOfModules.fullyFaithfulForget.{max u v w}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).reflectsIsomorphisms
  exact isIso_of_reflects_iso t
    (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- `homUnitEvaluation` is compatible with the differentials when the differential leaving the
degree `k` term of the source vanishes. -/
theorem homUnitEvaluation_d (k n m : ℤ) (hnm : n + 1 = m)
    (e : E.X k ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hd : E.d k (k + 1) = 0) :
    (sheafHomComplex X E F).obj.d n m ≫ homUnitEvaluation X (F := F) k m e =
      homUnitEvaluation X (F := F) k n e ≫
        SheafOfModules.uliftForPresentationMap.{u, v, w, w, max u v w} (F.d (k + n) (k + m)) := by
  ext U s
  have hc : AddCommGrpCat.Hom.hom (((sheafHomComplex X E F).sectionsIso U.unop).hom.f m)
        (((sheafHomComplex X E F).obj.d n m).val.app U s) =
      δ n m (AddCommGrpCat.Hom.hom (((sheafHomComplex X E F).sectionsIso U.unop).hom.f n) s) :=
    (congrArg (fun z => AddCommGrpCat.Hom.hom z s)
      (((sheafHomComplex X E F).sectionsIso U.unop).hom.comm n m)).symm
  have hdU : (restrictComplex X E U.unop).d k (k + 1) = 0 := by
    change (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U.unop).map
      (E.d k (k + 1)) = 0
    rw [hd, Functor.map_zero]
  have key (z : Cochain (restrictComplex X E U.unop) (restrictComplex X F U.unop) n) :
      (δ n m z).v k (k + m) rfl =
        z.v k (k + n) rfl ≫ (restrictComplex X F U.unop).d (k + n) (k + m) := by
    rw [δ_v n m hnm z k (k + m) rfl (k + n) (k + 1) (by omega) rfl,
      hdU, zero_comp, smul_zero, add_zero]
  let ev {j : ℤ} (φ : (restrictComplex X E U.unop).X k ⟶ (restrictComplex X F U.unop).X j) :=
    φ.val.app (op (Over.mk (𝟙 U.unop)))
      (e.inv.val.app U (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U))
  exact congrArg ULift.up <|
    (congrArg (fun z : Cochain (restrictComplex X E U.unop) (restrictComplex X F U.unop) m =>
      ev (z.v k (k + m) rfl)) hc).trans (congrArg ev (key _))

/-- The evaluation isomorphism `SheafHom(E, F)^n ≅ F^{k+n}`, up to the universe lift, for a
source concentrated in degree `k` with `E^k ≅ O`. -/
def homUnitEvaluationIso (k n : ℤ)
    (e : E.X k ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hE : ∀ p, p ≠ k → IsZero (E.X p)) :
    (sheafHomComplex X E F).obj.X n ≅
      SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w} (F.X (k + n)) :=
  @asIso _ _ _ _ (homUnitEvaluation X (F := F) k n e) (homUnitEvaluation_isIso X k n e hE)

/-- The three-term truncations of the internal Hom complex out of a source concentrated in
degree `k` with `E^k ≅ O` are the universe lifts of those of the target, shifted by `k`. -/
def homUnitShortComplexIso (k i n j : ℤ) (hi : i + 1 = n) (hj : n + 1 = j)
    (e : E.X k ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hd : E.d k (k + 1) = 0) (hE : ∀ p, p ≠ k → IsZero (E.X p)) :
    ((sheafHomComplex X E F).obj.sc' i n j) ≅
      (F.sc' (k + i) (k + n) (k + j)).map
        (SheafOfModules.uliftForPresentationFunctor.{u, v, w, w, max u v w}) :=
  ShortComplex.isoMk (homUnitEvaluationIso X k i e hE) (homUnitEvaluationIso X k n e hE)
    (homUnitEvaluationIso X k j e hE)
    (homUnitEvaluation_d X k i n hi e hd).symm
    (homUnitEvaluation_d X k n j hj e hd).symm

end AlgebraicGeometry.RingedSite.Raised

end
