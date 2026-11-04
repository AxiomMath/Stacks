module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.InternalHomTermwiseSplit
import StacksCore.Tactic.StacksAttribute

/-!
# The internal Hom complex out of a trivialised single term

Let `(C, O)` be a ringed site and let `E` be a complex of `O`-modules concentrated in a single
degree `k`, with `E^k` isomorphic to the structure sheaf `O`. This file identifies the internal
Hom complex `SheafHom(E, F)` of Stacks 0A8Z with the shift `F[k]` of the target, degreewise and
compatibly with the differentials, and deduces that

`SheafHom(E, F) ⟶ SheafHom(E, G)`

is a quasi-isomorphism whenever `F ⟶ G` is one. This is the base case of Stacks 08JH: the
general strictly perfect source is reduced to it by finite direct sums, retracts and the stupid
filtration.

The identification is evaluation at the unit section. A degree-`n` section of `SheafHom(E, F)`
over `U` is a degree-`n` cochain `E|_U ⟶ F|_U`; since `E` is concentrated in degree `k` the
cochain is just its `(k, k+n)` component, a morphism `E^k|_U ⟶ F^{k+n}|_U`; and a morphism out
of `O|_U` is determined by the image of `1`. That chain of bijections is
`unitOverHomEquiv`, `cochainSingleSourceEquiv` and `SheafHomComplex.sectionsIso`, and the
morphism of sheaves of modules realising it is `homUnitEvaluation`.

## Main definitions

* `AlgebraicGeometry.RingedSite.unitOverHomEquiv`: a morphism of `O|_U`-modules out of the
  restricted structure sheaf is the image of the unit section.
* `AlgebraicGeometry.RingedSite.homUnitEvaluation` and
  `AlgebraicGeometry.RingedSite.homUnitEvaluationIso`: evaluation of the internal Hom complex at
  a trivialisation of the single nonzero term of the source.

## Main results

* `AlgebraicGeometry.RingedSite.homUnitEvaluation_isIso`,
  `AlgebraicGeometry.RingedSite.homUnitEvaluation_d` and
  `AlgebraicGeometry.RingedSite.homUnitEvaluation_naturality`: it is an isomorphism, compatible
  with the differentials, and natural in the target.
* `AlgebraicGeometry.RingedSite.homMap_quasiIso_of_unit`: the base case of Stacks 08JH.

## Implementation notes

The internal Hom complex of Stacks 0A8Z is produced by `Classical.choice`, so its terms are
opaque; every statement below is proved through the characterising data `sectionsIso`,
`restrict_natural` and `smul_natural` of `AlgebraicGeometry.RingedSite.SheafHomComplex`, and
through `sectionsIso_homMap_v` for the induced maps. Nothing inspects the construction.

The compatibility with the differentials is the one place where a `rw` has to be made on a goal
that is not type-correct at `implicit` transparency, because a section `s` of the `n`-th term is
not *reducibly* a section of the complex of sections. The cure used is the one the repository
prescribes: the cochain identity coming from `CochainComplex.HomComplex.δ_v` is stated once for
an arbitrary cochain (`key`) and then applied, rather than rewritten in place.

No hypothesis on `E` beyond `E^p = 0` for `p ≠ k`, `d^k = 0` and `E^k ≅ O` is used; in
particular the statements apply verbatim to `(HomologicalComplex.single _ _ k).obj O`.

## References

* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})
/-- A morphism of `O|_U`-modules out of the restriction of the structure sheaf is determined by
the image of the unit section. -/
def unitOverHomEquiv (B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (U : X.C) :
    ((SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U ⟶ B.over U) ≃
      B.val.obj (op U) where
  toFun φ := (φ.val.app (op (Over.mk (𝟙 U))))
    (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
  invFun b := (B.over U).unitHomEquiv.symm
    ((B.over U).val.sectionsMk (fun V => B.val.map V.unop.hom.op b) (by
      intro V W g
      change B.val.map g.unop.left.op (B.val.map V.unop.hom.op b) = B.val.map W.unop.hom.op b
      rw [← PresheafOfModules.map_comp_apply]
      have hg : V.unop.hom.op ≫ g.unop.left.op = W.unop.hom.op :=
        congrArg Quiver.Hom.op (Over.w g.unop)
      rw [hg]))
  left_inv φ := by
    apply (B.over U).unitHomEquiv.injective
    rw [Equiv.apply_symm_apply]
    apply PresheafOfModules.sections_ext
    intro V
    have h := PresheafOfModules.naturality_apply φ.val
      (show V.unop ⟶ Over.mk (𝟙 U) from Over.homMk V.unop.hom (by simp)).op
      (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
    change B.val.map V.unop.hom.op
      (φ.val.app (op (Over.mk (𝟙 U)))
        (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))) =
      φ.val.app V (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V.unop.left))
    change φ.val.app V ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map V.unop.hom.op
        (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))) =
      B.val.map V.unop.hom.op
        (φ.val.app (op (Over.mk (𝟙 U)))
          (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))) at h
    rw [map_one] at h
    exact h.symm
  right_inv b := by
    change ((B.over U).unitHomEquiv ((B.over U).unitHomEquiv.symm _)).val
      (op (Over.mk (𝟙 U))) = b
    rw [Equiv.apply_symm_apply]
    change B.val.map (𝟙 U).op b = b
    rw [op_id, B.val.map_id]
    rfl

/-- A degree-`n` cochain out of a complex concentrated in degree `k` is the same thing as a
single morphism `E^k ⟶ F^{k+n}`. -/
private def cochainSingleSourceEquiv {A : Type*} [Category A] [Preadditive A]
    (E F : CochainComplex A ℤ) (k n : ℤ) (hE : ∀ p, p ≠ k → IsZero (E.X p)) :
    Cochain E F n ≃ (E.X k ⟶ F.X (k + n)) where
  toFun c := c.v k (k + n) rfl
  invFun f := Cochain.single f n
  left_inv c := by
    ext p q hpq
    by_cases hp : p = k
    · subst p
      subst q
      simp
    · exact (hE p hp).eq_of_src _ _
  right_inv f := Cochain.single_v f n rfl

variable {E F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- Evaluation of the internal Hom complex at a trivialisation of a single term of the source.

If `E^k ≅ O`, a degree-`n` section of `SheafHom(E, F)` over `U` has a `(k, k+n)` component, a
morphism `E^k|_U ⟶ F^{k+n}|_U`, and evaluating it at the image of the unit section gives a
section of `F^{k+n}` over `U`. -/
def homUnitEvaluation (k n : ℤ)
    (e : E.X k ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (sheafHomComplex X E F).obj.X n ⟶ F.X (k + n) where
  val :=
    { app := fun U => ModuleCat.ofHom
        { toFun := fun s =>
            (((AddCommGrpCat.Hom.hom (((sheafHomComplex X E F).sectionsIso U.unop).hom.f n)
              s).v k (k + n) rfl).val.app (op (Over.mk (𝟙 U.unop))))
                (e.inv.val.app U (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U))
          map_add' := fun a b =>
            congrArg
              (fun c : Cochain (restrictComplex X E U.unop) (restrictComplex X F U.unop) n =>
                (c.v k (k + n) rfl).val.app (op (Over.mk (𝟙 U.unop)))
                  (e.inv.val.app U (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)))
              (map_add (AddCommGrpCat.Hom.hom
                (((sheafHomComplex X E F).sectionsIso U.unop).hom.f n)) a b)
          map_smul' := by
            intro r s
            have h := (sheafHomComplex X E F).smul_natural U.unop r n k (k + n)
              rfl s (𝟙 U.unop)
              (e.inv.val.app U (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U))
            rw [op_id, (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map_id] at h
            exact h }
      naturality := by
        intro U V f
        refine ModuleCat.hom_ext (LinearMap.ext fun s => ?_)
        have he := PresheafOfModules.naturality_apply e.inv.val f
          (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)
        change e.inv.val.app V ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f 1) = _ at he
        rw [map_one] at he
        have hφ := PresheafOfModules.naturality_apply
          (((AddCommGrpCat.Hom.hom (((sheafHomComplex X E F).sectionsIso U.unop).hom.f n)
            s).v k (k + n) rfl).val)
          (Over.homMk (U := Over.mk f.unop) (V := Over.mk (𝟙 U.unop)) f.unop (by simp)).op
          (e.inv.val.app U (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U))
        have hr := (sheafHomComplex X E F).restrict_natural f.unop n k (k + n)
          rfl s (𝟙 V.unop)
          (e.inv.val.app V (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj V))
        rw [Category.id_comp] at hr
        exact hr.symm.trans (he ▸ hφ) }

/-- If `E` is concentrated in degree `k` and `E^k ≅ O`, then `homUnitEvaluation` is an
isomorphism. -/
theorem homUnitEvaluation_isIso (k n : ℤ)
    (e : E.X k ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hE : ∀ p, p ≠ k → IsZero (E.X p)) :
    IsIso (homUnitEvaluation X (F := F) k n e) := by
  let t := homUnitEvaluation X (F := F) k n e
  have ht (U : X.Cᵒᵖ) : IsIso (t.val.app U) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    let e₁ := (HomologicalComplex.Hom.isoApp
      ((sheafHomComplex X E F).sectionsIso U.unop) n).addCommGroupIsoToAddEquiv.toEquiv
    let e₂ := cochainSingleSourceEquiv (restrictComplex X E U.unop)
      (restrictComplex X F U.unop) k n
      (fun p hp => (SheafOfModules.overFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U.unop).map_isZero (hE p hp))
    let e₃ := Iso.homCongr
      ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U.unop).mapIso e)
        (Iso.refl ((F.X (k + n)).over U.unop))
    exact ((e₁.trans e₂).trans (e₃.trans (unitOverHomEquiv X (F.X (k + n)) U.unop))).bijective
  have : IsIso ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map t) :=
    (PresheafOfModules.isoMk (fun U => asIso (t.val.app U))
      fun _ _ g => t.val.naturality g).isIso_hom
  let := (SheafOfModules.fullyFaithfulForget.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).reflectsIsomorphisms
  exact isIso_of_reflects_iso t (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- `homUnitEvaluation` is compatible with the differentials when the differential leaving the
degree `k` term of the source vanishes. -/
theorem homUnitEvaluation_d (k n m : ℤ) (hnm : n + 1 = m)
    (e : E.X k ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hd : E.d k (k + 1) = 0) :
    (sheafHomComplex X E F).obj.d n m ≫ homUnitEvaluation X (F := F) k m e =
      homUnitEvaluation X (F := F) k n e ≫ F.d (k + n) (k + m) := by
  ext U s
  have hc : AddCommGrpCat.Hom.hom (((sheafHomComplex X E F).sectionsIso U.unop).hom.f m)
        (((sheafHomComplex X E F).obj.d n m).val.app U s) =
      CochainComplex.HomComplex.δ n m
        (AddCommGrpCat.Hom.hom (((sheafHomComplex X E F).sectionsIso U.unop).hom.f n) s) :=
    (congrArg (fun z => AddCommGrpCat.Hom.hom z s)
      (((sheafHomComplex X E F).sectionsIso U.unop).hom.comm n m)).symm
  have hdU : (restrictComplex X E U.unop).d k (k + 1) = 0 := by
    show (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U.unop).map
      (E.d k (k + 1)) = 0
    rw [hd, Functor.map_zero]
  have key : ∀ z : CochainComplex.HomComplex.Cochain (restrictComplex X E U.unop)
        (restrictComplex X F U.unop) n,
      (CochainComplex.HomComplex.δ n m z).v k (k + m) rfl =
        z.v k (k + n) rfl ≫ (restrictComplex X F U.unop).d (k + n) (k + m) := by
    intro z
    rw [CochainComplex.HomComplex.δ_v n m hnm z k (k + m) rfl (k + n) (k + 1) (by omega) rfl,
      hdU, zero_comp, smul_zero, add_zero]
  change (((AddCommGrpCat.Hom.hom (((sheafHomComplex X E F).sectionsIso U.unop).hom.f m)
    (((sheafHomComplex X E F).obj.d n m).val.app U s)).v k (k + m) rfl).val.app
      (op (Over.mk (𝟙 U.unop))))
    (e.inv.val.app U (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)) = _
  rw [hc]
  exact congrArg (fun φ : (restrictComplex X E U.unop).X k ⟶ _ =>
    φ.val.app (op (Over.mk (𝟙 U.unop)))
      (e.inv.val.app U (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U))) (key _)

/-- `homUnitEvaluation` is natural in the target complex. -/
theorem homUnitEvaluation_naturality
    {G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (f : F ⟶ G) (k n : ℤ)
    (e : E.X k ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (homMap X (𝟙 E) f).f n ≫ homUnitEvaluation X (F := G) k n e =
      homUnitEvaluation X (F := F) k n e ≫ f.f (k + n) := by
  ext U s
  have h := sectionsIso_homMap_v X (𝟙 E) f U.unop n k (k + n) rfl s
  show (((AddCommGrpCat.Hom.hom
    (((sheafHomComplex X E G).sectionsIso U.unop).hom.f n)
      (((homMap X (𝟙 E) f).f n).val.app U s)).v k (k + n) rfl).val.app
        (op (Over.mk (𝟙 U.unop))))
      (e.inv.val.app U (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)) = _
  rw [h]
  rfl

/-- The evaluation isomorphism `SheafHom(E, F)^n ≅ F^{k+n}` for a source concentrated in degree
`k` with `E^k ≅ O`. -/
def homUnitEvaluationIso (k n : ℤ)
    (e : E.X k ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hE : ∀ p, p ≠ k → IsZero (E.X p)) :
    (sheafHomComplex X E F).obj.X n ≅ F.X (k + n) :=
  @asIso _ _ _ _ (homUnitEvaluation X (F := F) k n e) (homUnitEvaluation_isIso X k n e hE)

/-- The three-term truncations of the internal Hom complex out of a source concentrated in
degree `k` with `E^k ≅ O` are isomorphic to those of the target, shifted by `k`. -/
def homUnitShortComplexIso (k i n j : ℤ) (hi : i + 1 = n) (hj : n + 1 = j)
    (e : E.X k ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hd : E.d k (k + 1) = 0) (hE : ∀ p, p ≠ k → IsZero (E.X p)) :
    ((sheafHomComplex X E F).obj.sc' i n j) ≅ F.sc' (k + i) (k + n) (k + j) :=
  ShortComplex.isoMk (homUnitEvaluationIso X k i e hE) (homUnitEvaluationIso X k n e hE)
    (homUnitEvaluationIso X k j e hE)
    (homUnitEvaluation_d X k i n hi e hd).symm
    (homUnitEvaluation_d X k n j hj e hd).symm

/-- **The single-term unit case.** If `E` is concentrated in degree `k` with `E^k ≅ O`, then the
internal Hom complex out of `E` carries a quasi-isomorphism of targets to a
quasi-isomorphism. -/
theorem homMap_quasiIso_of_unit
    {G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (f : F ⟶ G) [QuasiIso f] (k : ℤ)
    (e : E.X k ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hd : E.d k (k + 1) = 0) (hE : ∀ p, p ≠ k → IsZero (E.X p)) :
    QuasiIso (homMap X (𝟙 E) f) := by
  refine ⟨fun n => ?_⟩
  rw [quasiIsoAt_iff' _ (n - 1) n (n + 1) (by simp) (by simp)]
  have hf : ShortComplex.QuasiIso
      ((HomologicalComplex.shortComplexFunctor' _ _ (k + (n - 1)) (k + n)
        (k + (n + 1))).map f) :=
    (quasiIsoAt_iff' f (k + (n - 1)) (k + n) (k + (n + 1))
      (by simp; omega) (by simp; omega)).1 inferInstance
  refine (ShortComplex.quasiIso_iff_of_arrow_mk_iso _ _ (Arrow.isoMk
    (homUnitShortComplexIso X (F := F) k (n - 1) n (n + 1) (by omega) rfl e hd hE)
    (homUnitShortComplexIso X (F := G) k (n - 1) n (n + 1) (by omega) rfl e hd hE) ?_)).2 hf
  exact ShortComplex.hom_ext _ _ (homUnitEvaluation_naturality X f k (n - 1) e).symm
    (homUnitEvaluation_naturality X f k n e).symm
    (homUnitEvaluation_naturality X f k (n + 1) e).symm


end AlgebraicGeometry.RingedSite

end
