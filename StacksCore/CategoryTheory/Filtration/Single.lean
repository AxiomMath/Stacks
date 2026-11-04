module

public import StacksCore.CategoryTheory.Filtration.GradedPieces

/-! # Filtered objects concentrated in one degree

`Filtration.single p W` is the filtration on `W` with `F^qW = W` for `q ≤ p` and `F^qW = 0` for
`q > p` (finite, with `gr^p = W` and all other graded pieces zero), the filtered analogue of
`HomologicalComplex.single`; `FilteredObject.singleFunctor p : W ↦ single p W`. It is left
adjoint to evaluation at `p` (`FilteredObject.singleAdjEval : singleFunctor p ⊣ eval (op p)`: a
morphism `single p W ⟶ X` is a morphism `W ⟶ F^pX`) and right adjoint to the quotient by the
`(p + 1)`-th step (`FilteredObject.quotAdjSingle : quot (op p) ⊣ singleFunctor (p - 1)`: a
morphism `X ⟶ single (p - 1) W` is a morphism `X/F^pX ⟶ W`). Hence over `ℤᵒᵖ` the functors
`F^p` and `X ↦ X/F^pX` are a right and a left adjoint (`Functor.IsRightAdjoint`/`IsLeftAdjoint`
instances), so `F^p` preserves all limits and `X/F^pX` all colimits, in particular kernels and
cokernels, which Stacks 05QH uses. Only zero morphisms, a zero object (and cokernels for `quot`)
are needed in `C`.

For a general index category both adjoints exist as well but are different functors (`F^j = ⊤`
iff there is an arrow `i ⟶ j`, resp. iff there is no arrow `j ⟶ i`); only the `ℤᵒᵖ` case is
constructed here.
-/

@[expose] public section

namespace CategoryTheory

open Limits Opposite

variable {C : Type*} [Category* C]

namespace Filtration

section Single

variable [HasZeroObject C]

/-- The steps of the filtration on `W` concentrated in degree `p` (`Filtration.single`):
`F^qW = W` for `q ≤ p` and `F^qW = 0` for `q > p`. -/
noncomputable def singleSubobject (p : ℤ) (W : C) (q : ℤ) : Subobject W :=
  if q ≤ p then ⊤ else ⊥

/-- `F^qW = W` for `q ≤ p`. -/
lemma singleSubobject_eq_top_of_le {p q : ℤ} (W : C) (h : q ≤ p) : singleSubobject p W q = ⊤ :=
  ite_eq_left h

/-- `F^qW = 0` for `q > p`. -/
lemma singleSubobject_eq_bot_of_lt {p q : ℤ} (W : C) (h : p < q) : singleSubobject p W q = ⊥ :=
  ite_eq_right h.not_ge

/-- The steps of `single p W` decrease. -/
lemma antitone_singleSubobject (p : ℤ) (W : C) : Antitone (singleSubobject p W) := by
  intro a b hab
  rcases le_or_gt b p with h | h
  · rw [singleSubobject_eq_top_of_le W h, singleSubobject_eq_top_of_le W (hab.trans h)]
  · rw [singleSubobject_eq_bot_of_lt W h]; exact bot_le

/-- The step `F^qW` of `single p W` is a zero object for `q > p`. -/
lemma isZero_singleSubobject_of_lt {p q : ℤ} (W : C) (h : p < q) :
    IsZero ((singleSubobject p W q : Subobject W) : C) := by
  rw [singleSubobject_eq_bot_of_lt W h]; exact (Limits.isZero_zero C).of_iso Subobject.botCoeIsoZero

/-- The filtration on `W` concentrated in degree `p`: `F^qW = W` for `q ≤ p` and `F^qW = 0` for
`q > p`, so that `gr^p = W` and every other graded piece vanishes. -/
@[implicit_reducible]
noncomputable def single (p : ℤ) (W : C) : Filtration W ℤᵒᵖ :=
  ofAntitone (singleSubobject p W) (antitone_singleSubobject p W)

/-- The steps of `single p W` are the representatives of `singleSubobject p W`. -/
lemma single_obj (p : ℤ) (W : C) (q : ℤ) :
    (single p W).obj (op q) = (singleSubobject p W q : C) := rfl

/-- The steps of `single p W`, in the form `simp` produces after unfolding `diagram`; this lets
`simp` close goals about `(single p W).ι.app (op q)`. -/
@[simp] lemma single_toMonoOver_obj_obj_left (p : ℤ) (W : C) (q : ℤ) :
    ((single p W).toMonoOver.obj (op q)).obj.left = (singleSubobject p W q : C) := rfl

/-- The inclusions of the steps of `single p W`. -/
@[simp] lemma single_ι_app (p : ℤ) (W : C) (q : ℤ) :
    (single p W).ι.app (op q) = (singleSubobject p W q).arrow := rfl

/-- The steps of `single p W`, as subobjects. -/
@[simp] lemma subobject_single (p : ℤ) (W : C) (q : ℤ) :
    (single p W).subobject (op q) = singleSubobject p W q :=
  subobject_ofAntitone _ _ q

/-- `F^q(single p W) = W` for `q ≤ p`. -/
lemma isIso_single_ι_app_of_le {p q : ℤ} (W : C) (h : q ≤ p) :
    IsIso ((single p W).ι.app (op q)) :=
  (Subobject.isIso_arrow_iff_eq_top _).2 (singleSubobject_eq_top_of_le W h)

/-- `F^q(single p W) = 0` for `q > p`. -/
lemma isZero_single_obj_of_lt {p q : ℤ} (W : C) (h : p < q) :
    IsZero ((single p W).obj (op q)) :=
  isZero_singleSubobject_of_lt W h

/-- `F^p(single p W) = W`. -/
instance isIso_single_ι_app (p : ℤ) (W : C) : IsIso ((single p W).ι.app (op p)) :=
  isIso_single_ι_app_of_le W le_rfl

/-- `single p W` is finite: `F^pW = W` and `F^{p+1}W = 0`. -/
instance isFinite_single (p : ℤ) (W : C) : IsFinite (single p W) where
  exists_isIso := ⟨op p, inferInstance⟩
  exists_isInitial := ⟨op (p + 1), ⟨(isZero_single_obj_of_lt W (Int.lt_succ p)).isInitial⟩⟩

end Single

end Filtration

namespace FilteredObject

open Filtration

section Single

variable [HasZeroMorphisms C] [HasZeroObject C]

/-- `W` concentrated in degree `p`: the filtered object with `F^qW = W` for `q ≤ p` and
`F^qW = 0` for `q > p`. -/
noncomputable abbrev single (p : ℤ) (W : C) : FilteredObject C ℤᵒᵖ := ⟨W, Filtration.single p W⟩

/-- A morphism into `W` factors through `F^qW` if it is zero whenever `q > p`. -/
private lemma singleSubobject_factors_of_eq_zero {p q : ℤ} {W A : C} (f : A ⟶ W)
    (h : p < q → f = 0) : (singleSubobject p W q).Factors f := by
  rcases le_or_gt q p with hq | hq
  · rw [singleSubobject_eq_top_of_le W hq]; exact Subobject.top_factors _
  · rw [h hq]; exact Subobject.factors_zero

/-- Morphisms `W ⟶ W'` respect the filtrations concentrated in degree `p`. -/
lemma singleSubobject_factors (p : ℤ) {W W' : C} (g : W ⟶ W') (q : ℤ) :
    (singleSubobject p W' q).Factors ((singleSubobject p W q).arrow ≫ g) :=
  singleSubobject_factors_of_eq_zero _ fun h => (isZero_singleSubobject_of_lt W h).eq_of_src _ _

/-- `W ↦ single p W` as a functor `C ⥤ FilteredObject C ℤᵒᵖ`; it is left adjoint to `eval (op p)`
(`singleAdjEval`), and `singleFunctor (p - 1)` is right adjoint to `quot (op p)`
(`quotAdjSingle`). -/
@[implicit_reducible]
noncomputable def singleFunctor (p : ℤ) : C ⥤ FilteredObject C ℤᵒᵖ where
  obj W := single p W
  map {_ W'} g := homMk g
    (fun q => (singleSubobject p W' q.unop).factorThru _ (singleSubobject_factors p g q.unop))
    (fun _ => Subobject.factorThru_arrow _ _ _)
  map_id _ := hom_ext rfl
  map_comp _ _ := hom_ext rfl

/-- The objects of `singleFunctor p`. -/
@[simp] lemma singleFunctor_obj (p : ℤ) (W : C) : (singleFunctor p).obj W = single p W := rfl

/-- The underlying morphisms of `singleFunctor p`. -/
@[simp] lemma singleFunctor_map_hom (p : ℤ) {W W' : C} (g : W ⟶ W') :
    ((singleFunctor p).map g).hom = g := rfl

/-- A morphism of filtered objects `X ⟶ single p W` kills `F^qX` for `q > p`, since
`F^q(single p W) = 0`. -/
lemma ι_app_hom_of_lt {p q : ℤ} {X : FilteredObject C ℤᵒᵖ} {W : C} (φ : X ⟶ single p W)
    (h : p < q) : X.filtration.ι.app (op q) ≫ φ.hom = 0 := by
  have h0 : φ.natTrans.app (op q) = 0 := (isZero_single_obj_of_lt W h).eq_of_tgt _ _
  rw [← φ.comm, h0, zero_comp]

/-- `singleFunctor p ⊣ eval (op p)`: a morphism `single p W ⟶ X` of filtered objects is a
morphism `W ⟶ F^pX`. Hence `X ↦ F^pX` is a right adjoint and preserves all limits. -/
noncomputable def singleAdjEval (p : ℤ) : singleFunctor p ⊣ eval (C := C) (op p) :=
  Adjunction.mkOfHomEquiv
    { homEquiv W X :=
        { toFun φ := inv ((single p W).filtration.ι.app (op p)) ≫ φ.natTrans.app (op p)
          invFun g := homMk' (g ≫ X.filtration.ι.app (op p)) fun q => by
            obtain ⟨q⟩ := q
            simp only [singleFunctor_obj, Filtration.single_ι_app]
            rcases le_or_gt q p with h | h
            · refine Subobject.factors_of_le _
                (X.filtration.subobject_le_of_hom (opHomOfLE h)) ?_
              exact Subobject.factors_of_factors_right _
                (Subobject.factors_of_factors_right g (Subobject.mk_factors_self _))
            · rw [(isZero_singleSubobject_of_lt W h).eq_of_src
                ((singleSubobject p W q).arrow ≫ g ≫ X.filtration.ι.app (op p)) 0]
              exact Subobject.factors_zero
          left_inv φ := hom_ext (by
            dsimp only
            rw [homMk'_hom, Category.assoc, φ.comm]
            exact IsIso.inv_hom_id_assoc _ _)
          right_inv g := by
            dsimp only
            rw [← cancel_mono (X.filtration.ι.app (op p)), Category.assoc, Hom.comm, homMk'_hom]
            exact IsIso.inv_hom_id_assoc _ _ }
      homEquiv_naturality_left_symm _ _ := hom_ext (Category.assoc _ _ _)
      homEquiv_naturality_right _ _ := (Category.assoc _ _ _).symm }

/-- `X ↦ F^pX` is a right adjoint (`singleAdjEval`), so it preserves all limits, in particular
kernels and monomorphisms. -/
instance isRightAdjoint_eval (i : ℤᵒᵖ) : (eval (C := C) i).IsRightAdjoint :=
  (singleAdjEval i.unop).isRightAdjoint

variable [HasCokernels C]

/-- `X ⟶ X/F^pX ⟶ W` maps every step `F^qX` into `F^q(single (p - 1) W)`: for `q ≥ p` the
composite `F^qX ⟶ X ⟶ X/F^pX` vanishes. -/
lemma singleSubobject_factors_ι_app_quotπ (p : ℤ) (X : FilteredObject C ℤᵒᵖ) {W : C}
    (g : (quot (op p)).obj X ⟶ W) (q : ℤᵒᵖ) :
    (singleSubobject (p - 1) W q.unop).Factors (X.filtration.ι.app q ≫ quotπ (op p) X ≫ g) :=
  singleSubobject_factors_of_eq_zero _ fun h => by
    rw [ι_app_quotπ_of_hom_assoc (op p) (opHomOfLE (Int.le_of_sub_one_lt h)) X, zero_comp]

/-- `quot (op p) ⊣ singleFunctor (p - 1)`: a morphism `X ⟶ single (p - 1) W` of filtered objects
is a morphism `X/F^pX ⟶ W`, since `F^p(single (p - 1) W) = 0`. Hence `X ↦ X/F^pX` is a left
adjoint and preserves all colimits. -/
noncomputable def quotAdjSingle (p : ℤ) : quot (C := C) (op p) ⊣ singleFunctor (p - 1) :=
  Adjunction.mkOfHomEquiv
    { homEquiv X W :=
        { toFun g := homMk (quotπ (op p) X ≫ g)
            (fun q => (singleSubobject (p - 1) W q.unop).factorThru _
              (singleSubobject_factors_ι_app_quotπ p X g q))
            (fun _ => Subobject.factorThru_arrow _ _ _)
          invFun φ :=
            quotDesc (op p) φ.hom (ι_app_hom_of_lt φ (Int.sub_one_lt_of_le le_rfl))
          left_inv _ := quot_hom_ext _ (quotπ_desc _ _ _)
          right_inv _ := hom_ext (quotπ_desc _ _ _) }
      homEquiv_naturality_left_symm _ _ := quot_hom_ext _ (by simp)
      homEquiv_naturality_right _ _ := hom_ext (Category.assoc _ _ _).symm }

/-- `X ↦ X/F^pX` is a left adjoint (`quotAdjSingle`), so it preserves all colimits, in
particular cokernels and epimorphisms. -/
instance isLeftAdjoint_quot (i : ℤᵒᵖ) : (quot (C := C) i).IsLeftAdjoint :=
  (quotAdjSingle i.unop).isLeftAdjoint

end Single

end FilteredObject

end CategoryTheory
