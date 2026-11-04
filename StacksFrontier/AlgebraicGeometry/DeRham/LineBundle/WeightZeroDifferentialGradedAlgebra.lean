module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.WeightZeroWedge
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.LogDifferentialGradedAlgebra

/-!
# The weight-zero forms of the complement of the zero section as a differential graded algebra

Let `f : X ⟶ S` be a morphism of schemes, `L` an invertible `𝒪_X`-module and `π : L^⋆ ⟶ X` the
complement of the zero section of its line bundle. The proof of Stacks Tag 0FUG observes:

> As the degree zero part of a grading on `(L^⋆ → X)_*Ω^•_{L^⋆/S}` we see that
> `Ω^•_{L^⋆/S,0}` is a differential graded `𝒪_X`-algebra and that the map
> `Ω^•_{X/S} → Ω^•_{L^⋆/S,0}` is a homomorphism of differential graded `𝒪_X`-algebras.

This file constructs that structure on the complex `Ω^•_{L^⋆/S,0}` of sheaves of
`f^{-1}𝒪_S`-modules of Tag 0FUF, extended by zero to negative degrees, and the homomorphism.

## Main definitions

* `Stacks.LineBundle.Situation.weightZeroDifferentialGradedAlgebra`: **the sheaf of differential
  graded `f^{-1}𝒪_S`-algebras `Ω^•_{L^⋆/S,0}`**, with the wedge product of forms of `L^⋆`.
* `Stacks.LineBundle.Situation.weightZeroDifferentialGradedAlgebraInclusion`: **the pullback of
  forms `Ω^•_{X/S} ⟶ Ω^•_{L^⋆/S,0}` as a homomorphism of sheaves of differential graded
  algebras**, from the relative de Rham complex of Tag 0FU6.

## Implementation notes

The structure is built as `AlgebraicGeometry.Scheme.Hom.logPolesDifferentialGradedAlgebra` is: in
nonnegative degrees the term of the extended complex is the weight-zero sheaf
(`Stacks.LineBundle.Situation.weightZeroBaseComplexInt_X_natCast`), the multiplication is the
weight-zero wedge product transported along that equality, and it is zero as soon as a degree is
negative.

## References

* [Stacks Project, Tag 0FUG](https://stacks.math.columbia.edu/tag/0FUG)
* [Stacks Project, Tag 0FUF](https://stacks.math.columbia.edu/tag/0FUF)
-/

@[expose] public noncomputable section

open CategoryTheory ComplexShape Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.SheafOfModules

universe u

namespace Stacks.LineBundle

variable (D : Situation.{u})

/-! ### Transport along equalities of sheaves of modules -/

/-- A morphism of sheaves of modules on `X` transported along equalities of its source and target
acts on heterogeneously equal local sections as the original morphism. -/
theorem Situation.sheafHom_app_heq {R : Sheaf (Opens.grothendieckTopology D.X.carrier) RingCat.{u}}
    {M M' N N' : _root_.SheafOfModules.{u} R} (hM : M = M') (hN : N = N') (g : M ⟶ N)
    (g' : M' ⟶ N') (hg : HEq g g') (U : D.X.Opensᵒᵖ) (x : M.val.obj U) (x' : M'.val.obj U)
    (hx : HEq x x') : HEq (g'.val.app U x') (g.val.app U x) := by
  cases hM
  cases hN
  cases eq_of_heq hg
  cases eq_of_heq hx
  rfl

/-- A transported bilinear map agrees with the original one on local sections identified by the
transport. -/
theorem Situation.bilinearMapOfEq_app_heq
    {R : Sheaf (Opens.grothendieckTopology D.X.carrier) RingCat.{u}}
    {M M' N N' P P' : _root_.SheafOfModules.{u} R}
    (hM : M = M') (hN : N = N') (hP : P = P')
    (m : _root_.SheafOfModules.BilinearMap M N P) (U : D.X.Opensᵒᵖ)
    (x : M'.val.obj U) (y : N'.val.obj U) (x' : M.val.obj U) (y' : N.val.obj U)
    (hx : HEq x' x) (hy : HEq y' y) :
    HEq (m.app U x' y') ((bilinearMapOfEq hM hN hP m).app U x y) := by
  cases hM
  cases hN
  cases hP
  cases eq_of_heq hx
  cases eq_of_heq hy
  rfl

/-- Sums with integer multiples of heterogeneously equal sections are heterogeneously equal. -/
theorem Situation.add_zsmul_heq
    {R : Sheaf (Opens.grothendieckTopology D.X.carrier) RingCat.{u}}
    {U : D.X.Opensᵒᵖ} {M N : ModuleCat.{u} (R.obj.obj U)} (hMN : M = N)
    (a b : M) (a' b' : N) (ha : HEq a a') (hb : HEq b b') (z : ℤ) :
    HEq (a' + z • b') (a + z • b) := by
  cases hMN
  cases eq_of_heq ha
  cases eq_of_heq hb
  rfl

/-- The zero sections of two terms of a complex in equal degrees are heterogeneously equal. -/
theorem Situation.complex_zero_heq_zero
    {R : Sheaf (Opens.grothendieckTopology D.X.carrier) RingCat.{u}}
    (K : CochainComplex (_root_.SheafOfModules.{u} R) ℤ) {i j : ℤ} (h : i = j) (U : D.X.Opensᵒᵖ) :
    HEq (0 : (K.X i).val.obj U) (0 : (K.X j).val.obj U) := by
  cases h
  rfl

/-- A bilinear map vanishes when its first argument does. -/
theorem Situation.bilinearMap_app_eq_zero_left
    {R : Sheaf (Opens.grothendieckTopology D.X.carrier) RingCat.{u}}
    {M N P : _root_.SheafOfModules.{u} R}
    (m : _root_.SheafOfModules.BilinearMap M N P) (U : D.X.Opensᵒᵖ)
    {x : M.val.obj U} (y : N.val.obj U) (hx : x = 0) : m.app U x y = 0 := by
  rw [hx, map_zero, AddMonoidHom.zero_apply]

/-- A bilinear map vanishes when its second argument does. -/
theorem Situation.bilinearMap_app_eq_zero_right
    {R : Sheaf (Opens.grothendieckTopology D.X.carrier) RingCat.{u}}
    {M N P : _root_.SheafOfModules.{u} R}
    (m : _root_.SheafOfModules.BilinearMap M N P) (U : D.X.Opensᵒᵖ)
    (x : M.val.obj U) {y : N.val.obj U} (hy : y = 0) : m.app U x y = 0 := by
  rw [hy, map_zero]

/-! ### The extended weight-zero complex -/

/-- The weight-zero de Rham complex `Ω^•_{L^⋆/S,0}` of sheaves of `f^{-1}𝒪_S`-modules, extended by
zero to negative degrees: the middle term of the residue sequence of Tag 0FUF. -/
abbrev Situation.weightZeroBaseComplexInt :
    CochainComplex (_root_.SheafOfModules.{u} (Scheme.Hom.baseRingSheaf D.f)) ℤ :=
  D.weightZeroBaseComplex.extend embeddingUpNat

/-- The middle term of the residue sequence is the extended weight-zero complex. -/
theorem Situation.residueBaseSequence_middle :
    D.residueBaseSequence.middle = D.weightZeroBaseComplexInt :=
  rfl

/-- In a nonnegative degree the term of the extended complex **is** `Ω^p_{L^⋆/S,0}`. -/
theorem Situation.weightZeroBaseComplexInt_X_natCast (p : ℕ) :
    D.weightZeroBaseComplexInt.X (p : ℤ) = (Scheme.Hom.toBaseModules D.f).obj (D.weightZero p) := by
  show HomologicalComplex.extend.X D.weightZeroBaseComplex
      (embeddingUpNat.r (embeddingUpNat.f p)) =
    HomologicalComplex.extend.X D.weightZeroBaseComplex (some p)
  exact congrArg (HomologicalComplex.extend.X D.weightZeroBaseComplex) (embeddingUpNat.r_f p)

/-- In a nonnegative degree `i` the term of the extended complex is `Ω^{i}_{L^⋆/S,0}`. -/
theorem Situation.weightZeroBaseComplexInt_X_of_nonneg (i : ℤ) (hi : 0 ≤ i) :
    D.weightZeroBaseComplexInt.X i =
      (Scheme.Hom.toBaseModules D.f).obj (D.weightZero i.toNat) := by
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hi
  exact D.weightZeroBaseComplexInt_X_natCast p

/-- In nonnegative degrees the differential of the extended complex is that of
`Ω^•_{L^⋆/S,0}`. -/
theorem Situation.weightZeroBaseComplexInt_d_heq (p q : ℕ) :
    HEq (D.weightZeroBaseComplexInt.d (p : ℤ) (q : ℤ)) (D.weightZeroBaseComplex.d p q) := by
  show HEq (HomologicalComplex.extend.d D.weightZeroBaseComplex
    (embeddingUpNat.r (embeddingUpNat.f p)) (embeddingUpNat.r (embeddingUpNat.f q))) _
  rw [embeddingUpNat.r_f p, embeddingUpNat.r_f q]
  rfl

/-- On a local section in degree `p`, the differential of the extended complex acts as the
weight-zero differential `Ω^p_{L^⋆/S,0} → Ω^{p+1}_{L^⋆/S,0}`. -/
theorem Situation.weightZeroBaseComplexInt_d_app_heq (i j : ℤ) (p : ℕ) (hi : i = (p : ℤ))
    (hj : j = ((p + 1 : ℕ) : ℤ)) (U : D.X.Opensᵒᵖ)
    (x : (D.weightZeroBaseComplexInt.X i).val.obj U)
    (x' : ((Scheme.Hom.toBaseModules D.f).obj (D.weightZero p)).val.obj U) (hx : HEq x x') :
    HEq ((D.weightZeroBaseComplexInt.d i j).val.app U x) (D.weightZeroD p U.unop x') := by
  subst hi hj
  have h := D.sheafHom_app_heq (D.weightZeroBaseComplexInt_X_natCast p)
    (D.weightZeroBaseComplexInt_X_natCast (p + 1)) _ _
    (D.weightZeroBaseComplexInt_d_heq p (p + 1)) U x x' hx
  rw [D.weightZeroBaseComplex_d] at h
  exact h.symm

/-- Every local section of a negative-degree term vanishes. -/
theorem Situation.weightZeroBaseComplexInt_section_eq_zero (i : ℤ) (hi : i < 0) (U : D.X.Opensᵒᵖ)
    (x : (D.weightZeroBaseComplexInt.X i).val.obj U) : x = 0 := by
  have hz : Limits.IsZero (D.weightZeroBaseComplexInt.X i) :=
    D.weightZeroBaseComplex.isZero_extend_X embeddingUpNat i fun n hn =>
      absurd hi (not_lt_of_ge (hn ▸ Int.natCast_nonneg n))
  let ev := _root_.SheafOfModules.evaluation (Scheme.Hom.baseRingSheaf D.f) U
  have hev : ev.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  exact (ModuleCat.isZero_iff_subsingleton.mp (Functor.map_isZero ev hz)).elim x 0

/-- Local sections of the term of the extended complex in degree `p` are those of
`Ω^p_{L^⋆/S,0}`. -/
private theorem Situation.weightZeroBaseComplexInt_obj_natCast (p : ℕ) (U : D.X.Opensᵒᵖ) :
    (D.weightZeroBaseComplexInt.X (p : ℤ)).val.obj U =
      ((Scheme.Hom.toBaseModules D.f).obj (D.weightZero p)).val.obj U :=
  congrArg (fun M : _root_.SheafOfModules.{u} (Scheme.Hom.baseRingSheaf D.f) => M.val.obj U)
    (D.weightZeroBaseComplexInt_X_natCast p)

/-- A local section of a nonnegative-degree term of the extended complex is a local section of
`Ω^a_{L^⋆/S,0}` for the natural number `a` equal to its degree. -/
theorem Situation.exists_heq_weightZero (i : ℤ) (hi : 0 ≤ i) (U : D.X.Opensᵒᵖ)
    (x : (D.weightZeroBaseComplexInt.X i).val.obj U) :
    ∃ (a : ℕ) (_ : i = (a : ℤ))
      (x' : ((Scheme.Hom.toBaseModules D.f).obj (D.weightZero a)).val.obj U), HEq x x' := by
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hi
  exact ⟨a, rfl, cast (by rw [D.weightZeroBaseComplexInt_obj_natCast a U]) x, (cast_heq _ x).symm⟩

/-! ### The multiplication -/

/-- The weight-zero wedge product, as a bilinear map of sheaves of `f⁻¹𝒪_S`-modules. -/
def Situation.weightZeroWedgeBase (p q : ℕ) :
    _root_.SheafOfModules.BilinearMap ((Scheme.Hom.toBaseModules D.f).obj (D.weightZero p))
      ((Scheme.Hom.toBaseModules D.f).obj (D.weightZero q))
      ((Scheme.Hom.toBaseModules D.f).obj (D.weightZero (p + q))) where
  app U := (D.weightZeroWedge p q).app U
  map_smul_left U s φ ψ :=
    (D.weightZeroWedge p q).map_smul_left U ((Scheme.Hom.baseRingHom D.f).hom.app U s) φ ψ
  map_smul_right U s φ ψ :=
    (D.weightZeroWedge p q).map_smul_right U ((Scheme.Hom.baseRingHom D.f).hom.app U s) φ ψ
  naturality g φ ψ := (D.weightZeroWedge p q).naturality g φ ψ

/-- For nonnegative degrees `i` and `j`, the sheaf `Ω^{i+j}_{L^⋆/S,0}` is the term of the extended
complex in degree `i + j`. -/
theorem Situation.weightZero_toNat_add (i j : ℤ) (hi : 0 ≤ i) (hj : 0 ≤ j) :
    (Scheme.Hom.toBaseModules D.f).obj (D.weightZero (i.toNat + j.toNat)) =
      D.weightZeroBaseComplexInt.X (i + j) := by
  rw [D.weightZeroBaseComplexInt_X_of_nonneg (i + j) (by omega), Int.toNat_add hi hj]

/-- The wedge product on the terms of the extended complex, in a pair of nonnegative degrees. -/
def Situation.weightZeroMulOfNonneg (i j : ℤ) (hi : 0 ≤ i) (hj : 0 ≤ j) :
    _root_.SheafOfModules.BilinearMap (D.weightZeroBaseComplexInt.X i)
      (D.weightZeroBaseComplexInt.X j) (D.weightZeroBaseComplexInt.X (i + j)) :=
  bilinearMapOfEq (D.weightZeroBaseComplexInt_X_of_nonneg i hi).symm
    (D.weightZeroBaseComplexInt_X_of_nonneg j hj).symm
    (D.weightZero_toNat_add i j hi hj) (D.weightZeroWedgeBase i.toNat j.toNat)

/-- The zero bilinear map. -/
def Situation.weightZeroMulZero (i j : ℤ) :
    _root_.SheafOfModules.BilinearMap (D.weightZeroBaseComplexInt.X i)
      (D.weightZeroBaseComplexInt.X j) (D.weightZeroBaseComplexInt.X (i + j)) where
  app _ := 0
  map_smul_left _ r _ _ := (smul_zero r).symm
  map_smul_right _ r _ _ := (smul_zero r).symm
  naturality _ _ _ := map_zero _

/-- **The multiplication of `Ω^•_{L^⋆/S,0}`**: the wedge product in nonnegative degrees, and zero
as soon as one degree is negative. -/
def Situation.weightZeroMul (i j : ℤ) :
    _root_.SheafOfModules.BilinearMap (D.weightZeroBaseComplexInt.X i)
      (D.weightZeroBaseComplexInt.X j) (D.weightZeroBaseComplexInt.X (i + j)) :=
  if hi : 0 ≤ i then
    if hj : 0 ≤ j then D.weightZeroMulOfNonneg i j hi hj
    else D.weightZeroMulZero i j
  else D.weightZeroMulZero i j

/-- On local sections in degrees `a` and `b`, the multiplication is the weight-zero wedge
product. -/
theorem Situation.weightZeroMul_app_heq (i j : ℤ) (a b : ℕ) (ha : i = (a : ℤ)) (hb : j = (b : ℤ))
    (U : D.X.Opensᵒᵖ) (x : (D.weightZeroBaseComplexInt.X i).val.obj U)
    (y : (D.weightZeroBaseComplexInt.X j).val.obj U)
    (x' : ((Scheme.Hom.toBaseModules D.f).obj (D.weightZero a)).val.obj U)
    (y' : ((Scheme.Hom.toBaseModules D.f).obj (D.weightZero b)).val.obj U)
    (hx : HEq x x') (hy : HEq y y') :
    HEq ((D.weightZeroMul i j).app U x y) ((D.weightZeroWedge a b).app U x' y') := by
  subst ha hb
  rw [show D.weightZeroMul (a : ℤ) (b : ℤ) =
      D.weightZeroMulOfNonneg a b (Int.natCast_nonneg a) (Int.natCast_nonneg b) by
    simp [Situation.weightZeroMul]]
  exact (D.bilinearMapOfEq_app_heq _ _ _ (D.weightZeroWedgeBase a b) U x y x' y'
    hx.symm hy.symm).symm

/-! ### The unit -/

/-- **The unit of `Ω^•_{L^⋆/S,0}`**: the constant form `1`, the image of the unit `1` of
`Ω^•_{X/S}` under the pullback of forms. -/
def Situation.weightZeroIntOne : (D.weightZeroBaseComplexInt.X 0).sections :=
  _root_.SheafOfModules.sectionsMap (D.residueBaseSequence.incl.f 0)
    (deRhamComplexIntOne (Scheme.Hom.deRhamAlgebras D.f)
      (deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f)))

/-- In degree `p` the first map of the residue sequence is the pullback of forms
`Ω^p_{X/S} → Ω^p_{L^⋆/S,0}`. -/
theorem Situation.residueBaseSequence_incl_f_heq (p : ℕ) :
    HEq (D.residueBaseSequence.incl.f (p : ℤ))
      ((Scheme.Hom.toBaseModules D.f).map (D.pullbackHom p)) := by
  show HEq (HomologicalComplex.extend.mapX D.inclusionBaseMap
    (embeddingUpNat.r (embeddingUpNat.f p))) _
  rw [embeddingUpNat.r_f p]
  rfl

/-- On a local section in degree `p`, the first map of the residue sequence acts as the pullback of
forms. -/
theorem Situation.residueBaseSequence_incl_f_app_heq (i : ℤ) (p : ℕ) (hi : i = (p : ℤ))
    (U : D.X.Opensᵒᵖ)
    (x : ((deRhamComplexInt (Scheme.Hom.deRhamAlgebras D.f)
      (deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f))).X i).val.obj U)
    (x' : Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), U.unop)) (hx : HEq x x') :
    HEq ((D.residueBaseSequence.incl.f i).val.app U x) ((D.pullbackHom p).app U.unop x') := by
  subst hi
  exact (D.sheafHom_app_heq (Scheme.Hom.deRhamComplexInt_X_natCast D.f p)
    (D.weightZeroBaseComplexInt_X_natCast p) _ _ (D.residueBaseSequence_incl_f_heq p) U x x'
    hx).symm

/-- The unit `1` of the extended complex is, on each open, the constant weight-zero form `1`. -/
theorem Situation.weightZeroIntOne_eval_heq (U : D.X.Opensᵒᵖ) :
    HEq (D.weightZeroIntOne.eval U) (D.weightZeroOne.eval U) :=
  (D.residueBaseSequence_incl_f_app_heq 0 0 rfl U _ _
    (deRhamDifferentialGradedAlgebra_one (Scheme.Hom.deRhamAlgebras D.f)
      (deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f)) U)).trans
    (heq_of_eq (D.pullbackHom_one U.unop))

/-! ### The Leibniz rule -/

/-- The graded Leibniz rule for the multiplication, in a pair of nonnegative degrees. -/
theorem Situation.weightZeroMul_leibniz_of_nonneg (n m : ℤ) (hn : 0 ≤ n) (hm : 0 ≤ m)
    (U : D.X.Opensᵒᵖ) (x : (D.weightZeroBaseComplexInt.X n).val.obj U)
    (y : (D.weightZeroBaseComplexInt.X m).val.obj U) :
    (D.weightZeroBaseComplexInt.d (n + m) (n + m + 1)).val.app U
        ((D.weightZeroMul n m).app U x y) =
      _root_.SheafOfModules.gradedCast
          (fun k => (D.weightZeroBaseComplexInt.X k).val.obj U) (add_right_comm n 1 m)
          ((D.weightZeroMul (n + 1) m).app U
            ((D.weightZeroBaseComplexInt.d n (n + 1)).val.app U x) y) +
        (Int.negOnePow n : ℤ) •
          _root_.SheafOfModules.gradedCast
            (fun k => (D.weightZeroBaseComplexInt.X k).val.obj U) (add_assoc n m 1).symm
            ((D.weightZeroMul n (m + 1)).app U x
              ((D.weightZeroBaseComplexInt.d m (m + 1)).val.app U y)) := by
  obtain ⟨a, rfl, x', hx⟩ := D.exists_heq_weightZero n hn U x
  obtain ⟨b, rfl, y', hy⟩ := D.exists_heq_weightZero m hm U y
  have hmul := D.weightZeroMul_app_heq _ _ a b rfl rfl U x y x' y' hx hy
  have hleft := D.weightZeroBaseComplexInt_d_app_heq ((a : ℤ) + b) ((a : ℤ) + b + 1) (a + b)
    (by push_cast; ring) (by push_cast; ring) U _ _ hmul
  have hdx := D.weightZeroBaseComplexInt_d_app_heq (a : ℤ) ((a : ℤ) + 1) a rfl
    (by push_cast; ring) U x x' hx
  have hdy := D.weightZeroBaseComplexInt_d_app_heq (b : ℤ) ((b : ℤ) + 1) b rfl
    (by push_cast; ring) U y y' hy
  have hfirst := D.weightZeroMul_app_heq ((a : ℤ) + 1) b (a + 1) b (by push_cast; ring) rfl U _ y
    _ y' hdx hy
  have hsecond := D.weightZeroMul_app_heq a ((b : ℤ) + 1) a (b + 1) rfl (by push_cast; ring) U
    x _ x' _ hx hdy
  have hcast₁ := (_root_.SheafOfModules.gradedCast_heq
    (fun k => (D.weightZeroBaseComplexInt.X k).val.obj U)
    (add_right_comm (a : ℤ) 1 (b : ℤ)) _).trans
      (hfirst.trans (D.weightZeroCast_heq (Nat.add_right_comm a 1 b) _).symm)
  have hcast₂ := (_root_.SheafOfModules.gradedCast_heq
    (fun k => (D.weightZeroBaseComplexInt.X k).val.obj U)
    (add_assoc (a : ℤ) (b : ℤ) 1).symm _).trans hsecond
  have hpiece : (D.weightZeroBaseComplexInt.X ((a : ℤ) + b + 1)).val.obj U =
      ((Scheme.Hom.toBaseModules D.f).obj (D.weightZero (a + b + 1))).val.obj U := by
    rw [show (a : ℤ) + b + 1 = ((a + b + 1 : ℕ) : ℤ) by push_cast; ring]
    exact D.weightZeroBaseComplexInt_obj_natCast (a + b + 1) U
  rw [Int.coe_negOnePow_natCast]
  exact eq_of_heq (hleft.trans ((heq_of_eq (D.weightZeroD_weightZeroWedge a b U.unop x' y')).trans
    (D.add_zsmul_heq hpiece _ _ _ _ hcast₁ hcast₂ ((-1 : ℤ) ^ a))))

/-! ### The differential graded algebra -/

/-- **The weight-zero part `Ω^•_{L^⋆/S,0}` of `π_*Ω^•_{L^⋆/S}` as a sheaf of differential graded
`f⁻¹𝒪_S`-algebras**, with the wedge product of forms of `L^⋆` and the unit `1`. Its complex is the
middle term of the residue sequence of Tag 0FUF. -/
def Situation.weightZeroDifferentialGradedAlgebra :
    _root_.SheafOfModules.DifferentialGradedAlgebra.{u, u} (Scheme.Hom.baseRingSheaf D.f) where
  complex := D.weightZeroBaseComplexInt
  mul := D.weightZeroMul
  one := D.weightZeroIntOne
  mul_assoc n m k U x y z := by
    by_cases hn : 0 ≤ n
    · by_cases hm : 0 ≤ m
      · by_cases hk : 0 ≤ k
        · obtain ⟨a, rfl, x', hx⟩ := D.exists_heq_weightZero n hn U x
          obtain ⟨b, rfl, y', hy⟩ := D.exists_heq_weightZero m hm U y
          obtain ⟨c, rfl, z', hz⟩ := D.exists_heq_weightZero k hk U z
          have hxy := D.weightZeroMul_app_heq _ _ a b rfl rfl U x y x' y' hx hy
          have hyz := D.weightZeroMul_app_heq _ _ b c rfl rfl U y z y' z' hy hz
          refine (D.weightZeroMul_app_heq _ _ (a + b) c (by push_cast; ring) rfl U _ z _ z'
            hxy hz).trans ?_
          refine HEq.trans ?_ (D.weightZeroMul_app_heq _ _ a (b + c) rfl (by push_cast; ring) U
            x _ x' _ hx hyz).symm
          exact D.weightZeroWedge_assoc a b c U.unop x' y' z'
        · have hz0 := D.weightZeroBaseComplexInt_section_eq_zero k (by omega) U z
          rw [D.bilinearMap_app_eq_zero_right _ U _ hz0,
            D.bilinearMap_app_eq_zero_right _ U _ (D.bilinearMap_app_eq_zero_right _ U y hz0)]
          exact D.complex_zero_heq_zero D.weightZeroBaseComplexInt (add_assoc n m k) U
      · have hy0 := D.weightZeroBaseComplexInt_section_eq_zero m (by omega) U y
        rw [D.bilinearMap_app_eq_zero_left _ U _ (D.bilinearMap_app_eq_zero_right _ U x hy0),
          D.bilinearMap_app_eq_zero_right _ U _ (D.bilinearMap_app_eq_zero_left _ U z hy0)]
        exact D.complex_zero_heq_zero D.weightZeroBaseComplexInt (add_assoc n m k) U
    · have hx0 := D.weightZeroBaseComplexInt_section_eq_zero n (by omega) U x
      rw [D.bilinearMap_app_eq_zero_left _ U _ (D.bilinearMap_app_eq_zero_left _ U y hx0),
        D.bilinearMap_app_eq_zero_left _ U _ hx0]
      exact D.complex_zero_heq_zero D.weightZeroBaseComplexInt (add_assoc n m k) U
  one_mul n U x := by
    by_cases hn : 0 ≤ n
    · obtain ⟨a, rfl, x', hx⟩ := D.exists_heq_weightZero n hn U x
      refine (D.weightZeroMul_app_heq 0 a 0 a rfl rfl U _ x _ x'
        (D.weightZeroIntOne_eval_heq U) hx).trans ?_
      exact (D.weightZeroWedge_one_left a U.unop x').trans hx.symm
    · have hx0 := D.weightZeroBaseComplexInt_section_eq_zero n (by omega) U x
      rw [D.bilinearMap_app_eq_zero_right _ U _ hx0, hx0]
      exact D.complex_zero_heq_zero D.weightZeroBaseComplexInt (zero_add n) U
  mul_one n U x := by
    by_cases hn : 0 ≤ n
    · obtain ⟨a, rfl, x', hx⟩ := D.exists_heq_weightZero n hn U x
      refine (D.weightZeroMul_app_heq a 0 a 0 rfl rfl U x _ x' _ hx
        (D.weightZeroIntOne_eval_heq U)).trans ?_
      exact (heq_of_eq (D.weightZeroWedge_one_right a U.unop x')).trans hx.symm
    · have hx0 := D.weightZeroBaseComplexInt_section_eq_zero n (by omega) U x
      rw [D.bilinearMap_app_eq_zero_left _ U _ hx0, hx0]
      exact D.complex_zero_heq_zero D.weightZeroBaseComplexInt (add_zero n) U
  leibniz n m U x y := by
    by_cases hn : 0 ≤ n
    · by_cases hm : 0 ≤ m
      · exact D.weightZeroMul_leibniz_of_nonneg n m hn hm U x y
      · have hy0 := D.weightZeroBaseComplexInt_section_eq_zero m (by omega) U y
        rw [D.bilinearMap_app_eq_zero_right _ U x hy0, map_zero,
          D.bilinearMap_app_eq_zero_right _ U _ hy0,
          D.bilinearMap_app_eq_zero_right _ U x (by rw [hy0, map_zero]),
          _root_.SheafOfModules.gradedCast_zero, _root_.SheafOfModules.gradedCast_zero, smul_zero,
          add_zero]
    · have hx0 := D.weightZeroBaseComplexInt_section_eq_zero n (by omega) U x
      rw [D.bilinearMap_app_eq_zero_left _ U y hx0, map_zero,
        D.bilinearMap_app_eq_zero_left _ U y (by rw [hx0, map_zero]),
        D.bilinearMap_app_eq_zero_left _ U _ hx0,
        _root_.SheafOfModules.gradedCast_zero, _root_.SheafOfModules.gradedCast_zero, smul_zero,
        add_zero]

/-- The underlying complex of `Ω^•_{L^⋆/S,0}` is the middle term of the residue sequence. -/
theorem Situation.weightZeroDifferentialGradedAlgebra_complex :
    D.weightZeroDifferentialGradedAlgebra.complex = D.residueBaseSequence.middle :=
  rfl

/-- Multiplication in `Ω^•_{L^⋆/S,0}` is the wedge product of weight-zero forms. -/
theorem Situation.weightZeroDifferentialGradedAlgebra_mul (p q : ℕ) (U : D.X.Opensᵒᵖ)
    (x : (D.weightZeroDifferentialGradedAlgebra.complex.X (p : ℤ)).val.obj U)
    (y : (D.weightZeroDifferentialGradedAlgebra.complex.X (q : ℤ)).val.obj U)
    (x' : ((Scheme.Hom.toBaseModules D.f).obj (D.weightZero p)).val.obj U)
    (y' : ((Scheme.Hom.toBaseModules D.f).obj (D.weightZero q)).val.obj U)
    (hx : HEq x x') (hy : HEq y y') :
    HEq ((D.weightZeroDifferentialGradedAlgebra.mul (p : ℤ) (q : ℤ)).app U x y)
      ((D.weightZeroWedge p q).app U x' y') :=
  D.weightZeroMul_app_heq _ _ p q rfl rfl U x y x' y' hx hy

/-! ### The pullback of forms as a homomorphism of differential graded algebras -/

/-- **The pullback of forms `Ω^•_{X/S} ⟶ Ω^•_{L^⋆/S,0}` as a homomorphism of sheaves of
differential graded `f⁻¹𝒪_S`-algebras**: the first map of the residue sequence of Tag 0FUF. -/
def Situation.weightZeroDifferentialGradedAlgebraInclusion :
    _root_.SheafOfModules.DifferentialGradedAlgebra.Hom
      (deRhamDifferentialGradedAlgebra (Scheme.Hom.deRhamAlgebras D.f)
        (deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f)))
      D.weightZeroDifferentialGradedAlgebra where
  toHomologicalComplex := D.residueBaseSequence.incl
  map_mul n m U x y := by
    by_cases hn : 0 ≤ n
    · by_cases hm : 0 ≤ m
      · obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hn
        obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le hm
        obtain ⟨x', hx⟩ := Scheme.Hom.exists_heq_deRhamPiece D.f (a : ℤ) hn U x
        obtain ⟨y', hy⟩ := Scheme.Hom.exists_heq_deRhamPiece D.f (b : ℤ) hm U y
        have hmul := deRhamDifferentialGradedAlgebra_mul (Scheme.Hom.deRhamAlgebras D.f)
          (deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f)) a b U x y x' y' hx hy
        have hL := D.residueBaseSequence_incl_f_app_heq ((a : ℤ) + b) (a + b)
          (by push_cast; ring) U _ (Scheme.Hom.formWedge D.f a b U.unop x' y') hmul
        have hix := D.residueBaseSequence_incl_f_app_heq a a rfl U x x' hx
        have hiy := D.residueBaseSequence_incl_f_app_heq b b rfl U y y' hy
        have hR := D.weightZeroMul_app_heq _ _ a b rfl rfl U _ _ _ _ hix hiy
        exact eq_of_heq (hL.trans ((heq_of_eq (D.pullbackHom_formWedge a b U.unop x' y')).trans
          hR.symm))
      · have hy0 := Scheme.Hom.deRhamComplexInt_section_eq_zero' D.f m (by omega) U y
        have hy1 : (D.residueBaseSequence.incl.f m).val.app U y = 0 := by
          rw [hy0, map_zero]
        rw [D.bilinearMap_app_eq_zero_right _ U x hy0, map_zero]
        exact (D.bilinearMap_app_eq_zero_right (D.weightZeroMul n m) U _ hy1).symm
    · have hx0 := Scheme.Hom.deRhamComplexInt_section_eq_zero' D.f n (by omega) U x
      have hx1 : (D.residueBaseSequence.incl.f n).val.app U x = 0 := by
        rw [hx0, map_zero]
      rw [D.bilinearMap_app_eq_zero_left _ U y hx0, map_zero]
      exact (D.bilinearMap_app_eq_zero_left (D.weightZeroMul n m) U _ hx1).symm

/-- The underlying map of complexes of the pullback of forms is the first map of the residue
sequence. -/
theorem Situation.weightZeroDifferentialGradedAlgebraInclusion_toHomologicalComplex :
    D.weightZeroDifferentialGradedAlgebraInclusion.toHomologicalComplex =
      D.residueBaseSequence.incl :=
  rfl

/-- **The inclusion is unital.** -/
theorem Situation.weightZeroDifferentialGradedAlgebraInclusion_one (U : D.X.Opensᵒᵖ) :
    (D.weightZeroDifferentialGradedAlgebraInclusion.toHomologicalComplex.f 0).val.app U
        ((deRhamDifferentialGradedAlgebra (Scheme.Hom.deRhamAlgebras D.f)
          (deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f))).one.eval U) =
      D.weightZeroDifferentialGradedAlgebra.one.eval U :=
  rfl

end Stacks.LineBundle
