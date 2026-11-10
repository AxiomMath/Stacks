module

public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.LogWedgeAlgebra
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.DeRhamComplexLogPoles
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedAlgebraHom
public import StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.Basic

/-!
# The de Rham complex of log poles as a sheaf of differential graded algebras

Let `f : X ⟶ S` be a morphism of schemes and `Y ⊆ X` an effective Cartier divisor for which the
de Rham complex of log poles is defined. This file proves clause (2) of [Stacks, Tag 0FUP]: with
the wedge product of clause (1), the de Rham complex of log poles
`AlgebraicGeometry.Scheme.Hom.deRhamComplexLogPoles` of [Stacks, Tag 0FUA] is a sheaf of
differential graded `f⁻¹𝒪_S`-algebras, and the inclusion `Ω^•_{X/S} ⟶ Ω^•_{X/S}(log Y)` is a
homomorphism of sheaves of differential graded algebras from the relative de Rham complex of
[Stacks, Tag 0FU6].

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.logPolesDifferentialGradedAlgebra`: **the sheaf of differential
  graded `f⁻¹𝒪_S`-algebras `Ω^•_{X/S}(log Y)`**, on the extension by zero
  `AlgebraicGeometry.Scheme.Hom.deRhamComplexLogPolesInt` of the complex of Tag 0FUA.
* `AlgebraicGeometry.Scheme.Hom.logPolesDifferentialGradedAlgebraInclusion`: **the inclusion as a
  homomorphism of sheaves of differential graded algebras**, from
  `AlgebraicGeometry.SheafOfModules.relativeDeRhamDifferentialGradedAlgebra`.

## Implementation notes

The structure is built as `AlgebraicGeometry.SheafOfModules.deRhamDifferentialGradedAlgebra` is
for `Ω^•_{X/S}`: in nonnegative degrees the term of the extended complex *is* the sheaf of forms
with logarithmic poles (`AlgebraicGeometry.Scheme.Hom.deRhamComplexLogPolesInt_X_natCast`), the
multiplication is the wedge product transported along that equality, and it is zero as soon as a
degree is negative, where the term is a zero sheaf. The axioms are then associativity, unit and
the Leibniz rule of the wedge product (`AlgebraicGeometry.Scheme.Hom.logFormsWedge_assoc`,
`AlgebraicGeometry.Scheme.Hom.logFormsWedge_one_left`,
`AlgebraicGeometry.Scheme.Hom.logD_logFormsWedge`), read through the transport.

## References

* [Stacks Project, Tag 0FUP](https://stacks.math.columbia.edu/tag/0FUP)
* [Stacks Project, Tag 0FU6](https://stacks.math.columbia.edu/tag/0FU6)
-/

@[expose] public noncomputable section

open CategoryTheory ComplexShape Opposite TopologicalSpace
open AlgebraicGeometry.SheafOfModules

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData)
  (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) (hlog : f.HasLogPolesDeRhamComplex I)

/-! ### Transport along equalities of sheaves of `f⁻¹𝒪_S`-modules -/

/-- A morphism of sheaves of `f⁻¹𝒪_S`-modules transported along equalities of its source and
target acts on local sections as the original morphism. -/
private theorem baseHom_app_heq {M M' N N' : _root_.SheafOfModules.{u} (baseRingSheaf f)}
    (hM : M = M') (hN : N = N') (g : M ⟶ N) (g' : M' ⟶ N') (hg : HEq g g') (U : X.Opensᵒᵖ)
    (x : M.val.obj U) (x' : M'.val.obj U) (hx : HEq x x') :
    HEq (g.val.app U x) (g'.val.app U x') := by
  cases hM; cases hN
  cases eq_of_heq hg; cases eq_of_heq hx
  rfl

/-- A transported bilinear map of sheaves of `f⁻¹𝒪_S`-modules agrees with the original one on
local sections identified by the transport. -/
private theorem baseBilinearMapOfEq_app_heq
    {M M' N N' P P' : _root_.SheafOfModules.{u} (baseRingSheaf f)}
    (hM : M = M') (hN : N = N') (hP : P = P')
    (m : _root_.SheafOfModules.BilinearMap M N P) (U : X.Opensᵒᵖ)
    (x : M'.val.obj U) (y : N'.val.obj U) (x' : M.val.obj U) (y' : N.val.obj U)
    (hx : HEq x x') (hy : HEq y y') :
    HEq ((bilinearMapOfEq hM hN hP m).app U x y) (m.app U x' y') := by
  cases hM; cases hN; cases hP
  cases eq_of_heq hx; cases eq_of_heq hy
  rfl

/-- Adding and scaling by an integer respect a heterogeneous equality of sections of equal
modules over `f⁻¹𝒪_S`. -/
private theorem baseAdd_zsmul_heq {U : X.Opensᵒᵖ}
    {M N : ModuleCat.{u} ((baseRingSheaf f).obj.obj U)} (hMN : M = N)
    (a b : M) (a' b' : N) (ha : HEq a a') (hb : HEq b b') (z : ℤ) :
    HEq (a + z • b) (a' + z • b') := by
  cases hMN; cases eq_of_heq ha; cases eq_of_heq hb; rfl

/-- Every local section of a zero sheaf of `f⁻¹𝒪_S`-modules vanishes. -/
private theorem baseSection_eq_zero_of_isZero {M : _root_.SheafOfModules.{u} (baseRingSheaf f)}
    (hz : Limits.IsZero M) (U : X.Opensᵒᵖ) (x : M.val.obj U) : x = 0 := by
  let ev : _root_.SheafOfModules.{u} (baseRingSheaf f) ⥤
      ModuleCat.{u} ((baseRingSheaf f).obj.obj U) :=
    _root_.SheafOfModules.evaluation (baseRingSheaf f) U
  have hev : ev.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  exact (ModuleCat.isZero_iff_subsingleton.mp (Functor.map_isZero ev hz)).elim x 0

/-- A local section of a sheaf of `f⁻¹𝒪_S`-modules is, up to transport, a local section of any
equal sheaf. -/
private theorem exists_heq_of_baseSheaf_eq {M M' : _root_.SheafOfModules.{u} (baseRingSheaf f)}
    (h : M = M') (U : X.Opensᵒᵖ) (x : M.val.obj U) : ∃ x' : M'.val.obj U, HEq x x' :=
  ⟨cast (congrArg (fun M : _root_.SheafOfModules.{u} (baseRingSheaf f) => (M.val.obj U : Type u))
    h) x, (cast_heq _ x).symm⟩

/-- Every local section of a negative-degree term of the extended relative de Rham complex
vanishes. -/
theorem deRhamComplexInt_section_eq_zero' (i : ℤ) (hi : i < 0) (U : X.Opensᵒᵖ)
    (x : ((deRhamComplexInt (deRhamAlgebras f) (deRhamDifferential (deRhamAlgebras f))).X i).val.obj
      U) : x = 0 := by
  refine baseSection_eq_zero_of_isZero f ?_ U x
  refine (Scheme.Hom.deRhamComplex f).isZero_extend_X embeddingUpNat i fun n hn => ?_
  exact absurd hi (not_lt_of_ge (hn ▸ Int.natCast_nonneg n))

/-- A local section of a nonnegative-degree term of the extended relative de Rham complex is,
up to transport, a local relative differential form. -/
theorem exists_heq_deRhamPiece (i : ℤ) (hi : 0 ≤ i) (U : X.Opensᵒᵖ)
    (x : ((deRhamComplexInt (deRhamAlgebras f) (deRhamDifferential (deRhamAlgebras f))).X i).val.obj
      U) : ∃ x' : ((deRhamAlgebras f).exterior.piece i).val.obj U, HEq x x' :=
  exists_heq_of_baseSheaf_eq f
    (deRhamComplexInt_X_of_nonneg (deRhamAlgebras f) (deRhamDifferential (deRhamAlgebras f)) i hi)
    U x

/-! ### The terms of the extended complex -/

/-- In a nonnegative degree the term of the de Rham complex of log poles extended by zero **is**
`Ω^p_{X/S}(log Y)`, read as a sheaf of `f⁻¹𝒪_S`-modules. -/
theorem deRhamComplexLogPolesInt_X_natCast (p : ℕ) :
    (deRhamComplexLogPolesInt f I hI hlog).X (p : ℤ) = logPolesFormsBase f I p := by
  change HomologicalComplex.extend.X (deRhamComplexLogPoles f I hI hlog)
      (embeddingUpNat.r (embeddingUpNat.f p)) =
    HomologicalComplex.extend.X (deRhamComplexLogPoles f I hI hlog) (some p)
  exact congrArg (HomologicalComplex.extend.X (deRhamComplexLogPoles f I hI hlog))
    (embeddingUpNat.r_f p)

/-- In a nonnegative degree `i` the term of the de Rham complex of log poles extended by zero is
`Ω^{i}_{X/S}(log Y)`, read as a sheaf of `f⁻¹𝒪_S`-modules. -/
theorem deRhamComplexLogPolesInt_X_of_nonneg (i : ℤ) (hi : 0 ≤ i) :
    (deRhamComplexLogPolesInt f I hI hlog).X i = logPolesFormsBase f I i.toNat := by
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hi
  exact deRhamComplexLogPolesInt_X_natCast f I hI hlog p

/-- In nonnegative degrees the differential of the extended complex is the differential of forms
with logarithmic poles. -/
theorem deRhamComplexLogPolesInt_d_heq (p q : ℕ) :
    HEq ((deRhamComplexLogPolesInt f I hI hlog).d (p : ℤ) (q : ℤ))
      ((deRhamComplexLogPoles f I hI hlog).d p q) := by
  change HEq (HomologicalComplex.extend.d (deRhamComplexLogPoles f I hI hlog)
    (embeddingUpNat.r (embeddingUpNat.f p)) (embeddingUpNat.r (embeddingUpNat.f q))) _
  rw [embeddingUpNat.r_f p, embeddingUpNat.r_f q]
  rfl

/-- On local sections, the differential of the extended complex from degree `p` to degree `p + 1`
is the differential `logD` of forms with logarithmic poles. -/
theorem deRhamComplexLogPolesInt_d_app_heq (i j : ℤ) (p : ℕ) (hi : i = (p : ℤ))
    (hj : j = ((p + 1 : ℕ) : ℤ)) (U : X.Opensᵒᵖ)
    (x : ((deRhamComplexLogPolesInt f I hI hlog).X i).val.obj U)
    (x' : (logPolesForms f I p).val.obj U) (hx : HEq x x') :
    HEq (((deRhamComplexLogPolesInt f I hI hlog).d i j).val.app U x)
      (logD hI hlog (W := U.unop) x') := by
  subst hi hj
  have h := baseHom_app_heq f (deRhamComplexLogPolesInt_X_natCast f I hI hlog p)
    (deRhamComplexLogPolesInt_X_natCast f I hI hlog (p + 1)) _ _
    (deRhamComplexLogPolesInt_d_heq f I hI hlog p (p + 1)) U x x' hx
  rwa [deRhamComplexLogPoles_d] at h

/-- Every local section of a negative-degree term vanishes. -/
theorem deRhamComplexLogPolesInt_section_eq_zero (i : ℤ) (hi : i < 0) (U : X.Opensᵒᵖ)
    (x : ((deRhamComplexLogPolesInt f I hI hlog).X i).val.obj U) : x = 0 := by
  refine baseSection_eq_zero_of_isZero f ?_ U x
  refine (deRhamComplexLogPoles f I hI hlog).isZero_extend_X embeddingUpNat i fun n hn => ?_
  exact absurd hi (not_lt_of_ge (hn ▸ Int.natCast_nonneg n))

/-- A local section of a nonnegative-degree term of the extended complex is, up to transport, a
local form with logarithmic poles. -/
theorem exists_heq_logPolesForms (i : ℤ) (hi : 0 ≤ i) (U : X.Opensᵒᵖ)
    (x : ((deRhamComplexLogPolesInt f I hI hlog).X i).val.obj U) :
    ∃ x' : (logPolesForms f I i.toNat).val.obj U, HEq x x' :=
  exists_heq_of_baseSheaf_eq f (deRhamComplexLogPolesInt_X_of_nonneg f I hI hlog i hi) U x

/-! ### The multiplication -/

/-- The wedge product of forms with logarithmic poles, as a bilinear map of sheaves of
`f⁻¹𝒪_S`-modules. -/
def logFormsWedgeBase (p q : ℕ) :
    _root_.SheafOfModules.BilinearMap (logPolesFormsBase f I p) (logPolesFormsBase f I q)
      (logPolesFormsBase f I (p + q)) where
  app U := (logFormsWedgeMap hI hlog p q).app U
  map_smul_left U s φ ψ :=
    (logFormsWedgeMap hI hlog p q).map_smul_left U ((baseRingHom f).hom.app U s) φ ψ
  map_smul_right U s φ ψ :=
    (logFormsWedgeMap hI hlog p q).map_smul_right U ((baseRingHom f).hom.app U s) φ ψ
  naturality g φ ψ := (logFormsWedgeMap hI hlog p q).naturality g φ ψ

/-- For nonnegative degrees `i` and `j`, the sheaf `Ω^{i + j}_{X/S}(log Y)` is the term of the
extended complex in degree `i + j`. -/
theorem logPolesFormsBase_toNat_add (i j : ℤ) (hi : 0 ≤ i) (hj : 0 ≤ j) :
    logPolesFormsBase f I (i.toNat + j.toNat)
        = (deRhamComplexLogPolesInt f I hI hlog).X (i + j) := by
  rw [deRhamComplexLogPolesInt_X_of_nonneg f I hI hlog (i + j) (by omega), Int.toNat_add hi hj]

/-- The wedge product on the terms of the extended complex, in a pair of nonnegative degrees. -/
def logMulOfNonneg (i j : ℤ) (hi : 0 ≤ i) (hj : 0 ≤ j) :
    _root_.SheafOfModules.BilinearMap ((deRhamComplexLogPolesInt f I hI hlog).X i)
      ((deRhamComplexLogPolesInt f I hI hlog).X j)
      ((deRhamComplexLogPolesInt f I hI hlog).X (i + j)) :=
  bilinearMapOfEq (deRhamComplexLogPolesInt_X_of_nonneg f I hI hlog i hi).symm
    (deRhamComplexLogPolesInt_X_of_nonneg f I hI hlog j hj).symm
    (logPolesFormsBase_toNat_add f I hI hlog i j hi hj)
        (logFormsWedgeBase f I hI hlog i.toNat j.toNat)

/-- The zero bilinear map. -/
def logMulZero (i j : ℤ) :
    _root_.SheafOfModules.BilinearMap ((deRhamComplexLogPolesInt f I hI hlog).X i)
      ((deRhamComplexLogPolesInt f I hI hlog).X j)
      ((deRhamComplexLogPolesInt f I hI hlog).X (i + j)) where
  app _ := 0
  map_smul_left _ r _ _ := (smul_zero r).symm
  map_smul_right _ r _ _ := (smul_zero r).symm
  naturality _ _ _ := map_zero _

/-- **The multiplication of the differential graded algebra `Ω^•_{X/S}(log Y)`**: the wedge
product in nonnegative degrees, and zero as soon as one degree is negative. -/
def logMul (i j : ℤ) :
    _root_.SheafOfModules.BilinearMap ((deRhamComplexLogPolesInt f I hI hlog).X i)
      ((deRhamComplexLogPolesInt f I hI hlog).X j)
      ((deRhamComplexLogPolesInt f I hI hlog).X (i + j)) :=
  if hi : 0 ≤ i then
    if hj : 0 ≤ j then logMulOfNonneg f I hI hlog i j hi hj
    else logMulZero f I hI hlog i j
  else logMulZero f I hI hlog i j

/-- In nonnegative degrees the multiplication `logMul` acts on local sections as the wedge product
of forms with logarithmic poles. -/
theorem logMul_app_heq (i j : ℤ) (hi : 0 ≤ i) (hj : 0 ≤ j) (U : X.Opensᵒᵖ)
    (x : ((deRhamComplexLogPolesInt f I hI hlog).X i).val.obj U)
    (y : ((deRhamComplexLogPolesInt f I hI hlog).X j).val.obj U)
    (x' : (logPolesForms f I i.toNat).val.obj U) (y' : (logPolesForms f I j.toNat).val.obj U)
    (hx : HEq x x') (hy : HEq y y') :
    HEq ((logMul f I hI hlog i j).app U x y) (logFormsWedge hI hlog (W := U.unop) x' y') := by
  have h : logMul f I hI hlog i j = logMulOfNonneg f I hI hlog i j hi hj := by
    simp [logMul, hi, hj]
  rw [h]
  exact baseBilinearMapOfEq_app_heq f _ _ _
      (logFormsWedgeBase f I hI hlog i.toNat j.toNat) U x y x' y'
    hx hy

/-! ### The unit -/

/-- In nonnegative degrees the term of the extended relative de Rham complex is the term of the
relative de Rham complex. -/
theorem deRhamComplexInt_X_natCast (p : ℕ) :
    (deRhamComplexInt (deRhamAlgebras f) (deRhamDifferential (deRhamAlgebras f))).X (p : ℤ) =
      (Scheme.Hom.deRhamComplex f).X p := by
  change HomologicalComplex.extend.X (Scheme.Hom.deRhamComplex f)
      (embeddingUpNat.r (embeddingUpNat.f p)) =
    HomologicalComplex.extend.X (Scheme.Hom.deRhamComplex f) (some p)
  exact congrArg (HomologicalComplex.extend.X (Scheme.Hom.deRhamComplex f)) (embeddingUpNat.r_f p)

/-- In nonnegative degrees the inclusion of extended complexes is the inclusion of forms with no
pole. -/
theorem deRhamComplexLogPolesIntInclusion_f_heq (p : ℕ) :
    HEq ((deRhamComplexLogPolesIntInclusion f I hI hlog).f (p : ℤ))
      ((deRhamComplexLogPolesInclusion f I hI hlog).f p) := by
  change HEq (HomologicalComplex.extend.mapX (deRhamComplexLogPolesInclusion f I hI hlog)
    (embeddingUpNat.r (embeddingUpNat.f p))) _
  rw [embeddingUpNat.r_f p]
  rfl

/-- On local sections in degree `p`, the inclusion of extended complexes is the inclusion
`logPolesFormsInclusion` of relative differential forms into forms with logarithmic poles. -/
theorem deRhamComplexLogPolesIntInclusion_f_app_heq (i : ℤ) (p : ℕ) (hi : i = (p : ℤ))
    (U : X.Opensᵒᵖ)
    (x : ((deRhamComplexInt (deRhamAlgebras f) (deRhamDifferential
        (deRhamAlgebras f))).X i).val.obj U)
    (x' : Γ(relativeDifferentialForms f (p : ℤ), U.unop)) (hx : HEq x x') :
    HEq (((deRhamComplexLogPolesIntInclusion f I hI hlog).f i).val.app U x)
      ((logPolesFormsInclusion f I p).val.app U x') := by
  subst hi
  exact baseHom_app_heq f (deRhamComplexInt_X_natCast f p)
      (deRhamComplexLogPolesInt_X_natCast f I hI hlog p)
    _ _ (deRhamComplexLogPolesIntInclusion_f_heq f I hI hlog p) U x x' hx

/-- **The unit of the differential graded algebra `Ω^•_{X/S}(log Y)`**: the image of the unit
`1` of `Ω^•_{X/S}`. -/
def logOne : ((deRhamComplexLogPolesInt f I hI hlog).X 0).sections :=
  _root_.SheafOfModules.sectionsMap ((deRhamComplexLogPolesIntInclusion f I hI hlog).f 0)
    (deRhamComplexIntOne (deRhamAlgebras f) (deRhamDifferential (deRhamAlgebras f)))

/-- On every open, the unit `logOne` is the form `1` with logarithmic poles. -/
theorem logOne_eval_heq (U : X.Opensᵒᵖ) :
    HEq ((logOne f I hI hlog).eval U) (logFormsOne (f := f) (I := I) U.unop) :=
  deRhamComplexLogPolesIntInclusion_f_app_heq f I hI hlog 0 0 rfl U _ _
    (deRhamDifferentialGradedAlgebra_one (deRhamAlgebras f) (deRhamDifferential
        (deRhamAlgebras f)) U)

/-- In degrees `a` and `b` given by natural numbers, the multiplication `logMul` acts on local
sections as the wedge product of forms with logarithmic poles. -/
theorem logMul_app_heq' (i j : ℤ) (a b : ℕ) (ha : i = (a : ℤ)) (hb : j = (b : ℤ))
    (U : X.Opensᵒᵖ)
    (x : ((deRhamComplexLogPolesInt f I hI hlog).X i).val.obj U)
    (y : ((deRhamComplexLogPolesInt f I hI hlog).X j).val.obj U)
    (x' : (logPolesForms f I a).val.obj U) (y' : (logPolesForms f I b).val.obj U)
    (hx : HEq x x') (hy : HEq y y') :
    HEq ((logMul f I hI hlog i j).app U x y) (logFormsWedge hI hlog (W := U.unop) x' y') := by
  subst ha; subst hb
  exact logMul_app_heq f I hI hlog _ _ (Int.natCast_nonneg a)
      (Int.natCast_nonneg b) U x y x' y' hx hy

/-- A local section of a nonnegative-degree term of the extended complex lies in a degree given by
a natural number `a`, and is, up to transport, a local form of degree `a` with logarithmic
poles. -/
theorem exists_heq_logPolesForms' (i : ℤ) (hi : 0 ≤ i) (U : X.Opensᵒᵖ)
    (x : ((deRhamComplexLogPolesInt f I hI hlog).X i).val.obj U) :
    ∃ (a : ℕ) (_ : i = (a : ℤ)) (x' : (logPolesForms f I a).val.obj U), HEq x x' := by
  obtain ⟨x', hx⟩ := exists_heq_logPolesForms f I hI hlog i hi U x
  exact ⟨i.toNat, (Int.toNat_of_nonneg hi).symm, x', hx⟩

private theorem zero_heq_zero_log {i j : ℤ} (h : i = j) (U : X.Opensᵒᵖ) :
    HEq (0 : ((deRhamComplexLogPolesInt f I hI hlog).X i).val.obj U)
      (0 : ((deRhamComplexLogPolesInt f I hI hlog).X j).val.obj U) := by
  cases h; rfl

private theorem bilin_eq_zero_left {M N P : _root_.SheafOfModules.{u} (baseRingSheaf f)}
    (m : _root_.SheafOfModules.BilinearMap M N P) (U : X.Opensᵒᵖ)
    {x : M.val.obj U} (y : N.val.obj U) (hx : x = 0) : m.app U x y = 0 := by
  rw [hx, map_zero, AddMonoidHom.zero_apply]

private theorem bilin_eq_zero_right {M N P : _root_.SheafOfModules.{u} (baseRingSheaf f)}
    (m : _root_.SheafOfModules.BilinearMap M N P) (U : X.Opensᵒᵖ)
    (x : M.val.obj U) {y : N.val.obj U} (hy : y = 0) : m.app U x y = 0 := by
  rw [hy, map_zero]

/-- The graded Leibniz rule for the multiplication, in a pair of nonnegative degrees. -/
theorem logMul_leibniz_of_nonneg (n m : ℤ) (hn : 0 ≤ n) (hm : 0 ≤ m) (U : X.Opensᵒᵖ)
    (x : ((deRhamComplexLogPolesInt f I hI hlog).X n).val.obj U)
    (y : ((deRhamComplexLogPolesInt f I hI hlog).X m).val.obj U) :
    ((deRhamComplexLogPolesInt f I hI hlog).d (n + m) (n + m + 1)).val.app U
        ((logMul f I hI hlog n m).app U x y) =
      _root_.SheafOfModules.gradedCast
          (fun k => ((deRhamComplexLogPolesInt f I hI hlog).X k).val.obj U) (add_right_comm n 1 m)
          ((logMul f I hI hlog (n + 1) m).app U
            (((deRhamComplexLogPolesInt f I hI hlog).d n (n + 1)).val.app U x) y) +
        (Int.negOnePow n : ℤ) •
          _root_.SheafOfModules.gradedCast
            (fun k => ((deRhamComplexLogPolesInt f I hI hlog).X k).val.obj U) (add_assoc n m 1).symm
            ((logMul f I hI hlog n (m + 1)).app U x
              (((deRhamComplexLogPolesInt f I hI hlog).d m (m + 1)).val.app U y)) := by
  obtain ⟨a, rfl, x', hx⟩ := exists_heq_logPolesForms' f I hI hlog n hn U x
  obtain ⟨b, rfl, y', hy⟩ := exists_heq_logPolesForms' f I hI hlog m hm U y
  have hmul := logMul_app_heq' f I hI hlog _ _ a b rfl rfl U x y x' y' hx hy
  have hleft := deRhamComplexLogPolesInt_d_app_heq f I hI hlog ((a : ℤ) + b) ((a : ℤ) + b + 1)
    (a + b) (by push_cast; ring) (by push_cast; ring) U _ _ hmul
  have hdx := deRhamComplexLogPolesInt_d_app_heq f I hI hlog (a : ℤ) ((a : ℤ) + 1) a rfl
    (by push_cast; ring) U x x' hx
  have hdy := deRhamComplexLogPolesInt_d_app_heq f I hI hlog (b : ℤ) ((b : ℤ) + 1) b rfl
    (by push_cast; ring) U y y' hy
  have hfirst := logMul_app_heq' f I hI hlog ((a : ℤ) + 1) b (a + 1) b
    (by push_cast; ring) rfl U _ y _ y' hdx hy
  have hsecond := logMul_app_heq' f I hI hlog a ((b : ℤ) + 1) a (b + 1) rfl (by push_cast; ring) U
    x _ x' _ hx hdy
  have hcast₁ := (_root_.SheafOfModules.gradedCast_heq
    (fun k => ((deRhamComplexLogPolesInt f I hI hlog).X k).val.obj U)
    (add_right_comm (a : ℤ) 1 (b : ℤ)) _).trans
      (hfirst.trans (logFormsCast_heq (Nat.add_right_comm a 1 b) _).symm)
  have hcast₂ := (_root_.SheafOfModules.gradedCast_heq
    (fun k => ((deRhamComplexLogPolesInt f I hI hlog).X k).val.obj U)
    (add_assoc (a : ℤ) (b : ℤ) 1).symm _).trans hsecond
  have hpiece : ((deRhamComplexLogPolesInt f I hI hlog).X ((a : ℤ) + b + 1)).val.obj U =
      (logPolesFormsBase f I (a + b + 1)).val.obj U := by
    have hi : (a : ℤ) + b + 1 = ((a + b + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [hi]
    exact congrArg (fun M : _root_.SheafOfModules.{u} (baseRingSheaf f) => M.val.obj U)
      (deRhamComplexLogPolesInt_X_natCast f I hI hlog (a + b + 1))
  rw [Int.coe_negOnePow_natCast]
  refine eq_of_heq (hleft.trans ((heq_of_eq
    (logD_logFormsWedge hI hlog (W := U.unop) x' y')).trans ?_))
  exact (baseAdd_zsmul_heq f hpiece _ _ _ _ hcast₁ hcast₂ ((-1 : ℤ) ^ a)).symm

/-! ### The differential graded algebra -/

/-- **The de Rham complex of log poles as a sheaf of differential graded `f⁻¹𝒪_S`-algebras**,
with the wedge product of `AlgebraicGeometry.Scheme.Hom.logFormsWedge` and the unit `1`. -/
def logPolesDifferentialGradedAlgebra :
    _root_.SheafOfModules.DifferentialGradedAlgebra.{u, u} (baseRingSheaf f) where
  complex := deRhamComplexLogPolesInt f I hI hlog
  mul := logMul f I hI hlog
  one := logOne f I hI hlog
  mul_assoc n m k U x y z := by
    by_cases hn : 0 ≤ n
    · by_cases hm : 0 ≤ m
      · by_cases hk : 0 ≤ k
        · obtain ⟨a, rfl, x', hx⟩ := exists_heq_logPolesForms' f I hI hlog n hn U x
          obtain ⟨b, rfl, y', hy⟩ := exists_heq_logPolesForms' f I hI hlog m hm U y
          obtain ⟨c, rfl, z', hz⟩ := exists_heq_logPolesForms' f I hI hlog k hk U z
          have hxy := logMul_app_heq' f I hI hlog _ _ a b rfl rfl U x y x' y' hx hy
          have hyz := logMul_app_heq' f I hI hlog _ _ b c rfl rfl U y z y' z' hy hz
          refine (logMul_app_heq' f I hI hlog _ _ (a + b) c (by push_cast; ring) rfl U _ z _ z'
            hxy hz).trans ?_
          refine HEq.trans ?_ (logMul_app_heq' f I hI hlog _ _ a (b + c) rfl (by push_cast; ring) U
            x _ x' _ hx hyz).symm
          exact (logFormsCast_heq (Nat.add_assoc a b c) _).symm.trans
            (heq_of_eq (logFormsWedge_assoc hI hlog x' y' z'))
        · have hz0 := deRhamComplexLogPolesInt_section_eq_zero f I hI hlog k (by omega) U z
          rw [bilin_eq_zero_right f _ U _ hz0,
            bilin_eq_zero_right f _ U _ (bilin_eq_zero_right f _ U y hz0)]
          exact zero_heq_zero_log f I hI hlog (add_assoc n m k) U
      · have hy0 := deRhamComplexLogPolesInt_section_eq_zero f I hI hlog m (by omega) U y
        rw [bilin_eq_zero_left f _ U _ (bilin_eq_zero_right f _ U x hy0),
          bilin_eq_zero_right f _ U _ (bilin_eq_zero_left f _ U z hy0)]
        exact zero_heq_zero_log f I hI hlog (add_assoc n m k) U
    · have hx0 := deRhamComplexLogPolesInt_section_eq_zero f I hI hlog n (by omega) U x
      rw [bilin_eq_zero_left f _ U _ (bilin_eq_zero_left f _ U y hx0),
        bilin_eq_zero_left f _ U _ hx0]
      exact zero_heq_zero_log f I hI hlog (add_assoc n m k) U
  one_mul n U x := by
    by_cases hn : 0 ≤ n
    · obtain ⟨a, rfl, x', hx⟩ := exists_heq_logPolesForms' f I hI hlog n hn U x
      refine (logMul_app_heq' f I hI hlog 0 a 0 a rfl rfl U _ x _ x'
        (logOne_eval_heq f I hI hlog U) hx).trans ?_
      exact (logFormsCast_heq (Nat.zero_add a) _).symm.trans
        ((heq_of_eq (logFormsWedge_one_left hI hlog x')).trans hx.symm)
    · have hx0 := deRhamComplexLogPolesInt_section_eq_zero f I hI hlog n (by omega) U x
      rw [bilin_eq_zero_right f _ U _ hx0, hx0]
      exact zero_heq_zero_log f I hI hlog (zero_add n) U
  mul_one n U x := by
    by_cases hn : 0 ≤ n
    · obtain ⟨a, rfl, x', hx⟩ := exists_heq_logPolesForms' f I hI hlog n hn U x
      refine (logMul_app_heq' f I hI hlog a 0 a 0 rfl rfl U x _ x' _ hx
        (logOne_eval_heq f I hI hlog U)).trans ?_
      exact (heq_of_eq (logFormsWedge_one_right hI hlog x')).trans hx.symm
    · have hx0 := deRhamComplexLogPolesInt_section_eq_zero f I hI hlog n (by omega) U x
      rw [bilin_eq_zero_left f _ U _ hx0, hx0]
      exact zero_heq_zero_log f I hI hlog (add_zero n) U
  leibniz n m U x y := by
    by_cases hn : 0 ≤ n
    · by_cases hm : 0 ≤ m
      · exact logMul_leibniz_of_nonneg f I hI hlog n m hn hm U x y
      · have hy0 := deRhamComplexLogPolesInt_section_eq_zero f I hI hlog m (by omega) U y
        rw [bilin_eq_zero_right f _ U x hy0, map_zero,
          bilin_eq_zero_right f _ U _ hy0,
          bilin_eq_zero_right f _ U x (by rw [hy0, map_zero]),
          _root_.SheafOfModules.gradedCast_zero, _root_.SheafOfModules.gradedCast_zero, smul_zero,
          add_zero]
    · have hx0 := deRhamComplexLogPolesInt_section_eq_zero f I hI hlog n (by omega) U x
      rw [bilin_eq_zero_left f _ U y hx0, map_zero,
        bilin_eq_zero_left f _ U y (by rw [hx0, map_zero]),
        bilin_eq_zero_left f _ U _ hx0,
        _root_.SheafOfModules.gradedCast_zero, _root_.SheafOfModules.gradedCast_zero, smul_zero,
        add_zero]

/-- The underlying complex of `logPolesDifferentialGradedAlgebra` is the de Rham complex of log
poles extended by zero. -/
theorem logPolesDifferentialGradedAlgebra_complex :
    (logPolesDifferentialGradedAlgebra f I hI hlog).complex
        = deRhamComplexLogPolesInt f I hI hlog :=
  rfl

/-- Multiplication in the differential graded algebra `Ω^•_{X/S}(log Y)` is the wedge product
of forms with logarithmic poles. -/
theorem logPolesDifferentialGradedAlgebra_mul (p q : ℕ) (U : X.Opensᵒᵖ)
    (x : ((logPolesDifferentialGradedAlgebra f I hI hlog).complex.X (p : ℤ)).val.obj U)
    (y : ((logPolesDifferentialGradedAlgebra f I hI hlog).complex.X (q : ℤ)).val.obj U)
    (x' : (logPolesForms f I p).val.obj U) (y' : (logPolesForms f I q).val.obj U)
    (hx : HEq x x') (hy : HEq y y') :
    HEq (((logPolesDifferentialGradedAlgebra f I hI hlog).mul (p : ℤ) (q : ℤ)).app U x y)
      (logFormsWedge hI hlog (W := U.unop) x' y') :=
  logMul_app_heq' f I hI hlog _ _ p q rfl rfl U x y x' y' hx hy

/-- The unit of the differential graded algebra `Ω^•_{X/S}(log Y)` is the form `1`. -/
theorem logPolesDifferentialGradedAlgebra_one (U : X.Opensᵒᵖ) :
    HEq ((logPolesDifferentialGradedAlgebra f I hI hlog).one.eval U)
      (logFormsOne (f := f) (I := I) U.unop) :=
  logOne_eval_heq f I hI hlog U

/-! ### The inclusion as a homomorphism of differential graded algebras -/

/-- **The inclusion `Ω^•_{X/S} ⟶ Ω^•_{X/S}(log Y)` as a homomorphism of sheaves of differential
graded `f⁻¹𝒪_S`-algebras.** -/
def logPolesDifferentialGradedAlgebraInclusion :
    _root_.SheafOfModules.DifferentialGradedAlgebra.Hom
      (relativeDeRhamDifferentialGradedAlgebra (inverseImageStructureMap f))
      (logPolesDifferentialGradedAlgebra f I hI hlog) where
  toHomologicalComplex := deRhamComplexLogPolesIntInclusion f I hI hlog
  map_mul n m U x y := by
    by_cases hn : 0 ≤ n
    · by_cases hm : 0 ≤ m
      · obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hn
        obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le hm
        obtain ⟨x', hx⟩ := exists_heq_deRhamPiece f (a : ℤ) hn U x
        obtain ⟨y', hy⟩ := exists_heq_deRhamPiece f (b : ℤ) hm U y
        have hmul := deRhamDifferentialGradedAlgebra_mul (deRhamAlgebras f)
          (deRhamDifferential (deRhamAlgebras f)) a b U x y x' y' hx hy
        have hL := deRhamComplexLogPolesIntInclusion_f_app_heq f I hI hlog ((a : ℤ) + b) (a + b)
          (by push_cast; ring) U _ (formWedge f a b U.unop x' y') hmul
        have hix := deRhamComplexLogPolesIntInclusion_f_app_heq f I hI hlog a a rfl U x x' hx
        have hiy := deRhamComplexLogPolesIntInclusion_f_app_heq f I hI hlog b b rfl U y y' hy
        have hR := logMul_app_heq' f I hI hlog _ _ a b rfl rfl U _ _ _ _ hix hiy
        refine eq_of_heq (hL.trans (HEq.trans ?_ hR.symm))
        exact heq_of_eq (logFormsWedge_logPolesFormsInclusion hI hlog (W := U.unop) x' y').symm
      · have hy0 := deRhamComplexInt_section_eq_zero' f m (by omega) U y
        have hy1 : ((deRhamComplexLogPolesIntInclusion f I hI hlog).f m).val.app U y = 0 := by
          rw [hy0, map_zero]
        have hl : ((relativeDeRhamDifferentialGradedAlgebra (inverseImageStructureMap f)).mul n
            m).app U x y = 0 := bilin_eq_zero_right f _ U x hy0
        refine ((congrArg (fun z => ((deRhamComplexLogPolesIntInclusion f I hI hlog).f
          (n + m)).val.app U z) hl).trans (map_zero _)).trans ?_
        exact (bilin_eq_zero_right f (logMul f I hI hlog n m) U _ hy1).symm
    · have hx0 := deRhamComplexInt_section_eq_zero' f n (by omega) U x
      have hx1 : ((deRhamComplexLogPolesIntInclusion f I hI hlog).f n).val.app U x = 0 := by
        rw [hx0, map_zero]
      have hl : ((relativeDeRhamDifferentialGradedAlgebra (inverseImageStructureMap f)).mul n
          m).app U x y = 0 := bilin_eq_zero_left f _ U y hx0
      refine ((congrArg (fun z => ((deRhamComplexLogPolesIntInclusion f I hI hlog).f
        (n + m)).val.app U z) hl).trans (map_zero _)).trans ?_
      exact (bilin_eq_zero_left f (logMul f I hI hlog n m) U _ hx1).symm

/-- The underlying morphism of complexes of `logPolesDifferentialGradedAlgebraInclusion` is the
inclusion of extended complexes `deRhamComplexLogPolesIntInclusion`. -/
theorem logPolesDifferentialGradedAlgebraInclusion_toHomologicalComplex :
    (logPolesDifferentialGradedAlgebraInclusion f I hI hlog).toHomologicalComplex =
      deRhamComplexLogPolesIntInclusion f I hI hlog :=
  rfl

/-- **The inclusion is unital**: it carries the unit of `Ω^•_{X/S}` to the unit of
`Ω^•_{X/S}(log Y)`. -/
theorem logPolesDifferentialGradedAlgebraInclusion_one (U : X.Opensᵒᵖ) :
    ((logPolesDifferentialGradedAlgebraInclusion f I hI hlog).toHomologicalComplex.f 0).val.app U
        ((relativeDeRhamDifferentialGradedAlgebra (inverseImageStructureMap f)).one.eval U) =
      (logPolesDifferentialGradedAlgebra f I hI hlog).one.eval U :=
  rfl

end AlgebraicGeometry.Scheme.Hom
