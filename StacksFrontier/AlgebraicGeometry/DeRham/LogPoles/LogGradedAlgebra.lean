module

public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.LogWedgeAlgebra
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.DifferentialForms
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAlgebraPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerDegreeOne

/-!
# The forms with logarithmic poles as a sheaf of graded algebras

Let `f : X ⟶ S` be a morphism of schemes and `Y ⊆ X` an effective Cartier divisor for which the
de Rham complex of log poles is defined. This file assembles the forms with logarithmic poles
into a sheaf of `ℤ`-graded `𝒪_X`-algebras under the wedge product of [Stacks, Tag 0FUP] (1), and
the inclusion of the forms with no pole into a unital homomorphism of sheaves of graded algebras.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.logGradedAlgebra`: `Ω^•_{X/S}(log Y)` as a sheaf of graded
  `𝒪_X`-algebras; its degree-`i` piece is `Ω^i_{X/S}(log Y)` for `i ≥ 0` and zero for `i < 0`.
* `AlgebraicGeometry.Scheme.Hom.logGradedInclusion`: the inclusion `Ω^•_{X/S} ⟶ Ω^•_{X/S}(log Y)`
  as a unital homomorphism of sheaves of graded algebras.

## Main results

* `AlgebraicGeometry.Scheme.Hom.logFormsWedge_self_eq_zero`: a `1`-form with logarithmic poles has
  square zero.

## References

* [Stacks Project, Tag 0FUP](https://stacks.math.columbia.edu/tag/0FUP)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open scoped ZeroObject

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData)
  (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) (hlog : f.HasLogPolesDeRhamComplex I)

/-- The sheaf `Ω^i_{X/S}(log Y)` for an integer degree `i`: zero in negative degrees. -/
def logPiece : ℤ → X.Modules
  | Int.ofNat p => logPolesForms f I p
  | Int.negSucc _ => 0

/-- The zero bilinear map. -/
def logPieceMulZero (i j : ℤ) :
    _root_.SheafOfModules.BilinearMap (logPiece f I i) (logPiece f I j) (logPiece f I (i + j)) where
  app _ := 0
  map_smul_left _ r _ _ := (smul_zero r).symm
  map_smul_right _ r _ _ := (smul_zero r).symm
  naturality _ _ _ := map_zero _

/-- The wedge product of forms with logarithmic poles in integer degrees. -/
def logPieceMul : (i j : ℤ) →
    _root_.SheafOfModules.BilinearMap (logPiece f I i) (logPiece f I j) (logPiece f I (i + j))
  | Int.ofNat p, Int.ofNat q => logFormsWedgeMap hI hlog p q
  | Int.ofNat p, Int.negSucc n => logPieceMulZero f I (Int.ofNat p) (Int.negSucc n)
  | Int.negSucc n, j => logPieceMulZero f I (Int.negSucc n) j

/-- Every section of `Ω^i_{X/S}(log Y)` in a negative degree `i` is zero. -/
theorem logPiece_section_eq_zero (n : ℕ) (U : X.Opensᵒᵖ)
    (x : (logPiece f I (Int.negSucc n)).val.obj U) : x = 0 := by
  have hz : Limits.IsZero (logPiece f I (Int.negSucc n)) := Limits.isZero_zero _
  let ev : X.Modules ⥤ ModuleCat.{u} (X.ringCatSheaf.obj.obj U) :=
    _root_.SheafOfModules.evaluation X.ringCatSheaf U
  have hev : ev.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  exact (ModuleCat.isZero_iff_subsingleton.mp (Functor.map_isZero ev hz)).elim x 0

/-- The zero sections of `Ω^i_{X/S}(log Y)` and `Ω^j_{X/S}(log Y)` agree when `i = j`. -/
theorem logPiece_zero_heq_zero {i j : ℤ} (h : i = j) (U : X.Opensᵒᵖ) :
    HEq (0 : (logPiece f I i).val.obj U) (0 : (logPiece f I j).val.obj U) := by
  cases h
  rfl

/-- The unit of the forms with logarithmic poles, a global section of `Ω^0_{X/S}(log Y)`. -/
def logPieceOne : (logPiece f I 0).sections :=
  _root_.SheafOfModules.sectionsMap (logPolesFormsInclusion f I 0) (deRhamAlgebras f).exterior.one

/-- On an open `U`, the unit `logPieceOne` evaluates to `logFormsOne`. -/
theorem logPieceOne_eval (U : X.Opensᵒᵖ) :
    (logPieceOne f I).eval U = logFormsOne (f := f) (I := I) U.unop :=
  rfl

private theorem bilin_zero_left' {M N P : X.Modules}
    (m : _root_.SheafOfModules.BilinearMap M N P) (U : X.Opensᵒᵖ)
    {x : M.val.obj U} (y : N.val.obj U) (hx : x = 0) : m.app U x y = 0 := by
  rw [hx, map_zero, AddMonoidHom.zero_apply]

private theorem bilin_zero_right' {M N P : X.Modules}
    (m : _root_.SheafOfModules.BilinearMap M N P) (U : X.Opensᵒᵖ)
    (x : M.val.obj U) {y : N.val.obj U} (hy : y = 0) : m.app U x y = 0 := by
  rw [hy, map_zero]

/-- **The forms with logarithmic poles as a sheaf of graded `𝒪_X`-algebras**, with the wedge
product of `AlgebraicGeometry.Scheme.Hom.logFormsWedge` and the unit `1`. -/
def logGradedAlgebra :
    _root_.SheafOfModules.GradedAlgebra.{u, u}
        (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace) where
  piece := logPiece f I
  mul := logPieceMul f I hI hlog
  one := logPieceOne f I
  mul_assoc i j k U x y z := by
    rcases i with a | a
    · rcases j with b | b
      · rcases k with c | c
        · exact (logFormsCast_heq (Nat.add_assoc a b c) _).symm.trans
            (heq_of_eq (logFormsWedge_assoc hI hlog (W := U.unop) x y z))
        · rw [logPiece_section_eq_zero f I c U z, map_zero, map_zero, map_zero]
          exact logPiece_zero_heq_zero f I (add_assoc _ _ _) U
      · rw [logPiece_section_eq_zero f I b U y,
          bilin_zero_left' _ U _ (bilin_zero_right' _ U x rfl),
          bilin_zero_right' _ U _ (bilin_zero_left' _ U z rfl)]
        exact logPiece_zero_heq_zero f I (add_assoc _ _ _) U
    · rw [logPiece_section_eq_zero f I a U x,
        bilin_zero_left' _ U _ (bilin_zero_left' _ U y rfl), bilin_zero_left' _ U _ rfl]
      exact logPiece_zero_heq_zero f I (add_assoc _ _ _) U
  one_mul i U x := by
    rcases i with a | a
    · exact (logFormsCast_heq (Nat.zero_add a) _).symm.trans
        (heq_of_eq (logFormsWedge_one_left hI hlog (W := U.unop) x))
    · rw [logPiece_section_eq_zero f I a U x, bilin_zero_right' _ U _ rfl]
  mul_one i U x := by
    rcases i with a | a
    · exact heq_of_eq (logFormsWedge_one_right hI hlog (W := U.unop) x)
    · rw [logPiece_section_eq_zero f I a U x, bilin_zero_left' _ U _ rfl]

/-- The degree-`p` piece of `logGradedAlgebra` for `p : ℕ` is `Ω^p_{X/S}(log Y)`. -/
theorem logGradedAlgebra_piece_natCast (p : ℕ) :
    (logGradedAlgebra f I hI hlog).piece (p : ℤ) = logPolesForms f I p :=
  rfl

/-- In nonnegative degrees, the multiplication of `logGradedAlgebra` is `logFormsWedge`. -/
theorem logGradedAlgebra_mul_app (p q : ℕ) (U : X.Opensᵒᵖ) (x : (logPolesForms f I p).val.obj U)
    (y : (logPolesForms f I q).val.obj U) :
    ((logGradedAlgebra f I hI hlog).mul (p : ℤ) (q : ℤ)).app U x y =
      logFormsWedge hI hlog (W := U.unop) x y :=
  rfl

/-! ### The inclusion of the forms with no pole -/

/-- The inclusion `Ω^i_{X/S} ⟶ Ω^i_{X/S}(log Y)` in integer degrees. -/
def logPieceInclusion : (n : ℤ) →
    (relativeDifferentialFormsAlgebra f).piece n ⟶ logPiece f I n
  | Int.ofNat p => logPolesFormsInclusion f I p
  | Int.negSucc _ => (Limits.isZero_zero X.Modules).from_ _

/-- Every section of `Ω^i_{X/S}` in a negative degree `i` is zero. -/
theorem relativeDifferentialFormsAlgebra_section_eq_zero (n : ℕ) (U : X.Opensᵒᵖ)
    (x : ((relativeDifferentialFormsAlgebra f).piece (Int.negSucc n)).val.obj U) : x = 0 :=
  (SheafOfModules.algebras _ (relativeDifferentials f)).exteriorPiece_eq_zero_of_neg _
    (Int.negSucc_lt_zero n) U x

/-- **The inclusion `Ω^•_{X/S} ⟶ Ω^•_{X/S}(log Y)` as a unital homomorphism of sheaves of graded
`𝒪_X`-algebras.** -/
def logGradedInclusion :
    _root_.SheafOfModules.GradedAlgebra.UnitalHom (relativeDifferentialFormsAlgebra f)
      (logGradedAlgebra f I hI hlog) where
  app := logPieceInclusion f I
  map_mul i j U x y := by
    rcases i with a | a
    · rcases j with b | b
      · exact (logFormsWedge_logPolesFormsInclusion hI hlog (W := U.unop) x y).symm
      · rw [relativeDifferentialFormsAlgebra_section_eq_zero f b U y, map_zero, map_zero, map_zero]
        rfl
    · rw [relativeDifferentialFormsAlgebra_section_eq_zero f a U x, map_zero,
        AddMonoidHom.zero_apply, map_zero]
      rfl
  map_one _ := rfl

/-- In degree `p : ℕ`, `logGradedInclusion` is the inclusion `logPolesFormsInclusion`. -/
theorem logGradedInclusion_app_natCast (p : ℕ) :
    (logGradedInclusion f I hI hlog).app (p : ℤ) = logPolesFormsInclusion f I p :=
  rfl

/-! ### Degree-one forms with logarithmic poles have square zero -/

/-- A relative `1`-form has square zero. -/
theorem formWedge_self_eq_zero (V : X.Opens) (κ : Γ(relativeDifferentialForms f ((1 : ℕ) : ℤ), V)) :
    formWedge f 1 1 V κ κ = 0 := by
  let A := SheafOfModules.algebras _ (relativeDifferentials f)
  have := A.isIso_exteriorGenerator
  have hκ : A.exteriorGenerator.val.app (op V) ((inv A.exteriorGenerator).val.app (op V) κ) = κ :=
    _root_.SheafOfModules.iso_inv_hom_app_apply (asIso A.exteriorGenerator).symm (op V) κ
  have h := A.squareZero_exteriorGenerator (op V) ((inv A.exteriorGenerator).val.app (op V) κ)
  rwa [hκ] at h

end AlgebraicGeometry.Scheme.Hom

namespace Stacks.Divisors.IdealTrivialization

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} {f : X ⟶ S} {I : X.IdealSheafData} {U : X.Opens}
  (e : IdealTrivialization I U)
  (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) (hlog : f.HasLogPolesDeRhamComplex I)

include e in
/-- A degree-one form with logarithmic poles has square zero, on a chart. -/
theorem logFormsWedge_self_eq_zero_of_le {V : X.Opens} (hV : V ≤ U)
    (φ : (logPolesForms f I 1).val.obj (op V)) : logFormsWedge hI hlog φ φ = 0 := by
  refine e.logForms_eq_zero_of_equationAt_smul_eq_zero hlog hV _
    (e.logForms_eq_zero_of_equationAt_smul_eq_zero hlog hV _ ?_)
  rw [← logFormsWedge_smul_left, ← logFormsWedge_smul_right,
    e.equationAt_smul_eq_logPolesFormsInclusion hV φ, logFormsWedge_logPolesFormsInclusion,
    formWedge_self_eq_zero]
  exact map_zero _

end Stacks.Divisors.IdealTrivialization

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData)
  (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) (hlog : f.HasLogPolesDeRhamComplex I)

/-- **A degree-one form with logarithmic poles has square zero**: `φ ∧ φ = 0`. -/
theorem logFormsWedge_self_eq_zero {W : X.Opens} (φ : (logPolesForms f I 1).val.obj (op W)) :
    logFormsWedge hI hlog φ φ = 0 := by
  refine logPolesForms_ext_of_local fun x hx => ?_
  obtain ⟨Ux, hxU, ⟨e⟩⟩ := Stacks.Divisors.IdealTrivialization.exists_mem_nonempty hI x
  refine ⟨W ⊓ Ux, inf_le_left, ⟨hx, hxU⟩, ?_⟩
  rw [← logFormsWedge_res, map_zero]
  exact e.logFormsWedge_self_eq_zero_of_le hI hlog inf_le_right _

end AlgebraicGeometry.Scheme.Hom
