module

public import StacksFrontier.AlgebraicGeometry.TwistTensor.ThetaGlobal

/-!
# Multiplicativity of the comparison `𝒪_X(d)^{⊗ n} ≅ 𝒪_X(dn)` on all of `Proj S`

Let `S = ⨁_{k ≥ 0} 𝒮 k` be a graded ring covered in degree one (Tag 01MT's hypothesis) and
`X = Proj S`. `Stacks.AlgebraicGeometry.ThetaGlobal.theta` is the comparison
`𝒪_X(d)^{⊗ n} ≅ 𝒪_X(dn)` on the whole of `X`, built by recursion on `n`. This file proves that
the family is **multiplicative in an arbitrary bidegree**: the addition law of the tensor powers
of Tag 01CU followed by the comparison in degree `n + m` is the comparisons in degrees `n` and `m`
on the two factors followed by the canonical multiplication map of Equation 01MO at `(dn, dm)`.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01MO](https://stacks.math.columbia.edu/tag/01MO)
* [Stacks Project, Tag 01MT](https://stacks.math.columbia.edu/tag/01MT)
* [Stacks Project, Tag 03GM](https://stacks.math.columbia.edu/tag/03GM)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.Ample
open Stacks.RelativeVeryAmple

namespace Stacks.AlgebraicGeometry.ThetaGlobalMul

universe u w

open Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover (DegreeOneCover)
open Stacks.AlgebraicGeometry.ThetaGlobal

attribute [local instance] Stacks.AlgebraicGeometry.ThetaMul.schemeMonoidal
  Stacks.AlgebraicGeometry.ThetaMul.strictSchemeMonoidal

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮] (hcover : DegreeOneCover 𝒮) (d : ℕ)

/-! ### The canonical multiplication map, at the spelling the comparison family is written in -/

/-- The canonical multiplication map `𝒪_X(a) ⊗ 𝒪_X(b) ⟶ 𝒪_X(a + b)` of Equation 01MO, with its
source ascribed at the tensor product of
`Stacks.AlgebraicGeometry.ThetaMul.schemeMonoidal` — the monoidal structure the comparison family
and the addition law of the tensor powers are written against. The body is
`Stacks.AlgebraicGeometry.TwistTensor.twistMul`; the ascription is the whole content, and this is
the one place the two spellings of the tensor product are identified. -/
def twistMulHom (a b : ℤ) : twist 𝒮 a ⊗ twist 𝒮 b ⟶ twist 𝒮 (a + b) :=
  Stacks.AlgebraicGeometry.TwistTensor.twistMul 𝒮 a b

/-- **The retyping changes no term.** -/
theorem twistMulHom_eq (a b : ℤ) :
    twistMulHom 𝒮 a b = Stacks.AlgebraicGeometry.TwistTensor.twistMul 𝒮 a b := rfl

/-- **The multiplication isomorphism of `ThetaGlobal` is the canonical multiplication map
followed by the transport along `dn + dm = d(n + m)`.** -/
theorem twistMulIso_hom (n m : ℤ) :
    (twistMulIso 𝒮 hcover d n m).hom =
      twistMulHom 𝒮 ((d : ℤ) * n) ((d : ℤ) * m) ≫
        eqToHom (congrArg (twist 𝒮)
          (show (d : ℤ) * n + (d : ℤ) * m = (d : ℤ) * (n + m) from by ring)) := rfl

/-- **Associativity of the canonical multiplication map with every degree sum carried along a
transport.** This is the form in which a consumer whose degrees are written `d * n`, `d * m`,
`d * k` meets associativity: the inner sums `a + b` and `b + c` are replaced by arbitrary degrees
`a'`, `b'` equal to them, both outer sums are carried to a common degree `e`, and all four
hypotheses are then `by ring`.

The input is `Stacks.AlgebraicGeometry.TwistTensor.twistMul_assoc`, which holds in arbitrary
integer degrees over an arbitrary graded ring with no hypothesis in the style of Tag 01MU. -/
theorem twistMulHom_assoc_transport {a b c a' b' e : ℤ} (ha : a + b = a') (hb : b + c = b')
    (h₁ : a' + c = e) (h₂ : a + b' = e) :
    (twistMulHom 𝒮 a b ≫ eqToHom (congrArg (twist 𝒮) ha)) ▷ twist 𝒮 c ≫
        (twistMulHom 𝒮 a' c ≫ eqToHom (congrArg (twist 𝒮) h₁)) =
      (α_ (twist 𝒮 a) (twist 𝒮 b) (twist 𝒮 c)).hom ≫
        twist 𝒮 a ◁ (twistMulHom 𝒮 b c ≫ eqToHom (congrArg (twist 𝒮) hb)) ≫
          (twistMulHom 𝒮 a b' ≫ eqToHom (congrArg (twist 𝒮) h₂)) := by
  subst ha
  subst hb
  subst h₁
  simp only [eqToHom_refl, Category.comp_id]
  exact Stacks.AlgebraicGeometry.TwistTensor.twistMul_assoc 𝒮 a b c

/-- **Associativity of the canonical multiplication isomorphism on `Proj S`**, read at the
spelling `Stacks.AlgebraicGeometry.ThetaGlobal.twistMulIso` is stated in and against the
associator of `Stacks.AlgebraicGeometry.ThetaMul.schemeMonoidal` — the same monoidal structure
`Stacks.AlgebraicGeometry.ThetaMul.tensorPowModuleAddIso_assoc` is stated at. -/
theorem twistMulIso_assoc (n m k : ℤ) :
    (twistMulIso 𝒮 hcover d n m).hom ▷ twist 𝒮 ((d : ℤ) * k) ≫
        (twistMulIso 𝒮 hcover d (n + m) k).hom =
      (α_ (twist 𝒮 ((d : ℤ) * n)) (twist 𝒮 ((d : ℤ) * m)) (twist 𝒮 ((d : ℤ) * k))).hom ≫
        twist 𝒮 ((d : ℤ) * n) ◁ (twistMulIso 𝒮 hcover d m k).hom ≫
          (twistMulIso 𝒮 hcover d n (m + k)).hom ≫
            eqToHom (congrArg (twist 𝒮)
              (show (d : ℤ) * (n + (m + k)) = (d : ℤ) * (n + m + k) from by ring)) := by
  rw [twistMulIso_hom, twistMulIso_hom, twistMulIso_hom, twistMulIso_hom, Category.assoc,
    eqToHom_trans]
  exact twistMulHom_assoc_transport 𝒮 (by ring) (by ring) (by ring) (by ring)

/-! ### The two unit laws -/

/-- The unit `𝒪_X ⟶ 𝒪_X(0)` of the twists, as a morphism out of the monoidal unit of
`Stacks.AlgebraicGeometry.ThetaMul.schemeMonoidal`. The body is the inverse of
`Stacks.AlgebraicGeometry.ThetaGlobal.twistZeroIsoUnit`, so the unit laws below are statements
about the very isomorphism the comparison family is built from in degree zero, and no second
identification of `𝒪_X(0)` with `𝒪_X` enters. -/
def twistUnitHom : 𝟙_ (AlgebraicGeometry.Proj 𝒮).Modules ⟶ twist 𝒮 0 :=
  (twistZeroIsoUnit 𝒮).inv

/-- **The retyping changes no term**: this is
`Stacks.AlgebraicGeometry.TwistTensor.twistUnit`. -/
theorem twistUnitHom_eq :
    twistUnitHom 𝒮 = Stacks.AlgebraicGeometry.TwistTensor.twistUnit 𝒮 := rfl

/-- **The left unit law of the canonical multiplication map on `Proj S`**, at the spelling the
comparison family is written in: the unit whiskered into `𝒪_X(b)` on the right and multiplied is
the left unitor of Tag 01CA, followed by the transport along `b = 0 + b`.

This is `Stacks.AlgebraicGeometry.TwistTensor.one_twistMul`, given as a term: the crossing of the
two spellings of the tensor product is made by `:=`, which tolerates definitional equality,
whereas a `rw` whose motive spans them is not type-correct at `implicit` transparency. -/
theorem twistMulHom_one_left (b : ℤ) :
    twistUnitHom 𝒮 ▷ twist 𝒮 b ≫ twistMulHom 𝒮 0 b =
      (λ_ (twist 𝒮 b)).hom ≫ eqToHom (congrArg (twist 𝒮) (zero_add b).symm) :=
  Stacks.AlgebraicGeometry.TwistTensor.one_twistMul 𝒮 b

/-- **The right unit law of the canonical multiplication map on `Proj S`**, at the same spelling.
This is `Stacks.AlgebraicGeometry.TwistTensor.twistMul_one`, given as a term for the same
reason. -/
theorem twistMulHom_one_right (a : ℤ) :
    twist 𝒮 a ◁ twistUnitHom 𝒮 ≫ twistMulHom 𝒮 a 0 =
      (ρ_ (twist 𝒮 a)).hom ≫ eqToHom (congrArg (twist 𝒮) (add_zero a).symm) :=
  Stacks.AlgebraicGeometry.TwistTensor.twistMul_one 𝒮 a

/-- **The left unit law with every degree carried along a transport**: the zero degree is replaced
by an arbitrary degree `a` equal to it, the sum `a + b` by an arbitrary degree `e`, and all three
hypotheses are then `by ring`. -/
theorem twistMulHom_one_left_transport {a b e : ℤ} (ha : (0 : ℤ) = a) (h₁ : a + b = e)
    (h₂ : b = e) :
    (twistUnitHom 𝒮 ≫ eqToHom (congrArg (twist 𝒮) ha)) ▷ twist 𝒮 b ≫
        (twistMulHom 𝒮 a b ≫ eqToHom (congrArg (twist 𝒮) h₁)) =
      (λ_ (twist 𝒮 b)).hom ≫ eqToHom (congrArg (twist 𝒮) h₂) := by
  subst ha
  subst h₂
  simp only [eqToHom_refl, Category.comp_id]
  rw [← Category.assoc, twistMulHom_one_left, Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.comp_id]

/-- **The right unit law with every degree carried along a transport**, the mirror of
`twistMulHom_one_left_transport`. -/
theorem twistMulHom_one_right_transport {a b e : ℤ} (hb : (0 : ℤ) = b) (h₁ : a + b = e)
    (h₂ : a = e) :
    twist 𝒮 a ◁ (twistUnitHom 𝒮 ≫ eqToHom (congrArg (twist 𝒮) hb)) ≫
        (twistMulHom 𝒮 a b ≫ eqToHom (congrArg (twist 𝒮) h₁)) =
      (ρ_ (twist 𝒮 a)).hom ≫ eqToHom (congrArg (twist 𝒮) h₂) := by
  subst hb
  subst h₂
  simp only [eqToHom_refl, Category.comp_id]
  rw [← Category.assoc, twistMulHom_one_right, Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.comp_id]

/-- **The left unit law of the canonical multiplication isomorphism on `Proj S`**, read at the
spelling `Stacks.AlgebraicGeometry.ThetaGlobal.twistMulIso` is stated in and against the left
unitor of `Stacks.AlgebraicGeometry.ThetaMul.schemeMonoidal`: the inverse of
`Stacks.AlgebraicGeometry.ThetaGlobal.twistZeroIsoUnit`, transported to degree `d · 0`, whiskered
into `𝒪_X(dm)` and multiplied, is that left unitor. -/
theorem twistMulIso_zero_left (m : ℤ) :
    ((twistZeroIsoUnit 𝒮).inv ≫
          eqToHom (congrArg (twist 𝒮) (show (0 : ℤ) = (d : ℤ) * 0 from by ring))) ▷
          twist 𝒮 ((d : ℤ) * m) ≫
        (twistMulIso 𝒮 hcover d 0 m).hom =
      (λ_ (twist 𝒮 ((d : ℤ) * m))).hom ≫
        eqToHom (congrArg (twist 𝒮) (show (d : ℤ) * m = (d : ℤ) * (0 + m) from by ring)) := by
  rw [twistMulIso_hom]
  exact twistMulHom_one_left_transport 𝒮 (by ring) (by ring) (by ring)

/-- **The right unit law of the canonical multiplication isomorphism on `Proj S`**, the mirror of
`twistMulIso_zero_left`: the inverse of
`Stacks.AlgebraicGeometry.ThetaGlobal.twistZeroIsoUnit`, transported to degree `d · 0`, whiskered
into `𝒪_X(dn)` on the left and multiplied, is the right unitor. -/
theorem twistMulIso_zero_right (n : ℤ) :
    twist 𝒮 ((d : ℤ) * n) ◁
          ((twistZeroIsoUnit 𝒮).inv ≫
            eqToHom (congrArg (twist 𝒮) (show (0 : ℤ) = (d : ℤ) * 0 from by ring))) ≫
        (twistMulIso 𝒮 hcover d n 0).hom =
      (ρ_ (twist 𝒮 ((d : ℤ) * n))).hom ≫
        eqToHom (congrArg (twist 𝒮) (show (d : ℤ) * n = (d : ℤ) * (n + 0) from by ring)) := by
  rw [twistMulIso_hom]
  exact twistMulHom_one_right_transport 𝒮 (by ring) (by ring) (by ring)

/-! ### The multiplicativity square in a full bidegree -/

variable [IsInvertibleModule (AlgebraicGeometry.Proj 𝒮) (twist 𝒮 (d : ℤ))]

/-- **The degree one value of the comparison family is the canonical identification of the first
tensor power**: `Stacks.AlgebraicGeometry.ThetaGlobal.theta 𝒮 hcover d 1` is
`Stacks.AlgebraicGeometry.ThetaGlobal.twistOneIso 𝒮 d`.

By the recursion, the degree one value is built out of the degree zero one, which is the canonical
`𝒪_X(d)^{⊗ 0} ≅ 𝒪_X ≅ 𝒪_X(0)`. The two unit laws
`Stacks.AlgebraicGeometry.ThetaMul.tensorPowModuleAddIso_zero_left` and `twistMulIso_zero_left`
say that the two multiplications agree with the left unitor of Stacks Tag 01CA on that
identification, which pins the degree one value down. -/
theorem theta_one_eq : theta 𝒮 hcover d 1 = twistOneIso 𝒮 d :=
  Iso.ext
    (Stacks.AlgebraicGeometry.ThetaMul.unit_tensorHom_cancel
      (tensorPowModuleZeroIso (AlgebraicGeometry.Proj 𝒮) (twist 𝒮 (d : ℤ))).hom
      ((twistZeroIsoUnit 𝒮).inv ≫
        eqToHom (congrArg (twist 𝒮) (show (0 : ℤ) = (d : ℤ) * 0 from by ring)))
      (twistOneIso 𝒮 d).hom
      (tensorModulesMapIso (AlgebraicGeometry.Proj 𝒮) (theta 𝒮 hcover d 0)
        (twistOneIso 𝒮 d)).hom
      (twistMulIso 𝒮 hcover d 0 1).hom
      (eqToHom (congrArg (twist 𝒮)
        (show (d : ℤ) * ((0 : ℤ) + 1) = (d : ℤ) * (((0 + 1 : ℕ)) : ℤ) from by push_cast; ring)))
      (eqToHom (congrArg (twist 𝒮) (show (d : ℤ) * 1 = (d : ℤ) * (0 + 1) from by ring)))
      (thetaStep 𝒮 d 0).inv (thetaStep 𝒮 d 0).hom
      ((Stacks.AlgebraicGeometry.ThetaMul.tensorModulesMapIso_hom (AlgebraicGeometry.Proj 𝒮)
          (theta 𝒮 hcover d 0) (twistOneIso 𝒮 d)).trans
        (congrArg (fun φ ↦ φ ⊗ₘ (twistOneIso 𝒮 d).hom)
          (rfl : (theta 𝒮 hcover d 0).hom = _)))
      (twistMulIso_zero_left 𝒮 hcover d 1)
      (by rw [eqToHom_trans]; rfl)
      (Stacks.AlgebraicGeometry.ThetaMul.tensorPowModuleAddIso_zero_left
        (AlgebraicGeometry.Proj 𝒮) (twist 𝒮 (d : ℤ)) 1)
      (thetaStep 𝒮 d 0).inv_hom_id)

/-- **The addition law of the tensor powers of `𝒪_X(d)` in a pair of natural-number exponents**,
`𝒪_X(d)^{⊗ n} ⊗ 𝒪_X(d)^{⊗ m} ≅ 𝒪_X(d)^{⊗ (n+m)}`. The body is `Stacks.Ample.tensorPowModuleAddIso`;
the ascription spells the source with the tensor product of
`Stacks.AlgebraicGeometry.ThetaMul.schemeMonoidal` and the target exponent as the natural number
`n + m`, which is how the comparison family is indexed. At `m = 1` this is
`Stacks.AlgebraicGeometry.ThetaGlobal.thetaStep`. -/
def thetaStepNat (n m : ℕ) :
    tensorPowModule (AlgebraicGeometry.Proj 𝒮) (twist 𝒮 (d : ℤ)) (n : ℤ) ⊗
        tensorPowModule (AlgebraicGeometry.Proj 𝒮) (twist 𝒮 (d : ℤ)) (m : ℤ) ≅
      tensorPowModule (AlgebraicGeometry.Proj 𝒮) (twist 𝒮 (d : ℤ)) ((n + m : ℕ) : ℤ) :=
  tensorPowModuleAddIso (AlgebraicGeometry.Proj 𝒮) (twist 𝒮 (d : ℤ)) (n : ℤ) (m : ℤ)

/-- **The canonical multiplication isomorphism on `Proj S` in a pair of natural-number degrees**,
`𝒪_X(dn) ⊗ 𝒪_X(dm) ≅ 𝒪_X(d(n+m))`. The body is
`Stacks.AlgebraicGeometry.ThetaGlobal.twistMulIso`; the ascription spells the target degree with
the natural number `n + m`. -/
def twistMulIsoNat (n m : ℕ) :
    twist 𝒮 ((d : ℤ) * (n : ℤ)) ⊗ twist 𝒮 ((d : ℤ) * (m : ℤ)) ≅
      twist 𝒮 ((d : ℤ) * ((n + m : ℕ) : ℤ)) :=
  twistMulIso 𝒮 hcover d (n : ℤ) (m : ℤ)

/-- The associativity constraint of the addition law in the bidegrees `(n, m)` and `(n + m, 1)`,
at the natural-number spelling. This is
`Stacks.AlgebraicGeometry.ThetaMul.tensorPowModuleAddIso_assoc` with the transport along
`n + (m + 1) = n + m + 1` removed: in the third degree `1` its two ends are the same object. -/
theorem thetaStepNat_assoc (n m : ℕ) :
    (thetaStepNat 𝒮 d n m).hom ▷
        tensorPowModule (AlgebraicGeometry.Proj 𝒮) (twist 𝒮 (d : ℤ)) (((1 : ℕ)) : ℤ) ≫
        (thetaStepNat 𝒮 d (n + m) 1).hom =
      (α_ _ _ _).hom ≫
        tensorPowModule (AlgebraicGeometry.Proj 𝒮) (twist 𝒮 (d : ℤ)) (n : ℤ) ◁
            (thetaStepNat 𝒮 d m 1).hom ≫
          (thetaStepNat 𝒮 d n (m + 1)).hom :=
  (Stacks.AlgebraicGeometry.ThetaMul.tensorPowModuleAddIso_assoc (AlgebraicGeometry.Proj 𝒮)
      (twist 𝒮 (d : ℤ)) n m 1).trans
    (Stacks.AlgebraicGeometry.ThetaMul.comp_comp_comp_eq_self _ _ _ _ rfl)

omit [IsInvertibleModule (AlgebraicGeometry.Proj 𝒮) (twist 𝒮 (d : ℤ))] in
/-- The associativity constraint of the canonical multiplication in the same two bidegrees. This
is `twistMulIso_assoc` with the transport along `d(n + (m + 1)) = d(n + m + 1)` removed. -/
theorem twistMulIsoNat_assoc (n m : ℕ) :
    (twistMulIsoNat 𝒮 hcover d n m).hom ▷ twist 𝒮 ((d : ℤ) * (((1 : ℕ)) : ℤ)) ≫
        (twistMulIsoNat 𝒮 hcover d (n + m) 1).hom =
      (α_ _ _ _).hom ≫
        twist 𝒮 ((d : ℤ) * (n : ℤ)) ◁ (twistMulIsoNat 𝒮 hcover d m 1).hom ≫
          (twistMulIsoNat 𝒮 hcover d n (m + 1)).hom :=
  (twistMulIso_assoc 𝒮 hcover d (n : ℤ) (m : ℤ) (((1 : ℕ)) : ℤ)).trans
    (Stacks.AlgebraicGeometry.ThetaMul.comp_comp_comp_eq_self _ _ _ _ rfl)

/-- **Multiplicativity of the comparison family in the bidegree `(n, 1)`**, at the spellings
above: `Stacks.AlgebraicGeometry.ThetaGlobal.theta_mul_one` with the degree one factor read as the
degree one value of the family through `theta_one_eq`, the tensor product of the two comparisons
read as a monoidal tensor product of morphisms through
`Stacks.AlgebraicGeometry.ThetaMul.tensorModulesMapIso_hom`, and the two transports absorbed. -/
theorem theta_mul_one_nat (n : ℕ) :
    (thetaStepNat 𝒮 d n 1).hom ≫ (theta 𝒮 hcover d (n + 1)).hom =
      ((theta 𝒮 hcover d n).hom ⊗ₘ (theta 𝒮 hcover d 1).hom) ≫
        (twistMulIsoNat 𝒮 hcover d n 1).hom :=
  (Stacks.AlgebraicGeometry.ThetaMul.comp_cancel_left (thetaStepNat 𝒮 d n 1).hom _ rfl
      (theta 𝒮 hcover d (n + 1)).hom).symm.trans
    ((theta_mul_one 𝒮 hcover d n).trans
      ((Stacks.AlgebraicGeometry.ThetaMul.comp_comp_eq_self _ _ _ rfl).trans
        (congrArg (fun z ↦ z ≫ (twistMulIsoNat 𝒮 hcover d n 1).hom)
          ((Stacks.AlgebraicGeometry.ThetaMul.tensorModulesMapIso_hom
              (AlgebraicGeometry.Proj 𝒮) (theta 𝒮 hcover d n) (twistOneIso 𝒮 d)).trans
            (congrArg (fun e ↦ (theta 𝒮 hcover d n).hom ⊗ₘ Iso.hom e)
              (theta_one_eq 𝒮 hcover d).symm)))))

/-- **Multiplicativity of the comparison family in the bidegree `(n, 0)`**, which is the right
unit law: the degree zero value of the family is the identification `𝒪_X(d)^{⊗ 0} ≅ 𝒪_X ≅ 𝒪_X(0)`,
and the two right unit laws
`Stacks.AlgebraicGeometry.ThetaMul.tensorPowModuleAddIso_zero_right` and
`twistMulIso_zero_right` say that the two multiplications agree with the right unitor of Stacks
Tag 01CA on it. The transport between the two spellings `d · n` and `d · (n + 0)` of the target
degree is an identity. -/
theorem theta_mul_zero_nat (n : ℕ) :
    (thetaStepNat 𝒮 d n 0).hom ≫ (theta 𝒮 hcover d (n + 0)).hom =
      ((theta 𝒮 hcover d n).hom ⊗ₘ (theta 𝒮 hcover d 0).hom) ≫
        (twistMulIsoNat 𝒮 hcover d n 0).hom :=
  (Stacks.AlgebraicGeometry.ThetaMul.comp_comp_eq_self (thetaStepNat 𝒮 d n 0).hom
      (theta 𝒮 hcover d n).hom _ rfl).symm.trans
    (Stacks.AlgebraicGeometry.ThetaMul.tensorHom_unit_square
      (tensorPowModuleZeroIso (AlgebraicGeometry.Proj 𝒮) (twist 𝒮 (d : ℤ))).hom
      ((twistZeroIsoUnit 𝒮).inv ≫
        eqToHom (congrArg (twist 𝒮) (show (0 : ℤ) = (d : ℤ) * 0 from by ring)))
      (theta 𝒮 hcover d n).hom
      ((theta 𝒮 hcover d n).hom ⊗ₘ (theta 𝒮 hcover d 0).hom)
      (twistMulIsoNat 𝒮 hcover d n 0).hom
      (eqToHom (congrArg (twist 𝒮)
        (show (d : ℤ) * (n : ℤ) = (d : ℤ) * ((n : ℤ) + 0) from by ring)))
      (thetaStepNat 𝒮 d n 0).hom
      (congrArg (fun φ ↦ (theta 𝒮 hcover d n).hom ⊗ₘ φ)
        (rfl : (theta 𝒮 hcover d 0).hom = _))
      (twistMulIso_zero_right 𝒮 hcover d (n : ℤ))
      (Stacks.AlgebraicGeometry.ThetaMul.tensorPowModuleAddIso_zero_right
        (AlgebraicGeometry.Proj 𝒮) (twist 𝒮 (d : ℤ)) n))

/-- **Multiplicativity of the comparison family on all of `Proj S` in an arbitrary bidegree
`(n, m)`**: the addition law of the tensor powers followed by the comparison in degree `n + m` is
the comparisons in degrees `n` and `m` on the two factors followed by the canonical multiplication
at `(dn, dm)`. Both degrees are arbitrary natural numbers; in particular the bidegrees `(n, 0)`
and `(0, m)` are included.

By induction on `m`. The base case `m = 0` is the right unit law `theta_mul_zero_nat`; the step is
`Stacks.AlgebraicGeometry.ThetaMul.square_step` fed with the two associativity constraints
`thetaStepNat_assoc` and `twistMulIsoNat_assoc` together with the squares in the bidegrees
`(n, m)`, `(n + m, 1)` and `(m, 1)`. -/
theorem theta_mul (n m : ℕ) :
    (thetaStepNat 𝒮 d n m).hom ≫ (theta 𝒮 hcover d (n + m)).hom =
      ((theta 𝒮 hcover d n).hom ⊗ₘ (theta 𝒮 hcover d m).hom) ≫
        (twistMulIsoNat 𝒮 hcover d n m).hom := by
  induction m with
  | zero => exact theta_mul_zero_nat 𝒮 hcover d n
  | succ k ih =>
      exact Stacks.AlgebraicGeometry.ThetaMul.square_step (thetaStepNat_assoc 𝒮 d n k)
        (twistMulIsoNat_assoc 𝒮 hcover d n k) ih
        (theta_mul_one_nat 𝒮 hcover d (n + k)) (theta_mul_one_nat 𝒮 hcover d k)

/-! ### The Veronese spelling of the degrees -/

/-- **The canonical multiplication isomorphism with the twist degrees spelled as the `d`-th
Veronese section ring spells them**, `𝒪_X(nd) ⊗ 𝒪_X(md) ≅ 𝒪_X((n+m)d)`. This is `twistMulIsoNat`
conjugated by the transports along `nd = dn`. -/
def twistMulIsoVeronese (n m : ℕ) :
    twist 𝒮 ((n * d : ℕ) : ℤ) ⊗ twist 𝒮 ((m * d : ℕ) : ℤ) ≅
      twist 𝒮 (((n + m) * d : ℕ) : ℤ) :=
  (eqToIso (congrArg (twist 𝒮)
        (show ((n * d : ℕ) : ℤ) = (d : ℤ) * (n : ℤ) from by push_cast; ring)) ⊗ᵢ
      eqToIso (congrArg (twist 𝒮)
        (show ((m * d : ℕ) : ℤ) = (d : ℤ) * (m : ℤ) from by push_cast; ring))) ≪≫
    twistMulIsoNat 𝒮 hcover d n m ≪≫
    eqToIso (congrArg (twist 𝒮)
      (show (d : ℤ) * ((n + m : ℕ) : ℤ) = (((n + m) * d : ℕ) : ℤ) from by push_cast; ring))

/-- The Veronese spelling of the comparison family is the comparison family followed by the
transport along `dn = nd`. -/
theorem thetaNat_hom (n : ℕ) :
    (thetaNat 𝒮 hcover d n).hom = (theta 𝒮 hcover d n).hom ≫
      eqToHom (congrArg (twist 𝒮)
        (show (d : ℤ) * (n : ℤ) = ((n * d : ℕ) : ℤ) from by push_cast; ring)) :=
  rfl

omit [IsInvertibleModule (AlgebraicGeometry.Proj 𝒮) (twist 𝒮 (d : ℤ))] in
/-- The Veronese spelling of the canonical multiplication, unfolded into its three factors. -/
theorem twistMulIsoVeronese_hom (n m : ℕ) :
    (twistMulIsoVeronese 𝒮 hcover d n m).hom =
      (eqToHom (congrArg (twist 𝒮)
            (show ((n * d : ℕ) : ℤ) = (d : ℤ) * (n : ℤ) from by push_cast; ring)) ⊗ₘ
          eqToHom (congrArg (twist 𝒮)
            (show ((m * d : ℕ) : ℤ) = (d : ℤ) * (m : ℤ) from by push_cast; ring))) ≫
        (twistMulIsoNat 𝒮 hcover d n m).hom ≫
          eqToHom (congrArg (twist 𝒮)
            (show (d : ℤ) * ((n + m : ℕ) : ℤ) = (((n + m) * d : ℕ) : ℤ) from by
              push_cast; ring)) :=
  rfl

omit [IsInvertibleModule (AlgebraicGeometry.Proj 𝒮) (twist 𝒮 (d : ℤ))] in
/-- The two transports between the degrees `dn` and `nd` cancel. -/
private theorem veronese_eqToHom_cancel (n : ℕ) :
    eqToHom (congrArg (twist 𝒮)
        (show (d : ℤ) * (n : ℤ) = ((n * d : ℕ) : ℤ) from by push_cast; ring)) ≫
      eqToHom (congrArg (twist 𝒮)
        (show ((n * d : ℕ) : ℤ) = (d : ℤ) * (n : ℤ) from by push_cast; ring)) =
      𝟙 (twist 𝒮 ((d : ℤ) * (n : ℤ))) := by
  rw [eqToHom_trans]; rfl

/-- The left-hand side of the multiplicativity square, carried to the Veronese spelling of the
target degree. -/
private theorem thetaNat_mul_left (n m : ℕ)
    (h : (thetaStepNat 𝒮 d n m).hom ≫ (theta 𝒮 hcover d (n + m)).hom =
      ((theta 𝒮 hcover d n).hom ⊗ₘ (theta 𝒮 hcover d m).hom) ≫
        (twistMulIsoNat 𝒮 hcover d n m).hom) :
    (thetaStepNat 𝒮 d n m).hom ≫ (thetaNat 𝒮 hcover d (n + m)).hom =
      ((theta 𝒮 hcover d n).hom ⊗ₘ (theta 𝒮 hcover d m).hom) ≫
        (twistMulIsoNat 𝒮 hcover d n m).hom ≫
          eqToHom (congrArg (twist 𝒮)
            (show (d : ℤ) * ((n + m : ℕ) : ℤ) = (((n + m) * d : ℕ) : ℤ) from by
              push_cast; ring)) := by
  rw [thetaNat_hom, ← Category.assoc, h, Category.assoc]

/-- The right-hand side of the multiplicativity square, carried to the Veronese spelling of the
two source degrees: the four transports cancel in pairs. -/
private theorem thetaNat_mul_right (n m : ℕ) :
    ((theta 𝒮 hcover d n).hom ⊗ₘ (theta 𝒮 hcover d m).hom) ≫
        (twistMulIsoNat 𝒮 hcover d n m).hom ≫
          eqToHom (congrArg (twist 𝒮)
            (show (d : ℤ) * ((n + m : ℕ) : ℤ) = (((n + m) * d : ℕ) : ℤ) from by
              push_cast; ring)) =
      ((thetaNat 𝒮 hcover d n).hom ⊗ₘ (thetaNat 𝒮 hcover d m).hom) ≫
        (twistMulIsoVeronese 𝒮 hcover d n m).hom := by
  rw [thetaNat_hom, thetaNat_hom, twistMulIsoVeronese_hom,
    ← Category.assoc (((theta 𝒮 hcover d n).hom ≫ _) ⊗ₘ ((theta 𝒮 hcover d m).hom ≫ _)),
    MonoidalCategory.tensorHom_comp_tensorHom, Category.assoc (theta 𝒮 hcover d n).hom,
    Category.assoc (theta 𝒮 hcover d m).hom, veronese_eqToHom_cancel, veronese_eqToHom_cancel,
    Category.comp_id, Category.comp_id]

/-- **Multiplicativity of `𝒪_X(d)^{⊗ n} ≅ 𝒪_X(nd)` on all of `Proj S` in an arbitrary bidegree
`(n, m)`**, with every twist degree spelled as the `d`-th Veronese section ring spells it. This is
`theta_mul` with the three degrees carried along the transports `dn = nd`, which cancel against
the ones inside `twistMulIsoVeronese`. As in `theta_mul` both degrees are arbitrary natural
numbers. -/
theorem thetaNat_mul (n m : ℕ) :
    (thetaStepNat 𝒮 d n m).hom ≫ (thetaNat 𝒮 hcover d (n + m)).hom =
      ((thetaNat 𝒮 hcover d n).hom ⊗ₘ (thetaNat 𝒮 hcover d m).hom) ≫
        (twistMulIsoVeronese 𝒮 hcover d n m).hom :=
  (thetaNat_mul_left 𝒮 hcover d n m (theta_mul 𝒮 hcover d n m)).trans
    (thetaNat_mul_right 𝒮 hcover d n m)

end Stacks.AlgebraicGeometry.ThetaGlobalMul

end
