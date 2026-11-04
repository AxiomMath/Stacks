module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwistRelative
public import StacksFrontier.AlgebraicGeometry.TensorPowerTrivialize.GeneralModule

/-!
# The comparison of graded rings of sections attached to a local section of a twisting module

Let `𝒜` be a sheaf of graded algebras on a scheme `S`, `ℒ` an invertible `𝒪_S`-module and
`ℬ = twist 𝒜 ℒ`, with `ℬ_d = 𝒜_d ⊗_{𝒪_S} ℒ^{⊗ d}`. A section `x` of `ℒ` over an open `V` of `S`
induces a homomorphism of graded rings of sections `𝒜(V) → ℬ(V)`, given in degree `d` by
`a ↦ a ⊗ x^d`. It is bijective in every degree `d` in which `x^d` trivializes `ℒ^{⊗ d}` over `V`,
and when `x` is the value of a global section of `ℒ` it is the homomorphism of graded rings of
sections induced by the comparison `psi` of that global section.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.powSecAt`: the `d`-th power of a section of
  the twisting module over one open, as a section of `ℒ^{⊗ d}` over that open.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.psiPieceAt`: the comparison on degree-`d`
  homogeneous sections, `a ↦ a ⊗ x^d`.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.psiSectionAt`: the comparison homomorphism of
  graded rings of sections attached to a section of the twisting module over an open of the base.

## Main results

* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.heq_powSecAt_mul`: the powers of a local
  section multiply. The two sides sit in the degrees `(i : ℤ) + (j : ℤ)` and `((i + j : ℕ) : ℤ)`,
  which are only propositionally equal, so the identity is heterogeneous.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.psiPieceAt_mul` and `psiPieceAt_one`: the
  comparison is multiplicative and preserves the unit.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.bijective_psiPieceAt`: the comparison is
  bijective on sections in a degree whose tensor power the section trivializes.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.psiSectionAt_eval`: for the value over `V` of
  a global section of `ℒ`, the comparison is the homomorphism of graded rings of sections attached
  to `psi`.

## References

* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
* [Stacks Project, Tag 02NB](https://stacks.math.columbia.edu/tag/02NB)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.SheafOfModules
open Stacks.SheafOfModules.TensorSheafification (structureSheaf)
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.GradedAlgebraTwist

universe u

namespace Stacks.AlgebraicGeometry.RelativeInvertibleTwist

variable {S : Scheme.{u}} (L : S.Modules)
  [Stacks.SheafOfModules.IsInvertible S.sheaf.obj S.ringCatSheaf.property L]

/-- The `d`-th power of a local section of the twisting module over a fixed open, as a local
section of the `d`-th tensor power over that open. -/
def powSecAt (U : (Opens S)ᵒᵖ) (x : (tp L 1).val.obj U) :
    ∀ d : ℕ, (tp L (d : ℤ)).val.obj U
  | 0 => (TensorPower.oneSection S.sheaf.obj S.ringCatSheaf.property L).eval U
  | (d + 1) => (reix L (succ_cast d)).hom.val.app U
      ((lmul L (d : ℤ) 1).app U (powSecAt U x d) x)

/-- The zeroth power of a local section is the unit section. -/
theorem powSecAt_zero (U : (Opens S)ᵒᵖ) (x : (tp L 1).val.obj U) :
    powSecAt L U x 0 =
      (TensorPower.oneSection S.sheaf.obj S.ringCatSheaf.property L).eval U := rfl

/-- The `(d + 1)`-st power of a local section is its `d`-th power multiplied by the section. -/
theorem powSecAt_succ (U : (Opens S)ᵒᵖ) (x : (tp L 1).val.obj U) (d : ℕ) :
    powSecAt L U x (d + 1) = (reix L (succ_cast d)).hom.val.app U
      ((lmul L (d : ℤ) 1).app U (powSecAt L U x d) x) := rfl

/-- The powers of a local section multiply. -/
theorem heq_powSecAt_mul (U : (Opens S)ᵒᵖ) (x : (tp L 1).val.obj U) :
    ∀ i j : ℕ, HEq ((lmul L (i : ℤ) (j : ℤ)).app U (powSecAt L U x i) (powSecAt L U x j))
      (powSecAt L U x (i + j)) := by
  intro i j
  induction j with
  | zero =>
      exact TensorPower.mulBilinear_mul_one S.sheaf.obj S.ringCatSheaf.property L
        (i : ℤ) U (powSecAt L U x i)
  | succ j ih =>
      have hstep : HEq (powSecAt L U x (j + 1))
          ((lmul L (j : ℤ) 1).app U (powSecAt L U x j) x) := by
        rw [powSecAt_succ]
        exact heq_reix L (succ_cast j) U _
      refine HEq.trans (heq_lmul L U (rfl : (i : ℤ) = (i : ℤ)) (succ_cast j).symm
        (HEq.refl (powSecAt L U x i)) hstep) ?_
      refine HEq.trans (TensorPower.mulBilinear_assoc S.sheaf.obj S.ringCatSheaf.property L
        (i : ℤ) (j : ℤ) 1 U (powSecAt L U x i) (powSecAt L U x j) x).symm ?_
      refine HEq.trans (heq_lmul L U (by push_cast; ring : (i : ℤ) + (j : ℤ) = ((i + j : ℕ) : ℤ))
        (rfl : (1 : ℤ) = 1) ih (HEq.refl x)) ?_
      exact (((heq_of_eq (powSecAt_succ L U x (i + j))).trans
        (heq_reix L (succ_cast (i + j)) U _))).symm

variable (𝒜 : SheafGradedAlgebra S)

/-- The comparison on degree-`d` homogeneous sections over an open, attached to a section `x` of
the twisting module over that open: `a ↦ a ⊗ x^d`. -/
def psiPieceAt (V : S.Opens) (x : (tp L 1).val.obj (op V)) (d : ℕ) :
    𝒜.sectionPieces V d →+ (twist 𝒜 L).sectionPieces V d :=
  AddMonoidHom.mk'
    (fun a => tensorSectionsAt S.sheaf.obj S.ringCatSheaf.property (op V) (𝒜.piece (d : ℤ))
      (tp L (d : ℤ)) a (powSecAt L (op V) x d))
    fun a b => tensorSectionsAt_add_left S.sheaf.obj S.ringCatSheaf.property (op V)
      (𝒜.piece (d : ℤ)) (tp L (d : ℤ)) a b (powSecAt L (op V) x d)

/-- The comparison `psiPieceAt` sends a homogeneous section `a` of degree `d` to `a ⊗ x^d`. -/
theorem psiPieceAt_apply (V : S.Opens) (x : (tp L 1).val.obj (op V)) (d : ℕ)
    (a : 𝒜.sectionPieces V d) :
    psiPieceAt L 𝒜 V x d a =
      tensorSectionsAt S.sheaf.obj S.ringCatSheaf.property (op V) (𝒜.piece (d : ℤ))
        (tp L (d : ℤ)) a (powSecAt L (op V) x d) := rfl

/-- The comparison attached to a local section is multiplicative. -/
theorem psiPieceAt_mul (V : S.Opens) (x : (tp L 1).val.obj (op V)) (i j : ℕ)
    (a : 𝒜.sectionPieces V i) (b : 𝒜.sectionPieces V j) :
    psiPieceAt L 𝒜 V x (i + j) ((𝒜.mul (i : ℤ) (j : ℤ)).app V a b) =
      ((twist 𝒜 L).mul (i : ℤ) (j : ℤ)).app V
        (psiPieceAt L 𝒜 V x i a) (psiPieceAt L 𝒜 V x j b) := by
  refine Eq.trans (psiPieceAt_apply L 𝒜 V x (i + j) ((𝒜.mul (i : ℤ) (j : ℤ)).app V a b)) ?_
  refine Eq.trans ?_ (congrArg₂
    (fun s t => mulSection S.sheaf.obj S.ringCatSheaf.property 𝒜.piece
      (mulHom 𝒜) L (i : ℤ) (j : ℤ) (op V) s t)
    (psiPieceAt_apply L 𝒜 V x i a) (psiPieceAt_apply L 𝒜 V x j b)).symm
  refine Eq.trans ?_ (mulSection_pure S.sheaf.obj S.ringCatSheaf.property 𝒜.piece
    (mulHom 𝒜) L (i : ℤ) (j : ℤ) (op V) a (powSecAt L (op V) x i) b
    (powSecAt L (op V) x j)).symm
  refine congrArg₂ (fun s t => tensorSectionsAt S.sheaf.obj S.ringCatSheaf.property (op V)
    (𝒜.piece ((i : ℤ) + (j : ℤ))) (tp L ((i : ℤ) + (j : ℤ))) s t)
    (mulA_eq 𝒜 (i : ℤ) (j : ℤ) (op V) a b).symm ?_
  refine Eq.trans (eq_of_heq (heq_powSecAt_mul L (op V) x i j)).symm ?_
  exact (coherentMulIso_app_eq_mulBilinear S.sheaf.obj S.ringCatSheaf.property L
    (i : ℤ) (j : ℤ) (op V) (powSecAt L (op V) x i) (powSecAt L (op V) x j)).symm

/-- The comparison attached to a local section carries the unit to the unit. -/
theorem psiPieceAt_one (V : S.Opens) (x : (tp L 1).val.obj (op V)) :
    psiPieceAt L 𝒜 V x 0 (𝒜.one V) = (twist 𝒜 L).one V := by
  refine Eq.trans (psiPieceAt_apply L 𝒜 V x 0 (𝒜.one V)) ?_
  refine Eq.trans ?_ (oneSec_def S.sheaf.obj S.ringCatSheaf.property 𝒜.piece L
    (oneHom 𝒜) (op V)).symm
  exact congrArg (fun s => tensorSectionsAt S.sheaf.obj S.ringCatSheaf.property (op V)
    (𝒜.piece 0) (tp L 0) s
    ((TensorPower.oneSection S.sheaf.obj S.ringCatSheaf.property L).eval (op V)))
    (oneHom_app 𝒜 (op V)).symm

/-- The homomorphism of the graded rings of sections induced by a local section of the twisting
module. -/
def psiSectionRingAt (V : S.Opens) (x : (tp L 1).val.obj (op V)) :
    𝒜.sectionRing V →+* (twist 𝒜 L).sectionRing V :=
  DirectSum.toSemiring
    (fun n => (DirectSum.of ((twist 𝒜 L).sectionPieces V) n).comp (psiPieceAt L 𝒜 V x n))
    ((congrArg (DirectSum.of ((twist 𝒜 L).sectionPieces V) 0)
      (psiPieceAt_one L 𝒜 V x)).trans (DirectSum.one_def _).symm)
    (fun {i j} a b => by
      simp only [AddMonoidHom.coe_comp, Function.comp_apply]
      rw [DirectSum.of_mul_of]
      exact congrArg (DirectSum.of ((twist 𝒜 L).sectionPieces V) (i + j))
        (psiPieceAt_mul L 𝒜 V x i j a b))

/-- On the summand of degree `n`, `psiSectionRingAt` is the degree-`n` comparison `psiPieceAt`. -/
theorem psiSectionRingAt_of (V : S.Opens) (x : (tp L 1).val.obj (op V)) {n : ℕ}
    (a : 𝒜.sectionPieces V n) :
    psiSectionRingAt L 𝒜 V x (DirectSum.of (𝒜.sectionPieces V) n a) =
      DirectSum.of ((twist 𝒜 L).sectionPieces V) n (psiPieceAt L 𝒜 V x n a) :=
  DirectSum.toSemiring_of _ _ _ n a

/-- The comparison homomorphism of graded rings of sections attached to a section of the twisting
module over an open of the base. -/
def psiSectionAt (V : S.Opens) (x : (tp L 1).val.obj (op V)) :
    𝒜.grading V →+*ᵍ (twist 𝒜 L).grading V where
  __ := psiSectionRingAt L 𝒜 V x
  map_mem := fun {_ _} hx => by
    obtain ⟨y, rfl⟩ := hx
    exact ⟨_, (psiSectionRingAt_of L 𝒜 V x y).symm⟩

/-- On the summand of degree `n`, `psiSectionAt` is the degree-`n` comparison `psiPieceAt`. -/
theorem psiSectionAt_of (V : S.Opens) (x : (tp L 1).val.obj (op V)) {n : ℕ}
    (a : 𝒜.sectionPieces V n) :
    psiSectionAt L 𝒜 V x (DirectSum.of (𝒜.sectionPieces V) n a) =
      DirectSum.of ((twist 𝒜 L).sectionPieces V) n (psiPieceAt L 𝒜 V x n a) :=
  psiSectionRingAt_of L 𝒜 V x a

/-! ### Bijectivity in a degree whose tensor power the section trivializes -/

/-- The comparison in degree `d` is bijective on sections over `V` as soon as the `d`-th tensor
power of the twisting module is trivialized over `V` by the `d`-th power of the section. -/
theorem bijective_psiPieceAt (V : S.Opens) (x : (tp L 1).val.obj (op V)) (d : ℕ)
    (e : (tp L (d : ℤ)).over V ≅ SheafOfModules.unit
      (Stacks.SheafOfModules.SliceRestriction.sliceStructureSheaf
        S.sheaf.obj S.ringCatSheaf.property V))
    (he : Stacks.SheafOfModules.TensorGenerator.generator S.sheaf.obj S.ringCatSheaf.property V
      (tp L (d : ℤ)) e = powSecAt L (op V) x d) :
    Function.Bijective (psiPieceAt L 𝒜 V x d) := by
  have hfun : ∀ t : 𝒜.sectionPieces V d, psiPieceAt L 𝒜 V x d t =
      Stacks.SheafOfModules.TensorGenerator.tensorSectionsEquiv S.sheaf.obj
        S.ringCatSheaf.property V (𝒜.piece (d : ℤ)) (tp L (d : ℤ)) e t := fun t =>
    (psiPieceAt_apply L 𝒜 V x d t).trans
      ((congrArg (fun z => tensorSectionsAt S.sheaf.obj S.ringCatSheaf.property (op V)
          (𝒜.piece (d : ℤ)) (tp L (d : ℤ)) t z) he.symm).trans
        (Stacks.SheafOfModules.TensorGenerator.tensorSectionsEquiv_apply S.sheaf.obj
          S.ringCatSheaf.property V (𝒜.piece (d : ℤ)) (tp L (d : ℤ)) e t).symm)
  have hbij := (Stacks.SheafOfModules.TensorGenerator.tensorSectionsEquiv S.sheaf.obj
    S.ringCatSheaf.property V (𝒜.piece (d : ℤ)) (tp L (d : ℤ)) e).bijective
  refine ⟨fun a b hab => hbij.injective ((hfun a).symm.trans (hab.trans (hfun b))), fun y => ?_⟩
  obtain ⟨a, ha⟩ := hbij.surjective y
  exact ⟨a, (hfun a).trans ha⟩

/-! ### Agreement with the comparison attached to a global section -/

/-- The powers of the value of a global section are the values of its powers. -/
theorem powSecAt_eval (ℓ : (tp L 1).sections) (U : (Opens S)ᵒᵖ) :
    ∀ d : ℕ, powSecAt L U (ℓ.eval U) d = (powSec L ℓ d).eval U
  | 0 => rfl
  | (d + 1) => by
      refine Eq.trans (powSecAt_succ L U (ℓ.eval U) d) ?_
      refine Eq.trans ?_ (powSec_succ_eval L ℓ d U).symm
      exact congrArg (fun z => (reix L (succ_cast d)).hom.val.app U
        ((lmul L (d : ℤ) 1).app U z (ℓ.eval U))) (powSecAt_eval ℓ U d)

/-- The comparison attached to the value over `V` of a global section `ℓ` is the map on degree-`d`
sections over `V` of the comparison `psi` induced by `ℓ`. -/
theorem psiPieceAt_eval (ℓ : (tp L 1).sections) (V : S.Opens) (d : ℕ)
    (a : 𝒜.sectionPieces V d) :
    psiPieceAt L 𝒜 V (ℓ.eval (op V)) d a = (psi L 𝒜 ℓ).sectionPieceHom V d a :=
  (psiPieceAt_apply L 𝒜 V (ℓ.eval (op V)) d a).trans
    ((congrArg (fun z => tensorSectionsAt S.sheaf.obj S.ringCatSheaf.property (op V)
        (𝒜.piece (d : ℤ)) (tp L (d : ℤ)) a z) (powSecAt_eval L ℓ (op V) d)).trans
      (psiNat_app L 𝒜 ℓ d (op V) a).symm)

/-- The comparison attached to the value over `V` of a global section `ℓ` is the homomorphism of
graded rings of sections over `V` induced by the comparison `psi` of `ℓ`. -/
theorem psiSectionAt_eval (ℓ : (tp L 1).sections) (V : S.Opens) :
    psiSectionAt L 𝒜 V (ℓ.eval (op V)) = (psi L 𝒜 ℓ).sectionHom V := by
  refine GradedRingHom.ext fun z => ?_
  induction z using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero]
  | of n y =>
      refine (psiSectionAt_of L 𝒜 V (ℓ.eval (op V)) y).trans ?_
      refine Eq.trans ?_ ((psi L 𝒜 ℓ).sectionHom_of V y).symm
      exact congrArg (DirectSum.of ((twist 𝒜 L).sectionPieces V) n)
        (psiPieceAt_eval L 𝒜 ℓ V n y)
  | add z w hz hw => rw [map_add, map_add, hz, hw]

end Stacks.AlgebraicGeometry.RelativeInvertibleTwist

end
