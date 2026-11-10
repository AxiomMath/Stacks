module

public import StacksFrontier.AlgebraicGeometry.GradedAlgebraTwist.Basic
public import StacksFrontier.AlgebraicGeometry.Morphism.TwistAlgebra
public import StacksFrontier.AlgebraicGeometry.Morphism.TwistEventual
public import StacksFrontier.AlgebraicGeometry.ProjTwistGradedAlgebra.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProjMapDomain.EventualBijective

/-!
# The comparison homomorphism of the relative twist

Let `S` be a scheme, `𝒜` a quasi-coherent graded `𝒪_S`-algebra and `ℒ` an invertible
`𝒪_S`-module, with twist `ℬ_d = 𝒜_d ⊗_{𝒪_S} ℒ^{⊗ d}`
(`Stacks.AlgebraicGeometry.GradedAlgebraTwist.twist`). A global section `ℓ` of `ℒ` defines a
homomorphism `ψ : 𝒜 ⟶ ℬ` of graded `𝒪_S`-algebras, `x ↦ x ⊗ ℓ^d` in degree `d`. When `ℓ`
trivializes `ℒ`, the morphism of relative homogeneous spectra induced by `ψ` is defined on all of
`Proj_S(ℬ)`, is an isomorphism onto `Proj_S(𝒜)` over `S`, and the comparison maps of the twisting
sheaves assemble into an isomorphism of graded algebras.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.powSec`: the `d`-th power of a global
  section of `ℒ`, as a global section of `ℒ^{⊗ d}`, formed with the multiplication of the Laurent
  algebra of `ℒ`.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.psiNat` and `psiInt`: the comparison map
  `𝒜_d ⟶ 𝒜_d ⊗ ℒ^{⊗ d}`, `x ↦ x ⊗ ℓ^d`, in a natural-number degree and in an arbitrary integer
  degree.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.psi`: the comparison homomorphism
  `ψ : 𝒜 ⟶ ℬ` of graded quasi-coherent `𝒪_S`-algebras.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.relativeThetaGradedIsoOfTrivialized`: for a
  trivializing `ℓ`, the isomorphism of graded algebras assembled from the comparison maps `θ_n`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.heq_powSec_mul`: the powers of a global
  section multiply.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.psiNat_app`: the comparison map pairs a
  local section of `𝒜_d` with the `d`-th power of `ℓ`.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.relativeComparison_of_trivialized`: for a
  trivializing `ℓ`, the induced morphism `Proj_S(ℬ) ⟶ Proj_S(𝒜)` is everywhere defined, an
  isomorphism and a morphism over `S`, and every `θ_n` is an isomorphism.

## References

* [Stacks Project, Tag 02NB](https://stacks.math.columbia.edu/tag/02NB)
* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
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

/-- The `n`-th integer tensor power of the twisting module. -/
abbrev tp (n : ℤ) : SheafOfModules.{u} (structureSheaf S.sheaf.obj S.ringCatSheaf.property) :=
  TensorPower.tensorPower S.sheaf.obj S.ringCatSheaf.property L n

/-- The multiplication of the Laurent algebra of the twisting module, on local sections. -/
abbrev lmul (n m : ℤ) : (tp L n).BilinearMap (tp L m) (tp L (n + m)) :=
  TensorPower.mulBilinear S.sheaf.obj S.ringCatSheaf.property L n m

/-- Reindexing a tensor power along an equality of exponents. -/
abbrev reix {a b : ℤ} (h : a = b) : tp L a ≅ tp L b :=
  TensorPower.tensorPowerReindex S.sheaf.obj S.ringCatSheaf.property L h

/-- Reindexing a tensor power along an equality of exponents is heterogeneously the identity on
local sections. -/
theorem heq_reix {a b : ℤ} (h : a = b) (U : (Opens S)ᵒᵖ) (x : (tp L a).val.obj U) :
    HEq ((reix L h).hom.val.app U x) x :=
  TensorPower.heq_reindex S.sheaf.obj S.ringCatSheaf.property L U h x

/-- The cast of a successor: `(d : ℤ) + 1 = ((d + 1 : ℕ) : ℤ)`. -/
theorem succ_cast (d : ℕ) : ((d : ℤ) + 1) = ((d + 1 : ℕ) : ℤ) := by push_cast; ring

/-- The `d`-th power of a global section of the twisting module, as a global section of the
`d`-th tensor power. -/
def powSec (ℓ : (tp L 1).sections) : ∀ d : ℕ, (tp L (d : ℤ)).sections
  | 0 => TensorPower.oneSection S.sheaf.obj S.ringCatSheaf.property L
  | (d + 1) =>
      PresheafOfModules.sectionsMk
        (fun U => (reix L (succ_cast d)).hom.val.app U
          ((lmul L (d : ℤ) 1).app U ((powSec ℓ d).eval U) (ℓ.eval U)))
        (fun {_ V} f =>
          (PresheafOfModules.naturality_apply ((reix L (succ_cast d)).hom.val) f _).trans
            (congrArg ((reix L (succ_cast d)).hom.val.app V)
              (((lmul L (d : ℤ) 1).naturality f _ _).trans
                (congrArg₂ (fun x y => (lmul L (d : ℤ) 1).app V x y)
                  (PresheafOfModules.sections_property (powSec ℓ d) f)
                  (PresheafOfModules.sections_property ℓ f)))))

/-- The zeroth power of a global section is the unit section. -/
theorem powSec_zero_eval (ℓ : (tp L 1).sections) (U : (Opens S)ᵒᵖ) :
    (powSec L ℓ 0).eval U =
      (TensorPower.oneSection S.sheaf.obj S.ringCatSheaf.property L).eval U := rfl

/-- The `(d + 1)`-st power of a global section is the `d`-th power multiplied by it, reindexed
along `succ_cast`. -/
theorem powSec_succ_eval (ℓ : (tp L 1).sections) (d : ℕ) (U : (Opens S)ᵒᵖ) :
    (powSec L ℓ (d + 1)).eval U =
      (reix L (succ_cast d)).hom.val.app U
        ((lmul L (d : ℤ) 1).app U ((powSec L ℓ d).eval U) (ℓ.eval U)) := rfl

/-- The `(d + 1)`-st power of a global section is heterogeneously equal to the unreindexed product
of the `d`-th power with it. -/
private theorem heq_powSec_succ_eval (ℓ : (tp L 1).sections) (d : ℕ) (U : (Opens S)ᵒᵖ) :
    HEq ((powSec L ℓ (d + 1)).eval U)
      ((lmul L (d : ℤ) 1).app U ((powSec L ℓ d).eval U) (ℓ.eval U)) :=
  (heq_of_eq (powSec_succ_eval L ℓ d U)).trans (heq_reix L (succ_cast d) U _)

/-- Multiplication in the Laurent algebra respects heterogeneous equality of its two arguments,
once the degrees agree. -/
theorem heq_lmul (U : (Opens S)ᵒᵖ) {a a' b b' : ℤ} (ha : a = a') (hb : b = b')
    {x : (tp L a).val.obj U} {x' : (tp L a').val.obj U} (hx : HEq x x')
    {y : (tp L b).val.obj U} {y' : (tp L b').val.obj U} (hy : HEq y y') :
    HEq ((lmul L a b).app U x y) ((lmul L a' b').app U x' y') := by
  subst ha hb
  rw [eq_of_heq hx, eq_of_heq hy]

/-- **The powers of a global section multiply.** The product in the Laurent algebra of the
`i`-th and the `j`-th power of `ℓ` is its `(i + j)`-th power, as a heterogeneous equality between
the degrees `(i : ℤ) + (j : ℤ)` and `((i + j : ℕ) : ℤ)`. -/
theorem heq_powSec_mul (ℓ : (tp L 1).sections) (U : (Opens S)ᵒᵖ) :
    ∀ i j : ℕ, HEq ((lmul L (i : ℤ) (j : ℤ)).app U
        ((powSec L ℓ i).eval U) ((powSec L ℓ j).eval U))
      ((powSec L ℓ (i + j)).eval U) := by
  intro i j
  induction j with
  | zero =>
      refine HEq.trans ?_ (HEq.refl ((powSec L ℓ i).eval U))
      exact TensorPower.mulBilinear_mul_one S.sheaf.obj S.ringCatSheaf.property L
        (i : ℤ) U ((powSec L ℓ i).eval U)
  | succ j ih =>
      refine HEq.trans (heq_lmul L U (rfl : (i : ℤ) = (i : ℤ)) (succ_cast j).symm
        (HEq.refl ((powSec L ℓ i).eval U)) (heq_powSec_succ_eval L ℓ j U)) ?_
      refine HEq.trans (TensorPower.mulBilinear_assoc S.sheaf.obj S.ringCatSheaf.property L
        (i : ℤ) (j : ℤ) 1 U ((powSec L ℓ i).eval U) ((powSec L ℓ j).eval U) (ℓ.eval U)).symm ?_
      refine HEq.trans (heq_lmul L U (by push_cast; ring : (i : ℤ) + (j : ℤ) = ((i + j : ℕ) : ℤ))
        (rfl : (1 : ℤ) = 1) ih (HEq.refl (ℓ.eval U))) ?_
      exact (heq_powSec_succ_eval L ℓ (i + j) U).symm

/-! ### The comparison homomorphism -/

/-- The morphism `𝒪_S ⟶ ℒ^{⊗ d}` determined by the `d`-th power of `ℓ`. -/
def powHom (ℓ : (tp L 1).sections) (d : ℕ) :
    SheafOfModules.unit (structureSheaf S.sheaf.obj S.ringCatSheaf.property) ⟶ tp L (d : ℤ) :=
  (tp L (d : ℤ)).unitHomEquiv.symm (powSec L ℓ d)

/-- The morphism determined by the `d`-th power of `ℓ` sends the unit section to that power. -/
theorem powHom_app (ℓ : (tp L 1).sections) (d : ℕ) (U : (Opens S)ᵒᵖ) :
    (powHom L ℓ d).val.app U
        (Stacks.AlgebraicGeometry.GradedAlgebraTwist.unitSection
          S.sheaf.obj S.ringCatSheaf.property U) =
      (powSec L ℓ d).eval U :=
  congrArg (fun σ : (tp L (d : ℤ)).sections => σ.val U)
    ((tp L (d : ℤ)).unitHomEquiv.apply_symm_apply (powSec L ℓ d))

/-- **Two morphisms out of the structure sheaf agree as soon as they agree on the unit section
over every open.** -/
theorem unitHom_ext {M : SheafOfModules.{u} (structureSheaf S.sheaf.obj S.ringCatSheaf.property)}
    (f g : SheafOfModules.unit (structureSheaf S.sheaf.obj S.ringCatSheaf.property) ⟶ M)
    (h : ∀ U : (Opens S)ᵒᵖ, f.val.app U
        (Stacks.AlgebraicGeometry.GradedAlgebraTwist.unitSection
          S.sheaf.obj S.ringCatSheaf.property U) =
      g.val.app U (Stacks.AlgebraicGeometry.GradedAlgebraTwist.unitSection
        S.sheaf.obj S.ringCatSheaf.property U)) : f = g :=
  M.unitHomEquiv.injective (PresheafOfModules.sections_ext _ _ h)

/-- **The first power of `ℓ` is `ℓ`.** -/
theorem powSec_one (ℓ : (tp L 1).sections) : powSec L ℓ 1 = ℓ :=
  PresheafOfModules.sections_ext _ _ fun U =>
    eq_of_heq ((heq_powSec_succ_eval L ℓ 0 U).trans
      (TensorPower.mulBilinear_one_mul S.sheaf.obj S.ringCatSheaf.property L 1 U (ℓ.eval U)))

/-! ### Multiplying a sheaf of modules by a global section -/

section MulRight

variable (M A : SheafOfModules.{u} (structureSheaf S.sheaf.obj S.ringCatSheaf.property))

/-- **Multiplication on the right by a global section of `A`**, as a morphism `M ⟶ M ⊗ A`:
write `M` as `M ⊗ 𝒪_S` and tensor the morphism into the second factor. -/
def mulRightHom (s : SheafOfModules.unit (structureSheaf S.sheaf.obj
    S.ringCatSheaf.property) ⟶ A) :
    M ⟶ (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.sheaf.obj,
      Presheaf.isSheaf_of_isSheaf_comp _ (S.sheaf.obj) (forget₂ CommRingCat RingCat)
        (S.ringCatSheaf.property)⟩).obj (M)).obj (A)) :=
  (Invertible.tensorProductRightUnitor S.sheaf.obj S.ringCatSheaf.property M).inv ≫
    (Invertible.tensorProductBifunctor S.sheaf.obj S.ringCatSheaf.property).map
      (X := (M, SheafOfModules.unit (structureSheaf S.sheaf.obj S.ringCatSheaf.property)))
      (Y := (M, A)) (𝟙 M, s)

/-- **Multiplication on the right, on local sections**: it pairs the section with the value of
the morphism on the unit section. -/
theorem mulRightHom_app (s : SheafOfModules.unit (structureSheaf S.sheaf.obj
    S.ringCatSheaf.property) ⟶ A) (U : (Opens S)ᵒᵖ) (x : M.val.obj U) :
    (mulRightHom M A s).val.app U x =
      tensorSectionsAt S.sheaf.obj S.ringCatSheaf.property U M A x
        (s.val.app U (Stacks.AlgebraicGeometry.GradedAlgebraTwist.unitSection
          S.sheaf.obj S.ringCatSheaf.property U)) := by
  change ((Invertible.tensorProductBifunctor S.sheaf.obj S.ringCatSheaf.property).map
      (X := (M, SheafOfModules.unit (structureSheaf S.sheaf.obj S.ringCatSheaf.property)))
      (Y := (M, A)) (𝟙 M, s)).val.app U
      ((Invertible.tensorProductRightUnitor S.sheaf.obj
        S.ringCatSheaf.property M).inv.val.app U x) = _
  refine Eq.trans (congrArg (((Invertible.tensorProductBifunctor S.sheaf.obj
      S.ringCatSheaf.property).map
      (X := (M, SheafOfModules.unit (structureSheaf S.sheaf.obj S.ringCatSheaf.property)))
      (Y := (M, A)) (𝟙 M, s)).val.app U)
    (Stacks.AlgebraicGeometry.GradedAlgebraTwist.tensorSections_rightUnitorInvAt
      S.sheaf.obj S.ringCatSheaf.property U M x)) ?_
  exact tensorSections_tensorMapAt S.sheaf.obj S.ringCatSheaf.property U M M
    (SheafOfModules.unit (structureSheaf S.sheaf.obj S.ringCatSheaf.property)) A (𝟙 M) s x
    (Stacks.AlgebraicGeometry.GradedAlgebraTwist.unitSection
      S.sheaf.obj S.ringCatSheaf.property U)

/-- **Multiplication by a global section that trivializes `A` is an isomorphism.** -/
instance isIso_mulRightHom (s : SheafOfModules.unit (structureSheaf S.sheaf.obj
    S.ringCatSheaf.property) ⟶ A) [IsIso s] : IsIso (mulRightHom M A s) :=
  ((Invertible.tensorProductRightUnitor S.sheaf.obj S.ringCatSheaf.property M).symm ≪≫
    Invertible.tensorProductIso S.sheaf.obj S.ringCatSheaf.property
      (Iso.refl M) (asIso s)).isIso_hom

end MulRight

/-! ### The powers of a trivializing section trivialize the tensor powers -/

/-- **Multiplication by `ℓ`, as a morphism `ℒ^{⊗ d} ⟶ ℒ^{⊗ (d + 1)}`.** -/
def powStep (ℓ : (tp L 1).sections) (d : ℕ) : tp L (d : ℤ) ⟶ tp L ((d + 1 : ℕ) : ℤ) :=
  mulRightHom (tp L (d : ℤ)) (tp L 1) (powHom L ℓ 1) ≫
    (TensorPower.coherentMulIso S.sheaf.obj S.ringCatSheaf.property L (d : ℤ) 1).hom ≫
      (reix L (succ_cast d)).hom

/-- If `ℓ` trivializes the twisting module, multiplication by `ℓ` is an isomorphism
`ℒ^{⊗ d} ⟶ ℒ^{⊗ (d + 1)}`. -/
theorem isIso_powStep (ℓ : (tp L 1).sections) (d : ℕ) (h1 : IsIso (powHom L ℓ 1)) :
    IsIso (powStep L ℓ d) :=
  IsIso.comp_isIso' (isIso_mulRightHom (tp L (d : ℤ)) (tp L 1) (powHom L ℓ 1))
    (IsIso.comp_isIso'
      (TensorPower.coherentMulIso S.sheaf.obj S.ringCatSheaf.property L (d : ℤ) 1).isIso_hom
      (reix L (succ_cast d)).isIso_hom)

/-- **The `(d + 1)`-st power of `ℓ` is the `d`-th followed by multiplication by `ℓ`.** -/
theorem powHom_succ (ℓ : (tp L 1).sections) (d : ℕ) :
    powHom L ℓ (d + 1) = powHom L ℓ d ≫ powStep L ℓ d := by
  refine unitHom_ext _ _ fun U => ?_
  refine Eq.trans (powHom_app L ℓ (d + 1) U) ?_
  refine Eq.trans (powSec_succ_eval L ℓ d U) ?_
  change _ = (powStep L ℓ d).val.app U ((powHom L ℓ d).val.app U _)
  refine Eq.trans ?_ (congrArg ((powStep L ℓ d).val.app U) (powHom_app L ℓ d U)).symm
  change _ = (reix L (succ_cast d)).hom.val.app U
    ((TensorPower.coherentMulIso S.sheaf.obj S.ringCatSheaf.property L (d : ℤ) 1).hom.val.app U
      ((mulRightHom (tp L (d : ℤ)) (tp L 1) (powHom L ℓ 1)).val.app U
        ((powSec L ℓ d).eval U)))
  refine congrArg ((reix L (succ_cast d)).hom.val.app U) ?_
  refine Eq.trans (TensorPower.mulBilinear_app S.sheaf.obj S.ringCatSheaf.property L
    (d : ℤ) 1 U ((powSec L ℓ d).eval U) (ℓ.eval U)) ?_
  refine congrArg ((TensorPower.coherentMulIso S.sheaf.obj S.ringCatSheaf.property L
    (d : ℤ) 1).hom.val.app U) ?_
  refine Eq.trans ?_ (mulRightHom_app (tp L (d : ℤ)) (tp L 1) (powHom L ℓ 1) U
    ((powSec L ℓ d).eval U)).symm
  exact congrArg
    (fun t => tensorSectionsAt S.sheaf.obj S.ringCatSheaf.property U (tp L (d : ℤ))
      (tp L 1) ((powSec L ℓ d).eval U) t)
    ((congrArg (fun σ : (tp L 1).sections => σ.eval U) (powSec_one L ℓ)).symm.trans
      (powHom_app L ℓ 1 U).symm)

/-- **Every positive power of a trivializing global section trivializes the corresponding
tensor power.** -/
theorem isIso_powHom_succ (ℓ : (tp L 1).sections) (h1 : IsIso (powHom L ℓ 1)) :
    ∀ d : ℕ, IsIso (powHom L ℓ (d + 1))
  | 0 => h1
  | (d + 1) => by
      have := isIso_powHom_succ ℓ h1 d
      have := isIso_powStep L ℓ (d + 1) h1
      rw [powHom_succ]
      infer_instance

variable (𝒜 : SheafGradedAlgebra S)

/-- **The comparison map `𝒜_d ⟶ 𝒜_d ⊗ ℒ^{⊗ d}` in degree `d`**: tensoring with the `d`-th power
of `ℓ`. -/
def psiNat (ℓ : (tp L 1).sections) (d : ℕ) : 𝒜.piece (d : ℤ) ⟶ (twist 𝒜 L).piece (d : ℤ) :=
  mulRightHom (𝒜.piece (d : ℤ)) (tp L (d : ℤ)) (powHom L ℓ d)

/-- **The comparison map on local sections** pairs a section of `𝒜_d` with the `d`-th power
of `ℓ`. -/
theorem psiNat_app (ℓ : (tp L 1).sections) (d : ℕ) (U : (Opens S)ᵒᵖ)
    (x : (𝒜.piece (d : ℤ)).val.obj U) :
    (psiNat L 𝒜 ℓ d).val.app U x =
      tensorSectionsAt S.sheaf.obj S.ringCatSheaf.property U (𝒜.piece (d : ℤ))
        (tp L (d : ℤ)) x ((powSec L ℓ d).eval U) :=
  (mulRightHom_app (𝒜.piece (d : ℤ)) (tp L (d : ℤ)) (powHom L ℓ d) U x).trans
    (congrArg
      (fun t => tensorSectionsAt S.sheaf.obj S.ringCatSheaf.property U (𝒜.piece (d : ℤ))
        (tp L (d : ℤ)) x t) (powHom_app L ℓ d U))

/-- **The comparison map in degree `d` is an isomorphism** as soon as the `d`-th power of `ℓ`
trivializes the `d`-th tensor power of the twisting module. -/
instance isIso_psiNat (ℓ : (tp L 1).sections) (d : ℕ) [IsIso (powHom L ℓ d)] :
    IsIso (psiNat L 𝒜 ℓ d) :=
  isIso_mulRightHom (𝒜.piece (d : ℤ)) (tp L (d : ℤ)) (powHom L ℓ d)

/-- A local section of a sheaf of modules that is a zero object vanishes. -/
theorem eq_zero_of_isZero {M : SheafOfModules.{u} (structureSheaf S.sheaf.obj
    S.ringCatSheaf.property)} (h : IsZero M) (U : (Opens S)ᵒᵖ) (a : M.val.obj U) : a = 0 := by
  have h1 : (𝟙 M) = (0 : M ⟶ M) := h.eq_of_src _ _
  have h2 := congrArg (fun f : M ⟶ M => (SheafOfModules.Hom.val f).app U a) h1
  refine h2.trans ?_
  change (ConcreteCategory.hom (((0 : M.val ⟶ M.val)).app U)) a = 0
  rw [PresheafOfModules.zero_app]
  simp

/-- **The comparison map in every integer degree.** In a negative degree the source is a zero
object and there is nothing to choose. -/
def psiInt (ℓ : (tp L 1).sections) : ∀ n : ℤ, 𝒜.piece n ⟶ (twist 𝒜 L).piece n
  | Int.ofNat d => psiNat L 𝒜 ℓ d
  | Int.negSucc d => (𝒜.negative_isZero (Int.negSucc d) (by omega)).to_ _

/-- In a natural-number degree the comparison map is `psiNat`. -/
theorem psiInt_ofNat (ℓ : (tp L 1).sections) (d : ℕ) :
    psiInt L 𝒜 ℓ (d : ℤ) = psiNat L 𝒜 ℓ d := rfl

/-- **The comparison homomorphism `ψ : 𝒜 ⟶ ℬ`** of graded algebras attached to a global section
`ℓ` of the twisting module: in degree `d` it is `x ↦ x ⊗ ℓ^d`. -/
def psi (ℓ : (tp L 1).sections) :
    Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom 𝒜 (twist 𝒜 L) where
  app n := psiInt L 𝒜 ℓ n
  app_mul i j U a b := by
    obtain (p | p) := i
    · obtain (q | q) := j
      · refine Eq.trans (psiNat_app L 𝒜 ℓ (p + q) (op U) ((𝒜.mul (p : ℤ) (q : ℤ)).app U a b)) ?_
        refine Eq.trans ?_ (congrArg₂
          (fun s t => mulSection S.sheaf.obj S.ringCatSheaf.property 𝒜.piece
            (mulHom 𝒜) L (p : ℤ) (q : ℤ) (op U) s t)
          (psiNat_app L 𝒜 ℓ p (op U) a) (psiNat_app L 𝒜 ℓ q (op U) b)).symm
        refine Eq.trans ?_ (mulSection_pure S.sheaf.obj S.ringCatSheaf.property 𝒜.piece
          (mulHom 𝒜) L (p : ℤ) (q : ℤ) (op U) a ((powSec L ℓ p).eval (op U)) b
          ((powSec L ℓ q).eval (op U))).symm
        refine congrArg₂ (fun s t => tensorSectionsAt S.sheaf.obj S.ringCatSheaf.property (op U)
          (𝒜.piece ((p : ℤ) + (q : ℤ))) (tp L ((p : ℤ) + (q : ℤ))) s t)
          (mulA_eq 𝒜 (p : ℤ) (q : ℤ) (op U) a b).symm ?_
        refine Eq.trans (eq_of_heq (heq_powSec_mul L ℓ (op U) p q)).symm ?_
        exact (coherentMulIso_app_eq_mulBilinear S.sheaf.obj S.ringCatSheaf.property L
          (p : ℤ) (q : ℤ) (op U) ((powSec L ℓ p).eval (op U))
          ((powSec L ℓ q).eval (op U))).symm
      · have hb : b = 0 :=
          eq_zero_of_isZero (𝒜.negative_isZero _ (Int.negSucc_lt_zero q)) (op U) b
        subst hb
        simp
    · have ha : a = 0 :=
        eq_zero_of_isZero (𝒜.negative_isZero _ (Int.negSucc_lt_zero p)) (op U) a
      subst ha
      simp
  app_one U := by
    refine Eq.trans (psiNat_app L 𝒜 ℓ 0 (op U) (𝒜.one U)) ?_
    refine Eq.trans ?_ (oneSec_def S.sheaf.obj S.ringCatSheaf.property 𝒜.piece L
      (oneHom 𝒜) (op U)).symm
    exact congrArg (fun s => tensorSectionsAt S.sheaf.obj S.ringCatSheaf.property (op U)
      (𝒜.piece 0) (tp L 0) s
      ((TensorPower.oneSection S.sheaf.obj S.ringCatSheaf.property L).eval (op U)))
      (oneHom_app 𝒜 (op U)).symm

/-! ### The comparison for a trivialized twisting module -/

/-- **The comparison is an isomorphism in every positive degree**, when `ℓ` trivializes the
twisting module. -/
theorem eventually_isIso_psi_app (ℓ : (tp L 1).sections) (h1 : IsIso (powHom L ℓ 1)) :
    ∀ᶠ d : ℕ in Filter.atTop, IsIso ((psi L 𝒜 ℓ).app (d : ℤ)) := by
  refine Filter.eventually_atTop.2 ⟨1, fun d hd => ?_⟩
  obtain ⟨e, rfl⟩ : ∃ e : ℕ, d = e + 1 := ⟨d - 1, by omega⟩
  have := isIso_powHom_succ L ℓ h1 e
  exact isIso_psiNat L 𝒜 ℓ (e + 1)

/-- **The comparison for a twisting module trivialized by a global section.** Let `ℓ` be a
global section of `ℒ` whose induced map `𝒪_S ⟶ ℒ` is an isomorphism, and `ℬ` the twist of `𝒜`
(`Stacks.AlgebraicGeometry.GradedAlgebraTwist.twist`). Then:

1. the open `U(ψ)` of `Proj_S(ℬ)` on which the morphism induced by `ψ` is defined is the whole
   of `Proj_S(ℬ)`;
2. the induced morphism `U(ψ) ⟶ Proj_S(𝒜)` is an isomorphism;
3. it is a morphism over `S`;
4. for every `n : ℤ` the comparison `θ_n` on the `n`-th twisting sheaf is an isomorphism. -/
theorem relativeComparison_of_trivialized (ℓ : (tp L 1).sections) (h1 : IsIso (powHom L ℓ 1)) :
    (psi L 𝒜 ℓ).relativeMapDomain = ⊤ ∧
      IsIso (Tag07ZGMorphism.relativeMapHom (psi L 𝒜 ℓ)) ∧
      Tag07ZGMorphism.relativeMapHom (psi L 𝒜 ℓ) ≫ (RelativeProj.relativeProj 𝒜).toBase =
        (psi L 𝒜 ℓ).relativeMapDomain.ι ≫
          (RelativeProj.relativeProj (twist 𝒜 L)).toBase ∧
      ∀ n : ℤ, IsIso (Tag07ZGTwist.relativeTwistMap (psi L 𝒜 ℓ) n) :=
  ⟨RelativeProjMapDomain.relativeMapDomain_eq_top_of_eventually_isIso _
      (eventually_isIso_psi_app L 𝒜 ℓ h1),
    RelativeProjMapDomain.isIso_relativeMapHom_of_eventually_isIso _
      (eventually_isIso_psi_app L 𝒜 ℓ h1),
    Tag07ZGMorphism.relativeMapHom_comp_toBase _,
    fun n => Tag07ZGTwist.isIso_relativeTwistMap_of_eventually_isIso _
      (eventually_isIso_psi_app L 𝒜 ℓ h1) n⟩

/-! ### The graded assembly of the comparison maps -/

/-- **For a twisting module trivialized by a global section, the comparison maps `θ_n` fit
together into an isomorphism of sheaves of `ℤ`-graded algebras**, from the pullback of the twisting
algebra of `𝒜` along the induced morphism to the restriction of the twisting algebra of the twist
to `U(ψ)`. -/
def relativeThetaGradedIsoOfTrivialized (ℓ : (tp L 1).sections) (h1 : IsIso (powHom L ℓ 1)) :
    Stacks.RingedSpace.pullbackGradedAlgebra
        (Tag07ZGMorphism.relativeMapHom (psi L 𝒜 ℓ)).toLRSHom.toShHom
        (Tag07ZGTwist.twistAlgebra 𝒜) ≅
      Stacks.RingedSpace.pullbackGradedAlgebra
        (psi L 𝒜 ℓ).relativeMapDomain.ι.toLRSHom.toShHom
        (Tag07ZGTwist.twistAlgebra (twist 𝒜 L)) :=
  SheafOfModules.GradedAlgebra.isoOfIsIsoApp
    (Tag07ZGTwist.relativeTwistAlgebraHom (psi L 𝒜 ℓ))
    fun n => Tag07ZGTwist.isIso_relativeTwistMap_of_eventually_isIso _
      (eventually_isIso_psi_app L 𝒜 ℓ h1) n

/-- The degreewise components of the graded isomorphism are the comparison maps `θ_n`. -/
theorem relativeThetaGradedIsoOfTrivialized_hom_app (ℓ : (tp L 1).sections)
    (h1 : IsIso (powHom L ℓ 1)) (n : ℤ) :
    (relativeThetaGradedIsoOfTrivialized L 𝒜 ℓ h1).hom.app n =
      Tag07ZGTwist.relativeTwistMap (psi L 𝒜 ℓ) n := rfl

end Stacks.AlgebraicGeometry.RelativeInvertibleTwist

end
