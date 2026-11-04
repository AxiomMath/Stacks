module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.HomogeneousTwistComparison
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.LaurentPullbackDifferential
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.IdealPowerQuasicoherent
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorProduct.Quasicoherent
import StacksCore.Tactic.StacksAttribute

/-!
# The graded forms of `L^⋆` are quasi-coherent

Let `f : X ⟶ S` be a morphism of schemes, `L` an invertible `𝒪_X`-module and `L^⋆ ⟶ X` the
complement of the zero section of the associated line bundle. The degree-`n` part
`Ω^p_{L^⋆/S, n}` of the pushed-forward relative differential forms is a *quasi-coherent*
`𝒪_X`-module, for every `p : ℕ` and every `n : ℤ`. With the identification
`Stacks.LineBundle.Situation.gradedTwistIso` of
`StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.HomogeneousTwistComparison` that completes
clause (1) of Tag 0FUH, which asserts the identification *as quasi-coherent `𝒪_X`-modules*.

The route is `Stacks.AlgebraicGeometry.GabberColimit.isQuasicoherent_sheafSubmodule`: the
`Γ(X, U)`-spans of the homogeneous forms of degree `n` over the affine opens `U` of `X` form a
compatible family, and the subsheaf cut out by such a family is quasi-coherent. The work is the
compatibility condition, namely that for nested affine opens `W ≤ U` every homogeneous form of
degree `n` over `π⁻¹W` is a `Γ(X, W)`-combination of restrictions of homogeneous forms of degree
`n` over `π⁻¹U`.

## Main definitions

* `Stacks.LineBundle.Situation.gradedWedge`, `Situation.gradedSmul`, `Situation.gradedD` and
  `Situation.gradedOne`: the graded multiplication by a one-form, multiplication by a function on
  `π⁻¹U`, the relative de Rham differential and the constant form `1`, all read at the
  `Situation.gradedAmbient` spelling of the pushforward, which is the one the spans below are
  submodules of.
* `Stacks.LineBundle.Situation.homogeneousSheafSubmodule`: the subsheaf of the pushed-forward
  forms cut out by the affine-local spans of the homogeneous forms of degree `n`.

## Main results

* `Stacks.LineBundle.Situation.gradedWedge_gradedD_mem_span`: **wedging with the differential of
  an arbitrary homogeneous function on the smaller chart stays in the span of the restricted
  homogeneous forms.** This is the step the recursion turns on.
* `Stacks.LineBundle.Situation.isHomogeneousLaurentForm_mem_span` and
  `Situation.homogeneousSet_subset_span`: **every homogeneous form of degree `n` over the smaller
  affine chart is a `Γ(X, W)`-combination of restrictions of homogeneous forms of degree `n` over
  the bigger one.**
* `Stacks.LineBundle.Situation.isCompatible_homogeneousSet`: **the spans of the homogeneous forms
  form a compatible family.**
* `Stacks.LineBundle.Situation.homogeneousSheafSubmodule_eq`: the subsheaf that family cuts out
  is `Situation.gradedLaurentForms`.
* `Stacks.LineBundle.Situation.isQuasicoherent_gradedLaurentForms`,
  `Situation.isQuasicoherent_gradedAt` and `Situation.isQuasicoherent_gradedTwistSource`:
  **both sides of clause (1) of Tag 0FUH are quasi-coherent `𝒪_X`-modules.**

## Implementation notes

The recursion follows the definition of `Situation.IsHomogeneousLaurentForm`. With no wedge
factors the form is a homogeneous function times the constant form `1`, and
`Situation.gradedSmul_mem_span` writes the function's section of `L^{⊗ n}` through restrictions
from the bigger chart, `L^{⊗ n}` being quasi-coherent; the scalars are functions on `X` and
factor out of the span. With one more factor the induction hypothesis handles the `p`-form and
`Situation.gradedWedge_gradedD_mem_span` the differential: the section of `L^{⊗ j}` is again
written through restrictions, and the Leibniz rule splits each term into a differential restricted
from the bigger chart and the differential of a function pulled back from `X`. The second term is
where the expansion used to become circular — it is a degree-zero one-form over `π⁻¹W`, the same
shape the expansion started from — and what breaks it is
`Situation.laurentDifferential_pullback_mem_span` of
`StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.LaurentPullbackDifferential`, which finds the
combination on `X` and pushes it forward. A function pulled back from `X` is the homogeneous
function of degree zero of a multiple of the algebra unit,
`Situation.laurentPullbackFunction_eq`, so those differentials are themselves homogeneous
generators.

Every operation is wrapped at the `Γ(Situation.gradedAmbient p, U)` spelling rather than used at
the `D.laurentFormsAlgebra.piece p` indexing it is defined at. The two are equal by definition,
but the `Submodule` the spans live in is taken at the first, and a membership written at the
second does not typecheck against it: the `Membership` instance is rejected at `implicit`
transparency. `Situation.gradedPieceAt` is the same re-seating for the sections of the degree-`n`
part, which is what lets `Submodule.span_le` compare the two.

The degree-zero part is not a special case here: the recursion runs for every `n` at once, so
`Situation.isQuasicoherent_gradedLaurentForms` is proved in every degree directly and no transport
along `Situation.isIso_gradedTwistComparison` is needed. Tag 0GQM is used only for the tensor
product `Ω^p_{L^⋆/S, 0} ⊗_{𝒪_X} L^{⊗ n}` in `Situation.isQuasicoherent_gradedTwistSource`.

## References

* [Stacks Project, Tag 0FUH](https://stacks.math.columbia.edu/tag/0FUH), clause (1)
* [Stacks Project, Tag 0FU9](https://stacks.math.columbia.edu/tag/0FU9), the graded pieces
* [Stacks Project, Tag 077N](https://stacks.math.columbia.edu/tag/077N), Gabber's lemma and the
  compatible families its proof is built on
* [Stacks Project, Tag 0GQM](https://stacks.math.columbia.edu/tag/0GQM), tensor products of
  quasi-coherent modules
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite

universe u

namespace Stacks.LineBundle

variable (D : Situation.{u})

/-! ### Wedging a form with a one-form, at the pushed-forward spelling -/

/-- **Wedging a pushed-forward `p`-form with a pushed-forward one-form.** This is the graded
multiplication `Situation.laurentFormsAlgebra.mul p 1` of the forms of `L^⋆`, read at the
`Situation.gradedAmbient` spelling of the pushforward; the degree `((p + 1 : ℕ) : ℤ)` of the
target is `(p : ℤ) + 1` by `rfl`, so no transport along an equality of degrees occurs. -/
def Situation.gradedWedge (p : ℕ) (U : D.X.Opens) (η : Γ(D.gradedAmbient p, U))
    (ξ : Γ(D.gradedAmbient 1, U)) : Γ(D.gradedAmbient (p + 1), U) :=
  (D.laurentFormsAlgebra.mul (p : ℤ) 1).app (op (D.laurentSpectrumToBase ⁻¹ᵁ U)) η ξ

/-- Wedging is additive in the one-form. -/
theorem Situation.gradedWedge_add_right (p : ℕ) (U : D.X.Opens) (η : Γ(D.gradedAmbient p, U))
    (ξ₁ ξ₂ : Γ(D.gradedAmbient 1, U)) :
    D.gradedWedge p U η (ξ₁ + ξ₂) = D.gradedWedge p U η ξ₁ + D.gradedWedge p U η ξ₂ :=
  map_add ((D.laurentFormsAlgebra.mul (p : ℤ) 1).app
    (op (D.laurentSpectrumToBase ⁻¹ᵁ U)) η) ξ₁ ξ₂

/-- Wedging with zero is zero. -/
theorem Situation.gradedWedge_zero_right (p : ℕ) (U : D.X.Opens)
    (η : Γ(D.gradedAmbient p, U)) : D.gradedWedge p U η 0 = 0 :=
  map_zero ((D.laurentFormsAlgebra.mul (p : ℤ) 1).app
    (op (D.laurentSpectrumToBase ⁻¹ᵁ U)) η)

/-- Wedging is additive in the `p`-form. -/
theorem Situation.gradedWedge_add_left (p : ℕ) (U : D.X.Opens)
    (η₁ η₂ : Γ(D.gradedAmbient p, U)) (ξ : Γ(D.gradedAmbient 1, U)) :
    D.gradedWedge p U (η₁ + η₂) ξ = D.gradedWedge p U η₁ ξ + D.gradedWedge p U η₂ ξ :=
  (D.laurentFormsAlgebra.mul (p : ℤ) 1).map_add_left
    (op (D.laurentSpectrumToBase ⁻¹ᵁ U)) η₁ η₂ ξ

/-- Wedging a zero `p`-form gives zero. -/
theorem Situation.gradedWedge_zero_left (p : ℕ) (U : D.X.Opens)
    (ξ : Γ(D.gradedAmbient 1, U)) : D.gradedWedge p U 0 ξ = 0 :=
  map_zero (((D.laurentFormsAlgebra.mul (p : ℤ) 1).app
    (op (D.laurentSpectrumToBase ⁻¹ᵁ U))).flip ξ)

/-- **Wedging is `𝒪_X(U)`-linear in the one-form**, the `𝒪_X`-action on the pushforward being
multiplication by the pullback of the function. -/
theorem Situation.gradedWedge_smul_right (p : ℕ) (U : D.X.Opens) (r : Γ(D.X, U))
    (η : Γ(D.gradedAmbient p, U)) (ξ : Γ(D.gradedAmbient 1, U)) :
    D.gradedWedge p U η (r • ξ) = r • D.gradedWedge p U η ξ :=
  (D.laurentFormsAlgebra.mul (p : ℤ) 1).map_smul_right
    (op (D.laurentSpectrumToBase ⁻¹ᵁ U)) (D.laurentPullbackFunction U r) η ξ

/-- **Wedging is `𝒪_X(U)`-linear in the `p`-form.** -/
theorem Situation.gradedWedge_smul_left (p : ℕ) (U : D.X.Opens) (r : Γ(D.X, U))
    (η : Γ(D.gradedAmbient p, U)) (ξ : Γ(D.gradedAmbient 1, U)) :
    D.gradedWedge p U (r • η) ξ = r • D.gradedWedge p U η ξ :=
  (D.laurentFormsAlgebra.mul (p : ℤ) 1).map_smul_left
    (op (D.laurentSpectrumToBase ⁻¹ᵁ U)) (D.laurentPullbackFunction U r) η ξ

/-- **A function on `π⁻¹U` passes from the one-form factor to the `p`-form factor**, the graded
multiplication being bilinear over the functions on `π⁻¹U`. -/
theorem Situation.gradedWedge_laurentSmul_right (p : ℕ) (U : D.X.Opens)
    (f : D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ U)))
    (η : Γ(D.gradedAmbient p, U)) (ξ : Γ(D.gradedAmbient 1, U)) :
    D.gradedWedge p U η (D.laurentSmul 1 U f ξ) =
      D.gradedWedge p U (D.laurentSmul (p : ℤ) U f η) ξ :=
  ((D.laurentFormsAlgebra.mul (p : ℤ) 1).map_smul_right
      (op (D.laurentSpectrumToBase ⁻¹ᵁ U)) f η ξ).trans
    ((D.laurentFormsAlgebra.mul (p : ℤ) 1).map_smul_left
      (op (D.laurentSpectrumToBase ⁻¹ᵁ U)) f η ξ).symm

/-- **Wedging commutes with restriction to a smaller open of `X`.** -/
theorem Situation.gradedWedge_map (p : ℕ) {U W : D.X.Opens} (hWU : W ≤ U)
    (η : Γ(D.gradedAmbient p, U)) (ξ : Γ(D.gradedAmbient 1, U)) :
    (D.gradedAmbient (p + 1)).presheaf.map (homOfLE hWU).op (D.gradedWedge p U η ξ) =
      D.gradedWedge p W ((D.gradedAmbient p).presheaf.map (homOfLE hWU).op η)
        ((D.gradedAmbient 1).presheaf.map (homOfLE hWU).op ξ) :=
  (D.laurentFormsAlgebra.mul (p : ℤ) 1).naturality (D.laurentPreimageHom hWU).op η ξ

/-! ### Elementary rules for the homogeneous functions and their differentials -/

/-- **The homogeneous function of a sum of sections is the sum of the functions**, over an
affine open. -/
theorem Situation.laurentFunction_add (n : ℤ) (U : D.X.affineOpens)
    (x y : Γ(D.tensorPower n, U.1)) :
    D.laurentFunction n U (x + y) = D.laurentFunction n U x + D.laurentFunction n U y :=
  ((D.laurentFunctionOfOpen_affine n U (x + y)).symm.trans
      (D.laurentFunctionOfOpen_add n U.1 x y)).trans
    (congr_arg₂ (· + ·) (D.laurentFunctionOfOpen_affine n U x)
      (D.laurentFunctionOfOpen_affine n U y))

/-- **The homogeneous function of the zero section is the zero function.** -/
theorem Situation.laurentFunction_zero (n : ℤ) (U : D.X.affineOpens) :
    D.laurentFunction n U (0 : Γ(D.tensorPower n, U.1)) = 0 := by
  have h := D.laurentFunction_add n U 0 0
  rw [add_zero] at h
  exact left_eq_add.mp h

/-- **The homogeneous function is `𝒪_X(U)`-linear in its section**, over an affine open. -/
theorem Situation.laurentFunction_smul (n : ℤ) (U : D.X.affineOpens) (r : Γ(D.X, U.1))
    (x : Γ(D.tensorPower n, U.1)) :
    D.laurentFunction n U (r • x) =
      D.laurentPullbackFunction U.1 r * D.laurentFunction n U x :=
  ((D.laurentFunctionOfOpen_affine n U (r • x)).symm.trans
      (D.laurentFunctionOfOpen_smul n U.1 r x)).trans
    (congrArg (D.laurentPullbackFunction U.1 r * ·)
      (D.laurentFunctionOfOpen_affine n U x))

/-- **The function pulled back from `X` is the homogeneous function of degree zero** attached to
the corresponding multiple of the algebra unit. This is what lets the differential of a
pulled-back function be read as a homogeneous generator. -/
theorem Situation.laurentPullbackFunction_eq (U : D.X.affineOpens) (r : Γ(D.X, U.1)) :
    D.laurentPullbackFunction U.1 r =
      D.laurentFunction 0 U
        (r • id (α := Γ(D.tensorPower 0, U.1)) (D.laurentAlgebra.one.eval (op U.1))) :=
  ((mul_one (D.laurentPullbackFunction U.1 r)).symm.trans
      (congrArg (D.laurentPullbackFunction U.1 r * ·)
        (D.laurentFunctionOfOpen_one U.1).symm)).trans
    ((D.laurentFunctionOfOpen_smul 0 U.1 r _).symm.trans
      (D.laurentFunctionOfOpen_affine 0 U _))

/-- **The relative de Rham differential of `L^⋆` kills the zero function.** -/
theorem Situation.laurentDifferential_zero (V : D.laurentSpectrum.Opens) :
    (D.laurentDifferential V 0 : Γ(D.laurentForms 1, V)) = 0 := by
  have h := D.laurentDifferential_add V 0 0
  rw [add_zero] at h
  exact left_eq_add.mp h

/-- **Restricting a homogeneous function gives the homogeneous function of the restricted
section**, with the restriction of the section read at the `Γ(L^{⊗ n}, ·)` spelling the spans
below are taken at. -/
theorem Situation.laurentFunction_restrict (n : ℤ) {U W : D.X.affineOpens} (hWU : W.1 ≤ U.1)
    (x : Γ(D.tensorPower n, U.1)) :
    (D.laurentSpectrum.sheaf.obj.map (D.laurentPreimageHom hWU).op).hom
        (D.laurentFunction n U x) =
      D.laurentFunction n W ((D.tensorPower n).presheaf.map (homOfLE hWU).op x) :=
  D.laurentFunction_map n hWU x

/-! ### The pushed-forward operations at the `Γ` spelling -/

/-- **Multiplication of a pushed-forward form by a function on `π⁻¹U`**, read at the
`Situation.gradedAmbient` spelling. This is `Situation.laurentSmul`; what the definition adds is
that its value is typed as a section of `Situation.gradedAmbient`, which is the type the spans
below are submodules of. -/
def Situation.gradedSmul (p : ℕ) (U : D.X.Opens)
    (f : D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ U)))
    (ω : Γ(D.gradedAmbient p, U)) : Γ(D.gradedAmbient p, U) :=
  D.laurentSmul (p : ℤ) U f ω

/-- Multiplication by a function is additive in the form. -/
theorem Situation.gradedSmul_add (p : ℕ) (U : D.X.Opens)
    (f : D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ U)))
    (ω η : Γ(D.gradedAmbient p, U)) :
    D.gradedSmul p U f (ω + η) = D.gradedSmul p U f ω + D.gradedSmul p U f η :=
  D.laurentSmul_add (p : ℤ) U f ω η

/-- Multiplying the zero form gives zero. -/
theorem Situation.gradedSmul_zero (p : ℕ) (U : D.X.Opens)
    (f : D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ U))) :
    D.gradedSmul p U f 0 = 0 :=
  D.laurentSmul_zero (p : ℤ) U f

/-- Multiplication by a sum of functions is the sum of the multiplications. -/
theorem Situation.add_gradedSmul (p : ℕ) (U : D.X.Opens)
    (f g : D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ U)))
    (ω : Γ(D.gradedAmbient p, U)) :
    D.gradedSmul p U (f + g) ω = D.gradedSmul p U f ω + D.gradedSmul p U g ω :=
  D.add_laurentSmul (p : ℤ) U f g ω

/-- Multiplication by the zero function gives zero. -/
theorem Situation.zero_gradedSmul (p : ℕ) (U : D.X.Opens) (ω : Γ(D.gradedAmbient p, U)) :
    D.gradedSmul p U 0 ω = 0 := by
  have h := D.add_gradedSmul p U 0 0 ω
  rw [add_zero] at h
  exact left_eq_add.mp h

/-- Multiplication by a function is `𝒪_X(U)`-linear in the form. -/
theorem Situation.gradedSmul_smul (p : ℕ) (U : D.X.Opens)
    (f : D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ U)))
    (r : Γ(D.X, U)) (ω : Γ(D.gradedAmbient p, U)) :
    D.gradedSmul p U f (r • ω) = r • D.gradedSmul p U f ω :=
  D.laurentSmul_smul (p : ℤ) U f r ω

/-- Multiplication by a product of functions is the composite of the two multiplications. -/
theorem Situation.gradedSmul_mul (p : ℕ) (U : D.X.Opens)
    (g f : D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ U)))
    (ω : Γ(D.gradedAmbient p, U)) :
    D.gradedSmul p U (g * f) ω = D.gradedSmul p U g (D.gradedSmul p U f ω) :=
  D.laurentSmul_mul (p : ℤ) U g f ω

/-- **Multiplication by a function pulled back from `X` is the `𝒪_X`-action.** -/
theorem Situation.gradedSmul_pullback (p : ℕ) (U : D.X.Opens) (r : Γ(D.X, U))
    (ω : Γ(D.gradedAmbient p, U)) :
    D.gradedSmul p U (D.laurentPullbackFunction U r) ω = r • ω :=
  (D.smul_eq_laurentSmul (p : ℤ) U r ω).symm

/-- Multiplication by a function commutes with restriction. -/
theorem Situation.gradedSmul_map (p : ℕ) {U W : D.X.Opens} (hWU : W ≤ U)
    (f : D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ U)))
    (ω : Γ(D.gradedAmbient p, U)) :
    (D.gradedAmbient p).presheaf.map (homOfLE hWU).op (D.gradedSmul p U f ω) =
      D.gradedSmul p W ((D.laurentSpectrum.sheaf.obj.map (D.laurentPreimageHom hWU).op).hom f)
        ((D.gradedAmbient p).presheaf.map (homOfLE hWU).op ω) :=
  D.laurentSmul_map (p : ℤ) hWU f ω

/-- **A function on `π⁻¹U` passes from the one-form factor of a wedge to the `p`-form
factor.** -/
theorem Situation.gradedWedge_gradedSmul_right (p : ℕ) (U : D.X.Opens)
    (f : D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ U)))
    (η : Γ(D.gradedAmbient p, U)) (ξ : Γ(D.gradedAmbient 1, U)) :
    D.gradedWedge p U η (D.gradedSmul 1 U f ξ) =
      D.gradedWedge p U (D.gradedSmul p U f η) ξ :=
  D.gradedWedge_laurentSmul_right p U f η ξ

/-- **The relative de Rham differential of a function on `π⁻¹U`**, read at the
`Situation.gradedAmbient` spelling of the pushed-forward one-forms. -/
def Situation.gradedD (U : D.X.Opens)
    (b : D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ U))) :
    Γ(D.gradedAmbient 1, U) :=
  D.laurentDifferential (D.laurentSpectrumToBase ⁻¹ᵁ U) b

/-- The differential is additive. -/
theorem Situation.gradedD_add (U : D.X.Opens)
    (b c : D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ U))) :
    D.gradedD U (b + c) = D.gradedD U b + D.gradedD U c :=
  D.laurentDifferential_add _ b c

/-- The differential kills the zero function. -/
theorem Situation.gradedD_zero (U : D.X.Opens) : D.gradedD U 0 = 0 :=
  D.laurentDifferential_zero _

/-- **The Leibniz rule**, at the `Situation.gradedAmbient` spelling. -/
theorem Situation.gradedD_mul (U : D.X.Opens)
    (b c : D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ U))) :
    D.gradedD U (b * c) =
      D.gradedSmul 1 U b (D.gradedD U c) + D.gradedSmul 1 U c (D.gradedD U b) :=
  D.laurentDifferential_mul _ b c

/-- The differential commutes with restriction. -/
theorem Situation.gradedD_map {U W : D.X.Opens} (hWU : W ≤ U)
    (b : D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ U))) :
    (D.gradedAmbient 1).presheaf.map (homOfLE hWU).op (D.gradedD U b) =
      D.gradedD W ((D.laurentSpectrum.sheaf.obj.map (D.laurentPreimageHom hWU).op).hom b) :=
  D.laurentDifferential_map (D.laurentPreimageHom hWU) b

/-- **The constant form `1`** on `π⁻¹U`, at the `Situation.gradedAmbient` spelling: the unit of
the algebra of relative forms of `L^⋆`, which is the `p = 0` homogeneous generator of degree
zero. -/
def Situation.gradedOne (U : D.X.Opens) : Γ(D.gradedAmbient 0, U) :=
  D.laurentFormsAlgebra.one.eval (op (D.laurentSpectrumToBase ⁻¹ᵁ U))

/-- The constant form `1` restricts to the constant form `1`. -/
theorem Situation.gradedOne_map {U W : D.X.Opens} (hWU : W ≤ U) :
    (D.gradedAmbient 0).presheaf.map (homOfLE hWU).op (D.gradedOne U) = D.gradedOne W :=
  PresheafOfModules.sections_property D.laurentFormsAlgebra.one (D.laurentPreimageHom hWU).op

/-! ### Homogeneity, at the `Γ` spelling -/

/-- **The constant form `1` is homogeneous of degree zero with no wedge factors.** -/
theorem Situation.isHomogeneousLaurentForm_gradedOne (U : D.X.affineOpens) :
    D.IsHomogeneousLaurentForm U 0 0 (D.gradedOne U.1) := by
  refine ⟨D.laurentAlgebra.one.eval (op U.1), ?_⟩
  rw [D.laurentFunction_one U]
  exact (D.laurentSmul_one 0 U.1 (D.gradedOne U.1)).symm

/-- **A homogeneous function of degree `n` times the constant form `1` is a homogeneous form of
degree `n` with no wedge factors.** -/
theorem Situation.isHomogeneousLaurentForm_gradedSmul_one (n : ℤ) (U : D.X.affineOpens)
    (x : Γ(D.tensorPower n, U.1)) :
    D.IsHomogeneousLaurentForm U 0 n
      (D.gradedSmul 0 U.1 (D.laurentFunction n U x) (D.gradedOne U.1)) :=
  ⟨x, rfl⟩

/-- **Multiplying a homogeneous form by a homogeneous function adds the degrees**, at the
`Γ` spelling. -/
theorem Situation.isHomogeneousLaurentForm_gradedSmul (p : ℕ) (m i n : ℤ) (hmin : m + i = n)
    (U : D.X.affineOpens) (y : Γ(D.tensorPower m, U.1)) {ω : Γ(D.gradedAmbient p, U.1)}
    (hω : D.IsHomogeneousLaurentForm U p i ω) :
    D.IsHomogeneousLaurentForm U p n (D.gradedSmul p U.1 (D.laurentFunction m U y) ω) := by
  subst hmin
  exact D.isHomogeneousLaurentForm_smul U m y p i ω hω

/-- **Wedging a homogeneous form of degree `i` with the differential of a homogeneous function of
degree `j` gives a homogeneous form of degree `i + j`**, which is the recursion defining the
homogeneous forms read at the `Γ` spelling. -/
theorem Situation.isHomogeneousLaurentForm_gradedWedge (p : ℕ) (i j n : ℤ) (hijn : i + j = n)
    (U : D.X.affineOpens) {η : Γ(D.gradedAmbient p, U.1)}
    (hη : D.IsHomogeneousLaurentForm U p i η) (x : Γ(D.tensorPower j, U.1)) :
    D.IsHomogeneousLaurentForm U (p + 1) n
      (D.gradedWedge p U.1 η (D.gradedD U.1 (D.laurentFunction j U x))) :=
  ⟨i, j, hijn, η, x, hη, rfl⟩

/-! ### The homogeneous forms of the smaller chart come from the bigger one -/

section Descent

variable {U W : D.X.affineOpens}

/-- **Multiplying by a homogeneous function restricted from the bigger chart keeps a section in
the span of the restricted homogeneous forms**, raising the degree. -/
theorem Situation.gradedSmul_restrict_mem_span (p : ℕ) (i j n : ℤ) (hjin : j + i = n)
    (hWU : W.1 ≤ U.1) (y : Γ(D.tensorPower j, U.1)) {ζ : Γ(D.gradedAmbient p, W.1)}
    (hζ : ζ ∈ Submodule.span Γ(D.X, W.1)
      ((D.gradedAmbient p).presheaf.map (homOfLE hWU).op '' D.homogeneousSet p i U)) :
    D.gradedSmul p W.1
        ((D.laurentSpectrum.sheaf.obj.map (D.laurentPreimageHom hWU).op).hom
          (D.laurentFunction j U y)) ζ ∈
      Submodule.span Γ(D.X, W.1)
        ((D.gradedAmbient p).presheaf.map (homOfLE hWU).op '' D.homogeneousSet p n U) := by
  induction hζ using Submodule.span_induction with
  | mem ω hω =>
      obtain ⟨η, hη, rfl⟩ := hω
      exact Submodule.subset_span ⟨D.gradedSmul p U.1 (D.laurentFunction j U y) η,
        D.isHomogeneousLaurentForm_gradedSmul p j i n hjin U y hη,
        D.gradedSmul_map p hWU _ η⟩
  | zero => rw [D.gradedSmul_zero]; exact Submodule.zero_mem _
  | add z₁ z₂ _ _ h₁ h₂ => rw [D.gradedSmul_add]; exact Submodule.add_mem _ h₁ h₂
  | smul c z _ h => rw [D.gradedSmul_smul]; exact Submodule.smul_mem _ c h

/-- Every section of `L^{⊗ j}` over the smaller affine chart is a combination of restrictions of
sections over the bigger one. -/
private theorem Situation.mem_span_range_tensorPower_restrict (j : ℤ) (hWU : W.1 ≤ U.1)
    (x : Γ(D.tensorPower j, W.1)) :
    x ∈ Submodule.span Γ(D.X, W.1)
      (Set.range ((D.tensorPower j).presheaf.map (homOfLE hWU).op)) := by
  rw [Stacks.AlgebraicGeometry.GabberColimit.span_range_restrict_eq_top
    (D.tensorPower j) U.2 W.2 hWU]
  trivial

/-- **Multiplying by an arbitrary homogeneous function on the smaller chart keeps a section in
the span of the restricted homogeneous forms**, raising the degree. The section of `L^{⊗ j}` the
function comes from is a `Γ(X, W)`-combination of restrictions from the bigger chart, `L^{⊗ j}`
being quasi-coherent, and the scalars factor out. -/
theorem Situation.gradedSmul_mem_span (p : ℕ) (i j n : ℤ) (hjin : j + i = n)
    (hWU : W.1 ≤ U.1) (x : Γ(D.tensorPower j, W.1)) {ζ : Γ(D.gradedAmbient p, W.1)}
    (hζ : ζ ∈ Submodule.span Γ(D.X, W.1)
      ((D.gradedAmbient p).presheaf.map (homOfLE hWU).op '' D.homogeneousSet p i U)) :
    D.gradedSmul p W.1 (D.laurentFunction j W x) ζ ∈
      Submodule.span Γ(D.X, W.1)
        ((D.gradedAmbient p).presheaf.map (homOfLE hWU).op '' D.homogeneousSet p n U) := by
  have hx := D.mem_span_range_tensorPower_restrict j hWU x
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨y, rfl⟩ := hx
      rw [← D.laurentFunction_restrict j hWU y]
      exact D.gradedSmul_restrict_mem_span p i j n hjin hWU y hζ
  | zero => rw [D.laurentFunction_zero, D.zero_gradedSmul]; exact Submodule.zero_mem _
  | add x₁ x₂ _ _ h₁ h₂ =>
      rw [D.laurentFunction_add, D.add_gradedSmul]; exact Submodule.add_mem _ h₁ h₂
  | smul c x _ h =>
      rw [D.laurentFunction_smul, D.gradedSmul_mul, D.gradedSmul_pullback]
      exact Submodule.smul_mem _ c h

/-- **Wedging with the restriction of the differential of a homogeneous function on the bigger
chart keeps a section in the span of the restricted homogeneous forms**, adding the degrees. -/
theorem Situation.gradedWedge_restrict_mem_span (p : ℕ) (i j n : ℤ) (hijn : i + j = n)
    (hWU : W.1 ≤ U.1) (y : Γ(D.tensorPower j, U.1)) {ζ : Γ(D.gradedAmbient p, W.1)}
    (hζ : ζ ∈ Submodule.span Γ(D.X, W.1)
      ((D.gradedAmbient p).presheaf.map (homOfLE hWU).op '' D.homogeneousSet p i U)) :
    D.gradedWedge p W.1 ζ
        ((D.gradedAmbient 1).presheaf.map (homOfLE hWU).op
          (D.gradedD U.1 (D.laurentFunction j U y))) ∈
      Submodule.span Γ(D.X, W.1)
        ((D.gradedAmbient (p + 1)).presheaf.map (homOfLE hWU).op ''
          D.homogeneousSet (p + 1) n U) := by
  induction hζ using Submodule.span_induction with
  | mem ω hω =>
      obtain ⟨η, hη, rfl⟩ := hω
      exact Submodule.subset_span
        ⟨D.gradedWedge p U.1 η (D.gradedD U.1 (D.laurentFunction j U y)),
          D.isHomogeneousLaurentForm_gradedWedge p i j n hijn U hη y,
          D.gradedWedge_map p hWU η _⟩
  | zero => rw [D.gradedWedge_zero_left]; exact Submodule.zero_mem _
  | add z₁ z₂ _ _ h₁ h₂ => rw [D.gradedWedge_add_left]; exact Submodule.add_mem _ h₁ h₂
  | smul c z _ h => rw [D.gradedWedge_smul_left]; exact Submodule.smul_mem _ c h

/-- **Wedging with a combination of restricted differentials of pulled-back functions keeps a
section in the span of the restricted homogeneous forms**, leaving the degree alone: a function
pulled back from `X` is homogeneous of degree zero, by
`Situation.laurentPullbackFunction_eq`. -/
theorem Situation.gradedWedge_pullD_mem_span (p : ℕ) (n : ℤ) (hWU : W.1 ≤ U.1)
    {ζ : Γ(D.gradedAmbient p, W.1)}
    (hζ : ζ ∈ Submodule.span Γ(D.X, W.1)
      ((D.gradedAmbient p).presheaf.map (homOfLE hWU).op '' D.homogeneousSet p n U))
    {g : Γ(D.gradedAmbient 1, W.1)}
    (hg : g ∈ Submodule.span Γ(D.X, W.1)
      ((D.gradedAmbient 1).presheaf.map (homOfLE hWU).op ''
        Set.range fun a : Γ(D.X, U.1) => D.gradedD U.1 (D.laurentPullbackFunction U.1 a))) :
    D.gradedWedge p W.1 ζ g ∈
      Submodule.span Γ(D.X, W.1)
        ((D.gradedAmbient (p + 1)).presheaf.map (homOfLE hWU).op ''
          D.homogeneousSet (p + 1) n U) := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨-, ⟨a, rfl⟩, rfl⟩ := hg
      show D.gradedWedge p W.1 ζ
          ((D.gradedAmbient 1).presheaf.map (homOfLE hWU).op
            (D.gradedD U.1 (D.laurentPullbackFunction U.1 a))) ∈ _
      rw [D.laurentPullbackFunction_eq U a]
      exact D.gradedWedge_restrict_mem_span p n 0 n (add_zero n) hWU _ hζ
  | zero => rw [D.gradedWedge_zero_right]; exact Submodule.zero_mem _
  | add g₁ g₂ _ _ h₁ h₂ => rw [D.gradedWedge_add_right]; exact Submodule.add_mem _ h₁ h₂
  | smul c g _ h => rw [D.gradedWedge_smul_right]; exact Submodule.smul_mem _ c h

/-- **Wedging with the differential of an arbitrary homogeneous function on the smaller chart
keeps a section in the span of the restricted homogeneous forms**, adding the degrees. This is
the step the recursion turns on. The section of `L^{⊗ j}` is written through restrictions from
the bigger chart, `L^{⊗ j}` being quasi-coherent, and the Leibniz rule splits the differential of
each term into one differential restricted from the bigger chart and one differential of a
function pulled back from `X`; the second is handled by
`Situation.laurentDifferential_pullback_mem_span`, which is what breaks the circularity. -/
theorem Situation.gradedWedge_gradedD_mem_span (p : ℕ) (i j n : ℤ) (hijn : i + j = n)
    (hWU : W.1 ≤ U.1) (x : Γ(D.tensorPower j, W.1)) {ζ : Γ(D.gradedAmbient p, W.1)}
    (hζ : ζ ∈ Submodule.span Γ(D.X, W.1)
      ((D.gradedAmbient p).presheaf.map (homOfLE hWU).op '' D.homogeneousSet p i U)) :
    D.gradedWedge p W.1 ζ (D.gradedD W.1 (D.laurentFunction j W x)) ∈
      Submodule.span Γ(D.X, W.1)
        ((D.gradedAmbient (p + 1)).presheaf.map (homOfLE hWU).op ''
          D.homogeneousSet (p + 1) n U) := by
  have hx := D.mem_span_range_tensorPower_restrict j hWU x
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨y, rfl⟩ := hx
      rw [← D.laurentFunction_restrict j hWU y, ← D.gradedD_map hWU]
      exact D.gradedWedge_restrict_mem_span p i j n hijn hWU y hζ
  | zero =>
      rw [D.laurentFunction_zero, D.gradedD_zero, D.gradedWedge_zero_right]
      exact Submodule.zero_mem _
  | add x₁ x₂ _ _ h₁ h₂ =>
      rw [D.laurentFunction_add, D.gradedD_add, D.gradedWedge_add_right]
      exact Submodule.add_mem _ h₁ h₂
  | smul c x _ h =>
      rw [D.laurentFunction_smul, D.gradedD_mul, D.gradedWedge_add_right,
        D.gradedSmul_pullback, D.gradedWedge_smul_right, D.gradedWedge_gradedSmul_right]
      refine Submodule.add_mem _ (Submodule.smul_mem _ c h) ?_
      exact D.gradedWedge_pullD_mem_span p n hWU
        (D.gradedSmul_mem_span p i j n (by omega) hWU x hζ)
        (D.laurentDifferential_pullback_mem_span U W hWU c)

/-- **Every homogeneous form of degree `n` over the smaller affine chart is a
`Γ(X, W)`-combination of restrictions of homogeneous forms of degree `n` over the bigger one.**
The induction is on the number of wedge factors: with none, the form is a homogeneous function
times the constant form `1`, and the function's section is written through restrictions by
`Situation.gradedSmul_mem_span`; with one more factor, the induction hypothesis handles the
`p`-form factor and `Situation.gradedWedge_gradedD_mem_span` the differential. -/
theorem Situation.isHomogeneousLaurentForm_mem_span (hWU : W.1 ≤ U.1) :
    ∀ (p : ℕ) (n : ℤ) (ω : Γ(D.gradedAmbient p, W.1)),
      D.IsHomogeneousLaurentForm W p n ω →
        ω ∈ Submodule.span Γ(D.X, W.1)
          ((D.gradedAmbient p).presheaf.map (homOfLE hWU).op '' D.homogeneousSet p n U) := by
  intro p
  induction p with
  | zero =>
      rintro n ω ⟨x, rfl⟩
      refine D.gradedSmul_mem_span 0 0 n n (add_zero n) hWU x ?_
      exact Submodule.subset_span ⟨D.gradedOne U.1,
        D.isHomogeneousLaurentForm_gradedOne U, D.gradedOne_map hWU⟩
  | succ q ih =>
      rintro n ω ⟨i, j, hij, η, x, hη, rfl⟩
      exact D.gradedWedge_gradedD_mem_span q i j n hij hWU x (ih i η hη)

/-- **The homogeneous forms of degree `n` over the smaller affine chart lie in the span of the
restrictions of those over the bigger one.** -/
theorem Situation.homogeneousSet_subset_span (p : ℕ) (n : ℤ) (hWU : W.1 ≤ U.1) :
    D.homogeneousSet p n W ⊆ Submodule.span Γ(D.X, W.1)
      ((D.gradedAmbient p).presheaf.map (homOfLE hWU).op '' D.homogeneousSet p n U) :=
  fun ω hω => D.isHomogeneousLaurentForm_mem_span hWU p n ω hω

end Descent

/-- **The spans of the homogeneous forms of degree `n` over the affine opens of `X` form a
compatible family of submodules of the pushed-forward relative forms**, which is the datum
`Stacks.AlgebraicGeometry.GabberColimit.sheafSubmodule` turns into a quasi-coherent subsheaf.
One inclusion is `Situation.span_homogeneousSet_image_le`, the restrictions of homogeneous forms
being homogeneous; the other is `Situation.homogeneousSet_subset_span`. -/
theorem Situation.isCompatible_homogeneousSet (p : ℕ) (n : ℤ) :
    Stacks.AlgebraicGeometry.GabberColimit.IsCompatible (D.gradedAmbient p)
      fun U => Submodule.span Γ(D.X, U.1) (D.homogeneousSet p n U) :=
  Stacks.AlgebraicGeometry.GabberColimit.isCompatible_span (D.gradedAmbient p)
    (fun U => D.homogeneousSet p n U) fun _ _ hWU =>
      le_antisymm (Submodule.span_le.mpr (D.homogeneousSet_subset_span p n hWU))
        (D.span_homogeneousSet_image_le p n hWU)

/-! ### Quasi-coherence of the graded pieces -/

/-- **The pushed-forward relative forms are quasi-coherent**, as an instance at the
`Situation.gradedAmbient` spelling, which is what
`Stacks.AlgebraicGeometry.GabberColimit.sheafSubmodule` asks for. -/
instance Situation.isQuasicoherent_gradedAmbient (p : ℕ) :
    (D.gradedAmbient p).IsQuasicoherent :=
  D.isQuasicoherent_laurentFormsPushforward p

/-- **The subsheaf of the pushed-forward relative forms cut out by the affine-local spans of the
homogeneous forms of degree `n`.** By `Situation.homogeneousSheafSubmodule_eq` it is the
degree-`n` part `Ω^p_{L^⋆/S, n}`; this construction of it is the one Gabber's lemma gives
quasi-coherence for. Its type is given at the `Situation.laurentFormsPushforward` spelling, which
it is by definition and at which the lattice of sub-sheaves of modules is found. -/
def Situation.homogeneousSheafSubmodule (p : ℕ) (n : ℤ) :
    (D.laurentFormsPushforward (p : ℤ)).Submodule :=
  Stacks.AlgebraicGeometry.GabberColimit.sheafSubmodule (D.gradedAmbient p)
    (fun U => Submodule.span Γ(D.X, U.1) (D.homogeneousSet p n U))
    (D.isCompatible_homogeneousSet p n)

/-- **Over an affine open the subsheaf cut out by the compatible family is the span of the
homogeneous forms there.** -/
theorem Situation.homogeneousSheafSubmodule_obj (p : ℕ) (n : ℤ) (U : D.X.affineOpens) :
    (D.homogeneousSheafSubmodule p n).toSubmodule.obj (op U.1) =
      Submodule.span Γ(D.X, U.1) (D.homogeneousSet p n U) :=
  Stacks.AlgebraicGeometry.GabberColimit.obj_sheafSubmodule (D.gradedAmbient p)
    (fun U => Submodule.span Γ(D.X, U.1) (D.homogeneousSet p n U))
    (D.isCompatible_homogeneousSet p n) U

/-- The sections of the degree-`n` part over an affine open, re-seated as a submodule of the
sections of `Situation.gradedAmbient` over `Γ(X, U)`. The two spellings of the ring and of the
module are the same by definition, and this named re-seating is what lets `Submodule.span_le`
compare the span of the homogeneous forms with the degree-`n` part. -/
def Situation.gradedPieceAt (p : ℕ) (n : ℤ) (U : D.X.affineOpens) :
    Submodule Γ(D.X, U.1) Γ(D.gradedAmbient p, U.1) :=
  (D.gradedLaurentForms p n).obj (op U.1)

/-- **The span of the homogeneous forms of degree `n` over an affine open is contained in the
degree-`n` part there.** -/
theorem Situation.span_homogeneousSet_le (p : ℕ) (n : ℤ) (U : D.X.affineOpens) :
    Submodule.span Γ(D.X, U.1) (D.homogeneousSet p n U) ≤ D.gradedPieceAt p n U :=
  Submodule.span_le.mpr fun _ hω => D.mem_gradedLaurentForms U hω

/-- **The subsheaf cut out by the affine-local spans of the homogeneous forms is the degree-`n`
part `Ω^p_{L^⋆/S, n}`.** One inclusion is the minimality of the degree-`n` part,
`Situation.gradedLaurentForms_le_iff`, since the spans contain the homogeneous forms; the other
is affine-locality of membership in a subsheaf, `Stacks.Algebraization.mem_submodule_of_affine`,
together with `Situation.span_homogeneousSet_le`. -/
theorem Situation.homogeneousSheafSubmodule_eq (p : ℕ) (n : ℤ) :
    D.homogeneousSheafSubmodule p n = D.gradedLaurentForms p n := by
  refine le_antisymm (fun V s hs => ?_) ((D.gradedLaurentForms_le_iff _).mpr fun U ω hω => ?_)
  · refine Stacks.Algebraization.mem_submodule_of_affine (F := D.gradedAmbient p)
      (D.gradedLaurentForms p n) V.unop
      (id (α := Γ(D.gradedAmbient p, V.unop)) s) fun U i => ?_
    exact D.span_homogeneousSet_le p n U (hs U i.le)
  · exact fun W h => Submodule.subset_span (D.isHomogeneousLaurentForm_map h p n ω hω)

/-- **The degree-`n` part `Ω^p_{L^⋆/S, n}` of the pushed-forward relative differential forms of
`L^⋆` is a quasi-coherent `𝒪_X`-module**, for every `p` and every `n`. The homogeneous forms of
degree `n` over the affine opens of `X` span a compatible family of submodules, by
`Situation.isCompatible_homogeneousSet`, and the subsheaf Gabber's lemma cuts out from such a
family is quasi-coherent. -/
theorem Situation.isQuasicoherent_gradedLaurentForms (p : ℕ) (n : ℤ) :
    ((D.gradedLaurentForms p n).toSheafOfModules : D.X.Modules).IsQuasicoherent := by
  rw [← D.homogeneousSheafSubmodule_eq p n]
  exact Stacks.AlgebraicGeometry.GabberColimit.isQuasicoherent_sheafSubmodule
    (D.gradedAmbient p) (fun U => Submodule.span Γ(D.X, U.1) (D.homogeneousSet p n U))
    (D.isCompatible_homogeneousSet p n)

/-- **The degree-`n` part `Ω^p_{L^⋆/S, n}` is quasi-coherent**, read at the indexing the tensor
product of Tag 05NA and the comparison map of clause (1) are defined over. This is
`Situation.isQuasicoherent_gradedLaurentForms` at the `Situation.gradedAt` spelling, which is the
same object by definition. -/
@[stacks 0FUH "clause (1): the degree-n part is a quasi-coherent O_X-module"]
theorem Situation.isQuasicoherent_gradedAt (p : ℕ) (n : ℤ) :
    (D.gradedAt p n).IsQuasicoherent :=
  D.isQuasicoherent_gradedLaurentForms p n

/-- **The source `Ω^p_{L^⋆/S, 0} ⊗_{𝒪_X} L^{⊗ n}` of the comparison map of clause (1) is
quasi-coherent**: both factors are, the degree-zero part by
`Situation.isQuasicoherent_gradedAt` and the tensor power by
`Situation.isQuasicoherent_tensorPower`, so Tag 0GQM applies. -/
@[stacks 0FUH "clause (1): the twisted degree-zero part is a quasi-coherent O_X-module"]
theorem Situation.isQuasicoherent_gradedTwistSource (p : ℕ) (n : ℤ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor D.X.sheaf).obj (D.gradedAt p 0)).obj
      (D.tensorPowerAt n)).IsQuasicoherent :=
  have := D.isQuasicoherent_gradedAt p 0
  have : (D.tensorPowerAt n).IsQuasicoherent := D.isQuasicoherent_tensorPower n
  Stacks.SheafOfModules.TensorProduct.isQuasicoherent_tensorSheaf' D.X.sheaf.obj
    D.X.ringCatSheaf.property (D.gradedAt p 0) (D.tensorPowerAt n)

end Stacks.LineBundle

end
