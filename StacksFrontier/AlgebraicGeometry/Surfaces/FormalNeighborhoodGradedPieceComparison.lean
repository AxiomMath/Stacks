module

public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Isomorphism
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.SumSequenceSections
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveThickeningSurjective
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveTwistSections
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveTwistSuccessor
public import StacksFrontier.AlgebraicGeometry.Surfaces.FormalNeighborhoodGradedPiece
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.SumKernelMap
public import StacksFrontier.AlgebraicGeometry.Surfaces.FormalNeighborhoodResidueMap

/-!
# The degreewise comparison of a graded piece with the sections of a twist

Let `E ⊆ X` be an exceptional curve of the first kind, presented as the projective line by
`e : 𝐏¹_k ≅ E`, let `D` be its ideal sheaf and let `A` be the ring of compatible global functions
on the infinitesimal thickenings `Eₙ₊₁ = (D ^ (n + 1)).subscheme`. The graded piece `Iₘ₊₁ / Iₘ₊₂`
of the projection-kernel filtration is the kernel of the restriction
`Γ(Eₘ₊₁, 𝒪) ⟶ Γ(Eₘ, 𝒪)`. This file identifies that kernel, elementwise, with
`H⁰(𝐏¹_k, 𝒪(m + 1))`:

`ρ : RingHom.ker (thickeningRestriction D m) ≅ Γ(𝐏¹_k, 𝒪(m + 1))`,

additively and semilinearly over the residue map `A ⟶ k`. Consequently, for an exceptional curve
of the first kind, spanning and independence of the degree-`(m + 1)` monomials in
[Stacks, Tag 0C2K] are one condition in each degree.

The kernel of the restriction is the image of the injective map
`Γ(X, 𝒪_X(-(m + 1)E)|_E) ⟶ Γ(Eₘ₊₁, 𝒪)` of [Stacks, Tag 0C4T]. These global sections are carried
to the projective line along `e`, and the pullback of the ideal sheaf is identified with the twist
`𝒪(m + 1)` by
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.curveTwistIso`.

## Main definitions

* `AlgebraicGeometry.Scheme.IdealSheafData.gradedPieceTwistSections`: the `k`-space
  `H⁰(𝐏¹_k, 𝒪(d))`, and `gradedPieceTwistSectionsBasis` its monomial basis indexed by
  `Fin (d + 1)`.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.curveSectionsIso`:
  `Γ(E, 𝒪_X(-(m + 1)E)|_E) ≅ H⁰(𝐏¹_k, 𝒪(m + 1))`.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.gradedPieceComparison`:
  the degreewise comparison `ρ`.

## Main results

* `Stacks.Divisors.thickeningRestriction_appTop_thickeningKernelMap` and
  `Stacks.Divisors.appTop_thickeningKernelMap_smul_eq_mul`: the kernel inclusion of
  [Stacks, Tag 0C4T] at the thickenings lands in the kernel of the restriction, and it is
  semilinear over the functions on the thickening.
* `AlgebraicGeometry.Scheme.IdealSheafData.coeffScalar_formalNeighborhoodResidue`: the residue of
  a compatible function is its restriction to `E`, read through `e`.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
  `.gradedPieceComparison_add`, `_smul`, `_eq_zero_iff` and `_surjective`: on the kernel of the
  restriction, `ρ` is additive, semilinear over the residue map, injective and surjective.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
  `.le_span_pow_sup_iff_coeff_mem_one`: for two elements of `I₁`, spanning and independence of the
  degree-`(m + 1)` monomials in them are equivalent.

## Implementation notes

* `AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodResidue` is unfolded by rewriting
  with `formalNeighborhoodResidue_apply`, never by `rfl`: definitional unfolding descends into the
  bijectivity proof inside `Stacks.ProjectiveSpace.Cohomology.coeffRingEquivGlobalSections` and
  exhausts the heartbeat budget. For the same reason `sectionsSubschemeRingEquivOfIso_apply` is
  stated over an arbitrary ideal sheaf and presentation and used as a rewrite rule.
* `Stacks.Divisors.IsEffectiveCartierDivisor D` is an instance binder of `curveSectionsIso` and the
  declarations after it: supplying that instance inside a `def` body over concrete objects is
  orders of magnitude slower.

## References

* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
* [Stacks Project, Tag 0C4T](https://stacks.math.columbia.edu/tag/0C4T)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SemistableReduction
open Stacks.ProjectiveSpace.Cohomology

universe u

attribute [local instance] Stacks.PullbackSheafTensor.monoidalModules

namespace Stacks.Divisors

open AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-! ### The sequence of Tag 0C4T at the thickenings of a divisor -/

/-- **The kernel inclusion lands in the kernel of the restriction.** For `C * D = D'`, the global
function on `D'` induced by `Stacks.Divisors.sumKernelMapOf` from a global section of the twisted
ideal sheaf restricts to zero along `D' ≤ D`. -/
public theorem appTop_inclusion_sumKernelMapOf_eq_zero (D C D' : X.IdealSheafData)
    (hD : IsEffectiveCartierDivisor D) (hsum : C * D = D') (hsub : D' ≤ D)
    (a : Γ((Scheme.Modules.pushforward C.subschemeι).obj
      ((Scheme.Modules.pullback C.subschemeι).obj (negativeTwist D)), (⊤ : X.Opens))) :
    (inclusion hsub).appTop ((sumKernelMapOf D C D' hD hsum).app ⊤ a) = 0 := by
  subst hsum
  rw [sumKernelMapOf_rfl, ← closedSubschemeRestriction_appTop,
    ← comp_app_apply (sumKernelMap D C hD) (closedSubschemeRestriction hsub) ⊤ a]
  have key : ∀ {M N : X.Modules} {g : M ⟶ N}, g = 0 → ∀ (U : X.Opens) (m : Γ(M, U)),
      g.app U m = 0 := by
    intro M N g hg U m
    subst hg
    simp
  exact key (sumKernelMap_comp_closedSubschemeRestriction D C hD hsub) ⊤ a

/-- **A global section of `𝒪_X(-(n + 1)E)|_E` induces a function on the `(n + 2)`-nd thickening
that restricts to zero on the `(n + 1)`-st.** -/
public theorem thickeningRestriction_appTop_thickeningKernelMap (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] (n : ℕ)
    (a : Γ((Scheme.Modules.pushforward D.subschemeι).obj
        ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (n + 1)))),
      (⊤ : X.Opens))) :
    thickeningRestriction D n ((thickeningKernelMap D n).app ⊤ a) = 0 := by
  rw [thickeningKernelMap_eq]
  exact appTop_inclusion_sumKernelMapOf_eq_zero (D ^ (n + 1)) D (D ^ (n + 2)) inferInstance
    (mul_pow_succ_eq D n) (pow_succ_le_pow_succ D (Nat.le_succ n)) a

/-- **The kernel inclusion is semilinear over the functions on the sum.** For `C * D = D'` and
`D' ≤ C`, a global function `t` on `D'` acting through its restriction to `C` is carried by
`Stacks.Divisors.sumKernelMapOf` to multiplication by `t`. -/
public theorem appTop_sumKernelMapOf_smul_eq_mul (D C D' : X.IdealSheafData)
    (hD : IsEffectiveCartierDivisor D) (hsum : C * D = D') (hsubC : D' ≤ C)
    (t : Γ(D'.subscheme, (⊤ : D'.subscheme.Opens)))
    (w : Γ((Scheme.Modules.pullback C.subschemeι).obj (negativeTwist D),
      (⊤ : C.subscheme.Opens)))
    {x : Γ(D'.subscheme, (⊤ : D'.subscheme.Opens))}
    (hx : (sumKernelMapOf D C D' hD hsum).app ⊤ w = x) :
    (sumKernelMapOf D C D' hD hsum).app ⊤ ((inclusion hsubC).appTop t • w) = t * x := by
  subst hsum
  rw [sumKernelMapOf_rfl] at hx ⊢
  exact appTop_sumKernelMap_smul_eq_mul D C hD t w hx

/-- **The kernel inclusion of [Stacks, Tag 0C4T] at the thickenings is semilinear over the
functions on the thickening.** A global function `t` on `Eₙ₊₂` acts on a global section of
`𝒪_X(-(n + 1)E)|_E` through its restriction to `E`, and the kernel inclusion carries that action
to multiplication by `t`. -/
public theorem appTop_thickeningKernelMap_smul_eq_mul (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] (n : ℕ) (hsub : D ^ (n + 2) ≤ D)
    (t : Γ(thickening D (n + 1), ⊤))
    (w : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (n + 1))),
      (⊤ : D.subscheme.Opens)))
    {x : Γ(thickening D (n + 1), ⊤)}
    (hx : (thickeningKernelMap D n).app ⊤ w = x) :
    (thickeningKernelMap D n).app ⊤ ((inclusion hsub).appTop t • w) = t * x := by
  rw [thickeningKernelMap_eq] at hx ⊢
  exact appTop_sumKernelMapOf_smul_eq_mul (D ^ (n + 1)) D (D ^ (n + 2)) inferInstance
    (mul_pow_succ_eq D n) hsub t w hx

/-! ### The kernel statements with their sections typed on the curve

The source of `Stacks.Divisors.thickeningKernelMap` is pushed forward from `E`, so its global
sections are spelled over the total open of `X`. The statements below have them spelled over the
total open of `E`: the two spellings are the same type, but only one of the two module structures
is found on each, and a rewrite whose motive mentions both is not type-correct at reducible
transparency. -/

/-- `Stacks.Divisors.injective_thickeningKernelMap_appTop` with its argument typed as a section on
the curve. -/
public theorem injective_curveAppTop_thickeningKernelMap (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] (n : ℕ) :
    Function.Injective fun a : Γ((Scheme.Modules.pullback D.subschemeι).obj
        (negativeTwist (D ^ (n + 1))), (⊤ : D.subscheme.Opens)) =>
      (thickeningKernelMap D n).app ⊤ a :=
  injective_thickeningKernelMap_appTop D n

/-- `Stacks.Divisors.exists_thickeningKernelMap_appTop_eq` with its witness typed as a section on
the curve. -/
public theorem exists_curveAppTop_thickeningKernelMap_eq (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] (n : ℕ) (x : Γ(thickening D (n + 1), ⊤))
    (hx : thickeningRestriction D n x = 0) :
    ∃ a : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (n + 1))),
      (⊤ : D.subscheme.Opens)), (thickeningKernelMap D n).app ⊤ a = x :=
  exists_thickeningKernelMap_appTop_eq D n x hx

/-- `Stacks.Divisors.thickeningRestriction_appTop_thickeningKernelMap` with its argument typed as
a section on the curve. -/
public theorem thickeningRestriction_curveAppTop_thickeningKernelMap (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] (n : ℕ)
    (a : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (n + 1))),
      (⊤ : D.subscheme.Opens))) :
    thickeningRestriction D n ((thickeningKernelMap D n).app ⊤ a) = 0 :=
  thickeningRestriction_appTop_thickeningKernelMap D n a

/-- The kernel inclusion is additive, on sections typed on the curve. -/
public theorem appTop_thickeningKernelMap_add (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] (n : ℕ)
    (a b : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (n + 1))),
      (⊤ : D.subscheme.Opens))) :
    (thickeningKernelMap D n).app ⊤ (a + b) =
      (thickeningKernelMap D n).app ⊤ a + (thickeningKernelMap D n).app ⊤ b :=
  map_add ((thickeningKernelMap D n).app ⊤).hom a b

/-- The kernel inclusion kills zero, on sections typed on the curve.

Implementation note: this is deduced from additivity, since `map_zero` makes the kernel compare the
`Zero` instances of the two spellings, which exceeds its reduction budget. -/
public theorem appTop_thickeningKernelMap_zero (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] (n : ℕ) :
    (thickeningKernelMap D n).app ⊤
        (0 : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (n + 1))),
          (⊤ : D.subscheme.Opens))) = 0 := by
  have hzz : (0 : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (n + 1))),
      (⊤ : D.subscheme.Opens))) + 0 = 0 := add_zero 0
  exact left_eq_add.mp
    ((congrArg (fun c => (thickeningKernelMap D n).app ⊤ c) hzz).symm.trans
      (appTop_thickeningKernelMap_add D n 0 0))

end Stacks.Divisors

namespace AlgebraicGeometry.Scheme.IdealSheafData

open Stacks.Divisors

variable {X : Scheme.{u}}

/-! ### The residue of a compatible function is its restriction to the curve -/

/-- The two spellings of the map on global functions of a morphism of schemes, through the
`CommRingCat` coercion and through `CommRingCat.Hom.hom`, agree. -/
public theorem appTop_apply_eq {A B : Scheme.{u}} (f : A ⟶ B)
    (y : Γ(B, (⊤ : B.Opens))) : f.appTop y = f.appTop.hom y := rfl

/-- **The inclusion of subschemes along an equality of ideal sheaves is the transport.** -/
public theorem inclusion_eq_eqToIso_symm_hom {I J : X.IdealSheafData} (hIJ : I = J) :
    inclusion (le_of_eq hIJ) =
      (eqToIso (congrArg (fun K : X.IdealSheafData => K.subscheme) hIJ)).symm.hom := by
  subst hIJ
  simp

/-- Restriction between nested closed subschemes composes, on global functions. -/
public theorem appTop_inclusion_trans {I J K : X.IdealSheafData} (h1 : I ≤ J) (h2 : J ≤ K)
    (x : Γ(I.subscheme, (⊤ : I.subscheme.Opens))) :
    (inclusion h2).appTop.hom ((inclusion h1).appTop.hom x) =
      (inclusion (h1.trans h2)).appTop.hom x := by
  rw [← inclusion_comp h1 h2, Scheme.Hom.comp_appTop]
  rfl

/-- **Restriction of a compatible function to the curve, factored through the first thickening.**
Restricting the `(i + 1)`-st component all the way to `E` is restricting the `0`-th component
along `D ^ 1 = D`. -/
public theorem appTop_inclusion_formalNeighborhoodProjection (D : X.IdealSheafData) {i : ℕ}
    (h1 : D ^ (i + 1) ≤ D ^ 1) (h2 : D ^ 1 ≤ D) (a : formalNeighborhoodRing D) :
    (inclusion h2).appTop.hom (formalNeighborhoodProjection D 0 a) =
      (inclusion (h1.trans h2)).appTop.hom (formalNeighborhoodProjection D i a) := by
  rw [← thickeningRestrictionLE_formalNeighborhoodProjection D (Nat.zero_le i) a]
  exact appTop_inclusion_trans h1 h2 _

variable {D : X.IdealSheafData} {k : Type u} [Field k]
  {e : projectiveLineProj k ≅ D.subscheme}

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The chosen presentation of the first thickening as a projective line, split into the
presentation of `E` and the transport along `D ^ 1 = D`. -/
public theorem appTop_hom_isoPowOne
    (y : Γ((D ^ 1).subscheme, (⊤ : (D ^ 1).subscheme.Opens))) :
    (e ≪≫ (eqToIso (congrArg (fun J : X.IdealSheafData => J.subscheme)
          (pow_one D))).symm).hom.appTop.hom y =
      e.hom.appTop.hom ((inclusion (le_of_eq (pow_one D))).appTop.hom y) := by
  rw [inclusion_eq_eqToIso_symm_hom (pow_one D), Iso.trans_hom]
  exact (Stacks.Thickenings.appTop_comp_apply e.hom _ y).symm

/-- **The identification of the functions on a projective line with the ground field, applied**,
for an arbitrary ideal sheaf `J` and an arbitrary presentation `e''` of its subscheme. -/
public theorem sectionsSubschemeRingEquivOfIso_apply (J : X.IdealSheafData)
    (e'' : projectiveLineProj k ≅ J.subscheme)
    (y : Γ(J.subscheme, (⊤ : J.subscheme.Opens))) :
    sectionsSubschemeRingEquivOfIso J k e'' y =
      (coeffRingEquivGlobalSections k 1).symm (e''.hom.appTop.hom y) := rfl

/-- **The residue map applied to a compatible function.** The value is the `0`-th component read
through the chosen presentation of the first thickening. -/
public theorem formalNeighborhoodResidue_apply (a : formalNeighborhoodRing D) :
    formalNeighborhoodResidue D k e a =
      sectionsSubschemeRingEquivOfIso (D ^ 1) k
        (e ≪≫ (eqToIso (congrArg (fun J : X.IdealSheafData => J.subscheme)
          (pow_one D))).symm) (formalNeighborhoodProjection D 0 a) := by
  rw [formalNeighborhoodResidue, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom]

/-- **The residue of a compatible function is its restriction to the curve, read through `e`.**
The scalar by which `AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodResidue` multiplies
is, as a global function on `𝐏¹_k`, the image under `e` of the restriction of the `(m + 1)`-st
component of the function to `E`. -/
public theorem coeffScalar_formalNeighborhoodResidue (m : ℕ) (hsub : D ^ (m + 2) ≤ D)
    (a : formalNeighborhoodRing D) :
    coeffScalar k 1 (formalNeighborhoodResidue D k e a) =
      e.hom.appTop.hom ((inclusion hsub).appTop.hom
        (formalNeighborhoodProjection D (m + 1) a)) := by
  have hstep : (inclusion (le_of_eq (pow_one D))).appTop.hom
        (formalNeighborhoodProjection D 0 a) =
      (inclusion hsub).appTop.hom (formalNeighborhoodProjection D (m + 1) a) :=
    appTop_inclusion_formalNeighborhoodProjection D
      (pow_succ_le_pow_succ D (Nat.zero_le (m + 1))) (le_of_eq (pow_one D)) a
  rw [formalNeighborhoodResidue_apply, sectionsSubschemeRingEquivOfIso_apply,
    appTop_hom_isoPowOne, hstep]
  exact (coeffRingEquivGlobalSections k 1).apply_symm_apply _

/-! ### The sections of a twist as a `k`-space with its monomial basis -/

/-- `H⁰(𝐏¹_k, 𝒪(d))` as a `k`-module, the coefficients acting through the structure morphism. -/
public def gradedPieceTwistSections (k : Type u) [Field k] (d : ℕ) : ModuleCat.{u} k :=
  (ModuleCat.restrictScalars.{u} (coeffScalar k 1)).obj
    ((Stacks.Cohomology.sectionsFunctor (projectiveLineProj k) ⊤).obj
      (ProjectiveSpectrum.Proj.twistingSheaf
        (MvPolynomial.homogeneousSubmodule (Fin 2) k) (d : ℤ)))

/-- **`H⁰(𝐏¹_k, 𝒪(d))` is free of rank `d + 1` over `k`**, on the monomial basis. This is
`AlgebraicGeometry.projectiveLineProjTwistSectionsBasis` with the index set written as
`Fin (d + 1)` for a natural number `d`. -/
public def gradedPieceTwistSectionsBasis (k : Type u) [Field k] (d : ℕ) :
    Module.Basis (Fin (d + 1)) k (gradedPieceTwistSections k d) :=
  (projectiveLineProjTwistSectionsBasis k (d : ℤ) (Int.natCast_nonneg d)).reindex
    (finCongr (by rw [Int.toNat_natCast]))

/-- **Scalars act on the sections of a twist through the structure morphism**: this is the
defining equation of the restriction of scalars along
`Stacks.ProjectiveSpace.Cohomology.coeffScalar`.

Implementation note: the scalar and the element are taken as variables with their defining
equations, since each ring and module involved has two spellings and the instance is found on only
one of them. -/
public theorem gradedPieceTwistSections_smul (k : Type u) [Field k] (d : ℕ) (c : k)
    (r : Γ(projectiveLineProj k, (⊤ : (projectiveLineProj k).Opens)))
    (hr : coeffScalar k 1 c = r) (w : gradedPieceTwistSections k d)
    (w' : (Stacks.Cohomology.sectionsFunctor (projectiveLineProj k) ⊤).obj
      (ProjectiveSpectrum.Proj.twistingSheaf
        (MvPolynomial.homogeneousSubmodule (Fin 2) k) (d : ℤ)))
    (hw : w = w') : c • w = r • w' := by
  subst hr
  subst hw
  rfl

/-! ### The degreewise comparison -/

namespace IsExceptionalCurveOfFirstKind

variable [IsEffectiveCartierDivisor D] (hE : IsExceptionalCurveOfFirstKind D k e)

/-- **`Γ(E, 𝒪_X(-(m + 1)E)|_E)` is `H⁰(𝐏¹_k, 𝒪(m + 1))`.** The unit of `e^* ⊣ e_*` is an
isomorphism along the isomorphism `e`, and the pullback of the restricted ideal sheaf is the
`(m + 1)`-st twist in that single degree, by the member of the family
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.curveTwistIso`. -/
public def curveSectionsIso (m : ℕ) :
    (Stacks.Cohomology.sectionsFunctor D.subscheme ⊤).obj
        ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (m + 1)))) ≅
      (ModuleCat.restrictScalars e.hom.appTop.hom).obj
        ((Stacks.Cohomology.sectionsFunctor (projectiveLineProj k) ⊤).obj
          (ProjectiveSpectrum.Proj.twistingSheaf
            (MvPolynomial.homogeneousSubmodule (Fin 2) k) ((m + 1 : ℕ) : ℤ))) :=
  Stacks.ClosedImmersion.sectionsIsoPullbackOfIsIso e.hom
      ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (m + 1)))) ≪≫
    (ModuleCat.restrictScalars e.hom.appTop.hom).mapIso
      ((Stacks.Cohomology.sectionsFunctor (projectiveLineProj k) ⊤).mapIso
        (hE.curveTwistIso (m + 1)))

/-- The underlying function of
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.curveSectionsIso`. -/
public def curveSections (m : ℕ) :
    Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (m + 1))),
        (⊤ : D.subscheme.Opens)) →
      (Stacks.Cohomology.sectionsFunctor (projectiveLineProj k) ⊤).obj
        (ProjectiveSpectrum.Proj.twistingSheaf
          (MvPolynomial.homogeneousSubmodule (Fin 2) k) ((m + 1 : ℕ) : ℤ)) :=
  fun w => (hE.curveSectionsIso m).hom.hom w

/-- `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.curveSections` is
additive. -/
public theorem curveSections_add (m : ℕ)
    (u v : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (m + 1))),
      (⊤ : D.subscheme.Opens))) :
    hE.curveSections m (u + v) = hE.curveSections m u + hE.curveSections m v :=
  map_add (hE.curveSectionsIso m).hom.hom u v

/-- `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.curveSections` maps
zero to zero. -/
public theorem curveSections_zero (m : ℕ) : hE.curveSections m 0 = 0 :=
  map_zero (hE.curveSectionsIso m).hom.hom

/-- `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.curveSections` is
bijective. -/
public theorem curveSections_bijective (m : ℕ) : Function.Bijective (hE.curveSections m) :=
  ConcreteCategory.bijective_of_isIso (hE.curveSectionsIso m).hom

/-- `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.curveSections` is
semilinear over the map `e.hom.appTop` on global functions. -/
public theorem curveSections_smul (m : ℕ) (s : Γ(D.subscheme, (⊤ : D.subscheme.Opens)))
    (w : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (m + 1))),
      (⊤ : D.subscheme.Opens))) :
    hE.curveSections m (s • w) = e.hom.appTop.hom s • hE.curveSections m w :=
  (hE.curveSectionsIso m).hom.hom.map_smul s w

/-- **The degreewise comparison of the graded piece `Iₘ₊₁ / Iₘ₊₂` with `H⁰(𝐏¹_k, 𝒪(m + 1))`.**

A global function on `Eₘ₊₁` restricting to zero on `Eₘ` is the image of a unique global section of
`𝒪_X(-(m + 1)E)|_E` under the kernel inclusion of [Stacks, Tag 0C4T]; this carries it to the
sections of the twist. Off the kernel of the restriction the value is whatever
`Function.invFun` returns. -/
public def gradedPieceComparison (m : ℕ) :
    Γ(thickening D (m + 1), ⊤) → gradedPieceTwistSections k (m + 1) :=
  fun z => hE.curveSections m
    (Function.invFun (fun a : Γ((Scheme.Modules.pullback D.subschemeι).obj
      (negativeTwist (D ^ (m + 1))), (⊤ : D.subscheme.Opens)) =>
        (thickeningKernelMap D m).app ⊤ a) z)

/-- On the image of the kernel inclusion the comparison is the identification of the sections. -/
public theorem gradedPieceComparison_appTop (m : ℕ)
    (a : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (m + 1))),
      (⊤ : D.subscheme.Opens))) :
    hE.gradedPieceComparison m ((thickeningKernelMap D m).app ⊤ a) = hE.curveSections m a :=
  congrArg (hE.curveSections m)
    (Function.leftInverse_invFun (injective_curveAppTop_thickeningKernelMap D m) a)

/-- **The comparison is additive on the kernel of the restriction.** -/
public theorem gradedPieceComparison_add (m : ℕ) {u v : Γ(thickening D (m + 1), ⊤)}
    (hu : thickeningRestriction D m u = 0) (hv : thickeningRestriction D m v = 0) :
    hE.gradedPieceComparison m (u + v) =
      hE.gradedPieceComparison m u + hE.gradedPieceComparison m v := by
  obtain ⟨a, ha⟩ := exists_curveAppTop_thickeningKernelMap_eq D m u hu
  obtain ⟨b, hb⟩ := exists_curveAppTop_thickeningKernelMap_eq D m v hv
  subst ha
  subst hb
  refine Eq.trans (congrArg (hE.gradedPieceComparison m)
    (appTop_thickeningKernelMap_add D m a b).symm) ?_
  rw [hE.gradedPieceComparison_appTop, hE.gradedPieceComparison_appTop,
    hE.gradedPieceComparison_appTop]
  exact hE.curveSections_add m a b

/-- **The comparison is semilinear over the residue map.** On the kernel of the restriction,
multiplying by the `(m + 1)`-st component of a compatible function is multiplying by its residue
in `k`. -/
public theorem gradedPieceComparison_smul (m : ℕ) (r : formalNeighborhoodRing D)
    {z : Γ(thickening D (m + 1), ⊤)} (hz : thickeningRestriction D m z = 0) :
    hE.gradedPieceComparison m (formalNeighborhoodProjection D (m + 1) r * z) =
      formalNeighborhoodResidue D k e r • hE.gradedPieceComparison m z := by
  obtain ⟨a, ha⟩ := exists_curveAppTop_thickeningKernelMap_eq D m z hz
  subst ha
  have hsub : D ^ (m + 2) ≤ D :=
    (pow_succ_le_pow_succ D (Nat.zero_le (m + 1))).trans (le_of_eq (pow_one D))
  refine Eq.trans (congrArg (hE.gradedPieceComparison m)
    (appTop_thickeningKernelMap_smul_eq_mul D m hsub
      (formalNeighborhoodProjection D (m + 1) r) a rfl).symm) ?_
  refine Eq.trans (hE.gradedPieceComparison_appTop m
    ((inclusion hsub).appTop (formalNeighborhoodProjection D (m + 1) r) • a)) ?_
  refine Eq.trans (hE.curveSections_smul m
    ((inclusion hsub).appTop (formalNeighborhoodProjection D (m + 1) r)) a) ?_
  rw [hE.gradedPieceComparison_appTop m a,
    appTop_apply_eq (inclusion hsub) (formalNeighborhoodProjection D (m + 1) r)]
  exact (gradedPieceTwistSections_smul k (m + 1) (formalNeighborhoodResidue D k e r)
    (e.hom.appTop.hom ((inclusion hsub).appTop.hom
      (formalNeighborhoodProjection D (m + 1) r)))
    (coeffScalar_formalNeighborhoodResidue m hsub r)
    (hE.curveSections m a) (hE.curveSections m a) rfl).symm

/-- **The comparison is injective on the kernel of the restriction.** -/
public theorem gradedPieceComparison_eq_zero_iff (m : ℕ) {z : Γ(thickening D (m + 1), ⊤)}
    (hz : thickeningRestriction D m z = 0) :
    hE.gradedPieceComparison m z = 0 ↔ z = 0 := by
  obtain ⟨a, ha⟩ := exists_curveAppTop_thickeningKernelMap_eq D m z hz
  subst ha
  rw [hE.gradedPieceComparison_appTop m a]
  exact ((hE.curveSections_bijective m).1.eq_iff' (hE.curveSections_zero m)).trans
    ((injective_curveAppTop_thickeningKernelMap D m).eq_iff'
      (appTop_thickeningKernelMap_zero D m)).symm

/-- **The comparison is onto `H⁰(𝐏¹_k, 𝒪(m + 1))` from the kernel of the restriction.** -/
public theorem gradedPieceComparison_surjective (m : ℕ) (w : gradedPieceTwistSections k (m + 1)) :
    ∃ z, thickeningRestriction D m z = 0 ∧ hE.gradedPieceComparison m z = w := by
  obtain ⟨a, ha⟩ := (hE.curveSections_bijective m).2 w
  exact ⟨(thickeningKernelMap D m).app ⊤ a,
    thickeningRestriction_curveAppTop_thickeningKernelMap D m a,
    (hE.gradedPieceComparison_appTop m a).trans ha⟩

end IsExceptionalCurveOfFirstKind

/-- **Spanning and independence of the degree-`(m + 1)` monomials are one condition, for an
exceptional curve of the first kind.** For `x, y ∈ I₁`, the filtration step `Iₘ₊₁` lies in
`(x, y) ^ (m + 1) ⊔ Iₘ₊₂` if and only if every combination of the degree-`(m + 1)` monomials in
`x, y` lying in `Iₘ₊₂` has all its coefficients in `I₁`. -/
public theorem IsExceptionalCurveOfFirstKind.le_span_pow_sup_iff_coeff_mem_one
    (hE : IsExceptionalCurveOfFirstKind D k e) {x y : formalNeighborhoodRing D}
    (hx : x ∈ formalNeighborhoodFiltration D 1) (hy : y ∈ formalNeighborhoodFiltration D 1)
    (m : ℕ) :
    formalNeighborhoodFiltration D (m + 1) ≤
        Ideal.span {x, y} ^ (m + 1) ⊔ formalNeighborhoodFiltration D (m + 1 + 1) ↔
      ∀ c : ℕ → formalNeighborhoodRing D,
        (∑ j ∈ Finset.range (m + 1 + 1), c j * genMonomial x y (m + 1) j) ∈
          formalNeighborhoodFiltration D (m + 1 + 1) →
        ∀ j ≤ m + 1, c j ∈ formalNeighborhoodFiltration D 1 :=
  have : IsEffectiveCartierDivisor D := hE.isEffectiveCartierDivisor
  le_span_pow_sup_iff_coeff_mem_one_of_gradedPiece D hE.surjective_thickeningRestriction
    (formalNeighborhoodResidue D k e)
    (surjective_formalNeighborhoodResidue D k (hE.surjective_formalNeighborhoodProjection 0) e)
    (ker_formalNeighborhoodResidue D k e) hx hy m (hE.gradedPieceComparison m)
    (fun hu hv => hE.gradedPieceComparison_add m hu hv)
    (fun r _ hz => hE.gradedPieceComparison_smul m r hz)
    (fun hz => hE.gradedPieceComparison_eq_zero_iff m hz)
    (hE.gradedPieceComparison_surjective m)
    (gradedPieceTwistSectionsBasis k (m + 1))

end AlgebraicGeometry.Scheme.IdealSheafData

end
