module

public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.AffineUnitSections
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.SumKernelMap
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.RestrictedIdealTensorSections
public import StacksFrontier.AlgebraicGeometry.Surfaces.ThickeningKernelFiltration

/-!
# The symbol of a product of two lifts is the restricted product of their symbols

`AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsHom` is the injection

`Γ(E, i^*ℐ_{D ^ (m + 1)}) ⟶ Γ(Eₘ₊₁, 𝒪)`

of [Stacks, Tag 0C4T], which identifies the graded piece `Kₘ / Kₘ₊₁` of the filtration of a
thickening with the global sections of a twist. The pairing those graded pieces carry is a
function of the two symbols, by
`AlgebraicGeometry.Scheme.IdealSheafData.exists_gradedSectionsHom_eq_mul`, but nothing so far
said *which* function. This file proves that it is
`Stacks.Divisors.restrictedIdealMulSections`:

for `u` a lift of a symbol `a` in degree `m` and `v` a lift of a symbol `b` in degree `n` to the
ambient thickening `E_{m+n+2}`, the symbol of `u v` is the restricted product of `a` and `b`.

That is `AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsHomOfEq_restrictedIdealMulSections`.

## Why it has to be checked on a cover

`gradedSectionsHom` exists only on *global* sections, and `Γ(X, ℐ_{D ^ m}) ⟶ Γ(E, i^*ℐ_{D ^ m})`
is not surjective — the `H¹` failure recorded in the module docstring of
`StacksFrontier/AlgebraicGeometry/Surfaces/ThickeningKernelFiltration.lean` — so a global section of
the twist is not the restriction of a section of the ideal sheaf and the identity cannot be read
off `Stacks.Divisors.sumKernelMap_app_restrictedIdealMulSections`, which is
about exactly those sections that are. Both sides of the identity are global functions on
`E_{m+n+2}`, so it suffices to check it on a cover, and the affine opens of `X` pull back to one.
Four local ingredients and the sheaf condition are what the proof uses.

## The four ingredients

**Sections do lift over an affine open of `X`.** That is
`Stacks.ClosedImmersion.surjective_unit_app_of_isAffineOpen`: the unit is an epimorphism along a
closed immersion and `Γ(U, -)` is exact on quasi-coherent modules for `U` affine, so over an
affine open of `X` — and not over an arbitrary open of `E` — a section of `i^*ℐ_I` *is* a
`Stacks.RingedSpace.pullbackUnit` section. `Stacks.Divisors.exists_pullbackUnit_eq` is that
statement for an ideal sheaf. This replaces the local generation of
`Stacks.PullbackUnitGenerators.exists_mem_span`, whose coefficients live in `Γ(E, 𝒪_E)` and would
have to be lifted to `Γ(X, 𝒪_X)` before they could act on `𝒪_{C + D}`.

**The injection is the value at `⊤` of a morphism of sheaves**, so it commutes with restriction:
`Stacks.Divisors.addEffectiveCartierDivisorSections_restrict`. Composed with
`Stacks.Divisors.sumKernelMap_app_pullbackUnit`, which holds over an arbitrary
open already, this computes the restriction of a graded symbol to `Eₙ₊₁ ∩ U` as the class of the
lifted section:
`AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsHom_restrict_of_pullbackUnit`.

**Multiplication is local.** Over an affine open of `X` the structure sheaf of a thickening is
an honest quotient, so the statement "a function agreeing with `σ` on `Eₘ₊₁` times one agreeing
with `τ` on `Eₙ₊₁` agrees with `σ τ` on `E_{m+n+2}`" is the ideal arithmetic
`J ^ (m + 2) · J ^ (n + 1) + J ^ (m + 1) · J ^ (n + 2) ⊆ J ^ (m + n + 3)`:
`AlgebraicGeometry.Scheme.IdealSheafData.subschemeι_app_mul_eq_of_sub_mem`. This is the local
form of `AlgebraicGeometry.Scheme.IdealSheafData.sub_mul_sub_mem_thickeningKernel`, whose own
statement is about global functions on one thickening and cannot be restricted to an open.

**The restricted multiplication is local too.**
`Stacks.Divisors.restrictedIdealMulSections` is the value at `⊤` of
`Stacks.Divisors.restrictedIdealTensorMulIso`, so it commutes with restriction, and
`Stacks.Divisors.restrictedIdealTensorMulIso_hom_app_pullbackUnit` already computes it over an
arbitrary open: `Stacks.Divisors.restrictedIdealMulSections_restrict_pullbackUnit`. The two
spellings of the tensor product are crossed only in the *statements* of the lemmas below, never
by a `rw`, for the reason recorded in the module docstring of
`StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.RestrictedIdealTensorSections`.

## The index of the product

`Stacks.Divisors.restrictedIdealMulSections` returns a section of `i^*ℐ_{I · J}`, and at
`I = D ^ (m + 1)`, `J = D ^ (n + 1)` the ideal sheaf `D ^ (m + 1) · D ^ (n + 1)` is not the term
`D ^ (q + 1)` for variable `m, n`. `AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsHomOfEq`
is therefore `gradedSectionsHom` with the divisor a free variable and an equation
`D · J = D ^ (N + 1)`, the shape of
`AlgebraicGeometry.Scheme.IdealSheafData.thickeningKernel_mul_le_of_eq`; no cast of a section
along an equality of ideal sheaves occurs anywhere.

## Main results

* `Stacks.ClosedImmersion.surjective_unit_app_of_isAffineOpen` (in
  `StacksFrontier.AlgebraicGeometry.ClosedPushforward.AffineUnitSections`) and
  `Stacks.Divisors.exists_pullbackUnit_eq` — sections of `i^*ℐ_I` lift over an affine open of
  `X`.
* `Stacks.Divisors.addEffectiveCartierDivisorSections_restrict` and
  `Stacks.Divisors.restrictedIdealMulSections_restrict_pullbackUnit` — the two maps of
  [Stacks, Tag 0C4T] and of the restricted multiplication commute with restriction, and are
  computed over an arbitrary open on the sections that lift there.
* `AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsHom_restrict_of_pullbackUnit` — the
  restriction of a graded symbol to `Eₘ₊₁ ∩ U` is the class of the lifted section.
* `AlgebraicGeometry.Scheme.IdealSheafData.subschemeι_app_mul_eq_of_sub_mem` — multiplication of
  symbols, affine-locally.
* `AlgebraicGeometry.Scheme.IdealSheafData`
  `.gradedSectionsHomOfEq_restrictedIdealMulSections` — **the symbol of a product of two lifts
  is `Stacks.Divisors.restrictedIdealMulSections` of the two symbols.**
* `AlgebraicGeometry.Scheme.IdealSheafData`
  `.mem_gradedSectionsDegreeOneProducts_of_gradedSectionsHom_eq` and
  `exists_mem_gradedSectionsDegreeOneProducts` — **the restricted product of a degree-one symbol
  with a degree-`p + 1` symbol is a symbol of a degree-one product**, that is a member of
  `AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsDegreeOneProducts`, the `hgen` input of
  `AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData`
  `.ofGradedSectionsDegreeOneGeneration`.

## The transport to `D ^ (q + 1)`, without a cast

`gradedSectionsDegreeOneProducts` is a set of sections of `i^*ℐ_{D ^ (p + 2)}`, while the
symbol of the product is produced at the divisor `D ^ (0 + 1) · D ^ (p + 1)` — the same ideal
sheaf, not the same term. The two results above cross between them with no cast of a section
along an equality of ideal sheaves: the section at `D ^ (p + 2)` is a free variable `c` and the
hypothesis is the equation identifying its symbol, and such a `c` exists because
`AlgebraicGeometry.Scheme.IdealSheafData.exists_gradedSectionsHom_eq_mul` already produces one
there whenever the transition maps are surjective.

## What this does not give

The other half of what [Stacks, Tag 0C2K] needs is not here: nothing in this file compares
`Stacks.Divisors.restrictedIdealMulSections` with the multiplication of the twists of `𝐏¹`. That
comparison is
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
`.prodTwistSection_restrictedIdealMulSections` in
`StacksFrontier/AlgebraicGeometry/Surfaces/ExceptionalCurveTwistMultiplicative.lean`, and with it
`hgen` is proved. Nothing here carries a `@[stacks]` attribute: this is a step in the proof of
Tag 0C2K, not one of its assertions.

## References

* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
* [Stacks Project, Tag 0C4T](https://stacks.math.columbia.edu/tag/0C4T)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite TopologicalSpace
open Stacks.RingedSpace Stacks.SheafOfModules.TensorStalkRingedSpace
open scoped TensorProduct

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}}

/-! ### Sections of the restricted ideal sheaf over an affine open of `X` -/

/-- **Over an affine open of `X` every section of `i^*ℐ_I` is a pullback-unit section.** The
ideal sheaf of a closed subscheme is quasi-coherent, by
`Stacks.AlgebraicGeometry.ClosedImmersionTFAE.isQuasicoherent_idealSheaf`, so this is
`Stacks.ClosedImmersion.surjective_unit_app_of_isAffineOpen`.

Over a general open of `C` the statement fails, which is why the identification of the graded
pieces is proved on the affine opens of `X` rather than on `C`. -/
theorem exists_pullbackUnit_eq (C I : X.IdealSheafData) (U : X.Opens) (hU : IsAffineOpen U)
    (x : ((Scheme.Modules.pullback C.subschemeι).obj (idealSheafOfModules I)).val.obj
      (op (C.subschemeι ⁻¹ᵁ U))) :
    ∃ s, pullbackUnit C.subschemeι.toLRSHom.toShHom (negativeTwist I) (op U) s = x :=
  @Stacks.ClosedImmersion.surjective_unit_app_of_isAffineOpen _ X C.subschemeι _
    (idealSheafOfModules I)
    (Stacks.AlgebraicGeometry.ClosedImmersionTFAE.isQuasicoherent_idealSheaf I.subschemeι)
    U hU x

/-! ### The injection of Tag 0C4T commutes with restriction -/

/-- **The injection of [Stacks, Tag 0C4T] on global sections commutes with restriction to an
open of `X`.** `Stacks.Divisors.addEffectiveCartierDivisorSections` is the value at `⊤` of the
morphism of sheaves `Stacks.Divisors.sumKernelMap`, so this is that morphism's
naturality, read through the two presentations of both sides. -/
theorem addEffectiveCartierDivisorSections_restrict (C D : X.IdealSheafData)
    (hD : IsEffectiveCartierDivisor D) (U : X.Opens)
    (x : Γ((Scheme.Modules.pullback C.subschemeι).obj (negativeTwist D),
      (⊤ : C.subscheme.Opens))) :
    ((C * D).subscheme.presheaf.map (homOfLE le_top).op).hom
        (addEffectiveCartierDivisorSections C D hD x) =
      ((sumKernelMap D C hD).val.app (op U)).hom
        (((Scheme.Modules.pullback C.subschemeι).obj (negativeTwist D)).val.map
          (homOfLE le_top).op x) :=
  closedSubschemeSectionsAddEquivAt_app_map C.subschemeι
    (sumKernelMap D C hD) (U := U) (V := ⊤) (homOfLE le_top) x

/-! ### The restricted multiplication commutes with restriction -/

attribute [local instance] Stacks.PullbackSheafTensor.monoidalSheafTensor

/-- **The restricted multiplication of global sections commutes with restriction to an open of
`X`.** `Stacks.Divisors.restrictedIdealMulSections` is the value at `⊤` of the morphism
`Stacks.Divisors.restrictedIdealTensorMulIso`, so this is that morphism's naturality. -/
theorem restrictedIdealMulSections_restrict (C I J : X.IdealSheafData)
    (hJ : IsEffectiveCartierDivisor J) (U : X.Opens)
    (a : Γ((pullbackFunctor C.subschemeι.toLRSHom.toShHom).obj (negativeTwist I),
      (⊤ : C.subscheme.Opens)))
    (b : Γ((pullbackFunctor C.subschemeι.toLRSHom.toShHom).obj (negativeTwist J),
      (⊤ : C.subscheme.Opens))) :
    ((pullbackFunctor C.subschemeι.toLRSHom.toShHom).obj (negativeTwist (I * J))).val.map
        (homOfLE (le_top (a := C.subschemeι ⁻¹ᵁ U))).op
        (restrictedIdealMulSections C I J hJ a b) =
      ((restrictedIdealTensorMulIso C I J hJ).hom.val.app (op (C.subschemeι ⁻¹ᵁ U))).hom
        (((pullbackFunctor C.subschemeι.toLRSHom.toShHom).obj (negativeTwist I) ⊗
            (pullbackFunctor C.subschemeι.toLRSHom.toShHom).obj (negativeTwist J)).val.map
          (homOfLE (le_top (a := C.subschemeι ⁻¹ᵁ U))).op
          (toTensorSheafSection C.subscheme.toRingedSpace
            ((pullbackFunctor C.subschemeι.toLRSHom.toShHom).obj (negativeTwist I))
            ((pullbackFunctor C.subschemeι.toLRSHom.toShHom).obj (negativeTwist J))
            (op (⊤ : C.subscheme.Opens)) (a ⊗ₜ b))) :=
  (PresheafOfModules.naturality_apply (restrictedIdealTensorMulIso C I J hJ).hom.val
    (homOfLE (le_top (a := C.subschemeι ⁻¹ᵁ U))).op _).symm

/-- The canonical section of the tensor product sheaf attached to a pure tensor commutes with
restriction, in the monoidal spelling the type of
`Stacks.Divisors.restrictedIdealTensorMulIso` uses. -/
theorem toTensorSheafSection_restrict (C I J : X.IdealSheafData) (U : X.Opens)
    (a : Γ((pullbackFunctor C.subschemeι.toLRSHom.toShHom).obj (negativeTwist I),
      (⊤ : C.subscheme.Opens)))
    (b : Γ((pullbackFunctor C.subschemeι.toLRSHom.toShHom).obj (negativeTwist J),
      (⊤ : C.subscheme.Opens))) :
    ((pullbackFunctor C.subschemeι.toLRSHom.toShHom).obj (negativeTwist I) ⊗
        (pullbackFunctor C.subschemeι.toLRSHom.toShHom).obj (negativeTwist J)).val.map
        (homOfLE (le_top (a := C.subschemeι ⁻¹ᵁ U))).op
        (toTensorSheafSection C.subscheme.toRingedSpace
          ((pullbackFunctor C.subschemeι.toLRSHom.toShHom).obj (negativeTwist I))
          ((pullbackFunctor C.subschemeι.toLRSHom.toShHom).obj (negativeTwist J))
          (op (⊤ : C.subscheme.Opens)) (a ⊗ₜ b)) =
      toTensorSheafSection C.subscheme.toRingedSpace
        ((pullbackFunctor C.subschemeι.toLRSHom.toShHom).obj (negativeTwist I))
        ((pullbackFunctor C.subschemeι.toLRSHom.toShHom).obj (negativeTwist J))
        (op (C.subschemeι ⁻¹ᵁ U))
        (((pullbackFunctor C.subschemeι.toLRSHom.toShHom).obj (negativeTwist I)).val.map
            (homOfLE (le_top (a := C.subschemeι ⁻¹ᵁ U))).op a ⊗ₜ
          ((pullbackFunctor C.subschemeι.toLRSHom.toShHom).obj (negativeTwist J)).val.map
            (homOfLE (le_top (a := C.subschemeι ⁻¹ᵁ U))).op b) :=
  Stacks.Tag01VSPullbackTensor.toTensorSheafSection_presheaf_map
    ((pullbackFunctor C.subschemeι.toLRSHom.toShHom).obj (negativeTwist I))
    ((pullbackFunctor C.subschemeι.toLRSHom.toShHom).obj (negativeTwist J))
    (homOfLE (le_top (a := C.subschemeι ⁻¹ᵁ U))) a b

/-- **The restricted multiplication of two global sections, read over an open on which both
lift.** If `a` restricts over `U` to the pullback-unit section of `s` and `b` to that of `t`,
then their restricted product restricts to the pullback-unit section of the product `s t` inside
`ℐ_{I · J}`.

This is `Stacks.Divisors.restrictedIdealTensorMulIso_hom_app_pullbackUnit`, which already holds
over an arbitrary open, preceded by the naturality of the isomorphism and of
`Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection`. Every step is a term: no
`rw` crosses the two spellings of the tensor product. -/
theorem restrictedIdealMulSections_restrict_pullbackUnit (C I J : X.IdealSheafData)
    (hJ : IsEffectiveCartierDivisor J) (U : X.Opens)
    (a : Γ((pullbackFunctor C.subschemeι.toLRSHom.toShHom).obj (negativeTwist I),
      (⊤ : C.subscheme.Opens)))
    (b : Γ((pullbackFunctor C.subschemeι.toLRSHom.toShHom).obj (negativeTwist J),
      (⊤ : C.subscheme.Opens)))
    (s : (idealSheafOfModules I).val.obj (op U)) (t : (idealSheafOfModules J).val.obj (op U))
    (ha : ((pullbackFunctor C.subschemeι.toLRSHom.toShHom).obj (negativeTwist I)).val.map
        (homOfLE (le_top (a := C.subschemeι ⁻¹ᵁ U))).op a =
      pullbackUnit C.subschemeι.toLRSHom.toShHom (negativeTwist I) (op U) s)
    (hb : ((pullbackFunctor C.subschemeι.toLRSHom.toShHom).obj (negativeTwist J)).val.map
        (homOfLE (le_top (a := C.subschemeι ⁻¹ᵁ U))).op b =
      pullbackUnit C.subschemeι.toLRSHom.toShHom (negativeTwist J) (op U) t) :
    ((pullbackFunctor C.subschemeι.toLRSHom.toShHom).obj (negativeTwist (I * J))).val.map
        (homOfLE (le_top (a := C.subschemeι ⁻¹ᵁ U))).op
        (restrictedIdealMulSections C I J hJ a b) =
      pullbackUnit C.subschemeι.toLRSHom.toShHom (negativeTwist (I * J)) (op U)
        (((idealTensorMul I J).val.app (op U)).hom
          (toTensorSheafSection X.toRingedSpace (idealSheafOfModules I)
            (idealSheafOfModules J) (op U) (s ⊗ₜ t))) := by
  refine Eq.trans (restrictedIdealMulSections_restrict C I J hJ U a b) ?_
  refine Eq.trans (congrArg (((restrictedIdealTensorMulIso C I J hJ).hom.val.app
    (op (C.subschemeι ⁻¹ᵁ U))).hom) (toTensorSheafSection_restrict C I J U a b)) ?_
  refine Eq.trans (congrArg (fun z => ((restrictedIdealTensorMulIso C I J hJ).hom.val.app
      (op (C.subschemeι ⁻¹ᵁ U))).hom
      (toTensorSheafSection C.subscheme.toRingedSpace
        ((pullbackFunctor C.subschemeι.toLRSHom.toShHom).obj (negativeTwist I))
        ((pullbackFunctor C.subschemeι.toLRSHom.toShHom).obj (negativeTwist J))
        (op (C.subschemeι ⁻¹ᵁ U)) z))
    (congrArg₂ (· ⊗ₜ ·) ha hb)) ?_
  exact restrictedIdealTensorMulIso_hom_app_pullbackUnit C I J hJ (op U) s t

end Stacks.Divisors

namespace AlgebraicGeometry.Scheme.IdealSheafData

open Stacks.Divisors

attribute [local instance] Stacks.PullbackSheafTensor.monoidalSheafTensor

variable {X : Scheme.{u}}

/-! ### The graded symbol, restricted to an open of `X` -/

/-- The restriction to `U` of a lifted section of `ℐ_J`, seen in `E_{N+1}`, is the restriction of
the image of the global section `x` under the injection of Tag 0C4T. -/
private theorem subschemeι_app_idealSheafSection_eq_restrict (D J : X.IdealSheafData)
    [IsEffectiveCartierDivisor J] {N : ℕ} (h : D * J = D ^ (N + 1)) (U : X.Opens)
    (x : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist J),
      (⊤ : D.subscheme.Opens)))
    (s : (idealSheafOfModules J).val.obj (op U))
    (hx : ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist J)).val.map
        (homOfLE le_top).op x =
      pullbackUnit D.subschemeι.toLRSHom.toShHom (negativeTwist J) (op U) s) :
    ((D ^ (N + 1)).subschemeι.app U).hom (idealSheafSection J s) =
      ((D ^ (N + 1)).subscheme.presheaf.map (homOfLE le_top).op).hom
        ((inclusion h.le).appTop.hom (addEffectiveCartierDivisorSections D J inferInstance x)) := by
  refine subschemeι_app_eq_restrict_inclusion_appTop h.le U
    (addEffectiveCartierDivisorSections D J inferInstance x) _ ?_
  refine Eq.trans ?_ (addEffectiveCartierDivisorSections_restrict D J inferInstance U x).symm
  refine Eq.trans (sumKernelMap_app_pullbackUnit D J inferInstance U s).symm ?_
  exact congrArg ((sumKernelMap J D inferInstance).val.app (op U)).hom hx.symm

/-- **The restriction of a graded symbol to `Eₙ₊₁ ∩ U`, when the symbol lifts over `U`.** If the
section `x` of `i^*ℐ_{D ^ (n + 1)}` restricts over `U` to the pullback-unit section of
`s : ℐ_{D ^ (n + 1)}(U)`, then the symbol `gradedSectionsHom D n x` restricts to the class of `s`
in `Γ(Eₙ₊₁ ∩ U, 𝒪)`.

This is `Stacks.Divisors.sumKernelMap_app_pullbackUnit`, which already holds
over an arbitrary open, carried along the naturality of
`Stacks.Divisors.addEffectiveCartierDivisorSections` and then along the equality
`D · D ^ (n + 1) = D ^ (n + 2)` by
`Stacks.Divisors.subschemeι_app_eq_restrict_inclusion_appTop`. -/
theorem gradedSectionsHom_restrict_of_pullbackUnit (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] (n : ℕ) (U : X.Opens)
    (x : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (n + 1))),
      (⊤ : D.subscheme.Opens)))
    (s : (idealSheafOfModules (D ^ (n + 1))).val.obj (op U))
    (hx : ((Scheme.Modules.pullback D.subschemeι).obj
        (negativeTwist (D ^ (n + 1)))).val.map (homOfLE le_top).op x =
      pullbackUnit D.subschemeι.toLRSHom.toShHom (negativeTwist (D ^ (n + 1))) (op U) s) :
    ((D ^ (n + 2)).subschemeι.app U).hom (idealSheafSection (D ^ (n + 1)) s) =
      ((D ^ (n + 2)).subscheme.presheaf.map (homOfLE le_top).op).hom
        (gradedSectionsHom D n x) :=
  subschemeι_app_idealSheafSection_eq_restrict D (D ^ (n + 1)) (mul_pow_succ_eq D n) U x s hx

/-! ### The graded symbol with the divisor a free variable -/

/-- **`AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsHom` with the divisor a free
variable and an equation**, rather than the term `D ^ (n + 1)`.

A consumer whose divisor is a product `D ^ (m + 1) · D ^ (n + 1)` — the output type of
`Stacks.Divisors.restrictedIdealMulSections` — would otherwise have to transport a section along
an equality of ideal sheaves, since `D ^ (m + 1) · D ^ (n + 1)` is not the term `D ^ (q + 1)` for
variable `m, n`. This is the shape of
`AlgebraicGeometry.Scheme.IdealSheafData.thickeningKernel_mul_le_of_eq`, for the same reason. -/
def gradedSectionsHomOfEq (D J : X.IdealSheafData) [IsEffectiveCartierDivisor J] {N : ℕ}
    (h : D * J = D ^ (N + 1)) :
    Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist J),
        (⊤ : D.subscheme.Opens)) →+ Γ(thickening D N, ⊤) :=
  ((inclusion h.le).appTop.hom.toAddMonoidHom).comp
    (addEffectiveCartierDivisorSections D J inferInstance)

/-- At the divisor `D ^ (n + 1)` the free-variable shape is
`AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsHom` itself. -/
theorem gradedSectionsHomOfEq_pow (D : X.IdealSheafData) [IsEffectiveCartierDivisor D] (n : ℕ)
    (x : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (n + 1))),
      (⊤ : D.subscheme.Opens))) :
    gradedSectionsHomOfEq D (D ^ (n + 1)) (Stacks.Divisors.mul_pow_succ_eq D n) x =
      gradedSectionsHom D n x :=
  rfl

/-- The restriction of a symbol in the free-variable shape to `E_{N+1} ∩ U`, when the section
lifts over `U`: `gradedSectionsHom_restrict_of_pullbackUnit` with the divisor free. -/
theorem gradedSectionsHomOfEq_restrict_of_pullbackUnit (D J : X.IdealSheafData)
    [IsEffectiveCartierDivisor J] {N : ℕ} (h : D * J = D ^ (N + 1)) (U : X.Opens)
    (x : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist J),
      (⊤ : D.subscheme.Opens)))
    (s : (idealSheafOfModules J).val.obj (op U))
    (hx : ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist J)).val.map
        (homOfLE le_top).op x =
      pullbackUnit D.subschemeι.toLRSHom.toShHom (negativeTwist J) (op U) s) :
    ((D ^ (N + 1)).subschemeι.app U).hom (idealSheafSection J s) =
      ((D ^ (N + 1)).subscheme.presheaf.map (homOfLE le_top).op).hom
        (gradedSectionsHomOfEq D J h x) :=
  subschemeι_app_idealSheafSection_eq_restrict D J h U x s hx

/-! ### Multiplicativity, affine-locally -/

/-- **The local form of multiplicativity of the thickening filtration.** Over an affine open `U`
of `X` the structure sheaf of a thickening is the quotient of `Γ(X, U)` by a power of the ideal,
so if `u` and `σ ∈ ℐ_{D ^ (m + 1)}(U)` agree on `Eₘ₊₁ ∩ U` and `v` and
`τ ∈ ℐ_{D ^ (n + 1)}(U)` agree on `Eₙ₊₁ ∩ U`, then `u v` and `σ τ` agree on `E_{m+n+2} ∩ U`.

The whole content is the ideal arithmetic
`J ^ (m + 2) · J ^ (n + 1) + J ^ (m + 1) · J ^ (n + 2) ⊆ J ^ (m + n + 3)`, and there is no
hypothesis on `D` or on `X` whatever. Unlike
`AlgebraicGeometry.Scheme.IdealSheafData.sub_mul_sub_mem_thickeningKernel`, which says the same
thing about the global functions on one fixed ambient thickening, both sides here are sections
over an open and so can be glued.

The exponent of the target is a free variable with an equation for the reason recorded on
`AlgebraicGeometry.Scheme.IdealSheafData.thickeningKernel_mul_le_of_eq`. -/
theorem subschemeι_app_mul_eq_of_sub_mem (D : X.IdealSheafData) (U : X.affineOpens) {m n k : ℕ}
    (hk : k = m + n + 3) {u v σ τ : Γ(X, (U : X.Opens))}
    (hσ : σ ∈ (D ^ (m + 1)).ideal U) (hτ : τ ∈ (D ^ (n + 1)).ideal U)
    (hu : ((D ^ (m + 2)).subschemeι.app U.1).hom u
      = ((D ^ (m + 2)).subschemeι.app U.1).hom σ)
    (hv : ((D ^ (n + 2)).subschemeι.app U.1).hom v
      = ((D ^ (n + 2)).subschemeι.app U.1).hom τ) :
    ((D ^ k).subschemeι.app U.1).hom (u * v)
      = ((D ^ k).subschemeι.app U.1).hom (σ * τ) := by
  subst hk
  have mem : ∀ (k : ℕ) {a b : Γ(X, (U : X.Opens))},
      ((D ^ k).subschemeι.app U.1).hom a = ((D ^ k).subschemeι.app U.1).hom b →
      a - b ∈ (D ^ k).ideal U := by
    intro k a b hab
    rw [← ker_subschemeι_app (D ^ k) U, RingHom.mem_ker, map_sub, hab, sub_self]
  have hu' := mem (m + 2) hu
  have hv' := mem (n + 2) hv
  simp only [ideal_pow, Pi.pow_apply] at hσ hτ hu' hv' ⊢
  have hvmem : v ∈ D.ideal U ^ (n + 1) := by
    have hvv : v = (v - τ) + τ := by ring
    rw [hvv]
    exact Ideal.add_mem _ (Ideal.pow_le_pow_right (show n + 1 ≤ n + 2 by omega) hv') hτ
  have hleft : D.ideal U ^ (m + 2) * D.ideal U ^ (n + 1) ≤ D.ideal U ^ (m + n + 3) :=
    le_of_eq (Eq.trans (pow_add (D.ideal U) (m + 2) (n + 1)).symm
      (congrArg (D.ideal U ^ ·) (by omega)))
  have hright : D.ideal U ^ (m + 1) * D.ideal U ^ (n + 2) ≤ D.ideal U ^ (m + n + 3) :=
    le_of_eq (Eq.trans (pow_add (D.ideal U) (m + 1) (n + 2)).symm
      (congrArg (D.ideal U ^ ·) (by omega)))
  have hdiff : u * v - σ * τ ∈ D.ideal U ^ (m + n + 3) := by
    have hsum : u * v - σ * τ = (u - σ) * v + σ * (v - τ) := by ring
    rw [hsum]
    exact Ideal.add_mem _ (hleft (Ideal.mul_mem_mul hu' hvmem))
      (hright (Ideal.mul_mem_mul hσ hv'))
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, ker_subschemeι_app]
  simpa only [ideal_pow, Pi.pow_apply] using hdiff

/-! ### The symbol of a product of two lifts -/

/-- **The symbol of a product of two lifts is the restricted product of their symbols.**

Let `a` be a global section of `𝒪_X(-D ^ (m + 1))|_E` and `b` one of `𝒪_X(-D ^ (n + 1))|_E`, and
let `u` and `v` be lifts of their symbols to the ambient thickening `E_N`, `N = m + n + 2`. Then
the symbol of `u v` is `Stacks.Divisors.restrictedIdealMulSections a b`.

This is the identification of the pairing of the graded pieces that
`AlgebraicGeometry.Scheme.IdealSheafData.exists_gradedSectionsHom_eq_mul` leaves unnamed: there
the product of two lifts was shown to be the symbol of *some* section depending only on the two
symbols, and here that section is computed.

The identity is one of global functions on `E_N`, and both `gradedSectionsHom` and
`Stacks.Divisors.restrictedIdealMulSections` exist only on global sections, so it is checked on
the affine opens of `X`, which pull back to a cover of `E_N`. Over such an open `U` the sections
`a` and `b` are pullback-unit sections of `s` and `t`
(`Stacks.Divisors.exists_pullbackUnit_eq`); the left-hand side restricts to the class of `s t`
(`gradedSectionsHom_restrict_of_pullbackUnit` and
`Stacks.Divisors.restrictedIdealMulSections_restrict_pullbackUnit`); and `u` and `v` are
represented over `U` by sections of `𝒪_X` agreeing with `s` and with `t` on `Eₘ₊₁` and `Eₙ₊₁`, so
their product agrees with `s t` on `E_N` by `subschemeι_app_mul_eq_of_sub_mem`.

The divisor of the target is the product `D ^ (m + 1) · D ^ (n + 1)` — the output type of
`Stacks.Divisors.restrictedIdealMulSections` — with an equation `D · (D ^ (m + 1) · D ^ (n + 1))
= D ^ (N + 1)`, rather than the term `D ^ (N + 1)`; no section is transported along an equality
of ideal sheaves. -/
theorem gradedSectionsHomOfEq_restrictedIdealMulSections (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] {m n N : ℕ} (hN : N = m + n + 2)
    (hmul : D * (D ^ (m + 1) * D ^ (n + 1)) = D ^ (N + 1))
    (hm1 : m + 1 ≤ N) (hn1 : n + 1 ≤ N)
    (a : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (m + 1))),
      (⊤ : D.subscheme.Opens)))
    (b : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (n + 1))),
      (⊤ : D.subscheme.Opens)))
    (u v : Γ(thickening D N, ⊤))
    (hu : thickeningRestrictionLE D hm1 u = gradedSectionsHom D m a)
    (hv : thickeningRestrictionLE D hn1 v = gradedSectionsHom D n b) :
    gradedSectionsHomOfEq D (D ^ (m + 1) * D ^ (n + 1)) hmul
      (restrictedIdealMulSections D (D ^ (m + 1)) (D ^ (n + 1)) inferInstance a b) = u * v := by
  refine (D ^ (N + 1)).subscheme.sheaf.eq_of_locally_eq'
    (fun U : X.affineOpens => (D ^ (N + 1)).subschemeι ⁻¹ᵁ U.1) ⊤ (fun _ => homOfLE le_top)
    (le_of_eq ((D ^ (N + 1)).subschemeι.iSup_preimage_eq_top
      (iSup_affineOpens_eq_top X)).symm) _ (u * v) ?_
  intro U
  obtain ⟨s, hs⟩ := exists_pullbackUnit_eq D (D ^ (m + 1)) U.1 U.2
    (((Scheme.Modules.pullback D.subschemeι).obj
      (negativeTwist (D ^ (m + 1)))).val.map (homOfLE le_top).op a)
  obtain ⟨t, ht⟩ := exists_pullbackUnit_eq D (D ^ (n + 1)) U.1 U.2
    (((Scheme.Modules.pullback D.subschemeι).obj
      (negativeTwist (D ^ (n + 1)))).val.map (homOfLE le_top).op b)
  obtain ⟨uu, huu⟩ := (D ^ (N + 1)).subschemeι_app_surjective U
    (((D ^ (N + 1)).subscheme.presheaf.map (homOfLE le_top).op).hom u)
  obtain ⟨vv, hvv⟩ := (D ^ (N + 1)).subschemeι_app_surjective U
    (((D ^ (N + 1)).subscheme.presheaf.map (homOfLE le_top).op).hom v)
  have huu' : ((D ^ (N + 1)).subschemeι.app U.1).hom uu =
      ((D ^ (N + 1)).subscheme.presheaf.map (homOfLE le_top).op).hom u := huu
  have hvv' : ((D ^ (N + 1)).subschemeι.app U.1).hom vv =
      ((D ^ (N + 1)).subscheme.presheaf.map (homOfLE le_top).op).hom v := hvv
  -- Over `U` the left-hand side is the class of the product of the two lifted sections.
  have hlhs : ((D ^ (N + 1)).subschemeι.app U.1).hom
        (idealSheafSection (D ^ (m + 1)) s * idealSheafSection (D ^ (n + 1)) t) =
      ((D ^ (N + 1)).subscheme.presheaf.map (homOfLE le_top).op).hom
        (gradedSectionsHomOfEq D (D ^ (m + 1) * D ^ (n + 1)) hmul
          (restrictedIdealMulSections D (D ^ (m + 1)) (D ^ (n + 1)) inferInstance a b)) := by
    refine Eq.trans (congrArg ((D ^ (N + 1)).subschemeι.app U.1).hom
      (Eq.trans (idealSheafSection_idealTensorMul (D ^ (m + 1)) (D ^ (n + 1)) U.1 _)
        (idealTensorToUnit_app_tmul (D ^ (m + 1)) (D ^ (n + 1)) U.1 s t)).symm) ?_
    exact gradedSectionsHomOfEq_restrict_of_pullbackUnit D (D ^ (m + 1) * D ^ (n + 1)) hmul U.1 _
      _ (restrictedIdealMulSections_restrict_pullbackUnit D (D ^ (m + 1)) (D ^ (n + 1))
        inferInstance U.1 a b s t hs.symm ht.symm)
  -- Each factor is represented over `U` by a section agreeing with its symbol's lift.
  have hfac : ∀ (j : ℕ) (hj : j + 1 ≤ N) (w : Γ(thickening D N, ⊤)) (ww : Γ(X, U.1))
      (c : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (j + 1))),
        (⊤ : D.subscheme.Opens)))
      (y : (idealSheafOfModules (D ^ (j + 1))).val.obj (op U.1)),
      ((D ^ (N + 1)).subschemeι.app U.1).hom ww
        = ((D ^ (N + 1)).subscheme.presheaf.map (homOfLE le_top).op).hom w →
      thickeningRestrictionLE D hj w = gradedSectionsHom D j c →
      ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (j + 1)))).val.map
          (homOfLE le_top).op c =
        pullbackUnit D.subschemeι.toLRSHom.toShHom (negativeTwist (D ^ (j + 1))) (op U.1) y →
      ((D ^ (j + 2)).subschemeι.app U.1).hom ww
        = ((D ^ (j + 2)).subschemeι.app U.1).hom (idealSheafSection (D ^ (j + 1)) y) := by
    intro j hj w ww c y hww hw hy
    refine Eq.trans (subschemeι_app_eq_restrict_inclusion_appTop
      (pow_succ_le_pow_succ D hj) U.1 w ww hww) ?_
    refine Eq.trans (congrArg ((D ^ (j + 2)).subscheme.presheaf.map (homOfLE le_top).op).hom
      hw) ?_
    exact (gradedSectionsHom_restrict_of_pullbackUnit D j U.1 c y hy).symm
  have hum := hfac m hm1 u uu a s huu' hu hs.symm
  have hvm := hfac n hn1 v vv b t hvv' hv ht.symm
  -- And the product does too, by the affine-local multiplication of symbols.
  refine Eq.trans hlhs.symm ?_
  refine Eq.trans ?_ (Eq.trans (congrArg₂ (· * ·) huu' hvv')
    (map_mul ((D ^ (N + 1)).subscheme.presheaf.map (homOfLE le_top).op).hom u v).symm)
  refine Eq.trans ?_ (map_mul ((D ^ (N + 1)).subschemeι.app U.1).hom uu vv)
  refine (subschemeι_app_mul_eq_of_sub_mem D U (by omega) ?_ ?_ hum hvm).symm
  · exact (mem_ideal_iff_exists_idealSheafSection (D ^ (m + 1)) U _).2 ⟨s, rfl⟩
  · exact (mem_ideal_iff_exists_idealSheafSection (D ^ (n + 1)) U _).2 ⟨t, rfl⟩

/-! ### The symbols of the degree-one products -/

/-- The equation `AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsHomOfEq` asks of the
divisor `D ^ (0 + 1) · D ^ (p + 1)` — the one
`Stacks.Divisors.restrictedIdealMulSections` produces at `m = 0`, `n = p` — when the ambient
thickening is `E_{p+2}`: summed with `D` it is the `(p + 3)`-rd power. -/
theorem self_mul_pow_one_mul_pow_succ (D : X.IdealSheafData) (p : ℕ) :
    D * (D ^ (0 + 1) * D ^ (p + 1)) = D ^ (p + 1 + 1 + 1) :=
  have h : D ^ (0 + 1) * D ^ (p + 1) = D ^ (p + 1 + 1) :=
    Eq.trans (pow_add D (0 + 1) (p + 1)).symm
      (congrArg (fun i => D ^ i) (show 0 + 1 + (p + 1) = p + 1 + 1 by omega))
  Eq.trans (Eq.trans (congrArg (fun y => D * y) h) (Stacks.Divisors.mul_pow_succ_eq D (p + 1)))
    (congrArg (fun i => D ^ i) (show p + 1 + 2 = p + 1 + 1 + 1 by omega))

/-- **The restricted product of a degree-one symbol with a degree-`p + 1` symbol is a symbol of
a degree-one product.**

`AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsDegreeOneProducts` is a set of global
sections of `𝒪_X(-D ^ (p + 2))|_E`, while
`AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsHomOfEq_restrictedIdealMulSections`
produces its section at the divisor `D ^ (0 + 1) · D ^ (p + 1)`, which is the same ideal sheaf
but not the same term. The passage between them is made here with no cast: the section `c` of
`i^*ℐ_{D ^ (p + 2)}` is a free variable, and the hypothesis is the equation identifying its
symbol with the symbol of the restricted product — the discipline recorded on
`AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsHomOfEq`.

Such a `c` exists, and is unique by
`AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsHom_injective`;
`AlgebraicGeometry.Scheme.IdealSheafData.exists_mem_gradedSectionsDegreeOneProducts` produces
it. There is no hypothesis on `D` or on `X` here beyond the effective Cartier instance, and in
particular no surjectivity of the transition maps: the lifts `u` and `v` are universally
quantified in the set, so if none exists the membership is vacuous and if one does the symbol of
the product is already determined by Tag 0C4T. -/
theorem mem_gradedSectionsDegreeOneProducts_of_gradedSectionsHom_eq (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] {p : ℕ}
    (a : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (0 + 1))),
      (⊤ : D.subscheme.Opens)))
    (b : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (p + 1))),
      (⊤ : D.subscheme.Opens)))
    (c : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (p + 1 + 1))),
      (⊤ : D.subscheme.Opens)))
    (hc : gradedSectionsHom D (p + 1) c =
      gradedSectionsHomOfEq D (D ^ (0 + 1) * D ^ (p + 1)) (self_mul_pow_one_mul_pow_succ D p)
        (restrictedIdealMulSections D (D ^ (0 + 1)) (D ^ (p + 1)) inferInstance a b)) :
    c ∈ gradedSectionsDegreeOneProducts D p :=
  ⟨a, b, fun u v hu hv => Eq.trans hc
    (gradedSectionsHomOfEq_restrictedIdealMulSections D (m := 0) (n := p) (N := p + 1 + 1)
      (by omega) (self_mul_pow_one_mul_pow_succ D p) (by omega) (by omega) a b u v hu hv)⟩

/-- **The restricted product of two symbols is transported to the degree-one products.**

For every degree-one symbol `a` and degree-`p + 1` symbol `b` there is a global section `c` of
`𝒪_X(-D ^ (p + 2))|_E` whose symbol is the symbol of
`Stacks.Divisors.restrictedIdealMulSections a b`, and that `c` lies in
`AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsDegreeOneProducts`. This is the transport
along `D ^ (0 + 1) · D ^ (p + 1) = D ^ (p + 2)` carried out by the surjectivity of the
transition maps rather than by a cast: the section is obtained from
`AlgebraicGeometry.Scheme.IdealSheafData.exists_gradedSectionsHom_eq_mul`, already at the
divisor `D ^ (p + 2)`, and
`AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsHomOfEq_restrictedIdealMulSections`
identifies its symbol.

It is unique, by
`AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsHom_injective`, so the conjunction is a
description of one section and not a choice. -/
theorem exists_mem_gradedSectionsDegreeOneProducts (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D]
    (hsurj : ∀ j, Function.Surjective (thickeningRestriction D j)) (p : ℕ)
    (a : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (0 + 1))),
      (⊤ : D.subscheme.Opens)))
    (b : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (p + 1))),
      (⊤ : D.subscheme.Opens))) :
    ∃ c ∈ gradedSectionsDegreeOneProducts D p,
      gradedSectionsHom D (p + 1) c =
        gradedSectionsHomOfEq D (D ^ (0 + 1) * D ^ (p + 1)) (self_mul_pow_one_mul_pow_succ D p)
          (restrictedIdealMulSections D (D ^ (0 + 1)) (D ^ (p + 1)) inferInstance a b) := by
  have h₀ : 0 + 1 ≤ p + 1 + 1 := by omega
  have h₁ : p + 1 ≤ p + 1 + 1 := Nat.le_succ (p + 1)
  obtain ⟨u, hu⟩ := surjective_thickeningRestrictionLE D hsurj h₀ (gradedSectionsHom D 0 a)
  obtain ⟨v, hv⟩ := surjective_thickeningRestrictionLE D hsurj h₁ (gradedSectionsHom D p b)
  obtain ⟨c, hc⟩ := exists_gradedSectionsHom_eq_mul D hsurj (m := 0) (n := p) (q := p + 1)
    (by omega) h₀ h₁ a b
  refine ⟨c, ⟨a, b, hc⟩, Eq.trans (hc u v hu hv) ?_⟩
  exact (gradedSectionsHomOfEq_restrictedIdealMulSections D (m := 0) (n := p) (N := p + 1 + 1)
    (by omega) (self_mul_pow_one_mul_pow_succ D p) h₀ h₁ a b u v hu hv).symm

end AlgebraicGeometry.Scheme.IdealSheafData

end
