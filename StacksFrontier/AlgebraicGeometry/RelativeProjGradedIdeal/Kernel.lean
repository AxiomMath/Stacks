module

public import StacksFrontier.AlgebraicGeometry.Duality.IdealPowerDegreeFiltration
public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.SectionwiseQuotient

/-!
# The graded ideal cut out by a homomorphism of sheaf-level graded algebras

Tag 0801 names the graded ideal `ℐ ⊆ 𝒜` of the homogeneous local sections of `𝒜` that die under
a homomorphism of graded `𝒪_S`-algebras, and the quotient `𝒜/ℐ`. **This file constructs that
ideal** for an arbitrary `ψ : 𝒜 ⟶ ℬ` of sheaf-level graded algebras, as the degreewise sectionwise
kernel, and discharges every hypothesis the quotient of
`StacksFrontier/AlgebraicGeometry/RelativeProjGradedIdeal/Quotient.lean` needs of it.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.kernelGradedIdeal`: **the graded ideal
  `ker ψ`**, with degree-`n` piece the sectionwise kernel of `ψ_n`.
* `…quotByKernel` and `…quotMkKernel`: the quotient `𝒜/ker ψ` and its quotient homomorphism,
  with no hypothesis left.
* `…kernelAmbientHom`: `Proj_S(𝒜/ker ψ) ⟶ Proj_S(𝒜)`.

## Main results

* `…mem_kernelGradedIdeal_iff`: a local section lies in `ker ψ` exactly when `ψ` kills it.
* `…isQuasicoherent_kernelGradedIdeal_piece`: **the pieces of `ker ψ` are quasi-coherent**, with
  no hypothesis — the kernel of a morphism of quasi-coherent modules is quasi-coherent.
* `…isQuasicoherentQuotPieces_kernelGradedIdeal`: so are the pieces of `𝒜/ker ψ`.
* `…surjectiveOnAffineSections_quotMkKernel` and `…isClosedImmersion_kernelAmbientHom`:
  `Proj_S(𝒜/ker ψ)` is a closed subscheme of `Proj_S(𝒜)`.
* `…quotMkKernel_app_eq_zero_iff`: **the kernel clause.** A homogeneous local section dies in
  `𝒜/ker ψ` exactly when it dies under `ψ`, over every open of the base.
* `…mem_kernelGradedIdeal_of_app_eq_zero`: the vanishing local sections lie in `ker ψ`, which is
  the form Tag 0803 consumes.

## Implementation notes

**Why the ideal is the sectionwise kernel and not the categorical one.** A `GradedIdeal` carries a
`SheafOfModules.Submodule` of each piece, so the ideal has to be a submodule of `𝒜_n` rather than
an object mapping into it; `Stacks.Algebraization.kernelSubmodule` is that submodule. Its
quasi-coherence is not reproved here: `Stacks.Duality.isQuasicoherent_kernelSubmodule` already
says it for an arbitrary morphism of quasi-coherent modules on an arbitrary scheme, by
`Stacks.Algebraization.kernelSubmoduleIso` and
`Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel` (Tag 01LB), and is imported rather
than restated — the same three lines appear inline twice inside
`StacksFrontier/AlgebraicGeometry/RelativeProjGradedIdeal/ClosedSubscheme.lean` for a single degree,
and the statement wanted here is about every degree at once.

**The ideal property.** That the kernel absorbs multiplication is the product law of `ψ` and
nothing else: `ψ_{i+j}(x · b) = ψ_i(x) · ψ_j(b)` is zero as soon as `ψ_i(x)` is, the
multiplication of `ℬ` being additive in its first variable. No commutativity of `𝒜` and no
degree transport is used, so unlike `GradedIdeal.mul_mem`'s companion
`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.piece_mul_mem_right` this needs no `HEq`.

**What this leaves of Tag 0801.** Four of the five fields of `GradedQuotientPresentation` are
constructible from here with no hypothesis: `target`, `hom`, `surjective` and the closed immersion
that `iso_comp` compares against. The missing one is `iso`; the `Not done here` section of
`StacksFrontier/AlgebraicGeometry/RelativeProjGradedIdeal/Quotient.lean` records the route and the
chart-level statement that blocks it.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 0801](https://stacks.math.columbia.edu/tag/0801)
* [Stacks Project, Tag 01LB](https://stacks.math.columbia.edu/tag/01LB)

## Not done here

No Stacks tag is claimed. Tag 0801 identifies the closed subscheme cut out by `ℐ` with
`Proj_S(𝒜/ℐ)`, which is the `iso` clause and is not proved; what is proved here is that the ideal
of the tag exists, is quasi-coherent, and has the quotient the tag names.

`ψ` is an arbitrary homomorphism of sheaf-level graded algebras, and nothing below depends on
which `ψ` it is. Tag 0801 takes it to be `𝒜 ⟶ ⨁_d p_*((i_*𝒪_Z)(d))` for a closed immersion
`i : Z ⟶ Proj_S(𝒜)`. **That particular `ψ` is now assembled**, as
`Stacks.AlgebraicGeometry.RelativeProjTwists.psiClosedHom` in
`StacksFrontier/AlgebraicGeometry/RelativeProjGradedIdeal/ClosedTwistAlgebra.lean`: the
homogeneous-section map `Stacks.AlgebraicGeometry.RelativeProjTwists.psiHom` of
`StacksFrontier/AlgebraicGeometry/RelativeProjGradedIdeal/TwistHom.lean` composed with the truncated
direct image of the quotient homomorphism of the graded algebra `d ↦ (i_*𝒪_Z)(d)`, which that
file builds as the degreewise quotient of the twists by the graded ideal generated in degree `0`
by the ideal sheaf of `Z`. Everything in this file is applied to it there, giving Tag 0801's
graded ideal, its quotient and the closed immersion `Proj_S(𝒜/ℐ) ⟶ Proj_S(𝒜)`. What remains of
Tag 0801 in the relative case is quasi-coherence of `ℐ_Z · 𝒪(d)` and the `iso` clause; the `Not
done here` section of that file records both.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjMapDomain

namespace Stacks.AlgebraicGeometry.RelativeProjGradedIdeal

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

universe u

variable {S : Scheme.{u}} {𝒜 ℬ : SheafGradedAlgebra S} (ψ : SheafGradedAlgebraHom 𝒜 ℬ)

/-! ### The kernel of a homomorphism of graded algebras, as a graded ideal -/

/-- A product of homogeneous local sections one of whose factors `ψ` kills is killed by `ψ`: the
product law of `ψ` and additivity of the multiplication of `ℬ` in its first variable. -/
theorem app_mul_eq_zero_of_left (i j : ℤ) (U : S.Opens) {x : Γ(𝒜.piece i, U)}
    (hx : (ψ.app i).app U x = 0) (b : Γ(𝒜.piece j, U)) :
    (ψ.app (i + j)).app U ((𝒜.mul i j).app U x b) = 0 := by
  rw [ψ.app_mul i j U x b, hx, map_zero, AddMonoidHom.zero_apply]

/-- The sectionwise kernels of `ψ` absorb multiplication by an arbitrary homogeneous local
section, which is the ideal property of the degreewise kernel. -/
theorem mul_mem_kernelSubmodule (i j : ℤ) (U : S.Opens) {x : Γ(𝒜.piece i, U)}
    (hx : x ∈ (Stacks.Algebraization.kernelSubmodule (ψ.app i)).toSubmodule.obj (op U))
    (b : Γ(𝒜.piece j, U)) :
    (𝒜.mul i j).app U x b ∈
      (Stacks.Algebraization.kernelSubmodule (ψ.app (i + j))).toSubmodule.obj (op U) :=
  (AlgebraicGeometry.mem_kernelSubmodule_iff (ψ.app (i + j)) U _).2
    (app_mul_eq_zero_of_left ψ i j U
      ((AlgebraicGeometry.mem_kernelSubmodule_iff (ψ.app i) U x).1 hx) b)

/-- **The graded ideal `ker ψ` cut out by a homomorphism of sheaf-level graded algebras**: in
degree `n` the sectionwise kernel of `ψ_n`, an `𝒪_S`-submodule of `𝒜_n`.

It is an ideal because `ψ` preserves products: `ψ_{i+j}(x · b) = ψ_i(x) · ψ_j(b)`. -/
def kernelGradedIdeal : GradedIdeal 𝒜 where
  piece n := Stacks.Algebraization.kernelSubmodule (ψ.app n)
  mul_mem i j U := mul_mem_kernelSubmodule ψ i j U

/-- **A homogeneous local section lies in `ker ψ` exactly when `ψ` kills it.** -/
theorem mem_kernelGradedIdeal_iff (n : ℤ) (U : S.Opens) (a : Γ(𝒜.piece n, U)) :
    a ∈ ((kernelGradedIdeal ψ).piece n).toSubmodule.obj (op U) ↔ (ψ.app n).app U a = 0 :=
  AlgebraicGeometry.mem_kernelSubmodule_iff (ψ.app n) U a

/-- **The vanishing homogeneous local sections lie in `ker ψ`.** This is the direction Tag 0801's
kernel clause is consumed in: the sections that die under `ψ` over an open of the base are
sections of the ideal there. -/
theorem mem_kernelGradedIdeal_of_app_eq_zero (n : ℤ) (U : S.Opens) (a : Γ(𝒜.piece n, U))
    (ha : (ψ.app n).app U a = 0) :
    a ∈ ((kernelGradedIdeal ψ).piece n).toSubmodule.obj (op U) :=
  (mem_kernelGradedIdeal_iff ψ n U a).2 ha

/-- **Every piece of `ker ψ` is quasi-coherent**, with no hypothesis: the sectionwise kernel is
the categorical kernel of a morphism of quasi-coherent modules, every piece of a
`SheafGradedAlgebra` being quasi-coherent. -/
theorem isQuasicoherent_kernelGradedIdeal_piece (n : ℤ) :
    (((kernelGradedIdeal ψ).piece n).toSheafOfModules : S.Modules).IsQuasicoherent :=
  Stacks.Duality.isQuasicoherent_kernelSubmodule (ψ.app n) (𝒜.isQuasicoherent n)
    (ℬ.isQuasicoherent n)

/-- **Every piece of `𝒜/ker ψ` is quasi-coherent**, so the quotient is the input of the relative
Proj construction with no hypothesis left. -/
theorem isQuasicoherentQuotPieces_kernelGradedIdeal :
    IsQuasicoherentQuotPieces 𝒜 (kernelGradedIdeal ψ) :=
  isQuasicoherentQuotPieces 𝒜 (kernelGradedIdeal ψ) (isQuasicoherent_kernelGradedIdeal_piece ψ)

/-! ### The quotient by the kernel -/

/-- **The quotient `𝒜/ker ψ`**, as sheaf-level graded algebra data. -/
def quotByKernel : SheafGradedAlgebra S :=
  quotSheafGradedAlgebra 𝒜 (kernelGradedIdeal ψ) (isQuasicoherentQuotPieces_kernelGradedIdeal ψ)

/-- **The quotient homomorphism `𝒜 ⟶ 𝒜/ker ψ`.** -/
def quotMkKernel : SheafGradedAlgebraHom 𝒜 (quotByKernel ψ) :=
  quotMk 𝒜 (kernelGradedIdeal ψ) (isQuasicoherentQuotPieces_kernelGradedIdeal ψ)

/-- **The quotient homomorphism is degreewise surjective on the sections over the affine opens of
the base.** This is the `surjective` field of `GradedQuotientPresentation`. -/
theorem surjectiveOnAffineSections_quotMkKernel :
    ProjBundleSurjection.SurjectiveOnAffineSections (quotMkKernel ψ) :=
  surjectiveOnAffineSections_quotMk 𝒜 (kernelGradedIdeal ψ)
    (isQuasicoherentQuotPieces_kernelGradedIdeal ψ) (isQuasicoherent_kernelGradedIdeal_piece ψ)

/-- **`Proj_S(𝒜/ker ψ) ⟶ Proj_S(𝒜)`**, the morphism `GradedQuotientPresentation.iso_comp`
compares the closed subscheme against. -/
def kernelAmbientHom :
    (relativeProj (quotByKernel ψ)).scheme ⟶ (relativeProj 𝒜).scheme :=
  quotAmbientHom 𝒜 (kernelGradedIdeal ψ) (isQuasicoherentQuotPieces_kernelGradedIdeal ψ)
    (isQuasicoherent_kernelGradedIdeal_piece ψ)

/-- **`Proj_S(𝒜/ker ψ)` is a closed subscheme of `Proj_S(𝒜)`.** -/
theorem isClosedImmersion_kernelAmbientHom : IsClosedImmersion (kernelAmbientHom ψ) :=
  isClosedImmersion_quotAmbientHom 𝒜 (kernelGradedIdeal ψ)
    (isQuasicoherentQuotPieces_kernelGradedIdeal ψ) (isQuasicoherent_kernelGradedIdeal_piece ψ)

/-- The closed immersion is a morphism over the base. -/
@[reassoc]
theorem kernelAmbientHom_comp_toBase :
    kernelAmbientHom ψ ≫ (relativeProj 𝒜).toBase =
      (relativeProj (quotByKernel ψ)).toBase :=
  quotAmbientHom_comp_toBase 𝒜 (kernelGradedIdeal ψ)
    (isQuasicoherentQuotPieces_kernelGradedIdeal ψ) (isQuasicoherent_kernelGradedIdeal_piece ψ)

/-! ### The kernel clause -/

/-- **The kernel clause.** A homogeneous local section of `𝒜` dies in `𝒜/ker ψ` exactly when it
dies under `ψ`, over **every** open of the base and not only the affine ones. So the quotient by
`ker ψ` has precisely the vanishing of `ψ`. -/
theorem quotMkKernel_app_eq_zero_iff (n : ℤ) (U : S.Opens) (a : Γ(𝒜.piece n, U)) :
    ((quotMkKernel ψ).app n).app U a = 0 ↔ (ψ.app n).app U a = 0 :=
  (quotMkApp_app_eq_zero_iff 𝒜 (kernelGradedIdeal ψ) n U a).trans
    (mem_kernelGradedIdeal_iff ψ n U a)

/-- **The sections of `ker ψ` are exactly the sections dying in the quotient**, over every open of
the base: the quotient homomorphism and `ψ` cut out the same ideal. -/
theorem mem_kernelGradedIdeal_iff_quotMkKernel_app_eq_zero (n : ℤ) (U : S.Opens)
    (a : Γ(𝒜.piece n, U)) :
    a ∈ ((kernelGradedIdeal ψ).piece n).toSubmodule.obj (op U) ↔
      ((quotMkKernel ψ).app n).app U a = 0 :=
  (mem_kernelGradedIdeal_iff ψ n U a).trans (quotMkKernel_app_eq_zero_iff ψ n U a).symm

/-- **`ℐ_n ⟶ 𝒜_n ⟶ (𝒜/ker ψ)_n` is short exact**, in every degree. -/
theorem shortExact_quotShortComplex_kernelGradedIdeal (n : ℤ) :
    (quotShortComplex 𝒜 (kernelGradedIdeal ψ) n).ShortExact :=
  shortExact_quotShortComplex 𝒜 (kernelGradedIdeal ψ) n

end Stacks.AlgebraicGeometry.RelativeProjGradedIdeal

end
