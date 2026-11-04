module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistSectionModuleGraded
public import StacksFrontier.AlgebraicGeometry.TwistRigidity.Pointwise

/-!
# Multiplication by a homogeneous scalar is the canonical twist product with its section

Two spellings of "multiply a local section of `𝒪(n)` on `Proj 𝒮` by a homogeneous element `a` of
degree `i`" occur in this repository and were never compared:

* `Stacks.AlgebraicGeometry.ProjTwistedSections.twistScalarSheafMap`, the associated-sheaf
  morphism `𝒪(n) ⟶ 𝒪(i + n)` of the degree-preserving linear map `LinearMap.mul S S a` on the
  twisted gradings. This is what the graded module structure on the twisted global sections —
  `Stacks.AlgebraicGeometry.ProjTwistedSections.homogeneousScalarTwistedSections`, hence the
  finiteness statements of [Stacks, Tag 01YS] clause (5) — is built from.
* `Stacks.AlgebraicGeometry.RelativeProjTwists.absoluteTwistProduct` against
  `Stacks.AlgebraicGeometry.TwistRigidity.degreeSectionOn`, the canonical product
  `𝒪(i) ⊗ 𝒪(n) ⟶ 𝒪(i + n)` evaluated against the restriction of the global section attached to
  `a`. This is the product that
  `Stacks.AlgebraicGeometry.ThetaMultiplicative.twistPushforwardMap_absoluteTwistProduct` — the
  adjoint form of [Stacks, Tag 01MY]'s comparison `θ`, with its product formula in full strength
  — is stated with.

Both are pointwise multiplication in the homogeneous localizations, and this file proves they
agree. It is the comparison of spellings that the closing section of
`StacksFrontier/AlgebraicGeometry/Blowup/ProjectivePushforwardGradedSections.lean` records as the
missing input: with it, a product formula stated at `absoluteTwistProduct` can be read as a
statement about the module action the finiteness theorems use.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistedSections.localizedModule_map_mul_eq_mkOne_mul`: in one
  fibre, the localization of multiplication-by-`c` is multiplication by the fraction `c / 1`.
* `Stacks.AlgebraicGeometry.ProjTwistedSections.twistScalarSheafMap_app_eq_absoluteTwistProduct`:
  **multiplication by a homogeneous scalar, as a morphism of twisting sheaves, is the canonical
  twist product against the section attached to that scalar**, on the sections over an arbitrary
  open.
* `Stacks.AlgebraicGeometry.ProjTwistedSections.absoluteTwistProduct_degreeSectionOn_eq`: the
  same identity read in the other direction, with the degrees given by `hk`.

## Implementation notes

The fibres of the twisting sheaves are `LocalizedModule P S` for `P` the prime complement, and at
this pin that type *is* `Localization P` with the module action being ring multiplication — the
coincidence recorded in `Stacks.AlgebraicGeometry.ProjTrivialization` and used throughout
`StacksFrontier/AlgebraicGeometry/TwistRigidity/Pointwise.lean`. So the fibre identity is
`LocalizedModule.map_mk` followed by `Localization.mk_mul`, and the sheaf identity is that
identity at every point, the sections of an associated-module sheaf being functions with a
property.

## References

* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf twistGrading)
open Stacks.AlgebraicGeometry.RelativeProjTwists (absoluteTwistProduct)
open Stacks.AlgebraicGeometry.TwistRigidity (degreeSectionOn degreeSectionOn_apply
  absoluteTwistProduct_apply)

namespace Stacks.AlgebraicGeometry.ProjTwistedSections

universe u w

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-! ### One fibre -/

omit [SetLike σ S] [AddSubgroupClass σ S] [GradedRing 𝒮] in
/-- **In one fibre, the localization of multiplication by `c` is multiplication by `c / 1`.**
`LocalizedModule P S` is `Localization P` at this pin, so both sides send `m / t` to `c * m / t`
and the identity is `Localization.mk_mul` after `one_mul` on the denominator. -/
public theorem localizedModule_map_mul_eq_mkOne_mul (P : Submonoid S) (c : S)
    (v : LocalizedModule P S) :
    LocalizedModule.map P (LinearMap.mul S S c) v = LocalizedModule.mk c (1 : P) * v := by
  induction v using LocalizedModule.induction_on with
  | _ m t =>
    rw [LocalizedModule.map_mk]
    show _ = Localization.mk c (1 : P) * Localization.mk m t
    rw [Localization.mk_mul]
    exact congrArg (Localization.mk ((LinearMap.mul S S c) m)) (one_mul t).symm

/-! ### The two spellings of the scalar action -/

/-- **Multiplication by a homogeneous scalar, as a morphism of twisting sheaves, is the canonical
product of the twists against the section attached to that scalar.**

The left side is `Stacks.AlgebraicGeometry.ProjTwistedSections.twistScalarSheafMap`, the
associated-sheaf morphism of `LinearMap.mul S S a`; the right side is
`Stacks.AlgebraicGeometry.RelativeProjTwists.absoluteTwistProduct` against
`Stacks.AlgebraicGeometry.TwistRigidity.degreeSectionOn`. Both have the value
`a / 1 * s x` at every point `x`. -/
public theorem twistScalarSheafMap_app_eq_absoluteTwistProduct (i : ℕ) (n : ℤ) (a : 𝒮 i)
    (V : Opens (ProjectiveSpectrum.top 𝒮)) (s : (twistingSheaf 𝒮 n).val.obj (op V)) :
    ((twistScalarSheafMap 𝒮 i n ((i : ℤ) + n) rfl a).val.app (op V)).hom s =
      absoluteTwistProduct 𝒮 (i : ℤ) n V (degreeSectionOn 𝒮 i a.2 V) s := by
  refine Subtype.ext (funext fun x => ?_)
  show LocalizedModule.map x.1.asHomogeneousIdeal.toIdeal.primeCompl
      (LinearMap.mul S S (a : S)) (s.1 x) = _
  refine Eq.trans (localizedModule_map_mul_eq_mkOne_mul _ (a : S) (s.1 x)) ?_
  refine Eq.trans ?_ (absoluteTwistProduct_apply 𝒮 (i : ℤ) n V
    (degreeSectionOn 𝒮 i a.2 V) s x).symm
  exact congrArg (· * s.1 x) (degreeSectionOn_apply 𝒮 i a.2 V x).symm

/-- The identity above with the target degree given by a hypothesis `hk : i + n = k`, which is
the shape `twistScalarSheafMap` is used at. -/
public theorem twistScalarSheafMap_app_eq_absoluteTwistProduct' (i : ℕ) (n k : ℤ)
    (hk : (i : ℤ) + n = k) (a : 𝒮 i) (V : Opens (ProjectiveSpectrum.top 𝒮))
    (s : (twistingSheaf 𝒮 n).val.obj (op V)) :
    ((twistScalarSheafMap 𝒮 i n k hk a).val.app (op V)).hom s =
      hk ▸ absoluteTwistProduct 𝒮 (i : ℤ) n V (degreeSectionOn 𝒮 i a.2 V) s := by
  subst hk
  exact twistScalarSheafMap_app_eq_absoluteTwistProduct 𝒮 i n a V s

/-- The canonical product against a homogeneous section, read as the scalar action: the
right-to-left form of `twistScalarSheafMap_app_eq_absoluteTwistProduct`. -/
public theorem absoluteTwistProduct_degreeSectionOn_eq (i : ℕ) (n : ℤ) (a : 𝒮 i)
    (V : Opens (ProjectiveSpectrum.top 𝒮)) (s : (twistingSheaf 𝒮 n).val.obj (op V)) :
    absoluteTwistProduct 𝒮 (i : ℤ) n V (degreeSectionOn 𝒮 i a.2 V) s =
      ((twistScalarSheafMap 𝒮 i n ((i : ℤ) + n) rfl a).val.app (op V)).hom s :=
  (twistScalarSheafMap_app_eq_absoluteTwistProduct 𝒮 i n a V s).symm

end Stacks.AlgebraicGeometry.ProjTwistedSections

end
