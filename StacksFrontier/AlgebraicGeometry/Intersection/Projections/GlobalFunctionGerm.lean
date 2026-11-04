module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.TripleTautologicalGerm

/-!
# The germ of a global function times a section, against the function's value

The germ calculus of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.TripleTautologicalGerm` computes the germ
of a tensor of tautological sections modulo `𝔪ₜ · ℒₜ`, and its coefficients are **constants**:
scalars of the ground field, entering through
`AlgebraicGeometry.ProjectiveSpaceOfModule.scalarGerm`. The sections that cut out the incidence
correspondence of Tag 0B1S are not combinations of that kind. Their coefficients are *global
functions* on the source — the coordinate functions of the affine parameters
`(c, u, u', w, h)` of `AlgebraicGeometry.ProjectiveSpaceOfModule.transitionEnd`, which vary from
point to point and are not pulled back from `Spec k`.

This file supplies the one step that closes that gap: **modulo `𝔪ₜ · ℒₜ` a global function acts on
a germ through its value at the point.** If the germ of `P` differs from the constant `r` by an
element of the maximal ideal — which is what "`P` takes the value `r` at `t`" says — then
`P • s` and `r • s` have the same germ modulo `𝔪ₜ · ℒₜ`. The proof is one line of module algebra
once the germ map is known to be semilinear, which is
`Stacks.SheafOfModules.stalkModule_germ_smul`.

With it, a section written as `∑ i, Pᵢ • sᵢ` has the germ `∑ i, rᵢ • germ sᵢ` modulo `𝔪ₜ · ℒₜ`,
and the vanishing criterion
`AlgebraicGeometry.ProjectiveSpaceOfModule.mem_nonvanishingLocus_pair_iff_of_germ_sub_smul_mem`
applies to it with the scalar `D` assembled from the values `rᵢ`.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.grpGerm_smul_sub_smul_mem`: a global function acts
  on a germ through its value at the point, modulo `𝔪ₜ · ℒₜ`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.grpGerm_sum_smul_sub_smul_mem`: the same for a
  finite sum, which is the form the coordinates of a parametrisation take.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.ringGerm_sub_scalarTop_mem_maximalIdeal`: **the
  value a global function takes at a `k`-point**, which is the hypothesis the two lemmas above
  consume. At a point presented as the image of a morphism `p : Spec k ⟶ T` splitting the
  structure morphism, the germ of `P` differs from the constant of the scalar `P` pulls back to
  by an element of the maximal ideal.

## Implementation notes

**Why there is no residue field here.** Reading a value off a global function looks like a
statement about the residue field `κ(x)`, and the library has `AlgebraicGeometry.Scheme.residue`
and `AlgebraicGeometry.Scheme.Hom.residueFieldMap`; going that way would need `κ(x) ≅ k`, which
over an algebraically closed field is true at a closed point and is not in the library. It is not
needed. Presenting the point as `p.base a` for a section `p : Spec k ⟶ T` of the structure
morphism makes the comparison a statement about the *stalk map of `p`*, which Mathlib already
has: `AlgebraicGeometry.Scheme.Hom.germ_stalkMap_apply` commutes the germ with it, and an element
whose image under a ring map into a nontrivial ring is zero is not a unit, so it lies in the
maximal ideal of a local ring. And the presentation costs nothing where it is used: a point of
affine space over a base *is* such a section, by `AlgebraicGeometry.AffineSpace.homOfVector`, and
the pullback of a coordinate function along it is its component, by
`AlgebraicGeometry.AffineSpace.homOfVector_appTop_coord` — which is exactly the hypothesis `hPr`
below. For an arbitrary scheme over `k` the same presentation is
`AlgebraicGeometry.sectionEquivIsRationalPoint`, the library's identification of the sections
over `Spec k` with the `k`-rational points.

## References

* [Stacks Project, Tag 0B1S](https://stacks.math.columbia.edu/tag/0B1S)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open Stacks.SheafOfModules Stacks.SheafOfModules.TensorStalkRingedSpace

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable {T : Scheme.{u}}

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

/-- **A global function acts on a germ through its value at the point.** The hypothesis is that
the germ of `P` differs from the germ of a reference function `ρ` by an element of the maximal
ideal, which is what it means for `P` and `ρ` to take the same value at `x`; the conclusion is
that `P • m` and `ρ • m` have the same germ modulo `𝔪ₓ · Fₓ`.

The reference function the germ calculus of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.TripleTautologicalGerm` wants is a
constant, `AlgebraicGeometry.ProjectiveSpaceOfModule.scalarTop k τ r`, whose germ is
`AlgebraicGeometry.ProjectiveSpaceOfModule.scalarGerm k τ x r` by
`AlgebraicGeometry.ProjectiveSpaceOfModule.ringGerm_scalarTop`; stating it for an arbitrary `ρ`
keeps the lemma free of the structure morphism. It is the one step that lets that calculus, whose
coefficients are constants, be applied to a section whose coefficients are global functions. -/
public theorem grpGerm_smul_sub_smul_mem (F : PresheafOfModules.{u} (O T.toRingedSpace))
    (x : T) (U : Opens ↥T) (hxU : x ∈ U) (P rho : T.toRingedSpace.presheaf.obj (op U))
    (hP : ringGerm T.toRingedSpace x U hxU P - ringGerm T.toRingedSpace x U hxU rho ∈
      IsLocalRing.maximalIdeal (ringStalk T.toRingedSpace x))
    (m : F.obj (op U)) :
    grpGerm T.toRingedSpace F x U hxU (P • m) -
        ringGerm T.toRingedSpace x U hxU rho • grpGerm T.toRingedSpace F x U hxU m ∈
      IsLocalRing.maximalIdeal (ringStalk T.toRingedSpace x) •
        (⊤ : Submodule (ringStalk T.toRingedSpace x) (grpStalk T.toRingedSpace F x)) := by
  rw [stalkModule_germ_smul T.toRingedSpace F x U hxU P m, ← sub_smul]
  exact Submodule.smul_mem_smul hP Submodule.mem_top

/-- **A finite sum of global functions times sections has the germ of the corresponding reference
combination**, modulo `𝔪ₓ · Fₓ`. This is the shape the coordinates of the bilinear parametrisation
of Tag 0B1S take: one term per pair of basis vectors, with the coefficient a polynomial in the
affine parameters. -/
public theorem grpGerm_sum_smul_sub_smul_mem (F : PresheafOfModules.{u} (O T.toRingedSpace))
    (x : T) (U : Opens ↥T) (hxU : x ∈ U) {ι : Type*} [Fintype ι]
    (P rho : ι → T.toRingedSpace.presheaf.obj (op U))
    (hP : ∀ i, ringGerm T.toRingedSpace x U hxU (P i) -
      ringGerm T.toRingedSpace x U hxU (rho i) ∈
      IsLocalRing.maximalIdeal (ringStalk T.toRingedSpace x))
    (m : ι → F.obj (op U)) :
    grpGerm T.toRingedSpace F x U hxU (∑ i, P i • m i) -
        ∑ i, ringGerm T.toRingedSpace x U hxU (rho i) •
          grpGerm T.toRingedSpace F x U hxU (m i) ∈
      IsLocalRing.maximalIdeal (ringStalk T.toRingedSpace x) •
        (⊤ : Submodule (ringStalk T.toRingedSpace x) (grpStalk T.toRingedSpace F x)) := by
  rw [map_sum, ← Finset.sum_sub_distrib]
  exact Submodule.sum_mem _ fun i _ =>
    grpGerm_smul_sub_smul_mem F x U hxU (P i) (rho i) (hP i) (m i)

/-! ### The value of a global function at a `k`-point -/

section Value

variable (k : Type u) [Field k]

/-- **A global function has, at a `k`-point of the scheme, the germ of the constant it pulls back
to.** This is the hypothesis `hP` of
`AlgebraicGeometry.ProjectiveSpaceOfModule.grpGerm_smul_sub_smul_mem` at a point presented as the
image of a morphism `p : Spec k ⟶ T` splitting the structure morphism — which is what a point of
the parametrisation's source is, by
`AlgebraicGeometry.AffineSpace.homOfVector`, and what a rational point of any `k`-scheme is, by
`AlgebraicGeometry.sectionEquivIsRationalPoint`. The reference constant is the one whose pullback
along `p` is the pullback of `P`, and `AlgebraicGeometry.AffineSpace.homOfVector_appTop_coord`
supplies exactly that equation for a coordinate function of affine space.

**No identification of the residue field with `k` is built.** The germ is compared with the
constant *through the stalk map of `p`*: the pullback of `P - scalarTop k τ r` along `p` is zero,
the germ map commutes with the stalk map
(`AlgebraicGeometry.Scheme.Hom.germ_stalkMap_apply`), and an element whose image under a ring map
into a nontrivial ring is zero cannot be a unit — so the germ lies in the maximal ideal. -/
public theorem ringGerm_sub_scalarTop_mem_maximalIdeal (τ : T ⟶ Spec (CommRingCat.of k))
    (p : Spec (CommRingCat.of k) ⟶ T) (hp : p ≫ τ = 𝟙 _) (a : Spec (CommRingCat.of k))
    (P : T.toRingedSpace.presheaf.obj (op ⊤)) (r : k)
    (hPr : p.appTop.hom P = (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom r) :
    ringGerm T.toRingedSpace (p.base a) ⊤ (Opens.mem_top _) P -
        ringGerm T.toRingedSpace (p.base a) ⊤ (Opens.mem_top _) (scalarTop k τ r) ∈
      IsLocalRing.maximalIdeal (ringStalk T.toRingedSpace (p.base a)) := by
  have hconst : p.appTop.hom (scalarTop k τ r) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom r := by
    rw [appTop_scalarTop k p τ r, hp]
    simp [scalarTop]
  have hP := Scheme.Hom.germ_stalkMap_apply p ⊤ a (Opens.mem_top _) P
  have hC := Scheme.Hom.germ_stalkMap_apply p ⊤ a (Opens.mem_top _) (scalarTop k τ r)
  have heq : (p.stalkMap a).hom
        (ringGerm T.toRingedSpace (p.base a) ⊤ (Opens.mem_top _) P) =
      (p.stalkMap a).hom
        (ringGerm T.toRingedSpace (p.base a) ⊤ (Opens.mem_top _) (scalarTop k τ r)) := by
    exact hP.trans ((congrArg _ (hPr.trans hconst.symm)).trans hC.symm)
  refine (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr fun hu => ?_)
  have hu' := hu.map (p.stalkMap a).hom
  rw [map_sub, heq, sub_self] at hu'
  exact not_isUnit_zero hu'

end Value

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
