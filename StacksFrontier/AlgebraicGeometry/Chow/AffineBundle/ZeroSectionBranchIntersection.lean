module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.ZeroSectionBranchCarrier
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.WholeTag

/-!
# The intersection of the two branches is the zero section of either one

In the situation of [Stacks, Tag 0F97] the proof of [Stacks, Tag 0F98] in the case `W ⊆ D` ends
with the sentence

  "Since `W₁ ∩ W₂` is the zero section of the line bundle `W₁ → W` we see from Lemma 42.32.4 that
  `[W₁ ∩ W₂]_k = p₁^*(c₁(L₂) ∩ [W])`."

This file proves the clause before the comma, for an arbitrary decomposition: the scheme-theoretic
intersection of the two branches, carried into the total space of the line bundle presenting the
first branch, **is** the image of that bundle's zero section — as an ideal sheaf, hence as a
closed subscheme.

Nothing about the case `W ⊆ D` is used. The identity holds for every decomposition, and the case
`W ⊆ D` enters only through *which* decomposition it is applied to: the base change
`Stacks.Chow.TensorZeroScheme.decompositionComap` of the diagram along `W ↪ Y`, whose two closed
subschemes are `W₁` and `W₂` by
`Stacks.Chow.TensorZeroScheme.comap_branch₁_decompositionComap` and `…₂…`, and over which the
divisor is all of `W` by
`Stacks.Chow.TensorZeroScheme.zeroIdeal_pullbackTensorSection_subschemeι_eq_bot`.

## Main results

* `Stacks.Chow.TensorZeroScheme.Decomposition.ker_inclusion_comp_branch₁_eq_ker_zeroSection` —
  **the intersection of the two branches is the zero section of the first**, as an identity of
  ideal sheaves on the total space of the line bundle of [Stacks, Tag 0F97](4).
* `Stacks.Chow.TensorZeroScheme.Decomposition.intersectionIsoKerZeroSection` — the same read as an
  isomorphism of closed subschemes, which is what moves a cycle from `W₁ ∩ W₂` onto the image of
  the zero section.

## Implementation notes

### Why there is no transport here

Conditions (6) and (7) of [Stacks, Tag 0F97] are recorded as *fields* of
`Stacks.Chow.TensorZeroScheme.Decomposition`: condition (6) says that
`D₁ ∩ D₂ ⟶ D₁ ⟶ D` is an isomorphism and condition (7) that `D₁ ∩ D₂ ⟶ D₁ ≅ L(D)` factors
through the zero section along it. So the proof below is the rewrite of one field by the other
followed by `AlgebraicGeometry.Scheme.Hom.ker_comp_of_isIso`, and no equality of concrete schemes
or ideals is ever transported along: the isomorphism of condition (6) is a morphism given with the
data, not a `cast` manufactured from an equation. This is the same discipline as
`Stacks.Chow.TensorZeroScheme.inf_sup_comap_proj_of_le`, which goes through the Galois connection
`AlgebraicGeometry.Scheme.IdealSheafData.le_map_iff_comap_le` and transports nothing.

In particular the base of the branch bundle is left spelled as the zero scheme of the restricted
section throughout, never rewritten to `W` along
`…zeroIdeal_pullbackTensorSection_subschemeι_eq_bot`. That equation is between concrete ideal
sheaves, and an `Eq.rec` at it would put a line-bundle situation under a `cast`; a consumer that
wants to see `W` should use the isomorphism of condition (6), as the statements here do.

### Why only the first branch

The identity for the second branch is the same two lines against
`Stacks.Chow.TensorZeroScheme.Decomposition.intersection_zeroSection₂` and the `le_sup_right`
half of condition (6), which the structure does not record; the source uses only `W₁`, and so
does the dévissage.

### No `@[stacks]` attribute here

Conditions (6) and (7) of Tag 0F97 are asserted by
`Stacks.Chow.TensorZeroScheme.isIso_intersectionProj` and
`Stacks.Chow.TensorZeroScheme.intersectionι₁_eq`; this is those conditions combined, read on
kernel ideals. Nor does anything here assert [Stacks, Tag 0F98], which is a single identity of
maps; see the convention note in
`StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.ChowMaps`.

## References

* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
* [Stacks Project, Tag 0F98](https://stacks.math.columbia.edu/tag/0F98)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow.TensorZeroScheme

variable (Y : Scheme.{u}) (L₁ L₂ : Y.Modules)
  [h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]
  (s : Γ(Stacks.Divisors.tensorModules L₁ L₂, ⊤)) (R : Decomposition Y L₁ L₂ s)

include h₁ h₂ in
/-- **The intersection of the two branches is the zero section of the first.** Carried into the
total space of the line bundle `branchSituation Y L₁ L₂ s L₂` that presents `D₁` by
[Stacks, Tag 0F97](4), the scheme-theoretic intersection `D₁ ∩ D₂` cuts out exactly the image of
the zero section.

This is the clause "`W₁ ∩ W₂` is the zero section of the line bundle `W₁ → W`" of the case
`W ⊆ D` of [Stacks, Tag 0F98], at an arbitrary decomposition. Condition (7) of
[Stacks, Tag 0F97] factors the immersion through the zero section along `D₁ ∩ D₂ ⟶ D`, and
condition (6) says that morphism is an isomorphism, so the two immersions have the same kernel
ideal. -/
theorem Decomposition.ker_inclusion_comp_branch₁_eq_ker_zeroSection :
    (Scheme.IdealSheafData.inclusion (le_sup_left : R.D₁ ≤ R.D₁ ⊔ R.D₂) ≫ R.branch₁.hom).ker =
      (branchSituation Y L₁ L₂ s L₂).zeroSection.ker := by
  have := R.intersection_isIso
  rw [R.intersection_zeroSection₁]
  exact Scheme.Hom.ker_comp_of_isIso _ _

include h₁ h₂ in
/-- **The intersection of the two branches is the zero section of the first, as an isomorphism of
closed subschemes.** The two closed immersions into the total space of
`branchSituation Y L₁ L₂ s L₂` have the same kernel ideal by
`Stacks.Chow.TensorZeroScheme.Decomposition.ker_inclusion_comp_branch₁_eq_ker_zeroSection`, so the
comparison morphism between their sources is an isomorphism.

This is the form that moves a cycle: `[W₁ ∩ W₂]` becomes the fundamental cycle of the image of the
zero section, which is where clause (5) of [Stacks, Tag 0F96] computes it. -/
def Decomposition.intersectionIsoKerZeroSection :
    (R.D₁ ⊔ R.D₂).subscheme ≅ (branchSituation Y L₁ L₂ s L₂).zeroSection.ker.subscheme :=
  haveI := IsClosedImmersion.isIso_lift
    (branchSituation Y L₁ L₂ s L₂).zeroSection.ker.subschemeι
    (Scheme.IdealSheafData.inclusion (le_sup_left : R.D₁ ≤ R.D₁ ⊔ R.D₂) ≫ R.branch₁.hom)
    ((Scheme.IdealSheafData.ker_subschemeι _).trans
      (R.ker_inclusion_comp_branch₁_eq_ker_zeroSection Y L₁ L₂ s).symm)
  asIso (IsClosedImmersion.lift
    (branchSituation Y L₁ L₂ s L₂).zeroSection.ker.subschemeι
    (Scheme.IdealSheafData.inclusion (le_sup_left : R.D₁ ≤ R.D₁ ⊔ R.D₂) ≫ R.branch₁.hom)
    ((Scheme.IdealSheafData.ker_subschemeι _).trans
      (R.ker_inclusion_comp_branch₁_eq_ker_zeroSection Y L₁ L₂ s).symm).le)

include h₁ h₂ in
/-- The isomorphism of
`Stacks.Chow.TensorZeroScheme.Decomposition.intersectionIsoKerZeroSection` lies over the total
space of the branch bundle. -/
@[reassoc]
theorem Decomposition.intersectionIsoKerZeroSection_hom_comp_subschemeι :
    (R.intersectionIsoKerZeroSection Y L₁ L₂ s).hom ≫
        (branchSituation Y L₁ L₂ s L₂).zeroSection.ker.subschemeι =
      Scheme.IdealSheafData.inclusion (le_sup_left : R.D₁ ≤ R.D₁ ⊔ R.D₂) ≫ R.branch₁.hom :=
  IsClosedImmersion.lift_fac _ _ _

end Stacks.Chow.TensorZeroScheme

end
