module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.AffineOpenSectionsCohomology

/-!
# Conclusion (c) of [Stacks, Tag 0EX3] from bijectivity on sections, at a cartesian square

`Stacks.AlgebraicGeometry.TopDegreeBaseChange`
`.isIso_topDirectImageBaseChangeMap_of_bijective_app_plus_affineOpens`
reduces conclusion (c) of [Stacks, Tag 0EX3] to bijectivity of `γ⁺` on the sections over the
affine opens of `Y''` lying over an affine open of `Y'`, and carries quasi-compactness and
quasi-separatedness of the twice-base-changed morphism `f''` as explicit arguments. Conclusion
(c) is stated for a *cartesian* second square, where both are automatic: they are properties of
`S.f` stable under base change. This file supplies that form, so that a consumer proving the
bijectivity has nothing left to discharge but the bijectivity.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange`
  `.isIso_topDirectImageBaseChangeMap_of_bijective_app_plus_affineOpens_of_isPullback`: **the
  entry point for conclusion (c)** — invertibility of the canonical map `γ` of
  [Stacks, Tag 0EX3] from bijectivity of `γ⁺` on the sections over a compatible pair of affine
  opens, for a cartesian second square.

## Implementation notes

The two finiteness properties come from
`CategoryTheory.MorphismProperty.IsStableUnderBaseChange.of_isPullback` at `@QuasiCompact` and
at `@QuasiSeparated`, applied to the situation's own `quasiCompact_f'` and `quasiSeparated_f'`;
this is the same discharge
`isIso_topDirectImageBaseChangeMap_of_bijective_app_of_isPullback` performs for the unbounded
spelling of `γ`.

*No `@[stacks 0EX3]` attribute is placed here.* What is proved is a reduction of conclusion (c)
to a hypothesis, not (c) itself, so by the covering-set rule it is not a member of the covering
set of the tag.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open DerivedCategory

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {X'' Y'' : Scheme.{u}}

/-- **Conclusion (c) of [Stacks, Tag 0EX3] from bijectivity of `γ⁺` on the sections over the
affine opens of `Y''` lying over an affine open of `Y'`, at a cartesian second square.** The
finiteness of the twice-base-changed morphism is read off the square, both properties being
stable under base change, so the only hypothesis left is the bijectivity. -/
theorem isIso_topDirectImageBaseChangeMap_of_bijective_app_plus_affineOpens_of_isPullback
    (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
    (F' : S.X'.Modules) [F'.IsQuasicoherent]
    (h' : X'' ⟶ S.X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ S.Y')
    (sq : IsPullback h' f'' S.f' h)
    (hbij : ∀ V : S.Y'.Opens, IsAffineOpen V → ∀ W : Y''.Opens, IsAffineOpen W →
      W.1 ⊆ (h ⁻¹ᵁ V).1 →
      Function.Bijective
        ((topDirectImageBaseChangeMapPlus S F' h' f'' h
          (toShHom_comm_of_isPullback h' f'' h sq)).val.app (op W))) :
    IsIso (topDirectImageBaseChangeMap S F' h' f'' h
      (toShHom_comm_of_isPullback h' f'' h sq)) :=
  isIso_topDirectImageBaseChangeMap_of_bijective_app_plus_affineOpens S F' h' f'' h _
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiCompact) sq
      S.quasiCompact_f')
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiSeparated) sq
      S.quasiSeparated_f')
    hbij

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
