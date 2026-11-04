module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Reduction
public import StacksFrontier.AlgebraicGeometry.FlatBaseChange.Affine
public import StacksFrontier.AlgebraicGeometry.FlatBaseChange.MateComparison
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineIsoCriterion
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DirectImageStructureSheafFlat

/-!
# The base-change comparison of `f_* 𝒪_X`: mate reading and reduction to global sections

Two auxiliary facts about the comparison `g^* (f_* 𝒪_X) ⟶ f'_* 𝒪_{X'}` used by the proof of
clause (b) of [Stacks, Tag 0E7K] in `DirectImageStructureSheafCommutesBaseChange.lean`.

## Main results

All in the namespace `Stacks.AlgebraicGeometry.TopDegreeBaseChange`.

* `isIso_directImageStructureSheafBaseChangeMap_iff`: the comparison
  `directImageStructureSheafBaseChangeMap` of `StructureSheafSurjectivityBaseChange.lean` is
  invertible exactly when the mate `AffinePushforward.baseChangeNatTrans` of the pullback square
  is invertible at `𝒪_X`, which is the spelling the locality and affineness criteria of
  `AffineBaseChangeIso/` are stated for.
* `isIso_app_of_iso`: a component of a natural transformation is invertible at an object as soon
  as it is invertible at an isomorphic one.
* `isIso_baseChangeNatTrans_structureSheaf_of_isIso_appTop`: over an affine lower right corner the
  comparison at `𝒪_X` is invertible as soon as it is invertible on global sections.

## A remark on the hypotheses of Tag 0E7K

The flatness of `X ⟶ S` in [Stacks, Tag 0E7K] cannot be dropped from clause (b), even over an
affine `Y`: for `k` a field, `A = k[t]` and `X = Proj(A[x, y]/(t x²)) ⊆ P¹_A` over `Y = Spec A`,
the morphism `X ⟶ Y` is proper with fibres of dimension at most one and `R¹ f_* 𝒪_X = 0`, but
`Γ(X, 𝒪_X) ≅ A ⊕ A` while the fibre over `t = 0` is `P¹_k` with `Γ = k`, so the comparison along
`Spec A/t ⟶ Spec A` is `k² ⟶ k`, surjective and not injective.

## References

* [Stacks Project, Tag 0E7K](https://stacks.math.columbia.edu/tag/0E7K)
* [Stacks Project, Tag 02N7](https://stacks.math.columbia.edu/tag/02N7)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.TwoSquare

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance] HasDerivedCategory.standard

noncomputable section

/-- **Clause (b) of [Stacks, Tag 0E7K] is a statement about the mate comparison.** The
comparison `g^* (f_* 𝒪_X) ⟶ f'_* 𝒪_{X'}` of `StructureSheafSurjectivityBaseChange.lean` is
invertible exactly when the mate
`Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans` of the pullback square is
invertible at `𝒪_X`.

The comparison is the adjoint transpose `pushforwardBaseChange` of that square followed by the
direct image of the isomorphism `(g')^* 𝒪_X ≅ 𝒪_{X'}`, and the transpose is the mate by
`Stacks.AlgebraicGeometry.FlatBaseChange.baseChangeNatTrans_app_eq_pushforwardBaseChange`; so
the two differ by an isomorphism. -/
theorem isIso_directImageStructureSheafBaseChangeMap_iff {X Y Y' : Scheme.{u}} (f : X ⟶ Y)
    (g : Y' ⟶ Y) :
    IsIso (directImageStructureSheafBaseChangeMap f g) ↔
      IsIso ((AffinePushforward.baseChangeNatTrans
        (pullback.condition (f := f) (g := g))).app (Scheme.unitModule X)) := by
  have h : directImageStructureSheafBaseChangeMap f g =
      (AffinePushforward.baseChangeNatTrans
          (pullback.condition (f := f) (g := g))).app (Scheme.unitModule X) ≫
        (Scheme.Modules.pushforward (pullback.snd f g)).map
          (Scheme.Modules.pullbackUnitIso (pullback.fst f g)).hom := by
    rw [directImageStructureSheafBaseChangeMap,
      FlatBaseChange.baseChangeNatTrans_app_eq_pushforwardBaseChange]
  have hr : IsIso ((Scheme.Modules.pushforward (pullback.snd f g)).map
      (Scheme.Modules.pullbackUnitIso (pullback.fst f g)).hom) := Functor.map_isIso _ _
  rw [h]
  exact @isIso_comp_right_iff _ _ _ _ _ _ _ hr

/-- A component of a natural transformation is invertible at an object as soon as it is
invertible at an isomorphic one: naturality writes the first component as the second conjugated
by the images of the isomorphism.

The three `IsIso` facts are supplied by explicit application of `CategoryTheory.IsIso.comp_isIso`
rather than by instance search, as elsewhere in this cluster: the category structure on
`AlgebraicGeometry.Scheme.Modules` is a different instance from the one on `SheafOfModules`. -/
theorem isIso_app_of_iso {C : Type*} [Category C] {D : Type*} [Category D]
    {G H : C ⥤ D} (τ : G ⟶ H) {A B : C} (e : A ≅ B) (h : IsIso (τ.app B)) :
    IsIso (τ.app A) := by
  have hG : IsIso (G.map e.hom) := Functor.map_isIso _ _
  have hH : IsIso (H.map e.inv) := Functor.map_isIso _ _
  have key : τ.app A = G.map e.hom ≫ τ.app B ≫ H.map e.inv := by
    rw [← Category.assoc, τ.naturality e.hom, Category.assoc, ← H.map_comp, e.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
  rw [key]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ hG (@IsIso.comp_isIso _ _ _ _ _ _ _ h hH)

/-- **The affine residue is a statement about modules.** For a cartesian square whose lower right
corner `V'` is affine and whose right-hand edge `f` is quasi-compact and quasi-separated, the
base-change comparison at `𝒪_X` is invertible as soon as it is invertible on global sections.

Both sides are quasi-coherent — the source by
`Stacks.AlgebraicGeometry.FlatBaseChange.isQuasicoherent_pullback_pushforward` and the target by
`…FlatBaseChange.isQuasicoherent_pushforward_pullback`, both of which need exactly that `f` is
quasi-compact and quasi-separated — and on an affine scheme global sections detect invertibility
of a morphism of quasi-coherent modules
(`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_app_top`).

This reduces the affine case of clause (b) of [Stacks, Tag 0E7K] to the bijectivity of one map
of modules, the comparison on global sections. -/
theorem isIso_baseChangeNatTrans_structureSheaf_of_isIso_appTop
    {X V X' V' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ V'} {f : X ⟶ V} {g : V' ⟶ V}
    (hw : IsPullback g' f' f g) [IsAffine V'] [QuasiCompact f] [QuasiSeparated f]
    (h : IsIso (((AffinePushforward.baseChangeNatTrans hw.w).app
      (Scheme.unitModule X)).app ⊤)) :
    IsIso ((AffinePushforward.baseChangeNatTrans hw.w).app (Scheme.unitModule X)) := by
  have hsrc : ((Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback g).obj
      (Scheme.unitModule X)).IsQuasicoherent :=
    FlatBaseChange.isQuasicoherent_pullback_pushforward g f (Scheme.unitModule X)
  have htgt : ((Scheme.Modules.pullback g' ⋙ Scheme.Modules.pushforward f').obj
      (Scheme.unitModule X)).IsQuasicoherent :=
    FlatBaseChange.isQuasicoherent_pushforward_pullback hw (Scheme.unitModule X)
  exact AffineBaseChange.isIso_of_isIso_app_top _ h

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
