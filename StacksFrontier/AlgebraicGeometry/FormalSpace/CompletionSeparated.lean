module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionClosedImmersion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionDiagonal
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionQuasiCompact
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SeparatedMorphism

/-!
# Separation axioms for a morphism of completions

Let `S` be a scheme contained in a big fppf site `B`, let `f : X' ⟶ X` be a morphism of
algebraic spaces over `S` and let `T` be a set of points of `X`. **Stacks 0GDG** says that if
`f` is separated, respectively quasi-separated, then so is the induced morphism of completions
`f_{/T} : X'_{/|f|⁻¹ T} ⟶ X_{/T}`.

## Main results

* `AlgebraicGeometry.Space.pullback_diagonal_completionSheafMap`: the relative diagonal of
  `f_{/T}` is the diagonal of Stacks 0GDF, read through the identification of the chosen fibre
  product `X'_{/T'} ×_{X_{/T}} X'_{/T'}` with `(X' ×_X X')_{/T''}`.
* `AlgebraicGeometry.FormalSpace.isSeparatedMorphism_completionSheafMap`: **Stacks 0GDG**, the
  separatedness clause.
* `AlgebraicGeometry.FormalSpace.isQuasiSeparatedMorphism_completionSheafMap`: **Stacks
  0GDG**, the quasi-separatedness clause.

## Implementation notes

Both clauses are conditions on the relative diagonal of `f_{/T}`, and **Stacks 0GDF** —
`AlgebraicGeometry.Space.isPullback_completionSheafPullback` together with
`AlgebraicGeometry.Space.completionSheafDiagonal_eq_completionSheafMap_diagonal` — identifies
that relative diagonal with the completion of the relative diagonal of `f` along the set `T''`
of points of `X' ×_X X'` lying over `T`. The identification holds up to two isomorphisms: the
comparison of `(X' ×_X X')_{/T''}` with the chosen fibre product
`X'_{/T'} ×_{X_{/T}} X'_{/T'}`, and the `eqToHom` transporting the completion of `X'` along the
inverse image of `T''` under `Δ_f` to the completion along `T'`.

So the separatedness clause is **Stacks 0GDC**, the completion of a closed immersion is a closed
immersion, applied to `Δ_f`, together with stability of closed immersions of formal algebraic
spaces under composition with an isomorphism; and the quasi-separatedness clause is **Stacks
0GDE**, the completion of a quasi-compact morphism is quasi-compact, applied to `Δ_f`, together
with the corresponding invariance of quasi-compactness. Stacks 0GDE delivers quasi-compactness
in the Bootstrap form of Stacks 03XZ, which
`AlgebraicGeometry.Space.isQuasiCompactULift_of_forall_pullback_fst` turns into the condition
`AlgebraicGeometry.Space.IsQuasiCompactULift` that
`AlgebraicGeometry.FormalSpace.IsQuasiSeparatedMorphism` is built from.

The transport of quasi-compactness along the `eqToHom` is isolated in
`isQuasiCompactULift_eqToHom_comp`, which takes the equality of sets of points as a hypothesis
and substitutes it; transporting along the concrete equality instead leaves the kernel reducing
that equality, which it does not finish.

Closedness of `T` is not used, exactly as in Stacks 0GDC and Stacks 0GDE: it is what makes the
completions formal algebraic spaces, which neither separation axiom refers to. Algebraicity of
`X` and `X'` is used, through those two inputs, and algebraicity of `X' ×_X X'` follows from it
by `AlgebraicGeometry.isAlgebraicSpace_pullback`.

## References

* [Stacks Project, Tag 0GDG](https://stacks.math.columbia.edu/tag/0GDG)
* [Stacks Project, Tag 0GDF](https://stacks.math.columbia.edu/tag/0GDF)
* [Stacks Project, Tag 0GDC](https://stacks.math.columbia.edu/tag/0GDC)
* [Stacks Project, Tag 0GDE](https://stacks.math.columbia.edu/tag/0GDE)
* [Stacks Project, Tag 0ARN](https://stacks.math.columbia.edu/tag/0ARN)
* [Stacks Project, Tag 03HL](https://stacks.math.columbia.edu/tag/03HL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
private instance (priority := high) hasPullbacks_presheaf_CompletionSeparated :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

private instance (priority := high) hasPullback_presheaf_CompletionSeparated
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_CompletionSeparated B S hS).has_limit _

namespace Space

/-- The relative diagonal of the completed morphism `f_{/T}` is the diagonal
`AlgebraicGeometry.Space.completionSheafDiagonal` of Stacks 0GDF, composed with the comparison
of `(X' ×_X X')_{/T''}` with the chosen fibre product `X'_{/T'} ×_{X_{/T}} X'_{/T'}`. -/
theorem pullback_diagonal_completionSheafMap (f : X' ⟶ X) (T : Set (points B S hS X)) :
    pullback.diagonal (completionSheafMap B S hS f T) =
      completionSheafDiagonal B S hS f T ≫
        (isPullback_completionSheafPullback B S hS f f T).isoPullback.hom := by
  apply pullback.hom_ext
  · rw [pullback.diagonal_fst, Category.assoc,
      (isPullback_completionSheafPullback B S hS f f T).isoPullback_hom_fst,
      completionSheafDiagonal_comp_fst]
  · rw [pullback.diagonal_snd, Category.assoc,
      (isPullback_completionSheafPullback B S hS f f T).isoPullback_hom_snd,
      completionSheafDiagonal_comp_snd]

end Space

namespace FormalSpace

/-- Quasi-compactness of a morphism out of a completion is unchanged by transporting the source
along an equality of sets of points. -/
private theorem isQuasiCompactULift_eqToHom_comp (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    {T₁ T₂ : Set (Space.points B S hS Z)} (h : T₁ = T₂) {W : FppfSheaf B S hS}
    (g : Space.completionSheaf B S hS Z T₂ ⟶ W)
    (hg : Space.IsQuasiCompactULift.{u + 1} B S hS g.hom) :
    Space.IsQuasiCompactULift.{u + 1} B S hS
      (eqToHom (congrArg (Space.completionSheaf B S hS Z) h) ≫ g).hom := by
  subst h
  simpa using hg

/-- **Stacks 0GDG, the separatedness clause.** Let `f : X' ⟶ X` be a morphism of algebraic
spaces over `S` and let `T` be a set of points of `X`. If `f` is separated, then the induced
morphism of completions `f_{/T} : X'_{/|f|⁻¹ T} ⟶ X_{/T}` is separated: its relative diagonal
is the completion of the relative diagonal of `f`, which is a closed immersion by Stacks
0GDC. -/
@[stacks 0GDG "separated: the completion of a separated morphism of algebraic spaces along a \
set of points of its target is a separated morphism of formal algebraic spaces, separatedness \
of the completion read as the separatedness axiom of Stacks 0ARN"]
theorem isSeparatedMorphism_completionSheafMap
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (f : X' ⟶ X) (T : Set (Space.points B S hS X))
    (hf : Space.IsSeparated B S hS f) :
    IsSeparatedMorphism B S hS (Space.completionSheafMap B S hS f T) := by
  have hX'' : IsAlgebraicSpace B S hS (pullback f f) :=
    isAlgebraicSpace_pullback B S hS f f hX' hX' hX
  have hΔ : IsClosedImmersion B S hS
      (Space.completionSheafMap B S hS (pullback.diagonal f)
        (Space.pullbackPoints B S hS f f T)) :=
    isClosedImmersion_completionSheafMap B S hS hX' hX'' (pullback.diagonal f) _ hf
  change IsClosedImmersion B S hS (pullback.diagonal (Space.completionSheafMap B S hS f T))
  rw [Space.pullback_diagonal_completionSheafMap B S hS f T,
    Space.completionSheafDiagonal_eq_completionSheafMap_diagonal]
  exact isClosedImmersion_comp B S hS _ _
    (isClosedImmersion_comp B S hS _ _ (isClosedImmersion_of_isIso B S hS _) hΔ)
    (isClosedImmersion_of_isIso B S hS _)

/-- **Stacks 0GDG, the quasi-separatedness clause.** Let `f : X' ⟶ X` be a morphism of algebraic
spaces over `S` and let `T` be a set of points of `X`. If `f` is quasi-separated, then the
induced morphism of completions `f_{/T} : X'_{/|f|⁻¹ T} ⟶ X_{/T}` has quasi-compact relative
diagonal: that relative diagonal is the completion of the relative diagonal of `f`, which is
quasi-compact by Stacks 0GDE. -/
@[stacks 0GDG "quasi-separated: the completion of a quasi-separated morphism of algebraic \
spaces along a set of points of its target has quasi-compact relative diagonal. \
Quasi-compactness of the diagonal is read as `IsQuasiSeparatedMorphism`, that is, as \
`Space.IsQuasiCompactULift`: every base change of the diagonal along a morphism from a \
quasi-compact algebraic space has quasi-compact source. The implementation notes of \
`StacksFrontier.AlgebraicGeometry.FormalSpace.SeparatedMorphism` record that condition as a \
priori stronger than the source's quasi-compactness of a morphism of formal algebraic spaces, \
so the conclusion delivered is a priori stronger than the source's; the hypothesis is the \
source's quasi-separatedness of Stacks 03HL, part (3)"]
theorem isQuasiSeparatedMorphism_completionSheafMap
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (f : X' ⟶ X) (T : Set (Space.points B S hS X))
    (hf : Space.IsQuasiSeparated B S hS f) :
    IsQuasiSeparatedMorphism B S hS (Space.completionSheafMap B S hS f T) := by
  have hX'' : IsAlgebraicSpace B S hS (pullback f f) :=
    isAlgebraicSpace_pullback B S hS f f hX' hX' hX
  obtain ⟨_, hprop⟩ := isQuasiCompact_completionSheafMap B S hS hX' hX''
    (pullback.diagonal f) (Space.pullbackPoints B S hS f f T) hf
  have hΔ : Space.IsQuasiCompactULift.{u + 1} B S hS
      (Space.completionSheafMap B S hS (pullback.diagonal f)
        (Space.pullbackPoints B S hS f f T)).hom :=
    Space.isQuasiCompactULift_of_forall_pullback_fst.{u + 1} B S hS _ hprop
  have hd : Space.IsQuasiCompactULift.{u + 1} B S hS
      (Space.completionSheafDiagonal B S hS f T).hom := by
    rw [Space.completionSheafDiagonal_eq_completionSheafMap_diagonal]
    exact isQuasiCompactULift_eqToHom_comp B S hS X'
      (Space.pointsMap_diagonal_preimage_pullbackPoints B S hS f T).symm _ hΔ
  change Space.IsQuasiCompactULift.{u + 1} B S hS
    (pullback.diagonal (Space.completionSheafMap B S hS f T)).hom
  rw [Space.pullback_diagonal_completionSheafMap B S hS f T]
  exact Space.isQuasiCompactULift_postcomp.{u + 1} B S hS
    ((sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).mapIso
      (Space.isPullback_completionSheafPullback B S hS f f T).isoPullback) _ hd

end FormalSpace

end AlgebraicGeometry

end
