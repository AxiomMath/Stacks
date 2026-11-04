module

public import StacksFrontier.AlgebraicGeometry.Spaces.CutoffBoundedNoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SchemeStageOfCutoffBoundedSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.CutoffBoundedFiniteLocallyFreeStageModel
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.CutoffBoundedFinitePresentationDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleOpenLocusOfCutoffBoundedApproximation

/-!
# Stacks 0D3D from W-systems over approximations bounded by the cutoff

`Space.exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_cutoffBoundedApproximation`
proves Stacks 0D3D from Stacks 0A0X, 07SQ, 07SR and 0D2X, part (2), for systems bounded by the
cutoff (`AlgebraicGeometry.Space.IsCutoffBoundedSystem`), and from Stacks 0D3A. This file
discharges four of those inputs:

* `h0A0X` is
  `Space.exists_descentSituation_arrow_isCutoffBoundedSystem_of_cutoffBoundedWSystems`,
  with its input Stacks 07SK for a system bounded by the cutoff discharged by
  `AlgebraicGeometry.Space.IsCutoffBoundedSystem.exists_model_of_finitePresentation`;
* `h07SQ` is
  `Space.DescentSituation.exists_isAffineSpace_system_obj_of_isCutoffBoundedSystem`;
* `h07SR` is
  `Space.DescentSituation.exists_isRepresentable_system_obj_of_isCutoffBoundedSystem`;
* `h0D2X` is
  `Space.DescentSituation.exists_isInvertibleModule_stage_model_of_isCutoffBoundedSystem`.

## Main results

* `Space.exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_cutoffBoundedWSystems`:
  the statement of Stacks 0D3D from W-systems over Noetherian approximations bounded by the cutoff
  (`hW`), Stacks 0A0W (`h0A0W`), Stacks 08K1 for systems bounded by the cutoff (`h08K1`) and
  Stacks 0D3A (`h0D3A`).

## Implementation notes

The hypothesis `hW` is `AlgebraicGeometry.Space.ElementaryChart.HasCutoffBoundedWSystems`, which
is proved as `AlgebraicGeometry.Space.ElementaryChart.hasCutoffBoundedWSystems`; the statement with
it discharged is
`Space.exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_isCutoffBoundedSystem`.
The other three are inputs still owed elsewhere: `h0A0W` and `h08K1` are the inputs of the 0A0X
assembly, and `h0D3A` is Stacks 0D3A at a residue field. Nothing here is registered.

## References

* [Stacks Project, Tag 0D3D](https://stacks.math.columbia.edu/tag/0D3D)
* [Stacks Project, Tag 0A0X](https://stacks.math.columbia.edu/tag/0A0X)
* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 07SR](https://stacks.math.columbia.edu/tag/07SR)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0D3D, from W-systems over Noetherian approximations bounded by the cutoff.** Let `S`
be a scheme, `f : X ⟶ Y` a proper morphism of algebraic spaces over `S` and `L` an invertible
`𝒪_X`-module. There is an open subspace `V ⊆ Y` such that a morphism `g : Y' ⟶ Y` of algebraic
spaces factors through `V` if and only if the pullback of `L` to `X' = Y' ×_Y X` is ample on
`X'/Y'` (Stacks 0D31).

This is
`Space.exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_cutoffBoundedApproximation`
with `h0A0X`, `h07SQ`, `h07SR` and `h0D2X` discharged. The hypotheses are all over the integers:
`hW`, the W-systems over Noetherian approximations bounded by the cutoff, proved as
`AlgebraicGeometry.Space.ElementaryChart.hasCutoffBoundedWSystems` (the form without it is
`Space.exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_isCutoffBoundedSystem`);
and the inputs still owed, `h0A0W`, Stacks 0A0W; `h08K1`, Stacks 08K1 for a system bounded by the
cutoff; and `h0D3A`, Stacks 0D3A
at a residue field over a Noetherian scheme of the site. It is not registered. -/
theorem exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_cutoffBoundedWSystems
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hW : ElementaryChart.HasCutoffBoundedWSystems B hZ)
    (h0A0W : ∀ {X Y : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)} (_ : IsAlgebraicSpace B _ hZ
      X) (_ : IsAlgebraicSpace B _ hZ Y)
      (f : X ⟶ Y) (_ : IsProper B _ hZ f) (_ : IsQuasiCompactSpace B _ hZ Y)
      (_ : IsAbsolutelyQuasiSeparated B _ hZ B.contains_terminal Y),
      ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·)) (_ : Nonempty I)
        (D : Iᵒᵖ ⥤ ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)) (t : D ⟶ (Functor.const
          Iᵒᵖ).obj Y) (π : (Functor.const Iᵒᵖ).obj X ⟶ D),
        (∀ i, IsAlgebraicSpace B _ hZ (D.obj i)) ∧
        (∀ i, IsProper B _ hZ (t.app i) ∧ IsFinitePresentation B _ hZ (t.app i)) ∧
        (∀ ⦃i j : Iᵒᵖ⦄ (e : i ⟶ j), IsClosedImmersion B _ hZ (D.map e)) ∧
        (∀ i, IsClosedImmersion B _ hZ (π.app i)) ∧
        π ≫ t = (Functor.const Iᵒᵖ).map f ∧
        Nonempty (IsLimit (Cone.mk X π)))
    (h08K1 : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : Iᵒᵖ ⥤
      ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)), IsCutoffBoundedSystem B _ hZ D →
      (∀ i : I, IsAlgebraicSpace B _ hZ (D.obj (op i))) →
      (∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom B _ hZ (D.map g)) →
      IsAlgebraicSpace B _ hZ (limit D) →
      ∀ (i₀ : I) {X₀ Y₀ : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)} (a : X₀ ⟶ D.obj (op i₀))
        (b : Y₀ ⟶ D.obj (op i₀)) (f₀ : X₀ ⟶ Y₀)
        (hf₀ : f₀ ≫ b = a), IsAlgebraicSpace B _ hZ X₀ → IsAlgebraicSpace B _ hZ Y₀ →
        IsQuasiCompactSpace B _ hZ (D.obj (op i₀)) →
        IsAbsolutelyQuasiSeparated B _ hZ hZ (D.obj (op i₀)) →
        IsQuasiCompactSpace B _ hZ X₀ → IsAbsolutelyQuasiSeparated B _ hZ hZ X₀ →
        IsQuasiCompactSpace B _ hZ Y₀ → IsAbsolutelyQuasiSeparated B _ hZ hZ Y₀ →
        IsProper B _ hZ (pullback.map (limit.π D (op i₀)) a (limit.π D (op i₀)) b (𝟙 _) f₀ (𝟙 _)
          (by simp) (by simp [hf₀])) →
        IsLocallyOfFiniteType B _ hZ f₀ →
        ∃ (i : I) (hi : i₀ ≤ i), IsProper B _ hZ (pullback.map (D.map (homOfLE hi).op) a
          (D.map (homOfLE hi).op) b (𝟙 _) f₀ (𝟙 _) (by simp) (by simp [hf₀])))
    (h0D3A : ∀ (T : BigFppfOver B (⊤_ Scheme.{u}) hZ),
      _root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B _ hZ).obj T) →
      ∀ {Xᵢ : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ}
        (fᵢ : Xᵢ ⟶ schemeSpace T), IsProper B _ hZ fᵢ.hom →
      ∀ (Lᵢ : Modules.{u, u} B _ hZ Xᵢ.1 Xᵢ.2),
        Stacks.SheafOfModules.IsInvertible (structurePresheaf B _ hZ Xᵢ.1)
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B _ hZ Xᵢ.1 Xᵢ.2).O)).property Lᵢ →
      ∀ y : (BigFppfOver.toScheme B _ hZ).obj T,
        (∀ ⦃X₀ : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ⦄ (p₀ : X₀ ⟶ Xᵢ)
          (f₀ : X₀ ⟶ schemeSpace (residueFieldObject B _ hZ T y
              (B.residueField_spec_contains T.left.property y))),
          IsPullback p₀ f₀ fᵢ (schemeSpaceMap
              (residueFieldMap B _ hZ T y (B.residueField_spec_contains T.left.property y))) →
          IsRelativelyAmple B _ hZ f₀ ((modulePullback B _ hZ p₀).obj Lᵢ)) →
        ∃ V : ((BigFppfOver.toScheme B _ hZ).obj T).Opens, y ∈ V ∧
          ∀ ⦃X₁ : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ⦄ (p₁ : X₁ ⟶ Xᵢ)
            (f₁ : X₁ ⟶ schemeSpace (openSub T V)),
            IsPullback p₁ f₁ fᵢ (schemeSpaceMap (openSubHom T V)) →
            IsRelativelyAmple B _ hZ f₁ ((modulePullback B _ hZ p₁).obj Lᵢ))
    {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (hf : IsProper B S hS f.hom)
    {L : Modules.{u, u} B S hS X.1 X.2}
    (hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O)).property L) :
    ∃ V : Subfunctor Y.1, IsOpenSubspace B S hS V ∧
      ∀ ⦃X' Y' : AlgebraicSpaces B S hS⦄ (g : Y' ⟶ Y) (p : X' ⟶ X) (f' : X' ⟶ Y'),
        IsPullback p f' f g →
          ((∃ l : Y'.1 ⟶ V.toFunctor, l ≫ V.ι = g.hom) ↔
            IsRelativelyAmple B S hS f' ((modulePullback B S hS p).obj L)) := by
  refine exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_cutoffBoundedApproximation hZ
    (exists_descentSituation_arrow_isCutoffBoundedSystem_of_cutoffBoundedWSystems hZ hW h0A0W
      (fun {_} _ _ D hC hD hA hQc hQs =>
        IsCutoffBoundedSystem.exists_model_of_finitePresentation B _ hZ hZ D hD hA hQc hQs hC)
      h08K1)
    (fun D hD hX => D.exists_isAffineSpace_system_obj_of_isCutoffBoundedSystem hD hX)
    (fun D hD hX => D.exists_isRepresentable_system_obj_of_isCutoffBoundedSystem hD hX)
    (fun D hc L hL => D.exists_isInvertibleModule_stage_model_of_isCutoffBoundedSystem hc L hL)
    h0D3A hf hL

end AlgebraicGeometry.Space

end
