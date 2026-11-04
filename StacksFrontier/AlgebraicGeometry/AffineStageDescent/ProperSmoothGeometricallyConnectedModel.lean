module

public import StacksFrontier.AlgebraicGeometry.AffineStageDescent.ProperSmoothModel
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusDescentNoetherianApproximation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A proper smooth morphism with geometrically connected fibres comes from a Noetherian base

Let `f : X ⟶ S` be a proper smooth morphism with geometrically connected fibres and `S` affine.
Then `f` is the base change of a proper smooth morphism with geometrically connected fibres to a
Noetherian affine scheme.

This is `AlgebraicGeometry.exists_isPullback_isNoetherian_properSmooth` with the condition on the
fibres carried along. `S` is the limit of the spectra of the finitely generated subrings of
`Γ(S, ⊤)` (`AlgebraicGeometry.affineStageCone`); `f` is the base change of a proper flat morphism
of finite presentation to one of those spectra, and smoothness
(`AlgebraicGeometry.exists_smooth_baseChange_of_smooth_limitBaseChange`, [Stacks, Tag 0C0C]) and
geometric connectedness of the fibres
(`AlgebraicGeometry.exists_geometricallyConnected_pullback_snd`) each hold after passing to a
later stage. The two stages are compared in a common later one, where both conditions hold
because both are stable under base change.

## Main results

* `AlgebraicGeometry.exists_isPullback_isNoetherian_properSmoothGeometricallyConnected`.

## References

* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 0C0C](https://stacks.math.columbia.edu/tag/0C0C)
* [Stacks Project, Tag 081F](https://stacks.math.columbia.edu/tag/081F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- **A proper smooth morphism with geometrically connected fibres to an affine scheme is the
base change of a proper smooth morphism with geometrically connected fibres to a Noetherian
affine scheme.**

The absolute Noetherian approximation of
`AlgebraicGeometry.exists_isPullback_isNoetherian_properSmooth`, with geometric connectedness of
the fibres carried along: the locus of the base of a morphism of finite presentation whose fibre
is geometrically connected is locally constructible, so it contains the image of a late enough
stage. -/
@[ega "IV 8.1.2" "special case"]
theorem exists_isPullback_isNoetherian_properSmoothGeometricallyConnected {X S : Scheme.{u}}
    [IsAffine S] (f : X ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f] :
    ∃ (T Y : Scheme.{u}) (h : Y ⟶ T) (q : S ⟶ T) (q' : X ⟶ Y),
      IsNoetherian T ∧ IsProper h ∧ Smooth h ∧ GeometricallyConnected h ∧ IsPullback q' f h q := by
  let D := specAdjoinFinsetDiagram Γ(S, ⊤)
  let c := affineStageCone S
  have hc : IsLimit c := isLimit_affineStageCone S
  have hfp : FinitePresentation f := ⟨inferInstance, inferInstance, inferInstance⟩
  let f' : X ⟶ c.pt := f
  have : IsProper f' := ‹IsProper f›
  have : GeometricallyConnected f' := ‹GeometricallyConnected f›
  have : Flat f' := inferInstanceAs (Flat f)
  obtain ⟨i, X₁, f₁, g₁, hpr₁, -, hfp₁, hpb₁⟩ :=
    exists_stage_properFlatModel D c hc f' hfp
  obtain ⟨_, _, _⟩ := id hfp₁
  have : CompactSpace X₁ := QuasiCompact.compactSpace_of_compactSpace f₁
  have : QuasiSeparatedSpace X₁ := quasiSeparatedSpace_of_quasiSeparated f₁
  have : MorphismProperty.RespectsIso (@Smooth.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  -- `f₁`, as a morphism of `Over (D.obj i)` into the terminal object
  let X₀ : Over (D.obj i) := Over.mk f₁
  let Y₀ : Over (D.obj i) := Over.mk (𝟙 (D.obj i))
  let a : X₀ ⟶ Y₀ := Over.homMk f₁ (Category.comp_id f₁)
  have : CompactSpace X₀.left := inferInstanceAs (CompactSpace X₁)
  have : QuasiSeparatedSpace X₀.left := inferInstanceAs (QuasiSeparatedSpace X₁)
  have : CompactSpace Y₀.left := inferInstanceAs (CompactSpace (D.obj i))
  have : QuasiSeparatedSpace Y₀.left := inferInstanceAs (QuasiSeparatedSpace (D.obj i))
  have : LocallyOfFinitePresentation a.left := inferInstanceAs (LocallyOfFinitePresentation f₁)
  -- smoothness of a base change of `a` is smoothness of the corresponding base change of `f₁`
  have hsm : Smooth ((Over.pullback (c.π.app i)).map a).left := by
    rw [smooth_overPullback_map_left_iff a,
      ← MorphismProperty.cancel_left_of_respectsIso (@Smooth.{u}) hpb₁.isoPullback.hom,
      hpb₁.isoPullback_hom_snd]
    exact inferInstanceAs (Smooth f)
  obtain ⟨jsm, k, hjsm⟩ := exists_smooth_baseChange_of_smooth_limitBaseChange D c i X₀ Y₀ a hc
  rw [smooth_overPullback_map_left_iff a] at hjsm
  -- geometric connectedness of the fibres at a stage
  obtain ⟨jgc, hgcle, hjgc⟩ :=
    exists_geometricallyConnected_pullback_snd D c hc hpb₁ hfp₁
  -- a common later stage
  obtain ⟨m, hm₁, hm₂⟩ := exists_ge_ge jsm.unop jgc
  have him : i.unop ≤ m := (leOfHom k.unop).trans hm₁
  have hsmooth : Smooth (pullback.snd f₁ (transition D him)) := by
    rw [show transition D him = D.map (homOfLE hm₁).op ≫ D.map k by rw [← D.map_comp]; rfl]
    exact pullback_snd_comp_of f₁ (D.map k) (D.map (homOfLE hm₁).op) hjsm
  have hgconn : GeometricallyConnected (pullback.snd f₁ (transition D him)) := by
    rw [show transition D him = D.map (homOfLE hm₂).op ≫ transition D hgcle by
      rw [← D.map_comp]; rfl]
    exact pullback_snd_comp_of f₁ (transition D hgcle) (D.map (homOfLE hm₂).op) hjgc
  have hsq : IsPullback (pullback.fst f₁ (transition D him))
      (pullback.snd f₁ (transition D him)) f₁ (transition D him) :=
    IsPullback.of_hasPullback f₁ (transition D him)
  have hcond : g₁ ≫ f₁ = (f' ≫ c.π.app (op m)) ≫ transition D him := by
    rw [hpb₁.w, Category.assoc, c.w (homOfLE him).op]
  have hpb : IsPullback (pullback.lift g₁ (f' ≫ c.π.app (op m)) hcond) f'
      (pullback.snd f₁ (transition D him)) (c.π.app (op m)) := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) hsq
    rw [pullback.lift_fst, c.w (homOfLE him).op]
    exact hpb₁
  exact ⟨D.obj (op m), pullback f₁ (transition D him), pullback.snd f₁ (transition D him),
    c.π.app (op m), pullback.lift g₁ (f' ≫ c.π.app (op m)) hcond,
    isNoetherian_specAdjoinFinsetDiagram_obj _ (op m),
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsProper) hsq hpr₁,
    hsmooth, hgconn, hpb⟩

end AlgebraicGeometry

end
