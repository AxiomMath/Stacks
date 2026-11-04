module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.PullbackSystemCohomologyColimit
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.QuasiCompactOpen

/-!
# Étale cohomology of a base change to an algebraic field extension

Let `Y` be a quasi-compact and quasi-separated scheme over a field `L`, let `G` be an abelian
sheaf on the small étale site of `Y`, and let `Ω/L` be an algebraic extension. The base change
`Y_Ω` is the limit of the base changes `Y_E` to the finite subextensions `E` of `Ω/L`, with affine
transition morphisms, so [Stacks, Tag 03Q6] gives

`H^p(Y_Ω, G|_{Y_Ω}) = colim_E H^p(Y_E, G|_{Y_E})`.

This file proves the two halves of that equality: a class on `Y` that dies on `Y_Ω` already dies
on `Y_E` for some finite subextension `E`, and every class on `Y_Ω` comes from some `Y_E`.

## Main results

* `Stacks.EtaleCohomology.exists_finiteDimensional_restriction_eq_zero_of_isAlgebraic`
* `Stacks.EtaleCohomology.exists_finiteDimensional_eq_etaleCohomologyMapTo_of_isAlgebraic`

## Implementation notes

The base change is written `Spec E ×_{Spec L} Y`, as in
`AlgebraicGeometry.fextPullbackDiagram`, whose limit presentation
`AlgebraicGeometry.fextPullbackConeIsLimit` is the geometric input. The cohomological input is
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.exists_restriction_eq_zero_of_isLimit`, that is
[Stacks, Tag 09YQ] for the inverse images of one sheaf.

## References

* [Stacks Project, Tag 03Q6](https://stacks.math.columbia.edu/tag/03Q6)
* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable {L Ω : Type u} [Field L] [Field Ω] [Algebra L Ω]

/-- The finite subextensions of `Ω/L` form a nonempty type: `⊥` is one. -/
instance nonempty_fExt : Nonempty (FExt L Ω) :=
  ⟨⟨⊥, inferInstance⟩⟩

/-- The finite subextensions of `Ω/L` are directed under inclusion: `E ⊔ F` is finite over `L`
and contains both `E` and `F`. -/
instance isDirected_fExt : IsDirected (FExt L Ω) (· ≤ ·) where
  directed E F :=
    have := E.2
    have := F.2
    ⟨⟨E.1 ⊔ F.1, IntermediateField.finiteDimensional_sup E.1 F.1⟩,
      show E.1 ≤ E.1 ⊔ F.1 from le_sup_left, show F.1 ≤ E.1 ⊔ F.1 from le_sup_right⟩

variable {Y : Scheme.{u}} (f : Y ⟶ Spec (.of L))

/-- For a field extension `E/L`, the projection `Spec E ×_{Spec L} Y ⟶ Y` is affine. -/
instance isAffineHom_pullback_snd_spectrumMap (E : Type u) [Field E] [Algebra L E] :
    IsAffineHom (pullback.snd (spectrumMap L E) f) := by
  have : MorphismProperty.IsStableUnderBaseChangeAlong (@IsAffineHom) f :=
    ⟨fun sq hg => MorphismProperty.IsStableUnderBaseChange.of_isPullback sq hg⟩
  exact MorphismProperty.pullback_snd _ _ inferInstance

/-- If `Y` is quasi-compact, then so is `Spec E ×_{Spec L} Y` for every field extension `E/L`. -/
theorem compactSpace_pullback_spectrumMap [CompactSpace Y] (E : Type u) [Field E] [Algebra L E] :
    CompactSpace ↥(pullback (spectrumMap L E) f) :=
  QuasiCompact.compactSpace_of_compactSpace (pullback.snd (spectrumMap L E) f)

/-- If `Y` is quasi-separated, then so is `Spec E ×_{Spec L} Y` for every field extension
`E/L`. -/
theorem quasiSeparatedSpace_pullback_spectrumMap [QuasiSeparatedSpace Y] (E : Type u) [Field E]
    [Algebra L E] : QuasiSeparatedSpace ↥(pullback (spectrumMap L E) f) :=
  have : IsSeparated (pullback.snd (spectrumMap L E) f) := IsSeparated.of_isAffineHom _
  quasiSeparatedSpace_of_quasiSeparated (pullback.snd (spectrumMap L E) f)

/-- If `Y` is quasi-compact, then so is each base change `Spec E ×_{Spec L} Y` in
`AlgebraicGeometry.fextPullbackDiagram`. -/
instance compactSpace_fextPullbackDiagram_obj [CompactSpace Y] (E : (FExt L Ω)ᵒᵖ) :
    CompactSpace ((fextPullbackDiagram (k := L) (K := Ω) Y f).obj E) :=
  compactSpace_pullback_spectrumMap f E.unop.1

/-- If `Y` is quasi-separated, then so is each base change `Spec E ×_{Spec L} Y` in
`AlgebraicGeometry.fextPullbackDiagram`. -/
instance quasiSeparatedSpace_fextPullbackDiagram_obj [QuasiSeparatedSpace Y]
    (E : (FExt L Ω)ᵒᵖ) :
    QuasiSeparatedSpace ((fextPullbackDiagram (k := L) (K := Ω) Y f).obj E) :=
  quasiSeparatedSpace_pullback_spectrumMap f E.unop.1

/-- The transition morphisms of `AlgebraicGeometry.fextPullbackDiagram` are affine. -/
instance isAffineHom_fextPullbackDiagram_map {E F : (FExt L Ω)ᵒᵖ} (a : E ⟶ F) :
    IsAffineHom ((fextPullbackDiagram (k := L) (K := Ω) Y f).map a) :=
  fextPullbackTransition_isAffineHom Y f a

variable [Algebra.IsAlgebraic L Ω] [CompactSpace Y] [QuasiSeparatedSpace Y]
  (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})

/-- **A class dying on the base change to an algebraic extension dies at a finite stage.** Let
`Y` be a quasi-compact and quasi-separated scheme over a field `L`, let `G` be an abelian sheaf on
the small étale site of `Y` and let `Ω/L` be algebraic. If the restriction of
`ξ ∈ H^p(Y, G)` to the base change `Y_Ω` vanishes, then so does its restriction to `Y_E` for some
subextension `E` of `Ω/L` of finite degree. This is the injectivity half of
[Stacks, Tag 03Q6] for the system of finite subextensions of `Ω/L`. -/
theorem exists_finiteDimensional_restriction_eq_zero_of_isAlgebraic (p : ℕ)
    (ξ : Sheaf.H.{u + 1, u + 1} G p)
    (hξ : etaleCohomologyRestrictionMap.{u, u + 1, u + 1} (pullback.snd (spectrumMap L Ω) f) G p ξ
      = 0) :
    ∃ E : IntermediateField L Ω, FiniteDimensional L E ∧
      etaleCohomologyRestrictionMap.{u, u + 1, u + 1} (pullback.snd (spectrumMap L E) f) G p ξ
        = 0 := by
  obtain ⟨E, hE⟩ := SmallEtaleLimitCohomology.exists_restriction_eq_zero_of_isLimit
    (D := fextPullbackDiagram (k := L) (K := Ω) Y f) G
    (fun E => pullback.snd (spectrumMap L E.unop.1) f) (fun a => (Over.w ((Over.pullback f).map
      ((fextOverDiagram (k := L) (K := Ω)).map a))).symm)
    (fextPullbackConeIsLimit (k := L) (K := Ω) Y f) (pullback.snd (spectrumMap L Ω) f)
    (fun E => (Over.w ((Over.pullback f).map ((fextOverCone (k := L) (K := Ω)).π.app E))).symm)
    p ξ hξ
  exact ⟨E.unop.1, E.unop.2, hE⟩

/-- **Every class on the base change to an algebraic extension comes from a finite stage.** In
the situation of `exists_finiteDimensional_restriction_eq_zero_of_isAlgebraic`, every class in
`H^p(Y_Ω, G|_{Y_Ω})` is the image of a class in `H^p(Y_E, G|_{Y_E})` for some subextension `E` of
finite degree, under restriction along `Y_Ω ⟶ Y_E` followed by the canonical identification of the
inverse images. This is the surjectivity half of [Stacks, Tag 03Q6]. -/
theorem exists_finiteDimensional_eq_etaleCohomologyMapTo_of_isAlgebraic (p : ℕ)
    (y : Sheaf.H.{u + 1, u + 1}
      ((etaleAbelianInverseImage.{u, u + 1} (pullback.snd (spectrumMap L Ω) f)).obj G) p) :
    ∃ (E : FExt L Ω) (x : Sheaf.H.{u + 1, u + 1}
        ((etaleAbelianInverseImage.{u, u + 1} (pullback.snd (spectrumMap L E.1) f)).obj G) p),
      etaleCohomologyMapTo ((fextPullbackCone (k := L) (K := Ω) Y f).π.app (op E))
        ((etaleAbelianInverseImageCompIso'.{u, u + 1}
          ((fextPullbackCone (k := L) (K := Ω) Y f).π.app (op E))
          (pullback.snd (spectrumMap L E.1) f) (pullback.snd (spectrumMap L Ω) f)
          (Over.w ((Over.pullback f).map ((fextOverCone (k := L) (K := Ω)).π.app (op E)))).symm
          ).inv.app G) p x = y := by
  obtain ⟨E, x, hx⟩ := SmallEtaleLimitCohomology.exists_eq_etaleCohomologyMapTo_of_isLimit
    (D := fextPullbackDiagram (k := L) (K := Ω) Y f) G
    (fun E => pullback.snd (spectrumMap L E.unop.1) f) (fun a => (Over.w ((Over.pullback f).map
      ((fextOverDiagram (k := L) (K := Ω)).map a))).symm)
    (fextPullbackConeIsLimit (k := L) (K := Ω) Y f) (pullback.snd (spectrumMap L Ω) f)
    (fun E => (Over.w ((Over.pullback f).map ((fextOverCone (k := L) (K := Ω)).π.app E))).symm)
    p y
  exact ⟨E.unop, x, hx⟩

end Stacks.EtaleCohomology

end
