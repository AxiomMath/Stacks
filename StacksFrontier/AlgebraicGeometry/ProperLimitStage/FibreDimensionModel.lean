module

public import StacksFrontier.AlgebraicGeometry.FibreDimension.IntegralReduction
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.ProperLimitStage.SeparatedModel
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A proper model of finite presentation over a stage that still bounds the fibre dimensions

`StacksFrontier/AlgebraicGeometry/ProperLimitStage/SeparatedModel.lean` writes a proper morphism of
finite presentation over a cofiltered limit of Noetherian schemes as the base change of a proper
morphism of finite presentation over a stage, isomorphism included
(`AlgebraicGeometry.exists_isProper_finitePresentation_model_of_isLimit`). It says nothing about
the dimensions of the fibres of the model, and a bound on the fibres of the morphism over the
limit is no bound on the fibres of the model: the model has fibres over every point of the stage,
and only those over the image of the limit are accounted for.

This file adds the missing clause. [Stacks, Tag 05M5], in the form
`AlgebraicGeometry.exists_relativeDimensionLE_baseChangeMap_of_isLimit`, moves a bound on the
relative dimension of the base change to the limit down to a bound on the base change to some
later stage; replacing the model by its base change along that transition keeps properness
(by base change), keeps finite presentation
(`AlgebraicGeometry.finitePresentation_overPullbackObj`) and keeps the isomorphism with the
source (`AlgebraicGeometry.overPullbackObj_shiftIso`). So one more transition is appended to the
assembly of the model theorem and the bound comes with it.

## Main results

* `AlgebraicGeometry.topologicalKrullDim_fiber_eq_of_overIso`: isomorphic objects of a category
  of schemes over a base have fibres of equal dimension over each point of the base.
* `AlgebraicGeometry.forall_topologicalKrullDim_fiber_baseChangeMap_terminal_le_iff`: the
  translation between the two spellings of the base change of an object over a stage — the
  structure morphism of `CategoryTheory.Over.pullback`, and `AlgebraicGeometry.baseChangeMap` at
  the morphism to the terminal object — read on the dimensions of the fibres.
* `AlgebraicGeometry.exists_isProper_finitePresentation_relativeDimensionLE_model_of_isLimit`:
  **the model theorem with the fibre-dimension bound**.
* `exists_isProper_finitePresentation_relativeDimensionLE_baseChange_of_isAffine`:
  the same over an arbitrary affine base, which is what the limit-descent paragraph of
  [Stacks, Tag 0E7D] needs: it reduces a statement about a proper morphism of finite presentation
  with fibres of dimension at most `d` over an arbitrary affine base to the same statement over
  an affine *Noetherian* base.

## Implementation notes

**The two spellings of a base change have to be reconciled, and that is the whole cost.** The
model theorem delivers an object `Xⱼ` of `CategoryTheory.Over (D.obj j)` and expresses the source
as `(Over.pullback (c.π.app j)).obj Xⱼ`, whose structure morphism is
`pullback.snd Xⱼ.hom (c.π.app j)`. Tag 05M5 is stated for `AlgebraicGeometry.baseChangeMap`,
which puts the base-change parameter first and reads the structure morphism as the morphism to
the terminal object `Over.mk (𝟙 (D.obj j))`, so its target is `pullback (c.π.app j) (𝟙 _)` rather
than the stage itself. The two differ by `CategoryTheory.Limits.pullbackSymmetry` on the source
and by the projection `pullback.fst b (𝟙 _)`, an isomorphism, on the target, and
`AlgebraicGeometry.topologicalKrullDim_fiber_eq_of_square` — the fibre comparison of
`AlgebraicGeometry.fiberHomeoOfSquare` — carries the dimensions across that square in both
directions at once.

No new fibre-comparison lemma is needed for this: `topologicalKrullDim_fiber_eq_of_square` is an
equality of dimensions across a square whose horizontal maps are a homeomorphism and an injection,
so it serves the hypothesis of Tag 05M5 and its conclusion alike.

The relative-dimension hypotheses of Tag 05M5 are phrased with
`AlgebraicGeometry.RelativeDimensionLE`, which is not a `CategoryTheory.MorphismProperty` — it
takes the local finite-type condition as an instance argument — so
`AlgebraicGeometry.baseChangeMap_prop_iff` does not apply and the translation cannot be had from
the morphism-property machinery. It is instead taken through the fibrewise form of Tag 05F8,
`AlgebraicGeometry.relativeDimensionLE_iff_forall_fiberDimension_le`.

## References

* [Stacks Project, Tag 0E7D](https://stacks.math.columbia.edu/tag/0E7D)
* [Stacks Project, Tag 05M5](https://stacks.math.columbia.edu/tag/05M5)
* [Stacks Project, Tag 0H3V](https://stacks.math.columbia.edu/tag/0H3V)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 081F](https://stacks.math.columbia.edu/tag/081F)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

universe u

noncomputable section

/-- **Isomorphic schemes over a base have fibres of the same dimension.** If `A` and `B` are
isomorphic as schemes over `S`, then for every `s : S` the fibre of `A.hom` over `s` and the
fibre of `B.hom` over `s` have the same topological Krull dimension.

The isomorphism is a homeomorphism on the sources and commutes with the two structure morphisms
over the identity of `S`, so `AlgebraicGeometry.topologicalKrullDim_fiber_eq_of_square` applies. -/
lemma topologicalKrullDim_fiber_eq_of_overIso {S : Scheme.{u}} {A B : Over S} (e : A ≅ B)
    (s : S) :
    topologicalKrullDim (A.hom.fiber s) = topologicalKrullDim (B.hom.fiber s) := by
  have _ : IsIso e.hom.left := (Over.forget S).map_isIso e.hom
  have hcomm : ∀ x : A.left, B.hom ((Scheme.homeoOfIso (asIso e.hom.left)) x) = (𝟙 S) (A.hom x) :=
    fun x => congrArg (fun m : A.left ⟶ S => m.base x) e.hom.w
  have hinj : Function.Injective (𝟙 S : S ⟶ S).base := fun _ _ h => h
  exact topologicalKrullDim_fiber_eq_of_square B.hom A.hom
    (Scheme.homeoOfIso (asIso e.hom.left)) (𝟙 S) hinj hcomm s

/-- The projection `pullback.fst b (𝟙 S)` is bijective on points, being an isomorphism. -/
private theorem bijective_base_pullback_fst_overMk_id {S T : Scheme.{u}} (b : T ⟶ S) :
    Function.Bijective (pullback.fst b (Over.mk (𝟙 S)).hom).base := by
  have : IsIso (pullback.fst b (Over.mk (𝟙 S)).hom) :=
    inferInstanceAs (IsIso (pullback.fst b (𝟙 S)))
  exact (Scheme.homeoOfIso (asIso (pullback.fst b (Over.mk (𝟙 S)).hom))).bijective

/-- **The fibre of the base change of an object over a base, in the two spellings.** For
`b : T ⟶ S` and `Z : CategoryTheory.Over S`, the fibre of
`AlgebraicGeometry.baseChangeMap b Z (Over.mk (𝟙 S)) (Over.homMk Z.hom)` over a point `y` of
`pullback b (𝟙 S)` has the same dimension as the fibre of the structure morphism
`pullback.snd Z.hom b` of `(Over.pullback b).obj Z` over the image of `y` under the projection
`pullback.fst b (𝟙 S)`.

The square whose horizontal maps are `CategoryTheory.Limits.pullbackSymmetry` and that projection
commutes by `AlgebraicGeometry.baseChangeMap_fst`, the first is a homeomorphism and the second an
isomorphism, so `AlgebraicGeometry.topologicalKrullDim_fiber_eq_of_square` applies. -/
lemma topologicalKrullDim_fiber_baseChangeMap_terminal_eq {S T : Scheme.{u}} (b : T ⟶ S)
    (Z : Over S) (y : (pullback b (Over.mk (𝟙 S)).hom : Scheme.{u})) :
    topologicalKrullDim ((baseChangeMap b Z (Over.mk (𝟙 S))
        (Over.homMk Z.hom : Z ⟶ Over.mk (𝟙 S))).fiber y) =
      topologicalKrullDim ((pullback.snd Z.hom b).fiber
        ((pullback.fst b (Over.mk (𝟙 S)).hom).base y)) := by
  have hcomm : ∀ x : (pullback b Z.hom : Scheme.{u}),
      (pullback.snd Z.hom b) ((Scheme.homeoOfIso (pullbackSymmetry b Z.hom)) x) =
        (pullback.fst b (Over.mk (𝟙 S)).hom)
          ((baseChangeMap b Z (Over.mk (𝟙 S)) (Over.homMk Z.hom)) x) :=
    fun x => congrArg (fun m : (pullback b Z.hom : Scheme.{u}) ⟶ T => m.base x)
      ((pullbackSymmetry_hom_comp_snd b Z.hom).trans
        (baseChangeMap_fst b Z (Over.mk (𝟙 S)) (Over.homMk Z.hom)).symm)
  exact topologicalKrullDim_fiber_eq_of_square (pullback.snd Z.hom b)
    (baseChangeMap b Z (Over.mk (𝟙 S)) (Over.homMk Z.hom))
    (Scheme.homeoOfIso (pullbackSymmetry b Z.hom)) (pullback.fst b (Over.mk (𝟙 S)).hom)
    (bijective_base_pullback_fst_overMk_id b).1 hcomm y

/-- **A bound on the dimensions of the fibres of a base change, in the two spellings.** Every
fibre of `AlgebraicGeometry.baseChangeMap b Z (Over.mk (𝟙 S)) (Over.homMk Z.hom)` has dimension
at most `d` exactly when every fibre of the structure morphism `pullback.snd Z.hom b` of
`(Over.pullback b).obj Z` does.

This is `AlgebraicGeometry.topologicalKrullDim_fiber_baseChangeMap_terminal_eq` read in both
directions, the projection `pullback.fst b (𝟙 S)` being an isomorphism and so a bijection on
points. -/
lemma forall_topologicalKrullDim_fiber_baseChangeMap_terminal_le_iff {S T : Scheme.{u}}
    (b : T ⟶ S) (Z : Over S) (d : ℕ) :
    (∀ y : (pullback b (Over.mk (𝟙 S)).hom : Scheme.{u}),
        topologicalKrullDim ((baseChangeMap b Z (Over.mk (𝟙 S))
          (Over.homMk Z.hom : Z ⟶ Over.mk (𝟙 S))).fiber y) ≤ (d : WithBot ℕ∞)) ↔
      ∀ t : T, topologicalKrullDim ((pullback.snd Z.hom b).fiber t) ≤ (d : WithBot ℕ∞) := by
  refine ⟨fun h t => ?_, fun h y => ?_⟩
  · obtain ⟨y, hy⟩ := (bijective_base_pullback_fst_overMk_id b).2 t
    rw [← hy, ← topologicalKrullDim_fiber_baseChangeMap_terminal_eq]
    exact h y
  · rw [topologicalKrullDim_fiber_baseChangeMap_terminal_eq]
    exact h _

/-- **A proper morphism of finite presentation with bounded fibre dimension over a cofiltered
limit of Noetherian schemes has a proper model of finite presentation over a stage whose fibres
are still bounded.** Let `D` be a cofiltered inverse system of Noetherian quasi-separated schemes
with affine transition morphisms and limit cone `c`, let `X` be proper and of finite presentation
over `c.pt`, and suppose every fibre of `X.hom` has dimension at most `d`. Then there are a stage
`j` and a scheme `Xⱼ` over `D.obj j`, proper and of finite presentation over that stage and with
every fibre of dimension at most `d`, together with an isomorphism
`X ≅ (Over.pullback (c.π.app j)).obj Xⱼ` over `c.pt`.

`AlgebraicGeometry.exists_isProper_finitePresentation_model_of_isLimit` produces the model and the
isomorphism; the bound on the fibres of `X.hom` is carried across the isomorphism by
`AlgebraicGeometry.topologicalKrullDim_fiber_eq_of_overIso` and read in the spelling of Tag 05M5
by `AlgebraicGeometry.forall_topologicalKrullDim_fiber_baseChangeMap_terminal_le_iff`, so that
`AlgebraicGeometry.exists_relativeDimensionLE_baseChangeMap_of_isLimit` supplies a transition
after which the model's own fibres are bounded. Base changing the model along that transition
keeps properness, keeps finite presentation and keeps the isomorphism. -/
@[sga "1 VIII 3.6" "(ii) ⇒ (i), proper case",
  sga "1 VIII 6.6" "partial",
  sga "4 VII 5.2" "b, special case"]
theorem exists_isProper_finitePresentation_relativeDimensionLE_model_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)] [∀ i : I, IsNoetherian (D.obj i)]
    (c : Cone D) (hc : IsLimit c)
    (X : Over c.pt) [IsProper X.hom] (hX : FinitePresentation X.hom) (d : ℕ)
    (hdim : ∀ s : c.pt, topologicalKrullDim (X.hom.fiber s) ≤ (d : WithBot ℕ∞)) :
    ∃ (j : I) (Xⱼ : Over (D.obj j)), FinitePresentation Xⱼ.hom ∧ IsProper Xⱼ.hom ∧
      (∀ t : D.obj j, topologicalKrullDim (Xⱼ.hom.fiber t) ≤ (d : WithBot ℕ∞)) ∧
      Nonempty (X ≅ (Over.pullback (c.π.app j)).obj Xⱼ) := by
  obtain ⟨j, Z, hfp, hprop, ⟨e⟩⟩ :=
    exists_isProper_finitePresentation_model_of_isLimit D c hc X hX
  have _ : LocallyOfFinitePresentation Z.hom := hfp.1
  have _ : QuasiCompact Z.hom := hfp.2.1
  have _ : LocallyOfFiniteType (Over.homMk Z.hom : Z ⟶ Over.mk (𝟙 (D.obj j))).left :=
    inferInstanceAs (LocallyOfFiniteType Z.hom)
  have _ : QuasiCompact (Over.homMk Z.hom : Z ⟶ Over.mk (𝟙 (D.obj j))).left :=
    inferInstanceAs (QuasiCompact Z.hom)
  have _ : CompactSpace (Over.mk (𝟙 (D.obj j))).left :=
    inferInstanceAs (CompactSpace (D.obj j))
  have hrel : RelativeDimensionLE (baseChangeMap (c.π.app j) Z (Over.mk (𝟙 (D.obj j)))
      (Over.homMk Z.hom (Category.comp_id Z.hom))) d := by
    rw [relativeDimensionLE_iff_forall_fiberDimension_le]
    refine (forall_topologicalKrullDim_fiber_baseChangeMap_terminal_le_iff
      (c.π.app j) Z d).mpr fun s => ?_
    have hs := hdim s
    rw [topologicalKrullDim_fiber_eq_of_overIso e s] at hs
    exact hs
  obtain ⟨i, g, hrel'⟩ := exists_relativeDimensionLE_baseChangeMap_of_isLimit D c hc j Z
    (Over.mk (𝟙 (D.obj j))) (Over.homMk Z.hom (Category.comp_id Z.hom)) d hrel
  rw [relativeDimensionLE_iff_forall_fiberDimension_le] at hrel'
  exact ⟨i, (Over.pullback (D.map g)).obj Z, finitePresentation_overPullbackObj _ Z hfp,
    MorphismProperty.of_isPullback (P := @IsProper)
      (IsPullback.of_hasPullback Z.hom (D.map g)) hprop,
    (forall_topologicalKrullDim_fiber_baseChangeMap_terminal_le_iff (D.map g) Z d).mp hrel',
    ⟨e ≪≫ overPullbackObj_shiftIso D c g Z⟩⟩

/-- **A proper scheme of finite presentation with bounded fibre dimension over an affine scheme is
the base change of one over an affine Noetherian scheme of finite type over the integers.** Let
`S` be affine and let `X` be proper and of finite presentation over `S` with every fibre of
dimension at most `d`. Then there are an affine Noetherian scheme `T` of finite type over `ℤ`, a
morphism `q : S ⟶ T`, and a scheme `XT` over `T` which is proper and of finite presentation over
it with every fibre of dimension at most `d`, together with an isomorphism `X ≅ XT ×_T S` over
`S`.

This is the **second limit reduction of [Stacks, Tag 0E7D]** on its geometric side: it reduces a
statement about a proper morphism of finite presentation with fibres of dimension at most `d` over
an arbitrary affine base to the same statement over an affine *Noetherian* base, which is where
[Stacks, Tag 02V7] lives. It is
`AlgebraicGeometry.exists_isProper_finitePresentation_relativeDimensionLE_model_of_isLimit` at
`AlgebraicGeometry.affineStageCone`, and is the fibre-dimension-carrying companion of
`AlgebraicGeometry.exists_isProper_finitePresentation_baseChange_of_isAffine`, which that theorem
was not strong enough to replace: the fibres of the model over the points of `T` outside the image
of `q` are seen by no hypothesis on `X`.

The properness of `X` is passed to the generic theorem as an explicit instance argument, for the
reason recorded at
`AlgebraicGeometry.exists_isProper_finitePresentation_baseChange_of_isAffine`: as an instance
*binder* it is not found at the spelling `(affineStageCone S).pt`, although that is `S` by
`rfl`. -/
theorem exists_isProper_finitePresentation_relativeDimensionLE_baseChange_of_isAffine
    (S : Scheme.{u}) [IsAffine S] (X : Over S) [IsProper X.hom]
    (hX : FinitePresentation X.hom) (d : ℕ)
    (hdim : ∀ s : S, topologicalKrullDim (X.hom.fiber s) ≤ (d : WithBot ℕ∞)) :
    ∃ (T : Scheme.{u}) (q : S ⟶ T) (XT : Over T),
      IsAffine T ∧ IsNoetherian T ∧ LocallyOfFiniteType (terminal.from T) ∧
        FinitePresentation XT.hom ∧ IsProper XT.hom ∧
        (∀ t : T, topologicalKrullDim (XT.hom.fiber t) ≤ (d : WithBot ℕ∞)) ∧
        Nonempty (X ≅ (Over.pullback q).obj XT) := by
  obtain ⟨j, XT, hfp, hprop, hdimj, hiso⟩ :=
    @exists_isProper_finitePresentation_relativeDimensionLE_model_of_isLimit _ _ _
      (specAdjoinFinsetDiagram Γ(S, ⊤)) _ _ _
      (affineStageCone S) (isLimit_affineStageCone S) X ‹IsProper X.hom› hX d hdim
  exact ⟨(specAdjoinFinsetDiagram Γ(S, ⊤)).obj j, (affineStageCone S).π.app j, XT,
    isAffine_specAdjoinFinsetDiagram_obj _ j, isNoetherian_specAdjoinFinsetDiagram_obj _ j,
    locallyOfFiniteType_terminalFrom_specAdjoinFinsetDiagram_obj _ j, hfp, hprop, hdimj, hiso⟩

end

end AlgebraicGeometry

end
