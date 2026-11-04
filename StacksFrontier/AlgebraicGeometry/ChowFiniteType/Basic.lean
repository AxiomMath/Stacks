module

public import StacksFrontier.AlgebraicGeometry.FiniteTypeLimitFinitePresentation.Basic
public import StacksFrontier.AlgebraicGeometry.ProperLimitStage.SeparatedModel
public import StacksFrontier.AlgebraicGeometry.ProperLimitStage.NoetherianChow
public import StacksFrontier.AlgebraicGeometry.Segre.ChartSurjective

/-!
# Chow's lemma over a quasi-compact quasi-separated base

[Stacks, Tag 0202] is Chow's lemma for a separated morphism of finite type `f : X ⟶ S` with `S`
quasi-compact and quasi-separated: there are an `n`, a scheme `X'`, a proper surjective
`π : X' ⟶ X` and an immersion `X' ⟶ ℙⁿ_S` over `S`. Its proof has two halves, and both are
assembled here.

**The first half is a reduction to the case of a morphism of finite presentation.** Proposition
01ZJ factors `f` as a closed immersion into a separated morphism of finite presentation, and
Chow's lemma descends along a closed immersion by pulling the modification back
(`AlgebraicGeometry.HasChowModification.of_isClosedImmersion`).

**The second half is absolute Noetherian approximation.** Writing `S` as the limit of an inverse
system of Noetherian schemes with affine transition morphisms ([Stacks, Tag 01ZA]), part (1) of
[Stacks, Tag 01ZM] presents a morphism of finite presentation over `S` as the base change of one
over a stage, [Stacks, Tag 01ZQ] makes that model separated over a later stage, and Chow's lemma
over a Noetherian base ([Stacks, Tag 0200], formalized as
`AlgebraicGeometry.hasChowModification`) applies there. The modification is transported back by
`AlgebraicGeometry.HasChowModification.of_isPullback`.

Both halves are conditional on the single-affine step of Noetherian approximation,
`AlgebraicGeometry.Scheme.FiniteTypeApproximation.IsOneAffineOpenStep` — the first through
Proposition 01ZJ, the second through Tag 01ZA. Nothing else is assumed.

## Main results

* `AlgebraicGeometry.exists_isSeparated_finitePresentation_model_of_isLimit`: a separated
  morphism of finite presentation over a cofiltered limit of Noetherian schemes is the base
  change of a separated morphism of finite presentation over a stage, isomorphism included.
* `AlgebraicGeometry.hasChowModification_of_isLimit_of_isNoetherian`: Chow's lemma for a
  separated morphism of finite presentation over such a limit, unconditionally.
* `AlgebraicGeometry.hasChowModification_of_finitePresentation_of_isOneAffineOpenStep`: Chow's
  lemma for a separated morphism of **finite presentation** onto a quasi-compact quasi-separated
  base.
* `AlgebraicGeometry.hasChowModification_of_isOneAffineOpenStep`: the conclusion of
  **[Stacks, Tag 0202]**.
* `AlgebraicGeometry.exists_isProper_baseChange_of_isLimit_of_isOneAffineOpenStep`:
  [Stacks, Tag 081F] with the Noetherian hypothesis on the stage base removed.

## Implementation notes

**No `@[stacks 0202]` attribute is attached.** Every statement below carries
`AlgebraicGeometry.Scheme.FiniteTypeApproximation.IsOneAffineOpenStep`, a hypothesis the tag does
not have; withholding is the same decision made for Tags 01ZE, 01ZG, 09ZQ and 01ZJ in
`StacksFrontier/AlgebraicGeometry/FiniteTypeClosedInFinitePresentation/Glueing.lean` and
`StacksFrontier/AlgebraicGeometry/FiniteTypeLimitFinitePresentation/Basic.lean`. With that step
proved, `AlgebraicGeometry.hasChowModification_of_isOneAffineOpenStep` is the tag with its
hypothesis deleted and nothing else changed.

`AlgebraicGeometry.exists_isSeparated_finitePresentation_model_of_isLimit` is the first two steps
of `AlgebraicGeometry.exists_isProper_finitePresentation_model_of_isLimit`
(`StacksFrontier/AlgebraicGeometry/ProperLimitStage/SeparatedModel.lean`), which writes them out
inline before applying Tag 081F; that theorem could be refactored through this one. The
`[∀ i, QuasiSeparatedSpace (D.obj i)]` binder that theorem
carries beside `[∀ i, IsNoetherian (D.obj i)]` is **redundant** — a Noetherian scheme is a
Noetherian space and hence quasi-separated, and `infer_instance` finds it — so the statement
below omits it.

An isomorphism in a category over `S` has an isomorphism as its left component, and that is
supplied by hand: `CategoryTheory.Over.forget` does carry it, but the instance is not found at the
spelling `(e.hom).left`. The closed-immersion instance for an isomorphism is then found by
search, which is what lets Chow's lemma cross the isomorphism that part (1) of Tag 01ZM returns
with no further bridge.

## References

* [Stacks Project, Tag 0202](https://stacks.math.columbia.edu/tag/0202)
* [Stacks Project, Tag 0200](https://stacks.math.columbia.edu/tag/0200)
* [Stacks Project, Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
* [Stacks Project, Tag 01ZJ](https://stacks.math.columbia.edu/tag/01ZJ)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 01ZQ](https://stacks.math.columbia.edu/tag/01ZQ)
* [Stacks Project, Tag 081F](https://stacks.math.columbia.edu/tag/081F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry

add_to_stacks 05LZ "the displayed diagram, as the predicate HasChowModification"
  AlgebraicGeometry.HasChowModification

/-- The left component of an isomorphism of a category over `S` is an isomorphism. -/
theorem isIso_left_of_overIso {S : Scheme.{u}} {A B : Over S} (e : A ≅ B) : IsIso e.hom.left :=
  ⟨e.inv.left, by rw [← Over.comp_left, e.hom_inv_id, Over.id_left],
    by rw [← Over.comp_left, e.inv_hom_id, Over.id_left]⟩

/-- **A separated morphism of finite presentation over a cofiltered limit of Noetherian schemes
is the base change of a separated morphism of finite presentation over a stage.** Let `D` be a
cofiltered inverse system of Noetherian schemes with affine transition morphisms, `c` a limit
cone, and let `X` be separated and of finite presentation over `c.pt`. Then there are a stage `j`
and an `Xⱼ` over `D.obj j`, separated and of finite presentation over it, together with an
isomorphism `X ≅ (Over.pullback (c.π.app j)).obj Xⱼ` over `c.pt`.

Part (1) of [Stacks, Tag 01ZM] produces the model of finite presentation and
[Stacks, Tag 01ZQ], in the form `AlgebraicGeometry.exists_isSeparated_overPullback_of_isLimit`,
makes it separated over a later stage; the base change along the transition keeps finite
presentation and keeps the isomorphism with `X`. -/
theorem exists_isSeparated_finitePresentation_model_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [∀ i : I, IsNoetherian (D.obj i)]
    (c : Cone D) (hc : IsLimit c)
    (X : Over c.pt) [IsSeparated X.hom] (hX : FinitePresentation X.hom) :
    ∃ (j : I) (Xⱼ : Over (D.obj j)), FinitePresentation Xⱼ.hom ∧ IsSeparated Xⱼ.hom ∧
      Nonempty (X ≅ (Over.pullback (c.π.app j)).obj Xⱼ) := by
  obtain ⟨i, Xᵢ, hXᵢ, ⟨e⟩⟩ :=
    LimitDescent.exists_model_of_finitePresentation_of_essentiallySmall D c hc X hX
  have hlfp : LocallyOfFinitePresentation Xᵢ.hom := hXᵢ.1
  have hqc : QuasiCompact Xᵢ.hom := hXᵢ.2.1
  have hqs : QuasiSeparated Xᵢ.hom := hXᵢ.2.2
  have hcs : CompactSpace Xᵢ.left := QuasiCompact.compactSpace_of_compactSpace Xᵢ.hom
  have hqss : QuasiSeparatedSpace Xᵢ.left := quasiSeparatedSpace_of_quasiSeparated Xᵢ.hom
  have hsep₀ : IsSeparated ((Over.pullback (c.π.app i)).obj Xᵢ).hom :=
    prop_of_overIso (@IsSeparated) e ‹IsSeparated X.hom›
  obtain ⟨j₁, a, hsep₁⟩ := exists_isSeparated_overPullback_of_isLimit D c hc i Xᵢ
  exact ⟨j₁, (Over.pullback (D.map a)).obj Xᵢ,
    finitePresentation_overPullbackObj _ Xᵢ hXᵢ, hsep₁,
    ⟨e ≪≫ overPullbackObj_shiftIso D c a Xᵢ⟩⟩

/-- **Chow's lemma for a separated morphism of finite presentation over a cofiltered limit of
Noetherian schemes with affine transition morphisms.** This is the second half of the Stacks
proof of [Stacks, Tag 0202]: descend the morphism to a separated model of finite presentation
over a Noetherian stage, apply Chow's lemma over a Noetherian base ([Stacks, Tag 0200]) there,
and base change the modification back. -/
theorem hasChowModification_of_isLimit_of_isNoetherian
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [∀ i : I, IsNoetherian (D.obj i)]
    (c : Cone D) (hc : IsLimit c)
    (X : Over c.pt) [IsSeparated X.hom] (hX : FinitePresentation X.hom) :
    HasChowModification X.hom := by
  obtain ⟨j, Xⱼ, hfp, hsep, ⟨e⟩⟩ :=
    exists_isSeparated_finitePresentation_model_of_isLimit D c hc X hX
  have := hfp.1
  have := hfp.2.1
  have hbase : HasChowModification ((Over.pullback (c.π.app j)).obj Xⱼ).hom :=
    HasChowModification.of_isPullback
      (IsPullback.of_hasPullback Xⱼ.hom (c.π.app j)) (hasChowModification Xⱼ.hom)
  have := isIso_left_of_overIso e
  have : IsClosedImmersion e.hom.left := inferInstance
  exact HasChowModification.of_isClosedImmersion (j := e.hom.left) (Over.w e.hom) hbase

variable {X S : Scheme.{u}}

/-- **Chow's lemma for a separated morphism of finite presentation onto a quasi-compact
quasi-separated base**, granted the single-affine step of Noetherian approximation.

Absolute Noetherian approximation ([Stacks, Tag 01ZA], available on that step as
`exists_limitNoetherianSituation_of_isOneAffineOpenStep` in the namespace
`AlgebraicGeometry.Scheme.FiniteTypeApproximation`)
writes `S` as a cofiltered limit of Noetherian schemes with affine transition morphisms, and
`AlgebraicGeometry.hasChowModification_of_isLimit_of_isNoetherian` applies to that system. -/
theorem hasChowModification_of_finitePresentation_of_isOneAffineOpenStep
    (hstep : Scheme.FiniteTypeApproximation.IsOneAffineOpenStep.{u}) (f : X ⟶ S)
    [IsSeparated f] (hf : FinitePresentation f)
    [CompactSpace S] [QuasiSeparatedSpace S] : HasChowModification f := by
  obtain ⟨J, _, _, _, D, hEq, _⟩ :=
    Scheme.FiniteTypeApproximation.exists_limitNoetherianSituation_of_isOneAffineOpenStep hstep S
  subst hEq
  have haff : ∀ {i j : Jᵒᵖ} (g : i ⟶ j), IsAffineHom (D.system.map g) :=
    D.transition_affine
  have hnoeth : ∀ i : Jᵒᵖ, IsNoetherian (D.system.obj i) := fun i => D.noetherian i.unop
  have hsepm : IsSeparated (Over.mk f).hom := ‹IsSeparated f›
  exact hasChowModification_of_isLimit_of_isNoetherian D.system D.limitCone D.isLimit
    (Over.mk f) hf

/-- **The conclusion of [Stacks, Tag 0202]**, granted the single-affine step of Noetherian
approximation: Chow's lemma for a separated morphism of finite type onto a quasi-compact
quasi-separated scheme.

Proposition 01ZJ, in the form
`AlgebraicGeometry.exists_isSeparated_finitePresentation_isClosedImmersion_of_isOneAffineOpenStep`,
factors `f` as a closed immersion into a separated morphism of finite presentation; Chow's lemma
holds for the latter by
`AlgebraicGeometry.hasChowModification_of_finitePresentation_of_isOneAffineOpenStep` and descends
along the closed immersion by `AlgebraicGeometry.HasChowModification.of_isClosedImmersion`. No
attribute is attached; see the implementation notes. -/
theorem hasChowModification_of_isOneAffineOpenStep
    (hstep : Scheme.FiniteTypeApproximation.IsOneAffineOpenStep.{u}) (f : X ⟶ S)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [CompactSpace S] [QuasiSeparatedSpace S] : HasChowModification f := by
  obtain ⟨X', p, ι, hp, hsep, hι, hfac⟩ :=
    exists_isSeparated_finitePresentation_isClosedImmersion_of_isOneAffineOpenStep hstep f
  exact HasChowModification.of_isClosedImmersion hfac
    (hasChowModification_of_finitePresentation_of_isOneAffineOpenStep hstep p hp)

/-- **[Stacks, Tag 081F] with the Noetherian hypothesis on the stage base removed**, granted the
single-affine step of Noetherian approximation and separatedness of `f₀`.

`AlgebraicGeometry.exists_isProper_baseChange_of_isLimit_of_hasChowModification` is Stacks 081F on
the hypothesis that Chow's lemma holds for `f₀`, and
`AlgebraicGeometry.exists_isProper_baseChange_of_isLimit_of_isNoetherian` discharges it by the
Noetherian case of Chow's lemma, [Stacks, Tag 0200], at the price of asking the stage base `Y₀` to
be Noetherian. `AlgebraicGeometry.hasChowModification_of_isOneAffineOpenStep` discharges it over
the merely quasi-compact quasi-separated `Y₀` that Situation 081D already provides, so that price
is not paid here. The composition needs no bridging lemma: the hypothesis slot is
`HasChowModification f₀.left` on the nose.

`@[stacks 081F]` is still **withheld**, for two reasons. The step is a hypothesis the tag does not
have. And `[IsSeparated f₀.left]` is one too: the Stacks proof obtains it by applying
[Stacks, Tag 01ZQ] to `f₀` and re-indexing the system at the stage it supplies, which is not done
here — the re-indexing has to move the conclusion back along a composite transition, and that
bookkeeping is left for whoever needs the tag's exact statement. -/
theorem exists_isProper_baseChange_of_isLimit_of_isOneAffineOpenStep
    (hstep : Scheme.FiniteTypeApproximation.IsOneAffineOpenStep.{u})
    {I : Type v} [Category.{v} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (X₀ Y₀ : Over (D.obj i₀)) (f₀ : X₀ ⟶ Y₀)
    [CompactSpace (D.obj i₀)] [QuasiSeparatedSpace (D.obj i₀)]
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    [LocallyOfFiniteType f₀.left] [IsSeparated f₀.left]
    [IsProper ((Over.pullback (c.π.app i₀)).map f₀).left] :
    ∃ (i : I) (hi : i ⟶ i₀), IsProper ((Over.pullback (D.map hi)).map f₀).left :=
  exists_isProper_baseChange_of_isLimit_of_hasChowModification D c hc i₀ X₀ Y₀ f₀
    (hasChowModification_of_isOneAffineOpenStep hstep f₀.left)

end AlgebraicGeometry

end
