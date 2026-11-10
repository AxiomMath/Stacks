module

public import StacksFrontier.AlgebraicGeometry.Limits.ChowLemma
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Diagonal
public import StacksFrontier.AlgebraicGeometry.Segre.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Descending properness to a finite stage

Let `S = lim S_i` be the limit of a cofiltered inverse system of schemes with affine transition
morphisms, let `f₀ : X₀ ⟶ Y₀` be a morphism of schemes over a stage `S₀`, and write `f_i` and
`f` for its base changes to `S_i` and to `S`. **Stacks 081F** says that if `f` is proper and `f₀`
is locally of finite type, then `f_i` is proper for some `i`.

The Stacks proof is a descent along Chow's lemma. Choose a proper surjective modification
`π : X₀' ⟶ X₀` with `X₀' ⟶ ℙⁿ_{Y₀}` an immersion (Stacks 0202). After base change to the limit,
`X' ⟶ Y` is proper, so `X' ⟶ ℙⁿ_Y` is a proper monomorphism and therefore a closed immersion;
closed immersions descend to a finite stage (Stacks 01ZP), so `X'_i ⟶ ℙⁿ_{Y_i}` is a closed
immersion for some `i`, whence `X'_i ⟶ Y_i` is proper. Since `X'_i ⟶ X_i` is surjective, `X_i`
is universally closed over `Y_i` (Stacks 03GN); separatedness comes from Stacks 01ZQ and local
finite type is stable under base change, so `f_i` is proper.

Chow's lemma over a quasi-compact quasi-separated base, Stacks 0202, is not available in this
repository, so it enters as the hypothesis `AlgebraicGeometry.HasChowModification`, which is
verbatim its conclusion.

## Main results

* `AlgebraicGeometry.isProper_of_comp_surjective`: the properness conclusion of Stacks 03GN —
  a scheme that is separated and locally of finite type over a base, and receives a surjection
  from a scheme universally closed over that base, is proper over it.
* `AlgebraicGeometry.exists_isProper_baseChange_of_isLimit_of_hasChowModification`: Stacks 081F,
  on the hypothesis that Chow's lemma holds for the given morphism.

## Implementation notes

The inverse system is a cofiltered category rather than a directed partially ordered set, and
"some `i ≥ 0`" is an object `i` together with a morphism `i ⟶ i₀`, as in
`AlgebraicGeometry.exists_isClosedImmersion_baseChange_of_isLimit` and
`AlgebraicGeometry.exists_isSeparated_baseChange_of_isLimit`. The index category's morphisms
live in the same universe as its objects because that is the shape in which the latter — the
Stacks 01ZQ input — is stated.

Projective space over `Y₀` and the Chow modification of `X₀` are both regarded as schemes over
`S₀` by composing with the structure morphism of `Y₀`, so that the two descent inputs apply
unchanged; the triangle over `Y₀` which the Chow modification satisfies is recorded as the
identity `u ≫ pr = ρ ≫ f₀` of morphisms over `S₀`, and base change carries it to every stage.

The two stages supplied by Stacks 01ZP and Stacks 01ZQ are merged by taking their meet in the
over category of `S₀`, which makes the two transition morphisms to `S₀` equal by construction.

No `@[stacks 081F]` attribute is attached: `hchow` is a hypothesis that Stacks 081F does not
carry, since there it is discharged by Chow's lemma over the quasi-compact quasi-separated base
`Y₀`.

**`hchow` is dischargeable over a Noetherian base.** Stacks 0200,
Chow's lemma over a Noetherian base, is `AlgebraicGeometry.hasDenseChowModification`
(`StacksFrontier/AlgebraicGeometry/Segre/ChartSurjective.lean:461`, with `@[stacks 0200]` at
`:460`), and `AlgebraicGeometry.hasChowModification` (`:466`) is its `HasChowModification` form,
unconditional for a separated quasi-compact morphism locally of finite type onto a Noetherian
scheme. The resulting form of Stacks 081F is
`AlgebraicGeometry.exists_isProper_baseChange_of_isLimit_of_isNoetherian`
(`StacksFrontier/AlgebraicGeometry/ProperLimitStage/NoetherianChow.lean:76`). What is still
missing is Stacks 0202, the quasi-compact quasi-separated case, whose residue is Stacks 01ZJ.

## References

* [Stacks Project, Tag 081F](https://stacks.math.columbia.edu/tag/081F)
* [Stacks Project, Tag 03GN](https://stacks.math.columbia.edu/tag/03GN)
* [Stacks Project, Tag 0202](https://stacks.math.columbia.edu/tag/0202)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe v u

/-- **Stacks 03GN, the properness conclusion.** If `f : X ⟶ Y` is surjective, `X` is universally
closed over `S` and `Y` is separated and locally of finite type over `S`, then `Y` is proper over
`S`.

The universal closedness of `g` is the first conclusion of Stacks 03GN, which is Mathlib's
`AlgebraicGeometry.UniversallyClosed.of_comp_surjective` — tagged just below — and properness
adds nothing beyond the two remaining hypotheses, quasi-compactness of `g` being implied by
universal closedness. The tag is therefore recorded against that Mathlib declaration and no
attribute is attached here; `AlgebraicGeometry.IsProper` is a Mathlib class with exactly these
three fields, so the proof is the Mathlib lemma followed by the structure constructor. -/
lemma isProper_of_comp_surjective {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [UniversallyClosed (f ≫ g)] [Surjective f] [IsSeparated g] [LocallyOfFiniteType g] :
    IsProper g :=
  have := UniversallyClosed.of_comp_surjective f g
  ⟨⟩

add_to_stacks 03GN "the universal closedness conclusion"
  AlgebraicGeometry.UniversallyClosed.of_comp_surjective
add_to_sga "3 V 7.4" "partial" AlgebraicGeometry.UniversallyClosed.of_comp_surjective
add_to_ega "II 5.4.9" "more general" AlgebraicGeometry.UniversallyClosed.of_comp_surjective
add_to_ega "IV 2.4.3" "(v), universally closed"
  AlgebraicGeometry.UniversallyClosed.of_comp_surjective

/-- **Stacks 081F, on the hypothesis of Chow's lemma.** Let `D` be a cofiltered inverse system of
schemes with affine transition morphisms and limit cone `c`, let `f₀ : X₀ ⟶ Y₀` be a morphism of
schemes over the stage `D.obj i₀` with all three of `D.obj i₀`, `X₀` and `Y₀` quasi-compact and
quasi-separated, and assume `f₀` is locally of finite type and becomes proper after base change
to the limit. If Chow's lemma holds for `f₀` then `f₀` is proper after base change to some later
stage.

The hypothesis `hchow` is the conclusion of Chow's lemma (Stacks 0202) for `f₀`, which that
lemma supplies from separatedness and finite type of `f₀` over the quasi-compact and
quasi-separated `Y₀`; separatedness at the limit is part of the properness assumed here, so the
hypothesis is exactly the content of Stacks 0202 that this repository cannot yet produce. -/
theorem exists_isProper_baseChange_of_isLimit_of_hasChowModification
    {I : Type v} [Category.{v} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (X₀ Y₀ : Over (D.obj i₀)) (f₀ : X₀ ⟶ Y₀)
    [CompactSpace (D.obj i₀)] [QuasiSeparatedSpace (D.obj i₀)]
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    [LocallyOfFiniteType f₀.left]
    [IsProper ((Over.pullback (c.π.app i₀)).map f₀).left]
    (hchow : HasChowModification f₀.left) :
    ∃ (i : I) (hi : i ⟶ i₀), IsProper ((Over.pullback (D.map hi)).map f₀).left := by
  classical
  obtain ⟨n, X', π, jimm, hproper, hsurj, himm, hcomm⟩ := hchow
  -- Projective space over `Y₀` and the modification `X'`, as schemes over `D.obj i₀`.
  set P : Over (D.obj i₀) := Over.mk ((ProjectiveSpace n Y₀.left ↘ Y₀.left) ≫ Y₀.hom) with hP
  set Xp : Over (D.obj i₀) := Over.mk (π ≫ X₀.hom) with hXp
  set pr : P ⟶ Y₀ := Over.homMk (ProjectiveSpace n Y₀.left ↘ Y₀.left) rfl with hpr
  set ρ : Xp ⟶ X₀ := Over.homMk π rfl with hρ
  have hu : jimm ≫ P.hom = Xp.hom := by
    change jimm ≫ (ProjectiveSpace n Y₀.left ↘ Y₀.left) ≫ Y₀.hom = π ≫ X₀.hom
    rw [← Category.assoc, ← hcomm, Category.assoc, Over.w f₀]
  set u : Xp ⟶ P := Over.homMk jimm hu with hu'
  -- The Chow triangle, as an identity of morphisms over `D.obj i₀`.
  have hupr : u ≫ pr = ρ ≫ f₀ := by
    ext
    change jimm ≫ (ProjectiveSpace n Y₀.left ↘ Y₀.left) = π ≫ f₀.left
    exact hcomm.symm
  have : CompactSpace Xp.left := QuasiCompact.compactSpace_of_compactSpace π
  have : QuasiSeparatedSpace Xp.left := (quasiSeparated_iff_quasiSeparatedSpace π).mp inferInstance
  have : CompactSpace P.left := inferInstanceAs (CompactSpace (ProjectiveSpace n Y₀.left))
  have : QuasiSeparatedSpace P.left :=
    (quasiSeparated_iff_quasiSeparatedSpace (ProjectiveSpace n Y₀.left ↘ Y₀.left)).mp inferInstance
  have hlft : LocallyOfFiniteType u.left := inferInstanceAs (LocallyOfFiniteType jimm)
  -- Base change preserves the Chow triangle.
  have hcompose : ∀ {T : Scheme.{u}} (q : T ⟶ D.obj i₀),
      ((Over.pullback q).map u).left ≫ ((Over.pullback q).map pr).left
        = ((Over.pullback q).map ρ).left ≫ ((Over.pullback q).map f₀).left := by
    intro T q
    rw [← Over.comp_left, ← Over.comp_left, ← Functor.map_comp, ← Functor.map_comp, hupr]
  have hprop : ∀ {T : Scheme.{u}} (q : T ⟶ D.obj i₀), IsProper ((Over.pullback q).map pr).left :=
    fun q => MorphismProperty.overPullbackMap (P := @IsProper) q pr
      (inferInstanceAs (IsProper (ProjectiveSpace n Y₀.left ↘ Y₀.left)))
  -- Over the limit, `X' ⟶ ℙⁿ_Y` is a proper monomorphism, hence a closed immersion.
  have hciLimit : IsClosedImmersion ((Over.pullback (c.π.app i₀)).map u).left := by
    have h1 : IsImmersion ((Over.pullback (c.π.app i₀)).map u).left :=
      MorphismProperty.overPullbackMap (P := @IsImmersion) (c.π.app i₀) u himm
    have h2 : IsProper ((Over.pullback (c.π.app i₀)).map ρ).left :=
      MorphismProperty.overPullbackMap (P := @IsProper) (c.π.app i₀) ρ hproper
    have := hprop (c.π.app i₀)
    have h3 : IsProper (((Over.pullback (c.π.app i₀)).map u).left ≫
        ((Over.pullback (c.π.app i₀)).map pr).left) := by
      rw [hcompose]; infer_instance
    exact isClosedImmersion_of_mono_of_isProper_of_comp _
      ((Over.pullback (c.π.app i₀)).map pr).left _ rfl
  -- Stacks 01ZP for the closed immersion, Stacks 01ZQ for separatedness.
  obtain ⟨i₂, h₂, hci₂⟩ :=
    exists_isClosedImmersion_baseChange_of_isLimit D c hc i₀ Xp P u
  obtain ⟨i₁, h₁, hsep₁⟩ :=
    exists_isSeparated_baseChange_of_isLimit D c i₀ X₀ Y₀ f₀ hc
  -- Merge the two stages: a base-change-stable property passes from `b` to any `a ⟶ b`.
  have hmove : ∀ (R : MorphismProperty Scheme.{u}) [R.IsStableUnderBaseChange]
      {X Y : Over (D.obj i₀)} (f : X ⟶ Y) {a b : Over i₀} (g : a ⟶ b),
      R ((Over.pullback (D.map b.hom)).map f).left →
        R ((Over.pullback (D.map a.hom)).map f).left :=
    @fun R _ _ _ f a b g h => by
      have hc := overPullback_map_comp R (D.map b.hom) (D.map g.left) f h
      rwa [← D.map_comp, Over.w g] at hc
  set C : Over i₀ := IsCofiltered.min (Over.mk h₁) (Over.mk h₂)
  have := hmove _ f₀ (IsCofiltered.minToLeft (Over.mk h₁) (Over.mk h₂)) hsep₁
  have := hmove _ u (IsCofiltered.minToRight (Over.mk h₁) (Over.mk h₂)) hci₂
  refine ⟨C.left, C.hom, ?_⟩
  have := hprop (D.map C.hom)
  have : IsProper (((Over.pullback (D.map C.hom)).map ρ).left ≫
      ((Over.pullback (D.map C.hom)).map f₀).left) := by
    rw [← hcompose]
    infer_instance
  have : Surjective _ :=
    MorphismProperty.overPullbackMap (P := @Surjective) (D.map C.hom) ρ hsurj
  have : LocallyOfFiniteType _ :=
    MorphismProperty.overPullbackMap (P := @LocallyOfFiniteType) (D.map C.hom) f₀ inferInstance
  exact isProper_of_comp_surjective ((Over.pullback (D.map C.hom)).map ρ).left
    ((Over.pullback (D.map C.hom)).map f₀).left

end AlgebraicGeometry

end
