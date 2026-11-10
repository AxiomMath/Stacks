module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.RepresentableByAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCover

/-!
# Criteria for a morphism of algebraic spaces to be quasi-separated

Quasi-separatedness of a morphism of algebraic spaces over a scheme `S` is stable under base
change, and may therefore be tested on all scheme base changes, on affine scheme base changes,
or on a surjective étale scheme atlas of the target. These are the implications of Stacks 03KM,
part (3), that start from quasi-separatedness of the morphism itself.

## Main results

* `AlgebraicGeometry.Space.quasiCompactMorphisms` reifies
  `AlgebraicGeometry.Space.IsQuasiCompact` as a `CategoryTheory.MorphismProperty` of the
  presheaf category, so that quasi-separatedness becomes its
  `CategoryTheory.MorphismProperty.diagonal`. It is the presheaf-category reification;
  `AlgebraicGeometry.Space.quasiCompactProperty` is the reification of the same predicate as a
  `CategoryTheory.MorphismProperty (AlgebraicSpaces B S hS)`, on the category of algebraic
  spaces rather than of presheaves, and the two are properties of different categories.
* `AlgebraicGeometry.Space.isQuasiSeparated_of_isPullback` and
  `AlgebraicGeometry.Space.isQuasiSeparated_pullback_snd`: quasi-separatedness of a morphism
  is stable under base change along an arbitrary morphism of presheaves.
* `AlgebraicGeometry.Space.forall_isQuasiSeparated_pullback_snd`,
  `AlgebraicGeometry.Space.forall_isAffine_isQuasiSeparated_pullback_snd`,
  `AlgebraicGeometry.Space.exists_surjective_etale_isQuasiSeparated_pullback_snd` and
  `AlgebraicGeometry.Space.exists_isZariskiCover_isQuasiSeparated_pullback_snd` are the
  implications (1) ⇒ (2), (2) ⇒ (3), (2) ⇒ (5) and (1) ⇒ (6) of Stacks 03KM, part (3).
* `AlgebraicGeometry.Space.isOpenImmersion_of_isIso`: an isomorphism of presheaves is an open
  immersion. That an algebraic space is an open subspace of itself and that the resulting
  one-member family is a Zariski covering are
  `AlgebraicGeometry.Space.isOpenSubspace_top` and
  `AlgebraicGeometry.Space.isZariskiCover_top`, in
  `StacksFrontier/AlgebraicGeometry/Spaces/Immersions.lean`.

## Implementation notes

`AlgebraicGeometry.Space.IsQuasiCompact` is not a `CategoryTheory.MorphismProperty` of the
presheaf category on the nose but the assertion that every base change along a morphism from a
quasi-compact algebraic space has quasi-compact source, so neither
`CategoryTheory.MorphismProperty.presheaf` nor the descent lemmas written for it apply to it.
Reifying it as `AlgebraicGeometry.Space.quasiCompactMorphisms` costs nothing — the predicate is
literally the same proposition, as `AlgebraicGeometry.Space.quasiCompactMorphisms_iff` records
by `Iff.rfl` — and buys the whole `CategoryTheory.MorphismProperty` API. In particular
`AlgebraicGeometry.Space.IsQuasiSeparated` is its
`CategoryTheory.MorphismProperty.diagonal` by definitional unfolding
(`AlgebraicGeometry.Space.diagonal_quasiCompactMorphisms_iff`), so base-change stability of
quasi-separatedness is Mathlib's
`CategoryTheory.MorphismProperty.IsStableUnderBaseChange.diagonal` applied to Stacks 03HF,
which is `AlgebraicGeometry.Space.isQuasiCompact_of_isPullback`. Mathlib proves that instance
through `CategoryTheory.Limits.diagonal_pullback_fst`, which identifies the diagonal of a
first projection with a base change of the diagonal, so no cartesian square has to be built by
hand here.

The four implications below are stated with the clauses of the source written out, so that each
is an implication between two of the six conditions of Stacks 03KM rather than a statement
about an auxiliary predicate. The base-change lemma does not use representability of the test
object, which is what makes the criterion on a Zariski covering available as well: the members
of a covering are subfunctors, not representables, and the covering exhibited is the improper
one consisting of the target alone. What is missing for the full equivalence is every
implication back to (1) — that is fppf descent of quasi-compactness along the atlas, for a
predicate that is not a `CategoryTheory.MorphismProperty.presheaf`, so the descent lemmas
proved for those do not reach it — and the comparison (3) ⇔ (4) with the absolute
quasi-separatedness of Stacks 03BS, which runs through
`CategoryTheory.OverShriek.relocalizePresheafFunctor`.

## References

* [Stacks Project, Tag 03KM](https://stacks.math.columbia.edu/tag/03KM)
* [Stacks Project, Tag 03HF](https://stacks.math.columbia.edu/tag/03HF)
* [Stacks Project, Tag 03HL](https://stacks.math.columbia.edu/tag/03HL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Quasi-compactness of a morphism as a morphism property -/

/-- Quasi-compactness of a morphism of algebraic spaces over `S`, reified as a morphism
property of the presheaf category. -/
def quasiCompactMorphisms : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  fun _ _ f => IsQuasiCompact B S hS f

variable {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The reification of quasi-compactness is quasi-compactness. -/
theorem quasiCompactMorphisms_iff (f : F ⟶ G) :
    quasiCompactMorphisms B S hS f ↔ IsQuasiCompact B S hS f :=
  Iff.rfl

/-- **Stacks 03HF**, as base-change stability of
`AlgebraicGeometry.Space.quasiCompactMorphisms`. -/
instance quasiCompactMorphisms_isStableUnderBaseChange :
    (quasiCompactMorphisms B S hS).IsStableUnderBaseChange where
  of_isPullback sq hg := isQuasiCompact_of_isPullback B S hS sq hg

/-- **Stacks 03HL, part (3)**, as the diagonal of
`AlgebraicGeometry.Space.quasiCompactMorphisms`: a morphism is quasi-separated exactly when its
relative diagonal is quasi-compact. -/
theorem diagonal_quasiCompactMorphisms_iff (f : F ⟶ G) :
    (quasiCompactMorphisms B S hS).diagonal f ↔ IsQuasiSeparated B S hS f :=
  Iff.rfl

/-! ### Base change of quasi-separatedness -/

/-- Quasi-separatedness of a morphism of algebraic spaces over `S` is stable under base
change. -/
theorem isQuasiSeparated_of_isPullback {P A C : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {fst : P ⟶ A} {snd : P ⟶ F} {a : A ⟶ C} {b : F ⟶ C}
    (sq : IsPullback fst snd a b) (ha : IsQuasiSeparated B S hS a) :
    IsQuasiSeparated B S hS snd :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := (quasiCompactMorphisms B S hS).diagonal) sq ha

/-- The base change of a quasi-separated morphism of algebraic spaces over `S` along an
arbitrary morphism of presheaves is quasi-separated. -/
theorem isQuasiSeparated_pullback_snd {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (g : Z ⟶ G) (hf : IsQuasiSeparated B S hS f) :
    IsQuasiSeparated B S hS (pullback.snd f g) :=
  isQuasiSeparated_of_isPullback B S hS (IsPullback.of_hasPullback f g) hf

/-! ### The criteria of Stacks 03KM for quasi-separatedness -/

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 03KM, part (3), (1) ⇒ (2).** A quasi-separated morphism of algebraic spaces over
`S` has quasi-separated base change along every morphism from a representable presheaf. -/
theorem forall_isQuasiSeparated_pullback_snd (f : X ⟶ Y) (hf : IsQuasiSeparated B S hS f) :
    ∀ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y),
      IsQuasiSeparated B S hS (pullback.snd f g) :=
  fun _ g ↦ isQuasiSeparated_pullback_snd B S hS f g hf

/-- **Stacks 03KM, part (3), (2) ⇒ (3).** Testing quasi-separatedness of the base changes on
all representable presheaves implies testing it on the affine ones. -/
theorem forall_isAffine_isQuasiSeparated_pullback_snd (f : X ⟶ Y)
    (hf : ∀ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y),
      IsQuasiSeparated B S hS (pullback.snd f g)) :
    ∀ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y),
      IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
        IsQuasiSeparated B S hS (pullback.snd f g) :=
  fun T g _ ↦ hf T g

/-- **Stacks 03KM, part (3), (2) ⇒ (5).** Testing quasi-separatedness of the base changes on
all representable presheaves implies testing it on a surjective étale scheme atlas of the
target, which exists because the target is an algebraic space. -/
theorem exists_surjective_etale_isQuasiSeparated_pullback_snd (f : X ⟶ Y)
    (hY : IsAlgebraicSpace B S hS Y)
    (hf : ∀ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y),
      IsQuasiSeparated B S hS (pullback.snd f g)) :
    ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) g ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) g ∧
      IsQuasiSeparated B S hS (pullback.snd f g) := by
  obtain ⟨V, g, hsurj, hetale⟩ := hY.exists_atlas
  exact ⟨V, g, hsurj, hetale, hf V g⟩

/-! ### The improper Zariski covering -/

/-- An isomorphism of presheaves on the big fppf site of `S` is an open immersion of algebraic
spaces: each of its represented base changes is an isomorphism of representables, chosen here
to be an identity. -/
theorem isOpenImmersion_of_isIso (f : F ⟶ G) [IsIso f] : IsOpenImmersion B S hS f := by
  refine MorphismProperty.relative.of_exists (fun a g ↦ ⟨a, g ≫ inv f, 𝟙 a, ?_, ?_⟩)
  · exact IsPullback.of_vert_isIso ⟨by simp⟩
  · change AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (𝟙 a))
    rw [CategoryTheory.Functor.map_id]
    infer_instance



/-- **Stacks 03KM, part (3), (1) ⇒ (6).** A quasi-separated morphism of algebraic spaces over
`S` has quasi-separated base change along the members of some Zariski covering of its target,
witnessed by the improper covering of the target by itself. -/
theorem exists_isZariskiCover_isQuasiSeparated_pullback_snd (f : X ⟶ Y)
    (hY : IsAlgebraicSpace B S hS Y) (hf : IsQuasiSeparated B S hS f) :
    ∃ (I : Type u) (U : I → Subfunctor Y),
      IsZariskiCover B S hS I U ∧
        ∀ i, IsQuasiSeparated B S hS (pullback.snd f (U i).ι) :=
  ⟨PUnit.{u + 1}, fun _ ↦ ⊤, isZariskiCover_top hY,
    fun _ ↦ isQuasiSeparated_pullback_snd B S hS f _ hf⟩

end AlgebraicGeometry.Space

end
