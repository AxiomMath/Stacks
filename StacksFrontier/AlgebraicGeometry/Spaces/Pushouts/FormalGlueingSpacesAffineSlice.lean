module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesAffineFull

/-!
# Stacks 0AF4 reduced to one construction: affine glueing data in the slice over a space

In a formal glueing situation `(f : Y ⟶ X, Z, U = X \ Z, V = Y \ f⁻¹(Z))`, write `F` for the
restriction functor of Stacks 0AF3. This module reduces all three clauses of Stacks 0AF4 to a
single construction, `AlgebraicGeometry.Space.FormalGlueingSituation.AffineSliceRealization`:
a morphism of glueing data `ψ : G ⟶ F Qq` into the restriction of a space `Qq` over `X`, whose
two legs are affine, is the restriction of a morphism `T ⟶ Qq` of spaces over `X`, up to an
isomorphism `F T ≅ G` of glueing data.

* Taking `Qq = X` itself, whose restriction is terminal among glueing data, the construction is
  essential surjectivity of clause (1)
  (`AlgebraicGeometry.Space.FormalGlueingSituation.essSurj_affineGlueingFunctor_of_realization`):
  the legs of the unique `ψ : G ⟶ F X` are the legs of `G` up to isomorphism, and the space `T`
  produced is affine over `X` by the fpqc-local criterion of Stacks 041Z through the covering of
  Stacks 0AF1.
* A closed immersion is affine, so the construction contains the closed-immersion construction
  in the slice over a space which the graph argument of Stacks 0AF6 consumes, and with it
  fullness of clause (1)
  (`AlgebraicGeometry.Space.FormalGlueingSituation.full_affineGlueingFunctor_of_realization`).

## Main definitions

* `AlgebraicGeometry.Space.FormalGlueingSituation.AffineSliceRealization`.

## Main results

* `AlgebraicGeometry.Space.FormalGlueingSituation.closedSliceRealization_of_affine`.
* `AlgebraicGeometry.Space.FormalGlueingSituation.affineOverX_of_legs`: a space over `X` whose two
  restrictions are affine is affine over `X`.
* `AlgebraicGeometry.Space.FormalGlueingSituation.essSurj_affineGlueingFunctor_of_affineSlice`.
* `FormalGlueingSituation.isEquivalence_affineGlueingFunctor_of_affineSlice`,
  `…isEquivalence_closedGlueingFunctor_of_affineSlice` and
  `…isEquivalence_finiteGlueingFunctor_of_affineSlice`: the three clauses of Stacks 0AF4 from
  the construction.

## Implementation notes

These are reductions; Stacks 0AF4 is registered on
`AlgebraicGeometry.Space.FormalGlueingSituation.affineGlueingFunctor_isEquivalence`,
`closedGlueingFunctor_isEquivalence` and `finiteGlueingFunctor_isEquivalence`
(`StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesRestrictedEquivalences`).

## References

* [Stacks Project, Tag 0AF1](https://stacks.math.columbia.edu/tag/0AF1)
* [Stacks Project, Tag 0AF4](https://stacks.math.columbia.edu/tag/0AF4)
* [Stacks Project, Tag 0AF6](https://stacks.math.columbia.edu/tag/0AF6)
* [Stacks Project, Tag 041Z](https://stacks.math.columbia.edu/tag/041Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.FormalGlueingSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The construction of affine glueing data in the slice over a space `Qq` over `X`: a morphism
of glueing data `ψ : G ⟶ F Qq` whose two legs are affine is the restriction of a morphism
`k : T ⟶ Qq` of spaces over `X`, up to an isomorphism `F T ≅ G`. Clause (1) of Stacks 0AF4 for
the base change of the situation along `Qq ⟶ X`, read in the slice over `F Qq`. -/
def AffineSliceRealization (D : FormalGlueingSituation B S hS) : Prop :=
  ∀ (Qq : spacesOverX D) (G : glueingData D) (ψ : G ⟶ (formalGlueingFunctor D).1.obj Qq),
    IsAffineHom B S hS ψ.hom.left.left →
    IsAffineHom B S hS ψ.hom.right.left →
    ∃ (T : spacesOverX D) (k : T ⟶ Qq) (θ : (formalGlueingFunctor D).1.obj T ≅ G),
      θ.hom ≫ ψ = (formalGlueingFunctor D).1.map k

/-- The affine construction contains the closed-immersion construction, a closed immersion
being affine. -/
theorem closedSliceRealization_of_affine (D : FormalGlueingSituation B S hS)
    (h : AffineSliceRealization D) : ClosedSliceRealization D :=
  fun Qq G ψ hU hY ↦
    h Qq G ψ (isAffineHom_of_isClosedImmersion hU) (isAffineHom_of_isClosedImmersion hY)

/-- Being affine, as a property of morphisms of presheaves on the big fppf site of `S`. -/
abbrev isAffinePresheaf (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  fun _ _ f ↦ IsAffineHom B S hS f

/-- Affine morphisms of presheaves are stable under base change. -/
instance : (isAffinePresheaf B S hS).IsStableUnderBaseChange where
  of_isPullback sq hf := isAffineHom_of_isPullback sq hf

/-- A space over `X` whose two restrictions — the two legs of its glueing triple — are affine is
affine over `X`. This is `isAffineHom_iff_restrictions` read in the category `Over X`. -/
theorem affineOverX_of_legs (D : FormalGlueingSituation B S hS) (T : spacesOverX D)
    (hU : IsAffineHom B S hS (pullback.snd T.1.hom D.U.ι))
    (hY : IsAffineHom B S hS (pullback.snd T.1.hom D.f)) : affineOverX D T :=
  (isAffineHom_iff_restrictions D (X' := ⟨T.1.left, T.2⟩) ⟨T.1.hom⟩).2
    ⟨(property_pullback_snd_hom_iff (isAffinePresheaf B S hS) _ _).1 hU,
      (property_pullback_snd_hom_iff (isAffinePresheaf B S hS) _ _).1 hY⟩

/-- `X` over itself, as a space over `X`. Its glueing triple is terminal. -/
abbrev terminalOverX (D : FormalGlueingSituation B S hS) : spacesOverX D :=
  ⟨Over.mk (𝟙 D.X), D.algebraicSpace_X⟩

/-- A morphism of `Over W` into the restriction of `X` over itself along `g : W ⟶ X` is affine on
underlying morphisms as soon as the structure morphism of its source is: the structure morphism
of the target is invertible. -/
private theorem isAffineHom_left_of_terminal {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {X₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : W ⟶ X₀) (A : Over W)
    (t : A ⟶ (Over.pullback g).obj (Over.mk (𝟙 X₀))) (hA : IsAffineHom B S hS A.hom) :
    IsAffineHom B S hS t.left := by
  have hw : t.left ≫ pullback.snd (𝟙 X₀) g = A.hom := Over.w t
  have sq : IsPullback (𝟙 A.left) t.left A.hom (pullback.snd (𝟙 X₀) g) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, hw]⟩
  exact isAffineHom_of_isPullback sq hA

/-- **Essential surjectivity in clause (1) of Stacks 0AF4 from the slice construction.** The
glueing triple of `X` over itself is terminal, so every glueing triple `G` with affine legs has
a unique morphism to it, whose legs are affine; the construction produces a space `T` over `X`
with `F T ≅ G`, and `T` is affine over `X` because its restrictions are isomorphic to the legs
of `G`. -/
theorem essSurj_affineGlueingFunctor_of_affineSlice (D : FormalGlueingSituation B S hS)
    (h : AffineSliceRealization D) : (affineGlueingFunctor D).EssSurj := by
  refine ⟨fun G ↦ ?_⟩
  let tU : IsTerminal ((Over.pullback D.U.ι).obj (Over.mk (𝟙 D.X))) :=
    IsTerminal.isTerminalObj _ _ Over.mkIdTerminal
  let tY : IsTerminal ((Over.pullback D.f).obj (Over.mk (𝟙 D.X))) :=
    IsTerminal.isTerminalObj _ _ Over.mkIdTerminal
  let tV : IsTerminal ((Over.pullback D.V.ι).obj ((Over.pullback D.f).obj (Over.mk (𝟙 D.X)))) :=
    IsTerminal.isTerminalObj _ _ tY
  let c : G.obj.obj ⟶ ((formalGlueingFunctor D).1.obj (terminalOverX D)).obj :=
    { left := tU.from G.obj.obj.left
      right := tY.from G.obj.obj.right
      w := tV.hom_ext _ _ }
  let ψ : G.obj ⟶ (formalGlueingFunctor D).1.obj (terminalOverX D) := ObjectProperty.homMk c
  obtain ⟨T, -, θ, -⟩ := h (terminalOverX D) G.obj ψ
    (isAffineHom_left_of_terminal D.U.ι _ _ G.property.1)
    (isAffineHom_left_of_terminal D.f _ _ G.property.2.2)
  exact ⟨⟨T, affineOverX_of_legs D T
    (property_legLeft_of_iso (isAffinePresheaf B S hS) D θ G.property.1)
    (property_legRight_of_iso (isAffinePresheaf B S hS) D θ G.property.2.2)⟩,
    ⟨(ObjectProperty.fullyFaithfulι (affineLegs D)).preimageIso θ⟩⟩

/-- **Clause (1) of Stacks 0AF4 from the slice construction.** -/
theorem isEquivalence_affineGlueingFunctor_of_affineSlice (D : FormalGlueingSituation B S hS)
    (h : AffineSliceRealization D) : (affineGlueingFunctor D).IsEquivalence :=
  isEquivalence_affineGlueingFunctor_of_realization D
    (essSurj_affineGlueingFunctor_of_affineSlice D h) (closedSliceRealization_of_affine D h)

/-- **Clause (2) of Stacks 0AF4 from the slice construction.** -/
theorem isEquivalence_closedGlueingFunctor_of_affineSlice (D : FormalGlueingSituation B S hS)
    (h : AffineSliceRealization D) : (closedGlueingFunctor D).IsEquivalence :=
  isEquivalence_closedGlueingFunctor D (isEquivalence_affineGlueingFunctor_of_affineSlice D h)

/-- **Clause (3) of Stacks 0AF4 from the slice construction.** -/
theorem isEquivalence_finiteGlueingFunctor_of_affineSlice (D : FormalGlueingSituation B S hS)
    (h : AffineSliceRealization D) : (finiteGlueingFunctor D).IsEquivalence :=
  isEquivalence_finiteGlueingFunctor D (isEquivalence_affineGlueingFunctor_of_affineSlice D h)

end AlgebraicGeometry.Space.FormalGlueingSituation

end
