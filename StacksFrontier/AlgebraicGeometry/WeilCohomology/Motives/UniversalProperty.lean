module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Motives.MonoidalStructure
public import StacksFrontier.CategoryTheory.Idempotents.KaroubiMonoidalExtension
public import StacksFrontier.CategoryTheory.Monoidal.BraidedEquivalenceInverse
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleObject
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Extending a functor on correspondences to the Karoubi envelope

For a correspondence structure `S`, a symmetric monoidal functor `F : S.Obj ⥤ 𝒞` into a Karoubian
symmetric monoidal category extends to a symmetric monoidal functor on the Karoubi envelope
`S.Motive = Karoubi S.Obj`, and the extension is unique up to a unique isomorphism. This is the
universal property of the Karoubi envelope, the first step of the proof of Stacks 0FGH.

These results are auxiliary and are not the statement of Stacks 0FGH: the domain `S.Obj` is the
ambient category of `S` (which, to produce `M_k`, already contains the Tate twists), not the
category of correspondences of degree zero, and the step of the source that extends `F` across the
twists by inverting the image of `F(c₂)` is not carried out here. The statement of Stacks 0FGH is
`Stacks.WeilCohomology.ChowMotiveCat.universalProperty` in
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.MotivesUniversalProperty`.

## Main definitions

* `Stacks.WeilCohomology.CorrespondenceStructure.motiveExtension`: the extension of a functor on
  `S.Obj` to a functor on its Karoubi envelope `S.Motive`.

## Main results

* `Stacks.WeilCohomology.CorrespondenceStructure.motiveExtensionCompToKaroubi`: the extension
  restricts to the original functor along `h`.
* `Stacks.WeilCohomology.CorrespondenceStructure.existsUnique_natTrans_of_restriction`: a map
  between two functors on `S.Motive` is determined by its restriction along `h`, so the
  extension is unique up to a unique isomorphism.
* `Stacks.WeilCohomology.CorrespondenceStructure.exists_symmetricMonoidal_factorisation`: a
  symmetric monoidal functor on `S.Obj` factors through `S.Motive` by a symmetric monoidal
  functor.

## Implementation notes

The hypotheses on an idempotent `c` of an object `X` with invertible image `F(c)` in
`exists_symmetricMonoidal_factorisation` are not used by its proof: the Karoubi envelope's
universal property needs no invertible object. Inverting the image of `F(c₂)` is the second step of
the proof of Stacks 0FGH, carried out for `M_k` in
`Stacks.WeilCohomology.ChowMotiveCat.universalProperty`.

## References

* [Stacks Project, Tag 0FGH](https://stacks.math.columbia.edu/tag/0FGH)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Idempotents Functor

universe v u w v₂ u₂

namespace Stacks.WeilCohomology.CorrespondenceStructure

variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
  (S : CorrespondenceStructure.{v, u, w} D)
  {𝒞 : Type u₂} [Category.{v₂} 𝒞] [MonoidalCategory 𝒞] [SymmetricCategory 𝒞]
  [IsIdempotentComplete 𝒞]

section Extension

variable (F : S.Obj ⥤ 𝒞) [F.Braided]

/-- The extension to Chow motives of a symmetric monoidal functor on correspondences with
Karoubian target: a motive `(X, p, m)` is sent to the image of the projector `F(p)` on `F(X)`,
which exists because the target is Karoubian. -/
noncomputable def motiveExtension : S.Motive ⥤ 𝒞 :=
  Karoubi.mapFunctor F ⋙ (toKaroubiEquivalence 𝒞).inverse

/-- The monoidal structure on the extension: the Karoubi envelope of a monoidal category is
monoidal, the extension of a monoidal functor is monoidal, and Karoubi completion does not
change a monoidal category that is already idempotent complete. -/
noncomputable instance motiveExtensionMonoidal : (motiveExtension S F).Monoidal :=
  letI : (toKaroubiEquivalence 𝒞).inverse.Monoidal := (toKaroubiEquivalence 𝒞).inverseMonoidal
  inferInstanceAs (Karoubi.mapFunctor F ⋙ (toKaroubiEquivalence 𝒞).inverse).Monoidal

/-- The extension is a functor of symmetric monoidal categories: both factors are braided. -/
noncomputable instance motiveExtensionBraided : (motiveExtension S F).Braided :=
  letI : (toKaroubiEquivalence 𝒞).functor.Braided := inferInstanceAs (toKaroubi 𝒞).Braided
  letI : (toKaroubiEquivalence 𝒞).inverse.Braided := (toKaroubiEquivalence 𝒞).inverseBraided
  inferInstanceAs (Karoubi.mapFunctor F ⋙ (toKaroubiEquivalence 𝒞).inverse).Braided

/-- The extension restricts along `toKaroubi S.Obj` to the functor one started with: `F` factors
through the Karoubi envelope `S.Motive`. An auxiliary step towards Stacks 0FGH, whose statement is
`Stacks.WeilCohomology.ChowMotiveCat.universalProperty`. -/
noncomputable def motiveExtensionCompToKaroubi :
    toKaroubi S.Obj ⋙ motiveExtension S F ≅ F :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (Karoubi.toKaroubiCompMapFunctorIso F) (toKaroubiEquivalence 𝒞).inverse ≪≫
      Functor.associator _ _ _ ≪≫
        (isoWhiskerLeft F (toKaroubiEquivalence 𝒞).unitIso).symm ≪≫ F.rightUnitor

end Extension

omit [MonoidalCategory 𝒞] [SymmetricCategory 𝒞] [IsIdempotentComplete 𝒞] in
/-- A natural transformation between two functors on the Karoubi envelope `S.Motive` is
determined by its restriction along `toKaroubi S.Obj`, and every natural transformation of the
restrictions arises this way. Hence a factorisation of a functor on `S.Obj` through `S.Motive` is
unique up to a unique isomorphism. An auxiliary step towards Stacks 0FGH, whose statement is
`Stacks.WeilCohomology.ChowMotiveCat.universalProperty`. -/
theorem existsUnique_natTrans_of_restriction {G₁ G₂ : S.Motive ⥤ 𝒞}
    (τ : toKaroubi S.Obj ⋙ G₁ ⟶ toKaroubi S.Obj ⋙ G₂) :
    ∃! α : G₁ ⟶ G₂, whiskerLeft (toKaroubi S.Obj) α = τ := by
  have hff := whiskeringLeftObjToKaroubiFullyFaithful (C := S.Obj) (D := 𝒞)
  exact ⟨hff.preimage τ, hff.map_preimage τ,
    fun β hβ => hff.map_injective (hβ.trans (hff.map_preimage τ).symm)⟩

/-- A `ℚ`-linear symmetric monoidal functor `F` on `S.Obj` into a `ℚ`-linear Karoubian symmetric
monoidal category factors through the Karoubi envelope `S.Motive` by a symmetric monoidal functor.
The hypotheses on the idempotent `c` of `X` with invertible image are not used: this is the
Karoubi envelope's universal property, an auxiliary step towards Stacks 0FGH, whose statement is
`Stacks.WeilCohomology.ChowMotiveCat.universalProperty`. Uniqueness of the factorisation up to a
unique isomorphism is
`Stacks.WeilCohomology.CorrespondenceStructure.existsUnique_natTrans_of_restriction`. -/
theorem exists_symmetricMonoidal_factorisation [Preadditive S.Obj] [Linear ℚ S.Obj]
    [Preadditive 𝒞] [Linear ℚ 𝒞] (F : S.Obj ⥤ 𝒞) [F.Braided] [F.Additive]
    [Functor.Linear ℚ F]
    (X : S.Obj) (c : X ⟶ X) (_hc : c ≫ c = c)
    (_hinv : ∃ (U : 𝒞) (i : U ⟶ F.obj X) (e : F.obj X ⟶ U),
      i ≫ e = 𝟙 U ∧ e ≫ i = F.map c ∧ IsInvertible U) :
    ∃ (G : S.Motive ⥤ 𝒞) (_ : G.Braided), Nonempty (toKaroubi S.Obj ⋙ G ≅ F) :=
  ⟨motiveExtension S F, motiveExtensionBraided S F, ⟨motiveExtensionCompToKaroubi S F⟩⟩

end Stacks.WeilCohomology.CorrespondenceStructure

end
