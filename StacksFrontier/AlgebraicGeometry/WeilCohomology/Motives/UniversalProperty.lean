module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Motives.MonoidalStructure
public import StacksFrontier.CategoryTheory.Idempotents.KaroubiMonoidalExtension
public import StacksFrontier.CategoryTheory.Monoidal.BraidedEquivalenceInverse
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleObject
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# The universal property of the category of Chow motives

A `ℚ`-linear functor of symmetric monoidal categories from the category of correspondences of
degree zero to a `ℚ`-linear Karoubian symmetric monoidal category factors through the category
`M_k` of Chow motives, and the factorisation is unique up to a unique isomorphism.

The extension is the Karoubi envelope's universal property: `M_k` is the Karoubi envelope of the
category of correspondences, the target is Karoubian, and a functor into a Karoubian category
extends to the Karoubi envelope.

## Main definitions

* `Stacks.WeilCohomology.CorrespondenceStructure.motiveExtension`: the extension of a functor on
  correspondences to a functor on Chow motives.

## Main results

* `Stacks.WeilCohomology.CorrespondenceStructure.motiveExtensionCompToKaroubi`: the extension
  restricts to the original functor along `h`.
* `Stacks.WeilCohomology.CorrespondenceStructure.existsUnique_natTrans_of_restriction`: a map
  between two functors on `M_k` is determined by its restriction along `h`, so the
  factorisation is unique up to a unique isomorphism.
* `Stacks.WeilCohomology.CorrespondenceStructure.exists_symmetricMonoidal_factorisation`: the
  statement of Stacks 0FGH.

## Implementation notes

Two points where the formalisation departs from the letter of the source.

The source says the functor factors *uniquely*. Taken literally that is false for the
construction the source gives, which depends on choices: the image of a projector in a Karoubian
category is a kernel and so is determined only up to unique isomorphism, an inverse of the
invertible object is a further choice, and the identifications used on morphisms of unequal twist
depend on a choice of rational point of `P¹`. What is true, and what is proved here, is that the
factorisation is unique up to a unique isomorphism; this is also the form in which the result is
used.

The Tate twist `m` of a motive `(X, p, m)` is carried by the ambient symmetric monoidal category,
the convention of `StacksFrontier.AlgebraicGeometry.WeilCohomology.Motives.Category`. The source's
construction tensors by the `-m`-th power of the invertible object to account for the twist; here
the twists are already objects of the ambient category, so that bookkeeping is absorbed into the
ambient category and the hypothesis that the image of `F(c₂)` is invertible is not needed for the
construction. It is carried in `exists_symmetricMonoidal_factorisation` all the same, that being
the statement of the source.

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

/-- **Stacks Project, Tag 0FGH.** The extension restricts along the functor `h` of Stacks 0FGA to
the functor one started with: `F` factors through the category of Chow motives. -/
@[stacks 0FGH "the extension of F to M_k restricts to F along h"]
noncomputable def motiveExtensionCompToKaroubi :
    toKaroubi S.Obj ⋙ motiveExtension S F ≅ F :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (Karoubi.toKaroubiCompMapFunctorIso F) (toKaroubiEquivalence 𝒞).inverse ≪≫
      Functor.associator _ _ _ ≪≫
        (isoWhiskerLeft F (toKaroubiEquivalence 𝒞).unitIso).symm ≪≫ F.rightUnitor

end Extension

omit [MonoidalCategory 𝒞] [SymmetricCategory 𝒞] [IsIdempotentComplete 𝒞] in
/-- **Stacks Project, Tag 0FGH.** A natural transformation between two functors on the category of
Chow motives is determined by its restriction along the functor `h` of Stacks 0FGA, and every
natural transformation of the restrictions arises this way. Hence a factorisation of a functor on
correspondences through `M_k` is unique up to a unique isomorphism. -/
@[stacks 0FGH "a factorisation through M_k is unique up to a unique isomorphism; the source's \
`uniquely` is corrected, the construction it gives depending on choices"]
theorem existsUnique_natTrans_of_restriction {G₁ G₂ : S.Motive ⥤ 𝒞}
    (τ : toKaroubi S.Obj ⋙ G₁ ⟶ toKaroubi S.Obj ⋙ G₂) :
    ∃! α : G₁ ⟶ G₂, whiskerLeft (toKaroubi S.Obj) α = τ := by
  have hff := whiskeringLeftObjToKaroubiFullyFaithful (C := S.Obj) (D := 𝒞)
  exact ⟨hff.preimage τ, hff.map_preimage τ,
    fun β hβ => hff.map_injective (hβ.trans (hff.map_preimage τ).symm)⟩

/-- **Stacks Project, Tag 0FGH.** Let `X`, `c₂` be as in Stacks 0FG6. Let `𝒞` be a `ℚ`-linear
Karoubian symmetric monoidal category. A `ℚ`-linear functor of symmetric monoidal categories from
the category of correspondences of degree zero to `𝒞`, such that the image of `F(c₂)` on `F(X)`
is an invertible object, factors through a functor `M_k ⟶ 𝒞` of symmetric monoidal categories;
the factorisation is unique up to a unique isomorphism by
`Stacks.WeilCohomology.CorrespondenceStructure.existsUnique_natTrans_of_restriction`. -/
@[stacks 0FGH "a Q-linear symmetric monoidal functor on degree-zero correspondences whose image \
of F(c2) is invertible factors through M_k"]
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
