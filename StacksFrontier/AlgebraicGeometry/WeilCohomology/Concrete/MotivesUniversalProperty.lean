module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.MotivesFiniteBiproducts
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.MotivesMonoidal
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectiveLineSummands
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CorrespondenceMonoidal
public import StacksFrontier.CategoryTheory.Graded.TwistedKaroubiUniversal
public import StacksFrontier.CategoryTheory.Graded.TwistedKaroubiMonoidalPreadditive
public import StacksFrontier.CategoryTheory.Monoidal.InvertingObject.Existence
public import StacksFrontier.CategoryTheory.Monoidal.InvertingObject.Uniqueness
public import StacksFrontier.CategoryTheory.Monoidal.InvertingObject.Linear

/-!
# The universal property of the category of Chow motives

Stacks 0FGH. Let `X = P¹_k`, let `x` be a `k`-rational point of `X` and `c₂ = [X × x]` as in
Example 0FG6. Let `𝒞` be a `ℚ`-linear Karoubian symmetric monoidal category. Any `ℚ`-linear functor
of symmetric monoidal categories

  `F : {smooth projective schemes over k, correspondences of degree 0} ⥤ 𝒞`

such that the image of `F(c₂)` on `F(X)` is an invertible object factors uniquely through a
functor `M_k ⥤ 𝒞` of symmetric monoidal categories, along `X ↦ (X, 1, 0)`.

The category of smooth projective schemes with correspondences of degree zero is the degree-zero
category `DegreeZero ℚ (CorrespondenceCategory k)` of the graded category of correspondences of
Stacks 0FG2, symmetric monoidal by Stacks 0FG7; `M_k = ChowMotiveCat k` is the category of triples
`(X, p, m)` of Stacks 0FGA with the symmetric monoidal structure of Stacks 0FGC
(`Stacks.WeilCohomology.ChowMotiveCat.symmetricCategory`); and the functor along which `F`
factors is `CategoryTheory.GradedCategory.TwistedKaroubi.untwistedOfObj`, `X ↦ (X, 1, 0)`.

## Proof

As in the source: first `F` is extended to the motives of twist zero, `(X, p) ↦` the image of
`F(p)` in `F(X)`, which exists because `𝒞` is Karoubian
(`CategoryTheory.Idempotents.Karoubi.lift`); then it is extended across the twists, using that the
image of `F(c₂)`, the value at the Lefschetz motive `(X, c₂, 0) ≅ 𝟏(-1)` (Stacks 0FGD), is
invertible. The second step is the abstract result `CategoryTheory.InvertingObject.linearExistence`
and `CategoryTheory.InvertingObject.uniqueness` for the functor `(X, p) ↦ (X, p, 0)`, whose
hypotheses (`(X, c₂, 0) ⊗ 𝟏(1) ≅ 𝟏`, the symmetry of `𝟏(1) ⊗ 𝟏(1)` is the identity, every motive
is `(Y, q, 0) ⊗ 𝟏(1)^{⊗ n}`) are proved in
`StacksFrontier.CategoryTheory.Graded.TwistedKaroubiTate`.

## Implementation notes

"Factors uniquely" is stated in the form in which it holds: the factorization is unique up to a
unique monoidal isomorphism compatible with the identifications along `X ↦ (X, 1, 0)`. Literal
uniqueness of the functor fails, as the source's construction involves choices (an image of each
projector, an inverse of `F(c₂)`). The extension is moreover additive and `ℚ`-linear. The target is
assumed to have an additive tensor product (`MonoidalPreadditive`), part of what a `ℚ`-linear
symmetric monoidal category is.

## Main results

* `Stacks.WeilCohomology.ChowMotiveCat.universalProperty`: **Stacks 0FGH**.

## References

* [Stacks Project, Tag 0FGH](https://stacks.math.columbia.edu/tag/0FGH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GradedCategory MonoidalCategory
  Idempotents AlgebraicGeometry Stacks.Chow

universe u v₂ u₂

namespace Stacks.WeilCohomology.ChowMotiveCat

/-- `X = P¹_k` as an object of the category of correspondences of degree zero. -/
abbrev projectiveLineDegreeZero (k : Type u) [Field k] : DegreeZero ℚ (CorrespondenceCategory k) :=
  GradedCompositionData.Obj.mk (projectiveLineObj k)

variable {k : Type u} [Field k]
  (x : (fieldChowSituation k).S ⟶ Stacks.Chow.relativeProjectiveLine (Spec (CommRingCat.of k)))
  (hx : x ≫ (Stacks.Chow.relativeProjectiveLine (Spec (CommRingCat.of k)) ↘
    Spec (CommRingCat.of k)) = 𝟙 (fieldChowSituation k).S)

/-- The projector `c₂ = [X × x]` of `X = P¹_k`, as an endomorphism of `X` in the category of
correspondences of degree zero. -/
def projectiveLineFibrePointDegreeZero :
    projectiveLineDegreeZero k ⟶ projectiveLineDegreeZero k :=
  DegreeZero.homMk (homOf 0 (projectiveLineFibrePointCorr x hx)) (homOf_mem_grade _)

/-- **Stacks Project, Tag 0FGH.** Let `X = P¹_k`, `x` a rational point and `c₂ = [X × x]`
(Example 0FG6). Let `𝒞` be a `ℚ`-linear Karoubian symmetric monoidal category. A `ℚ`-linear functor
of symmetric monoidal categories `F` from the category of smooth projective schemes over `k` with
correspondences of degree `0` to `𝒞`, such that the image of `F(c₂)` on `F(X)` is an invertible
object, factors through a functor `G : M_k ⥤ 𝒞` of symmetric monoidal categories along
`X ↦ (X, 1, 0)` — by a monoidal isomorphism, `G` being moreover additive and `ℚ`-linear — and the
factorization is unique: any two are related by a unique monoidal isomorphism compatible with the
identifications. -/
@[stacks 0FGH "a Q-linear symmetric monoidal functor F on degree-0 correspondences with the image
of F(c₂) on F(P¹) invertible factors through M_k, uniquely up to unique monoidal isomorphism"]
theorem universalProperty {𝒞 : Type u₂} [Category.{v₂} 𝒞] [MonoidalCategory 𝒞]
    [SymmetricCategory 𝒞] [Preadditive 𝒞] [Linear ℚ 𝒞] [MonoidalPreadditive 𝒞]
    [IsIdempotentComplete 𝒞]
    (F : DegreeZero ℚ (CorrespondenceCategory k) ⥤ 𝒞) [F.Braided] [F.Additive]
    [Functor.Linear ℚ F]
    (hF : ∃ (U : 𝒞) (i : U ⟶ F.obj (projectiveLineDegreeZero k))
      (e : F.obj (projectiveLineDegreeZero k) ⟶ U),
      i ≫ e = 𝟙 U ∧ e ≫ i = F.map (projectiveLineFibrePointDegreeZero x hx) ∧ IsInvertible U) :
    (∃ (G : ChowMotiveCat k ⥤ 𝒞) (_ : G.Braided) (_ : G.Additive) (_ : Functor.Linear ℚ G)
        (φ : TwistedKaroubi.untwistedOfObj (CorrespondenceCategory k) ⋙ G ≅ F),
        NatTrans.IsMonoidal φ.hom) ∧
      ∀ (G₁ G₂ : ChowMotiveCat k ⥤ 𝒞) [G₁.Braided] [G₂.Braided]
        (φ₁ : TwistedKaroubi.untwistedOfObj (CorrespondenceCategory k) ⋙ G₁ ≅ F)
        (φ₂ : TwistedKaroubi.untwistedOfObj (CorrespondenceCategory k) ⋙ G₂ ≅ F)
        [NatTrans.IsMonoidal φ₁.hom] [NatTrans.IsMonoidal φ₂.hom],
        ∃! θ : G₁ ≅ G₂, NatTrans.IsMonoidal θ.hom ∧
          Functor.whiskerLeft (TwistedKaroubi.untwistedOfObj (CorrespondenceCategory k)) θ.hom ≫
            φ₂.hom = φ₁.hom :=
  ⟨TwistedKaroubi.exists_extension_of_linearExistence (lefschetzKaroubi x hx)
      (lefschetzKaroubiIso x hx) (InvertingObject.linearExistence _ _ _ _) F hF,
    fun G₁ G₂ _ _ φ₁ φ₂ _ _ ↦ TwistedKaroubi.existsUnique_iso_of_uniqueness (lefschetzKaroubi x hx)
      (lefschetzKaroubiIso x hx) (InvertingObject.uniqueness _ _ _ _) F G₁ G₂ φ₁ φ₂⟩

end Stacks.WeilCohomology.ChowMotiveCat
