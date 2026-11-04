module

public import StacksFrontier.Homology.KFlat.BifunctorTransportEquivalence

/-!
# Transporting bounded below K-flat resolutions along an equivalence

`CochainComplex.KFlatBifunctor.exists_kFlat_resolution_of_equivalence` carries the existence of
K-flat resolutions across an equivalence `e : A ≌ A'` which takes a bifunctor `F` on `A` to a
bifunctor `F'` on `A'`.  It says nothing about boundedness, and the consumer that needs
boundedness is
`CochainComplex.KFlatMonoidal.derivedPlusMonoidal`, whose hypothesis `hGE` asks that a complex
vanishing in degrees below `a` receive a quasi-isomorphism from a K-flat complex vanishing in
degrees below some `a'`.  This file adds the bounded below statement, in exactly that shape.

Nothing about the proof is new: an equivalence of abelian categories is faithful and additive in
both directions, so `CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff` moves the bound
across it in either direction, and the bound on the resolving complex is produced by the same
`e.functor` that produces the resolution.  What is new is that the statement now says it, so a
consumer whose hypothesis is `hGE` can be fed a reduction to the other side of an equivalence
rather than to the unbounded statement.

## Main results

* `CochainComplex.KFlatBifunctor.exists_kFlat_resolution_isStrictlyGE_of_equivalence`:
  **bounded below K-flat resolutions transport along an equivalence carrying `F` to `F'`.**
  This is the bounded below companion of
  `CochainComplex.KFlatBifunctor.exists_kFlat_resolution_of_equivalence`, and it is the
  hypothesis `hGE` of `CochainComplex.KFlatMonoidal.derivedPlusMonoidal` transported.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CochainComplex.KFlatBifunctor

variable {A A' : Type*} [Category A] [Category A'] [Abelian A] [Abelian A']
  (F : A ⥤ A ⥤ A) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ K₂ : CochainComplex A ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ F (ComplexShape.up ℤ)]
  (F' : A' ⥤ A' ⥤ A') [F'.Additive] [∀ X, (F'.obj X).Additive]
  [∀ (K₁ K₂ : CochainComplex A' ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ F' (ComplexShape.up ℤ)]
  (e : A ≌ A') [e.functor.Additive] [e.inverse.Additive]
  (ε : ∀ a b : A, e.functor.obj ((F.obj a).obj b) ≅
    (F'.obj (e.functor.obj a)).obj (e.functor.obj b))
  (hε₁ : ∀ {a a' : A} (f : a ⟶ a') (b : A),
    e.functor.map ((F.map f).app b) ≫ (ε a' b).hom =
      (ε a b).hom ≫ (F'.map (e.functor.map f)).app (e.functor.obj b))
  (hε₂ : ∀ (a : A) {b b' : A} (g : b ⟶ b'),
    e.functor.map ((F.obj a).map g) ≫ (ε a b').hom =
      (ε a b).hom ≫ (F'.obj (e.functor.obj a)).map (e.functor.map g))

include ε hε₁ hε₂

/-- **The existence of bounded below K-flat resolutions transports along an equivalence carrying
`F` to `F'`.**

If every cochain complex over `A` vanishing in degrees below `a` receives a quasi-isomorphism
from a complex which is K-flat for `F` and vanishes in degrees below some `a'`, then the same
holds over `A'` for `F'`.  Given `G` over `A'` vanishing below `a`, the complex `e⁻¹G` vanishes
below `a` because `e.inverse` is faithful and additive
(`CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff`); resolve it over `A` and apply
`e`, which both preserves the bound, for the same reason, and preserves K-flatness, by
`CochainComplex.KFlatBifunctor.kFlat_map_of_equivalence`.  The counit
`CochainComplex.KFlatBifunctor.equivalenceCounitComplexIso` lands the resolution on `G` itself,
exactly as in the unbounded
`CochainComplex.KFlatBifunctor.exists_kFlat_resolution_of_equivalence`.

This is the hypothesis `hGE` of `CochainComplex.KFlatMonoidal.derivedPlusMonoidal`, so an
equivalence carries that hypothesis across and with it the monoidal structure on the bounded
below derived category. -/
theorem exists_kFlat_resolution_isStrictlyGE_of_equivalence
    (hres : ∀ (a : ℤ) (G : CochainComplex A ℤ), G.IsStrictlyGE a →
      ∃ (a' : ℤ) (P : CochainComplex A ℤ) (f : P ⟶ G), P.IsStrictlyGE a' ∧
        KFlat F P ∧ QuasiIso f)
    (a : ℤ) (G : CochainComplex A' ℤ) (hG : G.IsStrictlyGE a) :
    ∃ (a' : ℤ) (P : CochainComplex A' ℤ) (f : P ⟶ G), P.IsStrictlyGE a' ∧
      KFlat F' P ∧ QuasiIso f := by
  have hGinv : CochainComplex.IsStrictlyGE
      ((e.inverse.mapHomologicalComplex (ComplexShape.up ℤ)).obj G) a :=
    (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff _ e.inverse a).2 hG
  obtain ⟨a', P₀, f₀, hP₀GE, hP₀, hf₀⟩ :=
    hres a ((e.inverse.mapHomologicalComplex (ComplexShape.up ℤ)).obj G) hGinv
  exact ⟨a', _, (e.functor.mapHomologicalComplex (ComplexShape.up ℤ)).map f₀ ≫
      (equivalenceCounitComplexIso e G).hom,
    (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff _ e.functor a').2 hP₀GE,
    kFlat_map_of_equivalence F F' e ε hε₁ hε₂ P₀ hP₀, inferInstance⟩

end CochainComplex.KFlatBifunctor

end
