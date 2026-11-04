module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedColimits

/-!
# A morphism between two homotopy colimits compatible with an isomorphism of systems

Let `C` be an abelian category in which colimits over `ℕ` exist and are exact, and whose
cohomology functors `Hⁿ : D(C) ⥤ C` commute with countable direct sums. Let `cₙ : Kₙ ⟶ K` and
`c'ₙ : K'ₙ ⟶ K'` exhibit `K` and `K'` as homotopy colimits of two systems of `D(C)`, let
`α : (Kₙ) ≅ (K'ₙ)` be an isomorphism of systems and let `h : K ⟶ K'` be compatible with the
coprojections, `cₙ ≫ h = αₙ ≫ c'ₙ`. Then `h` is an isomorphism.

A morphism out of a homotopy colimit is not determined by its restrictions to the terms of the
system, so this cannot be proved by the uniqueness of homotopy colimits alone: the morphism `h` is
given, and only its restrictions are known. Cohomology detects it. By [Stacks, Tag 0CRK]
(`CategoryTheory.Pretriangulated.exists_iso_colimit_of_isHomotopyColimit`) `Hⁿ(K)` is the colimit
of the `Hⁿ(Kₙ)` with the coprojections `Hⁿ(cₙ)`, and likewise for `K'`; through these
identifications `Hⁿ(h)` is the colimit of the isomorphisms `Hⁿ(αₙ)`.

## Main results

* `DerivedCategory.isIso_of_isHomotopyColimitCocone_of_iso`: the comparison.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DerivedCategory

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  [HasColimitsOfShape ℕ C] [HasExactColimitsOfShape ℕ C]
  [∀ n : ℤ, PreservesColimitsOfShape (Discrete ℕ) (homologyFunctor C n)]

/-- **A morphism between two homotopy colimits compatible with an isomorphism of the systems is
an isomorphism**, in the derived category of an abelian category whose cohomology functors
commute with countable direct sums and in which colimits over `ℕ` are exact. -/
theorem isIso_of_isHomotopyColimitCocone_of_iso {F F' : ℕ ⥤ DerivedCategory C}
    [HasCoproduct F.obj] [HasCoproduct F'.obj] {K K' : DerivedCategory C}
    {c : ∀ n, F.obj n ⟶ K} {c' : ∀ n, F'.obj n ⟶ K'}
    (hc : IsHomotopyColimitCocone F c) (hc' : IsHomotopyColimitCocone F' c')
    (α : F ≅ F') (h : K ⟶ K') (hcomm : ∀ n, c n ≫ h = α.hom.app n ≫ c' n) : IsIso h := by
  rw [DerivedCategory.isIso_iff]
  intro n
  let H := homologyFunctor C n
  obtain ⟨q, hT⟩ := hc
  obtain ⟨q', hT'⟩ := hc'
  obtain ⟨e, he⟩ := exists_iso_colimit_of_isHomotopyColimit F H (Sigma.desc c) q hT
  obtain ⟨e', he'⟩ := exists_iso_colimit_of_isHomotopyColimit F' H (Sigma.desc c') q' hT'
  have key : e.hom ≫ H.map h = colimMap (Functor.whiskerRight α.hom H) ≫ e'.hom := by
    refine colimit.hom_ext fun m => ?_
    rw [reassoc_of% (he m), ι_colimMap_assoc, he' m]
    simp only [Sigma.ι_desc, ← H.map_comp, hcomm, Functor.whiskerRight_app]
  have : IsIso (e.hom ≫ H.map h) := by
    rw [key]
    infer_instance
  exact IsIso.of_isIso_comp_left e.hom (H.map h)

end DerivedCategory
