module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationQuotientQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FiniteAlgebraSurjectiveSystemOfSymmetricAlgebra

/-!
# A finite quasi-coherent algebra on a qcqs algebraic space is a directed colimit of finite and
finitely presented algebras

Let `S` be a scheme, `Y` a quasi-compact and quasi-separated algebraic space over `S` and `𝒜` a
finite quasi-coherent `𝒪_Y`-algebra.  Then `𝒜` is a directed colimit of finite and finitely
presented quasi-coherent `𝒪_Y`-algebras with surjective transition maps (Stacks 086Z).

The underlying module of `𝒜` is quasi-coherent of finite type
(`AlgebraicGeometry.Space.isFiniteTypeOnSite_underlyingModule_of_isFinite`), so by the first step
of Stacks 086Y (`AlgebraicGeometry.Space.exists_epi_of_isFinitePresentationOnSite_of_isFiniteType`)
it is a quotient of a module `𝒢` of finite presentation; the rest of the source's proof, from such
a `𝒢`, is
`AlgebraicGeometry.Space.exists_directed_isFinite_isFinitePresentation_locallySurjective_of_epi`.

## Main results

* `exists_directed_isFinite_isFinitePresentation_locallySurjective_of_isFinite`: a finite
  quasi-coherent algebra on a qcqs algebraic space is a directed colimit of finite and finitely
  presented quasi-coherent algebras with surjective transition maps.

## References

* [Stacks Project, Tag 086Z](https://stacks.math.columbia.edu/tag/086Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks Project, Tag 086Z.** Let `S` be a scheme, let `Y` be a quasi-compact and
quasi-separated algebraic space over `S` and let `𝒜` be a finite quasi-coherent `𝒪_Y`-algebra.
Then `𝒜` is the colimit of a system of quasi-coherent `𝒪_Y`-algebras indexed by a nonempty
directed preorder, every member of which is finite and of finite presentation, and every
transition map of which is surjective (locally surjective as a morphism of sheaves on the small
étale site, which for quasi-coherent algebras is surjectivity on the sections over every affine
étale chart).

The proof is the source's.  Stacks 086Y gives a quasi-coherent module `𝒢` of finite presentation
with an epimorphism `𝒢 ⟶ 𝒜`; then
`AlgebraicGeometry.Space.exists_directed_isFinite_isFinitePresentation_locallySurjective_of_epi`
forms `Sym(𝒢)`, writes the kernel of `Sym(𝒢) ⟶ 𝒜` as the union of its finite type
quasi-coherent submodules `ℰ` (Stacks 0829), takes the quotients `Sym(𝒢)/(ℰ)`, shows they are
finite for `ℰ` large, and reindexes by a directed preorder. -/
@[stacks 086Z]
theorem exists_directed_isFinite_isFinitePresentation_locallySurjective_of_isFinite
    (Y : AlgebraicSpaces B S hS) (A : QuasicoherentAlgebra B S hS Y)
    (hqc : IsQuasiCompactSpace B S hS Y.obj)
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y.obj)
    (hA : A.obj.IsFinite) :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (D : I ⥤ QuasicoherentAlgebra B S hS Y) (φ : D ⟶ (Functor.const I).obj A),
      Nonempty (IsColimit (Cocone.mk A φ)) ∧
      (∀ i, (D.obj i).obj.IsFinite ∧ (D.obj i).obj.IsFinitePresentation) ∧
      ∀ i j (h : i ≤ j), Presheaf.IsLocallySurjective
        (SmallEtale.topology B S hS Y.obj) (D.map (homOfLE h)).hom.right.hom := by
  have := isFiniteTypeOnSite_underlyingModule_of_isFinite B S hS A.obj A.property hA
  obtain ⟨G, hGfp, p, hp⟩ := exists_epi_of_isFinitePresentationOnSite_of_isFiniteType B S hS
    B.contains_terminal Y.2 hqc hqs (AlgebraSheaf.underlyingModule A.obj) A.property
  exact exists_directed_isFinite_isFinitePresentation_locallySurjective_of_epi B S hS Y A hqc hqs
    hA G (SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentationOnSite G) hGfp p hp

end AlgebraicGeometry.Space
