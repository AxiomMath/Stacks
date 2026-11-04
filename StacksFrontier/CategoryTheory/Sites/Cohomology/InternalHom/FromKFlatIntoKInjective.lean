module

public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.Defs
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplex
import StacksCore.Tactic.StacksAttribute

/-!
# The internal Hom complex from a K-flat complex into a K-injective complex

Let `(C, O)` be a ringed site, let `L` be a K-flat complex of `O`-modules and let `I` be a
K-injective complex of `O`-modules. Stacks 0A96 asserts that the internal Hom complex
`SheafHom(L, I)` is again K-injective.

The Stacks proof is a four-step computation: for an acyclic complex `K`,

`Hom_{K(O)}(K, SheafHom(L, I)) = H⁰(Γ(SheafHom(K, SheafHom(L, I))))`
`                              = H⁰(Γ(SheafHom(Tot(K ⊗_O L), I)))`
`                              = Hom_{K(O)}(Tot(K ⊗_O L), I) = 0`,

the outer two equalities being Stacks 0A8Z, the middle one the currying isomorphism of
Stacks 0A90, and the vanishing holding because `Tot(K ⊗_O L)` is acyclic (`L` is K-flat) and
`I` is K-injective.

Everything in that computation except the currying isomorphism is available here, so this file
proves the implication with the currying isomorphism as an explicit hypothesis, in exactly the
shape the `iso` field of Stacks 0A90 provides it. The tagged statement of Stacks 0A96 is
obtained from `isKInjective_sheafHomComplex_of_curryIso` by supplying that field, and nothing
else is missing.

## Main results

* `CochainComplex.subsingleton_homotopyCategory_hom_of_acyclic_of_isKInjective`: in the
  homotopy category of an abelian category there is at most one morphism from an acyclic
  complex into a K-injective complex.
* `AlgebraicGeometry.RingedSite.subsingleton_homotopyCategoryHom_sheafHomComplex`: for `L`
  K-flat and `I` K-injective, and granted the currying isomorphism at `K`, there is at most one
  morphism `K ⟶ SheafHom(L, I)` in the homotopy category whenever `K` is acyclic.
* `AlgebraicGeometry.RingedSite.isKInjective_sheafHomComplex_of_curryIso`: Stacks 0A96, with
  the currying isomorphism of Stacks 0A90 as a hypothesis.

## Implementation notes

The hypothesis is taken as a family of isomorphisms indexed by the first complex rather than as
the whole structure of Stacks 0A90, so that it is the weakest input from which the conclusion
follows: neither the induced maps of internal Hom complexes nor their naturality is used.

Stacks 0A8Z computes `Hⁿ(Γ(SheafHom(K, M)))` as morphisms `K ⟶ M[n]` in the homotopy category,
so the degree-zero instance lands in morphisms into the shift `M⟦(0 : ℤ)⟧` rather than into `M`
itself; the two are compared by the image under the quotient functor of
`CategoryTheory.shiftFunctorZero`, which is the last step of
`subsingleton_homotopyCategoryHom_sheafHomComplex`.

The complexes are those of `SheafOfModules.{u} X.ringSheaf`, the spelling of the internal Hom
complex of Stacks 0A8Z, while K-flatness and the total tensor complex of Stacks 06YM are stated
over `Stacks.SheafOfModules.Tensor.ringSheaf X.O`. The two sheaves of rings are definitionally
  equal and both
spellings are abbreviations, so no transport and no transparency option is needed; this is the
same arrangement as in `StacksDraft.Ch21.Sec34.DerivedInternalHomTensorSource`.

## References

* [Stacks Project, Tag 0A96](https://stacks.math.columbia.edu/tag/0A96)
* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v w

namespace CochainComplex

/-- In the homotopy category of cochain complexes in an abelian category there is at most one
morphism from an acyclic complex into a K-injective complex, namely zero.

This is `CochainComplex.IsKInjective.rightOrthogonal` packaged as a `Subsingleton`, which is the
form in which it transports along the additive equivalences of Stacks 0A8Z. -/
theorem subsingleton_homotopyCategory_hom_of_acyclic_of_isKInjective
    {A : Type v} [Category.{w} A] [Abelian A] {T J : CochainComplex A ℤ}
    (hT : T.Acyclic) [J.IsKInjective] :
    Subsingleton
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj T ⟶
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj J) :=
  subsingleton_of_forall_eq 0 fun g => IsKInjective.rightOrthogonal J g
    ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic T).2 hT)

end CochainComplex

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]

/-- For `L` K-flat, `I` K-injective and `K` acyclic, there is at most one morphism
`K ⟶ SheafHom(L, I)` in the homotopy category.

This is the Stacks 0A96 computation: by Stacks 0A8Z such morphisms are `H⁰` of the global
sections of `SheafHom(K, SheafHom(L, I))`, by the currying isomorphism `curry` that complex is
`SheafHom(Tot(K ⊗ L), I)`, and by Stacks 0A8Z again its `H⁰` computes morphisms
`Tot(K ⊗ L) ⟶ I` in the homotopy category, of which there is at most one because
`Tot(K ⊗ L)` is acyclic and `I` is K-injective. -/
theorem subsingleton_homotopyCategoryHom_sheafHomComplex
    (K L I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hK : K.Acyclic) (hL : Stacks.SheafOfModules.IsKFlat X.O L) [I.IsKInjective]
    (curry : (sheafHomComplex X K (sheafHomComplex X L I).obj).obj ≅
      (sheafHomComplex X
        (((Stacks.SheafOfModules.Tensor.tensorComplex.{u, u, u} X.O).obj K).obj L) I).obj) :
    Subsingleton
      ((HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (ComplexShape.up ℤ)).obj K ⟶
        (HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (ComplexShape.up ℤ)).obj (sheafHomComplex X L I).obj) := by
  set T := ((Stacks.SheafOfModules.Tensor.tensorComplex.{u, u, u} X.O).obj K).obj L
  -- `H⁰(Γ(SheafHom(Tot(K ⊗ L), I)))` is a subsingleton, by Stacks 0A8Z and K-injectivity.
  have hInner : Subsingleton
      ((globalSectionsComplex X (sheafHomComplex X T I).obj).homology 0) := by
    have := CochainComplex.subsingleton_homotopyCategory_hom_of_acyclic_of_isKInjective
      (J := I⟦(0 : ℤ)⟧) (show T.Acyclic from hL K hK)
    exact (sheafHomComplexHomologyEquivHomotopyCategory X T I 0).injective.subsingleton
  -- Transport along the currying isomorphism.
  have hOuter : Subsingleton
      ((globalSectionsComplex X
        (sheafHomComplex X K (sheafHomComplex X L I).obj).obj).homology 0) := by
    have eSections :
        globalSectionsComplex X (sheafHomComplex X K (sheafHomComplex X L I).obj).obj ≅
          globalSectionsComplex X (sheafHomComplex X T I).obj :=
      ((abelianGlobalSectionsFunctor X).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
        (((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          ).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso curry)
    have eHomology :=
      ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) 0).mapIso
        eSections).addCommGroupIsoToAddEquiv
    exact ⟨fun a b => eHomology.injective (hInner.elim (eHomology a) (eHomology b))⟩
  -- Stacks 0A8Z again, and the degree-zero shift.
  have eOuter :=
    sheafHomComplexHomologyEquivHomotopyCategory X K (sheafHomComplex X L I).obj 0
  have eQ : (HomotopyCategory.quotient
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ)).obj ((sheafHomComplex X L I).obj⟦(0 : ℤ)⟧) ≅
      (HomotopyCategory.quotient
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ)).obj (sheafHomComplex X L I).obj :=
    (HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ)).mapIso
        ((CategoryTheory.shiftFunctorZero
          (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
            ℤ).app (sheafHomComplex X L I).obj)
  exact ⟨fun g₁ g₂ => (cancel_mono eQ.inv).1 <| eOuter.symm.injective <|
    hOuter.elim (eOuter.symm (g₁ ≫ eQ.inv)) (eOuter.symm (g₂ ≫ eQ.inv))⟩

/-- **Stacks 0A96**, granted the currying isomorphism of Stacks 0A90. The internal Hom complex
from a K-flat complex `L` into a K-injective complex `I` is K-injective.

The hypothesis `curry` is the `iso` field of the currying construction of Stacks 0A90,
evaluated at an arbitrary first complex and at `L` and `I`; no other part of that construction
is used. -/
theorem isKInjective_sheafHomComplex_of_curryIso
    (L I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hL : Stacks.SheafOfModules.IsKFlat X.O L) [I.IsKInjective]
    (curry : ∀ K : CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ,
      (sheafHomComplex X K (sheafHomComplex X L I).obj).obj ≅
        (sheafHomComplex X
          (((Stacks.SheafOfModules.Tensor.tensorComplex.{u, u, u} X.O).obj K).obj L) I).obj) :
    (sheafHomComplex X L I).obj.IsKInjective := by
  refine ⟨fun {K} f hK => ?_⟩
  rw [← HomotopyCategory.quotient_map_eq_zero_iff]
  exact (subsingleton_homotopyCategoryHom_sheafHomComplex X K L I hK hL (curry K)).elim _ 0

end AlgebraicGeometry.RingedSite

end
