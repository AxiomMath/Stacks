module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConeWeakCokernel
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedHom

/-!
# Morphisms in the derived category into a graded injective K-injective module

Let `X` be a ringed site and let `A` be a sheaf of differential graded algebras on it. A right
differential graded `A`-module `I` which is K-injective and graded injective is *local for the
quasi-isomorphisms* of `K(Mod(A, d))`: precomposition with a quasi-isomorphism is bijective on
homotopy classes of morphisms into `I`. Consequently, for a quasi-isomorphism `N ⟶ I` into such
an `I`, `Hom_{D(A, d)}(M, N) = Hom_{K(Mod(A, d))}(M, I)`, and a quasi-isomorphism between two
such modules is an isomorphism of `K(Mod(A, d))`.

## Main results

* `SheafOfModules.DifferentialGradedModule.isLocal_quotient_obj_of_isKInjective`: a K-injective
  and graded injective right differential graded module is local for the quasi-isomorphisms.
* `SheafOfModules.DifferentialGradedModule.derivedHomEquivHomotopyHomOfKInjective`: the
  identification of `Hom_{D(A, d)}(M, N)` with the homotopy classes of morphisms `M ⟶ I`.
* `SheafOfModules.DifferentialGradedModule.derivedHomEquivHomotopyHomOfKInjective_symm_apply`:
  that identification sends a homotopy class to its image in `D(A, d)` composed with the inverse
  of the given quasi-isomorphism.
* `SheafOfModules.DifferentialGradedModule.isIso_quotient_map_of_quasiIso_of_isKInjective`: a
  quasi-isomorphism between two K-injective and graded injective right differential graded
  modules is an isomorphism of `K(Mod(A, d))`.

## Implementation notes

A ringed site here is one whose underlying category, its morphisms and its structure sheaf lie in
one universe. Locality is bijectivity of precomposition with a quasi-isomorphism: its
surjectivity is `exists_homotopic_lift_of_quasiIso` and its injectivity is
`homotopic_of_comp_homotopic`.

## References

* [Stacks Project, Tag 0FT8](https://stacks.math.columbia.edu/tag/0FT8)
* [Stacks Project, Tag 0FTN](https://stacks.math.columbia.edu/tag/0FTN)
* [Stacks Project, Tag 0FSX](https://stacks.math.columbia.edu/tag/0FSX)
-/
@[expose] public noncomputable section

open CategoryTheory

universe u v w

namespace SheafOfModules.DifferentialGradedModule

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}

section Abelian

variable [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-! ### Locality of a graded injective K-injective module -/

/-- A K-injective and graded injective right differential graded module `I` is local for the
quasi-isomorphisms of `K(Mod(A, d))`: precomposition with a quasi-isomorphism is bijective on
homotopy classes of morphisms into `I`. -/
@[stacks 0FSX "the bijectivity of precomposition with a quasi-isomorphism on homotopy classes of
morphisms into a graded injective K-injective module, which the source's proof establishes and
of which the lemma's dotted arrow is the surjectivity half"]
theorem isLocal_quotient_obj_of_isKInjective {I : DifferentialGradedModule.{u, v, w} A}
    (hI : IsKInjective I) (hI' : GradedInjective I) :
    (quasiIsomorphisms.{u, v, w} A).isLocal ((HomotopyCategory.quotient A).obj I) := by
  intro P Q φ hφ
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient A).map_surjective φ
  have hqi : QuasiIso f.toHomologicalComplex := hφ _ rfl
  refine ⟨fun g g' hgg => ?_, fun a => ?_⟩
  · obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient A).map_surjective g
    obtain ⟨g', rfl⟩ := (HomotopyCategory.quotient A).map_surjective g'
    simp only [← (HomotopyCategory.quotient A).map_comp] at hgg
    exact (HomotopyCategory.quotient_map_eq_iff _ _).mpr
      (homotopic_of_comp_homotopic hI hI' hqi _ _
        ((HomotopyCategory.quotient_map_eq_iff _ _).mp hgg))
  · obtain ⟨a, rfl⟩ := (HomotopyCategory.quotient A).map_surjective a
    obtain ⟨c, hc⟩ := exists_homotopic_lift_of_quasiIso hI hI' a f hqi
    refine ⟨(HomotopyCategory.quotient A).map c, ?_⟩
    change _ ≫ _ = _
    rw [← (HomotopyCategory.quotient A).map_comp,
      (HomotopyCategory.quotient_map_eq_iff _ _).mpr hc]

/-! ### Morphisms in the derived category into a graded injective K-injective module -/

/-- Let `(A, d)` be a sheaf of differential graded algebras on a ringed site, let `M`, `N` be
right differential graded `A`-modules and let `N ⟶ I` be a quasi-isomorphism into a graded
injective and K-injective right differential graded module `I`. Then morphisms `M ⟶ N` in
`D(A, d)` are the homotopy classes of morphisms `M ⟶ I`. -/
@[stacks 0FT8]
def derivedHomEquivHomotopyHomOfKInjective {M N I : DifferentialGradedModule.{u, v, w} A}
    (hI : IsKInjective I) (hI' : GradedInjective I) {b : N ⟶ I}
    (hb : QuasiIso b.toHomologicalComplex) :
    ((toDerivedCategory.{u, v, w} A).obj ((HomotopyCategory.quotient A).obj M) ⟶
        (toDerivedCategory.{u, v, w} A).obj ((HomotopyCategory.quotient A).obj N)) ≃
      ((HomotopyCategory.quotient A).obj M ⟶ (HomotopyCategory.quotient A).obj I) :=
  derivedHomEquivHomotopyHom (M := M) (isLocal_quotient_obj_of_isKInjective hI hI') hb

/-- The identification `derivedHomEquivHomotopyHomOfKInjective` sends a homotopy class
`f : M ⟶ I` to its image in `D(A, d)` composed with the inverse of the given
quasi-isomorphism. -/
@[stacks 0FT8 "the identification is the one of the source and not an arbitrary bijection: it
sends a homotopy class to its image in D(A, d) composed with the inverse of the given
quasi-isomorphism"]
theorem derivedHomEquivHomotopyHomOfKInjective_symm_apply
    {M N I : DifferentialGradedModule.{u, v, w} A}
    (hI : IsKInjective I) (hI' : GradedInjective I) {b : N ⟶ I}
    (hb : QuasiIso b.toHomologicalComplex)
    (f : (HomotopyCategory.quotient A).obj M ⟶ (HomotopyCategory.quotient A).obj I) :
    (derivedHomEquivHomotopyHomOfKInjective (M := M) hI hI' hb).symm f =
      (toDerivedCategory.{u, v, w} A).map f ≫ (toDerivedCategoryIso b hb).inv :=
  derivedHomEquivHomotopyHom_symm_apply (M := M)
    (isLocal_quotient_obj_of_isKInjective hI hI') hb f

/-- A quasi-isomorphism between two graded injective and K-injective right differential graded
modules is an isomorphism of `K(Mod(A, d))`. -/
theorem isIso_quotient_map_of_quasiIso_of_isKInjective
    {I I' : DifferentialGradedModule.{u, v, w} A}
    (hI : IsKInjective I) (hIg : GradedInjective I)
    (hI' : IsKInjective I') (hI'g : GradedInjective I')
    {w : I ⟶ I'} (hw : QuasiIso w.toHomologicalComplex) :
    IsIso ((HomotopyCategory.quotient A).map w) :=
  isIso_quotient_map_of_quasiIso_of_isLocal (isLocal_quotient_obj_of_isKInjective hI hIg)
    (isLocal_quotient_obj_of_isKInjective hI' hI'g) hw

/-- Every functor out of `K(Mod(A, d))` sends a quasi-isomorphism between two graded injective and
K-injective right differential graded modules to an isomorphism. -/
theorem isIso_map_quotient_map_of_quasiIso_of_isKInjective {D : Type*} [Category D]
    (T : HomotopyCategory.{u, v, w} A ⥤ D) {I I' : DifferentialGradedModule.{u, v, w} A}
    (hI : IsKInjective I) (hIg : GradedInjective I)
    (hI' : IsKInjective I') (hI'g : GradedInjective I')
    {w : I ⟶ I'} (hw : QuasiIso w.toHomologicalComplex) :
    IsIso (T.map ((HomotopyCategory.quotient A).map w)) :=
  isIso_map_quotient_map_of_quasiIso_of_isLocal T
    (isLocal_quotient_obj_of_isKInjective hI hIg)
    (isLocal_quotient_obj_of_isKInjective hI' hI'g) hw

end Abelian

end SheafOfModules.DifferentialGradedModule

end
