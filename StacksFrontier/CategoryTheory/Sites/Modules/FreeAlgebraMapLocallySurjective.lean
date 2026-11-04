module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalPolynomialModel
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangent
public import StacksFrontier.CategoryTheory.Sites.Modules.PolynomialPresheafSections

/-!
# Renaming the variables of a free algebra sheaf along a locally surjective map

Let `A` be a sheaf of commutative rings on a site and let `h : E₁ ⟶ E₂` be a morphism of presheaves
of sets which is locally surjective. Then the induced morphism of free algebra sheaves
`A[E₁] ⟶ A[E₂]` is locally surjective.

Consequently, if `α : E₂ ⟶ B` presents a sheaf of `A`-algebras `B`, that is `A[E₂] ⟶ B` is locally
surjective, then so does `h ≫ α`.

## Main results

* `Stacks.Sites.FreeAlgebra.polynomialUnit_comp_freeAlgebraMap`: on the polynomial model the
  morphism `A[E₁] ⟶ A[E₂]` renames the variables.
* `Stacks.Sites.FreeAlgebra.isLocallySurjective_freeAlgebraMap`: it is locally surjective when
  `h` is.
* `Stacks.Sites.FreeAlgebra.isLocallySurjective_presentation_comp`: refining a presentation along
  a locally surjective map of generators gives a presentation.

## References

* [Stacks Project, Tag 08TU](https://stacks.math.columbia.edu/tag/08TU), the free algebra sheaf.
* [Stacks Project, Tag 08UK](https://stacks.math.columbia.edu/tag/08UK)
-/

@[expose] public section

open CategoryTheory Opposite

universe v u w

namespace Stacks.Sites.FreeAlgebra

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (A : Sheaf J CommRingCat.{w}) {E₁ E₂ : Cᵒᵖ ⥤ Type w} (h : E₁ ⟶ E₂)

/-- On a polynomial section, a locally surjective renaming of the variables is surjective after
restriction to a covering sieve. -/
theorem exists_covering_rename_eq_polynomialPresheaf_map [Presheaf.IsLocallySurjective J h]
    {X : C} (p : (polynomialPresheaf J A E₂).obj (op X)) :
    ∃ T : Sieve X, T ∈ J X ∧ ∀ (Z : C) (g : Z ⟶ X), T g →
      ∃ q : (polynomialPresheaf J A E₁).obj (op Z),
        MvPolynomial.rename (h.app (op Z)) q = (polynomialPresheaf J A E₂).map g.op p := by
  classical
  obtain ⟨s, p₀, rfl⟩ := MvPolynomial.exists_finset_rename p
  refine ⟨s.inf fun e ↦ Presheaf.imageSieve h e,
    Stacks.SheafOfModules.FiniteTypeKernel.finsetInf_mem J _ _
      (fun e _ ↦ Presheaf.imageSieve_mem J h e), fun Z g hg ↦ ?_⟩
  have hlift : ∀ e : s, ∃ e' : E₁.obj (op Z), h.app (op Z) e' = E₂.map g.op e.1 := fun e ↦
    (Finset.inf_le e.2 : s.inf (fun e ↦ Presheaf.imageSieve h e) ≤ Presheaf.imageSieve h e.1) _ hg
  choose ℓ hℓ using hlift
  refine ⟨MvPolynomial.rename ℓ (MvPolynomial.map (A.obj.map g.op).hom p₀), ?_⟩
  have hfun : h.app (op Z) ∘ ℓ = E₂.map g.op ∘ ((↑) : s → E₂.obj (op X)) := funext hℓ
  rw [MvPolynomial.rename_rename, hfun]
  show _ = (MvPolynomial.eval₂Hom (MvPolynomial.C.comp (A.obj.map g.op).hom)
    (fun x ↦ MvPolynomial.X (E₂.map g.op x))) (MvPolynomial.rename (↑) p₀)
  rw [polynomialPresheaf_map_eq_rename_comp_map]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
    MvPolynomial.map_rename, MvPolynomial.rename_rename]

variable [HasWeakSheafify J CommRingCat.{w}]

/-- On the polynomial model, the morphism `A[E₁] ⟶ A[E₂]` induced by `h` renames the
variables along `h`. -/
theorem polynomialUnit_comp_freeAlgebraMap (U : Cᵒᵖ) :
    (polynomialUnit J A E₁).app U ≫
        (Stacks.SheafOfModules.freeAlgebraMap J A E₁ E₂ h).hom.app U =
      CommRingCat.ofHom (MvPolynomial.rename (h.app U)).toRingHom ≫
        (polynomialUnit J A E₂).app U := by
  refine (NatTrans.congr_app (polynomialUnit_comp_desc J A
    (freeAlgebraSheaf J A E₂) E₁ (freeAlgebraSheafCoefficientMap J A E₂)
    (h ≫ freeAlgebraSheafVariable J A E₂)) U).trans ?_
  apply CommRingCat.hom_ext
  apply MvPolynomial.ringHom_ext
  · intro a
    refine (polynomialEvaluation_app_C J A E₁ _ _ _ U a).trans ?_
    show (polynomialUnit J A E₂).app U (MvPolynomial.C a) =
      (polynomialUnit J A E₂).app U (MvPolynomial.rename (h.app U) (MvPolynomial.C a))
    rw [MvPolynomial.rename_C]
  · intro x
    refine (polynomialEvaluation_app_X J A E₁ _ _ _ U x).trans ?_
    show (polynomialUnit J A E₂).app U (MvPolynomial.X (h.app U x)) =
      (polynomialUnit J A E₂).app U (MvPolynomial.rename (h.app U) (MvPolynomial.X x))
    rw [MvPolynomial.rename_X]

/-- The morphism `A[E₁] ⟶ A[E₂]` induced by `h` sends the image of a polynomial `p` to the image of
`p` with its variables renamed along `h`. -/
theorem freeAlgebraMap_app_polynomialUnit (U : Cᵒᵖ) (p : (polynomialPresheaf J A E₁).obj U) :
    (Stacks.SheafOfModules.freeAlgebraMap J A E₁ E₂ h).hom.app U
        ((polynomialUnit J A E₁).app U p) =
      (polynomialUnit J A E₂).app U (MvPolynomial.rename (h.app U) p) :=
  ConcreteCategory.congr_hom (polynomialUnit_comp_freeAlgebraMap J A h U) p

variable [J.WEqualsLocallyBijective CommRingCat.{w}]

/-- **Renaming the variables of a free algebra sheaf along a locally surjective map is locally
surjective.** -/
theorem isLocallySurjective_freeAlgebraMap [Presheaf.IsLocallySurjective J h] :
    Presheaf.IsLocallySurjective J (Stacks.SheafOfModules.freeAlgebraMap J A E₁ E₂ h).hom where
  imageSieve_mem {X} s := by
    refine J.transitive (Presheaf.imageSieve_mem J (polynomialUnit J A E₂) s) _ ?_
    rintro Y f ⟨p, hp⟩
    obtain ⟨T, hT, hlift⟩ := exists_covering_rename_eq_polynomialPresheaf_map J A h p
    refine J.superset_covering ?_ hT
    intro Z g hg
    obtain ⟨q, hq⟩ := hlift Z g hg
    refine ⟨(polynomialUnit J A E₁).app (op Z) q, ?_⟩
    rw [freeAlgebraMap_app_polynomialUnit, hq, NatTrans.naturality_apply (polynomialUnit J A E₂),
      hp, op_comp, Functor.map_comp_apply]

/-- **Refining a presentation along a locally surjective map of generators gives a
presentation.** If `A[E₂] ⟶ B` is locally surjective and `h : E₁ ⟶ E₂` is locally surjective,
then so is the presentation `A[E₁] ⟶ B` attached to `h ≫ α`. -/
theorem isLocallySurjective_presentation_comp (B : Sheaf J CommRingCat.{w}) (a : A ⟶ B)
    (α : E₂ ⟶ underlyingPresheaf J B) [Presheaf.IsLocallySurjective J h]
    [Presheaf.IsLocallySurjective J (Stacks.SheafOfModules.presentation J A B a E₂ α).hom] :
    Presheaf.IsLocallySurjective J
      (Stacks.SheafOfModules.presentation J A B a E₁ (h ≫ α)).hom := by
  have := isLocallySurjective_freeAlgebraMap J A h
  rw [← Stacks.SheafOfModules.freeAlgebraMap_comp_presentation J A E₁ E₂ h B a (h ≫ α) α rfl]
  exact Presheaf.isLocallySurjective_comp J _ _

end Stacks.Sites.FreeAlgebra

end
