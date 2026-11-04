module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons

/-!
# The composition comparison of degreewise derived functors, read over `DerivedCategory.Qh`

The degreewise action of an exact functor on unbounded derived categories admits two comparisons
with the localization functors: `CategoryTheory.Functor.mapDerivedCategoryFactors` over
`DerivedCategory.Q`, and `CategoryTheory.Functor.mapDerivedCategoryFactorsh` over
`DerivedCategory.Qh`. The comparison

`Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso :
  (F ⋙ G).mapDerivedCategory ≅ F.mapDerivedCategory ⋙ G.mapDerivedCategory`

is built over `DerivedCategory.Q`, and its value at the image of a cochain complex is
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_inv_app_Q`. A proof that meets it at
an object `DerivedCategory.Qh.obj J` of the derived category coming from the *homotopy* category —
which is where a total left derived functor's defining comparison lives — cannot use that value:
the two comparisons live over different localization functors.

This file supplies the missing companion, over `DerivedCategory.Qh`.

## Main results

* `Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_inv_app_Qh`: the value of the
  composition comparison at `DerivedCategory.Qh.obj J`, in the vocabulary of
  `CategoryTheory.Functor.mapDerivedCategoryFactorsh`.

## Implementation notes

Every object of the homotopy category of cochain complexes is the quotient of the complex
representing it, so the statement at an arbitrary object `J` follows from the statement at
`(HomotopyCategory.quotient _ _).obj J.as`, which is how it is proved here.

The two localization functors are compared only through `DerivedCategory.quotientCompQhIso`, never
through the definition of `DerivedCategory.Qh`: that definition is not exposed, so the fact that
`DerivedCategory.Qh` is the lift of `DerivedCategory.Q` along the quotient functor — hence that the
components of `DerivedCategory.quotientCompQhIso` are identities — is not available. The proof
instead conjugates the statement over `DerivedCategory.Q` by that isomorphism and cancels the two
copies of each of its components, exactly as
`CategoryTheory.Functor.mapDerivedCategoryFactorsh_hom_app` does.

One object of a derived category has several definitionally equal but syntactically distinct
spellings, and a composite whose consecutive factors use different ones is well typed and yet
invisible to the keyed matching of `rw` and `simp`. The cancellation is therefore carried out on a
composite written in a single spelling, and the conjugated factors are only afterwards recognised
as the comparisons over `DerivedCategory.Qh`, by an explicit `congrArg₂` term, which is checked up
to definitional equality and so is indifferent to the spelling.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.DerivedCategoryComparisons

universe w₃ w₂ w₁

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

variable {C₁ : Type*} [Category C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type*} [Category C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {C₃ : Type*} [Category C₃] [Abelian C₃] [HasDerivedCategory.{w₃} C₃]

/-- At the image of a cochain complex under `HomotopyCategory.quotient`, the comparison of the
degreewise action of an exact functor with `DerivedCategory.Qh` is its comparison with
`DerivedCategory.Q`, read through the identification `DerivedCategory.quotientCompQhIso`. This is
`CategoryTheory.Functor.mapDerivedCategoryFactorsh_hom_app` with its last factor — the
localization of a component of `CategoryTheory.Functor.mapHomotopyCategoryFactors`, which is an
identity — removed. -/
private lemma factorsh_hom_app_quotient_obj (F : C₁ ⥤ C₂) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (K : CochainComplex C₁ ℤ) :
    F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C₁).hom.app K) ≫
        F.mapDerivedCategoryFactors.hom.app K ≫
          (DerivedCategory.quotientCompQhIso C₂).inv.app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
      F.mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj K) := by
  have hid : DerivedCategory.Qh.map
      ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K) = 𝟙 _ :=
    (congrArg DerivedCategory.Qh.map
      (CategoryTheory.Quotient.lift.isLift_inv _ _ _ K)).trans (DerivedCategory.Qh.map_id _)
  refine Eq.trans ?_ (F.mapDerivedCategoryFactorsh_hom_app K).symm
  exact congrArg (F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C₁).hom.app K) ≫ ·)
    (congrArg (F.mapDerivedCategoryFactors.hom.app K ≫ ·)
      ((Category.comp_id _).symm.trans
        (congrArg ((DerivedCategory.quotientCompQhIso C₂).inv.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫ ·) hid.symm)))

/-- The inverse half of `factorsh_hom_app_quotient_obj`: the inverse of a composite of
isomorphisms is the composite of the inverses in the opposite order. -/
private lemma factorsh_inv_app_quotient_obj (F : C₁ ⥤ C₂) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (K : CochainComplex C₁ ℤ) :
    (DerivedCategory.quotientCompQhIso C₂).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        F.mapDerivedCategoryFactors.inv.app K ≫
          F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C₁).inv.app K) =
      F.mapDerivedCategoryFactorsh.inv.app
        ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj K) :=
  (Category.assoc _ _ _).symm.trans (congrArg Iso.inv
    (Iso.ext (α := F.mapDerivedCategory.mapIso ((DerivedCategory.quotientCompQhIso C₁).app K) ≪≫
        F.mapDerivedCategoryFactors.app K ≪≫
          ((DerivedCategory.quotientCompQhIso C₂).app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).symm)
      (β := F.mapDerivedCategoryFactorsh.app _)
      (factorsh_hom_app_quotient_obj F K)))

variable (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (G : C₂ ⥤ C₃) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- The value of the composition comparison at the image under `DerivedCategory.Qh` of the
quotient of a cochain complex: `mapDerivedCategoryCompIso_inv_app_Q` conjugated by
`DerivedCategory.quotientCompQhIso`, with the three conjugated factors recognised as the
comparisons over `DerivedCategory.Qh`. -/
private lemma mapDerivedCategoryCompIso_inv_app_Qh_quotient_obj (K : CochainComplex C₁ ℤ) :
    (mapDerivedCategoryCompIso F G).inv.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj K)) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app
          ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj K)) ≫
        G.mapDerivedCategoryFactorsh.hom.app
            ((HomotopyCategory.quotient C₂ (ComplexShape.up ℤ)).obj
              ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
          (F ⋙ G).mapDerivedCategoryFactorsh.inv.app
            ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj K) := by
  have hL : (mapDerivedCategoryCompIso F G).inv.app
        ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).obj K) =
      G.mapDerivedCategory.map (F.mapDerivedCategory.map
          ((DerivedCategory.quotientCompQhIso C₁).hom.app K)) ≫
        ((mapDerivedCategoryCompIso F G).inv.app (DerivedCategory.Q.obj K) ≫
          (F ⋙ G).mapDerivedCategory.map
            ((DerivedCategory.quotientCompQhIso C₁).inv.app K)) := by
    have nat := (mapDerivedCategoryCompIso F G).inv.naturality
      ((DerivedCategory.quotientCompQhIso C₁).hom.app K)
    simp only [Functor.comp_map] at nat
    rw [← Category.assoc, nat, Category.assoc, ← CategoryTheory.Functor.map_comp,
      Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.comp_id]
  have hExp : (mapDerivedCategoryCompIso F G).inv.app
        ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).obj K) =
      G.mapDerivedCategory.map
          (F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C₁).hom.app K) ≫
            F.mapDerivedCategoryFactors.hom.app K ≫
              (DerivedCategory.quotientCompQhIso C₂).inv.app
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
        (G.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C₂).hom.app
              ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
            G.mapDerivedCategoryFactors.hom.app
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
              (DerivedCategory.quotientCompQhIso C₃).inv.app
                (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
          ((DerivedCategory.quotientCompQhIso C₃).hom.app
                (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
              (F ⋙ G).mapDerivedCategoryFactors.inv.app K ≫
                (F ⋙ G).mapDerivedCategory.map
                  ((DerivedCategory.quotientCompQhIso C₁).inv.app K)) := by
    have hcancel : F.mapDerivedCategoryFactors.hom.app K ≫
        𝟙 (DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) =
        F.mapDerivedCategoryFactors.hom.app K := Category.comp_id _
    refine hL.trans ?_
    rw [mapDerivedCategoryCompIso_inv_app_Q]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, hcancel,
      ← CategoryTheory.Functor.map_comp_assoc]
  exact hExp.trans (congrArg₂ (· ≫ ·)
    (congrArg G.mapDerivedCategory.map (factorsh_hom_app_quotient_obj F K))
    (congrArg₂ (· ≫ ·)
      (factorsh_hom_app_quotient_obj G
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
      (factorsh_inv_app_quotient_obj (F ⋙ G) K)))

/-- **The composition comparison of degreewise derived functors, at an object coming from the
homotopy category.** At `DerivedCategory.Qh.obj J` the inverse of
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso` is assembled from the comparisons of
the degreewise actions of `F`, of `G` and of `F ⋙ G` with `DerivedCategory.Qh`.

This is the form in which the comparison meets a total derived functor, whose defining
factorization is stated at such an object; the form over `DerivedCategory.Q`,
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_inv_app_Q`, cannot be used there. -/
theorem mapDerivedCategoryCompIso_inv_app_Qh
    (J : HomotopyCategory C₁ (ComplexShape.up ℤ)) :
    (mapDerivedCategoryCompIso F G).inv.app (DerivedCategory.Qh.obj J) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app J) ≫
        G.mapDerivedCategoryFactorsh.hom.app
            ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj J) ≫
          (F ⋙ G).mapDerivedCategoryFactorsh.inv.app J :=
  mapDerivedCategoryCompIso_inv_app_Qh_quotient_obj F G J.as

end Stacks.DerivedCategoryComparisons

end
