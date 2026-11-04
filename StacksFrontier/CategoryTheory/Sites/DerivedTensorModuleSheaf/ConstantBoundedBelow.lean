module

public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.Constant
public import StacksFrontier.Homology.KFlat.BifunctorBoundedBelowFlatCycles

/-!
# Constant sheaves on a bounded below complex of flat modules

Let `Λ` be a commutative ring and `P` a strictly bounded below complex of `Λ`-modules whose
terms and whose cycle modules are flat. Then `P` is K-flat, and for every site `(C, J)` the
complex `P̲` of constant sheaves on its terms is a K-flat complex of sheaves of `Λ`-modules.

Both are instances of `CochainComplex.KFlatBifunctor.kFlat_mapHomologicalComplex_of_isStrictlyGE`:
the constant sheaf functor commutes with colimits, and the constant sheaf on a flat module is the
sheafification of a presheaf of flat modules, hence flat.

Over a ring in which a submodule of a flat module is flat, such as `ℤ`, the hypothesis on the
cycles is automatic.

## Main results

* `Stacks.ModuleSheaf.kFlat_single_of_flat`: a flat module placed in one degree is K-flat.
* `Stacks.ModuleSheaf.kFlat_of_isStrictlyGE_of_flat`: a strictly bounded below complex of
  modules with flat terms and flat cycles is K-flat.
* `Stacks.ModuleSheaf.preservesFiniteLimits_tensorRight_constantSheaf`: the constant sheaf on a
  flat module is flat.
* `Stacks.ModuleSheaf.kFlat_constantSheaf_of_isStrictlyGE_of_flat`: the complex of constant
  sheaves on a strictly bounded below complex with flat terms and flat cycles is K-flat.

## References

* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 06YR](https://stacks.math.columbia.edu/tag/06YR)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CochainComplex.KFlatBifunctor

universe w v u

namespace Stacks.ModuleSheaf

section Modules

variable {Λ : Type w} [CommRing Λ]

/-- An object `M` such that `tensorRight M` is exact is K-flat when placed in a single degree. -/
private theorem kFlat_single_of_exact_tensorRight {A : Type*} [Category A] [Abelian A]
    [MonoidalCategory A] [BraidedCategory A] [(curriedTensor A).Additive]
    [∀ X, ((curriedTensor A).obj X).Additive]
    [∀ K₁ K₂ : CochainComplex A ℤ, K₁.HasMapBifunctor K₂ (curriedTensor A)]
    (M : A) (q : ℤ)
    [PreservesFiniteLimits (tensorRight M)] [PreservesFiniteColimits (tensorRight M)] :
    KFlat (curriedTensor A) ((HomologicalComplex.single _ (ComplexShape.up ℤ) q).obj M) :=
  kFlat_single_of_exact (curriedTensor A) M q
    (fun _ hG => HomologicalComplex.Acyclic.map (tensorRight M) hG)

/-- Sequential colimits of complexes of `Λ`-modules carry acyclic complexes to an acyclic
complex. -/
theorem acyclic_of_isColimit_nat_moduleCat (E : ℕ ⥤ CochainComplex (ModuleCat.{w} Λ) ℤ)
    (s : Cocone E) (hs : IsColimit s) (hE : ∀ i, (E.obj i).Acyclic) : s.pt.Acyclic := by
  have : HasExactColimitsOfShape ℕ (ModuleCat.{w} Λ) := by
    have : AB5OfSize.{0, 0} (ModuleCat.{w} Λ) := AB5OfSize_shrink _
    exact AB5OfSize.ofShape ℕ
  exact fun n => (CochainComplex.KFlat.acyclic_colimit E hE n).of_iso
    ((colimit.isColimit E).coconePointUniqueUpToIso hs)

/-- Tensoring a `Λ`-module with a fixed one commutes with sequential colimits. -/
theorem preservesColimitsOfShape_nat_curriedTensor_moduleCat (X : ModuleCat.{w} Λ) :
    PreservesColimitsOfShape ℕ ((curriedTensor (ModuleCat.{w} Λ)).obj X) :=
  (ihom.adjunction X).leftAdjoint_preservesColimits.preservesColimitsOfShape

/-- **A flat module placed in a single degree is K-flat**: tensoring with it is exact. -/
theorem kFlat_single_of_flat (M : ModuleCat.{w} Λ) [Module.Flat Λ M] (q : ℤ) :
    KFlat (curriedTensor (ModuleCat.{w} Λ))
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) q).obj M) := by
  have : PreservesFiniteColimits (tensorRight M) :=
    have : PreservesColimitsOfSize (tensorLeft M) :=
      (ihom.adjunction M).leftAdjoint_preservesColimits
    preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)
  exact kFlat_single_of_exact_tensorRight M q

/-- **A strictly bounded below complex of `Λ`-modules whose terms and cycles are flat is
K-flat.** -/
theorem kFlat_of_isStrictlyGE_of_flat (P : CochainComplex (ModuleCat.{w} Λ) ℤ) (a : ℤ)
    [P.IsStrictlyGE a] (hterm : ∀ q, Module.Flat Λ (P.X q))
    (hcyc : ∀ q, Module.Flat Λ (P.cycles q)) :
    KFlat (curriedTensor (ModuleCat.{w} Λ)) P :=
  (kFlat_mapHomologicalComplex_of_isStrictlyGE (curriedTensor (ModuleCat.{w} Λ)) (𝟭 _) P a
    preservesColimitsOfShape_nat_curriedTensor_moduleCat acyclic_of_isColimit_nat_moduleCat
    (fun q => by have := hterm q; exact kFlat_single_of_flat (P.X q) q)
    (fun q => by have := hcyc q; exact kFlat_single_of_flat (P.cycles q) q)).of_iso _
    ((Functor.mapHomologicalComplexIdIso _ _).app P)

end Modules

section Site

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory monoidalClosed

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {Λ : Type w} [CommRing Λ] [UnivLE.{max u v, w}]

/-- **The constant sheaf on a flat module is flat**: it is the sheafification of the constant
presheaf, whose values are flat. -/
theorem preservesFiniteLimits_tensorRight_constantSheaf (M : ModuleCat.{w} Λ)
    [Module.Flat Λ M] :
    PreservesFiniteLimits (tensorRight ((constantSheaf J (ModuleCat.{w} Λ)).obj M)) :=
  preservesFiniteLimits_tensorRight_presheafToSheaf_obj J ((Functor.const Cᵒᵖ).obj M)
    (fun _ => inferInstanceAs (Module.Flat Λ M))

/-- The constant sheaf on a flat module, placed in a single degree, is K-flat. -/
theorem kFlat_single_constantSheaf_of_flat (M : ModuleCat.{w} Λ) [Module.Flat Λ M] (q : ℤ) :
    KFlat (curriedTensor (Sheaf J (ModuleCat.{w} Λ)))
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) q).obj
        ((constantSheaf J (ModuleCat.{w} Λ)).obj M)) := by
  have := preservesFiniteLimits_tensorRight_constantSheaf J M
  exact kFlat_single_of_exact_tensorRight _ q

/-- **The complex of constant sheaves on a strictly bounded below complex of `Λ`-modules whose
terms and cycles are flat is K-flat.** -/
theorem kFlat_constantSheaf_of_isStrictlyGE_of_flat (P : CochainComplex (ModuleCat.{w} Λ) ℤ)
    (a : ℤ) [P.IsStrictlyGE a] (hterm : ∀ q, Module.Flat Λ (P.X q))
    (hcyc : ∀ q, Module.Flat Λ (P.cycles q)) :
    KFlat (curriedTensor (Sheaf J (ModuleCat.{w} Λ)))
      (((constantSheaf J (ModuleCat.{w} Λ)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  kFlat_mapHomologicalComplex_of_isStrictlyGE (curriedTensor (Sheaf J (ModuleCat.{w} Λ)))
    (constantSheaf J (ModuleCat.{w} Λ)) P a (fun _ ↦ inferInstance)
    (acyclic_of_isColimit_nat)
    (fun q => by have := hterm q; exact kFlat_single_constantSheaf_of_flat J (P.X q) q)
    (fun q => by have := hcyc q; exact kFlat_single_constantSheaf_of_flat J (P.cycles q) q)

end Site

end Stacks.ModuleSheaf

end
