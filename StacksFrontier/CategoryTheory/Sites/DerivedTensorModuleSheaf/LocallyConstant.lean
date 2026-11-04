module

public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.Constant
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.Slice
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.BoundedComplexes

/-!
# Derived tensor products of locally constant sheaves of finite type

Let `(C, J)` be a site and `Λ` a Noetherian ring. If `F` and `G` are sheaves of `Λ`-modules which
are locally constant of finite type, then every cohomology sheaf `Hⁿ(F ⊗_Λ^L G)` of their derived
tensor product is locally constant of finite type. This is the case of single sheaves of
Stacks 094H.

## Main results

* `Stacks.ModuleSheaf.isConstantFGOver_homology_tensor_single`: over an object on which both
  sheaves are constant on finitely generated modules, so is each cohomology sheaf of their
  derived tensor product.
* `Stacks.ModuleSheaf.isFiniteTypeLocallyConstantModuleSheaf_homology_tensor_single`: the local
  constancy.

## Implementation notes

Over an object `V` trivializing both sheaves, restriction to `C/V` commutes with the cohomology
of the derived tensor product (`Stacks.ModuleSheaf.nonempty_homology_overPullback_tensor_iso`),
and on `C/V` the two sheaves are constant sheaves on finitely generated modules, for which the
cohomology of the derived tensor product is constant on a finitely generated module
(`Stacks.ModuleSheaf.exists_homology_constantSheaf_tensor_iso`). The objects trivializing both
sheaves form a covering sieve, the intersection of the two trivializing sieves.

The derived category of sheaves on the slice site is used only inside the proof, and is the
standard one; the statements concern the derived category of sheaves on `C` given as a parameter.

## References

* [Stacks Project, Tag 094H](https://stacks.math.columbia.edu/tag/094H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Stacks.ConstantSheaf

universe t w v u

namespace Stacks.ModuleSheaf

attribute [local instance] Sheaf.monoidalCategory derivedMonoidal

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {Λ : Type (max u v w)} [CommRing Λ] [IsNoetherianRing Λ]
  [HasDerivedCategory.{t} (Sheaf J (ModuleCat.{max u v w} Λ))]

/-- **Over an object trivializing two sheaves of `Λ`-modules as constant sheaves on finitely
generated modules, every cohomology sheaf of their derived tensor product is constant on a
finitely generated module.** -/
theorem isConstantFGOver_homology_tensor_single {F G : Sheaf J (ModuleCat.{max u v w} Λ)} {V : C}
    (hF : IsConstantFGOver.{v, u, w} J Λ V F) (hG : IsConstantFGOver.{v, u, w} J Λ V G) (n : ℤ) :
    IsConstantFGOver.{v, u, w} J Λ V ((DerivedCategory.homologyFunctor _ n).obj
      ((DerivedCategory.singleFunctor _ 0).obj F ⊗ (DerivedCategory.singleFunctor _ 0).obj G)) := by
  let : HasDerivedCategory.{max (max u v) (max u v w + 1)}
      (Sheaf (J.over V) (ModuleCat.{max u v w} Λ)) := HasDerivedCategory.standard _
  obtain ⟨E, hE, ⟨eF⟩⟩ := hF
  obtain ⟨E', hE', ⟨eG⟩⟩ := hG
  let R := J.overPullback (ModuleCat.{max u v w} Λ) V
  let c := constantSheaf (J.over V) (ModuleCat.{max u v w} Λ)
  obtain ⟨e₁⟩ := nonempty_homology_overPullback_tensor_iso V
    ((DerivedCategory.singleFunctor _ 0).obj F) ((DerivedCategory.singleFunctor _ 0).obj G) 0 n
  let s : ∀ (X : Sheaf J (ModuleCat.{max u v w} Λ)) (Y : ModuleCat.{max u v w} Λ),
      (c.obj Y ≅ R.obj X) →
      (R.mapDerivedCategory.obj ((DerivedCategory.singleFunctor _ 0).obj X) ≅
        DerivedCategory.Q.obj ((c.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj Y))) :=
    fun X Y e => (R.mapDerivedCategorySingleFunctor 0).app X ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso e.symm ≪≫
      (DerivedCategory.singleFunctorIsoCompQ _ 0).app (c.obj Y) ≪≫
      DerivedCategory.Q.mapIso
        ((HomologicalComplex.singleMapHomologicalComplex c (ComplexShape.up ℤ) 0).app Y).symm
  have hsingle : ∀ (Y : ModuleCat.{max u v w} Λ), ModuleCat.isFG Λ Y →
      (∀ k, k ∉ Set.Icc (0 : ℤ) 0 →
        IsZero (((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj Y).X k)) ∧
      ∀ k, ModuleCat.isFG Λ (((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj Y).X k) :=
    fun Y hY => ⟨fun k hk => HomologicalComplex.isZero_single_obj_X _ _ _ _
      (by simp only [Set.mem_Icc] at hk; omega), fun k => by
        by_cases hk : k = 0
        · subst hk
          have : Module.Finite Λ Y := (ModuleCat.isFG_iff _).1 hY
          exact (ModuleCat.isFG_iff _).2 (Module.Finite.equiv
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Y).symm.toLinearEquiv)
        · exact isFG_of_isZero Λ (HomologicalComplex.isZero_single_obj_X _ _ _ _ hk)⟩
  obtain ⟨E'', hE'', ⟨e₂⟩⟩ := exists_homology_constantSheaf_tensor_iso.{max u v w, v, max u v}
    (J := J.over V) _ _ 0 0 0 0 (hsingle E hE).1 (hsingle E hE).2 (hsingle E' hE').1
      (hsingle E' hE').2 n
  exact ⟨E'', hE'', ⟨e₂.symm ≪≫ (DerivedCategory.homologyFunctor _ n).mapIso
    (s F E eF ⊗ᵢ s G E' eG).symm ≪≫ e₁.symm⟩⟩

/-- **Stacks 094H for single sheaves.** If `F` and `G` are sheaves of `Λ`-modules, `Λ` Noetherian,
which are locally constant of finite type, then every cohomology sheaf of `F ⊗_Λ^L G` is locally
constant of finite type. -/
theorem isFiniteTypeLocallyConstantModuleSheaf_homology_tensor_single
    {F G : Sheaf J (ModuleCat.{max u v w} Λ)}
    (hF : IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ F)
    (hG : IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ G) (n : ℤ) :
    IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ ((DerivedCategory.homologyFunctor _ n).obj
      ((DerivedCategory.singleFunctor _ 0).obj F ⊗ (DerivedCategory.singleFunctor _ 0).obj G)) := by
  rw [isFiniteTypeLocallyConstantModuleSheaf_iff_trivSieve_mem] at hF hG ⊢
  intro U
  refine J.superset_covering ?_ (J.intersection_covering (hF U) (hG U))
  intro Y g hg
  exact isConstantFGOver_homology_tensor_single hg.1 hg.2 n

end Stacks.ModuleSheaf
