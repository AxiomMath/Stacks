module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictExact
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.QuasiCoherentExtension

/-!
# The graph kernel away from the open it extends across

Let `j : U ⟶ X` be an open immersion and `φ : G ⟶ j⁻¹F` a monomorphism of modules, so that the
graph kernel `AlgebraicGeometry.graphKernel j F G φ` is a submodule of `F` whose restriction to
`U` is `G`. Over an open `V` of `X` on which `φ` is already an isomorphism, the graph kernel is
*all* of `F`.

## Main results

* `CategoryTheory.Limits.isSplitEpi_map_kernel_ι_comp_fst`: under an additive, finite-limit
  preserving functor sending `ψ` to an isomorphism, the first projection out of the kernel of
  `(η, -ψ) : A ⊞ B ⟶ T` becomes a split epimorphism.
* `AlgebraicGeometry.isIso_of_isIso_app` and `AlgebraicGeometry.isIso_app_of_isIso`: a morphism
  of modules on a scheme is an isomorphism exactly when it is one on sections over every open.
* `AlgebraicGeometry.isIso_restrict_pushforward_map`: a morphism of modules on an open
  subscheme which is an isomorphism on sections over the opens lying in `V` has
  `V`-restricted pushforward an isomorphism.
* `AlgebraicGeometry.graphKernelProjection_restrict_isIso`: the projection of the graph kernel
  to `F` restricts to an isomorphism over any open on which `φ` is an isomorphism.

## References

* [Stacks Project, Tag 01PE](https://stacks.math.columbia.edu/tag/01PE)
* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

universe v₁ v₂ u₁ u₂ u

namespace CategoryTheory.Limits

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] (R : C ⥤ D) [R.Additive] [PreservesFiniteLimits R]

/-- If an additive, finite-limit preserving functor `R` sends `ψ : B ⟶ T` to an isomorphism, then
it sends the first projection out of the kernel of `(η, -ψ) : A ⊞ B ⟶ T` to a split epimorphism.
-/
lemma isSplitEpi_map_kernel_ι_comp_fst {A B T : C} (η : A ⟶ T) (ψ : B ⟶ T)
    [IsIso (R.map ψ)] :
    IsSplitEpi (R.map (kernel.ι (biprod.desc η (-ψ)) ≫ biprod.fst)) := by
  have ht : (R.map (biprod.inl : A ⟶ A ⊞ B) +
      (R.map η ≫ inv (R.map ψ)) ≫ R.map (biprod.inr : B ⟶ A ⊞ B)) ≫
      R.map (biprod.desc η (-ψ)) = 0 := by
    rw [Preadditive.add_comp, Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
      biprod.inl_desc, biprod.inr_desc, Functor.map_neg]
    simp
  have hfst : (R.map (biprod.inl : A ⟶ A ⊞ B) +
      (R.map η ≫ inv (R.map ψ)) ≫ R.map (biprod.inr : B ⟶ A ⊞ B)) ≫
      R.map (biprod.fst : A ⊞ B ⟶ A) = 𝟙 _ := by
    rw [Preadditive.add_comp, Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
    simp
  refine IsSplitEpi.mk ⟨kernel.lift (R.map (biprod.desc η (-ψ))) _ ht ≫
    (PreservesKernel.iso R (biprod.desc η (-ψ))).inv, ?_⟩
  have hcomp : R.map (kernel.ι (biprod.desc η (-ψ))) =
      (PreservesKernel.iso R (biprod.desc η (-ψ))).hom ≫
        kernel.ι (R.map (biprod.desc η (-ψ))) := by
    rw [PreservesKernel.iso_hom, kernelComparison_comp_ι]
  rw [Functor.map_comp, hcomp]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, kernel.lift_ι]
  simpa only [Category.assoc] using hfst

end CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A morphism of modules on a scheme which is bijective on sections over every open is an
isomorphism. -/
lemma isIso_of_isIso_app {X : Scheme.{u}} {M N : X.Modules} (ψ : M ⟶ N)
    (h : ∀ U : X.Opens, IsIso (ψ.app U)) : IsIso ψ := by
  have h2 : IsIso ((Scheme.Modules.toPresheaf X).map ψ) :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun U => h U.unop)
  exact isIso_of_reflects_iso ψ (Scheme.Modules.toPresheaf X)

/-- An isomorphism of modules on a scheme is bijective on sections over every open. -/
lemma isIso_app_of_isIso {X : Scheme.{u}} {M N : X.Modules} (ψ : M ⟶ N) [IsIso ψ]
    (U : X.Opens) : IsIso (ψ.app U) := by
  exact NatIso.isIso_app_of_isIso ((Scheme.Modules.toPresheaf X).map ψ) (.op U)

/-- If a morphism of modules on the open subscheme `Y` is bijective on sections over every open
whose image lies in `V`, then its pushforward to the ambient scheme restricts to an isomorphism
over `V`. -/
lemma isIso_restrict_pushforward_map {X : Scheme.{u}} (Y V : X.Opens)
    {B N : Y.toScheme.Modules} (φ : B ⟶ N)
    (h : ∀ W : Y.toScheme.Opens, Y.ι ''ᵁ W ≤ V → IsIso (φ.app W)) :
    IsIso ((Scheme.Modules.restrictFunctor V.ι).map
      ((Scheme.Modules.pushforward Y.ι).map φ)) :=
  isIso_of_isIso_app _ fun W => h _ ((Y.ι.image_preimage_le _).trans (V.ι_image_le W))

/-- The projection of the graph kernel to `F` is an isomorphism over any open `V` of `X` on which
`φ` has already become an isomorphism after pushforward. -/
lemma graphKernelProjection_restrict_isIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : X.Modules) (G : U.Modules) (φ : G ⟶ (Scheme.Modules.pullback j).obj F) [Mono φ]
    (V : X.Opens)
    [IsIso ((Scheme.Modules.restrictFunctor V.ι).map ((Scheme.Modules.pushforward j).map φ))] :
    IsIso ((Scheme.Modules.restrictFunctor V.ι).map (graphKernelProjection j F G φ)) := by
  have hp : Mono (graphKernelProjection j F G φ) := graphKernelProjection_mono j F G φ
  have hmono : Mono ((Scheme.Modules.restrictFunctor V.ι).map (graphKernelProjection j F G φ)) :=
    CategoryTheory.preserves_mono_of_preservesLimit _ _
  have hsplit : IsSplitEpi ((Scheme.Modules.restrictFunctor V.ι).map
      (graphKernelProjection j F G φ)) :=
    isSplitEpi_map_kernel_ι_comp_fst (Scheme.Modules.restrictFunctor V.ι)
      ((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app F)
      ((Scheme.Modules.pushforward j).map φ)
  exact isIso_of_mono_of_epi _

end AlgebraicGeometry
