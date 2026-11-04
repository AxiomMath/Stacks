module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
public import Mathlib.CategoryTheory.Sites.Spaces

/-!
# Monomorphisms and sections of a fibre product of sheaves of modules

Let `R` be a sheaf of rings on a topological space. A morphism of sheaves of `R`-modules is a
monomorphism exactly when it is injective on the sections over every open set, and a section
over an open set lifts along the first projection of a fibre product exactly when its image
under one leg of the defining cospan is also hit by the other leg.

## Main results

* `SheafOfModules.mono_iff_forall_app_injective`: a morphism of sheaves of modules on a space
  is a monomorphism if and only if it is injective on sections over every open set.
* `SheafOfModules.exists_pullback_fst_eq_iff`: the sections of `M ×_P N` over an open set are
  exactly the compatible pairs of sections of `M` and of `N`.

## Implementation notes

Both statements are consequences of the fact that evaluation at an open set preserves limits of
sheaves of modules (`SheafOfModules.evaluationPreservesLimit`). For the fibre product this is
used through `CategoryTheory.Functor.map_isPullback`, which turns the defining square into a
pullback square of modules over the sections of `R`; a section of the module `M` over `U` is
then produced as the image of `1` under a linear map out of the ring of sections, namely
`LinearMap.toSpanSingleton`, which is how the universal property of a limit is made to yield an
element rather than a morphism.

The criterion for being a monomorphism goes through the underlying sheaf of abelian groups,
whose monomorphisms are detected sectionwise, and the identification of the two injectivity
statements is definitional: restricting scalars and forgetting the module structure change
neither the sections nor the function between them.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace SheafOfModules

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}

/-- A morphism of sheaves of modules on a topological space is a monomorphism exactly when it
is injective on the sections over every open set. -/
theorem mono_iff_forall_app_injective {M N : SheafOfModules.{u} R} (φ : M ⟶ N) :
    Mono φ ↔ ∀ U : (Opens X)ᵒᵖ, Function.Injective ((φ.val.app U).hom) := by
  have key : ∀ U : (Opens X)ᵒᵖ,
      Function.Injective (((SheafOfModules.toSheaf R).map φ).hom.app U).hom ↔
        Function.Injective ((φ.val.app U).hom) := fun _ ↦ Iff.rfl
  rw [← (SheafOfModules.toSheaf R).mono_map_iff_mono, Sheaf.Hom.mono_iff_presheaf_mono,
    CategoryTheory.NatTrans.mono_iff_mono_app]
  refine ⟨fun h U ↦ (key U).mp ?_,
    fun h U ↦ ConcreteCategory.mono_of_injective _ ((key U).mpr (h U))⟩
  exact (ConcreteCategory.mono_iff_injective_of_preservesPullback
    (((SheafOfModules.toSheaf R).map φ).hom.app U)).mp (h U)

/-- A section of `M` over an open set `U` is the image under the first projection of a section
of the fibre product `M ×_P N` exactly when its image in `P` is also the image of a section of
`N` over `U`. -/
theorem exists_pullback_fst_eq_iff {M N P : SheafOfModules.{u} R} (f : M ⟶ P) (g : N ⟶ P)
    (U : (Opens X)ᵒᵖ) (a : M.val.obj U) :
    (∃ d : (pullback f g).val.obj U, ((pullback.fst f g).val.app U).hom d = a) ↔
      ∃ b : N.val.obj U, (f.val.app U).hom a = (g.val.app U).hom b := by
  have hpb : IsPullback ((SheafOfModules.evaluation R U).map (pullback.fst f g))
      ((SheafOfModules.evaluation R U).map (pullback.snd f g))
      ((SheafOfModules.evaluation R U).map f) ((SheafOfModules.evaluation R U).map g) :=
    (IsPullback.of_hasPullback f g).map (SheafOfModules.evaluation R U)
  refine ⟨fun ⟨d, hd⟩ ↦ hd ▸ ⟨((pullback.snd f g).val.app U).hom d,
      ConcreteCategory.congr_hom hpb.w d⟩,
    fun ⟨b, hab⟩ ↦ ?_⟩
  have hsq : ModuleCat.ofHom (LinearMap.toSpanSingleton (R.obj.obj U) (M.val.obj U) a) ≫
      (SheafOfModules.evaluation R U).map f =
      ModuleCat.ofHom (LinearMap.toSpanSingleton (R.obj.obj U) (N.val.obj U) b) ≫
        (SheafOfModules.evaluation R U).map g := by
    refine ModuleCat.hom_ext (LinearMap.ext fun r ↦ ?_)
    change (f.val.app U).hom (r • a) = (g.val.app U).hom (r • b)
    rw [map_smul, map_smul, hab]
  exact ⟨(hpb.lift _ _ hsq).hom (1 : R.obj.obj U),
    (ConcreteCategory.congr_hom (hpb.lift_fst _ _ hsq) 1).trans (one_smul _ a)⟩

end SheafOfModules
