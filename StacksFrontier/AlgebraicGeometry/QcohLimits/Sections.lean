module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentBaseChange

/-!
# Sections of a kernel of a morphism of modules on a scheme

Let `X` be a scheme and let `φ : M ⟶ N` be a morphism of `𝒪_X`-modules.  Limits of sheaves of
modules are computed on sections, so for every open `W` the sections `Γ(kernel φ, W)` are the
kernel of the map `φ.app W` on sections. In particular the map on sections induced by
`kernel.ι φ` is injective, and the pair of maps on sections induced by `kernel.ι φ` and `φ` is
exact.

The file also contains the map on sections of a morphism of modules, as a linear map over the
sections of the structure sheaf on an open containing the one in question, and the linear
equivalence onto a kernel provided by an injective linear map which is exact at its target.

## Main results

* `Stacks.AlgebraicGeometry.QcohLimits.injective_app_kernel_ι` and
  `Stacks.AlgebraicGeometry.QcohLimits.exact_app_kernel`: the two facts about sections of a
  kernel described above.
* `Stacks.AlgebraicGeometry.QcohLimits.appₗ` and
  `Stacks.AlgebraicGeometry.QcohLimits.appOfLEₗ`: the map on sections of a morphism of
  `𝒪_X`-modules as a linear map over `Γ(X, U)`, for sections over `U` itself and for sections
  over an open `W ≤ U`.
* `Stacks.AlgebraicGeometry.QcohLimits.kerEquivOfExact`: an injective linear map whose image is
  the kernel of a second map is a linear equivalence onto that kernel.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

noncomputable section

namespace Stacks.AlgebraicGeometry.QcohLimits

variable {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) (W : X.Opens)

/-! ### Sections as a functor preserving finite limits -/

/-- The functor taking an `𝒪_X`-module to its sections over an open `W`. -/
def sectionsFunctor (X : Scheme.{u}) (W : X.Opens) : X.Modules ⥤ AddCommGrpCat.{u} :=
  Scheme.Modules.toPresheaf X ⋙
    (CategoryTheory.evaluation (X.Opens)ᵒᵖ AddCommGrpCat.{u}).obj (op W)

/-- Taking sections over `W` preserves zero morphisms. -/
instance preservesZeroMorphisms_sectionsFunctor :
    (sectionsFunctor X W).PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-- Taking sections over `W` preserves finite limits. -/
instance preservesFiniteLimits_sectionsFunctor : PreservesFiniteLimits (sectionsFunctor X W) := by
  have : PreservesLimitsOfSize.{0, 0}
      ((CategoryTheory.evaluation (X.Opens)ᵒᵖ AddCommGrpCat.{u}).obj (op W)) :=
    preservesLimitsOfSize_shrink _
  exact comp_preservesFiniteLimits _ _

/-! ### Sections of a kernel -/

/-- The sections of `kernel φ` over an open `W`, identified with the kernel of the map on
sections of `φ` over `W`. -/
def kernelSectionsIso : (sectionsFunctor X W).obj (kernel φ) ≅
    AddCommGrpCat.of (AddCommGrpCat.Hom.hom ((sectionsFunctor X W).map φ)).ker :=
  asIso (kernelComparison φ (sectionsFunctor X W)) ≪≫ AddCommGrpCat.kernelIsoKer _

/-- `kernelSectionsIso` followed by the inclusion of the kernel is the map on sections of
`kernel.ι φ`. -/
theorem kernelSectionsIso_hom_comp :
    (kernelSectionsIso φ W).hom ≫ AddCommGrpCat.ofHom
        (AddSubgroup.subtype (AddCommGrpCat.Hom.hom ((sectionsFunctor X W).map φ)).ker) =
      (sectionsFunctor X W).map (kernel.ι φ) := by
  rw [kernelSectionsIso, Iso.trans_hom, Category.assoc,
    AddCommGrpCat.kernelIsoKer_hom_comp_subtype, asIso_hom, kernelComparison_comp_ι]

/-- The underlying section of `M` of the image of `x` under `kernelSectionsIso` is
`(kernel.ι φ).app W x`. -/
theorem kernelSectionsIso_val (x : Γ(kernel φ, W)) :
    (((kernelSectionsIso φ W).hom x).1 : Γ(M, W)) = (kernel.ι φ).app W x :=
  congrFun (congrArg (fun f ↦ (ConcreteCategory.hom f : _ → _))
    (kernelSectionsIso_hom_comp φ W)) x

/-- The map underlying `kernelSectionsIso` is bijective. -/
theorem bijective_kernelSectionsIso :
    Function.Bijective (ConcreteCategory.hom (kernelSectionsIso φ W).hom) :=
  ConcreteCategory.bijective_of_isIso _

/-- The map on sections induced by the inclusion of a kernel is injective. -/
theorem injective_app_kernel_ι : Function.Injective ((kernel.ι φ).app W) := by
  intro x y h
  rw [← kernelSectionsIso_val, ← kernelSectionsIso_val] at h
  exact (bijective_kernelSectionsIso φ W).1 (Subtype.ext h)

/-- **The sections of a kernel are the kernel of the sections.** The maps on sections induced
by the inclusion of `kernel φ` and by `φ` form an exact pair. -/
theorem exact_app_kernel : Function.Exact ((kernel.ι φ).app W) (φ.app W) := fun b ↦ by
  refine ⟨fun hb ↦ ?_, ?_⟩
  · exact ((bijective_kernelSectionsIso φ W).2 ⟨b, hb⟩).imp fun y hy ↦
      (kernelSectionsIso_val φ W y).symm.trans (congrArg Subtype.val hy)
  · rintro ⟨x, rfl⟩
    rw [← kernelSectionsIso_val]
    exact ((kernelSectionsIso φ W).hom x).2

/-! ### Naturality and linearity of the maps on sections -/

/-- The maps on sections of a morphism of `𝒪_X`-modules commute with restriction. -/
theorem app_naturality {W U : X.Opens} (h : W ≤ U) (x : Γ(M, U)) :
    φ.app W (M.presheaf.map (homOfLE h).op x) =
      N.presheaf.map (homOfLE h).op (φ.app U x) :=
  congr($(φ.mapPresheaf.naturality (homOfLE h).op) x)

/-- The map on sections over `U` of a morphism of `𝒪_X`-modules, as a `Γ(X, U)`-linear map. -/
def appₗ (φ : M ⟶ N) (U : X.Opens) : Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) where
  toFun := φ.app U
  map_add' := map_add _
  map_smul' r x := φ.app_smul r x

/-- The map on sections over `W` of a morphism of `𝒪_X`-modules, as a `Γ(X, U)`-linear map for
the module structures obtained by restricting scalars along `Γ(X, U) ⟶ Γ(X, W)`, where
`W ≤ U`. -/
def appOfLEₗ (φ : M ⟶ N) {W U : X.Opens} (h : W ≤ U) :
    letI := QuasicoherentBaseChange.moduleOfLE M h
    letI := QuasicoherentBaseChange.moduleOfLE N h
    Γ(M, W) →ₗ[Γ(X, U)] Γ(N, W) :=
  letI := QuasicoherentBaseChange.moduleOfLE M h
  letI := QuasicoherentBaseChange.moduleOfLE N h
  { toFun := φ.app W
    map_add' := map_add _
    map_smul' r x := φ.app_smul (X.presheaf.map (homOfLE h).op r) x }

/-! ### Linear equivalences onto a kernel -/

/-- An injective linear map whose image is the kernel of a second linear map is a linear
equivalence onto that kernel. -/
def kerEquivOfExact {R A B C : Type u} [CommRing R] [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [Module R A] [Module R B] [Module R C] (ι : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hinj : Function.Injective ι) (hex : Function.Exact ι g) : A ≃ₗ[R] ↥(LinearMap.ker g) :=
  LinearEquiv.ofBijective (ι.codRestrict (LinearMap.ker g) fun c ↦ (hex (ι c)).mpr ⟨c, rfl⟩)
    ⟨fun _ _ h ↦ hinj (congrArg Subtype.val h), fun b ↦ ((hex b.1).mp b.2).imp fun _ ↦ Subtype.ext⟩

end Stacks.AlgebraicGeometry.QcohLimits

end

end
