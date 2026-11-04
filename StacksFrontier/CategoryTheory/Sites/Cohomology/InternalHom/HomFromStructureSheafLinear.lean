module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsTargetNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomAdditive
public import StacksFrontier.CategoryTheory.Sites.Modules.GlobalSmulFunctoriality
public import Mathlib.Algebra.Homology.DerivedCategory.Linear

/-!
# `Hom(K, M) = Hom(𝒪, RSheafHom(K, M))`, linearly over the base

Let `(C, 𝒪)` be a ringed site and `A` a commutative ring mapping to the global sections of `𝒪`,
so that `𝒪`-modules and `D(𝒪)` are `A`-linear (`Stacks.SheafOfModules.linearOver`).  Stacks 08JA
identifies `Hom_{D(𝒪)}(K, M)` with the degree-zero global hypercohomology of the derived internal
Hom `RSheafHom(K, M)`, which is `Hom_{D(𝒪)}(𝒪, RSheafHom(K, M))`.  This file records the composite
identification `Hom(K, M) ≃ Hom(𝒪, RSheafHom(K, M))` and shows that it is `A`-linear: both
identifications are natural in `M`, and `RSheafHom(K, -)` carries multiplication by a global
section to multiplication by that section
(`AlgebraicGeometry.RingedSite.derivedSheafHom_map_globalSectionToEnd`).

## Main definitions

* `AlgebraicGeometry.RingedSite.homLinearEquivHomStructureSheafDerivedSheafHom`.

## References

* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.ModuleSections
open scoped IsMulCommutative


namespace DerivedCategory

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
  {R₁ R₂ : Type*} [Ring R₁] [Ring R₂] [Linear R₁ C] [Linear R₂ C]

/-- **Two linear structures that agree on identities of `C` agree on identities of `D(C)`.**  Both
are transported along the localization `Q`, which is linear for each, and every object of `D(C)`
is isomorphic to the class of a complex. -/
theorem smul_id_eq_smul_id_of_forall (r₁ : R₁) (r₂ : R₂) (h : ∀ B : C, r₁ • 𝟙 B = r₂ • 𝟙 B)
    (N : DerivedCategory C) : r₁ • 𝟙 N = r₂ • 𝟙 N := by
  have hB : r₁ • 𝟙 (Q.objPreimage N) = r₂ • 𝟙 (Q.objPreimage N) := by
    ext n
    simp only [HomologicalComplex.smul_f_apply, HomologicalComplex.id_f]
    exact h _
  have hQ : r₁ • 𝟙 (Q.obj (Q.objPreimage N)) = r₂ • 𝟙 (Q.obj (Q.objPreimage N)) := by
    rw [← Q.map_id, ← Functor.Linear.map_smul, ← Functor.Linear.map_smul, hB]
  simpa using (Q.objObjPreimageIso N).inv ≫= hQ =≫ (Q.objObjPreimageIso N).hom

end DerivedCategory

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- **Stacks 08JA, read as morphisms out of the structure sheaf**:
`Hom(K, M) = Hom(𝒪, RSheafHom(K, M))`. -/
def homAddEquivHomStructureSheafDerivedSheafHom
    (K M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (K ⟶ M) ≃+ (derivedStructureSheaf X ⟶ ((derivedSheafHomBifunctor X).obj (op K)).obj M) :=
  (derivedSheafHomGlobalSectionsEquiv X K M).symm.trans
    (derivedStructureSheafGlobalSectionsEquiv X _)

/-- The identification `Hom(K, M) = Hom(𝒪, RSheafHom(K, M))` is natural in `M`. -/
theorem homAddEquivHomStructureSheafDerivedSheafHom_comp
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {M M' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (f : K ⟶ M) (g : M ⟶ M') :
    homAddEquivHomStructureSheafDerivedSheafHom X K M' (f ≫ g) =
      homAddEquivHomStructureSheafDerivedSheafHom X K M f ≫
        ((derivedSheafHomBifunctor X).obj (op K)).map g := by
  have h₁ : (derivedSheafHomGlobalSectionsEquiv X K M').symm (f ≫ g) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections X).map (((derivedSheafHomBifunctor X).obj (op K)).map g))
        ((derivedSheafHomGlobalSectionsEquiv X K M).symm f) := by
    apply (derivedSheafHomGlobalSectionsEquiv X K M').injective
    rw [AddEquiv.apply_symm_apply, derivedSheafHomGlobalSectionsEquiv_naturality_target,
      AddEquiv.apply_symm_apply]
  rw [homAddEquivHomStructureSheafDerivedSheafHom, homAddEquivHomStructureSheafDerivedSheafHom,
    AddEquiv.trans_apply, AddEquiv.trans_apply, h₁]
  exact derivedStructureSheafGlobalSectionsEquiv_naturality X _ _

section Linear

variable {A : Type*} [CommRing A]
  (ψ : A →+* Stacks.Cohomology.SiteModules.GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- **`RSheafHom(K, -)` is `A`-linear**: it carries multiplication by `a ∈ A` to multiplication by
`a`.  This is `AlgebraicGeometry.RingedSite.derivedSheafHom_map_globalSectionToEnd` at the central
endomorphism of the global section `ψ(a)`, read through
`DerivedCategory.smul_id_eq_smul_id_of_forall`. -/
theorem derivedSheafHom_map_smul_id (a : A)
    (K M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    letI := Stacks.SheafOfModules.linearOver.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ψ
    ((derivedSheafHomBifunctor X).obj (op K)).map (a • 𝟙 M) =
      a • 𝟙 (((derivedSheafHomBifunctor X).obj (op K)).obj M) := by
  let := Stacks.SheafOfModules.linearOver.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ψ
  let := linearCatCenterRingSheaf X
  let c := Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    ⟨(ψ a).1, (ψ a).2⟩
  have h : ∀ B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O),
      a • 𝟙 B = c • 𝟙 B := fun B => by
    rw [Stacks.SheafOfModules.linearOver_smul_id]
    rfl
  rw [DerivedCategory.smul_id_eq_smul_id_of_forall a c h M,
    DerivedCategory.smul_id_eq_smul_id_of_forall a c h]
  exact derivedSheafHom_map_globalSectionToEnd X _ K M

/-- **Stacks 08JA, `A`-linearly**: `Hom(K, M) ≃ₗ[A] Hom(𝒪, RSheafHom(K, M))`. -/
def homLinearEquivHomStructureSheafDerivedSheafHom
    (K M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    letI := Stacks.SheafOfModules.linearOver.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ψ
    (K ⟶ M) ≃ₗ[A] (derivedStructureSheaf X ⟶ ((derivedSheafHomBifunctor X).obj (op K)).obj M) :=
  letI := Stacks.SheafOfModules.linearOver.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ψ
  (homAddEquivHomStructureSheafDerivedSheafHom X K M).toLinearEquiv fun a f => by
    rw [show a • f = f ≫ (a • 𝟙 M) by rw [Linear.comp_smul, Category.comp_id],
      homAddEquivHomStructureSheafDerivedSheafHom_comp, derivedSheafHom_map_smul_id,
      Linear.comp_smul, Category.comp_id]

end Linear

end AlgebraicGeometry.RingedSite

end
