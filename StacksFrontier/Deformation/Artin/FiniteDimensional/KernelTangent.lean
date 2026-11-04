module

public import StacksFrontier.Deformation.Applications.TwoFibreProductSixTermExact

/-!
# Finite-dimensionality of a tangent space from the kernel of a tangent map

Let `φ : 𝓕 ⟶ 𝓖` be a `1`-morphism of deformation categories over `𝒞_Λ` whose target has a
finite-dimensional tangent space. The tangent space of `𝓕` is then finite-dimensional as soon as
the kernel of the tangent map of `φ` is, and the kernel is finite-dimensional as soon as it
admits a family of maps to an additive `k`-linear functor `E` on finitely generated
`k`-modules, natural in the coordinate module and injective at the rank-one module, with `E` of
finite dimension there.

## Main results

* `Deformation.finiteDimensional_of_natural_on_ker`: the statement for an arbitrary natural
  family of linear maps between additive `k`-linear functors on finitely generated modules.
* `Deformation.finiteDimensional_tangentModuleAt_of_ker`: the statement for the tangent modules
  of deformation categories and the tangent map of a `1`-morphism.
-/

@[expose] public section

namespace Deformation

open CategoryTheory

section Abstract

universe vM z₁ z₂ z₃ w

variable {k : Type w} [Field k]

/-- **A natural family of maps on the kernel of a natural family of linear maps is linear on that
kernel.** Let `τ : F ⟶ G` be a natural family of linear maps between functors on finitely generated
`k`-modules, with `F` additive and `k`-linear, and let `α : F ⟶ E` be a family of maps to an
additive `k`-linear functor `E` which is natural on the kernel of `τ`. Then `α A` restricts to a
`k`-linear map on the kernel of `τ A`. -/
theorem exists_linearMap_ker_of_natural
    (F : FGModuleCat.{vM} k ⥤ ModuleCat.{z₁} k) (G : FGModuleCat.{vM} k ⥤ ModuleCat.{z₂} k)
    (E : FGModuleCat.{vM} k ⥤ ModuleCat.{z₃} k)
    [F.Additive] [F.Linear k] [E.Additive] [E.Linear k]
    (τ : ∀ X, F.obj X →ₗ[k] G.obj X)
    (hτ : ∀ {X Y} (f : X ⟶ Y) (x : F.obj X), τ Y ((F.map f) x) = (G.map f) (τ X x))
    (α : ∀ X, F.obj X → E.obj X)
    (hα : ∀ {X Y} (f : X ⟶ Y) (x : F.obj X), τ X x = 0 →
      α Y ((F.map f) x) = (E.map f) (α X x))
    (A : FGModuleCat.{vM} k) :
    ∃ ψ : LinearMap.ker (τ A) →ₗ[k] E.obj A, ∀ x, ψ x = α A x.1 := by
  let B : FGModuleCat.{vM} k := FGModuleCat.of k (↥A × ↥A)
  let p₁ : B ⟶ A := FGModuleCat.ofHom (LinearMap.fst k ↥A ↥A)
  let p₂ : B ⟶ A := FGModuleCat.ofHom (LinearMap.snd k ↥A ↥A)
  let i₁ : A ⟶ B := FGModuleCat.ofHom (LinearMap.inl k ↥A ↥A)
  let i₂ : A ⟶ B := FGModuleCat.ofHom (LinearMap.inr k ↥A ↥A)
  have hp₁i₁ : i₁ ≫ p₁ = 𝟙 A := by
    apply FGModuleCat.hom_ext; apply LinearMap.ext; intro x; rfl
  have hp₂i₂ : i₂ ≫ p₂ = 𝟙 A := by
    apply FGModuleCat.hom_ext; apply LinearMap.ext; intro x; rfl
  have hp₁i₂ : i₂ ≫ p₁ = 0 := by
    apply FGModuleCat.hom_ext; apply LinearMap.ext; intro x; rfl
  have hp₂i₁ : i₁ ≫ p₂ = 0 := by
    apply FGModuleCat.hom_ext; apply LinearMap.ext; intro x; rfl
  refine ⟨{ toFun := fun x => α A x.1, map_add' := ?_, map_smul' := ?_ }, fun _ => rfl⟩
  · rintro ⟨x, hx⟩ ⟨y, hy⟩
    let z : F.obj B := (F.map i₁) x + (F.map i₂) y
    have hz : τ B z = 0 := by
      change τ B ((F.map i₁) x + (F.map i₂) y) = 0
      rw [map_add, hτ, hτ, LinearMap.mem_ker.1 hx, LinearMap.mem_ker.1 hy, map_zero, map_zero,
        add_zero]
    have h11 : (F.map p₁) ((F.map i₁) x) = x := by
      simpa using congrArg (fun f => f x) (congrArg F.map hp₁i₁)
    have h12 : (F.map p₁) ((F.map i₂) y) = 0 := by
      simpa using congrArg (fun f => f y) (congrArg F.map hp₁i₂)
    have h21 : (F.map p₂) ((F.map i₁) x) = 0 := by
      simpa using congrArg (fun f => f x) (congrArg F.map hp₂i₁)
    have h22 : (F.map p₂) ((F.map i₂) y) = y := by
      simpa using congrArg (fun f => f y) (congrArg F.map hp₂i₂)
    have hF₁ : (F.map p₁) z = x := by
      change (F.map p₁) ((F.map i₁) x + (F.map i₂) y) = x
      rw [map_add, h11, h12, add_zero]
    have hF₂ : (F.map p₂) z = y := by
      change (F.map p₂) ((F.map i₁) x + (F.map i₂) y) = y
      rw [map_add, h21, h22, zero_add]
    have hFadd : (F.map (p₁ + p₂)) z = x + y := by
      rw [F.map_add]
      change (F.map p₁) z + (F.map p₂) z = x + y
      rw [hF₁, hF₂]
    change α A (x + y) = α A x + α A y
    rw [← hFadd, hα _ z hz, E.map_add, ← hF₁, ← hF₂, hα p₁ z hz, hα p₂ z hz]
    rfl
  · rintro r ⟨x, hx⟩
    let f : A ⟶ A := r • (𝟙 A)
    change α A (r • x) = r • α A x
    calc
      _ = α A ((F.map f) x) := by simp [f]
      _ = (E.map f) (α A x) := hα f x hx
      _ = _ := by simp [f]

/-- **Finite-dimensionality from a natural injection of the kernel.** Let `τ : F ⟶ G` be a
natural family of linear maps between additive `k`-linear functors on finitely generated
`k`-modules, and let `α : F ⟶ E` be a family of maps to a third such functor which is natural
on the kernel of `τ` and injective on it at a module `A`. If `G(A)` and `E(A)` are
finite-dimensional, so is `F(A)`. -/
theorem finiteDimensional_of_natural_on_ker
    (F : FGModuleCat.{vM} k ⥤ ModuleCat.{z₁} k) (G : FGModuleCat.{vM} k ⥤ ModuleCat.{z₂} k)
    (E : FGModuleCat.{vM} k ⥤ ModuleCat.{z₃} k)
    [F.Additive] [F.Linear k] [E.Additive] [E.Linear k]
    (τ : ∀ X, F.obj X →ₗ[k] G.obj X)
    (hτ : ∀ {X Y} (f : X ⟶ Y) (x : F.obj X), τ Y ((F.map f) x) = (G.map f) (τ X x))
    (α : ∀ X, F.obj X → E.obj X)
    (hα : ∀ {X Y} (f : X ⟶ Y) (x : F.obj X), τ X x = 0 →
      α Y ((F.map f) x) = (E.map f) (α X x))
    (A : FGModuleCat.{vM} k) [FiniteDimensional k (G.obj A)] [FiniteDimensional k (E.obj A)]
    (hinj : ∀ x y, τ A x = 0 → τ A y = 0 → α A x = α A y → x = y) :
    FiniteDimensional k (F.obj A) := by
  obtain ⟨ψ, hψ⟩ := exists_linearMap_ker_of_natural F G E τ hτ α hα A
  have hψinj : Function.Injective ψ := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    rw [hψ, hψ] at h
    exact Subtype.ext (hinj x y hx hy h)
  have : FiniteDimensional k (LinearMap.ker (τ A)) := FiniteDimensional.of_injective ψ hψinj
  have : FiniteDimensional k (F.obj A ⧸ LinearMap.ker (τ A)) :=
    Module.Finite.equiv (τ A).quotKerEquivRange.symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker (τ A))

end Abstract

/-! ### Tangent modules of deformation categories -/

section TangentModule

universe u v w u₁ v₁ u₂ v₂ z

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, max v w, w} Λ k)}
  {𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, max v w, w} Λ k)}

/-- The tangent map of a `1`-morphism is natural in the coordinate module. -/
theorem tangentMapAt_naturality (h𝓕 : IsDeformationCategory.{u, v, w} 𝓕.p)
    (h𝓖 : IsDeformationCategory.{u, v, w} 𝓖.p) (φ : 𝓕 ⥤ᵇ 𝓖)
    {M N : FGModuleCat.{max v w} k} (f : M ⟶ N) (x : ↥(tangentModuleAt.{u, v, w} 𝓕 h𝓕 M)) :
    tangentMapAt.{u, v, w} h𝓕 h𝓖 φ N
        (((associatedTangentSpaceModuleStructure.{u, v, w} 𝓕 h𝓕.predeformation
          (tangentConditionS2.{u, v, w} h𝓕)).functor.map f) x) =
      ((associatedTangentSpaceModuleStructure.{u, v, w} 𝓖 h𝓖.predeformation
          (tangentConditionS2.{u, v, w} h𝓖)).functor.map f)
        (tangentMapAt.{u, v, w} h𝓕 h𝓖 φ M x) :=
  associatedTangentLiftFun_naturality.{u, v, w} 𝓕 𝓖 h𝓕.predeformation h𝓖.predeformation
    (tangentConditionS2.{u, v, w} h𝓕) (tangentConditionS2.{u, v, w} h𝓖) φ f x

/-- **The functoriality of the tangent module in the coordinate module, on representatives.**
A morphism `x ⟶ y` of the total category lying over `k[f] : k[M] ⟶ k[N]` carries the class of
`x` to the class of `y`. -/
theorem tangentModuleAt_map_tangentClassAt (h𝓕 : IsDeformationCategory.{u, v, w} 𝓕.p)
    {M N : FGModuleCat.{max v w} k} (f : M ⟶ N)
    (x : 𝓕.p.Fiber ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M))
    (y : 𝓕.p.Fiber ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj N)) (a : x.1 ⟶ y.1)
    [𝓕.p.IsHomLift ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).map f) a] :
    ((associatedTangentSpaceModuleStructure.{u, v, w} 𝓕 h𝓕.predeformation
        (tangentConditionS2.{u, v, w} h𝓕)).functor.map f) (tangentClassAt.{u, v, w} 𝓕 h𝓕 M x) =
      tangentClassAt.{u, v, w} 𝓕 h𝓕 N y := by
  refine (Equiv.cast (associatedTangentLift_carrier.{u, v, w} 𝓕 h𝓕.predeformation
    (tangentConditionS2.{u, v, w} h𝓕) N)).injective ?_
  change cast _ _ = cast _ (cast _ _)
  rw [moduleFunctor_map_cast k _ (squareZeroExtensionArtinian.{u, w, max v w} Λ k ⋙
    isomorphismClasses 𝓕 h𝓕.predeformation.cofibered)
    (associatedTangentSpaceModuleStructure.{u, v, w} 𝓕 h𝓕.predeformation
      (tangentConditionS2.{u, v, w} h𝓕)).forget_comp f, tangentClassAt_eq, cast_symm_cancel,
    cast_symm_cancel]
  exact map_classOf 𝓕 h𝓕.predeformation.cofibered _ x y a

/-- **The tangent module of a deformation category is finite-dimensional when the tangent map of
a `1`-morphism out of it has finite-dimensional target and a kernel injecting naturally into an
additive `k`-linear functor of finite dimension.**

The family `α` is asked to be natural, in the coordinate module, only on the kernel of the
tangent map, and injective only on that kernel at the module `A`. -/
theorem finiteDimensional_tangentModuleAt_of_ker (h𝓕 : IsDeformationCategory.{u, v, w} 𝓕.p)
    (h𝓖 : IsDeformationCategory.{u, v, w} 𝓖.p) (φ : 𝓕 ⥤ᵇ 𝓖)
    (E : FGModuleCat.{max v w} k ⥤ ModuleCat.{z} k) [E.Additive] [E.Linear k]
    (α : ∀ M, ↥(tangentModuleAt.{u, v, w} 𝓕 h𝓕 M) → E.obj M)
    (hα : ∀ {M N : FGModuleCat.{max v w} k} (f : M ⟶ N)
      (x : ↥(tangentModuleAt.{u, v, w} 𝓕 h𝓕 M)), tangentMapAt.{u, v, w} h𝓕 h𝓖 φ M x = 0 →
        α N (((associatedTangentSpaceModuleStructure.{u, v, w} 𝓕 h𝓕.predeformation
          (tangentConditionS2.{u, v, w} h𝓕)).functor.map f) x) = (E.map f) (α M x))
    (A : FGModuleCat.{max v w} k)
    [FiniteDimensional k ↥(tangentModuleAt.{u, v, w} 𝓖 h𝓖 A)] [FiniteDimensional k (E.obj A)]
    (hinj : ∀ x y, tangentMapAt.{u, v, w} h𝓕 h𝓖 φ A x = 0 →
      tangentMapAt.{u, v, w} h𝓕 h𝓖 φ A y = 0 → α A x = α A y → x = y) :
    FiniteDimensional k ↥(tangentModuleAt.{u, v, w} 𝓕 h𝓕 A) :=
  finiteDimensional_of_natural_on_ker
    (associatedTangentSpaceModuleStructure.{u, v, w} 𝓕 h𝓕.predeformation
      (tangentConditionS2.{u, v, w} h𝓕)).functor
    (associatedTangentSpaceModuleStructure.{u, v, w} 𝓖 h𝓖.predeformation
      (tangentConditionS2.{u, v, w} h𝓖)).functor
    E (fun M => tangentMapAt.{u, v, w} h𝓕 h𝓖 φ M)
    (fun f x => tangentMapAt_naturality h𝓕 h𝓖 φ f x) α hα A hinj

end TangentModule

end Deformation

end
