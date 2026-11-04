module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Left adjoints out of `A`-modules are determined by their value on `A` and its action

Let `A` be a commutative ring and `Φ : ModuleCat A ⥤ 𝒞` an additive functor to a preadditive
category with a right adjoint `G`. An element `x` of `G(F)` is an `A`-linear map `A ⟶ G(F)`,
hence a morphism `Φ(A) ⟶ F`; through an isomorphism `θ : Φ(A) ≅ U` this identifies `G(F)` with
`U ⟶ F`, the action of `a ∈ A` becoming precomposition with the endomorphism of `U` that
`Φ(a • -)` induces (`CategoryTheory.Adjunction.moduleCatSectionsHomEquiv`).

Consequently two functors `G₁ G₂ : 𝒞 ⥤ ModuleCat A` that both identify `G_i(F)` with `U ⟶ F`,
naturally, additively and with the same action of `A` on `U`, are isomorphic
(`ModuleCat.rightAdjointIsoOfSectionsHomEquiv`), and so are their left adjoints
(`ModuleCat.leftAdjointIsoOfSectionsHomEquiv`). This is how the module `𝒪_X ⊗_A M` is compared
with other functors `M ↦ 𝒪_X ⊗_A M` defined differently: it suffices to compare their values on
`A` together with the action of `A`.

## Main definitions

* `CategoryTheory.Adjunction.moduleCatSectionsHomEquiv`: `G(F) ≃ (U ⟶ F)` for `Φ ⊣ G` and
  `θ : Φ(A) ≅ U`.
* `ModuleCat.rightAdjointIsoOfSectionsHomEquiv`, `ModuleCat.leftAdjointIsoOfSectionsHomEquiv`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u w₁ w₂

variable {A : Type u} [CommRing A] {𝒞 : Type w₁} [Category.{w₂} 𝒞] [Preadditive 𝒞]

namespace CategoryTheory.Adjunction

variable {Φ : ModuleCat.{u} A ⥤ 𝒞} [Φ.Additive] {G : 𝒞 ⥤ ModuleCat.{u} A} (adj : Φ ⊣ G)
  {U : 𝒞} (θ : Φ.obj (ModuleCat.of A A) ≅ U)

/-- The endomorphism of `U ≅ Φ(A)` induced by multiplication by `a` on `A`. -/
def moduleCatUnitAction (a : A) : U ⟶ U :=
  θ.inv ≫ Φ.map (a • 𝟙 _) ≫ θ.hom

/-- The `A`-linear map `A ⟶ M` sending `1` to `x`. -/
def moduleCatSingletonHom {M : ModuleCat.{u} A} (x : M) : ModuleCat.of A A ⟶ M :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton A M x)

/-- `moduleCatSingletonHom x` sends `r` to `r • x`. -/
theorem moduleCatSingletonHom_apply {M : ModuleCat.{u} A} (x : M) (r : A) :
    (moduleCatSingletonHom x).hom r = r • x := rfl

/-- Two `A`-linear maps out of `A` are equal if they agree at `1`. -/
private theorem moduleCatHom_ext_one {M : ModuleCat.{u} A} {f g : ModuleCat.of A A ⟶ M}
    (h : f.hom 1 = g.hom 1) : f = g :=
  ModuleCat.hom_ext (LinearMap.ext_ring h)

/-- **Sections of a right adjoint are morphisms out of `U ≅ Φ(A)`.** -/
def moduleCatSectionsHomEquiv (F : 𝒞) : G.obj F ≃ (U ⟶ F) where
  toFun x := θ.inv ≫ (adj.homEquiv _ _).symm (moduleCatSingletonHom x)
  invFun v := (adj.homEquiv _ _ (θ.hom ≫ v)).hom (1 : A)
  left_inv x := by
    change (adj.homEquiv _ _ (θ.hom ≫ θ.inv ≫ (adj.homEquiv _ _).symm
      (moduleCatSingletonHom x))).hom (1 : A) = x
    rw [Iso.hom_inv_id_assoc, Equiv.apply_symm_apply]
    exact one_smul A x
  right_inv v := by
    change θ.inv ≫ (adj.homEquiv _ _).symm (moduleCatSingletonHom
      ((adj.homEquiv _ _ (θ.hom ≫ v)).hom (1 : A))) = v
    rw [Iso.inv_comp_eq, Equiv.symm_apply_eq]
    refine ModuleCat.hom_ext (LinearMap.ext fun r => ?_)
    change r • (adj.homEquiv _ _ (θ.hom ≫ v)).hom (1 : A) = _
    rw [← LinearMap.map_smul, smul_eq_mul, mul_one]

omit [Preadditive 𝒞] [Φ.Additive] in
/-- The section `x` goes to `θ.inv` followed by the morphism adjoint to
`moduleCatSingletonHom x`. -/
theorem moduleCatSectionsHomEquiv_apply (F : 𝒞) (x : G.obj F) :
    adj.moduleCatSectionsHomEquiv θ F x =
      θ.inv ≫ (adj.homEquiv _ _).symm (moduleCatSingletonHom x) := rfl

omit [Preadditive 𝒞] [Φ.Additive] in
/-- `moduleCatSectionsHomEquiv` is natural in `F`: applying `G(f)` to a section is postcomposing
with `f`. -/
theorem moduleCatSectionsHomEquiv_naturality {F F' : 𝒞} (f : F ⟶ F') (x : G.obj F) :
    adj.moduleCatSectionsHomEquiv θ F' (G.map f x) = adj.moduleCatSectionsHomEquiv θ F x ≫ f := by
  rw [moduleCatSectionsHomEquiv_apply, moduleCatSectionsHomEquiv_apply, Category.assoc,
    ← Adjunction.homEquiv_naturality_right_symm]
  congr 2
  exact moduleCatHom_ext_one (by simp [moduleCatSingletonHom])

/-- `moduleCatSectionsHomEquiv` is additive: a sum of sections goes to the sum of morphisms. -/
theorem moduleCatSectionsHomEquiv_add (F : 𝒞) (x y : G.obj F) :
    adj.moduleCatSectionsHomEquiv θ F (x + y) =
      adj.moduleCatSectionsHomEquiv θ F x + adj.moduleCatSectionsHomEquiv θ F y := by
  rw [moduleCatSectionsHomEquiv_apply, moduleCatSectionsHomEquiv_apply,
    moduleCatSectionsHomEquiv_apply, ← Preadditive.comp_add, ← Adjunction.homAddEquiv_symm_add]
  congr 2
  exact moduleCatHom_ext_one (by simp [moduleCatSingletonHom])

omit [Preadditive 𝒞] [Φ.Additive] in
/-- `moduleCatSectionsHomEquiv` turns the action of `a ∈ A` on sections into precomposition with
`moduleCatUnitAction θ a`. -/
theorem moduleCatSectionsHomEquiv_smul (F : 𝒞) (a : A) (x : G.obj F) :
    adj.moduleCatSectionsHomEquiv θ F (a • x) =
      moduleCatUnitAction θ a ≫ adj.moduleCatSectionsHomEquiv θ F x := by
  rw [moduleCatSectionsHomEquiv_apply, moduleCatSectionsHomEquiv_apply, moduleCatUnitAction,
    Category.assoc, Category.assoc, Iso.hom_inv_id_assoc,
    ← Adjunction.homEquiv_naturality_left_symm]
  congr 2
  exact moduleCatHom_ext_one (by simp [moduleCatSingletonHom])

end CategoryTheory.Adjunction

namespace ModuleCat

variable {G₁ G₂ : 𝒞 ⥤ ModuleCat.{u} A} {U : 𝒞} (μ : A → (U ⟶ U))
  (β₁ : ∀ F, G₁.obj F ≃ (U ⟶ F)) (β₂ : ∀ F, G₂.obj F ≃ (U ⟶ F))
  (h₁ : ∀ {F F' : 𝒞} (f : F ⟶ F') (x : G₁.obj F), β₁ F' (G₁.map f x) = β₁ F x ≫ f)
  (h₂ : ∀ {F F' : 𝒞} (f : F ⟶ F') (x : G₂.obj F), β₂ F' (G₂.map f x) = β₂ F x ≫ f)
  (a₁ : ∀ F (x y : G₁.obj F), β₁ F (x + y) = β₁ F x + β₁ F y)
  (a₂ : ∀ F (x y : G₂.obj F), β₂ F (x + y) = β₂ F x + β₂ F y)
  (s₁ : ∀ F (a : A) (x : G₁.obj F), β₁ F (a • x) = μ a ≫ β₁ F x)
  (s₂ : ∀ F (a : A) (x : G₂.obj F), β₂ F (a • x) = μ a ≫ β₂ F x)

include a₁ a₂ s₁ s₂ in
/-- The `A`-linear equivalence `G₁(F) ≃ G₂(F)` through `U ⟶ F`. -/
def sectionsLinearEquivOfHomEquiv (F : 𝒞) : G₁.obj F ≃ₗ[A] G₂.obj F where
  toFun x := (β₂ F).symm (β₁ F x)
  invFun y := (β₁ F).symm (β₂ F y)
  left_inv x := by simp
  right_inv y := by simp
  map_add' x y := (β₂ F).injective (by simp [a₁, a₂])
  map_smul' a x := (β₂ F).injective (by simp [s₁, s₂])

include h₁ h₂ a₁ a₂ s₁ s₂ in
/-- **Two functors to `A`-modules identified with `U ⟶ -` compatibly with the action of `A` on `U`
are isomorphic.** -/
def rightAdjointIsoOfSectionsHomEquiv : G₁ ≅ G₂ :=
  NatIso.ofComponents (fun F => (sectionsLinearEquivOfHomEquiv μ β₁ β₂ a₁ a₂ s₁ s₂ F).toModuleIso)
    (fun {F F'} f => by
      ext x
      change (β₂ F').symm (β₁ F' (G₁.map f x)) = G₂.map f ((β₂ F).symm (β₁ F x))
      refine (β₂ F').injective ?_
      rw [Equiv.apply_symm_apply, h₂, Equiv.apply_symm_apply, h₁])

include h₁ h₂ a₁ a₂ s₁ s₂ in
/-- **Two left adjoints out of `A`-modules whose right adjoints are identified with `U ⟶ -`
compatibly with the action of `A` on `U` are isomorphic.** -/
def leftAdjointIsoOfSectionsHomEquiv {Φ₁ Φ₂ : ModuleCat.{u} A ⥤ 𝒞} (adj₁ : Φ₁ ⊣ G₁)
    (adj₂ : Φ₂ ⊣ G₂) : Φ₁ ≅ Φ₂ :=
  adj₁.leftAdjointUniq
    (adj₂.ofNatIsoRight (rightAdjointIsoOfSectionsHomEquiv μ β₁ β₂ h₁ h₂ a₁ a₂ s₁ s₂).symm)

end ModuleCat

end
