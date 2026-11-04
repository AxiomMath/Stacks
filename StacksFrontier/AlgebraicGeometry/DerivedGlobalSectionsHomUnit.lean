module

public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSections
public import StacksFrontier.Algebra.Homology.DerivedCategory.CorepresentedRightDerived

/-!
# Derived global sections of a scheme are a derived `Hom` out of the structure sheaf

Let `A` be a commutative ring and `f : X ⟶ Spec A` a scheme over `A`. The `A`-linear unbounded
derived global sections `RΓ(X, -) : D(𝒪_X) ⥤ D(A)` are a triangulated functor
(`AlgebraicGeometry.derivedGlobalSectionsOver_isTriangulated`), and for every `M ∈ D(𝒪_X)` the
classes in `H⁰(X, M)` are exactly the morphisms `𝒪_X[0] ⟶ M`:
`x ↦ H⁰(RΓ x)(1)` is a bijection `Hom_{D(𝒪_X)}(𝒪_X[0], M) ≃ H⁰(X, M)`.

## Main results

* `AlgebraicGeometry.bijective_derivedGlobalSectionsOver_homToHomology`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- A morphism out of the structure sheaf is determined by, and determines, the image of `1` in
global sections. -/
theorem bijective_unitHom_app_top_one (M : X.Modules) :
    Function.Bijective (fun s : SheafOfModules.unit X.ringCatSheaf ⟶ M =>
      (s.val.app (op ⊤)).hom (1 : X.ringCatSheaf.obj.obj (op ⊤))) := by
  let ev : M.val.sections → M.val.obj (op ⊤) := fun sec => sec.val (op ⊤)
  have hev : Function.Bijective ev := by
    constructor
    · intro s₁ s₂ h
      refine PresheafOfModules.sections_ext _ _ fun V => ?_
      rw [← PresheafOfModules.sections_property s₁ (homOfLE (le_top : V.unop ≤ ⊤)).op,
        ← PresheafOfModules.sections_property s₂ (homOfLE (le_top : V.unop ≤ ⊤)).op]
      exact congrArg _ h
    · intro m
      refine ⟨PresheafOfModules.sectionsMk
        (fun V => M.val.map (homOfLE (le_top : V.unop ≤ ⊤)).op m) (fun V W g => ?_), ?_⟩
      · refine ((ConcreteCategory.comp_apply _ _ m).symm.trans
          (ConcreteCategory.congr_hom (M.val.map_comp _ _).symm m)).trans ?_
        exact congrArg (fun k : op (⊤ : X.Opens) ⟶ W => (ConcreteCategory.hom (M.val.map k)) m)
          (Subsingleton.elim _ _ : (homOfLE (le_top : V.unop ≤ ⊤)).op ≫ g =
            (homOfLE (le_top : W.unop ≤ ⊤)).op)
      · change M.val.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op m = m
        rw [show (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 (op ⊤) from rfl,
          M.val.map_id]
        rfl
  exact hev.comp M.unitHomEquiv.bijective

/-- The morphism `A ⟶ N` of `A`-modules sending `1` to `m`. -/
def _root_.ModuleCat.homOfElement {A : Type u} [CommRing A] (N : ModuleCat.{u} A) (m : N) :
    ModuleCat.of A A ⟶ N :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton A N m)

/-- `ModuleCat.homOfElement N m` sends `a` to `a • m`. -/
@[simp]
theorem _root_.ModuleCat.homOfElement_apply {A : Type u} [CommRing A] (N : ModuleCat.{u} A)
    (m : N) (a : A) : (ModuleCat.homOfElement N m).hom a = a • m :=
  rfl

/-- The element `1 ∈ Γ(X, 𝒪_X)`, as a morphism `A ⟶ Γ(X, 𝒪_X)` of `A`-modules. -/
def globalSectionsOverOne :
    ModuleCat.of A A ⟶ (globalSectionsOver f).obj (SheafOfModules.unit X.ringCatSheaf) :=
  ModuleCat.homOfElement ((globalSectionsOver f).obj (SheafOfModules.unit X.ringCatSheaf))
    (1 : X.ringCatSheaf.obj.obj (op ⊤))

/-- `s ↦ 1 ≫ Γ(s)` is a bijection `Hom(𝒪_X, M) ≃ Hom_A(A, Γ(X, M))`. -/
theorem bijective_globalSectionsOverOne_comp (M : X.Modules) :
    Function.Bijective (fun s : SheafOfModules.unit X.ringCatSheaf ⟶ M =>
      globalSectionsOverOne f ≫ (globalSectionsOver f).map s) := by
  let e : ((globalSectionsOver f).obj M : Type u) ≃
      (ModuleCat.of A A ⟶ (globalSectionsOver f).obj M) :=
    { toFun := fun m => ModuleCat.homOfElement ((globalSectionsOver f).obj M) m
      invFun := fun g => g.hom 1
      left_inv := fun m => one_smul A m
      right_inv := fun g => ModuleCat.hom_ext (LinearMap.ext_ring (one_smul A _)) }
  have heq : (fun s : SheafOfModules.unit X.ringCatSheaf ⟶ M =>
      globalSectionsOverOne f ≫ (globalSectionsOver f).map s) =
      e ∘ (fun s => (s.val.app (op ⊤)).hom (1 : X.ringCatSheaf.obj.obj (op ⊤))) := by
    funext s
    refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
    change ((globalSectionsOver f).map s).hom ((ModuleCat.homOfElement _ _).hom 1) =
      (ModuleCat.homOfElement _ _).hom 1
    exact LinearMap.map_smul ((globalSectionsOver f).map s).hom (1 : A) _
  rw [heq]
  exact e.bijective.comp (bijective_unitHom_app_top_one M)

/-- **`H⁰(X, M) = Hom_{D(𝒪_X)}(𝒪_X[0], M)`.** -/
theorem bijective_derivedGlobalSectionsOver_homToHomology (M : DerivedCategory X.Modules) :
    Function.Bijective (CorepresentedRightDerived.homToHomology (globalSectionsOver f)
      (SheafOfModules.unit X.ringCatSheaf) (globalSectionsOverOne f) (derivedGlobalSectionsOver f)
      (derivedGlobalSectionsOverUnit f) M) :=
  CorepresentedRightDerived.bijective_homToHomology _ _ _ _ _
    (bijective_globalSectionsOverOne_comp f)
    (fun I hI =>
      (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
        (homotopyGlobalSectionsOver f) (Scheme.Modules.exists_quasiIso_isKInjective X)).2
          DerivedCategory.Qh _ (derivedGlobalSectionsOverUnit f) I hI)
    (Scheme.Modules.exists_quasiIso_isKInjective X) M

end AlgebraicGeometry

end
