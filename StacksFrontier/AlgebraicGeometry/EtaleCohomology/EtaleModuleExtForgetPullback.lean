module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalarsCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import StacksFrontier.CategoryTheory.Abelian.ExtMapFunctorial
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapCohomologyExt
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ConstantSheafInverseImage

/-!
# `Ext` of sheaves of modules out of the constant sheaf, read through the forgetful functor

Let `X` be a scheme and `Λ` a commutative ring. For a sheaf `M` of `Λ`-modules on the small
étale site of `X`, the forgetful functor `U` to abelian sheaves is exact, so it acts on `Ext`
classes, and the constant sheaf `ℤ_X` maps to `U Λ_X` by `1 ↦ 1`. Together they give

`Ext^i_Λ(Λ_X, M) ⟶ Ext^i(ℤ_X, U M) = Hⁱ(X, U M)`, `a ↦ c ∘ U(a)`,

the étale cohomology of `M` computed in sheaves of `Λ`-modules mapped to Mathlib's sheaf
cohomology `CategoryTheory.Sheaf.H` of the underlying abelian sheaf. This file proves it is
bijective (`Stacks.EtaleCohomology.extForgetSheafH_bijective`).

`Stacks.EtaleCohomology.extConstantAddEquivSheafH` is also a bijection between these groups,
but it is built from right derived functors. The map here is built from operations on `Ext`
classes only (an exact functor, composition with a morphism), so it commutes with every other
such operation. That is what the pullback compatibility of the next section needs.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleUnderlyingAbelianConstantMap`: `ℤ_X ⟶ U Λ_X`.
* `Stacks.EtaleCohomology.extForgetSheafH`: `Ext^i_Λ(Λ_X, M) →+ Hⁱ(X, U M)`.
* `Stacks.EtaleCohomology.extForgetSheafHAddEquiv`: the same map as an additive equivalence.

## Main results

* `Stacks.EtaleCohomology.extForgetSheafH_bijective`: the map is bijective. In degree zero both
  sides are the global sections of `M` (constant sheaf adjunction). In positive degree this is
  dimension shifting along an injective presentation `M ↪ I ↠ C`: the map commutes with the
  connecting morphisms, because `U` is exact, and `Hⁱ(X, U I) = 0` for `i > 0`, because
  `extConstantAddEquivSheafH` identifies it with `Ext^i_Λ(Λ_X, I) = 0`.

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

section Forget

variable (Λ : Type) [CommRing Λ] (X : Scheme.{u})

/-- Sheafification of presheaves of `Λ`-modules on the small étale site commutes with passing
to the underlying abelian presheaves. -/
local instance : X.smallEtaleTopology.PreservesSheafification
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
  ModuleSheaf.preservesSheafification_forget₂.{u + 1} Λ X.smallEtaleTopology

/-- The forgetful functor from sheaves of `Λ`-modules to abelian sheaves is additive. -/
instance etaleModuleUnderlyingAbelian_additive : (etaleModuleUnderlyingAbelian X Λ).Additive :=
  ⟨fun {_ _ _ _} => by
    ext U : 3
    exact (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map_add⟩

/-- The forgetful functor to abelian sheaves preserves finite limits: it is restriction of
scalars to `ℤ` followed by the identification of sheaves of `ℤ`-modules with abelian
sheaves. -/
instance etaleModuleUnderlyingAbelian_preservesFiniteLimits :
    PreservesFiniteLimits (etaleModuleUnderlyingAbelian X Λ) :=
  inferInstanceAs (PreservesFiniteLimits
    (etaleModuleRestrictScalars (Int.castRingHom Λ) X ⋙ etaleModuleUnderlyingAbelian X ℤ))

/-- The forgetful functor to abelian sheaves preserves finite colimits. -/
instance etaleModuleUnderlyingAbelian_preservesFiniteColimits :
    PreservesFiniteColimits (etaleModuleUnderlyingAbelian X Λ) :=
  inferInstanceAs (PreservesFiniteColimits
    (etaleModuleRestrictScalars (Int.castRingHom Λ) X ⋙ etaleModuleUnderlyingAbelian X ℤ))

/-- The additive map `ℤ ⟶ Λ`, `n ↦ n • 1`, between the lifted rings. -/
def uliftIntToULiftHom :
    AddCommGrpCat.of (ULift.{u + 1} ℤ) ⟶
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj
        (ModuleCat.of Λ (ULift.{u + 1} Λ)) :=
  AddCommGrpCat.ofHom ((zmultiplesHom (ULift.{u + 1} Λ) 1).comp
    AddEquiv.ulift.toAddMonoidHom)

/-- **The map `ℤ_X ⟶ U Λ_X`**, `1 ↦ 1`, from the constant abelian sheaf on `ℤ` to the abelian
sheaf underlying the constant sheaf of `Λ`-modules. -/
def etaleModuleUnderlyingAbelianConstantMap :
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶
      (etaleModuleUnderlyingAbelian X Λ).obj
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology) :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map (uliftIntToULiftHom Λ) ≫
    (Stacks.ModuleCatLift.constantSheafForget₂Iso.{u + 1} Λ X.smallEtaleTopology).inv.app
      (ModuleCat.of Λ (ULift.{u + 1} Λ))

/-- The constant sheaf adjunction for sheaves of `Λ`-modules, at a final object `T`. -/
abbrev etaleModuleConstantAdj {T : X.Etale} (hT : IsTerminal T) :=
  constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ) hT

/-- The constant sheaf adjunction for abelian sheaves, at a final object `T`. -/
abbrev etaleAbelianConstantAdj {T : X.Etale} (hT : IsTerminal T) :=
  constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1} hT

/-- **The map `ℤ_X ⟶ U Λ_X` followed by `U a`**, for `a : Λ_X ⟶ M`, is adjoint to the composite
of `ℤ ⟶ Λ` with the section `Λ ⟶ M(T)` adjoint to `a`, over any final object `T` of the site. -/
theorem etaleModuleUnderlyingAbelianConstantMap_comp_map {T : X.Etale} (hT : IsTerminal T)
    {M : EtaleModules.{u, 0} Λ X}
    (a : Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology ⟶ M) :
    etaleModuleUnderlyingAbelianConstantMap Λ X ≫ (etaleModuleUnderlyingAbelian X Λ).map a =
      ((etaleAbelianConstantAdj X hT).homEquiv (AddCommGrpCat.of (ULift.{u + 1} ℤ))
        ((etaleModuleUnderlyingAbelian X Λ).obj M)).symm
        (uliftIntToULiftHom Λ ≫ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
          ((etaleModuleConstantAdj Λ X hT).homEquiv _ _ a)) := by
  set ā := (etaleModuleConstantAdj Λ X hT).homEquiv _ _ a
  have ha : ((etaleModuleConstantAdj Λ X hT).homEquiv _ _).symm ā = a :=
    Equiv.symm_apply_apply _ _
  rw [Adjunction.homEquiv_counit] at ha
  have hw := constantSheafAdj_counit_w X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) M hT
  have hn := (Stacks.ModuleCatLift.constantSheafForget₂Iso.{u + 1} Λ
    X.smallEtaleTopology).inv.naturality ā
  rw [Adjunction.homEquiv_counit, ← ha, Functor.map_comp, etaleModuleUnderlyingAbelianConstantMap,
    Category.assoc]
  have e : Stacks.ModuleCatLift.constantSheafForget₂Iso.{u + 1} Λ X.smallEtaleTopology =
      constantCommuteCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) := rfl
  dsimp only [Functor.comp_map] at hn
  rw [e] at hn ⊢
  have key := ((constantCommuteCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).app
      (M.obj.obj (Opposite.op T))).inv_comp_eq.2 hw.symm
  simp only [Iso.app_inv] at key
  refine (congrArg (fun t => (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
    (uliftIntToULiftHom Λ) ≫ t) ((reassoc_of% hn)
      ((etaleModuleUnderlyingAbelian X Λ).map
        ((etaleModuleConstantAdj Λ X hT).counit.app M))).symm).trans ?_
  refine (congrArg (fun t => (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
    (uliftIntToULiftHom Λ) ≫ (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
      ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map ā) ≫ t) key).trans ?_
  exact (Category.assoc _ _ _).symm.trans (congrArg (fun t => t ≫
    (etaleAbelianConstantAdj X hT).counit.app ((etaleModuleUnderlyingAbelian X Λ).obj M))
    ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map_comp _ _).symm)

/-- Composing with `ℤ ⟶ Λ` and forgetting the `Λ`-linear structure is a bijection from linear
maps out of `Λ` to additive maps out of `ℤ`: both are the value at `1`. -/
theorem uliftIntToULiftHom_comp_forget₂_bijective (N : ModuleCat.{u + 1} Λ) :
    Function.Bijective (fun f : ModuleCat.of Λ (ULift.{u + 1} Λ) ⟶ N =>
      uliftIntToULiftHom Λ ≫ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map f) := by
  have key : ∀ (f : ModuleCat.of Λ (ULift.{u + 1} Λ) ⟶ N) (n : ℤ),
      (uliftIntToULiftHom Λ ≫ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map f).hom
        (ULift.up n) = n • f.hom (ULift.up 1) := by
    intro f n
    show f.hom (n • (1 : ULift.{u + 1} Λ)) = _
    rw [map_zsmul]
    rfl
  constructor
  · intro f g h
    apply (Stacks.Cohomology.GlobalSections.moduleULiftHomAddEquiv.{0, u + 1} Λ N).injective
    have h' : uliftIntToULiftHom Λ ≫ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map f =
        uliftIntToULiftHom Λ ≫ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map g := h
    have := key f 1
    rw [h', key g 1, one_zsmul, one_zsmul] at this
    exact this.symm
  · intro g
    refine ⟨(Stacks.Cohomology.GlobalSections.moduleULiftHomAddEquiv.{0, u + 1} Λ N).symm
      (g.hom (ULift.up 1)), ?_⟩
    ext ⟨n⟩
    rw [key]
    show n • (Stacks.Cohomology.GlobalSections.moduleULiftHomAddEquiv.{0, u + 1} Λ N
      ((Stacks.Cohomology.GlobalSections.moduleULiftHomAddEquiv.{0, u + 1} Λ N).symm
        (g.hom (ULift.up 1)))) = g.hom (ULift.up n)
    rw [AddEquiv.apply_symm_apply, ← map_zsmul]
    congr 1
    exact ULift.ext (by simp)

/-- **In degree zero, `a ↦ (ℤ_X ⟶ U Λ_X) ≫ U a` is bijective**: by the constant sheaf
adjunctions both sides are the global sections of `M`. -/
theorem etaleModuleUnderlyingAbelianConstantMap_comp_map_bijective (M : EtaleModules.{u, 0} Λ X) :
    Function.Bijective (fun a : Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ
        X.smallEtaleTopology ⟶ M =>
      etaleModuleUnderlyingAbelianConstantMap Λ X ≫ (etaleModuleUnderlyingAbelian X Λ).map a) := by
  have h : (fun a : Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ
        X.smallEtaleTopology ⟶ M =>
      etaleModuleUnderlyingAbelianConstantMap Λ X ≫ (etaleModuleUnderlyingAbelian X Λ).map a) =
      ((etaleAbelianConstantAdj X terminalIsTerminal).homEquiv
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ((etaleModuleUnderlyingAbelian X Λ).obj M)).symm ∘
      (fun f => uliftIntToULiftHom Λ ≫
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map f) ∘
      ((etaleModuleConstantAdj Λ X terminalIsTerminal).homEquiv _ _) :=
    funext (etaleModuleUnderlyingAbelianConstantMap_comp_map Λ X terminalIsTerminal)
  rw [h]
  exact (Equiv.bijective _).comp
    ((uliftIntToULiftHom_comp_forget₂_bijective Λ _).comp (Equiv.bijective _))

variable [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **`Ext^i_Λ(Λ_X, M) →+ Hⁱ(X, U M)`**: apply the exact forgetful functor `U` to an `Ext` class
and precompose with `ℤ_X ⟶ U Λ_X`. -/
def extForgetSheafH (M : EtaleModules.{u, 0} Λ X) (i : ℕ) :
    Ext.{u + 1} (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology)
        M i →+
      Sheaf.H.{u + 1} ((etaleModuleUnderlyingAbelian X Λ).obj M) i where
  toFun a := (Ext.mk₀ (etaleModuleUnderlyingAbelianConstantMap Λ X)).comp
    (a.mapExactFunctor (etaleModuleUnderlyingAbelian X Λ)) (zero_add i)
  map_zero' := by simp
  map_add' a b := by simp [Ext.mapExactFunctor_add]

/-- The value of `extForgetSheafH` on an `Ext` class `a` is `(ℤ_X ⟶ U Λ_X) ∘ U a`. -/
theorem extForgetSheafH_apply (M : EtaleModules.{u, 0} Λ X) {i : ℕ}
    (a : Ext.{u + 1} (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ
      X.smallEtaleTopology) M i) :
    extForgetSheafH Λ X M i a = (Ext.mk₀ (etaleModuleUnderlyingAbelianConstantMap Λ X)).comp
      (a.mapExactFunctor (etaleModuleUnderlyingAbelian X Λ)) (zero_add i) :=
  rfl

/-- In degree zero the map sends `a : Λ_X ⟶ M` to `(ℤ_X ⟶ U Λ_X) ≫ U a`. -/
theorem extForgetSheafH_mk₀ {M : EtaleModules.{u, 0} Λ X}
    (a : Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology ⟶ M) :
    extForgetSheafH Λ X M 0 (Ext.mk₀ a) =
      Ext.mk₀ (etaleModuleUnderlyingAbelianConstantMap Λ X ≫
        (etaleModuleUnderlyingAbelian X Λ).map a) := by
  rw [extForgetSheafH_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]

/-- The map is natural in `M`. -/
theorem extForgetSheafH_comp_mk₀ {M N : EtaleModules.{u, 0} Λ X} (g : M ⟶ N) {i : ℕ}
    (a : Ext.{u + 1} (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ
      X.smallEtaleTopology) M i) :
    extForgetSheafH Λ X N i (a.comp (Ext.mk₀ g) (add_zero i)) =
      (extForgetSheafH Λ X M i a).comp
        (Ext.mk₀ ((etaleModuleUnderlyingAbelian X Λ).map g)) (add_zero i) := by
  rw [extForgetSheafH_apply, extForgetSheafH_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀, Ext.comp_assoc_of_third_deg_zero]

/-- The map commutes with the connecting morphisms. -/
theorem extForgetSheafH_comp_extClass {S : ShortComplex (EtaleModules.{u, 0} Λ X)}
    (hS : S.ShortExact) {n : ℕ}
    (a : Ext.{u + 1} (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ
      X.smallEtaleTopology) S.X₃ n) :
    extForgetSheafH Λ X S.X₁ (n + 1) (a.comp hS.extClass rfl) =
      (extForgetSheafH Λ X S.X₃ n a).comp
        (hS.map_of_exact (etaleModuleUnderlyingAbelian X Λ)).extClass rfl := by
  rw [extForgetSheafH_apply, extForgetSheafH_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_extClass]
  exact (Ext.comp_assoc _ _ _ (zero_add n) rfl (by lia)).symm

/-- The abelian sheaf underlying an injective sheaf of `Λ`-modules has no higher cohomology. -/
theorem subsingleton_sheafH_underlying_of_injective (I : EtaleModules.{u, 0} Λ X) [Injective I]
    (n : ℕ) : Subsingleton (Sheaf.H.{u + 1} ((etaleModuleUnderlyingAbelian X Λ).obj I) (n + 1)) :=
  have : Subsingleton ((extFunctorObj (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ
      X.smallEtaleTopology) (n + 1)).obj I) :=
    Ext.subsingleton_of_injective.{u + 1} _ I n
  (extConstantAddEquivSheafH X I (n + 1)).symm.injective.subsingleton

attribute [local instance] Ext.subsingleton_of_injective in
/-- **`Ext^i_Λ(Λ_X, M) →+ Hⁱ(X, U M)` is bijective.** -/
theorem extForgetSheafH_bijective (n : ℕ) : ∀ M : EtaleModules.{u, 0} Λ X,
    Function.Bijective (extForgetSheafH Λ X M n) := by
  induction n with
  | zero =>
    intro M
    have h : (extForgetSheafH Λ X M 0 : _ → _) = Ext.mk₀ ∘
        (fun a => etaleModuleUnderlyingAbelianConstantMap Λ X ≫
          (etaleModuleUnderlyingAbelian X Λ).map a) ∘ Ext.homEquiv₀ := by
      funext a
      conv_lhs => rw [← Ext.mk₀_homEquiv₀_apply a]
      exact extForgetSheafH_mk₀ Λ X _
    rw [h]
    exact (Ext.mk₀_bijective _ _).comp
      ((etaleModuleUnderlyingAbelianConstantMap_comp_map_bijective Λ X M).comp
        Ext.homEquiv₀.bijective)
  | succ n hn =>
    intro M
    let S := ShortComplex.mk (Injective.ι M) (cokernel.π (Injective.ι M))
      (cokernel.condition _)
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (Injective.ι M)) }
    have hUS := hS.map_of_exact (etaleModuleUnderlyingAbelian X Λ)
    have : Injective S.X₂ := Injective.injective_under M
    have hinj : Function.Surjective (extForgetSheafH Λ X S.X₂ n) := by
      cases n with
      | zero => exact (hn S.X₂).surjective
      | succ m =>
        have := subsingleton_sheafH_underlying_of_injective Λ X S.X₂ m
        exact fun _ => ⟨0, Subsingleton.elim _ _⟩
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
      (extForgetSheafH Λ X S.X₂ n) (extForgetSheafH Λ X S.X₃ n)
      (extForgetSheafH Λ X S.X₁ (n + 1))
      (AddMonoidHom.ext fun e => (extForgetSheafH_comp_mk₀ Λ X S.g e).symm)
      (AddMonoidHom.ext fun e => (extForgetSheafH_comp_extClass Λ X hS e).symm)
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' _ hS n (n + 1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' _ hUS n (n + 1) rfl))
      hinj (hn S.X₃)
      (fun x₁ ↦ Ext.covariant_sequence_exact₁ _ hS x₁ (by subsingleton) rfl)
      (fun y₁ ↦ by
        have : Subsingleton (Ext.{u + 1} ((constantSheaf X.smallEtaleTopology
            AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
            (S.map (etaleModuleUnderlyingAbelian X Λ)).X₂ (n + 1)) :=
          subsingleton_sheafH_underlying_of_injective Λ X S.X₂ n
        exact Ext.covariant_sequence_exact₁ _ hUS y₁ (Subsingleton.elim _ _) rfl)

/-- **`Ext^i_Λ(Λ_X, M) ≃+ Hⁱ(X, U M)`**, through the forgetful functor. -/
def extForgetSheafHAddEquiv (M : EtaleModules.{u, 0} Λ X) (i : ℕ) :
    Ext.{u + 1} (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology)
        M i ≃+
      Sheaf.H.{u + 1} ((etaleModuleUnderlyingAbelian X Λ).obj M) i :=
  AddEquiv.ofBijective (extForgetSheafH Λ X M i) (extForgetSheafH_bijective Λ X i M)

end Forget

section Pullback

variable (Λ : Type) [CommRing Λ] {X Y : Scheme.{u}} (g : Y ⟶ X)

/-- Postcomposition with the forgetful functor carries sheaves of modules to abelian sheaves. -/
local instance (Z : Scheme.{u}) : Z.smallEtaleTopology.HasSheafCompose
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
  ModuleSheaf.hasSheafCompose_forget₂.{u + 1} Λ Z.smallEtaleTopology

/-- Sheafification commutes with forgetting the module structure. -/
local instance (Z : Scheme.{u}) : Z.smallEtaleTopology.PreservesSheafification
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
  ModuleSheaf.preservesSheafification_forget₂.{u + 1} Λ Z.smallEtaleTopology

/-- **Forgetting the module structure preserves the left Kan extensions defining inverse
image**: the comma categories are filtered (base change of étale schemes is representably
flat), and the forgetful functor preserves filtered colimits. -/
instance preservesLeftKanExtensions_forget₂_smallEtaleBaseChange :
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).PreservesLeftKanExtensions
      (smallEtaleBaseChange g).op := by
  intro P
  have hfil : ∀ V : Y.Etaleᵒᵖ,
      IsFiltered (CostructuredArrow (smallEtaleBaseChange g).op V) := fun V =>
    IsFiltered.of_equivalence (structuredArrowOpEquivalence (smallEtaleBaseChange g) V.unop)
  have : PreservesFilteredColimitsOfSize.{u, u + 1}
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u + 1} _
  infer_instance

/-- **Inverse image commutes with forgetting the module structure**:
`g^{-1}(U M) ≅ U(g^{-1} M)`, the inverse image of abelian sheaves being
`Stacks.EtaleCohomology.etaleAbelianInverseImage`. -/
def etaleModuleUnderlyingAbelianInverseImageIso :
    etaleModuleUnderlyingAbelian X Λ ⋙ etaleAbelianInverseImage.{u, 0} g ≅
      etaleModuleInverseImage.{u, 0} Λ g ⋙ etaleModuleUnderlyingAbelian Y Λ :=
  Functor.isoWhiskerLeft _ (Functor.sheafPullbackConstruction.sheafPullbackIso
      (smallEtaleBaseChange g) AddCommGrpCat.{u + 1} X.smallEtaleTopology
      Y.smallEtaleTopology).symm ≪≫
    asIso (coefficientSheafPullbackTwoSquare (smallEtaleBaseChange g) X.smallEtaleTopology
      Y.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).natTrans

/-- **The comparison matches the units**: `U` applied to the unit of `g^{-1} ⊣ g_*` on modules is
the unit of `g^{-1} ⊣ g_*` on abelian sheaves followed by `g_*` of the comparison. -/
theorem etaleModuleUnderlyingAbelianInverseImageIso_unit (M : EtaleModules.{u, 0} Λ X) :
    (etaleModuleUnderlyingAbelian X Λ).map ((etaleModuleInverseImageAdj.{u, 0} Λ g).unit.app M) =
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (smallEtaleBaseChange g)
          AddCommGrpCat.{u + 1} X.smallEtaleTopology Y.smallEtaleTopology).unit.app
          ((etaleModuleUnderlyingAbelian X Λ).obj M) ≫
        ((smallEtaleBaseChange g).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          X.smallEtaleTopology Y.smallEtaleTopology).map
          ((etaleModuleUnderlyingAbelianInverseImageIso Λ g).hom.app M) := by
  have h1 := coefficientSheafPullbackTwoSquare_unit (smallEtaleBaseChange g) X.smallEtaleTopology
    Y.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) M
  have h2 := Adjunction.unit_leftAdjointUniq_hom_app
    ((smallEtaleBaseChange g).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      X.smallEtaleTopology Y.smallEtaleTopology)
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (smallEtaleBaseChange g)
      AddCommGrpCat.{u + 1} X.smallEtaleTopology Y.smallEtaleTopology)
    ((etaleModuleUnderlyingAbelian X Λ).obj M)
  refine h1.trans ?_
  simp only [etaleModuleUnderlyingAbelianInverseImageIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom, asIso_hom,
    Functor.map_comp, ← h2, Category.assoc]
  simp only [Functor.sheafPullbackConstruction.sheafPullbackIso, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

/-- `Stacks.EtaleCohomology.etaleModuleUnderlyingAbelianInverseImageIso_unit`, for the
inverse image adjunction `Stacks.EtaleCohomology.etaleAbelianInverseImageDirectImageAdj`. -/
theorem etaleModuleUnderlyingAbelianInverseImageIso_unit' (M : EtaleModules.{u, 0} Λ X) :
    (etaleModuleUnderlyingAbelian X Λ).map ((etaleModuleInverseImageAdj.{u, 0} Λ g).unit.app M) =
      (etaleAbelianInverseImageDirectImageAdj.{u, 0} g).unit.app
          ((etaleModuleUnderlyingAbelian X Λ).obj M) ≫
        ((smallEtaleBaseChange g).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          X.smallEtaleTopology Y.smallEtaleTopology).map
          ((etaleModuleUnderlyingAbelianInverseImageIso Λ g).hom.app M) :=
  etaleModuleUnderlyingAbelianInverseImageIso_unit Λ g M

/-- `Stacks.EtaleCohomology.etaleModuleInverseImageConstantIso` is the comparison of the two
left adjoints of the sections over the base change of `X ⟶ X`. -/
theorem etaleModuleInverseImageConstantIso_eq :
    etaleModuleInverseImageConstantIso.{u, 0} Λ g =
      ((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
          (etaleSiteTerminalIsTerminal X)).comp
          (etaleModuleInverseImageAdj.{u, 0} Λ g)).leftAdjointUniq
        (constantSheafAdj Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)
          ((etaleSiteTerminalIsTerminal X).isTerminalObj (smallEtaleBaseChange g))) :=
  rfl

/-- The inverse of the comparison of two left adjoints of `G` is adjoint to the unit of the
first adjunction. -/
private theorem homEquiv_leftAdjointUniq_inv_app {C D : Type*} [Category* C] [Category* D]
    {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) (x : C) :
    adj2.homEquiv _ _ ((adj1.leftAdjointUniq adj2).inv.app x) = adj1.unit.app x := by
  rw [Adjunction.homEquiv_unit, ← Adjunction.unit_leftAdjointUniq_hom_app adj1 adj2,
    Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  simp

/-- **The constant sheaf comparisons for modules and for abelian sheaves agree** under the
forgetful functor and the maps `ℤ ⟶ U Λ`: the map `ℤ_Y ⟶ U Λ_Y ⟶ U g^{-1} Λ_X` is
`ℤ_Y ⟶ g^{-1} ℤ_X ⟶ g^{-1} U Λ_X ⟶ U g^{-1} Λ_X`. -/
theorem etaleModuleUnderlyingAbelianConstantMap_comp_inverseImageConstantIso :
    etaleModuleUnderlyingAbelianConstantMap Λ Y ≫ (etaleModuleUnderlyingAbelian Y Λ).map
        ((etaleModuleInverseImageConstantIso.{u, 0} Λ g).inv.app
          (ModuleCat.of Λ (ULift.{u + 1} Λ))) =
      (etaleAbelianInverseImageConstantIso.{u, 0} g).inv.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ≫
        (etaleAbelianInverseImage.{u, 0} g).map (etaleModuleUnderlyingAbelianConstantMap Λ X) ≫
        (etaleModuleUnderlyingAbelianInverseImageIso Λ g).hom.app
          (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology) := by
  apply ((etaleAbelianConstantAdj Y ((etaleSiteTerminalIsTerminal X).isTerminalObj
    (smallEtaleBaseChange g))).homEquiv _ _).injective
  -- the left side
  have hL := etaleModuleUnderlyingAbelianConstantMap_comp_map Λ Y
    ((etaleSiteTerminalIsTerminal X).isTerminalObj (smallEtaleBaseChange g))
    ((etaleModuleInverseImageConstantIso.{u, 0} Λ g).inv.app (ModuleCat.of Λ (ULift.{u + 1} Λ)))
  have hAmod := homEquiv_leftAdjointUniq_inv_app
    ((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
          (etaleSiteTerminalIsTerminal X)).comp
          (etaleModuleInverseImageAdj.{u, 0} Λ g))
    (constantSheafAdj Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)
          ((etaleSiteTerminalIsTerminal X).isTerminalObj (smallEtaleBaseChange g)))
    (ModuleCat.of Λ (ULift.{u + 1} Λ))
  rw [← etaleModuleInverseImageConstantIso_eq, Adjunction.comp_unit_app] at hAmod
  rw [hL, Equiv.apply_symm_apply]
  have hAab := homEquiv_leftAdjointUniq_inv_app
    ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
          (etaleSiteTerminalIsTerminal X)).comp
          (etaleAbelianInverseImageDirectImageAdj.{u, 0} g))
    (constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u + 1}
          ((etaleSiteTerminalIsTerminal X).isTerminalObj (smallEtaleBaseChange g)))
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  rw [← etaleAbelianInverseImageConstantIso_eq.{u, 0}, Adjunction.comp_unit_app] at hAab
  -- `U` of the unit, read through the constant sheaf adjunction of `X`
  have key := congrArg ((etaleAbelianConstantAdj X (etaleSiteTerminalIsTerminal X)).homEquiv _ _)
    (etaleModuleUnderlyingAbelianConstantMap_comp_map Λ X (etaleSiteTerminalIsTerminal X)
      ((etaleModuleInverseImageAdj.{u, 0} Λ g).unit.app
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology)))
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    etaleModuleUnderlyingAbelianInverseImageIso_unit'] at key
  have nat := (etaleAbelianInverseImageDirectImageAdj.{u, 0} g).unit.naturality
    (etaleModuleUnderlyingAbelianConstantMap Λ X)
  refine (congrArg (fun t => uliftIntToULiftHom Λ ≫
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map t) hAmod).trans ?_
  refine key.symm.trans ?_
  refine Eq.trans ?_ (Adjunction.homEquiv_naturality_right
    (etaleAbelianConstantAdj Y ((etaleSiteTerminalIsTerminal X).isTerminalObj
      (smallEtaleBaseChange g)))
    ((etaleAbelianInverseImageConstantIso.{u, 0} g).inv.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    ((etaleAbelianInverseImage.{u, 0} g).map (etaleModuleUnderlyingAbelianConstantMap Λ X) ≫
      (etaleModuleUnderlyingAbelianInverseImageIso Λ g).hom.app
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology))).symm
  refine Eq.trans ?_ (congrArg (fun t => t ≫ _) hAab.symm)
  refine (congrArg (fun t => (etaleAbelianConstantAdj X (etaleSiteTerminalIsTerminal X)).unit.app
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ≫
    ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (Opposite.op (etaleSiteTerminal X))).map t) ((reassoc_of% nat)
        (((smallEtaleBaseChange g).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          X.smallEtaleTopology Y.smallEtaleTopology).map
          ((etaleModuleUnderlyingAbelianInverseImageIso Λ g).hom.app
            (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ
              X.smallEtaleTopology))))).trans ?_
  simp only [Functor.map_comp]
  rfl

section Restriction

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits comp_preservesFiniteLimits
  comp_preservesFiniteColimits

/-- **Restriction on `Ext` of sheaves of modules along `g : Y ⟶ X`**:
`Ext^i_Λ(Λ_X, M) →+ Ext^i_Λ(Λ_Y, g^{-1} M)`, apply the exact inverse image and precompose with
`Λ_Y ≅ g^{-1} Λ_X`. -/
def etaleModuleExtRestriction (M : EtaleModules.{u, 0} Λ X) (i : ℕ) :
    Ext.{u + 1} (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology)
        M i →+
      Ext.{u + 1} (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ Y.smallEtaleTopology)
        ((etaleModuleInverseImage.{u, 0} Λ g).obj M) i where
  toFun a := (Ext.mk₀ ((etaleModuleInverseImageConstantIso.{u, 0} Λ g).inv.app
    (ModuleCat.of Λ (ULift.{u + 1} Λ)))).comp
      (a.mapExactFunctor (etaleModuleInverseImage.{u, 0} Λ g)) (zero_add i)
  map_zero' := by simp
  map_add' a b := by simp [Ext.mapExactFunctor_add]

/-- The value of `etaleModuleExtRestriction` on an `Ext` class `a` is
`(Λ_Y ≅ g^{-1} Λ_X) ∘ g^{-1} a`. -/
theorem etaleModuleExtRestriction_apply (M : EtaleModules.{u, 0} Λ X) {i : ℕ}
    (a : Ext.{u + 1} (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ
      X.smallEtaleTopology) M i) :
    etaleModuleExtRestriction Λ g M i a = (Ext.mk₀
      ((etaleModuleInverseImageConstantIso.{u, 0} Λ g).inv.app
        (ModuleCat.of Λ (ULift.{u + 1} Λ)))).comp
      (a.mapExactFunctor (etaleModuleInverseImage.{u, 0} Λ g)) (zero_add i) :=
  rfl

private lemma mk₀_comp_mk₀_comp {𝒞 : Type*} [Category* 𝒞] [Abelian 𝒞] [HasExt.{u + 1} 𝒞]
    {A B C D : 𝒞} (f : A ⟶ B) (f' : B ⟶ C) {i : ℕ} (x : Ext.{u + 1} C D i) :
    (Ext.mk₀ f).comp ((Ext.mk₀ f').comp x (zero_add i)) (zero_add i) =
      (Ext.mk₀ (f ≫ f')).comp x (zero_add i) := by
  rw [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero]

/-- Restriction on `Ext` is natural in the sheaf of modules. -/
theorem etaleModuleExtRestriction_comp_mk₀ {M N : EtaleModules.{u, 0} Λ X} (h : M ⟶ N) {i : ℕ}
    (a : Ext.{u + 1} (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ
      X.smallEtaleTopology) M i) :
    etaleModuleExtRestriction Λ g N i (a.comp (Ext.mk₀ h) (add_zero i)) =
      (etaleModuleExtRestriction Λ g M i a).comp
        (Ext.mk₀ ((etaleModuleInverseImage.{u, 0} Λ g).map h)) (add_zero i) := by
  rw [etaleModuleExtRestriction_apply, etaleModuleExtRestriction_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀, Ext.comp_assoc_of_third_deg_zero]

variable [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **Restriction on `Ext` of sheaves of modules is restriction on étale cohomology**: under
`Ext^i_Λ(Λ, -) ≃+ Hⁱ(-, U -)` (`Stacks.EtaleCohomology.extForgetSheafH`) on `X` and on `Y`, the
restriction of `Ext` classes of sheaves of `Λ`-modules along `g : Y ⟶ X` is the restriction map
`Stacks.EtaleCohomology.etaleCohomologyRestrictionMap` of the underlying abelian sheaves,
followed by `g^{-1}(U M) ≅ U(g^{-1} M)`. -/
theorem extForgetSheafH_etaleModuleExtRestriction (M : EtaleModules.{u, 0} Λ X) {i : ℕ}
    (a : Ext.{u + 1} (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ
      X.smallEtaleTopology) M i) :
    extForgetSheafH Λ Y _ i (etaleModuleExtRestriction Λ g M i a) =
      (etaleCohomologyRestrictionMap.{u, 0, u + 1} g ((etaleModuleUnderlyingAbelian X Λ).obj M) i
        (extForgetSheafH Λ X M i a)).comp
        (Ext.mk₀ ((etaleModuleUnderlyingAbelianInverseImageIso Λ g).hom.app M)) (add_zero i) := by
  rw [extForgetSheafH_apply, extForgetSheafH_apply, etaleModuleExtRestriction_apply,
    etaleCohomologyRestrictionMap_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_mk₀, mk₀_comp_mk₀_comp,
    Stacks.ExtFunctorial.mapExactFunctor_comp_functor,
    Stacks.ExtFunctorial.mapExactFunctor_comp_functor, mk₀_comp_mk₀_comp,
    Ext.comp_assoc_of_third_deg_zero,
    ← Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor
      (etaleModuleUnderlyingAbelianInverseImageIso Λ g).hom, mk₀_comp_mk₀_comp,
    etaleModuleUnderlyingAbelianConstantMap_comp_inverseImageConstantIso, Iso.app_inv,
    Category.assoc]

end Restriction

end Pullback

end Stacks.EtaleCohomology

end
