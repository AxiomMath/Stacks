module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDualGroupsAbelianExt
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.PostcompositionFunctor
public import StacksFrontier.RingTheory.Ext.DerivedHomFinitenessSource
public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.TensorPullbackGlobalSmul

/-!
# The receptacle `V ↦ Ext¹(𝒢₀, 𝒢₀ ⊗ p^*Ṽ)` of the tangent spaces of `Coh_{X/Y}`

Let `x₀ = (Spec k, 𝒢₀)` be an object of `Coh_{X/Y}` over a field `k` (Stacks 08KB), with
`p : X_k ⟶ Spec k`. The proof of Stacks 08W8 identifies the tangent space of `Coh_{X/Y}` at `x₀`
with `Ext¹_{X_k}(𝒢₀, 𝒢₀)`, and in its natural form the value at `k[V]` with
`Ext¹_{X_k}(𝒢₀, 𝒢₀ ⊗ p^*Ṽ)`. This file builds that receptacle as a functor on finite
dimensional `k`-vector spaces,

`V ↦ Ext¹_{X_k}(𝒢₀, 𝒢₀ ⊗ p^*Ṽ)`,

additive and `k`-linear, the scalar `c` acting through the map `c • 𝟙_V`, and proves that its value
at `k` is finite dimensional. The finiteness is the one the source draws from Stacks 0D0T for a
module with proper support; here it comes from part (B) of Stacks 08JR over the field
(`AlgebraicGeometry.Space.CoherentSituation.exists_isPseudoCoherentFrom_extEquiv`): the group is
`Ext¹_k(L, k)` for a pseudo-coherent `L`, which is finite
(`StacksDraft.DerivedHomFiniteness.finite_hom_to_single_shift_of_isPseudoCoherentFrom`).

This is the additive `k`-linear functor `G` of the finite dimensionality criterion
`Deformation.finiteDimensional_artinianTangentSpace_of_natural_injection` for the tangent space
of Stacks 08W8. No declaration here carries a `@[stacks]` attribute.

## Main definitions

* `AlgebraicGeometry.Space.CoherentSituation.tangentCoefficientFunctor`: `V ↦ 𝒢₀ ⊗ p^*Ṽ`.
* `AlgebraicGeometry.Space.CoherentSituation.tangentExtFunctor`: `V ↦ Ext¹(𝒢₀, 𝒢₀ ⊗ p^*Ṽ)`.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.finiteDimensional_tangentExtFunctor_obj_self`: its
  value at `k` is finite dimensional.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

namespace CoherentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (D : CoherentSituation B S hS)
  (x : CoherentObject D) [IsAffine ((BigFppfOver.toScheme B S hS).obj x.T.left)]
  {A : Type u} [CommRing A] (e : A ≃+* D.baseRing x)

/-- **The coefficient functor `M ↦ 𝒢 ⊗ p^*M̃`** on `A`-modules, the coefficients of the groups
`AlgebraicGeometry.Space.CoherentSituation.extGroup`, in the spelling of
`AlgebraicGeometry.Space.CoherentSituation.extCoefficient`. -/
abbrev extCoefficientFunctor :
    ModuleCat.{u} A ⥤ SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS (D.space x.T)) :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.symm).functor ⋙
    representedAffineAssociated B S hS x.T.left ⋙
    (tensorPullbackBifunctor (D.baseProjection x)).obj x.F

/-- The coefficient functor is additive. -/
instance extCoefficientFunctor_additive : (D.extCoefficientFunctor x e).Additive := by
  have h1 : (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.symm).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  have h3 : ((tensorPullbackBifunctor (D.baseProjection x)).obj x.F).Additive := by
    have := Stacks.Cohomology.DerivedPullbackOfToposHom.preservesFiniteColimits_tensorPullback
      (X := smallEtaleRingedTopos B S hS (D.space x.T))
      (Y := smallEtaleRingedTopos B S hS (D.baseSpace x))
      (smallEtaleRingedToposHom B S hS (D.baseProjection x)) x.F
    have : PreservesBinaryBiproducts (Stacks.Cohomology.DerivedPullbackOfToposHom.tensorPullback
        (X := smallEtaleRingedTopos B S hS (D.space x.T))
        (Y := smallEtaleRingedTopos B S hS (D.baseSpace x))
        (smallEtaleRingedToposHom B S hS (D.baseProjection x)) x.F) :=
      preservesBinaryBiproducts_of_preservesBinaryCoproducts _
    exact Functor.additive_of_preservesBinaryBiproducts
      (Stacks.Cohomology.DerivedPullbackOfToposHom.tensorPullback
        (X := smallEtaleRingedTopos B S hS (D.space x.T))
        (Y := smallEtaleRingedTopos B S hS (D.baseSpace x))
        (smallEtaleRingedToposHom B S hS (D.baseProjection x)) x.F)
  have h2 : (representedAffineAssociated B S hS x.T.left).Additive :=
    additive_representedAffineAssociated B S hS _
  have h23 := @Functor.instAdditiveComp _ _ _ _ _ _ (representedAffineAssociated B S hS x.T.left) h2
    _ _ _ ((tensorPullbackBifunctor (D.baseProjection x)).obj x.F) h3
  exact @Functor.instAdditiveComp _ _ _ _ _ _
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.symm).functor h1 _ _ _ _ h23

variable {k : Type u} [Field k] (ek : k ≃+* D.baseRing x)

/-- **The coefficient functor `V ↦ 𝒢 ⊗ p^*Ṽ`** on finite dimensional `k`-vector spaces, in the
category of modules on `X_T`. -/
abbrev tangentCoefficientFunctor :
    FGModuleCat.{u} k ⥤ Modules.{u, u} B S hS (D.space x.T).1 (D.space x.T).2 :=
  ObjectProperty.ι _ ⋙ D.extCoefficientFunctor x ek

/-- The coefficient functor on finite dimensional vector spaces is additive. -/
theorem tangentCoefficientFunctor_additive : (D.tangentCoefficientFunctor x ek).Additive :=
  @Functor.instAdditiveComp _ _ _ _ _ _ (ObjectProperty.ι (ModuleCat.isFG.{u} k))
    ⟨fun {_ _ _ _} ↦ rfl⟩ _ _ _ (D.extCoefficientFunctor x ek)
    (D.extCoefficientFunctor_additive x ek)

section Abelian

attribute [local instance 5000] SheafOfModules.instAbelian

/-- `tangentCoefficientFunctor_additive`, for the preadditive structure of the abelian
category of modules. -/
instance tangentCoefficientFunctor_additive' : (D.tangentCoefficientFunctor x ek).Additive :=
  tangentCoefficientFunctor_additive D x ek

variable [HasExt.{w} (Modules.{u, u} B S hS (D.space x.T).1 (D.space x.T).2)]

/-- **The receptacle `V ↦ Ext¹(𝒢, 𝒢 ⊗ p^*Ṽ)`**, an additive `k`-linear functor on finite
dimensional `k`-vector spaces, the scalar `c` acting by composition with the map of
coefficients induced by `c • 𝟙_V`. -/
abbrev tangentExtFunctor : FGModuleCat.{u} k ⥤ ModuleCat.{w} k :=
  Abelian.Ext.postcompFunctor (R := k) (D.objectModule x) (D.tangentCoefficientFunctor x ek) 1

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj x.T.left)]
  [HasExt.{w} (Modules.{u, u} B S hS (D.space x.T).1 (D.space x.T).2)] in
/-- An `A`-module of rank one, read over the ring of global functions through `e`, is finite. -/
theorem moduleFinite_baseModule_self :
    Module.Finite (D.baseRing x) (D.baseModule x e (ModuleCat.of A A)) := by
  refine Module.Finite.of_surjective
    (LinearMap.toSpanSingleton (D.baseRing x) (D.baseModule x e (ModuleCat.of A A)) (1 : A))
    fun a ↦ ⟨e (show A from a),
      (congrArg (fun r : A ↦ r * (1 : A)) (e.symm_apply_apply (show A from a))).trans
        (mul_one (show A from a))⟩

section Finiteness

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse

/-- Composition with the map of `N[0]` induced by multiplication by `r` is multiplication by
`r`. -/
theorem _root_.CategoryTheory.ShiftedHom.comp_mk₀_singleFunctor_map_smul_id {R : Type u}
    [CommRing R] (L : DerivedCategory (ModuleCat.{u} R)) (N : ModuleCat.{u} R) (r : R) (n : ℤ)
    (y : ShiftedHom L ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N) n) :
    y.comp (ShiftedHom.mk₀ (0 : ℤ) rfl ((DerivedCategory.singleFunctor _ 0).map (r • 𝟙 N)))
      (zero_add n) = r • y := by
  rw [Functor.map_smul, CategoryTheory.Functor.map_id, ShiftedHom.mk₀_smul,
    ShiftedHom.comp_smul, ShiftedHom.comp_mk₀_id]

/-- Restriction of scalars along a ring isomorphism carries multiplication by `a` to
multiplication by its image. -/
theorem _root_.ModuleCat.restrictScalarsEquivalenceOfRingEquiv_symm_map_smul_id {A A' : Type u}
    [CommRing A] [CommRing A'] (e : A ≃+* A') (M : ModuleCat.{u} A) (a : A) :
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.symm).functor.map (a • 𝟙 M) =
      e a • 𝟙 _ := by
  refine ModuleCat.hom_ext (LinearMap.ext fun z ↦ ?_)
  change a • (show M from z) = e.symm (e a) • (show M from z)
  rw [RingEquiv.symm_apply_apply]

variable [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj x.T.left, ⊤)]

/-- The identification of `Ext¹(𝒢, 𝒢 ⊗ p^*k̃)` with `Ext¹_k(L, k)` through part (B) of
Stacks 08JR, for given data of the conclusion of
`AlgebraicGeometry.Space.CoherentSituation.exists_isPseudoCoherentFrom_extEquiv`. -/
def tangentExtShiftedHomEquiv (L : DerivedCategory (ModuleCat.{u} (D.baseRing x)))
    (Ξ : ∀ (N : ModuleCat.{u} (D.baseRing x)) (i : ℤ),
      ShiftedHom L ((DerivedCategory.singleFunctor _ 0).obj N) i ≃+
        ShiftedHom (D.singleObject x) (tensorPullbackComplexDerived (D.baseProjection x)
          (D.singleComplex x)
          ((HomologicalComplex.single (SheafOfModules.{u}
            (ringedToposStructureRingSheaf B S hS (D.baseSpace x))) (ComplexShape.up ℤ) 0).obj
            ((representedAffineAssociated B S hS x.T.left).obj N))) i) :
    Abelian.Ext.{w} (D.objectModule x) (D.extCoefficientModule x ek (ModuleCat.of k k)) 1 ≃+
      ShiftedHom L ((DerivedCategory.singleFunctor _ 0).obj
        (D.baseModule x ek (ModuleCat.of k k))) ((1 : ℕ) : ℤ) :=
  ((D.extGroupAbelianExtEquiv x ek (ModuleCat.of k k) 1).symm.trans
      (D.extGroupEquiv x ek (ModuleCat.of k k) ((1 : ℕ) : ℤ))).trans
    (Ξ (D.baseModule x ek (ModuleCat.of k k)) ((1 : ℕ) : ℤ)).symm

omit [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj x.T.left, ⊤)] in
/-- The identification carries the scalars acting through the coefficients to the scalars of
`Ext¹_k(L, k)`. -/
theorem tangentExtShiftedHomEquiv_smul (L : DerivedCategory (ModuleCat.{u} (D.baseRing x)))
    (Ξ : ∀ (N : ModuleCat.{u} (D.baseRing x)) (i : ℤ),
      ShiftedHom L ((DerivedCategory.singleFunctor _ 0).obj N) i ≃+
        ShiftedHom (D.singleObject x) (tensorPullbackComplexDerived (D.baseProjection x)
          (D.singleComplex x)
          ((HomologicalComplex.single (SheafOfModules.{u}
            (ringedToposStructureRingSheaf B S hS (D.baseSpace x))) (ComplexShape.up ℤ) 0).obj
            ((representedAffineAssociated B S hS x.T.left).obj N))) i)
    (hΞnat : ∀ {N N' : ModuleCat.{u} (D.baseRing x)}
      (g : N ⟶ N') (i : ℤ) (y : ShiftedHom L ((DerivedCategory.singleFunctor _ 0).obj N) i),
      Ξ N' i (y.comp (ShiftedHom.mk₀ (0 : ℤ) rfl
          ((DerivedCategory.singleFunctor _ 0).map g)) (zero_add i)) =
        Ξ N i y ≫ (DerivedCategory.Q.map ((tensorPullbackComplex (D.baseProjection x)
          (D.singleComplex x)).map ((HomologicalComplex.single (SheafOfModules.{u}
            (ringedToposStructureRingSheaf B S hS (D.baseSpace x))) (ComplexShape.up ℤ) 0).map
            ((representedAffineAssociated B S hS x.T.left).map g))))⟦i⟧')
    (r : D.baseRing x)
    (m : Abelian.Ext.{w} (D.objectModule x) (D.extCoefficientModule x ek (ModuleCat.of k k)) 1) :
    D.tangentExtShiftedHomEquiv x ek L Ξ (m.comp (Abelian.Ext.mk₀
        (D.extCoefficientModuleMap x ek (ek.symm r • 𝟙 (ModuleCat.of k k)))) (add_zero 1)) =
      r • D.tangentExtShiftedHomEquiv x ek L Ξ m := by
  let c := (D.extGroupAbelianExtEquiv x ek (ModuleCat.of k k) 1).symm m
  have h1 : (D.extGroupAbelianExtEquiv x ek (ModuleCat.of k k) 1).symm
      (m.comp (Abelian.Ext.mk₀ (D.extCoefficientModuleMap x ek
        (ek.symm r • 𝟙 (ModuleCat.of k k)))) (add_zero 1)) =
      D.extGroupMap x ek (ek.symm r • 𝟙 (ModuleCat.of k k)) ((1 : ℕ) : ℤ) c := by
    apply (D.extGroupAbelianExtEquiv x ek (ModuleCat.of k k) 1).injective
    rw [AddEquiv.apply_symm_apply, extGroupAbelianExtEquiv_extGroupMap, AddEquiv.apply_symm_apply]
  have hg' := ModuleCat.restrictScalarsEquivalenceOfRingEquiv_symm_map_smul_id ek
    (ModuleCat.of k k) (ek.symm r)
  rw [RingEquiv.apply_symm_apply] at hg'
  have h2 : D.extGroupEquiv x ek (ModuleCat.of k k) ((1 : ℕ) : ℤ)
      (D.extGroupMap x ek (ek.symm r • 𝟙 (ModuleCat.of k k)) ((1 : ℕ) : ℤ) c) =
      Ξ (D.baseModule x ek (ModuleCat.of k k)) ((1 : ℕ) : ℤ)
        (r • (Ξ (D.baseModule x ek (ModuleCat.of k k)) ((1 : ℕ) : ℤ)).symm
          (D.extGroupEquiv x ek (ModuleCat.of k k) ((1 : ℕ) : ℤ) c)) := by
    rw [← ShiftedHom.comp_mk₀_singleFunctor_map_smul_id, ← hg', hΞnat, AddEquiv.apply_symm_apply,
      extGroupMap_apply, AddEquiv.apply_symm_apply]
  change (Ξ (D.baseModule x ek (ModuleCat.of k k)) ((1 : ℕ) : ℤ)).symm
      (D.extGroupEquiv x ek (ModuleCat.of k k) ((1 : ℕ) : ℤ)
        ((D.extGroupAbelianExtEquiv x ek (ModuleCat.of k k) 1).symm
          (m.comp (Abelian.Ext.mk₀ (D.extCoefficientModuleMap x ek
            (ek.symm r • 𝟙 (ModuleCat.of k k)))) (add_zero 1)))) =
    r • (Ξ (D.baseModule x ek (ModuleCat.of k k)) ((1 : ℕ) : ℤ)).symm
      (D.extGroupEquiv x ek (ModuleCat.of k k) ((1 : ℕ) : ℤ) c)
  rw [h1, h2, AddEquiv.symm_apply_apply]

/-- **The value at `k` of the receptacle is finite dimensional.** By part (B) of Stacks 08JR
over the field, `Ext¹(𝒢, 𝒢 ⊗ p^*k̃)` is `Ext¹_k(L, k)` for a pseudo-coherent `L`, which is
finite; the identification carries the scalars of the receptacle, which act through the
coefficients, to the scalars of `Ext¹_k(L, k)`. -/
theorem finiteDimensional_tangentExtFunctor_obj_self :
    FiniteDimensional k ((D.tangentExtFunctor x ek).obj (FGModuleCat.of k k)) := by
  have hX := D.exists_isPseudoCoherentFrom_extEquiv x
  have hL : StacksDraft.PseudoCoherence.IsPseudoCoherentFrom hX.choose (-3) := hX.choose_spec.1
  have : Module.Finite (D.baseRing x) (D.baseModule x ek (ModuleCat.of k k)) :=
    D.moduleFinite_baseModule_self x ek
  have hfin : Module.Finite (D.baseRing x)
      (ShiftedHom hX.choose ((DerivedCategory.singleFunctor _ 0).obj
        (D.baseModule x ek (ModuleCat.of k k))) ((1 : ℕ) : ℤ)) :=
    StacksDraft.DerivedHomFiniteness.finite_hom_to_single_shift_of_isPseudoCoherentFrom
      (D.baseModule x ek (ModuleCat.of k k)) hX.choose (-3) ((1 : ℕ) : ℤ) hL (by norm_num)
  exact Module.finite_of_addEquiv_of_forall_exists_smul
    (D.tangentExtShiftedHomEquiv x ek hX.choose hX.choose_spec.2.choose)
    fun r ↦ ⟨ek.symm r, fun m ↦ D.tangentExtShiftedHomEquiv_smul x ek hX.choose
      hX.choose_spec.2.choose hX.choose_spec.2.choose_spec.1 r m⟩

end Finiteness

end Abelian

end CoherentSituation

end AlgebraicGeometry.Space

end
