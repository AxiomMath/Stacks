module

public import StacksFrontier.CategoryTheory.Sites.Point.ConstantSheafFiber
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ConstantTwistComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TraceFormulaDimensionOne
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ShortExactTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.OpenClosedPointReduction
public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.TwoTermTrace
public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.ProjectiveTrace
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleGlobalSectionsUnit
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeUnit

/-!
# The geometric Frobenius acts trivially on the stalks of a constant sheaf

A morphism of points `Φ₁ ⟶ Φ₂` of a site induces a map on fibres `Φ₂^* ⟶ Φ₁^*`. On a constant
presheaf with value `A` both fibres are `A`, through the all-identity colimit cocone, and the
induced map is the identity of `A`. Sheafification does not change fibres, so the same holds
for the constant sheaf. In particular an endomorphism of a point acts as the identity on the
fibre of a constant sheaf.

For the small étale site of a scheme `X` over a finite field `k` and a rational point `x`, the
geometric Frobenius `π_x` of [Stacks, Tag 03SW] is the action of an automorphism of the geometric
point over `x`. It therefore acts as the identity on the stalk of a constant sheaf, and degreewise
on the stalk of a complex of constant sheaves. This is the local term of the trace formula
[Stacks, Tag 03UG] for constant coefficients, as used in [Stacks, Tag 03UJ].

## Main results

* `CategoryTheory.Sites.pointHom_presheafFiber_app_const_comp`: a morphism of points commutes with
  the identifications of the fibres of a constant presheaf with its value.
* `CategoryTheory.Sites.pointHom_sheafFiber_app_constantSheaf`: an endomorphism of a point acts as
  the identity on the fibre of a constant sheaf.
* `Stacks.EtaleCohomology.geometricFrobeniusStalkFunctor_app_etaleModuleConstantSheaf`: `π_x` is
  the identity on the stalk of a constant sheaf of modules.
* `Stacks.EtaleCohomology.rationalPointStalkFrobenius_constant`: `π_x` is the identity on the stalk
  of a complex of constant sheaves.
* `Stacks.EtaleCohomology.perfectDerivedTrace_rationalPointStalkFrobenius_constant`: the local term
  `Tr(π_x | (N_X)_x̄)` for constant coefficients is `Tr(id | N)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe w v₁ u₁ v₂ u₂ u r

namespace CategoryTheory.Sites

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {D : Type u₂} [Category.{v₂} D] [HasColimitsOfSize.{w, w} D]

/-- A morphism of points commutes with the identifications of the fibres of a constant presheaf
with its value. -/
theorem pointHom_presheafFiber_app_const_comp {Φ₁ Φ₂ : J.Point.{w}} (f : Φ₁ ⟶ Φ₂) (A : D) :
    f.presheafFiber.app ((Functor.const Cᵒᵖ).obj A) ≫ (constantPresheafFiberIso Φ₁ A).hom =
      (constantPresheafFiberIso Φ₂ A).hom := by
  refine Φ₂.presheafFiber_hom_ext fun X x => ?_
  have h : Φ₂.toPresheafFiber X x ((Functor.const Cᵒᵖ).obj A) ≫
      f.presheafFiber.app ((Functor.const Cᵒᵖ).obj A) =
        Φ₁.toPresheafFiber X (f.hom.app X x) ((Functor.const Cᵒᵖ).obj A) := by
    simp
  rw [← Category.assoc, h, constantPresheafFiberIso_ι, constantPresheafFiberIso_ι]

variable [hP : HasProducts.{w} D] [hS : HasWeakSheafify J D]

/-- **An endomorphism of a point acts as the identity on the fibre of a constant sheaf.** On the
constant presheaf it is the identity by `pointHom_presheafFiber_app_const_comp`. The
sheafification map is an isomorphism on fibres, and the action commutes with it. -/
theorem pointHom_sheafFiber_app_constantSheaf {Φ : J.Point.{w}} (f : Φ ⟶ Φ) (A : D) :
    f.sheafFiber.app ((constantSheaf J D).obj A) = 𝟙 _ := by
  have h1 : f.presheafFiber.app ((Functor.const Cᵒᵖ).obj A) = 𝟙 _ := by
    rw [← cancel_mono (constantPresheafFiberIso Φ A).hom, pointHom_presheafFiber_app_const_comp,
      Category.id_comp]
  have hnat := f.presheafFiber.naturality (toSheafify J ((Functor.const Cᵒᵖ).obj A))
  rw [h1, Category.id_comp] at hnat
  show f.presheafFiber.app (sheafify J ((Functor.const Cᵒᵖ).obj A)) = 𝟙 _
  rw [← cancel_epi (Φ.presheafFiber.map (toSheafify J ((Functor.const Cᵒᵖ).obj A))), hnat,
    Category.comp_id]

end CategoryTheory.Sites


namespace CategoryTheory.FilteredDerived

attribute [local instance] HasDerivedCategory.standard

/-- A module placed in degree zero has trivial components away from degree zero. -/
private theorem subsingleton_single_obj_X (R : Type u₁) [Ring R] (A : ModuleCat.{v₁} R) {i : ℤ}
    (hi : i ≠ 0) :
    Subsingleton (((HomologicalComplex.single (ModuleCat.{v₁} R) (ComplexShape.up ℤ) 0).obj A).X
      i) :=
  ModuleCat.subsingleton_of_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi)

/-- A finite projective module placed in degree zero has finite projective components. -/
private theorem projective_finite_single_obj_X (R : Type u₁) [Ring R] (A : ModuleCat.{v₁} R)
    [Module.Finite R A] [Module.Projective R A] (i : ℤ) :
    Module.Projective R (((HomologicalComplex.single (ModuleCat.{v₁} R) (ComplexShape.up ℤ) 0).obj
      A).X i) ∧
    Module.Finite R (((HomologicalComplex.single (ModuleCat.{v₁} R) (ComplexShape.up ℤ) 0).obj
      A).X i) := by
  by_cases hi : i = 0
  · subst hi
    let e₀ := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 A).toLinearEquiv
    exact ⟨Module.Projective.of_equiv e₀.symm, Module.Finite.equiv e₀.symm⟩
  · have := subsingleton_single_obj_X R A hi
    exact ⟨inferInstance, inferInstance⟩

/-- **The trace of an endomorphism of a module placed in degree zero** is its trace as an
endomorphism of the finite projective module. -/
theorem perfectDerivedTrace_single_map (R : Type u₁) [Ring R] (A : ModuleCat.{v₁} R)
    [Module.Finite R A] [Module.Projective R A] (f : A ⟶ A)
    (hS : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
      ((HomologicalComplex.single (ModuleCat.{v₁} R) (ComplexShape.up ℤ) 0).obj A))) :
    perfectDerivedTrace R ⟨_, hS⟩ (DerivedCategory.Q.map
        ((HomologicalComplex.single (ModuleCat.{v₁} R) (ComplexShape.up ℤ) 0).map f)) =
      Stacks.Trace.projectiveModuleTrace R A f.hom := by
  classical
  set P := (HomologicalComplex.single (ModuleCat.{v₁} R) (ComplexShape.up ℤ) 0).obj A
  let e₀ : P.X 0 ≃ₗ[R] A :=
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 A).toLinearEquiv
  have hP : finiteProjectiveComplex R P :=
    ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, projective_finite_single_obj_X R A⟩
  rw [perfectDerivedTrace_eq_alternatingTrace R ⟨_, hS⟩ _ P hP (Iso.refl _)
    ((HomologicalComplex.single (ModuleCat.{v₁} R) (ComplexShape.up ℤ) 0).map f) (by simp),
    alternatingTrace, finsum_eq_single _ (0 : ℤ) fun i hi => ?_]
  · have := (hP.2 0).1
    have := (hP.2 0).2
    have hf : ((HomologicalComplex.single (ModuleCat.{v₁} R) (ComplexShape.up ℤ) 0).map f).f 0 =
        ModuleCat.ofHom (e₀.symm.toLinearMap.comp (f.hom.comp e₀.toLinearMap)) := by
      rw [HomologicalComplex.single_map_f_self]
      rfl
    simp only [if_pos (even_iff_two_dvd.mpr (dvd_zero 2) : Even (0 : ℤ)), hf, ModuleCat.hom_ofHom]
    simpa only [LinearEquiv.symm_symm] using projectiveModuleTrace_conj R e₀.symm f.hom
  · have := subsingleton_single_obj_X R A hi
    have := (hP.2 i).1
    have := (hP.2 i).2
    simp only [projectiveModuleTrace_eq_zero_of_subsingleton, neg_zero, ite_self]

end CategoryTheory.FilteredDerived

namespace Stacks.EtaleCohomology

open CategoryTheory.FilteredDerived

attribute [local instance] HasDerivedCategory.standard

section Stalk

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] {X : Scheme.{u}}
  (K : Type u) [Field K] [IsAlgClosed K] [Algebra k K]

/-- **An automorphism of `K` over `k` acts as the identity on the stalk of a constant sheaf** at
the geometric point over a rational point. -/
theorem galoisStalkAction_app_etaleModuleConstantSheaf (σ : K ≃ₐ[k] K) (x : Spec (.of k) ⟶ X)
    (M : ModuleCat.{max (u + 1) r} Λ) :
    (Stacks.Frobenius.galoisStalkAction (ModuleCat.{max (u + 1) r} Λ) K σ x).app
        (etaleModuleConstantSheaf Λ M X) =
      𝟙 ((rationalPointStalkFunctor.{u, r} Λ K x).obj (etaleModuleConstantSheaf Λ M X)) :=
  CategoryTheory.Sites.pointHom_sheafFiber_app_constantSheaf (D := ModuleCat.{max (u + 1) r} Λ)
    (hP := fun _ => (moduleCat_hasLimitsOfSize.{u, u, r, max (u + 1) r} Λ).has_limits_of_shape _)
    (hS := inferInstance) _ M

/-- **The geometric Frobenius `π_x` is the identity on the stalk of a constant sheaf**
([Stacks, Tag 03SW]): it is the action of an automorphism of `K` over `k`. -/
theorem geometricFrobeniusStalkFunctor_app_etaleModuleConstantSheaf [Fintype k] (p f : ℕ)
    [Fact p.Prime] [CharP K p] (hcard : Fintype.card k = p ^ f) (x : Spec (.of k) ⟶ X)
    (M : ModuleCat.{max (u + 1) r} Λ) :
    (Stacks.Frobenius.geometricFrobeniusStalkFunctor (ModuleCat.{max (u + 1) r} Λ) K p f
        hcard x).app (etaleModuleConstantSheaf Λ M X) =
      𝟙 ((rationalPointStalkFunctor.{u, r} Λ K x).obj (etaleModuleConstantSheaf Λ M X)) :=
  galoisStalkAction_app_etaleModuleConstantSheaf Λ K _ x M

end Stalk

section Constant

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime]
  [CharP kbar p]

/-- **`π_x` is the identity on the stalk of a complex of constant sheaves.** Degreewise it is the
geometric Frobenius on the stalk of a constant sheaf. -/
theorem rationalPointStalkFrobenius_constant (hcard : Fintype.card k = p ^ q)
    (x : Spec (.of k) ⟶ X) (N : CochainComplex.Plus (ModuleCat.{max (u + 1) r} Λ)) :
    rationalPointStalkFrobenius.{u, r} Λ kbar p q hcard x
        ((constantSheaf X.smallEtaleTopology
          (ModuleCat.{max (u + 1) r} Λ)).mapCochainComplexPlus.obj N) = 𝟙 _ := by
  ext n : 1
  exact geometricFrobeniusStalkFunctor_app_etaleModuleConstantSheaf Λ kbar p q hcard x (N.obj.X n)

/-- **The stalk of a complex of constant sheaves is the complex of values**, degreewise by the
identification of the fibre of a constant sheaf with its value. -/
def rationalPointStalkComplexConstantIso (x : Spec (.of k) ⟶ X)
    (N : CochainComplex.Plus (ModuleCat.{max (u + 1) r} Λ)) :
    rationalPointStalkComplex.{u, r} Λ kbar x
        ((constantSheaf X.smallEtaleTopology
          (ModuleCat.{max (u + 1) r} Λ)).mapCochainComplexPlus.obj N) ≅ N.obj :=
  have hL : HasLimitsOfSize.{u, u} (ModuleCat.{max (u + 1) r} Λ) :=
    moduleCat_hasLimitsOfSize.{u, u, r, max (u + 1) r} Λ
  let e := CategoryTheory.Sites.constantSheafFiberNatIso
    (D := ModuleCat.{max (u + 1) r} Λ) (J := X.smallEtaleTopology)
    (Scheme.pointSmallEtale (Stacks.Frobenius.rationalGeometricPoint kbar x).hom)
  HomologicalComplex.Hom.isoOfComponents (fun n => e.app (N.obj.X n))
    (fun i j _ => (e.hom.naturality (N.obj.d i j)).symm)

/-- The stalk of a complex of constant sheaves with perfect values is perfect. -/
theorem isPerfect_rationalPointStalkComplex_constant (x : Spec (.of k) ⟶ X)
    (N : CochainComplex.Plus (ModuleCat.{max (u + 1) r} Λ))
    (hN : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj N.obj)) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj (rationalPointStalkComplex.{u, r} Λ kbar x
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).mapCochainComplexPlus.obj
        N))) := by
  obtain ⟨P, a, b, ha, hb, hfin, hproj, ⟨e⟩⟩ := hN
  exact ⟨P, a, b, ha, hb, hfin, hproj,
    ⟨DerivedCategory.Q.mapIso (rationalPointStalkComplexConstantIso Λ kbar x N) ≪≫ e⟩⟩

/-- **The local term of the trace formula for constant coefficients.** For a complex of constant
sheaves with value a perfect complex `N`, the trace of `π_x` on the stalk at the geometric point
over a rational point is the trace of the identity of `N`. -/
theorem perfectDerivedTrace_rationalPointStalkFrobenius_constant (hcard : Fintype.card k = p ^ q)
    (x : Spec (.of k) ⟶ X) (N : CochainComplex.Plus (ModuleCat.{max (u + 1) r} Λ))
    (hN : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj N.obj))
    (hS : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj (rationalPointStalkComplex.{u, r} Λ
      kbar x
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).mapCochainComplexPlus.obj
        N)))) :
    perfectDerivedTrace Λ ⟨_, hS⟩ (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, r} Λ kbar
        p q hcard x
        ((constantSheaf X.smallEtaleTopology
          (ModuleCat.{max (u + 1) r} Λ)).mapCochainComplexPlus.obj N))) =
      perfectDerivedTrace Λ ⟨_, hN⟩ (𝟙 _) := by
  rw [rationalPointStalkFrobenius_constant, CategoryTheory.Functor.map_id]
  exact perfectDerivedTrace_congr Λ _ _
    (DerivedCategory.Q.mapIso (rationalPointStalkComplexConstantIso Λ kbar x N)) _ _ (by simp)

/-- The module `Λ`, in the module universe of sheaves of `Λ`-modules on a small étale site, placed
in degree zero. -/
abbrev constantCoefficientComplex : CochainComplex.Plus (ModuleCat.{max (u + 1) r} Λ) :=
  (Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj (ModuleCat.of Λ (ULift.{u + 1} Λ))

/-- `Λ` placed in degree zero is perfect. -/
theorem isPerfect_constantCoefficientComplex :
    StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Q.obj (constantCoefficientComplex.{u, r} Λ).obj) := by
  refine ⟨_, 0, 0,
    inferInstanceAs (CochainComplex.IsStrictlyGE ((HomologicalComplex.single
      (ModuleCat.{max (u + 1) r} Λ) (ComplexShape.up ℤ) 0).obj
        (ModuleCat.of Λ (ULift.{u + 1} Λ))) 0),
    inferInstanceAs (CochainComplex.IsStrictlyLE ((HomologicalComplex.single
      (ModuleCat.{max (u + 1) r} Λ) (ComplexShape.up ℤ) 0).obj
        (ModuleCat.of Λ (ULift.{u + 1} Λ))) 0),
    fun i => (projective_finite_single_obj_X Λ (ModuleCat.of Λ (ULift.{u + 1} Λ)) i).2,
    fun i => (projective_finite_single_obj_X Λ (ModuleCat.of Λ (ULift.{u + 1} Λ)) i).1,
    ⟨Iso.refl _⟩⟩

/-- **The trace of the identity of `Λ` placed in degree zero is `1`.** -/
theorem perfectDerivedTrace_id_constantCoefficientComplex
    (hN : StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Q.obj (constantCoefficientComplex.{u, r} Λ).obj)) :
    perfectDerivedTrace Λ ⟨_, hN⟩ (𝟙 _) = additiveCommutatorQuotientMk Λ 1 := by
  let eU : ULift.{u + 1} Λ ≃ₗ[Λ] Λ := ULift.moduleEquiv
  have : Module.Finite Λ (ULift.{u + 1} Λ) := Module.Finite.equiv eU.symm
  have : Module.Projective Λ (ULift.{u + 1} Λ) := Module.Projective.of_equiv eU.symm
  have h1 : (𝟙 (DerivedCategory.Q.obj (constantCoefficientComplex.{u, r} Λ).obj)) =
      DerivedCategory.Q.map ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
        (𝟙 (ModuleCat.of Λ (ULift.{u + 1} Λ)))) := by
    simp only [CategoryTheory.Functor.map_id]
    rfl
  rw [h1]
  refine (perfectDerivedTrace_single_map Λ (ModuleCat.of Λ (ULift.{u + 1} Λ)) (𝟙 _) hN).trans ?_
  classical
  let pr : (Fin 1 → Λ) →ₗ[Λ] ULift.{u + 1} Λ := eU.symm.toLinearMap.comp (LinearMap.proj 0)
  let ι : ULift.{u + 1} Λ →ₗ[Λ] (Fin 1 → Λ) := LinearMap.pi fun _ => eU.toLinearMap
  rw [ModuleCat.hom_id, projectiveModuleTrace_eq_of_split Λ _ _ pr ι
    (LinearMap.ext fun x => by simp [pr, ι]), freeModuleTrace_apply, Fin.sum_univ_one]
  simp [pr, ι, standardBasisVector]

end Constant

section ConstantModuleSheaf

variable (Λ : Type r) [CommRing Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime]
  [CharP kbar p]

/-- **The local term of the trace formula for the constant sheaf `Λ`** is `1`: the stalk of `Λ_X`
at the geometric point over a rational point is `Λ`, and `π_x` acts on it as the identity. -/
theorem perfectDerivedTrace_rationalPointStalkFrobenius_constantModuleSheaf
    (hcard : Fintype.card k = p ^ q) (x : Spec (.of k) ⟶ X)
    (hS : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj (rationalPointStalkComplex.{u, r} Λ
      kbar x ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf.{r, u, u + 1} Λ
          X.smallEtaleTopology))))) :
    perfectDerivedTrace Λ ⟨_, hS⟩ (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, r} Λ kbar
        p q hcard x ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          (Stacks.Cohomology.GlobalSections.constantModuleSheaf.{r, u, u + 1} Λ
            X.smallEtaleTopology)))) =
      additiveCommutatorQuotientMk Λ 1 := by
  let F := constantSheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)
  let E := (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app
    (ModuleCat.of Λ (ULift.{u + 1} Λ))
  have hN := isPerfect_constantCoefficientComplex.{u, r} Λ
  rw [perfectDerivedTrace_rationalPointStalkFrobenius_congr Λ kbar p q hcard x
    (M' := F.mapCochainComplexPlus.obj (constantCoefficientComplex.{u, r} Λ))
    (fun n => (HomologicalComplex.eval _ _ n).mapIso E.symm) (fun a b => (E.inv.comm a b).symm) hS
    (isPerfect_rationalPointStalkComplex_constant Λ kbar x _ hN),
    perfectDerivedTrace_rationalPointStalkFrobenius_constant Λ kbar p q hcard x _ hN]
  exact perfectDerivedTrace_id_constantCoefficientComplex Λ hN

end ConstantModuleSheaf

end Stacks.EtaleCohomology

end
