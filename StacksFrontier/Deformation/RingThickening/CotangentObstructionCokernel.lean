module

public import StacksFrontier.Cotangent.ExtendScalars
public import StacksFrontier.Deformation.RingThickening.CotangentExtComparison
public import StacksFrontier.Deformation.RingThickening.CotangentObstructionClasses
public import StacksFrontier.Deformation.SquareZero.AlgebraExtensionMaps

/-!
# The conormal cokernels as cokernels of lifted maps

`Ext¹_B(NL_{B/A'}, N)` and `Ext¹_A(NL_{A/A'}, N)` are presented in
`StacksFrontier/Deformation/SquareZero/Obstruction.lean` by the cokernels
`Hom_B(J_B/J_B², N) / Hom_B(Ω_B, N)` and `Hom_A(J_A/J_A², N) / Hom_A(Ω_A, N)` of the canonical
presentations `A'[B] → B` and `A'[A] → A`. This file identifies them with the cokernels of the
maps which present `Ext¹_B(NL_{B/A'}, N)` and `Ext¹_B(NL_{A/A'} ⊗_A B, N)` in the module universe
of `cotangentExt`: the first by the universe lift, the second by the extension–restriction
adjunction `Hom_A(M, N) = Hom_B(B ⊗_A M, N)`.

## Main definitions

* `Stacks.Deformation.quotientCongr`: quotients by corresponding submodules are equivalent.
* `Stacks.Deformation.SquareZeroExtensionProblem.towerHomEquiv`,
  `Stacks.Deformation.SquareZeroExtensionProblem.baseHomEquiv`: functionals into `N` as morphisms
  into the lifted `N`, the second by `Hom_A(M, N) = Hom_B(B ⊗_A M, N)`.
* `Stacks.Deformation.SquareZeroExtensionProblem.towerCokernelEquiv`,
  `Stacks.Deformation.SquareZeroExtensionProblem.baseCokernelEquiv`.
* `Stacks.Deformation.SquareZeroExtensionProblem.towerClass`,
  `Stacks.Deformation.SquareZeroExtensionProblem.baseClass`:
  `Ext¹_B(NL_{B/A'}, N) = Ext¹_B(L_{B/A'}, N)` and
  `Ext¹_A(NL_{A/A'}, N) = Ext¹_B(L_{A/A'} ⊗_A B, N)`, by cocycles.

## References

* [Stacks Project, Tag 08SP](https://stacks.math.columbia.edu/tag/08SP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

universe u u₄

namespace Stacks.Deformation

/-- **Quotients by corresponding submodules are equivalent**: an additive equivalence carrying
one submodule onto the other descends to the quotients. The two modules may be over different
rings. -/
def quotientCongr {R R' M M' : Type*} [Ring R] [Ring R'] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R' M'] (p : Submodule R M) (p' : Submodule R' M') (e : M ≃+ M')
    (h : ∀ x, x ∈ p ↔ e x ∈ p') : M ⧸ p ≃ M' ⧸ p' :=
  Quotient.congr e.toEquiv fun a b => by
    change p.quotientRel a b ↔ p'.quotientRel (e a) (e b)
    rw [Submodule.quotientRel_def, Submodule.quotientRel_def, ← map_sub]
    exact h _

/-- `quotientCongr` sends the class of `x` to the class of `e x`. -/
theorem quotientCongr_mk {R R' M M' : Type*} [Ring R] [Ring R'] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R' M'] (p : Submodule R M) (p' : Submodule R' M') (e : M ≃+ M')
    (h : ∀ x, x ∈ p ↔ e x ∈ p') (x : M) :
    quotientCongr p p' e h (Submodule.Quotient.mk x) = Submodule.Quotient.mk (e x) :=
  rfl

namespace SquareZeroExtensionProblem

variable (S : SquareZeroExtensionProblem.{u, u, u, u})

/-- A universe-lifted module is isomorphic to the module itself. -/
noncomputable abbrev liftBIso (X : ModuleCat.{u} S.B) : S.liftB.obj X ≅ X :=
  (ULift.moduleEquiv (R := S.B) (M := X)).toModuleIso

/-- Precomposition with `liftBIso`. -/
noncomputable def liftBHomEquiv (X : ModuleCat.{u} S.B) (Z : ModuleCat.{u} S.B) :
    (X ⟶ Z) ≃+ (S.liftB.obj X ⟶ Z) where
  toFun φ := (S.liftBIso X).hom ≫ φ
  invFun ψ := (S.liftBIso X).inv ≫ ψ
  left_inv _φ := Iso.inv_hom_id_assoc _ _
  right_inv _ψ := Iso.hom_inv_id_assoc _ _
  map_add' _φ _ψ := Preadditive.comp_add _ _ _ _ _ _

/-- Linear maps into `N` are morphisms into the lifted `N`. -/
noncomputable def toLiftedKernelEquiv (M : ModuleCat.{u} S.B) :
    (M →ₗ[S.B] S.N) ≃+ (M ⟶ liftedKernelModule.{u, u, u, u} S) where
  toFun g := ModuleCat.ofHom ((ULift.moduleEquiv (R := S.B) (M := S.N)).symm.toLinearMap ∘ₗ g)
  invFun φ := (ULift.moduleEquiv (R := S.B) (M := S.N)).toLinearMap ∘ₗ φ.hom
  left_inv g := by ext x; rfl
  right_inv φ := by ext x; rfl
  map_add' g g' := by ext x; rfl

/-- `A`-linear maps into `N` are `A`-linear maps into the restriction of the lifted `N`. -/
noncomputable def toRestrictedKernelLinearEquiv (M : ModuleCat.{u} S.A) :
    letI : Module S.A ((ModuleCat.restrictScalars (algebraMap S.A S.B)).obj
      (liftedKernelModule.{u, u, u, u} S)) :=
      ((ModuleCat.restrictScalars (algebraMap S.A S.B)).obj
        (liftedKernelModule.{u, u, u, u} S)).isModule
    (M →ₗ[S.A] S.N) ≃+
      (M →ₗ[S.A] (ModuleCat.restrictScalars (algebraMap S.A S.B)).obj
        (liftedKernelModule.{u, u, u, u} S)) :=
  letI : Module S.A ((ModuleCat.restrictScalars (algebraMap S.A S.B)).obj
      (liftedKernelModule.{u, u, u, u} S)) :=
    ((ModuleCat.restrictScalars (algebraMap S.A S.B)).obj
      (liftedKernelModule.{u, u, u, u} S)).isModule
  { toFun := fun g =>
      { toFun := fun x => ULift.up (g x)
        map_add' := fun x y => by rw [map_add]; rfl
        map_smul' := fun a x => by
          rw [map_smul, RingHom.id_apply]
          exact ULift.ext (by
            change a • g x = algebraMap S.A S.B a • g x
            rw [algebraMap_smul]) }
    invFun := fun φ =>
      { toFun := fun x => (φ x).down
        map_add' := fun x y => by rw [map_add]; rfl
        map_smul' := fun a x => by
          rw [map_smul, RingHom.id_apply, ModuleCat.restrictScalars.smul_def]
          change algebraMap S.A S.B a • (φ x).down = a • (φ x).down
          rw [algebraMap_smul] }
    left_inv := fun g => LinearMap.ext fun x => rfl
    right_inv := fun φ => LinearMap.ext fun x => rfl
    map_add' := fun g g' => LinearMap.ext fun x => rfl }

/-- `A`-linear maps into `N` are morphisms into the restriction of the lifted `N`. -/
noncomputable def toRestrictedKernelEquiv (M : ModuleCat.{u} S.A) :
    (M →ₗ[S.A] S.N) ≃+
      (M ⟶ (ModuleCat.restrictScalars (algebraMap S.A S.B)).obj
        (liftedKernelModule.{u, u, u, u} S)) :=
  (S.toRestrictedKernelLinearEquiv M).trans ModuleCat.homAddEquiv.symm

/-- **`Hom_B(N₁, N) = Hom_B(N₁, N)` after the universe lift**, for a `B`-module `N₁`. -/
noncomputable def towerHomEquiv (M : ModuleCat.{u} S.B) :
    (M →ₗ[S.B] S.N) ≃+ (S.liftB.obj M ⟶ liftedKernelModule.{u, u, u, u} S) :=
  (S.toLiftedKernelEquiv M).trans (S.liftBHomEquiv M _)

/-- **`Hom_A(M, N) = Hom_B(B ⊗_A M, N)`**, the extension–restriction adjunction, after the
universe lift. -/
noncomputable def baseHomEquiv (M : ModuleCat.{u} S.A) :
    (M →ₗ[S.A] S.N) ≃+ (S.liftBaseChange.obj M ⟶ liftedKernelModule.{u, u, u, u} S) :=
  (S.toRestrictedKernelEquiv M).trans
    ((((ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap S.A S.B)).homAddEquiv M
      (liftedKernelModule.{u, u, u, u} S)).symm).trans
    (S.liftBHomEquiv (S.baseChangeFunctor.obj M) _))

/-- `baseHomEquiv g` on a pure tensor: `s ⊗ x` goes to `s • g x`. -/
theorem baseHomEquiv_apply_tmul (M : ModuleCat.{u} S.A) (g : M →ₗ[S.A] S.N) (s : S.B)
    (x : M) :
    S.baseHomEquiv M g (ULift.up (s ⊗ₜ[S.A, algebraMap S.A S.B] x)) = ULift.up (s • g x) := by
  change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars (algebraMap S.A S.B)
    ((S.toRestrictedKernelEquiv M) g) (s ⊗ₜ[S.A, algebraMap S.A S.B] x) = _
  rw [ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_tmul]
  rfl

/-- `towerHomEquiv g` is `g` itself, read through the universe lift. -/
theorem towerHomEquiv_apply (M : ModuleCat.{u} S.B) (g : M →ₗ[S.B] S.N) (x : M) :
    S.towerHomEquiv M g (ULift.up x) = ULift.up (g x) :=
  rfl

/-- The lift of a composite: `towerHomEquiv` is natural in the source. -/
theorem towerHomEquiv_comp {M₁ M₀ : ModuleCat.{u} S.B} (d : M₁ ⟶ M₀) (k : M₀ →ₗ[S.B] S.N) :
    S.towerHomEquiv M₁ (k ∘ₗ d.hom) = S.liftB.map d ≫ S.towerHomEquiv M₀ k :=
  rfl

/-- `baseHomEquiv` is natural in the source. -/
theorem baseHomEquiv_comp {M₁ M₀ : ModuleCat.{u} S.A} (d : M₁ ⟶ M₀) (k : M₀ →ₗ[S.A] S.N) :
    S.baseHomEquiv M₁ (k ∘ₗ d.hom) = S.liftBaseChange.map d ≫ S.baseHomEquiv M₀ k := by
  have h₁ : S.toRestrictedKernelEquiv M₁ (k ∘ₗ d.hom) = d ≫ S.toRestrictedKernelEquiv M₀ k :=
    rfl
  change (S.liftBIso _).hom ≫ ((ModuleCat.extendRestrictScalarsAdj.{u, u, u}
      (algebraMap S.A S.B)).homEquiv M₁ _).symm (S.toRestrictedKernelEquiv M₁ (k ∘ₗ d.hom)) =
    S.liftB.map (S.baseChangeFunctor.map d) ≫ (S.liftBIso _).hom ≫
      ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap S.A S.B)).homEquiv M₀
        _).symm (S.toRestrictedKernelEquiv M₀ k)
  rw [h₁, Adjunction.homEquiv_naturality_left_symm, ← Category.assoc, ← Category.assoc]
  rfl

/-- A point is in the range of `f` exactly when its image under an equivalence is in the range of
`f'`, if the equivalences intertwine `f` and `f'`. -/
private theorem exists_eq_iff_equiv {G₁ G₀ H₁ H₀ : Type*} (f : G₀ → G₁) (f' : H₀ → H₁)
    (e₁ : G₁ ≃ H₁) (e₀ : G₀ ≃ H₀) (h : ∀ k, e₁ (f k) = f' (e₀ k)) (g : G₁) :
    (∃ k, f k = g) ↔ ∃ ψ, f' ψ = e₁ g := by
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨e₀ k, (h k).symm⟩
  · rintro ⟨ψ, hψ⟩
    refine ⟨e₀.symm ψ, e₁.injective ?_⟩
    rw [h, Equiv.apply_symm_apply, hψ]

/-- A `B`-linear functional on `M₁` is in the range of precomposition with `d` exactly when its
lift is. -/
theorem mem_range_iff_towerHomEquiv {M₁ M₀ : ModuleCat.{u} S.B} (d : M₁ ⟶ M₀)
    (g : M₁ →ₗ[S.B] S.N) :
    g ∈ LinearMap.range (LinearMap.lcomp S.B S.N d.hom) ↔
      S.towerHomEquiv M₁ g ∈ LinearMap.range
        (Linear.leftComp S.B (liftedKernelModule.{u, u, u, u} S) (S.liftB.map d)) :=
  exists_eq_iff_equiv _ _ (S.towerHomEquiv M₁).toEquiv (S.towerHomEquiv M₀).toEquiv
    (fun k => S.towerHomEquiv_comp d k) g

/-- An `A`-linear functional on `M₁` is in the range of precomposition with `d` exactly when its
`B`-linear extension is. -/
theorem mem_range_iff_baseHomEquiv {M₁ M₀ : ModuleCat.{u} S.A} (d : M₁ ⟶ M₀)
    (g : M₁ →ₗ[S.A] S.N) :
    g ∈ LinearMap.range (LinearMap.lcomp S.A S.N d.hom) ↔
      S.baseHomEquiv M₁ g ∈ LinearMap.range
        (Linear.leftComp S.B (liftedKernelModule.{u, u, u, u} S) (S.liftBaseChange.map d)) :=
  exists_eq_iff_equiv _ _ (S.baseHomEquiv M₁).toEquiv (S.baseHomEquiv M₀).toEquiv
    (fun k => S.baseHomEquiv_comp d k) g

/-- **The conormal cokernel of `A'[B] → B`** is the cokernel of the lifted conormal
differential. -/
noncomputable def towerCokernelEquiv :
    extOneCokernel S.A' S.B S.N ≃
      (S.liftB.obj (ModuleCat.of S.B S.towerNaive.Cotangent) ⟶
          liftedKernelModule.{u, u, u, u} S) ⧸
        LinearMap.range (Linear.leftComp S.B (liftedKernelModule.{u, u, u, u} S)
          S.towerDifferential) :=
  quotientCongr _ _ (S.towerHomEquiv (ModuleCat.of S.B S.towerNaive.Cotangent))
    (S.mem_range_iff_towerHomEquiv (ModuleCat.ofHom S.towerNaive.cotangentComplex))

/-- **The conormal cokernel of `A'[A] → A`** is the cokernel of the conormal differential base
changed to `B` and lifted: the extension–restriction adjunction. -/
noncomputable def baseCokernelEquiv :
    extOneCokernel S.A' S.A S.N ≃
      (S.liftBaseChange.obj (ModuleCat.of S.A S.baseNaive.Cotangent) ⟶
          liftedKernelModule.{u, u, u, u} S) ⧸
        LinearMap.range (Linear.leftComp S.B (liftedKernelModule.{u, u, u, u} S)
          S.baseDifferential) :=
  quotientCongr _ _ (S.baseHomEquiv (ModuleCat.of S.A S.baseNaive.Cotangent))
    (S.mem_range_iff_baseHomEquiv (ModuleCat.ofHom S.baseNaive.cotangentComplex))

attribute [local instance high] HasDerivedCategory.standard

/-- The lift of `Ω_{A'[B]/A'} ⊗ B`, a free module, is projective. -/
instance projective_towerCotangentSpace :
    Projective (S.liftB.obj (ModuleCat.of S.B S.towerNaive.CotangentSpace)) :=
  (S.liftB.obj
    (ModuleCat.of S.B S.towerNaive.CotangentSpace)).projective_of_categoryTheory_projective

/-- The lift of `Ω_{A'[A]/A'} ⊗ A` base changed to `B` is projective: extension of scalars
preserves projectives. -/
instance projective_baseCotangentSpace :
    Projective (S.liftBaseChange.obj (ModuleCat.of S.A S.baseNaive.CotangentSpace)) := by
  have : Projective (ModuleCat.of S.A S.baseNaive.CotangentSpace) :=
    (ModuleCat.of S.A S.baseNaive.CotangentSpace).projective_of_categoryTheory_projective
  have : Projective (S.baseChangeFunctor.obj (ModuleCat.of S.A S.baseNaive.CotangentSpace)) :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap S.A S.B)).map_projective _
      inferInstance
  exact Functor.projective_obj S.liftB _

/-- **`Ext¹_B(NL_{B/A'}, N) = Ext¹_B(L_{B/A'}, N)`, by cocycles**: a class of
`Ext¹_B(NL_{B/A'}, N)` is presented by a conormal functional `f : J_B/J_B² → N`; it goes to the
class of the cochain map of `f` on the naive cotangent complex, pulled back along
`L_{B/A'} → NL_{B/A'}`. -/
noncomputable def towerClass :
    naiveCotangentExtOne S.A' S.B S.N ≃
      (DerivedCategory.Q.obj ((S.liftB.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (CommAlgCat.cotangentComplex.{u, u} S.A' (CommAlgCat.of S.A' S.B))) ⟶
        (liftedKernelSingle.{u, u, u, u} S)⟦(1 : ℤ)⟧) :=
  haveI := S.isIso_truncGE_map_Q_towerCocycleMap
  haveI := isGE_liftedKernelSingle_shift_one.{u, u, u, u} S
  (extCokernelIso S.A' S.B S.N).toEquiv.trans
    (S.towerCokernelEquiv.trans
      ((NaiveCotangent.ExtCokernelLinear.cokernelExtOneEquiv S.towerDifferential).toEquiv.trans
        (Equiv.ofBijective _ (bijective_comp_of_isIso_truncGE
          (DerivedCategory.Q.map S.towerCocycleMap) (-1)))))

/-- **`Ext¹_A(NL_{A/A'}, N) = Ext¹_B(L_{A/A'} ⊗_A B, N)`, by cocycles**: a class of
`Ext¹_A(NL_{A/A'}, N)` is presented by a conormal functional `f : J_A/J_A² → N`; it goes to the
class of the cochain map of its `B`-linear extension on `NL_{A/A'} ⊗_A B`, pulled back along
`L_{A/A'} ⊗_A B → NL_{A/A'} ⊗_A B`. -/
noncomputable def baseClass :
    naiveCotangentExtOne S.A' S.A S.N ≃
      (DerivedCategory.Q.obj ((S.liftBaseChange.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (CommAlgCat.cotangentComplex.{u, u} S.A' (CommAlgCat.of S.A' S.A))) ⟶
        (liftedKernelSingle.{u, u, u, u} S)⟦(1 : ℤ)⟧) :=
  haveI := S.isIso_truncGE_map_Q_baseCocycleMap
  haveI := isGE_liftedKernelSingle_shift_one.{u, u, u, u} S
  (extCokernelIso S.A' S.A S.N).toEquiv.trans
    (S.baseCokernelEquiv.trans
      ((NaiveCotangent.ExtCokernelLinear.cokernelExtOneEquiv S.baseDifferential).toEquiv.trans
        (Equiv.ofBijective _ (bijective_comp_of_isIso_truncGE
          (DerivedCategory.Q.map S.baseCocycleMap) (-1)))))

end SquareZeroExtensionProblem

end Stacks.Deformation

end
