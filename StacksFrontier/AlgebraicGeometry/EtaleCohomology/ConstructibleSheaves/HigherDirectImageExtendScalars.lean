module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.HigherDirectImageQuotientRing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleProperVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HigherDirectImageFilteredColimits
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.ConstantCoefficientsCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CompactModuleSheaves
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.CoproductsFromFiltered
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionCoefficientsDirectSums
public import StacksFrontier.Algebra.Homology.RightDerivedCentralEndomorphism
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicTower
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.InverseImage
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Higher direct images of the constant sheaf after extending the coefficient field

Let `f : X ⟶ S` be a quasi-compact quasi-separated morphism of schemes, `K` a field and `A` a
commutative `K`-algebra. This file shows that the higher direct image `R^q f_* A` of the constant
sheaf of `A`-modules is the extension of scalars to `A` of the higher direct image `R^q f_* K` of
the constant sheaf of `K`-vector spaces, as sheaves of `A`-modules: a special case of
[Stacks, Tag 0F0G]. As a consequence, constructibility of `R^q f_* 𝐙/ℓ` for every prime `ℓ`
implies constructibility of `R^q f_* M` for finite modules `M` annihilated by a positive integer
([Stacks, Tag 0GKW]).

## Implementation notes

Choose a `K`-basis `(b_i)` of `A`. Forgetting to sheaves of `K`-vector spaces:

* the extension of scalars `E ⊗_K A` of a sheaf `E` of `K`-vector spaces is the direct sum of
  copies of `E` with injections `e ↦ e ⊗ b_i`;
* `R^q f_* A` is the direct sum of copies of `R^q f_* K` with injections the images of
  `K → A, c ↦ c b_i`, because `R^q f_*` commutes with direct sums
  (`Stacks.EtaleCohomology.preservesColimitsOfShape_discrete_rightDerived_etaleModuleDirectImage`)
  and with restriction of scalars; and the multiplication by `b_i` on `R^q f_* A` is
  `R^q f_*` of multiplication by `b_i` on `A`
  (`CategoryTheory.Functor.rightDerived_map_app_of_natTrans`).

The `A`-linear comparison `R^q f_* K ⊗_K A → R^q f_* A` adjoint to `R^q f_*(K → A)` carries the
injections of the first direct sum to those of the second, so it is an isomorphism.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleSMul`: multiplication by a scalar, an endomorphism of the
  identity functor of sheaves of modules over a commutative ring.
* `Stacks.EtaleCohomology.extendScalarsRightDerivedConstantUnitHom`: the `A`-linear comparison
  `R^q f_* K ⊗_K A ⟶ R^q f_* A`.

## Main results

* `Stacks.EtaleCohomology.isIso_extendScalarsRightDerivedConstantUnitHom`: the comparison
  `R^q f_* K ⊗_K A ⟶ R^q f_* A` is an isomorphism.
* `Stacks.EtaleCohomology.isConstructibleEtaleModule_etaleModuleExtendScalars`: extension of
  scalars along a homomorphism of Noetherian rings preserves constructibility.
* `Stacks.EtaleCohomology.isConstructibleEtaleModule_rightDerived_constantSheaf_of_zmod`: if
  `R^q f_* 𝐙/ℓ` is constructible for every prime `ℓ` and every `q`, then so is `R^q f_* M` for
  every finite `Λ`-module `M` annihilated by a positive integer.

## References

* [Stacks, Tag 0F0G]
* [Stacks, Tag 0GKW]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology

section SMul

variable {A : Type} [CommRing A] (Z : Scheme.{u})

/-- **Multiplication by a scalar** `a` of a commutative ring `A`, as an endomorphism of the
identity functor of sheaves of `A`-modules on the small étale site. -/
def etaleModuleSMul (a : A) : 𝟭 (EtaleModules.{u, 0} A Z) ⟶ 𝟭 (EtaleModules.{u, 0} A Z) where
  app G := ObjectProperty.homMk
    { app U := ModuleCat.ofHom (a • LinearMap.id)
      naturality U V g := by
        ext x
        exact (map_smul (G.obj.map g).hom a x).symm }
  naturality G H φ := by
    apply Sheaf.hom_ext
    ext U x
    change a • (φ.hom.app U) x = (φ.hom.app U) (a • x)
    exact (map_smul (φ.hom.app U).hom a x).symm

/-- Multiplication by `a` acts on each section by the scalar action of `a`. -/
@[simp]
theorem etaleModuleSMul_app_hom_app_apply (a : A) (G : EtaleModules.{u, 0} A Z) (U : Z.Etaleᵒᵖ)
    (x : G.obj.obj U) : ((etaleModuleSMul Z a).app G).hom.app U x = a • x :=
  rfl

/-- The direct image commutes with multiplication by a scalar. -/
theorem etaleModuleDirectImage_map_etaleModuleSMul {X Y : Scheme.{u}} (f : X ⟶ Y) (a : A)
    (G : EtaleModules.{u, 0} A X) :
    (etaleModuleDirectImage.{u, 0} A f).map ((etaleModuleSMul X a).app G) =
      (etaleModuleSMul Y a).app ((etaleModuleDirectImage.{u, 0} A f).obj G) := by
  apply Sheaf.hom_ext
  ext U x
  rfl

/-- **Multiplication by a scalar on a higher direct image is the higher direct image of the
multiplication by that scalar.** -/
theorem rightDerived_etaleModuleDirectImage_map_etaleModuleSMul {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : A) (q : ℕ) (G : EtaleModules.{u, 0} A X) :
    ((etaleModuleDirectImage.{u, 0} A f).rightDerived q).map ((etaleModuleSMul X a).app G) =
      (etaleModuleSMul Y a).app (((etaleModuleDirectImage.{u, 0} A f).rightDerived q).obj G) :=
  Functor.rightDerived_map_app_of_natTrans _ (etaleModuleSMul X a) (etaleModuleSMul Y a)
    (etaleModuleDirectImage_map_etaleModuleSMul f a) q G

/-- On a constant sheaf, multiplication by a scalar is the constant sheaf of the multiplication
by that scalar. -/
theorem etaleModuleSMul_app_constantSheaf (a : A) (M : ModuleCat.{u + 1} A) :
    (etaleModuleSMul Z a).app ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M) =
      (constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)).map
        (ModuleCat.ofHom (a • LinearMap.id)) := by
  let adj := constantSheafAdj Z.smallEtaleTopology (ModuleCat.{u + 1} A) terminalIsTerminal
  apply adj.homEquiv _ _ |>.injective
  rw [show (etaleModuleSMul Z a).app ((constantSheaf Z.smallEtaleTopology _).obj M) =
      𝟙 _ ≫ (etaleModuleSMul Z a).app ((constantSheaf Z.smallEtaleTopology _).obj M) from
      (Category.id_comp _).symm,
    show (constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)).map
        (ModuleCat.ofHom (a • LinearMap.id)) =
      (constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)).map
        (ModuleCat.ofHom (a • LinearMap.id)) ≫ 𝟙 _ from (Category.comp_id _).symm,
    adj.homEquiv_naturality_right, adj.homEquiv_naturality_left]
  ext x
  exact (map_smul (adj.homEquiv _ _ (𝟙 _)).hom a x).symm

end SMul

section RestrictScalarsNatural

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ')

/-- Restriction of scalars commutes with the cohomology objects of bounded below complexes,
naturally. -/
def etaleModuleRestrictScalarsPlusHomologyNatIso (Z : Scheme.{u}) (q : ℤ) :
    (etaleModuleRestrictScalars ρ Z).mapDerivedCategoryPlus ⋙
        DerivedCategory.Plus.homologyFunctor (EtaleModules.{u, 0} Λ Z) q ≅
      DerivedCategory.Plus.homologyFunctor (EtaleModules.{u, 0} Λ' Z) q ⋙
        etaleModuleRestrictScalars ρ Z :=
  NatIso.ofComponents
    (fun K => (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (etaleModuleRestrictScalars ρ Z) q).app (DerivedCategory.Plus.ι.obj K))
    (fun {_ _} g => (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (etaleModuleRestrictScalars ρ Z) q).hom.naturality (DerivedCategory.Plus.ι.map g))

/-- **`res_ρ ∘ R^q f_* ≅ R^q f_* ∘ res_ρ` naturally** ([Stacks, Tag 0D6J] for a change of
constant coefficient rings). -/
@[sga "4½ Th_finitude 2.2" "Clause b)"]
def etaleModuleRightDerivedDirectImageRestrictScalarsNatIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (q : ℕ) :
    (etaleModuleDirectImage.{u, 0} Λ' f).rightDerived q ⋙ etaleModuleRestrictScalars ρ Y ≅
      etaleModuleRestrictScalars ρ X ⋙ (etaleModuleDirectImage.{u, 0} Λ f).rightDerived q :=
  Functor.isoWhiskerRight (Stacks.DerivedIndexing.rightDerivedIso
      (etaleModuleDirectImage.{u, 0} Λ' f) q) (etaleModuleRestrictScalars ρ Y) ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor _ 0 ⋙
        (etaleModuleDirectImage.{u, 0} Λ' f).rightDerivedFunctorPlus)
      (etaleModuleRestrictScalarsPlusHomologyNatIso ρ Y (q : ℤ)).symm ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor _ 0)
      (Functor.isoWhiskerRight (etaleModuleDerivedDirectImageRestrictScalars ρ f)
        (DerivedCategory.Plus.homologyFunctor _ (q : ℤ))) ≪≫
    Functor.isoWhiskerRight
      (Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle (etaleModuleRestrictScalars ρ X) 0)
      ((etaleModuleDirectImage.{u, 0} Λ f).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor _ (q : ℤ)) ≪≫
    Functor.isoWhiskerLeft (etaleModuleRestrictScalars ρ X)
      (Stacks.DerivedIndexing.rightDerivedIso (etaleModuleDirectImage.{u, 0} Λ f) q).symm

end RestrictScalarsNatural

section Algebra

open scoped ChangeOfRings

variable {K A : Type} [Field K] [CommRing A] (φ : K →+* A) {I : Type}
  (b : Module.Basis I K ((ModuleCat.restrictScalars.{0} φ).obj (ModuleCat.of A A)))

/-- The `i`-th basis vector, as an element of the ring `A`. -/
def basisVec (i : I) : A := b i

/-- The `K`-module `A ⊗_K M` obtained by restricting the scalars of the extension of scalars is the
tensor product with its own `K`-module structure: the identity is `K`-linear. -/
def restrictScalarsExtendScalarsLinearEquiv (M : ModuleCat.{u + 1} K) :
    ↑((ModuleCat.restrictScalars.{u + 1} φ).obj ((ModuleCat.extendScalars φ).obj M)) ≃ₗ[K]
      TensorProduct K ((ModuleCat.restrictScalars.{0} φ).obj (ModuleCat.of A A)) M where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- On `A ⊗_K M`, multiplication by a scalar `a` of `A` sends `1 ⊗ m` to `a ⊗ m`. -/
theorem extendScalars_smul_one_tmul (M : ModuleCat.{u + 1} K) (a : A) (m : M) :
    (a • 𝟙 ((ModuleCat.extendScalars φ).obj M)).hom ((1 : A) ⊗ₜ[K,φ] m) = a ⊗ₜ[K,φ] m := by
  simp only [ModuleCat.hom_smul, ModuleCat.hom_id]
  exact (ModuleCat.ExtendScalars.smul_tmul φ a 1 m).trans (by rw [mul_one])

/-- The injections of the direct sum decomposition of `A ⊗_K M`: `m ↦ b_i ⊗ m`. -/
abbrev extendScalarsBasisInj (M : ModuleCat.{u + 1} K) (i : I) :
    M ⟶ (ModuleCat.restrictScalars.{u + 1} φ).obj ((ModuleCat.extendScalars φ).obj M) :=
  (ModuleCat.extendRestrictScalarsAdj φ).unit.app M ≫
    (ModuleCat.restrictScalars.{u + 1} φ).map
      (basisVec φ b i • 𝟙 ((ModuleCat.extendScalars φ).obj M))

/-- The injection `extendScalarsBasisInj φ b M i` sends `m` to `b i ⊗ m`. -/
theorem restrictScalarsExtendScalarsLinearEquiv_extendScalarsBasisInj (M : ModuleCat.{u + 1} K)
    (i : I) (m : M) :
    restrictScalarsExtendScalarsLinearEquiv φ M ((extendScalarsBasisInj φ b M i).hom m) =
      b i ⊗ₜ[K] m :=
  extendScalars_smul_one_tmul φ M (basisVec φ b i) m

/-- The `K`-linear map `A ⊗_K M → T` attached to a family `(s_i : M → T)` and the basis
`(b_i)`: `a ⊗ m ↦ Σ_i a_i s_i(m)`. -/
def extendScalarsBasisDesc (M T : ModuleCat.{u + 1} K) (s : I → (M ⟶ T)) :
    (ModuleCat.restrictScalars.{u + 1} φ).obj ((ModuleCat.extendScalars φ).obj M) ⟶ T :=
  ModuleCat.ofHom
    (X := ↑((ModuleCat.restrictScalars.{u + 1} φ).obj ((ModuleCat.extendScalars φ).obj M)))
    (Y := ↑T) ((TensorProduct.lift (b.constr K (fun i => (s i).hom))).comp
      (restrictScalarsExtendScalarsLinearEquiv φ M).toLinearMap)

/-- **Extension of scalars along `K → A` of a `K`-module `M`, read as a `K`-module, is the direct
sum of copies of `M` indexed by a `K`-basis `(b_i)` of `A`**, with injections `m ↦ b_i ⊗ m`,
that is, the unit `m ↦ 1 ⊗ m` followed by multiplication by `b_i`. -/
def isColimitCofanExtendScalars (M : ModuleCat.{u + 1} K) :
    IsColimit (Cofan.mk ((ModuleCat.restrictScalars.{u + 1} φ).obj
        ((ModuleCat.extendScalars φ).obj M)) (extendScalarsBasisInj φ b M)) := by
  refine Cofan.IsColimit.mk _ (fun s => extendScalarsBasisDesc φ b M s.pt s.inj) (fun s i => ?_)
    (fun s g hg => ?_)
  · ext m
    change TensorProduct.lift (b.constr K (fun i => (s.inj i).hom))
      (restrictScalarsExtendScalarsLinearEquiv φ M ((extendScalarsBasisInj φ b M i).hom m)) = _
    rw [restrictScalarsExtendScalarsLinearEquiv_extendScalarsBasisInj, TensorProduct.lift.tmul,
      Module.Basis.constr_basis]
  · let e := restrictScalarsExtendScalarsLinearEquiv φ M
    have key : g.hom.comp e.symm.toLinearMap =
        TensorProduct.lift (b.constr K (fun i => (s.inj i).hom)) := by
      refine TensorProduct.ext' fun a n => ?_
      let L : (ModuleCat.restrictScalars.{0} φ).obj (ModuleCat.of A A) →ₗ[K] s.pt :=
        (g.hom.comp e.symm.toLinearMap).comp ((TensorProduct.mk K _ _).flip n)
      have hL : L = (b.constr K (fun i => (s.inj i).hom)).flip n := by
        refine b.ext fun i => ?_
        change g.hom (e.symm (b i ⊗ₜ[K] n)) = (b.constr K (fun i => (s.inj i).hom) (b i)) n
        rw [Module.Basis.constr_basis, ← hg i,
          ← restrictScalarsExtendScalarsLinearEquiv_extendScalarsBasisInj φ b M i n,
          LinearEquiv.symm_apply_apply]
        rfl
      change L a = _
      rw [hL, TensorProduct.lift.tmul]
      rfl
    ext x
    have := LinearMap.congr_fun key (e x)
    rwa [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply] at this

end Algebra

section Sheaf

variable {K A : Type} [Field K] [CommRing A] (φ : K →+* A) {I : Type}
  (b : Module.Basis I K ((ModuleCat.restrictScalars.{0} φ).obj (ModuleCat.of A A))) (Z : Scheme.{u})

/-- The injections `m ↦ b_i ⊗ m` are natural in the `K`-module `M`. -/
theorem extendScalarsBasisInj_naturality {M M' : ModuleCat.{u + 1} K} (g : M ⟶ M') (i : I) :
    g ≫ extendScalarsBasisInj φ b M' i =
      extendScalarsBasisInj φ b M i ≫
        (ModuleCat.restrictScalars.{u + 1} φ).map ((ModuleCat.extendScalars φ).map g) := by
  have h := (ModuleCat.extendRestrictScalarsAdj φ).unit.naturality g
  simp only [Functor.id_map, Functor.comp_map] at h
  simp only [extendScalarsBasisInj, ← Category.assoc, h]
  simp only [Category.assoc, ← Functor.map_comp, Linear.smul_comp, Linear.comp_smul,
    Category.id_comp, Category.comp_id]

/-- The presheaf version of the injections `N ⟶ res (ext N)`, sectionwise `n ↦ b_i ⊗ n`. -/
def extendScalarsBasisPresheafInj (N : EtaleModules.{u, 0} K Z) (i : I) :
    N.obj ⟶ N.obj ⋙ ModuleCat.extendScalars φ ⋙ ModuleCat.restrictScalars.{u + 1} φ where
  app U := extendScalarsBasisInj φ b (N.obj.obj U) i
  naturality _ _ g := extendScalarsBasisInj_naturality φ b (N.obj.map g) i

/-- Sectionwise, `res (N ⊗_K A)` is the direct sum of copies of `N` along the basis. -/
def isColimitExtendScalarsBasisPresheafCofan (N : EtaleModules.{u, 0} K Z) :
    IsColimit (Cofan.mk (N.obj ⋙ ModuleCat.extendScalars φ ⋙ ModuleCat.restrictScalars.{u + 1} φ)
      (extendScalarsBasisPresheafInj φ b Z N)) :=
  evaluationJointlyReflectsColimits _ fun U =>
    (IsColimit.equivIsoColimit (Cocone.ext (Iso.refl _) (fun ⟨i⟩ => by
      dsimp [extendScalarsBasisPresheafInj]
      simp))).symm
      (isColimitCofanExtendScalars φ b (N.obj.obj U))

/-- **Extension of scalars of a sheaf of `K`-vector spaces along `K → A`, read as a sheaf of
`K`-vector spaces, is the direct sum of copies of the sheaf** indexed by a `K`-basis `(b_i)` of
`A`, with injections the unit followed by multiplication by `b_i`. -/
def isColimitExtendScalarsBasisCofan (N : EtaleModules.{u, 0} K Z) :
    IsColimit (Cofan.mk
      ((etaleModuleRestrictScalars φ Z).obj ((etaleModuleExtendScalars φ Z).obj N))
      (fun i => (etaleModuleExtendScalarsAdj φ Z).unit.app N ≫
        (etaleModuleRestrictScalars φ Z).map
          ((etaleModuleSMul Z (basisVec φ b i)).app ((etaleModuleExtendScalars φ Z).obj N)))) := by
  let J := Z.smallEtaleTopology
  let P := N.obj ⋙ ModuleCat.extendScalars φ
  let τ := toSheafify J P
  let θ : P ⋙ ModuleCat.restrictScalars.{u + 1} φ ⟶
      ((etaleModuleRestrictScalars φ Z).obj ((etaleModuleExtendScalars φ Z).obj N)).obj :=
    Functor.whiskerRight τ (ModuleCat.restrictScalars.{u + 1} φ)
  have hW : J.W θ := J.W_of_preservesSheafification _ τ (J.W_toSheafify P)
  have hpre := isColimitExtendScalarsBasisPresheafCofan φ b Z N
  have hleg : ∀ i : I, ((etaleModuleExtendScalarsAdj φ Z).unit.app N ≫
      (etaleModuleRestrictScalars φ Z).map
        ((etaleModuleSMul Z (basisVec φ b i)).app ((etaleModuleExtendScalars φ Z).obj N))).hom =
      extendScalarsBasisPresheafInj φ b Z N i ≫ θ := by
    intro i
    have hτ : τ ≫ ((etaleModuleSMul Z (basisVec φ b i)).app
        ((etaleModuleExtendScalars φ Z).obj N)).hom =
        (basisVec φ b i • 𝟙 P) ≫ τ := by
      ext U x
      exact (map_smul (τ.app U).hom (basisVec φ b i) x).symm
    rw [ObjectProperty.FullSubcategory.comp_hom]
    dsimp only [etaleModuleExtendScalarsAdj]
    rw [Sheaf.adjunction_unit_app_hom]
    ext U : 2
    have hU := congr_app hτ U
    simp only [NatTrans.comp_app, NatTrans.app_smul, NatTrans.id_app] at hU
    simp only [extendScalarsBasisPresheafInj, θ, extendScalarsBasisInj]
    change _ ≫ (ModuleCat.restrictScalars.{u + 1} φ).map (τ.app U) ≫
        (ModuleCat.restrictScalars.{u + 1} φ).map (((etaleModuleSMul Z (basisVec φ b i)).app
          ((etaleModuleExtendScalars φ Z).obj N)).hom.app U) = _
    rw [← Functor.map_comp, hU, Functor.map_comp]
    rfl
  have hc : ∀ (T : EtaleModules.{u, 0} K Z) (σ : _ ⟶ T.obj),
      θ ≫ Classical.choose ((hW T.obj T.property).2 σ) = σ :=
    fun T σ => Classical.choose_spec ((hW T.obj T.property).2 σ)
  refine Cofan.IsColimit.mk _ (fun s => ObjectProperty.homMk (Classical.choose
    ((hW s.pt.obj s.pt.property).2 (hpre.desc (Cofan.mk s.pt.obj (fun i => (s.inj i).hom))))))
    (fun s i => ?_) (fun s m hm => ?_)
  · apply Sheaf.hom_ext
    change (((etaleModuleExtendScalarsAdj φ Z).unit.app N ≫ (etaleModuleRestrictScalars φ Z).map
      ((etaleModuleSMul Z (basisVec φ b i)).app ((etaleModuleExtendScalars φ Z).obj N))).hom ≫
        Classical.choose ((hW s.pt.obj s.pt.property).2
          (hpre.desc (Cofan.mk s.pt.obj (fun i => (s.inj i).hom))))) = _
    rw [hleg, Category.assoc, hc]
    exact hpre.fac (Cofan.mk s.pt.obj (fun i => (s.inj i).hom)) ⟨i⟩
  · apply Sheaf.hom_ext
    apply (hW s.pt.obj s.pt.property).1
    change θ ≫ m.hom = θ ≫ Classical.choose ((hW s.pt.obj s.pt.property).2
      (hpre.desc (Cofan.mk s.pt.obj (fun i => (s.inj i).hom))))
    rw [hc]
    refine hpre.uniq (Cofan.mk s.pt.obj (fun i => (s.inj i).hom)) _ (fun ⟨i⟩ => ?_)
    have := Sheaf.hom_ext_iff.1 (hm i)
    change (((etaleModuleExtendScalarsAdj φ Z).unit.app N ≫ (etaleModuleRestrictScalars φ Z).map
      ((etaleModuleSMul Z (basisVec φ b i)).app ((etaleModuleExtendScalars φ Z).obj N))).hom ≫
        m.hom) = (s.inj i).hom at this
    rwa [hleg, Category.assoc] at this

end Sheaf

section Unit

variable {K A : Type} [Field K] [CommRing A] (φ : K →+* A) {I : Type}
  (b : Module.Basis I K ((ModuleCat.restrictScalars.{0} φ).obj (ModuleCat.of A A)))

/-- The `K`-linear map `K → A`, `c ↦ c • 1`, between the universe-lifted modules of rank one. -/
def unitULiftHom :
    ModuleCat.of K (ULift.{u + 1} K) ⟶
      (ModuleCat.restrictScalars.{u + 1} φ).obj (ModuleCat.of A (ULift.{u + 1} A)) :=
  ModuleCat.ofHom (X := ULift.{u + 1} K)
    (Y := ↑((ModuleCat.restrictScalars.{u + 1} φ).obj (ModuleCat.of A (ULift.{u + 1} A))))
    { toFun := fun c => ULift.up (φ c.down)
      map_add' := fun x y => by
        apply ULift.ext
        exact map_add φ x.down y.down
      map_smul' := fun c x => by
        apply ULift.ext
        change φ (c * x.down) = φ c * φ x.down
        exact map_mul φ c x.down }

/-- The `K`-linear map `ULift A → T` attached to a family `(s_i : K → T)` and the basis `(b_i)`. -/
def unitULiftBasisDesc (T : ModuleCat.{u + 1} K) (s : I → (ModuleCat.of K (ULift.{u + 1} K) ⟶ T)) :
    (ModuleCat.restrictScalars.{u + 1} φ).obj (ModuleCat.of A (ULift.{u + 1} A)) ⟶ T :=
  let D : ↑((ModuleCat.restrictScalars.{u + 1} φ).obj (ModuleCat.of A (ULift.{u + 1} A))) →ₗ[K]
      ((ModuleCat.restrictScalars.{0} φ).obj (ModuleCat.of A A)) :=
    { toFun := fun x => x.down
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  ModuleCat.ofHom
    (X := ↑((ModuleCat.restrictScalars.{u + 1} φ).obj (ModuleCat.of A (ULift.{u + 1} A))))
    (Y := ↑T) ((b.constr K (fun i => (s i).hom (ULift.up 1))).comp D)

/-- **The free `A`-module of rank one, read as a `K`-vector space, is the direct sum of copies of
`K` indexed by a `K`-basis `(b_i)` of `A`**, with injections `c ↦ c b_i`, that is, the unit
`K → A` followed by multiplication by `b_i`. -/
def isColimitCofanUnitULift :
    IsColimit (Cofan.mk
      ((ModuleCat.restrictScalars.{u + 1} φ).obj (ModuleCat.of A (ULift.{u + 1} A)))
      (fun i => unitULiftHom.{u} φ ≫ (ModuleCat.restrictScalars.{u + 1} φ).map
        (basisVec φ b i • 𝟙 (ModuleCat.of A (ULift.{u + 1} A))))) := by
  refine Cofan.IsColimit.mk _ (fun s => unitULiftBasisDesc φ b s.pt s.inj) (fun s i => ?_)
    (fun s m hm => ?_)
  · ext c
    change b.constr K (fun i => (s.inj i).hom (ULift.up 1)) (basisVec φ b i * φ c.down) =
      (s.inj i).hom c
    have hc : (basisVec φ b i * φ c.down : A) = (c.down • b i :
        (ModuleCat.restrictScalars.{0} φ).obj (ModuleCat.of A A)) := mul_comm _ _
    rw [hc, map_smul, Module.Basis.constr_basis]
    have : c = c.down • (ULift.up 1 : ULift.{u + 1} K) := by
      apply ULift.ext
      change c.down = c.down * 1
      rw [mul_one]
    conv_rhs => rw [this, map_smul]
  · ext x
    change m.hom x = b.constr K (fun i => (s.inj i).hom (ULift.up 1)) x.down
    let L : (ModuleCat.restrictScalars.{0} φ).obj (ModuleCat.of A A) →ₗ[K] s.pt :=
      { toFun := fun a => m.hom (ULift.up a)
        map_add' := fun x y => map_add m.hom (ULift.up x) (ULift.up y)
        map_smul' := fun c x => map_smul m.hom c (ULift.up x) }
    have hL : L = b.constr K (fun i => (s.inj i).hom (ULift.up 1)) := by
      refine b.ext fun i => ?_
      rw [Module.Basis.constr_basis, ← hm i]
      change m.hom (ULift.up (b i)) = m.hom (ULift.up (basisVec φ b i * φ 1))
      rw [map_one, mul_one]
      rfl
    exact LinearMap.congr_fun hL x.down

end Unit

section Comparison

variable {K A : Type} [Field K] [CommRing A] (φ : K →+* A) {X S : Scheme.{u}} (f : X ⟶ S)
  (q : ℕ)

/-- `R^q f_* K` for the constant sheaf of `K`-vector spaces of rank one. -/
abbrev rightDerivedConstantUnit (Λ : Type) [CommRing Λ] : EtaleModules.{u, 0} Λ S :=
  ((etaleModuleDirectImage.{u, 0} Λ f).rightDerived q).obj
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (ModuleCat.of Λ (ULift.{u + 1} Λ)))

/-- The comparison `R^q f_* K ⟶ R^q f_* A` induced by `K → A`, landing in `R^q f_* A` read as a
sheaf of `K`-vector spaces. -/
def rightDerivedConstantUnitHom :
    rightDerivedConstantUnit f q K ⟶
      (etaleModuleRestrictScalars φ S).obj (rightDerivedConstantUnit f q A) :=
  ((etaleModuleDirectImage.{u, 0} K f).rightDerived q).map
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} K)).map (unitULiftHom.{u} φ) ≫
        ((etaleModuleRestrictScalarsConstantIso φ X).app
          (ModuleCat.of A (ULift.{u + 1} A))).inv) ≫
    ((etaleModuleRightDerivedDirectImageRestrictScalarsNatIso φ f q).app _).inv

/-- The `A`-linear comparison `R^q f_* K ⊗_K A ⟶ R^q f_* A`, adjoint to
`rightDerivedConstantUnitHom`. -/
def extendScalarsRightDerivedConstantUnitHom :
    (etaleModuleExtendScalars φ S).obj (rightDerivedConstantUnit f q K) ⟶
      rightDerivedConstantUnit f q A :=
  ((etaleModuleExtendScalarsAdj φ S).homEquiv _ _).symm (rightDerivedConstantUnitHom φ f q)

/-- **`R^q f_* K ⊗_K A ≅ R^q f_* A`** ([Stacks, Tag 0F0G] for constant coefficients `K → A`, `K` a
field, `f` quasi-compact and quasi-separated): the `A`-linear comparison is an isomorphism. Read
as sheaves of `K`-vector spaces, both sides are direct sums of copies of `R^q f_* K` indexed by a
`K`-basis `(b_i)` of `A`, and the comparison matches the injections. -/
@[sga "4½ Th_finitude 2.2" "Step c), special case"]
theorem isIso_extendScalarsRightDerivedConstantUnitHom [QuasiCompact f] [QuasiSeparated f] :
    IsIso (extendScalarsRightDerivedConstantUnitHom φ f q) := by
  classical
  let b := Module.Free.chooseBasis K ((ModuleCat.restrictScalars.{0} φ).obj (ModuleCat.of A A))
  let I := Module.Free.ChooseBasisIndex K ((ModuleCat.restrictScalars.{0} φ).obj (ModuleCat.of A A))
  let G := rightDerivedConstantUnit f q K
  let H := rightDerivedConstantUnit f q A
  let κ := extendScalarsRightDerivedConstantUnitHom φ f q
  let g := rightDerivedConstantUnitHom φ f q
  let res := etaleModuleRestrictScalars φ S
  let A₁ := ModuleCat.of A (ULift.{u + 1} A)
  let RK := (etaleModuleDirectImage.{u, 0} K f).rightDerived q
  let RA := (etaleModuleDirectImage.{u, 0} A f).rightDerived q
  let cK := constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} K)
  let cA := constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)
  let Ψ := cK ⋙ RK
  have hRE := isColimitExtendScalarsBasisCofan φ b S G
  have : PreservesColimitsOfShape (Discrete I) Ψ := by
    have h1 : PreservesColimitsOfShape (Discrete I) cK :=
      (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} K)
        terminalIsTerminal).leftAdjoint_preservesColimits.preservesColimitsOfShape
    have h2 : PreservesColimitsOfShape (Discrete (ULift.{u + 1} I)) RK :=
      preservesColimitsOfShape_discrete_rightDerived_etaleModuleDirectImage K f q _
    have h2' : PreservesColimitsOfShape (Discrete I) RK :=
      preservesColimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) RK
    infer_instance
  have hΨ := isColimitCofanMkObjOfIsColimit Ψ _ _ (isColimitCofanUnitULift.{u} φ b)
  let iso1 := (etaleModuleRestrictScalarsConstantIso φ X).app A₁
  let iso2 := (etaleModuleRightDerivedDirectImageRestrictScalarsNatIso φ f q).app (cA.obj A₁)
  let e : Ψ.obj ((ModuleCat.restrictScalars.{u + 1} φ).obj A₁) ≅ res.obj H :=
    RK.mapIso iso1.symm ≪≫ iso2.symm
  have he : ∀ m : A₁ ⟶ A₁, Ψ.map ((ModuleCat.restrictScalars.{u + 1} φ).map m) ≫ e.hom =
      e.hom ≫ res.map (RA.map (cA.map m)) := by
    intro m
    have n1 : cK.map ((ModuleCat.restrictScalars.{u + 1} φ).map m) ≫ iso1.inv =
        iso1.inv ≫ (etaleModuleRestrictScalars φ X).map (cA.map m) :=
      (etaleModuleRestrictScalarsConstantIso φ X).inv.naturality m
    have n2 : RK.map ((etaleModuleRestrictScalars φ X).map (cA.map m)) ≫ iso2.inv =
        iso2.inv ≫ res.map (RA.map (cA.map m)) :=
      (etaleModuleRightDerivedDirectImageRestrictScalarsNatIso φ f q).inv.naturality (cA.map m)
    change RK.map (cK.map ((ModuleCat.restrictScalars.{u + 1} φ).map m)) ≫
        RK.map iso1.inv ≫ iso2.inv = (RK.map iso1.inv ≫ iso2.inv) ≫ res.map (RA.map (cA.map m))
    rw [← RK.map_comp_assoc, n1, RK.map_comp, Category.assoc, n2, Category.assoc]
  have hg : g = Ψ.map (unitULiftHom.{u} φ) ≫ e.hom := by
    change RK.map (cK.map (unitULiftHom.{u} φ) ≫ iso1.inv) ≫ iso2.inv =
      RK.map (cK.map (unitULiftHom.{u} φ)) ≫ RK.map iso1.inv ≫ iso2.inv
    rw [RK.map_comp, Category.assoc]
  have hsmul : ∀ i : I, RA.map (cA.map (basisVec φ b i • 𝟙 A₁)) =
      (etaleModuleSMul S (basisVec φ b i)).app H := by
    intro i
    have : (basisVec φ b i • 𝟙 A₁) = ModuleCat.ofHom (basisVec φ b i • LinearMap.id) := rfl
    rw [this]
    change RA.map ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).map
      (ModuleCat.ofHom (basisVec φ b i • LinearMap.id))) = _
    rw [(etaleModuleSMul_app_constantSheaf X (basisVec φ b i) A₁).symm]
    exact rightDerived_etaleModuleDirectImage_map_etaleModuleSMul f _ q _
  have hH : IsColimit (Cofan.mk (res.obj H)
      (fun i => g ≫ res.map ((etaleModuleSMul S (basisVec φ b i)).app H))) := by
    refine IsColimit.ofIsoColimit hΨ (Cofan.ext e (fun i => ?_))
    change Ψ.map (unitULiftHom.{u} φ ≫ (ModuleCat.restrictScalars.{u + 1} φ).map
        (basisVec φ b i • 𝟙 A₁)) ≫ e.hom = g ≫ res.map ((etaleModuleSMul S (basisVec φ b i)).app H)
    rw [Ψ.map_comp, Category.assoc, he, hsmul, hg, Category.assoc]
  have hκ : ∀ i : I, ((etaleModuleExtendScalarsAdj φ S).unit.app G ≫
      res.map ((etaleModuleSMul S (basisVec φ b i)).app
        ((etaleModuleExtendScalars φ S).obj G))) ≫ res.map κ =
      g ≫ res.map ((etaleModuleSMul S (basisVec φ b i)).app H) := by
    intro i
    have hn := (etaleModuleSMul S (basisVec φ b i)).naturality κ
    simp only [Functor.id_map] at hn
    have hu : (etaleModuleExtendScalarsAdj φ S).unit.app G ≫ res.map κ = g :=
      ((etaleModuleExtendScalarsAdj φ S).homEquiv_unit G H κ).symm.trans
        (Equiv.apply_symm_apply _ _)
    rw [Category.assoc, ← res.map_comp, ← hn, res.map_comp, ← Category.assoc, hu]
  let φc : Cofan.mk (res.obj ((etaleModuleExtendScalars φ S).obj G))
      (fun i => (etaleModuleExtendScalarsAdj φ S).unit.app G ≫
        res.map ((etaleModuleSMul S (basisVec φ b i)).app ((etaleModuleExtendScalars φ S).obj G))) ⟶
      Cofan.mk (res.obj H) (fun i => g ≫ res.map ((etaleModuleSMul S (basisVec φ b i)).app H)) :=
    { hom := res.map κ
      w := fun ⟨i⟩ => hκ i }
  have : IsIso φc := IsColimit.hom_isIso hRE hH φc
  have : IsIso (res.map κ) := (Cocone.forget _).map_isIso φc
  exact isIso_of_reflects_iso κ res

end Comparison

section Constructible

attribute [local instance] moduleCat_hasLimitsOfSize SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

variable (B : BigEtaleSite.{u}) (S : B.Scheme) {K A : Type} [CommRing K] [CommRing A]
  [IsNoetherianRing K] [IsNoetherianRing A] (φ : K →+* A)

/-- **Stacks 0GKB on Mathlib's small étale site**: extension of scalars along a homomorphism of
Noetherian rings preserves constructibility. Reading sheaves on the small étale site of Stacks
021B commutes with restriction of scalars, hence with its left adjoint, extension of scalars. -/
theorem isConstructibleEtaleModule_etaleModuleExtendScalars (G : EtaleModules.{u, 0} K S.obj)
    (hG : IsBigSiteConstructibleEtaleModule B S K G) :
    IsBigSiteConstructibleEtaleModule B S A ((etaleModuleExtendScalars φ S.obj).obj G) := by
  let := SmallEtale.hasSheafify_moduleCat.{u, 0, 0} B S K
  let := SmallEtale.hasSheafify_moduleCat.{u, 0, 0} B S A
  let J := SmallEtale.topology B S.obj S.property
  let eK := SmallEtale.sheafEquiv B S.obj S.property (ModuleCat.{u + 1} K)
  let eA := SmallEtale.sheafEquiv B S.obj S.property (ModuleCat.{u + 1} A)
  let adjB := Sheaf.adjunction J (ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, 0} φ)
  let adj1 := (etaleModuleExtendScalarsAdj φ S.obj).comp eA.symm.toAdjunction
  let adj2 := eK.symm.toAdjunction.comp adjB
  let adj2' := adj2.ofNatIsoRight (sheafEquivRestrictScalarsIso B S.obj S.property φ).symm
  let iso := adj1.leftAdjointUniq adj2'
  exact isConstructibleModuleSheaf_congr B A S (iso.app G).symm
    (isConstructibleModuleSheaf_extendScalars.{u, u + 1, 0, 0} B S K A φ
      ((etaleModulesToSmallEtale B S K).obj G) hG)

end Constructible

section ZeroGKW

attribute [local instance] moduleCat_hasLimitsOfSize SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

variable (B : BigEtaleSite.{u}) {X S : B.Scheme} (f : X.obj ⟶ S.obj) [QuasiCompact f]
  [QuasiSeparated f]

/-- **From `𝐙/ℓ` coefficients to Noetherian `𝐙/ℓ`-algebras.** If `R^q f_* 𝐙/ℓ` is constructible
for every prime `ℓ` and every `q`, then `R^q f_* A` is a constructible sheaf of `A`-modules for
every Noetherian ring `A` in which `ℓ = 0`: it is `R^q f_* 𝐙/ℓ ⊗_{𝐙/ℓ} A`
(`Stacks.EtaleCohomology.isIso_extendScalarsRightDerivedConstantUnitHom`), and extension of
scalars preserves constructibility ([Stacks, Tag 0GKB]). -/
@[sga "4 XIV 1.11" "partial"]
theorem isConstructibleEtaleModule_rightDerivedConstantUnit_of_zmod
    (hℓ : ∀ ℓ : ℕ, ℓ.Prime → ∀ q : ℕ,
      IsBigSiteConstructibleEtaleModule B S (ZMod ℓ) (rightDerivedConstantUnit f q (ZMod ℓ)))
    (ℓ : ℕ) (hp : ℓ.Prime) (A : Type) [CommRing A] [IsNoetherianRing A] (hA : (ℓ : A) = 0)
    (q : ℕ) : IsBigSiteConstructibleEtaleModule B S A (rightDerivedConstantUnit f q A) := by
  have : Fact ℓ.Prime := ⟨hp⟩
  let φ : ZMod ℓ →+* A :=
    (Ideal.Quotient.lift (Ideal.span {(ℓ : ℤ)}) (Int.castRingHom A) (fun a ha => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      rw [map_mul, map_natCast, hA, mul_zero])).comp
      (Int.quotientSpanNatEquivZMod ℓ).symm.toRingHom
  have hQ := isWeakSerreClass_isBigSiteConstructibleEtaleModule B S A
  have := isIso_extendScalarsRightDerivedConstantUnitHom φ f q
  exact (IsBigSiteConstructibleEtaleModule B S A).prop_of_iso
    (asIso (extendScalarsRightDerivedConstantUnitHom φ f q))
    (isConstructibleEtaleModule_etaleModuleExtendScalars B S φ _ (hℓ ℓ hp q))

/-- **[Stacks, Tag 0GKW] from [Stacks, Tag 0GKV].** Let `f : X ⟶ S` be quasi-compact and
quasi-separated and `Λ` a Noetherian ring. If `R^q f_* 𝐙/ℓ` is constructible for every prime `ℓ`
and every `q` (which is [Stacks, Tag 0GKV] for `f` proper smooth with geometrically connected
fibres of dimension `1`), then `R^q f_* M` is a constructible sheaf of `Λ`-modules for every
finite `Λ`-module `M` annihilated by a positive integer and every `q`. -/
theorem isConstructibleEtaleModule_rightDerived_constantSheaf_of_zmod (Λ : Type) [CommRing Λ]
    [IsNoetherianRing Λ]
    (hℓ : ∀ ℓ : ℕ, ℓ.Prime → ∀ q : ℕ,
      IsBigSiteConstructibleEtaleModule B S (ZMod ℓ) (rightDerivedConstantUnit f q (ZMod ℓ)))
    (n : ℕ) (hn : 0 < n) (M : ModuleCat.{u + 1} Λ) (hM : Module.Finite Λ M)
    (hnM : ∀ m : M, n • m = 0) (q : ℕ) :
    IsBigSiteConstructibleEtaleModule B S Λ
      (((etaleModuleDirectImage.{u, 0} Λ f).rightDerived q).obj
        ((constantSheaf X.obj.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) :=
  isConstructibleEtaleModule_rightDerived_constantSheaf_of_unit B f Λ
    (fun ℓ hp A _ _ hA q => isConstructibleEtaleModule_rightDerivedConstantUnit_of_zmod B f hℓ ℓ hp
      A hA q) n hn M hM hnM q

end ZeroGKW

end Stacks.EtaleCohomology

end
