module

public import StacksFrontier.Algebra.Homology.DerivedCategory.TopTruncationExtDegreeZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LowerShriekGlobalTranspose
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.PointClassNonzero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ProperCohomologyExtComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.InducedCompactification

/-!
# The class of a point as a morphism over the base field

Let `f : V → Spec k` have a compactification `j : V → X̄`, let `Λ = ℤ/N` and let `A`, `B` be
sheaves of `Λ`-modules on `V`. For `e ∈ Ext^m_V(A, B)`, some `z ∈ Ext⁰_X̄(Λ, j_! A)` has
`j_!(e) ∘ z ≠ 0` exactly when some morphism `ẑ : Λ_k[0] ⟶ Rf_!(A[0])` of `D⁺(Spec k)` has
`Rf_!(e) ∘ ẑ ≠ 0` (`Stacks.EtaleCohomology.exists_comp_derivedLowerShriek_map_ne_zero_iff`): the
transpose `Stacks.EtaleCohomology.unitHomEquivLowerShriek` moves the test morphism to the base
field, and `Rj_!` is exact in degree zero
(`Stacks.TopTruncationExt.exists_comp_map_extPlus_ne_zero_iff`).

So the class of a `k`-point `i : P → V` is nonzero in `H^{2e}_c(V)`
(`Stacks.EtaleCohomology.PointClassNonzeroAt` with `N = V`) exactly when some
`β ∈ Ext^{2e}_V(i_* Λ_P, Λ_V)` and some `ẑ : Λ_k[0] ⟶ Rf_!((i_* Λ_P)[0])` have `Rf_!(β) ∘ ẑ ≠ 0`
(`Stacks.EtaleCohomology.pointClassNonzeroAt_id_iff`). In this form the class can be pushed along
the Leray isomorphism `Rf_! ≅ Rq_! ∘ Rg_!` of a factorization, in degree zero, in the proof of the
step of the class of a point through an elementary fibration
(proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

The statements consume `Rf_!`, defined in the standard model `HasDerivedCategory.standard` of the
derived category, which is therefore a local instance here.

## Main results

* `Stacks.EtaleCohomology.exists_comp_derivedLowerShriek_map_ne_zero_iff`.
* `Stacks.EtaleCohomology.pointClassNonzeroAt_id_iff`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

open ExtensionTorsor

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
  Stacks.DerivedIndexing.isTriangulated_rightDerivedFunctorPlus

variable {k : Type u} [Field k] {V : Scheme.{u}} (f : V ⟶ Spec (.of k))
  (jc : CompactificationOf (Over.mk f)) (N : ℕ)

/-- `H⁰(Rj_!((-)[0])) ≅ j_!`, extension by zero being exact. -/
def extensionByZeroTopHomologyIso :
    Stacks.TopTruncationExt.topHomology
        (etaleModuleDerivedExtensionByZero.{u, 0} (ZMod N) jc.immersion ⋙
          DerivedCategory.Plus.ι) 0 ≅
      etaleModuleExtensionByZero.{u, 0} (ZMod N) jc.immersion :=
  (Iso.refl _ : _ ≅ (DerivedCategory.Plus.singleFunctor _ 0 ⋙
      etaleModuleDerivedExtensionByZero.{u, 0} (ZMod N) jc.immersion) ⋙
        (DerivedCategory.Plus.ι ⋙ DerivedCategory.homologyFunctor _ 0)) ≪≫
    Functor.isoWhiskerRight (Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
      (etaleModuleExtensionByZero.{u, 0} (ZMod N) jc.immersion) 0).symm _ ≪≫
    (Iso.refl _ : _ ≅ etaleModuleExtensionByZero.{u, 0} (ZMod N) jc.immersion ⋙
      (DerivedCategory.singleFunctor _ 0 ⋙ DerivedCategory.homologyFunctor _ 0)) ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0) ≪≫
    Functor.rightUnitor _

/-- `Rj_!(M[0]) ≅ (j_! M)[0]`, read in `D(X̄)`. -/
def extensionByZeroSingleIso (M : EtaleModules.{u, 0} (ZMod N) V) :
    DerivedCategory.Plus.ι.obj ((etaleModuleDerivedExtensionByZero.{u, 0} (ZMod N)
        jc.immersion).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj M)) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod N) jc.immersion).obj M) :=
  DerivedCategory.Plus.ι.mapIso ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
    (etaleModuleExtensionByZero.{u, 0} (ZMod N) jc.immersion) 0).app M).symm

theorem isLE_extensionByZero_single (M : EtaleModules.{u, 0} (ZMod N) V) :
    (DerivedCategory.Plus.ι.obj ((etaleModuleDerivedExtensionByZero.{u, 0} (ZMod N)
        jc.immersion).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj M))).IsLE 0 :=
  DerivedCategory.TStructure.t.isLE_of_iso (extensionByZeroSingleIso f jc N M).symm 0

theorem isGE_extensionByZero_single (M : EtaleModules.{u, 0} (ZMod N) V) :
    (DerivedCategory.Plus.ι.obj ((etaleModuleDerivedExtensionByZero.{u, 0} (ZMod N)
        jc.immersion).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj M))).IsGE 0 :=
  DerivedCategory.TStructure.t.isGE_of_iso (extensionByZeroSingleIso f jc N M).symm 0

/-- **A class through `Rf_!` is nonzero against some morphism `Λ_k[0] ⟶ Rf_!(A[0])` exactly when
its extension by zero is nonzero against some class of `Ext⁰_X̄(Λ, j_! A)`.** Here `G` is any
exact functor isomorphic to `j_!`. -/
theorem exists_comp_derivedLowerShriek_map_ne_zero_iff
    (G : EtaleModules.{u, 0} (ZMod N) V ⥤ EtaleModules.{u, 0} (ZMod N) jc.space) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (θ : G ≅ etaleModuleExtensionByZero.{u, 0} (ZMod N) jc.immersion)
    {A B : EtaleModules.{u, 0} (ZMod N) V} {m : ℕ} (e : Ext A B m) :
    (∃ w₀ : (DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := Spec (.of k)) N) ⟶
        (derivedLowerShriek.{u, 0} f jc (ZMod N)).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj A),
      w₀ ≫ (derivedLowerShriek.{u, 0} f jc (ZMod N)).map (Stacks.TopTruncationExt.extPlus e) ≠ 0) ↔
      ∃ z : Ext (unitSheaf (X := jc.space) N) (G.obj A) 0,
        z.comp (e.mapExactFunctor G) (zero_add m) ≠ 0 := by
  let Rj := etaleModuleDerivedExtensionByZero.{u, 0} (ZMod N) jc.immersion
  rw [← Stacks.TopTruncationExt.exists_comp_map_extPlus_ne_zero_iff (Rj ⋙ DerivedCategory.Plus.ι)
    (isLE_extensionByZero_single f jc N) (isGE_extensionByZero_single f jc N) G
    (extensionByZeroTopHomologyIso f jc N ≪≫ θ.symm) (unitSheaf (X := jc.space) N) e]
  rw [(unitHomEquivLowerShriek f jc N _).surjective.exists]
  simp only [← unitHomEquivLowerShriek_comp, Ne, unitHomEquivLowerShriek_eq_zero_iff]
  constructor
  · rintro ⟨ψ, h⟩
    refine ⟨DerivedCategory.Plus.ι.map ψ, fun h' => h ?_⟩
    apply DerivedCategory.Plus.ι.map_injective
    rw [Functor.map_comp, Functor.map_zero]
    simp only [ShiftedHom.map] at h'
    exact (cancel_mono (((Rj ⋙ DerivedCategory.Plus.ι).commShiftIso (m : ℤ)).hom.app _)).1
      ((Category.assoc _ _ _).trans (h'.trans zero_comp.symm))
  · rintro ⟨φ, h⟩
    obtain ⟨ψ, rfl⟩ := (DerivedCategory.Plus.ι.map_surjective : Function.Surjective
      (DerivedCategory.Plus.ι.map : ((DerivedCategory.Plus.singleFunctor _ 0).obj
        (unitSheaf (X := jc.space) N) ⟶ Rj.obj ((DerivedCategory.Plus.singleFunctor _ 0).obj A)) →
          _)) φ
    refine ⟨ψ, fun h' => h ?_⟩
    have h'' := congrArg DerivedCategory.Plus.ι.map h'
    rw [Functor.map_comp, Functor.map_zero] at h''
    simp only [ShiftedHom.map]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) h'').trans zero_comp)

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- **The class of a point of `V` is nonzero, read over the base field**: with `N = V`, the class
of `i : P → V` is nonzero in `H^{2e}_c(V)` exactly when some `β ∈ Ext^{2e}_V(i_* Λ_P, Λ_V)` and
some `ẑ : Λ_k[0] ⟶ Rf_!((i_* Λ_P)[0])` have `Rf_!(β) ∘ ẑ ≠ 0`. -/
theorem pointClassNonzeroAt_id_iff (e : ℕ) {P : Scheme.{u}} (i : P ⟶ V) :
    PointClassNonzeroAt ℓ e f jc (𝟙 V) i ↔
      ∃ (β : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := P) ℓ))
          (unitSheaf (X := V) ℓ) (2 * e))
        (w₀ : (DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := Spec (.of k)) ℓ) ⟶
          (derivedLowerShriek.{u, 0} f jc (ZMod ℓ)).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj
              ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := P) ℓ)))),
        w₀ ≫ (derivedLowerShriek.{u, 0} f jc (ZMod ℓ)).map
          (Stacks.TopTruncationExt.extPlus β) ≠ 0 := by
  let j' := 𝟙 V ≫ jc.immersion
  let E : etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) j' ≅
      etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion :=
    etaleModuleExtensionByZeroCompIso (ZMod ℓ) (𝟙 V) jc.immersion ≪≫
      Functor.isoWhiskerRight (etaleModuleExtensionByZeroIdIso (ZMod ℓ) V) _ ≪≫
      Functor.leftUnitor _
  let θ₀ := E.app (unitSheaf (X := V) ℓ)
  let κ : unitSheaf (X := V) ℓ ⟶ (etaleModuleRestriction.{u, 0} (ZMod ℓ) j').obj
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj (unitSheaf (X := V) ℓ)) :=
    (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) j').unit.app _ ≫
      (etaleModuleRestriction.{u, 0} (ZMod ℓ) j').map θ₀.hom
  have : Mono j' := inferInstanceAs (Mono (𝟙 V ≫ jc.immersion))
  have : IsIso (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) j').unit := inferInstance
  have hgen : ∀ (X : EtaleModules.{u, 0} (ZMod ℓ) V)
      (T : EtaleModules.{u, 0} (ZMod ℓ) jc.space)
      (θ : (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) j').obj X ≅ T),
      IsIso ((etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) j').unit.app X ≫
        (etaleModuleRestriction.{u, 0} (ZMod ℓ) j').map θ.hom) ∧
      (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) j').map
          ((etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) j').unit.app X ≫
            (etaleModuleRestriction.{u, 0} (ZMod ℓ) j').map θ.hom) ≫
        (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) j').counit.app T = θ.hom := by
    intro X T θ
    refine ⟨inferInstance, ?_⟩
    have h := ((etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) j').homEquiv X T).symm_apply_apply
      θ.hom
    rwa [Adjunction.homEquiv_unit, Adjunction.homEquiv_counit] at h
  have : IsIso κ := (hgen _ _ θ₀).1
  have hcounit : (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) j').map κ ≫
      (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) j').counit.app _ = θ₀.hom :=
    (hgen _ _ θ₀).2
  have key : ∀ β : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := P) ℓ))
      (unitSheaf (X := V) ℓ) (2 * e),
      Stacks.ExtAdjunction.extMap (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) j') _ _ (2 * e)
          (β.comp (Ext.mk₀ κ) (add_zero _)) =
        (β.mapExactFunctor (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) j')).comp
          (Ext.mk₀ θ₀.hom) (add_zero _) := by
    intro β
    rw [Stacks.ExtAdjunction.extMap_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
      Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, hcounit]
  have hQ := fun β : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj
      (unitSheaf (X := P) ℓ)) (unitSheaf (X := V) ℓ) (2 * e) =>
    exists_comp_derivedLowerShriek_map_ne_zero_iff f jc ℓ
      (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) j') E β
  constructor
  · rintro ⟨γ₀, z, h⟩
    refine ⟨γ₀.comp (Ext.mk₀ (inv κ)) (add_zero _), (hQ _).2 ⟨z, fun h' => h ?_⟩⟩
    have hγ : γ₀ = (γ₀.comp (Ext.mk₀ (inv κ)) (add_zero _)).comp (Ext.mk₀ κ) (add_zero _) := by
      rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, IsIso.inv_hom_id, Ext.comp_mk₀_id]
    rw [hγ, key, ← Ext.comp_assoc_of_third_deg_zero, h', Ext.zero_comp]
  · rintro ⟨β, w₀, h⟩
    obtain ⟨z, hz⟩ := (hQ β).1 ⟨w₀, h⟩
    refine ⟨β.comp (Ext.mk₀ κ) (add_zero _), z, ?_⟩
    rw [key, ← Ext.comp_assoc_of_third_deg_zero]
    intro h'
    apply hz
    have h'' := congrArg (fun x => x.comp (Ext.mk₀ θ₀.inv) (add_zero _)) h'
    simpa only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Iso.hom_inv_id,
      Ext.comp_mk₀_id, Ext.zero_comp] using h''

end Stacks.EtaleCohomology

end
