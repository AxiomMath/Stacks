module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.TopTraceFibre
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.RootsOfUnityModuleCohomology
public import StacksFrontier.CategoryTheory.Sites.Point.ConstantSheafFiber
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.SmoothFlat
public import StacksFrontier.Topology.Dimension.LocalKrullDim

/-!
# The top-degree trace of the Kummer class of the diagonal

Let `f : X ⟶ S` be proper, smooth of relative dimension one, with geometrically irreducible
fibres, `N ≥ 1` invertible on `X`, and `ζ` a primitive `N`-th root of unity of a field `k` over
which `Y = X ×_S X` lies. The Kummer class `δ[𝒪(Δ)] ∈ H²(Y, μ_N)` of the diagonal
(`Stacks.Kummer.diagonalKummerClass`), read through `μ_N ≅ ℤ/N` (`m ↦ ζ^m`) and the bijection
`Ext²_Λ(Λ_Y, Λ_Y) ≅ H²(Y, ℤ/N)` (`Stacks.EtaleCohomology.extForgetSheafHAddEquiv`), is a class
`c ∈ Ext²(Λ_Y, Λ_Y)` of sheaves of `Λ = ℤ/N`-modules
(`Stacks.EtaleCohomology.TopTrace.diagonalModuleClass`).

For the second projection `pr₂ : Y ⟶ X` the top-degree trace `ν : G ⟶ R²pr₂_*(pr₂⁻¹G)` of `c`
(`Stacks.EtaleCohomology.TopTrace.trace`) is an isomorphism for every sheaf of `Λ`-modules `G`
on `X` (`Stacks.EtaleCohomology.TopTrace.isIso_trace_diagonalModuleClass`):

* at `G = Λ` the edge map of `c` is the edge map of the Kummer class of the diagonal
  (`Stacks.EtaleCohomology.TopTrace.single_comp_edgeHom_unit`), which generates at every geometric
  point (`Stacks.EtaleCohomology.isZModGenerator_homologyMap_diagonalEdge`, the degree of a point
  of a curve is one);
* by proper base change the trace restricted to a geometric fibre is the trace of the restricted
  class, invertible at `Λ` and hence everywhere
  (`Stacks.EtaleCohomology.TopTrace.isIso_trace_of_isSeparator`);
* `Stacks.EtaleCohomology.TopTrace.isIso_trace_of_fibres` concludes.

This is the global step of the construction of the top-degree trace of a relative curve in the
proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

The derived categories are those of the standard model `HasDerivedCategory.standard`.

## Main definitions

* `Stacks.EtaleCohomology.TopTrace.diagonalModuleClass`.

## Main results

* `Stacks.ExtUnitAction.action_tensorUnit`: the action of `c` on the unit is `c`.
* `Stacks.EtaleCohomology.TopTrace.flatFibres_constantModuleSheaf`.
* `Stacks.EtaleCohomology.TopTrace.isIso_edge_of_isIso_inverseImage_edge`: the converse of
  `Stacks.EtaleCohomology.TopTrace.isIso_inverseImage_edge`.
* `Stacks.EtaleCohomology.TopTrace.isIso_trace_diagonalModuleClass`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory
open AlgebraicGeometry Opposite

universe w v u

namespace Stacks.ExtUnitAction

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [HasExt.{w} C]
  [EnoughInjectives C]

/-- **The action of `c ∈ Ext^n(𝟙, 𝟙)` on the unit is `c`**: `- ⊗ 𝟙` is the identity through the
right unitor, and the two unitors of `𝟙` agree. -/
theorem action_tensorUnit {n : ℕ} (c : Ext.{w} (𝟙_ C) (𝟙_ C) n)
    [(MonoidalCategory.tensorRight (𝟙_ C)).Additive]
    [PreservesFiniteLimits (MonoidalCategory.tensorRight (𝟙_ C))]
    [PreservesFiniteColimits (MonoidalCategory.tensorRight (𝟙_ C))] :
    action c (𝟙_ C) = c := by
  let ρn : MonoidalCategory.tensorRight (𝟙_ C) ≅ 𝟭 C :=
    NatIso.ofComponents (fun X => ρ_ X) (fun f => by simp)
  have key := Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor ρn.hom (𝟙_ C) n c
  rw [Stacks.ExtFunctorial.mapExactFunctor_id] at key
  rw [action_eq_sandwich, unitors_equal, unitors_inv_equal]
  exact (eq_sandwich_of_mk₀_comp (ρ_ (𝟙_ C)) (ρ_ (𝟙_ C)).hom c _ key).symm

end Stacks.ExtUnitAction

namespace Stacks.EtaleCohomology.TopTrace

attribute [local instance] HasDerivedCategory.standard Sheaf.monoidalCategory
  isMonoidal_W_etaleModules isGrothendieckAbelian_sheaf_smallEtale_objectUniverse
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits

/-! ### Generalities -/

/-- **The constant sheaf has flat fibres**: the fibre of the constant sheaf `ℤ/N` is `ℤ/N`. -/
theorem flatFibres_constantModuleSheaf {N : ℕ} (S : Scheme.{u}) :
    FlatFibres (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N)
      S.smallEtaleTopology) := by
  intro Ω _ _ s
  have : Module.Flat (ZMod N) (ULift.{u + 1} (ZMod N)) :=
    Module.Flat.of_linearEquiv (ULift.moduleEquiv (R := ZMod N) (M := ZMod N))
  let _ : PreservesFilteredColimitsOfSize.{u + 1, u + 1} (forget (ModuleCat.{u + 1} (ZMod N))) := by
    show PreservesFilteredColimitsOfSize
      (forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat.{u + 1} ⋙ forget AddCommGrpCat.{u + 1})
    infer_instance
  exact Module.Flat.of_linearEquiv (CategoryTheory.Sites.constantSheafFiberIso
    ((Scheme.pointSmallEtale s).ulift.{u + 1})
      (ModuleCat.of (ZMod N) (ULift.{u + 1} (ZMod N)))).toLinearEquiv

/-- The fibres of a morphism smooth of relative dimension one have dimension `≤ 1`. -/
theorem topologicalKrullDim_fiber_le_one {X S : Scheme.{u}} (p : X ⟶ S)
    [SmoothOfRelativeDimension 1 p] (s : S) : topologicalKrullDim (p.fiber s) ≤ 1 := by
  rw [TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
  refine iSup_le fun z => ?_
  rw [← TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim,
    topologicalKrullDimAt_fiber_eq_of_smoothOfRelativeDimension p 1 s z]
  simp

/-- **A criterion for a morphism out of a constant sheaf to be an isomorphism**: `v : A ⟶ G` with
`ε : ℤ ⟶ A`, such that at the geometric point of every point the morphisms `ℤ ⟶ x̄⁻¹A` form a group
of order `n` and the restriction of `ε ≫ v` generates the morphisms `ℤ ⟶ x̄⁻¹G` as a cyclic group
of order `n`. -/
theorem isIso_of_isZModGenerator_at {S : Scheme.{u}} {n : ℕ} [NeZero n]
    {A G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}} (v : A ⟶ G) (ε : intSheaf S ⟶ A)
    (hA : ∀ x : S, Nat.card (intSheaf (Spec (.of (GeometricPoint.ofPoint S x).residueField)) ⟶
      (etaleAbelianInverseImage.{u, 0} (GeometricPoint.ofPoint S x).hom).obj A) = n)
    (hG : ∀ x : S, IsZModGenerator n
      ((intSheafInverseImageIso (GeometricPoint.ofPoint S x).hom).inv ≫
        (etaleAbelianInverseImage.{u, 0} (GeometricPoint.ofPoint S x).hom).map (ε ≫ v))) :
    IsIso v := by
  refine isIso_of_geometricStalkAb_family
    (Ω := fun x : S => (GeometricPoint.ofPoint S x).residueField)
    (fun x : S => (GeometricPoint.ofPoint S x).hom) ?_ v (fun x => ?_)
  · exact Set.eq_univ_of_forall fun s =>
      Set.mem_iUnion.2 ⟨s, default, GeometricPoint.ofPoint_liesOver S s⟩
  refine isIso_stalk_of_isIso_etaleAbelianInverseImage_map (GeometricPoint.ofPoint S x) v ?_
  set y := (GeometricPoint.ofPoint S x).hom
  refine isIso_of_bijective_comp_intSheaf _ _ ?_
  obtain ⟨e, he⟩ := hG x
  set g := (intSheafInverseImageIso y).inv ≫ (etaleAbelianInverseImage.{u, 0} y).map (ε ≫ v)
  set d := (intSheafInverseImageIso y).inv ≫ (etaleAbelianInverseImage.{u, 0} y).map ε
  have hd : d ≫ (etaleAbelianInverseImage.{u, 0} y).map v = g := by
    simp only [d, g, Category.assoc, ← Functor.map_comp]
  have hsurj : Function.Surjective
      (fun z : intSheaf (Spec (.of (GeometricPoint.ofPoint S x).residueField)) ⟶
        (etaleAbelianInverseImage.{u, 0} y).obj A =>
          z ≫ (etaleAbelianInverseImage.{u, 0} y).map v) := by
    intro c
    refine ⟨(e c).val • d, ?_⟩
    have hc : c = (e c).val • g := e.injective (by
      rw [map_nsmul, he, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val])
    simp only [Preadditive.nsmul_comp, hd]
    exact hc.symm
  have : Finite (intSheaf (Spec (.of (GeometricPoint.ofPoint S x).residueField)) ⟶
      (etaleAbelianInverseImage.{u, 0} y).obj A) :=
    Nat.finite_of_card_ne_zero (hA x ▸ NeZero.ne n)
  refine hsurj.bijective_of_nat_card_le ?_
  rw [hA x, Nat.card_congr e.toEquiv, Nat.card_zmod]

/-- **The converse of `Stacks.EtaleCohomology.TopTrace.isIso_inverseImage_edge`**: for a cartesian
square with `p` proper and `A` with flat fibres, the edge map of `g'⁻¹ c` at `g⁻¹ A` is invertible
as soon as `g⁻¹ Θ_A` is (proper base change, Tag 0DDE). -/
theorem isIso_edge_of_isIso_inverseImage_edge {N : ℕ} {Y Y' B B' : Scheme.{u}} (g' : Y' ⟶ Y)
    (c : Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod N) Y)) (𝟙_ _) 2) (p : Y ⟶ B) (g : B' ⟶ B)
    (p' : Y' ⟶ B') [IsProper p] (hN : N ≠ 0) (sq : IsPullback g' p' p g)
    (A : EtaleModules.{u, 0} (ZMod N) B) (hA : FlatFibres A)
    (h : IsIso ((etaleAbelianInverseImage.{u, 0} g).map (edge p c A (hA.inverseImage p)))) :
    IsIso (edge p' (pullClass g' c) _ ((hA.inverseImage g).inverseImage p')) := by
  obtain ⟨z, hz⟩ := exists_edgeHom_baseChange g' c p g p' sq.w A hA
  have : IsIso ((etaleAbelianDerivedBaseChange.{u, 0} p g g' p'
      ((rfl : g' ≫ p = g' ≫ p).symm.trans sq.w)).app (((DerivedCategory.singleFunctor _ 0).obj
        ((etaleModuleUnderlyingAbelian Y (ZMod N)).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod N) p).obj A)))⟦((2 : ℕ) : ℤ)⟧)) :=
    isIso_etaleAbelianDerivedBaseChange_of_isProper p sq _ (-2)
      (DerivedCategory.TStructure.t.isGE_shift _ 0 2 (-2) (by omega))
      (torsionCohomologyProperty_shift_single hN _)
  -- `g⁻¹` of `H⁰` of the derived edge map is invertible
  have h4 : IsIso ((etaleAbelianInverseImage.{u, 0} g).map
      ((DerivedCategory.homologyFunctor _ 0).map (edgeHom p c A (hA.inverseImage p)))) := by
    rw [← isIso_comp_left_iff ((etaleAbelianInverseImage.{u, 0} g).map
      (singleHomologyZeroIso ((etaleModuleUnderlyingAbelian B (ZMod N)).obj A)).hom),
      ← Functor.map_comp]
    exact h
  -- `H⁰` of the base-changed derived edge map is invertible
  have hnat := (StacksDraft.PseudoCoherence.mapDerivedCategoryHomologyIso
    (etaleAbelianInverseImage.{u, 0} g) 0).hom.naturality (edgeHom p c A (hA.inverseImage p))
  simp only [Functor.comp_map] at hnat
  have h3 : IsIso ((DerivedCategory.homologyFunctor _ 0).map
      ((etaleAbelianDerivedInverseImage.{u, 0} g).map (edgeHom p c A (hA.inverseImage p)))) := by
    rw [← isIso_comp_right_iff _ ((StacksDraft.PseudoCoherence.mapDerivedCategoryHomologyIso
      (etaleAbelianInverseImage.{u, 0} g) 0).hom.app _), hnat]
    infer_instance
  have h2 := congrArg (DerivedCategory.homologyFunctor _ 0).map hz
  simp only [Functor.map_comp] at h2
  have h1 : IsIso ((DerivedCategory.homologyFunctor _ 0).map
      (edgeHom p' (pullClass g' c) _ ((hA.inverseImage g).inverseImage p'))) := by
    rw [← isIso_comp_left_iff ((DerivedCategory.homologyFunctor _ 0).map
      (inverseImageSingleIso g A).hom), ← h2]
    infer_instance
  have := h1
  exact (inferInstance : IsIso ((singleHomologyZeroIso
    ((etaleModuleUnderlyingAbelian B' (ZMod N)).obj
      ((etaleModuleInverseImage.{u, 0} (ZMod N) g).obj A))).hom ≫
      (DerivedCategory.homologyFunctor _ 0).map
        (edgeHom p' (pullClass g' c) _ ((hA.inverseImage g).inverseImage p'))))

/-- **The action of a class on the constant sheaf is the class itself**, read in the derived
category of abelian sheaves. -/
private theorem classHom_constantModuleSheaf {Y : Scheme.{u}} {N : ℕ}
    (c : Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod N) Y)) (𝟙_ _) 2)
    (hΛ : FlatFibres (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N)
      Y.smallEtaleTopology)) :
    classHom c (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N)
      Y.smallEtaleTopology) hΛ =
      (c.mapExactFunctor (etaleModuleUnderlyingAbelian Y (ZMod N))).hom := by
  show classHom c (𝟙_ _) hΛ = _
  let := etaleModules_enoughInjectives.{u, 0} (ZMod N) Y
  have := hΛ.exact.1
  have := hΛ.exact.2.1
  have := hΛ.exact.2.2
  unfold classHom
  rw [Stacks.ExtUnitAction.action_tensorUnit]

/-! ### The class -/

section Class

variable {k : Type u} [Field k] {S X : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
  [SmoothOfRelativeDimension 1 f] {N : ℕ} (hN0 : N ≠ 0)
  (hY : IsUnit ((N : ℕ) : Γ(pullback f f, ⊤))) (qY : pullback f f ⟶ Spec (.of k)) {ζ : k}
  (hζ : IsPrimitiveRoot ζ N)

/-- `U(ℤ/N) ≅ μ_N` through `m ↦ ζ^m` (`Stacks.Kummer.etaleModuleConstantUnderlyingIso`), with the
target in the universe of `Stacks.Kummer.diagonalKummerClass`. -/
def constantUnderlyingRootsOfUnityIso {Y : Scheme.{u}} (qY : Y ⟶ Spec (.of k)) {N : ℕ}
    (hN0 : N ≠ 0) {ζ : k} (hζ : IsPrimitiveRoot ζ N) :
    (etaleModuleUnderlyingAbelian Y (ZMod N)).obj
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N) Y.smallEtaleTopology) ≅
      Stacks.Kummer.rootsOfUnitySheaf.{u, u + 1} Y N :=
  Stacks.Kummer.etaleModuleConstantUnderlyingIso qY hζ hN0

/-- **The Kummer class of the diagonal as a class of sheaves of `ℤ/N`-modules**: `δ[𝒪(Δ)]`, read
in `H²(Y, ℤ/N)` through `μ_N ≅ ℤ/N` (`m ↦ ζ^m`), and in `Ext²(Λ_Y, Λ_Y)` through the bijection
`Stacks.EtaleCohomology.extForgetSheafHAddEquiv`. -/
def diagonalModuleClass :
    Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod N) (pullback f f))) (𝟙_ _) 2 :=
  (extForgetSheafHAddEquiv (ZMod N) (pullback f f)
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N)
        (pullback f f).smallEtaleTopology) 2).symm
    ((Stacks.Kummer.diagonalKummerClass f hN0 hY).comp
      (Ext.mk₀ (constantUnderlyingRootsOfUnityIso qY hN0 hζ).inv) (add_zero 2))

/-- **The defining property of the class**: under the forgetful functor and `ℤ ⟶ ℤ/N`, it is the
Kummer class of the diagonal read in `H²(Y, ℤ/N)`. -/
theorem mk₀_comp_mapExactFunctor_diagonalModuleClass :
    (Ext.mk₀ (etaleModuleUnderlyingAbelianConstantMap (ZMod N) (pullback f f))).comp
        ((diagonalModuleClass f hN0 hY qY hζ).mapExactFunctor
          (etaleModuleUnderlyingAbelian (pullback f f) (ZMod N))) (zero_add 2) =
      (Stacks.Kummer.diagonalKummerClass f hN0 hY).comp
        (Ext.mk₀ (constantUnderlyingRootsOfUnityIso qY hN0 hζ).inv) (add_zero 2) :=
  (extForgetSheafHAddEquiv (ZMod N) (pullback f f)
    (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N)
      (pullback f f).smallEtaleTopology) 2).apply_symm_apply _

/-- **The action of the class on `pr₂⁻¹ Λ_X`, precomposed with `ℤ ⟶ ℤ/N`, is the Kummer class of
the diagonal**, up to the identification `μ_N ≅ ℤ/N ≅ pr₂⁻¹ ℤ/N`. -/
theorem inverseImage_single_comp_classHom
    (hF : FlatFibres ((etaleModuleInverseImage.{u, 0} (ZMod N) (pullback.snd f f)).obj
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N) X.smallEtaleTopology))) :
    (etaleAbelianDerivedInverseImage.{u, 0} (pullback.snd f f)).map
        ((DerivedCategory.singleFunctor _ 0).map
          (etaleModuleUnderlyingAbelianConstantMap (ZMod N) X)) ≫
      (inverseImageSingleIso (pullback.snd f f)
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N) X.smallEtaleTopology)).hom ≫
        classHom (diagonalModuleClass f hN0 hY qY hζ) _ hF =
    (inverseImageSingleIntSheafIso (pullback.snd f f)).hom ≫
      (Stacks.Kummer.diagonalKummerClass f hN0 hY).hom ≫
        ((DerivedCategory.singleFunctor _ 0).map
          ((constantUnderlyingRootsOfUnityIso qY hN0 hζ).inv ≫
            (etaleModuleUnderlyingAbelian (pullback f f) (ZMod N)).map
              ((etaleModuleInverseImageConstantIso.{u, 0} (ZMod N) (pullback.snd f f)).inv.app
                (ModuleCat.of (ZMod N) (ULift.{u + 1} (ZMod N))))))⟦((2 : ℕ) : ℤ)⟧' := by
  set pr := pullback.snd f f
  set c := diagonalModuleClass f hN0 hY qY hζ
  set U := etaleModuleUnderlyingAbelian (pullback f f) (ZMod N)
  set ψ := (etaleModuleInverseImageConstantIso.{u, 0} (ZMod N) pr).inv.app
    (ModuleCat.of (ZMod N) (ULift.{u + 1} (ZMod N)))
  have hΛ : FlatFibres (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N)
      (pullback f f).smallEtaleTopology) := flatFibres_constantModuleSheaf _
  have hL' : (etaleAbelianInverseImage.{u, 0} pr).map
        (etaleModuleUnderlyingAbelianConstantMap (ZMod N) X) ≫
      (etaleModuleUnderlyingAbelianInverseImageIso (ZMod N) pr).hom.app
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N) X.smallEtaleTopology) =
      (etaleAbelianInverseImageConstantIso.{u, 0} pr).hom.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ≫
        etaleModuleUnderlyingAbelianConstantMap (ZMod N) (pullback f f) ≫ U.map ψ := by
    rw [etaleModuleUnderlyingAbelianConstantMap_comp_inverseImageConstantIso,
      Iso.hom_inv_id_app_assoc]
  have hcl₀ := congrArg Ext.hom (mk₀_comp_mapExactFunctor_diagonalModuleClass f hN0 hY qY hζ)
  have e1 := Ext.comp_hom
    (Ext.mk₀ (etaleModuleUnderlyingAbelianConstantMap (ZMod N) (pullback f f)))
    (c.mapExactFunctor U) (zero_add 2)
  have e2 := Ext.comp_hom (Stacks.Kummer.diagonalKummerClass f hN0 hY)
    (Ext.mk₀ (constantUnderlyingRootsOfUnityIso qY hN0 hζ).inv) (add_zero 2)
  have hcl := e1.symm.trans (hcl₀.trans e2)
  simp only [Ext.mk₀_hom, ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀] at hcl
  have hcl2 : (DerivedCategory.singleFunctor _ 0).map
        (etaleModuleUnderlyingAbelianConstantMap (ZMod N) (pullback f f)) ≫
        classHom c (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N)
          (pullback f f).smallEtaleTopology) hΛ =
      (Stacks.Kummer.diagonalKummerClass f hN0 hY).hom ≫
        ((DerivedCategory.singleFunctor _ 0).map
          (constantUnderlyingRootsOfUnityIso qY hN0 hζ).inv)⟦((2 : ℕ) : ℤ)⟧' := by
    rwa [classHom_constantModuleSheaf]
  have hs := ((etaleAbelianInverseImage.{u, 0} pr).mapDerivedCategorySingleFunctor 0).hom.naturality
    (etaleModuleUnderlyingAbelianConstantMap (ZMod N) X)
  simp only [Functor.comp_map] at hs
  simp only [inverseImageSingleIso, inverseImageSingleNatIso, inverseImageSingleIntSheafIso,
    Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Iso.symm_hom, Functor.associator_hom_app,
    Functor.associator_inv_app, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.id_comp, Category.comp_id, Category.assoc]
  rw [reassoc_of% hs, ← Functor.map_comp_assoc, hL', Functor.map_comp, Functor.map_comp,
    Category.assoc, Category.assoc, classHom_naturality c hΛ hF ψ, reassoc_of% hcl2,
    Functor.map_comp, Functor.map_comp]

end Class

/-! ### The edge map at the unit generates -/

section Generator

variable {k : Type u} [Field k] {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
  [SmoothOfRelativeDimension 1 f] [GeometricallyIrreducible f] {N : ℕ} [NeZero N]
  (hX : IsUnit ((N : ℕ) : Γ(X, ⊤))) (hY : IsUnit ((N : ℕ) : Γ(pullback f f, ⊤)))
  (qY : pullback f f ⟶ Spec (.of k)) {ζ : k} (hζ : IsPrimitiveRoot ζ N)

omit [GeometricallyIrreducible f] in
/-- **The edge map of the class at `Λ`, precomposed with `ℤ ⟶ ℤ/N`, is the edge map of the
Kummer class of the diagonal**, up to the identification `μ_N ≅ pr₂⁻¹ ℤ/N`. -/
theorem single_comp_edgeHom_unit
    (hF : FlatFibres ((etaleModuleInverseImage.{u, 0} (ZMod N) (pullback.snd f f)).obj
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N) X.smallEtaleTopology))) :
    (DerivedCategory.singleFunctor _ 0).map (etaleModuleUnderlyingAbelianConstantMap (ZMod N) X) ≫
        edgeHom (pullback.snd f f) (diagonalModuleClass f (NeZero.ne N) hY qY hζ)
          (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N) X.smallEtaleTopology) hF =
      diagonalEdge f (NeZero.ne N) hY ≫
        (etaleAbelianDerivedDirectImage.{u, 0} (pullback.snd f f)).map
          (((DerivedCategory.singleFunctor _ 0).map
            ((constantUnderlyingRootsOfUnityIso qY (NeZero.ne N) hζ).inv ≫
              (etaleModuleUnderlyingAbelian (pullback f f) (ZMod N)).map
                ((etaleModuleInverseImageConstantIso.{u, 0} (ZMod N) (pullback.snd f f)).inv.app
                  (ModuleCat.of (ZMod N) (ULift.{u + 1} (ZMod N))))))⟦((2 : ℕ) : ℤ)⟧') := by
  rw [edgeHom, diagonalEdge, ← Adjunction.homEquiv_naturality_left,
    ← Adjunction.homEquiv_naturality_right, diagonalKummerShiftedHom, Category.assoc,
    ← inverseImage_single_comp_classHom f (NeZero.ne N) hY qY hζ hF]
  rfl

/-- **The morphisms `ℤ ⟶ x̄⁻¹ ℤ/N` form a group of order `N`** at the geometric point of every
point `x`. -/
private theorem natCard_hom_intSheaf_inverseImage_constantModuleSheaf {N : ℕ} (X : Scheme.{u})
    (x : X) :
    Nat.card (intSheaf (Spec (.of (GeometricPoint.ofPoint X x).residueField)) ⟶
      (etaleAbelianInverseImage.{u, 0} (GeometricPoint.ofPoint X x).hom).obj
        ((etaleModuleUnderlyingAbelian X (ZMod N)).obj
          (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N) X.smallEtaleTopology))) =
      N := by
  let i := (etaleAbelianInverseImage.{u, 0} (GeometricPoint.ofPoint X x).hom).mapIso
      ((Stacks.ModuleCatLift.constantSheafForget₂Iso.{u + 1} (ZMod N) X.smallEtaleTopology).app
        (ModuleCat.of (ZMod N) (ULift.{u + 1} (ZMod N)))) ≪≫
    (etaleAbelianInverseImageConstantIso.{u, 0} (GeometricPoint.ofPoint X x).hom).app
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod N)))
  refine (Nat.card_congr (Iso.homCongr (Iso.refl _) i)).trans ?_
  rw [natCard_hom_intSheaf_constantSheaf, Nat.card_ulift, Nat.card_zmod]

/-- If `N` is invertible on `X`, it is invertible in the residue field of the geometric point of
every point `x`. -/
private theorem isUnit_natCast_residueField_ofPoint {X : Scheme.{u}} {N : ℕ}
    (hX : IsUnit (N : Γ(X, ⊤))) (x : X) :
    IsUnit (N : (GeometricPoint.ofPoint X x).residueField) := by
  have := (hX.map ((X.presheaf.germ ⊤ x trivial ≫ X.residue x).hom)).map
    (algebraMap (X.residueField x) (AlgebraicClosure (X.residueField x)))
  rwa [map_natCast, map_natCast] at this

include hX in
/-- **The edge map of the class at `Λ` is an isomorphism**: at every geometric point of `X` its
restriction generates `H²` of the geometric fibre, a cyclic group of order `N`. -/
theorem isIso_edge_unit
    (hF : FlatFibres ((etaleModuleInverseImage.{u, 0} (ZMod N) (pullback.snd f f)).obj
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N) X.smallEtaleTopology))) :
    IsIso (edge (pullback.snd f f) (diagonalModuleClass f (NeZero.ne N) hY qY hζ)
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N) X.smallEtaleTopology) hF) := by
  set ε := etaleModuleUnderlyingAbelianConstantMap (ZMod N) X
  set J := (DerivedCategory.singleFunctor _ 0).mapIso
    ((constantUnderlyingRootsOfUnityIso qY (NeZero.ne N) hζ).symm ≪≫
      (etaleModuleUnderlyingAbelian (pullback f f) (ZMod N)).mapIso
        ((etaleModuleInverseImageConstantIso.{u, 0} (ZMod N) (pullback.snd f f)).app
          (ModuleCat.of (ZMod N) (ULift.{u + 1} (ZMod N)))).symm)
  refine isIso_of_isZModGenerator_at (n := N) _ ε (fun x => ?_) (fun x => ?_)
  · exact natCard_hom_intSheaf_inverseImage_constantModuleSheaf X x
  · set y := (GeometricPoint.ofPoint X x).hom
    have h := isZModGenerator_homologyMap_diagonalEdge f (NeZero.ne N) hY y
      (isUnit_natCast_residueField_ofPoint hX x)
    have hE : ε ≫ (singleHomologyZeroIso _).hom ≫ (DerivedCategory.homologyFunctor _ 0).map
        (edgeHom (pullback.snd f f) (diagonalModuleClass f (NeZero.ne N) hY qY hζ)
          (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N) X.smallEtaleTopology) hF) =
        (singleHomologyZeroIso (intSheaf X)).hom ≫
          (DerivedCategory.homologyFunctor _ 0).map (diagonalEdge f (NeZero.ne N) hY) ≫
            (DerivedCategory.homologyFunctor _ 0).map
              ((etaleAbelianDerivedDirectImage.{u, 0} (pullback.snd f f)).map
                (J.hom⟦((2 : ℕ) : ℤ)⟧')) := by
      rw [reassoc_of% (singleHomologyZeroIso_hom_naturality ε), ← Functor.map_comp,
        ← Functor.map_comp]
      exact congrArg _ (congrArg _ (single_comp_edgeHom_unit f hY qY hζ hF))
    let ν := StacksDraft.PseudoCoherence.mapDerivedCategoryHomologyIso
      (etaleAbelianInverseImage.{u, 0} y) 0
    have hnat := ν.hom.naturality (diagonalEdge f (NeZero.ne N) hY)
    simp only [Functor.comp_map] at hnat
    let I₁ := (intSheafInverseImageIso y).symm ≪≫
      (etaleAbelianInverseImage.{u, 0} y).mapIso (singleHomologyZeroIso (intSheaf X)) ≪≫
      (ν.app ((DerivedCategory.singleFunctor _ 0).obj (intSheaf X))).symm
    let I₂ := ν.app ((etaleAbelianDerivedDirectImage.{u, 0} (pullback.snd f f)).obj
        (((DerivedCategory.singleFunctor _ 0).obj
          (Stacks.Kummer.rootsOfUnitySheaf.{u, u + 1} (pullback f f) N))⟦(2 : ℤ)⟧)) ≪≫
      (etaleAbelianInverseImage.{u, 0} y).mapIso ((DerivedCategory.homologyFunctor _ 0).mapIso
        ((etaleAbelianDerivedDirectImage.{u, 0} (pullback.snd f f)).mapIso
          ((shiftFunctor _ ((2 : ℕ) : ℤ)).mapIso J)))
    have key : (intSheafInverseImageIso y).inv ≫ (etaleAbelianInverseImage.{u, 0} y).map
        (ε ≫ edge (pullback.snd f f) (diagonalModuleClass f (NeZero.ne N) hY qY hζ)
          (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N) X.smallEtaleTopology) hF) =
        I₁.hom ≫ (DerivedCategory.homologyFunctor _ 0).map
          ((etaleAbelianDerivedInverseImage.{u, 0} y).map (diagonalEdge f (NeZero.ne N) hY)) ≫
            I₂.hom := by
      show (intSheafInverseImageIso y).inv ≫ (etaleAbelianInverseImage.{u, 0} y).map
        (ε ≫ (singleHomologyZeroIso _).hom ≫ (DerivedCategory.homologyFunctor _ 0).map
          (edgeHom (pullback.snd f f) (diagonalModuleClass f (NeZero.ne N) hY qY hζ)
            (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N)
              X.smallEtaleTopology) hF)) = _
      rw [hE]
      simp only [I₁, I₂, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom,
        Iso.app_inv, Category.assoc, Functor.map_comp]
      rw [reassoc_of% hnat, Iso.inv_hom_id_app_assoc]
    rw [key]
    exact h.map (isoHomAddEquiv I₁ I₂)

include hX in
/-- **The top-degree trace of the class is an isomorphism**: for every sheaf `G` of `ℤ/N`-modules
on `X`, `ν_G : G ⟶ R²pr₂_*(pr₂⁻¹G)` is invertible. -/
theorem isIso_trace_diagonalModuleClass (G : EtaleModules.{u, 0} (ZMod N) X) :
    IsIso ((trace (pullback.snd f f) (diagonalModuleClass f (NeZero.ne N) hY qY hζ)).app G) := by
  have hN : N ≠ 0 := NeZero.ne N
  have : SmoothOfRelativeDimension 1 (pullback.snd f f) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback f f) inferInstance
  set c := diagonalModuleClass f hN hY qY hζ
  have hF : FlatFibres ((etaleModuleInverseImage.{u, 0} (ZMod N) (pullback.snd f f)).obj
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N) X.smallEtaleTopology)) :=
    (flatFibres_constantModuleSheaf X).inverseImage _
  have := isIso_edge_unit f hX hY qY hζ hF
  refine isIso_trace_of_fibres (pullback.snd f f) (topologicalKrullDim_fiber_le_one _) hN c
    (fun b A hA => ?_) G
  set x := (GeometricPoint.ofPoint X b).hom
  have : SmoothOfRelativeDimension 1 (pullback.snd (pullback.snd f f) x) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback (pullback.snd f f) x) inferInstance
  have sq := IsPullback.of_hasPullback (pullback.snd f f) x
  -- the edge map at `x̄⁻¹Λ` on the fibre is invertible
  have h1 : IsIso (edge (pullback.snd (pullback.snd f f) x)
      (pullClass (pullback.fst (pullback.snd f f) x) c) _
        (((flatFibres_constantModuleSheaf X).inverseImage x).inverseImage _)) :=
    isIso_edge_of_isIso_inverseImage_edge _ c (pullback.snd f f) x _ hN sq _
      (flatFibres_constantModuleSheaf X) inferInstance
  have h2 : IsIso ((trace (pullback.snd (pullback.snd f f) x)
      (pullClass (pullback.fst (pullback.snd f f) x) c)).app
        ((etaleModuleInverseImage.{u, 0} (ZMod N) x).obj
          (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N)
            X.smallEtaleTopology))) := by
    rw [trace_app_eq_edge _ _ _
      (((flatFibres_constantModuleSheaf X).inverseImage x).inverseImage _)]
    exact h1
  -- `x̄⁻¹Λ ≅ Λ` is a separator
  have hsep : IsSeparator ((etaleModuleInverseImage.{u, 0} (ZMod N) x).obj
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N) X.smallEtaleTopology)) :=
    isSeparator_of_iso ((etaleModuleInverseImageConstantIso.{u, 0} (ZMod N) x).app
      (ModuleCat.of (ZMod N) (ULift.{u + 1} (ZMod N))))
      (isSeparator_constantModuleSheaf _ N)
  have h3 := isIso_trace_of_isSeparator (pullback.snd (pullback.snd f f) x)
    (topologicalKrullDim_fiber_le_one _) hN
    (pullClass (pullback.fst (pullback.snd f f) x) c) _ hsep
    ((etaleModuleInverseImage.{u, 0} (ZMod N) x).obj A)
  rwa [trace_app_eq_edge] at h3

end Generator

end Stacks.EtaleCohomology.TopTrace
