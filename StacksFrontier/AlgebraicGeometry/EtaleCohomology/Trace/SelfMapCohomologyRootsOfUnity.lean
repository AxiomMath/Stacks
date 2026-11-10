module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapCohomologyExtTwist
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ConstantTwistComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.RootsOfUnityModuleCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnityPullbackDegree
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage

/-!
# The pullback action `φ^*` on `Hⁱ(Y, ℤ/n)` is pullback on `Hⁱ(Y, μ_n)`

Let `k` be a field containing a primitive `n`-th root of unity `ζ`, let `g : Y ⟶ Spec k` be a
scheme over `k` and let `φ : Y ⟶ Y` be an endomorphism over `k`. The pullback action `φ^*` on
`RΓ(Y, ℤ/n) = RΓ(Spec k, Rg_*(g^{-1} ℤ/n))` (`Stacks.EtaleCohomology.selfMapCohomologyEndo`, the
action whose trace Step 9 of the proof of [Stacks, Tag 03UG] computes) is, on cohomology and
under the choice of `ζ`, the pullback

`φ^* : Hⁱ(Y, μ_n) ⟶ Hⁱ(Y, μ_n)`,

restriction along `φ` followed by the comparison `φ^{-1} μ_n ≅ μ_n`
(`Stacks.EtaleCohomology.rootsOfUnityPullbackMap`). This is the identification
`Hⁱ(C, ℤ/ℓⁿ) ≅ Hⁱ(C, μ_{ℓⁿ})` "compatibly with the action of the geometric Frobenius" of the
proof of [Stacks, Tag 03U3], and it is what lets the degree computations `H¹(C, μ_n) = Pic(C)[n]`
and `H²(C, μ_n) = Pic(C)/n` read off the traces of `φ^*`.

Two identities of constant sheaves go into it. At the level of sheaves of `ℤ/n`-modules, the
self-map twist of `g^{-1} ℤ/n`, transported to `ℤ/n_Y`, is adjoint to the comparison
`φ^{-1} ℤ/n_Y ≅ ℤ/n_Y` (`Stacks.EtaleCohomology.map_selfMapTwist_constant_comp_counit`): both send
the constant section to the constant section. At the level of abelian sheaves, the comparison of
constant sheaves is the comparison `φ^{-1} μ_n ⟶ μ_n` under `m ↦ ζ^m`
(`Stacks.EtaleCohomology.underlyingInverseImageConstant_comp_rootsOfUnity`), because `φ` is a
morphism over `k` and so pulls `ζ` back to `ζ`. None of the declarations here is registered.

## Main definitions

* `Stacks.EtaleCohomology.selfMapCohomologyRootsOfUnityAddEquiv`: `Hⁱ(RΓ(Y, ℤ/n)) ≃+ Hⁱ(Y, μ_n)`.

## Main results

* `Stacks.EtaleCohomology.selfMapCohomologyRootsOfUnityAddEquiv_selfMapCohomologyEndo`: under it,
  `φ^*` is `Stacks.EtaleCohomology.rootsOfUnityPullbackMap φ n i`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section Module

variable (Λ : Type) [CommRing Λ] {Y S : Scheme.{u}} (f : Y ⟶ S) (φ : Y ⟶ Y) (w : φ ≫ f = f)

/-- **The self-map twist of a pulled back constant sheaf is the comparison of constant sheaves**:
transported along `f^{-1} M_S ≅ M_Y`, the map `φ^{-1} f^{-1} M_S ⟶ f^{-1} M_S` adjoint to the
self-map twist is the comparison `φ^{-1} M_Y ≅ M_Y`. Both send the constant section to the
constant section. -/
theorem map_selfMapTwist_constant_comp_counit (M : ModuleCat.{u + 1} Λ) :
    (etaleModuleInverseImage.{u, 0} Λ φ).map
        ((inverseImageEtaleModuleConstantSheafIso.{u, 0} Λ M f).inv ≫
          (selfMapTwist.{u, 0} Λ f φ w).app (etaleModuleConstantSheaf Λ M S)) ≫
      (etaleModuleInverseImageAdj.{u, 0} Λ φ).counit.app _ ≫
      (inverseImageEtaleModuleConstantSheafIso.{u, 0} Λ M f).hom =
    (inverseImageEtaleModuleConstantSheafIso.{u, 0} Λ M φ).hom := by
  apply ((etaleModuleInverseImageAdj.{u, 0} Λ φ).homEquiv _ _).injective
  have hL : (etaleModuleInverseImageAdj.{u, 0} Λ φ).homEquiv _ _
      ((etaleModuleInverseImage.{u, 0} Λ φ).map
          ((inverseImageEtaleModuleConstantSheafIso.{u, 0} Λ M f).inv ≫
            (selfMapTwist.{u, 0} Λ f φ w).app (etaleModuleConstantSheaf Λ M S)) ≫
      (etaleModuleInverseImageAdj.{u, 0} Λ φ).counit.app _ ≫
      (inverseImageEtaleModuleConstantSheafIso.{u, 0} Λ M f).hom) =
      transportedConstantTwist.{u, 0} Λ M f φ
        ((selfMapTwist.{u, 0} Λ f φ w).app (etaleModuleConstantSheaf Λ M S)) := by
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
      Adjunction.homEquiv_unit]
    simp only [Functor.comp_obj, Adjunction.right_triangle_components, Category.id_comp,
      Category.assoc]
  rw [hL]
  obtain ⟨ρ₀, hτ⟩ := exists_pulledBackConstantSection_comp_selfMapTwist Λ M f φ w
  refine constantSheaf_hom_ext Λ M ?_
  refine (constantSheafSection_comp_transportedConstantTwist Λ M f φ _ ρ₀ hτ).trans ?_
  exact (constantSheafSection_comp_constantSelfMapTwist Λ M φ).symm

end Module

section RootsOfUnity

variable {k : Type u} [Field k] {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k)) {n : ℕ} {ζ : k}
  (hζ : IsPrimitiveRoot ζ n) (hn : n ≠ 0)

/-- The constant sheaf `ℤ/n_Y` of `ℤ/n`-modules on `Y`. -/
local notation "ΛY" => Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod n)
  Y.smallEtaleTopology

/-- **The map `ℤ_Y ⟶ U ℤ/n_Y ≅ μ_n ⊆ 𝐆_m`, read on a final object `V`**: it sends `z` to `ζ^z`. -/
theorem homEquiv_constantMap_comp_constantUnderlyingIso {V : Y.Etale} (hV : IsTerminal V) :
    (etaleAbelianConstantAdj Y hV).homEquiv _ _
        (etaleModuleUnderlyingAbelianConstantMap (ZMod n) Y ≫
          (Stacks.Kummer.etaleModuleConstantUnderlyingIso g hζ hn).hom ≫
          Stacks.Kummer.rootsOfUnityι.{u, 0} Y n) =
      uliftIntToULiftHom (ZMod n) ≫ (Stacks.Kummer.rootPresheafHom g hζ hn).app (op V) := by
  have h : etaleModuleUnderlyingAbelianConstantMap (ZMod n) Y ≫
        (Stacks.Kummer.etaleModuleConstantUnderlyingIso g hζ hn).hom ≫
        Stacks.Kummer.rootsOfUnityι.{u, 0} Y n =
      (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).map (uliftIntToULiftHom (ZMod n)) ≫
        Stacks.Kummer.rootSheafHom g hζ hn := by
    simp only [etaleModuleUnderlyingAbelianConstantMap,
      Stacks.Kummer.etaleModuleConstantUnderlyingIso,
      Iso.trans_hom, Iso.app_hom, Category.assoc, Iso.inv_hom_id_app_assoc,
      Stacks.Kummer.rootsOfUnityConstantIso, asIso_hom,
      Stacks.Kummer.rootsOfUnityConstantHom_comp_ι]
  rw [h, Adjunction.homEquiv_naturality_left, Stacks.ConstantSheaf.constantSheafAdj_homEquiv_apply]
  congr 1
  exact congrArg (fun t => t.app (op V)) (Stacks.Kummer.toSheafify_rootSheafHom g hζ hn)

/-- The `n`-th root `ζ` pulled back along an endomorphism `φ` over `k`: the projection
`φ^* V ⟶ V` carries `ζ` on `V` to `ζ` on `φ^* V`. -/
theorem map_rootOn_pullbackFst (φ : Y ⟶ Y) (w : φ ≫ g = g) (V : Y.Etale) :
    Units.map (pullback.fst V.hom φ).appTop.hom.toMonoidHom (Stacks.Kummer.rootOn g hζ hn V) =
      Stacks.Kummer.rootOn g hζ hn ((smallEtaleBaseChange φ).obj V) := by
  have hs : (pullback.fst V.hom φ).appTop.hom.comp (Stacks.Kummer.structMap g V) =
      Stacks.Kummer.structMap g ((smallEtaleBaseChange φ).obj V) := by
    rw [Stacks.Kummer.structMap, Stacks.Kummer.structMap, ← CommRingCat.hom_comp]
    congr 1
    rw [Category.assoc, Category.assoc, ← Scheme.Hom.comp_appTop]
    change _ ≫ g.appTop ≫ (pullback.fst V.hom φ ≫ V.hom).appTop =
      _ ≫ g.appTop ≫ (pullback.snd V.hom φ).appTop
    rw [pullback.condition, Scheme.Hom.comp_appTop, ← Category.assoc g.appTop,
      ← Scheme.Hom.comp_appTop, w]
  rw [Stacks.Kummer.rootOn, Stacks.Kummer.rootOn, ← hs]
  rfl

/-- Forgetting the module structure commutes with direct image on the nose: both are
precomposition with base change followed by forgetting. -/
def etaleModuleUnderlyingAbelianDirectImageHom {X : Scheme.{u}} (Λ : Type) [CommRing Λ]
    (φ : Y ⟶ X) (M : EtaleModules.{u, 0} Λ Y) :
    (etaleModuleUnderlyingAbelian X Λ).obj ((etaleModuleDirectImage.{u, 0} Λ φ).obj M) ⟶
      (etaleAbelianDirectImage.{u, 0} φ).obj ((etaleModuleUnderlyingAbelian Y Λ).obj M) :=
  𝟙 _

/-- **The comparison of constant sheaves is the comparison on `μ_n`**: for an endomorphism `φ`
of `Y` over `k`, the comparison `φ^{-1} ℤ/n_Y ≅ ℤ/n_Y` of constant sheaves of `ℤ/n`-modules, read
on the underlying abelian sheaves, is the comparison `φ^{-1} μ_n ⟶ μ_n` under `m ↦ ζ^m`. -/
theorem underlyingInverseImageConstant_comp_rootsOfUnity (φ : Y ⟶ Y) (w : φ ≫ g = g) :
    (etaleModuleUnderlyingAbelianInverseImageIso (ZMod n) φ).hom.app ΛY ≫
      (etaleModuleUnderlyingAbelian Y (ZMod n)).map
        (inverseImageEtaleModuleConstantSheafIso.{u, 0} (ZMod n)
          (ModuleCat.of (ZMod n) (ULift.{u + 1} (ZMod n))) φ).hom ≫
      (Stacks.Kummer.etaleModuleConstantUnderlyingIso g hζ hn).hom =
    (etaleAbelianInverseImage.{u, 0} φ).map
        (Stacks.Kummer.etaleModuleConstantUnderlyingIso g hζ hn).hom ≫
      Stacks.Kummer.rootsOfUnityInverseImageComparison.{u, 0} φ n := by
  rw [← cancel_mono (Stacks.Kummer.rootsOfUnityι.{u, 0} Y n), Category.assoc, Category.assoc,
    Category.assoc, Stacks.Kummer.rootsOfUnityInverseImageComparison_comp_rootsOfUnityι,
    ← Functor.map_comp_assoc]
  apply ((etaleAbelianInverseImageDirectImageAdj.{u, 0} φ).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left,
    Stacks.Kummer.multiplicativeInverseImageComparison_transpose]
  -- the left side is `U` of the canonical twist of `ℤ/n_Y`, followed by `φ_*(c ≫ ι)`
  have hL : (etaleAbelianInverseImageDirectImageAdj.{u, 0} φ).homEquiv _ _
      ((etaleModuleUnderlyingAbelianInverseImageIso (ZMod n) φ).hom.app ΛY ≫
        (etaleModuleUnderlyingAbelian Y (ZMod n)).map
          (inverseImageEtaleModuleConstantSheafIso.{u, 0} (ZMod n)
            (ModuleCat.of (ZMod n) (ULift.{u + 1} (ZMod n))) φ).hom ≫
          (Stacks.Kummer.etaleModuleConstantUnderlyingIso g hζ hn).hom ≫
          Stacks.Kummer.rootsOfUnityι.{u, 0} Y n) =
      (etaleModuleUnderlyingAbelian Y (ZMod n)).map
          (constantSelfMapTwist.{u, 0} (ZMod n)
            (ModuleCat.of (ZMod n) (ULift.{u + 1} (ZMod n))) φ) ≫
        etaleModuleUnderlyingAbelianDirectImageHom (ZMod n) φ ΛY ≫
        (etaleAbelianDirectImage.{u, 0} φ).map
          ((Stacks.Kummer.etaleModuleConstantUnderlyingIso g hζ hn).hom ≫
            Stacks.Kummer.rootsOfUnityι.{u, 0} Y n) := by
    have h1 := etaleModuleUnderlyingAbelianInverseImageIso_unit' (ZMod n) φ ΛY
    have h2 : (etaleModuleUnderlyingAbelian Y (ZMod n)).map
        (constantSelfMapTwist.{u, 0} (ZMod n)
          (ModuleCat.of (ZMod n) (ULift.{u + 1} (ZMod n))) φ) =
        (etaleModuleUnderlyingAbelian Y (ZMod n)).map
          ((etaleModuleInverseImageAdj.{u, 0} (ZMod n) φ).unit.app ΛY) ≫
        (etaleModuleUnderlyingAbelian Y (ZMod n)).map
          ((etaleModuleDirectImage.{u, 0} (ZMod n) φ).map
            (inverseImageEtaleModuleConstantSheafIso.{u, 0} (ZMod n)
              (ModuleCat.of (ZMod n) (ULift.{u + 1} (ZMod n))) φ).hom) := by
      rw [constantSelfMapTwist, Adjunction.homEquiv_unit, Functor.map_comp]
      rfl
    rw [Adjunction.homEquiv_unit, h2, h1]
    simp only [Functor.map_comp]
    rfl
  rw [hL]
  -- both sides are maps out of `U ℤ/n_Y`; precompose with the epimorphism `ℤ_Y ⟶ U ℤ/n_Y`
  have hT := isTerminalEtaleMkId Y
  have hT' : IsTerminal ((smallEtaleBaseChange φ).obj (Scheme.Etale.mk (𝟙 Y))) :=
    hT.isTerminalObj (smallEtaleBaseChange φ)
  have : (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).IsLeftAdjoint :=
    (constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u + 1} hT).isLeftAdjoint
  have : Epi (uliftIntToULiftHom (ZMod n)) := by
    rw [AddCommGrpCat.epi_iff_surjective]
    rintro ⟨m⟩
    obtain ⟨z, rfl⟩ := ZMod.intCast_surjective m
    exact ⟨ULift.up z, by
      change ULift.up ((z : ℤ) • (1 : ZMod n)) = _
      simp⟩
  have : Epi (etaleModuleUnderlyingAbelianConstantMap (ZMod n) Y) := by
    unfold etaleModuleUnderlyingAbelianConstantMap
    infer_instance
  rw [← cancel_epi (etaleModuleUnderlyingAbelianConstantMap (ZMod n) Y)]
  apply ((etaleAbelianConstantAdj Y hT).homEquiv _ _).injective
  -- the left side, read on the final object: `ζ` on the base change of the final object
  have h1 := etaleModuleUnderlyingAbelianConstantMap_comp_map (ZMod n) Y hT' (𝟙 ΛY)
  rw [CategoryTheory.Functor.map_id, Category.comp_id] at h1
  have hL' : (etaleAbelianConstantAdj Y hT).homEquiv _ _
      (etaleModuleUnderlyingAbelianConstantMap (ZMod n) Y ≫
        ((etaleModuleUnderlyingAbelian Y (ZMod n)).map
          (constantSelfMapTwist.{u, 0} (ZMod n)
            (ModuleCat.of (ZMod n) (ULift.{u + 1} (ZMod n))) φ) ≫
        etaleModuleUnderlyingAbelianDirectImageHom (ZMod n) φ ΛY ≫
        (etaleAbelianDirectImage.{u, 0} φ).map
          ((Stacks.Kummer.etaleModuleConstantUnderlyingIso g hζ hn).hom ≫
            Stacks.Kummer.rootsOfUnityι.{u, 0} Y n))) =
      uliftIntToULiftHom (ZMod n) ≫
        (Stacks.Kummer.rootPresheafHom g hζ hn).app
          (op ((smallEtaleBaseChange φ).obj (Scheme.Etale.mk (𝟙 Y)))) := by
    have hcs : (etaleModuleConstantAdj (ZMod n) Y hT).homEquiv _ _
        (constantSelfMapTwist.{u, 0} (ZMod n)
          (ModuleCat.of (ZMod n) (ULift.{u + 1} (ZMod n))) φ) =
        constantSheafSection (ZMod n) (ModuleCat.of (ZMod n) (ULift.{u + 1} (ZMod n)))
          ((smallEtaleBaseChange φ).obj (Scheme.Etale.mk (𝟙 Y))) := by
      rw [Stacks.ConstantSheaf.constantSheafAdj_homEquiv_apply]
      exact constantSheafSection_comp_constantSelfMapTwist (ZMod n) _ φ
    have h1' : (etaleAbelianConstantAdj Y hT').homEquiv _ _
        (etaleModuleUnderlyingAbelianConstantMap (ZMod n) Y) =
        uliftIntToULiftHom (ZMod n) ≫
          (forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1}).map
            (constantSheafSection (ZMod n) (ModuleCat.of (ZMod n) (ULift.{u + 1} (ZMod n)))
              ((smallEtaleBaseChange φ).obj (Scheme.Etale.mk (𝟙 Y)))) := by
      rw [h1, Equiv.apply_symm_apply, Stacks.ConstantSheaf.constantSheafAdj_homEquiv_apply]
      rfl
    refine Eq.trans ?_ (homEquiv_constantMap_comp_constantUnderlyingIso g hζ hn hT')
    rw [← Category.assoc, Adjunction.homEquiv_naturality_right,
      etaleModuleUnderlyingAbelianConstantMap_comp_map (ZMod n) Y hT, Equiv.apply_symm_apply, hcs,
      Adjunction.homEquiv_naturality_right, h1']
    rfl
  -- the right side, read on the final object: `ζ` pulled back along the projection
  have hR : (etaleAbelianConstantAdj Y hT).homEquiv _ _
      (etaleModuleUnderlyingAbelianConstantMap (ZMod n) Y ≫
        ((Stacks.Kummer.etaleModuleConstantUnderlyingIso g hζ hn).hom ≫
          Stacks.Kummer.rootsOfUnityι.{u, 0} Y n) ≫ multiplicativeDirectImageComparison.{u, 0} φ) =
      uliftIntToULiftHom (ZMod n) ≫
        (Stacks.Kummer.rootPresheafHom g hζ hn).app (op (Scheme.Etale.mk (𝟙 Y))) ≫
        (multiplicativeDirectImageComparison.{u, 0} φ).hom.app (op (Scheme.Etale.mk (𝟙 Y))) := by
    have h3 := homEquiv_constantMap_comp_constantUnderlyingIso g hζ hn hT
    rw [← Category.assoc, Adjunction.homEquiv_naturality_right, h3, Category.assoc]
    rfl
  rw [hL', hR]
  congr 1
  ext ⟨m⟩
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective m
  change Stacks.Kummer.rootHom g hζ hn _ (z : ZMod n) =
    (multiplicativeDirectImageComparison.{u, 0} φ).hom.app (op (Scheme.Etale.mk (𝟙 Y)))
      (Stacks.Kummer.rootHom g hζ hn _ (z : ZMod n))
  rw [Stacks.Kummer.rootHom_intCast, Stacks.Kummer.rootHom_intCast, map_zsmul,
    multiplicativeDirectImageComparison_app_ofUnit, map_rootOn_pullbackFst g hζ hn φ w]
  rfl

end RootsOfUnity

section Cohomology

attribute [local instance] Sheaf.monoidalCategory etaleModuleInverseImageSheafPullbackMonoidal
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits

variable {k : Type u} [Field k] {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k)) (φ : Y ⟶ Y)
  (w : φ ≫ g = g) {n : ℕ} {ζ : k} (hζ : IsPrimitiveRoot ζ n) (hn : n ≠ 0)
  [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- The identification `U(g^{-1} ℤ/n) ≅ U ℤ/n_Y ≅ μ_n` of abelian sheaves on `Y`. -/
def inverseImageConstantUnderlyingRootsOfUnityIso :
    (etaleModuleUnderlyingAbelian Y (ZMod n)).obj ((etaleModuleInverseImage.{u, 0} (ZMod n) g).obj
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod n)
          (Spec (.of k)).smallEtaleTopology)) ≅
      Stacks.Kummer.rootsOfUnitySheaf.{u, 0} Y n :=
  (etaleModuleUnderlyingAbelian Y (ZMod n)).mapIso
      (inverseImageEtaleModuleConstantSheafIso.{u, 0} (ZMod n)
        (ModuleCat.of (ZMod n) (ULift.{u + 1} (ZMod n))) g) ≪≫
    Stacks.Kummer.etaleModuleConstantUnderlyingIso g hζ hn

/-- **`Hⁱ(RΓ(Y, ℤ/n)) ≃+ Hⁱ(Y, μ_n)`**, for `Y` over a field `k` with a primitive `n`-th root of
unity `ζ`: the cohomology of `RΓ(Spec k, Rg_*(g^{-1} ℤ/n))` is `Ext^i(ℤ/n_Y, g^{-1} ℤ/n)`, which
is `Hⁱ(Y, U g^{-1} ℤ/n)`, and `U g^{-1} ℤ/n ≅ μ_n` through `m ↦ ζ^m`. -/
def selfMapCohomologyRootsOfUnityAddEquiv (i : ℕ) :
    (forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1}).obj
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} (ZMod n)) i).obj
          (selfMapCohomology.{u, 0} (ZMod n) g ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
            (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod n)
              (Spec (.of k)).smallEtaleTopology)))) ≃+
      Sheaf.H.{u + 1} (Stacks.Kummer.rootsOfUnitySheaf.{u, 0} Y n) i :=
  (selfMapCohomologySingleIsoExt (ZMod n) g _ i).addCommGroupIsoToAddEquiv.trans
    ((extForgetSheafHAddEquiv (ZMod n) Y _ i).trans
      (SmallEtale.extPostcompIsoAddEquiv (inverseImageConstantUnderlyingRootsOfUnityIso g hζ hn) i))

/-- `selfMapCohomologyRootsOfUnityAddEquiv` sends a class `x` to the image of `x` in
`Ext^i(ℤ/n_Y, U g^{-1} ℤ/n)` composed with the isomorphism `U g^{-1} ℤ/n ≅ μ_n`. -/
theorem selfMapCohomologyRootsOfUnityAddEquiv_apply (i : ℕ)
    (x : (forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1}).obj
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} (ZMod n)) i).obj
          (selfMapCohomology.{u, 0} (ZMod n) g ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
            (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod n)
              (Spec (.of k)).smallEtaleTopology))))) :
    selfMapCohomologyRootsOfUnityAddEquiv g hζ hn i x =
      (extForgetSheafH (ZMod n) Y _ i
          ((selfMapCohomologySingleIsoExt (ZMod n) g _ i).hom.hom x)).comp
        (Ext.mk₀ (inverseImageConstantUnderlyingRootsOfUnityIso g hζ hn).hom) (add_zero i) :=
  rfl

variable [(Y.smallEtaleTopology.W (A := ModuleCat.{u + 1} (ZMod n))).IsMonoidal]
  [PreservesFiniteColimits (etaleModuleDirectImage.{u, 0} (ZMod n) φ)]

omit [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [(Y.smallEtaleTopology.W (A := ModuleCat.{u + 1} (ZMod n))).IsMonoidal]
  [PreservesFiniteColimits (etaleModuleDirectImage.{u, 0} (ZMod n) φ)] in
/-- The sheaf-level identity behind
`Stacks.EtaleCohomology.selfMapCohomologyRootsOfUnityAddEquiv_selfMapCohomologyEndo`: the map
`φ^{-1} U g^{-1} ℤ/n ⟶ U g^{-1} ℤ/n` of the self-map twist is, under `U g^{-1} ℤ/n ≅ μ_n`, the
comparison `φ^{-1} μ_n ⟶ μ_n`. -/
theorem selfMapTwist_underlying_comp_rootsOfUnityIso :
    ((etaleModuleUnderlyingAbelianInverseImageIso (ZMod n) φ).hom.app _ ≫
        (etaleModuleUnderlyingAbelian Y (ZMod n)).map
          ((etaleModuleInverseImage.{u, 0} (ZMod n) φ).map ((selfMapTwist.{u, 0} (ZMod n) g φ w).app
            (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod n)
              (Spec (.of k)).smallEtaleTopology)) ≫
            (etaleModuleInverseImageAdj.{u, 0} (ZMod n) φ).counit.app _)) ≫
      (inverseImageConstantUnderlyingRootsOfUnityIso g hζ hn).hom =
    (etaleAbelianInverseImage.{u, 0} φ).map
        (inverseImageConstantUnderlyingRootsOfUnityIso g hζ hn).hom ≫
      Stacks.Kummer.rootsOfUnityInverseImageComparison.{u, 0} φ n := by
  have hmod := map_selfMapTwist_constant_comp_counit (ZMod n) g φ w
    (ModuleCat.of (ZMod n) (ULift.{u + 1} (ZMod n)))
  have hmod' : (etaleModuleInverseImage.{u, 0} (ZMod n) φ).map
        ((selfMapTwist.{u, 0} (ZMod n) g φ w).app
          (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod n)
            (Spec (.of k)).smallEtaleTopology)) ≫
      (etaleModuleInverseImageAdj.{u, 0} (ZMod n) φ).counit.app _ ≫
      (inverseImageEtaleModuleConstantSheafIso.{u, 0} (ZMod n)
        (ModuleCat.of (ZMod n) (ULift.{u + 1} (ZMod n))) g).hom =
      (etaleModuleInverseImage.{u, 0} (ZMod n) φ).map
        (inverseImageEtaleModuleConstantSheafIso.{u, 0} (ZMod n)
          (ModuleCat.of (ZMod n) (ULift.{u + 1} (ZMod n))) g).hom ≫
      (inverseImageEtaleModuleConstantSheafIso.{u, 0} (ZMod n)
        (ModuleCat.of (ZMod n) (ULift.{u + 1} (ZMod n))) φ).hom := by
    rw [← hmod, ← Functor.map_comp_assoc, Iso.hom_inv_id_assoc]
  have hnat := (etaleModuleUnderlyingAbelianInverseImageIso (ZMod n) φ).hom.naturality
    (inverseImageEtaleModuleConstantSheafIso.{u, 0} (ZMod n)
      (ModuleCat.of (ZMod n) (ULift.{u + 1} (ZMod n))) g).hom
  simp only [Functor.comp_map] at hnat
  simp only [inverseImageConstantUnderlyingRootsOfUnityIso, Iso.trans_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc, hmod',
    Functor.map_comp, Category.assoc, ← reassoc_of% hnat,
    underlyingInverseImageConstant_comp_rootsOfUnity g hζ hn φ w]

/-- **`φ^*` on `Hⁱ(Y, ℤ/n)` is pullback on `Hⁱ(Y, μ_n)`.** For an endomorphism `φ` of a scheme `Y`
over a field `k` containing a primitive `n`-th root of unity `ζ`, the pullback action
`φ^* = Stacks.EtaleCohomology.selfMapCohomologyEndo` on the cohomology of
`RΓ(Y, ℤ/n) = RΓ(Spec k, Rg_*(g^{-1} ℤ/n))` is, under
`Stacks.EtaleCohomology.selfMapCohomologyRootsOfUnityAddEquiv`, the pullback
`Stacks.EtaleCohomology.rootsOfUnityPullbackMap φ n i` on `Hⁱ(Y, μ_n)`: restriction along `φ`
followed by the comparison `φ^{-1} μ_n ⟶ μ_n`. -/
theorem selfMapCohomologyRootsOfUnityAddEquiv_selfMapCohomologyEndo (i : ℕ)
    (x : (forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1}).obj
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} (ZMod n)) i).obj
          (selfMapCohomology.{u, 0} (ZMod n) g ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
            (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod n)
              (Spec (.of k)).smallEtaleTopology))))) :
    selfMapCohomologyRootsOfUnityAddEquiv g hζ hn i
        (((forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1}).map
          ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} (ZMod n)) i).map
            (selfMapCohomologyEndo.{u, 0} (ZMod n) g φ w
              ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
                (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod n)
                  (Spec (.of k)).smallEtaleTopology))))).hom x) =
      rootsOfUnityPullbackMap.{u, 0, u + 1} φ n i
        (selfMapCohomologyRootsOfUnityAddEquiv g hζ hn i x) := by
  obtain ⟨b, rfl⟩ : ∃ b, x = ((selfMapCohomologySingleIsoExt (ZMod n) g _ i).inv).hom b :=
    ⟨((selfMapCohomologySingleIsoExt (ZMod n) g _ i).hom).hom x, by
      rw [← AddCommGrpCat.comp_apply, Iso.hom_inv_id, AddCommGrpCat.id_apply]⟩
  rw [selfMapCohomologyRootsOfUnityAddEquiv_apply, selfMapCohomologyRootsOfUnityAddEquiv_apply]
  have hb : ((selfMapCohomologySingleIsoExt (ZMod n) g _ i).hom).hom
      (((selfMapCohomologySingleIsoExt (ZMod n) g _ i).inv).hom b) = b := by
    rw [← AddCommGrpCat.comp_apply, Iso.inv_hom_id, AddCommGrpCat.id_apply]
  rw [extForgetSheafH_selfMapCohomologyEndo (ZMod n) g φ w _ i b, hb]
  generalize extForgetSheafH (ZMod n) Y _ i b = y
  rw [rootsOfUnityPullbackMap_apply, Sheaf.H.map_apply,
    etaleCohomologyRestrictionMap_apply, etaleCohomologyRestrictionMap_apply,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]
  rw [selfMapTwist_underlying_comp_rootsOfUnityIso g φ w hζ hn]

end Cohomology

end Stacks.EtaleCohomology

end
