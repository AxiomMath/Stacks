module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.ClassMapStalkConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.KummerDivisorSectionGeneratorStalks
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.KummerClassMapLevel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.RelativeCurvePurityLAdic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.RootsOfUnityModuleLocallyConstant
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stalkwise purity of the class map of an étale divisor of a smooth relative curve

Let `W` be smooth over a field `k`, `g : U ⟶ W` smooth of relative dimension one, `i : Z ⟶ U` a
closed immersion with `Z ⟶ W` étale, `j : U₀ ⟶ U` the open complement, `N` invertible in `k` and
`H` a locally constant sheaf of finite type of `ℤ/N`-modules on `U_étale`. The purity map
`𝓗om(μ_N, H) ⟶ R¹ j_*(j⁻¹ H)`, `α ↦ α_* s` (`Stacks.EtaleCohomology.Purity.kummerClassMapAb`),
is invertible on the stalks at the geometric points over `Z`
(`Stacks.EtaleCohomology.Purity.purityClassMapStalkIsoInput`), the stalkwise form of relative
cohomological purity ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main results

* `Stacks.EtaleCohomology.Purity.isIso_stalk_higherDirectImageClassMap_of_generator`: the class
  map is invertible on the stalk at a geometric point for locally constant coefficients of finite
  type once the images of the class generate the stalks freely at every level `n ∣ N`.
* `Stacks.EtaleCohomology.Purity.bijective_nsmul_germ_powClass`: the image of the fundamental
  class at level `n ∣ N` generates the stalks of `R¹ j_*(j⁻¹ μ_n)` over `Z` freely over `ℤ/n`.
* `Stacks.EtaleCohomology.Purity.purityClassMapStalkIsoInput`: stalkwise purity of the class map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
  GrothendieckTopology

universe u

namespace Stacks.EtaleCohomology.Purity

open Stacks.Kummer

-- `AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives` has a free universe; with it in scope
-- the instance problems `EnoughInjectives (EtaleModules Λ X)` get stuck on a universe constraint.
attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

attribute [local instance] AlgebraicGeometry.preservesFilteredColimitsOfSize_forget_addCommGrpCat

section Neighbourhoods

variable {U : Scheme.{u}} (N : ℕ) [NeZero N]

/-- A geometric point of `U_étale` has a point in the fibre over the terminal object. -/
private theorem nonempty_fiber_opensToEtale_top (Φ : Point.{u} U.smallEtaleTopology) :
    Nonempty (Φ.fiber.obj ((opensToEtale U).obj ⊤)) :=
  ⟨(Φ.uniqueFiberObj _ (isTerminal_opensToEtale_top U)).default⟩

/-- **Every point of `U_étale` lies over the neighbourhood `U ⊗_k k(ζ_N)`**, which carries a
primitive `N`-th root of unity. -/
theorem nonempty_fiber_cyclotomicBaseChange {k : Type u} [Field k] (f : U ⟶ Spec (.of k))
    [NeZero (N : k)] (Φ : Point.{u} U.smallEtaleTopology) :
    Nonempty (Φ.fiber.obj (cyclotomicBaseChange f N ((opensToEtale U).obj ⊤))) := by
  obtain ⟨t0⟩ := nonempty_fiber_opensToEtale_top Φ
  have hR : Sieve.ofArrows (fun _ : Unit => cyclotomicBaseChange f N ((opensToEtale U).obj ⊤))
      (fun _ => cyclotomicBaseChangeπ f N ((opensToEtale U).obj ⊤)) ∈
        U.smallEtaleTopology ((opensToEtale U).obj ⊤) := by
    rw [ofArrows_mem_smallEtaleTopology_iff]
    exact Set.eq_univ_of_forall fun p => Set.mem_iUnion.2 ⟨(), by
      rw [range_cyclotomicBaseChangeπ]; trivial⟩
  obtain ⟨Y, a, ⟨Z', b, _, ⟨_⟩, -⟩, y, -⟩ := Φ.jointly_surjective _ hR t0
  exact ⟨Φ.fiber.map b y⟩

/-- **A locally constant sheaf of finite type of `ℤ/N`-modules is constant with finite value near
every point of `U_étale`.** -/
theorem exists_fiber_sliceIso_constantSheaf (Φ : Point.{u} U.smallEtaleTopology)
    (H : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ZMod N)))
    (hH : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod N) U.smallEtaleTopology H) :
    ∃ (V₁ : U.Etale) (_ : Φ.fiber.obj V₁) (M : ModuleCat.{u + 1} (ZMod N)) (_ : Finite M),
      Nonempty ((U.smallEtaleTopology.overPullback (ModuleCat.{u + 1} (ZMod N)) V₁).obj H ≅
        (U.smallEtaleTopology.overPullback (ModuleCat.{u + 1} (ZMod N)) V₁).obj
          ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ZMod N))).obj M)) := by
  obtain ⟨t0⟩ := nonempty_fiber_opensToEtale_top Φ
  obtain ⟨I, V, f, hcov, hloc⟩ := hH ((opensToEtale U).obj ⊤)
  obtain ⟨Y, a, ⟨Z', b, _, ⟨i⟩, -⟩, y, -⟩ := Φ.jointly_surjective _ hcov t0
  obtain ⟨E, hE, ⟨e⟩⟩ := hloc i
  rw [ModuleCat.isFG_iff] at hE
  have : Finite E := Module.finite_of_finite (ZMod N)
  exact ⟨V i, Φ.fiber.map b y, E, inferInstance, ⟨e.symm ≪≫
    (Stacks.ConstantSheaf.overPullbackConstantSheafIso U.smallEtaleTopology
      (ModuleCat.{u + 1} (ZMod N)) (V i)).app E⟩⟩

end Neighbourhoods

section Generic

variable {X U : Scheme.{u}} (g : X ⟶ U) (q : ℕ) (N : ℕ) [NeZero N]
  (s : ToType ((((smallEtalePushforwardAb g).rightDerived q).obj
    ((smallEtalePullbackAb g).obj (smallEtaleModuleSheafForgetAb (ZMod N)
      (rootsOfUnityModule.{u, 0} U N)))).obj.obj (op ((opensToEtale U).obj ⊤))))

/-- **The class map is invertible on the stalk at a geometric point for locally constant
coefficients of finite type**, as soon as for every `n ∣ N` the image of the class in
`R^q g_*(g⁻¹ μ_n)` generates the stalk freely over `ℤ/n`. -/
theorem isIso_stalk_higherDirectImageClassMap_of_generator {k : Type u} [Field k]
    (f : U ⟶ Spec (.of k)) [NeZero (N : k)] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ U)
    (hgen : ∀ (ℓ n : ℕ) (hn : ℓ * n = N) [NeZero n]
      (y : (Scheme.pointSmallEtale x).fiber.obj ((opensToEtale U).obj ⊤)),
      Function.Bijective (fun a : ZMod n => a.val • (Scheme.pointSmallEtale x).toPresheafFiber
        ((opensToEtale U).obj ⊤) y (((smallEtalePushforwardAb g).rightDerived q).obj
          ((smallEtalePullbackAb g).obj (smallEtaleModuleSheafForgetAb (ZMod N)
            (restrictRootsOfUnityModule U N ℓ n hn)))).obj (powClass g q N s ℓ n hn)))
    (H : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ZMod N)))
    (hH : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod N) U.smallEtaleTopology H) :
    IsIso ((smallEtaleStalkAb x).map (classMap g q N s H)) := by
  obtain ⟨v⟩ := nonempty_fiber_cyclotomicBaseChange N f (Scheme.pointSmallEtale x)
  obtain ⟨V₁, v₁, M, _, ⟨ρ⟩⟩ :=
    exists_fiber_sliceIso_constantSheaf N (Scheme.pointSmallEtale x) H hH
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective ((Scheme.pointSmallEtale x).presheafFiber.map (classMap g q N s H).hom)
  rw [bijective_presheafFiber_map_classMap_iff g q N s (Scheme.pointSmallEtale x) v
      (cyclotomicBaseChangeStructMap f N _) (IsCyclotomicExtension.zeta_spec N k _) H,
    bijective_classMapGermMap_iff_of_slice_iso g q N s (Scheme.pointSmallEtale x) v
      (cyclotomicBaseChangeStructMap f N _) (IsCyclotomicExtension.zeta_spec N k _) v₁ ρ]
  exact bijective_classMapGermMap_constantSheaf g q N s x v (cyclotomicBaseChangeStructMap f N _)
    (IsCyclotomicExtension.zeta_spec N k _) hgen M

end Generic

section Kummer

variable (k : Type u) [Field k] (N : ℕ) [NeZero N] (hN : IsUnit (N : k)) {U W Z U₀ : Scheme.{u}}
  (pW : W ⟶ Spec (.of k)) [Smooth pW] (g : U ⟶ W) [SmoothOfRelativeDimension 1 g]
  (i : Z ⟶ U) [IsClosedImmersion i] [Etale (i ≫ g)] (j : U₀ ⟶ U) [IsOpenImmersion j]
  (hj : Set.range j.base = (Set.range i.base)ᶜ)
  [HasDerivedCategory.{u + 2} (Sheaf (smallEtaleTopology U₀) Ab.{u + 1})]
  [HasDerivedCategory.{u + 2} (Sheaf (smallEtaleTopology U) Ab.{u + 1})]
  (hN₀ : IsUnit ((N : ℕ) : Γ(U₀, ⊤))) (hNU : IsUnit ((N : ℕ) : Γ(U, ⊤)))
  (hcov : ∀ x : U, ∃ (V : U.Opens) (t : Γ(U, V)), x ∈ V ∧ IsLocalEquation i V t)

include hN pW g in
/-- **The image of the fundamental class at level `n ∣ N` generates the stalks of
`R¹ j_*(j⁻¹ μ_n)` over `Z` freely over `ℤ/n`**. -/
theorem bijective_nsmul_germ_powClass {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ U) (hx : Set.range x.base ⊆ Set.range i.base) (ℓ n : ℕ) (hn : ℓ * n = N)
    [NeZero n] (y : (Scheme.pointSmallEtale x).fiber.obj ((opensToEtale U).obj ⊤)) :
    Function.Bijective (fun a : ZMod n => a.val • (Scheme.pointSmallEtale x).toPresheafFiber
      ((opensToEtale U).obj ⊤) y (((smallEtalePushforwardAb j).rightDerived 1).obj
        ((smallEtalePullbackAb j).obj (smallEtaleModuleSheafForgetAb (ZMod N)
          (restrictRootsOfUnityModule U N ℓ n hn)))).obj
        (powClass j 1 N (kummerDivisorPullbackSection j N hN₀ hNU i hj.subset hcov) ℓ n hn)) := by
  have hnN : (n : ℕ) ∣ N := ⟨ℓ, by rw [← hn, mul_comm]⟩
  have hnk : IsUnit (n : k) := isUnit_of_dvd_unit (Nat.cast_dvd_cast hnN) hN
  have hn₀ : IsUnit ((n : ℕ) : Γ(U₀, ⊤)) := isUnit_of_dvd_unit (Nat.cast_dvd_cast hnN) hN₀
  have hnU : IsUnit ((n : ℕ) : Γ(U, ⊤)) := isUnit_of_dvd_unit (Nat.cast_dvd_cast hnN) hNU
  have hσ : IsIsoStalksOver (Set.range i.base) _ :=
    isIsoStalksOver_torsionSectionSheafHom_kummerDivisorSection k n hnk pW g i j hj hn₀ hnU hcov
  have hb := (isIso_stalk_torsionSectionSheafHom_iff x _ _ y).1 (hσ x hx)
  have hpow : powClass j 1 N (kummerDivisorPullbackSection j N hN₀ hNU i hj.subset hcov) ℓ n hn =
      kummerDivisorPullbackSection j n hn₀ hnU i hj.subset hcov :=
    map_kummerDivisorPullbackSection j ℓ n N hn hn₀ hnU hN₀ hNU i hj.subset hcov
  rw [hpow]
  have hfun : (fun a : ZMod n => a.val • (Scheme.pointSmallEtale x).toPresheafFiber
      ((opensToEtale U).obj ⊤) y (((smallEtalePushforwardAb j).rightDerived 1).obj
        ((smallEtalePullbackAb j).obj (smallEtaleModuleSheafForgetAb (ZMod N)
          (restrictRootsOfUnityModule U N ℓ n hn)))).obj
        (kummerDivisorPullbackSection j n hn₀ hnU i hj.subset hcov)) =
      (Scheme.pointSmallEtale x).presheafFiber.map
          (((smallEtalePushforwardAb j).rightDerived 1).map
            (pullbackRootsOfUnityIso j n hnU).inv).hom ∘
        (fun a : ZMod n => a.val • (Scheme.pointSmallEtale x).toPresheafFiber
          ((opensToEtale U).obj ⊤) y (kummerTarget j n).obj
          (kummerDivisorSection j (NeZero.ne n) hn₀ hnU i hj.subset hcov)) := by
    funext a
    rw [Function.comp_apply, map_nsmul, Point.toPresheafFiber_naturality_apply]
    rfl
  rw [hfun]
  exact (ConcreteCategory.bijective_of_isIso ((smallEtaleStalkAb x).map
    (((smallEtalePushforwardAb j).rightDerived 1).map
      (pullbackRootsOfUnityIso j n hnU).inv))).comp hb

end Kummer

/-- **Stalkwise purity of the class map** (Stacks, Tag 03VH): for `g : U ⟶ W` smooth of relative
dimension one over `W` smooth over a field `k`, a closed immersion `i : Z ⟶ U` with `Z ⟶ W`
étale, `j : U₀ ⟶ U` the open complement, `N` invertible in `k` and `H` a locally constant sheaf of
finite type of `ℤ/N`-modules on `U`, the purity map `𝓗om(μ_N, H) ⟶ R¹ j_*(j⁻¹ H)`,
`α ↦ α_* s`, is invertible on the stalks at the geometric points over `Z`. -/
@[sga "4 XVI 3.6" "Abelian case", sga "4 XVI 3.7" "special case"]
theorem purityClassMapStalkIsoInput : PurityClassMapStalkIsoInput.{u} := by
  intro k _ N _ hN U W Z U₀ pW _ g _ i _ _ j _ hj _ _ hN₀ hNU hcov H hH Ω _ _ x hx
  have : NeZero (N : k) := ⟨hN.ne_zero⟩
  exact isIso_stalk_higherDirectImageClassMap_of_generator j 1 N
    (kummerDivisorPullbackSection j N hN₀ hNU i hj.subset hcov) (g ≫ pW) x
    (fun ℓ n hn _ y => bijective_nsmul_germ_powClass k N hN pW g i j hj hN₀ hNU hcov x hx ℓ n hn y)
    H hH

end Stacks.EtaleCohomology.Purity

end
