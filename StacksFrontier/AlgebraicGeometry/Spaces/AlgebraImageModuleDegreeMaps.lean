module

public import StacksFrontier.AlgebraicGeometry.Spaces.ReesModuleOnBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardGlobalSmul
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerSmulFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedInjective

/-!
# The degree maps into the direct image of the image module

Let `f : X ⟶ h_T`, `φ : R ⟶ R'` a map of finitely generated `A`-algebras, `π : X_R ⟶ X` and
`ψ : X_{R'} ⟶ X_R` the induced morphisms, `N₀` a quasi-coherent submodule of an `𝒪_X`-module,
`K = ψ^*π^*N₀` and `G` the image of the unit `u : π^*N₀ ⟶ ψ_*K`
(`AlgebraicGeometry.Space.algebraImageModule`).  On `X` put `V = π_*ψ_*K`, with the unit
`N₀ ⟶ V` and the action `ρ(c) = π_*ψ_*(c ·)` of global functions `c` of `X_{R'}`.

Given global functions `aᵢ` of `X` generating a sheaf of ideals `I` on affine charts, a global
function `t` of `X_{R'}` and global functions `sᵢ` of `X_R` with `ψ♯ sᵢ = aᵢ t`, the map
`IᵐN₀ ⟶ N₀ ⟶ V` followed by `ρ(tᵐ)` factors through `π_*G ⊆ V` for every `m`.

## Main definitions

* `AlgebraicGeometry.Space.algebraImageTotalUnit`: `N₀ ⟶ π_*ψ_*K`.
* `AlgebraicGeometry.Space.algebraImageScalarEnd`: `ρ(c)`.

## Main results

* `AlgebraicGeometry.Space.exists_algebraImageDegreeMap`: the factorization `IᵐN₀ ⟶ π_*G`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.SiteModules (globalSmul)



universe u

namespace AlgebraicGeometry.Space


variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace T)
  (R : Type u) [CommRing R] [Algebra Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R]
  [Algebra.FiniteType Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R]
  (R' : Type u) [CommRing R'] [Algebra Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R']
  [Algebra.FiniteType Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R']
  (φ : R →ₐ[Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)] R')

/-- `K = ψ^*π^*F` on `X_{R'}`. -/
abbrev algebraImageTarget (F : Modules.{u, u} B S hS X.1 X.2) :
    Modules.{u, u} B S hS (algebraBaseChange B S hS T f R').1 (algebraBaseChange B S hS T f R').2 :=
  (modulePullback B S hS (algebraBaseChangeMap B S hS T f R R' φ)).obj
    ((modulePullback B S hS (algebraBaseChangeProjection B S hS T f R)).obj F)

/-- `V = π_*ψ_*ψ^*π^*F` on `X`. -/
abbrev algebraImageTotal (F : Modules.{u, u} B S hS X.1 X.2) : Modules.{u, u} B S hS X.1 X.2 :=
  (modulePushforward B S hS (algebraBaseChangeProjection B S hS T f R)).obj
    ((modulePushforward B S hS (algebraBaseChangeMap B S hS T f R R' φ)).obj
      (algebraImageTarget B S hS T f R R' φ F))

/-- **The unit `F ⟶ π_*ψ_*ψ^*π^*F`**: the unit of `π^* ⊣ π_*` followed by `π_*` of the unit of
`ψ^* ⊣ ψ_*`. -/
def algebraImageTotalUnit (F : Modules.{u, u} B S hS X.1 X.2) :
    F ⟶ algebraImageTotal B S hS T f R R' φ F :=
  (modulePullbackAdjunction B S hS (algebraBaseChangeProjection B S hS T f R)).unit.app F ≫
    (modulePushforward B S hS (algebraBaseChangeProjection B S hS T f R)).map
      (algebraImageUnit B S hS T f R R' φ F)

/-- **The action `ρ(c) = π_*ψ_*(c ·)` of a global function `c` of `X_{R'}` on `π_*ψ_*K`.** -/
def algebraImageScalarEnd (F : Modules.{u, u} B S hS X.1 X.2)
    (c : RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS
      (algebraBaseChange B S hS T f R').1 (algebraBaseChange B S hS T f R').2).O).obj) :
    algebraImageTotal B S hS T f R R' φ F ⟶ algebraImageTotal B S hS T f R R' φ F :=
  (modulePushforward B S hS (algebraBaseChangeProjection B S hS T f R)).map
    ((modulePushforward B S hS (algebraBaseChangeMap B S hS T f R R' φ)).map
      (globalSmul _ c (algebraImageTarget B S hS T f R R' φ F)))

/-- `ρ(1)` is the identity. -/
theorem algebraImageScalarEnd_one (F : Modules.{u, u} B S hS X.1 X.2) :
    algebraImageScalarEnd B S hS T f R R' φ F 1 = 𝟙 _ := by
  rw [algebraImageScalarEnd, Stacks.Cohomology.SiteModules.globalSmul_one,
    CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]

/-- `ρ(c d) = ρ(c) ≫ ρ(d)`. -/
theorem algebraImageScalarEnd_mul (F : Modules.{u, u} B S hS X.1 X.2)
    (c d : RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS
      (algebraBaseChange B S hS T f R').1 (algebraBaseChange B S hS T f R').2).O).obj) :
    algebraImageScalarEnd B S hS T f R R' φ F (c * d) =
      algebraImageScalarEnd B S hS T f R R' φ F c ≫
        algebraImageScalarEnd B S hS T f R R' φ F d := by
  rw [algebraImageScalarEnd, algebraImageScalarEnd, algebraImageScalarEnd,
    Stacks.Cohomology.SiteModules.globalSmul_mul, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp]

/-- `ρ(c + d) = ρ(c) + ρ(d)`. -/
theorem algebraImageScalarEnd_add (F : Modules.{u, u} B S hS X.1 X.2)
    (c d : RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS
      (algebraBaseChange B S hS T f R').1 (algebraBaseChange B S hS T f R').2).O).obj) :
    algebraImageScalarEnd B S hS T f R R' φ F (c + d) =
      algebraImageScalarEnd B S hS T f R R' φ F c +
        algebraImageScalarEnd B S hS T f R R' φ F d := by
  rw [algebraImageScalarEnd, algebraImageScalarEnd, algebraImageScalarEnd,
    Stacks.Cohomology.SiteModules.globalSmul_add, CategoryTheory.Functor.map_add,
    CategoryTheory.Functor.map_add]

/-- `ρ(ψ♯ c)` is the direct image along `π` of multiplication by `c` on `ψ_*K`. -/
theorem algebraImageScalarEnd_globalSectionsRingHomSite (F : Modules.{u, u} B S hS X.1 X.2)
    (c : RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS
      (algebraBaseChange B S hS T f R).1 (algebraBaseChange B S hS T f R).2).O).obj) :
    algebraImageScalarEnd B S hS T f R R' φ F
        (globalSectionsRingHomSite B S hS (algebraBaseChangeMap B S hS T f R R' φ) c) =
      (modulePushforward B S hS (algebraBaseChangeProjection B S hS T f R)).map
        (globalSmul _ c ((modulePushforward B S hS (algebraBaseChangeMap B S hS T f R R' φ)).obj
          (algebraImageTarget B S hS T f R R' φ F))) := by
  rw [algebraImageScalarEnd, modulePushforward_map_globalSmul_globalSectionsRingHomSite]

/-- `ρ(ψ♯ π♯ b)` is multiplication by `b` on `V`. -/
theorem algebraImageScalarEnd_globalSectionsRingHomSite_comp (F : Modules.{u, u} B S hS X.1 X.2)
    (b : RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj) :
    algebraImageScalarEnd B S hS T f R R' φ F
        (globalSectionsRingHomSite B S hS (algebraBaseChangeMap B S hS T f R R' φ)
          (globalSectionsRingHomSite B S hS (algebraBaseChangeProjection B S hS T f R) b)) =
      globalSmul _ b (algebraImageTotal B S hS T f R R' φ F) := by
  rw [algebraImageScalarEnd_globalSectionsRingHomSite,
    modulePushforward_map_globalSmul_globalSectionsRingHomSite]

attribute [local instance 10000] smallEtaleModulesAbelian in
/-- The mono `π_*G ⟶ V`. -/
abbrev algebraImageModuleι (F : Modules.{u, u} B S hS X.1 X.2) :
    (modulePushforward B S hS (algebraBaseChangeProjection B S hS T f R)).obj
        (algebraImageModule B S hS T f R R' φ F) ⟶ algebraImageTotal B S hS T f R R' φ F :=
  (modulePushforward B S hS (algebraBaseChangeProjection B S hS T f R)).map
    (image.ι (algebraImageUnit B S hS T f R R' φ F))

attribute [local instance 10000] smallEtaleModulesAbelian in
/-- **`π_*G ⊆ V` is stable under the global functions of `X_R`.** -/
theorem algebraImageModuleι_comp_scalarEnd (F : Modules.{u, u} B S hS X.1 X.2)
    (c : RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS
      (algebraBaseChange B S hS T f R).1 (algebraBaseChange B S hS T f R).2).O).obj) :
    algebraImageModuleι B S hS T f R R' φ F ≫
        algebraImageScalarEnd B S hS T f R R' φ F
          (globalSectionsRingHomSite B S hS (algebraBaseChangeMap B S hS T f R R' φ) c) =
      (modulePushforward B S hS (algebraBaseChangeProjection B S hS T f R)).map
          (globalSmul _ c (algebraImageModule B S hS T f R R' φ F)) ≫
        algebraImageModuleι B S hS T f R R' φ F := by
  rw [algebraImageScalarEnd_globalSectionsRingHomSite, algebraImageModuleι]
  exact (CategoryTheory.Functor.map_comp _ _ _).symm.trans
    ((congrArg (modulePushforward B S hS (algebraBaseChangeProjection B S hS T f R)).map
      (Stacks.Cohomology.SiteModules.comp_globalSmul _ c
        (image.ι (algebraImageUnit B S hS T f R R' φ F)))).trans
      (CategoryTheory.Functor.map_comp _ _ _))

attribute [local instance 10000] smallEtaleModulesAbelian in
/-- `π_*` of the unit factors through `π_*G ⊆ V`. -/
theorem algebraImageTotalUnit_eq (F : Modules.{u, u} B S hS X.1 X.2) :
    algebraImageTotalUnit B S hS T f R R' φ F =
      (modulePullbackAdjunction B S hS (algebraBaseChangeProjection B S hS T f R)).unit.app F ≫
        (modulePushforward B S hS (algebraBaseChangeProjection B S hS T f R)).map
          (factorThruImage (algebraImageUnit B S hS T f R R' φ F)) ≫
        algebraImageModuleι B S hS T f R R' φ F := by
  rw [algebraImageTotalUnit, algebraImageModuleι]
  exact congrArg (_ ≫ ·) ((congrArg (modulePushforward B S hS
    (algebraBaseChangeProjection B S hS T f R)).map
      (image.fac (algebraImageUnit B S hS T f R R' φ F)).symm).trans
    (CategoryTheory.Functor.map_comp _ _ _))

attribute [local instance 10000] smallEtaleModulesAbelian in
/-- The unit `F ⟶ V` factors through `π_*G ⊆ V`. -/
theorem exists_comp_algebraImageModuleι_eq_totalUnit (F : Modules.{u, u} B S hS X.1 X.2) :
    ∃ w, w ≫ algebraImageModuleι B S hS T f R R' φ F = algebraImageTotalUnit B S hS T f R R' φ F :=
  ⟨(modulePullbackAdjunction B S hS (algebraBaseChangeProjection B S hS T f R)).unit.app F ≫
      (modulePushforward B S hS (algebraBaseChangeProjection B S hS T f R)).map
        (factorThruImage (algebraImageUnit B S hS T f R R' φ F)),
    (Category.assoc _ _ _).trans (algebraImageTotalUnit_eq B S hS T f R R' φ F).symm⟩

/-- In a commutative monoid, if `y = x t` then `x tᵐ⁺¹ = tᵐ y`. -/
theorem mul_pow_succ_eq_pow_mul_of_eq {A : Type*} [CommMonoid A] (x t y : A) (h : y = x * t)
    (m : ℕ) : x * t ^ (m + 1) = t ^ m * y := by
  rw [h, pow_succ, mul_left_comm]

section Degree

variable (F : Modules.{u, u} B S hS X.1 X.2) (N₀ : F.Submodule)
  (I : IdealSheaves B S hS X.1 X.2) {r : ℕ}
  (a : Fin r → RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj)
  (ha : ∀ i (W : SmallEtale B S hS X.1), (a i).1 (op W) ∈ I.obj (op W))
  (hgen : ∀ A : SmallEtale B S hS X.1,
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj A) →
      ∀ b ∈ I.obj (op A), ∃ c : Fin r → (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj
        (op A), b = ∑ i, c i * (a i).1 (op A))
  (t : RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS
      (algebraBaseChange B S hS T f R').1 (algebraBaseChange B S hS T f R').2).O).obj)
  (s : Fin r → RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS
      (algebraBaseChange B S hS T f R).1 (algebraBaseChange B S hS T f R).2).O).obj)
  (hs : ∀ i, globalSectionsRingHomSite B S hS (algebraBaseChangeMap B S hS T f R R' φ) (s i) =
    globalSectionsRingHomSite B S hS (algebraBaseChangeMap B S hS T f R R' φ)
      (globalSectionsRingHomSite B S hS (algebraBaseChangeProjection B S hS T f R) (a i)) * t)

/-- The inclusion `IᵐN₀ ⟶ N₀`. -/
abbrev idealPowSmulIncl (m : ℕ) :
    (Stacks.Sites.idealPowSmul (M := F) I m N₀).toSheafOfModules ⟶ N₀.toSheafOfModules :=
  Stacks.SheafOfModules.Submodule.homOfLE (Stacks.Sites.idealPowSmul_le_self I m N₀)

/-- The map `IᵐN₀ ⟶ N₀ ⟶ V ⟶ V` of degree `m`. -/
abbrev algebraImageDegreeComposite (m : ℕ) :
    (Stacks.Sites.idealPowSmul (M := F) I m N₀).toSheafOfModules ⟶
      algebraImageTotal B S hS T f R R' φ N₀.toSheafOfModules :=
  idealPowSmulIncl B S hS F N₀ I m ≫ algebraImageTotalUnit B S hS T f R R' φ N₀.toSheafOfModules ≫
    algebraImageScalarEnd B S hS T f R R' φ N₀.toSheafOfModules (t ^ m)

include ha hgen hs in
/-- **The degree-`m` map `IᵐN₀ ⟶ π_*G`**: the map `IᵐN₀ ⟶ N₀ ⟶ V` followed by `ρ(tᵐ)` factors
through `π_*G ⊆ V`. -/
theorem exists_algebraImageDegreeMap (hN : N₀.toSheafOfModules.IsQuasicoherentOnSite) (m : ℕ) :
    ∃ w, w ≫ algebraImageModuleι B S hS T f R R' φ N₀.toSheafOfModules =
        algebraImageDegreeComposite B S hS T f R R' φ F N₀ I t m := by
  refine exists_comp_eq_idealPowSmul_homOfLE_comp
    (hι := (epi_mono_modulePushforward_algebraImageModule B S hS T f R R' φ
      N₀.toSheafOfModules hN).2) N₀ I a ha hgen
    (algebraImageTotalUnit B S hS T f R R' φ N₀.toSheafOfModules)
    (fun m => algebraImageScalarEnd B S hS T f R R' φ N₀.toSheafOfModules (t ^ m))
    (algebraImageModuleι B S hS T f R R' φ N₀.toSheafOfModules)
    (fun i => algebraImageScalarEnd B S hS T f R R' φ N₀.toSheafOfModules
      (globalSectionsRingHomSite B S hS (algebraBaseChangeMap B S hS T f R R' φ) (s i)))
    (fun i => (modulePushforward B S hS (algebraBaseChangeProjection B S hS T f R)).map
      (globalSmul _ (s i) (algebraImageModule B S hS T f R R' φ N₀.toSheafOfModules)))
    ⟨idealPowSmulIncl B S hS F N₀ I 0 ≫
      (exists_comp_algebraImageModuleι_eq_totalUnit B S hS T f R R' φ N₀.toSheafOfModules).choose,
      ?_⟩
    (fun i m => ?_)
    (fun i => algebraImageModuleι_comp_scalarEnd B S hS T f R R' φ N₀.toSheafOfModules (s i)) m
  · rw [pow_zero, algebraImageScalarEnd_one, Category.comp_id, Category.assoc,
      (exists_comp_algebraImageModuleι_eq_totalUnit B S hS T f R R' φ
        N₀.toSheafOfModules).choose_spec]
  · have e4 := mul_pow_succ_eq_pow_mul_of_eq _ _ _ (hs i) m
    exact (congrArg (· ≫ algebraImageScalarEnd B S hS T f R R' φ N₀.toSheafOfModules (t ^ (m + 1)))
      (algebraImageScalarEnd_globalSectionsRingHomSite_comp B S hS T f R R' φ
        N₀.toSheafOfModules (a i)).symm).trans
      ((algebraImageScalarEnd_mul B S hS T f R R' φ N₀.toSheafOfModules _ _).symm.trans
        ((congrArg (algebraImageScalarEnd B S hS T f R R' φ N₀.toSheafOfModules) e4).trans
          (algebraImageScalarEnd_mul B S hS T f R R' φ N₀.toSheafOfModules _ _)))

end Degree

end AlgebraicGeometry.Space

end
