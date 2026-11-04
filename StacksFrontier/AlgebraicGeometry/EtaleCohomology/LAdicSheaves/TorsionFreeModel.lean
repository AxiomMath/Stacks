module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.LevelConstructibility
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.Presentation
public import StacksFrontier.CategoryTheory.Abelian.PowExactImage
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The torsion-free model `ℓᴺ F` of an ℓ-adic sheaf

For an ℓ-adic sheaf `F = {Fₙ}` and `N : ℕ`, the sheaves `F'ₙ = ℓᴺ F_{N+n}` (the image of
multiplication by `ℓᴺ` on `F_{N+n}`) are killed by `ℓⁿ⁺¹`, and the transition maps of `F` induce
maps `F'ₙ₊₁ ⟶ F'ₙ` exhibiting `F'ₙ` as `F'ₙ₊₁ / ℓⁿ⁺¹`; so they form an ℓ-adic sheaf
`ℓᴺ F`. Multiplication by `ℓᴺ` followed by the transition `F_{N+n} ⟶ Fₙ` and back gives
morphisms `F ⟶ ℓᴺ F ⟶ F` whose composites in both orders are multiplication by `ℓᴺ`: `F` and
`ℓᴺ F` are isogenous, so they define the same `ℚ_ℓ`-sheaf.

The torsion of `F` is bounded (the iterated Verschiebung kernels stabilise, which is where the
constructibility of the levels enters, through
`Stacks.EtaleCohomology.LAdicSheaf.underlyingLAdic_torsion_divisibility`), and once `N` is beyond
the bound the levels of `ℓᴺ F` are flat sheaves of `ℤ/ℓⁿ⁺¹ℤ`-modules: `ℓᴺ F` is torsion-free.
This is the first step of the proof of [Tag 03V2](https://stacks.math.columbia.edu/tag/03V2):
"we can write `F` as `F' ⊗ Q_ℓ` where `F'` is a `Z_ℓ`-sheaf without torsion".

## Main definitions

* `Stacks.EtaleCohomology.LAdicSheaf.torsionFreeModel F N`: the ℓ-adic sheaf `ℓᴺ F`.
* `Stacks.EtaleCohomology.LAdicSheaf.toTorsionFreeModel` and
  `Stacks.EtaleCohomology.LAdicSheaf.fromTorsionFreeModel`: the isogeny `F ⟶ ℓᴺ F ⟶ F`.
* `Stacks.EtaleCohomology.LAdicSheaf.torsionBound F`: a bound for the torsion of `F`.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.toTorsionFreeModel_comp_fromTorsionFreeModel` and
  `Stacks.EtaleCohomology.LAdicSheaf.fromTorsionFreeModel_comp_toTorsionFreeModel`: both
  composites are multiplication by `ℓᴺ`.
* `Stacks.EtaleCohomology.LAdicSheaf.powExact_torsionFreeModel_level`: beyond the torsion bound,
  every level of `ℓᴺ F` is flat over `ℤ/ℓⁿ⁺¹ℤ`.

## References

* [Stacks Project, Tag 03V2](https://stacks.math.columbia.edu/tag/03V2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

variable {B : BigEtaleSite.{u}} {X : B.Scheme} {ℓ : ℕ}

variable [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

attribute [local instance] underlyingLevelFunctor_additive
  underlyingLevelFunctor_preservesMonomorphisms underlyingLevelFunctor_isLeftAdjoint
  underlyingLevelFunctor_preservesKernels underlyingLevelFunctor_full

variable [Fact ℓ.Prime] [IsNoetherian X.1]

namespace LAdicSheaf

attribute [local instance] underlyingTransitionLE_epi

/-- The image `ℓᴺ F_{N+n}` of multiplication by `ℓᴺ` on the underlying level `N + n`. -/
def torsionFreeModelImage (F : LAdicSheaf.{u, u + 1} B X ℓ) (N n : ℕ) :
    Sheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{u + 1} :=
  Abelian.image ((ℓ ^ N) • 𝟙 (underlyingLAdicLevel B X ℓ F (N + n)))

/-- `ℓᴺ F_{N+n}` is killed by `ℓⁿ⁺¹`. -/
theorem torsionFreeModelImage_annihilated (F : LAdicSheaf.{u, u + 1} B X ℓ) (N n : ℕ) :
    (ℓ ^ (n + 1)) • 𝟙 (torsionFreeModelImage F N n) = 0 :=
  abelianImage_pow_nsmul_eq_zero (N := N) (underlyingLAdicLevel_annihilated B X ℓ F (N + n))

/-- `ℓᴺ F_{N+n}` is killed by `ℓⁿ⁺¹`, sectionwise. -/
theorem torsionFreeModelImage_annihilated_app (F : LAdicSheaf.{u, u + 1} B X ℓ) (N n : ℕ)
    (U : (SmallEtale B X.1 X.property)ᵒᵖ) (x : (torsionFreeModelImage F N n).obj.obj U) :
    (ℓ ^ (n + 1)) • x = 0 := by
  have h := congrArg (fun f => (f.hom.app U).hom x) (torsionFreeModelImage_annihilated F N n)
  rwa [abelianSheaf_nsmul_app] at h

/-- The level `n` of `ℓᴺ F`: the sheaf `ℓᴺ F_{N+n}`, as a sheaf of `ℤ/ℓⁿ⁺¹ℤ`-modules. -/
def torsionFreeModelLevel (F : LAdicSheaf.{u, u + 1} B X ℓ) (N n : ℕ) :
    FiniteLevelSheaf.{u, u + 1} B X ℓ n :=
  zmodSheafOfAnnihilated.{u + 1, u + 1, u} (SmallEtale.topology B X.1 X.property) (ℓ ^ (n + 1))
    (torsionFreeModelImage F N n) (torsionFreeModelImage_annihilated_app F N n)

/-- The underlying sheaf of abelian groups of the level `n` of `ℓᴺ F` is `ℓᴺ F_{N+n}`. -/
def torsionFreeModelLevelIso (F : LAdicSheaf.{u, u + 1} B X ℓ) (N n : ℕ) :
    (underlyingLevelFunctor B X ℓ n).obj (torsionFreeModelLevel F N n) ≅
      torsionFreeModelImage F N n :=
  zmodSheafOfAnnihilatedIso.{u + 1, u + 1, u} _ _ _ _

/-- Multiplication by `ℓᴺ` from `F_{N+n}` onto the level `n` of `ℓᴺ F`. -/
def torsionFreeModelπ (F : LAdicSheaf.{u, u + 1} B X ℓ) (N n : ℕ) :
    underlyingLAdicLevel B X ℓ F (N + n) ⟶
      (underlyingLevelFunctor B X ℓ n).obj (torsionFreeModelLevel F N n) :=
  Abelian.factorThruImage _ ≫ (torsionFreeModelLevelIso F N n).inv

/-- The inclusion of the level `n` of `ℓᴺ F` into `F_{N+n}`. -/
def torsionFreeModelι (F : LAdicSheaf.{u, u + 1} B X ℓ) (N n : ℕ) :
    (underlyingLevelFunctor B X ℓ n).obj (torsionFreeModelLevel F N n) ⟶
      underlyingLAdicLevel B X ℓ F (N + n) :=
  (torsionFreeModelLevelIso F N n).hom ≫ Abelian.image.ι _

/-- Multiplication by `ℓᴺ` from `F_{N+n}` onto `ℓᴺ F_{N+n}` is an epimorphism. -/
instance (F : LAdicSheaf.{u, u + 1} B X ℓ) (N n : ℕ) : Epi (torsionFreeModelπ F N n) :=
  epi_factorThruImage_comp_inv _ _

/-- The inclusion `ℓᴺ F_{N+n} ⊆ F_{N+n}` is a monomorphism. -/
instance (F : LAdicSheaf.{u, u + 1} B X ℓ) (N n : ℕ) : Mono (torsionFreeModelι F N n) :=
  mono_hom_comp_image_ι _ _

/-- `ℓᴺ F_{N+n} ⊆ F_{N+n}` factors multiplication by `ℓᴺ`. -/
@[reassoc]
theorem torsionFreeModelπ_ι (F : LAdicSheaf.{u, u + 1} B X ℓ) (N n : ℕ) :
    torsionFreeModelπ F N n ≫ torsionFreeModelι F N n =
      (ℓ ^ N) • 𝟙 (underlyingLAdicLevel B X ℓ F (N + n)) :=
  factorThruImage_comp_inv_comp_hom_comp_image_ι _ _

/-- The underlying level `n` of `ℓᴺ F` is killed by `ℓⁿ⁺¹`. -/
theorem torsionFreeModelLevel_annihilated (F : LAdicSheaf.{u, u + 1} B X ℓ) (N n : ℕ) :
    (ℓ ^ (n + 1)) • 𝟙 ((underlyingLevelFunctor B X ℓ n).obj (torsionFreeModelLevel F N n)) = 0 :=
  image_pow_nsmul_eq_zero (N := N) (underlyingLAdicLevel_annihilated B X ℓ F (N + n))
    (torsionFreeModelπ F N n) (torsionFreeModelι F N n) (torsionFreeModelπ_ι F N n)

/-- The transition `F_{N+n+1} ⟶ F_{N+n}` kills the kernel of `ℓᴺ` on `F_{N+n+1}`. -/
theorem torsionFreeModel_kernel_condition (F : LAdicSheaf.{u, u + 1} B X ℓ) (N n : ℕ) :
    kernel.ι (torsionFreeModelπ F N (n + 1)) ≫
      underlyingLAdicTransition B X ℓ F (N + n) ≫ torsionFreeModelπ F N n = 0 := by
  rw [← cancel_mono (torsionFreeModelι F N n), Category.assoc, Category.assoc,
    torsionFreeModelπ_ι, ← nsmul_id_comp, ← torsionFreeModelπ_ι F N (n + 1), Category.assoc,
    kernel.condition_assoc, zero_comp, zero_comp]

/-- The transition `ℓᴺ F_{N+n+1} ⟶ ℓᴺ F_{N+n}` of the underlying sheaves of `ℓᴺ F`, induced by the
transition of `F`. -/
def torsionFreeModelUnderlyingTransition (F : LAdicSheaf.{u, u + 1} B X ℓ) (N n : ℕ) :
    (underlyingLevelFunctor B X ℓ (n + 1)).obj (torsionFreeModelLevel F N (n + 1)) ⟶
      (underlyingLevelFunctor B X ℓ n).obj (torsionFreeModelLevel F N n) :=
  epiDesc (torsionFreeModelπ F N (n + 1))
    (underlyingLAdicTransition B X ℓ F (N + n) ≫ torsionFreeModelπ F N n)
    (torsionFreeModel_kernel_condition F N n)

/-- The transition of `ℓᴺ F` lies over that of `F`. -/
@[reassoc]
theorem torsionFreeModelπ_underlyingTransition (F : LAdicSheaf.{u, u + 1} B X ℓ) (N n : ℕ) :
    torsionFreeModelπ F N (n + 1) ≫ torsionFreeModelUnderlyingTransition F N n =
      underlyingLAdicTransition B X ℓ F (N + n) ≫ torsionFreeModelπ F N n :=
  comp_epiDesc _ _ _

/-- The transition `F'ₙ₊₁ ⟶ F'ₙ` of `ℓᴺ F`, as a map of sheaves of `ℤ/ℓⁿ⁺²ℤ`-modules. -/
def torsionFreeModelTransition (F : LAdicSheaf.{u, u + 1} B X ℓ) (N n : ℕ) :
    torsionFreeModelLevel F N (n + 1) ⟶
      (restrictScalarsFunctor B X ℓ n).obj (torsionFreeModelLevel F N n) :=
  (underlyingLevelFunctor B X ℓ (n + 1)).preimage
    (torsionFreeModelUnderlyingTransition F N n :
      _ ⟶ (underlyingLevelFunctor B X ℓ (n + 1)).obj
        ((restrictScalarsFunctor B X ℓ n).obj (torsionFreeModelLevel F N n)))

/-- The underlying map of the transition of `ℓᴺ F` is `torsionFreeModelUnderlyingTransition`. -/
theorem underlyingLevelFunctor_map_torsionFreeModelTransition (F : LAdicSheaf.{u, u + 1} B X ℓ)
    (N n : ℕ) :
    (underlyingLevelFunctor B X ℓ (n + 1)).map (torsionFreeModelTransition F N n) =
      torsionFreeModelUnderlyingTransition F N n :=
  (underlyingLevelFunctor B X ℓ (n + 1)).map_preimage _

/-- **The transitions of `ℓᴺ F` satisfy the compatibility of Tag 03UM**: `F'ₙ = F'ₙ₊₁ / ℓⁿ⁺¹`. -/
theorem torsionFreeModelTransition_reduction_isIso (F : LAdicSheaf.{u, u + 1} B X ℓ) (N n : ℕ) :
    IsIso (FiniteLevelSheaf.scalarReductionMap B X ℓ n (torsionFreeModelLevel F N (n + 1))
      (torsionFreeModelLevel F N n) (torsionFreeModelTransition F N n)) := by
  have hτ : torsionFreeModelπ F N (n + 1) ≫
      (underlyingLevelFunctor B X ℓ (n + 1)).map (torsionFreeModelTransition F N n) =
        underlyingLAdicTransition B X ℓ F (N + n) ≫ torsionFreeModelπ F N n := by
    rw [underlyingLevelFunctor_map_torsionFreeModelTransition]
    exact torsionFreeModelπ_underlyingTransition F N n
  exact reduction_isIso_of_underlying_cokernel B X ℓ n _ _ _ _
    (isColimitImageTransition (N := N) (underlyingLAdicLevel_annihilated B X ℓ F (N + n))
      (underlyingLAdicTransition B X ℓ F (N + n))
      (underlyingTransition_condition B X ℓ F (N + n))
      (underlyingTransition_isCokernel B X ℓ F (N + n))
      (torsionFreeModelπ F N (n + 1)) (torsionFreeModelι F N (n + 1))
      (torsionFreeModelπ_ι F N (n + 1))
      (torsionFreeModelπ F N n) (torsionFreeModelι F N n) (torsionFreeModelπ_ι F N n) _ hτ)

/-- `ℓᴺ` on `F_{N+n}` kills `ℓⁿ⁺¹ F_{N+n}`. -/
theorem torsionFreeModelπ_condition (F : LAdicSheaf.{u, u + 1} B X ℓ) (N n : ℕ) :
    ((ℓ ^ (n + 1)) • 𝟙 (underlyingLAdicLevel B X ℓ F (N + n))) ≫ torsionFreeModelπ F N n = 0 := by
  rw [nsmul_id_comp, torsionFreeModelLevel_annihilated, Limits.comp_zero]

/-- The map `Fₙ ⟶ ℓᴺ F_{N+n}`, `x ↦ ℓᴺ x̃`, on underlying sheaves: multiplication by `ℓᴺ`
descends along the quotient `F_{N+n} ⟶ Fₙ` by `ℓⁿ⁺¹`. -/
def toTorsionFreeModelUnderlying (F : LAdicSheaf.{u, u + 1} B X ℓ) (N n : ℕ) :
    underlyingLAdicLevel B X ℓ F n ⟶
      (underlyingLevelFunctor B X ℓ n).obj (torsionFreeModelLevel F N n) :=
  (CokernelCofork.IsColimit.desc' (underlyingTransitionLE_isCokernel B X ℓ F
    (Nat.le_add_left n N)) (torsionFreeModelπ F N n) (torsionFreeModelπ_condition F N n)).1

/-- The transition `F_{N+n} ⟶ Fₙ` followed by `Fₙ ⟶ ℓᴺ F_{N+n}` is multiplication by `ℓᴺ`. -/
@[reassoc]
theorem transitionLE_toTorsionFreeModelUnderlying (F : LAdicSheaf.{u, u + 1} B X ℓ) (N n : ℕ) :
    underlyingTransitionLE B X ℓ F (Nat.le_add_left n N) ≫ toTorsionFreeModelUnderlying F N n =
      torsionFreeModelπ F N n :=
  (CokernelCofork.IsColimit.desc' (underlyingTransitionLE_isCokernel B X ℓ F
    (Nat.le_add_left n N)) (torsionFreeModelπ F N n) (torsionFreeModelπ_condition F N n)).2

/-- The map `Fₙ ⟶ ℓᴺ F_{N+n}` on underlying sheaves is an epimorphism. -/
instance (F : LAdicSheaf.{u, u + 1} B X ℓ) (N n : ℕ) :
    Epi (toTorsionFreeModelUnderlying F N n) :=
  epi_of_epi_fac (transitionLE_toTorsionFreeModelUnderlying F N n)

/-- The map `Fₙ ⟶ ℓᴺ F_{N+n}`, `x ↦ ℓᴺ x̃`, as a map of sheaves of `ℤ/ℓⁿ⁺¹ℤ`-modules. -/
def toTorsionFreeModelApp (F : LAdicSheaf.{u, u + 1} B X ℓ) (N n : ℕ) :
    F.level n ⟶ torsionFreeModelLevel F N n :=
  (underlyingLevelFunctor B X ℓ n).preimage (toTorsionFreeModelUnderlying F N n)

/-- The underlying map of `toTorsionFreeModelApp` is `toTorsionFreeModelUnderlying`. -/
theorem underlyingLevelFunctor_map_toTorsionFreeModelApp (F : LAdicSheaf.{u, u + 1} B X ℓ)
    (N n : ℕ) :
    (underlyingLevelFunctor B X ℓ n).map (toTorsionFreeModelApp F N n) =
      toTorsionFreeModelUnderlying F N n :=
  (underlyingLevelFunctor B X ℓ n).map_preimage _

/-- The map `Fₙ ⟶ ℓᴺ F_{N+n}` of sheaves of `ℤ/ℓⁿ⁺¹ℤ`-modules is an epimorphism. -/
instance (F : LAdicSheaf.{u, u + 1} B X ℓ) (N n : ℕ) : Epi (toTorsionFreeModelApp F N n) := by
  apply (underlyingLevelFunctor B X ℓ n).epi_of_epi_map
  rw [underlyingLevelFunctor_map_toTorsionFreeModelApp]
  infer_instance

/-- **The ℓ-adic sheaf `ℓᴺ F`**, with levels `ℓᴺ F_{N+n}`. Its levels are constructible, being
quotients of the levels of `F`. -/
def torsionFreeModel (F : LAdicSheaf.{u, u + 1} B X ℓ) (N : ℕ) : LAdicSheaf.{u, u + 1} B X ℓ where
  level n := torsionFreeModelLevel F N n
  constructible n := FiniteLevelSheaf.isConstructible_of_epi B X ℓ n
    (toTorsionFreeModelApp F N n) (F.constructible n)
  transition n := torsionFreeModelTransition F N n
  reduction_isIso n := torsionFreeModelTransition_reduction_isIso F N n

/-- The transitions `F_{N+n+1} ⟶ F_{N+n} ⟶ Fₙ` and `F_{N+n+1} ⟶ F_{n+1} ⟶ Fₙ` agree. -/
theorem underlyingTransition_comp_transitionLE (F : LAdicSheaf.{u, u + 1} B X ℓ) (N n : ℕ) :
    underlyingLAdicTransition B X ℓ F (N + n) ≫
        underlyingTransitionLE B X ℓ F (Nat.le_add_left n N) =
      underlyingTransitionLE B X ℓ F (Nat.le_add_left (n + 1) N) ≫
        underlyingLAdicTransition B X ℓ F n := by
  rw [← underlyingTransitionLE_succ, ← underlyingTransitionLE_succ, underlyingTransitionLE_comp,
    underlyingTransitionLE_comp]

/-- `Fₙ ⟶ ℓᴺ F_{N+n}` commutes with the transitions, on underlying sheaves. -/
theorem toTorsionFreeModelUnderlying_naturality (F : LAdicSheaf.{u, u + 1} B X ℓ) (N n : ℕ) :
    toTorsionFreeModelUnderlying F N (n + 1) ≫ torsionFreeModelUnderlyingTransition F N n =
      underlyingLAdicTransition B X ℓ F n ≫ toTorsionFreeModelUnderlying F N n := by
  rw [← cancel_epi (underlyingTransitionLE B X ℓ F (Nat.le_add_left (n + 1) N)),
    transitionLE_toTorsionFreeModelUnderlying_assoc, torsionFreeModelπ_underlyingTransition,
    ← Category.assoc, ← underlyingTransition_comp_transitionLE, Category.assoc,
    transitionLE_toTorsionFreeModelUnderlying]

/-- The map `F ⟶ ℓᴺ F`, `x ↦ ℓᴺ x̃` at every level. -/
def toTorsionFreeModel (F : LAdicSheaf.{u, u + 1} B X ℓ) (N : ℕ) : F ⟶ torsionFreeModel F N where
  app n := toTorsionFreeModelApp F N n
  naturality n := by
    apply (underlyingLevelFunctor B X ℓ (n + 1)).map_injective
    change (underlyingLevelFunctor B X ℓ (n + 1)).map (toTorsionFreeModelApp F N (n + 1) ≫
        torsionFreeModelTransition F N n) =
      (underlyingLevelFunctor B X ℓ (n + 1)).map (F.transition n) ≫
        (underlyingLevelFunctor B X ℓ n).map (toTorsionFreeModelApp F N n)
    rw [Functor.map_comp, underlyingLevelFunctor_map_toTorsionFreeModelApp,
      underlyingLevelFunctor_map_toTorsionFreeModelApp,
      underlyingLevelFunctor_map_torsionFreeModelTransition]
    exact toTorsionFreeModelUnderlying_naturality F N n

/-- The map `ℓᴺ F_{N+n} ⊆ F_{N+n} ⟶ Fₙ` on underlying sheaves. -/
def fromTorsionFreeModelUnderlying (F : LAdicSheaf.{u, u + 1} B X ℓ) (N n : ℕ) :
    (underlyingLevelFunctor B X ℓ n).obj (torsionFreeModelLevel F N n) ⟶
      underlyingLAdicLevel B X ℓ F n :=
  torsionFreeModelι F N n ≫ underlyingTransitionLE B X ℓ F (Nat.le_add_left n N)

/-- The map `ℓᴺ F_{N+n} ⊆ F_{N+n} ⟶ Fₙ`, as a map of sheaves of `ℤ/ℓⁿ⁺¹ℤ`-modules. -/
def fromTorsionFreeModelApp (F : LAdicSheaf.{u, u + 1} B X ℓ) (N n : ℕ) :
    torsionFreeModelLevel F N n ⟶ F.level n :=
  (underlyingLevelFunctor B X ℓ n).preimage (fromTorsionFreeModelUnderlying F N n)

/-- The underlying map of `fromTorsionFreeModelApp` is `fromTorsionFreeModelUnderlying`. -/
theorem underlyingLevelFunctor_map_fromTorsionFreeModelApp (F : LAdicSheaf.{u, u + 1} B X ℓ)
    (N n : ℕ) :
    (underlyingLevelFunctor B X ℓ n).map (fromTorsionFreeModelApp F N n) =
      fromTorsionFreeModelUnderlying F N n :=
  (underlyingLevelFunctor B X ℓ n).map_preimage _

/-- `ℓᴺ F_{N+n} ⟶ Fₙ` commutes with the transitions, on underlying sheaves. -/
theorem fromTorsionFreeModelUnderlying_naturality (F : LAdicSheaf.{u, u + 1} B X ℓ) (N n : ℕ) :
    fromTorsionFreeModelUnderlying F N (n + 1) ≫ underlyingLAdicTransition B X ℓ F n =
      torsionFreeModelUnderlyingTransition F N n ≫ fromTorsionFreeModelUnderlying F N n := by
  rw [← cancel_epi (torsionFreeModelπ F N (n + 1)), torsionFreeModelπ_underlyingTransition_assoc]
  simp only [fromTorsionFreeModelUnderlying, Category.assoc]
  rw [torsionFreeModelπ_ι_assoc, torsionFreeModelπ_ι_assoc,
    ← underlyingTransition_comp_transitionLE, ← Category.assoc, nsmul_id_comp, Category.assoc]

/-- The map `ℓᴺ F ⟶ F`, the inclusion `ℓᴺ F_{N+n} ⊆ F_{N+n}` followed by the transition to
`Fₙ`. -/
def fromTorsionFreeModel (F : LAdicSheaf.{u, u + 1} B X ℓ) (N : ℕ) :
    torsionFreeModel F N ⟶ F where
  app n := fromTorsionFreeModelApp F N n
  naturality n := by
    apply (underlyingLevelFunctor B X ℓ (n + 1)).map_injective
    change (underlyingLevelFunctor B X ℓ (n + 1)).map (fromTorsionFreeModelApp F N (n + 1) ≫
        F.transition n) =
      (underlyingLevelFunctor B X ℓ (n + 1)).map (torsionFreeModelTransition F N n) ≫
        (underlyingLevelFunctor B X ℓ n).map (fromTorsionFreeModelApp F N n)
    rw [Functor.map_comp, underlyingLevelFunctor_map_fromTorsionFreeModelApp,
      underlyingLevelFunctor_map_fromTorsionFreeModelApp,
      underlyingLevelFunctor_map_torsionFreeModelTransition]
    exact fromTorsionFreeModelUnderlying_naturality F N n

/-- The underlying map of a morphism of ℓ-adic sheaves which is multiplication by `k` at every
level. -/
theorem underlyingLevelFunctor_map_nsmul_id (F : LAdicSheaf.{u, u + 1} B X ℓ) (k n : ℕ) :
    (underlyingLevelFunctor B X ℓ n).map (k • 𝟙 (F.level n)) =
      k • 𝟙 (underlyingLAdicLevel B X ℓ F n) := by
  rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]

/-- `Fₙ ⟶ ℓᴺ F_{N+n} ⟶ Fₙ` is multiplication by `ℓᴺ`, on underlying sheaves. -/
theorem toTorsionFreeModelUnderlying_comp (F : LAdicSheaf.{u, u + 1} B X ℓ) (N n : ℕ) :
    toTorsionFreeModelUnderlying F N n ≫ fromTorsionFreeModelUnderlying F N n =
      (ℓ ^ N) • 𝟙 (underlyingLAdicLevel B X ℓ F n) := by
  rw [← cancel_epi (underlyingTransitionLE B X ℓ F (Nat.le_add_left n N)),
    transitionLE_toTorsionFreeModelUnderlying_assoc, fromTorsionFreeModelUnderlying,
    torsionFreeModelπ_ι_assoc, nsmul_id_comp]

/-- `ℓᴺ F_{N+n} ⟶ Fₙ ⟶ ℓᴺ F_{N+n}` is multiplication by `ℓᴺ`, on underlying sheaves. -/
theorem fromTorsionFreeModelUnderlying_comp (F : LAdicSheaf.{u, u + 1} B X ℓ) (N n : ℕ) :
    fromTorsionFreeModelUnderlying F N n ≫ toTorsionFreeModelUnderlying F N n =
      (ℓ ^ N) • 𝟙 ((underlyingLevelFunctor B X ℓ n).obj (torsionFreeModelLevel F N n)) := by
  rw [← cancel_epi (torsionFreeModelπ F N n), ← cancel_mono (torsionFreeModelι F N n)]
  simp only [fromTorsionFreeModelUnderlying, Category.assoc,
    transitionLE_toTorsionFreeModelUnderlying_assoc, torsionFreeModelπ_ι_assoc,
    torsionFreeModelπ_ι, Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.id_comp,
    Category.comp_id]

/-- A composite of morphisms of ℓ-adic sheaves is multiplication by `k` if it is so on the
underlying sheaves of every level. -/
private theorem comp_eq_nsmul_id_of_map_underlying {F G : LAdicSheaf.{u, u + 1} B X ℓ} {k : ℕ}
    (φ : F ⟶ G) (ψ : G ⟶ F)
    (h : ∀ n, (underlyingLevelFunctor B X ℓ n).map (φ.app n) ≫
      (underlyingLevelFunctor B X ℓ n).map (ψ.app n) = k • 𝟙 (underlyingLAdicLevel B X ℓ F n)) :
    φ ≫ ψ = k • 𝟙 F := by
  refine LAdicSheaf.Hom.ext _ _ _ fun n => ?_
  change φ.app n ≫ ψ.app n = k • 𝟙 (F.level n)
  apply (underlyingLevelFunctor B X ℓ n).map_injective
  rw [Functor.map_comp, h, underlyingLevelFunctor_map_nsmul_id]

/-- **`F ⟶ ℓᴺ F ⟶ F` is multiplication by `ℓᴺ`.** -/
theorem toTorsionFreeModel_comp_fromTorsionFreeModel (F : LAdicSheaf.{u, u + 1} B X ℓ) (N : ℕ) :
    toTorsionFreeModel F N ≫ fromTorsionFreeModel F N = (ℓ ^ N) • 𝟙 F := by
  refine comp_eq_nsmul_id_of_map_underlying _ _ fun n => ?_
  erw [underlyingLevelFunctor_map_toTorsionFreeModelApp F N n,
    underlyingLevelFunctor_map_fromTorsionFreeModelApp F N n]
  exact toTorsionFreeModelUnderlying_comp F N n

/-- **`ℓᴺ F ⟶ F ⟶ ℓᴺ F` is multiplication by `ℓᴺ`.** -/
theorem fromTorsionFreeModel_comp_toTorsionFreeModel (F : LAdicSheaf.{u, u + 1} B X ℓ) (N : ℕ) :
    fromTorsionFreeModel F N ≫ toTorsionFreeModel F N = (ℓ ^ N) • 𝟙 (torsionFreeModel F N) := by
  refine comp_eq_nsmul_id_of_map_underlying _ _ fun n => ?_
  erw [underlyingLevelFunctor_map_toTorsionFreeModelApp F N n,
    underlyingLevelFunctor_map_fromTorsionFreeModelApp F N n]
  exact fromTorsionFreeModelUnderlying_comp F N n

/-- A bound for the torsion of `F`: beyond it, `ℓⁿ` times a map into level `m` killed by `ℓᵐ` is
divisible by `ℓⁿ⁺¹`. -/
def torsionBound (F : LAdicSheaf.{u, u + 1} B X ℓ) : ℕ :=
  (underlyingLAdic_torsion_divisibility B X ℓ F).choose

/-- Beyond the torsion bound, multiplication by `ℓᴺ` on `F_{N+n}` makes torsion divisible. -/
theorem torsionBound_divisible (F : LAdicSheaf.{u, u + 1} B X ℓ) {N : ℕ} (hN : torsionBound F ≤ N)
    (n : ℕ) ⦃T : Sheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{u + 1}⦄
    (g : T ⟶ underlyingLAdicLevel B X ℓ F (N + n)) (hg : (ℓ ^ (N + n)) • g = 0) :
    ∃ (T' : Sheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{u + 1}) (π : T' ⟶ T)
      (_ : Epi π) (y : T' ⟶ underlyingLAdicLevel B X ℓ F (N + n)),
      π ≫ ((ℓ ^ N) • g) = (ℓ ^ (N + 1)) • y := by
  have h := (underlyingLAdic_torsion_divisibility B X ℓ F).choose_spec N (N + n) hN
    (Nat.le_add_right N n) T g hg
  obtain ⟨T', π, hπ, y, hy⟩ :=
    (ShortComplex.exact_cokernel ((ℓ ^ (N + 1)) • 𝟙 (underlyingLAdicLevel B X ℓ F (N + n))))
      |>.exact_up_to_refinements _ h
  refine ⟨T', π, hπ, y, ?_⟩
  change π ≫ ((ℓ ^ N) • g) = y ≫ ((ℓ ^ (N + 1)) • 𝟙 _) at hy
  rw [hy, Preadditive.comp_nsmul, Category.comp_id]

/-- **The levels of `ℓᴺ F` are flat**: beyond the torsion bound, each level `ℓᴺ F_{N+n}` is a flat
sheaf of `ℤ/ℓⁿ⁺¹ℤ`-modules. -/
@[sga "4½ Rapport 2.8" "partial"]
theorem powExact_torsionFreeModel_level (F : LAdicSheaf.{u, u + 1} B X ℓ) {N : ℕ}
    (hN : torsionBound F ≤ N) (n : ℕ) :
    PowExact ℓ (n + 1) ((torsionFreeModel F N).level n) := by
  show PowExact ℓ (n + 1) (torsionFreeModelLevel F N n)
  refine PowExact.of_map (underlyingLevelFunctor B X ℓ n) ?_
    (powExact_of_image (torsionBound_divisible F hN n) (torsionFreeModelπ F N n)
      (torsionFreeModelι F N n) (torsionFreeModelπ_ι F N n))
  apply (underlyingLevelFunctor B X ℓ n).map_injective
  rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero]
  exact torsionFreeModelLevel_annihilated F N n

end LAdicSheaf

end Stacks.EtaleCohomology
