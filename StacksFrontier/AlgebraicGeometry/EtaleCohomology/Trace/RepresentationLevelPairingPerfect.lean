module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationDualPairingAssembly
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseEtaleSheafTensorStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseTrivialConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseSheafStalkLinear
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.TensorPairingExt
public import StacksFrontier.CategoryTheory.Sites.Point.ExactPairingFiberPerfect
public import StacksFrontier.CategoryTheory.Monoidal.Rigid

/-!
# The pairing of the levels of `ℱ_ρ` and of its dual coefficients, perfect on all fibres

Let `ρ₀ : π₁(X, x̄) → GL_r(ℤ_ℓ)` be continuous. At level `k` the module `(ℤ/ℓᵏ)^r` of `ρ₀` and that
of its contragredient `ρ₀^∨` are paired by the dot product, invariantly
(`Stacks.EtaleCohomology.levelRepresentation_dotProduct_contragredient`), which gives a morphism
`ℱ_{ρ₀,k} ⊗ ℱ_{ρ₀^∨,k} ⟶ ℤ/ℓᵏ` of sheaves on Mathlib's small étale site
(`Stacks.EtaleCohomology.lisseEtaleSheafTensorHom`, followed by the identification of the lisse
sheaf of the trivial module with the constant sheaf). On the stalk at a geometric point it is the
dot product (`Stacks.EtaleCohomology.lisseEtaleSheafStalkCounit_tensorHom`), hence perfect; so it
is the evaluation of an exact pairing (`Stacks.SheafDuality.exactPairingOfPerfect`), exact
pairings are carried to exact pairings by the monoidal inverse image and fibre functors
(`CategoryTheory.ExactPairing.map`), and the evaluation of an exact pairing of modules is perfect
(`Stacks.SheafDuality.bijective_curry_evaluation_of_exactPairing`). This proves
`Stacks.EtaleCohomology.LAdicSheaf.RepresentationLevelPairingInput`, hence the dual coefficients
input of the purity half of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main definitions

* `Stacks.EtaleCohomology.levelDotPairing`: the dot product of the level modules.
* `Stacks.EtaleCohomology.levelTensorHom`: the pairing of sheaves.

## Main results

* `Stacks.EtaleCohomology.bijective_levelTensorHom_ulift`.
* `Stacks.EtaleCohomology.LAdicSheaf.representationLevelPairingInput`.
* `Stacks.EtaleCohomology.LAdicSheaf.representationDualPairingInput`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale Stacks.Frobenius
open Matrix

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize Sheaf.monoidalCategory

/-! ### Flat fibres at lifted points -/

/-- The fibre of an étale sheaf of modules at the universe lift of a point is flat when the fibre
at the point is. -/
theorem flat_sheafFiber_ulift_of_flat (Λ : Type) [CommRing Λ] {S : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ S) (K : EtaleModules.{u, 0} Λ S)
    (h : Module.Flat Λ ((Scheme.pointSmallEtale t).sheafFiber
      (A := ModuleCat.{u + 1} Λ) |>.obj K)) :
    Module.Flat Λ (((Scheme.pointSmallEtale t).ulift.{u + 1}).sheafFiber
      (A := ModuleCat.{u + 1} Λ) |>.obj K) :=
  have := h
  Module.Flat.of_linearEquiv (((Scheme.pointSmallEtale t).sheafFiberUliftNatIso
    (ModuleCat.{u + 1} Λ)).app K).toLinearEquiv

/-! ### The dot product of the level modules -/

section Dot

variable {X : Scheme.{u}} [ConnectedSpace X] {x : GeometricPoint X} {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}
  (ρ₀ : EtaleFundamentalGroup X x →* GL (Fin r) ℤ_[ℓ]) (hρ₀ : Continuous ρ₀) (k : ℕ)
  [NeZero (ℓ ^ k)]

/-- **The dot product of the level modules** of `ρ₀` and of its contragredient, with values in
`ℤ/ℓᵏ` with the trivial action. -/
def levelDotPairing :
    (levelModule.{u + 1, u + 1} ρ₀ hρ₀ k).obj.obj.obj.V →ₗ[ZMod (ℓ ^ k)]
      (levelModule.{u + 1, u + 1} (contragredient ρ₀) (continuous_contragredient hρ₀)
        k).obj.obj.obj.V
        →ₗ[ZMod (ℓ ^ k)]
      (trivialContinuousModule (G := EtaleFundamentalGroup X x) (ℓ ^ k)).obj.obj.obj.V :=
  LinearMap.mk₂ (ZMod (ℓ ^ k))
    (fun (a b : ULift.{u + 1} (Fin r → ZMod (ℓ ^ k))) ↦
      (ULift.up (a.down ⬝ᵥ b.down) : ULift.{u + 1} (ZMod (ℓ ^ k))))
    (fun a₁ a₂ b ↦ ULift.ext _ _ (add_dotProduct a₁.down a₂.down b.down))
    (fun c a b ↦ ULift.ext _ _ (smul_dotProduct c a.down b.down))
    (fun a b₁ b₂ ↦ ULift.ext _ _ (dotProduct_add a.down b₁.down b₂.down))
    (fun c a b ↦ ULift.ext _ _ (dotProduct_smul c a.down b.down))

omit [NeZero (ℓ ^ k)] in
/-- The value of `levelDotPairing` at `a` and `b` is the dot product of the underlying vectors. -/
theorem levelDotPairing_apply (a b) :
    (levelDotPairing ρ₀ hρ₀ k a b).down =
      (a : ULift.{u + 1} (Fin r → ZMod (ℓ ^ k))).down ⬝ᵥ
        (b : ULift.{u + 1} (Fin r → ZMod (ℓ ^ k))).down :=
  rfl

omit [NeZero (ℓ ^ k)] in
/-- The dot product of the level modules is `π₁`-equivariant. -/
theorem levelDotPairing_equivariant (g : EtaleFundamentalGroup X x) (a b) :
    levelDotPairing ρ₀ hρ₀ k
        (((levelModule.{u + 1, u + 1} ρ₀ hρ₀ k).obj.obj.obj.ρ g).hom a)
        (((levelModule.{u + 1, u + 1} (contragredient ρ₀) (continuous_contragredient hρ₀)
          k).obj.obj.obj.ρ g).hom b) =
      ((trivialContinuousModule (G := EtaleFundamentalGroup X x) (ℓ ^ k)).obj.obj.obj.ρ g).hom
        (levelDotPairing ρ₀ hρ₀ k a b) :=
  ULift.ext _ _ (levelRepresentation_dotProduct_contragredient ρ₀ k g _ _)

omit [NeZero (ℓ ^ k)] in
/-- **The dot product is nondegenerate** in the first variable. -/
theorem levelDotPairing_eq_zero_of_forall (a)
    (h : ∀ b, levelDotPairing ρ₀ hρ₀ k a b = 0) : a = 0 := by
  refine ULift.ext _ _ (funext fun i ↦ ?_)
  have := congrArg ULift.down (h (ULift.up (Pi.single i 1)))
  change (a : ULift.{u + 1} (Fin r → ZMod (ℓ ^ k))).down ⬝ᵥ Pi.single i 1 = 0 at this
  rwa [dotProduct_single, mul_one] at this

end Dot

/-! ### The pairing of sheaves, perfect on geometric fibres -/

section Pairing

/-- Presheaves of `ZMod N`-modules on the small étale site of `Y` over `V` can be sheafified. -/
local instance hasWeakSheafify_smallEtale_over_zmod' (Y : Scheme.{u}) (N : ℕ) (V : Y.Etale) :
    HasWeakSheafify (Y.smallEtaleTopology.over V) (ModuleCat.{u + 1} (ZMod N)) :=
  haveI := Stacks.ConstantSheaf.hasSheafify_moduleCat.{u + 1, u, 0, u + 1}
    (Y.smallEtaleTopology.over V) (ZMod N)
  inferInstance

/-- The morphisms of presheaves of `Λ`-modules on the small étale site of `S` inverted by
sheafification form a monoidal class. -/
local instance (Λ : Type) [CommRing Λ] (S : Scheme.{u}) :
    (S.smallEtaleTopology.W (A := ModuleCat.{u + 1} Λ)).IsMonoidal :=
  isMonoidal_W_etaleModules (Λ := Λ) S

attribute [local instance] AlgebraicGeometry.moduleCat_preservesColimits_tensorLeft
  AlgebraicGeometry.moduleCat_preservesColimits_tensorRight
  CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.moduleCat_preservesColimits_tensorLeft
  CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.moduleCat_preservesColimits_tensorRight

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}
  (ρ₀ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]) (hρ₀ : Continuous ρ₀) (k : ℕ)
  [NeZero (ℓ ^ k)]

/-- The pairing `ℱ_{ρ₀,k} ⊗ ℱ_{ρ₀^∨,k} ⟶ ℱ_{ℤ/ℓᵏ}` of lisse sheaves on Mathlib's small étale
site attached to the dot product. -/
abbrev levelLisseTensorHom :=
  lisseEtaleSheafTensorHom B X x (ZMod (ℓ ^ k)) (levelDotPairing ρ₀ hρ₀ k)
    (levelDotPairing_equivariant ρ₀ hρ₀ k)

/-- **On the stalk at a geometric point, the pairing of the levels is perfect.** Along a path
from `s̄` to `x̄` the stalks are the level modules and the pairing is the dot product, which is
nondegenerate; the source and the dual of the second factor have `ℓ^{kr}` elements. -/
theorem bijective_levelLisseTensorHom_sheafFiber (s : GeometricPoint X.1) :
    Function.Bijective (TensorProduct.curry (Functor.LaxMonoidal.μ
      ((Scheme.pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{u + 1} (ZMod (ℓ ^ k)))) _ _ ≫
        ((Scheme.pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{u + 1} (ZMod (ℓ ^ k)))).map
          (levelLisseTensorHom B X x ρ₀ hρ₀ k)).hom) := by
  obtain ⟨t⟩ := nonempty_finiteEtaleFiberFunctorIso (X := X.1) (x := s) (x' := x)
  let P := levelModule.{u + 1, u + 1} ρ₀ hρ₀ k
  let Q := levelModule.{u + 1, u + 1} (contragredient ρ₀) (continuous_contragredient hρ₀) k
  let R := trivialContinuousModule (G := EtaleFundamentalGroup X.1 x) (ℓ ^ k)
  let φ := TensorProduct.curry (Functor.LaxMonoidal.μ
      ((Scheme.pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{u + 1} (ZMod (ℓ ^ k)))) _ _ ≫
        ((Scheme.pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{u + 1} (ZMod (ℓ ^ k)))).map
          (levelLisseTensorHom B X x ρ₀ hρ₀ k)).hom
  have hφ : ∀ z₁ z₂, lisseEtaleSheafStalkCounit B X x (ZMod (ℓ ^ k)) t R (φ z₁ z₂) =
      levelDotPairing ρ₀ hρ₀ k (lisseEtaleSheafStalkCounit B X x (ZMod (ℓ ^ k)) t P z₁)
        (lisseEtaleSheafStalkCounit B X x (ZMod (ℓ ^ k)) t Q z₂) :=
    lisseEtaleSheafStalkCounit_tensorHom B X x (ZMod (ℓ ^ k)) t (levelDotPairing ρ₀ hρ₀ k)
      (levelDotPairing_equivariant ρ₀ hρ₀ k)
  have hinj : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).2 fun z₁ hz ↦ ?_
    have key : ∀ b, levelDotPairing ρ₀ hρ₀ k
        (lisseEtaleSheafStalkCounit B X x (ZMod (ℓ ^ k)) t P z₁ -
          lisseEtaleSheafStalkCounit B X x (ZMod (ℓ ^ k)) t P 0) b = 0 := fun b ↦ by
      obtain ⟨z₂, rfl⟩ := (lisseEtaleSheafStalkCounit_bijective B X x (ZMod (ℓ ^ k)) t Q).2 b
      rw [map_sub, LinearMap.sub_apply, ← hφ, ← hφ, hz, map_zero, sub_self]
    exact (lisseEtaleSheafStalkCounit_bijective B X x (ZMod (ℓ ^ k)) t P).1
      (sub_eq_zero.1 (levelDotPairing_eq_zero_of_forall ρ₀ hρ₀ k _ key))
  let eP := (lisseEtaleSheafModuleFiberIso B X x (ZMod (ℓ ^ k)) t P).toLinearEquiv
  let eQ := (lisseEtaleSheafModuleFiberIso B X x (ZMod (ℓ ^ k)) t Q).toLinearEquiv
  let eR := (lisseEtaleSheafModuleFiberIso B X x (ZMod (ℓ ^ k)) t R).toLinearEquiv
  let fP : ULift.{u + 1} (Fin r → ZMod (ℓ ^ k)) ≃ₗ[ZMod (ℓ ^ k)] (Fin r → ZMod (ℓ ^ k)) :=
    ULift.moduleEquiv
  let fR : ULift.{u + 1} (ZMod (ℓ ^ k)) ≃ₗ[ZMod (ℓ ^ k)] ZMod (ℓ ^ k) := ULift.moduleEquiv
  let eH := ((eQ.trans fP).arrowCongr (eR.trans fR)).trans
    (LinearEquiv.piRing (ZMod (ℓ ^ k)) (ZMod (ℓ ^ k)) (Fin r) (ZMod (ℓ ^ k)))
  have : Finite (_ →ₗ[ZMod (ℓ ^ k)] _) := Finite.of_equiv _ eH.toEquiv.symm
  refine hinj.bijective_of_nat_card_le ?_
  rw [Nat.card_congr eH.toEquiv, Nat.card_congr (eP.trans fP).toEquiv]

/-- **The pairing of the levels** `ℱ_{ρ₀,k} ⊗ ℱ_{ρ₀^∨,k} ⟶ ℤ/ℓᵏ` on Mathlib's small étale site: the
pairing of lisse sheaves attached to the dot product, followed by the identification of the lisse
sheaf of `ℤ/ℓᵏ` with the trivial action with the constant sheaf. -/
def levelTensorHom :
    (lisseEtaleSheaf B X x (ZMod (ℓ ^ k))).obj (levelModule.{u + 1, u + 1} ρ₀ hρ₀ k) ⊗
        (lisseEtaleSheaf B X x (ZMod (ℓ ^ k))).obj
          (levelModule.{u + 1, u + 1} (contragredient ρ₀) (continuous_contragredient hρ₀) k) ⟶
      𝟙_ (EtaleModules.{u, 0} (ZMod (ℓ ^ k)) X.1) :=
  levelLisseTensorHom B X x ρ₀ hρ₀ k ≫
    (nonempty_lisseEtaleSheaf_trivialContinuousModule_iso B X x (ℓ ^ k)).some.hom

/-- **The pairing of the levels is perfect on the fibres at the universe lifts of the geometric
points**: the fibre at `Φ.ulift` is the fibre at `Φ`
(`Stacks.SheafDuality.ulift_μ_map_tensorDesc`), perfect by
`Stacks.EtaleCohomology.bijective_levelLisseTensorHom_sheafFiber`. -/
theorem bijective_levelTensorHom_ulift (s : GeometricPoint X.1) :
    Function.Bijective (TensorProduct.curry (Functor.LaxMonoidal.μ
      (((Scheme.pointSmallEtale s.hom).ulift.{u + 1}).sheafFiber
        (A := ModuleCat.{u + 1} (ZMod (ℓ ^ k)))) _ _ ≫
        (((Scheme.pointSmallEtale s.hom).ulift.{u + 1}).sheafFiber
          (A := ModuleCat.{u + 1} (ZMod (ℓ ^ k)))).map (levelTensorHom B X x ρ₀ hρ₀ k)).hom) := by
  let Φ := Scheme.pointSmallEtale s.hom
  let u' : (Φ.ulift.{u + 1}).sheafFiber (A := ModuleCat.{u + 1} (ZMod (ℓ ^ k))) ≅ Φ.sheafFiber :=
    Φ.sheafFiberUliftNatIso (ModuleCat.{u + 1} (ZMod (ℓ ^ k)))
  let c := (nonempty_lisseEtaleSheaf_trivialContinuousModule_iso B X x (ℓ ^ k)).some
  have hU : (Functor.LaxMonoidal.μ (Φ.ulift.{u + 1}).sheafFiber _ _ ≫
      (Φ.ulift.{u + 1}).sheafFiber.map (levelLisseTensorHom B X x ρ₀ hρ₀ k)) ≫ (u'.app _).hom =
      ((u'.app _).hom ⊗ₘ (u'.app _).hom) ≫ Functor.LaxMonoidal.μ Φ.sheafFiber _ _ ≫
        Φ.sheafFiber.map (levelLisseTensorHom B X x ρ₀ hρ₀ k) :=
    Stacks.SheafDuality.ulift_μ_map_tensorDesc Φ
      (lisseEtaleSheafBilinear B X x (ZMod (ℓ ^ k)) (levelDotPairing ρ₀ hρ₀ k)
        (levelDotPairing_equivariant ρ₀ hρ₀ k))
      (fun f a b ↦ lisseEtaleSheafBilinear_naturality B X x (ZMod (ℓ ^ k))
        (levelDotPairing ρ₀ hρ₀ k) (levelDotPairing_equivariant ρ₀ hρ₀ k) f a b)
  have key : Functor.LaxMonoidal.μ (Φ.ulift.{u + 1}).sheafFiber _ _ ≫
      (Φ.ulift.{u + 1}).sheafFiber.map (levelTensorHom B X x ρ₀ hρ₀ k) =
      ((u'.app _).hom ⊗ₘ (u'.app _).hom) ≫
        (Functor.LaxMonoidal.μ Φ.sheafFiber _ _ ≫
          Φ.sheafFiber.map (levelLisseTensorHom B X x ρ₀ hρ₀ k)) ≫
          ((u'.app _).symm ≪≫ (Φ.ulift.{u + 1}).sheafFiber.mapIso c).hom := by
    have h₁ : (Φ.ulift.{u + 1}).sheafFiber.map (levelTensorHom B X x ρ₀ hρ₀ k) =
        (Φ.ulift.{u + 1}).sheafFiber.map (levelLisseTensorHom B X x ρ₀ hρ₀ k) ≫
          (Φ.ulift.{u + 1}).sheafFiber.map c.hom :=
      (Φ.ulift.{u + 1}).sheafFiber.map_comp _ _
    have h₂ : Functor.LaxMonoidal.μ (Φ.ulift.{u + 1}).sheafFiber _ _ ≫
        (Φ.ulift.{u + 1}).sheafFiber.map (levelLisseTensorHom B X x ρ₀ hρ₀ k) =
        (((u'.app _).hom ⊗ₘ (u'.app _).hom) ≫ Functor.LaxMonoidal.μ Φ.sheafFiber _ _ ≫
          Φ.sheafFiber.map (levelLisseTensorHom B X x ρ₀ hρ₀ k)) ≫ (u'.app _).inv :=
      (Iso.eq_comp_inv _).2 hU
    exact (congrArg (_ ≫ ·) h₁).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) h₂).trans ((Category.assoc _ _ _).trans (Category.assoc _ _ _))))
  show Function.Bijective (TensorProduct.curry (Functor.LaxMonoidal.μ
    (Φ.ulift.{u + 1}).sheafFiber _ _ ≫
      (Φ.ulift.{u + 1}).sheafFiber.map (levelTensorHom B X x ρ₀ hρ₀ k)).hom)
  rw [key]
  exact Stacks.SheafDuality.bijective_curry_tensorHom_comp _ (u'.app _) (u'.app _) _
    (bijective_levelLisseTensorHom_sheafFiber B X x ρ₀ hρ₀ k s)

end Pairing

/-! ### On the identity compactification, and the exact pairing -/

section Proper

attribute [local instance] etaleModules_AB5OfSize etaleModules_preservesFilteredColimits_forget
  etaleModuleInverseImageSheafPullbackMonoidal etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

/-- The morphisms of presheaves of `Λ`-modules on the small étale site of `S` inverted by
sheafification form a monoidal class. -/
local instance (Λ : Type) [CommRing Λ] (S : Scheme.{u}) :
    (S.smallEtaleTopology.W (A := ModuleCat.{u + 1} Λ)).IsMonoidal :=
  isMonoidal_W_etaleModules (Λ := Λ) S

attribute [local instance] AlgebraicGeometry.moduleCat_preservesColimits_tensorLeft
  AlgebraicGeometry.moduleCat_preservesColimits_tensorRight
  CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.moduleCat_preservesColimits_tensorLeft
  CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.moduleCat_preservesColimits_tensorRight

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}
  (ρ₀ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]) (hρ₀ : Continuous ρ₀)
  {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k)) [IsProper f] (n : ℕ)

/-- Every power of the prime `ℓ` is nonzero. -/
local instance neZero_prime_pow_representationLevelPairing (n : ℕ) : NeZero (ℓ ^ n) :=
  ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩

/-- **The pairing of the levels on the identity compactification**: `j_!` along the identity is the
identity (`Stacks.EtaleCohomology.etaleModuleExtensionByZeroIdIso`). -/
def representationLevelPairingOfProper :
    (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (CompactificationOf.ofProper f).immersion).obj
        ((lisseEtaleSheaf B X x (ZMod (ℓ ^ (n + 1)))).obj
          (levelModule.{u + 1, u + 1} ρ₀ hρ₀ (n + 1))) ⊗
      (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (CompactificationOf.ofProper f).immersion).obj
        ((lisseEtaleSheaf B X x (ZMod (ℓ ^ (n + 1)))).obj
          (levelModule.{u + 1, u + 1} (contragredient ρ₀) (continuous_contragredient hρ₀)
            (n + 1))) ⟶
      𝟙_ (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1))) X.1) :=
  ((etaleModuleExtensionByZeroIdIso (ZMod (ℓ ^ (n + 1))) X.1).hom.app _ ⊗ₘ
    (etaleModuleExtensionByZeroIdIso (ZMod (ℓ ^ (n + 1))) X.1).hom.app _) ≫
    levelTensorHom B X x ρ₀ hρ₀ (n + 1)

/-- The pairing of the levels on the identity compactification is perfect on the fibres at the
universe lifts of the geometric points. -/
theorem bijective_representationLevelPairing_ulift (s : GeometricPoint X.1) :
    Function.Bijective (TensorProduct.curry (Functor.LaxMonoidal.μ
      (((Scheme.pointSmallEtale s.hom).ulift.{u + 1}).sheafFiber
        (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))) _ _ ≫
        (((Scheme.pointSmallEtale s.hom).ulift.{u + 1}).sheafFiber
          (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).map
          (representationLevelPairingOfProper B X x ρ₀ hρ₀ f n)).hom) := by
  let Ψ := ((Scheme.pointSmallEtale s.hom).ulift.{u + 1}).sheafFiber
    (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
  let e := etaleModuleExtensionByZeroIdIso (ZMod (ℓ ^ (n + 1))) X.1
  have key :
      Functor.LaxMonoidal.μ Ψ _ _ ≫ Ψ.map (representationLevelPairingOfProper B X x ρ₀ hρ₀ f n) =
      ((Ψ.mapIso (e.app _)).hom ⊗ₘ (Ψ.mapIso (e.app _)).hom) ≫
        (Functor.LaxMonoidal.μ Ψ _ _ ≫ Ψ.map (levelTensorHom B X x ρ₀ hρ₀ (n + 1))) ≫
          (Iso.refl _).hom :=
    (congrArg (_ ≫ ·) (Ψ.map_comp _ _)).trans
      ((Functor.LaxMonoidal.μ_natural_assoc Ψ _ _ _).symm.trans (congrArg (_ ≫ ·)
        (Category.comp_id _).symm))
  show Function.Bijective (TensorProduct.curry (Functor.LaxMonoidal.μ Ψ _ _ ≫
    Ψ.map (representationLevelPairingOfProper B X x ρ₀ hρ₀ f n)).hom)
  rw [key]
  exact Stacks.SheafDuality.bijective_curry_tensorHom_comp _ _ _ _
    (bijective_levelTensorHom_ulift B X x ρ₀ hρ₀ (n + 1) s)

/-- The geometric points of `X`, as points of its small étale site relative to the coefficient
universe. -/
abbrev geometricPointsAt :
    ObjectProperty (GrothendieckTopology.Point.{u + 1} X.1.smallEtaleTopology) :=
  ObjectProperty.ofObj
    (fun y : X.1 ↦ (Scheme.pointSmallEtale (geometricPointAt X.1 y).hom).ulift.{u + 1})

omit [ConnectedSpace X.1] in
/-- The geometric points of `X` form a conservative family of points of its small étale site. -/
theorem isConservativeFamilyOfPoints_geometricPointsAt :
    (geometricPointsAt B X).IsConservativeFamilyOfPoints :=
  Scheme.isConservative_pointSmallEtale_ulift.{0, u} (fun y : X.1 ↦ (geometricPointAt X.1 y).hom)
    (Set.eq_univ_of_forall fun y ↦ Set.mem_iUnion.2
      ⟨y, default, geometricPointAt_liesOver X.1 y⟩)

variable [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [IsNoetherian X.1]

/-- **The pairing of the levels is the evaluation of an exact pairing**
(`Stacks.SheafDuality.exactPairingOfPerfect` at the geometric points). -/
@[instance_reducible]
def representationLevelExactPairing :
    ExactPairing ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (CompactificationOf.ofProper f).immersion).obj
        ((lisseEtaleSheaf B X x (ZMod (ℓ ^ (n + 1)))).obj
          (levelModule.{u + 1, u + 1} (contragredient ρ₀) (continuous_contragredient hρ₀) (n + 1))))
      ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (CompactificationOf.ofProper f).immersion).obj
        ((lisseEtaleSheaf B X x (ZMod (ℓ ^ (n + 1)))).obj
          (levelModule.{u + 1, u + 1} ρ₀ hρ₀ (n + 1)))) := by
  haveI : ∀ V : X.1.Etale,
      (X.1.smallEtaleTopology.over V).WEqualsLocallyBijective
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) :=
    fun V ↦ Stacks.ConstantSheaf.wEqualsLocallyBijective_moduleCat.{u, u + 1, u + 1, 0} _ _
  refine Stacks.SheafDuality.exactPairingOfPerfect
    (isConservativeFamilyOfPoints_geometricPointsAt B X)
    (representationLevelPairingOfProper B X x ρ₀ hρ₀ f n) ?_ ?_ ?_
  · exact Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_congr _ (ZMod (ℓ ^ (n + 1)))
      ((etaleModuleExtensionByZeroIdIso (ZMod (ℓ ^ (n + 1))) X.1).app _).symm
      (isFiniteTypeLocallyConstant_etaleLevel_representationLAdicSheaf B X x _ _ n)
  · rintro ⟨_, ⟨y⟩⟩
    exact flat_sheafFiber_ulift_of_flat _ _ _ (flat_sheafFiber_extensionByZero (ZMod (ℓ ^ (n + 1)))
      (CompactificationOf.ofProper f).immersion (geometricPointAt X.1 y).hom
      ((lisseEtaleSheaf B X x (ZMod (ℓ ^ (n + 1)))).obj
        (levelModule.{u + 1, u + 1} (contragredient ρ₀) (continuous_contragredient hρ₀) (n + 1)))
      fun t _ ↦ flat_sheafFiber_of_powExact _
        (powExact_etaleLevel_representationLAdicSheaf B X x (contragredient ρ₀)
          (continuous_contragredient hρ₀) n) t)
  · rintro ⟨_, ⟨y⟩⟩
    convert Function.Bijective.comp (LinearEquiv.congrRight (Stacks.SheafDuality.unitEquiv
      ((Scheme.pointSmallEtale (geometricPointAt X.1 y).hom).ulift.{u + 1}).sheafFiber)).bijective
        (bijective_representationLevelPairing_ulift B X x ρ₀ hρ₀ f n (geometricPointAt X.1 y))
      using 1
    funext b
    ext g
    rfl

/-- **The pulled back pairing of the levels is perfect on all fibres**: for `g : T ⟶ X` and a point
`s` of `T` with separably closed residue field, the inverse image along `g` of the pairing of the
levels induces a perfect pairing on the fibres at `s`. The pairing is the evaluation of an exact
pairing on `X` (`Stacks.EtaleCohomology.representationLevelExactPairing`), carried by the monoidal
functors `g⁻¹` and `(-)_s` to an exact pairing of modules
(`CategoryTheory.ExactPairing.map`), whose evaluation is perfect
(`Stacks.SheafDuality.bijective_curry_evaluation_of_exactPairing`); the identifications of the
units only change the target by an isomorphism. -/
theorem bijective_inverseImage_representationLevelPairingOfProper {T : Scheme.{u}}
    (g : T ⟶ X.1) (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ T) :
    Function.Bijective (TensorProduct.curry (Functor.LaxMonoidal.μ
      (((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
        (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))))
      ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1))) g).obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (CompactificationOf.ofProper f).immersion).obj
          ((lisseEtaleSheaf B X x (ZMod (ℓ ^ (n + 1)))).obj
            (levelModule.{u + 1, u + 1} ρ₀ hρ₀ (n + 1)))))
      ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1))) g).obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (CompactificationOf.ofProper f).immersion).obj
          ((lisseEtaleSheaf B X x (ZMod (ℓ ^ (n + 1)))).obj
            (levelModule.{u + 1, u + 1} (contragredient ρ₀) (continuous_contragredient hρ₀)
              (n + 1))))) ≫
      (((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
        (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).map
        (inverseImageConstantPairing g (ℓ ^ (n + 1))
          (representationLevelPairingOfProper B X x ρ₀ hρ₀ f n))).hom) := by
  let K := (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
    (CompactificationOf.ofProper f).immersion).obj
      ((lisseEtaleSheaf B X x (ZMod (ℓ ^ (n + 1)))).obj (levelModule.{u + 1, u + 1} ρ₀ hρ₀ (n + 1)))
  let K' := (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
    (CompactificationOf.ofProper f).immersion).obj
      ((lisseEtaleSheaf B X x (ZMod (ℓ ^ (n + 1)))).obj
        (levelModule.{u + 1, u + 1} (contragredient ρ₀) (continuous_contragredient hρ₀) (n + 1)))
  let Ψ := ((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
    (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
  let G := etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1))) g
  let p : ExactPairing K' K := representationLevelExactPairing B X x ρ₀ hρ₀ f n
  let p' := @ExactPairing.map _ _ _ _ _ _ G _ K' K p
  let p'' := ExactPairing.map Ψ (G.obj K') (G.obj K)
  let c := inverseImageEtaleModuleConstantSheafIso.{u, 0} (ZMod (ℓ ^ (n + 1)))
    (ModuleCat.of (ZMod (ℓ ^ (n + 1))) (ULift.{u + 1} (ZMod (ℓ ^ (n + 1))))) g
  let iT := Functor.Monoidal.εIso Ψ ≪≫ Ψ.mapIso (Functor.Monoidal.εIso G ≪≫ c)
  have key : Functor.LaxMonoidal.μ Ψ (G.obj K) (G.obj K') ≫
      Ψ.map (inverseImageConstantPairing g (ℓ ^ (n + 1))
        (representationLevelPairingOfProper B X x ρ₀ hρ₀ f n)) =
      ε_ (Ψ.obj (G.obj K')) (Ψ.obj (G.obj K)) ≫ iT.hom := by
    show Functor.LaxMonoidal.μ Ψ (G.obj K) (G.obj K') ≫
        Ψ.map (Functor.LaxMonoidal.μ G K K' ≫
          G.map (representationLevelPairingOfProper B X x ρ₀ hρ₀ f n) ≫ c.hom) =
      (Functor.LaxMonoidal.μ Ψ (G.obj K) (G.obj K') ≫ Ψ.map (Functor.LaxMonoidal.μ G K K' ≫
        G.map (representationLevelPairingOfProper B X x ρ₀ hρ₀ f n) ≫
          Functor.OplaxMonoidal.η G) ≫ Functor.OplaxMonoidal.η Ψ) ≫
        (Functor.LaxMonoidal.ε Ψ ≫ Ψ.map (Functor.LaxMonoidal.ε G ≫ c.hom))
    simp only [Category.assoc, Functor.Monoidal.η_ε_assoc, ← Functor.map_comp]
    exact congrArg (fun t ↦ Functor.LaxMonoidal.μ Ψ _ _ ≫ Ψ.map (Functor.LaxMonoidal.μ G K K' ≫
        G.map (representationLevelPairingOfProper B X x ρ₀ hρ₀ f n) ≫ t))
      (Functor.Monoidal.η_ε_assoc G c.hom).symm
  rw [key]
  exact Stacks.SheafDuality.bijective_curry_comp_iso _ iT
    (Stacks.SheafDuality.bijective_curry_evaluation_of_exactPairing (Ψ.obj (G.obj K))
      (Ψ.obj (G.obj K')))

end Proper

/-! ### The inputs of purity -/

section Inputs

attribute [local instance] HasDerivedCategory.standard etaleModuleInverseImageSheafPullbackMonoidal
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits

/-- The morphisms of presheaves of `Λ`-modules on the small étale site of `S` inverted by
sheafification form a monoidal class. -/
local instance (Λ : Type) [CommRing Λ] (S : Scheme.{u}) :
    (S.smallEtaleTopology.W (A := ModuleCat.{u + 1} Λ)).IsMonoidal :=
  isMonoidal_W_etaleModules (Λ := Λ) S

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

omit [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- **The pairing of the levels of `ℱ_ρ` and `ℱ_{ρ₀^∨}`, perfect on the geometric fibres over
`X_k̄`** (`Stacks.EtaleCohomology.LAdicSheaf.RepresentationLevelPairingInput`): the pairing of the
levels on the identity compactification
(`Stacks.EtaleCohomology.representationLevelPairingOfProper`), for the integral model of `ρ`. -/
theorem LAdicSheaf.representationLevelPairingInput :
    LAdicSheaf.RepresentationLevelPairingInput B ℓ := by
  intro k _ kbar _ _ X _ _ f _ x r ρ hρ
  have := compactSpace_etaleFundamentalGroup X.1 x
  exact ⟨fun n ↦ representationLevelPairingOfProper B X x (integralModel ρ hρ)
      (continuous_integralModel ρ hρ) f n,
    fun n Ω _ _ s ↦ bijective_inverseImage_representationLevelPairingOfProper B X x
      (integralModel ρ hρ) (continuous_integralModel ρ hρ) f n
      (fieldBaseChangeProj (Over.mk f) kbar) Ω s⟩

/-- **The dual coefficients of `ℱ_ρ`**
(`Stacks.EtaleCohomology.LAdicSheaf.RepresentationDualPairingInput`, an input of the purity half
of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)), proved: `F' = ℱ_{ρ₀^∨}` with the pairing
of the levels. -/
theorem LAdicSheaf.representationDualPairingInput :
    LAdicSheaf.RepresentationDualPairingInput B ℓ :=
  LAdicSheaf.representationDualPairingInput_of_levelPairingInput B ℓ
    (LAdicSheaf.representationLevelPairingInput B ℓ)

end Inputs

end Stacks.EtaleCohomology

end
