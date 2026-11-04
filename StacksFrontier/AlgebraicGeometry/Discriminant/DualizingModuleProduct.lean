module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Discriminant.CommonRefinement
public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingModuleComparison
public import StacksFrontier.AlgebraicGeometry.Discriminant.ProductFactorizationEquiv

/-!
# The relative dualizing module of a product of quasi-finite algebras

Let `A` be a Noetherian ring and let `B` and `C` be quasi-finite Noetherian `A`-algebras. The
relative dualizing module of `A → B × C` is the product of the relative dualizing modules of
`A → B` and `A → C`, where the product ring acts on the two factors through its two projections.

The construction combines two steps. A finite-open factorization of the product restricts to one
of each factor with the same intermediate algebra, and there the dualizing module splits by
`Stacks.Discriminant.productFactorizationEquiv`; the canonical comparisons of
`Stacks.Discriminant.dualizingModuleEquiv` then move the two halves to arbitrary chosen
factorizations of `B` and of `C`. The resulting equivalence is pinned down on pure tensors when
the middle algebra is the product of the two chosen middle algebras, and is independent of all
three choices.

## Main definitions

* `Stacks.Discriminant.dualizingModuleProdEquiv` is the product equivalence.

## Main results

* `Stacks.Discriminant.dualizingModuleProdEquiv_tmul`: for a product factorization the
  equivalence restricts a functional to each summand and projects the coefficient.
* `Stacks.Discriminant.dualizingModuleProdEquiv_naturality`: the equivalence commutes with the
  canonical comparisons for any change of the three factorizations.
* `Stacks.Discriminant.dualizingModule_product_ext`: two additive maps out of the dualizing
  module of a product agree as soon as they agree on the pure tensors supported on each factor.

## Implementation notes

The construction of a dualizing module retains a choice of finite-open factorization, so the
equivalence is stated for choices of factorizations of the two factors and of their product. The
naturality equation is what makes the pure-tensor formula determine the equivalence
independently of those choices.

The intermediate algebra of `Stacks.Discriminant.firstFactorization F` is that of `F` carrying a
different algebra structure on the target, so identifying the two costs a definitional unfolding
inside instance arguments. A `rw`, an `ext` or a `change` will not perform that unfolding, because
it matches only up to reducible transparency; the proofs below therefore compose the relevant
equations with `Eq.trans` and `congrArg`, which are elaborated against the goal and so do see
through the two algebra structures.

## References

* [Stacks Project, Tag 0BT5](https://stacks.math.columbia.edu/tag/0BT5)
-/

@[expose] public section

universe u v w x y z x' y' z'

namespace Stacks.Discriminant

open scoped TensorProduct

/-- A pure tensor whose target factor vanishes is zero. This complements
`Stacks.Discriminant.dualizingModule.zero_tmul` on the other factor, and lets a rewrite stay
inside the `Stacks.Discriminant.dualizingModule.tmul` interface instead of unfolding the
dualizing module to a tensor product. -/
theorem dualizingModule.tmul_zero {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (f : Module.Dual A F.middle) : dualizingModule.tmul F f 0 = 0 := by
  let := algebraDualModule A F.middle
  show f ⊗ₜ[F.middle] (0 : B) = 0
  exact TensorProduct.tmul_zero (R := F.middle) (N := B) f

/-- The canonical comparison between two finite-open factorizations kills a pure tensor whose
target factor vanishes. -/
theorem dualizingModuleEquiv_tmul_zero {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (G : FiniteOpenFactorization.{u, v, x} A B)
    (f : Module.Dual A F.middle) :
    dualizingModuleEquiv F G (dualizingModule.tmul F f 0) = 0 :=
  (congrArg (fun z : dualizingModule F => dualizingModuleEquiv F G z)
    (dualizingModule.tmul_zero F f)).trans (map_zero (dualizingModuleEquiv F G))

/-- **Stacks Project, Tag 0BT5.** The dualizing module of a product of quasi-finite
Noetherian algebras is canonically the product of their dualizing modules. -/
@[stacks 0BT5]
noncomputable def dualizingModuleProdEquiv
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    [Algebra.QuasiFinite A B] [Algebra.QuasiFinite A C]
    (F : FiniteOpenFactorization.{u, max v w, x} A (B × C))
    (FB : FiniteOpenFactorization.{u, v, y} A B)
    (FC : FiniteOpenFactorization.{u, w, z} A C) :
    letI : Module (B × C) (dualizingModule FB) :=
      Module.compHom _ (RingHom.fst B C)
    letI : Module (B × C) (dualizingModule FC) :=
      Module.compHom _ (RingHom.snd B C)
    dualizingModule F ≃ₗ[B × C] (dualizingModule FB × dualizingModule FC) := by
  let FB₀ := firstFactorization F
  let FC₀ := secondFactorization F
  letI : Module (B × C) (dualizingModule FB₀) :=
    Module.compHom _ (RingHom.fst B C)
  letI : Module (B × C) (dualizingModule FC₀) :=
    Module.compHom _ (RingHom.snd B C)
  letI : Module (B × C) (dualizingModule FB) :=
    Module.compHom _ (RingHom.fst B C)
  letI : Module (B × C) (dualizingModule FC) :=
    Module.compHom _ (RingHom.snd B C)
  let eB := dualizingModuleEquiv FB₀ FB
  let eC := dualizingModuleEquiv FC₀ FC
  exact (productFactorizationEquiv F).trans
    ((linearEquivCompHom (RingHom.fst B C) eB).prodCongr
      (linearEquivCompHom (RingHom.snd B C) eC))

/-- The product equivalence is the product factorization equivalence followed by the canonical
comparisons on the two factors. -/
theorem dualizingModuleProdEquiv_apply
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    [Algebra.QuasiFinite A B] [Algebra.QuasiFinite A C]
    (F : FiniteOpenFactorization.{u, max v w, x} A (B × C))
    (FB : FiniteOpenFactorization.{u, v, y} A B)
    (FC : FiniteOpenFactorization.{u, w, z} A C) (ω : dualizingModule F) :
    dualizingModuleProdEquiv F FB FC ω =
      (dualizingModuleEquiv (firstFactorization F) FB
        (productFactorizationEquiv F ω).1,
       dualizingModuleEquiv (secondFactorization F) FC
        (productFactorizationEquiv F ω).2) := by
  rfl

/-- For a product factorization whose middle algebra is the product of the chosen middle
algebras, the map to the first chosen dualizing module: restrict the functional to the first
summand and keep the coefficient. -/
noncomputable def dualizingModuleProductFirstRestrict
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    (F : FiniteOpenFactorization.{u, max v w, x} A (B × C))
    (FB : FiniteOpenFactorization.{u, v, y} A B)
    (FC : FiniteOpenFactorization.{u, w, z} A C)
    (e : (FB.middle × FC.middle) ≃ₐ[A] F.middle)
    (hcompat : ∀ p : FB.middle × FC.middle,
      algebraMap F.middle (B × C) (e p) =
        (algebraMap FB.middle B p.1, algebraMap FC.middle C p.2)) :
    dualizingModule (firstFactorization F) →+ dualizingModule FB := by
  let F₁ := firstFactorization F
  letI : Algebra F.middle B := F₁.algebraTarget
  let i : FB.middle →ₗ[A] F.middle :=
    e.toLinearEquiv.toLinearMap.comp (LinearMap.inl A FB.middle FC.middle)
  let p : F.middle →ₐ[A] FB.middle :=
    (AlgHom.fst A FB.middle FC.middle).comp e.symm.toAlgHom
  let σ : F.middle →+* B := algebraMap F.middle B
  letI : Module F₁.middle (Module.Dual A F₁.middle) :=
    algebraDualModule A F₁.middle
  letI : Module F.middle (Module.Dual A F.middle) :=
    algebraDualModule A F.middle
  letI : Module FB.middle (Module.Dual A FB.middle) :=
    algebraDualModule A FB.middle
  have hσ (r : F.middle) : σ r = algebraMap FB.middle B (p r) := by
    calc
      σ r = (algebraMap F.middle (B × C) r).1 := rfl
      _ = algebraMap FB.middle B (p r) := by
        simpa [p, RingHom.algebraMap_toAlgebra] using congrArg Prod.fst (hcompat (e.symm r))
  letI : Module F.middle (dualizingModule FB) := Module.compHom _ σ
  let ψmap : Module.Dual A F.middle →ₛₗ[σ]
      B →ₛₗ[σ] dualizingModule FB := {
    toFun := fun φ => {
      toFun := fun b => dualizingModule.tmul FB (φ.comp i) b
      map_add' := fun _ _ => TensorProduct.tmul_add _ _ _
      map_smul' := by
        intro r b
        change dualizingModule.tmul FB (φ.comp i) (σ r • b) =
          σ r • dualizingModule.tmul FB (φ.comp i) b
        exact (dualizingModule.smul_tmul FB (σ r) b (φ.comp i)).symm
    }
    map_add' := by
      intro φ ψ
      ext b
      change dualizingModule.tmul FB ((φ + ψ).comp i) b = _
      have hfun : (φ + ψ).comp i = φ.comp i + ψ.comp i := by
        ext x
        rfl
      rw [hfun]
      exact TensorProduct.add_tmul _ _ _
    map_smul' := by
      intro r φ
      have hfun : (r • φ).comp i = p r • (φ.comp i) := by
        ext x
        change φ (r * i x) = φ (i (p r * x))
        congr 1
        apply e.symm.injective
        change e.symm (r * e (x, 0)) = e.symm (e (p r * x, 0))
        rw [map_mul, e.symm_apply_apply, e.symm_apply_apply]
        change e.symm r * (x, 0) = (p r * x, 0)
        apply Prod.ext
        · rfl
        · simp
      ext b
      calc
        dualizingModule.tmul FB ((r • φ).comp i) b =
            dualizingModule.tmul FB (p r • (φ.comp i)) b := by
              rw [hfun]
        _ = dualizingModule.tmul FB (φ.comp i) (p r • b) := by
              change ((p r) • (φ.comp i)) ⊗ₜ[FB.middle] b =
                (φ.comp i) ⊗ₜ[FB.middle] (p r • b)
              rw [TensorProduct.smul_tmul]
        _ = dualizingModule.tmul FB (φ.comp i)
            (algebraMap FB.middle B (p r) * b) := by
              rw [Algebra.smul_def]
        _ = σ r • dualizingModule.tmul FB (φ.comp i) b := by
              rw [← hσ r]
              simp [dualizingModule.smul_tmul]
  }
  let L := TensorProduct.lift ψmap
  exact L.toAddMonoidHom

/-- The first-factor restriction on a pure tensor. -/
theorem dualizingModuleProductFirstRestrict_tmul
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    (F : FiniteOpenFactorization.{u, max v w, x} A (B × C))
    (FB : FiniteOpenFactorization.{u, v, y} A B)
    (FC : FiniteOpenFactorization.{u, w, z} A C)
    (e : (FB.middle × FC.middle) ≃ₐ[A] F.middle)
    (hcompat : ∀ p : FB.middle × FC.middle,
      algebraMap F.middle (B × C) (e p) =
        (algebraMap FB.middle B p.1, algebraMap FC.middle C p.2))
    (φ : Module.Dual A F.middle) (b : B) :
    dualizingModuleProductFirstRestrict F FB FC e hcompat
      (dualizingModule.tmul (firstFactorization F)
        φ b) =
      dualizingModule.tmul FB
        (φ.comp (e.toLinearMap.comp (LinearMap.inl A FB.middle FC.middle))) b := by
  let := algebraDualModule A F.middle
  let : Algebra F.middle B := (firstFactorization F).algebraTarget
  simp only [dualizingModuleProductFirstRestrict, dualizingModule.tmul]
  rfl

/-- For a product factorization whose middle algebra is the product of the chosen middle
algebras, the map to the second chosen dualizing module: restrict the functional to the second
summand and keep the coefficient. -/
noncomputable def dualizingModuleProductSecondRestrict
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    (F : FiniteOpenFactorization.{u, max v w, x} A (B × C))
    (FB : FiniteOpenFactorization.{u, v, y} A B)
    (FC : FiniteOpenFactorization.{u, w, z} A C)
    (e : (FB.middle × FC.middle) ≃ₐ[A] F.middle)
    (hcompat : ∀ p : FB.middle × FC.middle,
      algebraMap F.middle (B × C) (e p) =
        (algebraMap FB.middle B p.1, algebraMap FC.middle C p.2)) :
    dualizingModule (secondFactorization F) →+ dualizingModule FC := by
  let F₁ := secondFactorization F
  letI : Algebra F.middle C := F₁.algebraTarget
  let i : FC.middle →ₗ[A] F.middle :=
    e.toLinearEquiv.toLinearMap.comp (LinearMap.inr A FB.middle FC.middle)
  let p : F.middle →ₐ[A] FC.middle :=
    (AlgHom.snd A FB.middle FC.middle).comp e.symm.toAlgHom
  let σ : F.middle →+* C := algebraMap F.middle C
  letI : Module F₁.middle (Module.Dual A F₁.middle) :=
    algebraDualModule A F₁.middle
  letI : Module F.middle (Module.Dual A F.middle) :=
    algebraDualModule A F.middle
  letI : Module FC.middle (Module.Dual A FC.middle) :=
    algebraDualModule A FC.middle
  have hσ (r : F.middle) : σ r = algebraMap FC.middle C (p r) := by
    calc
      σ r = (algebraMap F.middle (B × C) r).2 := rfl
      _ = algebraMap FC.middle C (p r) := by
        simpa [p, RingHom.algebraMap_toAlgebra] using congrArg Prod.snd (hcompat (e.symm r))
  letI : Module F.middle (dualizingModule FC) := Module.compHom _ σ
  let ψmap : Module.Dual A F.middle →ₛₗ[σ]
      C →ₛₗ[σ] dualizingModule FC := {
    toFun := fun φ => {
      toFun := fun b => dualizingModule.tmul FC (φ.comp i) b
      map_add' := fun _ _ => TensorProduct.tmul_add _ _ _
      map_smul' := by
        intro r b
        change dualizingModule.tmul FC (φ.comp i) (σ r • b) =
          σ r • dualizingModule.tmul FC (φ.comp i) b
        exact (dualizingModule.smul_tmul FC (σ r) b (φ.comp i)).symm
    }
    map_add' := by
      intro φ ψ
      ext b
      change dualizingModule.tmul FC ((φ + ψ).comp i) b = _
      have hfun : (φ + ψ).comp i = φ.comp i + ψ.comp i := by
        ext x
        rfl
      rw [hfun]
      exact TensorProduct.add_tmul _ _ _
    map_smul' := by
      intro r φ
      have hfun : (r • φ).comp i = p r • (φ.comp i) := by
        ext x
        change φ (r * i x) = φ (i (p r * x))
        congr 1
        apply e.symm.injective
        change e.symm (r * e (0, x)) = e.symm (e (0, p r * x))
        rw [map_mul, e.symm_apply_apply, e.symm_apply_apply]
        change e.symm r * (0, x) = (0, p r * x)
        apply Prod.ext
        · simp
        · rfl
      ext b
      calc
        dualizingModule.tmul FC ((r • φ).comp i) b =
            dualizingModule.tmul FC (p r • (φ.comp i)) b := by
              rw [hfun]
        _ = dualizingModule.tmul FC (φ.comp i) (p r • b) := by
              change ((p r) • (φ.comp i)) ⊗ₜ[FC.middle] b =
                (φ.comp i) ⊗ₜ[FC.middle] (p r • b)
              rw [TensorProduct.smul_tmul]
        _ = dualizingModule.tmul FC (φ.comp i)
            (algebraMap FC.middle C (p r) * b) := by
              rw [Algebra.smul_def]
        _ = σ r • dualizingModule.tmul FC (φ.comp i) b := by
              rw [← hσ r]
              simp [dualizingModule.smul_tmul]
  }
  let L := TensorProduct.lift ψmap
  exact L.toAddMonoidHom

/-- The second-factor restriction on a pure tensor. -/
theorem dualizingModuleProductSecondRestrict_tmul
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    (F : FiniteOpenFactorization.{u, max v w, x} A (B × C))
    (FB : FiniteOpenFactorization.{u, v, y} A B)
    (FC : FiniteOpenFactorization.{u, w, z} A C)
    (e : (FB.middle × FC.middle) ≃ₐ[A] F.middle)
    (hcompat : ∀ p : FB.middle × FC.middle,
      algebraMap F.middle (B × C) (e p) =
        (algebraMap FB.middle B p.1, algebraMap FC.middle C p.2))
    (φ : Module.Dual A F.middle) (b : C) :
    dualizingModuleProductSecondRestrict F FB FC e hcompat
      (dualizingModule.tmul (secondFactorization F)
        φ b) =
      dualizingModule.tmul FC
        (φ.comp (e.toLinearMap.comp (LinearMap.inr A FB.middle FC.middle))) b := by
  let := algebraDualModule A F.middle
  let : Algebra F.middle C := (secondFactorization F).algebraTarget
  simp only [dualizingModuleProductSecondRestrict, dualizingModule.tmul]
  rfl

/-- Two additive maps out of a relative dualizing module agree as soon as they agree on pure
tensors. -/
theorem dualizingModule_addMonoidHom_ext_tmul
    {A : Type u} {B : Type v} {N : Type x}
    [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    [AddCommGroup N]
    (f g : dualizingModule F →+ N)
    (h : ∀ φ b, f (dualizingModule.tmul F φ b) =
      g (dualizingModule.tmul F φ b)) : f = g := by
  refine AddMonoidHom.ext fun z => ?_
  show f z = g z
  induction z using TensorProduct.induction_on with
  | zero => exact f.map_zero.trans g.map_zero.symm
  | tmul φ b => exact h φ b
  | add x y hx hy =>
      calc
        f (x + y) = f x + f y := f.map_add x y
        _ = g x + g y := congrArg₂ (· + ·) hx hy
        _ = g (x + y) := (g.map_add x y).symm

/-- Two additive maps out of a relative dualizing module agree as soon as they agree on the
pure tensors whose functional is restricted from a common refinement embedded in the target:
such tensors already generate, because the comparison with the refinement is surjective. -/
theorem dualizingModule_addMonoidHom_ext_common
    {A : Type u} {B : Type v} {N : Type x}
    [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (H : FiniteOpenFactorization.{u, v, y} A B)
    (hH : Function.Injective (algebraMap H.middle B))
    (rF : F.middle →ₐ[A] H.middle)
    (hF : ∀ c : F.middle,
      algebraMap H.middle B (rF c) = algebraMap F.middle B c)
    [AddCommGroup N]
    (f g : dualizingModule F →+ N)
    (h : ∀ (φ : Module.Dual A H.middle) (b : B),
      f (dualizingModule.tmul F (φ.comp rF.toLinearMap) b) =
      g (dualizingModule.tmul F (φ.comp rF.toLinearMap) b)) : f = g := by
  let e := dualizingModuleEquiv H F
  have heq (φ : Module.Dual A H.middle) (b : B) :
      e (dualizingModule.tmul H φ b) =
        dualizingModule.tmul F (φ.comp rF.toLinearMap) b :=
    dualizingModuleEquiv_tmul H F H hH (AlgHom.id A H.middle) rF (fun _ => rfl) hF φ b
  have hcomp : f.comp e.toLinearMap.toAddMonoidHom =
      g.comp e.toLinearMap.toAddMonoidHom := by
    refine dualizingModule_addMonoidHom_ext_tmul H _ _ fun φ b => ?_
    show f (e (dualizingModule.tmul H φ b)) =
      g (e (dualizingModule.tmul H φ b))
    rw [heq φ b]
    exact h φ b
  refine AddMonoidHom.ext fun z => ?_
  simpa [AddMonoidHom.comp_apply] using
    congrArg (fun k : dualizingModule H →+ N => k (e.symm z)) hcomp

/-- An additive map between relative dualizing modules which restricts the functional along a
linear map compatible with the maps to the target is the canonical comparison. -/
private theorem addMonoidHom_eq_dualizingModuleEquiv
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Algebra.QuasiFinite A B]
    (F : FiniteOpenFactorization.{u, v, w} A B) (G : FiniteOpenFactorization.{u, v, y} A B)
    (i : G.middle →ₗ[A] F.middle)
    (hi : ∀ a, algebraMap F.middle B (i a) = algebraMap G.middle B a)
    (g : dualizingModule F →+ dualizingModule G)
    (hg : ∀ φ b, g (dualizingModule.tmul F φ b) = dualizingModule.tmul G (φ.comp i) b) :
    g = (dualizingModuleEquiv F G).toLinearMap.toAddMonoidHom := by
  obtain ⟨H, ⟨⟨rF, rG⟩, hF, hG, hH⟩⟩ := commonFiniteOpenRefinement F G
  refine dualizingModule_addMonoidHom_ext_common F H hH rF hF _ _ fun φ b => ?_
  have key : (φ.comp rF.toLinearMap).comp i = φ.comp rG.toLinearMap := by
    ext a
    exact congrArg φ (hH ((hF (i a)).trans ((hi a).trans (hG a).symm)))
  exact (hg _ b).trans ((congrArg (fun ψ => dualizingModule.tmul G ψ b) key).trans
    (dualizingModuleEquiv_tmul F G H hH rF rG hF hG φ b).symm)

/-- The first-factor restriction is the canonical comparison of the restricted factorization
with the chosen one. -/
theorem dualizingModuleProductFirstRestrict_eq
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [IsNoetherianRing A] [Algebra.QuasiFinite A B]
    (F : FiniteOpenFactorization.{u, max v w, x} A (B × C))
    (FB : FiniteOpenFactorization.{u, v, y} A B)
    (FC : FiniteOpenFactorization.{u, w, z} A C)
    (e : (FB.middle × FC.middle) ≃ₐ[A] F.middle)
    (hcompat : ∀ p : FB.middle × FC.middle,
      algebraMap F.middle (B × C) (e p) =
        (algebraMap FB.middle B p.1, algebraMap FC.middle C p.2)) :
    dualizingModuleProductFirstRestrict F FB FC e hcompat =
      (dualizingModuleEquiv (firstFactorization F) FB).toLinearMap.toAddMonoidHom :=
  addMonoidHom_eq_dualizingModuleEquiv (firstFactorization F) FB
    (e.toLinearMap.comp (LinearMap.inl A FB.middle FC.middle))
    (fun a => congrArg Prod.fst (hcompat (a, 0))) _
    (dualizingModuleProductFirstRestrict_tmul F FB FC e hcompat)

/-- The second-factor restriction is the canonical comparison of the restricted factorization
with the chosen one. -/
theorem dualizingModuleProductSecondRestrict_eq
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [IsNoetherianRing A] [Algebra.QuasiFinite A C]
    (F : FiniteOpenFactorization.{u, max v w, x} A (B × C))
    (FB : FiniteOpenFactorization.{u, v, y} A B)
    (FC : FiniteOpenFactorization.{u, w, z} A C)
    (e : (FB.middle × FC.middle) ≃ₐ[A] F.middle)
    (hcompat : ∀ p : FB.middle × FC.middle,
      algebraMap F.middle (B × C) (e p) =
        (algebraMap FB.middle B p.1, algebraMap FC.middle C p.2)) :
    dualizingModuleProductSecondRestrict F FB FC e hcompat =
      (dualizingModuleEquiv (secondFactorization F) FC).toLinearMap.toAddMonoidHom :=
  addMonoidHom_eq_dualizingModuleEquiv (secondFactorization F) FC
    (e.toLinearMap.comp (LinearMap.inr A FB.middle FC.middle))
    (fun a => congrArg Prod.snd (hcompat (0, a))) _
    (dualizingModuleProductSecondRestrict_tmul F FB FC e hcompat)

/-- For a product factorization, the product equivalence sends a pure tensor to the pair
obtained by restricting its functional to the two factors and projecting its coefficient.
The compatibility condition identifies the map from the middle algebra to the product target
with the componentwise maps. -/
@[stacks 0BT5 "pure-tensor formula for a product factorization"]
theorem dualizingModuleProdEquiv_tmul
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    [Algebra.QuasiFinite A B] [Algebra.QuasiFinite A C]
    (F : FiniteOpenFactorization.{u, max v w, x} A (B × C))
    (FB : FiniteOpenFactorization.{u, v, y} A B)
    (FC : FiniteOpenFactorization.{u, w, z} A C)
    (e : (FB.middle × FC.middle) ≃ₐ[A] F.middle)
    (hcompat : ∀ p : FB.middle × FC.middle,
      (algebraMap F.middle (B × C)) (e p) =
        ((algebraMap FB.middle B) p.1, (algebraMap FC.middle C) p.2))
    (f : Module.Dual A F.middle) (b : B) (c : C) :
    (dualizingModuleProdEquiv F FB FC) (dualizingModule.tmul F f (b, c)) =
      (dualizingModule.tmul FB
        (f.comp (e.toLinearMap.comp (LinearMap.inl A FB.middle FC.middle))) b,
       dualizingModule.tmul FC
        (f.comp (e.toLinearMap.comp (LinearMap.inr A FB.middle FC.middle))) c) := by
  rw [dualizingModuleProdEquiv_apply, productFactorizationEquiv_tmul]
  refine Prod.ext ?_ ?_
  · exact congrArg (fun k : dualizingModule (firstFactorization F) →+ dualizingModule FB =>
      k (dualizingModule.tmul (firstFactorization F) f b))
      (dualizingModuleProductFirstRestrict_eq F FB FC e hcompat).symm |>.trans
        (dualizingModuleProductFirstRestrict_tmul F FB FC e hcompat f b)
  · exact congrArg (fun k : dualizingModule (secondFactorization F) →+ dualizingModule FC =>
      k (dualizingModule.tmul (secondFactorization F) f c))
      (dualizingModuleProductSecondRestrict_eq F FB FC e hcompat).symm |>.trans
        (dualizingModuleProductSecondRestrict_tmul F FB FC e hcompat f c)

/-- Two additive maps out of the dualizing module of a product agree as soon as they agree on
the pure tensors supported on each of the two factors. -/
theorem dualizingModule_product_ext
    {A : Type u} {B : Type v} {C : Type w} {N : Type*}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    [Algebra.QuasiFinite A B] [Algebra.QuasiFinite A C]
    (F : FiniteOpenFactorization.{u, max v w, x} A (B × C))
    (FB : FiniteOpenFactorization.{u, v, y} A B)
    (FC : FiniteOpenFactorization.{u, w, z} A C)
    (e : (FB.middle × FC.middle) ≃ₐ[A] F.middle)
    (hcompat : ∀ p : FB.middle × FC.middle,
      algebraMap F.middle (B × C) (e p) =
        (algebraMap FB.middle B p.1, algebraMap FC.middle C p.2))
    [AddCommGroup N] (L R : dualizingModule F →+ N)
    (hB : ∀ (φ : Module.Dual A FB.middle) (b : B),
      L (dualizingModule.tmul F
        (φ.comp ((LinearMap.fst A FB.middle FC.middle).comp e.symm.toLinearMap)) (b, 0)) =
      R (dualizingModule.tmul F
        (φ.comp ((LinearMap.fst A FB.middle FC.middle).comp e.symm.toLinearMap)) (b, 0)))
    (hC : ∀ (φ : Module.Dual A FC.middle) (c : C),
      L (dualizingModule.tmul F
        (φ.comp ((LinearMap.snd A FB.middle FC.middle).comp e.symm.toLinearMap)) (0, c)) =
      R (dualizingModule.tmul F
        (φ.comp ((LinearMap.snd A FB.middle FC.middle).comp e.symm.toLinearMap)) (0, c))) :
    L = R := by
  let : Module (B × C) (dualizingModule FB) := Module.compHom _ (RingHom.fst B C)
  let : Module (B × C) (dualizingModule FC) := Module.compHom _ (RingHom.snd B C)
  let E := (dualizingModuleProdEquiv F FB FC).toLinearMap.toAddMonoidHom
  let E' := (dualizingModuleProdEquiv F FB FC).symm.toLinearMap.toAddMonoidHom
  have hB' : (L.comp E').comp (AddMonoidHom.inl _ _) =
      (R.comp E').comp (AddMonoidHom.inl _ _) := by
    refine dualizingModule_addMonoidHom_ext_tmul FB _ _ fun φ b => ?_
    have he : E (dualizingModule.tmul F
        (φ.comp ((LinearMap.fst A FB.middle FC.middle).comp e.symm.toLinearMap)) (b, 0)) =
        (dualizingModule.tmul FB φ b, 0) := by
      have key : (φ.comp ((LinearMap.fst A FB.middle FC.middle).comp
          e.symm.toLinearMap)).comp
          (e.toLinearMap.comp (LinearMap.inl A FB.middle FC.middle)) = φ := by
        ext a
        show φ ((e.symm (e (a, 0))).1) = φ a
        rw [e.symm_apply_apply]
      show dualizingModuleProdEquiv F FB FC _ = _
      rw [dualizingModuleProdEquiv_tmul F FB FC e hcompat]
      refine Prod.ext ?_ ?_
      · exact congrArg (fun χ : Module.Dual A FB.middle =>
          dualizingModule.tmul FB χ b) key
      · exact dualizingModule.tmul_zero FC _
    show L (E' (dualizingModule.tmul FB φ b, 0)) =
      R (E' (dualizingModule.tmul FB φ b, 0))
    rw [← he]
    simpa [E, E'] using hB φ b
  have hC' : (L.comp E').comp (AddMonoidHom.inr _ _) =
      (R.comp E').comp (AddMonoidHom.inr _ _) := by
    refine dualizingModule_addMonoidHom_ext_tmul FC _ _ fun φ c => ?_
    have he : E (dualizingModule.tmul F
        (φ.comp ((LinearMap.snd A FB.middle FC.middle).comp e.symm.toLinearMap)) (0, c)) =
        (0, dualizingModule.tmul FC φ c) := by
      have key : (φ.comp ((LinearMap.snd A FB.middle FC.middle).comp
          e.symm.toLinearMap)).comp
          (e.toLinearMap.comp (LinearMap.inr A FB.middle FC.middle)) = φ := by
        ext a
        show φ ((e.symm (e (0, a))).2) = φ a
        rw [e.symm_apply_apply]
      show dualizingModuleProdEquiv F FB FC _ = _
      rw [dualizingModuleProdEquiv_tmul F FB FC e hcompat]
      refine Prod.ext ?_ ?_
      · exact dualizingModule.tmul_zero FB _
      · exact congrArg (fun χ : Module.Dual A FC.middle =>
          dualizingModule.tmul FC χ c) key
    show L (E' (0, dualizingModule.tmul FC φ c)) =
      R (E' (0, dualizingModule.tmul FC φ c))
    rw [← he]
    simpa [E, E'] using hC φ c
  refine AddMonoidHom.ext fun ω => ?_
  obtain ⟨⟨b, c⟩, rfl⟩ := (dualizingModuleProdEquiv F FB FC).symm.surjective ω
  have hb := DFunLike.congr_fun hB' b
  have hc := DFunLike.congr_fun hC' c
  show L (E' (b, c)) = R (E' (b, c))
  change L (E' (b, 0)) = R (E' (b, 0)) at hb
  change L (E' (0, c)) = R (E' (0, c)) at hc
  rw [show (b, c) = (b, 0) + (0, c) by simp, map_add, map_add, map_add, hb, hc]

/-- The canonical comparison out of a factorization whose intermediate algebra embeds in the
target and dominates the other one, read on pure tensors. -/
theorem dualizingModuleEquiv_from_injective
    {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    (H : FiniteOpenFactorization.{u, v, w} A B)
    (F : FiniteOpenFactorization.{u, v, x} A B)
    (hH : Function.Injective (algebraMap H.middle B))
    (r : F.middle →ₐ[A] H.middle)
    (hr : ∀ a, algebraMap H.middle B (r a) = algebraMap F.middle B a)
    (φ : Module.Dual A H.middle) (b : B) :
    dualizingModuleEquiv H F (dualizingModule.tmul H φ b) =
      dualizingModule.tmul F (φ.comp r.toLinearMap) b :=
  dualizingModuleEquiv_tmul H F H hH (AlgHom.id A H.middle) r (fun _ => rfl) hr φ b

/-- Changing the finite-open factorizations of the product and its two factors commutes
with the canonical product equivalence. -/
@[stacks 0BT5 "independence of factorization"]
theorem dualizingModuleProdEquiv_naturality
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    [Algebra.QuasiFinite A B] [Algebra.QuasiFinite A C]
    (F : FiniteOpenFactorization.{u, max v w, x} A (B × C))
    (G : FiniteOpenFactorization.{u, max v w, x'} A (B × C))
    (FB : FiniteOpenFactorization.{u, v, y} A B)
    (GB : FiniteOpenFactorization.{u, v, y'} A B)
    (FC : FiniteOpenFactorization.{u, w, z} A C)
    (GC : FiniteOpenFactorization.{u, w, z'} A C)
    (ω : dualizingModule F) :
    (dualizingModuleProdEquiv G GB GC) (dualizingModuleEquiv F G ω) =
      (dualizingModuleEquiv FB GB
        ((dualizingModuleProdEquiv F FB FC ω).1),
       dualizingModuleEquiv FC GC
        ((dualizingModuleProdEquiv F FB FC ω).2)) := by
  let hB := commonFiniteOpenRefinementFour (firstFactorization F)
    (firstFactorization G) FB GB
  let hC := commonFiniteOpenRefinementFour (secondFactorization F)
    (secondFactorization G) FC GC
  let HB := hB.factorization
  let HC := hC.factorization
  let H := productFiniteOpenFactorization HB HC
  let rF : F.middle →ₐ[A] H.middle := hB.map₀.prod hC.map₀
  let rG : G.middle →ₐ[A] H.middle := hB.map₁.prod hC.map₁
  have hH : Function.Injective (algebraMap H.middle (B × C)) := fun _ _ hpq =>
    Prod.ext (hB.injective (congrArg Prod.fst hpq)) (hC.injective (congrArg Prod.snd hpq))
  have hF (a : F.middle) :
      algebraMap H.middle (B × C) (rF a) = algebraMap F.middle (B × C) a :=
    Prod.ext (hB.compat₀ a) (hC.compat₀ a)
  have hG (a : G.middle) :
      algebraMap H.middle (B × C) (rG a) = algebraMap G.middle (B × C) a :=
    Prod.ext (hB.compat₁ a) (hC.compat₁ a)
  let : Module (B × C) (dualizingModule FB) := Module.compHom _ (RingHom.fst B C)
  let : Module (B × C) (dualizingModule FC) := Module.compHom _ (RingHom.snd B C)
  let : Module (B × C) (dualizingModule GB) := Module.compHom _ (RingHom.fst B C)
  let : Module (B × C) (dualizingModule GC) := Module.compHom _ (RingHom.snd B C)
  let L : dualizingModule H →+ (dualizingModule GB × dualizingModule GC) :=
    (dualizingModuleProdEquiv G GB GC).toLinearMap.toAddMonoidHom.comp
      (dualizingModuleEquiv H G).toLinearMap.toAddMonoidHom
  let R : dualizingModule H →+ (dualizingModule GB × dualizingModule GC) :=
    ((dualizingModuleEquiv FB GB).toLinearMap.toAddMonoidHom.prodMap
      (dualizingModuleEquiv FC GC).toLinearMap.toAddMonoidHom).comp
        ((dualizingModuleProdEquiv F FB FC).toLinearMap.toAddMonoidHom.comp
          (dualizingModuleEquiv H F).toLinearMap.toAddMonoidHom)
  have hL : L = R := by
    apply dualizingModule_product_ext H HB HC (AlgEquiv.refl) (fun _ => rfl)
    · intro φ b
      show dualizingModuleProdEquiv G GB GC
          (dualizingModuleEquiv H G _) =
        (dualizingModuleEquiv FB GB
          (dualizingModuleProdEquiv F FB FC (dualizingModuleEquiv H F _)).1,
        dualizingModuleEquiv FC GC
          (dualizingModuleProdEquiv F FB FC (dualizingModuleEquiv H F _)).2)
      simp only [dualizingModuleEquiv_from_injective H G hH rG hG,
        dualizingModuleEquiv_from_injective H F hH rF hF,
        dualizingModuleProdEquiv_apply, productFactorizationEquiv_tmul]
      refine Prod.ext ?_ ?_
      · exact (dualizingModuleEquiv_tmul (firstFactorization G) GB HB
            hB.injective hB.map₁ hB.map₃ hB.compat₁ hB.compat₃ φ b).trans
          ((dualizingModuleEquiv_tmul FB GB HB
              hB.injective hB.map₂ hB.map₃ hB.compat₂ hB.compat₃ φ b).symm.trans
            (congrArg (fun z : dualizingModule FB => dualizingModuleEquiv FB GB z)
              (dualizingModuleEquiv_tmul (firstFactorization F) FB HB
                hB.injective hB.map₀ hB.map₂ hB.compat₀ hB.compat₂ φ b).symm))
      · exact (dualizingModuleEquiv_tmul_zero (secondFactorization G) GC _).trans
          (((congrArg (fun z : dualizingModule FC => dualizingModuleEquiv FC GC z)
              (dualizingModuleEquiv_tmul_zero (secondFactorization F) FC _)).trans
            (map_zero (dualizingModuleEquiv FC GC))).symm)
    · intro φ c
      show dualizingModuleProdEquiv G GB GC
          (dualizingModuleEquiv H G _) =
        (dualizingModuleEquiv FB GB
          (dualizingModuleProdEquiv F FB FC (dualizingModuleEquiv H F _)).1,
        dualizingModuleEquiv FC GC
          (dualizingModuleProdEquiv F FB FC (dualizingModuleEquiv H F _)).2)
      simp only [dualizingModuleEquiv_from_injective H G hH rG hG,
        dualizingModuleEquiv_from_injective H F hH rF hF,
        dualizingModuleProdEquiv_apply, productFactorizationEquiv_tmul]
      refine Prod.ext ?_ ?_
      · exact (dualizingModuleEquiv_tmul_zero (firstFactorization G) GB _).trans
          (((congrArg (fun z : dualizingModule FB => dualizingModuleEquiv FB GB z)
              (dualizingModuleEquiv_tmul_zero (firstFactorization F) FB _)).trans
            (map_zero (dualizingModuleEquiv FB GB))).symm)
      · exact (dualizingModuleEquiv_tmul (secondFactorization G) GC HC
            hC.injective hC.map₁ hC.map₃ hC.compat₁ hC.compat₃ φ c).trans
          ((dualizingModuleEquiv_tmul FC GC HC
              hC.injective hC.map₂ hC.map₃ hC.compat₂ hC.compat₃ φ c).symm.trans
            (congrArg (fun z : dualizingModule FC => dualizingModuleEquiv FC GC z)
              (dualizingModuleEquiv_tmul (secondFactorization F) FC HC
                hC.injective hC.map₀ hC.map₂ hC.compat₀ hC.compat₂ φ c).symm))
  obtain ⟨η, rfl⟩ := (dualizingModuleEquiv H F).surjective ω
  have htrans := DFunLike.congr_fun (dualizingModuleEquiv_trans H F G) η
  change dualizingModuleEquiv F G (dualizingModuleEquiv H F η) =
    dualizingModuleEquiv H G η at htrans
  rw [htrans]
  exact DFunLike.congr_fun hL η

end Stacks.Discriminant
