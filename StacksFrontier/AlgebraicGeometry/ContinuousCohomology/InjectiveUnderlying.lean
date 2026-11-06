module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.DiscreteModules
public import Mathlib.Algebra.Module.Injective
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Algebra.Category.Grp.Injective
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.DiscreteCompletedGroupAlgebraModule
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.InternalHomComplex

/-!
# Injective discrete modules are divisible

Let `Q` be a compact topological group. An injective object `J` of the category of continuous
discrete `Q`-modules (discrete `ℤ`-`Q`-modules) has a divisible, hence injective, underlying
abelian group. Given `x ∈ J` and `m ≠ 0`, let `U` be an open normal subgroup fixing `x` and
`ℤ[Q/U]` the permutation module. The orbit map `ℤ[Q/U] → J`, `[qU] ↦ q · x`, extends along the
monomorphism `m · : ℤ[Q/U] → ℤ[Q/U]` (the permutation module is torsion free) by injectivity of
`J`; the extension `ψ` gives `x = m · ψ([U])`.

## Main definitions

* `Stacks.ContinuousCohomology.permutationModule`: the permutation module `M[Q/U]`, for `U` open
  normal, as a continuous discrete `R`-`Q`-module.

## Main results

* `Stacks.ContinuousCohomology.exists_zsmul_eq_of_injective`: an injective discrete module is
  divisible.
* `Stacks.ContinuousCohomology.injective_forgetAb_of_injective`: its underlying abelian group is
  injective.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v w

namespace Stacks.ContinuousCohomology

variable (R : Type u) [Ring R] {Q : Type v} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]

section Permutation

variable (U : OpenNormalSubgroup Q) (M : Type w) [AddCommGroup M] [Module R M]

/-- The permutation representation of `Q` on `Q/U →₀ M`. -/
def permutationRep : Representation R Q (Q ⧸ (U : Subgroup Q) →₀ M) where
  toFun q := Finsupp.lmapDomain M R (fun c => q • c)
  map_one' := by
    refine LinearMap.ext fun f => ?_
    change Finsupp.mapDomain (fun c => (1 : Q) • c) f = f
    simp only [one_smul]
    exact Finsupp.mapDomain_id
  map_mul' q q' := by
    refine LinearMap.ext fun f => ?_
    change Finsupp.mapDomain (fun c => (q * q') • c) f =
      Finsupp.mapDomain (fun c => q • c) (Finsupp.mapDomain (fun c => q' • c) f)
    rw [← Finsupp.mapDomain_comp]
    congr 1
    exact funext (mul_smul q q')

omit [IsTopologicalGroup Q] in
/-- The permutation representation sends `single c m` to `single (q • c) m`. -/
lemma permutationRep_single (q : Q) (c : Q ⧸ (U : Subgroup Q)) (m : M) :
    permutationRep R U M q (Finsupp.single c m) = Finsupp.single (q • c) m :=
  Finsupp.mapDomain_single

omit [IsTopologicalGroup Q] in
/-- An element of `U` acts trivially in the permutation representation. -/
lemma permutationRep_of_mem (q : Q) (hq : q ∈ (U : Subgroup Q)) (f : Q ⧸ (U : Subgroup Q) →₀ M) :
    permutationRep R U M q f = f := by
  show Finsupp.mapDomain (fun c => q • c) f = f
  have : (fun c : Q ⧸ (U : Subgroup Q) => q • c) = id := by
    funext c
    induction c using QuotientGroup.induction_on with
    | H a =>
      show ((q * a : Q) : Q ⧸ (U : Subgroup Q)) = (a : Q ⧸ (U : Subgroup Q))
      rw [QuotientGroup.eq, mul_inv_rev, mul_assoc]
      simpa [mul_assoc] using U.isNormal'.conj_mem q⁻¹ (inv_mem hq) a⁻¹
  rw [this]
  exact Finsupp.mapDomain_id

/-- The permutation representation, transported to `ULift (Q/U →₀ M)`. -/
def permutationRepULift : Representation R Q (ULift.{max v w} (Q ⧸ (U : Subgroup Q) →₀ M)) where
  toFun q := (ULift.moduleEquiv (R := R)).symm.toLinearMap ∘ₗ permutationRep R U M q ∘ₗ
    (ULift.moduleEquiv (R := R)).toLinearMap
  map_one' := by
    refine LinearMap.ext fun f => ?_
    change ULift.up (permutationRep R U M 1 f.down) = f
    rw [map_one]
    rfl
  map_mul' q q' := by
    refine LinearMap.ext fun f => ?_
    change ULift.up (permutationRep R U M (q * q') f.down) =
      ULift.up (permutationRep R U M q (permutationRep R U M q' f.down))
    rw [map_mul]
    rfl

omit [IsTopologicalGroup Q] in
/-- The transported permutation representation acts on the underlying element. -/
lemma permutationRepULift_apply (q : Q) (f : ULift.{max v w} (Q ⧸ (U : Subgroup Q) →₀ M)) :
    permutationRepULift R U M q f = ULift.up (permutationRep R U M q f.down) := rfl

/-- **The permutation module** `M[Q/U]`, for `U` open normal, as a continuous discrete
`R`-`Q`-module (in a universe large enough for `Q`, `M` and `w`). -/
def permutationModule : Stacks.Injectives.ContinuousModule.{u, v, max v w} R Q :=
  Stacks.GroupCohomology.ofRepresentation (permutationRepULift R U M) (by
    rw [Stacks.GroupCohomology.isContinuous_actionOfRepresentation_iff]
    intro f
    let S : Subgroup Q :=
      { carrier := {g | permutationRepULift R U M g f = f}
        mul_mem' := fun {a b} ha hb => by
          change permutationRepULift R U M (a * b) f = f
          rw [map_mul, Module.End.mul_apply, show permutationRepULift R U M b f = f from hb, ha]
        one_mem' := by
          change permutationRepULift R U M 1 f = f
          rw [map_one]; rfl
        inv_mem' := fun {a} ha => by
          change permutationRepULift R U M a⁻¹ f = f
          conv_lhs => rw [← (show permutationRepULift R U M a f = f from ha)]
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl }
    change IsOpen (S : Set Q)
    refine Subgroup.isOpen_mono (H₁ := (U : Subgroup Q)) (fun g hg => ?_) U.isOpen'
    change permutationRepULift R U M g f = f
    rw [permutationRepULift_apply, permutationRep_of_mem R U M g hg])

end Permutation

section Mono

variable {R}

omit [IsTopologicalGroup Q] in
/-- A morphism of discrete modules with injective underlying map is a monomorphism. -/
lemma mono_of_injective_hom {X Y : Stacks.Injectives.ContinuousModule.{u, v, w} R Q} (f : X ⟶ Y)
    (h : Function.Injective f.hom.hom.hom.hom) : Mono f :=
  ⟨fun _ _ hab => (Stacks.GroupCohomology.homEquiv R Q _ _).injective <| Subtype.ext <|
    LinearMap.ext fun z => h (congrArg (fun t : _ ⟶ Y => t.hom.hom.hom.hom z) hab)⟩

end Mono

section Divisible

variable {Q : Type v} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [CompactSpace Q]
  (J : Stacks.Injectives.ContinuousModule.{0, v, max v w} ℤ Q)

/-- The orbit map `Q/U → J`, `qU ↦ q · x`, for `x` fixed by `U`. -/
def orbitMap (U : OpenNormalSubgroup Q) (x : J.obj.obj.V)
    (hx : ∀ g ∈ (U : Subgroup Q), (J.obj.obj.ρ g).asHom.hom x = x) :
    Q ⧸ (U : Subgroup Q) → J.obj.obj.V :=
  Quotient.lift (fun q => (J.obj.obj.ρ q).asHom.hom x) (by
    intro a b hab
    replace hab : a⁻¹ * b ∈ (U : Subgroup Q) := QuotientGroup.leftRel_apply.mp hab
    change (J.obj.obj.ρ a).asHom.hom x = (J.obj.obj.ρ b).asHom.hom x
    rw [show b = a * (a⁻¹ * b) by group, continuousModuleRho_mul_apply, hx _ hab])

omit [IsTopologicalGroup Q] [CompactSpace Q] in
/-- The orbit map sends the coset `qU` to `q · x`. -/
lemma orbitMap_mk (U : OpenNormalSubgroup Q) (x : J.obj.obj.V)
    (hx : ∀ g ∈ (U : Subgroup Q), (J.obj.obj.ρ g).asHom.hom x = x) (q : Q) :
    orbitMap J U x hx (q : Q ⧸ (U : Subgroup Q)) = (J.obj.obj.ρ q).asHom.hom x := rfl

omit [IsTopologicalGroup Q] [CompactSpace Q] in
/-- The orbit map is `Q`-equivariant. -/
lemma orbitMap_smul (U : OpenNormalSubgroup Q) (x : J.obj.obj.V)
    (hx : ∀ g ∈ (U : Subgroup Q), (J.obj.obj.ρ g).asHom.hom x = x) (q : Q) (c : Q ⧸ (U : Subgroup Q)) :
    orbitMap J U x hx (q • c) = (J.obj.obj.ρ q).asHom.hom (orbitMap J U x hx c) := by
  induction c using QuotientGroup.induction_on with
  | H a =>
    show (J.obj.obj.ρ (q * a)).asHom.hom x = (J.obj.obj.ρ q).asHom.hom ((J.obj.obj.ρ a).asHom.hom x)
    exact continuousModuleRho_mul_apply ℤ J q a x

/-- **An injective discrete `Q`-module is divisible.** -/
theorem exists_zsmul_eq_of_injective [Injective J] (x : J.obj.obj.V) (m : ℤ) (hm : m ≠ 0) :
    ∃ y : J.obj.obj.V, m • y = x := by
  let U := fixingSubgroup ℤ J x
  have hx : ∀ g ∈ (U : Subgroup Q), (J.obj.obj.ρ g).asHom.hom x = x :=
    mem_fixedSubmodule.mp (mem_fixedSubmodule_fixingSubgroup ℤ J x)
  let P := permutationModule.{0, v, w} ℤ U (ULift.{w} ℤ)
  let lin : (Q ⧸ (U : Subgroup Q) →₀ ULift.{w} ℤ) →+ J.obj.obj.V :=
    Finsupp.liftAddHom fun c =>
      (zmultiplesHom J.obj.obj.V (orbitMap J U x hx c)).comp AddEquiv.ulift.toAddMonoidHom
  have lin_single : ∀ c k, lin (Finsupp.single c k) = k.down • orbitMap J U x hx c := fun c k => by
    simp only [lin, Finsupp.liftAddHom_apply_single, AddMonoidHom.coe_comp, Function.comp_apply,
      zmultiplesHom_apply]
    rfl
  let φlin : P.obj.obj.V →ₗ[ℤ] J.obj.obj.V :=
    { toFun f := lin (ULift.down f)
      map_add' f g := map_add lin f.down g.down
      map_smul' r f := by
        have h := map_intCast_smul lin ℤ ℤ r f.down
        simp only [Int.cast_id] at h
        exact h }
  have hφ : ∀ (q : Q) (f : P.obj.obj.V),
      φlin ((P.obj.obj.ρ q).asHom.hom f) = (J.obj.obj.ρ q).asHom.hom (φlin f) := by
    rintro q ⟨f⟩
    show lin (permutationRep ℤ U (ULift.{w} ℤ) q f) = (J.obj.obj.ρ q).asHom.hom (lin f)
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simp only [map_add, hf, hg]
    | single c k =>
      rw [permutationRep_single, lin_single, lin_single, orbitMap_smul, map_zsmul]
  let φ : P ⟶ J := (Stacks.GroupCohomology.homEquiv ℤ Q P J).symm ⟨φlin, hφ⟩
  let ι : P ⟶ P := m • 𝟙 P
  have hι : Mono ι := mono_of_injective_hom ι (by
    rintro ⟨f⟩ ⟨g⟩ hfg
    have h : m • f = m • g := congrArg ULift.down hfg
    congr 1
    ext c
    have := congrArg (fun F : Q ⧸ (U : Subgroup Q) →₀ ULift.{w} ℤ => (F c).down) h
    simp only [Finsupp.coe_smul, Pi.smul_apply, ULift.smul_down, smul_eq_mul] at this
    exact mul_left_cancel₀ hm this)
  let ψ : P ⟶ J := Injective.factorThru φ ι
  have hψ : ι ≫ ψ = φ := Injective.comp_factorThru φ ι
  let e : P.obj.obj.V := ULift.up (Finsupp.single ((1 : Q) : Q ⧸ (U : Subgroup Q)) (ULift.up 1))
  refine ⟨ψ.hom.hom.hom.hom e, (map_zsmul ψ.hom.hom.hom.hom m e).symm.trans ?_⟩
  refine (congrArg (fun t : P ⟶ J => t.hom.hom.hom.hom e) hψ).trans ?_
  show lin (Finsupp.single _ (ULift.up 1)) = x
  rw [lin_single, orbitMap_mk, one_zsmul, continuousModuleRho_one_apply]

/-- The divisibility of an injective discrete module, as a `DivisibleBy` structure. -/
@[reducible] noncomputable def divisibleByOfInjective [Injective J] :
    DivisibleBy J.obj.obj.V ℤ where
  div a n := if h : n = 0 then 0 else (exists_zsmul_eq_of_injective J a n h).choose
  div_zero a := dif_pos rfl
  div_cancel {n} a h := by
    rw [dif_neg h]
    exact (exists_zsmul_eq_of_injective J a n h).choose_spec

/-- **The underlying abelian group of an injective discrete `Q`-module is injective.** -/
theorem injective_forgetAb_of_injective [Injective J] : Injective ((forgetAb ℤ Q).obj J) := by
  let := divisibleByOfInjective J
  exact AddCommGrpCat.injective_of_divisible J.obj.obj.V

end Divisible

end Stacks.ContinuousCohomology

end
