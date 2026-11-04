module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GroupRingInvariantsLimit
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Coinduction from `Λ` to `Λ[G]` for a finite group

Let `Λ` be a commutative ring and `G` a finite group.  Coinduction is coextension of scalars
along `ι : Λ → Λ[G]`, `M ↦ Hom_Λ(Λ[G], M)`.  It is right adjoint to restriction of scalars along
`ι`; for finite `G` it is also *left* adjoint to it (Frobenius reciprocity, "induced equals
coinduced"): a `Λ[G]`-linear map `Hom_Λ(Λ[G], M) ⟶ N` is determined by the `Λ`-linear map
`m ↦ φ(δ_m)`, where `δ_m(a) = a(1) • m`, and conversely `ψ : M ⟶ N` extends to
`f ↦ ∑_g g • ψ(f(g⁻¹))`.

Moreover invariants of a coinduced module are the module itself: coinduction followed by
invariants is coextension of scalars along the composite `Λ → Λ[G] → Λ`, the identity.

## Main definitions

* `Stacks.EtaleCohomology.groupRingCoinductionAdj`: coinduction is left adjoint to restriction
  of scalars along `Λ → Λ[G]`, for finite `G`.
* `Stacks.EtaleCohomology.groupRingCoinductionInvariantsIso`: invariants of coinduction are the
  identity.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v

namespace Stacks.EtaleCohomology

variable (Λ : Type) [CommRing Λ] (G : Type) [Group G]

/-- Coinduction `M ↦ Hom_Λ(Λ[G], M)`, coextension of scalars along `Λ → Λ[G]`. -/
abbrev groupRingCoinduction : ModuleCat.{v} Λ ⥤ ModuleCat.{v} (MonoidAlgebra Λ G) :=
  ModuleCat.coextendScalars (groupRingScalars Λ G)

/-- `Λ[G]` viewed as a `Λ`-module by restriction of scalars, the source of the `Λ`-linear maps
making up the coinduced module. -/
abbrev GroupRingRes : Type :=
  (ModuleCat.restrictScalars (groupRingScalars Λ G)).obj
    (ModuleCat.of (MonoidAlgebra Λ G) (MonoidAlgebra Λ G))

variable {Λ G}

/-- An element of `Λ[G]`, read in `GroupRingRes Λ G`. -/
def toGroupRingRes (a : MonoidAlgebra Λ G) : GroupRingRes Λ G := a

/-- An element of `GroupRingRes Λ G`, read in `Λ[G]`. -/
def ofGroupRingRes (a : GroupRingRes Λ G) : MonoidAlgebra Λ G := a

/-- `ofGroupRingRes` is additive. -/
lemma ofGroupRingRes_add (a b : GroupRingRes Λ G) :
    ofGroupRingRes (a + b) = ofGroupRingRes a + ofGroupRingRes b := rfl

/-- The scalar `c : Λ` acts on `GroupRingRes Λ G` as left multiplication by `c • 1 ∈ Λ[G]`. -/
lemma ofGroupRingRes_smul (c : Λ) (a : GroupRingRes Λ G) :
    ofGroupRingRes (c • a) = MonoidAlgebra.single (1 : G) c * ofGroupRingRes a := rfl

/-- `toGroupRingRes` is additive. -/
lemma toGroupRingRes_add (a b : MonoidAlgebra Λ G) :
    toGroupRingRes (a + b) = toGroupRingRes a + toGroupRingRes b := rfl

/-- `toGroupRingRes` sends `0` to `0`. -/
lemma toGroupRingRes_zero : toGroupRingRes (0 : MonoidAlgebra Λ G) = 0 := rfl

/-- Left multiplication by `c • 1 ∈ Λ[G]` corresponds to the action of `c : Λ` on
`GroupRingRes Λ G`. -/
lemma toGroupRingRes_single_one_mul (c : Λ) (a : MonoidAlgebra Λ G) :
    toGroupRingRes (MonoidAlgebra.single (1 : G) c * a) = c • toGroupRingRes a := rfl

section Elements

variable {M : ModuleCat.{v} Λ}

/-- Evaluation of an element of the coinduced module at an element of `Λ[G]`. -/
def coindEval (f : (groupRingCoinduction Λ G).obj M) (a : MonoidAlgebra Λ G) : M :=
  ModuleCat.CoextendScalars.equiv _ M f (toGroupRingRes a)

/-- Evaluation of an element of the coinduced module is additive in the argument. -/
lemma coindEval_add (f : (groupRingCoinduction Λ G).obj M) (a b : MonoidAlgebra Λ G) :
    coindEval f (a + b) = coindEval f a + coindEval f b := by
  rw [coindEval, toGroupRingRes_add, map_add]; rfl

/-- An element of the coinduced module vanishes at `0`. -/
lemma coindEval_zero (f : (groupRingCoinduction Λ G).obj M) :
    coindEval f (0 : MonoidAlgebra Λ G) = 0 := by
  rw [coindEval, toGroupRingRes_zero, map_zero]

/-- An element `f` of the coinduced module is `Λ`-linear: `f((c • 1) * a) = c • f(a)`. -/
lemma coindEval_single_one_mul (f : (groupRingCoinduction Λ G).obj M) (c : Λ)
    (a : MonoidAlgebra Λ G) :
    coindEval f (MonoidAlgebra.single (1 : G) c * a) = c • coindEval f a := by
  rw [coindEval, toGroupRingRes_single_one_mul, map_smul]; rfl

/-- `f(c • g) = c • f(g)` for an element `f` of the coinduced module. -/
lemma coindEval_single (f : (groupRingCoinduction Λ G).obj M) (g : G) (c : Λ) :
    coindEval f (MonoidAlgebra.single g c) = c • coindEval f (MonoidAlgebra.single g 1) := by
  rw [← coindEval_single_one_mul, MonoidAlgebra.single_mul_single, one_mul, mul_one]

/-- The action of `Λ[G]` on the coinduced module: `(s • f)(a) = f(a * s)`. -/
lemma coindEval_smul (f : (groupRingCoinduction Λ G).obj M) (s a : MonoidAlgebra Λ G) :
    coindEval (s • f) a = coindEval f (a * s) :=
  rfl

/-- Evaluation is additive in the element of the coinduced module. -/
lemma coindEval_add_left (f f' : (groupRingCoinduction Λ G).obj M) (a : MonoidAlgebra Λ G) :
    coindEval (f + f') a = coindEval f a + coindEval f' a :=
  rfl

/-- The zero element of the coinduced module evaluates to `0` everywhere. -/
lemma coindEval_zero_left (a : MonoidAlgebra Λ G) :
    coindEval (0 : (groupRingCoinduction Λ G).obj M) a = 0 :=
  rfl

/-- Evaluation of a finite sum of elements of the coinduced module is the sum of the
evaluations. -/
lemma coindEval_sum_left {ι : Type*} (s : Finset ι)
    (f : ι → (groupRingCoinduction Λ G).obj M) (a : MonoidAlgebra Λ G) :
    coindEval (∑ i ∈ s, f i) a = ∑ i ∈ s, coindEval (f i) a := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, coindEval_add_left, ih]

/-- Two elements of the coinduced module agreeing at every `a : Λ[G]` are equal. -/
lemma coind_ext {f f' : (groupRingCoinduction Λ G).obj M}
    (h : ∀ a : MonoidAlgebra Λ G, coindEval f a = coindEval f' a) : f = f' :=
  ModuleCat.CoextendScalars.ext (LinearMap.ext fun a => h a)

end Elements

/-- The coinduced element `δ_m : a ↦ a(1) • m`. -/
def groupRingCoinductionDelta (M : ModuleCat.{v} Λ) (m : M) :
    (groupRingCoinduction Λ G).obj M :=
  (ModuleCat.CoextendScalars.equiv _ M).symm
    { toFun := fun a : MonoidAlgebra Λ G => a.coeff 1 • m
      map_add' := fun a b => by exact add_smul _ _ m
      map_smul' := fun c a => by
        exact (congrArg (· • m)
          (MonoidAlgebra.coeff_single_one_mul (a : MonoidAlgebra Λ G) c 1)).trans
            (mul_smul _ _ _) }

/-- `δ_m(a) = a(1) • m`. -/
lemma coindEval_delta (M : ModuleCat.{v} Λ) (m : M) (a : MonoidAlgebra Λ G) :
    coindEval (groupRingCoinductionDelta M m) a = a.coeff 1 • m :=
  rfl

/-- `δ_{m + m'} = δ_m + δ_{m'}`. -/
lemma groupRingCoinductionDelta_add (M : ModuleCat.{v} Λ) (m m' : M) :
    groupRingCoinductionDelta (G := G) M (m + m') =
      groupRingCoinductionDelta M m + groupRingCoinductionDelta M m' :=
  coind_ext fun _ => smul_add _ m m'

/-- `δ_{c • m} = (c • 1) • δ_m` for `c : Λ`. -/
lemma groupRingCoinductionDelta_smul (M : ModuleCat.{v} Λ) (c : Λ) (m : M) :
    groupRingCoinductionDelta (G := G) M (c • m) =
      MonoidAlgebra.single (1 : G) c • groupRingCoinductionDelta M m :=
  coind_ext fun a => by
    rw [coindEval_smul, coindEval_delta, coindEval_delta, MonoidAlgebra.coeff_mul_single_one,
      mul_smul]

/-- The `Λ`-linear map `m ↦ δ_m` from `M` to the restriction of scalars of its coinduction. -/
def groupRingCoinductionDeltaHom (M : ModuleCat.{v} Λ) :
    M ⟶ (ModuleCat.restrictScalars (groupRingScalars Λ G)).obj
      ((groupRingCoinduction Λ G).obj M) :=
  ModuleCat.ofHom (X := M) (Y := (ModuleCat.restrictScalars (groupRingScalars Λ G)).obj
      ((groupRingCoinduction Λ G).obj M))
    ({ toFun := fun m => groupRingCoinductionDelta M m
       map_add' := groupRingCoinductionDelta_add M
       map_smul' := groupRingCoinductionDelta_smul M } :
      M →ₗ[Λ] (ModuleCat.restrictScalars (groupRingScalars Λ G)).obj
        ((groupRingCoinduction Λ G).obj M))

/-- An element of a restriction of scalars, read as an element of the module itself. -/
def groupRingRes {N : ModuleCat.{v} (MonoidAlgebra Λ G)}
    (x : (ModuleCat.restrictScalars (groupRingScalars Λ G)).obj N) : N := x

/-- The scalar `c : Λ` acts on a restriction of scalars as `c • 1 ∈ Λ[G]`. -/
lemma groupRingRes_smul {N : ModuleCat.{v} (MonoidAlgebra Λ G)} (c : Λ)
    (x : (ModuleCat.restrictScalars (groupRingScalars Λ G)).obj N) :
    groupRingRes (c • x) = MonoidAlgebra.single (1 : G) c • groupRingRes x :=
  rfl

/-- `groupRingRes` is additive. -/
lemma groupRingRes_add {N : ModuleCat.{v} (MonoidAlgebra Λ G)}
    (x y : (ModuleCat.restrictScalars (groupRingScalars Λ G)).obj N) :
    groupRingRes (x + y) = groupRingRes x + groupRingRes y :=
  rfl

/-- `groupRingRes` sends `0` to `0`. -/
lemma groupRingRes_zero {N : ModuleCat.{v} (MonoidAlgebra Λ G)} :
    groupRingRes (0 : (ModuleCat.restrictScalars (groupRingScalars Λ G)).obj N) = 0 :=
  rfl

variable [Fintype G]

/-- `f(a) = ∑_g a(g)·f(g)`, for an element of the coinduced module. -/
lemma coindEval_eq_sum {M : ModuleCat.{v} Λ}
    (f : (groupRingCoinduction Λ G).obj M) (a : MonoidAlgebra Λ G) :
    coindEval f a = ∑ g : G, a.coeff g • coindEval f (MonoidAlgebra.single g 1) := by
  classical
  induction a using MonoidAlgebra.induction_linear with
  | zero =>
    rw [coindEval_zero]
    simp
  | add a b ha hb =>
    rw [coindEval_add, ha, hb, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [MonoidAlgebra.coeff_add, Finsupp.add_apply, add_smul]
  | single h c =>
    rw [coindEval_single]
    simp [MonoidAlgebra.coeff_single, Finsupp.single_apply]

/-- The extension `f ↦ ∑_g g • ψ(f(g⁻¹))` of a `Λ`-linear map `ψ : M ⟶ N` to the coinduced
module. -/
def groupRingCoinductionLiftLinear {M : ModuleCat.{v} Λ} {N : ModuleCat.{v} (MonoidAlgebra Λ G)}
    (ψ : M ⟶ (ModuleCat.restrictScalars (groupRingScalars Λ G)).obj N) :
    (groupRingCoinduction Λ G).obj M →ₗ[MonoidAlgebra Λ G] N where
  toFun f := ∑ g : G, MonoidAlgebra.single g (1 : Λ) •
    groupRingRes (ψ (coindEval f (MonoidAlgebra.single g⁻¹ 1)))
  map_add' f f' := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← smul_add, coindEval_add_left, map_add, groupRingRes_add]
  map_smul' s f := by
    rw [RingHom.id_apply]
    induction s using MonoidAlgebra.induction_linear with
    | zero =>
      refine (Finset.sum_eq_zero fun g _ => ?_).trans (zero_smul _ _).symm
      rw [zero_smul, coindEval_zero_left, map_zero, groupRingRes_zero, smul_zero]
    | add s t hs ht =>
      rw [add_smul, add_smul, ← hs, ← ht, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [← smul_add, coindEval_add_left, map_add, groupRingRes_add]
    | single h c =>
      rw [Finset.smul_sum]
      refine (Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_).symm
      rw [Equiv.coe_mulLeft, coindEval_smul, MonoidAlgebra.single_mul_single,
        one_mul, mul_inv_rev, inv_mul_cancel_right, coindEval_single f g⁻¹ c, map_smul,
        groupRingRes_smul]
      simp only [smul_smul, MonoidAlgebra.single_mul_single, mul_one, one_mul]

/-- The extension of `ψ : M ⟶ N` to the coinduced module, as a morphism. -/
def groupRingCoinductionLift {M : ModuleCat.{v} Λ} {N : ModuleCat.{v} (MonoidAlgebra Λ G)}
    (ψ : M ⟶ (ModuleCat.restrictScalars (groupRingScalars Λ G)).obj N) :
    (groupRingCoinduction Λ G).obj M ⟶ N :=
  ModuleCat.ofHom (groupRingCoinductionLiftLinear ψ)

/-- The extension of `ψ` sends `f` to `∑_g g • ψ(f(g⁻¹))`. -/
lemma groupRingCoinductionLift_apply {M : ModuleCat.{v} Λ} {N : ModuleCat.{v} (MonoidAlgebra Λ G)}
    (ψ : M ⟶ (ModuleCat.restrictScalars (groupRingScalars Λ G)).obj N)
    (f : (groupRingCoinduction Λ G).obj M) :
    groupRingCoinductionLift ψ f = ∑ g : G, MonoidAlgebra.single g (1 : Λ) •
        groupRingRes (ψ (coindEval f (MonoidAlgebra.single g⁻¹ 1))) :=
  rfl

/-- The extension of `ψ` sends `δ_m` to `ψ(m)`. -/
lemma groupRingCoinductionLift_delta {M : ModuleCat.{v} Λ} {N : ModuleCat.{v} (MonoidAlgebra Λ G)}
    (ψ : M ⟶ (ModuleCat.restrictScalars (groupRingScalars Λ G)).obj N) (m : M) :
    groupRingCoinductionLift ψ (groupRingCoinductionDelta M m) = groupRingRes (ψ m) := by
  classical
  rw [groupRingCoinductionLift_apply, Finset.sum_eq_single (1 : G)]
  · rw [coindEval_delta, inv_one, MonoidAlgebra.coeff_single, Finsupp.single_eq_same, one_smul]
    exact one_smul _ _
  · intro g _ hg
    rw [coindEval_delta, MonoidAlgebra.coeff_single,
      Finsupp.single_eq_of_ne (by simpa using hg), zero_smul, map_zero, groupRingRes_zero,
      smul_zero]
  · simp

/-- `f = ∑_g g • δ_{f(g⁻¹)}` in the coinduced module. -/
lemma groupRingCoinduction_eq_sum_smul_delta (M : ModuleCat.{v} Λ)
    (f : (groupRingCoinduction Λ G).obj M) :
    f = ∑ g : G, MonoidAlgebra.single g (1 : Λ) •
      groupRingCoinductionDelta M (coindEval f (MonoidAlgebra.single g⁻¹ 1)) := by
  classical
  refine coind_ext fun a => ?_
  rw [coindEval_sum_left, coindEval_eq_sum]
  refine (Fintype.sum_equiv (Equiv.inv G) _ _ fun g => ?_)
  rw [Equiv.inv_apply, inv_inv, coindEval_smul, coindEval_delta,
    MonoidAlgebra.coeff_mul_single_apply, inv_inv, one_mul, mul_one]

variable (Λ G)

/-- **Frobenius reciprocity**: for a finite group, coinduction is left adjoint to restriction of
scalars along `Λ → Λ[G]`. -/
def groupRingCoinductionAdj :
    groupRingCoinduction.{v} Λ G ⊣ ModuleCat.restrictScalars (groupRingScalars Λ G) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M N =>
        { toFun := fun φ => groupRingCoinductionDeltaHom M ≫
            (ModuleCat.restrictScalars (groupRingScalars Λ G)).map φ
          invFun := fun ψ => groupRingCoinductionLift ψ
          left_inv := fun φ => by
            refine ModuleCat.hom_ext (LinearMap.ext fun f => ?_)
            change groupRingCoinductionLift (groupRingCoinductionDeltaHom M ≫
              (ModuleCat.restrictScalars (groupRingScalars Λ G)).map φ) f = φ f
            rw [groupRingCoinductionLift_apply]
            conv_rhs => rw [groupRingCoinduction_eq_sum_smul_delta M f, map_sum]
            refine Finset.sum_congr rfl fun g _ => ?_
            rw [map_smul]
            rfl
          right_inv := fun ψ => by
            refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
            exact groupRingCoinductionLift_delta ψ m }
      homEquiv_naturality_left_symm := fun f g => rfl
      homEquiv_naturality_right := fun f g => by
        dsimp only [Equiv.coe_fn_mk]
        rw [Functor.map_comp, Category.assoc] }

/-- Invariants of a coinduced module: coinduction followed by coextension of scalars along the
augmentation is the identity, coextension along the composite `Λ → Λ[G] → Λ`. -/
def groupRingCoinductionInvariantsIso :
    groupRingCoinduction.{v} Λ G ⋙ ModuleCat.coextendScalars (groupRingAugmentation Λ G) ≅
      𝟭 (ModuleCat.{v} Λ) :=
  Adjunction.rightAdjointUniq
    ((ModuleCat.restrictCoextendScalarsAdj (groupRingAugmentation Λ G)).comp
      (ModuleCat.restrictCoextendScalarsAdj (groupRingScalars Λ G)))
    (Adjunction.id.ofNatIsoLeft
      ((ModuleCat.restrictScalarsId' _ (RingHom.ext fun c =>
          groupRingAugmentation_scalars Λ G c)).symm ≪≫
        ModuleCat.restrictScalarsComp' (groupRingScalars Λ G) (groupRingAugmentation Λ G) _ rfl))

end Stacks.EtaleCohomology

end
