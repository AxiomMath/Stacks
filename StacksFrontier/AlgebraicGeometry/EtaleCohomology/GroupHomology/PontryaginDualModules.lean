module

public import Mathlib.Topology.Algebra.PontryaginDual
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.TorsionDerivedVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupHomology.CompactModules

/-!
# Pontryagin duality between compact and discrete `G`-modules

For an abelian topological group `M`, the character group `M^∧ = Hom_cont(M, S¹)` carries the
compact-open topology, and an action of a group `G` on `M` by continuous automorphisms induces the
contragredient action `(g • χ)(m) = χ(g⁻¹ • m)` on `M^∧`. When `M` is a compact `G`-module,
`M^∧` is a discrete `G`-module; when `M` is a discrete `G`-module, `M^∧` is a compact `G`-module.
This gives the two functors of the trivial duality of [Stacks, Tag 03VI], together with the
evaluation maps from a module to its double dual.

## Main definitions

* `Stacks.GroupHomology.AddPontryaginDual M`: the character group of an additive topological
  group, the additive form of `PontryaginDual (Multiplicative M)`.
* `Stacks.GroupHomology.AddPontryaginDual.comap`: precomposition with a continuous homomorphism.
* `Stacks.GroupHomology.discreteDual`: `M ↦ M^∧` from compact `G`-modules to discrete
  `G`-modules.
* `Stacks.GroupHomology.compactDual`: `M ↦ M^∧` from discrete `G`-modules to compact
  `G`-modules.
* `Stacks.GroupHomology.compactEvaluation` and `Stacks.GroupHomology.discreteEvaluation`: the
  natural evaluation maps from a module to its double dual.

## Main results

* `Stacks.GroupHomology.AddPontryaginDual.isOpen_stabilizer`: the stabilizer of a character of a
  compact `G`-module is open.
* `Stacks.GroupHomology.AddPontryaginDual.continuousSMul_of_discreteTopology`: the contragredient
  action on the dual of a discrete `G`-module is jointly continuous.

## Implementation notes

The circle is Mathlib's `Circle`, and `AddPontryaginDual M` is `Additive` of Mathlib's
`PontryaginDual (Multiplicative M)`, so that Mathlib's results on Pontryagin duals apply: the dual
of a compact group is discrete and the dual of a discrete group is compact. The underlying abelian
group of a discrete `G`-module is given the discrete topology inside `compactDual`.

## References

* [Stacks Project, Tag 03VI](https://stacks.math.columbia.edu/tag/03VI)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Filter Topology Stacks.GroupCohomology

universe u v

namespace Stacks.GroupHomology

/-- The character group `Hom_cont(M, S¹)` of an additive topological group, written additively:
the additive form of the Pontryagin dual of `Multiplicative M`. -/
def AddPontryaginDual (M : Type v) [AddMonoid M] [TopologicalSpace M] : Type v :=
  Additive (PontryaginDual (Multiplicative M))

namespace AddPontryaginDual

section Basic

variable {M N P : Type v} [AddCommGroup M] [TopologicalSpace M] [AddCommGroup N]
  [TopologicalSpace N] [AddCommGroup P] [TopologicalSpace P]

instance : AddCommGroup (AddPontryaginDual M) :=
  inferInstanceAs (AddCommGroup (Additive (PontryaginDual (Multiplicative M))))

instance : TopologicalSpace (AddPontryaginDual M) :=
  inferInstanceAs (TopologicalSpace (Additive (PontryaginDual (Multiplicative M))))

instance : IsTopologicalAddGroup (AddPontryaginDual M) :=
  inferInstanceAs (IsTopologicalAddGroup (Additive (PontryaginDual (Multiplicative M))))

instance : T2Space (AddPontryaginDual M) :=
  inferInstanceAs (T2Space (PontryaginDual (Multiplicative M)))

/-- The dual of a discrete group is compact. -/
instance [DiscreteTopology M] : CompactSpace (AddPontryaginDual M) :=
  inferInstanceAs (CompactSpace (PontryaginDual (Multiplicative M)))

/-- The dual of a compact group is discrete. -/
instance [CompactSpace M] : DiscreteTopology (AddPontryaginDual M) :=
  inferInstanceAs (DiscreteTopology (PontryaginDual (Multiplicative M)))

/-- A character, as a continuous homomorphism `Multiplicative M →ₜ* Circle`. -/
def toContinuousMonoidHom : AddPontryaginDual M ≃ (Multiplicative M →ₜ* Circle) :=
  Additive.toMul

/-- The passage to continuous monoid homomorphisms is continuous. -/
lemma continuous_toContinuousMonoidHom :
    Continuous (toContinuousMonoidHom : AddPontryaginDual M → (Multiplicative M →ₜ* Circle)) :=
  continuous_id

instance : FunLike (AddPontryaginDual M) M Circle where
  coe χ m := toContinuousMonoidHom χ (Multiplicative.ofAdd m)
  coe_injective _ _ h := toContinuousMonoidHom.injective
    (ContinuousMonoidHom.ext fun x ↦ congrFun h (Multiplicative.toAdd x))

/-- Two characters are equal when they agree at every point. -/
@[ext]
lemma ext {χ ψ : AddPontryaginDual M} (h : ∀ m, χ m = ψ m) : χ = ψ :=
  DFunLike.ext _ _ h

/-- A character takes sums to products. -/
@[simp] lemma map_add (χ : AddPontryaginDual M) (a b : M) : χ (a + b) = χ a * χ b :=
  MonoidHom.map_mul (toContinuousMonoidHom χ).toMonoidHom (Multiplicative.ofAdd a)
    (Multiplicative.ofAdd b)

/-- A character takes `0` to `1`. -/
@[simp] lemma map_zero (χ : AddPontryaginDual M) : χ 0 = 1 :=
  MonoidHom.map_one (toContinuousMonoidHom χ).toMonoidHom

/-- A character takes multiples to powers. -/
@[simp] lemma map_nsmul (χ : AddPontryaginDual M) (n : ℕ) (a : M) : χ (n • a) = χ a ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, map_add, ih, pow_succ]

/-- A character is continuous. -/
lemma continuous_apply (χ : AddPontryaginDual M) : Continuous χ :=
  (toContinuousMonoidHom χ).continuous.comp continuous_ofAdd

/-- The sum of two characters is their pointwise product. -/
@[simp] lemma add_apply (χ ψ : AddPontryaginDual M) (m : M) : (χ + ψ) m = χ m * ψ m := rfl

/-- The zero character is constant at `1`. -/
@[simp] lemma zero_apply (m : M) : (0 : AddPontryaginDual M) m = 1 := rfl

/-- The negative of a character is its pointwise inverse. -/
@[simp] lemma neg_apply (χ : AddPontryaginDual M) (m : M) : (-χ) m = (χ m)⁻¹ := rfl

/-- Evaluation of characters at a point is continuous. -/
lemma continuous_eval_apply (m : M) : Continuous fun χ : AddPontryaginDual M ↦ χ m :=
  (continuous_eval_const (F := Multiplicative M →ₜ* Circle) (Multiplicative.ofAdd m)).comp
    continuous_toContinuousMonoidHom

/-- The character given by a continuous map `M → S¹` taking sums to products. -/
def mk (f : M → Circle) (h0 : f 0 = 1) (hadd : ∀ a b, f (a + b) = f a * f b)
    (hf : Continuous f) : AddPontryaginDual M :=
  toContinuousMonoidHom.symm
    { toFun := fun x ↦ f (Multiplicative.toAdd x)
      map_one' := h0
      map_mul' := fun a b ↦ hadd (Multiplicative.toAdd a) (Multiplicative.toAdd b)
      continuous_toFun := hf.comp continuous_toAdd }

/-- The character `AddPontryaginDual.mk f` is `f`. -/
@[simp] lemma mk_apply (f : M → Circle) (h0 : f 0 = 1) (hadd : ∀ a b, f (a + b) = f a * f b)
    (hf : Continuous f) (m : M) : mk f h0 hadd hf m = f m := rfl

/-- A continuous homomorphism, viewed between the multiplicative forms. -/
def _root_.ContinuousAddMonoidHom.toContinuousMonoidHomMultiplicative (f : M →ₜ+ N) :
    Multiplicative M →ₜ* Multiplicative N where
  toMonoidHom := AddMonoidHom.toMultiplicative f.toAddMonoidHom
  continuous_toFun := continuous_ofAdd.comp (f.continuous.comp continuous_toAdd)

/-- Precomposition of characters with a continuous homomorphism `f : M →ₜ+ N`, the dual map
`N^∧ → M^∧`. -/
def comap (f : M →ₜ+ N) : AddPontryaginDual N →ₜ+ AddPontryaginDual M where
  toFun χ := toContinuousMonoidHom.symm
    ((toContinuousMonoidHom χ).comp f.toContinuousMonoidHomMultiplicative)
  map_zero' := rfl
  map_add' _ _ := rfl
  continuous_toFun := ContinuousMonoidHom.continuous_comp_left _

/-- The dual map is precomposition. -/
@[simp] lemma comap_apply (f : M →ₜ+ N) (χ : AddPontryaginDual N) (m : M) :
    comap f χ m = χ (f m) := rfl

/-- The dual of the identity is the identity. -/
@[simp] lemma comap_id : comap (ContinuousAddMonoidHom.id M) = ContinuousAddMonoidHom.id _ :=
  ContinuousAddMonoidHom.ext fun _ ↦ ext fun _ ↦ rfl

/-- The dual of a composite is the composite of the duals in the opposite order. -/
lemma comap_comp (f : M →ₜ+ N) (f' : N →ₜ+ P) :
    comap (f'.comp f) = (comap f).comp (comap f') :=
  ContinuousAddMonoidHom.ext fun _ ↦ ext fun _ ↦ rfl

/-- The dual of a sum of homomorphisms is the sum of the duals. -/
lemma comap_add [IsTopologicalAddGroup N] (f f' : M →ₜ+ N) :
    comap (f + f') = comap f + comap f' :=
  ContinuousAddMonoidHom.ext fun _ ↦ ext fun _ ↦ map_add _ _ _

end Basic

section Action

variable {G : Type u} [Group G] {M : Type v} [AddCommGroup M] [TopologicalSpace M]
  [DistribMulAction G M] [ContinuousConstSMul G M]

/-- The action of a group element, as a continuous homomorphism. -/
def smulHom (g : G) : M →ₜ+ M where
  toAddMonoidHom := DistribSMul.toAddMonoidHom M g
  continuous_toFun := continuous_const_smul g

/-- The contragredient action `(g • χ)(m) = χ(g⁻¹ • m)` on characters. -/
instance : SMul G (AddPontryaginDual M) where
  smul g χ := comap (smulHom g⁻¹) χ

/-- The contragredient action is `(g • χ)(m) = χ(g⁻¹ • m)`. -/
@[simp] lemma smul_apply (g : G) (χ : AddPontryaginDual M) (m : M) :
    (g • χ) m = χ (g⁻¹ • m) := rfl

/-- The contragredient action is an action by group automorphisms. -/
instance : DistribMulAction G (AddPontryaginDual M) where
  one_smul χ := ext fun m ↦ by rw [smul_apply, inv_one, one_smul]
  mul_smul g h χ := ext fun m ↦ by rw [smul_apply, smul_apply, smul_apply, mul_inv_rev, mul_smul]
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

/-- Each element of `G` acts continuously on the characters. -/
instance : ContinuousConstSMul G (AddPontryaginDual M) :=
  ⟨fun g ↦ (comap (smulHom g⁻¹)).continuous⟩

/-- The dual map of an equivariant homomorphism is equivariant. -/
lemma comap_smul {N : Type v} [AddCommGroup N] [TopologicalSpace N] [DistribMulAction G N]
    [ContinuousConstSMul G N] (f : M →ₜ+ N) (hf : ∀ (g : G) (m : M), f (g • m) = g • f m)
    (g : G) (χ : AddPontryaginDual N) : comap f (g • χ) = g • comap f χ :=
  ext fun m ↦ by simp [hf]

end Action

section Compact

variable {G : Type u} [Group G] [TopologicalSpace G] {M : Type v} [AddCommGroup M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [CompactSpace M] [DistribMulAction G M]
  [ContinuousSMul G M]

omit [IsTopologicalAddGroup M] [CompactSpace M] in
/-- A character of a compact group whose values on the image of a homomorphism all lie in the
open arc of length `π` around `1` vanishes on that image: the values on multiples of a point are
the powers of its value, and `1` is the only point of the circle all of whose powers lie in that
arc. -/
lemma apply_eq_one_of_forall_mem_centeredArc (χ : AddPontryaginDual M) (ψ : M →+ M)
    (h : ∀ m, χ (ψ m) ∈ Circle.centeredArc (Real.pi / 2)) (m : M) : χ (ψ m) = 1 :=
  Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two fun n _ ↦ by
    have hn := h (n • m)
    rwa [_root_.map_nsmul ψ n m, map_nsmul] at hn

/-- **The stabilizer of a character of a compact `G`-module is open.** For `g` near `1`, the
character `m ↦ χ(g • m - m)` takes values uniformly near `1` on the compact group `M` (tube
lemma), so it is trivial. -/
theorem isOpen_stabilizer [IsTopologicalGroup G] (χ : AddPontryaginDual M) :
    IsOpen (MulAction.stabilizer G χ : Set G) := by
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  set U := Circle.centeredArc (Real.pi / 2)
  have hU : IsOpen U := Circle.isOpen_centeredArc _
  have h1U : (1 : Circle) ∈ U := by
    rw [Circle.mem_centeredArc (by linarith [Real.pi_pos])]
    simp [Real.pi_pos]
  have hF : Continuous fun z : G × M ↦ χ (z.1 • z.2 - z.2) :=
    χ.continuous_apply.comp (continuous_smul.sub continuous_snd)
  have hev : ∀ᶠ g in 𝓝 (1 : G), ∀ m ∈ (Set.univ : Set M), χ (g • m - m) ∈ U :=
    isCompact_univ.eventually_forall_of_forall_eventually fun m _ ↦
      hF.continuousAt.eventually_mem (hU.mem_nhds (by simpa using h1U))
  have hinv : Tendsto (fun g : G ↦ g⁻¹) (𝓝 1) (𝓝 1) := by
    simpa using (continuous_inv.tendsto (1 : G))
  filter_upwards [hinv.eventually hev] with g hg
  rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
  ext m
  let ψ : M →+ M := DistribSMul.toAddMonoidHom M g⁻¹ - AddMonoidHom.id M
  have h := apply_eq_one_of_forall_mem_centeredArc χ ψ (fun m ↦ hg m (Set.mem_univ m)) m
  have hsplit : g⁻¹ • m = ψ m + m := by simp [ψ]
  rw [smul_apply, hsplit, map_add, h, one_mul]

end Compact

section Discrete

variable {G : Type u} [Group G] [TopologicalSpace G] {M : Type v} [AddCommGroup M]
  [TopologicalSpace M] [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M]

/-- **The contragredient action on the dual of a discrete `G`-module is jointly continuous.** The
dual carries the compact-open topology, so continuity reduces to continuity of
`((g, χ), m) ↦ χ(g⁻¹ • m)`, which holds because evaluation is continuous on the dual of a discrete
group. -/
theorem continuousSMul_of_discreteTopology [ContinuousInv G] :
    ContinuousSMul G (AddPontryaginDual M) := by
  refine ⟨?_⟩
  have h : Continuous fun p : G × AddPontryaginDual M ↦
      toContinuousMonoidHom (p.1 • p.2) := by
    refine ContinuousMonoidHom.continuous_of_continuous_uncurry _ ?_
    refine continuous_eval.comp
      ((continuous_toContinuousMonoidHom.comp (continuous_snd.comp continuous_fst)).prodMk ?_)
    exact continuous_ofAdd.comp
      (((continuous_inv.comp (continuous_fst.comp continuous_fst)).smul
        (continuous_toAdd.comp continuous_snd)))
  exact h

end Discrete

end AddPontryaginDual

section Functors

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

open AddPontryaginDual

/-- The character group of a compact `G`-module, as a discrete `G`-module. -/
def discreteDualObj (M : CompactGModule.{u, v} G) : ContinuousGModule.{u, v} G :=
  ofDistribMulAction (M := AddPontryaginDual M)
    (isContinuous_ofDistribMulAction_iff.mpr fun χ ↦ isOpen_stabilizer χ)

/-- The action of `G` on the character group of a compact `G`-module is the contragredient one. -/
lemma discreteDualObj_ρ_hom (M : CompactGModule.{u, v} G) (g : G)
    (χ : AddPontryaginDual M) :
    ((discreteDualObj G M).obj.obj.ρ g).asHom.hom χ = g • χ := rfl

/-- **Trivial duality, from compact to discrete.** The functor `M ↦ M^∧ = Hom_cont(M, S¹)` from
compact `G`-modules to discrete `G`-modules, with the contragredient action. -/
@[stacks 03VI "M ↦ Hom_cont(M, S¹) from compact G-modules to discrete G-modules"]
def discreteDual : (CompactGModule.{u, v} G)ᵒᵖ ⥤ ContinuousGModule.{u, v} G where
  obj M := discreteDualObj G M.unop
  map {M N} f := (gModuleHomEquiv G (discreteDualObj G M.unop) (discreteDualObj G N.unop)).symm
    ⟨(AddPontryaginDual.comap f.unop.hom).toAddMonoidHom,
      fun g χ ↦ comap_smul _ f.unop.map_smul g χ⟩
  map_id _ := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    exact ModuleCat.hom_ext (LinearMap.ext fun _ ↦ AddPontryaginDual.ext fun _ ↦ rfl)
  map_comp _ _ := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    exact ModuleCat.hom_ext (LinearMap.ext fun _ ↦ AddPontryaginDual.ext fun _ ↦ rfl)

/-- The functor `discreteDual` is additive. -/
instance : (discreteDual.{u, v} G).Additive where
  map_add {X Y f f'} := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    exact ModuleCat.hom_ext (LinearMap.ext fun χ ↦ AddPontryaginDual.ext (M := Y.unop) fun m ↦
      AddPontryaginDual.map_add (show AddPontryaginDual X.unop from χ) (f.unop.hom m)
        (f'.unop.hom m))

section CompactDual

attribute [local instance] carrierAction

/-- The action of `G` on the underlying group of a discrete `G`-module, as an action. -/
@[instance_reducible]
def carrierMulAction (M : ContinuousGModule.{u, v} G) : MulAction G M.obj.obj.V :=
  (carrierAction M).toMulAction

attribute [local instance] carrierMulAction

/-- The discrete topology on the underlying group of a discrete `G`-module. -/
@[instance_reducible]
def carrierTopology (M : ContinuousGModule.{u, v} G) : TopologicalSpace M.obj.obj.V := ⊥

attribute [local instance] carrierTopology

omit [IsTopologicalGroup G] in
variable {G} in
/-- The underlying group of a discrete `G`-module is discrete. -/
lemma discreteTopology_carrier (M : ContinuousGModule.{u, v} G) :
    DiscreteTopology M.obj.obj.V := ⟨rfl⟩

attribute [local instance] discreteTopology_carrier

variable {G} in
/-- The action of `G` on the underlying group of a discrete `G`-module is continuous. -/
lemma continuousSMul_carrier (M : ContinuousGModule.{u, v} G) :
    ContinuousSMul G M.obj.obj.V :=
  continuousSMul_iff_stabilizer_isOpen.mpr fun x ↦ isOpen_stabilizer ℤ G M x

attribute [local instance] continuousSMul_carrier

variable {G} in
/-- The contragredient action on the character group of a discrete `G`-module is continuous. -/
lemma continuousSMul_dual_carrier (M : ContinuousGModule.{u, v} G) :
    ContinuousSMul G (AddPontryaginDual M.obj.obj.V) :=
  continuousSMul_of_discreteTopology

attribute [local instance] continuousSMul_dual_carrier

/-- The character group of a discrete `G`-module, as a compact `G`-module. -/
def compactDualObj (M : ContinuousGModule.{u, v} G) : CompactGModule.{u, v} G :=
  CompactGModule.of (AddPontryaginDual M.obj.obj.V)

/-- A morphism of discrete `G`-modules, as a continuous homomorphism of the underlying discrete
groups. -/
def carrierHom {M N : ContinuousGModule.{u, v} G} (f : M ⟶ N) : M.obj.obj.V →ₜ+ N.obj.obj.V where
  toAddMonoidHom := f.hom.hom.hom.hom.toAddMonoidHom
  continuous_toFun := continuous_of_discreteTopology

omit [IsTopologicalGroup G] in
/-- A morphism of discrete `G`-modules is equivariant. -/
lemma carrierHom_smul {M N : ContinuousGModule.{u, v} G} (f : M ⟶ N) (g : G)
    (x : M.obj.obj.V) : carrierHom G f (g • x) = g • carrierHom G f x :=
  ConcreteCategory.congr_hom (f.hom.hom.comm g) x

/-- **Trivial duality, from discrete to compact.** The functor `M ↦ M^∧ = Hom(M, S¹)` from
discrete `G`-modules to compact `G`-modules, the character group carrying the compact-open
topology and the contragredient action. -/
@[stacks 03VI "M ↦ Hom_cont(M, S¹) from discrete G-modules to compact G-modules"]
def compactDual : (ContinuousGModule.{u, v} G)ᵒᵖ ⥤ CompactGModule.{u, v} G where
  obj M := compactDualObj G M.unop
  map f := CompactGModule.ofHom (AddPontryaginDual.comap (carrierHom G f.unop))
    (comap_smul _ (carrierHom_smul G f.unop))
  map_id _ := CompactGModule.hom_ext (ContinuousAddMonoidHom.ext fun _ ↦
    AddPontryaginDual.ext fun _ ↦ rfl)
  map_comp _ _ := CompactGModule.hom_ext (ContinuousAddMonoidHom.ext fun _ ↦
    AddPontryaginDual.ext fun _ ↦ rfl)

/-- The functor `compactDual` is additive. -/
instance : (compactDual.{u, v} G).Additive where
  map_add {X Y f f'} := CompactGModule.hom_ext (ContinuousAddMonoidHom.ext fun χ ↦
    AddPontryaginDual.ext (M := Y.unop.obj.obj.V) fun x ↦
      AddPontryaginDual.map_add (show AddPontryaginDual X.unop.obj.obj.V from χ)
        (f.unop.hom.hom.hom.hom x) (f'.unop.hom.hom.hom.hom x))

/-- The evaluation map `M → (M^∧)^∧` of a compact `G`-module, `m ↦ (χ ↦ χ(m))`. -/
def compactEvaluationHom (M : CompactGModule.{u, v} G) :
    M →ₜ+ compactDualObj G (discreteDualObj G M) where
  toFun m := mk (M := (discreteDualObj G M).obj.obj.V)
    (fun χ : AddPontryaginDual M ↦ χ m) rfl (fun _ _ ↦ rfl) continuous_of_discreteTopology
  map_zero' := AddPontryaginDual.ext fun χ ↦
    AddPontryaginDual.map_zero (show AddPontryaginDual M from χ)
  map_add' a b := AddPontryaginDual.ext fun χ ↦
    AddPontryaginDual.map_add (show AddPontryaginDual M from χ) a b
  continuous_toFun := by
    refine ContinuousMonoidHom.continuous_of_continuous_uncurry
      (fun m : M ↦ toContinuousMonoidHom (mk (M := (discreteDualObj G M).obj.obj.V)
        (fun χ : AddPontryaginDual M ↦ χ m) rfl (fun _ _ ↦ rfl)
        continuous_of_discreteTopology)) ?_
    rw [continuous_prod_of_discrete_right]
    intro x
    exact (Multiplicative.toAdd x : AddPontryaginDual M).continuous_apply

/-- **The evaluation map of a compact `G`-module into its double dual**, natural in the module.
Its bijectivity is Pontryagin duality for compact abelian groups. -/
def compactEvaluation : 𝟭 (CompactGModule.{u, v} G) ⟶ (discreteDual G).rightOp ⋙ compactDual G where
  app M := CompactGModule.ofHom (compactEvaluationHom G M) fun g m ↦
    AddPontryaginDual.ext fun χ ↦ by
      change (show AddPontryaginDual M from χ) (g • m) =
        (show AddPontryaginDual M from χ) (g⁻¹⁻¹ • m)
      rw [inv_inv]
  naturality _ _ _ := CompactGModule.hom_ext (ContinuousAddMonoidHom.ext fun _ ↦
    AddPontryaginDual.ext fun _ ↦ rfl)

/-- The evaluation map of a compact `G`-module sends `m` to evaluation at `m`. -/
@[simp] lemma compactEvaluation_app_apply (M : CompactGModule.{u, v} G) (m : M)
    (χ : AddPontryaginDual M) :
    (show AddPontryaginDual (discreteDualObj G M).obj.obj.V from
      ((compactEvaluation G).app M).hom m) χ = χ m := rfl

/-- The evaluation map `M → (M^∧)^∧` of a discrete `G`-module, `x ↦ (χ ↦ χ(x))`. -/
def discreteEvaluationHom (M : ContinuousGModule.{u, v} G) :
    M.obj.obj.V →+ AddPontryaginDual (compactDualObj G M) where
  toFun x := mk (fun χ : AddPontryaginDual M.obj.obj.V ↦ χ x) rfl (fun _ _ ↦ rfl)
    (continuous_eval_apply x)
  map_zero' := AddPontryaginDual.ext fun χ ↦ AddPontryaginDual.map_zero χ
  map_add' a b := AddPontryaginDual.ext fun χ ↦ AddPontryaginDual.map_add χ a b

/-- **The evaluation map of a discrete `G`-module into its double dual**, natural in the module.
Its bijectivity is Pontryagin duality for discrete abelian groups. -/
def discreteEvaluation :
    𝟭 (ContinuousGModule.{u, v} G) ⟶ (compactDual G).rightOp ⋙ discreteDual G where
  app M := (gModuleHomEquiv G M (discreteDualObj G (compactDualObj G M))).symm
    ⟨discreteEvaluationHom G M, fun g x ↦ AddPontryaginDual.ext fun χ ↦ by
      change (show AddPontryaginDual M.obj.obj.V from χ) (g • x) =
        (show AddPontryaginDual M.obj.obj.V from χ) (g⁻¹⁻¹ • x)
      rw [inv_inv]⟩
  naturality _ _ _ := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    exact ModuleCat.hom_ext (LinearMap.ext fun _ ↦ AddPontryaginDual.ext fun _ ↦ rfl)

end CompactDual

end Functors

end Stacks.GroupHomology
