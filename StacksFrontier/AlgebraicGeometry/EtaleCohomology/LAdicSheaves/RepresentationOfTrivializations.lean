module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.StalkMatrix

/-!
# The `ℤ_ℓ`-representation of a compatible system of trivialised finite `G`-modules

Let `G` be a topological group and let `Vₙ` (`n ≥ 0`) be finite discrete `G`-modules with
`G`-equivariant maps `Tₙ : Vₙ₊₁ → Vₙ`. Suppose given additive identifications
`cₙ : Vₙ ≃ (ℤ/ℓⁿ⁺¹ℤ)^r` under which `Tₙ` becomes reduction modulo `ℓⁿ⁺¹`. Then `g ∈ G` acts on
`(ℤ/ℓⁿ⁺¹ℤ)^r` by a matrix `Mₙ(g)` (an additive endomorphism of `(ℤ/ℓⁿ⁺¹ℤ)^r` is
`ℤ/ℓⁿ⁺¹ℤ`-linear), these matrices are compatible under reduction, and their inverse limit is a
matrix `ρ(g) ∈ M_r(ℤ_ℓ)`. This is the passage from the finite levels of a torsion-free lisse
ℓ-adic sheaf to its representation `ρ : π₁ → GL_r(ℤ_ℓ)` in the equivalence "lisse ℓ-adic sheaves =
finitely generated `ℤ_ℓ`-modules with continuous `π₁`-action" stated before
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main definitions

* `Stacks.EtaleCohomology.trivializationRepresentation`: the representation
  `ρ : G →* GL_r(ℤ_ℓ)`.
* `Stacks.EtaleCohomology.trivializationLevelIso`: the isomorphism of finite discrete
  `G`-modules `Vₙ ≅ (ℤ/ℓⁿ⁺¹ℤ)^r` with `G` acting through `ρ` modulo `ℓⁿ⁺¹`.

## Main results

* `Stacks.EtaleCohomology.continuous_trivializationRepresentation`: `ρ` is continuous.
* `Stacks.EtaleCohomology.trivializationLevelIso_hom_comp_levelAbelianReduction`: the
  isomorphisms carry `Tₙ` to reduction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.GroupCohomology

universe u

attribute [local instance] discreteForget₂AddCommGrpCat

open scoped Stacks.DiscreteModuleTopology Matrix

namespace Stacks.EtaleCohomology

variable {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}

/-! ### ℓ-adic integers from their reductions -/

/-- Two `ℓ`-adic matrices with the same reductions modulo every `ℓⁿ⁺¹` are equal. -/
public theorem matrix_eq_of_map_toZModPow_eq {A B : Matrix (Fin r) (Fin r) ℤ_[ℓ]}
    (h : ∀ n, A.map (PadicInt.toZModPow (n + 1)) = B.map (PadicInt.toZModPow (n + 1))) :
    A = B := by
  ext i j
  rw [← PadicInt.ext_of_toZModPow]
  intro n
  cases n with
  | zero =>
    have : Subsingleton (ZMod (ℓ ^ 0)) := ZMod.subsingleton_iff.2 (pow_zero ℓ)
    exact Subsingleton.elim _ _
  | succ n => exact congrFun (congrFun (h n) i) j

/-- A function to `ℤ_ℓ` all of whose reductions modulo `ℓⁿ⁺¹` are locally constant is
continuous. -/
public theorem continuous_of_isOpen_setOf_toZModPow_eq {X : Type*} [TopologicalSpace X]
    {f : X → ℤ_[ℓ]} (hf : ∀ n a, IsOpen {x | PadicInt.toZModPow (n + 1) (f x) = a}) :
    Continuous f := by
  have hℓ : (1 : ℝ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).one_lt
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hℓ)
  filter_upwards [(hf n (PadicInt.toZModPow (n + 1) (f x₀))).mem_nhds rfl] with x hx
  rw [dist_eq_norm]
  refine lt_of_le_of_lt ((toZModPow_eq_iff_norm_sub_le (n + 1) _ _).1 hx) (lt_of_le_of_lt ?_ hn)
  rw [zpow_neg, zpow_natCast, ← inv_pow]
  exact pow_le_pow_of_le_one (inv_nonneg.2 (by positivity)) (inv_le_one_of_one_le₀ hℓ.le)
    (Nat.le_succ n)

/-! ### The action on a finite discrete `G`-module -/

section Action

variable {G : Type (u + 1)} [Group G] [TopologicalSpace G]

/-- The set of `g` carrying `v` to `w` in a finite discrete `G`-module is open. -/
public theorem isOpen_setOf_finiteModule_act_eq
    (M : (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1} G).FullSubcategory)
    (v w : M.obj.obj.obj.V) : IsOpen {g : G | (M.obj.obj.obj.ρ g).hom v = w} := by
  have : DiscreteTopology ((forget₂ (Action AddCommGrpCat.{u + 1} G) TopCat).obj
      M.obj.obj.obj) := M.obj.property
  have h := continuous_prod_of_discrete_right.mp
    ((Action.isContinuous_def M.obj.obj.obj).mp M.obj.obj.property) v
  exact (isOpen_discrete ({w} : Set ((forget₂ (Action AddCommGrpCat.{u + 1} G) TopCat).obj
    M.obj.obj.obj))).preimage h

/-- The action of a product. -/
public theorem finiteModule_act_mul
    (M : (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1} G).FullSubcategory) (g h : G)
    (v : M.obj.obj.obj.V) :
    (M.obj.obj.obj.ρ (g * h)).hom v = (M.obj.obj.obj.ρ g).hom ((M.obj.obj.obj.ρ h).hom v) := by
  rw [map_mul]
  rfl

/-- The action of the unit. -/
public theorem finiteModule_act_one
    (M : (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1} G).FullSubcategory)
    (v : M.obj.obj.obj.V) : (M.obj.obj.obj.ρ 1).hom v = v := by
  rw [map_one]
  rfl

/-- A morphism of finite discrete `G`-modules is equivariant. -/
public theorem finiteModule_hom_act
    {M N : (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1} G).FullSubcategory} (f : M ⟶ N)
    (g : G) (v : M.obj.obj.obj.V) :
    f.hom.hom.hom.hom.hom ((M.obj.obj.obj.ρ g).hom v) =
      (N.obj.obj.obj.ρ g).hom (f.hom.hom.hom.hom.hom v) :=
  ConcreteCategory.congr_hom (f.hom.hom.hom.comm g) v

end Action

/-! ### The representation -/

section Representation

variable {G : Type (u + 1)} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (V : ℕ → (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1} G).FullSubcategory)
  (T : ∀ n, V (n + 1) ⟶ V n)
  (c : ∀ n, (V n).obj.obj.obj.V ≃+ (Fin r → ZMod (ℓ ^ (n + 1))))
  (hc : ∀ n (y : (V (n + 1)).obj.obj.obj.V),
    c n ((T n).hom.hom.hom.hom.hom y) = levelReduction (n + 1) (c (n + 1) y))

/-- The action of `g` on `Vₙ`, read on `(ℤ/ℓⁿ⁺¹ℤ)^r` through `cₙ`; it is `ℤ/ℓⁿ⁺¹ℤ`-linear, being
additive. -/
public def trivializationLinearMap (n : ℕ) (g : G) :
    (Fin r → ZMod (ℓ ^ (n + 1))) →ₗ[ZMod (ℓ ^ (n + 1))] (Fin r → ZMod (ℓ ^ (n + 1))) :=
  AddMonoidHom.toZModLinearMap (ℓ ^ (n + 1))
    ((c n).toAddMonoidHom.comp (((V n).obj.obj.obj.ρ g).hom.comp (c n).symm.toAddMonoidHom))

public theorem trivializationLinearMap_apply (n : ℕ) (g : G) (y : Fin r → ZMod (ℓ ^ (n + 1))) :
    trivializationLinearMap V c n g y = c n (((V n).obj.obj.obj.ρ g).hom ((c n).symm y)) :=
  rfl

public theorem trivializationLinearMap_mul (n : ℕ) (g h : G) :
    trivializationLinearMap V c n (g * h) =
      trivializationLinearMap V c n g ∘ₗ trivializationLinearMap V c n h := by
  refine LinearMap.ext fun y => ?_
  rw [LinearMap.comp_apply, trivializationLinearMap_apply, trivializationLinearMap_apply,
    trivializationLinearMap_apply, AddEquiv.symm_apply_apply, finiteModule_act_mul]

public theorem trivializationLinearMap_one (n : ℕ) :
    trivializationLinearMap V c n (1 : G) = LinearMap.id := by
  refine LinearMap.ext fun y => ?_
  rw [trivializationLinearMap_apply, finiteModule_act_one, AddEquiv.apply_symm_apply,
    LinearMap.id_apply]

include hc in
/-- The matrices of the action at consecutive levels are compatible under reduction. -/
public theorem levelRingHom_toMatrix'_trivializationLinearMap (n : ℕ) (g : G) (i j : Fin r) :
    levelRingHom (n + 1) (LinearMap.toMatrix' (trivializationLinearMap V c (n + 1) g) i j) =
      LinearMap.toMatrix' (trivializationLinearMap V c n g) i j := by
  rw [LinearMap.toMatrix'_apply, LinearMap.toMatrix'_apply, trivializationLinearMap_apply,
    trivializationLinearMap_apply, ← levelReduction_apply, ← hc, finiteModule_hom_act]
  have hT : (T n).hom.hom.hom.hom.hom ((c (n + 1)).symm (Pi.single j 1)) =
      (c n).symm (Pi.single j 1) := by
    apply (c n).injective
    rw [hc, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    funext k
    rw [levelReduction_apply, Pi.single_apply, Pi.single_apply]
    split_ifs <;> simp only [map_one, map_zero]
  rw [hT]

/-- **The matrix `ρ(g) ∈ M_r(ℤ_ℓ)`**: the inverse limit of the matrices of the action of `g` on the
levels. -/
public def trivializationMatrix (g : G) : Matrix (Fin r) (Fin r) ℤ_[ℓ] :=
  Matrix.of fun i j => (exists_toZModPow_eq
    (fun n => LinearMap.toMatrix' (trivializationLinearMap V c n g) i j)
    (fun n => levelRingHom_toMatrix'_trivializationLinearMap V T c hc n g i j)).choose

public theorem map_trivializationMatrix (n : ℕ) (g : G) :
    (trivializationMatrix V T c hc g).map (PadicInt.toZModPow (n + 1)) =
      LinearMap.toMatrix' (trivializationLinearMap V c n g) := by
  ext i j
  exact (exists_toZModPow_eq
    (fun n => LinearMap.toMatrix' (trivializationLinearMap V c n g) i j)
    (fun n => levelRingHom_toMatrix'_trivializationLinearMap V T c hc n g i j)).choose_spec n

/-- The reductions of `ρ(g)` act on the levels as `g`. -/
public theorem map_trivializationMatrix_mulVec (n : ℕ) (g : G) (v : (V n).obj.obj.obj.V) :
    (trivializationMatrix V T c hc g).map (PadicInt.toZModPow (n + 1)) *ᵥ c n v =
      c n (((V n).obj.obj.obj.ρ g).hom v) := by
  rw [map_trivializationMatrix, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix',
    trivializationLinearMap_apply, AddEquiv.symm_apply_apply]

/-- `g ↦ ρ(g)` as a monoid homomorphism to matrices. -/
public def trivializationMatrixHom : G →* Matrix (Fin r) (Fin r) ℤ_[ℓ] where
  toFun := trivializationMatrix V T c hc
  map_one' := matrix_eq_of_map_toZModPow_eq fun n => by
    rw [map_trivializationMatrix, trivializationLinearMap_one, LinearMap.toMatrix'_id,
      Matrix.map_one _ (map_zero _) (map_one _)]
  map_mul' g h := matrix_eq_of_map_toZModPow_eq fun n => by
    rw [map_trivializationMatrix, Matrix.map_mul, map_trivializationMatrix,
      map_trivializationMatrix, trivializationLinearMap_mul, LinearMap.toMatrix'_comp]

/-- **The representation `ρ : G →* GL_r(ℤ_ℓ)`** of a compatible system of trivialised finite
discrete `G`-modules. -/
public def trivializationRepresentation : G →* GL (Fin r) ℤ_[ℓ] :=
  (trivializationMatrixHom V T c hc).toHomUnits

public theorem trivializationRepresentation_val (g : G) :
    (trivializationRepresentation V T c hc g).val = trivializationMatrix V T c hc g :=
  rfl

/-- The entries of `ρ(g)` are continuous in `g`. -/
public theorem continuous_trivializationMatrix :
    Continuous (trivializationMatrix V T c hc) := by
  refine continuous_pi fun i => continuous_pi fun j =>
    continuous_of_isOpen_setOf_toZModPow_eq fun n a => ?_
  have : {g : G | PadicInt.toZModPow (n + 1) (trivializationMatrix V T c hc g i j) = a} =
      ⋃ v ∈ {v : (V n).obj.obj.obj.V | c n v i = a},
        {g : G | ((V n).obj.obj.obj.ρ g).hom
          ((c n).symm (Pi.single j 1)) = v} := by
    ext g
    have h := congrFun (congrFun (map_trivializationMatrix V T c hc n g) i) j
    simp only [Matrix.map_apply] at h
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop, h, LinearMap.toMatrix'_apply,
      trivializationLinearMap_apply]
    exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨v, hv, hg⟩ => hg ▸ hv⟩
  rw [this]
  exact isOpen_biUnion fun v _ => isOpen_setOf_finiteModule_act_eq (V n) _ v

/-- **`ρ` is continuous.** -/
public theorem continuous_trivializationRepresentation :
    Continuous (trivializationRepresentation V T c hc) := by
  refine Units.continuous_iff.2 ⟨continuous_trivializationMatrix V T c hc, ?_⟩
  have : (fun g => ((trivializationRepresentation V T c hc g)⁻¹ : GL (Fin r) ℤ_[ℓ]).val) =
      trivializationMatrix V T c hc ∘ fun g => g⁻¹ := by
    funext g
    rw [← map_inv]
    rfl
  rw [this]
  exact (continuous_trivializationMatrix V T c hc).comp continuous_inv

/-- The level representation of `ρ` at level `n + 1` is the action on `Vₙ`. -/
public theorem levelRepresentation_trivializationRepresentation (n : ℕ) (g : G)
    (v : (V n).obj.obj.obj.V) :
    levelRepresentation (trivializationRepresentation V T c hc) (n + 1) g (c n v) =
      c n (((V n).obj.obj.obj.ρ g).hom v) := by
  rw [levelRepresentation_apply, trivializationRepresentation_val,
    map_trivializationMatrix_mulVec]

/-- **The isomorphism of finite discrete `G`-modules `Vₙ ≅ (ℤ/ℓⁿ⁺¹ℤ)^r`**, with `G` acting on the
target through `ρ` modulo `ℓⁿ⁺¹`. -/
public def trivializationLevelIso (n : ℕ) :
    V n ≅ levelAbelian (trivializationRepresentation V T c hc)
      (continuous_trivializationRepresentation V T c hc) (n + 1) where
  hom := ObjectProperty.homMk (ObjectProperty.homMk (ObjectProperty.homMk
    { hom := AddCommGrpCat.ofHom
        { toFun := fun v => ULift.up (c n v)
          map_zero' := ULift.ext _ _ (map_zero _)
          map_add' := fun a b => ULift.ext _ _ (map_add _ _ _) }
      comm := fun g => by
        ext v
        exact ULift.ext _ _
          (levelRepresentation_trivializationRepresentation V T c hc n g v).symm }))
  inv := ObjectProperty.homMk (ObjectProperty.homMk (ObjectProperty.homMk
    { hom := AddCommGrpCat.ofHom
        { toFun := fun y => (c n).symm y.down
          map_zero' := map_zero _
          map_add' := fun a b => map_add _ _ _ }
      comm := fun g => by
        ext y
        change (c n).symm (levelRepresentation (trivializationRepresentation V T c hc) (n + 1) g
          y.down) = ((V n).obj.obj.obj.ρ g).hom ((c n).symm y.down)
        apply (c n).injective
        rw [AddEquiv.apply_symm_apply, ← levelRepresentation_trivializationRepresentation,
          AddEquiv.apply_symm_apply] }))
  hom_inv_id := by
    apply finiteContinuousAbelianHom_ext
    ext v
    exact (c n).symm_apply_apply v
  inv_hom_id := by
    apply finiteContinuousAbelianHom_ext
    ext y
    exact ULift.ext _ _ ((c n).apply_symm_apply y.down)

public theorem trivializationLevelIso_hom_apply (n : ℕ) (v : (V n).obj.obj.obj.V) :
    (trivializationLevelIso V T c hc n).hom.hom.hom.hom.hom.hom v = ULift.up (c n v) :=
  rfl

/-- **The isomorphisms carry the transitions to reduction.** -/
public theorem trivializationLevelIso_hom_comp_levelAbelianReduction (n : ℕ) :
    (trivializationLevelIso V T c hc (n + 1)).hom ≫
        levelAbelianReduction (trivializationRepresentation V T c hc)
          (continuous_trivializationRepresentation V T c hc) (n + 1) =
      T n ≫ (trivializationLevelIso V T c hc n).hom := by
  apply finiteContinuousAbelianHom_ext
  ext y
  exact ULift.ext _ _ (hc n y).symm

end Representation

end Stacks.EtaleCohomology

end
