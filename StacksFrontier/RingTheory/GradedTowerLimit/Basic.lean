module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.DirectSum.Algebra
public import Mathlib.Algebra.DirectSum.Internal
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# The graded inverse limit of a tower of graded algebras

Let `R₀ ← R₁ ← R₂ ← ⋯` be an inverse system of commutative rings, and let `A₀ ← A₁ ← A₂ ← ⋯`
be a compatible tower of graded algebras, `Aₙ` a graded `Rₙ`-algebra and `Aₙ₊₁ → Aₙ` a graded
ring map over `Rₙ₊₁ → Rₙ`. The *graded inverse limit* is the graded algebra over `R = lim Rₙ`
whose degree-`d` piece is the inverse limit `lim (Aₙ)_d` of the degree-`d` pieces; it is the
direct sum of these limits, not the inverse limit of the rings `Aₙ`.

This is the algebraic construction in the proof of Stacks Tag 0D4T (strong formal effectiveness
for polarized schemes), where `Aₙ = Rₙ ⊕ ⨁_{d ≥ d₀} H⁰(Xₙ, ℒₙ^{⊗ d})`.

## Main definitions

* `Stacks.GradedTowerLimit.GradedTower`: a tower of graded algebras over an inverse system of
  rings.
* `Stacks.GradedTowerLimit.GradedTower.IsAdmissible`: the hypotheses of Stacks 0D4T on such a
  tower — surjective transition maps of rings with locally nilpotent kernels, finite projective
  homogeneous pieces, degree-zero pieces equal to the base rings, homogeneous pieces compatible
  with base change, and a finitely presented bottom algebra.
* `Stacks.GradedTowerLimit.GradedTower.piece`: the degree-`d` piece `lim (Aₙ)_d`, realized as the
  compatible families of degree-`d` elements.
* `Stacks.GradedTowerLimit.GradedTower.Lim`: the graded inverse limit, the direct sum of the
  pieces, with its grading `limGrading`.
* `Stacks.GradedTowerLimit.GradedTower.proj`: the projections `lim → Aₙ`.

## Implementation notes

The base ring `limit Rg` acts on `Aₙ` through the limit projection `limit Rg → Rₙ`. These
actions, and the action of `Rₙ₊₁` on `Rₙ` through the transition map, are scoped instances of
the namespace `Stacks.GradedTowerLimit`: they are definitional unfoldings of
`RingHom.toAlgebra`, so a consumer installing `(limit.π Rg (op n)).hom.toAlgebra` by hand gets
the same structure.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct DirectSum

universe u

namespace Stacks.GradedTowerLimit

variable (Rg : ℕᵒᵖ ⥤ CommRingCat.{u})

/-- The transition map `Rₙ₊₁ → Rₙ` of the inverse system of rings. -/
abbrev tr (n : ℕ) : Rg.obj (op (n + 1)) ⟶ Rg.obj (op n) :=
  Rg.map (homOfLE (Nat.le_succ n)).op

/-- The limit projection `lim Rg → Rₙ` makes `Rₙ` an algebra over the limit. -/
scoped instance limitAlgebra (n : ℕ) : Algebra (limit Rg : CommRingCat.{u}) (Rg.obj (op n)) :=
  (limit.π Rg (op n)).hom.toAlgebra

/-- The transition map `Rₙ₊₁ → Rₙ` makes `Rₙ` an `Rₙ₊₁`-algebra. -/
scoped instance trAlgebra (n : ℕ) : Algebra (Rg.obj (op (n + 1))) (Rg.obj (op n)) :=
  (tr Rg n).hom.toAlgebra

/-- The algebra map `lim Rg → Rₙ` is the limit projection. -/
theorem limitAlgebra_algebraMap (n : ℕ) :
    algebraMap (limit Rg : CommRingCat.{u}) (Rg.obj (op n)) = (limit.π Rg (op n)).hom := rfl

/-- The algebra map `Rₙ₊₁ → Rₙ` is the transition map. -/
theorem trAlgebra_algebraMap (n : ℕ) :
    algebraMap (Rg.obj (op (n + 1))) (Rg.obj (op n)) = (tr Rg n).hom := rfl

/-- The limit projections are compatible with the transition maps. -/
theorem tr_limit_π (n : ℕ) (r : (limit Rg : CommRingCat.{u})) :
    (tr Rg n).hom ((limit.π Rg (op (n + 1))).hom r) = (limit.π Rg (op n)).hom r := by
  rw [← CommRingCat.comp_apply, limit.w]

/-! ### Families compatible along consecutive maps -/

/-- A family of morphisms into an `ℕᵒᵖ`-indexed diagram compatible with the consecutive
transition maps is compatible with every transition map. -/
theorem comp_map_eq_of_succ {C : Type*} [Category C] {F : ℕᵒᵖ ⥤ C} {X : C}
    (g : ∀ n : ℕ, X ⟶ F.obj (op n))
    (hg : ∀ n : ℕ, g (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op = g n)
    {i j : ℕᵒᵖ} (f : i ⟶ j) : g i.unop ≫ F.map f = g j.unop := by
  obtain ⟨m⟩ := i
  obtain ⟨n⟩ := j
  have hnm : n ≤ m := f.unop.le
  obtain rfl : f = (homOfLE hnm).op := Subsingleton.elim _ _
  induction m, hnm using Nat.le_induction with
  | base => simp
  | succ m hnm ih =>
    have : (homOfLE (hnm.trans (Nat.le_succ m))).op =
        (homOfLE (Nat.le_succ m)).op ≫ (homOfLE hnm).op := Subsingleton.elim _ _
    simp only [unop_op] at ih ⊢
    rw [this, F.map_comp, ← Category.assoc, hg, ih]

/-- A family of elements of an `ℕᵒᵖ`-indexed diagram of types compatible with the consecutive
transition maps is a section. -/
theorem mem_sections_of_succ {F : ℕᵒᵖ ⥤ Type*} (x : ∀ n : ℕ, F.obj (op n))
    (hx : ∀ n : ℕ, F.map (homOfLE (Nat.le_succ n)).op (x (n + 1)) = x n) :
    (fun i : ℕᵒᵖ => x i.unop) ∈ F.sections := by
  rintro ⟨m⟩ ⟨n⟩ f
  have hnm : n ≤ m := f.unop.le
  obtain rfl : f = (homOfLE hnm).op := Subsingleton.elim _ _
  induction m, hnm using Nat.le_induction with
  | base => simp
  | succ m hnm ih =>
    have : (homOfLE (hnm.trans (Nat.le_succ m))).op =
        (homOfLE (Nat.le_succ m)).op ≫ (homOfLE hnm).op := Subsingleton.elim _ _
    simp only [unop_op] at ih ⊢
    rw [this, F.map_comp, types_comp_apply, hx, ih]

/-- An element of the limit of rings with prescribed images, from a family compatible with the
consecutive transition maps. -/
theorem exists_limit_eq (x : ∀ n : ℕ, Rg.obj (op n))
    (hx : ∀ n : ℕ, (tr Rg n).hom (x (n + 1)) = x n) :
    ∃ r : (limit Rg : CommRingCat.{u}), ∀ n, (limit.π Rg (op n)).hom r = x n := by
  let e := Types.isLimitEquivSections
    (isLimitOfPreserves (forget CommRingCat.{u}) (limit.isLimit Rg))
  let s : (Rg ⋙ forget CommRingCat.{u}).sections :=
    ⟨fun i => x i.unop, mem_sections_of_succ (F := Rg ⋙ forget CommRingCat.{u}) x hx⟩
  refine ⟨e.symm s, fun n => ?_⟩
  have h := Types.isLimitEquivSections_symm_apply
    (isLimitOfPreserves (forget CommRingCat.{u}) (limit.isLimit Rg)) s (op n)
  simpa [e, s] using h

/-! ### Towers of graded algebras -/

/-- **A tower of graded algebras** over the inverse system of rings `Rg`: for each `n` a graded
`Rₙ`-algebra `Aₙ`, and graded ring maps `ρₙ : Aₙ₊₁ → Aₙ` over the transition maps
`Rₙ₊₁ → Rₙ`. -/
structure GradedTower where
  /-- The algebras of the tower. -/
  A : ℕ → Type u
  /-- Each algebra is a commutative ring. -/
  [commRing : ∀ n, CommRing (A n)]
  /-- Each algebra is an algebra over the corresponding ring. -/
  [algebra : ∀ n, Algebra (Rg.obj (op n)) (A n)]
  /-- The gradings. -/
  𝒜 : ∀ n, ℕ → Submodule (Rg.obj (op n)) (A n)
  /-- Each grading makes the algebra a graded algebra. -/
  [gradedAlgebra : ∀ n, GradedAlgebra (𝒜 n)]
  /-- The transition maps of the tower. -/
  ρ : ∀ n, A (n + 1) →+* A n
  /-- The transition maps preserve degrees. -/
  ρ_mem : ∀ (n d : ℕ) {x : A (n + 1)}, x ∈ 𝒜 (n + 1) d → ρ n x ∈ 𝒜 n d
  /-- The transition maps lie over the transition maps of the rings. -/
  ρ_algebraMap : ∀ (n : ℕ) (r : Rg.obj (op (n + 1))),
    ρ n (algebraMap (Rg.obj (op (n + 1))) (A (n + 1)) r) =
      algebraMap (Rg.obj (op n)) (A n) ((tr Rg n).hom r)

namespace GradedTower

attribute [instance] commRing algebra gradedAlgebra

variable {Rg} (T : GradedTower Rg)

/-- `Aₙ` as an algebra over the limit ring, through the limit projection. -/
scoped instance limitAlgebraA (n : ℕ) : Algebra (limit Rg : CommRingCat.{u}) (T.A n) :=
  ((algebraMap (Rg.obj (op n)) (T.A n)).comp (limit.π Rg (op n)).hom).toAlgebra

/-- `Aₙ` as an algebra over `Rₙ₊₁`, through the transition map. -/
scoped instance trAlgebraA (n : ℕ) : Algebra (Rg.obj (op (n + 1))) (T.A n) :=
  ((algebraMap (Rg.obj (op n)) (T.A n)).comp (tr Rg n).hom).toAlgebra

/-- The algebra map `lim Rg → Aₙ` is the composite of the limit projection `lim Rg → Rₙ` with
the algebra map `Rₙ → Aₙ`. -/
theorem limitAlgebraA_algebraMap (n : ℕ) (r : (limit Rg : CommRingCat.{u})) :
    algebraMap (limit Rg : CommRingCat.{u}) (T.A n) r =
      algebraMap (Rg.obj (op n)) (T.A n) ((limit.π Rg (op n)).hom r) := rfl

/-- The actions of `lim Rg`, `Rₙ` and `Aₙ` form a scalar tower. -/
instance isScalarTower_limit (n : ℕ) :
    IsScalarTower (limit Rg : CommRingCat.{u}) (Rg.obj (op n)) (T.A n) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The actions of `Rₙ₊₁`, `Rₙ` and `Aₙ` form a scalar tower. -/
instance isScalarTower_tr (n : ℕ) :
    IsScalarTower (Rg.obj (op (n + 1))) (Rg.obj (op n)) (T.A n) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The degree-`d` transition map `(Aₙ₊₁)_d → (Aₙ)_d`, linear over `Rₙ₊₁`. -/
def trPiece (n d : ℕ) : T.𝒜 (n + 1) d →ₗ[Rg.obj (op (n + 1))] T.𝒜 n d where
  toFun x := ⟨T.ρ n x, T.ρ_mem n d x.2⟩
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' r x := Subtype.ext <| by
    change T.ρ n (r • (x : T.A (n + 1))) = r • T.ρ n x
    rw [Algebra.smul_def, map_mul, T.ρ_algebraMap, Algebra.smul_def]
    rfl

/-- The degree-`d` transition map is the restriction of `ρₙ`. -/
@[simp]
theorem coe_trPiece (n d : ℕ) (x : T.𝒜 (n + 1) d) : (T.trPiece n d x : T.A n) = T.ρ n x := rfl

/-- **The base-change map** `Rₙ ⊗_{Rₙ₊₁} (Aₙ₊₁)_d → (Aₙ)_d`, `r ⊗ x ↦ r • ρₙ(x)`. -/
def baseChangeMap (n d : ℕ) :
    Rg.obj (op n) ⊗[Rg.obj (op (n + 1))] T.𝒜 (n + 1) d →ₗ[Rg.obj (op n)] T.𝒜 n d :=
  (T.trPiece n d).liftBaseChange (Rg.obj (op n))

/-- The base-change map sends `r ⊗ x` to `r • ρₙ(x)`. -/
@[simp]
theorem baseChangeMap_tmul (n d : ℕ) (r : Rg.obj (op n)) (x : T.𝒜 (n + 1) d) :
    T.baseChangeMap n d (r ⊗ₜ x) = r • T.trPiece n d x :=
  LinearMap.liftBaseChange_tmul _ _ _ _

/-- **The hypotheses of Stacks 0D4T on a tower of graded algebras.** The transition maps of the
rings are surjective with locally nilpotent kernels; every homogeneous piece is a finite
projective module; the degree-zero pieces are the base rings; the homogeneous pieces are
compatible with base change; and the bottom algebra is finitely presented. -/
structure IsAdmissible : Prop where
  /-- The transition maps `Rₙ₊₁ → Rₙ` are surjective. -/
  surjective : ∀ n : ℕ, Function.Surjective (tr Rg n).hom
  /-- The kernels of the transition maps `Rₙ₊₁ → Rₙ` consist of nilpotent elements. -/
  ker_le_nilradical : ∀ n : ℕ, RingHom.ker (tr Rg n).hom ≤ nilradical (Rg.obj (op (n + 1)))
  /-- Every homogeneous piece `(Aₙ)_d` is a finite `Rₙ`-module. -/
  finite : ∀ n d : ℕ, Module.Finite (Rg.obj (op n)) (T.𝒜 n d)
  /-- Every homogeneous piece `(Aₙ)_d` is a projective `Rₙ`-module. -/
  projective : ∀ n d : ℕ, Module.Projective (Rg.obj (op n)) (T.𝒜 n d)
  /-- The algebra map `Rₙ → (Aₙ)_0` is bijective. -/
  zero_bijective : ∀ n : ℕ, Function.Bijective fun r : Rg.obj (op n) =>
    (⟨algebraMap (Rg.obj (op n)) (T.A n) r, SetLike.algebraMap_mem_graded (T.𝒜 n) r⟩ :
      T.𝒜 n 0)
  /-- The base-change maps `Rₙ ⊗_{Rₙ₊₁} (Aₙ₊₁)_d → (Aₙ)_d` are bijective. -/
  baseChange_bijective : ∀ n d : ℕ, Function.Bijective (T.baseChangeMap n d)
  /-- The algebra `A₀` is finitely presented over `R₀`. -/
  finitePresentation : Algebra.FinitePresentation (Rg.obj (op 0)) (T.A 0)

/-! ### The pieces of the limit -/

/-- **The degree-`d` piece of the graded inverse limit**: the families of degree-`d` elements
compatible with the transition maps. -/
def piece (d : ℕ) : Submodule (limit Rg : CommRingCat.{u}) (∀ n, T.A n) where
  carrier := {x | ∀ n, x n ∈ T.𝒜 n d ∧ T.ρ n (x (n + 1)) = x n}
  add_mem' {x y} hx hy n := ⟨add_mem (hx n).1 (hy n).1, by
    simp only [Pi.add_apply, map_add, (hx n).2, (hy n).2]⟩
  zero_mem' n := ⟨zero_mem _, by simp⟩
  smul_mem' r x hx n := by
    refine ⟨?_, ?_⟩
    · change r • x n ∈ T.𝒜 n d
      rw [← algebraMap_smul (Rg.obj (op n))]
      exact Submodule.smul_mem _ _ (hx n).1
    · change T.ρ n (r • x (n + 1)) = r • x n
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, limitAlgebraA_algebraMap, T.ρ_algebraMap,
        tr_limit_π, (hx n).2, limitAlgebraA_algebraMap]

/-- A family lies in the degree-`d` piece iff each term has degree `d` and the family is
compatible with the transition maps. -/
theorem mem_piece {d : ℕ} {x : ∀ n, T.A n} :
    x ∈ T.piece d ↔ ∀ n, x n ∈ T.𝒜 n d ∧ T.ρ n (x (n + 1)) = x n := Iff.rfl

/-- The pieces `lim (Aₙ)_d` form a graded monoid in `∏ₙ Aₙ`. -/
instance gradedMonoid_piece : SetLike.GradedMonoid T.piece where
  one_mem n := ⟨SetLike.one_mem_graded _, map_one _⟩
  mul_mem i j x y hx hy n := ⟨SetLike.mul_mem_graded (hx n).1 (hy n).1, by
    simp only [Pi.mul_apply, map_mul, (hx n).2, (hy n).2]⟩

/-- **The graded inverse limit**: the direct sum of the pieces `lim (Aₙ)_d`. -/
abbrev Lim : Type u := ⨁ d : ℕ, T.piece d

/-- The graded inverse limit is a commutative ring. -/
instance : CommRing T.Lim := inferInstance

/-- The graded inverse limit is an algebra over the limit ring. -/
instance : Algebra (limit Rg : CommRingCat.{u}) T.Lim := inferInstance

/-- The grading of the graded inverse limit: the image of the degree-`d` summand. -/
abbrev limGrading (d : ℕ) : Submodule (limit Rg : CommRingCat.{u}) T.Lim :=
  LinearMap.range (DirectSum.lof (limit Rg : CommRingCat.{u}) ℕ (fun d => T.piece d) d)

/-- The image of an element of the degree-`d` piece lies in the degree-`d` part of the limit. -/
theorem lof_mem_limGrading {d : ℕ} (y : T.piece d) :
    DirectSum.of (fun d => T.piece d) d y ∈ T.limGrading d := ⟨y, rfl⟩

/-- The graded inverse limit is the direct sum of its homogeneous parts. -/
@[instance_reducible]
noncomputable def decomposition : DirectSum.Decomposition T.limGrading := by
  let e : T.Lim →+ ⨁ d : ℕ, T.limGrading d :=
    DirectSum.toAddMonoid fun d =>
      (DirectSum.of (fun d => T.limGrading d) d).comp
        (DirectSum.lof (limit Rg : CommRingCat.{u}) ℕ (fun d => T.piece d)
          d).rangeRestrict.toAddMonoidHom
  refine DirectSum.Decomposition.ofAddHom _ e ?_ ?_
  · apply DirectSum.addHom_ext
    intro d x
    simp [e]
    rfl
  · apply DirectSum.addHom_ext
    intro d y
    obtain ⟨x, hx⟩ := y
    obtain ⟨a, rfl⟩ := hx
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, DirectSum.coeAddMonoidHom_of,
      AddMonoidHom.id_apply, e]
    exact (DirectSum.toAddMonoid_of (β := fun d => T.piece d) _ d a).trans rfl

/-- **The graded inverse limit is a graded algebra over the limit ring.** -/
noncomputable instance gradedAlgebra_limGrading : GradedAlgebra T.limGrading where
  toDecomposition := T.decomposition
  one_mem := ⟨_, (DirectSum.one_def _).symm⟩
  mul_mem := by
    rintro i j a b ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨_, (DirectSum.of_mul_of (A := fun d => T.piece d) a b).symm⟩

/-- The degree-`d` part of the limit is the degree-`d` piece. -/
noncomputable def limGradingEquiv (d : ℕ) :
    T.piece d ≃ₗ[(limit Rg : CommRingCat.{u})] T.limGrading d :=
  LinearEquiv.ofInjective _ (DirectSum.of_injective (β := fun d => T.piece d) d)

/-- The equivalence `limGradingEquiv` is the inclusion of the degree-`d` summand. -/
@[simp]
theorem coe_limGradingEquiv (d : ℕ) (y : T.piece d) :
    (T.limGradingEquiv d y : T.Lim) = DirectSum.of (fun d => T.piece d) d y := rfl

/-! ### The projections -/

/-- **The projection** `lim → Aₙ` of the graded inverse limit. -/
def proj (n : ℕ) : T.Lim →+* T.A n :=
  (Pi.evalRingHom (fun n => T.A n) n).comp (DirectSum.coeRingHom T.piece)

/-- The projection `lim → Aₙ` sends a compatible family in a single degree to its `n`-th term. -/
@[simp]
theorem proj_of (n d : ℕ) (y : T.piece d) :
    T.proj n (DirectSum.of (fun d => T.piece d) d y) = (y : ∀ n, T.A n) n := by
  simp [proj, DirectSum.coeRingHom_of]

/-- The projection `lim → Aₙ` preserves degrees. -/
theorem proj_mem (n : ℕ) {d : ℕ} {x : T.Lim} (hx : x ∈ T.limGrading d) :
    T.proj n x ∈ T.𝒜 n d := by
  obtain ⟨y, rfl⟩ := hx
  show T.proj n (DirectSum.of (fun d => T.piece d) d y) ∈ _
  rw [proj_of]
  exact (y.2 n).1

/-- The projections are compatible with the transition maps of the tower. -/
theorem ρ_proj (n : ℕ) (x : T.Lim) : T.ρ n (T.proj (n + 1) x) = T.proj n x := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of d y => rw [proj_of, proj_of]; exact (y.2 n).2
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

/-- The projections lie over the limit projections of the rings. -/
theorem proj_algebraMap (n : ℕ) (r : (limit Rg : CommRingCat.{u})) :
    T.proj n (algebraMap (limit Rg : CommRingCat.{u}) T.Lim r) =
      algebraMap (Rg.obj (op n)) (T.A n) ((limit.π Rg (op n)).hom r) := by
  rw [DirectSum.algebraMap_apply, proj_of]
  rfl

/-- The projection as a homomorphism of algebras over the limit ring. -/
def projAlgHom (n : ℕ) : T.Lim →ₐ[(limit Rg : CommRingCat.{u})] T.A n where
  __ := T.proj n
  commutes' r := T.proj_algebraMap n r

/-- The algebra homomorphism `projAlgHom` agrees with the projection `proj`. -/
@[simp]
theorem projAlgHom_apply (n : ℕ) (x : T.Lim) : T.projAlgHom n x = T.proj n x := rfl

end GradedTower

end Stacks.GradedTowerLimit
