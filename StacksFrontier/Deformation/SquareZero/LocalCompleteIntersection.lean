module

public import StacksFrontier.Deformation.SquareZero.Problem
public import StacksFrontier.RingTheory.CompleteIntersection.RingMap.Defs
public import StacksFrontier.RingTheory.Regular.Ideal
public import StacksFrontier.RingTheory.Regular.Quasiregular
public import StacksFrontier.RingTheory.Koszul.Descent
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.Algebra.TrivSqZeroExt.Ideal
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Ideal.Cotangent

/-!
# Solving the square-zero extension problem for a local complete intersection

Let `A' → A` be a surjection of commutative rings with square-zero kernel `I`, let `A → B` be a
ring map, let `N` be a `B`-module and let `c : I → N` be `A`-linear.  This file proves that the
resulting square-zero extension problem always has a solution when `A → B` is a local complete
intersection ring map.

## Main results

* `Stacks.Deformation.nonempty_compatibleExtension_of_isLocalCompleteIntersection`: **Stacks
  08S6**, a local complete intersection ring map `A → B` admits a solution to the extension
  problem of Stacks 08S4.

## Implementation notes

Write `B = A[x₁, …, x_n]/J` with `J` Koszul-regular, put `R = A'[x₁, …, x_n]` and let
`q : R → B` be the composite of the reduction `π : R → A[x₁, …, x_n]` with the presentation.
The whole construction is reduced to producing one `R`-linear map `Φ : ker q → N` sending
`i ∈ I ⊆ R` to `c i`; given such a `Φ`, the set
`{(z, -Φ z) : z ∈ ker q} ⊆ R ⋉ N` is an ideal of the trivial square-zero extension, and the
quotient `(R ⋉ N)/W` is a solution.  This replaces the splitting-plus-pushout argument of the
source: `Φ` is automatically zero on `(ker q)²`, so no separate conormal quotient is needed on
the construction side, and no pushout along `I ⊗_A B → N` is required because `Φ` need not be
surjective.

The map `Φ` is built in two steps.  On `ker π = I·R` it is the map corresponding to `c` under
`I·R ≅ R ⊗_{A'} I`, the isomorphism supplied by freeness — hence flatness — of `R` over `A'`.
Extending it over `ker q` is where the local complete intersection hypothesis enters, twice.
The conormal module `ker q/(ker q)²` has the image of `I·R` as a submodule, and the quotient
by that submodule is the conormal module `J/J²` of the presentation; the map out of the
submodule is well defined because `I·R ∩ (ker q)² = (I·R)·(ker q)` (Stacks 07CX, applied to
`I·R ⊆ ker q` through the isomorphism `R/I·R ≅ A[x₁, …, x_n]`, under which `ker q/I·R` becomes
the `H₁`-regular ideal `J`), and it extends because `J/J²` is a finite projective
`B`-module (Stacks 08RK, since a Koszul-regular ideal is quasi-regular).

Both conormal modules are handled as modules over `A[x₁, …, x_n]/J`: the one of `ker q` carries
that action because it is annihilated by `ker π` as well as by `ker q`, so the actions of `R`
factor through `R/ker π ≅ A[x₁, …, x_n]` and then through `J`.  That avoids transporting
projectivity along a ring isomorphism.

The universe of the solution ring is `max u₁ u₂ u₃ u₄`; the construction itself produces a ring
in `Type (max u₁ u₄)`, and the last step moves it up with `ULift`.

## References

* [Stacks Project, Tag 08S6](https://stacks.math.columbia.edu/tag/08S6)
* [Stacks Project, Tag 08S4](https://stacks.math.columbia.edu/tag/08S4)
* [Stacks Project, Tag 07CX](https://stacks.math.columbia.edu/tag/07CX)
* [Stacks Project, Tag 08RK](https://stacks.math.columbia.edu/tag/08RK)
-/

@[expose] public section

universe u₁ u₂ u₃ u₄ w

namespace Stacks.Deformation

open TrivSqZeroExt

/-- The canonical ring isomorphism `Rᵐᵒᵖ → R` of a commutative ring with its opposite. -/
private def unopHom (R : Type w) [CommRing R] : Rᵐᵒᵖ →+* R where
  toFun := MulOpposite.unop
  map_one' := rfl
  map_mul' _ _ := mul_comm _ _
  map_zero' := rfl
  map_add' _ _ := rfl

/-- A module over a commutative ring is a module over the opposite ring. -/
@[instance_reducible]
private def opModule (R : Type w) [CommRing R] (N : Type u₄) [AddCommGroup N] [Module R N] :
    Module Rᵐᵒᵖ N := Module.compHom N (unopHom R)

attribute [local instance] opModule

private theorem centralOp (R : Type w) [CommRing R] (N : Type u₄) [AddCommGroup N]
    [Module R N] : IsCentralScalar R N := ⟨fun _ _ => rfl⟩

attribute [local instance] centralOp

section Gluing

variable (S : SquareZeroExtensionProblem.{u₁, u₂, u₃, u₄})
    {R : Type w} [CommRing R] [Module R S.N]
    (q : R →+* S.B) (Φ : (RingHom.ker q) →ₗ[R] S.N)

/-- The ideal of `R ⋉ N` whose quotient is the solution to the extension problem
determined by `Φ`. -/
private def gluingIdeal (hsmul : ∀ (r : R) (x : S.N), r • x = q r • x) :
    Ideal (TrivSqZeroExt R S.N) where
  carrier := Set.range fun z : RingHom.ker q =>
    (TrivSqZeroExt.inl (z : R) - TrivSqZeroExt.inr (Φ z) : TrivSqZeroExt R S.N)
  add_mem' := by
    rintro _ _ ⟨z, rfl⟩ ⟨y, rfl⟩
    refine ⟨z + y, ?_⟩
    apply TrivSqZeroExt.ext
    · simp
    · simp [map_add]
      abel
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro c _ ⟨z, rfl⟩
    refine ⟨c.fst • z, ?_⟩
    have hz : q (z : R) = 0 := z.2
    rw [smul_eq_mul]
    apply TrivSqZeroExt.ext
    · simp [TrivSqZeroExt.fst_mul]
    · simp only [TrivSqZeroExt.snd_mul, snd_sub, snd_inl, snd_inr, fst_sub, fst_inl, fst_inr,
        sub_zero, zero_sub, smul_neg, map_smul, Submodule.coe_smul_of_tower]
      rw [op_smul_eq_smul, hsmul (z : R) c.snd, hz, zero_smul, add_zero]


/-- The ring homomorphism `R ⋉ N → R` projecting to the first coordinate. -/
private def fstRingHom (R : Type w) [CommRing R] (N : Type u₄) [AddCommGroup N] [Module R N] :
    TrivSqZeroExt R N →+* R where
  toFun := TrivSqZeroExt.fst
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Elements of the kernel `I` of `A' → A` map to zero in `A`. -/
private theorem algebraMap_eq_zero_of_mem_I (S : SquareZeroExtensionProblem.{u₁, u₂, u₃, u₄})
    (i : S.I) : algebraMap S.A' S.A (i : S.A') = 0 := by
  rw [← RingHom.mem_ker, S.kernel_eq]
  exact i.2

/-- **Existence of a solution from a functional on the presentation ideal.**
If `q : R → B` is a surjective ring map and `Φ` is an `R`-linear map from `ker q` to `N`
inducing the prescribed map `c` on `I`, then the extension problem has a solution. -/
private theorem nonempty_of_functional
    (S : SquareZeroExtensionProblem.{u₁, u₂, u₃, u₄})
    {R : Type w} [CommRing R] [Module R S.N]
    (ι : S.A' →+* R) (q : R →+* S.B)
    (hq : Function.Surjective q)
    (hsmul : ∀ (r : R) (x : S.N), r • x = q r • x)
    (hιq : ∀ a : S.A', q (ι a) = algebraMap S.A' S.B a)
    (Φ : (RingHom.ker q) →ₗ[R] S.N)
    (hΦ : ∀ (i : S.I) (hi : ι i ∈ RingHom.ker q), Φ ⟨ι i, hi⟩ = S.c i) :
    Nonempty (S.CompatibleExtension.{max w u₄}) := by
  classical
  set W : Ideal (TrivSqZeroExt R S.N) := gluingIdeal S q Φ hsmul
  have hWmem : ∀ z : RingHom.ker q,
      (TrivSqZeroExt.inl (z : R) - TrivSqZeroExt.inr (Φ z) : (TrivSqZeroExt R S.N)) ∈ W :=
    fun z => ⟨z, rfl⟩
  have hWiff : ∀ v : (TrivSqZeroExt R S.N), v ∈ W ↔ ∃ z : RingHom.ker q,
      v = TrivSqZeroExt.inl (z : R) - TrivSqZeroExt.inr (Φ z) := by
    intro v
    exact ⟨fun ⟨z, hz⟩ => ⟨z, hz.symm⟩, fun ⟨z, hz⟩ => hz ▸ hWmem z⟩
  set fq : (TrivSqZeroExt R S.N) →+* S.B := q.comp (fstRingHom R S.N)
  have hfqapply : ∀ v : (TrivSqZeroExt R S.N), fq v = q v.fst := fun _ => rfl
  have hWker : ∀ v ∈ W, fq v = 0 := by
    rintro v ⟨z, rfl⟩
    have hz : q (z : R) = 0 := z.2
    simpa [hfqapply] using hz
  set toB0 : TrivSqZeroExt R S.N ⧸ W →+* S.B := Ideal.Quotient.lift W fq hWker with htoB0
  have htoB0mk : ∀ v : (TrivSqZeroExt R S.N),
      toB0 (Ideal.Quotient.mk W v) = q v.fst := fun _ => rfl
  set ιB' : S.A' →+* TrivSqZeroExt R S.N ⧸ W :=
    (Ideal.Quotient.mk W).comp ((algebraMap R (TrivSqZeroExt R S.N)).comp ι) with hιB'
  let algA' : Algebra S.A' (TrivSqZeroExt R S.N ⧸ W) := ιB'.toAlgebra
  have halg : ∀ a : S.A', algebraMap S.A' (TrivSqZeroExt R S.N ⧸ W) a =
      Ideal.Quotient.mk W (TrivSqZeroExt.inl (ι a)) := by
    intro a
    rw [RingHom.algebraMap_toAlgebra]
    rfl
  set toB : (TrivSqZeroExt R S.N ⧸ W) →ₐ[S.A'] S.B :=
    { toB0 with
      commutes' := by
        intro a
        rw [halg a]
        change toB0 (Ideal.Quotient.mk W (TrivSqZeroExt.inl (ι a))) = _
        rw [htoB0mk]
        simpa using hιq a }
  have htoBmk : ∀ v : (TrivSqZeroExt R S.N), toB (Ideal.Quotient.mk W v) = q v.fst := fun _ => rfl
  set K : Ideal (TrivSqZeroExt R S.N ⧸ W) := RingHom.ker toB.toRingHom with hK
  have hKiff : ∀ v : (TrivSqZeroExt R S.N), Ideal.Quotient.mk W v ∈ K ↔ q v.fst = 0 := by
    intro v
    rw [hK, RingHom.mem_ker]
    exact Iff.rfl
  -- the identification of the kernel with `N`
  have hinrK : ∀ n : S.N, Ideal.Quotient.mk W (TrivSqZeroExt.inr n) ∈ K := by
    intro n
    rw [hKiff]
    simp
  set gN : S.N →+ K :=
    { toFun := fun n => ⟨Ideal.Quotient.mk W (TrivSqZeroExt.inr n), hinrK n⟩
      map_zero' := by apply Subtype.ext; simp
      map_add' := by
        intro x y
        apply Subtype.ext
        simp [TrivSqZeroExt.inr_add] } with hgN
  have hgNinj : Function.Injective gN := by
    intro x y hxy
    have h0 : Ideal.Quotient.mk W (TrivSqZeroExt.inr (x - y)) = 0 := by
      have := congrArg Subtype.val hxy
      simp only [hgN, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
      rw [TrivSqZeroExt.inr_sub, map_sub, this, sub_self]
    rw [Ideal.Quotient.eq_zero_iff_mem, hWiff] at h0
    obtain ⟨z, hz⟩ := h0
    have h1 : (z : R) = 0 := by
      have := congrArg TrivSqZeroExt.fst hz
      simpa [TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr] using this.symm
    have h2 : x - y = -Φ z := by
      have := congrArg TrivSqZeroExt.snd hz
      simpa [TrivSqZeroExt.snd_sub, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr] using this
    rw [show z = 0 from Subtype.ext h1, map_zero, neg_zero, sub_eq_zero] at h2
    exact h2
  have hgNsurj : Function.Surjective gN := by
    intro x
    obtain ⟨v, hv0⟩ := Ideal.Quotient.mk_surjective (x : TrivSqZeroExt R S.N ⧸ W)
    have hv : q v.fst = 0 := (hKiff v).1 (hv0 ▸ x.2)
    refine ⟨v.snd + Φ ⟨v.fst, hv⟩, ?_⟩
    apply Subtype.ext
    simp only [hgN, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [← hv0, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem, hWiff]
    refine ⟨-⟨v.fst, hv⟩, ?_⟩
    apply TrivSqZeroExt.ext
    · simp [TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr]
    · simp [TrivSqZeroExt.snd_sub, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr]
  set e : S.N ≃+ K := AddEquiv.ofBijective gN ⟨hgNinj, hgNsurj⟩
  let smulK : SMul S.B K := ⟨fun b x => e (b • e.symm x)⟩
  have hsmulK : ∀ (b : S.B) (x : K), b • x = e (b • e.symm x) := fun _ _ => rfl
  let modK : Module S.B K :=
    Function.Injective.module S.B (e.symm : K →+ S.N) e.symm.injective
      (fun b x => by rw [hsmulK]; simp)
  have hinrmk : ∀ n : S.N, (e n : TrivSqZeroExt R S.N ⧸ W) =
      Ideal.Quotient.mk W (TrivSqZeroExt.inr n) := fun _ => rfl
  -- the identification is `B`-linear
  set kEquiv : S.N ≃ₗ[S.B] K :=
    { e with
      map_smul' := by
        intro b n
        rw [hsmulK]
        exact congrArg e (by simp) }
  -- the kernel carries the canonical `B`-module structure
  have hsmulker : ∀ (b' : TrivSqZeroExt R S.N ⧸ W) (x : K), toB b' • x = b' • x := by
    intro b' x
    obtain ⟨v, hv⟩ := Ideal.Quotient.mk_surjective b'
    apply Subtype.ext
    rw [hsmulK, hinrmk, ← hv]
    change _ = Ideal.Quotient.mk W v * (x : TrivSqZeroExt R S.N ⧸ W)
    obtain ⟨n, hn⟩ := e.surjective x
    rw [← hn, hinrmk, ← map_mul, htoBmk]
    have hmul : v * TrivSqZeroExt.inr n = TrivSqZeroExt.inr (v.fst • n) := by
      apply TrivSqZeroExt.ext
      · simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inr]
      · simp [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_inr]
    rw [hmul, hsmul v.fst n]
    congr 1
    simp
  -- the kernel is of square zero
  have hsqzero : K ^ 2 = ⊥ := by
    rw [pow_two]
    refine le_antisymm (Ideal.mul_le.mpr ?_) bot_le
    intro x hx y hy
    obtain ⟨u, hu⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨v, hv⟩ := Ideal.Quotient.mk_surjective y
    have hu0 : q u.fst = 0 := (hKiff u).1 (hu ▸ hx)
    have hv0 : q v.fst = 0 := (hKiff v).1 (hv ▸ hy)
    have hz : u.fst * v.fst ∈ RingHom.ker q := by
      rw [RingHom.mem_ker, map_mul, hu0, zero_mul]
    have hΦz : Φ ⟨u.fst * v.fst, hz⟩ = 0 := by
      have hsm : (⟨u.fst * v.fst, hz⟩ : RingHom.ker q) =
          u.fst • (⟨v.fst, by rw [RingHom.mem_ker, hv0]⟩ : RingHom.ker q) := by
        apply Subtype.ext
        simp
      rw [hsm, map_smul, hsmul, hu0, zero_smul]
    rw [Ideal.mem_bot, ← hu, ← hv, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, hWiff]
    refine ⟨⟨u.fst * v.fst, hz⟩, ?_⟩
    apply TrivSqZeroExt.ext
    · simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_inl,
        TrivSqZeroExt.fst_inr]
    · rw [hΦz]
      simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_sub, TrivSqZeroExt.snd_inl,
        TrivSqZeroExt.snd_inr, sub_zero]
      rw [op_smul_eq_smul, hsmul u.fst v.snd, hsmul v.fst u.snd, hu0, hv0, zero_smul,
        zero_smul, add_zero]
  -- the prescribed map on the ideal `I`
  have hIker : ∀ i : S.I, ι i ∈ RingHom.ker q := by
    intro i
    rw [RingHom.mem_ker, hιq, IsScalarTower.algebraMap_apply S.A' S.A S.B,
      algebraMap_eq_zero_of_mem_I, map_zero]
  have hmapI : ∀ i : S.I, ((kEquiv (S.c i) : K) : TrivSqZeroExt R S.N ⧸ W) =
      algebraMap S.A' (TrivSqZeroExt R S.N ⧸ W) i := by
    intro i
    rw [halg]
    change (e (S.c i) : TrivSqZeroExt R S.N ⧸ W) = _
    rw [hinrmk, eq_comm, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem, hWiff]
    refine ⟨⟨ι i, hIker i⟩, ?_⟩
    rw [hΦ i (hIker i)]
  refine ⟨{ B' := TrivSqZeroExt R S.N ⧸ W
            algebraA'B' := algA'
            toB := toB
            surjective := ?_
            sq_zero := hsqzero
            moduleKernel := modK
            toB_smul_kernel := hsmulker
            kernelEquiv := kEquiv
            map_I := hmapI }⟩
  intro b
  obtain ⟨r, hr⟩ := hq b
  exact ⟨Ideal.Quotient.mk W (TrivSqZeroExt.inl r), by rw [htoBmk]; simpa using hr⟩

end Gluing


section Functional

open TensorProduct

/-- **The functional induced by `c` on the extension of `I`.**
If `R` is a flat `A'`-algebra and `N` is an `R`-module through a ring map `q : R → B`
compatible with `A' → B`, then `c : I → N` extends to an `R`-linear map on `I·R`. -/
private theorem exists_functional_on_extended_ideal
    (S : SquareZeroExtensionProblem.{u₁, u₂, u₃, u₄})
    {R : Type w} [CommRing R] [Algebra S.A' R] [Module.Flat S.A' R]
    [Module R S.N] (q : R →+* S.B)
    (hsmul : ∀ (r : R) (x : S.N), r • x = q r • x)
    (hq : ∀ a : S.A', q (algebraMap S.A' R a) = algebraMap S.A' S.B a) :
    ∃ θ : (Ideal.map (algebraMap S.A' R) S.I) →ₗ[R] S.N,
      ∀ (i : S.I) (hi : algebraMap S.A' R (i : S.A') ∈ Ideal.map (algebraMap S.A' R) S.I),
        θ ⟨algebraMap S.A' R (i : S.A'), hi⟩ = S.c i := by
  classical
  let modA'N : Module S.A' S.N := Module.compHom S.N (algebraMap S.A' S.B)
  have hA'smul : ∀ (a : S.A') (x : S.N), a • x = algebraMap S.A' S.B a • x := fun _ _ => rfl
  let towA' : IsScalarTower S.A' R S.N :=
    ⟨fun a r x => by
      rw [hsmul (a • r) x, Algebra.smul_def, map_mul, hq a, hA'smul a (r • x), hsmul r x,
        smul_smul]⟩
  let commA' : SMulCommClass S.A' R S.N :=
    ⟨fun a r x => by
      rw [hsmul r (a • x), hA'smul a x, hA'smul a (r • x), hsmul r x, smul_smul, smul_smul,
        mul_comm]⟩
  -- `c` is `A'`-linear
  have hcA'smul : ∀ (a : S.A') (i : S.I), S.c (a • i) = a • S.c i := by
    intro a i
    rw [← S.algebraMap_smul_I a i, map_smul, hA'smul,
      IsScalarTower.algebraMap_apply S.A' S.A S.B,
      IsScalarTower.algebraMap_smul S.B (algebraMap S.A' S.A a) (S.c i)]
  let cA' : S.I →ₗ[S.A'] S.N :=
    { toFun := fun i => S.c i
      map_add' := fun x y => by simp
      map_smul' := fun a i => hcA'smul a i }
  -- the two maps out of `R ⊗[A'] I`
  let μT : TensorProduct S.A' R S.I →ₗ[R] R :=
    (TensorProduct.AlgebraTensorModule.rid S.A' R R).toLinearMap ∘ₗ
      TensorProduct.AlgebraTensorModule.map (LinearMap.id : R →ₗ[R] R) S.I.subtype
  have hμT : ∀ (r : R) (i : S.I), μT (r ⊗ₜ[S.A'] i) = algebraMap S.A' R (i : S.A') * r := by
    intro r i
    change (i : S.A') • r = _
    rw [Algebra.smul_def]
  let νT : TensorProduct S.A' R S.I →ₗ[R] S.N :=
    TensorProduct.AlgebraTensorModule.lift
      { toFun := fun r => r • cA'
        map_add' := fun x y => by rw [add_smul]
        map_smul' := fun r x => by
          dsimp only [RingHom.id_apply]
          rw [smul_smul, smul_eq_mul] }
  have hνT : ∀ (r : R) (i : S.I), νT (r ⊗ₜ[S.A'] i) = r • S.c i := fun _ _ => rfl
  -- `μT` is injective
  have hinj : Function.Injective μT := by
    have h1 : Function.Injective (LinearMap.lTensor R S.I.subtype) :=
      Module.Flat.lTensor_preserves_injective_linearMap S.I.subtype Subtype.val_injective
    have h2 : ∀ x : TensorProduct S.A' R S.I,
        TensorProduct.AlgebraTensorModule.map (LinearMap.id : R →ₗ[R] R) S.I.subtype x =
          LinearMap.lTensor R S.I.subtype x := by
      intro x
      induction x using TensorProduct.inductionOn with
      | tmul r i => simp
      | add a b ha hb => rw [map_add, map_add, ha, hb]
    intro x y hxy
    apply h1
    rw [← h2, ← h2]
    exact (TensorProduct.AlgebraTensorModule.rid S.A' R R).injective hxy
  -- the range of `μT` is the extension of `I`
  have hrange : LinearMap.range μT = (Ideal.map (algebraMap S.A' R) S.I : Submodule R R) := by
    apply le_antisymm
    · rw [LinearMap.range_le_iff_comap]
      apply Submodule.eq_top_iff'.2
      intro x
      induction x using TensorProduct.inductionOn with
      | tmul r i =>
          simp only [Submodule.mem_comap]
          rw [hμT]
          exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ i.2)
      | add a b ha hb =>
          simp only [Submodule.mem_comap, map_add] at ha hb ⊢
          exact Submodule.add_mem _ ha hb
    · rw [Ideal.map_le_iff_le_comap]
      intro i hi
      exact ⟨(1 : R) ⊗ₜ[S.A'] (⟨i, hi⟩ : S.I), by rw [hμT, mul_one]⟩
  refine ⟨νT ∘ₗ ((LinearEquiv.ofInjective μT hinj).symm.toLinearMap ∘ₗ
    (LinearEquiv.ofEq _ _ hrange).symm.toLinearMap), ?_⟩
  intro i hi
  have hkey : (LinearEquiv.ofInjective μT hinj) ((1 : R) ⊗ₜ[S.A'] i) =
      (LinearEquiv.ofEq _ _ hrange).symm ⟨algebraMap S.A' R (i : S.A'), hi⟩ := by
    apply Subtype.ext
    simp only [LinearEquiv.ofInjective_apply, LinearEquiv.ofEq_symm, LinearEquiv.coe_ofEq_apply]
    rw [hμT, mul_one]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, ← hkey,
    LinearEquiv.symm_apply_apply]
  rw [hνT, one_smul]

end Functional


section Conormal

/-- **The conormal intersection identity for a lifted ideal** (Stacks 07CX in the form used
for the deformation problem).  If `π : R → P` is surjective and `J ⊆ P` is `H₁`-regular,
then `ker π ∩ (π⁻¹J)² = (ker π)·(π⁻¹J)`. -/
private theorem inf_sq_eq_mul_of_comap
    {R : Type u₁} {P : Type u₂} [CommRing R] [CommRing P]
    (π : R →+* P) (hπsurj : Function.Surjective π)
    (J : Ideal P) (hJ : Ideal.IsH1Regular J) :
    RingHom.ker π ⊓ (Ideal.comap π J) ^ 2 = RingHom.ker π * Ideal.comap π J := by
  have hle : RingHom.ker π ≤ Ideal.comap π J := Ideal.ker_le_comap π
  refine Ideal.inf_sq_eq_mul_of_quotient_isH1RegularIdeal _ _ hle ?_
  set μ : R ⧸ RingHom.ker π ≃+* P := RingHom.quotientKerEquivOfSurjective hπsurj
  have hsym : ∀ z : R, (μ.symm : P →+* R ⧸ RingHom.ker π) (π z) =
      Ideal.Quotient.mk (RingHom.ker π) z :=
    fun z => RingHom.quotientKerEquivOfSurjective_symm_apply hπsurj z
  have hmapeq : Ideal.map (Ideal.Quotient.mk (RingHom.ker π)) (Ideal.comap π J) =
      Ideal.map (μ.symm : P →+* R ⧸ RingHom.ker π) J := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro z hz
      rw [Ideal.mem_comap, ← hsym z]
      exact Ideal.mem_map_of_mem _ hz
    · rw [Ideal.map_le_iff_le_comap]
      intro y hy
      obtain ⟨z, rfl⟩ := hπsurj y
      rw [Ideal.mem_comap, hsym z]
      exact Ideal.mem_map_of_mem _ hy
  rw [hmapeq]
  exact (Koszul.regularIdeals_map_flat (μ.symm : P →+* R ⧸ RingHom.ker π)
    (RingHom.Flat.of_bijective μ.symm.bijective) J).2.1 hJ

end Conormal



section Extension

/-- An `R`-linear map between `Λ`-modules is `Λ`-linear when `R → Λ` is surjective and the
`R`-actions are induced by it. -/
private def linearOfSurjective {R Λ M N : Type*} [CommRing R] [CommRing Λ]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] [Module Λ M] [Module Λ N]
    (ρ : R →+* Λ) (hρ : Function.Surjective ρ)
    (hM : ∀ (r : R) (x : M), ρ r • x = r • x) (hN : ∀ (r : R) (x : N), ρ r • x = r • x)
    (f : M →ₗ[R] N) : M →ₗ[Λ] N where
  toFun := f
  map_add' := f.map_add
  map_smul' c x := by
    obtain ⟨r, rfl⟩ := hρ c
    dsimp only [RingHom.id_apply]
    rw [hM r x, hN r (f x)]
    exact f.map_smul r x

/-- **Extension of a functional across the conormal module.**
Let `π : R → P` be surjective, let `J ⊆ P` be a Koszul-regular ideal and `J' = π⁻¹ J`.
An `R`-linear map `ker π → N` which vanishes on `(ker π)·J'` extends to `J'`. -/
private theorem exists_extension_of_koszul
    {R : Type u₁} {P : Type u₂} [CommRing R] [CommRing P]
    (π : R →+* P) (hπsurj : Function.Surjective π)
    (J : Ideal P) (hJ : Ideal.IsKoszulRegular J)
    {N : Type u₄} [AddCommGroup N] [Module R N]
    (θ : ↥(RingHom.ker π) →ₗ[R] N)
    (hθ : ∀ (z : R) (hz : z ∈ RingHom.ker π),
        z ∈ RingHom.ker π * Ideal.comap π J → θ ⟨z, hz⟩ = 0) :
    ∃ Φ : ↥(Ideal.comap π J) →ₗ[R] N,
      ∀ (z : R) (hz : z ∈ RingHom.ker π) (hz' : z ∈ Ideal.comap π J),
        Φ ⟨z, hz'⟩ = θ ⟨z, hz⟩ := by
  classical
  have hle : RingHom.ker π ≤ Ideal.comap π J := Ideal.ker_le_comap π
  have hinf := inf_sq_eq_mul_of_comap π hπsurj J hJ.isH1Regular
  let algRP : Algebra R P := π.toAlgebra
  have halgRP : ∀ r : R, algebraMap R P r = π r := fun _ => rfl
  -- the quotient map onto the conormal module of `J' = π⁻¹ J`
  have htorsJ' : Module.IsTorsionBySet R ((Ideal.comap π J).Cotangent)
      ((Ideal.comap π J : Ideal R) : Set R) :=
    Module.isTorsionBySet_quotient_ideal_smul _ _
  have htors1 : Module.IsTorsionBySet R ((Ideal.comap π J).Cotangent)
      ((RingHom.ker π : Ideal R) : Set R) :=
    fun x a => htorsJ' (x := x) (a := ⟨(a : R), hle a.2⟩)
  let modQ : Module (R ⧸ RingHom.ker π) ((Ideal.comap π J).Cotangent) := htors1.module
  have hmkQsmul : ∀ (r : R) (x : (Ideal.comap π J).Cotangent),
      Ideal.Quotient.mk (RingHom.ker π) r • x = r • x := fun _ _ => rfl
  set μ : R ⧸ RingHom.ker π ≃+* P := RingHom.quotientKerEquivOfSurjective hπsurj
  have hμsym : ∀ z : R, (μ.symm : P →+* R ⧸ RingHom.ker π) (π z) =
      Ideal.Quotient.mk (RingHom.ker π) z :=
    fun z => RingHom.quotientKerEquivOfSurjective_symm_apply hπsurj z
  let modP : Module P ((Ideal.comap π J).Cotangent) :=
    Module.compHom _ (μ.symm : P →+* R ⧸ RingHom.ker π)
  have hsmulP : ∀ (y : P) (x : (Ideal.comap π J).Cotangent),
      y • x = (μ.symm : P →+* R ⧸ RingHom.ker π) y • x := fun _ _ => rfl
  have hπsmul : ∀ (r : R) (x : (Ideal.comap π J).Cotangent), π r • x = r • x := by
    intro r x
    rw [hsmulP, hμsym r, hmkQsmul]
  have hlift : ∀ y ∈ J, ∃ z, π z = y ∧ z ∈ Ideal.comap π J := fun y hy =>
    let ⟨z, hz⟩ := hπsurj y
    ⟨z, hz, by rw [Ideal.mem_comap, hz]; exact hy⟩
  have htors2 : Module.IsTorsionBySet P ((Ideal.comap π J).Cotangent) (J : Set P) := by
    intro x a
    obtain ⟨z, hz, hz'⟩ := hlift a a.2
    rw [show ((a : P) • x) = π z • x by rw [hz], hπsmul]
    exact htorsJ' (x := x) (a := ⟨z, hz'⟩)
  let modΛ : Module (P ⧸ J) ((Ideal.comap π J).Cotangent) := htors2.module
  have hmkΛsmul : ∀ (y : P) (x : (Ideal.comap π J).Cotangent),
      Ideal.Quotient.mk J y • x = y • x := fun _ _ => rfl
  have hRΛsmul : ∀ (r : R) (x : (Ideal.comap π J).Cotangent),
      Ideal.Quotient.mk J (π r) • x = r • x := by
    intro r x
    rw [hmkΛsmul, hπsmul]
  -- the comparison map to the conormal module of `J`
  let Λ₁ : (Ideal.comap π J).Cotangent →ₗ[R] J.Cotangent :=
    Ideal.mapCotangent (Ideal.comap π J) J (Algebra.ofId R P) le_rfl
  have hΛ₁ : ∀ z : ↥(Ideal.comap π J),
      Λ₁ ((Ideal.comap π J).toCotangent z) =
        J.toCotangent ⟨π (z : R), z.2⟩ := fun _ => rfl
  -- upgrade to a `P ⧸ J`-linear map
  let Λ₂ : (Ideal.comap π J).Cotangent →ₗ[P ⧸ J] J.Cotangent :=
    linearOfSurjective ((Ideal.Quotient.mk J).comp π)
      (Ideal.Quotient.mk_surjective.comp hπsurj)
      (fun r x => by rw [RingHom.comp_apply, hRΛsmul])
      (fun r x => by
        rw [RingHom.comp_apply,
          show (Ideal.Quotient.mk J) (π r) = algebraMap P (P ⧸ J) (π r) from rfl,
          IsScalarTower.algebraMap_smul, ← halgRP r, IsScalarTower.algebraMap_smul])
      Λ₁
  have hΛ₂ : ∀ x, Λ₂ x = Λ₁ x := fun _ => rfl
  have hΛ₂surj : Function.Surjective Λ₂ := by
    intro y
    obtain ⟨w, rfl⟩ := J.toCotangent_surjective y
    obtain ⟨z, hz, hz'⟩ := hlift w w.2
    refine ⟨(Ideal.comap π J).toCotangent ⟨z, hz'⟩, ?_⟩
    rw [hΛ₂, hΛ₁]
    congr 1
    exact Subtype.ext hz
  -- the quotient by the kernel is projective, so the kernel is a direct summand
  have projJ : Module.Projective (P ⧸ J) J.Cotangent :=
    (Quasiregular.cotangent_finite_projective_of_quasiregular J hJ.isQuasiregular).2
  have projQ : Module.Projective (P ⧸ J)
      (((Ideal.comap π J).Cotangent) ⧸ LinearMap.ker Λ₂) :=
    Module.Projective.of_equiv (Λ₂.quotKerEquivOfSurjective hΛ₂surj).symm
  obtain ⟨sec, hsec⟩ := Module.projective_lifting_property
    (LinearMap.ker Λ₂).mkQ (LinearMap.id) (LinearMap.ker Λ₂).mkQ_surjective
  let ρ₀ : (Ideal.comap π J).Cotangent →ₗ[P ⧸ J] (Ideal.comap π J).Cotangent :=
    LinearMap.id - sec ∘ₗ (LinearMap.ker Λ₂).mkQ
  let ρ₀R : (Ideal.comap π J).Cotangent →ₗ[R] (Ideal.comap π J).Cotangent :=
    { toFun := ρ₀
      map_add' := ρ₀.map_add
      map_smul' := fun r x => by
        dsimp only [RingHom.id_apply]
        rw [← hRΛsmul r x, ρ₀.map_smul, hRΛsmul] }
  have hρ₀R : ∀ x, ρ₀R x = ρ₀ x := fun _ => rfl
  have hρ₀mem : ∀ x, ρ₀R x ∈ LinearMap.ker Λ₁ := by
    intro x
    have h1 := congrArg (fun (f : _ →ₗ[P ⧸ J] _) => f ((LinearMap.ker Λ₂).mkQ x)) hsec
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at h1
    have h2 : (LinearMap.ker Λ₂).mkQ (ρ₀ x) = 0 := by
      simp only [ρ₀, LinearMap.sub_apply, LinearMap.id_coe, id_eq, LinearMap.coe_comp,
        Function.comp_apply, map_sub, h1, sub_self]
    rw [LinearMap.mem_ker, hρ₀R, ← hΛ₂]
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.mem_ker] at h2
  have hρ₀id : ∀ x, Λ₁ x = 0 → ρ₀R x = x := by
    intro x hx
    have h0 : (LinearMap.ker Λ₂).mkQ x = 0 := by
      rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.mem_ker, hΛ₂]
    rw [hρ₀R]
    simp only [ρ₀, LinearMap.sub_apply, LinearMap.id_coe, id_eq, LinearMap.coe_comp,
      Function.comp_apply, h0, map_zero, sub_zero]
  -- the functional on the kernel, transported to the conormal module
  let X : Submodule R ↥(Ideal.comap π J) :=
    Submodule.comap (Ideal.comap π J).subtype (RingHom.ker π)
  let incl : ↥X →ₗ[R] ↥(RingHom.ker π) :=
    { toFun := fun x => ⟨((x : ↥(Ideal.comap π J)) : R), x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let hmap : ↥X →ₗ[R] (Ideal.comap π J).Cotangent :=
    (Ideal.comap π J).toCotangent ∘ₗ X.subtype
  have hmapapply : ∀ x : ↥X, hmap x =
      (Ideal.comap π J).toCotangent (x : ↥(Ideal.comap π J)) := fun _ => rfl
  let θX : ↥X →ₗ[R] N := θ ∘ₗ incl
  have hθX : ∀ (x : ↥X), θX x = θ ⟨((x : ↥(Ideal.comap π J)) : R), x.2⟩ := fun _ => rfl
  have hθXker : LinearMap.ker hmap ≤ LinearMap.ker θX := by
    intro x hx
    have hx0 : (Ideal.comap π J).toCotangent (x : ↥(Ideal.comap π J)) = 0 := by
      rwa [LinearMap.mem_ker, hmapapply] at hx
    have h1 : ((x : ↥(Ideal.comap π J)) : R) ∈ (Ideal.comap π J) ^ 2 :=
      ((Ideal.comap π J).toCotangent_eq_zero _).1 hx0
    have h2 : ((x : ↥(Ideal.comap π J)) : R) ∈ RingHom.ker π := x.2
    rw [LinearMap.mem_ker, hθX]
    refine hθ _ h2 ?_
    rw [← hinf]
    exact Submodule.mem_inf.2 ⟨h2, h1⟩
  have hrange : LinearMap.range hmap = LinearMap.ker Λ₁ := by
    rw [show LinearMap.ker Λ₁ = _ from
        Ideal.mapCotangent_ker_of_surjective (A := R) (B := P) hπsurj
          (I := J) (J := Ideal.comap π J) (sup_eq_right.mpr hle).symm,
      LinearMap.range_comp, Submodule.range_subtype]
    congr 1
    exact congrArg (Submodule.comap (Ideal.comap π J).subtype) (inf_eq_left.mpr hle).symm
  let θ₁ : ↥(LinearMap.ker Λ₁) →ₗ[R] N :=
    (Submodule.liftQ _ θX hθXker) ∘ₗ hmap.quotKerEquivRange.symm.toLinearMap ∘ₗ
      (LinearEquiv.ofEq _ _ hrange).symm.toLinearMap
  have hθ₁ : ∀ (x : ↥X) (hx : hmap x ∈ LinearMap.ker Λ₁), θ₁ ⟨hmap x, hx⟩ = θX x := by
    intro x hx
    have h1 : (LinearEquiv.ofEq _ _ hrange).symm ⟨hmap x, hx⟩ =
        ⟨hmap x, LinearMap.mem_range.2 ⟨x, rfl⟩⟩ := rfl
    have h2 : hmap.quotKerEquivRange.symm ⟨hmap x, LinearMap.mem_range.2 ⟨x, rfl⟩⟩ =
        (LinearMap.ker hmap).mkQ x := by
      rw [LinearEquiv.symm_apply_eq]
      apply Subtype.ext
      rfl
    simp only [θ₁, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, h1, h2]
    rfl
  -- the solution
  refine ⟨θ₁ ∘ₗ (LinearMap.codRestrict (LinearMap.ker Λ₁) ρ₀R hρ₀mem) ∘ₗ
    (Ideal.comap π J).toCotangent, ?_⟩
  intro z hz hz'
  have hxX : (⟨z, hz'⟩ : ↥(Ideal.comap π J)) ∈ X := Submodule.mem_comap.mpr hz
  have hker : Λ₁ (hmap ⟨⟨z, hz'⟩, hxX⟩) = 0 := by
    rw [← LinearMap.mem_ker, ← hrange]
    exact LinearMap.mem_range.2 ⟨_, rfl⟩
  have hfix : ρ₀R (hmap ⟨⟨z, hz'⟩, hxX⟩) = hmap ⟨⟨z, hz'⟩, hxX⟩ := hρ₀id _ hker
  simp only [LinearMap.coe_comp, Function.comp_apply]
  rw [show (Ideal.comap π J).toCotangent ⟨z, hz'⟩ = hmap ⟨⟨z, hz'⟩, hxX⟩ from rfl,
    show (LinearMap.codRestrict (LinearMap.ker Λ₁) ρ₀R hρ₀mem) (hmap ⟨⟨z, hz'⟩, hxX⟩) =
      ⟨hmap ⟨⟨z, hz'⟩, hxX⟩, by rw [← hfix]; exact hρ₀mem _⟩ from Subtype.ext hfix,
    hθ₁, hθX]

end Extension




section Main

/-- A local complete intersection ring map admits a finite polynomial presentation whose
kernel is a Koszul-regular ideal. -/
private theorem presentation_of_isLocalCompleteIntersection
    {A : Type u₂} {B : Type u₃} [CommRing A] [CommRing B] [Algebra A B]
    (h : (algebraMap A B).IsLocalCompleteIntersection) :
    ∃ (n : ℕ) (p : MvPolynomial (Fin n) A →+* B), Function.Surjective p ∧
      (∀ a : A, p (MvPolynomial.C a) = algebraMap A B a) ∧
      Ideal.IsKoszulRegular (RingHom.ker p) := by
  obtain ⟨n, p, hp, hker⟩ := h.2
  let _ : Algebra A B := (algebraMap A B).toAlgebra
  refine ⟨n, p.toRingHom, hp, fun a ↦ ?_, hker⟩
  rw [← MvPolynomial.algebraMap_eq]
  exact p.commutes a

/-- **Stacks 08S6.**  If `A → B` is a local complete intersection ring map, then every
square-zero extension problem over `A' → A` with target `B` and prescribed kernel map
`c : I → N` has a solution. -/
@[stacks 08S6]
public theorem nonempty_compatibleExtension_of_isLocalCompleteIntersection
    (S : SquareZeroExtensionProblem.{u₁, u₂, u₃, u₄})
    (h : (algebraMap S.A S.B).IsLocalCompleteIntersection) :
    Nonempty (S.CompatibleExtension.{max u₁ (max u₂ (max u₃ u₄))}) := by
  classical
  obtain ⟨n, p, hps, hpC, hJreg⟩ := presentation_of_isLocalCompleteIntersection h
  set π : MvPolynomial (Fin n) S.A' →+* MvPolynomial (Fin n) S.A :=
    MvPolynomial.map (algebraMap S.A' S.A) with hπ
  have hπsurj : Function.Surjective π := MvPolynomial.map_surjective _ S.surjective
  have hπC : ∀ a : S.A',
      π (algebraMap S.A' (MvPolynomial (Fin n) S.A') a) =
        algebraMap S.A (MvPolynomial (Fin n) S.A) (algebraMap S.A' S.A a) := by
    intro a
    rw [MvPolynomial.algebraMap_eq, MvPolynomial.algebraMap_eq, hπ]
    simp
  set q : MvPolynomial (Fin n) S.A' →+* S.B := p.comp π with hq
  have hqsurj : Function.Surjective q := hps.comp hπsurj
  have hqapply : ∀ z, q z = p (π z) := fun _ => rfl
  have hqC : ∀ a : S.A',
      q (algebraMap S.A' (MvPolynomial (Fin n) S.A') a) = algebraMap S.A' S.B a := by
    intro a
    rw [hqapply, hπC, MvPolynomial.algebraMap_eq, hpC, ← IsScalarTower.algebraMap_apply]
  let modRN : Module (MvPolynomial (Fin n) S.A') S.N := Module.compHom S.N q
  have hsmulR : ∀ (r : MvPolynomial (Fin n) S.A') (x : S.N), r • x = q r • x := fun _ _ => rfl
  have flatR : Module.Flat S.A' (MvPolynomial (Fin n) S.A') := Module.Flat.of_free
  -- the two kernels
  have hJ'eq : RingHom.ker q = Ideal.comap π (RingHom.ker p) := by
    ext z
    simp only [RingHom.mem_ker, Ideal.mem_comap, hqapply]
  have hIPeq : Ideal.map (algebraMap S.A' (MvPolynomial (Fin n) S.A')) S.I = RingHom.ker π := by
    rw [MvPolynomial.algebraMap_eq, hπ, MvPolynomial.ker_map, S.kernel_eq]
  -- the functional on `I·R` induced by `c`
  obtain ⟨θ0, hθ0⟩ := exists_functional_on_extended_ideal S q hsmulR hqC
  set θ : ↥(RingHom.ker π) →ₗ[MvPolynomial (Fin n) S.A'] S.N :=
    θ0 ∘ₗ (LinearEquiv.ofEq _ _ hIPeq).symm.toLinearMap with hθdef
  have hθC : ∀ (i : S.I) (hi : algebraMap S.A' (MvPolynomial (Fin n) S.A') (i : S.A') ∈
      RingHom.ker π), θ ⟨_, hi⟩ = S.c i := by
    intro i hi
    rw [hθdef]
    exact hθ0 i _
  -- `θ` kills `(ker π)·(ker q)`
  have hθmul : ∀ (z : MvPolynomial (Fin n) S.A') (hz : z ∈ RingHom.ker π),
      z ∈ RingHom.ker π * Ideal.comap π (RingHom.ker p) → θ ⟨z, hz⟩ = 0 := by
    have hsub : RingHom.ker π * RingHom.ker q ≤
        Submodule.map (RingHom.ker π).subtype (LinearMap.ker θ) := by
      refine Ideal.mul_le.mpr ?_
      intro a ha b hb
      rw [Submodule.mem_map]
      refine ⟨⟨a * b, Ideal.mul_mem_right _ _ ha⟩, ?_, rfl⟩
      have hab : (⟨a * b, Ideal.mul_mem_right _ _ ha⟩ : ↥(RingHom.ker π)) =
          b • (⟨a, ha⟩ : ↥(RingHom.ker π)) := by
        apply Subtype.ext
        change a * b = b * a
        ring
      rw [LinearMap.mem_ker, hab, map_smul, hsmulR, (show q b = 0 from hb), zero_smul]
    intro z hz hmem
    rw [← hJ'eq] at hmem
    obtain ⟨x, hx, hxz⟩ := hsub hmem
    rw [show (⟨z, hz⟩ : ↥(RingHom.ker π)) = x from Subtype.ext hxz.symm]
    exact hx
  -- extend it to the full presentation ideal
  obtain ⟨Φ0, hΦ0⟩ := exists_extension_of_koszul π hπsurj (RingHom.ker p) hJreg θ hθmul
  set Φ : ↥(RingHom.ker q) →ₗ[MvPolynomial (Fin n) S.A'] S.N :=
    Φ0 ∘ₗ (LinearEquiv.ofEq _ _ hJ'eq).toLinearMap with hΦdef
  have hIker : ∀ i : S.I,
      algebraMap S.A' (MvPolynomial (Fin n) S.A') (i : S.A') ∈ RingHom.ker π := by
    intro i
    rw [RingHom.mem_ker, hπC, algebraMap_eq_zero_of_mem_I, map_zero]
  have hΦC : ∀ (i : S.I) (hi : algebraMap S.A' (MvPolynomial (Fin n) S.A') (i : S.A') ∈
      RingHom.ker q), Φ ⟨_, hi⟩ = S.c i := by
    intro i hi
    have hz' : algebraMap S.A' (MvPolynomial (Fin n) S.A') (i : S.A') ∈
        Ideal.comap π (RingHom.ker p) := hJ'eq ▸ hi
    rw [show Φ ⟨_, hi⟩ = Φ0 ⟨_, hz'⟩ from rfl, hΦ0 _ (hIker i) hz']
    exact hθC i (hIker i)
  have hπq : RingHom.ker π ≤ RingHom.ker q := by
    intro z hz
    rw [RingHom.mem_ker, hqapply, (show π z = 0 from hz), map_zero]
  have hIkerq : ∀ i : S.I,
      algebraMap S.A' (MvPolynomial (Fin n) S.A') (i : S.A') ∈ RingHom.ker q :=
    fun i => hπq (hIker i)
  -- transport the data to a universe containing all four of the problem's universes
  let eU : ULift.{max u₂ u₃} (MvPolynomial (Fin n) S.A') ≃+* MvPolynomial (Fin n) S.A' :=
    ULift.ringEquiv
  let qU : ULift.{max u₂ u₃} (MvPolynomial (Fin n) S.A') →+* S.B := q.comp eU.toRingHom
  let ιU : S.A' →+* ULift.{max u₂ u₃} (MvPolynomial (Fin n) S.A') :=
    eU.symm.toRingHom.comp (algebraMap S.A' (MvPolynomial (Fin n) S.A'))
  let modUN : Module (ULift.{max u₂ u₃} (MvPolynomial (Fin n) S.A')) S.N :=
    Module.compHom S.N qU
  have hsmulU : ∀ (r : ULift.{max u₂ u₃} (MvPolynomial (Fin n) S.A')) (x : S.N),
      r • x = qU r • x := fun _ _ => rfl
  have hqUsurj : Function.Surjective qU := hqsurj.comp eU.surjective
  have heU : ∀ a : S.A', eU (ιU a) = algebraMap S.A' (MvPolynomial (Fin n) S.A') a := by
    intro a
    change eU (eU.symm _) = _
    rw [eU.apply_symm_apply]
  have hιqU : ∀ a : S.A', qU (ιU a) = algebraMap S.A' S.B a := by
    intro a
    change q (eU (ιU a)) = _
    rw [heU, hqC]
  have hkerU : ∀ x : ULift.{max u₂ u₃} (MvPolynomial (Fin n) S.A'),
      x ∈ RingHom.ker qU → eU x ∈ RingHom.ker q := fun _ hx => hx
  let ΦU : ↥(RingHom.ker qU) →ₗ[ULift.{max u₂ u₃} (MvPolynomial (Fin n) S.A')] S.N :=
    { toFun := fun x => Φ ⟨eU (x : ULift.{max u₂ u₃} (MvPolynomial (Fin n) S.A')),
        hkerU _ x.2⟩
      map_add' := fun x y => by
        rw [← map_add]
        congr 1
      map_smul' := fun r x => by
        dsimp only [RingHom.id_apply]
        have hx : (⟨eU ((r • x : ↥(RingHom.ker qU)) :
              ULift.{max u₂ u₃} (MvPolynomial (Fin n) S.A')),
            hkerU _ (r • x : ↥(RingHom.ker qU)).2⟩ : ↥(RingHom.ker q)) =
              eU r • (⟨eU (x : ULift.{max u₂ u₃} (MvPolynomial (Fin n) S.A')),
                hkerU _ x.2⟩ : ↥(RingHom.ker q)) := by
          apply Subtype.ext
          change eU (r * (x : ULift.{max u₂ u₃} (MvPolynomial (Fin n) S.A'))) =
            eU r * eU (x : ULift.{max u₂ u₃} (MvPolynomial (Fin n) S.A'))
          rw [map_mul]
        rw [hx, map_smul, hsmulR]
        exact (hsmulU r _).symm }
  have hιUker : ∀ i : S.I, ιU (i : S.A') ∈ RingHom.ker qU := by
    intro i
    rw [RingHom.mem_ker]
    change q (eU (ιU (i : S.A'))) = 0
    rw [heU]
    exact hIkerq i
  have hΦU : ∀ (i : S.I) (hi : ιU (i : S.A') ∈ RingHom.ker qU),
      ΦU ⟨ιU (i : S.A'), hi⟩ = S.c i := by
    intro i hi
    change Φ ⟨eU (ιU (i : S.A')), hkerU _ hi⟩ = S.c i
    rw [show (⟨eU (ιU (i : S.A')), hkerU _ hi⟩ : ↥(RingHom.ker q)) =
      ⟨algebraMap S.A' (MvPolynomial (Fin n) S.A') (i : S.A'), hIkerq i⟩ from
        Subtype.ext (heU (i : S.A'))]
    exact hΦC i (hIkerq i)
  exact nonempty_of_functional S ιU qU hqUsurj hsmulU hιqU ΦU hΦU

end Main



end Stacks.Deformation

end
