module

public import StacksFrontier.AlgebraicGeometry.Pushout.Affine
public import StacksFrontier.AlgebraicGeometry.Smooth.ThickeningRestriction

/-!
# The fibre product `A ×_C C'` as a square-zero thickening of `A`

Let `φ : A → C` be a map of `Λ`-algebras and let `f : C' → C` be a surjection of `Λ`-algebras
with square-zero kernel `I`. The direction `(2) ⇒ (1)` of [Stacks, Tag 07YM] forms the fibre
product `A' = A ×_C C'` and uses it twice: as a square-zero thickening of `A` whose obstruction
class the cohomological hypothesis kills, and as the receptacle of the section that the
vanishing of that class produces — a `Λ`-algebra section `A → A'` is exactly a `Λ`-algebra map
`A → C'` lifting `φ` along `f`, which is the lift of the base the versality criterion asks for.

This file supplies the algebra of that fibre product. Nothing here mentions schemes, sites or
cohomology.

## Main definitions

* `Deformation.Artin.fibreProductAlgebra` — the `A`-algebra structure on `A ×_C C'` given by the
  first projection, together with `Deformation.Artin.fibreProductIsScalarTower`, the tower
  `Λ → A ×_C C' → A`. The fibre product itself is Mathlib's `AlgHom.pullback`, a `Λ`-subalgebra
  of `A × C'`, so its `Λ`-algebra structure is not rebuilt.
* `Deformation.Artin.fibreProductKerEquiv` — the identification of the kernel of
  `A ×_C C' → A` with the residue field, carrying the `A`-action of
  `Stacks.Smooth.kerModule`.

## Main results

* `Deformation.Artin.surjective_fibreProduct_algebraMap` and
  `Deformation.Artin.ker_fibreProduct_sq_eq_bot` — `A ×_C C' → A` is a square-zero surjection.
* `Deformation.Artin.exists_algHom_lift_of_algHom_section` — **what the section is for**: a
  `Λ`-algebra section of `A ×_C C' → A` is a `Λ`-algebra map `A → C'` with `f ∘ ψ = φ`.

## Implementation notes

The `A`-algebra structure of the fibre product is `RingHom.toAlgebra` of the first projection.
That is sound here, and is the only such construction in the file: the structure is attached to
a *new* type — the subalgebra `AlgHom.pullback φ f` of `A × C'`, which carries no `A`-algebra
structure of its own — so nothing is replaced, and the `Λ`-algebra structure, the one that could
be replaced, is the subalgebra's own and is reused unchanged. With that choice
`algebraMap (A ×_C C') A` is `RingHom.pullbackFst` by `rfl`, which is what lets the results of
`StacksFrontier.AlgebraicGeometry.Pushout.Affine` — stated for Mathlib's `RingHom.pullback`, the
same subring — be applied without transport.

The hypotheses describing the kernel are stated with plain ring maps `rC : C → k` and
`rC' : C' → k` to the residue field rather than with the residue data of
`Deformation.ArtinianLocalAlgCat`: the identification of `I` with `k` that
[Stacks, Tag 06H0] provides is `C'`-linear for the action of `C'` on the *ideal* `I`, which is
the canonical `Submodule` action and needs no module structure to be built, and the `A`-action
it has to be compared with factors through `rC ∘ φ`.

## References

* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
* [Stacks Project, Tag 06H0](https://stacks.math.columbia.edu/tag/06H0)
-/

@[expose] public noncomputable section

universe u

namespace Deformation.Artin

section FibreProduct

variable {Λ A C C' : Type u} [CommRing Λ] [CommRing A] [CommRing C] [CommRing C']
  [Algebra Λ A] [Algebra Λ C] [Algebra Λ C']
  (φ : A →ₐ[Λ] C) (f : C' →ₐ[Λ] C)

/-- The `A`-algebra structure on the fibre product `A ×_C C'` given by the first projection.
This is the structure under which `A ×_C C' → A` is a square-zero thickening of `A`. -/
@[instance_reducible]
public instance fibreProductAlgebra : Algebra (AlgHom.pullback φ f) A :=
  (AlgHom.pullbackFst φ f).toRingHom.toAlgebra

/-- The tower `Λ → A ×_C C' → A`: the structure map of `A` over the fibre product is the first
projection, which carries `Λ` to `Λ`. -/
public instance fibreProductIsScalarTower : IsScalarTower Λ (AlgHom.pullback φ f) A :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The structure map of `A` over the fibre product is the first projection, read as a map of
Mathlib's `RingHom.pullback`. This is what makes the results of
`StacksFrontier.AlgebraicGeometry.Pushout.Affine` applicable without transport. -/
public theorem algebraMap_fibreProduct_eq :
    (algebraMap (AlgHom.pullback φ f) A) =
      RingHom.pullbackFst (φ : A →+* C) (f : C' →+* C) := rfl

/-- The first coordinate of a point of the fibre product is the structure map of `A` over it. -/
@[simp] public theorem algebraMap_fibreProduct_apply (z : AlgHom.pullback φ f) :
    algebraMap (AlgHom.pullback φ f) A z = ((z : A × C')).1 := rfl

/-- A point of the fibre product has `φ` of its first coordinate equal to `f` of its second. -/
public theorem fibreProduct_prop (z : AlgHom.pullback φ f) :
    φ ((z : A × C')).1 = f ((z : A × C')).2 := z.2

/-- `A ×_C C' → A` is surjective when `f` is. -/
public theorem surjective_fibreProduct_algebraMap (hf : Function.Surjective f) :
    Function.Surjective (algebraMap (AlgHom.pullback φ f) A) :=
  RingHom.surjective_pullbackFst_of_surjective (φ : A →+* C) (f : C' →+* C) hf

/-- An element of the kernel of `A ×_C C' → A` has first coordinate zero and second coordinate
in the kernel of `f`. -/
public theorem mem_ker_fibreProduct_iff (z : AlgHom.pullback φ f) :
    z ∈ RingHom.ker (algebraMap (AlgHom.pullback φ f) A) ↔
      ((z : A × C')).1 = 0 ∧ ((z : A × C')).2 ∈ RingHom.ker (f : C' →+* C) := by
  refine ⟨fun hz => ?_, fun h => RingHom.mem_ker.2 h.1⟩
  have h1 : ((z : A × C')).1 = 0 := RingHom.mem_ker.1 hz
  refine ⟨h1, RingHom.mem_ker.2 ?_⟩
  change f ((z : A × C')).2 = 0
  rw [← fibreProduct_prop φ f z, h1, map_zero]

/-- The kernel of `A ×_C C' → A` is square-zero when the kernel of `f` is: an element of it has
first coordinate zero and second coordinate in `Ker f`, so the product of two of them is
`(0, 0)`. -/
public theorem ker_fibreProduct_sq_eq_bot
    (hsq : RingHom.ker (f : C' →+* C) ^ 2 = ⊥) :
    RingHom.ker (algebraMap (AlgHom.pullback φ f) A) ^ 2 = ⊥ := by
  rw [← le_bot_iff, pow_two]
  refine Ideal.mul_le.mpr fun z hz w hw => ?_
  obtain ⟨hz1, hz2⟩ := (mem_ker_fibreProduct_iff φ f z).1 hz
  obtain ⟨hw1, hw2⟩ := (mem_ker_fibreProduct_iff φ f w).1 hw
  have hmul : ((z : A × C')).2 * ((w : A × C')).2 = 0 := by
    have h : ((z : A × C')).2 * ((w : A × C')).2 ∈ RingHom.ker (f : C' →+* C) ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul hz2 hw2
    rwa [hsq, Ideal.mem_bot] at h
  rw [Ideal.mem_bot]
  refine Subtype.ext (Prod.ext ?_ ?_)
  · change ((z : A × C')).1 * ((w : A × C')).1 = 0
    rw [hz1, zero_mul]
  · change ((z : A × C')).2 * ((w : A × C')).2 = 0
    exact hmul

end FibreProduct

/-! ### The kernel of the fibre product, identified with the residue field -/

section Kernel

variable {Λ A C C' k : Type u} [CommRing Λ] [CommRing A] [CommRing C] [CommRing C']
  [Field k] [Algebra Λ A] [Algebra Λ C] [Algebra Λ C'] [Algebra A k]
  {φ : A →ₐ[Λ] C} {f : C' →ₐ[Λ] C}

variable (hf : Function.Surjective f) (hsq : RingHom.ker (f : C' →+* C) ^ 2 = ⊥)
  (rC : C →+* k) (rC' : C' →+* k)
  (hrC' : ∀ c : C', rC (f c) = rC' c)
  (hrφ : ∀ a : A, rC (φ a) = algebraMap A k a)
  (e : RingHom.ker (f : C' →+* C) ≃+ k)
  (he : ∀ (c : C') (i : RingHom.ker (f : C' →+* C)), e (c • i) = rC' c * e i)

/-- The second coordinate of an element of the kernel of `A ×_C C' → A`, as an element of the
kernel of `f`. -/
public def fibreProductKerSnd (z : RingHom.ker (algebraMap (AlgHom.pullback φ f) A)) :
    RingHom.ker (f : C' →+* C) :=
  ⟨((z.1 : A × C')).2, ((mem_ker_fibreProduct_iff φ f z.1).1 z.2).2⟩

include hf hsq hrC' hrφ he in
/-- **The kernel of the fibre product is the residue field.** The second projection carries the
kernel of `A ×_C C' → A` bijectively onto the kernel `I` of `f`, and the identification of `I`
with `k` is `A`-linear for the action of `A` on the kernel through `Stacks.Smooth.kerModule`:
lifting `a : A` to a point `(a, c)` of the fibre product, the action is multiplication by `c`,
and `rC' c = rC (f c) = rC (φ a)` is the image of `a` in `k`. -/
public def fibreProductKerEquiv :
    letI := Stacks.Smooth.kerModule (surjective_fibreProduct_algebraMap φ f hf)
      (ker_fibreProduct_sq_eq_bot φ f hsq)
    RingHom.ker (algebraMap (AlgHom.pullback φ f) A) ≃ₗ[A] k := by
  letI := Stacks.Smooth.kerModule (surjective_fibreProduct_algebraMap φ f hf)
    (ker_fibreProduct_sq_eq_bot φ f hsq)
  refine LinearEquiv.ofBijective
    ({ toFun := fun z => e (fibreProductKerSnd z)
       map_add' := fun z w => map_add e (fibreProductKerSnd z) (fibreProductKerSnd w)
       map_smul' := fun a z => ?_ } : _ →ₗ[A] k) ⟨?_, ?_⟩
  · -- `A`-linearity
    obtain ⟨c, hc⟩ := hf (φ a)
    have hmem : (a, c) ∈ AlgHom.pullback φ f := by
      simpa [AlgHom.pullback, AlgHom.mem_equalizer] using hc.symm
    have hact : a • z = (⟨(a, c), hmem⟩ : AlgHom.pullback φ f) • z :=
      Stacks.Smooth.kerModule_smul (surjective_fibreProduct_algebraMap φ f hf)
        (ker_fibreProduct_sq_eq_bot φ f hsq) ⟨(a, c), hmem⟩ z
    have hcoord : fibreProductKerSnd ((⟨(a, c), hmem⟩ : AlgHom.pullback φ f) • z) =
        c • fibreProductKerSnd z := rfl
    change e (fibreProductKerSnd (a • z)) = (RingHom.id A) a • e (fibreProductKerSnd z)
    rw [RingHom.id_apply, Algebra.smul_def, hact, hcoord, he c (fibreProductKerSnd z),
      ← hrC' c, hc, hrφ a]
  · -- injectivity
    intro z w hzw
    refine Subtype.ext (Subtype.ext (Prod.ext ?_ ?_))
    · rw [((mem_ker_fibreProduct_iff φ f z.1).1 z.2).1,
        ((mem_ker_fibreProduct_iff φ f w.1).1 w.2).1]
    · exact congrArg Subtype.val (e.injective hzw)
  · -- surjectivity
    intro t
    obtain ⟨i, rfl⟩ := e.surjective t
    have hmem : ((0 : A), (i : C')) ∈ AlgHom.pullback φ f := by
      simpa [AlgHom.pullback, AlgHom.mem_equalizer] using (RingHom.mem_ker.1 i.2).symm
    exact ⟨⟨⟨(0, (i : C')), hmem⟩, RingHom.mem_ker.2 rfl⟩, congrArg e (Subtype.ext rfl)⟩

end Kernel

/-! ### A section of the fibre product is a lift of the base -/

section Section

variable {Λ A C C' : Type u} [CommRing Λ] [CommRing A] [CommRing C] [CommRing C']
  [Algebra Λ A] [Algebra Λ C] [Algebra Λ C']
  (φ : A →ₐ[Λ] C) (f : C' →ₐ[Λ] C)

/-- **What the section is for.** A `Λ`-algebra section of the projection `A ×_C C' → A` is the
same thing as a `Λ`-algebra map `ψ : A → C'` with `f ∘ ψ = φ`: compose the section with the
second projection, and the defining relation of the fibre product turns the section property
into the factorization. -/
public theorem exists_algHom_lift_of_algHom_section
    (σ : A →ₐ[Λ] AlgHom.pullback φ f)
    (hσ : (algebraMap (AlgHom.pullback φ f) A).comp (σ : A →+* AlgHom.pullback φ f) =
      RingHom.id A) :
    ∃ ψ : A →ₐ[Λ] C', f.comp ψ = φ := by
  refine ⟨(AlgHom.pullbackSnd φ f).comp σ, AlgHom.ext fun a => ?_⟩
  have h1 : ((σ a : A × C')).1 = a := by simpa using RingHom.congr_fun hσ a
  change f ((σ a : A × C')).2 = φ a
  rw [← fibreProduct_prop φ f (σ a), h1]

end Section

end Deformation.Artin

end
