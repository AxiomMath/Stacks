module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Localization.BaseChange
public import StacksFrontier.Algebra.Category.Ring.Epi.GenericFlatness
public import StacksFrontier.RingTheory.Localization.Glueing.Functions
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Multiplication by a finite family, under base change and over a generic point

A finite union of standard opens `⋃ⱼ D(gⱼ)` in an affine scheme `Spec B` is
scheme-theoretically dense exactly when `B → ∏ⱼ B_{gⱼ}` is injective, and by Stacks 0565 that
is equivalent to injectivity of the *multiplication map*
`Φ : B → ∏ⱼ B`, `b ↦ (g₁ b, …, gₘ b)`,
which is `bigPhi` of `StacksFrontier.RingTheory.Localization.Glueing.Functions`. This file collects
what is needed to compare that injectivity across the fibres of `Spec B → Spec A`.

Two independent things are proved. The first is that `bigPhi` *commutes with base change*: for an
`A`-algebra `C` the map `Φ` of the family `gⱼ` becomes, after `C ⊗[A] -`, the map `Φ` of the
family `1 ⊗ gⱼ` over `C ⊗[A] B`. So the fibrewise question is a question about one `A`-linear map
and its base changes. The second is a sufficient condition for injectivity to be *inherited* by
every base change at once: it suffices that the cokernel of the map be flat, since then the map
is the left-hand term of a short exact sequence with flat right-hand term.

Over a domain `A` these combine with generic freeness (Stacks 051T) to say that the cokernel
becomes free, hence flat, after inverting one nonzero element of `A`: the content of
`Algebra.exists_ne_zero_free_tensor_cokernelMulFamily`.

Putting the three together gives the algebraic heart of Stacks 0573, in
`Algebra.exists_ne_zero_injective_bigPhi_tmul`: if the multiplication map of the family `gⱼ`
becomes injective over one field `K` into which the domain `A` embeds, then there is a nonzero
`h : A` such that it is injective over *every* `A`-algebra in which `h` becomes invertible — in
particular over every field `L` over `A` with `h ↦ 0` false. In the geometry of Stacks 0573 that
says: if `⋃ⱼ D(gⱼ)` is scheme-theoretically dense in the fibre of `Spec B → Spec A` over the
generic point, then it is scheme-theoretically dense in every fibre over the standard open `D(h)`.

**How the generic fibre is reached.** Freeness of `A_h ⊗[A] B` over `A_h` — the other half of what
generic freeness supplies — makes `A_h ⊗[A] B → K ⊗[A] B` injective, which is Stacks 0538's
"flat implies torsion free, hence `B ⊆ B_K`" in the form the argument uses it. The multiplication
map over `A_h ⊗[A] B` is therefore injective because it is over `K ⊗[A] B`; this is the step at
which the hypothesis about one fibre becomes a hypothesis about the whole of `D(h)`, and it is why
the kernel `I` of the Stacks proof may be discarded.

## Main results

* `injective_lTensor_of_flat_quotient_range`: if the cokernel of `φ` is flat then `φ` stays
  injective after every base change.
* `injective_mkLinearMap_of_isTorsionFree`: a torsion-free module over a domain injects into its
  localization at the nonzero divisors.
* `piRight_comp_lTensor_bigPhi`: `bigPhi` commutes with base change.
* `injective_bigPhi_tmul_iff`: consequently, injectivity of the base-changed multiplication map is
  injectivity of the multiplication map of the base-changed family.
* `injective_bigPhi_of_ringEquiv`: injectivity of a multiplication map is invariant under a ring
  isomorphism carrying the family to the family.
* `Algebra.exists_ne_zero_free_tensor_cokernelMulFamily`: generic freeness of the cokernel, from
  Stacks 051T.
* `Algebra.cokernelMulFamilyBaseChange`, `Algebra.surjective_cokernelMulFamilyBaseChange` and
  `Algebra.exact_bigPhi_cokernelMulFamilyBaseChange`: the base-changed multiplication map sits in
  a short exact sequence whose right-hand term is the model of the cokernel that generic freeness
  speaks about.
* `Algebra.injective_bigPhi_tmul_of_free`: **the algebraic core of Stacks 0573.** Over a base in
  which the two modules of Stacks 051T are already free, injectivity over one field spreads to
  every base change.
* `Algebra.exists_ne_zero_injective_bigPhi_tmul` and
  `Algebra.exists_ne_zero_injective_bigPhi_tmul_of_algebraMap_ne_zero`: the same with the base
  shrunk by generic freeness, stated for an arbitrary algebra over the localization and for a
  field in which `h` stays nonzero.

## Implementation notes

`bigPhi` is stated for an index type `Fin n` and a module `M` over the ring whose elements the
family consists of; here that ring and that module are both `B`, so `bigPhi n g` is the `B`-linear
map `B → (Fin n → B)`. Its restriction of scalars to `A` is what base change is applied to.

The identification `C ⊗[A] (Fin n → B) ≃ (Fin n → C ⊗[A] B)` is `TensorProduct.piRight`, which is
why the index type is finite with decidable equality; `Fin n` supplies both.

The cokernel is written as the quotient of `Fin n → B` by the range of the map, rather than
through an abstract `Module.Finite` hypothesis, so that its `A`-module structure and the scalar
tower over `A → B` are found by instance search; that is what lets generic freeness be applied to
it with the base-change models of the localizations.

Generic freeness delivers the cokernel in the model `(A_h ⊗[A] B) ⊗[B] M`, not as the cokernel of
the base-changed multiplication map, so the exact sequence over `A_h` is built with that model as
its right-hand term rather than with a quotient: `Algebra.cokernelMulFamilyBaseChange` is the
composite of `Algebra.piBaseChangeEquiv` with the base change of the quotient map, and right
exactness of the tensor product gives its surjectivity and the exactness. The alternative — an
isomorphism between `(A_h ⊗[A] B) ⊗[B] M` and the cokernel of the base-changed map — would have to
be built by hand, Mathlib's `lTensor.equiv` being linear only over `B`, and is not needed:
`LinearMap.lTensor_injective_of_exact_of_flat` accepts any flat right-hand term.

The spreading statement `Algebra.injective_bigPhi_tmul_of_free` is stated over an arbitrary base
`A'` with the two freeness hypotheses, with `A' = Localization.Away h` substituted only in the
corollaries. That keeps the conclusion free of the localization and lets a consumer supply its own
model of `A_h`.

## References

* [Stacks Project, Tag 0565](https://stacks.math.columbia.edu/tag/0565)
* [Stacks Project, Tag 051T](https://stacks.math.columbia.edu/tag/051T)
* [Stacks Project, Tag 0538](https://stacks.math.columbia.edu/tag/0538)
* [Stacks Project, Tag 056C](https://stacks.math.columbia.edu/tag/056C)
* [Stacks Project, Tag 0573](https://stacks.math.columbia.edu/tag/0573)
-/

@[expose] public section

open scoped TensorProduct

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- If the cokernel of an `R`-linear map `φ` is flat, then `φ` is injective after tensoring with
any `R`-module. Indeed `φ` is then the left-hand map of a short exact sequence whose right-hand
term is flat, so the sequence stays exact on the left after base change.

This is the direction in which injectivity of a multiplication map is transported from a ring to
all of its base changes at once. -/
@[ega "0 6.1.2" "partial",
  ega "IV 11.3.7" "(a) ⇒ (b)",
  sga "1 IV 1.1" "(i)",
  sga "3 III 4.6.4" "more general"]
theorem injective_lTensor_of_flat_quotient_range {R : Type*} [CommRing R] {N P : Type*}
    [AddCommGroup N] [AddCommGroup P] [Module R N] [Module R P] (φ : N →ₗ[R] P)
    (hφ : Function.Injective φ) [Module.Flat R (P ⧸ LinearMap.range φ)]
    (C : Type*) [AddCommGroup C] [Module R C] :
    Function.Injective (LinearMap.lTensor C φ) :=
  LinearMap.lTensor_injective_of_exact_of_flat (LinearMap.range φ).mkQ
    (Submodule.mkQ_surjective _) φ hφ (LinearMap.exact_map_mkQ_range φ) C

/-- A torsion-free module over a domain injects into its localization at the nonzero divisors.
An element of the kernel is annihilated by some nonzero divisor, and over a domain every nonzero
element is regular, so torsion-freeness forces the element to vanish. -/
@[ega "II 6.4.2" "partial"]
theorem injective_mkLinearMap_of_isTorsionFree (A : Type u) [CommRing A] [IsDomain A]
    (P : Type u) [AddCommGroup P] [Module A P] [Module.IsTorsionFree A P] :
    Function.Injective (LocalizedModule.mkLinearMap (nonZeroDivisors A) P) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  rw [← LinearMap.mem_ker, LocalizedModule.mem_ker_mkLinearMap_iff] at hp
  obtain ⟨r, hr, h⟩ := hp
  exact Module.IsTorsionFree.isSMulRegular (IsRegular.of_ne_zero (nonZeroDivisors.ne_zero hr))
    (by simpa using h)

/-- **Base change of the multiplication map.** For an `A`-algebra `C` and a family `g` in an
`A`-algebra `B`, the base change `C ⊗[A] -` of the multiplication map of `g` is, after the
identification `C ⊗[A] (Fin n → B) ≃ (Fin n → C ⊗[A] B)`, the multiplication map of the family
`1 ⊗ gⱼ` over `C ⊗[A] B`.

Both sides send `c ⊗ b` to the tuple `(c ⊗ gⱼ b)ⱼ`. -/
theorem piRight_comp_lTensor_bigPhi {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {n : ℕ} (g : Fin n → B) (C : Type u) [CommRing C] [Algebra A C] :
    (TensorProduct.piRight A A C (fun _ : Fin n => B)).toLinearMap ∘ₗ
        LinearMap.lTensor C ((bigPhi (M := B) n g).restrictScalars A) =
      (bigPhi (M := C ⊗[A] B) n (fun j => (1 : C) ⊗ₜ[A] g j)).restrictScalars A := by
  ext c b
  simp [bigPhi, Algebra.TensorProduct.tmul_mul_tmul]

/-- Injectivity of the base-changed multiplication map is exactly injectivity of the
multiplication map of the base-changed family, the identification
`C ⊗[A] (Fin n → B) ≃ (Fin n → C ⊗[A] B)` being an isomorphism. -/
theorem injective_bigPhi_tmul_iff {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {n : ℕ} (g : Fin n → B) (C : Type u) [CommRing C] [Algebra A C] :
    Function.Injective (bigPhi (M := C ⊗[A] B) n (fun j => (1 : C) ⊗ₜ[A] g j)) ↔
      Function.Injective (LinearMap.lTensor C ((bigPhi (M := B) n g).restrictScalars A)) := by
  have hcoe := congrArg (fun f : (C ⊗[A] B) →ₗ[A] (Fin n → C ⊗[A] B) => ⇑f)
    (piRight_comp_lTensor_bigPhi g C)
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, LinearMap.coe_restrictScalars] at hcoe
  rw [← hcoe]
  exact (TensorProduct.piRight A A C (fun _ : Fin n => B)).injective.of_comp_iff _

/-- If a ring map `ρ : R →+* S` is injective and the multiplication map of the family `ρ ∘ f`
over `S` is injective, then so is that of `f` over `R`. -/
private theorem injective_bigPhi_of_injective_ringHom {R S : Type u} [CommRing R] [CommRing S]
    (ρ : R →+* S) (hρ : Function.Injective ρ) {n : ℕ} (f : Fin n → R)
    (hS : Function.Injective (bigPhi (M := S) n fun j => ρ (f j))) :
    Function.Injective (bigPhi (M := R) n f) := by
  rw [bigPhi_injective_iff_commonAnnihilator] at hS ⊢
  intro r hr
  refine hρ ((hS _ fun i => ?_).trans (map_zero ρ).symm)
  simp only [smul_eq_mul] at hr ⊢
  rw [← map_mul, hr i, map_zero]

/-- **Injectivity of a multiplication map is a ring-isomorphism invariant.** If `e : R ≃+* S` and
`f` is a family in `R`, then the multiplication map of the family `e ∘ f` over `S` is injective as
soon as that of `f` over `R` is: an element of `S` annihilated by every `e (f i)` has `e.symm` of
it annihilated by every `f i`.

In the proof of Stacks 0573 this is what moves the conclusion from `C ⊗[A_h] (A_h ⊗[A] B)`, where
the base-change argument produces it, to `C ⊗[A] B`, where it is wanted; the isomorphism is
`Algebra.TensorProduct.cancelBaseChange`, which carries `1 ⊗ (1 ⊗ gⱼ)` to `1 ⊗ gⱼ`. -/
theorem injective_bigPhi_of_ringEquiv {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S)
    {n : ℕ} (f : Fin n → R) (hf : Function.Injective (bigPhi (M := R) n f)) :
    Function.Injective (bigPhi (M := S) n fun j => e (f j)) := by
  exact injective_bigPhi_of_injective_ringHom e.symm.toRingHom e.symm.injective _
    (by simpa using hf)

namespace Algebra

/-- The cokernel of multiplication by a finite family `g` in `B`, as a `B`-module. Its
scheme-theoretic meaning is the structure sheaf of the scheme-theoretic closure of
`⋃ⱼ D(gⱼ)`'s complementary data; what matters here is only that it is a finite `B`-module, so that
generic freeness applies to it. -/
abbrev cokernelMulFamily {B : Type u} [CommRing B] {n : ℕ} (g : Fin n → B) : Type u :=
  (Fin n → B) ⧸ LinearMap.range (bigPhi (M := B) n g)

/-- **Generic freeness of the cokernel of a multiplication map** (Stacks 051T). Over a domain `A`,
for a finite type `A`-algebra `B` and a finite family `g` in `B`, there is a nonzero `h : A` such
that after inverting `h` both `B` and the cokernel of multiplication by `g` become free modules
over the localized base.

Freeness of the cokernel is what makes injectivity of the multiplication map spread from the
generic fibre to all fibres over `D(h)`, by
`injective_lTensor_of_flat_quotient_range`; freeness of `B` itself is what makes the localized
`B` torsion-free, which is how injectivity is recovered over `D(h)` in the first place. -/
@[ega "IV 6.11.9" "more general", ega "IV 8.9.4.1" "special case", sga "1 IV 6.7" "special case"]
theorem exists_ne_zero_free_tensor_cokernelMulFamily {A B : Type u} [CommRing A] [IsDomain A]
    [CommRing B] [Algebra A B] [Algebra.FiniteType A B] {n : ℕ} (g : Fin n → B) :
    ∃ h : A, h ≠ 0 ∧
      Module.Free (Localization.Away h) (Localization.Away h ⊗[A] B) ∧
      Module.Free (Localization.Away h)
        ((Localization.Away h ⊗[A] B) ⊗[B] cokernelMulFamily g) := by
  obtain ⟨h, hne, hfp⟩ :=
    Algebra.exists_ne_zero_isFinitePresentationFreeAway (R := A) (S := B)
      (M := cokernelMulFamily g)
  have key := (Algebra.isFinitePresentationFreeAway_iff (R := A) (S := B)
      (M := cokernelMulFamily g) h (Localization.Away h) (Localization.Away h ⊗[A] B)
      ((Localization.Away h ⊗[A] B) ⊗[B] cokernelMulFamily g)
      (TensorProduct.mk B (Localization.Away h ⊗[A] B) (cokernelMulFamily g) 1)).mp hfp
  exact ⟨h, hne, key.2.2⟩

section BaseChange

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] {n : ℕ} (g : Fin n → B)
  (A' : Type u) [CommRing A'] [Algebra A A']

/-- **The base change of a finite product of copies of `B`.** For an `A`-algebra `A'` the base
change of `Fin n → B` along `B → A' ⊗[A] B` is `Fin n → A' ⊗[A] B`, linearly over `A' ⊗[A] B`.

This is `TensorProduct.piRight` followed by cancelling the `B` in each factor; it is what turns
the base change of the multiplication map of `g` into the multiplication map of the family
`1 ⊗ gⱼ`, in the shape needed for the exact sequence of Stacks 0573. -/
def piBaseChangeEquiv :
    (A' ⊗[A] B) ⊗[B] (Fin n → B) ≃ₗ[A' ⊗[A] B] (Fin n → A' ⊗[A] B) :=
  (_root_.TensorProduct.piRight B (A' ⊗[A] B) (A' ⊗[A] B) fun _ : Fin n => B).trans
    (LinearEquiv.piCongrRight fun _ =>
      _root_.TensorProduct.AlgebraTensorModule.rid B (A' ⊗[A] B) (A' ⊗[A] B))

/-- `Algebra.piBaseChangeEquiv` sends `x ⊗ y` to the tuple `(yⱼ • x)ⱼ`. -/
@[simp] lemma piBaseChangeEquiv_tmul (x : A' ⊗[A] B) (y : Fin n → B) :
    piBaseChangeEquiv (n := n) A' (x ⊗ₜ[B] y) = fun j => y j • x := rfl

/-- **The base-changed multiplication map, in coordinates.** Under
`Algebra.piBaseChangeEquiv` the base change along `B → A' ⊗[A] B` of the multiplication map of `g`
is the multiplication map of the family `1 ⊗ gⱼ` over `A' ⊗[A] B`.

Both sides send `x` to the tuple `((1 ⊗ gⱼ) * x)ⱼ`; this is the identity on which the exactness
statement for Stacks 0573 rests. -/
lemma piBaseChangeEquiv_lTensor_bigPhi (x : A' ⊗[A] B) :
    piBaseChangeEquiv (n := n) A'
        (LinearMap.lTensor (A' ⊗[A] B) (bigPhi (M := B) n g) (x ⊗ₜ[B] (1 : B))) =
      bigPhi (M := A' ⊗[A] B) n (fun j => (1 : A') ⊗ₜ[A] g j) x := by
  ext j
  simp [bigPhi, Algebra.smul_def, Algebra.TensorProduct.right_algebraMap_apply]

/-- **The cokernel of the base-changed multiplication map, in the model of Stacks 051T.** The map
`Fin n → A' ⊗[A] B` to `(A' ⊗[A] B) ⊗[B] M`, where `M` is the cokernel of the multiplication map
of `g` over `B`, obtained by base changing the quotient map along `B → A' ⊗[A] B`.

Generic freeness (Stacks 051T) asserts freeness of `(A' ⊗[A] B) ⊗[B] M` over `A'`, so this is the
model in which the exact sequence of Stacks 0573 has a flat right-hand term. -/
def cokernelMulFamilyBaseChange : (Fin n → A' ⊗[A] B) →ₗ[A' ⊗[A] B]
    (A' ⊗[A] B) ⊗[B] cokernelMulFamily g :=
  _root_.TensorProduct.AlgebraTensorModule.lTensor (A' ⊗[A] B) (A' ⊗[A] B)
      (LinearMap.range (bigPhi (M := B) n g)).mkQ ∘ₗ
    (piBaseChangeEquiv (n := n) A').symm.toLinearMap

/-- `Algebra.cokernelMulFamilyBaseChange` is the base-changed quotient map read through
`Algebra.piBaseChangeEquiv`. -/
lemma cokernelMulFamilyBaseChange_apply (x : Fin n → A' ⊗[A] B) :
    cokernelMulFamilyBaseChange g A' x =
      LinearMap.lTensor (A' ⊗[A] B) (LinearMap.range (bigPhi (M := B) n g)).mkQ
        ((piBaseChangeEquiv (n := n) A').symm x) := rfl

/-- The base change of a surjection is a surjection, so
`Algebra.cokernelMulFamilyBaseChange` is surjective. This is the right-hand end of the short exact
sequence used for Stacks 0573. -/
lemma surjective_cokernelMulFamilyBaseChange :
    Function.Surjective (cokernelMulFamilyBaseChange (A := A) g A') := by
  intro y
  obtain ⟨z, hz⟩ := LinearMap.lTensor_surjective (A' ⊗[A] B)
    (Submodule.mkQ_surjective (LinearMap.range (bigPhi (M := B) n g))) y
  exact ⟨piBaseChangeEquiv (n := n) A' z, by
    rw [cokernelMulFamilyBaseChange_apply, LinearEquiv.symm_apply_apply, hz]⟩

/-- **The short exact sequence of Stacks 0573 after base change.** The multiplication map of the
family `1 ⊗ gⱼ` over `A' ⊗[A] B` and `Algebra.cokernelMulFamilyBaseChange` form an exact pair.

The tensor product is right exact, so base changing
`B → (Fin n → B) → M → 0` along `B → A' ⊗[A] B` keeps it exact; `Algebra.piBaseChangeEquiv`
identifies the middle term with `Fin n → A' ⊗[A] B` and, by
`Algebra.piBaseChangeEquiv_lTensor_bigPhi`, the left-hand map with the multiplication map of the
base-changed family. -/
lemma exact_bigPhi_cokernelMulFamilyBaseChange :
    Function.Exact (bigPhi (M := A' ⊗[A] B) n fun j => (1 : A') ⊗ₜ[A] g j)
      (cokernelMulFamilyBaseChange (A := A) g A') := by
  have hex := lTensor_exact (A' ⊗[A] B)
    (LinearMap.exact_map_mkQ_range (bigPhi (M := B) n g)) (Submodule.mkQ_surjective _)
  intro x
  rw [cokernelMulFamilyBaseChange_apply, hex]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨b, rfl⟩ : ∃ b : A' ⊗[A] B, b ⊗ₜ[B] (1 : B) = y :=
      ⟨_root_.TensorProduct.AlgebraTensorModule.rid B (A' ⊗[A] B) (A' ⊗[A] B) y,
        (_root_.TensorProduct.AlgebraTensorModule.rid B (A' ⊗[A] B)
          (A' ⊗[A] B)).symm_apply_apply y⟩
    exact ⟨b, by
      rw [← piBaseChangeEquiv_lTensor_bigPhi g A' b, hy, LinearEquiv.apply_symm_apply]⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b ⊗ₜ[B] (1 : B), by
      rw [← piBaseChangeEquiv_lTensor_bigPhi g A' b, LinearEquiv.symm_apply_apply]⟩

/-- **The algebraic core of Stacks 0573.** Let `A'` be an `A`-algebra for which both `A' ⊗[A] B`
and the cokernel model `(A' ⊗[A] B) ⊗[B] M` are free over `A'` — the conclusion of generic
freeness, Stacks 051T. Let `K` be a field over `A` and over `A'`, compatibly, with `A' → K`
injective. If the multiplication map of the family `1 ⊗ gⱼ` is injective over `K ⊗[A] B`, then it
is injective over `C ⊗[A] B` for *every* commutative `A'`-algebra `C`.

Three steps. Freeness of `A' ⊗[A] B` over `A'` makes it flat, hence `A' ⊗[A] B → K ⊗[A] B`
injective (the use of Stacks 0538 in the source), so the multiplication map is injective already
over `A' ⊗[A] B`. Freeness of the cokernel model makes it flat over `A'`, so the exact sequence
`Algebra.exact_bigPhi_cokernelMulFamilyBaseChange` stays exact on the left after `C ⊗[A'] -`
(Stacks 00HL). Finally `injective_bigPhi_tmul_iff` and `Algebra.TensorProduct.cancelBaseChange`
rewrite that as injectivity over `C ⊗[A] B`. -/
theorem injective_bigPhi_tmul_of_free [Module.Free A' (A' ⊗[A] B)]
    [Module.Free A' ((A' ⊗[A] B) ⊗[B] cokernelMulFamily g)]
    (K : Type u) [Field K] [Algebra A K] [Algebra A' K] [IsScalarTower A A' K]
    (hA'K : Function.Injective (algebraMap A' K))
    (hK : Function.Injective (bigPhi (M := K ⊗[A] B) n fun j => (1 : K) ⊗ₜ[A] g j))
    (C : Type u) [CommRing C] [Algebra A C] [Algebra A' C] [IsScalarTower A A' C] :
    Function.Injective (bigPhi (M := C ⊗[A] B) n fun j => (1 : C) ⊗ₜ[A] g j) := by
  have : Module.Flat A' (A' ⊗[A] B) := Module.Flat.of_free
  set rho : (A' ⊗[A] B) →ₐ[A] (K ⊗[A] B) :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom A A' K) (AlgHom.id A B) with hrhodef
  have hrho : Function.Injective rho := by
    have hcomp : ∀ x : A' ⊗[A] B, rho x =
        _root_.TensorProduct.AlgebraTensorModule.cancelBaseChange A A' K K B
          (LinearMap.rTensor (A' ⊗[A] B) (Algebra.linearMap A' K)
            ((_root_.TensorProduct.lid A' (A' ⊗[A] B)).symm x)) := by
      intro x
      induction x with
      | tmul a b => simp [hrhodef, Algebra.smul_def]
      | add x y hx hy => simp [map_add, hx, hy]
    rw [show (rho : _ → _) = _ from funext hcomp]
    exact (_root_.TensorProduct.AlgebraTensorModule.cancelBaseChange A A' K K B).injective.comp
      ((Module.Flat.rTensor_preserves_injective_linearMap (M := A' ⊗[A] B)
          (Algebra.linearMap A' K) hA'K).comp
        (_root_.TensorProduct.lid A' (A' ⊗[A] B)).symm.injective)
  have hbigPhi : Function.Injective
      (bigPhi (M := A' ⊗[A] B) n fun j => (1 : A') ⊗ₜ[A] g j) := by
    exact injective_bigPhi_of_injective_ringHom rho.toRingHom hrho _ (by simpa [hrhodef] using hK)
  have : Module.Flat A' ((A' ⊗[A] B) ⊗[B] cokernelMulFamily g) := Module.Flat.of_free
  have hCinj := LinearMap.lTensor_injective_of_exact_of_flat
    ((cokernelMulFamilyBaseChange (A := A) g A').restrictScalars A')
    (surjective_cokernelMulFamilyBaseChange g A')
    ((bigPhi (M := A' ⊗[A] B) n fun j => (1 : A') ⊗ₜ[A] g j).restrictScalars A')
    hbigPhi (exact_bigPhi_cokernelMulFamilyBaseChange g A') C
  simpa using injective_bigPhi_of_ringEquiv
    (Algebra.TensorProduct.cancelBaseChange A A' C C B).toRingEquiv _
    ((injective_bigPhi_tmul_iff (A := A') (B := A' ⊗[A] B)
      (fun j => (1 : A') ⊗ₜ[A] g j) C).mpr hCinj)

/-- **Stacks 0573, affine and algebraic.** Let `A` be a domain, `B` a finite type `A`-algebra, `g`
a finite family in `B` and `K` a field over `A` with `A → K` injective. If the multiplication map
of the family `1 ⊗ gⱼ` is injective over `K ⊗[A] B`, then there is a nonzero `h : A` such that it
is injective over `C ⊗[A] B` for every commutative `A`-algebra `C` which is an algebra over
`A_h = Localization.Away h`, compatibly.

The element `h` is the one produced by generic freeness, Stacks 051T, in
`Algebra.exists_ne_zero_free_tensor_cokernelMulFamily`; the spreading is
`Algebra.injective_bigPhi_tmul_of_free`, whose hypothesis that `A_h → K` be injective holds
because `h` is invertible in `K` and `A → K` is injective. -/
theorem exists_ne_zero_injective_bigPhi_tmul [IsDomain A] [Algebra.FiniteType A B]
    (K : Type u) [Field K] [Algebra A K] (hAK : Function.Injective (algebraMap A K))
    (hK : Function.Injective (bigPhi (M := K ⊗[A] B) n fun j => (1 : K) ⊗ₜ[A] g j)) :
    ∃ h : A, h ≠ 0 ∧ ∀ (C : Type u) [CommRing C] [Algebra A C]
        [Algebra (Localization.Away h) C] [IsScalarTower A (Localization.Away h) C],
      Function.Injective (bigPhi (M := C ⊗[A] B) n fun j => (1 : C) ⊗ₜ[A] g j) := by
  obtain ⟨h, hne, hfreeB, hfreecok⟩ := exists_ne_zero_free_tensor_cokernelMulFamily (A := A) g
  have hunit : IsUnit (algebraMap A K h) :=
    isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ hAK).mpr hne)
  let _ : Algebra (Localization.Away h) K := (IsLocalization.Away.lift h hunit).toAlgebra
  have : IsScalarTower A (Localization.Away h) K :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.lift_comp _).symm
  have := hfreeB
  have := hfreecok
  have hA'K : Function.Injective (algebraMap (Localization.Away h) K) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨y, s⟩, rfl⟩ :=
      IsLocalization.mk'_surjective (M := Submonoid.powers h) (S := Localization.Away h) x
    have h2 := congrArg (algebraMap (Localization.Away h) K)
      (IsLocalization.mk'_spec (Localization.Away h) y s)
    rw [map_mul, hx, zero_mul, ← IsScalarTower.algebraMap_apply] at h2
    obtain rfl : y = 0 := hAK (by rw [map_zero, ← h2])
    exact IsLocalization.mk'_zero _
  exact ⟨h, hne, fun C _ _ _ _ => injective_bigPhi_tmul_of_free g _ K hA'K hK C⟩

/-- **Stacks 0573 over the fibres of `D(h)`.** The form of
`Algebra.exists_ne_zero_injective_bigPhi_tmul` in which the base change is a field: there is a
nonzero `h : A` such that the multiplication map of `1 ⊗ gⱼ` is injective over `L ⊗[A] B` for
every field `L` over `A` in which `h` does not become zero, i.e. over every point of the standard
open `D(h)` of `Spec A`.

A nonzero element of a field is a unit, so such an `L` is an algebra over `A_h` and the general
form applies. -/
theorem exists_ne_zero_injective_bigPhi_tmul_of_algebraMap_ne_zero [IsDomain A]
    [Algebra.FiniteType A B] (K : Type u) [Field K] [Algebra A K]
    (hAK : Function.Injective (algebraMap A K))
    (hK : Function.Injective (bigPhi (M := K ⊗[A] B) n fun j => (1 : K) ⊗ₜ[A] g j)) :
    ∃ h : A, h ≠ 0 ∧ ∀ (L : Type u) [Field L] [Algebra A L], algebraMap A L h ≠ 0 →
      Function.Injective (bigPhi (M := L ⊗[A] B) n fun j => (1 : L) ⊗ₜ[A] g j) := by
  obtain ⟨h, hne, hmain⟩ := exists_ne_zero_injective_bigPhi_tmul g K hAK hK
  refine ⟨h, hne, fun L _ _ hL => ?_⟩
  let _ : Algebra (Localization.Away h) L :=
    (IsLocalization.Away.lift h (isUnit_iff_ne_zero.mpr hL)).toAlgebra
  have : IsScalarTower A (Localization.Away h) L :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.lift_comp _).symm
  exact hmain L

end BaseChange

end Algebra

end
