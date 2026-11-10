module

public import Mathlib.Algebra.Algebra.Epi
public import Mathlib.Algebra.Category.Ring.Epi
public import Mathlib.Algebra.Category.Ring.Instances
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.LocalProperties.Submodule
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.StacksAttribute

/-!
# Epimorphisms of rings

An *epimorphism of rings* is a right-cancellable map of commutative rings, that is an
epimorphism in the category `CommRingCat`. Mathlib's class `Algebra.IsEpi R S` says this of
`algebraMap R S`, in the equivalent form that the multiplication map `S ⊗[R] S → S` is
injective (`CommRingCat.epi_iff_epi`).

The tensor square governs everything here. A pair of ring maps out of `S` agreeing on `R` is one
ring map out of `S ⊗_R S`, so right-cancellability of `R → S` is the equality of the two
coprojections `s ↦ s ⊗ 1` and `s ↦ 1 ⊗ s`; the multiplication map `μ : S ⊗_R S → S` is the
codiagonal of that pushout, and each coprojection is a section of it, since `s * 1 = s = 1 * s`. A
retraction is bijective exactly when one of its sections is, and that ties the five conditions of
`CommRingCat.epi_tfae` together. Enlarging the base carries the identity `1 ⊗ c = c ⊗ 1` along the
comparison map `TensorProduct.mapOfCompatibleSMul : C ⊗_A C → C ⊗_B C`. Over a field, splitting off
the line `k · 1` by a linear functional `φ` turns that same identity into
`s = algebraMap k S (φ s)`. A ring map out of a residue field `κ(𝔮)` is determined by its
restriction to `S`, so `κ(𝔭) → κ(𝔮)` inherits right-cancellability from `R → S` and is therefore
surjective; being a map of fields it is bijective, and two primes of `S` over one prime of `R` are
then nested, each by a factorization of `S → κ(𝔮)` through the other's residue field.

## Main results

* `CommRingCat.epi_tfae`: for a ring map `R → S` the following are equivalent — it is an
  epimorphism; the two maps `S → S ⊗_R S` are equal; either one of them is bijective; the
  multiplication map `S ⊗_R S → S` is bijective.
* `Algebra.IsEpi.tower_top`: an epimorphism stays one over a larger base — for a tower
  `A → B → C` with `A → C` an epimorphism, `B → C` is an epimorphism.
* `Algebra.IsEpi.surjective_algebraMap_of_field`: an epimorphism out of a field is surjective.
* `PrimeSpectrum.comap_injective_and_residueFieldMap_bijective_of_isEpi`: for an epimorphism
  `R → S` the map `Spec S → Spec R` is injective, and the residue field extension at a prime of
  `S` and the prime of `R` below it is bijective.

## Implementation notes

Two spellings of the hypothesis are in play, and each statement takes the one that carries
content. `CommRingCat.epi_tfae` uses `CategoryTheory.Epi` in `CommRingCat`: `Algebra.IsEpi` is
*by definition* injectivity of the multiplication map, so using it would turn the last item into
a restatement of the first and lose the content of the lemma, which is that the categorical
condition is a condition on the tensor square. The other three use the class, which is
universe-polymorphic where `CommRingCat` confines its objects to one universe.
`CommRingCat.epi_iff_epi` transfers between the two.

`Algebra.IsEpi.tower_top` reads the source's hypothesis that `A → C` is the composite of
`A → B` and `B → C` as `IsScalarTower A B C`; without it the statement is false, as
`ℚ × ℚ → ℚ → ℚ × ℚ` (first projection, then the diagonal) shows. Read in `CommRingCat` the
lemma would be `CategoryTheory.epi_of_epi`, which holds in any category; over the class it is
instead the assertion that enlarging the base preserves injectivity of multiplication.

`Algebra.IsEpi.surjective_algebraMap_of_field` states the source's "`S = k` or `S = 0`" as
surjectivity of `algebraMap k S`, which over a field is equivalent to it and is the half that
carries the content: a subsingleton target makes every map onto it surjective, and conversely
`subsingleton_or_nontrivial` together with `RingHom.injective` recovers the disjunction. Its
target is only a `Ring`: the argument never multiplies two elements of `S`. That is why the
direct proof is taken rather than the source's alternative deduction from a faithfully flat
epimorphism being an isomorphism, which is a statement about commutative rings.

In `PrimeSpectrum.comap_injective_and_residueFieldMap_bijective_of_isEpi` the source's equality
`κ(𝔭) = κ(𝔮)` is bijectivity of the canonical map `Ideal.ResidueField.map`. It is *not*
strengthened to surjectivity of `R_𝔭 → S_𝔮`, which is false for epimorphisms: the fibre
computation gives only `S_𝔮 = image(R_𝔭) + 𝔭 S_𝔮`, and Nakayama upgrades that only when `S_𝔮`
is finite over `R_𝔭`, precisely the case where the strengthening is vacuous, since an
epimorphism that is finite is surjective. For a counterexample take the normalization of a
nodal cubic with one branch removed: over a field `k` of characteristic `≠ 2`, with
`R = k[t² - 1, t³ - t] ≅ k[x, y]/(y² - x³ - x²)` and `S = k[t][1/(t + 1)]`, the map `R → S` is
an epimorphism, and at the node `𝔭 = {f ∈ R : f(1) = 0}`, `𝔮 = (t - 1)S` one has
`κ(𝔭) = k = κ(𝔮)` while `t ∈ S_𝔮` is not in the image of `R_𝔭`. The two conclusions are
conjoined because they are the two halves of one computation and each uses the whole hypothesis;
neither follows from the other, the second failing for `ℚ → ℚ(X)` at `𝔭 = 𝔮 = (0)`, where the
first holds because `Spec ℚ(X)` is a point, and the first for `ℚ → ℚ × ℚ`, where the second
holds because both residue fields are `ℚ`.

The source computes the fibre of `Spec S → Spec R` over `𝔭` as the spectrum of `S ⊗_R κ(𝔭)`,
uses that base change preserves epimorphisms to see that `κ(𝔭) → S ⊗_R κ(𝔭)` is one, and then
applies the field case. The proof below is that argument with the fibre ring replaced by
`κ(𝔮)` itself, so the base change becomes right-cancellability of `κ(𝔭) → κ(𝔮)` and the tensor
product stays inside `Algebra.IsEpi`; the equality of residue fields is obtained first and the
injectivity on spectra follows from it rather than in parallel with it.

## References

* [Stacks Project, Tag 04VN](https://stacks.math.columbia.edu/tag/04VN)
* [Stacks Project, Tag 04VR](https://stacks.math.columbia.edu/tag/04VR)
* [Stacks Project, Tag 04VV](https://stacks.math.columbia.edu/tag/04VV)
* [Stacks Project, Tag 04VW](https://stacks.math.columbia.edu/tag/04VW)

## Tags

epimorphism of rings, tensor square, tower of algebras, field, prime spectrum, residue field
-/

@[expose] public section

universe u v

open TensorProduct

/-- A retraction is bijective exactly when one of its sections is: if `g ∘ f = id`, then `f` is
bijective if and only if `g` is. -/
private lemma bijective_iff_of_leftInverse {α β : Type*} {f : α → β} {g : β → α}
    (h : Function.LeftInverse g f) : Function.Bijective f ↔ Function.Bijective g :=
  ⟨fun hf ↦ ⟨(Function.RightInverse.leftInverse_of_surjective h hf.2).injective, h.surjective⟩,
    fun hg ↦ ⟨h.injective, (Function.RightInverse.leftInverse_of_injective h hg.1).surjective⟩⟩

section TensorSquare

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]

/-- A section of the multiplication map `S ⊗[R] S → S` is bijective exactly when the
multiplication map is; both inclusions `S → S ⊗[R] S` are such sections. -/
private lemma bijective_iff_bijective_lmul' {f : S →ₐ[R] S ⊗[R] S}
    (hf : (Algebra.TensorProduct.lmul' R).comp f = AlgHom.id R S) :
    Function.Bijective f ↔ Function.Bijective (Algebra.TensorProduct.lmul' (S := S) R) :=
  bijective_iff_of_leftInverse fun s ↦ congr($hf s)

/-- `R → S` is an epimorphism of algebras exactly when the multiplication map `S ⊗[R] S → S` is
bijective: it is injective by definition, and surjective always, `s` being the image of
`s ⊗ 1`. -/
private lemma isEpi_iff_bijective_lmul' :
    Algebra.IsEpi R S ↔ Function.Bijective (Algebra.TensorProduct.lmul' (S := S) R) :=
  ⟨fun h ↦ ⟨h.injective_lift_mul, fun s ↦ ⟨s ⊗ₜ 1, by simp⟩⟩, fun h ↦ ⟨h.injective⟩⟩

/-- `R → S` is an epimorphism of algebras exactly when the two inclusions `S → S ⊗[R] S` agree.
This is `Algebra.isEpi_iff_forall_one_tmul_eq` as an equality of algebra maps. -/
private lemma isEpi_iff_includeLeft_eq_includeRight :
    Algebra.IsEpi R S ↔
      (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] S)
        = Algebra.TensorProduct.includeRight :=
  (Algebra.isEpi_iff_forall_one_tmul_eq R S).trans <| by simp [AlgHom.ext_iff, eq_comm]

end TensorSquare

/-- **The tensor square detects a ring epimorphism** (Stacks 04VN). Let `R → S` be a ring map.
The following are equivalent: (1) `R → S` is an epimorphism of commutative rings; (2) the two
ring maps `S → S ⊗_R S`, namely `s ↦ s ⊗ 1` and `s ↦ 1 ⊗ s`, are equal; (3) `s ↦ s ⊗ 1` is an
isomorphism; (4) `s ↦ 1 ⊗ s` is an isomorphism; (5) the multiplication map `S ⊗_R S → S` is an
isomorphism. -/
@[stacks 04VN "Item (1) is `CategoryTheory.Epi` in `CommRingCat`, the source's categorical
notion, rather than the class `Algebra.IsEpi`, which is by definition injectivity of the
multiplication map and would make item (5) restate item (1); `CommRingCat.epi_iff_epi` transfers
between them. The source's `either of the ring maps` is the two items (3) and (4) below, one per
map, and `is an isomorphism` is `Function.Bijective`. See the module docstring."]
theorem CommRingCat.epi_tfae {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] :
    List.TFAE
      [CategoryTheory.Epi (CommRingCat.ofHom (algebraMap R S)),
       (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] S) = Algebra.TensorProduct.includeRight,
       Function.Bijective (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] S),
       Function.Bijective (Algebra.TensorProduct.includeRight : S →ₐ[R] S ⊗[R] S),
       Function.Bijective (Algebra.TensorProduct.lmul' (S := S) R)] := by
  tfae_have 1 ↔ 5 := CommRingCat.epi_iff_epi.trans (isEpi_iff_bijective_lmul' R S)
  tfae_have 2 ↔ 5 :=
    (isEpi_iff_includeLeft_eq_includeRight R S).symm.trans (isEpi_iff_bijective_lmul' R S)
  tfae_have 3 ↔ 5 := bijective_iff_bijective_lmul' R S (by simp)
  tfae_have 4 ↔ 5 := bijective_iff_bijective_lmul' R S (by simp)
  tfae_finish

namespace Algebra.IsEpi

/-- **An epimorphism of rings stays one over a larger base** (Stacks 04VR). If `A → B → C`
are ring maps, `A → C` being the composite, and `A → C` is an epimorphism, then `B → C` is
an epimorphism.

The proof transports the identity `1 ⊗ c = c ⊗ 1` along the base-enlargement comparison map
`TensorProduct.mapOfCompatibleSMul B A B C C : C ⊗[A] C →ₗ[B] C ⊗[B] C`, whose
`TensorProduct.CompatibleSMul B A C C` instance is where `IsScalarTower A B C` enters. -/
@[stacks 04VR "Epimorphy is Mathlib's `Algebra.IsEpi` (equivalently `CategoryTheory.Epi`
in `CommRingCat`, by `CommRingCat.epi_iff_epi`), and the source's hypothesis that `A → C`
is the composite `A → B → C` is `IsScalarTower A B C`. Named after its sibling
`Algebra.IsIntegral.tower_top`. See the module docstring."]
theorem tower_top {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C] [Algebra.IsEpi A C] :
    Algebra.IsEpi B C :=
  (Algebra.isEpi_iff_forall_one_tmul_eq B C).mpr fun c ↦
    congrArg (TensorProduct.mapOfCompatibleSMul B A B C C)
      ((Algebra.isEpi_iff_forall_one_tmul_eq A C).mp ‹Algebra.IsEpi A C› c)

/-- An epimorphism of rings `k → S` out of a field `k` is surjective; equivalently, `S = k` or
`S = 0`.

Over a field the line `k · 1 ⊆ S` is split off by a linear functional `φ : S →ₗ[k] k` with
`φ 1 = 1`; applying `φ` to the left factor of the identity `1 ⊗ s = s ⊗ 1` in `S ⊗[k] S` turns
it into `s = algebraMap k S (φ s)`. -/
@[stacks 04VV "The source's `S = k` or `S = 0` is stated as surjectivity of `algebraMap k S`,
which over a field is equivalent to it; the target need not be commutative. See the module
docstring."]
theorem surjective_algebraMap_of_field {k S : Type*} [Field k] [Ring S] [Algebra k S]
    [Algebra.IsEpi k S] : Function.Surjective (algebraMap k S) := by
  rcases subsingleton_or_nontrivial S with _ | _
  · exact fun s ↦ ⟨0, Subsingleton.elim _ _⟩
  obtain ⟨φ, hφ⟩ := (Algebra.linearMap k S).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap k S).injective)
  have hφ1 : φ (1 : S) = 1 := by simpa using LinearMap.congr_fun hφ 1
  refine fun s ↦ ⟨φ s, ?_⟩
  simpa [hφ1, Algebra.algebraMap_eq_smul_one] using
    congrArg (fun x ↦ TensorProduct.lid k S (φ.rTensor S x))
      ((Algebra.isEpi_iff_forall_one_tmul_eq k S).mp ‹Algebra.IsEpi k S› s).symm

end Algebra.IsEpi

section Cancellation

/-- An epimorphism of rings is right-cancellable: two ring maps out of `S` agreeing on `R` are
equal. This is `Epi (CommRingCat.ofHom (algebraMap R S))` unfolded, without the restriction to
a single universe that `CommRingCat.epi_iff_epi` carries. -/
private theorem ringHom_ext_of_isEpi {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    [Algebra.IsEpi R S] {U : Type*} [CommSemiring U] {f g : S →+* U}
    (h : f.comp (algebraMap R S) = g.comp (algebraMap R S)) : f = g := by
  let _ : Algebra R U := (g.comp (algebraMap R S)).toAlgebra
  let f' : S →ₐ[R] U := ⟨f, fun r ↦ (RingHom.congr_fun h r).trans rfl⟩
  let g' : S →ₐ[R] U := ⟨g, fun _ ↦ rfl⟩
  refine RingHom.ext fun s ↦ show f' s = g' s from ?_
  simpa only [Algebra.TensorProduct.lift_tmul, map_one, one_mul, mul_one] using
    (congrArg (Algebra.TensorProduct.lift f' g' fun _ _ ↦ Commute.all _ _)
      ((Algebra.isEpi_iff_forall_one_tmul_eq R S).mp ‹Algebra.IsEpi R S› s)).symm

/-- Converse to `ringHom_ext_of_isEpi`: an `R`-algebra `S` whose structure map is
right-cancellable among ring maps to commutative targets in the universe of `S` is an
epimorphism. The witness is `S ⊗[R] S`, which is where both the universe and the commutativity
of the targets come from. -/
private theorem isEpi_of_ringHom_ext {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] (h : ∀ {U : Type v} [CommRing U] (f g : S →+* U),
      f.comp (algebraMap R S) = g.comp (algebraMap R S) → f = g) : Algebra.IsEpi R S := by
  refine (Algebra.isEpi_iff_forall_one_tmul_eq R S).mpr fun s ↦ ?_
  refine (RingHom.congr_fun (h Algebra.TensorProduct.includeLeftRingHom
    (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := S)).toRingHom ?_) s).symm
  ext r
  change algebraMap R S r ⊗ₜ[R] (1 : S) = 1 ⊗ₜ[R] algebraMap R S r
  simp only [Algebra.algebraMap_eq_smul_one, smul_tmul]

/-- A ring map is an epimorphism in `CommRingCat` exactly when it is right-cancellable among ring
maps to commutative rings of the same universe. -/
private theorem epi_ofHom_iff_ringHom_ext {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) :
    CategoryTheory.Epi (CommRingCat.ofHom f) ↔
      ∀ (T : Type u) [CommRing T] (g h : S →+* T), g.comp f = h.comp f → g = h := by
  let := f.toAlgebra
  rw [CommRingCat.epi_iff_epi (R := R) (S := S)]
  exact ⟨fun _ T _ g h hgh ↦ ringHom_ext_of_isEpi hgh,
    fun H ↦ isEpi_of_ringHom_ext fun g h ↦ H _ g h⟩

/-- A right-cancellable ring map out of a field is surjective: the bare ring map form of Stacks
04VV. Right-cancellability is asked for among commutative targets only, which is all that
`isEpi_of_ringHom_ext` needs. -/
private theorem surjective_of_ringHom_ext {k : Type u} {L : Type v} [Field k] [CommRing L]
    (φ : k →+* L)
    (h : ∀ {U : Type v} [CommRing U] (f g : L →+* U), f.comp φ = g.comp φ → f = g) :
    Function.Surjective φ :=
  let : Algebra k L := φ.toAlgebra
  have : Algebra.IsEpi k L := isEpi_of_ringHom_ext h
  Algebra.IsEpi.surjective_algebraMap_of_field (k := k) (S := L)

end Cancellation

namespace PrimeSpectrum

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsEpi R S]

/-- For an epimorphism `R → S` and a prime `𝔮 ⊆ S` lying over `𝔭 ⊆ R`, the canonical map
`κ(𝔭) → κ(𝔮)` is surjective.

A ring map out of `κ(𝔮)` is determined by its restriction to `S`, so two ring maps out of
`κ(𝔮)` agreeing on `κ(𝔭)` agree on `R`, hence on `S`, hence are equal; thus `κ(𝔭) → κ(𝔮)` is
right-cancellable, and `surjective_of_ringHom_ext` applies. -/
private theorem surjective_residueFieldMap (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    (h : p = q.comap (algebraMap R S)) :
    Function.Surjective (Ideal.ResidueField.map p q (algebraMap R S) h) := by
  refine surjective_of_ringHom_ext _ fun {U} _ f g hfg ↦ Ideal.ResidueField.ringHom_ext
    (ringHom_ext_of_isEpi (R := R) (RingHom.ext fun r ↦ ?_))
  simpa using RingHom.congr_fun hfg (algebraMap R p.ResidueField r)

/-- For an epimorphism `R → S`, two primes of `S` lying over the same prime `𝔭` of `R` are
nested.

By `surjective_residueFieldMap` the canonical map `κ(𝔭) → κ(𝔮₁)` is an isomorphism, so
`S → κ(𝔮₂)` factors as `S → κ(𝔮₁) ≅ κ(𝔭) → κ(𝔮₂)` — the two maps `S → κ(𝔮₂)` agree on `R`,
hence are equal — and a factorization puts the kernel `𝔮₁` of `S → κ(𝔮₁)` inside the kernel
`𝔮₂` of `S → κ(𝔮₂)`. -/
private theorem le_of_comap_eq (p : Ideal R) [p.IsPrime] {q₁ q₂ : Ideal S} [q₁.IsPrime]
    [q₂.IsPrime] (h₁ : p = q₁.comap (algebraMap R S)) (h₂ : p = q₂.comap (algebraMap R S)) :
    q₁ ≤ q₂ := by
  let e : p.ResidueField ≃+* q₁.ResidueField :=
    .ofBijective (Ideal.ResidueField.map p q₁ (algebraMap R S) h₁)
      ⟨RingHom.injective _, surjective_residueFieldMap p q₁ h₁⟩
  have key : ((Ideal.ResidueField.map p q₂ (algebraMap R S) h₂).comp
      (e.symm : q₁.ResidueField →+* p.ResidueField)).comp (algebraMap S q₁.ResidueField) =
      algebraMap S q₂.ResidueField := by
    refine ringHom_ext_of_isEpi (R := R) (RingHom.ext fun r ↦ ?_)
    have hr : algebraMap S q₁.ResidueField (algebraMap R S r) =
        e (algebraMap R p.ResidueField r) :=
      (Ideal.ResidueField.map_algebraMap p q₁ (algebraMap R S) h₁ r).symm
    simp [hr]
  intro x hx
  rw [← Ideal.algebraMap_residueField_eq_zero, ← key]
  simp [Ideal.algebraMap_residueField_eq_zero.mpr hx]

end

/-- Let `R → S` be an epimorphism of rings. Then `Spec S → Spec R` is injective, and for every
prime `𝔮 ⊆ S` lying over a prime `𝔭 ⊆ R` the canonical residue field extension
`κ(𝔭) → κ(𝔮)` is bijective, that is, `κ(𝔭) = κ(𝔮)`. -/
@[stacks 04VW "The equality `κ(𝔭) = κ(𝔮)` of part (2) is bijectivity of the canonical map
`Ideal.ResidueField.map`; it is not surjectivity of `R_𝔭 → S_𝔮`, which is false for
epimorphisms. See the module docstring."]
theorem comap_injective_and_residueFieldMap_bijective_of_isEpi
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsEpi R S] :
    Function.Injective (comap (algebraMap R S)) ∧
      ∀ (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] (h : p = q.comap (algebraMap R S)),
        Function.Bijective (Ideal.ResidueField.map p q (algebraMap R S) h) := by
  refine ⟨fun q₁ q₂ hq ↦ ?_, fun p _ q _ h ↦
    ⟨RingHom.injective _, surjective_residueFieldMap p q h⟩⟩
  have h : q₁.asIdeal.comap (algebraMap R S) = q₂.asIdeal.comap (algebraMap R S) := by
    simpa using congrArg PrimeSpectrum.asIdeal hq
  exact PrimeSpectrum.ext (le_antisymm (le_of_comap_eq _ rfl h) (le_of_comap_eq _ h rfl))

end PrimeSpectrum

end

section

/-!
# Composition of epimorphisms of rings

The composition of two epimorphisms of rings is an epimorphism. This is the case
`C = CommRingCat` of the general categorical fact `CategoryTheory.epi_comp`.
-/

add_to_stacks 04VP "The case `C = CommRingCat` of the general categorical fact."
  CategoryTheory.epi_comp
add_to_sga "3 IV 1.4" CategoryTheory.epi_comp

end

/-!
# Base change of an epimorphism is an epimorphism

If `R → S` is an epimorphism in `CommRingCat` and `R → R'` is any ring map,
then `R' → R' ⊗_R S` is an epimorphism.
-/

@[expose] public section

open CategoryTheory TensorProduct

/-- In `R' ⊗[R] S`, the tensor `1 ⊗ algebraMap R S r` equals
`algebraMap R R' r ⊗ 1`. -/
lemma includeLeft_algebraMap_eq_includeRight_aux
    (R R' S : Type) [CommRing R] [CommRing R'] [CommRing S]
    [Algebra R R'] [Algebra R S] (r : R) :
    ((1 : R') ⊗ₜ[R] (algebraMap R S r) : TensorProduct R R' S) =
      (algebraMap R R' r) ⊗ₜ[R] (1 : S) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

/-- An arrow in `CommRingCat` is epi iff it is right-cancellable for ring
homomorphisms into arbitrary commutative rings. -/
lemma commRingCat_epi_iff_right_cancel
    {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) :
    Epi (CommRingCat.ofHom φ) ↔
      ∀ (T : Type) [CommRing T] (f g : B →+* T),
        f.comp φ = g.comp φ → f = g :=
  epi_ofHom_iff_ringHom_ext φ

/-- Two ring homomorphisms out of `R' ⊗[R] S` are equal iff they agree on
elementary tensors `r' ⊗ 1` and `1 ⊗ s`. -/
lemma ringHom_tensor_ext_left_right
    (R R' S T : Type) [CommRing R] [CommRing R'] [CommRing S] [CommRing T]
    [Algebra R R'] [Algebra R S]
    (f g : TensorProduct R R' S →+* T)
    (hL : ∀ r' : R', f (r' ⊗ₜ[R] (1 : S)) = g (r' ⊗ₜ[R] (1 : S)))
    (hR : ∀ s : S, f ((1 : R') ⊗ₜ[R] s) = g ((1 : R') ⊗ₜ[R] s)) :
    f = g := by
  refine RingHom.ext fun x => ?_
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    rw [← mul_one a, ← one_mul b, ← Algebra.TensorProduct.tmul_mul_tmul, map_mul, map_mul, hL, hR]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- **Base change of an epimorphism is an epimorphism.** If `R → S` is an
epimorphism in `CommRingCat` and `R → R'` is any ring map, then the canonical
ring map `R' → R' ⊗_R S` is an epimorphism. -/
@[stacks 04VQ]
theorem epi_includeLeftRingHom_of_epi
    (R R' S : Type) [CommRing R] [CommRing R'] [CommRing S]
    [Algebra R R'] [Algebra R S]
    (h : Epi (CommRingCat.ofHom (algebraMap R S))) :
    Epi (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom :
        R' →+* TensorProduct R R' S)) := by
  rw [commRingCat_epi_iff_right_cancel] at h ⊢
  intro T _ f g hfg
  have hR : f.comp Algebra.TensorProduct.includeRight.toRingHom =
      g.comp Algebra.TensorProduct.includeRight.toRingHom := by
    refine h T _ _ (RingHom.ext fun r => ?_)
    simpa [includeLeft_algebraMap_eq_includeRight_aux] using congrArg (· (algebraMap R R' r)) hfg
  exact ringHom_tensor_ext_left_right R R' S T f g (fun r' => congrArg (· r') hfg)
    (fun s => congrArg (· s) hR)

end

/-!
# Being an epimorphism is a local property of a ring map

All rings are commutative with unit and all ring maps are unital.

A ring map `f : R → S` is an *epimorphism* if it is an epimorphism in the category of
commutative rings; that is, for every ring `T` and every pair of ring maps `g, h : S → T`, the
equality `g ∘ f = h ∘ f` implies `g = h`.

For a prime ideal `p` of `R`, the localization `R_p` is the localization of `R` at the
multiplicative set `R \ p`, with its canonical map `R → R_p`. Given `f : R → S`, the ring
`S_p` is the localization of `S` at the multiplicative subset `f(R \ p) ⊆ S`. It carries a
canonical `R_p`-algebra structure making the square
```
  R  ---->  S
  |         |
  v         v
  R_p ----> S_p
```
commute; the induced map below is the bottom horizontal map `R_p → S_p`.

## Main result

For a ring map `f : R → S`, the following are equivalent:

1. `f` is an epimorphism of rings;
2. for every prime ideal `p` of `R`, the induced ring map `R_p → S_p` is an epimorphism.

## Implementation notes

In the category of commutative rings, `f` is an epimorphism if and only if the multiplication
map `S ⊗[R] S → S` is an isomorphism. The categorical definition, epimorphism in
`CommRingCat`, is used directly, as the literal translation of the universal property.
-/

@[expose] public section

open CategoryTheory

universe u

/-- A ring map `f` is an epimorphism in `CommRingCat` exactly when it satisfies the elementary
universal property of an epimorphism of rings. -/
theorem CommRingCat.epi_ofHom_iff {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    Epi (CommRingCat.ofHom f) ↔
      ∀ (T : Type u) [CommRing T] (g h : S →+* T), g.comp f = h.comp f → g = h :=
  epi_ofHom_iff_ringHom_ext f

/-- The multiplicative subset `f(R \ p) = f(R \ p)` of `S` along which `S_p` is
formed: the image under `f` of the prime complement of `p`. -/
def mappedPrimeCompl {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (p : Ideal R) [p.IsPrime] : Submonoid S :=
  (p.primeCompl).map f

/-- `mappedPrimeCompl f p` is Mathlib's `Algebra.algebraMapSubmonoid` for the algebra
structure `f.toAlgebra`; stating it lets consumers rewrite instead of relying on the
two spellings being definitionally equal. -/
theorem mappedPrimeCompl_eq {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (p : Ideal R) [p.IsPrime] :
    letI := f.toAlgebra; mappedPrimeCompl f p = Algebra.algebraMapSubmonoid S p.primeCompl :=
  rfl

/-- The localization `S_p` of `S` at the image `f(R \ p)` of the prime
complement of `p`. -/
@[ega "0 19.8.3"]
abbrev LocalizationS {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (p : Ideal R) [p.IsPrime] : Type u :=
  Localization (mappedPrimeCompl f p)

/-- The induced ring map `R_p → S_p` on localizations. It is the unique ring map
making the localization square commute, obtained from `f : R →+* S` by the
universal property of localization, using that `f` carries `R \ p` into
`f(R \ p)`. -/
@[ega "0 1.5.1" "special case"]
noncomputable def inducedLocalizationMap {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (p : Ideal R) [p.IsPrime] :
    Localization.AtPrime p →+* LocalizationS f p :=
  IsLocalization.map (M := p.primeCompl) (T := mappedPrimeCompl f p) _ f
    (fun _ hx => Submonoid.mem_comap.mpr (Submonoid.mem_map_of_mem f hx))

/-- The localization square `R → R_p → S_p = R → S → S_p` commutes. -/
theorem inducedLocalizationMap_comp_algebraMap {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (p : Ideal R) [p.IsPrime] :
    (inducedLocalizationMap f p).comp (algebraMap R (Localization.AtPrime p)) =
      (algebraMap S (LocalizationS f p)).comp f :=
  IsLocalization.map_comp _

section TensorChar

open TensorProduct

/-- Epi characterization via the tensor product. Under the `R`-algebra
structure on `S` given by `f`, `f` is an epimorphism iff `s ⊗ₜ 1 = 1 ⊗ₜ s`
for every `s : S`. -/
theorem CommRingCat.epi_ofHom_iff_tmul {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    Epi (CommRingCat.ofHom f) ↔
      letI := f.toAlgebra
      ∀ s : S, (s ⊗ₜ[R] (1 : S) : TensorProduct R S S) = 1 ⊗ₜ[R] s := by
  let := f.toAlgebra
  exact CommRingCat.epi_iff_epi.trans
    ((Algebra.isEpi_iff_forall_one_tmul_eq R S).trans (forall_congr' fun _ ↦ eq_comm))

end TensorChar

section Locality

open TensorProduct

/-- **Local-to-global vanishing of a module element.** If an element `t` of an
`R`-module `M` maps to `0` in the localization `M_J` for every maximal ideal
`J` of `R`, then `t = 0`.

*Informal proof.* This is the standard "an element vanishing in every maximal
localization is zero" fact (Stacks 00HN, the element form). Concretely, apply
`injective_of_localized_maximal` to the `R`-linear map
`LinearMap.toSpanSingleton R M t : R →ₗ[R] M`, `r ↦ r • t`. Localization
commutes with `toSpanSingleton`: the localized map at `J` is
`toSpanSingleton R_J M_J ((mk 1) t)`. By hypothesis `(mk 1) t = 0` in `M_J`, so
the localized map is the zero map, hence injective iff `M_J = 0`... — actually
the clean route is the contrapositive via the annihilator/`Submodule.span`:
`t = 0 ↔ Submodule.span R {t} = ⊥`, and a submodule is `⊥` iff it is `⊥` after
localizing at every maximal ideal (`Submodule.eq_bot_of_localization_maximal` /
`Submodule.localized'_bot`). Equivalently, use that `LocalizedModule.mkLinearMap`
is, for the family over all maximal `J`, jointly injective (this is exactly the
content of `injective_of_localized_maximal` applied to the inclusion
`Submodule.span R {t} ↪ M`, or to `id : M → M`). -/
@[ega "0 1.7.1" "partial", sga "3 V 4.1.3" "more general"]
theorem eq_zero_of_localized_maximal {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] (t : M)
    (h : ∀ (J : Ideal R) [J.IsMaximal],
      (LocalizedModule.mkLinearMap J.primeCompl M) t = 0) :
    t = 0 :=
  -- Stacks 00HN, supplied by Mathlib's `Module.eq_zero_of_localization_maximal`
  -- instantiated with the family `Mₚ J := LocalizedModule J.primeCompl M` and
  -- the localization maps `LocalizedModule.mkLinearMap J.primeCompl M`.
  Module.eq_zero_of_localization_maximal
    (Mₚ := fun P _ => LocalizedModule P.primeCompl M)
    (fun P _ => LocalizedModule.mkLinearMap P.primeCompl M) t h

/-- **Local vanishing of `s ⊗ₜ 1 - 1 ⊗ₜ s`.** Assume every induced localization
map `R_p →+* S_p` is a ring epimorphism. Then for every maximal ideal `J` of `R`
and every `s : S`, the element `s ⊗ₜ 1 - 1 ⊗ₜ s` of `S ⊗[R] S` maps to `0` in
the localization `(S ⊗[R] S)_J`.

*Informal proof.* Fix a maximal (hence prime) ideal `J` and `s : S`. Write
`M := S ⊗[R] S` and let `μ : M → M_J` be the localization map. The localization
`M_J = (S ⊗_R S)_J` is, as an `R_J`-module, naturally isomorphic to
`S_J ⊗_{R_J} S_J`: localization is exact (Stacks 00CS,
`LocalizedModule.map_exact`) and is base change along `R → R_J`, i.e. commutes
with tensor products (Stacks 00DK,
`IsLocalization.tensorProduct_isLocalizedModule`). Under this isomorphism the
image `μ(s ⊗ₜ 1)` corresponds to `(s/1) ⊗ₜ (1) = s' ⊗ₜ 1` and `μ(1 ⊗ₜ s)` to
`1 ⊗ₜ s'`, where `s' := algebraMap S S_J s` is the image of `s` in `S_J`.
Therefore `μ(s ⊗ₜ 1 - 1 ⊗ₜ s)` corresponds to `s' ⊗ₜ 1 - 1 ⊗ₜ s'` in
`S_J ⊗_{R_J} S_J`. Now `inducedLocalizationMap f J : R_J →+* S_J` is a ring
epimorphism by hypothesis `hloc J`, so by `CommRingCat.epi_ofHom_iff_tmul` (applied to that
map, with `S_J` carrying its `R_J`-algebra structure) we have
`s' ⊗ₜ 1 = 1 ⊗ₜ s'`, i.e. `s' ⊗ₜ 1 - 1 ⊗ₜ s' = 0`. Transporting back through
the isomorphism gives `μ(s ⊗ₜ 1 - 1 ⊗ₜ s) = 0`. -/
theorem localized_tmul_sub_eq_zero {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (hloc : ∀ (p : Ideal R) [p.IsPrime], Epi (CommRingCat.ofHom (inducedLocalizationMap f p)))
    (J : Ideal R) [J.IsMaximal] (s : S) :
    letI := f.toAlgebra
    (LocalizedModule.mkLinearMap J.primeCompl (TensorProduct R S S))
        (s ⊗ₜ[R] (1 : S) - 1 ⊗ₜ[R] s) = 0 := by
  let := f.toAlgebra
  set RJ := Localization.AtPrime J
  set SJ := LocalizationS f J
  let : Algebra RJ SJ := (inducedLocalizationMap f J).toAlgebra
  -- the scalar tower R → R_J → S_J
  have : IsScalarTower R RJ SJ :=
    IsScalarTower.of_algebraMap_eq' (inducedLocalizationMap_comp_algebraMap f J).symm
  -- S → S_J is a localization of S-modules at J.primeCompl
  have : IsLocalizedModule J.primeCompl (IsScalarTower.toAlgHom R S SJ).toLinearMap :=
    isLocalizedModule_iff_isLocalization.mpr
      (mappedPrimeCompl_eq f J ▸ inferInstanceAs (IsLocalization (mappedPrimeCompl f J) SJ))
  -- base change isomorphism R_J ⊗_R S ≃ S_J
  have hbcS : IsBaseChange RJ (IsScalarTower.toAlgHom R S SJ).toLinearMap :=
    IsLocalizedModule.isBaseChange J.primeCompl RJ _
  let eS : TensorProduct R RJ S ≃ₗ[RJ] SJ := hbcS.equiv
  -- big base change isomorphism R_J ⊗_R (S ⊗_R S) ≃ S_J ⊗_{R_J} S_J
  let e : TensorProduct R RJ (TensorProduct R S S) ≃ₗ[RJ] TensorProduct RJ SJ SJ :=
    (TensorProduct.AlgebraTensorModule.distribBaseChange R RJ S S) ≪≫ₗ
      (TensorProduct.AlgebraTensorModule.congr eS eS)
  let mk1 : TensorProduct R S S →ₗ[R] TensorProduct R RJ (TensorProduct R S S) :=
    TensorProduct.mk R RJ (TensorProduct R S S) 1
  have : IsLocalizedModule J.primeCompl mk1 :=
    IsLocalization.tensorProduct_isLocalizedModule J.primeCompl RJ
  -- the natural map g : (S ⊗_R S) → S_J ⊗_{R_J} S_J, again a localization at J.primeCompl
  let g : TensorProduct R S S →ₗ[R] TensorProduct RJ SJ SJ :=
    (e.restrictScalars R).toLinearMap ∘ₗ mk1
  have : IsLocalizedModule J.primeCompl g :=
    IsLocalizedModule.of_linearEquiv J.primeCompl mk1 (e.restrictScalars R)
  -- compute g on simple tensors
  have hes (a : S) : eS (1 ⊗ₜ[R] a) = (IsScalarTower.toAlgHom R S SJ) a := by
    simp [eS, IsBaseChange.equiv_tmul]
  have hg : ∀ a b : S, g (a ⊗ₜ[R] b)
      = (IsScalarTower.toAlgHom R S SJ a) ⊗ₜ[RJ] (IsScalarTower.toAlgHom R S SJ b) := by
    intro a b
    change (TensorProduct.AlgebraTensorModule.congr eS eS)
        ((TensorProduct.AlgebraTensorModule.distribBaseChange R RJ S S)
          (1 ⊗ₜ[R] (a ⊗ₜ[R] b))) = _
    rw [TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
        TensorProduct.AlgebraTensorModule.congr_tmul, hes, hes]
  -- g sends s ⊗ 1 - 1 ⊗ s to 0, by the epimorphism property at J
  have hgker : g (s ⊗ₜ[R] (1 : S) - 1 ⊗ₜ[R] s) = 0 := by
    rw [map_sub, hg, hg, map_one,
      (CommRingCat.epi_ofHom_iff_tmul (inducedLocalizationMap f J)).mp (hloc J), sub_self]
  -- transport back through the canonical isomorphism of localizations
  refine (IsLocalizedModule.linearEquiv J.primeCompl
    (LocalizedModule.mkLinearMap J.primeCompl (TensorProduct R S S)) g).map_eq_zero_iff.mp ?_
  rw [IsLocalizedModule.linearEquiv_apply, hgker]

end Locality

/-- **Stacks Tag 04VS.** Being an epimorphism is a local property of a ring
map: a ring map `f : R →+* S` is an epimorphism of rings if and only if for
every prime ideal `p` of `R`, the induced map `R_p →+* S_p` is an epimorphism of
rings. -/
@[stacks 04VS]
theorem CommRingCat.epi_ofHom_iff_forall_prime {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) :
    Epi (CommRingCat.ofHom f) ↔
      ∀ (p : Ideal R) [p.IsPrime], Epi (CommRingCat.ofHom (inducedLocalizationMap f p)) := by
  refine ⟨fun hf p _ ↦ ?_, fun hloc ↦ ?_⟩
  · -- Forward: epimorphisms localize (base change / cancellation argument).
    -- The square R → R_p → S_p = R → S → S_p commutes; R → S → S_p is epi as a
    -- composite of epis (f epi, localization S → S_p epi via IsLocalization.epi),
    -- hence R_p → S_p is epi by right-cancellation (CategoryTheory.epi_of_epi).
    have hsq : (CommRingCat.ofHom (algebraMap R (Localization.AtPrime p))) ≫
          (CommRingCat.ofHom (inducedLocalizationMap f p)) =
        (CommRingCat.ofHom f) ≫
          (CommRingCat.ofHom (algebraMap S (LocalizationS f p))) := by
      rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
        inducedLocalizationMap_comp_algebraMap]
    have := IsLocalization.epi (mappedPrimeCompl f p) (LocalizationS f p)
    exact epi_of_epi_fac hsq
  · -- Reverse: locality of "s ⊗ 1 = 1 ⊗ s".
    -- By `CommRingCat.epi_ofHom_iff_tmul`, it suffices to show `t := s⊗1 - 1⊗s = 0` in
    -- `S ⊗[R] S` for every `s`. By `eq_zero_of_localized_maximal` it suffices to
    -- show `t` vanishes in `(S⊗_R S)_J` for every maximal `J`, which is exactly
    -- `localized_tmul_sub_eq_zero` (using the localized epi hypothesis `hloc`).
    rw [CommRingCat.epi_ofHom_iff_tmul]
    let := f.toAlgebra
    exact fun s => sub_eq_zero.mp
      (eq_zero_of_localized_maximal _ fun J _ => localized_tmul_sub_eq_zero f hloc J s)

end

add_to_stacks 04VT "a ring map is surjective iff it is a finite epimorphism"
  RingHom.surjective_iff_epi_and_finite

/-!
# A faithfully flat epimorphism of rings is an isomorphism

Throughout, `R` and `S` are commutative rings and `φ : R → S` is a ring homomorphism, making
`S` an `R`-algebra, so that `φ = algebraMap R S`. The `R`-module structure on `S` is the one
induced by `φ`, that is `r • s = φ r * s`.

The three notions involved:

* `φ` is an *epimorphism* of rings if for every ring `T` and every pair of ring homomorphisms
  `f, g : S → T` with `f ∘ φ = g ∘ φ` one has `f = g`. This is `Algebra.IsEpi R S`, and it is
  equivalent to `1 ⊗ a = a ⊗ 1` in `S ⊗[R] S` for every `a : S`
  (`Algebra.isEpi_iff_forall_one_tmul_eq`).
* An `R`-module `M` is *faithfully flat* if it is flat and `- ⊗[R] M` reflects exactness;
  equivalently, `M` is flat and `N ⊗[R] M ≠ 0` for every nonzero `R`-module `N`. This is
  `Module.FaithfullyFlat R M`.
* `φ` is an *isomorphism* if it is bijective. A bijective ring homomorphism between
  commutative rings is automatically a ring isomorphism, so this is rendered as
  `Function.Bijective (algebraMap R S)`.

## Main result

`faithfullyFlat_epimorphism_isIso`: if `φ` is an epimorphism of rings and `S` is faithfully
flat as an `R`-module, then `φ` is bijective.

Since `φ` is an epimorphism, the ring map `S → S ⊗[R] S`, `s ↦ s ⊗ 1`, is an isomorphism, and
this map is `φ` base-changed along `S`. Because `S` is faithfully flat over `R`, a map of
`R`-modules is an isomorphism if and only if it becomes one after applying `S ⊗[R] -`. As the
base change of `φ` along the faithfully flat `S` is an isomorphism, so is `φ`.
-/

@[expose] public section

/-- If `algebraMap R S` is an epimorphism of commutative rings and `S` is faithfully flat as
an `R`-module, then `algebraMap R S` is bijective, i.e. an isomorphism of rings. -/
@[stacks 04VU, sga "3 VIB 12.1" "affine case", sga "3 XI 3.9" "Affine case"]
theorem faithfullyFlat_epimorphism_isIso
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsEpi R S] [Module.FaithfullyFlat R S] :
    Function.Bijective (algebraMap R S) := by
  open TensorProduct in
  -- It suffices to prove that `Algebra.linearMap R S` is bijective.
  suffices h : Function.Bijective (Algebra.linearMap R S) from h
  -- By faithful flatness of `S`, a map of `R`-modules is bijective iff its
  -- base change `S ⊗[R] -` is bijective.
  rw [← Module.FaithfullyFlat.lTensor_bijective_iff_bijective R S
    (Algebra.linearMap R S)]
  -- The base change `lTensor S (Algebra.linearMap R S)` factors as the
  -- section `σ : s ↦ s ⊗ₜ 1` composed with the isomorphism `S ⊗[R] R ≃ S`.
  have hfac : LinearMap.lTensor S (Algebra.linearMap R S)
      = ((TensorProduct.mk R S S).flip 1) ∘ₗ (TensorProduct.rid R S).toLinearMap := by
    ext s
    simp [Algebra.linearMap]
  rw [hfac]
  -- `σ` is bijective: the multiplication map `μ = lift (mul R S)` is its inverse.
  have hσbij : Function.Bijective (⇑((TensorProduct.mk R S S).flip 1) : S → S ⊗[R] S) := by
    have hμσ : ∀ s, TensorProduct.lift (LinearMap.mul R S) ((TensorProduct.mk R S S).flip 1 s) =
        s := fun s ↦ by simp
    exact ⟨Function.LeftInverse.injective hμσ,
      fun y ↦ ⟨_, Algebra.IsEpi.injective_lift_mul (hμσ _)⟩⟩
  -- The composite of `σ` with the isomorphism `rid` is bijective.
  rw [LinearMap.coe_comp]
  exact hσbij.comp (TensorProduct.rid R S).bijective

end
