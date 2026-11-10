module

public import StacksFrontier.AlgebraicGeometry.Curves.NodalVectorFields
public import StacksFrontier.AlgebraicGeometry.Curves.NodeQuadraticAlgebra.Conductor

/-!
# The exact sequence of a node and its normalization

Let `A` be a nodal local algebra over a field `k` and let
`A' = integralClosure A (FractionRing A)` be its normalization inside its total ring of
fractions. Suppose the two branches of the node are rational, that is, that `A'` carries two
distinct `k`-algebra maps `ε₁, ε₂ : A' → k` agreeing on the image of `A`. Then

```
0 → A → A' → k → 0
```

is exact, with the second map `t ↦ ε₁ t - ε₂ t`: the image of `A` in `A'` is exactly the set of
elements whose two residues agree. For `A = 𝒪_{X, x}` the local ring at a node of a curve and
`ε₁`, `ε₂` the residues at the two points of the normalization above `x`, this is the sequence

```
0 → 𝒪_{X, x} → 𝒪_{X^ν, x'} × 𝒪_{X^ν, x''} → k → 0
```

that the proof of Tag 0E68 derives from Tag 0C1X, and the identification of the image is the
"set of elements having the same residue classes in `k`" of the proof of Tag 0C1X.

The consequence Tag 0E68 needs is immediate from it: a `k`-derivation of `A'` fixing the two
points of the normalization carries the subring `A` into itself, and therefore restricts to a
`k`-derivation of `A`.

## Main definitions

There are no definitions.

## Main results

* `Stacks.Curves.surjective_sub_of_ne` — the difference of two distinct `k`-algebra maps to `k`
  is surjective, so the sequence is exact on the right.
* `Stacks.Curves.mem_range_iff_of_isCoatom` — the criterion: when the image of `A` is a coatom,
  it is cut out by the equality of two distinct `k`-algebra maps to `k` that agree on it.
* `Stacks.Curves.range_algebraMap_integralClosure_eq_equalizer` — the image of `A` in `A'` is
  the set of elements with equal residues at the two branches.
* `Stacks.Curves.exact_integralClosure_of_isNodalAlgebra` — the three exactness statements of
  `0 → A → A' → k → 0` together.
* `Stacks.Curves.nodeAlg_eq_range_algebraMap_integralClosure` — when the normalization is a
  product `B₁ × B₂` of the two branches, the image of `A` is the node algebra
  `Stacks.Curves.NodalVectorFields.nodeAlg` of the two augmented branches.
* `Stacks.Curves.mem_range_algebraMap_of_fixes` — a `k`-derivation of `A'` fixing the two
  branch points carries the image of `A` into itself.
* `Stacks.Curves.existsUnique_restrict_of_fixes` — such a derivation therefore restricts
  uniquely to `A`.

## Implementation notes

The whole weight of the identification of the image rests on one fact: the image of `A`
in `A'` is a *coatom* in the lattice of `A`-submodules of `A'`
(`Stacks.Curves.isCoatom_range_algebraMap_integralClosure_of_isNodalAlgebra`, the computation
behind `Ring.deltaInvariant A = 1`). The equalizer of `ε₁` and `ε₂` is an `A`-submodule
containing the image — that is what the agreement hypothesis says — and it is not everything
because `ε₁ ≠ ε₂`; a coatom has nothing strictly between it and the top, so the two coincide.
That argument uses nothing about the normalization, so it is stated for an arbitrary `A`-algebra
in `Stacks.Curves.mem_range_iff_of_isCoatom`, and likewise for the two derivation statements.
Neither the splitting behaviour of the quadratic relation nor the count of maximal ideals of
`A'` is used; what plays the role of "the node is split with rational branches" is exactly the
existence of the two distinct maps to `k`.

The branches are presented as `k`-algebra maps `A' → k` rather than as maximal ideals of `A'`
together with identifications of their residue fields, because that is the form in which the
node algebra of `Stacks.Curves.NodalVectorFields` and its `Fixes` condition are stated, so no
transport along a residue-field isomorphism is needed anywhere. For a node of a curve over an
algebraically closed field the two presentations agree: a `k`-algebra map `A' → k` has maximal
kernel, and a maximal ideal of `A'` has residue field `k`.

The agreement hypothesis is not vacuous and not automatic: it says that the two branch residues
restrict to the *same* map on `A`, which is what makes the node one point of `X` rather than
two. It holds whenever the residue field of `A` is `k`, since a local `k`-algebra map to a field
kills the maximal ideal.

## What is not done here

The passage from this local statement to the sheaves `𝒪_X` and `𝒪_{X^ν}` is not carried out in
this file; it is `Stacks.Curves.existsUnique_descend_normalization_of_fixes`, which feeds
`Stacks.Curves.mem_range_algebraMap_of_fixes` into the sheaf-level descent criterion. The
converse direction of Tag 0E68 — extending a derivation of `A` to `A'`, which the source gets
from `𝒪_{X^ν, x'} = k + (u)` — is
`Stacks.Curves.existsUnique_extend_integralClosure_of_isNodalAlgebra`, which gets it from the
exact sequence proved in this file instead; the two directions are assembled into the tag by
`Stacks.Curves.NodalVectorFields.range_branchPair`. The hypothesis that the
normalization of
the stalk is a *product* of the two branch rings, which
`Stacks.Curves.nodeAlg_eq_range_algebraMap_integralClosure` takes as an input, is a real
hypothesis rather than a consequence of nodality: `A'` is the semilocal ring
`(ν_* 𝒪_{X^ν})_x`, and it is the product of the local rings `𝒪_{X^ν, x'}` and `𝒪_{X^ν, x''}`
only when `A` has two minimal primes — on an irreducible nodal curve such as `y² = x²(x + 1)`
the local ring at the node is a domain and `A'` is a semilocal domain, not a product. The
equalizer form `Stacks.Curves.range_algebraMap_integralClosure_eq_equalizer` is the form of the
sequence that holds without that hypothesis.

## References

* [Stacks Project, Tag 0C1X](https://stacks.math.columbia.edu/tag/0C1X)
* [Stacks Project, Tag 0E68](https://stacks.math.columbia.edu/tag/0E68)
* [Stacks Project, Tag 0C4A](https://stacks.math.columbia.edu/tag/0C4A)
-/

@[expose] public noncomputable section

open IsLocalRing Stacks.Curves.NodalVectorFields

universe u v w w'

namespace Stacks.Curves

section Criterion

variable {k : Type u} {A : Type v} {S : Type w}
variable [Field k] [CommRing A] [Algebra k A] [CommRing S] [Algebra k S] [Algebra A S]

/-- The difference of two distinct `k`-algebra maps from a `k`-algebra to `k` is surjective:
rescaling an element on which they differ by a scalar hits every value. -/
theorem surjective_sub_of_ne {ε₁ ε₂ : S →ₐ[k] k} (hne : ε₁ ≠ ε₂) :
    Function.Surjective fun t : S => ε₁ t - ε₂ t := by
  obtain ⟨t₀, ht₀⟩ := DFunLike.ne_iff.mp hne
  have hd : ε₁ t₀ - ε₂ t₀ ≠ 0 := sub_ne_zero_of_ne ht₀
  intro c
  refine ⟨algebraMap k S (c / (ε₁ t₀ - ε₂ t₀)) * t₀, ?_⟩
  change ε₁ (algebraMap k S (c / (ε₁ t₀ - ε₂ t₀)) * t₀) -
    ε₂ (algebraMap k S (c / (ε₁ t₀ - ε₂ t₀)) * t₀) = c
  rw [map_mul, map_mul, AlgHom.commutes, AlgHom.commutes, ← mul_sub]
  simpa using div_mul_cancel₀ c hd

/-- The `A`-submodule of elements of an `A`-algebra on which two `k`-algebra maps to `k` agree.
It is a submodule precisely because the two maps agree on the image of `A`. -/
private def equalizerSubmodule (ε₁ ε₂ : S →ₐ[k] k)
    (hres : ∀ a : A, ε₁ (algebraMap A S a) = ε₂ (algebraMap A S a)) :
    Submodule A S where
  carrier := {t | ε₁ t = ε₂ t}
  add_mem' {s t} hs ht := by
    simp only [Set.mem_ofPred_eq, map_add] at hs ht ⊢
    rw [hs, ht]
  zero_mem' := by simp
  smul_mem' a t ht := by
    simp only [Set.mem_ofPred_eq] at ht ⊢
    rw [Algebra.smul_def, map_mul, map_mul, hres a, ht]

omit [Algebra k A] in
private theorem mem_equalizerSubmodule {ε₁ ε₂ : S →ₐ[k] k}
    {hres : ∀ a : A, ε₁ (algebraMap A S a) = ε₂ (algebraMap A S a)} {t : S} :
    t ∈ equalizerSubmodule (A := A) ε₁ ε₂ hres ↔ ε₁ t = ε₂ t := Iff.rfl

omit [Algebra k A] in
/-- **A coatomic image is cut out by the equality of two maps to the base field.** Let `S` be an
algebra over a local ring `A` whose own base is a field `k`, and suppose the image of `A` in `S`
is a coatom in the lattice of `A`-submodules of `S`. If `ε₁ ≠ ε₂` are `k`-algebra maps `S → k`
which agree on the image of `A`, then the image of `A` is exactly the set where they agree: the
equalizer is an `A`-submodule lying between the image and the top, and it is not the top. -/
theorem mem_range_iff_of_isCoatom (ε₁ ε₂ : S →ₐ[k] k)
    (hres : ∀ a : A, ε₁ (algebraMap A S a) = ε₂ (algebraMap A S a)) (hne : ε₁ ≠ ε₂)
    (hcoatom : IsCoatom (LinearMap.range (Algebra.linearMap A S))) (t : S) :
    ε₁ t = ε₂ t ↔ t ∈ Set.range (algebraMap A S) := by
  have hRE : LinearMap.range (Algebra.linearMap A S) ≤ equalizerSubmodule (A := A) ε₁ ε₂ hres := by
    rintro s ⟨a, rfl⟩
    exact hres a
  have hEne : equalizerSubmodule (A := A) ε₁ ε₂ hres ≠ ⊤ := by
    obtain ⟨s, hs⟩ := DFunLike.ne_iff.mp hne
    exact fun htop => hs (mem_equalizerSubmodule.mp (htop ▸ Submodule.mem_top))
  have heq : LinearMap.range (Algebra.linearMap A S) = equalizerSubmodule (A := A) ε₁ ε₂ hres :=
    hRE.eq_of_not_lt fun hlt => hEne (hcoatom.2 _ hlt)
  refine ⟨fun ht => ?_, fun ⟨a, ha⟩ => ha ▸ hres a⟩
  obtain ⟨a, ha⟩ := heq.ge (mem_equalizerSubmodule.mpr ht)
  exact ⟨a, ha⟩

omit [Algebra k A] in
/-- **A derivation fixing both points preserves a coatomic image.** With the hypotheses of
`Stacks.Curves.mem_range_iff_of_isCoatom`, a `k`-derivation of `S` preserving the two maximal
ideals `ker ε₁` and `ker ε₂` carries the image of `A` into itself: an element of the image
differs from a scalar by an element of both kernels, and the derivation kills the scalar. -/
theorem mem_range_of_fixes_of_isCoatom (ε₁ ε₂ : S →ₐ[k] k)
    (hres : ∀ a : A, ε₁ (algebraMap A S a) = ε₂ (algebraMap A S a)) (hne : ε₁ ≠ ε₂)
    (hcoatom : IsCoatom (LinearMap.range (Algebra.linearMap A S)))
    (D : Derivation k S S) (h₁ : Fixes ε₁ D) (h₂ : Fixes ε₂ D) {t : S}
    (ht : t ∈ Set.range (algebraMap A S)) : D t ∈ Set.range (algebraMap A S) := by
  have heq := mem_range_iff_of_isCoatom (A := A) ε₁ ε₂ hres hne hcoatom
  have hs₁ : ε₁ (t - algebraMap k S (ε₁ t)) = 0 := by simp
  have hs₂ : ε₂ (t - algebraMap k S (ε₁ t)) = 0 := by simp [(heq t).mpr ht]
  have hDs : D (t - algebraMap k S (ε₁ t)) = D t := by
    rw [map_sub, Derivation.map_algebraMap, sub_zero]
  exact (heq (D t)).mp (by rw [← hDs, h₁ _ hs₁, h₂ _ hs₂])

end Criterion

section Node

variable (k : Type u) (A : Type v) [Field k] [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable [Algebra k A]

/-- A reduced ring injects into its integral closure in its own total ring of fractions. -/
private theorem injective_algebraMap_integralClosure (A : Type v) [CommRing A] [IsReduced A] :
    Function.Injective (algebraMap A ↥(integralClosure A (FractionRing A))) :=
  fun _ _ hab => IsFractionRing.injective A (FractionRing A) (congrArg Subtype.val hab)

/-- **The image of a node in its normalization is cut out by the equality of the two branch
residues.** Let `A` be a nodal local algebra over `k` with normalization
`A' = integralClosure A (FractionRing A)`, and let `ε₁ ≠ ε₂` be two `k`-algebra maps `A' → k`
restricting to the same map on `A`. Then an element of `A'` comes from `A` exactly when its two
residues agree.

This is the identification of the image in the exact sequence
`0 → 𝒪_{X, x} → 𝒪_{X^ν, x'} × 𝒪_{X^ν, x''} → k → 0` of the proof of Tag 0E68, which that proof
takes from Tag 0C1X: the local ring at the node is "the set of elements having the same residue
classes in `k`". -/
theorem range_algebraMap_integralClosure_eq_equalizer (hA : IsNodalAlgebra k A)
    (ε₁ ε₂ : ↥(integralClosure A (FractionRing A)) →ₐ[k] k)
    (hres : ∀ a : A, ε₁ (algebraMap A ↥(integralClosure A (FractionRing A)) a) =
      ε₂ (algebraMap A ↥(integralClosure A (FractionRing A)) a))
    (hne : ε₁ ≠ ε₂) (t : ↥(integralClosure A (FractionRing A))) :
    ε₁ t = ε₂ t ↔ t ∈ Set.range (algebraMap A ↥(integralClosure A (FractionRing A))) :=
  mem_range_iff_of_isCoatom ε₁ ε₂ hres hne
    (isCoatom_range_algebraMap_integralClosure_of_isNodalAlgebra k A hA) t

/-- **The exact sequence of a node and its normalization.** For a nodal local algebra `A` over
`k` whose normalization `A'` carries two distinct `k`-algebra maps `ε₁, ε₂` to `k` agreeing on
`A`, the sequence `0 → A → A' → k → 0` with second map `t ↦ ε₁ t - ε₂ t` is exact: the first
map is injective, the second is surjective, and the kernel of the second is the image of the
first. -/
theorem exact_integralClosure_of_isNodalAlgebra (hA : IsNodalAlgebra k A)
    (ε₁ ε₂ : ↥(integralClosure A (FractionRing A)) →ₐ[k] k)
    (hres : ∀ a : A, ε₁ (algebraMap A ↥(integralClosure A (FractionRing A)) a) =
      ε₂ (algebraMap A ↥(integralClosure A (FractionRing A)) a))
    (hne : ε₁ ≠ ε₂) :
    Function.Injective (algebraMap A ↥(integralClosure A (FractionRing A))) ∧
      Function.Surjective
        (fun t : ↥(integralClosure A (FractionRing A)) => ε₁ t - ε₂ t) ∧
      ∀ t : ↥(integralClosure A (FractionRing A)),
        ε₁ t - ε₂ t = 0 ↔
          t ∈ Set.range (algebraMap A ↥(integralClosure A (FractionRing A))) := by
  have _ : IsReduced A := hA.2.1
  exact ⟨injective_algebraMap_integralClosure A, surjective_sub_of_ne hne, fun t =>
    sub_eq_zero.trans (range_algebraMap_integralClosure_eq_equalizer k A hA ε₁ ε₂ hres hne t)⟩

/-- **A derivation fixing the two branch points preserves the node.** Let `A` be a nodal local
algebra over `k` with normalization `A'`, and let `ε₁ ≠ ε₂` be two `k`-algebra maps `A' → k`
agreeing on `A`. A `k`-derivation of `A'` fixing both of the points they cut out carries the
image of `A` into itself.

This is the step "given a `D'` fixing `x'` and `x''` we find that `D'` preserves the subring
`𝒪_{X, x}`" of the proof of Tag 0E68, in local ring-theoretic form. -/
theorem mem_range_algebraMap_of_fixes (hA : IsNodalAlgebra k A)
    (ε₁ ε₂ : ↥(integralClosure A (FractionRing A)) →ₐ[k] k)
    (hres : ∀ a : A, ε₁ (algebraMap A ↥(integralClosure A (FractionRing A)) a) =
      ε₂ (algebraMap A ↥(integralClosure A (FractionRing A)) a))
    (hne : ε₁ ≠ ε₂)
    (D : Derivation k ↥(integralClosure A (FractionRing A))
      ↥(integralClosure A (FractionRing A)))
    (h₁ : Fixes ε₁ D) (h₂ : Fixes ε₂ D)
    {t : ↥(integralClosure A (FractionRing A))}
    (ht : t ∈ Set.range (algebraMap A ↥(integralClosure A (FractionRing A)))) :
    D t ∈ Set.range (algebraMap A ↥(integralClosure A (FractionRing A))) :=
  mem_range_of_fixes_of_isCoatom ε₁ ε₂ hres hne
    (isCoatom_range_algebraMap_integralClosure_of_isNodalAlgebra k A hA) D h₁ h₂ ht

/-- **A derivation fixing the two branch points restricts to the node.** With the hypotheses of
`Stacks.Curves.mem_range_algebraMap_of_fixes`, the value of `D` on the image of `a` is the image
of a unique element of `A`; that element is the value at `a` of the restricted derivation.

This is the local form of `Stacks.Curves.existsUnique_descend_iff_preserves`: the image of `A`
is preserved and `A → A'` is injective, so the restriction exists and is unique. -/
theorem existsUnique_restrict_of_fixes (hA : IsNodalAlgebra k A)
    (ε₁ ε₂ : ↥(integralClosure A (FractionRing A)) →ₐ[k] k)
    (hres : ∀ a : A, ε₁ (algebraMap A ↥(integralClosure A (FractionRing A)) a) =
      ε₂ (algebraMap A ↥(integralClosure A (FractionRing A)) a))
    (hne : ε₁ ≠ ε₂)
    (D : Derivation k ↥(integralClosure A (FractionRing A))
      ↥(integralClosure A (FractionRing A)))
    (h₁ : Fixes ε₁ D) (h₂ : Fixes ε₂ D) (a : A) :
    ∃! b : A, algebraMap A ↥(integralClosure A (FractionRing A)) b =
      D (algebraMap A ↥(integralClosure A (FractionRing A)) a) := by
  have _ : IsReduced A := hA.2.1
  obtain ⟨b, hb⟩ := mem_range_algebraMap_of_fixes k A hA ε₁ ε₂ hres hne D h₁ h₂ ⟨a, rfl⟩
  exact ⟨b, hb, fun b' hb' =>
    injective_algebraMap_integralClosure A (hb'.trans hb.symm)⟩

end Node

section NodeAlgebra

variable (k : Type u) (A : Type v) [Field k] [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable [Algebra k A]

/-- **The node algebra of the two branches is the image of the node.** If the normalization `A'`
of a nodal local algebra `A` over `k` is, as a `k`-algebra, the product `B₁ × B₂` of the two
branch rings, each carrying an augmentation `εᵢ : Bᵢ → k`, and the two augmentations agree on
the image of `A`, then the image of `A` in `B₁ × B₂` is exactly the node algebra
`B₁ ×_k B₂` of `Stacks.Curves.NodalVectorFields.nodeAlg`.

This instantiates the node algebra at the normalization of an actual node: the ambient algebra
of `Stacks.Curves.NodalVectorFields.range_branchPair_eq_setOf_fixes` is this one, and that
lemma's remaining assumptions are the uniformizer conditions on the two augmentation ideals. -/
theorem nodeAlg_eq_range_algebraMap_integralClosure (hA : IsNodalAlgebra k A)
    {B₁ : Type w} {B₂ : Type w'} [CommRing B₁] [CommRing B₂] [Algebra k B₁] [Algebra k B₂]
    (ε₁ : B₁ →ₐ[k] k) (ε₂ : B₂ →ₐ[k] k)
    (e : ↥(integralClosure A (FractionRing A)) ≃ₐ[k] B₁ × B₂)
    (hres : ∀ a : A,
      ε₁ (e (algebraMap A ↥(integralClosure A (FractionRing A)) a)).1 =
        ε₂ (e (algebraMap A ↥(integralClosure A (FractionRing A)) a)).2)
    (b : B₁ × B₂) :
    b ∈ nodeAlg ε₁ ε₂ ↔
      b ∈ Set.range fun a : A => e (algebraMap A ↥(integralClosure A (FractionRing A)) a) := by
  have hne : ε₁.comp ((AlgHom.fst k B₁ B₂).comp e.toAlgHom) ≠
      ε₂.comp ((AlgHom.snd k B₁ B₂).comp e.toAlgHom) := by
    intro hcon
    have h1 : ε₁.comp ((AlgHom.fst k B₁ B₂).comp e.toAlgHom) (e.symm (1, 0)) = 1 := by
      simp
    rw [hcon] at h1
    simp at h1
  have hkey := range_algebraMap_integralClosure_eq_equalizer k A hA
    (ε₁.comp ((AlgHom.fst k B₁ B₂).comp e.toAlgHom))
    (ε₂.comp ((AlgHom.snd k B₁ B₂).comp e.toAlgHom)) hres hne (e.symm b)
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply] at hkey
  rw [mem_nodeAlg]
  refine hkey.trans ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨a, ha⟩ := h
    refine ⟨a, ?_⟩
    change e (algebraMap A ↥(integralClosure A (FractionRing A)) a) = b
    rw [ha, e.apply_symm_apply]
  · obtain ⟨a, ha⟩ := h
    have ha' : e (algebraMap A ↥(integralClosure A (FractionRing A)) a) = b := ha
    exact ⟨a, e.injective (by rw [e.apply_symm_apply]; exact ha')⟩

end NodeAlgebra

end Stacks.Curves

end
