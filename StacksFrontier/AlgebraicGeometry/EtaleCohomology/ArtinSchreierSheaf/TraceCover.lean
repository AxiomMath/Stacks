module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSheaf.Cover
public import Mathlib.FieldTheory.Finite.Trace

/-!
# The Artin–Schreier covers of a finite extension and the trace

Let `k ⊆ κ` be finite fields, `q = #k`, `#κ = q ^ r`, and `g` an element of a `κ`-algebra `A`. The
Artin–Schreier cover `S^{q^r} - S = g` of `Spec A` (for the field `κ`) maps to the cover
`T^q - T = g` (for the field `k`) by `T ↦ S + S^q + ⋯ + S^{q^{r-1}}`
(`Stacks.ArtinSchreier.traceRingMap`): indeed `(∑ S^{q^i})^q - ∑ S^{q^i} = S^{q^r} - S = g`. The
translation `S ↦ S + a` by `a ∈ κ` becomes the translation `T ↦ T + Tr_{κ/k}(a)`, since
`Tr_{κ/k}(a) = ∑_{i < r} a^{q^i}` (`FiniteField.algebraMap_trace_eq_sum_pow`). Hence the character
of the `k`-cover is the trace of the character of the `κ`-cover
(`Stacks.ArtinSchreier.torsorCover_character_coverTraceHom`), so that
`L_{ψ ∘ Tr_{κ/k}}(g) = L_ψ(g)` for an additive character `ψ` of `k`. This identifies the restriction
of the Artin–Schreier factor of Laumon's family to a fibre with residue field `κ(v)` in
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main definitions

* `Stacks.ArtinSchreier.traceRingMap`, `Stacks.ArtinSchreier.coverTraceHom`.

## Main results

* `AlgebraicGeometry.TorsorCover.character_eq_of_hom_addMonoidHom`: an equivariant morphism of
  torsor covers along a homomorphism `K₁ → K₂` maps the character to its image.
* `Stacks.ArtinSchreier.torsorCover_character_coverTraceHom`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial

universe u

namespace AlgebraicGeometry.TorsorCover

variable {X : Scheme.{u}} [ConnectedSpace X] {K₁ K₂ : Type*} [AddCommGroup K₁] [AddCommGroup K₂]

/-- **An equivariant morphism of torsor covers along `τ : K₁ →+ K₂` maps the character to its
image under `τ`.** -/
public theorem character_eq_of_hom_addMonoidHom {T₁ : TorsorCover X K₁} {T₂ : TorsorCover X K₂}
    (τ : K₁ →+ K₂) (h : T₁.cover ⟶ T₂.cover) (hh : ∀ a, T₁.τ a ≫ h = h ≫ T₂.τ (τ a))
    (x : GeometricPoint X) (p₀ : (finiteEtaleFiberFunctor x).obj T₁.cover)
    (σ : EtaleFundamentalGroup X x) :
    T₂.character x ((finiteEtaleFiberFunctor x).map h p₀) σ =
      Multiplicative.ofAdd (τ (Multiplicative.toAdd (T₁.character x p₀ σ))) := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_ofAdd]
  refine T₂.character_eq_of_smul x _ σ ((finiteEtaleFiberFunctor x).map h p₀) ?_
  have hσ : σ • (finiteEtaleFiberFunctor x).map h p₀ = (finiteEtaleFiberFunctor x).map h (σ • p₀) :=
    (ConcreteCategory.congr_hom (σ.hom.naturality h) p₀)
  rw [hσ, T₁.smul_eq_character x p₀ σ p₀, ← Functor.map_comp_apply, hh, Functor.map_comp_apply]

end AlgebraicGeometry.TorsorCover

namespace Stacks.ArtinSchreier

section Powers

variable (k : Type u) [Field k] [Fintype k] {S : Type*} [CommRing S] [Algebra k S]

/-- `x ↦ x ^ (q ^ i)` is additive on an `𝔽_q`-algebra. -/
public theorem add_pow_card_pow (x y : S) (i : ℕ) :
    (x + y) ^ (Fintype.card k ^ i) = x ^ (Fintype.card k ^ i) + y ^ (Fintype.card k ^ i) := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ, pow_mul, pow_mul, pow_mul, ih, add_pow_card]

/-- `x ↦ x ^ q` commutes with finite sums on an `𝔽_q`-algebra. -/
public theorem sum_pow_card {ι : Type*} (s : Finset ι) (f : ι → S) :
    (∑ i ∈ s, f i) ^ Fintype.card k = ∑ i ∈ s, f i ^ Fintype.card k := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [zero_pow (Fintype.card_ne_zero (α := k))]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, add_pow_card, ih]

end Powers

variable (k : Type u) [Field k] [Fintype k] (κ : Type u) [Field κ] [Fintype κ] [Algebra k κ]
  {A : Type u} [CommRing A] [Algebra k A] [Algebra κ A] [IsScalarTower k κ A] (g : A)

/-- **The trace of the root**: `S + S^q + ⋯ + S^{q^{r-1}}` in the `κ`-Artin–Schreier algebra,
`r = [κ : k]`. -/
public def traceRoot : Ring κ g :=
  ∑ i ∈ Finset.range (Module.finrank k κ), AdjoinRoot.root (poly κ g) ^ (Fintype.card k ^ i)

/-- **The trace of the root is a root of `T^q - T - g`**: with `q = #k`,
`(S + S^q + ⋯ + S^{q^{r-1}})^q = S + S^q + ⋯ + S^{q^{r-1}} + g`, since `S^{q^r} = S + g`. -/
public theorem traceRoot_pow_card :
    traceRoot k κ g ^ Fintype.card k = traceRoot k κ g + algebraMap A (Ring κ g) g := by
  set S := AdjoinRoot.root (poly κ g)
  set r := Module.finrank k κ
  have h1 : traceRoot k κ g ^ Fintype.card k =
      ∑ i ∈ Finset.range r, S ^ (Fintype.card k ^ (i + 1)) := by
    rw [traceRoot, sum_pow_card]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← pow_mul, pow_succ]
  have h2 := Finset.sum_range_succ' (fun i => S ^ (Fintype.card k ^ i)) r
  have h3 := Finset.sum_range_succ (fun i => S ^ (Fintype.card k ^ i)) r
  have hr : S ^ (Fintype.card k ^ r) = S + algebraMap A (Ring κ g) g := by
    rw [← Module.card_eq_pow_finrank (K := k) (V := κ)]
    exact root_pow_card κ g
  have h0 : S ^ (Fintype.card k ^ 0) = S := by rw [pow_zero, pow_one]
  rw [h1]
  show _ = ∑ i ∈ Finset.range r, S ^ (Fintype.card k ^ i) + _
  linear_combination h3 - h2 + hr - h0

/-- **`T ↦ S + S^q + ⋯ + S^{q^{r-1}}`, from the `k`-Artin–Schreier algebra of `g` to the
`κ`-Artin–Schreier algebra of `g`.** -/
public def traceRingMap : Ring k g →ₐ[A] Ring κ g :=
  AdjoinRoot.liftAlgHom (poly k g) (Algebra.ofId A (Ring κ g)) (traceRoot k κ g) (by
    change eval₂ _ _ (X ^ Fintype.card k - (X + C g)) = 0
    rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_add, eval₂_X, eval₂_C, traceRoot_pow_card]
    change _ - (_ + algebraMap A (Ring κ g) g) = 0
    ring)

/-- `Stacks.ArtinSchreier.traceRingMap` sends the root `T` of the `k`-Artin–Schreier algebra to
`Stacks.ArtinSchreier.traceRoot`. -/
@[simp]
public theorem traceRingMap_root :
    traceRingMap k κ g (AdjoinRoot.root (poly k g)) = traceRoot k κ g :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- **The translation by `a ∈ κ` corresponds to the translation by `Tr_{κ/k}(a)`.** -/
public theorem translate_comp_traceRingMap (a : κ) :
    (translate κ g a).comp (traceRingMap k κ g) =
      (traceRingMap k κ g).comp (translate k g (Algebra.trace k κ a)) := by
  apply AdjoinRoot.algHom_ext
  rw [AlgHom.comp_apply, AlgHom.comp_apply, traceRingMap_root, translate_root, map_add,
    traceRingMap_root, traceRoot, map_sum]
  simp only [map_pow, translate_root, add_pow_card_pow, Finset.sum_add_distrib]
  congr 1
  rw [IsScalarTower.algebraMap_apply k A (Ring k g), (traceRingMap k κ g).commutes,
    ← IsScalarTower.algebraMap_apply k A (Ring κ g), IsScalarTower.algebraMap_apply k κ (Ring κ g),
    FiniteField.algebraMap_trace_eq_sum_pow, map_sum, Nat.card_eq_fintype_card]
  simp only [map_pow]

/-- **The morphism from the `κ`-Artin–Schreier cover of `g` to the `k`-Artin–Schreier cover of
`g`**, over `Spec A`. -/
public def coverTraceHom : cover κ A g ⟶ cover k A g :=
  MorphismProperty.Over.homMk (Spec.map (CommRingCat.ofHom (traceRingMap k κ g).toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext a
    exact (traceRingMap k κ g).commutes a)

/-- **The translation by `a ∈ κ` of the `κ`-Artin–Schreier cover corresponds to the translation
by `Tr_{κ/k}(a)` of the `k`-Artin–Schreier cover** along `Stacks.ArtinSchreier.coverTraceHom`. -/
public theorem coverTranslate_comp_coverTraceHom (a : κ) :
    coverTranslate κ A g a ≫ coverTraceHom k κ g =
      coverTraceHom k κ g ≫ coverTranslate k A g (Algebra.trace k κ a) := by
  ext : 1
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun b => ?_)
  exact congrArg (fun φ : Ring k g →ₐ[A] Ring κ g => φ b) (translate_comp_traceRingMap k κ g a)

/-- **The character of the `k`-Artin–Schreier cover is the trace of the character of the
`κ`-Artin–Schreier cover.** -/
public theorem torsorCover_character_coverTraceHom [ConnectedSpace (Spec (.of A))]
    (x : GeometricPoint (Spec (.of A))) (p₀ : (finiteEtaleFiberFunctor x).obj (cover κ A g))
    (σ : EtaleFundamentalGroup (Spec (.of A)) x) :
    (torsorCover k A g).character x ((finiteEtaleFiberFunctor x).map (coverTraceHom k κ g) p₀) σ =
      Multiplicative.ofAdd (Algebra.trace k κ
        (Multiplicative.toAdd ((torsorCover κ A g).character x p₀ σ))) :=
  TorsorCover.character_eq_of_hom_addMonoidHom (T₁ := torsorCover κ A g) (T₂ := torsorCover k A g)
    (Algebra.trace k κ).toAddMonoidHom (coverTraceHom k κ g)
    (coverTranslate_comp_coverTraceHom k κ g) x p₀ σ

end Stacks.ArtinSchreier

end
