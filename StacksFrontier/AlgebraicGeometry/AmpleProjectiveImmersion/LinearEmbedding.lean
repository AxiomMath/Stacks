module

public import StacksFrontier.AlgebraicGeometry.Limits.ProjGradedSurjection01N0
public import StacksFrontier.AlgebraicGeometry.SegreEmbedding.ProjPoly
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.ChartTwistOne

/-!
# The linear embedding `ℙⁿ_S ↪ ℙᴺ_S`, with its hyperplane sheaf

`Stacks.AmpleProjectiveImmersion.HasImmersionTwistOver f M` says that `M` is `𝒪(1)` pulled back
along an immersion `X ⟶ ℙⁿ_S` over `S` **for some `n : ℕ`**, where [Stacks, Tag 01VS] and the
immersion clauses (5) and (6) of [Stacks, Tag 01VT] write `∃ n ≥ 1`. This file shows the
lower bound is no restriction: an immersion into `ℙⁿ_S` composed with the linear embedding
`ℙⁿ_S ↪ ℙᴺ_S` is an immersion into `ℙᴺ_S` carrying the same hyperplane sheaf, so a witness at
`n` gives one at `max n 1`.

The embedding is [Stacks, Tag 01N0] at a polynomial ring, in all three of its parts:

* the graded homomorphism is `MvPolynomial.rename` along the surjection
  `Fin (N + 1) → Fin (n + 1)`, `k ↦ min k n`, which collapses the last `N - n` coordinates onto
  the `n`-th. It is surjective, so part (1) — the domain of definition is everything — is
  `AlgebraicGeometry.Proj.irrelevant_le_map_of_surjective` and part (2) — a closed immersion —
  is `AlgebraicGeometry.Proj.isClosedImmersion_map_of_surjective'`;
* part (3), that the comparison `θ : r^* 𝒪(1) ⟶ 𝒪(1)` is an isomorphism, is
  `Stacks.AlgebraicGeometry.TwistChartLocality.isIso_projTwistComparison`: the images of the
  degree-one part contain every variable of `ℤ[T₀, …, Tₙ]`, which generates its irrelevant ideal.

The embedding over `S` is the base change of the integral one along `S ⟶ Spec ℤ`, a closed
immersion by [Stacks, Tag 01JY]; its hyperplane sheaf follows because `𝒪(1)` on `ℙᵏ_S` is by
definition the inverse image of the integral `𝒪(1)` and the base-change square commutes.

## Main definitions

* `Stacks.AmpleProjectiveImmersion.linearEmbeddingAtUniverse`: the linear embedding of the
  integral models `ℙⁿ ↪ ℙᴺ`, for `n ≤ N`.
* `Stacks.AmpleProjectiveImmersion.linearEmbeddingOver`: its base change `ℙⁿ_S ↪ ℙᴺ_S`.
* `Stacks.AmpleProjectiveImmersion.HasImmersionTwistOverPos`: the source's own clause, with the
  lower bound `n ≥ 1` on the dimension of the projective space.

## Main results

* `Stacks.AmpleProjectiveImmersion.nonempty_pullback_linearEmbeddingAtUniverse_twistingSheaf`
  and `nonempty_pullback_linearEmbeddingOver_projectiveSpaceTwistingSheaf`: **the hyperplane
  sheaf pulls back to the hyperplane sheaf**, over `Spec ℤ` and over `S`.
* `Stacks.AmpleProjectiveImmersion.hasImmersionTwistOver_exists_of_le`: an immersion witness at
  `n` gives one at every `N ≥ n`.
* `Stacks.AmpleProjectiveImmersion.hasImmersionTwistOverPos_iff`: **the lower bound `n ≥ 1` of
  the source costs nothing** — `HasImmersionTwistOver` and `HasImmersionTwistOverPos` are
  equivalent.

## Implementation notes

**The collapsing map, not an inclusion.** A section `Fin (N + 1) → Fin (n + 1)` is needed, not
an injection the other way: `AlgebraicGeometry.Proj.map` is contravariant, so the embedding
`Proj ℤ[T₀, …, Tₙ] ⟶ Proj ℤ[T₀, …, T_N]` comes from a graded map
`ℤ[T₀, …, T_N] → ℤ[T₀, …, Tₙ]`, and that map must be **surjective** for the morphism to be a
closed immersion. `k ↦ min k n` is the cheapest surjection; it sends `T_k ↦ T_n` for `k ≥ n`
rather than `T_k ↦ 0`, which makes the image of `ℙⁿ` a linear subspace of `ℙᴺ` in different
coordinates but is equally good for every purpose here, and keeps the map a `rename` so that
`Stacks.AlgebraicGeometry.ProjPoly.renameGradedHom` supplies the graded structure.

**No `stacks` attribute is attached.** Tag 01N0 is carried in the generality it states where it
is proved: parts (1) and (2) in
`StacksFrontier/AlgebraicGeometry/RelativeProjChain/EventualSurjective.lean`, part (3) in
`StacksFrontier/AlgebraicGeometry/ProjTwistEpi/Basic.lean` and
`StacksFrontier/AlgebraicGeometry/ProjTwistCompare/NotIsoExample.lean`; this file applies it at one
homomorphism. The consumer of this file is [Stacks, Tag 01VT], whose attributes are in
`StacksFrontier/AlgebraicGeometry/AmpleRelativeFiniteType/`.

## References

* [Stacks Project, Tag 01N0](https://stacks.math.columbia.edu/tag/01N0)
* [Stacks Project, Tag 01JY](https://stacks.math.columbia.edu/tag/01JY)
* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
* [Stacks Project, Tag 01VT](https://stacks.math.columbia.edu/tag/01VT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjPoly (renameGradedHom)

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace Stacks.AmpleProjectiveImmersion

/-! ### The graded surjection collapsing the last coordinates -/

/-- **The surjection of coordinate indices** `Fin (N + 1) → Fin (n + 1)`, `k ↦ min k n`, for
`n ≤ N`. Renaming along it is the graded surjection whose `Proj` is the linear embedding
`ℙⁿ ↪ ℙᴺ`. -/
def coordCollapse {n N : ℕ} : Fin (N + 1) → Fin (n + 1) :=
  fun k => ⟨min (k : ℕ) n, by omega⟩

/-- The collapse `k ↦ min k n` of coordinate indices is surjective. -/
theorem surjective_coordCollapse {n N : ℕ} (hnN : n ≤ N) :
    Function.Surjective (coordCollapse (n := n) (N := N)) := by
  intro j
  refine ⟨Fin.castLE (by omega) j, Fin.ext ?_⟩
  have hj := j.isLt
  simp only [coordCollapse, Fin.val_castLE]
  omega

/-- **The graded surjection `ℤ[T₀, …, T_N] → ℤ[T₀, …, Tₙ]`** of the linear embedding: renaming
along `Stacks.AmpleProjectiveImmersion.coordCollapse`. -/
abbrev linearGradedHom {n N : ℕ} :
    MvPolynomial.homogeneousSubmodule (Fin (N + 1)) (ULift.{u} ℤ) →+*ᵍ
      MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ) :=
  renameGradedHom (ULift.{u} ℤ) (coordCollapse (n := n) (N := N))

/-- The graded homomorphism `ℤ[T₀, …, T_N] → ℤ[T₀, …, Tₙ]` of the linear embedding is
surjective. -/
theorem surjective_linearGradedHom {n N : ℕ} (hnN : n ≤ N) :
    Function.Surjective (linearGradedHom.{u} (n := n) (N := N)) := fun p =>
  MvPolynomial.rename_surjective _ (surjective_coordCollapse hnN) p

/-- **Part (1) of [Stacks, Tag 01N0] at the linear embedding**: the irrelevant ideal of
`ℤ[T₀, …, Tₙ]` lies in the ideal generated by the image of the irrelevant ideal of
`ℤ[T₀, …, T_N]`, so the induced morphism of `Proj`s is defined everywhere. -/
theorem irrelevant_le_map_linearGradedHom {n N : ℕ} (hnN : n ≤ N) :
    HomogeneousIdeal.irrelevant
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) ≤
      (HomogeneousIdeal.irrelevant
        (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) (ULift.{u} ℤ))).map
        (linearGradedHom.{u} (n := n) (N := N)) :=
  AlgebraicGeometry.Proj.irrelevant_le_map_of_surjective _ (surjective_linearGradedHom hnN)

/-- **The irrelevant ideal of `ℤ[T₀, …, Tₙ]` is generated by the images of the degree-one part of
`ℤ[T₀, …, T_N]`**, which is what inverts [Stacks, Tag 01MY]'s comparison on the twists. Every
variable of the target is the image of a variable of the source, because
`Stacks.AmpleProjectiveImmersion.coordCollapse` is surjective. -/
theorem irrelevant_le_span_image_linearGradedHom {n N : ℕ} (hnN : n ≤ N) :
    (HomogeneousIdeal.irrelevant
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))).toIdeal ≤
      Ideal.span (linearGradedHom.{u} (n := n) (N := N) ''
        ((MvPolynomial.homogeneousSubmodule (Fin (N + 1)) (ULift.{u} ℤ) 1 : Set _))) := by
  refine Stacks.SymGraded.irrelevant_le_span_X_of_index.trans (Ideal.span_mono ?_)
  rintro _ ⟨j, rfl⟩
  obtain ⟨k, hk⟩ := surjective_coordCollapse hnN j
  refine ⟨MvPolynomial.X k,
    (MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_X _ _), ?_⟩
  rw [show (linearGradedHom.{u} (n := n) (N := N)) (MvPolynomial.X k) =
    MvPolynomial.X (coordCollapse (n := n) (N := N) k) from MvPolynomial.rename_X _ _, hk]

/-! ### The linear embedding of the integral models -/

/-- **The linear embedding `ℙⁿ ↪ ℙᴺ` of the integral models**, for `n ≤ N`: `Proj` of the graded
surjection `ℤ[T₀, …, T_N] → ℤ[T₀, …, Tₙ]`. -/
def linearEmbeddingAtUniverse {n N : ℕ} (hnN : n ≤ N) :
    projectiveSpaceAtUniverse.{u} n ⟶ projectiveSpaceAtUniverse.{u} N :=
  AlgebraicGeometry.Proj.map (linearGradedHom.{u} (n := n) (N := N))
    (irrelevant_le_map_linearGradedHom hnN)

/-- The linear embedding `ℙⁿ ↪ ℙᴺ` of the integral models is a closed immersion. -/
theorem isClosedImmersion_linearEmbeddingAtUniverse {n N : ℕ} (hnN : n ≤ N) :
    IsClosedImmersion (linearEmbeddingAtUniverse.{u} hnN) :=
  AlgebraicGeometry.Proj.isClosedImmersion_map_of_surjective' _
    (surjective_linearGradedHom hnN)

/-- **The hyperplane sheaf of `ℙᴺ` pulls back to the hyperplane sheaf of `ℙⁿ`** along the linear
embedding of the integral models. This is part (3) of [Stacks, Tag 01N0] at this homomorphism,
supplied by the degree-one chart argument of
`Stacks.AlgebraicGeometry.TwistChartLocality.isIso_projTwistComparison`. -/
theorem nonempty_pullback_linearEmbeddingAtUniverse_twistingSheaf {n N : ℕ} (hnN : n ≤ N) :
    Nonempty ((Scheme.Modules.pullback (linearEmbeddingAtUniverse.{u} hnN)).obj
        (twistingSheafAtUniverse.{u} N) ≅ twistingSheafAtUniverse.{u} n) := by
  have h : IsIso (Stacks.ProjTwistComparison.twistMap (linearGradedHom.{u} (n := n) (N := N))
      (irrelevant_le_map_linearGradedHom hnN) 1) :=
    Stacks.AlgebraicGeometry.TwistChartLocality.isIso_projTwistComparison _ _ _
      (irrelevant_le_map_linearGradedHom hnN) 1 (irrelevant_le_span_image_linearGradedHom hnN)
  exact ⟨@asIso _ _ _ _ _ h⟩

/-! ### The linear embedding over a base -/

/-- **The linear embedding `ℙⁿ_S ↪ ℙᴺ_S`**, the base change along `S ⟶ Spec ℤ` of the linear
embedding of the integral models. -/
def linearEmbeddingOver (S : Scheme.{u}) {n N : ℕ} (hnN : n ≤ N) :
    projectiveSpaceOver n S ⟶ projectiveSpaceOver N S :=
  pullback.map (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} n))
    (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} N)) (𝟙 S)
    (linearEmbeddingAtUniverse.{u} hnN) (𝟙 _) (by simp) (by simp)

/-- The linear embedding `ℙⁿ_S ↪ ℙᴺ_S` is an immersion. -/
theorem isImmersion_linearEmbeddingOver (S : Scheme.{u}) {n N : ℕ} (hnN : n ≤ N) :
    IsImmersion (linearEmbeddingOver S hnN) := by
  have : MorphismProperty.IsStableUnderComposition @IsClosedImmersion :=
    ⟨fun a c ha hc => @IsClosedImmersion.comp _ _ _ a c ha hc⟩
  have : IsClosedImmersion (linearEmbeddingOver S hnN) :=
    MorphismProperty.pullbackMap (P := @IsClosedImmersion) inferInstance
      (isClosedImmersion_linearEmbeddingAtUniverse hnN) (Category.id_comp _).symm (by simp)
  infer_instance

/-- The linear embedding is a morphism over `S`. -/
theorem linearEmbeddingOver_comp_fst (S : Scheme.{u}) {n N : ℕ} (hnN : n ≤ N) :
    linearEmbeddingOver S hnN ≫
        pullback.fst (terminal.from S)
          (terminal.from (projectiveSpaceAtUniverse.{u} N)) =
      pullback.fst (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} n)) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- The linear embedding is compatible with the projections to the integral models. -/
theorem linearEmbeddingOver_comp_snd (S : Scheme.{u}) {n N : ℕ} (hnN : n ≤ N) :
    linearEmbeddingOver S hnN ≫ projectiveSpaceOver.toIntegralAtUniverse N S =
      projectiveSpaceOver.toIntegralAtUniverse n S ≫ linearEmbeddingAtUniverse.{u} hnN :=
  pullback.lift_snd _ _ _

/-- **The hyperplane sheaf of `ℙᴺ_S` pulls back to the hyperplane sheaf of `ℙⁿ_S`** along the
linear embedding over `S`. Both are inverse images of the integral `𝒪(1)` along the projection to
the integral model, and the base-change square commutes, so this is the integral comparison
transported. -/
theorem nonempty_pullback_linearEmbeddingOver_projectiveSpaceTwistingSheaf (S : Scheme.{u})
    {n N : ℕ} (hnN : n ≤ N) :
    Nonempty ((Scheme.Modules.pullback (linearEmbeddingOver S hnN)).obj
        (projectiveSpaceTwistingSheaf N S) ≅ projectiveSpaceTwistingSheaf n S) := by
  obtain ⟨t⟩ := nonempty_pullback_linearEmbeddingAtUniverse_twistingSheaf.{u} hnN
  exact ⟨(Scheme.Modules.pullbackComp (linearEmbeddingOver S hnN)
      (projectiveSpaceOver.toIntegralAtUniverse N S)).app _ ≪≫
    (Scheme.Modules.pullbackCongr (linearEmbeddingOver_comp_snd S hnN)).app _ ≪≫
    ((Scheme.Modules.pullbackComp (projectiveSpaceOver.toIntegralAtUniverse n S)
      (linearEmbeddingAtUniverse.{u} hnN)).app _).symm ≪≫
    (Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse n S)).mapIso t⟩

/-! ### The lower bound on the dimension costs nothing -/

variable {X S : Scheme.{u}}

/-- **An immersion witness at `n` gives one at every `N ≥ n`**: compose with the linear
embedding. -/
theorem hasImmersionTwistOver_exists_of_le (f : X ⟶ S) (M : X.Modules) {n N : ℕ} (hnN : n ≤ N)
    (i : X ⟶ projectiveSpaceOver n S) (hi : IsImmersion i)
    (hif : i ≫ pullback.fst (terminal.from S)
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) = f)
    (e : M ≅ (Scheme.Modules.pullback i).obj (projectiveSpaceTwistingSheaf n S)) :
    ∃ j : X ⟶ projectiveSpaceOver N S, IsImmersion j ∧
      j ≫ pullback.fst (terminal.from S)
        (terminal.from (projectiveSpaceAtUniverse.{u} N)) = f ∧
      Nonempty (M ≅ (Scheme.Modules.pullback j).obj (projectiveSpaceTwistingSheaf N S)) := by
  obtain ⟨t⟩ := nonempty_pullback_linearEmbeddingOver_projectiveSpaceTwistingSheaf S hnN
  have := hi
  have := isImmersion_linearEmbeddingOver S hnN
  refine ⟨i ≫ linearEmbeddingOver S hnN, inferInstance, ?_, ⟨?_⟩⟩
  · rw [Category.assoc, linearEmbeddingOver_comp_fst, hif]
  · exact e ≪≫ (Scheme.Modules.pullback i).mapIso t.symm ≪≫
      (Scheme.Modules.pullbackComp i (linearEmbeddingOver S hnN)).app _

/-- **The immersion clause of [Stacks, Tag 01VS] with the source's lower bound**: `M` is `𝒪(1)`
pulled back along an immersion `X ⟶ ℙⁿ_S` over `S`, for some `n ≥ 1`. This is
`Stacks.AmpleProjectiveImmersion.HasImmersionTwistOver` with the source's `∃ n ≥ 1` in place of
`∃ n : ℕ`. -/
def HasImmersionTwistOverPos (f : X ⟶ S) (M : X.Modules) : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧ ∃ i : X ⟶ projectiveSpaceOver n S, IsImmersion i ∧
    i ≫ pullback.fst (terminal.from S)
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) = f ∧
    Nonempty (M ≅ (Scheme.Modules.pullback i).obj (projectiveSpaceTwistingSheaf n S))

/-- **The source's lower bound on the dimension of the projective space costs nothing.** A
witness at `n` is pushed to `max n 1` by the linear embedding, and a witness with the bound is
one without it. -/
theorem hasImmersionTwistOverPos_iff (f : X ⟶ S) (M : X.Modules) :
    HasImmersionTwistOver f M ↔ HasImmersionTwistOverPos f M := by
  constructor
  · rintro ⟨n, i, hi, hif, ⟨e⟩⟩
    exact ⟨max n 1, le_max_right n 1,
      hasImmersionTwistOver_exists_of_le f M (le_max_left n 1) i hi hif e⟩
  · rintro ⟨n, -, h⟩
    exact ⟨n, h⟩

end Stacks.AmpleProjectiveImmersion

end
