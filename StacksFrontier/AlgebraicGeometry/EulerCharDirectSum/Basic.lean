module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Pi
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.KernelCokernel
public import StacksCore.Tactic.StacksAttribute

/-!
# The Euler characteristic of a finite direct sum, with no finiteness hypothesis

For a scheme proper over a field and a coherent module `𝒢`, the Euler characteristic of the
`n`-fold direct sum of `𝒢` with itself is `n · χ(X, 𝒢)`. **This is unconditional**: it needs
neither [Stacks, Tag 02O6] (finite dimensionality of the cohomology over `k`) nor any vanishing
statement.

That is worth stating, because the Euler characteristic is *not* additive along an arbitrary
short exact sequence without Tag 02O6 — `AlgebraicGeometry.eulerCharacteristic` is an
alternating sum of `Module.finrank`s, and `Module.finrank` is not additive on a product of
infinite-dimensional spaces. The equal-summand case escapes that: `Module.finrank k (Fin n → V)`
is `n * Module.finrank k V` for *every* `k`-vector space `V`, both sides being zero when `V` is
infinite-dimensional and `n` is positive. So the direct-sum formula needs no finiteness input,
whereas the two-out-of-three formula of [Stacks, Tag 08AA] does.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.biprodPow`: the `n`-fold biproduct `𝒢^{⊞ n}` of a module
  with itself, by recursion on `n`, with the zero object at `n = 0`.

## Main results

* `Module.finrank_fun_fin`: `Module.finrank k (Fin n → V) = n * Module.finrank k V`, with no
  finiteness hypothesis on `V`.
* `AlgebraicGeometry.nonempty_cohomologyOverField_biprod_linearEquiv`:
  `Hᵐ(X, 𝒜 ⊞ ℬ) ≅ Hᵐ(X, 𝒜) × Hᵐ(X, ℬ)` as `k`-vector spaces, for any morphism to `Spec k`.
* `AlgebraicGeometry.nonempty_cohomologyOverField_biprodPow_linearEquiv`:
  `Hᵐ(X, 𝒢^{⊞ n}) ≅ (Fin n → Hᵐ(X, 𝒢))`.
* `AlgebraicGeometry.eulerCharacteristic_biprodPow`: **`χ(X, 𝒢^{⊞ n}) = n · χ(X, 𝒢)`**,
  unconditional.
* `AlgebraicGeometry.exists_eulerCharacteristic_eq_mul_of_iso_biprodPow`: a coherent module
  isomorphic to `𝒢^{⊞ n}` has Euler characteristic `n · χ(X, 𝒢)`. This is the shape in which
  clause (5) of [Stacks, Tag 0AYT] consumes the result: that clause asserts
  `χ(X, 𝒢 ⊗ ℰ) = n · χ(X, 𝒢)` for `ℰ` locally free of rank `n` and `𝒢` coherent with
  zero-dimensional support, and this reduces it to the *sheaf* isomorphism
  `𝒢 ⊗ ℰ ≅ 𝒢^{⊞ n}`, with the cohomology eliminated.

## Implementation notes

**Why the cohomology isomorphism is obtained from the long exact sequence rather than from
additivity of the functor.** `AlgebraicGeometry.cohomologyOverField` is
`CategoryTheory.Functor.rightDerived` of evaluation at the whole space, and Mathlib has **no
instance making a right derived functor additive** — so
`CategoryTheory.Functor.mapBiprod` is not available for it, and neither is
`CategoryTheory.Limits.PreservesBinaryBiproduct`. What *is* available is the long exact sequence
`AlgebraicGeometry.exists_cohomologyOverField_longExactSequence`, which holds with no hypothesis
at all. Applying it to the split short exact sequence
`0 ⟶ 𝒜 ⟶ 𝒜 ⊞ ℬ ⟶ ℬ ⟶ 0` gives exactness in the middle, while the splittings `biprod.fst` and
`biprod.inr` give a retraction and a section *through functoriality alone*
(`AlgebraicGeometry.cohomologyOverFieldMap_id` and
`AlgebraicGeometry.cohomologyOverFieldMap_comp`). A short exact sequence of modules with a
retraction of its injection splits, which is Mathlib's
`Function.Exact.splitInjectiveEquiv`. So the isomorphism is produced without ever asserting that
the derived functor is additive.

**And that detour is not necessary, though the sentence above is true of Mathlib.**
`CategoryTheory.Functor.additive_rightDerived` of
`StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/DerivedFunctorAdditive.lean` is a public
instance of this repository, so `CategoryTheory.Functor.mapBiprod` *is* available once
`CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBiproducts` — a lemma and not an
instance, which is the only reason `inferInstance` does not find it — turns additivity into
preservation of binary biproducts. The ring-base analogue of the two statements above,
`AlgebraicGeometry.nonempty_cohomology_ringBase_biprod_linearEquiv` of
`StacksFrontier/AlgebraicGeometry/CohomologyFinitenessTwists/RingBase.lean`, is built that way
and is four lines with no short exact sequence, no connecting map and no splitting. The proofs
below take the longer route; either route gives the same statements.

**The isomorphism is carried, not its dimension.** The statements below produce a `Nonempty` of
a `LinearEquiv` rather than an equality of `Module.finrank`s, because the additive statement
`Module.finrank k Hᵐ(𝒜 ⊞ ℬ) = Module.finrank k Hᵐ(𝒜) + Module.finrank k Hᵐ(ℬ)` is **false** in
general — take `Hᵐ(𝒜)` infinite-dimensional and `Hᵐ(ℬ)` of dimension one. The equality only
appears at the end, after the `n` summands have been identified with one another.

## References

* [Stacks Project, Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT)
* [Stacks Project, Tag 0BEJ](https://stacks.math.columbia.edu/tag/0BEJ)
* [Stacks Project, Tag 08AA](https://stacks.math.columbia.edu/tag/08AA)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped ZeroObject

universe u

/-! ### The dimension of a finite power of a vector space -/

namespace Module

/-- **`Module.finrank k (Fin n → V) = n * Module.finrank k V`, with no finiteness hypothesis on
`V`.** Both sides vanish when `V` is infinite-dimensional and `n` is positive: a power of an
infinite-dimensional space is infinite-dimensional, because `V` is the image of the projection.

The analogous statement for a product of two *different* spaces is false — `Module.finrank` of
an infinite-dimensional space is `0`, so `finrank (V × k) = 0` while
`finrank V + finrank k = 1`. Equal summands are exactly the case that escapes it. -/
theorem finrank_fun_fin (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V]
    (n : ℕ) : finrank k (Fin n → V) = n * finrank k V := by
  classical
  by_cases hV : FiniteDimensional k V
  · rw [finrank_pi_fintype k (M := fun _ : Fin n => V)]
    simp
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have : Subsingleton (Fin 0 → V) := ⟨fun a b => funext fun i => i.elim0⟩
      simp [finrank_zero_of_subsingleton]
    · have h0 : finrank k V = 0 := finrank_of_infinite_dimensional hV
      have hne : ¬ FiniteDimensional k (Fin n → V) := fun h =>
        hV (Module.Finite.of_surjective
          (LinearMap.proj (R := k) (φ := fun _ : Fin n => V) ⟨0, hn⟩)
          (fun v => ⟨fun _ => v, rfl⟩))
      rw [finrank_of_infinite_dimensional hne, h0, mul_zero]

end Module

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### Powers of a module under the biproduct -/

/-- **The `n`-fold biproduct `𝒢^{⊞ n}` of a module with itself**, by recursion on `n`. At
`n = 0` it is the zero object. -/
noncomputable def Scheme.Modules.biprodPow (G : X.Modules) : ℕ → X.Modules
  | 0 => 0
  | (n + 1) => G ⊞ G.biprodPow n

/-- A module isomorphic to a zero object is coherent: coherent modules contain the zero object
and are closed under isomorphism, being a weak Serre class ([Stacks, Tag 01BY] (5)). -/
theorem SheafOfModules.isCoherent_of_isZero {Z : X.Modules} (hZ : IsZero Z) :
    Z.IsCoherent := by
  let P : ObjectProperty X.Modules := fun M => M.IsCoherent
  let : P.IsWeakSerreClass := _root_.SheafOfModules.coherentModules_isWeakSerreClass
  exact P.prop_of_iso hZ.isoZero.symm P.prop_zero

/-- **A biproduct of coherent modules is coherent**: coherent modules are closed under
extensions ([Stacks, Tag 01BY] (4)) and a biproduct is an extension of one summand by the
other. -/
theorem SheafOfModules.isCoherent_biprod (A B : X.Modules) (hA : A.IsCoherent)
    (hB : B.IsCoherent) : (A ⊞ B).IsCoherent := by
  let P : ObjectProperty X.Modules := fun M => M.IsCoherent
  let : P.IsWeakSerreClass := _root_.SheafOfModules.coherentModules_isWeakSerreClass
  exact P.prop_biprod hA hB

/-- **Every power of a coherent module is coherent.** -/
theorem SheafOfModules.isCoherent_biprodPow (G : X.Modules) (hG : G.IsCoherent) :
    ∀ n : ℕ, (G.biprodPow n).IsCoherent
  | 0 =>
    SheafOfModules.isCoherent_of_isZero
      (show IsZero (G.biprodPow 0) from isZero_zero X.Modules)
  | (n + 1) =>
    SheafOfModules.isCoherent_biprod G (G.biprodPow n) hG
      (SheafOfModules.isCoherent_biprodPow G hG n)

/-! ### The short exact sequence of a biproduct, and its splitting -/

/-- The short exact sequence `0 ⟶ 𝒜 ⟶ 𝒜 ⊞ ℬ ⟶ ℬ ⟶ 0` of a biproduct. -/
noncomputable def biprodShortComplex (A B : X.Modules) : ShortComplex X.Modules :=
  ShortComplex.mk (biprod.inl : A ⟶ A ⊞ B) (biprod.snd : A ⊞ B ⟶ B) (by simp)

/-- The canonical splitting of `AlgebraicGeometry.biprodShortComplex`: the retraction is
`biprod.fst`, the section is `biprod.inr`, and their compatibility is
`CategoryTheory.Limits.biprod.total`. -/
noncomputable def biprodShortComplexSplitting (A B : X.Modules) :
    (biprodShortComplex A B).Splitting where
  r := biprod.fst
  s := biprod.inr
  f_r := biprod.inl_fst
  s_g := biprod.inr_snd
  id := biprod.total

variable (k : Type u) [Field k] (f : X ⟶ Spec (.of k))

/-! ### Cohomology of a biproduct -/

/-- **The cohomology of a biproduct is the product of the cohomologies**, as `k`-vector spaces,
with no hypothesis on `f` or on the modules.

The long exact sequence of `AlgebraicGeometry.exists_cohomologyOverField_longExactSequence`
applied to `0 ⟶ 𝒜 ⟶ 𝒜 ⊞ ℬ ⟶ ℬ ⟶ 0` gives exactness at the middle term; functoriality of
`AlgebraicGeometry.cohomologyOverFieldMap` turns `biprod.fst` into a retraction of the first map
and `biprod.inr` into a section of the second; and `Function.Exact.splitInjectiveEquiv` splits
the result. No additivity of the derived functor is used — Mathlib has no such instance. -/
theorem nonempty_cohomologyOverField_biprod_linearEquiv (A B : X.Modules) (m : ℕ) :
    Nonempty (cohomologyOverField k f (A ⊞ B) m ≃ₗ[k]
      cohomologyOverField k f A m × cohomologyOverField k f B m) := by
  obtain ⟨d, -, hab, -, -⟩ :=
    exists_cohomologyOverField_longExactSequence k f
      (biprodShortComplexSplitting A B).shortExact
  have hretr : (cohomologyOverFieldMap k f (biprod.fst : A ⊞ B ⟶ A) m).hom ∘ₗ
      (cohomologyOverFieldMap k f (biprod.inl : A ⟶ A ⊞ B) m).hom = LinearMap.id := by
    have h : cohomologyOverFieldMap k f (biprod.inl : A ⟶ A ⊞ B) m ≫
        cohomologyOverFieldMap k f (biprod.fst : A ⊞ B ⟶ A) m = 𝟙 _ := by
      rw [← cohomologyOverFieldMap_comp, biprod.inl_fst, cohomologyOverFieldMap_id]
    have h' := congrArg ModuleCat.Hom.hom h
    rwa [ModuleCat.hom_comp, ModuleCat.hom_id] at h'
  have hsect : (cohomologyOverFieldMap k f (biprod.snd : A ⊞ B ⟶ B) m).hom ∘ₗ
      (cohomologyOverFieldMap k f (biprod.inr : B ⟶ A ⊞ B) m).hom = LinearMap.id := by
    have h : cohomologyOverFieldMap k f (biprod.inr : B ⟶ A ⊞ B) m ≫
        cohomologyOverFieldMap k f (biprod.snd : A ⊞ B ⟶ B) m = 𝟙 _ := by
      rw [← cohomologyOverFieldMap_comp, biprod.inr_snd, cohomologyOverFieldMap_id]
    have h' := congrArg ModuleCat.Hom.hom h
    rwa [ModuleCat.hom_comp, ModuleCat.hom_id] at h'
  have hsurj : Function.Surjective
      (cohomologyOverFieldMap k f (biprod.snd : A ⊞ B ⟶ B) m).hom := fun y =>
    ⟨(cohomologyOverFieldMap k f (biprod.inr : B ⟶ A ⊞ B) m).hom y,
      congrFun (congrArg (fun l : _ →ₗ[k] _ => (l : _ → _)) hsect) y⟩
  exact ⟨(((hab m).splitInjectiveEquiv hsurj) ⟨_, hretr⟩).1⟩

/-- **The cohomology of a power is the power of the cohomology**, as `k`-vector spaces, with no
hypothesis on `f` or on the module. -/
theorem nonempty_cohomologyOverField_biprodPow_linearEquiv (G : X.Modules) (m : ℕ) :
    ∀ n : ℕ, Nonempty (cohomologyOverField k f (G.biprodPow n) m ≃ₗ[k]
      (Fin n → cohomologyOverField k f G m))
  | 0 => by
    obtain ⟨d, -, hab, -, -⟩ :=
      exists_cohomologyOverField_longExactSequence k f
        (S := ShortComplex.mk (𝟙 (0 : X.Modules)) (𝟙 (0 : X.Modules))
          (by rw [(isZero_zero X.Modules).eq_of_src (𝟙 (0 : X.Modules)) 0]; simp))
        { mono_f := inferInstance
          epi_g := inferInstance
          exact := ShortComplex.exact_of_isZero_X₂ _ (isZero_zero X.Modules) }
    have hsub : Subsingleton (cohomologyOverField k f (G.biprodPow 0) m) := by
      have h := hab m
      rw [cohomologyOverFieldMap_id] at h
      exact ⟨fun a b => ((h a).2 ⟨a, rfl⟩).trans ((h b).2 ⟨b, rfl⟩).symm⟩
    have : Subsingleton (Fin 0 → cohomologyOverField k f G m) :=
      ⟨fun a b => funext fun i => i.elim0⟩
    exact ⟨LinearEquiv.ofSubsingleton _ _⟩
  | (n + 1) => by
    obtain ⟨e⟩ := nonempty_cohomologyOverField_biprod_linearEquiv k f G (G.biprodPow n) m
    obtain ⟨e'⟩ := nonempty_cohomologyOverField_biprodPow_linearEquiv G m n
    exact ⟨e.trans (((LinearEquiv.refl k _).prodCongr e').trans
      (Fin.consLinearEquiv k (fun _ : Fin (n + 1) => cohomologyOverField k f G m)))⟩

/-- The dimension of the cohomology of a power is `n` times the dimension of the cohomology. -/
theorem finrank_cohomologyOverField_biprodPow (G : X.Modules) (n m : ℕ) :
    Module.finrank k (cohomologyOverField k f (G.biprodPow n) m) =
      n * Module.finrank k (cohomologyOverField k f G m) := by
  obtain ⟨e⟩ := nonempty_cohomologyOverField_biprodPow_linearEquiv k f G m n
  rw [e.finrank_eq, Module.finrank_fun_fin]

/-! ### The Euler characteristic of a power -/

/-- **`χ(X, 𝒢^{⊞ n}) = n · χ(X, 𝒢)`, unconditionally.** No finiteness of the cohomology is
needed: see the module docstring for why the equal-summand case escapes the obstruction that
makes [Stacks, Tag 08AA] depend on [Stacks, Tag 02O6]. -/
theorem eulerCharacteristic_biprodPow [IsProper f] (G : X.Modules) [hG : G.IsCoherent]
    (n : ℕ) (hGn : (G.biprodPow n).IsCoherent) :
    @eulerCharacteristic k _ X f _ (G.biprodPow n) hGn =
      (n : ℤ) * eulerCharacteristic k f G := by
  rw [eulerCharacteristic_eq_finsum, eulerCharacteristic_eq_finsum, mul_finsum]
  refine finsum_congr fun m => ?_
  rw [finrank_cohomologyOverField_biprodPow]
  push_cast
  ring

/-- **A coherent module isomorphic to `𝒢^{⊞ n}` has Euler characteristic `n · χ(X, 𝒢)`.**

This is the form in which clause (5) of [Stacks, Tag 0AYT] consumes the direct-sum formula. That
clause asserts `χ(X, 𝒢 ⊗ ℰ) = n · χ(X, 𝒢)` for `ℰ` locally free of rank `n` and `𝒢` coherent
with support of dimension at most zero; this theorem reduces it to the sheaf isomorphism
`𝒢 ⊗ ℰ ≅ 𝒢^{⊞ n}`, eliminating the cohomology — and in particular showing that the clause does
**not** need [Stacks, Tag 02O6], unlike the additivity of [Stacks, Tag 08AA] that the
neighbouring tags in the chain rest on.

No `@[stacks 0AYT]` attribute is attached: the hypothesis `e` is not a hypothesis of the tag. -/
theorem exists_eulerCharacteristic_eq_mul_of_iso_biprodPow [IsProper f] (G : X.Modules)
    [hG : G.IsCoherent] (T : X.Modules) (n : ℕ) (e : T ≅ G.biprodPow n) :
    ∃ hT : T.IsCoherent,
      @eulerCharacteristic k _ X f _ T hT = (n : ℤ) * eulerCharacteristic k f G := by
  have hGn : (G.biprodPow n).IsCoherent := SheafOfModules.isCoherent_biprodPow G hG n
  have hT : T.IsCoherent := by
    let P : ObjectProperty X.Modules := fun M => M.IsCoherent
    let : P.IsWeakSerreClass := _root_.SheafOfModules.coherentModules_isWeakSerreClass
    exact P.prop_of_iso e.symm hGn
  refine ⟨hT, ?_⟩
  rw [@eulerCharacteristic_eq_of_iso k _ X f _ T (G.biprodPow n) hT hGn e,
    eulerCharacteristic_biprodPow k f G n hGn]

end AlgebraicGeometry

end
