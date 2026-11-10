module

public import StacksFrontier.Algebra.MittagLeffler.TensorProductPi

@[expose] public section

universe u v

/-!
# The smallest submodule carrying an element of a tensor product with a flat Mittag-Leffler module

Let `R` be a commutative ring, let `M` be a flat Mittag-Leffler `R`-module, let `F` be an
`R`-module and let `x ∈ F ⊗[R] M`. Say a submodule `N ⊆ F` *carries* `x` when `x` lies in the
image of `N ⊗[R] M → F ⊗[R] M`. Then the submodules carrying `x` have a smallest element, and it
is a finite `R`-module.

The argument is the source's. Let `(N i)` be a family of submodules each carrying `x` and let
`φ : F → ∏ᵢ F/N i` be the product of the quotient maps, so that `Ker φ = ⨅ᵢ N i`. The composite
`N i ⊗[R] M → F ⊗[R] M → (F/N i) ⊗[R] M` vanishes, so `x` dies in every factor of
`∏ᵢ ((F/N i) ⊗[R] M)`; since `M` is Mittag-Leffler the canonical map from `(∏ᵢ F/N i) ⊗[R] M` to
that product is injective (Stacks 059M), whence `(φ ⊗ id_M)(x) = 0`. Flatness of `M` makes
`⨅ᵢ N i ⊗[R] M → F ⊗[R] M → (∏ᵢ F/N i) ⊗[R] M` exact, so `x` lies in the image of
`(⨅ᵢ N i) ⊗[R] M`. Applied to the family of *all* submodules carrying `x` this says that their
infimum carries `x`, hence is the least element of that set. Finiteness is then automatic: writing
`x` as the image of some `y` over the least such submodule `N` and applying
`Submodule.exists_fg_le_eq_rTensor_inclusion` to `y` produces a finitely generated `J ≤ N` that
still carries `x`, so `N ≤ J` and the two coincide.

## Main results

* `Stacks.MittagLeffler.SmallestSubmodule.solution`: the proof of Stacks 0AS6, as stated in
  `Submodule.exists_fg_isLeast_mem_range_rTensor_subtype_of_mittagLeffler`.

## Implementation notes

The two halves of the source's proof are the two private lemmas
`Stacks.MittagLeffler.SmallestSubmodule.mem_range_rTensor_subtype_iInf` — the infimum of a family
of submodules carrying `x` carries `x`, where flatness and Stacks 059M are consumed — and
`Stacks.MittagLeffler.SmallestSubmodule.fg_of_isLeast_mem_range_rTensor_subtype` — a least
submodule carrying `x` is finitely generated. The first is stated for a family rather than for the
set of all submodules carrying `x`, which is where it is applied through `sInf_eq_iInf'`: the
family form needs no nonemptiness hypothesis and keeps the quotients indexed by `ι` rather than by
a set of submodules.

Stacks 059M is phrased for `TensorProduct.piRightHom R R M Q : M ⊗[R] (∀ α, Q α) →ₗ[R]
∀ α, M ⊗[R] Q α`, with `M` on the left, while this file puts `M` on the right of every tensor
product; Mathlib has no left-handed form of `piRightHom`. The two sides are exchanged by
`TensorProduct.comm`, the compatibility being
`Stacks.MittagLeffler.SmallestSubmodule.piRightHom_comm_apply`, and the
consequence actually used is
`Stacks.MittagLeffler.SmallestSubmodule.eq_zero_of_forall_rTensor_proj_eq_zero`: an element of
`(∀ α, Q α) ⊗[R] M` all of whose projections to the `Q α ⊗[R] M` vanish is zero. That is the
right-handed reading of the injectivity of the comparison map, and it is the only form in which
the Mittag-Leffler hypothesis is used.

Mathlib has the exact sequence `N → F → F ⧸ N` (`LinearMap.exact_subtype_mkQ`) and the kernel of a
single quotient map (`Submodule.ker_mkQ`), but not their versions for a family, whose product of
quotient maps has kernel the infimum; the ideal-theoretic analogue of the latter is
`Ideal.ker_Pi_Quotient_mk`. Both are proved here as
`Stacks.MittagLeffler.SmallestSubmodule.ker_pi_mkQ` and
`Stacks.MittagLeffler.SmallestSubmodule.exact_subtype_iInf_pi_mkQ`.

## References

* [StacksProject 0AS6](https://stacks.math.columbia.edu/tag/0AS6)
-/



namespace Stacks.MittagLeffler.SmallestSubmodule

open TensorProduct

section

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-! ### Exchanging the two sides of the comparison map -/

/-- The comparison map `TensorProduct.piRightHom` of Stacks 059M, read on the other side of the
tensor product: for `t : (∀ α, Q α) ⊗[R] M`, the `α`-th component of the image of `t` under
`piRightHom R R M Q ∘ TensorProduct.comm` is the image of the `α`-th projection of `t`. -/
private lemma piRightHom_comm_apply {A : Type*} {Q : A → Type*} [∀ α, AddCommGroup (Q α)]
    [∀ α, Module R (Q α)] (t : (∀ α, Q α) ⊗[R] M) (α : A) :
    TensorProduct.piRightHom R R M Q (TensorProduct.comm R (∀ α, Q α) M t) α
      = TensorProduct.comm R (Q α) M ((LinearMap.proj α).rTensor M t) := by
  induction t using TensorProduct.inductionOn with
  | tmul p m => simp
  | add t₁ t₂ h₁ h₂ => simp [h₁, h₂, map_add]

/-- Injectivity of the comparison map of Stacks 059M, read on the other side of the tensor
product: if `M` is Mittag-Leffler then an element of `(∀ α, Q α) ⊗[R] M` whose image in
`Q α ⊗[R] M` vanishes for every `α` is zero. -/
private lemma eq_zero_of_forall_rTensor_proj_eq_zero
    (hinj : ∀ (A : Type v) (Q : A → Type v) [∀ α, AddCommGroup (Q α)] [∀ α, Module R (Q α)],
      Function.Injective (TensorProduct.piRightHom R R M Q))
    {A : Type v} {Q : A → Type v} [∀ α, AddCommGroup (Q α)] [∀ α, Module R (Q α)]
    {t : (∀ α, Q α) ⊗[R] M} (ht : ∀ α, (LinearMap.proj α).rTensor M t = 0) : t = 0 := by
  have h : TensorProduct.piRightHom R R M Q (TensorProduct.comm R (∀ α, Q α) M t) = 0 := by
    funext α
    rw [piRightHom_comm_apply, ht α, map_zero]
    rfl
  simpa using hinj A Q (h.trans (map_zero _).symm)

/-! ### The infimum of the submodules carrying an element -/

variable {F : Type v} [AddCommGroup F] [Module R F]

/-- The kernel of the product of the quotient maps of a family of submodules is the infimum of the
family. The one-submodule case is `Submodule.ker_mkQ`, the ideal-theoretic analogue
`Ideal.ker_Pi_Quotient_mk`. -/
private lemma ker_pi_mkQ {ι : Type*} (N : ι → Submodule R F) :
    LinearMap.ker (LinearMap.pi fun i => (N i).mkQ) = ⨅ i, N i := by
  simp [LinearMap.ker_pi]

/-- A family of submodules and the product of the quotient maps form an exact sequence
`⨅ i, N i → F → ∀ i, F ⧸ N i`. The one-submodule case is `LinearMap.exact_subtype_mkQ`. -/
private lemma exact_subtype_iInf_pi_mkQ {ι : Type*} (N : ι → Submodule R F) :
    Function.Exact (⨅ i, N i).subtype (LinearMap.pi fun i => (N i).mkQ) := by
  rw [LinearMap.exact_iff, ker_pi_mkQ, Submodule.range_subtype]

/-- An element of `F ⊗[R] M` carried by a submodule `N` dies in `(F ⧸ N) ⊗[R] M`. -/
private lemma rTensor_mkQ_eq_zero_of_mem_range {N : Submodule R F} {x : F ⊗[R] M}
    (hx : x ∈ LinearMap.range (N.subtype.rTensor M)) : N.mkQ.rTensor M x = 0 := by
  obtain ⟨y, rfl⟩ := hx
  rw [← LinearMap.rTensor_comp_apply, (LinearMap.exact_subtype_mkQ N).linearMap_comp_eq_zero]
  simp

/-- If `x ∈ F ⊗[R] M` lies in the image of `N i ⊗[R] M` for every member of a family `N` of
submodules of `F`, and `M` is flat with `TensorProduct.piRightHom` injective for every family of
`R`-modules in `Type v` — that is, `M` is a flat Mittag-Leffler module, by Stacks 059M — then `x`
lies in the image of `(⨅ i, N i) ⊗[R] M`. -/
private lemma mem_range_rTensor_subtype_iInf [Module.Flat R M]
    (hinj : ∀ (A : Type v) (Q : A → Type v) [∀ α, AddCommGroup (Q α)] [∀ α, Module R (Q α)],
      Function.Injective (TensorProduct.piRightHom R R M Q))
    {ι : Type v} {N : ι → Submodule R F} {x : F ⊗[R] M}
    (hN : ∀ i, x ∈ LinearMap.range ((N i).subtype.rTensor M)) :
    x ∈ LinearMap.range ((⨅ i, N i).subtype.rTensor M) := by
  have hx0 : (LinearMap.pi fun i => (N i).mkQ).rTensor M x = 0 := by
    refine eq_zero_of_forall_rTensor_proj_eq_zero hinj fun i => ?_
    rw [← LinearMap.rTensor_comp_apply, LinearMap.proj_pi]
    exact rTensor_mkQ_eq_zero_of_mem_range (hN i)
  obtain ⟨y, hy⟩ := (Module.Flat.rTensor_exact M (exact_subtype_iInf_pi_mkQ N) x).mp hx0
  exact ⟨y, hy⟩

/-! ### Finiteness of the least submodule carrying an element -/

/-- A least submodule carrying `x ∈ F ⊗[R] M` is finitely generated: `x` is the image of some
`y` over it, a finitely generated submodule carrying `y` carries `x`, and minimality forces it to
be everything. -/
private lemma fg_of_isLeast_mem_range_rTensor_subtype {x : F ⊗[R] M} {N : Submodule R F}
    (h : IsLeast {N : Submodule R F | x ∈ LinearMap.range (N.subtype.rTensor M)} N) : N.FG := by
  obtain ⟨y, hy⟩ := h.1
  obtain ⟨J, hJ, hle, z, hz⟩ := Submodule.exists_fg_le_eq_rTensor_inclusion (M := M) y
  have hJmem : x ∈ LinearMap.range (J.subtype.rTensor M) := by
    refine ⟨z, ?_⟩
    rw [← hy, hz, ← LinearMap.rTensor_comp_apply, Submodule.subtype_comp_inclusion]
  exact le_antisymm hle (h.2 hJmem) ▸ hJ

end

/-! ### The main result -/

/-- Let `M` be a flat Mittag-Leffler `R`-module and let `x ∈ F ⊗[R] M`. Among the submodules `N`
of `F` with `x` in the range of `N ⊗[R] M → F ⊗[R] M` there is a least one, and it is finitely
generated. -/
public theorem solution {R : Type u} [CommRing R] [Small.{v} R] {M : Type v} [AddCommGroup M]
    [Module R M] [Module.Flat R M]
    (hML : ∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
      (f : P →ₗ[R] M), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
        (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (N : Type v) [AddCommGroup N]
          [Module R N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N))
    {F : Type v} [AddCommGroup F] [Module R F] (x : F ⊗[R] M) :
    ∃ F' : Submodule R F, F'.FG ∧
      IsLeast {N : Submodule R F | x ∈ LinearMap.range (N.subtype.rTensor M)} F' := by
  have hinj := (Module.mittagLeffler_iff_piRightHom_injective R M).mp hML
  have h : IsLeast {N : Submodule R F | x ∈ LinearMap.range (N.subtype.rTensor M)}
      (sInf {N : Submodule R F | x ∈ LinearMap.range (N.subtype.rTensor M)}) := by
    refine ⟨?_, fun N hN => sInf_le hN⟩
    rw [sInf_eq_iInf']
    exact mem_range_rTensor_subtype_iInf hinj fun i => i.2
  exact ⟨_, fg_of_isLeast_mem_range_rTensor_subtype h, h⟩

end Stacks.MittagLeffler.SmallestSubmodule

/-!
# The smallest submodule carrying an element of a tensor product with a flat Mittag-Leffler module

Let `R` be a commutative ring, let `M` be a flat Mittag-Leffler `R`-module, let `F` be an
`R`-module and let `x ∈ F ⊗[R] M`. Call a submodule `N ⊆ F` *carrying* `x` if `x` lies in the
image of `N ⊗[R] M → F ⊗[R] M`; flatness of `M` makes that map injective, so this says `x` lies
in the submodule `N ⊗[R] M` of `F ⊗[R] M`. The submodules carrying `x` then have a smallest
element, and it is a finite `R`-module.

The source's proof is short. Let `(N_i)` be the family of all submodules carrying `x`. Then `x`
dies in `(F/N_i) ⊗[R] M` for each `i`, hence in `∏ᵢ ((F/N_i) ⊗[R] M)`, hence — this is where the
Mittag-Leffler hypothesis enters, through the injectivity of the canonical map
`(∏ᵢ F/N_i) ⊗[R] M → ∏ᵢ ((F/N_i) ⊗[R] M)` of Proposition 059M — already in
`(∏ᵢ F/N_i) ⊗[R] M`. Since `M` is flat, the kernel of `F ⊗[R] M → (∏ᵢ F/N_i) ⊗[R] M` is
`(⨅ᵢ N_i) ⊗[R] M`, so `⨅ᵢ N_i` carries `x` and is therefore the smallest such submodule.
Finiteness is then automatic: writing `x = ∑ⱼ fⱼ ⊗ mⱼ` with `fⱼ` in the smallest submodule
exhibits a finitely generated submodule of it that also carries `x`, so the two coincide.

## Main results

* `Submodule.exists_fg_isLeast_mem_range_rTensor_subtype_of_mittagLeffler`: for `M` flat and
  Mittag-Leffler and `x ∈ F ⊗[R] M`, the submodules `N ⊆ F` whose tensor product with `M` contains
  `x` have a least element, and it is finitely generated.

## Implementation notes

The hypothesis is spelled out inline in the intrinsic form 059E (1), exactly as in
Proposition 059M and Lemma 05CQ: every map `f : P → M` from a finitely presented module dominates
and is dominated by a map `g : P → Q` into a finitely presented module, domination meaning
`Ker(f ⊗ id_N) = Ker(g ⊗ id_N)` for every `R`-module `N`; Mathlib's
`CategoryTheory.Functor.IsMittagLeffler` is the Mittag-Leffler condition on an inverse *system*,
not on a module. Proposition 059M is what converts the hypothesis into the injectivity the proof
consumes.

The source's `x ∈ N ⊗_R M` for a submodule `N ⊆ F` is rendered as
`x ∈ LinearMap.range (N.subtype.rTensor M)`, the spelling of Mathlib's
`TensorProduct.exists_of_fg` and `Submodule.exists_fg_le_eq_rTensor_subtype`. The canonical map is
thereby pinned to `LinearMap.rTensor M N.subtype`. Under the flatness hypothesis this range is a
copy of `N ⊗[R] M` inside `F ⊗[R] M`, which is the sense in which the source reads `⊆`; the range
formulation needs no flatness to be meaningful, so the statement is the source's without a
side condition attached to its own wording.

"There exists a smallest submodule" is `IsLeast` on the set of submodules carrying `x`: it packages
both halves, that the witness carries `x` and that it is below every submodule that does, and it
identifies the witness as the infimum of that set (`IsLeast.csInf_eq`), which is the description
the source's proof produces. "Finite `R`-module" is `Submodule.FG`, equivalent to
`Module.Finite R ↥N` by `Module.Finite.iff_fg` and the form used by the neighbouring Mathlib
lemmas on finiteness in tensor products.

`F` and `M` and the test modules of the Mittag-Leffler condition all live in one universe
`Type v`, with `R` `v`-small, as in 059D, 059M and 05CQ. `Small.{v} R` is not decoration: it is
what makes the displayed quantifier over finitely presented modules in `Type v` the source's
quantifier over all finitely presented modules, hence what makes the hypothesis Mittag-Leffler-ness
rather than a weakening of it, and it is carried by 059M. It holds automatically when `R : Type v`,
by `small_self`. A module `F` in a larger universe is reached by applying the statement to a
`ULift` copy, submodules and the tensor product being transported along the isomorphism.

Faithfulness. (1) Every hypothesis is used by the conclusion: without flatness the conclusion
fails for `R = ℤ`, `M = ℤ/p` and `F = ℤ` with `x = 1 ⊗ 1`, where every `nℤ` with `p ∤ n` carries
`x` and their infimum `0` does not — and this `M`, being finitely presented, is Mittag-Leffler, so
the example isolates flatness; without the Mittag-Leffler hypothesis it fails for some finite
free `F`, since for flat `M` the conclusion for finite free `F` is *equivalent* to Mittag-Leffler
by Lemma 059S, so e.g. `M = ℚ` over `R = ℤ` is a counterexample; and `Small.{v} R` is used as
described above. (2) The scalars and the base are the source's: one commutative ring `R`
throughout, `F ⊗[R] M` and every tensor product in the Mittag-Leffler condition over `R`, every
map `R`-linear, submodules `R`-submodules of `F`; nothing is localized or base changed.
(3) The canonical map `N ⊗_R M → F ⊗_R M` is pinned to `LinearMap.rTensor M N.subtype`, and the
conclusion is not bare existence of a submodule: `IsLeast` states the characterizing property,
that the witness carries `x` and is contained in every submodule that does, which determines it
uniquely. (4) The instantiation is not degenerate: for `R = ℤ`, `M = ℤ` (free, hence flat and
Mittag-Leffler), `F = ℤ × ℤ` and `x = (1, 0) ⊗ 1` the hypotheses hold and the least submodule is
`ℤ · (1, 0)`, neither `⊥` nor `⊤`, and finitely generated as claimed.

## References

* [StacksProject 0AS6](https://stacks.math.columbia.edu/tag/0AS6)
-/



open TensorProduct

@[expose] public section

/-- Let `R` be a commutative ring, let `M` be a flat Mittag-Leffler `R`-module, let `F` be an
`R`-module and let `x ∈ F ⊗[R] M`. Then among the submodules `N ⊆ F` with `x ∈ N ⊗[R] M` — that is,
with `x` in the range of `N ⊗[R] M → F ⊗[R] M` — there is a smallest one, and it is a finite
`R`-module.

Being Mittag-Leffler is spelled out inline as condition (1) of Proposition 059E: every map
`f : P → M` from a finitely presented `R`-module dominates and is dominated by a map `g : P → Q`
into a finitely presented `R`-module, that is `Ker(f ⊗ id_N) = Ker(g ⊗ id_N)` for every
`R`-module `N`. -/
@[stacks 0AS6 "Mittag-Leffler is spelled out inline as condition (1) of 059E, as in 059M and 05CQ;
`x ∈ N ⊗_R M` is membership in the range of `N.subtype.rTensor M`, and `smallest` is `IsLeast`.
Test data in the universe of `M` and `F`, whence `Small.{v} R`. See the module docstring."]
public theorem Submodule.exists_fg_isLeast_mem_range_rTensor_subtype_of_mittagLeffler
    {R : Type u} [CommRing R] [Small.{v} R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Flat R M]
    (hML : ∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
      (f : P →ₗ[R] M), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
        (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (N : Type v) [AddCommGroup N]
          [Module R N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N))
    {F : Type v} [AddCommGroup F] [Module R F] (x : F ⊗[R] M) :
    ∃ F' : Submodule R F, F'.FG ∧
      IsLeast {N : Submodule R F | x ∈ LinearMap.range (N.subtype.rTensor M)} F' :=
  Stacks.MittagLeffler.SmallestSubmodule.solution hML x

end

/-!
# Flat Mittag-Leffler modules, via smallest submodules of finite free modules

Let `R` be a commutative ring and let `M` be a flat `R`-module. Say that a submodule `N` of an
`R`-module `F` *carries* an element `x` of `F ⊗[R] M` if `x` lies in the range of
`N ⊗[R] M → F ⊗[R] M`. This file proves Stacks 059S: `M` is Mittag-Leffler if and only if, for
every finite free `R`-module `F` and every `x ∈ F ⊗[R] M`, the submodules of `F` carrying `x` have
a least element.

The forward implication is Lemma 0AS6, which proves it for an arbitrary `F` and moreover produces
a finitely generated witness.

For the converse the mechanism is a single observation. Fix a flat `M`, a module `G`, an element
`x ∈ G ⊗[R] M` whose carriers have a least element `N₀`, and a map `u : G → T`. Then
`u ⊗ id_M` kills `x` if and only if `N₀ ⊆ Ker u`: flatness makes
`Ker(u ⊗ id_M) = (Ker u) ⊗[R] M`, so `x` being killed says exactly that `Ker u` carries `x`, and
`N₀` is the least such submodule. So the least carrier of `x` computes, uniformly in `T`, which
maps out of `G` kill `x` after tensoring with `M`.

That observation turns the right-hand side into the Mittag-Leffler condition, in the form of
Lemma 05CP: it suffices to dominate maps `f : F → M` out of finite free modules. Choose a finite
basis `b` of `F` and let `x = ∑ i, b i ⊗ f (b i) ∈ F ⊗[R] M` be the element corresponding to `f`
under `Hom_R(F, M) = F^∨ ⊗_R M` — the identification of the source's proof, written in the basis,
which is what makes `F` play both the role of the source of `f` and the role of the module the
hypothesis is applied to. An element `y = ∑ i, b i ⊗ t i` of `F ⊗[R] T` corresponds in the same
way to the map `u = b.constr t : F → T`, and both `Ker(f ⊗ id_T)` and the least carrier `N₀` of
`x` see `y` through `u`, because the pairing `(f, t) ↦ ∑ i, f (b i) ⊗ t i` is symmetric in its two
arguments: `(f ⊗ id_T) y = (u ⊗ id_M) x` up to the commutativity `T ⊗ M ≅ M ⊗ T`, so
`y ∈ Ker(f ⊗ id_T)` if and only if `N₀ ⊆ Ker u`. Since `N₀` is finitely generated — the source
notes this, and it also follows from leastness, an element of `N₀ ⊗[R] M` being a finite sum — a
finite generating family `φ : Fin k → F` of `N₀` may be paired against `y` through the dual basis
of `b`, that is through `g = (⟨φ a, -⟩)_a : F → R^k`, and `N₀ ⊆ Ker u` says precisely that
`g ⊗ id_T` kills `y`. So `f` and `g` dominate each other, and `R^k` is finitely presented.

## Main results

* `Stacks.MittagLeffler.FlatCharacterization.solution`: Stacks 059S, the statement of
  `Module.mittagLeffler_iff_exists_isLeast_mem_range_rTensor_subtype`.

## Implementation notes

The route is not the source's. The source writes `M` as a directed colimit of finite free
modules by Lazard's theorem (Theorem 058G), reduces to the Mittag-Leffler condition on the
inverse system of duals by Remark 059G, and identifies the image of
`Hom_R(M j, R) → Hom_R(M i, R)` with the least carrier of the transition map `f i j`. The proof
here keeps the identification `Hom_R(F, M) = F^∨ ⊗_R M` and the computation of the least carrier,
which is where the mathematics of that argument lives, but replaces the colimit by Lemma 05CP,
which already reduces the Mittag-Leffler condition to maps out of finite free modules. No
colimit, no dual system and no cofinality argument are then needed, and flatness is consumed once,
in `Stacks.MittagLeffler.FlatCharacterization.rTensor_eq_zero_iff_le_ker`, rather than through
Lazard's theorem.

Since the finite free module supplied by 05CP is abstract, a basis of it is chosen rather than
working with a model `Fin n → R`; the basis is also what identifies `F` with its own dual
(`Module.Basis.toDual`), which is why the hypothesis can be applied to `F` itself. The finitely
presented module produced is `Fin k → Shrink.{v} R`, the copy of `R^k` in the universe of the test
data, `R` itself living in a possibly larger universe; `Shrink.linearEquiv` transports freeness
and finiteness to it, and the computation is carried out in `Fin k → R`, the two being
interchangeable for the purposes of a kernel by
`Stacks.MittagLeffler.FlatCharacterization.ker_rTensor_equiv_comp`, tensoring a
linear equivalence with `T` again giving an equivalence.

## References

* [StacksProject 059S](https://stacks.math.columbia.edu/tag/059S)
-/

namespace Stacks.MittagLeffler.FlatCharacterization



open scoped TensorProduct

variable {R : Type u} [CommRing R]

section Basis

variable {ι ν F M T : Type*} [Fintype ι] [Fintype ν] [AddCommGroup F] [Module R F]
  [AddCommGroup M] [Module R M] [AddCommGroup T] [Module R T] (b : Module.Basis ι R F)

/-- A sum `∑ i, b i ⊗ t i` over a finite basis of `F` vanishes exactly when every `t i` does.
This is `TensorProduct.sum_tmul_basis_left_eq_zero` for a `Fintype` index. -/
private theorem sum_tmul_eq_zero_iff (t : ι → T) :
    ∑ i, b i ⊗ₜ[R] t i = 0 ↔ ∀ i, t i = 0 := by
  refine ⟨fun h i => ?_, fun h => by simp [h]⟩
  have h0 : ((Finsupp.equivFunOnFinite.symm t).sum fun i n => b i ⊗ₜ[R] n) = 0 := by
    rwa [Finsupp.sum_fintype _ _ fun i => TensorProduct.tmul_zero T (b i)]
  simpa using congrArg (fun c : ι →₀ T => c i)
    (TensorProduct.sum_tmul_basis_left_eq_zero b _ h0)

/-- An element of `F ⊗[R] T`, for `F` free with a finite basis `b`, is `∑ i, b i ⊗ t i` for a
family `t`, unique by `sum_tmul_eq_zero_iff`; only existence is needed here. -/
private theorem exists_sum_tmul (y : F ⊗[R] T) : ∃ t : ι → T, y = ∑ i, b i ⊗ₜ[R] t i := by
  obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_left b y
  exact ⟨c, Finsupp.sum_fintype _ _ fun i => TensorProduct.tmul_zero T (b i)⟩

/-- **The pairing `Hom_R(F, M) × Hom_R(F, T) → M ⊗[R] T` is symmetric.** Under the two
identifications `F ⊗[R] T = Hom_R(F, T)` and `F ⊗[R] M = Hom_R(F, M)` afforded by a finite basis
`b` of `F`, applying `f ⊗ id_T` to the element `∑ i, b i ⊗ t i` of `F ⊗[R] T` and applying
`b.constr t ⊗ id_M` to the element `∑ i, b i ⊗ f (b i)` of `F ⊗[R] M` give the same answer,
`∑ i, f (b i) ⊗ t i`, up to the commutativity `T ⊗[R] M ≅ M ⊗[R] T`. -/
private theorem rTensor_sum_tmul_comm (f : F →ₗ[R] M) (t : ι → T) :
    (f.rTensor T) (∑ i, b i ⊗ₜ[R] t i)
      = TensorProduct.comm R T M (((b.constr R t).rTensor M) (∑ i, b i ⊗ₜ[R] f (b i))) := by
  simp only [map_sum, LinearMap.rTensor_tmul, Module.Basis.constr_basis, TensorProduct.comm_tmul]

/-- Pairing the element `∑ i, b i ⊗ t i` of `F ⊗[R] T` against a family `φ : ν → F`, read as
functionals through the dual basis of `b`, computes the values on `φ` of the map
`u = b.constr t : F → T` that `∑ i, b i ⊗ t i` corresponds to. -/
private theorem rTensor_pi_toDual_sum_tmul [DecidableEq ι] (t : ι → T) (φ : ν → F) :
    (LinearMap.rTensor T (LinearMap.pi fun a => b.toDual (φ a))) (∑ i, b i ⊗ₜ[R] t i)
      = ∑ a, Pi.basisFun R ν a ⊗ₜ[R] (b.constr R t) (φ a) := by
  classical
  simp only [map_sum, LinearMap.rTensor_tmul, Module.Basis.constr_apply_fintype,
    Module.Basis.equivFun_apply, TensorProduct.tmul_sum, Pi.basisFun_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hterm : ∀ a : ν, Pi.single a (1 : R) ⊗ₜ[R] (b.repr (φ a) i • t i)
      = (Pi.single a (b.repr (φ a) i) : ν → R) ⊗ₜ[R] t i := fun a => by
    rw [← TensorProduct.smul_tmul, ← Pi.single_smul, smul_eq_mul, mul_one]
  simp only [hterm, ← TensorProduct.sum_tmul, Finset.univ_sum_single]
  congr 1
  funext a
  rw [LinearMap.pi_apply, Module.Basis.toDual_apply_left]

end Basis

section LeastCarrier

variable {M G : Type*} [AddCommGroup M] [Module R M] [AddCommGroup G] [Module R G]
  {x : G ⊗[R] M} {N₀ : Submodule R G}

/-- **The mechanism of Stacks 059S.** For `M` flat and `x ∈ G ⊗[R] M` with a least carrier `N₀`,
a map `u : G → T` kills `x` after tensoring with `M` exactly when `N₀ ⊆ Ker u`. Flatness enters
through `Ker(u ⊗ id_M) = (Ker u) ⊗[R] M`, which turns the left-hand side into the statement that
`Ker u` carries `x`. -/
private theorem rTensor_eq_zero_iff_le_ker [Module.Flat R M]
    (hN₀ : IsLeast {N : Submodule R G | x ∈ LinearMap.range (N.subtype.rTensor M)} N₀)
    {T : Type*} [AddCommGroup T] [Module R T] (u : G →ₗ[R] T) :
    u.rTensor M x = 0 ↔ N₀ ≤ LinearMap.ker u := by
  refine ⟨fun hx => hN₀.2 ((Module.Flat.rTensor_exact M
    (LinearMap.exact_subtype_ker_map u) x).mp hx), fun h => ?_⟩
  obtain ⟨z, hz⟩ := hN₀.1
  rw [← hz, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp,
    show u ∘ₗ N₀.subtype = 0 from by ext w; exact h w.2]
  simp

end LeastCarrier

/-- Precomposing with a linear equivalence does not change the kernel of a tensored map. -/
private theorem ker_rTensor_equiv_comp {A B C T : Type*} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C] [AddCommGroup T] [Module R T]
    (e : B ≃ₗ[R] C) (h : A →ₗ[R] B) :
    LinearMap.ker ((e.toLinearMap ∘ₗ h).rTensor T) = LinearMap.ker (h.rTensor T) := by
  rw [LinearMap.rTensor_comp]
  exact LinearMap.ker_comp_of_ker_eq_bot _
    (LinearMap.ker_eq_bot_of_injective (e.rTensor T).injective)

/-- The converse half of Stacks 059S, in the shape Lemma 05CP asks for: if the submodules of a
finite free module carrying an element of its tensor product with the flat module `M` always have
a least element, then every map out of a finite free module into `M` dominates and is dominated by
a map into a finitely presented module. -/
private theorem exists_finitePresentation_ker_rTensor_eq [Small.{v} R] {M : Type v}
    [AddCommGroup M] [Module R M] [Module.Flat R M]
    (h₂ : ∀ (F : Type v) [AddCommGroup F] [Module R F] [Module.Free R F] [Module.Finite R F]
      (x : F ⊗[R] M), ∃ F' : Submodule R F,
        IsLeast {N : Submodule R F | x ∈ LinearMap.range (N.subtype.rTensor M)} F')
    (F : Type v) [AddCommGroup F] [Module R F] [Module.Free R F] [Module.Finite R F]
    (f : F →ₗ[R] M) :
    ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q) (_ : Module.FinitePresentation R Q)
      (g : F →ₗ[R] Q), ∀ (N : Type v) [AddCommGroup N] [Module R N],
        LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N) := by
  classical
  obtain ⟨ι, _, ⟨b⟩⟩ : ∃ (ι : Type v) (_ : Fintype ι), Nonempty (Module.Basis ι R F) :=
    ⟨Module.Free.ChooseBasisIndex R F, inferInstance, ⟨Module.Free.chooseBasis R F⟩⟩
  obtain ⟨N₀, hN₀⟩ := h₂ F (∑ i, b i ⊗ₜ[R] f (b i))
  obtain ⟨k, φ, hφ⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (Stacks.MittagLeffler.SmallestSubmodule.fg_of_isLeast_mem_range_rTensor_subtype hN₀)
  have hfree : Module.Free R (Shrink.{v} R) := Module.Free.of_equiv (Shrink.linearEquiv R R).symm
  have hfin : Module.Finite R (Shrink.{v} R) := Module.Finite.equiv (Shrink.linearEquiv R R).symm
  refine ⟨Fin k → Shrink.{v} R, inferInstance, inferInstance,
    Module.finitePresentation_of_projective R _,
    (LinearEquiv.piCongrRight fun _ => Shrink.linearEquiv R R).symm.toLinearMap ∘ₗ
      LinearMap.pi fun a => b.toDual (φ a), ?_⟩
  intro T _ _
  rw [ker_rTensor_equiv_comp]
  ext y
  obtain ⟨t, rfl⟩ := exists_sum_tmul b y
  simp only [LinearMap.mem_ker]
  calc (f.rTensor T) (∑ i, b i ⊗ₜ[R] t i) = 0
      ↔ ((b.constr R t).rTensor M) (∑ i, b i ⊗ₜ[R] f (b i)) = 0 := by
        rw [rTensor_sum_tmul_comm]
        exact map_eq_zero_iff _ (TensorProduct.comm R T M).injective
    _ ↔ N₀ ≤ LinearMap.ker (b.constr R t) := rTensor_eq_zero_iff_le_ker hN₀ _
    _ ↔ ∀ a, (b.constr R t) (φ a) = 0 := by
        rw [← hφ, Submodule.span_le]; simp [Set.subset_def, SetLike.mem_coe]
    _ ↔ (LinearMap.rTensor T (LinearMap.pi fun a => b.toDual (φ a)))
          (∑ i, b i ⊗ₜ[R] t i) = 0 := by
        rw [rTensor_pi_toDual_sum_tmul, sum_tmul_eq_zero_iff]

/-- Let `R` be a commutative ring and let `M` be a flat `R`-module. Then `M` is Mittag-Leffler if
and only if for every finite free `R`-module `F` and every `x ∈ F ⊗[R] M` there is a smallest
submodule `F'` of `F` with `x ∈ F' ⊗[R] M`. -/
public theorem solution (R : Type u) [CommRing R] [Small.{v} R] (M : Type v) [AddCommGroup M]
    [Module R M] [Module.Flat R M] :
    (∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
        (f : P →ₗ[R] M), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
          (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (N : Type v) [AddCommGroup N]
            [Module R N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N)) ↔
      ∀ (F : Type v) [AddCommGroup F] [Module R F] [Module.Free R F] [Module.Finite R F]
        (x : F ⊗[R] M), ∃ F' : Submodule R F,
          IsLeast {N : Submodule R F | x ∈ LinearMap.range (N.subtype.rTensor M)} F' := by
  refine ⟨fun hML F _ _ _ _ x => ?_, fun h₂ => ?_⟩
  · obtain ⟨F', -, hF'⟩ :=
      Submodule.exists_fg_isLeast_mem_range_rTensor_subtype_of_mittagLeffler hML x
    exact ⟨F', hF'⟩
  · rw [Module.mittagLeffler_iff_forall_finite_free]
    exact fun F _ _ _ _ f => exists_finitePresentation_ker_rTensor_eq h₂ F f

end Stacks.MittagLeffler.FlatCharacterization

/-!
# Flat Mittag-Leffler modules, via smallest submodules of finite free modules

Let `R` be a commutative ring and let `M` be a *flat* `R`-module. Say that a submodule `N` of an
`R`-module `F` *carries* an element `x` of `F ⊗[R] M` if `x` lies in the image of
`N ⊗[R] M → F ⊗[R] M`; flatness makes that map injective, so this says `x` lies in the submodule
`N ⊗[R] M` of `F ⊗[R] M`, which is how the source writes it. An infinite intersection of
submodules carrying `x` need not carry `x`, and this file states that whether the submodules
carrying a given `x` always have a *smallest* element, for `F` finite free, is exactly the
Mittag-Leffler condition on `M`.

The forward implication is the case `F` finite free of Lemma 0AS6, which proves it for arbitrary
`F` and moreover gets a finitely generated witness. For the converse, flatness lets one write `M`
as a directed colimit `M = colim M i` of finite free modules (Theorem 058G, Lazard's theorem),
and by Remark 059G it is enough that the inverse system `(Hom_R(M i, R))` be Mittag-Leffler:
fixing `i` and letting `Q j` be the image of `Hom_R(M j, R) → Hom_R(M i, R)`, the identification
`Hom_R(M i, M j) = Hom_R(M i, R) ⊗[R] M j` exhibits `Q j` as the smallest submodule of
`Hom_R(M i, R)` carrying `f i j`, and the hypothesis applied to the finite free
`F = Hom_R(M i, R)` and to `x = f i`, the image of `M i → M` in `Hom_R(M i, R) ⊗[R] M`, produces
a submodule `Q` to which the `Q j` stabilize.

## Main results

* `Module.mittagLeffler_iff_exists_isLeast_mem_range_rTensor_subtype`: a flat `R`-module `M` is
  Mittag-Leffler if and only if, for every finite free `R`-module `F` and every `x ∈ F ⊗[R] M`,
  the submodules of `F` carrying `x` have a least element.

## Implementation notes

Mathlib has no predicate for a Mittag-Leffler *module*: its
`CategoryTheory.Functor.IsMittagLeffler` is the Mittag-Leffler condition on an inverse *system*,
which is condition (4) of Proposition 059E for the system of duals. So being Mittag-Leffler is
spelled out inline here in the intrinsic form 059E (1), exactly as in Proposition 059M, Lemma
05CQ and Lemma 0AS6: every map `f : P → M` from a finitely presented module dominates and is
dominated by a map `g : P → Q` into a finitely presented module, domination meaning
`Ker(f ⊗ id_N) = Ker(g ⊗ id_N)` for every `R`-module `N`. The left-hand side here is therefore
byte-for-byte the left-hand side of 059M and the hypothesis `hML` of 0AS6.

This project does carry Definition 059F as a predicate, `IsMittagLeffler`, and the left-hand side
is that predicate on the nose: `isMittagLeffler_def_iff` identifies it with
`IsMittagLeffler.{u, v, v, v, v} R M`, the only differences being that the predicate reads mutual
domination as a pair of kernel inclusions rather than an equality, and that it carries the
universes of `P`, of `Q` and of the test module `N` as three independent parameters, pinned to `v`
here. The inline form is the one kept, being literally the hypothesis `hML` of 0AS6 and the
Mittag-Leffler conjunct of Lemma 05D0 and Lemma 059T.

"`F` is a finite free `R`-module" is `[Module.Free R F] [Module.Finite R F]`, the abstract form,
rather than a choice of model `Fin n → R`: the concrete choice would have to be undone by every
user, and `Module.Free.chooseBasis` recovers a basis indexed by a `Fintype`. "`x ∈ F' ⊗_R M` for
a submodule `F' ⊆ F`" is `x ∈ LinearMap.range (F'.subtype.rTensor M)`, the spelling of Mathlib's
`TensorProduct.exists_of_fg` and `Submodule.exists_fg_le_eq_rTensor_subtype` and of the sibling
0AS6; it pins the canonical map to `LinearMap.rTensor M F'.subtype`, and under flatness its range
is a copy of `F' ⊗[R] M` inside `F ⊗[R] M`, which is the sense in which the source reads `∈`.
"There exists a smallest submodule" is `IsLeast` on the set of submodules carrying `x`: it
packages both halves, that the witness carries `x` and that it is below every submodule that
does, hence determines the witness uniquely and identifies it with the infimum of that set
(`IsLeast.csInf_eq`), which is what the source's proof produces. Unlike 0AS6, no finiteness of
the witness is asserted, since the source asserts none here and it is automatic for `F` finite
free.

`M`, `F` and the test modules of the Mittag-Leffler condition all live in one universe `Type v`,
with `R` `v`-small, as in 059D, 059E, 059M, 05CQ and 0AS6. `Small.{v} R` is load-bearing on both
sides: on the left it is what makes the displayed quantifier over finitely presented modules in
`Type v` the source's quantifier over all of them, hence what makes the condition Mittag-Leffler
rather than a weakening; on the right it is what puts a finite free module of each rank in
`Type v` at all (`Fin n → Shrink.{v} R`, free and finite by transport along
`Shrink.linearEquiv R R`), without which the right-hand side would be near-vacuous. It holds
automatically when `R : Type v`, by `small_self`. A module in a larger universe is reached by
applying the statement to a `ULift` copy, submodules and the tensor product being transported
along the isomorphism.

Faithfulness. (1) Every hypothesis is used by the conclusion: flatness is not decoration but the
source's standing hypothesis, consumed in both directions — without it the forward implication
fails for `R = ℤ`, `M = ℤ/5` and `F = ℤ` with `x = 1 ⊗ 1`, where `nℤ` carries `x` exactly when
`5 ∤ n` and no such submodule is least, while `M`, being finitely presented, is Mittag-Leffler;
and the converse consumes it through Lazard's theorem 058G, which is how the colimit of finite
free modules is obtained. `Small.{v} R` is used as described above. (2) The scalars and the base
are the source's: one commutative ring `R` throughout, `F ⊗[R] M` and every tensor product of the
Mittag-Leffler condition over `R`, every map `R`-linear, submodules `R`-submodules of `F`;
nothing is localized or base changed. (3) Where the source names canonical maps the statement
pins them: `N ⊗_R M → F ⊗_R M` is `LinearMap.rTensor M N.subtype`, and the tensored maps of the
Mittag-Leffler condition are `LinearMap.rTensor N f` and `LinearMap.rTensor N g`, their kernels
compared by equality; the right-hand side is not bare existence of a submodule, `IsLeast` being
the characterising property. (4) The instantiation is not degenerate and neither side is vacuous:
for `R = ℤ` and `M = ℤ` both sides hold — `M` is free, hence flat and Mittag-Leffler, and for
`F = ℤ × ℤ` and `x = (1, 0) ⊗ 1` the least submodule is `ℤ ∙ (1, 0)`, neither `⊥` nor `⊤` —
while for `R = ℤ` and `M = ℚ` both fail, `ℚ` being flat and not Mittag-Leffler by Example 059I,
and `x = 1 ⊗ 1 ∈ ℤ ⊗[ℤ] ℚ` being carried by every `nℤ` with `n ≠ 0` and by no least submodule.

## References

* [StacksProject 059S](https://stacks.math.columbia.edu/tag/059S)
-/



open TensorProduct

@[expose] public section

/-- Let `R` be a commutative ring and let `M` be a flat `R`-module. Then `M` is Mittag-Leffler if
and only if for every finite free `R`-module `F` and every `x ∈ F ⊗[R] M` there is a smallest
submodule `F'` of `F` with `x ∈ F' ⊗[R] M` — that is, with `x` in the range of
`F' ⊗[R] M → F ⊗[R] M`.

Being Mittag-Leffler is spelled out inline as condition (1) of Proposition 059E: every map
`f : P → M` from a finitely presented `R`-module dominates and is dominated by a map `g : P → Q`
into a finitely presented `R`-module, that is `Ker(f ⊗ id_N) = Ker(g ⊗ id_N)` for every
`R`-module `N`. This is Definition 059F, `IsMittagLeffler`, by `isMittagLeffler_def_iff`. -/
@[stacks 059S "Mittag-Leffler is spelled out inline as condition (1) of 059E, as in 059M and
0AS6; `finite free` is `Module.Free` and `Module.Finite`, `x ∈ F' ⊗_R M` is membership in the
range of `F'.subtype.rTensor M`, and `smallest` is `IsLeast`. Test data in the universe of `M`,
whence `Small.{v} R`. See the module docstring."]
public theorem Module.mittagLeffler_iff_exists_isLeast_mem_range_rTensor_subtype (R : Type u)
    [CommRing R] [Small.{v} R] (M : Type v) [AddCommGroup M] [Module R M] [Module.Flat R M] :
    (∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
        (f : P →ₗ[R] M), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
          (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (N : Type v) [AddCommGroup N]
            [Module R N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N)) ↔
      ∀ (F : Type v) [AddCommGroup F] [Module R F] [Module.Free R F] [Module.Finite R F]
        (x : F ⊗[R] M), ∃ F' : Submodule R F,
          IsLeast {N : Submodule R F | x ∈ LinearMap.range (N.subtype.rTensor M)} F' :=
  Stacks.MittagLeffler.FlatCharacterization.solution R M

end
