module

public import StacksFrontier.Algebra.MittagLeffler.TensorProductPi

@[expose] public section

universe u v w

/-!
# Mittag-Leffler passes to a colimit of a universally injective directed system

Let `R` be a commutative ring, let `F : J ⥤ ModuleCat R` be a directed system `(M i, f i j)` of
`R`-modules over a nonempty directed preorder `J`, and let `c` be a colimit cocone on `F`, so that
`M = c.pt` is `colim_i M i`. This file proves Stacks 0AS7: if every transition map is universally
injective and every `M i` is Mittag-Leffler, then `M` is Mittag-Leffler.

Proposition 059M turns "`M` is Mittag-Leffler" into injectivity of the comparison map
`TensorProduct.piRightHom R R M Q : M ⊗[R] (∀ α, Q α) → ∀ α, M ⊗[R] Q α` for every family `Q`, so
the route of the source is: an element of `M ⊗[R] (∀ α, Q α)` comes from some `M i ⊗[R] (∀ α, Q α)`
because tensoring commutes with the colimit; its image under `piRightHom` for `M i` has every
component killed by `f i ⊗ id`, hence vanishes because `f i` is universally injective; and then the
element itself vanishes by 059M for `M i`.

## Main results

* `Stacks.MittagLeffler.DirectedColimit.solution`: Stacks 0AS7, the statement of
  `ModuleCat.mittagLeffler_pt_of_forall_mittagLeffler_of_forall_rTensor_injective`.

## Implementation notes

The canonical maps of a colimit cocone are universally injective as soon as the transition maps
are, and this is where the work is. `Mathlib` computes a filtered colimit of modules elementwise
only for a diagram indexed by a category in the universe of the modules, while the statement leaves the
index type `J` in its own universe `w`; the two facts needed about `c` are therefore proved here
from the universal property alone:

* `Stacks.MittagLeffler.DirectedColimit.exists_legHom_rTensor_eq`: the legs of `c`, tensored with a
  module, are jointly
  surjective. The untensored statement comes from the observation that the quotient of `c.pt` by
  the supremum of the ranges of the legs receives the zero map and the projection, which the
  universal property forces to agree; the tensored one follows by induction on tensors, using
  directedness of `J` to put finitely many stages together.
* `Stacks.MittagLeffler.DirectedColimit.exists_map_rTensor_eq_zero`: an element of `M i ⊗[R] T`
  killed by `f i ⊗ id_T` is
  killed by `f i k ⊗ id_T` for some `k ≥ i`. An element of `M i ⊗[R] T` which is not killed by any
  transition map is nonzero in `Module.DirectLimit`, so some character of that direct limit does
  not vanish on it; the character, valued in the injective cogenerator `CharacterModule R`
  transported to the universe of the modules by `Small.{v} R`, curries into a cocone on `F` with
  point `T →ₗ[R] CharacterModule (Shrink R)`, and the map that the universal property of `c`
  produces out of `c.pt` uncurries to a map killing the element. This is the only use of
  `Small.{v} R`, and the reason the argument does not need `J` to be small: the cogenerator is a
  single module, not a colimit.

A leg `c.ι.app i` of a cocone has codomain `((Functor.const J).obj c.pt).obj i`, which is only
definitionally the underlying module of `c.pt`, so a family such as the ranges of the legs is not
even well typed as written; `Stacks.MittagLeffler.DirectedColimit.legHom` is the leg with its
codomain displayed as `↥c.pt`,
and it is an `abbrev` because there is nothing to say about it beyond that.

The naturality of `TensorProduct.piRightHom` in its module argument is not in `Mathlib` either; it
is `Stacks.MittagLeffler.DirectedColimit.piRightHom_comp_rTensor`, as in the proof of Lemma 059N.

## References

* [StacksProject 0AS7](https://stacks.math.columbia.edu/tag/0AS7)
-/



open CategoryTheory Limits
open scoped TensorProduct

@[expose] public section

namespace Stacks.MittagLeffler.DirectedColimit

section Legs

variable {R : Type u} [CommRing R] {J : Type w} [Preorder J] {F : J ⥤ ModuleCat.{v} R}

/-- The leg at `i` of a cocone on a diagram of `R`-modules, with its codomain the underlying
module of the cocone point rather than the value at `i` of a constant functor. -/
abbrev legHom (c : Cocone F) (i : J) : (F.obj i : Type v) →ₗ[R] (c.pt : Type v) :=
  (c.ι.app i).hom

/-- The legs of a cocone factor the earlier legs through the transition maps. -/
lemma legHom_comp_map (c : Cocone F) {i j : J} (u : i ⟶ j) :
    legHom c j ∘ₗ (F.map u).hom = legHom c i := by
  ext y
  exact congrArg (fun h : F.obj i ⟶ ((Functor.const J).obj c.pt).obj i ↦ h.hom y) (c.w u)

end Legs

section Helpers

variable {R : Type u} [CommRing R] {J : Type w} [Preorder J] [IsDirectedOrder J]
  {F : J ⥤ ModuleCat.{v} R} {c : Cocone F}

/-- The comparison map `M ⊗[R] (∀ α, Q α) → ∀ α, M ⊗[R] Q α` is natural in `M`. -/
private lemma piRightHom_comp_rTensor {M M' : Type v} [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] (f : M →ₗ[R] M') {A : Type v} (Q : A → Type v)
    [∀ α, AddCommGroup (Q α)] [∀ α, Module R (Q α)] :
    TensorProduct.piRightHom R R M' Q ∘ₗ LinearMap.rTensor (∀ α, Q α) f =
      (LinearMap.piMap fun α ↦ LinearMap.rTensor (Q α) f) ∘ₗ
        TensorProduct.piRightHom R R M Q := by
  ext x q
  simp

/-- The ranges of the legs of a cocone over a directed system are a directed family. -/
lemma directed_range_legHom :
    Directed (· ≤ ·) fun i : J ↦ LinearMap.range (legHom c i) := by
  refine Monotone.directed_le fun i k h ↦ ?_
  rw [← legHom_comp_map c (homOfLE h)]
  exact LinearMap.range_comp_le_range _ _

omit [IsDirectedOrder J] in
/-- The ranges of the legs of a colimit cocone cover its point. -/
lemma iSup_range_legHom_eq_top (hc : IsColimit c) :
    (⨆ i : J, LinearMap.range (legHom c i)) = ⊤ := by
  set N := ⨆ i : J, LinearMap.range (legHom c i)
  have key : ModuleCat.ofHom N.mkQ = (0 : c.pt ⟶ ModuleCat.of R (↥c.pt ⧸ N)) := by
    refine hc.hom_ext fun i ↦ ?_
    rw [comp_zero]
    ext y
    exact (Submodule.Quotient.mk_eq_zero N).2 (Submodule.mem_iSup_of_mem i ⟨y, rfl⟩)
  refine eq_top_iff.2 fun x _ ↦ ?_
  have hx : N.mkQ x = 0 := by
    have := congrArg (fun a : c.pt ⟶ ModuleCat.of R (↥c.pt ⧸ N) ↦ a.hom x) key
    simpa using this
  exact (Submodule.Quotient.mk_eq_zero N).1 hx

/-- The legs of a colimit cocone over a nonempty directed system are jointly surjective. -/
lemma exists_legHom_eq [Nonempty J] (hc : IsColimit c) (x : c.pt) :
    ∃ (i : J) (y : F.obj i), legHom c i y = x := by
  have hx : x ∈ ⨆ i : J, LinearMap.range (legHom c i) := by
    rw [iSup_range_legHom_eq_top hc]; exact Submodule.mem_top
  obtain ⟨i, y, hy⟩ := (Submodule.mem_iSup_of_directed _ directed_range_legHom).1 hx
  exact ⟨i, y, hy⟩

/-- The legs of a colimit cocone stay jointly surjective after tensoring with a module. -/
lemma exists_legHom_rTensor_eq [Nonempty J] (hc : IsColimit c) (T : Type v)
    [AddCommGroup T] [Module R T] (x : (↥c.pt) ⊗[R] T) :
    ∃ (i : J) (y : (F.obj i : Type v) ⊗[R] T), (legHom c i).rTensor T y = x := by
  induction x with
  | tmul m s =>
    obtain ⟨i, y, hy⟩ := exists_legHom_eq hc m
    exact ⟨i, y ⊗ₜ s, by simp [hy]⟩
  | add x₁ x₂ h₁ h₂ =>
    obtain ⟨i, y₁, hy₁⟩ := h₁
    obtain ⟨j, y₂, hy₂⟩ := h₂
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    refine ⟨k, (F.map (homOfLE hik)).hom.rTensor T y₁ +
      (F.map (homOfLE hjk)).hom.rTensor T y₂, ?_⟩
    rw [map_add, ← hy₁, ← hy₂, ← LinearMap.rTensor_comp_apply, ← LinearMap.rTensor_comp_apply,
      legHom_comp_map, legHom_comp_map]

/-- A character of a module induces an `R`-linear map into the character module of `R`, shrunk to
the universe of the modules of the diagram. -/
private noncomputable def charLift [Small.{v} R] {D : Type*} [AddCommGroup D] [Module R D]
    (lam : CharacterModule D) : D →ₗ[R] CharacterModule (Shrink.{v} R) :=
  CharacterModule.curry (CharacterModule.dual
    ((TensorProduct.rid R D).toLinearMap ∘ₗ
      LinearMap.lTensor D (Shrink.linearEquiv (R := R) (α := R)).toLinearMap) lam)

private lemma charLift_ne_zero [Small.{v} R] {D : Type*} [AddCommGroup D] [Module R D]
    {lam : CharacterModule D} {z : D} (hz : lam z ≠ 0) :
    (charLift lam : D →ₗ[R] CharacterModule (Shrink.{v} R)) z ≠ 0 := by
  intro h
  refine hz ?_
  have h2 : ∀ s : Shrink.{v} R,
      lam ((Shrink.linearEquiv (R := R) (α := R) s) • z) = 0 := by
    intro s
    have h1 : (charLift lam : D →ₗ[R] CharacterModule (Shrink.{v} R)) z s
        = lam ((TensorProduct.rid R D) (LinearMap.lTensor D
            (Shrink.linearEquiv (R := R) (α := R)).toLinearMap (z ⊗ₜ[R] s))) := rfl
    rw [h] at h1
    simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul] at h1
    exact h1.symm.trans rfl
  have h3 := h2 ((Shrink.linearEquiv (R := R) (α := R)).symm 1)
  rwa [LinearEquiv.apply_symm_apply, one_smul] at h3

/-- An element of `M i ⊗[R] T` killed by the leg of a colimit cocone is killed by some transition
map, tensored with `T`. -/
private lemma exists_map_rTensor_eq_zero [Small.{v} R] (hc : IsColimit c) (T : Type v)
    [AddCommGroup T] [Module R T] (i : J) (x : (F.obj i : Type v) ⊗[R] T)
    (hx : (legHom c i).rTensor T x = 0) :
    ∃ (k : J) (u : i ⟶ k), (F.map u).hom.rTensor T x = 0 := by
  classical
  by_contra hcon
  have hcon' : ∀ (k : J) (u : i ⟶ k), (F.map u).hom.rTensor T x ≠ 0 := by
    intro k u h
    exact hcon ⟨k, u, h⟩
  set G : J → Type v := fun j ↦ (F.obj j : Type v) ⊗[R] T
  set g : ∀ a b : J, a ≤ b → G a →ₗ[R] G b :=
    fun a b h ↦ LinearMap.rTensor T (F.map (homOfLE h)).hom with hg
  have hds : DirectedSystem G fun a b h ↦ g a b h := by
    refine ⟨fun a z ↦ ?_, fun a b d hab hbd z ↦ ?_⟩
    · simp only [hg]
      have : (F.map (homOfLE (le_refl a))).hom = LinearMap.id := by
        rw [show homOfLE (le_refl a) = 𝟙 a from rfl, F.map_id]
        rfl
      rw [this]
      simp
    · simp only [hg]
      rw [← LinearMap.rTensor_comp_apply, ← ModuleCat.hom_comp, ← F.map_comp]
      congr 2
  have hne : Module.DirectLimit.of R J G g i x ≠ 0 := by
    intro h0
    obtain ⟨k, hik, hk⟩ := Module.DirectLimit.of.zero_exact h0
    exact hcon' k (homOfLE hik) hk
  obtain ⟨lam, hlam⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hne
  set E := CharacterModule (Shrink.{v} R)
  set Ψ : Module.DirectLimit G g →ₗ[R] E := charLift lam
  set appMap : ∀ j : J, F.obj j ⟶ ModuleCat.of R (T →ₗ[R] E) := fun j ↦ ModuleCat.ofHom
    (TensorProduct.curry (Ψ ∘ₗ Module.DirectLimit.of R J G g j))
  have happ_apply : ∀ (j : J) (y : F.obj j) (s : T),
      (appMap j).hom y s = Ψ (Module.DirectLimit.of R J G g j (y ⊗ₜ[R] s)) := by
    intro j y s
    simp [appMap, TensorProduct.curry_apply]
  have hnat : ∀ (a b : J) (u : a ⟶ b), F.map u ≫ appMap b = appMap a := by
    intro a b u
    refine ModuleCat.hom_ext (LinearMap.ext fun y ↦ LinearMap.ext fun s ↦ ?_)
    have hl : ((F.map u ≫ appMap b).hom y) s = Ψ (Module.DirectLimit.of R J G g b
        ((F.map u).hom y ⊗ₜ[R] s)) := by
      rw [ModuleCat.hom_comp, LinearMap.comp_apply, happ_apply]
    rw [hl, happ_apply]
    refine congrArg Ψ ?_
    have hgt : g a b (leOfHom u) (y ⊗ₜ[R] s) = (F.map u).hom y ⊗ₜ[R] s := by
      have h1 : homOfLE (leOfHom u) = u := rfl
      have h0 : g a b (leOfHom u) (y ⊗ₜ[R] s) =
          LinearMap.rTensor T (F.map (homOfLE (leOfHom u))).hom (y ⊗ₜ[R] s) := rfl
      rw [h0, h1, LinearMap.rTensor_tmul]
    rw [← hgt, Module.DirectLimit.of_f]
  set t : Cocone F :=
    { pt := ModuleCat.of R (T →ₗ[R] E)
      ι := { app := appMap, naturality := fun a b u ↦ by simpa using hnat a b u } }
  have hfac : ∀ (j : J) (y : F.obj j) (s : T),
      Ψ (Module.DirectLimit.of R J G g j (y ⊗ₜ[R] s)) =
        (hc.desc t).hom (legHom c j y) s := by
    intro j y s
    have h1 : c.ι.app j ≫ hc.desc t = appMap j := hc.fac t j
    have h2 := congrArg (fun a : F.obj j ⟶ t.pt ↦ (a.hom y : T →ₗ[R] E) s) h1
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
    rw [← happ_apply, ← h2]
  have key : ∀ (j : J) (z : (F.obj j : Type v) ⊗[R] T),
      Ψ (Module.DirectLimit.of R J G g j z) =
        TensorProduct.lift (hc.desc t).hom ((legHom c j).rTensor T z) := by
    intro j z
    induction z with
    | tmul y s => simpa using hfac j y s
    | add z₁ z₂ h₁ h₂ => simp [map_add, h₁, h₂]
  have hzero := key i x
  rw [hx, map_zero] at hzero
  exact charLift_ne_zero hlam hzero

/-- The legs of a colimit cocone over a directed system with universally injective transition maps
are universally injective. -/
private lemma legHom_rTensor_injective [Small.{v} R]
    (hinj : ∀ ⦃i j : J⦄ (u : i ⟶ j) (T : Type v) [AddCommGroup T] [Module R T],
      Function.Injective ((F.map u).hom.rTensor T))
    (hc : IsColimit c) (T : Type v) [AddCommGroup T] [Module R T] (i : J) :
    Function.Injective ((legHom c i).rTensor T) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨k, u, hk⟩ := exists_map_rTensor_eq_zero hc T i x hx
  exact hinj u T (by rw [hk, map_zero])

end Helpers

end Stacks.MittagLeffler.DirectedColimit

end

/-!
# Mittag-Leffler passes to a colimit of a universally injective directed system

Let `R` be a commutative ring. An `R`-module `M` is *Mittag-Leffler* when every map `f : P → M`
from a finitely presented module dominates and is dominated by a map `g : P → Q` into a finitely
presented module, that is `Ker(f ⊗ id_N) = Ker(g ⊗ id_N)` for every `R`-module `N`; this is
condition (1) of Proposition 059E, the one of the five conditions there that mentions `M` alone,
and it is Definition 059F. A map is *universally injective* when it stays injective after tensoring
with an arbitrary module (Definition 058I).

This file states that the Mittag-Leffler property passes to a filtered colimit whose transition
maps are universally injective: if `M = colim M i` for a directed system `(M i, f i j)` of
Mittag-Leffler modules with every `f i j` universally injective, then `M` is Mittag-Leffler. By
Proposition 059M it is enough to see that `M ⊗ (∏ Q α) → ∏ (M ⊗ Q α)` is injective for every
family `(Q α)`, and, tensoring commuting with filtered colimits, that map is the composite

```
M ⊗ (∏ Q α) = colim (M i ⊗ (∏ Q α)) → colim (∏ (M i ⊗ Q α)) → ∏ (M ⊗ Q α).
```

The first arrow is a filtered colimit of the maps `M i ⊗ (∏ Q α) → ∏ (M i ⊗ Q α)`, each injective
by 059M again, hence injective. The second is a filtered colimit of the maps
`∏ (M i ⊗ Q α) → ∏ (M ⊗ Q α)`, injective because each `M i ⊗ Q α → M ⊗ Q α` is: the canonical map
`M i → M` is a filtered colimit of the universally injective transition maps, so is itself
universally injective.

## Main results

* `ModuleCat.mittagLeffler_pt_of_forall_mittagLeffler_of_forall_rTensor_injective`: the colimit of
  a directed system of Mittag-Leffler `R`-modules with universally injective transition maps is
  Mittag-Leffler.

## Implementation notes

Departures from the source's form, none of them weakening it.

*The Mittag-Leffler property is spelled out.* Neither `Mathlib` nor this project has a predicate
for a Mittag-Leffler module: `CategoryTheory.Functor.IsMittagLeffler` is the condition on an
inverse system, that is condition (4) of 059E for the dual systems, and does not apply to a module
on its own. So the property is written inline in the intrinsic form 059E (1), the spelling of
Propositions 059M and 05CQ and of Lemmas 059N and 0AS6, once for the members and once for the
colimit.

*The directed system is a functor with a colimit cocone.* "`M = colim M i`" is a functor
`F : J ⥤ ModuleCat R` on a nonempty directed preorder `J` together with an arbitrary cocone `c`
and `IsColimit c`, as in 059E and 059W, rather than a chosen construction such as
`Module.DirectLimit`: `M` is `c.pt`, the transition map `f i j` is `F.map u` for `u : i ⟶ j`, and
the canonical map `M i → M` is the leg `c.ι.app i`. A user with a colimit in hand therefore needs
no transport along an isomorphism, and the canonical maps of the source are pinned rather than
existentially quantified. The Mittag-Leffler conditions are stated for the underlying modules
`↥(F.obj i)` and `↥c.pt` in the plain-module form of 059M and 059N, since that is the form in
which the two tags used here and the dependent Lemma 059P speak.

*The members are arbitrary.* Unlike 059E, no finite presentation of the `M i` is assumed; the
source assumes none, and the route through 059M uses none.

*Universal injectivity is stated for the transition maps, not the canonical maps.* Under
`IsColimit c` the two hypotheses are equivalent, and the transition-map form is the weaker one:
`c.ι.app i = F.map u ≫ c.ι.app j` makes universal injectivity of the legs imply that of the
transition maps at once, whereas the converse is the filtered-colimit argument of the proof. So the
source's hypothesis is kept, and the statement is the stronger of the two.

*Universes.* The members of the system, the test module `T` of universal injectivity and the
modules `P`, `Q`, `N` of the Mittag-Leffler condition all live in `Type v`, with `R : Type u`
assumed `Small.{v}`, the convention of 059E, 059M, 059N and 05CQ; the index `J` is left in its own
universe `w`, as in 059W, nothing here needing it small. `Small.{v} R` is not a weakening: it is
automatic when `v = max u v`, in particular whenever `R` and the modules share a universe, so the
single-universe form is the instance `v := max u v`. It is also what makes the `Type v` quantifiers
the source's quantifiers over all modules — domination may be tested on the finitely presented
modules of `Type v` alone (Lemma 059C) — and it is carried by Proposition 059M, through which the
proof passes.

Faithfulness. (1) No hypothesis is dead: `hML` is used for each `i`, and it cannot be dropped, as
the one-point system constant at `ℚ` over `ℤ` shows — its transition maps are identities, hence
universally injective, and `ℚ` is not Mittag-Leffler (Example 059I); `hinj` is used for every
transition map, and it cannot be dropped either, `ℚ` being the colimit of the directed system of
its cyclic subgroups `ℤ · (1 / n !)`, whose members are finitely presented, hence Mittag-Leffler,
and whose transition maps are multiplication by `n + 1`, killed by `· ⊗ ℤ ⧸ (n + 1) ℤ`;
directedness of `J` is what makes `J` filtered, hence what makes tensoring commute with the
colimit, and `Nonempty J` is the source's convention for a directed set; `hc` is what identifies
the module of the conclusion as the colimit; and `Small.{v} R` is used as described above.
(2) The scalars and the base are the source's: one commutative ring `R` throughout, `F` takes
values in `R`-modules, all tensor products are `⊗[R]`, all maps are `R`-linear and finite
presentation is over `R`; nothing is localized or base changed. (3) The maps the source names are
pinned, not merely asserted to exist: the cocone `c` is part of the data, so the colimit and its
canonical maps are the source's; `f i j ⊗ id_T` is `(F.map u).hom.rTensor T`, built from the
transition map itself; and the maps whose kernels are compared in the Mittag-Leffler condition are
`f.rTensor N` and `g.rTensor N`. Only the finitely presented module `Q` and the map `g` are
existentially quantified, as they are in 059E (1). (4) The instantiation is not degenerate: take
`R = ℤ`, `J` the finite subsets of `ℕ`, `F` the system of the free modules `ℤ^i` with the
inclusions as transition maps and `c` the colimit cocone with `c.pt = ⨁_{n ∈ ℕ} ℤ`. Every
hypothesis holds — the inclusions are split, hence universally injective (058J (1)), and each `ℤ^i`
is finitely presented, hence Mittag-Leffler with `Q = ℤ^i` and `g = f` — and the conclusion has
content, `c.pt` being neither finitely presented nor a member of the system, so that the witness
`Q = c.pt` is not available for it.

## References

* [StacksProject 0AS7](https://stacks.math.columbia.edu/tag/0AS7)
-/



open CategoryTheory Limits

@[expose] public section

/-- **Stacks 0AS7.** Let `R` be a commutative ring, let `F : J ⥤ ModuleCat R` be a directed system
`(M i, f i j)` of `R`-modules over a nonempty directed preorder `J`, and let `c` be a colimit
cocone on `F`, so that `M = c.pt` is `colim_{i ∈ J} M i`. Assume every transition map is
universally injective, that is `f i j ⊗ id_T` is injective for every `R`-module `T`, and that every
`M i` is Mittag-Leffler. Then `M` is Mittag-Leffler. Being Mittag-Leffler is spelled out in the
intrinsic form 059E (1): every map `f : P → M` from a finitely presented module dominates and is
dominated by a map `g : P → Q` into a finitely presented module, domination meaning
`Ker(f ⊗ id_N) = Ker(g ⊗ id_N)` for every `R`-module `N`. -/
@[stacks 0AS7 "Mittag-Leffler is spelled out inline as condition (1) of 059E, as in 059M and 059N;
the directed system is a functor with a colimit cocone, as in 059E and 059W; universal injectivity
of `f i j` is injectivity of `(F.map u).hom.rTensor T` for every `T`, as in 058K (1). See the
module docstring."]
public theorem ModuleCat.mittagLeffler_pt_of_forall_mittagLeffler_of_forall_rTensor_injective
    {R : Type u} [CommRing R] [Small.{v} R] {J : Type w} [Preorder J] [IsDirectedOrder J]
    [Nonempty J] {F : J ⥤ ModuleCat.{v} R}
    (hinj : ∀ ⦃i j : J⦄ (u : i ⟶ j) (T : Type v) [AddCommGroup T] [Module R T],
      Function.Injective ((F.map u).hom.rTensor T))
    (hML : ∀ i : J, ∀ (P : Type v) [AddCommGroup P] [Module R P]
        [Module.FinitePresentation R P] (f : P →ₗ[R] F.obj i),
      ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q) (_ : Module.FinitePresentation R Q)
        (g : P →ₗ[R] Q), ∀ (N : Type v) [AddCommGroup N] [Module R N],
          LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N))
    {c : Cocone F} (hc : IsColimit c) :
    ∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
        (f : P →ₗ[R] c.pt),
      ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q) (_ : Module.FinitePresentation R Q)
        (g : P →ₗ[R] Q), ∀ (N : Type v) [AddCommGroup N] [Module R N],
          LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N) := by
  rw [Module.mittagLeffler_iff_piRightHom_injective R (↥c.pt)]
  intro A Q _ _
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨i, y, hy⟩ :=
    Stacks.MittagLeffler.DirectedColimit.exists_legHom_rTensor_eq hc (∀ α, Q α) x
  have hcomp : ∀ α, (Stacks.MittagLeffler.DirectedColimit.legHom c i).rTensor (Q α)
      (TensorProduct.piRightHom R R (F.obj i) Q y α) = 0 := by
    intro α
    have h4 := congrFun
      (LinearMap.congr_fun (Stacks.MittagLeffler.DirectedColimit.piRightHom_comp_rTensor
        (Stacks.MittagLeffler.DirectedColimit.legHom c i) Q) y) α
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_piMap,
      Pi.map_apply] at h4
    rw [← h4, hy]
    simp only [hx, Pi.zero_apply]
  have hy0 : TensorProduct.piRightHom R R (F.obj i) Q y = 0 := by
    funext α
    exact Stacks.MittagLeffler.DirectedColimit.legHom_rTensor_injective hinj hc (Q α) i
      (by rw [hcomp α]; exact (map_zero _).symm)
  have hinj' := (Module.mittagLeffler_iff_piRightHom_injective R (F.obj i)).mp (hML i) A Q
  have hy00 : y = 0 := hinj' (by rw [hy0, map_zero])
  rw [← hy, hy00, map_zero]

namespace Stacks.MittagLeffler.DirectedColimit

public alias solution :=
    ModuleCat.mittagLeffler_pt_of_forall_mittagLeffler_of_forall_rTensor_injective

end Stacks.MittagLeffler.DirectedColimit

end
