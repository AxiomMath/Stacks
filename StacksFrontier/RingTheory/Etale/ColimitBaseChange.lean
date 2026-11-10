module

import StacksFrontier.RingTheory.SpreadingOut.Smooth
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Presentation

/-!
# Étale ring maps spread out in a filtered colimit of base rings

Let `R` be a commutative ring, let `A` be a filtered colimit of `R`-algebras `Aᵢ` (computed on
underlying sets), and let `φ : B →ₐ[R] C` be a map of `R`-algebras of finite presentation. This
file proves Stacks 07RI: if the base change `1 ⊗ φ : A ⊗[R] B → A ⊗[R] C` is étale, then already
`1 ⊗ φ : Aᵢ ⊗[R] B → Aᵢ ⊗[R] C` is étale for some `i`.

Étale is smooth together with formal unramifiedness, so the statement splits into the smooth half,
which is Stacks 0C0B (`RingHom.Smooth.exists_baseChange_smooth_of_colimitPresentation`, the same
statement with `Etale` replaced by `Smooth`), and the unramified half, which is Stacks 0C4F. In
terms of a presentation `C = B[x_1, …, x_n]/(f_1, …, f_m)`, étaleness of `A ⊗[R] B → A ⊗[R] C`
says that `d : (f_1, …, f_m)/(f_1, …, f_m)^2 → ⨁_k (A ⊗[R] C) dx_k` is an isomorphism, smoothness
that it is a split injection, and unramifiedness that it is surjective, which is the vanishing of
`Ω`.

The unramified half is proved as `Ω` is: writing `Bₛ = S ⊗[R] B` and `Cₛ = S ⊗[R] C` for an
`R`-algebra `S`, the square `B → C`, `B → Bₛ`, `C → Cₛ`, `Bₛ → Cₛ` is a pushout, so
`Ω[Cₛ⁄Bₛ] ≅ Bₛ ⊗[B] Ω[C⁄B] ≅ S ⊗[R] Ω[C⁄B]`
(`formallyUnramified_tensorProduct_map_iff`). Thus `1 ⊗ φ` is formally unramified after base
change along `R → S` exactly when every element of `Ω[C⁄B]` dies in `S ⊗[R] Ω[C⁄B]`. Finite
presentation of `φ` makes `Ω[C⁄B]` a finite `C`-module, `A ⊗[R] Ω[C⁄B]` is the filtered colimit
of the `Aᵢ ⊗[R] Ω[C⁄B]`, and so finitely many generators of `Ω[C⁄B]` already die at one stage
`k`; that condition then persists along every map out of `k`.

Since 0C0B produces *some* stage, and the vanishing above holds at `k` and at every stage after
it, the two halves are combined by applying 0C0B to the diagram restricted to the stages after
`k`: the index category `Under k` is filtered and `Under.forget k` is final, so the restricted
diagram has the same colimit, computed on underlying sets again
(`exists_baseChange_smooth_under`).

## Main results

* `Stacks.Etale.ColimitSpreadOut.solution`: the statement of Stacks 07RI.
* `RingHom.Etale.exists_baseChange_etale_of_colimitPresentation`: the same statement, in the
  `RingHom.Etale` namespace.

## Implementation notes

The pushout square `isPushout_tensorProduct` is stated with the `Algebra (S ⊗[R] B) (S ⊗[R] C)`
instance as a hypothesis, together with the equation identifying its `algebraMap` with `1 ⊗ φ`,
rather than fixing that instance: the caller installs it from `φ` by `RingHom.toAlgebra`, and
`Algebra.IsPushout` needs the instance in the ambient context before the square can be stated.

The unramified half is stated for a tower `[Algebra B C] [IsScalarTower R B C]` rather than for
an `AlgHom`, so that `Ω[C⁄B]` and the base changed algebra structures are found by instance
synthesis; `solution` installs the tower from `φ` and rewrites `φ` as `IsScalarTower.toAlgHom`.

The base ring is `R`, playing the role of the source's `A_0`. The source's index set `I` contains
`0`, its terms `A_i` for `i ≥ 0` are `A_0`-algebras, and the conclusion is about some `i ≥ 0`;
since `{i ∈ I | i ≥ 0}` is cofinal in `I` it computes the same colimit, so the source's situation
is this one with `R = A_0` and the diagram indexed by that cofinal subset. Nothing forces `R`
itself to be a term of the diagram, and the argument does not use that it is, so the hypothesis
is the weaker one.

The diagram of the `Aᵢ` and the cocone exhibiting `A` are the bundled
`Limits.ColimitPresentation J A` in `CommAlgCat R`, the category of commutative `R`-algebras: a
diagram `J ⥤ CommAlgCat R`, a cocone with tip `A`, and the assertion that the cocone is
colimiting. No construction of the colimit is chosen, and `CommAlgCat R` is used rather than
`Under (CommRingCat.of R)` so that each `↥(pres.diag.obj i)` carries its `Algebra R` instance and
the tensor products below typecheck as written. The index is an arbitrary filtered category rather
than the source's nonempty directed partial order: that is the weaker hypothesis, since a nonempty
directed preorder is filtered.

A colimit presentation is by itself *weaker* than the source's `A = colim A_i`, and this is what
the extra instance argument repairs. The objects of `CommAlgCat.{v} R` are algebras in `Type v`,
so for a diagram indexed by a category which is not `v`-small a colimiting cocone there need not
stay colimiting after passing to underlying sets: the set-theoretic colimit of the `Aᵢ` need not
be `v`-small, and where it is not, no cocone with tip in `CommAlgCat.{v} R` computes it while a
colimiting cocone in `CommAlgCat.{v} R` may still exist. For such a presentation `A` bears no
relation to the `Aᵢ` beyond receiving compatible maps from them, and the conclusion fails. The
hypothesis `[PreservesColimit (pres.diag ⋙ forget₂ (CommAlgCat R) CommRingCat)
(forget CommRingCat)]` supplies the missing content: `J` is filtered, hence connected, so the
cocone of underlying *rings* is again colimiting — the `R`-algebra structure on the tip of a
cocone of rings is forced by connectedness — and the instance then says that the cocone of
underlying *sets* is colimiting too, which is how the source reads `A = colim A_i`. This is
Mathlib's own formulation of that hypothesis, in
`RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit` and
`CommRingCat.preservesColimit_coyoneda_of_finitePresentation`, the spreading-out lemmas for
finitely presented algebras which this one is proved from. When `J` is `v`-small — `J : Type v`
with `Category.{v} J`, the shape of the source's directed set — the instance is found by instance
synthesis, so the aligned-universe statement is the special case `w = t = v` and costs its callers
nothing.

The base change of `φ` along `R → Aᵢ` is the concrete `Algebra.TensorProduct.map (AlgHom.id R _)
φ`, that is `1 ⊗ φ`, which is the map the source writes, and is how Mathlib spells the base
change of an algebra map (`CommAlgCat.FiniteEtale.baseChange`,
`CommRingCat.tensorProd_map_right`). Those write the identity as an `↥Aᵢ`-algebra map, so that
the base change is one of `↥Aᵢ`-algebras; here it is written as an `R`-algebra map, the
underlying ring map — all that `RingHom.Etale` sees — being the same. An abstract base change,
given by `Algebra.IsPushout R B (Aᵢ) Bᵢ` and `Algebra.IsPushout R C (Aᵢ) Cᵢ`, is carried to this
one by the canonical isomorphisms, along which étaleness transports; asking for such data for
every `i` would only add the transport to every application.

`φ` is an `AlgHom`, not a tower `[Algebra B C] [IsScalarTower R B C]`, because the two properties
in play are properties of a map with no algebra instance attached: they are `RingHom.Etale` and
`RingHom.FinitePresentation` of the base changes and of `φ` itself.

The conclusion is the source's existential. Its cofinal strengthening, `∀ i, ∃ j ≥ i`, follows in
one step from `RingHom.Etale.isStableUnderBaseChange`, since `A_j ⊗_R C` is the base change of
`A_i ⊗_R C` along `A_i ⊗_R B → A_j ⊗_R B`, so it is a corollary rather than a separate statement.

Faithfulness. (1) Every hypothesis is used: `hφ` fails and the conclusion with it for
`R = B = ℤ`, `C = ℚ` and `A = ℚ = colim ℤ[1/n!]`, where every `ℤ[1/n!] → ℚ` is flat and
unramified but not of finite presentation while `ℚ → ℚ` is étale; `hA` fails together with the
conclusion for `C = B[x]`; `IsFiltered J` supplies the nonemptiness that `0 ∈ I` supplies in the
source, without which no `i` exists; and the `PreservesColimit` instance is what makes `A` the
colimit of the `Aᵢ` rather than merely the tip of a colimiting cocone in a category of `v`-small
algebras. (2) The scalars and base are the source's: the tensor products are over `R = A_0`, and
étaleness is asserted of `Aᵢ ⊗_R B → Aᵢ ⊗_R C`, a map of `Aᵢ ⊗_R B`-algebras, not of `R`- or
`Aᵢ`-algebras. (3) The canonical maps are pinned: the base change is the named map `1 ⊗ φ` rather
than an unspecified map `Aᵢ ⊗_R B → Aᵢ ⊗_R C`, and the comparison maps `Aᵢ → A` are the components
of the cocone carried by `pres`, which `pres.isColimit` exhibits as colimiting. (4) The
instantiation is not degenerate: with `R = ℤ`, `J = ℕ`, `Aᵢ = ℤ[1/i!]`, `A = ℚ`, `B = ℤ` and
`C = ℤ[x]/(x(x - 2))` the hypotheses hold — `J` is `v`-small, so the instance is automatic — and
the conclusion holds exactly for those `i` with `2` invertible in `ℤ[1/i!]`, that is for `i ≥ 2`,
so the index produced is genuinely constrained.

## References

* [StacksProject 07RI](https://stacks.math.columbia.edu/tag/07RI)
* [StacksProject 0C4F](https://stacks.math.columbia.edu/tag/0C4F)
* [StacksProject 0C0B](https://stacks.math.columbia.edu/tag/0C0B)

## Tags

étale, filtered colimit, base change, finite presentation, spreading out
-/

@[expose] public section

universe u v w t

open CategoryTheory Limits TensorProduct



namespace Stacks.Etale.ColimitSpreadOut

open Stacks.SpreadingOut.Smoothness

variable {R : Type u} [CommRing R]


section Diagram

variable {J : Type w} [Category.{t} J] {A : CommAlgCat.{v} R} (pres : ColimitPresentation J A)

end Diagram

section Descent

variable {J : Type w} [Category.{t} J] [IsFiltered J] {A : CommAlgCat.{v} R}
  (pres : ColimitPresentation J A)
  [PreservesColimit (pres.diag ⋙ forget₂ (CommAlgCat.{v} R) CommRingCat.{v})
    (forget CommRingCat)]

end Descent

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section BaseChange

variable {B C : Type*} [CommRing B] [CommRing C] [Algebra R B] [Algebra R C] [Algebra B C]
  [IsScalarTower R B C] (S : Type*) [CommRing S] [Algebra R S]

/-- A module `N` over `R` has `S ⊗[R] N = 0` as soon as `1 ⊗ x = 0` for every `x : N`. -/
private lemma subsingleton_tensor_of_forall {N : Type*} [AddCommGroup N] [Module R N]
    (h : ∀ x : N, (1 : S) ⊗ₜ[R] x = 0) : Subsingleton (S ⊗[R] N) := by
  refine subsingleton_of_forall_eq 0 fun z => ?_
  induction z using TensorProduct.inductionOn with
  | tmul s x =>
      simpa using congrArg (LinearMap.rTensor N (LinearMap.mulLeft R s)) (h x)
  | add a b ha hb => rw [ha, hb, add_zero]

variable [Algebra (S ⊗[R] B) (S ⊗[R] C)] [Algebra B (S ⊗[R] C)]
  [IsScalarTower B C (S ⊗[R] C)] [IsScalarTower B (S ⊗[R] B) (S ⊗[R] C)]

/-- Base change along `R → S` of an algebra map is a pushout square: for `Bₛ = S ⊗[R] B` and
`Cₛ = S ⊗[R] C` the square `B → C`, `B → Bₛ`, `C → Cₛ`, `1 ⊗ φ` is a pushout of rings.

The canonical square `B → C`, `B → Bₛ`, `C → Bₛ ⊗[B] C` is a pushout, and
`Algebra.IsPushout.cancelBaseChangeAlg R S B Bₛ C : Bₛ ⊗[B] C ≃ₐ[S] Cₛ` is a ring isomorphism
over both `Bₛ` and `C`, so `Algebra.IsPushout.of_equiv` transports the square along it. -/
lemma isPushout_tensorProduct
    (hmap : algebraMap (S ⊗[R] B) (S ⊗[R] C) =
      (Algebra.TensorProduct.map (AlgHom.id R S) (IsScalarTower.toAlgHom R B C)).toRingHom) :
    Algebra.IsPushout B (S ⊗[R] B) C (S ⊗[R] C) := by
  refine Algebra.IsPushout.of_equiv (R := B) (R' := S ⊗[R] B) (S := C)
    (AlgEquiv.ofRingEquiv
      (f := (Algebra.IsPushout.cancelBaseChangeAlg R S B (S ⊗[R] B) C).toRingEquiv) ?_) ?_
  · intro x
    apply (Algebra.IsPushout.cancelBaseChangeAlg R S B (S ⊗[R] B) C).symm.injective
    simp only [AlgEquiv.coe_toRingEquiv, AlgEquiv.symm_apply_apply, hmap]
    induction x using TensorProduct.inductionOn with
    | tmul s b =>
        have hstep : (Algebra.TensorProduct.map (AlgHom.id R S)
            (IsScalarTower.toAlgHom R B C)).toRingHom (s ⊗ₜ[R] b) =
            s ⊗ₜ[R] algebraMap B C b := rfl
        rw [hstep, Algebra.IsPushout.cancelBaseChangeAlg_symm_tmul,
          Algebra.algebraMap_eq_smul_one (R := B) (A := C) b, ← TensorProduct.smul_tmul]
        change (s ⊗ₜ[R] b) ⊗ₜ[B] (1 : C) = _
        congr 1
        simp [Algebra.smul_def, Algebra.TensorProduct.right_algebraMap_apply,
          Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  · ext c
    change (Algebra.IsPushout.cancelBaseChangeAlg R S B (S ⊗[R] B) C)
        (algebraMap C ((S ⊗[R] B) ⊗[B] C) c) = algebraMap C (S ⊗[R] C) c
    apply (Algebra.IsPushout.cancelBaseChangeAlg R S B (S ⊗[R] B) C).symm.injective
    rw [AlgEquiv.symm_apply_apply]
    change _ = (Algebra.IsPushout.cancelBaseChangeAlg R S B (S ⊗[R] B) C).symm ((1 : S) ⊗ₜ[R] c)
    rw [Algebra.IsPushout.cancelBaseChangeAlg_symm_tmul, map_one,
      Algebra.TensorProduct.right_algebraMap_apply, Algebra.TensorProduct.one_def]

/-- The Kähler differentials of a base change: `Ω[Cₛ⁄Bₛ]` vanishes exactly when every element of
`Ω[C⁄B]` dies in `S ⊗[R] Ω[C⁄B]`. -/
private lemma subsingleton_kaehlerDifferential_iff
    [Algebra.IsPushout B (S ⊗[R] B) C (S ⊗[R] C)] :
    Subsingleton Ω[(S ⊗[R] C)⁄(S ⊗[R] B)] ↔ ∀ x : Ω[C⁄B], (1 : S) ⊗ₜ[R] x = 0 := by
  have E : S ⊗[R] Ω[C⁄B] ≃ Ω[(S ⊗[R] C)⁄(S ⊗[R] B)] :=
    (Algebra.IsPushout.cancelBaseChange R S B (S ⊗[R] B) Ω[C⁄B]).toEquiv.symm.trans
      (KaehlerDifferential.tensorKaehlerEquivBase B (S ⊗[R] B) C (S ⊗[R] C)).toEquiv
  refine ⟨fun h x => ?_, fun h => E.subsingleton_congr.mp (subsingleton_tensor_of_forall S h)⟩
  have : Subsingleton (S ⊗[R] Ω[C⁄B]) := E.subsingleton_congr.mpr h
  exact Subsingleton.elim _ _

end BaseChange

/-- Formal unramifiedness of the base change of `φ : B →ₐ[R] C` along `R → S` says exactly that
every element of `Ω[C⁄B]` dies in `S ⊗[R] Ω[C⁄B]`. -/
private lemma formallyUnramified_baseChange_iff {B C : Type*} [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] [Algebra B C] [IsScalarTower R B C]
    (S : Type*) [CommRing S] [Algebra R S] :
    (Algebra.TensorProduct.map (AlgHom.id R S)
        (IsScalarTower.toAlgHom R B C)).toRingHom.FormallyUnramified ↔
      ∀ x : Ω[C⁄B], (1 : S) ⊗ₜ[R] x = 0 := by
  let : Algebra (S ⊗[R] B) (S ⊗[R] C) :=
    (Algebra.TensorProduct.map (AlgHom.id R S) (IsScalarTower.toAlgHom R B C)).toRingHom.toAlgebra
  let : Algebra B (S ⊗[R] C) := ((algebraMap C (S ⊗[R] C)).comp (algebraMap B C)).toAlgebra
  have : IsScalarTower B C (S ⊗[R] C) :=
    IsScalarTower.of_algebraMap_eq fun b => by rw [RingHom.algebraMap_toAlgebra]; rfl
  have : IsScalarTower B (S ⊗[R] B) (S ⊗[R] C) :=
    IsScalarTower.of_algebraMap_eq fun b => by
      simp [RingHom.algebraMap_toAlgebra]
  have := isPushout_tensorProduct (R := R) (B := B) (C := C) S
    (by rw [RingHom.algebraMap_toAlgebra])
  rw [show (Algebra.TensorProduct.map (AlgHom.id R S)
      (IsScalarTower.toAlgHom R B C)).toRingHom.FormallyUnramified ↔
      Subsingleton Ω[(S ⊗[R] C)⁄(S ⊗[R] B)] from ⟨fun h => h.1, fun h => ⟨h⟩⟩]
  exact subsingleton_kaehlerDifferential_iff S

section Spread

variable {J : Type w} [Category.{t} J] [IsFiltered J] {A : CommAlgCat.{v} R}
  (pres : ColimitPresentation J A)
  [PreservesColimit (pres.diag ⋙ forget₂ (CommAlgCat.{v} R) CommRingCat.{v})
    (forget CommRingCat)]

omit [IsFiltered J]
  [PreservesColimit (pres.diag ⋙ forget₂ (CommAlgCat.{v} R) CommRingCat.{v})
    (forget CommRingCat)] in
/-- Vanishing of `1 ⊗ x` at a stage of the diagram persists at every later stage. -/
private lemma tmul_eq_zero_of_map {M : Type*} [AddCommGroup M] [Module R M] {k l : J} (f : k ⟶ l)
    (x : M) (h : (1 : ↥(pres.diag.obj k)) ⊗ₜ[R] x = 0) :
    (1 : ↥(pres.diag.obj l)) ⊗ₜ[R] x = 0 := by
  simpa using congrArg (LinearMap.rTensor M (pres.diag.map f).hom.toLinearMap) h

/-- If `M` is a finite `C`-module and every `1 ⊗ x` dies in `A ⊗[R] M`, then already every
`1 ⊗ x` dies in `Aₖ ⊗[R] M` at some stage `k` of the diagram. -/
private lemma exists_forall_tmul_eq_zero {C M : Type*} [CommRing C] [Algebra R C]
    [AddCommGroup M] [Module C M] [Module R M] [IsScalarTower R C M] [Module.Finite C M]
    (hA : ∀ x : M, (1 : ↥A) ⊗ₜ[R] x = 0) :
    ∃ k : J, ∀ x : M, (1 : ↥(pres.diag.obj k)) ⊗ₜ[R] x = 0 := by
  classical
  obtain ⟨s, hs⟩ : (⊤ : Submodule C M).FG := Module.finite_def.mp inferInstance
  obtain ⟨i₀⟩ : Nonempty J := IsFiltered.nonempty
  have key : ∀ m : M, ∃ (k : J) (_ : i₀ ⟶ k), (1 : ↥(pres.diag.obj k)) ⊗ₜ[R] m = 0 := by
    intro m
    obtain ⟨k, f, hk⟩ := exists_map_rTensor_eq_zero pres M
      ((1 : ↥(pres.diag.obj i₀)) ⊗ₜ[R] m) (by simpa using hA m)
    exact ⟨k, f, by simpa using hk⟩
  choose g hg hg' using key
  obtain ⟨l, hl⟩ := IsFiltered.sup_objs_exists (s.image g)
  refine ⟨l, fun x => ?_⟩
  have hsub : ∀ m ∈ s, (1 : ↥(pres.diag.obj l)) ⊗ₜ[R] m = 0 := by
    intro m hm
    obtain ⟨f⟩ := hl (Finset.mem_image_of_mem g hm)
    exact tmul_eq_zero_of_map pres f m (hg' m)
  have hx : x ∈ Submodule.span C (s : Set M) := hs ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem m hm => exact hsub m hm
  | zero => simp
  | add a b _ _ ha hb => rw [TensorProduct.tmul_add, ha, hb, add_zero]
  | smul c a _ ha =>
      simpa using congrArg (LinearMap.lTensor ↥(pres.diag.obj l)
        ((LinearMap.lsmul C M c).restrictScalars R)) ha

/-- Stacks 0C0B applied to the stages after `k`: the base change to `A` being smooth, some stage
receiving a map from `k` is already smooth. -/
private lemma exists_baseChange_smooth_under
    {B C : Type*} [CommRing B] [CommRing C] [Algebra R B] [Algebra R C] (φ : B →ₐ[R] C)
    (hφ : φ.toRingHom.FinitePresentation)
    (hA : (Algebra.TensorProduct.map (AlgHom.id R ↥A) φ).toRingHom.Smooth) (k : J) :
    ∃ (l : J) (_ : k ⟶ l),
      (Algebra.TensorProduct.map (AlgHom.id R ↥(pres.diag.obj l)) φ).toRingHom.Smooth := by
  let pres' : ColimitPresentation (Under k) A := pres.reindex (Under.forget k)
  have h₂ : IsColimit ((forget CommRingCat.{v}).mapCocone
      ((forget₂ (CommAlgCat.{v} R) CommRingCat.{v}).mapCocone pres'.cocone)) :=
    (Functor.Final.isColimitWhiskerEquiv (Under.forget k) _).symm (isColimitForget pres)
  have : PreservesColimit (pres'.diag ⋙ forget₂ (CommAlgCat.{v} R) CommRingCat.{v})
      (forget CommRingCat.{v}) :=
    preservesColimit_of_preserves_colimit_cocone (isColimitForget₂ pres') h₂
  obtain ⟨i, hi⟩ :=
    RingHom.Smooth.exists_baseChange_smooth_of_colimitPresentation pres' φ hφ hA
  exact ⟨i.right, i.hom, hi⟩

end Spread

/-- **Stacks 07RI.** If `φ : B →ₐ[R] C` is of finite presentation and its base change
`A ⊗[R] B → A ⊗[R] C` to the filtered colimit `A` of the `Aᵢ` is étale, then already
`Aᵢ ⊗[R] B → Aᵢ ⊗[R] C` is étale for some stage `i`. -/
public theorem solution
    {R : Type u} [CommRing R] {J : Type w} [Category.{t} J] [IsFiltered J]
    {A : CommAlgCat.{v} R} (pres : ColimitPresentation J A)
    [PreservesColimit (pres.diag ⋙ forget₂ (CommAlgCat.{v} R) CommRingCat.{v})
      (forget CommRingCat)]
    {B C : Type*} [CommRing B] [CommRing C] [Algebra R B] [Algebra R C] (φ : B →ₐ[R] C)
    (hφ : φ.toRingHom.FinitePresentation)
    (hA : (Algebra.TensorProduct.map (AlgHom.id R ↥A) φ).toRingHom.Etale) :
    ∃ i : J, (Algebra.TensorProduct.map (AlgHom.id R ↥(pres.diag.obj i)) φ).toRingHom.Etale := by
  let : Algebra B C := φ.toRingHom.toAlgebra
  have : IsScalarTower R B C :=
    IsScalarTower.of_algebraMap_eq fun r => by
      rw [RingHom.algebraMap_toAlgebra]; exact (φ.commutes r).symm
  have hφeq : IsScalarTower.toAlgHom R B C = φ := AlgHom.ext fun b => rfl
  have : Algebra.FiniteType B C := by
    have h := RingHom.FiniteType.of_finitePresentation hφ
    rwa [show φ.toRingHom = algebraMap B C from (RingHom.algebraMap_toAlgebra _).symm,
      RingHom.finiteType_algebraMap] at h
  rw [RingHom.etale_iff_formallyUnramified_and_smooth] at hA
  have hunr : ∀ x : Ω[C⁄B], (1 : ↥A) ⊗ₜ[R] x = 0 := by
    rw [← formallyUnramified_baseChange_iff (B := B) (C := C) ↥A, hφeq]
    exact hA.1
  obtain ⟨k, hk⟩ := exists_forall_tmul_eq_zero pres (C := C) (M := Ω[C⁄B]) hunr
  obtain ⟨l, f, hl⟩ := exists_baseChange_smooth_under pres φ hφ hA.2 k
  refine ⟨l, ?_⟩
  rw [RingHom.etale_iff_formallyUnramified_and_smooth]
  refine ⟨?_, hl⟩
  rw [← hφeq, formallyUnramified_baseChange_iff (B := B) (C := C) ↥(pres.diag.obj l)]
  exact fun x => tmul_eq_zero_of_map pres f x (hk x)

end Stacks.Etale.ColimitSpreadOut

open CategoryTheory Limits



namespace RingHom.Etale

/-- **Étale spreads out in a filtered colimit of base rings.** Let `A` be the colimit of a
filtered diagram of `R`-algebras `Aᵢ`, computed on underlying sets, and let `φ : B →ₐ[R] C` be of
finite presentation. If the base change `1 ⊗ φ : A ⊗[R] B → A ⊗[R] C` is étale, then
`1 ⊗ φ : Aᵢ ⊗[R] B → Aᵢ ⊗[R] C` is étale for some `i`. -/
@[stacks 07RI "The source's `A_0` is the base ring `R` and its index set restricted to `i ≥ 0`,
which is cofinal, is the diagram; `A = colim A_i` is `Limits.ColimitPresentation J A` in
`CommAlgCat R` over an arbitrary filtered `J`, together with the `PreservesColimit` instance
saying the colimit is computed on underlying sets, and the base change of `φ` is Mathlib's
`Algebra.TensorProduct.map (AlgHom.id R _) φ`. See the module docstring."]
public theorem exists_baseChange_etale_of_colimitPresentation
    {R : Type u} [CommRing R] {J : Type w} [Category.{t} J] [IsFiltered J]
    {A : CommAlgCat.{v} R} (pres : ColimitPresentation J A)
    [PreservesColimit (pres.diag ⋙ forget₂ (CommAlgCat R) CommRingCat) (forget CommRingCat)]
    {B C : Type*} [CommRing B] [CommRing C] [Algebra R B] [Algebra R C] (φ : B →ₐ[R] C)
    (hφ : φ.toRingHom.FinitePresentation)
    (hA : (Algebra.TensorProduct.map (AlgHom.id R ↥A) φ).toRingHom.Etale) :
    ∃ i : J, (Algebra.TensorProduct.map (AlgHom.id R ↥(pres.diag.obj i)) φ).toRingHom.Etale :=
  Stacks.Etale.ColimitSpreadOut.solution pres φ hφ hA

end RingHom.Etale
