module

public import StacksFrontier.AlgebraicGeometry.CartierAffineLocal.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleRankOneScheme.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The reverse direction of Tag 01WS, and the biconditional

Let `X` be a scheme and `I : X.IdealSheafData` a closed subscheme `D ⊆ X`. The forward direction
of [Stacks, Tag 01WS] is `Stacks.CartierAffineLocal.exists_affineOpen_nonZeroDivisor`: if the
ideal sheaf of `D` is an invertible `𝒪_X`-module then `D` is cut out, on an affine open around
every point, by a single nonzerodivisor. **This file proves the reverse direction and assembles
the biconditional, which carries the `@[stacks 01WS]` attribute.**

## Main results

* `Stacks.CartierAffineLocalConverse.isEffectiveCartierDivisor_iff_isRegular`: **Stacks Project,
  Tag 01WS.** `Stacks.Divisors.IsEffectiveCartierDivisor I` holds exactly when every point of
  the support of `I` has an affine open neighbourhood `V` carrying `f : Γ(X, V)` with
  `IsRegular f` and `I.ideal V = Ideal.span {f}`.
* `Stacks.CartierAffineLocalConverse.isEffectiveCartierDivisor_of_affineLocal`: the reverse
  direction on its own.
* `Stacks.CartierAffineLocalConverse.isEffectiveCartierDivisor_iff_nonZeroDivisor`: the same
  biconditional with the quantifier over all of `X` and the generator described by
  `nonZeroDivisors`, which is the shape this repository's consumers hold.
* `Stacks.CartierAffineLocalConverse.trivializationOfGenerator`: **reusable.** A sectionwise
  `Stacks.SheafDescent.Trivialization` of a presheaf of modules `P` over an object `U` of any
  site, built from an injective linear form `ι : P(W) ⟶ 𝒪(W)` whose image is the multiples of a
  left-cancellable `gen W`. Nothing about schemes enters.
* `Stacks.CartierAffineLocalConverse.ker_eq_span`: the geometric heart. For every open
  `W ≤ V` — not only the affine ones — the sections of `𝒪_X` over `W` killed by `D` are exactly
  the multiples of the restricted generator.

## How a load-bearing compiler option is avoided

The chart-by-chart route to the reverse direction goes through a trivialization of the ideal
sheaf over each affine chart and then through the equivalence of invertibility with being finite
locally free of rank one (Tag 0B8M). Its key step needs
`set_option backward.isDefEq.respectTransparency false`, because it builds a `LocalGeneratorsData`
out of an isomorphism `M.over V ≅ 𝒪|_V` —
moving a module sheaf along `Scheme.Opens.ι`, a *load-bearing* use of that option:
`Scheme.Modules.restrictAppIso` is `Iso.refl` and the
restriction maps are `rfl`, but the module structure of `L|_P` acts through
`(P.ι.appIso V).inv`, whose body is not exposed.

**The replacement is to never form `M.over V` at all.** `Stacks.SheafDescent.Trivialization O P U`
is a *sectionwise* object: a family of `𝒪(W)`-linear isomorphisms `P(W) ≃ 𝒪(W)` for every
`W ⟶ U` in the site, compatible with restriction. It mentions neither the slice site nor the
restriction functor, so no module sheaf is moved anywhere, and
`Stacks.SheafDescent.isInvertible_of_trivialization` — clause 1 of [Stacks, Tag 0B8M], proved,
which produces the inverse as the sheafified dual — consumes exactly that. So the chain here is

    (affine-local nonzerodivisor description)
      → ker_eq_span                         (the sections of `ℐ` over EVERY open `W ≤ V`)
      → trivializationOfGenerator           (the sectionwise trivialization)
      → Stacks.SheafDescent.isInvertible_of_trivialization

with no compiler option set anywhere in this file. The bijection route of
`Stacks.NormMapInvertible.bijective_smul_restrictAppIso` was not needed either: it is the repair
for a proof that has already crossed the open immersion, and the point here is not to cross it.

**What the replacement costs.** `Trivialization` quantifies over *every* open `W ≤ V`, not just
the affine ones, so the affine-chart hypothesis has to be propagated to arbitrary opens. That is
`ker_eq_span`, and it is the only genuinely new mathematics below:

* the generator stays a nonzerodivisor on every `W ≤ V` (`nonZeroDivisor_res`), because a section
  it kills is killed on every basic open `D(g) ⊆ W` of `V` — where `Γ(X, D(g))` is a localization
  of `Γ(X, V)` and `IsLocalization.map_nonZeroDivisors_le` applies — and those cover `W`;
* the generator generates the sections killed by `D` over every `W ≤ V`. The inclusion `⊇` is
  naturality of `AlgebraicGeometry.Scheme.Hom.app`. The inclusion `⊆` is a gluing: on each
  `D(g) ⊆ W` the section is `a_g` times the generator by
  `AlgebraicGeometry.Scheme.IdealSheafData.map_ideal_basicOpen`, the `a_g` agree on overlaps
  because the generator is a nonzerodivisor there, and `TopCat.Sheaf.existsUnique_gluing'`
  assembles them.

The sections of the ideal sheaf over an **arbitrary** open are identified with that ideal of
`Γ(X, W)` by `Stacks.Conormal.AffineCotangent.Sections.exists_idealSheaf_section_iff_mem_ker`,
which needs no affineness — that is what makes the arbitrary-open statement sayable at all, and
it is what makes this route cheaper than the chart-by-chart one.

## Implementation notes

**The same three spellings of `Γ(X, W)`'s ring meet here as in
`StacksFrontier/AlgebraicGeometry/CartierAffineLocal/Basic.lean`, and the same recipe applies.**
The core (`coeff` … `apply_eq_genEquiv_mul`) is stated over a bare `Semiring R` with the module
structure an *ordinary implicit* argument `{inst : Module R M}` and with `ι : M →ₗ[R] R` the
first explicit argument, so `R`, `M` and `inst` are all fixed by unification rather than by
instance search. The core concludes only equations in `R` written with `*` and `0`; no `Ideal`
and no `nonZeroDivisors` appears there, because at the
  `Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf`
spelling the ring is a `RingCat` object and `CommRing ↑(…)` is not synthesizable. All the
commutative algebra happens in `Γ(X, V)`.

**`trivializationOfGenerator` localises every crossing to one application site.** It is stated
entirely in `Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O` vocabulary, so its
  own proof never crosses a
spelling; `trivialization` then supplies the hypotheses at the `Γ(X, W)` spelling and the
argument-type checks are `isDefEq` at *default* transparency, which unfolds
`structureSheafRing`, `CategoryTheory.sheafCompose` and
`CategoryTheory.SheafOfModules.unit`. Three bridges hold by `rfl`:
`(structureRingPresheaf X.presheaf).map i r = (X.presheaf.map i).hom r`, the same for
`(SheafOfModules.unit (structureSheafRing X.toRingedSpace)).val.map`, and
`PresheafOfModules.naturality_apply` of the ideal-sheaf inclusion read at `Γ(X, W)`.

**Two `rw` failures, both fixed in term mode.**

* In `trivializationOfGenerator.θ_naturality` the section `P.map h'.op m` has
  `(ModuleCat.restrictScalars …).obj (P.obj (op W'))` as the *type* of its elaborated form, so a
  `rw` motive over it is not type-correct at implicit transparency and the rewrite is reported as
  "did not find an occurrence of the pattern" on a pattern that is present. The whole naturality
  argument is therefore a chain of `Eq.trans`.
* `TopCat.Sheaf.existsUnique_gluing'` returns its section at the `X.sheaf.obj` spelling of the
  structure presheaf, at which `s * r` is again not type-correct at implicit transparency. The
  section is re-obtained at `Γ(X, W)` by `obtain ⟨s, hs⟩ : ∃ s : Γ(X, W), …`, after which the
  rewrites go through.

**Restriction bookkeeping is free.** In `X.Opens` any two morphisms with the same endpoints are
equal by definitional proof irrelevance, so `res_res` is stated with an *arbitrary* third
morphism `k : D ⟶ A` and closes by `rfl` after `← Functor.map_comp`. Every composite restriction
below is handled by it, and no `eqToHom` appears anywhere in this file.

## The covering set for Tag 01WS

Tag 01WS is a single biconditional with no labelled parts, so the covering set is that one
biconditional, and
`isEffectiveCartierDivisor_iff_isRegular` is it: same hypotheses (none beyond
`I : X.IdealSheafData`), same quantifier `∀ x ∈ I.supportSet`, same `IsRegular f`.

**What differs is the rendering of the source's `D ∩ U = Spec(A/fA)`.** A scheme-level rendering
packages it as
the data of an isomorphism `pullback I.subschemeι U.ι ≅ Spec (A ⧸ (f))` together with a
compatibility square against the closed immersions; the statement here is the equation
`I.ideal U = Ideal.span {f}` between ideals of `A = Γ(X, U)`. `I.ideal U` *is* the ideal cutting
`D` out on `U`, so the two express the same condition, and the ideal-level form is the one this
repository's consumers ask for -- it is literally the hypothesis of
`Stacks.AlgebraicGeometry.CartierComplementDense`
`.isSchemeTheoreticallyDense_supportCompl_of_nonZeroDivisor`. The scheme-level packaging is not
produced; see *What is not done*.

## What is not done, and what is not claimed

* **The scheme-level isomorphism `D ×_X U ≅ Spec (Γ(X, U) ⧸ (f))` compatible with the closed
  immersions is not produced**, in either direction. The Mathlib input for both bridges to the
  ideal-level statement is `AlgebraicGeometry.Scheme.IdealSheafData.subschemeIsoSpecQuotient`;
  nothing here depends on them and nothing here supplies them.
* **No `@[stacks 07ZU]` attribute is attached.** The density half of Tag 07ZU is now
  unconditional — `Stacks.CartierAffineLocal.isSchemeTheoreticallyDense_supportCompl` — but Tag
  07ZU also asserts that `U ⟶ S` is affine, which is proved nowhere in this repository, so the
  covering set is still incomplete.
* **No `@[stacks 0B8M]` or `@[stacks 01WR]` attribute is attached.** Clause 1 of 0B8M is
  consumed, not reproved; 01WR's two definitions are consumed from
  `StacksFrontier/AlgebraicGeometry/Divisors/EffectiveCartier.lean`, where they are already tagged.
* Nothing is proved about the invertible sheaf `ℐ_D` beyond invertibility: no identification of
  `ℐ_D` with `𝒪_X(-D)`, and no statement about the normal sheaf or the conormal module.
* `trivializationOfGenerator` is stated for an arbitrary site but is instantiated here only at
  the site of opens of a scheme.

## References

* [Stacks Project, Tag 01WS](https://stacks.math.columbia.edu/tag/01WS)
* [Stacks Project, Tag 01WR](https://stacks.math.columbia.edu/tag/01WR)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 07ZU](https://stacks.math.columbia.edu/tag/07ZU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction Stacks.SheafOfModules.TensorSheafification

universe v u w

namespace Stacks.CartierAffineLocalConverse

/-! ### The typeclass-free core -/

section Core

variable {R : Type u} [Semiring R] {M : Type u} [AddCommMonoid M] {inst : Module R M}

/-- The coefficient of a section against a generator: the element `a` with `ι m = a * f`. -/
noncomputable def coeff (ι : M →ₗ[R] R) (f : R) (hgen : ∀ m : M, ∃ a : R, ι m = a * f)
    (m : M) : R :=
  (hgen m).choose

/-- The value `ι m` is the coefficient `coeff ι f hgen m` times the generator `f`. -/
theorem apply_eq_coeff_mul (ι : M →ₗ[R] R) (f : R) (hgen : ∀ m : M, ∃ a : R, ι m = a * f)
    (m : M) : ι m = coeff ι f hgen m * f :=
  (hgen m).choose_spec

/-- The coefficient map is linear as soon as the generator is a left-cancellable element. -/
noncomputable def coeffMap (ι : M →ₗ[R] R) (f : R) (hgen : ∀ m : M, ∃ a : R, ι m = a * f)
    (hreg : ∀ a b : R, a * f = b * f → a = b) : M →ₗ[R] R where
  toFun := coeff ι f hgen
  map_add' m m' := hreg _ _ <| by
    rw [add_mul, ← apply_eq_coeff_mul, ← apply_eq_coeff_mul, ← apply_eq_coeff_mul, map_add]
  map_smul' c m := hreg _ _ <| by
    have h := apply_eq_coeff_mul ι f hgen (c • m)
    rw [map_smul, apply_eq_coeff_mul ι f hgen m] at h
    simpa [smul_eq_mul, mul_assoc] using h.symm

/-- The value `ι m` is `coeffMap ι f hgen hreg m` times the generator `f`. -/
theorem apply_eq_coeffMap_mul (ι : M →ₗ[R] R) (f : R) (hgen : ∀ m : M, ∃ a : R, ι m = a * f)
    (hreg : ∀ a b : R, a * f = b * f → a = b) (m : M) :
    ι m = coeffMap ι f hgen hreg m * f :=
  apply_eq_coeff_mul ι f hgen m

/-- **The trivialization attached to a regular generator.** If an injective linear form `ι` on
`M` has image exactly the multiples of `f`, and `f` is left-cancellable, then `M ≃ₗ[R] R`. -/
noncomputable def genEquiv (ι : M →ₗ[R] R) (hι : Function.Injective ι) (f : R)
    (hgen : ∀ m : M, ∃ a : R, ι m = a * f) (hsurj : ∀ a : R, ∃ m : M, ι m = a * f)
    (hreg : ∀ a b : R, a * f = b * f → a = b) : M ≃ₗ[R] R :=
  LinearEquiv.ofBijective (coeffMap ι f hgen hreg)
    ⟨fun m m' h => hι (by
        rw [apply_eq_coeffMap_mul ι f hgen hreg m, apply_eq_coeffMap_mul ι f hgen hreg m']
        exact congrArg (· * f) h),
      fun a => by
        obtain ⟨m, hm⟩ := hsurj a
        exact ⟨m, hreg _ _ (by rw [← apply_eq_coeffMap_mul, hm])⟩⟩

/-- The value `ι m` is `genEquiv ι hι f hgen hsurj hreg m` times the generator `f`. -/
theorem apply_eq_genEquiv_mul (ι : M →ₗ[R] R) (hι : Function.Injective ι) (f : R)
    (hgen : ∀ m : M, ∃ a : R, ι m = a * f) (hsurj : ∀ a : R, ∃ m : M, ι m = a * f)
    (hreg : ∀ a b : R, a * f = b * f → a = b) (m : M) :
    ι m = genEquiv ι hι f hgen hsurj hreg m * f :=
  apply_eq_coeff_mul ι f hgen m

end Core

/-! ### A sectionwise trivialization from a regular generator -/

section Generic

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ CommRingCat.{max u v w})
  (P : PresheafOfModules.{max u v w} (structureRingPresheaf O))

/-- **A sectionwise trivialization from a regular generator.** -/
noncomputable def trivializationOfGenerator (U : C)
    (ι : ∀ (W : C) (_ : W ⟶ U),
      (P.obj (op W) : Type max u v w) →ₗ[((structureRingPresheaf O).obj (op W) :
        Type max u v w)] ((structureRingPresheaf O).obj (op W) : Type max u v w))
    (hι : ∀ (W : C) (h : W ⟶ U), Function.Injective (ι W h))
    (hnat : ∀ (W W' : C) (h : W ⟶ U) (h' : W' ⟶ W) (m : P.obj (op W)),
      ι W' (h' ≫ h) (P.map h'.op m) = (structureRingPresheaf O).map h'.op (ι W h m))
    (gen : ∀ (W : C) (_ : W ⟶ U), ((structureRingPresheaf O).obj (op W) : Type max u v w))
    (hres : ∀ (W W' : C) (h : W ⟶ U) (h' : W' ⟶ W),
      (structureRingPresheaf O).map h'.op (gen W h) = gen W' (h' ≫ h))
    (hgen : ∀ (W : C) (h : W ⟶ U) (m : P.obj (op W)), ∃ a, ι W h m = a * gen W h)
    (hsurj : ∀ (W : C) (h : W ⟶ U) (a : ((structureRingPresheaf O).obj (op W) :
      Type max u v w)), ∃ m : P.obj (op W), ι W h m = a * gen W h)
    (hreg : ∀ (W : C) (h : W ⟶ U) (a b : ((structureRingPresheaf O).obj (op W) :
      Type max u v w)), a * gen W h = b * gen W h → a = b) :
    Stacks.SheafDescent.Trivialization O P U where
  θ W h := genEquiv (ι W h) (hι W h) (gen W h) (hgen W h) (hsurj W h) (hreg W h)
  -- Term mode throughout: the section `P.map h'.op m` has the `ModuleCat.restrictScalars`
  -- carrier as its type, so a `rw` motive over it is not type-correct at implicit
  -- transparency and the rewrite is reported as a missing pattern.
  θ_naturality {W W'} h h' m := by
    refine hreg W' (h' ≫ h) _ _ ?_
    refine Eq.trans (apply_eq_genEquiv_mul (ι W' (h' ≫ h)) (hι W' (h' ≫ h))
      (gen W' (h' ≫ h)) (hgen W' (h' ≫ h)) (hsurj W' (h' ≫ h)) (hreg W' (h' ≫ h))
      (P.map h'.op m)).symm ?_
    refine Eq.trans (hnat W W' h h' m) ?_
    refine Eq.trans (congrArg (ConcreteCategory.hom ((structureRingPresheaf O).map h'.op))
      (apply_eq_genEquiv_mul (ι W h) (hι W h) (gen W h) (hgen W h) (hsurj W h)
        (hreg W h) m)) ?_
    refine Eq.trans (map_mul _ _ _) ?_
    rw [hres]

end Generic

/-! ### Restriction bookkeeping -/

variable {X : Scheme.{u}}

/-- **Two restrictions compose to one.** All morphisms between two fixed opens agree by proof
irrelevance, so the third morphism is arbitrary. -/
theorem res_res {A B D : X.Opens} (i : B ⟶ A) (j : D ⟶ B) (k : D ⟶ A) (s : Γ(X, A)) :
    (X.presheaf.map j.op).hom ((X.presheaf.map i.op).hom s) = (X.presheaf.map k.op).hom s := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← X.presheaf.map_comp]
  rfl

/-! ### The ideal of sections cut out by a closed subscheme -/

variable (I : X.IdealSheafData)

/-- **The sections killed by a closed immersion restrict to sections killed by it.** This is
naturality of `AlgebraicGeometry.Scheme.Hom.app`. -/
theorem mem_ker_res {W W' : X.Opens} (i : W' ⟶ W) {r : Γ(X, W)}
    (hr : r ∈ RingHom.ker (I.subschemeι.app W).hom) :
    (X.presheaf.map i.op).hom r ∈ RingHom.ker (I.subschemeι.app W').hom := by
  rw [RingHom.mem_ker] at hr ⊢
  have hn := congr($(I.subschemeι.naturality (U' := W) (U := W') i.op).hom r)
  rw [CommRingCat.hom_comp, CommRingCat.hom_comp, RingHom.comp_apply, RingHom.comp_apply] at hn
  rw [hn, hr, map_zero]

/-! ### The chart data -/

section Chart

variable (V : X.affineOpens) (f : Γ(X, V.1)) (hf : f ∈ nonZeroDivisors Γ(X, V.1))
  (hgen : I.ideal V = Ideal.span {f})

include hf in
omit hgen in
/-- **The generator stays a nonzerodivisor on a basic open.** `Γ(X, D(g))` is a localization of
`Γ(X, V)`, and localizing cannot turn a nonzerodivisor into a zerodivisor. -/
theorem nonZeroDivisor_basicOpen (g : Γ(X, V.1)) :
    (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom f ∈
      nonZeroDivisors Γ(X, X.basicOpen g) := by
  have hres : IsLocalization.Away g Γ(X, X.basicOpen g) := V.2.isLocalization_basicOpen g
  refine IsLocalization.map_nonZeroDivisors_le (M := Submonoid.powers g)
    (S := Γ(X, X.basicOpen g)) ?_
  rw [← RingHom.algebraMap_toAlgebra (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom]
  exact ⟨f, hf, rfl⟩

include hgen in
/-- **The ideal on a basic open of the chart is generated by the restricted generator.** -/
theorem ker_basicOpen (g : Γ(X, V.1)) :
    RingHom.ker (I.subschemeι.app (X.basicOpen g)).hom =
      Ideal.span {(X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom f} := by
  have h1 : RingHom.ker (I.subschemeι.app (X.basicOpen g)).hom =
      I.ideal (X.affineBasicOpen g) := I.ker_subschemeι_app (X.affineBasicOpen g)
  rw [h1, ← I.map_ideal_basicOpen V g, hgen, Ideal.map_span, Set.image_singleton]

include hf in
omit hgen in
/-- **The generator stays a nonzerodivisor on every open of the chart.** A section killed by it
is killed on every basic open of `V` inside the given one, and those cover it. -/
theorem nonZeroDivisor_res {W : X.Opens} (i : W ⟶ V.1) :
    (X.presheaf.map i.op).hom f ∈ nonZeroDivisors Γ(X, W) :=
  mem_nonZeroDivisors_iff_right.mpr fun a ha => by
    refine X.IsSheaf.section_ext (U := op W) fun x hx => ?_
    obtain ⟨g, hgW, hxg⟩ := V.2.exists_basicOpen_le (V := W) ⟨x, hx⟩ (i.le hx)
    refine ⟨X.basicOpen g, hgW, hxg, ?_⟩
    rw [map_zero]
    refine mem_nonZeroDivisors_iff_right.mp
      (nonZeroDivisor_basicOpen V f hf g) _ ?_
    rw [← res_res i (homOfLE hgW) (homOfLE (X.basicOpen_le g)) f, ← map_mul, ha, map_zero]

include hf in
omit hgen in
/-- The coefficient of a section against the generator is unique. -/
theorem coeff_unique {W : X.Opens} (i : W ⟶ V.1) {a b : Γ(X, W)}
    (h : a * (X.presheaf.map i.op).hom f = b * (X.presheaf.map i.op).hom f) : a = b :=
  (mul_cancel_right_mem_nonZeroDivisors (nonZeroDivisor_res V f hf i)).mp h

/-- **The coefficient over a basic open of the chart, restricted.** If `a` is the coefficient of
`r` against the generator over `D(g)`, then its restriction to a smaller open is the coefficient
of `r` there. -/
theorem res_coeff {W : X.Opens} (r : Γ(X, W)) (g : Γ(X, V.1)) (hgW : X.basicOpen g ≤ W)
    {D : X.Opens} (j : D ⟶ (X.basicOpen g : X.Opens)) (k : D ⟶ V.1) (k' : D ⟶ W)
    {a : Γ(X, X.basicOpen g)}
    (ha : a * (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom f =
      (X.presheaf.map (homOfLE hgW).op).hom r) :
    (X.presheaf.map j.op).hom a * (X.presheaf.map k.op).hom f =
      (X.presheaf.map k'.op).hom r := by
  rw [← res_res (homOfLE (X.basicOpen_le g)) j k f, ← map_mul, ha,
    res_res (homOfLE hgW) j k' r]

include hf hgen in
/-- **The ideal of sections killed by the subscheme is generated by the generator, on every open
of the chart.** The inclusion `⊇` is naturality of `AlgebraicGeometry.Scheme.Hom.app`; the
inclusion `⊆` is a gluing: on each basic open of `V` inside `W` the section is a multiple of the
generator, the coefficients agree on overlaps because the generator is a nonzerodivisor there,
and the glued coefficient works because the structure sheaf is separated. -/
theorem ker_eq_span {W : X.Opens} (i : W ⟶ V.1) :
    RingHom.ker (I.subschemeι.app W).hom = Ideal.span {(X.presheaf.map i.op).hom f} := by
  have hfV : f ∈ RingHom.ker (I.subschemeι.app V.1).hom := by
    rw [I.ker_subschemeι_app V, hgen]
    exact Ideal.mem_span_singleton_self f
  refine le_antisymm ?_ ?_
  · intro r hr
    rw [Ideal.mem_span_singleton']
    choose g hgW hxg using fun x : W => V.2.exists_basicOpen_le (V := W) x (i.le x.2)
    have hcoe : ∀ x : W, ∃ a : Γ(X, X.basicOpen (g x)),
        a * (X.presheaf.map (homOfLE (X.basicOpen_le (g x))).op).hom f =
          (X.presheaf.map (homOfLE (hgW x)).op).hom r := by
      intro x
      rw [← Ideal.mem_span_singleton', ← ker_basicOpen I V f hgen (g x)]
      exact mem_ker_res I _ hr
    choose a ha using hcoe
    have hcover : W ≤ ⨆ x : W, X.basicOpen (g x) := fun y hy =>
      Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxg ⟨y, hy⟩⟩
    have hcompat : TopCat.Presheaf.IsCompatible X.presheaf
        (fun x : W => X.basicOpen (g x)) a := by
      intro x y
      refine coeff_unique V f hf
        (homOfLE ((inf_le_left (a := X.basicOpen (g x)) (b := X.basicOpen (g y))).trans
          ((hgW x).trans i.le))) ?_
      rw [res_coeff V f r (g x) (hgW x) (Opens.infLELeft _ _) _
            (homOfLE (inf_le_left.trans (hgW x))) (ha x),
        res_coeff V f r (g y) (hgW y) (Opens.infLERight _ _) _
            (homOfLE (inf_le_right.trans (hgW y))) (ha y)]
    obtain ⟨s₀, hs₀, -⟩ := X.sheaf.existsUnique_gluing'
      (fun x : W => X.basicOpen (g x)) W (fun x => homOfLE (hgW x)) hcover a hcompat
    -- The gluing produces its section at the `X.sheaf.obj` spelling of the structure presheaf;
    -- re-obtaining it at `Γ(X, W)` is what makes the multiplication below type-correct at
    -- implicit transparency, hence rewritable.
    obtain ⟨s, hs⟩ : ∃ s : Γ(X, W), ∀ x : W,
        (X.presheaf.map (homOfLE (hgW x)).op).hom s = a x := ⟨s₀, hs₀⟩
    refine ⟨s, X.IsSheaf.section_ext (U := op W) fun x hx => ?_⟩
    refine ⟨X.basicOpen (g ⟨x, hx⟩), hgW ⟨x, hx⟩, hxg ⟨x, hx⟩, ?_⟩
    rw [map_mul, res_res i (homOfLE (hgW ⟨x, hx⟩)) (homOfLE (X.basicOpen_le (g ⟨x, hx⟩))) f,
      hs ⟨x, hx⟩, ha ⟨x, hx⟩]
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact mem_ker_res I i hfV

/-! ### The trivialization of the ideal sheaf over a chart -/

include hf hgen in
/-- Every section of the ideal sheaf over an open of the chart is a multiple of the generator. -/
theorem exists_mul {W : X.Opens} (h : W ⟶ V.1)
    (m : (Stacks.ClosedImmersion.idealSheaf I.subschemeι.toLRSHom.toShHom).val.obj (op W)) :
    ∃ a : Γ(X, W), ((Stacks.CartierAffineLocal.incl I).val.app (op W)).hom m =
      a * (X.presheaf.map h.op).hom f := by
  have hmem := (Stacks.Conormal.AffineCotangent.Sections.exists_idealSheaf_section_iff_mem_ker
    I.subschemeι W (((Stacks.CartierAffineLocal.incl I).val.app (op W)).hom m)).mp ⟨m, rfl⟩
  rw [ker_eq_span I V f hf hgen h] at hmem
  exact (Ideal.mem_span_singleton'.mp hmem).imp fun _ => Eq.symm

include hf hgen in
/-- Every multiple of the generator is a section of the ideal sheaf. -/
theorem exists_section {W : X.Opens} (h : W ⟶ V.1) (a : Γ(X, W)) :
    ∃ m : (Stacks.ClosedImmersion.idealSheaf I.subschemeι.toLRSHom.toShHom).val.obj (op W),
      ((Stacks.CartierAffineLocal.incl I).val.app (op W)).hom m =
        a * (X.presheaf.map h.op).hom f := by
  refine (Stacks.Conormal.AffineCotangent.Sections.exists_idealSheaf_section_iff_mem_ker
    I.subschemeι W (a * (X.presheaf.map h.op).hom f)).mpr ?_
  rw [ker_eq_span I V f hf hgen h]
  exact Ideal.mem_span_singleton'.mpr ⟨a, rfl⟩

include hf hgen in
/-- **The ideal sheaf is sectionwise trivial over a chart on which it is cut out by a
nonzerodivisor.** -/
noncomputable def trivialization :
    Stacks.SheafDescent.Trivialization X.presheaf
      (Stacks.ClosedImmersion.idealSheaf I.subschemeι.toLRSHom.toShHom).val V.1 :=
  trivializationOfGenerator X.presheaf
    (Stacks.ClosedImmersion.idealSheaf I.subschemeι.toLRSHom.toShHom).val V.1
    (fun W _ => ((Stacks.CartierAffineLocal.incl I).val.app (op W)).hom)
    (fun W _ => Stacks.CartierAffineLocal.injective_incl_app I W)
    (fun _ _ _ h' m => PresheafOfModules.naturality_apply
      (Stacks.CartierAffineLocal.incl I).val h'.op m)
    (fun _ h => (X.presheaf.map h.op).hom f)
    (fun _ _ h h' => res_res h h' (h' ≫ h) f)
    (fun _ h m => exists_mul I V f hf hgen h m)
    (fun _ h a => exists_section I V f hf hgen h a)
    (fun _ h _ _ hab => coeff_unique V f hf h hab)

include hf hgen in
/-- **The trivialization is the coefficient against the generator.** The image in the structure
sheaf of a section of the ideal sheaf is its trivialization times the restricted generator. This
is what lets two trivializations built from two different generators be compared.

The coefficient is passed as an element `a` of `Γ(X, W)` together with the equation naming it,
rather than written into the statement: `Stacks.SheafDescent.Trivialization.θ` takes its values
in `Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf`, which is `Γ(X, W)` only
after `forget₂ CommRingCat RingCat` is unfolded, so a product written there finds no `HMul`. -/
theorem incl_app_eq_θ_mul {W : X.Opens} (h : W ⟶ V.1)
    (m : (Stacks.ClosedImmersion.idealSheaf I.subschemeι.toLRSHom.toShHom).val.obj (op W))
    (a : Γ(X, W)) (ha : (trivialization I V f hf hgen).θ W h m = a) :
    ((Stacks.CartierAffineLocal.incl I).val.app (op W)).hom m
      = a * (X.presheaf.map h.op).hom f := by
  rw [← ha]
  exact apply_eq_coeff_mul ((Stacks.CartierAffineLocal.incl I).val.app (op W)).hom
    ((X.presheaf.map h.op).hom f) (fun m => exists_mul I V f hf hgen h m) m

end Chart

/-! ### Away from the support the ideal is the unit ideal -/

/-- **Off the support of `I` there is an affine open on which `I` is the unit ideal.** A point
outside the support lies in a basic open `D(g)` of some affine open `U` with `g ∈ I.ideal U`;
`Γ(X, D(g))` is the localization of `Γ(X, U)` away from `g`, in which the image of `g` is a
unit, so the ideal becomes everything. -/
theorem exists_affineOpen_ideal_eq_top (I : X.IdealSheafData) {x : X}
    (hx : x ∉ I.supportSet) :
    ∃ V : X.affineOpens, x ∈ (V : Set X) ∧ I.ideal V = ⊤ := by
  obtain ⟨-, ⟨U₀, hU₀, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  set U : X.affineOpens := ⟨U₀, hU₀⟩
  have hxU' : x ∈ (U : X.Opens) := hxU
  have hz : x ∉ X.zeroLocus (U := U.1) (I.ideal U) := fun hzero =>
    hx ((I.mem_supportSet_iff_of_mem hxU').2 hzero)
  simp only [Scheme.mem_zeroLocus_iff, SetLike.mem_coe] at hz
  obtain ⟨g, hg⟩ := not_forall.mp hz
  obtain ⟨hgI, hgb⟩ := not_imp.mp hg
  refine ⟨X.affineBasicOpen g, by simpa using hgb, ?_⟩
  have hWU : X.affineBasicOpen g ≤ U := X.affineBasicOpen_le g
  let _ : Algebra Γ(X, U.1) Γ(X, X.basicOpen g) :=
    (X.presheaf.map (homOfLE hWU).op).hom.toAlgebra
  have _ : IsLocalization.Away g Γ(X, X.basicOpen g) :=
    U.2.isLocalization_of_eq_basicOpen g (homOfLE hWU) rfl
  have hunit : IsUnit ((X.presheaf.map (homOfLE hWU).op).hom g) := by
    change IsUnit (algebraMap Γ(X, U.1) Γ(X, X.basicOpen g) g)
    exact IsLocalization.Away.algebraMap_isUnit g
  rw [← I.map_ideal hWU]
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hgI) hunit

/-! ### Tag 01WS -/

/-- **Stacks Project, Tag 01WS, reverse direction.** A closed subscheme which near every point
of its support is cut out on an affine open by a single nonzerodivisor is an effective Cartier
divisor, that is, its ideal sheaf is an invertible `𝒪_X`-module.

The charts supplied by the hypothesis cover only the support; `exists_affineOpen_ideal_eq_top`
supplies a chart with generator `1` around every other point, and the two families together
cover `X`. Over each chart `Stacks.CartierAffineLocalConverse.trivialization` makes the ideal
sheaf sectionwise isomorphic to the structure sheaf, and
`Stacks.SheafDescent.isInvertible_of_trivialization` -- clause 1 of [Stacks, Tag 0B8M], whose
inverse is the sheafified dual -- turns that into invertibility. -/
theorem isEffectiveCartierDivisor_of_affineLocal (I : X.IdealSheafData)
    (hloc : ∀ x ∈ I.supportSet, ∃ V : X.affineOpens, x ∈ (V : Set X) ∧ ∃ f : Γ(X, V.1),
      f ∈ nonZeroDivisors Γ(X, V.1) ∧ I.ideal V = Ideal.span {f}) :
    Stacks.Divisors.IsEffectiveCartierDivisor I := by
  have hall : ∀ x : X, ∃ V : X.affineOpens, x ∈ (V : Set X) ∧ ∃ f : Γ(X, V.1),
      f ∈ nonZeroDivisors Γ(X, V.1) ∧ I.ideal V = Ideal.span {f} := by
    intro x
    by_cases hx : x ∈ I.supportSet
    · exact hloc x hx
    · obtain ⟨V, hxV, htop⟩ := exists_affineOpen_ideal_eq_top I hx
      exact ⟨V, hxV, 1, one_mem _, by rw [htop, Ideal.span_singleton_one]⟩
  choose V hxV f hf hgen using hall
  exact Stacks.SheafDescent.isInvertible_of_trivialization
    X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property
    (Stacks.ClosedImmersion.idealSheaf I.subschemeι.toLRSHom.toShHom)
    ((Opens.coversTop_iff _ fun x : X => (V x).1).mpr
      (TopologicalSpace.IsOpenCover.mk
        (eq_top_iff.mpr fun x _ => Opens.mem_iSup.mpr ⟨x, hxV x⟩)))
    fun x => trivialization I (V x) (f x) (hf x) (hgen x)

/-- **Stacks Project, Tag 01WS.** A closed subscheme `D ⊆ X` is an effective Cartier divisor if
and only if every point of `D` has an affine open neighbourhood `U` in `X` on which `D` is cut
out by a nonzerodivisor `f ∈ Γ(X, U)`.

The forward direction is `Stacks.CartierAffineLocal.exists_affineOpen_isRegular`, which proves
the stronger statement with the quantifier over all of `X`; the reverse direction is
`isEffectiveCartierDivisor_of_affineLocal`.

The right-hand side renders the source's `D ∩ U = Spec(A/fA)` as the equation
`I.ideal U = Ideal.span {f}` between ideals of `A = Γ(X, U)`: `I.ideal U` *is* the ideal cutting
`D` out on `U`, so the two say the same thing. The scheme-level packaging as an isomorphism
`D ×_X U ≅ Spec (A ⧸ (f))` compatible with the closed immersions is not produced here; see the
module docstring. -/
@[stacks 01WS, ega "IV 21.2.12" "partial", ega "IV 21.6.5" "partial"]
theorem isEffectiveCartierDivisor_iff_isRegular (I : X.IdealSheafData) :
    Stacks.Divisors.IsEffectiveCartierDivisor I ↔
      ∀ x ∈ I.supportSet, ∃ V : X.affineOpens, x ∈ (V : Set X) ∧
        ∃ f : Γ(X, V.1), IsRegular f ∧ I.ideal V = Ideal.span {f} :=
  ⟨fun hI x _ => Stacks.CartierAffineLocal.exists_affineOpen_isRegular I hI x,
    fun h => isEffectiveCartierDivisor_of_affineLocal I fun x hx => by
      obtain ⟨V, hxV, g, hg, hgen⟩ := h x hx
      exact ⟨V, hxV, g, isRegular_iff_mem_nonZeroDivisors.mp hg, hgen⟩⟩

/-- **Stacks Project, Tag 01WS, with the quantifier over all of `X` and the generator described
by `nonZeroDivisors`.** The form the consumers in this repository ask for: both sides of
`isEffectiveCartierDivisor_iff_isRegular` imply it, because off the support the ideal is the unit
ideal, generated by the nonzerodivisor `1`. -/
@[ega "IV 21.2.12" "partial"]
theorem isEffectiveCartierDivisor_iff_nonZeroDivisor (I : X.IdealSheafData) :
    Stacks.Divisors.IsEffectiveCartierDivisor I ↔
      ∀ x : X, ∃ V : X.affineOpens, x ∈ (V : Set X) ∧
        ∃ f : Γ(X, V.1), f ∈ nonZeroDivisors Γ(X, V.1) ∧ I.ideal V = Ideal.span {f} :=
  ⟨Stacks.CartierAffineLocal.exists_affineOpen_nonZeroDivisor I,
    fun h => isEffectiveCartierDivisor_of_affineLocal I fun x _ => h x⟩

end Stacks.CartierAffineLocalConverse

end
