module

public import Mathlib.Algebra.Ring.Action.End
public import Mathlib.Algebra.Ring.Prod
public import StacksFrontier.CategoryTheory.Sites.Point.SkyscraperOnGSets
import StacksCore.Tactic.StacksAttribute

/-!
# The skyscraper splitting is not linear over the stalk ring

Let `G` be a monoid, let `𝒯_G` be the site of `G`-sets and let `p` be the point of its topos
whose inverse image forgets the `G`-action. A commutative ring `R` with an action of `G` gives a
sheaf of rings `𝒪` on `𝒯_G` whose stalk at `p` is `R` with the action forgotten, and a module
over that sheaf of rings is an `R`-module with a compatible `G`-action. For such a module `M`
the stalk of its skyscraper is `Map(G, M)`, and the scalar action of `R` on it is

`(r • f) σ = σ(r) • f σ`.

The canonical section `M → Map(G, M)` of the splitting of Stacks 05V7 sends `m` to the constant
function with value `m`, and this map is **not** `R`-linear for that action as soon as the action
of `G` on `R` is nontrivial: for `M = R` and `σ` with `σ(r) ≠ r`, the constant function `1` is
sent by `r •` to the function `σ ↦ σ(r)`, which is not constant. So the direct sum
decomposition of Stacks 05V7 is not a decomposition of modules over the stalk ring.

## Main definitions

* `Stacks.Sheaves.RingedPoint.GSets.twistedModule`: the scalar action `(r • f) σ = σ(r) • f σ`
  of `R` on `Map(G, M)`, as a module structure.
* `Stacks.Sheaves.RingedPoint.GSets.sectionsSMul` and
  `Stacks.Sheaves.RingedPoint.GSets.sectionsModule`: the pointwise action of the sections of `𝒪`
  over `{}_G G` on the sections of `p_*M` over `{}_G G`, as a module structure.
* `Stacks.Sheaves.RingedPoint.GSets.realSMul`: that action read through the identification
  `𝒪_p = R` of Stacks 05V9 — the actual `𝒪_p`-module structure on `p⁻¹p_*M = Map(G, M)`.
* `Stacks.Sheaves.RingedPoint.GSets.IsRealLinear`: a map `M → Map(G, M)` is additive and commutes
  with that action; `IsTwistedLinear` is the same for `(r • f) σ = σ(r) • f σ`.

## Main results

* `Stacks.Sheaves.RingedPoint.GSets.realSMul_eq_twistedSMul`: **part (3), first half** — the
  actual `𝒪_p`-module structure on `p⁻¹p_*M` is `(r f)(σ) = σ(r) f(σ)`.
* `Stacks.Sheaves.RingedPoint.GSets.translate_realSMul` and
  `Stacks.Sheaves.RingedPoint.GSets.realSMul_one`: the two facts it is deduced from — the actual
  structure is `G`-equivariant, and evaluation at `1_G` is `R`-linear for it.
* `Stacks.Sheaves.RingedPoint.GSets.twistedSMul_eq_of_equivariant_of_evalOne`: the scalar action
  `(r • f) σ = σ(r) • f σ` is the only `G`-equivariant one for which evaluation at `1_G` is
  `R`-linear; this is the uniqueness the previous deduction uses.
* `Stacks.Sheaves.RingedPoint.GSets.not_exists_const_twistedSMul_const`: the constant functions
  are not an `R`-submodule of `Map(G, R)` when the action of `G` on `R` is nontrivial.
* `Stacks.Sheaves.RingedPoint.GSets.not_isRealLinear_skyscraperSection`: **part (3)** — the
  canonical section of the counit, read through the identification `p⁻¹p_*R = Map(G, R)`, is not
  linear for the actual `𝒪_p`-module structure on `p⁻¹p_*R`.
* `Stacks.Sheaves.RingedPoint.GSets.exists_smul_ne_self`: a commutative ring with a nontrivial
  action of a monoid, so that the hypothesis of the previous result is satisfiable.

## Implementation notes

The actual `𝒪_p`-module structure on `p⁻¹p_*M` is not written out by the source's formula: it is
built as the action of sections on sections and the formula is then proved of it. A section of
`p_*M` over a `G`-set `X` is a map `X → M` and a section of `𝒪` over `X` is an *equivariant* map
`X → R`; the direct image of modules along a morphism of ringed topoi acts on sections through
the structure map, so the action is the pointwise one, `sectionsSMul`. Over `X = {}_G G`, whose
sections compute the stalk (Stacks 05V9), this is the action of `𝒪_p` on `p⁻¹p_*M = Map(G, M)`,
and `realSMul` is it read through the identification `𝒪_p = R`, which is
`sectionsAtRegularRingEquiv`, evaluation at `1_G`. No twist is put into `realSMul`; the twist of
the source's formula comes out of the equivariance of the sections of `𝒪`, which forces
`s(σ) = σ(s(1_G))`.

`realSMul_eq_twistedSMul` then runs the source's own argument on that structure rather than
assuming it: `realSMul` is `G`-equivariant — where `G` acts on `Map(G, M)` by right translation,
as it does on `p_*M` — and evaluation at `1_G`, which is the counit `p⁻¹p_*M → M` and is
`𝒪_p`-linear by part (2) (formally
`Stacks.Sheaves.RingedPoint.RingedPointSituation.pullbackPushforwardModules_counit_stalk`, which
identifies that counit with the underlying map of the counit `p^*p_*M ⟶ M` of the adjunction for
modules), is `R`-linear for it; and by
`twistedSMul_eq_of_equivariant_of_evalOne` there is exactly one such action.

`R`-linearity is expressed by the predicates `IsRealLinear` and `IsTwistedLinear` on functions
rather than by a bundled linear map, because `Map(G, M)` already carries the pointwise
`R`-module structure of `Pi.module`, which is a different one.

The failure is stated for an arbitrary site of `G`-sets and an arbitrary equivalence `e` with
its sheaves of sets, under the single hypothesis that some `σ` moves some `r`; that hypothesis
is about the given ring action and not about the conclusion, and `exists_smul_ne_self` exhibits
a ring satisfying it. The identification `𝒪_p = R` is `sectionsAtRegularRingEquiv`, and
`p⁻¹p_*M = Map(G, M)` is `skyscraperStalkEquiv`, both of Stacks 05V9.

## References

* [Stacks Project, Tag 05V8](https://stacks.math.columbia.edu/tag/05V8)
* [Stacks Project, Tag 05V9](https://stacks.math.columbia.edu/tag/05V9)
-/

@[expose] public section

namespace Stacks.Sheaves.RingedPoint.GSets

open CategoryTheory Stacks.Sites.GSets

universe w v u

section Twisted

variable (G : Type w) [Monoid G] (R : Type w) [CommRing R] [MulSemiringAction G R]
  (M : Type w) [AddCommGroup M] [Module R M]

/-- The scalar action of `R` on `Map(G, M)` induced on the stalk `p⁻¹p_*M` of a skyscraper:
`(r • f) σ = σ(r) • f σ`. -/
def twistedSMul (r : R) (f : G → M) : G → M := fun σ => (σ • r) • f σ

/-- The scalar action `(r • f) σ = σ(r) • f σ` of `R` on `Map(G, M)` is a module structure. -/
@[instance_reducible] def twistedModule : Module R (G → M) where
  smul := twistedSMul G R M
  one_smul f := funext fun σ => by
    change (σ • (1 : R)) • f σ = f σ
    rw [smul_one, one_smul]
  mul_smul r r' f := funext fun σ => by
    change (σ • (r * r')) • f σ = (σ • r) • (σ • r') • f σ
    rw [smul_mul', mul_smul]
  smul_zero r := funext fun σ => smul_zero (σ • r)
  smul_add r f g := funext fun σ => smul_add (σ • r) (f σ) (g σ)
  add_smul r r' f := funext fun σ => by
    change (σ • (r + r')) • f σ = (σ • r) • f σ + (σ • r') • f σ
    rw [smul_add, add_smul]
  zero_smul f := funext fun σ => by
    change (σ • (0 : R)) • f σ = 0
    rw [smul_zero, zero_smul]

/-- Right translation of the argument: the action of `G` on `Map(G, M)` carried by the direct
image `p_*M`. -/
def translate (g : G) (f : G → M) : G → M := fun σ => f (σ * g)

/-- **The scalar action on `Map(G, M)` is forced.** A scalar action of `R` on `Map(G, M)` which
is `G`-equivariant and for which evaluation at `1_G` is `R`-linear is given by
`(r • f) σ = σ(r) • f σ`.

This is a uniqueness statement about an arbitrary `sm`; that the actual `𝒪_p`-module structure
on `p⁻¹p_*M` satisfies the two hypotheses, and hence is this action, is
`realSMul_eq_twistedSMul`. -/
theorem twistedSMul_eq_of_equivariant_of_evalOne (sm : R → (G → M) → (G → M))
    (hequiv : ∀ (g : G) (r : R) (f : G → M),
      translate G M g (sm r f) = sm (g • r) (translate G M g f))
    (heval : ∀ (r : R) (f : G → M), sm r f 1 = r • f 1) (r : R) (f : G → M) :
    sm r f = twistedSMul G R M r f := by
  funext σ
  have h₁ : sm r f σ = translate G M σ (sm r f) 1 := by
    show sm r f σ = sm r f (1 * σ)
    rw [one_mul]
  have h₂ : translate G M σ f 1 = f σ := by
    show f (1 * σ) = f σ
    rw [one_mul]
  rw [h₁, hequiv σ r f, heval (σ • r) (translate G M σ f), h₂]
  rfl

/-- A map `M → Map(G, M)` is `R`-linear for the scalar action `(r • f) σ = σ(r) • f σ` if it is
additive and commutes with that action. This is a helper: linearity for the actual
`𝒪_p`-module structure on `p⁻¹p_*M` is `IsRealLinear`, and the two agree by
`isRealLinear_iff_isTwistedLinear`. -/
def IsTwistedLinear (s : M → G → M) : Prop :=
  (∀ m m' : M, s (m + m') = s m + s m') ∧
    ∀ (r : R) (m : M) (σ : G), s (r • m) σ = (σ • r) • s m σ

end Twisted

/-! ### The actual `𝒪_p`-module structure on `p⁻¹p_*M` -/

section RealStructure

variable (G : Type w) [Monoid G] (R : Type w) [CommRing R] [MulSemiringAction G R]
  (M : Type w) [AddCommGroup M] [Module R M]

/-- **The identification `𝒪_p = R` of Stacks 05V9 at the regular `G`-set itself.** The stalk
ring is the ring of sections of `𝒪` over `{}_G G`, that is the ring of equivariant maps
`{}_G G → R`, and evaluation at `1_G` carries it isomorphically onto `R`. This is
`Stacks.Sites.GSets.sectionsAtRegularRingEquiv` for the identity presentation of `{}_G G`. -/
def stalkRingEquiv : equivariantSubring G R (Action.leftRegular G) ≃+* R :=
  sectionsAtRegularRingEquiv G R
    (ι := Functor.id (Action (Type w) G)) (u₀ := Action.leftRegular G) (Iso.refl _)

/-- The identification `𝒪_p = R` is evaluation at `1_G`. -/
theorem stalkRingEquiv_apply (s : equivariantSubring G R (Action.leftRegular G)) :
    stalkRingEquiv G R s = s.1 (1 : G) := rfl

/-- The section of `𝒪` over `{}_G G` that the identification `𝒪_p = R` attaches to `r` takes the
value `r` at `1_G`. -/
theorem coe_stalkRingEquiv_symm_one (r : R) : ((stalkRingEquiv G R).symm r).1 (1 : G) = r :=
  (stalkRingEquiv_apply G R _).symm.trans ((stalkRingEquiv G R).apply_symm_apply r)

/-- A section of `𝒪` over the regular `G`-set is determined by its value at `1_G`: equivariance
gives `s(σ) = σ(s(1_G))`. This is where the twist of the source's formula comes from. -/
theorem coe_equivariantSubring_apply (s : equivariantSubring G R (Action.leftRegular G))
    (σ : G) : s.1 σ = σ • s.1 (1 : G) :=
  (congrArg s.1 (mul_one σ)).symm.trans (s.2 σ (1 : G))

/-- The section of `𝒪` over `{}_G G` attached to `r` takes the value `σ(r)` at `σ`. -/
private theorem coe_stalkRingEquiv_symm_apply (r : R) (σ : G) :
    ((stalkRingEquiv G R).symm r).1 σ = σ • r :=
  (coe_equivariantSubring_apply G R _ σ).trans
    (congrArg (fun x => σ • x) (coe_stalkRingEquiv_symm_one G R r))

/-- **The action of a section of `𝒪` on a section of `p_*M`.** A section of `p_*M` over a
`G`-set `X` is a map `X → M` and a section of `𝒪` over `X` is an equivariant map `X → R`
(`equivariantSubring`); the direct image of modules along a morphism of ringed topoi acts on
sections through the structure map, so the action is the pointwise one. Over `X = {}_G G`, whose
sections compute the stalk (Stacks 05V9), this is the action of `𝒪_p` on
`p⁻¹p_*M = Map(G, M)`. -/
def sectionsSMul (s : equivariantSubring G R (Action.leftRegular G)) (f : G → M) : G → M :=
  fun σ => s.1 σ • f σ

/-- The pointwise action of the stalk ring on `Map(G, M)` is a module structure. -/
@[instance_reducible] def sectionsModule :
    Module (equivariantSubring G R (Action.leftRegular G)) (G → M) where
  smul := sectionsSMul G R M
  one_smul f := funext fun σ => by
    change ((1 : R)) • f σ = f σ
    rw [one_smul]
  mul_smul s s' f := funext fun σ => by
    change (s.1 σ * s'.1 σ) • f σ = s.1 σ • s'.1 σ • f σ
    rw [mul_smul]
  smul_zero s := funext fun σ => smul_zero (s.1 σ)
  smul_add s f g := funext fun σ => smul_add (s.1 σ) (f σ) (g σ)
  add_smul s s' f := funext fun σ => by
    change (s.1 σ + s'.1 σ) • f σ = s.1 σ • f σ + s'.1 σ • f σ
    rw [add_smul]
  zero_smul f := funext fun σ => by
    change ((0 : R)) • f σ = 0
    rw [zero_smul]

/-- **The `𝒪_p`-module structure on `p⁻¹p_*M = Map(G, M)`**, read through the identification
`𝒪_p = R` of Stacks 05V9: `r : R` acts as the section of `𝒪` over `{}_G G` corresponding to it,
acting pointwise on sections of `p_*M`. No twist is written into this definition; the twist of
the source's formula is produced by the equivariance of that section
(`coe_equivariantSubring_apply`). -/
def realSMul (r : R) (f : G → M) : G → M :=
  sectionsSMul G R M ((stalkRingEquiv G R).symm r) f

/-- **The actual module structure on `p⁻¹p_*M` is `G`-equivariant.** The `G`-action on `p_*M` is
translation of the argument (Stacks 05V9) and `p_*M` is a module over `𝒪`, so
`g · (r · x) = g(r) · (g · x)`; here that is the equivariance of the sections of `𝒪` over
`{}_G G`. -/
theorem translate_realSMul (g : G) (r : R) (f : G → M) :
    translate G M g (realSMul G R M r f) = realSMul G R M (g • r) (translate G M g f) :=
  funext fun σ => by
    show ((stalkRingEquiv G R).symm r).1 (σ * g) • f (σ * g) =
      ((stalkRingEquiv G R).symm (g • r)).1 σ • f (σ * g)
    rw [coe_stalkRingEquiv_symm_apply, coe_stalkRingEquiv_symm_apply, mul_smul]

/-- **Evaluation at `1_G` is `R`-linear for the actual module structure on `p⁻¹p_*M`.** That map
is the counit `p⁻¹p_*M ⟶ M` (Stacks 05V9), which is `𝒪_p`-linear by part (2) of Stacks 05V8;
here it is the statement that the section of `𝒪` attached to `r` has value `r` at `1_G`. -/
theorem realSMul_one (r : R) (f : G → M) : realSMul G R M r f 1 = r • f 1 :=
  congrArg (fun x : R => x • f 1) (coe_stalkRingEquiv_symm_one G R r)

/-- **Stacks Project, Tag 05V8, part (3).** The `𝒪_p`-module structure on `p⁻¹p_*M = Map(G, M)`
is `(r f)(σ) = σ(r) f(σ)`.

This is the source's own justification, and it is applied to the actual structure rather than
assumed of it: `realSMul` is `G`-equivariant (`translate_realSMul`) and evaluation at `1_G` is
`R`-linear for it (`realSMul_one`), and by `twistedSMul_eq_of_equivariant_of_evalOne` there is
exactly one such scalar action, namely `twistedSMul`. -/
@[stacks 05V8 "(3) the O_p-module structure on p⁻¹p_*M is (r f)(σ) = σ(r) f(σ)"]
theorem realSMul_eq_twistedSMul (r : R) (f : G → M) :
    realSMul G R M r f = twistedSMul G R M r f :=
  twistedSMul_eq_of_equivariant_of_evalOne G R M (realSMul G R M)
    (translate_realSMul G R M) (realSMul_one G R M) r f

/-- A map `M → Map(G, M)` is `𝒪_p`-linear for the actual module structure on `p⁻¹p_*M` if it is
additive and commutes with `realSMul`. -/
def IsRealLinear (s : M → G → M) : Prop :=
  (∀ m m' : M, s (m + m') = s m + s m') ∧
    ∀ (r : R) (m : M), s (r • m) = realSMul G R M r (s m)

/-- Linearity for the actual module structure is linearity for `(r • f) σ = σ(r) • f σ`, the two
scalar actions being equal by `realSMul_eq_twistedSMul`. -/
theorem isRealLinear_iff_isTwistedLinear (s : M → G → M) :
    IsRealLinear G R M s ↔ IsTwistedLinear G R M s := by
  refine and_congr_right fun _ => ⟨fun h r m σ => ?_, fun h r m => ?_⟩
  · rw [h r m, realSMul_eq_twistedSMul]
    rfl
  · rw [realSMul_eq_twistedSMul]
    exact funext fun σ => h r m σ

end RealStructure

section NotLinear

variable {G : Type w} [Monoid G] {R : Type w} [CommRing R] [MulSemiringAction G R]

/-- **The constant functions are not an `R`-submodule of `Map(G, R)`.** If `σ₀` moves `r₀` then
`r₀ •` applied to the constant function `1` is the function `σ ↦ σ(r₀)`, which is not
constant. -/
theorem not_exists_const_twistedSMul_const {σ₀ : G} {r₀ : R} (h : σ₀ • r₀ ≠ r₀) :
    ¬ ∃ r : R, twistedSMul G R R r₀ (Function.const G 1) = Function.const G r := by
  rintro ⟨r, hr⟩
  have h₁ : (1 : G) • r₀ * (1 : R) = r := congrFun hr 1
  have h₂ : σ₀ • r₀ * (1 : R) = r := congrFun hr σ₀
  rw [one_smul, mul_one] at h₁
  rw [mul_one] at h₂
  exact h (h₂.trans h₁.symm)

/-- The map sending an element to the constant function with that value is not `R`-linear for
the scalar action `(r • f) σ = σ(r) • f σ` once the action of `G` on `R` is nontrivial. -/
theorem not_isTwistedLinear_const {σ₀ : G} {r₀ : R} (h : σ₀ • r₀ ≠ r₀) :
    ¬ IsTwistedLinear G R R (fun r => Function.const G r) := by
  rintro ⟨-, hsmul⟩
  refine not_exists_const_twistedSMul_const (σ₀ := σ₀) (r₀ := r₀) h ⟨r₀ * 1, ?_⟩
  funext σ
  exact (hsmul r₀ 1 σ).symm

variable {T : Type u} [Category.{v} T] {J : GrothendieckTopology T}

/-- The canonical section of the counit, read through the identification `p⁻¹p_*R = Map(G, R)`,
is not `R`-linear for the scalar action `(r • f) σ = σ(r) • f σ`.

This is the helper form of part (3) of Stacks 05V8; the statement for the actual `𝒪_p`-module
structure on `p⁻¹p_*R` is `not_isRealLinear_skyscraperSection`. -/
theorem not_isTwistedLinear_skyscraperSection
    (e : Action (Type w) G ≌ Sheaf J (Type w)) {σ₀ : G} {r₀ : R} (h : σ₀ • r₀ ≠ r₀) :
    ¬ IsTwistedLinear G R R (fun r =>
      skyscraperStalkEquiv G e R ((forgetfulPoint G e).counitSection.app R r)) := by
  have hconst : (fun r : R =>
      skyscraperStalkEquiv G e R ((forgetfulPoint G e).counitSection.app R r)) =
      fun r : R => Function.const G r :=
    funext fun r => skyscraperStalkEquiv_counitSection G e R r
  rw [hconst]
  exact not_isTwistedLinear_const h

/-- **Stacks Project, Tag 05V8, part (3).** The functorial direct sum decomposition
`p⁻¹p_*M = M ⊕ I(M)` of Stacks 05V7 is **not** `𝒪_p`-linear in general.

Take for `p` the point of the topos of `G`-sets whose inverse image forgets the action, and for
`𝒪` the sheaf of rings attached to a commutative ring `R` with an action of `G`, so that
`𝒪_p = R`. Then `p⁻¹p_*R = Map(G, R)`, the counit is evaluation at `1_G` and the canonical
section of the splitting sends `r` to the constant function with value `r`. That section is not
linear for the actual `𝒪_p`-module structure on `p⁻¹p_*R` — the pointwise action of the sections
of `𝒪` over `{}_G G`, read through `𝒪_p = R`, which is `realSMul` — as soon as some `σ` moves
some `r`: by `realSMul_eq_twistedSMul` that action carries the constant function `1` to
`σ ↦ σ(r₀)`, which is not constant. -/
@[stacks 05V8 "(3) the splitting is not O_p-linear in general"]
theorem not_isRealLinear_skyscraperSection
    (e : Action (Type w) G ≌ Sheaf J (Type w)) {σ₀ : G} {r₀ : R} (h : σ₀ • r₀ ≠ r₀) :
    ¬ IsRealLinear G R R (fun r =>
      skyscraperStalkEquiv G e R ((forgetfulPoint G e).counitSection.app R r)) := fun hlin =>
  not_isTwistedLinear_skyscraperSection e h
    ((isRealLinear_iff_isTwistedLinear G R R _).1 hlin)

end NotLinear

/-- A commutative ring with a nontrivial action of a monoid: the ring automorphisms of `ℤ × ℤ`
act on it, and swapping the factors moves `(0, 1)`. This is what makes the hypothesis of
`not_isTwistedLinear_skyscraperSection` satisfiable, so that the failure of linearity is a
failure in general and not a vacuous assertion. -/
theorem exists_smul_ne_self :
    ∃ (G : Type) (_ : Monoid G) (R : Type) (_ : CommRing R) (_ : MulSemiringAction G R)
      (σ₀ : G) (r₀ : R), σ₀ • r₀ ≠ r₀ := by
  refine ⟨RingAut (ℤ × ℤ), inferInstance, ℤ × ℤ, inferInstance, inferInstance,
    RingEquiv.prodComm, (0, 1), ?_⟩
  intro hcontra
  have : ((1 : ℤ), (0 : ℤ)) = ((0 : ℤ), (1 : ℤ)) := hcontra
  exact one_ne_zero (congrArg Prod.fst this)

end Stacks.Sheaves.RingedPoint.GSets

end
