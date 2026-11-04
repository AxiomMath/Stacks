module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
public import StacksFrontier.Algebra.Homology.DerivedCategory.GrothendieckSpectralSequenceFunctorial
public import StacksFrontier.Algebra.Homology.DerivedCategory.InverseLimitHelpers
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightAcyclicFiniteProduct
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointDirectSumCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.IntegralDirectImageAcyclic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.ProperFiniteFibre
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.AbelianSheafSpectralSequence
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.FunctorialFirstQuadrantAbutment
import StacksCore.Tactic.StacksAttribute

/-!
# Higher direct images of a torsion sheaf along a proper morphism with bounded fibre dimension

[Stacks, Tag 095U] says that for a proper morphism of schemes `f : X ⟶ Y` all of whose fibres
have dimension at most `n`, and for *any* abelian torsion sheaf `F` on `X_étale`, one has
`R^q f_* F = 0` for every `q > 2n`.

The source proves this by induction on the fibre dimension. This file proves outright the step
that carries that induction — **the Leray/composition bound**: if `R^q f_* = 0` above degree `a`
on torsion sheaves and `R^p g_* = 0` above degree `b` on torsion sheaves, then
`R^i (f ≫ g)_* = 0` above degree `a + b` on torsion sheaves. In the source this is the Leray
spectral sequence of `X' ⟶ P^1_k ⟶ Spec k`, where the fibre dimension of the first leg has
dropped by one and the second leg is a curve, and it is what makes `2(n - 1) + 2 = 2n` go
through. The base case `n = 0` is also discharged outright, from [Stacks, Tag 03QP] (2).

What is *not* proved here is the curve case nor the geometry that produces the factorisation.
Those enter the main theorem as a single explicit hypothesis *about the given morphism*; see the
implementation notes.

## Main results

* `Stacks.EtaleCohomology.ProperFibreDimension.isZero_rightDerived_comp` — **the composition
  bound for right derived functors**, for an arbitrary pair of additive functors satisfying the
  acyclicity criterion of [Stacks, Tag 015M]: if `R^q F` vanishes at `K` above `a` and `R^p G`
  vanishes above `b` at every `R^q F K`, then `R^n (F ⋙ G)` vanishes at `K` above `a + b`.
  Proved from the Grothendieck spectral sequence of [Stacks, Tag 015N] and its first-quadrant
  abutment: the second page vanishes on the whole antidiagonal `p + q = n` once `a + b < n`.
* `Stacks.EtaleCohomology.ProperFibreDimension.hasEtaleDirectImageBound_comp` — the same for
  direct image of abelian sheaves on small étale sites: the bounds of two morphisms add along a
  composition. The torsion hypothesis survives the first leg because `R^q f_*` of a torsion
  sheaf is torsion, [Stacks, Tag 0DDD] (1).
* `Stacks.EtaleCohomology.ProperFibreDimension.hasEtaleDirectImageBound_of_curveFactorisation` —
  the dévissage step: `2(n - 1) + 2 = 2n`.
* `ProperFibreDimension.isZero_rightDerived_etaleAbelianDirectImage_of_isProper` — **[Stacks,
  Tag 095U], its dévissage**: the tag's own conclusion `R^q f_* F = 0` for `q > 2n` and an
  arbitrary abelian torsion sheaf `F`, with the single dévissage input below.
* `Stacks.EtaleCohomology.ProperFibreDimension.isEtaleHigherDirectImageBound_of_isProper` — the
  same conclusion in the `ℕ∞`-valued shape of
  `AlgebraicGeometry.Scheme.Hom.IsEtaleHigherDirectImageBound`, i.e. `cd(f) ≤ 2n`.

## Implementation notes

*The hypotheses of the main theorem.* "Proper" is taken in the source's sense, `[IsProper f]`
together with `[QuasiCompact f]`: Mathlib's `IsProper` asks for *locally* of finite type,
whereas [Stacks, Tag 01W6] asks for finite type, which is locally of finite type plus
quasi-compactness. Quasi-separatedness then comes from separatedness. The fibre-dimension
hypothesis is `Stacks.EtaleCohomology.ProperFibreDimension.HasFibreDimLE`, the topological
Krull dimension of each scheme-theoretic fibre `f.fiber y`, as in
`AlgebraicGeometry.exists_topologicalKrullDim_fiber_le`.

*The base case.* For `n = 0` the source invokes [Stacks, Tag 02LS] (More on Morphisms, Lemma
37.44.1): a proper morphism with zero-dimensional fibres is finite. That step is proved, in
`StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.ProperFiniteFibre`, by
`AlgebraicGeometry.isFinite_iff_isProper_and_forall_finite_preimage_singleton` together with
`AlgebraicGeometry.finite_preimage_singleton_of_topologicalKrullDim_fiber_le_zero`, and it was
the *only* thing missing in that case: once `f` is finite, hence integral, the vanishing
`R^q f_* F = 0` for `q > 0` is
`Stacks.EtaleCohomology.isZero_rightDerived_etaleAbelianDirectImage_of_isIntegralHom`,
[Stacks, Tag 03QP] (2). So the base case is now unconditional.

*What is assumed, and why.* One input is carried, as a hypothesis about the given `f`:

* `hdev`, for `n ≥ 1`, is the outcome of the source's dévissage for `f`: a factorisation
  `f = h ≫ g` in which `h` already satisfies the bound `2(n - 1)` and `g`, the curve leg,
  satisfies the bound `2`. The bound for the curve leg is the conclusion of Theorem 59.83.11,
  [Stacks, Tag 03SC] — étale cohomology of a torsion sheaf on a proper curve over an
  algebraically closed field vanishes above degree `2` — carried to the relative setting by
  Lemma 59.91.13, [Stacks, Tag 0DDF]. **Tag 03SC is deliberately not formalized
  here**, and Tag 0DDF is not formalized in this repository either,
  which is why the bound is assumed relatively, for `g`. The existence of the factorisation is
  the geometry of the source's steps 5–7: passing to the reduction ([Stacks, Tag 03SI]) and the
  normalization ([Stacks, Tag 0BXR]), then taking the graph of a nonconstant rational function
  inside `X × P^1`, with the error term controlled by [Stacks, Tag 04CA] and the codimension
  estimate of [Stacks, Tag 0345].

That last point is why `hdev` is a hypothesis about the given `f` and not a lemma proved for
every proper `f`: a proper morphism with fibres of dimension at most `n` need *not* itself
factor through a relative curve — a pencil on a surface has base points, so the source's
construction produces a factorisation only after a modification, together with an error term
that the source handles by a separate induction. Quantifying the factorisation over all proper
morphisms would therefore be a false hypothesis, and the resulting statement vacuous.

*Why the second page controls the abutment.* The Grothendieck spectral sequence of
[Stacks, Tag 015N] is a first-quadrant `E₂` sequence, so `p` and `q` are natural numbers and
`E_2^{p,q} = R^p G (R^q F K)`. On the antidiagonal `p + q = n` with `a + b < n`, either `q > a`,
and then `R^q F K = 0`, so the term vanishes because the zero object is injective and hence
acyclic for `G`; or `q ≤ a`, and then `p = n - q > b`, so the term vanishes by the bound for `G`.
Vanishing on a page propagates to the infinity page, the infinity page is the graded object of a
finite filtration of the abutment, so every step of that filtration is an equality — and the
filtration runs from the whole of `H^n` at step `0` to `0` at step `n + 1`.

## References

* [Stacks Project, Tag 095U](https://stacks.math.columbia.edu/tag/095U)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 015N](https://stacks.math.columbia.edu/tag/015N)
* [Stacks Project, Tag 02LS](https://stacks.math.columbia.edu/tag/02LS)
* [Stacks Project, Tag 03QP](https://stacks.math.columbia.edu/tag/03QP)
* [Stacks Project, Tag 03SC](https://stacks.math.columbia.edu/tag/03SC)
* [Stacks Project, Tag 0DDD](https://stacks.math.columbia.edu/tag/0DDD)
* [Stacks Project, Tag 0DDF](https://stacks.math.columbia.edu/tag/0DDF)
* [Stacks Project, Tag 0F0Z](https://stacks.math.columbia.edu/tag/0F0Z)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Torsion

universe u d

namespace Stacks.EtaleCohomology.ProperFibreDimension

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### Vanishing of the abutment of a first-quadrant spectral sequence -/

/-- **Vanishing propagates up the pages of a spectral sequence.** A term of `E_{r+1}` is the
homology of a short complex whose middle object is the corresponding term of `E_r`, so a term
of `E_r` which is zero stays zero on every later page. -/
@[ega "0 11.1.6" "Finite-page persistence"]
theorem isZero_page_of_le {C : Type*} [Category* C] [Abelian C] {κ : Type*}
    {cs : ℤ → ComplexShape κ} {r₀ : ℤ} (E : SpectralSequence C cs r₀) {r : ℤ} (hr : r₀ ≤ r)
    (pq : κ) (hz : IsZero ((E.page r hr).X pq)) :
    ∀ s : ℤ, r ≤ s → ∀ hs : r₀ ≤ s, IsZero ((E.page s hs).X pq) := by
  intro s hle
  induction s, hle using Int.leInduction with
  | base => exact fun _ => hz
  | succ m hm ih =>
    intro _
    have hm0 : r₀ ≤ m := hr.trans hm
    exact IsZero.of_iso (ShortComplex.isZero_homology_of_isZero_X₂ _ (ih hm0))
      (E.iso m (m + 1) pq rfl hm0).symm

/-- **Vanishing on some page propagates to the infinity page**, which is read off any page from
which all differentials into and out of the bidegree vanish. -/
theorem isZero_pageInfinity {C : Type*} [Category* C] [Abelian C] {κ : Type*}
    {cs : ℤ → ComplexShape κ} {r₀ : ℤ} (E : SpectralSequence C cs r₀) {r : ℤ} (hr : r₀ ≤ r)
    (pq : κ) [E.HasPageInfinityAt pq] (hz : IsZero ((E.page r hr).X pq)) :
    IsZero (E.pageInfinity pq) := by
  have hsr : r ≤ max r (E.rMin pq) := le_max_left _ _
  have hs0 : r₀ ≤ max r (E.rMin pq) := hr.trans hsr
  have : E.HasEdgeMonoAtFrom pq (max r (E.rMin pq)) :=
    ⟨(E.rToMin_LE_rMin pq).trans (le_max_right _ _)⟩
  have : E.HasEdgeEpiAtFrom pq (max r (E.rMin pq)) :=
    ⟨(E.rFromMin_LE_rMin pq).trans (le_max_right _ _)⟩
  exact IsZero.of_iso (isZero_page_of_le E hr pq hz _ hsr hs0)
    (E.pageInfinityIso pq (max r (E.rMin pq)))

/-- **A first-quadrant abutment vanishes in a total degree in which the second page vanishes.**
Every graded piece of the finite filtration of `H^n` is a term of the infinity page in total
degree `n`, hence zero; a step of a filtration of subobjects with zero cokernel is an equality;
and the filtration of `H^n` runs from the whole of `H^n` at step `0` to `0` at step `n + 1`. -/
theorem isZero_of_isZero_pageTwo {C : Type*} [Category* C] [Abelian C]
    {E : CohomologicalSpectralSequenceNat C 2} {H : ℕ → C}
    (D : Stacks.Cohomology.Leray.FirstQuadrantAbutment E H) (n : ℕ)
    (hz : ∀ p q : ℕ, p + q = n → IsZero ((E.page 2).X (p, q))) :
    IsZero (H n) := by
  have hiso : ∀ p : ℕ, p ≤ n → IsIso (D.ι n p) := by
    intro p hp
    have hpq : p + (n - p) = n := by omega
    have hinf : IsZero (E.pageInfinity (p, n - p)) :=
      isZero_pageInfinity E (by norm_num) (p, n - p) (hz p (n - p) hpq)
    have hck : IsZero (cokernel (D.ι (p + (n - p)) p)) :=
      IsZero.of_iso hinf (D.gradedIso p (n - p)).symm
    rw [hpq] at hck
    have := D.mono_ι n p
    have : Epi (D.ι n p) := Preadditive.epi_of_isZero_cokernel _ hck
    exact isIso_of_mono_of_epi _
  have hup : ∀ p : ℕ, p ≤ n + 1 → IsZero (D.obj n p) → IsZero (D.obj n 0) := by
    intro p
    induction p with
    | zero => exact fun _ h => h
    | succ m ih =>
      intro hm h
      refine ih (by omega) ?_
      have := hiso m (by omega)
      exact IsZero.of_iso h (asIso (D.ι n m)).symm
  exact IsZero.of_iso (hup (n + 1) le_rfl (D.isZero_bot n)) (D.topIso n).symm

/-! ### The composition bound for right derived functors -/

/-- **The composition bound for right derived functors.** Let `F : 𝒜 ⥤ ℬ` and `G : ℬ ⥤ 𝒞` be
additive functors between abelian categories with enough injectives, with `F I` acyclic for `G`
at every injective `I` — the criterion of [Stacks, Tag 015M]. If `R^q F` vanishes at `K` for
`q > a`, and `R^p G` vanishes at each `R^q F K` for `p > b`, then `R^n (G ∘ F)` vanishes at `K`
for every `n > a + b`.

This is the vanishing consequence of the Grothendieck spectral sequence
`E_2^{p,q} = R^p G (R^q F K) ⟹ R^{p+q}(G ∘ F)(K)` of [Stacks, Tag 015N]: on the antidiagonal
`p + q = n` with `a + b < n`, either `q > a` or `p > b`. -/
theorem isZero_rightDerived_comp {A B C : Type*} [Category* A] [Category* B] [Category* C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [EnoughInjectives A] [EnoughInjectives B]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] [PreservesFiniteLimits G]
    (hFG : ∀ I : A, Injective I → G.rightAcyclic (F.obj I))
    (a b : ℕ) (K : A)
    (hF : ∀ q : ℕ, a < q → IsZero ((F.rightDerived q).obj K))
    (hG : ∀ p q : ℕ, b < p → IsZero ((G.rightDerived p).obj ((F.rightDerived q).obj K)))
    (n : ℕ) (hn : a + b < n) :
    IsZero (((F ⋙ G).rightDerived n).obj K) := by
  refine isZero_of_isZero_pageTwo
    ((Stacks.Cohomology.Grothendieck.natAbutment F G hFG).toFirstQuadrantAbutment K) n ?_
  intro p q hpq
  refine IsZero.of_iso ?_ ((Stacks.Cohomology.Grothendieck.natPageTwoIso F G p q).app K)
  rcases lt_or_ge a q with hq | hq
  · rcases Nat.eq_zero_or_pos p with rfl | hp
    · exact IsZero.of_iso (G.map_isZero (hF q hq)) (G.rightDerivedZeroIsoSelf.app _)
    · exact (rightAcyclic_iff_isZero_rightDerived G _).1
        (Stacks.Cohomology.Leray.rightAcyclic_of_injective G _ (hF q hq).injective) p hp
  · exact hG p q (by omega)

/-! ### Bounds for higher direct images on small étale sites -/

section Etale

variable {X Y W : Scheme.{u}}

/- The results of this section hold at **any** choice of derived-category model for the abelian
sheaves on the small étale sites involved: the model enters only through
`isZero_rightDerived_comp` above, whose own `HasDerivedCategory` binders are free. The binder is
quantified over all schemes because the dévissage below uses the model at the intermediate curve
`C`, which it obtains from an existential and so cannot name in a binder of its own. -/
variable [hDC : ∀ Z : Scheme.{u},
  HasDerivedCategory.{d} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- `R^q f_* F = 0` for every `q > a` and every abelian *torsion* sheaf `F` on `X_étale`: the
conclusion of [Stacks, Tag 095U] with the bound `a` in place of `2n`.

This is `AlgebraicGeometry.Scheme.Hom.IsEtaleHigherDirectImageBound f a` with the bound a
natural number rather than an element of `ℕ∞`, which is the shape the induction below adds in;
`isEtaleHigherDirectImageBound_of_hasEtaleDirectImageBound` moves between the two. -/
abbrev HasEtaleDirectImageBound (f : X ⟶ Y) (a : ℕ) : Prop :=
  ∀ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
    torsionSheafProperty X.smallEtaleTopology F → ∀ q : ℕ, a < q →
      IsZero (((etaleAbelianDirectImage.{u, u + 1} f).rightDerived q).obj F)

omit hDC in
/-- A bound for the higher direct images is a bound for every larger degree. -/
theorem HasEtaleDirectImageBound.mono {f : X ⟶ Y} {a a' : ℕ} (h : HasEtaleDirectImageBound f a)
    (haa' : a ≤ a') : HasEtaleDirectImageBound f a' :=
  fun F hF q hq => h F hF q (lt_of_le_of_lt haa' hq)

include hDC in
/-- **The bounds of two morphisms add along a composition.** If `R^q f_*` vanishes above `a` and
`R^p g_*` vanishes above `b`, both on torsion sheaves, then `R^i (f ≫ g)_*` vanishes above
`a + b` on torsion sheaves.

This is the Leray step of the argument of [Stacks, Tag 095U] — in the source, the Leray spectral
sequence of `X' ⟶ P^1_k ⟶ Spec k`. The general statement is `isZero_rightDerived_comp`; the two
étale inputs are that `f_*` preserves injective objects, which gives the acyclicity criterion of
[Stacks, Tag 015M], and that `R^q f_*` of a torsion abelian sheaf is again torsion,
[Stacks, Tag 0DDD] (1), which is what lets the bound for `g` be applied to it. -/
theorem hasEtaleDirectImageBound_comp (f : X ⟶ Y) (g : Y ⟶ W) [QuasiCompact f]
    [QuasiSeparated f] {a b : ℕ} (hf : HasEtaleDirectImageBound f a)
    (hg : HasEtaleDirectImageBound g b) :
    HasEtaleDirectImageBound (f ≫ g) (a + b) := by
  intro F hF i hi
  have : (etaleAbelianDirectImage.{u, u + 1} f).PreservesInjectiveObjects :=
    smallEtalePushforwardAb_preservesInjectiveObjects f
  have hcomp : IsZero ((((etaleAbelianDirectImage.{u, u + 1} f ⋙
      etaleAbelianDirectImage.{u, u + 1} g).rightDerived i).obj F)) := by
    refine isZero_rightDerived_comp (etaleAbelianDirectImage.{u, u + 1} f)
      (etaleAbelianDirectImage.{u, u + 1} g) (fun I hI => ?_) a b F (hf F hF) (fun p q hp => ?_)
      i hi
    · exact Stacks.Cohomology.Leray.rightAcyclic_of_injective _ _
        ((etaleAbelianDirectImage.{u, u + 1} f).injective_obj_of_injective hI)
    · exact hg _
        (torsionSheafProperty_rightDerived_smallEtaleDirectImageAb.{u + 1, u} f q F hF) p hp
  exact IsZero.of_iso hcomp
    ((Functor.rightDerivedIsoOfIso (etaleAbelianDirectImageCompIso.{u, u + 1} f g) i).app F).symm

omit hDC in
/-- A natural-number bound for the higher direct images gives the `ℕ∞`-valued bound of
`AlgebraicGeometry.Scheme.Hom.IsEtaleHigherDirectImageBound`, hence an upper bound for the
cohomological dimension `cd(f)` of [Stacks, Tag 0F0Z]. -/
theorem isEtaleHigherDirectImageBound_of_hasEtaleDirectImageBound (f : X ⟶ Y) (a : ℕ)
    (h : HasEtaleDirectImageBound f a)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}] :
    Scheme.Hom.IsEtaleHigherDirectImageBound f (a : ℕ∞) :=
  fun F hF i hi => h F hF i (by exact_mod_cast hi)

/-! ### The fibre-dimension dévissage of [Stacks, Tag 095U] -/

/-- All fibres of `f` have dimension at most `n`: the topological Krull dimension of every
scheme-theoretic fibre `f.fiber y` is at most `n`. This is the hypothesis of
[Stacks, Tag 095U], in the form used by
`AlgebraicGeometry.exists_topologicalKrullDim_fiber_le`. -/
abbrev HasFibreDimLE (f : X ⟶ Y) (n : ℕ) : Prop :=
  ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (n : WithBot ℕ∞)

omit hDC in
/-- The base case `n = 0` of [Stacks, Tag 095U]. A proper morphism with zero-dimensional fibres
is finite by [Stacks, Tag 02LS], hence integral, and the higher direct images along an integral
morphism all vanish by [Stacks, Tag 03QP] (2) — with no torsion hypothesis needed. -/
@[sga "4 VIII 5.6" "special case",
  sga "4 Vbis 4.3.4" "special case",
  sga "4 XVII 5.1.4" "partial",
  sga "4½ Arcata 2.3.6" "special case"]
theorem hasEtaleDirectImageBound_zero_of_isIntegralHom (f : X ⟶ Y) [IsIntegralHom f] :
    HasEtaleDirectImageBound f 0 :=
  fun F _ q hq =>
    isZero_rightDerived_etaleAbelianDirectImage_of_isIntegralHom.{u, u + 1} f F q hq

include hDC in
/-- **The dévissage step of [Stacks, Tag 095U].** Let `n ≥ 1`, and let `f : X ⟶ Y` factor as
`f = h ≫ g` where the bound `2(n - 1)` is already known for `h` — the inductive hypothesis of
the source's induction on the fibre dimension, `h` being the leg along which the fibre dimension
has dropped by one — and the bound `2` is known for `g`, the curve leg. Then `f` has the bound
`2n`.

This is the arithmetic of the source's last step, `2(n - 1) + 2 = 2n`; the addition of the
bounds is `hasEtaleDirectImageBound_comp`, i.e. the Leray spectral sequence. -/
theorem hasEtaleDirectImageBound_of_curveFactorisation {C : Scheme.{u}} (f : X ⟶ Y) (h : X ⟶ C)
    (g : C ⟶ Y) (hfac : f = h ≫ g) [QuasiCompact h] [QuasiSeparated h] {n : ℕ} (hn : 1 ≤ n)
    (hlower : HasEtaleDirectImageBound h (2 * (n - 1)))
    (h03SC : HasEtaleDirectImageBound g 2) :
    HasEtaleDirectImageBound f (2 * n) := by
  subst hfac
  exact (hasEtaleDirectImageBound_comp h g hlower h03SC).mono (by omega)

include hDC in
/-- **[Stacks, Tag 095U], its dévissage.** Let `f : X ⟶ Y` be a proper morphism of schemes — in
the source's sense, so `[IsProper f]` together with `[QuasiCompact f]`, Mathlib's `IsProper`
asking only for *locally* of finite type — all of whose fibres have dimension at most `n`. Then
for **any** abelian torsion sheaf `F` on `X_étale` and every `q > 2n`,

`R^q f_* F = 0`.

The case `n = 0` is proved outright: [Stacks, Tag 02LS] makes `f` finite, by
`AlgebraicGeometry.isFinite_iff_isProper_and_forall_finite_preimage_singleton` fed with
`AlgebraicGeometry.finite_preimage_singleton_of_topologicalKrullDim_fiber_le_zero`, finiteness
gives integrality, and the vanishing then comes from [Stacks, Tag 03QP] (2), already in this
library, through `hasEtaleDirectImageBound_zero_of_isIntegralHom`.

One input about `f` itself is assumed, and nothing else:

* `hdev` is the outcome of the source's dévissage for `f` when `n ≥ 1`: a factorisation
  `f = h ≫ g` in which `h` already satisfies the bound in dimension `n - 1` and `g`, the curve
  leg, satisfies the bound `2`. The bound for the curve leg is the conclusion of
  [Stacks, Tag 03SC] (through [Stacks, Tag 0DDF]); **Tag 03SC is deliberately not formalized
  here.** The existence of the factorisation is the
  geometry of the source's steps 5–7 (reduction, normalization, and the graph of a rational
  function in `X × P^1`), which is likewise unavailable here, and which is why it is a
  hypothesis about `f` rather than a statement proved for every proper `f`.

What the file proves is the step that turns that input into the bound: the Leray/composition
bound `hasEtaleDirectImageBound_comp`, and under it the purely homological
`isZero_rightDerived_comp`. -/
@[stacks 095U "the dévissage, with the curve input still open. PROVED: the tag's own conclusion, \
R^q f_* F = 0 for every q > 2n and every abelian TORSION sheaf F, for f proper in the source's \
sense (IsProper together with QuasiCompact, since Mathlib's IsProper asks only for locally of \
finite type) with every fibre of dimension at most n. The content proved outright is the \
Leray/composition step that makes the bounds add, 2(n-1) + 2 = 2n: that is \
hasEtaleDirectImageBound_comp, and under it isZero_rightDerived_comp, obtained from the \
Grothendieck spectral sequence of Tag 015N with no hypothesis beyond Tag 015M's acyclicity \
criterion. The base case n = 0 is proved outright as well: Tag 02LS, proved in this library by \
isFinite_iff_isProper_and_forall_finite_preimage_singleton together with \
finite_preimage_singleton_of_topologicalKrullDim_fiber_le_zero, makes f finite and therefore \
integral, and Tag 03QP (2) then gives the vanishing. ASSUMED, about the given f and nothing \
more: hdev, for \
n >= 1, a factorisation f = h ≫ g in which h already has the bound 2(n-1) and the curve leg g \
has the bound 2 — the latter is the conclusion of Tag 03SC (via Tag 0DDF), and TAG 03SC IS \
OWNED BY ANOTHER ITEM OF THIS PROJECT and is deliberately NOT formalized here, while the \
existence of the factorisation is the geometry of the source's steps 5-7 (reduction, \
normalization, graph of a rational function in X x P^1), also not available in this repository. \
The general bound is therefore NOT proved unconditionally.",
  sga "4 XVII 5.1.4" "special case",
  sga "4 XVII 5.2.8.1" "special case",
  sga "4½ Cycle 2.3.1" "special case"]
theorem isZero_rightDerived_etaleAbelianDirectImage_of_isProper
    (f : X ⟶ Y) [IsProper f] [QuasiCompact f] (n : ℕ) (hdim : HasFibreDimLE f n)
    (hdev : 1 ≤ n → ∃ (C : Scheme.{u}) (h : X ⟶ C) (g : C ⟶ Y), f = h ≫ g ∧
      QuasiCompact h ∧ QuasiSeparated h ∧
      HasEtaleDirectImageBound h (2 * (n - 1)) ∧ HasEtaleDirectImageBound g 2)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : torsionSheafProperty X.smallEtaleTopology F) (q : ℕ) (hq : 2 * n < q) :
    IsZero (((etaleAbelianDirectImage.{u, u + 1} f).rightDerived q).obj F) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : IsFinite f :=
      (isFinite_iff_isProper_and_forall_finite_preimage_singleton f).2
        ⟨inferInstance, fun y =>
          finite_preimage_singleton_of_topologicalKrullDim_fiber_le_zero f y (hdim y)⟩
    exact hasEtaleDirectImageBound_zero_of_isIntegralHom f F hF q (by omega)
  · obtain ⟨C, h, g, hfac, hqc, hqs, hlower, h03SC⟩ := hdev hn
    have := hqc
    have := hqs
    exact hasEtaleDirectImageBound_of_curveFactorisation f h g hfac hn hlower h03SC F hF q hq

include hDC in
/-- [Stacks, Tag 095U] in the shape of [Stacks, Tag 0F0Z]: under the same dévissage input, the
cohomological dimension of a proper morphism all of whose fibres have dimension at most `n` is
at most `2n`. -/
@[sga "4 XVII 5.1.4" "special case"]
theorem isEtaleHigherDirectImageBound_of_isProper
    (f : X ⟶ Y) [IsProper f] [QuasiCompact f] (n : ℕ) (hdim : HasFibreDimLE f n)
    (hdev : 1 ≤ n → ∃ (C : Scheme.{u}) (h : X ⟶ C) (g : C ⟶ Y), f = h ≫ g ∧
      QuasiCompact h ∧ QuasiSeparated h ∧
      HasEtaleDirectImageBound h (2 * (n - 1)) ∧ HasEtaleDirectImageBound g 2)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}] :
    Scheme.Hom.IsEtaleHigherDirectImageBound f ((2 * n : ℕ) : ℕ∞) :=
  isEtaleHigherDirectImageBound_of_hasEtaleDirectImageBound f (2 * n)
    (fun F hF q hq =>
      isZero_rightDerived_etaleAbelianDirectImage_of_isProper f n hdim hdev F hF q hq)

end Etale

end Stacks.EtaleCohomology.ProperFibreDimension

end
