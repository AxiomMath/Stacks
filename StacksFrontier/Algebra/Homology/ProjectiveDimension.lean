module

public import StacksCore
public import StacksCore.Tactic.StacksAttribute
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.DualNumber
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.RingTheory.LocalProperties.Projective
public import StacksFrontier.Algebra.Homology.Resolution.Defs.Comparison
public import Mathlib.Algebra.Homology.Augment
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Tactic.ENatToNat

/-!
# Projective dimension

Resolutions by projectives and the projective dimension of an object of an abelian category, and
of a module over a ring.

* `CategoryTheory.hasProjectiveDimensionLE_tfae_leftResolution` (Stacks 0CXC): projective
  dimension at most `d`, by resolutions and by syzygies.
* `schanuel` (Stacks 00O3): Schanuel's lemma.
* `DualNumberInfiniteProjDim.main_theorem`: a module of infinite projective dimension over the dual
  numbers.
* `pd_syzygy_projective` (Stacks 00O5): the leftmost syzygy of a truncated projective resolution of
  length at least `pd(M) - 1` is projective.
* `projectiveDimension_localization_le`, `globalDimension_localization_le` (Stacks 00O8):
  localization and bounds on projective and global dimension.
-/

@[expose] public section

universe v u

/-!
## Projective dimension at most `d`, by resolutions and by syzygies

Let `X` be an object of an abelian category `C` which admits a projective resolution — for
instance a module over a ring. A resolution of `X` by projectives is a left resolution by the
class `CategoryTheory.isProjective` of projective objects, in the sense of
`CategoryTheory.ObjectProperty.LeftResolution` (Stacks 00LQ): a chain complex `F.complex` of
projective objects together with a quasi-isomorphism `F.π` to `X` placed in degree `0`. It is the
source's

`⋯ → P₁ → P₀ → M → 0`,    `Pᵢ = F.complex.X i`,    `(P₀ → M) = F.π.f 0`,

the quasi-isomorphism `F.quasiIso` saying exactly that this augmented complex is exact: that
`P₀ → X` is an epimorphism and that `Ker(Pᵢ → Pᵢ₋₁)` is the image of `Pᵢ₊₁`.

The augmented complex itself is `A = F.complex.toSingle₀AsComplex X F.π`, the `ℕ`-indexed chain
complex with `X` in degree `0`, with `Pᵢ` in degree `i + 1` and with `F.π.f 0` as its differential
`A.d 1 0`: it is Mathlib's reading of a morphism to `X[0]` as a complex, inverse to
`ChainComplex.truncateTo`, so it is built from the augmentation `F.π` itself, the morphism whose
quasi-isomorphy is `F.quasiIso`. Its `d`-th cycles object `A.cycles d` is the `d`-th syzygy of `X`
along `F`: it is `X` for `d = 0`, the differential out of degree `0` being zero
(`ChainComplex.cycles₀Iso` together with `A.X 0 = X`), it is `Ker(P₀ → X)` for `d = 1`, and it is
`Ker(P_{d-1} → P_{d-2})` for `d ≥ 2`, these being the source's three cases in a single expression.

This file states that `X` has projective dimension at most `d` if and only if `X` admits a
resolution by projectives with `Pᵢ = 0` for `i > d`, if and only if the `d`-th syzygy of some
resolution by projectives is projective, if and only if the `d`-th syzygy of every one of them is
projective. The content lies in the last condition: a `d`-th syzygy is independent of the chosen
resolution up to projective summands, by Schanuel's lemma.

### Main results

* `CategoryTheory.hasProjectiveDimensionLE_tfae_leftResolution`: for `X` admitting a projective
  resolution and `d : ℕ`, the four conditions above are equivalent, in the source's order.

### Implementation notes

Mathlib's `HasProjectiveDimensionLE X d` is `HasProjectiveDimensionLT X (d + 1)`, the vanishing of
`Abelian.Ext X Y i` for every `Y` and every `i > d`, whereas the source *defines* the projective
dimension of `M` as the least length of a finite resolution of `M` by projectives. The equivalence
of items 1 and 2 is precisely the agreement of the two, so the source's definition is not restated
as a definition of its own: `Module.projectiveDimension R M` (Stacks 00O4) is `≤ d` exactly when
item 1 holds, by `CategoryTheory.projectiveDimension_le_iff`.

A resolution is this project's `CategoryTheory.ObjectProperty.LeftResolution` for the class of
projective objects (Stacks 00LQ) — the notion in which the companion statements Stacks 00O7, 0CXD
and 0CXE state resolutions by free, by finite free and by finite projective modules. It is
`CategoryTheory.ProjectiveResolution` in another spelling, field for field, so items 3 and 4 are
witnessed by, and apply to, the resolution that `HasProjectiveResolution X` provides. In
particular the augmentation `P₀ → M` is named — it is the field `F.π`, not the mere existence of
an identification of `X` with a term of the complex — and the exactness of `⋯ → P₁ → P₀ → M → 0`
is the field `F.quasiIso` rather than a condition imposed separately on the complex.

The syzygy is taken in the augmented complex `F.complex.toSingle₀AsComplex X F.π`, which is that
augmentation `F.π` read as a complex. Assembling the same complex by hand out of the morphism
`F.π.f 0` and a separate proof of `F.complex.d 1 0 ≫ F.π.f 0 = 0` gives a definitionally equal
object — that proof is the commutativity of `F.π` in degrees `1, 0` — but it presents items 3 and
4 as conditions on a complex built ad hoc, with nothing tying it to the resolution: what makes
`A.cycles d` a *syzygy* is that `A` is exact, `⋯ → P₁ → P₀ → X → 0`, and that is the
quasi-isomorphy of `F.π`, a hypothesis about `F.π` as a morphism and not about its component in
degree `0`.

The length of the resolution in item 2 is the vanishing of its terms in degrees `> d`, which is
the form Stacks 00O7 uses; exactness in degree `d` then makes `P_d → P_{d-1}` a monomorphism, the
source's leading `0 →`.

The statement is at the level of an abelian category, the source's `R`-modules being the case
`C = ModuleCat.{v} R`, where for `R` small in the universe `v` the instance assumed here follows
from `ModuleCat.enoughProjectives`. Every step of the source's argument — dimension shifting along
the short exact sequences `0 → Ker(Pᵢ → Pᵢ₋₁) → Pᵢ → Ker(Pᵢ₋₁ → Pᵢ₋₂) → 0`, and Schanuel's lemma —
is a statement about short exact sequences of projectives, so the hypotheses of the source that
are special to modules are not used and are dropped. `HasProjectiveResolution X` is assumed rather
than `EnoughProjectives C` because that is what the argument uses, the syzygies of a resolution of
`X` inheriting resolutions from it by truncation; it is the weaker hypothesis, and
`EnoughProjectives C` supplies it.

The name records that this is the characterization of `HasProjectiveDimensionLE` by left
resolutions, as opposed to the Ext-theoretic characterizations `hasProjectiveDimensionLT_iff` and
`CategoryTheory.hasProjectiveDimensionLT_of_enoughProjectives` (Stacks 065R), which measure the
same invariant without naming a resolution; it is the name under which Stacks 0CXD, 0CXE and 0CXF
cite this lemma to extend its list.

Faithfulness. (1) No hypothesis is dead: `X`, `d`, and the instance `HasProjectiveResolution X`
are all used, the instance exactly for the implications out of item 4, which is vacuously true for
an `X` with no resolution at all. (2) The base is the source's: all four items speak of one and
the same category `C`, all differentials are morphisms of `C` and the `Ext` groups behind item 1
are computed in `C`; for `C = ModuleCat R` every map in sight is `R`-linear and no change of rings
occurs. (3) The objects the source names are pinned, not merely asserted to exist: the resolution
is `F`, with its complex, its terms `F.complex.X i` and its augmentation `F.π`, and its `d`-th
syzygy is `A.cycles d` for the augmented complex `A` of those data. (4) The instantiation is not
degenerate: for `X` projective and `d = 0` all four conditions hold, item 2 witnessed by
`CategoryTheory.ProjectiveResolution.self X`, whose complex vanishes in positive degrees, whereas
over the dual numbers `R = k[x]/(x²)` the `R`-module `R/(x)` satisfies none of them for any `d`,
having no finite resolution by projectives (Stacks 0A5Q); so neither the existential items nor the
universal one is vacuously true.

### References

* [StacksProject 0CXC](https://stacks.math.columbia.edu/tag/0CXC)
* [StacksProject 00LQ](https://stacks.math.columbia.edu/tag/00LQ)
-/

/-!
## The proof of Stacks 0CXC

Let `X` be an object of an abelian category `C` which admits a resolution by projective objects.
This file proves that the following are equivalent, for `d : ℕ`: that `X` has projective dimension
at most `d`; that `X` admits a resolution by projectives whose terms vanish in degrees `> d`; that
the `d`-th syzygy of some resolution of `X` by projectives is projective; and that the `d`-th
syzygy of every one of them is projective.

A resolution of `X` by projectives is a `CategoryTheory.ObjectProperty.LeftResolution` for the
class of projective objects: a chain complex `F.complex` of projectives together with a
quasi-isomorphism `F.π` to `X` placed in degree `0`. Its *augmented complex*
`A = F.complex.toSingle₀AsComplex X F.π` is `X` in degree `0` and `F.complex.X i` in degree
`i + 1`, and the quasi-isomorphy of `F.π` says exactly that `A` is acyclic. The `d`-th syzygy of
`X` along `F` is `A.cycles d`: it is `X` for `d = 0`, it is `Ker(P₀ → X)` for `d = 1`, and it is
`Ker(P_{d-1} → P_{d-2})` for `d ≥ 2`.

The argument is dimension shifting along the syzygy sequences
`0 → A.cycles (n + 1) → A.X (n + 1) → A.cycles n → 0`, whose middle term is projective: each of
them raises or lowers a bound on the projective dimension by exactly one, so a bound `< d + 1` on
`X = A.cycles 0` is the same thing as projectivity of `A.cycles d`, independently of the resolution
chosen. A resolution whose terms vanish above degree `d` has vanishing syzygies from degree `d + 1`
on, and conversely a projective `d`-th syzygy is spliced onto the first `d` terms of the resolution
to produce one whose terms vanish above degree `d`.


### Implementation notes

A resolution by projectives in the sense of `ObjectProperty.LeftResolution` for
`CategoryTheory.isProjective` is a `CategoryTheory.ProjectiveResolution` field for field:
`CategoryTheory.ObjectProperty.LeftResolution.toProjectiveResolution` reads one as the other, and
`leftResolutionOfProjectiveResolution` is the converse reading. The whole argument is
carried out for `ProjectiveResolution`, where Mathlib's API lives.

Three facts used throughout are missing from Mathlib and proved here for want of a home:
that a projective resolution of `X` resolves any object isomorphic to `X`
(`projectiveResolutionOfIso`), that a bound on the projective dimension only depends
on the isomorphism class (`hasProjectiveDimensionLT_congr`), and that the cycles in
degree `n + 1` of a chain complex are killed by the map to the cycles in degree `n`
(`iCycles_comp_toCycles`).

The syzygy sequence `0 → A.cycles (n + 1) → A.X (n + 1) → A.cycles n → 0` of a chain complex `A`
exact in degree `n` is `shortExact_cycles`; its middle exactness is the fact that
`A.iCycles (n + 1)` is a kernel of `A.toCycles (n + 1) n`, and its epimorphy on the right is
exactness of `A` in degree `n`. Dimension shifting along it is
`hasProjectiveDimensionLT_cycles_iff`. Splicing a resolution of `Z` onto a projective
object `P` along a short exact sequence `0 → Z → P → Y → 0`, which resolves `Y`, is
`prepend`; taking for that sequence a syzygy sequence lowers by one, at the cost of
one term, the syzygy that has to be projective, and `d` such steps prove the implication from a
projective `d`-th syzygy to a resolution of length `d`
(`exists_projectiveResolution_of_projective_cycles`).

The link between a resolution and its augmented complex is a pair of facts that Mathlib records
only in one direction. Mathlib provides, for `P : ProjectiveResolution X`, the exactness of
`P.complex.X 1 → P.complex.X 0 → X` (`ProjectiveResolution.exact₀`), the exactness of
`P.complex` in positive degrees (`ProjectiveResolution.complex_exactAt_succ`) and the epimorphy of
`P.π.f 0`, which together say that the augmented complex is acyclic
(`exactAt_augmented`). The converse — that an acyclic `ℕ`-indexed chain complex `A`
of projectives in positive degrees is the augmented complex of a resolution of `A.X 0`, namely of
`ChainComplex.truncate.obj A` along `ChainComplex.truncateTo` — is `ofAcyclic`; it is
the statement left as a project in `Mathlib/Algebra/Homology/Augment.lean`, and it is what
produces the spliced resolutions. Its degree-`0` input is repackaged as
`StacksDraft.ProjectiveDimension.quasiIsoAt_zero_of`, and the three exactness conditions on
`ChainComplex.augment` as `exactAt_augment_zero`,
`StacksDraft.ProjectiveDimension.exactAt_augment_one` and
`StacksDraft.ProjectiveDimension.exactAt_augment_succ_succ`.

### References

* [StacksProject 0CXC](https://stacks.math.columbia.edu/tag/0CXC)
* [StacksProject 00O4](https://stacks.math.columbia.edu/tag/00O4)
* [StacksProject 00O5](https://stacks.math.columbia.edu/tag/00O5)
* [StacksProject 00LQ](https://stacks.math.columbia.edu/tag/00LQ)
-/

section


open CategoryTheory Limits ChainComplex HomologicalComplex

section Helpers

variable {C : Type u} [Category.{v} C] [Abelian C]

/-! ### Resolutions by projectives -/

/-- A projective resolution whose terms lie in a class `Q`, read as a left resolution by `Q` in
the sense of Stacks 00LQ. This is the converse reading to
`CategoryTheory.ObjectProperty.LeftResolution.toProjectiveResolution`; taking `Q` to be the
projective objects recovers the plain statement that a projective resolution is a left resolution
by projectives. -/
public def leftResolutionOfProjectiveResolution {Q : ObjectProperty C} {X : C}
    (P : ProjectiveResolution X) (hQ : ∀ n, Q (P.complex.X n)) : Q.LeftResolution X where
  complex := P.complex
  property := hQ
  π := P.π

/-- A projective resolution of `X` is a projective resolution of any object isomorphic to `X`,
with the same complex: the augmentation is composed with the isomorphism. -/
private noncomputable def projectiveResolutionOfIso {X Y : C} (e : X ≅ Y)
    (F : ProjectiveResolution X) : ProjectiveResolution Y where
  complex := F.complex
  projective := F.projective
  π := F.π ≫ (single₀ C).map e.hom

private lemma projectiveResolutionOfIso_complex {X Y : C} (e : X ≅ Y)
    (F : ProjectiveResolution X) : (projectiveResolutionOfIso e F).complex = F.complex :=
  rfl

/-- A bound on the projective dimension depends only on the isomorphism class of the object. -/
private lemma hasProjectiveDimensionLT_congr {X Y : C} (e : X ≅ Y) (n : ℕ) :
    HasProjectiveDimensionLT X n ↔ HasProjectiveDimensionLT Y n :=
  ⟨fun _ => hasProjectiveDimensionLT_of_iso e n, fun _ => hasProjectiveDimensionLT_of_iso e.symm n⟩

/-! ### Augmenting and truncating a chain complex -/

/-- The complex obtained by inserting `f : B.X 0 ⟶ Y` in degree `0` is exact in degree `0` exactly
when `f` is an epimorphism. -/
private lemma exactAt_augment_zero (B : ChainComplex C ℕ) {Y : C} (f : B.X 0 ⟶ Y)
    (w : B.d 1 0 ≫ f = 0) : (B.augment f w).ExactAt 0 ↔ Epi f := by
  rw [HomologicalComplex.exactAt_iff' _ 1 0 0 (by simp) (by simp)]
  exact ShortComplex.exact_iff_epi _ ((B.augment f w).shape 0 0 (by simp))

namespace StacksDraft.ProjectiveDimension

/-- The complex obtained by inserting `f : B.X 0 ⟶ Y` in degree `0` is exact in degree `1` exactly
when `B.X 1 → B.X 0 → Y` is exact. -/
public lemma exactAt_augment_one (B : ChainComplex C ℕ) {Y : C} (f : B.X 0 ⟶ Y)
    (w : B.d 1 0 ≫ f = 0) :
    (B.augment f w).ExactAt 1 ↔ (ShortComplex.mk (B.d 1 0) f w).Exact := by
  rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)]
  rfl

/-- Inserting an object in degree `0` shifts exactness in the positive degrees. -/
public lemma exactAt_augment_succ_succ (B : ChainComplex C ℕ) {Y : C} (f : B.X 0 ⟶ Y)
    (w : B.d 1 0 ≫ f = 0) (n : ℕ) :
    (B.augment f w).ExactAt (n + 2) ↔ B.ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 3) (n + 2) (n + 1) (by simp) (by simp),
    HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  rfl

end StacksDraft.ProjectiveDimension

open StacksDraft.ProjectiveDimension

/-- Deleting the object in degree `0` shifts exactness in the positive degrees. -/
private lemma exactAt_truncate (A : ChainComplex C ℕ) (n : ℕ) :
    (truncate.obj A).ExactAt (n + 1) ↔ A.ExactAt (n + 2) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp),
    HomologicalComplex.exactAt_iff' _ (n + 3) (n + 2) (n + 1) (by simp) (by simp)]
  rfl

private lemma truncateTo_f_zero (A : ChainComplex C ℕ) : A.truncateTo.f 0 = A.d 1 0 :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

namespace StacksDraft.ProjectiveDimension

/-- A morphism `φ` from an `ℕ`-indexed chain complex `K` to `Y` placed in degree `0` is a
quasi-isomorphism in degree `0` as soon as `K.X 1 → K.X 0 → Y` is exact and `K.X 0 → Y` is an
epimorphism. -/
public lemma quasiIsoAt_zero_of {K : ChainComplex C ℕ} {Y : C} (φ : K ⟶ (single₀ C).obj Y)
    {g : K.X 0 ⟶ Y} (hg : φ.f 0 = g) (w : K.d 1 0 ≫ g = 0)
    (hex : (ShortComplex.mk (K.d 1 0) g w).Exact) (hepi : Epi g) : QuasiIsoAt φ 0 := by
  subst hg
  rw [ChainComplex.quasiIsoAt₀_iff,
    ShortComplex.quasiIso_iff_of_zeros' _ (K.shape 0 0 (by simp))
      (HomologicalComplex.single_obj_d (ComplexShape.down ℕ) 0 Y 1 0)
      (HomologicalComplex.single_obj_d (ComplexShape.down ℕ) 0 Y 0 0)]
  exact ⟨hex, hepi⟩

end StacksDraft.ProjectiveDimension

/-- Exactness in degree `0` of an `ℕ`-indexed chain complex is epimorphy of `d 1 0`. -/
private lemma epi_d_one_zero (A : ChainComplex C ℕ) (h : A.ExactAt 0) : Epi (A.d 1 0) :=
  (ShortComplex.exact_iff_epi _ (A.shape 0 0 (by simp))).1
    ((HomologicalComplex.exactAt_iff' A 1 0 0 (by simp) (by simp)).1 h)

/-- An acyclic `ℕ`-indexed chain complex `A` whose terms in positive degrees are projective is the
augmented complex of a projective resolution of `A.X 0`: the resolution is the truncation
`ChainComplex.truncate.obj A` along the canonical morphism `A.truncateTo`.

This is the converse of the acyclicity of the augmented complex of a projective resolution, and is
the statement left as a project in `Mathlib/Algebra/Homology/Augment.lean`. -/
private noncomputable def ofAcyclic (A : ChainComplex C ℕ)
    (hproj : ∀ n, Projective (A.X (n + 1))) (hex : ∀ n, A.ExactAt n) :
    ProjectiveResolution (A.X 0) where
  complex := truncate.obj A
  projective n := hproj n
  π := A.truncateTo
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
        exact quasiIsoAt_zero_of _ (truncateTo_f_zero A) (A.d_comp_d 2 1 0)
          ((HomologicalComplex.exactAt_iff' A 2 1 0 (by simp) (by simp)).1 (hex 1))
          (epi_d_one_zero A (hex 0))
    | succ m =>
        rw [quasiIsoAt_iff_exactAt']
        · exact (exactAt_truncate A m).2 (hex (m + 2))
        · apply ChainComplex.exactAt_succ_single_obj⟩

/-! ### Exactness under composing with an epimorphism or a monomorphism -/

namespace StacksDraft.ProjectiveDimension

/-- Exactness of `X → Y → Z` is unchanged by precomposing with an epimorphism. -/
public lemma exact_of_epi_comp {X' X Y Z : C} {p : X' ⟶ X} [Epi p] {f : X ⟶ Y} {g : Y ⟶ Z}
    {w : f ≫ g = 0} (h : (ShortComplex.mk f g w).Exact) (w' : (p ≫ f) ≫ g = 0) :
    (ShortComplex.mk (p ≫ f) g w').Exact := by
  refine (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    (S₁ := ShortComplex.mk (p ≫ f) g w') (S₂ := ShortComplex.mk f g w)
    { τ₁ := p, τ₂ := 𝟙 _, τ₃ := 𝟙 _ }).2 h

/-- Exactness of `X → Y → Z` is unchanged by postcomposing with a monomorphism. -/
public lemma exact_of_comp_mono {X Y Z Z' : C} {f : X ⟶ Y} {g : Y ⟶ Z} {m : Z ⟶ Z'} [Mono m]
    {w : f ≫ g = 0} (h : (ShortComplex.mk f g w).Exact) (w' : f ≫ (g ≫ m) = 0) :
    (ShortComplex.mk f (g ≫ m) w').Exact := by
  refine (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    (S₁ := ShortComplex.mk f g w) (S₂ := ShortComplex.mk f (g ≫ m) w')
    { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := m }).1 h

end StacksDraft.ProjectiveDimension

/-! ### The syzygy sequences of a chain complex -/

/-- The cycles in degree `n + 1` are killed by the map to the cycles in degree `n`. -/
private lemma iCycles_comp_toCycles (A : ChainComplex C ℕ) (n : ℕ) :
    A.iCycles (n + 1) ≫ A.toCycles (n + 1) n = 0 := by
  rw [← cancel_mono (A.iCycles n), Category.assoc, toCycles_i, iCycles_d, zero_comp]

/-- Exactness in degree `n` makes `A.X (n + 1) → A.cycles n` an epimorphism. -/
private lemma epi_toCycles (A : ChainComplex C ℕ) (n : ℕ) (h : A.ExactAt n) :
    Epi (A.toCycles (n + 1) n) :=
  Preadditive.epi_of_isZero_cokernel' _ (A.homologyIsCokernel (i := n + 1) (j := n) (by simp))
    ((A.exactAt_iff_isZero_homology n).1 h)

/-- The **syzygy sequence** `0 → A.cycles (n + 1) → A.X (n + 1) → A.cycles n → 0` of a chain
complex `A` exact in degree `n`: the left-hand map is the inclusion of the cycles, of which the
right-hand map is a cokernel, and the right-hand map is the factorisation of the differential
`A.d (n + 1) n` through the cycles in degree `n`. -/
private lemma shortExact_cycles (A : ChainComplex C ℕ) (n : ℕ) (h : A.ExactAt n) :
    (ShortComplex.mk (A.iCycles (n + 1)) (A.toCycles (n + 1) n)
      (iCycles_comp_toCycles A n)).ShortExact where
  exact := by
    refine ShortComplex.exact_of_f_is_kernel _ (KernelFork.IsLimit.ofι _ _
      (fun {W} k hk => A.liftCycles' k n (by simp) ?_) ?_ ?_)
    · rw [← HomologicalComplex.toCycles_i (K := A) (i := n + 1) (j := n), ← Category.assoc, hk,
        zero_comp]
    · intro W k hk
      simp
    · intro W k hk m hm
      rw [← cancel_mono (A.iCycles (n + 1))]
      simpa using hm
  mono_f := inferInstance
  epi_g := epi_toCycles A n h

/-- **Dimension shifting.** For an acyclic chain complex `A` whose terms in positive degrees are
projective, a bound `< d + 1` on the projective dimension of the `k`-th syzygy `A.cycles k` is the
same thing as projectivity of the `(d + k)`-th syzygy. -/
private lemma hasProjectiveDimensionLT_cycles_iff (A : ChainComplex C ℕ)
    (hproj : ∀ n, Projective (A.X (n + 1))) (hex : ∀ n, A.ExactAt n) (d : ℕ) :
    ∀ k : ℕ, HasProjectiveDimensionLT (A.cycles k) (d + 1) ↔ Projective (A.cycles (d + k)) := by
  induction d with
  | zero =>
      intro k
      simp only [Nat.zero_add]
      exact (projective_iff_hasProjectiveDimensionLT_one (X := A.cycles k)).symm
  | succ d ih =>
      intro k
      rw [show d + 1 + k = d + (k + 1) from by omega]
      exact ((shortExact_cycles A k (hex k)).hasProjectiveDimensionLT_X₃_iff d
        (hproj k)).trans (ih (k + 1))

/-- A syzygy of an acyclic complex of projectives that is followed by a zero term is projective:
the syzygy sequence `0 → A.cycles (d + 1) → A.X (d + 1) → A.cycles d → 0` has projective middle
term, and its left-hand term is zero because `A.X (d + 2)` is and `A` is exact in degree
`d + 1`. -/
private lemma projective_cycles_of_isZero_X (A : ChainComplex C ℕ)
    (hproj : ∀ n, Projective (A.X (n + 1))) (hex : ∀ n, A.ExactAt n) (d : ℕ)
    (hz : IsZero (A.X (d + 2))) : Projective (A.cycles d) := by
  have := epi_toCycles A (d + 1) (hex (d + 1))
  have := hproj d
  have hzc : IsZero (A.cycles (d + 1)) :=
    IsZero.of_epi_eq_zero (A.toCycles (d + 2) (d + 1)) (hz.eq_zero_of_src _)
  exact projective_iff_hasProjectiveDimensionLT_one.2
    ((shortExact_cycles A d (hex d)).hasProjectiveDimensionLT_X₃ 0
      hzc.hasProjectiveDimensionLT_zero inferInstance)

/-! ### The augmented complex of a projective resolution -/

/-- The terms of the augmented complex of a projective resolution are projective in the positive
degrees. -/
private lemma projective_augmented_X_succ {X : C} (F : ProjectiveResolution X) (n : ℕ) :
    Projective ((F.complex.toSingle₀AsComplex X F.π).X (n + 1)) :=
  F.projective n

namespace StacksDraft.ProjectiveDimension

/-- The augmentation `P₀ ⟶ Y` of a projective resolution `F` of `Y`, as a morphism to `Y` itself:
`F.π.f 0` has for target the degree-`0` term of the complex `Y[0]`, which is `Y` only up to
unfolding the definition of `HomologicalComplex.single`. -/
public noncomputable def πZero {Y : C} (F : ProjectiveResolution Y) : F.complex.X 0 ⟶ Y :=
  ChainComplex.toSingle₀Equiv F.complex Y F.π

public lemma d_comp_πZero {Y : C} (F : ProjectiveResolution Y) :
    F.complex.d 1 0 ≫ πZero F = 0 :=
  (ChainComplex.toSingle₀Equiv F.complex Y F.π).2

public lemma epi_πZero {Y : C} (F : ProjectiveResolution Y) : Epi (πZero F) :=
  inferInstanceAs (Epi (F.π.f 0))

/-- The augmentation of a projective resolution `F` of `Y` is a cokernel of `F.complex.d 1 0`. -/
public lemma exact₀' {Y : C} (F : ProjectiveResolution Y) :
    (ShortComplex.mk (F.complex.d 1 0) (πZero F) (d_comp_πZero F)).Exact :=
  F.exact₀

end StacksDraft.ProjectiveDimension

/-- The augmented complex of a projective resolution is the augmentation of its complex by the
augmentation morphism. -/
private lemma toSingle₀AsComplex_eq {Y : C} (F : ProjectiveResolution Y) :
    F.complex.toSingle₀AsComplex Y F.π = F.complex.augment (πZero F) (d_comp_πZero F) :=
  rfl

/-- The augmented complex of a projective resolution is acyclic: this is the content of the
quasi-isomorphy of `F.π`. -/
private lemma exactAt_augmented {X : C} (F : ProjectiveResolution X) (n : ℕ) :
    (F.complex.toSingle₀AsComplex X F.π).ExactAt n := by
  rw [toSingle₀AsComplex_eq]
  match n with
  | 0 => exact (exactAt_augment_zero _ _ _).2 (epi_πZero F)
  | 1 => exact (exactAt_augment_one _ _ _).2 (exact₀' F)
  | (n + 2) => exact (exactAt_augment_succ_succ _ _ _ n).2 (F.complex_exactAt_succ n)

/-- The `0`-th syzygy of `X` along a resolution `F` by projectives is `X` itself: the augmented
complex is `X` in degree `0`, and the differential out of degree `0` is zero. -/
private noncomputable def augmentedCycles₀Iso {X : C} (F : ProjectiveResolution X) :
    (F.complex.toSingle₀AsComplex X F.π).cycles 0 ≅ X :=
  cycles₀Iso (F.complex.toSingle₀AsComplex X F.π)

/-! ### Splicing a resolution onto a short exact sequence -/

section Splice

variable {S : ShortComplex C} (F : ProjectiveResolution S.X₁)

/-- The complex `⋯ → F₁ → F₀ → P → Y → 0` built from a short exact sequence
`S : 0 → Z → P → Y → 0` and a projective resolution `F` of `Z`: it is `Y` in degree `0`, `P` in
degree `1` and `F.complex.X i` in degree `i + 2`, the differential in degree `1` being the
composite `F₀ → Z → P`. -/
private noncomputable def spliceComplex : ChainComplex C ℕ :=
  (F.complex.augment (πZero F ≫ S.f) (by rw [← Category.assoc, d_comp_πZero, zero_comp])).augment
    S.g (by change (πZero F ≫ S.f) ≫ S.g = 0; rw [Category.assoc, S.zero, comp_zero])

private lemma projective_spliceComplex_X_succ (hP : Projective S.X₂) :
    ∀ n, Projective ((spliceComplex F).X (n + 1))
  | 0 => hP
  | (n + 1) => F.projective n

/-- The spliced complex is acyclic: in degree `0` because `P → Y` is an epimorphism, in degree `1`
by exactness of `S` together with the epimorphy of `F₀ → Z`, in degree `2` because `F₀ → Z` is a
cokernel of `F₁ → F₀` and `Z → P` is a monomorphism, and above that by exactness of `F`. -/
private lemma exactAt_spliceComplex (hS : S.ShortExact) (n : ℕ) :
    (spliceComplex F).ExactAt n := by
  have := hS.mono_f
  have := epi_πZero F
  simp only [spliceComplex]
  match n with
  | 0 => exact (exactAt_augment_zero _ _ _).2 hS.epi_g
  | 1 => exact (exactAt_augment_one _ _ _).2 (exact_of_epi_comp (p := πZero F) hS.exact _)
  | 2 =>
      exact (exactAt_augment_succ_succ _ _ _ 0).2
        ((exactAt_augment_one _ _ _).2 (exact_of_comp_mono (exact₀' F) _))
  | (n + 3) =>
      exact (exactAt_augment_succ_succ _ _ _ (n + 1)).2
        ((exactAt_augment_succ_succ _ _ _ n).2 (F.complex_exactAt_succ n))

/-- **Splicing.** Let `0 → Z → P → Y → 0` be a short exact sequence with `P` projective. A
projective resolution `F` of `Z` is prepended to `P` to give a projective resolution of `Y`, whose
complex is `P` in degree `0` and `F.complex.X i` in degree `i + 1`: the complex
`⋯ → F₁ → F₀ → P → Y → 0` is acyclic, so `ofAcyclic` applies to it. -/
private noncomputable def prepend (hS : S.ShortExact) (hP : Projective S.X₂) :
    ProjectiveResolution S.X₃ :=
  ofAcyclic (spliceComplex F) (projective_spliceComplex_X_succ F hP) (exactAt_spliceComplex F hS)

private lemma prepend_complex_X_succ (hS : S.ShortExact) (hP : Projective S.X₂) (i : ℕ) :
    (prepend F hS hP).complex.X (i + 1) = F.complex.X i :=
  rfl

/-- Splicing raises by exactly one the degree above which the terms of the resolution vanish. -/
private lemma isZero_prepend_complex_X (hS : S.ShortExact) (hP : Projective S.X₂) {d : ℕ}
    (hF : ∀ i, d < i → IsZero (F.complex.X i)) (i : ℕ) (hi : d + 1 < i) :
    IsZero ((prepend F hS hP).complex.X i) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rw [prepend_complex_X_succ]
  exact hF j (by omega)

end Splice

end Helpers

section Main

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **Stacks 00O5.** The `d`-th syzygy of `X` along a resolution `F` of `X` by projectives is
projective exactly when `X` has projective dimension at most `d`. This is dimension shifting along
the syzygy sequences of the augmented complex, whose middle terms are the projective objects
`F.complex.X n`, together with the identification of the `0`-th syzygy with `X`. -/
@[ega "0 17.2.1" "more general"]
private lemma projective_cycles_iff (X : C) (F : ProjectiveResolution X) (d : ℕ) :
    Projective ((F.complex.toSingle₀AsComplex X F.π).cycles d) ↔ HasProjectiveDimensionLE X d :=
  (hasProjectiveDimensionLT_cycles_iff (F.complex.toSingle₀AsComplex X F.π)
      (projective_augmented_X_succ F) (exactAt_augmented F) d 0).symm.trans
    (hasProjectiveDimensionLT_congr (augmentedCycles₀Iso F) (d + 1))

/-- A resolution of `X` by projectives whose terms vanish in degrees `> d` has projective `d`-th
syzygy, its `(d + 1)`-st syzygy being zero. -/
private lemma projective_cycles_of_isZero (X : C) (F : ProjectiveResolution X) (d : ℕ)
    (h : ∀ i, d < i → IsZero (F.complex.X i)) :
    Projective ((F.complex.toSingle₀AsComplex X F.π).cycles d) :=
  projective_cycles_of_isZero_X _ (projective_augmented_X_succ F) (exactAt_augmented F) d
    (h (d + 1) (by omega))

/-- Let `A` be an acyclic chain complex whose terms in positive degrees are projective. If the
`(d + k)`-th syzygy of `A` is projective then the `k`-th one is resolved by the `d` terms
`A.X (k + 1), …, A.X (k + d)` above it followed by that syzygy: it has a resolution by projectives
whose terms vanish in degrees `> d`. Each step down the tower of syzygies is a splicing along a
syzygy sequence. -/
private lemma exists_projectiveResolution_of_projective_cycles (A : ChainComplex C ℕ)
    (hproj : ∀ n, Projective (A.X (n + 1))) (hex : ∀ n, A.ExactAt n) (d : ℕ) :
    ∀ k : ℕ, Projective (A.cycles (d + k)) →
      ∃ F : ProjectiveResolution (A.cycles k), ∀ i, d < i → IsZero (F.complex.X i) := by
  induction d with
  | zero =>
      intro k hk
      rw [Nat.zero_add] at hk
      have := hk
      refine ⟨ProjectiveResolution.self _, fun i hi => ?_⟩
      apply HomologicalComplex.isZero_single_obj_X
      omega
  | succ d ih =>
      intro k hk
      obtain ⟨F, hF⟩ := ih (k + 1) (by rwa [show d + (k + 1) = d + 1 + k from by omega])
      have hS := shortExact_cycles A k (hex k)
      exact ⟨prepend F hS (hproj k), isZero_prepend_complex_X F hS (hproj k) hF⟩

/-- An object of projective dimension at most `d` which admits a resolution by projectives admits
one whose terms vanish in degrees `> d`: the `d`-th syzygy of any resolution `F₀` of `X` is
projective, and the tower of syzygies of `F₀` resolves `X` by the first `d` terms of `F₀` followed
by it. -/
@[ega "0 17.2.1" "partial"]
private lemma exists_projectiveResolution_isZero (X : C) [HasProjectiveResolution X] (d : ℕ)
    (h : HasProjectiveDimensionLE X d) :
    ∃ F : ProjectiveResolution X, ∀ i, d < i → IsZero (F.complex.X i) := by
  obtain F₀ := (HasProjectiveResolution.out (Z := X)).some
  obtain ⟨F, hF⟩ := exists_projectiveResolution_of_projective_cycles
    (F₀.complex.toSingle₀AsComplex X F₀.π) (projective_augmented_X_succ F₀)
    (exactAt_augmented F₀) d 0 ((projective_cycles_iff X F₀ d).2 h)
  refine ⟨projectiveResolutionOfIso (augmentedCycles₀Iso F₀) F, fun i hi => ?_⟩
  rw [projectiveResolutionOfIso_complex]
  exact hF i hi

end Main

@[expose] public section

/-- **Stacks 0CXC.** Let `X` be an object of an abelian category which admits a projective
resolution, and let `d : ℕ`. The following are equivalent: (1) `X` has projective dimension
at most `d`; (2) there is a resolution `0 → P_d → ⋯ → P₀ → X → 0` by projectives, that is, a
left resolution `F` of `X` by projective objects with `F.complex.X i = 0` for `i > d`; (3) for
some resolution `⋯ → P₁ → P₀ → X → 0` by projectives the `d`-th syzygy of `X`, the `d`-th cycles
object of the augmented complex, is projective; (4) for every such resolution the `d`-th syzygy
is projective. -/
@[stacks 0CXC "A resolution `⋯ → P₁ → P₀ → M → 0` is an `ObjectProperty.LeftResolution` by the
class of projective objects (00LQ), the notion 00O7 uses; the source's `M`, `Ker(P₀ → M)` and
`Ker(P_{d-1} → P_{d-2})` are the single syzygy `(F.complex.toSingle₀AsComplex X F.π).cycles d`,
the `d`-th cycles of the augmentation `F.π` read as a complex; see the module docstring.",
  ega "0 17.2.1" "dim.proj resolution char"]
public theorem CategoryTheory.hasProjectiveDimensionLE_tfae_leftResolution {C : Type u}
    [Category.{v} C] [Abelian C] (X : C) [HasProjectiveResolution X] (d : ℕ) :
    List.TFAE
      [HasProjectiveDimensionLE X d,
        ∃ F : ObjectProperty.LeftResolution (isProjective C) X,
          ∀ i, d < i → Limits.IsZero (F.complex.X i),
        ∃ F : ObjectProperty.LeftResolution (isProjective C) X,
          Projective ((F.complex.toSingle₀AsComplex X F.π).cycles d),
        ∀ F : ObjectProperty.LeftResolution (isProjective C) X,
          Projective ((F.complex.toSingle₀AsComplex X F.π).cycles d)] := by
  tfae_have 1 → 2 := fun h => by
    obtain ⟨F, hF⟩ := exists_projectiveResolution_isZero X d h
    exact ⟨leftResolutionOfProjectiveResolution F F.projective, hF⟩
  tfae_have 2 → 3 := fun ⟨F, hF⟩ =>
    ⟨F, projective_cycles_of_isZero X (F.toProjectiveResolution F.property) d hF⟩
  tfae_have 3 → 1 := fun ⟨F, hF⟩ =>
    (projective_cycles_iff X (F.toProjectiveResolution F.property) d).1 hF
  tfae_have 1 → 4 := fun h F =>
    (projective_cycles_iff X (F.toProjectiveResolution F.property) d).2 h
  tfae_have 4 → 3 := fun h =>
    let P := (HasProjectiveResolution.out (Z := X)).some
    ⟨leftResolutionOfProjectiveResolution P P.projective, h _⟩
  tfae_finish

end

end


/-!
## Schanuel's Lemma

We work with modules over a fixed, not necessarily commutative, ring `R` and `R`-linear maps
between them. Let `M` be an `R`-module and suppose that

  `0 → K --c₁--> P₁ --p₁--> M → 0`   and   `0 → L --c₂--> P₂ --p₂--> M → 0`

are two short exact sequences of `R`-modules with `P₁` and `P₂` projective. Then there are
`R`-linear isomorphisms `φ : K ⊕ P₂ ≃ P₁ ⊕ L` and `ψ : P₁ ⊕ P₂ ≃ P₁ ⊕ P₂` making the diagram

  `0 → K ⊕ P₂ --(c₁,id)--> P₁ ⊕ P₂ --(p₁,0)--> M → 0`
            `φ ↓             ψ ↓           id ‖`
  `0 → P₁ ⊕ L --(id,c₂)--> P₁ ⊕ P₂ --(0,p₂)--> M → 0`

commute with both rows short exact; the right-hand vertical map is the identity on `M`. In
particular `K ⊕ P₂ ≅ P₁ ⊕ L` as `R`-modules. This is Stacks tag 00O3.

### Conventions

A short exact sequence `0 → A --f--> B --g--> C → 0` is encoded by `f` injective, `g`
surjective, and `range f = ker g`, the last being `Function.Exact f g`. The external direct sum
`X ⊕ Y` is the product type `X × Y` with its usual `R`-module structure, and projectivity is
`Module.Projective R P`, of which only the lifting property is used. The maps of the diagram
are

  * `(c₁, id) : K × P₂ → P₁ × P₂`, `(k, y) ↦ (c₁ k, y)`, i.e. `c₁.prodMap LinearMap.id`;
  * `(p₁, 0) : P₁ × P₂ → M`, `(x, y) ↦ p₁ x`, i.e. `LinearMap.coprod p₁ 0`;
  * `(id, c₂) : P₁ × L → P₁ × P₂`, `(x, ℓ) ↦ (x, c₂ ℓ)`, i.e. `LinearMap.id.prodMap c₂`;
  * `(0, p₂) : P₁ × P₂ → M`, `(x, y) ↦ p₂ y`, i.e. `LinearMap.coprod 0 p₂`.

No commutativity of `R` is assumed, and the maps are built directly from `LinearMap.prodMap`
and `LinearMap.coprod`, so no auxiliary definitions are needed.

### The argument

**Row exactness, no projectivity needed.** For any short exact sequence
`0 → A --c--> P --p--> M → 0`, the "left-tagged" row
`0 → A×Q --(c,id)--> P×Q --(p,0)--> M → 0` and the "right-tagged" row
`0 → Q×A --(id,c)--> Q×P --(0,p)--> M → 0` are short exact: injectivity of the left map follows
from injectivity of `c`, since the other coordinate is the identity; surjectivity of the right
map follows from surjectivity of `p`; and
`ker(p,0) = (ker p)×Q = (im c)×Q = im(c,id)` by exactness of `c, p`. These are
`schanuel_topRow_exact` and `schanuel_botRow_exact`.

**The middle isomorphism ψ, which uses projectivity.** By projectivity of `P₁`, lift `p₁`
through the surjection `p₂` to get `s₁ : P₁ → P₂` with `p₂ ∘ s₁ = p₁`; by projectivity of `P₂`,
lift `p₂` through `p₁` to get `s₂ : P₂ → P₁` with `p₁ ∘ s₂ = p₂`. Define the shear

  `ψ(x, y) = (x - s₂ y,  s₁ x + y - s₁ (s₂ y))`,

with inverse `ψ⁻¹(u, v) = (u + s₂ v - s₂ (s₁ u),  v - s₁ u)`; it is the product of the two
elementary transvections `[[1,0],[s₁,1]]` and `[[1,-s₂],[0,1]]`, hence invertible. The right
square `(0,p₂) ∘ ψ = (p₁,0)` holds because
`p₂ (s₁ x + y - s₁ (s₂ y)) = p₁ x + p₂ y - p₂ y = p₁ x`.

**The induced isomorphism φ on kernels.** Since `(0,p₂) ∘ ψ = (p₁,0)`, `ψ` maps `ker(p₁,0)`
onto `ker(0,p₂)`. The top row identifies `ker(p₁,0) = im(c₁,id)` and the bottom row identifies
`ker(0,p₂) = im(id,c₂)`; both `(c₁,id)` and `(id,c₂)` are injective, hence isomorphisms onto
their images. So `φ := (id,c₂)⁻¹ ∘ ψ ∘ (c₁,id)` is a well-defined isomorphism
`K×P₂ ≃ P₁×L` and the left square `(id,c₂)∘φ = ψ∘(c₁,id)` holds by construction. Concretely

  `φ(k, y) = (c₁ k - s₂ y,  c₂⁻¹ (s₁ (c₁ k) + y - s₁ (s₂ y)))`,

the second component lying in `im c₂` because its image under `p₂` is `0`.
-/

@[expose] public section

open LinearMap

-- Main Definition(s)
-- The maps of the diagram are realised directly via `LinearMap.prodMap` and
-- `LinearMap.coprod` (see the `let`-bindings in the statement below); there are
-- no auxiliary `def`s needed beyond the standard Mathlib constructions.

/-!
## Proof sketch overview (Schanuel's Lemma)

The proof has two independent strands:

**Row exactness (no projectivity needed).** For any short exact sequence
`0 → A --c--> P --p--> M → 0`, the "left-tagged" row `0 → A×Q --(c,id)--> P×Q --(p,0)--> M → 0`
and the "right-tagged" row `0 → Q×A --(id,c)--> Q×P --(0,p)--> M → 0` are short exact:
  * injectivity of the left map follows from `Injective c` (the other coordinate is `id`);
  * surjectivity of the right map follows from `Surjective p`;
  * exactness: `ker(p,0) = (ker p)×Q = (im c)×Q = im(c,id)` using `Exact c p`.
These are isolated as `schanuel_topRow_exact` and `schanuel_botRow_exact`.

**The middle isomorphism ψ (uses projectivity).** By projectivity of `P₁`, lift `p₁`
through the surjection `p₂` to get `s₁ : P₁ → P₂` with `p₂ ∘ s₁ = p₁`. By projectivity
of `P₂`, lift `p₂` through `p₁` to get `s₂ : P₂ → P₁` with `p₁ ∘ s₂ = p₂`. Define the
shear isomorphism
  `ψ(x, y) = (x - s₂ y,  s₁ x + y - s₁ (s₂ y))`
with inverse `ψ⁻¹(u, v) = (u + s₂ v - s₂ (s₁ u),  v - s₁ u)`. (ψ is the product of two
elementary transvections `[[1,0],[s₁,1]] ∘ [[1,-s₂],[0,1]]`, hence invertible.)
It satisfies the right square `(0,p₂) ∘ ψ = (p₁,0)` because
  `p₂ (s₁ x + y - s₁ (s₂ y)) = p₁ x + p₂ y - p₂ y = p₁ x`  (using `p₂∘s₁=p₁`, `p₁∘s₂=p₂`).
This is `schanuel_psi`.

**The induced isomorphism φ on kernels.** Since `(0,p₂) ∘ ψ = (p₁,0)`, ψ maps
`ker(p₁,0)` onto `ker(0,p₂)`. The top row identifies `ker(p₁,0) = im(c₁,id)` and the
bottom row identifies `ker(0,p₂) = im(id,c₂)`. Both `(c₁,id)` and `(id,c₂)` are injective,
so they are isomorphisms onto their images. Hence `φ := (id,c₂)⁻¹ ∘ ψ ∘ (c₁,id)` is a
well-defined isomorphism `K×P₂ ≃ P₁×L`, and the left square `(id,c₂)∘φ = ψ∘(c₁,id)`
holds by construction. Concretely
  `φ(k, y) = (c₁ k - s₂ y,  c₂⁻¹ (s₁ (c₁ k) + y - s₁ (s₂ y)))`,
the second component lying in `im c₂` because its image under `p₂` is `0`.
-/

section SchanuelHelpers

variable {R : Type*} [Ring R]
variable {A Q P M : Type*}
  [AddCommGroup A] [AddCommGroup Q] [AddCommGroup P] [AddCommGroup M]
  [Module R A] [Module R Q] [Module R P] [Module R M]

/-- For an exact pair `c, p`, the pair `(c, id) : A × Q → P × Q`, `(p, 0) : P × Q → M` is
exact. -/
theorem exact_prodMap_id_coprod_zero {c : A →ₗ[R] P} {p : P →ₗ[R] M}
    (hex : Function.Exact c p) :
    Function.Exact (c.prodMap (LinearMap.id : Q →ₗ[R] Q))
      (LinearMap.coprod p (0 : Q →ₗ[R] M)) := by
  rintro ⟨x, y⟩
  simp only [LinearMap.coprod_apply, LinearMap.zero_apply, add_zero, hex x]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨(a, y), by simp [ha]⟩
  · rintro ⟨⟨a, q⟩, hq⟩
    exact ⟨a, congrArg Prod.fst hq⟩

/-- For an exact pair `c, p`, the pair `(id, c) : Q × A → Q × P`, `(0, p) : Q × P → M` is
exact. -/
theorem exact_id_prodMap_zero_coprod {c : A →ₗ[R] P} {p : P →ₗ[R] M}
    (hex : Function.Exact c p) :
    Function.Exact ((LinearMap.id : Q →ₗ[R] Q).prodMap c)
      (LinearMap.coprod (0 : Q →ₗ[R] M) p) := by
  rintro ⟨x, y⟩
  simp only [LinearMap.coprod_apply, LinearMap.zero_apply, zero_add, hex y]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨(x, a), by simp [ha]⟩
  · rintro ⟨⟨q, a⟩, hq⟩
    exact ⟨a, congrArg Prod.snd hq⟩

/-- Row exactness for the **top** ("left-tagged") row of the diagram, in the abstract:
given a short exact sequence `0 → A --c--> P --p--> M → 0`, the row
`0 → A×Q --(c, id)--> P×Q --(p, 0)--> M → 0` is short exact.
Specialised in the main proof with `A=K`, `Q=P₂`, `c=c₁`, `p=p₁`. -/
theorem schanuel_topRow_exact
    (c : A →ₗ[R] P) (p : P →ₗ[R] M)
    (hc : Function.Injective c) (hp : Function.Surjective p)
    (hex : Function.Exact c p) :
    Function.Injective (c.prodMap (LinearMap.id : Q →ₗ[R] Q)) ∧
    Function.Surjective (LinearMap.coprod p (0 : Q →ₗ[R] M)) ∧
    Function.Exact (c.prodMap (LinearMap.id : Q →ₗ[R] Q))
      (LinearMap.coprod p (0 : Q →ₗ[R] M)) := by
  refine ⟨hc.prodMap Function.injective_id, fun m => ?_, exact_prodMap_id_coprod_zero hex⟩
  obtain ⟨x, rfl⟩ := hp m
  exact ⟨(x, 0), by simp⟩

/-- Row exactness for the **bottom** ("right-tagged") row of the diagram, in the abstract:
given a short exact sequence `0 → A --c--> P --p--> M → 0`, the row
`0 → Q×A --(id, c)--> Q×P --(0, p)--> M → 0` is short exact.
Specialised in the main proof with `A=L`, `Q=P₁`, `c=c₂`, `p=p₂`. -/
theorem schanuel_botRow_exact
    (c : A →ₗ[R] P) (p : P →ₗ[R] M)
    (hc : Function.Injective c) (hp : Function.Surjective p)
    (hex : Function.Exact c p) :
    Function.Injective ((LinearMap.id : Q →ₗ[R] Q).prodMap c) ∧
    Function.Surjective (LinearMap.coprod (0 : Q →ₗ[R] M) p) ∧
    Function.Exact ((LinearMap.id : Q →ₗ[R] Q).prodMap c)
      (LinearMap.coprod (0 : Q →ₗ[R] M) p) := by
  refine ⟨Function.injective_id.prodMap hc, fun m => ?_, exact_id_prodMap_zero_coprod hex⟩
  obtain ⟨y, rfl⟩ := hp m
  exact ⟨(0, y), by simp⟩

end SchanuelHelpers

section SchanuelPhi

variable {R : Type*} [Ring R]
variable {K L P₁ P₂ M : Type*}
  [AddCommGroup K] [AddCommGroup L] [AddCommGroup P₁] [AddCommGroup P₂] [AddCommGroup M]
  [Module R K] [Module R L] [Module R P₁] [Module R P₂] [Module R M]

/-- **The induced isomorphism on kernels.**
Given the middle isomorphism `ψ : P₁×P₂ ≃ P₁×P₂` intertwining the two presentations of
`M` (i.e. `(0,p₂) ∘ ψ = (p₁,0)`, the hypothesis `hcomm`), together with injectivity of
`c₁`, `c₂` and exactness of the two sequences, there is an isomorphism
`φ : K×P₂ ≃ P₁×L` making the left square commute:
`(id,c₂) ∘ φ = ψ ∘ (c₁,id)`.

Reason: `ψ` carries `ker (p₁,0)` isomorphically onto `ker (0,p₂)` (by `hcomm`); the top
row gives `ker (p₁,0) = range (c₁,id)` and the bottom row gives `ker (0,p₂) = range (id,c₂)`;
both `(c₁,id)` and `(id,c₂)` are injective, hence isomorphisms onto those ranges. So
`φ := (id,c₂)⁻¹ ∘ ψ ∘ (c₁,id)` is well defined and an isomorphism, with the left square
holding by construction.

Concretely, `φ(k,y) = (c₁ k - s₂ y, c₂⁻¹(s₁(c₁ k) + y - s₁(s₂ y)))` for the lifts `s₁,s₂`
of `ψ`. -/
theorem schanuel_phi_of_psi
    (c₁ : K →ₗ[R] P₁) (c₂ : L →ₗ[R] P₂) (p₁ : P₁ →ₗ[R] M) (p₂ : P₂ →ₗ[R] M)
    (ψ : (P₁ × P₂) ≃ₗ[R] (P₁ × P₂))
    (hc₁ : Function.Injective c₁) (hc₂ : Function.Injective c₂)
    (hex₁ : Function.Exact c₁ p₁) (hex₂ : Function.Exact c₂ p₂)
    (hcomm : (LinearMap.coprod (0 : P₁ →ₗ[R] M) p₂).comp ψ.toLinearMap
        = LinearMap.coprod p₁ (0 : P₂ →ₗ[R] M)) :
    ∃ φ : (K × P₂) ≃ₗ[R] (P₁ × L),
      (LinearMap.id.prodMap c₂).comp φ.toLinearMap
        = ψ.toLinearMap.comp (c₁.prodMap LinearMap.id) := by
  set topLeft : (K × P₂) →ₗ[R] (P₁ × P₂) := c₁.prodMap LinearMap.id
  set botLeft : (P₁ × L) →ₗ[R] (P₁ × P₂) := LinearMap.id.prodMap c₂
  have hTLinj : Function.Injective topLeft := hc₁.prodMap Function.injective_id
  have hBLinj : Function.Injective botLeft := Function.injective_id.prodMap hc₂
  have hMap : Submodule.map ψ.toLinearMap (LinearMap.range topLeft) = LinearMap.range botLeft := by
    rw [← (exact_prodMap_id_coprod_zero hex₁).linearMap_ker_eq,
      ← (exact_id_prodMap_zero_coprod hex₂).linearMap_ker_eq, ← hcomm, LinearMap.ker_comp,
      Submodule.map_comap_eq_of_surjective ψ.surjective]
  let e₂ := LinearEquiv.ofInjective botLeft hBLinj
  refine ⟨LinearEquiv.ofInjective topLeft hTLinj ≪≫ₗ ψ.submoduleMap _ ≪≫ₗ
    LinearEquiv.ofEq _ _ hMap ≪≫ₗ e₂.symm, LinearMap.ext fun z => ?_⟩
  change botLeft (e₂.symm _) = _
  rw [LinearEquiv.ofInjective_symm_apply]
  rfl

end SchanuelPhi

/-- **Schanuel's Lemma (Stacks Tag 00O3).**
Given two short exact sequences `0 → K → P₁ → M → 0` and `0 → L → P₂ → M → 0`
with `P₁`, `P₂` projective, there are `R`-linear isomorphisms
`φ : K × P₂ ≃ P₁ × L` and `ψ : P₁ × P₂ ≃ P₁ × P₂` fitting into a commutative
diagram of short exact sequences whose right-hand vertical map is the identity
on `M`. -/
@[stacks 00O3]
theorem schanuel
    {R : Type*} [Ring R]
    {K L P₁ P₂ M : Type*}
    [AddCommGroup K] [AddCommGroup L] [AddCommGroup P₁] [AddCommGroup P₂] [AddCommGroup M]
    [Module R K] [Module R L] [Module R P₁] [Module R P₂] [Module R M]
    (c₁ : K →ₗ[R] P₁) (p₁ : P₁ →ₗ[R] M) (c₂ : L →ₗ[R] P₂) (p₂ : P₂ →ₗ[R] M)
    (hP₁ : Module.Projective R P₁) (hP₂ : Module.Projective R P₂)
    -- first short exact sequence `0 → K → P₁ → M → 0`
    (hc₁ : Function.Injective c₁) (hp₁ : Function.Surjective p₁)
    (hex₁ : Function.Exact c₁ p₁)
    -- second short exact sequence `0 → L → P₂ → M → 0`
    (hc₂ : Function.Injective c₂) (hp₂ : Function.Surjective p₂)
    (hex₂ : Function.Exact c₂ p₂) :
    ∃ (φ : (K × P₂) ≃ₗ[R] (P₁ × L)) (ψ : (P₁ × P₂) ≃ₗ[R] (P₁ × P₂)),
      let topLeft : (K × P₂) →ₗ[R] (P₁ × P₂) := c₁.prodMap LinearMap.id
      let topRight : (P₁ × P₂) →ₗ[R] M := LinearMap.coprod p₁ 0
      let botLeft : (P₁ × L) →ₗ[R] (P₁ × P₂) := LinearMap.id.prodMap c₂
      let botRight : (P₁ × P₂) →ₗ[R] M := LinearMap.coprod 0 p₂
      -- (1) both rows are short exact sequences
      (Function.Injective topLeft ∧ Function.Surjective topRight ∧
        Function.Exact topLeft topRight) ∧
      (Function.Injective botLeft ∧ Function.Surjective botRight ∧
        Function.Exact botLeft botRight) ∧
      -- (3a) left square commutes: `(id, c₂) ∘ φ = ψ ∘ (c₁, id)`
      (botLeft.comp φ.toLinearMap = ψ.toLinearMap.comp topLeft) ∧
      -- (3b) right square commutes: `(0, p₂) ∘ ψ = (p₁, 0)`
      (botRight.comp ψ.toLinearMap = topRight) := by
  -- ===================================================================
  -- STEP 1.  Projective lifts s₁ : P₁ → P₂ and s₂ : P₂ → P₁.
  -- ===================================================================
  -- `p₂` is surjective and `P₁` projective, so lift `p₁ : P₁ → M` through `p₂` to get
  -- `s₁` with `p₂ ∘ s₁ = p₁`.  Symmetrically lift `p₂` through `p₁` to get `s₂` with
  -- `p₁ ∘ s₂ = p₂`.  Both lifts come from `Module.projective_lifting_property`.
  obtain ⟨s₁, (hs₁ : p₂.comp s₁ = p₁)⟩ :
      ∃ s₁ : P₁ →ₗ[R] P₂, p₂.comp s₁ = p₁ := by
    -- from projectivity of P₁ (hP₁) and surjectivity of p₂ (hp₂)
    have := hP₁
    exact Module.projective_lifting_property p₂ p₁ hp₂
  obtain ⟨s₂, (hs₂ : p₁.comp s₂ = p₂)⟩ :
      ∃ s₂ : P₂ →ₗ[R] P₁, p₁.comp s₂ = p₂ := by
    -- from projectivity of P₂ (hP₂) and surjectivity of p₁ (hp₁)
    have := hP₂
    exact Module.projective_lifting_property p₁ p₂ hp₁
  -- pointwise forms used repeatedly below
  have hs₁' : ∀ x, p₂ (s₁ x) = p₁ x := LinearMap.congr_fun hs₁
  have hs₂' : ∀ y, p₁ (s₂ y) = p₂ y := LinearMap.congr_fun hs₂
  -- ===================================================================
  -- STEP 2.  The middle isomorphism ψ : P₁ × P₂ ≃ₗ P₁ × P₂ (shear / transvection).
  --   ψ(x, y)   = (x - s₂ y,           s₁ x + y - s₁ (s₂ y))
  --   ψ⁻¹(u, v) = (u + s₂ v - s₂ (s₁ u),  v - s₁ u)
  -- ===================================================================
  set ψ : (P₁ × P₂) ≃ₗ[R] (P₁ × P₂) :=
    { toFun := fun w => (w.fst - s₂ w.snd, s₁ w.fst + w.snd - s₁ (s₂ w.snd))
      invFun := fun w => (w.fst + s₂ w.snd - s₂ (s₁ w.fst), w.snd - s₁ w.fst)
      map_add' x y := by
        simp only [Prod.fst_add, Prod.snd_add, map_add, Prod.mk_add_mk, Prod.mk.injEq]
        constructor <;> abel
      map_smul' m x := by
        simp only [Prod.smul_fst, Prod.smul_snd, map_smul, RingHom.id_apply, Prod.smul_mk,
          smul_sub, smul_add]
      left_inv := by
        intro w
        apply Prod.ext
        · simp only [map_add, map_sub]
          abel
        · simp only [map_sub]
          abel
      right_inv := by
        intro w
        apply Prod.ext
        · simp only [map_sub]
          abel
        · simp only [map_add, map_sub]
          abel } with hψdef
  -- Right square: `(0,p₂) ∘ ψ = (p₁,0)`.
  have hrightSq : (LinearMap.coprod (0 : P₁ →ₗ[R] M) p₂).comp ψ.toLinearMap
      = LinearMap.coprod p₁ (0 : P₂ →ₗ[R] M) := by
    -- Pointwise: `(0,p₂)(ψ(x,y)) = p₂ (s₁ x + y - s₁ (s₂ y))`
    --   `= p₂ (s₁ x) + p₂ y - p₂ (s₁ (s₂ y)) = p₁ x + p₂ y - p₁ (s₂ y) = p₁ x + p₂ y - p₂ y = p₁
    -- x`.
    -- using `p₂ (s₁ (s₂ y)) = p₁ (s₂ y) = p₂ y`.
    apply LinearMap.ext
    rintro ⟨x, y⟩
    simp only [LinearMap.comp_apply, hψdef,
      LinearMap.coprod_apply, LinearMap.zero_apply, zero_add, add_zero]
    change p₂ (s₁ x + y - s₁ (s₂ y)) = p₁ x
    rw [map_sub, map_add, hs₁' x, hs₁' (s₂ y), hs₂' y]
    abel
  -- ===================================================================
  have htop := schanuel_topRow_exact (Q := P₂) c₁ p₁ hc₁ hp₁ hex₁
  have hbot := schanuel_botRow_exact (Q := P₁) c₂ p₂ hc₂ hp₂ hex₂
  -- ===================================================================
  -- STEP 4.  The induced isomorphism φ : K × P₂ ≃ₗ P₁ × L on kernels.
  --   φ(k, y) = (c₁ k - s₂ y,  c₂⁻¹ (s₁ (c₁ k) + y - s₁ (s₂ y))).
  -- The second component lies in `range c₂` because its `p₂`-image is `0`:
  --   `p₂ (s₁ (c₁ k) + y - s₁ (s₂ y)) = p₁ (c₁ k) + p₂ y - p₂ y = 0`  (using `p₁∘c₁=0`).
  -- Since `c₂` is injective there is a unique preimage in `L`, defining the 2nd component.
  -- φ, together with the left-square identity, comes from `schanuel_phi_of_psi`: ψ maps
  -- `range topLeft = ker topRight` isomorphically onto `range botLeft = ker botRight`
  -- (since `botRight ∘ ψ = topRight`), and both `topLeft`, `botLeft` are injective, so
  -- `φ := botLeft⁻¹ ∘ ψ ∘ topLeft` is a well-defined iso with `botLeft ∘ φ = ψ ∘ topLeft`.
  obtain ⟨φ, hleftSq⟩ := schanuel_phi_of_psi c₁ c₂ p₁ p₂ ψ hc₁ hc₂ hex₁ hex₂ hrightSq
  -- ===================================================================
  -- STEP 5.  Assemble.
  -- ===================================================================
  exact ⟨φ, ψ, htop, hbot, hleftSq, hrightSq⟩

-- ===== merged from StacksDraft.Ch10.Sec109.Tag00O4 =====

/-!
## A module of infinite projective dimension over the dual numbers

Fix a field `k` and let `R = k[x]/(x^2)` be the ring of dual numbers over `k`. Write `ε ∈ R`
for the residue class of `x`, so `ε ^ 2 = 0` and `{1, ε}` is a `k`-basis of `R`; in
particular `ε ≠ 0`. Let `M = R/(ε)`, the quotient of `R` by the principal ideal generated by
`ε`, regarded as an `R`-module; as an `R`-module `M ≅ k` with `ε` acting as `0`.

An `A`-module `N` has finite projective dimension if there are `n : ℕ` and an exact sequence
`0 → P_n → P_{n-1} → ⋯ → P_1 → P_0 → N → 0` with every `P_i` a projective `A`-module; the
minimal such `n` is the projective dimension `pd_A(N)`, and `N` has finite projective
dimension exactly when `pd_A(N) < ∞`.

The `R`-module `M = R/(ε)` does *not* have finite projective dimension: there is no
finite-length resolution `0 → P_n → ⋯ → P_0 → M → 0` of `M` by projective `R`-modules
(Stacks tag 00O4).

`R = k[x]/(x^2)` is a local Artinian ring with maximal ideal `m = (ε)` and residue field
`R/m ≅ k ≅ M`. Multiplication by `ε` gives the periodic free, hence projective, resolution
`⋯ →[ε] R →[ε] R →[ε] R → M → 0`, which is the minimal free resolution of `M`. Being minimal
and never terminating, it shows `M` has no finite projective resolution; equivalently
`Ext^i_R(M, M) ≅ k ≠ 0` for all `i ≥ 0`, so `pd_R(M) = ∞`.
-/

@[expose] public section

open CategoryTheory

namespace DualNumberInfiniteProjDim

/- We use Mathlib's ring of dual numbers `DualNumber k`, with notation `k[ε]`, as the
ring `R = k[x]/(x^2)`.  Here `DualNumber.eps : k[ε]` is the residue class `ε`, and
`DualNumber.eps_pow_two` records `ε^2 = 0`. -/

variable (k : Type) [Field k]

/-- The `R`-module `M = R/(ε)`, the quotient by the principal ideal generated by `ε`. As an
`R`-module this is the residue field of the local ring `R`. -/
abbrev Mmod : Type := (DualNumber k) ⧸ Ideal.span {(DualNumber.eps : DualNumber k)}

/-- The module `M = R/(ε)` packaged as an object of the abelian category of `R`-modules. -/
noncomputable abbrev mObj : ModuleCat (DualNumber k) :=
  ModuleCat.of (DualNumber k) (Mmod k)

/-! ## Proof sketch

Overall strategy (dimension shifting / periodicity). We never compute `Ext`
explicitly; instead we use the abstract characterization of projective dimension
via `HasProjectiveDimensionLT` together with the dimension-shifting lemma
`CategoryTheory.ShortComplex.ShortExact.hasProjectiveDimensionLT_X₃_iff`.

Mathlib facts used:
* `HasProjectiveDimensionLE X n` is definitionally `HasProjectiveDimensionLT X (n+1)`.
* `instProjectiveOfHasProjectiveDimensionLTOfNatNat :`
  `[HasProjectiveDimensionLT X 1] → Projective X`
  and `hasProjectiveDimensionLT_X₃_iff : S.ShortExact → Projective S.X₂ →
      (HasProjectiveDimensionLT S.X₃ (n+2) ↔ HasProjectiveDimensionLT S.X₁ (n+1))`.
* `projectiveDimension_ne_top_iff : projectiveDimension X ≠ ⊤ ↔ ∃ n, HasProjectiveDimensionLE X n`.

The mathematical heart is the **2-periodic free resolution** of `M = R/(ε)`:
since `ann_R(ε) = (ε)`, multiplication by `ε` gives a short exact sequence
`0 → M → R → M → 0` (the kernel of the quotient `R → M` is `(ε)`, which is
isomorphic to `R/ann(ε) = R/(ε) = M`). Because the middle term `R` is free hence
projective, the dimension-shifting lemma turns this into a periodicity statement
`HasProjectiveDimensionLT M (n+2) ↔ HasProjectiveDimensionLT M (n+1)`. Starting
from the fact that `M` is **not projective** (so `¬ HasProjectiveDimensionLT M 1`),
induction gives `¬ HasProjectiveDimensionLT M (n+1)` for every `n`, i.e. `M` has
no finite projective dimension, so `projectiveDimension M = ⊤`.
-/

/-- `M = R/(ε)` is nontrivial, since `(ε)` is a proper ideal. -/
instance instNontrivialMmod : Nontrivial (Mmod k) :=
  Ideal.Quotient.nontrivial_iff.mpr DualNumber.isMaximal_span_singleton_eps.ne_top

/-- The class `ε` annihilates `M = R/(ε)`. -/
theorem eps_mem_annihilator :
    (DualNumber.eps : DualNumber k) ∈ Module.annihilator (DualNumber k) (Mmod k) := by
  rw [Module.mem_annihilator]
  intro m
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Ideal.mul_mem_right x _ (Ideal.mem_span_singleton_self _)

/-- `M = R/(ε)` is not a projective `R`-module. -/
theorem mObj_not_projective : ¬ Projective (mObj k) := by
  intro hproj
  have : Module.Projective (DualNumber k) (Mmod k) :=
    (IsProjective.iff_projective (Mmod k)).mpr hproj
  have : Module.Free (DualNumber k) (Mmod k) := Module.free_of_flat_of_isLocalRing
  have hann : Module.annihilator (DualNumber k) (Mmod k) = ⊥ :=
    Module.annihilator_eq_bot.mpr inferInstance
  have hmem := eps_mem_annihilator k
  rw [hann, Ideal.mem_bot] at hmem
  simpa using congrArg TrivSqZeroExt.snd hmem

/-- In the dual numbers, `r * ε = 0` exactly when `r ∈ (ε)`: the annihilator of `ε` is `(ε)`. -/
theorem mul_eps_eq_zero_iff_mem_span (r : DualNumber k) :
    r * DualNumber.eps = 0 ↔ r ∈ Ideal.span {(DualNumber.eps : DualNumber k)} := by
  rw [Ideal.mem_span_singleton']
  constructor
  · intro h
    have hfst : r.fst = 0 := by
      simpa [TrivSqZeroExt.snd_mul] using congrArg TrivSqZeroExt.snd h
    refine ⟨TrivSqZeroExt.inl r.snd, TrivSqZeroExt.ext ?_ ?_⟩
    · simp [TrivSqZeroExt.fst_mul, hfst]
    · simp [TrivSqZeroExt.snd_mul]
  · rintro ⟨s, rfl⟩
    simp [mul_assoc]

/-- The periodic short exact sequence `0 → M → R → M → 0` realizing the syzygy `Ω M ≅ M`.
The second map is the quotient `R ↠ R/(ε) = M`, with kernel `(ε)`, and the first identifies
`M ≅ (ε)` via `x̄ ↦ ε·x`, which is well defined and injective because `ann_R(ε) = (ε)`, i.e.
`ε·x = 0 ↔ x ∈ (ε)`. It is packaged as a `ShortComplex` whose middle term is the free module
`R`, so `Projective S.X₂`, together with `S.X₁ ≅ M` and `S.X₃ ≅ M`. -/
theorem exists_periodic_shortExact :
    ∃ S : ShortComplex (ModuleCat (DualNumber k)),
      S.ShortExact ∧ Projective S.X₂ ∧
        Nonempty (S.X₁ ≅ mObj k) ∧ Nonempty (S.X₃ ≅ mObj k) := by
  have hle : Ideal.span {(DualNumber.eps : DualNumber k)} ≤
      LinearMap.ker (LinearMap.toSpanSingleton (DualNumber k) (DualNumber k) DualNumber.eps) := by
    rw [Ideal.span_le]
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst hx
    simp [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, smul_eq_mul, DualNumber.eps_mul_eps]
  let fLin : Mmod k →ₗ[DualNumber k] DualNumber k :=
    Submodule.liftQ _ (LinearMap.toSpanSingleton (DualNumber k) (DualNumber k) DualNumber.eps) hle
  let gLin : DualNumber k →ₗ[DualNumber k] Mmod k :=
    (Ideal.span {(DualNumber.eps : DualNumber k)}).mkQ
  let f : mObj k ⟶ ModuleCat.of (DualNumber k) (DualNumber k) := ModuleCat.ofHom fLin
  let g : ModuleCat.of (DualNumber k) (DualNumber k) ⟶ mObj k := ModuleCat.ofHom gLin
  have hf_eval : ∀ x : DualNumber k,
      fLin (Submodule.Quotient.mk x) = x * DualNumber.eps := by
    intro x
    rw [show fLin = Submodule.liftQ _ _ hle from rfl, Submodule.liftQ_apply]
    simp [LinearMap.toSpanSingleton_apply, smul_eq_mul]
  have hrange : LinearMap.range fLin = Ideal.span {(DualNumber.eps : DualNumber k)} := by
    rw [show fLin = Submodule.liftQ _ _ hle from rfl, Submodule.range_liftQ,
      LinearMap.range_toSpanSingleton]
  have hker : LinearMap.ker gLin = Ideal.span {(DualNumber.eps : DualNumber k)} := by
    rw [show gLin = (Ideal.span {(DualNumber.eps : DualNumber k)}).mkQ from rfl, Submodule.ker_mkQ]
  have hfg : (ModuleCat.Hom.hom f).range ≤ (ModuleCat.Hom.hom g).ker := by
    change LinearMap.range fLin ≤ LinearMap.ker gLin
    rw [hrange, hker]
  let S := ShortComplex.moduleCatMkOfKerLERange f g hfg
  refine ⟨S, ?_, ?_, ?_, ?_⟩
  · -- ShortExact
    have hSf : S.f = f := ShortComplex.moduleCatMkOfKerLERange_f f g hfg
    have hSg : S.g = g := ShortComplex.moduleCatMkOfKerLERange_g f g hfg
    apply ModuleCat.shortComplex_shortExact
    · -- Exact
      rw [hSf, hSg]
      change Function.Exact (fLin : Mmod k → DualNumber k) (gLin : DualNumber k → Mmod k)
      rw [LinearMap.exact_iff, hker, hrange]
    · -- Injective f
      rw [hSf]
      change Function.Injective fLin
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro m hm
      simp only [LinearMap.mem_ker] at hm
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ m
      rw [hf_eval] at hm
      simp only [Submodule.mem_bot]
      rw [Submodule.Quotient.mk_eq_zero]
      exact (mul_eps_eq_zero_iff_mem_span k x).mp hm
    · -- Surjective g
      rw [hSg]
      change Function.Surjective gLin
      exact Submodule.Quotient.mk_surjective _
  · -- Projective S.X₂
    have hX₂ : S.X₂ = ModuleCat.of (DualNumber k) (DualNumber k) :=
      ShortComplex.moduleCatMkOfKerLERange_X₂ f g hfg
    rw [hX₂]
    exact ModuleCat.projective_of_free (Module.Free.chooseBasis (DualNumber k) (DualNumber k))
  · -- X₁ ≅ mObj k
    exact ⟨eqToIso (ShortComplex.moduleCatMkOfKerLERange_X₁ f g hfg)⟩
  · -- X₃ ≅ mObj k
    exact ⟨eqToIso (ShortComplex.moduleCatMkOfKerLERange_X₃ f g hfg)⟩

/-- Periodicity of projective dimension along the periodic short exact sequence:
`HasProjectiveDimensionLT M (n+2) ↔ HasProjectiveDimensionLT M (n+1)`. -/
theorem hasProjectiveDimensionLT_add_two_iff (n : ℕ) :
    HasProjectiveDimensionLT (mObj k) (n + 2) ↔ HasProjectiveDimensionLT (mObj k) (n + 1) := by
  obtain ⟨S, hSE, hproj, ⟨e₁⟩, ⟨e₃⟩⟩ := exists_periodic_shortExact k
  exact (hasProjectiveDimensionLT_congr e₃.symm _).trans
    ((hSE.hasProjectiveDimensionLT_X₃_iff n hproj).trans (hasProjectiveDimensionLT_congr e₁ _))

/-- `M` does not have projective dimension `< n + 1` for any `n`. -/
theorem not_hasProjectiveDimensionLT_succ (n : ℕ) :
    ¬ HasProjectiveDimensionLT (mObj k) (n + 1) := by
  induction n with
  | zero => exact fun _ ↦ mObj_not_projective k (instProjectiveOfHasProjectiveDimensionLTOfNatNat _)
  | succ m ih => exact fun h ↦ ih ((hasProjectiveDimensionLT_add_two_iff k m).mp h)

/-- There is no `n : ℕ` for which `M` has projective dimension `≤ n`, i.e. no finite-length
projective resolution `0 → P_n → ⋯ → P_0 → M → 0`. -/
theorem not_exists_hasProjectiveDimensionLE : ¬ ∃ n : ℕ, HasProjectiveDimensionLE (mObj k) n := by
  rintro ⟨n, hn⟩
  exact not_hasProjectiveDimensionLT_succ k n hn

/-- The projective dimension of `M` over `R = k[x]/(x^2)` is infinite, i.e. `⊤`, so `M` does
not have finite projective dimension. -/
theorem projectiveDimension_eq_top : projectiveDimension (mObj k) = ⊤ := by
  by_contra h
  exact not_exists_hasProjectiveDimensionLE k ((projectiveDimension_ne_top_iff (mObj k)).mp h)

end DualNumberInfiniteProjDim

-- ===== merged from StacksDraft.Ch10.Sec109.Tag00O5 =====

/-!
## The leftmost syzygy of a truncated projective resolution

Let `R` be a ring and let `M` be an `R`-module of finite projective dimension `d`, i.e.
`d = pd_R(M)` is a nonnegative integer. Suppose

  `F_e → F_{e-1} → ⋯ → F_1 → F_0 → M → 0`

is an exact sequence of `R`-modules in which each `F_i` (for `0 ≤ i ≤ e`) is projective, and
suppose `e ≥ d - 1`. Then:

1. if `e ≥ 1`, the kernel `Ker(F_e → F_{e-1})` is a projective `R`-module;
2. if `e = 0` — so the hypothesis forces `d ≤ 1` and the sequence is `F_0 → M → 0` — the
   kernel `Ker(F_0 → M)` is a projective `R`-module.

Equivalently, the leftmost syzygy of the given truncated projective resolution is
projective.

### The encoding

The ambient category is the abelian category `ModuleCat R`. Mathlib's
`CategoryTheory.projectiveDimension : C → WithBot ℕ∞` is the minimal length of a finite
projective resolution, taking the value `(d : WithBot ℕ∞)` exactly when `M` has finite
projective dimension `d`.

The truncated sequence `F_e → ⋯ → F_0 → M → 0` is a
`CategoryTheory.ComposableArrows (ModuleCat R) (e + 2)`, a functor on the poset
`0 ≤ 1 ≤ ⋯ ≤ e + 2`, with `F_{e-j}` at position `j` for `0 ≤ j ≤ e` (so `F_e` sits at
position `0` and `F_0` at position `e`), `M` at position `e + 1`, and the zero object at
position `e + 2`.

`ComposableArrows.Exact` asserts exactness at every internal object, i.e. at positions
`1, …, e + 1`. That yields exactness at each `F_i` for `0 ≤ i ≤ e - 1` and surjectivity of
`F_0 → M`, the latter being exactness at `M`, whose outgoing map is `M → 0`. Exactness is
deliberately *not* imposed at the leftmost object `F_e` at position `0`: the map
`F_e → F_{e-1}` need not be injective, and its kernel is the object of interest.

The leftmost differential is `S.map' 0 1`, which is `F_e → F_{e-1}` when `e ≥ 1` and
`F_0 → M` when `e = 0`. So `Limits.kernel (S.map' 0 1)` is the leftmost syzygy in both
cases, and `Projective (Limits.kernel (S.map' 0 1))` unifies the two conclusions. Finally,
the hypothesis `e ≥ d - 1` with truncated subtraction on `ℕ` is `d ≤ e + 1`, the form used
below.
-/

@[expose] public section


open CategoryTheory

variable {R : Type*} [Ring R]

/-!
## Proof strategy (Ext / dimension–shift formulation)

The informal Stacks proof uses Schanuel's Lemma and induction on `d = pd_R(M)`.
Mathlib already packages the relevant homological algebra through the *projective
dimension shift* lemma

  `CategoryTheory.ShortComplex.ShortExact.hasProjectiveDimensionLT_X₃_iff`
    : `S.ShortExact → Projective S.X₂ →
        (HasProjectiveDimensionLT S.X₃ (n + 2) ↔ HasProjectiveDimensionLT S.X₁ (n + 1))`

(this is the Ext long-exact-sequence dimension shift; it is exactly the categorical
content of "splitting + Schanuel + induction"). Combined with

  `projective_iff_hasProjectiveDimensionLE_zero : Projective X ↔ HasProjectiveDimensionLE X 0`
  (and `HasProjectiveDimensionLE X 0 = HasProjectiveDimensionLT X 1`),

this gives a cleaner induction on the *length* `e` of the truncated resolution,
peeling one projective term off the right end at a time.

Concretely, write `Kᵢ := Ker(F_i → F_{i-1})` (the leftmost differential being
`S.map' 0 1`). For each internal spot we have a short exact sequence

  `0 → Ker(S.map' j (j+1)) → F_{·} → Ker(S.map' (j+1) (j+2)) → 0`           (★)

obtained from exactness at position `j+1`: the image of the differential out of
position `j` equals the kernel of the differential out of position `j+1`, and the
first-isomorphism theorem identifies the coimage with that kernel. The middle term
is the projective `F` at position `j`. Applying the dimension-shift lemma to (★)
relates `pd(Ker(S.map' j (j+1)))` to `pd(Ker(S.map' (j+1) (j+2)))`, dropping the
dimension bound by one each step. Iterating from `j = 0` down through `j = e`
(the last syzygy being `Ker(F_0 → M)`, whose quotient is `M` itself) reduces the
claim `HasProjectiveDimensionLT (Ker(S.map' 0 1)) 1` to
`HasProjectiveDimensionLT M (e + 2)`, which holds because
`pd_R(M) = d ≤ e + 1`.

The induction is carried out by `syzygy_pd_shift` below, on the length parameter,
with the dimension bound `m` left free so the inductive hypothesis can be applied
to the truncation `S.δ₀` (which drops `F_e` and is again exact, by
`ComposableArrows.Exact.δ₀`).
-/

-- needed: `syzygy_leftmost_shortExact`'s `convert`/`Limits.kernel.lift` steps leave unsolved
-- goals unless the `ModuleCat R` kernel instances are unfolded at `default` transparency
set_option backward.isDefEq.respectTransparency false in
/-- **(Categorical bookkeeping lemma.)** From exactness of `S` at the internal
position `j + 1` (and the zero object at the very end making `F_0 → M` an
epimorphism) one extracts the short exact sequence

  `0 → Ker(S.map' j (j+1)) → S.obj j → Ker(S.map' (j+1) (j+2)) → 0`,

whose middle term is the (projective) object `S.obj j` at position `j`, whose
left term is the kernel of the leftmost remaining differential, and whose right
term is the next syzygy `Ker(S.map' (j+1) (j+2))`.

This packages, as a `ShortComplex.ShortExact`, the standard fact
`Im(S.map' j (j+1)) = Ker(S.map' (j+1) (j+2))` (exactness at `j+1`) together with
the first isomorphism theorem `S.obj j / Ker(S.map' j (j+1)) ≅ Im(S.map' j (j+1))`.
We only need the case `j = 0` of the chain (the rest are obtained by passing to the
truncation `S.δ₀`), so the statement is specialised to the leftmost spot.

The short complex is
`(Limits.kernel (S.map' 0 1)) → S.obj 0 → (Limits.kernel (S.map' 1 2))`, whose first map is
`Limits.kernel.ι (S.map' 0 1)` and whose second map is the factorisation of `S.map' 0 1`
through `Limits.kernel (S.map' 1 2)`; it lands there because `S.map' 0 1 ≫ S.map' 1 2 = 0`,
i.e. `S.IsComplex`. Left exactness — `X₁ → X₂` mono — is `Limits.kernel.ι` being mono, while
right exactness — `X₂ → X₃` epi — and exactness in the middle come from `S.Exact` at
position `1` together with the identification of `Ker(S.map' 1 2)` with the image of
`S.map' 0 1`. -/
theorem syzygy_leftmost_shortExact (n : ℕ)
    (S : ComposableArrows (ModuleCat R) (n + 2))
    (hexact : S.Exact) :
    ∃ (f : (Limits.kernel (S.map' 0 1) : ModuleCat R) ⟶ S.obj ⟨0, by omega⟩)
      (g : S.obj ⟨0, by omega⟩ ⟶ (Limits.kernel (S.map' 1 2) : ModuleCat R))
      (w : f ≫ g = 0),
      (ShortComplex.mk f g w).ShortExact := by
  -- Build `f = kernel.ι`, `g = ` factorisation of `S.map' 0 1` through the next
  -- kernel; show short-exactness from `S.Exact` at position 1 and `hzero`.
  have hic : S.IsComplex := hexact.toIsComplex
  have h : S.map' 0 1 ≫ S.map' 1 2 = 0 := hic.zero 0 (by omega)
  refine ⟨Limits.kernel.ι (S.map' 0 1), Limits.kernel.lift (S.map' 1 2) (S.map' 0 1) h, ?_, ?_⟩
  · rw [← cancel_mono (Limits.kernel.ι (S.map' 1 2))]
    simp [Limits.kernel.condition]
  · have hexact1 := hexact.exact 0 (by omega)
    have hepi : Epi (Limits.kernel.lift (S.map' 1 2) (S.map' 0 1) h) := by
      have := (S.sc hic 0 (by omega)).exact_iff_epi_kernel_lift.mp hexact1
      convert this using 2
    refine ShortComplex.ShortExact.mk ?_
    rw [ShortComplex.moduleCat_exact_iff]
    intro x₂ hx
    have hx' : (ModuleCat.Hom.hom (Limits.kernel.lift (S.map' 1 2) (S.map' 0 1) h)) x₂ = 0 := hx
    have hmap : (ModuleCat.Hom.hom (S.map' 0 1)) x₂ = 0 := by
      have heq := ConcreteCategory.congr_hom
        (Limits.kernel.lift_ι (S.map' 1 2) (S.map' 0 1) h) x₂
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at heq
      rw [← heq, hx', map_zero]
    refine ⟨(ModuleCat.kernelIsoKer (S.map' 0 1)).inv ⟨x₂, hmap⟩, ?_⟩
    have key := ModuleCat.kernelIsoKer_hom_ker_subtype (S.map' 0 1)
    have key2 := ConcreteCategory.congr_hom key
      ((ModuleCat.kernelIsoKer (S.map' 0 1)).inv ⟨x₂, hmap⟩)
    simp only [ModuleCat.hom_comp] at key2 ⊢
    rw [← key2]
    simp

/-- The leftmost syzygy has projective dimension `< m + 1` as soon as the next one has projective
dimension `< m + 2`, the object `S.obj 0` between them being projective. -/
private lemma hasProjectiveDimensionLT_kernel_map_zero_one {n : ℕ}
    (S : ComposableArrows (ModuleCat R) (n + 2)) (hexact : S.Exact)
    (h₀ : Projective (S.obj ⟨0, by omega⟩)) (m : ℕ)
    (h : HasProjectiveDimensionLT (Limits.kernel (S.map' 1 2)) (m + 2)) :
    HasProjectiveDimensionLT (Limits.kernel (S.map' 0 1)) (m + 1) := by
  obtain ⟨f, g, w, hSE⟩ := syzygy_leftmost_shortExact n S hexact
  exact (hSE.hasProjectiveDimensionLT_X₃_iff m h₀).1 h

/-- **(Core induction, on the length `n`.)** For a truncated exact sequence of
length `n + 2` with the leftmost object excepted, all interior objects projective,
the leftmost syzygy `Ker(S.map' 0 1)` has projective dimension `< m + 1` whenever
the final object `M = S.obj ⟨n+1⟩` has projective dimension `< m + n + 2`.

Taking `m = 0` and `n = e` recovers
`HasProjectiveDimensionLT (Ker(S.map' 0 1)) 1`, i.e. `Projective (Ker(S.map' 0 1))`,
from `HasProjectiveDimensionLT M (e + 2)`.

The proof is by induction on `n`.
* `n = 0`: the only short exact sequence is `0 → Ker(S.map' 0 1) → F_0 → M → 0`
  (here `S.map' 1 2 : M → 0`, so `Ker(S.map' 1 2) = M`). Apply
  `ShortExact.hasProjectiveDimensionLT_X₃_iff` with this SES (`X₂ = F_0` projective)
  and index `n := m`: `HasProjectiveDimensionLT M (m + 2) ↔
  HasProjectiveDimensionLT (Ker(S.map' 0 1)) (m + 1)`. The hypothesis gives the LHS
  (`m + 0 + 2 = m + 2`).
* `n + 1`: use `syzygy_leftmost_shortExact` to get
  `0 → Ker(S.map' 0 1) → F → Ker(S.map' 1 2) → 0` with `F = S.obj 0` projective.
  Apply `ShortExact.hasProjectiveDimensionLT_X₃_iff` with index `n := m`:
  `HasProjectiveDimensionLT (Ker(S.map' 1 2)) (m + 2) ↔
   HasProjectiveDimensionLT (Ker(S.map' 0 1)) (m + 1)`.
  It remains to prove the LHS. Apply the inductive hypothesis to the truncation
  `S.δ₀ : ComposableArrows _ (n + 2)` (exact by `ComposableArrows.Exact.δ₀`, same
  zero object at the end, interior objects still projective), with bound `m + 1`:
  its leftmost differential is `(S.δ₀).map' 0 1 = S.map' 1 2`, and its final object
  is `M`, so the IH yields
  `HasProjectiveDimensionLT (Ker(S.map' 1 2)) ((m+1) + 1) = ... (m + 2)`
  from `HasProjectiveDimensionLT M ((m+1) + n + 2) = ... (m + (n+1) + 2)`, which is
  exactly the available hypothesis. (Identifying `(S.δ₀).map' 0 1` with `S.map' 1 2`
  and `(S.δ₀).obj last` with `S.obj last` are the `ComposableArrows`-bookkeeping
  facts; they hold definitionally / by `ComposableArrows.δ₀_map`-type lemmas.) -/
@[ega "0 17.2.1" "Necessity"]
theorem syzygy_pd_shift (n : ℕ)
    (S : ComposableArrows (ModuleCat R) (n + 2))
    (hexact : S.Exact)
    (hzero : Limits.IsZero (S.obj (Fin.last (n + 2))))
    (hproj : ∀ i : Fin (n + 1), Projective (S.obj i.castSucc.castSucc))
    (m : ℕ)
    (hM : HasProjectiveDimensionLT (S.obj ⟨n + 1, Nat.lt_succ_of_lt (Nat.lt_succ_self (n + 1))⟩) (m
        + n + 2)) :
    HasProjectiveDimensionLT (Limits.kernel (S.map' 0 1)) (m + 1) := by
  induction n generalizing m with
  | zero =>
    refine hasProjectiveDimensionLT_kernel_map_zero_one S hexact (hproj 0) m ?_
    -- `S.map' 1 2 : S.obj 1 → S.obj 2`, and `S.obj 2` is the zero object, so the
    -- map is zero and `Ker(S.map' 1 2) ≅ S.obj 1 = M`.
    have hz : S.map' 1 2 = 0 := by
      have : Limits.IsZero (S.obj (⟨2, by omega⟩ : Fin 3)) := hzero
      exact this.eq_of_tgt _ _
    have e : Limits.kernel (S.map' 1 2) ≅ S.obj (⟨1, by omega⟩ : Fin 3) := by
      rw [hz]; exact Limits.kernelZeroIsoSource
    have : HasProjectiveDimensionLT (S.obj (⟨1, by omega⟩ : Fin 3)) (m + 2) := hM
    exact hasProjectiveDimensionLT_of_iso e.symm (m + 2)
  | succ n ih =>
    refine hasProjectiveDimensionLT_kernel_map_zero_one S hexact (hproj 0) m ?_
    -- Apply the inductive hypothesis to the truncation `S.δ₀` with bound `m + 1`.
    -- Note `S.δ₀.map' 0 1 = S.map' 1 2` and `S.δ₀.obj j = S.obj j.succ`, all by `rfl`.
    have hexact' : (S.δ₀).Exact := hexact.δ₀
    have hzero' : Limits.IsZero ((S.δ₀).obj (Fin.last (n + 2))) := hzero
    have hproj' : ∀ i : Fin (n + 1), Projective ((S.δ₀).obj i.castSucc.castSucc) := by
      intro i
      have h := hproj i.succ
      have e : (i.castSucc.castSucc : Fin (n + 1 + 2)).succ = i.succ.castSucc.castSucc := by
        ext; simp [Fin.succ, Fin.castSucc, Fin.castAdd, Fin.castLE]
      change Projective (S.obj (i.castSucc.castSucc).succ)
      rw [e]; exact h
    have hM' : HasProjectiveDimensionLT ((S.δ₀).obj ⟨n + 1, Nat.lt_succ_of_lt (Nat.lt_succ_self (n
        + 1))⟩) ((m + 1) + n + 2) := by
      change HasProjectiveDimensionLT (S.obj ⟨n + 1 + 1, Nat.lt_succ_of_lt (Nat.lt_succ_self (n + 1
          + 1))⟩) ((m + 1) + n + 2)
      convert hM using 2
      omega
    have ihres := ih (S.δ₀) hexact' hzero' hproj' (m + 1) hM'
    -- `ihres : HasProjectiveDimensionLT (Limits.kernel (S.δ₀.map' 0 1)) ((m+1)+1)`,
    -- and `S.δ₀.map' 0 1 = S.map' 1 2` (rfl), `(m+1)+1 = m+2`.
    have heq : Limits.kernel ((S.δ₀).map' 0 1) = Limits.kernel (S.map' 1 2) := rfl
    rw [heq] at ihres
    exact ihres

/-- **Stacks Tag 00O5 / Lemma 10.109.3.** Let `M` have projective dimension `d` and let
`F_e → ⋯ → F_0 → M → 0` be exact with every `F_i` projective and `d ≤ e + 1`. Then the
leftmost syzygy `Ker(F_e → F_{e-1})`, or `Ker(F_0 → M)` when `e = 0`, is projective. -/
@[stacks 00O5, ega "0 17.2.1" "Necessity"]
theorem pd_syzygy_projective (d e : ℕ)
    -- the truncated sequence `F_e → ⋯ → F_0 → M → 0`
    (S : ComposableArrows (ModuleCat R) (e + 2))
    -- `M`, the object at position `e + 1`, has projective dimension `d`
    (hpd : projectiveDimension (S.obj ⟨e + 1, by omega⟩) = (d : WithBot ℕ∞))
    -- the hypothesis `e ≥ d - 1`, equivalently `d ≤ e + 1`
    (hde : d ≤ e + 1)
    -- exactness at every internal object (in particular `F_0 → M` is surjective);
    -- note exactness is NOT imposed at the leftmost object `F_e`
    (hexact : S.Exact)
    -- the rightmost object (position `e + 2`) is the zero module
    (hzero : Limits.IsZero (S.obj (Fin.last (e + 2))))
    -- each `F_i` (positions `0, …, e`) is projective
    (hproj : ∀ i : Fin (e + 1), Projective (S.obj i.castSucc.castSucc)) :
    -- the leftmost syzygy `Ker(F_e → F_{e-1})` (or `Ker(F_0 → M)` when `e = 0`)
    -- is projective
    Projective (Limits.kernel (S.map' 0 1)) := by
  -- Step 1: from `pd_R(M) = d` and `d ≤ e + 1`, get `HasProjectiveDimensionLT M (e + 2)`.
  have hM : HasProjectiveDimensionLT (S.obj ⟨e + 1, by omega⟩) (e + 2) := by
    have hle : HasProjectiveDimensionLE (S.obj ⟨e + 1, by omega⟩) (e + 1) := by
      rw [← projectiveDimension_le_iff, hpd]; exact_mod_cast hde
    -- `HasProjectiveDimensionLE X (e+1)` is definitionally `HasProjectiveDimensionLT X (e+2)`.
    exact hle
  -- Step 2: the core dimension–shift induction with `m = 0` gives
  -- `HasProjectiveDimensionLT (Ker(S.map' 0 1)) 1`.
  have hker : HasProjectiveDimensionLT (Limits.kernel (S.map' 0 1)) 1 := by
    have := syzygy_pd_shift e S hexact hzero hproj 0 (by simpa using hM)
    simpa using this
  -- Step 3: `HasProjectiveDimensionLT X 1 ↔ HasProjectiveDimensionLE X 0 ↔ Projective X`.
  rw [projective_iff_hasProjectiveDimensionLE_zero]
  exact hker

-- ===== merged from StacksDraft.Ch10.Sec109.Tag00O8 =====

/-!
## Localization preserves bounds on projective and global dimension

Throughout, `R` is a commutative ring, `S ⊆ R` is a multiplicative subset — a submonoid of
the multiplicative monoid of `R` — and `S⁻¹R` is the localization of `R` at `S`. For an
`R`-module `M`, `S⁻¹M` is the localization of `M` at `S`, naturally an `S⁻¹R`-module.

A module has *projective dimension `≤ n`* when it admits a projective resolution of length
`≤ n`; equivalently, and this is the formulation adopted here to match Mathlib's
`CategoryTheory.HasProjectiveDimensionLT`, when `Extⁱ(N, -) = 0` for all `i > n`. Concretely,
an `A`-module `N` has projective dimension `≤ n` iff
`HasProjectiveDimensionLT (ModuleCat.of A N) (n + 1)`. A ring has *global dimension `≤ n`*
when every module has projective dimension `≤ n`. The bound `n` ranges over `ℕ`, and `≤ n`
asserts that the dimension is bounded by `n`, not that it equals `n`.

The two statements (Stacks tag 00O8, Lemma 10.109.13) are:

1. if `M` has projective dimension `≤ n` as an `R`-module, then `S⁻¹M` has projective
   dimension `≤ n` as an `S⁻¹R`-module;
2. if `R` has global dimension `≤ n`, then `S⁻¹R` has global dimension `≤ n`.

Exactness of localization (Stacks 00CS) is `LocalizedModule.map_exact`.
-/

@[expose] public section

open CategoryTheory


/-- An `A`-module `N` has *projective dimension `≤ n`* iff `Extⁱ(N, -) = 0` for
all `i > n`. In Mathlib terms this is `HasProjectiveDimensionLT` at level
`n + 1`, applied to the object `ModuleCat.of A N`. -/
abbrev ModuleProjectiveDimensionLE (A : Type u) [Ring A]
    (N : Type u) [AddCommGroup N] [Module A N] (n : ℕ) : Prop :=
  HasProjectiveDimensionLT (ModuleCat.of A N) (n + 1)

/-- A ring `A` has *global dimension `≤ n`* iff every `A`-module has projective
dimension `≤ n`, i.e. `HasProjectiveDimensionLT X (n + 1)` for every object `X`
of `ModuleCat A`. -/
@[ega "0 17.2.8"]
abbrev RingGlobalDimensionLE (A : Type u) [Ring A] (n : ℕ) : Prop :=
  ∀ X : ModuleCat.{u} A, HasProjectiveDimensionLT X (n + 1)

/-!
## The argument for Statement 1

Statement 1 is proved by **induction on `n`**, using **dimension shifting** along a short
exact sequence, rather than transporting a whole finite projective resolution object, which
is heavyweight in Lean.

Recall `ModuleProjectiveDimensionLE A N n = HasProjectiveDimensionLT (ModuleCat.of A N) (n+1)`
and `HasProjectiveDimensionLE X n = HasProjectiveDimensionLT X (n+1)` (definitionally,
`HasProjectiveDimensionLE` is an `abbrev`).

* **Base case `n = 0`.** `pd_R M ≤ 0` means `M` is projective over `R`
  (`projective_iff_hasProjectiveDimensionLT_one`, bridged to `Module.Projective`
  via `IsProjective.iff_projective`, with `Small.{u} R` discharged by
  `instSmallSelf`). The localization of a projective module is projective
  (`instProjectiveLocalizationLocalizedModule`), so `S⁻¹M` is projective over
  `S⁻¹R`, hence `pd_{S⁻¹R}(S⁻¹M) ≤ 0`.

* **Inductive step `n → n+1`.** Suppose the claim holds for `n` (for ALL R-modules
  — the induction is over `n` with `M` universally quantified). Let `M` have
  `pd_R M ≤ n+1`. Choose a projective presentation
  `0 → K → P → M → 0` over `R` (using `EnoughProjectives (ModuleCat R)`:
  `P = Projective.over (ModuleCat.of R M)`, `π = Projective.π _`, `K = kernel π`).
  This is a short exact sequence `sc : ShortComplex.ShortExact` in `ModuleCat R`
  with `sc.X₂ = P` projective. Dimension shifting down via
  `ShortComplex.ShortExact.hasProjectiveDimensionLT_X₁ sc (n+1) h₂ h₃`:
  here `h₂ : HasProjectiveDimensionLT P (n+1)` (P projective gives the instance
  `HasProjectiveDimensionLT P 1`, raised to `n+1` by `hasProjectiveDimensionLT_of_ge`
  / the `n+k` instance) and `h₃ : HasProjectiveDimensionLT M (n+2)` (= `pd M ≤ n+1`,
  which is `hM`); the lemma yields `HasProjectiveDimensionLT K (n+1)`, i.e.
  `pd_R K ≤ n`.  (Alternatively the `_X₃_iff` form with `Projective P`.)

  Apply the induction hypothesis to `K`: `pd_{S⁻¹R}(S⁻¹K) ≤ n`.

  Localize the SES.  By `LocalizedModule.map_exact`, the localized maps
  `S⁻¹K → S⁻¹P → S⁻¹M` form an exact sequence, with `S⁻¹K → S⁻¹P` injective
  (`LocalizedModule.map_injective`) and `S⁻¹P → S⁻¹M` surjective
  (`LocalizedModule.map_surjective`); package this as
  `scLoc : ShortComplex.ShortExact` in `ModuleCat (S⁻¹R)`.  Here `S⁻¹P` is
  projective over `S⁻¹R` (`instProjectiveLocalizationLocalizedModule`).

  Dimension shifting up
  (`ShortComplex.ShortExact.hasProjectiveDimensionLT_X₃ scLoc n h₁ h₂`: from
  `h₁ : HasProjectiveDimensionLT (scLoc.X₁ = S⁻¹K) n` (= IH output `pd(S⁻¹K) ≤ n`)
  and `h₂ : HasProjectiveDimensionLT (scLoc.X₂ = S⁻¹P) (n+1)` (`S⁻¹P` projective,
  instance + `hasProjectiveDimensionLT_of_ge`), conclude
  `HasProjectiveDimensionLT (scLoc.X₃ = S⁻¹M) (n+1)`, i.e. `pd(S⁻¹M) ≤ n+1`).

The construction of the localized short exact sequence `scLoc` in `ModuleCat (S⁻¹R)` from the
`R`-module sequence is isolated as `localizedModule_shortExact` below.
-/

/-- **Key sub-lemma (localizing a short exact sequence).**
Given a short exact sequence of `R`-modules `0 → K → P → M → 0` presented as
linear maps `g : K →ₗ[R] P`, `h : P →ₗ[R] M` with `g` injective, `h` surjective,
and `Function.Exact g h`, the localized maps `S⁻¹g`, `S⁻¹h` (i.e.
`LocalizedModule.map S g`, `LocalizedModule.map S h`) form a short exact sequence
`0 → S⁻¹K → S⁻¹P → S⁻¹M → 0` of `S⁻¹R`-modules, packaged as a
`ShortComplex.ShortExact` in `ModuleCat (Localization S)`.

Exactness of the localized sequence is
`LocalizedModule.map_exact S g h hexact` (Stacks 00CS). Injectivity of `S⁻¹g` is
`LocalizedModule.map_injective S g hg_inj`; surjectivity of `S⁻¹h` is
`LocalizedModule.map_surjective S h hh_surj`. To build the `ShortComplex` in
`ModuleCat (Localization S)`: take `X₁ = ModuleCat.of _ (LocalizedModule S K)`,
`X₂ = ... (LocalizedModule S P)`, `X₃ = ... (LocalizedModule S M)`, with morphisms
the `Localization S`-linear maps `LocalizedModule.map S g`, `LocalizedModule.map S h`
(these ARE `Localization S`-linear by the `LocalizedModule.map` API, which targets
`→ₗ[Localization S]`); turn these into `ModuleCat (Localization S)` morphisms with
`ModuleCat.ofHom`. The composition is zero because the originals compose to zero
(`hexact.comp_eq_zero` / functoriality of `LocalizedModule.map`). Build the
`ShortComplex` via `ShortComplex.mk f g (w : f ≫ g = 0)`, then provide
`ShortExact` as the structure literal `{ exact := hex, mono_f := hm, epi_g := he }`
where: `hex : sc.Exact` comes from `ShortComplex.moduleCat_exact_iff` fed by
`LocalizedModule.map_exact S g h hexact`; `hm : Mono sc.f` from
`ModuleCat.mono_iff_injective` + `LocalizedModule.map_injective S g hg`; and
`he : Epi sc.g` from `ModuleCat.epi_iff_surjective` +
`LocalizedModule.map_surjective S h hh`. The three object equalities hold by `rfl`
since the objects are defined as the stated `ModuleCat.of … (LocalizedModule S …)`. -/
theorem localizedModule_shortExact
    (R : Type u) [CommRing R] (S : Submonoid R)
    {K P M : Type u} [AddCommGroup K] [Module R K]
    [AddCommGroup P] [Module R P] [AddCommGroup M] [Module R M]
    (g : K →ₗ[R] P) (h : P →ₗ[R] M)
    (hg : Function.Injective g) (hh : Function.Surjective h)
    (hexact : Function.Exact g h) :
    ∃ sc : ShortComplex (ModuleCat.{u} (Localization S)),
      sc.ShortExact ∧
      sc.X₁ = ModuleCat.of (Localization S) (LocalizedModule S K) ∧
      sc.X₂ = ModuleCat.of (Localization S) (LocalizedModule S P) ∧
      sc.X₃ = ModuleCat.of (Localization S) (LocalizedModule S M) := by
  let f : ModuleCat.of (Localization S) (LocalizedModule S K) ⟶
      ModuleCat.of (Localization S) (LocalizedModule S P) :=
    ModuleCat.ofHom (LocalizedModule.map S g)
  let f' : ModuleCat.of (Localization S) (LocalizedModule S P) ⟶
      ModuleCat.of (Localization S) (LocalizedModule S M) :=
    ModuleCat.ofHom (LocalizedModule.map S h)
  have hmap_exact : Function.Exact ⇑(LocalizedModule.map S g) ⇑(LocalizedModule.map S h) :=
    LocalizedModule.map_exact S g h hexact
  have hw : f ≫ f' = 0 := by
    ext x
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_zero,
      LinearMap.comp_apply, LinearMap.zero_apply, f, f']
    exact hmap_exact.apply_apply_eq_zero x
  let sc : ShortComplex (ModuleCat.{u} (Localization S)) := ShortComplex.mk f f' hw
  exact ⟨sc,
    { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr hmap_exact
      mono_f := (ModuleCat.mono_iff_injective _).mpr (LocalizedModule.map_injective S g hg)
      epi_g := (ModuleCat.epi_iff_surjective _).mpr (LocalizedModule.map_surjective S h hh) },
    rfl, rfl, rfl⟩

/-- **Inductive-step sub-lemma for Statement 1.**
Assuming the localization-pd bound for `n` and ALL `R`-modules (the induction
hypothesis), the bound holds for `n+1` and any `M` with `pd_R M ≤ n+1`.

Pick a projective presentation
`0 → K → P → M → 0` over `R` (`EnoughProjectives (ModuleCat R)`, valid since
`Small.{u} R`), dimension-shift down to `pd_R K ≤ n`
(`ShortComplex.ShortExact.hasProjectiveDimensionLT_X₁`), apply the IH to `K` to get
`pd_{S⁻¹R}(S⁻¹K) ≤ n`, localize the SES via `localizedModule_shortExact` to a SES
`0 → S⁻¹K → S⁻¹P → S⁻¹M → 0` with `S⁻¹P` projective
(`instProjectiveLocalizationLocalizedModule`), then dimension-shift up
(`ShortComplex.ShortExact.hasProjectiveDimensionLT_X₃`) to `pd_{S⁻¹R}(S⁻¹M) ≤ n+1`. -/
theorem projectiveDimension_localization_le_step
    (R : Type u) [CommRing R] (S : Submonoid R) (n : ℕ)
    (ih : ∀ (K : Type u) [AddCommGroup K] [Module R K],
      ModuleProjectiveDimensionLE R K n →
      ModuleProjectiveDimensionLE (Localization S) (LocalizedModule S K) n)
    (M : Type u) [AddCommGroup M] [Module R M]
    (hM : ModuleProjectiveDimensionLE R M (n + 1)) :
    ModuleProjectiveDimensionLE (Localization S) (LocalizedModule S M) (n + 1) := by
  -- Projective presentation 0 → K → P → M → 0 over R.
  let π : CategoryTheory.Projective.over (ModuleCat.of R M) ⟶ ModuleCat.of R M :=
    CategoryTheory.Projective.π (ModuleCat.of R M)
  let sc : ShortComplex (ModuleCat R) :=
    ShortComplex.mk (CategoryTheory.Limits.kernel.ι π) π (by simp)
  have hse : sc.ShortExact :=
    { exact := ShortComplex.exact_kernel π, mono_f := inferInstance, epi_g := inferInstance }
  have hK : HasProjectiveDimensionLT sc.X₁ (n + 1) := hse.hasProjectiveDimensionLT_X₁ (n + 1)
    (hasProjectiveDimensionLT_of_ge sc.X₂ 1 (n + 1) (by omega)) hM
  let g : (sc.X₁ : Type u) →ₗ[R] (sc.X₂ : Type u) := sc.f.hom
  let h : (sc.X₂ : Type u) →ₗ[R] (sc.X₃ : Type u) := sc.g.hom
  obtain ⟨scL, hscL, hX₁, hX₂, hX₃⟩ := localizedModule_shortExact R S g h
    ((ModuleCat.mono_iff_injective _).mp hse.mono_f) ((ModuleCat.epi_iff_surjective _).mp hse.epi_g)
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hse.exact)
  have hL1 : HasProjectiveDimensionLT scL.X₁ (n + 1) := hX₁ ▸ ih _ hK
  have : Projective scL.X₂ := hX₂ ▸ (IsProjective.iff_projective _).mp
    (inferInstance : Module.Projective (Localization S) (LocalizedModule S sc.X₂))
  have hLM := hscL.hasProjectiveDimensionLT_X₃ (n + 1) hL1
    (hasProjectiveDimensionLT_of_ge scL.X₂ 1 (n + 1 + 1) (by omega))
  rw [hX₃] at hLM
  exact hLM

/-- **Statement 1.** If `M` has projective dimension `≤ n` as an `R`-module, then
the localization `S⁻¹M` has projective dimension `≤ n` as an `S⁻¹R`-module.

Proof by induction on `n`: base case proved inline (projective localizes to
projective); inductive step is `projectiveDimension_localization_le_step`.  The
induction generalizes `M` so the hypothesis applies to the syzygy `K` at the next
level. -/
@[stacks 00O8 "(1)", ega "0 17.2.5" "partial", ega "IV 6.2.1" "(i), special case"]
theorem projectiveDimension_localization_le
    (R : Type u) [CommRing R] (S : Submonoid R)
    (M : Type u) [AddCommGroup M] [Module R M] (n : ℕ)
    (hM : ModuleProjectiveDimensionLE R M n) :
    ModuleProjectiveDimensionLE (Localization S) (LocalizedModule S M) n := by
  induction n generalizing M with
  | zero =>
    rw [ModuleProjectiveDimensionLE, ← projective_iff_hasProjectiveDimensionLT_one] at hM ⊢
    have : Module.Projective R M := (IsProjective.iff_projective _).mpr hM
    exact (IsProjective.iff_projective _).mp inferInstance
  | succ n ih => exact projectiveDimension_localization_le_step R S n (fun K _ _ hK => ih K hK) M hM

/-- **Statement 2.** If `R` has global dimension `≤ n`, then `S⁻¹R` has global
dimension `≤ n`.

This reduces to Statement 1. Let `X : ModuleCat (S⁻¹R)` be
arbitrary, with underlying type `M'`.  View `M'` as an `R`-module by restriction of
scalars along `algebraMap R (S⁻¹R)` (`Module.compHom`, giving `IsScalarTower
R (S⁻¹R) M'`).  Every `S⁻¹R`-module is its own localization:
`isLocalizedModule_id S M' (Localization S)` gives `IsLocalizedModule S
(LinearMap.id : M' →ₗ[R] M')`, whence `IsLocalizedModule.iso S LinearMap.id :
LocalizedModule S M' ≃ₗ[R] M'`, upgraded to a `Localization S`-linear equivalence by
`LinearEquiv.extendScalarsOfIsLocalization S (Localization S)`.  This linear
equivalence yields an isomorphism `e : ModuleCat.of (S⁻¹R) (LocalizedModule S M') ≅
X` in `ModuleCat (S⁻¹R)` (`LinearEquiv.toModuleIso`).  By `hR` (applied to
`ModuleCat.of R M'`), `M'` has `pd_R M' ≤ n`, i.e. `ModuleProjectiveDimensionLE R M' n`.
Statement 1 gives `ModuleProjectiveDimensionLE (S⁻¹R) (LocalizedModule S M') n`, i.e.
`HasProjectiveDimensionLT (ModuleCat.of (S⁻¹R) (LocalizedModule S M')) (n+1)`.
Transport across `e` with `hasProjectiveDimensionLT_of_iso` to obtain
`HasProjectiveDimensionLT X (n+1)`. -/
@[stacks 00O8 "(2)", ega "0 17.2.10" "partial"]
theorem globalDimension_localization_le
    (R : Type u) [CommRing R] (S : Submonoid R) (n : ℕ)
    (hR : RingGlobalDimensionLE R n) :
    RingGlobalDimensionLE (Localization S) n := by
  intro X
  let M' := (X : Type u)
  -- View `M'` as an `R`-module by restriction of scalars along `algebraMap R (Localization S)`.
  let : Module R M' := Module.compHom M' (algebraMap R (Localization S))
  have : IsScalarTower R (Localization S) M' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hLM : IsLocalizedModule S (LinearMap.id : M' →ₗ[R] M') :=
    isLocalizedModule_id S M' (Localization S)
  have : HasProjectiveDimensionLT (ModuleCat.of (Localization S) (LocalizedModule S M')) (n + 1) :=
    projectiveDimension_localization_le R S M' n (hR (ModuleCat.of R M'))
  exact hasProjectiveDimensionLT_of_iso (LinearEquiv.extendScalarsOfIsLocalization S
    (Localization S) (IsLocalizedModule.iso S (LinearMap.id : M' →ₗ[R] M'))).toModuleIso (n + 1)

/-! ### Stacks 065S

Stacks 065S — the three implications between the projective dimensions of the terms of a short
exact sequence — is Mathlib's
`CategoryTheory.ShortComplex.ShortExact.hasProjectiveDimensionLT_X₁`, `…_X₂` and `…_X₃`
(`HasProjectiveDimensionLE X n` being Mathlib's abbreviation for
`HasProjectiveDimensionLT X (n + 1)`).
-/

-- The former @[stacks 065S] theorems are the Mathlib theorems.
add_to_stacks 065S "(1)" CategoryTheory.ShortComplex.ShortExact.hasProjectiveDimensionLT_X₁
add_to_stacks 065S "(2)" CategoryTheory.ShortComplex.ShortExact.hasProjectiveDimensionLT_X₂
add_to_stacks 065S "(3)" CategoryTheory.ShortComplex.ShortExact.hasProjectiveDimensionLT_X₃

