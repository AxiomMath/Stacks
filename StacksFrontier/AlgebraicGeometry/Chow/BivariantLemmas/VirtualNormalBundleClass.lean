module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ProperPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundle
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.RelativeDimension
public import StacksCore.Tactic.StacksAttribute

/-!
# The bivariant class of a virtual normal bundle

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `i : Z ⟶ X` be a closed immersion and let `𝒩` be a virtual normal
bundle for `i` in the sense of Stacks 0FBQ. Write `p : N ⟶ Z` for the vector bundle
`N = Spec_Z(Sym(𝒩^∨))`, let `b : W ⟶ 𝐏¹_X` be the blowup of Stacks 0FBG in `∞(Z)` with
`C ∈ A⁰(W_∞ ⟶ X)` the class of Stacks 0F9J, let `j : C_ZX ⟶ W_∞` be the open immersion of
Stacks 0FBH and let `ι : C_ZX ⟶ N` be the closed immersion of Stacks 0637. The construction
preceding Stacks 0FBK sends `α ∈ A_k(X)` to the unique `β` with

  `ι_* j^* (C ∩ α) = p^* β`,

the uniqueness being Stacks 02TY, and Stacks 0FBK asserts that `α ↦ β` is a bivariant class
`c(Z ⟶ X, 𝒩)`, that it is compatible with base change as in Stacks 0FBJ, and that it lies in
`A^r(Z ⟶ X)` when `𝒩` has constant rank `r`.

What that construction is, as an identity between bivariant classes, is

  `p^* ∘ c(Z ⟶ X, 𝒩) = ι_* ∘ j^* ∘ C`,

and this file formalizes that relation for a virtual normal bundle of constant rank `r`, proves
that it determines the class, and builds the class: `Stacks.Chow.virtualNormalGysinClass` is an
element of `A^r(Z ⟶ X)` whose cap operation is the prescribed one. The class `ι_* ∘ j^* ∘ C` is
carried as `E` and the flat pullback `p^*` along the base change of the bundle projection is
carried as `π`; of the three naturality laws of Stacks 0B76 the proper-pushforward one is
proved and the other two are carried, in the idiom the library uses for its own first Chern
class. See the implementation notes.

## Main definitions

* `Stacks.Chow.bundleTestBaseChange` — the base change `N ×_X T ⟶ Z ×_X T` of the bundle
  projection `p : N ⟶ Z` along a test scheme `g : T ⟶ X`, the morphism whose flat pullback the
  carried family `π` is.
* `Stacks.Chow.VirtualNormalBundleProjection` — the geometric input of the construction: a
  virtual normal bundle of constant rank `r` for `i`, together with a flat morphism of relative
  dimension `r` standing for the projection of the vector bundle it defines.
* `Stacks.Chow.IsVirtualNormalGysinClass` — **Stacks 0FBK**, the characterizing relation
  `p^* ∘ c = ι_* ∘ j^* ∘ C` of the construction: on every test scheme, capping with `c` and then
  applying the flat pullback of the bundle projection is capping with `ι_* j^* C`.
* `Stacks.Chow.virtualNormalGysinCap` — the cap operation `α ↦ β` the construction prescribes,
  namely `(p^*)^{-1} ∘ (ι_* ∘ j^* ∘ C)`.
* `Stacks.Chow.PiProperNaturality` — Stacks 02RG for the base-change square of the bundle
  projection, the one input the proper-pushforward law needs beyond the laws of `E`.
* `Stacks.Chow.TransportFlatNaturality`, `Stacks.Chow.TransportGysinNaturality` — the flat and
  Gysin laws of Stacks 0B76 written for the prescribed cap operation, carried as hypotheses.
* `Stacks.Chow.virtualNormalGysinClass` — **Stacks 0FBK**, the class `c(Z ⟶ X, 𝒩) ∈ A^r(Z ⟶ X)`.

## Main results

* `Stacks.Chow.eq_of_isVirtualNormalGysinClass` — **Stacks 0FBK**: the relation pins the class
  down. Any two bivariant classes in `A^r(Z ⟶ X)` satisfying it are equal, so `c(Z ⟶ X, 𝒩)` is
  well defined.
* `Stacks.Chow.pi_virtualNormalGysinCap` — the prescribed cap operation satisfies the relation,
  so the relation is not vacuous as a condition on cap operations.
* `Stacks.Chow.isVirtualNormalGysinClass_iff_cap_eq` — a bivariant class satisfies the relation
  exactly when its cap operation is the prescribed one.
* `Stacks.Chow.isVirtualNormalGysinClass_virtualNormalGysinClass` — **Stacks 0FBK**: the
  constructed class satisfies the relation, so with the uniqueness above it *is* the class
  `c(Z ⟶ X, 𝒩)` of the construction and not merely some element of `A^r(Z ⟶ X)`.

## Implementation notes

### Why the construction is a division and not a composition

The source defines `c(Z ⟶ X, 𝒩)` by the relation `p^* ∘ c = ι_* ∘ j^* ∘ C` between composites
of bivariant classes. Composition of bivariant classes is *not* constructible in this
repository: `Stacks.Chow.IsBivariantClassComposition` records the characterizing property
of a composite but produces none, the Gysin naturality of Stacks 0B76 for the composite cap
operation being unproved. Writing the relation as a composition would therefore make it
unstatable.

So the relation is written on cap operations instead, where no composite is needed. On a test
scheme `g : T ⟶ X` the three cap operations involved are

  `c ∩ - : A_k(T) ⟶ A_{k-r}(Z ×_X T)`,  `E ∩ - : A_k(T) ⟶ A_{k-e}(N ×_X T)`,
  `π : A_{k-r}(Z ×_X T) ⟶ A_{k-e}(N ×_X T)`,

and the relation is the equality `π (c ∩ α) = E ∩ α`. This is the `Stacks.Chow` idiom for a
construction whose existence is out of reach, and it is the shape of
`Stacks.Chow.IsBivariantClassComposition`; as there, the uniqueness statement
`Stacks.Chow.eq_of_isVirtualNormalGysinClass` is the content that is independent of existence.

Note that no transport of degrees appears: the degrees `k - r` and `k - e` are those of the cap
operations themselves, so the relation is a homogeneous equality and not an `HEq`. That is the
reason for carrying `π` with its target degree written as `k - e` rather than as `(k - r) + r`.

### The absent inputs, and that none of them is the conclusion

* `E` is the bivariant class `ι_* ∘ j^* ∘ C` for `N ⟶ X`. Its three inputs are absent. The
  class `C` of Stacks 0F9J is not in this repository — "the relative projective line of Stacks
  02S5 with its two sections and its standard affine chart is not available in a form the
  bivariant machinery can consume", as
  `StacksFrontier.AlgebraicGeometry.Chow.Bivariant.SpecializationProperPushforward` records while
  carrying `C` as a hypothesis for the same reason; the blowup of Stacks 0FBG and the open
  immersion `j` of Stacks 0FBH are absent entirely; and `ι_*` is the proper pushforward of
  bivariant classes of Stacks 0EPK. So `E` is an arbitrary bivariant class of degree `e` for
  `N ⟶ X`. It is a class for `N ⟶ X`, not for `Z ⟶ X`, so it is not the conclusion.
* `π` is the flat pullback along `Stacks.Chow.bundleTestBaseChange`, the base change of the
  bundle projection. Its naturality is exactly the assertion that `p^*` is a bivariant class,
  which *is* proved in this repository — `Stacks.Chow.flatPullbackBivariantClass`, Stacks 0B78 —
  but at the pullback `N ×_Z (Z ×_X T)` rather than at `N ×_X T`, which the construction needs;
  the two are identified by `CategoryTheory.Limits.pullbackRightPullbackFstIso` and that
  identification is not carried out here. So `π` is an arbitrary family of additive maps of the
  displayed types. Being a family of maps between Chow groups, it says nothing about bivariance
  for `Z ⟶ X`.
* Injectivity, resp. bijectivity, of `π` is Stacks 02TY, flat pullback along a vector bundle
  projection being an isomorphism on Chow groups. In this repository that is proved only in rank
  zero, where the projection is an isomorphism
  (`Stacks.Chow.flatPullbackChow_bijective_of_isAffineSpaceBundle_zero`), and rank `≥ 1` is
  recorded there as unreachable. It is the hypothesis the source itself cites at this point. It
  is a statement about flat pullback on Chow groups and mentions no bivariant class.
* The projection `p : N ⟶ Z` is a field of `Stacks.Chow.VirtualNormalBundleProjection`, which
  asks of it only flatness and relative dimension the rank of `𝒩`. The vector bundle
  `Spec_Z(Sym(𝒩^∨))` itself exists here, as `AlgebraicGeometry.Scheme.Modules.vectorBundle`,
  but is not connected to the Chow development: neither flatness nor the relative dimension of
  `vectorBundleToBase` is available, so the bundle cannot be fed to
  `Stacks.Chow.flatPullbackChow` and the projection has to be axiomatized by the two properties
  of it that the construction uses.

None of these is the conclusion: none of them is a bivariant class for `Z ⟶ X`, and none asserts
that one exists. In particular bijectivity of `π` is asked of it as a map of *Chow* groups, on
each test scheme separately. Asking it of `π` as a map of *bivariant* groups would be the
conclusion in disguise, since surjectivity there plus `E` would hand over an element of
`A^r(Z ⟶ X)` with no naturality proved at all.

### The three laws of Stacks 0B76: one proved, two carried

The proper-pushforward law of `Stacks.Chow.virtualNormalGysinCap` is **proved**, in
`Stacks.Chow.virtualNormalGysinClass`. The argument is the source's "since both `ι_* ∘ j^* ∘ C`
and `p^*` are bivariant", carried out: apply the injectivity of `π`, rewrite the left side by the
characterizing relation, move `π` past the pushforward by `Stacks.Chow.PiProperNaturality`, and
what remains is the proper-pushforward law of `E` at the canonical base-change map
`Stacks.Chow.bivariantBaseChangeMap`, whose cartesian square and compatibility with the
projection are `Stacks.Chow.isPullback_bivariantBaseChangeMap` and
`Stacks.Chow.bivariantBaseChangeMap_comp_fst`. The descent of proper pushforward to Chow groups
at the `N`-side map, Stacks 02S2, is the standing hypothesis
`Stacks.Chow.ProperPushforwardDescends`, as it is for `Stacks.Chow.bivariantCompositeCap`.

The flat and Gysin laws are **carried**, as `Stacks.Chow.TransportFlatNaturality` and
`Stacks.Chow.TransportGysinNaturality`. This is the idiom the library already uses for its own
constructions of this shape: `Stacks.Chow.firstChernClass` carries the flat and Gysin transports
of Stacks 0FDW in exactly this form, through
`Stacks.Chow.IdentityCapRule.TransportFlatNaturality` and
`Stacks.Chow.IdentityCapRule.TransportGysinNaturality`. The precedent is only partial on the
other side: `Stacks.Chow.rankBivariantClass` carries, for Stacks 0ESW, the Gysin transport
*alone*. Its flat transport is proved, by
`Stacks.Chow.transportFlatNaturality_identityCapRuleZero`, because the degree-zero identity rule
it is built from is the rule of
`StacksFrontier.AlgebraicGeometry.Chow.DiagonalGysinIdentity`, whose flat law is the isomorphism
case of Stacks 02RG. That route is specific to the identity rule and does not transfer to the
prescribed cap operation below. Each law is the corresponding field of
`Stacks.Chow.BivariantClass` with the cap operation replaced by the prescribed one, so each is a
statement *about the prescribed cap operation* and not about any other object; that is what the
attribute keys below disclose. The same two transports would follow from the two remaining
naturality properties of `π` exactly as the proper one does, and are carried rather than reduced
to those because the flat law is an `HEq` and the Gysin law carries a divisor identification,
so neither reduction is the three-line rewrite the proper one is.

### What is not delivered

The base-change clause, Stacks 0FBJ, is not proved. Its statement needs the bivariant restriction
of Stacks 0F9Z, and its proof reduces by the same injectivity to the base-change compatibility of
`E`, which is a statement about the absent `C`.

The constant-rank clause is delivered by the typing: `Stacks.Chow.IsVirtualNormalGysinClass` is
a predicate on `Stacks.Chow.BivariantClass C G sZ sX i hi (r : ℤ)`, that is on `A^r(Z ⟶ X)`, and
`r` is the rank of `𝒩`, tied to the geometry by the two fields
`Stacks.Chow.VirtualNormalBundleProjection.rank` and
`Stacks.Chow.VirtualNormalBundleProjection.relativeDimension`. That the degree must be `r` and
nothing else is forced by the relation: the flat pullback `p^*` raises degrees by the relative
dimension `r` of the projection, so the source degree of `π` is `k - r`. The general-rank
clause, which places the class in the completed group `A^*(Z ⟶ X)^∧` of
`Stacks.Chow.completedBivariantGroup`, is not delivered: it needs the decomposition of Stacks
0FDZ over the connected components of `Z` and a rank constant only on each of them.

### The degree of `E` is arbitrary

In the source `E = ι_* ∘ j^* ∘ C` has degree `0`, since `C` does, and `c` has degree `r`. Fixing
`e = 0` would put the degree `k - 0` in the types without making any proof below shorter, so `e`
is left arbitrary and the source's case is `e = 0`. Nothing below relates `r` and `e`.

## References

* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FBJ](https://stacks.math.columbia.edu/tag/0FBJ)
* [Stacks Project, Tag 0FBQ](https://stacks.math.columbia.edu/tag/0FBQ)
* [Stacks Project, Tag 0FBG](https://stacks.math.columbia.edu/tag/0FBG)
* [Stacks Project, Tag 0FBH](https://stacks.math.columbia.edu/tag/0FBH)
* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 0637](https://stacks.math.columbia.edu/tag/0637)
* [Stacks Project, Tag 02TY](https://stacks.math.columbia.edu/tag/02TY)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
* [Stacks Project, Tag 0B79](https://stacks.math.columbia.edu/tag/0B79)
* [Stacks Project, Tag 0EPK](https://stacks.math.columbia.edu/tag/0EPK)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 0FDW](https://stacks.math.columbia.edu/tag/0FDW)
* [Stacks Project, Tag 0ESW](https://stacks.math.columbia.edu/tag/0ESW)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The base change of the bundle projection along a test scheme -/

section BundleBaseChange

variable {Z X N : Scheme.{u}} (i : Z ⟶ X) (q : N ⟶ Z)

/-- The base change `N ×_X T ⟶ Z ×_X T` of the bundle projection `q : N ⟶ Z` along a test
scheme `g : T ⟶ X`, taken at the chosen pullbacks that `Stacks.Chow.BivariantClass` uses: it is
`q` on the first factor and the identity on the second. This is the morphism whose flat pullback
is the map `p^*` of the construction preceding Stacks 0FBK. -/
def bundleTestBaseChange {T : Scheme.{u}} (g : T ⟶ X) : pullback (q ≫ i) g ⟶ pullback i g :=
  pullback.lift (pullback.fst (q ≫ i) g ≫ q) (pullback.snd (q ≫ i) g) <| by
    rw [Category.assoc]; exact pullback.condition

@[simp]
theorem bundleTestBaseChange_fst {T : Scheme.{u}} (g : T ⟶ X) :
    bundleTestBaseChange i q g ≫ pullback.fst i g = pullback.fst (q ≫ i) g ≫ q :=
  pullback.lift_fst _ _ _

@[simp]
theorem bundleTestBaseChange_snd {T : Scheme.{u}} (g : T ⟶ X) :
    bundleTestBaseChange i q g ≫ pullback.snd i g = pullback.snd (q ≫ i) g :=
  pullback.lift_snd _ _ _

/-- The base change of the bundle projection is a morphism over the base of chapter 42. -/
theorem bundleTestBaseChange_comp_structureMorphism {C : ChowSituation.{u}} (sZ : Z ⟶ C.S)
    (sN : N ⟶ C.S) (hq : q ≫ sZ = sN) {T : Scheme.{u}} (g : T ⟶ X) :
    bundleTestBaseChange i q g ≫ (pullback.fst i g ≫ sZ) = pullback.fst (q ≫ i) g ≫ sN := by
  rw [← Category.assoc, bundleTestBaseChange_fst, Category.assoc, hq]

end BundleBaseChange

/-! ### The geometric input of the construction -/

/-- The geometric input of the construction preceding Stacks 0FBK, at constant rank: a virtual
normal bundle `𝒩` of Stacks 0FBQ for the immersion `i : Z ⟶ X` which has constant rank `r`,
together with the projection `q : N ⟶ Z` of the vector bundle `N = Spec_Z(Sym(𝒩^∨))` that `𝒩`
defines, of which only flatness and relative dimension `r` are recorded.

The vector bundle itself is available in this repository, as
`AlgebraicGeometry.Scheme.Modules.vectorBundle`, but neither its flatness nor its relative
dimension is; so the projection is a field here rather than a construction. See the
implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleClass`. -/
structure VirtualNormalBundleProjection {Z X N : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (q : N ⟶ Z) [LocallyOfFiniteType q] (r : ℕ) where
  /-- The virtual normal bundle `𝒩` for `i`, Stacks 0FBQ. -/
  normalBundle : VirtualNormalBundle i
  /-- `𝒩` has constant rank `r`. -/
  rank :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} normalBundle.bundle r
  /-- The bundle projection is flat. -/
  flat : AlgebraicGeometry.Flat q
  /-- The bundle projection has relative dimension `r`, the rank of `𝒩`: its fibres are the
  affine spaces of the fibres of `𝒩`. This is what makes the flat pullback along it raise
  degrees by `r`, hence what makes the class have degree `r`. -/
  relativeDimension : AlgebraicGeometry.RelativeDimension q r

/-! ### The characterizing relation of the construction -/

section Gysin

variable (C : ChowSituation.{u}) (G : GysinSystem C) {Z X N : Scheme.{u}}
  (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sN : N ⟶ C.S) [LocallyOfFiniteType sN]
  (i : Z ⟶ X) [IsImmersion i] [LocallyOfFiniteType i] (hi : i ≫ sX = sZ)
  (q : N ⟶ Z) [LocallyOfFiniteType q] (hq : q ≫ sZ = sN) (r : ℕ) (e : ℤ)
  (E : BivariantClass C G sN sX (q ≫ i) (comp_comp_structureMorphism_eq hq hi) e)
  (π : ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ),
    chowGroup C (pullback.fst i g ≫ sZ) (k - (r : ℤ)) →+
      chowGroup C (pullback.fst (q ≫ i) g ≫ sN) (k - e))

/-- **Stacks 0FBK.** The relation `p^* ∘ c(Z ⟶ X, 𝒩) = ι_* ∘ j^* ∘ C` that the construction
preceding Stacks 0FBK defines the class by, written on cap operations: on every test scheme
`g : T ⟶ X` and in every degree, capping with `c` and then applying the flat pullback `π` of the
bundle projection is capping with the class `E = ι_* ∘ j^* ∘ C`.

The construction's own formulation is that `c ∩ α` is the unique `β` with
`p^* β = ι_* j^* (C ∩ α)`, which is this equality together with the injectivity of `π` of
Stacks 02TY. The class `c` ranges over `A^r(Z ⟶ X)` for `r` the constant rank of `𝒩`, which is
the last clause of Stacks 0FBK.

The virtual normal bundle enters through the setting argument `_P`, which is what restricts the
relation to the situation of Stacks 0FBK: it may be formed only when `i` admits a virtual normal
bundle of constant rank `r` whose vector bundle projection is `q`. The relation itself is a
condition on `c` alone, so `_P` does not occur in it. -/
@[stacks 0FBK "the characterizing relation p^* ∘ c = ι_* ∘ j^* ∘ C of the construction, on a \
degree-r bivariant class for r the rank of 𝒩, with ι_* j^* C carried as E (Stacks 0F9J, 0FBG, \
0FBH absent) and the flat pullback of the bundle projection carried as π (Stacks 0B78 holds at \
the other pullback); the bivariance laws and the Stacks 0FBJ base change are not proved"]
def IsVirtualNormalGysinClass (_P : VirtualNormalBundleProjection i q r)
    (c : BivariantClass C G sZ sX i hi (r : ℤ)) : Prop :=
  ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sX) k),
    π g k (c.cap g k α) = E.cap g k α

/-- **Stacks 0FBK.** The relation determines the class: two bivariant classes of degree `r` for
`Z ⟶ X` which both satisfy it are equal. This is what makes `c(Z ⟶ X, 𝒩)` well defined, and it
is the content of the construction that does not depend on the class existing. Only injectivity
of `π` is used, which is the half of Stacks 02TY that the uniqueness assertion of the
construction rests on. -/
@[stacks 0FBK "uniqueness: the characterizing relation determines the class in A^r(Z ⟶ X), \
given injectivity of π (Stacks 02TY)"]
theorem eq_of_isVirtualNormalGysinClass (P : VirtualNormalBundleProjection i q r)
    (hπ : ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ),
      Function.Injective (π g k))
    {c c' : BivariantClass C G sZ sX i hi (r : ℤ)}
    (h : IsVirtualNormalGysinClass C G sZ sX sN i hi q hq r e E π P c)
    (h' : IsVirtualNormalGysinClass C G sZ sX sN i hi q hq r e E π P c') : c = c' := by
  refine BivariantClass.ext C G sZ sX i hi (r : ℤ) ?_
  intro T g _ k α
  exact hπ g k ((h g k α).trans (h' g k α).symm)

/-- The cap operation the construction preceding Stacks 0FBK prescribes: `α ↦ β` where `β` is
the unique class with `p^* β = ι_* j^* (C ∩ α)`, that is `(p^*)^{-1} ∘ (ι_* ∘ j^* ∘ C)`. The
inverse exists by Stacks 02TY, carried as bijectivity of `π`. -/
@[stacks 0FBK "the prescribed cap operation α ↦ β of the construction, as the inverse of π \
(Stacks 02TY) applied to the cap operation of E"]
def virtualNormalGysinCap
    (hπ : ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ),
      Function.Bijective (π g k))
    {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ) :
    chowGroup C (g ≫ sX) k →+ chowGroup C (pullback.fst i g ≫ sZ) (k - (r : ℤ)) :=
  (AddEquiv.ofBijective (π g k) (hπ g k)).symm.toAddMonoidHom.comp (E.cap g k)

omit [IsImmersion i] in
/-- The prescribed cap operation satisfies the characterizing relation,
`p^* β = ι_* j^* (C ∩ α)`. So the relation is a consistent condition on cap operations, and the
only thing a bivariant class satisfying it adds to the prescribed operation is bivariance. -/
@[stacks 0FBK "the prescribed cap operation satisfies the characterizing relation"]
theorem pi_virtualNormalGysinCap
    (hπ : ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ),
      Function.Bijective (π g k))
    {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ sX) k) :
    π g k (virtualNormalGysinCap C G sZ sX sN i hi q hq r e E π hπ g k α) = E.cap g k α :=
  (AddEquiv.ofBijective (π g k) (hπ g k)).apply_symm_apply (E.cap g k α)

/-- **Stacks 0FBK.** A bivariant class of degree `r` for `Z ⟶ X` satisfies the characterizing
relation exactly when its cap operation is the prescribed one. Together with
`Stacks.Chow.eq_of_isVirtualNormalGysinClass` this says that the construction leaves no freedom:
the class, if it exists, is the bivariant class whose cap operation is
`Stacks.Chow.virtualNormalGysinCap`. -/
@[stacks 0FBK "the relation holds exactly for a class whose cap operation is the prescribed \
one"]
theorem isVirtualNormalGysinClass_iff_cap_eq (P : VirtualNormalBundleProjection i q r)
    (hπ : ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ),
      Function.Bijective (π g k))
    (c : BivariantClass C G sZ sX i hi (r : ℤ)) :
    IsVirtualNormalGysinClass C G sZ sX sN i hi q hq r e E π P c ↔
      ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
        (α : chowGroup C (g ≫ sX) k),
        c.cap g k α = virtualNormalGysinCap C G sZ sX sN i hi q hq r e E π hπ g k α := by
  constructor
  · intro h T g _ k α
    exact (hπ g k).1 ((h g k α).trans
      (pi_virtualNormalGysinCap C G sZ sX sN i hi q hq r e E π hπ g k α).symm)
  · intro h T g _ k α
    rw [h g k α, pi_virtualNormalGysinCap]

/-! ### The laws of Stacks 0B76 for the prescribed cap operation -/

omit [IsImmersion i] in
/-- The base-change map of test schemes is compatible with the projection to the source. -/
theorem bivariantBaseChangeMap_comp_fst {A B T T' : Scheme.{u}} (f : A ⟶ B) (g : T ⟶ B)
    (h : T' ⟶ T) :
    bivariantBaseChangeMap f g h ≫ pullback.fst f g = pullback.fst f (h ≫ g) := by
  simp [bivariantBaseChangeMap]

omit [IsImmersion i] in
/-- **Stacks 02RG for the base-change square of the bundle projection.** The flat pullback `π`
along the base change of `p : N ⟶ Z` commutes with proper pushforward along a morphism of test
schemes: pushing forward on `Z ×_X T` and then applying `π` is applying `π` and then pushing
forward along the induced map of the `N`-side base changes.

This is the one input the proper-pushforward law of the prescribed cap operation needs beyond
the laws of `E`. It is a statement about flat pullback against proper pushforward in a
cartesian square, Stacks 02RG, which no declaration in this repository carries — the same gap
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FirstChernClass` records for the flat transport of
the first Chern class. It mentions neither the prescribed cap operation nor any bivariant class
for `Z ⟶ X`. -/
def PiProperNaturality : Prop :=
  ∀ {T T' : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (h : T' ⟶ T) [IsProper h]
      (h' : pullback i (h ≫ g) ⟶ pullback i g)
      (sq : IsPullback (pullback.snd i (h ≫ g)) h' h (pullback.snd i g))
      (hfst : h' ≫ pullback.fst i g = pullback.fst i (h ≫ g)) (k : ℤ),
      letI : IsProper h' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
      ∀ (hfacZ : ProperPushforwardFactorsThroughRationalEquivalence C
            (pullback.fst i (h ≫ g) ≫ sZ) (pullback.fst i g ≫ sZ) h'
            (by rw [← Category.assoc, hfst]) (k - (r : ℤ)))
        (hfacN : ProperPushforwardFactorsThroughRationalEquivalence C
            (pullback.fst (q ≫ i) (h ≫ g) ≫ sN) (pullback.fst (q ≫ i) g ≫ sN)
            (bivariantBaseChangeMap (q ≫ i) g h)
            (by rw [← Category.assoc, bivariantBaseChangeMap_comp_fst]) (k - e))
        (β : chowGroup C (pullback.fst i (h ≫ g) ≫ sZ) (k - (r : ℤ))),
        π g k (properChowPushforward C (pullback.fst i (h ≫ g) ≫ sZ) (pullback.fst i g ≫ sZ) h'
              (by rw [← Category.assoc, hfst]) (k - (r : ℤ)) hfacZ β) =
          properChowPushforward C (pullback.fst (q ≫ i) (h ≫ g) ≫ sN)
            (pullback.fst (q ≫ i) g ≫ sN) (bivariantBaseChangeMap (q ≫ i) g h)
            (by rw [← Category.assoc, bivariantBaseChangeMap_comp_fst]) (k - e) hfacN
            (π (h ≫ g) k β)

omit [IsImmersion i] in
/-- **Stacks 0B76 (2) for the prescribed cap operation.** The flat-pullback law of a bivariant
class of degree `r` for `i : Z ⟶ X`, written for `Stacks.Chow.virtualNormalGysinCap`: this is the
`flat_naturality` field of `Stacks.Chow.BivariantClass` with its cap operation replaced by the
prescribed one.

Carried as a hypothesis, in the idiom of
`Stacks.Chow.IdentityCapRule.TransportFlatNaturality`. It is an `HEq` for the reason recorded in
the implementation notes of `StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Basic`: the flat
pullback of a `k`-cycle has degree `k + m`, so the two sides sit in degrees `(k + m) - r` and
`(k - r) + m`, which are the same integer and not the same term. -/
def TransportFlatNaturality
    (hπ : ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ),
      Function.Bijective (π g k)) : Prop :=
  ∀ {T T' : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (h : T' ⟶ T)
      [LocallyOfFiniteType h] [Flat h] (m : ℕ) (hm : AlgebraicGeometry.RelativeDimension h m)
      (h' : pullback i (h ≫ g) ⟶ pullback i g)
      (sq : IsPullback (pullback.snd i (h ≫ g)) h' h (pullback.snd i g))
      (hfst : h' ≫ pullback.fst i g = pullback.fst i (h ≫ g)) (k : ℤ),
      letI : LocallyOfFiniteType h' :=
        MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
      letI : Flat h' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
      ∀ (hm' : AlgebraicGeometry.RelativeDimension h' m)
        (hfac : FlatPullbackFactorsThroughRationalEquivalence C ((h ≫ g) ≫ sX) (g ≫ sX) h
          (by simp [Category.assoc]) m hm k)
        (hfac' : FlatPullbackFactorsThroughRationalEquivalence C
          (pullback.fst i (h ≫ g) ≫ sZ) (pullback.fst i g ≫ sZ) h'
          (by rw [← Category.assoc, hfst]) m hm' (k - (r : ℤ)))
        (α : chowGroup C (g ≫ sX) k),
        HEq
          (virtualNormalGysinCap C G sZ sX sN i hi q hq r e E π hπ (h ≫ g) (k + (m : ℤ))
            (flatPullbackChow C ((h ≫ g) ≫ sX) (g ≫ sX) h (by simp [Category.assoc]) m hm k
              hfac α))
          (flatPullbackChow C (pullback.fst i (h ≫ g) ≫ sZ) (pullback.fst i g ≫ sZ) h'
            (by rw [← Category.assoc, hfst]) m hm' (k - (r : ℤ)) hfac'
            (virtualNormalGysinCap C G sZ sX sN i hi q hq r e E π hπ g k α))

omit [IsImmersion i] in
/-- **Stacks 0B76 (3) for the prescribed cap operation.** The Gysin law of a bivariant class of
degree `r` for `i : Z ⟶ X`, written for `Stacks.Chow.virtualNormalGysinCap`: this is the
`gysin_naturality` field of `Stacks.Chow.BivariantClass` with its cap operation replaced by the
prescribed one.

Carried as a hypothesis, in the idiom of
`Stacks.Chow.IdentityCapRule.TransportGysinNaturality`. The identification of the base change of
the zero scheme `D ⊆ T` with the zero scheme of the pulled-back section is the isomorphism `ε`,
and the induced map on Chow groups is proper pushforward along `ε.hom`, exactly as in the field
itself. -/
def TransportGysinNaturality
    (hπ : ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ),
      Function.Bijective (π g k)) : Prop :=
  ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (L : T.Modules)
      [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
      [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback i g).sheaf.obj
        (pullback i g).ringCatSheaf.property
        ((Scheme.Modules.pullback (pullback.snd i g)).obj L)]
      (s : Γ(L, ⊤)) (k : ℤ),
      let D := Stacks.Divisors.zeroScheme T L s
      let L' := (Scheme.Modules.pullback (pullback.snd i g)).obj L
      let s' := AlgebraicGeometry.pullbackGlobalSections (pullback.snd i g) L s
      let Ezero := Stacks.Divisors.zeroScheme (pullback i g) L' s'
      ∀ (ε : pullback i (D.subschemeι ≫ g) ≅ Ezero.subscheme)
        (_hε : ε.hom ≫ Ezero.subschemeι = bivariantBaseChangeMap i g D.subschemeι)
        (hbase : ε.hom ≫ (Ezero.subschemeι ≫ pullback.fst i g ≫ sZ) =
          pullback.fst i (D.subschemeι ≫ g) ≫ sZ)
        (hfac : ProperPushforwardFactorsThroughRationalEquivalence C
          (pullback.fst i (D.subschemeι ≫ g) ≫ sZ)
          (Ezero.subschemeι ≫ pullback.fst i g ≫ sZ) ε.hom hbase (k - (r : ℤ)))
        (α : chowGroup C (g ≫ sX) (k + 1)),
        properChowPushforward C (pullback.fst i (D.subschemeι ≫ g) ≫ sZ)
            (Ezero.subschemeι ≫ pullback.fst i g ≫ sZ) ε.hom hbase (k - (r : ℤ)) hfac
            (virtualNormalGysinCap C G sZ sX sN i hi q hq r e E π hπ (D.subschemeι ≫ g) k
              (G.onChow (g ≫ sX) L s k α)) =
          G.onChow (pullback.fst i g ≫ sZ) L' s' (k - (r : ℤ))
            (Eq.mp (congrArg (chowGroup C (pullback.fst i g ≫ sZ))
              (by omega : (k + 1) - (r : ℤ) = (k - (r : ℤ)) + 1))
              (virtualNormalGysinCap C G sZ sX sN i hi q hq r e E π hπ g (k + 1) α))

/-! ### The class -/

/-- **Stacks 0FBK.** The bivariant class `c(Z ⟶ X, 𝒩) ∈ A^r(Z ⟶ X)` of the construction
preceding Stacks 0FBK: the prescribed cap operation `(p^*)^{-1} ∘ (ι_* ∘ j^* ∘ C)` together with
the three naturality laws of Stacks 0B76.

The proper-pushforward law is **proved**, from the corresponding law of `E` and
`Stacks.Chow.PiProperNaturality`: this is the source's "since both `ι_* ∘ j^* ∘ C` and `p^*` are
bivariant", carried out. The flat and Gysin laws are carried as hypotheses, in the idiom the
library uses for its own rank class at Stacks 0ESW.

The library is not of one mind about attaching a `@[stacks]` attribute to a class that carries
laws this way, and the choice made here is deliberate. The rank class of Stacks 0ESW is tagged,
with the carrying disclosed in its key; the first Chern class built the same way in
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FirstChernClass` is deliberately left *untagged*,
under a section heading saying so. The attribute below follows the rank class: what it claims is
the statement as written, hypotheses included, and the hypotheses are named in the signature and
disclosed in the key, so nothing is hidden by tagging it. A reader who prefers the stricter
convention loses only the attribute, not the mathematics.

Its cap operation satisfies the characterizing relation, by
`Stacks.Chow.isVirtualNormalGysinClass_virtualNormalGysinClass`, so by
`Stacks.Chow.eq_of_isVirtualNormalGysinClass` it is *the* class of the construction. -/
@[stacks 0FBK "the bivariant element of A^r(Z ⟶ X) prescribed by the construction, with its \
proper-pushforward law proved from the same law for E and Stacks 02RG for the bundle \
base-change square; the flat and Gysin transport laws are carried as named hypotheses, as for \
the library's own rank class at Tag 0ESW"]
def virtualNormalGysinClass (_P : VirtualNormalBundleProjection i q r)
    (hpp : ProperPushforwardDescends C)
    (hπ : ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ),
      Function.Bijective (π g k))
    (hproper : PiProperNaturality C sZ sN i q r e π)
    (hflat : TransportFlatNaturality C G sZ sX sN i hi q hq r e E π hπ)
    (hgysin : TransportGysinNaturality C G sZ sX sN i hi q hq r e E π hπ) :
    BivariantClass C G sZ sX i hi (r : ℤ) where
  cap g _ k := virtualNormalGysinCap C G sZ sX sN i hi q hq r e E π hπ g k
  cap_properPushforward := by
    intro T T' g _ h _ h' sq hfst k α
    haveI : IsProper h' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
    refine (hπ g k).1 ?_
    rw [hproper g h h' sq hfst k (hpp _ _ _ _ _) (hpp _ _ _ _ _)]
    simp only [pi_virtualNormalGysinCap]
    exact E.proper_naturality g h (bivariantBaseChangeMap (q ≫ i) g h)
      (isPullback_bivariantBaseChangeMap (q ≫ i) g h)
      (bivariantBaseChangeMap_comp_fst (q ≫ i) g h) k (hpp _ _ _ _ _) (hpp _ _ _ _ _) α
  cap_flatPullbackChow := by
    intro T₀ T₀' g₀ _ w₀ _ _ r₀ hr₀ w₀' sq₀ hfst₀ k₀ α₀
    exact hflat g₀ w₀ r₀ hr₀ w₀' sq₀ hfst₀ k₀ _ _ _ α₀
  cap_gysin := by
    intro T₀ g₀ _ L₀ _ s₀ k₀ _ _ _ _ ε₀ hε₀ hbase₀ α₀
    exact hgysin g₀ L₀ s₀ k₀ ε₀ hε₀ hbase₀ _ α₀

/-- **Stacks 0FBK.** The constructed class satisfies the characterizing relation
`p^* ∘ c = ι_* ∘ j^* ∘ C`. With `Stacks.Chow.eq_of_isVirtualNormalGysinClass` this identifies it
as the class `c(Z ⟶ X, 𝒩)` of the construction, and not merely as some element of
`A^r(Z ⟶ X)`. -/
@[stacks 0FBK "the constructed element of A^r(Z ⟶ X) satisfies the characterizing relation, \
hence is the one the construction prescribes"]
theorem isVirtualNormalGysinClass_virtualNormalGysinClass
    (P : VirtualNormalBundleProjection i q r) (hpp : ProperPushforwardDescends C)
    (hπ : ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ),
      Function.Bijective (π g k))
    (hproper : PiProperNaturality C sZ sN i q r e π)
    (hflat : TransportFlatNaturality C G sZ sX sN i hi q hq r e E π hπ)
    (hgysin : TransportGysinNaturality C G sZ sX sN i hi q hq r e E π hπ) :
    IsVirtualNormalGysinClass C G sZ sX sN i hi q hq r e E π P
      (virtualNormalGysinClass C G sZ sX sN i hi q hq r e E π P hpp hπ hproper hflat hgysin) := by
  intro T g _ k α
  exact pi_virtualNormalGysinCap C G sZ sX sN i hi q hq r e E π hπ g k α

end Gysin

end Stacks.Chow

end
