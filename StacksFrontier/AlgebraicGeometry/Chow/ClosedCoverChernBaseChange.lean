module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Transport
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ExteriorProductCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Naturality
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardRationalEquivalence.ClosedImmersion

/-!
# The Chern classes of a cover by two closed subschemes are compatible with base change

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `i₁ : X₁ ⟶ X` and `i₂ : X₂ ⟶ X` be closed immersions with
`X = X₁ ∪ X₂` set theoretically, and let `E₂ ∈ D(𝒪_{X₂})` be a perfect object whose Chern
classes are defined and whose restriction to `X₁ ∩ X₂` is zero, resp. finite locally free of rank
`< p` in degree `0`. **Stacks 0F9H** produces a bivariant class

  `P'_p(E₂)`, resp. `c'_p(E₂) ∈ A^p(X₂ ⟶ X)`

*characterized* by the two cap identities

  `P'_p(E₂) ∩ i_{2,*}α₂ = P_p(E₂) ∩ α₂`  and  `P'_p(E₂) ∩ i_{1,*}α₁ = 0`

for `αⱼ ∈ CH_k(Xⱼ)`, "and similarly after any base change `X' ⟶ X` locally of finite type".

**Stacks 0GUG** says that for a morphism `q : X' ⟶ X` locally of finite type, with
`X' = X'₁ ∪ X'₂` and `E'₂ ∈ D(𝒪_{X'₂})` the pullbacks to `X'`, the class `P'_p(E'₂)`, resp.
`c'_p(E'₂)` in `A^p(X'₂ ⟶ X')` built by Stacks 0F9H from `X' = X'₁ ∪ X'₂` and `E'₂` is the
restriction (Remark 0F9Z) of `P'_p(E₂)`, resp. `c'_p(E₂)`. Its proof is "immediate from the
characterization of these classes in Lemma 0F9H".

## Main definitions

* `Stacks.Chow.ChernCapFamily` — a family of degree-`p` cap operations on the test schemes of a
  scheme over `S`, natural under isomorphisms of test schemes: the shape in which the ambient
  Chern class `P_p(E₂)`, resp. `c_p(E₂)`, enters the characterization of Stacks 0F9H.
* `Stacks.Chow.ChernCapFamily.restrict` — such a family, read along a morphism `X'₂ ⟶ X₂` over
  the base. A test scheme over `X'₂` is a test scheme over `X₂`, so this is precisely the ambient
  Chern class of the pullback `E'₂` of `E₂`; nothing about Chern classes is assumed to produce
  it.
* `Stacks.Chow.IsClosedCoverChernClass` — the characterization of Stacks 0F9H: the conjunction of
  the two cap identities, at *every* test scheme of `X`, which is the source's "and similarly
  after any base change `X' ⟶ X` locally of finite type".
* `Stacks.Chow.ClosedCoverChernClassUnique` — the assertion that the characterization determines
  the class, i.e. the word "characterized" in Stacks 0F9H.
* `Stacks.Chow.baseChangeWitnessProjection` and
  `Stacks.Chow.baseChangeWitnessComparison` — the projection `X'₂ ⟶ X₂` and the
  identification `X₂ ×_X T ≅ X'₂ ×_{X'} T` on a test scheme `T ⟶ X'`, both obtained from the
  witness `θ : X₂ ×_X X' ≅ X'₂` that `X'₂` is the base change of `X₂`.

## Main results

* `Stacks.Chow.isClosedCoverChernClass_bivariantTransport_bivariantRestriction` — **Stacks
  0GUG**, unconditionally: the restriction of the class of Stacks 0F9H along `q`, transported
  along `θ`, satisfies the characterization of Stacks 0F9H for the base-changed decomposition and
  the restricted ambient Chern class. This is the whole mathematical content of the tag.
* `Stacks.Chow.closedCoverChern_eq_bivariantTransport_bivariantRestriction` — **Stacks 0GUG**:
  the class built by Stacks 0F9H from the base-changed data *equals* that restriction. This is
  the equality of elements of `A^p(X'₂ ⟶ X')` that the tag asserts; it is the previous result
  together with the uniqueness half of Stacks 0F9H at `X'`.

Stacks 0GUG itself, for the classes of Stacks 0F9H as constructed in
`StacksFrontier.AlgebraicGeometry.Chow.BabyLocalizedChern.LocalizedChernClass`, is
`Stacks.Chow.localizedChernClassOfClosedCover_baseChange` and
`Stacks.Chow.localizedPowerSumOfClosedCover_baseChange` in
`StacksFrontier.AlgebraicGeometry.Chow.BabyLocalizedChern.LocalizedChernBaseChange`; the results here
are the form of its argument used by
`StacksFrontier.AlgebraicGeometry.Chow.LocalizedClassAtInfinity.Modification` (Stacks 0FAU).

## Implementation notes

### How the objects of the tag are spelled

`A^p(X₂ ⟶ X)` is `Stacks.Chow.BivariantClass` of degree `p` (Stacks 0B76), stated against a
`Stacks.Chow.GysinSystem`. The restriction of Remark 0F9Z is
`Stacks.Chow.bivariantRestriction`, which produces a class for the *chosen* fibre product
`X₂ ×_X X' ⟶ X'`; `Stacks.Chow.bivariantTransport` then carries it along the identification of
that fibre product with `X'₂`, so that the two sides of the conclusion lie in one and the same
group. Both are the library's own constructions: nothing here defines a second restriction or a
second cap operation. The pushforwards `i_{j,*}` are the unconditional
`Stacks.Chow.chowPushforwardOfIsClosedImmersion`, since each is a base change of a closed
immersion.

### Why Stacks 0F9H enters as data rather than as a theorem

Stacks 0F9H is not formalized here, and the existence half of it is not needed: Stacks 0GUG
compares two classes that Stacks 0F9H *produces*, and its proof uses only that each satisfies
the characterization and that the characterization pins a class down. So the two classes are
hypotheses — a `Stacks.Chow.BivariantClass` together with a proof of
`Stacks.Chow.IsClosedCoverChernClass` — and the word "characterized" is the separate hypothesis
`Stacks.Chow.ClosedCoverChernClassUnique` at `X'`. Neither is a weakening of the tag: both are
assertions of the ambient Lemma 0F9H, in whose setting the tag is stated.

In particular the perfect object `E₂` itself never appears. All that Stacks 0GUG uses of it is
its ambient Chern class as an operation on the Chow groups of test schemes, which is the
`Stacks.Chow.ChernCapFamily` parameter, and that the ambient Chern class of the pullback `E'₂` is
the same operation read on test schemes over `X'₂`, which is why the base-changed
characterization is stated against `Stacks.Chow.ChernCapFamily.restrict` and not against a second
unrelated family. The naturality field of `Stacks.Chow.ChernCapFamily` is the isomorphism case of
the proper-pushforward axiom of Stacks 0B76 for that Chern class, which holds because
`P_p(E₂)`, resp. `c_p(E₂)`, is a bivariant class (Stacks 0B7H); it is needed because the two
fibre products `X₂ ×_X T` and `X'₂ ×_{X'} T` are canonically isomorphic rather than equal.

### The hypothesis `X = X₁ ∪ X₂` is not assumed

The set-theoretic cover is what makes the characterization of Stacks 0F9H determine the class —
it is exactly the surjectivity half of Stacks 0F94, `CH_k(X₁) ⊕ CH_k(X₂) → CH_k(X)`, applied at
every test scheme. Here that determination is the hypothesis
`Stacks.Chow.ClosedCoverChernClassUnique`, so the cover is not assumed a second time and the
statements below hold for any two closed immersions. Dropping an unused hypothesis generalizes
the tag; it does not weaken it.

## References

* [Stacks Project, Tag 0GUG](https://stacks.math.columbia.edu/tag/0GUG)
* [Stacks Project, Tag 0F9H](https://stacks.math.columbia.edu/tag/0F9H)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0F94](https://stacks.math.columbia.edu/tag/0F94)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Pushforward along a closed immersion and transport of the target -/

/-- Pushforward along a closed immersion commutes with the transport of the target's Chow group
along an equality of structure morphisms: the closed-immersion counterpart of
`Stacks.Chow.chowGroupCongr_chowPushforwardOfIso_target`. -/
theorem chowGroupCongr_chowPushforwardOfIsClosedImmersion_target (C : ChowSituation.{u})
    {A B : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA] {sB sB' : B ⟶ C.S}
    [LocallyOfFiniteType sB] [LocallyOfFiniteType sB'] (hB : sB = sB') (w : A ⟶ B)
    [IsClosedImmersion w] (hw : w ≫ sB = sA) (hw' : w ≫ sB' = sA) (k : ℤ)
    (α : chowGroup C sA k) :
    chowGroupCongr C hB k (chowPushforwardOfIsClosedImmersion C sA sB w hw k α) =
      chowPushforwardOfIsClosedImmersion C sA sB' w hw' k α := by
  subst hB
  rfl

/-- Pushforward along an isomorphism over the base is pushforward along it read as a closed
immersion: both are the proper pushforward of Stacks 0GU8, whose two Stacks 02S2 instances are
propositions. -/
theorem chowPushforwardOfIso_eq_chowPushforwardOfIsClosedImmersion (C : ChowSituation.{u})
    {A B : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S)
    [LocallyOfFiniteType sB] (w : A ⟶ B) [IsIso w] (hw : w ≫ sB = sA) (k : ℤ) :
    chowPushforwardOfIso C sA sB w hw k = chowPushforwardOfIsClosedImmersion C sA sB w hw k :=
  rfl

/-- Pushing forward along two composable closed immersions is pushing forward along any
morphism equal to their composite. -/
private theorem chowPushforwardOfIsClosedImmersion_comp_eq (C : ChowSituation.{u})
    {A B D : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S)
    [LocallyOfFiniteType sB] (sD : D ⟶ C.S) [LocallyOfFiniteType sD] (f : A ⟶ B)
    [IsClosedImmersion f] (g : B ⟶ D) [IsClosedImmersion g] (h : A ⟶ D) [IsClosedImmersion h]
    (hfg : f ≫ g = h) (hf : f ≫ sB = sA) (hg : g ≫ sD = sB) (hh : h ≫ sD = sA) (k : ℤ)
    (α : chowGroup C sA k) :
    chowPushforwardOfIsClosedImmersion C sB sD g hg k
        (chowPushforwardOfIsClosedImmersion C sA sB f hf k α) =
      chowPushforwardOfIsClosedImmersion C sA sD h hh k α := by
  rw [← AddMonoidHom.comp_apply, chowPushforwardOfIsClosedImmersion_comp C sA sB sD f g hf hg k]
  exact DFunLike.congr_fun (chowPushforwardOfIsClosedImmersion_congr C sA sD _ _ hfg _ _ k) α

/-! ### Families of cap operations on test schemes -/

/-- A family of degree-`p` cap operations on the test schemes of a scheme `Z` locally of finite
type over the base, natural under isomorphisms of test schemes over `Z`.

This is the shape in which the ambient Chern class `P_p(E₂)`, resp. `c_p(E₂)`, of a perfect
object on `Z` enters the characterization of Stacks 0F9H: that characterization only ever uses
the operation `α ↦ P_p(E₂) ∩ α` on the Chow groups of test schemes of `Z`, together with its
naturality, which holds because `P_p(E₂)` is a bivariant class (Stacks 0B7H). -/
structure ChernCapFamily (C : ChowSituation.{u}) {Z : Scheme.{u}} (sZ : Z ⟶ C.S)
    [LocallyOfFiniteType sZ] (p : ℤ) where
  /-- The cap operation on a test scheme `g : T ⟶ Z`. -/
  cap : ∀ {T : Scheme.{u}} (g : T ⟶ Z) [LocallyOfFiniteType g] (k : ℤ),
    chowGroup C (g ≫ sZ) k →+ chowGroup C (g ≫ sZ) (k - p)
  /-- The cap operations commute with pushforward along an isomorphism of test schemes over `Z`:
  the isomorphism case of the proper-pushforward axiom of Stacks 0B76. -/
  cap_naturality : ∀ {T T' : Scheme.{u}} (g : T ⟶ Z) [LocallyOfFiniteType g] (g' : T' ⟶ Z)
      [LocallyOfFiniteType g'] (ι : T ⟶ T') [IsIso ι] (hι : ι ≫ g' = g) (k : ℤ)
      (α : chowGroup C (g ≫ sZ) k),
    chowPushforwardOfIso C (g ≫ sZ) (g' ≫ sZ) ι
        (by rw [← Category.assoc, hι]) (k - p) (cap g k α) =
      cap g' k (chowPushforwardOfIso C (g ≫ sZ) (g' ≫ sZ) ι (by rw [← Category.assoc, hι]) k α)

namespace ChernCapFamily

variable (C : ChowSituation.{u}) {Z Z' : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sZ' : Z' ⟶ C.S) [LocallyOfFiniteType sZ'] (u : Z' ⟶ Z) [LocallyOfFiniteType u]
  (hu : u ≫ sZ = sZ') (p : ℤ)

include hu in
omit [LocallyOfFiniteType sZ] [LocallyOfFiniteType sZ'] [LocallyOfFiniteType u] in
/-- The structure morphism of a test scheme of `Z'`, read through `u : Z' ⟶ Z`. -/
theorem comp_comp_eq {T : Scheme.{u}} (g : T ⟶ Z') : (g ≫ u) ≫ sZ = g ≫ sZ' :=
  comp_comp_structureMorphism_eq (rfl : g ≫ sZ' = g ≫ sZ') hu

/-- The cap operation, on a test scheme of `Z'`, of a family of cap operations on the test
schemes of `Z` read along a morphism `u : Z' ⟶ Z` over the base: a test scheme `g : T ⟶ Z'` is
the test scheme `g ≫ u` of `Z`, and this caps there exactly as the given family does. -/
def restrictCap (amb : ChernCapFamily C sZ p) {T : Scheme.{u}} (g : T ⟶ Z')
    [LocallyOfFiniteType g] (k : ℤ) :
    chowGroup C (g ≫ sZ') k →+ chowGroup C (g ≫ sZ') (k - p) :=
  (chowGroupCongr C (comp_comp_eq C sZ sZ' u hu g) (k - p)).toAddMonoidHom.comp
    ((amb.cap (g ≫ u) k).comp
      (chowGroupCongr C (comp_comp_eq C sZ sZ' u hu g).symm k).toAddMonoidHom)

/-- The restricted cap operation, read on an element. -/
theorem restrictCap_apply (amb : ChernCapFamily C sZ p) {T : Scheme.{u}} (g : T ⟶ Z')
    [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sZ') k) :
    restrictCap C sZ sZ' u hu p amb g k α =
      chowGroupCongr C (comp_comp_eq C sZ sZ' u hu g) (k - p)
        (amb.cap (g ≫ u) k (chowGroupCongr C (comp_comp_eq C sZ sZ' u hu g).symm k α)) :=
  rfl

/-- The restricted cap operations are natural under isomorphisms of test schemes over `Z'`: an
isomorphism of test schemes over `Z'` is one over `Z`. -/
theorem restrictCap_naturality (amb : ChernCapFamily C sZ p) {T T' : Scheme.{u}} (g : T ⟶ Z')
    [LocallyOfFiniteType g] (g' : T' ⟶ Z') [LocallyOfFiniteType g'] (ι : T ⟶ T') [IsIso ι]
    (hι : ι ≫ g' = g) (k : ℤ) (α : chowGroup C (g ≫ sZ') k) :
    chowPushforwardOfIso C (g ≫ sZ') (g' ≫ sZ') ι (by rw [← Category.assoc, hι]) (k - p)
        (restrictCap C sZ sZ' u hu p amb g k α) =
      restrictCap C sZ sZ' u hu p amb g' k
        (chowPushforwardOfIso C (g ≫ sZ') (g' ≫ sZ') ι (by rw [← Category.assoc, hι]) k α) := by
  have hιu : ι ≫ (g' ≫ u) = g ≫ u := by rw [← Category.assoc, hι]
  have hbase : ι ≫ (g' ≫ sZ') = g ≫ sZ' := by rw [← Category.assoc, hι]
  have hbaseu : ι ≫ ((g' ≫ u) ≫ sZ) = (g ≫ u) ≫ sZ := by rw [← Category.assoc, hιu]
  rw [restrictCap_apply, restrictCap_apply,
    ← chowPushforwardOfIso_chowGroupCongr C (comp_comp_eq C sZ sZ' u hu g)
      (comp_comp_eq C sZ sZ' u hu g') ι hbaseu hbase (k - p),
    amb.cap_naturality (g ≫ u) (g' ≫ u) ι hιu k,
    ← chowPushforwardOfIso_chowGroupCongr C (comp_comp_eq C sZ sZ' u hu g).symm
      (comp_comp_eq C sZ sZ' u hu g').symm ι hbase hbaseu k]

/-- A family of cap operations on the test schemes of `Z`, read along a morphism `u : Z' ⟶ Z`
over the base.

For the ambient Chern class of a perfect object `E₂` on `Z` this is the ambient Chern class of
its pullback to `Z'`, so nothing about Chern classes is assumed in forming it. -/
def restrict (amb : ChernCapFamily C sZ p) : ChernCapFamily C sZ' p where
  cap := restrictCap C sZ sZ' u hu p amb
  cap_naturality := restrictCap_naturality C sZ sZ' u hu p amb

/-- The restricted family of cap operations, read on an element. -/
theorem restrict_cap (amb : ChernCapFamily C sZ p) {T : Scheme.{u}} (g : T ⟶ Z')
    [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sZ') k) :
    (restrict C sZ sZ' u hu p amb).cap g k α =
      chowGroupCongr C (comp_comp_eq C sZ sZ' u hu g) (k - p)
        (amb.cap (g ≫ u) k (chowGroupCongr C (comp_comp_eq C sZ sZ' u hu g).symm k α)) :=
  rfl

end ChernCapFamily

/-! ### The characterization of Stacks 0F9H -/

section Characterization

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X X₁ X₂ : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (i₁ : X₁ ⟶ X) [IsClosedImmersion i₁] [LocallyOfFiniteType i₁]
  (i₂ : X₂ ⟶ X) [IsClosedImmersion i₂] [LocallyOfFiniteType i₂] (p : ℤ)

/-- Pushforward `i_{j,*} : CH_k(Xⱼ ×_X T) ⟶ CH_k(T)` along the base change of a closed immersion
`i : Xⱼ ⟶ X` by a test scheme `g : T ⟶ X`. -/
def closedSubschemeTestPushforward {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [LocallyOfFiniteType i] {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ) :
    chowGroup C (pullback.fst i g ≫ (i ≫ sX)) k →+ chowGroup C (g ≫ sX) k :=
  chowPushforwardOfIsClosedImmersion C (pullback.fst i g ≫ (i ≫ sX)) (g ≫ sX) (pullback.snd i g)
    (pullbackSnd_comp_structureMorphism_eq C (i ≫ sX) sX i rfl g) k

/-- The pushforward along the base change of a closed immersion, unfolded. -/
theorem closedSubschemeTestPushforward_eq {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [LocallyOfFiniteType i] {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ) :
    closedSubschemeTestPushforward C sX i g k =
      chowPushforwardOfIsClosedImmersion C (pullback.fst i g ≫ (i ≫ sX)) (g ≫ sX)
        (pullback.snd i g) (pullbackSnd_comp_structureMorphism_eq C (i ≫ sX) sX i rfl g) k :=
  rfl

/-- **The characterization of Stacks 0F9H.** A bivariant class `c ∈ A^p(X₂ ⟶ X)` *is* the class
`P'_p(E₂)`, resp. `c'_p(E₂)`, of Stacks 0F9H for the ambient Chern class `amb` when on every test
scheme `g : T ⟶ X` locally of finite type

* `c ∩ i_{2,*}α₂ = amb ∩ α₂` for `α₂ ∈ CH_k(X₂ ×_X T)`, and
* `c ∩ i_{1,*}α₁ = 0` for `α₁ ∈ CH_k(X₁ ×_X T)`.

Quantifying over all test schemes is the source's "and similarly after any base change
`X' ⟶ X` locally of finite type"; the case `g = 𝟙 X` is the pair of identities displayed in the
tag. -/
def IsClosedCoverChernClass (amb : ChernCapFamily C (i₂ ≫ sX) p)
    (c : BivariantClass C G (i₂ ≫ sX) sX i₂ rfl p) : Prop :=
  (∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
      (α₂ : chowGroup C (pullback.fst i₂ g ≫ (i₂ ≫ sX)) k),
    c.cap g k (closedSubschemeTestPushforward C sX i₂ g k α₂) = amb.cap (pullback.fst i₂ g) k α₂) ∧
  ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
      (α₁ : chowGroup C (pullback.fst i₁ g ≫ (i₁ ≫ sX)) k),
    c.cap g k (closedSubschemeTestPushforward C sX i₁ g k α₁) = 0

/-- The word "characterized" in Stacks 0F9H: the two cap identities, at every test scheme,
determine the bivariant class.

This is where the hypothesis `X = X₁ ∪ X₂` of Stacks 0F9H is used in the source — through the
surjectivity of `CH_k(X₁) ⊕ CH_k(X₂) → CH_k(X)` (Stacks 0F94) at every test scheme — and it is
the only part of Stacks 0F9H that the proof of Stacks 0GUG needs besides the two classes
themselves. -/
def ClosedCoverChernClassUnique (amb : ChernCapFamily C (i₂ ≫ sX) p) : Prop :=
  ∀ c d : BivariantClass C G (i₂ ≫ sX) sX i₂ rfl p,
    IsClosedCoverChernClass C G sX i₁ i₂ p amb c →
      IsClosedCoverChernClass C G sX i₁ i₂ p amb d → c = d

end Characterization

/-! ### The base change of a closed subscheme -/

section Comparison

variable {X X' X₂ X'₂ : Scheme.{u}} (q : X' ⟶ X) (i₂ : X₂ ⟶ X) (i'₂ : X'₂ ⟶ X')
  (θ : pullback i₂ q ≅ X'₂) (hθ : θ.hom ≫ i'₂ = pullback.snd i₂ q)

/-- The projection `A' ⟶ A` of a base change of a morphism `v : A ⟶ X` along `q : X' ⟶ X`, read
off a witness `θ : A ×_X X' ≅ A'` that `A'` is that base change. Below `v` is the closed
immersion `i₂ : X₂ ⟶ X`, but nothing here needs that. -/
def baseChangeWitnessProjection : X'₂ ⟶ X₂ := θ.inv ≫ pullback.fst i₂ q

/-- The projection `A' ⟶ A` of a base change along `q : X' ⟶ X` is locally of finite type when
`q` is: up to the witness `θ` it is the projection `A ×_X X' ⟶ A`, a base change of `q`. -/
instance locallyOfFiniteType_baseChangeWitnessProjection [LocallyOfFiniteType q] :
    LocallyOfFiniteType (baseChangeWitnessProjection q i₂ θ) := by
  rw [baseChangeWitnessProjection]
  infer_instance

include hθ in
/-- The projection of the base change of the closed subscheme lies over `q`. -/
theorem baseChangeWitnessProjection_comp :
    baseChangeWitnessProjection q i₂ θ ≫ i₂ = i'₂ ≫ q := by
  rw [baseChangeWitnessProjection, Category.assoc, pullback.condition, ← hθ,
    ← Category.assoc, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

include hθ in
/-- The projection of the base change of the closed subscheme lies over the base. -/
theorem baseChangeWitnessProjection_comp_structureMorphism {C : ChowSituation.{u}}
    (sX : X ⟶ C.S) :
    baseChangeWitnessProjection q i₂ θ ≫ (i₂ ≫ sX) = i'₂ ≫ (q ≫ sX) := by
  rw [← Category.assoc, baseChangeWitnessProjection_comp q i₂ i'₂ θ hθ, Category.assoc]

/-- The identification `X₂ ×_X T ≅ X'₂ ×_{X'} T` of the two base changes of the closed subscheme
by a test scheme `g : T ⟶ X'`: paste `X₂ ×_X T ≅ (X₂ ×_X X') ×_{X'} T` with the transport of the
witness `θ`. -/
def baseChangeWitnessComparison {T : Scheme.{u}} (g : T ⟶ X') :
    pullback i₂ (g ≫ q) ⟶ pullback i'₂ g :=
  (pullbackLeftPullbackSndIso i₂ q g).inv ≫
    (transportPullbackIso (pullback.snd i₂ q) i'₂ θ hθ g).hom

/-- The identification of the two base changes of the closed subscheme by a test scheme is an
isomorphism, being the composite of the pasting isomorphism with the transport of `θ`. -/
instance isIso_baseChangeWitnessComparison {T : Scheme.{u}} (g : T ⟶ X') :
    IsIso (baseChangeWitnessComparison q i₂ i'₂ θ hθ g) := by
  rw [baseChangeWitnessComparison]
  infer_instance

/-- The identification of the two base changes of the closed subscheme is the composite of the
pasting isomorphism with the transport of `θ`: the form in which the pushforward along it splits
into the restriction step of Remark 0F9Z and the transport step. -/
theorem baseChangeWitnessComparison_eq {T : Scheme.{u}} (g : T ⟶ X') :
    (pullbackLeftPullbackSndIso i₂ q g).inv ≫
        (transportPullbackIso (pullback.snd i₂ q) i'₂ θ hθ g).hom =
      baseChangeWitnessComparison q i₂ i'₂ θ hθ g :=
  rfl

/-- The identification of the two base changes of the closed subscheme lies over the test
scheme. -/
@[reassoc]
theorem baseChangeWitnessComparison_comp_snd {T : Scheme.{u}} (g : T ⟶ X') :
    baseChangeWitnessComparison q i₂ i'₂ θ hθ g ≫ pullback.snd i'₂ g =
      pullback.snd i₂ (g ≫ q) := by
  rw [baseChangeWitnessComparison, Category.assoc, transportPullbackIso_hom_snd,
    Iso.inv_comp_eq, pullbackLeftPullbackSndIso_hom_snd]

/-- The identification of the two base changes of the closed subscheme lies over the projection
`X'₂ ⟶ X₂` on the first factor. -/
@[reassoc]
theorem baseChangeWitnessComparison_comp_fst {T : Scheme.{u}} (g : T ⟶ X') :
    baseChangeWitnessComparison q i₂ i'₂ θ hθ g ≫
        (pullback.fst i'₂ g ≫ baseChangeWitnessProjection q i₂ θ) =
      pullback.fst i₂ (g ≫ q) := by
  rw [baseChangeWitnessComparison, baseChangeWitnessProjection,
    Category.assoc, transportPullbackIso_hom_fst_assoc, Iso.hom_inv_id_assoc, Iso.inv_comp_eq,
    pullbackLeftPullbackSndIso_hom_fst]

include hθ in
/-- The identification of the two base changes of the closed subscheme lies over the base. -/
theorem baseChangeWitnessComparison_comp_structureMorphism {C : ChowSituation.{u}}
    (sX : X ⟶ C.S) {T : Scheme.{u}} (g : T ⟶ X') :
    baseChangeWitnessComparison q i₂ i'₂ θ hθ g ≫
        (pullback.fst i'₂ g ≫ (i'₂ ≫ (q ≫ sX))) =
      pullback.fst i₂ (g ≫ q) ≫ (i₂ ≫ sX) :=
  calc baseChangeWitnessComparison q i₂ i'₂ θ hθ g ≫
          (pullback.fst i'₂ g ≫ (i'₂ ≫ (q ≫ sX)))
      = (baseChangeWitnessComparison q i₂ i'₂ θ hθ g ≫
          (pullback.fst i'₂ g ≫ baseChangeWitnessProjection q i₂ θ)) ≫ (i₂ ≫ sX) := by
        rw [← baseChangeWitnessProjection_comp_structureMorphism q i₂ i'₂ θ hθ sX]
        simp
    _ = pullback.fst i₂ (g ≫ q) ≫ (i₂ ≫ sX) := by
        rw [baseChangeWitnessComparison_comp_fst q i₂ i'₂ θ hθ g]

/-- The two base changes of a closed subscheme by a test scheme have the same pushforward to that
test scheme, after the identification of Stacks 0GUG: `i'_{2,*}α' = i_{2,*}(Φ^{-1}α')` where `Φ`
is `Stacks.Chow.baseChangeWitnessComparison`. The target of the pushforward is written
with the structure morphism `(g ≫ q) ≫ sX` of the test scheme, as the cap operations of the
unprimed class require. -/
theorem closedSubschemeTestPushforward_baseChange {C : ChowSituation.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] [LocallyOfFiniteType q] [IsClosedImmersion i₂]
    [LocallyOfFiniteType i₂] [IsClosedImmersion i'₂] [LocallyOfFiniteType i'₂] {T : Scheme.{u}}
    (g : T ⟶ X') [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (pullback.fst i'₂ g ≫ (i'₂ ≫ (q ≫ sX))) k) :
    chowGroupCongr C (Category.assoc g q sX).symm k
        (closedSubschemeTestPushforward C (q ≫ sX) i'₂ g k α) =
      closedSubschemeTestPushforward C sX i₂ (g ≫ q) k
        (chowPushforwardOfIsClosedImmersion C (pullback.fst i'₂ g ≫ (i'₂ ≫ (q ≫ sX)))
          (pullback.fst i₂ (g ≫ q) ≫ (i₂ ≫ sX))
          (inv (baseChangeWitnessComparison q i₂ i'₂ θ hθ g))
          (by rw [IsIso.inv_comp_eq]
              exact (baseChangeWitnessComparison_comp_structureMorphism q i₂ i'₂ θ hθ
                sX g).symm) k
          α) := by
  have hpq : pullback.snd i'₂ g =
      inv (baseChangeWitnessComparison q i₂ i'₂ θ hθ g) ≫ pullback.snd i₂ (g ≫ q) := by
    rw [IsIso.eq_inv_comp, baseChangeWitnessComparison_comp_snd q i₂ i'₂ θ hθ g]
  rw [closedSubschemeTestPushforward_eq, closedSubschemeTestPushforward_eq,
    chowGroupCongr_chowPushforwardOfIsClosedImmersion_target C
      (pullback.fst i'₂ g ≫ (i'₂ ≫ (q ≫ sX))) (Category.assoc g q sX).symm (pullback.snd i'₂ g)
      (pullbackSnd_comp_structureMorphism_eq C (i'₂ ≫ (q ≫ sX)) (q ≫ sX) i'₂ rfl g)
      (by rw [Category.assoc]
          exact pullbackSnd_comp_structureMorphism_eq C (i'₂ ≫ (q ≫ sX)) (q ≫ sX) i'₂ rfl g),
    chowPushforwardOfIsClosedImmersion_comp_eq C _ _ _ _ _ _ hpq.symm _ _ _ k]

end Comparison

/-! ### Stacks 0GUG -/

section BaseChange

variable {C : ChowSituation.{u}} {G : GysinSystem C} {X X₁ X₂ X' X'₁ X'₂ : Scheme.{u}}
  {sX : X ⟶ C.S} [LocallyOfFiniteType sX]
  {i₁ : X₁ ⟶ X} [IsClosedImmersion i₁] [LocallyOfFiniteType i₁]
  {i₂ : X₂ ⟶ X} [IsClosedImmersion i₂] [LocallyOfFiniteType i₂]
  (q : X' ⟶ X) [LocallyOfFiniteType q]
  {i'₁ : X'₁ ⟶ X'} [IsClosedImmersion i'₁] [LocallyOfFiniteType i'₁]
  {i'₂ : X'₂ ⟶ X'} [IsClosedImmersion i'₂] [LocallyOfFiniteType i'₂]
  {p : ℤ}

/-- **Stacks 0GUG, the content.** The restriction (Remark 0F9Z) of the class `P'_p(E₂)`, resp.
`c'_p(E₂)`, of Stacks 0F9H along `q : X' ⟶ X`, transported along the identification
`X₂ ×_X X' ≅ X'₂`, satisfies the characterization of Stacks 0F9H for the base-changed
decomposition `X' = X'₁ ∪ X'₂` and the restricted ambient Chern class — the latter being the
ambient Chern class of the pullback `E'₂` of `E₂`.

Nothing beyond the characterization of the unprimed class is used, which is the source's proof
"immediate from the characterization of these classes in Lemma 0F9H". -/
theorem isClosedCoverChernClass_bivariantTransport_bivariantRestriction
    (θ₁ : pullback i₁ q ≅ X'₁) (hθ₁ : θ₁.hom ≫ i'₁ = pullback.snd i₁ q)
    (θ₂ : pullback i₂ q ≅ X'₂) (hθ₂ : θ₂.hom ≫ i'₂ = pullback.snd i₂ q)
    (hgys : G.IsNaturalUnderBaseChangeIso) (amb : ChernCapFamily C (i₂ ≫ sX) p)
    (c : BivariantClass C G (i₂ ≫ sX) sX i₂ rfl p)
    (hc : IsClosedCoverChernClass C G sX i₁ i₂ p amb c) :
    IsClosedCoverChernClass C G (q ≫ sX) i'₁ i'₂ p
      (ChernCapFamily.restrict C (i₂ ≫ sX) (i'₂ ≫ (q ≫ sX))
        (baseChangeWitnessProjection q i₂ θ₂)
        (baseChangeWitnessProjection_comp_structureMorphism q i₂ i'₂ θ₂ hθ₂ sX) p amb)
      (bivariantTransport C G (pullback.fst i₂ q ≫ (i₂ ≫ sX)) (i'₂ ≫ (q ≫ sX)) (q ≫ sX)
        (pullback.snd i₂ q)
        (pullbackSnd_comp_structureMorphism_eq C (i₂ ≫ sX) sX i₂ rfl q) i'₂ rfl θ₂ hθ₂ p hgys
        (bivariantRestriction C G (i₂ ≫ sX) sX i₂ rfl q p hgys c)) := by
  have hprojbase :=
    baseChangeWitnessProjection_comp_structureMorphism q i₂ i'₂ θ₂ hθ₂ sX
  constructor
  · intro T g _ k α
    have hΦbase :=
      baseChangeWitnessComparison_comp_structureMorphism q i₂ i'₂ θ₂ hθ₂ sX g
    have hcc := ChernCapFamily.comp_comp_eq C (i₂ ≫ sX) (i'₂ ≫ (q ≫ sX))
      (baseChangeWitnessProjection q i₂ θ₂) hprojbase (pullback.fst i'₂ g)
    have hΦfst : baseChangeWitnessComparison q i₂ i'₂ θ₂ hθ₂ g ≫
        ((pullback.fst i'₂ g ≫ baseChangeWitnessProjection q i₂ θ₂) ≫ (i₂ ≫ sX)) =
        pullback.fst i₂ (g ≫ q) ≫ (i₂ ≫ sX) := by
      rw [← Category.assoc, baseChangeWitnessComparison_comp_fst q i₂ i'₂ θ₂ hθ₂ g]
    have hinner : chowPushforwardOfIso C (pullback.fst i₂ (g ≫ q) ≫ (i₂ ≫ sX))
        ((pullback.fst i'₂ g ≫ baseChangeWitnessProjection q i₂ θ₂) ≫ (i₂ ≫ sX))
        (baseChangeWitnessComparison q i₂ i'₂ θ₂ hθ₂ g) hΦfst k
        (chowPushforwardOfIsClosedImmersion C (pullback.fst i'₂ g ≫ (i'₂ ≫ (q ≫ sX)))
          (pullback.fst i₂ (g ≫ q) ≫ (i₂ ≫ sX))
          (inv (baseChangeWitnessComparison q i₂ i'₂ θ₂ hθ₂ g))
          (by rw [IsIso.inv_comp_eq]; exact hΦbase.symm) k α) =
        chowGroupCongr C hcc.symm k α := by
      rw [chowPushforwardOfIso_eq_chowPushforwardOfIsClosedImmersion,
        chowPushforwardOfIsClosedImmersion_comp_eq C _ _ _ _ _ _ (IsIso.inv_hom_id _) _ _
          ((Category.id_comp _).trans hcc) k,
        ← chowPushforwardOfIso_eq_chowPushforwardOfIsClosedImmersion,
        chowPushforwardOfIso_id_eq_chowGroupCongr]
    rw [bivariantTransport_cap, bivariantTransportCap_apply, bivariantRestriction_cap,
      bivariantRestrictionCap_apply,
      closedSubschemeTestPushforward_baseChange q i₂ i'₂ θ₂ hθ₂ sX g k α,
      hc.1 (g ≫ q) k,
      chowPushforwardOfIso_comp_apply C (pullback.fst i₂ (g ≫ q) ≫ (i₂ ≫ sX))
        (pullback.fst (pullback.snd i₂ q) g ≫ (pullback.fst i₂ q ≫ (i₂ ≫ sX)))
        (pullback.fst i'₂ g ≫ (i'₂ ≫ (q ≫ sX))) (pullbackLeftPullbackSndIso i₂ q g).inv
        (transportPullbackIso (pullback.snd i₂ q) i'₂ θ₂ hθ₂ g).hom _ _ (k - p),
      chowPushforwardOfIso_congr_apply C (pullback.fst i₂ (g ≫ q) ≫ (i₂ ≫ sX))
        (pullback.fst i'₂ g ≫ (i'₂ ≫ (q ≫ sX)))
        ((pullbackLeftPullbackSndIso i₂ q g).inv ≫
          (transportPullbackIso (pullback.snd i₂ q) i'₂ θ₂ hθ₂ g).hom)
        (baseChangeWitnessComparison q i₂ i'₂ θ₂ hθ₂ g)
        (baseChangeWitnessComparison_eq q i₂ i'₂ θ₂ hθ₂ g) _ hΦbase (k - p),
      ChernCapFamily.restrict_cap,
      ← chowGroupCongr_chowPushforwardOfIso_target C
        (pullback.fst i₂ (g ≫ q) ≫ (i₂ ≫ sX)) hcc
        (baseChangeWitnessComparison q i₂ i'₂ θ₂ hθ₂ g) hΦfst hΦbase (k - p),
      amb.cap_naturality (pullback.fst i₂ (g ≫ q))
        (pullback.fst i'₂ g ≫ baseChangeWitnessProjection q i₂ θ₂)
        (baseChangeWitnessComparison q i₂ i'₂ θ₂ hθ₂ g)
        (baseChangeWitnessComparison_comp_fst q i₂ i'₂ θ₂ hθ₂ g) k, hinner]
  · intro T g _ k α
    rw [bivariantTransport_cap, bivariantTransportCap_apply, bivariantRestriction_cap,
      bivariantRestrictionCap_apply,
      closedSubschemeTestPushforward_baseChange q i₁ i'₁ θ₁ hθ₁ sX g k α, hc.2 (g ≫ q) k,
      map_zero, map_zero]

/-- **Stacks 0GUG.** In the setting of Stacks 0F9H let `q : X' ⟶ X` be a morphism locally of
finite type, let `X' = X'₁ ∪ X'₂` be the base change of the decomposition, witnessed by
`θⱼ : Xⱼ ×_X X' ≅ X'ⱼ` over `X'`, and let `E'₂` be the pullback of `E₂`, so that its ambient
Chern class is the restriction of that of `E₂`. Then the class `P'_p(E'₂)`, resp. `c'_p(E'₂)` in
`A^p(X'₂ ⟶ X')` built by Stacks 0F9H from `X' = X'₁ ∪ X'₂` and `E'₂` is the restriction (Remark
0F9Z) of `P'_p(E₂)`, resp. `c'_p(E₂)` in `A^p(X₂ ⟶ X)`.

The transport along `θ₂` is needed only because `Stacks.Chow.bivariantRestriction` produces a
class for the chosen fibre product `X₂ ×_X X' ⟶ X'`, whereas the class of the tag is one for
`X'₂ ⟶ X'`; the tag identifies the two silently.

The hypotheses are those of the ambient Lemma 0F9H: the two classes, each satisfying the
characterization `Stacks.Chow.IsClosedCoverChernClass`, and the fact that the characterization
determines a class at `X'`, which is the word "characterized" in Stacks 0F9H and the only place
its hypothesis `X = X₁ ∪ X₂` is used. See the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.ClosedCoverChernBaseChange`. -/
theorem closedCoverChern_eq_bivariantTransport_bivariantRestriction
    (θ₁ : pullback i₁ q ≅ X'₁) (hθ₁ : θ₁.hom ≫ i'₁ = pullback.snd i₁ q)
    (θ₂ : pullback i₂ q ≅ X'₂) (hθ₂ : θ₂.hom ≫ i'₂ = pullback.snd i₂ q)
    (hgys : G.IsNaturalUnderBaseChangeIso) (amb : ChernCapFamily C (i₂ ≫ sX) p)
    (c : BivariantClass C G (i₂ ≫ sX) sX i₂ rfl p)
    (hc : IsClosedCoverChernClass C G sX i₁ i₂ p amb c)
    (c' : BivariantClass C G (i'₂ ≫ (q ≫ sX)) (q ≫ sX) i'₂ rfl p)
    (hc' : IsClosedCoverChernClass C G (q ≫ sX) i'₁ i'₂ p
      (ChernCapFamily.restrict C (i₂ ≫ sX) (i'₂ ≫ (q ≫ sX))
        (baseChangeWitnessProjection q i₂ θ₂)
        (baseChangeWitnessProjection_comp_structureMorphism q i₂ i'₂ θ₂ hθ₂ sX) p amb) c')
    (huniq : ClosedCoverChernClassUnique C G (q ≫ sX) i'₁ i'₂ p
      (ChernCapFamily.restrict C (i₂ ≫ sX) (i'₂ ≫ (q ≫ sX))
        (baseChangeWitnessProjection q i₂ θ₂)
        (baseChangeWitnessProjection_comp_structureMorphism q i₂ i'₂ θ₂ hθ₂ sX) p amb)) :
    c' =
      bivariantTransport C G (pullback.fst i₂ q ≫ (i₂ ≫ sX)) (i'₂ ≫ (q ≫ sX)) (q ≫ sX)
        (pullback.snd i₂ q)
        (pullbackSnd_comp_structureMorphism_eq C (i₂ ≫ sX) sX i₂ rfl q) i'₂ rfl θ₂ hθ₂ p hgys
        (bivariantRestriction C G (i₂ ≫ sX) sX i₂ rfl q p hgys c) :=
  huniq _ _ hc'
    (isClosedCoverChernClass_bivariantTransport_bivariantRestriction q θ₁ hθ₁ θ₂ hθ₂ hgys amb c hc)

end BaseChange

end Stacks.Chow

end
