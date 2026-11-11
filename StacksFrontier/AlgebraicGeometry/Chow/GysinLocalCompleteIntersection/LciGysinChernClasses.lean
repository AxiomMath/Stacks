module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.PointClassCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.BivariantClass
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.LciGysinFundamentalClass

/-!
# The Gysin map of a local complete intersection morphism and Chern classes

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `f : X ⟶ Y` be a
local complete intersection morphism of schemes locally of finite type over `S` for which the
Gysin map exists, in the sense of **Stacks 0FF3**. **Stacks 0FF8** is the remark that assembles
three consequences of the lemmas already available:

* **(a)** `f^! ∘ c_i(ℰ) = c_i(f^*ℰ) ∘ f^!`, and likewise for the Chern character, by
  **Stacks 0FF6**;
* **(b)** if `X` and `Y` satisfy the equivalent conditions of **Stacks 0FE3** and `Y` is
  Cohen-Macaulay, then `f^![Y] = [X]`, by **Stacks 0FF7**;
* **(c)** in that case `f^!(c_i(ℰ) ∩ [Y]) = c_i(f^*ℰ) ∩ [X]`, and likewise for the Chern
  character.

This file delivers special cases only: (b) with the excess vanishing assumed, and (a) and (c)
for the flat — in particular the smooth — factor of the factorization `f = i ≫ g`. The full
remark, for the Gysin map of Stacks 0FF3, is proved elsewhere and carries the tag:
(a) is `Stacks.Chow.lciGysinClass_comp_chernClassOfModule` and
`Stacks.Chow.lciGysinClass_comp_chernCharacterOfModule`, (b) is
`Stacks.Chow.lciGysinClass_completedCapDegreeZero_fundamentalClass`, and (c) is
`Stacks.Chow.lciGysinClass_completedCap_chernClassOfModule_cap` and
`Stacks.Chow.lciGysinClass_completedCap_chernCharacterOfModule_cap`.

## Main results

* `Stacks.Chow.bivariantCommute_flatPullbackBivariantClass_chernClassBivariant` — **part (a) for
  the flat factor**: the flat-pullback bivariant class of Stacks 0B78 commutes, in the sense of
  Stacks 0FA2, with the bivariant Chern class `c_j(ℰ) ∈ A^j(Y ⟶ Y)` of Stacks 0B7H.
* `Stacks.Chow.lciGysinCap_fundamentalChowClass_id` — **part (b)**: `f^![Y]_n = [X]_{n-(r-d)}`
  for `f = i ≫ g`, read on `X` itself rather than on the base change `X ×_Y Y`.
* `Stacks.Chow.flatPullbackChow_chernCap_fundamentalChowClass` — **part (c) for the flat
  factor**: `h^*(c_j(t^*ℰ) ∩ [T]_n) = c_j((h ≫ t)^*ℰ) ∩ [T']_{n+m}` for `h : T' ⟶ T` flat of
  relative dimension `m`; for a smooth `h` the left-hand side is the Gysin map of Stacks 0FF3.

## Implementation notes

### Why (a) and (c) are delivered only for the flat factor

The lci Gysin map `f^!` is not constructed in this repository; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection`. Stacks 0FF6, the input of
parts (a) and (c), is carried here by
`Stacks.Chow.bivariantCommute_flatPullbackBivariantClass`, which is the `g^*` half of the
factorization `f = i ≫ g` used by the source: the half the source calls "immediate from the
definition of a bivariant class". The other half — that the Gysin class `i^!` of the regular
immersion commutes with an arbitrary bivariant class — is **Stacks 0FBP**, Lemma 42.54.8 of the
source, which has no carrier in this repository; nor do the tags 0FBK, 0FBL, 0FBM, 0FBN, 0B79
and 02UA that would be needed to construct `f^!` outright. So the statement
`f^! ∘ c_i(ℰ) = c_i(f^*ℰ) ∘ f^!` cannot be reached, and no hypothesis short of the conclusion of
Stacks 0FF6 itself would reach it: by the discussion in
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackCommuting`, no field of
`Stacks.Chow.BivariantClass` relates two bivariant classes, so "an arbitrary bivariant class
commutes with `c_j(ℰ)`" is not a theorem.

Part (c) is in the same position for the same reason, and the two tag attributes below say so.
The Chern *character* is likewise not stated: its bivariant form needs the rationalized bivariant
group, which this repository does not build.

### What part (b) adds to Stacks 0FF7

`Stacks.Chow.lciGysinCap_fundamentalChowClass` proves `f^![Y']_n = [X']_{n'}` for an arbitrary
test scheme `g' : Y' ⟶ Y`, with `[X']` the fundamental class of the base change
`X ×_Y Y'`. Stacks 0FF8 (b) is the case `Y' = Y`, `g' = 𝟙 Y`, and its right-hand side is the
fundamental class of `X` itself. The two are not literally the same statement: the case
`g' = 𝟙 Y` produces the fundamental class of the chosen fibre product `X ×_Y Y`, and
`Stacks.Chow.chowPushforwardOfIso_fundamentalChowClass` is what moves it to `X` along the
projection `pullback.fst f (𝟙 Y)`, which is an isomorphism because `𝟙 Y` is.

### How the Cohen-Macaulay hypothesis and Stacks 0FE3 enter

Exactly as they do in `Stacks.Chow.lciGysinCap_fundamentalChowClass`, whose implementation notes
record this in detail. Hypotheses (2) and (3) of Stacks 0FF7 — that `X` and `Y` satisfy the
conditions of Stacks 0FE3, so that `[Y]` and `[X]` are fundamental classes of a single
δ-dimension — appear as the two δ-dimension bounds `hY` and `hX`; for a Cohen-Macaulay scheme
those conditions hold by `Stacks.Chow.IsLocallyPureDimensional.of_isCohenMacaulay`, the
Cohen-Macaulay case of Stacks 0FE3. Hypothesis (4), Cohen-Macaulayness of `Y` at the generic
points of `X`, is used by the source only to run Stacks 0FEA; neither that nor the going-up
statement it rests on is in this repository, so it is replaced by its consequence, the vanishing
of the excess, which is the hypothesis `hcone`. Carrying `IsCohenMacaulay Y` in addition would
leave a hypothesis that the proof never uses, so it is not carried.

### Transporting the Chern class to the structure morphism the commutation expects

`Stacks.Chow.chernClassBivariant` is a class for the identity of `Y` whose source structure
morphism is `sY`, while `Stacks.Chow.BivariantCommute` expects the source structure morphism of
a class for `f₂ : Z₂ ⟶ Y` to be written `f₂ ≫ sY`. For `f₂ = 𝟙 Y` the two are the same morphism
and not the same term, and `Stacks.Chow.bivariantClassCongrBase` transports across the
difference; `Stacks.Chow.chernClassBivariantOverIdComp` below is the transported class.

## References

* [Stacks Project, Tag 0FF8](https://stacks.math.columbia.edu/tag/0FF8)
* [Stacks Project, Tag 0FF6](https://stacks.math.columbia.edu/tag/0FF6)
* [Stacks Project, Tag 0FF7](https://stacks.math.columbia.edu/tag/0FF7)
* [Stacks Project, Tag 0FE3](https://stacks.math.columbia.edu/tag/0FE3)
* [Stacks Project, Tag 0FF3](https://stacks.math.columbia.edu/tag/0FF3)
* [Stacks Project, Tag 0FBP](https://stacks.math.columbia.edu/tag/0FBP)
* [Stacks Project, Tag 0FA2](https://stacks.math.columbia.edu/tag/0FA2)
* [Stacks Project, Tag 0B7H](https://stacks.math.columbia.edu/tag/0B7H)
* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
* [Stacks Project, Tag 02U8](https://stacks.math.columbia.edu/tag/02U8)
* [Stacks Project, Tag 02RB](https://stacks.math.columbia.edu/tag/02RB)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Transport of a fundamental class along an equality of structure morphisms -/


/-! ### Part (a) for the flat factor -/

section PartA

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (E : Y.Modules) (r : ℕ) (G : GysinSystem C) (cap : HigherChernCapRule C r)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (j : Fin (r + 1))
  (hproper : IdentityCapRule.ProperNaturality C sY (j : ℤ)
    (chernIdentityCapRuleOfRank C sY E r cap j))
  (hflat : IdentityCapRule.FlatNaturality C sY (j : ℤ)
    (chernIdentityCapRuleOfRank C sY E r cap j))
  (hgysin : IdentityCapRule.GysinNaturality C sY (j : ℤ)
    (chernIdentityCapRuleOfRank C sY E r cap j) G)
  (hiso : G.IsNaturalUnderInverseIso)

/-- The bivariant `j`-th Chern class of Stacks 0B7H, read as a class for `𝟙 Y` whose source
structure morphism is written `𝟙 Y ≫ sY` rather than `sY`.

This is the shape `Stacks.Chow.BivariantCommute` expects of a class for a morphism `f₂ : Z₂ ⟶ Y`,
and the two structure morphisms are the same morphism written two ways; the transport is
`Stacks.Chow.bivariantClassCongrBase`. -/
def chernClassBivariantOverIdComp :
    BivariantClass C G (𝟙 Y ≫ sY) sY (𝟙 Y) rfl (j : ℤ) :=
  bivariantClassCongrBase C G (𝟙 Y) (Category.id_comp sY).symm rfl (j : ℤ)
    (chernClassBivariant C sY E r G cap j hproper hflat hgysin hiso)

variable {P : Scheme.{u}} (g : P ⟶ Y) [Smooth g] [LocallyOfFiniteType g] (d : ℕ)
  (hgd : AlgebraicGeometry.RelativeDimension g d) (hdesc : FlatPullbackDescends C)
  (hRG : ProperPushforwardFlatPullbackBaseChange C) (h71 : G.FlatPullbackNaturality d)

/-- **Stacks 0FF8 (a), for the flat factor of the factorization.** The flat-pullback bivariant
class of Stacks 0B78 attached to a smooth morphism `g : P ⟶ Y` of relative dimension `d` commutes,
in the sense of Stacks 0FA2, with the bivariant `j`-th Chern class `c_j(ℰ) ∈ A^j(Y ⟶ Y)` of
Stacks 0B7H.

Stacks 0FF8 (a) asserts `f^! ∘ c_j(ℰ) = c_j(f^*ℰ) ∘ f^!` for the Gysin map of a local complete
intersection morphism `f = i ≫ g`, citing Stacks 0FF6. Stacks 0FF6 is proved in the source by
treating the two factors of the factorization separately, and its carrier in this repository,
`Stacks.Chow.bivariantCommute_flatPullbackBivariantClass`, is the `g^*` factor. This is that
carrier instantiated at the bivariant Chern class, which is the assembly Stacks 0FF8 performs.
The `i^!` factor is Stacks 0FBP and has no carrier here; see the implementation notes.

This is a special case of the factor, not Stacks 0FF8 (a) itself, which is
`Stacks.Chow.lciGysinClass_comp_chernClassOfModule` (and, for the Chern character,
`Stacks.Chow.lciGysinClass_comp_chernCharacterOfModule`), stated for the Gysin map of
Stacks 0FF3; the tag sits there.

Two further caveats on what this is. First, the statement is the commuting form of Stacks 0FA2
rather than the displayed composition `f^! ∘ c_j(ℰ) = c_j(f^*ℰ) ∘ f^!`; the two are equivalent by
`Stacks.Chow.bivariantCommute_iff_cap_eq_of_isBivariantClassComposition`, but rewriting
`res(c_j(ℰ))` as the bivariant Chern class of `g^*ℰ` is a separate identification, which needs
the pseudofunctoriality of pullback of modules against `Stacks.Chow.HigherChernCapRule` and is
not carried out here. Second, the Chern character is not stated. -/
theorem bivariantCommute_flatPullbackBivariantClass_chernClassBivariant :
    BivariantCommute C G sY g (𝟙 Y) (-(d : ℤ)) (j : ℤ)
      (flatPullbackBivariantClass C G (g ≫ sY) sY g rfl d hgd hdesc hRG h71)
      (chernClassBivariantOverIdComp C sY E r G cap j hproper hflat hgysin hiso) :=
  bivariantCommute_flatPullbackBivariantClass C G sY g (𝟙 Y) d hgd hdesc hRG h71 (j : ℤ)
    (chernClassBivariantOverIdComp C sY E r G cap j hproper hflat hgysin hiso)

end PartA

/-! ### Part (b) -/

section PartB

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X P Y N : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sN : N ⟶ C.S) [LocallyOfFiniteType sN]
  (i : X ⟶ P) [IsImmersion i] [LocallyOfFiniteType i] (hi : i ≫ sP = sX)
  (g : P ⟶ Y) [Smooth g] [LocallyOfFiniteType g] (hg : g ≫ sY = sP) (d : ℕ)
  (hgd : AlgebraicGeometry.RelativeDimension g d)
  (q : N ⟶ X) [LocallyOfFiniteType q] (hq : q ≫ sX = sN) (r : ℕ)
  (EC : BivariantClass C G sN sP (q ≫ i) (comp_comp_structureMorphism_eq hq hi) 0)
  (NP : VirtualNormalBundleProjection i q r) (hdesc : FlatPullbackDescends C)
  (hpp : ProperPushforwardDescends C) (hRG : ProperPushforwardFlatPullbackBaseChange C)
  (h71 : G.FlatPullbackNaturality d)

/-- **Stacks 0FF8 (b).** Let `f = i ≫ g` with `i : X ⟶ P` an immersion carrying a virtual normal
bundle of constant rank `r` and `g : P ⟶ Y` smooth of constant relative dimension `d`, so that
the Gysin map exists for `f` in the sense of Stacks 0FF3, and let `f^!` be the Gysin map, entering
as a bivariant class `cf` characterized as `i^! ∘ g^*`. If `dim_δ(Y) ≤ n` and
`dim_δ(X ×_P (P ×_Y Y)) ≤ n + d - r`, then

  `f^![Y]_n = [X]_{n - (r - d)}`

in the Chow group of `X` itself.

This is `Stacks.Chow.lciGysinCap_fundamentalChowClass`, the δ-equidimensional case of
Stacks 0FF7, at the test scheme `g' = 𝟙 Y`, followed by the identification of `X ×_Y Y` with `X`:
the projection `pullback.fst f (𝟙 Y)` is an isomorphism, and pushforward along an isomorphism
over the base carries a fundamental class to a fundamental class by
`Stacks.Chow.chowPushforwardOfIso_fundamentalChowClass`.

The hypotheses are those of `Stacks.Chow.lciGysinCap_fundamentalChowClass`, whose implementation
notes say what each one is and why none of them is the conclusion; see also the implementation
notes above for how the Cohen-Macaulay hypothesis and the conditions of Stacks 0FE3 enter.

This is a special case, with the excess vanishing `hcone` assumed; Stacks 0FF8 (b) itself, for the
Gysin map of Stacks 0FF3 under the conditions of Stacks 0FE3 only, is
`Stacks.Chow.lciGysinClass_completedCapDegreeZero_fundamentalClass`, which carries the tag. -/
theorem lciGysinCap_fundamentalChowClass_id
    (hinj : ∀ {T : Scheme.{u}} (t : T ⟶ P) [LocallyOfFiniteType t] (k : ℤ),
      Function.Injective
        (bundleFlatPullback C sX sN i q hq r NP.flat NP.relativeDimension hdesc t k))
    {ci : BivariantClass C G sX sP i hi (r : ℤ)}
    (hci : IsVirtualNormalGysinClass C G sX sP sN i hi q hq r 0 EC
      (bundleFlatPullback C sX sN i q hq r NP.flat NP.relativeDimension hdesc) NP ci)
    {cf : BivariantClass C G sX sY (i ≫ g) (comp_comp_structureMorphism_eq hi hg)
      ((r : ℤ) + -(d : ℤ))}
    (hcf : IsBivariantClassComposition C G sX sP sY i g hi hg hpp (r : ℤ) (-(d : ℤ)) ci
      (flatPullbackBivariantClass C G sP sY g hg d hgd hdesc hRG h71) cf)
    (n : ℤ) (hY : schemeDeltaDimension C (𝟙 Y ≫ sY) ≤ (n : EInt))
    (hX : schemeDeltaDimension C (pullback.fst i (pullback.fst g (𝟙 Y)) ≫ sX) ≤
      (((n + (d : ℤ)) - (r : ℤ) : ℤ) : EInt))
    (hcone : chowGroupDegreeEquiv C (pullback.fst (q ≫ i) (pullback.fst g (𝟙 Y)) ≫ sN)
        (by omega : (n + (d : ℤ)) - (0 : ℤ) = ((n + (d : ℤ)) - (r : ℤ)) + (r : ℤ))
        (EC.cap (pullback.fst g (𝟙 Y)) (n + (d : ℤ))
          (fundamentalChowClass C (pullback.fst g (𝟙 Y) ≫ sP) (n + (d : ℤ)))) =
      fundamentalChowClass C (pullback.fst (q ≫ i) (pullback.fst g (𝟙 Y)) ≫ sN)
        (((n + (d : ℤ)) - (r : ℤ)) + (r : ℤ))) :
    chowPushforwardOfIso C (pullback.fst (i ≫ g) (𝟙 Y) ≫ sX) sX
        (pullback.fst (i ≫ g) (𝟙 Y)) rfl (n - ((r : ℤ) + -(d : ℤ)))
        (cf.cap (𝟙 Y) n
          (chowGroupCongr C (Category.id_comp sY).symm n (fundamentalChowClass C sY n))) =
      fundamentalChowClass C sX (n - ((r : ℤ) + -(d : ℤ))) := by
  rw [chowGroupCongr_fundamentalChowClass C (Category.id_comp sY).symm n,
    lciGysinCap_fundamentalChowClass C G sX sP sY sN i hi g hg d hgd q hq r EC NP hdesc hpp hRG
      h71 hinj hci hcf (𝟙 Y) n hY hX hcone]
  exact chowPushforwardOfIso_fundamentalChowClass C (pullback.fst (i ≫ g) (𝟙 Y) ≫ sX) sX
    (pullback.fst (i ≫ g) (𝟙 Y)) rfl (n - ((r : ℤ) + -(d : ℤ)))

end PartB

/-! ### Part (c) for the flat factor -/

section PartC

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (E : Y.Modules) (r : ℕ) (cap : HigherChernCapRule C r)
  (hrank : PullbackPreservesRank E r) (j : Fin (r + 1))

/-- **Stacks 0FF8 (c), for the flat factor of the factorization.** Let `ℰ` be finite locally free
of rank `r` on `Y`, let `t : T ⟶ Y` be a test scheme with `dim_δ(T) ≤ n`, and let `h : T' ⟶ T` be
flat of constant relative dimension `m`. Then

  `h^*(c_j(t^*ℰ) ∩ [T]_n) = c_j((h ≫ t)^*ℰ) ∩ [T']_{n+m}`,

the two sides sitting in the degrees `(n - j) + m` and `(n + m) - j`, which are the same integer
written two ways.

This is Stacks 0FF8 (c) for the `g^*` factor of the factorization `f = i ≫ g`. For a *smooth*
`h` the Gysin map of Stacks 0FF3 is flat pullback, by the factorization with `i = 𝟙`, so the
display above is then literally `h^!(c_j(ℰ) ∩ [T]) = c_j(h^*ℰ) ∩ [T']`; the statement is proved
in the flat generality that its two inputs support, which is the generality in which
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackCommuting` carries Stacks 0FF6. Those
inputs are: part (b) for the factor, `h^*[T]_n = [T']_{n+m}`, which is Stacks 02RB on Chow
groups, `Stacks.Chow.flatPullbackChow_fundamentalChowClass`; and part (a) for the factor, the
commutation of the Chern class operations with flat pullback, Stacks 02U8, which is the
hypothesis `hflat` carried here, exactly as `Stacks.Chow.chernClassBivariant` carries it. The lci
case needs Stacks 0FBP; see the implementation notes. The Chern character is not stated.
Stacks 0FF8 (c) itself, for the Gysin map of Stacks 0FF3, is
`Stacks.Chow.lciGysinClass_completedCap_chernClassOfModule_cap` (and
`Stacks.Chow.lciGysinClass_completedCap_chernCharacterOfModule_cap`), which carry the tag.

`Stacks.Chow.chernIdentityCapRule C sY E r cap hrank j` is the rule `α ↦ c_j(u^*ℰ) ∩ α` on the
Chow groups of each test scheme `u : U ⟶ Y`; it unfolds to
`cap (u ≫ sY) ((Scheme.Modules.pullback u).obj E) k j`. -/
theorem flatPullbackChow_chernCap_fundamentalChowClass
    (hflat : IdentityCapRule.FlatNaturality C sY (j : ℤ)
      (chernIdentityCapRule C sY E r cap hrank j))
    {T T' : Scheme.{u}} (t : T ⟶ Y) [LocallyOfFiniteType t] (h : T' ⟶ T)
    [LocallyOfFiniteType h] [AlgebraicGeometry.Flat h] (m : ℕ)
    (hm : AlgebraicGeometry.RelativeDimension h m) (n : ℤ)
    (hdim : schemeDeltaDimension C (t ≫ sY) ≤ (n : EInt))
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C ((h ≫ t) ≫ sY) (t ≫ sY) h
      (by simp [Category.assoc]) m hm n)
    (hfacj : FlatPullbackFactorsThroughRationalEquivalence C ((h ≫ t) ≫ sY) (t ≫ sY) h
      (by simp [Category.assoc]) m hm (n - (j : ℤ))) :
    chernIdentityCapRule C sY E r cap hrank j (h ≫ t) (n + (m : ℤ))
        (fundamentalChowClass C ((h ≫ t) ≫ sY) (n + (m : ℤ))) ≍
      flatPullbackChow C ((h ≫ t) ≫ sY) (t ≫ sY) h (by simp [Category.assoc]) m hm
        (n - (j : ℤ)) hfacj
        (chernIdentityCapRule C sY E r cap hrank j t n (fundamentalChowClass C (t ≫ sY) n)) := by
  have h1 := hflat t h m hm n hfac hfacj (fundamentalChowClass C (t ≫ sY) n)
  rwa [flatPullbackChow_fundamentalChowClass C ((h ≫ t) ≫ sY) (t ≫ sY) h
    (by simp [Category.assoc]) m hm n hfac hdim] at h1

end PartC

end Stacks.Chow

end
