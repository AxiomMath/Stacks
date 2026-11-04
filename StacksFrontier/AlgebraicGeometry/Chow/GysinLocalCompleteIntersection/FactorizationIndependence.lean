module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection
public import StacksFrontier.AlgebraicGeometry.Divisors.Relative.SmoothSection
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.ImmersionIntoSmooth
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularIdealSheaf.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RegularImmersionComposition
public import StacksCore.Tactic.StacksAttribute

/-!
# Independence of the Gysin map of a local complete intersection morphism on its factorization

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `f : X ⟶ Y` be a
local complete intersection morphism of schemes locally of finite type over `S`. Stacks 0FF3
attaches to a factorization `f = g ∘ i` with `i : X ⟶ P` an immersion and `g : P ⟶ Y` smooth the
bivariant class

  `f^! = i^! ∘ g^* ∈ A^*(X ⟶ Y)^∧`,

and Stacks 0FF2 asserts that this class does not depend on the factorization chosen. The proof of
Stacks 0FF2 has two geometric steps, and both are carried out here:

* *the common refinement.* Two factorizations `f = g ∘ i` through `P` and `f = g' ∘ i'` through
  `P'` are both refined by the factorization through `P ×_Y P'`, whose immersion is `(i, i')` and
  whose smooth morphism is either projection followed by `g`, respectively `g'`. Independence
  therefore reduces to the case of two factorizations one of which refines the other, that is,
  to a *single* smooth morphism `p : P' ⟶ P` with `i' ≫ p = i` and `p ≫ g = g'`.

* *the cartesian diagram of the refined case.* Given such a `p`, the fibre product `X ×_P P'` of
  `i` along `p` carries a smooth retraction `p̄ : X ×_P P' ⟶ X`, the base change
  `j : X ×_P P' ⟶ P'` of `i` along `p`, and the section `s = (1, i') : X ⟶ X ×_P P'` of `p̄`,
  which satisfy `i' = s ≫ j`. Both `j` and `s` are regular immersions — `j` by flat base change
  of the regularity of `i` (Stacks 067P), `s` because it is a section of a smooth morphism
  (Stacks 067R) — which is what makes the Gysin classes `j^!` and `s^!` of section 42.54 of the
  Stacks Project available in the Stacks Project's argument.

The regularity of the immersion in *any* factorization of an lci morphism is also proved here,
from Stacks 069G.

## Main definitions

* `Stacks.Chow.SmoothFactorization` — the factorization datum of Stacks 0FF3: a scheme `P`, an
  immersion `X ⟶ P`, a smooth morphism `P ⟶ Y` and the identification of their composite
  with `f`.
* `Stacks.Chow.SmoothFactorization.Refines` — one factorization refines another, by a smooth
  morphism of the intermediate schemes compatible with both the immersions and the smooth
  morphisms.
* `Stacks.Chow.SmoothFactorization.commonRefinement` — the factorization through `P ×_Y P'`.
* `Stacks.Chow.SmoothFactorization.refinementAmbient`,
  `Stacks.Chow.SmoothFactorization.refinementRetraction`,
  `Stacks.Chow.SmoothFactorization.refinementProj`,
  `Stacks.Chow.SmoothFactorization.refinementSection` — the scheme `X ×_P P'` and the morphisms
  `p̄`, `j` and `s` of the diagram of the refined case.

## Main results

* `Stacks.Chow.SmoothFactorization.exists_refines_both` — the first step of the proof of
  Stacks 0FF2: any two factorizations of `f` are refined by a common one.
* `Stacks.Chow.SmoothFactorization.isKoszulRegularImmersion` — the immersion of a factorization
  of a local complete intersection morphism is Koszul-regular, by Stacks 069G.
* `Stacks.Chow.SmoothFactorization.isPullback_refinement`,
  `Stacks.Chow.SmoothFactorization.refinementSection_comp_retraction`,
  `Stacks.Chow.SmoothFactorization.refinementSection_comp_proj`,
  `Stacks.Chow.SmoothFactorization.isKoszulRegularImmersion_refinementProj`,
  `Stacks.Chow.SmoothFactorization.isRegularImmersion_refinementSection` — the second step of the
  proof of Stacks 0FF2: the cartesian diagram of the refined case, with the regularity of its two
  immersions.

## Implementation notes

### What is covered and what is not

The bivariant class `f^!` itself is *not* constructed in this repository, so the conclusion of
Stacks 0FF2 cannot be stated here. Its two inputs are both missing. The flat pullback class
`g^*` is `Stacks.Chow.flatPullbackBivariantClass` (Stacks 0B78) and is available, but the Gysin
class `i^! = c(X ⟶ P, 𝒩_{X/P})` of section 42.54 of the Stacks Project is constructed in the
proof of Stacks 0FBK out of the localized Chern classes of a perfect object, which are not in the
repository — `Stacks.Chow.totalLocalizedChernClass` takes them as parameters — and neither
Stacks 0FBK nor Stacks 0FBJ's bivariant class is present. Composition of bivariant classes is
available only as the characterizing predicate
`Stacks.Chow.IsBivariantClassComposition` (Stacks 0FE0), with no identity class and no
associativity, so the Stacks Project's chain
`(i')^! ∘ p^* = s^! ∘ j^! ∘ p^* = s^! ∘ p̄^* ∘ i^! = i^!` — which uses Stacks 0FF0, Stacks 0FBK,
Stacks 0F9Z and Stacks 0FF1 — cannot be written down either.

What *is* complete is the geometry those lemmas are applied to, and that is what is proved below.
Nothing here assumes any form of the conclusion of Stacks 0FF2: no bivariant class occurs in this
file at all.

### The reduction principle

`Stacks.Chow.SmoothFactorization.eq_of_refines_invariant` records the shape of the first step of
the argument for an arbitrary assignment of values to factorizations. It is deliberately **not**
tagged with Stacks 0FF2: its hypothesis, that the assignment agrees on a refining pair, is the
refined case of Stacks 0FF2's own conclusion, and a tagged statement carrying it would be
circular. It is stated because it makes precise what remains to be proved once `i^!` exists,
namely the refined case alone.

### Details

`Stacks.Chow.GysinMapExists` of Stacks 0FF3 is the propositional truncation of
`Stacks.Chow.SmoothFactorization`; `Stacks.Chow.gysinMapExists_iff_nonempty` identifies the two.
The immersion and smoothness fields are registered as instances, so that `F.imm` and `F.proj`
carry their properties without further `letI`.

The refinement relation is stated with the smooth morphism as an existential witness rather than
as structure, because the two steps above use it only through a chosen witness and because
`Stacks.Chow.SmoothFactorization.Refines.trans` is then the composition of witnesses. Refinement
is reflexive and transitive but not symmetric, and the common refinement of Stacks 0FF2's first
step is a genuine third factorization: the projections `P ×_Y P' ⟶ P` and `P ×_Y P' ⟶ P'` are
base changes of the smooth `g'` and `g` respectively, and the immersion `(i, i')` is an immersion
because composing it with the projection to `P` returns `i`.

Stacks 069G enters as
`AlgebraicGeometry.isKoszulRegularImmersion_of_isLocalCompleteIntersectionMorphism`,
whose immersion is one of an *open* of the source; it is applied to the top open and transported
back along `AlgebraicGeometry.Scheme.topIso`. That statement carries the Koszul case of
Stacks 0693 as the hypothesis `AlgebraicGeometry.KoszulRegularCompSmooth`, which is therefore a
hypothesis of `Stacks.Chow.SmoothFactorization.isKoszulRegularImmersion` as well.

Regularity of `j` is the Koszul-regular part of Stacks 067P, applied to the flat morphism `p`;
regularity of `s` is Stacks 067R, applied to the smooth morphism `p̄` of which `s` is a section.
The first is stated for Koszul-regularity, which is what Stacks 069G supplies and what section
42.54 of the Stacks Project needs; the second is stated for regularity, which is what
Stacks 067R gives.

## References

* [Stacks Project, Tag 0FF2](https://stacks.math.columbia.edu/tag/0FF2)
* [Stacks Project, Tag 0FF3](https://stacks.math.columbia.edu/tag/0FF3)
* [Stacks Project, Tag 0FF0](https://stacks.math.columbia.edu/tag/0FF0)
* [Stacks Project, Tag 0FF1](https://stacks.math.columbia.edu/tag/0FF1)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
* [Stacks Project, Tag 02RD](https://stacks.math.columbia.edu/tag/02RD)
* [Stacks Project, Tag 069F](https://stacks.math.columbia.edu/tag/069F)
* [Stacks Project, Tag 069G](https://stacks.math.columbia.edu/tag/069G)
* [Stacks Project, Tag 067P](https://stacks.math.columbia.edu/tag/067P)
* [Stacks Project, Tag 067R](https://stacks.math.columbia.edu/tag/067R)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace Stacks.Chow

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-! ### The factorization datum -/

/-- The factorization datum of **Stacks 0FF3**: a scheme `P`, an immersion `i : X ⟶ P`, a smooth
morphism `g : P ⟶ Y` and an identification of `g ∘ i` with `f`. Stacks 0FF2 asserts that the
Gysin class built from such a datum depends only on `f`. -/
structure SmoothFactorization (f : X ⟶ Y) where
  /-- The intermediate scheme `P`. -/
  ambient : Scheme.{u}
  /-- The immersion `i : X ⟶ P`. -/
  imm : X ⟶ ambient
  /-- The smooth morphism `g : P ⟶ Y`. -/
  proj : ambient ⟶ Y
  /-- The morphism `i` is an immersion. -/
  isImmersion : IsImmersion imm
  /-- The morphism `g` is smooth. -/
  isSmooth : Smooth proj
  /-- The factorization `f = g ∘ i`. -/
  imm_proj : imm ≫ proj = f

attribute [instance] SmoothFactorization.isImmersion SmoothFactorization.isSmooth

/-- A factorization of `f` as an immersion followed by a smooth morphism witnesses the existence
condition of Stacks 0FF3. -/
theorem SmoothFactorization.gysinMapExists (F : SmoothFactorization f) : GysinMapExists f :=
  ⟨F.ambient, F.imm, F.proj, F.isImmersion, F.isSmooth, F.imm_proj⟩

/-- The existence condition of Stacks 0FF3 is the propositional truncation of the type of
factorizations of `f` as an immersion followed by a smooth morphism. -/
theorem gysinMapExists_iff_nonempty (f : X ⟶ Y) :
    GysinMapExists f ↔ Nonempty (SmoothFactorization f) := by
  constructor
  · rintro ⟨P, i, g, hi, hg, hcomp⟩
    exact ⟨⟨P, i, g, hi, hg, hcomp⟩⟩
  · rintro ⟨F⟩
    exact F.gysinMapExists

/-! ### Regularity of the immersion of a factorization -/

/-- Koszul-regularity transports along an equality of immersions. The instance argument of
`IsKoszulRegularImmersion` makes the corresponding rewrite fail to compute its motive. -/
private theorem isKoszulRegularImmersion_of_eq {Z W : Scheme.{u}} {a b : Z ⟶ W} [IsImmersion a]
    [IsImmersion b] (h : a = b) (ha : IsKoszulRegularImmersion a) :
    IsKoszulRegularImmersion b := by
  subst h
  exact ha

/-- **Stacks 069G, for a factorization of a local complete intersection morphism.** The immersion
`i : X ⟶ P` of a factorization `f = g ∘ i` of a local complete intersection morphism `f` is a
Koszul-regular immersion. This is what makes the Gysin class `i^!` of section 42.54 of the Stacks
Project available, and it is the reason Stacks 0FF2 need not assume regularity of the immersion.

Stacks 069G is stated for an immersion of an open of the source; it is applied here to the top
open and transported back along `AlgebraicGeometry.Scheme.topIso`. The Koszul case of Stacks 0693
is a hypothesis of Stacks 069G in this repository, hence of this statement. -/
@[stacks 0FF2 "regularity of the immersion of a factorization of an lci morphism, which the \
statement of Stacks 0FF2 leaves implicit; Stacks 069G enters through its repository form, so the \
Koszul case of Stacks 0693 is carried as `hcompSmooth`", sga "6 VIII 1.2"]
theorem SmoothFactorization.isKoszulRegularImmersion
    (hcompSmooth : AlgebraicGeometry.KoszulRegularCompSmooth.{u}) (F : SmoothFactorization f)
    (hf : IsLocalCompleteIntersectionMorphism f) : IsKoszulRegularImmersion F.imm := by
  have htop : IsKoszulRegularImmersion ((⊤ : X.Opens).ι ≫ F.imm) :=
    AlgebraicGeometry.isKoszulRegularImmersion_of_isLocalCompleteIntersectionMorphism
      hcompSmooth f F.proj ⊤ ((⊤ : X.Opens).ι ≫ F.imm) hf (by rw [Category.assoc, F.imm_proj])
  have hinv : IsKoszulRegularImmersion (X.topIso.inv ≫ (⊤ : X.Opens).ι ≫ F.imm) :=
    Stacks.AlgebraicGeometry.isKoszulRegularImmersion_comp X.topIso.inv _
      (isKoszulRegularImmersion_of_isOpenImmersion _) htop
  exact isKoszulRegularImmersion_of_eq
    (by rw [← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp]) hinv

/-! ### Refinement of factorizations -/

/-- One factorization `F'` of `f` *refines* another, `F`, when there is a smooth morphism
`p : P' ⟶ P` of their intermediate schemes with `i' ≫ p = i` and `p ≫ g = g'`. This is the
situation to which the first step of the proof of Stacks 0FF2 reduces the independence of `f^!`:
there `(g')^* = p^* ∘ g^*` by Stacks 02RD, so only `i^! = (i')^! ∘ p^*` is left to prove. -/
def SmoothFactorization.Refines (F' F : SmoothFactorization f) : Prop :=
  ∃ p : F'.ambient ⟶ F.ambient, Smooth p ∧ F'.imm ≫ p = F.imm ∧ p ≫ F.proj = F'.proj

/-- Every factorization refines itself, by the identity of its intermediate scheme. -/
theorem SmoothFactorization.Refines.refl (F : SmoothFactorization f) : F.Refines F :=
  ⟨𝟙 F.ambient, inferInstance, Category.comp_id _, Category.id_comp _⟩

/-- Refinement is transitive: the witnesses compose. -/
theorem SmoothFactorization.Refines.trans {F F' F'' : SmoothFactorization f}
    (h' : F''.Refines F') (h : F'.Refines F) : F''.Refines F := by
  obtain ⟨q, hq, hqimm, hqproj⟩ := h'
  obtain ⟨p, hp, hpimm, hpproj⟩ := h
  refine ⟨q ≫ p, inferInstance, ?_, ?_⟩
  · rw [← Category.assoc, hqimm, hpimm]
  · rw [Category.assoc, hpproj, hqproj]

/-! ### The common refinement -/

section CommonRefinement

variable (F F' : SmoothFactorization f)

/-- The factorization of `f` through `P ×_Y P'`, which refines both `F` and `F'`. Its immersion is
the morphism `(i, i')` induced by the two immersions, and its smooth morphism is the projection to
`P` followed by `g`, which agrees with the projection to `P'` followed by `g'`. -/
def SmoothFactorization.commonRefinement : SmoothFactorization f where
  ambient := pullback F.proj F'.proj
  imm := pullback.lift F.imm F'.imm (by rw [F.imm_proj, F'.imm_proj])
  proj := pullback.fst F.proj F'.proj ≫ F.proj
  isImmersion := by
    have hfst : IsImmersion
        (pullback.lift F.imm F'.imm (by rw [F.imm_proj, F'.imm_proj] :
          F.imm ≫ F.proj = F'.imm ≫ F'.proj) ≫ pullback.fst F.proj F'.proj) := by
      rw [pullback.lift_fst]
      exact F.isImmersion
    exact IsImmersion.of_comp _ (pullback.fst F.proj F'.proj)
  isSmooth := inferInstance
  imm_proj := by rw [← Category.assoc, pullback.lift_fst, F.imm_proj]

/-- The projection `P ×_Y P' ⟶ P` is a smooth morphism identifying the common refinement as a
refinement of `F`. -/
theorem SmoothFactorization.commonRefinement_refines_left :
    (F.commonRefinement F').Refines F := by
  exact ⟨pullback.fst F.proj F'.proj,
    inferInstanceAs (Smooth (pullback.fst F.proj F'.proj)), pullback.lift_fst _ _ _, rfl⟩

/-- The projection `P ×_Y P' ⟶ P'` is a smooth morphism identifying the common refinement as a
refinement of `F'`. -/
theorem SmoothFactorization.commonRefinement_refines_right :
    (F.commonRefinement F').Refines F' := by
  exact ⟨pullback.snd F.proj F'.proj,
    inferInstanceAs (Smooth (pullback.snd F.proj F'.proj)), pullback.lift_snd _ _ _,
    (pullback.condition (f := F.proj) (g := F'.proj)).symm⟩

/-- **Stacks 0FF2, first step.** Any two factorizations of `f` as an immersion followed by a
smooth morphism are refined by a common one, namely the factorization through the fibre product
of their intermediate schemes over `Y`. The independence of `f^!` therefore reduces to the case
of a refining pair. -/
@[stacks 0FF2 "the first step of the proof: any two immersion--smooth factorizations of `f` are \
refined by a common one, through `P ×_Y P'`, which reduces the independence of `f^!` to the case \
of a single refinement `p : P' ⟶ P`"]
theorem SmoothFactorization.exists_refines_both :
    ∃ F'' : SmoothFactorization f, F''.Refines F ∧ F''.Refines F' :=
  ⟨F.commonRefinement F', F.commonRefinement_refines_left F',
    F.commonRefinement_refines_right F'⟩

/-- The first step of the proof of Stacks 0FF2, for an arbitrary assignment of values to
factorizations: an assignment that agrees on every refining pair is constant.

This is **not** Stacks 0FF2 and is deliberately left untagged. Its hypothesis `h` is the refining
case of Stacks 0FF2's own conclusion, so a statement about `f^!` carrying it would assume what
Stacks 0FF2 asserts. It is recorded because it isolates what remains to be proved once the Gysin
class `i^!` of section 42.54 of the Stacks Project is available: the refining case alone, which
the Stacks Project deduces from Stacks 0FF0, Stacks 0FBK and Stacks 0FF1 applied to the diagram
below. -/
theorem SmoothFactorization.eq_of_refines_invariant {α : Type*}
    (Φ : SmoothFactorization f → α)
    (h : ∀ A B : SmoothFactorization f, B.Refines A → Φ B = Φ A) : Φ F = Φ F' := by
  obtain ⟨F'', hleft, hright⟩ := F.exists_refines_both F'
  rw [← h F F'' hleft, h F' F'' hright]

end CommonRefinement

/-! ### The cartesian diagram of the refined case -/

section Refinement

variable (F : SmoothFactorization f) {F' : SmoothFactorization f}
  (p : F'.ambient ⟶ F.ambient)

/-- The scheme `X ×_P P'` of the second step of the proof of Stacks 0FF2, the fibre product of the
immersion `i : X ⟶ P` of `F` along a refinement `p : P' ⟶ P`. -/
abbrev SmoothFactorization.refinementAmbient : Scheme.{u} := pullback F.imm p

/-- The retraction `p̄ : X ×_P P' ⟶ X`, the base change of the refinement `p` along the immersion
`i : X ⟶ P`. It is smooth because `p` is. -/
abbrev SmoothFactorization.refinementRetraction : F.refinementAmbient p ⟶ X :=
  pullback.fst F.imm p

/-- The morphism `j : X ×_P P' ⟶ P'`, the base change of the immersion `i : X ⟶ P` along the
refinement `p`. The Stacks Project identifies `j^!` with the restriction of `i^!` to `P'` by
Stacks 0FBK and Stacks 0F9Z. -/
abbrev SmoothFactorization.refinementProj : F.refinementAmbient p ⟶ F'.ambient :=
  pullback.snd F.imm p

/-- The section `s = (1, i') : X ⟶ X ×_P P'` of the retraction `p̄`, which exists because the
refinement satisfies `i' ≫ p = i`. -/
abbrev SmoothFactorization.refinementSection (hp : F'.imm ≫ p = F.imm) :
    X ⟶ F.refinementAmbient p :=
  pullback.lift (𝟙 X) F'.imm (by rw [Category.id_comp, hp])

/-- The square defining `X ×_P P'` is cartesian: `j` is the base change of the immersion `i` of
`F` along the refinement `p`, and `p̄` is the base change of `p` along `i`. -/
theorem SmoothFactorization.isPullback_refinement :
    IsPullback (F.refinementRetraction p) (F.refinementProj p) F.imm p :=
  IsPullback.of_hasPullback F.imm p

variable (hp : F'.imm ≫ p = F.imm)

/-- The morphism `s` is a section of the retraction `p̄`. -/
@[simp]
theorem SmoothFactorization.refinementSection_comp_retraction :
    F.refinementSection p hp ≫ F.refinementRetraction p = 𝟙 X :=
  pullback.lift_fst _ _ _

/-- Composing the section `s` with `j` returns the immersion `i'` of the refining factorization:
this is the factorization `i' = j ∘ s` to which the Stacks Project applies Stacks 0FF0. -/
@[simp]
theorem SmoothFactorization.refinementSection_comp_proj :
    F.refinementSection p hp ≫ F.refinementProj p = F'.imm :=
  pullback.lift_snd _ _ _

/-- The section `s` is an immersion, admitting the retraction `p̄`. -/
instance SmoothFactorization.isImmersion_refinementSection :
    IsImmersion (F.refinementSection p hp) :=
  Stacks.AlgebraicGeometry.isImmersion_of_comp_eq_id _ (F.refinementRetraction p)
    (F.refinementSection_comp_retraction p hp)

variable [Smooth p]

/-- The retraction `p̄` is smooth, being a base change of the smooth refinement `p`. -/
instance SmoothFactorization.smooth_refinementRetraction :
    Smooth (F.refinementRetraction p) :=
  inferInstance

/-- The morphism `j` is an immersion, being a base change of the immersion `i` of `F`. -/
instance SmoothFactorization.isImmersion_refinementProj :
    IsImmersion (F.refinementProj p) :=
  inferInstance

/-- **Stacks 0FF2, second step: regularity of `j`.** The base change `j : X ×_P P' ⟶ P'` of the
immersion `i` of `F` along the refinement `p` is a Koszul-regular immersion, by the Koszul-regular
part of Stacks 067P: `p` is smooth, hence flat. For a local complete intersection morphism `f` the
hypothesis on `i` is automatic, by
`Stacks.Chow.SmoothFactorization.isKoszulRegularImmersion`. -/
@[stacks 0FF2 "the second step of the proof: the base change `j` of the immersion along the \
refinement is a Koszul-regular immersion, the Koszul-regular part of Stacks 067P; the regularity \
of `i` is the prerequisite `hreg`, supplied for an lci morphism by Stacks 069G"]
theorem SmoothFactorization.isKoszulRegularImmersion_refinementProj
    (hreg : IsKoszulRegularImmersion F.imm) :
    IsKoszulRegularImmersion (F.refinementProj p) :=
  Stacks.AlgebraicGeometry.isKoszulRegularImmersion_pullback_snd_of_flat F.imm p hreg

/-- **Stacks 0FF2, second step: regularity of `s`.** The section `s = (1, i')` of the smooth
retraction `p̄` is a regular immersion, by Stacks 067R. Together with the regularity of `j` this
is what makes both Gysin classes in the Stacks Project's identity `(i')^! = s^! ∘ j^!`
(Stacks 0FF0) available. -/
@[stacks 0FF2 "the second step of the proof: the section `s = (1, i')` of the smooth retraction \
`p̄ : X ×_P P' ⟶ X` is a regular immersion, Stacks 067R"]
theorem SmoothFactorization.isRegularImmersion_refinementSection :
    IsRegularImmersion (F.refinementSection p hp) :=
  Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_section (F.refinementRetraction p)
    (F.refinementSection p hp) (F.refinementSection_comp_retraction p hp)

end Refinement

/-- **Stacks 0FF2, second step, packaged.** For a refining pair of factorizations of `f`, with the
immersion of the coarser one Koszul-regular, the diagram of the second step of the proof of
Stacks 0FF2 exists: a scheme `W = X ×_P P'`, a smooth retraction `p̄ : W ⟶ X`, the base change
`j : W ⟶ P'` of `i` along the refinement, and a section `s : X ⟶ W` of `p̄` with `s ≫ j = i'`,
where `j` is a Koszul-regular immersion and `s` a regular immersion. -/
@[stacks 0FF2 "the second step of the proof, packaged for a refining pair: the cartesian square \
`W = X ×_P P'` with its smooth retraction `p̄`, the base change `j` of the immersion, and the \
section `s` of `p̄` satisfying `i' = s ≫ j`, with `j` Koszul-regular and `s` regular; the \
regularity of the coarser immersion is the prerequisite `hreg`"]
theorem SmoothFactorization.exists_refinement_diagram {F F' : SmoothFactorization f}
    (h : F'.Refines F) (hreg : IsKoszulRegularImmersion F.imm) :
    ∃ (W : Scheme.{u}) (pbar : W ⟶ X) (j : W ⟶ F'.ambient) (s : X ⟶ W),
      Smooth pbar ∧ s ≫ pbar = 𝟙 X ∧ s ≫ j = F'.imm ∧
        ∃ (hj : IsImmersion j) (hs : IsImmersion s),
          (letI := hj; IsKoszulRegularImmersion j) ∧ letI := hs; IsRegularImmersion s := by
  obtain ⟨p, hpsmooth, hp, -⟩ := h
  refine ⟨F.refinementAmbient p, F.refinementRetraction p, F.refinementProj p,
    F.refinementSection p hp, inferInstance, F.refinementSection_comp_retraction p hp,
    F.refinementSection_comp_proj p hp, inferInstance, inferInstance,
    F.isKoszulRegularImmersion_refinementProj p hreg,
    F.isRegularImmersion_refinementSection p hp⟩

end Stacks.Chow

end
