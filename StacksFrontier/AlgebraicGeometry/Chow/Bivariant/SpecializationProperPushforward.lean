module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ProperPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardInvertible

/-!
# The class at infinity is unchanged by a proper modification

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S` and let `b : W ⟶ 𝐏¹_X` be a proper morphism which is an isomorphism over
`𝐀¹_X`. Stacks 0F9J attaches to `b` a canonical class `C ∈ A⁰(W_∞ ⟶ X)`, where `W_∞ ⊆ W` is the
inverse image of the divisor at infinity: on a test scheme `t : T ⟶ X` it sends `α ∈ A_k(T)` to
`i_∞^*β`, for any `β ∈ Z_{k+1}(W_T)` whose restriction over `b^{-1}(𝐀¹_X)` is the flat pullback
of `α`.

Stacks 0FAQ compares two such compactifications. Given a further proper `g : W' ⟶ W` with
`b ∘ g` again an isomorphism over `𝐀¹_X`, and the classes `C' ∈ A⁰(W'_∞ ⟶ X)` and
`C ∈ A⁰(W_∞ ⟶ X)` of Stacks 0F9J, the lemma asserts

  `g_{∞,*} ∘ C' = C`  in  `A⁰(W_∞ ⟶ X)`,

the left side being the proper pushforward of bivariant classes of Stacks 0EPK along the induced
proper morphism `g_∞ : W'_∞ ⟶ W_∞`.

The source proof is the following chain. Lift `α` to `β' ∈ Z_{k+1}(W'_T)` over the affine chart;
then `g_{T,*}β'` is such a lift on `W_T`, so `C ∩ α = i_∞^*(g_{T,*}β')`; and Stacks 02TA turns
that into `g_{∞,T,*}((i'_∞)^*β') = g_{∞,T,*}(C' ∩ α)`, which is the cap operation of
`g_{∞,*} ∘ C'`. That chain is what is carried out below, over the zero-scheme presentation of
the divisor at infinity recorded by `Stacks.Chow.InfinityDivisorPresentation`.

## Main definitions

* `Stacks.Chow.InfinityDivisorPresentation` — the geometry of one test scheme `t : T ⟶ X` that
  the recipe of Stacks 0F9J runs on: the base changes `W_T` and `W'_T`, the proper comparison
  morphism between them, an invertible module with a section whose zero scheme is `(W_∞)_T`, the
  identifications of that zero scheme and of its pullback with the base changes of `W_∞` and of
  `W'_∞`, their compatibility with `g_∞`, and the integral-component case of Stacks 02TA.
* `Stacks.Chow.InfinityDivisorPresentation.gysinCap`,
  `Stacks.Chow.InfinityDivisorPresentation.gysinCap'` — the class `i_∞^*β` of Stacks 0F9J, read
  on the base change of `W_∞` respectively of `W'_∞` through the identification.
* `Stacks.Chow.InfinityDivisorPresentation.comparePushforward` — proper pushforward of cycles
  along `W'_T ⟶ W_T`.

## Implementation notes

### Stacks 0F9J is not in this repository, so its output is a hypothesis

The classes `C` and `C'` that Stacks 0FAQ is *about* are constructed by Stacks 0F9J, and that
construction is absent here: the relative projective line of Stacks 02S5 with its two sections
and its standard affine chart is not available in a form the bivariant machinery can consume. So
`C` and `C'` are arbitrary bivariant classes of degree `p` for `W_∞ ⟶ X` and `W'_∞ ⟶ X`, and
what Stacks 0F9J says about them is carried as the hypotheses `hcapW` and `hcapW'`: on every test
scheme each class caps by the Gysin recipe of that lemma, against the zero-scheme presentation of
the divisor at infinity supplied by `Stacks.Chow.InfinityDivisorPresentation`. These are
*prerequisite* hypotheses — the statement of another tag — and neither mentions `g_∞` nor the
pushforward of Stacks 0EPK, so neither gives the conclusion.

Carrying the recipe rather than the characterizing pushforward identity
`i_{∞,*}(C ∩ α) = i_{0,*}α` of Stacks 0F9J is forced: that identity determines `C ∩ α` only up
to the kernel of `i_{∞,*}`, which is not known to vanish, so it cannot identify two classes. The
source proof uses the recipe too.

### The lift over the affine chart is an abstract predicate

The Gysin recipe of Stacks 0F9J evaluates `i_∞^*` on *any* cycle `β` on `W_T` whose restriction
over the affine chart is the flat pullback of `α`. Writing that condition out needs the affine
chart, hence the projective line, hence exactly what is missing. It therefore enters as two
abstract predicates `ExtW` and `ExtW'`, on cycles on `W_T` and on `W'_T`, together with the two
properties of them the source proof uses:

* `hexists` — every class on the test scheme admits such a lift to `W'_T`. This is Stacks 02RC,
  surjectivity of restriction to an open, which in this repository is
  `Stacks.Chow.chowOpenRestriction_surjective` of
  `StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.LocalizationSequence` for Chow groups;
  the predicate here is on cycles, so the lifting statement is taken as given.
* `hpushExt` — the pushforward along `W'_T ⟶ W_T` of a lift is a lift. This is Stacks 02RG, flat
  pullback against proper pushforward in a cartesian square, available in this repository only
  when both flat legs are isomorphisms
  (`Stacks.Chow.flatPullbackChow_chowPushforwardOfIso`), together with the fact that `g` is an
  isomorphism over the affine chart.

Keeping the predicates abstract makes the theorem *more* general, not less: it holds for any
notion of lift closed under the two properties, and instantiating them with the restriction
condition of Stacks 0F9J gives the lemma. It also keeps the three hypotheses separate, each
recognizable as a distinct absent input, rather than collapsing them into a single statement
pairing a lift on `W'_T` with its image on `W_T`.

### Stacks 02S2 and Stacks 02ST

Proper pushforward on Chow groups, Stacks 0GU8, needs Stacks 02S2 at every morphism it is taken
along; as elsewhere in this repository that `Prop` is quantified, through
`Stacks.Chow.ProperPushforwardDescends`. The Gysin half of the chain is Stacks 02TA, in the form
`Stacks.Chow.gysinHomomorphismOfInvertible_properPushforward`, whose own remaining hypothesis is
the integral-component compatibility of the two first Chern component rules — the part of its
proof that rests on Stacks 02ST. That hypothesis is a field of
`Stacks.Chow.InfinityDivisorPresentation`, since it is a statement about the presentation alone.

### The degree is arbitrary

The lemma is about `A⁰`, but proper pushforward of bivariant classes preserves the degree and
the Gysin recipe shifts it by one whatever the degree is, so nothing below uses `p = 0`. The
theorem is stated for an arbitrary degree `p`, of which Stacks 0FAQ is the case `p = 0`; this
also keeps `k - p` as the single degree appearing, in place of the transports along `k - 0 = k`
that fixing `p = 0` would introduce.

## References

* [Stacks Project, Tag 0FAQ](https://stacks.math.columbia.edu/tag/0FAQ)
* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 0EPK](https://stacks.math.columbia.edu/tag/0EPK)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
* [Stacks Project, Tag 02RC](https://stacks.math.columbia.edu/tag/02RC)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 02ST](https://stacks.math.columbia.edu/tag/02ST)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 0GU8](https://stacks.math.columbia.edu/tag/0GU8)
* [Stacks Project, Tag 02S5](https://stacks.math.columbia.edu/tag/02S5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The zero-scheme presentation of the divisor at infinity over a test scheme -/

/-- The geometry over one test scheme `t : T ⟶ X` that the Gysin recipe of Stacks 0F9J runs on.

In the situation of Stacks 0FAQ, `amb` is the base change `W_T` of the modified projective line,
`amb'` is `W'_T`, and `compare` is the base change of the proper morphism `g : W' ⟶ W`. The
divisor at infinity of `W_T` is presented as the zero scheme of the section `divisorSection` of
the invertible module `line`, and `iso` identifies it with the base change `T ×_X W_∞` on which
the bivariant class `C` of Stacks 0F9J caps; `iso'` does the same for `W'_∞`, the zero scheme of
the pulled-back section being the divisor at infinity of `W'_T`.

The last two fields are what makes the presentation usable: `compare_compatible` says the two
identifications agree with the base change of `g_∞`, and `gysinCompatible` is the
integral-component hypothesis of Stacks 02TA for `compare`. -/
structure InfinityDivisorPresentation (C : ChowSituation.{u}) {X WInf WInf' T : Scheme.{u}}
    (sWInf : WInf ⟶ C.S) (sWInf' : WInf' ⟶ C.S) (pInf : WInf ⟶ X) (gInf : WInf' ⟶ WInf)
    (t : T ⟶ X) where
  /-- The base change `W_T` of the modified projective line. -/
  amb : Scheme.{u}
  /-- Its structure morphism over the base of the Chow situation. -/
  ambStructure : amb ⟶ C.S
  [finiteType_ambStructure : LocallyOfFiniteType ambStructure]
  /-- The base change `W'_T` of the further modification. -/
  amb' : Scheme.{u}
  /-- The base change of the proper comparison morphism `g : W' ⟶ W`. -/
  compare : amb' ⟶ amb
  [proper_compare : IsProper compare]
  /-- An invertible module on `W_T` cutting out the divisor at infinity. -/
  line : amb.Modules
  [invertible_line : AlgebraicGeometry.SheafOfModules.IsInvertible amb.sheaf.obj
    amb.ringCatSheaf.property line]
  /-- The section whose zero scheme is the divisor at infinity of `W_T`. -/
  divisorSection : Γ(line, ⊤)
  /-- The divisor at infinity of `W_T` is the base change of `W_∞`. -/
  iso : (Stacks.Divisors.zeroScheme amb line divisorSection).subscheme ≅ pullback pInf t
  /-- That identification lies over the base of the Chow situation. -/
  iso_comp : iso.hom ≫ (pullback.fst pInf t ≫ sWInf) =
    (Stacks.Divisors.zeroScheme amb line divisorSection).subschemeι ≫ ambStructure
  /-- The divisor at infinity of `W'_T`, the zero scheme of the pulled-back section, is the base
  change of `W'_∞`. -/
  iso' : (pullbackZeroScheme compare line divisorSection).subscheme ≅ pullback (gInf ≫ pInf) t
  /-- That identification lies over the base of the Chow situation. -/
  iso'_comp : iso'.hom ≫ (pullback.fst (gInf ≫ pInf) t ≫ sWInf') =
    (pullbackZeroScheme compare line divisorSection).subschemeι ≫ (compare ≫ ambStructure)
  /-- The two identifications agree with the base change of the induced morphism
  `g_∞ : W'_∞ ⟶ W_∞` of divisors at infinity. -/
  compare_compatible : iso'.hom ≫ bivariantPushforwardBaseChange gInf pInf t =
    zeroSchemePullbackHom compare line divisorSection ≫ iso.hom
  /-- The integral-component case of Stacks 02TA for `compare`, in every degree: the hypothesis
  that `Stacks.Chow.gysinHomomorphismOfInvertible_properPushforward` still carries. -/
  gysinCompatible : ∀ k : ℤ,
    GysinCompatibleWithPushforward C ambStructure k line divisorSection
      (firstChernComponentClass C ambStructure k line) (compare ≫ ambStructure) compare
      (firstChernComponentClass C (compare ≫ ambStructure) k
        ((Scheme.Modules.pullback compare).obj line))
      (zeroSchemePullbackHom compare line divisorSection)
      (zeroSchemePullbackHom_comp compare line divisorSection C ambStructure
        (compare ≫ ambStructure) rfl)

namespace InfinityDivisorPresentation

variable {C : ChowSituation.{u}} {X WInf WInf' T : Scheme.{u}} {sWInf : WInf ⟶ C.S}
  {sWInf' : WInf' ⟶ C.S} {pInf : WInf ⟶ X} {gInf : WInf' ⟶ WInf} {t : T ⟶ X}
  (P : InfinityDivisorPresentation C sWInf sWInf' pInf gInf t)

/-- The structure morphism `W_T ⟶ S` is locally of finite type. -/
instance locallyOfFiniteType_ambStructure : LocallyOfFiniteType P.ambStructure :=
  P.finiteType_ambStructure

/-- The comparison morphism `W'_T ⟶ W_T` is proper. -/
instance isProper_compare : IsProper P.compare := P.proper_compare

/-- The module cutting out the divisor at infinity of `W_T` is invertible. -/
instance isInvertible_line : AlgebraicGeometry.SheafOfModules.IsInvertible P.amb.sheaf.obj
    P.amb.ringCatSheaf.property P.line := P.invertible_line

/-- The structure morphism of `W'_T` over the base of the Chow situation. -/
abbrev ambStructure' : P.amb' ⟶ C.S := P.compare ≫ P.ambStructure

/-- Proper pushforward of cycles along the comparison morphism `W'_T ⟶ W_T`. -/
def comparePushforward (k : ℤ) (β : CycleGroup C P.ambStructure' k) :
    CycleGroup C P.ambStructure k :=
  properPushforward C P.ambStructure' P.ambStructure P.compare rfl k β

/-- **Stacks 02TA**, read on the presentation: the Gysin class of a pushed-forward cycle is the
pushforward, along the morphism of divisors at infinity, of its Gysin class. -/
theorem gysinHomomorphismOfInvertible_comparePushforward (hpp : ProperPushforwardDescends C)
    (k : ℤ) (β : CycleGroup C P.ambStructure' (k + 1)) :
    gysinHomomorphismOfInvertible C P.ambStructure k P.line P.divisorSection
        (P.comparePushforward (k + 1) β) =
      properChowPushforward C
        ((pullbackZeroScheme P.compare P.line P.divisorSection).subschemeι ≫ P.ambStructure')
        ((Stacks.Divisors.zeroScheme P.amb P.line P.divisorSection).subschemeι ≫ P.ambStructure)
        (zeroSchemePullbackHom P.compare P.line P.divisorSection)
        (zeroSchemePullbackHom_comp P.compare P.line P.divisorSection C P.ambStructure
          P.ambStructure' rfl) k (hpp _ _ _ _ _)
        (gysinHomomorphismOfInvertible C P.ambStructure' k
          ((Scheme.Modules.pullback P.compare).obj P.line)
          (AlgebraicGeometry.pullbackGlobalSections P.compare P.line P.divisorSection) β) :=
  gysinHomomorphismOfInvertible_properPushforward P.compare P.line P.divisorSection C
    P.ambStructure P.ambStructure' k rfl (hpp _ _ _ _ _) (P.gysinCompatible k) β

variable [LocallyOfFiniteType sWInf] [LocallyOfFiniteType t]

/-- The class `i_∞^*β` of the Gysin recipe of Stacks 0F9J, transported along the identification
of the divisor at infinity of `W_T` with the base change of `W_∞`. -/
def gysinCap (hpp : ProperPushforwardDescends C) (k : ℤ)
    (β : CycleGroup C P.ambStructure (k + 1)) :
    chowGroup C (pullback.fst pInf t ≫ sWInf) k :=
  properChowPushforward C
    ((Stacks.Divisors.zeroScheme P.amb P.line P.divisorSection).subschemeι ≫ P.ambStructure)
    (pullback.fst pInf t ≫ sWInf) P.iso.hom P.iso_comp k (hpp _ _ _ _ _)
    (gysinHomomorphismOfInvertible C P.ambStructure k P.line P.divisorSection β)

variable [LocallyOfFiniteType sWInf'] [IsProper gInf]

/-- The class `(i'_∞)^*β'` of the Gysin recipe of Stacks 0F9J on the further modification,
transported along the identification of the divisor at infinity of `W'_T` with the base change of
`W'_∞`. -/
def gysinCap' (hpp : ProperPushforwardDescends C) (k : ℤ)
    (β : CycleGroup C P.ambStructure' (k + 1)) :
    chowGroup C (pullback.fst (gInf ≫ pInf) t ≫ sWInf') k :=
  properChowPushforward C
    ((pullbackZeroScheme P.compare P.line P.divisorSection).subschemeι ≫ P.ambStructure')
    (pullback.fst (gInf ≫ pInf) t ≫ sWInf') P.iso'.hom P.iso'_comp k (hpp _ _ _ _ _)
    (gysinHomomorphismOfInvertible C P.ambStructure' k
      ((Scheme.Modules.pullback P.compare).obj P.line)
      (AlgebraicGeometry.pullbackGlobalSections P.compare P.line P.divisorSection) β)

/-- The Gysin class on the divisor at infinity of `W'_T` pushes forward along `g_∞` to the Gysin
class on the divisor at infinity of `W_T` of the pushed-forward cycle.

This is the geometric heart of Stacks 0FAQ: Stacks 02TA transports the Gysin map across the
proper morphism `W'_T ⟶ W_T`, and `compare_compatible` says that the resulting morphism of
divisors at infinity is, under the two identifications, the base change of `g_∞`. -/
theorem properChowPushforward_gysinCap' (hgInf : gInf ≫ sWInf = sWInf')
    (hpp : ProperPushforwardDescends C) (k : ℤ) (β : CycleGroup C P.ambStructure' (k + 1)) :
    properChowPushforward C (pullback.fst (gInf ≫ pInf) t ≫ sWInf')
        (pullback.fst pInf t ≫ sWInf) (bivariantPushforwardBaseChange gInf pInf t)
        (bivariantPushforwardBaseChange_comp_structure hgInf pInf t) k (hpp _ _ _ _ _)
        (P.gysinCap' hpp k β) =
      P.gysinCap hpp k (P.comparePushforward (k + 1) β) := by
  have hTA := P.gysinHomomorphismOfInvertible_comparePushforward hpp k β
  refine Eq.trans (properChowPushforward_comp_eq C
    ((pullbackZeroScheme P.compare P.line P.divisorSection).subschemeι ≫ P.ambStructure')
    (pullback.fst (gInf ≫ pInf) t ≫ sWInf')
    ((Stacks.Divisors.zeroScheme P.amb P.line P.divisorSection).subschemeι ≫ P.ambStructure)
    (pullback.fst pInf t ≫ sWInf) P.iso'.hom (bivariantPushforwardBaseChange gInf pInf t)
    (zeroSchemePullbackHom P.compare P.line P.divisorSection) P.iso.hom P.compare_compatible
    P.iso'_comp (bivariantPushforwardBaseChange_comp_structure hgInf pInf t)
    (zeroSchemePullbackHom_comp P.compare P.line P.divisorSection C P.ambStructure
      P.ambStructure' rfl)
    P.iso_comp k (hpp _ _ _ _ _) (hpp _ _ _ _ _) (hpp _ _ _ _ _) (hpp _ _ _ _ _)
    (gysinHomomorphismOfInvertible C P.ambStructure' k
      ((Scheme.Modules.pullback P.compare).obj P.line)
      (AlgebraicGeometry.pullbackGlobalSections P.compare P.line P.divisorSection) β)) ?_
  rw [← hTA]
  rfl

end InfinityDivisorPresentation

/-! ### The class at infinity is unchanged by a proper modification -/

section Specialization

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X WInf WInf' : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sWInf : WInf ⟶ C.S) [LocallyOfFiniteType sWInf]
  (sWInf' : WInf' ⟶ C.S) [LocallyOfFiniteType sWInf'] (pInf : WInf ⟶ X)
  [LocallyOfFiniteType pInf] (gInf : WInf' ⟶ WInf) [IsProper gInf]
  (hgInf : gInf ≫ sWInf = sWInf') (hpInf : pInf ≫ sX = sWInf)
  (hpp : ProperPushforwardDescends C) (p : ℤ)
  (P : ∀ {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t],
    InfinityDivisorPresentation C sWInf sWInf' pInf gInf t)
  (cW : BivariantClass C G sWInf sX pInf hpInf p)
  (cW' : BivariantClass C G sWInf' sX (gInf ≫ pInf) (comp_comp_structureMorphism_eq hgInf hpInf) p)
  (cPush : BivariantClass C G sWInf sX pInf hpInf p)
  (ExtW : ∀ {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ),
    chowGroup C (t ≫ sX) k → CycleGroup C (P t).ambStructure ((k - p) + 1) → Prop)
  (ExtW' : ∀ {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ),
    chowGroup C (t ≫ sX) k → CycleGroup C (P t).ambStructure' ((k - p) + 1) → Prop)

end Specialization

end Stacks.Chow

end
