module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.StandardPresentationExists
public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.AffineLift
public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.ArbitraryBaseChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.Bijectivity
public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.Glue
public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.HenselLift
public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.StalkHenselian
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHomLocallyRinged
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleTwoIsoAffineCover

/-!
# Recovering morphisms of algebraic spaces from their locally ringed small étale topoi

This is Stacks 04KL: for algebraic spaces `X`, `Y` over `Spec ℤ`, every morphism of locally
ringed topoi `(g, g♯) : (Sh(X_étale), 𝒪_X) ⟶ (Sh(Y_étale), 𝒪_Y)` is isomorphic to
`(f_small, f♯)` for a unique morphism of algebraic spaces `f : X ⟶ Y`.

## Main results

* `AlgebraicGeometry.Space.existsUnique_spaceHom_twoIso_of_isLocallyRinged`: **Stacks 04KL**,
  existence and uniqueness of `f` with `(g, g♯) ≅ (f_small, f♯)`.
* `AlgebraicGeometry.Space.bijective_smallEtaleLocallyRingedClass`: the reformulation of
  Stacks 04KL as full faithfulness of `X ↦ (X_étale, 𝒪_X)`, morphisms of locally ringed topoi being
  taken up to 2-isomorphism.
* `AlgebraicGeometry.Space.nonempty_twoIso_recoveredHom'`: the assembly of the 2-isomorphism from
  the stalk computations.

## Implementation notes

The base is `Spec ℤ` — in this development `Spec (ULift ℤ)`, the terminal scheme of the universe of
the site — as in the source.  Over a general base `S` the statement is false: the morphisms of
algebraic spaces over `S` are required to commute with the structure morphisms to `S`, which the
topos-theoretic data do not see (for `S = X = Y = Spec L` and a nontrivial automorphism `σ` of a
field `L`, `(σ_small, σ♯)` is locally ringed and not 2-isomorphic to the identity, while the
identity is the only morphism over `S`).

The base enters this chain at exactly one point.  Every declaration of
`StacksDraft.AlgebraicGeometry.Spaces.RecoveringMorphisms` is stated over an arbitrary base
scheme with `hover : IsChartOverBase g` as its only hypothesis on the base — that the morphism
of schemes `AlgebraicGeometry.Space.chartSchemeHom g V U s`, which is defined for every base,
commutes with the structure morphisms of the two charts to `S`, so that
`AlgebraicGeometry.BigFppfOver.homOfCompEq` can read it as a morphism of the big fppf site of
`S` (`AlgebraicGeometry.Space.OverBase.chartOverHom`).  The gluing, the stalk arguments, the
2-isomorphism and the uniqueness use nothing about the base.  Over a terminal base that
hypothesis is `AlgebraicGeometry.Space.isChartOverBase_of_isTerminal`, which is where
terminality is used below and the only place it is used.

That hypothesis is an equality of morphisms of schemes *into* `S`, so it is not a formality: the
chart construction yields only the ring map on global functions
`AlgebraicGeometry.Space.chartRingHom`, which pins a morphism of schemes down exactly when the
canonical morphism of the target to the spectrum of its global functions is a monomorphism
(`AlgebraicGeometry.ext_of_mono_toSpecΓ`).  For such a base it is therefore equivalent to a ring
identity, and
`StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.ChartBaseFunction` reduces it
there to a statement about `g` with neither the chart `V` nor the section `s` in it — that `g`
transports the functions pulled back from the base to themselves
(`AlgebraicGeometry.Space.chartSchemeHom_comp_inclusion_map_of_baseFunctionTransport`) — which
`StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.BaseFunctionTransport` derives
from the 2-compatibility of `g` with a pair of structure morphisms.  That is what makes
`AlgebraicGeometry.Space.isRecoveredFromSmallEtale_of_mono_toSpecΓ` — Stacks 04KL over a base
scheme whose canonical morphism `S ⟶ Spec Γ(S, ⊤)` is a monomorphism, so over an affine or
quasi-affine base — a theorem rather than a hypothesis.  That hypothesis is the exact reach of
the route: it says precisely that a morphism of schemes into `S` is determined by its ring map on
global functions.  For a base outside the class the equation is in addition a Zariski-local
question on `S`, which is not settled here.

The construction of `f` uses only that the chart morphisms are morphisms over the base
(`AlgebraicGeometry.Space.recoveredHom'`), and the 2-isomorphism is assembled from the
comparison of `g⁻¹h_V` with the chart maps over `f`
(`AlgebraicGeometry.Space.twoIsoOfChartComparison'`),
which is bijective on stalks because the stalks of the structure sheaves are strictly henselian
and `g♯` is local on stalks (Stacks 04GX).  Uniqueness is Stacks 04M6.

## References

* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
* [Stacks Project, Tag 04M6](https://stacks.math.columbia.edu/tag/04M6)
* [Stacks Project, Tag 04GX](https://stacks.math.columbia.edu/tag/04GX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] smallEtaleTopology_subcanonical

/-- The uniqueness half: over any base, two morphisms whose morphisms of small étale ringed topoi
are 2-isomorphic to the same `(g, g♯)` are equal (Stacks 04M6). -/
theorem eq_of_twoIso_of_twoIso {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : AlgebraicSpaces B S hS}
    (g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))
    (a b : X ⟶ Y)
    (ta : RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} g (smallEtaleRingedToposHom B S hS a))
    (tb : RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} g (smallEtaleRingedToposHom B S hS b)) :
    a = b :=
  eq_of_smallEtaleRingedToposHom_twoIso B S hS a b (ta.symm.trans tb)

/-- **The assembly.** For a terminal base scheme, a morphism of the small étale ringed topoi of two
algebraic spaces whose stalk comparisons have the Hensel lifting property and its uniqueness, and
for which the stalks of the inverse images of representable sheaves lift to affine opens and do
not all vanish, is 2-isomorphic to `(f_small, f♯)` for the recovered morphism `f`. -/
theorem nonempty_twoIso_recoveredHom' {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : AlgebraicSpaces B S hS}
    (g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))
    (hover : IsChartOverBase g)
    (hRS : ∀ (x : GeometricPoint B S hS X.1) {V₀ V' : SmallEtale B S hS Y.1}
      [IsAffine (chartSch V₀)] [IsAffine (chartSch V')] (c : V' ⟶ V₀),
      RelSurjAt' x (isChartCompatible_recoveredHom' g hover) c)
    (hRI : ∀ (x : GeometricPoint B S hS X.1) {V₀ V' : SmallEtale B S hS Y.1}
      [IsAffine (chartSch V₀)] [IsAffine (chartSch V')] (c : V' ⟶ V₀),
      RelInjAt' x (isChartCompatible_recoveredHom' g hover) c)
    (hT1 : ∀ (x : GeometricPoint B S hS X.1) (P : SmallEtale B S hS Y.1)
      (τ : (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj P)),
      ∃ (O : ((BigFppfOver.toScheme B S hS).obj P.1.left).affineOpens)
        (τ' : (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj
          (chartOpenRestriction B S hS Y.1 P O.1))),
        (invStalk g x).map ((SmallEtale.topology B S hS Y.1).yoneda.map
          (chartOpenRestrictionHom B S hS Y.1 P O.1)) τ' = τ)
    (hT6 : ∀ x : GeometricPoint B S hS X.1, ∃ (V₀ : SmallEtale B S hS Y.1)
      (_ : IsAffine (chartSch V₀)),
      Nonempty ((invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj V₀))) :
    Nonempty (RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} g
      (smallEtaleRingedToposHom B S hS (recoveredHom' g hover))) :=
  ⟨twoIsoOfChartComparison' (isChartCompatible_recoveredHom' g hover) fun V _ ↦
    W_invRepComparison_of_bijective' (isChartCompatible_recoveredHom' g hover) V fun x ↦
      ⟨stalkComparison_injective' x _ V (hRS x) (hRI x) (hT1 x),
        stalkComparison_surjective' x _ V (hRS x) (hT6 x)⟩⟩

/-- The Hensel lifting property of the stalk comparison along every morphism of affine charts,
for a morphism of locally ringed topoi. -/
theorem relSurjAt_of_isLocallyRinged' {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : AlgebraicSpaces B S hS}
    {g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y)}
    {hover : IsChartOverBase g}
    (hg : g.IsLocallyRinged) {f : X ⟶ Y} (hf : OverBase.IsChartCompatible hover f)
    (x : GeometricPoint B S hS X.1) {V₀ V' : SmallEtale B S hS Y.1}
    [IsAffine (chartSch V₀)] [IsAffine (chartSch V')] (c : V' ⟶ V₀) :
    RelSurjAt' x hf c := by
  obtain ⟨n, P, ⟨pres⟩, hP⟩ := Stacks.EtaleCohomology.exists_standardPresentationOver
    ((BigFppfOver.toScheme B S hS).map c.hom.left)
  exact fun σ₀ t' ht ↦ exists_stalk_lift' hf x c pres (isLocalHom_invStalkRingHom g x hg)
    (fun ψ ↦ Algebra.Etale.quotient_span_range_map ψ P) σ₀ t' ht

/-- The uniqueness of the Hensel lift along every morphism of affine charts, for a morphism of
locally ringed topoi. -/
theorem relInjAt_of_isLocallyRinged' {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : AlgebraicSpaces B S hS}
    {g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y)}
    {hover : IsChartOverBase g}
    (hg : g.IsLocallyRinged) {f : X ⟶ Y} (hf : OverBase.IsChartCompatible hover f)
    (x : GeometricPoint B S hS X.1) {V₀ V' : SmallEtale B S hS Y.1}
    [IsAffine (chartSch V₀)] [IsAffine (chartSch V')] (c : V' ⟶ V₀) :
    RelInjAt' x hf c := by
  obtain ⟨n, P, ⟨pres⟩, hP⟩ := Stacks.EtaleCohomology.exists_standardPresentationOver
    ((BigFppfOver.toScheme B S hS).map c.hom.left)
  exact fun σ' σ'' h₀ hc ↦ stalk_lift_unique' hf x c pres (isLocalHom_invStalkRingHom g x hg)
    (fun ψ ↦ Algebra.Etale.quotient_span_range_map ψ P) σ' σ'' h₀ hc


/-- **Stacks 04KL.** Let `X` and `Y` be algebraic spaces over `Spec ℤ` (here `Spec (ULift ℤ)`, the
terminal scheme at the universe of the site) and let
`(g, g♯) : (Sh(X_étale), 𝒪_X) ⟶ (Sh(Y_étale), 𝒪_Y)` be a morphism of locally ringed topoi.
Then there is a unique morphism of algebraic spaces `f : X ⟶ Y` such that `(g, g♯)` is
2-isomorphic to `(f_small, f♯)` (Stacks 04IC, 03G8). -/
@[stacks 04KL]
theorem existsUnique_spaceHom_twoIso_of_isLocallyRinged (B : BigFppfSite.{u})
    (hZ : B.Contains (Spec (CommRingCat.of (ULift.{u} ℤ))))
    {X Y : AlgebraicSpaces B (Spec (CommRingCat.of (ULift.{u} ℤ))) hZ}
    (g : RingedToposHom (smallEtaleRingedTopos B _ hZ X) (smallEtaleRingedTopos B _ hZ Y))
    (hg : g.IsLocallyRinged) :
    ∃! f : X ⟶ Y, Nonempty (RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} g
      (smallEtaleRingedToposHom B _ hZ f)) := by
  let hover : IsChartOverBase g :=
    isChartOverBase_of_isTerminal specULiftZIsTerminal g
  have h := nonempty_twoIso_recoveredHom' g hover
    (fun x _ _ _ _ c ↦ relSurjAt_of_isLocallyRinged' hg _ x c)
    (fun x _ _ _ _ c ↦ relInjAt_of_isLocallyRinged' hg _ x c)
    (fun x P τ ↦ exists_affineOpen_lift g x P τ) (fun x ↦ exists_affine_invStalk g x)
  refine ⟨recoveredHom' g hover, h, fun f ⟨t⟩ ↦ ?_⟩
  obtain ⟨t'⟩ := h
  exact eq_of_twoIso_of_twoIso g f _ t t'

section FullyFaithful

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X Y : AlgebraicSpaces B S hS)

/-- Morphisms of locally ringed topoi between the small étale ringed topoi of `X` and `Y`, up to
2-isomorphism (Stacks 04IC). -/
def locallyRingedTwoIsoSetoid : Setoid {h : RingedToposHom (smallEtaleRingedTopos B S hS X)
    (smallEtaleRingedTopos B S hS Y) // h.IsLocallyRinged} where
  r a b := Nonempty (RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} a.1 b.1)
  iseqv := ⟨fun a ↦ ⟨RingedToposHom.TwoIso.refl a.1⟩, fun ⟨t⟩ ↦ ⟨t.symm⟩,
    fun ⟨t⟩ ⟨t'⟩ ↦ ⟨t.trans t'⟩⟩

/-- The class, up to 2-isomorphism, of the morphism of locally ringed topoi `(f_small, f♯)` of a
morphism of algebraic spaces (Stacks 03G8, 04KJ). -/
def smallEtaleLocallyRingedClass (f : X ⟶ Y) : Quotient (locallyRingedTwoIsoSetoid B S hS X Y) :=
  Quotient.mk _ ⟨smallEtaleRingedToposHom B S hS f,
    smallEtaleRingedToposHom_isLocallyRinged B S hS f⟩

end FullyFaithful

/-- **Stacks 04KL, in the form of full faithfulness.** Over `Spec ℤ`, the construction
`X ↦ (X_étale, 𝒪_X)` is fully faithful from algebraic spaces to locally ringed topoi, morphisms of
the latter being taken up to 2-isomorphism: `f ↦ [(f_small, f♯)]` is a bijection from the
morphisms `X ⟶ Y` of algebraic spaces onto the 2-isomorphism classes of morphisms of locally ringed
topoi `(Sh(X_étale), 𝒪_X) ⟶ (Sh(Y_étale), 𝒪_Y)`. -/
@[stacks 04KL "the reformulation: X ↦ (X_étale, 𝒪_X) is fully faithful, morphisms of locally
  ringed topoi being taken up to 2-isomorphism"]
theorem bijective_smallEtaleLocallyRingedClass (B : BigFppfSite.{u})
    (hZ : B.Contains (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (X Y : AlgebraicSpaces B (Spec (CommRingCat.of (ULift.{u} ℤ))) hZ) :
    Function.Bijective (smallEtaleLocallyRingedClass B _ hZ X Y) := by
  refine ⟨fun a b h ↦ ?_, fun q ↦ ?_⟩
  · obtain ⟨t⟩ := Quotient.exact h
    exact eq_of_smallEtaleRingedToposHom_twoIso B _ hZ a b t
  · induction q using Quotient.inductionOn with
    | h g =>
      obtain ⟨f, ⟨t⟩, -⟩ := existsUnique_spaceHom_twoIso_of_isLocallyRinged B hZ g.1 g.2
      exact ⟨f, Quotient.sound ⟨t.symm⟩⟩

/-! ### The original forms, over a terminal base

The declarations of this section are the forms over a terminal base `S`, with
`hS₀ : IsTerminal S` as their hypothesis on the base. The primed declarations above are the same
constructions under `hover : AlgebraicGeometry.Space.IsChartOverBase g`, which
`AlgebraicGeometry.Space.isChartOverBase_of_isTerminal` derives from `hS₀`. -/

section TopBaseForm

attribute [local instance] smallEtaleTopology_subcanonical

/-- **The assembly.** For a terminal base scheme, a morphism of the small étale ringed topoi of two
algebraic spaces whose stalk comparisons have the Hensel lifting property and its uniqueness, and
for which the stalks of the inverse images of representable sheaves lift to affine opens and do
not all vanish, is 2-isomorphic to `(f_small, f♯)` for the recovered morphism `f`. -/
theorem nonempty_twoIso_recoveredHom {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (hS₀ : IsTerminal S) {X Y : AlgebraicSpaces B S hS}
    (g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))
    (hRS : ∀ (x : GeometricPoint B S hS X.1) {V₀ V' : SmallEtale B S hS Y.1}
      [IsAffine (chartSch V₀)] [IsAffine (chartSch V')] (c : V' ⟶ V₀),
      RelSurjAt x (isChartCompatible_recoveredHom hS₀ g) c)
    (hRI : ∀ (x : GeometricPoint B S hS X.1) {V₀ V' : SmallEtale B S hS Y.1}
      [IsAffine (chartSch V₀)] [IsAffine (chartSch V')] (c : V' ⟶ V₀),
      RelInjAt x (isChartCompatible_recoveredHom hS₀ g) c)
    (hT1 : ∀ (x : GeometricPoint B S hS X.1) (P : SmallEtale B S hS Y.1)
      (τ : (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj P)),
      ∃ (O : ((BigFppfOver.toScheme B S hS).obj P.1.left).affineOpens)
        (τ' : (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj
          (chartOpenRestriction B S hS Y.1 P O.1))),
        (invStalk g x).map ((SmallEtale.topology B S hS Y.1).yoneda.map
          (chartOpenRestrictionHom B S hS Y.1 P O.1)) τ' = τ)
    (hT6 : ∀ x : GeometricPoint B S hS X.1, ∃ (V₀ : SmallEtale B S hS Y.1)
      (_ : IsAffine (chartSch V₀)),
      Nonempty ((invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj V₀))) :
    Nonempty (RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} g
      (smallEtaleRingedToposHom B S hS (recoveredHom hS₀ g))) :=
  nonempty_twoIso_recoveredHom' g (isChartOverBase_of_isTerminal hS₀ g) hRS hRI hT1 hT6

/-- The Hensel lifting property of the stalk comparison along every morphism of affine charts,
for a morphism of locally ringed topoi. -/
theorem relSurjAt_of_isLocallyRinged {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {hS₀ : IsTerminal S} {X Y : AlgebraicSpaces B S hS}
    {g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y)}
    (hg : g.IsLocallyRinged) {f : X ⟶ Y} (hf : IsChartCompatible hS₀ g f)
    (x : GeometricPoint B S hS X.1) {V₀ V' : SmallEtale B S hS Y.1}
    [IsAffine (chartSch V₀)] [IsAffine (chartSch V')] (c : V' ⟶ V₀) :
    RelSurjAt x hf c := by
  exact relSurjAt_of_isLocallyRinged' (hover := isChartOverBase_of_isTerminal hS₀ g) hg hf x c

/-- The uniqueness of the Hensel lift along every morphism of affine charts, for a morphism of
locally ringed topoi. -/
theorem relInjAt_of_isLocallyRinged {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {hS₀ : IsTerminal S} {X Y : AlgebraicSpaces B S hS}
    {g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y)}
    (hg : g.IsLocallyRinged) {f : X ⟶ Y} (hf : IsChartCompatible hS₀ g f)
    (x : GeometricPoint B S hS X.1) {V₀ V' : SmallEtale B S hS Y.1}
    [IsAffine (chartSch V₀)] [IsAffine (chartSch V')] (c : V' ⟶ V₀) :
    RelInjAt x hf c := by
  exact relInjAt_of_isLocallyRinged' (hover := isChartOverBase_of_isTerminal hS₀ g) hg hf x c

end TopBaseForm

end AlgebraicGeometry.Space
