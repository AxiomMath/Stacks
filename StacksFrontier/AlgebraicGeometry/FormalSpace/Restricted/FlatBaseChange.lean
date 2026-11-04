module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeOnReductionsCharacterization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FlatCharacterization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyBaseChange
public import StacksFrontier.RingTheory.Rig.FlatBaseChange
public import StacksFrontier.Topology.Algebra.AdicTopology.NoetherianAdic

/-!
# Base change of a flat morphism of locally Noetherian formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` and `g : Z ⟶ Y` be
morphisms of locally Noetherian formal algebraic spaces over `S`. **Stacks 0GCE** says:

1. if `f` is flat and the morphism of reductions `g_red : Z_red ⟶ Y_red` is locally of finite
   type, then the base change `X ×_Y Z ⟶ Z` is flat;
2. if `f` is flat and locally of finite type, then `X ×_Y Z ⟶ Z` is flat and locally of finite
   type.

The fibre product is the categorical one in the category of fppf sheaves on the big site, which
is where this library's formal algebraic spaces live, and the base change is its second
projection `CategoryTheory.Limits.pullback.snd f g`; this is the fibre product whose charts the
proof of Stacks 0GBD computes, carried here by
`AlgebraicGeometry.FormalSpace.HasBaseChangeCoverOverPullbackSnd`.

## Main results

Both parts of Stacks 0GCE are proved unconditionally in the module
`StacksFrontier.AlgebraicGeometry.FormalSpace.Restricted.FlatBaseChangeLocallyNoetherian`, as
`isFlat_pullback_snd_of_isLocallyOfFiniteTypeOnReductions_of_isLocallyNoetherian` and
`isFlat_and_isLocallyOfFiniteType_pullback_snd`. What this file carries are chart-level inputs
of those proofs, all in the namespace `AlgebraicGeometry.FormalSpace`:

* `hasPropertyOnEveryAffineEtaleDiagram_finiteTypeOnReductions`: the implication (4) ⟹ (1) of
  **Stacks 0GC7**, read at the class of Noetherian adic rings.
* `hasPropertyOnEveryAffineEtaleDiagram_isFlatAdicOfFiniteTypeHom` and
  `hasPropertyOnEveryAffineEtaleDiagram_isFlatAdicOfFiniteTypeHom_pullback_snd`: the chart
  condition for flatness together with the property of **Stacks 0GBW** for a flat morphism
  locally of finite type, and its passage to the second projection of a fibre product by
  Remark **0GBF**.

## Implementation notes

Both parts are the composite of a ring-level stability statement with the geometric transfer
drawn in Remark 0GBG, which this library carries as
`AlgebraicGeometry.FormalSpace.hasPropertyOnEveryAffineEtaleDiagram_pullback_snd` and its
variant `..._pullback_snd_of_stableBaseChange`.
Those two carry three inputs apiece — the chart covering of the fibre product produced by the
argument of Stacks 0GBD, the implication (3) ⟹ (1) of Stacks 0ANG, and invariance of the
property under isomorphism of chart targets — and the statements below forward them unchanged.
The passage between flatness of a morphism in the sense of Definition 0GCC and condition (1) of
Stacks 0ANG for Noetherian adic rings and flat ring maps is
`AlgebraicGeometry.FormalSpace.isFlat_iff_hasPropertyOnEveryAffineEtaleDiagram`, which is
unconditional, so no part of Stacks 0GCD is assumed here.

For part (1) the ring-level input is part (1) of Stacks 0GCA, which the library carries outright
as `TopologicalRing.flat_isStableUnderBaseChangeByFiniteTypeOnReductions`: flatness of arrows of
`WAdm^{Noeth}` is stable under base change by arrows of finite type on reductions. The hypothesis
of the source is on the morphism of reductions `g_red`, and it is taken in exactly that form,
namely `AlgebraicGeometry.FormalSpace.IsLocallyOfFiniteTypeOnReductions` — condition (4) of
Stacks 0GC7. Turning it into the chart condition the transfer consumes is the implication
(4) ⟹ (1) of Stacks 0GC7; that leg is reproved here at the class of Noetherian adic rings, from
the same three inputs the library's `isLocallyOfFiniteTypeOnReductions_tfae` names for it, by
`hasPropertyOnEveryAffineEtaleDiagram_finiteTypeOnReductions`. Nothing about flatness is assumed
in those three.

For part (2) the ring-level input is part (2) of Stacks 0GCA: flatness together with the property
of Stacks 0GBW — being adic and topologically of finite type — is stable under base change along
an arbitrary arrow of `WAdm^{Noeth}`. The library proves it outright as
`TopologicalRing.flatAdicFiniteType_isStableUnderBaseChange`. The comparison of the predicate
of Stacks 0AM4 for a morphism of formal algebraic spaces with condition (1) of Stacks 0ANG for
the property of Stacks 0GBW is Stacks 0GC0; it is carried, in both directions and for every
morphism, as `ChartConditionIsLocallyOfFiniteTypeNoetherian`, so that it is a statement about
the generic machinery of Stacks 0GC0 and not a restatement of either conclusion of part (2).

The locally Noetherian hypotheses on `X`, `Y` and `Z` are carried by the class of rings over
which every chart condition here quantifies, exactly as in Definition 0GCC; the locally
countably indexed hypotheses of the Stacks 0GC7 leg below are those of that tag.

## References

* [Stacks Project, Tag 0AM4](https://stacks.math.columbia.edu/tag/0AM4)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
* [Stacks Project, Tag 0GBD](https://stacks.math.columbia.edu/tag/0GBD)
* [Stacks Project, Tag 0GBF](https://stacks.math.columbia.edu/tag/0GBF)
* [Stacks Project, Tag 0GBG](https://stacks.math.columbia.edu/tag/0GBG)
* [Stacks Project, Tag 0GBW](https://stacks.math.columbia.edu/tag/0GBW)
* [Stacks Project, Tag 0GC0](https://stacks.math.columbia.edu/tag/0GC0)
* [Stacks Project, Tag 0GC7](https://stacks.math.columbia.edu/tag/0GC7)
* [Stacks Project, Tag 0GCA](https://stacks.math.columbia.edu/tag/0GCA)
* [Stacks Project, Tag 0GCC](https://stacks.math.columbia.edu/tag/0GCC)
* [Stacks Project, Tag 0GCD](https://stacks.math.columbia.edu/tag/0GCD)
* [Stacks Project, Tag 0GCE](https://stacks.math.columbia.edu/tag/0GCE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Filter

open scoped Topology

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A Noetherian adic topological ring is weakly admissible with a countable fundamental system
of open ideals: the powers of an ideal of definition are a countable basis of neighbourhoods of
zero and its elements are topologically nilpotent. This is the inclusion of `WAdm^{Noeth}` into
`WAdm^{count}` that lets the chart conditions of Stacks 0GC7, stated for the latter class, be
read at the former. -/
private theorem isCountablyWeaklyAdmissible_of_isNoetherianAdic {R : Type u} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
    (hR : TopologicalRing.IsAdic R) : TopologicalRing.IsCountablyWeaklyAdmissible R := by
  obtain ⟨⟨I, hI, hIadic⟩, hcomplete⟩ := hR
  have hnil : ∀ x ∈ I, IsTopologicallyNilpotent x := by
    intro x hx
    rw [IsTopologicallyNilpotent, Filter.tendsto_def]
    intro U hU
    obtain ⟨n, hn⟩ := hI.2 U hU
    filter_upwards [eventually_ge_atTop n] with m hm
    exact hn (Ideal.pow_le_pow_right hm (Ideal.pow_mem_pow hx m))
  have hcount : (𝓝 (0 : R)).IsCountablyGenerated := by
    rw [hIadic]
    exact I.hasBasis_nhds_zero_adic.isCountablyGenerated
  exact ⟨⟨⟨I, hI.1, hnil⟩, hcomplete.2, hcomplete.1⟩, hcount⟩

/-! ### Part (1): base change by a morphism of finite type on reductions -/

/-- The implication (4) ⟹ (1) of **Stacks 0GC7**, read at the class of Noetherian adic
topological rings: a morphism of locally countably indexed formal algebraic spaces over `S`
whose morphism of reductions is locally of finite type has the property of Stacks 0GC2 on every
affine representable étale chart map.

The three inputs are those the library's `isLocallyOfFiniteTypeOnReductions_tfae` names for this
leg: the affine computation of Stacks 0GB6 as `hbridge`, the implication (2) ⟹ (1) of Stacks
0AKX as `h0AKX`, and the étale locality of Stacks 040Y read on reductions as `hredsquare`. The
charts of `WAdm^{Noeth}` lie in `WAdm^{count}`, which is what lets `hbridge` apply to them. -/
theorem hasPropertyOnEveryAffineEtaleDiagram_finiteTypeOnReductions
    (hbridge : ChartPropertyIsFiniteTypeOnReductions B S hS)
    (h0AKX : ∀ (W : FppfSheaf B S hS), IsLocallyCountablyIndexed B S hS W →
      ∀ (U : FppfSheaf B S hS) (a : U ⟶ W), IsAffineFormalAlgebraicSpace B S hS U →
      IsRepresentableEtale B S hS a → IsCountablyIndexed B S hS U)
    (hredsquare : IsLocallyOfFiniteTypeOnReductionsOnEveryAffineEtaleSquare B S hS)
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyCountablyIndexed B S hS X) (hY : IsLocallyCountablyIndexed B S hS Y)
    (hf : IsLocallyOfFiniteTypeOnReductions B S hS f) :
    HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsNoetherianAdic
      TopologicalRing.FiniteTypeOnReductionsProperty f := by
  intro U V a b t hU hV ha hb hsq
  have h := (hbridge t hU hV (h0AKX X hX U a hU ha) (h0AKX Y hY V b hV hb)).1
    (hredsquare f a b t hU hV ha hb hsq hf)
  intro A R _ _ _ _ _ _ _ _ hA hR hwa D E eU eV φ hφ
  exact h A R (isCountablyWeaklyAdmissible_of_isNoetherianAdic hA.1)
    (isCountablyWeaklyAdmissible_of_isNoetherianAdic hR.1) hwa D E eU eV φ hφ

/-! ### Part (2): base change of a flat morphism locally of finite type -/

/-- The conjunction of flatness with the property of **Stacks 0GBW**, being adic and
topologically of finite type. This is the property called `P + R` in the proof of Stacks 0GCA,
whose part (2) asserts that it is stable under arbitrary base change of arrows of
`WAdm^{Noeth}`. -/
abbrev IsFlatAdicOfFiniteTypeHom {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁]
    [IsTopologicalRing R₁] [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂]
    (φ : R₁ →+* R₂) : Prop :=
  φ.Flat ∧ RingHom.IsAdic φ ∧ TopologicalRing.IsTopologicallyOfFiniteType φ

/-- The comparison of **Stacks 0GC0**: a morphism of formal algebraic spaces over `S` is locally
of finite type in the sense of Stacks 0AM4 exactly when every affine representable étale chart
map of it is an adic arrow of `WAdm^{Noeth}` topologically of finite type. This is the
equivalence of conditions (1) and (4) of Stacks 0GC0, read at the class of Noetherian adic rings
and quantified over all morphisms, so that it speaks only of the machinery of that tag. -/
abbrev ChartConditionIsLocallyOfFiniteTypeNoetherian : Prop :=
  ∀ {X Y : FppfSheaf B S hS} (h : X ⟶ Y),
    IsLocallyOfFiniteType B S hS h ↔
      HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsNoetherianAdic
        (fun {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
          [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂] (φ : R₁ →+* R₂) ↦
          RingHom.IsAdic φ ∧ TopologicalRing.IsTopologicallyOfFiniteType φ) h

variable {B S hS}

/-- Condition (1) of Stacks 0ANG for flatness together with the property of Stacks 0GBW passes
from `f : X ⟶ Y` to the second projection `X ×_Y Z ⟶ Z` of its fibre product with any
`g : Z ⟶ Y`, by the variant of Stacks 0GBD for locally Noetherian formal algebraic spaces.

This is Remark 0GBF applied to part (2) of Stacks 0GCA,
`TopologicalRing.flatAdicFiniteType_isStableUnderBaseChange`; nothing is asked of `g`, exactly as
there. -/
theorem hasPropertyOnEveryAffineEtaleDiagram_isFlatAdicOfFiniteTypeHom_pullback_snd
    (hiso : PropertyIsInvariantUnderTargetIso.{u} IsFlatAdicOfFiniteTypeHom)
    (h31 : SourceCoverImpliesEveryAffineEtaleDiagram B S hS
      TopologicalRing.IsNoetherianAdic IsFlatAdicOfFiniteTypeHom)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hcover : HasBaseChangeCoverOverPullbackSnd B S hS f g)
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsNoetherianAdic
      IsFlatAdicOfFiniteTypeHom f) :
    HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsNoetherianAdic
      IsFlatAdicOfFiniteTypeHom (pullback.snd f g) :=
  hasPropertyOnEveryAffineEtaleDiagram_pullback_snd_of_stableBaseChange B S hS
    IsFlatAdicOfFiniteTypeHom TopologicalRing.flatAdicFiniteType_isStableUnderBaseChange hiso h31
    f g hcover hf

/-- A flat morphism locally of finite type satisfies condition (1) of Stacks 0ANG for flatness
together with the property of Stacks 0GBW: the two chart conditions are the two conjuncts, the
first by `isFlat_iff_hasPropertyOnEveryAffineEtaleDiagram` and the second by Stacks 0GC0. -/
theorem hasPropertyOnEveryAffineEtaleDiagram_isFlatAdicOfFiniteTypeHom
    (h0GC0 : ChartConditionIsLocallyOfFiniteTypeNoetherian B S hS)
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y) (hf : IsFlat B S hS f)
    (hft : IsLocallyOfFiniteType B S hS f) :
    HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsNoetherianAdic
      IsFlatAdicOfFiniteTypeHom f := by
  have hP := (isFlat_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS f).mp hf
  have hR := (h0GC0 f).mp hft
  intro U V a b t hU hV ha hb hsq A R _ _ _ _ _ _ _ _ hA hRc hwa D E eU eV φ hφ
  exact ⟨hP U V a b t hU hV ha hb hsq A R hA hRc hwa D E eU eV φ hφ,
    hR U V a b t hU hV ha hb hsq A R hA hRc hwa D E eU eV φ hφ⟩

end AlgebraicGeometry.FormalSpace

end
