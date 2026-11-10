module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AtlasChartCountablyIndexed
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeCharacterizationRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeOnReductionsCharacterizationRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FlatCharacterizationRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyBaseChangeRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Restricted.FlatBaseChange
public import StacksFrontier.RingTheory.Rig.FlatBaseChangeRefined
public import StacksFrontier.Topology.Algebra.AdicTopology.NoetherianAdic
import all StacksFrontier.AlgebraicGeometry.FormalSpace.Restricted.FlatBaseChange

/-!
# Base change of a flat morphism of locally Noetherian formal algebraic spaces: the refined forms

The strengthened and newly added declarations of the 2026-10 chapter-87 round that
belong with `StacksFrontier.AlgebraicGeometry.FormalSpace.Restricted.FlatBaseChange`. A declaration
of that module whose statement the round strengthened
keeps its original statement there; its strengthened form lives here under a primed name.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Filter

open scoped Topology

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Part (1): base change by a morphism of finite type on reductions -/

/-- The implication (4) ⟹ (1) of **Stacks 0GC7**, read at the class of Noetherian adic
topological rings: a morphism of locally countably indexed formal algebraic spaces over `S`
whose morphism of reductions is locally of finite type has the property of Stacks 0GC2 on every
affine representable étale chart map.

The two inputs are those the library's `isLocallyOfFiniteTypeOnReductions_tfae'` names for this
leg: the affine computation of Stacks 0GB6 as `hbridge` and the étale locality of Stacks 040Y
read on reductions as `hredsquare`. The implication (2) ⟹ (1) of Stacks 0AKX, which used to be
`h0AKX`, is
`FormalSpace.isCountablyIndexed_of_isRepresentableEtale_of_isLocallyCountablyIndexed`.
The charts of `WAdm^{Noeth}` lie in `WAdm^{count}`, which is what lets `hbridge` apply to
them. -/
theorem hasPropertyOnEveryAffineEtaleDiagram_finiteTypeOnReductions'
    (hbridge : ChartPropertyIsFiniteTypeOnReductions B S hS)
    (hredsquare : IsLocallyOfFiniteTypeOnReductionsOnEveryAffineEtaleSquare B S hS)
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyCountablyIndexed B S hS X) (hY : IsLocallyCountablyIndexed B S hS Y)
    (hf : IsLocallyOfFiniteTypeOnReductions B S hS f) :
    HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsNoetherianAdic
      TopologicalRing.FiniteTypeOnReductionsProperty f := by
  have h0AKX := isCountablyIndexed_of_isRepresentableEtale_of_isLocallyCountablyIndexed B S hS
  intro U V a b t hU hV ha hb hsq
  have h := (hbridge t hU hV (h0AKX X hX U a hU ha) (h0AKX Y hY V b hV hb)).1
    (hredsquare f a b t hU hV ha hb hsq hf)
  intro A R _ _ _ _ _ _ _ _ hA hR hwa D E eU eV φ hφ
  exact h A R (isCountablyWeaklyAdmissible_of_isNoetherianAdic hA.1)
    (isCountablyWeaklyAdmissible_of_isNoetherianAdic hR.1) hwa D E eU eV φ hφ

/-- **Stacks 0GCE, part (1).** Let `f : X ⟶ Y` and `g : Z ⟶ Y` be morphisms of locally
Noetherian formal algebraic spaces over `S`. If `f` is flat in the sense of Definition 0GCC and
the morphism of reductions `g_red : Z_red ⟶ Y_red` is locally of finite type, then the base
change `X ×_Y Z ⟶ Z` is flat.

Flatness of arrows of `WAdm^{Noeth}` is stable under base change by arrows of finite type on
reductions by part (1) of Stacks 0GCA, which the library proves outright; Remark 0GBG transfers
that to the second projection of the fibre product, on the two inputs `h31` and `hcover` it
carries — the invariance of flatness under isomorphism of targets is read off the locality
field of the stability bundle, whose first axiom it is; and the hypothesis on `g_red` becomes the
chart condition the transfer
consumes by the implication (4) ⟹ (1) of Stacks 0GC7, on the two inputs `hbridge` and
`hredsquare`. Nothing about flatness is assumed in any of the five. -/
@[stacks 0GCE "part (1), on the 0GBG transfer inputs and the 0GC7 (4) implies (1) inputs"]
theorem isFlat_pullback_snd_of_isLocallyOfFiniteTypeOnReductions'
    (h31 : SourceCoverImpliesEveryAffineEtaleDiagram B S hS
      TopologicalRing.IsNoetherianAdic TopologicalRing.IsFlatHom)
    (hbridge : ChartPropertyIsFiniteTypeOnReductions B S hS)
    (hredsquare : IsLocallyOfFiniteTypeOnReductionsOnEveryAffineEtaleSquare B S hS)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hcover : HasBaseChangeCoverOverPullbackSnd B S hS f g)
    (hZ : IsLocallyCountablyIndexed B S hS Z) (hY : IsLocallyCountablyIndexed B S hS Y)
    (hf : IsFlat B S hS f) (hg : IsLocallyOfFiniteTypeOnReductions B S hS g) :
    IsFlat B S hS (pullback.snd f g) :=
  (isFlat_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS (pullback.snd f g)).mpr
    (hasPropertyOnEveryAffineEtaleDiagram_pullback_snd' B S hS TopologicalRing.IsFlatHom
      TopologicalRing.FiniteTypeOnReductionsProperty
      TopologicalRing.flat_isStableUnderBaseChangeByFiniteTypeOnReductions' h31 f g hcover
      ((isFlat_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS f).mp hf)
      (hasPropertyOnEveryAffineEtaleDiagram_finiteTypeOnReductions'
        B S hS hbridge hredsquare g hZ hY hg))

/-! ### Part (2): base change of a flat morphism locally of finite type -/

variable {B S hS}

/-- Condition (1) of Stacks 0ANG for flatness together with the property of Stacks 0GBW passes
from `f : X ⟶ Y` to the second projection `X ×_Y Z ⟶ Z` of its fibre product with any
`g : Z ⟶ Y`, by the variant of Stacks 0GBD for locally Noetherian formal algebraic spaces.

This is Remark 0GBF applied to part (2) of Stacks 0GCA,
`TopologicalRing.flatAdicFiniteType_isStableUnderBaseChange'`; nothing is asked of `g`, exactly as
there. -/
theorem hasPropertyOnEveryAffineEtaleDiagram_isFlatAdicOfFiniteTypeHom_pullback_snd'
    (h31 : SourceCoverImpliesEveryAffineEtaleDiagram B S hS
      TopologicalRing.IsNoetherianAdic IsFlatAdicOfFiniteTypeHom)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hcover : HasBaseChangeCoverOverPullbackSnd B S hS f g)
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsNoetherianAdic
      IsFlatAdicOfFiniteTypeHom f) :
    HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsNoetherianAdic
      IsFlatAdicOfFiniteTypeHom (pullback.snd f g) :=
  hasPropertyOnEveryAffineEtaleDiagram_pullback_snd_of_stableBaseChange' B S hS
    IsFlatAdicOfFiniteTypeHom TopologicalRing.flatAdicFiniteType_isStableUnderBaseChange' h31
    f g hcover hf

/-- **Stacks 0GCE, part (2), flatness.** Let `f : X ⟶ Y` and `g : Z ⟶ Y` be morphisms of locally
Noetherian formal algebraic spaces over `S`. If `f` is flat in the sense of Definition 0GCC and
locally of finite type in the sense of Stacks 0AM4, then the base change `X ×_Y Z ⟶ Z` is flat.

Flatness together with the property of Stacks 0GBW is stable under arbitrary base change of
arrows of `WAdm^{Noeth}` by part (2) of Stacks 0GCA, which the library proves outright; Remark
0GBF transfers that
to the second projection on the inputs `h31` and `hcover`; and Stacks 0GC0, carried as
`h0GC0`, turns the hypothesis on `f` into the chart condition and is not used on the conclusion,
which is read off by `isFlat_iff_hasPropertyOnEveryAffineEtaleDiagram`. -/
theorem isFlat_pullback_snd_of_isLocallyOfFiniteType'
    (h31 : SourceCoverImpliesEveryAffineEtaleDiagram B S hS
      TopologicalRing.IsNoetherianAdic IsFlatAdicOfFiniteTypeHom)
    (h0GC0 : ChartConditionIsLocallyOfFiniteTypeNoetherian B S hS)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hcover : HasBaseChangeCoverOverPullbackSnd B S hS f g)
    (hf : IsFlat B S hS f) (hft : IsLocallyOfFiniteType B S hS f) :
    IsFlat B S hS (pullback.snd f g) := by
  have h := hasPropertyOnEveryAffineEtaleDiagram_isFlatAdicOfFiniteTypeHom_pullback_snd' h31 f g
    hcover (hasPropertyOnEveryAffineEtaleDiagram_isFlatAdicOfFiniteTypeHom h0GC0 f hf hft)
  refine (isFlat_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS (pullback.snd f g)).mpr ?_
  intro U V a b t hU hV ha hb hsq A R _ _ _ _ _ _ _ _ hA hRc hwa D E eU eV φ hφ
  exact (h U V a b t hU hV ha hb hsq A R hA hRc hwa D E eU eV φ hφ).1

/-- **Stacks 0GCE, part (2), locally of finite type.** Let `f : X ⟶ Y` and `g : Z ⟶ Y` be
morphisms of locally Noetherian formal algebraic spaces over `S`. If `f` is flat in the sense of
Definition 0GCC and locally of finite type in the sense of Stacks 0AM4, then the base change
`X ×_Y Z ⟶ Z` is locally of finite type.

The chart condition for flatness together with the property of Stacks 0GBW passes to the second
projection as in the flatness half; its second conjunct is condition (1) of Stacks 0GC0 for the
projection, and `h0GC0` reads it back as the predicate of Stacks 0AM4. -/
theorem isLocallyOfFiniteType_pullback_snd_of_isFlat'
    (h31 : SourceCoverImpliesEveryAffineEtaleDiagram B S hS
      TopologicalRing.IsNoetherianAdic IsFlatAdicOfFiniteTypeHom)
    (h0GC0 : ChartConditionIsLocallyOfFiniteTypeNoetherian B S hS)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hcover : HasBaseChangeCoverOverPullbackSnd B S hS f g)
    (hf : IsFlat B S hS f) (hft : IsLocallyOfFiniteType B S hS f) :
    IsLocallyOfFiniteType B S hS (pullback.snd f g) := by
  have h := hasPropertyOnEveryAffineEtaleDiagram_isFlatAdicOfFiniteTypeHom_pullback_snd' h31 f g
    hcover (hasPropertyOnEveryAffineEtaleDiagram_isFlatAdicOfFiniteTypeHom h0GC0 f hf hft)
  refine (h0GC0 (pullback.snd f g)).mpr ?_
  intro U V a b t hU hV ha hb hsq A R _ _ _ _ _ _ _ _ hA hRc hwa D E eU eV φ hφ
  exact (h U V a b t hU hV ha hb hsq A R hA hRc hwa D E eU eV φ hφ).2

/-! ### Part (2) without the quantifier-widened 0GC0 comparison

The two statements of this section are the two conclusions of Stacks 0GCE, part (2), and they
replace the two above: neither mentions `ChartConditionIsLocallyOfFiniteTypeNoetherian`, which
is false. -/

/-- A flat morphism locally of finite type between locally countably indexed formal algebraic
spaces over `S` satisfies condition (1) of **Stacks 0ANG** for flatness together with the
property of **Stacks 0GBW**, with nothing assumed.

The two chart conditions being conjoined are the two conjuncts. The first is
`isFlat_iff_hasPropertyOnEveryAffineEtaleDiagram`, which is unconditional. The second is the
implication (4) ⟹ (1) of **Stacks 0GC0** read at the class `WAdm^{Noeth}`, and at that class it
needs no input about the type of a chart, unlike Stacks 0GC0 at `WAdm^{adic*}`: condition (1)
of **Stacks 0ANW** is equivalent to `f` being locally of finite type outright, by
`isLocallyOfFiniteType_tfae'`, a Noetherian adic ring is countably indexed weakly admissible, and
on a chart map presented by Noetherian adic rings being taut and topologically of finite type is
being adic and topologically of finite type by the equivalence of conditions (1) and (2) of
Stacks 0GBW, every ideal of definition of a Noetherian ring being finitely generated. So the
class hypothesis of the condition supplies what `ChartPresentationIsNoetherianAdic` would
otherwise have to. -/
theorem hasPropertyOnEveryAffineEtaleDiagram_isFlatAdicOfFiniteTypeHom_of_isLocallyOfFiniteType
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyCountablyIndexed B S hS X) (hY : IsLocallyCountablyIndexed B S hS Y)
    (hf : IsFlat B S hS f) (hft : IsLocallyOfFiniteType B S hS f) :
    HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsNoetherianAdic
      IsFlatAdicOfFiniteTypeHom f := by
  have hP := (isFlat_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS f).mp hf
  have hT := ((isLocallyOfFiniteType_tfae' f hX hY).out 4 1).mp hft
  intro U V a b t hU hV ha hb hsq A R _ _ _ _ _ _ _ _ hA hRc hwa D E eU eV φ hφ
  have hAfg : ∃ I : Ideal A, TopologicalRing.IsIdealOfDefinition I ∧ I.FG := by
    have : IsNoetherianRing A := hA.2
    obtain ⟨⟨I, hIdef, -⟩, -⟩ := hA.1
    exact ⟨I, hIdef, Ideal.fg_of_isNoetherianRing I⟩
  have hRfg : ∃ J : Ideal R, TopologicalRing.IsIdealOfDefinition J ∧ J.FG := by
    have : IsNoetherianRing R := hRc.2
    obtain ⟨⟨J, hJdef, -⟩, -⟩ := hRc.1
    exact ⟨J, hJdef, Ideal.fg_of_isNoetherianRing J⟩
  refine ⟨hP U V a b t hU hV ha hb hsq A R hA hRc hwa D E eU eV φ hφ,
    ((Rig.adicFiniteType_tfae φ.toRingHom hA.1 hRc.1 hAfg hRfg).out 2 1).mp ?_⟩
  exact hT U V a b t hU hV ha hb hsq A R
    (isCountablyWeaklyAdmissible_of_isNoetherianAdic hA.1)
    (isCountablyWeaklyAdmissible_of_isNoetherianAdic hRc.1) hwa D E eU eV φ hφ

/-- **Stacks 0GCE, part (2), flatness.** Let `f : X ⟶ Y` and `g : Z ⟶ Y` be morphisms of locally
Noetherian formal algebraic spaces over `S`. If `f` is flat in the sense of Definition 0GCC and
locally of finite type in the sense of Stacks 0AM4, then the base change `X ×_Y Z ⟶ Z` is flat.

Flatness together with the property of Stacks 0GBW is stable under arbitrary base change of
arrows of `WAdm^{Noeth}` by part (2) of Stacks 0GCA, which the library proves outright, and
Remark 0GBF transfers that to the second projection. The hypotheses on `f` become the chart
condition the transfer consumes by
`hasPropertyOnEveryAffineEtaleDiagram_isFlatAdicOfFiniteTypeHom_of_isLocallyOfFiniteType`, and
the conclusion is read back off the first conjunct by
`isFlat_iff_hasPropertyOnEveryAffineEtaleDiagram`; both are unconditional, so the comparison of
Stacks 0GC0 is no longer an input here.

The source asks `X` and `Y` to be locally Noetherian, which gives `hX` and `hY` by Stacks 0AKY
and Stacks 0AIK, so this is at least as general as part (2). -/
theorem isFlat_pullback_snd_of_isFlat_of_isLocallyOfFiniteType
    (h31 : SourceCoverImpliesEveryAffineEtaleDiagram B S hS
      TopologicalRing.IsNoetherianAdic IsFlatAdicOfFiniteTypeHom)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hX : IsLocallyCountablyIndexed B S hS X) (hY : IsLocallyCountablyIndexed B S hS Y)
    (hcover : HasBaseChangeCoverOverPullbackSnd B S hS f g)
    (hf : IsFlat B S hS f) (hft : IsLocallyOfFiniteType B S hS f) :
    IsFlat B S hS (pullback.snd f g) := by
  have h := hasPropertyOnEveryAffineEtaleDiagram_isFlatAdicOfFiniteTypeHom_pullback_snd' h31 f g
    hcover (hasPropertyOnEveryAffineEtaleDiagram_isFlatAdicOfFiniteTypeHom_of_isLocallyOfFiniteType
      f hX hY hf hft)
  refine (isFlat_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS (pullback.snd f g)).mpr ?_
  intro U V a b t hU hV ha hb hsq A R _ _ _ _ _ _ _ _ hA hRc hwa D E eU eV φ hφ
  exact (h U V a b t hU hV ha hb hsq A R hA hRc hwa D E eU eV φ hφ).1

/-- **Stacks 0GCE, part (2), locally of finite type.** Let `f : X ⟶ Y` and `g : Z ⟶ Y` be
morphisms of locally Noetherian formal algebraic spaces over `S`. If `f` is locally of finite
type in the sense of Stacks 0AM4, then the base change `X ×_Y Z ⟶ Z` is locally of finite type.

The second projection of the fibre product is a base change of `f`, and a base change of a
morphism locally of finite type is locally of finite type by **Stacks 0AQ5**, which the library
proves outright as `IsLocallyOfFiniteType.of_isPullback`. Nothing else is needed, so neither
flatness of `f` nor the locally Noetherian hypotheses of the source nor the inputs of the
transfer of Remark 0GBF appear: the conclusion holds at every morphism of fppf sheaves, which is
at least as general as part (2) of the source. -/
@[stacks 0GCE "part (2), locally of finite type, from Stacks 0AQ5 alone -- the second \
projection is a base change of `f`. No input of Remark 0GBF and no comparison of Stacks 0GC0 \
is used, and flatness of `f` is not used"]
theorem isLocallyOfFiniteType_pullback_snd_of_isLocallyOfFiniteType {X Y Z : FppfSheaf B S hS}
    (f : X ⟶ Y) (g : Z ⟶ Y) (hft : IsLocallyOfFiniteType B S hS f) :
    IsLocallyOfFiniteType B S hS (pullback.snd f g) :=
  IsLocallyOfFiniteType.of_isPullback B S hS (IsPullback.of_hasPullback f g).flip hft

end AlgebraicGeometry.FormalSpace

end
