module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RepresentedHomotopyPullbackCoherenceConsequences
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeDescentSchemeLimitOfSize

/-!
# Stacks 0DKV: descent of derived homomorphisms in Situation 0DKU

In Situation 0DKU let `K₀` and `L₀` be objects of `D(𝒪_{X₀})`, and write `Kᵢ = Lf_{i0}^*K₀`,
`Lᵢ = Lf_{i0}^*L₀`, `K = Lf₀^*K₀` and `L = Lf₀^*L₀`.  If `K₀` is pseudo-coherent and `L₀` lies in
`D_QCoh(𝒪_{X₀})` and locally has finite Tor dimension as an object of
`D((X₀ → Y₀)⁻¹𝒪_{Y₀})`, then the comparison map
`colim_{i ≥ 0} Hom_{D(𝒪_{Xᵢ})}(Kᵢ, Lᵢ) ⟶ Hom_{D(𝒪_X)}(K, L)` is an isomorphism.

The proof is `AlgebraicGeometry.Space.RelativeDescentSituation.homDescentOfPseudoCoherent_proved`
(reduction to affine pieces by Mayer–Vietoris and the induction principle of Stacks 08GP, and on
an affine piece the case of schemes, Stacks 0DI7, read through Stacks 071Q), in the elementary
form `AlgebraicGeometry.Space.RelativeDescentSituation.HomDescent`, which is the statement about
the colimit by `AlgebraicGeometry.Space.RelativeDescentSituation.homDescent_iff_isIso_colimitDesc`.

## Main results

* `RelativeDescentSituation.isIso_colimitDesc_homCocone_of_isPseudoCoherent`:
  Stacks 0DKV, for a situation whose limit `Y = lim Yᵢ` is the limit of algebraic spaces of
  Stacks 07SF (`AlgebraicGeometry.Space.RelativeDescentSituation.IsSchemeLimit`).
* `RelativeDescentSituation.isIso_colimitDesc_homCocone_of_isPseudoCoherent_of_mk_lt`:
  Stacks 0DKV with no condition on the limit, for every directed index set with fewer elements
  than the cofinality of the size cutoff of the site.
* `RelativeDescentSituation.isIso_colimitDesc_homCocone_of_isPseudoCoherent_of_countable`:
  Stacks 0DKV with no condition on the limit, for every countable directed index set, on every
  big fppf site.

## Implementation notes

`AlgebraicGeometry.Space.RelativeDescentSituation` records `Y = lim Yᵢ` only as a limit cone of
presheaves on the size-bounded big fppf site.  The limit of Situation 0DKU is the limit of
algebraic spaces of Stacks 07SF, which over an affine chart of `Y₀` is the spectrum of the
colimit of the rings of the affine base changes, a limit of schemes; this is the predicate
`AlgebraicGeometry.Space.RelativeDescentSituation.IsSchemeLimit`.  The two readings agree when
the index set is small compared with the site
(`AlgebraicGeometry.Space.RelativeDescentSituation.isSchemeLimit_of_size`), in particular for
countable index sets, but not in general: the module documentation of
`StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeDescentSchemeLimit`
describes a situation indexed by the finite subsets of the cutoff whose presheaf limit is empty
while the colimit of the homomorphism groups is a nonzero field, so for the presheaf reading
alone the conclusion fails.  The index type lives in the universe of the schemes, that of
Stacks 0DI7.  The derived pullbacks are composed with the canonical pseudofunctoriality datum
`AlgebraicGeometry.Space.DerivedPullbackComposition.canonical`.

## References

* [Stacks Project, Tag 0DKV](https://stacks.math.columbia.edu/tag/0DKV)
* [Stacks Project, Tag 0DKU](https://stacks.math.columbia.edu/tag/0DKU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Space.RelativeDescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]

/-- **Stacks 0DKV.** In Situation 0DKU, with `Y = lim Yᵢ` the limit of algebraic spaces of
Stacks 07SF (a limit of schemes on affine charts), let `K₀`, `L₀` be objects of `D(𝒪_{X₀})`
with `K₀` pseudo-coherent and `L₀ ∈ D_QCoh(𝒪_{X₀})` locally of finite Tor dimension as an object
of `D((X₀ → Y₀)⁻¹𝒪_{Y₀})`.  Then the comparison map
`colim_{i ≥ 0} Hom_{D(𝒪_{Xᵢ})}(Lf_{i0}^*K₀, Lf_{i0}^*L₀) ⟶ Hom_{D(𝒪_X)}(Lf₀^*K₀, Lf₀^*L₀)`
is an isomorphism. -/
@[stacks 0DKV "the full statement; the condition D.IsSchemeLimit on the limit cone is the meaning \
  of Y = lim Y_i in Situation 0DKU, the limit of algebraic spaces of Stacks 07SF, which the \
  presheaf limit cone of RelativeDescentSituation does not record by itself (see the module \
  documentation of RelativeDescentSchemeLimit for a situation where the presheaf limit is \
  empty and the conclusion fails); it holds automatically for small index sets, see \
  isIso_colimitDesc_homCocone_of_isPseudoCoherent_of_mk_lt and \
  isIso_colimitDesc_homCocone_of_isPseudoCoherent_of_countable"]
theorem isIso_colimitDesc_homCocone_of_isPseudoCoherent
    (D : RelativeDescentSituation B S hS hZ I) (hD : D.IsSchemeLimit)
    (K₀ L₀ : derivedModules B S hS D.initialSource) (hK₀ : IsPseudoCoherentObject K₀)
    (hL₀ : IsInQuasicoherentDerived D.initialSource L₀)
    (hL₀tor : HasLocallyFiniteTorDimensionAlong D.initialStructure L₀) :
    IsIso (colimit.desc (D.homFunctor (DerivedPullbackComposition.canonical B S hS) K₀ L₀)
      (D.homCocone (DerivedPullbackComposition.canonical B S hS) K₀ L₀)) :=
  (D.homDescent_iff_isIso_colimitDesc _ K₀ L₀).1
    (homDescentOfPseudoCoherent_proved I D hD K₀ L₀ hK₀ hL₀ hL₀tor)

/-- **Stacks 0DKV for a small index set.** In Situation 0DKU indexed by a directed set with
fewer elements than the cofinality of the size cutoff of the site, let `K₀`, `L₀` be objects of
`D(𝒪_{X₀})` with `K₀` pseudo-coherent and `L₀ ∈ D_QCoh(𝒪_{X₀})` locally of finite Tor dimension
as an object of `D((X₀ → Y₀)⁻¹𝒪_{Y₀})`.  Then the comparison map
`colim_{i ≥ 0} Hom_{D(𝒪_{Xᵢ})}(Lf_{i0}^*K₀, Lf_{i0}^*L₀) ⟶ Hom_{D(𝒪_X)}(Lf₀^*K₀, Lf₀^*L₀)`
is an isomorphism.  No condition on the limit is needed: for such index sets the limit of
presheaves is the limit of algebraic spaces of Stacks 07SF. -/
@[stacks 0DKV "the full statement for every directed index set I with #I below the \
  cofinality of the size cutoff of the site, with no condition on the limit: the limit of \
  presheaves of RelativeDescentSituation is then the limit of algebraic spaces of Stacks 07SF \
  (isSchemeLimit_of_size)"]
theorem isIso_colimitDesc_homCocone_of_isPseudoCoherent_of_mk_lt
    (D : RelativeDescentSituation B S hS hZ I) (hI : #I < B.cutoff.ord.cof)
    (K₀ L₀ : derivedModules B S hS D.initialSource) (hK₀ : IsPseudoCoherentObject K₀)
    (hL₀ : IsInQuasicoherentDerived D.initialSource L₀)
    (hL₀tor : HasLocallyFiniteTorDimensionAlong D.initialStructure L₀) :
    IsIso (colimit.desc (D.homFunctor (DerivedPullbackComposition.canonical B S hS) K₀ L₀)
      (D.homCocone (DerivedPullbackComposition.canonical B S hS) K₀ L₀)) :=
  D.isIso_colimitDesc_homCocone_of_isPseudoCoherent (D.isSchemeLimit_of_size hI) K₀ L₀ hK₀ hL₀
    hL₀tor

/-- **Stacks 0DKV for a countable index set.** In Situation 0DKU indexed by a countable
directed set, on any big fppf site, let `K₀`, `L₀` be objects of `D(𝒪_{X₀})` with `K₀`
pseudo-coherent and `L₀ ∈ D_QCoh(𝒪_{X₀})` locally of finite Tor dimension as an object of
`D((X₀ → Y₀)⁻¹𝒪_{Y₀})`.  Then the comparison map
`colim_{i ≥ 0} Hom_{D(𝒪_{Xᵢ})}(Lf_{i0}^*K₀, Lf_{i0}^*L₀) ⟶ Hom_{D(𝒪_X)}(Lf₀^*K₀, Lf₀^*L₀)`
is an isomorphism.  The size cutoff of every big fppf site has uncountable cofinality. -/
@[stacks 0DKV "the full statement for every countable directed index set, on every big fppf \
  site, with no condition on the limit"]
theorem isIso_colimitDesc_homCocone_of_isPseudoCoherent_of_countable [Countable I]
    (D : RelativeDescentSituation B S hS hZ I)
    (K₀ L₀ : derivedModules B S hS D.initialSource) (hK₀ : IsPseudoCoherentObject K₀)
    (hL₀ : IsInQuasicoherentDerived D.initialSource L₀)
    (hL₀tor : HasLocallyFiniteTorDimensionAlong D.initialStructure L₀) :
    IsIso (colimit.desc (D.homFunctor (DerivedPullbackComposition.canonical B S hS) K₀ L₀)
      (D.homCocone (DerivedPullbackComposition.canonical B S hS) K₀ L₀)) :=
  D.isIso_colimitDesc_homCocone_of_isPseudoCoherent_of_mk_lt
    (Cardinal.mk_le_aleph0.trans_lt B.aleph0_lt_cutoff_cof) K₀ L₀ hK₀ hL₀ hL₀tor

end AlgebraicGeometry.Space.RelativeDescentSituation

end
