module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalKunnethMapOfSheaves
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.KunnethIsomorphism
import StacksCore.Tactic.StacksAttribute

/-!
# The global Künneth map for two module sheaves is an isomorphism

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes with `S` affine, let `W = X ×_S Y` with
projections `p` and `q`, and set `A = Γ(S, 𝒪_S)`.  For `ℱ` on `X` and `𝒢` on `Y` quasi-coherent
and flat over `S`, with `X` and `Y` quasi-compact with affine diagonal, [Stacks, Tag 0FU4]
asserts that the Künneth map of [Stacks, Tag 0G49]

`RΓ(X, ℱ) ⊗^𝐋_A RΓ(Y, 𝒢) ⟶ RΓ(X ×_S Y, p^*ℱ ⊗_{𝒪_W} q^*𝒢)`

is an isomorphism in `D(A)`.

`Stacks.Cohomology.GlobalKunneth.kunnethMapOfSheaves` is that map followed by nothing: by
`Stacks.Cohomology.GlobalKunneth.kunnethMapOfSheaves_eq` it is the derived global Künneth map of
[Stacks, Tag 0G7V] at `ℱ[0]` and `𝒢[0]`, followed by derived global sections of the
derived-to-ordinary comparison
`Stacks.Cohomology.GlobalKunneth.externalTensorComparison`.  So the assertion splits into
the invertibility of the derived map — which is [Stacks, Tag 0FLQ], carried in this repository by
`Stacks.Cohomology.DerivedKunneth.isIso_kunnethMap_of_projectionFormulas_of_baseChange` and
itself only conditionally — and the invertibility of that one comparison.  Both are carried here
as explicit hypotheses, together with the invertibility of the `A`-linear global cup product on
the base; what is proved is that the three suffice.

## Main results

* `Stacks.Cohomology.GlobalKunneth.isIso_externalTensorComparison`: the derived-to-ordinary
  comparison `Lp^*ℱ[0] ⊗^𝐋 Lq^*𝒢[0] ⟶ (p^*ℱ ⊗ q^*𝒢)[0]` is invertible as soon as its three
  nontrivial factors are; the fourth factor is discharged outright.
* `Stacks.Cohomology.GlobalKunneth.isIso_kunnethMapOfSheaves`: the Künneth map for two module
  sheaves on a commuting square of ringed spaces is invertible as soon as the global cup product
  on the base, the relative Künneth map of [Stacks, Tag 0FLP] at the two sheaves in degree zero,
  and `externalTensorComparison` are.
* `Stacks.Cohomology.GlobalKunneth.isIso_kunnethMapOfSheavesScheme`: **[Stacks, Tag 0FU4]** at the
  fibre product of two schemes, granted those same three inputs.
* `isIso_kunnethMapOfSheavesScheme_of_projectionFormulas_of_baseChange`, in the same namespace:
  the same, with the relative Künneth input replaced by the four inputs of [Stacks, Tag 0FLQ], so
  that every hypothesis is the conclusion of one named result of the source.

## Implementation notes

*What is carried and why.*  Three hypotheses, none of which this repository can supply.

* `hκ`, the invertibility of the global cup product `κ` at the pair `(Ra_*ℱ[0], Rb_*𝒢[0])`.  The
  datum `Stacks.Cohomology.GlobalKunneth.GlobalCupProduct` is a bare morphism of bifunctors, with
  no laws: the zero morphism inhabits it, and for that choice the Künneth map is zero and the
  assertion false.  So some hypothesis pinning `κ` is unavoidable, and affineness of `S` is what
  the source uses to supply this one.  Nothing in this repository constructs a global cup product
  over a space with nonzero cohomology — the residual gap recorded in
  `Stacks.Cohomology.DerivedGlobalCupProduct.OnePointComparison`.
* `hrel`, the invertibility of the relative Künneth map of [Stacks, Tag 0FLP] at `(ℱ[0], 𝒢[0])`.
  This is the conclusion of [Stacks, Tag 0FLQ], obtainable from
  `Stacks.Cohomology.DerivedKunneth.isIso_kunnethMap_of_projectionFormulas_of_baseChange` once its
  four named inputs are supplied: the projection formula of [Stacks, Tag 08EU] for `a` and for
  `p`, the base-change comparison of [Stacks, Tag 08IB] for the square, and the
  [Stacks, Tag 079U]/[Stacks, Tag 0D5S] monoidality coherence.  It is carried here as one
  hypothesis rather than four.
* `hext`, the invertibility of
  `Lp^*ℱ[0] ⊗^𝐋_{𝒪_W} Lq^*𝒢[0] ⟶ (p^*ℱ ⊗_{𝒪_W} q^*𝒢)[0]`.  Mathematically this is where flatness
  of `ℱ` and `𝒢` over `S` enters: it makes the two derived pullbacks underived and kills the
  higher Tor of the tensor product.  `isIso_externalTensorComparison` reduces it to the three
  comparisons that actually carry that content, discharging the fourth factor outright.

*Why relative flatness does not discharge `hext`.*  Every criterion in this library for the three
remaining factors is stated at K-flatness over the *structure sheaf*:
`Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat` and
`Stacks.SheafOfModules.isIso_toTensor_of_kFlat_left`/`_right`.  What [Stacks, Tag 0FU4] supplies
instead is `AlgebraicGeometry.IsFlatOver`, flatness of the stalks over the stalks of `𝒪_S`, and
the two conditions are incomparable: `ℱ` flat over `S` need not be flat over `𝒪_X`, and `p^*ℱ`
need not be flat over `𝒪_W`.  The bridge that would be needed is the stalk computation
identifying `Lp^*ℱ ⊗^𝐋_{𝒪_W} Lq^*𝒢` with `ℱ ⊗^𝐋_{𝒪_S} 𝒢` on the fibre product.  That bridge is
absent, and demonstrably so: `AlgebraicGeometry.PointwiseBaseChangeOfFlatOver`, in
`StacksFrontier/AlgebraicGeometry/BaseChange/TensorFlatPushforwardBaseChange.lean`, is exactly this
stalk check for a cartesian square — "the only step the source performs rather than cites" — and
that module declares it a `Prop` and carries it as a hypothesis rather than proving it, while
recording in its own notes that "K-flatness over `𝒪_X` is neither implied by nor implies flatness
of the terms over `S`".  So `hext` stays carried here, and supplying that stalk computation is the
work that would discharge it.

*Why the source's own proof is not followed.*  [Stacks, Tag 0FU4] is proved by computing both
sides with the Čech complexes of finite affine open coverings.  Every scheme-theoretic ingredient
of that argument is available — the comparison of the Čech complex with `RΓ` for a covering by
affine opens of a scheme with affine diagonal
(`Stacks.Cohomology.Cech.isIso_cechCohomologyToCohomology_app_of_affineDiagonal`), the
K-flatness of the total Čech complex (`AlgebraicGeometry.kFlat_totalCechComplex`,
[Stacks, Tag 0FMQ]), the affineness of `∐ U_i ⟶ X` used for the dimension shifting
([Stacks, Tag 01SG]), and the Čech cup product ([Stacks, Tag 07MB]) — but the Čech-level Künneth
arrow `Tot(Č(𝒰, ℱ) ⊗_A Č(𝒱, 𝒢)) ⟶ Č(𝒲, p^*ℱ ⊗ q^*𝒢)` of [Stacks, Tag 0FLU] and its
compatibility with the cup product ([Stacks, Tag 0FKV]) are not, and without them the Čech
computation cannot be connected to the map of [Stacks, Tag 0G49] at all.

*The geometric hypotheses are stated but not consumed.*  They are carried as underscore-prefixed
binders and instance arguments so that the statement is the source's, following
`Stacks.Cohomology.DerivedKunnethExt.isIso_kunnethExtMap_cartesian` for [Stacks, Tag 0FXZ].
Affineness of the diagonal is spelled, as everywhere in this repository, as affineness of
`pullback.diagonal (terminal.from X)`; flatness over the base is
`AlgebraicGeometry.IsFlatOver`, the flatness of every stalk over the corresponding stalk of
`𝒪_S`, which by the discussion following [Stacks, Tag 08KT] is flatness as an `a^{-1}𝒪_S`-module.

## References

* [Stacks Project, Tag 0FU4](https://stacks.math.columbia.edu/tag/0FU4)
* [Stacks Project, Tag 0G49](https://stacks.math.columbia.edu/tag/0G49)
* [Stacks Project, Tag 0G7V](https://stacks.math.columbia.edu/tag/0G7V)
* [Stacks Project, Tag 0FLQ](https://stacks.math.columbia.edu/tag/0FLQ)
* [Stacks Project, Tag 0FLP](https://stacks.math.columbia.edu/tag/0FLP)
* [Stacks Project, Tag 0FMQ](https://stacks.math.columbia.edu/tag/0FMQ)
* [Stacks Project, Tag 08KT](https://stacks.math.columbia.edu/tag/08KT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedProjectionFormula
open Stacks.DerivedTensor.RingedSite
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.GlobalKunneth

attribute [local instance] HasDerivedCategory.standard

/-! ### The derived-to-ordinary comparison, reduced to its three irreducible factors -/

section Comparison

variable {X Y W : RingedSpace.{u, u}} (p : W ⟶ X) (q : W ⟶ Y)

/-- **The comparison `Lp^*ℱ[0] ⊗^𝐋_{𝒪_W} Lq^*𝒢[0] ⟶ (p^*ℱ ⊗_{𝒪_W} q^*𝒢)[0]` is invertible as
soon as its three nontrivial factors are.**  By
`Stacks.Cohomology.GlobalKunneth.externalTensorComparison_eq` the comparison is a composite of
four maps: the two derived-to-ordinary pullback comparisons
`Stacks.Cohomology.GlobalKunneth.pullbackSingleComparison`, the derived-to-ordinary tensor
comparison `toTensor` of [Stacks, Tag 06YU], and the degree-zero identification of the total
tensor complex.  The fourth is the image under `DerivedCategory.Q` of the `hom` of an
isomorphism, hence invertible unconditionally; this discharges it and leaves the other three.

Each of the three is the conclusion of a criterion the library has, but only at *absolute*
K-flatness over the structure sheaf:
`Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat` for the
first two and `Stacks.SheafOfModules.isIso_toTensor_of_kFlat_left` or `_right` for the third.
Flatness over the base `S`, which is what [Stacks, Tag 0FU4] assumes, neither implies nor is
implied by that — see the implementation notes. -/
theorem isIso_externalTensorComparison (F : Modules X.sheaf) (G : Modules Y.sheaf)
    (hp : IsIso (pullbackSingleComparison p F)) (hq : IsIso (pullbackSingleComparison q G))
    (htensor : IsIso ((canonicalDerivedTensorProduct W.sheaf).toTensor
      (singleC ((modulePullback p).obj F)) (singleC ((modulePullback q).obj G)))) :
    IsIso (externalTensorComparison p q F G) := by
  rw [externalTensorComparison_eq]
  have := @Functor.map_isIso _ _ _ _ _ _ (derivedTensorProductFunctor W.sheaf) _ hp
  have := NatIso.isIso_app_of_isIso
    ((derivedTensorProductFunctor W.sheaf).map (pullbackSingleComparison p F))
    ((derivedPullback q).obj (singleD G))
  have := @Functor.map_isIso _ _ _ _ _ _ ((derivedTensorProductFunctor W.sheaf).obj
    (singleD ((modulePullback p).obj F))) _ hq
  refine @IsIso.comp_isIso _ _ _ _ _ _ _ ?_ (@IsIso.comp_isIso _ _ _ _ _ _ _ ?_
    (@IsIso.comp_isIso _ _ _ _ _ _ _ ?_ ?_))
  · infer_instance
  · infer_instance
  · exact htensor
  · exact (DerivedCategory.Q.mapIso (HomologicalComplex.mapBifunctorSingleIso
      (Stacks.SheafOfModules.Tensor.sheafTensor W.sheaf)
      ((modulePullback p).obj F) ((modulePullback q).obj G))).isIso_hom

end Comparison

/-! ### The reduction to the derived map and the one comparison -/

section

variable {S X Y W : RingedSpace.{u, u}} (a : X ⟶ S) (b : Y ⟶ S) (p : W ⟶ X) (q : W ⟶ Y)
  (f : W ⟶ S) (hp : p ≫ a = f) (hq : q ≫ b = f)

/-- **The three steps of the proof of [Stacks, Tag 0FU4] suffice.**  The Künneth map for two
module sheaves

`RΓ(X, ℱ) ⊗^𝐋_A RΓ(Y, 𝒢) ⟶ RΓ(W, p^*ℱ ⊗_{𝒪_W} q^*𝒢)`

is invertible as soon as the global cup product `κ` on the base is invertible at the pair
`(Ra_*ℱ[0], Rb_*𝒢[0])`, the relative Künneth map of [Stacks, Tag 0FLP] is invertible at
`(ℱ[0], 𝒢[0])`, and the derived-to-ordinary comparison
`Stacks.Cohomology.GlobalKunneth.externalTensorComparison` is invertible.  By
`Stacks.Cohomology.GlobalKunneth.kunnethMapOfSheaves_eq` the map is the global Künneth map of
[Stacks, Tag 0G7V] at the two sheaves in degree zero followed by derived global sections of that
comparison, and the first factor is invertible by
`Stacks.Cohomology.GlobalKunneth.isIso_kunnethGlobalMap`. -/
theorem isIso_kunnethMapOfSheaves (κ : GlobalCupProduct S) (F : Modules X.sheaf)
    (G : Modules Y.sheaf)
    (hκ : IsIso (κ.app ((derivedPushforward a).obj (singleD F),
      (derivedPushforward b).obj (singleD G))))
    (hrel : IsIso (Stacks.Cohomology.DerivedKunneth.kunnethMap a b p q f hp hq
      (singleD F) (singleD G)))
    (hext : IsIso (externalTensorComparison p q F G)) :
    IsIso (kunnethMapOfSheaves a b p q f hp hq κ F G) := by
  have := isIso_kunnethGlobalMap a b p q f hp hq κ (singleD F) (singleD G) hκ hrel
  rw [kunnethMapOfSheaves_eq]
  have := @Functor.map_isIso _ _ _ _ _ _ (sectionsOverBase f) _ hext
  infer_instance

end

/-! ### [Stacks, Tag 0FU4] at the fibre product of two schemes -/

section Schemes

variable {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-- **[Stacks, Tag 0FU4].**  Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes with `S`
affine, let `A = Γ(S, 𝒪_S)` and let `p`, `q` be the projections of `W = X ×_S Y`.  If `X` and `Y`
are quasi-compact with affine diagonal and `ℱ` on `X`, `𝒢` on `Y` are quasi-coherent and flat
over `S`, then the Künneth map of [Stacks, Tag 0G49]

`RΓ(X, ℱ) ⊗^𝐋_A RΓ(Y, 𝒢) ⟶ RΓ(X ×_S Y, ℱ ⊠ 𝒢)`

is an isomorphism in `D(A)`.

The three inputs of the proof are carried as the hypotheses `hκ`, `hrel` and `hext`, and the
geometric hypotheses are therefore not consumed; the implementation notes of this file say what
each of the three is and why none is available in the library.  `hκ` is the invertibility of the
`A`-linear global cup product on the affine base, `hrel` is [Stacks, Tag 0FLQ] at the two sheaves
placed in degree zero, and `hext` is the invertibility of the derived-to-ordinary comparison in
which the source consumes the flatness of `ℱ` and `𝒢`.  What is proved here is that the three
suffice. -/
@[stacks 0FU4 "the isomorphism at X ×_S Y; three inputs are carried, so the geometric \
hypotheses are not consumed: hκ, invertibility of the global cup product on the affine base, \
which no bare GlobalCupProduct has; hrel, Tag 0FLQ at the sheaves in degree zero; hext, the \
06YU comparison, which the tag's relative S-flatness cannot discharge in this library"]
theorem isIso_kunnethMapOfSheavesScheme [IsAffine S] [CompactSpace X] [CompactSpace Y]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (κ : GlobalCupProduct S.toRingedSpace) (F : X.Modules) (G : Y.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent]
    (_hF : IsFlatOver a.toLRSHom.toShHom F) (_hG : IsFlatOver b.toLRSHom.toShHom G)
    (hκ : IsIso (κ.app ((derivedPushforward a.toLRSHom.toShHom).obj (singleD F),
      (derivedPushforward b.toLRSHom.toShHom).obj (singleD G))))
    (hrel : IsIso (Stacks.Cohomology.DerivedKunneth.kunnethMap a.toLRSHom.toShHom
      b.toLRSHom.toShHom (pullback.fst a b).toLRSHom.toShHom
      (pullback.snd a b).toLRSHom.toShHom (pullback.fst a b ≫ a).toLRSHom.toShHom rfl
      (toShHom_pullback_condition a b) (singleD F) (singleD G)))
    (hext : IsIso (externalTensorComparison (pullback.fst a b).toLRSHom.toShHom
      (pullback.snd a b).toLRSHom.toShHom F G)) :
    IsIso (kunnethMapOfSheavesScheme a b κ F G) :=
  isIso_kunnethMapOfSheaves a.toLRSHom.toShHom b.toLRSHom.toShHom
    (pullback.fst a b).toLRSHom.toShHom (pullback.snd a b).toLRSHom.toShHom
    (pullback.fst a b ≫ a).toLRSHom.toShHom rfl (toShHom_pullback_condition a b) κ F G
    hκ hrel hext

/-- **[Stacks, Tag 0FU4] with `hrel` unfolded into the four inputs of [Stacks, Tag 0FLQ].**  The
same conclusion as `Stacks.Cohomology.GlobalKunneth.isIso_kunnethMapOfSheavesScheme`, with the
invertibility of the relative Künneth map of [Stacks, Tag 0FLP] replaced by the four inputs from
which `Stacks.Cohomology.DerivedKunneth.isIso_kunnethMap_of_projectionFormulas_of_baseChange`
produces it: the [Stacks, Tag 079U]/[Stacks, Tag 0D5S] monoidality coherence `hcoh`, the
projection formula of [Stacks, Tag 08EU] for `a` and for `p`, and the base-change comparison of
[Stacks, Tag 08IB] for the square.  Every hypothesis is then the conclusion of a single named
result of the source, and none is a Künneth statement. -/
theorem isIso_kunnethMapOfSheavesScheme_of_projectionFormulas_of_baseChange [IsAffine S]
    [CompactSpace X] [CompactSpace Y]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (κ : GlobalCupProduct S.toRingedSpace) (F : X.Modules) (G : Y.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent]
    (hF : IsFlatOver a.toLRSHom.toShHom F) (hG : IsFlatOver b.toLRSHom.toShHom G)
    (hκ : IsIso (κ.app ((derivedPushforward a.toLRSHom.toShHom).obj (singleD F),
      (derivedPushforward b.toLRSHom.toShHom).obj (singleD G))))
    (hcoh : Stacks.Cohomology.DerivedKunneth.PullbackTensorComparisonComp
      a.toLRSHom.toShHom (pullback.fst a b).toLRSHom.toShHom
      ((derivedPushforward a.toLRSHom.toShHom).obj (singleD F))
      ((derivedPushforward b.toLRSHom.toShHom).obj (singleD G)))
    (hproj₁ : IsIso (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap
      a.toLRSHom.toShHom (singleD F)
      ((derivedPushforward b.toLRSHom.toShHom).obj (singleD G))))
    (hbase : IsIso (Stacks.Cohomology.DerivedKunneth.kunnethBaseChangeLeg a.toLRSHom.toShHom
      b.toLRSHom.toShHom (pullback.fst a b).toLRSHom.toShHom
      (pullback.snd a b).toLRSHom.toShHom (toShHom_pullback_condition a b) (singleD G)))
    (hproj₂ : IsIso (Stacks.Cohomology.DerivedKunneth.adjunctionTensorMapRight
      (derivedAdjunction (pullback.fst a b).toLRSHom.toShHom)
      (Functor.uncurry.obj (derivedTensorProductFunctor X.toRingedSpace.sheaf))
      (Functor.uncurry.obj (derivedTensorProductFunctor (pullback a b).toRingedSpace.sheaf))
      (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison
        (pullback.fst a b).toLRSHom.toShHom) (singleD F)
      ((derivedPullback (pullback.snd a b).toLRSHom.toShHom).obj (singleD G))))
    (hext : IsIso (externalTensorComparison (pullback.fst a b).toLRSHom.toShHom
      (pullback.snd a b).toLRSHom.toShHom F G)) :
    IsIso (kunnethMapOfSheavesScheme a b κ F G) :=
  isIso_kunnethMapOfSheavesScheme a b κ F G hF hG hκ
    (Stacks.Cohomology.DerivedKunneth.isIso_kunnethMap_of_projectionFormulas_of_baseChange
      a.toLRSHom.toShHom b.toLRSHom.toShHom (pullback.fst a b).toLRSHom.toShHom
      (pullback.snd a b).toLRSHom.toShHom (toShHom_pullback_condition a b) (singleD F)
      (singleD G) hcoh hproj₁ hbase hproj₂)
    hext

end Schemes

end Stacks.Cohomology.GlobalKunneth

end
