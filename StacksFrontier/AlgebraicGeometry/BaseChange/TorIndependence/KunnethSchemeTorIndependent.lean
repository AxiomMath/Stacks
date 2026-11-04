module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.KunnethOpenImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.Composition
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.ProjectionFormulaDischarged
public import StacksFrontier.AlgebraicGeometry.Perfect.TorIndependenceSymm
public import StacksFrontier.AlgebraicGeometry.UnboundedDerivedDirectImage.QuasiCoherence
public import StacksFrontier.RingTheory.Tor.Balancing
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.DerivedPullbackTensorBraided
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.RelativeCupProductCommutativity

/-!
# Tag 0FLQ at the fibre product of two schemes, reduced to Tag 08EU and Tag 08IB

Let `a : X ⟶ S` and `b : Y ⟶ S` be quasi-compact quasi-separated morphisms of schemes with `X`
and `Y` Tor independent over `S`, let `W = X ×_S Y` with projections `p` and `q`, and let
`K ∈ D_QCoh(𝒪_X)`, `M ∈ D_QCoh(𝒪_Y)`.  Tag 0FLQ asserts that the relative Künneth morphism of
Tag 0FLP

`Ra_*K ⊗^𝐋_{𝒪_S} Rb_*M ⟶ R(p ≫ a)_*(Lp^*K ⊗^𝐋_{𝒪_W} Lq^*M)`

is an isomorphism, and that over an affine base the global map of Tag 0G7V is one too.

`Stacks.Cohomology.DerivedKunneth.isIso_kunnethMap_of_projectionFormulas_of_baseChange` proves
this for an *arbitrary* commuting square of *ringed spaces* from three explicit invertibility
hypotheses `hproj₁`, `hbase`, `hproj₂`.  At that generality the three cannot be discharged: for a
square that is not cartesian the base change of Tag 08IB is false.  This module specializes that
statement to the tag's own situation — a cartesian square of schemes, with the tag's
quasi-compactness, quasi-separatedness, Tor-independence and quasi-coherence hypotheses — and
discharges what the library has.

**What is discharged.**  `hbase`, completely, from the library's carried form of Tag 08IB.
`hproj₁`, completely, from the library's carried form of Tag 08EU: its two geometric hypotheses
are the tag's own, and the quasi-coherence of `Rb_*M` it needs is Tag 08D5 part (1).

`hproj₂` as well.  It is the projection formula at `p` with the *two tensor factors
interchanged*, and Tag 08EU gives the standard order; the two are conjugate under the
commutativity constraints of Tag 0FPB, so `hproj₂` follows from Tag 08EU together with the
compatibility of the monoidality comparison of Tag 079U with those constraints.  That
compatibility is
`Stacks.Cohomology.DerivedRelativeCupProduct.PullbackTensorComparisonBraided`, and it is
**proved**: `Stacks.Cohomology.DerivedRelativeCupProduct.pullbackTensorComparisonBraided` in
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/RelativeCupProductCommutativity.lean`.

**What is left.**  Exactly the two propositions the source cites, Tag 08EU and Tag 08IB.  The
final statements below rest on those two and on nothing else beyond the tag's own hypotheses,
and no declaration in this module carries the tag `0FLQ`.

## Main results

All in the namespace `Stacks.Cohomology.DerivedKunneth`.

* `adjunctionTensorMapRight_braiding`: **the two orders of the projection-formula map are
  conjugate** under a pair of symmetries compatible with the monoidality comparison; stated at
  the level of abstract adjunctions, where its content lies.
* `isIso_kunnethBaseChangeLeg_pullback_of_torIndependent`: **the base-change input of Tag 0FLQ
  at the tag's hypotheses**, granted the carried Tag 08IB.
* `isIso_projectionFormulaMap_pullbackFst_of_projectionFormula`: **Tag 08EU at `p`, in the
  standard order**, granted the carried Tag 08EU; its quasi-compactness and quasi-separatedness
  come from `b` by base change and the quasi-coherence of `Lq^*M` from Tag 08DW part (1).
* `isIso_adjunctionTensorMapRight_pullbackFst_of_braided`: **`hproj₂`**, from that and the
  braiding compatibility of Tag 079U, which is proved.
* `isIso_kunnethMap_pullback_of_torIndependent`: **the first conclusion of Tag 0FLQ at the
  fibre product of two schemes**, granted the carried Tag 08EU, the carried Tag 08IB and
  `hproj₂`; and `isIso_kunnethMap_pullback_of_torIndependent_of_braided`, the same with
  `hproj₂` discharged through the braiding compatibility, so granted the two cited tags alone.
* `isIso_kunnethGlobalMapScheme_of_torIndependent` and
  `isIso_kunnethGlobalMapScheme_of_torIndependent_of_braided`: **the second conclusion**, over an
  affine base, granted the same inputs together with the invertibility `hκ` of the global cup
  product.

## Implementation notes

*The two cited inputs, in the library's own spelling.*  Tag 08EU and Tag 08IB are the two results
the source's first proof of Tag 0FLQ cites, and the library already names both at their full
hypotheses, as the carried propositions
`AlgebraicGeometry.ProjectionFormulaIsIsoOnQuasicoherent` and
`AlgebraicGeometry.DerivedBaseChangeIsIsoOnQuasicoherent` of
`StacksFrontier/AlgebraicGeometry/DerivedVarieties/FourierMukai/Composition.lean`.  They are taken
as hypotheses here rather than restated, so that substituting an unconditional proof of either is
a single edit.  Nothing weaker is assumed and nothing is duplicated: in particular the
Tor-independence input of Tag 08IB on affine charts,
`AlgebraicGeometry.BaseChangeChart.isIso_derivedBaseChangeComparison`, is *not* used below — see
the next note.

*Why the chartwise Tag 08IB does not suffice for `hbase`.*  `hbase` asks for invertibility of the
derived base-change map `La^*Rb_*M ⟶ Rp_*Lq^*M` of Tag 08HY, a morphism of `D(𝒪_X)`.  What
`AlgebraicGeometry.BaseChangeChart.isIso_derivedBaseChangeComparison` supplies is invertibility of
the *ring-level* comparison `K ⊗^𝐋_R R' ⟶ K ⊗^𝐋_A A'` of Tag 065Z on a cartesian affine-open
chart; its own docstring records that it "does not say that the derived base-change map
`Lg^*Rf_*K ⟶ Rf'_*L(g')^*K` of Stacks 08HY is an isomorphism", the passage between the two being
Tag 0DJ9.  Tag 0DJ9 is itself carried, in
`StacksFrontier/AlgebraicGeometry/BaseChange/TorIndependence/GlobalBaseChange.lean`, on the three
hypotheses `BaseChangeAffineOpenCase`, `BaseChangeMayerVietorisStep` and the reduction to an
affine base.  So the chartwise statement cannot discharge `hbase`, and the carried global form is
what is used.

*The orientation of the square.*  In the Künneth square `q ≫ b = p ≫ a` the arrow playing the
base-change morphism `g` of Tag 08HY is `a` and the one playing `f` is `b`; the complex that
travels is `M`, on `Y`.  So Tag 08IB is applied with `f := b`, `g := a`, `f' := p`, `g' := q`, and
what it asks of the square is `QuasiCompact b`, `QuasiSeparated b`, `TorIndependent b a` and
`M ∈ D_QCoh(𝒪_Y)` — all four of them hypotheses of Tag 0FLQ, the third after the symmetry of Tor
independence.  The cartesian square in that orientation is `(IsPullback.of_hasPullback a b).flip`.

*The two orders of the projection formula.*  `hproj₁` is
`Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap` at `a`, which is
`CategoryTheory.adjunctionTensorMap`: the map `Ra_*K ⊗ N ⟶ Ra_*(K ⊗ La^*N)`,
exactly the shape of Tag 08EU.  `hproj₂` is
`Stacks.Cohomology.DerivedKunneth.adjunctionTensorMapRight` at `p`: the map
`K ⊗_X Rp_*G ⟶ Rp_*(Lp^*K ⊗_W G)` at `G = Lq^*M`, which is Tag 08EU with the two tensor factors
interchanged — the order in which the chain of
`isIso_kunnethMap_of_projectionFormulas_of_baseChange` composes without a braiding.  Tag 08EU in
the standard order at `p` gives instead `Rp_*(Lq^*M) ⊗_X K ⟶ Rp_*(Lq^*M ⊗_W Lp^*K)`, which is
`isIso_projectionFormulaMap_pullbackFst_of_projectionFormula` below.
`adjunctionTensorMapRight_braiding` identifies the two: they are conjugate under the
commutativity constraints of Tag 0FPB on `D(𝒪_X)` and on `D(𝒪_W)`, which are available as
`Stacks.Cohomology.DerivedRelativeCupProduct.derivedBraiding`, *provided* the monoidality
comparison of Tag 079U for `p` is compatible with them, i.e. that derived pullback is a braided
monoidal functor for that comparison.  That last is
`Stacks.Cohomology.DerivedRelativeCupProduct.PullbackTensorComparisonBraided`, and it is proved
by `Stacks.Cohomology.DerivedRelativeCupProduct.pullbackTensorComparisonBraided` in
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/RelativeCupProductCommutativity.lean`.
So `hproj₂` reduces to Tag 08EU, and no further.

*Why no tag is registered.*  Every statement below carries a hypothesis beyond those of
Tag 0FLQ — the carried Tag 08EU and the carried Tag 08IB, and in the two statements that keep it
`hproj₂` — so none of them proves the tag.  The two
conditional registrations of Tag 0FLQ in
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/KunnethIsomorphism.lean` are left
untouched.

*Symmetry of Tor independence.*  This is `AlgebraicGeometry.TorIndependent.symm` of
`StacksFrontier/AlgebraicGeometry/Perfect/TorIndependence.lean`, beside the affine criterion of
Tag 0FXV that proves it.

## References

* [Stacks Project, Tag 0FLQ](https://stacks.math.columbia.edu/tag/0FLQ)
* [Stacks Project, Tag 0FLP](https://stacks.math.columbia.edu/tag/0FLP)
* [Stacks Project, Tag 0G7V](https://stacks.math.columbia.edu/tag/0G7V)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 0FXV](https://stacks.math.columbia.edu/tag/0FXV)
* [Stacks Project, Tag 00M3](https://stacks.math.columbia.edu/tag/00M3)
* [Stacks Project, Tag 0FPB](https://stacks.math.columbia.edu/tag/0FPB)
* [Stacks Project, Tag 0FP5](https://stacks.math.columbia.edu/tag/0FP5)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite
open Stacks.Cohomology.DerivedProjectionFormula
open Stacks.Cohomology.DerivedBaseChange
open Stacks.Cohomology.DerivedRelativeCupProduct
open Stacks.SheafOfModules.DerivedMonoidal
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.DerivedKunneth

attribute [local instance 100000] HasDerivedCategory.standard

-- The pullback/pushforward development and the tensor-product development name the structure
-- sheaf of a ringed space differently, by `structureSheafRing` and by
-- `Stacks.SheafOfModules.Tensor.ringSheaf`; the symmetry of the derived tensor product is
-- stated at the second spelling and consumed here at the first, exactly as in
-- `StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/
-- StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/RelativeCupProductCommutativity.lean`.
attribute [local implicit_reducible] structureSheafRing

/-! ### Quasi-coherence of a derived direct image, Tag 08D5 part (1) -/

/-- **Tag 08D5 part (1)** in the spelling the carried Tag 08EU consumes: along a quasi-compact
quasi-separated morphism of schemes the derived direct image of a complex with quasi-coherent
cohomology again has quasi-coherent cohomology.  This is
`AlgebraicGeometry.isQuasicoherent_derivedPushforward_affineLocal`, read at the object
`⟨A, hA⟩` of `D_QCoh(𝒪_V)`. -/
lemma isQCohAll_derivedPushforward {V W : Scheme.{u}} (p : V ⟶ W) [QuasiCompact p]
    [QuasiSeparated p] {A : DerivedCategory V.Modules} (hA : IsQCohAll A) :
    IsQCohAll ((derivedPushforward p.toLRSHom.toShHom).obj A) :=
  fun j => isQuasicoherent_derivedPushforward_affineLocal p ⟨A, hA⟩ j

/-! ### The two orders of the projection formula, and what separates them -/

section Braiding

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (A : C × C ⥤ C) (B : D × D ⥤ D) (α : A ⋙ L ⟶ L.prod L ⋙ B)
  (sA : ∀ M N : C, A.obj (M, N) ⟶ A.obj (N, M))
  (sB : ∀ G G' : D, B.obj (G, G') ⟶ B.obj (G', G))

/-- **The two orders of the projection-formula map differ by the two symmetries.**  For an
adjunction `L ⊣ R`, bifunctors `A` on the source and `B` on the target and a monoidality
comparison `α`, if `sB` is natural and `α` carries `sA` to `sB`, then the opposite-order
projection-formula map `Stacks.Cohomology.DerivedKunneth.adjunctionTensorMapRight` is the
standard-order one `CategoryTheory.adjunctionTensorMap` conjugated by `sA` and `sB`.

Nothing about ringed spaces or derived categories enters, and no coherence axiom of the two
symmetries is used — only the naturality `hsB` and the compatibility `hα`.  This is the
`adjunctionTensorMap` analogue of
`Stacks.Cohomology.DerivedRelativeCupProduct.adjunctionBitensorMap_braiding`, with the same
proof: transpose both sides under the adjunction and the two hypotheses close the square. -/
theorem adjunctionTensorMapRight_braiding
    (hsB : ∀ {G G' H H' : D} (g : G ⟶ H) (g' : G' ⟶ H'),
      B.map (g ×ₘ g') ≫ sB H H' = sB G G' ≫ B.map (g' ×ₘ g))
    (hα : ∀ M N : C,
      L.map (sA M N) ≫ α.app (N, M) = α.app (M, N) ≫ sB (L.obj M) (L.obj N))
    (H : C) (G : D) :
    sA (R.obj G) H ≫ adjunctionTensorMapRight adj A B α H G =
      CategoryTheory.adjunctionTensorMap adj A B α G H ≫ R.map (sB G (L.obj H)) := by
  apply (adj.homEquiv _ _).symm.injective
  rw [adjunctionTensorMapRight, CategoryTheory.adjunctionTensorMap,
    Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_right_symm]
  simp only [Functor.comp_obj, Functor.prod_obj, Equiv.symm_apply_apply]
  rw [← Category.assoc, hα]
  simp only [Category.assoc]
  rw [hsB]

/-- **The interchanged order of the projection-formula map is invertible when the standard one
is**, the two symmetries being invertible.  `adjunctionTensorMapRight_braiding` makes the two
conjugate, and `CategoryTheory.IsIso.of_isIso_comp_left` cancels the symmetry on the left.

Stated here, at the abstract level, rather than at the geometric application: every morphism in
the equation is then a local variable, so the rewrite matches on the nose.  At the derived
functors of module sheaves the same rewrite performed on the geometric terms does not, the two
spellings of the symmetry differing in their instance arguments. -/
theorem isIso_adjunctionTensorMapRight_of_braiding
    (hsB : ∀ {G G' H H' : D} (g : G ⟶ H) (g' : G' ⟶ H'),
      B.map (g ×ₘ g') ≫ sB H H' = sB G G' ≫ B.map (g' ×ₘ g))
    (hα : ∀ M N : C,
      L.map (sA M N) ≫ α.app (N, M) = α.app (M, N) ≫ sB (L.obj M) (L.obj N))
    (H : C) (G : D) (hsAiso : IsIso (sA (R.obj G) H)) (hsBiso : IsIso (sB G (L.obj H)))
    (hstd : IsIso (CategoryTheory.adjunctionTensorMap adj A B α G H)) :
    IsIso (adjunctionTensorMapRight adj A B α H G) := by
  have := hsAiso
  have := hsBiso
  have := hstd
  have hcomp : IsIso (sA (R.obj G) H ≫ adjunctionTensorMapRight adj A B α H G) := by
    rw [adjunctionTensorMapRight_braiding adj A B α sA sB hsB hα H G]
    infer_instance
  exact IsIso.of_isIso_comp_left (sA (R.obj G) H) (adjunctionTensorMapRight adj A B α H G)

end Braiding

/-- **The symmetry of the derived tensor product is invertible**: it is the braiding of the
symmetric monoidal structure of Tag 0FPB on `D(𝒪_Z)`, read through
`Stacks.Cohomology.DerivedRelativeCupProduct.derivedBraiding_eq`. -/
theorem isIso_derivedBraiding (Z : RingedSpace.{u, u})
    [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (G G' : DerivedCategory (Stacks.SheafOfModules.DerivedMonoidal.Mod Z.sheaf)) :
    IsIso (derivedBraiding Z G G') :=
  let := canonicalDerivedMonoidal Z.sheaf
  let := canonicalDerivedSymmetric Z.sheaf
  (β_ G G').isIso_hom

/-! ### The three inputs of Tag 0FLQ at the fibre product of two schemes -/

section Schemes

variable {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-- **The base-change input of Tag 0FLQ, at the tag's own hypotheses.**  For `a : X ⟶ S` and
`b : Y ⟶ S` with `b` quasi-compact and quasi-separated and `X`, `Y` Tor independent over `S`, and
for `M ∈ D_QCoh(𝒪_Y)`, the base-change leg `La^*Rb_*M ⟶ Rp_*Lq^*M` of the cartesian square of
`W = X ×_S Y` is invertible.

This is the hypothesis `hbase` of
`Stacks.Cohomology.DerivedKunneth.isIso_kunnethMap_of_projectionFormulas_of_baseChange`, fully
discharged from the carried Tag 08IB.  The route is
`Stacks.Cohomology.DerivedKunneth.isIso_kunnethBaseChangeLeg_of_isIso_derivedBaseChangeMap`,
which identifies the leg with the derived base-change map of Tag 08HY, followed by `h08IB` for
the square in the orientation `f := b`, `g := a`, `f' := p`, `g' := q`;
`AlgebraicGeometry.TorIndependent.symm`
puts the Tor-independence hypothesis in that orientation. -/
theorem isIso_kunnethBaseChangeLeg_pullback_of_torIndependent
    (h08IB : DerivedBaseChangeIsIsoOnQuasicoherent.{u})
    [QuasiCompact b] [QuasiSeparated b] (hTor : TorIndependent a b)
    (M : DerivedCategory Y.Modules) (hM : IsQCohAll M) :
    IsIso (kunnethBaseChangeLeg a.toLRSHom.toShHom b.toLRSHom.toShHom
      (pullback.fst a b).toLRSHom.toShHom (pullback.snd a b).toLRSHom.toShHom
      (Stacks.Cohomology.GlobalKunneth.toShHom_pullback_condition a b) M) :=
  isIso_kunnethBaseChangeLeg_of_isIso_derivedBaseChangeMap a.toLRSHom.toShHom
    b.toLRSHom.toShHom (pullback.fst a b).toLRSHom.toShHom (pullback.snd a b).toLRSHom.toShHom
    (Stacks.Cohomology.GlobalKunneth.toShHom_pullback_condition a b) M
    (h08IB (pullback.snd a b) (pullback.fst a b) b a (IsPullback.of_hasPullback a b).flip
      inferInstance inferInstance (AlgebraicGeometry.TorIndependent.symm hTor)
      (Stacks.Cohomology.GlobalKunneth.toShHom_pullback_condition a b) M hM)

/-- **Tag 08EU at the first projection of `W = X ×_S Y`, in the standard order.**  The
projection-formula map

`Rp_*(Lq^*M) ⊗^𝐋_{𝒪_X} K ⟶ Rp_*(Lq^*M ⊗^𝐋_{𝒪_W} Lp^*K)`

is invertible for `K ∈ D_QCoh(𝒪_X)` and `M ∈ D_QCoh(𝒪_Y)`, granted the carried Tag 08EU.

Two of the hypotheses of Tag 08EU are discharged here rather than assumed: `p` is quasi-compact
and quasi-separated because it is the base change of `b` along `a`, which is where the tag's
hypotheses on `b` are consumed, and `Lq^*M` has quasi-coherent cohomology by Tag 08DW part (1),
`AlgebraicGeometry.isQCohAll_dpull`.

This is *not* the hypothesis `hproj₂` of
`Stacks.Cohomology.DerivedKunneth.isIso_kunnethMap_of_projectionFormulas_of_baseChange`, which is
the same projection formula with the two tensor factors interchanged; see the implementation
notes for what is missing between them. -/
theorem isIso_projectionFormulaMap_pullbackFst_of_projectionFormula
    (h08EU : ProjectionFormulaIsIsoOnQuasicoherent.{u})
    [QuasiCompact b] [QuasiSeparated b]
    (K : DerivedCategory X.Modules) (M : DerivedCategory Y.Modules)
    (hK : IsQCohAll K) (hM : IsQCohAll M) :
    IsIso (projectionFormulaMap (pullback.fst a b).toLRSHom.toShHom
      ((derivedPullback (pullback.snd a b).toLRSHom.toShHom).obj M) K) :=
  h08EU (pullback.fst a b) inferInstance inferInstance
    ((derivedPullback (pullback.snd a b).toLRSHom.toShHom).obj M) K
    (isQCohAll_dpull (pullback.snd a b) hM) hK

/-- **`hproj₂` from Tag 08EU at `p`.**  The interchanged-order projection formula

`K ⊗^𝐋_{𝒪_X} Rp_*(Lq^*M) ⟶ Rp_*(Lp^*K ⊗^𝐋_{𝒪_W} Lq^*M)`

is invertible, granted the carried Tag 08EU and nothing else.

By `adjunctionTensorMapRight_braiding` the two orders are conjugate under the commutativity
constraints of Tag 0FPB, and the constraints are invertible by `isIso_derivedBraiding`; the
standard order is `isIso_projectionFormulaMap_pullbackFst_of_projectionFormula`.

The compatibility of the monoidality comparison of Tag 079U for `p` with those constraints —
`Stacks.Cohomology.DerivedRelativeCupProduct.PullbackTensorComparisonBraided`, the exact and
only gap between `hproj₂` and Tag 08EU — is supplied by
`Stacks.Cohomology.DerivedRelativeCupProduct.pullbackTensorComparisonBraided`, so it is no
longer a hypothesis of this statement. -/
theorem isIso_adjunctionTensorMapRight_pullbackFst_of_braided
    (h08EU : ProjectionFormulaIsIsoOnQuasicoherent.{u})
    [QuasiCompact b] [QuasiSeparated b]
    (K : DerivedCategory X.Modules) (M : DerivedCategory Y.Modules)
    (hK : IsQCohAll K) (hM : IsQCohAll M) :
    IsIso (adjunctionTensorMapRight
      (derivedAdjunction (pullback.fst a b).toLRSHom.toShHom)
      (Functor.uncurry.obj (derivedTensorProductFunctor X.toRingedSpace.sheaf))
      (Functor.uncurry.obj (derivedTensorProductFunctor (pullback a b).toRingedSpace.sheaf))
      (pullbackTensorComparison (pullback.fst a b).toLRSHom.toShHom) K
      ((derivedPullback (pullback.snd a b).toLRSHom.toShHom).obj M)) :=
  isIso_adjunctionTensorMapRight_of_braiding
    (derivedAdjunction (pullback.fst a b).toLRSHom.toShHom)
    (Functor.uncurry.obj (derivedTensorProductFunctor X.toRingedSpace.sheaf))
    (Functor.uncurry.obj (derivedTensorProductFunctor (pullback a b).toRingedSpace.sheaf))
    (pullbackTensorComparison (pullback.fst a b).toLRSHom.toShHom)
    (derivedBraiding X.toRingedSpace) (derivedBraiding (pullback a b).toRingedSpace)
    (fun g g' => derivedBraiding_naturality (pullback a b).toRingedSpace g g')
    (pullbackTensorComparisonBraided (pullback.fst a b).toLRSHom.toShHom) K
    ((derivedPullback (pullback.snd a b).toLRSHom.toShHom).obj M)
    (isIso_derivedBraiding X.toRingedSpace _ _)
    (isIso_derivedBraiding (pullback a b).toRingedSpace _ _)
    (isIso_projectionFormulaMap_pullbackFst_of_projectionFormula a b h08EU K M hK hM)

/-- **The first conclusion of Tag 0FLQ at the fibre product of two schemes, reduced to its two
cited inputs.**

Let `a : X ⟶ S` and `b : Y ⟶ S` be quasi-compact and quasi-separated morphisms of schemes with
`X` and `Y` Tor independent over `S`, let `W = X ×_S Y` with projections `p = pullback.fst a b`
and `q = pullback.snd a b`, and let `K ∈ D_QCoh(𝒪_X)`, `M ∈ D_QCoh(𝒪_Y)`.  Then the relative
Künneth morphism of Tag 0FLP at `f = p ≫ a`,

`Ra_*K ⊗^𝐋_{𝒪_S} Rb_*M ⟶ Rf_*(Lp^*K ⊗^𝐋_{𝒪_W} Lq^*M)`,

is an isomorphism, granted Tag 08EU (`h08EU`), Tag 08IB (`h08IB`) and the interchanged-order
projection formula at `p` (`hproj₂`).

The square here *is* cartesian and the hypotheses are the tag's own, which is what makes the
three inputs of
`Stacks.Cohomology.DerivedKunneth.isIso_kunnethMap_of_projectionFormulas_of_baseChange`
dischargeable at all.  Two of them are discharged: `hproj₁` by `h08EU` at `a`, whose own
quasi-coherence hypothesis on `Rb_*M` is Tag 08D5 part (1), and `hbase` by
`isIso_kunnethBaseChangeLeg_pullback_of_torIndependent`.  The third, `hproj₂`, is passed through
unchanged.

No `@[stacks 0FLQ]` attribute is carried: `h08EU`, `h08IB` and `hproj₂` are hypotheses that
Tag 0FLQ does not have. -/
theorem isIso_kunnethMap_pullback_of_torIndependent
    (h08EU : ProjectionFormulaIsIsoOnQuasicoherent.{u})
    (h08IB : DerivedBaseChangeIsIsoOnQuasicoherent.{u})
    [QuasiCompact a] [QuasiSeparated a] [QuasiCompact b] [QuasiSeparated b]
    (hTor : TorIndependent a b)
    (K : DerivedCategory X.Modules) (M : DerivedCategory Y.Modules)
    (hK : IsQCohAll K) (hM : IsQCohAll M)
    (hproj₂ : IsIso (adjunctionTensorMapRight
      (derivedAdjunction (pullback.fst a b).toLRSHom.toShHom)
      (Functor.uncurry.obj (derivedTensorProductFunctor X.toRingedSpace.sheaf))
      (Functor.uncurry.obj (derivedTensorProductFunctor (pullback a b).toRingedSpace.sheaf))
      (pullbackTensorComparison (pullback.fst a b).toLRSHom.toShHom) K
      ((derivedPullback (pullback.snd a b).toLRSHom.toShHom).obj M))) :
    IsIso (kunnethMap a.toLRSHom.toShHom b.toLRSHom.toShHom
      (pullback.fst a b).toLRSHom.toShHom (pullback.snd a b).toLRSHom.toShHom
      (pullback.fst a b ≫ a).toLRSHom.toShHom rfl
      (Stacks.Cohomology.GlobalKunneth.toShHom_pullback_condition a b) K M) :=
  isIso_kunnethMap_of_projectionFormulas_of_baseChange a.toLRSHom.toShHom b.toLRSHom.toShHom
    (pullback.fst a b).toLRSHom.toShHom (pullback.snd a b).toLRSHom.toShHom
    (Stacks.Cohomology.GlobalKunneth.toShHom_pullback_condition a b) K M
    (pullbackTensorComparisonComp a.toLRSHom.toShHom (pullback.fst a b).toLRSHom.toShHom
      ((derivedPushforward a.toLRSHom.toShHom).obj K)
      ((derivedPushforward b.toLRSHom.toShHom).obj M))
    (h08EU a inferInstance inferInstance K
      ((derivedPushforward b.toLRSHom.toShHom).obj M) hK (isQCohAll_derivedPushforward b hM))
    (isIso_kunnethBaseChangeLeg_pullback_of_torIndependent a b h08IB hTor M hM)
    hproj₂

/-- **The second conclusion of Tag 0FLQ, over an affine base, reduced to the same inputs.**  With
`S = Spec A` affine and the hypotheses of `isIso_kunnethMap_pullback_of_torIndependent`, the
global Künneth morphism of Tag 0G7V

`RΓ(X, K) ⊗^𝐋_A RΓ(Y, M) ⟶ RΓ(X ×_S Y, Lp^*K ⊗^𝐋_{𝒪_W} Lq^*M)`

is an isomorphism, granted in addition the invertibility `hκ` of the carried global cup product
of the base at `(Ra_*K, Rb_*M)`.

`hκ` cannot be dropped and affineness of `S` cannot replace it:
`Stacks.Cohomology.GlobalKunneth.GlobalCupProduct` is a bare morphism of bifunctors with no laws,
so the zero morphism inhabits it and for that choice the conclusion is false.  This is the
situation recorded in the implementation notes of
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/KunnethIsomorphismOfSheaves.lean`;
`[IsAffine S]` is therefore stated, as the tag has it, but not consumed.

No `@[stacks 0FLQ]` attribute is carried, for the same reason as above and for `hκ` besides. -/
theorem isIso_kunnethGlobalMapScheme_of_torIndependent
    (h08EU : ProjectionFormulaIsIsoOnQuasicoherent.{u})
    (h08IB : DerivedBaseChangeIsIsoOnQuasicoherent.{u})
    [IsAffine S] [QuasiCompact a] [QuasiSeparated a] [QuasiCompact b] [QuasiSeparated b]
    (hTor : TorIndependent a b)
    (κ : Stacks.Cohomology.GlobalKunneth.GlobalCupProduct S.toRingedSpace)
    (K : DerivedCategory X.Modules) (M : DerivedCategory Y.Modules)
    (hK : IsQCohAll K) (hM : IsQCohAll M)
    (hκ : IsIso (κ.app ((derivedPushforward a.toLRSHom.toShHom).obj K,
      (derivedPushforward b.toLRSHom.toShHom).obj M)))
    (hproj₂ : IsIso (adjunctionTensorMapRight
      (derivedAdjunction (pullback.fst a b).toLRSHom.toShHom)
      (Functor.uncurry.obj (derivedTensorProductFunctor X.toRingedSpace.sheaf))
      (Functor.uncurry.obj (derivedTensorProductFunctor (pullback a b).toRingedSpace.sheaf))
      (pullbackTensorComparison (pullback.fst a b).toLRSHom.toShHom) K
      ((derivedPullback (pullback.snd a b).toLRSHom.toShHom).obj M))) :
    IsIso (Stacks.Cohomology.GlobalKunneth.kunnethGlobalMapScheme a b κ K M) :=
  Stacks.Cohomology.GlobalKunneth.isIso_kunnethGlobalMap a.toLRSHom.toShHom b.toLRSHom.toShHom
    (pullback.fst a b).toLRSHom.toShHom (pullback.snd a b).toLRSHom.toShHom
    (pullback.fst a b ≫ a).toLRSHom.toShHom rfl
    (Stacks.Cohomology.GlobalKunneth.toShHom_pullback_condition a b) κ K M hκ
    (isIso_kunnethMap_pullback_of_torIndependent a b h08EU h08IB hTor K M hK hM hproj₂)

/-- **Tag 0FLQ at the fibre product of two schemes, reduced to the two tags the source
cites.**  The same conclusion as `isIso_kunnethMap_pullback_of_torIndependent`, with `hproj₂`
discharged: the hypotheses beyond the tag's own are now exactly

* `h08EU`, Tag 08EU — `AlgebraicGeometry.ProjectionFormulaIsIsoOnQuasicoherent`;
* `h08IB`, Tag 08IB — `AlgebraicGeometry.DerivedBaseChangeIsIsoOnQuasicoherent`.

Both are inputs the source cites.  A third input — the
compatibility of the monoidality comparison of Tag 079U for `p` with the commutativity
constraints of Tag 0FPB, which arises from the shape in which the chain of
`isIso_kunnethMap_of_projectionFormulas_of_baseChange` composes — is proved, by
`Stacks.Cohomology.DerivedRelativeCupProduct.pullbackTensorComparisonBraided`, and is supplied
rather than assumed.  Substituting an unconditional proof of either remaining tag is a single
edit.

No `@[stacks 0FLQ]` attribute is carried: both are hypotheses Tag 0FLQ does not have. -/
theorem isIso_kunnethMap_pullback_of_torIndependent_of_braided
    (h08EU : ProjectionFormulaIsIsoOnQuasicoherent.{u})
    (h08IB : DerivedBaseChangeIsIsoOnQuasicoherent.{u})
    [QuasiCompact a] [QuasiSeparated a] [QuasiCompact b] [QuasiSeparated b]
    (hTor : TorIndependent a b)
    (K : DerivedCategory X.Modules) (M : DerivedCategory Y.Modules)
    (hK : IsQCohAll K) (hM : IsQCohAll M) :
    IsIso (kunnethMap a.toLRSHom.toShHom b.toLRSHom.toShHom
      (pullback.fst a b).toLRSHom.toShHom (pullback.snd a b).toLRSHom.toShHom
      (pullback.fst a b ≫ a).toLRSHom.toShHom rfl
      (Stacks.Cohomology.GlobalKunneth.toShHom_pullback_condition a b) K M) :=
  isIso_kunnethMap_pullback_of_torIndependent a b h08EU h08IB hTor K M hK hM
    (isIso_adjunctionTensorMapRight_pullbackFst_of_braided a b h08EU K M hK hM)

/-- **The second conclusion of Tag 0FLQ over an affine base, reduced to the two tags the source
cites.**  `isIso_kunnethGlobalMapScheme_of_torIndependent` with `hproj₂` discharged through the
proved braiding compatibility; `hκ` stays, for the reason recorded there. -/
theorem isIso_kunnethGlobalMapScheme_of_torIndependent_of_braided
    (h08EU : ProjectionFormulaIsIsoOnQuasicoherent.{u})
    (h08IB : DerivedBaseChangeIsIsoOnQuasicoherent.{u})
    [IsAffine S] [QuasiCompact a] [QuasiSeparated a] [QuasiCompact b] [QuasiSeparated b]
    (hTor : TorIndependent a b)
    (κ : Stacks.Cohomology.GlobalKunneth.GlobalCupProduct S.toRingedSpace)
    (K : DerivedCategory X.Modules) (M : DerivedCategory Y.Modules)
    (hK : IsQCohAll K) (hM : IsQCohAll M)
    (hκ : IsIso (κ.app ((derivedPushforward a.toLRSHom.toShHom).obj K,
      (derivedPushforward b.toLRSHom.toShHom).obj M))) :
    IsIso (Stacks.Cohomology.GlobalKunneth.kunnethGlobalMapScheme a b κ K M) :=
  isIso_kunnethGlobalMapScheme_of_torIndependent a b h08EU h08IB hTor κ K M hK hM hκ
    (isIso_adjunctionTensorMapRight_pullbackFst_of_braided a b h08EU K M hK hM)

/-- **The first conclusion of Tag 0FLQ, resting on Tag 08IB alone.**
`isIso_kunnethMap_pullback_of_torIndependent_of_braided` with `h08EU` discharged against the
proved Tag 08EU: `AlgebraicGeometry.projectionFormulaIsIsoOnQuasicoherent` of
`StacksFrontier/AlgebraicGeometry/DerivedVarieties/FourierMukai/ProjectionFormulaDischarged.lean`,
which proves the carried proposition outright from
`Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_quasiCoherent`
(registered bare on Tag 08EU).

Of the three comparisons the source's proof chains together, two are now proved outright in this
library and one remains carried: `hproj₁` and `hproj₂` both come from Tag 08EU, and the
interchanged-order conjugation they need is the proved braiding compatibility; `hbase` is Tag
08IB, which this development states but does not prove.

Still no `@[stacks 0FLQ]` attribute: `h08IB` is a hypothesis Tag 0FLQ does not have. -/
theorem isIso_kunnethMap_pullback_of_torIndependent_of_baseChange
    (h08IB : DerivedBaseChangeIsIsoOnQuasicoherent.{u})
    [QuasiCompact a] [QuasiSeparated a] [QuasiCompact b] [QuasiSeparated b]
    (hTor : TorIndependent a b)
    (K : DerivedCategory X.Modules) (M : DerivedCategory Y.Modules)
    (hK : IsQCohAll K) (hM : IsQCohAll M) :
    IsIso (kunnethMap a.toLRSHom.toShHom b.toLRSHom.toShHom
      (pullback.fst a b).toLRSHom.toShHom (pullback.snd a b).toLRSHom.toShHom
      (pullback.fst a b ≫ a).toLRSHom.toShHom rfl
      (Stacks.Cohomology.GlobalKunneth.toShHom_pullback_condition a b) K M) :=
  isIso_kunnethMap_pullback_of_torIndependent_of_braided a b
    AlgebraicGeometry.projectionFormulaIsIsoOnQuasicoherent h08IB hTor K M hK hM

/-- **The second conclusion of Tag 0FLQ over an affine base, resting on Tag 08IB and `hκ`.**
`isIso_kunnethGlobalMapScheme_of_torIndependent_of_braided` with `h08EU` discharged the same way.
`hκ` stays, for the reason recorded at that statement. -/
theorem isIso_kunnethGlobalMapScheme_of_torIndependent_of_baseChange
    (h08IB : DerivedBaseChangeIsIsoOnQuasicoherent.{u})
    [IsAffine S] [QuasiCompact a] [QuasiSeparated a] [QuasiCompact b] [QuasiSeparated b]
    (hTor : TorIndependent a b)
    (κ : Stacks.Cohomology.GlobalKunneth.GlobalCupProduct S.toRingedSpace)
    (K : DerivedCategory X.Modules) (M : DerivedCategory Y.Modules)
    (hK : IsQCohAll K) (hM : IsQCohAll M)
    (hκ : IsIso (κ.app ((derivedPushforward a.toLRSHom.toShHom).obj K,
      (derivedPushforward b.toLRSHom.toShHom).obj M))) :
    IsIso (Stacks.Cohomology.GlobalKunneth.kunnethGlobalMapScheme a b κ K M) :=
  isIso_kunnethGlobalMapScheme_of_torIndependent_of_braided a b
    AlgebraicGeometry.projectionFormulaIsIsoOnQuasicoherent h08IB hTor κ K M hK hM hκ

end Schemes

end Stacks.Cohomology.DerivedKunneth

end
