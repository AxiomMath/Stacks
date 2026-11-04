module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.UnramifiedLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.Unramified
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSource.SourceLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleFppfSourceLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.EtaleCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.Unramified

/-!
# Source locality for the étale topology transferred from schemes to algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`, and let `P` be a property of morphisms of
schemes which is étale local on the source and target (**Stacks 04QZ**). **Stacks 03MJ** turns
`P` into the property `AlgebraicGeometry.Space.HoldsOnEveryEtaleChart B S hS P` of morphisms of
algebraic spaces over `S`. **Stacks 06ER** says that if `P` is local on the source for one of
the five topologies of **Stacks 03YH** then so is the associated property of morphisms of
algebraic spaces. This module proves the **étale case**, and reads off from it that
unramifiedness of morphisms of algebraic spaces is étale local on the source
(**Stacks 06F6**).

The argument is the one
`AlgebraicGeometry.Space.isLocalAtSource_fpqc_of_schemes` runs for the fpqc topology. Given
`f : X ⟶ Y` and an étale covering `{Zᵢ ⟶ X}`, choose a surjective étale scheme atlas `V ⟶ Y`,
lift it to a surjective étale chart `T₀ ⟶ X` over a morphism `α : T₀ ⟶ V` of the site
(**Stacks 02X1**), base-change the covering along `T₀ ⟶ X` (**Stacks 041F**, base change),
choose a surjective étale scheme atlas `Wᵢ ⟶ Zᵢ ×_X T₀` of each member, and compose
(**Stacks 041F**, composition). The resulting family `{Wᵢ ⟶ T₀}` consists of morphisms of the
*site*, and an étale covering of algebraic spaces whose members and target are representable is
an étale covering of schemes — that step is
`AlgebraicGeometry.Space.Topology.isCovering_yoneda`. With both sides of the equivalence now
expressed on schemes, source locality of `P` for the étale topology of schemes gives the two
implications, and **Stacks 03MJ** carries them back.

## Main results

* `AlgebraicGeometry.Space.isLocalAtSource_etale_of_schemes`: **Stacks 06ER**, the étale case.
* `AlgebraicGeometry.Space.unramified_isLocalAtSource_etale`: **Stacks 06F6**.

## Implementation notes

`isLocalAtSource_etale_of_schemes` is **deliberately not tagged** `@[stacks 06ER]`, for the
reason recorded in `StacksFrontier/AlgebraicGeometry/Spaces/FpqcSourceLocalityTransfer.lean`:
Stacks 06ER asserts the transfer for all five topologies `fpqc`, `fppf`, `syntomic`, `smooth`
and `étale` at once, and this theorem is the `étale` instance of it only. With the fpqc case
already in the tree and the fppf case in
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleFppfSourceLocalityTransfer.lean`, the two cases still
missing are `syntomic` and `smooth`, each of which needs the composition and base-change lemmas
for its own covering families; the étale ones used here are
`AlgebraicGeometry.Space.isEtaleCovering_comp` and
`AlgebraicGeometry.Space.isEtaleCovering_pullback` (**Stacks 041F**).

Stacks 06F6 itself is complete and is tagged: being unramified is étale local on the source and
target (**Stacks 04R3**,
`AlgebraicGeometry.unramified_isEtaleLocalOnSourceAndTarget`) and local on the source for the
étale topology of schemes (**Stacks 03YV**,
`AlgebraicGeometry.unramified_isLocalAtSource`), which are exactly the two hypotheses of the
transfer.

The base-change clause of Stacks 041F in the tree is stated for the *first* projection of the
presheaf fibre product, whereas the transfer consumes the base change of a covering family
along a chart of its target as a family of *second* projections; `isEtaleCovering_pullback_snd`
below is that orientation, proved from the cartesian square of **Stacks 02X2** and the joint
surjectivity criterion of **Stacks 03H4** rather than by transporting along the symmetry of the
fibre product.

## References

* [Stacks Project, Tag 041F](https://stacks.math.columbia.edu/tag/041F)
* [Stacks Project, Tag 06ER](https://stacks.math.columbia.edu/tag/06ER)
* [Stacks Project, Tag 06F6](https://stacks.math.columbia.edu/tag/06F6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Base change of an étale covering, as a family of second projections -/

/-- **Stacks 041F**, the base-change clause in the orientation the source-locality transfer
consumes: the second projections of the fibre products of an étale covering `{Zᵢ ⟶ X}` with a
morphism `f : X' ⟶ X` form an étale covering of `X'`.

Each member is the base change of `gi i` along `f` in the cartesian square of Stacks 02X2, hence
étale by Stacks 03FU, and joint surjectivity is Stacks 03H4: a point of `X'` and a point of some
`Zᵢ` over its image amalgamate to a point of the fibre product. -/
theorem isEtaleCovering_pullback_snd {I : Type v} {X X' : AlgebraicSpaces B S hS}
    (Zi : I → AlgebraicSpaces B S hS) (gi : ∀ i, Zi i ⟶ X) (f : X' ⟶ X)
    (hcover : IsEtaleCovering B S hS (fun i => (Zi i).1) (fun i => (gi i).hom)) :
    IsEtaleCovering B S hS (fun i => pullback (gi i).hom f.hom)
      (fun i => pullback.snd (gi i).hom f.hom) := by
  have hsq (i : I) : IsPullback
      (ObjectProperty.homMk (pullback.fst (gi i).hom f.hom) :
        AlgebraicSpaces.fiberProduct B S hS (gi i) f ⟶ Zi i)
      (ObjectProperty.homMk (pullback.snd (gi i).hom f.hom)) (gi i) f :=
    AlgebraicSpaces.isPullback_fiberProduct B S hS (gi i) f
  refine ⟨X'.property,
    fun i => isAlgebraicSpace_pullback B S hS (gi i).hom f.hom (Zi i).property X'.property
      X.property,
    fun i => isEtale_of_isPullback B S hS _ _ (gi i) f (hsq i) (hcover.etale i), ?_⟩
  refine Set.eq_univ_of_forall fun x' => ?_
  obtain ⟨i, z, hz⟩ := Set.mem_iUnion.mp (Set.eq_univ_iff_forall.mp hcover.jointly_surjective
    (pointsMap B S hS X'.1 f.hom x'))
  obtain ⟨w, -, hwq⟩ := exists_point_of_isPullback B S hS (hsq i) z x' hz
  exact Set.mem_iUnion.mpr ⟨i, Set.mem_range.mpr ⟨w, hwq⟩⟩

/-! ### Stacks 06ER, the étale case -/

/-- **Stacks 06ER**, the étale case. If a property `P` of morphisms of schemes is étale local on
the source and target and local on the source for the étale topology of schemes, then the
associated property of morphisms of algebraic spaces over `S` of Stacks 03MJ is local on the
source for the étale topology of algebraic spaces.

Deliberately untagged: Stacks 06ER asserts this for all five topologies of Stacks 03YH at once,
and only the étale case is proved here; the fpqc case is
`AlgebraicGeometry.Space.isLocalAtSource_fpqc_of_schemes`. -/
theorem isLocalAtSource_etale_of_schemes (P : MorphismProperty Scheme.{u})
    (hP : IsEtaleLocalOnSourceAndTarget P) [P.IsLocalAtSource Scheme.etalePrecoverage] :
    MorphismProperty.IsLocalAtSource
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) =>
        HoldsOnEveryEtaleChart B S hS P f.hom)
      (Topology.precoverage.{u, v} .etale B S hS) :=
  isLocalAtSource_etale_of_schemes' B S hS P hP

/-! ### Stacks 06F6 -/

/-- **Stacks 06F6.** Unramifiedness of a morphism of algebraic spaces over `S` is local on the
source for the étale topology of Stacks 03YH.

Unramifiedness of morphisms of schemes is étale local on the source and target
([Stacks Project, Tag 04R3]) and local on the source for the étale topology of schemes
([Stacks Project, Tag 03YV]), so this is the instance of
`AlgebraicGeometry.Space.isLocalAtSource_etale_of_schemes` at that property. -/
@[stacks 06F6]
instance unramified_isLocalAtSource_etale :
    MorphismProperty.IsLocalAtSource
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) => IsUnramified B S hS f.hom)
      (Topology.precoverage.{u, v} .etale B S hS) :=
  isLocalAtSource_etale_of_schemes B S hS
    (@_root_.AlgebraicGeometry.Unramified.{u} : MorphismProperty Scheme.{u})
    unramified_isEtaleLocalOnSourceAndTarget

end AlgebraicGeometry.Space

end
