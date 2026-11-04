module

public import StacksFrontier.Deformation.Artin.Obstruction.DualNotion
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityTag

/-!
# Openness of versality for a dual deformation situation, at a charted object

A dual deformation situation records its data in raw variables: a ring `Λ`, a ring `A` of
finite type over it, the structure morphism `Spec A ⟶ S` and its factorization through the
affine open `Spec Λ ⊆ S`, and the object `x` with the witness that it lies over `Spec A`.
[Stacks, Tag 07YN] is stated at a `Deformation.Artin.ChartedObject`, which bundles exactly
the same data. This file is the bridge: it reads a dual deformation situation as a charted
object, turns the two assumptions of
`Deformation.Artin.DualNotion.OpennessInput` into a
`Deformation.Artin.NaiveObstructionAt`, and so discharges openness of versality for a dual
deformation situation against [Stacks, Tag 07YN].

## Main definitions

* `Deformation.Artin.DualNotion.chart` — the affine chart `Spec Λ ⊆ S` of a dual deformation
  situation.
* `Deformation.Artin.DualNotion.chartedObject` — the dual deformation situation read as a
  charted object for that chart.

## Main results

* `Deformation.Artin.DualNotion.naiveObstructionAt` — the assumptions (i) and (ii) of
  [Stacks, Tag 07YN] carried by a `Deformation.Artin.DualNotion.OpennessInput`, read at the
  charted object.
* `Deformation.Artin.DualNotion.exists_isOpen_isVersalAt_of_opennessInput` — openness of
  versality for a dual deformation situation admitting an `OpennessInput` at a bounded-above
  object with finite cohomology: this is [Stacks, Tag 07YN] applied, and it supplies what the
  statement of [Stacks, Tag 07YZ] would otherwise carry as a hypothesis.

## Implementation notes

The chart dictionary is definitional throughout: the site algebra of the charted object is
built from `A`, the membership `hA` and the structure morphism `toS`, so its spectrum as an
object over `S` in the site is `Deformation.Artin.algebraOver` on the nose and its structure
morphism as a morphism of schemes is `toS` on the nose. The only field needing an argument is
`Deformation.Artin.MapsIntoAffineOpen`, the side condition of
`Deformation.Artin.AffineObject`: the affine open is the open range of the open immersion
`Spec Λ ⟶ S`, which contains the image of `Spec A ⟶ S` because the structure morphism
factors through it.

The lifting criterion is the one field whose two presentations genuinely differ:
`Deformation.Artin.DualNotion.OpennessInput` phrases it on a
`Deformation.Artin.SquareZeroThickening` and
`Deformation.Artin.NaiveObstructionAt` on a `Deformation.Artin.DeformationSituation`. The two
carry the same data, and `Deformation.Artin.hasLift_iff_nonempty_underFiber` compares the two
descriptions of the category of lifts.

## References

* [Stacks Project, Tag 07YN](https://stacks.math.columbia.edu/tag/07YN)
* [Stacks Project, Tag 07YX](https://stacks.math.columbia.edu/tag/07YX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Deformation.Artin.DualNotion

universe u v w

attribute [local instance 10000] HasDerivedCategory.standard

variable (Λ A : Type u) [CommRing Λ] [CommRing A] [Algebra Λ A]
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) [IsLocallyNoetherian S]
variable (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
variable (X : Type v) [Category.{w} X] (p : X ⥤ BigFppfOver B S hS)
variable (sit : DualDeformationSituation A Λ B S hS toS hA X p)

/-- The affine chart `Spec Λ ⊆ S` of a dual deformation situation. -/
public def chart : AffineChart S where
  ring := Λ
  immersion := sit.affineOpen
  isOpenImmersion := sit.openImmersion

/-- The site algebra `A` of a dual deformation situation: the ring `A`, its membership in the
site and the structure morphism `Spec A ⟶ S`. -/
public def siteAlgebra : SiteAlgebra B S hS where
  carrier := A
  mem := hA
  toBase := ObjectProperty.homMk toS

omit [IsLocallyNoetherian S] in
/-- The structure morphism of the site algebra of a dual deformation situation is `toS`. -/
public theorem toScheme_siteAlgebra :
    (siteAlgebra A B S hS toS hA).toScheme = toS :=
  rfl

omit [IsLocallyNoetherian S] in
/-- `Spec A` as an object over `S` in the site, read from the site algebra of a dual
deformation situation, is `Deformation.Artin.algebraOver`. -/
public theorem over_siteAlgebra :
    (siteAlgebra A B S hS toS hA).over = algebraOver A B S hS toS hA :=
  rfl

include sit in
/-- The structure morphism of `Spec A` maps into an affine open of `S`, namely the open range
of the open immersion `Spec Λ ⟶ S` through which it factors. -/
public theorem mapsIntoAffineOpen_of_dualDeformationSituation :
    MapsIntoAffineOpen S (siteAlgebra A B S hS toS hA).toScheme := by
  have := sit.openImmersion
  refine ⟨sit.affineOpen.opensRange, isAffineOpen_opensRange sit.affineOpen, fun y => ?_⟩
  change toS.base y ∈ Set.range sit.affineOpen.base
  refine ⟨(Spec.map (CommRingCat.ofHom (algebraMap Λ A))).base y, ?_⟩
  exact congrArg (fun f : Spec (CommRingCat.of A) ⟶ S => f.base y) sit.factorization

/-- The object of the fibred category of a dual deformation situation, read as an object over
the site algebra `A` in the sense of clause (1) of [Stacks, Tag 07YP]. -/
public def affineObject : AffineObject B S hS p where
  alg := siteAlgebra A B S hS toS hA
  mapsIntoAffineOpen :=
    mapsIntoAffineOpen_of_dualDeformationSituation Λ A B S hS toS hA X p sit
  obj := ⟨sit.x, sit.hx⟩

/-- **A dual deformation situation is a charted object.** The data of
`Deformation.Artin.DualDeformationSituation` contains that of a
`Deformation.Artin.ChartedObject` for the chart `Spec Λ ⊆ S`: the ring `A` of finite type over
`Λ`, the object `x` over `Spec A`, and the factorization of `Spec A ⟶ S` through the chart. -/
public def chartedObject : ChartedObject B S hS p (chart Λ A B S hS toS hA X p sit) where
  obj := affineObject Λ A B S hS toS hA X p sit
  algebra := inferInstanceAs (Algebra Λ A)
  factorization := sit.factorization

/-- The ring of the charted object of a dual deformation situation is `A`. -/
public theorem ring_chartedObject :
    (chartedObject Λ A B S hS toS hA X p sit).ring = A :=
  rfl

/-- The object of the charted object of a dual deformation situation is `x`. -/
public theorem point_chartedObject :
    (chartedObject Λ A B S hS toS hA X p sit).point = sit.x :=
  rfl

variable (hΩ : B.Contains (Spec (squareZeroRing A (differentialsModule Λ A))))
variable (E : DerivedCategory (ModuleCat.{u} A)) (ξ : E ⟶ derivedNaiveCotangentComplex Λ A)

/-- **The assumptions of [Stacks, Tag 07YN] from those of the dual notion.** The two
assumptions (i) and (ii) collected in `Deformation.Artin.DualNotion.OpennessInput` are
assumptions (1) and (2) of [Stacks, Tag 07YN] at the charted object of the dual deformation
situation.

Only the lifting criterion needs an argument: it is phrased on a
`Deformation.Artin.SquareZeroThickening` in the first presentation and on a
`Deformation.Artin.DeformationSituation` in the second. The two structures carry the same
data, and the two descriptions of the category of lifts are compared by
`Deformation.Artin.hasLift_iff_nonempty_underFiber`. -/
public def naiveObstructionAt (input : OpennessInput Λ A B S hS toS hA X p sit hΩ E ξ) :
    NaiveObstructionAt sit.fibered sit.rsStar (chartedObject Λ A B S hS toS hA X p sit) hΩ
      E ξ where
  hasLift_iff_xi_comp_eq_zero := by
    intro t instTop instChart instTower hmap hchart
    let : Algebra t.top.carrier A := instTop
    let : Algebra Λ t.top.carrier := instChart
    let : IsScalarTower Λ t.top.carrier A := instTower
    refine (hasLift_iff_nonempty_underFiber sit.fibered
      (affineObject Λ A B S hS toS hA X p sit) t).trans ?_
    exact input.hasLift_iff_xi_comp_eq_zero t.top.carrier
      { q := t.hom.ringMap
        squareZeroSurjection := ⟨t.surjective, t.sq_eq_bot⟩
        hA' := t.top.mem
        toS' := t.top.toBase
        arrow := t.hom.specMap
        arrow_spec := t.hom.specMap_spec } hmap hchart
  tangentMap := input.tangentMap
  tangentMap_add := input.tangentMap_add
  tangentMap_natural := input.tangentMap_natural
  tangentMap_bijective := input.tangentMap_bijective
  tangentMap_canonicalElement := input.tangentMap_canonicalElement

/-- **Openness of versality for a dual deformation situation, granted the dual input.** This
is [Stacks, Tag 07YN] applied at the charted object of the dual deformation situation: given
a bounded-above object `E` of `D(A)` with finite cohomology modules and a morphism
`ξ : E ⟶ NL_{A/Λ}` satisfying the two assumptions of
`Deformation.Artin.DualNotion.OpennessInput`, versality of `x` at a closed point `u₀` spreads
to all finite type points of an open neighbourhood of `u₀`. -/
public theorem exists_isOpen_isVersalAt_of_opennessInput
    (hE : (DerivedCategory.TStructure.t (C := ModuleCat.{u} A)).minus E)
    (input : OpennessInput Λ A B S hS toS hA X p sit hΩ E ξ)
    (hFinite : ∀ n : ℤ,
      Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj E))
    (u₀ : Spec (.of A)) (hu₀ : IsClosed ({u₀} : Set (Spec (.of A))))
    (hversal : IsVersalAt (Over.mk toS) (p ⋙ Over.post B.inclusion) u₀ sit.x
      (versalityBase Λ A B S hS toS hA X p sit)) :
    ∃ V : Set (Spec (.of A)), IsOpen V ∧ u₀ ∈ V ∧
      ∀ u ∈ V, IsFiniteTypePoint u →
        IsVersalAt (Over.mk toS) (p ⋙ Over.post B.inclusion) u sit.x
          (versalityBase Λ A B S hS toS hA X p sit) := by
  have : Algebra.FiniteType (chart Λ A B S hS toS hA X p sit).ring
      (chartedObject Λ A B S hS toS hA X p sit).ring := sit.finiteType
  exact isOpenVersalityAt_of_naiveObstructionAt sit.fibered sit.rsStar
    (chartedObject Λ A B S hS toS hA X p sit) hΩ E hE ξ
    (naiveObstructionAt Λ A B S hS toS hA X p sit hΩ E ξ input) hFinite u₀ hu₀ hversal

end Deformation.Artin.DualNotion

end
