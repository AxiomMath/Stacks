module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaClosedEmbeddingUnconditional
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TorAmplitudeStalkwise
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.DeducingFullyFaithfulness.ResidueFieldSkyscraper
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.DeducingFullyFaithfulness.DerivedTensorResidueFieldSkyscraper
import StacksCore.Tactic.StacksAttribute

/-!
# Vanishing of a kernel off the diagonal: the two halves of Case I of Stacks 0G0R

[Stacks, Tag 0G0R] proves that a relative equivalence which is the diagonal on the fibre over a
rational point `s` makes a smooth proper family constant near `s`.  Its proof runs over the
closed points `z` of the fibre `Y_s × Y_s` and splits into two cases.  **Case I** is the case
`z ∉ Δ(Y_s)`; there the source argues

* the derived tensor product `K ⊗^𝐋 i_*𝒪_z` vanishes, because it is
  `Li^*K ⊗^𝐋 𝒪_z = Δ_*𝒪_{Y_s} ⊗^𝐋 𝒪_z` and the two factors are supported on disjoint sets;
* therefore, by [Stacks, Tag 0G03], `K` vanishes on an open neighbourhood of `z`.

This file supplies the two ends of that argument, each in the generality in which it is a
statement about sheaves of modules rather than about the geometry of `0G0R`:

* the **disjoint-support vanishing** of a derived tensor product, which is the first bullet;
* the **stalk form of [Stacks, Tag 0G03]**, which is the second bullet with its hypothesis
  stated as vanishing of the cohomology stalks at the point rather than as orthogonality to the
  residue-field skyscraper.

The step joining them is here too, now that the derived-tensor forms of [Stacks, Tag 0G03] are
proved: see the implementation notes for what Case I still waits on, which is geometry rather
than homological algebra.  Nothing in this file carries a `stacks` attribute.

## Main results

* `Stacks.SheafOfModules.DerivedTensorStalk.isZero_derivedTensor_of_isZero_right`: the derived
  tensor product over a ring is additive, hence zero, in its *second* variable — the mirror of
  `Stacks.SheafOfModules.DerivedTensorStalk.isZero_derivedTensor_of_isZero_left`.
* `Stacks.SheafOfModules.DerivedTensorStalk.cohomologySupportedOn_derivedTensor_of_right`: the
  derived tensor product of an arbitrary complex with one whose cohomology is supported on `T`
  again has cohomology supported on `T` — the mirror of
  `Stacks.SheafOfModules.DerivedTensorStalk.cohomologySupportedOn_derivedTensor_of_left`.
* `Stacks.SheafOfModules.DerivedTensorStalk.cohomologySupportedOn_derivedTensor_inter`: the
  derived tensor product of a complex supported on `T₁` with one supported on `T₂` has its
  cohomology supported on `T₁ ∩ T₂`.
* `Stacks.SheafOfModules.DerivedTensorStalk.isZero_of_cohomologySupportedOn_empty`: a complex
  whose cohomology is supported on the empty set is a zero object.
* `Stacks.SheafOfModules.DerivedTensorStalk.isZero_derivedTensor_of_disjoint_support`:
  **the first half of Case I.**  Two complexes whose cohomological supports are disjoint have
  vanishing derived tensor product.
* `AlgebraicGeometry.exists_mem_forall_stalkHomology_isZero_of_stalkHomology_isZero`:
  **the second half of Case I.**  A bounded complex with coherent cohomology on a Noetherian
  scheme whose cohomology stalks all vanish at `x` has all its cohomology stalks vanishing on an
  open neighbourhood of `x`.
* `AlgebraicGeometry.exists_mem_forall_isZero_stalkHomology_of_isZero_derivedTensorSkyscraper`:
  **the two halves joined.**  A perfect complex on a Noetherian scheme whose derived tensor
  product with the residue-field skyscraper at `x` is a zero object vanishes on an open
  neighbourhood of `x`.  This is the shape in which the first half hands its conclusion to
  [Stacks, Tag 0G03].

## Implementation notes

*The first half.* `cohomologySupportedOn_derivedTensor_of_left` is proved in
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/ProjectionFormulaClosedEmbeddingUnconditional.lean` by computing the derived stalk of a tensor
product as the tensor product of the derived stalks over the stalk ring
(`derivedTensorStalkIsoGeneral`, the derived form of [Stacks, Tag 01CB]) and using exactness of
the derived tensor product in its first variable.  The right-hand mirror is the same argument
with `DerivedTensorProduct.exact_right` in place of `DerivedTensorProduct.exact_left`, and the
two together give support in the intersection: a point outside `T₁ ∩ T₂` lies outside one of the
two, and the corresponding factor already kills the stalk there.  Disjointness makes the
intersection empty, and a complex with empty cohomological support is zero because a sheaf of
modules with no nonzero stalk is zero
(`AlgebraicGeometry.SheafOfModules.isZero_iff_forall_isZero_stalkFunctor_obj`, Stacks 01AG) and
a complex with no cohomology is zero in the derived category.

*The second half.* The library's [Stacks, Tag 0G03] is
`AlgebraicGeometry.exists_mem_forall_stalkHomology_isZero_of_hom_residueFieldSkyscraper`, and it
takes as hypothesis that no shift of the residue-field skyscraper at `x` receives a nonzero map
from `K`.  That hypothesis is *equivalent*
to the vanishing of all cohomology stalks at `x`, by the library's [Stacks, Tag 0GWZ],
`AlgebraicGeometry.stalkHomology_isZero_iff_hom_residueFieldSkyscraper_subsingleton`: the
equivalence there is stated degreewise above a bound `b`, so it is applied once per degree `i`
with `b := i - 1`.  Reading 0G03 this way is what makes it usable from a tensor computation,
since a tensor computation produces stalk information and not Hom information.

*Joining the two halves.* The first half outputs `IsZero (K ⊗^𝐋 𝒪_z)`; the second half wants
`H^i(K)_z = 0` for every `i`.  Passing from one to the other is derived Nakayama over the local
ring `𝒪_z`, which is what the source's proof of 0G03 invokes (More on Algebra, Lemma 15.78.4 =
[Stacks, Tag 068U]) for its parts (5) and (6).  Those parts are now proved, as
`AlgebraicGeometry.exists_mem_isZero_stalkHomology_of_derivedTensor_residueField` and
`AlgebraicGeometry.exists_mem_forall_isZero_stalkHomology_of_derivedTensor_residueField`; their
hypothesis is the vanishing of the cohomology of the *derived stalk* of `K ⊗^𝐋 𝒪_z` at `z`,
which a zero object satisfies because the derived stalk and the homology functors send a zero
object to a zero object.  That is the whole content of
`exists_mem_forall_isZero_stalkHomology_of_isZero_derivedTensorSkyscraper` below.

*Why instances are named in the local context.* Two places hand the elaborator an instance that
already exists rather than letting it search, each for the reason recorded at length in
`StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.DerivedTensorStalk` and in
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/ProjectionFormulaClosedEmbeddingUnconditional.lean`, whose
`cohomologySupportedOn_derivedTensor_of_left` — the mirror of
`cohomologySupportedOn_derivedTensor_of_right` below — does exactly the same thing.

* `CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective` for `AddCommGrpCat` is a *cost*
  problem, not a spelling one: that instance is affordable once, but
  `Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct` asks for
  `∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj M).Additive` as a single synthesis
  goal, and inside that binder the search is repeated for every candidate, exhausting the
  heartbeat budget before any is settled.  Named in the local context it is found without
  search; no heartbeat limit is changed.  The three statements over
  `Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor` carry the same `letI` in their
  conclusions, which is zeta-reducible and so states exactly what it stated without it.
* the exactness of `AlgebraicGeometry.SheafOfModules.stalkFunctor` is handed over because the
  instances `stalkFunctor_additive`, `stalkFunctor_preservesFiniteLimits` and
  `stalkFunctor_preservesColimits` are keyed on `𝒪.obj` for an opaque sheaf of rings, while
  `Stacks.SheafOfModules.Tensor.ringSheaf R` projects to a `Sheaf` literal, so lookup never
  offers them even though applying them succeeds.
* in `exists_mem_forall_isZero_stalkHomology_of_isZero_derivedTensorSkyscraper` the vanishing of
  the derived stalk is restated as `hstalk` over `X.ringCatSheaf`.  `X.ringCatSheaf` and
  `Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf` are `rfl`-equal
  (`StacksDraft.StalkRingComparison.stalkRing_eq_ringCatSheaf`) but not interchangeable for
  instance lookup, and the hypothesis of [Stacks, Tag 0G03] part (6) names the stalk ring in the
  second spelling.  Naming the intermediate vanishing in the first lets the final step cross
  between them by unification alone.

*What Case I still waits on.* Not homological algebra but the geometry of `0G0R`'s closed immersion
`i : Y_s ×_k Y_s ⟶ X ×_S Y`.  Two things are missing.  First, `i` is not known to be a closed
immersion: `AlgebraicGeometry.fibreSquareToProductComparison` is built as a morphism only, and
identifying it with the inclusion of the fibre `(X ×_S Y)_s` requires the pullback pasting
`Y_s ×_k Y_s ≅ (X ×_S Y)_s` together with the fact that a `k`-rational point of a finite-type
`k`-scheme is a closed point.  Second, the source's identification of `i_*𝒪_z` with the
residue-field skyscraper at `z` on `X ×_S Y` is not available.  Once `i` is a closed embedding the
transfer itself is immediate from the unconditional [Stacks, Tag 0B55] of this library,
`Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_of_isClosedEmbedding`, which
has no hypothesis on either tensor factor; the general projection formula of [Stacks, Tag 08EU] is
*not* needed, since `i` is a closed immersion.  No `stacks` attribute is placed anywhere in this
file.

## References

* [Stacks Project, Tag 0G0R](https://stacks.math.columbia.edu/tag/0G0R)
* [Stacks Project, Tag 0G0Q](https://stacks.math.columbia.edu/tag/0G0Q)
* [Stacks Project, Tag 0G03](https://stacks.math.columbia.edu/tag/0G03)
* [Stacks Project, Tag 0GWZ](https://stacks.math.columbia.edu/tag/0GWZ)
* [Stacks Project, Tag 0B55](https://stacks.math.columbia.edu/tag/0B55)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 068U](https://stacks.math.columbia.edu/tag/068U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

/-- The stalk functor on sheaves of modules is additive and preserves finite limits and colimits. -/
private theorem stalkFunctor_additive_and_preserves {X : TopCat.{u}}
    (𝒪 : CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (x : X) :
    (AlgebraicGeometry.SheafOfModules.stalkFunctor 𝒪 x).Additive ∧
      PreservesFiniteLimits (AlgebraicGeometry.SheafOfModules.stalkFunctor 𝒪 x) ∧
      PreservesColimits (AlgebraicGeometry.SheafOfModules.stalkFunctor 𝒪 x) :=
  ⟨AlgebraicGeometry.SheafOfModules.stalkFunctor_additive 𝒪 x,
    AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesFiniteLimits 𝒪 x,
    AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits 𝒪 x⟩

/-! ### Disjoint cohomological supports kill a derived tensor product -/

namespace Stacks.SheafOfModules.DerivedTensorStalk

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}}
  (R : CategoryTheory.Sheaf.{u, u, u, u + 1} (Opens.grothendieckTopology X) CommRingCat.{u})

/-- Tensoring anything with a zero object of `D(Λ)` is zero: the derived tensor product is exact,
hence additive, in its second variable.  This is the mirror of
`Stacks.SheafOfModules.DerivedTensorStalk.isZero_derivedTensor_of_isZero_left`. -/
lemma isZero_derivedTensor_of_isZero_right {Λ : Type u} [CommRing Λ]
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct Λ)
    (A B : CochainComplex.DerivedTensor.DObj Λ) (hB : IsZero B) :
    IsZero ((T.tensor.obj A).obj B) := by
  let _ := T.commShift_right A
  let _ := T.exact_right A
  exact Functor.map_isZero (T.tensor.obj A) hB

/-- **The derived tensor product of an arbitrary complex with a complex supported on `T` is
supported on `T`.**  The mirror of
`Stacks.SheafOfModules.DerivedTensorStalk.cohomologySupportedOn_derivedTensor_of_left`, proved
the same way: the derived stalk of the tensor product is the tensor product of the derived
stalks over the stalk ring, and the second of them vanishes outside `T`. -/
theorem cohomologySupportedOn_derivedTensor_of_right (T : Set X)
    (A K : DerivedCategory (Stacks.DerivedTensor.RingedSite.Modules R))
    (hK : AlgebraicGeometry.CohomologySupportedOn
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) T K) :
    letI : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
      inferInstance
    AlgebraicGeometry.CohomologySupportedOn
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) T
      (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor R).obj A).obj K) := by
  let : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    inferInstance
  rw [AlgebraicGeometry.cohomologySupportedOn_iff_forall_isZero_derivedStalk]
  intro y hy
  obtain ⟨_, _, _⟩ := stalkFunctor_additive_and_preserves
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) y
  refine IsZero.of_iso ?_ (derivedTensorStalkIsoGeneral R y A K).symm
  refine isZero_derivedTensor_of_isZero_right
    (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct _) _ _ ?_
  exact (AlgebraicGeometry.cohomologySupportedOn_iff_forall_isZero_derivedStalk _ T K).1 hK y hy

/-- **The derived tensor product of a complex supported on `T₁` with one supported on `T₂` is
supported on `T₁ ∩ T₂`.**  A point outside the intersection lies outside one of the two sets, and
there the corresponding factor already makes the derived stalk vanish. -/
theorem cohomologySupportedOn_derivedTensor_inter (T₁ T₂ : Set X)
    (A K : DerivedCategory (Stacks.DerivedTensor.RingedSite.Modules R))
    (hA : AlgebraicGeometry.CohomologySupportedOn
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) T₁ A)
    (hK : AlgebraicGeometry.CohomologySupportedOn
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) T₂ K) :
    letI : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
      inferInstance
    AlgebraicGeometry.CohomologySupportedOn
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) (T₁ ∩ T₂)
      (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor R).obj A).obj K) := by
  let : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    inferInstance
  intro i y hy
  by_cases hy₁ : y ∈ T₁
  · exact cohomologySupportedOn_derivedTensor_of_right R T₂ A K hK i y
      (fun hy₂ => hy ⟨hy₁, hy₂⟩)
  · exact cohomologySupportedOn_derivedTensor_of_left R T₁ A K hA i y hy₁

/-- **A complex whose cohomology is supported on the empty set is a zero object.**  Its
cohomology sheaves have no nonzero stalk, hence vanish by Stacks 01AG, and a complex with no
cohomology is zero in the derived category. -/
theorem isZero_of_cohomologySupportedOn_empty
    (E : DerivedCategory (Stacks.DerivedTensor.RingedSite.Modules R))
    (hE : AlgebraicGeometry.CohomologySupportedOn
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) (∅ : Set X) E) :
    IsZero E := by
  refine CategoryTheory.DerivedCategory.isZero_of_forall_isZero_homology fun n => ?_
  rw [AlgebraicGeometry.SheafOfModules.isZero_iff_forall_isZero_stalkFunctor_obj]
  intro y
  exact (AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj_iff _ y _).2
    (hE n y (by simp))

/-- **Disjoint cohomological supports kill a derived tensor product.**  This is the first half of
Case I of [Stacks, Tag 0G0R]: there `A` is the restriction of the kernel to the fibre, supported
on the diagonal, `K` is the skyscraper at a closed point `z` off the diagonal, and the conclusion
is the vanishing the source records as `K ⊗^𝐋 i_*𝒪_z = 0`. -/
@[sga "4 XVIII 1.3.17" "Vanishing clause only"]
theorem isZero_derivedTensor_of_disjoint_support (T₁ T₂ : Set X) (hdisj : Disjoint T₁ T₂)
    (A K : DerivedCategory (Stacks.DerivedTensor.RingedSite.Modules R))
    (hA : AlgebraicGeometry.CohomologySupportedOn
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) T₁ A)
    (hK : AlgebraicGeometry.CohomologySupportedOn
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) T₂ K) :
    letI : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
      inferInstance
    IsZero (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor R).obj A).obj K) := by
  let : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    inferInstance
  refine isZero_of_cohomologySupportedOn_empty R _ ?_
  rw [← hdisj.inter_eq]
  exact cohomologySupportedOn_derivedTensor_inter R T₁ T₂ A K hA hK

end Stacks.SheafOfModules.DerivedTensorStalk

/-! ### Stacks 0G03 with a stalk hypothesis -/

namespace AlgebraicGeometry

/-- **[Stacks, Tag 0G03] with its hypothesis read on stalks.**  Let `X` be a Noetherian scheme,
`x` a point of `X` and `K` a bounded complex of `𝒪_X`-modules with coherent cohomology.  If every
cohomology stalk of `K` at `x` vanishes, then every cohomology stalk of `K` vanishes at every
point of an open neighbourhood of `x`.

This is `AlgebraicGeometry.exists_mem_forall_stalkHomology_isZero_of_hom_residueFieldSkyscraper`,
whose hypothesis is that no shift of the residue-field skyscraper at `x` receives a nonzero map
from `K`, with that hypothesis supplied by [Stacks, Tag 0GWZ],
`AlgebraicGeometry.stalkHomology_isZero_iff_hom_residueFieldSkyscraper_subsingleton`, which says
the two are equivalent.  The equivalence is stated degreewise above a bound, so it is applied in
each degree `i` with the bound `i - 1`.

It bears no `stacks` attribute: the covering declaration for 0G03 in this library is the one
cited above, and this is that statement with an equivalent hypothesis. -/
theorem exists_mem_forall_stalkHomology_isZero_of_stalkHomology_isZero
    (X : Scheme.{u}) [IsNoetherian X] (x : X)
    [HasDerivedCategory (SheafOfModules.{u} X.ringCatSheaf)]
    (K : DerivedCategory.Bounded (SheafOfModules.{u} X.ringCatSheaf))
    (hK : ∀ i : ℤ,
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} X.ringCatSheaf) i).obj K.obj).IsCoherent)
    (hx : ∀ i : ℤ,
      IsZero (OXModule.stalk
        ((DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) i).obj K.obj) x)) :
    ∃ U : Opens X.carrier, x ∈ U ∧ ∀ y : X, y ∈ U → ∀ i : ℤ,
      IsZero (OXModule.stalk
        ((DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) i).obj K.obj) y) :=
  exists_mem_forall_stalkHomology_isZero_of_hom_residueFieldSkyscraper X x K hK fun i =>
    (stalkHomology_isZero_iff_hom_residueFieldSkyscraper_subsingleton X x K hK (i - 1)).mp
      (fun j _ => hx j) i (by omega)

/-! ### The two halves joined -/

section JoinedHalves

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.AssociatedSheaf.hasModuleSheafify
  Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective

/-- **A perfect complex killed by the residue-field skyscraper at `x` vanishes near `x`.**  Let
`X` be a Noetherian scheme, `x` a point of `X`, and `K` a perfect object of `D(𝒪_X)` whose
derived tensor product with the skyscraper `𝒪_x` at `x` with value `κ(x)` is a *zero object* of
`D(𝒪_X)`.  Then every cohomology sheaf of `K` has vanishing stalk at every point of an open
neighbourhood of `x`.

This is [Stacks, Tag 0G03] part (6),
`AlgebraicGeometry.exists_mem_forall_isZero_stalkHomology_of_derivedTensor_residueField`, whose
hypothesis is the degreewise vanishing of the cohomology of the derived stalk of
`K ⊗^𝐋_{𝒪_X} 𝒪_x` at `x`.  A zero object satisfies it because the derived stalk functor and the
homology functors preserve zero objects.

It is the form Case I of [Stacks, Tag 0G0R] needs: the first half of that case produces a zero
*object*, by `Stacks.SheafOfModules.DerivedTensorStalk.isZero_derivedTensor_of_disjoint_support`,
and not a statement about stalks.

No `stacks` attribute is carried: this is part (6) with a hypothesis strictly stronger than the
source's, and the covering declaration for 0G03 is the one cited above. -/
theorem exists_mem_forall_isZero_stalkHomology_of_isZero_derivedTensorSkyscraper
    (X : Scheme.{u}) [IsNoetherian X] (x : X)
    (K : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))
    (hK : RingedSpace.IsPerfect (X := X.toRingedSpace) K)
    (h : IsZero (derivedTensorResidueFieldSkyscraper X x K)) :
    ∃ U : Opens X.carrier, x ∈ U ∧ ∀ y : X, y ∈ U → ∀ i : ℤ,
      IsZero (SheafOfModules.stalkObj X.ringCatSheaf y
        ((DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) i).obj K)) := by
  obtain ⟨_, _, _⟩ := stalkFunctor_additive_and_preserves X.ringCatSheaf x
  refine exists_mem_forall_isZero_stalkHomology_of_derivedTensor_residueField X x K hK fun _ => ?_
  let : (SheafOfModules.stalkFunctor X.ringCatSheaf x).mapDerivedCategory.Additive :=
    inferInstance
  have hstalk : IsZero ((SheafOfModules.stalkFunctor X.ringCatSheaf x).mapDerivedCategory.obj
      (derivedTensorResidueFieldSkyscraper X x K)) :=
    Functor.map_isZero _ h
  exact Functor.map_isZero _ hstalk

end JoinedHalves

end AlgebraicGeometry

end
