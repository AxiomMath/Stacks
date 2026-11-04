module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.NoDeformations.ComparisonClosedImmersion
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.NoDeformations.DiagonalFibreVanishing
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.DeducingFullyFaithfulness.ResidueFieldSkyscraperPushforward
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.ClosedImmersionPushforward
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.ThickeningQuasicoherent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorReseat
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ClosedEmbeddingProjectionFormulaDerived
public import StacksFrontier.Topology.Sheaves.Modules.SkyscraperSupport
import StacksCore.Tactic.StacksAttribute

/-!
# Case I of Stacks 0G0R: the kernel vanishes near a point off the diagonal

[Stacks, Tag 0G0R] runs over the closed points `z` of the fibre `Y_s ×_k Y_s` of `X ×_S Y ⟶ S`
and splits into two cases.  **Case I** is `z ∉ Δ_{Y_s/k}(Y_s)`, and the source's argument is the
chain

`K ⊗^𝐋_{𝒪_{X ×_S Y}} i_*𝒪_z = Li^*K ⊗^𝐋_{𝒪_{Y_s × Y_s}} 𝒪_z = 0`,

followed by [Stacks, Tag 0G03]: the vanishing of that derived tensor product produces an open
neighbourhood `U(z)` of `z` in `X ×_S Y` on which `K` vanishes.

This file supplies the *first* equality of that chain — the step the source writes down without
comment and which is where all the machinery sits — and then closes Case I by feeding the result
into [Stacks, Tag 0G03].  Nothing here is about the diagonal: the statements are about an
arbitrary closed immersion `i : Z ⟶ W` of schemes, which is what `i` is in the source
(`AlgebraicGeometry.isClosedImmersion_fibreSquareToProductComparison`).

## Main definitions

* `AlgebraicGeometry.derivedTensorSymmIso`: the symmetry `A ⊗^𝐋_𝒪 B ≅ B ⊗^𝐋_𝒪 A` of the derived
  tensor product of [Stacks, Tag 06YU] on a ringed space.
* `AlgebraicGeometry.closedImmersionProjectionFormulaIso`: [Stacks, Tag 0B55] at a closed
  immersion of schemes, as an isomorphism.

## Main results

* `AlgebraicGeometry.isZero_derivedPushforward_of_isZero`: `Ri_*` of a zero object is zero.
* `AlgebraicGeometry.isZero_derivedTensorResidueFieldSkyscraper_of_isZero_derivedPullback`:
  **the source's first equality.**  For a closed immersion `i : Z ⟶ W` of schemes and `z : Z`, if
  `𝒪_z ⊗^𝐋_{𝒪_Z} Li^*K` is a zero object of `D(𝒪_Z)` then `K ⊗^𝐋_{𝒪_W} 𝒪_{i(z)}` is a zero
  object of `D(𝒪_W)`.
* `AlgebraicGeometry.exists_mem_forall_isZero_stalkHomology_caseI`: **Case I.**  For `W` a
  Noetherian scheme, `K` a perfect object of `D(𝒪_W)` and `i : Z ⟶ W` a closed immersion, if
  `𝒪_z ⊗^𝐋_{𝒪_Z} Li^*K = 0` then `K` vanishes on an open neighbourhood of `i(z)`.
* `AlgebraicGeometry.exists_mem_forall_isZero_stalkHomology_caseI_of_cohomologySupportedOn`:
  **Case I from the source's own assumption.**  The same conclusion with the hypothesis read as
  the source states it: `z` is a closed point of `Z` and the cohomology of `Li^*K` is supported on
  a set not containing `z`.  In [Stacks, Tag 0G0R] that set is `Δ_{Y_s/k}(Y_s)`, because `Li^*K`
  is `Δ_{Y_s/k,*}𝒪_{Y_s}` there.
* `AlgebraicGeometry.exists_mem_forall_isZero_stalkHomology_caseI_fibreSquare`: Case I at the
  comparison morphism `i : Y_s ×_k Y_s ⟶ X ×_S Y` of [Stacks, Tag 0G0R], which is the shape in
  which the source uses it.

## Implementation notes

*The three ingredients of the first equality.*  The source's `K ⊗^𝐋 i_*𝒪_z = Li^*K ⊗^𝐋 𝒪_z` is
the projection formula read backwards, and it needs three things, all of them already in the
library:

* **the projection formula at `i`.**  `Ri_*E ⊗^𝐋_{𝒪_W} K ≅ Ri_*(E ⊗^𝐋_{𝒪_Z} Li^*K)` is
  [Stacks, Tag 0B55], and this library's
  `Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_of_isClosedEmbedding`
  proves it for an arbitrary morphism of ringed spaces whose base map is a closed embedding, with
  no hypothesis on either complex.  The general projection formula of [Stacks, Tag 08EU] is *not*
  needed, because `i` is a closed immersion.
* **the direct image of the skyscraper.**  `Ri_*𝒪_z = i_*𝒪_z = 𝒪_{i(z)}`.  The first equality is
  exactness of `i_*` along a closed embedding, in the form
  `Stacks.Thickenings.derivedPushforwardSingleIso`; the second is
  `AlgebraicGeometry.pushforwardResidueFieldSkyscraperIso`.
* **the symmetry of the derived tensor product.**  The projection formula puts `Ri_*E` in the
  *left* tensor slot, whereas `AlgebraicGeometry.derivedTensorResidueFieldSkyscraper` — the form
  [Stacks, Tag 0G03] consumes — puts the skyscraper on the right.  The commutativity constraint
  of [Stacks, Tag 0FPB], re-seated by
  `Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric` so that its tensor product is
  the derived tensor product of [Stacks, Tag 06YU] on the nose, exchanges them.

*Where the hypothesis comes from.*  The source gets `𝒪_z ⊗^𝐋 Li^*K = 0` from disjointness of
supports: `Li^*K = Δ_{Y_s/k,*}𝒪_{Y_s}` is supported on the diagonal and `z` is a closed point off
it.  That implication is
`Stacks.SheafOfModules.DerivedTensorStalk.isZero_derivedTensor_of_disjoint_support` together with
`AlgebraicGeometry.SheafOfModules.cohomologySupportedOn_singleFunctor_skyscraperObj`, which says
the skyscraper at `z` is supported on `closure {z}` — so `{z}` for a closed point.  The support of
`Δ_{Y_s/k,*}𝒪_{Y_s}` itself is
`AlgebraicGeometry.cohomologySupportedOn_singleFunctor_pushforward_unit` ([Stacks, Tag 0CSJ]).

*Why `Ri_*` preserves zero objects is not an instance.*  `Rf_*` is a total right derived functor
and carries no additivity instance.  Along a closed immersion it is isomorphic to the functor
`i_*` induces on derived categories
(`Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategoryOfSchemes`), and that one is
additive because `i_*` is.

*The derived-category model.*  `HasDerivedCategory.standard` is given priority here, as in
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/ClosedImmersionStructureSheaf.lean`, so that the
model agrees with the one the pushforward and projection-formula development is stated over;
`StacksFrontier.Homology.DerivedCategory.LocallySmall` otherwise supplies a competing model at a
smaller universe.

No `stacks` attribute is carried.  Case I is one half of the proof of [Stacks, Tag 0G0R], not a
tagged result of the source, and the covering declarations for [Stacks, Tag 0G03] and
[Stacks, Tag 0B55] are the ones cited above.

## References

* [Stacks Project, Tag 0G0R](https://stacks.math.columbia.edu/tag/0G0R)
* [Stacks Project, Tag 0G03](https://stacks.math.columbia.edu/tag/0G03)
* [Stacks Project, Tag 0B55](https://stacks.math.columbia.edu/tag/0B55)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0FPB](https://stacks.math.columbia.edu/tag/0FPB)
* [Stacks Project, Tag 0E2K](https://stacks.math.columbia.edu/tag/0E2K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite
open Stacks.SheafOfModules.DerivedMonoidal

universe u

attribute [local instance 100000] HasDerivedCategory.standard
attribute [local instance] Stacks.AssociatedSheaf.hasModuleSheafify
  Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective

namespace AlgebraicGeometry

/-! ### The symmetry of the derived tensor product -/

section Symmetry

variable {X : TopCat.{u}}
  (R : CategoryTheory.Sheaf.{u, u, u, u + 1} (Opens.grothendieckTopology X) CommRingCat.{u})

/-- **The derived tensor product of [Stacks, Tag 06YU] is symmetric.**  This is the
commutativity constraint of [Stacks, Tag 0FPB], read through
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric`, whose monoidal structure has
the derived tensor bifunctor of [Stacks, Tag 06YU] as its tensor product on the nose
(`Stacks.SheafOfModules.DerivedMonoidal.curriedTensor_canonicalDerivedMonoidal`), so no transport
appears in the statement. -/
def derivedTensorSymmIso (A B : DerivedCategory (Modules R)) :
    ((derivedTensorProductFunctor R).obj A).obj B ≅
      ((derivedTensorProductFunctor R).obj B).obj A :=
  letI := canonicalDerivedMonoidal R
  letI := canonicalDerivedSymmetric R
  β_ A B

end Symmetry

/-! ### `K ⊗^𝐋 i_*𝒪_z = Li^*K ⊗^𝐋 𝒪_z` -/

section ClosedImmersion

variable {Z W : Scheme.{u}} (i : Z ⟶ W) [IsClosedImmersion i]

/-- **`Ri_*` of a zero object is a zero object.**  Along a closed immersion `Ri_*` is the functor
`i_*` induces on derived categories, by
`Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategoryOfSchemes`, and that functor is
additive because `i_*` is. -/
theorem isZero_derivedPushforward_of_isZero
    {A : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))}
    (hA : IsZero A) :
    IsZero ((derivedPushforward i.toLRSHom.toShHom).obj A) := by
  refine IsZero.of_iso ?_
    ((Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategoryOfSchemes i).app A)
  exact Functor.map_isZero _ hA

/-- **[Stacks, Tag 0B55] at a closed immersion of schemes**, as an isomorphism:

`Ri_*E ⊗^𝐋_{𝒪_W} K ≅ Ri_*(E ⊗^𝐋_{𝒪_Z} Li^*K)`

for arbitrary `E` in `D(𝒪_Z)` and `K` in `D(𝒪_W)`.  The underlying morphism is the one of
[Stacks, Tag 0B53], and it is invertible by
`Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_of_isClosedEmbedding`,
whose only hypothesis is that the base map be a closed embedding. -/
def closedImmersionProjectionFormulaIso
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing W.toRingedSpace))) :
    ((derivedTensorProductFunctor W.toRingedSpace.sheaf).obj
        ((derivedPushforward i.toLRSHom.toShHom).obj E)).obj K ≅
      (derivedPushforward i.toLRSHom.toShHom).obj
        (((derivedTensorProductFunctor Z.toRingedSpace.sheaf).obj E).obj
          ((derivedPullback i.toLRSHom.toShHom).obj K)) :=
  @asIso _ _ _ _ _
    (Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_of_isClosedEmbedding
      i.toLRSHom.toShHom i.isClosedEmbedding E K)

/-- **The first equality of Case I of [Stacks, Tag 0G0R]:**
`K ⊗^𝐋_{𝒪_W} i_*𝒪_z = Li^*K ⊗^𝐋_{𝒪_Z} 𝒪_z`, in the form in which the source uses it.

Let `i : Z ⟶ W` be a closed immersion of schemes, `z` a point of `Z` and `K` an object of
`D(𝒪_W)`.  If the derived tensor product of the residue-field skyscraper `𝒪_z` at `z` with the
derived pullback `Li^*K` is a zero object of `D(𝒪_Z)`, then the derived tensor product of `K`
with the residue-field skyscraper `𝒪_{i(z)}` at `i(z)` is a zero object of `D(𝒪_W)`.

The proof is the source's identification read as a chain of isomorphisms: push the hypothesis
forward along `Ri_*`, pull it back across the projection formula of [Stacks, Tag 0B55] at `i`,
replace `Ri_*𝒪_z` by `𝒪_{i(z)}`, and exchange the two tensor factors. -/
theorem isZero_derivedTensorResidueFieldSkyscraper_of_isZero_derivedPullback
    (z : Z) (K : DerivedCategory (SheafOfModules.{u} W.ringCatSheaf))
    (h : IsZero (((derivedTensorProductFunctor Z.toRingedSpace.sheaf).obj
      ((DerivedCategory.singleFunctor (SheafOfModules.{u}
        (structureSheafRing Z.toRingedSpace)) 0).obj (residueFieldSkyscraperSheaf Z z))).obj
      ((derivedPullback i.toLRSHom.toShHom).obj K))) :
    IsZero (derivedTensorResidueFieldSkyscraper W (i.base z) K) := by
  -- `Ri_*𝒪_z ⊗^𝐋 K ≅ Ri_*(𝒪_z ⊗^𝐋 Li^*K) = 0`
  have h₁ : IsZero (((derivedTensorProductFunctor W.toRingedSpace.sheaf).obj
      ((derivedPushforward i.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u}
          (structureSheafRing Z.toRingedSpace)) 0).obj
          (residueFieldSkyscraperSheaf Z z)))).obj K) :=
    IsZero.of_iso (isZero_derivedPushforward_of_isZero i h)
      (closedImmersionProjectionFormulaIso i _ K)
  -- `Ri_*𝒪_z = i_*𝒪_z = 𝒪_{i(z)}`
  have h₂ : IsZero (((derivedTensorProductFunctor W.toRingedSpace.sheaf).obj
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} W.ringCatSheaf) 0).obj
        (residueFieldSkyscraperSheaf W (i.base z)))).obj K) := by
    refine IsZero.of_iso h₁
      (((derivedTensorProductFunctor W.toRingedSpace.sheaf).mapIso ?_).app K)
    exact ((Stacks.Thickenings.derivedPushforwardSingleIso i.toLRSHom.toShHom
        i.isClosedEmbedding _).trans
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} W.ringCatSheaf) 0).mapIso
        (pushforwardResidueFieldSkyscraperIso i z))).symm
  -- exchange the two tensor factors
  exact IsZero.of_iso h₂ (derivedTensorSymmIso W.sheaf _ _)

/-- **Case I of [Stacks, Tag 0G0R].**  Let `i : Z ⟶ W` be a closed immersion of schemes with `W`
Noetherian, let `K` be a perfect object of `D(𝒪_W)` and let `z` be a point of `Z`.  If

`𝒪_z ⊗^𝐋_{𝒪_Z} Li^*K = 0`

in `D(𝒪_Z)` — which is the source's hypothesis in Case I, since there `Li^*K` is
`Δ_{Y_s/k,*}𝒪_{Y_s}` and `z` lies off the diagonal — then there is an open neighbourhood `U` of
`i(z)` in `W` on which every cohomology sheaf of `K` has vanishing stalks.  This is the
`K|_{U(z)} = 0` of the source.

The hypothesis is carried across the closed immersion by
`isZero_derivedTensorResidueFieldSkyscraper_of_isZero_derivedPullback` and then handed to
[Stacks, Tag 0G03] part (6) in the form
`AlgebraicGeometry.exists_mem_forall_isZero_stalkHomology_of_isZero_derivedTensorSkyscraper`. -/
theorem exists_mem_forall_isZero_stalkHomology_caseI [IsNoetherian W]
    (z : Z) (K : DerivedCategory (SheafOfModules.{u} W.ringCatSheaf))
    (hK : RingedSpace.IsPerfect (X := W.toRingedSpace) K)
    (h : IsZero (((derivedTensorProductFunctor Z.toRingedSpace.sheaf).obj
      ((DerivedCategory.singleFunctor (SheafOfModules.{u}
        (structureSheafRing Z.toRingedSpace)) 0).obj (residueFieldSkyscraperSheaf Z z))).obj
      ((derivedPullback i.toLRSHom.toShHom).obj K))) :
    ∃ U : Opens W.carrier, i.base z ∈ U ∧ ∀ y : W, y ∈ U → ∀ n : ℤ,
      IsZero (SheafOfModules.stalkObj W.ringCatSheaf y
        ((DerivedCategory.homologyFunctor (SheafOfModules.{u} W.ringCatSheaf) n).obj K)) :=
  exists_mem_forall_isZero_stalkHomology_of_isZero_derivedTensorSkyscraper W (i.base z) K hK
    (isZero_derivedTensorResidueFieldSkyscraper_of_isZero_derivedPullback i z K h)

/-- **Case I of [Stacks, Tag 0G0R] with the hypothesis as the source states it.**  Let
`i : Z ⟶ W` be a closed immersion of schemes with `W` Noetherian, let `K` be a perfect object of
`D(𝒪_W)`, let `z` be a *closed* point of `Z`, and suppose the cohomology of `Li^*K` is supported
on a subset `T` of `Z` with `z ∉ T`.  Then `K` vanishes on an open neighbourhood of `i(z)`.

In [Stacks, Tag 0G0R] the complex `Li^*K` is `Δ_{Y_s/k,*}𝒪_{Y_s}` by assumption, `T` is the
diagonal `Δ_{Y_s/k}(Y_s)` — on which that complex is supported, by [Stacks, Tag 0CSJ] — and
`z ∉ T` is exactly the case distinction `z ∉ Δ_{Y_s/k}(Y_s)` opening Case I.

The hypothesis of `exists_mem_forall_isZero_stalkHomology_caseI` is produced by the
disjoint-support vanishing of
`Stacks.SheafOfModules.DerivedTensorStalk.isZero_derivedTensor_of_disjoint_support`: the
skyscraper at `z` is supported on `closure {z} = {z}`, which is disjoint from `T`. -/
theorem exists_mem_forall_isZero_stalkHomology_caseI_of_cohomologySupportedOn [IsNoetherian W]
    (z : Z) (hz : IsClosed ({z} : Set Z)) (T : Set Z) (hzT : z ∉ T)
    (K : DerivedCategory (SheafOfModules.{u} W.ringCatSheaf))
    (hK : RingedSpace.IsPerfect (X := W.toRingedSpace) K)
    (hT : CohomologySupportedOn Z.ringCatSheaf T
      ((derivedPullback i.toLRSHom.toShHom).obj K)) :
    ∃ U : Opens W.carrier, i.base z ∈ U ∧ ∀ y : W, y ∈ U → ∀ n : ℤ,
      IsZero (SheafOfModules.stalkObj W.ringCatSheaf y
        ((DerivedCategory.homologyFunctor (SheafOfModules.{u} W.ringCatSheaf) n).obj K)) := by
  refine exists_mem_forall_isZero_stalkHomology_caseI i z K hK ?_
  have hdisj : Disjoint (closure ({z} : Set Z)) T := by
    rw [hz.closure_eq, Set.disjoint_singleton_left]
    exact hzT
  exact Stacks.SheafOfModules.DerivedTensorStalk.isZero_derivedTensor_of_disjoint_support
    Z.sheaf (closure ({z} : Set Z)) T hdisj _ _
    (SheafOfModules.cohomologySupportedOn_singleFunctor_skyscraperObj Z.ringCatSheaf z
      (residueFieldStalkModule Z z)) hT

end ClosedImmersion

/-! ### Case I at the comparison morphism of Stacks 0G0R -/

section FibreSquare

variable {k : Type u} [Field k] {S Y : Scheme.{u}}
  (q : S ⟶ Spec (.of k)) (g : Y ⟶ S) (s : Spec (.of k) ⟶ S) (hs : s ≫ q = 𝟙 _)

/-- **Case I of [Stacks, Tag 0G0R] at the source's own closed immersion.**  With `X = Y_s ×_k S`
the constant family and `i : Y_s ×_k Y_s ⟶ X ×_S Y` the comparison morphism of
[Stacks, Tag 0G0R] — a closed immersion by
`AlgebraicGeometry.isClosedImmersion_fibreSquareToProductComparison` — a point `z` of
`Y_s ×_k Y_s` at which `𝒪_z ⊗^𝐋 Li^*K` vanishes has an open neighbourhood `U(z)` in `X ×_S Y`
on which `K` vanishes.

In the source `Li^*K` is `Δ_{Y_s/k,*}𝒪_{Y_s}`, whose cohomology is supported on the diagonal, and
the hypothesis is the vanishing of its derived tensor product with the skyscraper at a point `z`
off the diagonal — supplied by
`Stacks.SheafOfModules.DerivedTensorStalk.isZero_derivedTensor_of_disjoint_support`. -/
theorem exists_mem_forall_isZero_stalkHomology_caseI_fibreSquare
    [IsNoetherian (Limits.pullback (constantFamilyπ q g s) g)]
    (z : ↥(Limits.pullback (fibreAtRationalPointπ g s) (fibreAtRationalPointπ g s)))
    (K : DerivedCategory (SheafOfModules.{u}
      (Limits.pullback (constantFamilyπ q g s) g).ringCatSheaf))
    (hK : RingedSpace.IsPerfect
      (X := (Limits.pullback (constantFamilyπ q g s) g).toRingedSpace) K)
    (h : IsZero (((derivedTensorProductFunctor
        (Limits.pullback (fibreAtRationalPointπ g s)
          (fibreAtRationalPointπ g s)).toRingedSpace.sheaf).obj
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing
        (Limits.pullback (fibreAtRationalPointπ g s)
          (fibreAtRationalPointπ g s)).toRingedSpace)) 0).obj
        (residueFieldSkyscraperSheaf
          (Limits.pullback (fibreAtRationalPointπ g s) (fibreAtRationalPointπ g s)) z))).obj
      ((derivedPullback (fibreSquareToProductComparison q g s hs).toLRSHom.toShHom).obj K))) :
    ∃ U : Opens (Limits.pullback (constantFamilyπ q g s) g).carrier,
      (fibreSquareToProductComparison q g s hs).base z ∈ U ∧
      ∀ y : ↥(Limits.pullback (constantFamilyπ q g s) g), y ∈ U → ∀ n : ℤ,
        IsZero (SheafOfModules.stalkObj
          (Limits.pullback (constantFamilyπ q g s) g).ringCatSheaf y
          ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
            (Limits.pullback (constantFamilyπ q g s) g).ringCatSheaf) n).obj K)) :=
  let := isClosedImmersion_fibreSquareToProductComparison q g s hs
  exists_mem_forall_isZero_stalkHomology_caseI (fibreSquareToProductComparison q g s hs) z K hK h

end FibreSquare

end AlgebraicGeometry

end
