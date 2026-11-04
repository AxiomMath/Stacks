module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorAdditiveOnOpens
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.PullbackPushforwardAdjunction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOnARingedSite
import StacksCore.Tactic.StacksAttribute

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

/-!
# The derived pullback on a ringed space: the K-flat resolving datum

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces.  Stacks 06YJ constructs the
derived pullback `Lf^* : D(𝒪_Y) ⟶ D(𝒪_X)` as the total left derived functor of degreewise
pullback, by the resolving-class criterion of Derived Categories 06XN at the class of K-flat
complexes.  That criterion has two halves: the K-flat complexes must *resolve* every complex
of `𝒪_Y`-modules, and degreewise pullback must carry a quasi-isomorphism *between* K-flat
complexes to an isomorphism of `D(𝒪_X)`.

`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackPushforwardAdjunction`
(Stacks Tag 079W) proves the criterion itself, parametrised by an arbitrary resolving datum
`(P, hP, hinv)`.  This file instantiates it at the K-flat class and discharges the resolving
half, leaving the second half as the single remaining input.  It is the ringed-space counterpart
of `Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.hasResolutions_isKFlat`, which does the
same for a ringed topos.

## Main definitions

* `Stacks.Cohomology.KFlatDerivedPullback.IsKFlat` is the K-flat class on the unbounded homotopy
  category of `𝒪_Y`-modules, the intended resolving class for `f^*`.

## Main results

* `Stacks.Cohomology.KFlatDerivedPullback.exists_kFlatResolution`: **Stacks 06YF at the
  ringed-space spelling.**  Every complex of `𝒪_Y`-modules receives a quasi-isomorphism from a
  K-flat complex with flat terms.
* `Stacks.Cohomology.KFlatDerivedPullback.hasResolutions_isKFlat`: **the K-flat complexes resolve
  every complex**, so the resolving half of the datum holds unconditionally.
* `pullbackOnHomotopy_hasPointwiseLeftDerivedFunctor_of_kFlat` and
  `Stacks.Cohomology.KFlatDerivedPullback.pullbackOnHomotopy_hasLeftDerivedFunctor_of_kFlat`:
  existence of `Lf^*`, from the one remaining hypothesis.
* `Stacks.Cohomology.KFlatDerivedPullback.comp_isLeftDerivedFunctor_of_kFlat`: *absoluteness* of
  `Lf^*` from the same one hypothesis.  This is the form the adjunction of Stacks 079W consumes,
  and it is strictly stronger than existence: `Functor.HasLeftDerivedFunctor` does not imply it.
* `Stacks.Cohomology.KFlatDerivedPullback.derivedPullbackPushforwardAdjunction_of_kFlat`:
  `Lf^* ⊣ Rf_*` from the same one hypothesis, the pushforward side being unconditional.

## Implementation notes

*The hypothesis of this file is a theorem*, namely
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackInvertsQuasiIso_isKFlat` (Stacks Tag
079W).  The results below are stated relative to
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.PullbackInvertsQuasiIso f IsKFlat`, and that
hypothesis is supplied unconditionally by that theorem.  Use the unconditional forms of Stacks
Tag 06YJ -- `Stacks.Cohomology.KFlatDerivedPullback.comp_isLeftDerivedFunctor` and
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.hasLeftDerivedFunctor_pullbackOnHomotopy` --
rather than re-deriving anything here.

The route taken was the stalk criterion, not the factorisation of `f^*` through `f^{-1}`:
`AlgebraicGeometry.SheafOfModules.acyclic_iff_forall_stalk_acyclic` reduces the conclusion to
the stalks, Stacks 0098 identifies `(f^* K)_x` with `K_{f x} ⊗_{𝒪_{Y, f x}} 𝒪_{X, x}`
(`Stacks.RingedSpace.stalkModulePullbackComplexIso`), and Stacks 06YB turns K-flatness of `K`
into K-flatness of `K_{f x}` (`Stacks.SheafOfModules.KFlatStalkCriterion.kFlat_iff_stalkwise`,
with `Stacks.SheafOfModules.KFlatPullback.stalkCriterion` the packaged form).

*Named instances.*  The four instance hypotheses of `CochainComplex.KFlatBifunctor.KFlat` are
seated below as named instances rather than left to synthesis. The canonical sheaf tensor
has independent site, ring and module universes. Pinning all five universes and
`J := Opens.grothendieckTopology Y.carrier` determines the module categories before instance
search begins. Two of the four, the additivity of `⊗_{𝒪_Y}`, are the shared
`Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive` and `sheafTensorObjAdditive`;
this is the same device as `Stacks.Cohomology.SheafHomComplexCurrying`'s `sheafTensorAdditive`
and the rest of its `RingedSpace` section.

*Two spellings of the sheaf of rings.*  `structureSheafRing Y` and
`Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf` are equal by `rfl`, but the first is a `def` and
so the equality is invisible to `rw`, `refine` and instance search.  Everything below is
therefore stated in the `structureSheafRing Y` spelling that
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces` uses, and crosses to the other spelling only
inside term-mode proofs, where the conversion check runs at default transparency.

## References

* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 06YF](https://stacks.math.columbia.edu/tag/06YF)
* [Stacks Project, Tag 06YB](https://stacks.math.columbia.edu/tag/06YB)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open RingedSpaceModuleAdjunction

namespace Stacks.Cohomology.KFlatDerivedPullback

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

section Space

variable (Y : RingedSpace.{u, u})

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive

/-- The total complexes `Tot(K₁ ⊗_{𝒪_Y} K₂)` exist. -/
local instance hasMapBifunctorSheafTensor :
    letI : (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).Additive :=
      Stacks.SheafOfModules.Tensor.sheafTensor_additive.{u, u, u, u, u} Y.sheaf
    letI : ∀ left : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf),
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj left).Additive :=
      Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u, u, u} Y.sheaf
    ∀ K₁ K₂ : CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.sheaf)) ℤ,
      HomologicalComplex.HasMapBifunctor K₁ K₂
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)
        (ComplexShape.up ℤ) :=
  Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor.{u, u, u, u, u}
    (J := Opens.grothendieckTopology Y.carrier) Y.sheaf

/-- K-flatness of a complex of `𝒪_Y`-modules, written at the spelling
`Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf` of the sheaf of rings.

Pinning the argument's type here rather than at each use is not cosmetic.  Elaborating
`CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf) K`
against a `K` whose type is written with `structureSheafRing Y` leaves the module universe of the
bifunctor's source an unsolved metavariable at the moment the four instance arguments are
synthesized, and the search then fails on `SheafOfModules.{?u}` with no diagnosis beyond "failed
to synthesize".  With the argument type written out the universes are known before synthesis
runs. -/
def KFlatComplex (K : CochainComplex
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.sheaf)) ℤ) : Prop :=
  letI : (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).Additive :=
    Stacks.SheafOfModules.Tensor.sheafTensor_additive.{u, u, u, u, u} Y.sheaf
  letI : ∀ left : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf),
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj left).Additive :=
    Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u, u, u} Y.sheaf
  CochainComplex.KFlatBifunctor.KFlat
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf) K

/-- **Stacks 06YF at the ringed-space spelling.**  Every complex of `𝒪_Y`-modules receives a
quasi-isomorphism from a K-flat complex whose terms are flat.

This is `Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution`, the statement for a ringed
*site*, read at the site of opens of `Y`.  The only content of the restatement is the passage
between the two spellings `structureSheafRing Y` and
`Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf` of the sheaf of rings, which are `rfl`-equal; it
is recorded as its own theorem because that passage cannot be made inside a tactic proof. -/
theorem exists_kFlatResolution
    (G : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ) :
    ∃ (K : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ) (g : K ⟶ G),
      KFlatComplex Y K ∧
        (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
          (O := Y.sheaf) (K.X i)) ∧ QuasiIso g ∧ (∀ i : ℤ, Epi (g.f i)) :=
  Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution.{u} Y.sheaf G

/-- **The K-flat complexes of `𝒪_Y`-modules**, as a property of objects of the unbounded
homotopy category.  This is the resolving class that Stacks 06YJ uses for `f^*`. -/
def IsKFlat :
    ObjectProperty
      (HomotopyCategory (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ)) :=
  fun M => KFlatComplex Y M.as

/-- **The K-flat complexes resolve every complex of `𝒪_Y`-modules**, by Stacks 06YF.  This
discharges the `HasResolutions` half of a resolving datum for `f^*` at the K-flat class,
leaving `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.PullbackInvertsQuasiIso f IsKFlat`
as the only remaining input. -/
theorem hasResolutions_isKFlat : Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.HasResolutions
  (IsKFlat Y) := by
  intro M
  obtain ⟨N, rfl⟩ := HomotopyCategory.quotient_obj_surjective M
  obtain ⟨K, g, hK, -, hg, -⟩ := exists_kFlatResolution Y N
  refine ⟨(HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K, hK,
    (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map g, ?_⟩
  rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
  exact hg

end Space

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

variable (hinv : Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.PullbackInvertsQuasiIso f
  (IsKFlat Y))

include hinv in
/-- K-flat resolutions compute the derived pullback pointwise, given that `f^*` inverts the
quasi-isomorphisms between K-flat complexes. -/
theorem pullbackOnHomotopy_hasPointwiseLeftDerivedFunctor_of_kFlat :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackOnHomotopy
      f).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ)) :=
  pullbackOnHomotopy_hasPointwiseLeftDerivedFunctor f (IsKFlat Y)
    (hasResolutions_isKFlat Y) hinv

include hinv in
/-- **Existence of the derived pullback `Lf^*`** on the whole unbounded derived category, from
the single hypothesis that `f^*` inverts the quasi-isomorphisms between K-flat complexes. -/
theorem pullbackOnHomotopy_hasLeftDerivedFunctor_of_kFlat :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackOnHomotopy f).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ)) :=
  Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackOnHomotopy_hasLeftDerivedFunctor f
    (IsKFlat Y)
    (hasResolutions_isKFlat Y) hinv

section Absolute

variable [(Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackOnHomotopy
  f).HasLeftDerivedFunctor
  (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ))]

include hinv in
/-- **Absoluteness of `Lf^*`** from the same single hypothesis: the derived pullback stays a
left derived functor after composing with the derived pushforward.

This is what the derived adjunction consumes, and `Functor.HasLeftDerivedFunctor` does not
imply it, so existence of `Lf^*` alone does not suffice for Stacks 079W. -/
theorem comp_isLeftDerivedFunctor_of_kFlat :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f ⋙
      Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).IsLeftDerivedFunctor
      ((Functor.associator DerivedCategory.Qh
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
          (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f)).inv ≫
        Functor.whiskerRight
          (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f)
          (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f))
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ)) :=
  Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.comp_isLeftDerivedFunctor f (IsKFlat Y)
    (hasResolutions_isKFlat Y) hinv

include hinv in
/-- **The adjunction `Lf^* ⊣ Rf_*`** on the unbounded derived categories of sheaves of modules
on ringed spaces, from the same single hypothesis.  The pushforward side of the input is
unconditional. -/
def derivedPullbackPushforwardAdjunction_of_kFlat :
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f ⊣
      Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f :=
  Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackPushforwardAdjunction f (IsKFlat
    Y)
    (hasResolutions_isKFlat Y) hinv

end Absolute

end

end Stacks.Cohomology.KFlatDerivedPullback

end
