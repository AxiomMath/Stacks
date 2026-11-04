module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.FlatRepresentative
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackExistence
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.Morphisms
public import StacksCore.Tactic.StacksAttribute

/-!
# Derived pullback preserves Tor amplitude

Let `f : (Sh(C), O) ⟶ (Sh(C'), O')` be a morphism of ringed topoi and let `E` be an object of
`D(O')` of Tor amplitude in `[a, b]`.  Then `Lf^* E` has Tor amplitude in `[a, b]`.

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_derivedPullback`: **Stacks 08H5.**
* `Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_derivedPullback_of_le`: the same
  for an interval which is already known to be nonempty, which is the shape Stacks 08G1 is
  stated at.
* `Stacks.SheafOfModules.DerivedTensorProduct.hasFiniteTorDimension_derivedPullback`: the
  consequence for finite Tor dimension.

## Implementation notes

*The route.*  `E` is replaced by a bounded flat representative `K` by Stacks 08G1; the
comparison `Lf^* K ⟶ f^* K` is then invertible, by the bounded-above clause of Stacks 06YY; the
degreewise pullback `f^* K` is again flat in each degree, by Stacks 05VD, and still vanishes
outside `[a, b]`, pullback being additive; and Stacks 08G1 read in the easy direction concludes.
That direction needs no comparison of the two derived tensor product data, so the datum on the
source is entirely arbitrary — exactly as in
`Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_derivedRestriction`, which is this
statement for the localization morphism.

*Why the statement is made on a morphism of ringed topoi.*  The Tor-amplitude vocabulary is
stated on `AlgebraicGeometry.RingedSite`, but `Lf^*` is constructed only for an
`AlgebraicGeometry.RingedToposSiteHom`: there is no derived pullback for a morphism of ringed
sites in this tree, and the morphism of ringed topoi that
`AlgebraicGeometry.RingedSite.Hom.associatedRingedToposHom` produces is an abstract
`AlgebraicGeometry.RingedToposHom`, which carries no derived pullback either.  A ringed topos
and a ringed site are the same data, so the Tor-amplitude predicate is read on
`AlgebraicGeometry.RingedTopos.toRingedSite` and nothing is lost.

*`hmos` is not an added hypothesis.*  `AlgebraicGeometry.RingedToposSiteHom` asks only that the
underlying functor be continuous; `f.u.IsMorphismOfSites Y.J X.J` is what makes `f` a morphism
of ringed *topoi*, and it is carried by every statement of the Stacks 06YY, 0G6R and 05VD chain
used here for that reason.

*The two spellings of the localization.*  Stacks 08G1 produces its representative as an object
of `D(O')` through `DerivedCategory.Q`, while the comparison of Stacks 06YY lives on the
homotopy category and so is phrased through `DerivedCategory.Qh`;
`DerivedCategory.quotientCompQhIso` is the bridge, as in the ringed-space statement
`Stacks.Cohomology.TorAmplitude.Pullback.hasTorAmplitude_derivedPullback` of Stacks 09U8.

*Universes.*  Everything collapses to one universe, and the collapse is forced three times
over: Stacks 08G1 produces a representative only when the sections of the structure sheaf live
in `max u v`; `CategoryTheory.Functor.IsMorphismOfSites`, which `hmos` is stated with, is
available only for small categories in a single universe; and the Stacks 06YY and 05VD chain is
stated at `AlgebraicGeometry.RingedTopos.{u, u, u}`.  The hom universe of the derived categories
is likewise not free: it is the one `HasDerivedCategory.standard` provides, which is what the
derived pullback of Stacks 06YY is constructed at.

## References

* [Stacks Project, Tag 08H5](https://stacks.math.columbia.edu/tag/08H5)
* [Stacks Project, Tag 08G1](https://stacks.math.columbia.edu/tag/08G1)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 05VD](https://stacks.math.columbia.edu/tag/05VD)
* [Stacks Project, Tag 09U8](https://stacks.math.columbia.edu/tag/09U8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Cohomology.DerivedPullbackOnRingedTopoi
open Stacks.Sheaves.DerivedPullback.KFlatPullback

namespace Stacks.SheafOfModules.DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, u, u} X.toRingedSite) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, u, u} Y.toRingedSite) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  (f : RingedToposSiteHom X Y) (hmos : f.u.IsMorphismOfSites Y.J X.J)

variable [(pullbackOnHomotopy f).HasLeftDerivedFunctor
  (HomotopyCategory.quasiIso
    (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]

include hmos in
/-- **Stacks 08H5 for a nonempty interval.**  The derived pullback along a morphism of ringed
topoi of an object of Tor amplitude in `[a, b]`, with `a ≤ b`, again has Tor amplitude in
`[a, b]`, for *any* derived tensor product datum on the source.

Stacks 08G1 represents `E` by a complex `K` of flat `O'`-modules concentrated in `[a, b]`.  Such
a `K` is bounded above, so the comparison `Lf^* K ⟶ f^* K` of Stacks 06YY is invertible on it;
`f^* K` has flat terms by Stacks 05VD and is still concentrated in `[a, b]`, pullback being
additive; and a complex of that shape has Tor amplitude in `[a, b]` by the direction of Stacks
08G1 which takes no input. -/
theorem hasTorAmplitude_derivedPullback_of_le
    (T : DerivedTensorProduct Y.toRingedSite) (T' : DerivedTensorProduct X.toRingedSite)
    (E : RingedSite.DerivedModules Y.toRingedSite) (a b : ℤ) (hab : a ≤ b)
    (hamp : HasTorAmplitude T E a b) :
    HasTorAmplitude T' ((derivedPullback f).obj E) a b := by
  obtain ⟨K, hflat, hzero, ⟨e⟩⟩ := exists_flatRepresentative_of_hasTorAmplitude T E a b hab hamp
  have hKLE : K.IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi => hzero i (by simp only [Set.mem_Icc]; omega)
  have hcomp : IsIso ((derivedPullbackComparison f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) :=
    isIso_derivedPullbackComparison_app_boundedAbove f hmos K ⟨b, hKLE⟩ hflat
  refine hasTorAmplitude_of_flatRepresentative T' _ a b ((pullbackComplex f).obj K)
    (fun i => isFlat_pullbackComplex_X f hmos (RingedToposSiteHom.pullbackPreservesIsFlat f) K
      hflat i)
    (fun i hi => Functor.map_isZero f.pullbackTopos (hzero i hi)) ?_
  refine ?_ ≪≫ (derivedPullback f).mapIso
    ((DerivedCategory.quotientCompQhIso
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).app K ≪≫ e)
  refine (DerivedCategory.Qh.mapIso
      ((f.pullbackTopos.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app K) ≪≫
    (DerivedCategory.quotientCompQhIso
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).app
      ((pullbackComplex f).obj K)).symm ≪≫ ?_
  exact (asIso ((derivedPullbackComparison f).app _)).symm

include hmos in
/-- **Stacks 08H5.**  The derived pullback along a morphism of ringed topoi preserves Tor
amplitude in a fixed interval.

A degenerate interval `b < a` says that the derived tensor products of `E` with every module
vanish in *every* degree, so in particular `E` has Tor amplitude in the one-point interval
`[i + 1, i + 1]` for whichever degree `i` is being examined, and
`hasTorAmplitude_derivedPullback_of_le` applies there. -/
@[stacks 08H5]
theorem hasTorAmplitude_derivedPullback
    (T : DerivedTensorProduct Y.toRingedSite) (T' : DerivedTensorProduct X.toRingedSite)
    (E : RingedSite.DerivedModules Y.toRingedSite) (a b : ℤ)
    (hamp : HasTorAmplitude T E a b) :
    HasTorAmplitude T' ((derivedPullback f).obj E) a b := by
  by_cases hab : a ≤ b
  · exact hasTorAmplitude_derivedPullback_of_le f hmos T T' E a b hab hamp
  · intro F i _
    have hamp' : HasTorAmplitude T E (i + 1) (i + 1) :=
      fun G j _ => hamp G j (by simp only [Set.mem_Icc]; omega)
    exact hasTorAmplitude_derivedPullback_of_le f hmos T T' E (i + 1) (i + 1) le_rfl hamp' F i
      (by simp only [Set.mem_Icc]; omega)

include hmos in
/-- **Finite Tor dimension is preserved by derived pullback**, Stacks 08H5 for the predicate of
Stacks 08FZ (2): an interval containing the Tor amplitude of `E` contains that of `Lf^* E`. -/
@[sga "6 I 5.6.1" "a)"]
theorem hasFiniteTorDimension_derivedPullback
    (T : DerivedTensorProduct Y.toRingedSite) (T' : DerivedTensorProduct X.toRingedSite)
    (E : RingedSite.DerivedModules Y.toRingedSite) (h : HasFiniteTorDimension T E) :
    HasFiniteTorDimension T' ((derivedPullback f).obj E) := by
  obtain ⟨a, b, hamp⟩ := h
  exact ⟨a, b, hasTorAmplitude_derivedPullback f hmos T T' E a b hamp⟩

end Stacks.SheafOfModules.DerivedTensorProduct

end
