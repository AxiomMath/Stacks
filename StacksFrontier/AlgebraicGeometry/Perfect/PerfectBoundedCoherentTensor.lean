module

public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.CoherentTorSheaves
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.PerfectBoundedCoherent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.BoundedBelowTensor
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PseudoCoherentAndFiniteTorDimension
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.BoundedBelowOnARingedSpace
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.LocalTorAmplitude
import StacksCore.Tactic.StacksAttribute

/-!
# The derived tensor product of a perfect object with a bounded coherent one

Let `X` be a Noetherian scheme. The derived tensor product carries
`D_perf(𝒪_X) × D^b_Coh(𝒪_X)` into `D^b_Coh(𝒪_X)`: tensoring a perfect object with a bounded
object with coherent cohomology sheaves gives again a bounded object with coherent cohomology
sheaves.

## Main results

* `Stacks.Cohomology.TorAmplitude.hasFiniteTorDimension_of_finite_cover`: an object of `D(𝒪_X)`
  whose restriction to each member of a *finite* open covering has finite Tor dimension has
  finite Tor dimension. The interval is the union of the finitely many local ones.
* `Stacks.Cohomology.TorAmplitude.hasFiniteTorDimension_of_isPerfect`: on a quasi-compact ringed
  space a perfect object of `D(𝒪_X)` has finite Tor dimension.
* `AlgebraicGeometry.derivedCategoryBBounded_derivedTensor_of_isPerfect`: **the closure fact**.
  On a Noetherian scheme the derived tensor product of a perfect object with an object of
  `D^b_Coh(𝒪_X)` lies in `D^b_Coh(𝒪_X)`.

## Implementation notes

Three of the four conditions to be checked are already available and are not reproved here.

* Coherence of every cohomology sheaf and the bound *above* are [Stacks, Tag 0AZS] part (2),
  `AlgebraicGeometry.TorFormula.derivedCategoryBMinus_derivedTensor`, applied to the two
  factors read in `D⁻_Coh(𝒪_X)`. A perfect object lies in `D^b_Coh(𝒪_X)` by [Stacks, Tag 0FXU],
  `Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect`, hence in
  `D⁻_Coh(𝒪_X)`; this is the only place perfectness of the first factor is used for coherence.
* The bound *below* is `Stacks.SheafOfModules.DerivedTensorProduct.isBoundedBelow_tensor_of_`
  `hasFiniteTorDimension`: a factor of finite Tor dimension shifts a lower bound of the other
  factor by the lower end of its Tor-amplitude interval. This is why the first factor has to be
  perfect and not merely bounded with coherent cohomology — on a singular scheme `D^b_Coh` is
  *not* closed under the derived tensor product.

What was missing is the *globalisation* of the Tor-amplitude interval. Perfectness gives finite
Tor dimension only locally (`Stacks.Cohomology.TorAmplitude.locallyHasFiniteTorDimension_of_`
`isPerfect`), with an interval depending on the member of the covering, while the bound below
needs one interval valid on all of `X`. A Noetherian scheme is quasi-compact, so finitely many
members of the covering suffice, and the union of their finitely many intervals is an interval:
that is `hasFiniteTorDimension_of_finite_cover`, whose only input is
`Stacks.Cohomology.TorAmplitude.hasTorAmplitude_of_iSup_eq_top`, the locality of Tor amplitude
in a *prescribed* interval.

The interval is enlarged to contain `0` as well as the finitely many local intervals, so that
the construction needs no case distinction on whether the finite subcovering is empty — which
it is exactly when `X` is empty.

The derived tensor product is the canonical one of [Stacks, Tag 06YU],
`Stacks.Cohomology.TorAmplitude.derTensor`, in the scheme spelling
`AlgebraicGeometry.TorFormula.derivedTensor`; this is the one Tag 0AZS and the Tor-amplitude
development are stated at. The derived category is the standard model, as in Tag 0AZS.

## References

* [Stacks Project, Tag 0FDK](https://stacks.math.columbia.edu/tag/0FDK)
* [Stacks Project, Tag 0AZS](https://stacks.math.columbia.edu/tag/0AZS)
* [Stacks Project, Tag 0FXU](https://stacks.math.columbia.edu/tag/0FXU)
* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open StrictlyPerfect

universe u d

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Cohomology.TorAmplitude

/-! ### Globalising a Tor-amplitude interval over a finite covering -/

/-- **An object of `D(𝒪_X)` of finite Tor dimension on each member of a finite open covering has
finite Tor dimension.** The finitely many local intervals, together with `0`, are contained in
one interval, and Tor amplitude in a prescribed interval is local on a covering. -/
theorem hasFiniteTorDimension_of_finite_cover (X : RingedSpace.{u, u})
    [HasDerivedCategory.{d} (OXMod.{u} X)] (E : DerivedCategory (OXMod.{u} X))
    {ι : Type*} [Finite ι] (V : ι → Opens X) (hV : iSup V = ⊤)
    (h : ∀ i : ι, HasFiniteTorDimension (X.restrict (V i).isOpenEmbedding)
      ((X.derivedRestrictModules (V i)).obj E)) :
    HasFiniteTorDimension X E := by
  have hA : ∀ i : ι, HasTorAmplitude (X.restrict (V i).isOpenEmbedding)
      ((X.derivedRestrictModules (V i)).obj E) (h i).choose (h i).choose_spec.choose :=
    fun i => (h i).choose_spec.choose_spec
  obtain ⟨a, ha⟩ := Finite.exists_ge fun i : ι => (h i).choose
  obtain ⟨b, hb⟩ := Finite.exists_le fun i : ι => (h i).choose_spec.choose
  exact ⟨a, b, hasTorAmplitude_of_iSup_eq_top X E a b V hV fun i F n hn =>
    hA i F n fun hmem => hn ⟨le_trans (ha i) hmem.1, le_trans hmem.2 (hb i)⟩⟩

/-- **A perfect object of `D(𝒪_X)` on a quasi-compact ringed space has finite Tor dimension.**
Perfectness gives a covering on which the object has finite Tor dimension; quasi-compactness
refines it to a finite one, over which the interval globalises. -/
theorem hasFiniteTorDimension_of_isPerfect (X : RingedSpace.{u, u})
    [HasDerivedCategory.{d} (OXMod.{u} X)] [CompactSpace X]
    (E : DerivedCategory (OXMod.{u} X))
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect E) :
    HasFiniteTorDimension X E := by
  classical
  obtain ⟨I, U, hsup, hfd⟩ :=
    @locallyHasFiniteTorDimension_of_isPerfect X _ (fun _ => HasDerivedCategory.standard _) E hE
  obtain ⟨t, ht⟩ := (isCompact_univ (X := X)).elim_finite_subcover
    (fun i : I => (U i : Set X)) (fun i => (U i).isOpen) (by
      intro x _
      exact Set.mem_iUnion.mpr (TopologicalSpace.Opens.mem_iSup.mp
        (show x ∈ iSup U from by rw [hsup]; trivial)))
  have hsup' : iSup (fun i : {x : I // x ∈ t} => U i.1) = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨i, hit, hx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, hit⟩, hx⟩
  exact hasFiniteTorDimension_of_finite_cover X E (fun i : {x : I // x ∈ t} => U i.1) hsup'
    fun i => hfd i.1

end Stacks.Cohomology.TorAmplitude

namespace AlgebraicGeometry

/-! ### The closure of `D^b_Coh` under tensoring with a perfect object -/

/-- **The derived tensor product of a perfect object with one of `D^b_Coh(𝒪_X)` lies in
`D^b_Coh(𝒪_X)`.** Let `X` be a Noetherian scheme. Coherence of the cohomology sheaves and the
bound above are [Stacks, Tag 0AZS] part (2) applied in `D⁻_Coh(𝒪_X)`, a perfect object lying
there by [Stacks, Tag 0FXU]; the bound below is the finite Tor dimension of the perfect factor.

Coherence is read at `SheafOfModules.IsCoherent` here;
`AlgebraicGeometry.derivedCategoryBBounded_coherentModules_derivedTensor_of_isPerfect` is the
same statement at `Stacks.SheafOfModules.IsCoherent`, the class [Stacks, Tag 0FDF] uses. -/
@[sga "6 I 5.3" "special case"]
theorem derivedCategoryBBounded_derivedTensor_of_isPerfect (X : Scheme.{u}) [IsNoetherian X]
    (K L : DerivedCategory X.Modules)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) K)
    (hL : DerivedCategoryB.derivedCategoryBBounded (fun F : X.Modules => F.IsCoherent) L) :
    DerivedCategoryB.derivedCategoryBBounded (fun F : X.Modules => F.IsCoherent)
      (((TorFormula.derivedTensor X).obj K).obj L) := by
  have hKb := Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect X K hK
  have hMinus := TorFormula.derivedCategoryBMinus_derivedTensor X K L
    ⟨hKb.1.2, hKb.2⟩ ⟨hL.1.2, hL.2⟩
  have hfin : Stacks.Cohomology.TorAmplitude.HasFiniteTorDimension X.toRingedSpace K :=
    Stacks.Cohomology.TorAmplitude.hasFiniteTorDimension_of_isPerfect X.toRingedSpace K hK
  have hbelow : DerivedCategoryB.IsBoundedBelow (((TorFormula.derivedTensor X).obj K).obj L) :=
    Stacks.SheafOfModules.DerivedTensorProduct.isBoundedBelow_tensor_of_hasFiniteTorDimension
      (Stacks.Cohomology.TorAmplitude.derTensorSite X.toRingedSpace) K L hfin hL.1.1
  exact ⟨⟨hbelow, hMinus.1⟩, hMinus.2⟩

end AlgebraicGeometry

end
