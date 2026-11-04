module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Fibres.ReducedFibreLocus
public import StacksFrontier.AlgebraicGeometry.FlatGoodDiagram.FlatModel
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibre.ProperOverDvr
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.DenseFlatLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Reduced
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Reduction
public import StacksFrontier.AlgebraicGeometry.ProperLimitStage.SeparatedModel
public import StacksFrontier.AlgebraicGeometry.Properties.DiscreteValuation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.GeometricallyReducedLocus
public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.ReducedTFAE
public import StacksFrontier.Topology.Constructible.NormalForm
public import StacksFrontier.Topology.Specialization.Constructible
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Openness of the geometrically reduced fibre locus

Let `f : X ⟶ Y` be a flat proper morphism of finite presentation. The points of `Y` whose fibre
is geometrically reduced form an open subset of `Y`.

Without flatness and properness the locus need not be open, but it is still large near a generic
point: for a morphism of finite presentation onto an irreducible scheme whose fibre over the
generic point is geometrically reduced, the locus contains a nonempty open subscheme of the base,
over which the morphism therefore has geometrically reduced fibres.

The locus is compatible with base change, so the statement is local on `Y` and reduces to an
affine base; over an affine base it reduces further to an affine *Noetherian* one, a flat proper
morphism of finite presentation over `Spec R` being the base change of such a morphism over
`Spec R₀` for a subring `R₀ ⊆ R` of finite type over `ℤ`. Over a Noetherian base the locus is
constructible, because geometric reducedness of the fibres is local on the source and
constructible for a morphism of affine schemes, and a constructible set is open as soon as it is
stable under generalization.

Stability under generalization is tested along a discrete valuation ring. A strict specialization
in the base is realized by a morphism from the spectrum of a discrete valuation ring whose
generic residue field is prescribed; flatness makes every irreducible component of the pullback
dominate that spectrum, so reducedness of the special fibre propagates to the generic fibre by
[Stacks, Tag 0C0D], and the geometric reducedness criterion over a purely inseparable finite
extension turns this into geometric reducedness at the generic point.

## Main results

* `AlgebraicGeometry.isOpen_geometricallyReduced_fiber`: the locus of points of the base whose
  fibre is geometrically reduced is open.
* `AlgebraicGeometry.isLocallyConstructible_geometricallyReduced_fiber`: for a quasi-compact
  morphism locally of finite presentation — no flatness, no properness — that locus is locally
  constructible, which is Stacks 0579.
* `AlgebraicGeometry.exists_opens_nonempty_geometricallyReduced_morphismRestrict_of_finiteType`:
  **Stacks 0578.** For a morphism of finite type onto an irreducible base whose fibre over the
  generic point is geometrically reduced, a nonempty open subscheme of the base over which the
  fibres are all geometrically reduced.
* `AlgebraicGeometry.exists_opens_nonempty_geometricallyReduced_morphismRestrict`: the same for a
  morphism of finite presentation, which is the case the constructibility of the locus settles
  directly and from which the finite type statement is deduced.
* `exists_opens_nonempty_geometricallyReduced_morphismRestrict_of_locallyOfFiniteType`
  (in `AlgebraicGeometry`): the finite type statement read off over a locally Noetherian base,
  where finite type and finite presentation agree outright.

## Implementation notes

Finite presentation is carried as the explicit hypothesis `AlgebraicGeometry.FinitePresentation`,
the conjunction of `AlgebraicGeometry.LocallyOfFinitePresentation`,
`AlgebraicGeometry.QuasiCompact` and `AlgebraicGeometry.QuasiSeparated`, rather than as three
instance arguments.

The fibre over `y : Y` is `f.fiberToSpecResidueField y`, a morphism to the spectrum of the residue
field of `y`, so geometric reducedness of the fibre is relative to that field.

[Stacks, Tag 0579] is available for a morphism of *affine* schemes
(`AlgebraicGeometry.isLocallyConstructible_geometricallyReduced_fiber_of_isAffine`); the case
needed here, a morphism of finite presentation from a quasi-compact scheme to an affine
Noetherian one, is obtained from it by the locality of geometric reducedness on the source.

Stacks 0579 itself is proved here in the generality of its statement, for a quasi-compact
morphism locally of finite presentation: the Noetherian-free affine-base case above is read on
each affine open of the target through the restriction `f ∣_ U`, whose locus is the inverse image
of the locus of `f` by Stacks 0576, and local constructibility is exactly constructibility on
every affine open. Its two hypotheses are therefore carried as instances: the source assumes
nothing about quasi-separatedness, and none is needed, each member of the finite affine cover of
the source being affine over the affine base by itself.

For Stacks 0578 the Noetherian hypothesis has to go, because the source assumes nothing about
the base; the input there is the Noetherian-free affine case
`AlgebraicGeometry.isLocallyConstructible_geometricallyReduced_fiber_of_isAffine_source`, again
combined with locality on the source. Once the locus is constructible on an affine open
neighbourhood of the generic point, no geometry is left: a constructible set containing the
generic point of an irreducible space contains a nonempty open set, since in the normal form of
Stacks 005G(1) the piece `U ∩ Vᶜ` holding the generic point has `V` an open set missing a point
whose closure is everything, so `V` is empty and the piece is the open set `U`.

Stacks 0578 asks only that `f` be of finite type, and that is how it is stated here. The step
down to the finite presentation case is the source's own bridge through Stacks 052A, run in two
moves. First the base is replaced by its reduction `Y_red ⟶ Y`, a universal homeomorphism by
Stacks 054M, which therefore matches the opens, the irreducibility and the generic point of `Y`;
by Stacks 0576 the geometrically reduced fibre locus of the base change to `Y_red` is the inverse
image of that of `f`, so it suffices to produce a nonempty open of `Y_red` inside the former.
Second, the base being now *reduced*, generic flatness
`AlgebraicGeometry.exists_dense_open_flat_finitePresentation_structureSheaf` — Stacks 052B read
for the structure sheaf of the source, of which Stacks 052A is the integral-base case — gives a
dense open `U ⊆ Y_red` over which the base change is of finite presentation. Density puts the
generic point in `U`, so the finite presentation case applies over `U`, and the open set it
produces is carried back to `Y` by the open immersion of `U` followed by the homeomorphism.

The locus form of the finite presentation case, which is what that transport consumes, is
`exists_opens_mem_subset_setOf_geometricallyReduced_fiber_of_finitePresentation`: it returns an
open neighbourhood of the generic point contained in the locus, rather than geometric reducedness
of a restricted morphism. Turning the one into the other is
`geometricallyReduced_morphismRestrict_of_subset_setOf`, which is Stacks 0576 once more.

## References

* [Stacks Project, Tag 0C0E](https://stacks.math.columbia.edu/tag/0C0E)
* [Stacks Project, Tag 0C0D](https://stacks.math.columbia.edu/tag/0C0D)
* [Stacks Project, Tag 0578](https://stacks.math.columbia.edu/tag/0578)
* [Stacks Project, Tag 0579](https://stacks.math.columbia.edu/tag/0579)
* [Stacks Project, Tag 005G](https://stacks.math.columbia.edu/tag/005G)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace AlgebraicGeometry

section

/-- **Geometric reducedness is local on the source.** A morphism is geometrically reduced exactly
when its restriction to each member of an open cover of the source is. -/
private theorem geometricallyReduced_iff_forall_openCover {X Y : Scheme.{u}} (f : X ⟶ Y)
    (𝒰 : X.OpenCover) :
    GeometricallyReduced f ↔ ∀ i, GeometricallyReduced (𝒰.f i ≫ f) := by
  simp only [geometricallyReduced_iff, geometrically_iff_of_isClosedUnderIsomorphisms]
  refine ⟨fun h i K _ y => ?_, fun h K _ y => ?_⟩
  · have : IsReduced (pullback f y) := h K y
    have : IsOpenImmersion (pullback.snd (𝒰.f i) (pullback.fst f y)) :=
      MorphismProperty.pullback_snd _ _ inferInstance
    exact ObjectProperty.prop_of_iso IsReduced (pullbackRightPullbackFstIso f y (𝒰.f i))
      (isReduced_of_isOpenImmersion (pullback.snd (𝒰.f i) (pullback.fst f y)))
  · have : ∀ i, IsReduced ((𝒰.pullback₂ (pullback.fst f y)).X i) := fun i =>
      ObjectProperty.prop_of_iso IsReduced (pullbackRightPullbackFstIso f y (𝒰.f i)).symm
        (h i K y)
    exact IsReduced.of_openCover _ (𝒰.pullback₂ (pullback.fst f y))

/-- **The geometrically reduced fibre locus is local on the source.** The fibre of `f` at `y` is
geometrically reduced exactly when the fibre at `y` of each restriction of `f` to a member of an
open cover of the source is. -/
private theorem geometricallyReduced_fiber_iff_forall_openCover {X Y : Scheme.{u}} (f : X ⟶ Y)
    (𝒰 : X.OpenCover) (y : Y) :
    GeometricallyReduced (f.fiberToSpecResidueField y) ↔
      ∀ i, GeometricallyReduced ((𝒰.f i ≫ f).fiberToSpecResidueField y) := by
  have : MorphismProperty.RespectsIso (@GeometricallyReduced : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  rw [geometricallyReduced_iff_forall_openCover (f.fiberToSpecResidueField y)
    (𝒰.pullback₂ (pullback.fst f (Y.fromSpecResidueField y)))]
  refine forall_congr' fun i => ?_
  have harrow : Arrow.mk ((𝒰.pullback₂ (pullback.fst f (Y.fromSpecResidueField y))).f i ≫
      f.fiberToSpecResidueField y) ≅ Arrow.mk ((𝒰.f i ≫ f).fiberToSpecResidueField y) := by
    refine Arrow.isoMk (pullbackRightPullbackFstIso f (Y.fromSpecResidueField y) (𝒰.f i))
      (Iso.refl _) ?_
    show (pullbackRightPullbackFstIso f (Y.fromSpecResidueField y) (𝒰.f i)).hom ≫
        pullback.snd (𝒰.f i ≫ f) (Y.fromSpecResidueField y) =
      (pullback.snd (𝒰.f i) (pullback.fst f (Y.fromSpecResidueField y)) ≫
        pullback.snd f (Y.fromSpecResidueField y)) ≫ 𝟙 _
    simp
  exact MorphismProperty.arrow_mk_iso_iff (P := @GeometricallyReduced) harrow

/-- The geometrically reduced fibre locus is the intersection of the loci of the restrictions to
the members of a finite affine cover of the source. -/
private theorem geometricallyReduced_fiber_set_eq_iInter_finiteSubcover {X S : Scheme.{u}}
    (f : X ⟶ S) [CompactSpace X] :
    {y : S | GeometricallyReduced (f.fiberToSpecResidueField y)} =
      ⋂ i, {y : S |
        GeometricallyReduced ((X.affineCover.finiteSubcover.f i ≫ f).fiberToSpecResidueField y)} :=
  Set.ext fun y => by
    simpa using geometricallyReduced_fiber_iff_forall_openCover f X.affineCover.finiteSubcover y

/-- The geometrically reduced fibre locus of a restriction `f ∣_ U` is the inverse image of the
locus of `f`, by Stacks 0576. -/
private theorem geometricallyReduced_fiber_set_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) :
    {z : (U : Scheme.{u}) | GeometricallyReduced ((f ∣_ U).fiberToSpecResidueField z)} =
      U.ι ⁻¹' {y : Y | GeometricallyReduced (f.fiberToSpecResidueField y)} :=
  geometricallyReduced_fiber_set_eq_preimage_of_isPullback f (f ∣_ U) (f ⁻¹ᵁ U).ι U.ι
    (isPullback_morphismRestrict f U).flip

/-- **[Stacks, Tag 0579] over an affine Noetherian base.** For a morphism of finite presentation
onto an affine locally Noetherian scheme, the locus of points whose fibre is geometrically reduced
is locally constructible. -/
@[ega "IV 9.7.7" "(iii), special case"]
private theorem isLocallyConstructible_geometricallyReduced_fiber_of_isAffine_target
    {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine S] [IsLocallyNoetherian S]
    (hf : FinitePresentation f) :
    IsLocallyConstructible {y : S | GeometricallyReduced (f.fiberToSpecResidueField y)} := by
  have : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
  have : QuasiCompact f := hf.quasiCompact
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  rw [geometricallyReduced_fiber_set_eq_iInter_finiteSubcover f]
  refine IsLocallyConstructible.iInter fun i => ?_
  exact isLocallyConstructible_geometricallyReduced_fiber_of_isAffine _
    ⟨inferInstance, inferInstance, inferInstance⟩

/-- **A flat proper morphism of finite presentation over an affine base has a Noetherian model.**
It is the base change of a flat proper morphism of finite presentation over the spectrum of a
Noetherian ring, namely a subring of finite type over `ℤ` of the base ring. -/
@[ega "IV 11.2.7" "a⇒b for proper f"]
private theorem exists_flat_isProper_noetherian_model {Y : Scheme.{u}} (R : CommRingCat.{u})
    (f : Y ⟶ Spec R) [Flat f] [IsProper f] (hfp : FinitePresentation f) :
    ∃ (R₀ : CommRingCat.{u}) (X₀ : Scheme.{u}) (g : Spec R ⟶ Spec R₀) (f₀ : X₀ ⟶ Spec R₀),
      IsNoetherianRing R₀ ∧ FinitePresentation f₀ ∧ Flat f₀ ∧ IsProper f₀ ∧
        Nonempty (Over.mk f ≅ (Over.pullback g).obj (Over.mk f₀)) := by
  let D := specAdjoinFinsetDiagram (R : Type u)
  let c := specAdjoinFinsetCone (R : Type u)
  have hc : IsLimit c := isLimit_specAdjoinFinsetCone (R : Type u)
  have hproperMk : IsProper (Over.mk f).hom := ‹IsProper f›
  obtain ⟨j, Z, hfpZ, hproperZ, ⟨e⟩⟩ :=
    @exists_isProper_model_baseChange_specAdjoinFinsetDiagram (R : Type u) _ (Over.mk f)
      hproperMk hfp
  have : LocallyOfFinitePresentation Z.hom := hfpZ.locallyOfFinitePresentation
  have : QuasiCompact Z.hom := hfpZ.quasiCompact
  have : QuasiSeparated Z.hom := hfpZ.quasiSeparated
  have : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  have : QuasiSeparatedSpace Z.left := quasiSeparatedSpace_of_quasiSeparated Z.hom
  have : CompactSpace (Over.mk (𝟙 (D.obj j))).left := inferInstanceAs (CompactSpace (D.obj j))
  have : QuasiSeparatedSpace (Over.mk (𝟙 (D.obj j))).left :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj j))
  let t : Z ⟶ Over.mk (𝟙 (D.obj j)) := Over.homMk Z.hom (Category.comp_id Z.hom)
  have : LocallyOfFinitePresentation t.left :=
    inferInstanceAs (LocallyOfFinitePresentation Z.hom)
  have : MorphismProperty.RespectsIso (@Flat : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : Flat ((Over.pullback (c.π.app j)).map t).left :=
    (flat_overPullback_terminal_iff _ Z).mpr
      (prop_of_overIso (@Flat) e (show Flat (Over.mk f).hom from ‹Flat f›))
  obtain ⟨k, a, hflat⟩ :=
    exists_flat_baseChange_of_limitBaseChange D c j Z (Over.mk (𝟙 (D.obj j))) t hc
  have hfpZ' : FinitePresentation ((Over.pullback (D.map a)).obj Z).hom :=
    finitePresentation_overPullbackObj _ Z hfpZ
  have hproperZ' : IsProper ((Over.pullback (D.map a)).obj Z).hom := by
    have : IsProper Z.hom := hproperZ
    show IsProper (pullback.snd Z.hom (D.map a))
    infer_instance
  exact ⟨CommRingCat.of (Algebra.adjoin ℤ ((k.unop : Finset (R : Type u)) : Set (R : Type u))),
    ((Over.pullback (D.map a)).obj Z).left, c.π.app k, ((Over.pullback (D.map a)).obj Z).hom,
    isNoetherianRing_adjoinFinset_int _ k.unop, hfpZ',
    (flat_overPullback_terminal_iff _ Z).mp hflat, hproperZ',
    ⟨e ≪≫ overPullbackObj_shiftIso D c a Z⟩⟩

/-- A scheme geometrically reduced over a field is reduced. -/
private theorem isReduced_of_geometricallyReduced_over_field {k : Type u} [Field k]
    {Z : Scheme.{u}} (g : Z ⟶ Spec (.of k))
    (hg : GeometricallyReduced g) : IsReduced Z := by
  have hgeom : geometrically IsReduced g := by
    rwa [← GeometricallyReduced.eq_geometrically]
  have hpb : IsReduced (pullback g (𝟙 (Spec (.of k)))) :=
    (geometrically_iff_of_isClosedUnderIsomorphisms.mp hgeom) k (𝟙 _)
  have : IsIso (pullback.fst g (𝟙 (Spec (.of k)))) := by infer_instance
  exact ObjectProperty.prop_of_iso IsReduced (asIso (pullback.fst g (𝟙 _))) hpb

/-- Every irreducible component of a scheme flat over a discrete valuation ring dominates the
base: its generic point has no proper generalization, so it must lie over the generic point. -/
@[ega "IV 1.10.4" "b) ⇒ c), special case",
  ega "IV 12.2.1.1" "special case",
  ega "IV 14.2.3" "special case",
  ega "IV 2.3.4" "(iii), special case",
  sga "3 X 5.14.0" "special case",
  sga "7 VIII 5.2" "special case"]
private theorem flat_irreducibleComponent_dense_over_dvr
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [Flat f]
    (Z : Set X) (hZ : Z ∈ irreducibleComponents X) : Dense (f '' Z) := by
  let c : irreducibleComponents X := ⟨Z, hZ⟩
  let ξ : X := genericPoints.ofComponent c
  have hξZ : ξ ∈ Z := (genericPoints.isGenericPoint_ofComponent c).mem
  have hξgeneric : IsGenericPoint ξ Z := genericPoints.isGenericPoint_ofComponent c
  have hnoGeneralization (z : X) (hz : z ⤳ ξ) : z = ξ := by
    have hsub : closure ({ξ} : Set X) ⊆ closure ({z} : Set X) :=
      specializes_iff_closure_subset.mp hz
    have hmax : closure ({z} : Set X) ⊆ Z := by
      apply hZ.2 isIrreducible_singleton.closure
      simpa only [hξgeneric.def] using hsub
    have hzZ : z ∈ Z := hmax (subset_closure (by simp))
    have hreverse : ξ ⤳ z := specializes_iff_mem_closure.mpr (hξgeneric.def.symm ▸ hzZ)
    exact (hz.antisymm hreverse).eq
  have hη_image : (⟨⊥, inferInstance⟩ : Spec (.of R)) ∈ f '' Z := by
    let η : Spec (.of R) := ⟨⊥, inferInstance⟩
    have hηne : η ≠ IsLocalRing.closedPoint (CommRingCat.of R) := by
      obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
      intro heq
      have hIdealEq : (⊥ : Ideal R) = IsLocalRing.maximalIdeal R :=
        congrArg (fun z : Spec (.of R) => z.asIdeal) heq
      have hπmax : π ∈ IsLocalRing.maximalIdeal R := by
        rw [hπ.maximalIdeal_eq]
        exact Ideal.subset_span (by simp)
      exact hπ.ne_zero (Ideal.mem_bot.mp (hIdealEq ▸ hπmax))
    have hfx : f ξ = η := by
      rcases IsLocalRing.Ring.KrullDimLE.eq_bot_or_eq_top (f ξ : PrimeSpectrum R) with hbot | htop
      · exact congrArg (fun z : PrimeSpectrum R => (z : Spec (.of R))) hbot
      · have hclosed : f ξ = IsLocalRing.closedPoint (CommRingCat.of R) := by
          have htop' : (⊤ : PrimeSpectrum R) = IsLocalRing.closedPoint (CommRingCat.of R) := rfl
          exact congrArg (fun z : PrimeSpectrum R => (z : Spec (.of R))) (htop.trans htop')
        have hηspec : η ⤳ f ξ := by
          rw [hclosed]
          show (⊥ : PrimeSpectrum R) ⤳ _
          exact (PrimeSpectrum.le_iff_specializes _ _).mp bot_le
        obtain ⟨z, hz, hfz⟩ := Flat.generalizingMap f hηspec
        obtain rfl := hnoGeneralization z hz
        exact (hηne (hfz.symm.trans hclosed)).elim
    exact ⟨ξ, hξZ, hfx⟩
  rw [dense_iff_closure_eq]
  ext y
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  · let η : Spec (.of R) := ⟨⊥, inferInstance⟩
    rcases IsLocalRing.Ring.KrullDimLE.eq_bot_or_eq_top (y : PrimeSpectrum R) with hbot | htop
    · have hy : y = η := congrArg (fun z : PrimeSpectrum R => (z : Spec (.of R))) hbot
      rw [hy]
      exact subset_closure hη_image
    · have hclosed : y = IsLocalRing.closedPoint (CommRingCat.of R) := by
        have htop' : (⊤ : PrimeSpectrum R) = IsLocalRing.closedPoint (CommRingCat.of R) := rfl
        exact congrArg (fun z : PrimeSpectrum R => (z : Spec (.of R))) (htop.trans htop')
      rw [hclosed]
      have hηclosed : η ⤳ IsLocalRing.closedPoint (CommRingCat.of R) := by
        show (⊥ : PrimeSpectrum R) ⤳ _
        exact (PrimeSpectrum.le_iff_specializes _ _).mp bot_le
      exact closure_mono (Set.singleton_subset_iff.mpr hη_image)
        (specializes_iff_mem_closure.mp hηclosed)

/-- The geometrically reduced fibre locus of a flat proper morphism over a Noetherian affine base
is stable under generalization. -/
private theorem stableUnderGeneralization_geometricallyReduced_fiber
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [Flat f] [IsProper f] :
    StableUnderGeneralization
      {y : Spec (.of R) | GeometricallyReduced (f.fiberToSpecResidueField y)} := by
  intro x y hxy hy
  by_cases hEq : x = y
  · simpa [hEq] using hy
  · by_contra hGeom
    let k := (Spec (.of R)).residueField y
    let F := f.fiberToSpecResidueField y
    let p := ringExpChar k
    let K := AlgebraicClosure k
    let kperf := perfectClosure k K
    let tfae := AlgebraicGeometry.geometricallyReduced_tfae k p F kperf K
    have hnot : ¬ GeometricallyReduced F := by
      simpa [F] using hGeom
    have hbad : ¬ ∀ (L : Type u) (hField : Field L) (hAlg : Algebra k L)
        (hDim : FiniteDimensional k L) (hPure : IsPurelyInseparable k L),
        IsReduced (pullback F (Spec.map (CommRingCat.ofHom (algebraMap k L)))) :=
      fun hgood => hnot ((tfae.out 1 3).mpr hgood)
    push Not at hbad
    obtain ⟨L, hField, hAlg, hDim, hPure, hL⟩ := hbad
    let : Field L := hField
    let : Algebra k L := hAlg
    let : FiniteDimensional k L := hDim
    let : IsPurelyInseparable k L := hPure
    have : Algebra.EssFiniteType k L := inferInstance
    obtain ⟨A, hCommA, hDomA, hDvrA, q, hqη, hqclosed, e, he⟩ :=
      AlgebraicGeometry.exists_dvr_morphism_of_specializes_with_residueField_equiv
        (X := Spec (.of R)) hxy hEq L
    subst y
    let : CommRing A := hCommA
    let : IsDomain A := hDomA
    let : IsDiscreteValuationRing A := hDvrA
    let fR := pullback.snd f q
    have hpull : IsPullback (pullback.fst f q) fR f q := .of_hasPullback f q
    have hlocus := AlgebraicGeometry.geometricallyReduced_fiber_set_eq_preimage_of_isPullback
      f fR (pullback.fst f q) q hpull
    have hclosedGeom : IsLocalRing.closedPoint A ∈
        {z : Spec (.of A) | GeometricallyReduced (fR.fiberToSpecResidueField z)} := by
      rw [hlocus]
      show GeometricallyReduced (f.fiberToSpecResidueField (q (IsLocalRing.closedPoint A)))
      rw [hqclosed]
      exact hy
    have : IsReduced (fR.fiber (IsLocalRing.closedPoint A)) :=
      isReduced_of_geometricallyReduced_over_field
        (fR.fiberToSpecResidueField (IsLocalRing.closedPoint A)) hclosedGeom
    let η : Spec (.of A) := genericPoint (Spec (.of A))
    let X' : Scheme.{u} := pullback f q
    have hcomponents : ∀ Z ∈ irreducibleComponents X', Dense (fR '' Z) := fun Z hZ =>
      flat_irreducibleComponent_dense_over_dvr (X := X') fR Z hZ
    have hred :=
      AlgebraicGeometry.isReduced_genericFiber_of_isProper_over_dvr_of_isReduced_specialFiber
        (f := fR) hcomponents
    have hredη : IsReduced (fR.fiber η) := by
      show IsReduced (fR.fiber (genericPoint (Spec (.of A))))
      rw [genericPoint_eq_bot_of_affine (CommRingCat.of A)]
      exact hred
    let κ := (Spec (.of A)).residueField η
    let ρ : k ⟶ κ := q.residueFieldMap η
    let gρ : Spec (.of κ) ⟶ Spec (.of k) := Spec.map ρ
    let gL : Spec (.of L) ⟶ Spec (.of k) :=
      Spec.map (CommRingCat.ofHom (algebraMap k L))
    let ie : Spec (.of L) ⟶ Spec (.of κ) :=
      Spec.map e.toCommRingCatIso.hom
    have : IsIso ie := by dsimp [ie]; infer_instance
    have hfield : (CommRingCat.ofHom (algebraMap k L)) = ρ ≫ e.toCommRingCatIso.hom := by
      apply CommRingCat.hom_ext
      ext a
      simpa [k, ρ] using (he a).symm
    have hbase : gL = ie ≫ gρ := by
      show Spec.map (CommRingCat.ofHom (algebraMap k L)) =
        Spec.map e.toCommRingCatIso.hom ≫ Spec.map ρ
      rw [← Spec.map_comp]
      simpa [k, ρ] using congrArg Spec.map hfield
    have hpullGeneric := isPullback_fiberToSpecResidueField_of_isPullback hpull η
    have hgenericIso : fR.fiber η ≅ pullback F gρ := hpullGeneric.isoPullback
    have hredρ : IsReduced (pullback F gρ) :=
      ObjectProperty.prop_of_iso IsReduced hgenericIso hredη
    let m : pullback F gL ⟶ pullback F gρ :=
      pullback.map F gL F gρ (𝟙 _) ie (𝟙 _) (by simp) (by
        simpa [gL, gρ] using hbase)
    have : IsIso m := by dsimp [m]; infer_instance
    have hredL : IsReduced (pullback F gL) :=
      ObjectProperty.prop_of_iso IsReduced (asIso m).symm hredρ
    exact hL hredL

/-- The geometrically reduced fibre locus is invariant under an isomorphism of schemes over the
base. -/
private theorem fiber_geometricallyReduced_iff_of_over_iso {Y X X' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y} (e : Over.mk f ≅ Over.mk f') (y : Y) :
    GeometricallyReduced (f.fiberToSpecResidueField y) ↔
      GeometricallyReduced (f'.fiberToSpecResidueField y) := by
  let e₁ := (Over.pullback (Y.fromSpecResidueField y)).mapIso e
  have eArrow : Arrow.mk (f.fiberToSpecResidueField y) ≅
      Arrow.mk (f'.fiberToSpecResidueField y) := by
    refine Arrow.isoMk ((Over.forget _).mapIso e₁) (Iso.refl _) ?_
    show e₁.hom.left ≫ _ = _
    exact e₁.hom.w
  rw [GeometricallyReduced.eq_geometrically]
  exact MorphismProperty.arrow_mk_iso_iff (P := geometrically IsReduced) eArrow

/-- The geometrically reduced fibre locus is transported by an isomorphism of the base. -/
private theorem fiber_geometricallyReduced_iff_of_target_iso {X Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (e : Y ≅ Y') (y : Y) :
    GeometricallyReduced (f.fiberToSpecResidueField y) ↔
      GeometricallyReduced ((f ≫ e.hom).fiberToSpecResidueField (e.hom y)) := by
  let g := f ≫ e.hom
  let pb := pullback.snd g e.hom
  let eover : Over.mk pb ≅ Over.mk f := by
    let a := pullback.fst g e.hom
    have : IsIso a := inferInstance
    refine Over.isoMk (asIso a) ?_
    apply (cancel_mono e.hom).1
    simpa [g, Category.assoc] using (pullback.condition (f := g) (g := e.hom))
  have hpb := fiber_geometricallyReduced_iff_of_over_iso eover y
  have hbase := AlgebraicGeometry.geometricallyReduced_fiber_set_eq_preimage_of_isPullback
    g pb (pullback.fst g e.hom) e.hom (IsPullback.of_hasPullback g e.hom)
  have hbase' : GeometricallyReduced (pb.fiberToSpecResidueField y) ↔
      GeometricallyReduced (g.fiberToSpecResidueField (e.hom y)) := by
    simpa using congrArg (fun E => y ∈ E) hbase
  exact hpb.symm.trans hbase'

/-- Over a Noetherian affine base the locus is constructible and stable under generalization,
hence open. -/
private theorem isOpen_geometricallyReduced_fiber_of_isNoetherianRing
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [Flat f] [IsProper f]
    (hfp : FinitePresentation f) :
    IsOpen {y : Spec (CommRingCat.of R) |
      GeometricallyReduced (f.fiberToSpecResidueField y)} := by
  have hcon : IsConstructible
      {y : Spec (CommRingCat.of R) | GeometricallyReduced (f.fiberToSpecResidueField y)} :=
    (isLocallyConstructible_geometricallyReduced_fiber_of_isAffine_target f hfp).isConstructible
  exact isOpen_of_stableUnderGeneralization_of_isConstructible _ _ hcon
    (stableUnderGeneralization_geometricallyReduced_fiber f)

/-- Over an affine base the locus is the preimage of the locus of a Noetherian model, hence
open. -/
private theorem isOpen_geometricallyReduced_fiber_spec
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [IsProper f] (hfp : FinitePresentation f) :
    IsOpen {y : Spec (CommRingCat.of R) |
      GeometricallyReduced (f.fiberToSpecResidueField y)} := by
  obtain ⟨R₀, X₀, g, f₀, hRing₀, hfp₀, hflat₀, hproper₀, ⟨e⟩⟩ :=
    exists_flat_isProper_noetherian_model (CommRingCat.of R) f hfp
  let : IsNoetherianRing R₀ := hRing₀
  let : Flat f₀ := hflat₀
  let : IsProper f₀ := hproper₀
  have hopen₀ := isOpen_geometricallyReduced_fiber_of_isNoetherianRing f₀ hfp₀
  have heq : {y : Spec (CommRingCat.of R) |
      GeometricallyReduced (f.fiberToSpecResidueField y)} =
      g ⁻¹' {z : Spec R₀ | GeometricallyReduced (f₀.fiberToSpecResidueField z)} := by
    ext y
    have hp := AlgebraicGeometry.geometricallyReduced_fiber_set_eq_preimage_of_isPullback
      f₀ (pullback.snd f₀ g) (pullback.fst f₀ g) g (IsPullback.of_hasPullback f₀ g)
    have hbc : GeometricallyReduced ((pullback.snd f₀ g).fiberToSpecResidueField y) ↔
        GeometricallyReduced (f₀.fiberToSpecResidueField (g y)) := by
      simpa using congrArg (fun E => y ∈ E) hp
    show GeometricallyReduced (f.fiberToSpecResidueField y) ↔
      GeometricallyReduced (f₀.fiberToSpecResidueField (g y))
    exact (fiber_geometricallyReduced_iff_of_over_iso e y).trans hbc
  rw [heq]
  exact hopen₀.preimage g.continuous

/-- Over an affine base the locus is open, by transporting the statement along the isomorphism
with the spectrum of the global sections. -/
@[ega "IV 12.2.4" "clause (v), affine base"]
private theorem isOpen_geometricallyReduced_fiber_of_isAffine
    {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y) [Flat f] [IsProper f]
    (hfp : FinitePresentation f) :
    IsOpen {y : Y | GeometricallyReduced (f.fiberToSpecResidueField y)} := by
  have : LocallyOfFinitePresentation f := hfp.locallyOfFinitePresentation
  have : QuasiCompact f := hfp.quasiCompact
  have : QuasiSeparated f := hfp.quasiSeparated
  have hfpSpec : FinitePresentation (f ≫ Y.isoSpec.hom) :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  have hopen := isOpen_geometricallyReduced_fiber_spec (f ≫ Y.isoSpec.hom) hfpSpec
  have heq : {y : Y | GeometricallyReduced (f.fiberToSpecResidueField y)} =
      Y.isoSpec.hom ⁻¹' {z : Spec (CommRingCat.of Γ(Y, ⊤)) |
        GeometricallyReduced ((f ≫ Y.isoSpec.hom).fiberToSpecResidueField z)} :=
    Set.ext fun y => fiber_geometricallyReduced_iff_of_target_iso f Y.isoSpec y
  rw [heq]
  exact hopen.preimage Y.isoSpec.hom.continuous

end

/-- **Stacks Project, Tag 0C0E.** The geometrically reduced fibres of a flat, proper, finitely
presented morphism form an open locus in the base. -/
@[stacks 0C0E]
theorem isOpen_geometricallyReduced_fiber
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [IsProper f]
    (hfp : FinitePresentation f) :
    IsOpen {y : Y | GeometricallyReduced (f.fiberToSpecResidueField y)} := by
  have : LocallyOfFinitePresentation f := hfp.locallyOfFinitePresentation
  have : QuasiCompact f := hfp.quasiCompact
  have : QuasiSeparated f := hfp.quasiSeparated
  rw [(Y.affineCover.isOpenCover_opensRange).isOpen_iff_coe_preimage]
  intro i
  let U := (Y.affineCover.f i).opensRange
  let : IsAffine (↑U : Scheme.{u}) := isAffineOpen_opensRange (Y.affineCover.f i)
  have hfpU : FinitePresentation (f ∣_ U) := ⟨inferInstance, inferInstance, inferInstance⟩
  have hopenU := isOpen_geometricallyReduced_fiber_of_isAffine (f ∣_ U) hfpU
  show IsOpen (U.ι ⁻¹' {y : Y | GeometricallyReduced (f.fiberToSpecResidueField y)})
  rw [← geometricallyReduced_fiber_set_morphismRestrict f U]
  exact hopenU

section GenericFibre

/-- **A constructible set containing the generic point of an irreducible space contains a
nonempty open set.** Writing `E` in the normal form of Stacks 005G(1) as a finite union of sets
`U ∩ Vᶜ` with `U` and `V` open, the generic point `η` lies in one such piece. Then `V` is an open
set not containing `η`, so its complement is a closed set containing `η`, hence containing the
closure of `{η}`, which is the whole space; so `V` is empty and the piece is `U`. -/
@[ega "IV 8.1.3" "partial"]
private theorem exists_isOpen_mem_subset_of_isConstructible {T : Type*} [TopologicalSpace T]
    {E : Set T} (hE : IsConstructible E) {η : T}
    (hη : IsGenericPoint η (Set.univ : Set T)) (hηE : η ∈ E) :
    ∃ U : Set T, IsOpen U ∧ η ∈ U ∧ U ⊆ E := by
  obtain ⟨t, ht, hEeq⟩ := Topology.isConstructible_iff_exists_finset_biUnion_inter_compl.mp hE
  rw [hEeq] at hηE ⊢
  obtain ⟨p, hpt, hηU, hηV⟩ := Set.mem_iUnion₂.mp hηE
  have hVempty : p.2 = ∅ := by
    have hsub : (Set.univ : Set T) ⊆ p.2ᶜ := by
      rw [← hη]
      exact (ht p hpt).2.2.1.isClosed_compl.closure_subset_iff.mpr
        (Set.singleton_subset_iff.mpr hηV)
    simpa using Set.subset_compl_comm.mp hsub
  exact ⟨p.1, (ht p hpt).1, hηU, fun x hx =>
    Set.mem_biUnion hpt ⟨hx, by simp [hVempty]⟩⟩

/-- A point of an open subscheme lying over a generic point of the ambient scheme is a generic
point of that open subscheme: the inclusion is an embedding, so it reflects specialization. -/
private theorem isGenericPoint_of_mem_opens {Y : Scheme.{u}} {η : Y}
    (hη : IsGenericPoint η (Set.univ : Set Y)) (W : Y.Opens) (w : (W : Scheme.{u}))
    (hw : W.ι w = η) :
    IsGenericPoint w (Set.univ : Set (W : Scheme.{u})) := by
  rw [isGenericPoint_iff_specializes]
  refine fun z => ⟨fun _ => Set.mem_univ _, fun _ => ?_⟩
  rw [← W.ι.isOpenEmbedding.isInducing.specializes_iff, hw]
  exact (isGenericPoint_iff_specializes.mp hη (W.ι z)).2 (Set.mem_univ _)

/-- **[Stacks, Tag 0579] over an affine base, with no Noetherian hypothesis.** For a
quasi-compact morphism locally of finite presentation onto an affine scheme the locus of points
whose fibre is geometrically reduced is constructible.

The source is covered by finitely many affine opens, geometric reducedness of the fibre at a
point is local on the source, and the affine case of Stacks 0579 without a Noetherian hypothesis
is `AlgebraicGeometry.isLocallyConstructible_geometricallyReduced_fiber_of_isAffine_source`.

Quasi-separatedness of `f` is not needed: each composite `Uᵢ ⟶ X ⟶ S` has affine source, hence
is quasi-separated for free. -/
@[ega "IV 9.7.7" "(iii), special case"]
private theorem isConstructible_geometricallyReduced_fiber_of_isAffine_target
    {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine S] [QuasiCompact f]
    [LocallyOfFinitePresentation f] :
    IsConstructible {y : S | GeometricallyReduced (f.fiberToSpecResidueField y)} := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  rw [geometricallyReduced_fiber_set_eq_iInter_finiteSubcover f]
  refine (IsLocallyConstructible.iInter fun i => ?_).isConstructible
  exact isLocallyConstructible_geometricallyReduced_fiber_of_isAffine_source _
    ⟨inferInstance, inferInstance, inferInstance⟩

/-- **Stacks Project, Tag 0579.** Let `f : X ⟶ Y` be a quasi-compact morphism of schemes which
is locally of finite presentation. Then the set of points of `Y` whose fibre is geometrically
reduced is locally constructible in `Y`.

Local constructibility is tested on the affine opens of `Y`
(`AlgebraicGeometry.isLocallyConstructible_iff_forall_affineOpens`). Over an affine open `U` the
restriction `f ∣_ U` is again quasi-compact and locally of finite presentation, and its
geometrically reduced fibre locus is the inverse image of that of `f` by Stacks 0576, so
`AlgebraicGeometry.isConstructible_geometricallyReduced_fiber_of_isAffine_target` applies. -/
@[stacks 0579, ega "IV 9.7.7" "more general"]
theorem isLocallyConstructible_geometricallyReduced_fiber {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [LocallyOfFinitePresentation f] :
    IsLocallyConstructible {y : Y | GeometricallyReduced (f.fiberToSpecResidueField y)} := by
  rw [isLocallyConstructible_iff_forall_affineOpens]
  intro U
  have : IsAffine (U.1 : Scheme.{u}) := U.2
  have h := isConstructible_geometricallyReduced_fiber_of_isAffine_target (f ∣_ U.1)
  rwa [geometricallyReduced_fiber_set_morphismRestrict] at h

/-- An open subscheme of the base all of whose points have geometrically reduced fibre has
geometrically reduced restricted morphism: the locus of the restriction is the inverse image of
the locus of `f`, by Stacks 0576. -/
private theorem geometricallyReduced_morphismRestrict_of_subset_setOf {X Y : Scheme.{u}}
    (f : X ⟶ Y) (V : Y.Opens)
    (hVE : (V : Set Y) ⊆ {y : Y | GeometricallyReduced (f.fiberToSpecResidueField y)}) :
    GeometricallyReduced (f ∣_ V) := by
  rw [GeometricallyReduced.iff_geometricallyReduced_fiber]
  intro z
  exact show z ∈ {z : (V : Scheme.{u}) |
    GeometricallyReduced ((f ∣_ V).fiberToSpecResidueField z)} from
    geometricallyReduced_fiber_set_morphismRestrict f V ▸ hVE z.2

/-- **The locus half of Stacks 0578 for a morphism of finite presentation.** For a morphism of
finite presentation onto an irreducible scheme whose fibre over the generic point `η` is
geometrically reduced, the locus of points with geometrically reduced fibre contains an open
neighbourhood of `η`.

The locus is constructible on an affine open neighbourhood `W` of `η`, by
`AlgebraicGeometry.isConstructible_geometricallyReduced_fiber_of_isAffine_target` applied to
`f ∣_ W` — the locus of the restriction being the preimage of the locus of `f`, by Stacks 0576.
The point of `W` over `η` is a generic point of `W`, so
`AlgebraicGeometry.exists_isOpen_mem_subset_of_isConstructible` produces an open subset of `W`
containing it and inside the locus; its image in `Y` is open, contains `η`, and lies in the
locus. -/
private theorem exists_opens_mem_subset_setOf_geometricallyReduced_fiber_of_finitePresentation
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace Y] (hf : FinitePresentation f) (η : Y)
    (hη : IsGenericPoint η (Set.univ : Set Y))
    (hηE : GeometricallyReduced (f.fiberToSpecResidueField η)) :
    ∃ V : Y.Opens, η ∈ (V : Set Y) ∧
      (V : Set Y) ⊆ {y : Y | GeometricallyReduced (f.fiberToSpecResidueField y)} := by
  have : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
  have : QuasiCompact f := hf.quasiCompact
  have : QuasiSeparated f := hf.quasiSeparated
  set E : Set Y := {y : Y | GeometricallyReduced (f.fiberToSpecResidueField y)} with hE
  set W : Y.Opens := (Y.affineCover.f (Y.affineCover.idx η)).opensRange with hWdef
  have hWaff : IsAffine (W : Scheme.{u}) := isAffineOpen_opensRange _
  obtain ⟨w, hw⟩ : ∃ w : (W : Scheme.{u}), W.ι w = η := by
    obtain ⟨x, hx⟩ : η ∈ (W : Set Y) := Y.affineCover.covers η
    exact ⟨⟨η, ⟨x, hx⟩⟩, rfl⟩
  have hpreW := geometricallyReduced_fiber_set_morphismRestrict f W
  have hwE : w ∈ W.ι ⁻¹' E := by
    show W.ι w ∈ E
    rwa [hw]
  obtain ⟨U, hUopen, hwU, hUE⟩ :=
    exists_isOpen_mem_subset_of_isConstructible
      (hpreW ▸ isConstructible_geometricallyReduced_fiber_of_isAffine_target (f ∣_ W))
      (isGenericPoint_of_mem_opens hη W w hw) hwE
  refine ⟨W.ι ''ᵁ ⟨U, hUopen⟩, ⟨w, hwU, hw⟩, ?_⟩
  rintro y ⟨v, hv, rfl⟩
  exact hUE hv

/-- **Stacks Project, Tag 0578 for a morphism of finite presentation.** Let `f : X ⟶ Y` be a
morphism of finite presentation onto an irreducible scheme with generic point `η`. If the fibre
of `f` over `η` is geometrically reduced, then there is a nonempty open subscheme `V ⊆ Y` such
that `X_V ⟶ V` has geometrically reduced fibres.

This is the special case of
`AlgebraicGeometry.exists_opens_nonempty_geometricallyReduced_morphismRestrict_of_finiteType`,
which carries `@[stacks 0578]`, in which the finite type hypothesis of the source is strengthened
to finite presentation; it is the form in which the locus is directly constructible, and the
general statement is deduced from it by generic flatness over the reduction of the base. -/
theorem exists_opens_nonempty_geometricallyReduced_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IrreducibleSpace Y] (hf : FinitePresentation f) (η : Y)
    (hη : IsGenericPoint η (Set.univ : Set Y))
    [GeometricallyReduced (f.fiberToSpecResidueField η)] :
    ∃ V : Y.Opens, Nonempty V ∧ GeometricallyReduced (f ∣_ V) := by
  obtain ⟨V, hηV, hVE⟩ :=
    exists_opens_mem_subset_setOf_geometricallyReduced_fiber_of_finitePresentation f hf η hη
      ‹GeometricallyReduced (f.fiberToSpecResidueField η)›
  exact ⟨V, ⟨⟨η, hηV⟩⟩, geometricallyReduced_morphismRestrict_of_subset_setOf f V hVE⟩

/-- **Stacks Project, Tag 0578.** Let `f : X ⟶ Y` be a morphism of finite type onto an
irreducible scheme with generic point `η`. If the fibre of `f` over `η` is geometrically reduced,
then there is a nonempty open subscheme `V ⊆ Y` such that `X_V ⟶ V` has geometrically reduced
fibres.

Finite presentation is reached by the source's own bridge, Stacks 052A. The base is replaced by
its reduction `r : Y_red ⟶ Y`, which is a universal homeomorphism, so it carries opens and
generic points across and, by Stacks 0576, carries the geometrically reduced fibre locus of the
base change back to that of `f`. Over the reduced base generic flatness
`AlgebraicGeometry.exists_dense_open_flat_finitePresentation_structureSheaf` supplies a dense
open `U ⊆ Y_red` over which the base change is of finite presentation; the generic point lies in
`U` because `U` is dense, so the finite presentation case applies over `U` and produces an open
subset of `U` inside the locus and containing the generic point. Its image in `Y` under the open
immersion of `U` followed by the homeomorphism `r` is open, nonempty and inside the locus of
`f`. -/
@[stacks 0578]
theorem exists_opens_nonempty_geometricallyReduced_morphismRestrict_of_finiteType
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace Y]
    [LocallyOfFiniteType f] [QuasiCompact f] (η : Y)
    (hη : IsGenericPoint η (Set.univ : Set Y))
    [GeometricallyReduced (f.fiberToSpecResidueField η)] :
    ∃ V : Y.Opens, Nonempty V ∧ GeometricallyReduced (f ∣_ V) := by
  set E : Set Y := {y : Y | GeometricallyReduced (f.fiberToSpecResidueField y)} with hE
  -- The reduction of the base, a universal homeomorphism onto `Y`.
  set r : Y.nilradical.subscheme ⟶ Y := Y.nilradical.subschemeι with hrdef
  have hrhomeo : IsHomeomorph r :=
    (inferInstance : UniversalHomeomorphism r).universally_isHomeomorph _ _ _
      IsPullback.of_id_snd
  have hred : IsReduced Y.nilradical.subscheme := by
    rw [← Scheme.IdealSheafData.vanishingIdeal_top]
    exact Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal ⊤
  have hirrsp : IrreducibleSpace Y.nilradical.subscheme :=
    (hrhomeo.homeomorph r).irreducibleSpace_iff.mpr inferInstance
  -- The base change of `f` to the reduction, and its geometrically reduced fibre locus.
  set fred : pullback f r ⟶ Y.nilradical.subscheme := pullback.snd f r with hfreddef
  have hpb : IsPullback (pullback.fst f r) fred f r := IsPullback.of_hasPullback f r
  have hftred : LocallyOfFiniteType fred :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb inferInstance
  have hqcred : QuasiCompact fred :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb inferInstance
  have hEred : {y : Y.nilradical.subscheme |
      GeometricallyReduced (fred.fiberToSpecResidueField y)} = r ⁻¹' E :=
    geometricallyReduced_fiber_set_eq_preimage_of_isPullback f fred (pullback.fst f r) r hpb
  -- The generic point of the reduction lies over `η`.
  set ηred : Y.nilradical.subscheme := genericPoint Y.nilradical.subscheme with hηreddef
  have hηredgen : IsGenericPoint ηred (Set.univ : Set Y.nilradical.subscheme) :=
    genericPoint_spec Y.nilradical.subscheme
  have hrη : r ηred = η :=
    (hη.eq (by
      simpa [Set.image_univ, Set.range_eq_univ.mpr hrhomeo.surjective] using
        hηredgen.image r.continuous)).symm
  -- Generic flatness over the reduced base: shrink to where `fred` is of finite presentation.
  obtain ⟨U, hUdense, -, hUfp⟩ := exists_dense_open_flat_finitePresentation_structureSheaf fred
  rw [Scheme.Hom.resLE_eq_morphismRestrict] at hUfp
  have hηredU : ηred ∈ (U : Set Y.nilradical.subscheme) :=
    (hηredgen.mem_open_set_iff U.2).2 (by simpa using hUdense.nonempty)
  -- The generic point of `U`, and the locus of the restriction over `U`.
  set ηU : (U : Scheme.{u}) := ⟨ηred, hηredU⟩ with hηUdef
  have hηUgen : IsGenericPoint ηU (Set.univ : Set (U : Scheme.{u})) :=
    isGenericPoint_of_mem_opens hηredgen U ηU rfl
  have hUirr : IrreducibleSpace (U : Scheme.{u}) :=
    { toPreirreducibleSpace := ⟨by
        rw [← hηUgen]
        exact (isIrreducible_singleton.closure).isPreirreducible⟩
      toNonempty := ⟨ηU⟩ }
  have hEU := geometricallyReduced_fiber_set_morphismRestrict fred U
  have hηUE : GeometricallyReduced ((fred ∣_ U).fiberToSpecResidueField ηU) := by
    show ηU ∈ {z : (U : Scheme.{u}) |
      GeometricallyReduced ((fred ∣_ U).fiberToSpecResidueField z)}
    rw [hEU]
    show U.ι ηU ∈ {y : Y.nilradical.subscheme |
      GeometricallyReduced (fred.fiberToSpecResidueField y)}
    rw [hEred]
    show r (U.ι ηU) ∈ E
    rw [show U.ι ηU = ηred from rfl, hrη]
    exact ‹GeometricallyReduced (f.fiberToSpecResidueField η)›
  -- The finite presentation case over `U`.
  obtain ⟨V', hηV', hV'E⟩ :=
    exists_opens_mem_subset_setOf_geometricallyReduced_fiber_of_finitePresentation
      (fred ∣_ U) hUfp ηU hηUgen hηUE
  -- Transport the open subset of `U` back to `Y` along `U.ι` and the homeomorphism `r`.
  refine ⟨⟨r '' (U.ι '' (V' : Set (U : Scheme.{u}))),
    hrhomeo.isOpenMap _ (U.ι.isOpenEmbedding.isOpenMap _ V'.2)⟩, ⟨⟨η, ?_⟩⟩,
    geometricallyReduced_morphismRestrict_of_subset_setOf f _ ?_⟩
  · exact ⟨U.ι ηU, ⟨ηU, hηV', rfl⟩, by rw [show U.ι ηU = ηred from rfl, hrη]⟩
  · rintro - ⟨-, ⟨z, hz, rfl⟩, rfl⟩
    have hz' : z ∈ U.ι ⁻¹' {y : Y.nilradical.subscheme |
        GeometricallyReduced (fred.fiberToSpecResidueField y)} := by
      rw [← hEU]; exact hV'E hz
    rwa [hEred] at hz'

/-- **Stacks Project, Tag 0578 over a locally Noetherian base.** The literal shape of the source
statement — `f` of finite type, carried by `LocallyOfFiniteType` together with `QuasiCompact` —
in the case where the base is locally Noetherian. The same statement over an arbitrary base is
`AlgebraicGeometry.exists_opens_nonempty_geometricallyReduced_morphismRestrict_of_finiteType`,
which is where `@[stacks 0578]` sits.

A morphism locally of finite type to a locally Noetherian scheme is locally of finite
presentation and has a locally Noetherian, hence quasi-separated, source, so it is of finite
presentation and
`AlgebraicGeometry.exists_opens_nonempty_geometricallyReduced_morphismRestrict` applies. -/
theorem exists_opens_nonempty_geometricallyReduced_morphismRestrict_of_locallyOfFiniteType
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace Y] [IsLocallyNoetherian Y]
    [LocallyOfFiniteType f] [QuasiCompact f] (η : Y)
    (hη : IsGenericPoint η (Set.univ : Set Y))
    [GeometricallyReduced (f.fiberToSpecResidueField η)] :
    ∃ V : Y.Opens, Nonempty V ∧ GeometricallyReduced (f ∣_ V) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  exact exists_opens_nonempty_geometricallyReduced_morphismRestrict f
    ⟨inferInstance, inferInstance, inferInstance⟩ η hη

end GenericFibre

end AlgebraicGeometry
