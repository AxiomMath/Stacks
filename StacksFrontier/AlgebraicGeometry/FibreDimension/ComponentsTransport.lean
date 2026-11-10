module

public import Mathlib.AlgebraicGeometry.Fiber
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.SourceMap
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChangeBirational.Basic

/-!
# Transporting "a closed set is a union of irreducible components"

The conclusion of Stacks 053R has the shape

> `W = ⋃₀ {C | C ∈ irreducibleComponents Y ∧ C ⊆ W}`

for a closed subset `W` of a space `Y`. This file collects the ways that shape moves around,
which is what the reductions in the proof of that tag consume: it is inherited by preimages
along maps that lift generalizations, it is local on `Y`, and for the fibres of a morphism of
schemes it passes along a composition with a preimmersion and is detected on an open cover of
the source.

The hinge in every case is the characterisation of the shape in terms of generic points: a
closed set has it exactly when each generic point of an irreducible component of the set is a
generic point of an irreducible component of the ambient space
(`AlgebraicGeometry.eq_sUnion_irreducibleComponents_of_genericPoints`), and generic points are
carried along by maps lifting generalizations
(`AlgebraicGeometry.mem_genericPoints_of_generalizingMap`).

## Main definitions

* `AlgebraicGeometry.fiberCompHomeo`: the fibre of `f : X ⟶ S` over `s` is homeomorphic to the
  fibre of `f ≫ i` over `i s`, for `i` a preimmersion.

## Main results

* `AlgebraicGeometry.eq_sUnion_irreducibleComponents_of_genericPoints`: a closed set is the
  union of the ambient irreducible components it contains as soon as the generic points of its
  own components are generic points of the ambient space.
* `AlgebraicGeometry.mem_genericPoints_val_of_eq_sUnion_irreducibleComponents`: the converse
  implication, which is what lets the criterion above be applied twice over — to a closed set
  and to its trace on a neighbourhood.
* `AlgebraicGeometry.fiberι_fiberCompHomeo`: the fibre comparison along a preimmersion is
  compatible with the embeddings of the two fibres into the source.
* `AlgebraicGeometry.eq_sUnion_irreducibleComponents_preimage_of_generalizingMap`: the shape is
  inherited by the preimage of a closed set along a continuous map lifting generalizations.
* `AlgebraicGeometry.eq_sUnion_irreducibleComponents_of_isOpen_locally`: the shape is local, so
  it can be checked on a neighbourhood of each point of the closed set.
* `AlgebraicGeometry.eq_sUnion_irreducibleComponents_fiber_comp`: the shape for a fibre of
  `f : X ⟶ S` gives the shape for the corresponding fibre of `f ≫ i` with `i` a preimmersion.
* `AlgebraicGeometry.fiber_preimage_eq_sUnion_irreducibleComponents_of_openCharts`: for the
  support of an ideal sheaf inside a fibre, the shape may be checked on open subschemes of the
  source covering the support.

## Implementation notes

The locality statement takes its neighbourhood as an open *set* rather than as an element of
`Opens Y`: the homeomorphism onto the neighbourhood that the open-chart statement feeds it is
`Topology.IsEmbedding.toHomeomorph`, whose target is the subtype of the range of the embedding,
and only for a set is that the subtype the locality statement speaks about.

## References

* [Stacks Project, Tag 053R](https://stacks.math.columbia.edu/tag/053R)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### The shape in terms of generic points -/

/-- A closed subset `W` of a quasi-sober space is the union of the ambient irreducible
components it contains as soon as every generic point of an irreducible component of `W` is a
generic point of an irreducible component of the ambient space. -/
public theorem eq_sUnion_irreducibleComponents_of_genericPoints {Y : Type*} [TopologicalSpace Y]
    [QuasiSober Y] (W : Set Y) (hW : IsClosed W)
    (hgeneric : ∀ y : W, y ∈ genericPoints W → (y : Y) ∈ genericPoints Y) :
    W = ⋃₀ {C : Set Y | C ∈ irreducibleComponents Y ∧ C ⊆ W} := by
  have : QuasiSober W := hW.isClosedEmbedding_subtypeVal.quasiSober
  refine Set.Subset.antisymm (fun y hy => ?_) ?_
  · have hcomp : irreducibleComponent (⟨y, hy⟩ : W) ∈ irreducibleComponents W :=
      irreducibleComponent_mem_irreducibleComponents _
    set point := genericPoints.ofComponent (⟨_, hcomp⟩ : irreducibleComponents W) with hpoint
    have hspecializes : point.1 ⤳ (⟨y, hy⟩ : W) :=
      (genericPoints.isGenericPoint_ofComponent (⟨_, hcomp⟩ : irreducibleComponents W)).specializes
        mem_irreducibleComponent
    refine Set.mem_sUnion_of_mem ?_ ⟨hgeneric point.1 point.2, ?_⟩
    · exact specializes_iff_mem_closure.mp (hspecializes.map continuous_subtype_val)
    · exact hW.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr point.1.2)
  · rintro y ⟨C, ⟨-, hCW⟩, hyC⟩
    exact hCW hyC

/-- In a closed subset, a point of the subset specializing to a generic point of an irreducible
component of the subset is that generic point. -/
private theorem eq_of_specializes_of_mem_genericPoints_subtype {Y : Type*} [TopologicalSpace Y]
    [T0Space Y] {W : Set Y} (hW : IsClosed W) {y : W} (hy : y ∈ genericPoints W) {z : Y}
    (hz : z ∈ W) (h : z ⤳ (y : Y)) : z = y :=
  congrArg Subtype.val (eq_of_specializes_of_mem_genericPoints (x := ⟨z, hz⟩) hy
    (hW.isClosedEmbedding_subtypeVal.isInducing.specializes_iff.mp h))

/-- The generic point of an irreducible component of a closed set with the shape of the
conclusion of Stacks 053R is a generic point of an irreducible component of the ambient
space. -/
public theorem mem_genericPoints_val_of_eq_sUnion_irreducibleComponents {Y : Type*}
    [TopologicalSpace Y] [T0Space Y] [QuasiSober Y] (W : Set Y) (hW : IsClosed W)
    (hcomponents : W = ⋃₀ {C : Set Y | C ∈ irreducibleComponents Y ∧ C ⊆ W})
    (y : W) (hy : y ∈ genericPoints W) : (y : Y) ∈ genericPoints Y := by
  obtain ⟨C, ⟨hC, hCW⟩, hmem⟩ := (Set.ext_iff.mp hcomponents y.1).mp y.2
  set generic := genericPoints.ofComponent (⟨C, hC⟩ : irreducibleComponents Y) with hgeneric
  have hspec : generic.1 ⤳ (y : Y) :=
    (genericPoints.isGenericPoint_ofComponent (⟨C, hC⟩ : irreducibleComponents Y)).specializes hmem
  have hmemW : generic.1 ∈ W :=
    hCW (genericPoints.isGenericPoint_ofComponent (⟨C, hC⟩ : irreducibleComponents Y)).mem
  exact (eq_of_specializes_of_mem_genericPoints_subtype hW hy hmemW hspec) ▸ generic.2

/-! ### Transport along maps lifting generalizations -/

/-- **The shape of the conclusion of Stacks 053R is inherited by preimages along maps lifting
generalizations.** If a closed set `W` is the union of the ambient irreducible components it
contains, then so is its preimage along a continuous map lifting generalizations — in
particular along an open embedding, or along the map on spectra of a flat ring map. -/
public theorem eq_sUnion_irreducibleComponents_preimage_of_generalizingMap {A B : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [T0Space A] [T0Space B] [QuasiSober A]
    [QuasiSober B] (φ : A → B) (hφ : Continuous φ) (hgen : GeneralizingMap φ) (W : Set B)
    (hW : IsClosed W) (hcomponents : W = ⋃₀ {C : Set B | C ∈ irreducibleComponents B ∧ C ⊆ W}) :
    φ ⁻¹' W = ⋃₀ {C : Set A | C ∈ irreducibleComponents A ∧ C ⊆ φ ⁻¹' W} := by
  have hpreimage := hW.preimage hφ
  have : QuasiSober W := hW.isClosedEmbedding_subtypeVal.quasiSober
  have : QuasiSober (φ ⁻¹' W : Set A) := hpreimage.isClosedEmbedding_subtypeVal.quasiSober
  refine eq_sUnion_irreducibleComponents_of_genericPoints _ hpreimage fun y hy => ?_
  have himage : W.restrictPreimage φ y ∈ genericPoints W :=
    mem_genericPoints_of_generalizingMap (hgen.restrictPreimage W) hy
  have hambient : φ (y : A) ∈ genericPoints B :=
    mem_genericPoints_val_of_eq_sUnion_irreducibleComponents W hW hcomponents _ himage
  refine (mem_genericPoints_iff_forall_specializes_eq (y : A)).2 fun z hz => ?_
  have hzW : z ∈ φ ⁻¹' W := by
    have hzy : φ z = φ (y : A) := eq_of_specializes_of_mem_genericPoints hambient (hz.map hφ)
    change φ z ∈ W
    rw [hzy]
    exact y.2
  exact eq_of_specializes_of_mem_genericPoints_subtype hpreimage hy hzW hz

/-- The preimage of a closed set with the shape of Stacks 053R along a homeomorphism has it. -/
private theorem eq_sUnion_irreducibleComponents_preimage_homeomorph {A B : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [T0Space A] [T0Space B] [QuasiSober A]
    [QuasiSober B] (e : A ≃ₜ B) (W : Set B) (hW : IsClosed W)
    (hcomponents : W = ⋃₀ {C : Set B | C ∈ irreducibleComponents B ∧ C ⊆ W}) :
    e ⁻¹' W = ⋃₀ {C : Set A | C ∈ irreducibleComponents A ∧ C ⊆ e ⁻¹' W} :=
  eq_sUnion_irreducibleComponents_preimage_of_generalizingMap e e.continuous
    e.isOpenEmbedding.generalizingMap W hW hcomponents

/-! ### Locality -/

/-- **The shape of the conclusion of Stacks 053R is local.** A closed set has it as soon as
each of its points has an open neighbourhood on which the trace of the set has it. -/
public theorem eq_sUnion_irreducibleComponents_of_isOpen_locally {Y : Type*}
    [TopologicalSpace Y] [T0Space Y] [QuasiSober Y] (W : Set Y) (hW : IsClosed W)
    (hlocal : ∀ y ∈ W, ∃ N : Set Y, IsOpen N ∧ y ∈ N ∧
      (Subtype.val ⁻¹' W : Set N) = ⋃₀ {C : Set N | C ∈ irreducibleComponents N ∧
        C ⊆ (Subtype.val ⁻¹' W : Set N)}) :
    W = ⋃₀ {C : Set Y | C ∈ irreducibleComponents Y ∧ C ⊆ W} := by
  refine eq_sUnion_irreducibleComponents_of_genericPoints _ hW fun y hy => ?_
  obtain ⟨N, hNopen, hmem, hcomponents⟩ := hlocal y.1 y.2
  have hpreimage := hW.preimage (continuous_subtype_val : Continuous ((↑) : N → Y))
  have : QuasiSober N := hNopen.isOpenEmbedding_subtypeVal.quasiSober
  have : QuasiSober (Subtype.val ⁻¹' W : Set N) :=
    hpreimage.isClosedEmbedding_subtypeVal.quasiSober
  have hlift : (⟨y.1, hmem⟩ : N) ∈ (Subtype.val ⁻¹' W : Set N) := y.2
  have hgenericLift : (⟨⟨y.1, hmem⟩, hlift⟩ : (Subtype.val ⁻¹' W : Set N)) ∈
      genericPoints (Subtype.val ⁻¹' W : Set N) := by
    refine (mem_genericPoints_iff_forall_specializes_eq _).2 fun z hz => ?_
    have hspec : (z.1 : Y) ⤳ (y : Y) :=
      (hz.map continuous_subtype_val).map continuous_subtype_val
    exact Subtype.ext (Subtype.ext
      (eq_of_specializes_of_mem_genericPoints_subtype hW hy z.2 hspec))
  have hambient := mem_genericPoints_val_of_eq_sUnion_irreducibleComponents
    (Subtype.val ⁻¹' W : Set N) hpreimage hcomponents _ hgenericLift
  exact mem_genericPoints_of_generalizingMap
    hNopen.isOpenEmbedding_subtypeVal.generalizingMap hambient

/-! ### Fibres -/

/-- The fibre of `f : X ⟶ S` over `s` is homeomorphic to the fibre of `f ≫ i` over `i s`, for
`i : S ⟶ T` a preimmersion: the two fibres have the same underlying set, because `i` is
injective on points. -/
public noncomputable def fiberCompHomeo {X S T : Scheme.{u}} (f : X ⟶ S) (i : S ⟶ T)
    [IsPreimmersion i] (s : S) : f.fiber s ≃ₜ (f ≫ i).fiber (i s) :=
  (f.fiberHomeo s).trans ((Homeomorph.setCongr (show
      f.base ⁻¹' {s} = (f ≫ i).base ⁻¹' {i s} from by
    ext x
    exact (i.isEmbedding.injective.eq_iff (a := f x) (b := s)).symm)).trans
      ((f ≫ i).fiberHomeo (i s)).symm)

/-- The homeomorphism `AlgebraicGeometry.fiberCompHomeo` is compatible with the embeddings of
the two fibres into `X`. -/
public theorem fiberι_fiberCompHomeo {X S T : Scheme.{u}} (f : X ⟶ S) (i : S ⟶ T)
    [IsPreimmersion i] (s : S) (x : f.fiber s) :
    (f ≫ i).fiberι (i s) (fiberCompHomeo f i s x) = f.fiberι s x :=
  (f ≫ i).fiberι_fiberHomeo_symm _ _

/-- **The shape of the conclusion of Stacks 053R passes to a composition with a preimmersion.**
If the part of the fibre of `f : X ⟶ S` over `s` lying in a closed subset of `X` is a union of
irreducible components of that fibre, the same holds for the fibre of `f ≫ i` over `i s`. -/
public theorem eq_sUnion_irreducibleComponents_fiber_comp {X S T : Scheme.{u}} (f : X ⟶ S)
    (i : S ⟶ T) [IsPreimmersion i] (s : S) (W : Set X) (hW : IsClosed W)
    (hcomponents : f.fiberι s ⁻¹' W =
      ⋃₀ {C : Set (f.fiber s) | C ∈ irreducibleComponents (f.fiber s) ∧
        C ⊆ f.fiberι s ⁻¹' W}) :
    (f ≫ i).fiberι (i s) ⁻¹' W =
      ⋃₀ {C : Set ((f ≫ i).fiber (i s)) | C ∈ irreducibleComponents ((f ≫ i).fiber (i s)) ∧
        C ⊆ (f ≫ i).fiberι (i s) ⁻¹' W} := by
  set e := fiberCompHomeo f i s with he
  have hpreimage : (f ≫ i).fiberι (i s) ⁻¹' W = e.symm ⁻¹' (f.fiberι s ⁻¹' W) := by
    ext x
    have heq := fiberι_fiberCompHomeo f i s (e.symm x)
    rw [he] at heq ⊢
    rw [Homeomorph.apply_symm_apply] at heq
    exact (congrArg (fun z => z ∈ W) heq).to_iff
  rw [hpreimage]
  exact eq_sUnion_irreducibleComponents_preimage_homeomorph e.symm _
    (hW.preimage (f.fiberι s).continuous) hcomponents

/-- **The shape of the conclusion of Stacks 053R may be checked on open charts.** Let
`f : X ⟶ S` be a morphism of schemes, `I` an ideal sheaf on `X` and `s` a point of `S`. If every
point of the fibre over `s` lying in the support of `I` is in the image of an open immersion
`Y ⟶ X` for which the corresponding statement holds, then the part of the fibre lying in the
support of `I` is a union of irreducible components of the fibre. -/
public theorem fiber_preimage_eq_sUnion_irreducibleComponents_of_openCharts {X S : Scheme.{u}}
    (f : X ⟶ S) (I : X.IdealSheafData) (s : S)
    (hcharts : ∀ x : f.fiber s, f.fiberι s x ∈ (I.support : Set X) →
      ∃ (Y : Scheme.{u}) (i : Y ⟶ X) (_ : IsOpenImmersion i),
        f.fiberι s x ∈ Set.range i.base ∧
        (i ≫ f).fiberι s ⁻¹' (i.base ⁻¹' (I.support : Set X)) =
          ⋃₀ {C : Set ((i ≫ f).fiber s) | C ∈ irreducibleComponents ((i ≫ f).fiber s) ∧
            C ⊆ (i ≫ f).fiberι s ⁻¹' (i.base ⁻¹' (I.support : Set X))}) :
    f.fiberι s ⁻¹' (I.support : Set X) =
      ⋃₀ {C : Set (f.fiber s) | C ∈ irreducibleComponents (f.fiber s) ∧
        C ⊆ f.fiberι s ⁻¹' (I.support : Set X)} := by
  refine eq_sUnion_irreducibleComponents_of_isOpen_locally _
    (I.support.isClosed.preimage (f.fiberι s).continuous) fun x hx => ?_
  obtain ⟨Y, i, hi, hmem, hcomponents⟩ := hcharts x hx
  set e := (f.fiberMap i s).isEmbedding.toHomeomorph with he
  have : QuasiSober (Set.range (f.fiberMap i s).base) :=
    (f.fiberMap i s).isOpenEmbedding.isOpen_range.isOpenEmbedding_subtypeVal.quasiSober
  refine ⟨Set.range (f.fiberMap i s).base, (f.fiberMap i s).isOpenEmbedding.isOpen_range,
    (f.range_fiberMap i s).symm ▸ hmem, ?_⟩
  have hclosed : (Subtype.val ⁻¹' (f.fiberι s ⁻¹' (I.support : Set X)) :
        Set (Set.range (f.fiberMap i s).base)) =
      e.symm ⁻¹' ((i ≫ f).fiberι s ⁻¹' (i.base ⁻¹' (I.support : Set X))) := by
    ext z
    change f.fiberι s z.1 ∈ I.support ↔ i ((i ≫ f).fiberι s (e.symm z)) ∈ I.support
    rw [← f.fiberι_fiberMap i s]
    have hequal : (f.fiberMap i s) (e.symm z) = z.1 :=
      congrArg Subtype.val (e.apply_symm_apply z)
    rw [hequal]
  rw [hclosed]
  exact eq_sUnion_irreducibleComponents_preimage_homeomorph e.symm _
    ((I.support.isClosed.preimage i.continuous).preimage ((i ≫ f).fiberι s).continuous)
    hcomponents

end AlgebraicGeometry

end
