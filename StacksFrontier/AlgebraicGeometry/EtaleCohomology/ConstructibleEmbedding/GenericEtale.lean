module
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ShortComplexDiagramHomology
public import StacksCore.Algebra.Homology.SpectralSequence.Tower
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Defs
public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.RingTheory.Ideal.Over.HeightOne
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.FlatModuleSheavesAndStalks

public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.AtPointCriteria
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.StalkDimension

/-!
# A finite morphism of integral schemes with separable function field extension is generically
étale

Let `g : Y ⟶ Z` be a finite morphism of finite presentation between integral schemes carrying the
generic point of `Y` to that of `Z`, and suppose the extension of function fields is separable.
Then `g` is finite étale over a nonempty open of `Z`.

At the generic point the local rings are the function fields, so the stalk map is flat and carries
the maximal ideal `0` to `0`, while the residue field extension is finite (as `g` is quasi-finite)
and separable; by the criterion `AlgebraicGeometry.etaleAt_tfae` the morphism is étale at the
generic point, hence on an open neighbourhood `V` of it. The image of the closed complement of `V`
is closed, as `g` is finite, and misses the generic point of `Z`, the fibre of `g` over it being
discrete; over the open complement `U` of that image `g` is étale.

## Main results

* `AlgebraicGeometry.exists_nonempty_open_etale_restrict_of_isSeparable` — the statement.
* `AlgebraicGeometry.IsGenericallyFiniteEtaleOntoImage` — the property of the morphisms
  `Yᵢ ⟶ X` in the last sentence of Stacks 09Z6.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **A finite morphism of integral schemes with separable function field extension is étale over
a nonempty open of the target.** -/
theorem exists_nonempty_open_etale_restrict_of_isSeparable {Y Z : Scheme.{u}} [IsIntegral Y]
    [IsIntegral Z] (g : Y ⟶ Z) [IsFinite g] [LocallyOfFinitePresentation g]
    [LocallyQuasiFinite g] (hg : g (genericPoint Y) = genericPoint Z)
    (hsep : letI := (g.residueFieldMap (genericPoint Y)).hom.toAlgebra
      Algebra.IsSeparable (Z.residueField (g (genericPoint Y))) (Y.residueField (genericPoint Y))) :
    ∃ U : Z.Opens, (U : Set Z).Nonempty ∧ Etale (g ∣_ U) := by
  set η := genericPoint Y
  have hfieldZ : IsField (Z.presheaf.stalk (g η)) := by
    refine isField_stalk_of_closure_mem_irreducibleComponents Z (g η) ?_
    rw [hg, (genericPoint_spec Z).def, irreducibleComponents_eq_singleton]
    exact Set.mem_singleton _
  have hfieldY : IsField (Y.presheaf.stalk η) := Field.toIsField Y.functionField
  let := hfieldZ.toField
  have hflat : (g.stalkMap η).hom.Flat := by
    algebraize [(g.stalkMap η).hom]
    exact Module.Flat.of_free
  have hmax : Ideal.map (g.stalkMap η).hom (IsLocalRing.maximalIdeal (Z.presheaf.stalk (g η))) =
      IsLocalRing.maximalIdeal (Y.presheaf.stalk η) := by
    rw [(IsLocalRing.isField_iff_maximalIdeal_eq).1 hfieldZ,
      (IsLocalRing.isField_iff_maximalIdeal_eq).1 hfieldY, Ideal.map_bot]
  have hEt : EtaleAt g η := by
    have h := (etaleAt_tfae g η).out 1 7
    exact h.2 ⟨hflat, hmax, g.finite_residueField_of_quasiFiniteAt η (g.quasiFiniteAt η), hsep⟩
  obtain ⟨V, -, hηV, hV⟩ := exists_isAffineOpen_etale_comp_ι_of_etaleAt g η hEt
  let C : Set Z := g '' (V : Set Y)ᶜ
  have hηC : g η ∉ C := by
    rintro ⟨y, hyV, hy⟩
    have hdisc : DiscreteTopology ↥(g.base ⁻¹' {g η}) :=
      isDiscrete_iff_discreteTopology.mp (g.isDiscrete_preimage_singleton _)
    have hsp : (⟨η, rfl⟩ : ↥(g.base ⁻¹' {g η})) ⤳ ⟨y, hy⟩ :=
      Topology.IsEmbedding.subtypeVal.toIsInducing.specializes_iff.mp
        ((genericPoint_spec Y).specializes (Set.mem_univ y))
    obtain rfl : η = y := congrArg Subtype.val hsp.eq
    exact hyV hηV
  let U : Z.Opens := ⟨Cᶜ, (g.isClosedMap _ V.isOpen.isClosed_compl).isOpen_compl⟩
  refine ⟨U, ⟨g η, hηC⟩, ?_⟩
  have hle : g ⁻¹ᵁ U ≤ V := fun y hy ↦ Classical.byContradiction fun hyV ↦ hy ⟨y, hyV, rfl⟩
  have : Etale ((g ∣_ U) ≫ U.ι) := by
    rw [morphismRestrict_ι, ← Scheme.homOfLE_ι Y hle, Category.assoc]
    infer_instance
  exact Etale.of_comp (g ∣_ U) U.ι

/-- The property of a morphism `f : Y ⟶ X` in the last sentence of Stacks 09Z6: `Y` is irreducible
and reduced, and `f` maps `Y` onto an irreducible and reduced closed subscheme `ι : Z ⟶ X`,
through a morphism `g : Y ⟶ Z` which is finite étale over a nonempty open of `Z`. -/
def IsGenericallyFiniteEtaleOntoImage {X Y : Scheme.{u}} (f : Y ⟶ X) : Prop :=
  IsIntegral Y ∧ ∃ (Z : Scheme.{u}) (ι : Z ⟶ X) (g : Y ⟶ Z), IsClosedImmersion ι ∧ IsIntegral Z ∧
    Surjective g ∧ g ≫ ι = f ∧
      ∃ U : Z.Opens, (U : Set Z).Nonempty ∧ IsFinite (g ∣_ U) ∧ Etale (g ∣_ U)

end AlgebraicGeometry

end
