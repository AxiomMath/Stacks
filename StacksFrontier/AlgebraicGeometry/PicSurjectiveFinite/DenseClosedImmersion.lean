module

public import StacksFrontier.AlgebraicGeometry.LiftInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.LiftInvertible.ClosedUnionGlue
public import StacksFrontier.AlgebraicGeometry.LimitMorphismAt.Dominant
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImageQuasicoherent
public import StacksFrontier.Topology.Dimension.NowhereDense
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Descending an invertible module along a morphism that is a closed immersion generically

Let `f : X ⟶ Y` be a finite morphism of schemes, let `Y` have Noetherian underlying space of
dimension at most one, and assume that `f` is a closed immersion over some dense open subset
`V` of `Y`. [Stacks, Tag 0C0U] asserts that every invertible `𝒪_X`-module is the pullback of an
invertible `𝒪_Y`-module.

A closed immersion need not be surjective, so `f ∣_ V` being a closed immersion does not make
it an isomorphism and the statement is not a direct instance of [Stacks, Tag 0C0T]. It becomes
one after replacing the target by the scheme-theoretic image `Z := f.image`: writing `f` as
`f.toImage ≫ f.imageι` and putting `U := f.imageι ⁻¹ᵁ V`, the restriction `f.toImage ∣_ U` is a
closed immersion by cancellation against `f.imageι ∣_ V`, and its kernel ideal sheaf is the
restriction of `f.toImage.ker = ⊥`, so it is an *isomorphism*. The complement of `U` in `Z` is
discrete because the complement of a dense open set in a Noetherian space of dimension at most
one is a finite set of closed points. So Tag 0C0T descends the module along `f.toImage` to an
invertible module on `Z`, and [Stacks, Tag 09NY] lifts that one further along the closed
immersion `f.imageι` to an invertible module on `Y`.

Only the underlying space of `Y` is required to be Noetherian, not the scheme: both the
topological input and Tag 09NY as it is formalized ask for no more.

## Main results

* `Stacks.PicFinite.discreteTopology_compl_preimage_of_dense`: the part of a closed subscheme
  of a Noetherian scheme of dimension at most one lying outside a dense open subset of the
  ambient scheme is a discrete space.
* `Stacks.PicFinite.exists_isInvertible_modulePullback_iso_of_isClosedImmersion_restrict`:
  **Tag 0C0U.**

## Implementation notes

Invertibility is read through Tag 01CS's `AlgebraicGeometry.SheafOfModules.IsInvertible`, in the
spelling of Tag 0C0T, which is the natural neighbour of this statement. Tag 09NY is stated with
its modules spelled `SheafOfModules (structureSheafRing _.toRingedSpace)`
and its pullback spelled `RingedSpaceModuleAdjunction.modulePullback _.toLRSHom.toShHom`; those
agree with `AlgebraicGeometry.Scheme.Modules` and `AlgebraicGeometry.Scheme.Modules.pullback`
by `rfl`, so no comparison isomorphism intervenes, and the two sheaf-condition witnesses
`Presheaf.isSheaf_comp_of_isSheaf` and `(Presheaf.isSheaf_iff_isSheaf_comp _ _ _).mp` are
interchangeable by proof irrelevance.

The dimension of `Y` is `topologicalKrullDim`, the Krull dimension of its underlying space,
which is the dimension of a scheme in the sense of [Stacks, Tag 04MT].

## References

* [Stacks Project, Tag 0C0U](https://stacks.math.columbia.edu/tag/0C0U)
* [Stacks Project, Tag 0C0T](https://stacks.math.columbia.edu/tag/0C0T)
* [Stacks Project, Tag 09NY](https://stacks.math.columbia.edu/tag/09NY)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 04MT](https://stacks.math.columbia.edu/tag/04MT)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.PicFinite

/-- **Outside a dense open subset of a curve, a closed subscheme is discrete.** Let `Y` be a
scheme whose underlying space is Noetherian of dimension at most one, let `V` be a dense open
subset of `Y`, and let `i : Z ⟶ Y` be a closed immersion. Then the part of `Z` lying outside
`V` is a discrete space.

The complement of a dense open set is closed with empty interior, so in a Noetherian space it
contains no irreducible component; dimension at most one then forces it to be a finite set of
closed points, hence discrete. The part of `Z` outside `V` is its preimage under the injective
continuous map `i`, so it inherits discreteness. -/
@[sga "4 XVIII 1.1.3" "more general"]
theorem discreteTopology_compl_preimage_of_dense {Y Z : Scheme.{u}} (i : Z ⟶ Y)
    [IsClosedImmersion i] [NoetherianSpace Y] (hdim : topologicalKrullDim Y ≤ 1)
    (V : Y.Opens) (hV : Dense (V : Set Y)) :
    DiscreteTopology ((((i ⁻¹ᵁ V : Z.Opens) : Set Z)ᶜ) : Set Z) := by
  have hcl : IsClosed ((V : Set Y)ᶜ) := V.isOpen.isClosed_compl
  have hnd : IsNowhereDense ((V : Set Y)ᶜ) :=
    hcl.isNowhereDense_iff.mpr (by rw [interior_compl, hV.closure_eq, Set.compl_univ])
  have : DiscreteTopology (((V : Set Y)ᶜ) : Set Y) :=
    Stacks.LiftInvertible.discreteTopology_compl_of_topologicalKrullDim_le_one Y hdim V
      (hcl.isNowhereDense_iff_forall_irreducibleComponents_not_subset.mp hnd)
  rw [Scheme.Hom.coe_preimage, ← Set.preimage_compl]
  exact DiscreteTopology.preimage_of_continuous_injective _ i.continuous
    i.isClosedEmbedding.injective

/-- **Stacks Project, Tag 0C0U.** Let `f : X ⟶ Y` be a finite morphism of schemes with `Y` of
Noetherian underlying space and dimension at most one, and suppose `f` is a closed immersion
over a dense open subset `V` of `Y`. Then every invertible `𝒪_X`-module is the pullback of an
invertible `𝒪_Y`-module.

The morphism factors as `f.toImage ≫ f.imageι` through its scheme-theoretic image `Z`. Over
`U := f.imageι ⁻¹ᵁ V` the first factor is a closed immersion with trivial kernel ideal sheaf,
hence an isomorphism, and the part of `Z` outside `U` is discrete, so Tag 0C0T descends the
module to `Z`; Tag 09NY then lifts it across the closed immersion `f.imageι` to `Y`. -/
@[stacks 0C0U]
theorem exists_isInvertible_modulePullback_iso_of_isClosedImmersion_restrict
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [NoetherianSpace Y]
    (hdim : topologicalKrullDim Y ≤ 1) (V : Y.Opens) (hV : Dense (V : Set Y))
    [IsClosedImmersion (f ∣_ V)]
    (L : X.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      ((Presheaf.isSheaf_iff_isSheaf_comp _ X.presheaf
        (forget₂ CommRingCat RingCat)).mp X.IsSheaf) L) :
    ∃ M : Y.Modules,
      AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf
          ((Presheaf.isSheaf_iff_isSheaf_comp _ Y.presheaf
            (forget₂ CommRingCat RingCat)).mp Y.IsSheaf) M ∧
        Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M ≅ L) := by
  have hfac : f.toImage ≫ f.imageι = f := f.toImage_imageι
  have : IsFinite f.toImage := by
    refine (IsFinite.comp_iff (f := f.toImage) (g := f.imageι)).mp ?_
    rw [hfac]; infer_instance
  have hfacRestrict : IsClosedImmersion ((f.toImage ≫ f.imageι) ∣_ V) := by
    rw [hfac]; infer_instance
  have : IsClosedImmersion ((f.toImage ∣_ f.imageι ⁻¹ᵁ V) ≫ (f.imageι ∣_ V)) := by
    rw [← morphismRestrict_comp f.toImage f.imageι V]
    exact hfacRestrict
  have : IsClosedImmersion (f.toImage ∣_ f.imageι ⁻¹ᵁ V) :=
    IsClosedImmersion.of_comp (f.toImage ∣_ f.imageι ⁻¹ᵁ V) (f.imageι ∣_ V)
  have : IsIso (f.toImage ∣_ f.imageι ⁻¹ᵁ V) := by
    rw [IsClosedImmersion.isIso_iff_ker_eq_bot, ker_morphismRestrict_eq_comap,
      f.toImage.ker_eq_bot, Scheme.IdealSheafData.comap_bot]
  have := discreteTopology_compl_preimage_of_dense f.imageι hdim V hV
  obtain ⟨N, hN, ⟨isoN⟩⟩ :=
    exists_isInvertible_modulePullback_iso f.toImage (f.imageι ⁻¹ᵁ V) L hL
  obtain ⟨M, hM, ⟨isoM⟩⟩ :=
    Stacks.LiftInvertible.exists_modulePullback_iso_of_isClosedImmersion_of_dimension_le_one
      Y f.image f.imageι hdim N
  refine ⟨M, hM, ⟨(eqToIso (congrArg
    (fun q : X ⟶ Y => (Scheme.Modules.pullback q).obj M) hfac)).symm.trans ?_⟩⟩
  exact ((Scheme.Modules.pullbackComp f.toImage f.imageι).app M).symm.trans
    (((Scheme.Modules.pullback f.toImage).mapIso isoM).trans isoN)

end Stacks.PicFinite

end
