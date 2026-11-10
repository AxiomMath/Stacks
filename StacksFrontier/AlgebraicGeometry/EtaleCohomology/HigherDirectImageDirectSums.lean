module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FilteredColimitsOfEtaleCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sheafification.SmallEtaleColimits
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.CoproductsFromFiltered
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedFunctorAdditive
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.FilteredColimits
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Higher direct images on the small étale site commute with colimits

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of schemes. For every degree
`p` the higher direct image `R^p f_*` of abelian sheaves on the small étale sites commutes with
filtered colimits and with arbitrary direct sums.

## Main results

* `Stacks.EtaleCohomology.isIso_colimit_post_rightDerived_sheafSections_of_qcqs` — over an object
  of the small étale site whose underlying scheme is quasi-compact and quasi-separated, étale
  cohomology commutes with filtered colimits (Stacks 0739 on the small étale site).
* `Stacks.EtaleCohomology.preservesColimitsOfShape_rightDerived_etaleAbelianDirectImage` —
  `R^p f_*` commutes with filtered colimits.
* `Stacks.EtaleCohomology.preservesColimitsOfShape_discrete_rightDerived_etaleAbelianDirectImage`
  — `R^p f_*` commutes with direct sums.

## Implementation notes

The filtered colimit statement is the argument of the source's proof of [Stacks, Tag 09Z1]
specialised to a constant system of schemes: by [Stacks, Tag 072W], `R^p f_*` is the
sheafification of `V ↦ H^p(V ×_Y X, -)`, which commutes with the colimit over every affine `V`
étale over `Y`, because `V ×_Y X` is then quasi-compact and quasi-separated. This is the local
criterion
`Stacks.Cohomology.HigherDirectImage.preservesColimit_rightDerived_sheafPushforwardContinuous'`
(Stacks 0H7B). Over a quasi-compact and quasi-separated object the cohomology commutes with
filtered colimits by Stacks 0739, with the objects whose underlying scheme is quasi-compact and
quasi-separated as the distinguished collection and the finite affine coverings as the cofinal
coverings.

A direct sum is the filtered colimit of its finite sub-sums, and the finite ones are handled by
additivity, as in
`Stacks.EtaleCohomology.preservesColimitsOfShape_discrete_rightDerived_Γ_smallEtale`.

Coefficients are `AddCommGrpCat.{max (u + 1) v}` and index categories live in
`Type (max (u + 1) v)`, the universe controlling the Grothendieck axioms of the sheaf
categories.

## References

* [Stacks Project, Tag 09Z1](https://stacks.math.columbia.edu/tag/09Z1)
* [Stacks Project, Tag 0739](https://stacks.math.columbia.edu/tag/0739)
* [Stacks Project, Tag 0H7B](https://stacks.math.columbia.edu/tag/0H7B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped AlgebraicGeometry.Scheme.SmallEtaleColimits

universe v u

namespace Stacks.EtaleCohomology

attribute [local instance] Stacks.Cohomology.ColimitsOfCohomology.additive_sheafΓ

section QCQSObjects

variable {X : Scheme.{u}}

/-- The objects of the small étale site of `X` whose underlying scheme is quasi-compact and
quasi-separated. -/
def qcqsEtaleObjects (X : Scheme.{u}) : Set X.Etale :=
  {V | CompactSpace V.left ∧ QuasiSeparatedSpace V.left}

/-- An object of the small étale site whose underlying scheme is affine is quasi-compact and
quasi-separated. -/
theorem mem_qcqsEtaleObjects_of_isAffine (V : X.Etale) [IsAffine V.left] :
    V ∈ qcqsEtaleObjects X :=
  ⟨inferInstance, inferInstance⟩

/-- The objects with quasi-compact and quasi-separated underlying scheme contain the vertex of a
fibre product of any two of their members over any third: the first projection is a base change
of a quasi-compact and quasi-separated morphism, a morphism out of a quasi-compact and
quasi-separated scheme into a quasi-separated one being both. -/
theorem exists_pullbackCone_mem_qcqsEtaleObjects {V₁ V₂ W : X.Etale} (f : V₁ ⟶ W)
    (g : V₂ ⟶ W) (h₁ : V₁ ∈ qcqsEtaleObjects X) (h₂ : V₂ ∈ qcqsEtaleObjects X)
    (hW : W ∈ qcqsEtaleObjects X) :
    ∃ t : PullbackCone f g, Nonempty (IsLimit t) ∧ t.pt ∈ qcqsEtaleObjects X := by
  obtain ⟨_, _⟩ := h₁
  obtain ⟨_, _⟩ := h₂
  obtain ⟨_, _⟩ := hW
  have hsq : IsPullback (pullback.snd f g).left (pullback.fst f g).left g.left f.left :=
    ((IsPullback.of_hasPullback f g).map
      (Scheme.Etale.forget X ⋙ CategoryTheory.Over.forget X)).flip
  have hg₁ : QuasiCompact g.left := inferInstance
  have hg₂ : QuasiSeparated g.left := inferInstance
  have hq : QuasiCompact (pullback.fst f g).left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq hg₁
  have hs : QuasiSeparated (pullback.fst f g).left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq hg₂
  refine ⟨PullbackCone.mk (pullback.fst f g) (pullback.snd f g) pullback.condition,
    ⟨pullbackIsPullback f g⟩, ?_, ?_⟩
  · exact @QuasiCompact.compactSpace_of_compactSpace _ _ (pullback.fst f g).left hq ‹_›
  · exact @quasiSeparatedSpace_of_quasiSeparated _ _ (pullback.fst f g).left ‹_› hs

/-- The finite covering families of an object of the small étale site by objects with
quasi-compact and quasi-separated underlying scheme, the object itself being of that kind. -/
def qcqsEtaleCovering (X : Scheme.{u}) (U : X.Etale) : Set (PreZeroHypercover.{u} U) :=
  {E | Finite E.I₀ ∧ U ∈ qcqsEtaleObjects X ∧ (∀ i, E.X i ∈ qcqsEtaleObjects X) ∧
    E.sieve₀ ∈ X.smallEtaleTopology U}

/-- **Étale cohomology over a quasi-compact and quasi-separated object commutes with filtered
colimits.** For every object `U` of the small étale site of an arbitrary scheme `X` whose
underlying scheme is quasi-compact and quasi-separated, every degree `p` and every filtered
system `F` of abelian sheaves, the canonical map
`colim_i H^p(U, F_i) ⟶ H^p(U, colim_i F_i)` is an isomorphism.

This is Stacks 0739 on the small étale site, with the objects with quasi-compact and
quasi-separated underlying scheme as the distinguished collection and the finite affine
coverings as cofinal coverings. -/
@[sga "4 VII 3.3" "more general"]
theorem isIso_colimit_post_rightDerived_sheafSections_of_qcqs (p : ℕ) (U : X.Etale)
    (hU : U ∈ qcqsEtaleObjects X) {I : Type (max (u + 1) v)} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    IsIso (colimit.post F (((sheafSections X.smallEtaleTopology
      AddCommGrpCat.{max (u + 1) v}).obj (op U)).rightDerived p)) :=
  Stacks.Cohomology.isIso_colimit_post_rightDerived_sheafSections_largeCoefficients.{v, u, u, u + 1}
    X.smallEtaleTopology (qcqsEtaleObjects X) (qcqsEtaleCovering X)
    (fun _ _ hE ↦ hE.2.2.2)
    (fun _ E hE ↦ ⟨hE.1, hE.2.1, hE.2.2.1, fun n A ↦
      Stacks.Cohomology.exists_widePullback_in (qcqsEtaleObjects X)
        (fun f g hu hv hw ↦ exists_pullbackCone_mem_qcqsEtaleObjects f g hu hv hw)
        hE.2.1 (n + 1) (fun i ↦ E.X (A i)) (fun i ↦ E.f (A i)) (fun i ↦ hE.2.2.1 (A i))⟩)
    (fun U hU R hR ↦ by
      have := hU.1
      obtain ⟨E, hfin, haff, hE, hle⟩ := exists_finite_isAffine_covering_le U R hR
      exact ⟨E, ⟨hfin, hU, fun i ↦ have := haff i; mem_qcqsEtaleObjects_of_isAffine _, hE⟩,
        hle⟩)
    p U hU F

end QCQSObjects

section HigherDirectImage

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]

/-- The base change along a quasi-compact and quasi-separated `f : X ⟶ Y` of an object of the
small étale site of `Y` with affine underlying scheme has quasi-compact and quasi-separated
underlying scheme. -/
theorem smallEtaleBaseChange_obj_mem_qcqsEtaleObjects (V : Y.Etale) [IsAffine V.left] :
    (smallEtaleBaseChange f).obj V ∈ qcqsEtaleObjects X := by
  let g : V.left ⟶ Y := V.hom
  change CompactSpace (Limits.pullback g f : Scheme.{u}) ∧
    QuasiSeparatedSpace (Limits.pullback g f : Scheme.{u})
  exact ⟨inferInstance, quasiSeparatedSpace_of_quasiSeparated (Limits.pullback.fst g f)⟩

/-- Every object of the small étale site is covered by objects with affine underlying scheme:
the affine open cover of its underlying scheme. -/
theorem exists_isAffine_cover (V : Y.Etale) :
    ∃ E : PreZeroHypercover.{u} V, E.sieve₀ ∈ Y.smallEtaleTopology V ∧
      ∀ i, IsAffine (E.X i).left := by
  let 𝒰 := V.left.affineCover
  have hEt (i : 𝒰.I₀) : Etale (𝒰.f i ≫ V.hom) := inferInstance
  let E : PreZeroHypercover.{u} V :=
    { I₀ := 𝒰.I₀
      X := fun i ↦ Scheme.Etale.mk (𝒰.f i ≫ V.hom)
      f := fun i ↦ MorphismProperty.Over.homMk (𝒰.f i) rfl trivial }
  refine ⟨E, ?_, fun i ↦ inferInstanceAs (IsAffine (𝒰.X i))⟩
  refine (Scheme.ofArrows_mem_smallEtaleTopology_iff _).2 ?_
  refine Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ⟨𝒰.idx x, 𝒰.covers x⟩

/-- **Higher direct images along a quasi-compact and quasi-separated morphism commute with
filtered colimits.** For a quasi-compact and quasi-separated `f : X ⟶ Y`, every degree `p` and
every filtered index category `I`, `R^p f_*` on abelian sheaves of the small étale sites
preserves colimits of shape `I`.

By the local criterion Stacks 0H7B it suffices that over every affine `V` étale over `Y` the
cohomology of `V ×_Y X` commutes with the colimit, and `V ×_Y X` is quasi-compact and
quasi-separated. -/
@[sga "4 VI 5.1" "special case"]
theorem preservesColimitsOfShape_rightDerived_etaleAbelianDirectImage (p : ℕ)
    (I : Type (max (u + 1) v)) [SmallCategory I] [IsFiltered I] :
    PreservesColimitsOfShape I ((etaleAbelianDirectImage.{u, v} f).rightDerived p) := by
  refine ⟨fun {F} ↦ ?_⟩
  refine Cohomology.HigherDirectImage.preservesColimit_rightDerived_sheafPushforwardContinuous'
    X.smallEtaleTopology Y.smallEtaleTopology (smallEtaleBaseChange f) p F (fun V ↦ ?_)
  obtain ⟨E, hE, haff⟩ := exists_isAffine_cover V
  refine ⟨E, hE, fun i ↦ ?_⟩
  have := haff i
  have := isIso_colimit_post_rightDerived_sheafSections_of_qcqs.{v} p _
    (smallEtaleBaseChange_obj_mem_qcqsEtaleObjects f (E.X i)) F
  exact preservesColimit_of_isIso_post _ _

/-- **Higher direct images along a quasi-compact and quasi-separated morphism commute with direct
sums.** A direct sum is the filtered colimit of its finite sub-sums; the filtered colimits are
`preservesColimitsOfShape_rightDerived_etaleAbelianDirectImage` and the finite sums are additivity
of a right derived functor. -/
theorem preservesColimitsOfShape_discrete_rightDerived_etaleAbelianDirectImage (p : ℕ)
    (α : Type (max (u + 1) v)) :
    PreservesColimitsOfShape (Discrete α) ((etaleAbelianDirectImage.{u, v} f).rightDerived p) :=
  have : HasCoproducts.{max (u + 1) v}
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :=
    fun _ => hasColimitsOfShape_sheaf_smallEtaleTopology.{u, v} X _
  have : PreservesColimitsOfShape (Finset (Discrete α))
      ((etaleAbelianDirectImage.{u, v} f).rightDerived p) :=
    preservesColimitsOfShape_rightDerived_etaleAbelianDirectImage.{v} f p _
  CoproductsFromFiltered.preservesColimitsOfShape_discrete _

end HigherDirectImage

end Stacks.EtaleCohomology

end
