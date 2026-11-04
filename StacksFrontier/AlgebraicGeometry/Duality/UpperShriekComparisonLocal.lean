module

public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekPullbackComparison
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.PullbackComparisonPerfect
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.PullbackComparisonMonoidal
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.PullbackComparisonExactPairing
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullbackMonoidal
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullbackTensorIso
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.OpenBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.CompositionMonoidal
public import StacksFrontier.CategoryTheory.Monoidal.ComparisonMapComp
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekPullbackComparisonCanonicalMaps

/-!
# The map `μ_{f,K}` through the comparison map of a monoidal adjunction

The map `μ_{f,K} : Lf^*K ⊗ᴸ f^!𝒪_Y ⟶ f^!K` of [Stacks, Tag 0B6T]
(`Stacks.Duality.upperShriekCompareWithPullbackCanonical`) is, up to isomorphisms on both sides,
the restriction `Lj^*` along the open immersion of the compactification of the comparison map
`Lf̄^*K ⊗ ā(𝒪_Y) ⟶ ā(K ⊗ 𝒪_Y)` of the monoidal adjunction `Lf̄^* ⊣ Rf̄_*`
(`CategoryTheory.Adjunction.comparisonMap`). So the invertibility of `μ_{f,K}` is a statement
about that comparison map, which is where the abstract base change and composition identities of
`StacksFrontier/CategoryTheory/Monoidal/ComparisonMapBaseChange.lean` and
`StacksFrontier/CategoryTheory/Monoidal/ComparisonMapComp.lean` apply.

## Main results

* `Stacks.Duality.isIso_projectionMap_quasiCoherentDerivedAdjunction` — the projection maps of
  `Lq^* ⊣ Rq_*` are invertible wherever the projection-formula maps of [Stacks, Tag 08EU] are.
* `Stacks.Duality.isIso_map_comparisonMap_baseChange_iff` — along an open immersion of the base,
  `Y` Noetherian and `f` proper, a functor inverts the restriction of the comparison map of `f` at
  `(K, L)` exactly when it inverts the comparison map of the base change at the restrictions, for
  `L` and `K ⊗ L` bounded below ([Stacks, Tag 0B6P] with [Stacks, Tag 0A9P]).
* `Stacks.Duality.isIso_upperShriekCompareWithPullback_iff` — `μ_{f,K}` is invertible exactly when
  `Lj^*` of the comparison map of `Lf̄^* ⊣ Rf̄_*` at `(K, 𝒪_Y)` is.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open Stacks.Duality.DerivedPushforward

universe u

namespace Stacks.Duality

section Projection

variable {X Y : Scheme.{u}} (q : X ⟶ Y)
  (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward q).obj K.obj)).IsQuasicoherent)
  [∀ (E : quasiCoherentDerivedCategory X) (K : quasiCoherentDerivedCategory Y),
    IsIso (projectionFormulaMap q hpush
      (quasiCoherentDerivedPullbackTensorIso q).hom E K)]

/-- **The projection maps of `Lq^* ⊣ Rq_*` on `D_QCoh` are invertible** wherever the
projection-formula maps of [Stacks, Tag 08EU] built from the tensor comparison of `Lq^*` are. -/
instance isIso_projectionMap_quasiCoherentDerivedAdjunction (K : quasiCoherentDerivedCategory Y)
    (E : quasiCoherentDerivedCategory X) :
    IsIso ((quasiCoherentDerivedAdjunction q (isQuasicoherent_homology_derivedPullback' q)
      hpush).projectionMap K E) :=
  isIso_projectionMap_of_isIso_projectionFormulaMap q hpush _
    (quasiCoherentDerivedPullbackTensorIso_hom_app q) K E

end Projection

/-- A composite of five morphisms whose outer four are invertible is invertible exactly when the
middle one is. -/
private lemma isIso_comp₅_iff {C : Type*} [Category C] {A B C' D E F : C} (a : A ⟶ B)
    (b : B ⟶ C') (c : C' ⟶ D) (d : D ⟶ E) (e : E ⟶ F) [IsIso a] [IsIso b] [IsIso d] [IsIso e] :
    IsIso (a ≫ (b ≫ c ≫ d) ≫ e) ↔ IsIso c := by
  rw [isIso_comp_left_iff, isIso_comp_right_iff, isIso_comp_left_iff, isIso_comp_right_iff]

section BaseChange

variable {U X V Y : Scheme.{u}} (j' : U ⟶ X) (f' : U ⟶ V) (f : X ⟶ Y) (j : V ⟶ Y)
  [IsOpenImmersion j] [IsNoetherian Y] [IsProper f]

/-- **Invertibility of the comparison map is compatible with restriction to an open of the
base** ([Stacks, Tag 0B6P] read through [Stacks, Tag 0A9P]): for `Y` Noetherian, `f` proper and
`j : V ⟶ Y` an open immersion with base change `j'`, a functor `H` out of `D_QCoh(𝒪_U)` inverts
`L(j')^*` of the comparison map `Lf^*K ⊗ a(L) ⟶ a(K ⊗ L)` exactly when it inverts the comparison
map of the base change `f'` at `(Lj^*K, Lj^*L)`, as soon as `L` and `K ⊗ L` are bounded
below. -/
theorem isIso_map_comparisonMap_baseChange_iff (sq : IsPullback j' f' f j)
    [∀ (E : quasiCoherentDerivedCategory X) (K : quasiCoherentDerivedCategory Y),
      IsIso (projectionFormulaMap f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (quasiCoherentDerivedPullbackTensorIso f).hom E K)]
    [∀ (E : quasiCoherentDerivedCategory U) (K : quasiCoherentDerivedCategory V),
      haveI := isNoetherian_of_isOpenImmersion j
      haveI : IsProper f' := MorphismProperty.of_isPullback sq inferInstance
      IsIso (projectionFormulaMap f' (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
        (quasiCoherentDerivedPullbackTensorIso f').hom E K)]
    {E : Type*} [Category E] (H : quasiCoherentDerivedCategory U ⥤ E)
    (K L : quasiCoherentDerivedCategory Y) (hL : DerivedCategoryB.IsBoundedBelow L.obj)
    (hKL : DerivedCategoryB.IsBoundedBelow (K ⊗ L).obj) :
    haveI := isNoetherian_of_isProper f
    haveI := isNoetherian_of_isOpenImmersion j
    haveI : IsProper f' := MorphismProperty.of_isPullback sq inferInstance
    haveI := isNoetherian_of_isProper f'
    IsIso (H.map ((quasiCoherentDerivedPullback' j').map
        ((quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).comparisonMap
          (twistedInverseImageAdjunction f
            (isQuasicoherent_homology_derivedPushforward_of_qcqs f)) K L))) ↔
      IsIso (H.map ((quasiCoherentDerivedAdjunction f'
          (isQuasicoherent_homology_derivedPullback' f')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f')).comparisonMap
          (twistedInverseImageAdjunction f'
            (isQuasicoherent_homology_derivedPushforward_of_qcqs f'))
          ((quasiCoherentDerivedPullback' j).obj K)
          ((quasiCoherentDerivedPullback' j).obj L))) := by
  have : IsOpenImmersion j' := MorphismProperty.of_isPullback sq.flip inferInstance
  have := isNoetherian_of_isProper f
  have : IsProper f' := MorphismProperty.of_isPullback sq inferInstance
  have := isNoetherian_of_isOpenImmersion j
  have := isNoetherian_of_isProper f'
  have := isIso_twoSquare_of_isOpenImmersion j' f' f j sq
  have := isIso_rightAdjointBaseChange_app_of_isOpenImmersion j' f' f j sq L hL
  have := isIso_rightAdjointBaseChange_app_of_isOpenImmersion j' f' f j sq (K ⊗ L) hKL
  have δ_isIso : ∀ {P Q : Scheme.{u}} (g : P ⟶ Q) (A B : quasiCoherentDerivedCategory Q),
      IsIso (Functor.OplaxMonoidal.δ (quasiCoherentDerivedPullback' g) A B) := fun g A B =>
    ⟨⟨Functor.LaxMonoidal.μ _ _ _, Functor.Monoidal.δ_μ _ _ _, Functor.Monoidal.μ_δ _ _ _⟩⟩
  have := δ_isIso j
  have := δ_isIso j'
  have : NatTrans.IsMonoidal
      (quasiCoherentDerivedPullbackCompIso j' f ≪≫ quasiCoherentDerivedPullbackCongr sq.w).hom :=
    inferInstanceAs (NatTrans.IsMonoidal ((quasiCoherentDerivedPullbackCompIso j' f).hom ≫
      (quasiCoherentDerivedPullbackCongr sq.w).hom))
  exact Stacks.CategoryTheory.BaseChange.isIso_map_comparisonMap_iff
    (quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
    (quasiCoherentDerivedAdjunction f' (isQuasicoherent_homology_derivedPullback' f')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f'))
    (quasiCoherentDerivedAdjunction j (isQuasicoherent_homology_derivedPullback' j)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs j))
    (quasiCoherentDerivedAdjunction j' (isQuasicoherent_homology_derivedPullback' j')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs j'))
    (quasiCoherentDerivedPullbackCompIso f' j)
    (quasiCoherentDerivedPullbackCompIso j' f ≪≫ quasiCoherentDerivedPullbackCongr sq.w)
    (Stacks.CategoryTheory.BaseChange.squareComposite_δ_compat _ _
      (NatTrans.IsMonoidal.δ_comp_tensorHom (quasiCoherentDerivedPullbackCompIso f' j).hom)
      (NatTrans.IsMonoidal.δ_comp_tensorHom
        (quasiCoherentDerivedPullbackCompIso j' f ≪≫ quasiCoherentDerivedPullbackCongr sq.w).hom))
    (twistedInverseImageAdjunction f (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
    (twistedInverseImageAdjunction f' (isQuasicoherent_homology_derivedPushforward_of_qcqs f'))
    H K L

end BaseChange

section Mu

variable {S : Scheme.{u}} {X Y : AlgebraicGeometry.FTS S} (f : X ⟶ Y)
  (j : AlgebraicGeometry.CompactificationOf (Over.mk f.left)) [CompactSpace S]
  [QuasiSeparatedSpace S]

/-- **`μ_{f,K}` is invertible exactly when `Lj^*` of the comparison map of the monoidal
adjunction `Lf̄^* ⊣ Rf̄_*` at `(K, 𝒪_Y)` is.** The other factors of `μ_{f,K}` — the composition
formula for derived pullback, the monoidality of `Lj^*`, the identification of `⊗ᴸ` with the
tensor product of `D_QCoh` and the right unitor — are isomorphisms. -/
theorem isIso_upperShriekCompareWithPullback_iff (K : quasiCoherentDerivedCategory Y.left) :
    IsIso (upperShriekCompareWithPullbackCanonical f j K) ↔
      IsIso ((quasiCoherentDerivedPullback' j.immersion).map
        ((quasiCoherentDerivedAdjunction j.toBase (isQuasicoherent_homology_derivedPullback' _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs j.toBase)).comparisonMap
          (twistedInverseImageAdjunction j.toBase
            (isQuasicoherent_homology_derivedPushforward_of_qcqs j.toBase))
          K (derivedStructureSheaf Y.left))) := by
  have e := compareWithPullbackTensor_eq_comparisonMap j.toBase
    (isQuasicoherent_homology_derivedPushforward_of_qcqs j.toBase)
    (quasiCoherentDerivedPullbackTensorIso j.toBase).hom
    (quasiCoherentDerivedPullbackTensorIso_hom_app j.toBase)
    (twistedInverseImageAdjunction j.toBase
      (isQuasicoherent_homology_derivedPushforward_of_qcqs j.toBase))
    K (derivedStructureSheaf Y.left)
  have : IsIso (((quasiCoherentDerivedTensorIsoCurriedTensor Y.left).inv.app K).app
      (derivedStructureSheaf Y.left)) :=
    (((quasiCoherentDerivedTensorIsoCurriedTensor Y.left).app K).symm.app _).isIso_hom
  have : IsIso (((quasiCoherentDerivedTensorIsoCurriedTensor j.space).hom.app
      ((quasiCoherentDerivedPullback' j.toBase).obj K)).app
        ((twistedInverseImage j.toBase
          (isQuasicoherent_homology_derivedPushforward_of_qcqs j.toBase)).obj
            (derivedStructureSheaf Y.left))) :=
    (((quasiCoherentDerivedTensorIsoCurriedTensor j.space).app _).app _).isIso_hom
  have : IsIso ((quasiCoherentDerivedTensorRightUnitor Y.left).hom.app K) :=
    ((quasiCoherentDerivedTensorRightUnitor Y.left).app K).isIso_hom
  simp only [upperShriekCompareWithPullbackCanonical, twistedInverseImageCompareWithPullback,
    compareWithPullback, e, Functor.map_comp, isIso_comp_left_iff]
  refine @isIso_comp₅_iff _ _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_
  · exact ((quasiCoherentDerivedPullbackTensorIso j.immersion).app _).isIso_inv
  · infer_instance
  · infer_instance
  · exact ((quasiCoherentDerivedPullback' j.immersion).mapIso
      ((twistedInverseImage j.toBase
        (isQuasicoherent_homology_derivedPushforward_of_qcqs j.toBase)).mapIso
          ((quasiCoherentDerivedTensorRightUnitor Y.left).app K))).isIso_hom

end Mu

end Stacks.Duality

end
