module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.AffineConservative
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullbackBraided
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.ProjectionFormulaQuasiCoherent
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.PullbackComparison
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.OpenBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.TorIndependentBaseChangeIsIso
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.CompositionMonoidal
public import StacksFrontier.CategoryTheory.Adjunction.PushedForwardMonoidalBaseChange

/-!
# The base change map of the twisted inverse image over an affine base

For a cartesian square of quasi-compact and quasi-separated schemes with `g` affine and `f`, `g`
Tor independent, the base change map `L(g')^* a(K) ⟶ a'(Lg^*K)` of [Stacks, Tag 0AA6] is
identified, after `Rg'_*`, with the comparison map `Lf^*J ⊗ᴸ a(K) ⟶ a(J ⊗ᴸ K)` of
[Stacks, Tag 0A9S] at `J = Rg_*𝒪_{Y'}`; since `Rg'_*` reflects isomorphisms, the base change map
is invertible at `K` as soon as that comparison map is. This is the reduction behind
[Stacks, Tag 0AA8].

## Main results

* `Stacks.Duality.twistedInverseImageBaseChangeMap_eq_rightAdjointBaseChange` — the map
  `L(g')^* ∘ a ⟶ a' ∘ Lg^*` is the abstract
  `Stacks.CategoryTheory.BaseChange.rightAdjointBaseChange`.
* `Stacks.Duality.isIso_twistedInverseImageBaseChangeMap_app_of_isIso_compareWithPullbackTensor`
  — the base change map is invertible at `K` once the comparison map at `J = Rg_*𝒪_{Y'}` is.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace Stacks.Duality


section Reduction

variable {X' X Y' Y : Scheme.{u}} [CompactSpace X'] [QuasiSeparatedSpace X'] [CompactSpace X]
  [QuasiSeparatedSpace X] [CompactSpace Y'] [QuasiSeparatedSpace Y'] [CompactSpace Y]
  [QuasiSeparatedSpace Y] {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- Inverses of equal isomorphisms agree. -/
private theorem inv_eq_inv_of_eq {C : Type*} [Category C] {A B : C} {p q : A ⟶ B} (h : p = q)
    [IsIso p] [IsIso q] : inv p = inv q := by
  subst h; rfl

/-- **The base change map `L(g')^* ∘ a ⟶ a' ∘ Lg^*` of [Stacks, Tag 0AA6] is the abstract
`rightAdjointBaseChange`**: the inverse mate of the inverse of
`Stacks.Duality.twistedInverseImagePushforwardBaseChange`. -/
theorem twistedInverseImageBaseChangeMap_eq_rightAdjointBaseChange (sq : IsPullback g' f' f g)
    [IsIso (twistedInverseImagePushforwardBaseChange g' f' f g
      (isQuasicoherent_homology_derivedPushforward_of_qcqs g')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs g) sq)]
    [IsIso (Stacks.CategoryTheory.BaseChange.rightAdjointSquare
        (quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
        (quasiCoherentDerivedAdjunction f' (isQuasicoherent_homology_derivedPullback' f')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f'))
        (quasiCoherentDerivedAdjunction g (isQuasicoherent_homology_derivedPullback' g)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs g))
        (quasiCoherentDerivedAdjunction g' (isQuasicoherent_homology_derivedPullback' g')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs g'))
        (quasiCoherentDerivedPullbackCompIso f' g)
        (quasiCoherentDerivedPullbackCompIso g' f ≪≫ quasiCoherentDerivedPullbackCongr sq.w)
        (twistedInverseImageAdjunction f (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
        (twistedInverseImageAdjunction f'
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f')))] :
    twistedInverseImageBaseChangeMap g' f' f g
        (isQuasicoherent_homology_derivedPushforward_of_qcqs g')
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
        (isQuasicoherent_homology_derivedPushforward_of_qcqs g)
        sq =
      (Stacks.CategoryTheory.BaseChange.rightAdjointBaseChange
        (quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
        (quasiCoherentDerivedAdjunction f' (isQuasicoherent_homology_derivedPullback' f')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f'))
        (quasiCoherentDerivedAdjunction g (isQuasicoherent_homology_derivedPullback' g)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs g))
        (quasiCoherentDerivedAdjunction g' (isQuasicoherent_homology_derivedPullback' g')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs g'))
        (quasiCoherentDerivedPullbackCompIso f' g)
        (quasiCoherentDerivedPullbackCompIso g' f ≪≫ quasiCoherentDerivedPullbackCongr sq.w)
        (twistedInverseImageAdjunction f (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
        (twistedInverseImageAdjunction f'
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f'))) := by
  have hinv := inv_eq_inv_of_eq
    (twistedInverseImagePushforwardBaseChange_eq_rightAdjointSquare g' f' f g sq)
  ext K
  simp only [twistedInverseImageBaseChangeMap,
    Stacks.CategoryTheory.BaseChange.rightAdjointBaseChange, mateEquiv, Equiv.coe_fn_symm_mk,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.leftUnitor_inv_app,
    Functor.rightUnitor_hom_app, Functor.comp_obj, Functor.id_obj, Category.id_comp,
    Category.comp_id, hinv]
  simp only [Functor.comp_map, CategoryTheory.Functor.map_id, Category.id_comp]

omit [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y] in
/-- The two-variable comparison of `Stacks.CategoryTheory.BaseChange.rightAdjointTensorComparison`
for the swapped derived tensor products is `Stacks.Duality.compareWithPullbackTensor`. -/
theorem rightAdjointTensorComparison_eq_compareWithPullbackTensor
    (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
    (α : quasiCoherentDerivedTensorSwap Y ⋙ quasiCoherentDerivedPullback' f ⟶
      (quasiCoherentDerivedPullback' f).prod (quasiCoherentDerivedPullback' f) ⋙
        quasiCoherentDerivedTensorSwap X)
    [∀ (E : quasiCoherentDerivedCategory X) (K : quasiCoherentDerivedCategory Y),
      IsIso (projectionFormulaMap f hpush α E K)]
    {a : quasiCoherentDerivedCategory Y ⥤ quasiCoherentDerivedCategory X}
    (adj : quasiCoherentDerivedPushforward f hpush ⊣ a) (K H : quasiCoherentDerivedCategory Y) :
    haveI : IsIso (adjunctionTensorMap
        (quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f) hpush)
        (quasiCoherentDerivedTensorSwap Y) (quasiCoherentDerivedTensorSwap X) α (a.obj K) H) :=
      inferInstanceAs (IsIso (projectionFormulaMap f hpush α (a.obj K) H))
    Stacks.CategoryTheory.BaseChange.rightAdjointTensorComparison
        (quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f) hpush) adj
        (quasiCoherentDerivedTensorSwap Y) (quasiCoherentDerivedTensorSwap X) α K H =
      compareWithPullbackTensor f hpush α adj H K := by
  unfold Stacks.CategoryTheory.BaseChange.rightAdjointTensorComparison compareWithPullbackTensor
  congr 2
  change ((quasiCoherentDerivedTensor Y).map (𝟙 H)).app _ ≫
    ((quasiCoherentDerivedTensor Y).obj H).map (adj.counit.app K) = _
  rw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]

/-- **The reduction of [Stacks, Tag 0AA8].** For a cartesian square of quasi-compact and
quasi-separated schemes with `g` affine and `f`, `g` Tor independent, the base change map
`L(g')^* a(K) ⟶ a'(Lg^*K)` of [Stacks, Tag 0AA6] is invertible at `K` as soon as the comparison
map `Lf^*J ⊗ᴸ a(K) ⟶ a(J ⊗ᴸ K)` of [Stacks, Tag 0A9S] is, for `J = Rg_*𝒪_{Y'}`. -/
theorem isIso_twistedInverseImageBaseChangeMap_app_of_isIso_compareWithPullbackTensor
    (sq : IsPullback g' f' f g) [IsAffineHom g] (hTor : TorIndependent f g)
    (K : quasiCoherentDerivedCategory Y)
    (hK : IsIso (compareWithPullbackTensor f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (quasiCoherentDerivedPullbackTensorIso f).hom
        (twistedInverseImageAdjunction f (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
        ((quasiCoherentDerivedPushforward g
          (isQuasicoherent_homology_derivedPushforward_of_qcqs g)).obj
          (𝟙_ (quasiCoherentDerivedCategory Y'))) K)) :
    haveI := isIso_twistedInverseImagePushforwardBaseChange_of_torIndependent sq hTor
    IsIso ((twistedInverseImageBaseChangeMap g' f' f g
      (isQuasicoherent_homology_derivedPushforward_of_qcqs g')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs g)
      sq).app K) := by
  have := isIso_twistedInverseImagePushforwardBaseChange_of_torIndependent sq hTor
  have : IsAffineHom g' := MorphismProperty.of_isPullback sq.flip inferInstance
  let hpg' := isQuasicoherent_homology_derivedPushforward_of_qcqs g'
  let hpf := isQuasicoherent_homology_derivedPushforward_of_qcqs f
  let hpf' := isQuasicoherent_homology_derivedPushforward_of_qcqs f'
  let hpg := isQuasicoherent_homology_derivedPushforward_of_qcqs g
  let adjf := quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f) hpf
  let adjf' := quasiCoherentDerivedAdjunction f' (isQuasicoherent_homology_derivedPullback' f') hpf'
  let adjg := quasiCoherentDerivedAdjunction g (isQuasicoherent_homology_derivedPullback' g) hpg
  let adjg' := quasiCoherentDerivedAdjunction g' (isQuasicoherent_homology_derivedPullback' g') hpg'
  let eg := quasiCoherentDerivedPullbackCompIso f' g
  let ef := quasiCoherentDerivedPullbackCompIso g' f ≪≫ quasiCoherentDerivedPullbackCongr sq.w
  let adja := twistedInverseImageAdjunction f hpf
  let adja' := twistedInverseImageAdjunction f' hpf'
  let eY := quasiCoherentDerivedTensorIsoCurriedTensor Y
  let eX := quasiCoherentDerivedTensorIsoCurriedTensor X
  let eY' := quasiCoherentDerivedTensorIsoCurriedTensor Y'
  let eX' := quasiCoherentDerivedTensorIsoCurriedTensor X'
  have : NatTrans.IsMonoidal ef.hom :=
    inferInstanceAs (NatTrans.IsMonoidal ((quasiCoherentDerivedPullbackCompIso g' f).hom ≫
      (quasiCoherentDerivedPullbackCongr sq.w).hom))
  have hbc : IsIso (Stacks.CategoryTheory.BaseChange.twoSquare adjf adjf' eg ef) := by
    have h := isIso_quasiCoherentDerivedBaseChange_natTrans hpg' hpf hpf' hpg sq hTor
    rwa [quasiCoherentDerivedBaseChange_eq_twoSquare] at h
  have := Stacks.CategoryTheory.BaseChange.isIso_rightAdjointSquare adjf adjf' adjg adjg' eg ef
    adja adja'
  have hPf : ∀ (E : quasiCoherentDerivedCategory X) (H : quasiCoherentDerivedCategory Y),
      IsIso (adjunctionTensorMap adjf (quasiCoherentDerivedTensorSwap Y)
        (quasiCoherentDerivedTensorSwap X) (quasiCoherentDerivedPullbackTensorIso f).hom E H) :=
    fun E H => isIso_projectionFormulaMap_of_qcqs f E H
  have hPg : ∀ (M : quasiCoherentDerivedCategory Y),
      IsIso (adjunctionTensorMap adjg (quasiCoherentDerivedTensorSwap Y)
        (quasiCoherentDerivedTensorSwap Y')
        (Functor.Monoidal.swapTensorIso (quasiCoherentDerivedPullback' g) eY eY').hom
        (𝟙_ (quasiCoherentDerivedCategory Y')) M) :=
    fun M => isIso_projectionFormulaMap_of_qcqs g _ M
  have hPg' : ∀ (M : quasiCoherentDerivedCategory X),
      IsIso (adjunctionTensorMap adjg' (quasiCoherentDerivedTensorSwap X)
        (quasiCoherentDerivedTensorSwap X')
        (Functor.Monoidal.swapTensorIso (quasiCoherentDerivedPullback' g') eX eX').hom
        (𝟙_ (quasiCoherentDerivedCategory X')) M) :=
    fun M => isIso_projectionFormulaMap_of_qcqs g' _ M
  have := isIso_quasiCoherentTransposedUnitBaseChange hpg' hpg sq hTor
    (𝟙_ (quasiCoherentDerivedCategory Y')) (𝟙_ (quasiCoherentDerivedCategory X'))
    (Functor.OplaxMonoidal.η (quasiCoherentDerivedPullback' f'))
  have : IsIso (Stacks.CategoryTheory.BaseChange.unitProjection adjg
      (quasiCoherentDerivedTensorSwap Y') (quasiCoherentDerivedTensorSwap Y)
      (quasiCoherentDerivedPullbackTensorIso g).hom (𝟙_ (quasiCoherentDerivedCategory Y'))
      (Stacks.CategoryTheory.BaseChange.swapLeftUnitor eY') K) :=
    Stacks.CategoryTheory.BaseChange.isIso_unitProjection_of_isIso eY eY' adjg
      (fun P Q => (quasiCoherentDerivedPullback_δ_braiding g P Q).symm) K
  have : IsIso (Stacks.CategoryTheory.BaseChange.unitProjection adjg'
      (quasiCoherentDerivedTensorSwap X') (quasiCoherentDerivedTensorSwap X)
      (quasiCoherentDerivedPullbackTensorIso g').hom (𝟙_ (quasiCoherentDerivedCategory X'))
      (Stacks.CategoryTheory.BaseChange.swapLeftUnitor eX') ((twistedInverseImage f hpf).obj K)) :=
    Stacks.CategoryTheory.BaseChange.isIso_unitProjection_of_isIso eX eX' adjg'
      (fun P Q => (quasiCoherentDerivedPullback_δ_braiding g' P Q).symm)
      ((twistedInverseImage f hpf).obj K)
  have : IsIso (Stacks.CategoryTheory.BaseChange.rightAdjointTensorComparison adjf adja
      (quasiCoherentDerivedTensorSwap Y) (quasiCoherentDerivedTensorSwap X)
      (quasiCoherentDerivedPullbackTensorIso f).hom K
      ((quasiCoherentDerivedPushforward g hpg).obj (𝟙_ (quasiCoherentDerivedCategory Y')))) := by
    rw [rightAdjointTensorComparison_eq_compareWithPullbackTensor]
    exact hK
  have hmain := Stacks.CategoryTheory.BaseChange.isIso_map_rightAdjointBaseChange adjf adjf' adjg
    adjg' eg ef adja adja' (quasiCoherentDerivedTensorSwap Y) (quasiCoherentDerivedTensorSwap Y')
    (quasiCoherentDerivedTensorSwap X) (quasiCoherentDerivedTensorSwap X')
    (quasiCoherentDerivedPullbackTensorIso f).hom (quasiCoherentDerivedPullbackTensorIso f').hom
    (quasiCoherentDerivedPullbackTensorIso g).hom (quasiCoherentDerivedPullbackTensorIso g').hom
    (𝟙_ (quasiCoherentDerivedCategory Y')) (Stacks.CategoryTheory.BaseChange.swapLeftUnitor eY')
    (𝟙_ (quasiCoherentDerivedCategory X')) (Stacks.CategoryTheory.BaseChange.swapLeftUnitor eX')
    (Functor.OplaxMonoidal.η (quasiCoherentDerivedPullback' f')) K
    (Stacks.CategoryTheory.BaseChange.tensorComparisonCompatible_swapTensorIso eY eX eY' eX' eg ef
      _ _)
    (fun P => Stacks.CategoryTheory.BaseChange.swapTensorIso_comp_map_swapLeftUnitor eY' eX'
      (quasiCoherentDerivedPullback' f') P)
  have : IsIso ((derivedPushforward g').map
      ((Stacks.CategoryTheory.BaseChange.rightAdjointBaseChange adjf adjf' adjg adjg' eg ef adja
        adja').app K).hom) :=
    inferInstanceAs (IsIso ((ObjectProperty.ι _).map ((quasiCoherentDerivedPushforward g' hpg').map
      ((Stacks.CategoryTheory.BaseChange.rightAdjointBaseChange adjf adjf' adjg adjg' eg ef adja
        adja').app K))))
  rw [twistedInverseImageBaseChangeMap_eq_rightAdjointBaseChange sq]
  exact isIso_of_isIso_derivedPushforward_map_of_isAffineHom g' _

end Reduction

end Stacks.Duality
