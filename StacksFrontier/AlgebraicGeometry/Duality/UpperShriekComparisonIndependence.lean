module

public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekComparisonLocal
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.ClosureCompactification
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.CompactificationMap

/-!
# Invertibility of `μ_{f,K}` does not depend on the compactification

Let `g : X̄₁ ⟶ X̄₂` be a proper morphism of compactifications of `X` over `Y` with `g⁻¹(X) = X`.
The comparison map `Lf̄^*K ⊗ ā(L) ⟶ ā(K ⊗ L)` of the monoidal adjunction `Lf̄^* ⊣ Rf̄_*`
(`CategoryTheory.Adjunction.comparisonMap`) becomes invertible on `X` for `f̄₁` exactly when it
does for `f̄₂`, for `L` and `K ⊗ L` bounded below. This is the part of the proof of
[Stacks, Tag 0B6T] showing that `μ_{f,K}` does not depend on the compactification, read for
invertibility: [Stacks, Tag 0B6R] writes the comparison map of `f̄₁ = f̄₂ ∘ g` through those of
`g` and `f̄₂`, and [Stacks, Tag 0B6P] along the open `X ⊆ X̄₂`, over which `g` is the identity,
compares the comparison map of `g` with that of the identity of `X`, which is invertible.

Unlike the source, which uses [Stacks, Tag 0B6Q] at the object `Lf̄₂^*K ⊗ ā₂(𝒪_Y)`, the argument
uses the base change map of [Stacks, Tag 0A9L] only at the bounded below objects `ā₂(L)` and
`ā₂(K ⊗ L)`, where [Stacks, Tag 0A9P] makes it invertible.

## Main results

* `Stacks.Duality.isIso_map_comparisonMap_congr` — equal morphisms have the same comparison maps.
* `Stacks.Duality.isIso_map_comparisonMap_comp_iff` — the comparison map of a composite `g ≫ q`
  is invertible after a functor exactly when that of the composite adjunction is.
* `Stacks.Duality.isIso_map_comparisonMap_iff_of_compactificationMap` — the independence of the
  compactification.
* `Stacks.Duality.isIso_map_comparisonMap_of_closedInOpen` — the comparison map on `U` at the
  compactification of `U` by closure in a proper `P`, from those of `π : P ⟶ V` and of the closed
  immersion `U ⟶ A ⊆ P`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace Stacks.Duality

/-- **Equal morphisms have the same comparison maps**, after any functor. -/
theorem isIso_map_comparisonMap_congr {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y] {q q' : X ⟶ Y} (h : q = q')
    [∀ (E : quasiCoherentDerivedCategory X) (K : quasiCoherentDerivedCategory Y),
      IsIso (projectionFormulaMap q (isQuasicoherent_homology_derivedPushforward_of_qcqs q)
        (quasiCoherentDerivedPullbackTensorIso q).hom E K)]
    [∀ (E : quasiCoherentDerivedCategory X) (K : quasiCoherentDerivedCategory Y),
      IsIso (projectionFormulaMap q' (isQuasicoherent_homology_derivedPushforward_of_qcqs q')
        (quasiCoherentDerivedPullbackTensorIso q').hom E K)]
    {E : Type*} [Category E] (H : quasiCoherentDerivedCategory X ⥤ E)
    (K L : quasiCoherentDerivedCategory Y) :
    IsIso (H.map ((quasiCoherentDerivedAdjunction q (isQuasicoherent_homology_derivedPullback' q)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs q)).comparisonMap
        (twistedInverseImageAdjunction q (isQuasicoherent_homology_derivedPushforward_of_qcqs q))
          K L)) ↔
      IsIso (H.map ((quasiCoherentDerivedAdjunction q'
        (isQuasicoherent_homology_derivedPullback' q')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs q')).comparisonMap
        (twistedInverseImageAdjunction q' (isQuasicoherent_homology_derivedPushforward_of_qcqs q'))
          K L)) := by
  subst h; rfl

section Comp

variable {Z X Y : Scheme.{u}} (g : Z ⟶ X) (q : X ⟶ Y) [CompactSpace Z] [QuasiSeparatedSpace Z]
  [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
  [∀ (E : quasiCoherentDerivedCategory Z) (K : quasiCoherentDerivedCategory X),
    IsIso (projectionFormulaMap g (isQuasicoherent_homology_derivedPushforward_of_qcqs g)
      (quasiCoherentDerivedPullbackTensorIso g).hom E K)]
  [∀ (E : quasiCoherentDerivedCategory X) (K : quasiCoherentDerivedCategory Y),
    IsIso (projectionFormulaMap q (isQuasicoherent_homology_derivedPushforward_of_qcqs q)
      (quasiCoherentDerivedPullbackTensorIso q).hom E K)]
  [∀ (E : quasiCoherentDerivedCategory Z) (K : quasiCoherentDerivedCategory Y),
    IsIso (projectionFormulaMap (g ≫ q)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (g ≫ q))
      (quasiCoherentDerivedPullbackTensorIso (g ≫ q)).hom E K)]

/-- **The comparison map of `g ≫ q` is that of the composite adjunction**, up to the
identification of the twisted inverse images, for invertibility after any functor
([Stacks, Tag 0B6R] with the composition formulas for `Lh^*`, `Rh_*` and `a_h`). -/
theorem isIso_map_comparisonMap_comp_iff {E : Type*} [Category E]
    (H : quasiCoherentDerivedCategory Z ⥤ E) (K L : quasiCoherentDerivedCategory Y) :
    IsIso (H.map ((quasiCoherentDerivedAdjunction (g ≫ q)
        (isQuasicoherent_homology_derivedPullback' (g ≫ q))
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (g ≫ q))).comparisonMap
        (twistedInverseImageAdjunction (g ≫ q)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs (g ≫ q))) K L)) ↔
      IsIso (H.map (((quasiCoherentDerivedAdjunction q (isQuasicoherent_homology_derivedPullback' q)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs q)).comp
        (quasiCoherentDerivedAdjunction g (isQuasicoherent_homology_derivedPullback' g)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs g))).comparisonMap
        ((twistedInverseImageAdjunction g
          (isQuasicoherent_homology_derivedPushforward_of_qcqs g)).comp
          (twistedInverseImageAdjunction q
            (isQuasicoherent_homology_derivedPushforward_of_qcqs q))) K L)) := by
  rw [Adjunction.isIso_map_comparisonMap_iff_of_iso
    ((quasiCoherentDerivedAdjunction q (isQuasicoherent_homology_derivedPullback' q)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs q)).comp
      (quasiCoherentDerivedAdjunction g (isQuasicoherent_homology_derivedPullback' g)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs g)))
    (quasiCoherentDerivedAdjunction (g ≫ q) (isQuasicoherent_homology_derivedPullback' (g ≫ q))
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (g ≫ q)))
    (quasiCoherentDerivedPullbackCompIso g q)
    (NatTrans.IsMonoidal.δ_comp_tensorHom (quasiCoherentDerivedPullbackCompIso g q).hom),
    H.map_comp, isIso_comp_right_iff]

end Comp

/-- The comparison map of `f ≫ p` restricted along the base change `j'` of an open immersion `j`
is invertible exactly when `f'^×` inverts the restriction by `j` of that of `p`, for the base
change `f'` of a proper `f` over a Noetherian `Y`, with `L` and `K ⊗ L` bounded below. -/
private theorem isIso_map_pullback_comparisonMap_comp_iff {U V X Y B : Scheme.{u}}
    [CompactSpace U] [QuasiSeparatedSpace U] [CompactSpace V] [QuasiSeparatedSpace V]
    [CompactSpace X] [QuasiSeparatedSpace X] [QuasiSeparatedSpace Y] [CompactSpace B]
    [QuasiSeparatedSpace B] {j' : U ⟶ X} {f' : U ⟶ V} {f : X ⟶ Y} {j : V ⟶ Y}
    (p : Y ⟶ B) (sq : IsPullback j' f' f j) [IsOpenImmersion j] [IsNoetherian Y]
    [IsProper f]
    [∀ (E : quasiCoherentDerivedCategory X) (K : quasiCoherentDerivedCategory Y),
      IsIso (projectionFormulaMap f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (quasiCoherentDerivedPullbackTensorIso f).hom E K)]
    [∀ (E : quasiCoherentDerivedCategory Y) (K : quasiCoherentDerivedCategory B),
      IsIso (projectionFormulaMap p (isQuasicoherent_homology_derivedPushforward_of_qcqs p)
        (quasiCoherentDerivedPullbackTensorIso p).hom E K)]
    [∀ (E : quasiCoherentDerivedCategory X) (K : quasiCoherentDerivedCategory B),
      IsIso (projectionFormulaMap (f ≫ p)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (f ≫ p))
        (quasiCoherentDerivedPullbackTensorIso (f ≫ p)).hom E K)]
    [∀ (E : quasiCoherentDerivedCategory U) (K : quasiCoherentDerivedCategory V),
      IsIso (projectionFormulaMap f' (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
        (quasiCoherentDerivedPullbackTensorIso f').hom E K)]
    [∀ A C : quasiCoherentDerivedCategory V,
      IsIso ((quasiCoherentDerivedAdjunction f' (isQuasicoherent_homology_derivedPullback' f')
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f')).comparisonMap
        (twistedInverseImageAdjunction f'
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f')) A C)]
    (K L : quasiCoherentDerivedCategory B) (hL : DerivedCategoryB.IsBoundedBelow L.obj)
    (hKL : DerivedCategoryB.IsBoundedBelow (K ⊗ L).obj) :
    IsIso ((quasiCoherentDerivedPullback' j').map
        ((quasiCoherentDerivedAdjunction (f ≫ p)
          (isQuasicoherent_homology_derivedPullback' (f ≫ p))
          (isQuasicoherent_homology_derivedPushforward_of_qcqs (f ≫ p))).comparisonMap
          (twistedInverseImageAdjunction (f ≫ p)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs (f ≫ p))) K L)) ↔
      IsIso ((twistedInverseImage f' (isQuasicoherent_homology_derivedPushforward_of_qcqs f')).map
        ((quasiCoherentDerivedPullback' j).map
          ((quasiCoherentDerivedAdjunction p (isQuasicoherent_homology_derivedPullback' p)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs p)).comparisonMap
            (twistedInverseImageAdjunction p
              (isQuasicoherent_homology_derivedPushforward_of_qcqs p)) K L))) := by
  have : IsOpenImmersion j' := MorphismProperty.of_isPullback sq.flip inferInstance
  have := isNoetherian_of_isProper f
  have : IsProper f' := MorphismProperty.of_isPullback sq inferInstance
  have := isNoetherian_of_isOpenImmersion j
  have := isNoetherian_of_isProper f'
  rw [isIso_map_comparisonMap_comp_iff f p]
  have : NatTrans.IsMonoidal
      (quasiCoherentDerivedPullbackCompIso j' f ≪≫ quasiCoherentDerivedPullbackCongr sq.w).hom :=
    inferInstanceAs (NatTrans.IsMonoidal ((quasiCoherentDerivedPullbackCompIso j' f).hom ≫
      (quasiCoherentDerivedPullbackCongr sq.w).hom))
  have := isIso_twoSquare_of_isOpenImmersion j' f' f j sq
  have : ∀ A C : quasiCoherentDerivedCategory Y,
      IsIso (Functor.OplaxMonoidal.δ (quasiCoherentDerivedPullback' j) A C) := fun A C =>
    ⟨⟨Functor.LaxMonoidal.μ _ _ _, Functor.Monoidal.δ_μ _ _ _, Functor.Monoidal.μ_δ _ _ _⟩⟩
  have : ∀ A C : quasiCoherentDerivedCategory X,
      IsIso (Functor.OplaxMonoidal.δ (quasiCoherentDerivedPullback' j') A C) := fun A C =>
    ⟨⟨Functor.LaxMonoidal.μ _ _ _, Functor.Monoidal.δ_μ _ _ _, Functor.Monoidal.μ_δ _ _ _⟩⟩
  have := isIso_rightAdjointBaseChange_app_of_isOpenImmersion j' f' f j sq _
    (isBoundedBelow_twistedInverseImage_obj p L hL)
  have := isIso_rightAdjointBaseChange_app_of_isOpenImmersion j' f' f j sq _
    (isBoundedBelow_twistedInverseImage_obj p (K ⊗ L) hKL)
  exact Stacks.CategoryTheory.BaseChange.isIso_map_comparisonMap_comp_iff
    (quasiCoherentDerivedAdjunction p (isQuasicoherent_homology_derivedPullback' p)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs p))
    (twistedInverseImageAdjunction p (isQuasicoherent_homology_derivedPushforward_of_qcqs p))
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
    (twistedInverseImageAdjunction f'
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f')) K L

section CompactificationData

variable {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S] [IsNoetherian S]
  {X Y : FTS S} (f : X ⟶ Y) (c₁ c₂ : CompactificationOf (Over.mk f.left))
  (g : c₁.space ⟶ c₂.space) [IsProper g]
  [∀ (E : quasiCoherentDerivedCategory c₁.space) (K : quasiCoherentDerivedCategory Y.left),
    IsIso (projectionFormulaMap c₁.toBase
      (isQuasicoherent_homology_derivedPushforward_of_qcqs c₁.toBase)
      (quasiCoherentDerivedPullbackTensorIso c₁.toBase).hom E K)]
  [∀ (E : quasiCoherentDerivedCategory c₂.space) (K : quasiCoherentDerivedCategory Y.left),
    IsIso (projectionFormulaMap c₂.toBase
      (isQuasicoherent_homology_derivedPushforward_of_qcqs c₂.toBase)
      (quasiCoherentDerivedPullbackTensorIso c₂.toBase).hom E K)]
  [∀ (E : quasiCoherentDerivedCategory c₁.space) (K : quasiCoherentDerivedCategory c₂.space),
    IsIso (projectionFormulaMap g (isQuasicoherent_homology_derivedPushforward_of_qcqs g)
      (quasiCoherentDerivedPullbackTensorIso g).hom E K)]
  [∀ (E : quasiCoherentDerivedCategory c₁.space) (K : quasiCoherentDerivedCategory Y.left),
    IsIso (projectionFormulaMap (g ≫ c₂.toBase)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (g ≫ c₂.toBase))
      (quasiCoherentDerivedPullbackTensorIso (g ≫ c₂.toBase)).hom E K)]
  [∀ (E : quasiCoherentDerivedCategory X.left) (K : quasiCoherentDerivedCategory X.left),
    IsIso (projectionFormulaMap (𝟙 X.left)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 X.left))
      (quasiCoherentDerivedPullbackTensorIso (𝟙 X.left)).hom E K)]

/-- **Invertibility of the comparison map on `X` does not depend on the compactification**
(the independence part of the proof of [Stacks, Tag 0B6T], for invertibility): for a proper
morphism `g : X̄₁ ⟶ X̄₂` of compactifications of `X` over `Y` with `g⁻¹(X) = X`, the restriction to
`X` of the comparison map of `f̄₁` at `(K, L)` is invertible exactly when that of `f̄₂` is, for `L`
and `K ⊗ L` bounded below. -/
theorem isIso_map_comparisonMap_iff_of_compactificationMap (hg : g ≫ c₂.toBase = c₁.toBase)
    (sq : IsPullback c₁.immersion (𝟙 X.left) g c₂.immersion)
    (K L : quasiCoherentDerivedCategory Y.left) (hL : DerivedCategoryB.IsBoundedBelow L.obj)
    (hKL : DerivedCategoryB.IsBoundedBelow (K ⊗ L).obj) :
    IsIso ((quasiCoherentDerivedPullback' c₁.immersion).map
        ((quasiCoherentDerivedAdjunction c₁.toBase
          (isQuasicoherent_homology_derivedPullback' c₁.toBase)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs c₁.toBase)).comparisonMap
          (twistedInverseImageAdjunction c₁.toBase
            (isQuasicoherent_homology_derivedPushforward_of_qcqs c₁.toBase)) K L)) ↔
      IsIso ((quasiCoherentDerivedPullback' c₂.immersion).map
        ((quasiCoherentDerivedAdjunction c₂.toBase
          (isQuasicoherent_homology_derivedPullback' c₂.toBase)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs c₂.toBase)).comparisonMap
          (twistedInverseImageAdjunction c₂.toBase
            (isQuasicoherent_homology_derivedPushforward_of_qcqs c₂.toBase)) K L)) := by
  have : (quasiCoherentDerivedPushforward (𝟙 X.left)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 X.left))).IsEquivalence :=
    Functor.isEquivalence_of_iso (quasiCoherentDerivedPushforwardIdIso X.left _).symm
  have : ∀ A B : quasiCoherentDerivedCategory X.left,
      IsIso ((quasiCoherentDerivedAdjunction (𝟙 X.left)
        (isQuasicoherent_homology_derivedPullback' (𝟙 X.left))
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 X.left))).comparisonMap
        (twistedInverseImageAdjunction (𝟙 X.left)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 X.left))) A B) :=
    fun A B => Adjunction.isIso_comparisonMap_of_isEquivalence _ _ A B
  rw [isIso_map_comparisonMap_congr hg.symm,
    isIso_map_pullback_comparisonMap_comp_iff c₂.toBase sq K L hL hKL]
  exact NatIso.isIso_map_iff (twistedInverseImageIdIso X.left _) _

end CompactificationData

section ClosedInOpen

open CompactificationOf

variable {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S] {U V : FTS S} (g : U ⟶ V)
  {A P : Scheme.{u}} [IsNoetherian P] [CompactSpace A] [QuasiSeparatedSpace A]
  (π : P ⟶ V.left) [IsProper π] (a : A ⟶ P) [IsOpenImmersion a] (ι : U.left ⟶ A)
  [IsClosedImmersion ι]
  [∀ (E : quasiCoherentDerivedCategory P) (K : quasiCoherentDerivedCategory V.left),
    IsIso (projectionFormulaMap π (isQuasicoherent_homology_derivedPushforward_of_qcqs π)
      (quasiCoherentDerivedPullbackTensorIso π).hom E K)]
  [∀ (E : quasiCoherentDerivedCategory (closedInOpenImmersion a ι).image)
    (K : quasiCoherentDerivedCategory P),
    IsIso (projectionFormulaMap (closedInOpenImmersion a ι).imageι
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (closedInOpenImmersion a ι).imageι)
      (quasiCoherentDerivedPullbackTensorIso (closedInOpenImmersion a ι).imageι).hom E K)]
  [∀ (E : quasiCoherentDerivedCategory U.left) (K : quasiCoherentDerivedCategory A),
    IsIso (projectionFormulaMap ι (isQuasicoherent_homology_derivedPushforward_of_qcqs ι)
      (quasiCoherentDerivedPullbackTensorIso ι).hom E K)]
  [∀ (E : quasiCoherentDerivedCategory (closedInOpenImmersion a ι).image)
    (K : quasiCoherentDerivedCategory V.left),
    IsIso (projectionFormulaMap ((closedInOpenImmersion a ι).imageι ≫ π)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs ((closedInOpenImmersion a ι).imageι ≫ π))
      (quasiCoherentDerivedPullbackTensorIso ((closedInOpenImmersion a ι).imageι ≫ π)).hom E K)]

/-- **The comparison map at the compactification by closure in `P`**: for `g : U ⟶ V` factored
as a closed immersion `ι : U ⟶ A` into an open `A ⊆ P` of a proper `π : P ⟶ V` with `P`
Noetherian, the restriction to `U` of the comparison map of `Ū ⟶ P ⟶ V` at `(K, L)` is invertible
as soon as the comparison map of `π` at `(K, L)` and all comparison maps of `ι` are, for `L` and
`K ⊗ L` bounded below. This is the source's reduction of [Stacks, Tag 0B6U] (e) to a perfect
closed immersion and a projective space, through [Stacks, Tag 0B6R] and [Stacks, Tag 0B6P]. -/
theorem isIso_map_comparisonMap_of_closedInOpen
    (K L : quasiCoherentDerivedCategory V.left) (hL : DerivedCategoryB.IsBoundedBelow L.obj)
    (hKL : DerivedCategoryB.IsBoundedBelow (K ⊗ L).obj)
    (hπ : IsIso ((quasiCoherentDerivedAdjunction π (isQuasicoherent_homology_derivedPullback' π)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs π)).comparisonMap
      (twistedInverseImageAdjunction π
        (isQuasicoherent_homology_derivedPushforward_of_qcqs π)) K L))
    (hι : ∀ B C : quasiCoherentDerivedCategory A,
      IsIso ((quasiCoherentDerivedAdjunction ι (isQuasicoherent_homology_derivedPullback' ι)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs ι)).comparisonMap
      (twistedInverseImageAdjunction ι
        (isQuasicoherent_homology_derivedPushforward_of_qcqs ι)) B C)) :
    IsIso ((quasiCoherentDerivedPullback' (closedInOpenImmersion a ι).toImage).map
      ((quasiCoherentDerivedAdjunction ((closedInOpenImmersion a ι).imageι ≫ π)
        (isQuasicoherent_homology_derivedPullback' ((closedInOpenImmersion a ι).imageι ≫ π))
      (isQuasicoherent_homology_derivedPushforward_of_qcqs
        ((closedInOpenImmersion a ι).imageι ≫ π))).comparisonMap
        (twistedInverseImageAdjunction ((closedInOpenImmersion a ι).imageι ≫ π)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs
            ((closedInOpenImmersion a ι).imageι ≫ π))) K L)) := by
  exact (isIso_map_pullback_comparisonMap_comp_iff π (isPullback_closedInOpen a ι) K L hL hKL).2
    inferInstance

end ClosedInOpen

end Stacks.Duality

end
