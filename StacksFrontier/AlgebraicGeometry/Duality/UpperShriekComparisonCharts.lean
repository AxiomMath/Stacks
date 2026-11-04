module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.DerivedIsoLocality
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekComparisonIndependence
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekFibreDimension
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.PullbackComparisonAffine
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.ProjectionFormulaQuasiCoherent
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekStructureSheafCharts
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.Composition
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.Flat
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.SmoothTarget
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Smooth
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekFibreDimensionCharts

/-!
# Invertibility of `μ_{f,K}` is local, and its reduction to the charts

The map `μ_{f,K} : Lf^*K ⊗ᴸ f^!𝒪_Y ⟶ f^!K` of [Stacks, Tag 0B6T] is invertible exactly when
`Lj^*` of the comparison map `Lf̄^*K ⊗ ā(𝒪_Y) ⟶ ā(K)` of the compactification is
(`Stacks.Duality.isIso_upperShriekCompareWithPullback_iff`). This file reduces that to the
affine charts `U ⊆ f⁻¹(V)` of `f`, following the proof of [Stacks, Tag 0B6U] (e): invertibility
in `D_QCoh` is local; the construction commutes with restriction to opens of the source and the
target; on a chart the compactification may be replaced by the closure of `U` in `Pⁿ_V`; and
there the comparison map is assembled from those of `Pⁿ_V ⟶ V` and of the closed immersion
`U ⟶ 𝔸ⁿ_V`.

## Main results

* `Stacks.Duality.isIso_of_forall_isIso_quasiCoherentDerivedPullback` — invertibility in
  `D_QCoh(𝒪_X)` is local on `X`.
* `Stacks.Duality.isIso_map_comparisonMap_iff_of_compactification` — the restriction to `X` of
  the comparison map of a compactification is invertible for one compactification exactly when it
  is for another.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace Stacks.Duality

/-! ### Locality -/

/-- **Invertibility in `D_QCoh(𝒪_X)` is local on `X`**: a morphism whose derived pullbacks to
the members of an open covering are invertible is invertible. -/
theorem isIso_of_forall_isIso_quasiCoherentDerivedPullback {X : Scheme.{u}} {I : Type*}
    (U : I → X.Opens) (hU : TopologicalSpace.IsOpenCover U)
    {A B : quasiCoherentDerivedCategory X} (φ : A ⟶ B)
    (h : ∀ i, IsIso ((quasiCoherentDerivedPullback' (U i).ι).map φ)) : IsIso φ := by
  have : IsIso φ.hom := by
    refine Stacks.AlgebraicGeometry.AffineBaseChange.isIso_derived_of_isIso_restrict U hU φ.hom
      fun i => ?_
    have : IsIso ((derivedPullback (U i).ι).map φ.hom) :=
      Functor.map_isIso (ObjectProperty.ι _) ((quasiCoherentDerivedPullback' (U i).ι).map φ)
    exact (NatIso.isIso_map_iff (derivedRestrictIsoDerivedPullback (U i).ι) φ.hom).2 this
  have : IsIso ((ObjectProperty.ι _).map φ) := inferInstanceAs (IsIso φ.hom)
  exact isIso_of_fully_faithful (ObjectProperty.ι _) φ

/-! ### Boundedness -/

/-- A derived pullback along an open immersion of a bounded below object is bounded below. -/
theorem isBoundedBelow_quasiCoherentDerivedPullback_obj {Z W : Scheme.{u}} (e : Z ⟶ W)
    [IsOpenImmersion e] (K : quasiCoherentDerivedCategory W)
    (hK : DerivedCategoryB.IsBoundedBelow K.obj) :
    DerivedCategoryB.IsBoundedBelow ((quasiCoherentDerivedPullback' e).obj K).obj :=
  let ⟨n₀, hn₀⟩ := hK
  ⟨n₀, fun m hm => ((Scheme.Modules.restrictFunctor e).map_isZero (hn₀ m hm)).of_iso
    ((DerivedCategory.homologyFunctor Z.Modules m).mapIso
        ((derivedRestrictIsoDerivedPullback e).app K.obj).symm ≪≫
      (DerivedCategoryB.mapDerivedCategoryHomologyIso
        (Scheme.Modules.restrictFunctor e) m).app K.obj)⟩

/-- Tensoring with the structure sheaf preserves boundedness below. -/
theorem isBoundedBelow_tensor_derivedStructureSheaf {Z : Scheme.{u}}
    (K : quasiCoherentDerivedCategory Z) (hK : DerivedCategoryB.IsBoundedBelow K.obj) :
    DerivedCategoryB.IsBoundedBelow (K ⊗ DerivedPushforward.derivedStructureSheaf Z).obj := by
  rw [← tensorUnit_quasiCoherentDerivedCategory]
  exact DerivedCategoryB.isBoundedBelow_of_iso ((ObjectProperty.ι _).mapIso (ρ_ K)).symm hK

/-- Derived direct image along an isomorphism of compact schemes is an equivalence. -/
private theorem isEquivalence_quasiCoherentDerivedPushforward_of_isIso {A B : Scheme.{u}}
    [CompactSpace A] [CompactSpace B] (e : A ⟶ B) [IsIso e] :
    (quasiCoherentDerivedPushforward e
      (isQuasicoherent_homology_derivedPushforward_of_qcqs e)).IsEquivalence :=
  (quasiCoherentDerivedPushforwardEquivalenceOfIsIso e
    (isQuasicoherent_homology_derivedPushforward_of_qcqs e)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs (inv e))
    (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 A))
    (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 B))).isEquivalence_functor

section IsoLocus

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [IsNoetherian X] [IsNoetherian Y]

/-- **Equation 48.8.0.1 through the comparison map of the monoidal adjunction**: a functor
inverts the map `Lf^*K ⊗ a(𝒪_Y) ⟶ a(K)` of [Stacks, Tag 0A9S] exactly when it inverts the
comparison map of `Lf^* ⊣ Rf_*` at `(K, 𝒪_Y)`; the two differ by isomorphisms. -/
theorem isIso_map_twistedInverseImageCompareWithPullback_iff {E : Type*} [Category E]
    (H : quasiCoherentDerivedCategory X ⥤ E) (K : quasiCoherentDerivedCategory Y) :
    IsIso (H.map (twistedInverseImageCompareWithPullback f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (quasiCoherentDerivedPullbackTensorIso f).hom
        (quasiCoherentDerivedTensorRightUnitor Y) K)) ↔
      IsIso (H.map ((quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).comparisonMap
          (twistedInverseImageAdjunction f (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
          K (DerivedPushforward.derivedStructureSheaf Y))) := by
  have e := compareWithPullbackTensor_eq_comparisonMap f
    (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
    (quasiCoherentDerivedPullbackTensorIso f).hom (quasiCoherentDerivedPullbackTensorIso_hom_app f)
    (twistedInverseImageAdjunction f (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
    K (DerivedPushforward.derivedStructureSheaf Y)
  simp only [twistedInverseImageCompareWithPullback, compareWithPullback, e, Functor.map_comp]
  rw [isIso_comp_right_iff, isIso_comp_left_iff, isIso_comp_right_iff]

/-- **Stacks Project, Tag 0B6Q (Lemma 48.8.3).** Let `f : X ⟶ Y` be a proper morphism of
Noetherian schemes and let `V ⊆ Y` be an open such that `f⁻¹(V) ⟶ V` is an isomorphism. Then for
`K ∈ D⁺_QCoh(𝒪_Y)` the map `Lf^*K ⊗ᴸ a(𝒪_Y) ⟶ a(K)` of Equation 48.8.0.1 restricts to an
isomorphism over `f⁻¹(V)`. -/
@[stacks 0B6Q]
theorem isIso_map_twistedInverseImageCompareWithPullback_of_isIso_morphismRestrict
    (V : Y.Opens) [IsIso (f ∣_ V)] (K : quasiCoherentDerivedCategory Y)
    (hK : DerivedCategoryB.IsBoundedBelow K.obj) :
    IsIso ((quasiCoherentDerivedPullback' (f ⁻¹ᵁ V).ι).map
      (twistedInverseImageCompareWithPullback f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (quasiCoherentDerivedPullbackTensorIso f).hom
        (quasiCoherentDerivedTensorRightUnitor Y) K)) := by
  rw [isIso_map_twistedInverseImageCompareWithPullback_iff]
  have := isNoetherian_of_isOpenImmersion V.ι
  have := isNoetherian_of_isOpenImmersion (f ⁻¹ᵁ V).ι
  have hO : DerivedCategoryB.IsBoundedBelow (DerivedPushforward.derivedStructureSheaf Y).obj :=
    Stacks.Duality.KoszulRegular.isBoundedBelow_singleFunctor_obj _
  have h := isIso_map_comparisonMap_baseChange_iff (f ⁻¹ᵁ V).ι (f ∣_ V) f V.ι
    (isPullback_morphismRestrict f V).flip (𝟭 _) K (DerivedPushforward.derivedStructureSheaf Y) hO
    (isBoundedBelow_tensor_derivedStructureSheaf K hK)
  simp only [Functor.id_map] at h
  refine h.2 ?_
  have := isEquivalence_quasiCoherentDerivedPushforward_of_isIso (f ∣_ V)
  exact Adjunction.isIso_comparisonMap_of_isEquivalence _ _ _ _

end IsoLocus

/-! ### Independence of the compactification -/

section CompactificationData

variable {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S] [IsNoetherian S]
  {X Y : FTS S} (f : X ⟶ Y)

/-- **Invertibility of the comparison map on `X` does not depend on the compactification**
(the independence part of the proof of [Stacks, Tag 0B6T], for invertibility): for any two
compactifications of `X` over `Y`, the restriction to `X` of the comparison map at `(K, L)` is
invertible for the first exactly when it is for the second, for `L` and `K ⊗ L` bounded below.
Both are compared with the dominating compactification. -/
theorem isIso_map_comparisonMap_iff_of_compactification
    (c₁ c₂ : CompactificationOf (Over.mk f.left))
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
  let Z := DominatingCompactification.compactification f c₁ c₂
  let p₁ : Z.space ⟶ c₁.space := DominatingCompactification.fst f c₁ c₂
  let p₂ : Z.space ⟶ c₂.space := DominatingCompactification.snd f c₁ c₂
  have sq₁ : IsPullback Z.immersion (𝟙 X.left) p₁ c₁.immersion :=
    DominatingCompactification.isPullback_fst f c₁ c₂
  have sq₂ : IsPullback Z.immersion (𝟙 X.left) p₂ c₂.immersion :=
    DominatingCompactification.isPullback_snd f c₁ c₂
  have hp₂ : p₂ ≫ c₂.toBase = Z.toBase := (DominatingCompactification.fst_comp_toBase f c₁ c₂).symm
  have : IsProper p₁ :=
    inferInstanceAs (IsProper (DominatingCompactification.fst f c₁ c₂))
  have : IsProper p₂ :=
    inferInstanceAs (IsProper (DominatingCompactification.snd f c₁ c₂))
  rw [← isIso_map_comparisonMap_iff_of_compactificationMap f Z c₁ p₁ rfl sq₁ K L hL hKL,
    isIso_map_comparisonMap_iff_of_compactificationMap f Z c₂ p₂ hp₂ sq₂ K L hL hKL]

end CompactificationData

/-! ### Restriction to opens of the source and the target -/

section RestrictOpen

open CompactificationOf

variable {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S] [IsNoetherian S]
  {U X V Y : FTS S} (f : X ⟶ Y) (g : U ⟶ V) (jU : U ⟶ X) (i : V ⟶ Y)
  [IsOpenImmersion jU.left] [IsOpenImmersion i.left] (w : jU ≫ f = g ≫ i)
  (c : CompactificationOf (Over.mk f.left))

omit [IsOpenImmersion jU.left] in
/-- **The comparison map on an open of `X` is that of the restricted compactification**: for open
immersions `U ⟶ X`, `V ⟶ Y` with `U ⟶ X ⟶ Y` factoring through `g : U ⟶ V`, the restriction to
`U` of the comparison map of `X̄ ⟶ Y` at `(K, L)` is invertible exactly when the restriction to
`U` of the comparison map of `X̄ ×_Y V ⟶ V` at the restrictions of `K` and `L` is, for `L` and
`K ⊗ L` bounded below ([Stacks, Tag 0B6P] with [Stacks, Tag 0A9P]). -/
theorem isIso_map_comparisonMap_restrictOpen_iff (K L : quasiCoherentDerivedCategory Y.left)
    (hL : DerivedCategoryB.IsBoundedBelow L.obj)
    (hKL : DerivedCategoryB.IsBoundedBelow (K ⊗ L).obj) :
    IsIso ((quasiCoherentDerivedPullback' jU.left).map
        ((quasiCoherentDerivedPullback' c.immersion).map
          ((quasiCoherentDerivedAdjunction c.toBase
            (isQuasicoherent_homology_derivedPullback' c.toBase)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs c.toBase)).comparisonMap
            (twistedInverseImageAdjunction c.toBase
              (isQuasicoherent_homology_derivedPushforward_of_qcqs c.toBase)) K L))) ↔
      IsIso ((quasiCoherentDerivedPullback' (restrictOpenImmersion f g jU i w c)).map
        ((quasiCoherentDerivedAdjunction (pullback.snd c.toBase i.left)
          (isQuasicoherent_homology_derivedPullback' (pullback.snd c.toBase i.left))
          (isQuasicoherent_homology_derivedPushforward_of_qcqs
            (pullback.snd c.toBase i.left))).comparisonMap
          (twistedInverseImageAdjunction (pullback.snd c.toBase i.left)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs (pullback.snd c.toBase i.left)))
          ((quasiCoherentDerivedPullback' i.left).obj K)
          ((quasiCoherentDerivedPullback' i.left).obj L))) := by
  have : IsNoetherian Y.left := ⟨⟩
  have hw : restrictOpenImmersion f g jU i w c ≫ pullback.fst c.toBase i.left =
      jU.left ≫ c.immersion := pullback.lift_fst _ _ _
  rw [← isIso_map_comparisonMap_baseChange_iff (pullback.fst c.toBase i.left)
    (pullback.snd c.toBase i.left) c.toBase i.left (IsPullback.of_hasPullback c.toBase i.left)
    (quasiCoherentDerivedPullback' (restrictOpenImmersion f g jU i w c)) K L hL hKL]
  exact (NatIso.isIso_map_iff (quasiCoherentDerivedPullbackCompIso jU.left c.immersion) _).trans
    ((NatIso.isIso_map_iff (quasiCoherentDerivedPullbackCongr hw.symm) _).trans
      (NatIso.isIso_map_iff (quasiCoherentDerivedPullbackCompIso
        (restrictOpenImmersion f g jU i w c) (pullback.fst c.toBase i.left)) _).symm)

end RestrictOpen

/-! ### Comparison maps over an affine target -/

section AffineTarget

/-- **The comparison map of `g ≫ e` for an isomorphism `e`** is invertible at `(K, L)` exactly
when that of `g` is at `(Le^*K, a_e L)`: by [Stacks, Tag 0B6R] it is the latter followed by `a_g`
of the comparison map of `e`, which is invertible since `Re_*` is an equivalence. -/
theorem isIso_comparisonMap_comp_iso_iff {A B C : Scheme.{u}} [CompactSpace A]
    [QuasiSeparatedSpace A] [CompactSpace B] [QuasiSeparatedSpace B] [CompactSpace C]
    [QuasiSeparatedSpace C] (g : A ⟶ B) (e : B ⟶ C) [IsIso e]
    (K L : quasiCoherentDerivedCategory C) :
    IsIso ((quasiCoherentDerivedAdjunction (g ≫ e)
        (isQuasicoherent_homology_derivedPullback' (g ≫ e))
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (g ≫ e))).comparisonMap
        (twistedInverseImageAdjunction (g ≫ e)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs (g ≫ e))) K L) ↔
      IsIso ((quasiCoherentDerivedAdjunction g (isQuasicoherent_homology_derivedPullback' g)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs g)).comparisonMap
        (twistedInverseImageAdjunction g (isQuasicoherent_homology_derivedPushforward_of_qcqs g))
        ((quasiCoherentDerivedPullback' e).obj K)
        ((twistedInverseImage e
          (isQuasicoherent_homology_derivedPushforward_of_qcqs e)).obj L)) := by
  have h := isIso_map_comparisonMap_comp_iff g e (𝟭 _) K L
  simp only [Functor.id_map] at h
  rw [h, Adjunction.comparisonMap_comp]
  have := isEquivalence_quasiCoherentDerivedPushforward_of_isIso e
  have := Adjunction.isIso_comparisonMap_of_isEquivalence
    (quasiCoherentDerivedAdjunction e (isQuasicoherent_homology_derivedPullback' e)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs e))
    (twistedInverseImageAdjunction e (isQuasicoherent_homology_derivedPushforward_of_qcqs e)) K L
  exact isIso_comp_right_iff _ _

/-- **[Stacks, Tag 0A9U] over an affine target, in two variables**: for `q : A ⟶ B` perfect and
proper with `B` affine and Noetherian, the comparison map `Lq^*K ⊗ a(L) ⟶ a(K ⊗ L)` is
invertible, by `Stacks.Duality.isIso_comparisonMap_of_specTarget` along `B ≅ Spec Γ(B)`. -/
theorem isIso_comparisonMap_of_isAffine {A B : Scheme.{u}} (q : A ⟶ B) [IsProper q] [Perfect q]
    [IsNoetherian B] [IsAffine B] [CompactSpace A] [QuasiSeparatedSpace A]
    (K L : quasiCoherentDerivedCategory B) :
    IsIso ((quasiCoherentDerivedAdjunction q (isQuasicoherent_homology_derivedPullback' q)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs q)).comparisonMap
      (twistedInverseImageAdjunction q (isQuasicoherent_homology_derivedPushforward_of_qcqs q))
        K L) := by
  let e := B.isoSpec
  let q' := q ≫ e.hom
  have hq : q = q' ≫ e.inv := by simp [q']
  have h := isIso_map_comparisonMap_congr hq (𝟭 _) K L
  simp only [Functor.id_map] at h
  rw [h, isIso_comparisonMap_comp_iso_iff q' e.inv]
  have : IsNoetherian A := isNoetherian_of_isProper q
  have : IsNoetherian (Spec Γ(B, ⊤)) := isNoetherian_of_isOpenImmersion e.inv
  have : Perfect e.hom := perfect_of_flat_of_locallyOfFinitePresentation _
  have : Perfect q' := perfect_comp q e.hom
  exact isIso_comparisonMap_of_specTarget q' _ _

/-- **[Stacks, Tag 0A9U] over an affine target**: for `q : A ⟶ B` perfect and proper with `B`
affine and Noetherian, the comparison map `Lq^*K ⊗ a(𝒪_B) ⟶ a(K ⊗ 𝒪_B)` is invertible, by
`Stacks.Duality.isIso_comparisonMap_structureSheaf_of_specTarget` along `B ≅ Spec Γ(B)`. -/
theorem isIso_comparisonMap_structureSheaf_of_isAffine {A B : Scheme.{u}} (q : A ⟶ B)
    [IsProper q] [Perfect q] [IsNoetherian B] [IsAffine B] [CompactSpace A]
    [QuasiSeparatedSpace A] (K : quasiCoherentDerivedCategory B) :
    IsIso ((quasiCoherentDerivedAdjunction q (isQuasicoherent_homology_derivedPullback' q)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs q)).comparisonMap
      (twistedInverseImageAdjunction q (isQuasicoherent_homology_derivedPushforward_of_qcqs q))
        K (DerivedPushforward.derivedStructureSheaf B)) := by
  let e := B.isoSpec
  let q' := q ≫ e.hom
  have hq : q = q' ≫ e.inv := by simp [q']
  have h := isIso_map_comparisonMap_congr hq (𝟭 _) K (DerivedPushforward.derivedStructureSheaf B)
  simp only [Functor.id_map] at h
  rw [h, isIso_comparisonMap_comp_iso_iff q' e.inv]
  refine (Adjunction.isIso_map_comparisonMap_iff_of_iso_right _ _ (𝟭 _) _
      ((twistedInverseImageIsoRestrictOfIsIso e.inv).app _ ≪≫
        ChartCompactification.restrictDerivedStructureSheafIso e.inv)).2 ?_
  have : IsNoetherian A := isNoetherian_of_isProper q
  have : IsNoetherian (Spec Γ(B, ⊤)) := isNoetherian_of_isOpenImmersion e.inv
  have : Perfect e.hom := perfect_of_flat_of_locallyOfFinitePresentation _
  have : Perfect q' := perfect_comp q e.hom
  exact isIso_comparisonMap_structureSheaf_of_specTarget q' _

end AffineTarget

/-! ### The charts -/

section Chart

open CompactificationOf ChartCompactification _root_.Stacks.Duality.ProjectiveSpace
  _root_.AlgebraicGeometry.ProjectiveSpace Stacks.AlgebraicGeometry.ProjPolyChart

attribute [local instance] MvPolynomial.gradedAlgebra

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y)

/-- The projection `Pⁿ_V ⟶ V` of a chart compactification is smooth. -/
private theorem ChartCompactification.smooth_π {U : X.left.Opens} {V : Y.left.Opens}
    (hV : IsAffineOpen V) (hUV : U ≤ f.left ⁻¹ᵁ V)
    (p : Dualizing.PolynomialPresentation (f.left.appLE V U hUV).hom) :
    Smooth (π f hV hUV p) := by
  have : Smooth (projToSpecCoeff Γ(Y.left, V) p.variableCount) := smooth_projToSpecCoeff _ _
  exact smooth_comp (projToSpecCoeff Γ(Y.left, V) p.variableCount) hV.isoSpec.inv

/-- For `f` perfect, the closed immersion `U ⟶ 𝔸ⁿ_V` of a chart compactification is perfect. -/
private theorem ChartCompactification.perfect_ι [Perfect f.left] {U : X.left.Opens}
    (hU : IsAffineOpen U) {V : Y.left.Opens} (hV : IsAffineOpen V) (hUV : U ≤ f.left ⁻¹ᵁ V)
    (p : Dualizing.PolynomialPresentation (f.left.appLE V U hUV).hom) :
    Perfect (ι f hU hUV p) := by
  have := smooth_π f hV hUV p
  let iU := FTS.ofAffineOpenι X U hU
  let iV := FTS.ofAffineOpenι Y V hV
  have : Perfect iU.left := perfect_of_flat_of_locallyOfFinitePresentation _
  have : Perfect (iU.left ≫ f.left) := perfect_comp iU.left f.left
  have : Smooth (π f hV hUV p ≫ iV.left) :=
    MorphismProperty.comp_mem @Smooth _ _ inferInstance inferInstance
  have : Smooth (chartι Γ(Y.left, V) p.variableCount ≫ π f hV hUV p ≫ iV.left) :=
    MorphismProperty.comp_mem @Smooth _ _ inferInstance inferInstance
  refine perfect_of_comp_eq_of_smooth (ι f hU hUV p)
    (chartι Γ(Y.left, V) p.variableCount ≫ π f hV hUV p ≫ iV.left) (p := iU.left ≫ f.left) ?_
  have h' : (ι f hU hUV p ≫ chartι Γ(Y.left, V) p.variableCount ≫ π f hV hUV p) ≫ iV.left =
      iU.left ≫ f.left := by
    rw [ι_comp f hU hV hUV p]
    exact Scheme.Hom.resLE_comp_ι f.left hUV
  simpa only [Category.assoc] using h'

/-- **The comparison map on an affine chart.** For a perfect morphism `f` of `FTS S`, `S`
Noetherian, any compactification `j`, affine opens `U ⊆ f⁻¹(V)` with a polynomial presentation
of `Γ(Y, V) ⟶ Γ(X, U)`, and `K` bounded below, the restriction to `U` of the comparison map
`Lf̄^*K ⊗ ā(𝒪_Y) ⟶ ā(K)` is invertible: restrict `j` to the chart, pass to the compactification
of `U` by its closure in `Pⁿ_V`, and assemble from `Pⁿ_V ⟶ V` and the closed immersion
`U ⟶ 𝔸ⁿ_V`, both perfect, where [Stacks, Tag 0A9U] applies. -/
theorem isIso_map_comparisonMap_of_chart [Perfect f.left]
    (j : CompactificationOf (Over.mk f.left)) {U : X.left.Opens} (hU : IsAffineOpen U)
    {V : Y.left.Opens} (hV : IsAffineOpen V) (hUV : U ≤ f.left ⁻¹ᵁ V)
    (p : Dualizing.PolynomialPresentation (f.left.appLE V U hUV).hom)
    (K : quasiCoherentDerivedCategory Y.left) (hK : DerivedCategoryB.IsBoundedBelow K.obj) :
    IsIso ((quasiCoherentDerivedPullback' U.ι).map
      ((quasiCoherentDerivedPullback' j.immersion).map
        ((quasiCoherentDerivedAdjunction j.toBase
          (isQuasicoherent_homology_derivedPullback' j.toBase)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs j.toBase)).comparisonMap
          (twistedInverseImageAdjunction j.toBase
            (isQuasicoherent_homology_derivedPushforward_of_qcqs j.toBase))
          K (DerivedPushforward.derivedStructureSheaf Y.left)))) := by
  have : IsAffine V.toScheme := hV
  have : IsAffine U.toScheme := hU
  have : IsNoetherian Y.left := ⟨⟩
  have : IsNoetherian V.toScheme := isNoetherian_of_isOpenImmersion V.ι
  have : IsNoetherian (FTS.ofAffineOpen Y V hV).left :=
    inferInstanceAs (IsNoetherian V.toScheme)
  have : IsAffine (FTS.ofAffineOpen Y V hV).left := inferInstanceAs (IsAffine V.toScheme)
  let g := FTS.homOfAffineOpens f hU hV hUV
  let w := FTS.ofAffineOpenι_comp f hU hV hUV
  let iV := FTS.ofAffineOpenι Y V hV
  let c₁ := j.restrictOpenPullback f g _ _ w
  let c₀ := compactification f hU hV hUV p
  let R := Γ(Y.left, V)
  let n := p.variableCount
  have hO := Stacks.Duality.KoszulRegular.isBoundedBelow_singleFunctor_obj
    (SheafOfModules.unit Y.left.ringCatSheaf)
  let K' := (quasiCoherentDerivedPullback' iV.left).obj K
  let O' := DerivedPushforward.derivedStructureSheaf (FTS.ofAffineOpen Y V hV).left
  have hK' : DerivedCategoryB.IsBoundedBelow K'.obj :=
    isBoundedBelow_quasiCoherentDerivedPullback_obj iV.left K hK
  have hO' : DerivedCategoryB.IsBoundedBelow O'.obj :=
    Stacks.Duality.KoszulRegular.isBoundedBelow_singleFunctor_obj _
  have hKO' := isBoundedBelow_tensor_derivedStructureSheaf K' hK'
  let eO : (quasiCoherentDerivedPullback' iV.left).obj
      (DerivedPushforward.derivedStructureSheaf Y.left) ≅ O' :=
    ObjectProperty.isoMk _ (derivedPullbackStructureSheafIso iV.left)
  refine (isIso_map_comparisonMap_restrictOpen_iff f g (FTS.ofAffineOpenι X U hU) iV w j K _ hO
    (isBoundedBelow_tensor_derivedStructureSheaf K hK)).2 ?_
  refine (Adjunction.isIso_map_comparisonMap_iff_of_iso_right _ _ _ _ eO).2 ?_
  refine (isIso_map_comparisonMap_iff_of_compactification g c₁ c₀ K' O' hO' hKO').2 ?_
  have : IsNoetherian (AlgebraicGeometry.Proj (polyGrading R n)) :=
    isNoetherian_of_isProper (π f hV hUV p)
  have := smooth_π f hV hUV p
  have : Perfect (π f hV hUV p) := perfect_of_flat_of_locallyOfFinitePresentation _
  have := perfect_ι f hU hV hUV p
  have : IsNoetherian (chartOpen R n).toScheme := isNoetherian_of_isOpenImmersion (chartι R n)
  exact isIso_map_comparisonMap_of_closedInOpen (π f hV hUV p) (chartι R n) (ι f hU hUV p)
    K' O' hO' hKO' (isIso_comparisonMap_structureSheaf_of_isAffine _ K')
    (isIso_comparisonMap_of_isAffine (ι f hU hUV p))

/-- **The comparison map of a compactification of a perfect morphism is invertible on `X`**
([Stacks, Tag 0B6U] (e), through `Stacks.Duality.isIso_upperShriekCompareWithPullback_iff`): for
a perfect morphism `f` of `FTS S`, `S` Noetherian, any compactification `j` and `K` bounded
below, `Lj^*` of the comparison map `Lf̄^*K ⊗ ā(𝒪_Y) ⟶ ā(K)` is invertible. Invertibility is
local, and `X` is covered by affine charts, where `Stacks.Duality.isIso_map_comparisonMap_of_chart`
applies. -/
theorem isIso_map_comparisonMap_of_perfect [Perfect f.left]
    (j : CompactificationOf (Over.mk f.left)) (K : quasiCoherentDerivedCategory Y.left)
    (hK : DerivedCategoryB.IsBoundedBelow K.obj) :
    IsIso ((quasiCoherentDerivedPullback' j.immersion).map
      ((quasiCoherentDerivedAdjunction j.toBase
        (isQuasicoherent_homology_derivedPullback' j.toBase)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs j.toBase)).comparisonMap
        (twistedInverseImageAdjunction j.toBase
          (isQuasicoherent_homology_derivedPushforward_of_qcqs j.toBase))
        K (DerivedPushforward.derivedStructureSheaf Y.left))) := by
  choose U hU V hV hUV hxU _ p using fun x : X.left => exists_chart_presentation f x ⊤ trivial
  exact isIso_of_forall_isIso_quasiCoherentDerivedPullback U
    (TopologicalSpace.IsOpenCover.mk (eq_top_iff.2 fun x _ =>
      TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxU x⟩)) _ fun x =>
    isIso_map_comparisonMap_of_chart f j (hU x) (hV x) (hUV x) (p x).some K hK

end Chart

end Stacks.Duality

end
