module

public import StacksFrontier.AlgebraicGeometry.HProjective.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.MonotoneSubschemeClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.SeparatedFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.SiteObjectBase
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ProperCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# A late member of a directed family of closed subspaces is proper

Let `g : X ⟶ Y` be a separated morphism of finite type of algebraic spaces over `S`, with `Y`
quasi-compact, and let `(Z_i)` be a directed decreasing family of closed subspaces of `X` whose
intersection is contained in a closed subspace `C ⊆ Z_i` which is proper over `Y`. Then `Z_i` is
proper over `Y` for every sufficiently large `i`.

This is the claim in the proof of **Stacks 0A0W** ("we claim that for all `i` large enough the
morphism `X_i ⟶ Y` is proper"), and the proof is the source's.

* Properness is checked after base change along one surjective étale morphism from an affine
  scheme (Stacks 083R), so `Y` may be taken affine.
* Over an affine `Y`, Chow's lemma (Stacks 089J) gives a proper surjective `π : X'' ⟶ X` from a
  scheme `X''` with an immersion `X'' ⟶ ℙⁿ_Y`. The inverse images `π⁻¹(Z_i)` are the closed
  subschemes of `X''` cut out by the chart ideals `K_i` of the `Z_i` along `π`, and `π⁻¹(C)` is
  cut out by `⨆ K_i`, because the `Z_i` intersect inside `C`.
* `π⁻¹(C)` is proper over `Y` (Stacks 04XY), hence a closed subscheme of `ℙⁿ_Y` (Stacks 04NX and
  04CD), so `π⁻¹(Z_i)` is a closed subscheme of `ℙⁿ_Y` for `i` large (the scheme case of Stacks
  0A0T, `AlgebraicGeometry.exists_forall_ge_isClosedImmersion_subschemeι_comp`, which is Tag
  0A0N), hence proper over `Y`; and `Z_i` is the image of `π⁻¹(Z_i)` under `π`, so it is proper
  over `Y` (Stacks 08AJ).

The source applies the algebraic-space Lemma 0A0T to the `π⁻¹(Z_i)`. They are closed
subschemes of the scheme `X''`, so its scheme case Tag 0A0N is what is used here; Stacks 07SR,
which the space case needs, does not enter.

## Main results

* `AlgebraicGeometry.Space.exists_chowSchemeCover_over_isAffine`: Stacks 089J over an affine
  object of the site, in the form with an explicit base object `Spec A`.
* `AlgebraicGeometry.Space.exists_forall_ge_isProper_closedSubspace_comp_of_isAffine`: the claim
  over an affine object of the site.
* `AlgebraicGeometry.Space.exists_forall_ge_isProper_closedSubspace_comp`: the claim over a
  quasi-compact algebraic space.

## References

* [Stacks Project, Tag 0A0W](https://stacks.math.columbia.edu/tag/0A0W)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
* [Stacks Project, Tag 083R](https://stacks.math.columbia.edu/tag/083R)
* [Stacks Project, Tag 08AJ](https://stacks.math.columbia.edu/tag/08AJ)
* [Stacks Project, Tag 0A0N](https://stacks.math.columbia.edu/tag/0A0N)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Transport of properties along cartesian squares of presheaves -/

/-- A cartesian square of presheaves whose four vertices are algebraic spaces is cartesian in the
category of algebraic spaces. -/
theorem isPullback_algebraicSpaces_homMk
    {X' X Y' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (hY' : IsAlgebraicSpace B S hS Y') (hY : IsAlgebraicSpace B S hS Y)
    (sq : IsPullback g' f' f g) :
    IsPullback (ObjectProperty.homMk g' : (⟨X', hX'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩)
      (ObjectProperty.homMk f' : (⟨X', hX'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y', hY'⟩)
      (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
      (ObjectProperty.homMk g : (⟨Y', hY'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩) :=
  IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ sq.w) sq

/-- In a cartesian square of algebraic spaces the base change of a morphism of finite type is of
finite type (Stacks 03XH), for a square of presheaves. -/
theorem isFiniteType_of_isPullback_of_isAlgebraicSpace
    {X' X Y' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (hY' : IsAlgebraicSpace B S hS Y') (hY : IsAlgebraicSpace B S hS Y)
    (sq : IsPullback g' f' f g) (hf : IsFiniteType B S hS f) :
    IsFiniteType B S hS f' :=
  (isFiniteType_isStableUnderBaseChange B S hS).of_isPullback
    (isPullback_algebraicSpaces_homMk B S hS hX' hX hY' hY sq) hf

/-! ### Chow's lemma over an affine object of the site -/

/-- **Stacks 089J over an affine object of the site.** Let `W` be an object of the big fppf site
of `S` with affine underlying scheme and let `g : X ⟶ h_W` be a separated morphism of finite type
from an algebraic space. Then `W` is isomorphic to an object `T = (Spec A ⟶ S)` of the site, and
there are an object `X'` of the site with a morphism `ψ : X' ⟶ T` which is H-quasi-projective on
underlying schemes and a proper surjective morphism `p : h_{X'} ⟶ X` lying over `ψ`. -/
theorem exists_chowSchemeCover_over_isAffine (W : BigFppfOver B S hS)
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W))
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (g : X ⟶ yoneda.obj W) (hsep : IsSeparated B S hS g) (hft : IsFiniteType B S hS g) :
    ∃ (T : BigFppfOver B S hS) (θ : T ≅ W) (X' : BigFppfOver B S hS) (ψ : X' ⟶ T)
      (p : yoneda.obj X' ⟶ X),
      IsAffine ((BigFppfOver.toScheme B S hS).obj T) ∧
      IsProper B S hS p ∧ IsSurjective B S hS p ∧ p ≫ g ≫ yoneda.map θ.inv = yoneda.map ψ ∧
        IsHQuasiProjective ((BigFppfOver.toScheme B S hS).map ψ) := by
  classical
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj W) := hW
  let A : CommRingCat.{u} := Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)
  let eT : Spec A ≅ (BigFppfOver.toScheme B S hS).obj W :=
    ((BigFppfOver.toScheme B S hS).obj W).isoSpec.symm
  have hA : B.Contains (Spec A) := (Scheme.size_congr eT).trans_lt W.left.property
  let εiso : B.obj hA ≅ W.left :=
    { hom := B.inclusion.preimage eT.hom
      inv := B.inclusion.preimage eT.inv
      hom_inv_id := B.inclusion.map_injective (by
        rw [CategoryTheory.Functor.map_comp, B.inclusion.map_preimage,
          B.inclusion.map_preimage, eT.hom_inv_id, CategoryTheory.Functor.map_id]
        rfl)
      inv_hom_id := B.inclusion.map_injective (by
        rw [CategoryTheory.Functor.map_comp, B.inclusion.map_preimage,
          B.inclusion.map_preimage, eT.inv_hom_id, CategoryTheory.Functor.map_id]
        rfl) }
  let g₀ : B.obj hA ⟶ B.obj hS := εiso.hom ≫ W.hom
  let θ : (Over.mk g₀ : BigFppfOver B S hS) ≅ W := Over.isoMk εiso rfl
  have hsep' : IsSeparated B S hS (g ≫ yoneda.map θ.inv) :=
    isSeparated_comp B S hS g _ hsep (isSeparated_of_isIso B S hS _)
  have hft' : IsFiniteType B S hS (g ≫ yoneda.map θ.inv) :=
    isFiniteType_of_arrowIso B S hS g (g ≫ yoneda.map θ.inv) (𝟙 X) (yoneda.map θ.inv)
      (by simp) hft
  obtain ⟨X', ψ, p, hp, hps, hpψ, hqp⟩ :=
    exists_chowSchemeCover_over_base B S hS A hA g₀ hX (g ≫ yoneda.map θ.inv) hsep' hft'
  exact ⟨Over.mk g₀, θ, X', ψ, p, IsAffine.of_isIso ((BigFppfOver.toScheme B S hS).map θ.hom),
    hp, hps, hpψ, hqp⟩

/-! ### Chart ideals of closed subspaces along a scheme chart -/

/-- Let `p : h_{X'} ⟶ X` be a chart lying over `ψ : X' ⟶ T` along `g : X ⟶ h_W` and `θ : T ≅ W`.
For a closed subspace `D ⊆ X`, the base change of `D ⟶ h_W` along `p` is proper exactly when the
closed subscheme of `X'` cut out by the chart ideal of `D` is proper over `T`. -/
private theorem isProper_rep_fst_comp_iff {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) {W T X' : BigFppfOver B S hS} (g : X ⟶ yoneda.obj W)
    (θ : T ≅ W) (ψ : X' ⟶ T) (p : yoneda.obj X' ⟶ X)
    (hpψ : p ≫ g ≫ yoneda.map θ.inv = yoneda.map ψ) (D : ClosedSubspaces B S hS X) :
    IsProper B S hS (D.2.2.rep.fst p ≫ D.1.ι ≫ g) ↔
      _root_.AlgebraicGeometry.IsProper
        ((chartKer B S hS ⟨X, hX⟩ D p).subschemeι ≫ (BigFppfOver.toScheme B S hS).map ψ) := by
  -- Comparison of the closed subscheme cut out by a chart ideal with the base change.
  have hcomp : yoneda.map (D.2.2.rep.snd p ≫ ψ) =
      D.2.2.rep.fst p ≫ (D.1.ι ≫ g) ≫ yoneda.map θ.inv := by
    rw [Functor.map_comp, ← hpψ, ← Category.assoc, ← (D.2.2.rep.isPullback p).w]
    simp only [Category.assoc]
  have hsub : (BigFppfOver.toScheme B S hS).map (D.2.2.rep.snd p ≫ ψ) =
      ((BigFppfOver.toScheme B S hS).map (D.2.2.rep.snd p)).toImage ≫
        (chartKer B S hS ⟨X, hX⟩ D p).subschemeι ≫ (BigFppfOver.toScheme B S hS).map ψ := by
    rw [Functor.map_comp]
    exact (congrArg (· ≫ (BigFppfOver.toScheme B S hS).map ψ)
      ((BigFppfOver.toScheme B S hS).map (D.2.2.rep.snd p)).toImage_imageι.symm).trans
      (Category.assoc _ _ _)
  have hstab : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsProper.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
    ⟨fun hsq hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @_root_.AlgebraicGeometry.IsProper)
      (hsq.map (BigFppfOver.toScheme B S hS)) hg⟩
  have hy : IsProper B S hS (D.2.2.rep.fst p ≫ D.1.ι ≫ g) ↔
      IsProper B S hS (yoneda.map (D.2.2.rep.snd p ≫ ψ)) :=
    (isProper_comp_isIso_iff B S hS _ (yoneda.map θ.inv)).symm.trans (by
      rw [hcomp]
      simp only [Category.assoc])
  have hs : IsProper B S hS (yoneda.map (D.2.2.rep.snd p ≫ ψ)) ↔
      _root_.AlgebraicGeometry.IsProper
        ((BigFppfOver.toScheme B S hS).map (D.2.2.rep.snd p ≫ ψ)) :=
    -- Properness of the represented morphism is `IsProper` of the schemes of its represented
    -- base changes (Stacks 03ZM), and the identity square is one of them.
    ⟨fun h => (MorphismProperty.relative_map_iff (F := yoneda)
      (P := MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsProper.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))).mp
      ((presheaf_isProper_iff B S hS _ (isAlgebraicSpace_yoneda B S hS _)
        (isAlgebraicSpace_yoneda B S hS _) (Functor.relativelyRepresentable.map yoneda _)).mp h),
      isProper_yoneda_map B S hS _⟩
  have : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (D.2.2.rep.snd p)) := D.2.2.property_snd p
  rw [hy, hs, hsub]
  exact MorphismProperty.cancel_left_of_respectsIso @_root_.AlgebraicGeometry.IsProper _ _

/-- **Stacks 08AJ for a closed subspace.** Let `g : X ⟶ h_W` be separated of finite type and let
`p : h_{X'} ⟶ X` be surjective. If the base change of `D ⟶ h_W` along `p` is proper for a closed
subspace `D ⊆ X`, then `D ⟶ h_W` is proper. -/
private theorem isProper_ι_comp_of_isProper_rep_fst {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) {W X' : BigFppfOver B S hS} (g : X ⟶ yoneda.obj W)
    (hsep : IsSeparated B S hS g) (hft : IsFiniteType B S hS g) (p : yoneda.obj X' ⟶ X)
    (hps : IsSurjective B S hS p) (D : ClosedSubspaces B S hS X)
    (h : IsProper B S hS (D.2.2.rep.fst p ≫ D.1.ι ≫ g)) :
    IsProper B S hS (D.1.ι ≫ g) :=
  isProper_of_isSurjective_comp B S hS (isAlgebraicSpace_yoneda B S hS _) D.2.1
    (isAlgebraicSpace_yoneda B S hS W) _ _ h.2.2
    (isSurjective_of_isPullback B S hS
      (isPullback_algebraicSpaces_homMk B S hS (isAlgebraicSpace_yoneda B S hS _)
        (isAlgebraicSpace_yoneda B S hS X') D.2.1 hX (D.2.2.rep.isPullback p).flip) hps)
    (isSeparated_comp B S hS _ _ (isSeparated_of_isClosedImmersion B S hS _ D.2.2) hsep)
    (isFiniteType_comp B S hS D.2.1 hX (isAlgebraicSpace_yoneda B S hS W) _ _
      (isFiniteType_of_isClosedImmersion B S hS _ D.2.2) hft)

/-- The chart ideal along `p` of a closed subspace is antitone in the subspace. -/
private theorem chartKer_le_chartKer_of_le {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) {X' : BigFppfOver B S hS} (p : yoneda.obj X' ⟶ X)
    {D E : ClosedSubspaces B S hS X} (h : D.1 ≤ E.1) :
    chartKer B S hS ⟨X, hX⟩ E p ≤ chartKer B S hS ⟨X, hX⟩ D p :=
  (le_chartKer_iff B S hS ⟨X, hX⟩ D p _).2 (by
    have hE : idealPoints B S hS (chartKer B S hS ⟨X, hX⟩ E p) = E.1.preimage p :=
      idealPoints_ker_rep_snd E.2.2 p
    rw [hE]
    exact fun _ _ hx => h _ hx)

/-- The chart ideals along `p` of a family of closed subspaces `Z_i` have supremum the chart ideal
of a closed subspace `C` contained in every `Z_i` and containing their intersection. -/
private theorem iSup_chartKer_eq_of_iInf_le {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) {X' : BigFppfOver B S hS} (p : yoneda.obj X' ⟶ X)
    {ι : Type u} (Z : ι → ClosedSubspaces B S hS X) (C : ClosedSubspaces B S hS X)
    (hCZ : ∀ i, C.1 ≤ (Z i).1) (hC : (⨅ i, (Z i).1) ≤ C.1) :
    ⨆ i, chartKer B S hS ⟨X, hX⟩ (Z i) p = chartKer B S hS ⟨X, hX⟩ C p := by
  have hpts : ∀ D : ClosedSubspaces B S hS X,
      idealPoints B S hS (chartKer B S hS ⟨X, hX⟩ D p) = D.1.preimage p :=
    fun D => idealPoints_ker_rep_snd D.2.2 p
  refine le_antisymm (iSup_le fun i => chartKer_le_chartKer_of_le B S hS hX p (hCZ i)) ?_
  · refine idealPoints_le_iff.mp ?_
    rw [hpts C]
    intro U x hx
    refine hC _ ?_
    rw [Subfunctor.iInf_obj, Set.mem_iInter]
    intro i
    have h := idealPoints_le_iff.mpr
      (le_iSup (fun i => chartKer B S hS ⟨X, hX⟩ (Z i) p) i) _ hx
    rwa [hpts (Z i)] at h

/-- A preimmersion of schemes whose composite with a separated morphism is proper is a closed
immersion. -/
private theorem isClosedImmersion_of_isProper_comp {X Y T : Scheme.{u}} (f : X ⟶ Y) (π : Y ⟶ T)
    [_root_.AlgebraicGeometry.IsPreimmersion f] [_root_.AlgebraicGeometry.IsSeparated π]
    [_root_.AlgebraicGeometry.IsProper (f ≫ π)] :
    _root_.AlgebraicGeometry.IsClosedImmersion f := by
  have := _root_.AlgebraicGeometry.IsProper.of_comp f π
  exact .of_isPreimmersion f f.isClosedMap.isClosed_range

/-- Let `p : h_{X'} ⟶ X` be a proper chart lying over `ψ : X' ⟶ T` along `g : X ⟶ h_W` and
`θ : T ≅ W`. If `C ⟶ h_W` is proper for a closed subspace `C ⊆ X`, then the closed subscheme of
`X'` cut out by the chart ideal of `C` is proper over `T`. -/
private theorem isProper_chartKer_subschemeι_comp {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) {W T X' : BigFppfOver B S hS} (g : X ⟶ yoneda.obj W)
    (θ : T ≅ W) (ψ : X' ⟶ T) (p : yoneda.obj X' ⟶ X) (hp : IsProper B S hS p)
    (hpψ : p ≫ g ≫ yoneda.map θ.inv = yoneda.map ψ) (C : ClosedSubspaces B S hS X)
    (hCp : IsProper B S hS (C.1.ι ≫ g)) :
    _root_.AlgebraicGeometry.IsProper
      ((chartKer B S hS ⟨X, hX⟩ C p).subschemeι ≫ (BigFppfOver.toScheme B S hS).map ψ) :=
  (isProper_rep_fst_comp_iff B S hS hX g θ ψ p hpψ C).1
    (isProper_comp B S hS (isAlgebraicSpace_yoneda B S hS _) C.2.1
      (isAlgebraicSpace_yoneda B S hS W) _ _
      (isProper_of_isPullback B S hS (isAlgebraicSpace_yoneda B S hS _)
        (isAlgebraicSpace_yoneda B S hS X') C.2.1 hX (C.2.2.rep.isPullback p).flip hp) hCp)

/-! ### The claim over an affine object of the site -/

/-- **The claim of the proof of Stacks 0A0W, over an affine base.** Let `W` be an object of the
site with affine underlying scheme, let `g : X ⟶ h_W` be a separated morphism of finite type from
an algebraic space, and let `(Z_i)` be a decreasing family of closed subspaces of `X` indexed by a
nonempty directed preorder. Let `C` be a closed subspace of `X` contained in every `Z_i` and
containing their intersection, with `C ⟶ h_W` proper. Then `Z_i ⟶ h_W` is proper for every
sufficiently large `i`.

The proof is the source's: Chow's lemma gives a proper surjective `p : h_{X'} ⟶ X` with an
immersion `j` of `X'` into a projective space `P` over `W`; the chart ideals `K_i` of the `Z_i`
along `p` are monotone with supremum the chart ideal of `C`; the closed subscheme it cuts out is
proper over `W`, hence closed in `P`; so the closed subscheme cut out by `K_i` is closed in `P`
for `i` large (Tag 0A0N, through
`AlgebraicGeometry.exists_forall_ge_isClosedImmersion_subschemeι_comp`), hence proper over `W`;
it is the base change of `p` to `Z_i`, which is therefore proper over `W` by Stacks 08AJ. -/
theorem exists_forall_ge_isProper_closedSubspace_comp_of_isAffine (W : BigFppfOver B S hS)
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W))
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (g : X ⟶ yoneda.obj W) (hsep : IsSeparated B S hS g) (hft : IsFiniteType B S hS g)
    {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (Z : ι → ClosedSubspaces B S hS X) (hZ : ∀ ⦃i j : ι⦄, i ≤ j → (Z j).1 ≤ (Z i).1)
    (C : ClosedSubspaces B S hS X) (hCZ : ∀ i, C.1 ≤ (Z i).1) (hC : (⨅ i, (Z i).1) ≤ C.1)
    (hCp : IsProper B S hS (C.1.ι ≫ g)) :
    ∃ i₀ : ι, ∀ i, i₀ ≤ i → IsProper B S hS ((Z i).1.ι ≫ g) := by
  classical
  obtain ⟨T, θ, X', ψ, p, hT, hp, hps, hpψ, n, j, hj, hjqc, hjψ⟩ :=
    exists_chowSchemeCover_over_isAffine B S hS W hW hX g hsep hft
  -- The chart ideals along the Chow cover.
  let Xa : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let K : ι → ((BigFppfOver.toScheme B S hS).obj X').IdealSheafData :=
    fun i => chartKer B S hS Xa (Z i) p
  let K₀ : ((BigFppfOver.toScheme B S hS).obj X').IdealSheafData := chartKer B S hS Xa C p
  have hKmono : Monotone K := fun i i' h => chartKer_le_chartKer_of_le B S hS hX p (hZ h)
  have hsup : ⨆ i, K i = K₀ := iSup_chartKer_eq_of_iInf_le B S hS hX p Z C hCZ hC
  -- The schemes involved.
  have hPT : _root_.AlgebraicGeometry.IsProper
      (projectiveSpaceOver n ((BigFppfOver.toScheme B S hS).obj T) ↘
        (BigFppfOver.toScheme B S hS).obj T) :=
    isProper_projectiveSpaceOver n _
  have : CompactSpace (projectiveSpaceOver n ((BigFppfOver.toScheme B S hS).obj T)) :=
    QuasiCompact.compactSpace_of_compactSpace
      (projectiveSpaceOver n ((BigFppfOver.toScheme B S hS).obj T) ↘
        (BigFppfOver.toScheme B S hS).obj T)
  have : QuasiSeparatedSpace (projectiveSpaceOver n ((BigFppfOver.toScheme B S hS).obj T)) :=
    quasiSeparatedSpace_of_quasiSeparated
      (projectiveSpaceOver n ((BigFppfOver.toScheme B S hS).obj T) ↘
        (BigFppfOver.toScheme B S hS).obj T)
  have : CompactSpace ((BigFppfOver.toScheme B S hS).obj X') :=
    QuasiCompact.compactSpace_of_compactSpace j
  have : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj X') :=
    quasiSeparatedSpace_of_quasiSeparated j
  -- The chart ideal of `C` cuts out a closed subscheme of `P`.
  have : _root_.AlgebraicGeometry.IsProper ((K₀.subschemeι ≫ j) ≫
      (projectiveSpaceOver n ((BigFppfOver.toScheme B S hS).obj T) ↘
        (BigFppfOver.toScheme B S hS).obj T)) := by
    rw [Category.assoc, hjψ]
    exact isProper_chartKer_subschemeι_comp B S hS hX g θ ψ p hp hpψ C hCp
  -- Tag 0A0N.
  obtain ⟨i₀, hi₀⟩ := exists_forall_ge_isClosedImmersion_subschemeι_comp K hKmono j K₀ hsup
    (isClosedImmersion_of_isProper_comp _
      (projectiveSpaceOver n ((BigFppfOver.toScheme B S hS).obj T) ↘
        (BigFppfOver.toScheme B S hS).obj T))
  refine ⟨i₀, fun i hi => isProper_ι_comp_of_isProper_rep_fst B S hS hX g hsep hft p hps (Z i)
    ((isProper_rep_fst_comp_iff B S hS hX g θ ψ p hpψ (Z i)).2 ?_)⟩
  have := hi₀ i hi
  rw [← hjψ, ← Category.assoc]
  infer_instance

/-! ### The claim over a quasi-compact algebraic space -/

/-- The base change of a closed subspace `D ⊆ X` along the projection `X ×_Y h_V ⟶ X`, mapped to
`h_V`, is the base change of `D ⟶ Y` along `h_V ⟶ Y`. -/
theorem isPullback_preimage_ι_comp_pullbackSnd {Y X V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (g : X ⟶ Y) (φ : V ⟶ Y) (D : Subfunctor X) :
    IsPullback (D.fromPreimage (pullback.fst g φ)) ((D.preimage (pullback.fst g φ)).ι ≫
      pullback.snd g φ) (D.ι ≫ g) φ :=
  (Subfunctor.isPullback_preimage (pullback.fst g φ) D).paste_vert
    (IsPullback.of_hasPullback g φ)

/-- **The claim of the proof of Stacks 0A0W.** Let `g : X ⟶ Y` be a separated morphism of finite
type of algebraic spaces over `S` with `Y` quasi-compact, and let `(Z_i)` be a decreasing family
of closed subspaces of `X` indexed by a nonempty directed preorder. Let `C` be a closed subspace
of `X` contained in every `Z_i` and containing their intersection, with `C ⟶ Y` proper. Then
`Z_i ⟶ Y` is proper for every sufficiently large `i`.

As in the source, properness is tested after base change along one surjective étale morphism
`h_V ⟶ Y` from an affine scheme (Stacks 083R, which exists by Stacks 03H6 since `Y` is
quasi-compact), where it is
`AlgebraicGeometry.Space.exists_forall_ge_isProper_closedSubspace_comp_of_isAffine`. -/
theorem exists_forall_ge_isProper_closedSubspace_comp
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hYqc : IsQuasiCompactSpace B S hS Y)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (g : X ⟶ Y) (hsep : IsSeparated B S hS g) (hft : IsFiniteType B S hS g)
    {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (Z : ι → ClosedSubspaces B S hS X) (hZ : ∀ ⦃i j : ι⦄, i ≤ j → (Z j).1 ≤ (Z i).1)
    (C : ClosedSubspaces B S hS X) (hCZ : ∀ i, C.1 ≤ (Z i).1) (hC : (⨅ i, (Z i).1) ≤ C.1)
    (hCp : IsProper B S hS (C.1.ι ≫ g)) :
    ∃ i₀ : ι, ∀ i, i₀ ≤ i → IsProper B S hS ((Z i).1.ι ≫ g) := by
  obtain ⟨V, φ, hVaff, hφs, hφe⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS Y hY).1 hYqc
  have hyV := isAlgebraicSpace_yoneda B S hS V
  have hXV : IsAlgebraicSpace B S hS (pullback g φ) :=
    isAlgebraicSpace_pullback B S hS g φ hX hyV hY
  have hsepV : IsSeparated B S hS (pullback.snd g φ) := isSeparated_pullbackSnd B S hS φ hsep
  have hftV : IsFiniteType B S hS (pullback.snd g φ) :=
    isFiniteType_of_isPullback_of_isAlgebraicSpace B S hS hXV hX hyV hY
      (IsPullback.of_hasPullback g φ) hft
  let base : ClosedSubspaces B S hS X → ClosedSubspaces B S hS (pullback g φ) := fun D =>
    ⟨D.1.preimage (pullback.fst g φ),
      isClosedSubspace_preimage B S hS (pullback.fst g φ) D.1 hX hXV D.2⟩
  have hbase : ∀ D : ClosedSubspaces B S hS X, IsPullback (D.1.fromPreimage (pullback.fst g φ))
      ((base D).1.ι ≫ pullback.snd g φ) (D.1.ι ≫ g) φ :=
    fun D => isPullback_preimage_ι_comp_pullbackSnd B S hS g φ D.1
  have hCVp : IsProper B S hS ((base C).1.ι ≫ pullback.snd g φ) :=
    isProper_of_isPullback B S hS (base C).2.1 C.2.1 hyV hY (hbase C) hCp
  obtain ⟨i₀, hi₀⟩ := exists_forall_ge_isProper_closedSubspace_comp_of_isAffine B S hS V hVaff
    hXV (pullback.snd g φ) hsepV hftV (fun i => base (Z i))
    (fun i j h _ x hx => hZ h _ hx) (base C) (fun i _ x hx => hCZ i _ hx)
    (by
      intro U x hx
      refine hC _ ?_
      rw [Subfunctor.iInf_obj, Set.mem_iInter] at hx ⊢
      exact fun i => hx i)
    hCVp
  refine ⟨i₀, fun i hi => ?_⟩
  have hfst : IsProper B S hS (pullback.fst φ ((Z i).1.ι ≫ g)) := by
    rw [← (hbase (Z i)).flip.isoPullback_inv_fst]
    exact (isProper_isIso_comp_iff B S hS _ _).2 (hi₀ i hi)
  have h41 := (isProper_tfae B S hS (Z i).2.1 hY ((Z i).1.ι ≫ g)).out 4 1
  exact h41.mp ⟨V, φ, isSurjective_of_presheafSurjective B S hS φ hφs, hφe, hfst⟩

end AlgebraicGeometry.Space

end
