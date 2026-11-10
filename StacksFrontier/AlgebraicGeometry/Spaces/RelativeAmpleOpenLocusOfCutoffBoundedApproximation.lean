module

public import StacksFrontier.AlgebraicGeometry.CofilteredLimits.Basic
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLimitExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ConstantBaseChangeSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.CutoffBoundedSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleOpenLocusOfApproximation

/-!
# Stacks 0D3D from a Noetherian approximation bounded by the cutoff

`AlgebraicGeometry.Space.exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_approximation`
proves Stacks 0D3D from its inputs with the standing convention of Section 70.2 (tag 07SD) read
as an abstract property `Conv` of inverse systems. This file takes for `Conv` the
cofinality-free convention `AlgebraicGeometry.Space.IsCutoffBoundedSystem`: fewer stages than the
site's cutoff, one cardinal below the cutoff bounding the hom types, and uniformly bounded base
changes of the stages. Unlike the bound by the cofinality of the cutoff, this convention can be
met by the approximation Stacks 0A0X produces
(`AlgebraicGeometry.Space.exists_descentSituation_arrow_isCutoffBoundedSystem_of_approximations`).

Under this convention the inputs Stacks 07SF, part (1), the passage of the convention to the
system of fibres, and the scheme limit of the stages over a representable stage are proved
here or in `StacksFrontier/AlgebraicGeometry/Spaces/Limits/CutoffBoundedSystem.lean`.

## Main results

* `AlgebraicGeometry.Space.isCutoffBoundedSystem_constantBaseChangeSystem`: the convention
  passes from `X` to the system `Xᵢ ×_{Yᵢ} K`.
* `AlgebraicGeometry.Space.preservesLimit_toScheme_of_overLift_of_baseChangeSizeBounded`: the
  underlying scheme functor preserves the limit of the stages over a representable stage of a
  system with uniformly bounded base changes, with no condition on the cofinality of the cutoff.
* `Space.exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_cutoffBoundedApproximation`:
  the statement of Stacks 0D3D from Stacks 0A0X for systems bounded by the cutoff, Stacks 0D3A,
  and Stacks 07SQ, 07SR and 0D2X, part (2), for systems bounded by the cutoff.

## Implementation notes

The library has Stacks 07SQ, 07SR and 0D2X, part (2), only for an index set below the
cofinality of the cutoff. The forms for a system bounded by the cutoff are taken here as the
hypotheses `h07SQ`, `h07SR` and `h0D2X`, stated exactly as the assembly consumes them. Nothing
here is registered.

## References

* [Stacks Project, Tag 0D3D](https://stacks.math.columbia.edu/tag/0D3D)
* [Stacks Project, Tag 0A0X](https://stacks.math.columbia.edu/tag/0A0X)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of systems of presheaves on the big fppf site is deep
/-- Pullbacks of inverse systems of presheaves on the big fppf site (instance search times out
without this shortcut). -/
local instance hasPullbacks_system_RelativeAmpleOpenLocusOfCutoffBoundedApproximation
    {I : Type u} [Preorder I] :
    HasPullbacks (Iᵒᵖ ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) := inferInstance

local instance (priority := high)
    hasPullback_system_RelativeAmpleOpenLocusOfCutoffBoundedApproximation
    {I : Type u} [Preorder I] {X Y Z : Iᵒᵖ ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    (f : X ⟶ Z) (g : Y ⟶ Z) : HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **The convention passes to the system of fibres.** Let `φ : X ⟶ Y` be a morphism of inverse
systems of algebraic spaces with affine transition morphisms, `cY` a cone over `Y` and
`k : K ⟶ cY.pt`. If `X` is bounded by the cutoff then so is the system `Xᵢ ×_{Yᵢ} K`: it has the
same index category, and its first projection to `X` together with any transition morphism is
jointly monomorphic, because the second projection to the constant system `K` is compatible with
the transition morphisms, so `AlgebraicGeometry.Space.baseChangeSizeBounded_of_jointlyMono`
applies. -/
theorem isCutoffBoundedSystem_constantBaseChangeSystem {I : Type u} [Preorder I]
    [IsDirected I (· ≤ ·)] [Nonempty I] {X Y : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (φ : X ⟶ Y) {cY : Cone Y} {K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (k : K ⟶ cY.pt)
    (hX : ∀ i, IsAlgebraicSpace B S hS (X.obj i))
    (hXaff : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom B S hS (X.map a))
    (hXc : IsCutoffBoundedSystem B S hS X) :
    IsCutoffBoundedSystem B S hS (constantBaseChangeSystem φ k) := by
  refine ⟨hXc.1, hXc.2.1, ?_⟩
  refine baseChangeSizeBounded_of_jointlyMono B S hS (F := 𝟭 _) (D := X)
    (pullback.fst φ (constantBaseChangeMap k)) ?_ hX hXaff hXc.2.2
  intro j j' a T x y h₁ h₂
  have hsnd : (constantBaseChangeSystem φ k).map a ≫
      (pullback.snd φ (constantBaseChangeMap k)).app j' =
        (pullback.snd φ (constantBaseChangeMap k)).app j := by
    rw [(pullback.snd φ (constantBaseChangeMap k)).naturality a]
    simp
  refine (isPullback_constantBaseChangeSystem φ k j).hom_ext h₂ ?_
  rw [← hsnd, ← Category.assoc, h₁, Category.assoc]

/-- For a system with uniformly bounded base changes, one cardinal below the cutoff bounds the
sizes of all the stages of a lift `W` of the stages over `i₀`. -/
private theorem exists_size_toScheme_obj_le_of_overLift {J : Type u} [Category.{u} J]
    {D : J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hB : BaseChangeSizeBounded B S hS D) (i₀ : J)
    (W : Over i₀ ⥤ BigFppfOver B S hS) (e : W ⋙ yoneda ≅ Over.forget i₀ ⋙ D) :
    ∃ μ < B.cutoff, ∀ k : Over i₀, ((BigFppfOver.toScheme B S hS).obj (W.obj k)).size ≤ μ := by
  let j₀ : Over i₀ := Over.mk (𝟙 i₀)
  obtain ⟨μ, hμ, hbound⟩ := hB i₀ (W.obj j₀) (e.hom.app j₀)
  refine ⟨μ, hμ, fun k => ?_⟩
  let m : k ⟶ j₀ := Over.homMk k.hom
  have hsq : CommSq (e.hom.app k) (yoneda.map (W.map m)) (D.map k.hom) (e.hom.app j₀) :=
    ⟨(e.hom.naturality m).symm⟩
  exact hbound k (W.obj k) (e.hom.app k) (yoneda.map (W.map m))
    (IsPullback.of_horiz_isIso hsq)

/-- **The limit of the stages over a representable stage, read in schemes, with no condition on
the cofinality.** Let `D` be a cofiltered inverse system of presheaves on the big fppf site of `S`
with affine transition morphisms, with fewer objects than the site's cutoff, its hom types
bounded by one cardinal below the cutoff and uniformly bounded base changes, and let `W` lift the
stages over a fixed stage `i₀` to objects of the site. Then the underlying scheme functor
preserves the limit of `W`.

This is `AlgebraicGeometry.Space.preservesLimit_toScheme_of_overLift` with the bound by the
cofinality of the cutoff traded for `AlgebraicGeometry.Space.BaseChangeSizeBounded`. The stage
`W k` is the base change of `D k ⟶ D i₀` along the isomorphism `h_{W i₀} ≅ D i₀`, so the one
cardinal that `BaseChangeSizeBounded` attaches to that isomorphism bounds every `W k`; that
uniform bound is what the size estimate of the limit uses, in place of a supremum over the
stages. -/
theorem preservesLimit_toScheme_of_overLift_of_baseChangeSizeBounded {J : Type u}
    [Category.{u} J] [IsCofiltered J] (D : J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    {ν : Cardinal.{u}} (hSize : #J < B.cutoff) (hν : ν < B.cutoff)
    (hHomSize : ∀ i j : J, #(i ⟶ j) ≤ ν) (hB : BaseChangeSizeBounded B S hS D)
    (hAffine : ∀ {i j : J} (f : i ⟶ j), IsAffineHom B S hS (D.map f)) (i₀ : J)
    (W : Over i₀ ⥤ BigFppfOver B S hS) (e : W ⋙ yoneda ≅ Over.forget i₀ ⋙ D) :
    PreservesLimit W (BigFppfOver.toScheme B S hS) := by
  classical
  have hW : ∀ {a b : Over i₀} (f : a ⟶ b), _root_.AlgebraicGeometry.IsAffineHom
      ((AlgebraicGeometry.underlyingDiagram W).map f) := by
    intro a b f
    apply isAffineHom_toScheme_map_of_isAffineHom B S hS
    have h : yoneda.map (W.map f) = e.hom.app a ≫ D.map f.left ≫ e.inv.app b := by
      have hn := e.hom.naturality f
      simp only [Functor.comp_map, Over.forget_map] at hn
      rw [← reassoc_of% hn]
      simp
    rw [h]
    exact isAffineHom_comp B S hS _ _ (isAffineHom_of_isIso _)
      (isAffineHom_comp B S hS _ _ (hAffine f.left) (isAffineHom_of_isIso _))
  have hJ : #(Over i₀) < B.cutoff :=
    mk_over_lt_of_mk_hom_le B.aleph0_lt_cutoff hSize hν hHomSize i₀
  have hJH : ∀ a b : Over i₀, #(a ⟶ b) ≤ ν := fun a b =>
    (Cardinal.mk_le_of_injective (f := fun φ : a ⟶ b => φ.left)
      fun _ _ h => Over.OverMorphism.ext h).trans (hHomSize _ _)
  -- one cardinal bounds all the stages over `i₀`
  obtain ⟨μ, hμ, hμle⟩ := exists_size_toScheme_obj_le_of_overLift hB i₀ W e
  -- the size of the limit of the underlying schemes
  have hsize : ∀ c : Cone (AlgebraicGeometry.underlyingDiagram W), IsLimit c →
      c.pt.size < B.cutoff := by
    intro c hc
    let E := AlgebraicGeometry.underlyingDiagram W
    obtain ⟨j⟩ := IsCofiltered.nonempty (C := Over i₀)
    have hOj : #(Over j) < B.cutoff :=
      mk_over_lt_of_mk_hom_le B.aleph0_lt_cutoff hJ hν hJH j
    have hb : max ℵ₀ (#(Over j) * μ) < B.cutoff :=
      max_lt B.aleph0_lt_cutoff (Cardinal.mul_lt_of_lt B.aleph0_lt_cutoff.le hOj hμ)
    have : _root_.AlgebraicGeometry.IsAffineHom (c.π.app j) :=
      _root_.AlgebraicGeometry.isAffineHom_π_app E c hc j
    have : Nonempty (E.obj j).affineOpens := ⟨⟨⊥, isAffineOpen_bot _⟩⟩
    refine (Scheme.size_le_of_iSup_eq_top
      (fun U : (E.obj j).affineOpens => c.π.app j ⁻¹ᵁ U.1)
      ((c.π.app j).iSup_preimage_eq_top (iSup_affineOpens_eq_top _))).trans_lt ?_
    refine max_lt ((Scheme.mk_affineOpens_le_size _).trans_lt (W.obj j).left.property)
      ((ciSup_le' fun U => ?_).trans_lt hb)
    change (AlgebraicGeometry.opensCone E c j U.1).pt.size ≤ _
    exact Scheme.size_le_of_isLimit_of_isAffine (AlgebraicGeometry.opensDiagram E j U.1)
      (fun k => U.2.preimage (E.map k.hom))
      (fun k => (Scheme.size_coe_opens_le _ _).trans (hμle k.left))
      (AlgebraicGeometry.isLimitOpensCone E c hc j U.1)
  -- the site creates the limit
  let E' := W ⋙ BigFppfOver.forget B S hS
  have : IsConnected (Over i₀) := IsCofiltered.isConnected _
  have : ∀ {a b : Over i₀} (f : a ⟶ b),
      _root_.AlgebraicGeometry.IsAffineHom ((E' ⋙ B.inclusion).map f) := hW
  have : HasLimit (E' ⋙ B.inclusion) := inferInstance
  let : CreatesLimit E' B.inclusion := createsLimitFullSubcategoryInclusion E'
    (hsize (limit.cone _) (limit.isLimit _))
  have : HasLimit E' := hasLimit_of_created E' B.inclusion
  have : PreservesLimit E' B.inclusion := inferInstance
  apply comp_preservesLimit

/-- **Stacks 0D3D, from a Noetherian approximation bounded by the cutoff.** Let `S` be a scheme,
`f : X ⟶ Y` a proper morphism of algebraic spaces over `S` and `L` an invertible `𝒪_X`-module.
There is an open subspace `V ⊆ Y` such that a morphism `g : Y' ⟶ Y` of algebraic spaces factors
through `V` if and only if the pullback of `L` to `X' = Y' ×_Y X` is ample on `X'/Y'`
(Stacks 0D31).

This is `Space.exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_approximation`
with the convention read as `AlgebraicGeometry.Space.IsCutoffBoundedSystem`. Stacks 07SF,
part (1), is `AlgebraicGeometry.Space.isAffineHom_limitπ_of_isCutoffBoundedSystem`; the convention
passes to the system of fibres by
`AlgebraicGeometry.Space.isCutoffBoundedSystem_constantBaseChangeSystem`; and the scheme limit of
the stages over a representable stage is
`AlgebraicGeometry.Space.preservesLimit_toScheme_of_overLift_of_baseChangeSizeBounded`.

The hypotheses are the inputs still owed, all over the integers: `h0A0X`, Stacks 0A0X for a
proper morphism to an affine scheme with the approximating systems bounded by the cutoff, which is
the conclusion of
`AlgebraicGeometry.Space.exists_descentSituation_arrow_isCutoffBoundedSystem_of_approximations`;
`h0D3A`, Stacks 0D3A at a residue field over a Noetherian scheme of the site; and `h07SQ`,
`h07SR`, `h0D2X`, Stacks 07SQ, 07SR and 0D2X, part (2), for situations of Stacks 084R bounded by
the cutoff (the library has them only below the cofinality of the cutoff). It is not
registered. -/
theorem exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_cutoffBoundedApproximation
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (h0A0X : ∀ (U : BigFppfOver B (⊤_ Scheme.{u}) hZ),
      IsAffine ((BigFppfOver.toScheme B _ hZ).obj U) →
      ∀ {X' : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ}
        (f' : X' ⟶ representedAlgebraicSpace B _ hZ U), IsProper B _ hZ f'.hom →
      ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·))
        (DX DY : DescentSituation B (⊤_ Scheme.{u}) hZ hZ I) (φ : DX.system ⟶ DY.system)
        (eX : DX.limitCone.pt ≅ X'.1) (eY : DY.limitCone.pt ≅ yoneda.obj U),
        (∀ i : I, DX.limitCone.π.app (op i) ≫ φ.app (op i) =
          eX.hom ≫ f'.hom ≫ eY.inv ≫ DY.limitCone.π.app (op i)) ∧
        (∀ i : I, IsProper B _ hZ (φ.app (op i)) ∧ IsFinitePresentation B _ hZ (φ.app (op i))) ∧
        (∀ i : I, IsFinitePresentation B _ hZ (terminal.from (DY.system.obj (op i)))) ∧
        IsCutoffBoundedSystem B _ hZ DX.system ∧ IsCutoffBoundedSystem B _ hZ DY.system)
    (h07SQ : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
      (D : DescentSituation B (⊤_ Scheme.{u}) hZ hZ I), IsCutoffBoundedSystem B _ hZ D.system →
        IsAffineSpace B _ hZ D.limitCone.pt →
          ∃ i, D.base ≤ i ∧ IsAffineSpace B _ hZ (D.system.obj (op i)))
    (h07SR : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
      (D : DescentSituation B (⊤_ Scheme.{u}) hZ hZ I), IsCutoffBoundedSystem B _ hZ D.system →
        D.limitCone.pt.IsRepresentable → ∃ i, (D.system.obj (op i)).IsRepresentable)
    (h0D2X : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
      (D : DescentSituation B (⊤_ Scheme.{u}) hZ hZ I), IsCutoffBoundedSystem B _ hZ D.system →
      ∀ (L : Modules.{u, u} B _ hZ D.limitCone.pt D.limitAlgebraicSpace),
        IsInvertibleModule ⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ L →
        ∃ (i : I) (Lᵢ : Modules.{u, u} B _ hZ (D.system.obj (op i)) (D.algebraicSpace i)),
          IsInvertibleModule ⟨D.system.obj (op i), D.algebraicSpace i⟩ Lᵢ ∧
            Nonempty (L ≅ (modulePullback B _ hZ (ObjectProperty.homMk (D.limitCone.π.app (op i)) :
              (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B _ hZ) ⟶
                ⟨D.system.obj (op i), D.algebraicSpace i⟩)).obj Lᵢ))
    (h0D3A : ∀ (T : BigFppfOver B (⊤_ Scheme.{u}) hZ),
      _root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B _ hZ).obj T) →
      ∀ {Xᵢ : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ}
        (fᵢ : Xᵢ ⟶ representedAlgebraicSpace B _ hZ T), IsProper B _ hZ fᵢ.hom →
      ∀ (Lᵢ : Modules.{u, u} B _ hZ Xᵢ.1 Xᵢ.2),
        Stacks.SheafOfModules.IsInvertible (structurePresheaf B _ hZ Xᵢ.1)
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B _ hZ Xᵢ.1 Xᵢ.2).O)).property Lᵢ →
      ∀ y : (BigFppfOver.toScheme B _ hZ).obj T,
        (∀ ⦃X₀ : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ⦄ (p₀ : X₀ ⟶ Xᵢ)
          (f₀ : X₀ ⟶ representedAlgebraicSpace B _ hZ
            (residueFieldObject B _ hZ T y (B.residueField_spec_contains T.left.property y))),
          IsPullback p₀ f₀ fᵢ (ObjectProperty.homMk (yoneda.map
            (residueFieldMap B _ hZ T y (B.residueField_spec_contains T.left.property y)))) →
          IsRelativelyAmple B _ hZ f₀ ((modulePullback B _ hZ p₀).obj Lᵢ)) →
        ∃ V : ((BigFppfOver.toScheme B _ hZ).obj T).Opens, y ∈ V ∧
          ∀ ⦃X₁ : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ⦄ (p₁ : X₁ ⟶ Xᵢ)
            (f₁ : X₁ ⟶ representedAlgebraicSpace B _ hZ (openSub T V)),
            IsPullback p₁ f₁ fᵢ (ObjectProperty.homMk (yoneda.map (openSubHom T V))) →
            IsRelativelyAmple B _ hZ f₁ ((modulePullback B _ hZ p₁).obj Lᵢ))
    {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (hf : IsProper B S hS f.hom)
    {L : Modules.{u, u} B S hS X.1 X.2}
    (hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O)).property L) :
    ∃ V : Subfunctor Y.1, IsOpenSubspace B S hS V ∧
      ∀ ⦃X' Y' : AlgebraicSpaces B S hS⦄ (g : Y' ⟶ Y) (p : X' ⟶ X) (f' : X' ⟶ Y'),
        IsPullback p f' f g →
          ((∃ l : Y'.1 ⟶ V.toFunctor, l ≫ V.ι = g.hom) ↔
            IsRelativelyAmple B S hS f' ((modulePullback B S hS p).obj L)) := by
  refine exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_approximation hZ
    (fun {J} [Category.{u} J] D => IsCutoffBoundedSystem B _ hZ D)
    h0A0X h07SQ h07SR ?_ h0D2X ?_ ?_ h0D3A hf hL
  · intro J _ _ D hc hA i
    exact isAffineHom_limitπ_of_isCutoffBoundedSystem B _ hZ D hc hA i
  · intro I _ _ _ DX DY φ V hV k hX hY
    exact isCutoffBoundedSystem_constantBaseChangeSystem φ k
      (fun i => DX.algebraicSpace i.unop) DX.transition_affine hX
  · intro I _ _ D hc i₀ _ W ⟨e⟩
    have : Nonempty I := ⟨D.base⟩
    obtain ⟨hSize, ⟨ν, hν, hHomSize⟩, hB⟩ := hc
    exact preservesLimit_toScheme_of_overLift_of_baseChangeSizeBounded D.system hSize hν
      hHomSize hB D.transition_affine (op i₀) W e

end AlgebraicGeometry.Space

end
