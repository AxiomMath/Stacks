module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitProjectionAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineChartSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DominantNoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactImageEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactSchemeTheoreticDensity

/-!
# Limits of chart systems of an inverse system with dominant projections

Let `D` be a cofiltered inverse system of algebraic spaces over `S` with affine transition
morphisms whose limit is an algebraic space, and let `U₀ ⟶ D i₀` be an affine étale chart of a
stage. The base changes `U_j = U₀ ×_{D i₀} D j` are affine objects of the big fppf site. Without
any bound on the size of the index category their limit in the site need not be the limit of
their underlying schemes: an uncountable field `k` is the colimit of its finitely generated
subrings `A_i`, and the presheaf limit of the `Spec A_i` is empty while the limit of schemes is
`Spec k`.

If the projections `lim D ⟶ D j` are scheme-theoretically dominant, the two limits agree. The
limit `P` of the presheaves the `U_j` represent is the base change of `lim D ⟶ D i₀` along the
chart, an affine object of the site by Stacks 07SF, part (1), and each `P ⟶ U_j` is
scheme-theoretically dominant, being an étale base change of a dominant quasi-compact morphism
(Stacks 082Z, part (3)). So each `Γ(U_j) ⟶ Γ(P)` is injective, hence so is
`Γ(lim U_j) = colim Γ(U_j) ⟶ Γ(P)`, and the closed subscheme of `lim U_j` cut out by the kernel of
that map, which is the limit in the site, is all of `lim U_j`.

## Main results

* `AlgebraicGeometry.Space.AffineChartSystem.nonempty_limitBridge_of_dominant`: under these
  hypotheses every chart system along an étale chart has a limit bridge, with no condition on
  the size of the index category.
* `AlgebraicGeometry.Space.HasChartLimitBridges`: every chart system of a stage along an étale
  chart has a limit bridge; `AlgebraicGeometry.Space.hasChartLimitBridges_of_small`,
  `AlgebraicGeometry.Space.hasChartLimitBridges_of_dominant` and
  `AlgebraicGeometry.Space.NoetherianApproximation.hasChartLimitBridges_of_dominant` supply it.

## References

* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Tag 082Z](https://stacks.math.columbia.edu/tag/082Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Limits of presheaves on the big fppf site over `S`, given directly: instance search for them
times out under Lean v4.35.0. These are `local` instances, with names unique to this file. -/
local instance (priority := high) hasLimitsOfSize_presheaf_dominantChartLimit :
    HasLimitsOfSize.{u, u} ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfSize

local instance (priority := high) epi_isoHom_presheaf_dominantChartLimit
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : X ≅ Y) : Epi e.hom :=
  IsIso.epi_of_iso _

local instance (priority := high) epi_isoInv_presheaf_dominantChartLimit
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : X ≅ Y) : Epi e.inv :=
  IsIso.epi_of_iso _

local instance (priority := high) hasPullbacks_presheaf_dominantChartLimit :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_dominantChartLimit
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  hasPullbacks_presheaf_dominantChartLimit.has_limit _

/-- **The scheme-theoretic image is unchanged by postcomposition with an isomorphism**, when it is
everything. -/
theorem schemeTheoreticImageSubfunctor_comp_isIso_eq_top
    {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} (e : Y ⟶ Y') [IsIso e]
    (hY : IsAlgebraicSpace B S hS Y) (hY' : IsAlgebraicSpace B S hS Y')
    (h : schemeTheoreticImageSubfunctor B S hS f = ⊤) :
    schemeTheoreticImageSubfunctor B S hS (f ≫ e) = ⊤ := by
  have hle := schemeTheoreticImageSubfunctor_le_preimage B S hS (f₁ := f) (q := e) (p := 𝟙 X)
    (f₂ := f ≫ e) hY hY' (Category.id_comp _).symm
  rw [h] at hle
  refine le_antisymm le_top fun U x _ => ?_
  have hx : (inv e).app U x ∈
      ((schemeTheoreticImageSubfunctor B S hS (f ≫ e)).preimage e).obj U :=
    hle U (by simp)
  change e.app U ((inv e).app U x) ∈ (schemeTheoreticImageSubfunctor B S hS (f ≫ e)).obj U at hx
  rwa [← types_comp_apply ((inv e).app U) (e.app U), ← NatTrans.comp_app, IsIso.inv_hom_id,
    NatTrans.id_app, types_id_apply] at hx

section ChartSystem

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {i₀ : I}
  {D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀}

omit [IsCofiltered I] in
/-- The canonical cone on the base change of `limit.π D i₀` along `f₀` is, at each stage
`j`, a cartesian square over the limit projection `limit.π D j`. -/
theorem isPullback_stageBaseChangeCone_π (j : Over i₀) :
    IsPullback (stageBaseChangeConeFst B S hS i₀ D U₀ f₀)
      ((stageBaseChangeCone B S hS i₀ D U₀ f₀).π.app j) (limit.π D j.left)
      (stageBaseChangeFst B S hS i₀ D U₀ f₀ j) := by
  have hout : IsPullback ((stageBaseChangeCone B S hS i₀ D U₀ f₀).π.app j ≫
        stageBaseChangeSnd B S hS i₀ D U₀ f₀ j)
      (stageBaseChangeConeFst B S hS i₀ D U₀ f₀) f₀ (limit.π D j.left ≫ D.map j.hom) := by
    rw [stageBaseChangeCone_π_comp_snd, limit.w]
    exact (isPullback_stageBaseChangeCone B S hS).flip
  exact (IsPullback.of_right hout (stageBaseChangeCone_π_comp_fst B S hS j)
    (isPullback_stageBaseChange B S hS i₀ D U₀ f₀ j).flip).flip

/-- **The projections of the canonical cone on the base change along an étale chart are
scheme-theoretically dominant**, when the limit projections of `D` are: each is an étale base
change of the quasi-compact limit projection `limit.π D j` (Stacks 082Z, part (3)). -/
theorem schemeTheoreticImageSubfunctor_stageBaseChangeCone_π
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (a : i ⟶ j), IsAffineHom B S hS (D.map a))
    (hlim : IsAlgebraicSpace B S hS (limit D))
    (hdom : ∀ i, schemeTheoreticImageSubfunctor B S hS (limit.π D i) = ⊤)
    (hf₀ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f₀) (j : Over i₀) :
    schemeTheoreticImageSubfunctor B S hS ((stageBaseChangeCone B S hS i₀ D U₀ f₀).π.app j) =
      ⊤ := by
  have hsq := isPullback_stageBaseChangeCone_π (f₀ := f₀) j
  have hG : IsAlgebraicSpace B S hS (pullback (D.map j.hom) f₀) :=
    isAlgebraicSpace_pullback B S hS _ _ (hD j.left)
      (isAlgebraicSpace_yoneda B S hS _) (hD i₀)
  have hfst : IsEtale B S hS (stageBaseChangeFst B S hS i₀ D U₀ f₀ j) :=
    isEtale_of_presheaf_etale B S hS
      (presheaf_of_isPullback B S hS (isPullback_stageBaseChange B S hS i₀ D U₀ f₀ j).flip hf₀)
  have hqc : IsQuasiCompact B S hS (limit.π D j.left) :=
    isQuasiCompact_of_isAffineHom' B S hS _ hlim (hD j.left)
      (isAffineHom_π_of_isAlgebraicSpace B S hS D hAffine (limit.isLimit D) hlim j.left
        (hD j.left))
  rw [← hsq.isoPullback_hom_snd, schemeTheoreticImageSubfunctor_comp_of_epi]
  refine (schemeTheoreticImageSubfunctor_pullback_snd_of_isEtale_of_isQuasiCompact' B S hS _ _
    hlim (hD j.left) hG hqc hfst).trans ?_
  rw [hdom]
  rfl

/-- **A chart system of an inverse system with dominant projections has a limit bridge**, with
no condition on the size of the index category. Let `D` be a cofiltered inverse system of
algebraic spaces with affine transition morphisms whose limit is an algebraic space and whose
limit projections are scheme-theoretically dominant, and let `C` be a chart system of `D` along
an étale chart `f₀ : U₀ ⟶ D i₀`. Then the limit of `C` in the big fppf site exists, is the limit
of the underlying schemes, and represents the base change of `limit.π D i₀` along `f₀`.

The base change `P` is represented by an affine object of the site, by Stacks 07SF, part (1);
the limit in the site is the closed subscheme of the scheme limit `L` cut out by the kernel of
`Γ(L) ⟶ Γ(P)`. Every global function on `L` comes from some chart `U_k`, and `Γ(U_k) ⟶ Γ(P)` is
injective because `P ⟶ U_k` is scheme-theoretically dominant, so the kernel vanishes. -/
theorem AffineChartSystem.nonempty_limitBridge_of_dominant
    (C : AffineChartSystem B S hS i₀ D U₀ f₀)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (a : i ⟶ j), IsAffineHom B S hS (D.map a))
    (hlim : IsAlgebraicSpace B S hS (limit D))
    (hdom : ∀ i, schemeTheoreticImageSubfunctor B S hS (limit.π D i) = ⊤)
    (hf₀ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f₀) :
    Nonempty C.LimitBridge := by
  classical
  have hbase : IsLimit (stageBaseChangeCone B S hS i₀ D U₀ f₀) :=
    isLimitPullbackLimitOverPost B S hS D i₀ f₀
  let c : Cone (C.siteDiagram ⋙ yoneda) :=
    (Cone.postcompose C.iso.inv).obj (stageBaseChangeCone B S hS i₀ D U₀ f₀)
  have hc : IsLimit c := (IsLimit.postcomposeInvEquiv C.iso _).symm hbase
  -- the base change of `limit.π D i₀` along `f₀` is represented by an affine object
  obtain ⟨A, p, q, hpb⟩ := isAffineHom_π_of_isAlgebraicSpace B S hS D hAffine (limit.isLimit D)
    hlim i₀ (hD i₀) U₀ f₀
  let e : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj A) ≅ c.pt := hpb.isoPullback
  have hW : ∀ k, IsAffine ((BigFppfOver.toScheme B S hS).obj (C.siteDiagram.obj k)) :=
    C.isAffine_obj
  -- the charts of the base change are dominated by it
  have hdomk (k : Over i₀) : schemeTheoreticImageSubfunctor B S hS (e.hom ≫ c.π.app k) = ⊤ := by
    rw [schemeTheoreticImageSubfunctor_comp_of_epi]
    exact schemeTheoreticImageSubfunctor_comp_isIso_eq_top (C.iso.inv.app k)
      (isAlgebraicSpace_pullback B S hS _ _ (hD k.left) (isAlgebraicSpace_yoneda B S hS _)
        (hD i₀))
      (isAlgebraicSpace_yoneda B S hS _)
      (schemeTheoreticImageSubfunctor_stageBaseChangeCone_π hD hAffine hlim hdom hf₀ k)
  have hker (k : Over i₀) :
      ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (e.hom ≫ c.π.app k))).ker = ⊥ := by
    have hmem : 𝟙 (C.siteDiagram.obj k) ∈ (schemeTheoreticImageSubfunctor B S hS
        (yoneda.map (yoneda.preimage (e.hom ≫ c.π.app k)))).obj (op (C.siteDiagram.obj k)) := by
      rw [Functor.map_preimage, hdomk k]
      trivial
    have hle := ker_le_of_mem_schemeTheoreticImageSubfunctor B S hS _ _ hmem
    rw [CategoryTheory.Functor.map_id, Scheme.Hom.ker_eq_bot_of_isIso (𝟙 _)] at hle
    exact le_bot_iff.1 hle
  have hW' : ∀ k, IsAffine ((C.siteDiagram ⋙ BigFppfOver.toScheme B S hS).obj k) := hW
  have hideal : BigFppfOver.coverIdeal C.siteDiagram e.hom = ⊥ := by
    refine eq_bot_iff.2 fun a ha => ?_
    obtain ⟨k, t, rfl⟩ := exists_appTop_π_eq_of_isAffine_of_isLimit
      (C.siteDiagram ⋙ BigFppfOver.toScheme B S hS) _ (limit.isLimit _) a
    have h0 : ((limit.π (C.siteDiagram ⋙ BigFppfOver.toScheme B S hS) k).appTop ≫
        (BigFppfOver.limitPoint C.siteDiagram e.hom).appTop) t = 0 := ha
    rw [← Scheme.Hom.comp_appTop, BigFppfOver.limitPoint_π] at h0
    set m := (BigFppfOver.toScheme B S hS).map (yoneda.preimage (e.hom ≫ c.π.app k))
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((BigAffineFppf.inclusion B S hS).obj A)) := A.property
    have htk : t ∈ RingHom.ker m.appTop.hom := h0
    have hideal' := Scheme.Hom.ker_apply m ⟨⊤, isAffineOpen_top _⟩
    rw [hker k] at hideal'
    have ht : t ∈ (⊥ : Scheme.IdealSheafData _).ideal ⟨⊤, isAffineOpen_top _⟩ := by
      rwa [hideal']
    simp [show t = 0 by simpa using ht]
  -- so the closed subscheme cut out by the kernel is the whole scheme limit
  have hquot : IsIso (BigFppfOver.coverQuot C.siteDiagram e.hom) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨fun x y hxy => ?_, Ideal.Quotient.mk_surjective⟩
    have hxy' : x - y ∈ BigFppfOver.coverIdeal C.siteDiagram e.hom :=
      Ideal.Quotient.eq.mp hxy
    rwa [hideal, Ideal.mem_bot, sub_eq_zero] at hxy'
  have hι : IsIso (BigFppfOver.coverι C.siteDiagram e.hom) := by
    rw [BigFppfOver.coverι]
    infer_instance
  let d := BigFppfOver.coverCone C.siteDiagram e.hom
  have hd : IsLimit d := BigFppfOver.isLimitCoverCone C.siteDiagram hc inferInstance
  have hdS : IsLimit ((BigFppfOver.toScheme B S hS).mapCone d) :=
    IsLimit.ofIsoLimit (limit.isLimit _)
      (Cone.ext (asIso (BigFppfOver.coverι C.siteDiagram e.hom)).symm fun k => by
        show limit.π _ k = inv (BigFppfOver.coverι C.siteDiagram e.hom) ≫
          (BigFppfOver.coverι C.siteDiagram e.hom ≫ limit.π _ k)
        simp)
  have hpost : IsLimit ((Cone.postcompose C.iso.hom).obj (yoneda.mapCone d)) :=
    (IsLimit.postcomposeHomEquiv C.iso _).symm (isLimitOfPreserves yoneda hd)
  exact ⟨{ cone := d
           isLimit := hd
           schemeIsLimit := hdS
           iso := hpost.conePointUniqueUpToIso hbase
           iso_comp_π := fun j ↦ hpost.conePointUniqueUpToIso_hom_comp hbase j }⟩

end ChartSystem

/-- **Every chart system of a stage along an étale chart has a limit bridge.** This is the
hypothesis under which the limit criteria of Stacks 0CP4 hold for an inverse system of
algebraic spaces with no condition on the size of its index category. -/
abbrev HasChartLimitBridges {I : Type u} [Category.{u} I]
    (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  ∀ (i₀ : I) (U₀ : BigAffineFppf B S hS)
    (f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀),
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f₀ →
    ∀ C : AffineChartSystem B S hS i₀ D U₀ f₀, Nonempty C.LimitBridge

/-- An inverse system indexed by a category small for the site has limit bridges (Stacks 07SF). -/
theorem hasChartLimitBridges_of_small {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hSize : Cardinal.mk I < B.cutoff.ord.cof)
    (hHomSize : ∀ i j : I, Cardinal.mk (i ⟶ j) < B.cutoff.ord.cof) :
    HasChartLimitBridges D :=
  fun _ _ _ _ C => ⟨C.limitBridge hSize hHomSize⟩

/-- An inverse system of algebraic spaces with affine transition morphisms whose limit is an
algebraic space with scheme-theoretically dominant projections has limit bridges, with no
condition on the size of its index category. -/
theorem hasChartLimitBridges_of_dominant {I : Type u} [Category.{u} I] [IsCofiltered I]
    {D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (a : i ⟶ j), IsAffineHom B S hS (D.map a))
    (hlim : IsAlgebraicSpace B S hS (limit D))
    (hdom : ∀ i, schemeTheoreticImageSubfunctor B S hS (limit.π D i) = ⊤) :
    HasChartLimitBridges D :=
  fun _ _ _ hf₀ C => C.nonempty_limitBridge_of_dominant hD hAffine hlim hdom hf₀

/-- **A Noetherian approximation with scheme-theoretically dominant projections has limit
bridges**, with no condition on the size of its index set: its limit is the given algebraic
space, and the limit projections are its projections up to an isomorphism. -/
theorem NoetherianApproximation.hasChartLimitBridges_of_dominant
    {hZ : B.Contains (⊤_ Scheme.{u})} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (A : NoetherianApproximation B S hS hZ X)
    (hdom : ∀ j, letI := A.preorder;
      schemeTheoreticImageSubfunctor B S hS (A.π.app j) = ⊤) :
    letI := A.preorder
    HasChartLimitBridges A.diagram := by
  let := A.preorder
  let := A.nonempty
  let := A.isDirected
  let : IsCofiltered (A.I)ᵒᵖ := A.isCofiltered_op
  let e : X ≅ limit A.diagram := A.isLimit.conePointUniqueUpToIso (limit.isLimit _)
  have he (j : (A.I)ᵒᵖ) : e.inv ≫ A.π.app j = limit.π A.diagram j :=
    A.isLimit.conePointUniqueUpToIso_inv_comp (limit.isLimit _) j
  refine Space.hasChartLimitBridges_of_dominant A.isAlgebraicSpace (fun g => A.isAffineHom_map g)
    (isAlgebraicSpace_of_iso B S hS e hX) fun j => ?_
  rw [← he, schemeTheoreticImageSubfunctor_comp_of_epi]
  exact hdom j

end AlgebraicGeometry.Space

end
