module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Limits.RelativeApproximation.ClosedImmersionDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteNoetherianApproximation.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.AffineMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Isomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SchemeStage
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SchemeStageSiteSmall
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartRespectsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.BaseChangeLimitsConvention
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartSystemConvention
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ImageSystemProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.NoetherianApproximationInduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SiteConventionAlgebraicLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SiteConventionCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae03KM
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocusPreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas

/-!
# Absolute Noetherian approximation: descending the étale scheme `W ⟶ U`

In the proof of Stacks 07SU one has a directed limit `U = lim U_i` of quasi-compact
quasi-separated algebraic spaces of finite type over `Spec ℤ` with affine transition morphisms,
and a quasi-compact quasi-separated scheme `W` étale over `U`. By Stacks 07SK and 07SL the
morphism `W ⟶ U` descends to an étale morphism `W_0 ⟶ U_0` of finite presentation, the base
changes `W_i = W_0 ×_{U_0} U_i` have limit `W`, and by Stacks 07SR they are schemes from some
index on. This file carries out that step. The descent results are applied in their forms under
the chapter's standing convention of Section 70.2 (tag 07SD) on the inverse system, which asks
nothing of the index.

## Main results

* `AlgebraicGeometry.Space.exists_etaleSchemeSystem_of_isLimit`: the step itself.
* `AlgebraicGeometry.Space.exists_etaleSchemeSystem_of_stages`: its last part, the passage from
  a cartesian system of representable presheaves étale over the stages to a system of schemes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {hZ : B.Contains (⊤_ Scheme.{u})}

/-! ### From a cartesian system of representable presheaves to a system of schemes -/

/-- **The last part of the step of Stacks 07SU.** Let `E` be an inverse system of presheaves
over the tail of the index set above `k`, mapping to the restriction of the system `D` with
cartesian naturality squares, whose members are representable, quasi-compact and étale over the
stages, and whose limit is the representable presheaf of `W`, compatibly with the given morphism
`W ⟶ Y`. Choosing representing objects turns `E` into a system of schemes with all the
properties asked for in the step of Stacks 07SU. -/
theorem exists_etaleSchemeSystem_of_stages
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)
    (hconv : SiteContainsBaseChangeLimits B (⊤_ Scheme.{u}) hZ D)
    (hD : ∀ j, IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ (D.obj j))
    (hAff : ∀ {j j' : Iᵒᵖ} (e : j ⟶ j'), IsAffineHom B (⊤_ Scheme.{u}) hZ (D.map e))
    (hDft : ∀ j, IsFiniteType B (⊤_ Scheme.{u}) hZ
      (terminal.from (viewOverIntegers B (⊤_ Scheme.{u}) hZ hZ (D.obj j))))
    {Y : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (uπ : (Functor.const Iᵒᵖ).obj Y ⟶ D)
    (W : BigFppfOver B (⊤_ Scheme.{u}) hZ) (gW : yoneda.obj W ⟶ Y) (k : I)
    (E : (LimitTail I k)ᵒᵖ ⥤ (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)
    (p : E ⟶ (Subtype.mono_coe fun i => k ≤ i).functor.op ⋙ D)
    (hpb : ∀ {j j' : (LimitTail I k)ᵒᵖ} (e : j ⟶ j'), IsPullback (E.map e) (p.app j)
      (p.app j') (((Subtype.mono_coe fun i => k ≤ i).functor.op ⋙ D).map e))
    (hrep : ∀ j, (E.obj j).IsRepresentable)
    (hEqc : ∀ j, IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ (E.obj j))
    (hEet : ∀ j, IsEtale B (⊤_ Scheme.{u}) hZ (p.app j))
    (c : (Functor.const (LimitTail I k)ᵒᵖ).obj (yoneda.obj W) ⟶ E)
    (hc : IsLimit (Cone.mk _ c))
    (hcomp : ∀ j, c.app j ≫ p.app j = gW ≫ uπ.app (op j.unop.1))
    (hcart : ∀ j, IsPullback (c.app j) gW (p.app j) (uπ.app (op j.unop.1))) :
    ∃ (Ws : (LimitTail I k)ᵒᵖ ⥤ BigFppfOver B (⊤_ Scheme.{u}) hZ)
      (g : Ws ⋙ yoneda ⟶ (Subtype.mono_coe fun i => k ≤ i).functor.op ⋙ D)
      (wπ : (Functor.const (LimitTail I k)ᵒᵖ).obj W ⟶ Ws),
      (∀ j, IsEtale B (⊤_ Scheme.{u}) hZ (g.app j)) ∧
      (∀ {j j' : (LimitTail I k)ᵒᵖ} (e : j ⟶ j'), IsPullback (yoneda.map (Ws.map e))
        (g.app j) (g.app j') (((Subtype.mono_coe fun i => k ≤ i).functor.op ⋙ D).map e)) ∧
      (∀ j, CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (Ws.obj j))) ∧
      (∀ j, LocallyOfFiniteType
        (terminal.from ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (Ws.obj j)))) ∧
      (∀ {j j' : (LimitTail I k)ᵒᵖ} (e : j ⟶ j'), _root_.AlgebraicGeometry.IsAffineHom
        ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (Ws.map e))) ∧
      (∀ j, yoneda.map (wπ.app j) ≫ g.app j = gW ≫ uπ.app (op j.unop.1)) ∧
      (∀ j, IsPullback (yoneda.map (wπ.app j)) gW (g.app j) (uπ.app (op j.unop.1))) ∧
      Nonempty (IsLimit ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).mapCone
        (Cone.mk W wπ))) := by
  classical
  have _ : Nonempty (LimitTail I k) := ⟨⟨k, le_rfl⟩⟩
  have _ : IsCofiltered (LimitTail I k)ᵒᵖ := inferInstance
  have hrepr : ∀ j, yoneda.essImage (E.obj j) := fun j => ⟨(E.obj j).reprX, ⟨(E.obj j).reprW⟩⟩
  let Ws := Functor.essImage.liftFunctor E yoneda hrepr
  let α : Ws ⋙ yoneda ≅ E := Functor.essImage.liftFunctorCompIso E yoneda hrepr
  let g : Ws ⋙ yoneda ⟶ (Subtype.mono_coe fun i => k ≤ i).functor.op ⋙ D := α.hom ≫ p
  let wπ : (Functor.const (LimitTail I k)ᵒᵖ).obj W ⟶ Ws :=
    { app := fun j => yoneda.preimage (c.app j ≫ α.inv.app j)
      naturality := fun j j' e => yoneda.map_injective (by
        have h₁ := c.naturality e
        have h₂ := α.inv.naturality e
        simp only [Functor.const_obj_map, Functor.const_obj_obj, Category.id_comp] at h₁
        simp only [Functor.const_obj_map, Functor.const_obj_obj, Functor.map_comp,
          Category.id_comp, Functor.map_preimage]
        rw [h₁, Category.assoc, h₂]
        rfl) }
  have hyw : ∀ j, yoneda.map (wπ.app j) = c.app j ≫ α.inv.app j := fun j =>
    Functor.map_preimage _ _
  have hWs : ∀ j, IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ (yoneda.obj (Ws.obj j)) := fun j =>
    isAlgebraicSpace_yoneda B (⊤_ Scheme.{u}) hZ _
  have hG : ∀ j : (LimitTail I k)ᵒᵖ, IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ
      (((Subtype.mono_coe fun i => k ≤ i).functor.op ⋙ D).obj j) := fun j => hD _
  have het : ∀ j, IsEtale B (⊤_ Scheme.{u}) hZ (g.app j) := fun j =>
    isEtale_comp B (⊤_ Scheme.{u}) hZ (isEtale_of_iso B (⊤_ Scheme.{u}) hZ (α.app j)) (hEet j)
  have hsq : ∀ {j j' : (LimitTail I k)ᵒᵖ} (e : j ⟶ j'), IsPullback (yoneda.map (Ws.map e))
      (g.app j) (g.app j') (((Subtype.mono_coe fun i => k ≤ i).functor.op ⋙ D).map e) := by
    intro j j' e
    refine (hpb e).of_iso (α.app j).symm (α.app j').symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · exact α.inv.naturality e
    · simp [g]
    · simp [g]
    · simp
  have hAffSp : ∀ {j j' : (LimitTail I k)ᵒᵖ} (e : j ⟶ j'),
      IsAffineHom B (⊤_ Scheme.{u}) hZ (yoneda.map (Ws.map e)) := fun e =>
    IsAffineHom.of_isPullback (hsq e).flip (hAff _)
  have hAffSch : ∀ {j j' : (LimitTail I k)ᵒᵖ} (e : j ⟶ j'),
      _root_.AlgebraicGeometry.IsAffineHom
        ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (Ws.map e)) := fun {j j'} e => by
    have h := ((isAffineHom_tfae_of_isAlgebraicSpace B (⊤_ Scheme.{u}) hZ
      (yoneda.map (Ws.map e)) (hWs j) (hWs j')).out 2 1).mp (hAffSp e)
    exact (presheaf_yoneda_map_iff B (⊤_ Scheme.{u}) hZ inferInstance (Ws.map e)).mp h.2
  have hinit : ∀ j : (LimitTail I k)ᵒᵖ,
      (Over.post (X := j) (Subtype.mono_coe fun i => k ≤ i).functor.op).Initial :=
    fun j => initial_post_limitTailForget k j
  have hconvWs : SiteContainsBaseChangeLimits B (⊤_ Scheme.{u}) hZ (Ws ⋙ yoneda) :=
    SiteContainsBaseChangeLimits.of_isPullback _ g hsq hAff hconv
  have hlimY : IsLimit (yoneda.mapCone (Cone.mk W wπ)) :=
    ((IsLimit.postcomposeInvEquiv α _).symm hc).ofIsoLimit
      (Cone.ext (Iso.refl _) (fun j => by simp [hyw]))
  refine ⟨Ws, g, wπ, het, hsq, fun j => ?_, fun j => ?_, hAffSch, fun j => ?_, fun j => ?_,
    ⟨isLimitMapConeToSchemeOfIsLimitMapConeYoneda Ws hAffSch hconvWs _ hlimY⟩⟩
  · exact compactSpace_of_isQuasiCompactSpace_yoneda_obj B (⊤_ Scheme.{u}) hZ
      (isQuasiCompactSpace_of_iso B (⊤_ Scheme.{u}) hZ (α.app j).symm (hEqc j))
  · exact GluedEtaleQuotient.locallyOfFiniteType_of_etale (hDft _) (g.app j)
      ((isEtale_iff_presheaf_of_yoneda B (⊤_ Scheme.{u}) hZ (g.app j)).mp (het j))
  · rw [hyw]
    simp [g, hcomp]
  · refine (hcart j).of_iso (Iso.refl _) (α.app j).symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [hyw]
    · simp
    · simp [g]
    · simp

/-- **The step of the proof of Stacks 07SU descending `W ⟶ U`.** An étale quasi-compact
quasi-separated scheme `W` over the limit `U = lim U_i` of the system descends to a system of
étale schemes `W_i ⟶ U_i` over the stages at or beyond some index, with cartesian transition
squares, each `W_i` quasi-compact and of finite type over the integers, affine transition
morphisms, cartesian squares `W = W_i ×_{U_i} U`, and limit `W`.

The proof is the source's: `W ⟶ U` is of finite presentation (it is étale, `W` is quasi-compact
and quasi-separated, and `U` is quasi-separated), so by Stacks 07SK it is the base change of a
morphism `W₀ ⟶ U₀` of finite presentation, which by Stacks 07SL is étale after base change to a
later stage; the base changes `W_i = W₀ ×_{U₀} U_i` have limit `W`, so by Stacks 07SR one of them
is a scheme, hence so are all later ones, their transition morphisms being affine. The passage to
a system of objects of the site is `AlgebraicGeometry.Space.exists_etaleSchemeSystem_of_stages`. -/
theorem exists_etaleSchemeSystem_of_isLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)
    (hconv : SiteContainsBaseChangeLimits B (⊤_ Scheme.{u}) hZ D)
    (hD : ∀ j, IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ (D.obj j))
    (hAff : ∀ {j j' : Iᵒᵖ} (e : j ⟶ j'), IsAffineHom B (⊤_ Scheme.{u}) hZ (D.map e))
    (hDqc : ∀ j, IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ (D.obj j))
    (hDqs : ∀ j, IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ (D.obj j))
    (hDft : ∀ j, IsFiniteType B (⊤_ Scheme.{u}) hZ
      (terminal.from (viewOverIntegers B (⊤_ Scheme.{u}) hZ hZ (D.obj j))))
    {Y : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ Y)
    (uπ : (Functor.const Iᵒᵖ).obj Y ⟶ D) (huπ : IsLimit (Cone.mk Y uπ))
    (W : BigFppfOver B (⊤_ Scheme.{u}) hZ)
    (hWc : CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj W))
    (hWqs : QuasiSeparatedSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj W))
    (gW : yoneda.obj W ⟶ Y) (hgW : IsEtale B (⊤_ Scheme.{u}) hZ gW) :
    ∃ (i₀ : I) (Ws : (LimitTail I i₀)ᵒᵖ ⥤ BigFppfOver B (⊤_ Scheme.{u}) hZ)
      (g : Ws ⋙ yoneda ⟶ (Subtype.mono_coe fun i => i₀ ≤ i).functor.op ⋙ D)
      (wπ : (Functor.const (LimitTail I i₀)ᵒᵖ).obj W ⟶ Ws),
      (∀ j, IsEtale B (⊤_ Scheme.{u}) hZ (g.app j)) ∧
      (∀ {j j' : (LimitTail I i₀)ᵒᵖ} (e : j ⟶ j'), IsPullback (yoneda.map (Ws.map e))
        (g.app j) (g.app j') (((Subtype.mono_coe fun i => i₀ ≤ i).functor.op ⋙ D).map e)) ∧
      (∀ j, CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (Ws.obj j))) ∧
      (∀ j, LocallyOfFiniteType
        (terminal.from ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (Ws.obj j)))) ∧
      (∀ {j j' : (LimitTail I i₀)ᵒᵖ} (e : j ⟶ j'), _root_.AlgebraicGeometry.IsAffineHom
        ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (Ws.map e))) ∧
      (∀ j, yoneda.map (wπ.app j) ≫ g.app j = gW ≫ uπ.app (op j.unop.1)) ∧
      (∀ j, IsPullback (yoneda.map (wπ.app j)) gW (g.app j) (uπ.app (op j.unop.1))) ∧
      Nonempty (IsLimit ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).mapCone
        (Cone.mk W wπ))) := by
  classical
  have _ : IsCofiltered Iᵒᵖ := inferInstance
  -- `Y` is the chosen limit of `D`
  let e : Y ≅ limit D := huπ.conePointUniqueUpToIso (limit.isLimit D)
  have he : ∀ j, e.hom ≫ limit.π D j = uπ.app j := fun j =>
    huπ.conePointUniqueUpToIso_hom_comp (limit.isLimit D) j
  have hlimAlg : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ (limit D) :=
    isAlgebraicSpace_limit_of_siteContainsBaseChangeLimits B (⊤_ Scheme.{u}) hZ D hconv hD hAff
      hDqc
  obtain ⟨i⟩ := ‹Nonempty I›
  have hπaff : ∀ j, IsAffineHom B (⊤_ Scheme.{u}) hZ (limit.π D j) :=
    isAffineHom_limitπ_of_siteContainsBaseChangeLimits B (⊤_ Scheme.{u}) hZ D hconv hAff
  have hlimqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ (limit D) :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ hlimAlg (hDqs (op i))
      (isQuasiSeparated_of_isAffineHom B (⊤_ Scheme.{u}) hZ (limit.π D (op i)) hlimAlg (hD _)
        (hπaff _))
  -- `W ⟶ U` is of finite presentation
  have hWalg := isAlgebraicSpace_yoneda B (⊤_ Scheme.{u}) hZ W
  have hWqs' : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ (yoneda.obj W) :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B (⊤_ Scheme.{u}) hZ _ hZ
      ⟨W, hWqs, ⟨Functor.RepresentableBy.yoneda W⟩⟩
  have hWqc' := isQuasiCompactSpace_yoneda B (⊤_ Scheme.{u}) hZ W hWc
  have hEt : IsEtale B (⊤_ Scheme.{u}) hZ (gW ≫ e.hom) :=
    isEtale_comp B (⊤_ Scheme.{u}) hZ hgW (isEtale_of_iso B (⊤_ Scheme.{u}) hZ e)
  have hFp : IsFinitePresentation B (⊤_ Scheme.{u}) hZ (gW ≫ e.hom) :=
    ⟨isLocallyOfFinitePresentation_of_isEtale B (⊤_ Scheme.{u}) hZ hEt,
      isQuasiCompact_of_isQuasiCompactSpace B (⊤_ Scheme.{u}) hZ hZ hlimAlg hlimqs hWqc' _,
      isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B (⊤_ Scheme.{u}) hZ hZ hWalg
        hWqs' _⟩
  -- Stacks 07SK: a model `W₀ ⟶ U₀` of finite presentation
  obtain ⟨i₀, Y₀, hY₀alg, hY₀fp, ⟨φ⟩⟩ :=
    exists_model_of_finitePresentation_of_siteContainsBaseChangeLimits B (⊤_ Scheme.{u}) hZ hZ
      D hD hAff hDqc hDqs hconv hlimAlg (Over.mk (gW ≫ e.hom)) hWalg hFp
  let a : yoneda.obj W ⟶ Y₀.left := φ.hom.left ≫ pullback.fst Y₀.hom (limit.π D i₀)
  have hsq : IsPullback a (gW ≫ e.hom) Y₀.hom (limit.π D i₀) := by
    refine (IsPullback.of_hasPullback Y₀.hom (limit.π D i₀)).of_iso
      ((Over.forget _).mapIso φ).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [a]
    · have := Over.w φ.inv
      simp only [Over.mk_hom, Over.pullback_obj_hom] at this
      simp [this]
    · simp
    · simp
  have hsq' : IsPullback a gW Y₀.hom (uπ.app i₀) := by
    refine hsq.of_iso (Iso.refl _) (Iso.refl _) e.symm (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp
    · simp [← he]
  have hY₀qc : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ Y₀.left :=
    isQuasiCompactSpace_source_of_isQuasiCompact B (⊤_ Scheme.{u}) hZ (hD i₀) (hDqc i₀)
      hY₀fp.2.1
  have hY₀qs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ Y₀.left :=
    isAbsolutelyQuasiSeparated_of_isFinitePresentation B (⊤_ Scheme.{u}) hZ hZ hY₀alg (hDqs i₀)
      hY₀fp
  -- the situation of Stacks 084W for `W₀ ⟶ U₀` over the system `D`
  let M : MorphismDescentSituation B (⊤_ Scheme.{u}) hZ hZ I :=
    { base := D
      base_isAlgebraicSpace := fun j => hD _
      transition_affine := hAff
      limit_isAlgebraicSpace := hlimAlg
      initial := i₀.unop
      source₀ := Y₀.left
      target₀ := D.obj i₀
      sourceToBase := Y₀.hom
      targetToBase := 𝟙 _
      map₀ := Y₀.hom
      map₀_over := Category.comp_id _
      source₀_isAlgebraicSpace := hY₀alg
      target₀_isAlgebraicSpace := hD i₀
      base₀_quasiCompact := hDqc i₀
      base₀_quasiSeparated := hDqs i₀
      source₀_quasiCompact := hY₀qc
      source₀_quasiSeparated := hY₀qs
      target₀_quasiCompact := hDqc i₀
      target₀_quasiSeparated := hDqs i₀ }
  -- its base change to the limit is `W ⟶ U`, which is étale
  have hEtLim : IsEtale B (⊤_ Scheme.{u}) hZ M.mapLimit := by
    have hfstEt : IsEtale B (⊤_ Scheme.{u}) hZ (pullback.fst (limit.π D i₀) Y₀.hom) := by
      rw [← hsq.flip.isoPullback_inv_fst]
      exact isEtale_comp B (⊤_ Scheme.{u}) hZ
        (isEtale_of_iso B (⊤_ Scheme.{u}) hZ hsq.flip.isoPullback.symm) hEt
    have _ : IsIso M.targetToBase := (inferInstance : IsIso (𝟙 (D.obj i₀)))
    have _ : IsIso (pullback.fst (limit.π M.base (op M.initial)) M.targetToBase) :=
      (IsPullback.of_hasPullback _ _).isIso_fst_of_isIso
    have hfst : M.mapLimit = pullback.fst (limit.π M.base (op M.initial)) M.sourceToBase ≫
        inv (pullback.fst (limit.π M.base (op M.initial)) M.targetToBase) :=
      (IsIso.eq_comp_inv
        (pullback.fst (limit.π M.base (op M.initial)) M.targetToBase)).2 M.mapLimit_fst
    rw [hfst]
    exact isEtale_comp B (⊤_ Scheme.{u}) hZ hfstEt (isEtale_of_iso B (⊤_ Scheme.{u}) hZ
      (asIso (inv (pullback.fst (limit.π M.base (op M.initial)) M.targetToBase))))
  -- Stacks 07SL: the base change to some stage is étale
  obtain ⟨i₁, hi₁, hEt₁⟩ :=
    M.exists_isEtale_mapAt_of_siteContainsBaseChangeLimits hconv hEtLim hY₀fp.1
  -- Stacks 07SR: some base change `W_i` is a scheme
  let DS := M.stagesBaseChangeDescentSituation Y₀.hom hY₀alg hY₀qc hY₀qs
  have hX : DS.limitCone.pt.IsRepresentable :=
    isRepresentable_of_natIso (yoneda.obj W) hsq.flip.isoPullback
  obtain ⟨j₂, hj₂⟩ := DS.exists_isRepresentable_system_obj_of_siteContainsBaseChangeLimits
    (M.siteContainsBaseChangeLimits_stagesBaseChangeSystem hconv Y₀.hom) hX
  obtain ⟨k, hk₁, hk₂⟩ := directed_of (· ≤ ·) i₁ j₂.1
  have hik : i₀.unop ≤ k := hi₁.trans hk₁
  -- the system `W_i = W₀ ×_{U₀} U_i` over the indices beyond `k`
  let G := (Subtype.mono_coe fun i => k ≤ i).functor.op ⋙ D
  let t : G ⟶ (Functor.const (LimitTail I k)ᵒᵖ).obj (D.obj i₀) :=
    { app := fun j => D.map (homOfLE (hik.trans j.unop.2)).op
      naturality := fun j j' f => by
        simp only [G, Functor.comp_map, Functor.const_obj_map, ← D.map_comp]
        rfl }
  let E := baseChangeOverSystem B (⊤_ Scheme.{u}) hZ G t Y₀.hom
  let p := baseChangeOverProj B (⊤_ Scheme.{u}) hZ G t Y₀.hom
  have hpb : ∀ {j j' : (LimitTail I k)ᵒᵖ} (f : j ⟶ j'), IsPullback (E.map f) (p.app j)
      (p.app j') (G.map f) := fun {j j'} f =>
    isPullback_baseChangeOverMap B (⊤_ Scheme.{u}) hZ (t.app j) (t.app j') (G.map f)
      ((t.naturality f).trans (Category.comp_id _)) Y₀.hom
  have hrep : ∀ j, (E.obj j).IsRepresentable := by
    intro j
    have _ : (pullback (M.baseAtToInitial j₂.1 j₂.2) Y₀.hom).IsRepresentable := hj₂
    have hcomm : D.map (homOfLE (hk₂.trans j.unop.2)).op ≫ M.baseAtToInitial j₂.1 j₂.2 =
        t.app j := by
      show D.map _ ≫ D.map _ = D.map _
      rw [← D.map_comp]
      rfl
    let f := baseChangeOverMap B (⊤_ Scheme.{u}) hZ (t.app j) (M.baseAtToInitial j₂.1 j₂.2)
      _ hcomm Y₀.hom
    exact isRepresentable_of_isAffineHom B (⊤_ Scheme.{u}) hZ f
      (isAlgebraicSpace_pullback B (⊤_ Scheme.{u}) hZ _ _ (hD _) hY₀alg (hD _))
      (isAlgebraicSpace_pullback B (⊤_ Scheme.{u}) hZ _ _ (hD _) hY₀alg (hD _))
      (IsAffineHom.of_isPullback (isPullback_baseChangeOverMap B (⊤_ Scheme.{u}) hZ _ _ _
        hcomm Y₀.hom).flip (hAff _))
  have hEqc : ∀ j, IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ (E.obj j) := fun j =>
    isQuasiCompactSpace_pullback B (⊤_ Scheme.{u}) hZ hZ (t.app j) Y₀.hom (hD _) (hD _)
      (hDqc _) hY₀qc (hDqs _)
  have hEet : ∀ j, IsEtale B (⊤_ Scheme.{u}) hZ (p.app j) := by
    intro j
    have h := M.isEtale_mapAt_of_le hi₁ (hk₁.trans j.unop.2) hEt₁
    have hfst := M.mapAt_fst j.unop.1 (hi₁.trans (hk₁.trans j.unop.2))
    show IsEtale B (⊤_ Scheme.{u}) hZ (pullback.fst (t.app j) Y₀.hom)
    change _ ≫ pullback.fst (t.app j) (𝟙 (D.obj i₀)) = pullback.fst (t.app j) Y₀.hom at hfst
    have _ : IsIso (𝟙 (D.obj i₀)) := inferInstance
    have _ : IsIso (pullback.fst (t.app j) (𝟙 (D.obj i₀))) :=
      (IsPullback.of_hasPullback _ _).isIso_fst_of_isIso
    rw [← hfst]
    exact isEtale_comp B (⊤_ Scheme.{u}) hZ h
      (isEtale_of_iso B (⊤_ Scheme.{u}) hZ (asIso (pullback.fst (t.app j) (𝟙 (D.obj i₀)))))
  -- the limit of the `W_i` is `W`
  have _ : Nonempty (LimitTail I k) := ⟨⟨k, le_rfl⟩⟩
  have _ : ((Subtype.mono_coe fun i => k ≤ i).functor).Final := by
    refine (Monotone.final_functor_iff (Subtype.mono_coe fun i => k ≤ i)).2 fun l => ?_
    obtain ⟨m, h₀, hl⟩ := exists_ge_ge k l
    exact ⟨⟨m, h₀⟩, hl⟩
  have hcG : IsLimit ((Cone.mk Y uπ).whisker (Subtype.mono_coe fun i => k ≤ i).functor.op) :=
    (Functor.Initial.isLimitWhiskerEquiv _ _).symm huπ
  have hg : ∀ j, ((Cone.mk Y uπ).whisker (Subtype.mono_coe fun i => k ≤ i).functor.op).π.app j ≫
      t.app j = uπ.app i₀ := fun j => by
    simpa using (uπ.naturality (homOfLE (hik.trans j.unop.2)).op).symm
  let bc := baseChangeOverCone B (⊤_ Scheme.{u}) hZ G t Y₀.hom
    ((Cone.mk Y uπ).whisker (Subtype.mono_coe fun i => k ≤ i).functor.op) (uπ.app i₀) hg
  have hbc : IsLimit bc := isLimit_baseChangeOverCone B (⊤_ Scheme.{u}) hZ G t Y₀.hom _ _ hg hcG
  have hc : IsLimit (bc.extend hsq'.flip.isoPullback.hom) :=
    hbc.ofIsoLimit (Cone.extendIso bc hsq'.flip.isoPullback.symm)
  have hcart : ∀ j, IsPullback ((bc.extend hsq'.flip.isoPullback.hom).π.app j) gW (p.app j)
      (uπ.app (op j.unop.1)) := fun j => by
    have h := isPullback_baseChangeOverMap B (⊤_ Scheme.{u}) hZ (uπ.app i₀) (t.app j)
      (((Cone.mk Y uπ).whisker (Subtype.mono_coe fun i => k ≤ i).functor.op).π.app j) (hg j)
      Y₀.hom
    refine h.of_iso hsq'.flip.isoPullback.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · exact (Category.comp_id _).trans
        (Iso.inv_hom_id_assoc hsq'.flip.isoPullback (bc.π.app j)).symm
    · simp
    · exact (Category.comp_id _).trans (Category.id_comp (p.app j)).symm
    · simp
  obtain ⟨Ws, g, wπ, h₁, h₂, h₃, h₄, h₅, h₆, h₈, h₇⟩ :=
    exists_etaleSchemeSystem_of_stages D hconv hD hAff hDft uπ W gW k E p hpb hrep hEqc hEet
      (bc.extend hsq'.flip.isoPullback.hom).π hc (fun j => by
        show (hsq'.flip.isoPullback.hom ≫ baseChangeOverMap B (⊤_ Scheme.{u}) hZ _ _ _ (hg j)
          Y₀.hom) ≫ pullback.fst (t.app j) Y₀.hom = _
        rw [Category.assoc, baseChangeOverMap_fst, ← Category.assoc,
          IsPullback.isoPullback_hom_fst]
        rfl) hcart
  exact ⟨k, Ws, g, wπ, h₁, h₂, h₃, h₄, h₅, h₆, h₈, h₇⟩

end AlgebraicGeometry.Space

end
