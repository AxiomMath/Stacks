module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.Factorization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LiftAlongAffineStages
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableEtaleCancellationGeneral
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpacesEtaleIdentification
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.ActionQuotientFieldPoints
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpacesEtaleIdentificationSupplement
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DependentProduct.Basic
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DependentProduct.BaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DependentProduct.Universal

/-!
# The dependent product over an affine formal algebraic space, and Stacks 0DEG

Let `S` be a scheme contained in a big fppf site `B`. This file proves the one assertion of
Stacks 0DEG that was left standing: the dependent product `U_{V, ψ}` along a representable
thickening `i : I ⟶ X` of an *affine* formal algebraic space `X` is a formal algebraic space.
With the reduction to an affine étale chart of the base, which is
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_liftAlong_of_affine`, that settles the
assertion for an arbitrary formal algebraic space, hence the essential surjectivity of the
comparison functor of Stacks 0DEG, hence Stacks 0DEG itself.

## Main results

* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_liftAlong_of_isAffineFormalAlgebraicSpace`:
  the affine case, which is what the source settles by the proof of Stacks 0DEE.
* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_liftAlong`: the assertion for an
  arbitrary formal algebraic space.
* `AlgebraicGeometry.FormalSpace.essSurj_spacesEtaleComparison`: essential surjectivity of the
  comparison functor.
* `AlgebraicGeometry.FormalSpace.spacesEtaleComparison_isEquivalence`: **Stacks 0DEG**, the
  equivalence `X_{spaces, étale} ≃ C`, with nothing assumed.

## Implementation notes

**The atlas.** Write `X = colim_ν X_ν` for a presentation of the affine formal algebraic space
`X` by affine objects of the site along thickenings, and let `T_ν = X_ν ×_X I` be the
corresponding stage of `I`, an affine object of the site thickened by `X_ν`. The base change
`W ×_I T_ν` is an algebraic space étale over `T_ν`, so it has a family of affine étale charts
`A_{ν, m} ⟶ T_ν`; the atlas of `U_{W, p}` is the family of dependent products

`U_{ν, m} = U_{C_{ν, m}, c_{ν, m}}`,  `C_{ν, m} = U_{A_{ν, m}, a_{ν, m}}` along `T_ν ⟶ I`,

where `c_{ν, m} : C_{ν, m} ⟶ W` is the unique extension of `A_{ν, m} ⟶ W` along the
representable thickening `A_{ν, m} ⟶ C_{ν, m}`, which
`AlgebraicGeometry.FormalSpace.existsUnique_hom_of_isRepresentableThickening` provides. Each
`U_{ν, m} ⟶ U_{W, p}` is representable by algebraic spaces and étale by
`AlgebraicGeometry.FormalSpace.isRepresentableEtale_liftAlongMap`, whose hypothesis is
discharged by étale cancellation,
`AlgebraicGeometry.FormalSpace.isRepresentableEtale_of_comp'`.

**Why each member is an affine formal algebraic space.** The base change of `U_{ν, m}` to a
stage `X_μ` is computed in two steps by
`AlgebraicGeometry.FormalSpace.exists_affine_etale_iso_pullback_liftAlongBase`: down to the
stage `T_μ` of `I` it is the dependent product, along the thickening `T_ν ×_I T_μ ⟶ T_μ` of
objects of the site, of the affine chart `A_{ν, m} ×_{T_ν} (T_ν ×_I T_μ)`, hence affine; and
down to `X_μ` it is the dependent product, along `T_μ ⟶ X_μ`, of that affine object, hence
again affine. Note that *every* stage `X_μ` is reached, not only those above `X_ν`: the fibre
product `T_ν ×_I T_μ` is a closed subscheme of the affine `T_μ`, so it is affine whatever `μ`
is. Stacks 0GVM then makes `U_{ν, m}` an affine formal algebraic space, and the set-theoretic
condition of Stacks 0AIS it needs descends from `X` along the representable structure morphism.

**Why the atlas is jointly surjective.** A section of `U_{W, p}` over an object `N` of the site
is a pair `(a, b)` with `a : N ⟶ X` and `b : N ×_{a, X} I ⟶ W`. Refining `N` by affines, the
quasi-compact point `a` factors through a single stage `X_{ν₀}` by Stacks 0AIA, so `N ×_X I` is
an affine object `N₀` of the site thickened by `N` mapping to `T_{ν₀}`, and `b` makes `N₀` a
point of `W ×_I T_{ν₀}`. The affine étale cover of `N₀` refining the charts `A_{ν₀, m}` lifts
along the thickening `N₀ ⟶ N`, by Stacks 039R in the family form
`AlgebraicGeometry.FormalSpace.exists_affine_etale_cover_lift_of_isThickening`, to an affine
étale cover `{N_k ⟶ N}` surjective on points; and over each `N_k` the section lifts to
`U_{ν₀, m}`, because the lift is prescribed on the thickening `N_k ×_N N₀` and
`U_{ν₀, m} ⟶ U_{W, p}` is representable by algebraic spaces and étale, so the prescription
extends uniquely. A jointly surjective étale family generates a covering sieve, which is what
`CategoryTheory.Sheaf.isLocallySurjective_sigmaDesc_iff` asks for.

## References

* [Stacks Project, Tag 039R](https://stacks.math.columbia.edu/tag/039R)
* [Stacks Project, Tag 0AIA](https://stacks.math.columbia.edu/tag/0AIA)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AJ1](https://stacks.math.columbia.edu/tag/0AJ1)
* [Stacks Project, Tag 0DEE](https://stacks.math.columbia.edu/tag/0DEE)
* [Stacks Project, Tag 0DEG](https://stacks.math.columbia.edu/tag/0DEG)
* [Stacks Project, Tag 0GVM](https://stacks.math.columbia.edu/tag/0GVM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

open AlgebraicGeometry.FormalSpace.DependentProduct

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] sheaf_hasColimits

/-- A representable thickening of sheaves is injective on sections over every object. -/
private theorem injective_app_of_isRepresentableThickeningULift' {X I : FppfSheaf B S hS}
    {i : I ⟶ X} (hi : Space.IsRepresentableThickeningULift.{u + 1} B S hS i.hom)
    (T : BigFppfOver B S hS) : Function.Injective (i.hom.app (Opposite.op T)) :=
  (mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1
    (mono_of_isRepresentableThickeningULift B S hS hi) (Opposite.op T))

/-- An object of the site thickened by an affine object is affine. -/
private theorem isAffine_toScheme_obj_of_isThickening {T₀ T : BigFppfOver B S hS} (k : T₀ ⟶ T)
    (hk : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map k))
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj T₀) := by
  have _ : _root_.AlgebraicGeometry.IsClosedImmersion
    ((BigFppfOver.toScheme B S hS).map k) := hk.1
  exact isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map k)

/-- **Stacks 0DEG.** The dependent product `U_{V, ψ}` along a representable thickening of an
*affine* formal algebraic space is a formal algebraic space. -/
theorem isFormalAlgebraicSpace_liftAlong_of_isAffineFormalAlgebraicSpace
    {Y I' W' : FppfSheaf B S hS} (i' : I' ⟶ Y) (p' : W' ⟶ I')
    (hY : IsAffineFormalAlgebraicSpace B S hS Y)
    (hi' : Space.IsRepresentableThickeningULift.{u + 1} B S hS i'.hom)
    (hp' : IsRepresentableEtale B S hS p') :
    IsFormalAlgebraicSpace B S hS (liftAlong B S hS i' p') := by
  classical
  obtain ⟨hYset, Λ, pre, hne, hdir, D, hDthick, ⟨eY⟩⟩ := hY
  have eY' : Y ≅ colimit (presentationDiagram D) := eY
  let _ : Preorder Λ := pre
  let _ : Nonempty Λ := hne
  let _ : IsDirected Λ (· ≤ ·) := hdir
  have hYaff : IsAffineFormalAlgebraicSpace B S hS Y :=
    ⟨hYset, Λ, pre, hne, hdir, D, hDthick, ⟨eY⟩⟩
  have hinj := injective_app_of_isRepresentableThickeningULift' hi'
  -- the stages of the presentation of `Y`, as objects of the site
  set Ys : Λ → BigFppfOver B S hS := fun ν ↦ (BigAffineFppf.inclusion B S hS).obj (D.obj ν)
    with hYsdef
  have hYsaff : ∀ ν, IsAffine ((BigFppfOver.toScheme B S hS).obj (Ys ν)) := fun ν ↦
    BigAffineFppf.isAffine_toScheme_obj B S hS (D.obj ν)
  have εs : ∀ ν : Λ, liftSheaf B S hS (schemeSpace (Ys ν))
      ≅ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (Ys ν) := fun ν ↦
    liftSheafYonedaSpaceIsoSheafifiedYoneda B S hS (Ys ν)
  set σ : ∀ ν, liftSheaf B S hS (schemeSpace (Ys ν)) ⟶ Y := fun ν ↦
    (εs ν).hom ≫ colimit.ι (presentationDiagram D) ν ≫ eY'.inv with hσdef
  have hσapp : ∀ ν, σ ν
      = (εs ν).hom ≫ colimit.ι (presentationDiagram D) ν ≫ eY'.inv := fun ν ↦ rfl
  have hσthick : ∀ ν, Space.IsRepresentableThickeningULift.{u + 1} B S hS (σ ν).hom := by
    intro ν
    have _ : ((MorphismProperty.inverseImage
        (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).relative
          (uliftYoneda.{u + 1} (C := BigFppfOver B S hS))).RespectsIso :=
      (MorphismProperty.relative_isStableUnderBaseChange _).respectsIso
    have _ : IsIso ((εs ν).hom.hom) :=
      inferInstanceAs (IsIso ((sheafToPresheaf (BigFppfOver.topology B S hS)
        (Type (u + 1))).map (εs ν).hom))
    exact MorphismProperty.RespectsIso.precomp _ (εs ν).hom.hom _
      ((relative_sheafifiedYoneda_iff_uliftYoneda' B S hS _
        (colimit.ι (presentationDiagram D) ν ≫ eY'.inv)).mp
        (isThickening_colimitι B S hS D hDthick Y eY'.symm ν))
  -- the stage of `I'` over each stage of `Y`
  choose Ts kk jj hkkthick hTsq using
    fun ν ↦ exists_isPullback_point_of_isRepresentableThickening hi' (σ ν)
  have hTsaff : ∀ ν, IsAffine ((BigFppfOver.toScheme B S hS).obj (Ts ν)) := fun ν ↦
    isAffine_toScheme_obj_of_isThickening (kk ν) (hkkthick ν) (hYsaff ν)
  have hjjthick : ∀ ν, Space.IsRepresentableThickeningULift.{u + 1} B S hS (jj ν).hom :=
    fun ν ↦ (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      ((hTsq ν).map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))))
      (hσthick ν)
  have hjjinj := fun ν ↦ injective_app_of_isRepresentableThickeningULift' (hjjthick ν)
  -- the affine étale charts of the base change of `p'` to each stage of `I'`
  choose Mc Ac ac wc hAcaff hacet hwcf hccov using
    fun ν ↦ exists_affine_etale_charts_of_isRepresentableEtale
      (isRepresentableEtale_pullback_snd B S hS p' (jj ν) hp')
  have hacrep : ∀ (ν : Λ) (m : Mc ν), IsRepresentableEtale B S hS
      (liftSheafMap B S hS (schemeSpaceMap (ac ν m))) := fun ν m ↦
    isRepresentableEtale_liftSheafMap B S hS (schemeSpaceMap (ac ν m))
      ((Space.isEtale_iff_presheaf_of_yoneda B S hS (yoneda.map (ac ν m))).2
        ((Space.presheaf_yoneda_map_etale_iff B S hS (ac ν m)).2 (hacet ν m)))
  -- the dependent products of the charts over the stage, and their structure morphisms
  set pc : ∀ n : Σ ν : Λ, Mc ν,
      liftAlong B S hS (jj n.1) (liftSheafMap B S hS (schemeSpaceMap (ac n.1 n.2))) ⟶ I' :=
    fun n ↦ liftAlongBase B S hS (jj n.1)
      (liftSheafMap B S hS (schemeSpaceMap (ac n.1 n.2))) with hpcdef
  have hpcapp : ∀ n : Σ ν : Λ, Mc ν, pc n = liftAlongBase B S hS (jj n.1)
      (liftSheafMap B S hS (schemeSpaceMap (ac n.1 n.2))) := fun n ↦ rfl
  have hpcet : ∀ n, IsRepresentableEtale B S hS (pc n) := fun n ↦
    isRepresentableEtale_liftAlongBase B S hS (hjjthick n.1) (hacrep n.1 n.2)
  -- the comparison `A ⟶ C` is a representable thickening, being a base change of the stage
  have hCsecthick : ∀ n : Σ ν : Λ, Mc ν, Space.IsRepresentableThickeningULift.{u + 1} B S hS
      (liftAlongSection B S hS (hjjinj n.1)
        (p := liftSheafMap B S hS (schemeSpaceMap (ac n.1 n.2)))).hom := fun n ↦
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      ((isPullback_liftAlongSection B S hS (hjjinj n.1)
        (p := liftSheafMap B S hS (schemeSpaceMap (ac n.1 n.2)))).flip.map
        (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))))
      (hjjthick n.1)
  -- the morphism `A ⟶ W'` the chart carries, and its unique extension to `C`
  set ŵ : ∀ n : Σ ν : Λ, Mc ν,
      liftSheaf B S hS (schemeSpace (Ac n.1 n.2)) ⟶ W' := fun n ↦
    wc n.1 n.2 ≫ pullback.fst p' (jj n.1) with hŵdef
  have hŵapp : ∀ n : Σ ν : Λ, Mc ν, ŵ n = wc n.1 n.2 ≫ pullback.fst p' (jj n.1) :=
    fun n ↦ rfl
  have hŵcond : ∀ n : Σ ν : Λ, Mc ν, ŵ n ≫ p'
      = liftAlongSection B S hS (hjjinj n.1)
          (p := liftSheafMap B S hS (schemeSpaceMap (ac n.1 n.2))) ≫ pc n := by
    intro n
    rw [hŵapp, hpcapp, Category.assoc, pullback.condition, ← Category.assoc,
      hwcf n.1 n.2, liftAlongSection_comp_liftAlongBase]
  choose cf hcf₁ hcf₂ using fun n : Σ ν : Λ, Mc ν ↦
    (existsUnique_hom_of_isRepresentableThickening (hCsecthick n) hp' (pc n)
      (hŵcond n)).exists
  have hcfet : ∀ n, IsRepresentableEtale B S hS (cf n) := fun n ↦
    isRepresentableEtale_of_comp' B S hS (cf n) p' hp' (by rw [hcf₁ n]; exact hpcet n)
  -- the atlas
  refine isFormalAlgebraicSpace_of_etaleCover B S hS (liftAlong B S hS i' p')
    (fun n ↦ liftAlong B S hS i' (pc n))
    (fun n ↦ liftAlongMap B S hS i' (cf n) (hcf₁ n)) (fun n ↦ ?_)
    (fun n ↦ isRepresentableEtale_liftAlongMap B S hS (cf n) (hcf₁ n) hi' (hcfet n)) ?_
    (SetTheoreticDescent.satisfiesSetTheoreticCondition_of_representable_over B S hS
      (liftAlongBase B S hS i' p')
      (isRepresentableEtale_liftAlongBase B S hS hi' hp').1 hYset)
  · -- each member of the atlas is an affine formal algebraic space
    refine isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS
      (isAffineFormalAlgebraicSpace_of_affine_stages D hDthick eY' hYset
        (liftAlongBase B S hS i' (pc n))
        (isRepresentableEtale_liftAlongBase B S hS hi' (hpcet n)).1 fun ν ↦ ?_)
    -- the stage of the base change: two nested applications of the stage computation
    obtain ⟨P, κ, gg, hκ, hPsq⟩ :=
      exists_isPullback_point_of_isRepresentableThickening (hjjthick n.1) (jj ν)
    obtain ⟨π, hπ⟩ := exists_liftSheafMap_schemeSpaceMap_eq gg
    subst hπ
    have hPaff := isAffine_toScheme_obj_of_isThickening κ hκ (hTsaff ν)
    have hsqA := (IsPullback.of_hasPullback (ac n.1 n.2) π).map (BigFppfOver.toScheme B S hS)
    have hQaff : IsAffine ((BigFppfOver.toScheme B S hS).obj
        (Limits.pullback (ac n.1 n.2) π)) := by
      have _ := hAcaff n.1 n.2
      have _ := hPaff
      have _ := hTsaff n.1
      have _ : IsAffine (Limits.pullback
          ((BigFppfOver.toScheme B S hS).map (ac n.1 n.2))
          ((BigFppfOver.toScheme B S hS).map π)) := inferInstance
      exact IsAffine.of_isIso hsqA.isoPullback.hom
    have hQet : Etale ((BigFppfOver.toScheme B S hS).map
        (Limits.pullback.snd (ac n.1 n.2) π)) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback hsqA (hacet n.1 n.2)
    obtain ⟨ε₀, hε₀⟩ := exists_iso_pullback_liftSheafMap (ac n.1 n.2) π
    obtain ⟨V, q, hVaff, hq, e₁, he₁⟩ :=
      exists_affine_etale_iso_pullback_liftAlongBase hκ hPsq _ hQaff _ hQet ε₀ hε₀
    obtain ⟨V', q', hV'aff, hq', e₂, -⟩ :=
      exists_affine_etale_iso_pullback_liftAlongBase (hkkthick ν) (hTsq ν) V hVaff q hq
        e₁ he₁
    have hsw : IsPullback
        (pullback.snd (liftAlongBase B S hS i' (pc n)) (σ ν) ≫ (εs ν).hom)
        (pullback.fst (liftAlongBase B S hS i' (pc n)) (σ ν))
        (colimit.ι (presentationDiagram D) ν)
        (liftAlongBase B S hS i' (pc n) ≫ eY'.hom) := by
      refine (IsPullback.of_hasPullback (liftAlongBase B S hS i' (pc n)) (σ ν)).flip.of_iso
        (Iso.refl _) (εs ν) (Iso.refl _) eY'
        (by simp) (by simp) ?_ (by simp)
      change σ ν ≫ eY'.hom = (εs ν).hom ≫ colimit.ι (presentationDiagram D) ν
      rw [hσapp, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact ⟨V', hV'aff, ⟨e₂ ≪≫ hsw.isoIsPullback _ _ (IsPullback.of_hasPullback _ _)⟩⟩
  · -- joint surjectivity
    refine (Sheaf.isLocallySurjective_sigmaDesc_iff _).2 ?_
    intro Nobj s
    set R : Sieve Nobj :=
      { arrows := fun V g ↦ ∃ (n : Σ ν : Λ, Mc ν)
            (t : (liftAlong B S hS i' (pc n)).obj.obj (Opposite.op V)),
            (liftAlongMap B S hS i' (cf n) (hcf₁ n)).hom.app (Opposite.op V) t
              = (liftAlong B S hS i' p').obj.map g.op s
        downward_closed := by
          rintro V V' g ⟨n, t, ht⟩ h
          refine ⟨n, (liftAlong B S hS i' (pc n)).obj.map h.op t, ?_⟩
          rw [app_map_op B S hS (liftAlongMap B S hS i' (cf n) (hcf₁ n)) h t, ht]
          exact (LiftAlong.map_comp_op_apply (liftAlong B S hS i' p').obj g h s).symm }
      with hRdef
    refine ⟨R, ?_, fun V g hg ↦ hg⟩
    obtain ⟨K₀, V₀, π₀, hV₀aff, hπ₀open, hπ₀sieve, -⟩ :=
      BigFppfOver.exists_affine_open_cover' B S hS Nobj
    have key : ∀ (V : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
        ∀ g : V ⟶ Nobj, R.pullback g ∈ BigFppfOver.topology B S hS V := by
      intro V hVaff g
      have _ := hVaff
      -- the section over `V`, read as a morphism of sheaves
      set ŝ : liftSheaf B S hS (schemeSpace V) ⟶ liftAlong B S hS i' p' :=
        ⟨uliftYonedaEquiv.{u + 1}.symm ((liftAlong B S hS i' p').obj.map g.op s)⟩ with hŝdef
      set â : liftSheaf B S hS (schemeSpace V) ⟶ Y := ŝ ≫ liftAlongBase B S hS i' p' with hâdef
      -- the point of `Y` factors through a stage, `V` being quasi-compact
      have εV : liftSheaf B S hS (schemeSpace V)
          ≅ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V :=
        liftSheafYonedaSpaceIsoSheafifiedYoneda B S hS V
      obtain ⟨ν₀, gg₀, hgg₀⟩ := exists_factor_through_thickening' B S hS Λ D
        (fun _ _ g ↦ (hDthick g).1) Y eY'
        (yoneda.obj V)
        (Space.isQuasiCompactSpace_yoneda_obj B S hS (U := V) inferInstance)
        (εV.inv ≫ â)
      obtain ⟨gg, hgg⟩ :
          ∃ gg : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V
            ⟶ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (Ys ν₀),
            gg ≫ colimit.ι (presentationDiagram D) ν₀ ≫ eY'.inv = εV.inv ≫ â :=
        ⟨gg₀, hgg₀⟩
      obtain ⟨v₀, hv₀⟩ := exists_liftSheafMap_schemeSpaceMap_eq
        (εV.hom ≫ gg ≫ (εs ν₀).inv)
      have hv₀σ : liftSheafMap B S hS (schemeSpaceMap v₀) ≫ σ ν₀ = â := by
        rw [hv₀, hσapp, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, hgg,
          Iso.hom_inv_id_assoc]
      -- the thickening `V ×_Y I' ⟶ V`
      obtain ⟨V₁, κ, γ, hκ, hV₁sq⟩ :=
        exists_isPullback_point_of_isRepresentableThickening hi' â
      -- the morphism `V ×_Y I' ⟶ W'` the section carries
      have hsecsq := isPullback_liftAlongSection B S hS hinj (i := i') (p := p')
      have hbw : (liftSheafMap B S hS (schemeSpaceMap κ) ≫ ŝ) ≫ liftAlongBase B S hS i' p'
          = γ ≫ i' := by rw [Category.assoc]; exact hV₁sq.w
      set b : liftSheaf B S hS (schemeSpace V₁) ⟶ W' :=
        hsecsq.lift (liftSheafMap B S hS (schemeSpaceMap κ) ≫ ŝ) γ hbw with hbdef
      have hb₁ : b ≫ liftAlongSection B S hS hinj
          = liftSheafMap B S hS (schemeSpaceMap κ) ≫ ŝ := hsecsq.lift_fst _ _ _
      have hb₂ : b ≫ p' = γ := hsecsq.lift_snd _ _ _
      -- the morphism `V ×_Y I' ⟶ T_{ν₀}` to the stage of `I'`
      have hδw : (liftSheafMap B S hS (schemeSpaceMap κ) ≫
          liftSheafMap B S hS (schemeSpaceMap v₀)) ≫ σ ν₀ = γ ≫ i' := by
        rw [Category.assoc, hv₀σ]; exact hV₁sq.w
      set δ : liftSheaf B S hS (schemeSpace V₁) ⟶ liftSheaf B S hS (schemeSpace (Ts ν₀)) :=
        (hTsq ν₀).lift (liftSheafMap B S hS (schemeSpaceMap κ) ≫
          liftSheafMap B S hS (schemeSpaceMap v₀)) γ hδw with hδdef
      have hδ₂ : δ ≫ jj ν₀ = γ := (hTsq ν₀).lift_snd _ _ _
      -- the point of the base change of `p'` to the stage
      set zz : liftSheaf B S hS (schemeSpace V₁) ⟶ pullback p' (jj ν₀) :=
        pullback.lift b δ (by rw [hb₂, hδ₂]) with hzzdef
      have hz₁ : zz ≫ pullback.fst p' (jj ν₀) = b := pullback.lift_fst _ _ _
      -- the affine étale cover of `V ×_Y I'` refining the charts
      obtain ⟨K, E, πE, mE, tE, hEaff, hπEet, hπEcov, hEcompat⟩ := hccov ν₀ V₁ zz
      -- lift that cover along the thickening `V ×_Y I' ⟶ V`
      obtain ⟨F, qF, hqFet, hFaff, hFpb, hFcov⟩ :=
        exists_affine_etale_cover_lift_of_isThickening B S hS κ hκ E hEaff
          (fun n ↦ (BigFppfOver.toScheme B S hS).map (πE n)) hπEet hπEcov
      choose bn hbn using fun n ↦ (hFpb n).elim fun e he ↦
        Space.exists_isPullback_of_iso_pullback_toScheme B S hS (qF n) κ (πE n) e he
      have hbnthick : ∀ n, Space.IsRepresentableThickeningULift.{u + 1} B S hS
          (liftSheafMap B S hS (schemeSpaceMap (bn n))).hom := fun n ↦
        (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
          ((hbn n).flip.map (uliftYoneda.{u + 1}))
          (MorphismProperty.relative_map hκ)
      -- on each member of the lifted cover the section lifts to the atlas
      have hlift : ∀ n, ∃ θ : liftSheaf B S hS (schemeSpace (F n))
            ⟶ liftAlong B S hS i' (pc ⟨ν₀, mE n⟩),
          θ ≫ liftAlongMap B S hS i' (cf ⟨ν₀, mE n⟩) (hcf₁ ⟨ν₀, mE n⟩)
            = liftSheafMap B S hS (schemeSpaceMap (qF n)) ≫ ŝ := by
        intro n
        refine ((existsUnique_hom_of_isRepresentableThickening (hbnthick n)
          (isRepresentableEtale_liftAlongMap B S hS (cf ⟨ν₀, mE n⟩) (hcf₁ ⟨ν₀, mE n⟩) hi'
            (hcfet ⟨ν₀, mE n⟩))
          (liftSheafMap B S hS (schemeSpaceMap (qF n)) ≫ ŝ)
          (h := liftSheafMap B S hS (schemeSpaceMap (tE n)) ≫
            liftAlongSection B S hS (hjjinj ν₀)
              (p := liftSheafMap B S hS (schemeSpaceMap (ac ν₀ (mE n)))) ≫
            liftAlongSection B S hS hinj (p := pc ⟨ν₀, mE n⟩)) ?_).exists.imp
          fun θ hθ ↦ hθ.1)
        -- the two routes from the chart to `U_{W', p'}` agree
        have hcompat : liftSheafMap B S hS (schemeSpaceMap (tE n)) ≫ ŵ ⟨ν₀, mE n⟩
            = liftSheafMap B S hS (schemeSpaceMap (πE n)) ≫ b := by
          rw [hŵapp, ← Category.assoc, hEcompat n, Category.assoc, hz₁]
        have hpb : liftSheafMap B S hS (schemeSpaceMap (bn n))
              ≫ liftSheafMap B S hS (schemeSpaceMap (qF n))
            = liftSheafMap B S hS (schemeSpaceMap (πE n))
              ≫ liftSheafMap B S hS (schemeSpaceMap κ) := by
          rw [← liftSheafMap_schemeSpaceMap_comp, ← liftSheafMap_schemeSpaceMap_comp,
            (hbn n).w]
        simp only [Category.assoc]
        rw [liftAlongSection_comp_liftAlongMap hinj (cf ⟨ν₀, mE n⟩) (hcf₁ ⟨ν₀, mE n⟩),
          reassoc_of% (hcf₂ ⟨ν₀, mE n⟩), reassoc_of% hcompat, hb₁,
          reassoc_of% hpb]
      choose θ hθ using hlift
      -- the lifted cover generates a covering sieve contained in the pullback of `R`
      refine (BigFppfOver.topology B S hS).superset_covering ?_
        (Space.sieve_ofArrows_mem_topology_of_etale B hS F qF hFcov hqFet)
      rintro V' h ⟨W₁, l, ff, hff, rfl⟩
      obtain ⟨n⟩ := hff
      change R.arrows ((l ≫ qF n) ≫ g)
      rw [Category.assoc]
      refine R.downward_closed ⟨⟨ν₀, mE n⟩, uliftYonedaEquiv.{u + 1} (θ n).hom, ?_⟩ l
      have hcomp := congrArg (fun m : liftSheaf B S hS (schemeSpace (F n))
        ⟶ liftAlong B S hS i' p' ↦ uliftYonedaEquiv.{u + 1} m.hom) (hθ n)
      exact hcomp.trans
        (LiftAlong.map_comp_op_apply (liftAlong B S hS i' p').obj g (qF n) s).symm
    refine (BigFppfOver.topology B S hS).transitive hπ₀sieve R ?_
    rintro V' gg ⟨W₁, h, ff, hff, rfl⟩
    obtain ⟨k₀⟩ := hff
    rw [Sieve.pullback_comp]
    exact (BigFppfOver.topology B S hS).pullback_stable h
      (key (V₀ k₀) (hV₀aff k₀) (π₀ k₀))

/-! ### Stacks 0DEG, with nothing assumed -/

/-- **Stacks 0DEG.** The dependent product `U_{V, ψ}` along a representable thickening of a
formal algebraic space is a formal algebraic space.

This is the source's assertion in full: the reduction to an affine étale chart of the base is
`isFormalAlgebraicSpace_liftAlong_of_affine`, and the affine case is
`isFormalAlgebraicSpace_liftAlong_of_isAffineFormalAlgebraicSpace`. -/
theorem isFormalAlgebraicSpace_liftAlong {X I W : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X) {i : I ⟶ X} {p : W ⟶ I}
    (hirep : Space.IsRepresentableThickeningULift.{u + 1} B S hS i.hom)
    (hp : IsRepresentableEtale B S hS p) :
    IsFormalAlgebraicSpace B S hS (liftAlong B S hS i p) :=
  isFormalAlgebraicSpace_liftAlong_of_affine B S hS hX hirep hp
    fun _ _ _ i' p' hY hi' hp' ↦
      isFormalAlgebraicSpace_liftAlong_of_isAffineFormalAlgebraicSpace i' p' hY hi' hp'

/-- **Stacks 0DEG.** The comparison functor from the formal algebraic spaces representable
étale over a formal algebraic space `X` to `X_{spaces, étale}` is essentially surjective. -/
theorem essSurj_spacesEtaleComparison {X : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X) (R : Reduction B S hS X) :
    (spacesEtaleComparison hX R).EssSurj :=
  essSurj_spacesEtaleComparison_of_affine B S hS hX R
    fun _ _ _ i' p' hY hi' hp' ↦
      isFormalAlgebraicSpace_liftAlong_of_isAffineFormalAlgebraicSpace i' p' hY hi' hp'

/-- **Stacks 0DEG.** The comparison functor from the category of the formal algebraic spaces
representable étale over a formal algebraic space `X` to `X_{spaces, étale}` is an equivalence
of categories.

Full faithfulness is `AlgebraicGeometry.FormalSpace.bijective_spacesEtaleComparison_map` and
essential surjectivity is `AlgebraicGeometry.FormalSpace.essSurj_spacesEtaleComparison`. Every
assertion of the source is proved: the sheaf `U_{V, ψ}` the source produces is constructed, in
`StacksFrontier/AlgebraicGeometry/FormalSpace/SpacesEtaleQuasiInverse.lean`, its fibre product with
`X_red` over `X` is identified with `V`, the source's omitted verification that
`U_{V, ψ} ⟶ X` is representable by algebraic spaces and étale is proved, in
`StacksFrontier/AlgebraicGeometry/FormalSpace/SpacesEtaleQuasiInverseRepresentable.lean`, and that
`U_{V, ψ}` is a formal algebraic space is
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_liftAlong`.

The reduction of `X` is a parameter, not a weakening: `X_{spaces, étale}` is defined, in Stacks
0DEA, only for a formal algebraic space with a given reduction, and the datum exists for every
formal algebraic space by Stacks 0AIN. -/
@[stacks 0DEG "the equivalence; full faithfulness and essential surjectivity are both proved,
  the latter from the source's assertion that `U_{V, ψ}` is a formal algebraic space, which is
  AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_liftAlong"]
theorem spacesEtaleComparison_isEquivalence' {X : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X) (R : Reduction B S hS X) :
    (spacesEtaleComparison hX R).IsEquivalence where
  faithful := faithful_spacesEtaleComparison hX R
  full := full_spacesEtaleComparison hX R
  essSurj := essSurj_spacesEtaleComparison hX R

end AlgebraicGeometry.FormalSpace

end
