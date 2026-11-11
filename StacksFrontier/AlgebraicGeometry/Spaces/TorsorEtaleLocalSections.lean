module

public import StacksFrontier.AlgebraicGeometry.Descent.FlatCoproductRefinement
public import StacksFrontier.AlgebraicGeometry.Descent.FppfLocalOnBase.Smoothness
public import StacksFrontier.AlgebraicGeometry.Spaces.Coproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringRestrictionCoproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.EtaleLocalLifts

/-!
# Étale-local sections of torsors under smooth groups

Let `p : P ⟶ h_X` be a morphism from a sheaf on the big fppf site of `S` to the presheaf
represented by `X`, which has sections fppf locally on `X` and whose base change along every
`W ⟶ X` through which `p` has a section is `h_W × h_G`, for a smooth `G` over `S`. Then `p` has
sections étale locally on `X`.

## Main results

* `AlgebraicGeometry.BigFppfOver.exists_flat_section_of_mem_topology`: a morphism of sheaves to
  a represented presheaf with sections over the arrows of a covering sieve has a section over a
  single surjective, flat morphism locally of finite presentation.
* `AlgebraicGeometry.isAlgebraicSpace_of_isPullback_yoneda_prod`: a sheaf whose base change along
  a surjective, flat morphism locally of finite presentation of represented presheaves is
  `h_V × h_G` is an algebraic space.
* `AlgebraicGeometry.smooth_toScheme_map_of_isPullback_yoneda_prod`: an étale chart of such a
  sheaf is smooth over the base.
* `AlgebraicGeometry.exists_etale_section_of_isPullback_prod`: the étale-local sections.

## Implementation notes

The sheaf `P` is an algebraic space by the bootstrap theorem (Stacks 04S6, condition (3)), applied
to `h_V × h_G ⟶ P`, the base change of the single fppf covering `V ⟶ X`. The composite of an étale
atlas `h_Y ⟶ P` with `p` is a morphism of schemes `Y ⟶ X`; its base change along `V ⟶ X` is étale
over `V ×_S G`, hence smooth over `V`, and smoothness is fppf local on the target. An étale
neighbourhood of a point of `X` then lifts along the smooth morphism `Y ⟶ X` (Stacks 055U).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism `p : P ⟶ h_X` from a sheaf on the big fppf site of `S`, which has sections over the
arrows of a covering sieve of `X`, has a section over a single surjective, flat morphism
`q : V ⟶ X` locally of finite presentation. -/
theorem BigFppfOver.exists_flat_section_of_mem_topology {X : BigFppfOver B S hS}
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hP : Presheaf.IsSheaf (BigFppfOver.topology B S hS) P) (p : P ⟶ yoneda.obj X)
    (hcov : ∃ R ∈ BigFppfOver.topology B S hS X, ∀ ⦃W : BigFppfOver B S hS⦄ (a : W ⟶ X),
      R a → ∃ l : P.obj (op W), p.app (op W) l = a) :
    ∃ (V : BigFppfOver B S hS) (q : V ⟶ X) (l : P.obj (op V)),
      Surjective ((BigFppfOver.toScheme B S hS).map q) ∧
      Flat ((BigFppfOver.toScheme B S hS).map q) ∧
      LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map q) ∧
      p.app (op V) l = q := by
  obtain ⟨R, hR, hRs⟩ := hcov
  obtain ⟨ι, Xi, V, j, q, g, hgR, hjq, hjoi, hjcov, hqsurj, hqflat, hqlfp, ⟨hcolim⟩⟩ :=
    exists_flat_singleton_refinement_of_mem_topology B S hS X hR
  choose l₀ hl₀ using fun i => hRs (g i) (hgR i)
  have hP' : Presieve.IsSheaf (BigFppfOver.topology B S hS) P :=
    (isSheaf_iff_isSheaf_of_type _ _).1 hP
  obtain ⟨l, hl⟩ := BigFppfOver.exists_section_of_disjoint_openCover hP' j hjoi
    (fun k k' hkk' y y' => ne_toScheme_map_cofan hcolim hkk' y y') hjcov l₀
  refine ⟨V, q, l, hqsurj, hqflat, hqlfp, ?_⟩
  refine Cofan.IsColimit.hom_ext hcolim _ _ fun i => ?_
  have h := NatTrans.naturality_apply p (j i).op l
  rw [hl i, hl₀ i] at h
  change j i ≫ p.app (op V) l = j i ≫ q
  rw [hjq i]
  exact h.symm

/-- A sheaf `P` on the big fppf site of `S` with a morphism `p : P ⟶ h_X` whose base change along
a surjective, flat morphism `q : V ⟶ X` locally of finite presentation is `h_V × h_G` is an
algebraic space. -/
theorem isAlgebraicSpace_of_isPullback_yoneda_prod {X V G : BigFppfOver B S hS}
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hP : Presheaf.IsSheaf (BigFppfOver.topology B S hS) P) (p : P ⟶ yoneda.obj X)
    (q : V ⟶ X)
    (hq : (@Surjective.{u} ⊓ @Flat.{u} ⊓ @LocallyOfFinitePresentation.{u} :
      MorphismProperty Scheme.{u}) ((BigFppfOver.toScheme B S hS).map q))
    (φ : yoneda.obj V ⨯ yoneda.obj G ⟶ P) (hφ : IsPullback φ prod.fst p (yoneda.map q)) :
    IsAlgebraicSpace B S hS P := by
  have hPbc : MorphismProperty.IsStableUnderBaseChange
      (@Surjective.{u} ⊓ @Flat.{u} ⊓ @LocallyOfFinitePresentation.{u} :
        MorphismProperty Scheme.{u}) := by
    have h₁ : MorphismProperty.IsStableUnderBaseChange
        (@Surjective.{u} ⊓ @Flat.{u} : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.inf
    exact MorphismProperty.IsStableUnderBaseChange.inf
      (P := (@Surjective.{u} ⊓ @Flat.{u} : MorphismProperty Scheme.{u}))
  exact Space.isAlgebraicSpace_of_relativelyRepresentable_of_isBootstrap B S hS
    (Space.isBootstrapAlgebraicSpaceAlongFlatSurjection_of_quotientSheaf B S hS
      (Space.bootstrap04S6QuotientSheaf B S hS)) P hP _
    (isAlgebraicSpace_prod B S hS (isAlgebraicSpace_yoneda B S hS V)
      (isAlgebraicSpace_yoneda B S hS G)) φ
    ((Functor.relativelyRepresentable.isStableUnderBaseChange yoneda).of_isPullback hφ.flip
      (Functor.relativelyRepresentable.map yoneda q))
    ((MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hφ.flip
      (Space.presheaf_yoneda_map_of_inverseImage B S hS hPbc q hq))

/-- Let `p : P ⟶ h_X` be a morphism of presheaves on the big fppf site of `S` whose base change
along a surjective, flat morphism `q : V ⟶ X` locally of finite presentation is `h_V × h_G`, for
`G` smooth over `S`. If `a : h_Y ⟶ P` is étale after every representable base change, then the
morphism `y : Y ⟶ X` with `h_y = a ≫ p` is smooth. -/
theorem smooth_toScheme_map_of_isPullback_yoneda_prod {X V G Y : BigFppfOver B S hS}
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : P ⟶ yoneda.obj X) (q : V ⟶ X)
    (hqsurj : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqflat : Flat ((BigFppfOver.toScheme B S hS).map q))
    (hqlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map q))
    (hG : Smooth ((BigFppfOver.toScheme B S hS).map (Over.mkIdTerminal.from G)))
    (φ : yoneda.obj V ⨯ yoneda.obj G ⟶ P) (hφ : IsPullback φ prod.fst p (yoneda.map q))
    (a : yoneda.obj Y ⟶ P)
    (ha : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a)
    (y : Y ⟶ X) (hy : yoneda.map y = a ≫ p) :
    Smooth ((BigFppfOver.toScheme B S hS).map y) := by
  let T := BigFppfOver.toScheme B S hS
  let tV : V ⟶ Over.mk (𝟙 (B.obj hS)) := Over.mkIdTerminal.from V
  let tG : G ⟶ Over.mk (𝟙 (B.obj hS)) := Over.mkIdTerminal.from G
  have hyT : IsTerminal (yoneda.obj (Over.mk (𝟙 (B.obj hS)))) :=
    Over.mkIdTerminal.isTerminalObj yoneda _
  -- `h_{V ×_S G}` is the product `h_V × h_G`
  have h₁ : IsPullback (yoneda.map (pullback.fst tV tG)) (yoneda.map (pullback.snd tV tG))
      (yoneda.map tV) (yoneda.map tG) :=
    (IsPullback.of_hasPullback tV tG).map yoneda
  have h₂ : IsPullback (prod.fst : yoneda.obj V ⨯ yoneda.obj G ⟶ _) prod.snd
      (yoneda.map tV) (yoneda.map tG) := by
    have h : IsPullback (prod.fst : yoneda.obj V ⨯ yoneda.obj G ⟶ _) prod.snd
        (hyT.from (yoneda.obj V)) (hyT.from (yoneda.obj G)) :=
      IsPullback.of_is_product (limit.isLimit (pair (yoneda.obj V) (yoneda.obj G))) hyT
    rwa [hyT.hom_ext (hyT.from _) (yoneda.map tV),
      hyT.hom_ext (hyT.from _) (yoneda.map tG)] at h
  let e := h₁.isoIsPullback _ _ h₂
  have hsq : IsPullback e.hom (yoneda.map (pullback.fst tV tG)) prod.fst (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [IsPullback.isoIsPullback_hom_fst, Category.comp_id]⟩
  have hφ' := hsq.paste_horiz hφ
  rw [Category.id_comp] at hφ'
  -- the base change of the atlas along `h_{V ×_S G} ⟶ P`
  let g := e.hom ≫ φ
  have hr := ha.rep.isPullback' g
  have hc : Etale (T.map (ha.rep.snd g)) := ha.property_snd g
  have hbig := hr.paste_vert hφ'
  rw [← Functor.map_comp, ← hy] at hbig
  have hC : IsPullback (ha.rep.fst' g) (ha.rep.snd g ≫ pullback.fst tV tG) y q :=
    IsPullback.of_map_of_faithful yoneda hbig
  have hT := hC.map T
  have hfst : Smooth (T.map (pullback.fst tV tG)) :=
    MorphismProperty.of_isPullback ((IsPullback.of_hasPullback tV tG).map T).flip hG
  have hsnd : Smooth (T.map (ha.rep.snd g ≫ pullback.fst tV tG)) := by
    rw [T.map_comp]
    infer_instance
  refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd (P := @Smooth)
    (K := Scheme.fppfPrecoverage) (R := Presieve.singleton (T.map q)) ?_ ?_
  · change Presieve.singleton _ ∈
      Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation) _
    exact (Scheme.singleton_mem_precoverage_iff _ _).2 ⟨hqsurj.1, hqflat, hqlfp⟩
  · rintro _ _ _ ⟨⟩
    rw [← hT.isoPullback_inv_snd]
    infer_instance

/-- **Étale-local sections of a torsor under a smooth group.**

Let `p : P ⟶ h_X` be a morphism from a sheaf on the big fppf site of `S` to the presheaf
represented by `X`. Assume `p` has sections over the arrows of a covering sieve of `X`, and that
over every `W` through which `p` has a section `l`, the base change of `p` along `p(l) : W ⟶ X`
is `h_W × h_G` for an object `G` smooth over `S`. Then every point of `X` is in the image of an
étale morphism `V ⟶ X` over which `p` has a section. -/
theorem exists_etale_section_of_isPullback_prod {X : BigFppfOver B S hS}
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hP : Presheaf.IsSheaf (BigFppfOver.topology B S hS) P) (p : P ⟶ yoneda.obj X)
    (G : BigFppfOver B S hS) (hG : Smooth ((BigFppfOver.toScheme B S hS).map
      (Over.mkIdTerminal.from G)))
    (hcov : ∃ R ∈ BigFppfOver.topology B S hS X, ∀ ⦃W : BigFppfOver B S hS⦄ (a : W ⟶ X),
      R a → ∃ l : P.obj (op W), p.app (op W) l = a)
    (htriv : ∀ (W : BigFppfOver B S hS) (l : P.obj (op W)),
      ∃ φ : yoneda.obj W ⨯ yoneda.obj G ⟶ P,
        IsPullback φ prod.fst p (yoneda.map (p.app (op W) l)))
    (x : (BigFppfOver.toScheme B S hS).obj X) :
    ∃ (V : BigFppfOver B S hS) (e : V ⟶ X), Etale ((BigFppfOver.toScheme B S hS).map e) ∧
      x ∈ Set.range ((BigFppfOver.toScheme B S hS).map e) ∧
      ∃ l : P.obj (op V), p.app (op V) l = e := by
  let T := BigFppfOver.toScheme B S hS
  obtain ⟨V, q, l, hqsurj, hqflat, hqlfp, hl⟩ :=
    BigFppfOver.exists_flat_section_of_mem_topology B S hS hP p hcov
  obtain ⟨φ, hφ⟩ := htriv V l
  rw [hl] at hφ
  have hPalg := isAlgebraicSpace_of_isPullback_yoneda_prod B S hS hP p q
    ⟨⟨hqsurj, hqflat⟩, hqlfp⟩ φ hφ
  obtain ⟨Y, a, ha_surj, ha_et⟩ := hPalg.exists_atlas
  let y : Y ⟶ X := yoneda.preimage (a ≫ p)
  have hy : yoneda.map y = a ≫ p := yoneda.map_preimage _
  have hsm : Smooth (T.map y) := smooth_toScheme_map_of_isPullback_yoneda_prod B S hS p q
    hqsurj hqflat hqlfp hG φ hφ a ha_et y hy
  -- `x` is in the image of `y`: pull the atlas back along the section `l`
  have hx : x ∈ Set.range (T.map y) := by
    obtain ⟨v, hv⟩ := hqsurj.1 x
    let lv : yoneda.obj V ⟶ P := yonedaEquiv.symm l
    have hlv : lv ≫ p = yoneda.map q := by
      apply yonedaEquiv.injective
      rw [yonedaEquiv_comp, Equiv.apply_symm_apply, yonedaEquiv_yoneda_map, hl]
    have hr := ha_surj.rep.isPullback' lv
    have hsurj : Surjective (T.map (ha_surj.rep.snd lv)) := ha_surj.property_snd lv
    obtain ⟨z, hz⟩ := hsurj.1 v
    refine ⟨T.map (ha_surj.rep.fst' lv) z, ?_⟩
    have hcomp : ha_surj.rep.fst' lv ≫ y = ha_surj.rep.snd lv ≫ q := by
      apply yoneda.map_injective
      rw [Functor.map_comp, Functor.map_comp, hy, ← Category.assoc, hr.w, Category.assoc, hlv]
    rw [← Scheme.Hom.comp_apply, ← T.map_comp, hcomp, T.map_comp, Scheme.Hom.comp_apply, hz, hv]
  -- Stacks 055U: an étale neighbourhood of `x` lifting along `y`
  obtain ⟨X', hX', e, he, hxe, c, hc⟩ := exists_contains_etale_lift_of_smooth B y.left hsm x hx
  let e' : B.obj hX' ⟶ X.left := ObjectProperty.homMk e
  let c' : B.obj hX' ⟶ Y.left := ObjectProperty.homMk c
  have hce : c' ≫ y.left = e' := ObjectProperty.hom_ext _ hc
  let V' : BigFppfOver B S hS := Over.mk (e' ≫ X.hom)
  let eV : V' ⟶ X := Over.homMk e'
  have hcw : c' ≫ Y.hom = e' ≫ X.hom := by
    rw [← Over.w y, ← Category.assoc, hce]
  let cV : V' ⟶ Y := Over.homMk c' hcw
  have hceq : cV ≫ y = eV := Over.OverMorphism.ext hce
  have h₁ : p.app (op Y) (yonedaEquiv a) = y := by
    rw [← yonedaEquiv_comp, ← hy, yonedaEquiv_yoneda_map]
  refine ⟨V', eV, he, hxe, P.map cV.op (yonedaEquiv a), ?_⟩
  rw [NatTrans.naturality_apply, h₁]
  exact hceq

end AlgebraicGeometry

end
