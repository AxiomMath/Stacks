module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.Topology.Dimension.KrullSupplement

/-!
# Presentations from a given atlas, and presentations over a chart of the target

Let `F` be an algebraic space over `S`. Every surjective étale atlas `a : U ⟶ F` by a scheme
gives an étale presentation of `F` with relation `U ×_F U` (Stacks 0262, 0263). For a morphism
`f : F ⟶ G` of algebraic spaces and presentations `P` of `F` and `Q` of `G`, the scheme
`U_P ×_G U_Q` is again a surjective étale atlas of `F`, and the resulting presentation of `F`
maps to `Q` over `f`: its presenting scheme maps to that of `Q`, and its relation scheme maps to
that of `Q`, compatibly with both projections. Maps out of an algebraic space are determined by,
and descend along, the atlas of a presentation (Stacks 0262 (3)).

## Main definitions

* `AlgebraicGeometry.Space.atlasPresentation`: the presentation attached to an atlas.
* `AlgebraicGeometry.Space.presentationOverChart`: a presentation of `F` mapping to a given
  presentation of `G` over `f`, with `presentationOverChartHom` and
  `presentationOverChartRelHom`.
* `AlgebraicGeometry.Space.quotientDescOfPresentation`: descent of a map along an atlas.

## References

* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
* [Stacks Project, Tag 0263](https://stacks.math.columbia.edu/tag/0263)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Groupoids

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0263, from a given atlas.** The presentation of an algebraic space attached to a
surjective étale atlas `a : U ⟶ F`, with relation the fibre product `U ×_F U`. -/
def atlasPresentation (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F)
    (hasurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a)
    (haetale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a) :
    Presentation B S hS F hF :=
  let hf : yoneda.relativelyRepresentable a := haetale.1
  let R := hf.pullback a
  let src : R ⟶ U := hf.snd a
  let tgt : R ⟶ U := yoneda.preimage (hf.fst a)
  have hkernel : IsPullback (yoneda.map tgt) (yoneda.map src) a a := by
    simpa [tgt, src] using hf.isPullback a
  have hsrc : PreRelation.source (prod.lift ((Over.post B.inclusion).map tgt)
      ((Over.post B.inclusion).map src)) = (Over.post B.inclusion).map src :=
    prod.lift_snd _ _
  have htgt : PreRelation.target (prod.lift ((Over.post B.inclusion).map tgt)
      ((Over.post B.inclusion).map src)) = (Over.post B.inclusion).map tgt :=
    prod.lift_fst _ _
  { U := U
    R := R
    target := tgt
    source := src
    isEtaleEquivalenceRelation :=
      { isEquivalenceRelation := by
          rw [htgt, hsrc]
          exact isEquivalenceRelation_of_isPullback B S hS a tgt src hkernel
        etale_source := by
          rw [hsrc]
          exact haetale.2 a (hf.fst a) (hf.snd a) (hf.isPullback a)
        etale_target := by
          rw [htgt]
          exact haetale.2 a (yoneda.map src) tgt
            (by simpa [tgt, src] using (hf.isPullback a).flip) }
    toSpace := a
    surjective := hasurj
    etale := haetale
    isPullback := hkernel }

variable {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}
  {hG : IsAlgebraicSpace B S hS G} (f : F ⟶ G) (P : Presentation B S hS F hF)
  (Q : Presentation B S hS G hG)

/-- The presenting scheme `U_P ×_G U_Q` of the presentation over a chart. -/
abbrev presentationOverChartScheme : BigFppfOver B S hS :=
  Q.etale.rep.pullback (P.toSpace ≫ f)

/-- The projection `U_P ×_G U_Q ⟶ U_P`. -/
abbrev presentationOverChartSnd : presentationOverChartScheme f P Q ⟶ P.U :=
  Q.etale.rep.snd (P.toSpace ≫ f)

/-- The atlas `U_P ×_G U_Q ⟶ U_P ⟶ F` is étale. -/
theorem etale_presentationOverChart :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)))
      (yoneda.map (presentationOverChartSnd f P Q) ≫ P.toSpace) :=
  etale_comp_of_scheme B S hS _ _
    (Q.etale.2 (P.toSpace ≫ f) (Q.etale.rep.fst _) (Q.etale.rep.snd _) (Q.etale.rep.isPullback _))
    P.etale

/-- The atlas `U_P ×_G U_Q ⟶ U_P ⟶ F` is surjective. -/
theorem surjective_presentationOverChart :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)))
      (yoneda.map (presentationOverChartSnd f P Q) ≫ P.toSpace) := by
  have := inverseImage_isStableUnderBaseChange B S hS
    (inferInstance : MorphismProperty.IsStableUnderBaseChange (@Surjective.{u}))
  have := inverseImage_isStableUnderComposition B S hS
    (inferInstance : MorphismProperty.IsMultiplicative (@Surjective.{u})).toIsStableUnderComposition
  refine MorphismProperty.comp_mem _ _ _ ((presheaf_yoneda_map_iff B S hS inferInstance _).2 ?_)
    P.surjective
  exact Q.surjective.2 (P.toSpace ≫ f) (Q.etale.rep.fst _) (Q.etale.rep.snd _)
    (Q.etale.rep.isPullback _)

/-- **A presentation of `F` over a presentation of `G`**: the presentation of `F` attached to
the atlas `U_P ×_G U_Q ⟶ U_P ⟶ F`, whose presenting scheme maps to `U_Q` over `f`. -/
def presentationOverChart : Presentation B S hS F hF :=
  atlasPresentation F hF (presentationOverChartScheme f P Q)
    (yoneda.map (presentationOverChartSnd f P Q) ≫ P.toSpace)
    (surjective_presentationOverChart f P Q) (etale_presentationOverChart f P Q)

/-- The map of presenting schemes `U_P ×_G U_Q ⟶ U_Q`. -/
def presentationOverChartHom : (presentationOverChart f P Q).U ⟶ Q.U :=
  yoneda.preimage (Q.etale.rep.fst (P.toSpace ≫ f))

/-- The map of presenting schemes lies over `f`. -/
theorem presentationOverChart_comm :
    (presentationOverChart f P Q).toSpace ≫ f =
      yoneda.map (presentationOverChartHom f P Q) ≫ Q.toSpace := by
  refine (Category.assoc _ _ _).trans (((Q.etale.rep.isPullback (P.toSpace ≫ f)).w).symm.trans ?_)
  exact congrArg (· ≫ Q.toSpace) (yoneda.map_preimage (Q.etale.rep.fst (P.toSpace ≫ f))).symm

/-- The map of relation schemes `R_P' ⟶ R_Q`, through the fibre product `R_Q = U_Q ×_G U_Q`. -/
def presentationOverChartRelHom : (presentationOverChart f P Q).R ⟶ Q.R :=
  yoneda.preimage (Q.isPullback.lift
    (yoneda.map ((presentationOverChart f P Q).target ≫ presentationOverChartHom f P Q))
    (yoneda.map ((presentationOverChart f P Q).source ≫ presentationOverChartHom f P Q)) (by
      rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
        ← presentationOverChart_comm, ← Category.assoc,
        ← Category.assoc, (presentationOverChart f P Q).isPullback.w]))

/-- The map of relation schemes `R_P' ⟶ R_Q` is compatible with the targets, via the map
`U_P ×_G U_Q ⟶ U_Q`. -/
theorem presentationOverChartRelHom_target :
    presentationOverChartRelHom f P Q ≫ Q.target =
      (presentationOverChart f P Q).target ≫ presentationOverChartHom f P Q :=
  yoneda.map_injective (by
    rw [Functor.map_comp, presentationOverChartRelHom, Functor.map_preimage, IsPullback.lift_fst])

/-- The map of relation schemes `R_P' ⟶ R_Q` is compatible with the sources, via the map
`U_P ×_G U_Q ⟶ U_Q`. -/
theorem presentationOverChartRelHom_source :
    presentationOverChartRelHom f P Q ≫ Q.source =
      (presentationOverChart f P Q).source ≫ presentationOverChartHom f P Q :=
  yoneda.map_injective (by
    rw [Functor.map_comp, presentationOverChartRelHom, Functor.map_preimage, IsPullback.lift_snd])

/-! ### Descent of maps along the atlas of a presentation -/

variable (hGsh : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G)

/-- **Stacks 0262 (3).** A map from the presenting scheme of a presentation of `F` to a sheaf
`G` which agrees on the two projections of the relation descends to `F`. -/
def quotientDescOfPresentation (k : yoneda.obj P.U ⟶ G)
    (hk : yoneda.map P.target ≫ k = yoneda.map P.source ≫ k) : F ⟶ G :=
  let h := isCoequalizer_of_surjectiveEtale B S hS P.toSpace P.target P.source P.isPullback hF
    P.surjective P.etale
  (sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)).map
    (Cofork.IsColimit.desc h.choose_spec.choose_spec.some
      (show (⟨yoneda.obj P.U, h.choose_spec.choose⟩ : Sheaf (BigFppfOver.topology B S hS)
        (Type u)) ⟶ ⟨G, hGsh⟩ from ⟨k⟩) (by apply Sheaf.hom_ext; exact hk))

/-- The descended map `F ⟶ G` composed with the atlas `U ⟶ F` is the given map `U ⟶ G`. -/
theorem toSpace_quotientDescOfPresentation (k : yoneda.obj P.U ⟶ G)
    (hk : yoneda.map P.target ≫ k = yoneda.map P.source ≫ k) :
    P.toSpace ≫ quotientDescOfPresentation P hGsh k hk = k := by
  exact congrArg (sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)).map
    (Cofork.IsColimit.π_desc' _ _ _)

include hGsh in
/-- **Maps out of an algebraic space are determined on the atlas of a presentation.** -/
theorem presentation_toSpace_hom_ext {a b : F ⟶ G}
    (hab : P.toSpace ≫ a = P.toSpace ≫ b) : a = b := by
  obtain ⟨_, _, ⟨hq⟩⟩ := isCoequalizer_of_surjectiveEtale B S hS P.toSpace P.target P.source
    P.isPullback hF P.surjective P.etale
  let A : (⟨F, hF.isSheaf⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶ ⟨G, hGsh⟩ := ⟨a⟩
  let A' : (⟨F, hF.isSheaf⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶ ⟨G, hGsh⟩ := ⟨b⟩
  have : A = A' := Cofork.IsColimit.hom_ext hq (by apply Sheaf.hom_ext; exact hab)
  exact congrArg (sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)).map this

end AlgebraicGeometry.Space

end
