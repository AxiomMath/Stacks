module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartRespectsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescentRealised
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeComposite

/-!
# Presented Noetherian approximations

A Noetherian approximation of a presheaf `X` on the big fppf site of `Spec ℤ` is a directed
inverse system of quasi-separated algebraic spaces of finite type over `Spec ℤ`, with affine
transition morphisms, whose limit is `X` (`AlgebraicGeometry.Space.NoetherianApproximation`). It
is *presented* when every stage comes with a surjective étale atlas by an object of the site and an
object of the site representing the kernel pair of that atlas, naturally in the stage, such that
both systems of objects of the site have affine transition morphisms and limits realised in the
site, the limit of the atlases being an atlas of `X`.

A presentation reduces statements about the system to statements about cofiltered systems of
schemes whose limits are realised in the site, and for those no bound on the size of the index set
is needed. In particular Stacks 0CP4 holds for a presented approximation: this is what replaces,
for the approximations produced by absolute Noetherian approximation, the bound on the index set
that the general form of Stacks 0CP4 in this development carries and that such approximations do
not satisfy.

## Main definitions

* `AlgebraicGeometry.Space.viewOverIntegersTerminalIso`: a presheaf on the big fppf site of
  `Spec ℤ`, viewed over `Spec ℤ`, is itself.
* `AlgebraicGeometry.Space.LimitPresentation`: a presentation of a cone over an inverse system
  of presheaves by atlases and their kernel pairs.
* `AlgebraicGeometry.Space.PresentedNoetherianApproximation`: a Noetherian approximation with a
  presentation.

## Main results

* `AlgebraicGeometry.Space.NoetherianApproximation.isQuasiCompactSpace_obj` and
  `AlgebraicGeometry.Space.NoetherianApproximation.isLocallyOfFinitePresentation_obj`: the stages
  of a Noetherian approximation over `Spec ℤ` are quasi-compact, and locally of finite
  presentation over `Spec ℤ`.
* `AlgebraicGeometry.Space.exists_stage_hom_of_isLimit_toScheme` and
  `AlgebraicGeometry.Space.exists_stage_eq_of_isLimit_toScheme`: Stacks 0CP4 for a cofiltered
  system of quasi-compact and quasi-separated objects of the site whose limit is realised in the
  site, and a target locally of finite presentation over the base.
* `AlgebraicGeometry.Space.PresentedNoetherianApproximation.exists_stage_hom` and
  `AlgebraicGeometry.Space.PresentedNoetherianApproximation.exists_stage_eq`: Stacks 0CP4 for a
  presented approximation and a target locally of finite presentation over `Spec ℤ`.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 0CP4](https://stacks.math.columbia.edu/tag/0CP4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

section Terminal

variable (B : BigFppfSite.{u}) (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **A presheaf over `Spec ℤ`, viewed over `Spec ℤ`, is itself.** The view is relocalization
along the structure morphism of the base, which over the terminal scheme is the identity. -/
noncomputable def viewOverIntegersTerminalIso
    (F : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u) :
    viewOverIntegers B (⊤_ Scheme.{u}) hZ hZ F ≅ F :=
  have h : (⟨terminal.from (⊤_ Scheme.{u})⟩ : B.obj hZ ⟶ B.obj hZ) = 𝟙 (B.obj hZ) := by
    ext
    exact terminal.hom_ext _ _
  eqToIso (congrArg (fun m => (OverShriek.relocalizePresheafFunctor m).obj F) h) ≪≫
    (OverShriek.relocalizePresheafFunctorIdIso (B.obj hZ)).app F

/-- The terminal presheaf on the big fppf site of `Spec ℤ` is represented by the identity of the
base. -/
noncomputable def terminalPresheafIso :
    yoneda.obj (Over.mk (𝟙 (B.obj hZ))) ≅
      ⊤_ ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u) :=
  ((Over.mkIdTerminal (X := B.obj hZ)).isTerminalObj yoneda _).uniqueUpToIso terminalIsTerminal

/-- An isomorphism of presheaves on the big fppf site has every relative morphism property pulled
back from a property of schemes containing the identities and respecting isomorphisms. -/
theorem presheaf_inverseImage_of_isIso' (P : MorphismProperty Scheme.{u})
    [P.ContainsIdentities] [P.RespectsIso]
    {F G : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u} (e : F ⟶ G) [IsIso e] :
    (P.inverseImage (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).presheaf e :=
  presheaf_of_isIso B (⊤_ Scheme.{u}) hZ (MorphismProperty.RespectsIso.inverseImage _ _)
    (fun U => by
      simpa using MorphismProperty.id_mem P ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj U))
    e

end Terminal

namespace NoetherianApproximation

attribute [local instance] NoetherianApproximation.preorder

variable {B : BigFppfSite.{u}} {hZ : B.Contains (⊤_ Scheme.{u})}
  {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
  (A : NoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ X)

/-- **The stages of a Noetherian approximation over `Spec ℤ` are quasi-compact.** A stage is of
finite type over `Spec ℤ`, so its structure morphism is quasi-compact, and the base change of
that morphism along the identity of the terminal presheaf, which is quasi-compact, is the stage
itself. -/
theorem isQuasiCompactSpace_obj (j : A.Iᵒᵖ) :
    IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ (A.diagram.obj j) := by
  have hterm : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ
      (⊤_ ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)) :=
    isQuasiCompactSpace_of_iso B _ hZ (terminalPresheafIso B hZ)
      (isQuasiCompactSpace_yoneda_of_isAffine B _ hZ (Over.mk (𝟙 (B.obj hZ)))
        (IsAffine.of_isIso (specULiftZIsTerminal.{u}.uniqueUpToIso terminalIsTerminal).inv))
  exact isQuasiCompactSpace_of_iso B _ hZ (viewOverIntegersTerminalIso B hZ _)
    (isQuasiCompactSpace_of_iso B _ hZ (asIso (pullback.snd (𝟙 _) _))
      ((A.isFiniteTypeOverIntegers j).2 (⊤_ ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u))
        (isAlgebraicSpace_terminal B (⊤_ Scheme.{u}) hZ) hterm (𝟙 _)))

/-- **The stages of a Noetherian approximation over `Spec ℤ` are locally of finite presentation
over `Spec ℤ`.** A stage is locally of finite type over `Spec ℤ`, and the terminal presheaf is
locally Noetherian, so Stacks 06G4 applies. -/
theorem isLocallyOfFinitePresentation_obj (j : A.Iᵒᵖ) :
    IsLocallyOfFinitePresentation B (⊤_ Scheme.{u}) hZ (terminal.from (A.diagram.obj j)) := by
  have hN : HasEtaleLocalProperty B (⊤_ Scheme.{u}) hZ
      (⊤_ ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u))
      (fun T : Scheme.{u} => IsLocallyNoetherian T) := by
    have _ : MorphismProperty.ContainsIdentities (@Surjective.{u} : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsMultiplicative.toContainsIdentities
    have _ : MorphismProperty.ContainsIdentities (@Etale.{u} : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsMultiplicative.toContainsIdentities
    have : IsNoetherianRing (ULift.{u} ℤ) :=
      isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
    exact ⟨Over.mk (𝟙 (B.obj hZ)), (terminalPresheafIso B hZ).hom,
      presheaf_inverseImage_of_isIso' B hZ _ _, presheaf_inverseImage_of_isIso' B hZ _ _,
      LocallyOfFiniteType.isLocallyNoetherian
        (specULiftZIsTerminal.{u}.uniqueUpToIso terminalIsTerminal).inv⟩
  exact isLocallyOfFinitePresentation_of_isLocallyOfFiniteType B (⊤_ Scheme.{u}) hZ
    (A.isAlgebraicSpace j) (isAlgebraicSpace_terminal B (⊤_ Scheme.{u}) hZ)
    (terminal.from (A.diagram.obj j)) hN
    ((isLocallyOfFiniteType_terminal_iff_of_iso B _ hZ
      (viewOverIntegersTerminalIso B hZ _)).mp (A.isFiniteTypeOverIntegers j).1)

end NoetherianApproximation

/-! ### Stacks 0CP4 over a limit of schemes realised in the site -/

section SchemeSystem

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ BigFppfOver B S hS}

/-- **Two morphisms out of a stage of a cofiltered system of quasi-compact objects of the site,
into an algebraic space locally of finite presentation over `S`, which agree over the limit agree
at a later stage.** The system has affine transition morphisms and its limit is realised in the
site; no hypothesis on the size of the index category is needed. -/
theorem exists_stage_eq_of_isLimit_toScheme
    (hAffine : ∀ {i j : I} (f : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom
      ((BigFppfOver.toScheme B S hS).map (D.map f)))
    {c : Cone D} (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
    (hQc : ∀ i, IsQuasiCompactSpace B S hS (yoneda.obj (D.obj i)))
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hYfp : IsLocallyOfFinitePresentation B S hS (terminal.from Y))
    {i : I} (f g : yoneda.obj (D.obj i) ⟶ Y)
    (h : yoneda.map (c.π.app i) ≫ f = yoneda.map (c.π.app i) ≫ g) :
    ∃ (j : I) (e : j ⟶ i), yoneda.map (D.map e) ≫ f = yoneda.map (D.map e) ≫ g := by
  have hfst : pullback.fst (𝟙 (yoneda.obj (D.obj i))) (yoneda.map (c.π.app i)) =
      pullback.snd _ _ ≫ yoneda.map (c.π.app i) := by
    simpa using pullback.condition (f := 𝟙 (yoneda.obj (D.obj i))) (g := yoneda.map (c.π.app i))
  obtain ⟨j, e, hj⟩ := eventually_eq_on_quasiCompact_source_of_isLimit B S hS hAffine hc i
    (isAlgebraicSpace_yoneda B S hS (D.obj i)) hY (isAlgebraicSpace_terminal B S hS) (hQc i)
    (𝟙 _) (terminal.from Y) (terminal.from _) hYfp f g (terminal.hom_ext _ _)
    (terminal.hom_ext _ _) (by rw [hfst, Category.assoc, Category.assoc, h])
  refine ⟨j, e, ?_⟩
  simpa only [pullback.lift_fst_assoc] using
    congrArg (fun k => pullback.lift (yoneda.map (D.map e)) (𝟙 _) (by simp) ≫ k) hj

/-- **A morphism from the limit of a cofiltered system of quasi-compact and quasi-separated
objects of the site to an algebraic space locally of finite presentation over `S` comes from a
stage.** The system has affine transition morphisms and its limit is realised in the site; no
hypothesis on the size of the index category is needed. -/
theorem exists_stage_hom_of_isLimit_toScheme
    (hAffine : ∀ {i j : I} (f : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom
      ((BigFppfOver.toScheme B S hS).map (D.map f)))
    {c : Cone D} (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
    (hQc : ∀ i, IsQuasiCompactSpace B S hS (yoneda.obj (D.obj i)))
    (hQs : ∀ i, IsAbsolutelyQuasiSeparated B S hS (BigFppfSite.contains_terminal B)
      (yoneda.obj (D.obj i)))
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hYfp : IsLocallyOfFinitePresentation B S hS (terminal.from Y))
    (g : yoneda.obj c.pt ⟶ Y) :
    ∃ (j : I) (h : yoneda.obj (D.obj j) ⟶ Y), yoneda.map (c.π.app j) ≫ h = g := by
  classical
  obtain ⟨i⟩ := IsCofiltered.nonempty (C := I)
  have hT := isAlgebraicSpace_terminal B S hS
  have hDi := isAlgebraicSpace_yoneda B S hS (D.obj i)
  let Yi : Over (yoneda.obj (D.obj i)) := Over.mk (𝟙 _)
  let Zi : Over (yoneda.obj (D.obj i)) :=
    Over.mk (pullback.snd (terminal.from Y) (terminal.from (yoneda.obj (D.obj i))))
  have hZalg : IsAlgebraicSpace B S hS Zi.left :=
    isAlgebraicSpace_pullback B S hS _ _ hY hDi hT
  have hZfp : IsLocallyOfFinitePresentation B S hS Zi.hom := by
    let Ys : AlgebraicSpaces B S hS := ⟨Y, hY⟩
    let Ds : AlgebraicSpaces B S hS := ⟨yoneda.obj (D.obj i), hDi⟩
    let Ts : AlgebraicSpaces B S hS := ⟨_, hT⟩
    exact (isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct B S hS
        (ObjectProperty.homMk (terminal.from Y) : Ys ⟶ Ts)
        (ObjectProperty.homMk (terminal.from _) : Ds ⟶ Ts)) hYfp
  let f₀ : pullback Yi.hom (yoneda.map (c.π.app i)) ⟶ Zi.left :=
    pullback.lift (pullback.snd _ _ ≫ g) (pullback.fst _ _) (terminal.hom_ext _ _)
  have hf₀ : f₀ ≫ Zi.hom = pullback.fst Yi.hom (yoneda.map (c.π.app i)) ≫ Yi.hom := by
    show f₀ ≫ pullback.snd _ _ = pullback.fst _ _ ≫ 𝟙 _
    rw [pullback.lift_snd, Category.comp_id]
  obtain ⟨j, U, p, g', hs, he, hg', hgf⟩ := exists_stage_atlas_factorization_of_isLimit B S hS
    hAffine hc i Yi hDi (hQc i) hZalg Zi.hom hZfp f₀ hf₀
  obtain ⟨k, e, raw, -, hraw⟩ := exists_stage_hom_of_atlas_factorization B S hS hAffine hc i j
    Yi Zi hDi hZalg (hQs i) (hQs j.left) hZfp U p hs he g' f₀ hg' hgf
  let d := e ≫ j.hom
  let σ : yoneda.obj c.pt ⟶ pullback Yi.hom (yoneda.map (c.π.app i)) :=
    pullback.lift (yoneda.map (c.π.app i)) (𝟙 _) (by simp [Yi])
  let ℓ : yoneda.obj (D.obj k) ⟶ pullback Yi.hom (yoneda.map (D.map d)) :=
    pullback.lift (yoneda.map (D.map d)) (𝟙 _) (by simp [Yi])
  refine ⟨k, ℓ ≫ raw ≫ pullback.fst _ _, ?_⟩
  have hσℓ : σ ≫ pullback.lift (pullback.fst Yi.hom (yoneda.map (c.π.app i)))
      (pullback.snd Yi.hom (yoneda.map (c.π.app i)) ≫ yoneda.map (c.π.app k))
      (by rw [Category.assoc, ← Functor.map_comp, c.w d, pullback.condition]) =
      yoneda.map (c.π.app k) ≫ ℓ := by
    apply pullback.hom_ext
    · simp only [σ, ℓ, Category.assoc, pullback.lift_fst, ← Functor.map_comp, c.w d]
    · simp only [σ, ℓ, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
        Category.id_comp, Category.comp_id]
  rw [← reassoc_of% hσℓ, reassoc_of% hraw]
  simp only [σ, f₀, pullback.lift_fst, pullback.lift_snd_assoc, Category.id_comp]

end SchemeSystem

/-! ### Presentations of inverse systems -/

/-- A *limit presentation* of a cone `c` over an inverse system `D` of presheaves on the big fppf
site of `S`: at every stage a surjective étale atlas by a quasi-compact and quasi-separated object
of the site and an object of the site representing its kernel pair, natural in the stage, with
the atlases cartesian over the transition morphisms; both systems of objects of the site have
affine transition morphisms and limits realised in the site, and the limit of the atlases is the
base change of every stage atlas to `c.pt`.

A presentation reduces statements about the system to statements about cofiltered systems of
schemes whose limits are realised in the site, for which no bound on the size of the index
category is needed. -/
structure LimitPresentation (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} [Category.{u} I] (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (c : Cone D) where
  /-- The atlases of the stages. -/
  atlas : I ⥤ BigFppfOver B S hS
  /-- The objects representing the kernel pairs of the atlases. -/
  relation : I ⥤ BigFppfOver B S hS
  /-- The atlas morphisms. -/
  atlasMap : atlas ⋙ yoneda ⟶ D
  /-- The first projection of a kernel pair. -/
  src : relation ⟶ atlas
  /-- The second projection of a kernel pair. -/
  tgt : relation ⟶ atlas
  /-- Every atlas morphism is surjective. -/
  surjective_atlasMap (j : I) :
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (atlasMap.app j)
  /-- Every atlas morphism is étale. -/
  etale_atlasMap (j : I) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (atlasMap.app j)
  /-- The two projections are the kernel pair of the atlas morphism. -/
  isPullback_relation (j : I) : IsPullback (yoneda.map (src.app j)) (yoneda.map (tgt.app j))
    (atlasMap.app j) (atlasMap.app j)
  /-- The atlases are cartesian over the transition morphisms. -/
  isPullback_atlas {j k : I} (g : j ⟶ k) : IsPullback (yoneda.map (atlas.map g))
    (atlasMap.app j) (atlasMap.app k) (D.map g)
  /-- The transition morphisms of the atlases are affine morphisms of schemes. -/
  isAffineHom_atlas {j k : I} (g : j ⟶ k) : _root_.AlgebraicGeometry.IsAffineHom
    ((BigFppfOver.toScheme B S hS).map (atlas.map g))
  /-- The transition morphisms of the kernel pairs are affine morphisms of schemes. -/
  isAffineHom_relation {j k : I} (g : j ⟶ k) : _root_.AlgebraicGeometry.IsAffineHom
    ((BigFppfOver.toScheme B S hS).map (relation.map g))
  /-- Every atlas is quasi-compact. -/
  isQuasiCompactSpace_atlas (j : I) : IsQuasiCompactSpace B S hS (yoneda.obj (atlas.obj j))
  /-- Every atlas is a quasi-separated scheme. -/
  quasiSeparatedSpace_atlas (j : I) :
    QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj (atlas.obj j))
  /-- Every kernel pair is quasi-compact. -/
  isQuasiCompactSpace_relation (j : I) :
    IsQuasiCompactSpace B S hS (yoneda.obj (relation.obj j))
  /-- Every kernel pair is a quasi-separated scheme. -/
  quasiSeparatedSpace_relation (j : I) :
    QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj (relation.obj j))
  /-- A cone over the atlases. -/
  atlasCone : Cone atlas
  /-- It is a limit cone of schemes. -/
  isLimit_atlasCone : IsLimit ((BigFppfOver.toScheme B S hS).mapCone atlasCone)
  /-- A cone over the kernel pairs. -/
  relationCone : Cone relation
  /-- It is a limit cone of schemes. -/
  isLimit_relationCone : IsLimit ((BigFppfOver.toScheme B S hS).mapCone relationCone)
  /-- The first projection of the limit kernel pair. -/
  srcLim : relationCone.pt ⟶ atlasCone.pt
  /-- The second projection of the limit kernel pair. -/
  tgtLim : relationCone.pt ⟶ atlasCone.pt
  /-- The first projection of the limit kernel pair is the limit of the first projections. -/
  srcLim_π (j : I) : srcLim ≫ atlasCone.π.app j = relationCone.π.app j ≫ src.app j
  /-- The second projection of the limit kernel pair is the limit of the second projections. -/
  tgtLim_π (j : I) : tgtLim ≫ atlasCone.π.app j = relationCone.π.app j ≫ tgt.app j
  /-- The limit of the atlases maps to the vertex. -/
  limitAtlas : yoneda.obj atlasCone.pt ⟶ c.pt
  /-- The limit of the atlases is the base change of every stage atlas to the vertex. -/
  isPullback_limitAtlas (j : I) : IsPullback (yoneda.map (atlasCone.π.app j)) limitAtlas
    (atlasMap.app j) (c.π.app j)

namespace LimitPresentation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {I : Type u} [Category.{u} I] {D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {c : Cone D}
  (P : LimitPresentation B S hS D c)

include P

/-- The limit atlas lies over every stage atlas. -/
theorem limitAtlas_π (j : I) :
    P.limitAtlas ≫ c.π.app j = yoneda.map (P.atlasCone.π.app j) ≫ P.atlasMap.app j :=
  (P.isPullback_limitAtlas j).w.symm

/-- The limit atlas is surjective, as a base change of a surjective atlas. -/
theorem surjective_limitAtlas [Nonempty I] :
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf P.limitAtlas :=
  have j := Classical.arbitrary I
  presheaf_of_isPullback B S hS (P.isPullback_limitAtlas j) (P.surjective_atlasMap j)

/-- The limit atlas is étale, as a base change of an étale atlas. -/
theorem etale_limitAtlas [Nonempty I] :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf P.limitAtlas :=
  have j := Classical.arbitrary I
  presheaf_of_isPullback B S hS (P.isPullback_limitAtlas j) (P.etale_atlasMap j)

/-- The two projections of the limit kernel pair have the same image in the vertex. -/
theorem srcLim_limitAtlas (hc : IsLimit c) :
    yoneda.map P.srcLim ≫ P.limitAtlas = yoneda.map P.tgtLim ≫ P.limitAtlas := by
  refine hc.hom_ext fun j => ?_
  rw [Category.assoc, Category.assoc, P.limitAtlas_π, ← Category.assoc, ← Category.assoc,
    ← Functor.map_comp, ← Functor.map_comp, P.srcLim_π, P.tgtLim_π, Functor.map_comp,
    Functor.map_comp, Category.assoc, Category.assoc, (P.isPullback_relation j).w]

variable [IsCofiltered I]

/-- **Stacks 0CP4, the injectivity half, for a presented system.** Two morphisms out of a stage
of a presented cofiltered system of algebraic spaces, into an algebraic space locally of finite
presentation over `S`, which agree over the vertex agree at a later stage. -/
theorem exists_stage_eq (hD : ∀ j, IsAlgebraicSpace B S hS (D.obj j))
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hYfp : IsLocallyOfFinitePresentation B S hS (terminal.from Y))
    {i : I} (r s : D.obj i ⟶ Y) (h : c.π.app i ≫ r = c.π.app i ≫ s) :
    ∃ (k : I) (a : k ⟶ i), D.map a ≫ r = D.map a ≫ s := by
  obtain ⟨k, a, hk⟩ := exists_stage_eq_of_isLimit_toScheme B S hS
    P.isAffineHom_atlas P.isLimit_atlasCone P.isQuasiCompactSpace_atlas hY hYfp
    (P.atlasMap.app i ≫ r) (P.atlasMap.app i ≫ s) (by
      rw [← Category.assoc, ← Category.assoc, ← P.limitAtlas_π, Category.assoc, Category.assoc,
        h])
  refine ⟨k, a, hom_ext_of_etale_atlas B S hS (hD k).isSheaf
    hY.isSheaf (P.atlasMap.app k) (P.surjective_atlasMap k) (P.etale_atlasMap k) ?_⟩
  have hn := P.atlasMap.naturality a
  simp only [Functor.comp_map] at hn
  rw [← Category.assoc, ← Category.assoc, ← hn, Category.assoc, Category.assoc, hk]

/-- **Stacks 0CP4, the surjectivity half, for a presented system.** A morphism from the vertex
of a presented cofiltered system of algebraic spaces to an algebraic space locally of finite
presentation over `S` factors through a stage. -/
theorem exists_stage_hom (hc : IsLimit c) (hD : ∀ j, IsAlgebraicSpace B S hS (D.obj j))
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hYfp : IsLocallyOfFinitePresentation B S hS (terminal.from Y))
    (x : c.pt ⟶ Y) : ∃ (j : I) (z : D.obj j ⟶ Y), c.π.app j ≫ z = x := by
  have hcs : Presheaf.IsSheaf (BigFppfOver.topology B S hS) c.pt :=
    (Presheaf.isSheaf_of_iso_iff (hc.conePointUniqueUpToIso (limit.isLimit _))).mpr
      (isSheaf_limit B S hS D fun j => (hD j).isSheaf)
  obtain ⟨k, hk, hhk⟩ := exists_stage_hom_of_isLimit_toScheme B S hS
    P.isAffineHom_atlas P.isLimit_atlasCone P.isQuasiCompactSpace_atlas
    (fun j => isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B S hS _
      (BigFppfSite.contains_terminal B)
      ⟨_, P.quasiSeparatedSpace_atlas j, ⟨Functor.RepresentableBy.yoneda _⟩⟩)
    hY hYfp (P.limitAtlas ≫ x)
  obtain ⟨l, a, hl⟩ := exists_stage_eq_of_isLimit_toScheme B S hS
    P.isAffineHom_relation P.isLimit_relationCone P.isQuasiCompactSpace_relation hY hYfp
    (yoneda.map (P.src.app k) ≫ hk) (yoneda.map (P.tgt.app k) ≫ hk) (by
      rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
        ← P.srcLim_π, ← P.tgtLim_π, Functor.map_comp, Functor.map_comp, Category.assoc,
        Category.assoc, hhk, ← Category.assoc, ← Category.assoc, P.srcLim_limitAtlas hc])
  let hl' : yoneda.obj (P.atlas.obj l) ⟶ Y := yoneda.map (P.atlas.map a) ≫ hk
  have heq : yoneda.map (P.src.app l) ≫ hl' = yoneda.map (P.tgt.app l) ≫ hl' := by
    simp only [hl', ← Category.assoc, ← Functor.map_comp, ← P.src.naturality a,
      ← P.tgt.naturality a]
    simpa only [Functor.map_comp, Category.assoc] using hl
  obtain ⟨z, hz, -⟩ := existsUnique_desc_of_surjective_etale_atlas B S hS
    (hD l).isSheaf (P.atlasMap.app l) (P.isPullback_relation l)
    (P.surjective_atlasMap l) (P.etale_atlasMap l) hY.isSheaf hl' heq
  have : Nonempty I := IsCofiltered.nonempty
  refine ⟨l, z, hom_ext_of_etale_atlas B S hS hcs hY.isSheaf P.limitAtlas
    P.surjective_limitAtlas P.etale_limitAtlas ?_⟩
  rw [← Category.assoc, P.limitAtlas_π, Category.assoc, hz, ← Category.assoc,
    ← Functor.map_comp, P.atlasCone.w a, hhk]

end LimitPresentation

/-! ### Presented Noetherian approximations -/

/-- A *presented Noetherian approximation* of a presheaf `X` on the big fppf site of `Spec ℤ`: a
Noetherian approximation of `X` together with a limit presentation of its limiting cone. -/
structure PresentedNoetherianApproximation (B : BigFppfSite.{u})
    (hZ : B.Contains (⊤_ Scheme.{u})) (X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)
    extends NoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ X where
  /-- The presentation of the limiting cone. -/
  presentation : LimitPresentation B (⊤_ Scheme.{u}) hZ diagram (Cone.mk X π)

namespace PresentedNoetherianApproximation

attribute [local instance] NoetherianApproximation.preorder NoetherianApproximation.nonempty
  NoetherianApproximation.isDirected

variable {B : BigFppfSite.{u}} {hZ : B.Contains (⊤_ Scheme.{u})}
  {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
  (A : PresentedNoetherianApproximation B hZ X)

/-- **Stacks 0CP4, the injectivity half, for a presented approximation.** Two morphisms out of a
stage of a presented Noetherian approximation over `Spec ℤ`, into an algebraic space which is
locally of finite presentation over `Spec ℤ`, which agree over the vertex agree at a later
stage. -/
theorem exists_stage_eq {Y : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ Y)
    (hYfp : IsLocallyOfFinitePresentation B (⊤_ Scheme.{u}) hZ (terminal.from Y))
    {i : A.Iᵒᵖ} (r s : A.diagram.obj i ⟶ Y) (h : A.π.app i ≫ r = A.π.app i ≫ s) :
    ∃ (k : A.Iᵒᵖ) (a : k ⟶ i), A.diagram.map a ≫ r = A.diagram.map a ≫ s :=
  A.presentation.exists_stage_eq A.isAlgebraicSpace hY hYfp r s h

/-- **Stacks 0CP4, the surjectivity half, for a presented approximation.** A morphism from the
vertex of a presented Noetherian approximation over `Spec ℤ` to an algebraic space which is
locally of finite presentation over `Spec ℤ` factors through a stage. -/
theorem exists_stage_hom {Y : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ Y)
    (hYfp : IsLocallyOfFinitePresentation B (⊤_ Scheme.{u}) hZ (terminal.from Y))
    (x : X ⟶ Y) : ∃ (j : A.Iᵒᵖ) (z : A.diagram.obj j ⟶ Y), A.π.app j ≫ z = x :=
  A.presentation.exists_stage_hom A.isLimit A.isAlgebraicSpace hY hYfp x

end PresentedNoetherianApproximation

end AlgebraicGeometry.Space

end
