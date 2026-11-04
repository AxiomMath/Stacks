module

public import StacksFrontier.AlgebraicGeometry.Quot.HilbertLimitStage
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.ProperMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions

/-!
# Properness of a closed subspace of a base change at a stage of a limit of affine schemes

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site and let
`T = lim T_λ` be a directed limit of affine schemes over `Y`, all in the site. A closed subspace
`Z ⊆ X_{T_l}` of finite presentation over `T_l` whose inverse image in `X_T` is proper over `T`
has a proper inverse image in `X_{T_λ}` for some `λ ≥ l`. This is Stacks 08K1, applied to
`Z ⟶ T_l` over the system of the `T_λ`; the chapter's standing convention it asks for holds here,
because the limits of the base changed affine systems are the fibre products with `T`, which lie
in the site.

## Main results

* `AlgebraicGeometry.Space.siteContainsBaseChangeLimits_yoneda`: the system of the `T_λ`, read in
  presheaves, satisfies the standing convention of Stacks 07SD.
* `AlgebraicGeometry.Space.exists_isProper_preimage_stage`: the properness at a stage.
* `AlgebraicGeometry.Space.exists_hilbertFamily_baseChange_eq`: a family of the Hilbert functor
  over the limit comes from a stage.
* `AlgebraicGeometry.Space.exists_hilbertFamily_baseChange_eq_of_eq`: two families at a stage
  which agree over the limit agree at a later stage.

## References

* [Stacks Project, Tag 08K1](https://stacks.math.columbia.edu/tag/08K1)
* [Stacks Project, Tag 07SD](https://stacks.math.columbia.edu/tag/07SD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {Y : AlgebraicSpaces B S hS}

section Convention

variable {J : Type u} [Category.{u} J] [IsCofiltered J]
    (Dy : J ⥤ SchemesOverPresheaf B S hS Y) (cy : Cone Dy)
    (hc : IsLimit ((CostructuredArrow.proj yoneda Y.obj ⋙ BigFppfOver.toScheme B S hS).mapCone cy))

/-- The base changes of the stages along a morphism `Z ⟶ T_i`, as a diagram in the site whose
underlying schemes are the fibre products `T_j ×_{T_i} Z`. -/
def stageFibreProductDiagram (i : J) {Z : BigFppfOver B S hS} (gz : Z ⟶ (Dy.obj i).left) :
    Over i ⥤ BigFppfOver B S hS where
  obj j := stageObj B S hS (Dy.map j.hom).left gz
  map {j j'} a := stageMap B S hS (Dy.map j'.hom).left gz (Dy.map a.left).left (by
    rw [← CostructuredArrow.comp_left, ← Dy.map_comp, Over.w a])
  map_id j := by
    apply (isPullback_stage B S hS _ gz).hom_ext
    · simp only [stageMap_fst, Category.id_comp, Over.id_left, Dy.map_id]
      exact Category.comp_id _
    · simp
  map_comp {j j' j''} a a' := by
    apply (isPullback_stage B S hS _ gz).hom_ext
    · simp only [stageMap_fst, Category.assoc, stageMap_fst_assoc, Over.comp_left, Dy.map_comp,
        CostructuredArrow.comp_left]
    · simp

/-- The diagram of base changes, read in schemes, is the base changed system of
`AlgebraicGeometry.pullbackDiagram`. -/
def stageFibreProductDiagramIso (i : J) {Z : BigFppfOver B S hS} (gz : Z ⟶ (Dy.obj i).left) :
    stageFibreProductDiagram Dy i gz ⋙ BigFppfOver.toScheme B S hS ≅
      pullbackDiagram (Dy ⋙ CostructuredArrow.proj yoneda Y.obj ⋙ BigFppfOver.toScheme B S hS)
        i ((BigFppfOver.toScheme B S hS).map gz) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => by
    simp only [Iso.refl_hom]
    rfl)

/-- The diagram of fibre products of presheaves `T_j ×_{T_i} Z`. -/
def stageFibreProductPresheafDiagram (i : J) {Z : BigFppfOver B S hS}
    (gz : Z ⟶ (Dy.obj i).left) : Over i ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u where
  obj j := pullback (yoneda.map (Dy.map j.hom).left) (yoneda.map gz)
  map {j j'} a := pullback.lift (pullback.fst _ _ ≫ yoneda.map (Dy.map a.left).left)
    (pullback.snd _ _) (by
      rw [Category.assoc, ← Functor.map_comp, ← CostructuredArrow.comp_left, ← Dy.map_comp,
        Over.w a]
      exact pullback.condition)
  map_id j := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Over.id_left, Dy.map_id, CostructuredArrow.id_left]
      simp
    · rw [pullback.lift_snd, Category.id_comp]
  map_comp {j j' j''} a a' := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
        Over.comp_left, Dy.map_comp, CostructuredArrow.comp_left, Functor.map_comp]
      simp
    · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, pullback.lift_snd]

/-- The diagram of base changes, read in presheaves, is the diagram of fibre products of
presheaves. -/
def stageFibreProductDiagramYonedaIso (i : J) {Z : BigFppfOver B S hS}
    (gz : Z ⟶ (Dy.obj i).left) :
    stageFibreProductDiagram Dy i gz ⋙ yoneda ≅ stageFibreProductPresheafDiagram Dy i gz :=
  NatIso.ofComponents
    (fun j => (isPullback_yoneda_stage B S hS (Dy.map j.hom).left gz).isoPullback) (by
      intro j j' a
      apply pullback.hom_ext
      · dsimp only [Functor.comp_map, stageFibreProductDiagram, stageFibreProductPresheafDiagram]
        rw [Category.assoc, Category.assoc, IsPullback.isoPullback_hom_fst, pullback.lift_fst,
          IsPullback.isoPullback_hom_fst_assoc, ← Functor.map_comp, ← Functor.map_comp]
        exact congrArg yoneda.map (stageMap_fst B S hS _ gz _ _)
      · dsimp only [Functor.comp_map, stageFibreProductDiagram, stageFibreProductPresheafDiagram]
        rw [Category.assoc, Category.assoc, IsPullback.isoPullback_hom_snd, pullback.lift_snd,
          IsPullback.isoPullback_hom_snd, ← Functor.map_comp]
        exact congrArg yoneda.map (stageMap_snd B S hS _ gz _ _))

include hc in
/-- **The standing convention of Stacks 07SD holds for a system of affine schemes with limit in
the site.** -/
theorem siteContainsBaseChangeLimits_yoneda :
    SiteContainsBaseChangeLimits B S hS (Dy ⋙ CostructuredArrow.proj yoneda Y.obj ⋙ yoneda) := by
  intro i Z g W ι
  obtain ⟨gz, rfl⟩ := (yoneda : BigFppfOver B S hS ⥤ _).map_surjective g
  let F := BigFppfOver.toScheme B S hS
  let E := Dy ⋙ CostructuredArrow.proj yoneda Y.obj ⋙ F
  have e₁ : (W ⋙ BigAffineFppf.inclusion B S hS) ⋙ yoneda ≅
      stageFibreProductDiagram Dy i gz ⋙ yoneda :=
    Functor.associator _ _ _ ≪≫ (ι : _ ≅ stageFibreProductPresheafDiagram Dy i gz) ≪≫
      (stageFibreProductDiagramYonedaIso Dy i gz).symm
  have e₂ : W ⋙ BigAffineFppf.inclusion B S hS ≅ stageFibreProductDiagram Dy i gz :=
    (Yoneda.fullyFaithful.whiskeringRight _).preimageIso e₁
  have e₃ : underlyingDiagram (W ⋙ BigAffineFppf.inclusion B S hS) ≅
      pullbackDiagram E i (F.map gz) :=
    Functor.isoWhiskerRight e₂ F ≪≫ stageFibreProductDiagramIso Dy i gz
  intro c hc'
  let cS := (CostructuredArrow.proj yoneda Y.obj ⋙ F).mapCone cy
  have hlim := isLimitPullbackCone E cS hc i (F.map gz)
  have e₄ : c.pt ≅ (pullbackCone E cS i (F.map gz)).pt := IsLimit.conePointsIsoOfNatIso hc' hlim e₃
  change c.pt.size < B.cutoff
  rw [Scheme.size_congr e₄]
  exact Scheme.size_pullback_lt _ _ cy.pt.left.left.property Z.obj.left.property

end Convention

section Transfer

/-- A base-change-stable property of morphisms of algebraic spaces passes along a pullback square
of presheaves whose objects are algebraic spaces. -/
private theorem prop_of_isPullback_presheaf
    (P : ∀ ⦃F G : AlgebraicSpaces B S hS⦄, (F ⟶ G) → Prop)
    [MorphismProperty.IsStableUnderBaseChange P]
    {P₁ P₂ C₁ C₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hC₁ : IsAlgebraicSpace B S hS C₁) (hC₂ : IsAlgebraicSpace B S hS C₂)
    (hP₁ : IsAlgebraicSpace B S hS P₁) (hP₂ : IsAlgebraicSpace B S hS P₂)
    {a : P₂ ⟶ P₁} {f₂ : P₂ ⟶ C₂} {f₁ : P₁ ⟶ C₁} {ε : C₂ ⟶ C₁} (sq : IsPullback a f₂ f₁ ε)
    (h : P (ObjectProperty.homMk f₁ : (⟨P₁, hP₁⟩ : AlgebraicSpaces B S hS) ⟶ ⟨C₁, hC₁⟩)) :
    P (ObjectProperty.homMk f₂ : (⟨P₂, hP₂⟩ : AlgebraicSpaces B S hS) ⟶ ⟨C₂, hC₂⟩) := by
  have hpb : IsPullback
      (ObjectProperty.homMk a : (⟨P₂, hP₂⟩ : AlgebraicSpaces B S hS) ⟶ ⟨P₁, hP₁⟩)
      (ObjectProperty.homMk f₂ : (⟨P₂, hP₂⟩ : AlgebraicSpaces B S hS) ⟶ ⟨C₂, hC₂⟩)
      (ObjectProperty.homMk f₁ : (⟨P₁, hP₁⟩ : AlgebraicSpaces B S hS) ⟶ ⟨C₁, hC₁⟩)
      (ObjectProperty.homMk ε : (⟨C₂, hC₂⟩ : AlgebraicSpaces B S hS) ⟶ ⟨C₁, hC₁⟩) :=
    IsPullback.of_map_of_faithful
      (F := ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F)) sq
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb h

/-- **Transport of a base-change-stable property between two base changes of one morphism.**
If `f₁` and `f₂` are base changes of the same morphism `p` along `g₁` and `g₂`, and `g₂` factors
through `g₁`, then `f₂` is a base change of `f₁`, so it inherits every base-change-stable
property of morphisms of algebraic spaces that `f₁` has. -/
theorem prop_of_isPullback_of_factor
    (P : ∀ ⦃F G : AlgebraicSpaces B S hS⦄, (F ⟶ G) → Prop)
    [MorphismProperty.IsStableUnderBaseChange P]
    {A Bs C₁ C₂ P₁ P₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hC₁ : IsAlgebraicSpace B S hS C₁) (hC₂ : IsAlgebraicSpace B S hS C₂)
    (hP₁ : IsAlgebraicSpace B S hS P₁) (hP₂ : IsAlgebraicSpace B S hS P₂)
    {p : A ⟶ Bs} {g₁ : C₁ ⟶ Bs} {g₂ : C₂ ⟶ Bs} {f₁ : P₁ ⟶ C₁} {a₁ : P₁ ⟶ A} {f₂ : P₂ ⟶ C₂}
    {a₂ : P₂ ⟶ A} (sq₁ : IsPullback a₁ f₁ p g₁) (sq₂ : IsPullback a₂ f₂ p g₂) (ε : C₂ ⟶ C₁)
    (hε : ε ≫ g₁ = g₂)
    (h : P (ObjectProperty.homMk f₁ : (⟨P₁, hP₁⟩ : AlgebraicSpaces B S hS) ⟶ ⟨C₁, hC₁⟩)) :
    P (ObjectProperty.homMk f₂ : (⟨P₂, hP₂⟩ : AlgebraicSpaces B S hS) ⟶ ⟨C₂, hC₂⟩) := by
  have hw : a₂ ≫ p = (f₂ ≫ ε) ≫ g₁ := by rw [Category.assoc, hε, sq₂.w]
  have hleft : IsPullback (sq₁.lift a₂ (f₂ ≫ ε) hw) f₂ f₁ ε :=
    IsPullback.of_right (by rwa [sq₁.lift_fst, hε]) (sq₁.lift_snd _ _ _) sq₁
  exact prop_of_isPullback_presheaf P hC₁ hC₂ hP₁ hP₂ hleft h

/-- The inverse image of a subfunctor of a base change along a transition morphism, read as a
base change over the test schemes. -/
theorem isPullback_preimage_schemeBaseChangeMap {X : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {T T' : SchemesOverPresheaf B S hS Y} (g : T' ⟶ T) (W : Subfunctor (schemeBaseChange f T)) :
    IsPullback (W.fromPreimage (schemeBaseChangeMap f g))
      ((W.preimage (schemeBaseChangeMap f g)).ι ≫ pullback.snd f.hom T'.hom)
      (W.ι ≫ pullback.snd f.hom T.hom) (yoneda.map g.left) :=
  (Subfunctor.isPullback_preimage (schemeBaseChangeMap f g) W).paste_vert
    (isPullback_schemeBaseChangeMap f g)

end Transfer

section Proper

variable {X : AlgebraicSpaces B S hS} (f : X ⟶ Y) {Λ : Type u} [PartialOrder Λ]
    [IsDirected Λ (· ≤ ·)] [Nonempty Λ]
    (Dy : Λᵒᵖ ⥤ SchemesOverPresheaf B S hS Y) (cy : Cone Dy)
    (hc : IsLimit ((CostructuredArrow.proj yoneda Y.obj ⋙ BigFppfOver.toScheme B S hS).mapCone cy))
    (hD : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (Dy.obj j).left))
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj cy.pt.left))

include hc hD hT in
/-- **Properness at a stage (Stacks 08K1).** A closed subspace of `X_{T_l}` of finite presentation
over `T_l` whose inverse image in `X_T` is proper over `T` has an inverse image in `X_{T_i}`
proper over `T_i` for some `i ≥ l`. -/
theorem exists_isProper_preimage_stage (l : Λ)
    {W : Subfunctor (schemeBaseChange f (Dy.obj (op l)))} (hW : IsClosedSubspace B S hS W)
    (hWfp : IsFinitePresentation B S hS (W.ι ≫ pullback.snd f.hom (Dy.obj (op l)).hom))
    (hprop : IsProper B S hS ((W.preimage (schemeBaseChangeMap f (cy.π.app (op l)))).ι ≫
      pullback.snd f.hom cy.pt.hom)) :
    ∃ (i : Λ) (hi : l ≤ i), IsProper B S hS
      ((W.preimage (schemeBaseChangeMap f (Dy.map (homOfLE hi).op))).ι ≫
        pullback.snd f.hom (Dy.obj (op i)).hom) := by
  classical
  have hZ := BigFppfSite.contains_terminal B
  have : IsCofiltered Λᵒᵖ := inferInstance
  have : IsConnected Λᵒᵖ := IsCofiltered.isConnected _
  have hsite : IsLimit ((CostructuredArrow.proj yoneda Y.obj).mapCone cy) :=
    isLimitOfReflects (BigFppfOver.toScheme B S hS) hc
  have hyl : IsLimit (yoneda.mapCone ((CostructuredArrow.proj yoneda Y.obj).mapCone cy)) :=
    isLimitOfPreserves yoneda hsite
  let base : Λᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
    Dy ⋙ CostructuredArrow.proj yoneda Y.obj ⋙ yoneda
  let toT : limit base ⟶ yoneda.obj cy.pt.left := hyl.lift (limit.cone base)
  have htoT : ∀ j, toT ≫ yoneda.map (cy.π.app j).left = limit.π base j := fun j =>
    hyl.fac (limit.cone base) j
  have hlimIso : limit base ≅ yoneda.obj cy.pt.left :=
    (limit.isLimit base).conePointUniqueUpToIso hyl
  have hyaff : ∀ (V : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
      IsQuasiCompactSpace B S hS (yoneda.obj V) ∧
        IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj V) := fun V hV =>
    ⟨isQuasiCompactSpace_yoneda_of_isAffine B S hS V hV,
      have := hV
      isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B S hS (yoneda.obj V) hZ
        ⟨V, inferInstance, ⟨Functor.RepresentableBy.yoneda V⟩⟩⟩
  have hTl := hyaff _ (hD (op l))
  have hYl := isAlgebraicSpace_yoneda B S hS (Dy.obj (op l)).left
  have hWqc : IsQuasiCompactSpace B S hS W.toFunctor :=
    isQuasiCompactSpace_of_isFinitePresentation B S hS _ hYl hTl.1 hWfp
  have hWqs : IsAbsolutelyQuasiSeparated B S hS hZ W.toFunctor :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hW.1 hTl.2 hWfp.2.2
  let Dsit : MorphismDescentSituation B S hS hZ Λ :=
    { base := base
      base_isAlgebraicSpace := fun i => isAlgebraicSpace_yoneda B S hS _
      transition_affine := fun {i j} a => by
        have : IsAffine ((BigFppfOver.toScheme B S hS).obj
          ((CostructuredArrow.proj yoneda Y.obj).obj (Dy.obj i))) := hD i
        have : IsAffine ((BigFppfOver.toScheme B S hS).obj
          ((CostructuredArrow.proj yoneda Y.obj).obj (Dy.obj j))) := hD j
        exact isAffineHom_of_presheaf
          ((presheaf_yoneda_map_iff B S hS
              (P := @_root_.AlgebraicGeometry.IsAffineHom.{u}) inferInstance _).mpr
            (_root_.AlgebraicGeometry.isAffineHom_of_isAffine _))
      limit_isAlgebraicSpace :=
        (isAlgebraicSpace_yoneda B S hS _).of_iso hlimIso.symm
      initial := l
      source₀ := W.toFunctor
      target₀ := yoneda.obj (Dy.obj (op l)).left
      sourceToBase := W.ι ≫ pullback.snd f.hom (Dy.obj (op l)).hom
      targetToBase := 𝟙 _
      map₀ := W.ι ≫ pullback.snd f.hom (Dy.obj (op l)).hom
      map₀_over := Category.comp_id _
      source₀_isAlgebraicSpace := hW.1
      target₀_isAlgebraicSpace := hYl
      base₀_quasiCompact := hTl.1
      base₀_quasiSeparated := hTl.2
      source₀_quasiCompact := hWqc
      source₀_quasiSeparated := hWqs
      target₀_quasiCompact := hTl.1
      target₀_quasiSeparated := hTl.2 }
  have hconv : SiteContainsBaseChangeLimits B S hS Dsit.base :=
    siteContainsBaseChangeLimits_yoneda Dy cy hc
  have hP : ∀ {T' : SchemesOverPresheaf B S hS Y} (g : T' ⟶ Dy.obj (op l)),
      IsAlgebraicSpace B S hS (W.preimage (schemeBaseChangeMap f g)).toFunctor := fun g =>
    (isClosedSubspace_preimage B S hS _ _ (isAlgebraicSpace_schemeBaseChange f _)
      (isAlgebraicSpace_schemeBaseChange f _) hW).1
  have hprop' : IsProper B S hS Dsit.mapLimit := by
    have sq₂ : IsPullback (pullback.snd (limit.π base (op l)) Dsit.sourceToBase) Dsit.mapLimit
        Dsit.map₀ (pullback.snd (limit.π base (op l)) Dsit.targetToBase) := by
      refine IsPullback.of_bot ?_ (Dsit.mapLimit_snd).symm Dsit.targetLimit_isPullback.flip
      exact Dsit.sourceLimit_isPullback.flip.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (Iso.refl _) (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]; rfl)
        (by
          simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
          exact Dsit.mapLimit_fst.symm)
        (by
          simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
          rfl)
        (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
    refine prop_of_isPullback_of_factor
      (fun ⦃_ _ : AlgebraicSpaces B S hS⦄ k => IsProper B S hS k.hom)
      (isAlgebraicSpace_yoneda B S hS _) Dsit.targetLimit_isAlgebraicSpace (hP _)
      Dsit.sourceLimit_isAlgebraicSpace
      (isPullback_preimage_schemeBaseChangeMap f (cy.π.app (op l)) W) sq₂
      (pullback.fst (limit.π base (op l)) Dsit.targetToBase ≫ toT) ?_ hprop
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun t => pullback.fst _ _ ≫ t) (htoT (op l))).trans
        (pullback.condition.trans (Category.comp_id _)))
  obtain ⟨i, hi, hpi⟩ := Dsit.exists_isProper_mapAt_of_siteContainsBaseChangeLimits hconv hprop'
    (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hWfp.1)
  refine ⟨i, hi, ?_⟩
  have sq₁ : IsPullback (pullback.snd (Dsit.baseAtToInitial i hi) Dsit.sourceToBase)
      (Dsit.mapAt i hi) Dsit.map₀
      (pullback.snd (Dsit.baseAtToInitial i hi) Dsit.targetToBase) := by
    refine IsPullback.of_bot ?_ (Dsit.mapAt_snd i hi).symm (Dsit.targetAt_isPullback i hi).flip
    exact (Dsit.sourceAt_isPullback i hi).flip.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (Iso.refl _) (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
      (by
        simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
        exact (Dsit.mapAt_fst i hi).symm)
      (by
        simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
        rfl)
      (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
  exact prop_of_isPullback_of_factor
    (fun ⦃_ _ : AlgebraicSpaces B S hS⦄ k => IsProper B S hS k.hom)
    (Dsit.targetAt_isAlgebraicSpace i hi) (isAlgebraicSpace_yoneda B S hS _)
    (Dsit.sourceAt_isAlgebraicSpace i hi) (hP _) sq₁
    (isPullback_preimage_schemeBaseChangeMap f (Dy.map (homOfLE hi).op) W)
    (pullback.lift (𝟙 _) (yoneda.map (Dy.map (homOfLE hi).op).left)
      (by rw [Category.id_comp, Category.comp_id]; rfl))
    (pullback.lift_snd _ _ _) hpi

end Proper

section Families

variable {X : AlgebraicSpaces B S hS} (f : X ⟶ Y) {Λ : Type u} [PartialOrder Λ]
    [IsDirected Λ (· ≤ ·)] [Nonempty Λ]
    (Dy : Λᵒᵖ ⥤ SchemesOverPresheaf B S hS Y) (cy : Cone Dy)
    (hc : IsLimit ((CostructuredArrow.proj yoneda Y.obj ⋙ BigFppfOver.toScheme B S hS).mapCone cy))
    (hD : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (Dy.obj j).left))
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj cy.pt.left))

/-- A base-change-stable property of the structure morphism of a subfunctor of a base change
passes to its inverse image along a transition morphism. -/
theorem prop_preimage_schemeBaseChangeMap
    (P : ∀ ⦃F G : AlgebraicSpaces B S hS⦄, (F ⟶ G) → Prop)
    [MorphismProperty.IsStableUnderBaseChange P]
    {T T' : SchemesOverPresheaf B S hS Y} (g : T' ⟶ T) {W : Subfunctor (schemeBaseChange f T)}
    (hW : IsAlgebraicSpace B S hS W.toFunctor)
    (hW' : IsAlgebraicSpace B S hS (W.preimage (schemeBaseChangeMap f g)).toFunctor)
    (h : P (ObjectProperty.homMk (W.ι ≫ pullback.snd f.hom T.hom) :
      (⟨W.toFunctor, hW⟩ : AlgebraicSpaces B S hS) ⟶ schemeOverSpace T)) :
    P (ObjectProperty.homMk ((W.preimage (schemeBaseChangeMap f g)).ι ≫
        pullback.snd f.hom T'.hom) :
      (⟨(W.preimage (schemeBaseChangeMap f g)).toFunctor, hW'⟩ : AlgebraicSpaces B S hS) ⟶
        schemeOverSpace T') := by
  exact prop_of_isPullback_presheaf P _ _ hW hW' (isPullback_preimage_schemeBaseChangeMap f g W) h

include hc hD hT in
/-- **A family of the Hilbert functor over the limit comes from a stage.** -/
theorem exists_hilbertFamily_baseChange_eq (hfp : IsFinitePresentation B S hS f.hom)
    (hsep : IsSeparated B S hS f.hom) (z : HilbertFamily f cy.pt) :
    ∃ (j : Λᵒᵖ) (z' : HilbertFamily f (Dy.obj j)), z'.baseChange (cy.π.app j) = z := by
  obtain ⟨j, W, hW, hWfp, hWflat, hWz⟩ :=
    exists_closedSubspace_stage_of_hilbertFamily f Dy cy hc hD hfp hsep z
  have hprop : IsProper B S hS ((W.preimage (schemeBaseChangeMap f (cy.π.app (op j.unop)))).ι ≫
      pullback.snd f.hom cy.pt.hom) := by
    rw [hWz]; exact z.proper
  obtain ⟨i, hi, hpi⟩ := exists_isProper_preimage_stage f Dy cy hc hD hT j.unop hW hWfp hprop
  let e : op i ⟶ j := (homOfLE hi).op
  have hW' : IsClosedSubspace B S hS (W.preimage (schemeBaseChangeMap f (Dy.map e))) :=
    isClosedSubspace_preimage B S hS _ _ (isAlgebraicSpace_schemeBaseChange f _)
      (isAlgebraicSpace_schemeBaseChange f _) hW
  refine ⟨op i, ⟨W.preimage (schemeBaseChangeMap f (Dy.map e)), hW', ?_, ?_, hpi⟩, ?_⟩
  · exact prop_preimage_schemeBaseChangeMap f
      (fun ⦃_ _ : AlgebraicSpaces B S hS⦄ k => IsFinitePresentation B S hS k.hom) (Dy.map e)
      hW.1 hW'.1 hWfp
  · have := Space.isFlat_isStableUnderBaseChange B S hS
    exact prop_preimage_schemeBaseChangeMap f
      (fun ⦃_ _ : AlgebraicSpaces B S hS⦄ k => IsFlat B S hS k.hom) (Dy.map e) hW.1 hW'.1 hWflat
  · apply HilbertFamily.ext
    rwa [HilbertFamily.baseChange_Z, ← Subfunctor.preimage_comp, ← schemeBaseChangeMap_comp,
      cy.w e]

include hc hD in
/-- **Two families at a stage which agree over the limit agree at a later stage.** -/
theorem exists_hilbertFamily_baseChange_eq_of_eq (hfp : IsFinitePresentation B S hS f.hom)
    (hsep : IsSeparated B S hS f.hom) (i : Λᵒᵖ) (z z' : HilbertFamily f (Dy.obj i))
    (h : z.baseChange (cy.π.app i) = z'.baseChange (cy.π.app i)) :
    ∃ (j : Λᵒᵖ) (e : j ⟶ i), z.baseChange (Dy.map e) = z'.baseChange (Dy.map e) := by
  obtain ⟨j, e, he⟩ := exists_preimage_eq_of_preimage_eq_limit f Dy cy hc hD hfp hsep i
    z.closed z'.closed z.finitePresentation.1 z'.finitePresentation.1
    (congrArg HilbertFamily.Z h)
  exact ⟨j, e, HilbertFamily.ext he⟩

end Families

end AlgebraicGeometry.Space

end
