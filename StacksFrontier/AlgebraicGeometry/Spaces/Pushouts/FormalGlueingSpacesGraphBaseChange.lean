module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSituationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesAffineFull

/-!
# The slice step of Stacks 0AF6: clause (2) of Stacks 0AF4 read over a space over `X`

In a formal glueing situation `D = (f : Y ⟶ X, Z, U = X \ Z, V = Y \ f⁻¹(Z))`, write `F` for the
restriction functor of Stacks 0AF3. The proof of Stacks 0AF6 takes a morphism `φ : F X'₁ ⟶ F X'₂`,
forms the glueing datum of its three graphs over `Qq = X'₁ ×_X X'₂`, and applies Stacks 0AF4
part (2) — *to the base change of the situation along `Qq ⟶ X`* — to realise that datum as a
closed subspace of `Qq`. The graph criterion and the separation argument are
`StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesGraph`; their input is the
statement `AlgebraicGeometry.Space.FormalGlueingSituation.ClosedSliceRealization D`, the
closed-immersion construction in the slice over a space over `X`.

This module proves that input from clause (2) of Stacks 0AF4 for the base changes of the
situation, which is exactly how the source uses Stacks 0AF4.

## Main results

* `AlgebraicGeometry.Space.FormalGlueingSituation.exists_iso_restrictionDiagram_of_closedLegs`:
  the transport for any situation `D'` lying over `D` through cartesian squares on `Y`, `U` and
  `V`. A morphism `ψ : G ⟶ F(X')` with closed-immersion legs gives a glueing datum `G'` for `D'`
  with closed-immersion legs; clause (2) for `D'` realises `G'` by a closed subspace `T'` of `X'`;
  and the two restrictions of `T'`, read over `X`, are identified with the two components of `G`
  compatibly with `ψ`.
* `AlgebraicGeometry.Space.FormalGlueingSituation.exists_iso_formalGlueingFunctor_of_legs`: the
  two identifications assemble into an isomorphism of glueing data over `F Qq`.
* `AlgebraicGeometry.Space.FormalGlueingSituation.closedSliceRealization_of_essSurj`: the slice
  construction from essential surjectivity of clause (2) of Stacks 0AF4, applied to
  `AlgebraicGeometry.Space.FormalGlueingSituation.baseChangeAlong`.
* `AlgebraicGeometry.Space.FormalGlueingSituation.closedSliceRealization_of_essSurj_affine`: the
  same from essential surjectivity of clause (1) of Stacks 0AF4 alone.
* `AlgebraicGeometry.Space.FormalGlueingSituation.bijective_formalGlueingFunctor_map_of_essSurj`:
  the bijection of Stacks 0AF6 from the same input.

## Implementation notes

The results take the essential surjectivity of clause (2) of Stacks 0AF4 as a hypothesis; Stacks
0AF6 is registered, with that input proved, on
`AlgebraicGeometry.Space.FormalGlueingSituation.bijective_formalGlueingFunctor_map_of_isSeparated`
(`StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesSeparatedBijection`).

*The transported datum.* The legs of `G'` are `ℓU : G_U ⟶ U'` and `ℓY : G_Y ⟶ Y'`, the morphisms
into the fibre products `U' = U ×_X X'` and `Y' = Y ×_X X'` with components the structure maps of
`G` and the legs of `ψ` followed by the projections to `X'`. They are the legs of `ψ` followed by
the identifications `U ×_X X' ≅ U'` and `Y ×_X X' ≅ Y'`, hence closed immersions. Since
`V' = U' ×_U V = Y' ×_Y V`, the restrictions of `ℓU` and `ℓY` to `V'` are the restrictions of
`G_U` and `G_Y` to `V`, and the overlap isomorphism of `G'` is that of `G`, transported
(`AlgebraicGeometry.Space.FormalGlueingSituation.exists_isIso_overlap`). That it lies over `V'`
is checked on the two projections of `V' ⊆ Y' = Y ×_X X'`: over `Y` it is the overlap of `G`
lying over `V`, and over `X'` it is the compatibility of `ψ` over `V`, read on the projections to
`X'` (`AlgebraicGeometry.Space.FormalGlueingSituation.fst_comp_fst_eq_of_comm`), for which the
comparison of Stacks 0AF3 is computed on those projections
(`AlgebraicGeometry.Space.FormalGlueingSituation.restrictionComparison_hom_app_left_fst_fst`).

*Reading back.* Each leg is handled separately by
`AlgebraicGeometry.Space.FormalGlueingSituation.exists_overIso_of_leg`, which pastes the cartesian
square of `T'` over `U'` with that of `U'` over `U`. The compatibility over `V` of the resulting
pair is not computed: it holds after composing with the restriction to `V` of the right leg of
`ψ`, which is a monomorphism, a closed immersion being one
(`AlgebraicGeometry.Space.FormalGlueingSituation.exists_commaHom_of_comp_eq`).

*Elaboration.* The components of `ψ` are passed as separate morphisms typed by the pullback
functors rather than projected out of a morphism into `(restrictionDiagram D).obj _`, and the
components of the realising isomorphism are read through the abbreviations `glueingLeft` and
`glueingRight` and two `rfl` lemmas: unifying the two spellings of the same object inside one
large proof exhausted the heartbeat budget, while each identification checked in isolation is
immediate.

## References

* [Stacks Project, Tag 03KO](https://stacks.math.columbia.edu/tag/03KO)
* [Stacks Project, Tag 05VW](https://stacks.math.columbia.edu/tag/05VW)
* [Stacks Project, Tag 0AEV](https://stacks.math.columbia.edu/tag/0AEV)
* [Stacks Project, Tag 0AF3](https://stacks.math.columbia.edu/tag/0AF3)
* [Stacks Project, Tag 0AF4](https://stacks.math.columbia.edu/tag/0AF4)
* [Stacks Project, Tag 0AF5](https://stacks.math.columbia.edu/tag/0AF5)
* [Stacks Project, Tag 0AF6](https://stacks.math.columbia.edu/tag/0AF6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.FormalGlueingSituation

/-! ### Generalities -/

/-- The composite isomorphism `Over.pullbackComp f g`, followed by the two first projections, is
the first projection of the pullback along the composite. -/
theorem overPullbackComp_hom_app_left_fst_fst {C : Type*} [Category C] [HasPullbacks C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (A : Over Z) :
    ((Over.pullbackComp f g).hom.app A).left ≫ pullback.fst (pullback.snd A.hom g) f ≫
      pullback.fst A.hom g = pullback.fst A.hom (f ≫ g) := by
  simpa [Over.pullbackComp, Adjunction.comp_counit_app] using
    congrArg CommaMorphism.left (conjugateEquiv_counit (Over.mapPullbackAdj (f ≫ g))
      ((Over.mapPullbackAdj f).comp (Over.mapPullbackAdj g)) (Over.mapComp f g).inv A)

/-- The identification of the pullback functors along two equal morphisms is compatible with
the first projections. -/
theorem eqToHom_overPullback_app_left_fst {C : Type*} [Category C] [HasPullbacks C]
    {X Y : C} {u v : X ⟶ Y} (h : u = v) (A : Over Y) :
    ((eqToHom (congrArg (fun g : X ⟶ Y ↦ Over.pullback g) h)).app A).left ≫
      pullback.fst A.hom v = pullback.fst A.hom u := by
  subst h
  simp

/-- A morphism `θ` of a comma category into the source of `ψ` is determined by its two
components and its composite with `ψ`, as soon as `R` sends the right component of `ψ` to a
monomorphism: the compatibility of the components is then forced. -/
theorem exists_commaHom_of_comp_eq {A₀ B₀ T₀ : Type*} [Category A₀] [Category B₀] [Category T₀]
    {L : A₀ ⥤ T₀} {R : B₀ ⥤ T₀} {K G H : Comma L R} (ψ : G ⟶ H) (χ : K ⟶ H)
    (l : K.left ⟶ G.left) (r : K.right ⟶ G.right) (hl : l ≫ ψ.left = χ.left)
    (hr : r ≫ ψ.right = χ.right) [Mono (R.map ψ.right)] :
    ∃ θ : K ⟶ G, θ.left = l ∧ θ.right = r ∧ θ ≫ ψ = χ := by
  have hw : L.map l ≫ G.hom = K.hom ≫ R.map r := by
    refine (cancel_mono (R.map ψ.right)).1 ?_
    rw [Category.assoc, Category.assoc, ← ψ.w, ← R.map_comp, hr, ← Category.assoc,
      ← L.map_comp, hl]
    exact χ.w
  exact ⟨⟨l, r, hw⟩, rfl, rfl, Comma.hom_ext _ _ hl hr⟩

/-- The compatibility over the overlap of a pair `(ψl, ψr)` of morphisms into the two
restrictions of `A`, read on the projections to `A`: if a comparison `c` of the two restrictions
of `A` to `V` commutes with those projections, so does the morphism `Gh` that `(ψl, ψr)` is
compatible with. -/
theorem fst_comp_fst_eq_of_comm {C : Type*} [Category C] [HasPullbacks C] {X U V Y : C}
    {ι : U ⟶ X} {u : V ⟶ U} {f : Y ⟶ X} {j : V ⟶ Y} {A : Over X}
    (c : (Over.pullback u).obj ((Over.pullback ι).obj A) ⟶
      (Over.pullback j).obj ((Over.pullback f).obj A))
    (hc : c.left ≫ pullback.fst (pullback.snd A.hom f) j ≫ pullback.fst A.hom f =
      pullback.fst (pullback.snd A.hom ι) u ≫ pullback.fst A.hom ι)
    {P₁ : Over U} {P₂ : Over Y} (Gh : (Over.pullback u).obj P₁ ⟶ (Over.pullback j).obj P₂)
    (ψl : P₁ ⟶ (Over.pullback ι).obj A) (ψr : P₂ ⟶ (Over.pullback f).obj A)
    (hw : (Over.pullback u).map ψl ≫ c = Gh ≫ (Over.pullback j).map ψr) :
    pullback.fst P₁.hom u ≫ ψl.left ≫ pullback.fst A.hom ι =
      Gh.left ≫ pullback.fst P₂.hom j ≫ ψr.left ≫ pullback.fst A.hom f := by
  have h : ((Over.pullback u).map ψl).left ≫ c.left = Gh.left ≫ ((Over.pullback j).map ψr).left :=
    congrArg CommaMorphism.left hw
  have e₁ := overPullback_map_left_comp_fst u ψl
  have e₂ := overPullback_map_left_comp_fst j ψr
  simp only [Over.pullback_obj_hom] at e₁ e₂
  rw [← reassoc_of% e₁, ← hc, reassoc_of% h, reassoc_of% e₂]

/-- **One leg of the slice step.** Let `U' ⟶ X'` be the base change of `ι : U ⟶ X` along
`q : X' ⟶ X`, let `ψ : A ⟶ U ×_X X'` be a morphism over `U`, and let `ℓ : A ⟶ U'` be `A` read
over `U'` through `ψ`, i.e. the morphism with components `A ⟶ U` and `A ⟶ U ×_X X' ⟶ X'`. If a
space `T'` over `X'` restricts to `U'` as `(A, ℓ)`, then `T'`, read over `X`, restricts to `U`
as `A`, compatibly with `ψ` and with the restriction of `T' ⟶ X'`. -/
theorem exists_overIso_of_leg {C : Type*} [Category C] [HasPullbacks C] {X X' U U' : C}
    {ι : U ⟶ X} {ι' : U' ⟶ X'} {gU : U' ⟶ U} {q : X' ⟶ X} (sq : IsPullback gU ι' ι q)
    {A : Over U} (ψ : A ⟶ (Over.pullback ι).obj (Over.mk q)) (ℓ : A.left ⟶ U')
    (hℓ₁ : ℓ ≫ gU = A.hom) (hℓ₂ : ℓ ≫ ι' = ψ.left ≫ pullback.fst (Over.mk q).hom ι)
    (T' : Over X') (ε : (Over.pullback ι').obj T' ≅ Over.mk ℓ) :
    ∃ θ : (Over.pullback ι).obj (Over.mk (T'.hom ≫ q)) ≅ A,
      θ.hom ≫ ψ = (Over.pullback ι).map
        (Over.homMk T'.hom rfl : Over.mk (T'.hom ≫ q) ⟶ Over.mk q) := by
  have hψ : ψ.left ≫ pullback.snd (Over.mk q).hom ι = A.hom := Over.w ψ
  have hε : ε.hom.left ≫ ℓ = pullback.snd T'.hom ι' := Over.w ε.hom
  have hP : IsPullback (pullback.fst T'.hom ι') (pullback.snd T'.hom ι' ≫ gU)
      (Over.mk (T'.hom ≫ q)).hom ι := (IsPullback.of_hasPullback T'.hom ι').paste_vert sq.flip
  have hc₁ : hP.isoPullback.inv ≫ pullback.fst T'.hom ι' =
      pullback.fst (Over.mk (T'.hom ≫ q)).hom ι := hP.isoPullback_inv_fst
  have hc₂ : hP.isoPullback.inv ≫ pullback.snd T'.hom ι' ≫ gU =
      pullback.snd (Over.mk (T'.hom ≫ q)).hom ι := hP.isoPullback_inv_snd
  have hw : hP.isoPullback.inv ≫ ε.hom.left ≫ A.hom =
      pullback.snd (Over.mk (T'.hom ≫ q)).hom ι := by
    rw [← hℓ₁, reassoc_of% hε, hc₂]
  refine ⟨Over.isoMk (hP.isoPullback.symm ≪≫ (Over.forget _).mapIso ε) ?_, ?_⟩
  · simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Over.forget_map, Category.assoc]
    exact hw
  · refine Over.OverMorphism.ext ?_
    have hk₁ : ((Over.pullback ι).map
        (Over.homMk T'.hom rfl : Over.mk (T'.hom ≫ q) ⟶ Over.mk q)).left ≫
          pullback.fst (Over.mk q).hom ι = pullback.fst (Over.mk (T'.hom ≫ q)).hom ι ≫ T'.hom :=
      overPullback_map_left_comp_fst ι _
    have hk₂ : ((Over.pullback ι).map
        (Over.homMk T'.hom rfl : Over.mk (T'.hom ≫ q) ⟶ Over.mk q)).left ≫
          pullback.snd (Over.mk q).hom ι = pullback.snd (Over.mk (T'.hom ≫ q)).hom ι :=
      overPullback_map_left_comp_snd ι _
    simp only [Over.comp_left, Over.isoMk_hom_left, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, Over.forget_map, Category.assoc]
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc]
      rw [hk₁, ← hℓ₂, reassoc_of% hε, ← pullback.condition, reassoc_of% hc₁]
    · simp only [Category.assoc]
      rw [hk₂, hψ, hw]

/-- A morphism into the base change `U'` of `ι` along `q` is the composite of its components into
the fibre product `X' ×_X U` with an isomorphism. -/
theorem exists_isIso_eq_comp_of_isPullback {C : Type*} [Category C] [HasPullbacks C]
    {X X' U U' A : C} {ι : U ⟶ X} {ι' : U' ⟶ X'} {gU : U' ⟶ U} {q : X' ⟶ X}
    (sq : IsPullback gU ι' ι q) (ℓ : A ⟶ U') (m : A ⟶ pullback q ι)
    (h₁ : ℓ ≫ gU = m ≫ pullback.snd q ι) (h₂ : ℓ ≫ ι' = m ≫ pullback.fst q ι) :
    ∃ e : pullback q ι ⟶ U', IsIso e ∧ ℓ = m ≫ e :=
  ⟨sq.flip.isoPullback.inv, inferInstance, sq.hom_ext
    (by rw [h₁, Category.assoc, sq.flip.isoPullback_inv_snd])
    (by rw [h₂, Category.assoc, sq.flip.isoPullback_inv_fst])⟩

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The comparison `restrictionComparison D` commutes with the projections to the space being
restricted. -/
theorem restrictionComparison_hom_app_left_fst_fst (D : FormalGlueingSituation B S hS)
    (A : Over D.X) :
    ((restrictionComparison D).hom.app A).left ≫
        pullback.fst (pullback.snd A.hom D.f) D.V.ι ≫ pullback.fst A.hom D.f =
      pullback.fst (pullback.snd A.hom D.U.ι) (D.U.fromPreimage D.f) ≫
        pullback.fst A.hom D.U.ι := by
  simp only [restrictionComparison, Iso.trans_hom, Iso.symm_hom, eqToIso.hom,
    NatTrans.comp_app, Over.comp_left, Category.assoc]
  rw [overPullbackComp_hom_app_left_fst_fst D.V.ι D.f A,
    eqToHom_overPullback_app_left_fst (Subfunctor.fromPreimage_ι D.U D.f) A,
    ← overPullbackComp_hom_app_left_fst_fst (D.U.fromPreimage D.f) D.U.ι A,
    ← Over.comp_left_assoc, ← NatTrans.comp_app, Iso.inv_hom_id, NatTrans.id_app,
    Over.id_left, Category.id_comp]

/-- The `U`-component of a glueing triple. -/
noncomputable abbrev glueingLeft (D : FormalGlueingSituation B S hS) :
    glueingData D ⥤ Over D.U.toFunctor :=
  ObjectProperty.ι _ ⋙ Comma.fst _ _

/-- The `Y`-component of a glueing triple. -/
noncomputable abbrev glueingRight (D : FormalGlueingSituation B S hS) : glueingData D ⥤ Over D.Y :=
  ObjectProperty.ι _ ⋙ Comma.snd _ _

/-- The `U`-component of the image of a closed subspace under the restriction of Stacks 0AF4
part (2) is its base change to `U`. -/
theorem glueingLeft_obj_closedGlueingFunctor (D : FormalGlueingSituation B S hS)
    (T : (closedOverX D).FullSubcategory) :
    (glueingLeft D).obj ((closedLegs D).ι.obj ((closedGlueingFunctor D).obj T)) =
      (Over.pullback D.U.ι).obj T.obj.obj :=
  rfl

/-- The `Y`-component of the image of a closed subspace under the restriction of Stacks 0AF4
part (2) is its base change to `Y`. -/
theorem glueingRight_obj_closedGlueingFunctor (D : FormalGlueingSituation B S hS)
    (T : (closedOverX D).FullSubcategory) :
    (glueingRight D).obj ((closedLegs D).ι.obj ((closedGlueingFunctor D).obj T)) =
      (Over.pullback D.f).obj T.obj.obj :=
  rfl

/-- **The overlap of the slice step.** In the situation of
`exists_iso_restrictionDiagram_of_closedLegs`, the two legs `ℓU : G_U ⟶ U'` and `ℓY : G_Y ⟶ Y'`
of `G` read over `D'` have isomorphic restrictions to `V'`: both are identified with the
restrictions of `G_U` and `G_Y` to `V`, which `G` identifies, and the identification is over
`V'` because its composite with `V' ⟶ Y' ⟶ X'` is the compatibility of `ψ` over `V`, read on
the projections to `X'`. -/
theorem exists_isIso_overlap (D D' : FormalGlueingSituation B S hS) {q : D'.X ⟶ D.X}
    {gY : D'.Y ⟶ D.Y} {gU : D'.U.toFunctor ⟶ D.U.toFunctor}
    {gV : D'.V.toFunctor ⟶ D.V.toFunctor}
    (hYsq : IsPullback gY D'.f D.f q) (hUsq : IsPullback gU D'.U.ι D.U.ι q)
    (hVsq : IsPullback gV D'.V.ι D.V.ι gY)
    (hW : D'.U.fromPreimage D'.f ≫ gU = gV ≫ D.U.fromPreimage D.f) (G : glueingData D)
    (ψl : G.obj.left ⟶ (Over.pullback D.U.ι).obj (Over.mk q))
    (ψr : G.obj.right ⟶ (Over.pullback D.f).obj (Over.mk q))
    (hψw : (Over.pullback (D.U.fromPreimage D.f)).map ψl ≫
      (restrictionComparison D).hom.app (Over.mk q) =
        G.obj.hom ≫ (Over.pullback D.V.ι).map ψr)
    (ℓU : G.obj.left.left ⟶ D'.U.toFunctor) (hℓUg : ℓU ≫ gU = G.obj.left.hom)
    (hℓUι : ℓU ≫ D'.U.ι = ψl.left ≫ pullback.fst (Over.mk q).hom D.U.ι)
    (ℓY : G.obj.right.left ⟶ D'.Y) (hℓYg : ℓY ≫ gY = G.obj.right.hom)
    (hℓYf : ℓY ≫ D'.f = ψr.left ≫ pullback.fst (Over.mk q).hom D.f) :
    ∃ h : (Over.pullback (D'.U.fromPreimage D'.f)).obj (Over.mk ℓU) ⟶
      (Over.pullback D'.V.ι).obj (Over.mk ℓY), IsIso h := by
  -- the overlap square `V' = U' ×_U V`
  have hWsq : IsPullback (D'.U.fromPreimage D'.f) gV gU (D.U.fromPreimage D.f) := by
    refine IsPullback.of_right ?_ hW hUsq.flip
    rw [Subfunctor.fromPreimage_ι, Subfunctor.fromPreimage_ι]
    exact hVsq.flip.paste_horiz hYsq.flip
  have big₁ : IsPullback (pullback.fst ℓU (D'.U.fromPreimage D'.f))
      (pullback.snd ℓU (D'.U.fromPreimage D'.f) ≫ gV) G.obj.left.hom
      (D.U.fromPreimage D.f) := by
    have h := (IsPullback.of_hasPullback ℓU (D'.U.fromPreimage D'.f)).paste_vert hWsq
    rwa [hℓUg] at h
  have big₂ : IsPullback (pullback.fst ℓY D'.V.ι) (pullback.snd ℓY D'.V.ι ≫ gV)
      G.obj.right.hom D.V.ι := by
    have h := (IsPullback.of_hasPullback ℓY D'.V.ι).paste_vert hVsq.flip
    rwa [hℓYg] at h
  have hGV : G.obj.hom.left ≫ pullback.snd G.obj.right.hom D.V.ι =
      pullback.snd G.obj.left.hom (D.U.fromPreimage D.f) := by
    simpa using Over.w G.obj.hom
  have hkey := fst_comp_fst_eq_of_comm ((restrictionComparison D).hom.app (Over.mk q))
    (restrictionComparison_hom_app_left_fst_fst D _) G.obj.hom ψl ψr hψw
  have : IsIso G.obj.hom := G.property.1
  have : IsIso G.obj.hom.left := Functor.map_isIso (Over.forget _) G.obj.hom
  obtain ⟨m, hmdef, hmiso⟩ : ∃ m : pullback ℓU (D'.U.fromPreimage D'.f) ⟶ pullback ℓY D'.V.ι,
      m = big₁.isoPullback.hom ≫ G.obj.hom.left ≫ big₂.isoPullback.inv ∧ IsIso m :=
    ⟨_, rfl, inferInstance⟩
  have hm : m ≫ pullback.snd ℓY D'.V.ι = pullback.snd ℓU (D'.U.fromPreimage D'.f) := by
    subst hmdef
    refine hVsq.hom_ext ?_ ?_
    · simp only [Category.assoc]
      rw [big₂.isoPullback_inv_snd, hGV, big₁.isoPullback_hom_snd]
    · have hb₂s : ∀ {Z} (h : D.V.toFunctor ⟶ Z), big₂.isoPullback.inv ≫
          pullback.snd ℓY D'.V.ι ≫ gV ≫ h = pullback.snd G.obj.right.hom D.V.ι ≫ h :=
        fun h ↦ by simpa only [Category.assoc] using big₂.isoPullback_inv_snd =≫ h
      have hb₁s : ∀ {Z} (h : D.V.toFunctor ⟶ Z), big₁.isoPullback.hom ≫
          pullback.snd G.obj.left.hom (D.U.fromPreimage D.f) ≫ h =
            pullback.snd ℓU (D'.U.fromPreimage D'.f) ≫ gV ≫ h :=
        fun h ↦ by simpa only [Category.assoc] using big₁.isoPullback_hom_snd =≫ h
      have hb₂f : ∀ {Z} (h : G.obj.right.left ⟶ Z), big₂.isoPullback.inv ≫
          pullback.fst ℓY D'.V.ι ≫ h = pullback.fst G.obj.right.hom D.V.ι ≫ h :=
        fun h ↦ by simpa only [Category.assoc] using big₂.isoPullback_inv_fst =≫ h
      have hb₁f : ∀ {Z} (h : G.obj.left.left ⟶ Z), big₁.isoPullback.hom ≫
          pullback.fst G.obj.left.hom (D.U.fromPreimage D.f) ≫ h =
            pullback.fst ℓU (D'.U.fromPreimage D'.f) ≫ h :=
        fun h ↦ by simpa only [Category.assoc] using big₁.isoPullback_hom_fst =≫ h
      refine hYsq.hom_ext ?_ ?_
      · simp only [Category.assoc]
        rw [← hVsq.w, hb₂s, reassoc_of% hGV, hb₁s]
      · simp only [Category.assoc]
        rw [← pullback.condition_assoc (f := ℓY), hℓYf, hb₂f, ← hkey, hb₁f,
          ← Subfunctor.fromPreimage_ι D'.U D'.f, ← pullback.condition_assoc (f := ℓU), hℓUι]
  exact ⟨Over.homMk m hm, (isIso_iff_of_reflects_iso _ (Over.forget _)).1 hmiso⟩

/-- A closed immersion into the fibre product `X' ×_X U` gives, by base change, a closed
immersion into `U'`, with the same components. -/
private theorem exists_closedImmersion_leg {X X' U U' A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {ι : U ⟶ X} {ι' : U' ⟶ X'} {gU : U' ⟶ U} {q : X' ⟶ X} (sq : IsPullback gU ι' ι q)
    (m : A ⟶ pullback q ι) (hm : IsClosedImmersion B S hS m) (a : A ⟶ U)
    (ha : m ≫ pullback.snd q ι = a) :
    ∃ ℓ : A ⟶ U', ℓ ≫ gU = a ∧ ℓ ≫ ι' = m ≫ pullback.fst q ι ∧ IsClosedImmersion B S hS ℓ := by
  have : (closedImmersionPresheaf B S hS).RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact ⟨m ≫ sq.flip.isoPullback.inv, by simp [← ha], by simp,
    ((closedImmersionPresheaf B S hS).cancel_right_of_respectsIso _ _).2 hm⟩

/-- **The slice step of Stacks 0AF6, for a cartesian morphism of situations.** Let `D'` be a
formal glueing situation lying over `D` along `q : X' ⟶ X` through cartesian squares on `Y`, `U`
and `V`, compatibly with the restrictions of the two morphisms glued along. If the restriction
of Stacks 0AF4 part (2) is essentially surjective for `D'`, then every morphism of glueing data
`ψ : G ⟶ F(X')` for `D` whose two components are closed immersions is, up to isomorphism, the
restriction of a space `T'` over `X'`, read over `X`.

The object of glueing data for `D'` fed to Stacks 0AF4 is `G` read over the restrictions of
`X'`: its two legs are those of `ψ` followed by the identifications `U ×_X X' ≅ U'` and
`Y ×_X X' ≅ Y'`, and its overlap isomorphism is that of `G`, transported along the
identifications of `G_U ×_{U'} V'` with `G_U ×_U V` and of `G_Y ×_{Y'} V'` with `G_Y ×_Y V`. -/
theorem exists_iso_restrictionDiagram_of_closedLegs
    (D D' : FormalGlueingSituation B S hS) {q : D'.X ⟶ D.X} {gY : D'.Y ⟶ D.Y}
    {gU : D'.U.toFunctor ⟶ D.U.toFunctor} {gV : D'.V.toFunctor ⟶ D.V.toFunctor}
    (hYsq : IsPullback gY D'.f D.f q) (hUsq : IsPullback gU D'.U.ι D.U.ι q)
    (hVsq : IsPullback gV D'.V.ι D.V.ι gY)
    (hW : D'.U.fromPreimage D'.f ≫ gU = gV ≫ D.U.fromPreimage D.f)
    (hess : (closedGlueingFunctor D').EssSurj) (G : glueingData D)
    (ψl : G.obj.left ⟶ (Over.pullback D.U.ι).obj (Over.mk q))
    (ψr : G.obj.right ⟶ (Over.pullback D.f).obj (Over.mk q))
    (hψw : (Over.pullback (D.U.fromPreimage D.f)).map ψl ≫
      (restrictionComparison D).hom.app (Over.mk q) =
        G.obj.hom ≫ (Over.pullback D.V.ι).map ψr)
    (hψlci : IsClosedImmersion B S hS ψl.left) (hψrci : IsClosedImmersion B S hS ψr.left) :
    ∃ (T' : Over D'.X) (_ : IsAlgebraicSpace B S hS T'.left)
      (θU : (Over.pullback D.U.ι).obj (Over.mk (T'.hom ≫ q)) ≅ G.obj.left)
      (θY : (Over.pullback D.f).obj (Over.mk (T'.hom ≫ q)) ≅ G.obj.right),
      θU.hom ≫ ψl = (Over.pullback D.U.ι).map
          (Over.homMk T'.hom rfl : Over.mk (T'.hom ≫ q) ⟶ Over.mk q) ∧
        θY.hom ≫ ψr = (Over.pullback D.f).map
          (Over.homMk T'.hom rfl : Over.mk (T'.hom ≫ q) ⟶ Over.mk q) := by
  -- the two legs of `G`, read over `D'`, kept opaque
  obtain ⟨ℓU, hℓUg, hℓUι, hℓUci⟩ := exists_closedImmersion_leg hUsq ψl.left hψlci _ (Over.w ψl)
  obtain ⟨ℓY, hℓYg, hℓYf, hℓYci⟩ := exists_closedImmersion_leg hYsq ψr.left hψrci _ (Over.w ψr)
  obtain ⟨h, hiso⟩ := exists_isIso_overlap D D' hYsq hUsq hVsq hW G ψl ψr hψw ℓU hℓUg hℓUι
    ℓY hℓYg hℓYf
  -- the transported object, with its legs closed immersions
  obtain ⟨T', ⟨e⟩⟩ := hess.mem_essImage
    ⟨⟨⟨Over.mk ℓU, Over.mk ℓY, h⟩, ⟨hiso, G.property.2.1, G.property.2.2⟩⟩,
      ⟨hℓUci,
        isClosedImmersion_presheaf_of_isPullback
          (IsPullback.of_hasPullback ℓU (D'.U.fromPreimage D'.f)) hℓUci,
        hℓYci⟩⟩
  have e₁ := (closedLegs D').ι.mapIso e
  have εU' : (glueingLeft D').obj ((closedLegs D').ι.obj ((closedGlueingFunctor D').obj T')) ≅
      Over.mk ℓU := (glueingLeft D').mapIso e₁
  have εY' : (glueingRight D').obj ((closedLegs D').ι.obj ((closedGlueingFunctor D').obj T')) ≅
      Over.mk ℓY := (glueingRight D').mapIso e₁
  have εU := eqToIso (glueingLeft_obj_closedGlueingFunctor D' T').symm ≪≫ εU'
  have εY := eqToIso (glueingRight_obj_closedGlueingFunctor D' T').symm ≪≫ εY'
  -- read back over `X`, leg by leg
  obtain ⟨θU, hθU⟩ := exists_overIso_of_leg hUsq ψl ℓU hℓUg hℓUι T'.obj.obj εU
  obtain ⟨θY, hθY⟩ := exists_overIso_of_leg hYsq ψr ℓY hℓYg hℓYf T'.obj.obj εY
  exact ⟨T'.obj.obj, T'.obj.property, θU, θY, hθU, hθY⟩

/-- **Assembling the slice step in the category of glueing data.** If the two restrictions of a
space `T'` over `Qq`, read over `X`, are identified with the two components of `G` compatibly
with `ψ`, and the right component of `ψ` is a monomorphism, then the identifications form an
isomorphism of glueing data `F T ≅ G` over `F Qq`: their compatibility over `V` is forced, as it
holds after the monomorphism `(ψ_Y)|_V`. -/
theorem exists_iso_formalGlueingFunctor_of_legs (D : FormalGlueingSituation B S hS)
    {Qq : spacesOverX D} {G : glueingData D} (ψ : G ⟶ (formalGlueingFunctor D).1.obj Qq)
    [Mono ψ.hom.right.left] (T' : Over Qq.obj.left) (hT' : IsAlgebraicSpace B S hS T'.left)
    (θU : (Over.pullback D.U.ι).obj (Over.mk (T'.hom ≫ Qq.obj.hom)) ≅ G.obj.left)
    (θY : (Over.pullback D.f).obj (Over.mk (T'.hom ≫ Qq.obj.hom)) ≅ G.obj.right)
    (hθU : θU.hom ≫ ψ.hom.left = (Over.pullback D.U.ι).map
      (Over.homMk T'.hom rfl : Over.mk (T'.hom ≫ Qq.obj.hom) ⟶ Qq.obj))
    (hθY : θY.hom ≫ ψ.hom.right = (Over.pullback D.f).map
      (Over.homMk T'.hom rfl : Over.mk (T'.hom ≫ Qq.obj.hom) ⟶ Qq.obj)) :
    ∃ (T : spacesOverX D) (k : T ⟶ Qq) (θ : (formalGlueingFunctor D).1.obj T ≅ G),
      θ.hom ≫ ψ = (formalGlueingFunctor D).1.map k := by
  have : Mono ψ.hom.right := Over.mono_of_mono_left _
  let T : spacesOverX D := ⟨Over.mk (T'.hom ≫ Qq.obj.hom), hT'⟩
  let k : T ⟶ Qq := ObjectProperty.homMk (Over.homMk T'.hom rfl)
  obtain ⟨θ, hθl, hθr, hθ⟩ := exists_commaHom_of_comp_eq ψ.hom
    ((formalGlueingFunctor D).1.map k).hom θU.hom θY.hom hθU hθY
  have hw := θ.w
  rw [hθl, hθr] at hw
  refine ⟨T, k, ObjectProperty.isoMk _ (Comma.isoMk θU θY hw), ObjectProperty.hom_ext _ ?_⟩
  rw [← hθ]
  exact congrArg (· ≫ ψ.hom) (Comma.hom_ext _ _ hθl.symm hθr.symm)

/-- **The closed-immersion construction in the slice over a space, from clause (2) of
Stacks 0AF4 for the base changes of the situation.** If the restriction of Stacks 0AF4 part (2)
is essentially surjective for every formal glueing situation, then a morphism of glueing data
`ψ : G ⟶ F Qq` into the restriction of a space `Qq` over `X`, whose two legs are closed
immersions, is the restriction of a morphism `T ⟶ Qq` of spaces over `X`.

This is the step of the proof of Stacks 0AF6 reading "these graphs fit together to give an
object of `Spaces(Y ×_X Qq → Qq, Z ×_X Qq)` whose triple of morphisms are closed immersions":
clause (2) is applied to the base change of the situation along `Qq ⟶ X`,
`AlgebraicGeometry.Space.FormalGlueingSituation.baseChangeAlong`, which needs no flatness of
`Qq ⟶ X` — the flatness of the base change along the inverse image of its closed part is
Stacks 05VW applied to the structure sheaf. -/
theorem closedSliceRealization_of_essSurj (D : FormalGlueingSituation B S hS)
    (hess : ∀ D' : FormalGlueingSituation B S hS, (closedGlueingFunctor D').EssSurj) :
    ClosedSliceRealization D := by
  intro Qq G ψ hl hr
  have hU := baseChangeAlong_U_eq D Qq.property Qq.obj.hom
  have hV := baseChangeAlong_V_eq D Qq.property Qq.obj.hom
  have hYsq := IsPullback.of_hasPullback D.f Qq.obj.hom
  obtain ⟨T', hT', θU, θY, hθU, hθY⟩ :=
    exists_iso_restrictionDiagram_of_closedLegs D (D.baseChangeAlong Qq.property Qq.obj.hom)
      hYsq (Subfunctor.isPullback_mapOfEqPreimage D.U Qq.obj.hom hU)
      (Subfunctor.isPullback_mapOfEqPreimage D.V (pullback.fst D.f Qq.obj.hom) hV)
      (Subfunctor.mapOfEqPreimage_comm D.U hYsq hU hV)
      (hess _) G ψ.hom.left ψ.hom.right ψ.hom.w hl hr
  have : Mono ψ.hom.right.left := mono_of_isClosedImmersion B S hS _ hr
  exact exists_iso_formalGlueingFunctor_of_legs D ψ T' hT' θU θY hθU hθY

/-- The slice construction from essential surjectivity in clause (1) of Stacks 0AF4 alone, for
every situation: clause (1) gives clause (2) for each base change
(`AlgebraicGeometry.Space.FormalGlueingSituation.essSurj_closedGlueingFunctor`, through
Stacks 0420), and clause (2) for the base changes gives the slice construction. With
`AlgebraicGeometry.Space.FormalGlueingSituation.isEquivalence_closedGlueingFunctor_of_realization`
and its companions this reduces all of Stacks 0AF4 to that essential surjectivity. -/
theorem closedSliceRealization_of_essSurj_affine (D : FormalGlueingSituation B S hS)
    (hes : ∀ D' : FormalGlueingSituation B S hS, (affineGlueingFunctor D').EssSurj) :
    ClosedSliceRealization D :=
  closedSliceRealization_of_essSurj D fun D' ↦ essSurj_closedGlueingFunctor D' (hes D')

/-- **The bijection of Stacks 0AF6 from clause (2) of Stacks 0AF4.** For `X'₂ ⟶ X` separated,
the restriction functor of Stacks 0AF3 induces a bijection `Mor_X(X'₁, X'₂) ⟶ Mor(F X'₁, F X'₂)`,
granted that the restriction of Stacks 0AF4 part (2) is essentially surjective for every formal
glueing situation — the source applies it to the base change of the situation along
`X'₁ ×_X X'₂ ⟶ X`. -/
theorem bijective_formalGlueingFunctor_map_of_essSurj (D : FormalGlueingSituation B S hS)
    (hess : ∀ D' : FormalGlueingSituation B S hS, (closedGlueingFunctor D').EssSurj)
    {X₁ X₂ : spacesOverX D} (hsep : IsSeparated B S hS X₂.obj.hom) :
    Function.Bijective fun a : X₁ ⟶ X₂ ↦ (formalGlueingFunctor D).1.map a :=
  bijective_formalGlueingFunctor_map_of_essSurj_closedImmersion D hsep
    (closedSliceRealization_of_essSurj D hess)

end AlgebraicGeometry.Space.FormalGlueingSituation

end
