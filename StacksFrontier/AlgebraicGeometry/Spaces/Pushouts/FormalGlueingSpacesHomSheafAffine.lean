module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesHomSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocusRelative

/-!
# The sheaf of glueing-data morphisms into the triple of a space

In a formal glueing situation write `Φ` for the restriction to the glueing triple
(`AlgebraicGeometry.Space.FormalGlueingSituation.restrictionDiagram`) and
`AlgebraicGeometry.Space.FormalGlueingSituation.homPresheaf D G` for the sheaf
`W ↦ {(w, φ : Φ(W, w) ⟶ G)}`. For a space `T'` over `X` there is a canonical morphism
`T' ⟶ homPresheaf D (F T')`, `t ↦ (t ≫ T'.hom, Φ(t))`. This module proves it is an isomorphism as
soon as the restriction functor `F` of Stacks 0AF3 is full on morphisms from affine schemes to
`T'`, and records the local criterion it rests on: a morphism of sheaves on the big fppf site
which is bijective on affine objects is an isomorphism.

## Main definitions

* `AlgebraicGeometry.Space.FormalGlueingSituation.toHomPresheaf`: the canonical morphism.

## Main results

* `AlgebraicGeometry.Space.isIso_of_bijective_app_of_isAffine`: a morphism of fppf sheaves
  bijective on every object with affine underlying scheme is an isomorphism.
* `AlgebraicGeometry.Space.FormalGlueingSituation.isIso_toHomPresheaf`: the canonical morphism is
  an isomorphism when `F` is full on morphisms out of affine schemes.

## References

* [Stacks Project, Tag 0AF4](https://stacks.math.columbia.edu/tag/0AF4)
* [Stacks Project, Tag 0AF6](https://stacks.math.columbia.edu/tag/0AF6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Every object of the big fppf site is covered, in its topology, by the affine opens of its
underlying scheme. -/
theorem exists_affineOpens_mem_topology (V : BigFppfOver B S hS) :
    ∃ (I : Type u) (Vi : I → BigFppfOver B S hS) (ui : ∀ i, Vi i ⟶ V),
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (Vi i))) ∧
        Sieve.ofArrows Vi ui ∈ BigFppfOver.topology B S hS V := by
  choose Vi ui hu hrange hVaff using fun U => BigFppfOver.exists_affineOpen_restrict B S hS V U
  refine ⟨_, Vi, ui, hVaff, ?_⟩
  change Sieve.ofArrows Vi ui ∈ B.topology.over (B.obj hS) V
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  apply Precoverage.generate_mem_toGrothendieck
  rw [bigFppfPrecoverage_eq_comap, Precoverage.mem_comap_iff, Presieve.map_ofArrows]
  refine (Scheme.ofArrows_mem_precoverage_iff _).mpr ⟨fun y => ?_, fun U => ?_⟩
  swap
  · have : _root_.AlgebraicGeometry.IsOpenImmersion (B.inclusion.map (ui U).left) := hu U
    exact ⟨inferInstance, inferInstance⟩
  have hy : y ∈ (⊤ : ((BigFppfOver.toScheme B S hS).obj V).Opens) := trivial
  rw [← iSup_affineOpens_eq_top] at hy
  obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  refine ⟨U, ?_⟩
  change y ∈ Set.range ((BigFppfOver.toScheme B S hS).map (ui U))
  rwa [hrange U]

/-- A morphism of sheaves on the big fppf site which is bijective on every object with affine
underlying scheme is an isomorphism. -/
theorem isIso_of_bijective_app_of_isAffine {A A' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hA : Presheaf.IsSheaf (BigFppfOver.topology B S hS) A)
    (hA' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) A') (α : A ⟶ A')
    (h : ∀ V : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
      Function.Bijective (α.app (op V))) : IsIso α := by
  rw [isSheaf_iff_isSheaf_of_type] at hA hA'
  have inj : ∀ V : BigFppfOver B S hS, Function.Injective (α.app (op V)) := by
    intro V x y hxy
    obtain ⟨I, Vi, ui, haff, hmem⟩ := exists_affineOpens_mem_topology V
    refine ((Presieve.isSheafFor_iff_generate _).2 (hA _ hmem)).isSeparatedFor.ext ?_
    rintro _ _ ⟨i⟩
    apply (h _ (haff i)).1
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hxy]
  have surj : ∀ V : BigFppfOver B S hS, Function.Surjective (α.app (op V)) := by
    intro V y
    obtain ⟨I, Vi, ui, haff, hmem⟩ := exists_affineOpens_mem_topology V
    let x : ∀ i, A.obj (op (Vi i)) := fun i =>
      Function.surjInv (h _ (haff i)).2 (A'.map (ui i).op y)
    have hx : ∀ i, α.app _ (x i) = A'.map (ui i).op y := fun i =>
      Function.surjInv_eq (h _ (haff i)).2 _
    obtain ⟨t, ht, -⟩ := (Presieve.isSheafFor_arrows_iff _ _).1
      ((Presieve.isSheafFor_iff_generate _).2 (hA _ hmem)) x (by
      intro i j Z gi gj hij
      apply inj
      rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hx, hx,
        ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
        hij])
    refine ⟨t, ((Presieve.isSheafFor_iff_generate _).2 (hA' _ hmem)).isSeparatedFor.ext ?_⟩
    rintro _ _ ⟨i⟩
    rw [← NatTrans.naturality_apply, ht i, hx]
  have : ∀ V, IsIso (α.app V) := fun V =>
    (isIso_iff_bijective _).2 ⟨inj V.unop, surj V.unop⟩
  exact NatIso.isIso_of_isIso_app α

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.FormalGlueingSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable (D : FormalGlueingSituation B S hS)

/-- The pair attached to a section `t` of a space `T` over `X`: the composite `t ≫ T.hom`
and the restriction of `t`. -/
noncomputable def glueSectionsOfSpace (T : spacesOverX D) {W : BigFppfOver B S hS}
    (t : yoneda.obj W ⟶ T.obj.left) : glueSections D ((formalGlueingFunctor D).1.obj T) W :=
  ⟨t ≫ T.obj.hom, (restrictionDiagram D).map (Over.homMk t : Over.mk (t ≫ T.obj.hom) ⟶ T.obj)⟩

/-- Restricting the pair attached to `t` along `g : W' ⟶ W` gives the pair attached to the
composite `yoneda.map g ≫ t`. -/
theorem glueSectionsOfSpace_restrict (T : spacesOverX D) {W W' : BigFppfOver B S hS}
    (g : W' ⟶ W) (t : yoneda.obj W ⟶ T.obj.left) :
    (glueSectionsOfSpace D T t).restrict g = glueSectionsOfSpace D T (yoneda.map g ≫ t) := by
  refine glueSections.ext' (Category.assoc _ _ _).symm ?_
  dsimp only [glueSectionsOfSpace, glueSections.restrict]
  refine (CategoryTheory.Functor.map_comp _ _ _).symm.trans
    ((congrArg (restrictionDiagram D).map ?_).trans (CategoryTheory.Functor.map_comp _ _ _))
  refine Over.OverMorphism.ext ?_
  simp only [Over.mk_left, Over.comp_left, Over.homMk_left, Category.id_comp]
  rfl

/-- **The canonical morphism from a space over `X` to the sheaf of glueing-data morphisms into
its triple**, `t ↦ (t ≫ T.hom, Φ(t))`. -/
noncomputable def toHomPresheaf (T : spacesOverX D) :
    T.obj.left ⟶ homPresheaf D ((formalGlueingFunctor D).1.obj T) where
  app W := ↾fun t => equivShrink _ (glueSectionsOfSpace D T (yonedaEquiv.symm t))
  naturality W W' g := by
    refine ConcreteCategory.hom_ext _ _ fun t => ?_
    change equivShrink _ (glueSectionsOfSpace D T (yonedaEquiv.symm (T.obj.left.map g t))) =
      equivShrink _ (((equivShrink _).symm
        (equivShrink _ (glueSectionsOfSpace D T (yonedaEquiv.symm t)))).restrict g.unop)
    rw [Equiv.symm_apply_apply, glueSectionsOfSpace_restrict, yonedaEquiv_symm_naturality_left]
    rfl

/-- Two equal pairs have second components related by the identification of their sources. -/
theorem glueSections.snd_eq_of_eq {G : glueingData D} {W : BigFppfOver B S hS}
    {s s' : glueSections D G W} (h : s = s') :
    s.2 = (restrictionDiagram D).map (Over.homMk (𝟙 _)
      (by rw [congrArg Sigma.fst h, Category.id_comp]) : Over.mk s.1 ⟶ Over.mk s'.1) ≫ s'.2 := by
  subst h
  rw [show (Over.homMk (𝟙 _) (by rw [Category.id_comp]) : Over.mk s.1 ⟶ Over.mk s.1) = 𝟙 _ from
    Over.OverMorphism.ext rfl, CategoryTheory.Functor.map_id, Category.id_comp]

/-- Distinct sections of a space over `X` have distinct pairs. -/
theorem eq_of_glueSectionsOfSpace_eq (T : spacesOverX D) {W : BigFppfOver B S hS}
    {t t' : yoneda.obj W ⟶ T.obj.left}
    (h : glueSectionsOfSpace D T t = glueSectionsOfSpace D T t') : t = t' := by
  have hw : t ≫ T.obj.hom = t' ≫ T.obj.hom := congrArg Sigma.fst h
  have h2 : (restrictionDiagram D).map (Over.homMk t rfl : Over.mk (t ≫ T.obj.hom) ⟶ T.obj) =
      (restrictionDiagram D).map (Over.homMk (𝟙 _) (by rw [hw, Category.id_comp]) :
        Over.mk (t ≫ T.obj.hom) ⟶ Over.mk (t' ≫ T.obj.hom)) ≫
      (restrictionDiagram D).map (Over.homMk t' rfl : Over.mk (t' ≫ T.obj.hom) ⟶ T.obj) :=
    glueSections.snd_eq_of_eq D h
  let P : spacesOverX D := ⟨Over.mk (t ≫ T.obj.hom), isAlgebraicSpace_yoneda B S hS W⟩
  let a : P ⟶ T := ObjectProperty.homMk (Over.homMk t rfl : Over.mk (t ≫ T.obj.hom) ⟶ T.obj)
  let a' : P ⟶ T :=
    ObjectProperty.homMk (Over.homMk t' hw.symm : Over.mk (t ≫ T.obj.hom) ⟶ T.obj)
  have hF : (formalGlueingFunctor D).1.map a = (formalGlueingFunctor D).1.map a' := by
    refine ObjectProperty.hom_ext _ ?_
    change (restrictionDiagram D).map (Over.homMk t rfl : Over.mk (t ≫ T.obj.hom) ⟶ T.obj) =
      (restrictionDiagram D).map (Over.homMk t' hw.symm : Over.mk (t ≫ T.obj.hom) ⟶ T.obj)
    refine h2.trans ?_
    rw [← CategoryTheory.Functor.map_comp]
    exact congrArg (restrictionDiagram D).map (Over.OverMorphism.ext (by simp))
  exact congrArg (fun m : P ⟶ T => m.hom.left) ((formalGlueingFunctor D).1.map_injective hF)

/-- The canonical morphism `toHomPresheaf D T` is an isomorphism provided the restriction functor
`formalGlueingFunctor D` is full on morphisms from affine schemes over `X` to `T`. -/
theorem isIso_toHomPresheaf (T : spacesOverX D)
    (hfull : ∀ (V : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
      ∀ (w : yoneda.obj V ⟶ D.X)
        (φ : (formalGlueingFunctor D).1.obj ⟨Over.mk w, isAlgebraicSpace_yoneda B S hS V⟩ ⟶
          (formalGlueingFunctor D).1.obj T),
        ∃ a, (formalGlueingFunctor D).1.map a = φ) :
    IsIso (toHomPresheaf D T) := by
  refine isIso_of_bijective_app_of_isAffine T.property.isSheaf
    (isSheaf_homPresheaf D _) _ fun V hV => ⟨fun t t' htt' => ?_, fun s => ?_⟩
  · exact yonedaEquiv.symm.injective
      (eq_of_glueSectionsOfSpace_eq D T ((equivShrink _).injective htt'))
  · obtain ⟨⟨w, φ⟩, rfl⟩ := (equivShrink _).surjective s
    obtain ⟨a, ha⟩ := hfull V hV w (ObjectProperty.homMk φ)
    refine ⟨yonedaEquiv a.hom.left, ?_⟩
    change equivShrink _ (glueSectionsOfSpace D T (yonedaEquiv.symm (yonedaEquiv a.hom.left))) =
      equivShrink _ ⟨w, φ⟩
    congr 1
    rw [Equiv.symm_apply_apply]
    change (⟨_, _⟩ : glueSections D _ V) = ⟨w, φ⟩
    refine glueSections.ext' (G := (formalGlueingFunctor D).1.obj T) (w' := w) (Over.w a.hom) ?_
    rw [show φ = ((formalGlueingFunctor D).1.map a).hom from congrArg (·.hom) ha.symm]
    change (restrictionDiagram D).map _ = (restrictionDiagram D).map _ ≫
      (restrictionDiagram D).map a.hom
    rw [← CategoryTheory.Functor.map_comp]
    congr 1

end AlgebraicGeometry.Space.FormalGlueingSituation

end
