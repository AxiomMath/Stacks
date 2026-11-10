module

public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.InvertibleQuotientDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.Algebra

/-!
# Sections of a morphism of algebraic spaces representing invertible quotients

Let `π : P ⟶ X` be a morphism of algebraic spaces and `ℰ` an `𝒪_X`-module, and suppose that for
every scheme `T` and every `T`-point `g` of `X` the `T`-points of `P` over `g` are in bijection
with the isomorphism classes of invertible quotients of `g^*ℰ`, naturally in `T`.  This is the
universal property of the projective bundle `𝐏(ℰ)` at scheme points.  Then the sections of `π` are
in bijection with the isomorphism classes of invertible quotients of `ℰ` itself: an invertible
quotient of `ℰ` gives a section point by point, and a section gives a compatible family of
invertible quotients on the étale charts of `X`, which glues (Stacks 03LY).

## Main definitions

* `AlgebraicGeometry.Space.homOfPoints`: a morphism of presheaves out of `F` from a family of
  morphisms out of the representable presheaves over `F`, compatible with restriction.
* `AlgebraicGeometry.Space.sectionsEquivOfPointsEquiv`: the bijection between the sections of `π`
  and the classes of invertible quotients of `ℰ`.

## Main results

* `AlgebraicGeometry.Space.sectionsEquivOfPointsEquiv_eq_iff`: the bijection sends `σ` to `c`
  exactly when, at every scheme point `g` of `X`, the point `g ≫ σ` of `P` over `g` corresponds to
  the pullback of `c` along `g`.

## References

* [Stacks Project, Tag 0B4I](https://stacks.math.columbia.edu/tag/0B4I)
* [Stacks Project, Tag 03LY](https://stacks.math.columbia.edu/tag/03LY)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section HomOfPoints

variable {F W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (k : ∀ (T : BigFppfOver B S hS), (yoneda.obj T ⟶ F) → (yoneda.obj T ⟶ W))
  (hk : ∀ (T T' : BigFppfOver B S hS) (h : T' ⟶ T) (g : yoneda.obj T ⟶ F),
    k T' (yoneda.map h ≫ g) = yoneda.map h ≫ k T g)

/-- **A morphism of presheaves from a compatible family of morphisms on representables.** -/
def homOfPoints (k : ∀ (T : BigFppfOver B S hS), (yoneda.obj T ⟶ F) → (yoneda.obj T ⟶ W))
    (hk : ∀ (T T' : BigFppfOver B S hS) (h : T' ⟶ T) (g : yoneda.obj T ⟶ F),
      k T' (yoneda.map h ≫ g) = yoneda.map h ≫ k T g) : F ⟶ W where
  app T := ↾(fun x => yonedaEquiv (k T.unop (yonedaEquiv.symm x)))
  naturality T T' h := by
    ext x
    change yonedaEquiv (k T'.unop (yonedaEquiv.symm (F.map h x))) =
      W.map h (yonedaEquiv (k T.unop (yonedaEquiv.symm x)))
    rw [yonedaEquiv_symm_map, hk]
    exact (yonedaEquiv_naturality _ h.unop).symm

include hk in
/-- Precomposing `homOfPoints k hk` with a point `g` of `F` over `T` gives `k T g`. -/
theorem comp_homOfPoints (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ F) :
    g ≫ homOfPoints k hk = k T g := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp]
  change yonedaEquiv (k T (yonedaEquiv.symm (yonedaEquiv g))) = _
  rw [Equiv.symm_apply_apply]

end HomOfPoints

/-- The component at an object of an isomorphism of functors followed by `eqToIso`, inverted. -/
theorem trans_eqToIso_app_symm {C D : Type*} [Category C] [Category D] {F G H : C ⥤ D}
    (α : F ≅ G) (p : G = H) (Y : C) :
    ((α ≪≫ eqToIso p).app Y).symm =
      eqToIso (congrArg (fun K : C ⥤ D => K.obj Y) p).symm ≪≫ (α.app Y).symm := by
  subst p
  ext
  simp

section PointLemmas

variable {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : F ⟶ G)

/-- A point of `F` over `x`, restricted along a morphism of test objects, lies over the
restriction of `x`. -/
theorem yoneda_map_comp_point_comp {T T' : BigFppfOver B S hS} (h : T' ⟶ T)
    {x : yoneda.obj T ⟶ G} (u : {u : yoneda.obj T ⟶ F // u ≫ p = x}) :
    (yoneda.map h ≫ u.1) ≫ p = yoneda.map h ≫ x := by
  rw [Category.assoc, u.2]

/-- The same, for a point given only up to equality. -/
theorem yoneda_map_comp_point_comp_of_eq {T T' : BigFppfOver B S hS} (h : T' ⟶ T)
    {x : yoneda.obj T ⟶ G} {x' : yoneda.obj T' ⟶ G} (hx : yoneda.map h ≫ x = x')
    (u : {u : yoneda.obj T ⟶ F // u ≫ p = x}) :
    (yoneda.map h ≫ u.1) ≫ p = x' := by
  rw [yoneda_map_comp_point_comp p h u, hx]

/-- A point `x` of the target followed by a section of `p` lies over `x`. -/
theorem comp_section_comp {T : BigFppfOver B S hS} (x : yoneda.obj T ⟶ G) {s : G ⟶ F}
    (hs : s ≫ p = 𝟙 G) : (x ≫ s) ≫ p = x := by
  rw [Category.assoc, hs, Category.comp_id]

end PointLemmas

variable (X : AlgebraicSpaces B S hS) (E : Modules.{u, u} B S hS X.1 X.2)

/-- The pullback of a class of invertible quotients of `ℰ` to a scheme point `g` of `X`. -/
abbrev pointRestrictClass (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ X.1) :
    InvertibleQuotientClass X E → InvertibleQuotientClass (yonedaSpace B S hS T)
      ((modulePullback B S hS (pointHom g)).obj E) :=
  invertibleQuotientBaseChangeClass (pointHom g) (Iso.refl _)

/-- The morphism of represented algebraic spaces induced by a morphism of the site: an
abbreviation of `AlgebraicGeometry.schemeSpaceMap`. -/
abbrev yonedaSpaceMap {T T' : BigFppfOver B S hS} (h : T' ⟶ T) :
    yonedaSpace B S hS T' ⟶ yonedaSpace B S hS T :=
  schemeSpaceMap h

/-- Restricting a class of invertible quotients to a point and then along a morphism of test
objects is restricting it to the composite point. -/
theorem pointRestrictClass_comp (T T' : BigFppfOver B S hS) (h : T' ⟶ T)
    (g : yoneda.obj T ⟶ X.1) (c : InvertibleQuotientClass X E) :
    invertibleQuotientBaseChangeClass (yonedaSpaceMap h)
        ((modulePullbackCompIso B S hS (yonedaSpaceMap h) (pointHom g)).app E).symm
        (pointRestrictClass X E T g c) =
      pointRestrictClass X E T' (yoneda.map h ≫ g) c := by
  rw [invertibleQuotientBaseChangeClass_comp]
  congr 1
  ext1
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_refl, Iso.refl_hom,
    Category.id_comp, Iso.app_hom, Iso.inv_hom_id_app]
  rfl

variable {P : AlgebraicSpaces B S hS} (π : P ⟶ X)
  (e : ∀ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ X.1),
    {u : yoneda.obj T ⟶ P.1 // u ≫ π.hom = g} ≃
      InvertibleQuotientClass (yonedaSpace B S hS T) ((modulePullback B S hS (pointHom g)).obj E))
  (he : ∀ (T T' : BigFppfOver B S hS) (h : T' ⟶ T) (g : yoneda.obj T ⟶ X.1)
    (u : {u : yoneda.obj T ⟶ P.1 // u ≫ π.hom = g}),
    e T' (yoneda.map h ≫ g) ⟨yoneda.map h ≫ u.1, yoneda_map_comp_point_comp π.hom h u⟩ =
      invertibleQuotientBaseChangeClass (yonedaSpaceMap h)
        ((modulePullbackCompIso B S hS (yonedaSpaceMap h) (pointHom g)).app E).symm (e T g u))

include he in
/-- The naturality hypothesis, at a point given as a composite only up to equality. -/
theorem pointsEquiv_natural_of_eq (T T' : BigFppfOver B S hS) (h : T' ⟶ T)
    (g : yoneda.obj T ⟶ X.1) (g' : yoneda.obj T' ⟶ X.1) (hg : yoneda.map h ≫ g = g')
    (u : {u : yoneda.obj T ⟶ P.1 // u ≫ π.hom = g}) :
    e T' g' ⟨yoneda.map h ≫ u.1, yoneda_map_comp_point_comp_of_eq π.hom h hg u⟩ =
      invertibleQuotientBaseChangeClass (yonedaSpaceMap h)
        (eqToIso (congrArg (fun k => (modulePullback B S hS (pointHom k)).obj E) hg.symm) ≪≫
          ((modulePullbackCompIso B S hS (yonedaSpaceMap h) (pointHom g)).app E).symm)
        (e T g u) := by
  subst hg
  rw [he]
  congr 1

/-- The point of `P` over a scheme point `g` of `X` attached to a class `c` of invertible
quotients of `ℰ`: the one corresponding to the pullback of `c` to `g`. -/
def pointOfClass (c : InvertibleQuotientClass X E) (T : BigFppfOver B S hS)
    (g : yoneda.obj T ⟶ X.1) : yoneda.obj T ⟶ P.1 :=
  ((e T g).symm (pointRestrictClass X E T g c)).1

/-- The point `pointOfClass X E π e c T g` of `P` lies over `g`. -/
theorem pointOfClass_comp (c : InvertibleQuotientClass X E) (T : BigFppfOver B S hS)
    (g : yoneda.obj T ⟶ X.1) : pointOfClass X E π e c T g ≫ π.hom = g :=
  ((e T g).symm (pointRestrictClass X E T g c)).2

/-- A point over `g` corresponds to the pullback of `c` to `g` exactly when it is
`pointOfClass X E π e c T g`. -/
private theorem pointsEquiv_eq_pointRestrictClass_iff (c : InvertibleQuotientClass X E)
    (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ X.1)
    (u : {u : yoneda.obj T ⟶ P.1 // u ≫ π.hom = g}) :
    e T g u = pointRestrictClass X E T g c ↔ u.1 = pointOfClass X E π e c T g := by
  rw [← Equiv.eq_symm_apply, Subtype.ext_iff]
  rfl

include he in
/-- The points `pointOfClass X E π e c` are compatible with restriction along morphisms of test
objects. -/
theorem pointOfClass_natural (c : InvertibleQuotientClass X E) (T T' : BigFppfOver B S hS)
    (h : T' ⟶ T) (g : yoneda.obj T ⟶ X.1) :
    pointOfClass X E π e c T' (yoneda.map h ≫ g) = yoneda.map h ≫ pointOfClass X E π e c T g := by
  have := he T T' h g ((e T g).symm (pointRestrictClass X E T g c))
  rw [Equiv.apply_symm_apply, pointRestrictClass_comp] at this
  exact congrArg Subtype.val ((Equiv.symm_apply_eq _).2 this.symm)

/-- **The section of `π` attached to a class of invertible quotients of `ℰ`.** -/
def sectionOfClass (c : InvertibleQuotientClass X E) : X ⟶ P :=
  ObjectProperty.homMk (homOfPoints (pointOfClass X E π e c) fun T T' h g =>
    pointOfClass_natural X E π e he c T T' h g)

/-- Precomposing the section attached to `c` with a point `g` of `X` gives
`pointOfClass X E π e c T g`. -/
theorem comp_sectionOfClass_hom (c : InvertibleQuotientClass X E) (T : BigFppfOver B S hS)
    (g : yoneda.obj T ⟶ X.1) :
    g ≫ (sectionOfClass X E π e he c).hom = pointOfClass X E π e c T g :=
  comp_homOfPoints (pointOfClass X E π e c)
    (fun T T' h g => pointOfClass_natural X E π e he c T T' h g) T g

/-- The morphism `sectionOfClass X E π e he c` is a section of `π`. -/
theorem sectionOfClass_comp (c : InvertibleQuotientClass X E) :
    sectionOfClass X E π e he c ≫ π = 𝟙 X := by
  ext1
  refine hom_ext_yoneda fun T g => ?_
  change g ≫ (sectionOfClass X E π e he c).hom ≫ π.hom = g ≫ 𝟙 X.1
  rw [← Category.assoc, comp_sectionOfClass_hom X E π e he c T g, pointOfClass_comp,
    Category.comp_id]

/-- The family of classes of invertible quotients on the étale charts of `X` attached to a
section of `π`: at a chart `U`, the class corresponding to the point `U ⟶ X ⟶ P`. -/
def chartClassOfSection (σ : X ⟶ P) (hσ : σ ≫ π = 𝟙 X) (U : SmallEtale B S hS X.1) :
    InvertibleQuotientClass (chartSpace B S hS X U) ((chartModuleRestriction B S hS X U).obj E) :=
  e U.obj.left U.obj.hom
    ⟨U.obj.hom ≫ σ.hom, comp_section_comp π.hom _ (congrArg InducedCategory.Hom.hom hσ)⟩

include he in
/-- The family `chartClassOfSection X E π e σ hσ` of classes on the étale charts of `X` is
compatible with the transition morphisms. -/
theorem isCompatible_chartClassOfSection (σ : X ⟶ P) (hσ : σ ≫ π = 𝟙 X) :
    IsCompatibleChartQuotientFamily X E (chartClassOfSection X E π e σ hσ) := by
  intro V U f
  have hσ' : σ.hom ≫ π.hom = 𝟙 X.1 := congrArg InducedCategory.Hom.hom hσ
  have h := pointsEquiv_natural_of_eq X E π e he U.obj.left V.obj.left f.hom.left U.obj.hom
    V.obj.hom (CostructuredArrow.w f.hom) ⟨U.obj.hom ≫ σ.hom, comp_section_comp π.hom _ hσ'⟩
  have hsub : (⟨V.obj.hom ≫ σ.hom, comp_section_comp π.hom _ hσ'⟩ :
        {u : yoneda.obj V.obj.left ⟶ P.1 // u ≫ π.hom = V.obj.hom}) =
      ⟨yoneda.map f.hom.left ≫ U.obj.hom ≫ σ.hom, by
        simpa only [Category.assoc, hσ', Category.comp_id] using CostructuredArrow.w f.hom⟩ :=
    Subtype.ext (by
      change V.obj.hom ≫ σ.hom = yoneda.map f.hom.left ≫ U.obj.hom ≫ σ.hom
      rw [← Category.assoc, CostructuredArrow.w f.hom])
  have hiso : (chartModuleRestrictionTransitions B S hS X E f).symm =
      eqToIso (congrArg (fun k => (modulePullback B S hS (pointHom k)).obj E)
          (CostructuredArrow.w f.hom).symm) ≪≫
        ((modulePullbackCompIso B S hS (chartMap B S hS X f) (chartToSpace B S hS X U)).app
          E).symm :=
    trans_eqToIso_app_symm _ _ E
  exact (congrArg (e V.obj.left V.obj.hom) hsub).trans (h.trans (congrArg
    (fun i => invertibleQuotientBaseChangeClass (chartMap B S hS X f) i
      (chartClassOfSection X E π e σ hσ U)) hiso.symm))

/-- **The class of invertible quotients of `ℰ` attached to a section of `π`**: the glueing of the
compatible family `chartClassOfSection`. -/
def classOfSection (σ : X ⟶ P) (hσ : σ ≫ π = 𝟙 X) : InvertibleQuotientClass X E :=
  (exists_chartRestrictClass_eq X E _ (isCompatible_chartClassOfSection X E π e he σ hσ)).choose

/-- The restriction of `classOfSection X E π e he σ hσ` to an étale chart `U` of `X` is
`chartClassOfSection X E π e σ hσ U`. -/
theorem chartRestrictClass_classOfSection (σ : X ⟶ P) (hσ : σ ≫ π = 𝟙 X)
    (U : SmallEtale B S hS X.1) :
    chartRestrictClass X E U (classOfSection X E π e he σ hσ) =
      chartClassOfSection X E π e σ hσ U :=
  (exists_chartRestrictClass_eq X E _
    (isCompatible_chartClassOfSection X E π e he σ hσ)).choose_spec U

/-- The class attached to the section `sectionOfClass X E π e he c` is `c`. -/
theorem classOfSection_sectionOfClass (c : InvertibleQuotientClass X E) :
    classOfSection X E π e he (sectionOfClass X E π e he c) (sectionOfClass_comp X E π e he c) =
      c := by
  refine invertibleQuotientClass_ext_of_chartRestrictClass X E _ _ fun U => ?_
  rw [chartRestrictClass_classOfSection, chartClassOfSection]
  exact (pointsEquiv_eq_pointRestrictClass_iff X E π e c _ _ _).2
    (comp_sectionOfClass_hom X E π e he c _ _)

/-- The section attached to the class `classOfSection X E π e he σ hσ` is `σ`. -/
theorem sectionOfClass_classOfSection (σ : X ⟶ P) (hσ : σ ≫ π = 𝟙 X) :
    sectionOfClass X E π e he (classOfSection X E π e he σ hσ) = σ := by
  obtain ⟨U, b, hsurj, hetale⟩ := X.2.exists_atlas
  ext1
  refine hom_ext_of_etale_atlas B S hS X.2.isSheaf P.2.isSheaf b hsurj hetale ?_
  rw [comp_sectionOfClass_hom, pointOfClass]
  let V : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk b, hetale⟩
  have hV := chartRestrictClass_classOfSection X E π e he σ hσ V
  change pointRestrictClass X E U b _ = e U b _ at hV
  rw [hV, Equiv.symm_apply_apply]
  rfl

/-- **The sections of `π` are the classes of invertible quotients of `ℰ`.** -/
def sectionsEquivOfPointsEquiv : { σ : X ⟶ P // σ ≫ π = 𝟙 X } ≃ InvertibleQuotientClass X E where
  toFun σ := classOfSection X E π e he σ.1 σ.2
  invFun c := ⟨sectionOfClass X E π e he c, sectionOfClass_comp X E π e he c⟩
  left_inv σ := Subtype.ext (sectionOfClass_classOfSection X E π e he σ.1 σ.2)
  right_inv c := classOfSection_sectionOfClass X E π e he c

/-- **The bijection is characterized pointwise**: it sends a section `σ` to the class `c` exactly
when, at every scheme point `g` of `X`, the point `g ≫ σ` of `P` over `g` corresponds to the
pullback of `c` to `g`. -/
theorem sectionsEquivOfPointsEquiv_eq_iff (σ : { σ : X ⟶ P // σ ≫ π = 𝟙 X })
    (c : InvertibleQuotientClass X E) :
    sectionsEquivOfPointsEquiv X E π e he σ = c ↔
      ∀ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ X.1),
        e T g ⟨g ≫ σ.1.hom, comp_section_comp π.hom g (congrArg InducedCategory.Hom.hom σ.2)⟩ =
          pointRestrictClass X E T g c := by
  constructor
  · rintro rfl T g
    have h := comp_sectionOfClass_hom X E π e he (sectionsEquivOfPointsEquiv X E π e he σ) T g
    have hσ : sectionOfClass X E π e he (sectionsEquivOfPointsEquiv X E π e he σ) = σ.1 :=
      congrArg Subtype.val ((sectionsEquivOfPointsEquiv X E π e he).symm_apply_apply σ)
    rw [hσ] at h
    exact (pointsEquiv_eq_pointRestrictClass_iff X E π e _ T g _).2 h
  · intro h
    rw [← Equiv.eq_symm_apply]
    refine Subtype.ext ?_
    ext1
    refine hom_ext_yoneda fun T g => ?_
    change g ≫ σ.1.hom = g ≫ (sectionOfClass X E π e he c).hom
    rw [comp_sectionOfClass_hom]
    exact (pointsEquiv_eq_pointRestrictClass_iff X E π e c T g _).1 (h T g)

end AlgebraicGeometry.Space

end
