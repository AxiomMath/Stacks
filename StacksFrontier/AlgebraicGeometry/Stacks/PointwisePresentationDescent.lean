module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.PointwiseFibrationModules
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentModules
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafFibredCategoryStack
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.PresentationComparisonSquares
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionComparisonAlgebraicSpaceComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionComparisonAlgebraicSpaceIso

/-!
# Descent data on the object space from a pointwise groupoid presentation

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces, let `𝒳` be a category fibred in
groupoids over `(Sch/S)_{fppf}`, and let `F : [U/_pR] ⥤ 𝒳` be a 1-morphism out of the pointwise
groupoid fibration (Stacks 044Q), so that `x = F ∘ ι : 𝒮_U ⥤ 𝒳` and `x ∘ s ⟶ x ∘ t` is the image
of the canonical 2-arrow.  For an `𝒪_𝒳`-module `ℱ` on the inherited étale site of `𝒳` this file
constructs the quasi-coherent module on `G` (Stacks 0441) of the proof of Stacks 06WT:
`(x^*ℱ|_{U_étale}, α)` with `α = c_t ≫ c_s⁻¹`, where `c_s`, `c_t` are the comparison maps of
equation 076R through the source and through the target.

## Main definitions

* `AlgebraicGeometry.Stack.pointwisePresentationRestriction`: `ℱ ↦ x^*ℱ|_{U_étale}`, with
  `AlgebraicGeometry.Stack.pointwisePresentationRestrictionMap`.
* `AlgebraicGeometry.Stack.pointwisePresentationSourceComparison`,
  `AlgebraicGeometry.Stack.pointwisePresentationTargetComparison`: the two comparison maps of
  equation 076R, and `AlgebraicGeometry.Stack.pointwisePresentationArrowComparison` the one along
  a morphism into the arrow space.
* `AlgebraicGeometry.Stack.IsPointwiseDescentAdmissible`: `x^*ℱ|_{U_étale}` is quasi-coherent
  and the comparison maps through the source, through the target and along the composition `c`
  are isomorphisms; `AlgebraicGeometry.Stack.pointwiseDescentAdmissible` is the object property.
* `AlgebraicGeometry.Stack.pointwiseDescentFunctor`: the functor from admissible modules to
  `AlgebraicGeometry.Space.QuasicoherentModule`, and
  `AlgebraicGeometry.Stack.pointwiseQuasicoherentDescentFunctor` its restriction to the
  quasi-coherent modules of Stacks 06WG, which are admissible
  (`AlgebraicGeometry.Stack.isPointwiseDescentAdmissible_of_quasicoherent`).

## Main results

* `AlgebraicGeometry.Stack.groupoidPullbackTransition_comp_of_pointwisePresentation`: the cocycle
  condition for any `α` with `α ≫ c_s = c_t`.
* `AlgebraicGeometry.Stack.groupoidPullbackTransition_identityArrow_of_pointwisePresentation`: the
  unit condition for any such `α`.

## References

* [Stacks Project, Tag 06WT](https://stacks.math.columbia.edu/tag/06WT)
* [Stacks Project, Tag 0441](https://stacks.math.columbia.edu/tag/0441)
* [Stacks Project, Tag 076R](https://stacks.math.columbia.edu/tag/076R)
* [Stacks Project, Tag 075D](https://stacks.math.columbia.edu/tag/075D)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Space

universe u v w v' w' v'' w''

section General

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A composite of two morphisms each lying over an identity lies over an identity. -/
theorem isHomLift_id_comp' {𝒜 : Type*} [Category 𝒜] {𝒮 : Type*} [Category 𝒮]
    (P : 𝒜 ⥤ 𝒮) {R R' : 𝒮} {x y z : 𝒜} {φ : x ⟶ y} {ψ : y ⟶ z}
    (h₁ : P.IsHomLift (𝟙 R) φ) (h₂ : P.IsHomLift (𝟙 R') ψ) :
    P.IsHomLift (𝟙 (P.obj x)) (φ ≫ ψ) := by
  obtain rfl := IsHomLift.codomain_eq P (𝟙 R) φ
  obtain rfl := IsHomLift.domain_eq P (𝟙 R') ψ
  have : P.IsHomLift (𝟙 (P.obj y)) (φ ≫ ψ) := inferInstance
  obtain h := IsHomLift.domain_eq P (𝟙 (P.obj y)) (φ ≫ ψ)
  rw [h]
  exact this

/-- Cancellation of an isomorphism on the right. -/
theorem eq_of_comp_isIso {𝒞 : Type*} [Category 𝒞] {A B : 𝒞} {a b : A ⟶ B} {N : 𝒞} (Q : B ⟶ N)
    [IsIso Q] (h : a ≫ Q = b ≫ Q) : a = b := by
  simpa using congrArg (· ≫ inv Q) h

/-- Naturality of a transition `c_t ≫ c_s⁻¹` built from two natural comparison maps. -/
theorem comp_inv_naturality {𝒞 : Type*} [Category 𝒞] {A A' B B' M M' : 𝒞}
    (cs : B ⟶ M) (cs' : B' ⟶ M') [IsIso cs] [IsIso cs'] (ct : A ⟶ M) (ct' : A' ⟶ M')
    (a : B ⟶ B') (b : A ⟶ A') (e : M ⟶ M') (hs : cs ≫ e = a ≫ cs') (ht : ct ≫ e = b ≫ ct') :
    (ct ≫ inv cs) ≫ a = b ≫ ct' ≫ inv cs' := by
  rw [← cancel_mono cs']
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← hs, IsIso.inv_hom_id_assoc, ht]

/-- Two morphisms lying over the same morphism along a faithful functor are equal. -/
theorem eq_of_isHomLift_of_faithful {𝒜 : Type*} [Category 𝒜] {𝒮 : Type*} [Category 𝒮]
    (P : 𝒜 ⥤ 𝒮) [P.Faithful] {R R' : 𝒮} {x y : 𝒜} (f : R ⟶ R') (φ ψ : x ⟶ y)
    [P.IsHomLift f φ] [P.IsHomLift f ψ] : φ = ψ :=
  P.map_injective ((IsHomLift.fac' P f φ).trans (IsHomLift.fac' P f ψ).symm)

variable {U V : AlgebraicSpaces B S hS}
  {𝒰 : Type v} [Category.{w} 𝒰] {𝒱 : Type v'} [Category.{w'} 𝒱]
  {𝒳 : Type v''} [Category.{w''} 𝒳]
  (p : 𝒰 ⥤ BigFppfOver B S hS) (q : 𝒱 ⥤ BigFppfOver B S hS) (r : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) (hr : r.IsFiberedInGroupoids)
  (eU : StacksRepresentableCFG.EquivalenceOver p
    (presheafOfCategories (U.1 ⋙ typeToCat)).p)
  (eV : StacksRepresentableCFG.EquivalenceOver q
    (presheafOfCategories (V.1 ⋙ typeToCat)).p)
  (f : 𝒰 ⥤ 𝒳) (g : 𝒱 ⥤ 𝒳)
  (hf : p.IsFibredOneMorphism r f) (hg : q.IsFibredOneMorphism r g) (aSpace : U ⟶ V)

/-- The morphism of charts underlying the comparison morphism lies over the vertical morphism of
the chart diagram. -/
theorem isHomLift_comparisonChartHom_ofUniv (a : 𝒰 ⥤ 𝒱)
    (ha : schemeChartFunctor B S hS U.1 p eU ⋙ a ≅
      CostructuredArrow.map aSpace.hom ⋙ schemeChartFunctor B S hS V.1 q eV)
    (hab : ∀ Z : CostructuredArrow yoneda U.1,
      q.IsHomLift (𝟙 (q.obj (a.obj ((schemeChartFunctor B S hS U.1 p eU).obj Z))))
        (ha.hom.app Z))
    (d : ChartDiagram B S hS U.1 V.1 aSpace.hom) :
    q.IsHomLift d.g (comparisonChartHom B S hS p q eU eV a aSpace ha d) := by
  have : (CostructuredArrow.proj yoneda V.1).IsHomLift d.g
      (chartDiagramChartHom B S hS aSpace d) :=
    IsHomLift.map (CostructuredArrow.proj yoneda V.1) (chartDiagramChartHom B S hS aSpace d)
  have : q.IsHomLift d.g ((schemeChartFunctor B S hS V.1 q eV).map
      (chartDiagramChartHom B S hS aSpace d)) :=
    Functor.isHomLift_map_of_comp_eq (schemeChartFunctor_comp B S hS V.1 q eV) d.g _
  have := hab d.U.1
  exact IsHomLift.comp_lift_id_left' q
    (q.obj (a.obj ((schemeChartFunctor B S hS U.1 p eU).obj d.U.1)))
    (ha.hom.app d.U.1) d.g
    ((schemeChartFunctor B S hS V.1 q eV).map (chartDiagramChartHom B S hS aSpace d))

/-- **The comparison map of equation 076R depends only on its comparison morphisms.**  Two
comparison maps between the same modules whose comparison morphisms agree at every diagram of
étale scheme charts are equal. -/
theorem comparisonAlgebraicSpacesModules_congr (a a' : 𝒰 ⥤ 𝒱) (φ : a ⋙ g ≅ f) (φ' : a' ⋙ g ≅ f)
    (ha : schemeChartFunctor B S hS U.1 p eU ⋙ a ≅
      CostructuredArrow.map aSpace.hom ⋙ schemeChartFunctor B S hS V.1 q eV)
    (ha' : schemeChartFunctor B S hS U.1 p eU ⋙ a' ≅
      CostructuredArrow.map aSpace.hom ⋙ schemeChartFunctor B S hS V.1 q eV)
    (hφ : ∀ X : 𝒰, r.IsHomLift (𝟙 (r.obj (f.obj X))) (φ.inv.app X))
    (hφ' : ∀ X : 𝒰, r.IsHomLift (𝟙 (r.obj (f.obj X))) (φ'.inv.app X))
    (hab : ∀ Z : CostructuredArrow yoneda U.1,
      q.IsHomLift (𝟙 (q.obj (a.obj ((schemeChartFunctor B S hS U.1 p eU).obj Z))))
        (ha.hom.app Z))
    (hab' : ∀ Z : CostructuredArrow yoneda U.1,
      q.IsHomLift (𝟙 (q.obj (a'.obj ((schemeChartFunctor B S hS U.1 p eU).obj Z))))
        (ha'.hom.app Z))
    (ℱ : inheritedEtaleModules B S hS r hr)
    (hm : ∀ d : ChartDiagram B S hS U.1 V.1 aSpace.hom,
      comparisonMorphism B S hS p q eU eV a f g φ aSpace ha d =
        comparisonMorphism B S hS p q eU eV a' f g φ' aSpace ha' d) :
    comparisonAlgebraicSpacesModules B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha hr hφ hab
        ℱ =
      comparisonAlgebraicSpacesModules B S hS p q r hp hq eU eV a' f g hf hg φ' aSpace ha' hr
        hφ' hab' ℱ := by
  have hF : moduleComparisonFMap B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha hr hφ hab ℱ =
      moduleComparisonFMap B S hS p q r hp hq eU eV a' f g hf hg φ' aSpace ha' hr hφ' hab' ℱ := by
    refine ModuleFMap.ext B S hS (funext fun d => funext fun s => ?_)
    refine (moduleComparisonFMap_app B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha hr hφ hab
      ℱ d s).trans (Eq.trans ?_ (moduleComparisonFMap_app B S hS p q r hp hq eU eV a' f g hf hg φ'
        aSpace ha' hr hφ' hab' ℱ d s).symm)
    rw [hm d]
  exact congrArg (fun F => ((modulePullbackAdjunction B S hS aSpace).homEquiv _ _).symm
    (moduleFMapHom B S hS aSpace _ _ F)) hF

/-- **Over a faithful presentation, the comparison map depends on the 2-morphism only.**  If the
structure functor of `𝒱` is faithful, two comparison maps along equal 1-morphisms `a = a'`
whose 2-morphisms agree up to the transport along `a = a'` are equal. -/
theorem comparisonAlgebraicSpacesModules_congr_of_faithful [q.Faithful] (a a' : 𝒰 ⥤ 𝒱)
    (e : a = a') (φ : a ⋙ g ≅ f) (φ' : a' ⋙ g ≅ f)
    (hφφ' : ∀ X : 𝒰, φ.inv.app X = φ'.inv.app X ≫ g.map (eqToHom (Functor.congr_obj e X).symm))
    (ha : schemeChartFunctor B S hS U.1 p eU ⋙ a ≅
      CostructuredArrow.map aSpace.hom ⋙ schemeChartFunctor B S hS V.1 q eV)
    (ha' : schemeChartFunctor B S hS U.1 p eU ⋙ a' ≅
      CostructuredArrow.map aSpace.hom ⋙ schemeChartFunctor B S hS V.1 q eV)
    (hφ : ∀ X : 𝒰, r.IsHomLift (𝟙 (r.obj (f.obj X))) (φ.inv.app X))
    (hφ' : ∀ X : 𝒰, r.IsHomLift (𝟙 (r.obj (f.obj X))) (φ'.inv.app X))
    (hab : ∀ Z : CostructuredArrow yoneda U.1,
      q.IsHomLift (𝟙 (q.obj (a.obj ((schemeChartFunctor B S hS U.1 p eU).obj Z))))
        (ha.hom.app Z))
    (hab' : ∀ Z : CostructuredArrow yoneda U.1,
      q.IsHomLift (𝟙 (q.obj (a'.obj ((schemeChartFunctor B S hS U.1 p eU).obj Z))))
        (ha'.hom.app Z))
    (ℱ : inheritedEtaleModules B S hS r hr) :
    comparisonAlgebraicSpacesModules B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha hr hφ hab
        ℱ =
      comparisonAlgebraicSpacesModules B S hS p q r hp hq eU eV a' f g hf hg φ' aSpace ha' hr
        hφ' hab' ℱ := by
  subst e
  refine comparisonAlgebraicSpacesModules_congr B S hS p q r hp hq hr eU eV f g hf hg aSpace
    a a φ φ' ha ha' hφ hφ' hab hab' ℱ fun d => ?_
  have h₁ := isHomLift_comparisonChartHom_ofUniv B S hS p q eU eV aSpace a ha hab d
  have h₂ := isHomLift_comparisonChartHom_ofUniv B S hS p q eU eV aSpace a ha' hab' d
  have hc : comparisonChartHom B S hS p q eU eV a aSpace ha d =
      comparisonChartHom B S hS p q eU eV a aSpace ha' d :=
    eq_of_isHomLift_of_faithful q d.g _ _
  unfold comparisonMorphism
  rw [hc, hφφ', eqToHom_refl, CategoryTheory.Functor.map_id]
  exact congrArg (· ≫ _) (Category.comp_id _)


end General


end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

universe u v w

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

/-! ### The category of an algebraic space -/

section Spaces

variable {X Y Z : AlgebraicSpaces C S hS}

/-- The category `𝒮_X` of an algebraic space `X` (Stacks 0458). -/
abbrev spaceCat (X : AlgebraicSpaces C S hS) := (fibredCategory C S hS X.obj).val.obj

/-- The structure functor `𝒮_X ⥤ (Sch/S)_{fppf}`. -/
abbrev spaceProj (X : AlgebraicSpaces C S hS) : spaceCat X ⥤ BigFppfOver C S hS :=
  (fibredCategory C S hS X.obj).val.p

/-- The category `𝒮_X` of an algebraic space is fibred in groupoids over `(Sch/S)_{fppf}`. -/
theorem isFiberedInGroupoids_spaceProj (X : AlgebraicSpaces C S hS) :
    (spaceProj X).IsFiberedInGroupoids :=
  (fibredCategory C S hS X.obj).property

/-- The tautological presentation of `𝒮_X` by the algebraic space `X`. -/
abbrev spacePresentation (X : AlgebraicSpaces C S hS) :
    StacksRepresentableCFG.EquivalenceOver (spaceProj X)
      (presheafOfCategories (X.1 ⋙ typeToCat)).p :=
  StacksRepresentableCFG.EquivalenceOver.refl _

/-- The 1-morphism `𝒮_X ⥤ 𝒮_Y` associated with a morphism of algebraic spaces (Stacks 0458). -/
abbrev spaceFunctor (h : X ⟶ Y) : spaceCat X ⥤ spaceCat Y :=
  (associatedMap C S hS h.hom).1.hom.toFunctor

/-- The 1-morphism `𝒮_X ⥤ 𝒮_Y` attached to `h : X ⟶ Y` is a 1-morphism of categories over
`(Sch/S)_{fppf}`. -/
theorem isFibredOneMorphism_spaceFunctor (h : X ⟶ Y) :
    (spaceProj X).IsFibredOneMorphism (spaceProj Y) (spaceFunctor h) :=
  (isFiberedInGroupoids_spaceProj Y).isFibredOneMorphism (associatedMap C S hS h.hom).1.hom.w

/-- The structure functor `𝒮_X ⥤ (Sch/S)_{fppf}` is faithful. -/
instance (X : AlgebraicSpaces C S hS) : (spaceProj X).Faithful :=
  faithful_fibredCategory_projection X.obj

/-- Through the tautological presentations, the 1-morphism attached to `h` is postcomposition
with `h`, on the nose. -/
abbrev spaceFunctorChartIso (h : X ⟶ Y) :
    Space.schemeChartFunctor C S hS X.obj (spaceProj X) (spacePresentation X) ⋙ spaceFunctor h ≅
      CostructuredArrow.map h.hom ⋙
        Space.schemeChartFunctor C S hS Y.obj (spaceProj Y) (spacePresentation Y) :=
  Iso.refl _

/-- The components of the presentation of `spaceFunctor h` lie over identities. -/
theorem isHomLift_spaceFunctorChartIso_hom_app (h : X ⟶ Y)
    (Z : CostructuredArrow yoneda X.obj) :
    (spaceProj Y).IsHomLift (𝟙 ((spaceProj Y).obj ((spaceFunctor h).obj
      ((Space.schemeChartFunctor C S hS X.obj (spaceProj X) (spacePresentation X)).obj Z))))
      ((spaceFunctorChartIso h).hom.app Z) :=
  IsHomLift.id rfl

/-- The category `𝒮_U` of the object space of a groupoid is fibred in groupoids. -/
theorem isFiberedInGroupoids_objects {A : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS A) : (spaceProj G.objects).IsFiberedInGroupoids :=
  isFiberedInGroupoids_spaceProj G.objects

/-- The category `𝒮_R` of the arrow space of a groupoid is fibred in groupoids. -/
theorem isFiberedInGroupoids_arrows {A : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS A) : (spaceProj G.arrows).IsFiberedInGroupoids :=
  isFiberedInGroupoids_spaceProj G.arrows

/-- The 1-morphism `𝒮_R ⥤ 𝒮_U` of the source `s` is a 1-morphism over `(Sch/S)_{fppf}`. -/
theorem isFibredOneMorphism_source {A : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS A) :
    (spaceProj G.arrows).IsFibredOneMorphism (spaceProj G.objects) (spaceFunctor G.source) :=
  isFibredOneMorphism_spaceFunctor G.source

/-- The 1-morphism `𝒮_R ⥤ 𝒮_U` of the target `t` is a 1-morphism over `(Sch/S)_{fppf}`. -/
theorem isFibredOneMorphism_target {A : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS A) :
    (spaceProj G.arrows).IsFibredOneMorphism (spaceProj G.objects) (spaceFunctor G.target) :=
  isFibredOneMorphism_spaceFunctor G.target

/-- The components of the presentation of the 1-morphism attached to the source `s` lie over
identities. -/
theorem isHomLift_sourceChartIso {A : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS A) (Z : CostructuredArrow yoneda G.arrows.obj) :
    (spaceProj G.objects).IsHomLift (𝟙 ((spaceProj G.objects).obj ((spaceFunctor G.source).obj
      ((Space.schemeChartFunctor C S hS G.arrows.obj (spaceProj G.arrows)
        (spacePresentation G.arrows)).obj Z))))
      ((spaceFunctorChartIso G.source).hom.app Z) :=
  isHomLift_spaceFunctorChartIso_hom_app G.source Z

/-- The components of the presentation of the 1-morphism attached to the target `t` lie over
identities. -/
theorem isHomLift_targetChartIso {A : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS A) (Z : CostructuredArrow yoneda G.arrows.obj) :
    (spaceProj G.objects).IsHomLift (𝟙 ((spaceProj G.objects).obj ((spaceFunctor G.target).obj
      ((Space.schemeChartFunctor C S hS G.arrows.obj (spaceProj G.arrows)
        (spacePresentation G.arrows)).obj Z))))
      ((spaceFunctorChartIso G.target).hom.app Z) :=
  isHomLift_spaceFunctorChartIso_hom_app G.target Z

/-- The components of the presentation of the 1-morphism of `h ≫ k` lie over identities. -/
theorem isHomLift_compChartIso (h : X ⟶ Y) (k : Y ⟶ Z) (W : CostructuredArrow yoneda X.obj) :
    (spaceProj Z).IsHomLift (𝟙 ((spaceProj Z).obj ((spaceFunctor (h ≫ k)).obj
      ((Space.schemeChartFunctor C S hS X.obj (spaceProj X) (spacePresentation X)).obj W))))
      ((spaceFunctorChartIso (h ≫ k)).hom.app W) :=
  isHomLift_spaceFunctorChartIso_hom_app (h ≫ k) W

/-- The presentation of a composite of associated 1-morphisms lies over identities. -/
theorem isHomLift_comparisonChartFunctorIsoComp (h : X ⟶ Y) (k : Y ⟶ Z)
    (W : CostructuredArrow yoneda X.obj) :
    (spaceProj Z).IsHomLift (𝟙 ((spaceProj Z).obj ((spaceFunctor h ⋙ spaceFunctor k).obj
      ((Space.schemeChartFunctor C S hS X.obj (spaceProj X) (spacePresentation X)).obj W))))
      ((Space.comparisonChartFunctorIsoComp C S hS (spaceProj X) (spaceProj Y) (spaceProj Z)
        (spacePresentation X) (spacePresentation Y) (spacePresentation Z) (spaceFunctor h)
        (spaceFunctor k) h k (spaceFunctorChartIso h) (spaceFunctorChartIso k)).hom.app W) :=
  Space.isHomLift_comparisonChartFunctorIsoComp_hom_app C S hS (spaceProj X) (spaceProj Y)
    (spaceProj Z) (spacePresentation X) (spacePresentation Y) (spacePresentation Z)
    (spaceFunctor h) (spaceFunctor k) h k (spaceFunctorChartIso h) (spaceFunctorChartIso k)
    (isFibredOneMorphism_spaceFunctor k) (isHomLift_spaceFunctorChartIso_hom_app h)
    (isHomLift_spaceFunctorChartIso_hom_app k) W

/-- The 1-morphism associated with an identity is the identity. -/
theorem spaceFunctor_id (X : AlgebraicSpaces C S hS) : spaceFunctor (𝟙 X) = 𝟭 _ := by
  have h : (associatedMap C S hS (InducedCategory.Hom.hom (𝟙 X))).1 = 𝟙 _ :=
    hom_ext_of_obj C S hS fun x => by rw [associatedMap_obj]; rfl
  exact congrArg (fun F => F.hom.toFunctor) h

/-- Functoriality of the associated 1-morphism (Stacks 0458). -/
theorem spaceFunctor_comp (h : X ⟶ Y) (k : Y ⟶ Z) :
    spaceFunctor (h ≫ k) = spaceFunctor h ⋙ spaceFunctor k :=
  congrArg (fun F => F.hom.toFunctor) (associatedMap_comp C S hS h.hom k.hom)

end Spaces

/-! ### A pointwise groupoid presentation -/

section Presentation

variable {A : AlgebraicSpaces C S hS} {G : GroupoidInAlgebraicSpaces C S hS A}
  {𝒳 : Type v} [Category.{w} 𝒳] {p : 𝒳 ⥤ BigFppfOver C S hS} {hp : p.IsFiberedInGroupoids}
  (F : PointwiseFibration G ⥤ 𝒳)
  (hF : F ⋙ p = (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p)

/-- The 1-morphism `x : 𝒮_U ⥤ 𝒳` of a pointwise presentation. -/
abbrev pointwisePresentationObject : spaceCat G.objects ⥤ 𝒳 := pointwiseObjectInclusion G ⋙ F

include hF in
/-- The 1-morphism `x : 𝒮_U ⥤ 𝒳` lies over `(Sch/S)_{fppf}`: `x ⋙ p` is the structure functor of
`𝒮_U`. -/
theorem pointwisePresentationObject_comp :
    pointwisePresentationObject F ⋙ p = spaceProj G.objects := by
  rw [Functor.assoc, hF]
  rfl

include hF in
/-- The 1-morphism `x : 𝒮_U ⥤ 𝒳` is a 1-morphism of categories fibred in groupoids. -/
theorem isFibredOneMorphism_pointwisePresentationObject (hp : p.IsFiberedInGroupoids) :
    (spaceProj G.objects).IsFibredOneMorphism p (pointwisePresentationObject F) :=
  hp.isFibredOneMorphism (pointwisePresentationObject_comp F hF)

/-- The 1-morphism `x ∘ s : 𝒮_R ⥤ 𝒳`. -/
abbrev pointwisePresentationSource : spaceCat G.arrows ⥤ 𝒳 :=
  spaceFunctor G.source ⋙ pointwisePresentationObject F

include hF in
/-- The 1-morphism `x ∘ s : 𝒮_R ⥤ 𝒳` is a 1-morphism of categories fibred in groupoids. -/
theorem isFibredOneMorphism_pointwisePresentationSource (hp : p.IsFiberedInGroupoids) :
    (spaceProj G.arrows).IsFibredOneMorphism p (pointwisePresentationSource F) :=
  hp.isFibredOneMorphism (by
    rw [Functor.assoc, pointwisePresentationObject_comp F hF]
    exact (associatedMap C S hS G.source.hom).1.hom.w)

/-- The components of the identity 2-morphism of `x ∘ s` lie over identities. -/
theorem isHomLift_pointwisePresentationSource_refl (Y : spaceCat G.arrows) :
    p.IsHomLift (𝟙 (p.obj ((pointwisePresentationSource F).obj Y)))
      ((Iso.refl (pointwisePresentationSource F)).inv.app Y) :=
  Space.isHomLift_iso_refl_inv_app C S hS p (pointwisePresentationSource F) Y

/-- The canonical 2-morphism `x ∘ s ⟶ x ∘ t` of a pointwise presentation: the image of the
canonical 2-arrow of the pointwise groupoid fibration. -/
def pointwisePresentationTwoArrow :
    pointwisePresentationSource F ⟶ spaceFunctor G.target ⋙ pointwisePresentationObject F :=
  Functor.whiskerRight (pointwiseTwoArrow G) F

include hF in
/-- The components of the canonical 2-morphism of a pointwise presentation lie over
identities. -/
theorem isHomLift_pointwisePresentationTwoArrow_app (Y : spaceCat G.arrows) :
    p.IsHomLift (𝟙 (p.obj ((pointwisePresentationSource F).obj Y)))
      ((pointwisePresentationTwoArrow F).app Y) := by
  have := pointwiseTwoArrow_isHomLift G Y
  have : p.IsHomLift (𝟙 ((spaceProj G.arrows).obj Y)) (F.map ((pointwiseTwoArrow G).app Y)) :=
    Functor.isHomLift_map_of_comp_eq hF _ ((pointwiseTwoArrow G).app Y)
  have h := IsHomLift.domain_eq p (𝟙 ((spaceProj G.arrows).obj Y))
    (F.map ((pointwiseTwoArrow G).app Y))
  exact h ▸ this

/-- The canonical 2-morphism `x ∘ s ⟶ x ∘ t` of a pointwise presentation is invertible. -/
instance : IsIso (pointwisePresentationTwoArrow F) := by
  have : ∀ Y, IsIso ((pointwisePresentationTwoArrow F).app Y) := fun Y => by
    have : IsIso ((pointwiseTwoArrow G).app Y) := isIso_vertHom (G := G) Y.base Y.fiber.as rfl rfl
    change IsIso (F.map ((pointwiseTwoArrow G).app Y))
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- The 2-isomorphism `x ∘ t ≅ x ∘ s` of a pointwise presentation, inverse of the canonical
2-morphism; it is the 2-morphism of the triangle through the target. -/
abbrev pointwisePresentationTwoIso :
    spaceFunctor G.target ⋙ pointwisePresentationObject F ≅ pointwisePresentationSource F :=
  (asIso (pointwisePresentationTwoArrow F)).symm

include hF in
/-- The components of the inverse of the 2-isomorphism `x ∘ t ≅ x ∘ s` lie over identities. -/
theorem isHomLift_pointwisePresentationTwoIso_inv_app (Y : spaceCat G.arrows) :
    p.IsHomLift (𝟙 (p.obj ((pointwisePresentationSource F).obj Y)))
      ((pointwisePresentationTwoIso F).inv.app Y) :=
  isHomLift_pointwisePresentationTwoArrow_app F hF Y

/-- **`ℱ ↦ x^*ℱ|_{U_étale}`.**  The restriction to the small étale site of the object space of
the inverse image of an `𝒪_𝒳`-module along `x : 𝒮_U ⥤ 𝒳`. -/
abbrev pointwisePresentationRestriction (ℱ : Space.inheritedEtaleModules.{u, v, w, u} C S hS p hp) :
    Space.Modules.{u, u} C S hS G.objects.1 G.objects.2 :=
  Space.etaleRestrictedModuleInverseImage C S hS (U := G.objects) (spaceProj G.objects) p
    (isFiberedInGroupoids_objects G) hp (spacePresentation G.objects)
    (pointwisePresentationObject F) (isFibredOneMorphism_pointwisePresentationObject F hF hp) ℱ

/-- **`ψ ↦ x^*ψ|_{U_étale}`.** -/
abbrev pointwisePresentationRestrictionMap
    {ℱ ℋ : Space.inheritedEtaleModules.{u, v, w, u} C S hS p hp} (ψ : ℱ ⟶ ℋ) :=
  Space.etaleRestrictedModuleInverseImageMap C S hS (U := G.objects) (spaceProj G.objects) p
    (isFiberedInGroupoids_objects G) hp (spacePresentation G.objects)
    (pointwisePresentationObject F) (isFibredOneMorphism_pointwisePresentationObject F hF hp) ψ

/-- **The comparison map through the source**,
`s_small^*(x^*ℱ|_{U_étale}) ⟶ (x ∘ s)^*ℱ|_{R_étale}`, of the triangle `x ∘ s = x ∘ s`. -/
abbrev pointwisePresentationSourceComparison
    (ℱ : Space.inheritedEtaleModules.{u, v, w, u} C S hS p hp) :=
  Space.comparisonAlgebraicSpacesModules C S hS (spaceProj G.arrows) (spaceProj G.objects) p
    (isFiberedInGroupoids_arrows G) (isFiberedInGroupoids_objects G)
    (spacePresentation G.arrows) (spacePresentation G.objects) (spaceFunctor G.source)
    (pointwisePresentationSource F) (pointwisePresentationObject F)
    (isFibredOneMorphism_pointwisePresentationSource F hF hp)
    (isFibredOneMorphism_pointwisePresentationObject F hF hp)
    (Iso.refl (pointwisePresentationSource F)) G.source (spaceFunctorChartIso G.source) hp
    (isHomLift_pointwisePresentationSource_refl F) (isHomLift_sourceChartIso G) ℱ

/-- **The comparison map through the target**,
`t_small^*(x^*ℱ|_{U_étale}) ⟶ (x ∘ s)^*ℱ|_{R_étale}`, of the triangle `x ∘ t ≅ x ∘ s` given by
the inverse of the canonical 2-morphism. -/
abbrev pointwisePresentationTargetComparison
    (ℱ : Space.inheritedEtaleModules.{u, v, w, u} C S hS p hp) :=
  Space.comparisonAlgebraicSpacesModules C S hS (spaceProj G.arrows) (spaceProj G.objects) p
    (isFiberedInGroupoids_arrows G) (isFiberedInGroupoids_objects G)
    (spacePresentation G.arrows) (spacePresentation G.objects) (spaceFunctor G.target)
    (pointwisePresentationSource F) (pointwisePresentationObject F)
    (isFibredOneMorphism_pointwisePresentationSource F hF hp)
    (isFibredOneMorphism_pointwisePresentationObject F hF hp)
    (pointwisePresentationTwoIso F) G.target (spaceFunctorChartIso G.target) hp
    (isHomLift_pointwisePresentationTwoIso_inv_app F hF) (isHomLift_targetChartIso G) ℱ

/-- Unfolding `x^*ℱ|_{U_étale}` as the étale restriction of the inverse image along `x`. -/
theorem pointwisePresentationRestriction_eq
    (ℱ : Space.inheritedEtaleModules.{u, v, w, u} C S hS p hp) :
    pointwisePresentationRestriction F hF ℱ =
      Space.etaleRestrictedModuleInverseImage C S hS (U := G.objects) (spaceProj G.objects) p
        (isFiberedInGroupoids_objects G) hp (spacePresentation G.objects)
        (pointwisePresentationObject F) (isFibredOneMorphism_pointwisePresentationObject F hF hp)
        ℱ := rfl

/-- Unfolding the comparison map through the source as a comparison map of equation 076R. -/
theorem pointwisePresentationSourceComparison_eq
    (ℱ : Space.inheritedEtaleModules.{u, v, w, u} C S hS p hp) :
    pointwisePresentationSourceComparison F hF ℱ = Space.comparisonAlgebraicSpacesModules C S hS
      (spaceProj G.arrows) (spaceProj G.objects) p
      (isFiberedInGroupoids_arrows G) (isFiberedInGroupoids_objects G)
      (spacePresentation G.arrows) (spacePresentation G.objects) (spaceFunctor G.source)
      (pointwisePresentationSource F) (pointwisePresentationObject F)
      (isFibredOneMorphism_pointwisePresentationSource F hF hp)
      (isFibredOneMorphism_pointwisePresentationObject F hF hp)
      (Iso.refl (pointwisePresentationSource F)) G.source (spaceFunctorChartIso G.source) hp
      (isHomLift_pointwisePresentationSource_refl F) (isHomLift_sourceChartIso G) ℱ := rfl

/-- Unfolding the comparison map through the target as a comparison map of equation 076R. -/
theorem pointwisePresentationTargetComparison_eq
    (ℱ : Space.inheritedEtaleModules.{u, v, w, u} C S hS p hp) :
    pointwisePresentationTargetComparison F hF ℱ = Space.comparisonAlgebraicSpacesModules C S hS
      (spaceProj G.arrows) (spaceProj G.objects) p
      (isFiberedInGroupoids_arrows G) (isFiberedInGroupoids_objects G)
      (spacePresentation G.arrows) (spacePresentation G.objects) (spaceFunctor G.target)
      (pointwisePresentationSource F) (pointwisePresentationObject F)
      (isFibredOneMorphism_pointwisePresentationSource F hF hp)
      (isFibredOneMorphism_pointwisePresentationObject F hF hp)
      (pointwisePresentationTwoIso F) G.target (spaceFunctorChartIso G.target) hp
      (isHomLift_pointwisePresentationTwoIso_inv_app F hF) (isHomLift_targetChartIso G) ℱ := rfl

/-- A morphism equal to a transport along an equality of objects lies over an identity. -/
theorem isHomLift_id_of_eq_eqToHom {a b : 𝒳} {φ : a ⟶ b} (hab : a = b) (h : φ = eqToHom hab) :
    p.IsHomLift (𝟙 (p.obj a)) φ := by
  subst h
  exact IsHomLift.eqToHom_domain_lift_id hab rfl

/-! ### The comparison map along a morphism into the object space -/

/-- The components of the presentation of the 1-morphism attached to `k : X ⟶ U` lie over
identities. -/
theorem isHomLift_objectsChartIso (G : GroupoidInAlgebraicSpaces C S hS A)
    {X : AlgebraicSpaces C S hS}
    (k : X ⟶ G.objects) (W : CostructuredArrow yoneda X.obj) :
    (spaceProj G.objects).IsHomLift (𝟙 ((spaceProj G.objects).obj ((spaceFunctor k).obj
      ((Space.schemeChartFunctor C S hS X.obj (spaceProj X) (spacePresentation X)).obj W))))
      ((spaceFunctorChartIso k).hom.app W) :=
  isHomLift_spaceFunctorChartIso_hom_app k W

/-- **The comparison map of equation 076R along a morphism `k : X ⟶ U`**,
`k_small^*(x^*ℱ|_{U_étale}) ⟶ f^*ℱ|_{X_étale}`, for a 2-isomorphism `φ : x ∘ k ≅ f` over the
identity. -/
abbrev pointwisePresentationComparison {X : AlgebraicSpaces C S hS} (k : X ⟶ G.objects)
    (f : spaceCat X ⥤ 𝒳) (hf : (spaceProj X).IsFibredOneMorphism p f)
    (φ : spaceFunctor k ⋙ pointwisePresentationObject F ≅ f)
    (hφ : ∀ Z, p.IsHomLift (𝟙 (p.obj (f.obj Z))) (φ.inv.app Z))
    (ℱ : Space.inheritedEtaleModules.{u, v, w, u} C S hS p hp) :=
  Space.comparisonAlgebraicSpacesModules C S hS (spaceProj X) (spaceProj G.objects) p
    (isFiberedInGroupoids_spaceProj X) (isFiberedInGroupoids_objects G)
    (spacePresentation X) (spacePresentation G.objects) (spaceFunctor k) f
    (pointwisePresentationObject F) hf (isFibredOneMorphism_pointwisePresentationObject F hF hp)
    φ k (spaceFunctorChartIso k) hp hφ (isHomLift_objectsChartIso G k) ℱ

/-- Unfolding the comparison map along `k : X ⟶ U` as a comparison map of equation 076R. -/
theorem pointwisePresentationComparison_eq {X : AlgebraicSpaces C S hS} (k : X ⟶ G.objects)
    (f : spaceCat X ⥤ 𝒳) (hf : (spaceProj X).IsFibredOneMorphism p f)
    (φ : spaceFunctor k ⋙ pointwisePresentationObject F ≅ f)
    (hφ : ∀ Z, p.IsHomLift (𝟙 (p.obj (f.obj Z))) (φ.inv.app Z))
    (ℱ : Space.inheritedEtaleModules.{u, v, w, u} C S hS p hp) :
    pointwisePresentationComparison F hF k f hf φ hφ ℱ =
      Space.comparisonAlgebraicSpacesModules C S hS (spaceProj X) (spaceProj G.objects) p
        (isFiberedInGroupoids_spaceProj X) (isFiberedInGroupoids_objects G)
        (spacePresentation X) (spacePresentation G.objects) (spaceFunctor k) f
        (pointwisePresentationObject F) hf (isFibredOneMorphism_pointwisePresentationObject F hF hp)
        φ k (spaceFunctorChartIso k) hp hφ (isHomLift_objectsChartIso G k) ℱ := rfl

/-- The comparison map along `k : X ⟶ U` depends only on the components of the inverse of its
2-isomorphism `φ : x ∘ k ≅ f`. -/
theorem pointwisePresentationComparison_congr {X : AlgebraicSpaces C S hS} (k : X ⟶ G.objects)
    (f : spaceCat X ⥤ 𝒳) (hf : (spaceProj X).IsFibredOneMorphism p f)
    (φ φ' : spaceFunctor k ⋙ pointwisePresentationObject F ≅ f)
    (hφ : ∀ Z, p.IsHomLift (𝟙 (p.obj (f.obj Z))) (φ.inv.app Z))
    (hφ' : ∀ Z, p.IsHomLift (𝟙 (p.obj (f.obj Z))) (φ'.inv.app Z))
    (ℱ : Space.inheritedEtaleModules.{u, v, w, u} C S hS p hp)
    (h : ∀ Z, φ.inv.app Z = φ'.inv.app Z) :
    pointwisePresentationComparison F hF k f hf φ hφ ℱ =
      pointwisePresentationComparison F hF k f hf φ' hφ' ℱ := by
  rw [pointwisePresentationComparison_eq, pointwisePresentationComparison_eq]
  exact Space.comparisonAlgebraicSpacesModules_congr_of_faithful C S hS (spaceProj X)
    (spaceProj G.objects) p (isFiberedInGroupoids_spaceProj X) (isFiberedInGroupoids_objects G)
    hp (spacePresentation X) (spacePresentation G.objects) f (pointwisePresentationObject F) hf
    (isFibredOneMorphism_pointwisePresentationObject F hF hp) k (spaceFunctor k)
    (spaceFunctor k) rfl φ φ' (fun Z => by simp [h Z]) (spaceFunctorChartIso k)
    (spaceFunctorChartIso k) hφ hφ' (isHomLift_objectsChartIso G k)
    (isHomLift_objectsChartIso G k) ℱ

/-- The 2-isomorphism `x ∘ k₁ ≅ x ∘ k₂` attached to an equality `k₁ = k₂`. -/
abbrev pointwisePresentationTransportIso {X : AlgebraicSpaces C S hS} {k₁ k₂ : X ⟶ G.objects}
    (e : k₁ = k₂) :
    spaceFunctor k₁ ⋙ pointwisePresentationObject F ≅
      spaceFunctor k₂ ⋙ pointwisePresentationObject F :=
  eqToIso (congrArg (fun k => spaceFunctor k ⋙ pointwisePresentationObject F) e)

/-- **Transporting the comparison map along an equality of morphisms.** -/
theorem pullbackTransport_comp_pointwisePresentationComparison {X : AlgebraicSpaces C S hS}
    {k₁ k₂ : X ⟶ G.objects} (e : k₁ = k₂) (f : spaceCat X ⥤ 𝒳)
    (hf : (spaceProj X).IsFibredOneMorphism p f)
    (φ : spaceFunctor k₂ ⋙ pointwisePresentationObject F ≅ f)
    (hφ : ∀ Z, p.IsHomLift (𝟙 (p.obj (f.obj Z))) (φ.inv.app Z))
    (hφ' : ∀ Z, p.IsHomLift (𝟙 (p.obj (f.obj Z)))
      ((pointwisePresentationTransportIso F e ≪≫ φ).inv.app Z))
    (ℱ : Space.inheritedEtaleModules.{u, v, w, u} C S hS p hp) :
    Space.pullbackTransport (Space.etaleRestrictedModuleInverseImage C S hS (U := G.objects)
      (spaceProj G.objects) p
          (isFiberedInGroupoids_objects G) hp (spacePresentation G.objects)
          (pointwisePresentationObject F)
          (isFibredOneMorphism_pointwisePresentationObject F hF hp) ℱ) e ≫
            pointwisePresentationComparison F hF k₂ f hf φ hφ ℱ =
      pointwisePresentationComparison F hF k₁ f hf (pointwisePresentationTransportIso F e ≪≫ φ)
        hφ' ℱ := by
  subst e
  refine (Category.id_comp _).trans ?_
  exact Space.comparisonAlgebraicSpacesModules_congr_of_faithful C S hS (spaceProj X)
    (spaceProj G.objects) p (isFiberedInGroupoids_spaceProj X) (isFiberedInGroupoids_objects G)
    hp (spacePresentation X) (spacePresentation G.objects) f (pointwisePresentationObject F) hf
    (isFibredOneMorphism_pointwisePresentationObject F hF hp) k₁ (spaceFunctor k₁)
    (spaceFunctor k₁) rfl φ _ (fun Z => by simp) (spaceFunctorChartIso k₁)
    (spaceFunctorChartIso k₁) hφ hφ' (isHomLift_objectsChartIso G k₁)
    (isHomLift_objectsChartIso G k₁) ℱ

/-- If the components of `φ⁻¹` lie over identities, so do those of the inverse of the composite of
the transport 2-isomorphism `x ∘ k₁ ≅ x ∘ k₂` with `φ`. -/
theorem isHomLift_pointwisePresentationTransportIso_trans {X : AlgebraicSpaces C S hS}
    {k₁ k₂ : X ⟶ G.objects} (e : k₁ = k₂) {f : spaceCat X ⥤ 𝒳}
    (φ : spaceFunctor k₂ ⋙ pointwisePresentationObject F ≅ f)
    (hφ : ∀ Z, p.IsHomLift (𝟙 (p.obj (f.obj Z))) (φ.inv.app Z)) (Z : spaceCat X) :
    p.IsHomLift (𝟙 (p.obj (f.obj Z))) ((pointwisePresentationTransportIso F e ≪≫ φ).inv.app Z) := by
  have h2 : p.IsHomLift (𝟙 (p.obj ((spaceFunctor k₂ ⋙ pointwisePresentationObject F).obj Z)))
      ((pointwisePresentationTransportIso F e).inv.app Z) :=
    isHomLift_id_of_eq_eqToHom (Functor.congr_obj
      (congrArg (fun k => spaceFunctor k ⋙ pointwisePresentationObject F) e) Z).symm (by simp)
  rw [Iso.trans_inv, NatTrans.comp_app]
  exact Space.isHomLift_id_comp' p (hφ Z) h2

/-! ### Reindexing along a morphism into the arrow space -/

section Reindex

variable {X : AlgebraicSpaces C S hS} (y : X ⟶ G.arrows)

/-- The 1-morphism `y ⋙ x ∘ s : 𝒮_X ⥤ 𝒳`, the common target of the reindexed comparisons. -/
abbrev pointwisePresentationReindex : spaceCat X ⥤ 𝒳 :=
  spaceFunctor y ⋙ pointwisePresentationSource F

include hF in
/-- The 1-morphism `y ⋙ x ∘ s : 𝒮_X ⥤ 𝒳` is a 1-morphism of categories fibred in groupoids. -/
theorem isFibredOneMorphism_pointwisePresentationReindex (hp : p.IsFiberedInGroupoids) :
    (spaceProj X).IsFibredOneMorphism p (pointwisePresentationReindex F y) :=
  hp.isFibredOneMorphism (by
    rw [Functor.assoc, (isFibredOneMorphism_pointwisePresentationSource F hF hp).comp_eq]
    exact (associatedMap C S hS y.hom).1.hom.w)

/-- The components of the identity 2-morphism of `y ⋙ x ∘ s` lie over identities. -/
theorem isHomLift_pointwisePresentationReindex_refl (Z : spaceCat X) :
    p.IsHomLift (𝟙 (p.obj ((pointwisePresentationReindex F y).obj Z)))
      ((Iso.refl (pointwisePresentationReindex F y)).inv.app Z) :=
  Space.isHomLift_iso_refl_inv_app C S hS p (pointwisePresentationReindex F y) Z

/-- The components of the presentation of the 1-morphism attached to `y : X ⟶ R` lie over
identities. -/
theorem isHomLift_reindexChartIso (W : CostructuredArrow yoneda X.obj) :
    (spaceProj G.arrows).IsHomLift (𝟙 ((spaceProj G.arrows).obj ((spaceFunctor y).obj
      ((Space.schemeChartFunctor C S hS X.obj (spaceProj X) (spacePresentation X)).obj W))))
      ((spaceFunctorChartIso y).hom.app W) :=
  isHomLift_spaceFunctorChartIso_hom_app y W

/-- **The comparison map along a morphism into the arrow space**,
`y_small^*((x ∘ s)^*ℱ|_{R_étale}) ⟶ (y ⋙ x ∘ s)^*ℱ|_{X_étale}`. -/
abbrev pointwisePresentationArrowComparison
    (ℱ : Space.inheritedEtaleModules.{u, v, w, u} C S hS p hp) :=
  Space.comparisonAlgebraicSpacesModules C S hS (spaceProj X) (spaceProj G.arrows) p
    (isFiberedInGroupoids_spaceProj X) (isFiberedInGroupoids_arrows G)
    (spacePresentation X) (spacePresentation G.arrows) (spaceFunctor y)
    (pointwisePresentationReindex F y) (pointwisePresentationSource F)
    (isFibredOneMorphism_pointwisePresentationReindex F hF y hp)
    (isFibredOneMorphism_pointwisePresentationSource F hF hp)
    (Iso.refl (pointwisePresentationReindex F y)) y (spaceFunctorChartIso y) hp
    (isHomLift_pointwisePresentationReindex_refl F y) (isHomLift_reindexChartIso y) ℱ

/-- The 2-isomorphism `x ∘ (y ≫ s) ≅ y ⋙ x ∘ s`. -/
abbrev pointwisePresentationSourceReindexIso :
    spaceFunctor (y ≫ G.source) ⋙ pointwisePresentationObject F ≅
      pointwisePresentationReindex F y :=
  eqToIso (congrArg (· ⋙ pointwisePresentationObject F) (spaceFunctor_comp y G.source))

/-- The 2-isomorphism `x ∘ (y ≫ t) ≅ y ⋙ x ∘ s`, through the inverse of the canonical
2-morphism. -/
abbrev pointwisePresentationTargetReindexIso :
    spaceFunctor (y ≫ G.target) ⋙ pointwisePresentationObject F ≅
      pointwisePresentationReindex F y :=
  eqToIso (congrArg (· ⋙ pointwisePresentationObject F) (spaceFunctor_comp y G.target)) ≪≫
    Functor.isoWhiskerLeft (spaceFunctor y) (pointwisePresentationTwoIso F)

/-- The components of the inverse of `x ∘ (y ≫ t) ≅ y ⋙ x ∘ s` are those of the canonical
2-morphism at `y`, followed by a transport. -/
theorem pointwisePresentationTargetReindexIso_inv_app (Z : spaceCat X) :
    (pointwisePresentationTargetReindexIso F y).inv.app Z =
      (pointwisePresentationTwoArrow F).app ((spaceFunctor y).obj Z) ≫
        eqToHom (Functor.congr_obj (congrArg (· ⋙ pointwisePresentationObject F)
          (spaceFunctor_comp y G.target)) Z).symm := by
  simp

/-- The components of the inverse of `x ∘ (y ≫ s) ≅ y ⋙ x ∘ s` lie over identities. -/
theorem isHomLift_pointwisePresentationSourceReindexIso_inv_app (Z : spaceCat X) :
    p.IsHomLift (𝟙 (p.obj ((pointwisePresentationReindex F y).obj Z)))
      ((pointwisePresentationSourceReindexIso F y).inv.app Z) :=
  isHomLift_id_of_eq_eqToHom (Functor.congr_obj (congrArg (· ⋙ pointwisePresentationObject F)
    (spaceFunctor_comp y G.source)) Z).symm (by simp)

include hF in
/-- The components of the inverse of `x ∘ (y ≫ t) ≅ y ⋙ x ∘ s` lie over identities. -/
theorem isHomLift_pointwisePresentationTargetReindexIso_inv_app (Z : spaceCat X) :
    p.IsHomLift (𝟙 (p.obj ((pointwisePresentationReindex F y).obj Z)))
      ((pointwisePresentationTargetReindexIso F y).inv.app Z) := by
  rw [pointwisePresentationTargetReindexIso_inv_app]
  have : p.IsHomLift (𝟙 (p.obj ((pointwisePresentationReindex F y).obj Z)))
      ((pointwisePresentationTwoArrow F).app ((spaceFunctor y).obj Z)) :=
    isHomLift_pointwisePresentationTwoArrow_app F hF ((spaceFunctor y).obj Z)
  infer_instance

/-- The components of the presentation of the 1-morphism of `y ≫ s` lie over identities. -/
theorem isHomLift_sourceReindexChartIso (W : CostructuredArrow yoneda X.obj) :
    (spaceProj G.objects).IsHomLift (𝟙 ((spaceProj G.objects).obj ((spaceFunctor (y ≫ G.source)).obj
      ((Space.schemeChartFunctor C S hS X.obj (spaceProj X) (spacePresentation X)).obj W))))
      ((spaceFunctorChartIso (y ≫ G.source)).hom.app W) :=
  isHomLift_spaceFunctorChartIso_hom_app (y ≫ G.source) W

/-- The components of the presentation of the 1-morphism of `y ≫ t` lie over identities. -/
theorem isHomLift_targetReindexChartIso (W : CostructuredArrow yoneda X.obj) :
    (spaceProj G.objects).IsHomLift (𝟙 ((spaceProj G.objects).obj ((spaceFunctor (y ≫ G.target)).obj
      ((Space.schemeChartFunctor C S hS X.obj (spaceProj X) (spacePresentation X)).obj W))))
      ((spaceFunctorChartIso (y ≫ G.target)).hom.app W) :=
  isHomLift_spaceFunctorChartIso_hom_app (y ≫ G.target) W

/-- The comparison map `(y ≫ s)_small^*(x^*ℱ|_{U_étale}) ⟶ (y ⋙ x ∘ s)^*ℱ|_{X_étale}`. -/
abbrev pointwisePresentationSourceReindex
    (ℱ : Space.inheritedEtaleModules.{u, v, w, u} C S hS p hp) :=
  pointwisePresentationComparison F hF (y ≫ G.source) (pointwisePresentationReindex F y)
    (isFibredOneMorphism_pointwisePresentationReindex F hF y hp)
      (pointwisePresentationSourceReindexIso F y)
      (isHomLift_pointwisePresentationSourceReindexIso_inv_app F y) ℱ

/-- The comparison map `(y ≫ t)_small^*(x^*ℱ|_{U_étale}) ⟶ (y ⋙ x ∘ s)^*ℱ|_{X_étale}`, through the
inverse of the canonical 2-morphism. -/
abbrev pointwisePresentationTargetReindex
    (ℱ : Space.inheritedEtaleModules.{u, v, w, u} C S hS p hp) :=
  pointwisePresentationComparison F hF (y ≫ G.target) (pointwisePresentationReindex F y)
    (isFibredOneMorphism_pointwisePresentationReindex F hF y hp)
      (pointwisePresentationTargetReindexIso F y)
      (isHomLift_pointwisePresentationTargetReindexIso_inv_app F hF y) ℱ

/-- Unfolding the comparison map along `y` as a comparison map of equation 076R. -/
theorem pointwisePresentationArrowComparison_eq
    (ℱ : Space.inheritedEtaleModules.{u, v, w, u} C S hS p hp) :
    pointwisePresentationArrowComparison F hF y ℱ =
      Space.comparisonAlgebraicSpacesModules C S hS (spaceProj X) (spaceProj G.arrows) p
        (isFiberedInGroupoids_spaceProj X) (isFiberedInGroupoids_arrows G)
        (spacePresentation X) (spacePresentation G.arrows) (spaceFunctor y)
        (pointwisePresentationReindex F y) (pointwisePresentationSource F)
        (isFibredOneMorphism_pointwisePresentationReindex F hF y hp)
        (isFibredOneMorphism_pointwisePresentationSource F hF hp)
        (Iso.refl (pointwisePresentationReindex F y)) y (spaceFunctorChartIso y) hp
        (isHomLift_pointwisePresentationReindex_refl F y) (isHomLift_reindexChartIso y) ℱ := rfl

/-- Unfolding the comparison map along `y ≫ s` as a comparison map of equation 076R. -/
theorem pointwisePresentationSourceReindex_eq
    (ℱ : Space.inheritedEtaleModules.{u, v, w, u} C S hS p hp) :
    pointwisePresentationSourceReindex F hF y ℱ =
      Space.comparisonAlgebraicSpacesModules C S hS (spaceProj X) (spaceProj G.objects) p
        (isFiberedInGroupoids_spaceProj X) (isFiberedInGroupoids_objects G)
        (spacePresentation X) (spacePresentation G.objects) (spaceFunctor (y ≫ G.source))
        (pointwisePresentationReindex F y) (pointwisePresentationObject F)
        (isFibredOneMorphism_pointwisePresentationReindex F hF y hp)
        (isFibredOneMorphism_pointwisePresentationObject F hF hp)
        (pointwisePresentationSourceReindexIso F y) (y ≫ G.source)
        (spaceFunctorChartIso (y ≫ G.source)) hp
        (isHomLift_pointwisePresentationSourceReindexIso_inv_app F y)
        (isHomLift_objectsChartIso G (y ≫ G.source)) ℱ := rfl

/-- Unfolding the comparison map along `y ≫ t` as a comparison map of equation 076R. -/
theorem pointwisePresentationTargetReindex_eq
    (ℱ : Space.inheritedEtaleModules.{u, v, w, u} C S hS p hp) :
    pointwisePresentationTargetReindex F hF y ℱ =
      Space.comparisonAlgebraicSpacesModules C S hS (spaceProj X) (spaceProj G.objects) p
        (isFiberedInGroupoids_spaceProj X) (isFiberedInGroupoids_objects G)
        (spacePresentation X) (spacePresentation G.objects) (spaceFunctor (y ≫ G.target))
        (pointwisePresentationReindex F y) (pointwisePresentationObject F)
        (isFibredOneMorphism_pointwisePresentationReindex F hF y hp)
        (isFibredOneMorphism_pointwisePresentationObject F hF hp)
        (pointwisePresentationTargetReindexIso F y) (y ≫ G.target)
        (spaceFunctorChartIso (y ≫ G.target)) hp
        (isHomLift_pointwisePresentationTargetReindexIso_inv_app F hF y)
        (isHomLift_objectsChartIso G (y ≫ G.target)) ℱ := rfl

/-- The composition law of Stacks 075D (1) for the comparison map through a morphism `g` out of
the arrow space with a 2-isomorphism `ρ : x ∘ g ≅ x ∘ s`, reindexed along `y`. -/
private theorem modulePullback_comparison_comp (g : G.arrows ⟶ G.objects)
    (ρ : spaceFunctor g ⋙ pointwisePresentationObject F ≅ pointwisePresentationSource F)
    (hρ : ∀ Z, p.IsHomLift (𝟙 (p.obj ((pointwisePresentationSource F).obj Z))) (ρ.inv.app Z))
    (ε : spaceFunctor (y ≫ g) ⋙ pointwisePresentationObject F ≅ pointwisePresentationReindex F y)
    (hε : ε = eqToIso (congrArg (· ⋙ pointwisePresentationObject F) (spaceFunctor_comp y g)) ≪≫
      Functor.isoWhiskerLeft (spaceFunctor y) ρ)
    (hε' : ∀ Z, p.IsHomLift (𝟙 (p.obj ((pointwisePresentationReindex F y).obj Z)))
      (ε.inv.app Z))
    (ℱ : Space.inheritedEtaleModules.{u, v, w, u} C S hS p hp) :
    (Space.modulePullback C S hS y).map (pointwisePresentationComparison F hF g
        (pointwisePresentationSource F) (isFibredOneMorphism_pointwisePresentationSource F hF hp)
        ρ hρ ℱ) ≫ pointwisePresentationArrowComparison F hF y ℱ =
      (Space.modulePullbackCompIso C S hS y g).hom.app
          (Space.etaleRestrictedModuleInverseImage C S hS (U := G.objects) (spaceProj G.objects) p
            (isFiberedInGroupoids_objects G) hp (spacePresentation G.objects)
            (pointwisePresentationObject F)
            (isFibredOneMorphism_pointwisePresentationObject F hF hp) ℱ) ≫
        pointwisePresentationComparison F hF (y ≫ g) (pointwisePresentationReindex F y)
          (isFibredOneMorphism_pointwisePresentationReindex F hF y hp) ε hε' ℱ := by
  have H3 := Space.comparisonAlgebraicSpacesModules_comp_compTriangleIso C S hS (spaceProj X)
    (spaceProj G.arrows) (spaceProj G.objects) p (isFiberedInGroupoids_spaceProj X)
    (isFiberedInGroupoids_arrows G) (isFiberedInGroupoids_objects G)
    hp (spacePresentation X) (spacePresentation G.arrows) (spacePresentation G.objects)
    (spaceFunctor y) (spaceFunctor g) (pointwisePresentationReindex F y)
    (pointwisePresentationSource F) (pointwisePresentationObject F)
    (isFibredOneMorphism_spaceFunctor g)
    (isFibredOneMorphism_pointwisePresentationReindex F hF y hp)
    (isFibredOneMorphism_pointwisePresentationSource F hF hp)
    (isFibredOneMorphism_pointwisePresentationObject F hF hp)
    (Iso.refl (pointwisePresentationReindex F y)) ρ
    y g (spaceFunctorChartIso y) (spaceFunctorChartIso g)
    (isHomLift_pointwisePresentationReindex_refl F y) hρ
    (isHomLift_reindexChartIso y) (isHomLift_objectsChartIso G g) ℱ
  have CL := Space.comparisonAlgebraicSpacesModules_congr_of_faithful C S hS (spaceProj X)
    (spaceProj G.objects) p (isFiberedInGroupoids_spaceProj X) (isFiberedInGroupoids_objects G)
    hp (spacePresentation X) (spacePresentation G.objects) (pointwisePresentationReindex F y)
    (pointwisePresentationObject F) (isFibredOneMorphism_pointwisePresentationReindex F hF y hp)
    (isFibredOneMorphism_pointwisePresentationObject F hF hp) (y ≫ g)
    (spaceFunctor y ⋙ spaceFunctor g) (spaceFunctor (y ≫ g))
    (spaceFunctor_comp y g).symm
    (Space.compTriangleIso (spaceFunctor y) (spaceFunctor g)
      (pointwisePresentationReindex F y) (pointwisePresentationSource F)
      (pointwisePresentationObject F) (Iso.refl (pointwisePresentationReindex F y)) ρ)
    ε (fun Z => by simp [hε, eqToHom_map])
    (Space.comparisonChartFunctorIsoComp C S hS (spaceProj X) (spaceProj G.arrows)
      (spaceProj G.objects) (spacePresentation X) (spacePresentation G.arrows)
      (spacePresentation G.objects) (spaceFunctor y) (spaceFunctor g) y g
      (spaceFunctorChartIso y) (spaceFunctorChartIso g))
    (spaceFunctorChartIso (y ≫ g))
    (Space.isHomLift_compTriangleIso_inv_app C S hS p (spaceFunctor y) (spaceFunctor g)
      (pointwisePresentationReindex F y) (pointwisePresentationSource F)
      (pointwisePresentationObject F) (Iso.refl (pointwisePresentationReindex F y)) ρ
      (isHomLift_pointwisePresentationReindex_refl F y) hρ)
    hε'
    (isHomLift_comparisonChartFunctorIsoComp y g) (isHomLift_objectsChartIso G (y ≫ g)) ℱ
  rw [CL] at H3
  rw [pointwisePresentationComparison_eq, pointwisePresentationComparison_eq,
    pointwisePresentationArrowComparison_eq]
  exact H3

/-- The composition law of Stacks 075D (1) for the comparison map through the source. -/
theorem pointwisePresentationSourceComparison_comp
    (ℱ : Space.inheritedEtaleModules.{u, v, w, u} C S hS p hp) :
    (Space.modulePullback C S hS y).map (pointwisePresentationSourceComparison F hF ℱ) ≫
        pointwisePresentationArrowComparison F hF y ℱ =
      (Space.modulePullbackCompIso C S hS y G.source).hom.app
          (Space.etaleRestrictedModuleInverseImage C S hS (U := G.objects) (spaceProj G.objects) p
            (isFiberedInGroupoids_objects G) hp (spacePresentation G.objects)
            (pointwisePresentationObject F)
            (isFibredOneMorphism_pointwisePresentationObject F hF hp) ℱ) ≫
        pointwisePresentationSourceReindex F hF y ℱ := by
  exact modulePullback_comparison_comp F hF y G.source (Iso.refl _)
    (isHomLift_pointwisePresentationSource_refl F) (pointwisePresentationSourceReindexIso F y)
    (by ext; simp) (isHomLift_pointwisePresentationSourceReindexIso_inv_app F y) ℱ

/-- The composition law of Stacks 075D (1) for the comparison map through the target. -/
theorem pointwisePresentationTargetComparison_comp
    (ℱ : Space.inheritedEtaleModules.{u, v, w, u} C S hS p hp) :
    (Space.modulePullback C S hS y).map (pointwisePresentationTargetComparison F hF ℱ) ≫
        pointwisePresentationArrowComparison F hF y ℱ =
      (Space.modulePullbackCompIso C S hS y G.target).hom.app
          (Space.etaleRestrictedModuleInverseImage C S hS (U := G.objects) (spaceProj G.objects) p
            (isFiberedInGroupoids_objects G) hp (spacePresentation G.objects)
            (pointwisePresentationObject F)
            (isFibredOneMorphism_pointwisePresentationObject F hF hp) ℱ) ≫
        pointwisePresentationTargetReindex F hF y ℱ := by
  exact modulePullback_comparison_comp F hF y G.target (pointwisePresentationTwoIso F)
    (isHomLift_pointwisePresentationTwoIso_inv_app F hF) (pointwisePresentationTargetReindexIso F y)
    rfl (isHomLift_pointwisePresentationTargetReindexIso_inv_app F hF y) ℱ

omit [Category.{w} 𝒳] in
/-- If `e₁' ≫ e₁ = 𝟙`, `m ≫ σ = τ`, `σ ≫ c = e₂ ≫ Q₂` and `τ ≫ c = e₁ ≫ Q₁`, then
`(e₁' ≫ m ≫ e₂) ≫ Q₂ = Q₁`. -/
theorem comp_reindex_aux {𝒞 : Type*} [Category 𝒞] {A₁ B₁ A₂ B₂ M N : 𝒞} (e₁ : B₁ ⟶ A₁)
    (e₁' : A₁ ⟶ B₁) (he : e₁' ≫ e₁ = 𝟙 A₁) (e₂ : B₂ ⟶ A₂) (m : B₁ ⟶ B₂) (σ : B₂ ⟶ M)
    (τ : B₁ ⟶ M) (c : M ⟶ N) (Q₂ : A₂ ⟶ N) (Q₁ : A₁ ⟶ N) (hm : m ≫ σ = τ)
    (h₂ : σ ≫ c = e₂ ≫ Q₂) (h₁ : τ ≫ c = e₁ ≫ Q₁) :
    (e₁' ≫ m ≫ e₂) ≫ Q₂ = Q₁ := by
  rw [Category.assoc, Category.assoc, ← h₂, reassoc_of% hm, h₁, reassoc_of% he]

/-- **Reindexing the transition morphism along a morphism into the arrow space.**  If
`α : t^*(x^*ℱ|_U) ⟶ s^*(x^*ℱ|_U)` satisfies `α ≫ c_s = c_t` for the two comparison maps of the
presentation, then its reindexing along `y : X ⟶ R` satisfies the same equation for the
reindexed comparison maps. -/
theorem groupoidPullbackTransition_comp_pointwisePresentationSourceReindex
    (ℱ : Space.inheritedEtaleModules.{u, v, w, u} C S hS p hp)
    (α : (Space.modulePullback C S hS G.target).obj (Space.etaleRestrictedModuleInverseImage C S hS
      (U := G.objects) (spaceProj G.objects) p
          (isFiberedInGroupoids_objects G) hp (spacePresentation G.objects)
          (pointwisePresentationObject F)
          (isFibredOneMorphism_pointwisePresentationObject F hF hp) ℱ) ⟶
      (Space.modulePullback C S hS G.source).obj (Space.etaleRestrictedModuleInverseImage C S hS
        (U := G.objects) (spaceProj G.objects) p
          (isFiberedInGroupoids_objects G) hp (spacePresentation G.objects)
          (pointwisePresentationObject F)
          (isFibredOneMorphism_pointwisePresentationObject F hF hp) ℱ))
    (hα : α ≫ pointwisePresentationSourceComparison F hF ℱ =
      pointwisePresentationTargetComparison F hF ℱ) :
    Space.groupoidPullbackTransition C S hS G (Space.etaleRestrictedModuleInverseImage C S hS
      (U := G.objects) (spaceProj G.objects) p
          (isFiberedInGroupoids_objects G) hp (spacePresentation G.objects)
          (pointwisePresentationObject F)
          (isFibredOneMorphism_pointwisePresentationObject F hF hp) ℱ) α y ≫
        pointwisePresentationSourceReindex F hF y ℱ =
      pointwisePresentationTargetReindex F hF y ℱ := by
  have hm : (Space.modulePullback C S hS y).map α ≫
      (Space.modulePullback C S hS y).map (pointwisePresentationSourceComparison F hF ℱ) =
      (Space.modulePullback C S hS y).map (pointwisePresentationTargetComparison F hF ℱ) := by
    rw [← Functor.map_comp, hα]
  exact comp_reindex_aux ((Space.modulePullbackCompIso C S hS y G.target).hom.app
      (Space.etaleRestrictedModuleInverseImage C S hS (U := G.objects) (spaceProj G.objects) p
          (isFiberedInGroupoids_objects G) hp (spacePresentation G.objects)
          (pointwisePresentationObject F)
          (isFibredOneMorphism_pointwisePresentationObject F hF hp) ℱ))
    ((Space.modulePullbackCompIso C S hS y G.target).inv.app
      (Space.etaleRestrictedModuleInverseImage C S hS (U := G.objects) (spaceProj G.objects) p
          (isFiberedInGroupoids_objects G) hp (spacePresentation G.objects)
          (pointwisePresentationObject F)
          (isFibredOneMorphism_pointwisePresentationObject F hF hp) ℱ))
    ((Space.modulePullbackCompIso C S hS y G.target).inv_hom_id_app
      (Space.etaleRestrictedModuleInverseImage C S hS (U := G.objects) (spaceProj G.objects) p
          (isFiberedInGroupoids_objects G) hp (spacePresentation G.objects)
          (pointwisePresentationObject F)
          (isFibredOneMorphism_pointwisePresentationObject F hF hp) ℱ))
    ((Space.modulePullbackCompIso C S hS y G.source).hom.app
      (Space.etaleRestrictedModuleInverseImage C S hS (U := G.objects) (spaceProj G.objects) p
          (isFiberedInGroupoids_objects G) hp (spacePresentation G.objects)
          (pointwisePresentationObject F)
          (isFibredOneMorphism_pointwisePresentationObject F hF hp) ℱ))
    ((Space.modulePullback C S hS y).map α)
    ((Space.modulePullback C S hS y).map (pointwisePresentationSourceComparison F hF ℱ))
    ((Space.modulePullback C S hS y).map (pointwisePresentationTargetComparison F hF ℱ))
    (pointwisePresentationArrowComparison F hF y ℱ) (pointwisePresentationSourceReindex F hF y ℱ)
    (pointwisePresentationTargetReindex F hF y ℱ) hm
    (pointwisePresentationSourceComparison_comp F hF y ℱ)
    (pointwisePresentationTargetComparison_comp F hF y ℱ)

include hF in
/-- If the components of `ψ⁻¹` lie over identities, so do those of the inverse of the composite
`x ∘ (y ≫ t) ≅ y ⋙ x ∘ s ≅ x ∘ (y ≫ s) ≅ f`. -/
theorem isHomLift_pointwisePresentationReindexTrans {f : spaceCat X ⥤ 𝒳}
    (ψ : spaceFunctor (y ≫ G.source) ⋙ pointwisePresentationObject F ≅ f)
    (hψ : ∀ Z, p.IsHomLift (𝟙 (p.obj (f.obj Z))) (ψ.inv.app Z)) (Z : spaceCat X) :
    p.IsHomLift (𝟙 (p.obj (f.obj Z)))
      ((pointwisePresentationTargetReindexIso F y ≪≫
        (pointwisePresentationSourceReindexIso F y).symm ≪≫ ψ).inv.app Z) := by
  have h2 : p.IsHomLift (𝟙 (p.obj ((spaceFunctor (y ≫ G.source) ⋙
      pointwisePresentationObject F).obj Z)))
      ((pointwisePresentationSourceReindexIso F y).hom.app Z) :=
    isHomLift_id_of_eq_eqToHom (Functor.congr_obj (congrArg (· ⋙ pointwisePresentationObject F)
      (spaceFunctor_comp y G.source)) Z) (by simp)
  have h3 := isHomLift_pointwisePresentationTargetReindexIso_inv_app F hF y Z
  have e : (pointwisePresentationTargetReindexIso F y ≪≫
        (pointwisePresentationSourceReindexIso F y).symm ≪≫ ψ).inv.app Z =
      (ψ.inv.app Z ≫ (pointwisePresentationSourceReindexIso F y).hom.app Z) ≫
        (pointwisePresentationTargetReindexIso F y).inv.app Z := rfl
  rw [e]
  exact Space.isHomLift_id_comp' p (Space.isHomLift_id_comp' p (hψ Z) h2) h3

/-- **The reindexed transition equation, for an arbitrary target.** -/
theorem groupoidPullbackTransition_comp_pointwisePresentationComparison
    (ℱ : Space.inheritedEtaleModules.{u, v, w, u} C S hS p hp)
    (α : (Space.modulePullback C S hS G.target).obj (Space.etaleRestrictedModuleInverseImage C S hS
      (U := G.objects) (spaceProj G.objects) p
          (isFiberedInGroupoids_objects G) hp (spacePresentation G.objects)
          (pointwisePresentationObject F)
          (isFibredOneMorphism_pointwisePresentationObject F hF hp) ℱ) ⟶
      (Space.modulePullback C S hS G.source).obj (Space.etaleRestrictedModuleInverseImage C S hS
        (U := G.objects) (spaceProj G.objects) p
          (isFiberedInGroupoids_objects G) hp (spacePresentation G.objects)
          (pointwisePresentationObject F)
          (isFibredOneMorphism_pointwisePresentationObject F hF hp) ℱ))
    (hα : α ≫ pointwisePresentationSourceComparison F hF ℱ =
      pointwisePresentationTargetComparison F hF ℱ)
    (f : spaceCat X ⥤ 𝒳) (hf : (spaceProj X).IsFibredOneMorphism p f)
    (ψ : spaceFunctor (y ≫ G.source) ⋙ pointwisePresentationObject F ≅ f)
    (hψ : ∀ Z, p.IsHomLift (𝟙 (p.obj (f.obj Z))) (ψ.inv.app Z))
    (hψ' : ∀ Z, p.IsHomLift (𝟙 (p.obj (f.obj Z)))
      ((pointwisePresentationTargetReindexIso F y ≪≫
        (pointwisePresentationSourceReindexIso F y).symm ≪≫ ψ).inv.app Z)) :
    Space.groupoidPullbackTransition C S hS G (Space.etaleRestrictedModuleInverseImage C S hS
      (U := G.objects) (spaceProj G.objects) p
          (isFiberedInGroupoids_objects G) hp (spacePresentation G.objects)
          (pointwisePresentationObject F)
          (isFibredOneMorphism_pointwisePresentationObject F hF hp) ℱ) α y ≫
        pointwisePresentationComparison F hF (y ≫ G.source) f hf ψ hψ ℱ =
      pointwisePresentationComparison F hF (y ≫ G.target) f hf
        (pointwisePresentationTargetReindexIso F y ≪≫
          (pointwisePresentationSourceReindexIso F y).symm ≪≫ ψ) hψ' ℱ := by
  have ht : ∀ Z, p.IsHomLift (𝟙 (p.obj (f.obj Z)))
      ((ψ.inv ≫ (pointwisePresentationSourceReindexIso F y).hom).app Z) := fun Z => by
    have h1 := hψ Z
    have h2 : p.IsHomLift (𝟙 (p.obj ((spaceFunctor (y ≫ G.source) ⋙
        pointwisePresentationObject F).obj Z)))
        ((pointwisePresentationSourceReindexIso F y).hom.app Z) :=
      isHomLift_id_of_eq_eqToHom (Functor.congr_obj (congrArg (· ⋙ pointwisePresentationObject F)
        (spaceFunctor_comp y G.source)) Z) (by simp)
    rw [NatTrans.comp_app]
    exact Space.isHomLift_id_comp' p h1 h2
  have Ls := Space.comparisonAlgebraicSpacesModules_twoMorphism C S hS (spaceProj X)
    (spaceProj G.objects) p (isFiberedInGroupoids_spaceProj X) (isFiberedInGroupoids_objects G)
    hp (spacePresentation X) (spacePresentation G.objects) (pointwisePresentationReindex F y) f
    (isFibredOneMorphism_pointwisePresentationReindex F hF y hp) hf
    (ψ.inv ≫ (pointwisePresentationSourceReindexIso F y).hom) ht (spaceFunctor (y ≫ G.source))
    (pointwisePresentationObject F) (isFibredOneMorphism_pointwisePresentationObject F hF hp)
    (pointwisePresentationSourceReindexIso F y) ψ (y ≫ G.source)
    (spaceFunctorChartIso (y ≫ G.source))
    (isHomLift_pointwisePresentationSourceReindexIso_inv_app F y) hψ
    (isHomLift_objectsChartIso G (y ≫ G.source)) (by simp) ℱ
  have Lt := Space.comparisonAlgebraicSpacesModules_twoMorphism C S hS (spaceProj X)
    (spaceProj G.objects) p (isFiberedInGroupoids_spaceProj X) (isFiberedInGroupoids_objects G)
    hp (spacePresentation X) (spacePresentation G.objects) (pointwisePresentationReindex F y) f
    (isFibredOneMorphism_pointwisePresentationReindex F hF y hp) hf
    (ψ.inv ≫ (pointwisePresentationSourceReindexIso F y).hom) ht (spaceFunctor (y ≫ G.target))
    (pointwisePresentationObject F) (isFibredOneMorphism_pointwisePresentationObject F hF hp)
    (pointwisePresentationTargetReindexIso F y)
    (pointwisePresentationTargetReindexIso F y ≪≫
      (pointwisePresentationSourceReindexIso F y).symm ≪≫ ψ) (y ≫ G.target)
    (spaceFunctorChartIso (y ≫ G.target))
    (isHomLift_pointwisePresentationTargetReindexIso_inv_app F hF y) hψ'
    (isHomLift_objectsChartIso G (y ≫ G.target)) (by simp) ℱ
  have K := groupoidPullbackTransition_comp_pointwisePresentationSourceReindex F hF y ℱ α hα
  rw [pointwisePresentationSourceReindex_eq] at K
  rw [pointwisePresentationTargetReindex_eq] at K
  rw [pointwisePresentationComparison_eq, pointwisePresentationComparison_eq, Ls, Lt,
    ← Category.assoc, K]

/-- The reindexed comparison map through the source is the comparison map along `y ≫ s`. -/
theorem pointwisePresentationSourceReindex_eq_comparison
    (ℱ : Space.inheritedEtaleModules.{u, v, w, u} C S hS p hp) :
    pointwisePresentationSourceReindex F hF y ℱ =
      pointwisePresentationComparison F hF (y ≫ G.source) (pointwisePresentationReindex F y)
        (isFibredOneMorphism_pointwisePresentationReindex F hF y hp)
        (pointwisePresentationSourceReindexIso F y)
        (isHomLift_pointwisePresentationSourceReindexIso_inv_app F y) ℱ := rfl

/-- The reindexed comparison map through the target is the comparison map along `y ≫ t`. -/
theorem pointwisePresentationTargetReindex_eq_comparison
    (ℱ : Space.inheritedEtaleModules.{u, v, w, u} C S hS p hp) :
    pointwisePresentationTargetReindex F hF y ℱ =
      pointwisePresentationComparison F hF (y ≫ G.target) (pointwisePresentationReindex F y)
        (isFibredOneMorphism_pointwisePresentationReindex F hF y hp)
        (pointwisePresentationTargetReindexIso F y)
        (isHomLift_pointwisePresentationTargetReindexIso_inv_app F hF y) ℱ := rfl

/-- The reindexed comparison through the source is invertible as soon as the comparison through
the source and the comparison along `y` are. -/
theorem isIso_pointwisePresentationSourceReindex
    (ℱ : Space.inheritedEtaleModules.{u, v, w, u} C S hS p hp)
    [IsIso (pointwisePresentationSourceComparison F hF ℱ)]
    [IsIso (pointwisePresentationArrowComparison F hF y ℱ)] :
    IsIso (pointwisePresentationSourceReindex F hF y ℱ) := by
  have h := pointwisePresentationSourceComparison_comp F hF y ℱ
  have : IsIso ((Space.modulePullbackCompIso C S hS y G.source).hom.app
      (Space.etaleRestrictedModuleInverseImage C S hS (U := G.objects) (spaceProj G.objects) p
          (isFiberedInGroupoids_objects G) hp (spacePresentation G.objects)
          (pointwisePresentationObject F)
          (isFibredOneMorphism_pointwisePresentationObject F hF hp) ℱ) ≫
      pointwisePresentationSourceReindex F hF y ℱ) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_left ((Space.modulePullbackCompIso C S hS y G.source).hom.app
      (Space.etaleRestrictedModuleInverseImage C S hS (U := G.objects) (spaceProj G.objects) p
          (isFiberedInGroupoids_objects G) hp (spacePresentation G.objects)
          (pointwisePresentationObject F)
          (isFibredOneMorphism_pointwisePresentationObject F hF hp) ℱ)) _

end Reindex

/-- The vertical morphism attached to an arrow `r` depends only on `r`. -/
theorem vertHom_congr' (T : BigFppfOver C S hS) {a b : G.objects.obj.obj (op T)}
    {r r' : G.arrows.obj.obj (op T)} (h : r = r') (hs : G.source.hom.app (op T) r = a)
    (ht : G.target.hom.app (op T) r = b) (hs' : G.source.hom.app (op T) r' = a)
    (ht' : G.target.hom.app (op T) r' = b) :
    vertHom G T r hs ht = vertHom G T r' hs' ht' := by
  subst h
  rfl

/-- At a unit arrow, the image of the canonical 2-arrow is a transport. -/
theorem pointwisePresentationTwoArrow_app_identityArrow (Z : spaceCat G.objects) :
    ∃ H, (pointwisePresentationTwoArrow F).app
        ((spaceFunctor (GroupoidInAlgebraicSpaces.identityArrow G)).obj Z) = eqToHom H := by
  have hs := source_identity G Z.base Z.fiber.as
  have ht := target_identity G Z.base Z.fiber.as
  have hid := GroupoidInAlgebraicSpaces.identityArrow_hom_app G (op Z.base) Z.fiber.as
  have hs1 : G.source.hom.app (op Z.base) (G.toGroupoidInFunctors.identity (op Z.base) Z.fiber.as) =
      G.source.hom.app (op Z.base)
        ((GroupoidInAlgebraicSpaces.identityArrow G).hom.app (op Z.base) Z.fiber.as) :=
    congrArg _ hid.symm
  have ht1 : G.target.hom.app (op Z.base) (G.toGroupoidInFunctors.identity (op Z.base) Z.fiber.as) =
      G.target.hom.app (op Z.base)
        ((GroupoidInAlgebraicSpaces.identityArrow G).hom.app (op Z.base) Z.fiber.as) :=
    congrArg _ hid.symm
  have E : G.source.hom.app (op Z.base)
        ((GroupoidInAlgebraicSpaces.identityArrow G).hom.app (op Z.base) Z.fiber.as) =
      G.target.hom.app (op Z.base)
        ((GroupoidInAlgebraicSpaces.identityArrow G).hom.app (op Z.base) Z.fiber.as) :=
    hs1.symm.trans (hs.trans (ht.symm.trans ht1))
  refine ⟨congrArg F.obj (congrArg (fun z => (⟨Z.base, z⟩ : PointwiseFibration G)) E), ?_⟩
  show F.map (vertHom G Z.base
    ((GroupoidInAlgebraicSpaces.identityArrow G).hom.app (op Z.base) Z.fiber.as) rfl rfl) = _
  rw [vertHom_congr' Z.base hid rfl rfl hs1 ht1,
    vertHom_identity G Z.base Z.fiber.as hs1 ht1 E]
  exact eqToHom_map F _

omit [Category.{w} 𝒳] in
/-- At a point of the space of composable pairs, the composition is the pointwise composite. -/
theorem comp_hom_app_eq_compose (T : BigFppfOver C S hS)
    (pt : (AlgebraicSpaces.fiberProduct C S hS G.source G.target).obj.obj (op T)) :
    G.comp.hom.app (op T) pt = G.toGroupoidInFunctors.compose (op T)
      ((GroupoidInAlgebraicSpaces.firstArrow G).hom.app (op T) pt)
      ((GroupoidInAlgebraicSpaces.secondArrow G).hom.app (op T) pt)
      (congrArg (fun m => m.hom.app (op T) pt)
        (GroupoidInAlgebraicSpaces.firstArrow_comp_source G) :) := by
  have key := congrArg (fun m => m.app (op T) pt)
    (pullbackToComposable_comp_composableToPullback G.source.hom G.target.hom)
  change (composableToPullback G.source.hom G.target.hom).app (op T)
    ((pullbackToComposable G.source.hom G.target.hom).app (op T) pt) = pt at key
  have h1 := congrArg (fun m => m.app (op T) pt)
    (pullbackToComposable_comp_composableFst G.source.hom G.target.hom)
  have h2 := congrArg (fun m => m.app (op T) pt)
    (pullbackToComposable_comp_composableSnd G.source.hom G.target.hom)
  change ((pullbackToComposable G.source.hom G.target.hom).app (op T) pt).1.1 = _ at h1
  change ((pullbackToComposable G.source.hom G.target.hom).app (op T) pt).1.2 = _ at h2
  show G.comp.hom.app (op T) pt = G.comp.hom.app (op T)
    ((composableToPullback G.source.hom G.target.hom).app (op T) ⟨(_, _), _⟩)
  conv_lhs => rw [← key]
  congr 2

/-- The canonical 2-arrows compose along a composable pair, at the level of the pointwise
groupoid fibration. -/
theorem vertHom_eq_comp_of_compose (T : BigFppfOver C S hS) (a b c : G.arrows.obj.obj (op T))
    (h : G.source.hom.app (op T) a = G.target.hom.app (op T) b)
    (hc : c = G.toGroupoidInFunctors.compose (op T) a b h)
    (e₁ : G.source.hom.app (op T) c = G.source.hom.app (op T) b)
    (e₃ : G.target.hom.app (op T) a = G.target.hom.app (op T) c) :
    vertHom G T c rfl rfl =
      eqToHom (congrArg (fun z => (⟨T, z⟩ : PointwiseFibration G)) e₁) ≫ vertHom G T b rfl rfl ≫
        eqToHom (congrArg (fun z => (⟨T, z⟩ : PointwiseFibration G)) h.symm) ≫
          vertHom G T a rfl rfl ≫
            eqToHom (congrArg (fun z => (⟨T, z⟩ : PointwiseFibration G)) e₃) := by
  rw [vertHom_comp_eqToHom G T e₃ a, eqToHom_comp_vertHom G T h.symm a, ← Category.assoc,
    eqToHom_comp_vertHom G T e₁ b]
  have hs'' : G.source.hom.app (op T) (G.toGroupoidInFunctors.compose (op T) a b h) =
      G.source.hom.app (op T) c := hc ▸ rfl
  have ht'' : G.target.hom.app (op T) (G.toGroupoidInFunctors.compose (op T) a b h) =
      G.target.hom.app (op T) c := hc ▸ rfl
  exact (vertHom_congr' T hc rfl rfl hs'' ht'').trans
    (vertHom_comp_vertHom G T b a _ _ _ _ hs'' ht'').symm

/-- At a composable pair, the canonical 2-arrows compose. -/
theorem pointwisePresentationTwoArrow_app_comp
    (Z : spaceCat (AlgebraicSpaces.fiberProduct C S hS G.source G.target)) :
    ∃ H₁ H₂ H₃, (pointwisePresentationTwoArrow F).app ((spaceFunctor G.comp).obj Z) =
      eqToHom H₁ ≫ (pointwisePresentationTwoArrow F).app
          ((spaceFunctor (GroupoidInAlgebraicSpaces.secondArrow G)).obj Z) ≫
        eqToHom H₂ ≫ (pointwisePresentationTwoArrow F).app
          ((spaceFunctor (GroupoidInAlgebraicSpaces.firstArrow G)).obj Z) ≫ eqToHom H₃ := by
  have h := congrArg (fun m => m.hom.app (op Z.base) Z.fiber.as)
    (GroupoidInAlgebraicSpaces.firstArrow_comp_source G)
  have e₁ := congrArg (fun m => m.hom.app (op Z.base) Z.fiber.as)
    (GroupoidInAlgebraicSpaces.comp_comp_source G)
  have e₃ := congrArg (fun m => m.hom.app (op Z.base) Z.fiber.as)
    (GroupoidInAlgebraicSpaces.comp_comp_target G).symm
  have hP := vertHom_eq_comp_of_compose Z.base _ _ _ h
    (comp_hom_app_eq_compose Z.base Z.fiber.as) e₁ e₃
  refine ⟨congrArg F.obj (congrArg (fun z => (⟨Z.base, z⟩ : PointwiseFibration G)) e₁),
    congrArg F.obj (congrArg (fun z => (⟨Z.base, z⟩ : PointwiseFibration G)) h.symm),
    congrArg F.obj (congrArg (fun z => (⟨Z.base, z⟩ : PointwiseFibration G)) e₃), ?_⟩
  show F.map (vertHom G Z.base (G.comp.hom.app (op Z.base) Z.fiber.as) rfl rfl) =
    eqToHom _ ≫ F.map (vertHom G Z.base
      ((GroupoidInAlgebraicSpaces.secondArrow G).hom.app (op Z.base) Z.fiber.as) rfl rfl) ≫
      eqToHom _ ≫ F.map (vertHom G Z.base
        ((GroupoidInAlgebraicSpaces.firstArrow G).hom.app (op Z.base) Z.fiber.as) rfl rfl) ≫
        eqToHom _
  rw [hP]
  refine (F.map_comp _ _).trans (congrArg₂ (· ≫ ·) (eqToHom_map F _) ?_)
  refine (F.map_comp _ _).trans (congrArg₂ (· ≫ ·) rfl ?_)
  refine (F.map_comp _ _).trans (congrArg₂ (· ≫ ·) (eqToHom_map F _) ?_)
  exact (F.map_comp _ _).trans (congrArg₂ (· ≫ ·) rfl (eqToHom_map F _))

/-! ### The comparison map along the identity -/

/-- **The comparison map along the identity of the object space is an isomorphism**, for a
2-isomorphism `x ≅ f` whose components are transports. -/
theorem isIso_pointwisePresentationComparison_id (f : spaceCat G.objects ⥤ 𝒳)
    (h : f = pointwisePresentationObject F) (hf : (spaceProj G.objects).IsFibredOneMorphism p f)
    (φ : spaceFunctor (𝟙 G.objects) ⋙ pointwisePresentationObject F ≅ f)
    (hφ : ∀ Z, p.IsHomLift (𝟙 (p.obj (f.obj Z))) (φ.inv.app Z))
    (hφe : ∀ Z, ∃ H, φ.inv.app Z = eqToHom H)
    (ℱ : Space.inheritedEtaleModules.{u, v, w, u} C S hS p hp) :
    IsIso (pointwisePresentationComparison F hF (𝟙 G.objects) f hf φ hφ ℱ) := by
  subst h
  rw [pointwisePresentationComparison_eq,
    Space.comparisonAlgebraicSpacesModules_congr_of_faithful C S hS (spaceProj G.objects)
    (spaceProj G.objects) p (isFiberedInGroupoids_objects G) (isFiberedInGroupoids_objects G)
    hp (spacePresentation G.objects) (spacePresentation G.objects) (pointwisePresentationObject F)
    (pointwisePresentationObject F) hf (isFibredOneMorphism_pointwisePresentationObject F hF hp)
    (𝟙 G.objects) (spaceFunctor (𝟙 G.objects)) (𝟭 _) (spaceFunctor_id G.objects) φ
    (Iso.refl (pointwisePresentationObject F))
    (fun Z => by obtain ⟨H, hH⟩ := hφe Z; rw [hH]; simp [eqToHom_map])
    (spaceFunctorChartIso (𝟙 G.objects))
    (Space.comparisonChartFunctorIsoId C S hS (spaceProj G.objects) (spacePresentation G.objects))
    hφ (Space.isHomLift_iso_refl_inv_app C S hS p _) (isHomLift_objectsChartIso G (𝟙 G.objects))
    (Space.isHomLift_comparisonChartFunctorIsoId_hom_app C S hS (spaceProj G.objects)
      (spacePresentation G.objects)) ℱ, Space.comparisonAlgebraicSpacesModules_id]
  infer_instance

/-- The reindexed comparison through the source along the unit is an isomorphism. -/
instance isIso_pointwisePresentationSourceReindex_identityArrow
    (ℱ : Space.inheritedEtaleModules.{u, v, w, u} C S hS p hp) :
    IsIso (pointwisePresentationSourceReindex F hF
      (GroupoidInAlgebraicSpaces.identityArrow G) ℱ) := by
  have e' := (GroupoidInAlgebraicSpaces.identityArrow_comp_source G).symm
  have hR : pointwisePresentationReindex F (GroupoidInAlgebraicSpaces.identityArrow G) =
      pointwisePresentationObject F := by
    change spaceFunctor (GroupoidInAlgebraicSpaces.identityArrow G) ⋙
      spaceFunctor G.source ⋙ pointwisePresentationObject F = _
    rw [← Functor.assoc, ← spaceFunctor_comp, GroupoidInAlgebraicSpaces.identityArrow_comp_source,
      spaceFunctor_id]
    rfl
  have T := pullbackTransport_comp_pointwisePresentationComparison F hF e'
    (pointwisePresentationReindex F (GroupoidInAlgebraicSpaces.identityArrow G))
    (isFibredOneMorphism_pointwisePresentationReindex F hF _ hp)
    (pointwisePresentationSourceReindexIso F (GroupoidInAlgebraicSpaces.identityArrow G))
    (isHomLift_pointwisePresentationSourceReindexIso_inv_app F _)
    (isHomLift_pointwisePresentationTransportIso_trans F e' _
      (isHomLift_pointwisePresentationSourceReindexIso_inv_app F _)) ℱ
  have hI := isIso_pointwisePresentationComparison_id F hF _ hR
    (isFibredOneMorphism_pointwisePresentationReindex F hF _ hp)
    (pointwisePresentationTransportIso F e' ≪≫
      pointwisePresentationSourceReindexIso F (GroupoidInAlgebraicSpaces.identityArrow G))
    (isHomLift_pointwisePresentationTransportIso_trans F e' _
      (isHomLift_pointwisePresentationSourceReindexIso_inv_app F _))
    (fun Z => ⟨Functor.congr_obj (hR.trans (congrArg (· ⋙ pointwisePresentationObject F)
      (spaceFunctor_id G.objects)).symm) Z, by simp⟩) ℱ
  rw [← T] at hI
  rw [pointwisePresentationSourceReindex_eq_comparison]
  have : IsIso (Space.pullbackTransport (Space.etaleRestrictedModuleInverseImage C S hS
      (U := G.objects) (spaceProj G.objects) p (isFiberedInGroupoids_objects G) hp
      (spacePresentation G.objects) (pointwisePresentationObject F)
      (isFibredOneMorphism_pointwisePresentationObject F hF hp) ℱ) e') := by
    unfold Space.pullbackTransport
    infer_instance
  exact IsIso.of_isIso_comp_left (Space.pullbackTransport _ e') _

/-! ### The unit law -/

/-- **The unit law for the transition morphism of a pointwise presentation.** -/
theorem groupoidPullbackTransition_identityArrow_of_pointwisePresentation
    (ℱ : Space.inheritedEtaleModules.{u, v, w, u} C S hS p hp)
    (α : (Space.modulePullback C S hS G.target).obj (Space.etaleRestrictedModuleInverseImage C S hS
      (U := G.objects) (spaceProj G.objects) p
          (isFiberedInGroupoids_objects G) hp (spacePresentation G.objects)
          (pointwisePresentationObject F)
          (isFibredOneMorphism_pointwisePresentationObject F hF hp) ℱ) ⟶
      (Space.modulePullback C S hS G.source).obj (Space.etaleRestrictedModuleInverseImage C S hS
        (U := G.objects) (spaceProj G.objects) p
          (isFiberedInGroupoids_objects G) hp (spacePresentation G.objects)
          (pointwisePresentationObject F)
          (isFibredOneMorphism_pointwisePresentationObject F hF hp) ℱ))
    (hα : α ≫ pointwisePresentationSourceComparison F hF ℱ =
      pointwisePresentationTargetComparison F hF ℱ) :
    Space.groupoidPullbackTransition C S hS G (Space.etaleRestrictedModuleInverseImage C S hS
      (U := G.objects) (spaceProj G.objects) p
          (isFiberedInGroupoids_objects G) hp (spacePresentation G.objects)
          (pointwisePresentationObject F)
          (isFibredOneMorphism_pointwisePresentationObject F hF hp) ℱ) α
            (GroupoidInAlgebraicSpaces.identityArrow G) =
      Space.pullbackTransport (Space.etaleRestrictedModuleInverseImage C S hS (U := G.objects)
        (spaceProj G.objects) p
          (isFiberedInGroupoids_objects G) hp (spacePresentation G.objects)
          (pointwisePresentationObject F)
          (isFibredOneMorphism_pointwisePresentationObject F hF hp) ℱ)
        ((GroupoidInAlgebraicSpaces.identityArrow_comp_target G).trans
          (GroupoidInAlgebraicSpaces.identityArrow_comp_source G).symm) := by
  refine Space.eq_of_comp_isIso (pointwisePresentationSourceReindex F hF
    (GroupoidInAlgebraicSpaces.identityArrow G) ℱ) ?_
  rw [groupoidPullbackTransition_comp_pointwisePresentationSourceReindex F hF _ ℱ α hα,
    pointwisePresentationSourceReindex_eq_comparison,
    pointwisePresentationTargetReindex_eq_comparison,
    pullbackTransport_comp_pointwisePresentationComparison F hF _ _ _ _ _
    (isHomLift_pointwisePresentationTransportIso_trans F _ _
      (isHomLift_pointwisePresentationSourceReindexIso_inv_app F _))]
  refine pointwisePresentationComparison_congr F hF _ _ _ _ _ _ _ ℱ fun Z => ?_
  obtain ⟨H, hH⟩ := pointwisePresentationTwoArrow_app_identityArrow F Z
  rw [pointwisePresentationTargetReindexIso_inv_app, Iso.trans_inv, NatTrans.comp_app, hH]
  simp

/-! ### The cocycle condition -/

omit [Category.{w} 𝒳] in
/-- The composite of the reindexings of a groupoid transition morphism along the two projections of
the space of composable pairs is the threefold composite of these reindexings with the transports
along the endpoint equations of the composition diagram. -/
theorem _root_.AlgebraicGeometry.Space.groupoidTransitionComposite_eq_comp₃
    (M : Space.Modules.{u, u} C S hS G.objects.1 G.objects.2)
    (α : (Space.modulePullback C S hS G.target).obj M ⟶
      (Space.modulePullback C S hS G.source).obj M) :
    Space.groupoidTransitionComposite C S hS G M α =
      comp₃ (Space.pullbackTransport M (GroupoidInAlgebraicSpaces.comp_comp_target G))
        (comp₃ (Space.groupoidPullbackTransition C S hS G M α
            (GroupoidInAlgebraicSpaces.firstArrow G))
          (Space.pullbackTransport M (GroupoidInAlgebraicSpaces.firstArrow_comp_source G))
          (Space.groupoidPullbackTransition C S hS G M α (GroupoidInAlgebraicSpaces.secondArrow G)))
        (Space.pullbackTransport M (GroupoidInAlgebraicSpaces.comp_comp_source G).symm) := rfl

/-- **The cocycle condition for the transition morphism of a pointwise presentation**, up to the
identity of the canonical 2-arrows at a composable pair. -/
theorem groupoidPullbackTransition_comp_of_pointwisePresentation
    (ℱ : Space.inheritedEtaleModules.{u, v, w, u} C S hS p hp)
    (α : (Space.modulePullback C S hS G.target).obj (Space.etaleRestrictedModuleInverseImage C S hS
      (U := G.objects) (spaceProj G.objects) p
          (isFiberedInGroupoids_objects G) hp (spacePresentation G.objects)
          (pointwisePresentationObject F)
          (isFibredOneMorphism_pointwisePresentationObject F hF hp) ℱ) ⟶
      (Space.modulePullback C S hS G.source).obj (Space.etaleRestrictedModuleInverseImage C S hS
        (U := G.objects) (spaceProj G.objects) p
          (isFiberedInGroupoids_objects G) hp (spacePresentation G.objects)
          (pointwisePresentationObject F)
          (isFibredOneMorphism_pointwisePresentationObject F hF hp) ℱ))
    (hα : α ≫ pointwisePresentationSourceComparison F hF ℱ =
      pointwisePresentationTargetComparison F hF ℱ)
    [IsIso (pointwisePresentationSourceReindex F hF G.comp ℱ)] :
    Space.groupoidPullbackTransition C S hS G (Space.etaleRestrictedModuleInverseImage C S hS
      (U := G.objects) (spaceProj G.objects) p
          (isFiberedInGroupoids_objects G) hp (spacePresentation G.objects)
          (pointwisePresentationObject F)
          (isFibredOneMorphism_pointwisePresentationObject F hF hp) ℱ) α G.comp =
      Space.groupoidTransitionComposite C S hS G (Space.etaleRestrictedModuleInverseImage C S hS
        (U := G.objects) (spaceProj G.objects) p
          (isFiberedInGroupoids_objects G) hp (spacePresentation G.objects)
          (pointwisePresentationObject F)
          (isFibredOneMorphism_pointwisePresentationObject F hF hp) ℱ) α := by
  refine Space.eq_of_comp_isIso (pointwisePresentationSourceReindex F hF G.comp ℱ) ?_
  rw [groupoidPullbackTransition_comp_pointwisePresentationSourceReindex F hF _ ℱ α hα,
    Space.groupoidTransitionComposite_eq_comp₃, CategoryTheory.comp₃_eq, CategoryTheory.comp₃_eq,
    Category.assoc, Category.assoc, Category.assoc, Category.assoc,
    pointwisePresentationSourceReindex_eq_comparison,
    pointwisePresentationTargetReindex_eq_comparison]
  have h₀ := isHomLift_pointwisePresentationSourceReindexIso_inv_app (p := p) F G.comp
  have h₁ := isHomLift_pointwisePresentationTransportIso_trans F
    (GroupoidInAlgebraicSpaces.comp_comp_source G).symm
    (pointwisePresentationSourceReindexIso F G.comp) h₀
  have h₂ := isHomLift_pointwisePresentationReindexTrans F hF
    (GroupoidInAlgebraicSpaces.secondArrow G)
    (pointwisePresentationTransportIso F (GroupoidInAlgebraicSpaces.comp_comp_source G).symm ≪≫
      pointwisePresentationSourceReindexIso F G.comp) h₁
  have h₃ := isHomLift_pointwisePresentationTransportIso_trans F
    (GroupoidInAlgebraicSpaces.firstArrow_comp_source G)
    (pointwisePresentationTargetReindexIso F (GroupoidInAlgebraicSpaces.secondArrow G) ≪≫
      (pointwisePresentationSourceReindexIso F (GroupoidInAlgebraicSpaces.secondArrow G)).symm ≪≫
      (pointwisePresentationTransportIso F (GroupoidInAlgebraicSpaces.comp_comp_source G).symm ≪≫
        pointwisePresentationSourceReindexIso F G.comp)) h₂
  have h₄ := isHomLift_pointwisePresentationReindexTrans F hF
    (GroupoidInAlgebraicSpaces.firstArrow G)
    (pointwisePresentationTransportIso F (GroupoidInAlgebraicSpaces.firstArrow_comp_source G) ≪≫
      (pointwisePresentationTargetReindexIso F (GroupoidInAlgebraicSpaces.secondArrow G) ≪≫
        (pointwisePresentationSourceReindexIso F (GroupoidInAlgebraicSpaces.secondArrow G)).symm ≪≫
        (pointwisePresentationTransportIso F (GroupoidInAlgebraicSpaces.comp_comp_source G).symm ≪≫
          pointwisePresentationSourceReindexIso F G.comp))) h₃
  have h₅ := isHomLift_pointwisePresentationTransportIso_trans F
    (GroupoidInAlgebraicSpaces.comp_comp_target G)
    (pointwisePresentationTargetReindexIso F (GroupoidInAlgebraicSpaces.firstArrow G) ≪≫
      (pointwisePresentationSourceReindexIso F (GroupoidInAlgebraicSpaces.firstArrow G)).symm ≪≫
      (pointwisePresentationTransportIso F (GroupoidInAlgebraicSpaces.firstArrow_comp_source G) ≪≫
        (pointwisePresentationTargetReindexIso F (GroupoidInAlgebraicSpaces.secondArrow G) ≪≫
          (pointwisePresentationSourceReindexIso F
            (GroupoidInAlgebraicSpaces.secondArrow G)).symm ≪≫
          (pointwisePresentationTransportIso F
              (GroupoidInAlgebraicSpaces.comp_comp_source G).symm ≪≫
            pointwisePresentationSourceReindexIso F G.comp)))) h₄
  have e1 := pullbackTransport_comp_pointwisePresentationComparison F hF
    (GroupoidInAlgebraicSpaces.comp_comp_source G).symm (pointwisePresentationReindex F G.comp)
    (isFibredOneMorphism_pointwisePresentationReindex F hF G.comp hp)
    (pointwisePresentationSourceReindexIso F G.comp) h₀ h₁ ℱ
  have e2 := groupoidPullbackTransition_comp_pointwisePresentationComparison F hF
    (GroupoidInAlgebraicSpaces.secondArrow G) ℱ α hα (pointwisePresentationReindex F G.comp)
    (isFibredOneMorphism_pointwisePresentationReindex F hF G.comp hp)
    (pointwisePresentationTransportIso F (GroupoidInAlgebraicSpaces.comp_comp_source G).symm ≪≫
      pointwisePresentationSourceReindexIso F G.comp) h₁ h₂
  have e3 := pullbackTransport_comp_pointwisePresentationComparison F hF
    (GroupoidInAlgebraicSpaces.firstArrow_comp_source G) (pointwisePresentationReindex F G.comp)
    (isFibredOneMorphism_pointwisePresentationReindex F hF G.comp hp)
    (pointwisePresentationTargetReindexIso F (GroupoidInAlgebraicSpaces.secondArrow G) ≪≫
      (pointwisePresentationSourceReindexIso F (GroupoidInAlgebraicSpaces.secondArrow G)).symm ≪≫
      (pointwisePresentationTransportIso F (GroupoidInAlgebraicSpaces.comp_comp_source G).symm ≪≫
        pointwisePresentationSourceReindexIso F G.comp)) h₂ h₃ ℱ
  have e4 := groupoidPullbackTransition_comp_pointwisePresentationComparison F hF
    (GroupoidInAlgebraicSpaces.firstArrow G) ℱ α hα (pointwisePresentationReindex F G.comp)
    (isFibredOneMorphism_pointwisePresentationReindex F hF G.comp hp)
    (pointwisePresentationTransportIso F (GroupoidInAlgebraicSpaces.firstArrow_comp_source G) ≪≫
      (pointwisePresentationTargetReindexIso F (GroupoidInAlgebraicSpaces.secondArrow G) ≪≫
        (pointwisePresentationSourceReindexIso F (GroupoidInAlgebraicSpaces.secondArrow G)).symm ≪≫
        (pointwisePresentationTransportIso F (GroupoidInAlgebraicSpaces.comp_comp_source G).symm ≪≫
          pointwisePresentationSourceReindexIso F G.comp))) h₃ h₄
  have e5 := pullbackTransport_comp_pointwisePresentationComparison F hF
    (GroupoidInAlgebraicSpaces.comp_comp_target G) (pointwisePresentationReindex F G.comp)
    (isFibredOneMorphism_pointwisePresentationReindex F hF G.comp hp)
    (pointwisePresentationTargetReindexIso F (GroupoidInAlgebraicSpaces.firstArrow G) ≪≫
      (pointwisePresentationSourceReindexIso F (GroupoidInAlgebraicSpaces.firstArrow G)).symm ≪≫
      (pointwisePresentationTransportIso F (GroupoidInAlgebraicSpaces.firstArrow_comp_source G) ≪≫
        (pointwisePresentationTargetReindexIso F (GroupoidInAlgebraicSpaces.secondArrow G) ≪≫
          (pointwisePresentationSourceReindexIso F
            (GroupoidInAlgebraicSpaces.secondArrow G)).symm ≪≫
          (pointwisePresentationTransportIso F
              (GroupoidInAlgebraicSpaces.comp_comp_source G).symm ≪≫
            pointwisePresentationSourceReindexIso F G.comp)))) h₄ h₅ ℱ
  have e6 := pointwisePresentationComparison_congr F hF (G.comp ≫ G.target)
    (pointwisePresentationReindex F G.comp)
    (isFibredOneMorphism_pointwisePresentationReindex F hF G.comp hp)
    (pointwisePresentationTargetReindexIso F G.comp)
    (pointwisePresentationTransportIso F (GroupoidInAlgebraicSpaces.comp_comp_target G) ≪≫
      (pointwisePresentationTargetReindexIso F (GroupoidInAlgebraicSpaces.firstArrow G) ≪≫
        (pointwisePresentationSourceReindexIso F (GroupoidInAlgebraicSpaces.firstArrow G)).symm ≪≫
        (pointwisePresentationTransportIso F
            (GroupoidInAlgebraicSpaces.firstArrow_comp_source G) ≪≫
          (pointwisePresentationTargetReindexIso F (GroupoidInAlgebraicSpaces.secondArrow G) ≪≫
            (pointwisePresentationSourceReindexIso F
              (GroupoidInAlgebraicSpaces.secondArrow G)).symm ≪≫
            (pointwisePresentationTransportIso F
                (GroupoidInAlgebraicSpaces.comp_comp_source G).symm ≪≫
              pointwisePresentationSourceReindexIso F G.comp)))))
    (isHomLift_pointwisePresentationTargetReindexIso_inv_app F hF G.comp) h₅ ℱ (fun Z => by
      obtain ⟨H₁, H₂, H₃, hc⟩ := pointwisePresentationTwoArrow_app_comp F Z
      simp only [Functor.comp_obj, Iso.trans_inv, Functor.isoWhiskerLeft_inv, Iso.symm_inv,
        asIso_hom, eqToIso.inv, NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app,
        eqToIso_trans, Iso.trans_assoc, eqToIso.hom, eqToHom_trans, Category.assoc]
      rw [hc]
      simp)
  exact e6.trans (e5.symm.trans (whisker_eq _ (e4.symm.trans (whisker_eq _ (e3.symm.trans
    (whisker_eq _ (e2.symm.trans (whisker_eq _ e1.symm))))))))

/-! ### The functor to quasi-coherent modules on the groupoid -/

/-- **Admissible modules for pointwise descent.**  An `𝒪_𝒳`-module `ℱ` on the inherited étale
site of `𝒳` is admissible for the pointwise presentation `F` when its restriction
`x^*ℱ|_{U_étale}` is quasi-coherent, the comparison maps of equation 076R through the source and
through the target are isomorphisms, and so is the comparison map along the composition
`c : R ×_{s,U,t} R ⟶ R`. -/
def IsPointwiseDescentAdmissible (ℱ : Space.inheritedEtaleModules.{u, v, w, u} C S hS p hp) :
    Prop :=
  (pointwisePresentationRestriction F hF ℱ).IsQuasicoherentOnSite ∧
    IsIso (pointwisePresentationSourceComparison F hF ℱ) ∧
    IsIso (pointwisePresentationTargetComparison F hF ℱ) ∧
    IsIso (pointwisePresentationArrowComparison F hF G.comp ℱ)

/-- The admissible modules, as an object property. -/
def pointwiseDescentAdmissible (hp : p.IsFiberedInGroupoids) :
    ObjectProperty (Space.inheritedEtaleModules.{u, v, w, u} C S hS p hp) :=
  fun ℱ => IsPointwiseDescentAdmissible F hF ℱ

/-- **The transition morphism** `α = c_t ≫ c_s⁻¹ : t^*(x^*ℱ|_U) ⟶ s^*(x^*ℱ|_U)` of a module
whose comparison map through the source is invertible. -/
def pointwisePresentationTransition (ℱ : Space.inheritedEtaleModules.{u, v, w, u} C S hS p hp)
    [IsIso (pointwisePresentationSourceComparison F hF ℱ)] :
    (Space.modulePullback C S hS G.target).obj (Space.etaleRestrictedModuleInverseImage C S hS
      (U := G.objects) (spaceProj G.objects) p
          (isFiberedInGroupoids_objects G) hp (spacePresentation G.objects)
          (pointwisePresentationObject F)
          (isFibredOneMorphism_pointwisePresentationObject F hF hp) ℱ) ⟶
      (Space.modulePullback C S hS G.source).obj (Space.etaleRestrictedModuleInverseImage C S hS
        (U := G.objects) (spaceProj G.objects) p
          (isFiberedInGroupoids_objects G) hp (spacePresentation G.objects)
          (pointwisePresentationObject F)
          (isFibredOneMorphism_pointwisePresentationObject F hF hp) ℱ) :=
  pointwisePresentationTargetComparison F hF ℱ ≫ inv (pointwisePresentationSourceComparison F hF ℱ)

/-- The transition morphism `α = c_t ≫ c_s⁻¹` satisfies `α ≫ c_s = c_t`. -/
theorem pointwisePresentationTransition_comp
    (ℱ : Space.inheritedEtaleModules.{u, v, w, u} C S hS p hp)
    [IsIso (pointwisePresentationSourceComparison F hF ℱ)] :
    pointwisePresentationTransition F hF ℱ ≫ pointwisePresentationSourceComparison F hF ℱ =
      pointwisePresentationTargetComparison F hF ℱ := by
  rw [pointwisePresentationTransition, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- **The quasi-coherent module on the groupoid attached to an admissible module**:
`(x^*ℱ|_{U_étale}, c_t ≫ c_s⁻¹)`. -/
def pointwiseDescentObj (ℱ : Space.inheritedEtaleModules.{u, v, w, u} C S hS p hp)
    (h : IsPointwiseDescentAdmissible F hF ℱ) : Space.QuasicoherentModule C S hS G :=
  haveI := h.2.1
  haveI := h.2.2.2
  haveI := isIso_pointwisePresentationSourceReindex F hF G.comp ℱ
  { F := ⟨(Space.etaleRestrictedModuleInverseImage C S hS (U := G.objects) (spaceProj G.objects) p
          (isFiberedInGroupoids_objects G) hp (spacePresentation G.objects)
          (pointwisePresentationObject F)
          (isFibredOneMorphism_pointwisePresentationObject F hF hp) ℱ), h.1⟩
    alpha := pointwisePresentationTransition F hF ℱ
    cocycle := groupoidPullbackTransition_comp_of_pointwisePresentation F hF ℱ _
      (pointwisePresentationTransition_comp F hF ℱ)
    unit := groupoidPullbackTransition_identityArrow_of_pointwisePresentation F hF ℱ _
      (pointwisePresentationTransition_comp F hF ℱ) }

/-- The descent datum of the module attached to an admissible module is `c_t ≫ c_s⁻¹`. -/
theorem pointwiseDescentObj_alpha (ℱ : Space.inheritedEtaleModules.{u, v, w, u} C S hS p hp)
    (h : IsPointwiseDescentAdmissible F hF ℱ) :
    haveI := h.2.1
    (pointwiseDescentObj F hF ℱ h).alpha = pointwisePresentationTransition F hF ℱ := rfl

/-- Compatibility of the transition morphisms with `x^*ψ|_{U_étale}`. -/
theorem pointwisePresentationTransition_naturality
    {ℱ ℋ : Space.inheritedEtaleModules.{u, v, w, u} C S hS p hp} (ψ : ℱ ⟶ ℋ)
    [IsIso (pointwisePresentationSourceComparison F hF ℱ)]
    [IsIso (pointwisePresentationSourceComparison F hF ℋ)] :
    pointwisePresentationTransition F hF ℱ ≫
        (Space.modulePullback C S hS G.source).map (pointwisePresentationRestrictionMap F hF ψ) =
      (Space.modulePullback C S hS G.target).map (pointwisePresentationRestrictionMap F hF ψ) ≫
        pointwisePresentationTransition F hF ℋ := by
  have ns := Space.comparisonAlgebraicSpacesModules_naturality C S hS (spaceProj G.arrows)
    (spaceProj G.objects) p (isFiberedInGroupoids_arrows G) (isFiberedInGroupoids_objects G)
    (spacePresentation G.arrows) (spacePresentation G.objects) (spaceFunctor G.source)
    (pointwisePresentationSource F) (pointwisePresentationObject F)
    (isFibredOneMorphism_pointwisePresentationSource F hF hp)
    (isFibredOneMorphism_pointwisePresentationObject F hF hp)
    (Iso.refl (pointwisePresentationSource F)) G.source (spaceFunctorChartIso G.source) hp
    (isHomLift_pointwisePresentationSource_refl F) (isHomLift_sourceChartIso G) ψ
  have nt := Space.comparisonAlgebraicSpacesModules_naturality C S hS (spaceProj G.arrows)
    (spaceProj G.objects) p (isFiberedInGroupoids_arrows G) (isFiberedInGroupoids_objects G)
    (spacePresentation G.arrows) (spacePresentation G.objects) (spaceFunctor G.target)
    (pointwisePresentationSource F) (pointwisePresentationObject F)
    (isFibredOneMorphism_pointwisePresentationSource F hF hp)
    (isFibredOneMorphism_pointwisePresentationObject F hF hp)
    (pointwisePresentationTwoIso F) G.target (spaceFunctorChartIso G.target) hp
    (isHomLift_pointwisePresentationTwoIso_inv_app F hF) (isHomLift_targetChartIso G) ψ
  exact Space.comp_inv_naturality _ _ _ _ _ _ _ ns nt

/-- **The functor `ℱ ↦ (x^*ℱ|_{U_étale}, c_t ≫ c_s⁻¹)`** from the modules admissible for
pointwise descent to the quasi-coherent modules on the groupoid (Stacks 0441). -/
def pointwiseDescentFunctor (hp : p.IsFiberedInGroupoids) :
    (pointwiseDescentAdmissible F hF hp).FullSubcategory ⥤
      Space.QuasicoherentModule C S hS G where
  obj ℱ := pointwiseDescentObj F hF ℱ.obj ℱ.property
  map {ℱ ℋ} ψ :=
    haveI := ℱ.property.2.1
    haveI := ℋ.property.2.1
    { hom := pointwisePresentationRestrictionMap F hF ψ.hom
      comm := pointwisePresentationTransition_naturality F hF ψ.hom }
  map_id ℱ := Space.QuasicoherentModule.Hom.ext (by
    have := Space.etaleChartToFibred_isContinuous C S hS (spaceProj G.objects) p
      (isFiberedInGroupoids_objects G) (spacePresentation G.objects) (pointwisePresentationObject F)
      (isFibredOneMorphism_pointwisePresentationObject F hF hp)
    exact (SheafOfModules.pushforward _).map_id _)
  map_comp ψ ψ' := Space.QuasicoherentModule.Hom.ext (by
    have := Space.etaleChartToFibred_isContinuous C S hS (spaceProj G.objects) p
      (isFiberedInGroupoids_objects G) (spacePresentation G.objects) (pointwisePresentationObject F)
      (isFibredOneMorphism_pointwisePresentationObject F hF hp)
    exact (SheafOfModules.pushforward _).map_comp _ _)

/-- **Quasi-coherent modules are admissible for pointwise descent.**  For a quasi-coherent module
on the fppf site of `𝒳` (Stacks 06WG), read on the inherited étale site, the restriction
`x^*ℱ|_{U_étale}` is quasi-coherent and every comparison map of equation 076R is an
isomorphism. -/
theorem isPointwiseDescentAdmissible_of_quasicoherent
    (ℱ : FibredSite.quasicoherentModules.{u, v, w, u} C S hS p hp) :
    IsPointwiseDescentAdmissible (hp := hp) F hF
      ((Stacks.Sites.CoarserTopology.modulePushforward
        (BigFppfOver.associatedTopology_le_fppf C S hS p .etale) _).obj ℱ.obj) :=
  ⟨Space.isQuasicoherentOnSite_etaleRestrictedModuleInverseImage_of_fppf C S hS
      (spaceProj G.objects) p (isFiberedInGroupoids_objects G) hp (spacePresentation G.objects)
      (pointwisePresentationObject F) (isFibredOneMorphism_pointwisePresentationObject F hF hp)
      ℱ.obj ℱ.property,
    Space.isIso_comparisonAlgebraicSpacesModules_of_quasicoherentModules C S hS _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _ _ ℱ,
    Space.isIso_comparisonAlgebraicSpacesModules_of_quasicoherentModules C S hS _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _ _ ℱ,
    Space.isIso_comparisonAlgebraicSpacesModules_of_quasicoherentModules C S hS _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _ _ ℱ⟩

/-- **The functor on quasi-coherent modules**: `QCoh(𝒪_𝒳) ⥤ QCoh(U, R, s, t, c)`,
`ℱ ↦ (x^*ℱ|_{U_étale}, c_t ≫ c_s⁻¹)`. -/
def pointwiseQuasicoherentDescentFunctor (hp : p.IsFiberedInGroupoids) :
    FibredSite.quasicoherentModules.{u, v, w, u} C S hS p hp ⥤
      Space.QuasicoherentModule C S hS G :=
  ObjectProperty.lift (pointwiseDescentAdmissible F hF hp)
    ((SheafOfModules.isQuasicoherentOnSite.{v, w, u, u}
        (FibredSite.ringStructureSheafCore C S hS p hp .fppf)).ι ⋙
      Stacks.Sites.CoarserTopology.modulePushforward
        (BigFppfOver.associatedTopology_le_fppf C S hS p .etale) _)
    (fun ℱ => isPointwiseDescentAdmissible_of_quasicoherent F hF ℱ) ⋙
    pointwiseDescentFunctor F hF hp

end Presentation

end AlgebraicGeometry.Stack
