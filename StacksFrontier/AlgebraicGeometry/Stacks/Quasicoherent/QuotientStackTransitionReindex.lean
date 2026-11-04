module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentModules
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ComparisonAlgebraicSpacesComp
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuotientStackTransition

/-!
# Reindexing the transition morphism of Stacks 06WT

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces, `𝒳 = [U/R]` its quotient stack,
`ℱ` a quasi-coherent module on `𝒳`, and `α : t^*𝒢 ⟶ s^*𝒢` the transition morphism of
`𝒢 = x^*ℱ|_{U_étale}` (`AlgebraicGeometry.Stack.quotientStackTransition`).  For a morphism
`a : P ⟶ R` of algebraic spaces this file computes the reindexing
`(a ≫ t)^*𝒢 ⟶ (a ≫ s)^*𝒢` of `α` along `a` (`AlgebraicGeometry.Space.groupoidPullbackTransition`)
through two comparison maps of equation 076R over `P` itself:

```
(a ≫ t)^*𝒢 ⟶ (x ∘ s ∘ a)^*ℱ|_{P_étale} ⟵ (a ≫ s)^*𝒢,
```

the first through the 2-morphism of Stacks 044S whiskered by `a`, the second through the
identity.  This is the reduction of the unit and cocycle conditions of Stacks 0441 for `(𝒢, α)`
to identities between morphisms of `𝒳`.

## Main definitions

* `AlgebraicGeometry.Stack.reindexLeg`: the 1-morphism `𝒮_P ⟶ 𝒮_R` attached to `a`.
* `AlgebraicGeometry.Stack.reindexTargetComparison` and
  `AlgebraicGeometry.Stack.reindexSourceComparison`: the two comparison maps.

## Main results

* `AlgebraicGeometry.Stack.groupoidPullbackTransition_quotientStackTransition`: the reindexed
  transition morphism followed by the second comparison is the first.

## References

* [Stacks Project, Tag 06WT](https://stacks.math.columbia.edu/tag/06WT)
* [Stacks Project, Tag 076R](https://stacks.math.columbia.edu/tag/076R)
* [Stacks Project, Tag 044S](https://stacks.math.columbia.edu/tag/044S)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Stack

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)
  {P : AlgebraicSpaces C S hS} (a : P ⟶ G.arrows)

/-- The 1-morphism `𝒮_P ⟶ 𝒮_R` attached to a morphism `a : P ⟶ R` (Stacks 0458). -/
noncomputable abbrev reindexLeg : (fibredCategory C S hS P.obj).val.obj ⥤
    (fibredCategory C S hS G.arrows.obj).val.obj :=
  (associatedMap C S hS a.hom).1.hom.toFunctor

/-- Through the tautological presentations by scheme charts, the 1-morphism attached to `a` is
postcomposition with `a`. -/
noncomputable def reindexChartIso :
    Space.schemeChartFunctor C S hS P.obj (fibredCategory C S hS P.obj).val.p
        (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS P.obj).val.p) ⋙
          reindexLeg G a ≅
      CostructuredArrow.map a.hom ⋙
        Space.schemeChartFunctor C S hS G.arrows.obj (fibredCategory C S hS G.arrows.obj).val.p
          (StacksRepresentableCFG.EquivalenceOver.refl
            (fibredCategory C S hS G.arrows.obj).val.p) :=
  Iso.refl _

/-- The same for the composite of `a` with the target. -/
noncomputable def reindexTargetChartIso :
    Space.schemeChartFunctor C S hS P.obj (fibredCategory C S hS P.obj).val.p
        (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS P.obj).val.p) ⋙
          (reindexLeg G a ⋙ quotientStackTargetLeg G) ≅
      CostructuredArrow.map (a ≫ G.target).hom ⋙
        Space.schemeChartFunctor C S hS G.objects.obj (fibredCategory C S hS G.objects.obj).val.p
          (StacksRepresentableCFG.EquivalenceOver.refl
            (fibredCategory C S hS G.objects.obj).val.p) :=
  Iso.refl _

/-- The same for the composite of `a` with the source. -/
noncomputable def reindexSourceChartIso :
    Space.schemeChartFunctor C S hS P.obj (fibredCategory C S hS P.obj).val.p
        (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS P.obj).val.p) ⋙
          (reindexLeg G a ⋙ quotientStackSourceLeg G) ≅
      CostructuredArrow.map (a ≫ G.source).hom ⋙
        Space.schemeChartFunctor C S hS G.objects.obj (fibredCategory C S hS G.objects.obj).val.p
          (StacksRepresentableCFG.EquivalenceOver.refl
            (fibredCategory C S hS G.objects.obj).val.p) :=
  Iso.refl _

/-- The composite `x ∘ s ∘ a` is a 1-morphism of fibred categories. -/
theorem isFibredOneMorphism_reindexSourceProj :
    (fibredCategory C S hS P.obj).val.p.IsFibredOneMorphism (quotientStack G).p
      (reindexLeg G a ⋙ (quotientStackSourceLeg G ⋙ quotientStackProj G)) :=
  (isFiberedInGroupoids_quotientStack G).isFibredOneMorphism
    (BasedFunctor.comp (associatedMap C S hS a.hom).1.hom
      (BasedFunctor.comp (associatedMap C S hS G.source.hom).1.hom
        (quotientStackProjection G))).w

/-- A morphism of the category fibred in sets attached to a presheaf is determined by its base. -/
theorem fibredCategory_hom_ext {F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    {X Y : (fibredCategory C S hS F).val.obj} (u w : X ⟶ Y) (h : u.base = w.base) : u = w := by
  obtain ⟨ub, uf⟩ := u
  obtain ⟨wb, wf⟩ := w
  change ub = wb at h
  subst h
  congr 1
  exact Discrete.hom_eq

/-- The bookkeeping of `groupoidPullbackTransition_quotientStackTransition`, in an arbitrary
category: if `α ≫ c_s = c_t` and the images of `c_s`, `c_t` under `L` are the components of the
isomorphisms `σ`, `τ` followed by `d_s`, `d_t`, up to the same `c`, then
`τ⁻¹ ≫ L(α) ≫ σ ≫ d_s = d_t`. -/
theorem _root_.CategoryTheory.Functor.inv_map_comp_hom_comp {𝒰 𝒜 ℬ : Type*} {_ : Category 𝒰}
    {_ : Category 𝒜} {_ : Category ℬ} (L : 𝒜 ⥤ ℬ) {T₁ T₂ : 𝒰 ⥤ 𝒜} {Lt Ls : 𝒰 ⥤ ℬ}
    (τ : T₁ ⋙ L ≅ Lt) (σ : T₂ ⋙ L ≅ Ls) {X : 𝒰} {Q : 𝒜} {α : T₁.obj X ⟶ T₂.obj X}
    {cs : T₂.obj X ⟶ Q} {ct : T₁.obj X ⟶ Q} (hα : α ≫ cs = ct) {H : ℬ} {c : L.obj Q ⟶ H}
    {dt : Lt.obj X ⟶ H} {ds : Ls.obj X ⟶ H} (hs : L.map cs ≫ c = σ.hom.app X ≫ ds)
    (ht : L.map ct ≫ c = τ.hom.app X ≫ dt) :
    ((τ.app X).inv ≫ L.map α ≫ (σ.app X).hom) ≫ ds = dt := by
  rw [Iso.app_inv, Iso.app_hom, Category.assoc, Category.assoc, ← hs,
    ← Category.assoc (L.map α), ← L.map_comp, hα, ht, Iso.inv_hom_id_app_assoc]

/-- `fibredCategory_hom_ext`, through the structure functor. -/
theorem fibredCategory_hom_ext' {F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    {X Y : (fibredCategory C S hS F).val.obj} (u w : X ⟶ Y)
    (h : (fibredCategory C S hS F).val.p.map u = (fibredCategory C S hS F).val.p.map w) :
    u = w :=
  fibredCategory_hom_ext u w h

variable (F : QuotientStackModules G) (hF : F.IsQuasicoherentOnSite)

/-- The comparison map `(a ≫ t)^*𝒢 ⟶ (x ∘ s ∘ a)^*ℱ|_{P_étale}` of equation 076R of the triangle
through `t ∘ a`, carried by the 2-morphism of Stacks 044S whiskered by `a`. -/
noncomputable abbrev reindexTargetComparison :=
  Space.comparisonAlgebraicSpacesModules C S hS (fibredCategory C S hS P.obj).val.p
    (fibredCategory C S hS G.objects.obj).val.p (quotientStack G).p
    (fibredCategory C S hS P.obj).property (fibredCategory C S hS G.objects.obj).property
    (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS P.obj).val.p)
    (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS G.objects.obj).val.p)
    (reindexLeg G a ⋙ quotientStackTargetLeg G)
    (reindexLeg G a ⋙ (quotientStackSourceLeg G ⋙ quotientStackProj G)) (quotientStackProj G)
    (isFibredOneMorphism_reindexSourceProj G a) (isFibredOneMorphism_quotientStackProj G)
    (Functor.isoWhiskerLeft (reindexLeg G a) (quotientStackTwoArrowIso G)) (a ≫ G.target)
    (reindexTargetChartIso G a) (isFiberedInGroupoids_quotientStack G)
    (fun X => isHomLift_quotientStackTwoArrowNat G ((reindexLeg G a).obj X))
    (fun _ => IsHomLift.id rfl) ((quotientStackToEtale G).obj F)

/-- The comparison map `(a ≫ s)^*𝒢 ⟶ (x ∘ s ∘ a)^*ℱ|_{P_étale}` of equation 076R of the triangle
through `s ∘ a`, carried by the identity. -/
noncomputable abbrev reindexSourceComparison :=
  Space.comparisonAlgebraicSpacesModules C S hS (fibredCategory C S hS P.obj).val.p
    (fibredCategory C S hS G.objects.obj).val.p (quotientStack G).p
    (fibredCategory C S hS P.obj).property (fibredCategory C S hS G.objects.obj).property
    (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS P.obj).val.p)
    (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS G.objects.obj).val.p)
    (reindexLeg G a ⋙ quotientStackSourceLeg G)
    (reindexLeg G a ⋙ (quotientStackSourceLeg G ⋙ quotientStackProj G)) (quotientStackProj G)
    (isFibredOneMorphism_reindexSourceProj G a) (isFibredOneMorphism_quotientStackProj G)
    (Iso.refl _) (a ≫ G.source)
    (reindexSourceChartIso G a) (isFiberedInGroupoids_quotientStack G)
    (fun _ => IsHomLift.id rfl) (fun _ => IsHomLift.id rfl) ((quotientStackToEtale G).obj F)

/-- The comparison map `a^*((x ∘ s)^*ℱ|_{R_étale}) ⟶ (x ∘ s ∘ a)^*ℱ|_{P_étale}` of equation 076R
of the strictly commutative triangle through `a`. -/
noncomputable abbrev reindexArrowComparison :=
  Space.comparisonAlgebraicSpacesModules C S hS (fibredCategory C S hS P.obj).val.p
    (fibredCategory C S hS G.arrows.obj).val.p (quotientStack G).p
    (fibredCategory C S hS P.obj).property (fibredCategory C S hS G.arrows.obj).property
    (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS P.obj).val.p)
    (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS G.arrows.obj).val.p)
    (reindexLeg G a)
    (reindexLeg G a ⋙ (quotientStackSourceLeg G ⋙ quotientStackProj G))
    (quotientStackSourceLeg G ⋙ quotientStackProj G)
    (isFibredOneMorphism_reindexSourceProj G a) (isFibredOneMorphism_quotientStackSourceProj G)
    (Iso.refl _) a
    (reindexChartIso G a) (isFiberedInGroupoids_quotientStack G)
    (fun _ => IsHomLift.id rfl) (fun _ => IsHomLift.id rfl) ((quotientStackToEtale G).obj F)

/-- The comparison morphisms of the triangle through `t ∘ a` are the composites of those of the
triangle through `a` and of the triangle through `t`: the naturality of the 2-morphism of
Stacks 044S, and uniqueness of morphisms of `𝒮_U` over a given morphism of the site. -/
theorem reindexTarget_comparisonMorphism_comp {U₀ : Space.SmallEtale C S hS P.obj}
    {V₀ : Space.SmallEtale C S hS G.arrows.obj} {W₀ : Space.SmallEtale C S hS G.objects.obj}
    (x : (Space.SmallEtale.toOver C S hS P.obj).obj U₀ ⟶
      (Space.SmallEtale.toOver C S hS G.arrows.obj).obj V₀)
    (y : (Space.SmallEtale.toOver C S hS G.arrows.obj).obj V₀ ⟶
      (Space.SmallEtale.toOver C S hS G.objects.obj).obj W₀)
    (hx : U₀.1.hom ≫ a.hom = yoneda.map x ≫ V₀.1.hom)
    (hy : V₀.1.hom ≫ G.target.hom = yoneda.map y ≫ W₀.1.hom) :
    Space.comparisonMorphism C S hS (fibredCategory C S hS P.obj).val.p
        (fibredCategory C S hS G.objects.obj).val.p
        (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS P.obj).val.p)
        (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS G.objects.obj).val.p)
        (reindexLeg G a ⋙ quotientStackTargetLeg G)
        (reindexLeg G a ⋙ (quotientStackSourceLeg G ⋙ quotientStackProj G)) (quotientStackProj G)
        (Functor.isoWhiskerLeft (reindexLeg G a) (quotientStackTwoArrowIso G)) (a ≫ G.target)
        (reindexTargetChartIso G a) (Space.ChartDiagram.comp C S hS a G.target x y hx hy) =
      Space.comparisonMorphism C S hS (fibredCategory C S hS P.obj).val.p
          (fibredCategory C S hS G.arrows.obj).val.p
          (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS P.obj).val.p)
          (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS G.arrows.obj).val.p)
          (reindexLeg G a)
          (reindexLeg G a ⋙ (quotientStackSourceLeg G ⋙ quotientStackProj G))
          (quotientStackSourceLeg G ⋙ quotientStackProj G) (Iso.refl _) a (reindexChartIso G a)
          ⟨U₀, V₀, x, hx⟩ ≫
        Space.comparisonMorphism C S hS (fibredCategory C S hS G.arrows.obj).val.p
          (fibredCategory C S hS G.objects.obj).val.p
          (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS G.arrows.obj).val.p)
          (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS G.objects.obj).val.p)
          (quotientStackTargetLeg G)
          (quotientStackSourceLeg G ⋙ quotientStackProj G) (quotientStackProj G)
          (quotientStackTwoArrowIso G) G.target (quotientStackTargetChartIso G)
          ⟨V₀, W₀, y, hy⟩ := by
  simp only [Space.comparisonMorphism, Space.comparisonChartHom, reindexTargetChartIso,
    reindexChartIso, quotientStackTargetChartIso, quotientStackTwoArrowIso, Iso.refl_hom,
    Iso.refl_inv, NatTrans.id_app, Category.id_comp, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, Iso.symm_inv, asIso_hom]
  rw [← Category.assoc, (quotientStackTwoArrowNat G).naturality, Category.assoc]
  congr 1
  rw [Functor.comp_map, ← Functor.map_comp]
  congr 1
  exact fibredCategory_hom_ext _ _ rfl

/-- **The composition law through the target**: `a^*(c_t) ≫ c_a` is the comparison of
Stacks 03LU followed by the comparison through `t ∘ a`. -/
theorem modulePullback_map_targetComparison_comp :
    (Space.modulePullback C S hS a).map (quotientStackTargetComparison G F) ≫
        reindexArrowComparison G a F =
      (Space.modulePullbackCompIso C S hS a G.target).hom.app _ ≫
        reindexTargetComparison G a F :=
  Space.comparisonAlgebraicSpacesModules_comp C S hS
    (fibredCategory C S hS P.obj).val.p (fibredCategory C S hS G.arrows.obj).val.p
    (fibredCategory C S hS G.objects.obj).val.p (quotientStack G).p
    (fibredCategory C S hS P.obj).property (fibredCategory C S hS G.arrows.obj).property
    (fibredCategory C S hS G.objects.obj).property
    (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS P.obj).val.p)
    (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS G.arrows.obj).val.p)
    (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS G.objects.obj).val.p)
    (reindexLeg G a) (quotientStackTargetLeg G) (reindexLeg G a ⋙ quotientStackTargetLeg G)
    (reindexLeg G a ⋙ (quotientStackSourceLeg G ⋙ quotientStackProj G))
    (quotientStackSourceLeg G ⋙ quotientStackProj G) (quotientStackProj G)
    (isFibredOneMorphism_reindexSourceProj G a) (isFibredOneMorphism_quotientStackSourceProj G)
    (isFibredOneMorphism_quotientStackProj G)
    (Iso.refl _) (quotientStackTwoArrowIso G)
    (Functor.isoWhiskerLeft (reindexLeg G a) (quotientStackTwoArrowIso G))
    a G.target (reindexChartIso G a) (quotientStackTargetChartIso G) (reindexTargetChartIso G a)
    (isFiberedInGroupoids_quotientStack G) (fun _ => IsHomLift.id rfl)
    (isHomLift_quotientStackTwoArrowNat G)
    (fun X => isHomLift_quotientStackTwoArrowNat G ((reindexLeg G a).obj X))
    (fun _ => IsHomLift.id rfl) (fun _ => IsHomLift.id rfl) (fun _ => IsHomLift.id rfl)
    (fun x y hx hy => reindexTarget_comparisonMorphism_comp G a x y hx hy) _

/-- The comparison morphisms of the triangle through `s ∘ a` are the composites of those of the
triangle through `a` and of the triangle through `s`. -/
theorem reindexSource_comparisonMorphism_comp {U₀ : Space.SmallEtale C S hS P.obj}
    {V₀ : Space.SmallEtale C S hS G.arrows.obj} {W₀ : Space.SmallEtale C S hS G.objects.obj}
    (x : (Space.SmallEtale.toOver C S hS P.obj).obj U₀ ⟶
      (Space.SmallEtale.toOver C S hS G.arrows.obj).obj V₀)
    (y : (Space.SmallEtale.toOver C S hS G.arrows.obj).obj V₀ ⟶
      (Space.SmallEtale.toOver C S hS G.objects.obj).obj W₀)
    (hx : U₀.1.hom ≫ a.hom = yoneda.map x ≫ V₀.1.hom)
    (hy : V₀.1.hom ≫ G.source.hom = yoneda.map y ≫ W₀.1.hom) :
    Space.comparisonMorphism C S hS (fibredCategory C S hS P.obj).val.p
        (fibredCategory C S hS G.objects.obj).val.p
        (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS P.obj).val.p)
        (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS G.objects.obj).val.p)
        (reindexLeg G a ⋙ quotientStackSourceLeg G)
        (reindexLeg G a ⋙ (quotientStackSourceLeg G ⋙ quotientStackProj G)) (quotientStackProj G)
        (Iso.refl _) (a ≫ G.source)
        (reindexSourceChartIso G a) (Space.ChartDiagram.comp C S hS a G.source x y hx hy) =
      Space.comparisonMorphism C S hS (fibredCategory C S hS P.obj).val.p
          (fibredCategory C S hS G.arrows.obj).val.p
          (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS P.obj).val.p)
          (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS G.arrows.obj).val.p)
          (reindexLeg G a)
          (reindexLeg G a ⋙ (quotientStackSourceLeg G ⋙ quotientStackProj G))
          (quotientStackSourceLeg G ⋙ quotientStackProj G) (Iso.refl _) a (reindexChartIso G a)
          ⟨U₀, V₀, x, hx⟩ ≫
        Space.comparisonMorphism C S hS (fibredCategory C S hS G.arrows.obj).val.p
          (fibredCategory C S hS G.objects.obj).val.p
          (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS G.arrows.obj).val.p)
          (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS G.objects.obj).val.p)
          (quotientStackSourceLeg G)
          (quotientStackSourceLeg G ⋙ quotientStackProj G) (quotientStackProj G)
          (Iso.refl _) G.source (quotientStackSourceChartIso G)
          ⟨V₀, W₀, y, hy⟩ := by
  simp only [Space.comparisonMorphism, Space.comparisonChartHom, reindexSourceChartIso,
    reindexChartIso, quotientStackSourceChartIso, Iso.refl_hom,
    Iso.refl_inv, NatTrans.id_app, Category.id_comp]
  refine (Category.id_comp _).trans ?_
  rw [Functor.comp_map, ← Functor.map_comp]
  refine congrArg (quotientStackProj G).map (fibredCategory_hom_ext _ _ ?_)
  exact (by simp : 𝟙 _ ≫ (x ≫ y) = (𝟙 _ ≫ x) ≫ (𝟙 _ ≫ y))

/-- **The composition law through the source**: `a^*(c_s) ≫ c_a` is the comparison of
Stacks 03LU followed by the comparison through `s ∘ a`. -/
theorem modulePullback_map_sourceComparison_comp :
    (Space.modulePullback C S hS a).map (quotientStackSourceComparison G F) ≫
        reindexArrowComparison G a F =
      (Space.modulePullbackCompIso C S hS a G.source).hom.app _ ≫
        reindexSourceComparison G a F :=
  Space.comparisonAlgebraicSpacesModules_comp C S hS
    (fibredCategory C S hS P.obj).val.p (fibredCategory C S hS G.arrows.obj).val.p
    (fibredCategory C S hS G.objects.obj).val.p (quotientStack G).p
    (fibredCategory C S hS P.obj).property (fibredCategory C S hS G.arrows.obj).property
    (fibredCategory C S hS G.objects.obj).property
    (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS P.obj).val.p)
    (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS G.arrows.obj).val.p)
    (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS G.objects.obj).val.p)
    (reindexLeg G a) (quotientStackSourceLeg G) (reindexLeg G a ⋙ quotientStackSourceLeg G)
    (reindexLeg G a ⋙ (quotientStackSourceLeg G ⋙ quotientStackProj G))
    (quotientStackSourceLeg G ⋙ quotientStackProj G) (quotientStackProj G)
    (isFibredOneMorphism_reindexSourceProj G a) (isFibredOneMorphism_quotientStackSourceProj G)
    (isFibredOneMorphism_quotientStackProj G)
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
    a G.source (reindexChartIso G a) (quotientStackSourceChartIso G) (reindexSourceChartIso G a)
    (isFiberedInGroupoids_quotientStack G) (fun _ => IsHomLift.id rfl)
    (fun _ => IsHomLift.id rfl) (fun _ => IsHomLift.id rfl)
    (fun _ => IsHomLift.id rfl) (fun _ => IsHomLift.id rfl) (fun _ => IsHomLift.id rfl)
    (fun x y hx hy => reindexSource_comparisonMorphism_comp G a x y hx hy) _

/-- The reindexing of a groupoid transition morphism `α` along `a`, computed through comparison
maps: if `α ≫ c_s = c_t` and `a^*c_s`, `a^*c_t` are the comparisons of Stacks 03LU followed by
`d_s`, `d_t` up to a common `c`, then the reindexed transition followed by `d_s` is `d_t`.  The
hypotheses `hs`, `ht` come first so that they fix the module `M`. -/
theorem _root_.AlgebraicGeometry.Space.groupoidPullbackTransition_comp_eq
    {M : Space.Modules.{u, u} C S hS G.objects.1 G.objects.2}
    {Q : Space.Modules.{u, u} C S hS G.arrows.1 G.arrows.2}
    {cs : (Space.modulePullback C S hS G.source).obj M ⟶ Q}
    {ct : (Space.modulePullback C S hS G.target).obj M ⟶ Q}
    {H : Space.Modules.{u, u} C S hS P.1 P.2} {c : (Space.modulePullback C S hS a).obj Q ⟶ H}
    {ds : (Space.modulePullback C S hS (a ≫ G.source)).obj M ⟶ H}
    {dt : (Space.modulePullback C S hS (a ≫ G.target)).obj M ⟶ H}
    (hs : (Space.modulePullback C S hS a).map cs ≫ c =
      (Space.modulePullbackCompIso C S hS a G.source).hom.app M ≫ ds)
    (ht : (Space.modulePullback C S hS a).map ct ≫ c =
      (Space.modulePullbackCompIso C S hS a G.target).hom.app M ≫ dt)
    (α : (Space.modulePullback C S hS G.target).obj M ⟶
      (Space.modulePullback C S hS G.source).obj M) (hα : α ≫ cs = ct) :
    Space.groupoidPullbackTransition C S hS G M α a ≫ ds = dt :=
  (Space.modulePullback C S hS a).inv_map_comp_hom_comp
    (Space.modulePullbackCompIso C S hS a G.target) (Space.modulePullbackCompIso C S hS a G.source)
    hα hs ht

include hF in
/-- **The reindexed transition morphism.**  For a quasi-coherent `ℱ` on `[U/R]` and `a : P ⟶ R`,
the reindexing of the transition morphism of Stacks 06WT along `a`, followed by the comparison
map of the triangle through `s ∘ a`, is the comparison map of the triangle through `t ∘ a`. -/
theorem groupoidPullbackTransition_quotientStackTransition :
    Space.groupoidPullbackTransition C S hS G _ (quotientStackTransition G F hF) a ≫
        reindexSourceComparison G a F =
      reindexTargetComparison G a F :=
  Space.groupoidPullbackTransition_comp_eq G a (modulePullback_map_sourceComparison_comp G a F)
    (modulePullback_map_targetComparison_comp G a F) _
    (quotientStackTransition_comp_sourceComparison G F hF)

end AlgebraicGeometry.Stack

end
