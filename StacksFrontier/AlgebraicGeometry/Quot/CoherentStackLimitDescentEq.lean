module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackFiberedUnconditional
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackFinitePresentationStability
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackMorSheaf
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackSpanIso
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackStageSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationModuleColimitTheorem
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStageDescent

/-!
# Descent of equalities of vertical morphisms for `Coh_{X/Y}`

In Situation 08KB let `T = lim T_j` be a cofiltered limit of affine schemes of the big fppf site,
taken in schemes. Two vertical morphisms of `Coh_{X/Y}` over a stage `T_i` which agree after
pullback to `T` already agree after pullback to a later stage. This is the descent condition
`Deformation.Artin.DescentEq` of Stacks 07XL that makes the comparison functor
`colim Coh_{X/Y, T_j} ⥤ Coh_{X/Y, T}` faithful, and it is the faithfulness clause of the proof of
Stacks 08KD.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.map_fibre_eq_of_comp_eq` and
  `AlgebraicGeometry.Space.CoherentSituation.comp_eq_of_map_fibre_eq`: two composites `δ ≫ ψ`,
  `δ ≫ ψ'` with `ψ, ψ'` sharing their base map agree exactly when the inverse images along the base
  map of `δ` of the module comparisons of `ψ, ψ'` agree.
* `AlgebraicGeometry.Space.CoherentSituation.map_relativeMap_eq_of_comp` and
  `AlgebraicGeometry.Space.CoherentSituation.map_relativeMap_eq_of_iso_comp`: equalities of inverse
  images pass along composites of morphisms of base changes, and back across isomorphisms.

* `AlgebraicGeometry.Space.CoherentSituation.descentEq_coherent`: the condition
  `Deformation.Artin.DescentEq` for `Coh_{X/Y}`, at every cofiltered system of affine schemes of
  the site whose limit in schemes lies in the site, with no bound on the index, and
  `AlgebraicGeometry.Space.CoherentSituation.faithful_colimitComparison_coherent`: the comparison
  functor of Stacks 07XL for `Coh_{X/Y}` is faithful.

## Implementation notes

A vertical morphism over `T_i` is a pair of the identity of test schemes and an isomorphism of
modules on `X_{T_i}`. The two morphisms share their base map, so their composites with a morphism
`δ` over `T ⟶ T_i` agree exactly when the inverse images of their module isomorphisms to `X_T`
agree; Stacks 07V7 for the system of base changes above `i`
(`AlgebraicGeometry.Space.finitePresentationModule_isColimit_of_isLimit`, at the hypotheses of
`StacksFrontier/AlgebraicGeometry/Quot/CoherentStackStageSystem.lean`) then produces the later
stage.

The comparisons of inverse images in the composition of `Coh_{X/Y}` contain `eqToIso` factors
which the kernel does not unfold in reasonable time, so every statement about a composite is
reduced, through `AlgebraicGeometry.Space.CoherentHom.comp_fibre`, to the abstract calculus of
`CategoryTheory.Functor.fibreComp` with an arbitrary comparison.

Morphisms of modules are only ever compared on algebraic spaces that are *syntactically* the same:
the stage spaces of the system of base changes are definitionally, but not syntactically, the
base changes `X_{T_k}` of the objects of `Coh_{X/Y}`, and elaborating `Functor.map` of a module
pullback across that definitional equality does not finish. The proof therefore passes between
the two through explicit identity morphisms of algebraic spaces built with
`CategoryTheory.ObjectProperty.homMk`, and composites of inverse images along them.

## References

* [Stacks Project, Tag 08KD](https://stacks.math.columbia.edu/tag/08KD)
* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
* [Stacks Project, Tag 07V7](https://stacks.math.columbia.edu/tag/07V7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.Functor

/-- Composing two fibre morphisms with the same first factor along one comparison determines the
image of the second factors, when the first factor is an isomorphism. -/
theorem map_eq_of_fibreComp_eq {C₀ C₁ C₂ : Type*} [Category* C₀] [Category* C₁] [Category* C₂]
    {La : C₁ ⥤ C₀} {Lb : C₂ ⥤ C₁} {Lab : C₂ ⥤ C₀} (τ : Lab ≅ Lb ⋙ La) {M : C₀} {M' : C₁}
    {M'' : C₂} (a : La.obj M' ⟶ M) [IsIso a] {b b' : Lb.obj M'' ⟶ M'}
    (h : fibreComp τ a b = fibreComp τ a b') : La.map b = La.map b' := by
  unfold fibreComp at h
  exact (Iso.cancel_iso_hom_right _ _ (asIso a)).1 ((Iso.cancel_iso_hom_left (τ.app M'') _ _).1 h)

/-- Composing two fibre morphisms with the same first factor along one comparison only depends
on the image of the second factor. -/
theorem fibreComp_eq_of_map_eq {C₀ C₁ C₂ : Type*} [Category* C₀] [Category* C₁] [Category* C₂]
    {La : C₁ ⥤ C₀} {Lb : C₂ ⥤ C₁} {Lab : C₂ ⥤ C₀} (τ : Lab ≅ Lb ⋙ La) {M : C₀} {M' : C₁}
    {M'' : C₂} (a : La.obj M' ⟶ M) {b b' : Lb.obj M'' ⟶ M'} (h : La.map b = La.map b') :
    fibreComp τ a b = fibreComp τ a b' := by
  unfold fibreComp
  rw [h]

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space.CoherentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (D : CoherentSituation B S hS)

/-- The inverse image along the morphism of base changes induced by an isomorphism of test
schemes is faithful. -/
theorem faithful_modulePullback_relativeMap_of_iso {T T' : SchemesOver D.Y} (e : T ≅ T') :
    (modulePullback B S hS (D.relativeMap e.hom)).Faithful := by
  have : IsIso (D.relativeMap e.hom) :=
    (inferInstance : IsIso ((baseChangeOver D.f ⋙ Over.forget D.X).map e.hom))
  exact faithful_modulePullback_of_isIso _

/-- Two morphisms of modules with equal inverse images along a morphism of base changes have equal
inverse images along any morphism of base changes factoring through it. -/
theorem map_relativeMap_eq_of_comp {T₁ T₂ T₃ : SchemesOver D.Y} (a : T₁ ⟶ T₂) (b : T₂ ⟶ T₃)
    {M N : Modules.{u, u} B S hS (D.space T₃).1 (D.space T₃).2} {φ ψ : M ⟶ N}
    (h : (modulePullback B S hS (D.relativeMap b)).map φ =
      (modulePullback B S hS (D.relativeMap b)).map ψ) :
    (modulePullback B S hS (D.relativeMap (a ≫ b))).map φ =
      (modulePullback B S hS (D.relativeMap (a ≫ b))).map ψ := by
  have e : D.relativeMap (a ≫ b) = D.relativeMap a ≫ D.relativeMap b := baseChangeMap_comp D.f a b
  rw [e]
  exact map_comp_eq_of_map_map_eq B S hS _ _ (by rw [h])

/-- Two morphisms of modules with equal inverse images along a composite of morphisms of base
changes, the first an isomorphism, have equal inverse images along the second. -/
theorem map_relativeMap_eq_of_iso_comp {T₁ T₂ T₃ : SchemesOver D.Y} (e : T₁ ≅ T₂) (b : T₂ ⟶ T₃)
    {M N : Modules.{u, u} B S hS (D.space T₃).1 (D.space T₃).2} {φ ψ : M ⟶ N}
    (h : (modulePullback B S hS (D.relativeMap (e.hom ≫ b))).map φ =
      (modulePullback B S hS (D.relativeMap (e.hom ≫ b))).map ψ) :
    (modulePullback B S hS (D.relativeMap b)).map φ =
      (modulePullback B S hS (D.relativeMap b)).map ψ := by
  have := D.faithful_modulePullback_relativeMap_of_iso e
  have e' : D.relativeMap (e.hom ≫ b) = D.relativeMap e.hom ≫ D.relativeMap b :=
    baseChangeMap_comp D.f e.hom b
  rw [e'] at h
  exact (modulePullback B S hS (D.relativeMap e.hom)).map_injective
    (map_map_eq_of_map_comp_eq B S hS _ _ h)

/-- Equal morphisms of `Coh_{X/Y}` have heterogeneously equal module comparisons. -/
theorem CoherentHom.fibre_heq_of_eq {A A' : CoherentObject D} {m n : CoherentHom A A'}
    (h : m = n) : m.fibre ≍ n.fibre := by
  subst h
  rfl

/-- A composite of morphisms of `Coh_{X/Y}` with the same first factor and second factors with
the same base map determines the inverse image of the module comparisons of the second factors
along the base map of the first. -/
theorem map_fibre_eq_of_comp_eq {A₁ A₂ A₃ : CoherentObject D} (δ : CoherentHom A₁ A₂)
    {b : A₂.T ⟶ A₃.T} (φ φ' : (modulePullback B S hS (D.relativeMap b)).obj A₃.F ⟶ A₂.F)
    [IsIso φ] [IsIso φ']
    (h : CoherentHom.comp δ ⟨b, φ, inferInstance⟩ = CoherentHom.comp δ ⟨b, φ', inferInstance⟩) :
    (modulePullback B S hS (D.relativeMap δ.base)).map φ =
      (modulePullback B S hS (D.relativeMap δ.base)).map φ' := by
  have hh := CoherentHom.fibre_heq_of_eq D h
  rw [CoherentHom.comp_fibre, CoherentHom.comp_fibre] at hh
  exact Functor.map_eq_of_fibreComp_eq _ _ (eq_of_heq hh)

/-- **Two composites of morphisms of `Coh_{X/Y}` with the same first factor and second factors
with the same base map are equal when the inverse images of the module comparisons of the second
factors agree.** -/
theorem comp_eq_of_map_fibre_eq {A₁ A₂ A₃ : CoherentObject D} (δ : CoherentHom A₁ A₂)
    {b : A₂.T ⟶ A₃.T} (φ φ' : (modulePullback B S hS (D.relativeMap b)).obj A₃.F ⟶ A₂.F)
    [IsIso φ] [IsIso φ']
    (h : (modulePullback B S hS (D.relativeMap δ.base)).map φ =
      (modulePullback B S hS (D.relativeMap δ.base)).map φ') :
    CoherentHom.comp δ ⟨b, φ, inferInstance⟩ = CoherentHom.comp δ ⟨b, φ', inferInstance⟩ :=
  coherentHom_eq_of_heq rfl (by
    rw [CoherentHom.comp_fibre, CoherentHom.comp_fibre]
    exact heq_of_eq (Functor.fibreComp_eq_of_map_eq _ _ h))

/-! ### Descent of equalities -/

section Descent

variable (hZ : B.Contains (⊤_ Scheme.{u})) {I : Type u} [Category.{u} I] [IsCofiltered I]
  (E : I ⥤ BigAffineFppf B S hS) (c : Cone E)
  (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c))


include hZ hc in
/-- **The descent of equalities of Stacks 07XL for `Coh_{X/Y}`.** Over a cofiltered limit
`T = lim T_j` of affine schemes of the site, taken in schemes, two vertical morphisms of
`Coh_{X/Y}` over a stage `T_i` whose composites with a morphism over `T ⟶ T_i` agree already agree
after composing with a morphism over a later transition morphism `T_k ⟶ T_i`. This is the
faithfulness half of the proof of Stacks 08KD, by the faithfulness clause of Stacks 07V7. -/
theorem descentEq_coherent :
    letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
    Deformation.Artin.DescentEq (coherentSiteProjection D.categoryData)
      (E ⋙ BigAffineFppf.inclusion B S hS) ((BigAffineFppf.inclusion B S hS).mapCone c) := by
  let : Category.{u + 1} (CoherentObject D) := D.categoryData.category
  let p := coherentSiteProjection D.categoryData
  let incl := BigAffineFppf.inclusion B S hS
  let hst := modulePullbackStabilityOfFinitePresentation B S hS
  rintro i ⟨A, hA⟩ ⟨A', hA'⟩ ⟨A₀, hA₀⟩ δ hδ ψ ψ' hψ hψ' hδψ
  change A.T.left = (E ⋙ incl).obj i at hA
  change A'.T.left = (E ⋙ incl).obj i at hA'
  change A₀.T.left = (incl.mapCone c).pt at hA₀
  change CoherentHom A₀ A at δ
  change CoherentHom A A' at ψ ψ'
  have hψψ : ψ.base.left = ψ'.base.left := by
    have h := IsHomLift.fac' p (𝟙 ((E ⋙ incl).obj i)) ψ
    have h' := IsHomLift.fac' p (𝟙 ((E ⋙ incl).obj i)) ψ'
    change ψ.base.left = _ at h
    change ψ'.base.left = _ at h'
    rw [h, h']
  have hδb : δ.base.left = eqToHom hA₀ ≫ (incl.mapCone c).π.app i ≫ eqToHom hA.symm :=
    IsHomLift.fac' p ((incl.mapCone c).π.app i) δ
  have hb : ψ.base = ψ'.base := CostructuredArrow.hom_ext _ _ hψψ
  obtain ⟨b, φ, iφ⟩ := ψ
  obtain ⟨b', φ', iφ'⟩ := ψ'
  obtain rfl : b = b' := hb
  have hmap := D.map_fibre_eq_of_comp_eq δ φ φ' hδψ
  -- the system of base changes above the stage `i`
  let g : (schemeSpaceFunctor B S hS).obj (incl.obj (E.obj i)) ⟶ D.Y :=
    (schemeSpaceFunctor B S hS).map (eqToHom hA.symm) ≫ A.T.hom
  let k₀ : Over i := Over.mk (𝟙 i)
  let u : (D.stageTestSystem E g).obj k₀ ⟶ A.T :=
    CostructuredArrow.homMk (incl.map (E.map (𝟙 i)) ≫ eqToHom hA.symm) (by
      change _ = (schemeSpaceFunctor B S hS).map (incl.map (E.map (𝟙 i))) ≫ g
      exact (schemeSpaceFunctor B S hS).map_comp_assoc _ _ _)
  let v : A₀.T ≅ (D.stageTestCone E c g).pt := CostructuredArrow.isoMk (eqToIso hA₀) (by
    have hw := δ.base.w
    change (schemeSpaceFunctor B S hS).map δ.base.left ≫ A.T.hom = A₀.T.hom at hw
    rw [hδb] at hw
    change (schemeSpaceFunctor B S hS).map (eqToHom hA₀) ≫
      ((schemeSpaceFunctor B S hS).map (incl.map (c.π.app i)) ≫ g) = A₀.T.hom
    rw [← hw]
    simp only [g, Functor.map_comp, Category.assoc]
    rfl)
  have hdec : δ.base = v.hom ≫ ((D.stageTestCone E c g).π.app k₀ ≫ u) := by
    apply CostructuredArrow.hom_ext
    rw [hδb]
    change _ = eqToHom hA₀ ≫ (incl.map (c.π.app i) ≫ incl.map (E.map (𝟙 i)) ≫ eqToHom hA.symm)
    simp [E.map_id]
  -- the stage and limit spaces of Stacks 07V7 for the system of base changes above `i`
  let uS : stageAlgebraicSpace B S hS (D.stageSpaceSystem E g)
      (D.isAlgebraicSpace_stageSpaceSystem E g) k₀ ⟶ D.space A.T :=
    ObjectProperty.homMk (D.relativeMap u).hom
  let vS : D.space A₀.T ⟶ (⟨(D.stageSpaceCone E c g).pt, (D.space (D.stageTestCone E c g).pt).2⟩ :
      AlgebraicSpaces B S hS) := ObjectProperty.homMk (D.relativeMap v.hom).hom
  have hsplit : D.relativeMap δ.base = vS ≫ coneProjection B S hS (D.stageSpaceSystem E g)
      (D.isAlgebraicSpace_stageSpaceSystem E g) (D.stageSpaceCone E c g)
      (D.space (D.stageTestCone E c g).pt).2 k₀ ≫ uS := by
    rw [hdec]
    apply ObjectProperty.hom_ext
    change (baseChangeMap D.f _).hom = (baseChangeMap D.f v.hom).hom ≫
      (baseChangeMap D.f ((D.stageTestCone E c g).π.app k₀)).hom ≫ (baseChangeMap D.f u).hom
    rw [baseChangeMap_comp D.f v.hom ((D.stageTestCone E c g).π.app k₀ ≫ u),
      baseChangeMap_comp D.f ((D.stageTestCone E c g).π.app k₀) u]
    rfl
  rw [hsplit] at hmap
  have : (modulePullback B S hS vS).Faithful := D.faithful_modulePullback_relativeMap_of_iso v
  have hmap₂ := map_map_eq_of_map_comp_eq B S hS _ _
    ((modulePullback B S hS vS).map_injective (map_map_eq_of_map_comp_eq B S hS _ _ hmap))
  obtain ⟨h₁, -, -⟩ := finitePresentationModule_isColimit_of_isLimit B S hS hZ
    (D.stageSpaceSystem E g) (D.isAlgebraicSpace_stageSpaceSystem E g)
    (D.stageSpaceCone E c g) (D.space (D.stageTestCone E c g).pt).2
    (D.isAffineHom_stageSpaceSystem_map E g) (D.isQuasiCompactSpace_stageSpaceSystem E g)
    (D.isAbsolutelyQuasiSeparated_stageSpaceSystem E g hZ) (D.isLimit_stageSpaceCone E c g hc)
    (D.siteContainsBaseChangeLimits_stageSpaceSystem E c g hc)
  have hM := isFinitePresentationOnSite_modulePullback B S hS uS _
    (isFinitePresentationOnSite_modulePullback B S hS (D.relativeMap b) A'.F A'.finitePresentation)
  have hN := isFinitePresentationOnSite_modulePullback B S hS uS A.F A.finitePresentation
  obtain ⟨j, e, hj⟩ := h₁ k₀ ((modulePullback B S hS uS).obj
      ((modulePullback B S hS (D.relativeMap b)).obj A'.F)) ((modulePullback B S hS uS).obj A.F)
    hM hN ((modulePullback B S hS uS).map φ) ((modulePullback B S hS uS).map φ') hmap₂
  have hj' := map_comp_eq_of_map_map_eq B S hS _ _ hj
  let w : (D.stageTestSystem E g).obj j ⟶ A.T := (D.stageTestSystem E g).map e ≫ u
  let dx := D.pullbackHom' hst A w
  let ι : D.space (D.pullbackObject' hst A w).T ⟶ stageAlgebraicSpace B S hS
      (D.stageSpaceSystem E g) (D.isAlgebraicSpace_stageSpaceSystem E g) j :=
    ObjectProperty.homMk (𝟙 _)
  have hwι : D.relativeMap dx.base = ι ≫ stageTransition B S hS (D.stageSpaceSystem E g)
      (D.isAlgebraicSpace_stageSpaceSystem E g) e ≫ uS := by
    apply ObjectProperty.hom_ext
    change (baseChangeMap D.f w).hom = 𝟙 _ ≫
      (baseChangeMap D.f ((D.stageTestSystem E g).map e)).hom ≫ (baseChangeMap D.f u).hom
    rw [baseChangeMap_comp D.f ((D.stageTestSystem E g).map e) u, Category.id_comp]
    rfl
  have hw : (modulePullback B S hS (D.relativeMap dx.base)).map φ =
      (modulePullback B S hS (D.relativeMap dx.base)).map φ' := by
    rw [hwι]
    exact map_comp_eq_of_map_map_eq B S hS _ _ (by rw [hj'])
  refine ⟨j.left, j.hom, ⟨D.pullbackObject' hst A w, rfl⟩, dx, ?_,
    D.comp_eq_of_map_fibre_eq dx φ φ' hw⟩
  refine IsHomLift.of_fac' p _ _ rfl hA ?_
  change w.left = _
  have hej : e.left = j.hom := by simpa [k₀] using Over.w e
  change incl.map (E.map e.left) ≫ (incl.map (E.map (𝟙 i)) ≫ eqToHom hA.symm) = _
  have h1 : incl.map (E.map (𝟙 i)) = 𝟙 _ := by
    simp only [CategoryTheory.Functor.map_id]
  rw [hej, h1]
  rfl

include hZ hc in
/-- **The comparison functor of Stacks 07XL for `Coh_{X/Y}` is faithful**: for every cofiltered
system of affine schemes of the site whose limit `T` in schemes lies in the site, the canonical
functor `colim Coh_{X/Y, T_j} ⥤ Coh_{X/Y, T}` is faithful. This is the faithfulness third of
Stacks 08KD. -/
theorem faithful_colimitComparison_coherent :
    letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
    letI : (coherentSiteProjection D.categoryData).IsFibered :=
      D.isFiberedInGroupoids_siteProjection.isFibered
    (Deformation.Artin.colimitComparison (coherentSiteProjection D.categoryData)
      (E ⋙ BigAffineFppf.inclusion B S hS) ((BigAffineFppf.inclusion B S hS).mapCone c)).Faithful :=
  let : Category.{u + 1} (CoherentObject D) := D.categoryData.category
  let : (coherentSiteProjection D.categoryData).IsFibered :=
    D.isFiberedInGroupoids_siteProjection.isFibered
  Deformation.Artin.faithful_of_descentEq (coherentSiteProjection D.categoryData)
    D.isFiberedInGroupoids_siteProjection _ _ (D.descentEq_coherent hZ E c hc)

end Descent

end AlgebraicGeometry.Space.CoherentSituation

end
