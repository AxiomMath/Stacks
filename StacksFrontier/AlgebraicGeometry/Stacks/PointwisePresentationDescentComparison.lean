module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.PointwiseFibrationModulesEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartSliceCounitDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.PointwisePresentationDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.PointwisePresentationHomRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatGroupoidPresentationRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionComparisonAlgebraicSpacePullback

/-!
# Comparing the descent functors of pointwise groupoid presentations

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces and let `F : [U/_pR] ⥤ 𝒳` be a
1-morphism out of its pointwise groupoid fibration into a category fibred in groupoids.  The
descent functor `Φ_F : QCoh(𝒪_𝒳) ⥤ QCoh(U, R, s, t, c)` of
`AlgebraicGeometry.Stack.pointwiseQuasicoherentDescentFunctor` sends `ℱ` to
`(x^*ℱ|_{U_étale}, α)` with `x` the composite of `F` with the inclusion of `𝒮_U`.  This file
proves that `Φ_F` is fully faithful when `F` is fully faithful and covers `𝒳`, and that `Φ_F` is
the descent functor of the identity presentation composed with the inverse image `F^*`:
`Φ_𝟭(F^*ℱ) ≅ Φ_F(ℱ)`.

## Main definitions

* `AlgebraicGeometry.Stack.modulePullbackEtaleIso`: the inverse image of an fppf module, read on
  the étale site, is the inverse image of its étale restriction.
* `AlgebraicGeometry.Stack.quasicoherentModuleIsoMk`: an isomorphism of quasi-coherent modules on
  a groupoid from an isomorphism of underlying modules compatible with the transitions.
* `AlgebraicGeometry.Stack.pointwiseQuasicoherentDescentFunctorPullbackIso`: the isomorphism
  `Φ_𝟭(F^*ℱ) ≅ Φ_F(ℱ)`.

## Main results

* `AlgebraicGeometry.Stack.faithful_pointwiseQuasicoherentDescentFunctor` and
  `AlgebraicGeometry.Stack.full_pointwiseQuasicoherentDescentFunctor`: `Φ_F` is fully faithful.
* `AlgebraicGeometry.Stack.comparisonAlgebraicSpacesModules_presentationPullback`: the comparison
  maps of equation 076R for `F^*ℱ` are those for `ℱ`.

## References

* [Stacks Project, Tag 06WT](https://stacks.math.columbia.edu/tag/06WT)
* [Stacks Project, Tag 076S](https://stacks.math.columbia.edu/tag/076S)
* [Stacks Project, Tag 076R](https://stacks.math.columbia.edu/tag/076R)
* [Stacks Project, Tag 06WR](https://stacks.math.columbia.edu/tag/06WR)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u v w

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The inverse image of fppf modules, read on the inherited étale sites -/

section FppfPullback

universe v' w'

variable {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
  (r : 𝒳 ⥤ BigFppfOver B S hS) (r' : 𝒴 ⥤ BigFppfOver B S hS)
  (hr : r.IsFiberedInGroupoids) (hr' : r'.IsFiberedInGroupoids)
  (K : 𝒳 ⥤ 𝒴) (hK : r.IsFibredOneMorphism r' K) (hK' : K ⋙ r' = r)

/-- The scalar identification of `AlgebraicGeometry.Stack.modulePullback` is that of
`AlgebraicGeometry.Space.inheritedEtaleStructureHom`. -/
theorem eqToHom_ringStructureSheafCore_obj_eq_eq :
    eqToHom (Stack.ringStructureSheafCore_obj_eq B S hS r r' hr hr' K hK' B.topology le_rfl) =
      (inheritedEtaleStructureHom B S hS r r' hr hr' K hK).hom := by
  ext X : 2
  rw [eqToHom_app, inheritedEtaleStructureHom_app, eqToHom_op, eqToHom_map]
  rfl

/-- The scalar identification of `AlgebraicGeometry.Stack.modulePullback`, as a morphism of
sheaves of rings on the inherited étale sites. -/
def modulePullbackEtaleStructureHom :
    letI := inheritedEtale_isContinuous B S hS r r' hr K hK
    FibredSite.ringStructureSheafCore B S hS r hr .etale ⟶
      (K.sheafPushforwardContinuous RingCat.{u}
        (BigFppfOver.associatedTopology B S hS r .etale)
        (BigFppfOver.associatedTopology B S hS r' .etale)).obj
        (FibredSite.ringStructureSheafCore B S hS r' hr' .etale) :=
  letI := inheritedEtale_isContinuous B S hS r r' hr K hK
  ⟨eqToHom (Stack.ringStructureSheafCore_obj_eq B S hS r r' hr hr' K hK' B.topology le_rfl)⟩

/-- The scalar identification `modulePullbackEtaleStructureHom` equals
`AlgebraicGeometry.Space.inheritedEtaleStructureHom`. -/
theorem modulePullbackEtaleStructureHom_eq :
    modulePullbackEtaleStructureHom B S hS r r' hr hr' K hK hK' =
      inheritedEtaleStructureHom B S hS r r' hr hr' K hK :=
  Sheaf.hom_ext (eqToHom_ringStructureSheafCore_obj_eq_eq B S hS r r' hr hr' K hK hK')

/-- `M ↦ M|_{ét}` on fppf modules over `AlgebraicGeometry.Stack.ringStructureSheafCore`. -/
abbrev stackEtale {𝒵 : Type v} [Category.{w} 𝒵] (t : 𝒵 ⥤ BigFppfOver B S hS)
    (ht : t.IsFiberedInGroupoids)
    (M : SheafOfModules.{u} (Stack.ringStructureSheafCore B S hS t ht B.topology le_rfl)) :
    inheritedEtaleModules.{u} B S hS t ht :=
  (Stacks.Sites.CoarserTopology.modulePushforward
    (BigFppfOver.associatedTopology_le_fppf B S hS t .etale)
    (FibredSite.ringStructureSheafCore B S hS t ht .fppf)).obj
    (M : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS t ht .fppf))

/-- **The inverse image of an fppf module, read on the étale site, is the inverse image of the
étale module**: `(K^*M)|_{ét} ≅ K^*(M|_{ét})`, with identity components.  On the left `K^*` is
`AlgebraicGeometry.Stack.modulePullback`, on the right
`AlgebraicGeometry.Space.inheritedEtalePullback`; both restrict sections along `K`. -/
def modulePullbackEtaleIso
    (M : SheafOfModules.{u} (Stack.ringStructureSheafCore B S hS r' hr' B.topology le_rfl)) :
    stackEtale B S hS r hr
        ((Stack.modulePullback.{u, v, w, u, v', w'} B S hS r r' hr hr' K hK' B.topology
          le_rfl).obj M) ≅
      (inheritedEtalePullback B S hS r r' hr hr' K hK).obj (stackEtale B S hS r' hr' M) :=
  letI := inheritedEtale_isContinuous B S hS r r' hr K hK
  (SheafOfModules.pushforwardCongr
    (modulePullbackEtaleStructureHom_eq B S hS r r' hr hr' K hK hK')).app
      (stackEtale B S hS r' hr' M)

/-- The components of the hom of `modulePullbackEtaleIso` are identities on sections. -/
theorem modulePullbackEtaleIso_hom_val_app
    (M : SheafOfModules.{u} (Stack.ringStructureSheafCore B S hS r' hr' B.topology le_rfl))
    (X : 𝒳ᵒᵖ) (x) :
    (modulePullbackEtaleIso B S hS r r' hr hr' K hK hK' M).hom.val.app X x = x := rfl

/-- The components of the inverse of `modulePullbackEtaleIso` are identities on sections. -/
theorem modulePullbackEtaleIso_inv_val_app
    (M : SheafOfModules.{u} (Stack.ringStructureSheafCore B S hS r' hr' B.topology le_rfl))
    (X : 𝒳ᵒᵖ) (x) :
    (modulePullbackEtaleIso B S hS r r' hr hr' K hK hK' M).inv.val.app X x = x := rfl

end FppfPullback

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

/-! ### Full faithfulness, for a full faithful pointwise presentation covering its target -/

section FullyFaithful

variable {A : AlgebraicSpaces C S hS} {G : GroupoidInAlgebraicSpaces C S hS A}
  {𝒳 : Type v} [Category.{w} 𝒳] {p : 𝒳 ⥤ BigFppfOver C S hS}
  (F : PointwiseFibration G ⥤ 𝒳)
  (hF : F ⋙ p = (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p)
  (hp : p.IsFiberedInGroupoids)

/-- On morphisms, `Φ_F` restricts a morphism of modules to the object space of the groupoid. -/
theorem pointwiseQuasicoherentDescentFunctor_map_hom
    {M N : FibredSite.quasicoherentModules.{u, v, w, u} C S hS p hp} (ψ : M ⟶ N) :
    ((pointwiseQuasicoherentDescentFunctor F hF hp).map ψ).hom =
      presentationObjectRestrictionMap F hF ψ.hom := rfl

/-- The transition of `Φ_F(M)` is the target comparison map followed by the inverse of the source
comparison map. -/
theorem pointwiseQuasicoherentDescentFunctor_obj_alpha
    (M : FibredSite.quasicoherentModules.{u, v, w, u} C S hS p hp) :
    haveI : IsIso (presentationSourceComparison (hp := hp) F hF M.obj) :=
      (isPointwiseDescentAdmissible_of_quasicoherent F hF M).2.1
    ((pointwiseQuasicoherentDescentFunctor F hF hp).obj M).alpha =
      presentationTargetComparison F hF M.obj ≫
        inv (presentationSourceComparison F hF M.obj) :=
  pointwiseDescentObj_alpha F hF _ (isPointwiseDescentAdmissible_of_quasicoherent F hF M)

variable [F.Full] (hloc : ∀ y : 𝒳, ∃ (I : Type u)
  (x : I → PointwiseFibration G) (g : ∀ i, F.obj (x i) ⟶ y),
    Sieve.ofArrows _ g ∈ BigFppfOver.associatedTopology C S hS p .fppf y)

include hloc in
/-- **The descent functor is faithful**: `Φ_F` is faithful when `F` is fully faithful and covers
`𝒳`. -/
theorem faithful_pointwiseQuasicoherentDescentFunctor :
    (pointwiseQuasicoherentDescentFunctor F hF hp).Faithful where
  map_injective {M N} f g h := by
    have h' := congrArg Space.QuasicoherentModule.Hom.hom h
    exact ObjectProperty.hom_ext _
      ((presentationObjectRestrictionMap_injective_and_range F hF hloc M.property N.obj).1 h')

include hloc in
/-- **The descent functor is full**: `Φ_F` is full when `F` is fully faithful and covers `𝒳`. -/
theorem full_pointwiseQuasicoherentDescentFunctor :
    (pointwiseQuasicoherentDescentFunctor F hF hp).Full where
  map_surjective {M N} φ := by
    obtain ⟨_, hrange⟩ := presentationObjectRestrictionMap_injective_and_range F hF hloc
      M.property N.obj
    have hcs : IsIso (presentationSourceComparison (hp := hp) F hF M.obj) :=
      (isPointwiseDescentAdmissible_of_quasicoherent F hF M).2.1
    have hcsN : IsIso (presentationSourceComparison (hp := hp) F hF N.obj) :=
      (isPointwiseDescentAdmissible_of_quasicoherent F hF N).2.1
    have hc := φ.comm
    rw [pointwiseQuasicoherentDescentFunctor_obj_alpha,
      pointwiseQuasicoherentDescentFunctor_obj_alpha] at hc
    obtain ⟨ψ, hψ⟩ := (hrange φ.hom).2 ⟨inv (presentationSourceComparison F hF M.obj) ≫
        (Space.modulePullback C S hS G.source).map φ.hom ≫
          presentationSourceComparison F hF N.obj, IsIso.hom_inv_id_assoc _ _,
      @comp_inv_comp_eq_of_comp_inv _ _ _ _ _ _ _ _ _ _ hcs _ _ hcsN _ _ hc⟩
    exact ⟨ObjectProperty.homMk ψ, Space.QuasicoherentModule.Hom.ext hψ⟩

end FullyFaithful

/-! ### Comparison maps and inverse image along a 1-morphism, for fppf modules -/

section PullbackGeneral

universe v' w' v₁ w₁ v₂ w₂

variable {𝒳 : Type v} [Category.{w} 𝒳] {p : 𝒳 ⥤ BigFppfOver C S hS}
  {𝒴 : Type v'} [Category.{w'} 𝒴] (r' : 𝒴 ⥤ BigFppfOver C S hS) (hr' : r'.IsFiberedInGroupoids)
  (K : 𝒴 ⥤ 𝒳) (hK : K ⋙ p = r') (hp : p.IsFiberedInGroupoids)

include hK hp in
/-- A functor `K` with `K ⋙ p = r'` into a category fibred in groupoids is a fibred
1-morphism. -/
theorem isFibredOneMorphism_pullbackFunctor :
    r'.IsFibredOneMorphism p K :=
  hp.isFibredOneMorphism hK

variable {U : AlgebraicSpaces C S hS} {𝒰 : Type v₁} [Category.{w₁} 𝒰]
  (p𝒰 : 𝒰 ⥤ BigFppfOver C S hS) (hp𝒰 : p𝒰.IsFiberedInGroupoids)
  (eU : StacksRepresentableCFG.EquivalenceOver p𝒰
    (presheafOfCategories (U.1 ⋙ typeToCat)).p)

/-- **`f^*(F^*ℱ)|_{U_étale} ≅ (f ⋙ K)^*ℱ|_{U_étale}`**, with identity components, for a
1-morphism `f` into the pointwise groupoid fibration. -/
def pullbackRestrictionIso
    (f : 𝒰 ⥤ 𝒴)
    (hf : p𝒰.IsFibredOneMorphism
      r' f)
    (hfK : p𝒰.IsFibredOneMorphism p (f ⋙ K))
    (ℱ : SheafOfModules.{u} (Stack.ringStructureSheafCore C S hS p hp C.topology le_rfl)) :
    Space.etaleRestrictedModuleInverseImage C S hS p𝒰 _ hp𝒰
        hr' eU f hf
        (Space.stackEtale C S hS _ hr'
          ((Stack.modulePullback.{u, v', w', u, v, w} C S hS _ p
            hr' hp K hK C.topology le_rfl).obj ℱ)) ≅
      Space.etaleRestrictedModuleInverseImage C S hS p𝒰 p hp𝒰 hp eU (f ⋙ K) hfK
        (Space.stackEtale C S hS p hp ℱ) :=
  haveI := Space.etaleChartToFibred_isContinuous C S hS p𝒰 _ hp𝒰 eU f hf
  (SheafOfModules.pushforward (Space.etaleChartStructureHom C S hS p𝒰 _ hp𝒰
      hr' eU f hf)).mapIso
    (Space.modulePullbackEtaleIso C S hS _ p hr' hp K
      (isFibredOneMorphism_pullbackFunctor r' K hK hp) hK ℱ) ≪≫
  Space.etaleRestrictedModuleInverseImagePullbackIso C S hS _ p
    hr' hp K (isFibredOneMorphism_pullbackFunctor r' K hK hp)
    p𝒰 hp𝒰 eU f hf hfK (Space.stackEtale C S hS p hp ℱ)

/-- The hom of `pullbackRestrictionIso` is the inverse image of the hom of
`AlgebraicGeometry.Space.modulePullbackEtaleIso` followed by the hom of
`AlgebraicGeometry.Space.etaleRestrictedModuleInverseImagePullbackIso`. -/
theorem pullbackRestrictionIso_hom
    (f : 𝒰 ⥤ 𝒴)
    (hf : p𝒰.IsFibredOneMorphism
      r' f)
    (hfK : p𝒰.IsFibredOneMorphism p (f ⋙ K))
    (ℱ : SheafOfModules.{u} (Stack.ringStructureSheafCore C S hS p hp C.topology le_rfl)) :
    (pullbackRestrictionIso r' hr' K hK hp p𝒰 hp𝒰 eU f hf hfK ℱ).hom =
      Space.etaleRestrictedModuleInverseImageMap C S hS p𝒰 _ hp𝒰
          hr' eU f hf
          (Space.modulePullbackEtaleIso C S hS _ p hr' hp
            K (isFibredOneMorphism_pullbackFunctor r' K hK hp) hK ℱ).hom ≫
        (Space.etaleRestrictedModuleInverseImagePullbackIso C S hS _ p
          hr' hp K
          (isFibredOneMorphism_pullbackFunctor r' K hK hp) p𝒰 hp𝒰 eU f hf hfK
          (Space.stackEtale C S hS p hp ℱ)).hom := rfl

variable {V : AlgebraicSpaces C S hS} {𝒱 : Type v₂} [Category.{w₂} 𝒱]
  (q𝒱 : 𝒱 ⥤ BigFppfOver C S hS) (hq𝒱 : q𝒱.IsFiberedInGroupoids)
  (eV : StacksRepresentableCFG.EquivalenceOver q𝒱
    (presheafOfCategories (V.1 ⋙ typeToCat)).p)

/-- **The comparison maps of equation 076R for `F^*ℱ` on the pointwise groupoid fibration are
those of `ℱ` on `𝒳`.**  For a 2-commutative triangle `φ : a ⋙ g ≅ f` into the pointwise groupoid
fibration, the comparison map of `φ` for `F^*ℱ` is the comparison map of `F ∘ φ` for `ℱ`, through
the identifications of `AlgebraicGeometry.Stack.pullbackRestrictionIso`. -/
theorem comparisonAlgebraicSpacesModules_pullbackFunctor
    (a : 𝒰 ⥤ 𝒱) (f : 𝒰 ⥤ 𝒴) (g : 𝒱 ⥤ 𝒴)
    (hf : p𝒰.IsFibredOneMorphism
      r' f)
    (hg : q𝒱.IsFibredOneMorphism
      r' g)
    (hfK : p𝒰.IsFibredOneMorphism p (f ⋙ K)) (hgK : q𝒱.IsFibredOneMorphism p (g ⋙ K))
    (φ : a ⋙ g ≅ f) (aSpace : U ⟶ V)
    (ha : Space.schemeChartFunctor C S hS U.1 p𝒰 eU ⋙ a ≅
      CostructuredArrow.map aSpace.hom ⋙ Space.schemeChartFunctor C S hS V.1 q𝒱 eV)
    (hφ : ∀ X : 𝒰, r'.IsHomLift (𝟙 _) (φ.inv.app X))
    (hab : ∀ Z : CostructuredArrow yoneda U.1,
      q𝒱.IsHomLift (𝟙 (q𝒱.obj (a.obj ((Space.schemeChartFunctor C S hS U.1 p𝒰 eU).obj Z))))
        (ha.hom.app Z))
    (hφK : ∀ X : 𝒰, p.IsHomLift (𝟙 (p.obj ((f ⋙ K).obj X)))
      ((Space.whiskerTriangleIso K f a g φ).inv.app X))
    (ℱ : SheafOfModules.{u} (Stack.ringStructureSheafCore C S hS p hp C.topology le_rfl)) :
    Space.comparisonAlgebraicSpacesModules C S hS p𝒰 q𝒱 _ hp𝒰 hq𝒱 eU eV a f g hf hg φ aSpace ha
        hr' hφ hab
        (Space.stackEtale C S hS _ hr'
          ((Stack.modulePullback.{u, v', w', u, v, w} C S hS _ p
            hr' hp K hK C.topology le_rfl).obj ℱ)) ≫
      (pullbackRestrictionIso r' hr' K hK hp p𝒰 hp𝒰 eU f hf hfK ℱ).hom =
    (Space.modulePullback C S hS aSpace).map
        (pullbackRestrictionIso r' hr' K hK hp q𝒱 hq𝒱 eV g hg hgK ℱ).hom ≫
      Space.comparisonAlgebraicSpacesModules C S hS p𝒰 q𝒱 p hp𝒰 hq𝒱 eU eV a (f ⋙ K) (g ⋙ K)
        hfK hgK (Space.whiskerTriangleIso K f a g φ) aSpace ha hp hφK hab
        (Space.stackEtale C S hS p hp ℱ) := by
  have n := Space.comparisonAlgebraicSpacesModules_naturality C S hS p𝒰 q𝒱 _ hp𝒰 hq𝒱 eU eV a f
    g hf hg φ aSpace ha hr' hφ hab
    (Space.modulePullbackEtaleIso C S hS _ p hr' hp
      K (isFibredOneMorphism_pullbackFunctor r' K hK hp) hK ℱ).hom
  have b := Space.comparisonAlgebraicSpacesModules_inheritedEtalePullback C S hS _ p
    hr' hp K (isFibredOneMorphism_pullbackFunctor r' K hK hp)
    p𝒰 hp𝒰 eU f hf hfK q𝒱 hq𝒱 eV a g hg hgK φ aSpace ha hφ hab hφK
    (Space.stackEtale C S hS p hp ℱ)
  rw [pullbackRestrictionIso_hom, pullbackRestrictionIso_hom,
    Functor.map_comp, ← Category.assoc, n, Category.assoc, b, ← Category.assoc]

end PullbackGeneral

/-! ### Reduction along a pointwise presentation to the pointwise groupoid fibration -/

section Reduction

universe v₁ w₁ v₂ w₂


variable {A : AlgebraicSpaces C S hS} {G : GroupoidInAlgebraicSpaces C S hS A}
  {𝒳 : Type v} [Category.{w} 𝒳] {p : 𝒳 ⥤ BigFppfOver C S hS}
  (F : PointwiseFibration G ⥤ 𝒳)
  (hF : F ⋙ p = (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p)
  (hp : p.IsFiberedInGroupoids)

/-- A quasi-coherent module on a groupoid is determined up to isomorphism by an isomorphism of
the underlying modules compatible with the transitions. -/
def quasicoherentModuleIsoMk {Q₁ Q₂ : Space.QuasicoherentModule C S hS G} (φ : Q₁ ⟶ Q₂)
    (hφ : IsIso φ.hom) : Q₁ ≅ Q₂ where
  hom := φ
  inv := ⟨inv φ.hom, by
    have h := φ.comm
    rw [Functor.map_inv, Functor.map_inv, IsIso.eq_inv_comp, ← Category.assoc, ← h,
      Category.assoc, IsIso.hom_inv_id, Category.comp_id]⟩
  hom_inv_id := Space.QuasicoherentModule.Hom.ext (IsIso.hom_inv_id φ.hom)
  inv_hom_id := Space.QuasicoherentModule.Hom.ext (IsIso.inv_hom_id φ.hom)

include hF hp in
/-- A pointwise presentation `F` with `F ⋙ p` the structure functor of the pointwise groupoid
fibration is a fibred 1-morphism. -/
theorem isFibredOneMorphism_presentation :
    (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p.IsFibredOneMorphism
      p F :=
  hp.isFibredOneMorphism hF

variable {U : AlgebraicSpaces C S hS} {𝒰 : Type v₁} [Category.{w₁} 𝒰]
  (p𝒰 : 𝒰 ⥤ BigFppfOver C S hS) (hp𝒰 : p𝒰.IsFiberedInGroupoids)
  (eU : StacksRepresentableCFG.EquivalenceOver p𝒰
    (presheafOfCategories (U.1 ⋙ typeToCat)).p)

/-- **`f^*(F^*ℱ)|_{U_étale} ≅ (f ⋙ F)^*ℱ|_{U_étale}`**, with identity components, for a
1-morphism `f` into the pointwise groupoid fibration. -/
def presentationPullbackRestrictionIso
    (f : 𝒰 ⥤ PointwiseFibration G)
    (hf : p𝒰.IsFibredOneMorphism
      (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p f)
    (hfF : p𝒰.IsFibredOneMorphism p (f ⋙ F))
    (ℱ : SheafOfModules.{u} (Stack.ringStructureSheafCore C S hS p hp C.topology le_rfl)) :
    Space.etaleRestrictedModuleInverseImage C S hS p𝒰 _ hp𝒰
        (isFiberedInGroupoids_presheafOfGroupoids _) eU f hf
        (Space.stackEtale C S hS _ (isFiberedInGroupoids_presheafOfGroupoids _)
          ((Stack.modulePullback.{u, u + 1, u, u, v, w} C S hS _ p
            (isFiberedInGroupoids_presheafOfGroupoids _) hp F hF C.topology le_rfl).obj ℱ)) ≅
      Space.etaleRestrictedModuleInverseImage C S hS p𝒰 p hp𝒰 hp eU (f ⋙ F) hfF
        (Space.stackEtale C S hS p hp ℱ) :=
  haveI := Space.etaleChartToFibred_isContinuous C S hS p𝒰 _ hp𝒰 eU f hf
  (SheafOfModules.pushforward (Space.etaleChartStructureHom C S hS p𝒰 _ hp𝒰
      (isFiberedInGroupoids_presheafOfGroupoids _) eU f hf)).mapIso
    (Space.modulePullbackEtaleIso C S hS _ p (isFiberedInGroupoids_presheafOfGroupoids _) hp F
      (isFibredOneMorphism_presentation F hF hp) hF ℱ) ≪≫
  Space.etaleRestrictedModuleInverseImagePullbackIso C S hS _ p
    (isFiberedInGroupoids_presheafOfGroupoids _) hp F (isFibredOneMorphism_presentation F hF hp)
    p𝒰 hp𝒰 eU f hf hfF (Space.stackEtale C S hS p hp ℱ)

/-- The hom of `presentationPullbackRestrictionIso` is the inverse image of the hom of
`AlgebraicGeometry.Space.modulePullbackEtaleIso` followed by the hom of
`AlgebraicGeometry.Space.etaleRestrictedModuleInverseImagePullbackIso`. -/
theorem presentationPullbackRestrictionIso_hom
    (f : 𝒰 ⥤ PointwiseFibration G)
    (hf : p𝒰.IsFibredOneMorphism
      (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p f)
    (hfF : p𝒰.IsFibredOneMorphism p (f ⋙ F))
    (ℱ : SheafOfModules.{u} (Stack.ringStructureSheafCore C S hS p hp C.topology le_rfl)) :
    (presentationPullbackRestrictionIso F hF hp p𝒰 hp𝒰 eU f hf hfF ℱ).hom =
      Space.etaleRestrictedModuleInverseImageMap C S hS p𝒰 _ hp𝒰
          (isFiberedInGroupoids_presheafOfGroupoids _) eU f hf
          (Space.modulePullbackEtaleIso C S hS _ p (isFiberedInGroupoids_presheafOfGroupoids _) hp
            F (isFibredOneMorphism_presentation F hF hp) hF ℱ).hom ≫
        (Space.etaleRestrictedModuleInverseImagePullbackIso C S hS _ p
          (isFiberedInGroupoids_presheafOfGroupoids _) hp F
          (isFibredOneMorphism_presentation F hF hp) p𝒰 hp𝒰 eU f hf hfF
          (Space.stackEtale C S hS p hp ℱ)).hom := rfl

variable {V : AlgebraicSpaces C S hS} {𝒱 : Type v₂} [Category.{w₂} 𝒱]
  (q𝒱 : 𝒱 ⥤ BigFppfOver C S hS) (hq𝒱 : q𝒱.IsFiberedInGroupoids)
  (eV : StacksRepresentableCFG.EquivalenceOver q𝒱
    (presheafOfCategories (V.1 ⋙ typeToCat)).p)

/-- **The comparison maps of equation 076R for `F^*ℱ` on the pointwise groupoid fibration are
those of `ℱ` on `𝒳`.**  For a 2-commutative triangle `φ : a ⋙ g ≅ f` into the pointwise groupoid
fibration, the comparison map of `φ` for `F^*ℱ` is the comparison map of `F ∘ φ` for `ℱ`, through
the identifications of `AlgebraicGeometry.Stack.presentationPullbackRestrictionIso`. -/
theorem comparisonAlgebraicSpacesModules_presentationPullback
    (a : 𝒰 ⥤ 𝒱) (f : 𝒰 ⥤ PointwiseFibration G) (g : 𝒱 ⥤ PointwiseFibration G)
    (hf : p𝒰.IsFibredOneMorphism
      (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p f)
    (hg : q𝒱.IsFibredOneMorphism
      (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p g)
    (hfF : p𝒰.IsFibredOneMorphism p (f ⋙ F)) (hgF : q𝒱.IsFibredOneMorphism p (g ⋙ F))
    (φ : a ⋙ g ≅ f) (aSpace : U ⟶ V)
    (ha : Space.schemeChartFunctor C S hS U.1 p𝒰 eU ⋙ a ≅
      CostructuredArrow.map aSpace.hom ⋙ Space.schemeChartFunctor C S hS V.1 q𝒱 eV)
    (hφ : ∀ X : 𝒰, (presheafOfGroupoids (evaluationGroupoidFunctor
      G.toGroupoidInFunctors)).p.IsHomLift (𝟙 _) (φ.inv.app X))
    (hab : ∀ Z : CostructuredArrow yoneda U.1,
      q𝒱.IsHomLift (𝟙 (q𝒱.obj (a.obj ((Space.schemeChartFunctor C S hS U.1 p𝒰 eU).obj Z))))
        (ha.hom.app Z))
    (hφF : ∀ X : 𝒰, p.IsHomLift (𝟙 (p.obj ((f ⋙ F).obj X)))
      ((Space.whiskerTriangleIso F f a g φ).inv.app X))
    (ℱ : SheafOfModules.{u} (Stack.ringStructureSheafCore C S hS p hp C.topology le_rfl)) :
    Space.comparisonAlgebraicSpacesModules C S hS p𝒰 q𝒱 _ hp𝒰 hq𝒱 eU eV a f g hf hg φ aSpace ha
        (isFiberedInGroupoids_presheafOfGroupoids _) hφ hab
        (Space.stackEtale C S hS _ (isFiberedInGroupoids_presheafOfGroupoids _)
          ((Stack.modulePullback.{u, u + 1, u, u, v, w} C S hS _ p
            (isFiberedInGroupoids_presheafOfGroupoids _) hp F hF C.topology le_rfl).obj ℱ)) ≫
      (presentationPullbackRestrictionIso F hF hp p𝒰 hp𝒰 eU f hf hfF ℱ).hom =
    (Space.modulePullback C S hS aSpace).map
        (presentationPullbackRestrictionIso F hF hp q𝒱 hq𝒱 eV g hg hgF ℱ).hom ≫
      Space.comparisonAlgebraicSpacesModules C S hS p𝒰 q𝒱 p hp𝒰 hq𝒱 eU eV a (f ⋙ F) (g ⋙ F)
        hfF hgF (Space.whiskerTriangleIso F f a g φ) aSpace ha hp hφF hab
        (Space.stackEtale C S hS p hp ℱ) := by
  exact comparisonAlgebraicSpacesModules_pullbackFunctor _ _ F hF hp p𝒰 hp𝒰 eU q𝒱 hq𝒱 eV a f g hf hg
    hfF hgF φ aSpace ha hφ hab hφF ℱ

end Reduction

/-! ### `Φ_F(ℱ) ≅ Φ_𝟭(F^*ℱ)` -/

section ReductionIso

variable {A : AlgebraicSpaces C S hS} {G : GroupoidInAlgebraicSpaces C S hS A}
  {𝒳 : Type v} [Category.{w} 𝒳] {p : 𝒳 ⥤ BigFppfOver C S hS}
  (F : PointwiseFibration G ⥤ 𝒳)
  (hF : F ⋙ p = (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p)
  (hp : p.IsFiberedInGroupoids)

variable (G) in
/-- The identity of the pointwise groupoid fibration is a pointwise presentation. -/
theorem pointwiseFibration_id_comp :
    𝟭 (PointwiseFibration G) ⋙
        (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p =
      (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p :=
  Functor.id_comp _

/-- The comparison map through the source of `F^*ℱ` is that of `ℱ`. -/
theorem presentationSourceComparison_pullback
    (ℱ : SheafOfModules.{u} (Stack.ringStructureSheafCore C S hS p hp C.topology le_rfl)) :
    pointwisePresentationSourceComparison (𝟭 (PointwiseFibration G)) (pointwiseFibration_id_comp G)
        (Space.stackEtale C S hS _ (isFiberedInGroupoids_presheafOfGroupoids _)
          ((Stack.modulePullback.{u, u + 1, u, u, v, w} C S hS _ p
            (isFiberedInGroupoids_presheafOfGroupoids _) hp F hF C.topology le_rfl).obj ℱ)) ≫
      (presentationPullbackRestrictionIso F hF hp (spaceProj G.arrows)
        (isFiberedInGroupoids_arrows G)
        (spacePresentation G.arrows) (pointwisePresentationSource (𝟭 (PointwiseFibration G)))
        (isFibredOneMorphism_pointwisePresentationSource (𝟭 (PointwiseFibration G))
          (pointwiseFibration_id_comp G)
          (isFiberedInGroupoids_presheafOfGroupoids _))
        (isFibredOneMorphism_pointwisePresentationSource F hF hp) ℱ).hom =
    (Space.modulePullback C S hS G.source).map (presentationPullbackRestrictionIso F hF hp
        (spaceProj G.objects) (isFiberedInGroupoids_objects G)
        (spacePresentation G.objects) (pointwisePresentationObject (𝟭 (PointwiseFibration G)))
        (isFibredOneMorphism_pointwisePresentationObject (𝟭 (PointwiseFibration G))
          (pointwiseFibration_id_comp G)
          (isFiberedInGroupoids_presheafOfGroupoids _))
        (isFibredOneMorphism_pointwisePresentationObject F hF hp) ℱ).hom ≫
      pointwisePresentationSourceComparison F hF (Space.stackEtale C S hS p hp ℱ) := by
  have h1 := comparisonAlgebraicSpacesModules_presentationPullback F hF hp (spaceProj G.arrows)
    (isFiberedInGroupoids_arrows G) (spacePresentation G.arrows) (spaceProj G.objects)
    (isFiberedInGroupoids_objects G) (spacePresentation G.objects)
    (spaceFunctor G.source) (pointwisePresentationSource (𝟭 _)) (pointwisePresentationObject (𝟭 _))
    (isFibredOneMorphism_pointwisePresentationSource (𝟭 _) (pointwiseFibration_id_comp G)
      (isFiberedInGroupoids_presheafOfGroupoids _))
    (isFibredOneMorphism_pointwisePresentationObject (𝟭 _) (pointwiseFibration_id_comp G)
      (isFiberedInGroupoids_presheafOfGroupoids _))
    (isFibredOneMorphism_pointwisePresentationSource F hF hp)
    (isFibredOneMorphism_pointwisePresentationObject F hF hp) (Iso.refl _) G.source
      (spaceFunctorChartIso G.source)
    (isHomLift_pointwisePresentationSource_refl (𝟭 _)) (isHomLift_sourceChartIso G)
    (fun X => Space.isHomLift_whiskerTriangleIso_inv_app C S hS _ p F
      (isFibredOneMorphism_presentation F hF hp) _ _ _ _
      (isHomLift_pointwisePresentationSource_refl (𝟭 _)) X) ℱ
  have h2 := Space.comparisonAlgebraicSpacesModules_congr C S hS (spaceProj G.arrows)
    (spaceProj G.objects) p (isFiberedInGroupoids_arrows G) (isFiberedInGroupoids_objects G) hp
    (spacePresentation G.arrows) (spacePresentation G.objects) (pointwisePresentationSource F)
    (pointwisePresentationObject F) (isFibredOneMorphism_pointwisePresentationSource F hF hp)
    (isFibredOneMorphism_pointwisePresentationObject F hF hp) G.source (spaceFunctor G.source)
    (spaceFunctor G.source) (Space.whiskerTriangleIso F (pointwisePresentationSource (𝟭 _))
      (spaceFunctor G.source) (pointwisePresentationObject (𝟭 _)) (Iso.refl _))
    (Iso.refl (pointwisePresentationSource F)) (spaceFunctorChartIso G.source)
      (spaceFunctorChartIso G.source)
    (fun X => Space.isHomLift_whiskerTriangleIso_inv_app C S hS _ p F
      (isFibredOneMorphism_presentation F hF hp) _ _ _ _
      (isHomLift_pointwisePresentationSource_refl (𝟭 _)) X)
    (isHomLift_pointwisePresentationSource_refl F) (isHomLift_sourceChartIso G)
    (isHomLift_sourceChartIso G)
    (Space.stackEtale C S hS p hp ℱ) (fun d => by simp [Space.comparisonMorphism])
  exact h1.trans (congrArg (fun c => _ ≫ c) h2)

/-- The comparison map through the target of `F^*ℱ` is that of `ℱ`. -/
theorem presentationTargetComparison_pullback
    (ℱ : SheafOfModules.{u} (Stack.ringStructureSheafCore C S hS p hp C.topology le_rfl)) :
    pointwisePresentationTargetComparison (𝟭 (PointwiseFibration G)) (pointwiseFibration_id_comp G)
        (Space.stackEtale C S hS _ (isFiberedInGroupoids_presheafOfGroupoids _)
          ((Stack.modulePullback.{u, u + 1, u, u, v, w} C S hS _ p
            (isFiberedInGroupoids_presheafOfGroupoids _) hp F hF C.topology le_rfl).obj ℱ)) ≫
      (presentationPullbackRestrictionIso F hF hp (spaceProj G.arrows)
        (isFiberedInGroupoids_arrows G)
        (spacePresentation G.arrows) (pointwisePresentationSource (𝟭 (PointwiseFibration G)))
        (isFibredOneMorphism_pointwisePresentationSource (𝟭 (PointwiseFibration G))
          (pointwiseFibration_id_comp G)
          (isFiberedInGroupoids_presheafOfGroupoids _))
        (isFibredOneMorphism_pointwisePresentationSource F hF hp) ℱ).hom =
    (Space.modulePullback C S hS G.target).map (presentationPullbackRestrictionIso F hF hp
        (spaceProj G.objects) (isFiberedInGroupoids_objects G)
        (spacePresentation G.objects) (pointwisePresentationObject (𝟭 (PointwiseFibration G)))
        (isFibredOneMorphism_pointwisePresentationObject (𝟭 (PointwiseFibration G))
          (pointwiseFibration_id_comp G)
          (isFiberedInGroupoids_presheafOfGroupoids _))
        (isFibredOneMorphism_pointwisePresentationObject F hF hp) ℱ).hom ≫
      pointwisePresentationTargetComparison F hF (Space.stackEtale C S hS p hp ℱ) := by
  have h1 := comparisonAlgebraicSpacesModules_presentationPullback F hF hp (spaceProj G.arrows)
    (isFiberedInGroupoids_arrows G) (spacePresentation G.arrows) (spaceProj G.objects)
    (isFiberedInGroupoids_objects G) (spacePresentation G.objects)
    (spaceFunctor G.target) (pointwisePresentationSource (𝟭 _)) (pointwisePresentationObject (𝟭 _))
    (isFibredOneMorphism_pointwisePresentationSource (𝟭 _) (pointwiseFibration_id_comp G)
      (isFiberedInGroupoids_presheafOfGroupoids _))
    (isFibredOneMorphism_pointwisePresentationObject (𝟭 _) (pointwiseFibration_id_comp G)
      (isFiberedInGroupoids_presheafOfGroupoids _))
    (isFibredOneMorphism_pointwisePresentationSource F hF hp)
    (isFibredOneMorphism_pointwisePresentationObject F hF hp)
    (pointwisePresentationTwoIso (𝟭 _)) G.target (spaceFunctorChartIso G.target)
    (isHomLift_pointwisePresentationTwoIso_inv_app (𝟭 _) (pointwiseFibration_id_comp G))
      (isHomLift_targetChartIso G)
    (fun X => Space.isHomLift_whiskerTriangleIso_inv_app C S hS _ p F
      (isFibredOneMorphism_presentation F hF hp) _ _ _ _
      (isHomLift_pointwisePresentationTwoIso_inv_app (𝟭 _) (pointwiseFibration_id_comp G)) X) ℱ
  have h2 := Space.comparisonAlgebraicSpacesModules_congr C S hS (spaceProj G.arrows)
    (spaceProj G.objects) p (isFiberedInGroupoids_arrows G) (isFiberedInGroupoids_objects G) hp
    (spacePresentation G.arrows) (spacePresentation G.objects) (pointwisePresentationSource F)
    (pointwisePresentationObject F) (isFibredOneMorphism_pointwisePresentationSource F hF hp)
    (isFibredOneMorphism_pointwisePresentationObject F hF hp) G.target (spaceFunctor G.target)
    (spaceFunctor G.target) (Space.whiskerTriangleIso F (pointwisePresentationSource (𝟭 _))
      (spaceFunctor G.target) (pointwisePresentationObject (𝟭 _))
      (pointwisePresentationTwoIso (𝟭 _)))
    (pointwisePresentationTwoIso F) (spaceFunctorChartIso G.target) (spaceFunctorChartIso G.target)
    (fun X => Space.isHomLift_whiskerTriangleIso_inv_app C S hS _ p F
      (isFibredOneMorphism_presentation F hF hp) _ _ _ _
      (isHomLift_pointwisePresentationTwoIso_inv_app (𝟭 _) (pointwiseFibration_id_comp G)) X)
    (isHomLift_pointwisePresentationTwoIso_inv_app F hF) (isHomLift_targetChartIso G)
    (isHomLift_targetChartIso G) (Space.stackEtale C S hS p hp ℱ)
    (fun d => by simp [Space.comparisonMorphism, pointwisePresentationTwoArrow])
  exact h1.trans (congrArg (fun c => _ ≫ c) h2)

/-- The transition of `Φ_K(M)` is `pointwisePresentationTransition` of the étale restriction
of `M`. -/
theorem pointwiseQuasicoherentDescentFunctor_obj_alpha_transition
    {𝒴 : Type v} [Category.{w} 𝒴] {q : 𝒴 ⥤ BigFppfOver C S hS}
    (K : PointwiseFibration G ⥤ 𝒴)
    (hK : K ⋙ q = (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p)
    (hq : q.IsFiberedInGroupoids)
    (M : FibredSite.quasicoherentModules.{u, v, w, u} C S hS q hq) :
    haveI : IsIso (pointwisePresentationSourceComparison K hK
        ((Stacks.Sites.CoarserTopology.modulePushforward
          (BigFppfOver.associatedTopology_le_fppf C S hS q .etale) _).obj M.obj)) :=
      (isPointwiseDescentAdmissible_of_quasicoherent K hK M).2.1
    ((pointwiseQuasicoherentDescentFunctor K hK hq).obj M).alpha =
      pointwisePresentationTransition K hK
        ((Stacks.Sites.CoarserTopology.modulePushforward
          (BigFppfOver.associatedTopology_le_fppf C S hS q .etale) _).obj M.obj) := rfl

/-- The transition of `F^*ℱ` is that of `ℱ`. -/
theorem pointwisePresentationTransition_pullback
    (ℱ : SheafOfModules.{u} (Stack.ringStructureSheafCore C S hS p hp C.topology le_rfl))
    [IsIso (pointwisePresentationSourceComparison (𝟭 (PointwiseFibration G))
      (pointwiseFibration_id_comp G) (Space.stackEtale C S hS _
          (isFiberedInGroupoids_presheafOfGroupoids _)
          ((Stack.modulePullback.{u, u + 1, u, u, v, w} C S hS _ p
            (isFiberedInGroupoids_presheafOfGroupoids _) hp F hF C.topology le_rfl).obj ℱ)))]
    [IsIso (pointwisePresentationSourceComparison F hF (Space.stackEtale C S hS p hp ℱ))] :
    pointwisePresentationTransition (𝟭 (PointwiseFibration G)) (pointwiseFibration_id_comp G)
        (Space.stackEtale C S hS _ (isFiberedInGroupoids_presheafOfGroupoids _)
          ((Stack.modulePullback.{u, u + 1, u, u, v, w} C S hS _ p
            (isFiberedInGroupoids_presheafOfGroupoids _) hp F hF C.topology le_rfl).obj ℱ)) ≫
      (Space.modulePullback C S hS G.source).map (presentationPullbackRestrictionIso F hF hp
        (spaceProj G.objects) (isFiberedInGroupoids_objects G)
        (spacePresentation G.objects) (pointwisePresentationObject (𝟭 (PointwiseFibration G)))
        (isFibredOneMorphism_pointwisePresentationObject (𝟭 (PointwiseFibration G))
          (pointwiseFibration_id_comp G) (isFiberedInGroupoids_presheafOfGroupoids _))
        (isFibredOneMorphism_pointwisePresentationObject F hF hp) ℱ).hom =
    (Space.modulePullback C S hS G.target).map (presentationPullbackRestrictionIso F hF hp
        (spaceProj G.objects) (isFiberedInGroupoids_objects G)
        (spacePresentation G.objects) (pointwisePresentationObject (𝟭 (PointwiseFibration G)))
        (isFibredOneMorphism_pointwisePresentationObject (𝟭 (PointwiseFibration G))
          (pointwiseFibration_id_comp G) (isFiberedInGroupoids_presheafOfGroupoids _))
        (isFibredOneMorphism_pointwisePresentationObject F hF hp) ℱ).hom ≫
      pointwisePresentationTransition F hF (Space.stackEtale C S hS p hp ℱ) :=
  Space.comp_inv_naturality _ _ _ _ _ _ _ (presentationSourceComparison_pullback F hF hp ℱ)
    (presentationTargetComparison_pullback F hF hp ℱ)

/-- `F^*ℱ` as a quasi-coherent module on the pointwise groupoid fibration, with underlying module
`AlgebraicGeometry.Stack.modulePullback` of `ℱ`. -/
def presentationPullbackObj (ℱ : FibredSite.quasicoherentModules.{u, v, w, u} C S hS p hp) :
    FibredSite.quasicoherentModules.{u, u + 1, u, u} C S hS
      (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p
      (isFiberedInGroupoids_presheafOfGroupoids _) :=
  ⟨(Stack.modulePullback.{u, u + 1, u, u, v, w} C S hS _ p
      (isFiberedInGroupoids_presheafOfGroupoids _) hp F hF C.topology le_rfl).obj ℱ.obj,
    ((quasicoherentPullback'.{u, u + 1, u, u, v, w} C S hS _ p
      (isFiberedInGroupoids_presheafOfGroupoids _) hp F hF).obj ℱ).property⟩

/-- The transition of `Φ_𝟭(F^*ℱ)` is `pointwisePresentationTransition` of the étale restriction
of `F^*ℱ`. -/
theorem presentationPullbackObj_alpha
    (ℱ : FibredSite.quasicoherentModules.{u, v, w, u} C S hS p hp) :
    haveI : IsIso (pointwisePresentationSourceComparison (𝟭 (PointwiseFibration G))
        (pointwiseFibration_id_comp G) (Space.stackEtale C S hS _
          (isFiberedInGroupoids_presheafOfGroupoids _)
          ((Stack.modulePullback.{u, u + 1, u, u, v, w} C S hS _ p
            (isFiberedInGroupoids_presheafOfGroupoids _) hp F hF C.topology le_rfl).obj ℱ.obj))) :=
      (isPointwiseDescentAdmissible_of_quasicoherent (𝟭 (PointwiseFibration G))
        (pointwiseFibration_id_comp G) (presentationPullbackObj F hF hp ℱ)).2.1
    ((pointwiseQuasicoherentDescentFunctor (𝟭 (PointwiseFibration G))
        (pointwiseFibration_id_comp G) (isFiberedInGroupoids_presheafOfGroupoids _)).obj
          (presentationPullbackObj F hF hp ℱ)).alpha =
      pointwisePresentationTransition (𝟭 (PointwiseFibration G)) (pointwiseFibration_id_comp G)
        (Space.stackEtale C S hS _ (isFiberedInGroupoids_presheafOfGroupoids _)
          ((Stack.modulePullback.{u, u + 1, u, u, v, w} C S hS _ p
            (isFiberedInGroupoids_presheafOfGroupoids _) hp F hF C.topology le_rfl).obj ℱ.obj)) :=
  rfl

/-- The transition of `Φ_F(ℱ)` is `pointwisePresentationTransition` of the étale restriction
of `ℱ`. -/
theorem presentationObj_alpha (ℱ : FibredSite.quasicoherentModules.{u, v, w, u} C S hS p hp) :
    haveI : IsIso (pointwisePresentationSourceComparison F hF
        (Space.stackEtale C S hS p hp ℱ.obj)) :=
      (isPointwiseDescentAdmissible_of_quasicoherent F hF ℱ).2.1
    ((pointwiseQuasicoherentDescentFunctor F hF hp).obj ℱ).alpha =
      pointwisePresentationTransition F hF (Space.stackEtale C S hS p hp ℱ.obj) := rfl

/-- The restriction isomorphism `presentationPullbackRestrictionIso` on the objects intertwines
the transitions of `Φ_𝟭(F^*ℱ)` and `Φ_F(ℱ)`. -/
theorem presentationPullbackObj_comm
    (ℱ : FibredSite.quasicoherentModules.{u, v, w, u} C S hS p hp) :
    ((pointwiseQuasicoherentDescentFunctor (𝟭 (PointwiseFibration G))
        (pointwiseFibration_id_comp G) (isFiberedInGroupoids_presheafOfGroupoids _)).obj
          (presentationPullbackObj F hF hp ℱ)).alpha ≫
      (Space.modulePullback C S hS G.source).map (presentationPullbackRestrictionIso F hF hp
        (spaceProj G.objects) (isFiberedInGroupoids_objects G)
        (spacePresentation G.objects) (pointwisePresentationObject (𝟭 (PointwiseFibration G)))
        (isFibredOneMorphism_pointwisePresentationObject (𝟭 (PointwiseFibration G))
          (pointwiseFibration_id_comp G) (isFiberedInGroupoids_presheafOfGroupoids _))
        (isFibredOneMorphism_pointwisePresentationObject F hF hp) ℱ.obj).hom =
    (Space.modulePullback C S hS G.target).map (presentationPullbackRestrictionIso F hF hp
        (spaceProj G.objects) (isFiberedInGroupoids_objects G)
        (spacePresentation G.objects) (pointwisePresentationObject (𝟭 (PointwiseFibration G)))
        (isFibredOneMorphism_pointwisePresentationObject (𝟭 (PointwiseFibration G))
          (pointwiseFibration_id_comp G) (isFiberedInGroupoids_presheafOfGroupoids _))
        (isFibredOneMorphism_pointwisePresentationObject F hF hp) ℱ.obj).hom ≫
      ((pointwiseQuasicoherentDescentFunctor F hF hp).obj ℱ).alpha := by
  have : IsIso (pointwisePresentationSourceComparison (𝟭 (PointwiseFibration G))
      (pointwiseFibration_id_comp G) (Space.stackEtale C S hS _
          (isFiberedInGroupoids_presheafOfGroupoids _)
          ((Stack.modulePullback.{u, u + 1, u, u, v, w} C S hS _ p
            (isFiberedInGroupoids_presheafOfGroupoids _) hp F hF C.topology le_rfl).obj ℱ.obj))) :=
    (isPointwiseDescentAdmissible_of_quasicoherent (𝟭 (PointwiseFibration G))
      (pointwiseFibration_id_comp G) (presentationPullbackObj F hF hp ℱ)).2.1
  have : IsIso (pointwisePresentationSourceComparison F hF (Space.stackEtale C S hS p hp ℱ.obj)) :=
      (isPointwiseDescentAdmissible_of_quasicoherent F hF ℱ).2.1
  rw [presentationPullbackObj_alpha, presentationObj_alpha]
  exact pointwisePresentationTransition_pullback F hF hp ℱ.obj

/-- **`Φ_𝟭(F^*ℱ) ≅ Φ_F(ℱ)`**: the descent datum of a quasi-coherent module along a pointwise
presentation `F` is that of its inverse image along `F` on the pointwise groupoid fibration. -/
def pointwiseQuasicoherentDescentFunctorPullbackIso
    (ℱ : FibredSite.quasicoherentModules.{u, v, w, u} C S hS p hp) :
    (pointwiseQuasicoherentDescentFunctor (𝟭 (PointwiseFibration G)) (pointwiseFibration_id_comp G)
        (isFiberedInGroupoids_presheafOfGroupoids _)).obj (presentationPullbackObj F hF hp ℱ) ≅
      (pointwiseQuasicoherentDescentFunctor F hF hp).obj ℱ :=
  quasicoherentModuleIsoMk ⟨(presentationPullbackRestrictionIso F hF hp (spaceProj G.objects)
        (isFiberedInGroupoids_objects G)
        (spacePresentation G.objects) (pointwisePresentationObject (𝟭 (PointwiseFibration G)))
        (isFibredOneMorphism_pointwisePresentationObject (𝟭 (PointwiseFibration G))
          (pointwiseFibration_id_comp G) (isFiberedInGroupoids_presheafOfGroupoids _))
        (isFibredOneMorphism_pointwisePresentationObject F hF hp) ℱ.obj).hom,
          presentationPullbackObj_comm F hF hp ℱ⟩ (Iso.isIso_hom _)

end ReductionIso

end AlgebraicGeometry.Stack

end
