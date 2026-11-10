module

public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionComparisonAlgebraicSpaceComposition

/-!
# The module comparison maps of equation 076R and inverse image along a 1-morphism

Let `K : 𝒳 ⥤ 𝒴` be a 1-morphism of categories fibred in groupoids over `(Sch/S)_{fppf}`.  An
`𝒪_𝒴`-module `ℱ` on the inherited étale site of `𝒴` has an inverse image `K^*ℱ` on the inherited
étale site of `𝒳`, restriction of sections along `K`
(`AlgebraicGeometry.Space.inheritedEtalePullback`).  For a 1-morphism `f : 𝒰 ⥤ 𝒳` from a
category representable by an algebraic space `U` the two restrictions
`f^*(K^*ℱ)|_{U_étale}` and `(f ⋙ K)^*ℱ|_{U_étale}` are identified, with identity components
(`AlgebraicGeometry.Space.etaleRestrictedModuleInverseImagePullbackIso`), and the comparison
maps of equation 076R are compatible with this identification: the comparison map of a
2-commutative triangle `φ : a ⋙ g ≅ f` for `K^*ℱ` is the comparison map of the whiskered triangle
`a ⋙ (g ⋙ K) ≅ f ⋙ K` for `ℱ`
(`AlgebraicGeometry.Space.comparisonAlgebraicSpacesModules_inheritedEtalePullback`).

This is the form of the functoriality of the comparison maps in the target category used to
compare the descent data of Stacks 06WT attached to different presentations.

## References

* [Stacks Project, Tag 076R](https://stacks.math.columbia.edu/tag/076R)
* [Stacks Project, Tag 06WT](https://stacks.math.columbia.edu/tag/06WT)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Space

universe u v w v' w' v'' w'' v''' w'''

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Pullback

variable {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
  (r : 𝒳 ⥤ BigFppfOver B S hS) (r' : 𝒴 ⥤ BigFppfOver B S hS)
  (hr : r.IsFiberedInGroupoids) (hr' : r'.IsFiberedInGroupoids)
  (K : 𝒳 ⥤ 𝒴) (hK : r.IsFibredOneMorphism r' K)

include hr hK in
/-- A 1-morphism of categories fibred in groupoids is continuous for the inherited étale
topologies. -/
theorem inheritedEtale_isContinuous :
    K.IsContinuous (BigFppfOver.associatedTopology B S hS r .etale)
      (BigFppfOver.associatedTopology B S hS r' .etale) :=
  let := hr.isFibered
  hK.isContinuous_inheritedTopology (BigFppfOver.baseOverTopology B S hS .etale)

/-- The identification of the structure sheaf of `𝒳` with the restriction along `K` of the
structure sheaf of `𝒴`, induced by the equality `K ⋙ r' = r`. -/
def inheritedEtaleStructureHom :
    letI := inheritedEtale_isContinuous B S hS r r' hr K hK
    FibredSite.ringStructureSheafCore B S hS r hr .etale ⟶
      (K.sheafPushforwardContinuous RingCat.{u}
        (BigFppfOver.associatedTopology B S hS r .etale)
        (BigFppfOver.associatedTopology B S hS r' .etale)).obj
        (FibredSite.ringStructureSheafCore B S hS r' hr' .etale) :=
  letI := inheritedEtale_isContinuous B S hS r r' hr K hK
  ⟨Functor.whiskerRight (NatTrans.op (eqToHom hK.comp_eq)) (BigFppfOver.structureSheaf B S hS).obj⟩

theorem inheritedEtaleStructureHom_app (X : 𝒳) :
    (inheritedEtaleStructureHom B S hS r r' hr hr' K hK).hom.app (op X) =
      (BigFppfOver.structureSheaf B S hS).obj.map
        (eqToHom (Functor.congr_obj hK.comp_eq X)).op := by
  change (BigFppfOver.structureSheaf B S hS).obj.map ((eqToHom hK.comp_eq).app X).op = _
  rw [eqToHom_app]

/-- **The inverse image of modules on the inherited étale sites along a 1-morphism `K`**:
restriction of sections along `K`, with scalars through
`AlgebraicGeometry.Space.inheritedEtaleStructureHom`. -/
def inheritedEtalePullback :
    inheritedEtaleModules.{u} B S hS r' hr' ⥤ inheritedEtaleModules.{u} B S hS r hr :=
  letI := inheritedEtale_isContinuous B S hS r r' hr K hK
  SheafOfModules.pushforward (inheritedEtaleStructureHom B S hS r r' hr hr' K hK)

theorem inheritedEtalePullback_obj_val_map (ℱ : inheritedEtaleModules.{u} B S hS r' hr')
    {X Y : 𝒳} (g : X ⟶ Y) (x : ℱ.val.obj (op (K.obj Y))) :
    ((inheritedEtalePullback B S hS r r' hr hr' K hK).obj ℱ).val.map g.op x =
      ℱ.val.map (K.map g).op x := rfl

theorem inheritedEtalePullback_map_val_app {ℱ ℱ' : inheritedEtaleModules.{u} B S hS r' hr'}
    (ψ : ℱ ⟶ ℱ') (X : 𝒳) (x : ℱ.val.obj (op (K.obj X))) :
    ((inheritedEtalePullback B S hS r r' hr hr' K hK).map ψ).val.app (op X) x =
      ψ.val.app (op (K.obj X)) x := rfl

variable {U : AlgebraicSpaces B S hS} {𝒰 : Type v''} [Category.{w''} 𝒰]
  (p : 𝒰 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (eU : StacksRepresentableCFG.EquivalenceOver p
    (presheafOfCategories (U.1 ⋙ typeToCat)).p)
  (f : 𝒰 ⥤ 𝒳) (hf : p.IsFibredOneMorphism r f) (hfK : p.IsFibredOneMorphism r' (f ⋙ K))

/-- Ring maps of `f^*(K^*-)|_{U_étale}` and of `(f ⋙ K)^*-|_{U_étale}` agree. -/
theorem etaleChartStructureHom_comp_inheritedEtaleStructureHom :
    letI := etaleChartToFibred_isContinuous B S hS p r hp eU f hf
    letI := inheritedEtale_isContinuous B S hS r r' hr K hK
    letI := etaleChartToFibred_isContinuous B S hS p r' hp eU (f ⋙ K) hfK
    (etaleChartStructureHom B S hS p r hp hr eU f hf ≫
        ((etaleChartToFibred B S hS p eU f).sheafPushforwardContinuous RingCat.{u}
          (SmallEtale.topology B S hS U.1)
          (BigFppfOver.associatedTopology B S hS r .etale)).map
          (inheritedEtaleStructureHom B S hS r r' hr hr' K hK) :
        structureRingSheaf B S hS U ⟶
          ((etaleChartToFibred B S hS p eU (f ⋙ K)).sheafPushforwardContinuous RingCat.{u}
            (SmallEtale.topology B S hS U.1)
            (BigFppfOver.associatedTopology B S hS r' .etale)).obj
            (FibredSite.ringStructureSheafCore B S hS r' hr' .etale)) =
      etaleChartStructureHom B S hS p r' hp hr' eU (f ⋙ K) hfK := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun W ↦ RingCat.hom_ext (RingHom.ext fun ρ ↦ ?_)))
  change (inheritedEtaleStructureHom B S hS r r' hr hr' K hK).hom.app
      (op ((etaleChartToFibred B S hS p eU f).obj W.unop))
      ((etaleChartStructureHom B S hS p r hp hr eU f hf).hom.app W ρ) =
    (etaleChartStructureHom B S hS p r' hp hr' eU (f ⋙ K) hfK).hom.app W ρ
  rw [inheritedEtaleStructureHom_app, etaleChartStructureHom_app, etaleChartStructureHom_app]
  change ((BigFppfOver.structureSheaf B S hS).obj.map _ ≫
    (BigFppfOver.structureSheaf B S hS).obj.map _) ρ = _
  rw [← Functor.map_comp, ← op_comp, eqToHom_trans]
  rfl

/-- **`f^*(K^*ℱ)|_{U_étale} ≅ (f ⋙ K)^*ℱ|_{U_étale}`**, with identity components. -/
def etaleRestrictedModuleInverseImagePullbackIso (ℱ : inheritedEtaleModules.{u} B S hS r' hr') :
    etaleRestrictedModuleInverseImage B S hS p r hp hr eU f hf
        ((inheritedEtalePullback B S hS r r' hr hr' K hK).obj ℱ) ≅
      etaleRestrictedModuleInverseImage B S hS p r' hp hr' eU (f ⋙ K) hfK ℱ :=
  letI := etaleChartToFibred_isContinuous B S hS p r hp eU f hf
  letI := inheritedEtale_isContinuous B S hS r r' hr K hK
  letI := etaleChartToFibred_isContinuous B S hS p r' hp eU (f ⋙ K) hfK
  (SheafOfModules.pushforwardComp (etaleChartStructureHom B S hS p r hp hr eU f hf)
      (inheritedEtaleStructureHom B S hS r r' hr hr' K hK)).app ℱ ≪≫
    (SheafOfModules.pushforwardCongr
      (etaleChartStructureHom_comp_inheritedEtaleStructureHom B S hS r r' hr hr' K hK p hp eU f hf
        hfK)).app ℱ

theorem etaleRestrictedModuleInverseImagePullbackIso_hom_val_app
    (ℱ : inheritedEtaleModules.{u} B S hS r' hr') (W : (SmallEtale B S hS U.1)ᵒᵖ) (x) :
    (etaleRestrictedModuleInverseImagePullbackIso B S hS r r' hr hr' K hK p hp eU f hf hfK
      ℱ).hom.val.app W x = x := rfl

theorem etaleRestrictedModuleInverseImagePullbackIso_inv_val_app
    (ℱ : inheritedEtaleModules.{u} B S hS r' hr') (W : (SmallEtale B S hS U.1)ᵒᵖ) (x) :
    (etaleRestrictedModuleInverseImagePullbackIso B S hS r r' hr hr' K hK p hp eU f hf hfK
      ℱ).inv.val.app W x = x := rfl

/-! ### The comparison maps of equation 076R and the inverse image along `K` -/

variable {V : AlgebraicSpaces B S hS} {𝒱 : Type v'''} [Category.{w'''} 𝒱]
  (q : 𝒱 ⥤ BigFppfOver B S hS) (hq : q.IsFiberedInGroupoids)
  (eV : StacksRepresentableCFG.EquivalenceOver q
    (presheafOfCategories (V.1 ⋙ typeToCat)).p)
  (a : 𝒰 ⥤ 𝒱) (g : 𝒱 ⥤ 𝒳) (hg : q.IsFibredOneMorphism r g)
  (hgK : q.IsFibredOneMorphism r' (g ⋙ K))
  (φ : a ⋙ g ≅ f) (aSpace : U ⟶ V)
  (ha : schemeChartFunctor B S hS U.1 p eU ⋙ a ≅
    CostructuredArrow.map aSpace.hom ⋙ schemeChartFunctor B S hS V.1 q eV)
  (hφ : ∀ X : 𝒰, r.IsHomLift (𝟙 (r.obj (f.obj X))) (φ.inv.app X))
  (hab : ∀ Z : CostructuredArrow yoneda U.1,
    q.IsHomLift (𝟙 (q.obj (a.obj ((schemeChartFunctor B S hS U.1 p eU).obj Z))))
      (ha.hom.app Z))

/-- The triangle `φ : a ⋙ g ≅ f` whiskered by `K`: `a ⋙ (g ⋙ K) ≅ f ⋙ K`. -/
abbrev whiskerTriangleIso : a ⋙ (g ⋙ K) ≅ f ⋙ K :=
  (Functor.associator a g K).symm ≪≫ Functor.isoWhiskerRight φ K

include hK hφ in
/-- The components of the whiskered triangle lie over identities. -/
theorem isHomLift_whiskerTriangleIso_inv_app (X : 𝒰) :
    r'.IsHomLift (𝟙 (r'.obj ((f ⋙ K).obj X))) ((whiskerTriangleIso K f a g φ).inv.app X) := by
  have := hφ X
  have h : r'.IsHomLift (𝟙 (r.obj (f.obj X))) (K.map (φ.inv.app X)) :=
    hK.map_isHomLift _ (φ.inv.app X)
  have e : (whiskerTriangleIso K f a g φ).inv.app X = K.map (φ.inv.app X) := by simp
  rw [e]
  have e' : r'.obj ((f ⋙ K).obj X) = r.obj (f.obj X) := Functor.congr_obj hK.comp_eq (f.obj X)
  rw [e']
  exact h

/-- The comparison morphism of the whiskered triangle is the image under `K` of the comparison
morphism of the triangle. -/
theorem comparisonMorphism_whiskerTriangleIso (d : ChartDiagram B S hS U.1 V.1 aSpace.hom) :
    comparisonMorphism B S hS p q eU eV a (f ⋙ K) (g ⋙ K) (whiskerTriangleIso K f a g φ) aSpace
        ha d =
      K.map (comparisonMorphism B S hS p q eU eV a f g φ aSpace ha d) := by
  simp [comparisonMorphism]

/-- **The comparison maps of equation 076R commute with inverse image along a 1-morphism.**
For a 2-commutative triangle `φ : a ⋙ g ≅ f` into `𝒳` and a 1-morphism `K : 𝒳 ⥤ 𝒴`, the
comparison map of `φ` for `K^*ℱ` is the comparison map of the whiskered triangle
`a ⋙ (g ⋙ K) ≅ f ⋙ K` for `ℱ`, through the identifications
`f^*(K^*ℱ)|_{U_étale} = (f ⋙ K)^*ℱ|_{U_étale}` and
`g^*(K^*ℱ)|_{V_étale} = (g ⋙ K)^*ℱ|_{V_étale}`. -/
theorem comparisonAlgebraicSpacesModules_inheritedEtalePullback
    (hφK : ∀ X : 𝒰, r'.IsHomLift (𝟙 (r'.obj ((f ⋙ K).obj X)))
      ((whiskerTriangleIso K f a g φ).inv.app X))
    (ℱ : inheritedEtaleModules.{u} B S hS r' hr') :
    comparisonAlgebraicSpacesModules B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha hr hφ hab
        ((inheritedEtalePullback B S hS r r' hr hr' K hK).obj ℱ) ≫
      (etaleRestrictedModuleInverseImagePullbackIso B S hS r r' hr hr' K hK p hp eU f hf hfK
        ℱ).hom =
    (modulePullback B S hS aSpace).map
        (etaleRestrictedModuleInverseImagePullbackIso B S hS r r' hr hr' K hK q hq eV g hg hgK
          ℱ).hom ≫
      comparisonAlgebraicSpacesModules B S hS p q r' hp hq eU eV a (f ⋙ K) (g ⋙ K) hfK hgK
        (whiskerTriangleIso K f a g φ) aSpace ha hr' hφK hab ℱ := by
  refine ((modulePullbackAdjunction B S hS aSpace).homEquiv _ _).injective ?_
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left,
    comparisonAlgebraicSpacesModules_adjoint, comparisonAlgebraicSpacesModules_adjoint]
  refine (modulePushforwardHomEquiv B S hS aSpace _ _).injective ?_
  refine ModuleFMap.ext B S hS (funext fun d ↦ funext fun s ↦ ?_)
  change (modulePushforwardHomFMap B S hS aSpace _ _ (_ ≫ _)).app d s =
    (modulePushforwardHomFMap B S hS aSpace _ _ (_ ≫ _)).app d s
  rw [modulePushforwardHomFMap_comp_map, modulePushforwardHomFMap_precomp]
  unfold moduleComparisonPushforwardHom
  rw [modulePushforwardHomFMap_moduleFMapHom, modulePushforwardHomFMap_moduleFMapHom,
    moduleComparisonFMap_app, moduleComparisonFMap_app]
  rw [comparisonMorphism_whiskerTriangleIso]
  rfl

end Pullback

end AlgebraicGeometry.Space

end
