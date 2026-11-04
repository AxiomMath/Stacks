module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedQuasicoherentCohomologyPrimed
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.PointwisePresentationHomRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedQuasicoherentCohomology
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeSheafCoherator
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentFlatBaseChangeSheafFppfExtensions
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticFlatGroupoidChart
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentFlatBaseChangeSheafAssembly
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionComparisonFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionToAlgebraicSpaceExactness
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreEssentialSmallness
public import StacksFrontier.CategoryTheory.Abelian.CoreflectionDetection

/-!
# `LQCoh^fbc(𝒪_𝒳)` read on a flat groupoid presentation (the functor `q₂` of Stacks 0778)

Let `𝒳` be an algebraic stack with a flat groupoid presentation `(U, R, s, t, c)`
(`AlgebraicGeometry.Stack.FlatGroupoidPresentation`), `x : U ⟶ 𝒳`.  The proof of **Stacks 0778**
builds the coherator `Q : LQCoh^fbc(𝒪_𝒳) ⟶ QCoh(𝒪_𝒳)` as `q₁ ∘ q₂`, where `q₁` is the equivalence
of Stacks 06WT and

```
q₂ : LQCoh^fbc(𝒪_𝒳) ⟶ QCoh(U, R, s, t, c),   ℱ ↦ (x^*ℱ|_{U_étale}, α),
```

`α : t_small^*(x^*ℱ|_{U_étale}) ⟶ s_small^*(x^*ℱ|_{U_étale})` being made of the comparison maps of
equation 076R; "`q₂(ℱ)` is quasi-coherent precisely because `ℱ` is locally quasi-coherent and we
used (and needed) the flat base change property in the construction of the descent datum `α`".
This file supplies `q₂` and its properties:

* `Stack.isPointwiseDescentAdmissible_of_locallyQuasicoherentFlatBaseChangeSheaf`: a module of
  `LQCoh^fbc` restricts to a quasi-coherent module on `U` and its comparison maps along the flat
  morphisms `s`, `t` and `c` (a base change of `s`, Stacks 043Z) are isomorphisms; this is the
  input of the general descent functor `AlgebraicGeometry.Stack.pointwiseDescentFunctor`.
* `AlgebraicGeometry.Stack.FlatGroupoidPresentation.flatBaseChangeRestriction`: the functor `q₂`.
* `AlgebraicGeometry.Stack.FlatGroupoidPresentation.bijective_flatBaseChangeRestriction_map`:
  for `𝒢` quasi-coherent, `Hom(𝒢, ℱ) ⟶ Hom(q₂ 𝒢, q₂ ℱ)` is bijective (Stacks 076S, read through
  `AlgebraicGeometry.Stack.presentationObjectRestrictionMap_injective_and_range`). This is the
  first equality in the proof of Stacks 0778.
* `AlgebraicGeometry.Stack.FlatGroupoidPresentation.preservesFiniteLimits_chartRestriction` and
  `…preservesFiniteColimits_chartRestriction`: `ℱ ↦ x^*ℱ|_{U_étale}` is exact on `LQCoh^fbc`
  (Stacks 0GQS (1), and Stacks 0771: cokernels in `LQCoh^fbc` are those of étale modules).

## References

* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
* [Stacks Project, Tag 076S](https://stacks.math.columbia.edu/tag/076S)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 0GQS](https://stacks.math.columbia.edu/tag/0GQS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.Stack

section Admissible

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {A : AlgebraicSpaces C S hS} {G : GroupoidInAlgebraicSpaces C S hS A}
  {𝒳 : Type v} [Category.{w} 𝒳] {p : 𝒳 ⥤ BigFppfOver C S hS} (hp : p.IsFiberedInGroupoids)
  (F : PointwiseFibration G ⥤ 𝒳)
  (hF : F ⋙ p = (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p)

/-- The composition of a groupoid is flat when the source is. -/
theorem isFlat_groupoid_comp (hs : Space.IsFlat C S hS G.source.hom) :
    Space.IsFlat C S hS G.comp.hom :=
  (Space.isFlat_isStableUnderBaseChange C S hS).of_isPullback
    (Space.isPullback_comp_source G).flip hs

include hF in
/-- **A module in `LQCoh^fbc` is admissible for pointwise descent** along a pointwise
presentation whose groupoid has flat source and target: its restriction to the object space is
quasi-coherent, and the comparison maps of equation 076R along the flat morphisms `s`, `t`, and
along the composition `c : R ×_{s,U,t} R ⟶ R`, flat as a base change of `s` (Stacks 043Z), are
isomorphisms. -/
theorem isPointwiseDescentAdmissible_of_locallyQuasicoherentFlatBaseChangeSheaf
    (hs : Space.IsFlat C S hS G.source.hom) (ht : Space.IsFlat C S hS G.target.hom)
    (ℱ : SheafOfModules.{u} (ringStructureSheafCore C S hS p hp (etaleTopology C)
      (etaleTopology_le_topology C)))
    (hℱ : locallyQuasicoherentFlatBaseChangeSheaf C (associatedBigEtaleSite C) rfl S hS p hp ℱ) :
    IsPointwiseDescentAdmissible (hp := hp) F hF ℱ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Space.isQuasicoherentOnSite_etaleRestrictedModuleInverseImage_of_isLocallyQuasicoherent
      C (associatedBigEtaleSite C) rfl S hS _ _ _ hp _ _ _ ℱ hℱ.1
  · exact Space.isIso_comparisonAlgebraicSpacesModules_of_locallyQuasicoherentFlatBaseChangeSheaf
      C (associatedBigEtaleSite C) rfl S hS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hp _ _ hs ℱ hℱ
  · exact Space.isIso_comparisonAlgebraicSpacesModules_of_locallyQuasicoherentFlatBaseChangeSheaf
      C (associatedBigEtaleSite C) rfl S hS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hp _ _ ht ℱ hℱ
  · exact Space.isIso_comparisonAlgebraicSpacesModules_of_locallyQuasicoherentFlatBaseChangeSheaf
      C (associatedBigEtaleSite C) rfl S hS (spaceProj _) (spaceProj G.arrows) p
      (isFiberedInGroupoids_spaceProj _) (isFiberedInGroupoids_arrows G)
      (spacePresentation _) (spacePresentation G.arrows) (spaceFunctor G.comp)
      (pointwisePresentationReindex F G.comp) (pointwisePresentationSource F)
      _ _ _ _ _ hp _ _ (isFlat_groupoid_comp hs) ℱ hℱ

end Admissible

end AlgebraicGeometry.Stack

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable (B S hS) in
/-- **`LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)`** for an algebraic stack, with the flat base change property
of **Stacks 0762** read on sheaves of modules as in the source. -/
abbrev lqcFbcFppf (𝒳 : AlgebraicStacks.{u, w} B S hS) : ObjectProperty (fppfModules B S hS 𝒳) :=
  locallyQuasicoherentFlatBaseChangeSheafFppf B (associatedBigEtaleSite B) rfl S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids

/-- A morphism compatible with `c_t ≫ c_s⁻¹` on both sides fits into the two
squares through `c_s` and `c_t`. -/
theorem comp_inv_comp_eq_of_comp_inv {𝒞 : Type*} [Category 𝒞] {tM sM aM tN sN aN : 𝒞}
    (ctM : tM ⟶ aM) (csM : sM ⟶ aM) [IsIso csM] (ctN : tN ⟶ aN) (csN : sN ⟶ aN) [IsIso csN]
    (φs : sM ⟶ sN) (φt : tM ⟶ tN) (hc : (ctM ≫ inv csM) ≫ φs = φt ≫ ctN ≫ inv csN) :
    ctM ≫ inv csM ≫ φs ≫ csN = φt ≫ ctN := by
  rw [← Category.assoc, ← Category.assoc, hc]
  simp

/-- The inclusion `i : QCoh(𝒪_𝒳) ⥤ LQCoh^fbc(𝒪_𝒳)`. -/
abbrev quasicoherentInclusion (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids ⥤ (lqcFbcFppf B S hS 𝒳).FullSubcategory :=
  quasicoherentToFlatBaseChangeSheafFppf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    (forall_hasFlatBaseChangePropertySheaf_toSiteModules_etale B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids)

end AlgebraicGeometry.Stack

namespace AlgebraicGeometry.Stack.FlatGroupoidPresentation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : AlgebraicStacks.{u, w} B S hS} (P : FlatGroupoidPresentation 𝒳)

/-- **`q₂ : LQCoh^fbc(𝒪_𝒳) ⥤ QCoh(U, R, s, t, c)`** of the proof of Stacks 0778:
`ℱ ↦ (x^*ℱ|_{U_étale}, α)` with `α` built from the comparison maps of equation 076R, which are
isomorphisms by the flat base change property. -/
def flatBaseChangeRestriction :
    (lqcFbcFppf B S hS 𝒳).FullSubcategory ⥤ Space.QuasicoherentModule B S hS P.G :=
  ObjectProperty.lift (pointwiseDescentAdmissible P.F P.hF 𝒳.val.isFiberedInGroupoids)
    ((lqcFbcFppf B S hS 𝒳).ι ⋙
      fppfToEtaleSheafOfModules B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids)
    (fun M => isPointwiseDescentAdmissible_of_locallyQuasicoherentFlatBaseChangeSheaf
      𝒳.val.isFiberedInGroupoids P.F P.hF P.hs P.ht _ M.property) ⋙
  pointwiseDescentFunctor P.F P.hF 𝒳.val.isFiberedInGroupoids

/-- The underlying morphism of `q₂ f` is the restriction of `f` to the object space. -/
theorem flatBaseChangeRestriction_map_hom {M N : (lqcFbcFppf B S hS 𝒳).FullSubcategory}
    (f : M ⟶ N) :
    (P.flatBaseChangeRestriction.map f).hom =
      presentationObjectRestrictionMap (hp := 𝒳.val.isFiberedInGroupoids) P.F P.hF f.hom :=
  rfl

/-- The source comparison map of a module of `LQCoh^fbc` is an isomorphism. -/
private theorem isIso_presentationSourceComparison (N : (lqcFbcFppf B S hS 𝒳).FullSubcategory) :
    IsIso (presentationSourceComparison (hp := 𝒳.val.isFiberedInGroupoids) P.F P.hF N.obj) :=
  (isPointwiseDescentAdmissible_of_locallyQuasicoherentFlatBaseChangeSheaf
    𝒳.val.isFiberedInGroupoids P.F P.hF P.hs P.ht _ N.property).2.1

/-- The descent datum of `q₂ N` is `c_t ≫ c_s⁻¹`, built from the comparison maps along the target
and the source. -/
theorem flatBaseChangeRestriction_obj_alpha (N : (lqcFbcFppf B S hS 𝒳).FullSubcategory) :
    haveI : IsIso (presentationSourceComparison (hp := 𝒳.val.isFiberedInGroupoids)
        P.F P.hF N.obj) :=
      (isPointwiseDescentAdmissible_of_locallyQuasicoherentFlatBaseChangeSheaf
        𝒳.val.isFiberedInGroupoids P.F P.hF P.hs P.ht _ N.property).2.1
    (P.flatBaseChangeRestriction.obj N).alpha =
      presentationTargetComparison P.F P.hF N.obj ≫
        inv (presentationSourceComparison P.F P.hF N.obj) :=
  pointwiseDescentObj_alpha P.F P.hF _
    (isPointwiseDescentAdmissible_of_locallyQuasicoherentFlatBaseChangeSheaf
      𝒳.val.isFiberedInGroupoids P.F P.hF P.hs P.ht _ N.property)

/-- **Stacks 076S read through `q₂`**: for `𝒢` quasi-coherent and `ℱ` in `LQCoh^fbc`, the map
`Hom(𝒢, ℱ) ⟶ Hom(q₂ 𝒢, q₂ ℱ)` is bijective. -/
theorem bijective_flatBaseChangeRestriction_map (M N : (lqcFbcFppf B S hS 𝒳).FullSubcategory)
    (hM : M.obj.IsQuasicoherentOnSite) :
    Function.Bijective (fun f : M ⟶ N => P.flatBaseChangeRestriction.map f) := by
  have := P.full
  have := P.faithful
  obtain ⟨hinj, hrange⟩ := presentationObjectRestrictionMap_injective_and_range P.F P.hF P.hloc
    hM N.obj
  refine ⟨fun f g h => ?_, fun φ => ?_⟩
  · have h' := congrArg Space.QuasicoherentModule.Hom.hom h
    exact ObjectProperty.hom_ext _ (hinj h')
  · have hcs := isIso_presentationSourceComparison P M
    have hcsN := isIso_presentationSourceComparison P N
    have hc := φ.comm
    rw [flatBaseChangeRestriction_obj_alpha, flatBaseChangeRestriction_obj_alpha] at hc
    obtain ⟨ψ, hψ⟩ := (hrange φ.hom).2 ⟨inv (presentationSourceComparison P.F P.hF M.obj) ≫
        (Space.modulePullback B S hS P.G.source).map φ.hom ≫
          presentationSourceComparison P.F P.hF N.obj, IsIso.hom_inv_id_assoc _ _,
      @comp_inv_comp_eq_of_comp_inv _ _ _ _ _ _ _ _ _ _ hcs _ _ hcsN _ _ hc⟩
    exact ⟨ObjectProperty.homMk ψ, Space.QuasicoherentModule.Hom.ext hψ⟩


section Exactness

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] FlatFppf.hasSheafify_fppf_addCommGrpCat
  FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat

/-- `ℱ ↦ x^*ℱ|_{U_étale}` on `LQCoh^fbc(𝒪_𝒳)`: `q₂` followed by forgetting the descent datum. -/
abbrev chartRestriction :
    (lqcFbcFppf B S hS 𝒳).FullSubcategory ⥤
      Space.Modules.{u, u} B S hS P.G.objects.1 P.G.objects.2 :=
  P.flatBaseChangeRestriction ⋙ Space.QuasicoherentModule.forget P.G

/-- `chartRestriction` is the inclusion into `Mod(𝒪_𝒳)`, followed by reading in the étale
topology and by the étale-restricted inverse image along the chart `x : U ⟶ 𝒳`. -/
theorem chartRestriction_eq : P.chartRestriction =
    (lqcFbcFppf B S hS 𝒳).ι ⋙
      fppfToEtaleSheafOfModules B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids ⋙
        Space.etaleRestrictedModuleInverseImageFunctor B S hS (spaceProj P.G.objects)
          𝒳.val.val.p (isFiberedInGroupoids_objects P.G) 𝒳.val.isFiberedInGroupoids
          (spacePresentation P.G.objects) (pointwisePresentationObject P.F)
          (isFibredOneMorphism_pointwisePresentationObject P.F P.hF 𝒳.val.isFiberedInGroupoids) :=
  rfl

/-- `LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)` is a weak Serre subcategory (Stacks 0771 (2)). -/
instance isWeakSerreClass_lqcFbcFppf :
    (lqcFbcFppf B S hS 𝒳).IsWeakSerreClass :=
  isWeakSerreClass_locallyQuasicoherentFlatBaseChangeSheafFppf_essentiallySmall B
    (associatedBigEtaleSite B) rfl S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids

/-- Reading a module of `LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)` in the étale topology, as a functor between
the two full subcategories `LQCoh^fbc`. -/
abbrev lqcFbcToEtale :
    (lqcFbcFppf B S hS 𝒳).FullSubcategory ⥤
      (locallyQuasicoherentFlatBaseChangeSheaf B (associatedBigEtaleSite B) rfl S hS
        𝒳.val.val.p 𝒳.val.isFiberedInGroupoids).FullSubcategory :=
  ObjectProperty.lift _ ((lqcFbcFppf B S hS 𝒳).ι ⋙
    fppfToEtaleSheafOfModules B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids) fun M => M.property

/-- `lqcFbcToEtale` is fully faithful: neither the sheaf condition nor the morphisms change. -/
def fullyFaithfulLqcFbcToEtale : (lqcFbcToEtale (𝒳 := 𝒳)).FullyFaithful where
  preimage f := ObjectProperty.homMk ⟨f.hom.val⟩

/-- `lqcFbcToEtale` is full. -/
instance : (lqcFbcToEtale (𝒳 := 𝒳)).Full := fullyFaithfulLqcFbcToEtale.full

/-- `lqcFbcToEtale` is faithful. -/
instance : (lqcFbcToEtale (𝒳 := 𝒳)).Faithful := fullyFaithfulLqcFbcToEtale.faithful

/-- `lqcFbcToEtale` is essentially surjective: every étale module of `LQCoh^fbc` is the étale
reading of its fppf extension. -/
instance : (lqcFbcToEtale (𝒳 := 𝒳)).EssSurj where
  mem_essImage N := ⟨⟨(locallyQuasicoherentFlatBaseChangeSheafToFppf B (associatedBigEtaleSite B)
      rfl S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids).obj N, N.property⟩,
    ⟨ObjectProperty.isoMk _ (Iso.refl _)⟩⟩

/-- `lqcFbcToEtale` is an equivalence of categories. -/
instance : (lqcFbcToEtale (𝒳 := 𝒳)).IsEquivalence where

/-- `ℱ ↦ x^*ℱ|_{U_étale}` preserves finite limits on `LQCoh^fbc(𝒪_𝒳)`. -/
theorem preservesFiniteLimits_chartRestriction : PreservesFiniteLimits P.chartRestriction := by
  let : HasSheafify (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, u} _ _
  let : (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u, u + 1, u + 1, u} _
  have h1 := (lqcFbcFppf B S hS 𝒳).preservesFiniteLimits_ι_of_isWeakSerreClass
  have h2 : PreservesFiniteLimits
      (fppfToEtaleSheafOfModules B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids) := inferInstance
  have h3 := (Space.exactFunctor_etaleRestrictedModuleInverseImageFunctor B S hS
    (spaceProj P.G.objects) 𝒳.val.val.p (isFiberedInGroupoids_objects P.G)
    𝒳.val.isFiberedInGroupoids (spacePresentation P.G.objects) (pointwisePresentationObject P.F)
    (isFibredOneMorphism_pointwisePresentationObject P.F P.hF 𝒳.val.isFiberedInGroupoids)).1
  rw [chartRestriction_eq]
  exact @comp_preservesFiniteLimits _ _ _ _ _ _ _ _ h1
    (@comp_preservesFiniteLimits _ _ _ _ _ _ _ _ h2 h3)

/-- `ℱ ↦ x^*ℱ|_{U_étale}` preserves finite colimits on `LQCoh^fbc(𝒪_𝒳)`. -/
theorem preservesFiniteColimits_chartRestriction :
    PreservesFiniteColimits P.chartRestriction := by
  let : HasSheafify (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, u} _ _
  let : (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u, u + 1, u + 1, u} _
  have := isWeakSerreClass_locallyQuasicoherentFlatBaseChangeSheaf_etale B
    (associatedBigEtaleSite B) rfl S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
  have h0 := (locallyQuasicoherentFlatBaseChangeSheaf B (associatedBigEtaleSite B) rfl S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids).preservesFiniteColimits_ι_of_isWeakSerreClass
  have h1 : PreservesFiniteColimits ((lqcFbcFppf B S hS 𝒳).ι ⋙
      fppfToEtaleSheafOfModules B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids) :=
    @comp_preservesFiniteColimits _ _ _ _ _ _ (lqcFbcToEtale (𝒳 := 𝒳)) (ObjectProperty.ι _)
      inferInstance h0
  have h3 := (Space.exactFunctor_etaleRestrictedModuleInverseImageFunctor B S hS
    (spaceProj P.G.objects) 𝒳.val.val.p (isFiberedInGroupoids_objects P.G)
    𝒳.val.isFiberedInGroupoids (spacePresentation P.G.objects) (pointwisePresentationObject P.F)
    (isFibredOneMorphism_pointwisePresentationObject P.F P.hF 𝒳.val.isFiberedInGroupoids)).2
  rw [chartRestriction_eq]
  exact @comp_preservesFiniteColimits _ _ _ _ _ _ ((lqcFbcFppf B S hS 𝒳).ι ⋙
      fppfToEtaleSheafOfModules B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids) _ h1 h3

end Exactness


end AlgebraicGeometry.Stack.FlatGroupoidPresentation
